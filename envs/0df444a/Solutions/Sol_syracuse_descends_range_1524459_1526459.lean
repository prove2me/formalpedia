-- Prove2me | solution 1 for syracuse_descends_range_1524459_1526459
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:32.815746+00:00
-- url     : https://prove2.me/submissions/1f26d1e7-cf08-43fb-b1e3-43975ce15b2b

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


theorem B3432509 : Blo 1524459 3432509 := bbase (se 3 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 3432509 = 1287191) (by norm_num)
theorem B2170957 : Blo 1524459 2170957 := bbase (se 3 (by rfl) ⟨407054, by rfl⟩ : syracuseStep 2170957 = 814109) (by norm_num)
theorem B3432581 : Blo 1524459 3432581 := bbase (se 4 (by rfl) ⟨321804, by rfl⟩ : syracuseStep 3432581 = 643609) (by norm_num)
theorem B2171053 : Blo 1524459 2171053 := bbase (se 3 (by rfl) ⟨407072, by rfl⟩ : syracuseStep 2171053 = 814145) (by norm_num)
theorem B3432653 : Blo 1524459 3432653 := bbase (se 3 (by rfl) ⟨643622, by rfl⟩ : syracuseStep 3432653 = 1287245) (by norm_num)
theorem B6185173 : Blo 1524459 6185173 := bbase (se 7 (by rfl) ⟨72482, by rfl⟩ : syracuseStep 6185173 = 144965) (by norm_num)
theorem B5497093 : Blo 1524459 5497093 := bbase (se 4 (by rfl) ⟨515352, by rfl⟩ : syracuseStep 5497093 = 1030705) (by norm_num)
theorem B3432725 : Blo 1524459 3432725 := bbase (se 6 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 3432725 = 160909) (by norm_num)
theorem B2572573 : Blo 1524459 2572573 := bbase (se 3 (by rfl) ⟨482357, by rfl⟩ : syracuseStep 2572573 = 964715) (by norm_num)
theorem B35225941 : Blo 1524459 35225941 := bbase (se 10 (by rfl) ⟨51600, by rfl⟩ : syracuseStep 35225941 = 103201) (by norm_num)
theorem B3432797 : Blo 1524459 3432797 := bbase (se 3 (by rfl) ⟨643649, by rfl⟩ : syracuseStep 3432797 = 1287299) (by norm_num)
theorem B2572661 : Blo 1524459 2572661 := bbase (se 5 (by rfl) ⟨120593, by rfl⟩ : syracuseStep 2572661 = 241187) (by norm_num)
theorem B3432869 : Blo 1524459 3432869 := bbase (se 4 (by rfl) ⟨321831, by rfl⟩ : syracuseStep 3432869 = 643663) (by norm_num)
theorem B7053797 : Blo 1524459 7053797 := bbase (se 4 (by rfl) ⟨661293, by rfl⟩ : syracuseStep 7053797 = 1322587) (by norm_num)
theorem B3432941 : Blo 1524459 3432941 := bbase (se 3 (by rfl) ⟨643676, by rfl⟩ : syracuseStep 3432941 = 1287353) (by norm_num)
theorem B2572789 : Blo 1524459 2572789 := bbase (se 5 (by rfl) ⟨120599, by rfl⟩ : syracuseStep 2572789 = 241199) (by norm_num)
theorem B13033973 : Blo 1524459 13033973 := bbase (se 5 (by rfl) ⟨610967, by rfl⟩ : syracuseStep 13033973 = 1221935) (by norm_num)
theorem B3858941 : Blo 1524459 3858941 := bbase (se 3 (by rfl) ⟨723551, by rfl⟩ : syracuseStep 3858941 = 1447103) (by norm_num)
theorem B1696297 : Blo 1524459 1696297 := bbase (se 2 (by rfl) ⟨636111, by rfl⟩ : syracuseStep 1696297 = 1272223) (by norm_num)
theorem B3433013 : Blo 1524459 3433013 := bbase (se 5 (by rfl) ⟨160922, by rfl⟩ : syracuseStep 3433013 = 321845) (by norm_num)
theorem B2572877 : Blo 1524459 2572877 := bbase (se 3 (by rfl) ⟨482414, by rfl⟩ : syracuseStep 2572877 = 964829) (by norm_num)
theorem B5145173 : Blo 1524459 5145173 := bbase (se 8 (by rfl) ⟨30147, by rfl⟩ : syracuseStep 5145173 = 60295) (by norm_num)
theorem B3433085 : Blo 1524459 3433085 := bbase (se 3 (by rfl) ⟨643703, by rfl⟩ : syracuseStep 3433085 = 1287407) (by norm_num)
theorem B2171549 : Blo 1524459 2171549 := bbase (se 3 (by rfl) ⟨407165, by rfl⟩ : syracuseStep 2171549 = 814331) (by norm_num)
theorem B7332533 : Blo 1524459 7332533 := bbase (se 5 (by rfl) ⟨343712, by rfl⟩ : syracuseStep 7332533 = 687425) (by norm_num)
theorem B2441917 : Blo 1524459 2441917 := bbase (se 3 (by rfl) ⟨457859, by rfl⟩ : syracuseStep 2441917 = 915719) (by norm_num)
theorem B3433157 : Blo 1524459 3433157 := bbase (se 4 (by rfl) ⟨321858, by rfl⟩ : syracuseStep 3433157 = 643717) (by norm_num)
theorem B2573005 : Blo 1524459 2573005 := bbase (se 3 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 2573005 = 964877) (by norm_num)
theorem B6513365 : Blo 1524459 6513365 := bbase (se 7 (by rfl) ⟨76328, by rfl⟩ : syracuseStep 6513365 = 152657) (by norm_num)
theorem B4342517 : Blo 1524459 4342517 := bbase (se 5 (by rfl) ⟨203555, by rfl⟩ : syracuseStep 4342517 = 407111) (by norm_num)
theorem B3433229 : Blo 1524459 3433229 := bbase (se 3 (by rfl) ⟨643730, by rfl⟩ : syracuseStep 3433229 = 1287461) (by norm_num)
theorem B2573093 : Blo 1524459 2573093 := bbase (se 4 (by rfl) ⟨241227, by rfl⟩ : syracuseStep 2573093 = 482455) (by norm_num)
theorem B3859285 : Blo 1524459 3859285 := bbase (se 9 (by rfl) ⟨11306, by rfl⟩ : syracuseStep 3859285 = 22613) (by norm_num)
theorem B3433301 : Blo 1524459 3433301 := bbase (se 9 (by rfl) ⟨10058, by rfl⟩ : syracuseStep 3433301 = 20117) (by norm_num)
theorem B7725941 : Blo 1524459 7725941 := bbase (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) (by norm_num)
theorem B6693781 : Blo 1524459 6693781 := bbase (se 6 (by rfl) ⟨156885, by rfl⟩ : syracuseStep 6693781 = 313771) (by norm_num)
theorem B3433373 : Blo 1524459 3433373 := bbase (se 3 (by rfl) ⟨643757, by rfl⟩ : syracuseStep 3433373 = 1287515) (by norm_num)
theorem B2573221 : Blo 1524459 2573221 := bbase (se 4 (by rfl) ⟨241239, by rfl⟩ : syracuseStep 2573221 = 482479) (by norm_num)
theorem B3859397 : Blo 1524459 3859397 := bbase (se 4 (by rfl) ⟨361818, by rfl⟩ : syracuseStep 3859397 = 723637) (by norm_num)
theorem B6513605 : Blo 1524459 6513605 := bbase (se 4 (by rfl) ⟨610650, by rfl⟩ : syracuseStep 6513605 = 1221301) (by norm_num)
theorem B5792741 : Blo 1524459 5792741 := bbase (se 4 (by rfl) ⟨543069, by rfl⟩ : syracuseStep 5792741 = 1086139) (by norm_num)
theorem B3433445 : Blo 1524459 3433445 := bbase (se 4 (by rfl) ⟨321885, by rfl⟩ : syracuseStep 3433445 = 643771) (by norm_num)
theorem B2573309 : Blo 1524459 2573309 := bbase (se 3 (by rfl) ⟨482495, by rfl⟩ : syracuseStep 2573309 = 964991) (by norm_num)
theorem B5145605 : Blo 1524459 5145605 := bbase (se 4 (by rfl) ⟨482400, by rfl⟩ : syracuseStep 5145605 = 964801) (by norm_num)
theorem B14664725 : Blo 1524459 14664725 := bbase (se 6 (by rfl) ⟨343704, by rfl⟩ : syracuseStep 14664725 = 687409) (by norm_num)
theorem B8692757 : Blo 1524459 8692757 := bbase (se 6 (by rfl) ⟨203736, by rfl⟩ : syracuseStep 8692757 = 407473) (by norm_num)
theorem B3433517 : Blo 1524459 3433517 := bbase (se 3 (by rfl) ⟨643784, by rfl⟩ : syracuseStep 3433517 = 1287569) (by norm_num)
theorem B7824437 : Blo 1524459 7824437 := bbase (se 5 (by rfl) ⟨366770, by rfl⟩ : syracuseStep 7824437 = 733541) (by norm_num)
theorem B2286701 : Blo 1524459 2286701 := bbase (se 3 (by rfl) ⟨428756, by rfl⟩ : syracuseStep 2286701 = 857513) (by norm_num)
theorem B3433589 : Blo 1524459 3433589 := bbase (se 5 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 3433589 = 321899) (by norm_num)
theorem B2573437 : Blo 1524459 2573437 := bbase (se 3 (by rfl) ⟨482519, by rfl⟩ : syracuseStep 2573437 = 965039) (by norm_num)
theorem B2286725 : Blo 1524459 2286725 := bbase (se 4 (by rfl) ⟨214380, by rfl⟩ : syracuseStep 2286725 = 428761) (by norm_num)
theorem B3859589 : Blo 1524459 3859589 := bbase (se 4 (by rfl) ⟨361836, by rfl⟩ : syracuseStep 3859589 = 723673) (by norm_num)
theorem B2286749 : Blo 1524459 2286749 := bbase (se 3 (by rfl) ⟨428765, by rfl⟩ : syracuseStep 2286749 = 857531) (by norm_num)
theorem B2286773 : Blo 1524459 2286773 := bbase (se 5 (by rfl) ⟨107192, by rfl⟩ : syracuseStep 2286773 = 214385) (by norm_num)
theorem B3433661 : Blo 1524459 3433661 := bbase (se 3 (by rfl) ⟨643811, by rfl⟩ : syracuseStep 3433661 = 1287623) (by norm_num)
theorem B2172101 : Blo 1524459 2172101 := bbase (se 4 (by rfl) ⟨203634, by rfl⟩ : syracuseStep 2172101 = 407269) (by norm_num)
theorem B2286797 : Blo 1524459 2286797 := bbase (se 3 (by rfl) ⟨428774, by rfl⟩ : syracuseStep 2286797 = 857549) (by norm_num)
theorem B2573525 : Blo 1524459 2573525 := bbase (se 7 (by rfl) ⟨30158, by rfl⟩ : syracuseStep 2573525 = 60317) (by norm_num)
theorem B2286821 : Blo 1524459 2286821 := bbase (se 4 (by rfl) ⟨214389, by rfl⟩ : syracuseStep 2286821 = 428779) (by norm_num)
theorem B2286845 : Blo 1524459 2286845 := bbase (se 3 (by rfl) ⟨428783, by rfl⟩ : syracuseStep 2286845 = 857567) (by norm_num)
theorem B5793029 : Blo 1524459 5793029 := bbase (se 4 (by rfl) ⟨543096, by rfl⟩ : syracuseStep 5793029 = 1086193) (by norm_num)
theorem B3433733 : Blo 1524459 3433733 := bbase (se 4 (by rfl) ⟨321912, by rfl⟩ : syracuseStep 3433733 = 643825) (by norm_num)
theorem B7718165 : Blo 1524459 7718165 := bbase (se 6 (by rfl) ⟨180894, by rfl⟩ : syracuseStep 7718165 = 361789) (by norm_num)
theorem B2286869 : Blo 1524459 2286869 := bbase (se 6 (by rfl) ⟨53598, by rfl⟩ : syracuseStep 2286869 = 107197) (by norm_num)
theorem B2286893 : Blo 1524459 2286893 := bbase (se 3 (by rfl) ⟨428792, by rfl⟩ : syracuseStep 2286893 = 857585) (by norm_num)
theorem B2286917 : Blo 1524459 2286917 := bbase (se 4 (by rfl) ⟨214398, by rfl⟩ : syracuseStep 2286917 = 428797) (by norm_num)
theorem B3433805 : Blo 1524459 3433805 := bbase (se 3 (by rfl) ⟨643838, by rfl⟩ : syracuseStep 3433805 = 1287677) (by norm_num)
theorem B2573653 : Blo 1524459 2573653 := bbase (se 12 (by rfl) ⟨942, by rfl⟩ : syracuseStep 2573653 = 1885) (by norm_num)
theorem B2286941 : Blo 1524459 2286941 := bbase (se 3 (by rfl) ⟨428801, by rfl⟩ : syracuseStep 2286941 = 857603) (by norm_num)
theorem B2286965 : Blo 1524459 2286965 := bbase (se 5 (by rfl) ⟨107201, by rfl⟩ : syracuseStep 2286965 = 214403) (by norm_num)
theorem B2286989 : Blo 1524459 2286989 := bbase (se 3 (by rfl) ⟨428810, by rfl⟩ : syracuseStep 2286989 = 857621) (by norm_num)
theorem B3433877 : Blo 1524459 3433877 := bbase (se 6 (by rfl) ⟨80481, by rfl⟩ : syracuseStep 3433877 = 160963) (by norm_num)
theorem B3663269 : Blo 1524459 3663269 := bbase (se 4 (by rfl) ⟨343431, by rfl⟩ : syracuseStep 3663269 = 686863) (by norm_num)
theorem B2287013 : Blo 1524459 2287013 := bbase (se 4 (by rfl) ⟨214407, by rfl⟩ : syracuseStep 2287013 = 428815) (by norm_num)
theorem B2573741 : Blo 1524459 2573741 := bbase (se 3 (by rfl) ⟨482576, by rfl⟩ : syracuseStep 2573741 = 965153) (by norm_num)
theorem B5146037 : Blo 1524459 5146037 := bbase (se 5 (by rfl) ⟨241220, by rfl⟩ : syracuseStep 5146037 = 482441) (by norm_num)
theorem B12371381 : Blo 1524459 12371381 := bbase (se 5 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 12371381 = 1159817) (by norm_num)
theorem B2287037 : Blo 1524459 2287037 := bbase (se 3 (by rfl) ⟨428819, by rfl⟩ : syracuseStep 2287037 = 857639) (by norm_num)
theorem B2287061 : Blo 1524459 2287061 := bbase (se 7 (by rfl) ⟨26801, by rfl⟩ : syracuseStep 2287061 = 53603) (by norm_num)
theorem B3859933 : Blo 1524459 3859933 := bbase (se 3 (by rfl) ⟨723737, by rfl⟩ : syracuseStep 3859933 = 1447475) (by norm_num)
theorem B3433949 : Blo 1524459 3433949 := bbase (se 3 (by rfl) ⟨643865, by rfl⟩ : syracuseStep 3433949 = 1287731) (by norm_num)
theorem B2287085 : Blo 1524459 2287085 := bbase (se 3 (by rfl) ⟨428828, by rfl⟩ : syracuseStep 2287085 = 857657) (by norm_num)
theorem B2287109 : Blo 1524459 2287109 := bbase (se 4 (by rfl) ⟨214416, by rfl⟩ : syracuseStep 2287109 = 428833) (by norm_num)
theorem B2287133 : Blo 1524459 2287133 := bbase (se 3 (by rfl) ⟨428837, by rfl⟩ : syracuseStep 2287133 = 857675) (by norm_num)
theorem B3434021 : Blo 1524459 3434021 := bbase (se 4 (by rfl) ⟨321939, by rfl⟩ : syracuseStep 3434021 = 643879) (by norm_num)
theorem B2573869 : Blo 1524459 2573869 := bbase (se 3 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 2573869 = 965201) (by norm_num)
theorem B2287157 : Blo 1524459 2287157 := bbase (se 5 (by rfl) ⟨107210, by rfl⟩ : syracuseStep 2287157 = 214421) (by norm_num)
theorem B2287181 : Blo 1524459 2287181 := bbase (se 3 (by rfl) ⟨428846, by rfl⟩ : syracuseStep 2287181 = 857693) (by norm_num)
theorem B3860045 : Blo 1524459 3860045 := bbase (se 3 (by rfl) ⟨723758, by rfl⟩ : syracuseStep 3860045 = 1447517) (by norm_num)
theorem B2475605 : Blo 1524459 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B2442845 : Blo 1524459 2442845 := bbase (se 3 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 2442845 = 916067) (by norm_num)
theorem B3663461 : Blo 1524459 3663461 := bbase (se 4 (by rfl) ⟨343449, by rfl⟩ : syracuseStep 3663461 = 686899) (by norm_num)
theorem B2287205 : Blo 1524459 2287205 := bbase (se 4 (by rfl) ⟨214425, by rfl⟩ : syracuseStep 2287205 = 428851) (by norm_num)
theorem B3434093 : Blo 1524459 3434093 := bbase (se 3 (by rfl) ⟨643892, by rfl⟩ : syracuseStep 3434093 = 1287785) (by norm_num)
theorem B2287229 : Blo 1524459 2287229 := bbase (se 3 (by rfl) ⟨428855, by rfl⟩ : syracuseStep 2287229 = 857711) (by norm_num)
theorem B2573957 : Blo 1524459 2573957 := bbase (se 4 (by rfl) ⟨241308, by rfl⟩ : syracuseStep 2573957 = 482617) (by norm_num)
theorem B2287253 : Blo 1524459 2287253 := bbase (se 6 (by rfl) ⟨53607, by rfl⟩ : syracuseStep 2287253 = 107215) (by norm_num)
theorem B2287277 : Blo 1524459 2287277 := bbase (se 3 (by rfl) ⟨428864, by rfl⟩ : syracuseStep 2287277 = 857729) (by norm_num)
theorem B3434165 : Blo 1524459 3434165 := bbase (se 5 (by rfl) ⟨160976, by rfl⟩ : syracuseStep 3434165 = 321953) (by norm_num)
theorem B2287301 : Blo 1524459 2287301 := bbase (se 4 (by rfl) ⟨214434, by rfl⟩ : syracuseStep 2287301 = 428869) (by norm_num)
theorem B2287325 : Blo 1524459 2287325 := bbase (se 3 (by rfl) ⟨428873, by rfl⟩ : syracuseStep 2287325 = 857747) (by norm_num)
theorem B6604517 : Blo 1524459 6604517 := bbase (se 4 (by rfl) ⟨619173, by rfl⟩ : syracuseStep 6604517 = 1238347) (by norm_num)
theorem B2287349 : Blo 1524459 2287349 := bbase (se 5 (by rfl) ⟨107219, by rfl⟩ : syracuseStep 2287349 = 214439) (by norm_num)
theorem B3434237 : Blo 1524459 3434237 := bbase (se 3 (by rfl) ⟨643919, by rfl⟩ : syracuseStep 3434237 = 1287839) (by norm_num)
theorem B2574085 : Blo 1524459 2574085 := bbase (se 4 (by rfl) ⟨241320, by rfl⟩ : syracuseStep 2574085 = 482641) (by norm_num)
theorem B2287373 : Blo 1524459 2287373 := bbase (se 3 (by rfl) ⟨428882, by rfl⟩ : syracuseStep 2287373 = 857765) (by norm_num)
theorem B3860237 : Blo 1524459 3860237 := bbase (se 3 (by rfl) ⟨723794, by rfl⟩ : syracuseStep 3860237 = 1447589) (by norm_num)
theorem B1738513 : Blo 1524459 1738513 := bbase (se 2 (by rfl) ⟨651942, by rfl⟩ : syracuseStep 1738513 = 1303885) (by norm_num)
theorem B2287397 : Blo 1524459 2287397 := bbase (se 4 (by rfl) ⟨214443, by rfl⟩ : syracuseStep 2287397 = 428887) (by norm_num)
theorem B2287421 : Blo 1524459 2287421 := bbase (se 3 (by rfl) ⟨428891, by rfl⟩ : syracuseStep 2287421 = 857783) (by norm_num)
theorem B3434309 : Blo 1524459 3434309 := bbase (se 4 (by rfl) ⟨321966, by rfl⟩ : syracuseStep 3434309 = 643933) (by norm_num)
theorem B2287445 : Blo 1524459 2287445 := bbase (se 9 (by rfl) ⟨6701, by rfl⟩ : syracuseStep 2287445 = 13403) (by norm_num)
theorem B2574173 : Blo 1524459 2574173 := bbase (se 3 (by rfl) ⟨482657, by rfl⟩ : syracuseStep 2574173 = 965315) (by norm_num)
theorem B5146469 : Blo 1524459 5146469 := bbase (se 4 (by rfl) ⟨482481, by rfl⟩ : syracuseStep 5146469 = 964963) (by norm_num)
theorem B2287469 : Blo 1524459 2287469 := bbase (se 3 (by rfl) ⟨428900, by rfl⟩ : syracuseStep 2287469 = 857801) (by norm_num)
theorem B10438517 : Blo 1524459 10438517 := bbase (se 5 (by rfl) ⟨489305, by rfl⟩ : syracuseStep 10438517 = 978611) (by norm_num)
theorem B3663749 : Blo 1524459 3663749 := bbase (se 4 (by rfl) ⟨343476, by rfl⟩ : syracuseStep 3663749 = 686953) (by norm_num)
theorem B2287493 : Blo 1524459 2287493 := bbase (se 4 (by rfl) ⟨214452, by rfl⟩ : syracuseStep 2287493 = 428905) (by norm_num)
theorem B3434381 : Blo 1524459 3434381 := bbase (se 3 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 3434381 = 1287893) (by norm_num)
theorem B4343701 : Blo 1524459 4343701 := bbase (se 6 (by rfl) ⟨101805, by rfl⟩ : syracuseStep 4343701 = 203611) (by norm_num)
theorem B2287517 : Blo 1524459 2287517 := bbase (se 3 (by rfl) ⟨428909, by rfl⟩ : syracuseStep 2287517 = 857819) (by norm_num)
theorem B2287541 : Blo 1524459 2287541 := bbase (se 5 (by rfl) ⟨107228, by rfl⟩ : syracuseStep 2287541 = 214457) (by norm_num)
theorem B2172853 : Blo 1524459 2172853 := bbase (se 5 (by rfl) ⟨101852, by rfl⟩ : syracuseStep 2172853 = 203705) (by norm_num)
theorem B2287565 : Blo 1524459 2287565 := bbase (se 3 (by rfl) ⟨428918, by rfl⟩ : syracuseStep 2287565 = 857837) (by norm_num)
theorem B3434453 : Blo 1524459 3434453 := bbase (se 7 (by rfl) ⟨40247, by rfl⟩ : syracuseStep 3434453 = 80495) (by norm_num)
theorem B2574301 : Blo 1524459 2574301 := bbase (se 3 (by rfl) ⟨482681, by rfl⟩ : syracuseStep 2574301 = 965363) (by norm_num)
theorem B2287589 : Blo 1524459 2287589 := bbase (se 4 (by rfl) ⟨214461, by rfl⟩ : syracuseStep 2287589 = 428923) (by norm_num)
theorem B2287613 : Blo 1524459 2287613 := bbase (se 3 (by rfl) ⟨428927, by rfl⟩ : syracuseStep 2287613 = 857855) (by norm_num)
theorem B5646341 : Blo 1524459 5646341 := bbase (se 4 (by rfl) ⟨529344, by rfl⟩ : syracuseStep 5646341 = 1058689) (by norm_num)
theorem B2287637 : Blo 1524459 2287637 := bbase (se 6 (by rfl) ⟨53616, by rfl⟩ : syracuseStep 2287637 = 107233) (by norm_num)
theorem B3434525 : Blo 1524459 3434525 := bbase (se 3 (by rfl) ⟨643973, by rfl⟩ : syracuseStep 3434525 = 1287947) (by norm_num)
theorem B2443301 : Blo 1524459 2443301 := bbase (se 4 (by rfl) ⟨229059, by rfl⟩ : syracuseStep 2443301 = 458119) (by norm_num)
theorem B2287661 : Blo 1524459 2287661 := bbase (se 3 (by rfl) ⟨428936, by rfl⟩ : syracuseStep 2287661 = 857873) (by norm_num)
theorem B4343861 : Blo 1524459 4343861 := bbase (se 5 (by rfl) ⟨203618, by rfl⟩ : syracuseStep 4343861 = 407237) (by norm_num)
theorem B2574389 : Blo 1524459 2574389 := bbase (se 5 (by rfl) ⟨120674, by rfl⟩ : syracuseStep 2574389 = 241349) (by norm_num)
theorem B2287685 : Blo 1524459 2287685 := bbase (se 4 (by rfl) ⟨214470, by rfl⟩ : syracuseStep 2287685 = 428941) (by norm_num)
theorem B1738837 : Blo 1524459 1738837 := bbase (se 8 (by rfl) ⟨10188, by rfl⟩ : syracuseStep 1738837 = 20377) (by norm_num)
theorem B2476117 : Blo 1524459 2476117 := bbase (se 8 (by rfl) ⟨14508, by rfl⟩ : syracuseStep 2476117 = 29017) (by norm_num)
theorem B2287709 : Blo 1524459 2287709 := bbase (se 3 (by rfl) ⟨428945, by rfl⟩ : syracuseStep 2287709 = 857891) (by norm_num)
theorem B3860581 : Blo 1524459 3860581 := bbase (se 4 (by rfl) ⟨361929, by rfl⟩ : syracuseStep 3860581 = 723859) (by norm_num)
theorem B2287733 : Blo 1524459 2287733 := bbase (se 5 (by rfl) ⟨107237, by rfl⟩ : syracuseStep 2287733 = 214475) (by norm_num)
theorem B7727237 : Blo 1524459 7727237 := bbase (se 4 (by rfl) ⟨724428, by rfl⟩ : syracuseStep 7727237 = 1448857) (by norm_num)
theorem B2287757 : Blo 1524459 2287757 := bbase (se 3 (by rfl) ⟨428954, by rfl⟩ : syracuseStep 2287757 = 857909) (by norm_num)
theorem B2287781 : Blo 1524459 2287781 := bbase (se 4 (by rfl) ⟨214479, by rfl⟩ : syracuseStep 2287781 = 428959) (by norm_num)
theorem B2574517 : Blo 1524459 2574517 := bbase (se 5 (by rfl) ⟨120680, by rfl⟩ : syracuseStep 2574517 = 241361) (by norm_num)
theorem B2287805 : Blo 1524459 2287805 := bbase (se 3 (by rfl) ⟨428963, by rfl⟩ : syracuseStep 2287805 = 857927) (by norm_num)
theorem B3860693 : Blo 1524459 3860693 := bbase (se 7 (by rfl) ⟨45242, by rfl⟩ : syracuseStep 3860693 = 90485) (by norm_num)
theorem B2287829 : Blo 1524459 2287829 := bbase (se 7 (by rfl) ⟨26810, by rfl⟩ : syracuseStep 2287829 = 53621) (by norm_num)
theorem B2287853 : Blo 1524459 2287853 := bbase (se 3 (by rfl) ⟨428972, by rfl⟩ : syracuseStep 2287853 = 857945) (by norm_num)
theorem B1984757 : Blo 1524459 1984757 := bbase (se 5 (by rfl) ⟨93035, by rfl⟩ : syracuseStep 1984757 = 186071) (by norm_num)
theorem B2287877 : Blo 1524459 2287877 := bbase (se 4 (by rfl) ⟨214488, by rfl⟩ : syracuseStep 2287877 = 428977) (by norm_num)
theorem B2574605 : Blo 1524459 2574605 := bbase (se 3 (by rfl) ⟨482738, by rfl⟩ : syracuseStep 2574605 = 965477) (by norm_num)
theorem B5146901 : Blo 1524459 5146901 := bbase (se 6 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 5146901 = 241261) (by norm_num)
theorem B2287901 : Blo 1524459 2287901 := bbase (se 3 (by rfl) ⟨428981, by rfl⟩ : syracuseStep 2287901 = 857963) (by norm_num)
theorem B4344101 : Blo 1524459 4344101 := bbase (se 4 (by rfl) ⟨407259, by rfl⟩ : syracuseStep 4344101 = 814519) (by norm_num)
theorem B2287925 : Blo 1524459 2287925 := bbase (se 5 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 2287925 = 214493) (by norm_num)
theorem B2287949 : Blo 1524459 2287949 := bbase (se 3 (by rfl) ⟨428990, by rfl⟩ : syracuseStep 2287949 = 857981) (by norm_num)
theorem B2287973 : Blo 1524459 2287973 := bbase (se 4 (by rfl) ⟨214497, by rfl⟩ : syracuseStep 2287973 = 428995) (by norm_num)
theorem B2287997 : Blo 1524459 2287997 := bbase (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) (by norm_num)
theorem B2894221 : Blo 1524459 2894221 := bbase (se 3 (by rfl) ⟨542666, by rfl⟩ : syracuseStep 2894221 = 1085333) (by norm_num)
theorem B2574733 : Blo 1524459 2574733 := bbase (se 3 (by rfl) ⟨482762, by rfl⟩ : syracuseStep 2574733 = 965525) (by norm_num)
theorem B3860885 : Blo 1524459 3860885 := bbase (se 6 (by rfl) ⟨90489, by rfl⟩ : syracuseStep 3860885 = 180979) (by norm_num)
theorem B2288021 : Blo 1524459 2288021 := bbase (se 6 (by rfl) ⟨53625, by rfl⟩ : syracuseStep 2288021 = 107251) (by norm_num)
theorem B5794213 : Blo 1524459 5794213 := bbase (se 4 (by rfl) ⟨543207, by rfl⟩ : syracuseStep 5794213 = 1086415) (by norm_num)
theorem B2288045 : Blo 1524459 2288045 := bbase (se 3 (by rfl) ⟨429008, by rfl⟩ : syracuseStep 2288045 = 858017) (by norm_num)
theorem B2288069 : Blo 1524459 2288069 := bbase (se 4 (by rfl) ⟨214506, by rfl⟩ : syracuseStep 2288069 = 429013) (by norm_num)
theorem B2288093 : Blo 1524459 2288093 := bbase (se 3 (by rfl) ⟨429017, by rfl⟩ : syracuseStep 2288093 = 858035) (by norm_num)
theorem B4344293 : Blo 1524459 4344293 := bbase (se 4 (by rfl) ⟨407277, by rfl⟩ : syracuseStep 4344293 = 814555) (by norm_num)
theorem B2574821 : Blo 1524459 2574821 := bbase (se 4 (by rfl) ⟨241389, by rfl⟩ : syracuseStep 2574821 = 482779) (by norm_num)
theorem B2288117 : Blo 1524459 2288117 := bbase (se 5 (by rfl) ⟨107255, by rfl⟩ : syracuseStep 2288117 = 214511) (by norm_num)
theorem B2288141 : Blo 1524459 2288141 := bbase (se 3 (by rfl) ⟨429026, by rfl⟩ : syracuseStep 2288141 = 858053) (by norm_num)
theorem B7719461 : Blo 1524459 7719461 := bbase (se 4 (by rfl) ⟨723699, by rfl⟩ : syracuseStep 7719461 = 1447399) (by norm_num)
theorem B2288165 : Blo 1524459 2288165 := bbase (se 4 (by rfl) ⟨214515, by rfl⟩ : syracuseStep 2288165 = 429031) (by norm_num)
theorem B2288189 : Blo 1524459 2288189 := bbase (se 3 (by rfl) ⟨429035, by rfl⟩ : syracuseStep 2288189 = 858071) (by norm_num)
theorem B3525205 : Blo 1524459 3525205 := bbase (se 8 (by rfl) ⟨20655, by rfl⟩ : syracuseStep 3525205 = 41311) (by norm_num)
theorem B2288213 : Blo 1524459 2288213 := bbase (se 8 (by rfl) ⟨13407, by rfl⟩ : syracuseStep 2288213 = 26815) (by norm_num)
theorem B2574949 : Blo 1524459 2574949 := bbase (se 4 (by rfl) ⟨241401, by rfl⟩ : syracuseStep 2574949 = 482803) (by norm_num)
theorem B2288237 : Blo 1524459 2288237 := bbase (se 3 (by rfl) ⟨429044, by rfl⟩ : syracuseStep 2288237 = 858089) (by norm_num)
theorem B4123253 : Blo 1524459 4123253 := bbase (se 5 (by rfl) ⟨193277, by rfl⟩ : syracuseStep 4123253 = 386555) (by norm_num)
theorem B2288261 : Blo 1524459 2288261 := bbase (se 4 (by rfl) ⟨214524, by rfl⟩ : syracuseStep 2288261 = 429049) (by norm_num)
theorem B2288285 : Blo 1524459 2288285 := bbase (se 3 (by rfl) ⟨429053, by rfl⟩ : syracuseStep 2288285 = 858107) (by norm_num)
theorem B2288309 : Blo 1524459 2288309 := bbase (se 5 (by rfl) ⟨107264, by rfl⟩ : syracuseStep 2288309 = 214529) (by norm_num)
theorem B2894525 : Blo 1524459 2894525 := bbase (se 3 (by rfl) ⟨542723, by rfl⟩ : syracuseStep 2894525 = 1085447) (by norm_num)
theorem B2575037 : Blo 1524459 2575037 := bbase (se 3 (by rfl) ⟨482819, by rfl⟩ : syracuseStep 2575037 = 965639) (by norm_num)
theorem B5147333 : Blo 1524459 5147333 := bbase (se 4 (by rfl) ⟨482562, by rfl⟩ : syracuseStep 5147333 = 965125) (by norm_num)
theorem B2288333 : Blo 1524459 2288333 := bbase (se 3 (by rfl) ⟨429062, by rfl⟩ : syracuseStep 2288333 = 858125) (by norm_num)
theorem B5794517 : Blo 1524459 5794517 := bbase (se 7 (by rfl) ⟨67904, by rfl⟩ : syracuseStep 5794517 = 135809) (by norm_num)
theorem B2288357 : Blo 1524459 2288357 := bbase (se 4 (by rfl) ⟨214533, by rfl⟩ : syracuseStep 2288357 = 429067) (by norm_num)
theorem B3304165 : Blo 1524459 3304165 := bbase (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) (by norm_num)
theorem B3861229 : Blo 1524459 3861229 := bbase (se 3 (by rfl) ⟨723980, by rfl⟩ : syracuseStep 3861229 = 1447961) (by norm_num)
theorem B2288381 : Blo 1524459 2288381 := bbase (se 3 (by rfl) ⟨429071, by rfl⟩ : syracuseStep 2288381 = 858143) (by norm_num)
theorem B2288405 : Blo 1524459 2288405 := bbase (se 6 (by rfl) ⟨53634, by rfl⟩ : syracuseStep 2288405 = 107269) (by norm_num)
theorem B2288429 : Blo 1524459 2288429 := bbase (se 3 (by rfl) ⟨429080, by rfl⟩ : syracuseStep 2288429 = 858161) (by norm_num)
theorem B2575165 : Blo 1524459 2575165 := bbase (se 3 (by rfl) ⟨482843, by rfl⟩ : syracuseStep 2575165 = 965687) (by norm_num)
theorem B2288453 : Blo 1524459 2288453 := bbase (se 4 (by rfl) ⟨214542, by rfl⟩ : syracuseStep 2288453 = 429085) (by norm_num)
theorem B1715017 : Blo 1524459 1715017 := bbase (se 2 (by rfl) ⟨643131, by rfl⟩ : syracuseStep 1715017 = 1286263) (by norm_num)
theorem B3861341 : Blo 1524459 3861341 := bbase (se 3 (by rfl) ⟨724001, by rfl⟩ : syracuseStep 3861341 = 1448003) (by norm_num)
theorem B2288477 : Blo 1524459 2288477 := bbase (se 3 (by rfl) ⟨429089, by rfl⟩ : syracuseStep 2288477 = 858179) (by norm_num)
theorem B2476901 : Blo 1524459 2476901 := bbase (se 4 (by rfl) ⟨232209, by rfl⟩ : syracuseStep 2476901 = 464419) (by norm_num)
theorem B1715053 : Blo 1524459 1715053 := bbase (se 3 (by rfl) ⟨321572, by rfl⟩ : syracuseStep 1715053 = 643145) (by norm_num)
theorem B2288501 : Blo 1524459 2288501 := bbase (se 5 (by rfl) ⟨107273, by rfl⟩ : syracuseStep 2288501 = 214547) (by norm_num)
theorem B2288525 : Blo 1524459 2288525 := bbase (se 3 (by rfl) ⟨429098, by rfl⟩ : syracuseStep 2288525 = 858197) (by norm_num)
theorem B1715089 : Blo 1524459 1715089 := bbase (se 2 (by rfl) ⟨643158, by rfl⟩ : syracuseStep 1715089 = 1286317) (by norm_num)
theorem B2575253 : Blo 1524459 2575253 := bbase (se 6 (by rfl) ⟨60357, by rfl⟩ : syracuseStep 2575253 = 120715) (by norm_num)
theorem B2288549 : Blo 1524459 2288549 := bbase (se 4 (by rfl) ⟨214551, by rfl⟩ : syracuseStep 2288549 = 429103) (by norm_num)
theorem B1715125 : Blo 1524459 1715125 := bbase (se 5 (by rfl) ⟨80396, by rfl⟩ : syracuseStep 1715125 = 160793) (by norm_num)
theorem B2288573 : Blo 1524459 2288573 := bbase (se 3 (by rfl) ⟨429107, by rfl⟩ : syracuseStep 2288573 = 858215) (by norm_num)
theorem B2288597 : Blo 1524459 2288597 := bbase (se 7 (by rfl) ⟨26819, by rfl⟩ : syracuseStep 2288597 = 53639) (by norm_num)
theorem B1715161 : Blo 1524459 1715161 := bbase (se 2 (by rfl) ⟨643185, by rfl⟩ : syracuseStep 1715161 = 1286371) (by norm_num)
theorem B2288621 : Blo 1524459 2288621 := bbase (se 3 (by rfl) ⟨429116, by rfl⟩ : syracuseStep 2288621 = 858233) (by norm_num)
theorem B1715197 : Blo 1524459 1715197 := bbase (se 3 (by rfl) ⟨321599, by rfl⟩ : syracuseStep 1715197 = 643199) (by norm_num)
theorem B2288645 : Blo 1524459 2288645 := bbase (se 4 (by rfl) ⟨214560, by rfl⟩ : syracuseStep 2288645 = 429121) (by norm_num)
theorem B2575381 : Blo 1524459 2575381 := bbase (se 6 (by rfl) ⟨60360, by rfl⟩ : syracuseStep 2575381 = 120721) (by norm_num)
theorem B3861533 : Blo 1524459 3861533 := bbase (se 3 (by rfl) ⟨724037, by rfl⟩ : syracuseStep 3861533 = 1448075) (by norm_num)
theorem B2288669 : Blo 1524459 2288669 := bbase (se 3 (by rfl) ⟨429125, by rfl⟩ : syracuseStep 2288669 = 858251) (by norm_num)
theorem B1715233 : Blo 1524459 1715233 := bbase (se 2 (by rfl) ⟨643212, by rfl⟩ : syracuseStep 1715233 = 1286425) (by norm_num)
theorem B1567793 : Blo 1524459 1567793 := bbase (se 2 (by rfl) ⟨587922, by rfl⟩ : syracuseStep 1567793 = 1175845) (by norm_num)
theorem B2288693 : Blo 1524459 2288693 := bbase (se 5 (by rfl) ⟨107282, by rfl⟩ : syracuseStep 2288693 = 214565) (by norm_num)
theorem B1715269 : Blo 1524459 1715269 := bbase (se 4 (by rfl) ⟨160806, by rfl⟩ : syracuseStep 1715269 = 321613) (by norm_num)
theorem B2288717 : Blo 1524459 2288717 := bbase (se 3 (by rfl) ⟨429134, by rfl⟩ : syracuseStep 2288717 = 858269) (by norm_num)
theorem B3091549 : Blo 1524459 3091549 := bbase (se 3 (by rfl) ⟨579665, by rfl⟩ : syracuseStep 3091549 = 1159331) (by norm_num)
theorem B2288741 : Blo 1524459 2288741 := bbase (se 4 (by rfl) ⟨214569, by rfl⟩ : syracuseStep 2288741 = 429139) (by norm_num)
theorem B1715305 : Blo 1524459 1715305 := bbase (se 2 (by rfl) ⟨643239, by rfl⟩ : syracuseStep 1715305 = 1286479) (by norm_num)
theorem B2575469 : Blo 1524459 2575469 := bbase (se 3 (by rfl) ⟨482900, by rfl⟩ : syracuseStep 2575469 = 965801) (by norm_num)
theorem B5147765 : Blo 1524459 5147765 := bbase (se 5 (by rfl) ⟨241301, by rfl⟩ : syracuseStep 5147765 = 482603) (by norm_num)
theorem B2288765 : Blo 1524459 2288765 := bbase (se 3 (by rfl) ⟨429143, by rfl⟩ : syracuseStep 2288765 = 858287) (by norm_num)
theorem B1715341 : Blo 1524459 1715341 := bbase (se 3 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 1715341 = 643253) (by norm_num)
theorem B2288789 : Blo 1524459 2288789 := bbase (se 6 (by rfl) ⟨53643, by rfl⟩ : syracuseStep 2288789 = 107287) (by norm_num)
theorem B2288813 : Blo 1524459 2288813 := bbase (se 3 (by rfl) ⟨429152, by rfl⟩ : syracuseStep 2288813 = 858305) (by norm_num)
theorem B1715377 : Blo 1524459 1715377 := bbase (se 2 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 1715377 = 1286533) (by norm_num)
theorem B6515893 : Blo 1524459 6515893 := bbase (se 5 (by rfl) ⟨305432, by rfl⟩ : syracuseStep 6515893 = 610865) (by norm_num)
theorem B2288837 : Blo 1524459 2288837 := bbase (se 4 (by rfl) ⟨214578, by rfl⟩ : syracuseStep 2288837 = 429157) (by norm_num)
theorem B4885717 : Blo 1524459 4885717 := bbase (se 7 (by rfl) ⟨57254, by rfl⟩ : syracuseStep 4885717 = 114509) (by norm_num)
theorem B1715413 : Blo 1524459 1715413 := bbase (se 7 (by rfl) ⟨20102, by rfl⟩ : syracuseStep 1715413 = 40205) (by norm_num)
theorem B2288861 : Blo 1524459 2288861 := bbase (se 3 (by rfl) ⟨429161, by rfl⟩ : syracuseStep 2288861 = 858323) (by norm_num)
theorem B2575597 : Blo 1524459 2575597 := bbase (se 3 (by rfl) ⟨482924, by rfl⟩ : syracuseStep 2575597 = 965849) (by norm_num)
theorem B2288885 : Blo 1524459 2288885 := bbase (se 5 (by rfl) ⟨107291, by rfl⟩ : syracuseStep 2288885 = 214583) (by norm_num)
theorem B1715449 : Blo 1524459 1715449 := bbase (se 2 (by rfl) ⟨643293, by rfl⟩ : syracuseStep 1715449 = 1286587) (by norm_num)
theorem B2288909 : Blo 1524459 2288909 := bbase (se 3 (by rfl) ⟨429170, by rfl⟩ : syracuseStep 2288909 = 858341) (by norm_num)
theorem B1715485 : Blo 1524459 1715485 := bbase (se 3 (by rfl) ⟨321653, by rfl⟩ : syracuseStep 1715485 = 643307) (by norm_num)
theorem B2288933 : Blo 1524459 2288933 := bbase (se 4 (by rfl) ⟨214587, by rfl⟩ : syracuseStep 2288933 = 429175) (by norm_num)
theorem B2288957 : Blo 1524459 2288957 := bbase (se 3 (by rfl) ⟨429179, by rfl⟩ : syracuseStep 2288957 = 858359) (by norm_num)
theorem B1715521 : Blo 1524459 1715521 := bbase (se 2 (by rfl) ⟨643320, by rfl⟩ : syracuseStep 1715521 = 1286641) (by norm_num)
theorem B2575685 : Blo 1524459 2575685 := bbase (se 4 (by rfl) ⟨241470, by rfl⟩ : syracuseStep 2575685 = 482941) (by norm_num)
theorem B2288981 : Blo 1524459 2288981 := bbase (se 11 (by rfl) ⟨1676, by rfl⟩ : syracuseStep 2288981 = 3353) (by norm_num)
theorem B1715557 : Blo 1524459 1715557 := bbase (se 4 (by rfl) ⟨160833, by rfl⟩ : syracuseStep 1715557 = 321667) (by norm_num)
theorem B2289005 : Blo 1524459 2289005 := bbase (se 3 (by rfl) ⟨429188, by rfl⟩ : syracuseStep 2289005 = 858377) (by norm_num)
theorem B3861877 : Blo 1524459 3861877 := bbase (se 5 (by rfl) ⟨181025, by rfl⟩ : syracuseStep 3861877 = 362051) (by norm_num)
theorem B2289029 : Blo 1524459 2289029 := bbase (se 4 (by rfl) ⟨214596, by rfl⟩ : syracuseStep 2289029 = 429193) (by norm_num)
theorem B1715593 : Blo 1524459 1715593 := bbase (se 2 (by rfl) ⟨643347, by rfl⟩ : syracuseStep 1715593 = 1286695) (by norm_num)
theorem B13036949 : Blo 1524459 13036949 := bbase (se 6 (by rfl) ⟨305553, by rfl⟩ : syracuseStep 13036949 = 611107) (by norm_num)
theorem B2289053 : Blo 1524459 2289053 := bbase (se 3 (by rfl) ⟨429197, by rfl⟩ : syracuseStep 2289053 = 858395) (by norm_num)
theorem B1715629 : Blo 1524459 1715629 := bbase (se 3 (by rfl) ⟨321680, by rfl⟩ : syracuseStep 1715629 = 643361) (by norm_num)
theorem B2895277 : Blo 1524459 2895277 := bbase (se 3 (by rfl) ⟨542864, by rfl⟩ : syracuseStep 2895277 = 1085729) (by norm_num)
theorem B2444717 : Blo 1524459 2444717 := bbase (se 3 (by rfl) ⟨458384, by rfl⟩ : syracuseStep 2444717 = 916769) (by norm_num)
theorem B2289077 : Blo 1524459 2289077 := bbase (se 5 (by rfl) ⟨107300, by rfl⟩ : syracuseStep 2289077 = 214601) (by norm_num)
theorem B4345285 : Blo 1524459 4345285 := bbase (se 4 (by rfl) ⟨407370, by rfl⟩ : syracuseStep 4345285 = 814741) (by norm_num)
theorem B2575813 : Blo 1524459 2575813 := bbase (se 4 (by rfl) ⟨241482, by rfl⟩ : syracuseStep 2575813 = 482965) (by norm_num)
theorem B2289101 : Blo 1524459 2289101 := bbase (se 3 (by rfl) ⟨429206, by rfl⟩ : syracuseStep 2289101 = 858413) (by norm_num)
theorem B1715665 : Blo 1524459 1715665 := bbase (se 2 (by rfl) ⟨643374, by rfl⟩ : syracuseStep 1715665 = 1286749) (by norm_num)
theorem B3861989 : Blo 1524459 3861989 := bbase (se 4 (by rfl) ⟨362061, by rfl⟩ : syracuseStep 3861989 = 724123) (by norm_num)
theorem B2289125 : Blo 1524459 2289125 := bbase (se 4 (by rfl) ⟨214605, by rfl⟩ : syracuseStep 2289125 = 429211) (by norm_num)
theorem B1715701 : Blo 1524459 1715701 := bbase (se 5 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 1715701 = 160847) (by norm_num)
theorem B2289149 : Blo 1524459 2289149 := bbase (se 3 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 2289149 = 858431) (by norm_num)
theorem B2289173 : Blo 1524459 2289173 := bbase (se 6 (by rfl) ⟨53652, by rfl⟩ : syracuseStep 2289173 = 107305) (by norm_num)
theorem B1715737 : Blo 1524459 1715737 := bbase (se 2 (by rfl) ⟨643401, by rfl⟩ : syracuseStep 1715737 = 1286803) (by norm_num)
theorem B2575901 : Blo 1524459 2575901 := bbase (se 3 (by rfl) ⟨482981, by rfl⟩ : syracuseStep 2575901 = 965963) (by norm_num)
theorem B5148197 : Blo 1524459 5148197 := bbase (se 4 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 5148197 = 965287) (by norm_num)
theorem B2289197 : Blo 1524459 2289197 := bbase (se 3 (by rfl) ⟨429224, by rfl⟩ : syracuseStep 2289197 = 858449) (by norm_num)
theorem B1715773 : Blo 1524459 1715773 := bbase (se 3 (by rfl) ⟨321707, by rfl⟩ : syracuseStep 1715773 = 643415) (by norm_num)
theorem B2895421 : Blo 1524459 2895421 := bbase (se 3 (by rfl) ⟨542891, by rfl⟩ : syracuseStep 2895421 = 1085783) (by norm_num)
theorem B2289221 : Blo 1524459 2289221 := bbase (se 4 (by rfl) ⟨214614, by rfl⟩ : syracuseStep 2289221 = 429229) (by norm_num)
theorem B29724245 : Blo 1524459 29724245 := bbase (se 8 (by rfl) ⟨174165, by rfl⟩ : syracuseStep 29724245 = 348331) (by norm_num)
theorem B2936405 : Blo 1524459 2936405 := bbase (se 8 (by rfl) ⟨17205, by rfl⟩ : syracuseStep 2936405 = 34411) (by norm_num)
theorem B2289245 : Blo 1524459 2289245 := bbase (se 3 (by rfl) ⟨429233, by rfl⟩ : syracuseStep 2289245 = 858467) (by norm_num)
theorem B1715809 : Blo 1524459 1715809 := bbase (se 2 (by rfl) ⟨643428, by rfl⟩ : syracuseStep 1715809 = 1286857) (by norm_num)
theorem B3092069 : Blo 1524459 3092069 := bbase (se 4 (by rfl) ⟨289881, by rfl⟩ : syracuseStep 3092069 = 579763) (by norm_num)
theorem B2289269 : Blo 1524459 2289269 := bbase (se 5 (by rfl) ⟨107309, by rfl⟩ : syracuseStep 2289269 = 214619) (by norm_num)
theorem B1715845 : Blo 1524459 1715845 := bbase (se 4 (by rfl) ⟨160860, by rfl⟩ : syracuseStep 1715845 = 321721) (by norm_num)
theorem B2289293 : Blo 1524459 2289293 := bbase (se 3 (by rfl) ⟨429242, by rfl⟩ : syracuseStep 2289293 = 858485) (by norm_num)
theorem B2444941 : Blo 1524459 2444941 := bbase (se 3 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 2444941 = 916853) (by norm_num)
theorem B3255965 : Blo 1524459 3255965 := bbase (se 3 (by rfl) ⟨610493, by rfl⟩ : syracuseStep 3255965 = 1220987) (by norm_num)
theorem B3862181 : Blo 1524459 3862181 := bbase (se 4 (by rfl) ⟨362079, by rfl⟩ : syracuseStep 3862181 = 724159) (by norm_num)
theorem B2289317 : Blo 1524459 2289317 := bbase (se 4 (by rfl) ⟨214623, by rfl⟩ : syracuseStep 2289317 = 429247) (by norm_num)
theorem B1715881 : Blo 1524459 1715881 := bbase (se 2 (by rfl) ⟨643455, by rfl⟩ : syracuseStep 1715881 = 1286911) (by norm_num)
theorem B2289341 : Blo 1524459 2289341 := bbase (se 3 (by rfl) ⟨429251, by rfl⟩ : syracuseStep 2289341 = 858503) (by norm_num)
theorem B4181701 : Blo 1524459 4181701 := bbase (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) (by norm_num)
theorem B1715917 : Blo 1524459 1715917 := bbase (se 3 (by rfl) ⟨321734, by rfl⟩ : syracuseStep 1715917 = 643469) (by norm_num)
theorem B8244949 : Blo 1524459 8244949 := bbase (se 7 (by rfl) ⟨96620, by rfl⟩ : syracuseStep 8244949 = 193241) (by norm_num)
theorem B2289365 : Blo 1524459 2289365 := bbase (se 7 (by rfl) ⟨26828, by rfl⟩ : syracuseStep 2289365 = 53657) (by norm_num)
theorem B2895581 : Blo 1524459 2895581 := bbase (se 3 (by rfl) ⟨542921, by rfl⟩ : syracuseStep 2895581 = 1085843) (by norm_num)
theorem B2289389 : Blo 1524459 2289389 := bbase (se 3 (by rfl) ⟨429260, by rfl⟩ : syracuseStep 2289389 = 858521) (by norm_num)
theorem B1715953 : Blo 1524459 1715953 := bbase (se 2 (by rfl) ⟨643482, by rfl⟩ : syracuseStep 1715953 = 1286965) (by norm_num)
theorem B3092213 : Blo 1524459 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B6270709 : Blo 1524459 6270709 := bbase (se 5 (by rfl) ⟨293939, by rfl⟩ : syracuseStep 6270709 = 587879) (by norm_num)
theorem B2289413 : Blo 1524459 2289413 := bbase (se 4 (by rfl) ⟨214632, by rfl⟩ : syracuseStep 2289413 = 429265) (by norm_num)
theorem B1715989 : Blo 1524459 1715989 := bbase (se 6 (by rfl) ⟨40218, by rfl⟩ : syracuseStep 1715989 = 80437) (by norm_num)
theorem B2289437 : Blo 1524459 2289437 := bbase (se 3 (by rfl) ⟨429269, by rfl⟩ : syracuseStep 2289437 = 858539) (by norm_num)
theorem B7720757 : Blo 1524459 7720757 := bbase (se 5 (by rfl) ⟨361910, by rfl⟩ : syracuseStep 7720757 = 723821) (by norm_num)
theorem B2289461 : Blo 1524459 2289461 := bbase (se 5 (by rfl) ⟨107318, by rfl⟩ : syracuseStep 2289461 = 214637) (by norm_num)
theorem B1716025 : Blo 1524459 1716025 := bbase (se 2 (by rfl) ⟨643509, by rfl⟩ : syracuseStep 1716025 = 1287019) (by norm_num)
theorem B2289485 : Blo 1524459 2289485 := bbase (se 3 (by rfl) ⟨429278, by rfl⟩ : syracuseStep 2289485 = 858557) (by norm_num)
theorem B3665749 : Blo 1524459 3665749 := bbase (se 9 (by rfl) ⟨10739, by rfl⟩ : syracuseStep 3665749 = 21479) (by norm_num)
theorem B1740629 : Blo 1524459 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1716061 : Blo 1524459 1716061 := bbase (se 3 (by rfl) ⟨321761, by rfl⟩ : syracuseStep 1716061 = 643523) (by norm_num)
theorem B2289509 : Blo 1524459 2289509 := bbase (se 4 (by rfl) ⟨214641, by rfl⟩ : syracuseStep 2289509 = 429283) (by norm_num)
theorem B2895725 : Blo 1524459 2895725 := bbase (se 3 (by rfl) ⟨542948, by rfl⟩ : syracuseStep 2895725 = 1085897) (by norm_num)
theorem B2289533 : Blo 1524459 2289533 := bbase (se 3 (by rfl) ⟨429287, by rfl⟩ : syracuseStep 2289533 = 858575) (by norm_num)
theorem B1716097 : Blo 1524459 1716097 := bbase (se 2 (by rfl) ⟨643536, by rfl⟩ : syracuseStep 1716097 = 1287073) (by norm_num)
theorem B2289557 : Blo 1524459 2289557 := bbase (se 6 (by rfl) ⟨53661, by rfl⟩ : syracuseStep 2289557 = 107323) (by norm_num)
theorem B1716133 : Blo 1524459 1716133 := bbase (se 4 (by rfl) ⟨160887, by rfl⟩ : syracuseStep 1716133 = 321775) (by norm_num)
theorem B2289581 : Blo 1524459 2289581 := bbase (se 3 (by rfl) ⟨429296, by rfl⟩ : syracuseStep 2289581 = 858593) (by norm_num)
theorem B2289605 : Blo 1524459 2289605 := bbase (se 4 (by rfl) ⟨214650, by rfl⟩ : syracuseStep 2289605 = 429301) (by norm_num)
theorem B1716169 : Blo 1524459 1716169 := bbase (se 2 (by rfl) ⟨643563, by rfl⟩ : syracuseStep 1716169 = 1287127) (by norm_num)
theorem B34344917 : Blo 1524459 34344917 := bbase (se 7 (by rfl) ⟨402479, by rfl⟩ : syracuseStep 34344917 = 804959) (by norm_num)
theorem B5148629 : Blo 1524459 5148629 := bbase (se 7 (by rfl) ⟨60335, by rfl⟩ : syracuseStep 5148629 = 120671) (by norm_num)
theorem B35229653 : Blo 1524459 35229653 := bbase (se 7 (by rfl) ⟨412847, by rfl⟩ : syracuseStep 35229653 = 825695) (by norm_num)
theorem B2289629 : Blo 1524459 2289629 := bbase (se 3 (by rfl) ⟨429305, by rfl⟩ : syracuseStep 2289629 = 858611) (by norm_num)
theorem B1716205 : Blo 1524459 1716205 := bbase (se 3 (by rfl) ⟨321788, by rfl⟩ : syracuseStep 1716205 = 643577) (by norm_num)
theorem B14651381 : Blo 1524459 14651381 := bbase (se 5 (by rfl) ⟨686783, by rfl⟩ : syracuseStep 14651381 = 1373567) (by norm_num)
theorem B2289653 : Blo 1524459 2289653 := bbase (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) (by norm_num)
theorem B3862525 : Blo 1524459 3862525 := bbase (se 3 (by rfl) ⟨724223, by rfl⟩ : syracuseStep 3862525 = 1448447) (by norm_num)
theorem B2289677 : Blo 1524459 2289677 := bbase (se 3 (by rfl) ⟨429314, by rfl⟩ : syracuseStep 2289677 = 858629) (by norm_num)
theorem B1716241 : Blo 1524459 1716241 := bbase (se 2 (by rfl) ⟨643590, by rfl⟩ : syracuseStep 1716241 = 1287181) (by norm_num)
theorem B8802325 : Blo 1524459 8802325 := bbase (se 6 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 8802325 = 412609) (by norm_num)
theorem B1716277 : Blo 1524459 1716277 := bbase (se 5 (by rfl) ⟨80450, by rfl⟩ : syracuseStep 1716277 = 160901) (by norm_num)
theorem B1716313 : Blo 1524459 1716313 := bbase (se 2 (by rfl) ⟨643617, by rfl⟩ : syracuseStep 1716313 = 1287235) (by norm_num)
theorem B3862637 : Blo 1524459 3862637 := bbase (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) (by norm_num)
theorem B1716349 : Blo 1524459 1716349 := bbase (se 3 (by rfl) ⟨321815, by rfl⟩ : syracuseStep 1716349 = 643631) (by norm_num)
theorem B2896013 : Blo 1524459 2896013 := bbase (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) (by norm_num)
theorem B1716385 : Blo 1524459 1716385 := bbase (se 2 (by rfl) ⟨643644, by rfl⟩ : syracuseStep 1716385 = 1287289) (by norm_num)
theorem B1716421 : Blo 1524459 1716421 := bbase (se 4 (by rfl) ⟨160914, by rfl⟩ : syracuseStep 1716421 = 321829) (by norm_num)
theorem B1716457 : Blo 1524459 1716457 := bbase (se 2 (by rfl) ⟨643671, by rfl⟩ : syracuseStep 1716457 = 1287343) (by norm_num)
theorem B4403461 : Blo 1524459 4403461 := bbase (se 4 (by rfl) ⟨412824, by rfl⟩ : syracuseStep 4403461 = 825649) (by norm_num)
theorem B5501189 : Blo 1524459 5501189 := bbase (se 4 (by rfl) ⟨515736, by rfl⟩ : syracuseStep 5501189 = 1031473) (by norm_num)
theorem B1716493 : Blo 1524459 1716493 := bbase (se 3 (by rfl) ⟨321842, by rfl⟩ : syracuseStep 1716493 = 643685) (by norm_num)
theorem B2896165 : Blo 1524459 2896165 := bbase (se 4 (by rfl) ⟨271515, by rfl⟩ : syracuseStep 2896165 = 543031) (by norm_num)
theorem B3911981 : Blo 1524459 3911981 := bbase (se 3 (by rfl) ⟨733496, by rfl⟩ : syracuseStep 3911981 = 1466993) (by norm_num)
theorem B3862829 : Blo 1524459 3862829 := bbase (se 3 (by rfl) ⟨724280, by rfl⟩ : syracuseStep 3862829 = 1448561) (by norm_num)
theorem B1929521 : Blo 1524459 1929521 := bbase (se 2 (by rfl) ⟨723570, by rfl⟩ : syracuseStep 1929521 = 1447141) (by norm_num)
theorem B1716529 : Blo 1524459 1716529 := bbase (se 2 (by rfl) ⟨643698, by rfl⟩ : syracuseStep 1716529 = 1287397) (by norm_num)
theorem B1716565 : Blo 1524459 1716565 := bbase (se 10 (by rfl) ⟨2514, by rfl⟩ : syracuseStep 1716565 = 5029) (by norm_num)
theorem B1929577 : Blo 1524459 1929577 := bbase (se 2 (by rfl) ⟨723591, by rfl⟩ : syracuseStep 1929577 = 1447183) (by norm_num)
theorem B1716601 : Blo 1524459 1716601 := bbase (se 2 (by rfl) ⟨643725, by rfl⟩ : syracuseStep 1716601 = 1287451) (by norm_num)
theorem B5149061 : Blo 1524459 5149061 := bbase (se 4 (by rfl) ⟨482724, by rfl⟩ : syracuseStep 5149061 = 965449) (by norm_num)
theorem B2748829 : Blo 1524459 2748829 := bbase (se 3 (by rfl) ⟨515405, by rfl⟩ : syracuseStep 2748829 = 1030811) (by norm_num)
theorem B1716637 : Blo 1524459 1716637 := bbase (se 3 (by rfl) ⟨321869, by rfl⟩ : syracuseStep 1716637 = 643739) (by norm_num)
theorem B1716673 : Blo 1524459 1716673 := bbase (se 2 (by rfl) ⟨643752, by rfl⟩ : syracuseStep 1716673 = 1287505) (by norm_num)
theorem B1929673 : Blo 1524459 1929673 := bbase (se 2 (by rfl) ⟨723627, by rfl⟩ : syracuseStep 1929673 = 1447255) (by norm_num)
theorem B1716709 : Blo 1524459 1716709 := bbase (se 4 (by rfl) ⟨160941, by rfl⟩ : syracuseStep 1716709 = 321883) (by norm_num)
theorem B5870069 : Blo 1524459 5870069 := bbase (se 5 (by rfl) ⟨275159, by rfl⟩ : syracuseStep 5870069 = 550319) (by norm_num)
theorem B1716745 : Blo 1524459 1716745 := bbase (se 2 (by rfl) ⟨643779, by rfl⟩ : syracuseStep 1716745 = 1287559) (by norm_num)
theorem B3256853 : Blo 1524459 3256853 := bbase (se 6 (by rfl) ⟨76332, by rfl⟩ : syracuseStep 3256853 = 152665) (by norm_num)
theorem B4346389 : Blo 1524459 4346389 := bbase (se 6 (by rfl) ⟨101868, by rfl⟩ : syracuseStep 4346389 = 203737) (by norm_num)
theorem B1716781 : Blo 1524459 1716781 := bbase (se 3 (by rfl) ⟨321896, by rfl⟩ : syracuseStep 1716781 = 643793) (by norm_num)
theorem B1716817 : Blo 1524459 1716817 := bbase (se 2 (by rfl) ⟨643806, by rfl⟩ : syracuseStep 1716817 = 1287613) (by norm_num)
theorem B2896469 : Blo 1524459 2896469 := bbase (se 8 (by rfl) ⟨16971, by rfl⟩ : syracuseStep 2896469 = 33943) (by norm_num)
theorem B1831529 : Blo 1524459 1831529 := bbase (se 2 (by rfl) ⟨686823, by rfl⟩ : syracuseStep 1831529 = 1373647) (by norm_num)
theorem B1929845 : Blo 1524459 1929845 := bbase (se 5 (by rfl) ⟨90461, by rfl⟩ : syracuseStep 1929845 = 180923) (by norm_num)
theorem B1716853 : Blo 1524459 1716853 := bbase (se 5 (by rfl) ⟨80477, by rfl⟩ : syracuseStep 1716853 = 160955) (by norm_num)
theorem B6517381 : Blo 1524459 6517381 := bbase (se 4 (by rfl) ⟨611004, by rfl⟩ : syracuseStep 6517381 = 1222009) (by norm_num)
theorem B3863173 : Blo 1524459 3863173 := bbase (se 4 (by rfl) ⟨362172, by rfl⟩ : syracuseStep 3863173 = 724345) (by norm_num)
theorem B6517397 : Blo 1524459 6517397 := bbase (se 6 (by rfl) ⟨152751, by rfl⟩ : syracuseStep 6517397 = 305503) (by norm_num)
theorem B1716889 : Blo 1524459 1716889 := bbase (se 2 (by rfl) ⟨643833, by rfl⟩ : syracuseStep 1716889 = 1287667) (by norm_num)
theorem B1929901 : Blo 1524459 1929901 := bbase (se 3 (by rfl) ⟨361856, by rfl⟩ : syracuseStep 1929901 = 723713) (by norm_num)
theorem B2200253 : Blo 1524459 2200253 := bbase (se 3 (by rfl) ⟨412547, by rfl⟩ : syracuseStep 2200253 = 825095) (by norm_num)
theorem B1716925 : Blo 1524459 1716925 := bbase (se 3 (by rfl) ⟨321923, by rfl⟩ : syracuseStep 1716925 = 643847) (by norm_num)
theorem B1716961 : Blo 1524459 1716961 := bbase (se 2 (by rfl) ⟨643860, by rfl⟩ : syracuseStep 1716961 = 1287721) (by norm_num)
theorem B3863285 : Blo 1524459 3863285 := bbase (se 5 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 3863285 = 362183) (by norm_num)
theorem B3257093 : Blo 1524459 3257093 := bbase (se 4 (by rfl) ⟨305352, by rfl⟩ : syracuseStep 3257093 = 610705) (by norm_num)
theorem B1716997 : Blo 1524459 1716997 := bbase (se 4 (by rfl) ⟨160968, by rfl⟩ : syracuseStep 1716997 = 321937) (by norm_num)
theorem B1929997 : Blo 1524459 1929997 := bbase (se 3 (by rfl) ⟨361874, by rfl⟩ : syracuseStep 1929997 = 723749) (by norm_num)
theorem B9777941 : Blo 1524459 9777941 := bbase (se 6 (by rfl) ⟨229170, by rfl⟩ : syracuseStep 9777941 = 458341) (by norm_num)
theorem B1717033 : Blo 1524459 1717033 := bbase (se 2 (by rfl) ⟨643887, by rfl⟩ : syracuseStep 1717033 = 1287775) (by norm_num)
theorem B5149493 : Blo 1524459 5149493 := bbase (se 5 (by rfl) ⟨241382, by rfl⟩ : syracuseStep 5149493 = 482765) (by norm_num)
theorem B1717069 : Blo 1524459 1717069 := bbase (se 3 (by rfl) ⟨321950, by rfl⟩ : syracuseStep 1717069 = 643901) (by norm_num)
theorem B1717105 : Blo 1524459 1717105 := bbase (se 2 (by rfl) ⟨643914, by rfl⟩ : syracuseStep 1717105 = 1287829) (by norm_num)
theorem B3093365 : Blo 1524459 3093365 := bbase (se 5 (by rfl) ⟨145001, by rfl⟩ : syracuseStep 3093365 = 290003) (by norm_num)
theorem B1717141 : Blo 1524459 1717141 := bbase (se 6 (by rfl) ⟨40245, by rfl⟩ : syracuseStep 1717141 = 80491) (by norm_num)
theorem B1831837 : Blo 1524459 1831837 := bbase (se 3 (by rfl) ⟨343469, by rfl⟩ : syracuseStep 1831837 = 686939) (by norm_num)
theorem B3863477 : Blo 1524459 3863477 := bbase (se 5 (by rfl) ⟨181100, by rfl⟩ : syracuseStep 3863477 = 362201) (by norm_num)
theorem B1930169 : Blo 1524459 1930169 := bbase (se 2 (by rfl) ⟨723813, by rfl⟩ : syracuseStep 1930169 = 1447627) (by norm_num)
theorem B1717177 : Blo 1524459 1717177 := bbase (se 2 (by rfl) ⟨643941, by rfl⟩ : syracuseStep 1717177 = 1287883) (by norm_num)
theorem B1717213 : Blo 1524459 1717213 := bbase (se 3 (by rfl) ⟨321977, by rfl⟩ : syracuseStep 1717213 = 643955) (by norm_num)
theorem B1930225 : Blo 1524459 1930225 := bbase (se 2 (by rfl) ⟨723834, by rfl⟩ : syracuseStep 1930225 = 1447669) (by norm_num)
theorem B1717249 : Blo 1524459 1717249 := bbase (se 2 (by rfl) ⟨643968, by rfl⟩ : syracuseStep 1717249 = 1287937) (by norm_num)
theorem B7722053 : Blo 1524459 7722053 := bbase (se 4 (by rfl) ⟨723942, by rfl⟩ : syracuseStep 7722053 = 1447885) (by norm_num)
theorem B2061389 : Blo 1524459 2061389 := bbase (se 3 (by rfl) ⟨386510, by rfl⟩ : syracuseStep 2061389 = 773021) (by norm_num)
theorem B1930321 : Blo 1524459 1930321 := bbase (se 2 (by rfl) ⟨723870, by rfl⟩ : syracuseStep 1930321 = 1447741) (by norm_num)
theorem B1832053 : Blo 1524459 1832053 := bbase (se 5 (by rfl) ⟨85877, by rfl⟩ : syracuseStep 1832053 = 171755) (by norm_num)
theorem B5788853 : Blo 1524459 5788853 := bbase (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) (by norm_num)
theorem B3527869 : Blo 1524459 3527869 := bbase (se 3 (by rfl) ⟨661475, by rfl⟩ : syracuseStep 3527869 = 1322951) (by norm_num)
theorem B3667133 : Blo 1524459 3667133 := bbase (se 3 (by rfl) ⟨687587, by rfl⟩ : syracuseStep 3667133 = 1375175) (by norm_num)
theorem B1545409 : Blo 1524459 1545409 := bbase (se 2 (by rfl) ⟨579528, by rfl⟩ : syracuseStep 1545409 = 1159057) (by norm_num)
theorem B5149925 : Blo 1524459 5149925 := bbase (se 4 (by rfl) ⟨482805, by rfl⟩ : syracuseStep 5149925 = 965611) (by norm_num)
theorem B3257597 : Blo 1524459 3257597 := bbase (se 3 (by rfl) ⟨610799, by rfl⟩ : syracuseStep 3257597 = 1221599) (by norm_num)
theorem B1930493 : Blo 1524459 1930493 := bbase (se 3 (by rfl) ⟨361967, by rfl⟩ : syracuseStep 1930493 = 723935) (by norm_num)
theorem B3257605 : Blo 1524459 3257605 := bbase (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) (by norm_num)
theorem B3863821 : Blo 1524459 3863821 := bbase (se 3 (by rfl) ⟨724466, by rfl⟩ : syracuseStep 3863821 = 1448933) (by norm_num)
theorem B1930549 : Blo 1524459 1930549 := bbase (se 5 (by rfl) ⟨90494, by rfl⟩ : syracuseStep 1930549 = 180989) (by norm_num)
theorem B2897221 : Blo 1524459 2897221 := bbase (se 4 (by rfl) ⟨271614, by rfl⟩ : syracuseStep 2897221 = 543229) (by norm_num)
theorem B1652065 : Blo 1524459 1652065 := bbase (se 2 (by rfl) ⟨619524, by rfl⟩ : syracuseStep 1652065 = 1239049) (by norm_num)
theorem B1930645 : Blo 1524459 1930645 := bbase (se 6 (by rfl) ⟨45249, by rfl⟩ : syracuseStep 1930645 = 90499) (by norm_num)
theorem B5789141 : Blo 1524459 5789141 := bbase (se 7 (by rfl) ⟨67841, by rfl⟩ : syracuseStep 5789141 = 135683) (by norm_num)
theorem B2897365 : Blo 1524459 2897365 := bbase (se 7 (by rfl) ⟨33953, by rfl⟩ : syracuseStep 2897365 = 67907) (by norm_num)
theorem B1545701 : Blo 1524459 1545701 := bbase (se 4 (by rfl) ⟨144909, by rfl⟩ : syracuseStep 1545701 = 289819) (by norm_num)
theorem B2749925 : Blo 1524459 2749925 := bbase (se 4 (by rfl) ⟨257805, by rfl⟩ : syracuseStep 2749925 = 515611) (by norm_num)
theorem B3913213 : Blo 1524459 3913213 := bbase (se 3 (by rfl) ⟨733727, by rfl⟩ : syracuseStep 3913213 = 1467455) (by norm_num)
theorem B5494325 : Blo 1524459 5494325 := bbase (se 5 (by rfl) ⟨257546, by rfl⟩ : syracuseStep 5494325 = 515093) (by norm_num)
theorem B1930817 : Blo 1524459 1930817 := bbase (se 2 (by rfl) ⟨724056, by rfl⟩ : syracuseStep 1930817 = 1448113) (by norm_num)
theorem B3667565 : Blo 1524459 3667565 := bbase (se 3 (by rfl) ⟨687668, by rfl⟩ : syracuseStep 3667565 = 1375337) (by norm_num)
theorem B2897525 : Blo 1524459 2897525 := bbase (se 5 (by rfl) ⟨135821, by rfl⟩ : syracuseStep 2897525 = 271643) (by norm_num)
theorem B1930873 : Blo 1524459 1930873 := bbase (se 2 (by rfl) ⟨724077, by rfl⟩ : syracuseStep 1930873 = 1448155) (by norm_num)
theorem B2061973 : Blo 1524459 2061973 := bbase (se 6 (by rfl) ⟨48327, by rfl⟩ : syracuseStep 2061973 = 96655) (by norm_num)
theorem B5150357 : Blo 1524459 5150357 := bbase (se 6 (by rfl) ⟨120711, by rfl⟩ : syracuseStep 5150357 = 241423) (by norm_num)
theorem B3430061 : Blo 1524459 3430061 := bbase (se 3 (by rfl) ⟨643136, by rfl⟩ : syracuseStep 3430061 = 1286273) (by norm_num)
theorem B1832653 : Blo 1524459 1832653 := bbase (se 3 (by rfl) ⟨343622, by rfl⟩ : syracuseStep 1832653 = 687245) (by norm_num)
theorem B1930969 : Blo 1524459 1930969 := bbase (se 2 (by rfl) ⟨724113, by rfl⟩ : syracuseStep 1930969 = 1448227) (by norm_num)
theorem B3430133 : Blo 1524459 3430133 := bbase (se 5 (by rfl) ⟨160787, by rfl⟩ : syracuseStep 3430133 = 321575) (by norm_num)
theorem B2750213 : Blo 1524459 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B2897669 : Blo 1524459 2897669 := bbase (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) (by norm_num)
theorem B3430205 : Blo 1524459 3430205 := bbase (se 3 (by rfl) ⟨643163, by rfl⟩ : syracuseStep 3430205 = 1286327) (by norm_num)
theorem B2062189 : Blo 1524459 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B3430277 : Blo 1524459 3430277 := bbase (se 4 (by rfl) ⟨321588, by rfl⟩ : syracuseStep 3430277 = 643177) (by norm_num)
theorem B5494661 : Blo 1524459 5494661 := bbase (se 4 (by rfl) ⟨515124, by rfl⟩ : syracuseStep 5494661 = 1030249) (by norm_num)
theorem B1931141 : Blo 1524459 1931141 := bbase (se 4 (by rfl) ⟨181044, by rfl⟩ : syracuseStep 1931141 = 362089) (by norm_num)
theorem B8689589 : Blo 1524459 8689589 := bbase (se 5 (by rfl) ⟨407324, by rfl⟩ : syracuseStep 8689589 = 814649) (by norm_num)
theorem B12375989 : Blo 1524459 12375989 := bbase (se 5 (by rfl) ⟨580124, by rfl⟩ : syracuseStep 12375989 = 1160249) (by norm_num)
theorem B1931197 : Blo 1524459 1931197 := bbase (se 3 (by rfl) ⟨362099, by rfl⟩ : syracuseStep 1931197 = 724199) (by norm_num)
theorem B3430349 : Blo 1524459 3430349 := bbase (se 3 (by rfl) ⟨643190, by rfl⟩ : syracuseStep 3430349 = 1286381) (by norm_num)
theorem B3094517 : Blo 1524459 3094517 := bbase (se 5 (by rfl) ⟨145055, by rfl⟩ : syracuseStep 3094517 = 290111) (by norm_num)
theorem B3430421 : Blo 1524459 3430421 := bbase (se 6 (by rfl) ⟨80400, by rfl⟩ : syracuseStep 3430421 = 160801) (by norm_num)
theorem B1931293 : Blo 1524459 1931293 := bbase (se 3 (by rfl) ⟨362117, by rfl⟩ : syracuseStep 1931293 = 724235) (by norm_num)
theorem B4888613 : Blo 1524459 4888613 := bbase (se 4 (by rfl) ⟨458307, by rfl⟩ : syracuseStep 4888613 = 916615) (by norm_num)
theorem B5150789 : Blo 1524459 5150789 := bbase (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) (by norm_num)
theorem B3430493 : Blo 1524459 3430493 := bbase (se 3 (by rfl) ⟨643217, by rfl⟩ : syracuseStep 3430493 = 1286435) (by norm_num)
theorem B1628273 : Blo 1524459 1628273 := bbase (se 2 (by rfl) ⟨610602, by rfl⟩ : syracuseStep 1628273 = 1221205) (by norm_num)
theorem B3430565 : Blo 1524459 3430565 := bbase (se 4 (by rfl) ⟨321615, by rfl⟩ : syracuseStep 3430565 = 643231) (by norm_num)
theorem B1931465 : Blo 1524459 1931465 := bbase (se 2 (by rfl) ⟨724299, by rfl⟩ : syracuseStep 1931465 = 1448599) (by norm_num)
theorem B3430637 : Blo 1524459 3430637 := bbase (se 3 (by rfl) ⟨643244, by rfl⟩ : syracuseStep 3430637 = 1286489) (by norm_num)
theorem B2062589 : Blo 1524459 2062589 := bbase (se 3 (by rfl) ⟨386735, by rfl⟩ : syracuseStep 2062589 = 773471) (by norm_num)
theorem B1931521 : Blo 1524459 1931521 := bbase (se 2 (by rfl) ⟨724320, by rfl⟩ : syracuseStep 1931521 = 1448641) (by norm_num)
theorem B1628461 : Blo 1524459 1628461 := bbase (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) (by norm_num)
theorem B3430709 : Blo 1524459 3430709 := bbase (se 5 (by rfl) ⟨160814, by rfl⟩ : syracuseStep 3430709 = 321629) (by norm_num)
theorem B7723349 : Blo 1524459 7723349 := bbase (se 10 (by rfl) ⟨11313, by rfl⟩ : syracuseStep 7723349 = 22627) (by norm_num)
theorem B1931617 : Blo 1524459 1931617 := bbase (se 2 (by rfl) ⟨724356, by rfl⟩ : syracuseStep 1931617 = 1448713) (by norm_num)
theorem B3258733 : Blo 1524459 3258733 := bbase (se 3 (by rfl) ⟨611012, by rfl⟩ : syracuseStep 3258733 = 1222025) (by norm_num)
theorem B3430781 : Blo 1524459 3430781 := bbase (se 3 (by rfl) ⟨643271, by rfl⟩ : syracuseStep 3430781 = 1286543) (by norm_num)
theorem B10041781 : Blo 1524459 10041781 := bbase (se 5 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 10041781 = 941417) (by norm_num)
theorem B11000245 : Blo 1524459 11000245 := bbase (se 5 (by rfl) ⟨515636, by rfl⟩ : syracuseStep 11000245 = 1031273) (by norm_num)
theorem B3430853 : Blo 1524459 3430853 := bbase (se 4 (by rfl) ⟨321642, by rfl⟩ : syracuseStep 3430853 = 643285) (by norm_num)
theorem B5151221 : Blo 1524459 5151221 := bbase (se 5 (by rfl) ⟨241463, by rfl⟩ : syracuseStep 5151221 = 482927) (by norm_num)
theorem B3430925 : Blo 1524459 3430925 := bbase (se 3 (by rfl) ⟨643298, by rfl⟩ : syracuseStep 3430925 = 1286597) (by norm_num)
theorem B1931789 : Blo 1524459 1931789 := bbase (se 3 (by rfl) ⟨362210, by rfl⟩ : syracuseStep 1931789 = 724421) (by norm_num)
theorem B1546813 : Blo 1524459 1546813 := bbase (se 3 (by rfl) ⟨290027, by rfl⟩ : syracuseStep 1546813 = 580055) (by norm_num)
theorem B1931845 : Blo 1524459 1931845 := bbase (se 4 (by rfl) ⟨181110, by rfl⟩ : syracuseStep 1931845 = 362221) (by norm_num)
theorem B3430997 : Blo 1524459 3430997 := bbase (se 8 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 3430997 = 40207) (by norm_num)
theorem B5790325 : Blo 1524459 5790325 := bbase (se 5 (by rfl) ⟨271421, by rfl⟩ : syracuseStep 5790325 = 542843) (by norm_num)
theorem B9771637 : Blo 1524459 9771637 := bbase (se 5 (by rfl) ⟨458045, by rfl⟩ : syracuseStep 9771637 = 916091) (by norm_num)
theorem B3431069 : Blo 1524459 3431069 := bbase (se 3 (by rfl) ⟨643325, by rfl⟩ : syracuseStep 3431069 = 1286651) (by norm_num)
theorem B10992341 : Blo 1524459 10992341 := bbase (se 7 (by rfl) ⟨128816, by rfl⟩ : syracuseStep 10992341 = 257633) (by norm_num)
theorem B3431141 : Blo 1524459 3431141 := bbase (se 4 (by rfl) ⟨321669, by rfl⟩ : syracuseStep 3431141 = 643339) (by norm_num)
theorem B3259109 : Blo 1524459 3259109 := bbase (se 4 (by rfl) ⟨305541, by rfl⟩ : syracuseStep 3259109 = 611083) (by norm_num)
theorem B3431213 : Blo 1524459 3431213 := bbase (se 3 (by rfl) ⟨643352, by rfl⟩ : syracuseStep 3431213 = 1286705) (by norm_num)
theorem B1833797 : Blo 1524459 1833797 := bbase (se 4 (by rfl) ⟨171918, by rfl⟩ : syracuseStep 1833797 = 343837) (by norm_num)
theorem B6519653 : Blo 1524459 6519653 := bbase (se 4 (by rfl) ⟨611217, by rfl⟩ : syracuseStep 6519653 = 1222435) (by norm_num)
theorem B3431285 : Blo 1524459 3431285 := bbase (se 5 (by rfl) ⟨160841, by rfl⟩ : syracuseStep 3431285 = 321683) (by norm_num)
theorem B5790629 : Blo 1524459 5790629 := bbase (se 4 (by rfl) ⟨542871, by rfl⟩ : syracuseStep 5790629 = 1085743) (by norm_num)
theorem B5151653 : Blo 1524459 5151653 := bbase (se 4 (by rfl) ⟨482967, by rfl⟩ : syracuseStep 5151653 = 965935) (by norm_num)
theorem B3431357 : Blo 1524459 3431357 := bbase (se 3 (by rfl) ⟨643379, by rfl⟩ : syracuseStep 3431357 = 1286759) (by norm_num)
theorem B11590613 : Blo 1524459 11590613 := bbase (se 7 (by rfl) ⟨135827, by rfl⟩ : syracuseStep 11590613 = 271655) (by norm_num)
theorem B5495813 : Blo 1524459 5495813 := bbase (se 4 (by rfl) ⟨515232, by rfl⟩ : syracuseStep 5495813 = 1030465) (by norm_num)
theorem B3431429 : Blo 1524459 3431429 := bbase (se 4 (by rfl) ⟨321696, by rfl⟩ : syracuseStep 3431429 = 643393) (by norm_num)
theorem B3431501 : Blo 1524459 3431501 := bbase (se 3 (by rfl) ⟨643406, by rfl⟩ : syracuseStep 3431501 = 1286813) (by norm_num)
theorem B8690773 : Blo 1524459 8690773 := bbase (se 8 (by rfl) ⟨50922, by rfl⟩ : syracuseStep 8690773 = 101845) (by norm_num)
theorem B1629281 : Blo 1524459 1629281 := bbase (se 2 (by rfl) ⟨610980, by rfl⟩ : syracuseStep 1629281 = 1221961) (by norm_num)
theorem B3431573 : Blo 1524459 3431573 := bbase (se 6 (by rfl) ⟨80427, by rfl⟩ : syracuseStep 3431573 = 160855) (by norm_num)
theorem B5291173 : Blo 1524459 5291173 := bbase (se 4 (by rfl) ⟨496047, by rfl⟩ : syracuseStep 5291173 = 992095) (by norm_num)
theorem B3431645 : Blo 1524459 3431645 := bbase (se 3 (by rfl) ⟨643433, by rfl⟩ : syracuseStep 3431645 = 1286867) (by norm_num)
theorem B3431717 : Blo 1524459 3431717 := bbase (se 4 (by rfl) ⟨321723, by rfl⟩ : syracuseStep 3431717 = 643447) (by norm_num)
theorem B3431789 : Blo 1524459 3431789 := bbase (se 3 (by rfl) ⟨643460, by rfl⟩ : syracuseStep 3431789 = 1286921) (by norm_num)
theorem B11582837 : Blo 1524459 11582837 := bbase (se 5 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 11582837 = 1085891) (by norm_num)
theorem B3431861 : Blo 1524459 3431861 := bbase (se 5 (by rfl) ⟨160868, by rfl⟩ : syracuseStep 3431861 = 321737) (by norm_num)
theorem B2645453 : Blo 1524459 2645453 := bbase (se 3 (by rfl) ⟨496022, by rfl⟩ : syracuseStep 2645453 = 992045) (by norm_num)
theorem B1883633 : Blo 1524459 1883633 := bbase (se 2 (by rfl) ⟨706362, by rfl⟩ : syracuseStep 1883633 = 1412725) (by norm_num)
theorem B3431933 : Blo 1524459 3431933 := bbase (se 3 (by rfl) ⟨643487, by rfl⟩ : syracuseStep 3431933 = 1286975) (by norm_num)
theorem B1629725 : Blo 1524459 1629725 := bbase (se 3 (by rfl) ⟨305573, by rfl⟩ : syracuseStep 1629725 = 611147) (by norm_num)
theorem B3432005 : Blo 1524459 3432005 := bbase (se 4 (by rfl) ⟨321750, by rfl⟩ : syracuseStep 3432005 = 643501) (by norm_num)
theorem B49495637 : Blo 1524459 49495637 := bbase (se 8 (by rfl) ⟨290013, by rfl⟩ : syracuseStep 49495637 = 580027) (by norm_num)
theorem B7724645 : Blo 1524459 7724645 := bbase (se 4 (by rfl) ⟨724185, by rfl⟩ : syracuseStep 7724645 = 1448371) (by norm_num)
theorem B3432077 : Blo 1524459 3432077 := bbase (se 3 (by rfl) ⟨643514, by rfl⟩ : syracuseStep 3432077 = 1287029) (by norm_num)
theorem B3432149 : Blo 1524459 3432149 := bbase (se 7 (by rfl) ⟨40220, by rfl⟩ : syracuseStep 3432149 = 80441) (by norm_num)
theorem B2318077 : Blo 1524459 2318077 := bbase (se 3 (by rfl) ⟨434639, by rfl⟩ : syracuseStep 2318077 = 869279) (by norm_num)
theorem B1629973 : Blo 1524459 1629973 := bbase (se 6 (by rfl) ⟨38202, by rfl⟩ : syracuseStep 1629973 = 76405) (by norm_num)
theorem B3432221 : Blo 1524459 3432221 := bbase (se 3 (by rfl) ⟨643541, by rfl⟩ : syracuseStep 3432221 = 1287083) (by norm_num)
theorem B3432293 : Blo 1524459 3432293 := bbase (se 4 (by rfl) ⟨321777, by rfl⟩ : syracuseStep 3432293 = 643555) (by norm_num)
theorem B2170757 : Blo 1524459 2170757 := bbase (se 4 (by rfl) ⟨203508, by rfl⟩ : syracuseStep 2170757 = 407017) (by norm_num)
theorem B3432365 : Blo 1524459 3432365 := bbase (se 3 (by rfl) ⟨643568, by rfl⟩ : syracuseStep 3432365 = 1287137) (by norm_num)
theorem B2170837 : Blo 1524459 2170837 := bbase (se 7 (by rfl) ⟨25439, by rfl⟩ : syracuseStep 2170837 = 50879) (by norm_num)
theorem B3432437 : Blo 1524459 3432437 := bbase (se 5 (by rfl) ⟨160895, by rfl⟩ : syracuseStep 3432437 = 321791) (by norm_num)
theorem B3301489 : Blo 1524459 3301489 := bstep (se 2 (by rfl) ⟨1238058, by rfl⟩ : syracuseStep 3301489 = 2476117) B2476117
theorem B5497037 : Blo 1524459 5497037 := bstep (se 3 (by rfl) ⟨1030694, by rfl⟩ : syracuseStep 5497037 = 2061389) B2061389
theorem B3432689 : Blo 1524459 3432689 := bstep (se 2 (by rfl) ⟨1287258, by rfl⟩ : syracuseStep 3432689 = 2574517) B2574517
theorem B3432707 : Blo 1524459 3432707 := bstep (se 1 (by rfl) ⟨2574530, by rfl⟩ : syracuseStep 3432707 = 5149061) B5149061
theorem B4342061 : Blo 1524459 4342061 := bstep (se 3 (by rfl) ⟨814136, by rfl⟩ : syracuseStep 4342061 = 1628273) B1628273
theorem B17383733 : Blo 1524459 17383733 := bstep (se 5 (by rfl) ⟨814862, by rfl⟩ : syracuseStep 17383733 = 1629725) B1629725
theorem B4702531 : Blo 1524459 4702531 := bstep (se 1 (by rfl) ⟨3526898, by rfl⟩ : syracuseStep 4702531 = 7053797) B7053797
theorem B2572627 : Blo 1524459 2572627 := bstep (se 1 (by rfl) ⟨1929470, by rfl⟩ : syracuseStep 2572627 = 3858941) B3858941
theorem B2171281 : Blo 1524459 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B9273797 : Blo 1524459 9273797 := bstep (se 4 (by rfl) ⟨869418, by rfl⟩ : syracuseStep 9273797 = 1738837) B1738837
theorem B2572769 : Blo 1524459 2572769 := bstep (se 2 (by rfl) ⟨964788, by rfl⟩ : syracuseStep 2572769 = 1929577) B1929577
theorem B4342243 : Blo 1524459 4342243 := bstep (se 1 (by rfl) ⟨3256682, by rfl⟩ : syracuseStep 4342243 = 6513365) B6513365
theorem B2171395 : Blo 1524459 2171395 := bstep (se 1 (by rfl) ⟨1628546, by rfl⟩ : syracuseStep 2171395 = 3257093) B3257093
theorem B5792269 : Blo 1524459 5792269 := bstep (se 3 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 5792269 = 2172101) B2172101
theorem B3858961 : Blo 1524459 3858961 := bstep (se 2 (by rfl) ⟨1447110, by rfl⟩ : syracuseStep 3858961 = 2894221) B2894221
theorem B3432977 : Blo 1524459 3432977 := bstep (se 2 (by rfl) ⟨1287366, by rfl⟩ : syracuseStep 3432977 = 2574733) B2574733
theorem B3432995 : Blo 1524459 3432995 := bstep (se 1 (by rfl) ⟨2574746, by rfl⟩ : syracuseStep 3432995 = 5149493) B5149493
theorem B7725617 : Blo 1524459 7725617 := bstep (se 2 (by rfl) ⟨2897106, by rfl⟩ : syracuseStep 7725617 = 5794213) B5794213
theorem B2572897 : Blo 1524459 2572897 := bstep (se 2 (by rfl) ⟨964836, by rfl⟩ : syracuseStep 2572897 = 1929673) B1929673
theorem B2572931 : Blo 1524459 2572931 := bstep (se 1 (by rfl) ⟨1929698, by rfl⟩ : syracuseStep 2572931 = 3859397) B3859397
theorem B4342403 : Blo 1524459 4342403 := bstep (se 1 (by rfl) ⟨3256802, by rfl⟩ : syracuseStep 4342403 = 6513605) B6513605
theorem B5292685 : Blo 1524459 5292685 := bstep (se 3 (by rfl) ⟨992378, by rfl⟩ : syracuseStep 5292685 = 1984757) B1984757
theorem B2261729 : Blo 1524459 2261729 := bstep (se 2 (by rfl) ⟨848148, by rfl⟩ : syracuseStep 2261729 = 1696297) B1696297
theorem B1524467 : Blo 1524459 1524467 := bstep (se 1 (by rfl) ⟨1143350, by rfl⟩ : syracuseStep 1524467 = 2286701) B2286701
theorem B1524483 : Blo 1524459 1524483 := bstep (se 1 (by rfl) ⟨1143362, by rfl⟩ : syracuseStep 1524483 = 2286725) B2286725
theorem B2573059 : Blo 1524459 2573059 := bstep (se 1 (by rfl) ⟨1929794, by rfl⟩ : syracuseStep 2573059 = 3859589) B3859589
theorem B1524499 : Blo 1524459 1524499 := bstep (se 1 (by rfl) ⟨1143374, by rfl⟩ : syracuseStep 1524499 = 2286749) B2286749
theorem B1524515 : Blo 1524459 1524515 := bstep (se 1 (by rfl) ⟨1143386, by rfl⟩ : syracuseStep 1524515 = 2286773) B2286773
theorem B3859235 : Blo 1524459 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B5145389 : Blo 1524459 5145389 := bstep (se 3 (by rfl) ⟨964760, by rfl⟩ : syracuseStep 5145389 = 1929521) B1929521
theorem B3433265 : Blo 1524459 3433265 := bstep (se 2 (by rfl) ⟨1287474, by rfl⟩ : syracuseStep 3433265 = 2574949) B2574949
theorem B1524531 : Blo 1524459 1524531 := bstep (se 1 (by rfl) ⟨1143398, by rfl⟩ : syracuseStep 1524531 = 2286797) B2286797
theorem B1524547 : Blo 1524459 1524547 := bstep (se 1 (by rfl) ⟨1143410, by rfl⟩ : syracuseStep 1524547 = 2286821) B2286821
theorem B3433283 : Blo 1524459 3433283 := bstep (se 1 (by rfl) ⟨2574962, by rfl⟩ : syracuseStep 3433283 = 5149925) B5149925
theorem B1524563 : Blo 1524459 1524563 := bstep (se 1 (by rfl) ⟨1143422, by rfl⟩ : syracuseStep 1524563 = 2286845) B2286845
theorem B5145443 : Blo 1524459 5145443 := bstep (se 1 (by rfl) ⟨3859082, by rfl⟩ : syracuseStep 5145443 = 7718165) B7718165
theorem B1524579 : Blo 1524459 1524579 := bstep (se 1 (by rfl) ⟨1143434, by rfl⟩ : syracuseStep 1524579 = 2286869) B2286869
theorem B1524595 : Blo 1524459 1524595 := bstep (se 1 (by rfl) ⟨1143446, by rfl⟩ : syracuseStep 1524595 = 2286893) B2286893
theorem B1524611 : Blo 1524459 1524611 := bstep (se 1 (by rfl) ⟨1143458, by rfl⟩ : syracuseStep 1524611 = 2286917) B2286917
theorem B2573201 : Blo 1524459 2573201 := bstep (se 2 (by rfl) ⟨964950, by rfl⟩ : syracuseStep 2573201 = 1929901) B1929901
theorem B1524627 : Blo 1524459 1524627 := bstep (se 1 (by rfl) ⟨1143470, by rfl⟩ : syracuseStep 1524627 = 2286941) B2286941
theorem B1524643 : Blo 1524459 1524643 := bstep (se 1 (by rfl) ⟨1143482, by rfl⟩ : syracuseStep 1524643 = 2286965) B2286965
theorem B1524659 : Blo 1524459 1524659 := bstep (se 1 (by rfl) ⟨1143494, by rfl⟩ : syracuseStep 1524659 = 2286989) B2286989
theorem B2442179 : Blo 1524459 2442179 := bstep (se 1 (by rfl) ⟨1831634, by rfl⟩ : syracuseStep 2442179 = 3663269) B3663269
theorem B1524675 : Blo 1524459 1524675 := bstep (se 1 (by rfl) ⟨1143506, by rfl⟩ : syracuseStep 1524675 = 2287013) B2287013
theorem B1524691 : Blo 1524459 1524691 := bstep (se 1 (by rfl) ⟨1143518, by rfl⟩ : syracuseStep 1524691 = 2287037) B2287037
theorem B1524707 : Blo 1524459 1524707 := bstep (se 1 (by rfl) ⟨1143530, by rfl⟩ : syracuseStep 1524707 = 2287061) B2287061
theorem B3859427 : Blo 1524459 3859427 := bstep (se 1 (by rfl) ⟨2894570, by rfl⟩ : syracuseStep 3859427 = 5789141) B5789141
theorem B1524723 : Blo 1524459 1524723 := bstep (se 1 (by rfl) ⟨1143542, by rfl⟩ : syracuseStep 1524723 = 2287085) B2287085
theorem B1524739 : Blo 1524459 1524739 := bstep (se 1 (by rfl) ⟨1143554, by rfl⟩ : syracuseStep 1524739 = 2287109) B2287109
theorem B8242181 : Blo 1524459 8242181 := bstep (se 4 (by rfl) ⟨772704, by rfl⟩ : syracuseStep 8242181 = 1545409) B1545409
theorem B2573329 : Blo 1524459 2573329 := bstep (se 2 (by rfl) ⟨964998, by rfl⟩ : syracuseStep 2573329 = 1929997) B1929997
theorem B1524755 : Blo 1524459 1524755 := bstep (se 1 (by rfl) ⟨1143566, by rfl⟩ : syracuseStep 1524755 = 2287133) B2287133
theorem B1524771 : Blo 1524459 1524771 := bstep (se 1 (by rfl) ⟨1143578, by rfl⟩ : syracuseStep 1524771 = 2287157) B2287157
theorem B1524787 : Blo 1524459 1524787 := bstep (se 1 (by rfl) ⟨1143590, by rfl⟩ : syracuseStep 1524787 = 2287181) B2287181
theorem B2573363 : Blo 1524459 2573363 := bstep (se 1 (by rfl) ⟨1930022, by rfl⟩ : syracuseStep 2573363 = 3860045) B3860045
theorem B2442307 : Blo 1524459 2442307 := bstep (se 1 (by rfl) ⟨1831730, by rfl⟩ : syracuseStep 2442307 = 3663461) B3663461
theorem B1524803 : Blo 1524459 1524803 := bstep (se 1 (by rfl) ⟨1143602, by rfl⟩ : syracuseStep 1524803 = 2287205) B2287205
theorem B3433553 : Blo 1524459 3433553 := bstep (se 2 (by rfl) ⟨1287582, by rfl⟩ : syracuseStep 3433553 = 2575165) B2575165
theorem B1524819 : Blo 1524459 1524819 := bstep (se 1 (by rfl) ⟨1143614, by rfl⟩ : syracuseStep 1524819 = 2287229) B2287229
theorem B2286689 : Blo 1524459 2286689 := bstep (se 2 (by rfl) ⟨857508, by rfl⟩ : syracuseStep 2286689 = 1715017) B1715017
theorem B1524835 : Blo 1524459 1524835 := bstep (se 1 (by rfl) ⟨1143626, by rfl⟩ : syracuseStep 1524835 = 2287253) B2287253
theorem B3433571 : Blo 1524459 3433571 := bstep (se 1 (by rfl) ⟨2575178, by rfl⟩ : syracuseStep 3433571 = 5150357) B5150357
theorem B5145713 : Blo 1524459 5145713 := bstep (se 2 (by rfl) ⟨1929642, by rfl⟩ : syracuseStep 5145713 = 3859285) B3859285
theorem B2286707 : Blo 1524459 2286707 := bstep (se 1 (by rfl) ⟨1715030, by rfl⟩ : syracuseStep 2286707 = 3430061) B3430061
theorem B1524851 : Blo 1524459 1524851 := bstep (se 1 (by rfl) ⟨1143638, by rfl⟩ : syracuseStep 1524851 = 2287277) B2287277
theorem B1524867 : Blo 1524459 1524867 := bstep (se 1 (by rfl) ⟨1143650, by rfl⟩ : syracuseStep 1524867 = 2287301) B2287301
theorem B2286737 : Blo 1524459 2286737 := bstep (se 2 (by rfl) ⟨857526, by rfl⟩ : syracuseStep 2286737 = 1715053) B1715053
theorem B1524883 : Blo 1524459 1524883 := bstep (se 1 (by rfl) ⟨1143662, by rfl⟩ : syracuseStep 1524883 = 2287325) B2287325
theorem B2286755 : Blo 1524459 2286755 := bstep (se 1 (by rfl) ⟨1715066, by rfl⟩ : syracuseStep 2286755 = 3430133) B3430133
theorem B1524899 : Blo 1524459 1524899 := bstep (se 1 (by rfl) ⟨1143674, by rfl⟩ : syracuseStep 1524899 = 2287349) B2287349
theorem B1524915 : Blo 1524459 1524915 := bstep (se 1 (by rfl) ⟨1143686, by rfl⟩ : syracuseStep 1524915 = 2287373) B2287373
theorem B2573491 : Blo 1524459 2573491 := bstep (se 1 (by rfl) ⟨1930118, by rfl⟩ : syracuseStep 2573491 = 3860237) B3860237
theorem B2286785 : Blo 1524459 2286785 := bstep (se 2 (by rfl) ⟨857544, by rfl⟩ : syracuseStep 2286785 = 1715089) B1715089
theorem B1524931 : Blo 1524459 1524931 := bstep (se 1 (by rfl) ⟨1143698, by rfl⟩ : syracuseStep 1524931 = 2287397) B2287397
theorem B2442449 : Blo 1524459 2442449 := bstep (se 2 (by rfl) ⟨915918, by rfl⟩ : syracuseStep 2442449 = 1831837) B1831837
theorem B2286803 : Blo 1524459 2286803 := bstep (se 1 (by rfl) ⟨1715102, by rfl⟩ : syracuseStep 2286803 = 3430205) B3430205
theorem B1524947 : Blo 1524459 1524947 := bstep (se 1 (by rfl) ⟨1143710, by rfl⟩ : syracuseStep 1524947 = 2287421) B2287421
theorem B1524963 : Blo 1524459 1524963 := bstep (se 1 (by rfl) ⟨1143722, by rfl⟩ : syracuseStep 1524963 = 2287445) B2287445
theorem B2286833 : Blo 1524459 2286833 := bstep (se 2 (by rfl) ⟨857562, by rfl⟩ : syracuseStep 2286833 = 1715125) B1715125
theorem B1524979 : Blo 1524459 1524979 := bstep (se 1 (by rfl) ⟨1143734, by rfl⟩ : syracuseStep 1524979 = 2287469) B2287469
theorem B2286851 : Blo 1524459 2286851 := bstep (se 1 (by rfl) ⟨1715138, by rfl⟩ : syracuseStep 2286851 = 3430277) B3430277
theorem B3663107 : Blo 1524459 3663107 := bstep (se 1 (by rfl) ⟨2747330, by rfl⟩ : syracuseStep 3663107 = 5494661) B5494661
theorem B1524995 : Blo 1524459 1524995 := bstep (se 1 (by rfl) ⟨1143746, by rfl⟩ : syracuseStep 1524995 = 2287493) B2287493
theorem B4121869 : Blo 1524459 4121869 := bstep (se 3 (by rfl) ⟨772850, by rfl⟩ : syracuseStep 4121869 = 1545701) B1545701
theorem B11584781 : Blo 1524459 11584781 := bstep (se 3 (by rfl) ⟨2172146, by rfl⟩ : syracuseStep 11584781 = 4344293) B4344293
theorem B1525011 : Blo 1524459 1525011 := bstep (se 1 (by rfl) ⟨1143758, by rfl⟩ : syracuseStep 1525011 = 2287517) B2287517
theorem B2286881 : Blo 1524459 2286881 := bstep (se 2 (by rfl) ⟨857580, by rfl⟩ : syracuseStep 2286881 = 1715161) B1715161
theorem B1525027 : Blo 1524459 1525027 := bstep (se 1 (by rfl) ⟨1143770, by rfl⟩ : syracuseStep 1525027 = 2287541) B2287541
theorem B5793059 : Blo 1524459 5793059 := bstep (se 1 (by rfl) ⟨4344794, by rfl⟩ : syracuseStep 5793059 = 8689589) B8689589
theorem B8250659 : Blo 1524459 8250659 := bstep (se 1 (by rfl) ⟨6187994, by rfl⟩ : syracuseStep 8250659 = 12375989) B12375989
theorem B2286899 : Blo 1524459 2286899 := bstep (se 1 (by rfl) ⟨1715174, by rfl⟩ : syracuseStep 2286899 = 3430349) B3430349
theorem B1525043 : Blo 1524459 1525043 := bstep (se 1 (by rfl) ⟨1143782, by rfl⟩ : syracuseStep 1525043 = 2287565) B2287565
theorem B2573633 : Blo 1524459 2573633 := bstep (se 2 (by rfl) ⟨965112, by rfl⟩ : syracuseStep 2573633 = 1930225) B1930225
theorem B1525059 : Blo 1524459 1525059 := bstep (se 1 (by rfl) ⟨1143794, by rfl⟩ : syracuseStep 1525059 = 2287589) B2287589
theorem B12363077 : Blo 1524459 12363077 := bstep (se 4 (by rfl) ⟨1159038, by rfl⟩ : syracuseStep 12363077 = 2318077) B2318077
theorem B2286929 : Blo 1524459 2286929 := bstep (se 2 (by rfl) ⟨857598, by rfl⟩ : syracuseStep 2286929 = 1715197) B1715197
theorem B1525075 : Blo 1524459 1525075 := bstep (se 1 (by rfl) ⟨1143806, by rfl⟩ : syracuseStep 1525075 = 2287613) B2287613
theorem B2286947 : Blo 1524459 2286947 := bstep (se 1 (by rfl) ⟨1715210, by rfl⟩ : syracuseStep 2286947 = 3430421) B3430421
theorem B1525091 : Blo 1524459 1525091 := bstep (se 1 (by rfl) ⟨1143818, by rfl⟩ : syracuseStep 1525091 = 2287637) B2287637
theorem B3433841 : Blo 1524459 3433841 := bstep (se 2 (by rfl) ⟨1287690, by rfl⟩ : syracuseStep 3433841 = 2575381) B2575381
theorem B1525107 : Blo 1524459 1525107 := bstep (se 1 (by rfl) ⟨1143830, by rfl⟩ : syracuseStep 1525107 = 2287661) B2287661
theorem B2286977 : Blo 1524459 2286977 := bstep (se 2 (by rfl) ⟨857616, by rfl⟩ : syracuseStep 2286977 = 1715233) B1715233
theorem B1525123 : Blo 1524459 1525123 := bstep (se 1 (by rfl) ⟨1143842, by rfl⟩ : syracuseStep 1525123 = 2287685) B2287685
theorem B3433859 : Blo 1524459 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B8684941 : Blo 1524459 8684941 := bstep (se 3 (by rfl) ⟨1628426, by rfl⟩ : syracuseStep 8684941 = 3256853) B3256853
theorem B2286995 : Blo 1524459 2286995 := bstep (se 1 (by rfl) ⟨1715246, by rfl⟩ : syracuseStep 2286995 = 3430493) B3430493
theorem B1525139 : Blo 1524459 1525139 := bstep (se 1 (by rfl) ⟨1143854, by rfl⟩ : syracuseStep 1525139 = 2287709) B2287709
theorem B1525155 : Blo 1524459 1525155 := bstep (se 1 (by rfl) ⟨1143866, by rfl⟩ : syracuseStep 1525155 = 2287733) B2287733
theorem B2287025 : Blo 1524459 2287025 := bstep (se 2 (by rfl) ⟨857634, by rfl⟩ : syracuseStep 2287025 = 1715269) B1715269
theorem B1525171 : Blo 1524459 1525171 := bstep (se 1 (by rfl) ⟨1143878, by rfl⟩ : syracuseStep 1525171 = 2287757) B2287757
theorem B2573761 : Blo 1524459 2573761 := bstep (se 2 (by rfl) ⟨965160, by rfl⟩ : syracuseStep 2573761 = 1930321) B1930321
theorem B2287043 : Blo 1524459 2287043 := bstep (se 1 (by rfl) ⟨1715282, by rfl⟩ : syracuseStep 2287043 = 3430565) B3430565
theorem B1525187 : Blo 1524459 1525187 := bstep (se 1 (by rfl) ⟨1143890, by rfl⟩ : syracuseStep 1525187 = 2287781) B2287781
theorem B8693189 : Blo 1524459 8693189 := bstep (se 4 (by rfl) ⟨814986, by rfl⟩ : syracuseStep 8693189 = 1629973) B1629973
theorem B4122065 : Blo 1524459 4122065 := bstep (se 2 (by rfl) ⟨1545774, by rfl⟩ : syracuseStep 4122065 = 3091549) B3091549
theorem B1525203 : Blo 1524459 1525203 := bstep (se 1 (by rfl) ⟨1143902, by rfl⟩ : syracuseStep 1525203 = 2287805) B2287805
theorem B2287073 : Blo 1524459 2287073 := bstep (se 2 (by rfl) ⟨857652, by rfl⟩ : syracuseStep 2287073 = 1715305) B1715305
theorem B2573795 : Blo 1524459 2573795 := bstep (se 1 (by rfl) ⟨1930346, by rfl⟩ : syracuseStep 2573795 = 3860693) B3860693
theorem B1525219 : Blo 1524459 1525219 := bstep (se 1 (by rfl) ⟨1143914, by rfl⟩ : syracuseStep 1525219 = 2287829) B2287829
theorem B2442737 : Blo 1524459 2442737 := bstep (se 2 (by rfl) ⟨916026, by rfl⟩ : syracuseStep 2442737 = 1832053) B1832053
theorem B2287091 : Blo 1524459 2287091 := bstep (se 1 (by rfl) ⟨1715318, by rfl⟩ : syracuseStep 2287091 = 3430637) B3430637
theorem B1525235 : Blo 1524459 1525235 := bstep (se 1 (by rfl) ⟨1143926, by rfl⟩ : syracuseStep 1525235 = 2287853) B2287853
theorem B1525251 : Blo 1524459 1525251 := bstep (se 1 (by rfl) ⟨1143938, by rfl⟩ : syracuseStep 1525251 = 2287877) B2287877
theorem B2287121 : Blo 1524459 2287121 := bstep (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) B1715341
theorem B1525267 : Blo 1524459 1525267 := bstep (se 1 (by rfl) ⟨1143950, by rfl⟩ : syracuseStep 1525267 = 2287901) B2287901
theorem B2287139 : Blo 1524459 2287139 := bstep (se 1 (by rfl) ⟨1715354, by rfl⟩ : syracuseStep 2287139 = 3430709) B3430709
theorem B1525283 : Blo 1524459 1525283 := bstep (se 1 (by rfl) ⟨1143962, by rfl⟩ : syracuseStep 1525283 = 2287925) B2287925
theorem B7054897 : Blo 1524459 7054897 := bstep (se 2 (by rfl) ⟨2645586, by rfl⟩ : syracuseStep 7054897 = 5291173) B5291173
theorem B1525299 : Blo 1524459 1525299 := bstep (se 1 (by rfl) ⟨1143974, by rfl⟩ : syracuseStep 1525299 = 2287949) B2287949
theorem B2287169 : Blo 1524459 2287169 := bstep (se 2 (by rfl) ⟨857688, by rfl⟩ : syracuseStep 2287169 = 1715377) B1715377
theorem B1525315 : Blo 1524459 1525315 := bstep (se 1 (by rfl) ⟨1143986, by rfl⟩ : syracuseStep 1525315 = 2287973) B2287973
theorem B6514253 : Blo 1524459 6514253 := bstep (se 3 (by rfl) ⟨1221422, by rfl⟩ : syracuseStep 6514253 = 2442845) B2442845
theorem B2287187 : Blo 1524459 2287187 := bstep (se 1 (by rfl) ⟨1715390, by rfl⟩ : syracuseStep 2287187 = 3430781) B3430781
theorem B1525331 : Blo 1524459 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B4703825 : Blo 1524459 4703825 := bstep (se 2 (by rfl) ⟨1763934, by rfl⟩ : syracuseStep 4703825 = 3527869) B3527869
theorem B2573923 : Blo 1524459 2573923 := bstep (se 1 (by rfl) ⟨1930442, by rfl⟩ : syracuseStep 2573923 = 3860885) B3860885
theorem B1525347 : Blo 1524459 1525347 := bstep (se 1 (by rfl) ⟨1144010, by rfl⟩ : syracuseStep 1525347 = 2288021) B2288021
theorem B4884077 : Blo 1524459 4884077 := bstep (se 3 (by rfl) ⟨915764, by rfl⟩ : syracuseStep 4884077 = 1831529) B1831529
theorem B2287217 : Blo 1524459 2287217 := bstep (se 2 (by rfl) ⟨857706, by rfl⟩ : syracuseStep 2287217 = 1715413) B1715413
theorem B6514289 : Blo 1524459 6514289 := bstep (se 2 (by rfl) ⟨2442858, by rfl⟩ : syracuseStep 6514289 = 4885717) B4885717
theorem B1525363 : Blo 1524459 1525363 := bstep (se 1 (by rfl) ⟨1144022, by rfl⟩ : syracuseStep 1525363 = 2288045) B2288045
theorem B2287235 : Blo 1524459 2287235 := bstep (se 1 (by rfl) ⟨1715426, by rfl⟩ : syracuseStep 2287235 = 3430853) B3430853
theorem B1525379 : Blo 1524459 1525379 := bstep (se 1 (by rfl) ⟨1144034, by rfl⟩ : syracuseStep 1525379 = 2288069) B2288069
theorem B5146253 : Blo 1524459 5146253 := bstep (se 3 (by rfl) ⟨964922, by rfl⟩ : syracuseStep 5146253 = 1929845) B1929845
theorem B3434129 : Blo 1524459 3434129 := bstep (se 2 (by rfl) ⟨1287798, by rfl⟩ : syracuseStep 3434129 = 2575597) B2575597
theorem B1525395 : Blo 1524459 1525395 := bstep (se 1 (by rfl) ⟨1144046, by rfl⟩ : syracuseStep 1525395 = 2288093) B2288093
theorem B2287265 : Blo 1524459 2287265 := bstep (se 2 (by rfl) ⟨857724, by rfl⟩ : syracuseStep 2287265 = 1715449) B1715449
theorem B1525411 : Blo 1524459 1525411 := bstep (se 1 (by rfl) ⟨1144058, by rfl⟩ : syracuseStep 1525411 = 2288117) B2288117
theorem B3434147 : Blo 1524459 3434147 := bstep (se 1 (by rfl) ⟨2575610, by rfl⟩ : syracuseStep 3434147 = 5151221) B5151221
theorem B4343473 : Blo 1524459 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B2287283 : Blo 1524459 2287283 := bstep (se 1 (by rfl) ⟨1715462, by rfl⟩ : syracuseStep 2287283 = 3430925) B3430925
theorem B1525427 : Blo 1524459 1525427 := bstep (se 1 (by rfl) ⟨1144070, by rfl⟩ : syracuseStep 1525427 = 2288141) B2288141
theorem B5146307 : Blo 1524459 5146307 := bstep (se 1 (by rfl) ⟨3859730, by rfl⟩ : syracuseStep 5146307 = 7719461) B7719461
theorem B1525443 : Blo 1524459 1525443 := bstep (se 1 (by rfl) ⟨1144082, by rfl⟩ : syracuseStep 1525443 = 2288165) B2288165
theorem B2287313 : Blo 1524459 2287313 := bstep (se 2 (by rfl) ⟨857742, by rfl⟩ : syracuseStep 2287313 = 1715485) B1715485
theorem B1525459 : Blo 1524459 1525459 := bstep (se 1 (by rfl) ⟨1144094, by rfl⟩ : syracuseStep 1525459 = 2288189) B2288189
theorem B2287331 : Blo 1524459 2287331 := bstep (se 1 (by rfl) ⟨1715498, by rfl⟩ : syracuseStep 2287331 = 3430997) B3430997
theorem B1525475 : Blo 1524459 1525475 := bstep (se 1 (by rfl) ⟨1144106, by rfl⟩ : syracuseStep 1525475 = 2288213) B2288213
theorem B2574065 : Blo 1524459 2574065 := bstep (se 2 (by rfl) ⟨965274, by rfl⟩ : syracuseStep 2574065 = 1930549) B1930549
theorem B1525491 : Blo 1524459 1525491 := bstep (se 1 (by rfl) ⟨1144118, by rfl⟩ : syracuseStep 1525491 = 2288237) B2288237
theorem B2287361 : Blo 1524459 2287361 := bstep (se 2 (by rfl) ⟨857760, by rfl⟩ : syracuseStep 2287361 = 1715521) B1715521
theorem B1525507 : Blo 1524459 1525507 := bstep (se 1 (by rfl) ⟨1144130, by rfl⟩ : syracuseStep 1525507 = 2288261) B2288261
theorem B2287379 : Blo 1524459 2287379 := bstep (se 1 (by rfl) ⟨1715534, by rfl⟩ : syracuseStep 2287379 = 3431069) B3431069
theorem B1525523 : Blo 1524459 1525523 := bstep (se 1 (by rfl) ⟨1144142, by rfl⟩ : syracuseStep 1525523 = 2288285) B2288285
theorem B1525539 : Blo 1524459 1525539 := bstep (se 1 (by rfl) ⟨1144154, by rfl⟩ : syracuseStep 1525539 = 2288309) B2288309
theorem B2287409 : Blo 1524459 2287409 := bstep (se 2 (by rfl) ⟨857778, by rfl⟩ : syracuseStep 2287409 = 1715557) B1715557
theorem B1525555 : Blo 1524459 1525555 := bstep (se 1 (by rfl) ⟨1144166, by rfl⟩ : syracuseStep 1525555 = 2288333) B2288333
theorem B2287427 : Blo 1524459 2287427 := bstep (se 1 (by rfl) ⟨1715570, by rfl⟩ : syracuseStep 2287427 = 3431141) B3431141
theorem B1525571 : Blo 1524459 1525571 := bstep (se 1 (by rfl) ⟨1144178, by rfl⟩ : syracuseStep 1525571 = 2288357) B2288357
theorem B2172739 : Blo 1524459 2172739 := bstep (se 1 (by rfl) ⟨1629554, by rfl⟩ : syracuseStep 2172739 = 3259109) B3259109
theorem B1525587 : Blo 1524459 1525587 := bstep (se 1 (by rfl) ⟨1144190, by rfl⟩ : syracuseStep 1525587 = 2288381) B2288381
theorem B2287457 : Blo 1524459 2287457 := bstep (se 2 (by rfl) ⟨857796, by rfl⟩ : syracuseStep 2287457 = 1715593) B1715593
theorem B1525603 : Blo 1524459 1525603 := bstep (se 1 (by rfl) ⟨1144202, by rfl⟩ : syracuseStep 1525603 = 2288405) B2288405
theorem B2574193 : Blo 1524459 2574193 := bstep (se 2 (by rfl) ⟨965322, by rfl⟩ : syracuseStep 2574193 = 1930645) B1930645
theorem B2287475 : Blo 1524459 2287475 := bstep (se 1 (by rfl) ⟨1715606, by rfl⟩ : syracuseStep 2287475 = 3431213) B3431213
theorem B1525619 : Blo 1524459 1525619 := bstep (se 1 (by rfl) ⟨1144214, by rfl⟩ : syracuseStep 1525619 = 2288429) B2288429
theorem B1525635 : Blo 1524459 1525635 := bstep (se 1 (by rfl) ⟨1144226, by rfl⟩ : syracuseStep 1525635 = 2288453) B2288453
theorem B2287505 : Blo 1524459 2287505 := bstep (se 2 (by rfl) ⟨857814, by rfl⟩ : syracuseStep 2287505 = 1715629) B1715629
theorem B3860369 : Blo 1524459 3860369 := bstep (se 2 (by rfl) ⟨1447638, by rfl⟩ : syracuseStep 3860369 = 2895277) B2895277
theorem B2574227 : Blo 1524459 2574227 := bstep (se 1 (by rfl) ⟨1930670, by rfl⟩ : syracuseStep 2574227 = 3861341) B3861341
theorem B1525651 : Blo 1524459 1525651 := bstep (se 1 (by rfl) ⟨1144238, by rfl⟩ : syracuseStep 1525651 = 2288477) B2288477
theorem B2287523 : Blo 1524459 2287523 := bstep (se 1 (by rfl) ⟨1715642, by rfl⟩ : syracuseStep 2287523 = 3431285) B3431285
theorem B1525667 : Blo 1524459 1525667 := bstep (se 1 (by rfl) ⟨1144250, by rfl⟩ : syracuseStep 1525667 = 2288501) B2288501
theorem B5793713 : Blo 1524459 5793713 := bstep (se 2 (by rfl) ⟨2172642, by rfl⟩ : syracuseStep 5793713 = 4345285) B4345285
theorem B1525683 : Blo 1524459 1525683 := bstep (se 1 (by rfl) ⟨1144262, by rfl⟩ : syracuseStep 1525683 = 2288525) B2288525
theorem B3434417 : Blo 1524459 3434417 := bstep (se 2 (by rfl) ⟨1287906, by rfl⟩ : syracuseStep 3434417 = 2575813) B2575813
theorem B2287553 : Blo 1524459 2287553 := bstep (se 2 (by rfl) ⟨857832, by rfl⟩ : syracuseStep 2287553 = 1715665) B1715665
theorem B3860419 : Blo 1524459 3860419 := bstep (se 1 (by rfl) ⟨2895314, by rfl⟩ : syracuseStep 3860419 = 5790629) B5790629
theorem B1525699 : Blo 1524459 1525699 := bstep (se 1 (by rfl) ⟨1144274, by rfl⟩ : syracuseStep 1525699 = 2288549) B2288549
theorem B3434435 : Blo 1524459 3434435 := bstep (se 1 (by rfl) ⟨2575826, by rfl⟩ : syracuseStep 3434435 = 5151653) B5151653
theorem B5146577 : Blo 1524459 5146577 := bstep (se 2 (by rfl) ⟨1929966, by rfl⟩ : syracuseStep 5146577 = 3859933) B3859933
theorem B2287571 : Blo 1524459 2287571 := bstep (se 1 (by rfl) ⟨1715678, by rfl⟩ : syracuseStep 2287571 = 3431357) B3431357
theorem B1525715 : Blo 1524459 1525715 := bstep (se 1 (by rfl) ⟨1144286, by rfl⟩ : syracuseStep 1525715 = 2288573) B2288573
theorem B1525731 : Blo 1524459 1525731 := bstep (se 1 (by rfl) ⟨1144298, by rfl⟩ : syracuseStep 1525731 = 2288597) B2288597
theorem B7727075 : Blo 1524459 7727075 := bstep (se 1 (by rfl) ⟨5795306, by rfl⟩ : syracuseStep 7727075 = 11590613) B11590613
theorem B2287601 : Blo 1524459 2287601 := bstep (se 2 (by rfl) ⟨857850, by rfl⟩ : syracuseStep 2287601 = 1715701) B1715701
theorem B1525747 : Blo 1524459 1525747 := bstep (se 1 (by rfl) ⟨1144310, by rfl⟩ : syracuseStep 1525747 = 2288621) B2288621
theorem B3663875 : Blo 1524459 3663875 := bstep (se 1 (by rfl) ⟨2747906, by rfl⟩ : syracuseStep 3663875 = 5495813) B5495813
theorem B2287619 : Blo 1524459 2287619 := bstep (se 1 (by rfl) ⟨1715714, by rfl⟩ : syracuseStep 2287619 = 3431429) B3431429
theorem B1525763 : Blo 1524459 1525763 := bstep (se 1 (by rfl) ⟨1144322, by rfl⟩ : syracuseStep 1525763 = 2288645) B2288645
theorem B7333901 : Blo 1524459 7333901 := bstep (se 3 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 7333901 = 2750213) B2750213
theorem B2574355 : Blo 1524459 2574355 := bstep (se 1 (by rfl) ⟨1930766, by rfl⟩ : syracuseStep 2574355 = 3861533) B3861533
theorem B1525779 : Blo 1524459 1525779 := bstep (se 1 (by rfl) ⟨1144334, by rfl⟩ : syracuseStep 1525779 = 2288669) B2288669
theorem B2287649 : Blo 1524459 2287649 := bstep (se 2 (by rfl) ⟨857868, by rfl⟩ : syracuseStep 2287649 = 1715737) B1715737
theorem B1525795 : Blo 1524459 1525795 := bstep (se 1 (by rfl) ⟨1144346, by rfl⟩ : syracuseStep 1525795 = 2288693) B2288693
theorem B2287667 : Blo 1524459 2287667 := bstep (se 1 (by rfl) ⟨1715750, by rfl⟩ : syracuseStep 2287667 = 3431501) B3431501
theorem B1525811 : Blo 1524459 1525811 := bstep (se 1 (by rfl) ⟨1144358, by rfl⟩ : syracuseStep 1525811 = 2288717) B2288717
theorem B1525827 : Blo 1524459 1525827 := bstep (se 1 (by rfl) ⟨1144370, by rfl⟩ : syracuseStep 1525827 = 2288741) B2288741
theorem B2287697 : Blo 1524459 2287697 := bstep (se 2 (by rfl) ⟨857886, by rfl⟩ : syracuseStep 2287697 = 1715773) B1715773
theorem B3860561 : Blo 1524459 3860561 := bstep (se 2 (by rfl) ⟨1447710, by rfl⟩ : syracuseStep 3860561 = 2895421) B2895421
theorem B1525843 : Blo 1524459 1525843 := bstep (se 1 (by rfl) ⟨1144382, by rfl⟩ : syracuseStep 1525843 = 2288765) B2288765
theorem B2287715 : Blo 1524459 2287715 := bstep (se 1 (by rfl) ⟨1715786, by rfl⟩ : syracuseStep 2287715 = 3431573) B3431573
theorem B1525859 : Blo 1524459 1525859 := bstep (se 1 (by rfl) ⟨1144394, by rfl⟩ : syracuseStep 1525859 = 2288789) B2288789
theorem B1525875 : Blo 1524459 1525875 := bstep (se 1 (by rfl) ⟨1144406, by rfl⟩ : syracuseStep 1525875 = 2288813) B2288813
theorem B2287745 : Blo 1524459 2287745 := bstep (se 2 (by rfl) ⟨857904, by rfl⟩ : syracuseStep 2287745 = 1715809) B1715809
theorem B1525891 : Blo 1524459 1525891 := bstep (se 1 (by rfl) ⟨1144418, by rfl⟩ : syracuseStep 1525891 = 2288837) B2288837
theorem B2287763 : Blo 1524459 2287763 := bstep (se 1 (by rfl) ⟨1715822, by rfl⟩ : syracuseStep 2287763 = 3431645) B3431645
theorem B1525907 : Blo 1524459 1525907 := bstep (se 1 (by rfl) ⟨1144430, by rfl⟩ : syracuseStep 1525907 = 2288861) B2288861
theorem B2574497 : Blo 1524459 2574497 := bstep (se 2 (by rfl) ⟨965436, by rfl⟩ : syracuseStep 2574497 = 1930873) B1930873
theorem B1525923 : Blo 1524459 1525923 := bstep (se 1 (by rfl) ⟨1144442, by rfl⟩ : syracuseStep 1525923 = 2288885) B2288885
theorem B2287793 : Blo 1524459 2287793 := bstep (se 2 (by rfl) ⟨857922, by rfl⟩ : syracuseStep 2287793 = 1715845) B1715845
theorem B1525939 : Blo 1524459 1525939 := bstep (se 1 (by rfl) ⟨1144454, by rfl⟩ : syracuseStep 1525939 = 2288909) B2288909
theorem B2287811 : Blo 1524459 2287811 := bstep (se 1 (by rfl) ⟨1715858, by rfl⟩ : syracuseStep 2287811 = 3431717) B3431717
theorem B1525955 : Blo 1524459 1525955 := bstep (se 1 (by rfl) ⟨1144466, by rfl⟩ : syracuseStep 1525955 = 2288933) B2288933
theorem B1525971 : Blo 1524459 1525971 := bstep (se 1 (by rfl) ⟨1144478, by rfl⟩ : syracuseStep 1525971 = 2288957) B2288957
theorem B2287841 : Blo 1524459 2287841 := bstep (se 2 (by rfl) ⟨857940, by rfl⟩ : syracuseStep 2287841 = 1715881) B1715881
theorem B1525987 : Blo 1524459 1525987 := bstep (se 1 (by rfl) ⟨1144490, by rfl⟩ : syracuseStep 1525987 = 2288981) B2288981
theorem B2287859 : Blo 1524459 2287859 := bstep (se 1 (by rfl) ⟨1715894, by rfl⟩ : syracuseStep 2287859 = 3431789) B3431789
theorem B1526003 : Blo 1524459 1526003 := bstep (se 1 (by rfl) ⟨1144502, by rfl⟩ : syracuseStep 1526003 = 2289005) B2289005
theorem B1526019 : Blo 1524459 1526019 := bstep (se 1 (by rfl) ⟨1144514, by rfl⟩ : syracuseStep 1526019 = 2289029) B2289029
theorem B6605069 : Blo 1524459 6605069 := bstep (se 3 (by rfl) ⟨1238450, by rfl⟩ : syracuseStep 6605069 = 2476901) B2476901
theorem B2287889 : Blo 1524459 2287889 := bstep (se 2 (by rfl) ⟨857958, by rfl⟩ : syracuseStep 2287889 = 1715917) B1715917
theorem B2443537 : Blo 1524459 2443537 := bstep (se 2 (by rfl) ⟨916326, by rfl⟩ : syracuseStep 2443537 = 1832653) B1832653
theorem B1526035 : Blo 1524459 1526035 := bstep (se 1 (by rfl) ⟨1144526, by rfl⟩ : syracuseStep 1526035 = 2289053) B2289053
theorem B2574625 : Blo 1524459 2574625 := bstep (se 2 (by rfl) ⟨965484, by rfl⟩ : syracuseStep 2574625 = 1930969) B1930969
theorem B2287907 : Blo 1524459 2287907 := bstep (se 1 (by rfl) ⟨1715930, by rfl⟩ : syracuseStep 2287907 = 3431861) B3431861
theorem B1526051 : Blo 1524459 1526051 := bstep (se 1 (by rfl) ⟨1144538, by rfl⟩ : syracuseStep 1526051 = 2289077) B2289077
theorem B1763635 : Blo 1524459 1763635 := bstep (se 1 (by rfl) ⟨1322726, by rfl⟩ : syracuseStep 1763635 = 2645453) B2645453
theorem B1526067 : Blo 1524459 1526067 := bstep (se 1 (by rfl) ⟨1144550, by rfl⟩ : syracuseStep 1526067 = 2289101) B2289101
theorem B2287937 : Blo 1524459 2287937 := bstep (se 2 (by rfl) ⟨857976, by rfl⟩ : syracuseStep 2287937 = 1715953) B1715953
theorem B2574659 : Blo 1524459 2574659 := bstep (se 1 (by rfl) ⟨1930994, by rfl⟩ : syracuseStep 2574659 = 3861989) B3861989
theorem B1526083 : Blo 1524459 1526083 := bstep (se 1 (by rfl) ⟨1144562, by rfl⟩ : syracuseStep 1526083 = 2289125) B2289125
theorem B2287955 : Blo 1524459 2287955 := bstep (se 1 (by rfl) ⟨1715966, by rfl⟩ : syracuseStep 2287955 = 3431933) B3431933
theorem B1526099 : Blo 1524459 1526099 := bstep (se 1 (by rfl) ⟨1144574, by rfl⟩ : syracuseStep 1526099 = 2289149) B2289149
theorem B1526115 : Blo 1524459 1526115 := bstep (se 1 (by rfl) ⟨1144586, by rfl⟩ : syracuseStep 1526115 = 2289173) B2289173
theorem B2287985 : Blo 1524459 2287985 := bstep (se 2 (by rfl) ⟨857994, by rfl⟩ : syracuseStep 2287985 = 1715989) B1715989
theorem B1526131 : Blo 1524459 1526131 := bstep (se 1 (by rfl) ⟨1144598, by rfl⟩ : syracuseStep 1526131 = 2289197) B2289197
theorem B2288003 : Blo 1524459 2288003 := bstep (se 1 (by rfl) ⟨1716002, by rfl⟩ : syracuseStep 2288003 = 3432005) B3432005
theorem B1526147 : Blo 1524459 1526147 := bstep (se 1 (by rfl) ⟨1144610, by rfl⟩ : syracuseStep 1526147 = 2289221) B2289221
theorem B1526163 : Blo 1524459 1526163 := bstep (se 1 (by rfl) ⟨1144622, by rfl⟩ : syracuseStep 1526163 = 2289245) B2289245
theorem B2288033 : Blo 1524459 2288033 := bstep (se 2 (by rfl) ⟨858012, by rfl⟩ : syracuseStep 2288033 = 1716025) B1716025
theorem B1526179 : Blo 1524459 1526179 := bstep (se 1 (by rfl) ⟨1144634, by rfl⟩ : syracuseStep 1526179 = 2289269) B2289269
theorem B2288051 : Blo 1524459 2288051 := bstep (se 1 (by rfl) ⟨1716038, by rfl⟩ : syracuseStep 2288051 = 3432077) B3432077
theorem B1526195 : Blo 1524459 1526195 := bstep (se 1 (by rfl) ⟨1144646, by rfl⟩ : syracuseStep 1526195 = 2289293) B2289293
theorem B2574787 : Blo 1524459 2574787 := bstep (se 1 (by rfl) ⟨1931090, by rfl⟩ : syracuseStep 2574787 = 3862181) B3862181
theorem B1526211 : Blo 1524459 1526211 := bstep (se 1 (by rfl) ⟨1144658, by rfl⟩ : syracuseStep 1526211 = 2289317) B2289317
theorem B2288081 : Blo 1524459 2288081 := bstep (se 2 (by rfl) ⟨858030, by rfl⟩ : syracuseStep 2288081 = 1716061) B1716061
theorem B1526227 : Blo 1524459 1526227 := bstep (se 1 (by rfl) ⟨1144670, by rfl⟩ : syracuseStep 1526227 = 2289341) B2289341
theorem B2288099 : Blo 1524459 2288099 := bstep (se 1 (by rfl) ⟨1716074, by rfl⟩ : syracuseStep 2288099 = 3432149) B3432149
theorem B1526243 : Blo 1524459 1526243 := bstep (se 1 (by rfl) ⟨1144682, by rfl⟩ : syracuseStep 1526243 = 2289365) B2289365
theorem B5147117 : Blo 1524459 5147117 := bstep (se 3 (by rfl) ⟨965084, by rfl⟩ : syracuseStep 5147117 = 1930169) B1930169
theorem B1526259 : Blo 1524459 1526259 := bstep (se 1 (by rfl) ⟨1144694, by rfl⟩ : syracuseStep 1526259 = 2289389) B2289389
theorem B2288129 : Blo 1524459 2288129 := bstep (se 2 (by rfl) ⟨858048, by rfl⟩ : syracuseStep 2288129 = 1716097) B1716097
theorem B1526275 : Blo 1524459 1526275 := bstep (se 1 (by rfl) ⟨1144706, by rfl⟩ : syracuseStep 1526275 = 2289413) B2289413
theorem B2288147 : Blo 1524459 2288147 := bstep (se 1 (by rfl) ⟨1716110, by rfl⟩ : syracuseStep 2288147 = 3432221) B3432221
theorem B1526291 : Blo 1524459 1526291 := bstep (se 1 (by rfl) ⟨1144718, by rfl⟩ : syracuseStep 1526291 = 2289437) B2289437
theorem B5147171 : Blo 1524459 5147171 := bstep (se 1 (by rfl) ⟨3860378, by rfl⟩ : syracuseStep 5147171 = 7720757) B7720757
theorem B1526307 : Blo 1524459 1526307 := bstep (se 1 (by rfl) ⟨1144730, by rfl⟩ : syracuseStep 1526307 = 2289461) B2289461
theorem B2288177 : Blo 1524459 2288177 := bstep (se 2 (by rfl) ⟨858066, by rfl⟩ : syracuseStep 2288177 = 1716133) B1716133
theorem B1526323 : Blo 1524459 1526323 := bstep (se 1 (by rfl) ⟨1144742, by rfl⟩ : syracuseStep 1526323 = 2289485) B2289485
theorem B2288195 : Blo 1524459 2288195 := bstep (se 1 (by rfl) ⟨1716146, by rfl⟩ : syracuseStep 2288195 = 3432293) B3432293
theorem B1526339 : Blo 1524459 1526339 := bstep (se 1 (by rfl) ⟨1144754, by rfl⟩ : syracuseStep 1526339 = 2289509) B2289509
theorem B2574929 : Blo 1524459 2574929 := bstep (se 2 (by rfl) ⟨965598, by rfl⟩ : syracuseStep 2574929 = 1931197) B1931197
theorem B1526355 : Blo 1524459 1526355 := bstep (se 1 (by rfl) ⟨1144766, by rfl⟩ : syracuseStep 1526355 = 2289533) B2289533
theorem B2288225 : Blo 1524459 2288225 := bstep (se 2 (by rfl) ⟨858084, by rfl⟩ : syracuseStep 2288225 = 1716169) B1716169
theorem B1526371 : Blo 1524459 1526371 := bstep (se 1 (by rfl) ⟨1144778, by rfl⟩ : syracuseStep 1526371 = 2289557) B2289557
theorem B2894449 : Blo 1524459 2894449 := bstep (se 2 (by rfl) ⟨1085418, by rfl⟩ : syracuseStep 2894449 = 2170837) B2170837
theorem B2288243 : Blo 1524459 2288243 := bstep (se 1 (by rfl) ⟨1716182, by rfl⟩ : syracuseStep 2288243 = 3432365) B3432365
theorem B1526387 : Blo 1524459 1526387 := bstep (se 1 (by rfl) ⟨1144790, by rfl⟩ : syracuseStep 1526387 = 2289581) B2289581
theorem B1526403 : Blo 1524459 1526403 := bstep (se 1 (by rfl) ⟨1144802, by rfl⟩ : syracuseStep 1526403 = 2289605) B2289605
theorem B2288273 : Blo 1524459 2288273 := bstep (se 2 (by rfl) ⟨858102, by rfl⟩ : syracuseStep 2288273 = 1716205) B1716205
theorem B1526419 : Blo 1524459 1526419 := bstep (se 1 (by rfl) ⟨1144814, by rfl⟩ : syracuseStep 1526419 = 2289629) B2289629
theorem B9767587 : Blo 1524459 9767587 := bstep (se 1 (by rfl) ⟨7325690, by rfl⟩ : syracuseStep 9767587 = 14651381) B14651381
theorem B2288291 : Blo 1524459 2288291 := bstep (se 1 (by rfl) ⟨1716218, by rfl⟩ : syracuseStep 2288291 = 3432437) B3432437
theorem B1526435 : Blo 1524459 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B1526451 : Blo 1524459 1526451 := bstep (se 1 (by rfl) ⟨1144838, by rfl⟩ : syracuseStep 1526451 = 2289677) B2289677
theorem B2288321 : Blo 1524459 2288321 := bstep (se 2 (by rfl) ⟨858120, by rfl⟩ : syracuseStep 2288321 = 1716241) B1716241
theorem B2575057 : Blo 1524459 2575057 := bstep (se 2 (by rfl) ⟨965646, by rfl⟩ : syracuseStep 2575057 = 1931293) B1931293
theorem B2288339 : Blo 1524459 2288339 := bstep (se 1 (by rfl) ⟨1716254, by rfl⟩ : syracuseStep 2288339 = 3432509) B3432509
theorem B2288369 : Blo 1524459 2288369 := bstep (se 2 (by rfl) ⟨858138, by rfl⟩ : syracuseStep 2288369 = 1716277) B1716277
theorem B2575091 : Blo 1524459 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B2288387 : Blo 1524459 2288387 := bstep (se 1 (by rfl) ⟨1716290, by rfl⟩ : syracuseStep 2288387 = 3432581) B3432581
theorem B2894609 : Blo 1524459 2894609 := bstep (se 2 (by rfl) ⟨1085478, by rfl⟩ : syracuseStep 2894609 = 2170957) B2170957
theorem B93940501 : Blo 1524459 93940501 := bstep (se 6 (by rfl) ⟨2201730, by rfl⟩ : syracuseStep 93940501 = 4403461) B4403461
theorem B2288417 : Blo 1524459 2288417 := bstep (se 2 (by rfl) ⟨858156, by rfl⟩ : syracuseStep 2288417 = 1716313) B1716313
theorem B4180781 : Blo 1524459 4180781 := bstep (se 3 (by rfl) ⟨783896, by rfl⟩ : syracuseStep 4180781 = 1567793) B1567793
theorem B5147441 : Blo 1524459 5147441 := bstep (se 2 (by rfl) ⟨1930290, by rfl⟩ : syracuseStep 5147441 = 3860581) B3860581
theorem B2288435 : Blo 1524459 2288435 := bstep (se 1 (by rfl) ⟨1716326, by rfl⟩ : syracuseStep 2288435 = 3432653) B3432653
theorem B2288465 : Blo 1524459 2288465 := bstep (se 2 (by rfl) ⟨858174, by rfl⟩ : syracuseStep 2288465 = 1716349) B1716349
theorem B2288483 : Blo 1524459 2288483 := bstep (se 1 (by rfl) ⟨1716362, by rfl⟩ : syracuseStep 2288483 = 3432725) B3432725
theorem B2575219 : Blo 1524459 2575219 := bstep (se 1 (by rfl) ⟨1931414, by rfl⟩ : syracuseStep 2575219 = 3862829) B3862829
theorem B2288513 : Blo 1524459 2288513 := bstep (se 2 (by rfl) ⟨858192, by rfl⟩ : syracuseStep 2288513 = 1716385) B1716385
theorem B2288531 : Blo 1524459 2288531 := bstep (se 1 (by rfl) ⟨1716398, by rfl⟩ : syracuseStep 2288531 = 3432797) B3432797
theorem B1715107 : Blo 1524459 1715107 := bstep (se 1 (by rfl) ⟨1286330, by rfl⟩ : syracuseStep 1715107 = 2572661) B2572661
theorem B4344749 : Blo 1524459 4344749 := bstep (se 3 (by rfl) ⟨814640, by rfl⟩ : syracuseStep 4344749 = 1629281) B1629281
theorem B2288561 : Blo 1524459 2288561 := bstep (se 2 (by rfl) ⟨858210, by rfl⟩ : syracuseStep 2288561 = 1716421) B1716421
theorem B2288579 : Blo 1524459 2288579 := bstep (se 1 (by rfl) ⟨1716434, by rfl⟩ : syracuseStep 2288579 = 3432869) B3432869
theorem B2288609 : Blo 1524459 2288609 := bstep (se 2 (by rfl) ⟨858228, by rfl⟩ : syracuseStep 2288609 = 1716457) B1716457
theorem B2288627 : Blo 1524459 2288627 := bstep (se 1 (by rfl) ⟨1716470, by rfl⟩ : syracuseStep 2288627 = 3432941) B3432941
theorem B2575361 : Blo 1524459 2575361 := bstep (se 2 (by rfl) ⟨965760, by rfl⟩ : syracuseStep 2575361 = 1931521) B1931521
theorem B2288657 : Blo 1524459 2288657 := bstep (se 2 (by rfl) ⟨858246, by rfl⟩ : syracuseStep 2288657 = 1716493) B1716493
theorem B2288675 : Blo 1524459 2288675 := bstep (se 1 (by rfl) ⟨1716506, by rfl⟩ : syracuseStep 2288675 = 3433013) B3433013
theorem B3861553 : Blo 1524459 3861553 := bstep (se 2 (by rfl) ⟨1448082, by rfl⟩ : syracuseStep 3861553 = 2896165) B2896165
theorem B1715251 : Blo 1524459 1715251 := bstep (se 1 (by rfl) ⟨1286438, by rfl⟩ : syracuseStep 1715251 = 2572877) B2572877
theorem B2288705 : Blo 1524459 2288705 := bstep (se 2 (by rfl) ⟨858264, by rfl⟩ : syracuseStep 2288705 = 1716529) B1716529
theorem B2288723 : Blo 1524459 2288723 := bstep (se 1 (by rfl) ⟨1716542, by rfl⟩ : syracuseStep 2288723 = 3433085) B3433085
theorem B4344931 : Blo 1524459 4344931 := bstep (se 1 (by rfl) ⟨3258698, by rfl⟩ : syracuseStep 4344931 = 6517397) B6517397
theorem B46967921 : Blo 1524459 46967921 := bstep (se 2 (by rfl) ⟨17612970, by rfl⟩ : syracuseStep 46967921 = 35225941) B35225941
theorem B2288753 : Blo 1524459 2288753 := bstep (se 2 (by rfl) ⟨858282, by rfl⟩ : syracuseStep 2288753 = 1716565) B1716565
theorem B2575489 : Blo 1524459 2575489 := bstep (se 2 (by rfl) ⟨965808, by rfl⟩ : syracuseStep 2575489 = 1931617) B1931617
theorem B2288771 : Blo 1524459 2288771 := bstep (se 1 (by rfl) ⟨1716578, by rfl⟩ : syracuseStep 2288771 = 3433157) B3433157
theorem B4344977 : Blo 1524459 4344977 := bstep (se 2 (by rfl) ⟨1629366, by rfl⟩ : syracuseStep 4344977 = 3258733) B3258733
theorem B2288801 : Blo 1524459 2288801 := bstep (se 2 (by rfl) ⟨858300, by rfl⟩ : syracuseStep 2288801 = 1716601) B1716601
theorem B2895011 : Blo 1524459 2895011 := bstep (se 1 (by rfl) ⟨2171258, by rfl⟩ : syracuseStep 2895011 = 4342517) B4342517
theorem B2575523 : Blo 1524459 2575523 := bstep (se 1 (by rfl) ⟨1931642, by rfl⟩ : syracuseStep 2575523 = 3863285) B3863285
theorem B2288819 : Blo 1524459 2288819 := bstep (se 1 (by rfl) ⟨1716614, by rfl⟩ : syracuseStep 2288819 = 3433229) B3433229
theorem B1715395 : Blo 1524459 1715395 := bstep (se 1 (by rfl) ⟨1286546, by rfl⟩ : syracuseStep 1715395 = 2573093) B2573093
theorem B3665105 : Blo 1524459 3665105 := bstep (se 2 (by rfl) ⟨1374414, by rfl⟩ : syracuseStep 3665105 = 2748829) B2748829
theorem B2288849 : Blo 1524459 2288849 := bstep (se 2 (by rfl) ⟨858318, by rfl⟩ : syracuseStep 2288849 = 1716637) B1716637
theorem B2288867 : Blo 1524459 2288867 := bstep (se 1 (by rfl) ⟨1716650, by rfl⟩ : syracuseStep 2288867 = 3433301) B3433301
theorem B13389041 : Blo 1524459 13389041 := bstep (se 2 (by rfl) ⟨5020890, by rfl⟩ : syracuseStep 13389041 = 10041781) B10041781
theorem B14666993 : Blo 1524459 14666993 := bstep (se 2 (by rfl) ⟨5500122, by rfl⟩ : syracuseStep 14666993 = 11000245) B11000245
theorem B2288897 : Blo 1524459 2288897 := bstep (se 2 (by rfl) ⟨858336, by rfl⟩ : syracuseStep 2288897 = 1716673) B1716673
theorem B2288915 : Blo 1524459 2288915 := bstep (se 1 (by rfl) ⟨1716686, by rfl⟩ : syracuseStep 2288915 = 3433373) B3433373
theorem B2575651 : Blo 1524459 2575651 := bstep (se 1 (by rfl) ⟨1931738, by rfl⟩ : syracuseStep 2575651 = 3863477) B3863477
theorem B2288945 : Blo 1524459 2288945 := bstep (se 2 (by rfl) ⟨858354, by rfl⟩ : syracuseStep 2288945 = 1716709) B1716709
theorem B3861827 : Blo 1524459 3861827 := bstep (se 1 (by rfl) ⟨2896370, by rfl⟩ : syracuseStep 3861827 = 5792741) B5792741
theorem B2288963 : Blo 1524459 2288963 := bstep (se 1 (by rfl) ⟨1716722, by rfl⟩ : syracuseStep 2288963 = 3433445) B3433445
theorem B8686925 : Blo 1524459 8686925 := bstep (se 3 (by rfl) ⟨1628798, by rfl⟩ : syracuseStep 8686925 = 3257597) B3257597
theorem B5147981 : Blo 1524459 5147981 := bstep (se 3 (by rfl) ⟨965246, by rfl⟩ : syracuseStep 5147981 = 1930493) B1930493
theorem B5500237 : Blo 1524459 5500237 := bstep (se 3 (by rfl) ⟨1031294, by rfl⟩ : syracuseStep 5500237 = 2062589) B2062589
theorem B1715539 : Blo 1524459 1715539 := bstep (se 1 (by rfl) ⟨1286654, by rfl⟩ : syracuseStep 1715539 = 2573309) B2573309
theorem B9776483 : Blo 1524459 9776483 := bstep (se 1 (by rfl) ⟨7332362, by rfl⟩ : syracuseStep 9776483 = 14664725) B14664725
theorem B2288993 : Blo 1524459 2288993 := bstep (se 2 (by rfl) ⟨858372, by rfl⟩ : syracuseStep 2288993 = 1716745) B1716745
theorem B5795171 : Blo 1524459 5795171 := bstep (se 1 (by rfl) ⟨4346378, by rfl⟩ : syracuseStep 5795171 = 8692757) B8692757
theorem B5795185 : Blo 1524459 5795185 := bstep (se 2 (by rfl) ⟨2173194, by rfl⟩ : syracuseStep 5795185 = 4346389) B4346389
theorem B2289011 : Blo 1524459 2289011 := bstep (se 1 (by rfl) ⟨1716758, by rfl⟩ : syracuseStep 2289011 = 3433517) B3433517
theorem B5148035 : Blo 1524459 5148035 := bstep (se 1 (by rfl) ⟨3861026, by rfl⟩ : syracuseStep 5148035 = 7722053) B7722053
theorem B2289041 : Blo 1524459 2289041 := bstep (se 2 (by rfl) ⟨858390, by rfl⟩ : syracuseStep 2289041 = 1716781) B1716781
theorem B2289059 : Blo 1524459 2289059 := bstep (se 1 (by rfl) ⟨1716794, by rfl⟩ : syracuseStep 2289059 = 3433589) B3433589
theorem B2575793 : Blo 1524459 2575793 := bstep (se 2 (by rfl) ⟨965922, by rfl⟩ : syracuseStep 2575793 = 1931845) B1931845
theorem B2289089 : Blo 1524459 2289089 := bstep (se 2 (by rfl) ⟨858408, by rfl⟩ : syracuseStep 2289089 = 1716817) B1716817
theorem B10431949 : Blo 1524459 10431949 := bstep (se 3 (by rfl) ⟨1955990, by rfl⟩ : syracuseStep 10431949 = 3911981) B3911981
theorem B2289107 : Blo 1524459 2289107 := bstep (se 1 (by rfl) ⟨1716830, by rfl⟩ : syracuseStep 2289107 = 3433661) B3433661
theorem B2444755 : Blo 1524459 2444755 := bstep (se 1 (by rfl) ⟨1833566, by rfl⟩ : syracuseStep 2444755 = 3667133) B3667133
theorem B1715683 : Blo 1524459 1715683 := bstep (se 1 (by rfl) ⟨1286762, by rfl⟩ : syracuseStep 1715683 = 2573525) B2573525
theorem B7720433 : Blo 1524459 7720433 := bstep (se 2 (by rfl) ⟨2895162, by rfl⟩ : syracuseStep 7720433 = 5790325) B5790325
theorem B13028849 : Blo 1524459 13028849 := bstep (se 2 (by rfl) ⟨4885818, by rfl⟩ : syracuseStep 13028849 = 9771637) B9771637
theorem B2289137 : Blo 1524459 2289137 := bstep (se 2 (by rfl) ⟨858426, by rfl⟩ : syracuseStep 2289137 = 1716853) B1716853
theorem B3862019 : Blo 1524459 3862019 := bstep (se 1 (by rfl) ⟨2896514, by rfl⟩ : syracuseStep 3862019 = 5793029) B5793029
theorem B2289155 : Blo 1524459 2289155 := bstep (se 1 (by rfl) ⟨1716866, by rfl⟩ : syracuseStep 2289155 = 3433733) B3433733
theorem B2289185 : Blo 1524459 2289185 := bstep (se 2 (by rfl) ⟨858444, by rfl⟩ : syracuseStep 2289185 = 1716889) B1716889
theorem B2289203 : Blo 1524459 2289203 := bstep (se 1 (by rfl) ⟨1716902, by rfl⟩ : syracuseStep 2289203 = 3433805) B3433805
theorem B11578949 : Blo 1524459 11578949 := bstep (se 4 (by rfl) ⟨1085526, by rfl⟩ : syracuseStep 11578949 = 2171053) B2171053
theorem B3255889 : Blo 1524459 3255889 := bstep (se 2 (by rfl) ⟨1220958, by rfl⟩ : syracuseStep 3255889 = 2441917) B2441917
theorem B2289233 : Blo 1524459 2289233 := bstep (se 2 (by rfl) ⟨858462, by rfl⟩ : syracuseStep 2289233 = 1716925) B1716925
theorem B2289251 : Blo 1524459 2289251 := bstep (se 1 (by rfl) ⟨1716938, by rfl⟩ : syracuseStep 2289251 = 3433877) B3433877
theorem B1715827 : Blo 1524459 1715827 := bstep (se 1 (by rfl) ⟨1286870, by rfl⟩ : syracuseStep 1715827 = 2573741) B2573741
theorem B2289281 : Blo 1524459 2289281 := bstep (se 2 (by rfl) ⟨858480, by rfl⟩ : syracuseStep 2289281 = 1716961) B1716961
theorem B5148305 : Blo 1524459 5148305 := bstep (se 2 (by rfl) ⟨1930614, by rfl⟩ : syracuseStep 5148305 = 3861229) B3861229
theorem B2289299 : Blo 1524459 2289299 := bstep (se 1 (by rfl) ⟨1716974, by rfl⟩ : syracuseStep 2289299 = 3433949) B3433949
theorem B2289329 : Blo 1524459 2289329 := bstep (se 2 (by rfl) ⟨858498, by rfl⟩ : syracuseStep 2289329 = 1716997) B1716997
theorem B2289347 : Blo 1524459 2289347 := bstep (se 1 (by rfl) ⟨1717010, by rfl⟩ : syracuseStep 2289347 = 3434021) B3434021
theorem B2289377 : Blo 1524459 2289377 := bstep (se 2 (by rfl) ⟨858516, by rfl⟩ : syracuseStep 2289377 = 1717033) B1717033
theorem B1650403 : Blo 1524459 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B2289395 : Blo 1524459 2289395 := bstep (se 1 (by rfl) ⟨1717046, by rfl⟩ : syracuseStep 2289395 = 3434093) B3434093
theorem B1715971 : Blo 1524459 1715971 := bstep (se 1 (by rfl) ⟨1286978, by rfl⟩ : syracuseStep 1715971 = 2573957) B2573957
theorem B2289425 : Blo 1524459 2289425 := bstep (se 2 (by rfl) ⟨858534, by rfl⟩ : syracuseStep 2289425 = 1717069) B1717069
theorem B2289443 : Blo 1524459 2289443 := bstep (se 1 (by rfl) ⟨1717082, by rfl⟩ : syracuseStep 2289443 = 3434165) B3434165
theorem B2289473 : Blo 1524459 2289473 := bstep (se 2 (by rfl) ⟨858552, by rfl⟩ : syracuseStep 2289473 = 1717105) B1717105
theorem B4403011 : Blo 1524459 4403011 := bstep (se 1 (by rfl) ⟨3302258, by rfl⟩ : syracuseStep 4403011 = 6604517) B6604517
theorem B2289491 : Blo 1524459 2289491 := bstep (se 1 (by rfl) ⟨1717118, by rfl⟩ : syracuseStep 2289491 = 3434237) B3434237
theorem B8925041 : Blo 1524459 8925041 := bstep (se 2 (by rfl) ⟨3346890, by rfl⟩ : syracuseStep 8925041 = 6693781) B6693781
theorem B2289521 : Blo 1524459 2289521 := bstep (se 2 (by rfl) ⟨858570, by rfl⟩ : syracuseStep 2289521 = 1717141) B1717141
theorem B2289539 : Blo 1524459 2289539 := bstep (se 1 (by rfl) ⟨1717154, by rfl⟩ : syracuseStep 2289539 = 3434309) B3434309
theorem B1716115 : Blo 1524459 1716115 := bstep (se 1 (by rfl) ⟨1287086, by rfl⟩ : syracuseStep 1716115 = 2574173) B2574173
theorem B2289569 : Blo 1524459 2289569 := bstep (se 2 (by rfl) ⟨858588, by rfl⟩ : syracuseStep 2289569 = 1717177) B1717177
theorem B2289587 : Blo 1524459 2289587 := bstep (se 1 (by rfl) ⟨1717190, by rfl⟩ : syracuseStep 2289587 = 3434381) B3434381
theorem B2289617 : Blo 1524459 2289617 := bstep (se 2 (by rfl) ⟨858606, by rfl⟩ : syracuseStep 2289617 = 1717213) B1717213
theorem B2289635 : Blo 1524459 2289635 := bstep (se 1 (by rfl) ⟨1717226, by rfl⟩ : syracuseStep 2289635 = 3434453) B3434453
theorem B2289665 : Blo 1524459 2289665 := bstep (se 2 (by rfl) ⟨858624, by rfl⟩ : syracuseStep 2289665 = 1717249) B1717249
theorem B3764227 : Blo 1524459 3764227 := bstep (se 1 (by rfl) ⟨2823170, by rfl⟩ : syracuseStep 3764227 = 5646341) B5646341
theorem B2289683 : Blo 1524459 2289683 := bstep (se 1 (by rfl) ⟨1717262, by rfl⟩ : syracuseStep 2289683 = 3434525) B3434525
theorem B2895907 : Blo 1524459 2895907 := bstep (se 1 (by rfl) ⟨2171930, by rfl⟩ : syracuseStep 2895907 = 4343861) B4343861
theorem B1716259 : Blo 1524459 1716259 := bstep (se 1 (by rfl) ⟨1287194, by rfl⟩ : syracuseStep 1716259 = 2574389) B2574389
theorem B11587697 : Blo 1524459 11587697 := bstep (se 2 (by rfl) ⟨4345386, by rfl⟩ : syracuseStep 11587697 = 8690773) B8690773
theorem B14651533 : Blo 1524459 14651533 := bstep (se 3 (by rfl) ⟨2747162, by rfl⟩ : syracuseStep 14651533 = 5494325) B5494325
theorem B5148845 : Blo 1524459 5148845 := bstep (se 3 (by rfl) ⟨965408, by rfl⟩ : syracuseStep 5148845 = 1930817) B1930817
theorem B1716403 : Blo 1524459 1716403 := bstep (se 1 (by rfl) ⟨1287302, by rfl⟩ : syracuseStep 1716403 = 2574605) B2574605
theorem B2896067 : Blo 1524459 2896067 := bstep (se 1 (by rfl) ⟨2172050, by rfl⟩ : syracuseStep 2896067 = 4344101) B4344101
theorem B5148899 : Blo 1524459 5148899 := bstep (se 1 (by rfl) ⟨3861674, by rfl⟩ : syracuseStep 5148899 = 7723349) B7723349
theorem B8687857 : Blo 1524459 8687857 := bstep (se 2 (by rfl) ⟨3257946, by rfl⟩ : syracuseStep 8687857 = 6515893) B6515893
theorem B1716547 : Blo 1524459 1716547 := bstep (se 1 (by rfl) ⟨1287410, by rfl⟩ : syracuseStep 1716547 = 2574821) B2574821
theorem B2748835 : Blo 1524459 2748835 := bstep (se 1 (by rfl) ⟨2061626, by rfl⟩ : syracuseStep 2748835 = 4123253) B4123253
theorem B3862961 : Blo 1524459 3862961 := bstep (se 2 (by rfl) ⟨1448610, by rfl⟩ : syracuseStep 3862961 = 2897221) B2897221
theorem B1929683 : Blo 1524459 1929683 := bstep (se 1 (by rfl) ⟨1447262, by rfl⟩ : syracuseStep 1929683 = 2894525) B2894525
theorem B1716691 : Blo 1524459 1716691 := bstep (se 1 (by rfl) ⟨1287518, by rfl⟩ : syracuseStep 1716691 = 2575037) B2575037
theorem B7328227 : Blo 1524459 7328227 := bstep (se 1 (by rfl) ⟨5496170, by rfl⟩ : syracuseStep 7328227 = 10992341) B10992341
theorem B3863011 : Blo 1524459 3863011 := bstep (se 1 (by rfl) ⟨2897258, by rfl⟩ : syracuseStep 3863011 = 5794517) B5794517
theorem B5149169 : Blo 1524459 5149169 := bstep (se 2 (by rfl) ⟨1930938, by rfl⟩ : syracuseStep 5149169 = 3861877) B3861877
theorem B8811013 : Blo 1524459 8811013 := bstep (se 4 (by rfl) ⟨826032, by rfl⟩ : syracuseStep 8811013 = 1652065) B1652065
theorem B4346435 : Blo 1524459 4346435 := bstep (se 1 (by rfl) ⟨3259826, by rfl⟩ : syracuseStep 4346435 = 6519653) B6519653
theorem B10998341 : Blo 1524459 10998341 := bstep (se 4 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 10998341 = 2062189) B2062189
theorem B1716835 : Blo 1524459 1716835 := bstep (se 1 (by rfl) ⟨1287626, by rfl⟩ : syracuseStep 1716835 = 2575253) B2575253
theorem B3863153 : Blo 1524459 3863153 := bstep (se 2 (by rfl) ⟨1448682, by rfl⟩ : syracuseStep 3863153 = 2897365) B2897365
theorem B8245901 : Blo 1524459 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B1716979 : Blo 1524459 1716979 := bstep (se 1 (by rfl) ⟨1287734, by rfl⟩ : syracuseStep 1716979 = 2575469) B2575469
theorem B2749297 : Blo 1524459 2749297 := bstep (se 2 (by rfl) ⟨1030986, by rfl⟩ : syracuseStep 2749297 = 2061973) B2061973
theorem B1717123 : Blo 1524459 1717123 := bstep (se 1 (by rfl) ⟨1287842, by rfl⟩ : syracuseStep 1717123 = 2575685) B2575685
theorem B4641677 : Blo 1524459 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B7721891 : Blo 1524459 7721891 := bstep (se 1 (by rfl) ⟨5791418, by rfl⟩ : syracuseStep 7721891 = 11582837) B11582837
theorem B5575601 : Blo 1524459 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B8360945 : Blo 1524459 8360945 := bstep (se 2 (by rfl) ⟨3135354, by rfl⟩ : syracuseStep 8360945 = 6270709) B6270709
theorem B5788685 : Blo 1524459 5788685 := bstep (se 3 (by rfl) ⟨1085378, by rfl⟩ : syracuseStep 5788685 = 2170757) B2170757
theorem B9769997 : Blo 1524459 9769997 := bstep (se 3 (by rfl) ⟨1831874, by rfl⟩ : syracuseStep 9769997 = 3663749) B3663749
theorem B5149709 : Blo 1524459 5149709 := bstep (se 3 (by rfl) ⟨965570, by rfl⟩ : syracuseStep 5149709 = 1931141) B1931141
theorem B1717267 : Blo 1524459 1717267 := bstep (se 1 (by rfl) ⟨1287950, by rfl⟩ : syracuseStep 1717267 = 2575901) B2575901
theorem B2061379 : Blo 1524459 2061379 := bstep (se 1 (by rfl) ⟨1546034, by rfl⟩ : syracuseStep 2061379 = 3092069) B3092069
theorem B5149763 : Blo 1524459 5149763 := bstep (se 1 (by rfl) ⟨3862322, by rfl⟩ : syracuseStep 5149763 = 7724645) B7724645
theorem B4887665 : Blo 1524459 4887665 := bstep (se 2 (by rfl) ⟨1832874, by rfl⟩ : syracuseStep 4887665 = 3665749) B3665749
theorem B1930387 : Blo 1524459 1930387 := bstep (se 1 (by rfl) ⟨1447790, by rfl⟩ : syracuseStep 1930387 = 2895581) B2895581
theorem B20092085 : Blo 1524459 20092085 := bstep (se 5 (by rfl) ⟨941816, by rfl⟩ : syracuseStep 20092085 = 1883633) B1883633
theorem B2897137 : Blo 1524459 2897137 := bstep (se 2 (by rfl) ⟨1086426, by rfl⟩ : syracuseStep 2897137 = 2172853) B2172853
theorem B1930483 : Blo 1524459 1930483 := bstep (se 1 (by rfl) ⟨1447862, by rfl⟩ : syracuseStep 1930483 = 2895725) B2895725
theorem B5150033 : Blo 1524459 5150033 := bstep (se 2 (by rfl) ⟨1931262, by rfl⟩ : syracuseStep 5150033 = 3862525) B3862525
theorem B11736433 : Blo 1524459 11736433 := bstep (se 2 (by rfl) ⟨4401162, by rfl⟩ : syracuseStep 11736433 = 8802325) B8802325
theorem B3667459 : Blo 1524459 3667459 := bstep (se 1 (by rfl) ⟨2750594, by rfl⟩ : syracuseStep 3667459 = 5501189) B5501189
theorem B8246897 : Blo 1524459 8246897 := bstep (se 2 (by rfl) ⟨3092586, by rfl⟩ : syracuseStep 8246897 = 6185173) B6185173
theorem B3913379 : Blo 1524459 3913379 := bstep (se 1 (by rfl) ⟨2935034, by rfl⟩ : syracuseStep 3913379 = 5870069) B5870069
theorem B8689315 : Blo 1524459 8689315 := bstep (se 1 (by rfl) ⟨6516986, by rfl⟩ : syracuseStep 8689315 = 13033973) B13033973
theorem B7329457 : Blo 1524459 7329457 := bstep (se 2 (by rfl) ⟨2748546, by rfl⟩ : syracuseStep 7329457 = 5497093) B5497093
theorem B7722701 : Blo 1524459 7722701 := bstep (se 3 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 7722701 = 2896013) B2896013
theorem B3430097 : Blo 1524459 3430097 := bstep (se 2 (by rfl) ⟨1286286, by rfl⟩ : syracuseStep 3430097 = 2572573) B2572573
theorem B3430115 : Blo 1524459 3430115 := bstep (se 1 (by rfl) ⟨2572586, by rfl⟩ : syracuseStep 3430115 = 5145173) B5145173
theorem B1930979 : Blo 1524459 1930979 := bstep (se 1 (by rfl) ⟨1448234, by rfl⟩ : syracuseStep 1930979 = 2896469) B2896469
theorem B4888355 : Blo 1524459 4888355 := bstep (se 1 (by rfl) ⟨3666266, by rfl⟩ : syracuseStep 4888355 = 7332533) B7332533
theorem B6518627 : Blo 1524459 6518627 := bstep (se 1 (by rfl) ⟨4888970, by rfl⟩ : syracuseStep 6518627 = 9777941) B9777941
theorem B5150573 : Blo 1524459 5150573 := bstep (se 3 (by rfl) ⟨965732, by rfl⟩ : syracuseStep 5150573 = 1931465) B1931465
theorem B2062243 : Blo 1524459 2062243 := bstep (se 1 (by rfl) ⟨1546682, by rfl⟩ : syracuseStep 2062243 = 3093365) B3093365
theorem B5150627 : Blo 1524459 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B3430385 : Blo 1524459 3430385 := bstep (se 2 (by rfl) ⟨1286394, by rfl⟩ : syracuseStep 3430385 = 2572789) B2572789
theorem B3430403 : Blo 1524459 3430403 := bstep (se 1 (by rfl) ⟨2572802, by rfl⟩ : syracuseStep 3430403 = 5145605) B5145605
theorem B5216291 : Blo 1524459 5216291 := bstep (se 1 (by rfl) ⟨3912218, by rfl⟩ : syracuseStep 5216291 = 7824437) B7824437
theorem B2062417 : Blo 1524459 2062417 := bstep (se 2 (by rfl) ⟨773406, by rfl⟩ : syracuseStep 2062417 = 1546813) B1546813
theorem B4700273 : Blo 1524459 4700273 := bstep (se 2 (by rfl) ⟨1762602, by rfl⟩ : syracuseStep 4700273 = 3525205) B3525205
theorem B8689841 : Blo 1524459 8689841 := bstep (se 2 (by rfl) ⟨3258690, by rfl⟩ : syracuseStep 8689841 = 6517381) B6517381
theorem B5150897 : Blo 1524459 5150897 := bstep (se 2 (by rfl) ⟨1931586, by rfl⟩ : syracuseStep 5150897 = 3863173) B3863173
theorem B3430673 : Blo 1524459 3430673 := bstep (se 2 (by rfl) ⟨1286502, by rfl⟩ : syracuseStep 3430673 = 2573005) B2573005
theorem B3430691 : Blo 1524459 3430691 := bstep (se 1 (by rfl) ⟨2573018, by rfl⟩ : syracuseStep 3430691 = 5146037) B5146037
theorem B8247587 : Blo 1524459 8247587 := bstep (se 1 (by rfl) ⟨6185690, by rfl⟩ : syracuseStep 8247587 = 12371381) B12371381
theorem B4405553 : Blo 1524459 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B1833283 : Blo 1524459 1833283 := bstep (se 1 (by rfl) ⟨1374962, by rfl⟩ : syracuseStep 1833283 = 2749925) B2749925
theorem B1931683 : Blo 1524459 1931683 := bstep (se 1 (by rfl) ⟨1448762, by rfl⟩ : syracuseStep 1931683 = 2897525) B2897525
theorem B1931779 : Blo 1524459 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B3430961 : Blo 1524459 3430961 := bstep (se 2 (by rfl) ⟨1286610, by rfl⟩ : syracuseStep 3430961 = 2573221) B2573221
theorem B3430979 : Blo 1524459 3430979 := bstep (se 1 (by rfl) ⟨2573234, by rfl⟩ : syracuseStep 3430979 = 5146469) B5146469
theorem B2063011 : Blo 1524459 2063011 := bstep (se 1 (by rfl) ⟨1547258, by rfl⟩ : syracuseStep 2063011 = 3094517) B3094517
theorem B1628867 : Blo 1524459 1628867 := bstep (se 1 (by rfl) ⟨1221650, by rfl⟩ : syracuseStep 1628867 = 2443301) B2443301
theorem B3259075 : Blo 1524459 3259075 := bstep (se 1 (by rfl) ⟨2444306, by rfl⟩ : syracuseStep 3259075 = 4888613) B4888613
theorem B5151437 : Blo 1524459 5151437 := bstep (se 3 (by rfl) ⟨965894, by rfl⟩ : syracuseStep 5151437 = 1931789) B1931789
theorem B5151491 : Blo 1524459 5151491 := bstep (se 1 (by rfl) ⟨3863618, by rfl⟩ : syracuseStep 5151491 = 7727237) B7727237
theorem B9272069 : Blo 1524459 9272069 := bstep (se 4 (by rfl) ⟨869256, by rfl⟩ : syracuseStep 9272069 = 1738513) B1738513
theorem B3431249 : Blo 1524459 3431249 := bstep (se 2 (by rfl) ⟨1286718, by rfl⟩ : syracuseStep 3431249 = 2573437) B2573437
theorem B3431267 : Blo 1524459 3431267 := bstep (se 1 (by rfl) ⟨2573450, by rfl⟩ : syracuseStep 3431267 = 5146901) B5146901
theorem B9780173 : Blo 1524459 9780173 := bstep (se 3 (by rfl) ⟨1833782, by rfl⟩ : syracuseStep 9780173 = 3667565) B3667565
theorem B5151761 : Blo 1524459 5151761 := bstep (se 2 (by rfl) ⟨1931910, by rfl⟩ : syracuseStep 5151761 = 3863821) B3863821
theorem B5790797 : Blo 1524459 5790797 := bstep (se 3 (by rfl) ⟨1085774, by rfl⟩ : syracuseStep 5790797 = 2171549) B2171549
theorem B3431537 : Blo 1524459 3431537 := bstep (se 2 (by rfl) ⟨1286826, by rfl⟩ : syracuseStep 3431537 = 2573653) B2573653
theorem B3431555 : Blo 1524459 3431555 := bstep (se 1 (by rfl) ⟨2573666, by rfl⟩ : syracuseStep 3431555 = 5147333) B5147333
theorem B23469365 : Blo 1524459 23469365 := bstep (se 5 (by rfl) ⟨1100126, by rfl⟩ : syracuseStep 23469365 = 2200253) B2200253
theorem B5217617 : Blo 1524459 5217617 := bstep (se 2 (by rfl) ⟨1956606, by rfl⟩ : syracuseStep 5217617 = 3913213) B3913213
theorem B3431825 : Blo 1524459 3431825 := bstep (se 2 (by rfl) ⟨1286934, by rfl⟩ : syracuseStep 3431825 = 2573869) B2573869
theorem B3431843 : Blo 1524459 3431843 := bstep (se 1 (by rfl) ⟨2573882, by rfl⟩ : syracuseStep 3431843 = 5147765) B5147765
theorem B4890125 : Blo 1524459 4890125 := bstep (se 3 (by rfl) ⟨916898, by rfl⟩ : syracuseStep 4890125 = 1833797) B1833797
theorem B3259921 : Blo 1524459 3259921 := bstep (se 2 (by rfl) ⟨1222470, by rfl⟩ : syracuseStep 3259921 = 2444941) B2444941
theorem B8691299 : Blo 1524459 8691299 := bstep (se 1 (by rfl) ⟨6518474, by rfl⟩ : syracuseStep 8691299 = 13036949) B13036949
theorem B10993265 : Blo 1524459 10993265 := bstep (se 2 (by rfl) ⟨4122474, by rfl⟩ : syracuseStep 10993265 = 8244949) B8244949
theorem B1629811 : Blo 1524459 1629811 := bstep (se 1 (by rfl) ⟨1222358, by rfl⟩ : syracuseStep 1629811 = 2444717) B2444717
theorem B27836045 : Blo 1524459 27836045 := bstep (se 3 (by rfl) ⟨5219258, by rfl⟩ : syracuseStep 27836045 = 10438517) B10438517
theorem B3432113 : Blo 1524459 3432113 := bstep (se 2 (by rfl) ⟨1287042, by rfl⟩ : syracuseStep 3432113 = 2574085) B2574085
theorem B3432131 : Blo 1524459 3432131 := bstep (se 1 (by rfl) ⟨2574098, by rfl⟩ : syracuseStep 3432131 = 5148197) B5148197
theorem B19816163 : Blo 1524459 19816163 := bstep (se 1 (by rfl) ⟨14862122, by rfl⟩ : syracuseStep 19816163 = 29724245) B29724245
theorem B32997091 : Blo 1524459 32997091 := bstep (se 1 (by rfl) ⟨24747818, by rfl⟩ : syracuseStep 32997091 = 49495637) B49495637
theorem B1957603 : Blo 1524459 1957603 := bstep (se 1 (by rfl) ⟨1468202, by rfl⟩ : syracuseStep 1957603 = 2936405) B2936405
theorem B2170643 : Blo 1524459 2170643 := bstep (se 1 (by rfl) ⟨1627982, by rfl⟩ : syracuseStep 2170643 = 3255965) B3255965
theorem B5791601 : Blo 1524459 5791601 := bstep (se 2 (by rfl) ⟨2171850, by rfl⟩ : syracuseStep 5791601 = 4343701) B4343701
theorem B3432401 : Blo 1524459 3432401 := bstep (se 2 (by rfl) ⟨1287150, by rfl⟩ : syracuseStep 3432401 = 2574301) B2574301
theorem B22896611 : Blo 1524459 22896611 := bstep (se 1 (by rfl) ⟨17172458, by rfl⟩ : syracuseStep 22896611 = 34344917) B34344917
theorem B3432419 : Blo 1524459 3432419 := bstep (se 1 (by rfl) ⟨2574314, by rfl⟩ : syracuseStep 3432419 = 5148629) B5148629
theorem B23486435 : Blo 1524459 23486435 := bstep (se 1 (by rfl) ⟨17614826, by rfl⟩ : syracuseStep 23486435 = 35229653) B35229653
theorem B3432473 : Blo 1524459 3432473 := bstep (se 2 (by rfl) ⟨1287177, by rfl⟩ : syracuseStep 3432473 = 2574355) B2574355
theorem B7725131 : Blo 1524459 7725131 := bstep (se 1 (by rfl) ⟨5793848, by rfl⟩ : syracuseStep 7725131 = 11587697) B11587697
theorem B3432563 : Blo 1524459 3432563 := bstep (se 1 (by rfl) ⟨2574422, by rfl⟩ : syracuseStep 3432563 = 5148845) B5148845
theorem B3432599 : Blo 1524459 3432599 := bstep (se 1 (by rfl) ⟨2574449, by rfl⟩ : syracuseStep 3432599 = 5148899) B5148899
theorem B11583809 : Blo 1524459 11583809 := bstep (se 2 (by rfl) ⟨4343928, by rfl⟩ : syracuseStep 11583809 = 8687857) B8687857
theorem B3432779 : Blo 1524459 3432779 := bstep (se 1 (by rfl) ⟨2574584, by rfl⟩ : syracuseStep 3432779 = 5149169) B5149169
theorem B3432833 : Blo 1524459 3432833 := bstep (se 2 (by rfl) ⟨1287312, by rfl⟩ : syracuseStep 3432833 = 2574625) B2574625
theorem B7332227 : Blo 1524459 7332227 := bstep (se 1 (by rfl) ⟨5499170, by rfl⟩ : syracuseStep 7332227 = 10998341) B10998341
theorem B2351513 : Blo 1524459 2351513 := bstep (se 2 (by rfl) ⟨881817, by rfl⟩ : syracuseStep 2351513 = 1763635) B1763635
theorem B2572823 : Blo 1524459 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B3433049 : Blo 1524459 3433049 := bstep (se 2 (by rfl) ⟨1287393, by rfl⟩ : syracuseStep 3433049 = 2574787) B2574787
theorem B2572951 : Blo 1524459 2572951 := bstep (se 1 (by rfl) ⟨1929713, by rfl⟩ : syracuseStep 2572951 = 3859427) B3859427
theorem B11748017 : Blo 1524459 11748017 := bstep (se 2 (by rfl) ⟨4405506, by rfl⟩ : syracuseStep 11748017 = 8811013) B8811013
theorem B3859123 : Blo 1524459 3859123 := bstep (se 1 (by rfl) ⟨2894342, by rfl⟩ : syracuseStep 3859123 = 5788685) B5788685
theorem B6513331 : Blo 1524459 6513331 := bstep (se 1 (by rfl) ⟨4884998, by rfl⟩ : syracuseStep 6513331 = 9769997) B9769997
theorem B3433139 : Blo 1524459 3433139 := bstep (se 1 (by rfl) ⟨2574854, by rfl⟩ : syracuseStep 3433139 = 5149709) B5149709
theorem B5145281 : Blo 1524459 5145281 := bstep (se 2 (by rfl) ⟨1929480, by rfl⟩ : syracuseStep 5145281 = 3858961) B3858961
theorem B3433175 : Blo 1524459 3433175 := bstep (se 1 (by rfl) ⟨2574881, by rfl⟩ : syracuseStep 3433175 = 5149763) B5149763
theorem B1524459 : Blo 1524459 1524459 := bstep (se 1 (by rfl) ⟨1143344, by rfl⟩ : syracuseStep 1524459 = 2286689) B2286689
theorem B1524471 : Blo 1524459 1524471 := bstep (se 1 (by rfl) ⟨1143353, by rfl⟩ : syracuseStep 1524471 = 2286707) B2286707
theorem B1524491 : Blo 1524459 1524491 := bstep (se 1 (by rfl) ⟨1143368, by rfl⟩ : syracuseStep 1524491 = 2286737) B2286737
theorem B1524503 : Blo 1524459 1524503 := bstep (se 1 (by rfl) ⟨1143377, by rfl⟩ : syracuseStep 1524503 = 2286755) B2286755
theorem B13394723 : Blo 1524459 13394723 := bstep (se 1 (by rfl) ⟨10046042, by rfl⟩ : syracuseStep 13394723 = 20092085) B20092085
theorem B1524523 : Blo 1524459 1524523 := bstep (se 1 (by rfl) ⟨1143392, by rfl⟩ : syracuseStep 1524523 = 2286785) B2286785
theorem B1524535 : Blo 1524459 1524535 := bstep (se 1 (by rfl) ⟨1143401, by rfl⟩ : syracuseStep 1524535 = 2286803) B2286803
theorem B3859265 : Blo 1524459 3859265 := bstep (se 2 (by rfl) ⟨1447224, by rfl⟩ : syracuseStep 3859265 = 2894449) B2894449
theorem B1524555 : Blo 1524459 1524555 := bstep (se 1 (by rfl) ⟨1143416, by rfl⟩ : syracuseStep 1524555 = 2286833) B2286833
theorem B1524567 : Blo 1524459 1524567 := bstep (se 1 (by rfl) ⟨1143425, by rfl⟩ : syracuseStep 1524567 = 2286851) B2286851
theorem B2442071 : Blo 1524459 2442071 := bstep (se 1 (by rfl) ⟨1831553, by rfl⟩ : syracuseStep 2442071 = 3663107) B3663107
theorem B1524587 : Blo 1524459 1524587 := bstep (se 1 (by rfl) ⟨1143440, by rfl⟩ : syracuseStep 1524587 = 2286881) B2286881
theorem B1524599 : Blo 1524459 1524599 := bstep (se 1 (by rfl) ⟨1143449, by rfl⟩ : syracuseStep 1524599 = 2286899) B2286899
theorem B1524619 : Blo 1524459 1524619 := bstep (se 1 (by rfl) ⟨1143464, by rfl⟩ : syracuseStep 1524619 = 2286929) B2286929
theorem B3433355 : Blo 1524459 3433355 := bstep (se 1 (by rfl) ⟨2575016, by rfl⟩ : syracuseStep 3433355 = 5150033) B5150033
theorem B1524631 : Blo 1524459 1524631 := bstep (se 1 (by rfl) ⟨1143473, by rfl⟩ : syracuseStep 1524631 = 2286947) B2286947
theorem B1524651 : Blo 1524459 1524651 := bstep (se 1 (by rfl) ⟨1143488, by rfl⟩ : syracuseStep 1524651 = 2286977) B2286977
theorem B1524663 : Blo 1524459 1524663 := bstep (se 1 (by rfl) ⟨1143497, by rfl⟩ : syracuseStep 1524663 = 2286995) B2286995
theorem B3433409 : Blo 1524459 3433409 := bstep (se 2 (by rfl) ⟨1287528, by rfl⟩ : syracuseStep 3433409 = 2575057) B2575057
theorem B1524683 : Blo 1524459 1524683 := bstep (se 1 (by rfl) ⟨1143512, by rfl⟩ : syracuseStep 1524683 = 2287025) B2287025
theorem B1524695 : Blo 1524459 1524695 := bstep (se 1 (by rfl) ⟨1143521, by rfl⟩ : syracuseStep 1524695 = 2287043) B2287043
theorem B1524715 : Blo 1524459 1524715 := bstep (se 1 (by rfl) ⟨1143536, by rfl⟩ : syracuseStep 1524715 = 2287073) B2287073
theorem B1524727 : Blo 1524459 1524727 := bstep (se 1 (by rfl) ⟨1143545, by rfl⟩ : syracuseStep 1524727 = 2287091) B2287091
theorem B1524747 : Blo 1524459 1524747 := bstep (se 1 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 1524747 = 2287121) B2287121
theorem B1524759 : Blo 1524459 1524759 := bstep (se 1 (by rfl) ⟨1143569, by rfl⟩ : syracuseStep 1524759 = 2287139) B2287139
theorem B1524779 : Blo 1524459 1524779 := bstep (se 1 (by rfl) ⟨1143584, by rfl⟩ : syracuseStep 1524779 = 2287169) B2287169
theorem B4342835 : Blo 1524459 4342835 := bstep (se 1 (by rfl) ⟨3257126, by rfl⟩ : syracuseStep 4342835 = 6514253) B6514253
theorem B1524791 : Blo 1524459 1524791 := bstep (se 1 (by rfl) ⟨1143593, by rfl⟩ : syracuseStep 1524791 = 2287187) B2287187
theorem B1524811 : Blo 1524459 1524811 := bstep (se 1 (by rfl) ⟨1143608, by rfl⟩ : syracuseStep 1524811 = 2287217) B2287217
theorem B4342859 : Blo 1524459 4342859 := bstep (se 1 (by rfl) ⟨3257144, by rfl⟩ : syracuseStep 4342859 = 6514289) B6514289
theorem B5497931 : Blo 1524459 5497931 := bstep (se 1 (by rfl) ⟨4123448, by rfl⟩ : syracuseStep 5497931 = 8246897) B8246897
theorem B1524823 : Blo 1524459 1524823 := bstep (se 1 (by rfl) ⟨1143617, by rfl⟩ : syracuseStep 1524823 = 2287235) B2287235
theorem B1524843 : Blo 1524459 1524843 := bstep (se 1 (by rfl) ⟨1143632, by rfl⟩ : syracuseStep 1524843 = 2287265) B2287265
theorem B1524855 : Blo 1524459 1524855 := bstep (se 1 (by rfl) ⟨1143641, by rfl⟩ : syracuseStep 1524855 = 2287283) B2287283
theorem B2286731 : Blo 1524459 2286731 := bstep (se 1 (by rfl) ⟨1715048, by rfl⟩ : syracuseStep 2286731 = 3430097) B3430097
theorem B1524875 : Blo 1524459 1524875 := bstep (se 1 (by rfl) ⟨1143656, by rfl⟩ : syracuseStep 1524875 = 2287313) B2287313
theorem B2286743 : Blo 1524459 2286743 := bstep (se 1 (by rfl) ⟨1715057, by rfl⟩ : syracuseStep 2286743 = 3430115) B3430115
theorem B1524887 : Blo 1524459 1524887 := bstep (se 1 (by rfl) ⟨1143665, by rfl⟩ : syracuseStep 1524887 = 2287331) B2287331
theorem B3433625 : Blo 1524459 3433625 := bstep (se 2 (by rfl) ⟨1287609, by rfl⟩ : syracuseStep 3433625 = 2575219) B2575219
theorem B1524907 : Blo 1524459 1524907 := bstep (se 1 (by rfl) ⟨1143680, by rfl⟩ : syracuseStep 1524907 = 2287361) B2287361
theorem B50136245 : Blo 1524459 50136245 := bstep (se 5 (by rfl) ⟨2350136, by rfl⟩ : syracuseStep 50136245 = 4700273) B4700273
theorem B1524919 : Blo 1524459 1524919 := bstep (se 1 (by rfl) ⟨1143689, by rfl⟩ : syracuseStep 1524919 = 2287379) B2287379
theorem B1524939 : Blo 1524459 1524939 := bstep (se 1 (by rfl) ⟨1143704, by rfl⟩ : syracuseStep 1524939 = 2287409) B2287409
theorem B1524951 : Blo 1524459 1524951 := bstep (se 1 (by rfl) ⟨1143713, by rfl⟩ : syracuseStep 1524951 = 2287427) B2287427
theorem B2286809 : Blo 1524459 2286809 := bstep (se 2 (by rfl) ⟨857553, by rfl⟩ : syracuseStep 2286809 = 1715107) B1715107
theorem B5145821 : Blo 1524459 5145821 := bstep (se 3 (by rfl) ⟨964841, by rfl⟩ : syracuseStep 5145821 = 1929683) B1929683
theorem B1524971 : Blo 1524459 1524971 := bstep (se 1 (by rfl) ⟨1143728, by rfl⟩ : syracuseStep 1524971 = 2287457) B2287457
theorem B3433715 : Blo 1524459 3433715 := bstep (se 1 (by rfl) ⟨2575286, by rfl⟩ : syracuseStep 3433715 = 5150573) B5150573
theorem B1524983 : Blo 1524459 1524983 := bstep (se 1 (by rfl) ⟨1143737, by rfl⟩ : syracuseStep 1524983 = 2287475) B2287475
theorem B1525003 : Blo 1524459 1525003 := bstep (se 1 (by rfl) ⟨1143752, by rfl⟩ : syracuseStep 1525003 = 2287505) B2287505
theorem B2573579 : Blo 1524459 2573579 := bstep (se 1 (by rfl) ⟨1930184, by rfl⟩ : syracuseStep 2573579 = 3860369) B3860369
theorem B1525015 : Blo 1524459 1525015 := bstep (se 1 (by rfl) ⟨1143761, by rfl⟩ : syracuseStep 1525015 = 2287523) B2287523
theorem B3433751 : Blo 1524459 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B1525035 : Blo 1524459 1525035 := bstep (se 1 (by rfl) ⟨1143776, by rfl⟩ : syracuseStep 1525035 = 2287553) B2287553
theorem B6513965 : Blo 1524459 6513965 := bstep (se 3 (by rfl) ⟨1221368, by rfl⟩ : syracuseStep 6513965 = 2442737) B2442737
theorem B1525047 : Blo 1524459 1525047 := bstep (se 1 (by rfl) ⟨1143785, by rfl⟩ : syracuseStep 1525047 = 2287571) B2287571
theorem B2286923 : Blo 1524459 2286923 := bstep (se 1 (by rfl) ⟨1715192, by rfl⟩ : syracuseStep 2286923 = 3430385) B3430385
theorem B1525067 : Blo 1524459 1525067 := bstep (se 1 (by rfl) ⟨1143800, by rfl⟩ : syracuseStep 1525067 = 2287601) B2287601
theorem B2286935 : Blo 1524459 2286935 := bstep (se 1 (by rfl) ⟨1715201, by rfl⟩ : syracuseStep 2286935 = 3430403) B3430403
theorem B2442583 : Blo 1524459 2442583 := bstep (se 1 (by rfl) ⟨1831937, by rfl⟩ : syracuseStep 2442583 = 3663875) B3663875
theorem B1525079 : Blo 1524459 1525079 := bstep (se 1 (by rfl) ⟨1143809, by rfl⟩ : syracuseStep 1525079 = 2287619) B2287619
theorem B1525099 : Blo 1524459 1525099 := bstep (se 1 (by rfl) ⟨1143824, by rfl⟩ : syracuseStep 1525099 = 2287649) B2287649
theorem B1525111 : Blo 1524459 1525111 := bstep (se 1 (by rfl) ⟨1143833, by rfl⟩ : syracuseStep 1525111 = 2287667) B2287667
theorem B1525131 : Blo 1524459 1525131 := bstep (se 1 (by rfl) ⟨1143848, by rfl⟩ : syracuseStep 1525131 = 2287697) B2287697
theorem B2573707 : Blo 1524459 2573707 := bstep (se 1 (by rfl) ⟨1930280, by rfl⟩ : syracuseStep 2573707 = 3860561) B3860561
theorem B1525143 : Blo 1524459 1525143 := bstep (se 1 (by rfl) ⟨1143857, by rfl⟩ : syracuseStep 1525143 = 2287715) B2287715
theorem B2287001 : Blo 1524459 2287001 := bstep (se 2 (by rfl) ⟨857625, by rfl⟩ : syracuseStep 2287001 = 1715251) B1715251
theorem B1525163 : Blo 1524459 1525163 := bstep (se 1 (by rfl) ⟨1143872, by rfl⟩ : syracuseStep 1525163 = 2287745) B2287745
theorem B1525175 : Blo 1524459 1525175 := bstep (se 1 (by rfl) ⟨1143881, by rfl⟩ : syracuseStep 1525175 = 2287763) B2287763
theorem B1525195 : Blo 1524459 1525195 := bstep (se 1 (by rfl) ⟨1143896, by rfl⟩ : syracuseStep 1525195 = 2287793) B2287793
theorem B5793227 : Blo 1524459 5793227 := bstep (se 1 (by rfl) ⟨4344920, by rfl⟩ : syracuseStep 5793227 = 8689841) B8689841
theorem B3433931 : Blo 1524459 3433931 := bstep (se 1 (by rfl) ⟨2575448, by rfl⟩ : syracuseStep 3433931 = 5150897) B5150897
theorem B1525207 : Blo 1524459 1525207 := bstep (se 1 (by rfl) ⟨1143905, by rfl⟩ : syracuseStep 1525207 = 2287811) B2287811
theorem B5793241 : Blo 1524459 5793241 := bstep (se 2 (by rfl) ⟨2172465, by rfl⟩ : syracuseStep 5793241 = 4344931) B4344931
theorem B1525227 : Blo 1524459 1525227 := bstep (se 1 (by rfl) ⟨1143920, by rfl⟩ : syracuseStep 1525227 = 2287841) B2287841
theorem B1525239 : Blo 1524459 1525239 := bstep (se 1 (by rfl) ⟨1143929, by rfl⟩ : syracuseStep 1525239 = 2287859) B2287859
theorem B3433985 : Blo 1524459 3433985 := bstep (se 2 (by rfl) ⟨1287744, by rfl⟩ : syracuseStep 3433985 = 2575489) B2575489
theorem B2287115 : Blo 1524459 2287115 := bstep (se 1 (by rfl) ⟨1715336, by rfl⟩ : syracuseStep 2287115 = 3430673) B3430673
theorem B1525259 : Blo 1524459 1525259 := bstep (se 1 (by rfl) ⟨1143944, by rfl⟩ : syracuseStep 1525259 = 2287889) B2287889
theorem B2287127 : Blo 1524459 2287127 := bstep (se 1 (by rfl) ⟨1715345, by rfl⟩ : syracuseStep 2287127 = 3430691) B3430691
theorem B1525271 : Blo 1524459 1525271 := bstep (se 1 (by rfl) ⟨1143953, by rfl⟩ : syracuseStep 1525271 = 2287907) B2287907
theorem B2573849 : Blo 1524459 2573849 := bstep (se 2 (by rfl) ⟨965193, by rfl⟩ : syracuseStep 2573849 = 1930387) B1930387
theorem B1525291 : Blo 1524459 1525291 := bstep (se 1 (by rfl) ⟨1143968, by rfl⟩ : syracuseStep 1525291 = 2287937) B2287937
theorem B1525303 : Blo 1524459 1525303 := bstep (se 1 (by rfl) ⟨1143977, by rfl⟩ : syracuseStep 1525303 = 2287955) B2287955
theorem B1525323 : Blo 1524459 1525323 := bstep (se 1 (by rfl) ⟨1143992, by rfl⟩ : syracuseStep 1525323 = 2287985) B2287985
theorem B1525335 : Blo 1524459 1525335 := bstep (se 1 (by rfl) ⟨1144001, by rfl⟩ : syracuseStep 1525335 = 2288003) B2288003
theorem B2287193 : Blo 1524459 2287193 := bstep (se 2 (by rfl) ⟨857697, by rfl⟩ : syracuseStep 2287193 = 1715395) B1715395
theorem B1525355 : Blo 1524459 1525355 := bstep (se 1 (by rfl) ⟨1144016, by rfl⟩ : syracuseStep 1525355 = 2288033) B2288033
theorem B1525367 : Blo 1524459 1525367 := bstep (se 1 (by rfl) ⟨1144025, by rfl⟩ : syracuseStep 1525367 = 2288051) B2288051
theorem B1525387 : Blo 1524459 1525387 := bstep (se 1 (by rfl) ⟨1144040, by rfl⟩ : syracuseStep 1525387 = 2288081) B2288081
theorem B1525399 : Blo 1524459 1525399 := bstep (se 1 (by rfl) ⟨1144049, by rfl⟩ : syracuseStep 1525399 = 2288099) B2288099
theorem B2573977 : Blo 1524459 2573977 := bstep (se 2 (by rfl) ⟨965241, by rfl⟩ : syracuseStep 2573977 = 1930483) B1930483
theorem B1525419 : Blo 1524459 1525419 := bstep (se 1 (by rfl) ⟨1144064, by rfl⟩ : syracuseStep 1525419 = 2288129) B2288129
theorem B1525431 : Blo 1524459 1525431 := bstep (se 1 (by rfl) ⟨1144073, by rfl⟩ : syracuseStep 1525431 = 2288147) B2288147
theorem B2287307 : Blo 1524459 2287307 := bstep (se 1 (by rfl) ⟨1715480, by rfl⟩ : syracuseStep 2287307 = 3430961) B3430961
theorem B1525451 : Blo 1524459 1525451 := bstep (se 1 (by rfl) ⟨1144088, by rfl⟩ : syracuseStep 1525451 = 2288177) B2288177
theorem B21989069 : Blo 1524459 21989069 := bstep (se 3 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 21989069 = 8245901) B8245901
theorem B2287319 : Blo 1524459 2287319 := bstep (se 1 (by rfl) ⟨1715489, by rfl⟩ : syracuseStep 2287319 = 3430979) B3430979
theorem B1525463 : Blo 1524459 1525463 := bstep (se 1 (by rfl) ⟨1144097, by rfl⟩ : syracuseStep 1525463 = 2288195) B2288195
theorem B3434201 : Blo 1524459 3434201 := bstep (se 2 (by rfl) ⟨1287825, by rfl⟩ : syracuseStep 3434201 = 2575651) B2575651
theorem B1525483 : Blo 1524459 1525483 := bstep (se 1 (by rfl) ⟨1144112, by rfl⟩ : syracuseStep 1525483 = 2288225) B2288225
theorem B1525495 : Blo 1524459 1525495 := bstep (se 1 (by rfl) ⟨1144121, by rfl⟩ : syracuseStep 1525495 = 2288243) B2288243
theorem B1525515 : Blo 1524459 1525515 := bstep (se 1 (by rfl) ⟨1144136, by rfl⟩ : syracuseStep 1525515 = 2288273) B2288273
theorem B7333649 : Blo 1524459 7333649 := bstep (se 2 (by rfl) ⟨2750118, by rfl⟩ : syracuseStep 7333649 = 5500237) B5500237
theorem B1525527 : Blo 1524459 1525527 := bstep (se 1 (by rfl) ⟨1144145, by rfl⟩ : syracuseStep 1525527 = 2288291) B2288291
theorem B2287385 : Blo 1524459 2287385 := bstep (se 2 (by rfl) ⟨857769, by rfl⟩ : syracuseStep 2287385 = 1715539) B1715539
theorem B1525547 : Blo 1524459 1525547 := bstep (se 1 (by rfl) ⟨1144160, by rfl⟩ : syracuseStep 1525547 = 2288321) B2288321
theorem B3434291 : Blo 1524459 3434291 := bstep (se 1 (by rfl) ⟨2575718, by rfl⟩ : syracuseStep 3434291 = 5151437) B5151437
theorem B1525559 : Blo 1524459 1525559 := bstep (se 1 (by rfl) ⟨1144169, by rfl⟩ : syracuseStep 1525559 = 2288339) B2288339
theorem B7726913 : Blo 1524459 7726913 := bstep (se 2 (by rfl) ⟨2897592, by rfl⟩ : syracuseStep 7726913 = 5795185) B5795185
theorem B1525579 : Blo 1524459 1525579 := bstep (se 1 (by rfl) ⟨1144184, by rfl⟩ : syracuseStep 1525579 = 2288369) B2288369
theorem B1525591 : Blo 1524459 1525591 := bstep (se 1 (by rfl) ⟨1144193, by rfl⟩ : syracuseStep 1525591 = 2288387) B2288387
theorem B3434327 : Blo 1524459 3434327 := bstep (se 1 (by rfl) ⟨2575745, by rfl⟩ : syracuseStep 3434327 = 5151491) B5151491
theorem B4343645 : Blo 1524459 4343645 := bstep (se 3 (by rfl) ⟨814433, by rfl⟩ : syracuseStep 4343645 = 1628867) B1628867
theorem B1525611 : Blo 1524459 1525611 := bstep (se 1 (by rfl) ⟨1144208, by rfl⟩ : syracuseStep 1525611 = 2288417) B2288417
theorem B1525623 : Blo 1524459 1525623 := bstep (se 1 (by rfl) ⟨1144217, by rfl⟩ : syracuseStep 1525623 = 2288435) B2288435
theorem B2287499 : Blo 1524459 2287499 := bstep (se 1 (by rfl) ⟨1715624, by rfl⟩ : syracuseStep 2287499 = 3431249) B3431249
theorem B1525643 : Blo 1524459 1525643 := bstep (se 1 (by rfl) ⟨1144232, by rfl⟩ : syracuseStep 1525643 = 2288465) B2288465
theorem B2287511 : Blo 1524459 2287511 := bstep (se 1 (by rfl) ⟨1715633, by rfl⟩ : syracuseStep 2287511 = 3431267) B3431267
theorem B1525655 : Blo 1524459 1525655 := bstep (se 1 (by rfl) ⟨1144241, by rfl⟩ : syracuseStep 1525655 = 2288483) B2288483
theorem B1525675 : Blo 1524459 1525675 := bstep (se 1 (by rfl) ⟨1144256, by rfl⟩ : syracuseStep 1525675 = 2288513) B2288513
theorem B6031277 : Blo 1524459 6031277 := bstep (se 3 (by rfl) ⟨1130864, by rfl⟩ : syracuseStep 6031277 = 2261729) B2261729
theorem B1525687 : Blo 1524459 1525687 := bstep (se 1 (by rfl) ⟨1144265, by rfl⟩ : syracuseStep 1525687 = 2288531) B2288531
theorem B1525707 : Blo 1524459 1525707 := bstep (se 1 (by rfl) ⟨1144280, by rfl⟩ : syracuseStep 1525707 = 2288561) B2288561
theorem B1525719 : Blo 1524459 1525719 := bstep (se 1 (by rfl) ⟨1144289, by rfl⟩ : syracuseStep 1525719 = 2288579) B2288579
theorem B2287577 : Blo 1524459 2287577 := bstep (se 2 (by rfl) ⟨857841, by rfl⟩ : syracuseStep 2287577 = 1715683) B1715683
theorem B1525739 : Blo 1524459 1525739 := bstep (se 1 (by rfl) ⟨1144304, by rfl⟩ : syracuseStep 1525739 = 2288609) B2288609
theorem B1525751 : Blo 1524459 1525751 := bstep (se 1 (by rfl) ⟨1144313, by rfl⟩ : syracuseStep 1525751 = 2288627) B2288627
theorem B1525771 : Blo 1524459 1525771 := bstep (se 1 (by rfl) ⟨1144328, by rfl⟩ : syracuseStep 1525771 = 2288657) B2288657
theorem B3434507 : Blo 1524459 3434507 := bstep (se 1 (by rfl) ⟨2575880, by rfl⟩ : syracuseStep 3434507 = 5151761) B5151761
theorem B1525783 : Blo 1524459 1525783 := bstep (se 1 (by rfl) ⟨1144337, by rfl⟩ : syracuseStep 1525783 = 2288675) B2288675
theorem B1525803 : Blo 1524459 1525803 := bstep (se 1 (by rfl) ⟨1144352, by rfl⟩ : syracuseStep 1525803 = 2288705) B2288705
theorem B3860531 : Blo 1524459 3860531 := bstep (se 1 (by rfl) ⟨2895398, by rfl⟩ : syracuseStep 3860531 = 5790797) B5790797
theorem B1525815 : Blo 1524459 1525815 := bstep (se 1 (by rfl) ⟨1144361, by rfl⟩ : syracuseStep 1525815 = 2288723) B2288723
theorem B9406529 : Blo 1524459 9406529 := bstep (se 2 (by rfl) ⟨3527448, by rfl⟩ : syracuseStep 9406529 = 7054897) B7054897
theorem B2287691 : Blo 1524459 2287691 := bstep (se 1 (by rfl) ⟨1715768, by rfl⟩ : syracuseStep 2287691 = 3431537) B3431537
theorem B31311947 : Blo 1524459 31311947 := bstep (se 1 (by rfl) ⟨23483960, by rfl⟩ : syracuseStep 31311947 = 46967921) B46967921
theorem B1525835 : Blo 1524459 1525835 := bstep (se 1 (by rfl) ⟨1144376, by rfl⟩ : syracuseStep 1525835 = 2288753) B2288753
theorem B2287703 : Blo 1524459 2287703 := bstep (se 1 (by rfl) ⟨1715777, by rfl⟩ : syracuseStep 2287703 = 3431555) B3431555
theorem B1525847 : Blo 1524459 1525847 := bstep (se 1 (by rfl) ⟨1144385, by rfl⟩ : syracuseStep 1525847 = 2288771) B2288771
theorem B13035613 : Blo 1524459 13035613 := bstep (se 3 (by rfl) ⟨2444177, by rfl⟩ : syracuseStep 13035613 = 4888355) B4888355
theorem B1525867 : Blo 1524459 1525867 := bstep (se 1 (by rfl) ⟨1144400, by rfl⟩ : syracuseStep 1525867 = 2288801) B2288801
theorem B1525879 : Blo 1524459 1525879 := bstep (se 1 (by rfl) ⟨1144409, by rfl⟩ : syracuseStep 1525879 = 2288819) B2288819
theorem B2443403 : Blo 1524459 2443403 := bstep (se 1 (by rfl) ⟨1832552, by rfl⟩ : syracuseStep 2443403 = 3665105) B3665105
theorem B1525899 : Blo 1524459 1525899 := bstep (se 1 (by rfl) ⟨1144424, by rfl⟩ : syracuseStep 1525899 = 2288849) B2288849
theorem B1525911 : Blo 1524459 1525911 := bstep (se 1 (by rfl) ⟨1144433, by rfl⟩ : syracuseStep 1525911 = 2288867) B2288867
theorem B2287769 : Blo 1524459 2287769 := bstep (se 2 (by rfl) ⟨857913, by rfl⟩ : syracuseStep 2287769 = 1715827) B1715827
theorem B2173081 : Blo 1524459 2173081 := bstep (se 2 (by rfl) ⟨814905, by rfl⟩ : syracuseStep 2173081 = 1629811) B1629811
theorem B1525931 : Blo 1524459 1525931 := bstep (se 1 (by rfl) ⟨1144448, by rfl⟩ : syracuseStep 1525931 = 2288897) B2288897
theorem B1525943 : Blo 1524459 1525943 := bstep (se 1 (by rfl) ⟨1144457, by rfl⟩ : syracuseStep 1525943 = 2288915) B2288915
theorem B1525963 : Blo 1524459 1525963 := bstep (se 1 (by rfl) ⟨1144472, by rfl⟩ : syracuseStep 1525963 = 2288945) B2288945
theorem B2574551 : Blo 1524459 2574551 := bstep (se 1 (by rfl) ⟨1930913, by rfl⟩ : syracuseStep 2574551 = 3861827) B3861827
theorem B1525975 : Blo 1524459 1525975 := bstep (se 1 (by rfl) ⟨1144481, by rfl⟩ : syracuseStep 1525975 = 2288963) B2288963
theorem B11585753 : Blo 1524459 11585753 := bstep (se 2 (by rfl) ⟨4344657, by rfl⟩ : syracuseStep 11585753 = 8689315) B8689315
theorem B1525995 : Blo 1524459 1525995 := bstep (se 1 (by rfl) ⟨1144496, by rfl⟩ : syracuseStep 1525995 = 2288993) B2288993
theorem B1526007 : Blo 1524459 1526007 := bstep (se 1 (by rfl) ⟨1144505, by rfl⟩ : syracuseStep 1526007 = 2289011) B2289011
theorem B2287883 : Blo 1524459 2287883 := bstep (se 1 (by rfl) ⟨1715912, by rfl⟩ : syracuseStep 2287883 = 3431825) B3431825
theorem B1526027 : Blo 1524459 1526027 := bstep (se 1 (by rfl) ⟨1144520, by rfl⟩ : syracuseStep 1526027 = 2289041) B2289041
theorem B2287895 : Blo 1524459 2287895 := bstep (se 1 (by rfl) ⟨1715921, by rfl⟩ : syracuseStep 2287895 = 3431843) B3431843
theorem B1526039 : Blo 1524459 1526039 := bstep (se 1 (by rfl) ⟨1144529, by rfl⟩ : syracuseStep 1526039 = 2289059) B2289059
theorem B1526059 : Blo 1524459 1526059 := bstep (se 1 (by rfl) ⟨1144544, by rfl⟩ : syracuseStep 1526059 = 2289089) B2289089
theorem B1526071 : Blo 1524459 1526071 := bstep (se 1 (by rfl) ⟨1144553, by rfl⟩ : syracuseStep 1526071 = 2289107) B2289107
theorem B5146955 : Blo 1524459 5146955 := bstep (se 1 (by rfl) ⟨3860216, by rfl⟩ : syracuseStep 5146955 = 7720433) B7720433
theorem B8685899 : Blo 1524459 8685899 := bstep (se 1 (by rfl) ⟨6514424, by rfl⟩ : syracuseStep 8685899 = 13028849) B13028849
theorem B1526091 : Blo 1524459 1526091 := bstep (se 1 (by rfl) ⟨1144568, by rfl⟩ : syracuseStep 1526091 = 2289137) B2289137
theorem B2574679 : Blo 1524459 2574679 := bstep (se 1 (by rfl) ⟨1931009, by rfl⟩ : syracuseStep 2574679 = 3862019) B3862019
theorem B1526103 : Blo 1524459 1526103 := bstep (se 1 (by rfl) ⟨1144577, by rfl⟩ : syracuseStep 1526103 = 2289155) B2289155
theorem B2287961 : Blo 1524459 2287961 := bstep (se 2 (by rfl) ⟨857985, by rfl⟩ : syracuseStep 2287961 = 1715971) B1715971
theorem B1526123 : Blo 1524459 1526123 := bstep (se 1 (by rfl) ⟨1144592, by rfl⟩ : syracuseStep 1526123 = 2289185) B2289185
theorem B1526135 : Blo 1524459 1526135 := bstep (se 1 (by rfl) ⟨1144601, by rfl⟩ : syracuseStep 1526135 = 2289203) B2289203
theorem B7719299 : Blo 1524459 7719299 := bstep (se 1 (by rfl) ⟨5789474, by rfl⟩ : syracuseStep 7719299 = 11578949) B11578949
theorem B1526155 : Blo 1524459 1526155 := bstep (se 1 (by rfl) ⟨1144616, by rfl⟩ : syracuseStep 1526155 = 2289233) B2289233
theorem B5794199 : Blo 1524459 5794199 := bstep (se 1 (by rfl) ⟨4345649, by rfl⟩ : syracuseStep 5794199 = 8691299) B8691299
theorem B1526167 : Blo 1524459 1526167 := bstep (se 1 (by rfl) ⟨1144625, by rfl⟩ : syracuseStep 1526167 = 2289251) B2289251
theorem B1526187 : Blo 1524459 1526187 := bstep (se 1 (by rfl) ⟨1144640, by rfl⟩ : syracuseStep 1526187 = 2289281) B2289281
theorem B18557363 : Blo 1524459 18557363 := bstep (se 1 (by rfl) ⟨13918022, by rfl⟩ : syracuseStep 18557363 = 27836045) B27836045
theorem B1526199 : Blo 1524459 1526199 := bstep (se 1 (by rfl) ⟨1144649, by rfl⟩ : syracuseStep 1526199 = 2289299) B2289299
theorem B2288075 : Blo 1524459 2288075 := bstep (se 1 (by rfl) ⟨1716056, by rfl⟩ : syracuseStep 2288075 = 3432113) B3432113
theorem B1526219 : Blo 1524459 1526219 := bstep (se 1 (by rfl) ⟨1144664, by rfl⟩ : syracuseStep 1526219 = 2289329) B2289329
theorem B2288087 : Blo 1524459 2288087 := bstep (se 1 (by rfl) ⟨1716065, by rfl⟩ : syracuseStep 2288087 = 3432131) B3432131
theorem B1526231 : Blo 1524459 1526231 := bstep (se 1 (by rfl) ⟨1144673, by rfl⟩ : syracuseStep 1526231 = 2289347) B2289347
theorem B1526251 : Blo 1524459 1526251 := bstep (se 1 (by rfl) ⟨1144688, by rfl⟩ : syracuseStep 1526251 = 2289377) B2289377
theorem B1526263 : Blo 1524459 1526263 := bstep (se 1 (by rfl) ⟨1144697, by rfl⟩ : syracuseStep 1526263 = 2289395) B2289395
theorem B1526283 : Blo 1524459 1526283 := bstep (se 1 (by rfl) ⟨1144712, by rfl⟩ : syracuseStep 1526283 = 2289425) B2289425
theorem B1526295 : Blo 1524459 1526295 := bstep (se 1 (by rfl) ⟨1144721, by rfl⟩ : syracuseStep 1526295 = 2289443) B2289443
theorem B2288153 : Blo 1524459 2288153 := bstep (se 2 (by rfl) ⟨858057, by rfl⟩ : syracuseStep 2288153 = 1716115) B1716115
theorem B1526315 : Blo 1524459 1526315 := bstep (se 1 (by rfl) ⟨1144736, by rfl⟩ : syracuseStep 1526315 = 2289473) B2289473
theorem B1526327 : Blo 1524459 1526327 := bstep (se 1 (by rfl) ⟨1144745, by rfl⟩ : syracuseStep 1526327 = 2289491) B2289491
theorem B5950027 : Blo 1524459 5950027 := bstep (se 1 (by rfl) ⟨4462520, by rfl⟩ : syracuseStep 5950027 = 8925041) B8925041
theorem B3861067 : Blo 1524459 3861067 := bstep (se 1 (by rfl) ⟨2895800, by rfl⟩ : syracuseStep 3861067 = 5791601) B5791601
theorem B1526347 : Blo 1524459 1526347 := bstep (se 1 (by rfl) ⟨1144760, by rfl⟩ : syracuseStep 1526347 = 2289521) B2289521
theorem B1526359 : Blo 1524459 1526359 := bstep (se 1 (by rfl) ⟨1144769, by rfl⟩ : syracuseStep 1526359 = 2289539) B2289539
theorem B5147225 : Blo 1524459 5147225 := bstep (se 2 (by rfl) ⟨1930209, by rfl⟩ : syracuseStep 5147225 = 3860419) B3860419
theorem B1526379 : Blo 1524459 1526379 := bstep (se 1 (by rfl) ⟨1144784, by rfl⟩ : syracuseStep 1526379 = 2289569) B2289569
theorem B1526391 : Blo 1524459 1526391 := bstep (se 1 (by rfl) ⟨1144793, by rfl⟩ : syracuseStep 1526391 = 2289587) B2289587
theorem B2288267 : Blo 1524459 2288267 := bstep (se 1 (by rfl) ⟨1716200, by rfl⟩ : syracuseStep 2288267 = 3432401) B3432401
theorem B1526411 : Blo 1524459 1526411 := bstep (se 1 (by rfl) ⟨1144808, by rfl⟩ : syracuseStep 1526411 = 2289617) B2289617
theorem B15264407 : Blo 1524459 15264407 := bstep (se 1 (by rfl) ⟨11448305, by rfl⟩ : syracuseStep 15264407 = 22896611) B22896611
theorem B2288279 : Blo 1524459 2288279 := bstep (se 1 (by rfl) ⟨1716209, by rfl⟩ : syracuseStep 2288279 = 3432419) B3432419
theorem B15657623 : Blo 1524459 15657623 := bstep (se 1 (by rfl) ⟨11743217, by rfl⟩ : syracuseStep 15657623 = 23486435) B23486435
theorem B1526423 : Blo 1524459 1526423 := bstep (se 1 (by rfl) ⟨1144817, by rfl⟩ : syracuseStep 1526423 = 2289635) B2289635
theorem B1526443 : Blo 1524459 1526443 := bstep (se 1 (by rfl) ⟨1144832, by rfl⟩ : syracuseStep 1526443 = 2289665) B2289665
theorem B1526455 : Blo 1524459 1526455 := bstep (se 1 (by rfl) ⟨1144841, by rfl⟩ : syracuseStep 1526455 = 2289683) B2289683
theorem B3861209 : Blo 1524459 3861209 := bstep (se 2 (by rfl) ⟨1447953, by rfl⟩ : syracuseStep 3861209 = 2895907) B2895907
theorem B2288345 : Blo 1524459 2288345 := bstep (se 2 (by rfl) ⟨858129, by rfl⟩ : syracuseStep 2288345 = 1716259) B1716259
theorem B3664691 : Blo 1524459 3664691 := bstep (se 1 (by rfl) ⟨2748518, by rfl⟩ : syracuseStep 3664691 = 5497037) B5497037
theorem B70454069 : Blo 1524459 70454069 := bstep (se 5 (by rfl) ⟨3302534, by rfl⟩ : syracuseStep 70454069 = 6605069) B6605069
theorem B4401985 : Blo 1524459 4401985 := bstep (se 2 (by rfl) ⟨1650744, by rfl⟩ : syracuseStep 4401985 = 3301489) B3301489
theorem B2288459 : Blo 1524459 2288459 := bstep (se 1 (by rfl) ⟨1716344, by rfl⟩ : syracuseStep 2288459 = 3432689) B3432689
theorem B2288471 : Blo 1524459 2288471 := bstep (se 1 (by rfl) ⟨1716353, by rfl⟩ : syracuseStep 2288471 = 3432707) B3432707
theorem B2894707 : Blo 1524459 2894707 := bstep (se 1 (by rfl) ⟨2171030, by rfl⟩ : syracuseStep 2894707 = 4342061) B4342061
theorem B2288537 : Blo 1524459 2288537 := bstep (se 2 (by rfl) ⟨858201, by rfl⟩ : syracuseStep 2288537 = 1716403) B1716403
theorem B2575307 : Blo 1524459 2575307 := bstep (se 1 (by rfl) ⟨1931480, by rfl⟩ : syracuseStep 2575307 = 3862961) B3862961
theorem B1715179 : Blo 1524459 1715179 := bstep (se 1 (by rfl) ⟨1286384, by rfl⟩ : syracuseStep 1715179 = 2572769) B2572769
theorem B2288651 : Blo 1524459 2288651 := bstep (se 1 (by rfl) ⟨1716488, by rfl⟩ : syracuseStep 2288651 = 3432977) B3432977
theorem B2288663 : Blo 1524459 2288663 := bstep (se 1 (by rfl) ⟨1716497, by rfl⟩ : syracuseStep 2288663 = 3432995) B3432995
theorem B2575435 : Blo 1524459 2575435 := bstep (se 1 (by rfl) ⟨1931576, by rfl⟩ : syracuseStep 2575435 = 3863153) B3863153
theorem B1715287 : Blo 1524459 1715287 := bstep (se 1 (by rfl) ⟨1286465, by rfl⟩ : syracuseStep 1715287 = 2572931) B2572931
theorem B2894935 : Blo 1524459 2894935 := bstep (se 1 (by rfl) ⟨2171201, by rfl⟩ : syracuseStep 2894935 = 4342403) B4342403
theorem B6270041 : Blo 1524459 6270041 := bstep (se 2 (by rfl) ⟨2351265, by rfl⟩ : syracuseStep 6270041 = 4702531) B4702531
theorem B2288729 : Blo 1524459 2288729 := bstep (se 2 (by rfl) ⟨858273, by rfl⟩ : syracuseStep 2288729 = 1716547) B1716547
theorem B2895041 : Blo 1524459 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B2288843 : Blo 1524459 2288843 := bstep (se 1 (by rfl) ⟨1716632, by rfl⟩ : syracuseStep 2288843 = 3433265) B3433265
theorem B2288855 : Blo 1524459 2288855 := bstep (se 1 (by rfl) ⟨1716641, by rfl⟩ : syracuseStep 2288855 = 3433283) B3433283
theorem B2575577 : Blo 1524459 2575577 := bstep (se 2 (by rfl) ⟨965841, by rfl⟩ : syracuseStep 2575577 = 1931683) B1931683
theorem B1715467 : Blo 1524459 1715467 := bstep (se 1 (by rfl) ⟨1286600, by rfl⟩ : syracuseStep 1715467 = 2573201) B2573201
theorem B5147927 : Blo 1524459 5147927 := bstep (se 1 (by rfl) ⟨3860945, by rfl⟩ : syracuseStep 5147927 = 7721891) B7721891
theorem B2288921 : Blo 1524459 2288921 := bstep (se 2 (by rfl) ⟨858345, by rfl⟩ : syracuseStep 2288921 = 1716691) B1716691
theorem B5573963 : Blo 1524459 5573963 := bstep (se 1 (by rfl) ⟨4180472, by rfl⟩ : syracuseStep 5573963 = 8360945) B8360945
theorem B2895193 : Blo 1524459 2895193 := bstep (se 2 (by rfl) ⟨1085697, by rfl⟩ : syracuseStep 2895193 = 2171395) B2171395
theorem B2575705 : Blo 1524459 2575705 := bstep (se 2 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 2575705 = 1931779) B1931779
theorem B1715575 : Blo 1524459 1715575 := bstep (se 1 (by rfl) ⟨1286681, by rfl⟩ : syracuseStep 1715575 = 2573363) B2573363
theorem B2289035 : Blo 1524459 2289035 := bstep (se 1 (by rfl) ⟨1716776, by rfl⟩ : syracuseStep 2289035 = 3433553) B3433553
theorem B2289047 : Blo 1524459 2289047 := bstep (se 1 (by rfl) ⟨1716785, by rfl⟩ : syracuseStep 2289047 = 3433571) B3433571
theorem B2289113 : Blo 1524459 2289113 := bstep (se 2 (by rfl) ⟨858417, by rfl⟩ : syracuseStep 2289113 = 1716835) B1716835
theorem B32968205 : Blo 1524459 32968205 := bstep (se 3 (by rfl) ⟨6181538, by rfl⟩ : syracuseStep 32968205 = 12363077) B12363077
theorem B3862039 : Blo 1524459 3862039 := bstep (se 1 (by rfl) ⟨2896529, by rfl⟩ : syracuseStep 3862039 = 5793059) B5793059
theorem B5500439 : Blo 1524459 5500439 := bstep (se 1 (by rfl) ⟨4125329, by rfl⟩ : syracuseStep 5500439 = 8250659) B8250659
theorem B1715755 : Blo 1524459 1715755 := bstep (se 1 (by rfl) ⟨1286816, by rfl⟩ : syracuseStep 1715755 = 2573633) B2573633
theorem B2289227 : Blo 1524459 2289227 := bstep (se 1 (by rfl) ⟨1716920, by rfl⟩ : syracuseStep 2289227 = 3433841) B3433841
theorem B2289239 : Blo 1524459 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B4345433 : Blo 1524459 4345433 := bstep (se 2 (by rfl) ⟨1629537, by rfl⟩ : syracuseStep 4345433 = 3259075) B3259075
theorem B5795459 : Blo 1524459 5795459 := bstep (se 1 (by rfl) ⟨4346594, by rfl⟩ : syracuseStep 5795459 = 8693189) B8693189
theorem B2748043 : Blo 1524459 2748043 := bstep (se 1 (by rfl) ⟨2061032, by rfl⟩ : syracuseStep 2748043 = 4122065) B4122065
theorem B1715863 : Blo 1524459 1715863 := bstep (se 1 (by rfl) ⟨1286897, by rfl⟩ : syracuseStep 1715863 = 2573795) B2573795
theorem B2289305 : Blo 1524459 2289305 := bstep (se 2 (by rfl) ⟨858489, by rfl⟩ : syracuseStep 2289305 = 1716979) B1716979
theorem B3256051 : Blo 1524459 3256051 := bstep (se 1 (by rfl) ⟨2442038, by rfl⟩ : syracuseStep 3256051 = 4884077) B4884077
theorem B2289419 : Blo 1524459 2289419 := bstep (se 1 (by rfl) ⟨1717064, by rfl⟩ : syracuseStep 2289419 = 3434129) B3434129
theorem B2608919 : Blo 1524459 2608919 := bstep (se 1 (by rfl) ⟨1956689, by rfl⟩ : syracuseStep 2608919 = 3913379) B3913379
theorem B2289431 : Blo 1524459 2289431 := bstep (se 1 (by rfl) ⟨1717073, by rfl⟩ : syracuseStep 2289431 = 3434147) B3434147
theorem B5148467 : Blo 1524459 5148467 := bstep (se 1 (by rfl) ⟨3861350, by rfl⟩ : syracuseStep 5148467 = 7722701) B7722701
theorem B3665729 : Blo 1524459 3665729 := bstep (se 2 (by rfl) ⟨1374648, by rfl⟩ : syracuseStep 3665729 = 2749297) B2749297
theorem B1716043 : Blo 1524459 1716043 := bstep (se 1 (by rfl) ⟨1287032, by rfl⟩ : syracuseStep 1716043 = 2574065) B2574065
theorem B2289497 : Blo 1524459 2289497 := bstep (se 2 (by rfl) ⟨858561, by rfl⟩ : syracuseStep 2289497 = 1717123) B1717123
theorem B4345751 : Blo 1524459 4345751 := bstep (se 1 (by rfl) ⟨3259313, by rfl⟩ : syracuseStep 4345751 = 6518627) B6518627
theorem B1716151 : Blo 1524459 1716151 := bstep (se 1 (by rfl) ⟨1287113, by rfl⟩ : syracuseStep 1716151 = 2574227) B2574227
theorem B3862475 : Blo 1524459 3862475 := bstep (se 1 (by rfl) ⟨2896856, by rfl⟩ : syracuseStep 3862475 = 5793713) B5793713
theorem B2289611 : Blo 1524459 2289611 := bstep (se 1 (by rfl) ⟨1717208, by rfl⟩ : syracuseStep 2289611 = 3434417) B3434417
theorem B2289623 : Blo 1524459 2289623 := bstep (se 1 (by rfl) ⟨1717217, by rfl⟩ : syracuseStep 2289623 = 3434435) B3434435
theorem B3477527 : Blo 1524459 3477527 := bstep (se 1 (by rfl) ⟨2608145, by rfl⟩ : syracuseStep 3477527 = 5216291) B5216291
theorem B2289689 : Blo 1524459 2289689 := bstep (se 2 (by rfl) ⟨858633, by rfl⟩ : syracuseStep 2289689 = 1717267) B1717267
theorem B5148737 : Blo 1524459 5148737 := bstep (se 2 (by rfl) ⟨1930776, by rfl⟩ : syracuseStep 5148737 = 3861553) B3861553
theorem B3256409 : Blo 1524459 3256409 := bstep (se 2 (by rfl) ⟨1221153, by rfl⟩ : syracuseStep 3256409 = 2442307) B2442307
theorem B2748505 : Blo 1524459 2748505 := bstep (se 2 (by rfl) ⟨1030689, by rfl⟩ : syracuseStep 2748505 = 2061379) B2061379
theorem B1716331 : Blo 1524459 1716331 := bstep (se 1 (by rfl) ⟨1287248, by rfl⟩ : syracuseStep 1716331 = 2574497) B2574497
theorem B2937035 : Blo 1524459 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B1716439 : Blo 1524459 1716439 := bstep (se 1 (by rfl) ⟨1287329, by rfl⟩ : syracuseStep 1716439 = 2574659) B2574659
theorem B3862849 : Blo 1524459 3862849 := bstep (se 2 (by rfl) ⟨1448568, by rfl⟩ : syracuseStep 3862849 = 2897137) B2897137
theorem B9777509 : Blo 1524459 9777509 := bstep (se 4 (by rfl) ⟨916641, by rfl⟩ : syracuseStep 9777509 = 1833283) B1833283
theorem B1716619 : Blo 1524459 1716619 := bstep (se 1 (by rfl) ⟨1287464, by rfl⟩ : syracuseStep 1716619 = 2574929) B2574929
theorem B1716727 : Blo 1524459 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B6181379 : Blo 1524459 6181379 := bstep (se 1 (by rfl) ⟨4636034, by rfl⟩ : syracuseStep 6181379 = 9272069) B9272069
theorem B1929739 : Blo 1524459 1929739 := bstep (se 1 (by rfl) ⟨1447304, by rfl⟩ : syracuseStep 1929739 = 2894609) B2894609
theorem B11579921 : Blo 1524459 11579921 := bstep (se 2 (by rfl) ⟨4342470, by rfl⟩ : syracuseStep 11579921 = 8684941) B8684941
theorem B5149277 : Blo 1524459 5149277 := bstep (se 3 (by rfl) ⟨965489, by rfl⟩ : syracuseStep 5149277 = 1930979) B1930979
theorem B2896499 : Blo 1524459 2896499 := bstep (se 1 (by rfl) ⟨2172374, by rfl⟩ : syracuseStep 2896499 = 4344749) B4344749
theorem B1716907 : Blo 1524459 1716907 := bstep (se 1 (by rfl) ⟨1287680, by rfl⟩ : syracuseStep 1716907 = 2575361) B2575361
theorem B4346561 : Blo 1524459 4346561 := bstep (se 2 (by rfl) ⟨1629960, by rfl⟩ : syracuseStep 4346561 = 3259921) B3259921
theorem B5788381 : Blo 1524459 5788381 := bstep (se 3 (by rfl) ⟨1085321, by rfl⟩ : syracuseStep 5788381 = 2170643) B2170643
theorem B2896651 : Blo 1524459 2896651 := bstep (se 1 (by rfl) ⟨2172488, by rfl⟩ : syracuseStep 2896651 = 4344977) B4344977
theorem B1930007 : Blo 1524459 1930007 := bstep (se 1 (by rfl) ⟨1447505, by rfl⟩ : syracuseStep 1930007 = 2895011) B2895011
theorem B1717015 : Blo 1524459 1717015 := bstep (se 1 (by rfl) ⟨1287761, by rfl⟩ : syracuseStep 1717015 = 2575523) B2575523
theorem B8926027 : Blo 1524459 8926027 := bstep (se 1 (by rfl) ⟨6694520, by rfl⟩ : syracuseStep 8926027 = 13389041) B13389041
theorem B9777995 : Blo 1524459 9777995 := bstep (se 1 (by rfl) ⟨7333496, by rfl⟩ : syracuseStep 9777995 = 14666993) B14666993
theorem B14660453 : Blo 1524459 14660453 := bstep (se 4 (by rfl) ⟨1374417, by rfl⟩ : syracuseStep 14660453 = 2748835) B2748835
theorem B10998629 : Blo 1524459 10998629 := bstep (se 4 (by rfl) ⟨1031121, by rfl⟩ : syracuseStep 10998629 = 2062243) B2062243
theorem B3478411 : Blo 1524459 3478411 := bstep (se 1 (by rfl) ⟨2608808, by rfl⟩ : syracuseStep 3478411 = 5217617) B5217617
theorem B6517655 : Blo 1524459 6517655 := bstep (se 1 (by rfl) ⟨4888241, by rfl⟩ : syracuseStep 6517655 = 9776483) B9776483
theorem B3863447 : Blo 1524459 3863447 := bstep (se 1 (by rfl) ⟨2897585, by rfl⟩ : syracuseStep 3863447 = 5795171) B5795171
theorem B1717195 : Blo 1524459 1717195 := bstep (se 1 (by rfl) ⟨1287896, by rfl⟩ : syracuseStep 1717195 = 2575793) B2575793
theorem B2200537 : Blo 1524459 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B43996121 : Blo 1524459 43996121 := bstep (se 2 (by rfl) ⟨16498545, by rfl⟩ : syracuseStep 43996121 = 32997091) B32997091
theorem B2610137 : Blo 1524459 2610137 := bstep (se 2 (by rfl) ⟨978801, by rfl⟩ : syracuseStep 2610137 = 1957603) B1957603
theorem B7328843 : Blo 1524459 7328843 := bstep (se 1 (by rfl) ⟨5496632, by rfl⟩ : syracuseStep 7328843 = 10993265) B10993265
theorem B5870681 : Blo 1524459 5870681 := bstep (se 2 (by rfl) ⟨2201505, by rfl⟩ : syracuseStep 5870681 = 4403011) B4403011
theorem B2896985 : Blo 1524459 2896985 := bstep (se 2 (by rfl) ⟨1086369, by rfl⟩ : syracuseStep 2896985 = 2172739) B2172739
theorem B13210775 : Blo 1524459 13210775 := bstep (se 1 (by rfl) ⟨9908081, by rfl⟩ : syracuseStep 13210775 = 19816163) B19816163
theorem B5018969 : Blo 1524459 5018969 := bstep (se 2 (by rfl) ⟨1882113, by rfl⟩ : syracuseStep 5018969 = 3764227) B3764227
theorem B2749889 : Blo 1524459 2749889 := bstep (se 2 (by rfl) ⟨1031208, by rfl⟩ : syracuseStep 2749889 = 2062417) B2062417
theorem B1930711 : Blo 1524459 1930711 := bstep (se 1 (by rfl) ⟨1448033, by rfl⟩ : syracuseStep 1930711 = 2896067) B2896067
theorem B19535377 : Blo 1524459 19535377 := bstep (se 2 (by rfl) ⟨7325766, by rfl⟩ : syracuseStep 19535377 = 14651533) B14651533
theorem B11589155 : Blo 1524459 11589155 := bstep (se 1 (by rfl) ⟨8691866, by rfl⟩ : syracuseStep 11589155 = 17383733) B17383733
theorem B6182531 : Blo 1524459 6182531 := bstep (se 1 (by rfl) ⟨4636898, by rfl⟩ : syracuseStep 6182531 = 9273797) B9273797
theorem B5150411 : Blo 1524459 5150411 := bstep (se 1 (by rfl) ⟨3862808, by rfl⟩ : syracuseStep 5150411 = 7725617) B7725617
theorem B2897623 : Blo 1524459 2897623 := bstep (se 1 (by rfl) ⟨2173217, by rfl⟩ : syracuseStep 2897623 = 4346435) B4346435
theorem B3430169 : Blo 1524459 3430169 := bstep (se 2 (by rfl) ⟨1286313, by rfl⟩ : syracuseStep 3430169 = 2572627) B2572627
theorem B3430259 : Blo 1524459 3430259 := bstep (se 1 (by rfl) ⟨2572694, by rfl⟩ : syracuseStep 3430259 = 5145389) B5145389
theorem B3430295 : Blo 1524459 3430295 := bstep (se 1 (by rfl) ⟨2572721, by rfl⟩ : syracuseStep 3430295 = 5145443) B5145443
theorem B3094451 : Blo 1524459 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B1628119 : Blo 1524459 1628119 := bstep (se 1 (by rfl) ⟨1221089, by rfl⟩ : syracuseStep 1628119 = 2442179) B2442179
theorem B5789657 : Blo 1524459 5789657 := bstep (se 2 (by rfl) ⟨2171121, by rfl⟩ : syracuseStep 5789657 = 4342243) B4342243
theorem B9770969 : Blo 1524459 9770969 := bstep (se 2 (by rfl) ⟨3664113, by rfl⟩ : syracuseStep 9770969 = 7328227) B7328227
theorem B5150681 : Blo 1524459 5150681 := bstep (se 2 (by rfl) ⟨1931505, by rfl⟩ : syracuseStep 5150681 = 3863011) B3863011
theorem B5494787 : Blo 1524459 5494787 := bstep (se 1 (by rfl) ⟨4121090, by rfl⟩ : syracuseStep 5494787 = 8242181) B8242181
theorem B7723025 : Blo 1524459 7723025 := bstep (se 2 (by rfl) ⟨2896134, by rfl⟩ : syracuseStep 7723025 = 5792269) B5792269
theorem B28227653 : Blo 1524459 28227653 := bstep (se 4 (by rfl) ⟨2646342, by rfl⟩ : syracuseStep 28227653 = 5292685) B5292685
theorem B3430475 : Blo 1524459 3430475 := bstep (se 1 (by rfl) ⟨2572856, by rfl⟩ : syracuseStep 3430475 = 5145713) B5145713
theorem B3258443 : Blo 1524459 3258443 := bstep (se 1 (by rfl) ⟨2443832, by rfl⟩ : syracuseStep 3258443 = 4887665) B4887665
theorem B21993565 : Blo 1524459 21993565 := bstep (se 3 (by rfl) ⟨4123793, by rfl⟩ : syracuseStep 21993565 = 8247587) B8247587
theorem B3430529 : Blo 1524459 3430529 := bstep (se 2 (by rfl) ⟨1286448, by rfl⟩ : syracuseStep 3430529 = 2572897) B2572897
theorem B1628299 : Blo 1524459 1628299 := bstep (se 1 (by rfl) ⟨1221224, by rfl⟩ : syracuseStep 1628299 = 2442449) B2442449
theorem B7723187 : Blo 1524459 7723187 := bstep (se 1 (by rfl) ⟨5792390, by rfl⟩ : syracuseStep 7723187 = 11584781) B11584781
theorem B13023449 : Blo 1524459 13023449 := bstep (se 2 (by rfl) ⟨4883793, by rfl⟩ : syracuseStep 13023449 = 9767587) B9767587
theorem B2750681 : Blo 1524459 2750681 := bstep (se 2 (by rfl) ⟨1031505, by rfl⟩ : syracuseStep 2750681 = 2063011) B2063011
theorem B39090437 : Blo 1524459 39090437 := bstep (se 4 (by rfl) ⟨3664728, by rfl⟩ : syracuseStep 39090437 = 7329457) B7329457
theorem B3430745 : Blo 1524459 3430745 := bstep (se 2 (by rfl) ⟨1286529, by rfl⟩ : syracuseStep 3430745 = 2573059) B2573059
theorem B125254001 : Blo 1524459 125254001 := bstep (se 2 (by rfl) ⟨46970250, by rfl⟩ : syracuseStep 125254001 = 93940501) B93940501
theorem B3135883 : Blo 1524459 3135883 := bstep (se 1 (by rfl) ⟨2351912, by rfl⟩ : syracuseStep 3135883 = 4703825) B4703825
theorem B3430835 : Blo 1524459 3430835 := bstep (se 1 (by rfl) ⟨2573126, by rfl⟩ : syracuseStep 3430835 = 5146253) B5146253
theorem B3430871 : Blo 1524459 3430871 := bstep (se 1 (by rfl) ⟨2573153, by rfl⟩ : syracuseStep 3430871 = 5146307) B5146307
theorem B3431051 : Blo 1524459 3431051 := bstep (se 1 (by rfl) ⟨2573288, by rfl⟩ : syracuseStep 3431051 = 5146577) B5146577
theorem B5151383 : Blo 1524459 5151383 := bstep (se 1 (by rfl) ⟨3863537, by rfl⟩ : syracuseStep 5151383 = 7727075) B7727075
theorem B4889267 : Blo 1524459 4889267 := bstep (se 1 (by rfl) ⟨3666950, by rfl⟩ : syracuseStep 4889267 = 7333901) B7333901
theorem B3431105 : Blo 1524459 3431105 := bstep (se 2 (by rfl) ⟨1286664, by rfl⟩ : syracuseStep 3431105 = 2573329) B2573329
theorem B13032197 : Blo 1524459 13032197 := bstep (se 4 (by rfl) ⟨1221768, by rfl⟩ : syracuseStep 13032197 = 2443537) B2443537
theorem B3431321 : Blo 1524459 3431321 := bstep (se 2 (by rfl) ⟨1286745, by rfl⟩ : syracuseStep 3431321 = 2573491) B2573491
theorem B3431411 : Blo 1524459 3431411 := bstep (se 1 (by rfl) ⟨2573558, by rfl⟩ : syracuseStep 3431411 = 5147117) B5147117
theorem B5495825 : Blo 1524459 5495825 := bstep (se 2 (by rfl) ⟨2060934, by rfl⟩ : syracuseStep 5495825 = 4121869) B4121869
theorem B3431447 : Blo 1524459 3431447 := bstep (se 1 (by rfl) ⟨2573585, by rfl⟩ : syracuseStep 3431447 = 5147171) B5147171
theorem B3431627 : Blo 1524459 3431627 := bstep (se 1 (by rfl) ⟨2573720, by rfl⟩ : syracuseStep 3431627 = 5147441) B5147441
theorem B3431681 : Blo 1524459 3431681 := bstep (se 2 (by rfl) ⟨1286880, by rfl⟩ : syracuseStep 3431681 = 2573761) B2573761
theorem B62594309 : Blo 1524459 62594309 := bstep (se 4 (by rfl) ⟨5868216, by rfl⟩ : syracuseStep 62594309 = 11736433) B11736433
theorem B13909265 : Blo 1524459 13909265 := bstep (se 2 (by rfl) ⟨5215974, by rfl⟩ : syracuseStep 13909265 = 10431949) B10431949
theorem B3259673 : Blo 1524459 3259673 := bstep (se 2 (by rfl) ⟨1222377, by rfl⟩ : syracuseStep 3259673 = 2444755) B2444755
theorem B6520115 : Blo 1524459 6520115 := bstep (se 1 (by rfl) ⟨4890086, by rfl⟩ : syracuseStep 6520115 = 9780173) B9780173
theorem B4889945 : Blo 1524459 4889945 := bstep (se 2 (by rfl) ⟨1833729, by rfl⟩ : syracuseStep 4889945 = 3667459) B3667459
theorem B4341185 : Blo 1524459 4341185 := bstep (se 2 (by rfl) ⟨1627944, by rfl⟩ : syracuseStep 4341185 = 3255889) B3255889
theorem B11148749 : Blo 1524459 11148749 := bstep (se 3 (by rfl) ⟨2090390, by rfl⟩ : syracuseStep 11148749 = 4180781) B4180781
theorem B3431897 : Blo 1524459 3431897 := bstep (se 2 (by rfl) ⟨1286961, by rfl⟩ : syracuseStep 3431897 = 2573923) B2573923
theorem B15646243 : Blo 1524459 15646243 := bstep (se 1 (by rfl) ⟨11734682, by rfl⟩ : syracuseStep 15646243 = 23469365) B23469365
theorem B5791283 : Blo 1524459 5791283 := bstep (se 1 (by rfl) ⟨4343462, by rfl⟩ : syracuseStep 5791283 = 8686925) B8686925
theorem B3431987 : Blo 1524459 3431987 := bstep (se 1 (by rfl) ⟨2573990, by rfl⟩ : syracuseStep 3431987 = 5147981) B5147981
theorem B5791297 : Blo 1524459 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B3432023 : Blo 1524459 3432023 := bstep (se 1 (by rfl) ⟨2574017, by rfl⟩ : syracuseStep 3432023 = 5148035) B5148035
theorem B3260083 : Blo 1524459 3260083 := bstep (se 1 (by rfl) ⟨2445062, by rfl⟩ : syracuseStep 3260083 = 4890125) B4890125
theorem B3432203 : Blo 1524459 3432203 := bstep (se 1 (by rfl) ⟨2574152, by rfl⟩ : syracuseStep 3432203 = 5148305) B5148305
theorem B14868269 : Blo 1524459 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B3432257 : Blo 1524459 3432257 := bstep (se 2 (by rfl) ⟨1287096, by rfl⟩ : syracuseStep 3432257 = 2574193) B2574193
theorem B2318351 : Blo 1524459 2318351 := bstep (se 1 (by rfl) ⟨1738763, by rfl⟩ : syracuseStep 2318351 = 3477527) B3477527
theorem B3432491 : Blo 1524459 3432491 := bstep (se 1 (by rfl) ⟨2574368, by rfl⟩ : syracuseStep 3432491 = 5148737) B5148737
theorem B1958023 : Blo 1524459 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B2171065 : Blo 1524459 2171065 := bstep (se 2 (by rfl) ⟨814149, by rfl⟩ : syracuseStep 2171065 = 1628299) B1628299
theorem B8683757 : Blo 1524459 8683757 := bstep (se 3 (by rfl) ⟨1628204, by rfl⟩ : syracuseStep 8683757 = 3256409) B3256409
theorem B7725293 : Blo 1524459 7725293 := bstep (se 3 (by rfl) ⟨1448492, by rfl⟩ : syracuseStep 7725293 = 2896985) B2896985
theorem B4120919 : Blo 1524459 4120919 := bstep (se 1 (by rfl) ⟨3090689, by rfl⟩ : syracuseStep 4120919 = 6181379) B6181379
theorem B3432851 : Blo 1524459 3432851 := bstep (se 1 (by rfl) ⟨2574638, by rfl⟩ : syracuseStep 3432851 = 5149277) B5149277
theorem B3432905 : Blo 1524459 3432905 := bstep (se 2 (by rfl) ⟨1287339, by rfl⟩ : syracuseStep 3432905 = 2574679) B2574679
theorem B7832011 : Blo 1524459 7832011 := bstep (se 1 (by rfl) ⟨5874008, by rfl⟩ : syracuseStep 7832011 = 11748017) B11748017
theorem B2572843 : Blo 1524459 2572843 := bstep (se 1 (by rfl) ⟨1929632, by rfl⟩ : syracuseStep 2572843 = 3859265) B3859265
theorem B9773635 : Blo 1524459 9773635 := bstep (se 1 (by rfl) ⟨7330226, by rfl⟩ : syracuseStep 9773635 = 14660453) B14660453
theorem B7332419 : Blo 1524459 7332419 := bstep (se 1 (by rfl) ⟨5499314, by rfl⟩ : syracuseStep 7332419 = 10998629) B10998629
theorem B2572985 : Blo 1524459 2572985 := bstep (se 2 (by rfl) ⟨964869, by rfl⟩ : syracuseStep 2572985 = 1929739) B1929739
theorem B1524487 : Blo 1524459 1524487 := bstep (se 1 (by rfl) ⟨1143365, by rfl⟩ : syracuseStep 1524487 = 2286731) B2286731
theorem B1524495 : Blo 1524459 1524495 := bstep (se 1 (by rfl) ⟨1143371, by rfl⟩ : syracuseStep 1524495 = 2286743) B2286743
theorem B8807183 : Blo 1524459 8807183 := bstep (se 1 (by rfl) ⟨6605387, by rfl⟩ : syracuseStep 8807183 = 13210775) B13210775
theorem B33424163 : Blo 1524459 33424163 := bstep (se 1 (by rfl) ⟨25068122, by rfl⟩ : syracuseStep 33424163 = 50136245) B50136245
theorem B1524539 : Blo 1524459 1524539 := bstep (se 1 (by rfl) ⟨1143404, by rfl⟩ : syracuseStep 1524539 = 2286809) B2286809
theorem B4342643 : Blo 1524459 4342643 := bstep (se 1 (by rfl) ⟨3256982, by rfl⟩ : syracuseStep 4342643 = 6513965) B6513965
theorem B1524615 : Blo 1524459 1524615 := bstep (se 1 (by rfl) ⟨1143461, by rfl⟩ : syracuseStep 1524615 = 2286923) B2286923
theorem B1524623 : Blo 1524459 1524623 := bstep (se 1 (by rfl) ⟨1143467, by rfl⟩ : syracuseStep 1524623 = 2286935) B2286935
theorem B5145497 : Blo 1524459 5145497 := bstep (se 2 (by rfl) ⟨1929561, by rfl⟩ : syracuseStep 5145497 = 3859123) B3859123
theorem B8684441 : Blo 1524459 8684441 := bstep (se 2 (by rfl) ⟨3256665, by rfl⟩ : syracuseStep 8684441 = 6513331) B6513331
theorem B1524667 : Blo 1524459 1524667 := bstep (se 1 (by rfl) ⟨1143500, by rfl⟩ : syracuseStep 1524667 = 2287001) B2287001
theorem B7717841 : Blo 1524459 7717841 := bstep (se 2 (by rfl) ⟨2894190, by rfl⟩ : syracuseStep 7717841 = 5788381) B5788381
theorem B1524743 : Blo 1524459 1524743 := bstep (se 1 (by rfl) ⟨1143557, by rfl⟩ : syracuseStep 1524743 = 2287115) B2287115
theorem B1524751 : Blo 1524459 1524751 := bstep (se 1 (by rfl) ⟨1143563, by rfl⟩ : syracuseStep 1524751 = 2287127) B2287127
theorem B7726103 : Blo 1524459 7726103 := bstep (se 1 (by rfl) ⟨5794577, by rfl⟩ : syracuseStep 7726103 = 11589155) B11589155
theorem B1524795 : Blo 1524459 1524795 := bstep (se 1 (by rfl) ⟨1143596, by rfl⟩ : syracuseStep 1524795 = 2287193) B2287193
theorem B4121687 : Blo 1524459 4121687 := bstep (se 1 (by rfl) ⟨3091265, by rfl⟩ : syracuseStep 4121687 = 6182531) B6182531
theorem B1524871 : Blo 1524459 1524871 := bstep (se 1 (by rfl) ⟨1143653, by rfl⟩ : syracuseStep 1524871 = 2287307) B2287307
theorem B3433607 : Blo 1524459 3433607 := bstep (se 1 (by rfl) ⟨2575205, by rfl⟩ : syracuseStep 3433607 = 5150411) B5150411
theorem B1524879 : Blo 1524459 1524879 := bstep (se 1 (by rfl) ⟨1143659, by rfl⟩ : syracuseStep 1524879 = 2287319) B2287319
theorem B3859609 : Blo 1524459 3859609 := bstep (se 2 (by rfl) ⟨1447353, by rfl⟩ : syracuseStep 3859609 = 2894707) B2894707
theorem B4637881 : Blo 1524459 4637881 := bstep (se 2 (by rfl) ⟨1739205, by rfl⟩ : syracuseStep 4637881 = 3478411) B3478411
theorem B2286779 : Blo 1524459 2286779 := bstep (se 1 (by rfl) ⟨1715084, by rfl⟩ : syracuseStep 2286779 = 3430169) B3430169
theorem B1524923 : Blo 1524459 1524923 := bstep (se 1 (by rfl) ⟨1143692, by rfl⟩ : syracuseStep 1524923 = 2287385) B2287385
theorem B2286839 : Blo 1524459 2286839 := bstep (se 1 (by rfl) ⟨1715129, by rfl⟩ : syracuseStep 2286839 = 3430259) B3430259
theorem B1524999 : Blo 1524459 1524999 := bstep (se 1 (by rfl) ⟨1143749, by rfl⟩ : syracuseStep 1524999 = 2287499) B2287499
theorem B2286863 : Blo 1524459 2286863 := bstep (se 1 (by rfl) ⟨1715147, by rfl⟩ : syracuseStep 2286863 = 3430295) B3430295
theorem B1525007 : Blo 1524459 1525007 := bstep (se 1 (by rfl) ⟨1143755, by rfl⟩ : syracuseStep 1525007 = 2287511) B2287511
theorem B2934049 : Blo 1524459 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B2286905 : Blo 1524459 2286905 := bstep (se 2 (by rfl) ⟨857589, by rfl⟩ : syracuseStep 2286905 = 1715179) B1715179
theorem B3859771 : Blo 1524459 3859771 := bstep (se 1 (by rfl) ⟨2894828, by rfl⟩ : syracuseStep 3859771 = 5789657) B5789657
theorem B1525051 : Blo 1524459 1525051 := bstep (se 1 (by rfl) ⟨1143788, by rfl⟩ : syracuseStep 1525051 = 2287577) B2287577
theorem B3433787 : Blo 1524459 3433787 := bstep (se 1 (by rfl) ⟨2575340, by rfl⟩ : syracuseStep 3433787 = 5150681) B5150681
theorem B3663191 : Blo 1524459 3663191 := bstep (se 1 (by rfl) ⟨2747393, by rfl⟩ : syracuseStep 3663191 = 5494787) B5494787
theorem B2573687 : Blo 1524459 2573687 := bstep (se 1 (by rfl) ⟨1930265, by rfl⟩ : syracuseStep 2573687 = 3860531) B3860531
theorem B18818435 : Blo 1524459 18818435 := bstep (se 1 (by rfl) ⟨14113826, by rfl⟩ : syracuseStep 18818435 = 28227653) B28227653
theorem B2286983 : Blo 1524459 2286983 := bstep (se 1 (by rfl) ⟨1715237, by rfl⟩ : syracuseStep 2286983 = 3430475) B3430475
theorem B1525127 : Blo 1524459 1525127 := bstep (se 1 (by rfl) ⟨1143845, by rfl⟩ : syracuseStep 1525127 = 2287691) B2287691
theorem B20874631 : Blo 1524459 20874631 := bstep (se 1 (by rfl) ⟨15655973, by rfl⟩ : syracuseStep 20874631 = 31311947) B31311947
theorem B2172295 : Blo 1524459 2172295 := bstep (se 1 (by rfl) ⟨1629221, by rfl⟩ : syracuseStep 2172295 = 3258443) B3258443
theorem B1525135 : Blo 1524459 1525135 := bstep (se 1 (by rfl) ⟨1143851, by rfl⟩ : syracuseStep 1525135 = 2287703) B2287703
theorem B2287019 : Blo 1524459 2287019 := bstep (se 1 (by rfl) ⟨1715264, by rfl⟩ : syracuseStep 2287019 = 3430529) B3430529
theorem B3433913 : Blo 1524459 3433913 := bstep (se 2 (by rfl) ⟨1287717, by rfl⟩ : syracuseStep 3433913 = 2575435) B2575435
theorem B1525179 : Blo 1524459 1525179 := bstep (se 1 (by rfl) ⟨1143884, by rfl⟩ : syracuseStep 1525179 = 2287769) B2287769
theorem B2287049 : Blo 1524459 2287049 := bstep (se 2 (by rfl) ⟨857643, by rfl⟩ : syracuseStep 2287049 = 1715287) B1715287
theorem B3859913 : Blo 1524459 3859913 := bstep (se 2 (by rfl) ⟨1447467, by rfl⟩ : syracuseStep 3859913 = 2894935) B2894935
theorem B26060291 : Blo 1524459 26060291 := bstep (se 1 (by rfl) ⟨19545218, by rfl⟩ : syracuseStep 26060291 = 39090437) B39090437
theorem B1525255 : Blo 1524459 1525255 := bstep (se 1 (by rfl) ⟨1143941, by rfl⟩ : syracuseStep 1525255 = 2287883) B2287883
theorem B1525263 : Blo 1524459 1525263 := bstep (se 1 (by rfl) ⟨1143947, by rfl⟩ : syracuseStep 1525263 = 2287895) B2287895
theorem B2287163 : Blo 1524459 2287163 := bstep (se 1 (by rfl) ⟨1715372, by rfl⟩ : syracuseStep 2287163 = 3430745) B3430745
theorem B1525307 : Blo 1524459 1525307 := bstep (se 1 (by rfl) ⟨1143980, by rfl⟩ : syracuseStep 1525307 = 2287961) B2287961
theorem B83502667 : Blo 1524459 83502667 := bstep (se 1 (by rfl) ⟨62627000, by rfl⟩ : syracuseStep 83502667 = 125254001) B125254001
theorem B5146199 : Blo 1524459 5146199 := bstep (se 1 (by rfl) ⟨3859649, by rfl⟩ : syracuseStep 5146199 = 7719299) B7719299
theorem B2287223 : Blo 1524459 2287223 := bstep (se 1 (by rfl) ⟨1715417, by rfl⟩ : syracuseStep 2287223 = 3430835) B3430835
theorem B12371575 : Blo 1524459 12371575 := bstep (se 1 (by rfl) ⟨9278681, by rfl⟩ : syracuseStep 12371575 = 18557363) B18557363
theorem B1525383 : Blo 1524459 1525383 := bstep (se 1 (by rfl) ⟨1144037, by rfl⟩ : syracuseStep 1525383 = 2288075) B2288075
theorem B2287247 : Blo 1524459 2287247 := bstep (se 1 (by rfl) ⟨1715435, by rfl⟩ : syracuseStep 2287247 = 3430871) B3430871
theorem B1525391 : Blo 1524459 1525391 := bstep (se 1 (by rfl) ⟨1144043, by rfl⟩ : syracuseStep 1525391 = 2288087) B2288087
theorem B2287289 : Blo 1524459 2287289 := bstep (se 2 (by rfl) ⟨857733, by rfl⟩ : syracuseStep 2287289 = 1715467) B1715467
theorem B1525435 : Blo 1524459 1525435 := bstep (se 1 (by rfl) ⟨1144076, by rfl⟩ : syracuseStep 1525435 = 2288153) B2288153
theorem B47605477 : Blo 1524459 47605477 := bstep (se 4 (by rfl) ⟨4463013, by rfl⟩ : syracuseStep 47605477 = 8926027) B8926027
theorem B2287367 : Blo 1524459 2287367 := bstep (se 1 (by rfl) ⟨1715525, by rfl⟩ : syracuseStep 2287367 = 3431051) B3431051
theorem B1525511 : Blo 1524459 1525511 := bstep (se 1 (by rfl) ⟨1144133, by rfl⟩ : syracuseStep 1525511 = 2288267) B2288267
theorem B10176271 : Blo 1524459 10176271 := bstep (se 1 (by rfl) ⟨7632203, by rfl⟩ : syracuseStep 10176271 = 15264407) B15264407
theorem B1525519 : Blo 1524459 1525519 := bstep (se 1 (by rfl) ⟨1144139, by rfl⟩ : syracuseStep 1525519 = 2288279) B2288279
theorem B10438415 : Blo 1524459 10438415 := bstep (se 1 (by rfl) ⟨7828811, by rfl⟩ : syracuseStep 10438415 = 15657623) B15657623
theorem B3434255 : Blo 1524459 3434255 := bstep (se 1 (by rfl) ⟨2575691, by rfl⟩ : syracuseStep 3434255 = 5151383) B5151383
theorem B3860257 : Blo 1524459 3860257 := bstep (se 2 (by rfl) ⟨1447596, by rfl⟩ : syracuseStep 3860257 = 2895193) B2895193
theorem B3434273 : Blo 1524459 3434273 := bstep (se 2 (by rfl) ⟨1287852, by rfl⟩ : syracuseStep 3434273 = 2575705) B2575705
theorem B2287403 : Blo 1524459 2287403 := bstep (se 1 (by rfl) ⟨1715552, by rfl⟩ : syracuseStep 2287403 = 3431105) B3431105
theorem B2574139 : Blo 1524459 2574139 := bstep (se 1 (by rfl) ⟨1930604, by rfl⟩ : syracuseStep 2574139 = 3861209) B3861209
theorem B1525563 : Blo 1524459 1525563 := bstep (se 1 (by rfl) ⟨1144172, by rfl⟩ : syracuseStep 1525563 = 2288345) B2288345
theorem B2287433 : Blo 1524459 2287433 := bstep (se 2 (by rfl) ⟨857787, by rfl⟩ : syracuseStep 2287433 = 1715575) B1715575
theorem B2443127 : Blo 1524459 2443127 := bstep (se 1 (by rfl) ⟨1832345, by rfl⟩ : syracuseStep 2443127 = 3664691) B3664691
theorem B1525639 : Blo 1524459 1525639 := bstep (se 1 (by rfl) ⟨1144229, by rfl⟩ : syracuseStep 1525639 = 2288459) B2288459
theorem B1525647 : Blo 1524459 1525647 := bstep (se 1 (by rfl) ⟨1144235, by rfl⟩ : syracuseStep 1525647 = 2288471) B2288471
theorem B2287547 : Blo 1524459 2287547 := bstep (se 1 (by rfl) ⟨1715660, by rfl⟩ : syracuseStep 2287547 = 3431321) B3431321
theorem B1525691 : Blo 1524459 1525691 := bstep (se 1 (by rfl) ⟨1144268, by rfl⟩ : syracuseStep 1525691 = 2288537) B2288537
theorem B2574281 : Blo 1524459 2574281 := bstep (se 2 (by rfl) ⟨965355, by rfl⟩ : syracuseStep 2574281 = 1930711) B1930711
theorem B2287607 : Blo 1524459 2287607 := bstep (se 1 (by rfl) ⟨1715705, by rfl⟩ : syracuseStep 2287607 = 3431411) B3431411
theorem B1525767 : Blo 1524459 1525767 := bstep (se 1 (by rfl) ⟨1144325, by rfl⟩ : syracuseStep 1525767 = 2288651) B2288651
theorem B3663883 : Blo 1524459 3663883 := bstep (se 1 (by rfl) ⟨2747912, by rfl⟩ : syracuseStep 3663883 = 5495825) B5495825
theorem B2287631 : Blo 1524459 2287631 := bstep (se 1 (by rfl) ⟨1715723, by rfl⟩ : syracuseStep 2287631 = 3431447) B3431447
theorem B1525775 : Blo 1524459 1525775 := bstep (se 1 (by rfl) ⟨1144331, by rfl⟩ : syracuseStep 1525775 = 2288663) B2288663
theorem B2287673 : Blo 1524459 2287673 := bstep (se 2 (by rfl) ⟨857877, by rfl⟩ : syracuseStep 2287673 = 1715755) B1715755
theorem B4180027 : Blo 1524459 4180027 := bstep (se 1 (by rfl) ⟨3135020, by rfl⟩ : syracuseStep 4180027 = 6270041) B6270041
theorem B1525819 : Blo 1524459 1525819 := bstep (se 1 (by rfl) ⟨1144364, by rfl⟩ : syracuseStep 1525819 = 2288729) B2288729
theorem B5146685 : Blo 1524459 5146685 := bstep (se 3 (by rfl) ⟨965003, by rfl⟩ : syracuseStep 5146685 = 1930007) B1930007
theorem B35719261 : Blo 1524459 35719261 := bstep (se 3 (by rfl) ⟨6697361, by rfl⟩ : syracuseStep 35719261 = 13394723) B13394723
theorem B2287751 : Blo 1524459 2287751 := bstep (se 1 (by rfl) ⟨1715813, by rfl⟩ : syracuseStep 2287751 = 3431627) B3431627
theorem B1525895 : Blo 1524459 1525895 := bstep (se 1 (by rfl) ⟨1144421, by rfl⟩ : syracuseStep 1525895 = 2288843) B2288843
theorem B1525903 : Blo 1524459 1525903 := bstep (se 1 (by rfl) ⟨1144427, by rfl⟩ : syracuseStep 1525903 = 2288855) B2288855
theorem B2287787 : Blo 1524459 2287787 := bstep (se 1 (by rfl) ⟨1715840, by rfl⟩ : syracuseStep 2287787 = 3431681) B3431681
theorem B3664057 : Blo 1524459 3664057 := bstep (se 2 (by rfl) ⟨1374021, by rfl⟩ : syracuseStep 3664057 = 2748043) B2748043
theorem B1525947 : Blo 1524459 1525947 := bstep (se 1 (by rfl) ⟨1144460, by rfl⟩ : syracuseStep 1525947 = 2288921) B2288921
theorem B2173115 : Blo 1524459 2173115 := bstep (se 1 (by rfl) ⟨1629836, by rfl⟩ : syracuseStep 2173115 = 3259673) B3259673
theorem B2287817 : Blo 1524459 2287817 := bstep (se 2 (by rfl) ⟨857931, by rfl⟩ : syracuseStep 2287817 = 1715863) B1715863
theorem B1526023 : Blo 1524459 1526023 := bstep (se 1 (by rfl) ⟨1144517, by rfl⟩ : syracuseStep 1526023 = 2289035) B2289035
theorem B1526031 : Blo 1524459 1526031 := bstep (se 1 (by rfl) ⟨1144523, by rfl⟩ : syracuseStep 1526031 = 2289047) B2289047
theorem B2894123 : Blo 1524459 2894123 := bstep (se 1 (by rfl) ⟨2170592, by rfl⟩ : syracuseStep 2894123 = 4341185) B4341185
theorem B7432499 : Blo 1524459 7432499 := bstep (se 1 (by rfl) ⟨5574374, by rfl⟩ : syracuseStep 7432499 = 11148749) B11148749
theorem B2287931 : Blo 1524459 2287931 := bstep (se 1 (by rfl) ⟨1715948, by rfl⟩ : syracuseStep 2287931 = 3431897) B3431897
theorem B1526075 : Blo 1524459 1526075 := bstep (se 1 (by rfl) ⟨1144556, by rfl⟩ : syracuseStep 1526075 = 2289113) B2289113
theorem B3860855 : Blo 1524459 3860855 := bstep (se 1 (by rfl) ⟨2895641, by rfl⟩ : syracuseStep 3860855 = 5791283) B5791283
theorem B2287991 : Blo 1524459 2287991 := bstep (se 1 (by rfl) ⟨1715993, by rfl⟩ : syracuseStep 2287991 = 3431987) B3431987
theorem B1526151 : Blo 1524459 1526151 := bstep (se 1 (by rfl) ⟨1144613, by rfl⟩ : syracuseStep 1526151 = 2289227) B2289227
theorem B2288015 : Blo 1524459 2288015 := bstep (se 1 (by rfl) ⟨1716011, by rfl⟩ : syracuseStep 2288015 = 3432023) B3432023
theorem B1526159 : Blo 1524459 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B2288057 : Blo 1524459 2288057 := bstep (se 2 (by rfl) ⟨858021, by rfl⟩ : syracuseStep 2288057 = 1716043) B1716043
theorem B1526203 : Blo 1524459 1526203 := bstep (se 1 (by rfl) ⟨1144652, by rfl⟩ : syracuseStep 1526203 = 2289305) B2289305
theorem B2288135 : Blo 1524459 2288135 := bstep (se 1 (by rfl) ⟨1716101, by rfl⟩ : syracuseStep 2288135 = 3432203) B3432203
theorem B1526279 : Blo 1524459 1526279 := bstep (se 1 (by rfl) ⟨1144709, by rfl⟩ : syracuseStep 1526279 = 2289419) B2289419
theorem B1739279 : Blo 1524459 1739279 := bstep (se 1 (by rfl) ⟨1304459, by rfl⟩ : syracuseStep 1739279 = 2608919) B2608919
theorem B1526287 : Blo 1524459 1526287 := bstep (se 1 (by rfl) ⟨1144715, by rfl⟩ : syracuseStep 1526287 = 2289431) B2289431
theorem B2288171 : Blo 1524459 2288171 := bstep (se 1 (by rfl) ⟨1716128, by rfl⟩ : syracuseStep 2288171 = 3432257) B3432257
theorem B2443819 : Blo 1524459 2443819 := bstep (se 1 (by rfl) ⟨1832864, by rfl⟩ : syracuseStep 2443819 = 3665729) B3665729
theorem B1526331 : Blo 1524459 1526331 := bstep (se 1 (by rfl) ⟨1144748, by rfl⟩ : syracuseStep 1526331 = 2289497) B2289497
theorem B2288201 : Blo 1524459 2288201 := bstep (se 2 (by rfl) ⟨858075, by rfl⟩ : syracuseStep 2288201 = 1716151) B1716151
theorem B2574983 : Blo 1524459 2574983 := bstep (se 1 (by rfl) ⟨1931237, by rfl⟩ : syracuseStep 2574983 = 3862475) B3862475
theorem B1526407 : Blo 1524459 1526407 := bstep (se 1 (by rfl) ⟨1144805, by rfl⟩ : syracuseStep 1526407 = 2289611) B2289611
theorem B1526415 : Blo 1524459 1526415 := bstep (se 1 (by rfl) ⟨1144811, by rfl⟩ : syracuseStep 1526415 = 2289623) B2289623
theorem B2288315 : Blo 1524459 2288315 := bstep (se 1 (by rfl) ⟨1716236, by rfl⟩ : syracuseStep 2288315 = 3432473) B3432473
theorem B1526459 : Blo 1524459 1526459 := bstep (se 1 (by rfl) ⟨1144844, by rfl⟩ : syracuseStep 1526459 = 2289689) B2289689
theorem B2288375 : Blo 1524459 2288375 := bstep (se 1 (by rfl) ⟨1716281, by rfl⟩ : syracuseStep 2288375 = 3432563) B3432563
theorem B2288399 : Blo 1524459 2288399 := bstep (se 1 (by rfl) ⟨1716299, by rfl⟩ : syracuseStep 2288399 = 3432599) B3432599
theorem B3664673 : Blo 1524459 3664673 := bstep (se 2 (by rfl) ⟨1374252, by rfl⟩ : syracuseStep 3664673 = 2748505) B2748505
theorem B2288441 : Blo 1524459 2288441 := bstep (se 2 (by rfl) ⟨858165, by rfl⟩ : syracuseStep 2288441 = 1716331) B1716331
theorem B2288519 : Blo 1524459 2288519 := bstep (se 1 (by rfl) ⟨1716389, by rfl⟩ : syracuseStep 2288519 = 3432779) B3432779
theorem B2288555 : Blo 1524459 2288555 := bstep (se 1 (by rfl) ⟨1716416, by rfl⟩ : syracuseStep 2288555 = 3432833) B3432833
theorem B1567675 : Blo 1524459 1567675 := bstep (se 1 (by rfl) ⟨1175756, by rfl⟩ : syracuseStep 1567675 = 2351513) B2351513
theorem B2288585 : Blo 1524459 2288585 := bstep (se 2 (by rfl) ⟨858219, by rfl⟩ : syracuseStep 2288585 = 1716439) B1716439
theorem B7719947 : Blo 1524459 7719947 := bstep (se 1 (by rfl) ⟨5789960, by rfl⟩ : syracuseStep 7719947 = 11579921) B11579921
theorem B1715215 : Blo 1524459 1715215 := bstep (se 1 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 1715215 = 2572823) B2572823
theorem B6515741 : Blo 1524459 6515741 := bstep (se 3 (by rfl) ⟨1221701, by rfl⟩ : syracuseStep 6515741 = 2443403) B2443403
theorem B2288699 : Blo 1524459 2288699 := bstep (se 1 (by rfl) ⟨1716524, by rfl⟩ : syracuseStep 2288699 = 3433049) B3433049
theorem B2288759 : Blo 1524459 2288759 := bstep (se 1 (by rfl) ⟨1716569, by rfl⟩ : syracuseStep 2288759 = 3433139) B3433139
theorem B2288783 : Blo 1524459 2288783 := bstep (se 1 (by rfl) ⟨1716587, by rfl⟩ : syracuseStep 2288783 = 3433175) B3433175
theorem B7720109 : Blo 1524459 7720109 := bstep (se 3 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 7720109 = 2895041) B2895041
theorem B2288825 : Blo 1524459 2288825 := bstep (se 2 (by rfl) ⟨858309, by rfl⟩ : syracuseStep 2288825 = 1716619) B1716619
theorem B4181177 : Blo 1524459 4181177 := bstep (se 2 (by rfl) ⟨1567941, by rfl⟩ : syracuseStep 4181177 = 3135883) B3135883
theorem B2288903 : Blo 1524459 2288903 := bstep (se 1 (by rfl) ⟨1716677, by rfl⟩ : syracuseStep 2288903 = 3433355) B3433355
theorem B4345103 : Blo 1524459 4345103 := bstep (se 1 (by rfl) ⟨3258827, by rfl⟩ : syracuseStep 4345103 = 6517655) B6517655
theorem B2575631 : Blo 1524459 2575631 := bstep (se 1 (by rfl) ⟨1931723, by rfl⟩ : syracuseStep 2575631 = 3863447) B3863447
theorem B2288939 : Blo 1524459 2288939 := bstep (se 1 (by rfl) ⟨1716704, by rfl⟩ : syracuseStep 2288939 = 3433409) B3433409
theorem B29330747 : Blo 1524459 29330747 := bstep (se 1 (by rfl) ⟨21998060, by rfl⟩ : syracuseStep 29330747 = 43996121) B43996121
theorem B1740091 : Blo 1524459 1740091 := bstep (se 1 (by rfl) ⟨1305068, by rfl⟩ : syracuseStep 1740091 = 2610137) B2610137
theorem B2288969 : Blo 1524459 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B2895239 : Blo 1524459 2895239 := bstep (se 1 (by rfl) ⟨2171429, by rfl⟩ : syracuseStep 2895239 = 4342859) B4342859
theorem B4885895 : Blo 1524459 4885895 := bstep (se 1 (by rfl) ⟨3664421, by rfl⟩ : syracuseStep 4885895 = 7328843) B7328843
theorem B3665287 : Blo 1524459 3665287 := bstep (se 1 (by rfl) ⟨2748965, by rfl⟩ : syracuseStep 3665287 = 5497931) B5497931
theorem B7933369 : Blo 1524459 7933369 := bstep (se 2 (by rfl) ⟨2975013, by rfl⟩ : syracuseStep 7933369 = 5950027) B5950027
theorem B5148089 : Blo 1524459 5148089 := bstep (se 2 (by rfl) ⟨1930533, by rfl⟩ : syracuseStep 5148089 = 3861067) B3861067
theorem B2289083 : Blo 1524459 2289083 := bstep (se 1 (by rfl) ⟨1716812, by rfl⟩ : syracuseStep 2289083 = 3433625) B3433625
theorem B2289143 : Blo 1524459 2289143 := bstep (se 1 (by rfl) ⟨1716857, by rfl⟩ : syracuseStep 2289143 = 3433715) B3433715
theorem B1715719 : Blo 1524459 1715719 := bstep (se 1 (by rfl) ⟨1286789, by rfl⟩ : syracuseStep 1715719 = 2573579) B2573579
theorem B2289167 : Blo 1524459 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B2289209 : Blo 1524459 2289209 := bstep (se 2 (by rfl) ⟨858453, by rfl⟩ : syracuseStep 2289209 = 1716907) B1716907
theorem B3862151 : Blo 1524459 3862151 := bstep (se 1 (by rfl) ⟨2896613, by rfl⟩ : syracuseStep 3862151 = 5793227) B5793227
theorem B2289287 : Blo 1524459 2289287 := bstep (se 1 (by rfl) ⟨1716965, by rfl⟩ : syracuseStep 2289287 = 3433931) B3433931
theorem B2289323 : Blo 1524459 2289323 := bstep (se 1 (by rfl) ⟨1716992, by rfl⟩ : syracuseStep 2289323 = 3433985) B3433985
theorem B3862201 : Blo 1524459 3862201 := bstep (se 2 (by rfl) ⟨1448325, by rfl⟩ : syracuseStep 3862201 = 2896651) B2896651
theorem B1715899 : Blo 1524459 1715899 := bstep (se 1 (by rfl) ⟨1286924, by rfl⟩ : syracuseStep 1715899 = 2573849) B2573849
theorem B2289353 : Blo 1524459 2289353 := bstep (se 2 (by rfl) ⟨858507, by rfl⟩ : syracuseStep 2289353 = 1717015) B1717015
theorem B5869313 : Blo 1524459 5869313 := bstep (se 2 (by rfl) ⟨2200992, by rfl⟩ : syracuseStep 5869313 = 4401985) B4401985
theorem B14659379 : Blo 1524459 14659379 := bstep (se 1 (by rfl) ⟨10994534, by rfl⟩ : syracuseStep 14659379 = 21989069) B21989069
theorem B2289467 : Blo 1524459 2289467 := bstep (se 1 (by rfl) ⟨1717100, by rfl⟩ : syracuseStep 2289467 = 3434201) B3434201
theorem B2289527 : Blo 1524459 2289527 := bstep (se 1 (by rfl) ⟨1717145, by rfl⟩ : syracuseStep 2289527 = 3434291) B3434291
theorem B2289551 : Blo 1524459 2289551 := bstep (se 1 (by rfl) ⟨1717163, by rfl⟩ : syracuseStep 2289551 = 3434327) B3434327
theorem B2895763 : Blo 1524459 2895763 := bstep (se 1 (by rfl) ⟨2171822, by rfl⟩ : syracuseStep 2895763 = 4343645) B4343645
theorem B2289593 : Blo 1524459 2289593 := bstep (se 2 (by rfl) ⟨858597, by rfl⟩ : syracuseStep 2289593 = 1717195) B1717195
theorem B2289671 : Blo 1524459 2289671 := bstep (se 1 (by rfl) ⟨1717253, by rfl⟩ : syracuseStep 2289671 = 3434507) B3434507
theorem B5148683 : Blo 1524459 5148683 := bstep (se 1 (by rfl) ⟨3861512, by rfl⟩ : syracuseStep 5148683 = 7723025) B7723025
theorem B6271019 : Blo 1524459 6271019 := bstep (se 1 (by rfl) ⟨4703264, by rfl⟩ : syracuseStep 6271019 = 9406529) B9406529
theorem B5148791 : Blo 1524459 5148791 := bstep (se 1 (by rfl) ⟨3861593, by rfl⟩ : syracuseStep 5148791 = 7723187) B7723187
theorem B1716367 : Blo 1524459 1716367 := bstep (se 1 (by rfl) ⟨1287275, by rfl⟩ : syracuseStep 1716367 = 2574551) B2574551
theorem B3862799 : Blo 1524459 3862799 := bstep (se 1 (by rfl) ⟨2897099, by rfl⟩ : syracuseStep 3862799 = 5794199) B5794199
theorem B3256777 : Blo 1524459 3256777 := bstep (se 2 (by rfl) ⟨1221291, by rfl⟩ : syracuseStep 3256777 = 2442583) B2442583
theorem B8688131 : Blo 1524459 8688131 := bstep (se 1 (by rfl) ⟨6516098, by rfl⟩ : syracuseStep 8688131 = 13032197) B13032197
theorem B46969379 : Blo 1524459 46969379 := bstep (se 1 (by rfl) ⟨35227034, by rfl⟩ : syracuseStep 46969379 = 70454069) B70454069
theorem B1716871 : Blo 1524459 1716871 := bstep (se 1 (by rfl) ⟨1287653, by rfl⟩ : syracuseStep 1716871 = 2575307) B2575307
theorem B26047169 : Blo 1524459 26047169 := bstep (se 2 (by rfl) ⟨9767688, by rfl⟩ : syracuseStep 26047169 = 19535377) B19535377
theorem B5149385 : Blo 1524459 5149385 := bstep (se 2 (by rfl) ⟨1931019, by rfl⟩ : syracuseStep 5149385 = 3862039) B3862039
theorem B20861657 : Blo 1524459 20861657 := bstep (se 2 (by rfl) ⟨7823121, by rfl⟩ : syracuseStep 20861657 = 15646243) B15646243
theorem B7721729 : Blo 1524459 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B1717051 : Blo 1524459 1717051 := bstep (se 1 (by rfl) ⟨1287788, by rfl⟩ : syracuseStep 1717051 = 2575577) B2575577
theorem B4346743 : Blo 1524459 4346743 := bstep (se 1 (by rfl) ⟨3260057, by rfl⟩ : syracuseStep 4346743 = 6520115) B6520115
theorem B3715975 : Blo 1524459 3715975 := bstep (se 1 (by rfl) ⟨2786981, by rfl⟩ : syracuseStep 3715975 = 5573963) B5573963
theorem B4346777 : Blo 1524459 4346777 := bstep (se 2 (by rfl) ⟨1630041, by rfl⟩ : syracuseStep 4346777 = 3260083) B3260083
theorem B3863497 : Blo 1524459 3863497 := bstep (se 2 (by rfl) ⟨1448811, by rfl⟩ : syracuseStep 3863497 = 2897623) B2897623
theorem B3666959 : Blo 1524459 3666959 := bstep (se 1 (by rfl) ⟨2750219, by rfl⟩ : syracuseStep 3666959 = 5500439) B5500439
theorem B2896955 : Blo 1524459 2896955 := bstep (se 1 (by rfl) ⟨2172716, by rfl⟩ : syracuseStep 2896955 = 4345433) B4345433
theorem B11588669 : Blo 1524459 11588669 := bstep (se 3 (by rfl) ⟨2172875, by rfl⟩ : syracuseStep 11588669 = 4345751) B4345751
theorem B3863639 : Blo 1524459 3863639 := bstep (se 1 (by rfl) ⟨2897729, by rfl⟩ : syracuseStep 3863639 = 5795459) B5795459
theorem B26055917 : Blo 1524459 26055917 := bstep (se 3 (by rfl) ⟨4885484, by rfl⟩ : syracuseStep 26055917 = 9770969) B9770969
theorem B5150087 : Blo 1524459 5150087 := bstep (se 1 (by rfl) ⟨3862565, by rfl⟩ : syracuseStep 5150087 = 7725131) B7725131
theorem B29324753 : Blo 1524459 29324753 := bstep (se 2 (by rfl) ⟨10996782, by rfl⟩ : syracuseStep 29324753 = 21993565) B21993565
theorem B17380817 : Blo 1524459 17380817 := bstep (se 2 (by rfl) ⟨6517806, by rfl⟩ : syracuseStep 17380817 = 13035613) B13035613
theorem B11580893 : Blo 1524459 11580893 := bstep (se 3 (by rfl) ⟨2171417, by rfl⟩ : syracuseStep 11580893 = 4342835) B4342835
theorem B2897441 : Blo 1524459 2897441 := bstep (se 2 (by rfl) ⟨1086540, by rfl⟩ : syracuseStep 2897441 = 2173081) B2173081
theorem B7722539 : Blo 1524459 7722539 := bstep (se 1 (by rfl) ⟨5791904, by rfl⟩ : syracuseStep 7722539 = 11583809) B11583809
theorem B6518339 : Blo 1524459 6518339 := bstep (se 1 (by rfl) ⟨4888754, by rfl⟩ : syracuseStep 6518339 = 9777509) B9777509
theorem B4888151 : Blo 1524459 4888151 := bstep (se 1 (by rfl) ⟨3666113, by rfl⟩ : syracuseStep 4888151 = 7332227) B7332227
theorem B5150465 : Blo 1524459 5150465 := bstep (se 2 (by rfl) ⟨1931424, by rfl⟩ : syracuseStep 5150465 = 3862849) B3862849
theorem B3430187 : Blo 1524459 3430187 := bstep (se 1 (by rfl) ⟨2572640, by rfl⟩ : syracuseStep 3430187 = 5145281) B5145281
theorem B2897707 : Blo 1524459 2897707 := bstep (se 1 (by rfl) ⟨2173280, by rfl⟩ : syracuseStep 2897707 = 4346561) B4346561
theorem B6518663 : Blo 1524459 6518663 := bstep (se 1 (by rfl) ⟨4888997, by rfl⟩ : syracuseStep 6518663 = 9777995) B9777995
theorem B1628047 : Blo 1524459 1628047 := bstep (se 1 (by rfl) ⟨1221035, by rfl⟩ : syracuseStep 1628047 = 2442071) B2442071
theorem B3913787 : Blo 1524459 3913787 := bstep (se 1 (by rfl) ⟨2935340, by rfl⟩ : syracuseStep 3913787 = 5870681) B5870681
theorem B3430547 : Blo 1524459 3430547 := bstep (se 1 (by rfl) ⟨2572910, by rfl⟩ : syracuseStep 3430547 = 5145821) B5145821
theorem B3430601 : Blo 1524459 3430601 := bstep (se 2 (by rfl) ⟨1286475, by rfl⟩ : syracuseStep 3430601 = 2572951) B2572951
theorem B13383917 : Blo 1524459 13383917 := bstep (se 3 (by rfl) ⟨2509484, by rfl⟩ : syracuseStep 13383917 = 5018969) B5018969
theorem B1833259 : Blo 1524459 1833259 := bstep (se 1 (by rfl) ⟨1374944, by rfl⟩ : syracuseStep 1833259 = 2749889) B2749889
theorem B4889099 : Blo 1524459 4889099 := bstep (se 1 (by rfl) ⟨3666824, by rfl⟩ : syracuseStep 4889099 = 7333649) B7333649
theorem B5151275 : Blo 1524459 5151275 := bstep (se 1 (by rfl) ⟨3863456, by rfl⟩ : syracuseStep 5151275 = 7726913) B7726913
theorem B4020851 : Blo 1524459 4020851 := bstep (se 1 (by rfl) ⟨3015638, by rfl⟩ : syracuseStep 4020851 = 6031277) B6031277
theorem B2062967 : Blo 1524459 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B8682299 : Blo 1524459 8682299 := bstep (se 1 (by rfl) ⟨6511724, by rfl⟩ : syracuseStep 8682299 = 13023449) B13023449
theorem B7723835 : Blo 1524459 7723835 := bstep (se 1 (by rfl) ⟨5792876, by rfl⟩ : syracuseStep 7723835 = 11585753) B11585753
theorem B1833787 : Blo 1524459 1833787 := bstep (se 1 (by rfl) ⟨1375340, by rfl⟩ : syracuseStep 1833787 = 2750681) B2750681
theorem B3431303 : Blo 1524459 3431303 := bstep (se 1 (by rfl) ⟨2573477, by rfl⟩ : syracuseStep 3431303 = 5146955) B5146955
theorem B5790599 : Blo 1524459 5790599 := bstep (se 1 (by rfl) ⟨4342949, by rfl⟩ : syracuseStep 5790599 = 8685899) B8685899
theorem B7723997 : Blo 1524459 7723997 := bstep (se 3 (by rfl) ⟨1448249, by rfl⟩ : syracuseStep 7723997 = 2896499) B2896499
theorem B3431483 : Blo 1524459 3431483 := bstep (se 1 (by rfl) ⟨2573612, by rfl⟩ : syracuseStep 3431483 = 5147225) B5147225
theorem B3259511 : Blo 1524459 3259511 := bstep (se 1 (by rfl) ⟨2444633, by rfl⟩ : syracuseStep 3259511 = 4889267) B4889267
theorem B3431609 : Blo 1524459 3431609 := bstep (se 2 (by rfl) ⟨1286853, by rfl⟩ : syracuseStep 3431609 = 2573707) B2573707
theorem B7724321 : Blo 1524459 7724321 := bstep (se 2 (by rfl) ⟨2896620, by rfl⟩ : syracuseStep 7724321 = 5793241) B5793241
theorem B41729539 : Blo 1524459 41729539 := bstep (se 1 (by rfl) ⟨31297154, by rfl⟩ : syracuseStep 41729539 = 62594309) B62594309
theorem B9272843 : Blo 1524459 9272843 := bstep (se 1 (by rfl) ⟨6954632, by rfl⟩ : syracuseStep 9272843 = 13909265) B13909265
theorem B3431951 : Blo 1524459 3431951 := bstep (se 1 (by rfl) ⟨2573963, by rfl⟩ : syracuseStep 3431951 = 5147927) B5147927
theorem B3431969 : Blo 1524459 3431969 := bstep (se 2 (by rfl) ⟨1286988, by rfl⟩ : syracuseStep 3431969 = 2573977) B2573977
theorem B3259963 : Blo 1524459 3259963 := bstep (se 1 (by rfl) ⟨2444972, by rfl⟩ : syracuseStep 3259963 = 4889945) B4889945
theorem B4341401 : Blo 1524459 4341401 := bstep (se 2 (by rfl) ⟨1628025, by rfl⟩ : syracuseStep 4341401 = 3256051) B3256051
theorem B21978803 : Blo 1524459 21978803 := bstep (se 1 (by rfl) ⟨16484102, by rfl⟩ : syracuseStep 21978803 = 32968205) B32968205
theorem B8683301 : Blo 1524459 8683301 := bstep (se 4 (by rfl) ⟨814059, by rfl⟩ : syracuseStep 8683301 = 1628119) B1628119
theorem B9912179 : Blo 1524459 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B3432311 : Blo 1524459 3432311 := bstep (se 1 (by rfl) ⟨2574233, by rfl⟩ : syracuseStep 3432311 = 5148467) B5148467
theorem B3432455 : Blo 1524459 3432455 := bstep (se 1 (by rfl) ⟨2574341, by rfl⟩ : syracuseStep 3432455 = 5148683) B5148683
theorem B3432527 : Blo 1524459 3432527 := bstep (se 1 (by rfl) ⟨2574395, by rfl⟩ : syracuseStep 3432527 = 5148791) B5148791
theorem B5792087 : Blo 1524459 5792087 := bstep (se 1 (by rfl) ⟨4344065, by rfl⟩ : syracuseStep 5792087 = 8688131) B8688131
theorem B3432923 : Blo 1524459 3432923 := bstep (se 1 (by rfl) ⟨2574692, by rfl⟩ : syracuseStep 3432923 = 5149385) B5149385
theorem B11149805 : Blo 1524459 11149805 := bstep (se 3 (by rfl) ⟨2090588, by rfl⟩ : syracuseStep 11149805 = 4181177) B4181177
theorem B22282775 : Blo 1524459 22282775 := bstep (se 1 (by rfl) ⟨16712081, by rfl⟩ : syracuseStep 22282775 = 33424163) B33424163
theorem B4342369 : Blo 1524459 4342369 := bstep (se 2 (by rfl) ⟨1628388, by rfl⟩ : syracuseStep 4342369 = 3256777) B3256777
theorem B5145227 : Blo 1524459 5145227 := bstep (se 1 (by rfl) ⟨3858920, by rfl⟩ : syracuseStep 5145227 = 7717841) B7717841
theorem B7725779 : Blo 1524459 7725779 := bstep (se 1 (by rfl) ⟨5794334, by rfl⟩ : syracuseStep 7725779 = 11588669) B11588669
theorem B1524519 : Blo 1524459 1524519 := bstep (se 1 (by rfl) ⟨1143389, by rfl⟩ : syracuseStep 1524519 = 2286779) B2286779
theorem B1524559 : Blo 1524459 1524559 := bstep (se 1 (by rfl) ⟨1143419, by rfl⟩ : syracuseStep 1524559 = 2286839) B2286839
theorem B1524575 : Blo 1524459 1524575 := bstep (se 1 (by rfl) ⟨1143431, by rfl⟩ : syracuseStep 1524575 = 2286863) B2286863
theorem B1524603 : Blo 1524459 1524603 := bstep (se 1 (by rfl) ⟨1143452, by rfl⟩ : syracuseStep 1524603 = 2286905) B2286905
theorem B1524655 : Blo 1524459 1524655 := bstep (se 1 (by rfl) ⟨1143491, by rfl⟩ : syracuseStep 1524655 = 2286983) B2286983
theorem B3433391 : Blo 1524459 3433391 := bstep (se 1 (by rfl) ⟨2575043, by rfl⟩ : syracuseStep 3433391 = 5150087) B5150087
theorem B1524679 : Blo 1524459 1524679 := bstep (se 1 (by rfl) ⟨1143509, by rfl⟩ : syracuseStep 1524679 = 2287019) B2287019
theorem B1524699 : Blo 1524459 1524699 := bstep (se 1 (by rfl) ⟨1143524, by rfl⟩ : syracuseStep 1524699 = 2287049) B2287049
theorem B2573275 : Blo 1524459 2573275 := bstep (se 1 (by rfl) ⟨1929956, by rfl⟩ : syracuseStep 2573275 = 3859913) B3859913
theorem B1524775 : Blo 1524459 1524775 := bstep (se 1 (by rfl) ⟨1143581, by rfl⟩ : syracuseStep 1524775 = 2287163) B2287163
theorem B1524815 : Blo 1524459 1524815 := bstep (se 1 (by rfl) ⟨1143611, by rfl⟩ : syracuseStep 1524815 = 2287223) B2287223
theorem B1524831 : Blo 1524459 1524831 := bstep (se 1 (by rfl) ⟨1143623, by rfl⟩ : syracuseStep 1524831 = 2287247) B2287247
theorem B1524859 : Blo 1524459 1524859 := bstep (se 1 (by rfl) ⟨1143644, by rfl⟩ : syracuseStep 1524859 = 2287289) B2287289
theorem B3433643 : Blo 1524459 3433643 := bstep (se 1 (by rfl) ⟨2575232, by rfl⟩ : syracuseStep 3433643 = 5150465) B5150465
theorem B1524911 : Blo 1524459 1524911 := bstep (se 1 (by rfl) ⟨1143683, by rfl⟩ : syracuseStep 1524911 = 2287367) B2287367
theorem B2286791 : Blo 1524459 2286791 := bstep (se 1 (by rfl) ⟨1715093, by rfl⟩ : syracuseStep 2286791 = 3430187) B3430187
theorem B1524935 : Blo 1524459 1524935 := bstep (se 1 (by rfl) ⟨1143701, by rfl⟩ : syracuseStep 1524935 = 2287403) B2287403
theorem B1524955 : Blo 1524459 1524955 := bstep (se 1 (by rfl) ⟨1143716, by rfl⟩ : syracuseStep 1524955 = 2287433) B2287433
theorem B2090233 : Blo 1524459 2090233 := bstep (se 2 (by rfl) ⟨783837, by rfl⟩ : syracuseStep 2090233 = 1567675) B1567675
theorem B1525031 : Blo 1524459 1525031 := bstep (se 1 (by rfl) ⟨1143773, by rfl⟩ : syracuseStep 1525031 = 2287547) B2287547
theorem B1525071 : Blo 1524459 1525071 := bstep (se 1 (by rfl) ⟨1143803, by rfl⟩ : syracuseStep 1525071 = 2287607) B2287607
theorem B1525087 : Blo 1524459 1525087 := bstep (se 1 (by rfl) ⟨1143815, by rfl⟩ : syracuseStep 1525087 = 2287631) B2287631
theorem B2286953 : Blo 1524459 2286953 := bstep (se 2 (by rfl) ⟨857607, by rfl⟩ : syracuseStep 2286953 = 1715215) B1715215
theorem B1525115 : Blo 1524459 1525115 := bstep (se 1 (by rfl) ⟨1143836, by rfl⟩ : syracuseStep 1525115 = 2287673) B2287673
theorem B4638077 : Blo 1524459 4638077 := bstep (se 3 (by rfl) ⟨869639, by rfl⟩ : syracuseStep 4638077 = 1739279) B1739279
theorem B54273445 : Blo 1524459 54273445 := bstep (se 4 (by rfl) ⟨5088135, by rfl⟩ : syracuseStep 54273445 = 10176271) B10176271
theorem B1525167 : Blo 1524459 1525167 := bstep (se 1 (by rfl) ⟨1143875, by rfl⟩ : syracuseStep 1525167 = 2287751) B2287751
theorem B2287031 : Blo 1524459 2287031 := bstep (se 1 (by rfl) ⟨1715273, by rfl⟩ : syracuseStep 2287031 = 3430547) B3430547
theorem B1525191 : Blo 1524459 1525191 := bstep (se 1 (by rfl) ⟨1143893, by rfl⟩ : syracuseStep 1525191 = 2287787) B2287787
theorem B2287067 : Blo 1524459 2287067 := bstep (se 1 (by rfl) ⟨1715300, by rfl⟩ : syracuseStep 2287067 = 3430601) B3430601
theorem B1525211 : Blo 1524459 1525211 := bstep (se 1 (by rfl) ⟨1143908, by rfl⟩ : syracuseStep 1525211 = 2287817) B2287817
theorem B8922611 : Blo 1524459 8922611 := bstep (se 1 (by rfl) ⟨6691958, by rfl⟩ : syracuseStep 8922611 = 13383917) B13383917
theorem B5146145 : Blo 1524459 5146145 := bstep (se 2 (by rfl) ⟨1929804, by rfl⟩ : syracuseStep 5146145 = 3859609) B3859609
theorem B1525287 : Blo 1524459 1525287 := bstep (se 1 (by rfl) ⟨1143965, by rfl⟩ : syracuseStep 1525287 = 2287931) B2287931
theorem B2573903 : Blo 1524459 2573903 := bstep (se 1 (by rfl) ⟨1930427, by rfl⟩ : syracuseStep 2573903 = 3860855) B3860855
theorem B1525327 : Blo 1524459 1525327 := bstep (se 1 (by rfl) ⟨1143995, by rfl⟩ : syracuseStep 1525327 = 2287991) B2287991
theorem B1525343 : Blo 1524459 1525343 := bstep (se 1 (by rfl) ⟨1144007, by rfl⟩ : syracuseStep 1525343 = 2288015) B2288015
theorem B1525371 : Blo 1524459 1525371 := bstep (se 1 (by rfl) ⟨1144028, by rfl⟩ : syracuseStep 1525371 = 2288057) B2288057
theorem B1525423 : Blo 1524459 1525423 := bstep (se 1 (by rfl) ⟨1144067, by rfl⟩ : syracuseStep 1525423 = 2288135) B2288135
theorem B1525447 : Blo 1524459 1525447 := bstep (se 1 (by rfl) ⟨1144085, by rfl⟩ : syracuseStep 1525447 = 2288171) B2288171
theorem B3434183 : Blo 1524459 3434183 := bstep (se 1 (by rfl) ⟨2575637, by rfl⟩ : syracuseStep 3434183 = 5151275) B5151275
theorem B1525467 : Blo 1524459 1525467 := bstep (se 1 (by rfl) ⟨1144100, by rfl⟩ : syracuseStep 1525467 = 2288201) B2288201
theorem B5146361 : Blo 1524459 5146361 := bstep (se 2 (by rfl) ⟨1929885, by rfl⟩ : syracuseStep 5146361 = 3859771) B3859771
theorem B2320121 : Blo 1524459 2320121 := bstep (se 2 (by rfl) ⟨870045, by rfl⟩ : syracuseStep 2320121 = 1740091) B1740091
theorem B1525543 : Blo 1524459 1525543 := bstep (se 1 (by rfl) ⟨1144157, by rfl⟩ : syracuseStep 1525543 = 2288315) B2288315
theorem B1525583 : Blo 1524459 1525583 := bstep (se 1 (by rfl) ⟨1144187, by rfl⟩ : syracuseStep 1525583 = 2288375) B2288375
theorem B1525599 : Blo 1524459 1525599 := bstep (se 1 (by rfl) ⟨1144199, by rfl⟩ : syracuseStep 1525599 = 2288399) B2288399
theorem B2443115 : Blo 1524459 2443115 := bstep (se 1 (by rfl) ⟨1832336, by rfl⟩ : syracuseStep 2443115 = 3664673) B3664673
theorem B1525627 : Blo 1524459 1525627 := bstep (se 1 (by rfl) ⟨1144220, by rfl⟩ : syracuseStep 1525627 = 2288441) B2288441
theorem B10577825 : Blo 1524459 10577825 := bstep (se 2 (by rfl) ⟨3966684, by rfl⟩ : syracuseStep 10577825 = 7933369) B7933369
theorem B2287535 : Blo 1524459 2287535 := bstep (se 1 (by rfl) ⟨1715651, by rfl⟩ : syracuseStep 2287535 = 3431303) B3431303
theorem B3860399 : Blo 1524459 3860399 := bstep (se 1 (by rfl) ⟨2895299, by rfl⟩ : syracuseStep 3860399 = 5790599) B5790599
theorem B1525679 : Blo 1524459 1525679 := bstep (se 1 (by rfl) ⟨1144259, by rfl⟩ : syracuseStep 1525679 = 2288519) B2288519
theorem B1525703 : Blo 1524459 1525703 := bstep (se 1 (by rfl) ⟨1144277, by rfl⟩ : syracuseStep 1525703 = 2288555) B2288555
theorem B1525723 : Blo 1524459 1525723 := bstep (se 1 (by rfl) ⟨1144292, by rfl⟩ : syracuseStep 1525723 = 2288585) B2288585
theorem B5146631 : Blo 1524459 5146631 := bstep (se 1 (by rfl) ⟨3859973, by rfl⟩ : syracuseStep 5146631 = 7719947) B7719947
theorem B2287625 : Blo 1524459 2287625 := bstep (se 2 (by rfl) ⟨857859, by rfl⟩ : syracuseStep 2287625 = 1715719) B1715719
theorem B4343827 : Blo 1524459 4343827 := bstep (se 1 (by rfl) ⟨3257870, by rfl⟩ : syracuseStep 4343827 = 6515741) B6515741
theorem B19818533 : Blo 1524459 19818533 := bstep (se 4 (by rfl) ⟨1857987, by rfl⟩ : syracuseStep 19818533 = 3715975) B3715975
theorem B2287655 : Blo 1524459 2287655 := bstep (se 1 (by rfl) ⟨1715741, by rfl⟩ : syracuseStep 2287655 = 3431483) B3431483
theorem B1525799 : Blo 1524459 1525799 := bstep (se 1 (by rfl) ⟨1144349, by rfl⟩ : syracuseStep 1525799 = 2288699) B2288699
theorem B1525839 : Blo 1524459 1525839 := bstep (se 1 (by rfl) ⟨1144379, by rfl⟩ : syracuseStep 1525839 = 2288759) B2288759
theorem B2173007 : Blo 1524459 2173007 := bstep (se 1 (by rfl) ⟨1629755, by rfl⟩ : syracuseStep 2173007 = 3259511) B3259511
theorem B1525855 : Blo 1524459 1525855 := bstep (se 1 (by rfl) ⟨1144391, by rfl⟩ : syracuseStep 1525855 = 2288783) B2288783
theorem B5146739 : Blo 1524459 5146739 := bstep (se 1 (by rfl) ⟨3860054, by rfl⟩ : syracuseStep 5146739 = 7720109) B7720109
theorem B2287739 : Blo 1524459 2287739 := bstep (se 1 (by rfl) ⟨1715804, by rfl⟩ : syracuseStep 2287739 = 3431609) B3431609
theorem B1525883 : Blo 1524459 1525883 := bstep (se 1 (by rfl) ⟨1144412, by rfl⟩ : syracuseStep 1525883 = 2288825) B2288825
theorem B1525935 : Blo 1524459 1525935 := bstep (se 1 (by rfl) ⟨1144451, by rfl⟩ : syracuseStep 1525935 = 2288903) B2288903
theorem B1525959 : Blo 1524459 1525959 := bstep (se 1 (by rfl) ⟨1144469, by rfl⟩ : syracuseStep 1525959 = 2288939) B2288939
theorem B1525979 : Blo 1524459 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B2287865 : Blo 1524459 2287865 := bstep (se 2 (by rfl) ⟨857949, by rfl⟩ : syracuseStep 2287865 = 1715899) B1715899
theorem B1526055 : Blo 1524459 1526055 := bstep (se 1 (by rfl) ⟨1144541, by rfl⟩ : syracuseStep 1526055 = 2289083) B2289083
theorem B63473969 : Blo 1524459 63473969 := bstep (se 2 (by rfl) ⟨23802738, by rfl⟩ : syracuseStep 63473969 = 47605477) B47605477
theorem B6515005 : Blo 1524459 6515005 := bstep (se 3 (by rfl) ⟨1221563, by rfl⟩ : syracuseStep 6515005 = 2443127) B2443127
theorem B1526095 : Blo 1524459 1526095 := bstep (se 1 (by rfl) ⟨1144571, by rfl⟩ : syracuseStep 1526095 = 2289143) B2289143
theorem B2287967 : Blo 1524459 2287967 := bstep (se 1 (by rfl) ⟨1715975, by rfl⟩ : syracuseStep 2287967 = 3431951) B3431951
theorem B1526111 : Blo 1524459 1526111 := bstep (se 1 (by rfl) ⟨1144583, by rfl⟩ : syracuseStep 1526111 = 2289167) B2289167
theorem B2287979 : Blo 1524459 2287979 := bstep (se 1 (by rfl) ⟨1715984, by rfl⟩ : syracuseStep 2287979 = 3431969) B3431969
theorem B1526139 : Blo 1524459 1526139 := bstep (se 1 (by rfl) ⟨1144604, by rfl⟩ : syracuseStep 1526139 = 2289209) B2289209
theorem B5147009 : Blo 1524459 5147009 := bstep (se 2 (by rfl) ⟨1930128, by rfl⟩ : syracuseStep 5147009 = 3860257) B3860257
theorem B2574767 : Blo 1524459 2574767 := bstep (se 1 (by rfl) ⟨1931075, by rfl⟩ : syracuseStep 2574767 = 3862151) B3862151
theorem B1526191 : Blo 1524459 1526191 := bstep (se 1 (by rfl) ⟨1144643, by rfl⟩ : syracuseStep 1526191 = 2289287) B2289287
theorem B2894267 : Blo 1524459 2894267 := bstep (se 1 (by rfl) ⟨2170700, by rfl⟩ : syracuseStep 2894267 = 4341401) B4341401
theorem B1526215 : Blo 1524459 1526215 := bstep (se 1 (by rfl) ⟨1144661, by rfl⟩ : syracuseStep 1526215 = 2289323) B2289323
theorem B1526235 : Blo 1524459 1526235 := bstep (se 1 (by rfl) ⟨1144676, by rfl⟩ : syracuseStep 1526235 = 2289353) B2289353
theorem B3861017 : Blo 1524459 3861017 := bstep (se 2 (by rfl) ⟨1447881, by rfl⟩ : syracuseStep 3861017 = 2895763) B2895763
theorem B1526311 : Blo 1524459 1526311 := bstep (se 1 (by rfl) ⟨1144733, by rfl⟩ : syracuseStep 1526311 = 2289467) B2289467
theorem B2288207 : Blo 1524459 2288207 := bstep (se 1 (by rfl) ⟨1716155, by rfl⟩ : syracuseStep 2288207 = 3432311) B3432311
theorem B1526351 : Blo 1524459 1526351 := bstep (se 1 (by rfl) ⟨1144763, by rfl⟩ : syracuseStep 1526351 = 2289527) B2289527
theorem B1526367 : Blo 1524459 1526367 := bstep (se 1 (by rfl) ⟨1144775, by rfl⟩ : syracuseStep 1526367 = 2289551) B2289551
theorem B1526395 : Blo 1524459 1526395 := bstep (se 1 (by rfl) ⟨1144796, by rfl⟩ : syracuseStep 1526395 = 2289593) B2289593
theorem B1526447 : Blo 1524459 1526447 := bstep (se 1 (by rfl) ⟨1144835, by rfl⟩ : syracuseStep 1526447 = 2289671) B2289671
theorem B2288327 : Blo 1524459 2288327 := bstep (se 1 (by rfl) ⟨1716245, by rfl⟩ : syracuseStep 2288327 = 3432491) B3432491
theorem B4180679 : Blo 1524459 4180679 := bstep (se 1 (by rfl) ⟨3135509, by rfl⟩ : syracuseStep 4180679 = 6271019) B6271019
theorem B19540709 : Blo 1524459 19540709 := bstep (se 4 (by rfl) ⟨1831941, by rfl⟩ : syracuseStep 19540709 = 3663883) B3663883
theorem B5573369 : Blo 1524459 5573369 := bstep (se 2 (by rfl) ⟨2090013, by rfl⟩ : syracuseStep 5573369 = 4180027) B4180027
theorem B2575199 : Blo 1524459 2575199 := bstep (se 1 (by rfl) ⟨1931399, by rfl⟩ : syracuseStep 2575199 = 3862799) B3862799
theorem B2288489 : Blo 1524459 2288489 := bstep (se 2 (by rfl) ⟨858183, by rfl⟩ : syracuseStep 2288489 = 1716367) B1716367
theorem B2747279 : Blo 1524459 2747279 := bstep (se 1 (by rfl) ⟨2060459, by rfl⟩ : syracuseStep 2747279 = 4120919) B4120919
theorem B2894753 : Blo 1524459 2894753 := bstep (se 2 (by rfl) ⟨1085532, by rfl⟩ : syracuseStep 2894753 = 2171065) B2171065
theorem B4885409 : Blo 1524459 4885409 := bstep (se 2 (by rfl) ⟨1832028, by rfl⟩ : syracuseStep 4885409 = 3664057) B3664057
theorem B2288567 : Blo 1524459 2288567 := bstep (se 1 (by rfl) ⟨1716425, by rfl⟩ : syracuseStep 2288567 = 3432851) B3432851
theorem B2288603 : Blo 1524459 2288603 := bstep (se 1 (by rfl) ⟨1716452, by rfl⟩ : syracuseStep 2288603 = 3432905) B3432905
theorem B31312919 : Blo 1524459 31312919 := bstep (se 1 (by rfl) ⟨23484689, by rfl⟩ : syracuseStep 31312919 = 46969379) B46969379
theorem B2444345 : Blo 1524459 2444345 := bstep (se 2 (by rfl) ⟨916629, by rfl⟩ : syracuseStep 2444345 = 1833259) B1833259
theorem B1715323 : Blo 1524459 1715323 := bstep (se 1 (by rfl) ⟨1286492, by rfl⟩ : syracuseStep 1715323 = 2572985) B2572985
theorem B5794973 : Blo 1524459 5794973 := bstep (se 3 (by rfl) ⟨1086557, by rfl⟩ : syracuseStep 5794973 = 2173115) B2173115
theorem B5147819 : Blo 1524459 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B2895095 : Blo 1524459 2895095 := bstep (se 1 (by rfl) ⟨2171321, by rfl⟩ : syracuseStep 2895095 = 4342643) B4342643
theorem B2444639 : Blo 1524459 2444639 := bstep (se 1 (by rfl) ⟨1833479, by rfl⟩ : syracuseStep 2444639 = 3666959) B3666959
theorem B2747791 : Blo 1524459 2747791 := bstep (se 1 (by rfl) ⟨2060843, by rfl⟩ : syracuseStep 2747791 = 4121687) B4121687
theorem B2575759 : Blo 1524459 2575759 := bstep (se 1 (by rfl) ⟨1931819, by rfl⟩ : syracuseStep 2575759 = 3863639) B3863639
theorem B2289071 : Blo 1524459 2289071 := bstep (se 1 (by rfl) ⟨1716803, by rfl⟩ : syracuseStep 2289071 = 3433607) B3433607
theorem B19819997 : Blo 1524459 19819997 := bstep (se 3 (by rfl) ⟨3716249, by rfl⟩ : syracuseStep 19819997 = 7432499) B7432499
theorem B17370611 : Blo 1524459 17370611 := bstep (se 1 (by rfl) ⟨13027958, by rfl⟩ : syracuseStep 17370611 = 26055917) B26055917
theorem B2289161 : Blo 1524459 2289161 := bstep (se 2 (by rfl) ⟨858435, by rfl⟩ : syracuseStep 2289161 = 1716871) B1716871
theorem B2289191 : Blo 1524459 2289191 := bstep (se 1 (by rfl) ⟨1716893, by rfl⟩ : syracuseStep 2289191 = 3433787) B3433787
theorem B9768509 : Blo 1524459 9768509 := bstep (se 3 (by rfl) ⟨1831595, by rfl⟩ : syracuseStep 9768509 = 3663191) B3663191
theorem B1715791 : Blo 1524459 1715791 := bstep (se 1 (by rfl) ⟨1286843, by rfl⟩ : syracuseStep 1715791 = 2573687) B2573687
theorem B12545623 : Blo 1524459 12545623 := bstep (se 1 (by rfl) ⟨9409217, by rfl⟩ : syracuseStep 12545623 = 18818435) B18818435
theorem B2289275 : Blo 1524459 2289275 := bstep (se 1 (by rfl) ⟨1716956, by rfl⟩ : syracuseStep 2289275 = 3433913) B3433913
theorem B24735365 : Blo 1524459 24735365 := bstep (se 4 (by rfl) ⟨2318940, by rfl⟩ : syracuseStep 24735365 = 4637881) B4637881
theorem B19549835 : Blo 1524459 19549835 := bstep (se 1 (by rfl) ⟨14662376, by rfl⟩ : syracuseStep 19549835 = 29324753) B29324753
theorem B11587211 : Blo 1524459 11587211 := bstep (se 1 (by rfl) ⟨8690408, by rfl⟩ : syracuseStep 11587211 = 17380817) B17380817
theorem B7720595 : Blo 1524459 7720595 := bstep (se 1 (by rfl) ⟨5790446, by rfl⟩ : syracuseStep 7720595 = 11580893) B11580893
theorem B5148359 : Blo 1524459 5148359 := bstep (se 1 (by rfl) ⟨3861269, by rfl⟩ : syracuseStep 5148359 = 7722539) B7722539
theorem B4345559 : Blo 1524459 4345559 := bstep (se 1 (by rfl) ⟨3259169, by rfl⟩ : syracuseStep 4345559 = 6518339) B6518339
theorem B2289401 : Blo 1524459 2289401 := bstep (se 2 (by rfl) ⟨858525, by rfl⟩ : syracuseStep 2289401 = 1717051) B1717051
theorem B2445049 : Blo 1524459 2445049 := bstep (se 2 (by rfl) ⟨916893, by rfl⟩ : syracuseStep 2445049 = 1833787) B1833787
theorem B5795657 : Blo 1524459 5795657 := bstep (se 2 (by rfl) ⟨2173371, by rfl⟩ : syracuseStep 5795657 = 4346743) B4346743
theorem B6958943 : Blo 1524459 6958943 := bstep (se 1 (by rfl) ⟨5219207, by rfl⟩ : syracuseStep 6958943 = 10438415) B10438415
theorem B2289503 : Blo 1524459 2289503 := bstep (se 1 (by rfl) ⟨1717127, by rfl⟩ : syracuseStep 2289503 = 3434255) B3434255
theorem B2289515 : Blo 1524459 2289515 := bstep (se 1 (by rfl) ⟨1717136, by rfl⟩ : syracuseStep 2289515 = 3434273) B3434273
theorem B4345775 : Blo 1524459 4345775 := bstep (se 1 (by rfl) ⟨3259331, by rfl⟩ : syracuseStep 4345775 = 6518663) B6518663
theorem B1716187 : Blo 1524459 1716187 := bstep (se 1 (by rfl) ⟨1287140, by rfl⟩ : syracuseStep 1716187 = 2574281) B2574281
theorem B13037597 : Blo 1524459 13037597 := bstep (se 3 (by rfl) ⟨2444549, by rfl⟩ : syracuseStep 13037597 = 4889099) B4889099
theorem B2609191 : Blo 1524459 2609191 := bstep (se 1 (by rfl) ⟨1956893, by rfl⟩ : syracuseStep 2609191 = 3913787) B3913787
theorem B1929415 : Blo 1524459 1929415 := bstep (se 1 (by rfl) ⟨1447061, by rfl⟩ : syracuseStep 1929415 = 2894123) B2894123
theorem B5501245 : Blo 1524459 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B3912065 : Blo 1524459 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B1716655 : Blo 1524459 1716655 := bstep (se 1 (by rfl) ⟨1287491, by rfl⟩ : syracuseStep 1716655 = 2574983) B2574983
theorem B27832841 : Blo 1524459 27832841 := bstep (se 2 (by rfl) ⟨10437315, by rfl⟩ : syracuseStep 27832841 = 20874631) B20874631
theorem B4887049 : Blo 1524459 4887049 := bstep (se 2 (by rfl) ⟨1832643, by rfl⟩ : syracuseStep 4887049 = 3665287) B3665287
theorem B2896393 : Blo 1524459 2896393 := bstep (se 2 (by rfl) ⟨1086147, by rfl⟩ : syracuseStep 2896393 = 2172295) B2172295
theorem B5788199 : Blo 1524459 5788199 := bstep (se 1 (by rfl) ⟨4341149, by rfl⟩ : syracuseStep 5788199 = 8682299) B8682299
theorem B5149223 : Blo 1524459 5149223 := bstep (se 1 (by rfl) ⟨3861917, by rfl⟩ : syracuseStep 5149223 = 7723835) B7723835
theorem B5149331 : Blo 1524459 5149331 := bstep (se 1 (by rfl) ⟨3861998, by rfl⟩ : syracuseStep 5149331 = 7723997) B7723997
theorem B4346617 : Blo 1524459 4346617 := bstep (se 2 (by rfl) ⟨1629981, by rfl⟩ : syracuseStep 4346617 = 3259963) B3259963
theorem B16495433 : Blo 1524459 16495433 := bstep (se 2 (by rfl) ⟨6185787, by rfl⟩ : syracuseStep 16495433 = 12371575) B12371575
theorem B2896735 : Blo 1524459 2896735 := bstep (se 1 (by rfl) ⟨2172551, by rfl⟩ : syracuseStep 2896735 = 4345103) B4345103
theorem B1717087 : Blo 1524459 1717087 := bstep (se 1 (by rfl) ⟨1287815, by rfl⟩ : syracuseStep 1717087 = 2575631) B2575631
theorem B5149547 : Blo 1524459 5149547 := bstep (se 1 (by rfl) ⟨3862160, by rfl⟩ : syracuseStep 5149547 = 7724321) B7724321
theorem B5149601 : Blo 1524459 5149601 := bstep (se 2 (by rfl) ⟨1931100, by rfl⟩ : syracuseStep 5149601 = 3862201) B3862201
theorem B1930159 : Blo 1524459 1930159 := bstep (se 1 (by rfl) ⟨1447619, by rfl⟩ : syracuseStep 1930159 = 2895239) B2895239
theorem B3257263 : Blo 1524459 3257263 := bstep (se 1 (by rfl) ⟨2442947, by rfl⟩ : syracuseStep 3257263 = 4885895) B4885895
theorem B26432477 : Blo 1524459 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B6181895 : Blo 1524459 6181895 := bstep (se 1 (by rfl) ⟨4636421, by rfl⟩ : syracuseStep 6181895 = 9272843) B9272843
theorem B3863609 : Blo 1524459 3863609 := bstep (se 2 (by rfl) ⟨1448853, by rfl⟩ : syracuseStep 3863609 = 2897707) B2897707
theorem B14652535 : Blo 1524459 14652535 := bstep (se 1 (by rfl) ⟨10989401, by rfl⟩ : syracuseStep 14652535 = 21978803) B21978803
theorem B3912875 : Blo 1524459 3912875 := bstep (se 1 (by rfl) ⟨2934656, by rfl⟩ : syracuseStep 3912875 = 5869313) B5869313
theorem B5788867 : Blo 1524459 5788867 := bstep (se 1 (by rfl) ⟨4341650, by rfl⟩ : syracuseStep 5788867 = 8683301) B8683301
theorem B5789171 : Blo 1524459 5789171 := bstep (se 1 (by rfl) ⟨4341878, by rfl⟩ : syracuseStep 5789171 = 8683757) B8683757
theorem B5150195 : Blo 1524459 5150195 := bstep (se 1 (by rfl) ⟨3862646, by rfl⟩ : syracuseStep 5150195 = 7725293) B7725293
theorem B24729077 : Blo 1524459 24729077 := bstep (se 5 (by rfl) ⟨1159175, by rfl⟩ : syracuseStep 24729077 = 2318351) B2318351
theorem B4888279 : Blo 1524459 4888279 := bstep (se 1 (by rfl) ⟨3666209, by rfl⟩ : syracuseStep 4888279 = 7332419) B7332419
theorem B17364779 : Blo 1524459 17364779 := bstep (se 1 (by rfl) ⟨13023584, by rfl⟩ : syracuseStep 17364779 = 26047169) B26047169
theorem B13907771 : Blo 1524459 13907771 := bstep (se 1 (by rfl) ⟨10430828, by rfl⟩ : syracuseStep 13907771 = 20861657) B20861657
theorem B190502725 : Blo 1524459 190502725 := bstep (se 4 (by rfl) ⟨17859630, by rfl⟩ : syracuseStep 190502725 = 35719261) B35719261
theorem B5871455 : Blo 1524459 5871455 := bstep (se 1 (by rfl) ⟨4403591, by rfl⟩ : syracuseStep 5871455 = 8807183) B8807183
theorem B10442681 : Blo 1524459 10442681 := bstep (se 2 (by rfl) ⟨3916005, by rfl⟩ : syracuseStep 10442681 = 7832011) B7832011
theorem B3430331 : Blo 1524459 3430331 := bstep (se 1 (by rfl) ⟨2572748, by rfl⟩ : syracuseStep 3430331 = 5145497) B5145497
theorem B5789627 : Blo 1524459 5789627 := bstep (se 1 (by rfl) ⟨4342220, by rfl⟩ : syracuseStep 5789627 = 8684441) B8684441
theorem B2897851 : Blo 1524459 2897851 := bstep (se 1 (by rfl) ⟨2173388, by rfl⟩ : syracuseStep 2897851 = 4346777) B4346777
theorem B5150735 : Blo 1524459 5150735 := bstep (se 1 (by rfl) ⟨3863051, by rfl⟩ : syracuseStep 5150735 = 7726103) B7726103
theorem B10442789 : Blo 1524459 10442789 := bstep (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) B1958023
theorem B1931303 : Blo 1524459 1931303 := bstep (se 1 (by rfl) ⟨1448477, by rfl⟩ : syracuseStep 1931303 = 2896955) B2896955
theorem B3430457 : Blo 1524459 3430457 := bstep (se 2 (by rfl) ⟨1286421, by rfl⟩ : syracuseStep 3430457 = 2572843) B2572843
theorem B3258425 : Blo 1524459 3258425 := bstep (se 2 (by rfl) ⟨1221909, by rfl⟩ : syracuseStep 3258425 = 2443819) B2443819
theorem B13031513 : Blo 1524459 13031513 := bstep (se 2 (by rfl) ⟨4886817, by rfl⟩ : syracuseStep 13031513 = 9773635) B9773635
theorem B17373527 : Blo 1524459 17373527 := bstep (se 1 (by rfl) ⟨13030145, by rfl⟩ : syracuseStep 17373527 = 26060291) B26060291
theorem B1931627 : Blo 1524459 1931627 := bstep (se 1 (by rfl) ⟨1448720, by rfl⟩ : syracuseStep 1931627 = 2897441) B2897441
theorem B3430799 : Blo 1524459 3430799 := bstep (se 1 (by rfl) ⟨2573099, by rfl⟩ : syracuseStep 3430799 = 5146199) B5146199
theorem B3258767 : Blo 1524459 3258767 := bstep (se 1 (by rfl) ⟨2444075, by rfl⟩ : syracuseStep 3258767 = 4888151) B4888151
theorem B5151329 : Blo 1524459 5151329 := bstep (se 2 (by rfl) ⟨1931748, by rfl⟩ : syracuseStep 5151329 = 3863497) B3863497
theorem B3431123 : Blo 1524459 3431123 := bstep (se 1 (by rfl) ⟨2573342, by rfl⟩ : syracuseStep 3431123 = 5146685) B5146685
theorem B10722269 : Blo 1524459 10722269 := bstep (se 3 (by rfl) ⟨2010425, by rfl⟩ : syracuseStep 10722269 = 4020851) B4020851
theorem B55639385 : Blo 1524459 55639385 := bstep (se 2 (by rfl) ⟨20864769, by rfl⟩ : syracuseStep 55639385 = 41729539) B41729539
theorem B111336889 : Blo 1524459 111336889 := bstep (se 2 (by rfl) ⟨41751333, by rfl⟩ : syracuseStep 111336889 = 83502667) B83502667
theorem B19553831 : Blo 1524459 19553831 := bstep (se 1 (by rfl) ⟨14665373, by rfl⟩ : syracuseStep 19553831 = 29330747) B29330747
theorem B3432059 : Blo 1524459 3432059 := bstep (se 1 (by rfl) ⟨2574044, by rfl⟩ : syracuseStep 3432059 = 5148089) B5148089
theorem B3432185 : Blo 1524459 3432185 := bstep (se 2 (by rfl) ⟨1287069, by rfl⟩ : syracuseStep 3432185 = 2574139) B2574139
theorem B2170729 : Blo 1524459 2170729 := bstep (se 2 (by rfl) ⟨814023, by rfl⟩ : syracuseStep 2170729 = 1628047) B1628047
theorem B9772919 : Blo 1524459 9772919 := bstep (se 1 (by rfl) ⟨7329689, by rfl⟩ : syracuseStep 9772919 = 14659379) B14659379
theorem B8691731 : Blo 1524459 8691731 := bstep (se 1 (by rfl) ⟨6518798, by rfl⟩ : syracuseStep 8691731 = 13037597) B13037597
theorem B5791769 : Blo 1524459 5791769 := bstep (se 2 (by rfl) ⟨2171913, by rfl⟩ : syracuseStep 5791769 = 4343827) B4343827
theorem B83501117 : Blo 1524459 83501117 := bstep (se 3 (by rfl) ⟨15656459, by rfl⟩ : syracuseStep 83501117 = 31312919) B31312919
theorem B2572553 : Blo 1524459 2572553 := bstep (se 2 (by rfl) ⟨964707, by rfl⟩ : syracuseStep 2572553 = 1929415) B1929415
theorem B18555227 : Blo 1524459 18555227 := bstep (se 1 (by rfl) ⟨13916420, by rfl⟩ : syracuseStep 18555227 = 27832841) B27832841
theorem B3858799 : Blo 1524459 3858799 := bstep (se 1 (by rfl) ⟨2894099, by rfl⟩ : syracuseStep 3858799 = 5788199) B5788199
theorem B3432815 : Blo 1524459 3432815 := bstep (se 1 (by rfl) ⟨2574611, by rfl⟩ : syracuseStep 3432815 = 5149223) B5149223
theorem B3432887 : Blo 1524459 3432887 := bstep (se 1 (by rfl) ⟨2574665, by rfl⟩ : syracuseStep 3432887 = 5149331) B5149331
theorem B3433031 : Blo 1524459 3433031 := bstep (se 1 (by rfl) ⟨2574773, by rfl⟩ : syracuseStep 3433031 = 5149547) B5149547
theorem B3433067 : Blo 1524459 3433067 := bstep (se 1 (by rfl) ⟨2574800, by rfl⟩ : syracuseStep 3433067 = 5149601) B5149601
theorem B17621651 : Blo 1524459 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B4121263 : Blo 1524459 4121263 := bstep (se 1 (by rfl) ⟨3090947, by rfl⟩ : syracuseStep 4121263 = 6181895) B6181895
theorem B1524527 : Blo 1524459 1524527 := bstep (se 1 (by rfl) ⟨1143395, by rfl⟩ : syracuseStep 1524527 = 2286791) B2286791
theorem B1524635 : Blo 1524459 1524635 := bstep (se 1 (by rfl) ⟨1143476, by rfl⟩ : syracuseStep 1524635 = 2286953) B2286953
theorem B1524687 : Blo 1524459 1524687 := bstep (se 1 (by rfl) ⟨1143515, by rfl⟩ : syracuseStep 1524687 = 2287031) B2287031
theorem B1524711 : Blo 1524459 1524711 := bstep (se 1 (by rfl) ⟨1143533, by rfl⟩ : syracuseStep 1524711 = 2287067) B2287067
theorem B3859447 : Blo 1524459 3859447 := bstep (se 1 (by rfl) ⟨2894585, by rfl⟩ : syracuseStep 3859447 = 5789171) B5789171
theorem B5948407 : Blo 1524459 5948407 := bstep (se 1 (by rfl) ⟨4461305, by rfl⟩ : syracuseStep 5948407 = 8922611) B8922611
theorem B3433463 : Blo 1524459 3433463 := bstep (se 1 (by rfl) ⟨2575097, by rfl⟩ : syracuseStep 3433463 = 5150195) B5150195
theorem B11576519 : Blo 1524459 11576519 := bstep (se 1 (by rfl) ⟨8682389, by rfl⟩ : syracuseStep 11576519 = 17364779) B17364779
theorem B2573545 : Blo 1524459 2573545 := bstep (se 2 (by rfl) ⟨965079, by rfl⟩ : syracuseStep 2573545 = 1930159) B1930159
theorem B1525023 : Blo 1524459 1525023 := bstep (se 1 (by rfl) ⟨1143767, by rfl⟩ : syracuseStep 1525023 = 2287535) B2287535
theorem B2573599 : Blo 1524459 2573599 := bstep (se 1 (by rfl) ⟨1930199, by rfl⟩ : syracuseStep 2573599 = 3860399) B3860399
theorem B2286887 : Blo 1524459 2286887 := bstep (se 1 (by rfl) ⟨1715165, by rfl⟩ : syracuseStep 2286887 = 3430331) B3430331
theorem B3859751 : Blo 1524459 3859751 := bstep (se 1 (by rfl) ⟨2894813, by rfl⟩ : syracuseStep 3859751 = 5789627) B5789627
theorem B1525083 : Blo 1524459 1525083 := bstep (se 1 (by rfl) ⟨1143812, by rfl⟩ : syracuseStep 1525083 = 2287625) B2287625
theorem B3433823 : Blo 1524459 3433823 := bstep (se 1 (by rfl) ⟨2575367, by rfl⟩ : syracuseStep 3433823 = 5150735) B5150735
theorem B1525103 : Blo 1524459 1525103 := bstep (se 1 (by rfl) ⟨1143827, by rfl⟩ : syracuseStep 1525103 = 2287655) B2287655
theorem B2286971 : Blo 1524459 2286971 := bstep (se 1 (by rfl) ⟨1715228, by rfl⟩ : syracuseStep 2286971 = 3430457) B3430457
theorem B1525159 : Blo 1524459 1525159 := bstep (se 1 (by rfl) ⟨1143869, by rfl⟩ : syracuseStep 1525159 = 2287739) B2287739
theorem B2287097 : Blo 1524459 2287097 := bstep (se 2 (by rfl) ⟨857661, by rfl⟩ : syracuseStep 2287097 = 1715323) B1715323
theorem B1525243 : Blo 1524459 1525243 := bstep (se 1 (by rfl) ⟨1143932, by rfl⟩ : syracuseStep 1525243 = 2287865) B2287865
theorem B1525311 : Blo 1524459 1525311 := bstep (se 1 (by rfl) ⟨1143983, by rfl⟩ : syracuseStep 1525311 = 2287967) B2287967
theorem B1525319 : Blo 1524459 1525319 := bstep (se 1 (by rfl) ⟨1143989, by rfl⟩ : syracuseStep 1525319 = 2287979) B2287979
theorem B7718489 : Blo 1524459 7718489 := bstep (se 2 (by rfl) ⟨2894433, by rfl⟩ : syracuseStep 7718489 = 5788867) B5788867
theorem B2287199 : Blo 1524459 2287199 := bstep (se 1 (by rfl) ⟨1715399, by rfl⟩ : syracuseStep 2287199 = 3430799) B3430799
theorem B2172511 : Blo 1524459 2172511 := bstep (se 1 (by rfl) ⟨1629383, by rfl⟩ : syracuseStep 2172511 = 3258767) B3258767
theorem B2786977 : Blo 1524459 2786977 := bstep (se 2 (by rfl) ⟨1045116, by rfl⟩ : syracuseStep 2786977 = 2090233) B2090233
theorem B2574011 : Blo 1524459 2574011 := bstep (se 1 (by rfl) ⟨1930508, by rfl⟩ : syracuseStep 2574011 = 3861017) B3861017
theorem B1525471 : Blo 1524459 1525471 := bstep (se 1 (by rfl) ⟨1144103, by rfl⟩ : syracuseStep 1525471 = 2288207) B2288207
theorem B3434219 : Blo 1524459 3434219 := bstep (se 1 (by rfl) ⟨2575664, by rfl⟩ : syracuseStep 3434219 = 5151329) B5151329
theorem B1525551 : Blo 1524459 1525551 := bstep (se 1 (by rfl) ⟨1144163, by rfl⟩ : syracuseStep 1525551 = 2288327) B2288327
theorem B2787119 : Blo 1524459 2787119 := bstep (se 1 (by rfl) ⟨2090339, by rfl⟩ : syracuseStep 2787119 = 4180679) B4180679
theorem B2287415 : Blo 1524459 2287415 := bstep (se 1 (by rfl) ⟨1715561, by rfl⟩ : syracuseStep 2287415 = 3431123) B3431123
theorem B13027139 : Blo 1524459 13027139 := bstep (se 1 (by rfl) ⟨9770354, by rfl⟩ : syracuseStep 13027139 = 19540709) B19540709
theorem B3663721 : Blo 1524459 3663721 := bstep (se 2 (by rfl) ⟨1373895, by rfl⟩ : syracuseStep 3663721 = 2747791) B2747791
theorem B3434345 : Blo 1524459 3434345 := bstep (se 2 (by rfl) ⟨1287879, by rfl⟩ : syracuseStep 3434345 = 2575759) B2575759
theorem B1525659 : Blo 1524459 1525659 := bstep (se 1 (by rfl) ⟨1144244, by rfl⟩ : syracuseStep 1525659 = 2288489) B2288489
theorem B148449185 : Blo 1524459 148449185 := bstep (se 2 (by rfl) ⟨55668444, by rfl⟩ : syracuseStep 148449185 = 111336889) B111336889
theorem B1525711 : Blo 1524459 1525711 := bstep (se 1 (by rfl) ⟨1144283, by rfl⟩ : syracuseStep 1525711 = 2288567) B2288567
theorem B1525735 : Blo 1524459 1525735 := bstep (se 1 (by rfl) ⟨1144301, by rfl⟩ : syracuseStep 1525735 = 2288603) B2288603
theorem B6186989 : Blo 1524459 6186989 := bstep (se 3 (by rfl) ⟨1160060, by rfl⟩ : syracuseStep 6186989 = 2320121) B2320121
theorem B2287721 : Blo 1524459 2287721 := bstep (se 2 (by rfl) ⟨857895, by rfl⟩ : syracuseStep 2287721 = 1715791) B1715791
theorem B289458373 : Blo 1524459 289458373 := bstep (se 4 (by rfl) ⟨27136722, by rfl⟩ : syracuseStep 289458373 = 54273445) B54273445
theorem B1526047 : Blo 1524459 1526047 := bstep (se 1 (by rfl) ⟨1144535, by rfl⟩ : syracuseStep 1526047 = 2289071) B2289071
theorem B1526107 : Blo 1524459 1526107 := bstep (se 1 (by rfl) ⟨1144580, by rfl⟩ : syracuseStep 1526107 = 2289161) B2289161
theorem B13035887 : Blo 1524459 13035887 := bstep (se 1 (by rfl) ⟨9776915, by rfl⟩ : syracuseStep 13035887 = 19553831) B19553831
theorem B1526127 : Blo 1524459 1526127 := bstep (se 1 (by rfl) ⟨1144595, by rfl⟩ : syracuseStep 1526127 = 2289191) B2289191
theorem B2288039 : Blo 1524459 2288039 := bstep (se 1 (by rfl) ⟨1716029, by rfl⟩ : syracuseStep 2288039 = 3432059) B3432059
theorem B1526183 : Blo 1524459 1526183 := bstep (se 1 (by rfl) ⟨1144637, by rfl⟩ : syracuseStep 1526183 = 2289275) B2289275
theorem B254003633 : Blo 1524459 254003633 := bstep (se 2 (by rfl) ⟨95251362, by rfl⟩ : syracuseStep 254003633 = 190502725) B190502725
theorem B5147063 : Blo 1524459 5147063 := bstep (se 1 (by rfl) ⟨3860297, by rfl⟩ : syracuseStep 5147063 = 7720595) B7720595
theorem B2894305 : Blo 1524459 2894305 := bstep (se 2 (by rfl) ⟨1085364, by rfl⟩ : syracuseStep 2894305 = 2170729) B2170729
theorem B2288123 : Blo 1524459 2288123 := bstep (se 1 (by rfl) ⟨1716092, by rfl⟩ : syracuseStep 2288123 = 3432185) B3432185
theorem B1526267 : Blo 1524459 1526267 := bstep (se 1 (by rfl) ⟨1144700, by rfl⟩ : syracuseStep 1526267 = 2289401) B2289401
theorem B4639295 : Blo 1524459 4639295 := bstep (se 1 (by rfl) ⟨3479471, by rfl⟩ : syracuseStep 4639295 = 6958943) B6958943
theorem B1526335 : Blo 1524459 1526335 := bstep (se 1 (by rfl) ⟨1144751, by rfl⟩ : syracuseStep 1526335 = 2289503) B2289503
theorem B1526343 : Blo 1524459 1526343 := bstep (se 1 (by rfl) ⟨1144757, by rfl⟩ : syracuseStep 1526343 = 2289515) B2289515
theorem B6515279 : Blo 1524459 6515279 := bstep (se 1 (by rfl) ⟨4886459, by rfl⟩ : syracuseStep 6515279 = 9772919) B9772919
theorem B2288249 : Blo 1524459 2288249 := bstep (se 2 (by rfl) ⟨858093, by rfl⟩ : syracuseStep 2288249 = 1716187) B1716187
theorem B2288303 : Blo 1524459 2288303 := bstep (se 1 (by rfl) ⟨1716227, by rfl⟩ : syracuseStep 2288303 = 3432455) B3432455
theorem B2288351 : Blo 1524459 2288351 := bstep (se 1 (by rfl) ⟨1716263, by rfl⟩ : syracuseStep 2288351 = 3432527) B3432527
theorem B5794685 : Blo 1524459 5794685 := bstep (se 3 (by rfl) ⟨1086503, by rfl⟩ : syracuseStep 5794685 = 2173007) B2173007
theorem B3861391 : Blo 1524459 3861391 := bstep (se 1 (by rfl) ⟨2896043, by rfl⟩ : syracuseStep 3861391 = 5792087) B5792087
theorem B2608043 : Blo 1524459 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B2288615 : Blo 1524459 2288615 := bstep (se 1 (by rfl) ⟨1716461, by rfl⟩ : syracuseStep 2288615 = 3432923) B3432923
theorem B7433203 : Blo 1524459 7433203 := bstep (se 1 (by rfl) ⟨5574902, by rfl⟩ : syracuseStep 7433203 = 11149805) B11149805
theorem B14855183 : Blo 1524459 14855183 := bstep (se 1 (by rfl) ⟨11141387, by rfl⟩ : syracuseStep 14855183 = 22282775) B22282775
theorem B8686673 : Blo 1524459 8686673 := bstep (se 2 (by rfl) ⟨3257502, by rfl⟩ : syracuseStep 8686673 = 6515005) B6515005
theorem B7334993 : Blo 1524459 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B10996955 : Blo 1524459 10996955 := bstep (se 1 (by rfl) ⟨8247716, by rfl⟩ : syracuseStep 10996955 = 16495433) B16495433
theorem B2288873 : Blo 1524459 2288873 := bstep (se 2 (by rfl) ⟨858327, by rfl⟩ : syracuseStep 2288873 = 1716655) B1716655
theorem B2288927 : Blo 1524459 2288927 := bstep (se 1 (by rfl) ⟨1716695, by rfl⟩ : syracuseStep 2288927 = 3433391) B3433391
theorem B6516065 : Blo 1524459 6516065 := bstep (se 2 (by rfl) ⟨2443524, by rfl⟩ : syracuseStep 6516065 = 4887049) B4887049
theorem B3861857 : Blo 1524459 3861857 := bstep (se 2 (by rfl) ⟨1448196, by rfl⟩ : syracuseStep 3861857 = 2896393) B2896393
theorem B2575739 : Blo 1524459 2575739 := bstep (se 1 (by rfl) ⟨1931804, by rfl⟩ : syracuseStep 2575739 = 3863609) B3863609
theorem B2608583 : Blo 1524459 2608583 := bstep (se 1 (by rfl) ⟨1956437, by rfl⟩ : syracuseStep 2608583 = 3912875) B3912875
theorem B2289095 : Blo 1524459 2289095 := bstep (se 1 (by rfl) ⟨1716821, by rfl⟩ : syracuseStep 2289095 = 3433643) B3433643
theorem B3092051 : Blo 1524459 3092051 := bstep (se 1 (by rfl) ⟨2319038, by rfl⟩ : syracuseStep 3092051 = 4638077) B4638077
theorem B5795489 : Blo 1524459 5795489 := bstep (se 2 (by rfl) ⟨2173308, by rfl⟩ : syracuseStep 5795489 = 4346617) B4346617
theorem B16486051 : Blo 1524459 16486051 := bstep (se 1 (by rfl) ⟨12364538, by rfl⟩ : syracuseStep 16486051 = 24729077) B24729077
theorem B1715935 : Blo 1524459 1715935 := bstep (se 1 (by rfl) ⟨1286951, by rfl⟩ : syracuseStep 1715935 = 2573903) B2573903
theorem B3862313 : Blo 1524459 3862313 := bstep (se 2 (by rfl) ⟨1448367, by rfl⟩ : syracuseStep 3862313 = 2896735) B2896735
theorem B2289449 : Blo 1524459 2289449 := bstep (se 2 (by rfl) ⟨858543, by rfl⟩ : syracuseStep 2289449 = 1717087) B1717087
theorem B2289455 : Blo 1524459 2289455 := bstep (se 1 (by rfl) ⟨1717091, by rfl⟩ : syracuseStep 2289455 = 3434183) B3434183
theorem B8687675 : Blo 1524459 8687675 := bstep (se 1 (by rfl) ⟨6515756, by rfl⟩ : syracuseStep 8687675 = 13031513) B13031513
theorem B42315979 : Blo 1524459 42315979 := bstep (se 1 (by rfl) ⟨31736984, by rfl⟩ : syracuseStep 42315979 = 63473969) B63473969
theorem B1716511 : Blo 1524459 1716511 := bstep (se 1 (by rfl) ⟨1287383, by rfl⟩ : syracuseStep 1716511 = 2574767) B2574767
theorem B1929511 : Blo 1524459 1929511 := bstep (se 1 (by rfl) ⟨1447133, by rfl⟩ : syracuseStep 1929511 = 2894267) B2894267
theorem B3715579 : Blo 1524459 3715579 := bstep (se 1 (by rfl) ⟨2786684, by rfl⟩ : syracuseStep 3715579 = 5573369) B5573369
theorem B1716799 : Blo 1524459 1716799 := bstep (se 1 (by rfl) ⟨1287599, by rfl⟩ : syracuseStep 1716799 = 2575199) B2575199
theorem B1831519 : Blo 1524459 1831519 := bstep (se 1 (by rfl) ⟨1373639, by rfl⟩ : syracuseStep 1831519 = 2747279) B2747279
theorem B1929835 : Blo 1524459 1929835 := bstep (se 1 (by rfl) ⟨1447376, by rfl⟩ : syracuseStep 1929835 = 2894753) B2894753
theorem B3256939 : Blo 1524459 3256939 := bstep (se 1 (by rfl) ⟨2442704, by rfl⟩ : syracuseStep 3256939 = 4885409) B4885409
theorem B7148179 : Blo 1524459 7148179 := bstep (se 1 (by rfl) ⟨5361134, by rfl⟩ : syracuseStep 7148179 = 10722269) B10722269
theorem B3863315 : Blo 1524459 3863315 := bstep (se 1 (by rfl) ⟨2897486, by rfl⟩ : syracuseStep 3863315 = 5794973) B5794973
theorem B1930063 : Blo 1524459 1930063 := bstep (se 1 (by rfl) ⟨1447547, by rfl⟩ : syracuseStep 1930063 = 2895095) B2895095
theorem B17372069 : Blo 1524459 17372069 := bstep (se 4 (by rfl) ⟨1628631, by rfl⟩ : syracuseStep 17372069 = 3257263) B3257263
theorem B6517705 : Blo 1524459 6517705 := bstep (se 2 (by rfl) ⟨2444139, by rfl⟩ : syracuseStep 6517705 = 4888279) B4888279
theorem B11580407 : Blo 1524459 11580407 := bstep (se 1 (by rfl) ⟨8685305, by rfl⟩ : syracuseStep 11580407 = 17370611) B17370611
theorem B2897039 : Blo 1524459 2897039 := bstep (se 1 (by rfl) ⟨2172779, by rfl⟩ : syracuseStep 2897039 = 4345559) B4345559
theorem B3863771 : Blo 1524459 3863771 := bstep (se 1 (by rfl) ⟨2897828, by rfl⟩ : syracuseStep 3863771 = 5795657) B5795657
theorem B3863801 : Blo 1524459 3863801 := bstep (se 2 (by rfl) ⟨1448925, by rfl⟩ : syracuseStep 3863801 = 2897851) B2897851
theorem B2897183 : Blo 1524459 2897183 := bstep (se 1 (by rfl) ⟨2172887, by rfl⟩ : syracuseStep 2897183 = 4345775) B4345775
theorem B5150141 : Blo 1524459 5150141 := bstep (se 3 (by rfl) ⟨965651, by rfl⟩ : syracuseStep 5150141 = 1931303) B1931303
theorem B8689133 : Blo 1524459 8689133 := bstep (se 3 (by rfl) ⟨1629212, by rfl⟩ : syracuseStep 8689133 = 3258425) B3258425
theorem B13915685 : Blo 1524459 13915685 := bstep (se 4 (by rfl) ⟨1304595, by rfl⟩ : syracuseStep 13915685 = 2609191) B2609191
theorem B3430151 : Blo 1524459 3430151 := bstep (se 1 (by rfl) ⟨2572613, by rfl⟩ : syracuseStep 3430151 = 5145227) B5145227
theorem B66909989 : Blo 1524459 66909989 := bstep (se 4 (by rfl) ⟨6272811, by rfl⟩ : syracuseStep 66909989 = 12545623) B12545623
theorem B5150519 : Blo 1524459 5150519 := bstep (se 1 (by rfl) ⟨3862889, by rfl⟩ : syracuseStep 5150519 = 7725779) B7725779
theorem B5789825 : Blo 1524459 5789825 := bstep (se 2 (by rfl) ⟨2171184, by rfl⟩ : syracuseStep 5789825 = 4342369) B4342369
theorem B6519037 : Blo 1524459 6519037 := bstep (se 3 (by rfl) ⟨1222319, by rfl⟩ : syracuseStep 6519037 = 2444639) B2444639
theorem B5151005 : Blo 1524459 5151005 := bstep (se 3 (by rfl) ⟨965813, by rfl⟩ : syracuseStep 5151005 = 1931627) B1931627
theorem B3430763 : Blo 1524459 3430763 := bstep (se 1 (by rfl) ⟨2573072, by rfl⟩ : syracuseStep 3430763 = 5146145) B5146145
theorem B3430907 : Blo 1524459 3430907 := bstep (se 1 (by rfl) ⟨2573180, by rfl⟩ : syracuseStep 3430907 = 5146361) B5146361
theorem B9271847 : Blo 1524459 9271847 := bstep (se 1 (by rfl) ⟨6953885, by rfl⟩ : syracuseStep 9271847 = 13907771) B13907771
theorem B3914303 : Blo 1524459 3914303 := bstep (se 1 (by rfl) ⟨2935727, by rfl⟩ : syracuseStep 3914303 = 5871455) B5871455
theorem B1628743 : Blo 1524459 1628743 := bstep (se 1 (by rfl) ⟨1221557, by rfl⟩ : syracuseStep 1628743 = 2443115) B2443115
theorem B7051883 : Blo 1524459 7051883 := bstep (se 1 (by rfl) ⟨5288912, by rfl⟩ : syracuseStep 7051883 = 10577825) B10577825
theorem B3431033 : Blo 1524459 3431033 := bstep (se 2 (by rfl) ⟨1286637, by rfl⟩ : syracuseStep 3431033 = 2573275) B2573275
theorem B6961787 : Blo 1524459 6961787 := bstep (se 1 (by rfl) ⟨5221340, by rfl⟩ : syracuseStep 6961787 = 10442681) B10442681
theorem B13040261 : Blo 1524459 13040261 := bstep (se 4 (by rfl) ⟨1222524, by rfl⟩ : syracuseStep 13040261 = 2445049) B2445049
theorem B3431087 : Blo 1524459 3431087 := bstep (se 1 (by rfl) ⟨2573315, by rfl⟩ : syracuseStep 3431087 = 5146631) B5146631
theorem B13212355 : Blo 1524459 13212355 := bstep (se 1 (by rfl) ⟨9909266, by rfl⟩ : syracuseStep 13212355 = 19818533) B19818533
theorem B6961859 : Blo 1524459 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B3431159 : Blo 1524459 3431159 := bstep (se 1 (by rfl) ⟨2573369, by rfl⟩ : syracuseStep 3431159 = 5146739) B5146739
theorem B19536713 : Blo 1524459 19536713 := bstep (se 2 (by rfl) ⟨7326267, by rfl⟩ : syracuseStep 19536713 = 14652535) B14652535
theorem B11582351 : Blo 1524459 11582351 := bstep (se 1 (by rfl) ⟨8686763, by rfl⟩ : syracuseStep 11582351 = 17373527) B17373527
theorem B3431339 : Blo 1524459 3431339 := bstep (se 1 (by rfl) ⟨2573504, by rfl⟩ : syracuseStep 3431339 = 5147009) B5147009
theorem B1629563 : Blo 1524459 1629563 := bstep (se 1 (by rfl) ⟨1222172, by rfl⟩ : syracuseStep 1629563 = 2444345) B2444345
theorem B3431879 : Blo 1524459 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B37092923 : Blo 1524459 37092923 := bstep (se 1 (by rfl) ⟨27819692, by rfl⟩ : syracuseStep 37092923 = 55639385) B55639385
theorem B13213331 : Blo 1524459 13213331 := bstep (se 1 (by rfl) ⟨9909998, by rfl⟩ : syracuseStep 13213331 = 19819997) B19819997
theorem B6512339 : Blo 1524459 6512339 := bstep (se 1 (by rfl) ⟨4884254, by rfl⟩ : syracuseStep 6512339 = 9768509) B9768509
theorem B16490243 : Blo 1524459 16490243 := bstep (se 1 (by rfl) ⟨12367682, by rfl⟩ : syracuseStep 16490243 = 24735365) B24735365
theorem B13033223 : Blo 1524459 13033223 := bstep (se 1 (by rfl) ⟨9774917, by rfl⟩ : syracuseStep 13033223 = 19549835) B19549835
theorem B7724807 : Blo 1524459 7724807 := bstep (se 1 (by rfl) ⟨5793605, by rfl⟩ : syracuseStep 7724807 = 11587211) B11587211
theorem B3432239 : Blo 1524459 3432239 := bstep (se 1 (by rfl) ⟨2574179, by rfl⟩ : syracuseStep 3432239 = 5148359) B5148359
theorem B5791783 : Blo 1524459 5791783 := bstep (se 1 (by rfl) ⟨4343837, by rfl⟩ : syracuseStep 5791783 = 8687675) B8687675
theorem B12370151 : Blo 1524459 12370151 := bstep (se 1 (by rfl) ⟨9277613, by rfl⟩ : syracuseStep 12370151 = 18555227) B18555227
theorem B8692049 : Blo 1524459 8692049 := bstep (se 2 (by rfl) ⟨3259518, by rfl⟩ : syracuseStep 8692049 = 6519037) B6519037
theorem B2572681 : Blo 1524459 2572681 := bstep (se 2 (by rfl) ⟨964755, by rfl⟩ : syracuseStep 2572681 = 1929511) B1929511
theorem B11747767 : Blo 1524459 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B5145065 : Blo 1524459 5145065 := bstep (se 2 (by rfl) ⟨1929399, by rfl⟩ : syracuseStep 5145065 = 3858799) B3858799
theorem B3859073 : Blo 1524459 3859073 := bstep (se 2 (by rfl) ⟨1447152, by rfl⟩ : syracuseStep 3859073 = 2894305) B2894305
theorem B2171657 : Blo 1524459 2171657 := bstep (se 2 (by rfl) ⟨814371, by rfl⟩ : syracuseStep 2171657 = 1628743) B1628743
theorem B2442025 : Blo 1524459 2442025 := bstep (se 2 (by rfl) ⟨915759, by rfl⟩ : syracuseStep 2442025 = 1831519) B1831519
theorem B7717679 : Blo 1524459 7717679 := bstep (se 1 (by rfl) ⟨5788259, by rfl⟩ : syracuseStep 7717679 = 11576519) B11576519
theorem B2573113 : Blo 1524459 2573113 := bstep (se 2 (by rfl) ⟨964917, by rfl⟩ : syracuseStep 2573113 = 1929835) B1929835
theorem B4342585 : Blo 1524459 4342585 := bstep (se 2 (by rfl) ⟨1628469, by rfl⟩ : syracuseStep 4342585 = 3256939) B3256939
theorem B1524591 : Blo 1524459 1524591 := bstep (se 1 (by rfl) ⟨1143443, by rfl⟩ : syracuseStep 1524591 = 2286887) B2286887
theorem B2573167 : Blo 1524459 2573167 := bstep (se 1 (by rfl) ⟨1929875, by rfl⟩ : syracuseStep 2573167 = 3859751) B3859751
theorem B21980069 : Blo 1524459 21980069 := bstep (se 4 (by rfl) ⟨2060631, by rfl⟩ : syracuseStep 21980069 = 4121263) B4121263
theorem B1524647 : Blo 1524459 1524647 := bstep (se 1 (by rfl) ⟨1143485, by rfl⟩ : syracuseStep 1524647 = 2286971) B2286971
theorem B3433427 : Blo 1524459 3433427 := bstep (se 1 (by rfl) ⟨2575070, by rfl⟩ : syracuseStep 3433427 = 5150141) B5150141
theorem B5792755 : Blo 1524459 5792755 := bstep (se 1 (by rfl) ⟨4344566, by rfl⟩ : syracuseStep 5792755 = 8689133) B8689133
theorem B1524731 : Blo 1524459 1524731 := bstep (se 1 (by rfl) ⟨1143548, by rfl⟩ : syracuseStep 1524731 = 2287097) B2287097
theorem B5145659 : Blo 1524459 5145659 := bstep (se 1 (by rfl) ⟨3859244, by rfl⟩ : syracuseStep 5145659 = 7718489) B7718489
theorem B1524799 : Blo 1524459 1524799 := bstep (se 1 (by rfl) ⟨1143599, by rfl⟩ : syracuseStep 1524799 = 2287199) B2287199
theorem B2573417 : Blo 1524459 2573417 := bstep (se 2 (by rfl) ⟨965031, by rfl⟩ : syracuseStep 2573417 = 1930063) B1930063
theorem B75220085 : Blo 1524459 75220085 := bstep (se 5 (by rfl) ⟨3525941, by rfl⟩ : syracuseStep 75220085 = 7051883) B7051883
theorem B2286767 : Blo 1524459 2286767 := bstep (se 1 (by rfl) ⟨1715075, by rfl⟩ : syracuseStep 2286767 = 3430151) B3430151
theorem B6956221 : Blo 1524459 6956221 := bstep (se 3 (by rfl) ⟨1304291, by rfl⟩ : syracuseStep 6956221 = 2608583) B2608583
theorem B1524943 : Blo 1524459 1524943 := bstep (se 1 (by rfl) ⟨1143707, by rfl⟩ : syracuseStep 1524943 = 2287415) B2287415
theorem B3433679 : Blo 1524459 3433679 := bstep (se 1 (by rfl) ⟨2575259, by rfl⟩ : syracuseStep 3433679 = 5150519) B5150519
theorem B8684759 : Blo 1524459 8684759 := bstep (se 1 (by rfl) ⟨6513569, by rfl⟩ : syracuseStep 8684759 = 13027139) B13027139
theorem B5145929 : Blo 1524459 5145929 := bstep (se 2 (by rfl) ⟨1929723, by rfl⟩ : syracuseStep 5145929 = 3859447) B3859447
theorem B7931209 : Blo 1524459 7931209 := bstep (se 2 (by rfl) ⟨2974203, by rfl⟩ : syracuseStep 7931209 = 5948407) B5948407
theorem B1525147 : Blo 1524459 1525147 := bstep (se 1 (by rfl) ⟨1143860, by rfl⟩ : syracuseStep 1525147 = 2287721) B2287721
theorem B3859883 : Blo 1524459 3859883 := bstep (se 1 (by rfl) ⟨2894912, by rfl⟩ : syracuseStep 3859883 = 5789825) B5789825
theorem B24724925 : Blo 1524459 24724925 := bstep (se 3 (by rfl) ⟨4635923, by rfl⟩ : syracuseStep 24724925 = 9271847) B9271847
theorem B10438141 : Blo 1524459 10438141 := bstep (se 3 (by rfl) ⟨1957151, by rfl⟩ : syracuseStep 10438141 = 3914303) B3914303
theorem B3434003 : Blo 1524459 3434003 := bstep (se 1 (by rfl) ⟨2575502, by rfl⟩ : syracuseStep 3434003 = 5151005) B5151005
theorem B2287175 : Blo 1524459 2287175 := bstep (se 1 (by rfl) ⟨1715381, by rfl⟩ : syracuseStep 2287175 = 3430763) B3430763
theorem B1525359 : Blo 1524459 1525359 := bstep (se 1 (by rfl) ⟨1144019, by rfl⟩ : syracuseStep 1525359 = 2288039) B2288039
theorem B2287271 : Blo 1524459 2287271 := bstep (se 1 (by rfl) ⟨1715453, by rfl⟩ : syracuseStep 2287271 = 3430907) B3430907
theorem B1525415 : Blo 1524459 1525415 := bstep (se 1 (by rfl) ⟨1144061, by rfl⟩ : syracuseStep 1525415 = 2288123) B2288123
theorem B4343519 : Blo 1524459 4343519 := bstep (se 1 (by rfl) ⟨3257639, by rfl⟩ : syracuseStep 4343519 = 6515279) B6515279
theorem B2287355 : Blo 1524459 2287355 := bstep (se 1 (by rfl) ⟨1715516, by rfl⟩ : syracuseStep 2287355 = 3431033) B3431033
theorem B1525499 : Blo 1524459 1525499 := bstep (se 1 (by rfl) ⟨1144124, by rfl⟩ : syracuseStep 1525499 = 2288249) B2288249
theorem B8693507 : Blo 1524459 8693507 := bstep (se 1 (by rfl) ⟨6520130, by rfl⟩ : syracuseStep 8693507 = 13040261) B13040261
theorem B2287391 : Blo 1524459 2287391 := bstep (se 1 (by rfl) ⟨1715543, by rfl⟩ : syracuseStep 2287391 = 3431087) B3431087
theorem B1525535 : Blo 1524459 1525535 := bstep (se 1 (by rfl) ⟨1144151, by rfl⟩ : syracuseStep 1525535 = 2288303) B2288303
theorem B1525567 : Blo 1524459 1525567 := bstep (se 1 (by rfl) ⟨1144175, by rfl⟩ : syracuseStep 1525567 = 2288351) B2288351
theorem B2287439 : Blo 1524459 2287439 := bstep (se 1 (by rfl) ⟨1715579, by rfl⟩ : syracuseStep 2287439 = 3431159) B3431159
theorem B2287559 : Blo 1524459 2287559 := bstep (se 1 (by rfl) ⟨1715669, by rfl⟩ : syracuseStep 2287559 = 3431339) B3431339
theorem B1525743 : Blo 1524459 1525743 := bstep (se 1 (by rfl) ⟨1144307, by rfl⟩ : syracuseStep 1525743 = 2288615) B2288615
theorem B1525915 : Blo 1524459 1525915 := bstep (se 1 (by rfl) ⟨1144436, by rfl⟩ : syracuseStep 1525915 = 2288873) B2288873
theorem B1525951 : Blo 1524459 1525951 := bstep (se 1 (by rfl) ⟨1144463, by rfl⟩ : syracuseStep 1525951 = 2288927) B2288927
theorem B21981401 : Blo 1524459 21981401 := bstep (se 2 (by rfl) ⟨8243025, by rfl⟩ : syracuseStep 21981401 = 16486051) B16486051
theorem B4344043 : Blo 1524459 4344043 := bstep (se 1 (by rfl) ⟨3258032, by rfl⟩ : syracuseStep 4344043 = 6516065) B6516065
theorem B2574571 : Blo 1524459 2574571 := bstep (se 1 (by rfl) ⟨1930928, by rfl⟩ : syracuseStep 2574571 = 3861857) B3861857
theorem B2287913 : Blo 1524459 2287913 := bstep (se 2 (by rfl) ⟨857967, by rfl⟩ : syracuseStep 2287913 = 1715935) B1715935
theorem B2287919 : Blo 1524459 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B1526063 : Blo 1524459 1526063 := bstep (se 1 (by rfl) ⟨1144547, by rfl⟩ : syracuseStep 1526063 = 2289095) B2289095
theorem B8808887 : Blo 1524459 8808887 := bstep (se 1 (by rfl) ⟨6606665, by rfl⟩ : syracuseStep 8808887 = 13213331) B13213331
theorem B4884961 : Blo 1524459 4884961 := bstep (se 2 (by rfl) ⟨1831860, by rfl⟩ : syracuseStep 4884961 = 3663721) B3663721
theorem B2574875 : Blo 1524459 2574875 := bstep (se 1 (by rfl) ⟨1931156, by rfl⟩ : syracuseStep 2574875 = 3862313) B3862313
theorem B1526299 : Blo 1524459 1526299 := bstep (se 1 (by rfl) ⟨1144724, by rfl⟩ : syracuseStep 1526299 = 2289449) B2289449
theorem B2288159 : Blo 1524459 2288159 := bstep (se 1 (by rfl) ⟨1716119, by rfl⟩ : syracuseStep 2288159 = 3432239) B3432239
theorem B1526303 : Blo 1524459 1526303 := bstep (se 1 (by rfl) ⟨1144727, by rfl⟩ : syracuseStep 1526303 = 2289455) B2289455
theorem B5794487 : Blo 1524459 5794487 := bstep (se 1 (by rfl) ⟨4345865, by rfl⟩ : syracuseStep 5794487 = 8691731) B8691731
theorem B3861179 : Blo 1524459 3861179 := bstep (se 1 (by rfl) ⟨2895884, by rfl⟩ : syracuseStep 3861179 = 5791769) B5791769
theorem B55667411 : Blo 1524459 55667411 := bstep (se 1 (by rfl) ⟨41750558, by rfl⟩ : syracuseStep 55667411 = 83501117) B83501117
theorem B1715035 : Blo 1524459 1715035 := bstep (se 1 (by rfl) ⟨1286276, by rfl⟩ : syracuseStep 1715035 = 2572553) B2572553
theorem B2288543 : Blo 1524459 2288543 := bstep (se 1 (by rfl) ⟨1716407, by rfl⟩ : syracuseStep 2288543 = 3432815) B3432815
theorem B385944497 : Blo 1524459 385944497 := bstep (se 2 (by rfl) ⟨144729186, by rfl⟩ : syracuseStep 385944497 = 289458373) B289458373
theorem B56421305 : Blo 1524459 56421305 := bstep (se 2 (by rfl) ⟨21157989, by rfl⟩ : syracuseStep 56421305 = 42315979) B42315979
theorem B2288591 : Blo 1524459 2288591 := bstep (se 1 (by rfl) ⟨1716443, by rfl⟩ : syracuseStep 2288591 = 3432887) B3432887
theorem B2288681 : Blo 1524459 2288681 := bstep (se 2 (by rfl) ⟨858255, by rfl⟩ : syracuseStep 2288681 = 1716511) B1716511
theorem B2288687 : Blo 1524459 2288687 := bstep (se 1 (by rfl) ⟨1716515, by rfl⟩ : syracuseStep 2288687 = 3433031) B3433031
theorem B2288711 : Blo 1524459 2288711 := bstep (se 1 (by rfl) ⟨1716533, by rfl⟩ : syracuseStep 2288711 = 3433067) B3433067
theorem B11586725 : Blo 1524459 11586725 := bstep (se 4 (by rfl) ⟨1086255, by rfl⟩ : syracuseStep 11586725 = 2172511) B2172511
theorem B2575543 : Blo 1524459 2575543 := bstep (se 1 (by rfl) ⟨1931657, by rfl⟩ : syracuseStep 2575543 = 3863315) B3863315
theorem B7720271 : Blo 1524459 7720271 := bstep (se 1 (by rfl) ⟨5790203, by rfl⟩ : syracuseStep 7720271 = 11580407) B11580407
theorem B2288975 : Blo 1524459 2288975 := bstep (se 1 (by rfl) ⟨1716731, by rfl⟩ : syracuseStep 2288975 = 3433463) B3433463
theorem B2289065 : Blo 1524459 2289065 := bstep (se 2 (by rfl) ⟨858399, by rfl⟩ : syracuseStep 2289065 = 1716799) B1716799
theorem B2575847 : Blo 1524459 2575847 := bstep (se 1 (by rfl) ⟨1931885, by rfl⟩ : syracuseStep 2575847 = 3863771) B3863771
theorem B2575867 : Blo 1524459 2575867 := bstep (se 1 (by rfl) ⟨1931900, by rfl⟩ : syracuseStep 2575867 = 3863801) B3863801
theorem B9530905 : Blo 1524459 9530905 := bstep (se 2 (by rfl) ⟨3574089, by rfl⟩ : syracuseStep 9530905 = 7148179) B7148179
theorem B2289215 : Blo 1524459 2289215 := bstep (se 1 (by rfl) ⟨1716911, by rfl⟩ : syracuseStep 2289215 = 3433823) B3433823
theorem B17616473 : Blo 1524459 17616473 := bstep (se 2 (by rfl) ⟨6606177, by rfl⟩ : syracuseStep 17616473 = 13212355) B13212355
theorem B4345501 : Blo 1524459 4345501 := bstep (se 3 (by rfl) ⟨814781, by rfl⟩ : syracuseStep 4345501 = 1629563) B1629563
theorem B1716007 : Blo 1524459 1716007 := bstep (se 1 (by rfl) ⟨1287005, by rfl⟩ : syracuseStep 1716007 = 2574011) B2574011
theorem B2289479 : Blo 1524459 2289479 := bstep (se 1 (by rfl) ⟨1717109, by rfl⟩ : syracuseStep 2289479 = 3434219) B3434219
theorem B5148521 : Blo 1524459 5148521 := bstep (se 2 (by rfl) ⟨1930695, by rfl⟩ : syracuseStep 5148521 = 3861391) B3861391
theorem B2289563 : Blo 1524459 2289563 := bstep (se 1 (by rfl) ⟨1717172, by rfl⟩ : syracuseStep 2289563 = 3434345) B3434345
theorem B8245469 : Blo 1524459 8245469 := bstep (se 3 (by rfl) ⟨1546025, by rfl⟩ : syracuseStep 8245469 = 3092051) B3092051
theorem B3092863 : Blo 1524459 3092863 := bstep (se 1 (by rfl) ⟨2319647, by rfl⟩ : syracuseStep 3092863 = 4639295) B4639295
theorem B4641191 : Blo 1524459 4641191 := bstep (se 1 (by rfl) ⟨3480893, by rfl⟩ : syracuseStep 4641191 = 6961787) B6961787
theorem B4641239 : Blo 1524459 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B3863123 : Blo 1524459 3863123 := bstep (se 1 (by rfl) ⟨2897342, by rfl⟩ : syracuseStep 3863123 = 5794685) B5794685
theorem B7721567 : Blo 1524459 7721567 := bstep (se 1 (by rfl) ⟨5791175, by rfl⟩ : syracuseStep 7721567 = 11582351) B11582351
theorem B178426637 : Blo 1524459 178426637 := bstep (se 3 (by rfl) ⟨33454994, by rfl⟩ : syracuseStep 178426637 = 66909989) B66909989
theorem B3715969 : Blo 1524459 3715969 := bstep (se 2 (by rfl) ⟨1393488, by rfl⟩ : syracuseStep 3715969 = 2786977) B2786977
theorem B1717159 : Blo 1524459 1717159 := bstep (se 1 (by rfl) ⟨1287869, by rfl⟩ : syracuseStep 1717159 = 2575739) B2575739
theorem B24728615 : Blo 1524459 24728615 := bstep (se 1 (by rfl) ⟨18546461, by rfl⟩ : syracuseStep 24728615 = 37092923) B37092923
theorem B3863659 : Blo 1524459 3863659 := bstep (se 1 (by rfl) ⟨2897744, by rfl⟩ : syracuseStep 3863659 = 5795489) B5795489
theorem B8688815 : Blo 1524459 8688815 := bstep (se 1 (by rfl) ⟨6516611, by rfl⟩ : syracuseStep 8688815 = 13033223) B13033223
theorem B5149871 : Blo 1524459 5149871 := bstep (se 1 (by rfl) ⟨3862403, by rfl⟩ : syracuseStep 5149871 = 7724807) B7724807
theorem B19559981 : Blo 1524459 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B11581379 : Blo 1524459 11581379 := bstep (se 1 (by rfl) ⟨8686034, by rfl⟩ : syracuseStep 11581379 = 17372069) B17372069
theorem B4954105 : Blo 1524459 4954105 := bstep (se 2 (by rfl) ⟨1857789, by rfl⟩ : syracuseStep 4954105 = 3715579) B3715579
theorem B1931359 : Blo 1524459 1931359 := bstep (se 1 (by rfl) ⟨1448519, by rfl⟩ : syracuseStep 1931359 = 2897039) B2897039
theorem B1931455 : Blo 1524459 1931455 := bstep (se 1 (by rfl) ⟨1448591, by rfl⟩ : syracuseStep 1931455 = 2897183) B2897183
theorem B1858079 : Blo 1524459 1858079 := bstep (se 1 (by rfl) ⟨1393559, by rfl⟩ : syracuseStep 1858079 = 2787119) B2787119
theorem B8690273 : Blo 1524459 8690273 := bstep (se 2 (by rfl) ⟨3258852, by rfl⟩ : syracuseStep 8690273 = 6517705) B6517705
theorem B98966123 : Blo 1524459 98966123 := bstep (se 1 (by rfl) ⟨74224592, by rfl⟩ : syracuseStep 98966123 = 148449185) B148449185
theorem B9910937 : Blo 1524459 9910937 := bstep (se 2 (by rfl) ⟨3716601, by rfl⟩ : syracuseStep 9910937 = 7433203) B7433203
theorem B37108493 : Blo 1524459 37108493 := bstep (se 3 (by rfl) ⟨6957842, by rfl⟩ : syracuseStep 37108493 = 13915685) B13915685
theorem B8690591 : Blo 1524459 8690591 := bstep (se 1 (by rfl) ⟨6517943, by rfl⟩ : syracuseStep 8690591 = 13035887) B13035887
theorem B169335755 : Blo 1524459 169335755 := bstep (se 1 (by rfl) ⟨127001816, by rfl⟩ : syracuseStep 169335755 = 254003633) B254003633
theorem B3431375 : Blo 1524459 3431375 := bstep (se 1 (by rfl) ⟨2573531, by rfl⟩ : syracuseStep 3431375 = 5147063) B5147063
theorem B3431393 : Blo 1524459 3431393 := bstep (se 2 (by rfl) ⟨1286772, by rfl⟩ : syracuseStep 3431393 = 2573545) B2573545
theorem B3431465 : Blo 1524459 3431465 := bstep (se 2 (by rfl) ⟨1286799, by rfl⟩ : syracuseStep 3431465 = 2573599) B2573599
theorem B13024475 : Blo 1524459 13024475 := bstep (se 1 (by rfl) ⟨9768356, by rfl⟩ : syracuseStep 13024475 = 19536713) B19536713
theorem B17366237 : Blo 1524459 17366237 := bstep (se 3 (by rfl) ⟨3256169, by rfl⟩ : syracuseStep 17366237 = 6512339) B6512339
theorem B9903455 : Blo 1524459 9903455 := bstep (se 1 (by rfl) ⟨7427591, by rfl⟩ : syracuseStep 9903455 = 14855183) B14855183
theorem B5791115 : Blo 1524459 5791115 := bstep (se 1 (by rfl) ⟨4343336, by rfl⟩ : syracuseStep 5791115 = 8686673) B8686673
theorem B7331303 : Blo 1524459 7331303 := bstep (se 1 (by rfl) ⟨5498477, by rfl⟩ : syracuseStep 7331303 = 10996955) B10996955
theorem B6954781 : Blo 1524459 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B10993495 : Blo 1524459 10993495 := bstep (se 1 (by rfl) ⟨8245121, by rfl⟩ : syracuseStep 10993495 = 16490243) B16490243
theorem B16498637 : Blo 1524459 16498637 := bstep (se 3 (by rfl) ⟨3093494, by rfl⟩ : syracuseStep 16498637 = 6186989) B6186989
theorem B5496979 : Blo 1524459 5496979 := bstep (se 1 (by rfl) ⟨4122734, by rfl⟩ : syracuseStep 5496979 = 8245469) B8245469
theorem B5792057 : Blo 1524459 5792057 := bstep (se 2 (by rfl) ⟨2172021, by rfl⟩ : syracuseStep 5792057 = 4344043) B4344043
theorem B3432761 : Blo 1524459 3432761 := bstep (se 2 (by rfl) ⟨1287285, by rfl⟩ : syracuseStep 3432761 = 2574571) B2574571
theorem B2572715 : Blo 1524459 2572715 := bstep (se 1 (by rfl) ⟨1929536, by rfl⟩ : syracuseStep 2572715 = 3859073) B3859073
theorem B5145119 : Blo 1524459 5145119 := bstep (se 1 (by rfl) ⟨3858839, by rfl⟩ : syracuseStep 5145119 = 7717679) B7717679
theorem B15663689 : Blo 1524459 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B6513281 : Blo 1524459 6513281 := bstep (se 2 (by rfl) ⟨2442480, by rfl⟩ : syracuseStep 6513281 = 4884961) B4884961
theorem B1524511 : Blo 1524459 1524511 := bstep (se 1 (by rfl) ⟨1143383, by rfl⟩ : syracuseStep 1524511 = 2286767) B2286767
theorem B5792543 : Blo 1524459 5792543 := bstep (se 1 (by rfl) ⟨4344407, by rfl⟩ : syracuseStep 5792543 = 8688815) B8688815
theorem B3433247 : Blo 1524459 3433247 := bstep (se 1 (by rfl) ⟨2574935, by rfl⟩ : syracuseStep 3433247 = 5149871) B5149871
theorem B2573255 : Blo 1524459 2573255 := bstep (se 1 (by rfl) ⟨1929941, by rfl⟩ : syracuseStep 2573255 = 3859883) B3859883
theorem B16483283 : Blo 1524459 16483283 := bstep (se 1 (by rfl) ⟨12362462, by rfl⟩ : syracuseStep 16483283 = 24724925) B24724925
theorem B1524783 : Blo 1524459 1524783 := bstep (se 1 (by rfl) ⟨1143587, by rfl⟩ : syracuseStep 1524783 = 2287175) B2287175
theorem B1524847 : Blo 1524459 1524847 := bstep (se 1 (by rfl) ⟨1143635, by rfl⟩ : syracuseStep 1524847 = 2287271) B2287271
theorem B2286713 : Blo 1524459 2286713 := bstep (se 2 (by rfl) ⟨857517, by rfl⟩ : syracuseStep 2286713 = 1715035) B1715035
theorem B1524903 : Blo 1524459 1524903 := bstep (se 1 (by rfl) ⟨1143677, by rfl⟩ : syracuseStep 1524903 = 2287355) B2287355
theorem B1524927 : Blo 1524459 1524927 := bstep (se 1 (by rfl) ⟨1143695, by rfl⟩ : syracuseStep 1524927 = 2287391) B2287391
theorem B1524959 : Blo 1524459 1524959 := bstep (se 1 (by rfl) ⟨1143719, by rfl⟩ : syracuseStep 1524959 = 2287439) B2287439
theorem B1525039 : Blo 1524459 1525039 := bstep (se 1 (by rfl) ⟨1143779, by rfl⟩ : syracuseStep 1525039 = 2287559) B2287559
theorem B1525275 : Blo 1524459 1525275 := bstep (se 1 (by rfl) ⟨1143956, by rfl⟩ : syracuseStep 1525275 = 2287913) B2287913
theorem B1525279 : Blo 1524459 1525279 := bstep (se 1 (by rfl) ⟨1143959, by rfl⟩ : syracuseStep 1525279 = 2287919) B2287919
theorem B3434057 : Blo 1524459 3434057 := bstep (se 2 (by rfl) ⟨1287771, by rfl⟩ : syracuseStep 3434057 = 2575543) B2575543
theorem B9274961 : Blo 1524459 9274961 := bstep (se 2 (by rfl) ⟨3478110, by rfl⟩ : syracuseStep 9274961 = 6956221) B6956221
theorem B1525439 : Blo 1524459 1525439 := bstep (se 1 (by rfl) ⟨1144079, by rfl⟩ : syracuseStep 1525439 = 2288159) B2288159
theorem B5793515 : Blo 1524459 5793515 := bstep (se 1 (by rfl) ⟨4345136, by rfl⟩ : syracuseStep 5793515 = 8690273) B8690273
theorem B26429165 : Blo 1524459 26429165 := bstep (se 3 (by rfl) ⟨4955468, by rfl⟩ : syracuseStep 26429165 = 9910937) B9910937
theorem B2574119 : Blo 1524459 2574119 := bstep (se 1 (by rfl) ⟨1930589, by rfl⟩ : syracuseStep 2574119 = 3861179) B3861179
theorem B37111607 : Blo 1524459 37111607 := bstep (se 1 (by rfl) ⟨27833705, by rfl⟩ : syracuseStep 37111607 = 55667411) B55667411
theorem B1525695 : Blo 1524459 1525695 := bstep (se 1 (by rfl) ⟨1144271, by rfl⟩ : syracuseStep 1525695 = 2288543) B2288543
theorem B5793727 : Blo 1524459 5793727 := bstep (se 1 (by rfl) ⟨4345295, by rfl⟩ : syracuseStep 5793727 = 8690591) B8690591
theorem B257296331 : Blo 1524459 257296331 := bstep (se 1 (by rfl) ⟨192972248, by rfl⟩ : syracuseStep 257296331 = 385944497) B385944497
theorem B2287583 : Blo 1524459 2287583 := bstep (se 1 (by rfl) ⟨1715687, by rfl⟩ : syracuseStep 2287583 = 3431375) B3431375
theorem B1525727 : Blo 1524459 1525727 := bstep (se 1 (by rfl) ⟨1144295, by rfl⟩ : syracuseStep 1525727 = 2288591) B2288591
theorem B2287595 : Blo 1524459 2287595 := bstep (se 1 (by rfl) ⟨1715696, by rfl⟩ : syracuseStep 2287595 = 3431393) B3431393
theorem B3434489 : Blo 1524459 3434489 := bstep (se 2 (by rfl) ⟨1287933, by rfl⟩ : syracuseStep 3434489 = 2575867) B2575867
theorem B2287643 : Blo 1524459 2287643 := bstep (se 1 (by rfl) ⟨1715732, by rfl⟩ : syracuseStep 2287643 = 3431465) B3431465
theorem B1525787 : Blo 1524459 1525787 := bstep (se 1 (by rfl) ⟨1144340, by rfl⟩ : syracuseStep 1525787 = 2288681) B2288681
theorem B1525791 : Blo 1524459 1525791 := bstep (se 1 (by rfl) ⟨1144343, by rfl⟩ : syracuseStep 1525791 = 2288687) B2288687
theorem B12707873 : Blo 1524459 12707873 := bstep (se 2 (by rfl) ⟨4765452, by rfl⟩ : syracuseStep 12707873 = 9530905) B9530905
theorem B1525807 : Blo 1524459 1525807 := bstep (se 1 (by rfl) ⟨1144355, by rfl⟩ : syracuseStep 1525807 = 2288711) B2288711
theorem B11577491 : Blo 1524459 11577491 := bstep (se 1 (by rfl) ⟨8683118, by rfl⟩ : syracuseStep 11577491 = 17366237) B17366237
theorem B5794001 : Blo 1524459 5794001 := bstep (se 2 (by rfl) ⟨2172750, by rfl⟩ : syracuseStep 5794001 = 4345501) B4345501
theorem B5146847 : Blo 1524459 5146847 := bstep (se 1 (by rfl) ⟨3860135, by rfl⟩ : syracuseStep 5146847 = 7720271) B7720271
theorem B1525983 : Blo 1524459 1525983 := bstep (se 1 (by rfl) ⟨1144487, by rfl⟩ : syracuseStep 1525983 = 2288975) B2288975
theorem B3860743 : Blo 1524459 3860743 := bstep (se 1 (by rfl) ⟨2895557, by rfl⟩ : syracuseStep 3860743 = 5791115) B5791115
theorem B1526043 : Blo 1524459 1526043 := bstep (se 1 (by rfl) ⟨1144532, by rfl⟩ : syracuseStep 1526043 = 2289065) B2289065
theorem B1526143 : Blo 1524459 1526143 := bstep (se 1 (by rfl) ⟨1144607, by rfl⟩ : syracuseStep 1526143 = 2289215) B2289215
theorem B2288009 : Blo 1524459 2288009 := bstep (se 2 (by rfl) ⟨858003, by rfl⟩ : syracuseStep 2288009 = 1716007) B1716007
theorem B14657993 : Blo 1524459 14657993 := bstep (se 2 (by rfl) ⟨5496747, by rfl⟩ : syracuseStep 14657993 = 10993495) B10993495
theorem B1526319 : Blo 1524459 1526319 := bstep (se 1 (by rfl) ⟨1144739, by rfl⟩ : syracuseStep 1526319 = 2289479) B2289479
theorem B1526375 : Blo 1524459 1526375 := bstep (se 1 (by rfl) ⟨1144781, by rfl⟩ : syracuseStep 1526375 = 2289563) B2289563
theorem B6605473 : Blo 1524459 6605473 := bstep (se 2 (by rfl) ⟨2477052, by rfl⟩ : syracuseStep 6605473 = 4954105) B4954105
theorem B2575145 : Blo 1524459 2575145 := bstep (se 2 (by rfl) ⟨965679, by rfl⟩ : syracuseStep 2575145 = 1931359) B1931359
theorem B5794699 : Blo 1524459 5794699 := bstep (se 1 (by rfl) ⟨4346024, by rfl⟩ : syracuseStep 5794699 = 8692049) B8692049
theorem B2575273 : Blo 1524459 2575273 := bstep (se 2 (by rfl) ⟨965727, by rfl⟩ : syracuseStep 2575273 = 1931455) B1931455
theorem B2575415 : Blo 1524459 2575415 := bstep (se 1 (by rfl) ⟨1931561, by rfl⟩ : syracuseStep 2575415 = 3863123) B3863123
theorem B5147711 : Blo 1524459 5147711 := bstep (se 1 (by rfl) ⟨3860783, by rfl⟩ : syracuseStep 5147711 = 7721567) B7721567
theorem B4123817 : Blo 1524459 4123817 := bstep (se 2 (by rfl) ⟨1546431, by rfl⟩ : syracuseStep 4123817 = 3092863) B3092863
theorem B118951091 : Blo 1524459 118951091 := bstep (se 1 (by rfl) ⟨89213318, by rfl⟩ : syracuseStep 118951091 = 178426637) B178426637
theorem B2288951 : Blo 1524459 2288951 := bstep (se 1 (by rfl) ⟨1716713, by rfl⟩ : syracuseStep 2288951 = 3433427) B3433427
theorem B16485743 : Blo 1524459 16485743 := bstep (se 1 (by rfl) ⟨12364307, by rfl⟩ : syracuseStep 16485743 = 24728615) B24728615
theorem B1715611 : Blo 1524459 1715611 := bstep (se 1 (by rfl) ⟨1286708, by rfl⟩ : syracuseStep 1715611 = 2573417) B2573417
theorem B50146723 : Blo 1524459 50146723 := bstep (se 1 (by rfl) ⟨37610042, by rfl⟩ : syracuseStep 50146723 = 75220085) B75220085
theorem B2289119 : Blo 1524459 2289119 := bstep (se 1 (by rfl) ⟨1716839, by rfl⟩ : syracuseStep 2289119 = 3433679) B3433679
theorem B2289335 : Blo 1524459 2289335 := bstep (se 1 (by rfl) ⟨1717001, by rfl⟩ : syracuseStep 2289335 = 3434003) B3434003
theorem B3256033 : Blo 1524459 3256033 := bstep (se 2 (by rfl) ⟨1221012, by rfl⟩ : syracuseStep 3256033 = 2442025) B2442025
theorem B2895679 : Blo 1524459 2895679 := bstep (se 1 (by rfl) ⟨2171759, by rfl⟩ : syracuseStep 2895679 = 4343519) B4343519
theorem B5795671 : Blo 1524459 5795671 := bstep (se 1 (by rfl) ⟨4346753, by rfl⟩ : syracuseStep 5795671 = 8693507) B8693507
theorem B2289545 : Blo 1524459 2289545 := bstep (se 2 (by rfl) ⟨858579, by rfl⟩ : syracuseStep 2289545 = 1717159) B1717159
theorem B7720919 : Blo 1524459 7720919 := bstep (se 1 (by rfl) ⟨5790689, by rfl⟩ : syracuseStep 7720919 = 11581379) B11581379
theorem B1716583 : Blo 1524459 1716583 := bstep (se 1 (by rfl) ⟨1287437, by rfl⟩ : syracuseStep 1716583 = 2574875) B2574875
theorem B3862991 : Blo 1524459 3862991 := bstep (se 1 (by rfl) ⟨2897243, by rfl⟩ : syracuseStep 3862991 = 5794487) B5794487
theorem B37614203 : Blo 1524459 37614203 := bstep (se 1 (by rfl) ⟨28210652, by rfl⟩ : syracuseStep 37614203 = 56421305) B56421305
theorem B112890503 : Blo 1524459 112890503 := bstep (se 1 (by rfl) ⟨84667877, by rfl⟩ : syracuseStep 112890503 = 169335755) B169335755
theorem B4887535 : Blo 1524459 4887535 := bstep (se 1 (by rfl) ⟨3665651, by rfl⟩ : syracuseStep 4887535 = 7331303) B7331303
theorem B1717231 : Blo 1524459 1717231 := bstep (se 1 (by rfl) ⟨1287923, by rfl⟩ : syracuseStep 1717231 = 2575847) B2575847
theorem B11744315 : Blo 1524459 11744315 := bstep (se 1 (by rfl) ⟨8808236, by rfl⟩ : syracuseStep 11744315 = 17616473) B17616473
theorem B10999091 : Blo 1524459 10999091 := bstep (se 1 (by rfl) ⟨8249318, by rfl⟩ : syracuseStep 10999091 = 16498637) B16498637
theorem B7722377 : Blo 1524459 7722377 := bstep (se 2 (by rfl) ⟨2895891, by rfl⟩ : syracuseStep 7722377 = 5791783) B5791783
theorem B8246767 : Blo 1524459 8246767 := bstep (se 1 (by rfl) ⟨6185075, by rfl⟩ : syracuseStep 8246767 = 12370151) B12370151
theorem B3094127 : Blo 1524459 3094127 := bstep (se 1 (by rfl) ⟨2320595, by rfl⟩ : syracuseStep 3094127 = 4641191) B4641191
theorem B3430043 : Blo 1524459 3430043 := bstep (se 1 (by rfl) ⟨2572532, by rfl⟩ : syracuseStep 3430043 = 5145065) B5145065
theorem B3430241 : Blo 1524459 3430241 := bstep (se 2 (by rfl) ⟨1286340, by rfl⟩ : syracuseStep 3430241 = 2572681) B2572681
theorem B14653379 : Blo 1524459 14653379 := bstep (se 1 (by rfl) ⟨10990034, by rfl⟩ : syracuseStep 14653379 = 21980069) B21980069
theorem B3430439 : Blo 1524459 3430439 := bstep (se 1 (by rfl) ⟨2572829, by rfl⟩ : syracuseStep 3430439 = 5145659) B5145659
theorem B5789839 : Blo 1524459 5789839 := bstep (se 1 (by rfl) ⟨4342379, by rfl⟩ : syracuseStep 5789839 = 8684759) B8684759
theorem B3430619 : Blo 1524459 3430619 := bstep (se 1 (by rfl) ⟨2572964, by rfl⟩ : syracuseStep 3430619 = 5145929) B5145929
theorem B13039987 : Blo 1524459 13039987 := bstep (se 1 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 13039987 = 19559981) B19559981
theorem B3430817 : Blo 1524459 3430817 := bstep (se 2 (by rfl) ⟨1286556, by rfl⟩ : syracuseStep 3430817 = 2573113) B2573113
theorem B5790113 : Blo 1524459 5790113 := bstep (se 2 (by rfl) ⟨2171292, by rfl⟩ : syracuseStep 5790113 = 4342585) B4342585
theorem B3430889 : Blo 1524459 3430889 := bstep (se 2 (by rfl) ⟨1286583, by rfl⟩ : syracuseStep 3430889 = 2573167) B2573167
theorem B4954625 : Blo 1524459 4954625 := bstep (se 2 (by rfl) ⟨1857984, by rfl⟩ : syracuseStep 4954625 = 3715969) B3715969
theorem B12376637 : Blo 1524459 12376637 := bstep (se 3 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 12376637 = 4641239) B4641239
theorem B7723673 : Blo 1524459 7723673 := bstep (se 2 (by rfl) ⟨2896377, by rfl⟩ : syracuseStep 7723673 = 5792755) B5792755
theorem B4954877 : Blo 1524459 4954877 := bstep (se 3 (by rfl) ⟨929039, by rfl⟩ : syracuseStep 4954877 = 1858079) B1858079
theorem B5151545 : Blo 1524459 5151545 := bstep (se 2 (by rfl) ⟨1931829, by rfl⟩ : syracuseStep 5151545 = 3863659) B3863659
theorem B14654267 : Blo 1524459 14654267 := bstep (se 1 (by rfl) ⟨10990700, by rfl⟩ : syracuseStep 14654267 = 21981401) B21981401
theorem B5872591 : Blo 1524459 5872591 := bstep (se 1 (by rfl) ⟨4404443, by rfl⟩ : syracuseStep 5872591 = 8808887) B8808887
theorem B65977415 : Blo 1524459 65977415 := bstep (se 1 (by rfl) ⟨49483061, by rfl⟩ : syracuseStep 65977415 = 98966123) B98966123
theorem B10574945 : Blo 1524459 10574945 := bstep (se 2 (by rfl) ⟨3965604, by rfl⟩ : syracuseStep 10574945 = 7931209) B7931209
theorem B24738995 : Blo 1524459 24738995 := bstep (se 1 (by rfl) ⟨18554246, by rfl⟩ : syracuseStep 24738995 = 37108493) B37108493
theorem B13917521 : Blo 1524459 13917521 := bstep (se 2 (by rfl) ⟨5219070, by rfl⟩ : syracuseStep 13917521 = 10438141) B10438141
theorem B5791085 : Blo 1524459 5791085 := bstep (se 3 (by rfl) ⟨1085828, by rfl⟩ : syracuseStep 5791085 = 2171657) B2171657
theorem B7724483 : Blo 1524459 7724483 := bstep (se 1 (by rfl) ⟨5793362, by rfl⟩ : syracuseStep 7724483 = 11586725) B11586725
theorem B8682983 : Blo 1524459 8682983 := bstep (se 1 (by rfl) ⟨6512237, by rfl⟩ : syracuseStep 8682983 = 13024475) B13024475
theorem B6602303 : Blo 1524459 6602303 := bstep (se 1 (by rfl) ⟨4951727, by rfl⟩ : syracuseStep 6602303 = 9903455) B9903455
theorem B9273041 : Blo 1524459 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B3432347 : Blo 1524459 3432347 := bstep (se 1 (by rfl) ⟨2574260, by rfl⟩ : syracuseStep 3432347 = 5148521) B5148521
theorem B25076135 : Blo 1524459 25076135 := bstep (se 1 (by rfl) ⟨18807101, by rfl⟩ : syracuseStep 25076135 = 37614203) B37614203
theorem B4342187 : Blo 1524459 4342187 := bstep (se 1 (by rfl) ⟨3256640, by rfl⟩ : syracuseStep 4342187 = 6513281) B6513281
theorem B75260335 : Blo 1524459 75260335 := bstep (se 1 (by rfl) ⟨56445251, by rfl⟩ : syracuseStep 75260335 = 112890503) B112890503
theorem B1524475 : Blo 1524459 1524475 := bstep (se 1 (by rfl) ⟨1143356, by rfl⟩ : syracuseStep 1524475 = 2286713) B2286713
theorem B7332727 : Blo 1524459 7332727 := bstep (se 1 (by rfl) ⟨5499545, by rfl⟩ : syracuseStep 7332727 = 10999091) B10999091
theorem B8807297 : Blo 1524459 8807297 := bstep (se 2 (by rfl) ⟨3302736, by rfl⟩ : syracuseStep 8807297 = 6605473) B6605473
theorem B2286695 : Blo 1524459 2286695 := bstep (se 1 (by rfl) ⟨1715021, by rfl⟩ : syracuseStep 2286695 = 3430043) B3430043
theorem B7726265 : Blo 1524459 7726265 := bstep (se 2 (by rfl) ⟨2897349, by rfl⟩ : syracuseStep 7726265 = 5794699) B5794699
theorem B24741071 : Blo 1524459 24741071 := bstep (se 1 (by rfl) ⟨18555803, by rfl⟩ : syracuseStep 24741071 = 37111607) B37111607
theorem B3433697 : Blo 1524459 3433697 := bstep (se 2 (by rfl) ⟨1287636, by rfl⟩ : syracuseStep 3433697 = 2575273) B2575273
theorem B2286827 : Blo 1524459 2286827 := bstep (se 1 (by rfl) ⟨1715120, by rfl⟩ : syracuseStep 2286827 = 3430241) B3430241
theorem B1525055 : Blo 1524459 1525055 := bstep (se 1 (by rfl) ⟨1143791, by rfl⟩ : syracuseStep 1525055 = 2287583) B2287583
theorem B1525063 : Blo 1524459 1525063 := bstep (se 1 (by rfl) ⟨1143797, by rfl⟩ : syracuseStep 1525063 = 2287595) B2287595
theorem B1525095 : Blo 1524459 1525095 := bstep (se 1 (by rfl) ⟨1143821, by rfl⟩ : syracuseStep 1525095 = 2287643) B2287643
theorem B8471915 : Blo 1524459 8471915 := bstep (se 1 (by rfl) ⟨6353936, by rfl⟩ : syracuseStep 8471915 = 12707873) B12707873
theorem B2286959 : Blo 1524459 2286959 := bstep (se 1 (by rfl) ⟨1715219, by rfl⟩ : syracuseStep 2286959 = 3430439) B3430439
theorem B7718327 : Blo 1524459 7718327 := bstep (se 1 (by rfl) ⟨5788745, by rfl⟩ : syracuseStep 7718327 = 11577491) B11577491
theorem B2287079 : Blo 1524459 2287079 := bstep (se 1 (by rfl) ⟨1715309, by rfl⟩ : syracuseStep 2287079 = 3430619) B3430619
theorem B1525339 : Blo 1524459 1525339 := bstep (se 1 (by rfl) ⟨1144004, by rfl⟩ : syracuseStep 1525339 = 2288009) B2288009
theorem B2287211 : Blo 1524459 2287211 := bstep (se 1 (by rfl) ⟨1715408, by rfl⟩ : syracuseStep 2287211 = 3430817) B3430817
theorem B3860075 : Blo 1524459 3860075 := bstep (se 1 (by rfl) ⟨2895056, by rfl⟩ : syracuseStep 3860075 = 5790113) B5790113
theorem B2287259 : Blo 1524459 2287259 := bstep (se 1 (by rfl) ⟨1715444, by rfl⟩ : syracuseStep 2287259 = 3430889) B3430889
theorem B3303083 : Blo 1524459 3303083 := bstep (se 1 (by rfl) ⟨2477312, by rfl⟩ : syracuseStep 3303083 = 4954625) B4954625
theorem B8251091 : Blo 1524459 8251091 := bstep (se 1 (by rfl) ⟨6188318, by rfl⟩ : syracuseStep 8251091 = 12376637) B12376637
theorem B3303251 : Blo 1524459 3303251 := bstep (se 1 (by rfl) ⟨2477438, by rfl⟩ : syracuseStep 3303251 = 4954877) B4954877
theorem B2287481 : Blo 1524459 2287481 := bstep (se 2 (by rfl) ⟨857805, by rfl⟩ : syracuseStep 2287481 = 1715611) B1715611
theorem B3434363 : Blo 1524459 3434363 := bstep (se 1 (by rfl) ⟨2575772, by rfl⟩ : syracuseStep 3434363 = 5151545) B5151545
theorem B10995689 : Blo 1524459 10995689 := bstep (se 2 (by rfl) ⟨4123383, by rfl⟩ : syracuseStep 10995689 = 8246767) B8246767
theorem B43984943 : Blo 1524459 43984943 := bstep (se 1 (by rfl) ⟨32988707, by rfl⟩ : syracuseStep 43984943 = 65977415) B65977415
theorem B16492663 : Blo 1524459 16492663 := bstep (se 1 (by rfl) ⟨12369497, by rfl⟩ : syracuseStep 16492663 = 24738995) B24738995
theorem B79300727 : Blo 1524459 79300727 := bstep (se 1 (by rfl) ⟨59475545, by rfl⟩ : syracuseStep 79300727 = 118951091) B118951091
theorem B1525967 : Blo 1524459 1525967 := bstep (se 1 (by rfl) ⟨1144475, by rfl⟩ : syracuseStep 1525967 = 2288951) B2288951
theorem B3860723 : Blo 1524459 3860723 := bstep (se 1 (by rfl) ⟨2895542, by rfl⟩ : syracuseStep 3860723 = 5791085) B5791085
theorem B1526079 : Blo 1524459 1526079 := bstep (se 1 (by rfl) ⟨1144559, by rfl⟩ : syracuseStep 1526079 = 2289119) B2289119
theorem B4401535 : Blo 1524459 4401535 := bstep (se 1 (by rfl) ⟨3301151, by rfl⟩ : syracuseStep 4401535 = 6602303) B6602303
theorem B3860905 : Blo 1524459 3860905 := bstep (se 2 (by rfl) ⟨1447839, by rfl⟩ : syracuseStep 3860905 = 2895679) B2895679
theorem B7727561 : Blo 1524459 7727561 := bstep (se 2 (by rfl) ⟨2897835, by rfl⟩ : syracuseStep 7727561 = 5795671) B5795671
theorem B1526223 : Blo 1524459 1526223 := bstep (se 1 (by rfl) ⟨1144667, by rfl⟩ : syracuseStep 1526223 = 2289335) B2289335
theorem B1526363 : Blo 1524459 1526363 := bstep (se 1 (by rfl) ⟨1144772, by rfl⟩ : syracuseStep 1526363 = 2289545) B2289545
theorem B2288231 : Blo 1524459 2288231 := bstep (se 1 (by rfl) ⟨1716173, by rfl⟩ : syracuseStep 2288231 = 3432347) B3432347
theorem B5147279 : Blo 1524459 5147279 := bstep (se 1 (by rfl) ⟨3860459, by rfl⟩ : syracuseStep 5147279 = 7720919) B7720919
theorem B7719785 : Blo 1524459 7719785 := bstep (se 2 (by rfl) ⟨2894919, by rfl⟩ : syracuseStep 7719785 = 5789839) B5789839
theorem B3861371 : Blo 1524459 3861371 := bstep (se 1 (by rfl) ⟨2896028, by rfl⟩ : syracuseStep 3861371 = 5792057) B5792057
theorem B2288507 : Blo 1524459 2288507 := bstep (se 1 (by rfl) ⟨1716380, by rfl⟩ : syracuseStep 2288507 = 3432761) B3432761
theorem B1715143 : Blo 1524459 1715143 := bstep (se 1 (by rfl) ⟨1286357, by rfl⟩ : syracuseStep 1715143 = 2572715) B2572715
theorem B2575327 : Blo 1524459 2575327 := bstep (se 1 (by rfl) ⟨1931495, by rfl⟩ : syracuseStep 2575327 = 3862991) B3862991
theorem B5147657 : Blo 1524459 5147657 := bstep (se 2 (by rfl) ⟨1930371, by rfl⟩ : syracuseStep 5147657 = 3860743) B3860743
theorem B2288777 : Blo 1524459 2288777 := bstep (se 2 (by rfl) ⟨858291, by rfl⟩ : syracuseStep 2288777 = 1716583) B1716583
theorem B17386649 : Blo 1524459 17386649 := bstep (se 2 (by rfl) ⟨6519993, by rfl⟩ : syracuseStep 17386649 = 13039987) B13039987
theorem B3861695 : Blo 1524459 3861695 := bstep (se 1 (by rfl) ⟨2896271, by rfl⟩ : syracuseStep 3861695 = 5792543) B5792543
theorem B2288831 : Blo 1524459 2288831 := bstep (se 1 (by rfl) ⟨1716623, by rfl⟩ : syracuseStep 2288831 = 3433247) B3433247
theorem B1715503 : Blo 1524459 1715503 := bstep (se 1 (by rfl) ⟨1286627, by rfl⟩ : syracuseStep 1715503 = 2573255) B2573255
theorem B10988855 : Blo 1524459 10988855 := bstep (se 1 (by rfl) ⟨8241641, by rfl⟩ : syracuseStep 10988855 = 16483283) B16483283
theorem B5148251 : Blo 1524459 5148251 := bstep (se 1 (by rfl) ⟨3861188, by rfl⟩ : syracuseStep 5148251 = 7722377) B7722377
theorem B2289371 : Blo 1524459 2289371 := bstep (se 1 (by rfl) ⟨1717028, by rfl⟩ : syracuseStep 2289371 = 3434057) B3434057
theorem B3862343 : Blo 1524459 3862343 := bstep (se 1 (by rfl) ⟨2896757, by rfl⟩ : syracuseStep 3862343 = 5793515) B5793515
theorem B1716079 : Blo 1524459 1716079 := bstep (se 1 (by rfl) ⟨1287059, by rfl⟩ : syracuseStep 1716079 = 2574119) B2574119
theorem B9768919 : Blo 1524459 9768919 := bstep (se 1 (by rfl) ⟨7326689, by rfl⟩ : syracuseStep 9768919 = 14653379) B14653379
theorem B6516713 : Blo 1524459 6516713 := bstep (se 2 (by rfl) ⟨2443767, by rfl⟩ : syracuseStep 6516713 = 4887535) B4887535
theorem B2289641 : Blo 1524459 2289641 := bstep (se 2 (by rfl) ⟨858615, by rfl⟩ : syracuseStep 2289641 = 1717231) B1717231
theorem B2289659 : Blo 1524459 2289659 := bstep (se 1 (by rfl) ⟨1717244, by rfl⟩ : syracuseStep 2289659 = 3434489) B3434489
theorem B3862667 : Blo 1524459 3862667 := bstep (se 1 (by rfl) ⟨2897000, by rfl⟩ : syracuseStep 3862667 = 5794001) B5794001
theorem B5149115 : Blo 1524459 5149115 := bstep (se 1 (by rfl) ⟨3861836, by rfl⟩ : syracuseStep 5149115 = 7723673) B7723673
theorem B1716763 : Blo 1524459 1716763 := bstep (se 1 (by rfl) ⟨1287572, by rfl⟩ : syracuseStep 1716763 = 2575145) B2575145
theorem B9769511 : Blo 1524459 9769511 := bstep (se 1 (by rfl) ⟨7327133, by rfl⟩ : syracuseStep 9769511 = 14654267) B14654267
theorem B1716943 : Blo 1524459 1716943 := bstep (se 1 (by rfl) ⟨1287707, by rfl⟩ : syracuseStep 1716943 = 2575415) B2575415
theorem B7049963 : Blo 1524459 7049963 := bstep (se 1 (by rfl) ⟨5287472, by rfl⟩ : syracuseStep 7049963 = 10574945) B10574945
theorem B2749211 : Blo 1524459 2749211 := bstep (se 1 (by rfl) ⟨2061908, by rfl⟩ : syracuseStep 2749211 = 4123817) B4123817
theorem B9278347 : Blo 1524459 9278347 := bstep (se 1 (by rfl) ⟨6958760, by rfl⟩ : syracuseStep 9278347 = 13917521) B13917521
theorem B10990495 : Blo 1524459 10990495 := bstep (se 1 (by rfl) ⟨8242871, by rfl⟩ : syracuseStep 10990495 = 16485743) B16485743
theorem B5149655 : Blo 1524459 5149655 := bstep (se 1 (by rfl) ⟨3862241, by rfl⟩ : syracuseStep 5149655 = 7724483) B7724483
theorem B5788655 : Blo 1524459 5788655 := bstep (se 1 (by rfl) ⟨4341491, by rfl⟩ : syracuseStep 5788655 = 8682983) B8682983
theorem B6182027 : Blo 1524459 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B7329305 : Blo 1524459 7329305 := bstep (se 2 (by rfl) ⟨2748489, by rfl⟩ : syracuseStep 7329305 = 5496979) B5496979
theorem B3430079 : Blo 1524459 3430079 := bstep (se 1 (by rfl) ⟨2572559, by rfl⟩ : syracuseStep 3430079 = 5145119) B5145119
theorem B10442459 : Blo 1524459 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B7829543 : Blo 1524459 7829543 := bstep (se 1 (by rfl) ⟨5872157, by rfl⟩ : syracuseStep 7829543 = 11744315) B11744315
theorem B6183307 : Blo 1524459 6183307 := bstep (se 1 (by rfl) ⟨4637480, by rfl⟩ : syracuseStep 6183307 = 9274961) B9274961
theorem B2062751 : Blo 1524459 2062751 := bstep (se 1 (by rfl) ⟨1547063, by rfl⟩ : syracuseStep 2062751 = 3094127) B3094127
theorem B17619443 : Blo 1524459 17619443 := bstep (se 1 (by rfl) ⟨13214582, by rfl⟩ : syracuseStep 17619443 = 26429165) B26429165
theorem B7830121 : Blo 1524459 7830121 := bstep (se 2 (by rfl) ⟨2936295, by rfl⟩ : syracuseStep 7830121 = 5872591) B5872591
theorem B171530887 : Blo 1524459 171530887 := bstep (se 1 (by rfl) ⟨128648165, by rfl⟩ : syracuseStep 171530887 = 257296331) B257296331
theorem B3431231 : Blo 1524459 3431231 := bstep (se 1 (by rfl) ⟨2573423, by rfl⟩ : syracuseStep 3431231 = 5146847) B5146847
theorem B9771995 : Blo 1524459 9771995 := bstep (se 1 (by rfl) ⟨7328996, by rfl⟩ : syracuseStep 9771995 = 14657993) B14657993
theorem B66862297 : Blo 1524459 66862297 := bstep (se 2 (by rfl) ⟨25073361, by rfl⟩ : syracuseStep 66862297 = 50146723) B50146723
theorem B3431807 : Blo 1524459 3431807 := bstep (se 1 (by rfl) ⟨2573855, by rfl⟩ : syracuseStep 3431807 = 5147711) B5147711
theorem B4341377 : Blo 1524459 4341377 := bstep (se 2 (by rfl) ⟨1628016, by rfl⟩ : syracuseStep 4341377 = 3256033) B3256033
theorem B7724969 : Blo 1524459 7724969 := bstep (se 2 (by rfl) ⟨2896863, by rfl⟩ : syracuseStep 7724969 = 5793727) B5793727
theorem B3432743 : Blo 1524459 3432743 := bstep (se 1 (by rfl) ⟨2574557, by rfl⟩ : syracuseStep 3432743 = 5149115) B5149115
theorem B6513007 : Blo 1524459 6513007 := bstep (se 1 (by rfl) ⟨4884755, by rfl⟩ : syracuseStep 6513007 = 9769511) B9769511
theorem B3433103 : Blo 1524459 3433103 := bstep (se 1 (by rfl) ⟨2574827, by rfl⟩ : syracuseStep 3433103 = 5149655) B5149655
theorem B3859103 : Blo 1524459 3859103 := bstep (se 1 (by rfl) ⟨2894327, by rfl⟩ : syracuseStep 3859103 = 5788655) B5788655
theorem B1524463 : Blo 1524459 1524463 := bstep (se 1 (by rfl) ⟨1143347, by rfl⟩ : syracuseStep 1524463 = 2286695) B2286695
theorem B4121351 : Blo 1524459 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B1524551 : Blo 1524459 1524551 := bstep (se 1 (by rfl) ⟨1143413, by rfl⟩ : syracuseStep 1524551 = 2286827) B2286827
theorem B1524639 : Blo 1524459 1524639 := bstep (se 1 (by rfl) ⟨1143479, by rfl⟩ : syracuseStep 1524639 = 2286959) B2286959
theorem B5145551 : Blo 1524459 5145551 := bstep (se 1 (by rfl) ⟨3859163, by rfl⟩ : syracuseStep 5145551 = 7718327) B7718327
theorem B1524719 : Blo 1524459 1524719 := bstep (se 1 (by rfl) ⟨1143539, by rfl⟩ : syracuseStep 1524719 = 2287079) B2287079
theorem B1524807 : Blo 1524459 1524807 := bstep (se 1 (by rfl) ⟨1143605, by rfl⟩ : syracuseStep 1524807 = 2287211) B2287211
theorem B2573383 : Blo 1524459 2573383 := bstep (se 1 (by rfl) ⟨1930037, by rfl⟩ : syracuseStep 2573383 = 3860075) B3860075
theorem B1524839 : Blo 1524459 1524839 := bstep (se 1 (by rfl) ⟨1143629, by rfl⟩ : syracuseStep 1524839 = 2287259) B2287259
theorem B2286719 : Blo 1524459 2286719 := bstep (se 1 (by rfl) ⟨1715039, by rfl⟩ : syracuseStep 2286719 = 3430079) B3430079
theorem B12371129 : Blo 1524459 12371129 := bstep (se 2 (by rfl) ⟨4639173, by rfl⟩ : syracuseStep 12371129 = 9278347) B9278347
theorem B1524987 : Blo 1524459 1524987 := bstep (se 1 (by rfl) ⟨1143740, by rfl⟩ : syracuseStep 1524987 = 2287481) B2287481
theorem B2286857 : Blo 1524459 2286857 := bstep (se 2 (by rfl) ⟨857571, by rfl⟩ : syracuseStep 2286857 = 1715143) B1715143
theorem B3433769 : Blo 1524459 3433769 := bstep (se 2 (by rfl) ⟨1287663, by rfl⟩ : syracuseStep 3433769 = 2575327) B2575327
theorem B2573815 : Blo 1524459 2573815 := bstep (se 1 (by rfl) ⟨1930361, by rfl⟩ : syracuseStep 2573815 = 3860723) B3860723
theorem B11577005 : Blo 1524459 11577005 := bstep (se 3 (by rfl) ⟨2170688, by rfl⟩ : syracuseStep 11577005 = 4341377) B4341377
theorem B2287337 : Blo 1524459 2287337 := bstep (se 2 (by rfl) ⟨857751, by rfl⟩ : syracuseStep 2287337 = 1715503) B1715503
theorem B1525487 : Blo 1524459 1525487 := bstep (se 1 (by rfl) ⟨1144115, by rfl⟩ : syracuseStep 1525487 = 2288231) B2288231
theorem B2287487 : Blo 1524459 2287487 := bstep (se 1 (by rfl) ⟨1715615, by rfl⟩ : syracuseStep 2287487 = 3431231) B3431231
theorem B5146523 : Blo 1524459 5146523 := bstep (se 1 (by rfl) ⟨3859892, by rfl⟩ : syracuseStep 5146523 = 7719785) B7719785
theorem B2574247 : Blo 1524459 2574247 := bstep (se 1 (by rfl) ⟨1930685, by rfl⟩ : syracuseStep 2574247 = 3861371) B3861371
theorem B1525671 : Blo 1524459 1525671 := bstep (se 1 (by rfl) ⟨1144253, by rfl⟩ : syracuseStep 1525671 = 2288507) B2288507
theorem B6514663 : Blo 1524459 6514663 := bstep (se 1 (by rfl) ⟨4885997, by rfl⟩ : syracuseStep 6514663 = 9771995) B9771995
theorem B1525851 : Blo 1524459 1525851 := bstep (se 1 (by rfl) ⟨1144388, by rfl⟩ : syracuseStep 1525851 = 2288777) B2288777
theorem B2574463 : Blo 1524459 2574463 := bstep (se 1 (by rfl) ⟨1930847, by rfl⟩ : syracuseStep 2574463 = 3861695) B3861695
theorem B1525887 : Blo 1524459 1525887 := bstep (se 1 (by rfl) ⟨1144415, by rfl⟩ : syracuseStep 1525887 = 2288831) B2288831
theorem B58615973 : Blo 1524459 58615973 := bstep (se 4 (by rfl) ⟨5495247, by rfl⟩ : syracuseStep 58615973 = 10990495) B10990495
theorem B7325903 : Blo 1524459 7325903 := bstep (se 1 (by rfl) ⟨5494427, by rfl⟩ : syracuseStep 7325903 = 10988855) B10988855
theorem B2287871 : Blo 1524459 2287871 := bstep (se 1 (by rfl) ⟨1715903, by rfl⟩ : syracuseStep 2287871 = 3431807) B3431807
theorem B1526247 : Blo 1524459 1526247 := bstep (se 1 (by rfl) ⟨1144685, by rfl⟩ : syracuseStep 1526247 = 2289371) B2289371
theorem B2288105 : Blo 1524459 2288105 := bstep (se 2 (by rfl) ⟨858039, by rfl⟩ : syracuseStep 2288105 = 1716079) B1716079
theorem B2574895 : Blo 1524459 2574895 := bstep (se 1 (by rfl) ⟨1931171, by rfl⟩ : syracuseStep 2574895 = 3862343) B3862343
theorem B17377901 : Blo 1524459 17377901 := bstep (se 3 (by rfl) ⟨3258356, by rfl⟩ : syracuseStep 17377901 = 6516713) B6516713
theorem B1526427 : Blo 1524459 1526427 := bstep (se 1 (by rfl) ⟨1144820, by rfl⟩ : syracuseStep 1526427 = 2289641) B2289641
theorem B1526439 : Blo 1524459 1526439 := bstep (se 1 (by rfl) ⟨1144829, by rfl⟩ : syracuseStep 1526439 = 2289659) B2289659
theorem B2575111 : Blo 1524459 2575111 := bstep (se 1 (by rfl) ⟨1931333, by rfl⟩ : syracuseStep 2575111 = 3862667) B3862667
theorem B21990217 : Blo 1524459 21990217 := bstep (se 2 (by rfl) ⟨8246331, by rfl⟩ : syracuseStep 21990217 = 16492663) B16492663
theorem B2894791 : Blo 1524459 2894791 := bstep (se 1 (by rfl) ⟨2171093, by rfl⟩ : syracuseStep 2894791 = 4342187) B4342187
theorem B5868713 : Blo 1524459 5868713 := bstep (se 2 (by rfl) ⟨2200767, by rfl⟩ : syracuseStep 5868713 = 4401535) B4401535
theorem B5147873 : Blo 1524459 5147873 := bstep (se 2 (by rfl) ⟨1930452, by rfl⟩ : syracuseStep 5147873 = 3860905) B3860905
theorem B100347113 : Blo 1524459 100347113 := bstep (se 2 (by rfl) ⟨37630167, by rfl⟩ : syracuseStep 100347113 = 75260335) B75260335
theorem B2289017 : Blo 1524459 2289017 := bstep (se 2 (by rfl) ⟨858381, by rfl⟩ : syracuseStep 2289017 = 1716763) B1716763
theorem B16494047 : Blo 1524459 16494047 := bstep (se 1 (by rfl) ⟨12370535, by rfl⟩ : syracuseStep 16494047 = 24741071) B24741071
theorem B10440161 : Blo 1524459 10440161 := bstep (se 2 (by rfl) ⟨3915060, by rfl⟩ : syracuseStep 10440161 = 7830121) B7830121
theorem B2289131 : Blo 1524459 2289131 := bstep (se 1 (by rfl) ⟨1716848, by rfl⟩ : syracuseStep 2289131 = 3433697) B3433697
theorem B228707849 : Blo 1524459 228707849 := bstep (se 2 (by rfl) ⟨85765443, by rfl⟩ : syracuseStep 228707849 = 171530887) B171530887
theorem B5647943 : Blo 1524459 5647943 := bstep (se 1 (by rfl) ⟨4235957, by rfl⟩ : syracuseStep 5647943 = 8471915) B8471915
theorem B2289257 : Blo 1524459 2289257 := bstep (se 2 (by rfl) ⟨858471, by rfl⟩ : syracuseStep 2289257 = 1716943) B1716943
theorem B4886203 : Blo 1524459 4886203 := bstep (se 1 (by rfl) ⟨3664652, by rfl⟩ : syracuseStep 4886203 = 7329305) B7329305
theorem B5500727 : Blo 1524459 5500727 := bstep (se 1 (by rfl) ⟨4125545, by rfl⟩ : syracuseStep 5500727 = 8251091) B8251091
theorem B9776969 : Blo 1524459 9776969 := bstep (se 2 (by rfl) ⟨3666363, by rfl⟩ : syracuseStep 9776969 = 7332727) B7332727
theorem B2289575 : Blo 1524459 2289575 := bstep (se 1 (by rfl) ⟨1717181, by rfl⟩ : syracuseStep 2289575 = 3434363) B3434363
theorem B29323295 : Blo 1524459 29323295 := bstep (se 1 (by rfl) ⟨21992471, by rfl⟩ : syracuseStep 29323295 = 43984943) B43984943
theorem B52867151 : Blo 1524459 52867151 := bstep (se 1 (by rfl) ⟨39650363, by rfl⟩ : syracuseStep 52867151 = 79300727) B79300727
theorem B89149729 : Blo 1524459 89149729 := bstep (se 2 (by rfl) ⟨33431148, by rfl⟩ : syracuseStep 89149729 = 66862297) B66862297
theorem B32977637 : Blo 1524459 32977637 := bstep (se 4 (by rfl) ⟨3091653, by rfl⟩ : syracuseStep 32977637 = 6183307) B6183307
theorem B5149979 : Blo 1524459 5149979 := bstep (se 1 (by rfl) ⟨3862484, by rfl⟩ : syracuseStep 5149979 = 7724969) B7724969
theorem B20878781 : Blo 1524459 20878781 := bstep (se 3 (by rfl) ⟨3914771, by rfl⟩ : syracuseStep 20878781 = 7829543) B7829543
theorem B16717423 : Blo 1524459 16717423 := bstep (se 1 (by rfl) ⟨12538067, by rfl⟩ : syracuseStep 16717423 = 25076135) B25076135
theorem B1832807 : Blo 1524459 1832807 := bstep (se 1 (by rfl) ⟨1374605, by rfl⟩ : syracuseStep 1832807 = 2749211) B2749211
theorem B5150843 : Blo 1524459 5150843 := bstep (se 1 (by rfl) ⟨3863132, by rfl⟩ : syracuseStep 5150843 = 7726265) B7726265
theorem B2202055 : Blo 1524459 2202055 := bstep (se 1 (by rfl) ⟨1651541, by rfl⟩ : syracuseStep 2202055 = 3303083) B3303083
theorem B6961639 : Blo 1524459 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B2202167 : Blo 1524459 2202167 := bstep (se 1 (by rfl) ⟨1651625, by rfl⟩ : syracuseStep 2202167 = 3303251) B3303251
theorem B7330459 : Blo 1524459 7330459 := bstep (se 1 (by rfl) ⟨5497844, by rfl⟩ : syracuseStep 7330459 = 10995689) B10995689
theorem B5151707 : Blo 1524459 5151707 := bstep (se 1 (by rfl) ⟨3863780, by rfl⟩ : syracuseStep 5151707 = 7727561) B7727561
theorem B22002677 : Blo 1524459 22002677 := bstep (se 5 (by rfl) ⟨1031375, by rfl⟩ : syracuseStep 22002677 = 2062751) B2062751
theorem B11746295 : Blo 1524459 11746295 := bstep (se 1 (by rfl) ⟨8809721, by rfl⟩ : syracuseStep 11746295 = 17619443) B17619443
theorem B3431519 : Blo 1524459 3431519 := bstep (se 1 (by rfl) ⟨2573639, by rfl⟩ : syracuseStep 3431519 = 5147279) B5147279
theorem B18799901 : Blo 1524459 18799901 := bstep (se 3 (by rfl) ⟨3524981, by rfl⟩ : syracuseStep 18799901 = 7049963) B7049963
theorem B3431771 : Blo 1524459 3431771 := bstep (se 1 (by rfl) ⟨2573828, by rfl⟩ : syracuseStep 3431771 = 5147657) B5147657
theorem B11591099 : Blo 1524459 11591099 := bstep (se 1 (by rfl) ⟨8693324, by rfl⟩ : syracuseStep 11591099 = 17386649) B17386649
theorem B23486125 : Blo 1524459 23486125 := bstep (se 3 (by rfl) ⟨4403648, by rfl⟩ : syracuseStep 23486125 = 8807297) B8807297
theorem B3432167 : Blo 1524459 3432167 := bstep (se 1 (by rfl) ⟨2574125, by rfl⟩ : syracuseStep 3432167 = 5148251) B5148251
theorem B13025225 : Blo 1524459 13025225 := bstep (se 2 (by rfl) ⟨4884459, by rfl⟩ : syracuseStep 13025225 = 9768919) B9768919
theorem B3432617 : Blo 1524459 3432617 := bstep (se 2 (by rfl) ⟨1287231, by rfl⟩ : syracuseStep 3432617 = 2574463) B2574463
theorem B118866305 : Blo 1524459 118866305 := bstep (se 2 (by rfl) ⟨44574864, by rfl⟩ : syracuseStep 118866305 = 89149729) B89149729
theorem B2572735 : Blo 1524459 2572735 := bstep (se 1 (by rfl) ⟨1929551, by rfl⟩ : syracuseStep 2572735 = 3859103) B3859103
theorem B8684009 : Blo 1524459 8684009 := bstep (se 2 (by rfl) ⟨3256503, by rfl⟩ : syracuseStep 8684009 = 6513007) B6513007
theorem B9282185 : Blo 1524459 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B3433193 : Blo 1524459 3433193 := bstep (se 2 (by rfl) ⟨1287447, by rfl⟩ : syracuseStep 3433193 = 2574895) B2574895
theorem B1524479 : Blo 1524459 1524479 := bstep (se 1 (by rfl) ⟨1143359, by rfl⟩ : syracuseStep 1524479 = 2286719) B2286719
theorem B1524571 : Blo 1524459 1524571 := bstep (se 1 (by rfl) ⟨1143428, by rfl⟩ : syracuseStep 1524571 = 2286857) B2286857
theorem B3433319 : Blo 1524459 3433319 := bstep (se 1 (by rfl) ⟨2574989, by rfl⟩ : syracuseStep 3433319 = 5149979) B5149979
theorem B9773945 : Blo 1524459 9773945 := bstep (se 2 (by rfl) ⟨3665229, by rfl⟩ : syracuseStep 9773945 = 7330459) B7330459
theorem B3433481 : Blo 1524459 3433481 := bstep (se 2 (by rfl) ⟨1287555, by rfl⟩ : syracuseStep 3433481 = 2575111) B2575111
theorem B29320289 : Blo 1524459 29320289 := bstep (se 2 (by rfl) ⟨10995108, by rfl⟩ : syracuseStep 29320289 = 21990217) B21990217
theorem B7718003 : Blo 1524459 7718003 := bstep (se 1 (by rfl) ⟨5788502, by rfl⟩ : syracuseStep 7718003 = 11577005) B11577005
theorem B1524891 : Blo 1524459 1524891 := bstep (se 1 (by rfl) ⟨1143668, by rfl⟩ : syracuseStep 1524891 = 2287337) B2287337
theorem B1524991 : Blo 1524459 1524991 := bstep (se 1 (by rfl) ⟨1143743, by rfl⟩ : syracuseStep 1524991 = 2287487) B2287487
theorem B3859721 : Blo 1524459 3859721 := bstep (se 2 (by rfl) ⟨1447395, by rfl⟩ : syracuseStep 3859721 = 2894791) B2894791
theorem B3433895 : Blo 1524459 3433895 := bstep (se 1 (by rfl) ⟨2575421, by rfl⟩ : syracuseStep 3433895 = 5150843) B5150843
theorem B39077315 : Blo 1524459 39077315 := bstep (se 1 (by rfl) ⟨29307986, by rfl⟩ : syracuseStep 39077315 = 58615973) B58615973
theorem B1525247 : Blo 1524459 1525247 := bstep (se 1 (by rfl) ⟨1143935, by rfl⟩ : syracuseStep 1525247 = 2287871) B2287871
theorem B1525403 : Blo 1524459 1525403 := bstep (se 1 (by rfl) ⟨1144052, by rfl⟩ : syracuseStep 1525403 = 2288105) B2288105
theorem B11585267 : Blo 1524459 11585267 := bstep (se 1 (by rfl) ⟨8688950, by rfl⟩ : syracuseStep 11585267 = 17377901) B17377901
theorem B3434471 : Blo 1524459 3434471 := bstep (se 1 (by rfl) ⟨2575853, by rfl⟩ : syracuseStep 3434471 = 5151707) B5151707
theorem B2287679 : Blo 1524459 2287679 := bstep (se 1 (by rfl) ⟨1715759, by rfl⟩ : syracuseStep 2287679 = 3431519) B3431519
theorem B66898075 : Blo 1524459 66898075 := bstep (se 1 (by rfl) ⟨50173556, by rfl⟩ : syracuseStep 66898075 = 100347113) B100347113
theorem B2287847 : Blo 1524459 2287847 := bstep (se 1 (by rfl) ⟨1715885, by rfl⟩ : syracuseStep 2287847 = 3431771) B3431771
theorem B6514937 : Blo 1524459 6514937 := bstep (se 2 (by rfl) ⟨2443101, by rfl⟩ : syracuseStep 6514937 = 4886203) B4886203
theorem B1526011 : Blo 1524459 1526011 := bstep (se 1 (by rfl) ⟨1144508, by rfl⟩ : syracuseStep 1526011 = 2289017) B2289017
theorem B7727399 : Blo 1524459 7727399 := bstep (se 1 (by rfl) ⟨5795549, by rfl⟩ : syracuseStep 7727399 = 11591099) B11591099
theorem B10996031 : Blo 1524459 10996031 := bstep (se 1 (by rfl) ⟨8247023, by rfl⟩ : syracuseStep 10996031 = 16494047) B16494047
theorem B1526087 : Blo 1524459 1526087 := bstep (se 1 (by rfl) ⟨1144565, by rfl⟩ : syracuseStep 1526087 = 2289131) B2289131
theorem B152471899 : Blo 1524459 152471899 := bstep (se 1 (by rfl) ⟨114353924, by rfl⟩ : syracuseStep 152471899 = 228707849) B228707849
theorem B1526171 : Blo 1524459 1526171 := bstep (se 1 (by rfl) ⟨1144628, by rfl⟩ : syracuseStep 1526171 = 2289257) B2289257
theorem B2288111 : Blo 1524459 2288111 := bstep (se 1 (by rfl) ⟨1716083, by rfl⟩ : syracuseStep 2288111 = 3432167) B3432167
theorem B1526383 : Blo 1524459 1526383 := bstep (se 1 (by rfl) ⟨1144787, by rfl⟩ : syracuseStep 1526383 = 2289575) B2289575
theorem B8686217 : Blo 1524459 8686217 := bstep (se 2 (by rfl) ⟨3257331, by rfl⟩ : syracuseStep 8686217 = 6514663) B6514663
theorem B19548863 : Blo 1524459 19548863 := bstep (se 1 (by rfl) ⟨14661647, by rfl⟩ : syracuseStep 19548863 = 29323295) B29323295
theorem B35244767 : Blo 1524459 35244767 := bstep (se 1 (by rfl) ⟨26433575, by rfl⟩ : syracuseStep 35244767 = 52867151) B52867151
theorem B2288495 : Blo 1524459 2288495 := bstep (se 1 (by rfl) ⟨1716371, by rfl⟩ : syracuseStep 2288495 = 3432743) B3432743
theorem B2288735 : Blo 1524459 2288735 := bstep (se 1 (by rfl) ⟨1716551, by rfl⟩ : syracuseStep 2288735 = 3433103) B3433103
theorem B2747567 : Blo 1524459 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B2289179 : Blo 1524459 2289179 := bstep (se 1 (by rfl) ⟨1716884, by rfl⟩ : syracuseStep 2289179 = 3433769) B3433769
theorem B55676749 : Blo 1524459 55676749 := bstep (se 3 (by rfl) ⟨10439390, by rfl⟩ : syracuseStep 55676749 = 20878781) B20878781
theorem B14668451 : Blo 1524459 14668451 := bstep (se 1 (by rfl) ⟨11001338, by rfl⟩ : syracuseStep 14668451 = 22002677) B22002677
theorem B3912475 : Blo 1524459 3912475 := bstep (se 1 (by rfl) ⟨2934356, by rfl⟩ : syracuseStep 3912475 = 5868713) B5868713
theorem B31314833 : Blo 1524459 31314833 := bstep (se 2 (by rfl) ⟨11743062, by rfl⟩ : syracuseStep 31314833 = 23486125) B23486125
theorem B4887485 : Blo 1524459 4887485 := bstep (se 3 (by rfl) ⟨916403, by rfl⟩ : syracuseStep 4887485 = 1832807) B1832807
theorem B6960107 : Blo 1524459 6960107 := bstep (se 1 (by rfl) ⟨5220080, by rfl⟩ : syracuseStep 6960107 = 10440161) B10440161
theorem B11744293 : Blo 1524459 11744293 := bstep (se 4 (by rfl) ⟨1101027, by rfl⟩ : syracuseStep 11744293 = 2202055) B2202055
theorem B3765295 : Blo 1524459 3765295 := bstep (se 1 (by rfl) ⟨2823971, by rfl⟩ : syracuseStep 3765295 = 5647943) B5647943
theorem B3667151 : Blo 1524459 3667151 := bstep (se 1 (by rfl) ⟨2750363, by rfl⟩ : syracuseStep 3667151 = 5500727) B5500727
theorem B6517979 : Blo 1524459 6517979 := bstep (se 1 (by rfl) ⟨4888484, by rfl⟩ : syracuseStep 6517979 = 9776969) B9776969
theorem B21985091 : Blo 1524459 21985091 := bstep (se 1 (by rfl) ⟨16488818, by rfl⟩ : syracuseStep 21985091 = 32977637) B32977637
theorem B19535741 : Blo 1524459 19535741 := bstep (se 3 (by rfl) ⟨3662951, by rfl⟩ : syracuseStep 19535741 = 7325903) B7325903
theorem B3430367 : Blo 1524459 3430367 := bstep (se 1 (by rfl) ⟨2572775, by rfl⟩ : syracuseStep 3430367 = 5145551) B5145551
theorem B8247419 : Blo 1524459 8247419 := bstep (se 1 (by rfl) ⟨6185564, by rfl⟩ : syracuseStep 8247419 = 12371129) B12371129
theorem B3431015 : Blo 1524459 3431015 := bstep (se 1 (by rfl) ⟨2573261, by rfl⟩ : syracuseStep 3431015 = 5146523) B5146523
theorem B3431177 : Blo 1524459 3431177 := bstep (se 2 (by rfl) ⟨1286691, by rfl⟩ : syracuseStep 3431177 = 2573383) B2573383
theorem B5872445 : Blo 1524459 5872445 := bstep (se 3 (by rfl) ⟨1101083, by rfl⟩ : syracuseStep 5872445 = 2202167) B2202167
theorem B3431753 : Blo 1524459 3431753 := bstep (se 2 (by rfl) ⟨1286907, by rfl⟩ : syracuseStep 3431753 = 2573815) B2573815
theorem B7830863 : Blo 1524459 7830863 := bstep (se 1 (by rfl) ⟨5873147, by rfl⟩ : syracuseStep 7830863 = 11746295) B11746295
theorem B22289897 : Blo 1524459 22289897 := bstep (se 2 (by rfl) ⟨8358711, by rfl⟩ : syracuseStep 22289897 = 16717423) B16717423
theorem B3431915 : Blo 1524459 3431915 := bstep (se 1 (by rfl) ⟨2573936, by rfl⟩ : syracuseStep 3431915 = 5147873) B5147873
theorem B12533267 : Blo 1524459 12533267 := bstep (se 1 (by rfl) ⟨9399950, by rfl⟩ : syracuseStep 12533267 = 18799901) B18799901
theorem B3432329 : Blo 1524459 3432329 := bstep (se 2 (by rfl) ⟨1287123, by rfl⟩ : syracuseStep 3432329 = 2574247) B2574247
theorem B8683483 : Blo 1524459 8683483 := bstep (se 1 (by rfl) ⟨6512612, by rfl⟩ : syracuseStep 8683483 = 13025225) B13025225
theorem B19546859 : Blo 1524459 19546859 := bstep (se 1 (by rfl) ⟨14660144, by rfl⟩ : syracuseStep 19546859 = 29320289) B29320289
theorem B5145335 : Blo 1524459 5145335 := bstep (se 1 (by rfl) ⟨3859001, by rfl⟩ : syracuseStep 5145335 = 7718003) B7718003
theorem B2573147 : Blo 1524459 2573147 := bstep (se 1 (by rfl) ⟨1929860, by rfl⟩ : syracuseStep 2573147 = 3859721) B3859721
theorem B26051543 : Blo 1524459 26051543 := bstep (se 1 (by rfl) ⟨19538657, by rfl⟩ : syracuseStep 26051543 = 39077315) B39077315
theorem B14656727 : Blo 1524459 14656727 := bstep (se 1 (by rfl) ⟨10992545, by rfl⟩ : syracuseStep 14656727 = 21985091) B21985091
theorem B2286911 : Blo 1524459 2286911 := bstep (se 1 (by rfl) ⟨1715183, by rfl⟩ : syracuseStep 2286911 = 3430367) B3430367
theorem B1525119 : Blo 1524459 1525119 := bstep (se 1 (by rfl) ⟨1143839, by rfl⟩ : syracuseStep 1525119 = 2287679) B2287679
theorem B5498279 : Blo 1524459 5498279 := bstep (se 1 (by rfl) ⟨4123709, by rfl⟩ : syracuseStep 5498279 = 8247419) B8247419
theorem B1525231 : Blo 1524459 1525231 := bstep (se 1 (by rfl) ⟨1143923, by rfl⟩ : syracuseStep 1525231 = 2287847) B2287847
theorem B4343291 : Blo 1524459 4343291 := bstep (se 1 (by rfl) ⟨3257468, by rfl⟩ : syracuseStep 4343291 = 6514937) B6514937
theorem B1525407 : Blo 1524459 1525407 := bstep (se 1 (by rfl) ⟨1144055, by rfl⟩ : syracuseStep 1525407 = 2288111) B2288111
theorem B2287343 : Blo 1524459 2287343 := bstep (se 1 (by rfl) ⟨1715507, by rfl⟩ : syracuseStep 2287343 = 3431015) B3431015
theorem B2287451 : Blo 1524459 2287451 := bstep (se 1 (by rfl) ⟨1715588, by rfl⟩ : syracuseStep 2287451 = 3431177) B3431177
theorem B1525663 : Blo 1524459 1525663 := bstep (se 1 (by rfl) ⟨1144247, by rfl⟩ : syracuseStep 1525663 = 2288495) B2288495
theorem B1525823 : Blo 1524459 1525823 := bstep (se 1 (by rfl) ⟨1144367, by rfl⟩ : syracuseStep 1525823 = 2288735) B2288735
theorem B2287835 : Blo 1524459 2287835 := bstep (se 1 (by rfl) ⟨1715876, by rfl⟩ : syracuseStep 2287835 = 3431753) B3431753
theorem B5220575 : Blo 1524459 5220575 := bstep (se 1 (by rfl) ⟨3915431, by rfl⟩ : syracuseStep 5220575 = 7830863) B7830863
theorem B2287943 : Blo 1524459 2287943 := bstep (se 1 (by rfl) ⟨1715957, by rfl⟩ : syracuseStep 2287943 = 3431915) B3431915
theorem B1526119 : Blo 1524459 1526119 := bstep (se 1 (by rfl) ⟨1144589, by rfl⟩ : syracuseStep 1526119 = 2289179) B2289179
theorem B2288219 : Blo 1524459 2288219 := bstep (se 1 (by rfl) ⟨1716164, by rfl⟩ : syracuseStep 2288219 = 3432329) B3432329
theorem B11577977 : Blo 1524459 11577977 := bstep (se 2 (by rfl) ⟨4341741, by rfl⟩ : syracuseStep 11577977 = 8683483) B8683483
theorem B2288411 : Blo 1524459 2288411 := bstep (se 1 (by rfl) ⟨1716308, by rfl⟩ : syracuseStep 2288411 = 3432617) B3432617
theorem B89197433 : Blo 1524459 89197433 := bstep (se 2 (by rfl) ⟨33449037, by rfl⟩ : syracuseStep 89197433 = 66898075) B66898075
theorem B79244203 : Blo 1524459 79244203 := bstep (se 1 (by rfl) ⟨59433152, by rfl⟩ : syracuseStep 79244203 = 118866305) B118866305
theorem B6188123 : Blo 1524459 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B7326845 : Blo 1524459 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B2288795 : Blo 1524459 2288795 := bstep (se 1 (by rfl) ⟨1716596, by rfl⟩ : syracuseStep 2288795 = 3433193) B3433193
theorem B2288879 : Blo 1524459 2288879 := bstep (se 1 (by rfl) ⟨1716659, by rfl⟩ : syracuseStep 2288879 = 3433319) B3433319
theorem B6515963 : Blo 1524459 6515963 := bstep (se 1 (by rfl) ⟨4886972, by rfl⟩ : syracuseStep 6515963 = 9773945) B9773945
theorem B20876555 : Blo 1524459 20876555 := bstep (se 1 (by rfl) ⟨15657416, by rfl⟩ : syracuseStep 20876555 = 31314833) B31314833
theorem B2288987 : Blo 1524459 2288987 := bstep (se 1 (by rfl) ⟨1716740, by rfl⟩ : syracuseStep 2288987 = 3433481) B3433481
theorem B4345319 : Blo 1524459 4345319 := bstep (se 1 (by rfl) ⟨3258989, by rfl⟩ : syracuseStep 4345319 = 6517979) B6517979
theorem B29322749 : Blo 1524459 29322749 := bstep (se 3 (by rfl) ⟨5498015, by rfl⟩ : syracuseStep 29322749 = 10996031) B10996031
theorem B2289263 : Blo 1524459 2289263 := bstep (se 1 (by rfl) ⟨1716947, by rfl⟩ : syracuseStep 2289263 = 3433895) B3433895
theorem B2289647 : Blo 1524459 2289647 := bstep (se 1 (by rfl) ⟨1717235, by rfl⟩ : syracuseStep 2289647 = 3434471) B3434471
theorem B15659057 : Blo 1524459 15659057 := bstep (se 2 (by rfl) ⟨5872146, by rfl⟩ : syracuseStep 15659057 = 11744293) B11744293
theorem B813183461 : Blo 1524459 813183461 := bstep (se 4 (by rfl) ⟨76235949, by rfl⟩ : syracuseStep 813183461 = 152471899) B152471899
theorem B18560285 : Blo 1524459 18560285 := bstep (se 3 (by rfl) ⟨3480053, by rfl⟩ : syracuseStep 18560285 = 6960107) B6960107
theorem B5789339 : Blo 1524459 5789339 := bstep (se 1 (by rfl) ⟨4342004, by rfl⟩ : syracuseStep 5789339 = 8684009) B8684009
theorem B9778967 : Blo 1524459 9778967 := bstep (se 1 (by rfl) ⟨7334225, by rfl⟩ : syracuseStep 9778967 = 14668451) B14668451
theorem B9779069 : Blo 1524459 9779069 := bstep (se 3 (by rfl) ⟨1833575, by rfl⟩ : syracuseStep 9779069 = 3667151) B3667151
theorem B3430313 : Blo 1524459 3430313 := bstep (se 2 (by rfl) ⟨1286367, by rfl⟩ : syracuseStep 3430313 = 2572735) B2572735
theorem B3258323 : Blo 1524459 3258323 := bstep (se 1 (by rfl) ⟨2443742, by rfl⟩ : syracuseStep 3258323 = 4887485) B4887485
theorem B5216633 : Blo 1524459 5216633 := bstep (se 2 (by rfl) ⟨1956237, by rfl⟩ : syracuseStep 5216633 = 3912475) B3912475
theorem B7723511 : Blo 1524459 7723511 := bstep (se 1 (by rfl) ⟨5792633, by rfl⟩ : syracuseStep 7723511 = 11585267) B11585267
theorem B13023827 : Blo 1524459 13023827 := bstep (se 1 (by rfl) ⟨9767870, by rfl⟩ : syracuseStep 13023827 = 19535741) B19535741
theorem B5020393 : Blo 1524459 5020393 := bstep (se 2 (by rfl) ⟨1882647, by rfl⟩ : syracuseStep 5020393 = 3765295) B3765295
theorem B5151599 : Blo 1524459 5151599 := bstep (se 1 (by rfl) ⟨3863699, by rfl⟩ : syracuseStep 5151599 = 7727399) B7727399
theorem B5790811 : Blo 1524459 5790811 := bstep (se 1 (by rfl) ⟨4343108, by rfl⟩ : syracuseStep 5790811 = 8686217) B8686217
theorem B13032575 : Blo 1524459 13032575 := bstep (se 1 (by rfl) ⟨9774431, by rfl⟩ : syracuseStep 13032575 = 19548863) B19548863
theorem B3914963 : Blo 1524459 3914963 := bstep (se 1 (by rfl) ⟨2936222, by rfl⟩ : syracuseStep 3914963 = 5872445) B5872445
theorem B93986045 : Blo 1524459 93986045 := bstep (se 3 (by rfl) ⟨17622383, by rfl⟩ : syracuseStep 93986045 = 35244767) B35244767
theorem B14859931 : Blo 1524459 14859931 := bstep (se 1 (by rfl) ⟨11144948, by rfl⟩ : syracuseStep 14859931 = 22289897) B22289897
theorem B8355511 : Blo 1524459 8355511 := bstep (se 1 (by rfl) ⟨6266633, by rfl⟩ : syracuseStep 8355511 = 12533267) B12533267
theorem B74235665 : Blo 1524459 74235665 := bstep (se 2 (by rfl) ⟨27838374, by rfl⟩ : syracuseStep 74235665 = 55676749) B55676749
theorem B542122307 : Blo 1524459 542122307 := bstep (se 1 (by rfl) ⟨406591730, by rfl⟩ : syracuseStep 542122307 = 813183461) B813183461
theorem B17367695 : Blo 1524459 17367695 := bstep (se 1 (by rfl) ⟨13025771, by rfl⟩ : syracuseStep 17367695 = 26051543) B26051543
theorem B1524607 : Blo 1524459 1524607 := bstep (se 1 (by rfl) ⟨1143455, by rfl⟩ : syracuseStep 1524607 = 2286911) B2286911
theorem B6693857 : Blo 1524459 6693857 := bstep (se 2 (by rfl) ⟨2510196, by rfl⟩ : syracuseStep 6693857 = 5020393) B5020393
theorem B3859559 : Blo 1524459 3859559 := bstep (se 1 (by rfl) ⟨2894669, by rfl⟩ : syracuseStep 3859559 = 5789339) B5789339
theorem B1524895 : Blo 1524459 1524895 := bstep (se 1 (by rfl) ⟨1143671, by rfl⟩ : syracuseStep 1524895 = 2287343) B2287343
theorem B1524967 : Blo 1524459 1524967 := bstep (se 1 (by rfl) ⟨1143725, by rfl⟩ : syracuseStep 1524967 = 2287451) B2287451
theorem B2286875 : Blo 1524459 2286875 := bstep (se 1 (by rfl) ⟨1715156, by rfl⟩ : syracuseStep 2286875 = 3430313) B3430313
theorem B2172215 : Blo 1524459 2172215 := bstep (se 1 (by rfl) ⟨1629161, by rfl⟩ : syracuseStep 2172215 = 3258323) B3258323
theorem B1525223 : Blo 1524459 1525223 := bstep (se 1 (by rfl) ⟨1143917, by rfl⟩ : syracuseStep 1525223 = 2287835) B2287835
theorem B1525295 : Blo 1524459 1525295 := bstep (se 1 (by rfl) ⟨1143971, by rfl⟩ : syracuseStep 1525295 = 2287943) B2287943
theorem B1525479 : Blo 1524459 1525479 := bstep (se 1 (by rfl) ⟨1144109, by rfl⟩ : syracuseStep 1525479 = 2288219) B2288219
theorem B7718651 : Blo 1524459 7718651 := bstep (se 1 (by rfl) ⟨5788988, by rfl⟩ : syracuseStep 7718651 = 11577977) B11577977
theorem B1525607 : Blo 1524459 1525607 := bstep (se 1 (by rfl) ⟨1144205, by rfl⟩ : syracuseStep 1525607 = 2288411) B2288411
theorem B3434399 : Blo 1524459 3434399 := bstep (se 1 (by rfl) ⟨2575799, by rfl⟩ : syracuseStep 3434399 = 5151599) B5151599
theorem B4884563 : Blo 1524459 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B1525863 : Blo 1524459 1525863 := bstep (se 1 (by rfl) ⟨1144397, by rfl⟩ : syracuseStep 1525863 = 2288795) B2288795
theorem B1525919 : Blo 1524459 1525919 := bstep (se 1 (by rfl) ⟨1144439, by rfl⟩ : syracuseStep 1525919 = 2288879) B2288879
theorem B4343975 : Blo 1524459 4343975 := bstep (se 1 (by rfl) ⟨3257981, by rfl⟩ : syracuseStep 4343975 = 6515963) B6515963
theorem B1525991 : Blo 1524459 1525991 := bstep (se 1 (by rfl) ⟨1144493, by rfl⟩ : syracuseStep 1525991 = 2288987) B2288987
theorem B19548499 : Blo 1524459 19548499 := bstep (se 1 (by rfl) ⟨14661374, by rfl⟩ : syracuseStep 19548499 = 29322749) B29322749
theorem B1526175 : Blo 1524459 1526175 := bstep (se 1 (by rfl) ⟨1144631, by rfl⟩ : syracuseStep 1526175 = 2289263) B2289263
theorem B49490443 : Blo 1524459 49490443 := bstep (se 1 (by rfl) ⟨37117832, by rfl⟩ : syracuseStep 49490443 = 74235665) B74235665
theorem B1526431 : Blo 1524459 1526431 := bstep (se 1 (by rfl) ⟨1144823, by rfl⟩ : syracuseStep 1526431 = 2289647) B2289647
theorem B10439371 : Blo 1524459 10439371 := bstep (se 1 (by rfl) ⟨7829528, by rfl⟩ : syracuseStep 10439371 = 15659057) B15659057
theorem B1715431 : Blo 1524459 1715431 := bstep (se 1 (by rfl) ⟨1286573, by rfl⟩ : syracuseStep 1715431 = 2573147) B2573147
theorem B12373523 : Blo 1524459 12373523 := bstep (se 1 (by rfl) ⟨9280142, by rfl⟩ : syracuseStep 12373523 = 18560285) B18560285
theorem B3665519 : Blo 1524459 3665519 := bstep (se 1 (by rfl) ⟨2749139, by rfl⟩ : syracuseStep 3665519 = 5498279) B5498279
theorem B2895527 : Blo 1524459 2895527 := bstep (se 1 (by rfl) ⟨2171645, by rfl⟩ : syracuseStep 2895527 = 4343291) B4343291
theorem B7721081 : Blo 1524459 7721081 := bstep (se 2 (by rfl) ⟨2895405, by rfl⟩ : syracuseStep 7721081 = 5790811) B5790811
theorem B3477755 : Blo 1524459 3477755 := bstep (se 1 (by rfl) ⟨2608316, by rfl⟩ : syracuseStep 3477755 = 5216633) B5216633
theorem B5149007 : Blo 1524459 5149007 := bstep (se 1 (by rfl) ⟨3861755, by rfl⟩ : syracuseStep 5149007 = 7723511) B7723511
theorem B4125415 : Blo 1524459 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B8688383 : Blo 1524459 8688383 := bstep (se 1 (by rfl) ⟨6516287, by rfl⟩ : syracuseStep 8688383 = 13032575) B13032575
theorem B2609975 : Blo 1524459 2609975 := bstep (se 1 (by rfl) ⟨1957481, by rfl⟩ : syracuseStep 2609975 = 3914963) B3914963
theorem B62657363 : Blo 1524459 62657363 := bstep (se 1 (by rfl) ⟨46993022, by rfl⟩ : syracuseStep 62657363 = 93986045) B93986045
theorem B19813241 : Blo 1524459 19813241 := bstep (se 2 (by rfl) ⟨7429965, by rfl⟩ : syracuseStep 19813241 = 14859931) B14859931
theorem B2896879 : Blo 1524459 2896879 := bstep (se 1 (by rfl) ⟨2172659, by rfl⟩ : syracuseStep 2896879 = 4345319) B4345319
theorem B13031239 : Blo 1524459 13031239 := bstep (se 1 (by rfl) ⟨9773429, by rfl⟩ : syracuseStep 13031239 = 19546859) B19546859
theorem B3430223 : Blo 1524459 3430223 := bstep (se 1 (by rfl) ⟨2572667, by rfl⟩ : syracuseStep 3430223 = 5145335) B5145335
theorem B9771151 : Blo 1524459 9771151 := bstep (se 1 (by rfl) ⟨7328363, by rfl⟩ : syracuseStep 9771151 = 14656727) B14656727
theorem B6519311 : Blo 1524459 6519311 := bstep (se 1 (by rfl) ⟨4889483, by rfl⟩ : syracuseStep 6519311 = 9778967) B9778967
theorem B105658937 : Blo 1524459 105658937 := bstep (se 2 (by rfl) ⟨39622101, by rfl⟩ : syracuseStep 105658937 = 79244203) B79244203
theorem B6519379 : Blo 1524459 6519379 := bstep (se 1 (by rfl) ⟨4889534, by rfl⟩ : syracuseStep 6519379 = 9779069) B9779069
theorem B3480383 : Blo 1524459 3480383 := bstep (se 1 (by rfl) ⟨2610287, by rfl⟩ : syracuseStep 3480383 = 5220575) B5220575
theorem B8682551 : Blo 1524459 8682551 := bstep (se 1 (by rfl) ⟨6511913, by rfl⟩ : syracuseStep 8682551 = 13023827) B13023827
theorem B59464955 : Blo 1524459 59464955 := bstep (se 1 (by rfl) ⟨44598716, by rfl⟩ : syracuseStep 59464955 = 89197433) B89197433
theorem B13917703 : Blo 1524459 13917703 := bstep (se 1 (by rfl) ⟨10438277, by rfl⟩ : syracuseStep 13917703 = 20876555) B20876555
theorem B11140681 : Blo 1524459 11140681 := bstep (se 2 (by rfl) ⟨4177755, by rfl⟩ : syracuseStep 11140681 = 8355511) B8355511
theorem B361414871 : Blo 1524459 361414871 := bstep (se 1 (by rfl) ⟨271061153, by rfl⟩ : syracuseStep 361414871 = 542122307) B542122307
theorem B3432671 : Blo 1524459 3432671 := bstep (se 1 (by rfl) ⟨2574503, by rfl⟩ : syracuseStep 3432671 = 5149007) B5149007
theorem B5792255 : Blo 1524459 5792255 := bstep (se 1 (by rfl) ⟨4344191, by rfl⟩ : syracuseStep 5792255 = 8688383) B8688383
theorem B41771575 : Blo 1524459 41771575 := bstep (se 1 (by rfl) ⟨31328681, by rfl⟩ : syracuseStep 41771575 = 62657363) B62657363
theorem B9274013 : Blo 1524459 9274013 := bstep (se 3 (by rfl) ⟨1738877, by rfl⟩ : syracuseStep 9274013 = 3477755) B3477755
theorem B65987257 : Blo 1524459 65987257 := bstep (se 2 (by rfl) ⟨24745221, by rfl⟩ : syracuseStep 65987257 = 49490443) B49490443
theorem B2573039 : Blo 1524459 2573039 := bstep (se 1 (by rfl) ⟨1929779, by rfl⟩ : syracuseStep 2573039 = 3859559) B3859559
theorem B8692505 : Blo 1524459 8692505 := bstep (se 2 (by rfl) ⟨3259689, by rfl⟩ : syracuseStep 8692505 = 6519379) B6519379
theorem B5792573 : Blo 1524459 5792573 := bstep (se 3 (by rfl) ⟨1086107, by rfl⟩ : syracuseStep 5792573 = 2172215) B2172215
theorem B1524583 : Blo 1524459 1524583 := bstep (se 1 (by rfl) ⟨1143437, by rfl⟩ : syracuseStep 1524583 = 2286875) B2286875
theorem B5145767 : Blo 1524459 5145767 := bstep (se 1 (by rfl) ⟨3859325, by rfl⟩ : syracuseStep 5145767 = 7718651) B7718651
theorem B2286815 : Blo 1524459 2286815 := bstep (se 1 (by rfl) ⟨1715111, by rfl⟩ : syracuseStep 2286815 = 3430223) B3430223
theorem B2287241 : Blo 1524459 2287241 := bstep (se 2 (by rfl) ⟨857715, by rfl⟩ : syracuseStep 2287241 = 1715431) B1715431
theorem B2320255 : Blo 1524459 2320255 := bstep (se 1 (by rfl) ⟨1740191, by rfl⟩ : syracuseStep 2320255 = 3480383) B3480383
theorem B18556937 : Blo 1524459 18556937 := bstep (se 2 (by rfl) ⟨6958851, by rfl⟩ : syracuseStep 18556937 = 13917703) B13917703
theorem B14854241 : Blo 1524459 14854241 := bstep (se 2 (by rfl) ⟨5570340, by rfl⟩ : syracuseStep 14854241 = 11140681) B11140681
theorem B39643303 : Blo 1524459 39643303 := bstep (se 1 (by rfl) ⟨29732477, by rfl⟩ : syracuseStep 39643303 = 59464955) B59464955
theorem B2443679 : Blo 1524459 2443679 := bstep (se 1 (by rfl) ⟨1832759, by rfl⟩ : syracuseStep 2443679 = 3665519) B3665519
theorem B5147387 : Blo 1524459 5147387 := bstep (se 1 (by rfl) ⟨3860540, by rfl⟩ : syracuseStep 5147387 = 7721081) B7721081
theorem B13028201 : Blo 1524459 13028201 := bstep (se 2 (by rfl) ⟨4885575, by rfl⟩ : syracuseStep 13028201 = 9771151) B9771151
theorem B11578463 : Blo 1524459 11578463 := bstep (se 1 (by rfl) ⟨8683847, by rfl⟩ : syracuseStep 11578463 = 17367695) B17367695
theorem B1739983 : Blo 1524459 1739983 := bstep (se 1 (by rfl) ⟨1304987, by rfl⟩ : syracuseStep 1739983 = 2609975) B2609975
theorem B13208827 : Blo 1524459 13208827 := bstep (se 1 (by rfl) ⟨9906620, by rfl⟩ : syracuseStep 13208827 = 19813241) B19813241
theorem B5500553 : Blo 1524459 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B55676645 : Blo 1524459 55676645 := bstep (se 4 (by rfl) ⟨5219685, by rfl⟩ : syracuseStep 55676645 = 10439371) B10439371
theorem B2289599 : Blo 1524459 2289599 := bstep (se 1 (by rfl) ⟨1717199, by rfl⟩ : syracuseStep 2289599 = 3434399) B3434399
theorem B3862505 : Blo 1524459 3862505 := bstep (se 2 (by rfl) ⟨1448439, by rfl⟩ : syracuseStep 3862505 = 2896879) B2896879
theorem B3256375 : Blo 1524459 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B2895983 : Blo 1524459 2895983 := bstep (se 1 (by rfl) ⟨2171987, by rfl⟩ : syracuseStep 2895983 = 4343975) B4343975
theorem B4346207 : Blo 1524459 4346207 := bstep (se 1 (by rfl) ⟨3259655, by rfl⟩ : syracuseStep 4346207 = 6519311) B6519311
theorem B70439291 : Blo 1524459 70439291 := bstep (se 1 (by rfl) ⟨52829468, by rfl⟩ : syracuseStep 70439291 = 105658937) B105658937
theorem B7721405 : Blo 1524459 7721405 := bstep (se 3 (by rfl) ⟨1447763, by rfl⟩ : syracuseStep 7721405 = 2895527) B2895527
theorem B5788367 : Blo 1524459 5788367 := bstep (se 1 (by rfl) ⟨4341275, by rfl⟩ : syracuseStep 5788367 = 8682551) B8682551
theorem B26064665 : Blo 1524459 26064665 := bstep (se 2 (by rfl) ⟨9774249, by rfl⟩ : syracuseStep 26064665 = 19548499) B19548499
theorem B4462571 : Blo 1524459 4462571 := bstep (se 1 (by rfl) ⟨3346928, by rfl⟩ : syracuseStep 4462571 = 6693857) B6693857
theorem B8249015 : Blo 1524459 8249015 := bstep (se 1 (by rfl) ⟨6186761, by rfl⟩ : syracuseStep 8249015 = 12373523) B12373523
theorem B17374985 : Blo 1524459 17374985 := bstep (se 2 (by rfl) ⟨6515619, by rfl⟩ : syracuseStep 17374985 = 13031239) B13031239
theorem B4341833 : Blo 1524459 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B240943247 : Blo 1524459 240943247 := bstep (se 1 (by rfl) ⟨180707435, by rfl⟩ : syracuseStep 240943247 = 361414871) B361414871
theorem B3858911 : Blo 1524459 3858911 := bstep (se 1 (by rfl) ⟨2894183, by rfl⟩ : syracuseStep 3858911 = 5788367) B5788367
theorem B1524543 : Blo 1524459 1524543 := bstep (se 1 (by rfl) ⟨1143407, by rfl⟩ : syracuseStep 1524543 = 2286815) B2286815
theorem B87983009 : Blo 1524459 87983009 := bstep (se 2 (by rfl) ⟨32993628, by rfl⟩ : syracuseStep 87983009 = 65987257) B65987257
theorem B1524827 : Blo 1524459 1524827 := bstep (se 1 (by rfl) ⟨1143620, by rfl⟩ : syracuseStep 1524827 = 2287241) B2287241
theorem B17376443 : Blo 1524459 17376443 := bstep (se 1 (by rfl) ⟨13032332, by rfl⟩ : syracuseStep 17376443 = 26064665) B26064665
theorem B12371291 : Blo 1524459 12371291 := bstep (se 1 (by rfl) ⟨9278468, by rfl⟩ : syracuseStep 12371291 = 18556937) B18556937
theorem B2319977 : Blo 1524459 2319977 := bstep (se 2 (by rfl) ⟨869991, by rfl⟩ : syracuseStep 2319977 = 1739983) B1739983
theorem B8685467 : Blo 1524459 8685467 := bstep (se 1 (by rfl) ⟨6514100, by rfl⟩ : syracuseStep 8685467 = 13028201) B13028201
theorem B7718975 : Blo 1524459 7718975 := bstep (se 1 (by rfl) ⟨5789231, by rfl⟩ : syracuseStep 7718975 = 11578463) B11578463
theorem B5499343 : Blo 1524459 5499343 := bstep (se 1 (by rfl) ⟨4124507, by rfl⟩ : syracuseStep 5499343 = 8249015) B8249015
theorem B1526399 : Blo 1524459 1526399 := bstep (se 1 (by rfl) ⟨1144799, by rfl⟩ : syracuseStep 1526399 = 2289599) B2289599
theorem B2575003 : Blo 1524459 2575003 := bstep (se 1 (by rfl) ⟨1931252, by rfl⟩ : syracuseStep 2575003 = 3862505) B3862505
theorem B2288447 : Blo 1524459 2288447 := bstep (se 1 (by rfl) ⟨1716335, by rfl⟩ : syracuseStep 2288447 = 3432671) B3432671
theorem B52857737 : Blo 1524459 52857737 := bstep (se 2 (by rfl) ⟨19821651, by rfl⟩ : syracuseStep 52857737 = 39643303) B39643303
theorem B46959527 : Blo 1524459 46959527 := bstep (se 1 (by rfl) ⟨35219645, by rfl⟩ : syracuseStep 46959527 = 70439291) B70439291
theorem B5147603 : Blo 1524459 5147603 := bstep (se 1 (by rfl) ⟨3860702, by rfl⟩ : syracuseStep 5147603 = 7721405) B7721405
theorem B3861503 : Blo 1524459 3861503 := bstep (se 1 (by rfl) ⟨2896127, by rfl⟩ : syracuseStep 3861503 = 5792255) B5792255
theorem B1715359 : Blo 1524459 1715359 := bstep (se 1 (by rfl) ⟨1286519, by rfl⟩ : syracuseStep 1715359 = 2573039) B2573039
theorem B5795003 : Blo 1524459 5795003 := bstep (se 1 (by rfl) ⟨4346252, by rfl⟩ : syracuseStep 5795003 = 8692505) B8692505
theorem B3861715 : Blo 1524459 3861715 := bstep (se 1 (by rfl) ⟨2896286, by rfl⟩ : syracuseStep 3861715 = 5792573) B5792573
theorem B14668141 : Blo 1524459 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B3093673 : Blo 1524459 3093673 := bstep (se 2 (by rfl) ⟨1160127, by rfl⟩ : syracuseStep 3093673 = 2320255) B2320255
theorem B11900189 : Blo 1524459 11900189 := bstep (se 3 (by rfl) ⟨2231285, by rfl⟩ : syracuseStep 11900189 = 4462571) B4462571
theorem B1930655 : Blo 1524459 1930655 := bstep (se 1 (by rfl) ⟨1447991, by rfl⟩ : syracuseStep 1930655 = 2895983) B2895983
theorem B2897471 : Blo 1524459 2897471 := bstep (se 1 (by rfl) ⟨2173103, by rfl⟩ : syracuseStep 2897471 = 4346207) B4346207
theorem B6182675 : Blo 1524459 6182675 := bstep (se 1 (by rfl) ⟨4637006, by rfl⟩ : syracuseStep 6182675 = 9274013) B9274013
theorem B55695433 : Blo 1524459 55695433 := bstep (se 2 (by rfl) ⟨20885787, by rfl⟩ : syracuseStep 55695433 = 41771575) B41771575
theorem B3430511 : Blo 1524459 3430511 := bstep (se 1 (by rfl) ⟨2572883, by rfl⟩ : syracuseStep 3430511 = 5145767) B5145767
theorem B9902827 : Blo 1524459 9902827 := bstep (se 1 (by rfl) ⟨7427120, by rfl⟩ : syracuseStep 9902827 = 14854241) B14854241
theorem B1629119 : Blo 1524459 1629119 := bstep (se 1 (by rfl) ⟨1221839, by rfl⟩ : syracuseStep 1629119 = 2443679) B2443679
theorem B17611769 : Blo 1524459 17611769 := bstep (se 2 (by rfl) ⟨6604413, by rfl⟩ : syracuseStep 17611769 = 13208827) B13208827
theorem B3431591 : Blo 1524459 3431591 := bstep (se 1 (by rfl) ⟨2573693, by rfl⟩ : syracuseStep 3431591 = 5147387) B5147387
theorem B37117763 : Blo 1524459 37117763 := bstep (se 1 (by rfl) ⟨27838322, by rfl⟩ : syracuseStep 37117763 = 55676645) B55676645
theorem B11583323 : Blo 1524459 11583323 := bstep (se 1 (by rfl) ⟨8687492, by rfl⟩ : syracuseStep 11583323 = 17374985) B17374985
theorem B160628831 : Blo 1524459 160628831 := bstep (se 1 (by rfl) ⟨120471623, by rfl⟩ : syracuseStep 160628831 = 240943247) B240943247
theorem B74260577 : Blo 1524459 74260577 := bstep (se 2 (by rfl) ⟨27847716, by rfl⟩ : syracuseStep 74260577 = 55695433) B55695433
theorem B2572607 : Blo 1524459 2572607 := bstep (se 1 (by rfl) ⟨1929455, by rfl⟩ : syracuseStep 2572607 = 3858911) B3858911
theorem B7332457 : Blo 1524459 7332457 := bstep (se 2 (by rfl) ⟨2749671, by rfl⟩ : syracuseStep 7332457 = 5499343) B5499343
theorem B58655339 : Blo 1524459 58655339 := bstep (se 1 (by rfl) ⟨43991504, by rfl⟩ : syracuseStep 58655339 = 87983009) B87983009
theorem B11584295 : Blo 1524459 11584295 := bstep (se 1 (by rfl) ⟨8688221, by rfl⟩ : syracuseStep 11584295 = 17376443) B17376443
theorem B3433337 : Blo 1524459 3433337 := bstep (se 2 (by rfl) ⟨1287501, by rfl⟩ : syracuseStep 3433337 = 2575003) B2575003
theorem B4121783 : Blo 1524459 4121783 := bstep (se 1 (by rfl) ⟨3091337, by rfl⟩ : syracuseStep 4121783 = 6182675) B6182675
theorem B5145983 : Blo 1524459 5145983 := bstep (se 1 (by rfl) ⟨3859487, by rfl⟩ : syracuseStep 5145983 = 7718975) B7718975
theorem B2287007 : Blo 1524459 2287007 := bstep (se 1 (by rfl) ⟨1715255, by rfl⟩ : syracuseStep 2287007 = 3430511) B3430511
theorem B2287145 : Blo 1524459 2287145 := bstep (se 2 (by rfl) ⟨857679, by rfl⟩ : syracuseStep 2287145 = 1715359) B1715359
theorem B1525631 : Blo 1524459 1525631 := bstep (se 1 (by rfl) ⟨1144223, by rfl⟩ : syracuseStep 1525631 = 2288447) B2288447
theorem B2574335 : Blo 1524459 2574335 := bstep (se 1 (by rfl) ⟨1930751, by rfl⟩ : syracuseStep 2574335 = 3861503) B3861503
theorem B2287727 : Blo 1524459 2287727 := bstep (se 1 (by rfl) ⟨1715795, by rfl⟩ : syracuseStep 2287727 = 3431591) B3431591
theorem B4344317 : Blo 1524459 4344317 := bstep (se 3 (by rfl) ⟨814559, by rfl⟩ : syracuseStep 4344317 = 1629119) B1629119
theorem B2894555 : Blo 1524459 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B19557521 : Blo 1524459 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B7726589 : Blo 1524459 7726589 := bstep (se 3 (by rfl) ⟨1448735, by rfl⟩ : syracuseStep 7726589 = 2897471) B2897471
theorem B7933459 : Blo 1524459 7933459 := bstep (se 1 (by rfl) ⟨5950094, by rfl⟩ : syracuseStep 7933459 = 11900189) B11900189
theorem B5148413 : Blo 1524459 5148413 := bstep (se 3 (by rfl) ⟨965327, by rfl⟩ : syracuseStep 5148413 = 1930655) B1930655
theorem B4124897 : Blo 1524459 4124897 := bstep (se 2 (by rfl) ⟨1546836, by rfl⟩ : syracuseStep 4124897 = 3093673) B3093673
theorem B5148953 : Blo 1524459 5148953 := bstep (se 2 (by rfl) ⟨1930857, by rfl⟩ : syracuseStep 5148953 = 3861715) B3861715
theorem B35238491 : Blo 1524459 35238491 := bstep (se 1 (by rfl) ⟨26428868, by rfl⟩ : syracuseStep 35238491 = 52857737) B52857737
theorem B31306351 : Blo 1524459 31306351 := bstep (se 1 (by rfl) ⟨23479763, by rfl⟩ : syracuseStep 31306351 = 46959527) B46959527
theorem B3863335 : Blo 1524459 3863335 := bstep (se 1 (by rfl) ⟨2897501, by rfl⟩ : syracuseStep 3863335 = 5795003) B5795003
theorem B24745175 : Blo 1524459 24745175 := bstep (se 1 (by rfl) ⟨18558881, by rfl⟩ : syracuseStep 24745175 = 37117763) B37117763
theorem B7722215 : Blo 1524459 7722215 := bstep (se 1 (by rfl) ⟨5791661, by rfl⟩ : syracuseStep 7722215 = 11583323) B11583323
theorem B8247527 : Blo 1524459 8247527 := bstep (se 1 (by rfl) ⟨6185645, by rfl⟩ : syracuseStep 8247527 = 12371291) B12371291
theorem B13203769 : Blo 1524459 13203769 := bstep (se 2 (by rfl) ⟨4951413, by rfl⟩ : syracuseStep 13203769 = 9902827) B9902827
theorem B1546651 : Blo 1524459 1546651 := bstep (se 1 (by rfl) ⟨1159988, by rfl⟩ : syracuseStep 1546651 = 2319977) B2319977
theorem B5790311 : Blo 1524459 5790311 := bstep (se 1 (by rfl) ⟨4342733, by rfl⟩ : syracuseStep 5790311 = 8685467) B8685467
theorem B3431735 : Blo 1524459 3431735 := bstep (se 1 (by rfl) ⟨2573801, by rfl⟩ : syracuseStep 3431735 = 5147603) B5147603
theorem B46964717 : Blo 1524459 46964717 := bstep (se 3 (by rfl) ⟨8805884, by rfl⟩ : syracuseStep 46964717 = 17611769) B17611769
theorem B107085887 : Blo 1524459 107085887 := bstep (se 1 (by rfl) ⟨80314415, by rfl⟩ : syracuseStep 107085887 = 160628831) B160628831
theorem B3432635 : Blo 1524459 3432635 := bstep (se 1 (by rfl) ⟨2574476, by rfl⟩ : syracuseStep 3432635 = 5148953) B5148953
theorem B17605025 : Blo 1524459 17605025 := bstep (se 2 (by rfl) ⟨6601884, by rfl⟩ : syracuseStep 17605025 = 13203769) B13203769
theorem B1524671 : Blo 1524459 1524671 := bstep (se 1 (by rfl) ⟨1143503, by rfl⟩ : syracuseStep 1524671 = 2287007) B2287007
theorem B1524763 : Blo 1524459 1524763 := bstep (se 1 (by rfl) ⟨1143572, by rfl⟩ : syracuseStep 1524763 = 2287145) B2287145
theorem B1525151 : Blo 1524459 1525151 := bstep (se 1 (by rfl) ⟨1143863, by rfl⟩ : syracuseStep 1525151 = 2287727) B2287727
theorem B5498351 : Blo 1524459 5498351 := bstep (se 1 (by rfl) ⟨4123763, by rfl⟩ : syracuseStep 5498351 = 8247527) B8247527
theorem B3860207 : Blo 1524459 3860207 := bstep (se 1 (by rfl) ⟨2895155, by rfl⟩ : syracuseStep 3860207 = 5790311) B5790311
theorem B7718813 : Blo 1524459 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B10577945 : Blo 1524459 10577945 := bstep (se 2 (by rfl) ⟨3966729, by rfl⟩ : syracuseStep 10577945 = 7933459) B7933459
theorem B2287823 : Blo 1524459 2287823 := bstep (se 1 (by rfl) ⟨1715867, by rfl⟩ : syracuseStep 2287823 = 3431735) B3431735
theorem B49507051 : Blo 1524459 49507051 := bstep (se 1 (by rfl) ⟨37130288, by rfl⟩ : syracuseStep 49507051 = 74260577) B74260577
theorem B1715071 : Blo 1524459 1715071 := bstep (se 1 (by rfl) ⟨1286303, by rfl⟩ : syracuseStep 1715071 = 2572607) B2572607
theorem B39103559 : Blo 1524459 39103559 := bstep (se 1 (by rfl) ⟨29327669, by rfl⟩ : syracuseStep 39103559 = 58655339) B58655339
theorem B2288891 : Blo 1524459 2288891 := bstep (se 1 (by rfl) ⟨1716668, by rfl⟩ : syracuseStep 2288891 = 3433337) B3433337
theorem B2747855 : Blo 1524459 2747855 := bstep (se 1 (by rfl) ⟨2060891, by rfl⟩ : syracuseStep 2747855 = 4121783) B4121783
theorem B9776609 : Blo 1524459 9776609 := bstep (se 2 (by rfl) ⟨3666228, by rfl⟩ : syracuseStep 9776609 = 7332457) B7332457
theorem B41741801 : Blo 1524459 41741801 := bstep (se 2 (by rfl) ⟨15653175, by rfl⟩ : syracuseStep 41741801 = 31306351) B31306351
theorem B5148143 : Blo 1524459 5148143 := bstep (se 1 (by rfl) ⟨3861107, by rfl⟩ : syracuseStep 5148143 = 7722215) B7722215
theorem B1716223 : Blo 1524459 1716223 := bstep (se 1 (by rfl) ⟨1287167, by rfl⟩ : syracuseStep 1716223 = 2574335) B2574335
theorem B2896211 : Blo 1524459 2896211 := bstep (se 1 (by rfl) ⟨2172158, by rfl⟩ : syracuseStep 2896211 = 4344317) B4344317
theorem B13038347 : Blo 1524459 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B2749931 : Blo 1524459 2749931 := bstep (se 1 (by rfl) ⟨2062448, by rfl⟩ : syracuseStep 2749931 = 4124897) B4124897
theorem B23492327 : Blo 1524459 23492327 := bstep (se 1 (by rfl) ⟨17619245, by rfl⟩ : syracuseStep 23492327 = 35238491) B35238491
theorem B7722863 : Blo 1524459 7722863 := bstep (se 1 (by rfl) ⟨5792147, by rfl⟩ : syracuseStep 7722863 = 11584295) B11584295
theorem B2062201 : Blo 1524459 2062201 := bstep (se 2 (by rfl) ⟨773325, by rfl⟩ : syracuseStep 2062201 = 1546651) B1546651
theorem B16496783 : Blo 1524459 16496783 := bstep (se 1 (by rfl) ⟨12372587, by rfl⟩ : syracuseStep 16496783 = 24745175) B24745175
theorem B3430655 : Blo 1524459 3430655 := bstep (se 1 (by rfl) ⟨2572991, by rfl⟩ : syracuseStep 3430655 = 5145983) B5145983
theorem B5151059 : Blo 1524459 5151059 := bstep (se 1 (by rfl) ⟨3863294, by rfl⟩ : syracuseStep 5151059 = 7726589) B7726589
theorem B5151113 : Blo 1524459 5151113 := bstep (se 2 (by rfl) ⟨1931667, by rfl⟩ : syracuseStep 5151113 = 3863335) B3863335
theorem B3432275 : Blo 1524459 3432275 := bstep (se 1 (by rfl) ⟨2574206, by rfl⟩ : syracuseStep 3432275 = 5148413) B5148413
theorem B31309811 : Blo 1524459 31309811 := bstep (se 1 (by rfl) ⟨23482358, by rfl⟩ : syracuseStep 31309811 = 46964717) B46964717
theorem B8692231 : Blo 1524459 8692231 := bstep (se 1 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 8692231 = 13038347) B13038347
theorem B2573471 : Blo 1524459 2573471 := bstep (se 1 (by rfl) ⟨1930103, by rfl⟩ : syracuseStep 2573471 = 3860207) B3860207
theorem B2286761 : Blo 1524459 2286761 := bstep (se 2 (by rfl) ⟨857535, by rfl⟩ : syracuseStep 2286761 = 1715071) B1715071
theorem B5145875 : Blo 1524459 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B1525215 : Blo 1524459 1525215 := bstep (se 1 (by rfl) ⟨1143911, by rfl⟩ : syracuseStep 1525215 = 2287823) B2287823
theorem B2287103 : Blo 1524459 2287103 := bstep (se 1 (by rfl) ⟨1715327, by rfl⟩ : syracuseStep 2287103 = 3430655) B3430655
theorem B3434039 : Blo 1524459 3434039 := bstep (se 1 (by rfl) ⟨2575529, by rfl⟩ : syracuseStep 3434039 = 5151059) B5151059
theorem B3434075 : Blo 1524459 3434075 := bstep (se 1 (by rfl) ⟨2575556, by rfl⟩ : syracuseStep 3434075 = 5151113) B5151113
theorem B62646205 : Blo 1524459 62646205 := bstep (se 3 (by rfl) ⟨11746163, by rfl⟩ : syracuseStep 62646205 = 23492327) B23492327
theorem B26069039 : Blo 1524459 26069039 := bstep (se 1 (by rfl) ⟨19551779, by rfl⟩ : syracuseStep 26069039 = 39103559) B39103559
theorem B1525927 : Blo 1524459 1525927 := bstep (se 1 (by rfl) ⟨1144445, by rfl⟩ : syracuseStep 1525927 = 2288891) B2288891
theorem B2288183 : Blo 1524459 2288183 := bstep (se 1 (by rfl) ⟨1716137, by rfl⟩ : syracuseStep 2288183 = 3432275) B3432275
theorem B2288297 : Blo 1524459 2288297 := bstep (se 2 (by rfl) ⟨858111, by rfl⟩ : syracuseStep 2288297 = 1716223) B1716223
theorem B2288423 : Blo 1524459 2288423 := bstep (se 1 (by rfl) ⟨1716317, by rfl⟩ : syracuseStep 2288423 = 3432635) B3432635
theorem B3665567 : Blo 1524459 3665567 := bstep (se 1 (by rfl) ⟨2749175, by rfl⟩ : syracuseStep 3665567 = 5498351) B5498351
theorem B5148575 : Blo 1524459 5148575 := bstep (se 1 (by rfl) ⟨3861431, by rfl⟩ : syracuseStep 5148575 = 7722863) B7722863
theorem B10997855 : Blo 1524459 10997855 := bstep (se 1 (by rfl) ⟨8248391, by rfl⟩ : syracuseStep 10997855 = 16496783) B16496783
theorem B1831903 : Blo 1524459 1831903 := bstep (se 1 (by rfl) ⟨1373927, by rfl⟩ : syracuseStep 1831903 = 2747855) B2747855
theorem B6517739 : Blo 1524459 6517739 := bstep (se 1 (by rfl) ⟨4888304, by rfl⟩ : syracuseStep 6517739 = 9776609) B9776609
theorem B2749601 : Blo 1524459 2749601 := bstep (se 2 (by rfl) ⟨1031100, by rfl⟩ : syracuseStep 2749601 = 2062201) B2062201
theorem B71390591 : Blo 1524459 71390591 := bstep (se 1 (by rfl) ⟨53542943, by rfl⟩ : syracuseStep 71390591 = 107085887) B107085887
theorem B1930807 : Blo 1524459 1930807 := bstep (se 1 (by rfl) ⟨1448105, by rfl⟩ : syracuseStep 1930807 = 2896211) B2896211
theorem B11736683 : Blo 1524459 11736683 := bstep (se 1 (by rfl) ⟨8802512, by rfl⟩ : syracuseStep 11736683 = 17605025) B17605025
theorem B66009401 : Blo 1524459 66009401 := bstep (se 2 (by rfl) ⟨24753525, by rfl⟩ : syracuseStep 66009401 = 49507051) B49507051
theorem B1833287 : Blo 1524459 1833287 := bstep (se 1 (by rfl) ⟨1374965, by rfl⟩ : syracuseStep 1833287 = 2749931) B2749931
theorem B7051963 : Blo 1524459 7051963 := bstep (se 1 (by rfl) ⟨5288972, by rfl⟩ : syracuseStep 7051963 = 10577945) B10577945
theorem B27827867 : Blo 1524459 27827867 := bstep (se 1 (by rfl) ⟨20870900, by rfl⟩ : syracuseStep 27827867 = 41741801) B41741801
theorem B3432095 : Blo 1524459 3432095 := bstep (se 1 (by rfl) ⟨2574071, by rfl⟩ : syracuseStep 3432095 = 5148143) B5148143
theorem B20873207 : Blo 1524459 20873207 := bstep (se 1 (by rfl) ⟨15654905, by rfl⟩ : syracuseStep 20873207 = 31309811) B31309811
theorem B7331903 : Blo 1524459 7331903 := bstep (se 1 (by rfl) ⟨5498927, by rfl⟩ : syracuseStep 7331903 = 10997855) B10997855
theorem B1524507 : Blo 1524459 1524507 := bstep (se 1 (by rfl) ⟨1143380, by rfl⟩ : syracuseStep 1524507 = 2286761) B2286761
theorem B1524735 : Blo 1524459 1524735 := bstep (se 1 (by rfl) ⟨1143551, by rfl⟩ : syracuseStep 1524735 = 2287103) B2287103
theorem B7824455 : Blo 1524459 7824455 := bstep (se 1 (by rfl) ⟨5868341, by rfl⟩ : syracuseStep 7824455 = 11736683) B11736683
theorem B1525455 : Blo 1524459 1525455 := bstep (se 1 (by rfl) ⟨1144091, by rfl⟩ : syracuseStep 1525455 = 2288183) B2288183
theorem B1525531 : Blo 1524459 1525531 := bstep (se 1 (by rfl) ⟨1144148, by rfl⟩ : syracuseStep 1525531 = 2288297) B2288297
theorem B1525615 : Blo 1524459 1525615 := bstep (se 1 (by rfl) ⟨1144211, by rfl⟩ : syracuseStep 1525615 = 2288423) B2288423
theorem B2574409 : Blo 1524459 2574409 := bstep (se 2 (by rfl) ⟨965403, by rfl⟩ : syracuseStep 2574409 = 1930807) B1930807
theorem B2288063 : Blo 1524459 2288063 := bstep (se 1 (by rfl) ⟨1716047, by rfl⟩ : syracuseStep 2288063 = 3432095) B3432095
theorem B2443711 : Blo 1524459 2443711 := bstep (se 1 (by rfl) ⟨1832783, by rfl⟩ : syracuseStep 2443711 = 3665567) B3665567
theorem B83528273 : Blo 1524459 83528273 := bstep (se 2 (by rfl) ⟨31323102, by rfl⟩ : syracuseStep 83528273 = 62646205) B62646205
theorem B4345159 : Blo 1524459 4345159 := bstep (se 1 (by rfl) ⟨3258869, by rfl⟩ : syracuseStep 4345159 = 6517739) B6517739
theorem B1715647 : Blo 1524459 1715647 := bstep (se 1 (by rfl) ⟨1286735, by rfl⟩ : syracuseStep 1715647 = 2573471) B2573471
theorem B2289359 : Blo 1524459 2289359 := bstep (se 1 (by rfl) ⟨1717019, by rfl⟩ : syracuseStep 2289359 = 3434039) B3434039
theorem B2289383 : Blo 1524459 2289383 := bstep (se 1 (by rfl) ⟨1717037, by rfl⟩ : syracuseStep 2289383 = 3434075) B3434075
theorem B17379359 : Blo 1524459 17379359 := bstep (se 1 (by rfl) ⟨13034519, by rfl⟩ : syracuseStep 17379359 = 26069039) B26069039
theorem B18551911 : Blo 1524459 18551911 := bstep (se 1 (by rfl) ⟨13913933, by rfl⟩ : syracuseStep 18551911 = 27827867) B27827867
theorem B9770149 : Blo 1524459 9770149 := bstep (se 4 (by rfl) ⟨915951, by rfl⟩ : syracuseStep 9770149 = 1831903) B1831903
theorem B13915471 : Blo 1524459 13915471 := bstep (se 1 (by rfl) ⟨10436603, by rfl⟩ : syracuseStep 13915471 = 20873207) B20873207
theorem B11589641 : Blo 1524459 11589641 := bstep (se 2 (by rfl) ⟨4346115, by rfl⟩ : syracuseStep 11589641 = 8692231) B8692231
theorem B1833067 : Blo 1524459 1833067 := bstep (se 1 (by rfl) ⟨1374800, by rfl⟩ : syracuseStep 1833067 = 2749601) B2749601
theorem B3430583 : Blo 1524459 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B4888765 : Blo 1524459 4888765 := bstep (se 3 (by rfl) ⟨916643, by rfl⟩ : syracuseStep 4888765 = 1833287) B1833287
theorem B9402617 : Blo 1524459 9402617 := bstep (se 2 (by rfl) ⟨3525981, by rfl⟩ : syracuseStep 9402617 = 7051963) B7051963
theorem B47593727 : Blo 1524459 47593727 := bstep (se 1 (by rfl) ⟨35695295, by rfl⟩ : syracuseStep 47593727 = 71390591) B71390591
theorem B44006267 : Blo 1524459 44006267 := bstep (se 1 (by rfl) ⟨33004700, by rfl⟩ : syracuseStep 44006267 = 66009401) B66009401
theorem B3432383 : Blo 1524459 3432383 := bstep (se 1 (by rfl) ⟨2574287, by rfl⟩ : syracuseStep 3432383 = 5148575) B5148575
theorem B3432545 : Blo 1524459 3432545 := bstep (se 2 (by rfl) ⟨1287204, by rfl⟩ : syracuseStep 3432545 = 2574409) B2574409
theorem B7726427 : Blo 1524459 7726427 := bstep (se 1 (by rfl) ⟨5794820, by rfl⟩ : syracuseStep 7726427 = 11589641) B11589641
theorem B2287055 : Blo 1524459 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B6268411 : Blo 1524459 6268411 := bstep (se 1 (by rfl) ⟨4701308, by rfl⟩ : syracuseStep 6268411 = 9402617) B9402617
theorem B31729151 : Blo 1524459 31729151 := bstep (se 1 (by rfl) ⟨23796863, by rfl⟩ : syracuseStep 31729151 = 47593727) B47593727
theorem B13026865 : Blo 1524459 13026865 := bstep (se 2 (by rfl) ⟨4885074, by rfl⟩ : syracuseStep 13026865 = 9770149) B9770149
theorem B1525375 : Blo 1524459 1525375 := bstep (se 1 (by rfl) ⟨1144031, by rfl⟩ : syracuseStep 1525375 = 2288063) B2288063
theorem B5793545 : Blo 1524459 5793545 := bstep (se 2 (by rfl) ⟨2172579, by rfl⟩ : syracuseStep 5793545 = 4345159) B4345159
theorem B2287529 : Blo 1524459 2287529 := bstep (se 2 (by rfl) ⟨857823, by rfl⟩ : syracuseStep 2287529 = 1715647) B1715647
theorem B29337511 : Blo 1524459 29337511 := bstep (se 1 (by rfl) ⟨22003133, by rfl⟩ : syracuseStep 29337511 = 44006267) B44006267
theorem B1526239 : Blo 1524459 1526239 := bstep (se 1 (by rfl) ⟨1144679, by rfl⟩ : syracuseStep 1526239 = 2289359) B2289359
theorem B1526255 : Blo 1524459 1526255 := bstep (se 1 (by rfl) ⟨1144691, by rfl⟩ : syracuseStep 1526255 = 2289383) B2289383
theorem B2288255 : Blo 1524459 2288255 := bstep (se 1 (by rfl) ⟨1716191, by rfl⟩ : syracuseStep 2288255 = 3432383) B3432383
theorem B11586239 : Blo 1524459 11586239 := bstep (se 1 (by rfl) ⟨8689679, by rfl⟩ : syracuseStep 11586239 = 17379359) B17379359
theorem B2444089 : Blo 1524459 2444089 := bstep (se 2 (by rfl) ⟨916533, by rfl⟩ : syracuseStep 2444089 = 1833067) B1833067
theorem B24735881 : Blo 1524459 24735881 := bstep (se 2 (by rfl) ⟨9275955, by rfl⟩ : syracuseStep 24735881 = 18551911) B18551911
theorem B55685515 : Blo 1524459 55685515 := bstep (se 1 (by rfl) ⟨41764136, by rfl⟩ : syracuseStep 55685515 = 83528273) B83528273
theorem B4887935 : Blo 1524459 4887935 := bstep (se 1 (by rfl) ⟨3665951, by rfl⟩ : syracuseStep 4887935 = 7331903) B7331903
theorem B3258281 : Blo 1524459 3258281 := bstep (se 2 (by rfl) ⟨1221855, by rfl⟩ : syracuseStep 3258281 = 2443711) B2443711
theorem B5216303 : Blo 1524459 5216303 := bstep (se 1 (by rfl) ⟨3912227, by rfl⟩ : syracuseStep 5216303 = 7824455) B7824455
theorem B26073413 : Blo 1524459 26073413 := bstep (se 4 (by rfl) ⟨2444382, by rfl⟩ : syracuseStep 26073413 = 4888765) B4888765
theorem B18553961 : Blo 1524459 18553961 := bstep (se 2 (by rfl) ⟨6957735, by rfl⟩ : syracuseStep 18553961 = 13915471) B13915471
theorem B65962349 : Blo 1524459 65962349 := bstep (se 3 (by rfl) ⟨12367940, by rfl⟩ : syracuseStep 65962349 = 24735881) B24735881
theorem B1524703 : Blo 1524459 1524703 := bstep (se 1 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 1524703 = 2287055) B2287055
theorem B21152767 : Blo 1524459 21152767 := bstep (se 1 (by rfl) ⟨15864575, by rfl⟩ : syracuseStep 21152767 = 31729151) B31729151
theorem B1525019 : Blo 1524459 1525019 := bstep (se 1 (by rfl) ⟨1143764, by rfl⟩ : syracuseStep 1525019 = 2287529) B2287529
theorem B2172187 : Blo 1524459 2172187 := bstep (se 1 (by rfl) ⟨1629140, by rfl⟩ : syracuseStep 2172187 = 3258281) B3258281
theorem B1525503 : Blo 1524459 1525503 := bstep (se 1 (by rfl) ⟨1144127, by rfl⟩ : syracuseStep 1525503 = 2288255) B2288255
theorem B17369153 : Blo 1524459 17369153 := bstep (se 2 (by rfl) ⟨6513432, by rfl⟩ : syracuseStep 17369153 = 13026865) B13026865
theorem B2288363 : Blo 1524459 2288363 := bstep (se 1 (by rfl) ⟨1716272, by rfl⟩ : syracuseStep 2288363 = 3432545) B3432545
theorem B74247353 : Blo 1524459 74247353 := bstep (se 2 (by rfl) ⟨27842757, by rfl⟩ : syracuseStep 74247353 = 55685515) B55685515
theorem B3862363 : Blo 1524459 3862363 := bstep (se 1 (by rfl) ⟨2896772, by rfl⟩ : syracuseStep 3862363 = 5793545) B5793545
theorem B3477535 : Blo 1524459 3477535 := bstep (se 1 (by rfl) ⟨2608151, by rfl⟩ : syracuseStep 3477535 = 5216303) B5216303
theorem B5150951 : Blo 1524459 5150951 := bstep (se 1 (by rfl) ⟨3863213, by rfl⟩ : syracuseStep 5150951 = 7726427) B7726427
theorem B3258623 : Blo 1524459 3258623 := bstep (se 1 (by rfl) ⟨2443967, by rfl⟩ : syracuseStep 3258623 = 4887935) B4887935
theorem B3258785 : Blo 1524459 3258785 := bstep (se 2 (by rfl) ⟨1222044, by rfl⟩ : syracuseStep 3258785 = 2444089) B2444089
theorem B17382275 : Blo 1524459 17382275 := bstep (se 1 (by rfl) ⟨13036706, by rfl⟩ : syracuseStep 17382275 = 26073413) B26073413
theorem B7724159 : Blo 1524459 7724159 := bstep (se 1 (by rfl) ⟨5793119, by rfl⟩ : syracuseStep 7724159 = 11586239) B11586239
theorem B12369307 : Blo 1524459 12369307 := bstep (se 1 (by rfl) ⟨9276980, by rfl⟩ : syracuseStep 12369307 = 18553961) B18553961
theorem B39116681 : Blo 1524459 39116681 := bstep (se 2 (by rfl) ⟨14668755, by rfl⟩ : syracuseStep 39116681 = 29337511) B29337511
theorem B33431525 : Blo 1524459 33431525 := bstep (se 4 (by rfl) ⟨3134205, by rfl⟩ : syracuseStep 33431525 = 6268411) B6268411
theorem B43974899 : Blo 1524459 43974899 := bstep (se 1 (by rfl) ⟨32981174, by rfl⟩ : syracuseStep 43974899 = 65962349) B65962349
theorem B74187413 : Blo 1524459 74187413 := bstep (se 6 (by rfl) ⟨1738767, by rfl⟩ : syracuseStep 74187413 = 3477535) B3477535
theorem B3433967 : Blo 1524459 3433967 := bstep (se 1 (by rfl) ⟨2575475, by rfl⟩ : syracuseStep 3433967 = 5150951) B5150951
theorem B2172415 : Blo 1524459 2172415 := bstep (se 1 (by rfl) ⟨1629311, by rfl⟩ : syracuseStep 2172415 = 3258623) B3258623
theorem B2172523 : Blo 1524459 2172523 := bstep (se 1 (by rfl) ⟨1629392, by rfl⟩ : syracuseStep 2172523 = 3258785) B3258785
theorem B1525575 : Blo 1524459 1525575 := bstep (se 1 (by rfl) ⟨1144181, by rfl⟩ : syracuseStep 1525575 = 2288363) B2288363
theorem B16492409 : Blo 1524459 16492409 := bstep (se 2 (by rfl) ⟨6184653, by rfl⟩ : syracuseStep 16492409 = 12369307) B12369307
theorem B49498235 : Blo 1524459 49498235 := bstep (se 1 (by rfl) ⟨37123676, by rfl⟩ : syracuseStep 49498235 = 74247353) B74247353
theorem B26077787 : Blo 1524459 26077787 := bstep (se 1 (by rfl) ⟨19558340, by rfl⟩ : syracuseStep 26077787 = 39116681) B39116681
theorem B11579435 : Blo 1524459 11579435 := bstep (se 1 (by rfl) ⟨8684576, by rfl⟩ : syracuseStep 11579435 = 17369153) B17369153
theorem B2896249 : Blo 1524459 2896249 := bstep (se 2 (by rfl) ⟨1086093, by rfl⟩ : syracuseStep 2896249 = 2172187) B2172187
theorem B11588183 : Blo 1524459 11588183 := bstep (se 1 (by rfl) ⟨8691137, by rfl⟩ : syracuseStep 11588183 = 17382275) B17382275
theorem B5149439 : Blo 1524459 5149439 := bstep (se 1 (by rfl) ⟨3862079, by rfl⟩ : syracuseStep 5149439 = 7724159) B7724159
theorem B5149817 : Blo 1524459 5149817 := bstep (se 2 (by rfl) ⟨1931181, by rfl⟩ : syracuseStep 5149817 = 3862363) B3862363
theorem B22287683 : Blo 1524459 22287683 := bstep (se 1 (by rfl) ⟨16715762, by rfl⟩ : syracuseStep 22287683 = 33431525) B33431525
theorem B28203689 : Blo 1524459 28203689 := bstep (se 2 (by rfl) ⟨10576383, by rfl⟩ : syracuseStep 28203689 = 21152767) B21152767
theorem B7725455 : Blo 1524459 7725455 := bstep (se 1 (by rfl) ⟨5794091, by rfl⟩ : syracuseStep 7725455 = 11588183) B11588183
theorem B3432959 : Blo 1524459 3432959 := bstep (se 1 (by rfl) ⟨2574719, by rfl⟩ : syracuseStep 3432959 = 5149439) B5149439
theorem B3433211 : Blo 1524459 3433211 := bstep (se 1 (by rfl) ⟨2574908, by rfl⟩ : syracuseStep 3433211 = 5149817) B5149817
theorem B59433821 : Blo 1524459 59433821 := bstep (se 3 (by rfl) ⟨11143841, by rfl⟩ : syracuseStep 59433821 = 22287683) B22287683
theorem B10994939 : Blo 1524459 10994939 := bstep (se 1 (by rfl) ⟨8246204, by rfl⟩ : syracuseStep 10994939 = 16492409) B16492409
theorem B32998823 : Blo 1524459 32998823 := bstep (se 1 (by rfl) ⟨24749117, by rfl⟩ : syracuseStep 32998823 = 49498235) B49498235
theorem B17385191 : Blo 1524459 17385191 := bstep (se 1 (by rfl) ⟨13038893, by rfl⟩ : syracuseStep 17385191 = 26077787) B26077787
theorem B18802459 : Blo 1524459 18802459 := bstep (se 1 (by rfl) ⟨14101844, by rfl⟩ : syracuseStep 18802459 = 28203689) B28203689
theorem B7719623 : Blo 1524459 7719623 := bstep (se 1 (by rfl) ⟨5789717, by rfl⟩ : syracuseStep 7719623 = 11579435) B11579435
theorem B49458275 : Blo 1524459 49458275 := bstep (se 1 (by rfl) ⟨37093706, by rfl⟩ : syracuseStep 49458275 = 74187413) B74187413
theorem B3861665 : Blo 1524459 3861665 := bstep (se 2 (by rfl) ⟨1448124, by rfl⟩ : syracuseStep 3861665 = 2896249) B2896249
theorem B2289311 : Blo 1524459 2289311 := bstep (se 1 (by rfl) ⟨1716983, by rfl⟩ : syracuseStep 2289311 = 3433967) B3433967
theorem B2896553 : Blo 1524459 2896553 := bstep (se 2 (by rfl) ⟨1086207, by rfl⟩ : syracuseStep 2896553 = 2172415) B2172415
theorem B2896697 : Blo 1524459 2896697 := bstep (se 2 (by rfl) ⟨1086261, by rfl⟩ : syracuseStep 2896697 = 2172523) B2172523
theorem B29316599 : Blo 1524459 29316599 := bstep (se 1 (by rfl) ⟨21987449, by rfl⟩ : syracuseStep 29316599 = 43974899) B43974899
theorem B100279781 : Blo 1524459 100279781 := bstep (se 4 (by rfl) ⟨9401229, by rfl⟩ : syracuseStep 100279781 = 18802459) B18802459
theorem B5146415 : Blo 1524459 5146415 := bstep (se 1 (by rfl) ⟨3859811, by rfl⟩ : syracuseStep 5146415 = 7719623) B7719623
theorem B2574443 : Blo 1524459 2574443 := bstep (se 1 (by rfl) ⟨1930832, by rfl⟩ : syracuseStep 2574443 = 3861665) B3861665
theorem B1526207 : Blo 1524459 1526207 := bstep (se 1 (by rfl) ⟨1144655, by rfl⟩ : syracuseStep 1526207 = 2289311) B2289311
theorem B2288639 : Blo 1524459 2288639 := bstep (se 1 (by rfl) ⟨1716479, by rfl⟩ : syracuseStep 2288639 = 3432959) B3432959
theorem B2288807 : Blo 1524459 2288807 := bstep (se 1 (by rfl) ⟨1716605, by rfl⟩ : syracuseStep 2288807 = 3433211) B3433211
theorem B21999215 : Blo 1524459 21999215 := bstep (se 1 (by rfl) ⟨16499411, by rfl⟩ : syracuseStep 21999215 = 32998823) B32998823
theorem B5150303 : Blo 1524459 5150303 := bstep (se 1 (by rfl) ⟨3862727, by rfl⟩ : syracuseStep 5150303 = 7725455) B7725455
theorem B1931035 : Blo 1524459 1931035 := bstep (se 1 (by rfl) ⟨1448276, by rfl⟩ : syracuseStep 1931035 = 2896553) B2896553
theorem B1931131 : Blo 1524459 1931131 := bstep (se 1 (by rfl) ⟨1448348, by rfl⟩ : syracuseStep 1931131 = 2896697) B2896697
theorem B39622547 : Blo 1524459 39622547 := bstep (se 1 (by rfl) ⟨29716910, by rfl⟩ : syracuseStep 39622547 = 59433821) B59433821
theorem B7329959 : Blo 1524459 7329959 := bstep (se 1 (by rfl) ⟨5497469, by rfl⟩ : syracuseStep 7329959 = 10994939) B10994939
theorem B19544399 : Blo 1524459 19544399 := bstep (se 1 (by rfl) ⟨14658299, by rfl⟩ : syracuseStep 19544399 = 29316599) B29316599
theorem B11590127 : Blo 1524459 11590127 := bstep (se 1 (by rfl) ⟨8692595, by rfl⟩ : syracuseStep 11590127 = 17385191) B17385191
theorem B32972183 : Blo 1524459 32972183 := bstep (se 1 (by rfl) ⟨24729137, by rfl⟩ : syracuseStep 32972183 = 49458275) B49458275
theorem B3433535 : Blo 1524459 3433535 := bstep (se 1 (by rfl) ⟨2575151, by rfl⟩ : syracuseStep 3433535 = 5150303) B5150303
theorem B7726751 : Blo 1524459 7726751 := bstep (se 1 (by rfl) ⟨5795063, by rfl⟩ : syracuseStep 7726751 = 11590127) B11590127
theorem B1525759 : Blo 1524459 1525759 := bstep (se 1 (by rfl) ⟨1144319, by rfl⟩ : syracuseStep 1525759 = 2288639) B2288639
theorem B1525871 : Blo 1524459 1525871 := bstep (se 1 (by rfl) ⟨1144403, by rfl⟩ : syracuseStep 1525871 = 2288807) B2288807
theorem B21981455 : Blo 1524459 21981455 := bstep (se 1 (by rfl) ⟨16486091, by rfl⟩ : syracuseStep 21981455 = 32972183) B32972183
theorem B2574713 : Blo 1524459 2574713 := bstep (se 2 (by rfl) ⟨965517, by rfl⟩ : syracuseStep 2574713 = 1931035) B1931035
theorem B14666143 : Blo 1524459 14666143 := bstep (se 1 (by rfl) ⟨10999607, by rfl⟩ : syracuseStep 14666143 = 21999215) B21999215
theorem B2574841 : Blo 1524459 2574841 := bstep (se 2 (by rfl) ⟨965565, by rfl⟩ : syracuseStep 2574841 = 1931131) B1931131
theorem B26415031 : Blo 1524459 26415031 := bstep (se 1 (by rfl) ⟨19811273, by rfl⟩ : syracuseStep 26415031 = 39622547) B39622547
theorem B1716295 : Blo 1524459 1716295 := bstep (se 1 (by rfl) ⟨1287221, by rfl⟩ : syracuseStep 1716295 = 2574443) B2574443
theorem B4886639 : Blo 1524459 4886639 := bstep (se 1 (by rfl) ⟨3664979, by rfl⟩ : syracuseStep 4886639 = 7329959) B7329959
theorem B13029599 : Blo 1524459 13029599 := bstep (se 1 (by rfl) ⟨9772199, by rfl⟩ : syracuseStep 13029599 = 19544399) B19544399
theorem B66853187 : Blo 1524459 66853187 := bstep (se 1 (by rfl) ⟨50139890, by rfl⟩ : syracuseStep 66853187 = 100279781) B100279781
theorem B3430943 : Blo 1524459 3430943 := bstep (se 1 (by rfl) ⟨2573207, by rfl⟩ : syracuseStep 3430943 = 5146415) B5146415
theorem B19554857 : Blo 1524459 19554857 := bstep (se 2 (by rfl) ⟨7333071, by rfl⟩ : syracuseStep 19554857 = 14666143) B14666143
theorem B3433121 : Blo 1524459 3433121 := bstep (se 2 (by rfl) ⟨1287420, by rfl⟩ : syracuseStep 3433121 = 2574841) B2574841
theorem B2287295 : Blo 1524459 2287295 := bstep (se 1 (by rfl) ⟨1715471, by rfl⟩ : syracuseStep 2287295 = 3430943) B3430943
theorem B35220041 : Blo 1524459 35220041 := bstep (se 2 (by rfl) ⟨13207515, by rfl⟩ : syracuseStep 35220041 = 26415031) B26415031
theorem B2288393 : Blo 1524459 2288393 := bstep (se 2 (by rfl) ⟨858147, by rfl⟩ : syracuseStep 2288393 = 1716295) B1716295
theorem B8686399 : Blo 1524459 8686399 := bstep (se 1 (by rfl) ⟨6514799, by rfl⟩ : syracuseStep 8686399 = 13029599) B13029599
theorem B2289023 : Blo 1524459 2289023 := bstep (se 1 (by rfl) ⟨1716767, by rfl⟩ : syracuseStep 2289023 = 3433535) B3433535
theorem B44568791 : Blo 1524459 44568791 := bstep (se 1 (by rfl) ⟨33426593, by rfl⟩ : syracuseStep 44568791 = 66853187) B66853187
theorem B1716475 : Blo 1524459 1716475 := bstep (se 1 (by rfl) ⟨1287356, by rfl⟩ : syracuseStep 1716475 = 2574713) B2574713
theorem B3257759 : Blo 1524459 3257759 := bstep (se 1 (by rfl) ⟨2443319, by rfl⟩ : syracuseStep 3257759 = 4886639) B4886639
theorem B5151167 : Blo 1524459 5151167 := bstep (se 1 (by rfl) ⟨3863375, by rfl⟩ : syracuseStep 5151167 = 7726751) B7726751
theorem B14654303 : Blo 1524459 14654303 := bstep (se 1 (by rfl) ⟨10990727, by rfl⟩ : syracuseStep 14654303 = 21981455) B21981455
theorem B29712527 : Blo 1524459 29712527 := bstep (se 1 (by rfl) ⟨22284395, by rfl⟩ : syracuseStep 29712527 = 44568791) B44568791
theorem B1524863 : Blo 1524459 1524863 := bstep (se 1 (by rfl) ⟨1143647, by rfl⟩ : syracuseStep 1524863 = 2287295) B2287295
theorem B3434111 : Blo 1524459 3434111 := bstep (se 1 (by rfl) ⟨2575583, by rfl⟩ : syracuseStep 3434111 = 5151167) B5151167
theorem B23480027 : Blo 1524459 23480027 := bstep (se 1 (by rfl) ⟨17610020, by rfl⟩ : syracuseStep 23480027 = 35220041) B35220041
theorem B1525595 : Blo 1524459 1525595 := bstep (se 1 (by rfl) ⟨1144196, by rfl⟩ : syracuseStep 1525595 = 2288393) B2288393
theorem B1526015 : Blo 1524459 1526015 := bstep (se 1 (by rfl) ⟨1144511, by rfl⟩ : syracuseStep 1526015 = 2289023) B2289023
theorem B2288633 : Blo 1524459 2288633 := bstep (se 2 (by rfl) ⟨858237, by rfl⟩ : syracuseStep 2288633 = 1716475) B1716475
theorem B13036571 : Blo 1524459 13036571 := bstep (se 1 (by rfl) ⟨9777428, by rfl⟩ : syracuseStep 13036571 = 19554857) B19554857
theorem B2288747 : Blo 1524459 2288747 := bstep (se 1 (by rfl) ⟨1716560, by rfl⟩ : syracuseStep 2288747 = 3433121) B3433121
theorem B8687357 : Blo 1524459 8687357 := bstep (se 3 (by rfl) ⟨1628879, by rfl⟩ : syracuseStep 8687357 = 3257759) B3257759
theorem B9769535 : Blo 1524459 9769535 := bstep (se 1 (by rfl) ⟨7327151, by rfl⟩ : syracuseStep 9769535 = 14654303) B14654303
theorem B11581865 : Blo 1524459 11581865 := bstep (se 2 (by rfl) ⟨4343199, by rfl⟩ : syracuseStep 11581865 = 8686399) B8686399
theorem B19808351 : Blo 1524459 19808351 := bstep (se 1 (by rfl) ⟨14856263, by rfl⟩ : syracuseStep 19808351 = 29712527) B29712527
theorem B6513023 : Blo 1524459 6513023 := bstep (se 1 (by rfl) ⟨4884767, by rfl⟩ : syracuseStep 6513023 = 9769535) B9769535
theorem B1525755 : Blo 1524459 1525755 := bstep (se 1 (by rfl) ⟨1144316, by rfl⟩ : syracuseStep 1525755 = 2288633) B2288633
theorem B1525831 : Blo 1524459 1525831 := bstep (se 1 (by rfl) ⟨1144373, by rfl⟩ : syracuseStep 1525831 = 2288747) B2288747
theorem B2289407 : Blo 1524459 2289407 := bstep (se 1 (by rfl) ⟨1717055, by rfl⟩ : syracuseStep 2289407 = 3434111) B3434111
theorem B7721243 : Blo 1524459 7721243 := bstep (se 1 (by rfl) ⟨5790932, by rfl⟩ : syracuseStep 7721243 = 11581865) B11581865
theorem B15653351 : Blo 1524459 15653351 := bstep (se 1 (by rfl) ⟨11740013, by rfl⟩ : syracuseStep 15653351 = 23480027) B23480027
theorem B8691047 : Blo 1524459 8691047 := bstep (se 1 (by rfl) ⟨6518285, by rfl⟩ : syracuseStep 8691047 = 13036571) B13036571
theorem B5791571 : Blo 1524459 5791571 := bstep (se 1 (by rfl) ⟨4343678, by rfl⟩ : syracuseStep 5791571 = 8687357) B8687357
theorem B13205567 : Blo 1524459 13205567 := bstep (se 1 (by rfl) ⟨9904175, by rfl⟩ : syracuseStep 13205567 = 19808351) B19808351
theorem B4342015 : Blo 1524459 4342015 := bstep (se 1 (by rfl) ⟨3256511, by rfl⟩ : syracuseStep 4342015 = 6513023) B6513023
theorem B5794031 : Blo 1524459 5794031 := bstep (se 1 (by rfl) ⟨4345523, by rfl⟩ : syracuseStep 5794031 = 8691047) B8691047
theorem B1526271 : Blo 1524459 1526271 := bstep (se 1 (by rfl) ⟨1144703, by rfl⟩ : syracuseStep 1526271 = 2289407) B2289407
theorem B3861047 : Blo 1524459 3861047 := bstep (se 1 (by rfl) ⟨2895785, by rfl⟩ : syracuseStep 3861047 = 5791571) B5791571
theorem B5147495 : Blo 1524459 5147495 := bstep (se 1 (by rfl) ⟨3860621, by rfl⟩ : syracuseStep 5147495 = 7721243) B7721243
theorem B10435567 : Blo 1524459 10435567 := bstep (se 1 (by rfl) ⟨7826675, by rfl⟩ : syracuseStep 10435567 = 15653351) B15653351
theorem B2574031 : Blo 1524459 2574031 := bstep (se 1 (by rfl) ⟨1930523, by rfl⟩ : syracuseStep 2574031 = 3861047) B3861047
theorem B13914089 : Blo 1524459 13914089 := bstep (se 2 (by rfl) ⟨5217783, by rfl⟩ : syracuseStep 13914089 = 10435567) B10435567
theorem B3862687 : Blo 1524459 3862687 := bstep (se 1 (by rfl) ⟨2897015, by rfl⟩ : syracuseStep 3862687 = 5794031) B5794031
theorem B8803711 : Blo 1524459 8803711 := bstep (se 1 (by rfl) ⟨6602783, by rfl⟩ : syracuseStep 8803711 = 13205567) B13205567
theorem B5789353 : Blo 1524459 5789353 := bstep (se 2 (by rfl) ⟨2171007, by rfl⟩ : syracuseStep 5789353 = 4342015) B4342015
theorem B3431663 : Blo 1524459 3431663 := bstep (se 1 (by rfl) ⟨2573747, by rfl⟩ : syracuseStep 3431663 = 5147495) B5147495
theorem B2287775 : Blo 1524459 2287775 := bstep (se 1 (by rfl) ⟨1715831, by rfl⟩ : syracuseStep 2287775 = 3431663) B3431663
theorem B7719137 : Blo 1524459 7719137 := bstep (se 2 (by rfl) ⟨2894676, by rfl⟩ : syracuseStep 7719137 = 5789353) B5789353
theorem B9276059 : Blo 1524459 9276059 := bstep (se 1 (by rfl) ⟨6957044, by rfl⟩ : syracuseStep 9276059 = 13914089) B13914089
theorem B46953125 : Blo 1524459 46953125 := bstep (se 4 (by rfl) ⟨4401855, by rfl⟩ : syracuseStep 46953125 = 8803711) B8803711
theorem B5150249 : Blo 1524459 5150249 := bstep (se 2 (by rfl) ⟨1931343, by rfl⟩ : syracuseStep 5150249 = 3862687) B3862687
theorem B3432041 : Blo 1524459 3432041 := bstep (se 2 (by rfl) ⟨1287015, by rfl⟩ : syracuseStep 3432041 = 2574031) B2574031
theorem B31302083 : Blo 1524459 31302083 := bstep (se 1 (by rfl) ⟨23476562, by rfl⟩ : syracuseStep 31302083 = 46953125) B46953125
theorem B3433499 : Blo 1524459 3433499 := bstep (se 1 (by rfl) ⟨2575124, by rfl⟩ : syracuseStep 3433499 = 5150249) B5150249
theorem B1525183 : Blo 1524459 1525183 := bstep (se 1 (by rfl) ⟨1143887, by rfl⟩ : syracuseStep 1525183 = 2287775) B2287775
theorem B5146091 : Blo 1524459 5146091 := bstep (se 1 (by rfl) ⟨3859568, by rfl⟩ : syracuseStep 5146091 = 7719137) B7719137
theorem B2288027 : Blo 1524459 2288027 := bstep (se 1 (by rfl) ⟨1716020, by rfl⟩ : syracuseStep 2288027 = 3432041) B3432041
theorem B6184039 : Blo 1524459 6184039 := bstep (se 1 (by rfl) ⟨4638029, by rfl⟩ : syracuseStep 6184039 = 9276059) B9276059
theorem B1525351 : Blo 1524459 1525351 := bstep (se 1 (by rfl) ⟨1144013, by rfl⟩ : syracuseStep 1525351 = 2288027) B2288027
theorem B2288999 : Blo 1524459 2288999 := bstep (se 1 (by rfl) ⟨1716749, by rfl⟩ : syracuseStep 2288999 = 3433499) B3433499
theorem B83472221 : Blo 1524459 83472221 := bstep (se 3 (by rfl) ⟨15651041, by rfl⟩ : syracuseStep 83472221 = 31302083) B31302083
theorem B8245385 : Blo 1524459 8245385 := bstep (se 2 (by rfl) ⟨3092019, by rfl⟩ : syracuseStep 8245385 = 6184039) B6184039
theorem B3430727 : Blo 1524459 3430727 := bstep (se 1 (by rfl) ⟨2573045, by rfl⟩ : syracuseStep 3430727 = 5146091) B5146091
theorem B5496923 : Blo 1524459 5496923 := bstep (se 1 (by rfl) ⟨4122692, by rfl⟩ : syracuseStep 5496923 = 8245385) B8245385
theorem B2287151 : Blo 1524459 2287151 := bstep (se 1 (by rfl) ⟨1715363, by rfl⟩ : syracuseStep 2287151 = 3430727) B3430727
theorem B1525999 : Blo 1524459 1525999 := bstep (se 1 (by rfl) ⟨1144499, by rfl⟩ : syracuseStep 1525999 = 2288999) B2288999
theorem B55648147 : Blo 1524459 55648147 := bstep (se 1 (by rfl) ⟨41736110, by rfl⟩ : syracuseStep 55648147 = 83472221) B83472221
theorem B1524767 : Blo 1524459 1524767 := bstep (se 1 (by rfl) ⟨1143575, by rfl⟩ : syracuseStep 1524767 = 2287151) B2287151
theorem B74197529 : Blo 1524459 74197529 := bstep (se 2 (by rfl) ⟨27824073, by rfl⟩ : syracuseStep 74197529 = 55648147) B55648147
theorem B3664615 : Blo 1524459 3664615 := bstep (se 1 (by rfl) ⟨2748461, by rfl⟩ : syracuseStep 3664615 = 5496923) B5496923
theorem B49465019 : Blo 1524459 49465019 := bstep (se 1 (by rfl) ⟨37098764, by rfl⟩ : syracuseStep 49465019 = 74197529) B74197529
theorem B4886153 : Blo 1524459 4886153 := bstep (se 2 (by rfl) ⟨1832307, by rfl⟩ : syracuseStep 4886153 = 3664615) B3664615
theorem B32976679 : Blo 1524459 32976679 := bstep (se 1 (by rfl) ⟨24732509, by rfl⟩ : syracuseStep 32976679 = 49465019) B49465019
theorem B3257435 : Blo 1524459 3257435 := bstep (se 1 (by rfl) ⟨2443076, by rfl⟩ : syracuseStep 3257435 = 4886153) B4886153
theorem B2171623 : Blo 1524459 2171623 := bstep (se 1 (by rfl) ⟨1628717, by rfl⟩ : syracuseStep 2171623 = 3257435) B3257435
theorem B43968905 : Blo 1524459 43968905 := bstep (se 2 (by rfl) ⟨16488339, by rfl⟩ : syracuseStep 43968905 = 32976679) B32976679
theorem B29312603 : Blo 1524459 29312603 := bstep (se 1 (by rfl) ⟨21984452, by rfl⟩ : syracuseStep 29312603 = 43968905) B43968905
theorem B2895497 : Blo 1524459 2895497 := bstep (se 2 (by rfl) ⟨1085811, by rfl⟩ : syracuseStep 2895497 = 2171623) B2171623
theorem B19541735 : Blo 1524459 19541735 := bstep (se 1 (by rfl) ⟨14656301, by rfl⟩ : syracuseStep 19541735 = 29312603) B29312603
theorem B1930331 : Blo 1524459 1930331 := bstep (se 1 (by rfl) ⟨1447748, by rfl⟩ : syracuseStep 1930331 = 2895497) B2895497
theorem B13027823 : Blo 1524459 13027823 := bstep (se 1 (by rfl) ⟨9770867, by rfl⟩ : syracuseStep 13027823 = 19541735) B19541735
theorem B5147549 : Blo 1524459 5147549 := bstep (se 3 (by rfl) ⟨965165, by rfl⟩ : syracuseStep 5147549 = 1930331) B1930331
theorem B8685215 : Blo 1524459 8685215 := bstep (se 1 (by rfl) ⟨6513911, by rfl⟩ : syracuseStep 8685215 = 13027823) B13027823
theorem B3431699 : Blo 1524459 3431699 := bstep (se 1 (by rfl) ⟨2573774, by rfl⟩ : syracuseStep 3431699 = 5147549) B5147549
theorem B2287799 : Blo 1524459 2287799 := bstep (se 1 (by rfl) ⟨1715849, by rfl⟩ : syracuseStep 2287799 = 3431699) B3431699
theorem B5790143 : Blo 1524459 5790143 := bstep (se 1 (by rfl) ⟨4342607, by rfl⟩ : syracuseStep 5790143 = 8685215) B8685215
theorem B1525199 : Blo 1524459 1525199 := bstep (se 1 (by rfl) ⟨1143899, by rfl⟩ : syracuseStep 1525199 = 2287799) B2287799
theorem B3860095 : Blo 1524459 3860095 := bstep (se 1 (by rfl) ⟨2895071, by rfl⟩ : syracuseStep 3860095 = 5790143) B5790143
theorem B5146793 : Blo 1524459 5146793 := bstep (se 2 (by rfl) ⟨1930047, by rfl⟩ : syracuseStep 5146793 = 3860095) B3860095
theorem B3431195 : Blo 1524459 3431195 := bstep (se 1 (by rfl) ⟨2573396, by rfl⟩ : syracuseStep 3431195 = 5146793) B5146793
theorem B2287463 : Blo 1524459 2287463 := bstep (se 1 (by rfl) ⟨1715597, by rfl⟩ : syracuseStep 2287463 = 3431195) B3431195
theorem B1524975 : Blo 1524459 1524975 := bstep (se 1 (by rfl) ⟨1143731, by rfl⟩ : syracuseStep 1524975 = 2287463) B2287463

theorem C0 (j : ℕ) (h1 : 381114 ≤ j) (h2 : j ≤ 381614) : Blo 1524459 (4 * j + 3) := by
  interval_cases j
  · exact B1524459
  · exact B1524463
  · exact B1524467
  · exact B1524471
  · exact B1524475
  · exact B1524479
  · exact B1524483
  · exact B1524487
  · exact B1524491
  · exact B1524495
  · exact B1524499
  · exact B1524503
  · exact B1524507
  · exact B1524511
  · exact B1524515
  · exact B1524519
  · exact B1524523
  · exact B1524527
  · exact B1524531
  · exact B1524535
  · exact B1524539
  · exact B1524543
  · exact B1524547
  · exact B1524551
  · exact B1524555
  · exact B1524559
  · exact B1524563
  · exact B1524567
  · exact B1524571
  · exact B1524575
  · exact B1524579
  · exact B1524583
  · exact B1524587
  · exact B1524591
  · exact B1524595
  · exact B1524599
  · exact B1524603
  · exact B1524607
  · exact B1524611
  · exact B1524615
  · exact B1524619
  · exact B1524623
  · exact B1524627
  · exact B1524631
  · exact B1524635
  · exact B1524639
  · exact B1524643
  · exact B1524647
  · exact B1524651
  · exact B1524655
  · exact B1524659
  · exact B1524663
  · exact B1524667
  · exact B1524671
  · exact B1524675
  · exact B1524679
  · exact B1524683
  · exact B1524687
  · exact B1524691
  · exact B1524695
  · exact B1524699
  · exact B1524703
  · exact B1524707
  · exact B1524711
  · exact B1524715
  · exact B1524719
  · exact B1524723
  · exact B1524727
  · exact B1524731
  · exact B1524735
  · exact B1524739
  · exact B1524743
  · exact B1524747
  · exact B1524751
  · exact B1524755
  · exact B1524759
  · exact B1524763
  · exact B1524767
  · exact B1524771
  · exact B1524775
  · exact B1524779
  · exact B1524783
  · exact B1524787
  · exact B1524791
  · exact B1524795
  · exact B1524799
  · exact B1524803
  · exact B1524807
  · exact B1524811
  · exact B1524815
  · exact B1524819
  · exact B1524823
  · exact B1524827
  · exact B1524831
  · exact B1524835
  · exact B1524839
  · exact B1524843
  · exact B1524847
  · exact B1524851
  · exact B1524855
  · exact B1524859
  · exact B1524863
  · exact B1524867
  · exact B1524871
  · exact B1524875
  · exact B1524879
  · exact B1524883
  · exact B1524887
  · exact B1524891
  · exact B1524895
  · exact B1524899
  · exact B1524903
  · exact B1524907
  · exact B1524911
  · exact B1524915
  · exact B1524919
  · exact B1524923
  · exact B1524927
  · exact B1524931
  · exact B1524935
  · exact B1524939
  · exact B1524943
  · exact B1524947
  · exact B1524951
  · exact B1524955
  · exact B1524959
  · exact B1524963
  · exact B1524967
  · exact B1524971
  · exact B1524975
  · exact B1524979
  · exact B1524983
  · exact B1524987
  · exact B1524991
  · exact B1524995
  · exact B1524999
  · exact B1525003
  · exact B1525007
  · exact B1525011
  · exact B1525015
  · exact B1525019
  · exact B1525023
  · exact B1525027
  · exact B1525031
  · exact B1525035
  · exact B1525039
  · exact B1525043
  · exact B1525047
  · exact B1525051
  · exact B1525055
  · exact B1525059
  · exact B1525063
  · exact B1525067
  · exact B1525071
  · exact B1525075
  · exact B1525079
  · exact B1525083
  · exact B1525087
  · exact B1525091
  · exact B1525095
  · exact B1525099
  · exact B1525103
  · exact B1525107
  · exact B1525111
  · exact B1525115
  · exact B1525119
  · exact B1525123
  · exact B1525127
  · exact B1525131
  · exact B1525135
  · exact B1525139
  · exact B1525143
  · exact B1525147
  · exact B1525151
  · exact B1525155
  · exact B1525159
  · exact B1525163
  · exact B1525167
  · exact B1525171
  · exact B1525175
  · exact B1525179
  · exact B1525183
  · exact B1525187
  · exact B1525191
  · exact B1525195
  · exact B1525199
  · exact B1525203
  · exact B1525207
  · exact B1525211
  · exact B1525215
  · exact B1525219
  · exact B1525223
  · exact B1525227
  · exact B1525231
  · exact B1525235
  · exact B1525239
  · exact B1525243
  · exact B1525247
  · exact B1525251
  · exact B1525255
  · exact B1525259
  · exact B1525263
  · exact B1525267
  · exact B1525271
  · exact B1525275
  · exact B1525279
  · exact B1525283
  · exact B1525287
  · exact B1525291
  · exact B1525295
  · exact B1525299
  · exact B1525303
  · exact B1525307
  · exact B1525311
  · exact B1525315
  · exact B1525319
  · exact B1525323
  · exact B1525327
  · exact B1525331
  · exact B1525335
  · exact B1525339
  · exact B1525343
  · exact B1525347
  · exact B1525351
  · exact B1525355
  · exact B1525359
  · exact B1525363
  · exact B1525367
  · exact B1525371
  · exact B1525375
  · exact B1525379
  · exact B1525383
  · exact B1525387
  · exact B1525391
  · exact B1525395
  · exact B1525399
  · exact B1525403
  · exact B1525407
  · exact B1525411
  · exact B1525415
  · exact B1525419
  · exact B1525423
  · exact B1525427
  · exact B1525431
  · exact B1525435
  · exact B1525439
  · exact B1525443
  · exact B1525447
  · exact B1525451
  · exact B1525455
  · exact B1525459
  · exact B1525463
  · exact B1525467
  · exact B1525471
  · exact B1525475
  · exact B1525479
  · exact B1525483
  · exact B1525487
  · exact B1525491
  · exact B1525495
  · exact B1525499
  · exact B1525503
  · exact B1525507
  · exact B1525511
  · exact B1525515
  · exact B1525519
  · exact B1525523
  · exact B1525527
  · exact B1525531
  · exact B1525535
  · exact B1525539
  · exact B1525543
  · exact B1525547
  · exact B1525551
  · exact B1525555
  · exact B1525559
  · exact B1525563
  · exact B1525567
  · exact B1525571
  · exact B1525575
  · exact B1525579
  · exact B1525583
  · exact B1525587
  · exact B1525591
  · exact B1525595
  · exact B1525599
  · exact B1525603
  · exact B1525607
  · exact B1525611
  · exact B1525615
  · exact B1525619
  · exact B1525623
  · exact B1525627
  · exact B1525631
  · exact B1525635
  · exact B1525639
  · exact B1525643
  · exact B1525647
  · exact B1525651
  · exact B1525655
  · exact B1525659
  · exact B1525663
  · exact B1525667
  · exact B1525671
  · exact B1525675
  · exact B1525679
  · exact B1525683
  · exact B1525687
  · exact B1525691
  · exact B1525695
  · exact B1525699
  · exact B1525703
  · exact B1525707
  · exact B1525711
  · exact B1525715
  · exact B1525719
  · exact B1525723
  · exact B1525727
  · exact B1525731
  · exact B1525735
  · exact B1525739
  · exact B1525743
  · exact B1525747
  · exact B1525751
  · exact B1525755
  · exact B1525759
  · exact B1525763
  · exact B1525767
  · exact B1525771
  · exact B1525775
  · exact B1525779
  · exact B1525783
  · exact B1525787
  · exact B1525791
  · exact B1525795
  · exact B1525799
  · exact B1525803
  · exact B1525807
  · exact B1525811
  · exact B1525815
  · exact B1525819
  · exact B1525823
  · exact B1525827
  · exact B1525831
  · exact B1525835
  · exact B1525839
  · exact B1525843
  · exact B1525847
  · exact B1525851
  · exact B1525855
  · exact B1525859
  · exact B1525863
  · exact B1525867
  · exact B1525871
  · exact B1525875
  · exact B1525879
  · exact B1525883
  · exact B1525887
  · exact B1525891
  · exact B1525895
  · exact B1525899
  · exact B1525903
  · exact B1525907
  · exact B1525911
  · exact B1525915
  · exact B1525919
  · exact B1525923
  · exact B1525927
  · exact B1525931
  · exact B1525935
  · exact B1525939
  · exact B1525943
  · exact B1525947
  · exact B1525951
  · exact B1525955
  · exact B1525959
  · exact B1525963
  · exact B1525967
  · exact B1525971
  · exact B1525975
  · exact B1525979
  · exact B1525983
  · exact B1525987
  · exact B1525991
  · exact B1525995
  · exact B1525999
  · exact B1526003
  · exact B1526007
  · exact B1526011
  · exact B1526015
  · exact B1526019
  · exact B1526023
  · exact B1526027
  · exact B1526031
  · exact B1526035
  · exact B1526039
  · exact B1526043
  · exact B1526047
  · exact B1526051
  · exact B1526055
  · exact B1526059
  · exact B1526063
  · exact B1526067
  · exact B1526071
  · exact B1526075
  · exact B1526079
  · exact B1526083
  · exact B1526087
  · exact B1526091
  · exact B1526095
  · exact B1526099
  · exact B1526103
  · exact B1526107
  · exact B1526111
  · exact B1526115
  · exact B1526119
  · exact B1526123
  · exact B1526127
  · exact B1526131
  · exact B1526135
  · exact B1526139
  · exact B1526143
  · exact B1526147
  · exact B1526151
  · exact B1526155
  · exact B1526159
  · exact B1526163
  · exact B1526167
  · exact B1526171
  · exact B1526175
  · exact B1526179
  · exact B1526183
  · exact B1526187
  · exact B1526191
  · exact B1526195
  · exact B1526199
  · exact B1526203
  · exact B1526207
  · exact B1526211
  · exact B1526215
  · exact B1526219
  · exact B1526223
  · exact B1526227
  · exact B1526231
  · exact B1526235
  · exact B1526239
  · exact B1526243
  · exact B1526247
  · exact B1526251
  · exact B1526255
  · exact B1526259
  · exact B1526263
  · exact B1526267
  · exact B1526271
  · exact B1526275
  · exact B1526279
  · exact B1526283
  · exact B1526287
  · exact B1526291
  · exact B1526295
  · exact B1526299
  · exact B1526303
  · exact B1526307
  · exact B1526311
  · exact B1526315
  · exact B1526319
  · exact B1526323
  · exact B1526327
  · exact B1526331
  · exact B1526335
  · exact B1526339
  · exact B1526343
  · exact B1526347
  · exact B1526351
  · exact B1526355
  · exact B1526359
  · exact B1526363
  · exact B1526367
  · exact B1526371
  · exact B1526375
  · exact B1526379
  · exact B1526383
  · exact B1526387
  · exact B1526391
  · exact B1526395
  · exact B1526399
  · exact B1526403
  · exact B1526407
  · exact B1526411
  · exact B1526415
  · exact B1526419
  · exact B1526423
  · exact B1526427
  · exact B1526431
  · exact B1526435
  · exact B1526439
  · exact B1526443
  · exact B1526447
  · exact B1526451
  · exact B1526455
  · exact B1526459

theorem solution (m : ℕ) (hlo : 1524459 ≤ m) (hhi : m ≤ 1526459) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 381114 ≤ j := by omega
    have hj2 : j ≤ 381614 := by omega
    have hb : Blo 1524459 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
