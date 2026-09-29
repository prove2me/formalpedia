-- Prove2me | solution 1 for syracuse_descends_range_346754_350754
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:35.499641+00:00
-- url     : https://prove2.me/submissions/1e2464d9-97df-4509-a0cc-c51cd6582186

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


theorem B786437 : Blo 346754 786437 := bbase (se 4 (by rfl) ⟨73728, by rfl⟩ : syracuseStep 786437 = 147457) (by norm_num)
theorem B524309 : Blo 346754 524309 := bbase (se 6 (by rfl) ⟨12288, by rfl⟩ : syracuseStep 524309 = 24577) (by norm_num)
theorem B393241 : Blo 346754 393241 := bbase (se 2 (by rfl) ⟨147465, by rfl⟩ : syracuseStep 393241 = 294931) (by norm_num)
theorem B524333 : Blo 346754 524333 := bbase (se 3 (by rfl) ⟨98312, by rfl⟩ : syracuseStep 524333 = 196625) (by norm_num)
theorem B1769525 : Blo 346754 1769525 := bbase (se 5 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 1769525 = 165893) (by norm_num)
theorem B393277 : Blo 346754 393277 := bbase (se 3 (by rfl) ⟨73739, by rfl⟩ : syracuseStep 393277 = 147479) (by norm_num)
theorem B524357 : Blo 346754 524357 := bbase (se 4 (by rfl) ⟨49158, by rfl⟩ : syracuseStep 524357 = 98317) (by norm_num)
theorem B786509 : Blo 346754 786509 := bbase (se 3 (by rfl) ⟨147470, by rfl⟩ : syracuseStep 786509 = 294941) (by norm_num)
theorem B589909 : Blo 346754 589909 := bbase (se 8 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 589909 = 6913) (by norm_num)
theorem B524381 : Blo 346754 524381 := bbase (se 3 (by rfl) ⟨98321, by rfl⟩ : syracuseStep 524381 = 196643) (by norm_num)
theorem B393313 : Blo 346754 393313 := bbase (se 2 (by rfl) ⟨147492, by rfl⟩ : syracuseStep 393313 = 294985) (by norm_num)
theorem B524405 : Blo 346754 524405 := bbase (se 5 (by rfl) ⟨24581, by rfl⟩ : syracuseStep 524405 = 49163) (by norm_num)
theorem B393349 : Blo 346754 393349 := bbase (se 4 (by rfl) ⟨36876, by rfl⟩ : syracuseStep 393349 = 73753) (by norm_num)
theorem B524429 : Blo 346754 524429 := bbase (se 3 (by rfl) ⟨98330, by rfl⟩ : syracuseStep 524429 = 196661) (by norm_num)
theorem B786581 : Blo 346754 786581 := bbase (se 6 (by rfl) ⟨18435, by rfl⟩ : syracuseStep 786581 = 36871) (by norm_num)
theorem B524453 : Blo 346754 524453 := bbase (se 4 (by rfl) ⟨49167, by rfl⟩ : syracuseStep 524453 = 98335) (by norm_num)
theorem B393385 : Blo 346754 393385 := bbase (se 2 (by rfl) ⟨147519, by rfl⟩ : syracuseStep 393385 = 295039) (by norm_num)
theorem B589997 : Blo 346754 589997 := bbase (se 3 (by rfl) ⟨110624, by rfl⟩ : syracuseStep 589997 = 221249) (by norm_num)
theorem B557237 : Blo 346754 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B524477 : Blo 346754 524477 := bbase (se 3 (by rfl) ⟨98339, by rfl⟩ : syracuseStep 524477 = 196679) (by norm_num)
theorem B1179845 : Blo 346754 1179845 := bbase (se 4 (by rfl) ⟨110610, by rfl⟩ : syracuseStep 1179845 = 221221) (by norm_num)
theorem B393421 : Blo 346754 393421 := bbase (se 3 (by rfl) ⟨73766, by rfl⟩ : syracuseStep 393421 = 147533) (by norm_num)
theorem B524501 : Blo 346754 524501 := bbase (se 7 (by rfl) ⟨6146, by rfl⟩ : syracuseStep 524501 = 12293) (by norm_num)
theorem B786653 : Blo 346754 786653 := bbase (se 3 (by rfl) ⟨147497, by rfl⟩ : syracuseStep 786653 = 294995) (by norm_num)
theorem B884965 : Blo 346754 884965 := bbase (se 4 (by rfl) ⟨82965, by rfl⟩ : syracuseStep 884965 = 165931) (by norm_num)
theorem B524525 : Blo 346754 524525 := bbase (se 3 (by rfl) ⟨98348, by rfl⟩ : syracuseStep 524525 = 196697) (by norm_num)
theorem B393457 : Blo 346754 393457 := bbase (se 2 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 393457 = 295093) (by norm_num)
theorem B524549 : Blo 346754 524549 := bbase (se 4 (by rfl) ⟨49176, by rfl⟩ : syracuseStep 524549 = 98353) (by norm_num)
theorem B393493 : Blo 346754 393493 := bbase (se 6 (by rfl) ⟨9222, by rfl⟩ : syracuseStep 393493 = 18445) (by norm_num)
theorem B524573 : Blo 346754 524573 := bbase (se 3 (by rfl) ⟨98357, by rfl⟩ : syracuseStep 524573 = 196715) (by norm_num)
theorem B786725 : Blo 346754 786725 := bbase (se 4 (by rfl) ⟨73755, by rfl⟩ : syracuseStep 786725 = 147511) (by norm_num)
theorem B590125 : Blo 346754 590125 := bbase (se 3 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 590125 = 221297) (by norm_num)
theorem B524597 : Blo 346754 524597 := bbase (se 5 (by rfl) ⟨24590, by rfl⟩ : syracuseStep 524597 = 49181) (by norm_num)
theorem B393529 : Blo 346754 393529 := bbase (se 2 (by rfl) ⟨147573, by rfl⟩ : syracuseStep 393529 = 295147) (by norm_num)
theorem B524621 : Blo 346754 524621 := bbase (se 3 (by rfl) ⟨98366, by rfl⟩ : syracuseStep 524621 = 196733) (by norm_num)
theorem B885077 : Blo 346754 885077 := bbase (se 10 (by rfl) ⟨1296, by rfl⟩ : syracuseStep 885077 = 2593) (by norm_num)
theorem B393565 : Blo 346754 393565 := bbase (se 3 (by rfl) ⟨73793, by rfl⟩ : syracuseStep 393565 = 147587) (by norm_num)
theorem B524645 : Blo 346754 524645 := bbase (se 4 (by rfl) ⟨49185, by rfl⟩ : syracuseStep 524645 = 98371) (by norm_num)
theorem B786797 : Blo 346754 786797 := bbase (se 3 (by rfl) ⟨147524, by rfl⟩ : syracuseStep 786797 = 295049) (by norm_num)
theorem B524669 : Blo 346754 524669 := bbase (se 3 (by rfl) ⟨98375, by rfl⟩ : syracuseStep 524669 = 196751) (by norm_num)
theorem B393601 : Blo 346754 393601 := bbase (se 2 (by rfl) ⟨147600, by rfl⟩ : syracuseStep 393601 = 295201) (by norm_num)
theorem B590213 : Blo 346754 590213 := bbase (se 4 (by rfl) ⟨55332, by rfl⟩ : syracuseStep 590213 = 110665) (by norm_num)
theorem B524693 : Blo 346754 524693 := bbase (se 6 (by rfl) ⟨12297, by rfl⟩ : syracuseStep 524693 = 24595) (by norm_num)
theorem B393637 : Blo 346754 393637 := bbase (se 4 (by rfl) ⟨36903, by rfl⟩ : syracuseStep 393637 = 73807) (by norm_num)
theorem B524717 : Blo 346754 524717 := bbase (se 3 (by rfl) ⟨98384, by rfl⟩ : syracuseStep 524717 = 196769) (by norm_num)
theorem B786869 : Blo 346754 786869 := bbase (se 5 (by rfl) ⟨36884, by rfl⟩ : syracuseStep 786869 = 73769) (by norm_num)
theorem B524741 : Blo 346754 524741 := bbase (se 4 (by rfl) ⟨49194, by rfl⟩ : syracuseStep 524741 = 98389) (by norm_num)
theorem B393673 : Blo 346754 393673 := bbase (se 2 (by rfl) ⟨147627, by rfl⟩ : syracuseStep 393673 = 295255) (by norm_num)
theorem B524765 : Blo 346754 524765 := bbase (se 3 (by rfl) ⟨98393, by rfl⟩ : syracuseStep 524765 = 196787) (by norm_num)
theorem B393709 : Blo 346754 393709 := bbase (se 3 (by rfl) ⟨73820, by rfl⟩ : syracuseStep 393709 = 147641) (by norm_num)
theorem B524789 : Blo 346754 524789 := bbase (se 5 (by rfl) ⟨24599, by rfl⟩ : syracuseStep 524789 = 49199) (by norm_num)
theorem B786941 : Blo 346754 786941 := bbase (se 3 (by rfl) ⟨147551, by rfl⟩ : syracuseStep 786941 = 295103) (by norm_num)
theorem B590341 : Blo 346754 590341 := bbase (se 4 (by rfl) ⟨55344, by rfl⟩ : syracuseStep 590341 = 110689) (by norm_num)
theorem B524813 : Blo 346754 524813 := bbase (se 3 (by rfl) ⟨98402, by rfl⟩ : syracuseStep 524813 = 196805) (by norm_num)
theorem B393745 : Blo 346754 393745 := bbase (se 2 (by rfl) ⟨147654, by rfl⟩ : syracuseStep 393745 = 295309) (by norm_num)
theorem B885269 : Blo 346754 885269 := bbase (se 6 (by rfl) ⟨20748, by rfl⟩ : syracuseStep 885269 = 41497) (by norm_num)
theorem B524837 : Blo 346754 524837 := bbase (se 4 (by rfl) ⟨49203, by rfl⟩ : syracuseStep 524837 = 98407) (by norm_num)
theorem B393781 : Blo 346754 393781 := bbase (se 5 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 393781 = 36917) (by norm_num)
theorem B524861 : Blo 346754 524861 := bbase (se 3 (by rfl) ⟨98411, by rfl⟩ : syracuseStep 524861 = 196823) (by norm_num)
theorem B1671749 : Blo 346754 1671749 := bbase (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) (by norm_num)
theorem B787013 : Blo 346754 787013 := bbase (se 4 (by rfl) ⟨73782, by rfl⟩ : syracuseStep 787013 = 147565) (by norm_num)
theorem B524885 : Blo 346754 524885 := bbase (se 8 (by rfl) ⟨3075, by rfl⟩ : syracuseStep 524885 = 6151) (by norm_num)
theorem B393817 : Blo 346754 393817 := bbase (se 2 (by rfl) ⟨147681, by rfl⟩ : syracuseStep 393817 = 295363) (by norm_num)
theorem B590429 : Blo 346754 590429 := bbase (se 3 (by rfl) ⟨110705, by rfl⟩ : syracuseStep 590429 = 221411) (by norm_num)
theorem B524909 : Blo 346754 524909 := bbase (se 3 (by rfl) ⟨98420, by rfl⟩ : syracuseStep 524909 = 196841) (by norm_num)
theorem B1180277 : Blo 346754 1180277 := bbase (se 5 (by rfl) ⟨55325, by rfl⟩ : syracuseStep 1180277 = 110651) (by norm_num)
theorem B393853 : Blo 346754 393853 := bbase (se 3 (by rfl) ⟨73847, by rfl⟩ : syracuseStep 393853 = 147695) (by norm_num)
theorem B524933 : Blo 346754 524933 := bbase (se 4 (by rfl) ⟨49212, by rfl⟩ : syracuseStep 524933 = 98425) (by norm_num)
theorem B787085 : Blo 346754 787085 := bbase (se 3 (by rfl) ⟨147578, by rfl⟩ : syracuseStep 787085 = 295157) (by norm_num)
theorem B524957 : Blo 346754 524957 := bbase (se 3 (by rfl) ⟨98429, by rfl⟩ : syracuseStep 524957 = 196859) (by norm_num)
theorem B393889 : Blo 346754 393889 := bbase (se 2 (by rfl) ⟨147708, by rfl⟩ : syracuseStep 393889 = 295417) (by norm_num)
theorem B524981 : Blo 346754 524981 := bbase (se 5 (by rfl) ⟨24608, by rfl⟩ : syracuseStep 524981 = 49217) (by norm_num)
theorem B393925 : Blo 346754 393925 := bbase (se 4 (by rfl) ⟨36930, by rfl⟩ : syracuseStep 393925 = 73861) (by norm_num)
theorem B525005 : Blo 346754 525005 := bbase (se 3 (by rfl) ⟨98438, by rfl⟩ : syracuseStep 525005 = 196877) (by norm_num)
theorem B787157 : Blo 346754 787157 := bbase (se 7 (by rfl) ⟨9224, by rfl⟩ : syracuseStep 787157 = 18449) (by norm_num)
theorem B590557 : Blo 346754 590557 := bbase (se 3 (by rfl) ⟨110729, by rfl⟩ : syracuseStep 590557 = 221459) (by norm_num)
theorem B525029 : Blo 346754 525029 := bbase (se 4 (by rfl) ⟨49221, by rfl⟩ : syracuseStep 525029 = 98443) (by norm_num)
theorem B393961 : Blo 346754 393961 := bbase (se 2 (by rfl) ⟨147735, by rfl⟩ : syracuseStep 393961 = 295471) (by norm_num)
theorem B525053 : Blo 346754 525053 := bbase (se 3 (by rfl) ⟨98447, by rfl⟩ : syracuseStep 525053 = 196895) (by norm_num)
theorem B393997 : Blo 346754 393997 := bbase (se 3 (by rfl) ⟨73874, by rfl⟩ : syracuseStep 393997 = 147749) (by norm_num)
theorem B525077 : Blo 346754 525077 := bbase (se 6 (by rfl) ⟨12306, by rfl⟩ : syracuseStep 525077 = 24613) (by norm_num)
theorem B787229 : Blo 346754 787229 := bbase (se 3 (by rfl) ⟨147605, by rfl⟩ : syracuseStep 787229 = 295211) (by norm_num)
theorem B525101 : Blo 346754 525101 := bbase (se 3 (by rfl) ⟨98456, by rfl⟩ : syracuseStep 525101 = 196913) (by norm_num)
theorem B394033 : Blo 346754 394033 := bbase (se 2 (by rfl) ⟨147762, by rfl⟩ : syracuseStep 394033 = 295525) (by norm_num)
theorem B590645 : Blo 346754 590645 := bbase (se 5 (by rfl) ⟨27686, by rfl⟩ : syracuseStep 590645 = 55373) (by norm_num)
theorem B525125 : Blo 346754 525125 := bbase (se 4 (by rfl) ⟨49230, by rfl⟩ : syracuseStep 525125 = 98461) (by norm_num)
theorem B394069 : Blo 346754 394069 := bbase (se 9 (by rfl) ⟨1154, by rfl⟩ : syracuseStep 394069 = 2309) (by norm_num)
theorem B525149 : Blo 346754 525149 := bbase (se 3 (by rfl) ⟨98465, by rfl⟩ : syracuseStep 525149 = 196931) (by norm_num)
theorem B787301 : Blo 346754 787301 := bbase (se 4 (by rfl) ⟨73809, by rfl⟩ : syracuseStep 787301 = 147619) (by norm_num)
theorem B885613 : Blo 346754 885613 := bbase (se 3 (by rfl) ⟨166052, by rfl⟩ : syracuseStep 885613 = 332105) (by norm_num)
theorem B525173 : Blo 346754 525173 := bbase (se 5 (by rfl) ⟨24617, by rfl⟩ : syracuseStep 525173 = 49235) (by norm_num)
theorem B394105 : Blo 346754 394105 := bbase (se 2 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 394105 = 295579) (by norm_num)
theorem B525197 : Blo 346754 525197 := bbase (se 3 (by rfl) ⟨98474, by rfl⟩ : syracuseStep 525197 = 196949) (by norm_num)
theorem B394141 : Blo 346754 394141 := bbase (se 3 (by rfl) ⟨73901, by rfl⟩ : syracuseStep 394141 = 147803) (by norm_num)
theorem B525221 : Blo 346754 525221 := bbase (se 4 (by rfl) ⟨49239, by rfl⟩ : syracuseStep 525221 = 98479) (by norm_num)
theorem B787373 : Blo 346754 787373 := bbase (se 3 (by rfl) ⟨147632, by rfl⟩ : syracuseStep 787373 = 295265) (by norm_num)
theorem B590773 : Blo 346754 590773 := bbase (se 5 (by rfl) ⟨27692, by rfl⟩ : syracuseStep 590773 = 55385) (by norm_num)
theorem B525245 : Blo 346754 525245 := bbase (se 3 (by rfl) ⟨98483, by rfl⟩ : syracuseStep 525245 = 196967) (by norm_num)
theorem B852925 : Blo 346754 852925 := bbase (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) (by norm_num)
theorem B394177 : Blo 346754 394177 := bbase (se 2 (by rfl) ⟨147816, by rfl⟩ : syracuseStep 394177 = 295633) (by norm_num)
theorem B525269 : Blo 346754 525269 := bbase (se 7 (by rfl) ⟨6155, by rfl⟩ : syracuseStep 525269 = 12311) (by norm_num)
theorem B885725 : Blo 346754 885725 := bbase (se 3 (by rfl) ⟨166073, by rfl⟩ : syracuseStep 885725 = 332147) (by norm_num)
theorem B394213 : Blo 346754 394213 := bbase (se 4 (by rfl) ⟨36957, by rfl⟩ : syracuseStep 394213 = 73915) (by norm_num)
theorem B525293 : Blo 346754 525293 := bbase (se 3 (by rfl) ⟨98492, by rfl⟩ : syracuseStep 525293 = 196985) (by norm_num)
theorem B2556917 : Blo 346754 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B787445 : Blo 346754 787445 := bbase (se 5 (by rfl) ⟨36911, by rfl⟩ : syracuseStep 787445 = 73823) (by norm_num)
theorem B525317 : Blo 346754 525317 := bbase (se 4 (by rfl) ⟨49248, by rfl⟩ : syracuseStep 525317 = 98497) (by norm_num)
theorem B394249 : Blo 346754 394249 := bbase (se 2 (by rfl) ⟨147843, by rfl⟩ : syracuseStep 394249 = 295687) (by norm_num)
theorem B590861 : Blo 346754 590861 := bbase (se 3 (by rfl) ⟨110786, by rfl⟩ : syracuseStep 590861 = 221573) (by norm_num)
theorem B525341 : Blo 346754 525341 := bbase (se 3 (by rfl) ⟨98501, by rfl⟩ : syracuseStep 525341 = 197003) (by norm_num)
theorem B1180709 : Blo 346754 1180709 := bbase (se 4 (by rfl) ⟨110691, by rfl⟩ : syracuseStep 1180709 = 221383) (by norm_num)
theorem B394285 : Blo 346754 394285 := bbase (se 3 (by rfl) ⟨73928, by rfl⟩ : syracuseStep 394285 = 147857) (by norm_num)
theorem B525365 : Blo 346754 525365 := bbase (se 5 (by rfl) ⟨24626, by rfl⟩ : syracuseStep 525365 = 49253) (by norm_num)
theorem B787517 : Blo 346754 787517 := bbase (se 3 (by rfl) ⟨147659, by rfl⟩ : syracuseStep 787517 = 295319) (by norm_num)
theorem B525389 : Blo 346754 525389 := bbase (se 3 (by rfl) ⟨98510, by rfl⟩ : syracuseStep 525389 = 197021) (by norm_num)
theorem B394321 : Blo 346754 394321 := bbase (se 2 (by rfl) ⟨147870, by rfl⟩ : syracuseStep 394321 = 295741) (by norm_num)
theorem B558173 : Blo 346754 558173 := bbase (se 3 (by rfl) ⟨104657, by rfl⟩ : syracuseStep 558173 = 209315) (by norm_num)
theorem B525413 : Blo 346754 525413 := bbase (se 4 (by rfl) ⟨49257, by rfl⟩ : syracuseStep 525413 = 98515) (by norm_num)
theorem B394357 : Blo 346754 394357 := bbase (se 5 (by rfl) ⟨18485, by rfl⟩ : syracuseStep 394357 = 36971) (by norm_num)
theorem B525437 : Blo 346754 525437 := bbase (se 3 (by rfl) ⟨98519, by rfl⟩ : syracuseStep 525437 = 197039) (by norm_num)
theorem B787589 : Blo 346754 787589 := bbase (se 4 (by rfl) ⟨73836, by rfl⟩ : syracuseStep 787589 = 147673) (by norm_num)
theorem B590989 : Blo 346754 590989 := bbase (se 3 (by rfl) ⟨110810, by rfl⟩ : syracuseStep 590989 = 221621) (by norm_num)
theorem B525461 : Blo 346754 525461 := bbase (se 6 (by rfl) ⟨12315, by rfl⟩ : syracuseStep 525461 = 24631) (by norm_num)
theorem B394393 : Blo 346754 394393 := bbase (se 2 (by rfl) ⟨147897, by rfl⟩ : syracuseStep 394393 = 295795) (by norm_num)
theorem B885917 : Blo 346754 885917 := bbase (se 3 (by rfl) ⟨166109, by rfl⟩ : syracuseStep 885917 = 332219) (by norm_num)
theorem B525485 : Blo 346754 525485 := bbase (se 3 (by rfl) ⟨98528, by rfl⟩ : syracuseStep 525485 = 197057) (by norm_num)
theorem B394429 : Blo 346754 394429 := bbase (se 3 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 394429 = 147911) (by norm_num)
theorem B525509 : Blo 346754 525509 := bbase (se 4 (by rfl) ⟨49266, by rfl⟩ : syracuseStep 525509 = 98533) (by norm_num)
theorem B787661 : Blo 346754 787661 := bbase (se 3 (by rfl) ⟨147686, by rfl⟩ : syracuseStep 787661 = 295373) (by norm_num)
theorem B525533 : Blo 346754 525533 := bbase (se 3 (by rfl) ⟨98537, by rfl⟩ : syracuseStep 525533 = 197075) (by norm_num)
theorem B394465 : Blo 346754 394465 := bbase (se 2 (by rfl) ⟨147924, by rfl⟩ : syracuseStep 394465 = 295849) (by norm_num)
theorem B591077 : Blo 346754 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B525557 : Blo 346754 525557 := bbase (se 5 (by rfl) ⟨24635, by rfl⟩ : syracuseStep 525557 = 49271) (by norm_num)
theorem B394501 : Blo 346754 394501 := bbase (se 4 (by rfl) ⟨36984, by rfl⟩ : syracuseStep 394501 = 73969) (by norm_num)
theorem B525581 : Blo 346754 525581 := bbase (se 3 (by rfl) ⟨98546, by rfl⟩ : syracuseStep 525581 = 197093) (by norm_num)
theorem B787733 : Blo 346754 787733 := bbase (se 6 (by rfl) ⟨18462, by rfl⟩ : syracuseStep 787733 = 36925) (by norm_num)
theorem B525605 : Blo 346754 525605 := bbase (se 4 (by rfl) ⟨49275, by rfl⟩ : syracuseStep 525605 = 98551) (by norm_num)
theorem B394537 : Blo 346754 394537 := bbase (se 2 (by rfl) ⟨147951, by rfl⟩ : syracuseStep 394537 = 295903) (by norm_num)
theorem B525629 : Blo 346754 525629 := bbase (se 3 (by rfl) ⟨98555, by rfl⟩ : syracuseStep 525629 = 197111) (by norm_num)
theorem B1115461 : Blo 346754 1115461 := bbase (se 4 (by rfl) ⟨104574, by rfl⟩ : syracuseStep 1115461 = 209149) (by norm_num)
theorem B1770821 : Blo 346754 1770821 := bbase (se 4 (by rfl) ⟨166014, by rfl⟩ : syracuseStep 1770821 = 332029) (by norm_num)
theorem B394573 : Blo 346754 394573 := bbase (se 3 (by rfl) ⟨73982, by rfl⟩ : syracuseStep 394573 = 147965) (by norm_num)
theorem B1901909 : Blo 346754 1901909 := bbase (se 12 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1901909 = 1393) (by norm_num)
theorem B525653 : Blo 346754 525653 := bbase (se 12 (by rfl) ⟨192, by rfl⟩ : syracuseStep 525653 = 385) (by norm_num)
theorem B787805 : Blo 346754 787805 := bbase (se 3 (by rfl) ⟨147713, by rfl⟩ : syracuseStep 787805 = 295427) (by norm_num)
theorem B591205 : Blo 346754 591205 := bbase (se 4 (by rfl) ⟨55425, by rfl⟩ : syracuseStep 591205 = 110851) (by norm_num)
theorem B525677 : Blo 346754 525677 := bbase (se 3 (by rfl) ⟨98564, by rfl⟩ : syracuseStep 525677 = 197129) (by norm_num)
theorem B1115525 : Blo 346754 1115525 := bbase (se 4 (by rfl) ⟨104580, by rfl⟩ : syracuseStep 1115525 = 209161) (by norm_num)
theorem B525701 : Blo 346754 525701 := bbase (se 4 (by rfl) ⟨49284, by rfl⟩ : syracuseStep 525701 = 98569) (by norm_num)
theorem B525725 : Blo 346754 525725 := bbase (se 3 (by rfl) ⟨98573, by rfl⟩ : syracuseStep 525725 = 197147) (by norm_num)
theorem B787877 : Blo 346754 787877 := bbase (se 4 (by rfl) ⟨73863, by rfl⟩ : syracuseStep 787877 = 147727) (by norm_num)
theorem B525749 : Blo 346754 525749 := bbase (se 5 (by rfl) ⟨24644, by rfl⟩ : syracuseStep 525749 = 49289) (by norm_num)
theorem B591293 : Blo 346754 591293 := bbase (se 3 (by rfl) ⟨110867, by rfl⟩ : syracuseStep 591293 = 221735) (by norm_num)
theorem B525773 : Blo 346754 525773 := bbase (se 3 (by rfl) ⟨98582, by rfl⟩ : syracuseStep 525773 = 197165) (by norm_num)
theorem B3179989 : Blo 346754 3179989 := bbase (se 7 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 3179989 = 74531) (by norm_num)
theorem B1181141 : Blo 346754 1181141 := bbase (se 7 (by rfl) ⟨13841, by rfl⟩ : syracuseStep 1181141 = 27683) (by norm_num)
theorem B558557 : Blo 346754 558557 := bbase (se 3 (by rfl) ⟨104729, by rfl⟩ : syracuseStep 558557 = 209459) (by norm_num)
theorem B755173 : Blo 346754 755173 := bbase (se 4 (by rfl) ⟨70797, by rfl⟩ : syracuseStep 755173 = 141595) (by norm_num)
theorem B525797 : Blo 346754 525797 := bbase (se 4 (by rfl) ⟨49293, by rfl⟩ : syracuseStep 525797 = 98587) (by norm_num)
theorem B787949 : Blo 346754 787949 := bbase (se 3 (by rfl) ⟨147740, by rfl⟩ : syracuseStep 787949 = 295481) (by norm_num)
theorem B886261 : Blo 346754 886261 := bbase (se 5 (by rfl) ⟨41543, by rfl⟩ : syracuseStep 886261 = 83087) (by norm_num)
theorem B525821 : Blo 346754 525821 := bbase (se 3 (by rfl) ⟨98591, by rfl⟩ : syracuseStep 525821 = 197183) (by norm_num)
theorem B525845 : Blo 346754 525845 := bbase (se 6 (by rfl) ⟨12324, by rfl⟩ : syracuseStep 525845 = 24649) (by norm_num)
theorem B525869 : Blo 346754 525869 := bbase (se 3 (by rfl) ⟨98600, by rfl⟩ : syracuseStep 525869 = 197201) (by norm_num)
theorem B788021 : Blo 346754 788021 := bbase (se 5 (by rfl) ⟨36938, by rfl⟩ : syracuseStep 788021 = 73877) (by norm_num)
theorem B591421 : Blo 346754 591421 := bbase (se 3 (by rfl) ⟨110891, by rfl⟩ : syracuseStep 591421 = 221783) (by norm_num)
theorem B525893 : Blo 346754 525893 := bbase (se 4 (by rfl) ⟨49302, by rfl⟩ : syracuseStep 525893 = 98605) (by norm_num)
theorem B558685 : Blo 346754 558685 := bbase (se 3 (by rfl) ⟨104753, by rfl⟩ : syracuseStep 558685 = 209507) (by norm_num)
theorem B525917 : Blo 346754 525917 := bbase (se 3 (by rfl) ⟨98609, by rfl⟩ : syracuseStep 525917 = 197219) (by norm_num)
theorem B886373 : Blo 346754 886373 := bbase (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) (by norm_num)
theorem B525941 : Blo 346754 525941 := bbase (se 5 (by rfl) ⟨24653, by rfl⟩ : syracuseStep 525941 = 49307) (by norm_num)
theorem B788093 : Blo 346754 788093 := bbase (se 3 (by rfl) ⟨147767, by rfl⟩ : syracuseStep 788093 = 295535) (by norm_num)
theorem B525965 : Blo 346754 525965 := bbase (se 3 (by rfl) ⟨98618, by rfl⟩ : syracuseStep 525965 = 197237) (by norm_num)
theorem B2393749 : Blo 346754 2393749 := bbase (se 6 (by rfl) ⟨56103, by rfl⟩ : syracuseStep 2393749 = 112207) (by norm_num)
theorem B591509 : Blo 346754 591509 := bbase (se 6 (by rfl) ⟨13863, by rfl⟩ : syracuseStep 591509 = 27727) (by norm_num)
theorem B525989 : Blo 346754 525989 := bbase (se 4 (by rfl) ⟨49311, by rfl⟩ : syracuseStep 525989 = 98623) (by norm_num)
theorem B526013 : Blo 346754 526013 := bbase (se 3 (by rfl) ⟨98627, by rfl⟩ : syracuseStep 526013 = 197255) (by norm_num)
theorem B788165 : Blo 346754 788165 := bbase (se 4 (by rfl) ⟨73890, by rfl⟩ : syracuseStep 788165 = 147781) (by norm_num)
theorem B526037 : Blo 346754 526037 := bbase (se 7 (by rfl) ⟨6164, by rfl⟩ : syracuseStep 526037 = 12329) (by norm_num)
theorem B526061 : Blo 346754 526061 := bbase (se 3 (by rfl) ⟨98636, by rfl⟩ : syracuseStep 526061 = 197273) (by norm_num)
theorem B2655989 : Blo 346754 2655989 := bbase (se 5 (by rfl) ⟨124499, by rfl⟩ : syracuseStep 2655989 = 248999) (by norm_num)
theorem B526085 : Blo 346754 526085 := bbase (se 4 (by rfl) ⟨49320, by rfl⟩ : syracuseStep 526085 = 98641) (by norm_num)
theorem B788237 : Blo 346754 788237 := bbase (se 3 (by rfl) ⟨147794, by rfl⟩ : syracuseStep 788237 = 295589) (by norm_num)
theorem B591637 : Blo 346754 591637 := bbase (se 6 (by rfl) ⟨13866, by rfl⟩ : syracuseStep 591637 = 27733) (by norm_num)
theorem B526109 : Blo 346754 526109 := bbase (se 3 (by rfl) ⟨98645, by rfl⟩ : syracuseStep 526109 = 197291) (by norm_num)
theorem B886565 : Blo 346754 886565 := bbase (se 4 (by rfl) ⟨83115, by rfl⟩ : syracuseStep 886565 = 166231) (by norm_num)
theorem B788309 : Blo 346754 788309 := bbase (se 9 (by rfl) ⟨2309, by rfl⟩ : syracuseStep 788309 = 4619) (by norm_num)
theorem B591725 : Blo 346754 591725 := bbase (se 3 (by rfl) ⟨110948, by rfl⟩ : syracuseStep 591725 = 221897) (by norm_num)
theorem B1181573 : Blo 346754 1181573 := bbase (se 4 (by rfl) ⟨110772, by rfl⟩ : syracuseStep 1181573 = 221545) (by norm_num)
theorem B788381 : Blo 346754 788381 := bbase (se 3 (by rfl) ⟨147821, by rfl⟩ : syracuseStep 788381 = 295643) (by norm_num)
theorem B788453 : Blo 346754 788453 := bbase (se 4 (by rfl) ⟨73917, by rfl⟩ : syracuseStep 788453 = 147835) (by norm_num)
theorem B591853 : Blo 346754 591853 := bbase (se 3 (by rfl) ⟨110972, by rfl⟩ : syracuseStep 591853 = 221945) (by norm_num)
theorem B788525 : Blo 346754 788525 := bbase (se 3 (by rfl) ⟨147848, by rfl⟩ : syracuseStep 788525 = 295697) (by norm_num)
theorem B788597 : Blo 346754 788597 := bbase (se 5 (by rfl) ⟨36965, by rfl⟩ : syracuseStep 788597 = 73931) (by norm_num)
theorem B886909 : Blo 346754 886909 := bbase (se 3 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 886909 = 332591) (by norm_num)
theorem B1411253 : Blo 346754 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B788669 : Blo 346754 788669 := bbase (se 3 (by rfl) ⟨147875, by rfl⟩ : syracuseStep 788669 = 295751) (by norm_num)
theorem B887021 : Blo 346754 887021 := bbase (se 3 (by rfl) ⟨166316, by rfl⟩ : syracuseStep 887021 = 332633) (by norm_num)
theorem B788741 : Blo 346754 788741 := bbase (se 4 (by rfl) ⟨73944, by rfl⟩ : syracuseStep 788741 = 147889) (by norm_num)
theorem B624917 : Blo 346754 624917 := bbase (se 6 (by rfl) ⟨14646, by rfl⟩ : syracuseStep 624917 = 29293) (by norm_num)
theorem B395561 : Blo 346754 395561 := bbase (se 2 (by rfl) ⟨148335, by rfl⟩ : syracuseStep 395561 = 296671) (by norm_num)
theorem B1182005 : Blo 346754 1182005 := bbase (se 5 (by rfl) ⟨55406, by rfl⟩ : syracuseStep 1182005 = 110813) (by norm_num)
theorem B1706309 : Blo 346754 1706309 := bbase (se 4 (by rfl) ⟨159966, by rfl⟩ : syracuseStep 1706309 = 319933) (by norm_num)
theorem B395597 : Blo 346754 395597 := bbase (se 3 (by rfl) ⟨74174, by rfl⟩ : syracuseStep 395597 = 148349) (by norm_num)
theorem B788813 : Blo 346754 788813 := bbase (se 3 (by rfl) ⟨147902, by rfl⟩ : syracuseStep 788813 = 295805) (by norm_num)
theorem B788885 : Blo 346754 788885 := bbase (se 6 (by rfl) ⟨18489, by rfl⟩ : syracuseStep 788885 = 36979) (by norm_num)
theorem B625061 : Blo 346754 625061 := bbase (se 4 (by rfl) ⟨58599, by rfl⟩ : syracuseStep 625061 = 117199) (by norm_num)
theorem B887213 : Blo 346754 887213 := bbase (se 3 (by rfl) ⟨166352, by rfl⟩ : syracuseStep 887213 = 332705) (by norm_num)
theorem B494029 : Blo 346754 494029 := bbase (se 3 (by rfl) ⟨92630, by rfl⟩ : syracuseStep 494029 = 185261) (by norm_num)
theorem B788957 : Blo 346754 788957 := bbase (se 3 (by rfl) ⟨147929, by rfl⟩ : syracuseStep 788957 = 295859) (by norm_num)
theorem B789029 : Blo 346754 789029 := bbase (se 4 (by rfl) ⟨73971, by rfl⟩ : syracuseStep 789029 = 147943) (by norm_num)
theorem B625205 : Blo 346754 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B559685 : Blo 346754 559685 := bbase (se 4 (by rfl) ⟨52470, by rfl⟩ : syracuseStep 559685 = 104941) (by norm_num)
theorem B1772117 : Blo 346754 1772117 := bbase (se 8 (by rfl) ⟨10383, by rfl⟩ : syracuseStep 1772117 = 20767) (by norm_num)
theorem B789101 : Blo 346754 789101 := bbase (se 3 (by rfl) ⟨147956, by rfl⟩ : syracuseStep 789101 = 295913) (by norm_num)
theorem B625277 : Blo 346754 625277 := bbase (se 3 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 625277 = 234479) (by norm_num)
theorem B428689 : Blo 346754 428689 := bbase (se 2 (by rfl) ⟨160758, by rfl⟩ : syracuseStep 428689 = 321517) (by norm_num)
theorem B789173 : Blo 346754 789173 := bbase (se 5 (by rfl) ⟨36992, by rfl⟩ : syracuseStep 789173 = 73985) (by norm_num)
theorem B559813 : Blo 346754 559813 := bbase (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) (by norm_num)
theorem B1182437 : Blo 346754 1182437 := bbase (se 4 (by rfl) ⟨110853, by rfl⟩ : syracuseStep 1182437 = 221707) (by norm_num)
theorem B887557 : Blo 346754 887557 := bbase (se 4 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 887557 = 166417) (by norm_num)
theorem B494365 : Blo 346754 494365 := bbase (se 3 (by rfl) ⟨92693, by rfl⟩ : syracuseStep 494365 = 185387) (by norm_num)
theorem B887669 : Blo 346754 887669 := bbase (se 5 (by rfl) ⟨41609, by rfl⟩ : syracuseStep 887669 = 83219) (by norm_num)
theorem B396181 : Blo 346754 396181 := bbase (se 6 (by rfl) ⟨9285, by rfl⟩ : syracuseStep 396181 = 18571) (by norm_num)
theorem B494581 : Blo 346754 494581 := bbase (se 5 (by rfl) ⟨23183, by rfl⟩ : syracuseStep 494581 = 46367) (by norm_num)
theorem B658469 : Blo 346754 658469 := bbase (se 4 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 658469 = 123463) (by norm_num)
theorem B560197 : Blo 346754 560197 := bbase (se 4 (by rfl) ⟨52518, by rfl⟩ : syracuseStep 560197 = 105037) (by norm_num)
theorem B2821205 : Blo 346754 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B1182869 : Blo 346754 1182869 := bbase (se 6 (by rfl) ⟨27723, by rfl⟩ : syracuseStep 1182869 = 55447) (by norm_num)
theorem B658621 : Blo 346754 658621 := bbase (se 3 (by rfl) ⟨123491, by rfl⟩ : syracuseStep 658621 = 246983) (by norm_num)
theorem B560453 : Blo 346754 560453 := bbase (se 4 (by rfl) ⟨52542, by rfl⟩ : syracuseStep 560453 = 105085) (by norm_num)
theorem B494957 : Blo 346754 494957 := bbase (se 3 (by rfl) ⟨92804, by rfl⟩ : syracuseStep 494957 = 185609) (by norm_num)
theorem B658925 : Blo 346754 658925 := bbase (se 3 (by rfl) ⟨123548, by rfl⟩ : syracuseStep 658925 = 247097) (by norm_num)
theorem B1183301 : Blo 346754 1183301 := bbase (se 4 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 1183301 = 221869) (by norm_num)
theorem B626525 : Blo 346754 626525 := bbase (se 3 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 626525 = 234947) (by norm_num)
theorem B1773413 : Blo 346754 1773413 := bbase (se 4 (by rfl) ⟨166257, by rfl⟩ : syracuseStep 1773413 = 332515) (by norm_num)
theorem B1183733 : Blo 346754 1183733 := bbase (se 5 (by rfl) ⟨55487, by rfl⟩ : syracuseStep 1183733 = 110975) (by norm_num)
theorem B561325 : Blo 346754 561325 := bbase (se 3 (by rfl) ⟨105248, by rfl⟩ : syracuseStep 561325 = 210497) (by norm_num)
theorem B9539797 : Blo 346754 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B659677 : Blo 346754 659677 := bbase (se 3 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 659677 = 247379) (by norm_num)
theorem B561421 : Blo 346754 561421 := bbase (se 3 (by rfl) ⟨105266, by rfl⟩ : syracuseStep 561421 = 210533) (by norm_num)
theorem B1118549 : Blo 346754 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B659821 : Blo 346754 659821 := bbase (se 3 (by rfl) ⟨123716, by rfl⟩ : syracuseStep 659821 = 247433) (by norm_num)
theorem B561581 : Blo 346754 561581 := bbase (se 3 (by rfl) ⟨105296, by rfl⟩ : syracuseStep 561581 = 210593) (by norm_num)
theorem B397801 : Blo 346754 397801 := bbase (se 2 (by rfl) ⟨149175, by rfl⟩ : syracuseStep 397801 = 298351) (by norm_num)
theorem B659981 : Blo 346754 659981 := bbase (se 3 (by rfl) ⟨123746, by rfl⟩ : syracuseStep 659981 = 247493) (by norm_num)
theorem B660125 : Blo 346754 660125 := bbase (se 3 (by rfl) ⟨123773, by rfl⟩ : syracuseStep 660125 = 247547) (by norm_num)
theorem B3347189 : Blo 346754 3347189 := bbase (se 5 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 3347189 = 313799) (by norm_num)
theorem B496381 : Blo 346754 496381 := bbase (se 3 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 496381 = 186143) (by norm_num)
theorem B660413 : Blo 346754 660413 := bbase (se 3 (by rfl) ⟨123827, by rfl⟩ : syracuseStep 660413 = 247655) (by norm_num)
theorem B660565 : Blo 346754 660565 := bbase (se 8 (by rfl) ⟨3870, by rfl⟩ : syracuseStep 660565 = 7741) (by norm_num)
theorem B3970133 : Blo 346754 3970133 := bbase (se 8 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 3970133 = 46525) (by norm_num)
theorem B1774709 : Blo 346754 1774709 := bbase (se 5 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 1774709 = 166379) (by norm_num)
theorem B791677 : Blo 346754 791677 := bbase (se 3 (by rfl) ⟨148439, by rfl⟩ : syracuseStep 791677 = 296879) (by norm_num)
theorem B595277 : Blo 346754 595277 := bbase (se 3 (by rfl) ⟨111614, by rfl⟩ : syracuseStep 595277 = 223229) (by norm_num)
theorem B496973 : Blo 346754 496973 := bbase (se 3 (by rfl) ⟨93182, by rfl⟩ : syracuseStep 496973 = 186365) (by norm_num)
theorem B660869 : Blo 346754 660869 := bbase (se 4 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 660869 = 123913) (by norm_num)
theorem B497053 : Blo 346754 497053 := bbase (se 3 (by rfl) ⟨93197, by rfl⟩ : syracuseStep 497053 = 186395) (by norm_num)
theorem B988661 : Blo 346754 988661 := bbase (se 5 (by rfl) ⟨46343, by rfl⟩ : syracuseStep 988661 = 92687) (by norm_num)
theorem B497173 : Blo 346754 497173 := bbase (se 6 (by rfl) ⟨11652, by rfl⟩ : syracuseStep 497173 = 23305) (by norm_num)
theorem B497269 : Blo 346754 497269 := bbase (se 5 (by rfl) ⟨23309, by rfl⟩ : syracuseStep 497269 = 46619) (by norm_num)
theorem B890677 : Blo 346754 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B628549 : Blo 346754 628549 := bbase (se 4 (by rfl) ⟨58926, by rfl⟩ : syracuseStep 628549 = 117853) (by norm_num)
theorem B530285 : Blo 346754 530285 := bbase (se 3 (by rfl) ⟨99428, by rfl⟩ : syracuseStep 530285 = 198857) (by norm_num)
theorem B530533 : Blo 346754 530533 := bbase (se 4 (by rfl) ⟨49737, by rfl⟩ : syracuseStep 530533 = 99475) (by norm_num)
theorem B497765 : Blo 346754 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B661621 : Blo 346754 661621 := bbase (se 5 (by rfl) ⟨31013, by rfl⟩ : syracuseStep 661621 = 62027) (by norm_num)
theorem B661765 : Blo 346754 661765 := bbase (se 4 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 661765 = 124081) (by norm_num)
theorem B792845 : Blo 346754 792845 := bbase (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) (by norm_num)
theorem B661925 : Blo 346754 661925 := bbase (se 4 (by rfl) ⟨62055, by rfl⟩ : syracuseStep 661925 = 124111) (by norm_num)
theorem B662069 : Blo 346754 662069 := bbase (se 5 (by rfl) ⟨31034, by rfl⟩ : syracuseStep 662069 = 62069) (by norm_num)
theorem B498317 : Blo 346754 498317 := bbase (se 3 (by rfl) ⟨93434, by rfl⟩ : syracuseStep 498317 = 186869) (by norm_num)
theorem B629429 : Blo 346754 629429 := bbase (se 5 (by rfl) ⟨29504, by rfl⟩ : syracuseStep 629429 = 59009) (by norm_num)
theorem B1317653 : Blo 346754 1317653 := bbase (se 6 (by rfl) ⟨30882, by rfl⟩ : syracuseStep 1317653 = 61765) (by norm_num)
theorem B662357 : Blo 346754 662357 := bbase (se 9 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 662357 = 3881) (by norm_num)
theorem B662509 : Blo 346754 662509 := bbase (se 3 (by rfl) ⟨124220, by rfl⟩ : syracuseStep 662509 = 248441) (by norm_num)
theorem B990245 : Blo 346754 990245 := bbase (se 4 (by rfl) ⟨92835, by rfl⟩ : syracuseStep 990245 = 185671) (by norm_num)
theorem B1317941 : Blo 346754 1317941 := bbase (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) (by norm_num)
theorem B1678421 : Blo 346754 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B2235509 : Blo 346754 2235509 := bbase (se 5 (by rfl) ⟨104789, by rfl⟩ : syracuseStep 2235509 = 209579) (by norm_num)
theorem B2170037 : Blo 346754 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B662813 : Blo 346754 662813 := bbase (se 3 (by rfl) ⟨124277, by rfl⟩ : syracuseStep 662813 = 248555) (by norm_num)
theorem B499069 : Blo 346754 499069 := bbase (se 3 (by rfl) ⟨93575, by rfl⟩ : syracuseStep 499069 = 187151) (by norm_num)
theorem B2989493 : Blo 346754 2989493 := bbase (se 5 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 2989493 = 280265) (by norm_num)
theorem B794261 : Blo 346754 794261 := bbase (se 6 (by rfl) ⟨18615, by rfl⟩ : syracuseStep 794261 = 37231) (by norm_num)
theorem B532133 : Blo 346754 532133 := bbase (se 4 (by rfl) ⟨49887, by rfl⟩ : syracuseStep 532133 = 99775) (by norm_num)
theorem B990917 : Blo 346754 990917 := bbase (se 4 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 990917 = 185797) (by norm_num)
theorem B1679093 : Blo 346754 1679093 := bbase (se 5 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 1679093 = 157415) (by norm_num)
theorem B794413 : Blo 346754 794413 := bbase (se 3 (by rfl) ⟨148952, by rfl⟩ : syracuseStep 794413 = 297905) (by norm_num)
theorem B663565 : Blo 346754 663565 := bbase (se 3 (by rfl) ⟨124418, by rfl⟩ : syracuseStep 663565 = 248837) (by norm_num)
theorem B1122341 : Blo 346754 1122341 := bbase (se 4 (by rfl) ⟨105219, by rfl⟩ : syracuseStep 1122341 = 210439) (by norm_num)
theorem B991349 : Blo 346754 991349 := bbase (se 5 (by rfl) ⟨46469, by rfl⟩ : syracuseStep 991349 = 92939) (by norm_num)
theorem B663709 : Blo 346754 663709 := bbase (se 3 (by rfl) ⟨124445, by rfl⟩ : syracuseStep 663709 = 248891) (by norm_num)
theorem B598213 : Blo 346754 598213 := bbase (se 4 (by rfl) ⟨56082, by rfl⟩ : syracuseStep 598213 = 112165) (by norm_num)
theorem B1319125 : Blo 346754 1319125 := bbase (se 7 (by rfl) ⟨15458, by rfl⟩ : syracuseStep 1319125 = 30917) (by norm_num)
theorem B663869 : Blo 346754 663869 := bbase (se 3 (by rfl) ⟨124475, by rfl⟩ : syracuseStep 663869 = 248951) (by norm_num)
theorem B1188229 : Blo 346754 1188229 := bbase (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) (by norm_num)
theorem B664013 : Blo 346754 664013 := bbase (se 3 (by rfl) ⟨124502, by rfl⟩ : syracuseStep 664013 = 249005) (by norm_num)
theorem B1319429 : Blo 346754 1319429 := bbase (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) (by norm_num)
theorem B664301 : Blo 346754 664301 := bbase (se 3 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 664301 = 249113) (by norm_num)
theorem B992101 : Blo 346754 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B664453 : Blo 346754 664453 := bbase (se 4 (by rfl) ⟨62292, by rfl⟩ : syracuseStep 664453 = 124585) (by norm_num)
theorem B1123253 : Blo 346754 1123253 := bbase (se 5 (by rfl) ⟨52652, by rfl⟩ : syracuseStep 1123253 = 105305) (by norm_num)
theorem B1025141 : Blo 346754 1025141 := bbase (se 5 (by rfl) ⟨48053, by rfl⟩ : syracuseStep 1025141 = 96107) (by norm_num)
theorem B664757 : Blo 346754 664757 := bbase (se 5 (by rfl) ⟨31160, by rfl⟩ : syracuseStep 664757 = 62321) (by norm_num)
theorem B403033 : Blo 346754 403033 := bbase (se 2 (by rfl) ⟨151137, by rfl⟩ : syracuseStep 403033 = 302275) (by norm_num)
theorem B1287845 : Blo 346754 1287845 := bbase (se 4 (by rfl) ⟨120735, by rfl⟩ : syracuseStep 1287845 = 241471) (by norm_num)
theorem B566957 : Blo 346754 566957 := bbase (se 3 (by rfl) ⟨106304, by rfl⟩ : syracuseStep 566957 = 212609) (by norm_num)
theorem B501653 : Blo 346754 501653 := bbase (se 6 (by rfl) ⟨11757, by rfl⟩ : syracuseStep 501653 = 23515) (by norm_num)
theorem B665509 : Blo 346754 665509 := bbase (se 4 (by rfl) ⟨62391, by rfl⟩ : syracuseStep 665509 = 124783) (by norm_num)
theorem B370693 : Blo 346754 370693 := bbase (se 4 (by rfl) ⟨34752, by rfl⟩ : syracuseStep 370693 = 69505) (by norm_num)
theorem B1484837 : Blo 346754 1484837 := bbase (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) (by norm_num)
theorem B665653 : Blo 346754 665653 := bbase (se 5 (by rfl) ⟨31202, by rfl⟩ : syracuseStep 665653 = 62405) (by norm_num)
theorem B370765 : Blo 346754 370765 := bbase (se 3 (by rfl) ⟨69518, by rfl⟩ : syracuseStep 370765 = 139037) (by norm_num)
theorem B3188821 : Blo 346754 3188821 := bbase (se 8 (by rfl) ⟨18684, by rfl⟩ : syracuseStep 3188821 = 37369) (by norm_num)
theorem B403553 : Blo 346754 403553 := bbase (se 2 (by rfl) ⟨151332, by rfl⟩ : syracuseStep 403553 = 302665) (by norm_num)
theorem B1976501 : Blo 346754 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B665813 : Blo 346754 665813 := bbase (se 7 (by rfl) ⟨7802, by rfl⟩ : syracuseStep 665813 = 15605) (by norm_num)
theorem B895349 : Blo 346754 895349 := bbase (se 5 (by rfl) ⟨41969, by rfl⟩ : syracuseStep 895349 = 83939) (by norm_num)
theorem B567685 : Blo 346754 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B371137 : Blo 346754 371137 := bbase (se 2 (by rfl) ⟨139176, by rfl⟩ : syracuseStep 371137 = 278353) (by norm_num)
theorem B4467221 : Blo 346754 4467221 := bbase (se 6 (by rfl) ⟨104700, by rfl⟩ : syracuseStep 4467221 = 209401) (by norm_num)
theorem B1321541 : Blo 346754 1321541 := bbase (se 4 (by rfl) ⟨123894, by rfl⟩ : syracuseStep 1321541 = 247789) (by norm_num)
theorem B2894453 : Blo 346754 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B371513 : Blo 346754 371513 := bbase (se 2 (by rfl) ⟨139317, by rfl⟩ : syracuseStep 371513 = 278635) (by norm_num)
theorem B1321829 : Blo 346754 1321829 := bbase (se 4 (by rfl) ⟨123921, by rfl⟩ : syracuseStep 1321829 = 247843) (by norm_num)
theorem B371585 : Blo 346754 371585 := bbase (se 2 (by rfl) ⟨139344, by rfl⟩ : syracuseStep 371585 = 278689) (by norm_num)
theorem B371773 : Blo 346754 371773 := bbase (se 3 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 371773 = 139415) (by norm_num)
theorem B371957 : Blo 346754 371957 := bbase (se 5 (by rfl) ⟨17435, by rfl⟩ : syracuseStep 371957 = 34871) (by norm_num)
theorem B1256741 : Blo 346754 1256741 := bbase (se 4 (by rfl) ⟨117819, by rfl⟩ : syracuseStep 1256741 = 235639) (by norm_num)
theorem B634277 : Blo 346754 634277 := bbase (se 4 (by rfl) ⟨59463, by rfl⟩ : syracuseStep 634277 = 118927) (by norm_num)
theorem B470461 : Blo 346754 470461 := bbase (se 3 (by rfl) ⟨88211, by rfl⟩ : syracuseStep 470461 = 176423) (by norm_num)
theorem B994949 : Blo 346754 994949 := bbase (se 4 (by rfl) ⟨93276, by rfl⟩ : syracuseStep 994949 = 186553) (by norm_num)
theorem B798373 : Blo 346754 798373 := bbase (se 4 (by rfl) ⟨74847, by rfl⟩ : syracuseStep 798373 = 149695) (by norm_num)
theorem B1486613 : Blo 346754 1486613 := bbase (se 6 (by rfl) ⟨34842, by rfl⟩ : syracuseStep 1486613 = 69685) (by norm_num)
theorem B6893333 : Blo 346754 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B3387253 : Blo 346754 3387253 := bbase (se 5 (by rfl) ⟨158777, by rfl⟩ : syracuseStep 3387253 = 317555) (by norm_num)
theorem B372709 : Blo 346754 372709 := bbase (se 4 (by rfl) ⟨34941, by rfl⟩ : syracuseStep 372709 = 69883) (by norm_num)
theorem B1323013 : Blo 346754 1323013 := bbase (se 4 (by rfl) ⟨124032, by rfl⟩ : syracuseStep 1323013 = 248065) (by norm_num)
theorem B372781 : Blo 346754 372781 := bbase (se 3 (by rfl) ⟨69896, by rfl⟩ : syracuseStep 372781 = 139793) (by norm_num)
theorem B372961 : Blo 346754 372961 := bbase (se 2 (by rfl) ⟨139860, by rfl⟩ : syracuseStep 372961 = 279721) (by norm_num)
theorem B1323317 : Blo 346754 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B1258021 : Blo 346754 1258021 := bbase (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) (by norm_num)
theorem B471629 : Blo 346754 471629 := bbase (se 3 (by rfl) ⟨88430, by rfl⟩ : syracuseStep 471629 = 176861) (by norm_num)
theorem B1421957 : Blo 346754 1421957 := bbase (se 4 (by rfl) ⟨133308, by rfl⟩ : syracuseStep 1421957 = 266617) (by norm_num)
theorem B373405 : Blo 346754 373405 := bbase (se 3 (by rfl) ⟨70013, by rfl⟩ : syracuseStep 373405 = 140027) (by norm_num)
theorem B438949 : Blo 346754 438949 := bbase (se 4 (by rfl) ⟨41151, by rfl⟩ : syracuseStep 438949 = 82303) (by norm_num)
theorem B504517 : Blo 346754 504517 := bbase (se 4 (by rfl) ⟨47298, by rfl⟩ : syracuseStep 504517 = 94597) (by norm_num)
theorem B1585909 : Blo 346754 1585909 := bbase (se 5 (by rfl) ⟨74339, by rfl⟩ : syracuseStep 1585909 = 148679) (by norm_num)
theorem B1487605 : Blo 346754 1487605 := bbase (se 5 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 1487605 = 139463) (by norm_num)
theorem B373529 : Blo 346754 373529 := bbase (se 2 (by rfl) ⟨140073, by rfl⟩ : syracuseStep 373529 = 280147) (by norm_num)
theorem B996133 : Blo 346754 996133 := bbase (se 4 (by rfl) ⟨93387, by rfl⟩ : syracuseStep 996133 = 186775) (by norm_num)
theorem B439121 : Blo 346754 439121 := bbase (se 2 (by rfl) ⟨164670, by rfl⟩ : syracuseStep 439121 = 329341) (by norm_num)
theorem B439177 : Blo 346754 439177 := bbase (se 2 (by rfl) ⟨164691, by rfl⟩ : syracuseStep 439177 = 329383) (by norm_num)
theorem B1880981 : Blo 346754 1880981 := bbase (se 6 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 1880981 = 88171) (by norm_num)
theorem B471997 : Blo 346754 471997 := bbase (se 3 (by rfl) ⟨88499, by rfl⟩ : syracuseStep 471997 = 176999) (by norm_num)
theorem B996293 : Blo 346754 996293 := bbase (se 4 (by rfl) ⟨93402, by rfl⟩ : syracuseStep 996293 = 186805) (by norm_num)
theorem B439273 : Blo 346754 439273 := bbase (se 2 (by rfl) ⟨164727, by rfl⟩ : syracuseStep 439273 = 329455) (by norm_num)
theorem B799741 : Blo 346754 799741 := bbase (se 3 (by rfl) ⟨149951, by rfl⟩ : syracuseStep 799741 = 299903) (by norm_num)
theorem B373781 : Blo 346754 373781 := bbase (se 6 (by rfl) ⟨8760, by rfl⟩ : syracuseStep 373781 = 17521) (by norm_num)
theorem B668701 : Blo 346754 668701 := bbase (se 3 (by rfl) ⟨125381, by rfl⟩ : syracuseStep 668701 = 250763) (by norm_num)
theorem B439445 : Blo 346754 439445 := bbase (se 6 (by rfl) ⟨10299, by rfl⟩ : syracuseStep 439445 = 20599) (by norm_num)
theorem B996533 : Blo 346754 996533 := bbase (se 5 (by rfl) ⟨46712, by rfl⟩ : syracuseStep 996533 = 93425) (by norm_num)
theorem B439501 : Blo 346754 439501 := bbase (se 3 (by rfl) ⟨82406, by rfl⟩ : syracuseStep 439501 = 164813) (by norm_num)
theorem B472277 : Blo 346754 472277 := bbase (se 7 (by rfl) ⟨5534, by rfl⟩ : syracuseStep 472277 = 11069) (by norm_num)
theorem B439597 : Blo 346754 439597 := bbase (se 3 (by rfl) ⟨82424, by rfl⟩ : syracuseStep 439597 = 164849) (by norm_num)
theorem B898397 : Blo 346754 898397 := bbase (se 3 (by rfl) ⟨168449, by rfl⟩ : syracuseStep 898397 = 336899) (by norm_num)
theorem B996725 : Blo 346754 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B374225 : Blo 346754 374225 := bbase (se 2 (by rfl) ⟨140334, by rfl⟩ : syracuseStep 374225 = 280669) (by norm_num)
theorem B439769 : Blo 346754 439769 := bbase (se 2 (by rfl) ⟨164913, by rfl⟩ : syracuseStep 439769 = 329827) (by norm_num)
theorem B439825 : Blo 346754 439825 := bbase (se 2 (by rfl) ⟨164934, by rfl⟩ : syracuseStep 439825 = 329869) (by norm_num)
theorem B439921 : Blo 346754 439921 := bbase (se 2 (by rfl) ⟨164970, by rfl⟩ : syracuseStep 439921 = 329941) (by norm_num)
theorem B833213 : Blo 346754 833213 := bbase (se 3 (by rfl) ⟨156227, by rfl⟩ : syracuseStep 833213 = 312455) (by norm_num)
theorem B374473 : Blo 346754 374473 := bbase (se 2 (by rfl) ⟨140427, by rfl⟩ : syracuseStep 374473 = 280855) (by norm_num)
theorem B440093 : Blo 346754 440093 := bbase (se 3 (by rfl) ⟨82517, by rfl⟩ : syracuseStep 440093 = 165035) (by norm_num)
theorem B440149 : Blo 346754 440149 := bbase (se 9 (by rfl) ⟨1289, by rfl⟩ : syracuseStep 440149 = 2579) (by norm_num)
theorem B669541 : Blo 346754 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B440245 : Blo 346754 440245 := bbase (se 5 (by rfl) ⟨20636, by rfl⟩ : syracuseStep 440245 = 41273) (by norm_num)
theorem B604157 : Blo 346754 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B440417 : Blo 346754 440417 := bbase (se 2 (by rfl) ⟨165156, by rfl⟩ : syracuseStep 440417 = 330313) (by norm_num)
theorem B473197 : Blo 346754 473197 := bbase (se 3 (by rfl) ⟨88724, by rfl⟩ : syracuseStep 473197 = 177449) (by norm_num)
theorem B440473 : Blo 346754 440473 := bbase (se 2 (by rfl) ⟨165177, by rfl⟩ : syracuseStep 440473 = 330355) (by norm_num)
theorem B440569 : Blo 346754 440569 := bbase (se 2 (by rfl) ⟨165213, by rfl⟩ : syracuseStep 440569 = 330427) (by norm_num)
theorem B735517 : Blo 346754 735517 := bbase (se 3 (by rfl) ⟨137909, by rfl⟩ : syracuseStep 735517 = 275819) (by norm_num)
theorem B899381 : Blo 346754 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B997717 : Blo 346754 997717 := bbase (se 10 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 997717 = 2923) (by norm_num)
theorem B1325429 : Blo 346754 1325429 := bbase (se 5 (by rfl) ⟨62129, by rfl⟩ : syracuseStep 1325429 = 124259) (by norm_num)
theorem B440741 : Blo 346754 440741 := bbase (se 4 (by rfl) ⟨41319, by rfl⟩ : syracuseStep 440741 = 82639) (by norm_num)
theorem B440797 : Blo 346754 440797 := bbase (se 3 (by rfl) ⟨82649, by rfl⟩ : syracuseStep 440797 = 165299) (by norm_num)
theorem B1587701 : Blo 346754 1587701 := bbase (se 5 (by rfl) ⟨74423, by rfl⟩ : syracuseStep 1587701 = 148847) (by norm_num)
theorem B440893 : Blo 346754 440893 := bbase (se 3 (by rfl) ⟨82667, by rfl⟩ : syracuseStep 440893 = 165335) (by norm_num)
theorem B1325717 : Blo 346754 1325717 := bbase (se 6 (by rfl) ⟨31071, by rfl⟩ : syracuseStep 1325717 = 62143) (by norm_num)
theorem B604829 : Blo 346754 604829 := bbase (se 3 (by rfl) ⟨113405, by rfl⟩ : syracuseStep 604829 = 226811) (by norm_num)
theorem B441065 : Blo 346754 441065 := bbase (se 2 (by rfl) ⟨165399, by rfl⟩ : syracuseStep 441065 = 330799) (by norm_num)
theorem B441121 : Blo 346754 441121 := bbase (se 2 (by rfl) ⟨165420, by rfl⟩ : syracuseStep 441121 = 330841) (by norm_num)
theorem B441217 : Blo 346754 441217 := bbase (se 2 (by rfl) ⟨165456, by rfl⟩ : syracuseStep 441217 = 330913) (by norm_num)
theorem B441389 : Blo 346754 441389 := bbase (se 3 (by rfl) ⟨82760, by rfl⟩ : syracuseStep 441389 = 165521) (by norm_num)
theorem B441445 : Blo 346754 441445 := bbase (se 4 (by rfl) ⟨41385, by rfl⟩ : syracuseStep 441445 = 82771) (by norm_num)
theorem B375925 : Blo 346754 375925 := bbase (se 5 (by rfl) ⟨17621, by rfl⟩ : syracuseStep 375925 = 35243) (by norm_num)
theorem B441541 : Blo 346754 441541 := bbase (se 4 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 441541 = 82789) (by norm_num)
theorem B670933 : Blo 346754 670933 := bbase (se 7 (by rfl) ⟨7862, by rfl⟩ : syracuseStep 670933 = 15725) (by norm_num)
theorem B441713 : Blo 346754 441713 := bbase (se 2 (by rfl) ⟨165642, by rfl⟩ : syracuseStep 441713 = 331285) (by norm_num)
theorem B998821 : Blo 346754 998821 := bbase (se 4 (by rfl) ⟨93639, by rfl⟩ : syracuseStep 998821 = 187279) (by norm_num)
theorem B441769 : Blo 346754 441769 := bbase (se 2 (by rfl) ⟨165663, by rfl⟩ : syracuseStep 441769 = 331327) (by norm_num)
theorem B1883573 : Blo 346754 1883573 := bbase (se 5 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 1883573 = 176585) (by norm_num)
theorem B703973 : Blo 346754 703973 := bbase (se 4 (by rfl) ⟨65997, by rfl⟩ : syracuseStep 703973 = 131995) (by norm_num)
theorem B441865 : Blo 346754 441865 := bbase (se 2 (by rfl) ⟨165699, by rfl⟩ : syracuseStep 441865 = 331399) (by norm_num)
theorem B442037 : Blo 346754 442037 := bbase (se 5 (by rfl) ⟨20720, by rfl⟩ : syracuseStep 442037 = 41441) (by norm_num)
theorem B442093 : Blo 346754 442093 := bbase (se 3 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 442093 = 165785) (by norm_num)
theorem B835373 : Blo 346754 835373 := bbase (se 3 (by rfl) ⟨156632, by rfl⟩ : syracuseStep 835373 = 313265) (by norm_num)
theorem B1326901 : Blo 346754 1326901 := bbase (se 5 (by rfl) ⟨62198, by rfl⟩ : syracuseStep 1326901 = 124397) (by norm_num)
theorem B442189 : Blo 346754 442189 := bbase (se 3 (by rfl) ⟨82910, by rfl⟩ : syracuseStep 442189 = 165821) (by norm_num)
theorem B442361 : Blo 346754 442361 := bbase (se 2 (by rfl) ⟨165885, by rfl⟩ : syracuseStep 442361 = 331771) (by norm_num)
theorem B442417 : Blo 346754 442417 := bbase (se 2 (by rfl) ⟨165906, by rfl⟩ : syracuseStep 442417 = 331813) (by norm_num)
theorem B1327205 : Blo 346754 1327205 := bbase (se 4 (by rfl) ⟨124425, by rfl⟩ : syracuseStep 1327205 = 248851) (by norm_num)
theorem B442513 : Blo 346754 442513 := bbase (se 2 (by rfl) ⟨165942, by rfl⟩ : syracuseStep 442513 = 331885) (by norm_num)
theorem B377137 : Blo 346754 377137 := bbase (se 2 (by rfl) ⟨141426, by rfl⟩ : syracuseStep 377137 = 282853) (by norm_num)
theorem B1589557 : Blo 346754 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B442685 : Blo 346754 442685 := bbase (se 3 (by rfl) ⟨83003, by rfl⟩ : syracuseStep 442685 = 166007) (by norm_num)
theorem B442741 : Blo 346754 442741 := bbase (se 5 (by rfl) ⟨20753, by rfl⟩ : syracuseStep 442741 = 41507) (by norm_num)
theorem B442837 : Blo 346754 442837 := bbase (se 7 (by rfl) ⟨5189, by rfl⟩ : syracuseStep 442837 = 10379) (by norm_num)
theorem B705125 : Blo 346754 705125 := bbase (se 4 (by rfl) ⟨66105, by rfl⟩ : syracuseStep 705125 = 132211) (by norm_num)
theorem B443009 : Blo 346754 443009 := bbase (se 2 (by rfl) ⟨166128, by rfl⟩ : syracuseStep 443009 = 332257) (by norm_num)
theorem B705205 : Blo 346754 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B443065 : Blo 346754 443065 := bbase (se 2 (by rfl) ⟨166149, by rfl⟩ : syracuseStep 443065 = 332299) (by norm_num)
theorem B443161 : Blo 346754 443161 := bbase (se 2 (by rfl) ⟨166185, by rfl⟩ : syracuseStep 443161 = 332371) (by norm_num)
theorem B1262405 : Blo 346754 1262405 := bbase (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) (by norm_num)
theorem B377773 : Blo 346754 377773 := bbase (se 3 (by rfl) ⟨70832, by rfl⟩ : syracuseStep 377773 = 141665) (by norm_num)
theorem B443333 : Blo 346754 443333 := bbase (se 4 (by rfl) ⟨41562, by rfl⟩ : syracuseStep 443333 = 83125) (by norm_num)
theorem B1262549 : Blo 346754 1262549 := bbase (se 7 (by rfl) ⟨14795, by rfl⟩ : syracuseStep 1262549 = 29591) (by norm_num)
theorem B836605 : Blo 346754 836605 := bbase (se 3 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 836605 = 313727) (by norm_num)
theorem B443389 : Blo 346754 443389 := bbase (se 3 (by rfl) ⟨83135, by rfl⟩ : syracuseStep 443389 = 166271) (by norm_num)
theorem B1197125 : Blo 346754 1197125 := bbase (se 4 (by rfl) ⟨112230, by rfl⟩ : syracuseStep 1197125 = 224461) (by norm_num)
theorem B443485 : Blo 346754 443485 := bbase (se 3 (by rfl) ⟨83153, by rfl⟩ : syracuseStep 443485 = 166307) (by norm_num)
theorem B443657 : Blo 346754 443657 := bbase (se 2 (by rfl) ⟨166371, by rfl⟩ : syracuseStep 443657 = 332743) (by norm_num)
theorem B443713 : Blo 346754 443713 := bbase (se 2 (by rfl) ⟨166392, by rfl⟩ : syracuseStep 443713 = 332785) (by norm_num)
theorem B443809 : Blo 346754 443809 := bbase (se 2 (by rfl) ⟨166428, by rfl⟩ : syracuseStep 443809 = 332857) (by norm_num)
theorem B837029 : Blo 346754 837029 := bbase (se 4 (by rfl) ⟨78471, by rfl⟩ : syracuseStep 837029 = 156943) (by norm_num)
theorem B1492613 : Blo 346754 1492613 := bbase (se 4 (by rfl) ⟨139932, by rfl⟩ : syracuseStep 1492613 = 279865) (by norm_num)
theorem B837317 : Blo 346754 837317 := bbase (se 4 (by rfl) ⟨78498, by rfl⟩ : syracuseStep 837317 = 156997) (by norm_num)
theorem B3786517 : Blo 346754 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B1492901 : Blo 346754 1492901 := bbase (se 4 (by rfl) ⟨139959, by rfl⟩ : syracuseStep 1492901 = 279919) (by norm_num)
theorem B1427557 : Blo 346754 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B1329317 : Blo 346754 1329317 := bbase (se 4 (by rfl) ⟨124623, by rfl⟩ : syracuseStep 1329317 = 249247) (by norm_num)
theorem B2017493 : Blo 346754 2017493 := bbase (se 7 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 2017493 = 47285) (by norm_num)
theorem B1329605 : Blo 346754 1329605 := bbase (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) (by norm_num)
theorem B2640437 : Blo 346754 2640437 := bbase (se 5 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 2640437 = 247541) (by norm_num)
theorem B1493653 : Blo 346754 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B1198901 : Blo 346754 1198901 := bbase (se 5 (by rfl) ⟨56198, by rfl⟩ : syracuseStep 1198901 = 112397) (by norm_num)
theorem B2116469 : Blo 346754 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B2378645 : Blo 346754 2378645 := bbase (se 6 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 2378645 = 111499) (by norm_num)
theorem B2837429 : Blo 346754 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B1494389 : Blo 346754 1494389 := bbase (se 5 (by rfl) ⟨70049, by rfl⟩ : syracuseStep 1494389 = 140099) (by norm_num)
theorem B1756565 : Blo 346754 1756565 := bbase (se 6 (by rfl) ⟨41169, by rfl⟩ : syracuseStep 1756565 = 82339) (by norm_num)
theorem B445873 : Blo 346754 445873 := bbase (se 2 (by rfl) ⟨167202, by rfl⟩ : syracuseStep 445873 = 334405) (by norm_num)
theorem B1330789 : Blo 346754 1330789 := bbase (se 4 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 1330789 = 249523) (by norm_num)
theorem B708221 : Blo 346754 708221 := bbase (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) (by norm_num)
theorem B1986389 : Blo 346754 1986389 := bbase (se 9 (by rfl) ⟨5819, by rfl⟩ : syracuseStep 1986389 = 11639) (by norm_num)
theorem B1331093 : Blo 346754 1331093 := bbase (se 6 (by rfl) ⟨31197, by rfl⟩ : syracuseStep 1331093 = 62395) (by norm_num)
theorem B741325 : Blo 346754 741325 := bbase (se 3 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 741325 = 277997) (by norm_num)
theorem B2019541 : Blo 346754 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B1757861 : Blo 346754 1757861 := bbase (se 4 (by rfl) ⟨164799, by rfl⟩ : syracuseStep 1757861 = 329599) (by norm_num)
theorem B840469 : Blo 346754 840469 := bbase (se 6 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 840469 = 39397) (by norm_num)
theorem B742213 : Blo 346754 742213 := bbase (se 4 (by rfl) ⟨69582, by rfl⟩ : syracuseStep 742213 = 139165) (by norm_num)
theorem B7131989 : Blo 346754 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B4445077 : Blo 346754 4445077 := bbase (se 6 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 4445077 = 208363) (by norm_num)
theorem B808013 : Blo 346754 808013 := bbase (se 3 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 808013 = 303005) (by norm_num)
theorem B808213 : Blo 346754 808213 := bbase (se 6 (by rfl) ⟨18942, by rfl⟩ : syracuseStep 808213 = 37885) (by norm_num)
theorem B742709 : Blo 346754 742709 := bbase (se 5 (by rfl) ⟨34814, by rfl⟩ : syracuseStep 742709 = 69629) (by norm_num)
theorem B841141 : Blo 346754 841141 := bbase (se 5 (by rfl) ⟨39428, by rfl⟩ : syracuseStep 841141 = 78857) (by norm_num)
theorem B841373 : Blo 346754 841373 := bbase (se 3 (by rfl) ⟨157757, by rfl⟩ : syracuseStep 841373 = 315515) (by norm_num)
theorem B841517 : Blo 346754 841517 := bbase (se 3 (by rfl) ⟨157784, by rfl⟩ : syracuseStep 841517 = 315569) (by norm_num)
theorem B841565 : Blo 346754 841565 := bbase (se 3 (by rfl) ⟨157793, by rfl⟩ : syracuseStep 841565 = 315587) (by norm_num)
theorem B1759157 : Blo 346754 1759157 := bbase (se 5 (by rfl) ⟨82460, by rfl⟩ : syracuseStep 1759157 = 164921) (by norm_num)
theorem B2414645 : Blo 346754 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B940133 : Blo 346754 940133 := bbase (se 4 (by rfl) ⟨88137, by rfl⟩ : syracuseStep 940133 = 176275) (by norm_num)
theorem B841853 : Blo 346754 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B1136773 : Blo 346754 1136773 := bbase (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) (by norm_num)
theorem B743573 : Blo 346754 743573 := bbase (se 6 (by rfl) ⟨17427, by rfl⟩ : syracuseStep 743573 = 34855) (by norm_num)
theorem B2513045 : Blo 346754 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B743717 : Blo 346754 743717 := bbase (se 4 (by rfl) ⟨69723, by rfl⟩ : syracuseStep 743717 = 139447) (by norm_num)
theorem B1431893 : Blo 346754 1431893 := bbase (se 10 (by rfl) ⟨2097, by rfl⟩ : syracuseStep 1431893 = 4195) (by norm_num)
theorem B1497685 : Blo 346754 1497685 := bbase (se 8 (by rfl) ⟨8775, by rfl⟩ : syracuseStep 1497685 = 17551) (by norm_num)
theorem B416621 : Blo 346754 416621 := bbase (se 3 (by rfl) ⟨78116, by rfl⟩ : syracuseStep 416621 = 156233) (by norm_num)
theorem B449425 : Blo 346754 449425 := bbase (se 2 (by rfl) ⟨168534, by rfl⟩ : syracuseStep 449425 = 337069) (by norm_num)
theorem B416669 : Blo 346754 416669 := bbase (se 3 (by rfl) ⟨78125, by rfl⟩ : syracuseStep 416669 = 156251) (by norm_num)
theorem B1170341 : Blo 346754 1170341 := bbase (se 4 (by rfl) ⟨109719, by rfl⟩ : syracuseStep 1170341 = 219439) (by norm_num)
theorem B416765 : Blo 346754 416765 := bbase (se 3 (by rfl) ⟨78143, by rfl⟩ : syracuseStep 416765 = 156287) (by norm_num)
theorem B744461 : Blo 346754 744461 := bbase (se 3 (by rfl) ⟨139586, by rfl⟩ : syracuseStep 744461 = 279173) (by norm_num)
theorem B973973 : Blo 346754 973973 := bbase (se 6 (by rfl) ⟨22827, by rfl⟩ : syracuseStep 973973 = 45655) (by norm_num)
theorem B416929 : Blo 346754 416929 := bbase (se 2 (by rfl) ⟨156348, by rfl⟩ : syracuseStep 416929 = 312697) (by norm_num)
theorem B449701 : Blo 346754 449701 := bbase (se 4 (by rfl) ⟨42159, by rfl⟩ : syracuseStep 449701 = 84319) (by norm_num)
theorem B1760453 : Blo 346754 1760453 := bbase (se 4 (by rfl) ⟨165042, by rfl⟩ : syracuseStep 1760453 = 330085) (by norm_num)
theorem B1170773 : Blo 346754 1170773 := bbase (se 11 (by rfl) ⟨857, by rfl⟩ : syracuseStep 1170773 = 1715) (by norm_num)
theorem B351589 : Blo 346754 351589 := bbase (se 4 (by rfl) ⟨32961, by rfl⟩ : syracuseStep 351589 = 65923) (by norm_num)
theorem B417145 : Blo 346754 417145 := bbase (se 2 (by rfl) ⟨156429, by rfl⟩ : syracuseStep 417145 = 312859) (by norm_num)
theorem B417313 : Blo 346754 417313 := bbase (se 2 (by rfl) ⟨156492, by rfl⟩ : syracuseStep 417313 = 312985) (by norm_num)
theorem B2022965 : Blo 346754 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B941701 : Blo 346754 941701 := bbase (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) (by norm_num)
theorem B351905 : Blo 346754 351905 := bbase (se 2 (by rfl) ⟨131964, by rfl⟩ : syracuseStep 351905 = 263929) (by norm_num)
theorem B2088629 : Blo 346754 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B745213 : Blo 346754 745213 := bbase (se 3 (by rfl) ⟨139727, by rfl⟩ : syracuseStep 745213 = 279455) (by norm_num)
theorem B1171205 : Blo 346754 1171205 := bbase (se 4 (by rfl) ⟨109800, by rfl⟩ : syracuseStep 1171205 = 219601) (by norm_num)
theorem B745357 : Blo 346754 745357 := bbase (se 3 (by rfl) ⟨139754, by rfl⟩ : syracuseStep 745357 = 279509) (by norm_num)
theorem B417841 : Blo 346754 417841 := bbase (se 2 (by rfl) ⟨156690, by rfl⟩ : syracuseStep 417841 = 313381) (by norm_num)
theorem B1597589 : Blo 346754 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B1171637 : Blo 346754 1171637 := bbase (se 5 (by rfl) ⟨54920, by rfl⟩ : syracuseStep 1171637 = 109841) (by norm_num)
theorem B745733 : Blo 346754 745733 := bbase (se 4 (by rfl) ⟨69912, by rfl⟩ : syracuseStep 745733 = 139825) (by norm_num)
theorem B1761749 : Blo 346754 1761749 := bbase (se 7 (by rfl) ⟨20645, by rfl⟩ : syracuseStep 1761749 = 41291) (by norm_num)
theorem B352765 : Blo 346754 352765 := bbase (se 3 (by rfl) ⟨66143, by rfl⟩ : syracuseStep 352765 = 132287) (by norm_num)
theorem B1172069 : Blo 346754 1172069 := bbase (se 4 (by rfl) ⟨109881, by rfl⟩ : syracuseStep 1172069 = 219763) (by norm_num)
theorem B746101 : Blo 346754 746101 := bbase (se 5 (by rfl) ⟨34973, by rfl⟩ : syracuseStep 746101 = 69947) (by norm_num)
theorem B353081 : Blo 346754 353081 := bbase (se 2 (by rfl) ⟨132405, by rfl⟩ : syracuseStep 353081 = 264811) (by norm_num)
theorem B942997 : Blo 346754 942997 := bbase (se 6 (by rfl) ⟨22101, by rfl⟩ : syracuseStep 942997 = 44203) (by norm_num)
theorem B1172501 : Blo 346754 1172501 := bbase (se 6 (by rfl) ⟨27480, by rfl⟩ : syracuseStep 1172501 = 54961) (by norm_num)
theorem B418937 : Blo 346754 418937 := bbase (se 2 (by rfl) ⟨157101, by rfl⟩ : syracuseStep 418937 = 314203) (by norm_num)
theorem B1533077 : Blo 346754 1533077 := bbase (se 6 (by rfl) ⟨35931, by rfl⟩ : syracuseStep 1533077 = 71863) (by norm_num)
theorem B451813 : Blo 346754 451813 := bbase (se 4 (by rfl) ⟨42357, by rfl⟩ : syracuseStep 451813 = 84715) (by norm_num)
theorem B877837 : Blo 346754 877837 := bbase (se 3 (by rfl) ⟨164594, by rfl⟩ : syracuseStep 877837 = 329189) (by norm_num)
theorem B845101 : Blo 346754 845101 := bbase (se 3 (by rfl) ⟨158456, by rfl⟩ : syracuseStep 845101 = 316913) (by norm_num)
theorem B353641 : Blo 346754 353641 := bbase (se 2 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 353641 = 265231) (by norm_num)
theorem B877949 : Blo 346754 877949 := bbase (se 3 (by rfl) ⟨164615, by rfl⟩ : syracuseStep 877949 = 329231) (by norm_num)
theorem B1172933 : Blo 346754 1172933 := bbase (se 4 (by rfl) ⟨109962, by rfl⟩ : syracuseStep 1172933 = 219925) (by norm_num)
theorem B878141 : Blo 346754 878141 := bbase (se 3 (by rfl) ⟨164651, by rfl⟩ : syracuseStep 878141 = 329303) (by norm_num)
theorem B2975413 : Blo 346754 2975413 := bbase (se 5 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 2975413 = 278945) (by norm_num)
theorem B353977 : Blo 346754 353977 := bbase (se 2 (by rfl) ⟨132741, by rfl⟩ : syracuseStep 353977 = 265483) (by norm_num)
theorem B353981 : Blo 346754 353981 := bbase (se 3 (by rfl) ⟨66371, by rfl⟩ : syracuseStep 353981 = 132743) (by norm_num)
theorem B648901 : Blo 346754 648901 := bbase (se 4 (by rfl) ⟨60834, by rfl⟩ : syracuseStep 648901 = 121669) (by norm_num)
theorem B1763045 : Blo 346754 1763045 := bbase (se 4 (by rfl) ⟨165285, by rfl⟩ : syracuseStep 1763045 = 330571) (by norm_num)
theorem B419629 : Blo 346754 419629 := bbase (se 3 (by rfl) ⟨78680, by rfl⟩ : syracuseStep 419629 = 157361) (by norm_num)
theorem B1173365 : Blo 346754 1173365 := bbase (se 5 (by rfl) ⟨55001, by rfl⟩ : syracuseStep 1173365 = 110003) (by norm_num)
theorem B1009541 : Blo 346754 1009541 := bbase (se 4 (by rfl) ⟨94644, by rfl⟩ : syracuseStep 1009541 = 189289) (by norm_num)
theorem B419725 : Blo 346754 419725 := bbase (se 3 (by rfl) ⟨78698, by rfl⟩ : syracuseStep 419725 = 157397) (by norm_num)
theorem B878485 : Blo 346754 878485 := bbase (se 6 (by rfl) ⟨20589, by rfl⟩ : syracuseStep 878485 = 41179) (by norm_num)
theorem B780245 : Blo 346754 780245 := bbase (se 7 (by rfl) ⟨9143, by rfl⟩ : syracuseStep 780245 = 18287) (by norm_num)
theorem B878597 : Blo 346754 878597 := bbase (se 4 (by rfl) ⟨82368, by rfl⟩ : syracuseStep 878597 = 164737) (by norm_num)
theorem B780317 : Blo 346754 780317 := bbase (se 3 (by rfl) ⟨146309, by rfl⟩ : syracuseStep 780317 = 292619) (by norm_num)
theorem B747605 : Blo 346754 747605 := bbase (se 8 (by rfl) ⟨4380, by rfl⟩ : syracuseStep 747605 = 8761) (by norm_num)
theorem B780389 : Blo 346754 780389 := bbase (se 4 (by rfl) ⟨73161, by rfl⟩ : syracuseStep 780389 = 146323) (by norm_num)
theorem B911477 : Blo 346754 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B2648213 : Blo 346754 2648213 := bbase (se 6 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 2648213 = 124135) (by norm_num)
theorem B780461 : Blo 346754 780461 := bbase (se 3 (by rfl) ⟨146336, by rfl⟩ : syracuseStep 780461 = 292673) (by norm_num)
theorem B878789 : Blo 346754 878789 := bbase (se 4 (by rfl) ⟨82386, by rfl⟩ : syracuseStep 878789 = 164773) (by norm_num)
theorem B747749 : Blo 346754 747749 := bbase (se 4 (by rfl) ⟨70101, by rfl⟩ : syracuseStep 747749 = 140203) (by norm_num)
theorem B780533 : Blo 346754 780533 := bbase (se 5 (by rfl) ⟨36587, by rfl⟩ : syracuseStep 780533 = 73175) (by norm_num)
theorem B420109 : Blo 346754 420109 := bbase (se 3 (by rfl) ⟨78770, by rfl⟩ : syracuseStep 420109 = 157541) (by norm_num)
theorem B1173797 : Blo 346754 1173797 := bbase (se 4 (by rfl) ⟨110043, by rfl⟩ : syracuseStep 1173797 = 220087) (by norm_num)
theorem B780605 : Blo 346754 780605 := bbase (se 3 (by rfl) ⟨146363, by rfl⟩ : syracuseStep 780605 = 292727) (by norm_num)
theorem B1272181 : Blo 346754 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B780677 : Blo 346754 780677 := bbase (se 4 (by rfl) ⟨73188, by rfl⟩ : syracuseStep 780677 = 146377) (by norm_num)
theorem B780749 : Blo 346754 780749 := bbase (se 3 (by rfl) ⟨146390, by rfl⟩ : syracuseStep 780749 = 292781) (by norm_num)
theorem B780821 : Blo 346754 780821 := bbase (se 6 (by rfl) ⟨18300, by rfl⟩ : syracuseStep 780821 = 36601) (by norm_num)
theorem B879133 : Blo 346754 879133 := bbase (se 3 (by rfl) ⟨164837, by rfl⟩ : syracuseStep 879133 = 329675) (by norm_num)
theorem B748109 : Blo 346754 748109 := bbase (se 3 (by rfl) ⟨140270, by rfl⟩ : syracuseStep 748109 = 280541) (by norm_num)
theorem B780893 : Blo 346754 780893 := bbase (se 3 (by rfl) ⟨146417, by rfl⟩ : syracuseStep 780893 = 292835) (by norm_num)
theorem B879245 : Blo 346754 879245 := bbase (se 3 (by rfl) ⟨164858, by rfl⟩ : syracuseStep 879245 = 329717) (by norm_num)
theorem B780965 : Blo 346754 780965 := bbase (se 4 (by rfl) ⟨73215, by rfl⟩ : syracuseStep 780965 = 146431) (by norm_num)
theorem B1174229 : Blo 346754 1174229 := bbase (se 7 (by rfl) ⟨13760, by rfl⟩ : syracuseStep 1174229 = 27521) (by norm_num)
theorem B781037 : Blo 346754 781037 := bbase (se 3 (by rfl) ⟨146444, by rfl⟩ : syracuseStep 781037 = 292889) (by norm_num)
theorem B781109 : Blo 346754 781109 := bbase (se 5 (by rfl) ⟨36614, by rfl⟩ : syracuseStep 781109 = 73229) (by norm_num)
theorem B879437 : Blo 346754 879437 := bbase (se 3 (by rfl) ⟨164894, by rfl⟩ : syracuseStep 879437 = 329789) (by norm_num)
theorem B781181 : Blo 346754 781181 := bbase (se 3 (by rfl) ⟨146471, by rfl⟩ : syracuseStep 781181 = 292943) (by norm_num)
theorem B781253 : Blo 346754 781253 := bbase (se 4 (by rfl) ⟨73242, by rfl⟩ : syracuseStep 781253 = 146485) (by norm_num)
theorem B1764341 : Blo 346754 1764341 := bbase (se 5 (by rfl) ⟨82703, by rfl⟩ : syracuseStep 1764341 = 165407) (by norm_num)
theorem B781325 : Blo 346754 781325 := bbase (se 3 (by rfl) ⟨146498, by rfl⟩ : syracuseStep 781325 = 292997) (by norm_num)
theorem B781397 : Blo 346754 781397 := bbase (se 8 (by rfl) ⟨4578, by rfl⟩ : syracuseStep 781397 = 9157) (by norm_num)
theorem B1174661 : Blo 346754 1174661 := bbase (se 4 (by rfl) ⟨110124, by rfl⟩ : syracuseStep 1174661 = 220249) (by norm_num)
theorem B781469 : Blo 346754 781469 := bbase (se 3 (by rfl) ⟨146525, by rfl⟩ : syracuseStep 781469 = 293051) (by norm_num)
theorem B879781 : Blo 346754 879781 := bbase (se 4 (by rfl) ⟨82479, by rfl⟩ : syracuseStep 879781 = 164959) (by norm_num)
theorem B355505 : Blo 346754 355505 := bbase (se 2 (by rfl) ⟨133314, by rfl⟩ : syracuseStep 355505 = 266629) (by norm_num)
theorem B781541 : Blo 346754 781541 := bbase (se 4 (by rfl) ⟨73269, by rfl⟩ : syracuseStep 781541 = 146539) (by norm_num)
theorem B879893 : Blo 346754 879893 := bbase (se 6 (by rfl) ⟨20622, by rfl⟩ : syracuseStep 879893 = 41245) (by norm_num)
theorem B421157 : Blo 346754 421157 := bbase (se 4 (by rfl) ⟨39483, by rfl⟩ : syracuseStep 421157 = 78967) (by norm_num)
theorem B781613 : Blo 346754 781613 := bbase (se 3 (by rfl) ⟨146552, by rfl⟩ : syracuseStep 781613 = 293105) (by norm_num)
theorem B781685 : Blo 346754 781685 := bbase (se 5 (by rfl) ⟨36641, by rfl⟩ : syracuseStep 781685 = 73283) (by norm_num)
theorem B781757 : Blo 346754 781757 := bbase (se 3 (by rfl) ⟨146579, by rfl⟩ : syracuseStep 781757 = 293159) (by norm_num)
theorem B585157 : Blo 346754 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B748997 : Blo 346754 748997 := bbase (se 4 (by rfl) ⟨70218, by rfl⟩ : syracuseStep 748997 = 140437) (by norm_num)
theorem B880085 : Blo 346754 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B781829 : Blo 346754 781829 := bbase (se 4 (by rfl) ⟨73296, by rfl⟩ : syracuseStep 781829 = 146593) (by norm_num)
theorem B585245 : Blo 346754 585245 := bbase (se 3 (by rfl) ⟨109733, by rfl⟩ : syracuseStep 585245 = 219467) (by norm_num)
theorem B1666597 : Blo 346754 1666597 := bbase (se 4 (by rfl) ⟨156243, by rfl⟩ : syracuseStep 1666597 = 312487) (by norm_num)
theorem B1175093 : Blo 346754 1175093 := bbase (se 5 (by rfl) ⟨55082, by rfl⟩ : syracuseStep 1175093 = 110165) (by norm_num)
theorem B781901 : Blo 346754 781901 := bbase (se 3 (by rfl) ⟨146606, by rfl⟩ : syracuseStep 781901 = 293213) (by norm_num)
theorem B2977397 : Blo 346754 2977397 := bbase (se 5 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 2977397 = 279131) (by norm_num)
theorem B781973 : Blo 346754 781973 := bbase (se 6 (by rfl) ⟨18327, by rfl⟩ : syracuseStep 781973 = 36655) (by norm_num)
theorem B585373 : Blo 346754 585373 := bbase (se 3 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 585373 = 219515) (by norm_num)
theorem B1994453 : Blo 346754 1994453 := bbase (se 7 (by rfl) ⟨23372, by rfl⟩ : syracuseStep 1994453 = 46745) (by norm_num)
theorem B782045 : Blo 346754 782045 := bbase (se 3 (by rfl) ⟨146633, by rfl⟩ : syracuseStep 782045 = 293267) (by norm_num)
theorem B585461 : Blo 346754 585461 := bbase (se 5 (by rfl) ⟨27443, by rfl⟩ : syracuseStep 585461 = 54887) (by norm_num)
theorem B782117 : Blo 346754 782117 := bbase (se 4 (by rfl) ⟨73323, by rfl⟩ : syracuseStep 782117 = 146647) (by norm_num)
theorem B880429 : Blo 346754 880429 := bbase (se 3 (by rfl) ⟨165080, by rfl⟩ : syracuseStep 880429 = 330161) (by norm_num)
theorem B782189 : Blo 346754 782189 := bbase (se 3 (by rfl) ⟨146660, by rfl⟩ : syracuseStep 782189 = 293321) (by norm_num)
theorem B585589 : Blo 346754 585589 := bbase (se 5 (by rfl) ⟨27449, by rfl⟩ : syracuseStep 585589 = 54899) (by norm_num)
theorem B880541 : Blo 346754 880541 := bbase (se 3 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 880541 = 330203) (by norm_num)
theorem B782261 : Blo 346754 782261 := bbase (se 5 (by rfl) ⟨36668, by rfl⟩ : syracuseStep 782261 = 73337) (by norm_num)
theorem B520133 : Blo 346754 520133 := bbase (se 4 (by rfl) ⟨48762, by rfl⟩ : syracuseStep 520133 = 97525) (by norm_num)
theorem B585677 : Blo 346754 585677 := bbase (se 3 (by rfl) ⟨109814, by rfl⟩ : syracuseStep 585677 = 219629) (by norm_num)
theorem B1142741 : Blo 346754 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B520157 : Blo 346754 520157 := bbase (se 3 (by rfl) ⟨97529, by rfl⟩ : syracuseStep 520157 = 195059) (by norm_num)
theorem B1175525 : Blo 346754 1175525 := bbase (se 4 (by rfl) ⟨110205, by rfl⟩ : syracuseStep 1175525 = 220411) (by norm_num)
theorem B520181 : Blo 346754 520181 := bbase (se 5 (by rfl) ⟨24383, by rfl⟩ : syracuseStep 520181 = 48767) (by norm_num)
theorem B782333 : Blo 346754 782333 := bbase (se 3 (by rfl) ⟨146687, by rfl⟩ : syracuseStep 782333 = 293375) (by norm_num)
theorem B520205 : Blo 346754 520205 := bbase (se 3 (by rfl) ⟨97538, by rfl⟩ : syracuseStep 520205 = 195077) (by norm_num)
theorem B520229 : Blo 346754 520229 := bbase (se 4 (by rfl) ⟨48771, by rfl⟩ : syracuseStep 520229 = 97543) (by norm_num)
theorem B520253 : Blo 346754 520253 := bbase (se 3 (by rfl) ⟨97547, by rfl⟩ : syracuseStep 520253 = 195095) (by norm_num)
theorem B782405 : Blo 346754 782405 := bbase (se 4 (by rfl) ⟨73350, by rfl⟩ : syracuseStep 782405 = 146701) (by norm_num)
theorem B585805 : Blo 346754 585805 := bbase (se 3 (by rfl) ⟨109838, by rfl⟩ : syracuseStep 585805 = 219677) (by norm_num)
theorem B520277 : Blo 346754 520277 := bbase (se 8 (by rfl) ⟨3048, by rfl⟩ : syracuseStep 520277 = 6097) (by norm_num)
theorem B880733 : Blo 346754 880733 := bbase (se 3 (by rfl) ⟨165137, by rfl⟩ : syracuseStep 880733 = 330275) (by norm_num)
theorem B520301 : Blo 346754 520301 := bbase (se 3 (by rfl) ⟨97556, by rfl⟩ : syracuseStep 520301 = 195113) (by norm_num)
theorem B520325 : Blo 346754 520325 := bbase (se 4 (by rfl) ⟨48780, by rfl⟩ : syracuseStep 520325 = 97561) (by norm_num)
theorem B782477 : Blo 346754 782477 := bbase (se 3 (by rfl) ⟨146714, by rfl⟩ : syracuseStep 782477 = 293429) (by norm_num)
theorem B520349 : Blo 346754 520349 := bbase (se 3 (by rfl) ⟨97565, by rfl⟩ : syracuseStep 520349 = 195131) (by norm_num)
theorem B585893 : Blo 346754 585893 := bbase (se 4 (by rfl) ⟨54927, by rfl⟩ : syracuseStep 585893 = 109855) (by norm_num)
theorem B520373 : Blo 346754 520373 := bbase (se 5 (by rfl) ⟨24392, by rfl⟩ : syracuseStep 520373 = 48785) (by norm_num)
theorem B520397 : Blo 346754 520397 := bbase (se 3 (by rfl) ⟨97574, by rfl⟩ : syracuseStep 520397 = 195149) (by norm_num)
theorem B782549 : Blo 346754 782549 := bbase (se 7 (by rfl) ⟨9170, by rfl⟩ : syracuseStep 782549 = 18341) (by norm_num)
theorem B520421 : Blo 346754 520421 := bbase (se 4 (by rfl) ⟨48789, by rfl⟩ : syracuseStep 520421 = 97579) (by norm_num)
theorem B520445 : Blo 346754 520445 := bbase (se 3 (by rfl) ⟨97583, by rfl⟩ : syracuseStep 520445 = 195167) (by norm_num)
theorem B1765637 : Blo 346754 1765637 := bbase (se 4 (by rfl) ⟨165528, by rfl⟩ : syracuseStep 1765637 = 331057) (by norm_num)
theorem B520469 : Blo 346754 520469 := bbase (se 6 (by rfl) ⟨12198, by rfl⟩ : syracuseStep 520469 = 24397) (by norm_num)
theorem B782621 : Blo 346754 782621 := bbase (se 3 (by rfl) ⟨146741, by rfl⟩ : syracuseStep 782621 = 293483) (by norm_num)
theorem B586021 : Blo 346754 586021 := bbase (se 4 (by rfl) ⟨54939, by rfl⟩ : syracuseStep 586021 = 109879) (by norm_num)
theorem B520493 : Blo 346754 520493 := bbase (se 3 (by rfl) ⟨97592, by rfl⟩ : syracuseStep 520493 = 195185) (by norm_num)
theorem B520517 : Blo 346754 520517 := bbase (se 4 (by rfl) ⟨48798, by rfl⟩ : syracuseStep 520517 = 97597) (by norm_num)
theorem B520541 : Blo 346754 520541 := bbase (se 3 (by rfl) ⟨97601, by rfl⟩ : syracuseStep 520541 = 195203) (by norm_num)
theorem B782693 : Blo 346754 782693 := bbase (se 4 (by rfl) ⟨73377, by rfl⟩ : syracuseStep 782693 = 146755) (by norm_num)
theorem B520565 : Blo 346754 520565 := bbase (se 5 (by rfl) ⟨24401, by rfl⟩ : syracuseStep 520565 = 48803) (by norm_num)
theorem B553333 : Blo 346754 553333 := bbase (se 5 (by rfl) ⟨25937, by rfl⟩ : syracuseStep 553333 = 51875) (by norm_num)
theorem B586109 : Blo 346754 586109 := bbase (se 3 (by rfl) ⟨109895, by rfl⟩ : syracuseStep 586109 = 219791) (by norm_num)
theorem B520589 : Blo 346754 520589 := bbase (se 3 (by rfl) ⟨97610, by rfl⟩ : syracuseStep 520589 = 195221) (by norm_num)
theorem B1175957 : Blo 346754 1175957 := bbase (se 6 (by rfl) ⟨27561, by rfl⟩ : syracuseStep 1175957 = 55123) (by norm_num)
theorem B520613 : Blo 346754 520613 := bbase (se 4 (by rfl) ⟨48807, by rfl⟩ : syracuseStep 520613 = 97615) (by norm_num)
theorem B782765 : Blo 346754 782765 := bbase (se 3 (by rfl) ⟨146768, by rfl⟩ : syracuseStep 782765 = 293537) (by norm_num)
theorem B881077 : Blo 346754 881077 := bbase (se 5 (by rfl) ⟨41300, by rfl⟩ : syracuseStep 881077 = 82601) (by norm_num)
theorem B520637 : Blo 346754 520637 := bbase (se 3 (by rfl) ⟨97619, by rfl⟩ : syracuseStep 520637 = 195239) (by norm_num)
theorem B520661 : Blo 346754 520661 := bbase (se 7 (by rfl) ⟨6101, by rfl⟩ : syracuseStep 520661 = 12203) (by norm_num)
theorem B520685 : Blo 346754 520685 := bbase (se 3 (by rfl) ⟨97628, by rfl⟩ : syracuseStep 520685 = 195257) (by norm_num)
theorem B782837 : Blo 346754 782837 := bbase (se 5 (by rfl) ⟨36695, by rfl⟩ : syracuseStep 782837 = 73391) (by norm_num)
theorem B586237 : Blo 346754 586237 := bbase (se 3 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 586237 = 219839) (by norm_num)
theorem B520709 : Blo 346754 520709 := bbase (se 4 (by rfl) ⟨48816, by rfl⟩ : syracuseStep 520709 = 97633) (by norm_num)
theorem B520733 : Blo 346754 520733 := bbase (se 3 (by rfl) ⟨97637, by rfl⟩ : syracuseStep 520733 = 195275) (by norm_num)
theorem B881189 : Blo 346754 881189 := bbase (se 4 (by rfl) ⟨82611, by rfl⟩ : syracuseStep 881189 = 165223) (by norm_num)
theorem B520757 : Blo 346754 520757 := bbase (se 5 (by rfl) ⟨24410, by rfl⟩ : syracuseStep 520757 = 48821) (by norm_num)
theorem B782909 : Blo 346754 782909 := bbase (se 3 (by rfl) ⟨146795, by rfl⟩ : syracuseStep 782909 = 293591) (by norm_num)
theorem B520781 : Blo 346754 520781 := bbase (se 3 (by rfl) ⟨97646, by rfl⟩ : syracuseStep 520781 = 195293) (by norm_num)
theorem B586325 : Blo 346754 586325 := bbase (se 8 (by rfl) ⟨3435, by rfl⟩ : syracuseStep 586325 = 6871) (by norm_num)
theorem B520805 : Blo 346754 520805 := bbase (se 4 (by rfl) ⟨48825, by rfl⟩ : syracuseStep 520805 = 97651) (by norm_num)
theorem B520829 : Blo 346754 520829 := bbase (se 3 (by rfl) ⟨97655, by rfl⟩ : syracuseStep 520829 = 195311) (by norm_num)
theorem B782981 : Blo 346754 782981 := bbase (se 4 (by rfl) ⟨73404, by rfl⟩ : syracuseStep 782981 = 146809) (by norm_num)
theorem B520853 : Blo 346754 520853 := bbase (se 6 (by rfl) ⟨12207, by rfl⟩ : syracuseStep 520853 = 24415) (by norm_num)
theorem B520877 : Blo 346754 520877 := bbase (se 3 (by rfl) ⟨97664, by rfl⟩ : syracuseStep 520877 = 195329) (by norm_num)
theorem B520901 : Blo 346754 520901 := bbase (se 4 (by rfl) ⟨48834, by rfl⟩ : syracuseStep 520901 = 97669) (by norm_num)
theorem B783053 : Blo 346754 783053 := bbase (se 3 (by rfl) ⟨146822, by rfl⟩ : syracuseStep 783053 = 293645) (by norm_num)
theorem B586453 : Blo 346754 586453 := bbase (se 7 (by rfl) ⟨6872, by rfl⟩ : syracuseStep 586453 = 13745) (by norm_num)
theorem B520925 : Blo 346754 520925 := bbase (se 3 (by rfl) ⟨97673, by rfl⟩ : syracuseStep 520925 = 195347) (by norm_num)
theorem B881381 : Blo 346754 881381 := bbase (se 4 (by rfl) ⟨82629, by rfl⟩ : syracuseStep 881381 = 165259) (by norm_num)
theorem B520949 : Blo 346754 520949 := bbase (se 5 (by rfl) ⟨24419, by rfl⟩ : syracuseStep 520949 = 48839) (by norm_num)
theorem B520973 : Blo 346754 520973 := bbase (se 3 (by rfl) ⟨97682, by rfl⟩ : syracuseStep 520973 = 195365) (by norm_num)
theorem B783125 : Blo 346754 783125 := bbase (se 6 (by rfl) ⟨18354, by rfl⟩ : syracuseStep 783125 = 36709) (by norm_num)
theorem B520997 : Blo 346754 520997 := bbase (se 4 (by rfl) ⟨48843, by rfl⟩ : syracuseStep 520997 = 97687) (by norm_num)
theorem B586541 : Blo 346754 586541 := bbase (se 3 (by rfl) ⟨109976, by rfl⟩ : syracuseStep 586541 = 219953) (by norm_num)
theorem B521021 : Blo 346754 521021 := bbase (se 3 (by rfl) ⟨97691, by rfl⟩ : syracuseStep 521021 = 195383) (by norm_num)
theorem B1176389 : Blo 346754 1176389 := bbase (se 4 (by rfl) ⟨110286, by rfl⟩ : syracuseStep 1176389 = 220573) (by norm_num)
theorem B521045 : Blo 346754 521045 := bbase (se 9 (by rfl) ⟨1526, by rfl⟩ : syracuseStep 521045 = 3053) (by norm_num)
theorem B783197 : Blo 346754 783197 := bbase (se 3 (by rfl) ⟨146849, by rfl⟩ : syracuseStep 783197 = 293699) (by norm_num)
theorem B521069 : Blo 346754 521069 := bbase (se 3 (by rfl) ⟨97700, by rfl⟩ : syracuseStep 521069 = 195401) (by norm_num)
theorem B1995637 : Blo 346754 1995637 := bbase (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) (by norm_num)
theorem B521093 : Blo 346754 521093 := bbase (se 4 (by rfl) ⟨48852, by rfl⟩ : syracuseStep 521093 = 97705) (by norm_num)
theorem B521117 : Blo 346754 521117 := bbase (se 3 (by rfl) ⟨97709, by rfl⟩ : syracuseStep 521117 = 195419) (by norm_num)
theorem B783269 : Blo 346754 783269 := bbase (se 4 (by rfl) ⟨73431, by rfl⟩ : syracuseStep 783269 = 146863) (by norm_num)
theorem B586669 : Blo 346754 586669 := bbase (se 3 (by rfl) ⟨110000, by rfl⟩ : syracuseStep 586669 = 220001) (by norm_num)
theorem B521141 : Blo 346754 521141 := bbase (se 5 (by rfl) ⟨24428, by rfl⟩ : syracuseStep 521141 = 48857) (by norm_num)
theorem B1143733 : Blo 346754 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B521165 : Blo 346754 521165 := bbase (se 3 (by rfl) ⟨97718, by rfl⟩ : syracuseStep 521165 = 195437) (by norm_num)
theorem B390109 : Blo 346754 390109 := bbase (se 3 (by rfl) ⟨73145, by rfl⟩ : syracuseStep 390109 = 146291) (by norm_num)
theorem B521189 : Blo 346754 521189 := bbase (se 4 (by rfl) ⟨48861, by rfl⟩ : syracuseStep 521189 = 97723) (by norm_num)
theorem B783341 : Blo 346754 783341 := bbase (se 3 (by rfl) ⟨146876, by rfl⟩ : syracuseStep 783341 = 293753) (by norm_num)
theorem B521213 : Blo 346754 521213 := bbase (se 3 (by rfl) ⟨97727, by rfl⟩ : syracuseStep 521213 = 195455) (by norm_num)
theorem B390145 : Blo 346754 390145 := bbase (se 2 (by rfl) ⟨146304, by rfl⟩ : syracuseStep 390145 = 292609) (by norm_num)
theorem B586757 : Blo 346754 586757 := bbase (se 4 (by rfl) ⟨55008, by rfl⟩ : syracuseStep 586757 = 110017) (by norm_num)
theorem B521237 : Blo 346754 521237 := bbase (se 6 (by rfl) ⟨12216, by rfl⟩ : syracuseStep 521237 = 24433) (by norm_num)
theorem B390181 : Blo 346754 390181 := bbase (se 4 (by rfl) ⟨36579, by rfl⟩ : syracuseStep 390181 = 73159) (by norm_num)
theorem B521261 : Blo 346754 521261 := bbase (se 3 (by rfl) ⟨97736, by rfl⟩ : syracuseStep 521261 = 195473) (by norm_num)
theorem B783413 : Blo 346754 783413 := bbase (se 5 (by rfl) ⟨36722, by rfl⟩ : syracuseStep 783413 = 73445) (by norm_num)
theorem B881725 : Blo 346754 881725 := bbase (se 3 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 881725 = 330647) (by norm_num)
theorem B521285 : Blo 346754 521285 := bbase (se 4 (by rfl) ⟨48870, by rfl⟩ : syracuseStep 521285 = 97741) (by norm_num)
theorem B390217 : Blo 346754 390217 := bbase (se 2 (by rfl) ⟨146331, by rfl⟩ : syracuseStep 390217 = 292663) (by norm_num)
theorem B521309 : Blo 346754 521309 := bbase (se 3 (by rfl) ⟨97745, by rfl⟩ : syracuseStep 521309 = 195491) (by norm_num)
theorem B390253 : Blo 346754 390253 := bbase (se 3 (by rfl) ⟨73172, by rfl⟩ : syracuseStep 390253 = 146345) (by norm_num)
theorem B521333 : Blo 346754 521333 := bbase (se 5 (by rfl) ⟨24437, by rfl⟩ : syracuseStep 521333 = 48875) (by norm_num)
theorem B783485 : Blo 346754 783485 := bbase (se 3 (by rfl) ⟨146903, by rfl⟩ : syracuseStep 783485 = 293807) (by norm_num)
theorem B586885 : Blo 346754 586885 := bbase (se 4 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 586885 = 110041) (by norm_num)
theorem B521357 : Blo 346754 521357 := bbase (se 3 (by rfl) ⟨97754, by rfl⟩ : syracuseStep 521357 = 195509) (by norm_num)
theorem B390289 : Blo 346754 390289 := bbase (se 2 (by rfl) ⟨146358, by rfl⟩ : syracuseStep 390289 = 292717) (by norm_num)
theorem B521381 : Blo 346754 521381 := bbase (se 4 (by rfl) ⟨48879, by rfl⟩ : syracuseStep 521381 = 97759) (by norm_num)
theorem B881837 : Blo 346754 881837 := bbase (se 3 (by rfl) ⟨165344, by rfl⟩ : syracuseStep 881837 = 330689) (by norm_num)
theorem B390325 : Blo 346754 390325 := bbase (se 5 (by rfl) ⟨18296, by rfl⟩ : syracuseStep 390325 = 36593) (by norm_num)
theorem B521405 : Blo 346754 521405 := bbase (se 3 (by rfl) ⟨97763, by rfl⟩ : syracuseStep 521405 = 195527) (by norm_num)
theorem B783557 : Blo 346754 783557 := bbase (se 4 (by rfl) ⟨73458, by rfl⟩ : syracuseStep 783557 = 146917) (by norm_num)
theorem B521429 : Blo 346754 521429 := bbase (se 7 (by rfl) ⟨6110, by rfl⟩ : syracuseStep 521429 = 12221) (by norm_num)
theorem B390361 : Blo 346754 390361 := bbase (se 2 (by rfl) ⟨146385, by rfl⟩ : syracuseStep 390361 = 292771) (by norm_num)
theorem B586973 : Blo 346754 586973 := bbase (se 3 (by rfl) ⟨110057, by rfl⟩ : syracuseStep 586973 = 220115) (by norm_num)
theorem B521453 : Blo 346754 521453 := bbase (se 3 (by rfl) ⟨97772, by rfl⟩ : syracuseStep 521453 = 195545) (by norm_num)
theorem B849133 : Blo 346754 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B1176821 : Blo 346754 1176821 := bbase (se 5 (by rfl) ⟨55163, by rfl⟩ : syracuseStep 1176821 = 110327) (by norm_num)
theorem B390397 : Blo 346754 390397 := bbase (se 3 (by rfl) ⟨73199, by rfl⟩ : syracuseStep 390397 = 146399) (by norm_num)
theorem B521477 : Blo 346754 521477 := bbase (se 4 (by rfl) ⟨48888, by rfl⟩ : syracuseStep 521477 = 97777) (by norm_num)
theorem B783629 : Blo 346754 783629 := bbase (se 3 (by rfl) ⟨146930, by rfl⟩ : syracuseStep 783629 = 293861) (by norm_num)
theorem B521501 : Blo 346754 521501 := bbase (se 3 (by rfl) ⟨97781, by rfl⟩ : syracuseStep 521501 = 195563) (by norm_num)
theorem B390433 : Blo 346754 390433 := bbase (se 2 (by rfl) ⟨146412, by rfl⟩ : syracuseStep 390433 = 292825) (by norm_num)
theorem B521525 : Blo 346754 521525 := bbase (se 5 (by rfl) ⟨24446, by rfl⟩ : syracuseStep 521525 = 48893) (by norm_num)
theorem B390469 : Blo 346754 390469 := bbase (se 4 (by rfl) ⟨36606, by rfl⟩ : syracuseStep 390469 = 73213) (by norm_num)
theorem B521549 : Blo 346754 521549 := bbase (se 3 (by rfl) ⟨97790, by rfl⟩ : syracuseStep 521549 = 195581) (by norm_num)
theorem B783701 : Blo 346754 783701 := bbase (se 13 (by rfl) ⟨143, by rfl⟩ : syracuseStep 783701 = 287) (by norm_num)
theorem B587101 : Blo 346754 587101 := bbase (se 3 (by rfl) ⟨110081, by rfl⟩ : syracuseStep 587101 = 220163) (by norm_num)
theorem B521573 : Blo 346754 521573 := bbase (se 4 (by rfl) ⟨48897, by rfl⟩ : syracuseStep 521573 = 97795) (by norm_num)
theorem B390505 : Blo 346754 390505 := bbase (se 2 (by rfl) ⟨146439, by rfl⟩ : syracuseStep 390505 = 292879) (by norm_num)
theorem B882029 : Blo 346754 882029 := bbase (se 3 (by rfl) ⟨165380, by rfl⟩ : syracuseStep 882029 = 330761) (by norm_num)
theorem B521597 : Blo 346754 521597 := bbase (se 3 (by rfl) ⟨97799, by rfl⟩ : syracuseStep 521597 = 195599) (by norm_num)
theorem B390541 : Blo 346754 390541 := bbase (se 3 (by rfl) ⟨73226, by rfl⟩ : syracuseStep 390541 = 146453) (by norm_num)
theorem B521621 : Blo 346754 521621 := bbase (se 6 (by rfl) ⟨12225, by rfl⟩ : syracuseStep 521621 = 24451) (by norm_num)
theorem B783773 : Blo 346754 783773 := bbase (se 3 (by rfl) ⟨146957, by rfl⟩ : syracuseStep 783773 = 293915) (by norm_num)
theorem B521645 : Blo 346754 521645 := bbase (se 3 (by rfl) ⟨97808, by rfl⟩ : syracuseStep 521645 = 195617) (by norm_num)
theorem B390577 : Blo 346754 390577 := bbase (se 2 (by rfl) ⟨146466, by rfl⟩ : syracuseStep 390577 = 292933) (by norm_num)
theorem B587189 : Blo 346754 587189 := bbase (se 5 (by rfl) ⟨27524, by rfl⟩ : syracuseStep 587189 = 55049) (by norm_num)
theorem B521669 : Blo 346754 521669 := bbase (se 4 (by rfl) ⟨48906, by rfl⟩ : syracuseStep 521669 = 97813) (by norm_num)
theorem B390613 : Blo 346754 390613 := bbase (se 7 (by rfl) ⟨4577, by rfl⟩ : syracuseStep 390613 = 9155) (by norm_num)
theorem B521693 : Blo 346754 521693 := bbase (se 3 (by rfl) ⟨97817, by rfl⟩ : syracuseStep 521693 = 195635) (by norm_num)
theorem B783845 : Blo 346754 783845 := bbase (se 4 (by rfl) ⟨73485, by rfl⟩ : syracuseStep 783845 = 146971) (by norm_num)
theorem B521717 : Blo 346754 521717 := bbase (se 5 (by rfl) ⟨24455, by rfl⟩ : syracuseStep 521717 = 48911) (by norm_num)
theorem B390649 : Blo 346754 390649 := bbase (se 2 (by rfl) ⟨146493, by rfl⟩ : syracuseStep 390649 = 292987) (by norm_num)
theorem B521741 : Blo 346754 521741 := bbase (se 3 (by rfl) ⟨97826, by rfl⟩ : syracuseStep 521741 = 195653) (by norm_num)
theorem B1766933 : Blo 346754 1766933 := bbase (se 6 (by rfl) ⟨41412, by rfl⟩ : syracuseStep 1766933 = 82825) (by norm_num)
theorem B390685 : Blo 346754 390685 := bbase (se 3 (by rfl) ⟨73253, by rfl⟩ : syracuseStep 390685 = 146507) (by norm_num)
theorem B521765 : Blo 346754 521765 := bbase (se 4 (by rfl) ⟨48915, by rfl⟩ : syracuseStep 521765 = 97831) (by norm_num)
theorem B783917 : Blo 346754 783917 := bbase (se 3 (by rfl) ⟨146984, by rfl⟩ : syracuseStep 783917 = 293969) (by norm_num)
theorem B587317 : Blo 346754 587317 := bbase (se 5 (by rfl) ⟨27530, by rfl⟩ : syracuseStep 587317 = 55061) (by norm_num)
theorem B521789 : Blo 346754 521789 := bbase (se 3 (by rfl) ⟨97835, by rfl⟩ : syracuseStep 521789 = 195671) (by norm_num)
theorem B390721 : Blo 346754 390721 := bbase (se 2 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 390721 = 293041) (by norm_num)
theorem B521813 : Blo 346754 521813 := bbase (se 8 (by rfl) ⟨3057, by rfl⟩ : syracuseStep 521813 = 6115) (by norm_num)
theorem B390757 : Blo 346754 390757 := bbase (se 4 (by rfl) ⟨36633, by rfl⟩ : syracuseStep 390757 = 73267) (by norm_num)
theorem B521837 : Blo 346754 521837 := bbase (se 3 (by rfl) ⟨97844, by rfl⟩ : syracuseStep 521837 = 195689) (by norm_num)
theorem B783989 : Blo 346754 783989 := bbase (se 5 (by rfl) ⟨36749, by rfl⟩ : syracuseStep 783989 = 73499) (by norm_num)
theorem B521861 : Blo 346754 521861 := bbase (se 4 (by rfl) ⟨48924, by rfl⟩ : syracuseStep 521861 = 97849) (by norm_num)
theorem B390793 : Blo 346754 390793 := bbase (se 2 (by rfl) ⟨146547, by rfl⟩ : syracuseStep 390793 = 293095) (by norm_num)
theorem B587405 : Blo 346754 587405 := bbase (se 3 (by rfl) ⟨110138, by rfl⟩ : syracuseStep 587405 = 220277) (by norm_num)
theorem B521885 : Blo 346754 521885 := bbase (se 3 (by rfl) ⟨97853, by rfl⟩ : syracuseStep 521885 = 195707) (by norm_num)
theorem B1177253 : Blo 346754 1177253 := bbase (se 4 (by rfl) ⟨110367, by rfl⟩ : syracuseStep 1177253 = 220735) (by norm_num)
theorem B390829 : Blo 346754 390829 := bbase (se 3 (by rfl) ⟨73280, by rfl⟩ : syracuseStep 390829 = 146561) (by norm_num)
theorem B521909 : Blo 346754 521909 := bbase (se 5 (by rfl) ⟨24464, by rfl⟩ : syracuseStep 521909 = 48929) (by norm_num)
theorem B784061 : Blo 346754 784061 := bbase (se 3 (by rfl) ⟨147011, by rfl⟩ : syracuseStep 784061 = 294023) (by norm_num)
theorem B882373 : Blo 346754 882373 := bbase (se 4 (by rfl) ⟨82722, by rfl⟩ : syracuseStep 882373 = 165445) (by norm_num)
theorem B521933 : Blo 346754 521933 := bbase (se 3 (by rfl) ⟨97862, by rfl⟩ : syracuseStep 521933 = 195725) (by norm_num)
theorem B390865 : Blo 346754 390865 := bbase (se 2 (by rfl) ⟨146574, by rfl⟩ : syracuseStep 390865 = 293149) (by norm_num)
theorem B521957 : Blo 346754 521957 := bbase (se 4 (by rfl) ⟨48933, by rfl⟩ : syracuseStep 521957 = 97867) (by norm_num)
theorem B390901 : Blo 346754 390901 := bbase (se 5 (by rfl) ⟨18323, by rfl⟩ : syracuseStep 390901 = 36647) (by norm_num)
theorem B521981 : Blo 346754 521981 := bbase (se 3 (by rfl) ⟨97871, by rfl⟩ : syracuseStep 521981 = 195743) (by norm_num)
theorem B784133 : Blo 346754 784133 := bbase (se 4 (by rfl) ⟨73512, by rfl⟩ : syracuseStep 784133 = 147025) (by norm_num)
theorem B587533 : Blo 346754 587533 := bbase (se 3 (by rfl) ⟨110162, by rfl⟩ : syracuseStep 587533 = 220325) (by norm_num)
theorem B522005 : Blo 346754 522005 := bbase (se 6 (by rfl) ⟨12234, by rfl⟩ : syracuseStep 522005 = 24469) (by norm_num)
theorem B390937 : Blo 346754 390937 := bbase (se 2 (by rfl) ⟨146601, by rfl⟩ : syracuseStep 390937 = 293203) (by norm_num)
theorem B522029 : Blo 346754 522029 := bbase (se 3 (by rfl) ⟨97880, by rfl⟩ : syracuseStep 522029 = 195761) (by norm_num)
theorem B882485 : Blo 346754 882485 := bbase (se 5 (by rfl) ⟨41366, by rfl⟩ : syracuseStep 882485 = 82733) (by norm_num)
theorem B390973 : Blo 346754 390973 := bbase (se 3 (by rfl) ⟨73307, by rfl⟩ : syracuseStep 390973 = 146615) (by norm_num)
theorem B522053 : Blo 346754 522053 := bbase (se 4 (by rfl) ⟨48942, by rfl⟩ : syracuseStep 522053 = 97885) (by norm_num)
theorem B784205 : Blo 346754 784205 := bbase (se 3 (by rfl) ⟨147038, by rfl⟩ : syracuseStep 784205 = 294077) (by norm_num)
theorem B522077 : Blo 346754 522077 := bbase (se 3 (by rfl) ⟨97889, by rfl⟩ : syracuseStep 522077 = 195779) (by norm_num)
theorem B391009 : Blo 346754 391009 := bbase (se 2 (by rfl) ⟨146628, by rfl⟩ : syracuseStep 391009 = 293257) (by norm_num)
theorem B587621 : Blo 346754 587621 := bbase (se 4 (by rfl) ⟨55089, by rfl⟩ : syracuseStep 587621 = 110179) (by norm_num)
theorem B849773 : Blo 346754 849773 := bbase (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) (by norm_num)
theorem B522101 : Blo 346754 522101 := bbase (se 5 (by rfl) ⟨24473, by rfl⟩ : syracuseStep 522101 = 48947) (by norm_num)
theorem B391045 : Blo 346754 391045 := bbase (se 4 (by rfl) ⟨36660, by rfl⟩ : syracuseStep 391045 = 73321) (by norm_num)
theorem B522125 : Blo 346754 522125 := bbase (se 3 (by rfl) ⟨97898, by rfl⟩ : syracuseStep 522125 = 195797) (by norm_num)
theorem B784277 : Blo 346754 784277 := bbase (se 6 (by rfl) ⟨18381, by rfl⟩ : syracuseStep 784277 = 36763) (by norm_num)
theorem B522149 : Blo 346754 522149 := bbase (se 4 (by rfl) ⟨48951, by rfl⟩ : syracuseStep 522149 = 97903) (by norm_num)
theorem B391081 : Blo 346754 391081 := bbase (se 2 (by rfl) ⟨146655, by rfl⟩ : syracuseStep 391081 = 293311) (by norm_num)
theorem B522173 : Blo 346754 522173 := bbase (se 3 (by rfl) ⟨97907, by rfl⟩ : syracuseStep 522173 = 195815) (by norm_num)
theorem B391117 : Blo 346754 391117 := bbase (se 3 (by rfl) ⟨73334, by rfl⟩ : syracuseStep 391117 = 146669) (by norm_num)
theorem B522197 : Blo 346754 522197 := bbase (se 7 (by rfl) ⟨6119, by rfl⟩ : syracuseStep 522197 = 12239) (by norm_num)
theorem B784349 : Blo 346754 784349 := bbase (se 3 (by rfl) ⟨147065, by rfl⟩ : syracuseStep 784349 = 294131) (by norm_num)
theorem B587749 : Blo 346754 587749 := bbase (se 4 (by rfl) ⟨55101, by rfl⟩ : syracuseStep 587749 = 110203) (by norm_num)
theorem B522221 : Blo 346754 522221 := bbase (se 3 (by rfl) ⟨97916, by rfl⟩ : syracuseStep 522221 = 195833) (by norm_num)
theorem B391153 : Blo 346754 391153 := bbase (se 2 (by rfl) ⟨146682, by rfl⟩ : syracuseStep 391153 = 293365) (by norm_num)
theorem B882677 : Blo 346754 882677 := bbase (se 5 (by rfl) ⟨41375, by rfl⟩ : syracuseStep 882677 = 82751) (by norm_num)
theorem B522245 : Blo 346754 522245 := bbase (se 4 (by rfl) ⟨48960, by rfl⟩ : syracuseStep 522245 = 97921) (by norm_num)
theorem B391189 : Blo 346754 391189 := bbase (se 6 (by rfl) ⟨9168, by rfl⟩ : syracuseStep 391189 = 18337) (by norm_num)
theorem B522269 : Blo 346754 522269 := bbase (se 3 (by rfl) ⟨97925, by rfl⟩ : syracuseStep 522269 = 195851) (by norm_num)
theorem B784421 : Blo 346754 784421 := bbase (se 4 (by rfl) ⟨73539, by rfl⟩ : syracuseStep 784421 = 147079) (by norm_num)
theorem B522293 : Blo 346754 522293 := bbase (se 5 (by rfl) ⟨24482, by rfl⟩ : syracuseStep 522293 = 48965) (by norm_num)
theorem B391225 : Blo 346754 391225 := bbase (se 2 (by rfl) ⟨146709, by rfl⟩ : syracuseStep 391225 = 293419) (by norm_num)
theorem B587837 : Blo 346754 587837 := bbase (se 3 (by rfl) ⟨110219, by rfl⟩ : syracuseStep 587837 = 220439) (by norm_num)
theorem B522317 : Blo 346754 522317 := bbase (se 3 (by rfl) ⟨97934, by rfl⟩ : syracuseStep 522317 = 195869) (by norm_num)
theorem B1177685 : Blo 346754 1177685 := bbase (se 8 (by rfl) ⟨6900, by rfl⟩ : syracuseStep 1177685 = 13801) (by norm_num)
theorem B391261 : Blo 346754 391261 := bbase (se 3 (by rfl) ⟨73361, by rfl⟩ : syracuseStep 391261 = 146723) (by norm_num)
theorem B522341 : Blo 346754 522341 := bbase (se 4 (by rfl) ⟨48969, by rfl⟩ : syracuseStep 522341 = 97939) (by norm_num)
theorem B784493 : Blo 346754 784493 := bbase (se 3 (by rfl) ⟨147092, by rfl⟩ : syracuseStep 784493 = 294185) (by norm_num)
theorem B522365 : Blo 346754 522365 := bbase (se 3 (by rfl) ⟨97943, by rfl⟩ : syracuseStep 522365 = 195887) (by norm_num)
theorem B391297 : Blo 346754 391297 := bbase (se 2 (by rfl) ⟨146736, by rfl⟩ : syracuseStep 391297 = 293473) (by norm_num)
theorem B522389 : Blo 346754 522389 := bbase (se 6 (by rfl) ⟨12243, by rfl⟩ : syracuseStep 522389 = 24487) (by norm_num)
theorem B391333 : Blo 346754 391333 := bbase (se 4 (by rfl) ⟨36687, by rfl⟩ : syracuseStep 391333 = 73375) (by norm_num)
theorem B522413 : Blo 346754 522413 := bbase (se 3 (by rfl) ⟨97952, by rfl⟩ : syracuseStep 522413 = 195905) (by norm_num)
theorem B784565 : Blo 346754 784565 := bbase (se 5 (by rfl) ⟨36776, by rfl⟩ : syracuseStep 784565 = 73553) (by norm_num)
theorem B587965 : Blo 346754 587965 := bbase (se 3 (by rfl) ⟨110243, by rfl⟩ : syracuseStep 587965 = 220487) (by norm_num)
theorem B522437 : Blo 346754 522437 := bbase (se 4 (by rfl) ⟨48978, by rfl⟩ : syracuseStep 522437 = 97957) (by norm_num)
theorem B391369 : Blo 346754 391369 := bbase (se 2 (by rfl) ⟨146763, by rfl⟩ : syracuseStep 391369 = 293527) (by norm_num)
theorem B522461 : Blo 346754 522461 := bbase (se 3 (by rfl) ⟨97961, by rfl⟩ : syracuseStep 522461 = 195923) (by norm_num)
theorem B1669349 : Blo 346754 1669349 := bbase (se 4 (by rfl) ⟨156501, by rfl⟩ : syracuseStep 1669349 = 313003) (by norm_num)
theorem B391405 : Blo 346754 391405 := bbase (se 3 (by rfl) ⟨73388, by rfl⟩ : syracuseStep 391405 = 146777) (by norm_num)
theorem B522485 : Blo 346754 522485 := bbase (se 5 (by rfl) ⟨24491, by rfl⟩ : syracuseStep 522485 = 48983) (by norm_num)
theorem B784637 : Blo 346754 784637 := bbase (se 3 (by rfl) ⟨147119, by rfl⟩ : syracuseStep 784637 = 294239) (by norm_num)
theorem B522509 : Blo 346754 522509 := bbase (se 3 (by rfl) ⟨97970, by rfl⟩ : syracuseStep 522509 = 195941) (by norm_num)
theorem B391441 : Blo 346754 391441 := bbase (se 2 (by rfl) ⟨146790, by rfl⟩ : syracuseStep 391441 = 293581) (by norm_num)
theorem B588053 : Blo 346754 588053 := bbase (se 6 (by rfl) ⟨13782, by rfl⟩ : syracuseStep 588053 = 27565) (by norm_num)
theorem B522533 : Blo 346754 522533 := bbase (se 4 (by rfl) ⟨48987, by rfl⟩ : syracuseStep 522533 = 97975) (by norm_num)
theorem B391477 : Blo 346754 391477 := bbase (se 5 (by rfl) ⟨18350, by rfl⟩ : syracuseStep 391477 = 36701) (by norm_num)
theorem B522557 : Blo 346754 522557 := bbase (se 3 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 522557 = 195959) (by norm_num)
theorem B784709 : Blo 346754 784709 := bbase (se 4 (by rfl) ⟨73566, by rfl⟩ : syracuseStep 784709 = 147133) (by norm_num)
theorem B883021 : Blo 346754 883021 := bbase (se 3 (by rfl) ⟨165566, by rfl⟩ : syracuseStep 883021 = 331133) (by norm_num)
theorem B522581 : Blo 346754 522581 := bbase (se 10 (by rfl) ⟨765, by rfl⟩ : syracuseStep 522581 = 1531) (by norm_num)
theorem B391513 : Blo 346754 391513 := bbase (se 2 (by rfl) ⟨146817, by rfl⟩ : syracuseStep 391513 = 293635) (by norm_num)
theorem B522605 : Blo 346754 522605 := bbase (se 3 (by rfl) ⟨97988, by rfl⟩ : syracuseStep 522605 = 195977) (by norm_num)
theorem B391549 : Blo 346754 391549 := bbase (se 3 (by rfl) ⟨73415, by rfl⟩ : syracuseStep 391549 = 146831) (by norm_num)
theorem B522629 : Blo 346754 522629 := bbase (se 4 (by rfl) ⟨48996, by rfl⟩ : syracuseStep 522629 = 97993) (by norm_num)
theorem B784781 : Blo 346754 784781 := bbase (se 3 (by rfl) ⟨147146, by rfl⟩ : syracuseStep 784781 = 294293) (by norm_num)
theorem B588181 : Blo 346754 588181 := bbase (se 6 (by rfl) ⟨13785, by rfl⟩ : syracuseStep 588181 = 27571) (by norm_num)
theorem B522653 : Blo 346754 522653 := bbase (se 3 (by rfl) ⟨97997, by rfl⟩ : syracuseStep 522653 = 195995) (by norm_num)
theorem B391585 : Blo 346754 391585 := bbase (se 2 (by rfl) ⟨146844, by rfl⟩ : syracuseStep 391585 = 293689) (by norm_num)
theorem B522677 : Blo 346754 522677 := bbase (se 5 (by rfl) ⟨24500, by rfl⟩ : syracuseStep 522677 = 49001) (by norm_num)
theorem B883133 : Blo 346754 883133 := bbase (se 3 (by rfl) ⟨165587, by rfl⟩ : syracuseStep 883133 = 331175) (by norm_num)
theorem B391621 : Blo 346754 391621 := bbase (se 4 (by rfl) ⟨36714, by rfl⟩ : syracuseStep 391621 = 73429) (by norm_num)
theorem B522701 : Blo 346754 522701 := bbase (se 3 (by rfl) ⟨98006, by rfl⟩ : syracuseStep 522701 = 196013) (by norm_num)
theorem B784853 : Blo 346754 784853 := bbase (se 7 (by rfl) ⟨9197, by rfl⟩ : syracuseStep 784853 = 18395) (by norm_num)
theorem B522725 : Blo 346754 522725 := bbase (se 4 (by rfl) ⟨49005, by rfl⟩ : syracuseStep 522725 = 98011) (by norm_num)
theorem B391657 : Blo 346754 391657 := bbase (se 2 (by rfl) ⟨146871, by rfl⟩ : syracuseStep 391657 = 293743) (by norm_num)
theorem B588269 : Blo 346754 588269 := bbase (se 3 (by rfl) ⟨110300, by rfl⟩ : syracuseStep 588269 = 220601) (by norm_num)
theorem B522749 : Blo 346754 522749 := bbase (se 3 (by rfl) ⟨98015, by rfl⟩ : syracuseStep 522749 = 196031) (by norm_num)
theorem B1178117 : Blo 346754 1178117 := bbase (se 4 (by rfl) ⟨110448, by rfl⟩ : syracuseStep 1178117 = 220897) (by norm_num)
theorem B391693 : Blo 346754 391693 := bbase (se 3 (by rfl) ⟨73442, by rfl⟩ : syracuseStep 391693 = 146885) (by norm_num)
theorem B522773 : Blo 346754 522773 := bbase (se 6 (by rfl) ⟨12252, by rfl⟩ : syracuseStep 522773 = 24505) (by norm_num)
theorem B784925 : Blo 346754 784925 := bbase (se 3 (by rfl) ⟨147173, by rfl⟩ : syracuseStep 784925 = 294347) (by norm_num)
theorem B522797 : Blo 346754 522797 := bbase (se 3 (by rfl) ⟨98024, by rfl⟩ : syracuseStep 522797 = 196049) (by norm_num)
theorem B391729 : Blo 346754 391729 := bbase (se 2 (by rfl) ⟨146898, by rfl⟩ : syracuseStep 391729 = 293797) (by norm_num)
theorem B1112629 : Blo 346754 1112629 := bbase (se 5 (by rfl) ⟨52154, by rfl⟩ : syracuseStep 1112629 = 104309) (by norm_num)
theorem B522821 : Blo 346754 522821 := bbase (se 4 (by rfl) ⟨49014, by rfl⟩ : syracuseStep 522821 = 98029) (by norm_num)
theorem B391765 : Blo 346754 391765 := bbase (se 8 (by rfl) ⟨2295, by rfl⟩ : syracuseStep 391765 = 4591) (by norm_num)
theorem B522845 : Blo 346754 522845 := bbase (se 3 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 522845 = 196067) (by norm_num)
theorem B784997 : Blo 346754 784997 := bbase (se 4 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 784997 = 147187) (by norm_num)
theorem B588397 : Blo 346754 588397 := bbase (se 3 (by rfl) ⟨110324, by rfl⟩ : syracuseStep 588397 = 220649) (by norm_num)
theorem B522869 : Blo 346754 522869 := bbase (se 5 (by rfl) ⟨24509, by rfl⟩ : syracuseStep 522869 = 49019) (by norm_num)
theorem B391801 : Blo 346754 391801 := bbase (se 2 (by rfl) ⟨146925, by rfl⟩ : syracuseStep 391801 = 293851) (by norm_num)
theorem B883325 : Blo 346754 883325 := bbase (se 3 (by rfl) ⟨165623, by rfl⟩ : syracuseStep 883325 = 331247) (by norm_num)
theorem B522893 : Blo 346754 522893 := bbase (se 3 (by rfl) ⟨98042, by rfl⟩ : syracuseStep 522893 = 196085) (by norm_num)
theorem B391837 : Blo 346754 391837 := bbase (se 3 (by rfl) ⟨73469, by rfl⟩ : syracuseStep 391837 = 146939) (by norm_num)
theorem B522917 : Blo 346754 522917 := bbase (se 4 (by rfl) ⟨49023, by rfl⟩ : syracuseStep 522917 = 98047) (by norm_num)
theorem B785069 : Blo 346754 785069 := bbase (se 3 (by rfl) ⟨147200, by rfl⟩ : syracuseStep 785069 = 294401) (by norm_num)
theorem B522941 : Blo 346754 522941 := bbase (se 3 (by rfl) ⟨98051, by rfl⟩ : syracuseStep 522941 = 196103) (by norm_num)
theorem B391873 : Blo 346754 391873 := bbase (se 2 (by rfl) ⟨146952, by rfl⟩ : syracuseStep 391873 = 293905) (by norm_num)
theorem B588485 : Blo 346754 588485 := bbase (se 4 (by rfl) ⟨55170, by rfl⟩ : syracuseStep 588485 = 110341) (by norm_num)
theorem B522965 : Blo 346754 522965 := bbase (se 7 (by rfl) ⟨6128, by rfl⟩ : syracuseStep 522965 = 12257) (by norm_num)
theorem B391909 : Blo 346754 391909 := bbase (se 4 (by rfl) ⟨36741, by rfl⟩ : syracuseStep 391909 = 73483) (by norm_num)
theorem B522989 : Blo 346754 522989 := bbase (se 3 (by rfl) ⟨98060, by rfl⟩ : syracuseStep 522989 = 196121) (by norm_num)
theorem B785141 : Blo 346754 785141 := bbase (se 5 (by rfl) ⟨36803, by rfl⟩ : syracuseStep 785141 = 73607) (by norm_num)
theorem B523013 : Blo 346754 523013 := bbase (se 4 (by rfl) ⟨49032, by rfl⟩ : syracuseStep 523013 = 98065) (by norm_num)
theorem B391945 : Blo 346754 391945 := bbase (se 2 (by rfl) ⟨146979, by rfl⟩ : syracuseStep 391945 = 293959) (by norm_num)
theorem B523037 : Blo 346754 523037 := bbase (se 3 (by rfl) ⟨98069, by rfl⟩ : syracuseStep 523037 = 196139) (by norm_num)
theorem B1768229 : Blo 346754 1768229 := bbase (se 4 (by rfl) ⟨165771, by rfl⟩ : syracuseStep 1768229 = 331543) (by norm_num)
theorem B391981 : Blo 346754 391981 := bbase (se 3 (by rfl) ⟨73496, by rfl⟩ : syracuseStep 391981 = 146993) (by norm_num)
theorem B523061 : Blo 346754 523061 := bbase (se 5 (by rfl) ⟨24518, by rfl⟩ : syracuseStep 523061 = 49037) (by norm_num)
theorem B1997621 : Blo 346754 1997621 := bbase (se 5 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 1997621 = 187277) (by norm_num)
theorem B785213 : Blo 346754 785213 := bbase (se 3 (by rfl) ⟨147227, by rfl⟩ : syracuseStep 785213 = 294455) (by norm_num)
theorem B588613 : Blo 346754 588613 := bbase (se 4 (by rfl) ⟨55182, by rfl⟩ : syracuseStep 588613 = 110365) (by norm_num)
theorem B523085 : Blo 346754 523085 := bbase (se 3 (by rfl) ⟨98078, by rfl⟩ : syracuseStep 523085 = 196157) (by norm_num)
theorem B392017 : Blo 346754 392017 := bbase (se 2 (by rfl) ⟨147006, by rfl⟩ : syracuseStep 392017 = 294013) (by norm_num)
theorem B1604437 : Blo 346754 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B523109 : Blo 346754 523109 := bbase (se 4 (by rfl) ⟨49041, by rfl⟩ : syracuseStep 523109 = 98083) (by norm_num)
theorem B359273 : Blo 346754 359273 := bbase (se 2 (by rfl) ⟨134727, by rfl⟩ : syracuseStep 359273 = 269455) (by norm_num)
theorem B392053 : Blo 346754 392053 := bbase (se 5 (by rfl) ⟨18377, by rfl⟩ : syracuseStep 392053 = 36755) (by norm_num)
theorem B523133 : Blo 346754 523133 := bbase (se 3 (by rfl) ⟨98087, by rfl⟩ : syracuseStep 523133 = 196175) (by norm_num)
theorem B785285 : Blo 346754 785285 := bbase (se 4 (by rfl) ⟨73620, by rfl⟩ : syracuseStep 785285 = 147241) (by norm_num)
theorem B523157 : Blo 346754 523157 := bbase (se 6 (by rfl) ⟨12261, by rfl⟩ : syracuseStep 523157 = 24523) (by norm_num)
theorem B392089 : Blo 346754 392089 := bbase (se 2 (by rfl) ⟨147033, by rfl⟩ : syracuseStep 392089 = 294067) (by norm_num)
theorem B588701 : Blo 346754 588701 := bbase (se 3 (by rfl) ⟨110381, by rfl⟩ : syracuseStep 588701 = 220763) (by norm_num)
theorem B523181 : Blo 346754 523181 := bbase (se 3 (by rfl) ⟨98096, by rfl⟩ : syracuseStep 523181 = 196193) (by norm_num)
theorem B1178549 : Blo 346754 1178549 := bbase (se 5 (by rfl) ⟨55244, by rfl⟩ : syracuseStep 1178549 = 110489) (by norm_num)
theorem B392125 : Blo 346754 392125 := bbase (se 3 (by rfl) ⟨73523, by rfl⟩ : syracuseStep 392125 = 147047) (by norm_num)
theorem B523205 : Blo 346754 523205 := bbase (se 4 (by rfl) ⟨49050, by rfl⟩ : syracuseStep 523205 = 98101) (by norm_num)
theorem B785357 : Blo 346754 785357 := bbase (se 3 (by rfl) ⟨147254, by rfl⟩ : syracuseStep 785357 = 294509) (by norm_num)
theorem B883669 : Blo 346754 883669 := bbase (se 7 (by rfl) ⟨10355, by rfl⟩ : syracuseStep 883669 = 20711) (by norm_num)
theorem B523229 : Blo 346754 523229 := bbase (se 3 (by rfl) ⟨98105, by rfl⟩ : syracuseStep 523229 = 196211) (by norm_num)
theorem B392161 : Blo 346754 392161 := bbase (se 2 (by rfl) ⟨147060, by rfl⟩ : syracuseStep 392161 = 294121) (by norm_num)
theorem B523253 : Blo 346754 523253 := bbase (se 5 (by rfl) ⟨24527, by rfl⟩ : syracuseStep 523253 = 49055) (by norm_num)
theorem B392197 : Blo 346754 392197 := bbase (se 4 (by rfl) ⟨36768, by rfl⟩ : syracuseStep 392197 = 73537) (by norm_num)
theorem B523277 : Blo 346754 523277 := bbase (se 3 (by rfl) ⟨98114, by rfl⟩ : syracuseStep 523277 = 196229) (by norm_num)
theorem B785429 : Blo 346754 785429 := bbase (se 6 (by rfl) ⟨18408, by rfl⟩ : syracuseStep 785429 = 36817) (by norm_num)
theorem B588829 : Blo 346754 588829 := bbase (se 3 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 588829 = 220811) (by norm_num)
theorem B523301 : Blo 346754 523301 := bbase (se 4 (by rfl) ⟨49059, by rfl⟩ : syracuseStep 523301 = 98119) (by norm_num)
theorem B392233 : Blo 346754 392233 := bbase (se 2 (by rfl) ⟨147087, by rfl⟩ : syracuseStep 392233 = 294175) (by norm_num)
theorem B523325 : Blo 346754 523325 := bbase (se 3 (by rfl) ⟨98123, by rfl⟩ : syracuseStep 523325 = 196247) (by norm_num)
theorem B883781 : Blo 346754 883781 := bbase (se 4 (by rfl) ⟨82854, by rfl⟩ : syracuseStep 883781 = 165709) (by norm_num)
theorem B392269 : Blo 346754 392269 := bbase (se 3 (by rfl) ⟨73550, by rfl⟩ : syracuseStep 392269 = 147101) (by norm_num)
theorem B523349 : Blo 346754 523349 := bbase (se 8 (by rfl) ⟨3066, by rfl⟩ : syracuseStep 523349 = 6133) (by norm_num)
theorem B785501 : Blo 346754 785501 := bbase (se 3 (by rfl) ⟨147281, by rfl⟩ : syracuseStep 785501 = 294563) (by norm_num)
theorem B523373 : Blo 346754 523373 := bbase (se 3 (by rfl) ⟨98132, by rfl⟩ : syracuseStep 523373 = 196265) (by norm_num)
theorem B392305 : Blo 346754 392305 := bbase (se 2 (by rfl) ⟨147114, by rfl⟩ : syracuseStep 392305 = 294229) (by norm_num)
theorem B588917 : Blo 346754 588917 := bbase (se 5 (by rfl) ⟨27605, by rfl⟩ : syracuseStep 588917 = 55211) (by norm_num)
theorem B523397 : Blo 346754 523397 := bbase (se 4 (by rfl) ⟨49068, by rfl⟩ : syracuseStep 523397 = 98137) (by norm_num)
theorem B392341 : Blo 346754 392341 := bbase (se 6 (by rfl) ⟨9195, by rfl⟩ : syracuseStep 392341 = 18391) (by norm_num)
theorem B523421 : Blo 346754 523421 := bbase (se 3 (by rfl) ⟨98141, by rfl⟩ : syracuseStep 523421 = 196283) (by norm_num)
theorem B785573 : Blo 346754 785573 := bbase (se 4 (by rfl) ⟨73647, by rfl⟩ : syracuseStep 785573 = 147295) (by norm_num)
theorem B523445 : Blo 346754 523445 := bbase (se 5 (by rfl) ⟨24536, by rfl⟩ : syracuseStep 523445 = 49073) (by norm_num)
theorem B392377 : Blo 346754 392377 := bbase (se 2 (by rfl) ⟨147141, by rfl⟩ : syracuseStep 392377 = 294283) (by norm_num)
theorem B523469 : Blo 346754 523469 := bbase (se 3 (by rfl) ⟨98150, by rfl⟩ : syracuseStep 523469 = 196301) (by norm_num)
theorem B392413 : Blo 346754 392413 := bbase (se 3 (by rfl) ⟨73577, by rfl⟩ : syracuseStep 392413 = 147155) (by norm_num)
theorem B523493 : Blo 346754 523493 := bbase (se 4 (by rfl) ⟨49077, by rfl⟩ : syracuseStep 523493 = 98155) (by norm_num)
theorem B785645 : Blo 346754 785645 := bbase (se 3 (by rfl) ⟨147308, by rfl⟩ : syracuseStep 785645 = 294617) (by norm_num)
theorem B589045 : Blo 346754 589045 := bbase (se 5 (by rfl) ⟨27611, by rfl⟩ : syracuseStep 589045 = 55223) (by norm_num)
theorem B523517 : Blo 346754 523517 := bbase (se 3 (by rfl) ⟨98159, by rfl⟩ : syracuseStep 523517 = 196319) (by norm_num)
theorem B392449 : Blo 346754 392449 := bbase (se 2 (by rfl) ⟨147168, by rfl⟩ : syracuseStep 392449 = 294337) (by norm_num)
theorem B883973 : Blo 346754 883973 := bbase (se 4 (by rfl) ⟨82872, by rfl⟩ : syracuseStep 883973 = 165745) (by norm_num)
theorem B523541 : Blo 346754 523541 := bbase (se 6 (by rfl) ⟨12270, by rfl⟩ : syracuseStep 523541 = 24541) (by norm_num)
theorem B392485 : Blo 346754 392485 := bbase (se 4 (by rfl) ⟨36795, by rfl⟩ : syracuseStep 392485 = 73591) (by norm_num)
theorem B523565 : Blo 346754 523565 := bbase (se 3 (by rfl) ⟨98168, by rfl⟩ : syracuseStep 523565 = 196337) (by norm_num)
theorem B785717 : Blo 346754 785717 := bbase (se 5 (by rfl) ⟨36830, by rfl⟩ : syracuseStep 785717 = 73661) (by norm_num)
theorem B523589 : Blo 346754 523589 := bbase (se 4 (by rfl) ⟨49086, by rfl⟩ : syracuseStep 523589 = 98173) (by norm_num)
theorem B392521 : Blo 346754 392521 := bbase (se 2 (by rfl) ⟨147195, by rfl⟩ : syracuseStep 392521 = 294391) (by norm_num)
theorem B589133 : Blo 346754 589133 := bbase (se 3 (by rfl) ⟨110462, by rfl⟩ : syracuseStep 589133 = 220925) (by norm_num)
theorem B523613 : Blo 346754 523613 := bbase (se 3 (by rfl) ⟨98177, by rfl⟩ : syracuseStep 523613 = 196355) (by norm_num)
theorem B1178981 : Blo 346754 1178981 := bbase (se 4 (by rfl) ⟨110529, by rfl⟩ : syracuseStep 1178981 = 221059) (by norm_num)
theorem B392557 : Blo 346754 392557 := bbase (se 3 (by rfl) ⟨73604, by rfl⟩ : syracuseStep 392557 = 147209) (by norm_num)
theorem B523637 : Blo 346754 523637 := bbase (se 5 (by rfl) ⟨24545, by rfl⟩ : syracuseStep 523637 = 49091) (by norm_num)
theorem B785789 : Blo 346754 785789 := bbase (se 3 (by rfl) ⟨147335, by rfl⟩ : syracuseStep 785789 = 294671) (by norm_num)
theorem B523661 : Blo 346754 523661 := bbase (se 3 (by rfl) ⟨98186, by rfl⟩ : syracuseStep 523661 = 196373) (by norm_num)
theorem B392593 : Blo 346754 392593 := bbase (se 2 (by rfl) ⟨147222, by rfl⟩ : syracuseStep 392593 = 294445) (by norm_num)
theorem B523685 : Blo 346754 523685 := bbase (se 4 (by rfl) ⟨49095, by rfl⟩ : syracuseStep 523685 = 98191) (by norm_num)
theorem B392629 : Blo 346754 392629 := bbase (se 5 (by rfl) ⟨18404, by rfl⟩ : syracuseStep 392629 = 36809) (by norm_num)
theorem B523709 : Blo 346754 523709 := bbase (se 3 (by rfl) ⟨98195, by rfl⟩ : syracuseStep 523709 = 196391) (by norm_num)
theorem B785861 : Blo 346754 785861 := bbase (se 4 (by rfl) ⟨73674, by rfl⟩ : syracuseStep 785861 = 147349) (by norm_num)
theorem B589261 : Blo 346754 589261 := bbase (se 3 (by rfl) ⟨110486, by rfl⟩ : syracuseStep 589261 = 220973) (by norm_num)
theorem B425425 : Blo 346754 425425 := bbase (se 2 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 425425 = 319069) (by norm_num)
theorem B523733 : Blo 346754 523733 := bbase (se 7 (by rfl) ⟨6137, by rfl⟩ : syracuseStep 523733 = 12275) (by norm_num)
theorem B392665 : Blo 346754 392665 := bbase (se 2 (by rfl) ⟨147249, by rfl⟩ : syracuseStep 392665 = 294499) (by norm_num)
theorem B523757 : Blo 346754 523757 := bbase (se 3 (by rfl) ⟨98204, by rfl⟩ : syracuseStep 523757 = 196409) (by norm_num)
theorem B392701 : Blo 346754 392701 := bbase (se 3 (by rfl) ⟨73631, by rfl⟩ : syracuseStep 392701 = 147263) (by norm_num)
theorem B523781 : Blo 346754 523781 := bbase (se 4 (by rfl) ⟨49104, by rfl⟩ : syracuseStep 523781 = 98209) (by norm_num)
theorem B785933 : Blo 346754 785933 := bbase (se 3 (by rfl) ⟨147362, by rfl⟩ : syracuseStep 785933 = 294725) (by norm_num)
theorem B523805 : Blo 346754 523805 := bbase (se 3 (by rfl) ⟨98213, by rfl⟩ : syracuseStep 523805 = 196427) (by norm_num)
theorem B392737 : Blo 346754 392737 := bbase (se 2 (by rfl) ⟨147276, by rfl⟩ : syracuseStep 392737 = 294553) (by norm_num)
theorem B589349 : Blo 346754 589349 := bbase (se 4 (by rfl) ⟨55251, by rfl⟩ : syracuseStep 589349 = 110503) (by norm_num)
theorem B523829 : Blo 346754 523829 := bbase (se 5 (by rfl) ⟨24554, by rfl⟩ : syracuseStep 523829 = 49109) (by norm_num)
theorem B392773 : Blo 346754 392773 := bbase (se 4 (by rfl) ⟨36822, by rfl⟩ : syracuseStep 392773 = 73645) (by norm_num)
theorem B523853 : Blo 346754 523853 := bbase (se 3 (by rfl) ⟨98222, by rfl⟩ : syracuseStep 523853 = 196445) (by norm_num)
theorem B786005 : Blo 346754 786005 := bbase (se 8 (by rfl) ⟨4605, by rfl⟩ : syracuseStep 786005 = 9211) (by norm_num)
theorem B884317 : Blo 346754 884317 := bbase (se 3 (by rfl) ⟨165809, by rfl⟩ : syracuseStep 884317 = 331619) (by norm_num)
theorem B523877 : Blo 346754 523877 := bbase (se 4 (by rfl) ⟨49113, by rfl⟩ : syracuseStep 523877 = 98227) (by norm_num)
theorem B392809 : Blo 346754 392809 := bbase (se 2 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 392809 = 294607) (by norm_num)
theorem B523901 : Blo 346754 523901 := bbase (se 3 (by rfl) ⟨98231, by rfl⟩ : syracuseStep 523901 = 196463) (by norm_num)
theorem B392845 : Blo 346754 392845 := bbase (se 3 (by rfl) ⟨73658, by rfl⟩ : syracuseStep 392845 = 147317) (by norm_num)
theorem B523925 : Blo 346754 523925 := bbase (se 6 (by rfl) ⟨12279, by rfl⟩ : syracuseStep 523925 = 24559) (by norm_num)
theorem B786077 : Blo 346754 786077 := bbase (se 3 (by rfl) ⟨147389, by rfl⟩ : syracuseStep 786077 = 294779) (by norm_num)
theorem B589477 : Blo 346754 589477 := bbase (se 4 (by rfl) ⟨55263, by rfl⟩ : syracuseStep 589477 = 110527) (by norm_num)
theorem B523949 : Blo 346754 523949 := bbase (se 3 (by rfl) ⟨98240, by rfl⟩ : syracuseStep 523949 = 196481) (by norm_num)
theorem B392881 : Blo 346754 392881 := bbase (se 2 (by rfl) ⟨147330, by rfl⟩ : syracuseStep 392881 = 294661) (by norm_num)
theorem B523973 : Blo 346754 523973 := bbase (se 4 (by rfl) ⟨49122, by rfl⟩ : syracuseStep 523973 = 98245) (by norm_num)
theorem B884429 : Blo 346754 884429 := bbase (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) (by norm_num)
theorem B392917 : Blo 346754 392917 := bbase (se 7 (by rfl) ⟨4604, by rfl⟩ : syracuseStep 392917 = 9209) (by norm_num)
theorem B523997 : Blo 346754 523997 := bbase (se 3 (by rfl) ⟨98249, by rfl⟩ : syracuseStep 523997 = 196499) (by norm_num)
theorem B786149 : Blo 346754 786149 := bbase (se 4 (by rfl) ⟨73701, by rfl⟩ : syracuseStep 786149 = 147403) (by norm_num)
theorem B556789 : Blo 346754 556789 := bbase (se 5 (by rfl) ⟨26099, by rfl⟩ : syracuseStep 556789 = 52199) (by norm_num)
theorem B524021 : Blo 346754 524021 := bbase (se 5 (by rfl) ⟨24563, by rfl⟩ : syracuseStep 524021 = 49127) (by norm_num)
theorem B392953 : Blo 346754 392953 := bbase (se 2 (by rfl) ⟨147357, by rfl⟩ : syracuseStep 392953 = 294715) (by norm_num)
theorem B589565 : Blo 346754 589565 := bbase (se 3 (by rfl) ⟨110543, by rfl⟩ : syracuseStep 589565 = 221087) (by norm_num)
theorem B524045 : Blo 346754 524045 := bbase (se 3 (by rfl) ⟨98258, by rfl⟩ : syracuseStep 524045 = 196517) (by norm_num)
theorem B1179413 : Blo 346754 1179413 := bbase (se 6 (by rfl) ⟨27642, by rfl⟩ : syracuseStep 1179413 = 55285) (by norm_num)
theorem B392989 : Blo 346754 392989 := bbase (se 3 (by rfl) ⟨73685, by rfl⟩ : syracuseStep 392989 = 147371) (by norm_num)
theorem B524069 : Blo 346754 524069 := bbase (se 4 (by rfl) ⟨49131, by rfl⟩ : syracuseStep 524069 = 98263) (by norm_num)
theorem B786221 : Blo 346754 786221 := bbase (se 3 (by rfl) ⟨147416, by rfl⟩ : syracuseStep 786221 = 294833) (by norm_num)
theorem B425785 : Blo 346754 425785 := bbase (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) (by norm_num)
theorem B524093 : Blo 346754 524093 := bbase (se 3 (by rfl) ⟨98267, by rfl⟩ : syracuseStep 524093 = 196535) (by norm_num)
theorem B393025 : Blo 346754 393025 := bbase (se 2 (by rfl) ⟨147384, by rfl⟩ : syracuseStep 393025 = 294769) (by norm_num)
theorem B524117 : Blo 346754 524117 := bbase (se 9 (by rfl) ⟨1535, by rfl⟩ : syracuseStep 524117 = 3071) (by norm_num)
theorem B393061 : Blo 346754 393061 := bbase (se 4 (by rfl) ⟨36849, by rfl⟩ : syracuseStep 393061 = 73699) (by norm_num)
theorem B524141 : Blo 346754 524141 := bbase (se 3 (by rfl) ⟨98276, by rfl⟩ : syracuseStep 524141 = 196553) (by norm_num)
theorem B786293 : Blo 346754 786293 := bbase (se 5 (by rfl) ⟨36857, by rfl⟩ : syracuseStep 786293 = 73715) (by norm_num)
theorem B589693 : Blo 346754 589693 := bbase (se 3 (by rfl) ⟨110567, by rfl⟩ : syracuseStep 589693 = 221135) (by norm_num)
theorem B524165 : Blo 346754 524165 := bbase (se 4 (by rfl) ⟨49140, by rfl⟩ : syracuseStep 524165 = 98281) (by norm_num)
theorem B393097 : Blo 346754 393097 := bbase (se 2 (by rfl) ⟨147411, by rfl⟩ : syracuseStep 393097 = 294823) (by norm_num)
theorem B884621 : Blo 346754 884621 := bbase (se 3 (by rfl) ⟨165866, by rfl⟩ : syracuseStep 884621 = 331733) (by norm_num)
theorem B524189 : Blo 346754 524189 := bbase (se 3 (by rfl) ⟨98285, by rfl⟩ : syracuseStep 524189 = 196571) (by norm_num)
theorem B393133 : Blo 346754 393133 := bbase (se 3 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 393133 = 147425) (by norm_num)
theorem B524213 : Blo 346754 524213 := bbase (se 5 (by rfl) ⟨24572, by rfl⟩ : syracuseStep 524213 = 49145) (by norm_num)
theorem B786365 : Blo 346754 786365 := bbase (se 3 (by rfl) ⟨147443, by rfl⟩ : syracuseStep 786365 = 294887) (by norm_num)
theorem B524237 : Blo 346754 524237 := bbase (se 3 (by rfl) ⟨98294, by rfl⟩ : syracuseStep 524237 = 196589) (by norm_num)
theorem B393169 : Blo 346754 393169 := bbase (se 2 (by rfl) ⟨147438, by rfl⟩ : syracuseStep 393169 = 294877) (by norm_num)
theorem B589781 : Blo 346754 589781 := bbase (se 7 (by rfl) ⟨6911, by rfl⟩ : syracuseStep 589781 = 13823) (by norm_num)
theorem B524261 : Blo 346754 524261 := bbase (se 4 (by rfl) ⟨49149, by rfl⟩ : syracuseStep 524261 = 98299) (by norm_num)
theorem B557045 : Blo 346754 557045 := bbase (se 5 (by rfl) ⟨26111, by rfl⟩ : syracuseStep 557045 = 52223) (by norm_num)
theorem B393205 : Blo 346754 393205 := bbase (se 5 (by rfl) ⟨18431, by rfl⟩ : syracuseStep 393205 = 36863) (by norm_num)
theorem B524285 : Blo 346754 524285 := bbase (se 3 (by rfl) ⟨98303, by rfl⟩ : syracuseStep 524285 = 196607) (by norm_num)
theorem B524291 : Blo 346754 524291 := bstep (se 1 (by rfl) ⟨393218, by rfl⟩ : syracuseStep 524291 = 786437) B786437
theorem B884753 : Blo 346754 884753 := bstep (se 2 (by rfl) ⟨331782, by rfl⟩ : syracuseStep 884753 = 663565) B663565
theorem B524321 : Blo 346754 524321 := bstep (se 2 (by rfl) ⟨196620, by rfl⟩ : syracuseStep 524321 = 393241) B393241
theorem B1179683 : Blo 346754 1179683 := bstep (se 1 (by rfl) ⟨884762, by rfl⟩ : syracuseStep 1179683 = 1769525) B1769525
theorem B524339 : Blo 346754 524339 := bstep (se 1 (by rfl) ⟨393254, by rfl⟩ : syracuseStep 524339 = 786509) B786509
theorem B589889 : Blo 346754 589889 := bstep (se 2 (by rfl) ⟨221208, by rfl⟩ : syracuseStep 589889 = 442417) B442417
theorem B884803 : Blo 346754 884803 := bstep (se 1 (by rfl) ⟨663602, by rfl⟩ : syracuseStep 884803 = 1327205) B1327205
theorem B524369 : Blo 346754 524369 := bstep (se 2 (by rfl) ⟨196638, by rfl⟩ : syracuseStep 524369 = 393277) B393277
theorem B524387 : Blo 346754 524387 := bstep (se 1 (by rfl) ⟨393290, by rfl⟩ : syracuseStep 524387 = 786581) B786581
theorem B786545 : Blo 346754 786545 := bstep (se 2 (by rfl) ⟨294954, by rfl⟩ : syracuseStep 786545 = 589909) B589909
theorem B393331 : Blo 346754 393331 := bstep (se 1 (by rfl) ⟨294998, by rfl⟩ : syracuseStep 393331 = 589997) B589997
theorem B524417 : Blo 346754 524417 := bstep (se 2 (by rfl) ⟨196656, by rfl⟩ : syracuseStep 524417 = 393313) B393313
theorem B786563 : Blo 346754 786563 := bstep (se 1 (by rfl) ⟨589922, by rfl⟩ : syracuseStep 786563 = 1179845) B1179845
theorem B524435 : Blo 346754 524435 := bstep (se 1 (by rfl) ⟨393326, by rfl⟩ : syracuseStep 524435 = 786653) B786653
theorem B524465 : Blo 346754 524465 := bstep (se 2 (by rfl) ⟨196674, by rfl⟩ : syracuseStep 524465 = 393349) B393349
theorem B590017 : Blo 346754 590017 := bstep (se 2 (by rfl) ⟨221256, by rfl⟩ : syracuseStep 590017 = 442513) B442513
theorem B524483 : Blo 346754 524483 := bstep (se 1 (by rfl) ⟨393362, by rfl⟩ : syracuseStep 524483 = 786725) B786725
theorem B884945 : Blo 346754 884945 := bstep (se 2 (by rfl) ⟨331854, by rfl⟩ : syracuseStep 884945 = 663709) B663709
theorem B524513 : Blo 346754 524513 := bstep (se 2 (by rfl) ⟨196692, by rfl⟩ : syracuseStep 524513 = 393385) B393385
theorem B590051 : Blo 346754 590051 := bstep (se 1 (by rfl) ⟨442538, by rfl⟩ : syracuseStep 590051 = 885077) B885077
theorem B524531 : Blo 346754 524531 := bstep (se 1 (by rfl) ⟨393398, by rfl⟩ : syracuseStep 524531 = 786797) B786797
theorem B393475 : Blo 346754 393475 := bstep (se 1 (by rfl) ⟨295106, by rfl⟩ : syracuseStep 393475 = 590213) B590213
theorem B2228485 : Blo 346754 2228485 := bstep (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) B417841
theorem B524561 : Blo 346754 524561 := bstep (se 2 (by rfl) ⟨196710, by rfl⟩ : syracuseStep 524561 = 393421) B393421
theorem B524579 : Blo 346754 524579 := bstep (se 1 (by rfl) ⟨393434, by rfl⟩ : syracuseStep 524579 = 786869) B786869
theorem B1179953 : Blo 346754 1179953 := bstep (se 2 (by rfl) ⟨442482, by rfl⟩ : syracuseStep 1179953 = 884965) B884965
theorem B524609 : Blo 346754 524609 := bstep (se 2 (by rfl) ⟨196728, by rfl⟩ : syracuseStep 524609 = 393457) B393457
theorem B524627 : Blo 346754 524627 := bstep (se 1 (by rfl) ⟨393470, by rfl⟩ : syracuseStep 524627 = 786941) B786941
theorem B590179 : Blo 346754 590179 := bstep (se 1 (by rfl) ⟨442634, by rfl⟩ : syracuseStep 590179 = 885269) B885269
theorem B524657 : Blo 346754 524657 := bstep (se 2 (by rfl) ⟨196746, by rfl⟩ : syracuseStep 524657 = 393493) B393493
theorem B1114499 : Blo 346754 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B524675 : Blo 346754 524675 := bstep (se 1 (by rfl) ⟨393506, by rfl⟩ : syracuseStep 524675 = 787013) B787013
theorem B786833 : Blo 346754 786833 := bstep (se 2 (by rfl) ⟨295062, by rfl⟩ : syracuseStep 786833 = 590125) B590125
theorem B393619 : Blo 346754 393619 := bstep (se 1 (by rfl) ⟨295214, by rfl⟩ : syracuseStep 393619 = 590429) B590429
theorem B524705 : Blo 346754 524705 := bstep (se 2 (by rfl) ⟨196764, by rfl⟩ : syracuseStep 524705 = 393529) B393529
theorem B786851 : Blo 346754 786851 := bstep (se 1 (by rfl) ⟨590138, by rfl⟩ : syracuseStep 786851 = 1180277) B1180277
theorem B524723 : Blo 346754 524723 := bstep (se 1 (by rfl) ⟨393542, by rfl⟩ : syracuseStep 524723 = 787085) B787085
theorem B524753 : Blo 346754 524753 := bstep (se 2 (by rfl) ⟨196782, by rfl⟩ : syracuseStep 524753 = 393565) B393565
theorem B524771 : Blo 346754 524771 := bstep (se 1 (by rfl) ⟨393578, by rfl⟩ : syracuseStep 524771 = 787157) B787157
theorem B590321 : Blo 346754 590321 := bstep (se 2 (by rfl) ⟨221370, by rfl⟩ : syracuseStep 590321 = 442741) B442741
theorem B524801 : Blo 346754 524801 := bstep (se 2 (by rfl) ⟨196800, by rfl⟩ : syracuseStep 524801 = 393601) B393601
theorem B524819 : Blo 346754 524819 := bstep (se 1 (by rfl) ⟨393614, by rfl⟩ : syracuseStep 524819 = 787229) B787229
theorem B393763 : Blo 346754 393763 := bstep (se 1 (by rfl) ⟨295322, by rfl⟩ : syracuseStep 393763 = 590645) B590645
theorem B524849 : Blo 346754 524849 := bstep (se 2 (by rfl) ⟨196818, by rfl⟩ : syracuseStep 524849 = 393637) B393637
theorem B524867 : Blo 346754 524867 := bstep (se 1 (by rfl) ⟨393650, by rfl⟩ : syracuseStep 524867 = 787301) B787301
theorem B524897 : Blo 346754 524897 := bstep (se 2 (by rfl) ⟨196836, by rfl⟩ : syracuseStep 524897 = 393673) B393673
theorem B590449 : Blo 346754 590449 := bstep (se 2 (by rfl) ⟨221418, by rfl⟩ : syracuseStep 590449 = 442837) B442837
theorem B524915 : Blo 346754 524915 := bstep (se 1 (by rfl) ⟨393686, by rfl⟩ : syracuseStep 524915 = 787373) B787373
theorem B524945 : Blo 346754 524945 := bstep (se 2 (by rfl) ⟨196854, by rfl⟩ : syracuseStep 524945 = 393709) B393709
theorem B590483 : Blo 346754 590483 := bstep (se 1 (by rfl) ⟨442862, by rfl⟩ : syracuseStep 590483 = 885725) B885725
theorem B1704611 : Blo 346754 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B524963 : Blo 346754 524963 := bstep (se 1 (by rfl) ⟨393722, by rfl⟩ : syracuseStep 524963 = 787445) B787445
theorem B787121 : Blo 346754 787121 := bstep (se 2 (by rfl) ⟨295170, by rfl⟩ : syracuseStep 787121 = 590341) B590341
theorem B393907 : Blo 346754 393907 := bstep (se 1 (by rfl) ⟨295430, by rfl⟩ : syracuseStep 393907 = 590861) B590861
theorem B524993 : Blo 346754 524993 := bstep (se 2 (by rfl) ⟨196872, by rfl⟩ : syracuseStep 524993 = 393745) B393745
theorem B787139 : Blo 346754 787139 := bstep (se 1 (by rfl) ⟨590354, by rfl⟩ : syracuseStep 787139 = 1180709) B1180709
theorem B6062789 : Blo 346754 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B525011 : Blo 346754 525011 := bstep (se 1 (by rfl) ⟨393758, by rfl⟩ : syracuseStep 525011 = 787517) B787517
theorem B525041 : Blo 346754 525041 := bstep (se 2 (by rfl) ⟨196890, by rfl⟩ : syracuseStep 525041 = 393781) B393781
theorem B525059 : Blo 346754 525059 := bstep (se 1 (by rfl) ⟨393794, by rfl⟩ : syracuseStep 525059 = 787589) B787589
theorem B590611 : Blo 346754 590611 := bstep (se 1 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 590611 = 885917) B885917
theorem B525089 : Blo 346754 525089 := bstep (se 2 (by rfl) ⟨196908, by rfl⟩ : syracuseStep 525089 = 393817) B393817
theorem B525107 : Blo 346754 525107 := bstep (se 1 (by rfl) ⟨393830, by rfl⟩ : syracuseStep 525107 = 787661) B787661
theorem B394051 : Blo 346754 394051 := bstep (se 1 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 394051 = 591077) B591077
theorem B1180493 : Blo 346754 1180493 := bstep (se 3 (by rfl) ⟨221342, by rfl⟩ : syracuseStep 1180493 = 442685) B442685
theorem B525137 : Blo 346754 525137 := bstep (se 2 (by rfl) ⟨196926, by rfl⟩ : syracuseStep 525137 = 393853) B393853
theorem B525155 : Blo 346754 525155 := bstep (se 1 (by rfl) ⟨393866, by rfl⟩ : syracuseStep 525155 = 787733) B787733
theorem B525185 : Blo 346754 525185 := bstep (se 2 (by rfl) ⟨196944, by rfl⟩ : syracuseStep 525185 = 393889) B393889
theorem B1180547 : Blo 346754 1180547 := bstep (se 1 (by rfl) ⟨885410, by rfl⟩ : syracuseStep 1180547 = 1770821) B1770821
theorem B525203 : Blo 346754 525203 := bstep (se 1 (by rfl) ⟨393902, by rfl⟩ : syracuseStep 525203 = 787805) B787805
theorem B590753 : Blo 346754 590753 := bstep (se 2 (by rfl) ⟨221532, by rfl⟩ : syracuseStep 590753 = 443065) B443065
theorem B525233 : Blo 346754 525233 := bstep (se 2 (by rfl) ⟨196962, by rfl⟩ : syracuseStep 525233 = 393925) B393925
theorem B558019 : Blo 346754 558019 := bstep (se 1 (by rfl) ⟨418514, by rfl⟩ : syracuseStep 558019 = 837029) B837029
theorem B525251 : Blo 346754 525251 := bstep (se 1 (by rfl) ⟨393938, by rfl⟩ : syracuseStep 525251 = 787877) B787877
theorem B787409 : Blo 346754 787409 := bstep (se 2 (by rfl) ⟨295278, by rfl⟩ : syracuseStep 787409 = 590557) B590557
theorem B394195 : Blo 346754 394195 := bstep (se 1 (by rfl) ⟨295646, by rfl⟩ : syracuseStep 394195 = 591293) B591293
theorem B525281 : Blo 346754 525281 := bstep (se 2 (by rfl) ⟨196980, by rfl⟩ : syracuseStep 525281 = 393961) B393961
theorem B787427 : Blo 346754 787427 := bstep (se 1 (by rfl) ⟨590570, by rfl⟩ : syracuseStep 787427 = 1181141) B1181141
theorem B525299 : Blo 346754 525299 := bstep (se 1 (by rfl) ⟨393974, by rfl⟩ : syracuseStep 525299 = 787949) B787949
theorem B525329 : Blo 346754 525329 := bstep (se 2 (by rfl) ⟨196998, by rfl⟩ : syracuseStep 525329 = 393997) B393997
theorem B590881 : Blo 346754 590881 := bstep (se 2 (by rfl) ⟨221580, by rfl⟩ : syracuseStep 590881 = 443161) B443161
theorem B525347 : Blo 346754 525347 := bstep (se 1 (by rfl) ⟨394010, by rfl⟩ : syracuseStep 525347 = 788021) B788021
theorem B525377 : Blo 346754 525377 := bstep (se 2 (by rfl) ⟨197016, by rfl⟩ : syracuseStep 525377 = 394033) B394033
theorem B590915 : Blo 346754 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B525395 : Blo 346754 525395 := bstep (se 1 (by rfl) ⟨394046, by rfl⟩ : syracuseStep 525395 = 788093) B788093
theorem B394339 : Blo 346754 394339 := bstep (se 1 (by rfl) ⟨295754, by rfl⟩ : syracuseStep 394339 = 591509) B591509
theorem B525425 : Blo 346754 525425 := bstep (se 2 (by rfl) ⟨197034, by rfl⟩ : syracuseStep 525425 = 394069) B394069
theorem B525443 : Blo 346754 525443 := bstep (se 1 (by rfl) ⟨394082, by rfl⟩ : syracuseStep 525443 = 788165) B788165
theorem B1180817 : Blo 346754 1180817 := bstep (se 2 (by rfl) ⟨442806, by rfl⟩ : syracuseStep 1180817 = 885613) B885613
theorem B525473 : Blo 346754 525473 := bstep (se 2 (by rfl) ⟨197052, by rfl⟩ : syracuseStep 525473 = 394105) B394105
theorem B1770659 : Blo 346754 1770659 := bstep (se 1 (by rfl) ⟨1327994, by rfl⟩ : syracuseStep 1770659 = 2655989) B2655989
theorem B885937 : Blo 346754 885937 := bstep (se 2 (by rfl) ⟨332226, by rfl⟩ : syracuseStep 885937 = 664453) B664453
theorem B525491 : Blo 346754 525491 := bstep (se 1 (by rfl) ⟨394118, by rfl⟩ : syracuseStep 525491 = 788237) B788237
theorem B591043 : Blo 346754 591043 := bstep (se 1 (by rfl) ⟨443282, by rfl⟩ : syracuseStep 591043 = 886565) B886565
theorem B525521 : Blo 346754 525521 := bstep (se 2 (by rfl) ⟨197070, by rfl⟩ : syracuseStep 525521 = 394141) B394141
theorem B525539 : Blo 346754 525539 := bstep (se 1 (by rfl) ⟨394154, by rfl⟩ : syracuseStep 525539 = 788309) B788309
theorem B787697 : Blo 346754 787697 := bstep (se 2 (by rfl) ⟨295386, by rfl⟩ : syracuseStep 787697 = 590773) B590773
theorem B394483 : Blo 346754 394483 := bstep (se 1 (by rfl) ⟨295862, by rfl⟩ : syracuseStep 394483 = 591725) B591725
theorem B525569 : Blo 346754 525569 := bstep (se 2 (by rfl) ⟨197088, by rfl⟩ : syracuseStep 525569 = 394177) B394177
theorem B787715 : Blo 346754 787715 := bstep (se 1 (by rfl) ⟨590786, by rfl⟩ : syracuseStep 787715 = 1181573) B1181573
theorem B525587 : Blo 346754 525587 := bstep (se 1 (by rfl) ⟨394190, by rfl⟩ : syracuseStep 525587 = 788381) B788381
theorem B525617 : Blo 346754 525617 := bstep (se 2 (by rfl) ⟨197106, by rfl⟩ : syracuseStep 525617 = 394213) B394213
theorem B525635 : Blo 346754 525635 := bstep (se 1 (by rfl) ⟨394226, by rfl⟩ : syracuseStep 525635 = 788453) B788453
theorem B1115473 : Blo 346754 1115473 := bstep (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) B836605
theorem B591185 : Blo 346754 591185 := bstep (se 2 (by rfl) ⟨221694, by rfl⟩ : syracuseStep 591185 = 443389) B443389
theorem B525665 : Blo 346754 525665 := bstep (se 2 (by rfl) ⟨197124, by rfl⟩ : syracuseStep 525665 = 394249) B394249
theorem B525683 : Blo 346754 525683 := bstep (se 1 (by rfl) ⟨394262, by rfl⟩ : syracuseStep 525683 = 788525) B788525
theorem B525713 : Blo 346754 525713 := bstep (se 2 (by rfl) ⟨197142, by rfl⟩ : syracuseStep 525713 = 394285) B394285
theorem B525731 : Blo 346754 525731 := bstep (se 1 (by rfl) ⟨394298, by rfl⟩ : syracuseStep 525731 = 788597) B788597
theorem B525761 : Blo 346754 525761 := bstep (se 2 (by rfl) ⟨197160, by rfl⟩ : syracuseStep 525761 = 394321) B394321
theorem B886211 : Blo 346754 886211 := bstep (se 1 (by rfl) ⟨664658, by rfl⟩ : syracuseStep 886211 = 1329317) B1329317
theorem B591313 : Blo 346754 591313 := bstep (se 2 (by rfl) ⟨221742, by rfl⟩ : syracuseStep 591313 = 443485) B443485
theorem B525779 : Blo 346754 525779 := bstep (se 1 (by rfl) ⟨394334, by rfl⟩ : syracuseStep 525779 = 788669) B788669
theorem B1344995 : Blo 346754 1344995 := bstep (se 1 (by rfl) ⟨1008746, by rfl⟩ : syracuseStep 1344995 = 2017493) B2017493
theorem B525809 : Blo 346754 525809 := bstep (se 2 (by rfl) ⟨197178, by rfl⟩ : syracuseStep 525809 = 394357) B394357
theorem B591347 : Blo 346754 591347 := bstep (se 1 (by rfl) ⟨443510, by rfl⟩ : syracuseStep 591347 = 887021) B887021
theorem B525827 : Blo 346754 525827 := bstep (se 1 (by rfl) ⟨394370, by rfl⟩ : syracuseStep 525827 = 788741) B788741
theorem B787985 : Blo 346754 787985 := bstep (se 2 (by rfl) ⟨295494, by rfl⟩ : syracuseStep 787985 = 590989) B590989
theorem B525857 : Blo 346754 525857 := bstep (se 2 (by rfl) ⟨197196, by rfl⟩ : syracuseStep 525857 = 394393) B394393
theorem B788003 : Blo 346754 788003 := bstep (se 1 (by rfl) ⟨591002, by rfl⟩ : syracuseStep 788003 = 1182005) B1182005
theorem B525875 : Blo 346754 525875 := bstep (se 1 (by rfl) ⟨394406, by rfl⟩ : syracuseStep 525875 = 788813) B788813
theorem B525905 : Blo 346754 525905 := bstep (se 2 (by rfl) ⟨197214, by rfl⟩ : syracuseStep 525905 = 394429) B394429
theorem B525923 : Blo 346754 525923 := bstep (se 1 (by rfl) ⟨394442, by rfl⟩ : syracuseStep 525923 = 788885) B788885
theorem B591475 : Blo 346754 591475 := bstep (se 1 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 591475 = 887213) B887213
theorem B525953 : Blo 346754 525953 := bstep (se 2 (by rfl) ⟨197232, by rfl⟩ : syracuseStep 525953 = 394465) B394465
theorem B886403 : Blo 346754 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B525971 : Blo 346754 525971 := bstep (se 1 (by rfl) ⟨394478, by rfl⟩ : syracuseStep 525971 = 788957) B788957
theorem B1181357 : Blo 346754 1181357 := bstep (se 3 (by rfl) ⟨221504, by rfl⟩ : syracuseStep 1181357 = 443009) B443009
theorem B526001 : Blo 346754 526001 := bstep (se 2 (by rfl) ⟨197250, by rfl⟩ : syracuseStep 526001 = 394501) B394501
theorem B526019 : Blo 346754 526019 := bstep (se 1 (by rfl) ⟨394514, by rfl⟩ : syracuseStep 526019 = 789029) B789029
theorem B526049 : Blo 346754 526049 := bstep (se 2 (by rfl) ⟨197268, by rfl⟩ : syracuseStep 526049 = 394537) B394537
theorem B1181411 : Blo 346754 1181411 := bstep (se 1 (by rfl) ⟨886058, by rfl⟩ : syracuseStep 1181411 = 1772117) B1772117
theorem B526067 : Blo 346754 526067 := bstep (se 1 (by rfl) ⟨394550, by rfl⟩ : syracuseStep 526067 = 789101) B789101
theorem B591617 : Blo 346754 591617 := bstep (se 2 (by rfl) ⟨221856, by rfl⟩ : syracuseStep 591617 = 443713) B443713
theorem B526097 : Blo 346754 526097 := bstep (se 2 (by rfl) ⟨197286, by rfl⟩ : syracuseStep 526097 = 394573) B394573
theorem B526115 : Blo 346754 526115 := bstep (se 1 (by rfl) ⟨394586, by rfl⟩ : syracuseStep 526115 = 789173) B789173
theorem B788273 : Blo 346754 788273 := bstep (se 2 (by rfl) ⟨295602, by rfl⟩ : syracuseStep 788273 = 591205) B591205
theorem B788291 : Blo 346754 788291 := bstep (se 1 (by rfl) ⟨591218, by rfl⟩ : syracuseStep 788291 = 1182437) B1182437
theorem B591745 : Blo 346754 591745 := bstep (se 2 (by rfl) ⟨221904, by rfl⟩ : syracuseStep 591745 = 443809) B443809
theorem B591779 : Blo 346754 591779 := bstep (se 1 (by rfl) ⟨443834, by rfl⟩ : syracuseStep 591779 = 887669) B887669
theorem B1771469 : Blo 346754 1771469 := bstep (se 3 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 1771469 = 664301) B664301
theorem B1181681 : Blo 346754 1181681 := bstep (se 2 (by rfl) ⟨443130, by rfl⟩ : syracuseStep 1181681 = 886261) B886261
theorem B788561 : Blo 346754 788561 := bstep (se 2 (by rfl) ⟨295710, by rfl⟩ : syracuseStep 788561 = 591421) B591421
theorem B788579 : Blo 346754 788579 := bstep (se 1 (by rfl) ⟨591434, by rfl⟩ : syracuseStep 788579 = 1182869) B1182869
theorem B3967217 : Blo 346754 3967217 := bstep (se 2 (by rfl) ⟨1487706, by rfl⟩ : syracuseStep 3967217 = 2975413) B2975413
theorem B788849 : Blo 346754 788849 := bstep (se 2 (by rfl) ⟨295818, by rfl⟩ : syracuseStep 788849 = 591637) B591637
theorem B788867 : Blo 346754 788867 := bstep (se 1 (by rfl) ⟨591650, by rfl⟩ : syracuseStep 788867 = 1183301) B1183301
theorem B559505 : Blo 346754 559505 := bstep (se 2 (by rfl) ⟨209814, by rfl⟩ : syracuseStep 559505 = 419629) B419629
theorem B1182221 : Blo 346754 1182221 := bstep (se 3 (by rfl) ⟨221666, by rfl⟩ : syracuseStep 1182221 = 443333) B443333
theorem B559633 : Blo 346754 559633 := bstep (se 2 (by rfl) ⟨209862, by rfl⟩ : syracuseStep 559633 = 419725) B419725
theorem B887345 : Blo 346754 887345 := bstep (se 2 (by rfl) ⟨332754, by rfl⟩ : syracuseStep 887345 = 665509) B665509
theorem B1182275 : Blo 346754 1182275 := bstep (se 1 (by rfl) ⟨886706, by rfl⟩ : syracuseStep 1182275 = 1773413) B1773413
theorem B887395 : Blo 346754 887395 := bstep (se 1 (by rfl) ⟨665546, by rfl⟩ : syracuseStep 887395 = 1331093) B1331093
theorem B789137 : Blo 346754 789137 := bstep (se 2 (by rfl) ⟨295926, by rfl⟩ : syracuseStep 789137 = 591853) B591853
theorem B789155 : Blo 346754 789155 := bstep (se 1 (by rfl) ⟨591866, by rfl⟩ : syracuseStep 789155 = 1183733) B1183733
theorem B494257 : Blo 346754 494257 := bstep (se 2 (by rfl) ⟨185346, by rfl⟩ : syracuseStep 494257 = 370693) B370693
theorem B887537 : Blo 346754 887537 := bstep (se 2 (by rfl) ⟨332826, by rfl⟩ : syracuseStep 887537 = 665653) B665653
theorem B494353 : Blo 346754 494353 := bstep (se 2 (by rfl) ⟨185382, by rfl⟩ : syracuseStep 494353 = 370765) B370765
theorem B1903409 : Blo 346754 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B1182545 : Blo 346754 1182545 := bstep (se 2 (by rfl) ⟨443454, by rfl⟩ : syracuseStep 1182545 = 886909) B886909
theorem B1117165 : Blo 346754 1117165 := bstep (se 3 (by rfl) ⟨209468, by rfl⟩ : syracuseStep 1117165 = 418937) B418937
theorem B2231459 : Blo 346754 2231459 := bstep (se 1 (by rfl) ⟨1673594, by rfl⟩ : syracuseStep 2231459 = 3347189) B3347189
theorem B756913 : Blo 346754 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B4754659 : Blo 346754 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B494849 : Blo 346754 494849 := bstep (se 2 (by rfl) ⟨185568, by rfl⟩ : syracuseStep 494849 = 371137) B371137
theorem B658705 : Blo 346754 658705 := bstep (se 2 (by rfl) ⟨247014, by rfl⟩ : syracuseStep 658705 = 494029) B494029
theorem B1183085 : Blo 346754 1183085 := bstep (se 3 (by rfl) ⟨221828, by rfl⟩ : syracuseStep 1183085 = 443657) B443657
theorem B1183139 : Blo 346754 1183139 := bstep (se 1 (by rfl) ⟨887354, by rfl⟩ : syracuseStep 1183139 = 1774709) B1774709
theorem B396851 : Blo 346754 396851 := bstep (se 1 (by rfl) ⟨297638, by rfl⟩ : syracuseStep 396851 = 595277) B595277
theorem B2657933 : Blo 346754 2657933 := bstep (se 3 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 2657933 = 996725) B996725
theorem B659107 : Blo 346754 659107 := bstep (se 1 (by rfl) ⟨494330, by rfl⟩ : syracuseStep 659107 = 988661) B988661
theorem B1183409 : Blo 346754 1183409 := bstep (se 2 (by rfl) ⟨443778, by rfl⟩ : syracuseStep 1183409 = 887557) B887557
theorem B659153 : Blo 346754 659153 := bstep (se 2 (by rfl) ⟨247182, by rfl⟩ : syracuseStep 659153 = 494365) B494365
theorem B560915 : Blo 346754 560915 := bstep (se 1 (by rfl) ⟨420686, by rfl⟩ : syracuseStep 560915 = 841373) B841373
theorem B561011 : Blo 346754 561011 := bstep (se 1 (by rfl) ⟨420758, by rfl⟩ : syracuseStep 561011 = 841517) B841517
theorem B561043 : Blo 346754 561043 := bstep (se 1 (by rfl) ⟨420782, by rfl⟩ : syracuseStep 561043 = 841565) B841565
theorem B659441 : Blo 346754 659441 := bstep (se 2 (by rfl) ⟨247290, by rfl⟩ : syracuseStep 659441 = 494581) B494581
theorem B1609763 : Blo 346754 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B495715 : Blo 346754 495715 := bstep (se 1 (by rfl) ⟨371786, by rfl⟩ : syracuseStep 495715 = 743573) B743573
theorem B1675363 : Blo 346754 1675363 := bstep (se 1 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 1675363 = 2513045) B2513045
theorem B528563 : Blo 346754 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B495811 : Blo 346754 495811 := bstep (se 1 (by rfl) ⟨371858, by rfl⟩ : syracuseStep 495811 = 743717) B743717
theorem B954595 : Blo 346754 954595 := bstep (se 1 (by rfl) ⟨715946, by rfl⟩ : syracuseStep 954595 = 1431893) B1431893
theorem B8556997 : Blo 346754 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B2232845 : Blo 346754 2232845 := bstep (se 3 (by rfl) ⟨418658, by rfl⟩ : syracuseStep 2232845 = 837317) B837317
theorem B594497 : Blo 346754 594497 := bstep (se 2 (by rfl) ⟨222936, by rfl⟩ : syracuseStep 594497 = 445873) B445873
theorem B627281 : Blo 346754 627281 := bstep (se 2 (by rfl) ⟨235230, by rfl⟩ : syracuseStep 627281 = 470461) B470461
theorem B496307 : Blo 346754 496307 := bstep (se 1 (by rfl) ⟨372230, by rfl⟩ : syracuseStep 496307 = 744461) B744461
theorem B660163 : Blo 346754 660163 := bstep (se 1 (by rfl) ⟨495122, by rfl⟩ : syracuseStep 660163 = 990245) B990245
theorem B1118947 : Blo 346754 1118947 := bstep (se 1 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 1118947 = 1678421) B1678421
theorem B1774385 : Blo 346754 1774385 := bstep (se 2 (by rfl) ⟨665394, by rfl⟩ : syracuseStep 1774385 = 1330789) B1330789
theorem B1414093 : Blo 346754 1414093 := bstep (se 3 (by rfl) ⟨265142, by rfl⟩ : syracuseStep 1414093 = 530285) B530285
theorem B2266061 : Blo 346754 2266061 := bstep (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) B849773
theorem B2692109 : Blo 346754 2692109 := bstep (se 3 (by rfl) ⟨504770, by rfl⟩ : syracuseStep 2692109 = 1009541) B1009541
theorem B1348643 : Blo 346754 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B529507 : Blo 346754 529507 := bstep (se 1 (by rfl) ⟨397130, by rfl⟩ : syracuseStep 529507 = 794261) B794261
theorem B660611 : Blo 346754 660611 := bstep (se 1 (by rfl) ⟨495458, by rfl⟩ : syracuseStep 660611 = 990917) B990917
theorem B1119395 : Blo 346754 1119395 := bstep (se 1 (by rfl) ⟨839546, by rfl⟩ : syracuseStep 1119395 = 1679093) B1679093
theorem B988433 : Blo 346754 988433 := bstep (se 2 (by rfl) ⟨370662, by rfl⟩ : syracuseStep 988433 = 741325) B741325
theorem B496945 : Blo 346754 496945 := bstep (se 2 (by rfl) ⟨186354, by rfl⟩ : syracuseStep 496945 = 372709) B372709
theorem B1611085 : Blo 346754 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B660899 : Blo 346754 660899 := bstep (se 1 (by rfl) ⟨495674, by rfl⟩ : syracuseStep 660899 = 991349) B991349
theorem B12719729 : Blo 346754 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B2692721 : Blo 346754 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B497281 : Blo 346754 497281 := bstep (se 2 (by rfl) ⟨186480, by rfl⟩ : syracuseStep 497281 = 372961) B372961
theorem B530401 : Blo 346754 530401 := bstep (se 2 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 530401 = 397801) B397801
theorem B1677361 : Blo 346754 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B1022051 : Blo 346754 1022051 := bstep (se 1 (by rfl) ⟨766538, by rfl⟩ : syracuseStep 1022051 = 1533077) B1533077
theorem B1054829 : Blo 346754 1054829 := bstep (se 3 (by rfl) ⟨197780, by rfl⟩ : syracuseStep 1054829 = 395561) B395561
theorem B2398349 : Blo 346754 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B2398405 : Blo 346754 2398405 := bstep (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) B449701
theorem B1054925 : Blo 346754 1054925 := bstep (se 3 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 1054925 = 395597) B395597
theorem B497873 : Blo 346754 497873 := bstep (se 2 (by rfl) ⟨186702, by rfl⟩ : syracuseStep 497873 = 373405) B373405
theorem B661841 : Blo 346754 661841 := bstep (se 2 (by rfl) ⟨248190, by rfl⟩ : syracuseStep 661841 = 496381) B496381
theorem B1120625 : Blo 346754 1120625 := bstep (se 2 (by rfl) ⟨420234, by rfl⟩ : syracuseStep 1120625 = 840469) B840469
theorem B858563 : Blo 346754 858563 := bstep (se 1 (by rfl) ⟨643922, by rfl⟩ : syracuseStep 858563 = 1287845) B1287845
theorem B3578309 : Blo 346754 3578309 := bstep (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) B670933
theorem B2660849 : Blo 346754 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B4528709 : Blo 346754 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B629329 : Blo 346754 629329 := bstep (se 2 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 629329 = 471997) B471997
theorem B989891 : Blo 346754 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B498403 : Blo 346754 498403 := bstep (se 1 (by rfl) ⟨373802, by rfl⟩ : syracuseStep 498403 = 747605) B747605
theorem B1317667 : Blo 346754 1317667 := bstep (se 1 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 1317667 = 1976501) B1976501
theorem B596899 : Blo 346754 596899 := bstep (se 1 (by rfl) ⟨447674, by rfl⟩ : syracuseStep 596899 = 895349) B895349
theorem B498739 : Blo 346754 498739 := bstep (se 1 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 498739 = 748109) B748109
theorem B5676085 : Blo 346754 5676085 := bstep (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) B532133
theorem B1678477 : Blo 346754 1678477 := bstep (se 3 (by rfl) ⟨314714, by rfl⟩ : syracuseStep 1678477 = 629429) B629429
theorem B662737 : Blo 346754 662737 := bstep (se 2 (by rfl) ⟨248526, by rfl⟩ : syracuseStep 662737 = 497053) B497053
theorem B1121521 : Blo 346754 1121521 := bstep (se 2 (by rfl) ⟨420570, by rfl⟩ : syracuseStep 1121521 = 841141) B841141
theorem B662897 : Blo 346754 662897 := bstep (se 2 (by rfl) ⟨248586, by rfl⟩ : syracuseStep 662897 = 497173) B497173
theorem B990701 : Blo 346754 990701 := bstep (se 3 (by rfl) ⟨185756, by rfl⟩ : syracuseStep 990701 = 371513) B371513
theorem B499297 : Blo 346754 499297 := bstep (se 2 (by rfl) ⟨187236, by rfl⟩ : syracuseStep 499297 = 374473) B374473
theorem B958061 : Blo 346754 958061 := bstep (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) B359273
theorem B499331 : Blo 346754 499331 := bstep (se 1 (by rfl) ⟨374498, by rfl⟩ : syracuseStep 499331 = 748997) B748997
theorem B5643917 : Blo 346754 5643917 := bstep (se 3 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 5643917 = 2116469) B2116469
theorem B990893 : Blo 346754 990893 := bstep (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) B371585
theorem B1187569 : Blo 346754 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B663299 : Blo 346754 663299 := bstep (se 1 (by rfl) ⟨497474, by rfl⟩ : syracuseStep 663299 = 994949) B994949
theorem B892721 : Blo 346754 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B4595555 : Blo 346754 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B761827 : Blo 346754 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B630929 : Blo 346754 630929 := bstep (se 2 (by rfl) ⟨236598, by rfl⟩ : syracuseStep 630929 = 473197) B473197
theorem B1253987 : Blo 346754 1253987 := bstep (se 1 (by rfl) ⟨940490, by rfl⟩ : syracuseStep 1253987 = 1880981) B1880981
theorem B664195 : Blo 346754 664195 := bstep (se 1 (by rfl) ⟨498146, by rfl⟩ : syracuseStep 664195 = 996293) B996293
theorem B991885 : Blo 346754 991885 := bstep (se 3 (by rfl) ⟨185978, by rfl⟩ : syracuseStep 991885 = 371957) B371957
theorem B1483505 : Blo 346754 1483505 := bstep (se 2 (by rfl) ⟨556314, by rfl⟩ : syracuseStep 1483505 = 1112629) B1112629
theorem B1123085 : Blo 346754 1123085 := bstep (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) B421157
theorem B664355 : Blo 346754 664355 := bstep (se 1 (by rfl) ⟨498266, by rfl⟩ : syracuseStep 664355 = 996533) B996533
theorem B598931 : Blo 346754 598931 := bstep (se 1 (by rfl) ⟨449198, by rfl⟩ : syracuseStep 598931 = 898397) B898397
theorem B1319885 : Blo 346754 1319885 := bstep (se 3 (by rfl) ⟨247478, by rfl⟩ : syracuseStep 1319885 = 494957) B494957
theorem B599233 : Blo 346754 599233 := bstep (se 2 (by rfl) ⟨224712, by rfl⟩ : syracuseStep 599233 = 449425) B449425
theorem B20194757 : Blo 346754 20194757 := bstep (se 4 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 20194757 = 3786517) B3786517
theorem B501233 : Blo 346754 501233 := bstep (se 2 (by rfl) ⟨187962, by rfl⟩ : syracuseStep 501233 = 375925) B375925
theorem B4236869 : Blo 346754 4236869 := bstep (se 4 (by rfl) ⟨397206, by rfl⟩ : syracuseStep 4236869 = 794413) B794413
theorem B1058467 : Blo 346754 1058467 := bstep (se 1 (by rfl) ⟨793850, by rfl⟩ : syracuseStep 1058467 = 1587701) B1587701
theorem B3352261 : Blo 346754 3352261 := bstep (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) B628549
theorem B403219 : Blo 346754 403219 := bstep (se 1 (by rfl) ⟨302414, by rfl⟩ : syracuseStep 403219 = 604829) B604829
theorem B468785 : Blo 346754 468785 := bstep (se 2 (by rfl) ⟨175794, by rfl⟩ : syracuseStep 468785 = 351589) B351589
theorem B665425 : Blo 346754 665425 := bstep (se 2 (by rfl) ⟨249534, by rfl⟩ : syracuseStep 665425 = 499069) B499069
theorem B567233 : Blo 346754 567233 := bstep (se 2 (by rfl) ⟨212712, by rfl⟩ : syracuseStep 567233 = 425425) B425425
theorem B1255601 : Blo 346754 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B1255715 : Blo 346754 1255715 := bstep (se 1 (by rfl) ⟨941786, by rfl⟩ : syracuseStep 1255715 = 1883573) B1883573
theorem B469315 : Blo 346754 469315 := bstep (se 1 (by rfl) ⟨351986, by rfl⟩ : syracuseStep 469315 = 703973) B703973
theorem B993617 : Blo 346754 993617 := bstep (se 2 (by rfl) ⟨372606, by rfl⟩ : syracuseStep 993617 = 745213) B745213
theorem B567713 : Blo 346754 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B993809 : Blo 346754 993809 := bstep (se 2 (by rfl) ⟨372678, by rfl⟩ : syracuseStep 993809 = 745357) B745357
theorem B371363 : Blo 346754 371363 := bstep (se 1 (by rfl) ⟨278522, by rfl⟩ : syracuseStep 371363 = 557045) B557045
theorem B2992909 : Blo 346754 2992909 := bstep (se 3 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 2992909 = 1122341) B1122341
theorem B797617 : Blo 346754 797617 := bstep (se 2 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 797617 = 598213) B598213
theorem B502849 : Blo 346754 502849 := bstep (se 2 (by rfl) ⟨188568, by rfl⟩ : syracuseStep 502849 = 377137) B377137
theorem B1485965 : Blo 346754 1485965 := bstep (se 3 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 1485965 = 557237) B557237
theorem B1584305 : Blo 346754 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B2829509 : Blo 346754 2829509 := bstep (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) B530533
theorem B798083 : Blo 346754 798083 := bstep (se 1 (by rfl) ⟨598562, by rfl⟩ : syracuseStep 798083 = 1197125) B1197125
theorem B372115 : Blo 346754 372115 := bstep (se 1 (by rfl) ⟨279086, by rfl⟩ : syracuseStep 372115 = 558173) B558173
theorem B994801 : Blo 346754 994801 := bstep (se 2 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 994801 = 746101) B746101
theorem B372371 : Blo 346754 372371 := bstep (se 1 (by rfl) ⟨279278, by rfl⟩ : syracuseStep 372371 = 558557) B558557
theorem B995075 : Blo 346754 995075 := bstep (se 1 (by rfl) ⟨746306, by rfl⟩ : syracuseStep 995075 = 1492613) B1492613
theorem B1322801 : Blo 346754 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B1257329 : Blo 346754 1257329 := bstep (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) B942997
theorem B995267 : Blo 346754 995267 := bstep (se 1 (by rfl) ⟨746450, by rfl⟩ : syracuseStep 995267 = 1492901) B1492901
theorem B2994245 : Blo 346754 2994245 := bstep (se 4 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 2994245 = 561421) B561421
theorem B1257677 : Blo 346754 1257677 := bstep (se 3 (by rfl) ⟨235814, by rfl⟩ : syracuseStep 1257677 = 471629) B471629
theorem B1880333 : Blo 346754 1880333 := bstep (se 3 (by rfl) ⟨352562, by rfl⟩ : syracuseStep 1880333 = 705125) B705125
theorem B602417 : Blo 346754 602417 := bstep (se 2 (by rfl) ⟨225906, by rfl⟩ : syracuseStep 602417 = 451813) B451813
theorem B373123 : Blo 346754 373123 := bstep (se 1 (by rfl) ⟨279842, by rfl⟩ : syracuseStep 373123 = 559685) B559685
theorem B1126801 : Blo 346754 1126801 := bstep (se 2 (by rfl) ⟨422550, by rfl⟩ : syracuseStep 1126801 = 845101) B845101
theorem B1487281 : Blo 346754 1487281 := bstep (se 2 (by rfl) ⟨557730, by rfl⟩ : syracuseStep 1487281 = 1115461) B1115461
theorem B471521 : Blo 346754 471521 := bstep (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) B353641
theorem B1585763 : Blo 346754 1585763 := bstep (se 1 (by rfl) ⟨1189322, by rfl⟩ : syracuseStep 1585763 = 2378645) B2378645
theorem B4239985 : Blo 346754 4239985 := bstep (se 2 (by rfl) ⟨1589994, by rfl⟩ : syracuseStep 4239985 = 3179989) B3179989
theorem B1880803 : Blo 346754 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B996077 : Blo 346754 996077 := bstep (se 3 (by rfl) ⟨186764, by rfl⟩ : syracuseStep 996077 = 373529) B373529
theorem B537377 : Blo 346754 537377 := bstep (se 2 (by rfl) ⟨201516, by rfl⟩ : syracuseStep 537377 = 403033) B403033
theorem B3191665 : Blo 346754 3191665 := bstep (se 2 (by rfl) ⟨1196874, by rfl⟩ : syracuseStep 3191665 = 2393749) B2393749
theorem B996259 : Blo 346754 996259 := bstep (se 1 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 996259 = 1494389) B1494389
theorem B439283 : Blo 346754 439283 := bstep (se 1 (by rfl) ⟨329462, by rfl⟩ : syracuseStep 439283 = 658925) B658925
theorem B1324259 : Blo 346754 1324259 := bstep (se 1 (by rfl) ⟨993194, by rfl⟩ : syracuseStep 1324259 = 1986389) B1986389
theorem B1881413 : Blo 346754 1881413 := bstep (se 4 (by rfl) ⟨176382, by rfl⟩ : syracuseStep 1881413 = 352765) B352765
theorem B996749 : Blo 346754 996749 := bstep (se 3 (by rfl) ⟨186890, by rfl⟩ : syracuseStep 996749 = 373781) B373781
theorem B374387 : Blo 346754 374387 := bstep (se 1 (by rfl) ⟨280790, by rfl⟩ : syracuseStep 374387 = 561581) B561581
theorem B2733709 : Blo 346754 2733709 := bstep (se 3 (by rfl) ⟨512570, by rfl⟩ : syracuseStep 2733709 = 1025141) B1025141
theorem B439987 : Blo 346754 439987 := bstep (se 1 (by rfl) ⟨329990, by rfl⟩ : syracuseStep 439987 = 659981) B659981
theorem B440083 : Blo 346754 440083 := bstep (se 1 (by rfl) ⟨330062, by rfl⟩ : syracuseStep 440083 = 660125) B660125
theorem B1259405 : Blo 346754 1259405 := bstep (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) B472277
theorem B1980557 : Blo 346754 1980557 := bstep (se 3 (by rfl) ⟨371354, by rfl⟩ : syracuseStep 1980557 = 742709) B742709
theorem B1325261 : Blo 346754 1325261 := bstep (se 3 (by rfl) ⟨248486, by rfl⟩ : syracuseStep 1325261 = 496973) B496973
theorem B440579 : Blo 346754 440579 := bstep (se 1 (by rfl) ⟨330434, by rfl⟩ : syracuseStep 440579 = 660869) B660869
theorem B997933 : Blo 346754 997933 := bstep (se 3 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 997933 = 374225) B374225
theorem B441283 : Blo 346754 441283 := bstep (se 1 (by rfl) ⟨330962, by rfl⟩ : syracuseStep 441283 = 661925) B661925
theorem B441379 : Blo 346754 441379 := bstep (se 1 (by rfl) ⟨331034, by rfl⟩ : syracuseStep 441379 = 662069) B662069
theorem B1490339 : Blo 346754 1490339 := bstep (se 1 (by rfl) ⟨1117754, by rfl⟩ : syracuseStep 1490339 = 2235509) B2235509
theorem B2112965 : Blo 346754 2112965 := bstep (se 4 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 2112965 = 396181) B396181
theorem B441875 : Blo 346754 441875 := bstep (se 1 (by rfl) ⟨331406, by rfl⟩ : syracuseStep 441875 = 662813) B662813
theorem B1064497 : Blo 346754 1064497 := bstep (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) B798373
theorem B2014789 : Blo 346754 2014789 := bstep (se 4 (by rfl) ⟨188886, by rfl⟩ : syracuseStep 2014789 = 377773) B377773
theorem B1392419 : Blo 346754 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B1065059 : Blo 346754 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B442579 : Blo 346754 442579 := bstep (se 1 (by rfl) ⟨331934, by rfl⟩ : syracuseStep 442579 = 663869) B663869
theorem B2507021 : Blo 346754 2507021 := bstep (se 3 (by rfl) ⟨470066, by rfl⟩ : syracuseStep 2507021 = 940133) B940133
theorem B1327373 : Blo 346754 1327373 := bstep (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) B497765
theorem B8962325 : Blo 346754 8962325 := bstep (se 6 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 8962325 = 420109) B420109
theorem B442675 : Blo 346754 442675 := bstep (se 1 (by rfl) ⟨332006, by rfl⟩ : syracuseStep 442675 = 664013) B664013
theorem B1982789 : Blo 346754 1982789 := bstep (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) B371773
theorem B2244941 : Blo 346754 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B737777 : Blo 346754 737777 := bstep (se 2 (by rfl) ⟨276666, by rfl⟩ : syracuseStep 737777 = 553333) B553333
theorem B443171 : Blo 346754 443171 := bstep (se 1 (by rfl) ⟨332378, by rfl⟩ : syracuseStep 443171 = 664757) B664757
theorem B672689 : Blo 346754 672689 := bstep (se 2 (by rfl) ⟨252258, by rfl⟩ : syracuseStep 672689 = 504517) B504517
theorem B2114545 : Blo 346754 2114545 := bstep (se 2 (by rfl) ⟨792954, by rfl⟩ : syracuseStep 2114545 = 1585909) B1585909
theorem B1983473 : Blo 346754 1983473 := bstep (se 2 (by rfl) ⟨743802, by rfl⟩ : syracuseStep 1983473 = 1487605) B1487605
theorem B1328177 : Blo 346754 1328177 := bstep (se 2 (by rfl) ⟨498066, by rfl⟩ : syracuseStep 1328177 = 996133) B996133
theorem B377971 : Blo 346754 377971 := bstep (se 1 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 377971 = 566957) B566957
theorem B1524977 : Blo 346754 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B1066321 : Blo 346754 1066321 := bstep (se 2 (by rfl) ⟨399870, by rfl⟩ : syracuseStep 1066321 = 799741) B799741
theorem B607651 : Blo 346754 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B443875 : Blo 346754 443875 := bstep (se 1 (by rfl) ⟨332906, by rfl⟩ : syracuseStep 443875 = 665813) B665813
theorem B1328845 : Blo 346754 1328845 := bstep (se 3 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 1328845 = 498317) B498317
theorem B3197069 : Blo 346754 3197069 := bstep (se 3 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 3197069 = 1198901) B1198901
theorem B837827 : Blo 346754 837827 := bstep (se 1 (by rfl) ⟨628370, by rfl⟩ : syracuseStep 837827 = 1256741) B1256741
theorem B1984931 : Blo 346754 1984931 := bstep (se 1 (by rfl) ⟨1488698, by rfl⟩ : syracuseStep 1984931 = 2977397) B2977397
theorem B1329635 : Blo 346754 1329635 := bstep (se 1 (by rfl) ⟨997226, by rfl⟩ : syracuseStep 1329635 = 1994453) B1994453
theorem B346755 : Blo 346754 346755 := bstep (se 1 (by rfl) ⟨260066, by rfl⟩ : syracuseStep 346755 = 520133) B520133
theorem B346771 : Blo 346754 346771 := bstep (se 1 (by rfl) ⟨260078, by rfl⟩ : syracuseStep 346771 = 520157) B520157
theorem B346787 : Blo 346754 346787 := bstep (se 1 (by rfl) ⟨260090, by rfl⟩ : syracuseStep 346787 = 520181) B520181
theorem B346803 : Blo 346754 346803 := bstep (se 1 (by rfl) ⟨260102, by rfl⟩ : syracuseStep 346803 = 520205) B520205
theorem B346819 : Blo 346754 346819 := bstep (se 1 (by rfl) ⟨260114, by rfl⟩ : syracuseStep 346819 = 520229) B520229
theorem B346835 : Blo 346754 346835 := bstep (se 1 (by rfl) ⟨260126, by rfl⟩ : syracuseStep 346835 = 520253) B520253
theorem B346851 : Blo 346754 346851 := bstep (se 1 (by rfl) ⟨260138, by rfl⟩ : syracuseStep 346851 = 520277) B520277
theorem B346867 : Blo 346754 346867 := bstep (se 1 (by rfl) ⟨260150, by rfl⟩ : syracuseStep 346867 = 520301) B520301
theorem B346883 : Blo 346754 346883 := bstep (se 1 (by rfl) ⟨260162, by rfl⟩ : syracuseStep 346883 = 520325) B520325
theorem B1755917 : Blo 346754 1755917 := bstep (se 3 (by rfl) ⟨329234, by rfl⟩ : syracuseStep 1755917 = 658469) B658469
theorem B346899 : Blo 346754 346899 := bstep (se 1 (by rfl) ⟨260174, by rfl⟩ : syracuseStep 346899 = 520349) B520349
theorem B346915 : Blo 346754 346915 := bstep (se 1 (by rfl) ⟨260186, by rfl⟩ : syracuseStep 346915 = 520373) B520373
theorem B346931 : Blo 346754 346931 := bstep (se 1 (by rfl) ⟨260198, by rfl⟩ : syracuseStep 346931 = 520397) B520397
theorem B346947 : Blo 346754 346947 := bstep (se 1 (by rfl) ⟨260210, by rfl⟩ : syracuseStep 346947 = 520421) B520421
theorem B346963 : Blo 346754 346963 := bstep (se 1 (by rfl) ⟨260222, by rfl⟩ : syracuseStep 346963 = 520445) B520445
theorem B346979 : Blo 346754 346979 := bstep (se 1 (by rfl) ⟨260234, by rfl⟩ : syracuseStep 346979 = 520469) B520469
theorem B346995 : Blo 346754 346995 := bstep (se 1 (by rfl) ⟨260246, by rfl⟩ : syracuseStep 346995 = 520493) B520493
theorem B347011 : Blo 346754 347011 := bstep (se 1 (by rfl) ⟨260258, by rfl⟩ : syracuseStep 347011 = 520517) B520517
theorem B347027 : Blo 346754 347027 := bstep (se 1 (by rfl) ⟨260270, by rfl⟩ : syracuseStep 347027 = 520541) B520541
theorem B347043 : Blo 346754 347043 := bstep (se 1 (by rfl) ⟨260282, by rfl⟩ : syracuseStep 347043 = 520565) B520565
theorem B347059 : Blo 346754 347059 := bstep (se 1 (by rfl) ⟨260294, by rfl⟩ : syracuseStep 347059 = 520589) B520589
theorem B347075 : Blo 346754 347075 := bstep (se 1 (by rfl) ⟨260306, by rfl⟩ : syracuseStep 347075 = 520613) B520613
theorem B347091 : Blo 346754 347091 := bstep (se 1 (by rfl) ⟨260318, by rfl⟩ : syracuseStep 347091 = 520637) B520637
theorem B347107 : Blo 346754 347107 := bstep (se 1 (by rfl) ⟨260330, by rfl⟩ : syracuseStep 347107 = 520661) B520661
theorem B347123 : Blo 346754 347123 := bstep (se 1 (by rfl) ⟨260342, by rfl⟩ : syracuseStep 347123 = 520685) B520685
theorem B347139 : Blo 346754 347139 := bstep (se 1 (by rfl) ⟨260354, by rfl⟩ : syracuseStep 347139 = 520709) B520709
theorem B347155 : Blo 346754 347155 := bstep (se 1 (by rfl) ⟨260366, by rfl⟩ : syracuseStep 347155 = 520733) B520733
theorem B347171 : Blo 346754 347171 := bstep (se 1 (by rfl) ⟨260378, by rfl⟩ : syracuseStep 347171 = 520757) B520757
theorem B347187 : Blo 346754 347187 := bstep (se 1 (by rfl) ⟨260390, by rfl⟩ : syracuseStep 347187 = 520781) B520781
theorem B347203 : Blo 346754 347203 := bstep (se 1 (by rfl) ⟨260402, by rfl⟩ : syracuseStep 347203 = 520805) B520805
theorem B347219 : Blo 346754 347219 := bstep (se 1 (by rfl) ⟨260414, by rfl⟩ : syracuseStep 347219 = 520829) B520829
theorem B347235 : Blo 346754 347235 := bstep (se 1 (by rfl) ⟨260426, by rfl⟩ : syracuseStep 347235 = 520853) B520853
theorem B1330289 : Blo 346754 1330289 := bstep (se 2 (by rfl) ⟨498858, by rfl⟩ : syracuseStep 1330289 = 997717) B997717
theorem B347251 : Blo 346754 347251 := bstep (se 1 (by rfl) ⟨260438, by rfl⟩ : syracuseStep 347251 = 520877) B520877
theorem B347267 : Blo 346754 347267 := bstep (se 1 (by rfl) ⟨260450, by rfl⟩ : syracuseStep 347267 = 520901) B520901
theorem B5786765 : Blo 346754 5786765 := bstep (se 3 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 5786765 = 2170037) B2170037
theorem B347283 : Blo 346754 347283 := bstep (se 1 (by rfl) ⟨260462, by rfl⟩ : syracuseStep 347283 = 520925) B520925
theorem B347299 : Blo 346754 347299 := bstep (se 1 (by rfl) ⟨260474, by rfl⟩ : syracuseStep 347299 = 520949) B520949
theorem B347315 : Blo 346754 347315 := bstep (se 1 (by rfl) ⟨260486, by rfl⟩ : syracuseStep 347315 = 520973) B520973
theorem B347331 : Blo 346754 347331 := bstep (se 1 (by rfl) ⟨260498, by rfl⟩ : syracuseStep 347331 = 520997) B520997
theorem B347347 : Blo 346754 347347 := bstep (se 1 (by rfl) ⟨260510, by rfl⟩ : syracuseStep 347347 = 521021) B521021
theorem B347363 : Blo 346754 347363 := bstep (se 1 (by rfl) ⟨260522, by rfl⟩ : syracuseStep 347363 = 521045) B521045
theorem B347379 : Blo 346754 347379 := bstep (se 1 (by rfl) ⟨260534, by rfl⟩ : syracuseStep 347379 = 521069) B521069
theorem B347395 : Blo 346754 347395 := bstep (se 1 (by rfl) ⟨260546, by rfl⟩ : syracuseStep 347395 = 521093) B521093
theorem B347411 : Blo 346754 347411 := bstep (se 1 (by rfl) ⟨260558, by rfl⟩ : syracuseStep 347411 = 521117) B521117
theorem B347427 : Blo 346754 347427 := bstep (se 1 (by rfl) ⟨260570, by rfl⟩ : syracuseStep 347427 = 521141) B521141
theorem B347443 : Blo 346754 347443 := bstep (se 1 (by rfl) ⟨260582, by rfl⟩ : syracuseStep 347443 = 521165) B521165
theorem B347459 : Blo 346754 347459 := bstep (se 1 (by rfl) ⟨260594, by rfl⟩ : syracuseStep 347459 = 521189) B521189
theorem B347475 : Blo 346754 347475 := bstep (se 1 (by rfl) ⟨260606, by rfl⟩ : syracuseStep 347475 = 521213) B521213
theorem B347491 : Blo 346754 347491 := bstep (se 1 (by rfl) ⟨260618, by rfl⟩ : syracuseStep 347491 = 521237) B521237
theorem B347507 : Blo 346754 347507 := bstep (se 1 (by rfl) ⟨260630, by rfl⟩ : syracuseStep 347507 = 521261) B521261
theorem B347523 : Blo 346754 347523 := bstep (se 1 (by rfl) ⟨260642, by rfl⟩ : syracuseStep 347523 = 521285) B521285
theorem B347539 : Blo 346754 347539 := bstep (se 1 (by rfl) ⟨260654, by rfl⟩ : syracuseStep 347539 = 521309) B521309
theorem B347555 : Blo 346754 347555 := bstep (se 1 (by rfl) ⟨260666, by rfl⟩ : syracuseStep 347555 = 521333) B521333
theorem B347571 : Blo 346754 347571 := bstep (se 1 (by rfl) ⟨260678, by rfl⟩ : syracuseStep 347571 = 521357) B521357
theorem B347587 : Blo 346754 347587 := bstep (se 1 (by rfl) ⟨260690, by rfl⟩ : syracuseStep 347587 = 521381) B521381
theorem B347603 : Blo 346754 347603 := bstep (se 1 (by rfl) ⟨260702, by rfl⟩ : syracuseStep 347603 = 521405) B521405
theorem B347619 : Blo 346754 347619 := bstep (se 1 (by rfl) ⟨260714, by rfl⟩ : syracuseStep 347619 = 521429) B521429
theorem B347635 : Blo 346754 347635 := bstep (se 1 (by rfl) ⟨260726, by rfl⟩ : syracuseStep 347635 = 521453) B521453
theorem B347651 : Blo 346754 347651 := bstep (se 1 (by rfl) ⟨260738, by rfl⟩ : syracuseStep 347651 = 521477) B521477
theorem B1494541 : Blo 346754 1494541 := bstep (se 3 (by rfl) ⟨280226, by rfl⟩ : syracuseStep 1494541 = 560453) B560453
theorem B347667 : Blo 346754 347667 := bstep (se 1 (by rfl) ⟨260750, by rfl⟩ : syracuseStep 347667 = 521501) B521501
theorem B347683 : Blo 346754 347683 := bstep (se 1 (by rfl) ⟨260762, by rfl⟩ : syracuseStep 347683 = 521525) B521525
theorem B347699 : Blo 346754 347699 := bstep (se 1 (by rfl) ⟨260774, by rfl⟩ : syracuseStep 347699 = 521549) B521549
theorem B347715 : Blo 346754 347715 := bstep (se 1 (by rfl) ⟨260786, by rfl⟩ : syracuseStep 347715 = 521573) B521573
theorem B347731 : Blo 346754 347731 := bstep (se 1 (by rfl) ⟨260798, by rfl⟩ : syracuseStep 347731 = 521597) B521597
theorem B347747 : Blo 346754 347747 := bstep (se 1 (by rfl) ⟨260810, by rfl⟩ : syracuseStep 347747 = 521621) B521621
theorem B347763 : Blo 346754 347763 := bstep (se 1 (by rfl) ⟨260822, by rfl⟩ : syracuseStep 347763 = 521645) B521645
theorem B347779 : Blo 346754 347779 := bstep (se 1 (by rfl) ⟨260834, by rfl⟩ : syracuseStep 347779 = 521669) B521669
theorem B1887877 : Blo 346754 1887877 := bstep (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) B353977
theorem B347795 : Blo 346754 347795 := bstep (se 1 (by rfl) ⟨260846, by rfl⟩ : syracuseStep 347795 = 521693) B521693
theorem B347811 : Blo 346754 347811 := bstep (se 1 (by rfl) ⟨260858, by rfl⟩ : syracuseStep 347811 = 521717) B521717
theorem B347827 : Blo 346754 347827 := bstep (se 1 (by rfl) ⟨260870, by rfl⟩ : syracuseStep 347827 = 521741) B521741
theorem B347843 : Blo 346754 347843 := bstep (se 1 (by rfl) ⟨260882, by rfl⟩ : syracuseStep 347843 = 521765) B521765
theorem B3460805 : Blo 346754 3460805 := bstep (se 4 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 3460805 = 648901) B648901
theorem B347859 : Blo 346754 347859 := bstep (se 1 (by rfl) ⟨260894, by rfl⟩ : syracuseStep 347859 = 521789) B521789
theorem B347875 : Blo 346754 347875 := bstep (se 1 (by rfl) ⟨260906, by rfl⟩ : syracuseStep 347875 = 521813) B521813
theorem B347891 : Blo 346754 347891 := bstep (se 1 (by rfl) ⟨260918, by rfl⟩ : syracuseStep 347891 = 521837) B521837
theorem B347907 : Blo 346754 347907 := bstep (se 1 (by rfl) ⟨260930, by rfl⟩ : syracuseStep 347907 = 521861) B521861
theorem B347923 : Blo 346754 347923 := bstep (se 1 (by rfl) ⟨260942, by rfl⟩ : syracuseStep 347923 = 521885) B521885
theorem B347939 : Blo 346754 347939 := bstep (se 1 (by rfl) ⟨260954, by rfl⟩ : syracuseStep 347939 = 521909) B521909
theorem B347955 : Blo 346754 347955 := bstep (se 1 (by rfl) ⟨260966, by rfl⟩ : syracuseStep 347955 = 521933) B521933
theorem B347971 : Blo 346754 347971 := bstep (se 1 (by rfl) ⟨260978, by rfl⟩ : syracuseStep 347971 = 521957) B521957
theorem B347987 : Blo 346754 347987 := bstep (se 1 (by rfl) ⟨260990, by rfl⟩ : syracuseStep 347987 = 521981) B521981
theorem B348003 : Blo 346754 348003 := bstep (se 1 (by rfl) ⟨261002, by rfl⟩ : syracuseStep 348003 = 522005) B522005
theorem B348019 : Blo 346754 348019 := bstep (se 1 (by rfl) ⟨261014, by rfl⟩ : syracuseStep 348019 = 522029) B522029
theorem B348035 : Blo 346754 348035 := bstep (se 1 (by rfl) ⟨261026, by rfl⟩ : syracuseStep 348035 = 522053) B522053
theorem B348051 : Blo 346754 348051 := bstep (se 1 (by rfl) ⟨261038, by rfl⟩ : syracuseStep 348051 = 522077) B522077
theorem B348067 : Blo 346754 348067 := bstep (se 1 (by rfl) ⟨261050, by rfl⟩ : syracuseStep 348067 = 522101) B522101
theorem B348083 : Blo 346754 348083 := bstep (se 1 (by rfl) ⟨261062, by rfl⟩ : syracuseStep 348083 = 522125) B522125
theorem B348099 : Blo 346754 348099 := bstep (se 1 (by rfl) ⟨261074, by rfl⟩ : syracuseStep 348099 = 522149) B522149
theorem B348115 : Blo 346754 348115 := bstep (se 1 (by rfl) ⟨261086, by rfl⟩ : syracuseStep 348115 = 522173) B522173
theorem B348131 : Blo 346754 348131 := bstep (se 1 (by rfl) ⟨261098, by rfl⟩ : syracuseStep 348131 = 522197) B522197
theorem B348147 : Blo 346754 348147 := bstep (se 1 (by rfl) ⟨261110, by rfl⟩ : syracuseStep 348147 = 522221) B522221
theorem B348163 : Blo 346754 348163 := bstep (se 1 (by rfl) ⟨261122, by rfl⟩ : syracuseStep 348163 = 522245) B522245
theorem B348179 : Blo 346754 348179 := bstep (se 1 (by rfl) ⟨261134, by rfl⟩ : syracuseStep 348179 = 522269) B522269
theorem B348195 : Blo 346754 348195 := bstep (se 1 (by rfl) ⟨261146, by rfl⟩ : syracuseStep 348195 = 522293) B522293
theorem B348211 : Blo 346754 348211 := bstep (se 1 (by rfl) ⟨261158, by rfl⟩ : syracuseStep 348211 = 522317) B522317
theorem B348227 : Blo 346754 348227 := bstep (se 1 (by rfl) ⟨261170, by rfl⟩ : syracuseStep 348227 = 522341) B522341
theorem B348243 : Blo 346754 348243 := bstep (se 1 (by rfl) ⟨261182, by rfl⟩ : syracuseStep 348243 = 522365) B522365
theorem B348259 : Blo 346754 348259 := bstep (se 1 (by rfl) ⟨261194, by rfl⟩ : syracuseStep 348259 = 522389) B522389
theorem B348275 : Blo 346754 348275 := bstep (se 1 (by rfl) ⟨261206, by rfl⟩ : syracuseStep 348275 = 522413) B522413
theorem B348291 : Blo 346754 348291 := bstep (se 1 (by rfl) ⟨261218, by rfl⟩ : syracuseStep 348291 = 522437) B522437
theorem B348307 : Blo 346754 348307 := bstep (se 1 (by rfl) ⟨261230, by rfl⟩ : syracuseStep 348307 = 522461) B522461
theorem B348323 : Blo 346754 348323 := bstep (se 1 (by rfl) ⟨261242, by rfl⟩ : syracuseStep 348323 = 522485) B522485
theorem B348339 : Blo 346754 348339 := bstep (se 1 (by rfl) ⟨261254, by rfl⟩ : syracuseStep 348339 = 522509) B522509
theorem B348355 : Blo 346754 348355 := bstep (se 1 (by rfl) ⟨261266, by rfl⟩ : syracuseStep 348355 = 522533) B522533
theorem B348371 : Blo 346754 348371 := bstep (se 1 (by rfl) ⟨261278, by rfl⟩ : syracuseStep 348371 = 522557) B522557
theorem B348387 : Blo 346754 348387 := bstep (se 1 (by rfl) ⟨261290, by rfl⟩ : syracuseStep 348387 = 522581) B522581
theorem B348403 : Blo 346754 348403 := bstep (se 1 (by rfl) ⟨261302, by rfl⟩ : syracuseStep 348403 = 522605) B522605
theorem B348419 : Blo 346754 348419 := bstep (se 1 (by rfl) ⟨261314, by rfl⟩ : syracuseStep 348419 = 522629) B522629
theorem B348435 : Blo 346754 348435 := bstep (se 1 (by rfl) ⟨261326, by rfl⟩ : syracuseStep 348435 = 522653) B522653
theorem B348451 : Blo 346754 348451 := bstep (se 1 (by rfl) ⟨261338, by rfl⟩ : syracuseStep 348451 = 522677) B522677
theorem B348467 : Blo 346754 348467 := bstep (se 1 (by rfl) ⟨261350, by rfl⟩ : syracuseStep 348467 = 522701) B522701
theorem B348483 : Blo 346754 348483 := bstep (se 1 (by rfl) ⟨261362, by rfl⟩ : syracuseStep 348483 = 522725) B522725
theorem B1888589 : Blo 346754 1888589 := bstep (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) B708221
theorem B348499 : Blo 346754 348499 := bstep (se 1 (by rfl) ⟨261374, by rfl⟩ : syracuseStep 348499 = 522749) B522749
theorem B348515 : Blo 346754 348515 := bstep (se 1 (by rfl) ⟨261386, by rfl⟩ : syracuseStep 348515 = 522773) B522773
theorem B348531 : Blo 346754 348531 := bstep (se 1 (by rfl) ⟨261398, by rfl⟩ : syracuseStep 348531 = 522797) B522797
theorem B348547 : Blo 346754 348547 := bstep (se 1 (by rfl) ⟨261410, by rfl⟩ : syracuseStep 348547 = 522821) B522821
theorem B348563 : Blo 346754 348563 := bstep (se 1 (by rfl) ⟨261422, by rfl⟩ : syracuseStep 348563 = 522845) B522845
theorem B348579 : Blo 346754 348579 := bstep (se 1 (by rfl) ⟨261434, by rfl⟩ : syracuseStep 348579 = 522869) B522869
theorem B938413 : Blo 346754 938413 := bstep (se 3 (by rfl) ⟨175952, by rfl⟩ : syracuseStep 938413 = 351905) B351905
theorem B348595 : Blo 346754 348595 := bstep (se 1 (by rfl) ⟨261446, by rfl⟩ : syracuseStep 348595 = 522893) B522893
theorem B348611 : Blo 346754 348611 := bstep (se 1 (by rfl) ⟨261458, by rfl⟩ : syracuseStep 348611 = 522917) B522917
theorem B348627 : Blo 346754 348627 := bstep (se 1 (by rfl) ⟨261470, by rfl⟩ : syracuseStep 348627 = 522941) B522941
theorem B348643 : Blo 346754 348643 := bstep (se 1 (by rfl) ⟨261482, by rfl⟩ : syracuseStep 348643 = 522965) B522965
theorem B348659 : Blo 346754 348659 := bstep (se 1 (by rfl) ⟨261494, by rfl⟩ : syracuseStep 348659 = 522989) B522989
theorem B348675 : Blo 346754 348675 := bstep (se 1 (by rfl) ⟨261506, by rfl⟩ : syracuseStep 348675 = 523013) B523013
theorem B348691 : Blo 346754 348691 := bstep (se 1 (by rfl) ⟨261518, by rfl⟩ : syracuseStep 348691 = 523037) B523037
theorem B348707 : Blo 346754 348707 := bstep (se 1 (by rfl) ⟨261530, by rfl⟩ : syracuseStep 348707 = 523061) B523061
theorem B1331747 : Blo 346754 1331747 := bstep (se 1 (by rfl) ⟨998810, by rfl⟩ : syracuseStep 1331747 = 1997621) B1997621
theorem B1331761 : Blo 346754 1331761 := bstep (se 2 (by rfl) ⟨499410, by rfl⟩ : syracuseStep 1331761 = 998821) B998821
theorem B348723 : Blo 346754 348723 := bstep (se 1 (by rfl) ⟨261542, by rfl⟩ : syracuseStep 348723 = 523085) B523085
theorem B348739 : Blo 346754 348739 := bstep (se 1 (by rfl) ⟨261554, by rfl⟩ : syracuseStep 348739 = 523109) B523109
theorem B348755 : Blo 346754 348755 := bstep (se 1 (by rfl) ⟨261566, by rfl⟩ : syracuseStep 348755 = 523133) B523133
theorem B348771 : Blo 346754 348771 := bstep (se 1 (by rfl) ⟨261578, by rfl⟩ : syracuseStep 348771 = 523157) B523157
theorem B348787 : Blo 346754 348787 := bstep (se 1 (by rfl) ⟨261590, by rfl⟩ : syracuseStep 348787 = 523181) B523181
theorem B348803 : Blo 346754 348803 := bstep (se 1 (by rfl) ⟨261602, by rfl⟩ : syracuseStep 348803 = 523205) B523205
theorem B348819 : Blo 346754 348819 := bstep (se 1 (by rfl) ⟨261614, by rfl⟩ : syracuseStep 348819 = 523229) B523229
theorem B348835 : Blo 346754 348835 := bstep (se 1 (by rfl) ⟨261626, by rfl⟩ : syracuseStep 348835 = 523253) B523253
theorem B348851 : Blo 346754 348851 := bstep (se 1 (by rfl) ⟨261638, by rfl⟩ : syracuseStep 348851 = 523277) B523277
theorem B348867 : Blo 346754 348867 := bstep (se 1 (by rfl) ⟨261650, by rfl⟩ : syracuseStep 348867 = 523301) B523301
theorem B348883 : Blo 346754 348883 := bstep (se 1 (by rfl) ⟨261662, by rfl⟩ : syracuseStep 348883 = 523325) B523325
theorem B348899 : Blo 346754 348899 := bstep (se 1 (by rfl) ⟨261674, by rfl⟩ : syracuseStep 348899 = 523349) B523349
theorem B348915 : Blo 346754 348915 := bstep (se 1 (by rfl) ⟨261686, by rfl⟩ : syracuseStep 348915 = 523373) B523373
theorem B348931 : Blo 346754 348931 := bstep (se 1 (by rfl) ⟨261698, by rfl⟩ : syracuseStep 348931 = 523397) B523397
theorem B348947 : Blo 346754 348947 := bstep (se 1 (by rfl) ⟨261710, by rfl⟩ : syracuseStep 348947 = 523421) B523421
theorem B348963 : Blo 346754 348963 := bstep (se 1 (by rfl) ⟨261722, by rfl⟩ : syracuseStep 348963 = 523445) B523445
theorem B348979 : Blo 346754 348979 := bstep (se 1 (by rfl) ⟨261734, by rfl⟩ : syracuseStep 348979 = 523469) B523469
theorem B348995 : Blo 346754 348995 := bstep (se 1 (by rfl) ⟨261746, by rfl⟩ : syracuseStep 348995 = 523493) B523493
theorem B349011 : Blo 346754 349011 := bstep (se 1 (by rfl) ⟨261758, by rfl⟩ : syracuseStep 349011 = 523517) B523517
theorem B349027 : Blo 346754 349027 := bstep (se 1 (by rfl) ⟨261770, by rfl⟩ : syracuseStep 349027 = 523541) B523541
theorem B349043 : Blo 346754 349043 := bstep (se 1 (by rfl) ⟨261782, by rfl⟩ : syracuseStep 349043 = 523565) B523565
theorem B349059 : Blo 346754 349059 := bstep (se 1 (by rfl) ⟨261794, by rfl⟩ : syracuseStep 349059 = 523589) B523589
theorem B349075 : Blo 346754 349075 := bstep (se 1 (by rfl) ⟨261806, by rfl⟩ : syracuseStep 349075 = 523613) B523613
theorem B349091 : Blo 346754 349091 := bstep (se 1 (by rfl) ⟨261818, by rfl⟩ : syracuseStep 349091 = 523637) B523637
theorem B349107 : Blo 346754 349107 := bstep (se 1 (by rfl) ⟨261830, by rfl⟩ : syracuseStep 349107 = 523661) B523661
theorem B349123 : Blo 346754 349123 := bstep (se 1 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 349123 = 523685) B523685
theorem B349139 : Blo 346754 349139 := bstep (se 1 (by rfl) ⟨261854, by rfl⟩ : syracuseStep 349139 = 523709) B523709
theorem B349155 : Blo 346754 349155 := bstep (se 1 (by rfl) ⟨261866, by rfl⟩ : syracuseStep 349155 = 523733) B523733
theorem B742385 : Blo 346754 742385 := bstep (se 2 (by rfl) ⟨278394, by rfl⟩ : syracuseStep 742385 = 556789) B556789
theorem B349171 : Blo 346754 349171 := bstep (se 1 (by rfl) ⟨261878, by rfl⟩ : syracuseStep 349171 = 523757) B523757
theorem B349187 : Blo 346754 349187 := bstep (se 1 (by rfl) ⟨261890, by rfl⟩ : syracuseStep 349187 = 523781) B523781
theorem B349203 : Blo 346754 349203 := bstep (se 1 (by rfl) ⟨261902, by rfl⟩ : syracuseStep 349203 = 523805) B523805
theorem B349219 : Blo 346754 349219 := bstep (se 1 (by rfl) ⟨261914, by rfl⟩ : syracuseStep 349219 = 523829) B523829
theorem B349235 : Blo 346754 349235 := bstep (se 1 (by rfl) ⟨261926, by rfl⟩ : syracuseStep 349235 = 523853) B523853
theorem B349251 : Blo 346754 349251 := bstep (se 1 (by rfl) ⟨261938, by rfl⟩ : syracuseStep 349251 = 523877) B523877
theorem B349267 : Blo 346754 349267 := bstep (se 1 (by rfl) ⟨261950, by rfl⟩ : syracuseStep 349267 = 523901) B523901
theorem B349283 : Blo 346754 349283 := bstep (se 1 (by rfl) ⟨261962, by rfl⟩ : syracuseStep 349283 = 523925) B523925
theorem B349299 : Blo 346754 349299 := bstep (se 1 (by rfl) ⟨261974, by rfl⟩ : syracuseStep 349299 = 523949) B523949
theorem B349315 : Blo 346754 349315 := bstep (se 1 (by rfl) ⟨261986, by rfl⟩ : syracuseStep 349315 = 523973) B523973
theorem B349331 : Blo 346754 349331 := bstep (se 1 (by rfl) ⟨261998, by rfl⟩ : syracuseStep 349331 = 523997) B523997
theorem B349347 : Blo 346754 349347 := bstep (se 1 (by rfl) ⟨262010, by rfl⟩ : syracuseStep 349347 = 524021) B524021
theorem B349363 : Blo 346754 349363 := bstep (se 1 (by rfl) ⟨262022, by rfl⟩ : syracuseStep 349363 = 524045) B524045
theorem B349379 : Blo 346754 349379 := bstep (se 1 (by rfl) ⟨262034, by rfl⟩ : syracuseStep 349379 = 524069) B524069
theorem B349395 : Blo 346754 349395 := bstep (se 1 (by rfl) ⟨262046, by rfl⟩ : syracuseStep 349395 = 524093) B524093
theorem B349411 : Blo 346754 349411 := bstep (se 1 (by rfl) ⟨262058, by rfl⟩ : syracuseStep 349411 = 524117) B524117
theorem B349427 : Blo 346754 349427 := bstep (se 1 (by rfl) ⟨262070, by rfl⟩ : syracuseStep 349427 = 524141) B524141
theorem B349443 : Blo 346754 349443 := bstep (se 1 (by rfl) ⟨262082, by rfl⟩ : syracuseStep 349443 = 524165) B524165
theorem B349459 : Blo 346754 349459 := bstep (se 1 (by rfl) ⟨262094, by rfl⟩ : syracuseStep 349459 = 524189) B524189
theorem B349475 : Blo 346754 349475 := bstep (se 1 (by rfl) ⟨262106, by rfl⟩ : syracuseStep 349475 = 524213) B524213
theorem B349491 : Blo 346754 349491 := bstep (se 1 (by rfl) ⟨262118, by rfl⟩ : syracuseStep 349491 = 524237) B524237
theorem B349507 : Blo 346754 349507 := bstep (se 1 (by rfl) ⟨262130, by rfl⟩ : syracuseStep 349507 = 524261) B524261
theorem B349523 : Blo 346754 349523 := bstep (se 1 (by rfl) ⟨262142, by rfl⟩ : syracuseStep 349523 = 524285) B524285
theorem B349539 : Blo 346754 349539 := bstep (se 1 (by rfl) ⟨262154, by rfl⟩ : syracuseStep 349539 = 524309) B524309
theorem B349555 : Blo 346754 349555 := bstep (se 1 (by rfl) ⟨262166, by rfl⟩ : syracuseStep 349555 = 524333) B524333
theorem B349571 : Blo 346754 349571 := bstep (se 1 (by rfl) ⟨262178, by rfl⟩ : syracuseStep 349571 = 524357) B524357
theorem B349587 : Blo 346754 349587 := bstep (se 1 (by rfl) ⟨262190, by rfl⟩ : syracuseStep 349587 = 524381) B524381
theorem B349603 : Blo 346754 349603 := bstep (se 1 (by rfl) ⟨262202, by rfl⟩ : syracuseStep 349603 = 524405) B524405
theorem B349619 : Blo 346754 349619 := bstep (se 1 (by rfl) ⟨262214, by rfl⟩ : syracuseStep 349619 = 524429) B524429
theorem B349635 : Blo 346754 349635 := bstep (se 1 (by rfl) ⟨262226, by rfl⟩ : syracuseStep 349635 = 524453) B524453
theorem B349651 : Blo 346754 349651 := bstep (se 1 (by rfl) ⟨262238, by rfl⟩ : syracuseStep 349651 = 524477) B524477
theorem B349667 : Blo 346754 349667 := bstep (se 1 (by rfl) ⟨262250, by rfl⟩ : syracuseStep 349667 = 524501) B524501
theorem B349683 : Blo 346754 349683 := bstep (se 1 (by rfl) ⟨262262, by rfl⟩ : syracuseStep 349683 = 524525) B524525
theorem B349699 : Blo 346754 349699 := bstep (se 1 (by rfl) ⟨262274, by rfl⟩ : syracuseStep 349699 = 524549) B524549
theorem B349715 : Blo 346754 349715 := bstep (se 1 (by rfl) ⟨262286, by rfl⟩ : syracuseStep 349715 = 524573) B524573
theorem B349731 : Blo 346754 349731 := bstep (se 1 (by rfl) ⟨262298, by rfl⟩ : syracuseStep 349731 = 524597) B524597
theorem B349747 : Blo 346754 349747 := bstep (se 1 (by rfl) ⟨262310, by rfl⟩ : syracuseStep 349747 = 524621) B524621
theorem B349763 : Blo 346754 349763 := bstep (se 1 (by rfl) ⟨262322, by rfl⟩ : syracuseStep 349763 = 524645) B524645
theorem B1988165 : Blo 346754 1988165 := bstep (se 4 (by rfl) ⟨186390, by rfl⟩ : syracuseStep 1988165 = 372781) B372781
theorem B349779 : Blo 346754 349779 := bstep (se 1 (by rfl) ⟨262334, by rfl⟩ : syracuseStep 349779 = 524669) B524669
theorem B349795 : Blo 346754 349795 := bstep (se 1 (by rfl) ⟨262346, by rfl⟩ : syracuseStep 349795 = 524693) B524693
theorem B1758833 : Blo 346754 1758833 := bstep (se 2 (by rfl) ⟨659562, by rfl⟩ : syracuseStep 1758833 = 1319125) B1319125
theorem B349811 : Blo 346754 349811 := bstep (se 1 (by rfl) ⟨262358, by rfl⟩ : syracuseStep 349811 = 524717) B524717
theorem B349827 : Blo 346754 349827 := bstep (se 1 (by rfl) ⟨262370, by rfl⟩ : syracuseStep 349827 = 524741) B524741
theorem B349843 : Blo 346754 349843 := bstep (se 1 (by rfl) ⟨262382, by rfl⟩ : syracuseStep 349843 = 524765) B524765
theorem B349859 : Blo 346754 349859 := bstep (se 1 (by rfl) ⟨262394, by rfl⟩ : syracuseStep 349859 = 524789) B524789
theorem B349875 : Blo 346754 349875 := bstep (se 1 (by rfl) ⟨262406, by rfl⟩ : syracuseStep 349875 = 524813) B524813
theorem B349891 : Blo 346754 349891 := bstep (se 1 (by rfl) ⟨262418, by rfl⟩ : syracuseStep 349891 = 524837) B524837
theorem B349907 : Blo 346754 349907 := bstep (se 1 (by rfl) ⟨262430, by rfl⟩ : syracuseStep 349907 = 524861) B524861
theorem B349923 : Blo 346754 349923 := bstep (se 1 (by rfl) ⟨262442, by rfl⟩ : syracuseStep 349923 = 524885) B524885
theorem B2119409 : Blo 346754 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B349939 : Blo 346754 349939 := bstep (se 1 (by rfl) ⟨262454, by rfl⟩ : syracuseStep 349939 = 524909) B524909
theorem B349955 : Blo 346754 349955 := bstep (se 1 (by rfl) ⟨262466, by rfl⟩ : syracuseStep 349955 = 524933) B524933
theorem B349971 : Blo 346754 349971 := bstep (se 1 (by rfl) ⟨262478, by rfl⟩ : syracuseStep 349971 = 524957) B524957
theorem B349987 : Blo 346754 349987 := bstep (se 1 (by rfl) ⟨262490, by rfl⟩ : syracuseStep 349987 = 524981) B524981
theorem B350003 : Blo 346754 350003 := bstep (se 1 (by rfl) ⟨262502, by rfl⟩ : syracuseStep 350003 = 525005) B525005
theorem B350019 : Blo 346754 350019 := bstep (se 1 (by rfl) ⟨262514, by rfl⟩ : syracuseStep 350019 = 525029) B525029
theorem B350035 : Blo 346754 350035 := bstep (se 1 (by rfl) ⟨262526, by rfl⟩ : syracuseStep 350035 = 525053) B525053
theorem B350051 : Blo 346754 350051 := bstep (se 1 (by rfl) ⟨262538, by rfl⟩ : syracuseStep 350051 = 525077) B525077
theorem B350067 : Blo 346754 350067 := bstep (se 1 (by rfl) ⟨262550, by rfl⟩ : syracuseStep 350067 = 525101) B525101
theorem B350083 : Blo 346754 350083 := bstep (se 1 (by rfl) ⟨262562, by rfl⟩ : syracuseStep 350083 = 525125) B525125
theorem B841603 : Blo 346754 841603 := bstep (se 1 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 841603 = 1262405) B1262405
theorem B350099 : Blo 346754 350099 := bstep (se 1 (by rfl) ⟨262574, by rfl⟩ : syracuseStep 350099 = 525149) B525149
theorem B350115 : Blo 346754 350115 := bstep (se 1 (by rfl) ⟨262586, by rfl⟩ : syracuseStep 350115 = 525173) B525173
theorem B350131 : Blo 346754 350131 := bstep (se 1 (by rfl) ⟨262598, by rfl⟩ : syracuseStep 350131 = 525197) B525197
theorem B350147 : Blo 346754 350147 := bstep (se 1 (by rfl) ⟨262610, by rfl⟩ : syracuseStep 350147 = 525221) B525221
theorem B350163 : Blo 346754 350163 := bstep (se 1 (by rfl) ⟨262622, by rfl⟩ : syracuseStep 350163 = 525245) B525245
theorem B350179 : Blo 346754 350179 := bstep (se 1 (by rfl) ⟨262634, by rfl⟩ : syracuseStep 350179 = 525269) B525269
theorem B841699 : Blo 346754 841699 := bstep (se 1 (by rfl) ⟨631274, by rfl⟩ : syracuseStep 841699 = 1262549) B1262549
theorem B350195 : Blo 346754 350195 := bstep (se 1 (by rfl) ⟨262646, by rfl⟩ : syracuseStep 350195 = 525293) B525293
theorem B350211 : Blo 346754 350211 := bstep (se 1 (by rfl) ⟨262658, by rfl⟩ : syracuseStep 350211 = 525317) B525317
theorem B1988621 : Blo 346754 1988621 := bstep (se 3 (by rfl) ⟨372866, by rfl⟩ : syracuseStep 1988621 = 745733) B745733
theorem B350227 : Blo 346754 350227 := bstep (se 1 (by rfl) ⟨262670, by rfl⟩ : syracuseStep 350227 = 525341) B525341
theorem B350243 : Blo 346754 350243 := bstep (se 1 (by rfl) ⟨262682, by rfl⟩ : syracuseStep 350243 = 525365) B525365
theorem B350259 : Blo 346754 350259 := bstep (se 1 (by rfl) ⟨262694, by rfl⟩ : syracuseStep 350259 = 525389) B525389
theorem B350275 : Blo 346754 350275 := bstep (se 1 (by rfl) ⟨262706, by rfl⟩ : syracuseStep 350275 = 525413) B525413
theorem B350291 : Blo 346754 350291 := bstep (se 1 (by rfl) ⟨262718, by rfl⟩ : syracuseStep 350291 = 525437) B525437
theorem B350307 : Blo 346754 350307 := bstep (se 1 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 350307 = 525461) B525461
theorem B350323 : Blo 346754 350323 := bstep (se 1 (by rfl) ⟨262742, by rfl⟩ : syracuseStep 350323 = 525485) B525485
theorem B350339 : Blo 346754 350339 := bstep (se 1 (by rfl) ⟨262754, by rfl⟩ : syracuseStep 350339 = 525509) B525509
theorem B350355 : Blo 346754 350355 := bstep (se 1 (by rfl) ⟨262766, by rfl⟩ : syracuseStep 350355 = 525533) B525533
theorem B350371 : Blo 346754 350371 := bstep (se 1 (by rfl) ⟨262778, by rfl⟩ : syracuseStep 350371 = 525557) B525557
theorem B350387 : Blo 346754 350387 := bstep (se 1 (by rfl) ⟨262790, by rfl⟩ : syracuseStep 350387 = 525581) B525581
theorem B350403 : Blo 346754 350403 := bstep (se 1 (by rfl) ⟨262802, by rfl⟩ : syracuseStep 350403 = 525605) B525605
theorem B350419 : Blo 346754 350419 := bstep (se 1 (by rfl) ⟨262814, by rfl⟩ : syracuseStep 350419 = 525629) B525629
theorem B1267939 : Blo 346754 1267939 := bstep (se 1 (by rfl) ⟨950954, by rfl⟩ : syracuseStep 1267939 = 1901909) B1901909
theorem B350435 : Blo 346754 350435 := bstep (se 1 (by rfl) ⟨262826, by rfl⟩ : syracuseStep 350435 = 525653) B525653
theorem B350451 : Blo 346754 350451 := bstep (se 1 (by rfl) ⟨262838, by rfl⟩ : syracuseStep 350451 = 525677) B525677
theorem B743683 : Blo 346754 743683 := bstep (se 1 (by rfl) ⟨557762, by rfl⟩ : syracuseStep 743683 = 1115525) B1115525
theorem B350467 : Blo 346754 350467 := bstep (se 1 (by rfl) ⟨262850, by rfl⟩ : syracuseStep 350467 = 525701) B525701
theorem B350483 : Blo 346754 350483 := bstep (se 1 (by rfl) ⟨262862, by rfl⟩ : syracuseStep 350483 = 525725) B525725
theorem B350499 : Blo 346754 350499 := bstep (se 1 (by rfl) ⟨262874, by rfl⟩ : syracuseStep 350499 = 525749) B525749
theorem B350515 : Blo 346754 350515 := bstep (se 1 (by rfl) ⟨262886, by rfl⟩ : syracuseStep 350515 = 525773) B525773
theorem B350531 : Blo 346754 350531 := bstep (se 1 (by rfl) ⟨262898, by rfl⟩ : syracuseStep 350531 = 525797) B525797
theorem B350547 : Blo 346754 350547 := bstep (se 1 (by rfl) ⟨262910, by rfl⟩ : syracuseStep 350547 = 525821) B525821
theorem B350563 : Blo 346754 350563 := bstep (se 1 (by rfl) ⟨262922, by rfl⟩ : syracuseStep 350563 = 525845) B525845
theorem B350579 : Blo 346754 350579 := bstep (se 1 (by rfl) ⟨262934, by rfl⟩ : syracuseStep 350579 = 525869) B525869
theorem B350595 : Blo 346754 350595 := bstep (se 1 (by rfl) ⟨262946, by rfl⟩ : syracuseStep 350595 = 525893) B525893
theorem B350611 : Blo 346754 350611 := bstep (se 1 (by rfl) ⟨262958, by rfl⟩ : syracuseStep 350611 = 525917) B525917
theorem B350627 : Blo 346754 350627 := bstep (se 1 (by rfl) ⟨262970, by rfl⟩ : syracuseStep 350627 = 525941) B525941
theorem B350643 : Blo 346754 350643 := bstep (se 1 (by rfl) ⟨262982, by rfl⟩ : syracuseStep 350643 = 525965) B525965
theorem B350659 : Blo 346754 350659 := bstep (se 1 (by rfl) ⟨262994, by rfl⟩ : syracuseStep 350659 = 525989) B525989
theorem B350675 : Blo 346754 350675 := bstep (se 1 (by rfl) ⟨263006, by rfl⟩ : syracuseStep 350675 = 526013) B526013
theorem B350691 : Blo 346754 350691 := bstep (se 1 (by rfl) ⟨263018, by rfl⟩ : syracuseStep 350691 = 526037) B526037
theorem B350707 : Blo 346754 350707 := bstep (se 1 (by rfl) ⟨263030, by rfl⟩ : syracuseStep 350707 = 526061) B526061
theorem B350723 : Blo 346754 350723 := bstep (se 1 (by rfl) ⟨263042, by rfl⟩ : syracuseStep 350723 = 526085) B526085
theorem B350739 : Blo 346754 350739 := bstep (se 1 (by rfl) ⟨263054, by rfl⟩ : syracuseStep 350739 = 526109) B526109
theorem B1137233 : Blo 346754 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B940835 : Blo 346754 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B416611 : Blo 346754 416611 := bstep (se 1 (by rfl) ⟨312458, by rfl⟩ : syracuseStep 416611 = 624917) B624917
theorem B1137539 : Blo 346754 1137539 := bstep (se 1 (by rfl) ⟨853154, by rfl⟩ : syracuseStep 1137539 = 1706309) B1706309
theorem B416707 : Blo 346754 416707 := bstep (se 1 (by rfl) ⟨312530, by rfl⟩ : syracuseStep 416707 = 625061) B625061
theorem B1170449 : Blo 346754 1170449 := bstep (se 2 (by rfl) ⟨438918, by rfl⟩ : syracuseStep 1170449 = 877837) B877837
theorem B1760291 : Blo 346754 1760291 := bstep (se 1 (by rfl) ⟨1320218, by rfl⟩ : syracuseStep 1760291 = 2640437) B2640437
theorem B3792053 : Blo 346754 3792053 := bstep (se 5 (by rfl) ⟨177752, by rfl⟩ : syracuseStep 3792053 = 355505) B355505
theorem B1891619 : Blo 346754 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B744913 : Blo 346754 744913 := bstep (se 2 (by rfl) ⟨279342, by rfl⟩ : syracuseStep 744913 = 558685) B558685
theorem B941549 : Blo 346754 941549 := bstep (se 3 (by rfl) ⟨176540, by rfl⟩ : syracuseStep 941549 = 353081) B353081
theorem B1170989 : Blo 346754 1170989 := bstep (se 3 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 1170989 = 439121) B439121
theorem B1171043 : Blo 346754 1171043 := bstep (se 1 (by rfl) ⟨878282, by rfl⟩ : syracuseStep 1171043 = 1756565) B1756565
theorem B1761101 : Blo 346754 1761101 := bstep (se 3 (by rfl) ⟨330206, by rfl⟩ : syracuseStep 1761101 = 660413) B660413
theorem B1171313 : Blo 346754 1171313 := bstep (se 2 (by rfl) ⟨439242, by rfl⟩ : syracuseStep 1171313 = 878485) B878485
theorem B417683 : Blo 346754 417683 := bstep (se 1 (by rfl) ⟨313262, by rfl⟩ : syracuseStep 417683 = 626525) B626525
theorem B4251761 : Blo 346754 4251761 := bstep (se 2 (by rfl) ⟨1594410, by rfl⟩ : syracuseStep 4251761 = 3188821) B3188821
theorem B2154701 : Blo 346754 2154701 := bstep (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) B808013
theorem B745699 : Blo 346754 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B1171853 : Blo 346754 1171853 := bstep (se 3 (by rfl) ⟨219722, by rfl⟩ : syracuseStep 1171853 = 439445) B439445
theorem B1171907 : Blo 346754 1171907 := bstep (se 1 (by rfl) ⟨878930, by rfl⟩ : syracuseStep 1171907 = 1757861) B1757861
theorem B1696241 : Blo 346754 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B1172177 : Blo 346754 1172177 := bstep (se 2 (by rfl) ⟨439566, by rfl⟩ : syracuseStep 1172177 = 879133) B879133
theorem B2646755 : Blo 346754 2646755 := bstep (se 1 (by rfl) ⟨1985066, by rfl⟩ : syracuseStep 2646755 = 3970133) B3970133
theorem B2286341 : Blo 346754 2286341 := bstep (se 4 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 2286341 = 428689) B428689
theorem B1991537 : Blo 346754 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B746417 : Blo 346754 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B3761093 : Blo 346754 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B1172717 : Blo 346754 1172717 := bstep (se 3 (by rfl) ⟨219884, by rfl⟩ : syracuseStep 1172717 = 439769) B439769
theorem B1172771 : Blo 346754 1172771 := bstep (se 1 (by rfl) ⟨879578, by rfl⟩ : syracuseStep 1172771 = 1759157) B1759157
theorem B746929 : Blo 346754 746929 := bstep (se 2 (by rfl) ⟨280098, by rfl⟩ : syracuseStep 746929 = 560197) B560197
theorem B1173041 : Blo 346754 1173041 := bstep (se 2 (by rfl) ⟨439890, by rfl⟩ : syracuseStep 1173041 = 879781) B879781
theorem B878161 : Blo 346754 878161 := bstep (se 2 (by rfl) ⟨329310, by rfl⟩ : syracuseStep 878161 = 658621) B658621
theorem B3958469 : Blo 346754 3958469 := bstep (se 4 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 3958469 = 742213) B742213
theorem B2221901 : Blo 346754 2221901 := bstep (se 3 (by rfl) ⟨416606, by rfl⟩ : syracuseStep 2221901 = 833213) B833213
theorem B943949 : Blo 346754 943949 := bstep (se 3 (by rfl) ⟨176990, by rfl⟩ : syracuseStep 943949 = 353981) B353981
theorem B878435 : Blo 346754 878435 := bstep (se 1 (by rfl) ⟨658826, by rfl⟩ : syracuseStep 878435 = 1317653) B1317653
theorem B780209 : Blo 346754 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B780227 : Blo 346754 780227 := bstep (se 1 (by rfl) ⟨585170, by rfl⟩ : syracuseStep 780227 = 1170341) B1170341
theorem B878627 : Blo 346754 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B2222129 : Blo 346754 2222129 := bstep (se 2 (by rfl) ⟨833298, by rfl⟩ : syracuseStep 2222129 = 1666597) B1666597
theorem B1173581 : Blo 346754 1173581 := bstep (se 3 (by rfl) ⟨220046, by rfl⟩ : syracuseStep 1173581 = 440093) B440093
theorem B649315 : Blo 346754 649315 := bstep (se 1 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 649315 = 973973) B973973
theorem B1173635 : Blo 346754 1173635 := bstep (se 1 (by rfl) ⟨880226, by rfl⟩ : syracuseStep 1173635 = 1760453) B1760453
theorem B780497 : Blo 346754 780497 := bstep (se 2 (by rfl) ⟨292686, by rfl⟩ : syracuseStep 780497 = 585373) B585373
theorem B780515 : Blo 346754 780515 := bstep (se 1 (by rfl) ⟨585386, by rfl⟩ : syracuseStep 780515 = 1170773) B1170773
theorem B1992995 : Blo 346754 1992995 := bstep (se 1 (by rfl) ⟨1494746, by rfl⟩ : syracuseStep 1992995 = 2989493) B2989493
theorem B1337741 : Blo 346754 1337741 := bstep (se 3 (by rfl) ⟨250826, by rfl⟩ : syracuseStep 1337741 = 501653) B501653
theorem B1173905 : Blo 346754 1173905 := bstep (se 2 (by rfl) ⟨440214, by rfl⟩ : syracuseStep 1173905 = 880429) B880429
theorem B780785 : Blo 346754 780785 := bstep (se 2 (by rfl) ⟨292794, by rfl⟩ : syracuseStep 780785 = 585589) B585589
theorem B4516337 : Blo 346754 4516337 := bstep (se 2 (by rfl) ⟨1693626, by rfl⟩ : syracuseStep 4516337 = 3387253) B3387253
theorem B780803 : Blo 346754 780803 := bstep (se 1 (by rfl) ⟨585602, by rfl⟩ : syracuseStep 780803 = 1171205) B1171205
theorem B1764017 : Blo 346754 1764017 := bstep (se 2 (by rfl) ⟨661506, by rfl⟩ : syracuseStep 1764017 = 1323013) B1323013
theorem B781073 : Blo 346754 781073 := bstep (se 2 (by rfl) ⟨292902, by rfl⟩ : syracuseStep 781073 = 585805) B585805
theorem B781091 : Blo 346754 781091 := bstep (se 1 (by rfl) ⟨585818, by rfl⟩ : syracuseStep 781091 = 1171637) B1171637
theorem B3566405 : Blo 346754 3566405 := bstep (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) B668701
theorem B748433 : Blo 346754 748433 := bstep (se 2 (by rfl) ⟨280662, by rfl⟩ : syracuseStep 748433 = 561325) B561325
theorem B1174445 : Blo 346754 1174445 := bstep (se 3 (by rfl) ⟨220208, by rfl⟩ : syracuseStep 1174445 = 440417) B440417
theorem B1076141 : Blo 346754 1076141 := bstep (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) B403553
theorem B879569 : Blo 346754 879569 := bstep (se 2 (by rfl) ⟨329838, by rfl⟩ : syracuseStep 879569 = 659677) B659677
theorem B1174499 : Blo 346754 1174499 := bstep (se 1 (by rfl) ⟨880874, by rfl⟩ : syracuseStep 1174499 = 1761749) B1761749
theorem B879619 : Blo 346754 879619 := bstep (se 1 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 879619 = 1319429) B1319429
theorem B781361 : Blo 346754 781361 := bstep (se 2 (by rfl) ⟨293010, by rfl⟩ : syracuseStep 781361 = 586021) B586021
theorem B781379 : Blo 346754 781379 := bstep (se 1 (by rfl) ⟨586034, by rfl⟩ : syracuseStep 781379 = 1172069) B1172069
theorem B879761 : Blo 346754 879761 := bstep (se 2 (by rfl) ⟨329910, by rfl⟩ : syracuseStep 879761 = 659821) B659821
theorem B1174769 : Blo 346754 1174769 := bstep (se 2 (by rfl) ⟨440538, by rfl⟩ : syracuseStep 1174769 = 881077) B881077
theorem B1993997 : Blo 346754 1993997 := bstep (se 3 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 1993997 = 747749) B747749
theorem B748835 : Blo 346754 748835 := bstep (se 1 (by rfl) ⟨561626, by rfl⟩ : syracuseStep 748835 = 1123253) B1123253
theorem B4222277 : Blo 346754 4222277 := bstep (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) B791677
theorem B781649 : Blo 346754 781649 := bstep (se 2 (by rfl) ⟨293118, by rfl⟩ : syracuseStep 781649 = 586237) B586237
theorem B781667 : Blo 346754 781667 := bstep (se 1 (by rfl) ⟨586250, by rfl⟩ : syracuseStep 781667 = 1172501) B1172501
theorem B585265 : Blo 346754 585265 := bstep (se 2 (by rfl) ⟨219474, by rfl⟩ : syracuseStep 585265 = 438949) B438949
theorem B585299 : Blo 346754 585299 := bstep (se 1 (by rfl) ⟨438974, by rfl⟩ : syracuseStep 585299 = 877949) B877949
theorem B781937 : Blo 346754 781937 := bstep (se 2 (by rfl) ⟨293226, by rfl⟩ : syracuseStep 781937 = 586453) B586453
theorem B781955 : Blo 346754 781955 := bstep (se 1 (by rfl) ⟨586466, by rfl⟩ : syracuseStep 781955 = 1172933) B1172933
theorem B585427 : Blo 346754 585427 := bstep (se 1 (by rfl) ⟨439070, by rfl⟩ : syracuseStep 585427 = 878141) B878141
theorem B1175309 : Blo 346754 1175309 := bstep (se 3 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 1175309 = 440741) B440741
theorem B1175363 : Blo 346754 1175363 := bstep (se 1 (by rfl) ⟨881522, by rfl⟩ : syracuseStep 1175363 = 1763045) B1763045
theorem B585569 : Blo 346754 585569 := bstep (se 2 (by rfl) ⟨219588, by rfl⟩ : syracuseStep 585569 = 439177) B439177
theorem B5926769 : Blo 346754 5926769 := bstep (se 2 (by rfl) ⟨2222538, by rfl⟩ : syracuseStep 5926769 = 4445077) B4445077
theorem B782225 : Blo 346754 782225 := bstep (se 2 (by rfl) ⟨293334, by rfl⟩ : syracuseStep 782225 = 586669) B586669
theorem B782243 : Blo 346754 782243 := bstep (se 1 (by rfl) ⟨586682, by rfl⟩ : syracuseStep 782243 = 1173365) B1173365
theorem B520145 : Blo 346754 520145 := bstep (se 2 (by rfl) ⟨195054, by rfl⟩ : syracuseStep 520145 = 390109) B390109
theorem B585697 : Blo 346754 585697 := bstep (se 2 (by rfl) ⟨219636, by rfl⟩ : syracuseStep 585697 = 439273) B439273
theorem B520163 : Blo 346754 520163 := bstep (se 1 (by rfl) ⟨390122, by rfl⟩ : syracuseStep 520163 = 780245) B780245
theorem B520193 : Blo 346754 520193 := bstep (se 2 (by rfl) ⟨195072, by rfl⟩ : syracuseStep 520193 = 390145) B390145
theorem B585731 : Blo 346754 585731 := bstep (se 1 (by rfl) ⟨439298, by rfl⟩ : syracuseStep 585731 = 878597) B878597
theorem B520211 : Blo 346754 520211 := bstep (se 1 (by rfl) ⟨390158, by rfl⟩ : syracuseStep 520211 = 780317) B780317
theorem B520241 : Blo 346754 520241 := bstep (se 2 (by rfl) ⟨195090, by rfl⟩ : syracuseStep 520241 = 390181) B390181
theorem B520259 : Blo 346754 520259 := bstep (se 1 (by rfl) ⟨390194, by rfl⟩ : syracuseStep 520259 = 780389) B780389
theorem B1175633 : Blo 346754 1175633 := bstep (se 2 (by rfl) ⟨440862, by rfl⟩ : syracuseStep 1175633 = 881725) B881725
theorem B520289 : Blo 346754 520289 := bstep (se 2 (by rfl) ⟨195108, by rfl⟩ : syracuseStep 520289 = 390217) B390217
theorem B1765475 : Blo 346754 1765475 := bstep (se 1 (by rfl) ⟨1324106, by rfl⟩ : syracuseStep 1765475 = 2648213) B2648213
theorem B880753 : Blo 346754 880753 := bstep (se 2 (by rfl) ⟨330282, by rfl⟩ : syracuseStep 880753 = 660565) B660565
theorem B520307 : Blo 346754 520307 := bstep (se 1 (by rfl) ⟨390230, by rfl⟩ : syracuseStep 520307 = 780461) B780461
theorem B585859 : Blo 346754 585859 := bstep (se 1 (by rfl) ⟨439394, by rfl⟩ : syracuseStep 585859 = 878789) B878789
theorem B1667213 : Blo 346754 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B520337 : Blo 346754 520337 := bstep (se 2 (by rfl) ⟨195126, by rfl⟩ : syracuseStep 520337 = 390253) B390253
theorem B520355 : Blo 346754 520355 := bstep (se 1 (by rfl) ⟨390266, by rfl⟩ : syracuseStep 520355 = 780533) B780533
theorem B782513 : Blo 346754 782513 := bstep (se 2 (by rfl) ⟨293442, by rfl⟩ : syracuseStep 782513 = 586885) B586885
theorem B520385 : Blo 346754 520385 := bstep (se 2 (by rfl) ⟨195144, by rfl⟩ : syracuseStep 520385 = 390289) B390289
theorem B782531 : Blo 346754 782531 := bstep (se 1 (by rfl) ⟨586898, by rfl⟩ : syracuseStep 782531 = 1173797) B1173797
theorem B520403 : Blo 346754 520403 := bstep (se 1 (by rfl) ⟨390302, by rfl⟩ : syracuseStep 520403 = 780605) B780605
theorem B520433 : Blo 346754 520433 := bstep (se 2 (by rfl) ⟨195162, by rfl⟩ : syracuseStep 520433 = 390325) B390325
theorem B520451 : Blo 346754 520451 := bstep (se 1 (by rfl) ⟨390338, by rfl⟩ : syracuseStep 520451 = 780677) B780677
theorem B586001 : Blo 346754 586001 := bstep (se 2 (by rfl) ⟨219750, by rfl⟩ : syracuseStep 586001 = 439501) B439501
theorem B520481 : Blo 346754 520481 := bstep (se 2 (by rfl) ⟨195180, by rfl⟩ : syracuseStep 520481 = 390361) B390361
theorem B520499 : Blo 346754 520499 := bstep (se 1 (by rfl) ⟨390374, by rfl⟩ : syracuseStep 520499 = 780749) B780749
theorem B1667405 : Blo 346754 1667405 := bstep (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) B625277
theorem B520529 : Blo 346754 520529 := bstep (se 2 (by rfl) ⟨195198, by rfl⟩ : syracuseStep 520529 = 390397) B390397
theorem B520547 : Blo 346754 520547 := bstep (se 1 (by rfl) ⟨390410, by rfl⟩ : syracuseStep 520547 = 780821) B780821
theorem B2978147 : Blo 346754 2978147 := bstep (se 1 (by rfl) ⟨2233610, by rfl⟩ : syracuseStep 2978147 = 4467221) B4467221
theorem B1077617 : Blo 346754 1077617 := bstep (se 2 (by rfl) ⟨404106, by rfl⟩ : syracuseStep 1077617 = 808213) B808213
theorem B520577 : Blo 346754 520577 := bstep (se 2 (by rfl) ⟨195216, by rfl⟩ : syracuseStep 520577 = 390433) B390433
theorem B881027 : Blo 346754 881027 := bstep (se 1 (by rfl) ⟨660770, by rfl⟩ : syracuseStep 881027 = 1321541) B1321541
theorem B586129 : Blo 346754 586129 := bstep (se 2 (by rfl) ⟨219798, by rfl⟩ : syracuseStep 586129 = 439597) B439597
theorem B520595 : Blo 346754 520595 := bstep (se 1 (by rfl) ⟨390446, by rfl⟩ : syracuseStep 520595 = 780893) B780893
theorem B1929635 : Blo 346754 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B520625 : Blo 346754 520625 := bstep (se 2 (by rfl) ⟨195234, by rfl⟩ : syracuseStep 520625 = 390469) B390469
theorem B586163 : Blo 346754 586163 := bstep (se 1 (by rfl) ⟨439622, by rfl⟩ : syracuseStep 586163 = 879245) B879245
theorem B520643 : Blo 346754 520643 := bstep (se 1 (by rfl) ⟨390482, by rfl⟩ : syracuseStep 520643 = 780965) B780965
theorem B782801 : Blo 346754 782801 := bstep (se 2 (by rfl) ⟨293550, by rfl⟩ : syracuseStep 782801 = 587101) B587101
theorem B520673 : Blo 346754 520673 := bstep (se 2 (by rfl) ⟨195252, by rfl⟩ : syracuseStep 520673 = 390505) B390505
theorem B782819 : Blo 346754 782819 := bstep (se 1 (by rfl) ⟨587114, by rfl⟩ : syracuseStep 782819 = 1174229) B1174229
theorem B520691 : Blo 346754 520691 := bstep (se 1 (by rfl) ⟨390518, by rfl⟩ : syracuseStep 520691 = 781037) B781037
theorem B520721 : Blo 346754 520721 := bstep (se 2 (by rfl) ⟨195270, by rfl⟩ : syracuseStep 520721 = 390541) B390541
theorem B520739 : Blo 346754 520739 := bstep (se 1 (by rfl) ⟨390554, by rfl⟩ : syracuseStep 520739 = 781109) B781109
theorem B586291 : Blo 346754 586291 := bstep (se 1 (by rfl) ⟨439718, by rfl⟩ : syracuseStep 586291 = 879437) B879437
theorem B520769 : Blo 346754 520769 := bstep (se 2 (by rfl) ⟨195288, by rfl⟩ : syracuseStep 520769 = 390577) B390577
theorem B881219 : Blo 346754 881219 := bstep (se 1 (by rfl) ⟨660914, by rfl⟩ : syracuseStep 881219 = 1321829) B1321829
theorem B520787 : Blo 346754 520787 := bstep (se 1 (by rfl) ⟨390590, by rfl⟩ : syracuseStep 520787 = 781181) B781181
theorem B1176173 : Blo 346754 1176173 := bstep (se 3 (by rfl) ⟨220532, by rfl⟩ : syracuseStep 1176173 = 441065) B441065
theorem B520817 : Blo 346754 520817 := bstep (se 2 (by rfl) ⟨195306, by rfl⟩ : syracuseStep 520817 = 390613) B390613
theorem B520835 : Blo 346754 520835 := bstep (se 1 (by rfl) ⟨390626, by rfl⟩ : syracuseStep 520835 = 781253) B781253
theorem B520865 : Blo 346754 520865 := bstep (se 2 (by rfl) ⟨195324, by rfl⟩ : syracuseStep 520865 = 390649) B390649
theorem B1176227 : Blo 346754 1176227 := bstep (se 1 (by rfl) ⟨882170, by rfl⟩ : syracuseStep 1176227 = 1764341) B1764341
theorem B520883 : Blo 346754 520883 := bstep (se 1 (by rfl) ⟨390662, by rfl⟩ : syracuseStep 520883 = 781325) B781325
theorem B586433 : Blo 346754 586433 := bstep (se 2 (by rfl) ⟨219912, by rfl⟩ : syracuseStep 586433 = 439825) B439825
theorem B520913 : Blo 346754 520913 := bstep (se 2 (by rfl) ⟨195342, by rfl⟩ : syracuseStep 520913 = 390685) B390685
theorem B520931 : Blo 346754 520931 := bstep (se 1 (by rfl) ⟨390698, by rfl⟩ : syracuseStep 520931 = 781397) B781397
theorem B783089 : Blo 346754 783089 := bstep (se 2 (by rfl) ⟨293658, by rfl⟩ : syracuseStep 783089 = 587317) B587317
theorem B520961 : Blo 346754 520961 := bstep (se 2 (by rfl) ⟨195360, by rfl⟩ : syracuseStep 520961 = 390721) B390721
theorem B783107 : Blo 346754 783107 := bstep (se 1 (by rfl) ⟨587330, by rfl⟩ : syracuseStep 783107 = 1174661) B1174661
theorem B520979 : Blo 346754 520979 := bstep (se 1 (by rfl) ⟨390734, by rfl⟩ : syracuseStep 520979 = 781469) B781469
theorem B521009 : Blo 346754 521009 := bstep (se 2 (by rfl) ⟨195378, by rfl⟩ : syracuseStep 521009 = 390757) B390757
theorem B586561 : Blo 346754 586561 := bstep (se 2 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 586561 = 439921) B439921
theorem B521027 : Blo 346754 521027 := bstep (se 1 (by rfl) ⟨390770, by rfl⟩ : syracuseStep 521027 = 781541) B781541
theorem B521057 : Blo 346754 521057 := bstep (se 2 (by rfl) ⟨195396, by rfl⟩ : syracuseStep 521057 = 390793) B390793
theorem B586595 : Blo 346754 586595 := bstep (se 1 (by rfl) ⟨439946, by rfl⟩ : syracuseStep 586595 = 879893) B879893
theorem B521075 : Blo 346754 521075 := bstep (se 1 (by rfl) ⟨390806, by rfl⟩ : syracuseStep 521075 = 781613) B781613
theorem B1766285 : Blo 346754 1766285 := bstep (se 3 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 1766285 = 662357) B662357
theorem B521105 : Blo 346754 521105 := bstep (se 2 (by rfl) ⟨195414, by rfl⟩ : syracuseStep 521105 = 390829) B390829
theorem B521123 : Blo 346754 521123 := bstep (se 1 (by rfl) ⟨390842, by rfl⟩ : syracuseStep 521123 = 781685) B781685
theorem B1176497 : Blo 346754 1176497 := bstep (se 2 (by rfl) ⟨441186, by rfl⟩ : syracuseStep 1176497 = 882373) B882373
theorem B521153 : Blo 346754 521153 := bstep (se 2 (by rfl) ⟨195432, by rfl⟩ : syracuseStep 521153 = 390865) B390865
theorem B422851 : Blo 346754 422851 := bstep (se 1 (by rfl) ⟨317138, by rfl⟩ : syracuseStep 422851 = 634277) B634277
theorem B1110989 : Blo 346754 1110989 := bstep (se 3 (by rfl) ⟨208310, by rfl⟩ : syracuseStep 1110989 = 416621) B416621
theorem B521171 : Blo 346754 521171 := bstep (se 1 (by rfl) ⟨390878, by rfl⟩ : syracuseStep 521171 = 781757) B781757
theorem B586723 : Blo 346754 586723 := bstep (se 1 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 586723 = 880085) B880085
theorem B521201 : Blo 346754 521201 := bstep (se 2 (by rfl) ⟨195450, by rfl⟩ : syracuseStep 521201 = 390901) B390901
theorem B521219 : Blo 346754 521219 := bstep (se 1 (by rfl) ⟨390914, by rfl⟩ : syracuseStep 521219 = 781829) B781829
theorem B783377 : Blo 346754 783377 := bstep (se 2 (by rfl) ⟨293766, by rfl⟩ : syracuseStep 783377 = 587533) B587533
theorem B390163 : Blo 346754 390163 := bstep (se 1 (by rfl) ⟨292622, by rfl⟩ : syracuseStep 390163 = 585245) B585245
theorem B521249 : Blo 346754 521249 := bstep (se 2 (by rfl) ⟨195468, by rfl⟩ : syracuseStep 521249 = 390937) B390937
theorem B783395 : Blo 346754 783395 := bstep (se 1 (by rfl) ⟨587546, by rfl⟩ : syracuseStep 783395 = 1175093) B1175093
theorem B521267 : Blo 346754 521267 := bstep (se 1 (by rfl) ⟨390950, by rfl⟩ : syracuseStep 521267 = 781901) B781901
theorem B1111117 : Blo 346754 1111117 := bstep (se 3 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 1111117 = 416669) B416669
theorem B521297 : Blo 346754 521297 := bstep (se 2 (by rfl) ⟨195486, by rfl⟩ : syracuseStep 521297 = 390973) B390973
theorem B521315 : Blo 346754 521315 := bstep (se 1 (by rfl) ⟨390986, by rfl⟩ : syracuseStep 521315 = 781973) B781973
theorem B586865 : Blo 346754 586865 := bstep (se 2 (by rfl) ⟨220074, by rfl⟩ : syracuseStep 586865 = 440149) B440149
theorem B521345 : Blo 346754 521345 := bstep (se 2 (by rfl) ⟨195504, by rfl⟩ : syracuseStep 521345 = 391009) B391009
theorem B521363 : Blo 346754 521363 := bstep (se 1 (by rfl) ⟨391022, by rfl⟩ : syracuseStep 521363 = 782045) B782045
theorem B390307 : Blo 346754 390307 := bstep (se 1 (by rfl) ⟨292730, by rfl⟩ : syracuseStep 390307 = 585461) B585461
theorem B521393 : Blo 346754 521393 := bstep (se 2 (by rfl) ⟨195522, by rfl⟩ : syracuseStep 521393 = 391045) B391045
theorem B521411 : Blo 346754 521411 := bstep (se 1 (by rfl) ⟨391058, by rfl⟩ : syracuseStep 521411 = 782117) B782117
theorem B4027589 : Blo 346754 4027589 := bstep (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) B755173
theorem B521441 : Blo 346754 521441 := bstep (se 2 (by rfl) ⟨195540, by rfl⟩ : syracuseStep 521441 = 391081) B391081
theorem B586993 : Blo 346754 586993 := bstep (se 2 (by rfl) ⟨220122, by rfl⟩ : syracuseStep 586993 = 440245) B440245
theorem B521459 : Blo 346754 521459 := bstep (se 1 (by rfl) ⟨391094, by rfl⟩ : syracuseStep 521459 = 782189) B782189
theorem B521489 : Blo 346754 521489 := bstep (se 2 (by rfl) ⟨195558, by rfl⟩ : syracuseStep 521489 = 391117) B391117
theorem B587027 : Blo 346754 587027 := bstep (se 1 (by rfl) ⟨440270, by rfl⟩ : syracuseStep 587027 = 880541) B880541
theorem B521507 : Blo 346754 521507 := bstep (se 1 (by rfl) ⟨391130, by rfl⟩ : syracuseStep 521507 = 782261) B782261
theorem B783665 : Blo 346754 783665 := bstep (se 2 (by rfl) ⟨293874, by rfl⟩ : syracuseStep 783665 = 587749) B587749
theorem B390451 : Blo 346754 390451 := bstep (se 1 (by rfl) ⟨292838, by rfl⟩ : syracuseStep 390451 = 585677) B585677
theorem B521537 : Blo 346754 521537 := bstep (se 2 (by rfl) ⟨195576, by rfl⟩ : syracuseStep 521537 = 391153) B391153
theorem B783683 : Blo 346754 783683 := bstep (se 1 (by rfl) ⟨587762, by rfl⟩ : syracuseStep 783683 = 1175525) B1175525
theorem B1111373 : Blo 346754 1111373 := bstep (se 3 (by rfl) ⟨208382, by rfl⟩ : syracuseStep 1111373 = 416765) B416765
theorem B521555 : Blo 346754 521555 := bstep (se 1 (by rfl) ⟨391166, by rfl⟩ : syracuseStep 521555 = 782333) B782333
theorem B521585 : Blo 346754 521585 := bstep (se 2 (by rfl) ⟨195594, by rfl⟩ : syracuseStep 521585 = 391189) B391189
theorem B521603 : Blo 346754 521603 := bstep (se 1 (by rfl) ⟨391202, by rfl⟩ : syracuseStep 521603 = 782405) B782405
theorem B587155 : Blo 346754 587155 := bstep (se 1 (by rfl) ⟨440366, by rfl⟩ : syracuseStep 587155 = 880733) B880733
theorem B521633 : Blo 346754 521633 := bstep (se 2 (by rfl) ⟨195612, by rfl⟩ : syracuseStep 521633 = 391225) B391225
theorem B521651 : Blo 346754 521651 := bstep (se 1 (by rfl) ⟨391238, by rfl⟩ : syracuseStep 521651 = 782477) B782477
theorem B390595 : Blo 346754 390595 := bstep (se 1 (by rfl) ⟨292946, by rfl⟩ : syracuseStep 390595 = 585893) B585893
theorem B1177037 : Blo 346754 1177037 := bstep (se 3 (by rfl) ⟨220694, by rfl⟩ : syracuseStep 1177037 = 441389) B441389
theorem B521681 : Blo 346754 521681 := bstep (se 2 (by rfl) ⟨195630, by rfl⟩ : syracuseStep 521681 = 391261) B391261
theorem B521699 : Blo 346754 521699 := bstep (se 1 (by rfl) ⟨391274, by rfl⟩ : syracuseStep 521699 = 782549) B782549
theorem B882161 : Blo 346754 882161 := bstep (se 2 (by rfl) ⟨330810, by rfl⟩ : syracuseStep 882161 = 661621) B661621
theorem B521729 : Blo 346754 521729 := bstep (se 2 (by rfl) ⟨195648, by rfl⟩ : syracuseStep 521729 = 391297) B391297
theorem B1177091 : Blo 346754 1177091 := bstep (se 1 (by rfl) ⟨882818, by rfl⟩ : syracuseStep 1177091 = 1765637) B1765637
theorem B521747 : Blo 346754 521747 := bstep (se 1 (by rfl) ⟨391310, by rfl⟩ : syracuseStep 521747 = 782621) B782621
theorem B587297 : Blo 346754 587297 := bstep (se 2 (by rfl) ⟨220236, by rfl⟩ : syracuseStep 587297 = 440473) B440473
theorem B882211 : Blo 346754 882211 := bstep (se 1 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 882211 = 1323317) B1323317
theorem B521777 : Blo 346754 521777 := bstep (se 2 (by rfl) ⟨195666, by rfl⟩ : syracuseStep 521777 = 391333) B391333
theorem B521795 : Blo 346754 521795 := bstep (se 1 (by rfl) ⟨391346, by rfl⟩ : syracuseStep 521795 = 782693) B782693
theorem B783953 : Blo 346754 783953 := bstep (se 2 (by rfl) ⟨293982, by rfl⟩ : syracuseStep 783953 = 587965) B587965
theorem B390739 : Blo 346754 390739 := bstep (se 1 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 390739 = 586109) B586109
theorem B521825 : Blo 346754 521825 := bstep (se 2 (by rfl) ⟨195684, by rfl⟩ : syracuseStep 521825 = 391369) B391369
theorem B783971 : Blo 346754 783971 := bstep (se 1 (by rfl) ⟨587978, by rfl⟩ : syracuseStep 783971 = 1175957) B1175957
theorem B521843 : Blo 346754 521843 := bstep (se 1 (by rfl) ⟨391382, by rfl⟩ : syracuseStep 521843 = 782765) B782765
theorem B521873 : Blo 346754 521873 := bstep (se 2 (by rfl) ⟨195702, by rfl⟩ : syracuseStep 521873 = 391405) B391405
theorem B587425 : Blo 346754 587425 := bstep (se 2 (by rfl) ⟨220284, by rfl⟩ : syracuseStep 587425 = 440569) B440569
theorem B521891 : Blo 346754 521891 := bstep (se 1 (by rfl) ⟨391418, by rfl⟩ : syracuseStep 521891 = 782837) B782837
theorem B882353 : Blo 346754 882353 := bstep (se 2 (by rfl) ⟨330882, by rfl⟩ : syracuseStep 882353 = 661765) B661765
theorem B521921 : Blo 346754 521921 := bstep (se 2 (by rfl) ⟨195720, by rfl⟩ : syracuseStep 521921 = 391441) B391441
theorem B587459 : Blo 346754 587459 := bstep (se 1 (by rfl) ⟨440594, by rfl⟩ : syracuseStep 587459 = 881189) B881189
theorem B980689 : Blo 346754 980689 := bstep (se 2 (by rfl) ⟨367758, by rfl⟩ : syracuseStep 980689 = 735517) B735517
theorem B521939 : Blo 346754 521939 := bstep (se 1 (by rfl) ⟨391454, by rfl⟩ : syracuseStep 521939 = 782909) B782909
theorem B390883 : Blo 346754 390883 := bstep (se 1 (by rfl) ⟨293162, by rfl⟩ : syracuseStep 390883 = 586325) B586325
theorem B521969 : Blo 346754 521969 := bstep (se 2 (by rfl) ⟨195738, by rfl⟩ : syracuseStep 521969 = 391477) B391477
theorem B521987 : Blo 346754 521987 := bstep (se 1 (by rfl) ⟨391490, by rfl⟩ : syracuseStep 521987 = 782981) B782981
theorem B947971 : Blo 346754 947971 := bstep (se 1 (by rfl) ⟨710978, by rfl⟩ : syracuseStep 947971 = 1421957) B1421957
theorem B1177361 : Blo 346754 1177361 := bstep (se 2 (by rfl) ⟨441510, by rfl⟩ : syracuseStep 1177361 = 883021) B883021
theorem B522017 : Blo 346754 522017 := bstep (se 2 (by rfl) ⟨195756, by rfl⟩ : syracuseStep 522017 = 391513) B391513
theorem B522035 : Blo 346754 522035 := bstep (se 1 (by rfl) ⟨391526, by rfl⟩ : syracuseStep 522035 = 783053) B783053
theorem B587587 : Blo 346754 587587 := bstep (se 1 (by rfl) ⟨440690, by rfl⟩ : syracuseStep 587587 = 881381) B881381
theorem B522065 : Blo 346754 522065 := bstep (se 2 (by rfl) ⟨195774, by rfl⟩ : syracuseStep 522065 = 391549) B391549
theorem B522083 : Blo 346754 522083 := bstep (se 1 (by rfl) ⟨391562, by rfl⟩ : syracuseStep 522083 = 783125) B783125
theorem B784241 : Blo 346754 784241 := bstep (se 2 (by rfl) ⟨294090, by rfl⟩ : syracuseStep 784241 = 588181) B588181
theorem B391027 : Blo 346754 391027 := bstep (se 1 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 391027 = 586541) B586541
theorem B522113 : Blo 346754 522113 := bstep (se 2 (by rfl) ⟨195792, by rfl⟩ : syracuseStep 522113 = 391585) B391585
theorem B784259 : Blo 346754 784259 := bstep (se 1 (by rfl) ⟨588194, by rfl⟩ : syracuseStep 784259 = 1176389) B1176389
theorem B522131 : Blo 346754 522131 := bstep (se 1 (by rfl) ⟨391598, by rfl⟩ : syracuseStep 522131 = 783197) B783197
theorem B522161 : Blo 346754 522161 := bstep (se 2 (by rfl) ⟨195810, by rfl⟩ : syracuseStep 522161 = 391621) B391621
theorem B522179 : Blo 346754 522179 := bstep (se 1 (by rfl) ⟨391634, by rfl⟩ : syracuseStep 522179 = 783269) B783269
theorem B2652101 : Blo 346754 2652101 := bstep (se 4 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 2652101 = 497269) B497269
theorem B587729 : Blo 346754 587729 := bstep (se 2 (by rfl) ⟨220398, by rfl⟩ : syracuseStep 587729 = 440797) B440797
theorem B522209 : Blo 346754 522209 := bstep (se 2 (by rfl) ⟨195828, by rfl⟩ : syracuseStep 522209 = 391657) B391657
theorem B522227 : Blo 346754 522227 := bstep (se 1 (by rfl) ⟨391670, by rfl⟩ : syracuseStep 522227 = 783341) B783341
theorem B391171 : Blo 346754 391171 := bstep (se 1 (by rfl) ⟨293378, by rfl⟩ : syracuseStep 391171 = 586757) B586757
theorem B522257 : Blo 346754 522257 := bstep (se 2 (by rfl) ⟨195846, by rfl⟩ : syracuseStep 522257 = 391693) B391693
theorem B522275 : Blo 346754 522275 := bstep (se 1 (by rfl) ⟨391706, by rfl⟩ : syracuseStep 522275 = 783413) B783413
theorem B522305 : Blo 346754 522305 := bstep (se 2 (by rfl) ⟨195864, by rfl⟩ : syracuseStep 522305 = 391729) B391729
theorem B587857 : Blo 346754 587857 := bstep (se 2 (by rfl) ⟨220446, by rfl⟩ : syracuseStep 587857 = 440893) B440893
theorem B522323 : Blo 346754 522323 := bstep (se 1 (by rfl) ⟨391742, by rfl⟩ : syracuseStep 522323 = 783485) B783485
theorem B522353 : Blo 346754 522353 := bstep (se 2 (by rfl) ⟨195882, by rfl⟩ : syracuseStep 522353 = 391765) B391765
theorem B1996913 : Blo 346754 1996913 := bstep (se 2 (by rfl) ⟨748842, by rfl⟩ : syracuseStep 1996913 = 1497685) B1497685
theorem B587891 : Blo 346754 587891 := bstep (se 1 (by rfl) ⟨440918, by rfl⟩ : syracuseStep 587891 = 881837) B881837
theorem B522371 : Blo 346754 522371 := bstep (se 1 (by rfl) ⟨391778, by rfl⟩ : syracuseStep 522371 = 783557) B783557
theorem B784529 : Blo 346754 784529 := bstep (se 2 (by rfl) ⟨294198, by rfl⟩ : syracuseStep 784529 = 588397) B588397
theorem B391315 : Blo 346754 391315 := bstep (se 1 (by rfl) ⟨293486, by rfl⟩ : syracuseStep 391315 = 586973) B586973
theorem B522401 : Blo 346754 522401 := bstep (se 2 (by rfl) ⟨195900, by rfl⟩ : syracuseStep 522401 = 391801) B391801
theorem B784547 : Blo 346754 784547 := bstep (se 1 (by rfl) ⟨588410, by rfl⟩ : syracuseStep 784547 = 1176821) B1176821
theorem B522419 : Blo 346754 522419 := bstep (se 1 (by rfl) ⟨391814, by rfl⟩ : syracuseStep 522419 = 783629) B783629
theorem B522449 : Blo 346754 522449 := bstep (se 2 (by rfl) ⟨195918, by rfl⟩ : syracuseStep 522449 = 391837) B391837
theorem B522467 : Blo 346754 522467 := bstep (se 1 (by rfl) ⟨391850, by rfl⟩ : syracuseStep 522467 = 783701) B783701
theorem B588019 : Blo 346754 588019 := bstep (se 1 (by rfl) ⟨441014, by rfl⟩ : syracuseStep 588019 = 882029) B882029
theorem B522497 : Blo 346754 522497 := bstep (se 2 (by rfl) ⟨195936, by rfl⟩ : syracuseStep 522497 = 391873) B391873
theorem B522515 : Blo 346754 522515 := bstep (se 1 (by rfl) ⟨391886, by rfl⟩ : syracuseStep 522515 = 783773) B783773
theorem B391459 : Blo 346754 391459 := bstep (se 1 (by rfl) ⟨293594, by rfl⟩ : syracuseStep 391459 = 587189) B587189
theorem B1177901 : Blo 346754 1177901 := bstep (se 3 (by rfl) ⟨220856, by rfl⟩ : syracuseStep 1177901 = 441713) B441713
theorem B522545 : Blo 346754 522545 := bstep (se 2 (by rfl) ⟨195954, by rfl⟩ : syracuseStep 522545 = 391909) B391909
theorem B522563 : Blo 346754 522563 := bstep (se 1 (by rfl) ⟨391922, by rfl⟩ : syracuseStep 522563 = 783845) B783845
theorem B522593 : Blo 346754 522593 := bstep (se 2 (by rfl) ⟨195972, by rfl⟩ : syracuseStep 522593 = 391945) B391945
theorem B1177955 : Blo 346754 1177955 := bstep (se 1 (by rfl) ⟨883466, by rfl⟩ : syracuseStep 1177955 = 1766933) B1766933
theorem B522611 : Blo 346754 522611 := bstep (se 1 (by rfl) ⟨391958, by rfl⟩ : syracuseStep 522611 = 783917) B783917
theorem B588161 : Blo 346754 588161 := bstep (se 2 (by rfl) ⟨220560, by rfl⟩ : syracuseStep 588161 = 441121) B441121
theorem B522641 : Blo 346754 522641 := bstep (se 2 (by rfl) ⟨195990, by rfl⟩ : syracuseStep 522641 = 391981) B391981
theorem B522659 : Blo 346754 522659 := bstep (se 1 (by rfl) ⟨391994, by rfl⟩ : syracuseStep 522659 = 783989) B783989
theorem B784817 : Blo 346754 784817 := bstep (se 2 (by rfl) ⟨294306, by rfl⟩ : syracuseStep 784817 = 588613) B588613
theorem B391603 : Blo 346754 391603 := bstep (se 1 (by rfl) ⟨293702, by rfl⟩ : syracuseStep 391603 = 587405) B587405
theorem B522689 : Blo 346754 522689 := bstep (se 2 (by rfl) ⟨196008, by rfl⟩ : syracuseStep 522689 = 392017) B392017
theorem B784835 : Blo 346754 784835 := bstep (se 1 (by rfl) ⟨588626, by rfl⟩ : syracuseStep 784835 = 1177253) B1177253
theorem B522707 : Blo 346754 522707 := bstep (se 1 (by rfl) ⟨392030, by rfl⟩ : syracuseStep 522707 = 784061) B784061
theorem B522737 : Blo 346754 522737 := bstep (se 2 (by rfl) ⟨196026, by rfl⟩ : syracuseStep 522737 = 392053) B392053
theorem B588289 : Blo 346754 588289 := bstep (se 2 (by rfl) ⟨220608, by rfl⟩ : syracuseStep 588289 = 441217) B441217
theorem B522755 : Blo 346754 522755 := bstep (se 1 (by rfl) ⟨392066, by rfl⟩ : syracuseStep 522755 = 784133) B784133
theorem B522785 : Blo 346754 522785 := bstep (se 2 (by rfl) ⟨196044, by rfl⟩ : syracuseStep 522785 = 392089) B392089
theorem B588323 : Blo 346754 588323 := bstep (se 1 (by rfl) ⟨441242, by rfl⟩ : syracuseStep 588323 = 882485) B882485
theorem B522803 : Blo 346754 522803 := bstep (se 1 (by rfl) ⟨392102, by rfl⟩ : syracuseStep 522803 = 784205) B784205
theorem B391747 : Blo 346754 391747 := bstep (se 1 (by rfl) ⟨293810, by rfl⟩ : syracuseStep 391747 = 587621) B587621
theorem B522833 : Blo 346754 522833 := bstep (se 2 (by rfl) ⟨196062, by rfl⟩ : syracuseStep 522833 = 392125) B392125
theorem B522851 : Blo 346754 522851 := bstep (se 1 (by rfl) ⟨392138, by rfl⟩ : syracuseStep 522851 = 784277) B784277
theorem B1178225 : Blo 346754 1178225 := bstep (se 2 (by rfl) ⟨441834, by rfl⟩ : syracuseStep 1178225 = 883669) B883669
theorem B522881 : Blo 346754 522881 := bstep (se 2 (by rfl) ⟨196080, by rfl⟩ : syracuseStep 522881 = 392161) B392161
theorem B883345 : Blo 346754 883345 := bstep (se 2 (by rfl) ⟨331254, by rfl⟩ : syracuseStep 883345 = 662509) B662509
theorem B522899 : Blo 346754 522899 := bstep (se 1 (by rfl) ⟨392174, by rfl⟩ : syracuseStep 522899 = 784349) B784349
theorem B588451 : Blo 346754 588451 := bstep (se 1 (by rfl) ⟨441338, by rfl⟩ : syracuseStep 588451 = 882677) B882677
theorem B522929 : Blo 346754 522929 := bstep (se 2 (by rfl) ⟨196098, by rfl⟩ : syracuseStep 522929 = 392197) B392197
theorem B522947 : Blo 346754 522947 := bstep (se 1 (by rfl) ⟨392210, by rfl⟩ : syracuseStep 522947 = 784421) B784421
theorem B785105 : Blo 346754 785105 := bstep (se 2 (by rfl) ⟨294414, by rfl⟩ : syracuseStep 785105 = 588829) B588829
theorem B391891 : Blo 346754 391891 := bstep (se 1 (by rfl) ⟨293918, by rfl⟩ : syracuseStep 391891 = 587837) B587837
theorem B522977 : Blo 346754 522977 := bstep (se 2 (by rfl) ⟨196116, by rfl⟩ : syracuseStep 522977 = 392233) B392233
theorem B785123 : Blo 346754 785123 := bstep (se 1 (by rfl) ⟨588842, by rfl⟩ : syracuseStep 785123 = 1177685) B1177685
theorem B522995 : Blo 346754 522995 := bstep (se 1 (by rfl) ⟨392246, by rfl⟩ : syracuseStep 522995 = 784493) B784493
theorem B523025 : Blo 346754 523025 := bstep (se 2 (by rfl) ⟨196134, by rfl⟩ : syracuseStep 523025 = 392269) B392269
theorem B523043 : Blo 346754 523043 := bstep (se 1 (by rfl) ⟨392282, by rfl⟩ : syracuseStep 523043 = 784565) B784565
theorem B588593 : Blo 346754 588593 := bstep (se 2 (by rfl) ⟨220722, by rfl⟩ : syracuseStep 588593 = 441445) B441445
theorem B523073 : Blo 346754 523073 := bstep (se 2 (by rfl) ⟨196152, by rfl⟩ : syracuseStep 523073 = 392305) B392305
theorem B1112899 : Blo 346754 1112899 := bstep (se 1 (by rfl) ⟨834674, by rfl⟩ : syracuseStep 1112899 = 1669349) B1669349
theorem B523091 : Blo 346754 523091 := bstep (se 1 (by rfl) ⟨392318, by rfl⟩ : syracuseStep 523091 = 784637) B784637
theorem B392035 : Blo 346754 392035 := bstep (se 1 (by rfl) ⟨294026, by rfl⟩ : syracuseStep 392035 = 588053) B588053
theorem B523121 : Blo 346754 523121 := bstep (se 2 (by rfl) ⟨196170, by rfl⟩ : syracuseStep 523121 = 392341) B392341
theorem B555905 : Blo 346754 555905 := bstep (se 2 (by rfl) ⟨208464, by rfl⟩ : syracuseStep 555905 = 416929) B416929
theorem B523139 : Blo 346754 523139 := bstep (se 1 (by rfl) ⟨392354, by rfl⟩ : syracuseStep 523139 = 784709) B784709
theorem B523169 : Blo 346754 523169 := bstep (se 2 (by rfl) ⟨196188, by rfl⟩ : syracuseStep 523169 = 392377) B392377
theorem B883619 : Blo 346754 883619 := bstep (se 1 (by rfl) ⟨662714, by rfl⟩ : syracuseStep 883619 = 1325429) B1325429
theorem B588721 : Blo 346754 588721 := bstep (se 2 (by rfl) ⟨220770, by rfl⟩ : syracuseStep 588721 = 441541) B441541
theorem B523187 : Blo 346754 523187 := bstep (se 1 (by rfl) ⟨392390, by rfl⟩ : syracuseStep 523187 = 784781) B784781
theorem B523217 : Blo 346754 523217 := bstep (se 2 (by rfl) ⟨196206, by rfl⟩ : syracuseStep 523217 = 392413) B392413
theorem B588755 : Blo 346754 588755 := bstep (se 1 (by rfl) ⟨441566, by rfl⟩ : syracuseStep 588755 = 883133) B883133
theorem B523235 : Blo 346754 523235 := bstep (se 1 (by rfl) ⟨392426, by rfl⟩ : syracuseStep 523235 = 784853) B784853
theorem B785393 : Blo 346754 785393 := bstep (se 2 (by rfl) ⟨294522, by rfl⟩ : syracuseStep 785393 = 589045) B589045
theorem B392179 : Blo 346754 392179 := bstep (se 1 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 392179 = 588269) B588269
theorem B523265 : Blo 346754 523265 := bstep (se 2 (by rfl) ⟨196224, by rfl⟩ : syracuseStep 523265 = 392449) B392449
theorem B785411 : Blo 346754 785411 := bstep (se 1 (by rfl) ⟨589058, by rfl⟩ : syracuseStep 785411 = 1178117) B1178117
theorem B523283 : Blo 346754 523283 := bstep (se 1 (by rfl) ⟨392462, by rfl⟩ : syracuseStep 523283 = 784925) B784925
theorem B523313 : Blo 346754 523313 := bstep (se 2 (by rfl) ⟨196242, by rfl⟩ : syracuseStep 523313 = 392485) B392485
theorem B523331 : Blo 346754 523331 := bstep (se 1 (by rfl) ⟨392498, by rfl⟩ : syracuseStep 523331 = 784997) B784997
theorem B588883 : Blo 346754 588883 := bstep (se 1 (by rfl) ⟨441662, by rfl⟩ : syracuseStep 588883 = 883325) B883325
theorem B523361 : Blo 346754 523361 := bstep (se 2 (by rfl) ⟨196260, by rfl⟩ : syracuseStep 523361 = 392521) B392521
theorem B883811 : Blo 346754 883811 := bstep (se 1 (by rfl) ⟨662858, by rfl⟩ : syracuseStep 883811 = 1325717) B1325717
theorem B523379 : Blo 346754 523379 := bstep (se 1 (by rfl) ⟨392534, by rfl⟩ : syracuseStep 523379 = 785069) B785069
theorem B392323 : Blo 346754 392323 := bstep (se 1 (by rfl) ⟨294242, by rfl⟩ : syracuseStep 392323 = 588485) B588485
theorem B1178765 : Blo 346754 1178765 := bstep (se 3 (by rfl) ⟨221018, by rfl⟩ : syracuseStep 1178765 = 442037) B442037
theorem B523409 : Blo 346754 523409 := bstep (se 2 (by rfl) ⟨196278, by rfl⟩ : syracuseStep 523409 = 392557) B392557
theorem B556193 : Blo 346754 556193 := bstep (se 2 (by rfl) ⟨208572, by rfl⟩ : syracuseStep 556193 = 417145) B417145
theorem B523427 : Blo 346754 523427 := bstep (se 1 (by rfl) ⟨392570, by rfl⟩ : syracuseStep 523427 = 785141) B785141
theorem B523457 : Blo 346754 523457 := bstep (se 2 (by rfl) ⟨196296, by rfl⟩ : syracuseStep 523457 = 392593) B392593
theorem B1178819 : Blo 346754 1178819 := bstep (se 1 (by rfl) ⟨884114, by rfl⟩ : syracuseStep 1178819 = 1768229) B1768229
theorem B523475 : Blo 346754 523475 := bstep (se 1 (by rfl) ⟨392606, by rfl⟩ : syracuseStep 523475 = 785213) B785213
theorem B589025 : Blo 346754 589025 := bstep (se 2 (by rfl) ⟨220884, by rfl⟩ : syracuseStep 589025 = 441769) B441769
theorem B523505 : Blo 346754 523505 := bstep (se 2 (by rfl) ⟨196314, by rfl⟩ : syracuseStep 523505 = 392629) B392629
theorem B523523 : Blo 346754 523523 := bstep (se 1 (by rfl) ⟨392642, by rfl⟩ : syracuseStep 523523 = 785285) B785285
theorem B785681 : Blo 346754 785681 := bstep (se 2 (by rfl) ⟨294630, by rfl⟩ : syracuseStep 785681 = 589261) B589261
theorem B392467 : Blo 346754 392467 := bstep (se 1 (by rfl) ⟨294350, by rfl⟩ : syracuseStep 392467 = 588701) B588701
theorem B523553 : Blo 346754 523553 := bstep (se 2 (by rfl) ⟨196332, by rfl⟩ : syracuseStep 523553 = 392665) B392665
theorem B785699 : Blo 346754 785699 := bstep (se 1 (by rfl) ⟨589274, by rfl⟩ : syracuseStep 785699 = 1178549) B1178549
theorem B523571 : Blo 346754 523571 := bstep (se 1 (by rfl) ⟨392678, by rfl⟩ : syracuseStep 523571 = 785357) B785357
theorem B523601 : Blo 346754 523601 := bstep (se 2 (by rfl) ⟨196350, by rfl⟩ : syracuseStep 523601 = 392701) B392701
theorem B589153 : Blo 346754 589153 := bstep (se 2 (by rfl) ⟨220932, by rfl⟩ : syracuseStep 589153 = 441865) B441865
theorem B523619 : Blo 346754 523619 := bstep (se 1 (by rfl) ⟨392714, by rfl⟩ : syracuseStep 523619 = 785429) B785429
theorem B556417 : Blo 346754 556417 := bstep (se 2 (by rfl) ⟨208656, by rfl⟩ : syracuseStep 556417 = 417313) B417313
theorem B523649 : Blo 346754 523649 := bstep (se 2 (by rfl) ⟨196368, by rfl⟩ : syracuseStep 523649 = 392737) B392737
theorem B589187 : Blo 346754 589187 := bstep (se 1 (by rfl) ⟨441890, by rfl⟩ : syracuseStep 589187 = 883781) B883781
theorem B3964301 : Blo 346754 3964301 := bstep (se 3 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 3964301 = 1486613) B1486613
theorem B523667 : Blo 346754 523667 := bstep (se 1 (by rfl) ⟨392750, by rfl⟩ : syracuseStep 523667 = 785501) B785501
theorem B392611 : Blo 346754 392611 := bstep (se 1 (by rfl) ⟨294458, by rfl⟩ : syracuseStep 392611 = 588917) B588917
theorem B523697 : Blo 346754 523697 := bstep (se 2 (by rfl) ⟨196386, by rfl⟩ : syracuseStep 523697 = 392773) B392773
theorem B523715 : Blo 346754 523715 := bstep (se 1 (by rfl) ⟨392786, by rfl⟩ : syracuseStep 523715 = 785573) B785573
theorem B1179089 : Blo 346754 1179089 := bstep (se 2 (by rfl) ⟨442158, by rfl⟩ : syracuseStep 1179089 = 884317) B884317
theorem B523745 : Blo 346754 523745 := bstep (se 2 (by rfl) ⟨196404, by rfl⟩ : syracuseStep 523745 = 392809) B392809
theorem B523763 : Blo 346754 523763 := bstep (se 1 (by rfl) ⟨392822, by rfl⟩ : syracuseStep 523763 = 785645) B785645
theorem B589315 : Blo 346754 589315 := bstep (se 1 (by rfl) ⟨441986, by rfl⟩ : syracuseStep 589315 = 883973) B883973
theorem B523793 : Blo 346754 523793 := bstep (se 2 (by rfl) ⟨196422, by rfl⟩ : syracuseStep 523793 = 392845) B392845
theorem B523811 : Blo 346754 523811 := bstep (se 1 (by rfl) ⟨392858, by rfl⟩ : syracuseStep 523811 = 785717) B785717
theorem B785969 : Blo 346754 785969 := bstep (se 2 (by rfl) ⟨294738, by rfl⟩ : syracuseStep 785969 = 589477) B589477
theorem B392755 : Blo 346754 392755 := bstep (se 1 (by rfl) ⟨294566, by rfl⟩ : syracuseStep 392755 = 589133) B589133
theorem B523841 : Blo 346754 523841 := bstep (se 2 (by rfl) ⟨196440, by rfl⟩ : syracuseStep 523841 = 392881) B392881
theorem B785987 : Blo 346754 785987 := bstep (se 1 (by rfl) ⟨589490, by rfl⟩ : syracuseStep 785987 = 1178981) B1178981
theorem B523859 : Blo 346754 523859 := bstep (se 1 (by rfl) ⟨392894, by rfl⟩ : syracuseStep 523859 = 785789) B785789
theorem B523889 : Blo 346754 523889 := bstep (se 2 (by rfl) ⟨196458, by rfl⟩ : syracuseStep 523889 = 392917) B392917
theorem B523907 : Blo 346754 523907 := bstep (se 1 (by rfl) ⟨392930, by rfl⟩ : syracuseStep 523907 = 785861) B785861
theorem B589457 : Blo 346754 589457 := bstep (se 2 (by rfl) ⟨221046, by rfl⟩ : syracuseStep 589457 = 442093) B442093
theorem B523937 : Blo 346754 523937 := bstep (se 2 (by rfl) ⟨196476, by rfl⟩ : syracuseStep 523937 = 392953) B392953
theorem B523955 : Blo 346754 523955 := bstep (se 1 (by rfl) ⟨392966, by rfl⟩ : syracuseStep 523955 = 785933) B785933
theorem B392899 : Blo 346754 392899 := bstep (se 1 (by rfl) ⟨294674, by rfl⟩ : syracuseStep 392899 = 589349) B589349
theorem B523985 : Blo 346754 523985 := bstep (se 2 (by rfl) ⟨196494, by rfl⟩ : syracuseStep 523985 = 392989) B392989
theorem B524003 : Blo 346754 524003 := bstep (se 1 (by rfl) ⟨393002, by rfl⟩ : syracuseStep 524003 = 786005) B786005
theorem B1769201 : Blo 346754 1769201 := bstep (se 2 (by rfl) ⟨663450, by rfl⟩ : syracuseStep 1769201 = 1326901) B1326901
theorem B524033 : Blo 346754 524033 := bstep (se 2 (by rfl) ⟨196512, by rfl⟩ : syracuseStep 524033 = 393025) B393025
theorem B589585 : Blo 346754 589585 := bstep (se 2 (by rfl) ⟨221094, by rfl⟩ : syracuseStep 589585 = 442189) B442189
theorem B524051 : Blo 346754 524051 := bstep (se 1 (by rfl) ⟨393038, by rfl⟩ : syracuseStep 524051 = 786077) B786077
theorem B524081 : Blo 346754 524081 := bstep (se 2 (by rfl) ⟨196530, by rfl⟩ : syracuseStep 524081 = 393061) B393061
theorem B589619 : Blo 346754 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B524099 : Blo 346754 524099 := bstep (se 1 (by rfl) ⟨393074, by rfl⟩ : syracuseStep 524099 = 786149) B786149
theorem B786257 : Blo 346754 786257 := bstep (se 2 (by rfl) ⟨294846, by rfl⟩ : syracuseStep 786257 = 589693) B589693
theorem B393043 : Blo 346754 393043 := bstep (se 1 (by rfl) ⟨294782, by rfl⟩ : syracuseStep 393043 = 589565) B589565
theorem B524129 : Blo 346754 524129 := bstep (se 2 (by rfl) ⟨196548, by rfl⟩ : syracuseStep 524129 = 393097) B393097
theorem B786275 : Blo 346754 786275 := bstep (se 1 (by rfl) ⟨589706, by rfl⟩ : syracuseStep 786275 = 1179413) B1179413
theorem B556915 : Blo 346754 556915 := bstep (se 1 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 556915 = 835373) B835373
theorem B524147 : Blo 346754 524147 := bstep (se 1 (by rfl) ⟨393110, by rfl⟩ : syracuseStep 524147 = 786221) B786221
theorem B524177 : Blo 346754 524177 := bstep (se 2 (by rfl) ⟨196566, by rfl⟩ : syracuseStep 524177 = 393133) B393133
theorem B524195 : Blo 346754 524195 := bstep (se 1 (by rfl) ⟨393146, by rfl⟩ : syracuseStep 524195 = 786293) B786293
theorem B589747 : Blo 346754 589747 := bstep (se 1 (by rfl) ⟨442310, by rfl⟩ : syracuseStep 589747 = 884621) B884621
theorem B524225 : Blo 346754 524225 := bstep (se 2 (by rfl) ⟨196584, by rfl⟩ : syracuseStep 524225 = 393169) B393169
theorem B524243 : Blo 346754 524243 := bstep (se 1 (by rfl) ⟨393182, by rfl⟩ : syracuseStep 524243 = 786365) B786365
theorem B393187 : Blo 346754 393187 := bstep (se 1 (by rfl) ⟨294890, by rfl⟩ : syracuseStep 393187 = 589781) B589781
theorem B1179629 : Blo 346754 1179629 := bstep (se 3 (by rfl) ⟨221180, by rfl⟩ : syracuseStep 1179629 = 442361) B442361
theorem B524273 : Blo 346754 524273 := bstep (se 2 (by rfl) ⟨196602, by rfl⟩ : syracuseStep 524273 = 393205) B393205
theorem B589835 : Blo 346754 589835 := bstep (se 1 (by rfl) ⟨442376, by rfl⟩ : syracuseStep 589835 = 884753) B884753
theorem B786455 : Blo 346754 786455 := bstep (se 1 (by rfl) ⟨589841, by rfl⟩ : syracuseStep 786455 = 1179683) B1179683
theorem B393259 : Blo 346754 393259 := bstep (se 1 (by rfl) ⟨294944, by rfl⟩ : syracuseStep 393259 = 589889) B589889
theorem B524363 : Blo 346754 524363 := bstep (se 1 (by rfl) ⟨393272, by rfl⟩ : syracuseStep 524363 = 786545) B786545
theorem B524375 : Blo 346754 524375 := bstep (se 1 (by rfl) ⟨393281, by rfl⟩ : syracuseStep 524375 = 786563) B786563
theorem B1179737 : Blo 346754 1179737 := bstep (se 2 (by rfl) ⟨442401, by rfl⟩ : syracuseStep 1179737 = 884803) B884803
theorem B589963 : Blo 346754 589963 := bstep (se 1 (by rfl) ⟨442472, by rfl⟩ : syracuseStep 589963 = 884945) B884945
theorem B393367 : Blo 346754 393367 := bstep (se 1 (by rfl) ⟨295025, by rfl⟩ : syracuseStep 393367 = 590051) B590051
theorem B524441 : Blo 346754 524441 := bstep (se 2 (by rfl) ⟨196665, by rfl⟩ : syracuseStep 524441 = 393331) B393331
theorem B1671347 : Blo 346754 1671347 := bstep (se 1 (by rfl) ⟨1253510, by rfl⟩ : syracuseStep 1671347 = 2507021) B2507021
theorem B884915 : Blo 346754 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B786635 : Blo 346754 786635 := bstep (se 1 (by rfl) ⟨589976, by rfl⟩ : syracuseStep 786635 = 1179953) B1179953
theorem B786689 : Blo 346754 786689 := bstep (se 2 (by rfl) ⟨295008, by rfl⟩ : syracuseStep 786689 = 590017) B590017
theorem B524555 : Blo 346754 524555 := bstep (se 1 (by rfl) ⟨393416, by rfl⟩ : syracuseStep 524555 = 786833) B786833
theorem B524567 : Blo 346754 524567 := bstep (se 1 (by rfl) ⟨393425, by rfl⟩ : syracuseStep 524567 = 786851) B786851
theorem B590105 : Blo 346754 590105 := bstep (se 2 (by rfl) ⟨221289, by rfl⟩ : syracuseStep 590105 = 442579) B442579
theorem B491851 : Blo 346754 491851 := bstep (se 1 (by rfl) ⟨368888, by rfl⟩ : syracuseStep 491851 = 737777) B737777
theorem B393547 : Blo 346754 393547 := bstep (se 1 (by rfl) ⟨295160, by rfl⟩ : syracuseStep 393547 = 590321) B590321
theorem B524633 : Blo 346754 524633 := bstep (se 2 (by rfl) ⟨196737, by rfl⟩ : syracuseStep 524633 = 393475) B393475
theorem B17170805 : Blo 346754 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B590233 : Blo 346754 590233 := bstep (se 2 (by rfl) ⟨221337, by rfl⟩ : syracuseStep 590233 = 442675) B442675
theorem B393655 : Blo 346754 393655 := bstep (se 1 (by rfl) ⟨295241, by rfl⟩ : syracuseStep 393655 = 590483) B590483
theorem B524747 : Blo 346754 524747 := bstep (se 1 (by rfl) ⟨393560, by rfl⟩ : syracuseStep 524747 = 787121) B787121
theorem B524759 : Blo 346754 524759 := bstep (se 1 (by rfl) ⟨393569, by rfl⟩ : syracuseStep 524759 = 787139) B787139
theorem B786905 : Blo 346754 786905 := bstep (se 2 (by rfl) ⟨295089, by rfl⟩ : syracuseStep 786905 = 590179) B590179
theorem B1409501 : Blo 346754 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B524825 : Blo 346754 524825 := bstep (se 2 (by rfl) ⟨196809, by rfl⟩ : syracuseStep 524825 = 393619) B393619
theorem B786995 : Blo 346754 786995 := bstep (se 1 (by rfl) ⟨590246, by rfl⟩ : syracuseStep 786995 = 1180493) B1180493
theorem B787031 : Blo 346754 787031 := bstep (se 1 (by rfl) ⟨590273, by rfl⟩ : syracuseStep 787031 = 1180547) B1180547
theorem B393835 : Blo 346754 393835 := bstep (se 1 (by rfl) ⟨295376, by rfl⟩ : syracuseStep 393835 = 590753) B590753
theorem B524939 : Blo 346754 524939 := bstep (se 1 (by rfl) ⟨393704, by rfl⟩ : syracuseStep 524939 = 787409) B787409
theorem B524951 : Blo 346754 524951 := bstep (se 1 (by rfl) ⟨393713, by rfl⟩ : syracuseStep 524951 = 787427) B787427
theorem B885451 : Blo 346754 885451 := bstep (se 1 (by rfl) ⟨664088, by rfl⟩ : syracuseStep 885451 = 1328177) B1328177
theorem B393943 : Blo 346754 393943 := bstep (se 1 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 393943 = 590915) B590915
theorem B525017 : Blo 346754 525017 := bstep (se 2 (by rfl) ⟨196881, by rfl⟩ : syracuseStep 525017 = 393763) B393763
theorem B787211 : Blo 346754 787211 := bstep (se 1 (by rfl) ⟨590408, by rfl⟩ : syracuseStep 787211 = 1180817) B1180817
theorem B1180439 : Blo 346754 1180439 := bstep (se 1 (by rfl) ⟨885329, by rfl⟩ : syracuseStep 1180439 = 1770659) B1770659
theorem B787265 : Blo 346754 787265 := bstep (se 2 (by rfl) ⟨295224, by rfl⟩ : syracuseStep 787265 = 590449) B590449
theorem B1016651 : Blo 346754 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B525131 : Blo 346754 525131 := bstep (se 1 (by rfl) ⟨393848, by rfl⟩ : syracuseStep 525131 = 787697) B787697
theorem B525143 : Blo 346754 525143 := bstep (se 1 (by rfl) ⟨393857, by rfl⟩ : syracuseStep 525143 = 787715) B787715
theorem B885593 : Blo 346754 885593 := bstep (se 2 (by rfl) ⟨332097, by rfl⟩ : syracuseStep 885593 = 664195) B664195
theorem B394123 : Blo 346754 394123 := bstep (se 1 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 394123 = 591185) B591185
theorem B525209 : Blo 346754 525209 := bstep (se 2 (by rfl) ⟨196953, by rfl⟩ : syracuseStep 525209 = 393907) B393907
theorem B590807 : Blo 346754 590807 := bstep (se 1 (by rfl) ⟨443105, by rfl⟩ : syracuseStep 590807 = 886211) B886211
theorem B394231 : Blo 346754 394231 := bstep (se 1 (by rfl) ⟨295673, by rfl⟩ : syracuseStep 394231 = 591347) B591347
theorem B525323 : Blo 346754 525323 := bstep (se 1 (by rfl) ⟨393992, by rfl⟩ : syracuseStep 525323 = 787985) B787985
theorem B525335 : Blo 346754 525335 := bstep (se 1 (by rfl) ⟨394001, by rfl⟩ : syracuseStep 525335 = 788003) B788003
theorem B787481 : Blo 346754 787481 := bstep (se 2 (by rfl) ⟨295305, by rfl⟩ : syracuseStep 787481 = 590611) B590611
theorem B590935 : Blo 346754 590935 := bstep (se 1 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 590935 = 886403) B886403
theorem B525401 : Blo 346754 525401 := bstep (se 2 (by rfl) ⟨197025, by rfl⟩ : syracuseStep 525401 = 394051) B394051
theorem B787571 : Blo 346754 787571 := bstep (se 1 (by rfl) ⟨590678, by rfl⟩ : syracuseStep 787571 = 1181357) B1181357
theorem B787607 : Blo 346754 787607 := bstep (se 1 (by rfl) ⟨590705, by rfl⟩ : syracuseStep 787607 = 1181411) B1181411
theorem B394411 : Blo 346754 394411 := bstep (se 1 (by rfl) ⟨295808, by rfl⟩ : syracuseStep 394411 = 591617) B591617
theorem B525515 : Blo 346754 525515 := bstep (se 1 (by rfl) ⟨394136, by rfl⟩ : syracuseStep 525515 = 788273) B788273
theorem B525527 : Blo 346754 525527 := bstep (se 1 (by rfl) ⟨394145, by rfl⟩ : syracuseStep 525527 = 788291) B788291
theorem B394519 : Blo 346754 394519 := bstep (se 1 (by rfl) ⟨295889, by rfl⟩ : syracuseStep 394519 = 591779) B591779
theorem B525593 : Blo 346754 525593 := bstep (se 2 (by rfl) ⟨197097, by rfl⟩ : syracuseStep 525593 = 394195) B394195
theorem B4523309 : Blo 346754 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B1180979 : Blo 346754 1180979 := bstep (se 1 (by rfl) ⟨885734, by rfl⟩ : syracuseStep 1180979 = 1771469) B1771469
theorem B2819393 : Blo 346754 2819393 := bstep (se 2 (by rfl) ⟨1057272, by rfl⟩ : syracuseStep 2819393 = 2114545) B2114545
theorem B787787 : Blo 346754 787787 := bstep (se 1 (by rfl) ⟨590840, by rfl⟩ : syracuseStep 787787 = 1181681) B1181681
theorem B787841 : Blo 346754 787841 := bstep (se 2 (by rfl) ⟨295440, by rfl⟩ : syracuseStep 787841 = 590881) B590881
theorem B525707 : Blo 346754 525707 := bstep (se 1 (by rfl) ⟨394280, by rfl⟩ : syracuseStep 525707 = 788561) B788561
theorem B525719 : Blo 346754 525719 := bstep (se 1 (by rfl) ⟨394289, by rfl⟩ : syracuseStep 525719 = 788579) B788579
theorem B2131379 : Blo 346754 2131379 := bstep (se 1 (by rfl) ⟨1598534, by rfl⟩ : syracuseStep 2131379 = 3197069) B3197069
theorem B558551 : Blo 346754 558551 := bstep (se 1 (by rfl) ⟨418913, by rfl⟩ : syracuseStep 558551 = 837827) B837827
theorem B525785 : Blo 346754 525785 := bstep (se 2 (by rfl) ⟨197169, by rfl⟩ : syracuseStep 525785 = 394339) B394339
theorem B1181249 : Blo 346754 1181249 := bstep (se 2 (by rfl) ⟨442968, by rfl⟩ : syracuseStep 1181249 = 885937) B885937
theorem B525899 : Blo 346754 525899 := bstep (se 1 (by rfl) ⟨394424, by rfl⟩ : syracuseStep 525899 = 788849) B788849
theorem B525911 : Blo 346754 525911 := bstep (se 1 (by rfl) ⟨394433, by rfl⟩ : syracuseStep 525911 = 788867) B788867
theorem B788057 : Blo 346754 788057 := bstep (se 2 (by rfl) ⟨295521, by rfl⟩ : syracuseStep 788057 = 591043) B591043
theorem B886423 : Blo 346754 886423 := bstep (se 1 (by rfl) ⟨664817, by rfl⟩ : syracuseStep 886423 = 1329635) B1329635
theorem B525977 : Blo 346754 525977 := bstep (se 2 (by rfl) ⟨197241, by rfl⟩ : syracuseStep 525977 = 394483) B394483
theorem B788147 : Blo 346754 788147 := bstep (se 1 (by rfl) ⟨591110, by rfl⟩ : syracuseStep 788147 = 1182221) B1182221
theorem B591563 : Blo 346754 591563 := bstep (se 1 (by rfl) ⟨443672, by rfl⟩ : syracuseStep 591563 = 887345) B887345
theorem B788183 : Blo 346754 788183 := bstep (se 1 (by rfl) ⟨591137, by rfl⟩ : syracuseStep 788183 = 1182275) B1182275
theorem B526091 : Blo 346754 526091 := bstep (se 1 (by rfl) ⟨394568, by rfl⟩ : syracuseStep 526091 = 789137) B789137
theorem B526103 : Blo 346754 526103 := bstep (se 1 (by rfl) ⟨394577, by rfl⟩ : syracuseStep 526103 = 789155) B789155
theorem B591691 : Blo 346754 591691 := bstep (se 1 (by rfl) ⟨443768, by rfl⟩ : syracuseStep 591691 = 887537) B887537
theorem B788363 : Blo 346754 788363 := bstep (se 1 (by rfl) ⟨591272, by rfl⟩ : syracuseStep 788363 = 1182545) B1182545
theorem B788417 : Blo 346754 788417 := bstep (se 2 (by rfl) ⟨295656, by rfl⟩ : syracuseStep 788417 = 591313) B591313
theorem B591833 : Blo 346754 591833 := bstep (se 2 (by rfl) ⟨221937, by rfl⟩ : syracuseStep 591833 = 443875) B443875
theorem B886859 : Blo 346754 886859 := bstep (se 1 (by rfl) ⟨665144, by rfl⟩ : syracuseStep 886859 = 1330289) B1330289
theorem B1181789 : Blo 346754 1181789 := bstep (se 3 (by rfl) ⟨221585, by rfl⟩ : syracuseStep 1181789 = 443171) B443171
theorem B788633 : Blo 346754 788633 := bstep (se 2 (by rfl) ⟨295737, by rfl⟩ : syracuseStep 788633 = 591475) B591475
theorem B1411289 : Blo 346754 1411289 := bstep (se 2 (by rfl) ⟨529233, by rfl⟩ : syracuseStep 1411289 = 1058467) B1058467
theorem B788723 : Blo 346754 788723 := bstep (se 1 (by rfl) ⟨591542, by rfl⟩ : syracuseStep 788723 = 1183085) B1183085
theorem B1771793 : Blo 346754 1771793 := bstep (se 2 (by rfl) ⟨664422, by rfl⟩ : syracuseStep 1771793 = 1328845) B1328845
theorem B788759 : Blo 346754 788759 := bstep (se 1 (by rfl) ⟨591569, by rfl⟩ : syracuseStep 788759 = 1183139) B1183139
theorem B8063381 : Blo 346754 8063381 := bstep (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) B377971
theorem B1771955 : Blo 346754 1771955 := bstep (se 1 (by rfl) ⟨1328966, by rfl⟩ : syracuseStep 1771955 = 2657933) B2657933
theorem B887233 : Blo 346754 887233 := bstep (se 2 (by rfl) ⟨332712, by rfl⟩ : syracuseStep 887233 = 665425) B665425
theorem B788939 : Blo 346754 788939 := bstep (se 1 (by rfl) ⟨591704, by rfl⟩ : syracuseStep 788939 = 1183409) B1183409
theorem B788993 : Blo 346754 788993 := bstep (se 2 (by rfl) ⟨295872, by rfl⟩ : syracuseStep 788993 = 591745) B591745
theorem B887831 : Blo 346754 887831 := bstep (se 1 (by rfl) ⟨665873, by rfl⟩ : syracuseStep 887831 = 1331747) B1331747
theorem B625753 : Blo 346754 625753 := bstep (se 2 (by rfl) ⟨234657, by rfl⟩ : syracuseStep 625753 = 469315) B469315
theorem B1182923 : Blo 346754 1182923 := bstep (se 1 (by rfl) ⟨887192, by rfl⟩ : syracuseStep 1182923 = 1774385) B1774385
theorem B494923 : Blo 346754 494923 := bstep (se 1 (by rfl) ⟨371192, by rfl⟩ : syracuseStep 494923 = 742385) B742385
theorem B1183193 : Blo 346754 1183193 := bstep (se 2 (by rfl) ⟨443697, by rfl⟩ : syracuseStep 1183193 = 887395) B887395
theorem B658955 : Blo 346754 658955 := bstep (se 1 (by rfl) ⟨494216, by rfl⟩ : syracuseStep 658955 = 988433) B988433
theorem B659009 : Blo 346754 659009 := bstep (se 2 (by rfl) ⟨247128, by rfl⟩ : syracuseStep 659009 = 494257) B494257
theorem B1412939 : Blo 346754 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B10030949 : Blo 346754 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B7180589 : Blo 346754 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B1773899 : Blo 346754 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B3019139 : Blo 346754 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B758155 : Blo 346754 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B659927 : Blo 346754 659927 := bstep (se 1 (by rfl) ⟨494945, by rfl⟩ : syracuseStep 659927 = 989891) B989891
theorem B496153 : Blo 346754 496153 := bstep (se 2 (by rfl) ⟨186057, by rfl⟩ : syracuseStep 496153 = 372115) B372115
theorem B1250093 : Blo 346754 1250093 := bstep (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) B468785
theorem B3183461 : Blo 346754 3183461 := bstep (se 4 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 3183461 = 596899) B596899
theorem B660467 : Blo 346754 660467 := bstep (se 1 (by rfl) ⟨495350, by rfl⟩ : syracuseStep 660467 = 990701) B990701
theorem B48534997 : Blo 346754 48534997 := bstep (se 7 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 48534997 = 1137539) B1137539
theorem B660953 : Blo 346754 660953 := bstep (se 2 (by rfl) ⟨247857, by rfl⟩ : syracuseStep 660953 = 495715) B495715
theorem B2233817 : Blo 346754 2233817 := bstep (se 2 (by rfl) ⟨837681, by rfl⟩ : syracuseStep 2233817 = 1675363) B1675363
theorem B989003 : Blo 346754 989003 := bstep (se 1 (by rfl) ⟨741752, by rfl⟩ : syracuseStep 989003 = 1483505) B1483505
theorem B497497 : Blo 346754 497497 := bstep (se 2 (by rfl) ⟨186561, by rfl⟩ : syracuseStep 497497 = 373123) B373123
theorem B1251217 : Blo 346754 1251217 := bstep (se 2 (by rfl) ⟨469206, by rfl⟩ : syracuseStep 1251217 = 938413) B938413
theorem B11409329 : Blo 346754 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B399287 : Blo 346754 399287 := bstep (se 1 (by rfl) ⟨299465, by rfl⟩ : syracuseStep 399287 = 598931) B598931
theorem B497611 : Blo 346754 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B1775681 : Blo 346754 1775681 := bstep (se 2 (by rfl) ⟨665880, by rfl⟩ : syracuseStep 1775681 = 1331761) B1331761
theorem B2824579 : Blo 346754 2824579 := bstep (se 1 (by rfl) ⟨2118434, by rfl⟩ : syracuseStep 2824579 = 4236869) B4236869
theorem B1481267 : Blo 346754 1481267 := bstep (se 1 (by rfl) ⟨1110950, by rfl⟩ : syracuseStep 1481267 = 2221901) B2221901
theorem B629299 : Blo 346754 629299 := bstep (se 1 (by rfl) ⟨471974, by rfl⟩ : syracuseStep 629299 = 943949) B943949
theorem B563801 : Blo 346754 563801 := bstep (se 2 (by rfl) ⟨211425, by rfl⟩ : syracuseStep 563801 = 422851) B422851
theorem B1481419 : Blo 346754 1481419 := bstep (se 1 (by rfl) ⟨1111064, by rfl⟩ : syracuseStep 1481419 = 2222129) B2222129
theorem B1481489 : Blo 346754 1481489 := bstep (se 2 (by rfl) ⟨555558, by rfl⟩ : syracuseStep 1481489 = 1111117) B1111117
theorem B662411 : Blo 346754 662411 := bstep (se 1 (by rfl) ⟨496808, by rfl⟩ : syracuseStep 662411 = 993617) B993617
theorem B891827 : Blo 346754 891827 := bstep (se 1 (by rfl) ⟨668870, by rfl⟩ : syracuseStep 891827 = 1337741) B1337741
theorem B662593 : Blo 346754 662593 := bstep (se 2 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 662593 = 496945) B496945
theorem B990301 : Blo 346754 990301 := bstep (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) B371363
theorem B498955 : Blo 346754 498955 := bstep (se 1 (by rfl) ⟨374216, by rfl⟩ : syracuseStep 498955 = 748433) B748433
theorem B990643 : Blo 346754 990643 := bstep (se 1 (by rfl) ⟨742982, by rfl⟩ : syracuseStep 990643 = 1485965) B1485965
theorem B1056203 : Blo 346754 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B663041 : Blo 346754 663041 := bstep (se 2 (by rfl) ⟨248640, by rfl⟩ : syracuseStep 663041 = 497281) B497281
theorem B3644945 : Blo 346754 3644945 := bstep (se 2 (by rfl) ⟨1366854, by rfl⟩ : syracuseStep 3644945 = 2733709) B2733709
theorem B499223 : Blo 346754 499223 := bstep (se 1 (by rfl) ⟨374417, by rfl⟩ : syracuseStep 499223 = 748835) B748835
theorem B532055 : Blo 346754 532055 := bstep (se 1 (by rfl) ⟨399041, by rfl⟩ : syracuseStep 532055 = 798083) B798083
theorem B663383 : Blo 346754 663383 := bstep (se 1 (by rfl) ⟨497537, by rfl⟩ : syracuseStep 663383 = 995075) B995075
theorem B1122137 : Blo 346754 1122137 := bstep (se 2 (by rfl) ⟨420801, by rfl⟩ : syracuseStep 1122137 = 841603) B841603
theorem B1122265 : Blo 346754 1122265 := bstep (se 2 (by rfl) ⟨420849, by rfl⟩ : syracuseStep 1122265 = 841699) B841699
theorem B2236481 : Blo 346754 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B1253555 : Blo 346754 1253555 := bstep (se 1 (by rfl) ⟨940166, by rfl⟩ : syracuseStep 1253555 = 1880333) B1880333
theorem B401611 : Blo 346754 401611 := bstep (se 1 (by rfl) ⟨301208, by rfl⟩ : syracuseStep 401611 = 602417) B602417
theorem B1286423 : Blo 346754 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B991577 : Blo 346754 991577 := bstep (se 2 (by rfl) ⟨371841, by rfl⟩ : syracuseStep 991577 = 743683) B743683
theorem B1057175 : Blo 346754 1057175 := bstep (se 1 (by rfl) ⟨792881, by rfl⟩ : syracuseStep 1057175 = 1585763) B1585763
theorem B1483181 : Blo 346754 1483181 := bstep (se 3 (by rfl) ⟨278096, by rfl⟩ : syracuseStep 1483181 = 556193) B556193
theorem B664051 : Blo 346754 664051 := bstep (se 1 (by rfl) ⟨498038, by rfl⟩ : syracuseStep 664051 = 996077) B996077
theorem B1319597 : Blo 346754 1319597 := bstep (se 3 (by rfl) ⟨247424, by rfl⟩ : syracuseStep 1319597 = 494849) B494849
theorem B1254275 : Blo 346754 1254275 := bstep (se 1 (by rfl) ⟨940706, by rfl⟩ : syracuseStep 1254275 = 1881413) B1881413
theorem B664499 : Blo 346754 664499 := bstep (se 1 (by rfl) ⟨498374, by rfl⟩ : syracuseStep 664499 = 996749) B996749
theorem B664537 : Blo 346754 664537 := bstep (se 2 (by rfl) ⟨249201, by rfl⟩ : syracuseStep 664537 = 498403) B498403
theorem B1483865 : Blo 346754 1483865 := bstep (se 2 (by rfl) ⟨556449, by rfl⟩ : syracuseStep 1483865 = 1112899) B1112899
theorem B664985 : Blo 346754 664985 := bstep (se 2 (by rfl) ⟨249369, by rfl⟩ : syracuseStep 664985 = 498739) B498739
theorem B1320371 : Blo 346754 1320371 := bstep (se 1 (by rfl) ⟨990278, by rfl⟩ : syracuseStep 1320371 = 1980557) B1980557
theorem B1058269 : Blo 346754 1058269 := bstep (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) B396851
theorem B2237969 : Blo 346754 2237969 := bstep (se 2 (by rfl) ⟨839238, by rfl⟩ : syracuseStep 2237969 = 1678477) B1678477
theorem B992989 : Blo 346754 992989 := bstep (se 3 (by rfl) ⟨186185, by rfl⟩ : syracuseStep 992989 = 372371) B372371
theorem B370603 : Blo 346754 370603 := bstep (se 1 (by rfl) ⟨277952, by rfl⟩ : syracuseStep 370603 = 555905) B555905
theorem B993217 : Blo 346754 993217 := bstep (se 2 (by rfl) ⟨372456, by rfl⟩ : syracuseStep 993217 = 744913) B744913
theorem B1419329 : Blo 346754 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B665729 : Blo 346754 665729 := bstep (se 2 (by rfl) ⟨249648, by rfl⟩ : syracuseStep 665729 = 499297) B499297
theorem B993559 : Blo 346754 993559 := bstep (se 1 (by rfl) ⟨745169, by rfl⟩ : syracuseStep 993559 = 1490339) B1490339
theorem B3352877 : Blo 346754 3352877 := bstep (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) B1257329
theorem B1583425 : Blo 346754 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B928279 : Blo 346754 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B5974883 : Blo 346754 5974883 := bstep (se 1 (by rfl) ⟨4481162, by rfl⟩ : syracuseStep 5974883 = 8962325) B8962325
theorem B1321859 : Blo 346754 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B994265 : Blo 346754 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B1682477 : Blo 346754 1682477 := bstep (se 3 (by rfl) ⟨315464, by rfl⟩ : syracuseStep 1682477 = 630929) B630929
theorem B4041859 : Blo 346754 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B1322315 : Blo 346754 1322315 := bstep (se 1 (by rfl) ⟨991736, by rfl⟩ : syracuseStep 1322315 = 1983473) B1983473
theorem B1322513 : Blo 346754 1322513 := bstep (se 2 (by rfl) ⟨495942, by rfl⟩ : syracuseStep 1322513 = 991885) B991885
theorem B896663 : Blo 346754 896663 := bstep (se 1 (by rfl) ⟨672497, by rfl⟩ : syracuseStep 896663 = 1344995) B1344995
theorem B6762341 : Blo 346754 6762341 := bstep (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) B1267939
theorem B1257389 : Blo 346754 1257389 := bstep (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) B471521
theorem B1585325 : Blo 346754 1585325 := bstep (se 3 (by rfl) ⟨297248, by rfl⟩ : syracuseStep 1585325 = 594497) B594497
theorem B798977 : Blo 346754 798977 := bstep (se 2 (by rfl) ⟨299616, by rfl⟩ : syracuseStep 798977 = 599233) B599233
theorem B1323287 : Blo 346754 1323287 := bstep (se 1 (by rfl) ⟨992465, by rfl⟩ : syracuseStep 1323287 = 1984931) B1984931
theorem B1487297 : Blo 346754 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B1421761 : Blo 346754 1421761 := bstep (se 2 (by rfl) ⟨533160, by rfl⟩ : syracuseStep 1421761 = 1066321) B1066321
theorem B1323485 : Blo 346754 1323485 := bstep (se 3 (by rfl) ⟨248153, by rfl⟩ : syracuseStep 1323485 = 496307) B496307
theorem B995905 : Blo 346754 995905 := bstep (se 2 (by rfl) ⟨373464, by rfl⟩ : syracuseStep 995905 = 746929) B746929
theorem B2994893 : Blo 346754 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B1487639 : Blo 346754 1487639 := bstep (se 1 (by rfl) ⟨1115729, by rfl⟩ : syracuseStep 1487639 = 2231459) B2231459
theorem B4469681 : Blo 346754 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B537625 : Blo 346754 537625 := bstep (se 2 (by rfl) ⟨201609, by rfl⟩ : syracuseStep 537625 = 403219) B403219
theorem B2307203 : Blo 346754 2307203 := bstep (se 1 (by rfl) ⟨1730402, by rfl⟩ : syracuseStep 2307203 = 3460805) B3460805
theorem B439435 : Blo 346754 439435 := bstep (se 1 (by rfl) ⟨329576, by rfl⟩ : syracuseStep 439435 = 659153) B659153
theorem B373943 : Blo 346754 373943 := bstep (se 1 (by rfl) ⟨280457, by rfl⟩ : syracuseStep 373943 = 560915) B560915
theorem B865753 : Blo 346754 865753 := bstep (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) B649315
theorem B1259059 : Blo 346754 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B1488563 : Blo 346754 1488563 := bstep (se 1 (by rfl) ⟨1116422, by rfl⟩ : syracuseStep 1488563 = 2232845) B2232845
theorem B899095 : Blo 346754 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B440407 : Blo 346754 440407 := bstep (se 1 (by rfl) ⟨330305, by rfl⟩ : syracuseStep 440407 = 660611) B660611
theorem B1325443 : Blo 346754 1325443 := bstep (se 1 (by rfl) ⟨994082, by rfl⟩ : syracuseStep 1325443 = 1988165) B1988165
theorem B1489553 : Blo 346754 1489553 := bstep (se 2 (by rfl) ⟨558582, by rfl⟩ : syracuseStep 1489553 = 1117165) B1117165
theorem B1325747 : Blo 346754 1325747 := bstep (se 1 (by rfl) ⟨994310, by rfl⟩ : syracuseStep 1325747 = 1988621) B1988621
theorem B670465 : Blo 346754 670465 := bstep (se 2 (by rfl) ⟨251424, by rfl⟩ : syracuseStep 670465 = 502849) B502849
theorem B2636549 : Blo 346754 2636549 := bstep (se 4 (by rfl) ⟨247176, by rfl⟩ : syracuseStep 2636549 = 494353) B494353
theorem B703283 : Blo 346754 703283 := bstep (se 1 (by rfl) ⟨527462, by rfl⟩ : syracuseStep 703283 = 1054925) B1054925
theorem B441227 : Blo 346754 441227 := bstep (se 1 (by rfl) ⟨330920, by rfl⟩ : syracuseStep 441227 = 661841) B661841
theorem B572375 : Blo 346754 572375 := bstep (se 1 (by rfl) ⟨429281, by rfl⟩ : syracuseStep 572375 = 858563) B858563
theorem B6339545 : Blo 346754 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B1326401 : Blo 346754 1326401 := bstep (se 2 (by rfl) ⟨497400, by rfl⟩ : syracuseStep 1326401 = 994801) B994801
theorem B1261079 : Blo 346754 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B441931 : Blo 346754 441931 := bstep (se 1 (by rfl) ⟨331448, by rfl⟩ : syracuseStep 441931 = 662897) B662897
theorem B638707 : Blo 346754 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B442199 : Blo 346754 442199 := bstep (se 1 (by rfl) ⟨331649, by rfl⟩ : syracuseStep 442199 = 663299) B663299
theorem B3063703 : Blo 346754 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B2834507 : Blo 346754 2834507 := bstep (se 1 (by rfl) ⟨2125880, by rfl⟩ : syracuseStep 2834507 = 4251761) B4251761
theorem B835991 : Blo 346754 835991 := bstep (se 1 (by rfl) ⟨626993, by rfl⟩ : syracuseStep 835991 = 1253987) B1253987
theorem B1524227 : Blo 346754 1524227 := bstep (se 1 (by rfl) ⟨1143170, by rfl⟩ : syracuseStep 1524227 = 2286341) B2286341
theorem B442903 : Blo 346754 442903 := bstep (se 1 (by rfl) ⟨332177, by rfl⟩ : syracuseStep 442903 = 664355) B664355
theorem B1327661 : Blo 346754 1327661 := bstep (se 3 (by rfl) ⟨248936, by rfl⟩ : syracuseStep 1327661 = 497873) B497873
theorem B1983041 : Blo 346754 1983041 := bstep (se 2 (by rfl) ⟨743640, by rfl⟩ : syracuseStep 1983041 = 1487281) B1487281
theorem B1327691 : Blo 346754 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B2507395 : Blo 346754 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B5653313 : Blo 346754 5653313 := bstep (se 2 (by rfl) ⟨2119992, by rfl⟩ : syracuseStep 5653313 = 4239985) B4239985
theorem B1491929 : Blo 346754 1491929 := bstep (se 2 (by rfl) ⟨559473, by rfl⟩ : syracuseStep 1491929 = 1118947) B1118947
theorem B1492013 : Blo 346754 1492013 := bstep (se 3 (by rfl) ⟨279752, by rfl⟩ : syracuseStep 1492013 = 559505) B559505
theorem B2638979 : Blo 346754 2638979 := bstep (se 1 (by rfl) ⟨1979234, by rfl⟩ : syracuseStep 2638979 = 3958469) B3958469
theorem B1328345 : Blo 346754 1328345 := bstep (se 2 (by rfl) ⟨498129, by rfl⟩ : syracuseStep 1328345 = 996259) B996259
theorem B1885457 : Blo 346754 1885457 := bstep (se 2 (by rfl) ⟨707046, by rfl⟩ : syracuseStep 1885457 = 1414093) B1414093
theorem B378155 : Blo 346754 378155 := bstep (se 1 (by rfl) ⟨283616, by rfl⟩ : syracuseStep 378155 = 567233) B567233
theorem B837067 : Blo 346754 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B706009 : Blo 346754 706009 := bstep (se 2 (by rfl) ⟨264753, by rfl⟩ : syracuseStep 706009 = 529507) B529507
theorem B837143 : Blo 346754 837143 := bstep (se 1 (by rfl) ⟨627857, by rfl⟩ : syracuseStep 837143 = 1255715) B1255715
theorem B1328663 : Blo 346754 1328663 := bstep (se 1 (by rfl) ⟨996497, by rfl⟩ : syracuseStep 1328663 = 1992995) B1992995
theorem B378475 : Blo 346754 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B2148113 : Blo 346754 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B2377603 : Blo 346754 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B2508893 : Blo 346754 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B1886339 : Blo 346754 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B1329331 : Blo 346754 1329331 := bstep (se 1 (by rfl) ⟨996998, by rfl⟩ : syracuseStep 1329331 = 1993997) B1993997
theorem B1263961 : Blo 346754 1263961 := bstep (se 2 (by rfl) ⟨473985, by rfl⟩ : syracuseStep 1263961 = 947971) B947971
theorem B3951179 : Blo 346754 3951179 := bstep (se 1 (by rfl) ⟨2963384, by rfl⟩ : syracuseStep 3951179 = 5926769) B5926769
theorem B707201 : Blo 346754 707201 := bstep (se 2 (by rfl) ⟨265200, by rfl⟩ : syracuseStep 707201 = 530401) B530401
theorem B346763 : Blo 346754 346763 := bstep (se 1 (by rfl) ⟨260072, by rfl⟩ : syracuseStep 346763 = 520145) B520145
theorem B346775 : Blo 346754 346775 := bstep (se 1 (by rfl) ⟨260081, by rfl⟩ : syracuseStep 346775 = 520163) B520163
theorem B346795 : Blo 346754 346795 := bstep (se 1 (by rfl) ⟨260096, by rfl⟩ : syracuseStep 346795 = 520193) B520193
theorem B346807 : Blo 346754 346807 := bstep (se 1 (by rfl) ⟨260105, by rfl⟩ : syracuseStep 346807 = 520211) B520211
theorem B346827 : Blo 346754 346827 := bstep (se 1 (by rfl) ⟨260120, by rfl⟩ : syracuseStep 346827 = 520241) B520241
theorem B346839 : Blo 346754 346839 := bstep (se 1 (by rfl) ⟨260129, by rfl⟩ : syracuseStep 346839 = 520259) B520259
theorem B346859 : Blo 346754 346859 := bstep (se 1 (by rfl) ⟨260144, by rfl⟩ : syracuseStep 346859 = 520289) B520289
theorem B346871 : Blo 346754 346871 := bstep (se 1 (by rfl) ⟨260153, by rfl⟩ : syracuseStep 346871 = 520307) B520307
theorem B346891 : Blo 346754 346891 := bstep (se 1 (by rfl) ⟨260168, by rfl⟩ : syracuseStep 346891 = 520337) B520337
theorem B346903 : Blo 346754 346903 := bstep (se 1 (by rfl) ⟨260177, by rfl⟩ : syracuseStep 346903 = 520355) B520355
theorem B346923 : Blo 346754 346923 := bstep (se 1 (by rfl) ⟨260192, by rfl⟩ : syracuseStep 346923 = 520385) B520385
theorem B838451 : Blo 346754 838451 := bstep (se 1 (by rfl) ⟨628838, by rfl⟩ : syracuseStep 838451 = 1257677) B1257677
theorem B346935 : Blo 346754 346935 := bstep (se 1 (by rfl) ⟨260201, by rfl⟩ : syracuseStep 346935 = 520403) B520403
theorem B346955 : Blo 346754 346955 := bstep (se 1 (by rfl) ⟨260216, by rfl⟩ : syracuseStep 346955 = 520433) B520433
theorem B346967 : Blo 346754 346967 := bstep (se 1 (by rfl) ⟨260225, by rfl⟩ : syracuseStep 346967 = 520451) B520451
theorem B346987 : Blo 346754 346987 := bstep (se 1 (by rfl) ⟨260240, by rfl⟩ : syracuseStep 346987 = 520481) B520481
theorem B346999 : Blo 346754 346999 := bstep (se 1 (by rfl) ⟨260249, by rfl⟩ : syracuseStep 346999 = 520499) B520499
theorem B347019 : Blo 346754 347019 := bstep (se 1 (by rfl) ⟨260264, by rfl⟩ : syracuseStep 347019 = 520529) B520529
theorem B347031 : Blo 346754 347031 := bstep (se 1 (by rfl) ⟨260273, by rfl⟩ : syracuseStep 347031 = 520547) B520547
theorem B1985431 : Blo 346754 1985431 := bstep (se 1 (by rfl) ⟨1489073, by rfl⟩ : syracuseStep 1985431 = 2978147) B2978147
theorem B347051 : Blo 346754 347051 := bstep (se 1 (by rfl) ⟨260288, by rfl⟩ : syracuseStep 347051 = 520577) B520577
theorem B3197873 : Blo 346754 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B347063 : Blo 346754 347063 := bstep (se 1 (by rfl) ⟨260297, by rfl⟩ : syracuseStep 347063 = 520595) B520595
theorem B347083 : Blo 346754 347083 := bstep (se 1 (by rfl) ⟨260312, by rfl⟩ : syracuseStep 347083 = 520625) B520625
theorem B347095 : Blo 346754 347095 := bstep (se 1 (by rfl) ⟨260321, by rfl⟩ : syracuseStep 347095 = 520643) B520643
theorem B347115 : Blo 346754 347115 := bstep (se 1 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 347115 = 520673) B520673
theorem B347127 : Blo 346754 347127 := bstep (se 1 (by rfl) ⟨260345, by rfl⟩ : syracuseStep 347127 = 520691) B520691
theorem B347147 : Blo 346754 347147 := bstep (se 1 (by rfl) ⟨260360, by rfl⟩ : syracuseStep 347147 = 520721) B520721
theorem B347159 : Blo 346754 347159 := bstep (se 1 (by rfl) ⟨260369, by rfl⟩ : syracuseStep 347159 = 520739) B520739
theorem B347179 : Blo 346754 347179 := bstep (se 1 (by rfl) ⟨260384, by rfl⟩ : syracuseStep 347179 = 520769) B520769
theorem B347191 : Blo 346754 347191 := bstep (se 1 (by rfl) ⟨260393, by rfl⟩ : syracuseStep 347191 = 520787) B520787
theorem B347211 : Blo 346754 347211 := bstep (se 1 (by rfl) ⟨260408, by rfl⟩ : syracuseStep 347211 = 520817) B520817
theorem B347223 : Blo 346754 347223 := bstep (se 1 (by rfl) ⟨260417, by rfl⟩ : syracuseStep 347223 = 520835) B520835
theorem B347243 : Blo 346754 347243 := bstep (se 1 (by rfl) ⟨260432, by rfl⟩ : syracuseStep 347243 = 520865) B520865
theorem B347255 : Blo 346754 347255 := bstep (se 1 (by rfl) ⟨260441, by rfl⟩ : syracuseStep 347255 = 520883) B520883
theorem B347275 : Blo 346754 347275 := bstep (se 1 (by rfl) ⟨260456, by rfl⟩ : syracuseStep 347275 = 520913) B520913
theorem B10112141 : Blo 346754 10112141 := bstep (se 3 (by rfl) ⟨1896026, by rfl⟩ : syracuseStep 10112141 = 3792053) B3792053
theorem B347287 : Blo 346754 347287 := bstep (se 1 (by rfl) ⟨260465, by rfl⟩ : syracuseStep 347287 = 520931) B520931
theorem B347307 : Blo 346754 347307 := bstep (se 1 (by rfl) ⟨260480, by rfl⟩ : syracuseStep 347307 = 520961) B520961
theorem B347319 : Blo 346754 347319 := bstep (se 1 (by rfl) ⟨260489, by rfl⟩ : syracuseStep 347319 = 520979) B520979
theorem B347339 : Blo 346754 347339 := bstep (se 1 (by rfl) ⟨260504, by rfl⟩ : syracuseStep 347339 = 521009) B521009
theorem B347351 : Blo 346754 347351 := bstep (se 1 (by rfl) ⟨260513, by rfl⟩ : syracuseStep 347351 = 521027) B521027
theorem B347371 : Blo 346754 347371 := bstep (se 1 (by rfl) ⟨260528, by rfl⟩ : syracuseStep 347371 = 521057) B521057
theorem B347383 : Blo 346754 347383 := bstep (se 1 (by rfl) ⟨260537, by rfl⟩ : syracuseStep 347383 = 521075) B521075
theorem B347403 : Blo 346754 347403 := bstep (se 1 (by rfl) ⟨260552, by rfl⟩ : syracuseStep 347403 = 521105) B521105
theorem B347415 : Blo 346754 347415 := bstep (se 1 (by rfl) ⟨260561, by rfl⟩ : syracuseStep 347415 = 521123) B521123
theorem B347435 : Blo 346754 347435 := bstep (se 1 (by rfl) ⟨260576, by rfl⟩ : syracuseStep 347435 = 521153) B521153
theorem B740659 : Blo 346754 740659 := bstep (se 1 (by rfl) ⟨555494, by rfl⟩ : syracuseStep 740659 = 1110989) B1110989
theorem B347447 : Blo 346754 347447 := bstep (se 1 (by rfl) ⟨260585, by rfl⟩ : syracuseStep 347447 = 521171) B521171
theorem B347467 : Blo 346754 347467 := bstep (se 1 (by rfl) ⟨260600, by rfl⟩ : syracuseStep 347467 = 521201) B521201
theorem B347479 : Blo 346754 347479 := bstep (se 1 (by rfl) ⟨260609, by rfl⟩ : syracuseStep 347479 = 521219) B521219
theorem B347499 : Blo 346754 347499 := bstep (se 1 (by rfl) ⟨260624, by rfl⟩ : syracuseStep 347499 = 521249) B521249
theorem B347511 : Blo 346754 347511 := bstep (se 1 (by rfl) ⟨260633, by rfl⟩ : syracuseStep 347511 = 521267) B521267
theorem B347531 : Blo 346754 347531 := bstep (se 1 (by rfl) ⟨260648, by rfl⟩ : syracuseStep 347531 = 521297) B521297
theorem B1330577 : Blo 346754 1330577 := bstep (se 2 (by rfl) ⟨498966, by rfl⟩ : syracuseStep 1330577 = 997933) B997933
theorem B347543 : Blo 346754 347543 := bstep (se 1 (by rfl) ⟨260657, by rfl⟩ : syracuseStep 347543 = 521315) B521315
theorem B347563 : Blo 346754 347563 := bstep (se 1 (by rfl) ⟨260672, by rfl⟩ : syracuseStep 347563 = 521345) B521345
theorem B347575 : Blo 346754 347575 := bstep (se 1 (by rfl) ⟨260681, by rfl⟩ : syracuseStep 347575 = 521363) B521363
theorem B839105 : Blo 346754 839105 := bstep (se 2 (by rfl) ⟨314664, by rfl⟩ : syracuseStep 839105 = 629329) B629329
theorem B347595 : Blo 346754 347595 := bstep (se 1 (by rfl) ⟨260696, by rfl⟩ : syracuseStep 347595 = 521393) B521393
theorem B347607 : Blo 346754 347607 := bstep (se 1 (by rfl) ⟨260705, by rfl⟩ : syracuseStep 347607 = 521411) B521411
theorem B347627 : Blo 346754 347627 := bstep (se 1 (by rfl) ⟨260720, by rfl⟩ : syracuseStep 347627 = 521441) B521441
theorem B347639 : Blo 346754 347639 := bstep (se 1 (by rfl) ⟨260729, by rfl⟩ : syracuseStep 347639 = 521459) B521459
theorem B347659 : Blo 346754 347659 := bstep (se 1 (by rfl) ⟨260744, by rfl⟩ : syracuseStep 347659 = 521489) B521489
theorem B347671 : Blo 346754 347671 := bstep (se 1 (by rfl) ⟨260753, by rfl⟩ : syracuseStep 347671 = 521507) B521507
theorem B347691 : Blo 346754 347691 := bstep (se 1 (by rfl) ⟨260768, by rfl⟩ : syracuseStep 347691 = 521537) B521537
theorem B740915 : Blo 346754 740915 := bstep (se 1 (by rfl) ⟨555686, by rfl⟩ : syracuseStep 740915 = 1111373) B1111373
theorem B347703 : Blo 346754 347703 := bstep (se 1 (by rfl) ⟨260777, by rfl⟩ : syracuseStep 347703 = 521555) B521555
theorem B347723 : Blo 346754 347723 := bstep (se 1 (by rfl) ⟨260792, by rfl⟩ : syracuseStep 347723 = 521585) B521585
theorem B347735 : Blo 346754 347735 := bstep (se 1 (by rfl) ⟨260801, by rfl⟩ : syracuseStep 347735 = 521603) B521603
theorem B347755 : Blo 346754 347755 := bstep (se 1 (by rfl) ⟨260816, by rfl⟩ : syracuseStep 347755 = 521633) B521633
theorem B347767 : Blo 346754 347767 := bstep (se 1 (by rfl) ⟨260825, by rfl⟩ : syracuseStep 347767 = 521651) B521651
theorem B347787 : Blo 346754 347787 := bstep (se 1 (by rfl) ⟨260840, by rfl⟩ : syracuseStep 347787 = 521681) B521681
theorem B347799 : Blo 346754 347799 := bstep (se 1 (by rfl) ⟨260849, by rfl⟩ : syracuseStep 347799 = 521699) B521699
theorem B347819 : Blo 346754 347819 := bstep (se 1 (by rfl) ⟨260864, by rfl⟩ : syracuseStep 347819 = 521729) B521729
theorem B347831 : Blo 346754 347831 := bstep (se 1 (by rfl) ⟨260873, by rfl⟩ : syracuseStep 347831 = 521747) B521747
theorem B347851 : Blo 346754 347851 := bstep (se 1 (by rfl) ⟨260888, by rfl⟩ : syracuseStep 347851 = 521777) B521777
theorem B347863 : Blo 346754 347863 := bstep (se 1 (by rfl) ⟨260897, by rfl⟩ : syracuseStep 347863 = 521795) B521795
theorem B1756889 : Blo 346754 1756889 := bstep (se 2 (by rfl) ⟨658833, by rfl⟩ : syracuseStep 1756889 = 1317667) B1317667
theorem B347883 : Blo 346754 347883 := bstep (se 1 (by rfl) ⟨260912, by rfl⟩ : syracuseStep 347883 = 521825) B521825
theorem B347895 : Blo 346754 347895 := bstep (se 1 (by rfl) ⟨260921, by rfl⟩ : syracuseStep 347895 = 521843) B521843
theorem B347915 : Blo 346754 347915 := bstep (se 1 (by rfl) ⟨260936, by rfl⟩ : syracuseStep 347915 = 521873) B521873
theorem B347927 : Blo 346754 347927 := bstep (se 1 (by rfl) ⟨260945, by rfl⟩ : syracuseStep 347927 = 521891) B521891
theorem B347947 : Blo 346754 347947 := bstep (se 1 (by rfl) ⟨260960, by rfl⟩ : syracuseStep 347947 = 521921) B521921
theorem B347959 : Blo 346754 347959 := bstep (se 1 (by rfl) ⟨260969, by rfl⟩ : syracuseStep 347959 = 521939) B521939
theorem B347979 : Blo 346754 347979 := bstep (se 1 (by rfl) ⟨260984, by rfl⟩ : syracuseStep 347979 = 521969) B521969
theorem B347991 : Blo 346754 347991 := bstep (se 1 (by rfl) ⟨260993, by rfl⟩ : syracuseStep 347991 = 521987) B521987
theorem B348011 : Blo 346754 348011 := bstep (se 1 (by rfl) ⟨261008, by rfl⟩ : syracuseStep 348011 = 522017) B522017
theorem B348023 : Blo 346754 348023 := bstep (se 1 (by rfl) ⟨261017, by rfl⟩ : syracuseStep 348023 = 522035) B522035
theorem B348043 : Blo 346754 348043 := bstep (se 1 (by rfl) ⟨261032, by rfl⟩ : syracuseStep 348043 = 522065) B522065
theorem B348055 : Blo 346754 348055 := bstep (se 1 (by rfl) ⟨261041, by rfl⟩ : syracuseStep 348055 = 522083) B522083
theorem B348075 : Blo 346754 348075 := bstep (se 1 (by rfl) ⟨261056, by rfl⟩ : syracuseStep 348075 = 522113) B522113
theorem B839603 : Blo 346754 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B348087 : Blo 346754 348087 := bstep (se 1 (by rfl) ⟨261065, by rfl⟩ : syracuseStep 348087 = 522131) B522131
theorem B348107 : Blo 346754 348107 := bstep (se 1 (by rfl) ⟨261080, by rfl⟩ : syracuseStep 348107 = 522161) B522161
theorem B2510797 : Blo 346754 2510797 := bstep (se 3 (by rfl) ⟨470774, by rfl⟩ : syracuseStep 2510797 = 941549) B941549
theorem B348119 : Blo 346754 348119 := bstep (se 1 (by rfl) ⟨261089, by rfl⟩ : syracuseStep 348119 = 522179) B522179
theorem B348139 : Blo 346754 348139 := bstep (se 1 (by rfl) ⟨261104, by rfl⟩ : syracuseStep 348139 = 522209) B522209
theorem B348151 : Blo 346754 348151 := bstep (se 1 (by rfl) ⟨261113, by rfl⟩ : syracuseStep 348151 = 522227) B522227
theorem B348171 : Blo 346754 348171 := bstep (se 1 (by rfl) ⟨261128, by rfl⟩ : syracuseStep 348171 = 522257) B522257
theorem B348183 : Blo 346754 348183 := bstep (se 1 (by rfl) ⟨261137, by rfl⟩ : syracuseStep 348183 = 522275) B522275
theorem B348203 : Blo 346754 348203 := bstep (se 1 (by rfl) ⟨261152, by rfl⟩ : syracuseStep 348203 = 522305) B522305
theorem B348215 : Blo 346754 348215 := bstep (se 1 (by rfl) ⟨261161, by rfl⟩ : syracuseStep 348215 = 522323) B522323
theorem B348235 : Blo 346754 348235 := bstep (se 1 (by rfl) ⟨261176, by rfl⟩ : syracuseStep 348235 = 522353) B522353
theorem B1331275 : Blo 346754 1331275 := bstep (se 1 (by rfl) ⟨998456, by rfl⟩ : syracuseStep 1331275 = 1996913) B1996913
theorem B348247 : Blo 346754 348247 := bstep (se 1 (by rfl) ⟨261185, by rfl⟩ : syracuseStep 348247 = 522371) B522371
theorem B348267 : Blo 346754 348267 := bstep (se 1 (by rfl) ⟨261200, by rfl⟩ : syracuseStep 348267 = 522401) B522401
theorem B348279 : Blo 346754 348279 := bstep (se 1 (by rfl) ⟨261209, by rfl⟩ : syracuseStep 348279 = 522419) B522419
theorem B348299 : Blo 346754 348299 := bstep (se 1 (by rfl) ⟨261224, by rfl⟩ : syracuseStep 348299 = 522449) B522449
theorem B348311 : Blo 346754 348311 := bstep (se 1 (by rfl) ⟨261233, by rfl⟩ : syracuseStep 348311 = 522467) B522467
theorem B348331 : Blo 346754 348331 := bstep (se 1 (by rfl) ⟨261248, by rfl⟩ : syracuseStep 348331 = 522497) B522497
theorem B348343 : Blo 346754 348343 := bstep (se 1 (by rfl) ⟨261257, by rfl⟩ : syracuseStep 348343 = 522515) B522515
theorem B348363 : Blo 346754 348363 := bstep (se 1 (by rfl) ⟨261272, by rfl⟩ : syracuseStep 348363 = 522545) B522545
theorem B348375 : Blo 346754 348375 := bstep (se 1 (by rfl) ⟨261281, by rfl⟩ : syracuseStep 348375 = 522563) B522563
theorem B348395 : Blo 346754 348395 := bstep (se 1 (by rfl) ⟨261296, by rfl⟩ : syracuseStep 348395 = 522593) B522593
theorem B348407 : Blo 346754 348407 := bstep (se 1 (by rfl) ⟨261305, by rfl⟩ : syracuseStep 348407 = 522611) B522611
theorem B348427 : Blo 346754 348427 := bstep (se 1 (by rfl) ⟨261320, by rfl⟩ : syracuseStep 348427 = 522641) B522641
theorem B348439 : Blo 346754 348439 := bstep (se 1 (by rfl) ⟨261329, by rfl⟩ : syracuseStep 348439 = 522659) B522659
theorem B348459 : Blo 346754 348459 := bstep (se 1 (by rfl) ⟨261344, by rfl⟩ : syracuseStep 348459 = 522689) B522689
theorem B348471 : Blo 346754 348471 := bstep (se 1 (by rfl) ⟨261353, by rfl⟩ : syracuseStep 348471 = 522707) B522707
theorem B1495361 : Blo 346754 1495361 := bstep (se 2 (by rfl) ⟨560760, by rfl⟩ : syracuseStep 1495361 = 1121521) B1121521
theorem B348491 : Blo 346754 348491 := bstep (se 1 (by rfl) ⟨261368, by rfl⟩ : syracuseStep 348491 = 522737) B522737
theorem B348503 : Blo 346754 348503 := bstep (se 1 (by rfl) ⟨261377, by rfl⟩ : syracuseStep 348503 = 522755) B522755
theorem B1331549 : Blo 346754 1331549 := bstep (se 3 (by rfl) ⟨249665, by rfl⟩ : syracuseStep 1331549 = 499331) B499331
theorem B348523 : Blo 346754 348523 := bstep (se 1 (by rfl) ⟨261392, by rfl⟩ : syracuseStep 348523 = 522785) B522785
theorem B348535 : Blo 346754 348535 := bstep (se 1 (by rfl) ⟨261401, by rfl⟩ : syracuseStep 348535 = 522803) B522803
theorem B348555 : Blo 346754 348555 := bstep (se 1 (by rfl) ⟨261416, by rfl⟩ : syracuseStep 348555 = 522833) B522833
theorem B348567 : Blo 346754 348567 := bstep (se 1 (by rfl) ⟨261425, by rfl⟩ : syracuseStep 348567 = 522851) B522851
theorem B348587 : Blo 346754 348587 := bstep (se 1 (by rfl) ⟨261440, by rfl⟩ : syracuseStep 348587 = 522881) B522881
theorem B348599 : Blo 346754 348599 := bstep (se 1 (by rfl) ⟨261449, by rfl⟩ : syracuseStep 348599 = 522899) B522899
theorem B348619 : Blo 346754 348619 := bstep (se 1 (by rfl) ⟨261464, by rfl⟩ : syracuseStep 348619 = 522929) B522929
theorem B2642381 : Blo 346754 2642381 := bstep (se 3 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 2642381 = 990893) B990893
theorem B348631 : Blo 346754 348631 := bstep (se 1 (by rfl) ⟨261473, by rfl⟩ : syracuseStep 348631 = 522947) B522947
theorem B348651 : Blo 346754 348651 := bstep (se 1 (by rfl) ⟨261488, by rfl⟩ : syracuseStep 348651 = 522977) B522977
theorem B348663 : Blo 346754 348663 := bstep (se 1 (by rfl) ⟨261497, by rfl⟩ : syracuseStep 348663 = 522995) B522995
theorem B741889 : Blo 346754 741889 := bstep (se 2 (by rfl) ⟨278208, by rfl⟩ : syracuseStep 741889 = 556417) B556417
theorem B348683 : Blo 346754 348683 := bstep (se 1 (by rfl) ⟨261512, by rfl⟩ : syracuseStep 348683 = 523025) B523025
theorem B348695 : Blo 346754 348695 := bstep (se 1 (by rfl) ⟨261521, by rfl⟩ : syracuseStep 348695 = 523043) B523043
theorem B348715 : Blo 346754 348715 := bstep (se 1 (by rfl) ⟨261536, by rfl⟩ : syracuseStep 348715 = 523073) B523073
theorem B348727 : Blo 346754 348727 := bstep (se 1 (by rfl) ⟨261545, by rfl⟩ : syracuseStep 348727 = 523091) B523091
theorem B348747 : Blo 346754 348747 := bstep (se 1 (by rfl) ⟨261560, by rfl⟩ : syracuseStep 348747 = 523121) B523121
theorem B348759 : Blo 346754 348759 := bstep (se 1 (by rfl) ⟨261569, by rfl⟩ : syracuseStep 348759 = 523139) B523139
theorem B348779 : Blo 346754 348779 := bstep (se 1 (by rfl) ⟨261584, by rfl⟩ : syracuseStep 348779 = 523169) B523169
theorem B348791 : Blo 346754 348791 := bstep (se 1 (by rfl) ⟨261593, by rfl⟩ : syracuseStep 348791 = 523187) B523187
theorem B348811 : Blo 346754 348811 := bstep (se 1 (by rfl) ⟨261608, by rfl⟩ : syracuseStep 348811 = 523217) B523217
theorem B348823 : Blo 346754 348823 := bstep (se 1 (by rfl) ⟨261617, by rfl⟩ : syracuseStep 348823 = 523235) B523235
theorem B348843 : Blo 346754 348843 := bstep (se 1 (by rfl) ⟨261632, by rfl⟩ : syracuseStep 348843 = 523265) B523265
theorem B348855 : Blo 346754 348855 := bstep (se 1 (by rfl) ⟨261641, by rfl⟩ : syracuseStep 348855 = 523283) B523283
theorem B348875 : Blo 346754 348875 := bstep (se 1 (by rfl) ⟨261656, by rfl⟩ : syracuseStep 348875 = 523313) B523313
theorem B348887 : Blo 346754 348887 := bstep (se 1 (by rfl) ⟨261665, by rfl⟩ : syracuseStep 348887 = 523331) B523331
theorem B348907 : Blo 346754 348907 := bstep (se 1 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 348907 = 523361) B523361
theorem B348919 : Blo 346754 348919 := bstep (se 1 (by rfl) ⟨261689, by rfl⟩ : syracuseStep 348919 = 523379) B523379
theorem B348939 : Blo 346754 348939 := bstep (se 1 (by rfl) ⟨261704, by rfl⟩ : syracuseStep 348939 = 523409) B523409
theorem B348951 : Blo 346754 348951 := bstep (se 1 (by rfl) ⟨261713, by rfl⟩ : syracuseStep 348951 = 523427) B523427
theorem B348971 : Blo 346754 348971 := bstep (se 1 (by rfl) ⟨261728, by rfl⟩ : syracuseStep 348971 = 523457) B523457
theorem B2380589 : Blo 346754 2380589 := bstep (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) B892721
theorem B24171317 : Blo 346754 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B348983 : Blo 346754 348983 := bstep (se 1 (by rfl) ⟨261737, by rfl⟩ : syracuseStep 348983 = 523475) B523475
theorem B349003 : Blo 346754 349003 := bstep (se 1 (by rfl) ⟨261752, by rfl⟩ : syracuseStep 349003 = 523505) B523505
theorem B349015 : Blo 346754 349015 := bstep (se 1 (by rfl) ⟨261761, by rfl⟩ : syracuseStep 349015 = 523523) B523523
theorem B349035 : Blo 346754 349035 := bstep (se 1 (by rfl) ⟨261776, by rfl⟩ : syracuseStep 349035 = 523553) B523553
theorem B349047 : Blo 346754 349047 := bstep (se 1 (by rfl) ⟨261785, by rfl⟩ : syracuseStep 349047 = 523571) B523571
theorem B349067 : Blo 346754 349067 := bstep (se 1 (by rfl) ⟨261800, by rfl⟩ : syracuseStep 349067 = 523601) B523601
theorem B349079 : Blo 346754 349079 := bstep (se 1 (by rfl) ⟨261809, by rfl⟩ : syracuseStep 349079 = 523619) B523619
theorem B349099 : Blo 346754 349099 := bstep (se 1 (by rfl) ⟨261824, by rfl⟩ : syracuseStep 349099 = 523649) B523649
theorem B2642867 : Blo 346754 2642867 := bstep (se 1 (by rfl) ⟨1982150, by rfl⟩ : syracuseStep 2642867 = 3964301) B3964301
theorem B349111 : Blo 346754 349111 := bstep (se 1 (by rfl) ⟨261833, by rfl⟩ : syracuseStep 349111 = 523667) B523667
theorem B349131 : Blo 346754 349131 := bstep (se 1 (by rfl) ⟨261848, by rfl⟩ : syracuseStep 349131 = 523697) B523697
theorem B349143 : Blo 346754 349143 := bstep (se 1 (by rfl) ⟨261857, by rfl⟩ : syracuseStep 349143 = 523715) B523715
theorem B1496029 : Blo 346754 1496029 := bstep (se 3 (by rfl) ⟨280505, by rfl⟩ : syracuseStep 1496029 = 561011) B561011
theorem B349163 : Blo 346754 349163 := bstep (se 1 (by rfl) ⟨261872, by rfl⟩ : syracuseStep 349163 = 523745) B523745
theorem B349175 : Blo 346754 349175 := bstep (se 1 (by rfl) ⟨261881, by rfl⟩ : syracuseStep 349175 = 523763) B523763
theorem B349195 : Blo 346754 349195 := bstep (se 1 (by rfl) ⟨261896, by rfl⟩ : syracuseStep 349195 = 523793) B523793
theorem B349207 : Blo 346754 349207 := bstep (se 1 (by rfl) ⟨261905, by rfl⟩ : syracuseStep 349207 = 523811) B523811
theorem B349227 : Blo 346754 349227 := bstep (se 1 (by rfl) ⟨261920, by rfl⟩ : syracuseStep 349227 = 523841) B523841
theorem B349239 : Blo 346754 349239 := bstep (se 1 (by rfl) ⟨261929, by rfl⟩ : syracuseStep 349239 = 523859) B523859
theorem B349259 : Blo 346754 349259 := bstep (se 1 (by rfl) ⟨261944, by rfl⟩ : syracuseStep 349259 = 523889) B523889
theorem B349271 : Blo 346754 349271 := bstep (se 1 (by rfl) ⟨261953, by rfl⟩ : syracuseStep 349271 = 523907) B523907
theorem B349291 : Blo 346754 349291 := bstep (se 1 (by rfl) ⟨261968, by rfl⟩ : syracuseStep 349291 = 523937) B523937
theorem B349303 : Blo 346754 349303 := bstep (se 1 (by rfl) ⟨261977, by rfl⟩ : syracuseStep 349303 = 523955) B523955
theorem B349323 : Blo 346754 349323 := bstep (se 1 (by rfl) ⟨261992, by rfl⟩ : syracuseStep 349323 = 523985) B523985
theorem B349335 : Blo 346754 349335 := bstep (se 1 (by rfl) ⟨262001, by rfl⟩ : syracuseStep 349335 = 524003) B524003
theorem B742553 : Blo 346754 742553 := bstep (se 2 (by rfl) ⟨278457, by rfl⟩ : syracuseStep 742553 = 556915) B556915
theorem B349355 : Blo 346754 349355 := bstep (se 1 (by rfl) ⟨262016, by rfl⟩ : syracuseStep 349355 = 524033) B524033
theorem B349367 : Blo 346754 349367 := bstep (se 1 (by rfl) ⟨262025, by rfl⟩ : syracuseStep 349367 = 524051) B524051
theorem B349387 : Blo 346754 349387 := bstep (se 1 (by rfl) ⟨262040, by rfl⟩ : syracuseStep 349387 = 524081) B524081
theorem B349399 : Blo 346754 349399 := bstep (se 1 (by rfl) ⟨262049, by rfl⟩ : syracuseStep 349399 = 524099) B524099
theorem B349419 : Blo 346754 349419 := bstep (se 1 (by rfl) ⟨262064, by rfl⟩ : syracuseStep 349419 = 524129) B524129
theorem B349431 : Blo 346754 349431 := bstep (se 1 (by rfl) ⟨262073, by rfl⟩ : syracuseStep 349431 = 524147) B524147
theorem B349451 : Blo 346754 349451 := bstep (se 1 (by rfl) ⟨262088, by rfl⟩ : syracuseStep 349451 = 524177) B524177
theorem B349463 : Blo 346754 349463 := bstep (se 1 (by rfl) ⟨262097, by rfl⟩ : syracuseStep 349463 = 524195) B524195
theorem B349483 : Blo 346754 349483 := bstep (se 1 (by rfl) ⟨262112, by rfl⟩ : syracuseStep 349483 = 524225) B524225
theorem B1758509 : Blo 346754 1758509 := bstep (se 3 (by rfl) ⟨329720, by rfl⟩ : syracuseStep 1758509 = 659441) B659441
theorem B349495 : Blo 346754 349495 := bstep (se 1 (by rfl) ⟨262121, by rfl⟩ : syracuseStep 349495 = 524243) B524243
theorem B349515 : Blo 346754 349515 := bstep (se 1 (by rfl) ⟨262136, by rfl⟩ : syracuseStep 349515 = 524273) B524273
theorem B349527 : Blo 346754 349527 := bstep (se 1 (by rfl) ⟨262145, by rfl⟩ : syracuseStep 349527 = 524291) B524291
theorem B349547 : Blo 346754 349547 := bstep (se 1 (by rfl) ⟨262160, by rfl⟩ : syracuseStep 349547 = 524321) B524321
theorem B349559 : Blo 346754 349559 := bstep (se 1 (by rfl) ⟨262169, by rfl⟩ : syracuseStep 349559 = 524339) B524339
theorem B349579 : Blo 346754 349579 := bstep (se 1 (by rfl) ⟨262184, by rfl⟩ : syracuseStep 349579 = 524369) B524369
theorem B349591 : Blo 346754 349591 := bstep (se 1 (by rfl) ⟨262193, by rfl⟩ : syracuseStep 349591 = 524387) B524387
theorem B710039 : Blo 346754 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B349611 : Blo 346754 349611 := bstep (se 1 (by rfl) ⟨262208, by rfl⟩ : syracuseStep 349611 = 524417) B524417
theorem B349623 : Blo 346754 349623 := bstep (se 1 (by rfl) ⟨262217, by rfl⟩ : syracuseStep 349623 = 524435) B524435
theorem B349643 : Blo 346754 349643 := bstep (se 1 (by rfl) ⟨262232, by rfl⟩ : syracuseStep 349643 = 524465) B524465
theorem B349655 : Blo 346754 349655 := bstep (se 1 (by rfl) ⟨262241, by rfl⟩ : syracuseStep 349655 = 524483) B524483
theorem B349675 : Blo 346754 349675 := bstep (se 1 (by rfl) ⟨262256, by rfl⟩ : syracuseStep 349675 = 524513) B524513
theorem B349687 : Blo 346754 349687 := bstep (se 1 (by rfl) ⟨262265, by rfl⟩ : syracuseStep 349687 = 524531) B524531
theorem B349707 : Blo 346754 349707 := bstep (se 1 (by rfl) ⟨262280, by rfl⟩ : syracuseStep 349707 = 524561) B524561
theorem B349719 : Blo 346754 349719 := bstep (se 1 (by rfl) ⟨262289, by rfl⟩ : syracuseStep 349719 = 524579) B524579
theorem B349739 : Blo 346754 349739 := bstep (se 1 (by rfl) ⟨262304, by rfl⟩ : syracuseStep 349739 = 524609) B524609
theorem B1496627 : Blo 346754 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B349751 : Blo 346754 349751 := bstep (se 1 (by rfl) ⟨262313, by rfl⟩ : syracuseStep 349751 = 524627) B524627
theorem B349771 : Blo 346754 349771 := bstep (se 1 (by rfl) ⟨262328, by rfl⟩ : syracuseStep 349771 = 524657) B524657
theorem B349783 : Blo 346754 349783 := bstep (se 1 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 349783 = 524675) B524675
theorem B349803 : Blo 346754 349803 := bstep (se 1 (by rfl) ⟨262352, by rfl⟩ : syracuseStep 349803 = 524705) B524705
theorem B349815 : Blo 346754 349815 := bstep (se 1 (by rfl) ⟨262361, by rfl⟩ : syracuseStep 349815 = 524723) B524723
theorem B349835 : Blo 346754 349835 := bstep (se 1 (by rfl) ⟨262376, by rfl⟩ : syracuseStep 349835 = 524753) B524753
theorem B349847 : Blo 346754 349847 := bstep (se 1 (by rfl) ⟨262385, by rfl⟩ : syracuseStep 349847 = 524771) B524771
theorem B349867 : Blo 346754 349867 := bstep (se 1 (by rfl) ⟨262400, by rfl⟩ : syracuseStep 349867 = 524801) B524801
theorem B2971313 : Blo 346754 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B349879 : Blo 346754 349879 := bstep (se 1 (by rfl) ⟨262409, by rfl⟩ : syracuseStep 349879 = 524819) B524819
theorem B349899 : Blo 346754 349899 := bstep (se 1 (by rfl) ⟨262424, by rfl⟩ : syracuseStep 349899 = 524849) B524849
theorem B349911 : Blo 346754 349911 := bstep (se 1 (by rfl) ⟨262433, by rfl⟩ : syracuseStep 349911 = 524867) B524867
theorem B349931 : Blo 346754 349931 := bstep (se 1 (by rfl) ⟨262448, by rfl⟩ : syracuseStep 349931 = 524897) B524897
theorem B349943 : Blo 346754 349943 := bstep (se 1 (by rfl) ⟨262457, by rfl⟩ : syracuseStep 349943 = 524915) B524915
theorem B349963 : Blo 346754 349963 := bstep (se 1 (by rfl) ⟨262472, by rfl⟩ : syracuseStep 349963 = 524945) B524945
theorem B349975 : Blo 346754 349975 := bstep (se 1 (by rfl) ⟨262481, by rfl⟩ : syracuseStep 349975 = 524963) B524963
theorem B349995 : Blo 346754 349995 := bstep (se 1 (by rfl) ⟨262496, by rfl⟩ : syracuseStep 349995 = 524993) B524993
theorem B350007 : Blo 346754 350007 := bstep (se 1 (by rfl) ⟨262505, by rfl⟩ : syracuseStep 350007 = 525011) B525011
theorem B350027 : Blo 346754 350027 := bstep (se 1 (by rfl) ⟨262520, by rfl⟩ : syracuseStep 350027 = 525041) B525041
theorem B350039 : Blo 346754 350039 := bstep (se 1 (by rfl) ⟨262529, by rfl⟩ : syracuseStep 350039 = 525059) B525059
theorem B350059 : Blo 346754 350059 := bstep (se 1 (by rfl) ⟨262544, by rfl⟩ : syracuseStep 350059 = 525089) B525089
theorem B350071 : Blo 346754 350071 := bstep (se 1 (by rfl) ⟨262553, by rfl⟩ : syracuseStep 350071 = 525107) B525107
theorem B350091 : Blo 346754 350091 := bstep (se 1 (by rfl) ⟨262568, by rfl⟩ : syracuseStep 350091 = 525137) B525137
theorem B350103 : Blo 346754 350103 := bstep (se 1 (by rfl) ⟨262577, by rfl⟩ : syracuseStep 350103 = 525155) B525155
theorem B350123 : Blo 346754 350123 := bstep (se 1 (by rfl) ⟨262592, by rfl⟩ : syracuseStep 350123 = 525185) B525185
theorem B350135 : Blo 346754 350135 := bstep (se 1 (by rfl) ⟨262601, by rfl⟩ : syracuseStep 350135 = 525203) B525203
theorem B448459 : Blo 346754 448459 := bstep (se 1 (by rfl) ⟨336344, by rfl⟩ : syracuseStep 448459 = 672689) B672689
theorem B350155 : Blo 346754 350155 := bstep (se 1 (by rfl) ⟨262616, by rfl⟩ : syracuseStep 350155 = 525233) B525233
theorem B350167 : Blo 346754 350167 := bstep (se 1 (by rfl) ⟨262625, by rfl⟩ : syracuseStep 350167 = 525251) B525251
theorem B350187 : Blo 346754 350187 := bstep (se 1 (by rfl) ⟨262640, by rfl⟩ : syracuseStep 350187 = 525281) B525281
theorem B350199 : Blo 346754 350199 := bstep (se 1 (by rfl) ⟨262649, by rfl⟩ : syracuseStep 350199 = 525299) B525299
theorem B350219 : Blo 346754 350219 := bstep (se 1 (by rfl) ⟨262664, by rfl⟩ : syracuseStep 350219 = 525329) B525329
theorem B350231 : Blo 346754 350231 := bstep (se 1 (by rfl) ⟨262673, by rfl⟩ : syracuseStep 350231 = 525347) B525347
theorem B350251 : Blo 346754 350251 := bstep (se 1 (by rfl) ⟨262688, by rfl⟩ : syracuseStep 350251 = 525377) B525377
theorem B350263 : Blo 346754 350263 := bstep (se 1 (by rfl) ⟨262697, by rfl⟩ : syracuseStep 350263 = 525395) B525395
theorem B350283 : Blo 346754 350283 := bstep (se 1 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 350283 = 525425) B525425
theorem B350295 : Blo 346754 350295 := bstep (se 1 (by rfl) ⟨262721, by rfl⟩ : syracuseStep 350295 = 525443) B525443
theorem B350315 : Blo 346754 350315 := bstep (se 1 (by rfl) ⟨262736, by rfl⟩ : syracuseStep 350315 = 525473) B525473
theorem B350327 : Blo 346754 350327 := bstep (se 1 (by rfl) ⟨262745, by rfl⟩ : syracuseStep 350327 = 525491) B525491
theorem B350347 : Blo 346754 350347 := bstep (se 1 (by rfl) ⟨262760, by rfl⟩ : syracuseStep 350347 = 525521) B525521
theorem B350359 : Blo 346754 350359 := bstep (se 1 (by rfl) ⟨262769, by rfl⟩ : syracuseStep 350359 = 525539) B525539
theorem B350379 : Blo 346754 350379 := bstep (se 1 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 350379 = 525569) B525569
theorem B350391 : Blo 346754 350391 := bstep (se 1 (by rfl) ⟨262793, by rfl⟩ : syracuseStep 350391 = 525587) B525587
theorem B350411 : Blo 346754 350411 := bstep (se 1 (by rfl) ⟨262808, by rfl⟩ : syracuseStep 350411 = 525617) B525617
theorem B4446413 : Blo 346754 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B350423 : Blo 346754 350423 := bstep (se 1 (by rfl) ⟨262817, by rfl⟩ : syracuseStep 350423 = 525635) B525635
theorem B350443 : Blo 346754 350443 := bstep (se 1 (by rfl) ⟨262832, by rfl⟩ : syracuseStep 350443 = 525665) B525665
theorem B350455 : Blo 346754 350455 := bstep (se 1 (by rfl) ⟨262841, by rfl⟩ : syracuseStep 350455 = 525683) B525683
theorem B350475 : Blo 346754 350475 := bstep (se 1 (by rfl) ⟨262856, by rfl⟩ : syracuseStep 350475 = 525713) B525713
theorem B350487 : Blo 346754 350487 := bstep (se 1 (by rfl) ⟨262865, by rfl⟩ : syracuseStep 350487 = 525731) B525731
theorem B350507 : Blo 346754 350507 := bstep (se 1 (by rfl) ⟨262880, by rfl⟩ : syracuseStep 350507 = 525761) B525761
theorem B350519 : Blo 346754 350519 := bstep (se 1 (by rfl) ⟨262889, by rfl⟩ : syracuseStep 350519 = 525779) B525779
theorem B350539 : Blo 346754 350539 := bstep (se 1 (by rfl) ⟨262904, by rfl⟩ : syracuseStep 350539 = 525809) B525809
theorem B350551 : Blo 346754 350551 := bstep (se 1 (by rfl) ⟨262913, by rfl⟩ : syracuseStep 350551 = 525827) B525827
theorem B2971997 : Blo 346754 2971997 := bstep (se 3 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 2971997 = 1114499) B1114499
theorem B2644325 : Blo 346754 2644325 := bstep (se 4 (by rfl) ⟨247905, by rfl⟩ : syracuseStep 2644325 = 495811) B495811
theorem B350571 : Blo 346754 350571 := bstep (se 1 (by rfl) ⟨262928, by rfl⟩ : syracuseStep 350571 = 525857) B525857
theorem B350583 : Blo 346754 350583 := bstep (se 1 (by rfl) ⟨262937, by rfl⟩ : syracuseStep 350583 = 525875) B525875
theorem B350603 : Blo 346754 350603 := bstep (se 1 (by rfl) ⟨262952, by rfl⟩ : syracuseStep 350603 = 525905) B525905
theorem B350615 : Blo 346754 350615 := bstep (se 1 (by rfl) ⟨262961, by rfl⟩ : syracuseStep 350615 = 525923) B525923
theorem B350635 : Blo 346754 350635 := bstep (se 1 (by rfl) ⟨262976, by rfl⟩ : syracuseStep 350635 = 525953) B525953
theorem B350647 : Blo 346754 350647 := bstep (se 1 (by rfl) ⟨262985, by rfl⟩ : syracuseStep 350647 = 525971) B525971
theorem B350667 : Blo 346754 350667 := bstep (se 1 (by rfl) ⟨263000, by rfl⟩ : syracuseStep 350667 = 526001) B526001
theorem B350679 : Blo 346754 350679 := bstep (se 1 (by rfl) ⟨263009, by rfl⟩ : syracuseStep 350679 = 526019) B526019
theorem B350699 : Blo 346754 350699 := bstep (se 1 (by rfl) ⟨263024, by rfl⟩ : syracuseStep 350699 = 526049) B526049
theorem B350711 : Blo 346754 350711 := bstep (se 1 (by rfl) ⟨263033, by rfl⟩ : syracuseStep 350711 = 526067) B526067
theorem B350731 : Blo 346754 350731 := bstep (se 1 (by rfl) ⟨263048, by rfl⟩ : syracuseStep 350731 = 526097) B526097
theorem B350743 : Blo 346754 350743 := bstep (se 1 (by rfl) ⟨263057, by rfl⟩ : syracuseStep 350743 = 526115) B526115
theorem B744025 : Blo 346754 744025 := bstep (se 2 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 744025 = 558019) B558019
theorem B2644811 : Blo 346754 2644811 := bstep (se 1 (by rfl) ⟨1983608, by rfl⟩ : syracuseStep 2644811 = 3967217) B3967217
theorem B4545629 : Blo 346754 4545629 := bstep (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) B1704611
theorem B1170611 : Blo 346754 1170611 := bstep (se 1 (by rfl) ⟨877958, by rfl⟩ : syracuseStep 1170611 = 1755917) B1755917
theorem B1268939 : Blo 346754 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B3857843 : Blo 346754 3857843 := bstep (se 1 (by rfl) ⟨2893382, by rfl⟩ : syracuseStep 3857843 = 5786765) B5786765
theorem B1170881 : Blo 346754 1170881 := bstep (se 2 (by rfl) ⟨439080, by rfl⟩ : syracuseStep 1170881 = 878161) B878161
theorem B1171421 : Blo 346754 1171421 := bstep (se 3 (by rfl) ⟨219641, by rfl⟩ : syracuseStep 1171421 = 439283) B439283
theorem B418187 : Blo 346754 418187 := bstep (se 1 (by rfl) ⟨313640, by rfl⟩ : syracuseStep 418187 = 627281) B627281
theorem B1794739 : Blo 346754 1794739 := bstep (se 1 (by rfl) ⟨1346054, by rfl⟩ : syracuseStep 1794739 = 2692109) B2692109
theorem B746177 : Blo 346754 746177 := bstep (se 2 (by rfl) ⟨279816, by rfl⟩ : syracuseStep 746177 = 559633) B559633
theorem B746263 : Blo 346754 746263 := bstep (se 1 (by rfl) ⟨559697, by rfl⟩ : syracuseStep 746263 = 1119395) B1119395
theorem B3990545 : Blo 346754 3990545 := bstep (se 2 (by rfl) ⟨1496454, by rfl⟩ : syracuseStep 3990545 = 2992909) B2992909
theorem B1172555 : Blo 346754 1172555 := bstep (se 1 (by rfl) ⟨879416, by rfl⟩ : syracuseStep 1172555 = 1758833) B1758833
theorem B8479819 : Blo 346754 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B1762397 : Blo 346754 1762397 := bstep (se 3 (by rfl) ⟨330449, by rfl⟩ : syracuseStep 1762397 = 660899) B660899
theorem B1336621 : Blo 346754 1336621 := bstep (se 3 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 1336621 = 501233) B501233
theorem B1172825 : Blo 346754 1172825 := bstep (se 2 (by rfl) ⟨439809, by rfl⟩ : syracuseStep 1172825 = 879619) B879619
theorem B681367 : Blo 346754 681367 := bstep (se 1 (by rfl) ⟨511025, by rfl⟩ : syracuseStep 681367 = 1022051) B1022051
theorem B1598899 : Blo 346754 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1009217 : Blo 346754 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B747083 : Blo 346754 747083 := bstep (se 1 (by rfl) ⟨560312, by rfl⟩ : syracuseStep 747083 = 1120625) B1120625
theorem B2385539 : Blo 346754 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B878273 : Blo 346754 878273 := bstep (se 2 (by rfl) ⟨329352, by rfl⟩ : syracuseStep 878273 = 658705) B658705
theorem B780299 : Blo 346754 780299 := bstep (se 1 (by rfl) ⟨585224, by rfl⟩ : syracuseStep 780299 = 1170449) B1170449
theorem B1992721 : Blo 346754 1992721 := bstep (se 2 (by rfl) ⟨747270, by rfl⟩ : syracuseStep 1992721 = 1494541) B1494541
theorem B1173527 : Blo 346754 1173527 := bstep (se 1 (by rfl) ⟨880145, by rfl⟩ : syracuseStep 1173527 = 1760291) B1760291
theorem B780353 : Blo 346754 780353 := bstep (se 2 (by rfl) ⟨292632, by rfl⟩ : syracuseStep 780353 = 585265) B585265
theorem B2517169 : Blo 346754 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B878809 : Blo 346754 878809 := bstep (se 2 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 878809 = 659107) B659107
theorem B4253957 : Blo 346754 4253957 := bstep (se 4 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 4253957 = 797617) B797617
theorem B780569 : Blo 346754 780569 := bstep (se 2 (by rfl) ⟨292713, by rfl⟩ : syracuseStep 780569 = 585427) B585427
theorem B2222437 : Blo 346754 2222437 := bstep (se 4 (by rfl) ⟨208353, by rfl⟩ : syracuseStep 2222437 = 416707) B416707
theorem B780659 : Blo 346754 780659 := bstep (se 1 (by rfl) ⟨585494, by rfl⟩ : syracuseStep 780659 = 1170989) B1170989
theorem B780695 : Blo 346754 780695 := bstep (se 1 (by rfl) ⟨585521, by rfl⟩ : syracuseStep 780695 = 1171043) B1171043
theorem B3762611 : Blo 346754 3762611 := bstep (se 1 (by rfl) ⟨2821958, by rfl⟩ : syracuseStep 3762611 = 5643917) B5643917
theorem B748057 : Blo 346754 748057 := bstep (se 2 (by rfl) ⟨280521, by rfl⟩ : syracuseStep 748057 = 561043) B561043
theorem B1174067 : Blo 346754 1174067 := bstep (se 1 (by rfl) ⟨880550, by rfl⟩ : syracuseStep 1174067 = 1761101) B1761101
theorem B780875 : Blo 346754 780875 := bstep (se 1 (by rfl) ⟨585656, by rfl⟩ : syracuseStep 780875 = 1171313) B1171313
theorem B780929 : Blo 346754 780929 := bstep (se 2 (by rfl) ⟨292848, by rfl⟩ : syracuseStep 780929 = 585697) B585697
theorem B1436467 : Blo 346754 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B1174337 : Blo 346754 1174337 := bstep (se 2 (by rfl) ⟨440376, by rfl⟩ : syracuseStep 1174337 = 880753) B880753
theorem B781145 : Blo 346754 781145 := bstep (se 2 (by rfl) ⟨292929, by rfl⟩ : syracuseStep 781145 = 585859) B585859
theorem B781235 : Blo 346754 781235 := bstep (se 1 (by rfl) ⟨585926, by rfl⟩ : syracuseStep 781235 = 1171853) B1171853
theorem B2812877 : Blo 346754 2812877 := bstep (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) B1054829
theorem B781271 : Blo 346754 781271 := bstep (se 1 (by rfl) ⟨585953, by rfl⟩ : syracuseStep 781271 = 1171907) B1171907
theorem B1272793 : Blo 346754 1272793 := bstep (se 2 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 1272793 = 954595) B954595
theorem B781451 : Blo 346754 781451 := bstep (se 1 (by rfl) ⟨586088, by rfl⟩ : syracuseStep 781451 = 1172177) B1172177
theorem B1764503 : Blo 346754 1764503 := bstep (se 1 (by rfl) ⟨1323377, by rfl⟩ : syracuseStep 1764503 = 2646755) B2646755
theorem B1502401 : Blo 346754 1502401 := bstep (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) B1126801
theorem B781505 : Blo 346754 781505 := bstep (se 2 (by rfl) ⟨293064, by rfl⟩ : syracuseStep 781505 = 586129) B586129
theorem B879923 : Blo 346754 879923 := bstep (se 1 (by rfl) ⟨659942, by rfl⟩ : syracuseStep 879923 = 1319885) B1319885
theorem B1174877 : Blo 346754 1174877 := bstep (se 3 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 1174877 = 440579) B440579
theorem B781721 : Blo 346754 781721 := bstep (se 2 (by rfl) ⟨293145, by rfl⟩ : syracuseStep 781721 = 586291) B586291
theorem B781811 : Blo 346754 781811 := bstep (se 1 (by rfl) ⟨586358, by rfl⟩ : syracuseStep 781811 = 1172717) B1172717
theorem B781847 : Blo 346754 781847 := bstep (se 1 (by rfl) ⟨586385, by rfl⟩ : syracuseStep 781847 = 1172771) B1172771
theorem B880217 : Blo 346754 880217 := bstep (se 2 (by rfl) ⟨330081, by rfl⟩ : syracuseStep 880217 = 660163) B660163
theorem B13463171 : Blo 346754 13463171 := bstep (se 1 (by rfl) ⟨10097378, by rfl⟩ : syracuseStep 13463171 = 20194757) B20194757
theorem B782027 : Blo 346754 782027 := bstep (se 1 (by rfl) ⟨586520, by rfl⟩ : syracuseStep 782027 = 1173041) B1173041
theorem B782081 : Blo 346754 782081 := bstep (se 2 (by rfl) ⟨293280, by rfl⟩ : syracuseStep 782081 = 586561) B586561
theorem B4255553 : Blo 346754 4255553 := bstep (se 2 (by rfl) ⟨1595832, by rfl⟩ : syracuseStep 4255553 = 3191665) B3191665
theorem B3993461 : Blo 346754 3993461 := bstep (se 5 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 3993461 = 374387) B374387
theorem B585623 : Blo 346754 585623 := bstep (se 1 (by rfl) ⟨439217, by rfl⟩ : syracuseStep 585623 = 878435) B878435
theorem B520139 : Blo 346754 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B520151 : Blo 346754 520151 := bstep (se 1 (by rfl) ⟨390113, by rfl⟩ : syracuseStep 520151 = 780227) B780227
theorem B782297 : Blo 346754 782297 := bstep (se 2 (by rfl) ⟨293361, by rfl⟩ : syracuseStep 782297 = 586723) B586723
theorem B585751 : Blo 346754 585751 := bstep (se 1 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 585751 = 878627) B878627
theorem B520217 : Blo 346754 520217 := bstep (se 2 (by rfl) ⟨195081, by rfl⟩ : syracuseStep 520217 = 390163) B390163
theorem B2650157 : Blo 346754 2650157 := bstep (se 3 (by rfl) ⟨496904, by rfl⟩ : syracuseStep 2650157 = 993809) B993809
theorem B782387 : Blo 346754 782387 := bstep (se 1 (by rfl) ⟨586790, by rfl⟩ : syracuseStep 782387 = 1173581) B1173581
theorem B782423 : Blo 346754 782423 := bstep (se 1 (by rfl) ⟨586817, by rfl⟩ : syracuseStep 782423 = 1173635) B1173635
theorem B520331 : Blo 346754 520331 := bstep (se 1 (by rfl) ⟨390248, by rfl⟩ : syracuseStep 520331 = 780497) B780497
theorem B520343 : Blo 346754 520343 := bstep (se 1 (by rfl) ⟨390257, by rfl⟩ : syracuseStep 520343 = 780515) B780515
theorem B520409 : Blo 346754 520409 := bstep (se 2 (by rfl) ⟨195153, by rfl⟩ : syracuseStep 520409 = 390307) B390307
theorem B782603 : Blo 346754 782603 := bstep (se 1 (by rfl) ⟨586952, by rfl⟩ : syracuseStep 782603 = 1173905) B1173905
theorem B782657 : Blo 346754 782657 := bstep (se 2 (by rfl) ⟨293496, by rfl⟩ : syracuseStep 782657 = 586993) B586993
theorem B520523 : Blo 346754 520523 := bstep (se 1 (by rfl) ⟨390392, by rfl⟩ : syracuseStep 520523 = 780785) B780785
theorem B3010891 : Blo 346754 3010891 := bstep (se 1 (by rfl) ⟨2258168, by rfl⟩ : syracuseStep 3010891 = 4516337) B4516337
theorem B520535 : Blo 346754 520535 := bstep (se 1 (by rfl) ⟨390401, by rfl⟩ : syracuseStep 520535 = 780803) B780803
theorem B520601 : Blo 346754 520601 := bstep (se 2 (by rfl) ⟨195225, by rfl⟩ : syracuseStep 520601 = 390451) B390451
theorem B1176011 : Blo 346754 1176011 := bstep (se 1 (by rfl) ⟨882008, by rfl⟩ : syracuseStep 1176011 = 1764017) B1764017
theorem B520715 : Blo 346754 520715 := bstep (se 1 (by rfl) ⟨390536, by rfl⟩ : syracuseStep 520715 = 781073) B781073
theorem B520727 : Blo 346754 520727 := bstep (se 1 (by rfl) ⟨390545, by rfl⟩ : syracuseStep 520727 = 781091) B781091
theorem B782873 : Blo 346754 782873 := bstep (se 2 (by rfl) ⟨293577, by rfl⟩ : syracuseStep 782873 = 587155) B587155
theorem B520793 : Blo 346754 520793 := bstep (se 2 (by rfl) ⟨195297, by rfl⟩ : syracuseStep 520793 = 390595) B390595
theorem B782963 : Blo 346754 782963 := bstep (se 1 (by rfl) ⟨587222, by rfl⟩ : syracuseStep 782963 = 1174445) B1174445
theorem B717427 : Blo 346754 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B586379 : Blo 346754 586379 := bstep (se 1 (by rfl) ⟨439784, by rfl⟩ : syracuseStep 586379 = 879569) B879569
theorem B782999 : Blo 346754 782999 := bstep (se 1 (by rfl) ⟨587249, by rfl⟩ : syracuseStep 782999 = 1174499) B1174499
theorem B520907 : Blo 346754 520907 := bstep (se 1 (by rfl) ⟨390680, by rfl⟩ : syracuseStep 520907 = 781361) B781361
theorem B520919 : Blo 346754 520919 := bstep (se 1 (by rfl) ⟨390689, by rfl⟩ : syracuseStep 520919 = 781379) B781379
theorem B1176281 : Blo 346754 1176281 := bstep (se 2 (by rfl) ⟨441105, by rfl⟩ : syracuseStep 1176281 = 882211) B882211
theorem B586507 : Blo 346754 586507 := bstep (se 1 (by rfl) ⟨439880, by rfl⟩ : syracuseStep 586507 = 879761) B879761
theorem B520985 : Blo 346754 520985 := bstep (se 2 (by rfl) ⟨195369, by rfl⟩ : syracuseStep 520985 = 390739) B390739
theorem B783179 : Blo 346754 783179 := bstep (se 1 (by rfl) ⟨587384, by rfl⟩ : syracuseStep 783179 = 1174769) B1174769
theorem B3240805 : Blo 346754 3240805 := bstep (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) B607651
theorem B783233 : Blo 346754 783233 := bstep (se 2 (by rfl) ⟨293712, by rfl⟩ : syracuseStep 783233 = 587425) B587425
theorem B2814851 : Blo 346754 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B521099 : Blo 346754 521099 := bstep (se 1 (by rfl) ⟨390824, by rfl⟩ : syracuseStep 521099 = 781649) B781649
theorem B521111 : Blo 346754 521111 := bstep (se 1 (by rfl) ⟨390833, by rfl⟩ : syracuseStep 521111 = 781667) B781667
theorem B586649 : Blo 346754 586649 := bstep (se 2 (by rfl) ⟨219993, by rfl⟩ : syracuseStep 586649 = 439987) B439987
theorem B1307585 : Blo 346754 1307585 := bstep (se 2 (by rfl) ⟨490344, by rfl⟩ : syracuseStep 1307585 = 980689) B980689
theorem B521177 : Blo 346754 521177 := bstep (se 2 (by rfl) ⟨195441, by rfl⟩ : syracuseStep 521177 = 390883) B390883
theorem B586777 : Blo 346754 586777 := bstep (se 2 (by rfl) ⟨220041, by rfl⟩ : syracuseStep 586777 = 440083) B440083
theorem B390199 : Blo 346754 390199 := bstep (se 1 (by rfl) ⟨292649, by rfl⟩ : syracuseStep 390199 = 585299) B585299
theorem B521291 : Blo 346754 521291 := bstep (se 1 (by rfl) ⟨390968, by rfl⟩ : syracuseStep 521291 = 781937) B781937
theorem B521303 : Blo 346754 521303 := bstep (se 1 (by rfl) ⟨390977, by rfl⟩ : syracuseStep 521303 = 781955) B781955
theorem B783449 : Blo 346754 783449 := bstep (se 2 (by rfl) ⟨293793, by rfl⟩ : syracuseStep 783449 = 587587) B587587
theorem B521369 : Blo 346754 521369 := bstep (se 2 (by rfl) ⟨195513, by rfl⟩ : syracuseStep 521369 = 391027) B391027
theorem B783539 : Blo 346754 783539 := bstep (se 1 (by rfl) ⟨587654, by rfl⟩ : syracuseStep 783539 = 1175309) B1175309
theorem B881867 : Blo 346754 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B783575 : Blo 346754 783575 := bstep (se 1 (by rfl) ⟨587681, by rfl⟩ : syracuseStep 783575 = 1175363) B1175363
theorem B390379 : Blo 346754 390379 := bstep (se 1 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 390379 = 585569) B585569
theorem B521483 : Blo 346754 521483 := bstep (se 1 (by rfl) ⟨391112, by rfl⟩ : syracuseStep 521483 = 782225) B782225
theorem B521495 : Blo 346754 521495 := bstep (se 1 (by rfl) ⟨391121, by rfl⟩ : syracuseStep 521495 = 782243) B782243
theorem B390487 : Blo 346754 390487 := bstep (se 1 (by rfl) ⟨292865, by rfl⟩ : syracuseStep 390487 = 585731) B585731
theorem B521561 : Blo 346754 521561 := bstep (se 2 (by rfl) ⟨195585, by rfl⟩ : syracuseStep 521561 = 391171) B391171
theorem B1996163 : Blo 346754 1996163 := bstep (se 1 (by rfl) ⟨1497122, by rfl⟩ : syracuseStep 1996163 = 2994245) B2994245
theorem B783755 : Blo 346754 783755 := bstep (se 1 (by rfl) ⟨587816, by rfl⟩ : syracuseStep 783755 = 1175633) B1175633
theorem B1176983 : Blo 346754 1176983 := bstep (se 1 (by rfl) ⟨882737, by rfl⟩ : syracuseStep 1176983 = 1765475) B1765475
theorem B1111475 : Blo 346754 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B783809 : Blo 346754 783809 := bstep (se 2 (by rfl) ⟨293928, by rfl⟩ : syracuseStep 783809 = 587857) B587857
theorem B521675 : Blo 346754 521675 := bstep (se 1 (by rfl) ⟨391256, by rfl⟩ : syracuseStep 521675 = 782513) B782513
theorem B521687 : Blo 346754 521687 := bstep (se 1 (by rfl) ⟨391265, by rfl⟩ : syracuseStep 521687 = 782531) B782531
theorem B390667 : Blo 346754 390667 := bstep (se 1 (by rfl) ⟨293000, by rfl⟩ : syracuseStep 390667 = 586001) B586001
theorem B521753 : Blo 346754 521753 := bstep (se 2 (by rfl) ⟨195657, by rfl⟩ : syracuseStep 521753 = 391315) B391315
theorem B718411 : Blo 346754 718411 := bstep (se 1 (by rfl) ⟨538808, by rfl⟩ : syracuseStep 718411 = 1077617) B1077617
theorem B587351 : Blo 346754 587351 := bstep (se 1 (by rfl) ⟨440513, by rfl⟩ : syracuseStep 587351 = 881027) B881027
theorem B390775 : Blo 346754 390775 := bstep (se 1 (by rfl) ⟨293081, by rfl⟩ : syracuseStep 390775 = 586163) B586163
theorem B521867 : Blo 346754 521867 := bstep (se 1 (by rfl) ⟨391400, by rfl⟩ : syracuseStep 521867 = 782801) B782801
theorem B521879 : Blo 346754 521879 := bstep (se 1 (by rfl) ⟨391409, by rfl⟩ : syracuseStep 521879 = 782819) B782819
theorem B784025 : Blo 346754 784025 := bstep (se 2 (by rfl) ⟨294009, by rfl⟩ : syracuseStep 784025 = 588019) B588019
theorem B5732021 : Blo 346754 5732021 := bstep (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) B537377
theorem B587479 : Blo 346754 587479 := bstep (se 1 (by rfl) ⟨440609, by rfl⟩ : syracuseStep 587479 = 881219) B881219
theorem B521945 : Blo 346754 521945 := bstep (se 2 (by rfl) ⟨195729, by rfl⟩ : syracuseStep 521945 = 391459) B391459
theorem B784115 : Blo 346754 784115 := bstep (se 1 (by rfl) ⟨588086, by rfl⟩ : syracuseStep 784115 = 1176173) B1176173
theorem B784151 : Blo 346754 784151 := bstep (se 1 (by rfl) ⟨588113, by rfl⟩ : syracuseStep 784151 = 1176227) B1176227
theorem B390955 : Blo 346754 390955 := bstep (se 1 (by rfl) ⟨293216, by rfl⟩ : syracuseStep 390955 = 586433) B586433
theorem B522059 : Blo 346754 522059 := bstep (se 1 (by rfl) ⟨391544, by rfl⟩ : syracuseStep 522059 = 783089) B783089
theorem B522071 : Blo 346754 522071 := bstep (se 1 (by rfl) ⟨391553, by rfl⟩ : syracuseStep 522071 = 783107) B783107
theorem B391063 : Blo 346754 391063 := bstep (se 1 (by rfl) ⟨293297, by rfl⟩ : syracuseStep 391063 = 586595) B586595
theorem B522137 : Blo 346754 522137 := bstep (se 2 (by rfl) ⟨195801, by rfl⟩ : syracuseStep 522137 = 391603) B391603
theorem B1177523 : Blo 346754 1177523 := bstep (se 1 (by rfl) ⟨883142, by rfl⟩ : syracuseStep 1177523 = 1766285) B1766285
theorem B784331 : Blo 346754 784331 := bstep (se 1 (by rfl) ⟨588248, by rfl⟩ : syracuseStep 784331 = 1176497) B1176497
theorem B784385 : Blo 346754 784385 := bstep (se 2 (by rfl) ⟨294144, by rfl⟩ : syracuseStep 784385 = 588289) B588289
theorem B522251 : Blo 346754 522251 := bstep (se 1 (by rfl) ⟨391688, by rfl⟩ : syracuseStep 522251 = 783377) B783377
theorem B522263 : Blo 346754 522263 := bstep (se 1 (by rfl) ⟨391697, by rfl⟩ : syracuseStep 522263 = 783395) B783395
theorem B391243 : Blo 346754 391243 := bstep (se 1 (by rfl) ⟨293432, by rfl⟩ : syracuseStep 391243 = 586865) B586865
theorem B522329 : Blo 346754 522329 := bstep (se 2 (by rfl) ⟨195873, by rfl⟩ : syracuseStep 522329 = 391747) B391747
theorem B2685059 : Blo 346754 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B882839 : Blo 346754 882839 := bstep (se 1 (by rfl) ⟨662129, by rfl⟩ : syracuseStep 882839 = 1324259) B1324259
theorem B391351 : Blo 346754 391351 := bstep (se 1 (by rfl) ⟨293513, by rfl⟩ : syracuseStep 391351 = 587027) B587027
theorem B1177793 : Blo 346754 1177793 := bstep (se 2 (by rfl) ⟨441672, by rfl⟩ : syracuseStep 1177793 = 883345) B883345
theorem B522443 : Blo 346754 522443 := bstep (se 1 (by rfl) ⟨391832, by rfl⟩ : syracuseStep 522443 = 783665) B783665
theorem B522455 : Blo 346754 522455 := bstep (se 1 (by rfl) ⟨391841, by rfl⟩ : syracuseStep 522455 = 783683) B783683
theorem B784601 : Blo 346754 784601 := bstep (se 2 (by rfl) ⟨294225, by rfl⟩ : syracuseStep 784601 = 588451) B588451
theorem B522521 : Blo 346754 522521 := bstep (se 2 (by rfl) ⟨195945, by rfl⟩ : syracuseStep 522521 = 391891) B391891
theorem B784691 : Blo 346754 784691 := bstep (se 1 (by rfl) ⟨588518, by rfl⟩ : syracuseStep 784691 = 1177037) B1177037
theorem B588107 : Blo 346754 588107 := bstep (se 1 (by rfl) ⟨441080, by rfl⟩ : syracuseStep 588107 = 882161) B882161
theorem B784727 : Blo 346754 784727 := bstep (se 1 (by rfl) ⟨588545, by rfl⟩ : syracuseStep 784727 = 1177091) B1177091
theorem B391531 : Blo 346754 391531 := bstep (se 1 (by rfl) ⟨293648, by rfl⟩ : syracuseStep 391531 = 587297) B587297
theorem B522635 : Blo 346754 522635 := bstep (se 1 (by rfl) ⟨391976, by rfl⟩ : syracuseStep 522635 = 783953) B783953
theorem B522647 : Blo 346754 522647 := bstep (se 1 (by rfl) ⟨391985, by rfl⟩ : syracuseStep 522647 = 783971) B783971
theorem B588235 : Blo 346754 588235 := bstep (se 1 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 588235 = 882353) B882353
theorem B391639 : Blo 346754 391639 := bstep (se 1 (by rfl) ⟨293729, by rfl⟩ : syracuseStep 391639 = 587459) B587459
theorem B555481 : Blo 346754 555481 := bstep (se 2 (by rfl) ⟨208305, by rfl⟩ : syracuseStep 555481 = 416611) B416611
theorem B522713 : Blo 346754 522713 := bstep (se 2 (by rfl) ⟨196017, by rfl⟩ : syracuseStep 522713 = 392035) B392035
theorem B784907 : Blo 346754 784907 := bstep (se 1 (by rfl) ⟨588680, by rfl⟩ : syracuseStep 784907 = 1177361) B1177361
theorem B784961 : Blo 346754 784961 := bstep (se 2 (by rfl) ⟨294360, by rfl⟩ : syracuseStep 784961 = 588721) B588721
theorem B522827 : Blo 346754 522827 := bstep (se 1 (by rfl) ⟨392120, by rfl⟩ : syracuseStep 522827 = 784241) B784241
theorem B522839 : Blo 346754 522839 := bstep (se 1 (by rfl) ⟨392129, by rfl⟩ : syracuseStep 522839 = 784259) B784259
theorem B588377 : Blo 346754 588377 := bstep (se 2 (by rfl) ⟨220641, by rfl⟩ : syracuseStep 588377 = 441283) B441283
theorem B1768067 : Blo 346754 1768067 := bstep (se 1 (by rfl) ⟨1326050, by rfl⟩ : syracuseStep 1768067 = 2652101) B2652101
theorem B391819 : Blo 346754 391819 := bstep (se 1 (by rfl) ⟨293864, by rfl⟩ : syracuseStep 391819 = 587729) B587729
theorem B522905 : Blo 346754 522905 := bstep (se 2 (by rfl) ⟨196089, by rfl⟩ : syracuseStep 522905 = 392179) B392179
theorem B588505 : Blo 346754 588505 := bstep (se 2 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 588505 = 441379) B441379
theorem B1178333 : Blo 346754 1178333 := bstep (se 3 (by rfl) ⟨220937, by rfl⟩ : syracuseStep 1178333 = 441875) B441875
theorem B7568113 : Blo 346754 7568113 := bstep (se 2 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 7568113 = 5676085) B5676085
theorem B391927 : Blo 346754 391927 := bstep (se 1 (by rfl) ⟨293945, by rfl⟩ : syracuseStep 391927 = 587891) B587891
theorem B523019 : Blo 346754 523019 := bstep (se 1 (by rfl) ⟨392264, by rfl⟩ : syracuseStep 523019 = 784529) B784529
theorem B523031 : Blo 346754 523031 := bstep (se 1 (by rfl) ⟨392273, by rfl⟩ : syracuseStep 523031 = 784547) B784547
theorem B785177 : Blo 346754 785177 := bstep (se 2 (by rfl) ⟨294441, by rfl⟩ : syracuseStep 785177 = 588883) B588883
theorem B883507 : Blo 346754 883507 := bstep (se 1 (by rfl) ⟨662630, by rfl⟩ : syracuseStep 883507 = 1325261) B1325261
theorem B523097 : Blo 346754 523097 := bstep (se 2 (by rfl) ⟨196161, by rfl⟩ : syracuseStep 523097 = 392323) B392323
theorem B785267 : Blo 346754 785267 := bstep (se 1 (by rfl) ⟨588950, by rfl⟩ : syracuseStep 785267 = 1177901) B1177901
theorem B785303 : Blo 346754 785303 := bstep (se 1 (by rfl) ⟨588977, by rfl⟩ : syracuseStep 785303 = 1177955) B1177955
theorem B392107 : Blo 346754 392107 := bstep (se 1 (by rfl) ⟨294080, by rfl⟩ : syracuseStep 392107 = 588161) B588161
theorem B883649 : Blo 346754 883649 := bstep (se 2 (by rfl) ⟨331368, by rfl⟩ : syracuseStep 883649 = 662737) B662737
theorem B523211 : Blo 346754 523211 := bstep (se 1 (by rfl) ⟨392408, by rfl⟩ : syracuseStep 523211 = 784817) B784817
theorem B523223 : Blo 346754 523223 := bstep (se 1 (by rfl) ⟨392417, by rfl⟩ : syracuseStep 523223 = 784835) B784835
theorem B392215 : Blo 346754 392215 := bstep (se 1 (by rfl) ⟨294161, by rfl⟩ : syracuseStep 392215 = 588323) B588323
theorem B523289 : Blo 346754 523289 := bstep (se 2 (by rfl) ⟨196233, by rfl⟩ : syracuseStep 523289 = 392467) B392467
theorem B785483 : Blo 346754 785483 := bstep (se 1 (by rfl) ⟨589112, by rfl⟩ : syracuseStep 785483 = 1178225) B1178225
theorem B785537 : Blo 346754 785537 := bstep (se 2 (by rfl) ⟨294576, by rfl⟩ : syracuseStep 785537 = 589153) B589153
theorem B523403 : Blo 346754 523403 := bstep (se 1 (by rfl) ⟨392552, by rfl⟩ : syracuseStep 523403 = 785105) B785105
theorem B523415 : Blo 346754 523415 := bstep (se 1 (by rfl) ⟨392561, by rfl⟩ : syracuseStep 523415 = 785123) B785123
theorem B392395 : Blo 346754 392395 := bstep (se 1 (by rfl) ⟨294296, by rfl⟩ : syracuseStep 392395 = 588593) B588593
theorem B523481 : Blo 346754 523481 := bstep (se 2 (by rfl) ⟨196305, by rfl⟩ : syracuseStep 523481 = 392611) B392611
theorem B589079 : Blo 346754 589079 := bstep (se 1 (by rfl) ⟨441809, by rfl⟩ : syracuseStep 589079 = 883619) B883619
theorem B392503 : Blo 346754 392503 := bstep (se 1 (by rfl) ⟨294377, by rfl⟩ : syracuseStep 392503 = 588755) B588755
theorem B523595 : Blo 346754 523595 := bstep (se 1 (by rfl) ⟨392696, by rfl⟩ : syracuseStep 523595 = 785393) B785393
theorem B523607 : Blo 346754 523607 := bstep (se 1 (by rfl) ⟨392705, by rfl⟩ : syracuseStep 523607 = 785411) B785411
theorem B785753 : Blo 346754 785753 := bstep (se 2 (by rfl) ⟨294657, by rfl⟩ : syracuseStep 785753 = 589315) B589315
theorem B589207 : Blo 346754 589207 := bstep (se 1 (by rfl) ⟨441905, by rfl⟩ : syracuseStep 589207 = 883811) B883811
theorem B523673 : Blo 346754 523673 := bstep (se 2 (by rfl) ⟨196377, by rfl⟩ : syracuseStep 523673 = 392755) B392755
theorem B2686385 : Blo 346754 2686385 := bstep (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) B2014789
theorem B785843 : Blo 346754 785843 := bstep (se 1 (by rfl) ⟨589382, by rfl⟩ : syracuseStep 785843 = 1178765) B1178765
theorem B785879 : Blo 346754 785879 := bstep (se 1 (by rfl) ⟨589409, by rfl⟩ : syracuseStep 785879 = 1178819) B1178819
theorem B392683 : Blo 346754 392683 := bstep (se 1 (by rfl) ⟨294512, by rfl⟩ : syracuseStep 392683 = 589025) B589025
theorem B523787 : Blo 346754 523787 := bstep (se 1 (by rfl) ⟨392840, by rfl⟩ : syracuseStep 523787 = 785681) B785681
theorem B523799 : Blo 346754 523799 := bstep (se 1 (by rfl) ⟨392849, by rfl⟩ : syracuseStep 523799 = 785699) B785699
theorem B392791 : Blo 346754 392791 := bstep (se 1 (by rfl) ⟨294593, by rfl⟩ : syracuseStep 392791 = 589187) B589187
theorem B523865 : Blo 346754 523865 := bstep (se 2 (by rfl) ⟨196449, by rfl⟩ : syracuseStep 523865 = 392899) B392899
theorem B1408643 : Blo 346754 1408643 := bstep (se 1 (by rfl) ⟨1056482, by rfl⟩ : syracuseStep 1408643 = 2112965) B2112965
theorem B786059 : Blo 346754 786059 := bstep (se 1 (by rfl) ⟨589544, by rfl⟩ : syracuseStep 786059 = 1179089) B1179089
theorem B786113 : Blo 346754 786113 := bstep (se 2 (by rfl) ⟨294792, by rfl⟩ : syracuseStep 786113 = 589585) B589585
theorem B523979 : Blo 346754 523979 := bstep (se 1 (by rfl) ⟨392984, by rfl⟩ : syracuseStep 523979 = 785969) B785969
theorem B523991 : Blo 346754 523991 := bstep (se 1 (by rfl) ⟨392993, by rfl⟩ : syracuseStep 523991 = 785987) B785987
theorem B1113821 : Blo 346754 1113821 := bstep (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) B417683
theorem B392971 : Blo 346754 392971 := bstep (se 1 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 392971 = 589457) B589457
theorem B524057 : Blo 346754 524057 := bstep (se 2 (by rfl) ⟨196521, by rfl⟩ : syracuseStep 524057 = 393043) B393043
theorem B1179467 : Blo 346754 1179467 := bstep (se 1 (by rfl) ⟨884600, by rfl⟩ : syracuseStep 1179467 = 1769201) B1769201
theorem B2654045 : Blo 346754 2654045 := bstep (se 3 (by rfl) ⟨497633, by rfl⟩ : syracuseStep 2654045 = 995267) B995267
theorem B393079 : Blo 346754 393079 := bstep (se 1 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 393079 = 589619) B589619
theorem B524171 : Blo 346754 524171 := bstep (se 1 (by rfl) ⟨393128, by rfl⟩ : syracuseStep 524171 = 786257) B786257
theorem B524183 : Blo 346754 524183 := bstep (se 1 (by rfl) ⟨393137, by rfl⟩ : syracuseStep 524183 = 786275) B786275
theorem B786329 : Blo 346754 786329 := bstep (se 2 (by rfl) ⟨294873, by rfl⟩ : syracuseStep 786329 = 589747) B589747
theorem B1015769 : Blo 346754 1015769 := bstep (se 2 (by rfl) ⟨380913, by rfl⟩ : syracuseStep 1015769 = 761827) B761827
theorem B524249 : Blo 346754 524249 := bstep (se 2 (by rfl) ⟨196593, by rfl⟩ : syracuseStep 524249 = 393187) B393187
theorem B786419 : Blo 346754 786419 := bstep (se 1 (by rfl) ⟨589814, by rfl⟩ : syracuseStep 786419 = 1179629) B1179629
theorem B393223 : Blo 346754 393223 := bstep (se 1 (by rfl) ⟨294917, by rfl⟩ : syracuseStep 393223 = 589835) B589835
theorem B524303 : Blo 346754 524303 := bstep (se 1 (by rfl) ⟨393227, by rfl⟩ : syracuseStep 524303 = 786455) B786455
theorem B524345 : Blo 346754 524345 := bstep (se 2 (by rfl) ⟨196629, by rfl⟩ : syracuseStep 524345 = 393259) B393259
theorem B786491 : Blo 346754 786491 := bstep (se 1 (by rfl) ⟨589868, by rfl⟩ : syracuseStep 786491 = 1179737) B1179737
theorem B1114231 : Blo 346754 1114231 := bstep (se 1 (by rfl) ⟨835673, by rfl⟩ : syracuseStep 1114231 = 1671347) B1671347
theorem B589943 : Blo 346754 589943 := bstep (se 1 (by rfl) ⟨442457, by rfl⟩ : syracuseStep 589943 = 884915) B884915
theorem B524423 : Blo 346754 524423 := bstep (se 1 (by rfl) ⟨393317, by rfl⟩ : syracuseStep 524423 = 786635) B786635
theorem B524459 : Blo 346754 524459 := bstep (se 1 (by rfl) ⟨393344, by rfl⟩ : syracuseStep 524459 = 786689) B786689
theorem B786617 : Blo 346754 786617 := bstep (se 2 (by rfl) ⟨294981, by rfl⟩ : syracuseStep 786617 = 589963) B589963
theorem B393403 : Blo 346754 393403 := bstep (se 1 (by rfl) ⟨295052, by rfl⟩ : syracuseStep 393403 = 590105) B590105
theorem B524489 : Blo 346754 524489 := bstep (se 2 (by rfl) ⟨196683, by rfl⟩ : syracuseStep 524489 = 393367) B393367
theorem B557327 : Blo 346754 557327 := bstep (se 1 (by rfl) ⟨417995, by rfl⟩ : syracuseStep 557327 = 835991) B835991
theorem B524603 : Blo 346754 524603 := bstep (se 1 (by rfl) ⟨393452, by rfl⟩ : syracuseStep 524603 = 786905) B786905
theorem B885107 : Blo 346754 885107 := bstep (se 1 (by rfl) ⟨663830, by rfl⟩ : syracuseStep 885107 = 1327661) B1327661
theorem B524663 : Blo 346754 524663 := bstep (se 1 (by rfl) ⟨393497, by rfl⟩ : syracuseStep 524663 = 786995) B786995
theorem B885127 : Blo 346754 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B524687 : Blo 346754 524687 := bstep (se 1 (by rfl) ⟨393515, by rfl⟩ : syracuseStep 524687 = 787031) B787031
theorem B524729 : Blo 346754 524729 := bstep (se 2 (by rfl) ⟨196773, by rfl⟩ : syracuseStep 524729 = 393547) B393547
theorem B524807 : Blo 346754 524807 := bstep (se 1 (by rfl) ⟨393605, by rfl⟩ : syracuseStep 524807 = 787211) B787211
theorem B786959 : Blo 346754 786959 := bstep (se 1 (by rfl) ⟨590219, by rfl⟩ : syracuseStep 786959 = 1180439) B1180439
theorem B786977 : Blo 346754 786977 := bstep (se 2 (by rfl) ⟨295116, by rfl⟩ : syracuseStep 786977 = 590233) B590233
theorem B3768875 : Blo 346754 3768875 := bstep (se 1 (by rfl) ⟨2826656, by rfl⟩ : syracuseStep 3768875 = 5653313) B5653313
theorem B524843 : Blo 346754 524843 := bstep (se 1 (by rfl) ⟨393632, by rfl⟩ : syracuseStep 524843 = 787265) B787265
theorem B590395 : Blo 346754 590395 := bstep (se 1 (by rfl) ⟨442796, by rfl⟩ : syracuseStep 590395 = 885593) B885593
theorem B524873 : Blo 346754 524873 := bstep (se 2 (by rfl) ⟨196827, by rfl⟩ : syracuseStep 524873 = 393655) B393655
theorem B393871 : Blo 346754 393871 := bstep (se 1 (by rfl) ⟨295403, by rfl⟩ : syracuseStep 393871 = 590807) B590807
theorem B885401 : Blo 346754 885401 := bstep (se 2 (by rfl) ⟨332025, by rfl⟩ : syracuseStep 885401 = 664051) B664051
theorem B524987 : Blo 346754 524987 := bstep (se 1 (by rfl) ⟨393740, by rfl⟩ : syracuseStep 524987 = 787481) B787481
theorem B590537 : Blo 346754 590537 := bstep (se 2 (by rfl) ⟨221451, by rfl⟩ : syracuseStep 590537 = 442903) B442903
theorem B525047 : Blo 346754 525047 := bstep (se 1 (by rfl) ⟨393785, by rfl⟩ : syracuseStep 525047 = 787571) B787571
theorem B525071 : Blo 346754 525071 := bstep (se 1 (by rfl) ⟨393803, by rfl⟩ : syracuseStep 525071 = 787607) B787607
theorem B525113 : Blo 346754 525113 := bstep (se 2 (by rfl) ⟨196917, by rfl⟩ : syracuseStep 525113 = 393835) B393835
theorem B885563 : Blo 346754 885563 := bstep (se 1 (by rfl) ⟨664172, by rfl⟩ : syracuseStep 885563 = 1328345) B1328345
theorem B3343193 : Blo 346754 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B3015539 : Blo 346754 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B787319 : Blo 346754 787319 := bstep (se 1 (by rfl) ⟨590489, by rfl⟩ : syracuseStep 787319 = 1180979) B1180979
theorem B525191 : Blo 346754 525191 := bstep (se 1 (by rfl) ⟨393893, by rfl⟩ : syracuseStep 525191 = 787787) B787787
theorem B2392985 : Blo 346754 2392985 := bstep (se 2 (by rfl) ⟨897369, by rfl⟩ : syracuseStep 2392985 = 1794739) B1794739
theorem B525227 : Blo 346754 525227 := bstep (se 1 (by rfl) ⟨393920, by rfl⟩ : syracuseStep 525227 = 787841) B787841
theorem B1180601 : Blo 346754 1180601 := bstep (se 2 (by rfl) ⟨442725, by rfl⟩ : syracuseStep 1180601 = 885451) B885451
theorem B525257 : Blo 346754 525257 := bstep (se 2 (by rfl) ⟨196971, by rfl⟩ : syracuseStep 525257 = 393943) B393943
theorem B54887381 : Blo 346754 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B558095 : Blo 346754 558095 := bstep (se 1 (by rfl) ⟨418571, by rfl⟩ : syracuseStep 558095 = 837143) B837143
theorem B885775 : Blo 346754 885775 := bstep (se 1 (by rfl) ⟨664331, by rfl⟩ : syracuseStep 885775 = 1328663) B1328663
theorem B1115165 : Blo 346754 1115165 := bstep (se 3 (by rfl) ⟨209093, by rfl⟩ : syracuseStep 1115165 = 418187) B418187
theorem B787499 : Blo 346754 787499 := bstep (se 1 (by rfl) ⟨590624, by rfl⟩ : syracuseStep 787499 = 1181249) B1181249
theorem B525371 : Blo 346754 525371 := bstep (se 1 (by rfl) ⟨394028, by rfl⟩ : syracuseStep 525371 = 788057) B788057
theorem B525431 : Blo 346754 525431 := bstep (se 1 (by rfl) ⟨394073, by rfl⟩ : syracuseStep 525431 = 788147) B788147
theorem B394375 : Blo 346754 394375 := bstep (se 1 (by rfl) ⟨295781, by rfl⟩ : syracuseStep 394375 = 591563) B591563
theorem B525455 : Blo 346754 525455 := bstep (se 1 (by rfl) ⟨394091, by rfl⟩ : syracuseStep 525455 = 788183) B788183
theorem B525497 : Blo 346754 525497 := bstep (se 2 (by rfl) ⟨197061, by rfl⟩ : syracuseStep 525497 = 394123) B394123
theorem B525575 : Blo 346754 525575 := bstep (se 1 (by rfl) ⟨394181, by rfl⟩ : syracuseStep 525575 = 788363) B788363
theorem B886049 : Blo 346754 886049 := bstep (se 2 (by rfl) ⟨332268, by rfl⟩ : syracuseStep 886049 = 664537) B664537
theorem B525611 : Blo 346754 525611 := bstep (se 1 (by rfl) ⟨394208, by rfl⟩ : syracuseStep 525611 = 788417) B788417
theorem B394555 : Blo 346754 394555 := bstep (se 1 (by rfl) ⟨295916, by rfl⟩ : syracuseStep 394555 = 591833) B591833
theorem B525641 : Blo 346754 525641 := bstep (se 2 (by rfl) ⟨197115, by rfl⟩ : syracuseStep 525641 = 394231) B394231
theorem B591239 : Blo 346754 591239 := bstep (se 1 (by rfl) ⟨443429, by rfl⟩ : syracuseStep 591239 = 886859) B886859
theorem B1672595 : Blo 346754 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B787859 : Blo 346754 787859 := bstep (se 1 (by rfl) ⟨590894, by rfl⟩ : syracuseStep 787859 = 1181789) B1181789
theorem B11306425 : Blo 346754 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B525755 : Blo 346754 525755 := bstep (se 1 (by rfl) ⟨394316, by rfl⟩ : syracuseStep 525755 = 788633) B788633
theorem B787913 : Blo 346754 787913 := bstep (se 2 (by rfl) ⟨295467, by rfl⟩ : syracuseStep 787913 = 590935) B590935
theorem B525815 : Blo 346754 525815 := bstep (se 1 (by rfl) ⟨394361, by rfl⟩ : syracuseStep 525815 = 788723) B788723
theorem B1181195 : Blo 346754 1181195 := bstep (se 1 (by rfl) ⟨885896, by rfl⟩ : syracuseStep 1181195 = 1771793) B1771793
theorem B525839 : Blo 346754 525839 := bstep (se 1 (by rfl) ⟨394379, by rfl⟩ : syracuseStep 525839 = 788759) B788759
theorem B525881 : Blo 346754 525881 := bstep (se 2 (by rfl) ⟨197205, by rfl⟩ : syracuseStep 525881 = 394411) B394411
theorem B5375587 : Blo 346754 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B1181303 : Blo 346754 1181303 := bstep (se 1 (by rfl) ⟨885977, by rfl⟩ : syracuseStep 1181303 = 1771955) B1771955
theorem B525959 : Blo 346754 525959 := bstep (se 1 (by rfl) ⟨394469, by rfl⟩ : syracuseStep 525959 = 788939) B788939
theorem B525995 : Blo 346754 525995 := bstep (se 1 (by rfl) ⟨394496, by rfl⟩ : syracuseStep 525995 = 788993) B788993
theorem B526025 : Blo 346754 526025 := bstep (se 2 (by rfl) ⟨197259, by rfl⟩ : syracuseStep 526025 = 394519) B394519
theorem B2623205 : Blo 346754 2623205 := bstep (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) B491851
theorem B558967 : Blo 346754 558967 := bstep (se 1 (by rfl) ⟨419225, by rfl⟩ : syracuseStep 558967 = 838451) B838451
theorem B2131865 : Blo 346754 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B1116089 : Blo 346754 1116089 := bstep (se 2 (by rfl) ⟨418533, by rfl⟩ : syracuseStep 1116089 = 837067) B837067
theorem B2131915 : Blo 346754 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B1411025 : Blo 346754 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B591887 : Blo 346754 591887 := bstep (se 1 (by rfl) ⟨443915, by rfl⟩ : syracuseStep 591887 = 887831) B887831
theorem B788615 : Blo 346754 788615 := bstep (se 1 (by rfl) ⟨591461, by rfl⟩ : syracuseStep 788615 = 1182923) B1182923
theorem B1181897 : Blo 346754 1181897 := bstep (se 2 (by rfl) ⟨443211, by rfl⟩ : syracuseStep 1181897 = 886423) B886423
theorem B887051 : Blo 346754 887051 := bstep (se 1 (by rfl) ⟨665288, by rfl⟩ : syracuseStep 887051 = 1330577) B1330577
theorem B559403 : Blo 346754 559403 := bstep (se 1 (by rfl) ⟨419552, by rfl⟩ : syracuseStep 559403 = 839105) B839105
theorem B788795 : Blo 346754 788795 := bstep (se 1 (by rfl) ⟨591596, by rfl⟩ : syracuseStep 788795 = 1183193) B1183193
theorem B493943 : Blo 346754 493943 := bstep (se 1 (by rfl) ⟨370457, by rfl⟩ : syracuseStep 493943 = 740915) B740915
theorem B788921 : Blo 346754 788921 := bstep (se 2 (by rfl) ⟨295845, by rfl⟩ : syracuseStep 788921 = 591691) B591691
theorem B494137 : Blo 346754 494137 := bstep (se 2 (by rfl) ⟨185301, by rfl⟩ : syracuseStep 494137 = 370603) B370603
theorem B6687299 : Blo 346754 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B2656961 : Blo 346754 2656961 := bstep (se 2 (by rfl) ⟨996360, by rfl⟩ : syracuseStep 2656961 = 1992721) B1992721
theorem B4950821 : Blo 346754 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B4787059 : Blo 346754 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B1182599 : Blo 346754 1182599 := bstep (se 1 (by rfl) ⟨886949, by rfl⟩ : syracuseStep 1182599 = 1773899) B1773899
theorem B887699 : Blo 346754 887699 := bstep (se 1 (by rfl) ⟨665774, by rfl⟩ : syracuseStep 887699 = 1331549) B1331549
theorem B1772441 : Blo 346754 1772441 := bstep (se 2 (by rfl) ⟨664665, by rfl⟩ : syracuseStep 1772441 = 1329331) B1329331
theorem B1182977 : Blo 346754 1182977 := bstep (se 2 (by rfl) ⟨443616, by rfl⟩ : syracuseStep 1182977 = 887233) B887233
theorem B495035 : Blo 346754 495035 := bstep (se 1 (by rfl) ⟨371276, by rfl⟩ : syracuseStep 495035 = 742553) B742553
theorem B659335 : Blo 346754 659335 := bstep (se 1 (by rfl) ⟨494501, by rfl⟩ : syracuseStep 659335 = 989003) B989003
theorem B7606219 : Blo 346754 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B1183787 : Blo 346754 1183787 := bstep (se 1 (by rfl) ⟨887840, by rfl⟩ : syracuseStep 1183787 = 1775681) B1775681
theorem B2691245 : Blo 346754 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B2003201 : Blo 346754 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B987511 : Blo 346754 987511 := bstep (se 1 (by rfl) ⟨740633, by rfl⟩ : syracuseStep 987511 = 1481267) B1481267
theorem B987545 : Blo 346754 987545 := bstep (se 2 (by rfl) ⟨370329, by rfl⟩ : syracuseStep 987545 = 740659) B740659
theorem B659897 : Blo 346754 659897 := bstep (se 2 (by rfl) ⟨247461, by rfl⟩ : syracuseStep 659897 = 494923) B494923
theorem B987659 : Blo 346754 987659 := bstep (se 1 (by rfl) ⟨740744, by rfl⟩ : syracuseStep 987659 = 1481489) B1481489
theorem B594551 : Blo 346754 594551 := bstep (se 1 (by rfl) ⟨445913, by rfl⟩ : syracuseStep 594551 = 891827) B891827
theorem B2429963 : Blo 346754 2429963 := bstep (se 1 (by rfl) ⟨1822472, by rfl⟩ : syracuseStep 2429963 = 3644945) B3644945
theorem B3347729 : Blo 346754 3347729 := bstep (se 2 (by rfl) ⟨1255398, by rfl⟩ : syracuseStep 3347729 = 2510797) B2510797
theorem B16258421 : Blo 346754 16258421 := bstep (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) B1524227
theorem B1775033 : Blo 346754 1775033 := bstep (se 2 (by rfl) ⟨665637, by rfl⟩ : syracuseStep 1775033 = 1331275) B1331275
theorem B661051 : Blo 346754 661051 := bstep (se 1 (by rfl) ⟨495788, by rfl⟩ : syracuseStep 661051 = 991577) B991577
theorem B988787 : Blo 346754 988787 := bstep (se 1 (by rfl) ⟨741590, by rfl⟩ : syracuseStep 988787 = 1483181) B1483181
theorem B989185 : Blo 346754 989185 := bstep (se 2 (by rfl) ⟨370944, by rfl⟩ : syracuseStep 989185 = 741889) B741889
theorem B2660363 : Blo 346754 2660363 := bstep (se 1 (by rfl) ⟨1995272, by rfl⟩ : syracuseStep 2660363 = 3990545) B3990545
theorem B661537 : Blo 346754 661537 := bstep (se 2 (by rfl) ⟨248076, by rfl⟩ : syracuseStep 661537 = 496153) B496153
theorem B989243 : Blo 346754 989243 := bstep (se 1 (by rfl) ⟨741932, by rfl⟩ : syracuseStep 989243 = 1483865) B1483865
theorem B956569 : Blo 346754 956569 := bstep (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) B717427
theorem B2235251 : Blo 346754 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B1875251 : Blo 346754 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B662843 : Blo 346754 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B1121651 : Blo 346754 1121651 := bstep (se 1 (by rfl) ⟨841238, by rfl⟩ : syracuseStep 1121651 = 1682477) B1682477
theorem B1678745 : Blo 346754 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B957881 : Blo 346754 957881 := bstep (se 2 (by rfl) ⟨359205, by rfl⟩ : syracuseStep 957881 = 718411) B718411
theorem B1875421 : Blo 346754 1875421 := bstep (se 3 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 1875421 = 703283) B703283
theorem B597775 : Blo 346754 597775 := bstep (se 1 (by rfl) ⟨448331, by rfl⟩ : syracuseStep 597775 = 896663) B896663
theorem B663329 : Blo 346754 663329 := bstep (se 2 (by rfl) ⟨248748, by rfl⟩ : syracuseStep 663329 = 497497) B497497
theorem B2662307 : Blo 346754 2662307 := bstep (se 1 (by rfl) ⟨1996730, by rfl⟩ : syracuseStep 2662307 = 3993461) B3993461
theorem B663481 : Blo 346754 663481 := bstep (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) B497611
theorem B1056883 : Blo 346754 1056883 := bstep (se 1 (by rfl) ⟨792662, by rfl⟩ : syracuseStep 1056883 = 1585325) B1585325
theorem B532651 : Blo 346754 532651 := bstep (se 1 (by rfl) ⟨399488, by rfl⟩ : syracuseStep 532651 = 798977) B798977
theorem B991531 : Blo 346754 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B991759 : Blo 346754 991759 := bstep (se 1 (by rfl) ⟨743819, by rfl⟩ : syracuseStep 991759 = 1487639) B1487639
theorem B1876567 : Blo 346754 1876567 := bstep (se 1 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 1876567 = 2814851) B2814851
theorem B992033 : Blo 346754 992033 := bstep (se 2 (by rfl) ⟨372012, by rfl⟩ : syracuseStep 992033 = 744025) B744025
theorem B1975225 : Blo 346754 1975225 := bstep (se 2 (by rfl) ⟨740709, by rfl⟩ : syracuseStep 1975225 = 1481419) B1481419
theorem B893953 : Blo 346754 893953 := bstep (se 2 (by rfl) ⟨335232, by rfl⟩ : syracuseStep 893953 = 670465) B670465
theorem B992375 : Blo 346754 992375 := bstep (se 1 (by rfl) ⟨744281, by rfl⟩ : syracuseStep 992375 = 1488563) B1488563
theorem B1320401 : Blo 346754 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B665273 : Blo 346754 665273 := bstep (se 2 (by rfl) ⟨249477, by rfl⟩ : syracuseStep 665273 = 498955) B498955
theorem B993035 : Blo 346754 993035 := bstep (se 1 (by rfl) ⟨744776, by rfl⟩ : syracuseStep 993035 = 1489553) B1489553
theorem B1320857 : Blo 346754 1320857 := bstep (se 2 (by rfl) ⟨495321, by rfl⟩ : syracuseStep 1320857 = 990643) B990643
theorem B2238941 : Blo 346754 2238941 := bstep (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) B839603
theorem B11447203 : Blo 346754 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B535481 : Blo 346754 535481 := bstep (se 2 (by rfl) ⟨200805, by rfl⟩ : syracuseStep 535481 = 401611) B401611
theorem B1322027 : Blo 346754 1322027 := bstep (se 1 (by rfl) ⟨991520, by rfl⟩ : syracuseStep 1322027 = 1983041) B1983041
theorem B994619 : Blo 346754 994619 := bstep (se 1 (by rfl) ⟨745964, by rfl⟩ : syracuseStep 994619 = 1491929) B1491929
theorem B994675 : Blo 346754 994675 := bstep (se 1 (by rfl) ⟨746006, by rfl⟩ : syracuseStep 994675 = 1492013) B1492013
theorem B1256971 : Blo 346754 1256971 := bstep (se 1 (by rfl) ⟨942728, by rfl⟩ : syracuseStep 1256971 = 1885457) B1885457
theorem B1879595 : Blo 346754 1879595 := bstep (se 1 (by rfl) ⟨1409696, by rfl⟩ : syracuseStep 1879595 = 2819393) B2819393
theorem B1420919 : Blo 346754 1420919 := bstep (se 1 (by rfl) ⟨1065689, by rfl⟩ : syracuseStep 1420919 = 2131379) B2131379
theorem B372367 : Blo 346754 372367 := bstep (se 1 (by rfl) ⟨279275, by rfl⟩ : syracuseStep 372367 = 558551) B558551
theorem B995017 : Blo 346754 995017 := bstep (se 2 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 995017 = 746263) B746263
theorem B2634119 : Blo 346754 2634119 := bstep (se 1 (by rfl) ⟨1975589, by rfl⟩ : syracuseStep 2634119 = 3951179) B3951179
theorem B1782161 : Blo 346754 1782161 := bstep (se 2 (by rfl) ⟨668310, by rfl⟩ : syracuseStep 1782161 = 1336621) B1336621
theorem B471467 : Blo 346754 471467 := bstep (se 1 (by rfl) ⟨353600, by rfl⟩ : syracuseStep 471467 = 707201) B707201
theorem B1323985 : Blo 346754 1323985 := bstep (se 2 (by rfl) ⟨496494, by rfl⟩ : syracuseStep 1323985 = 992989) B992989
theorem B439339 : Blo 346754 439339 := bstep (se 1 (by rfl) ⟨329504, by rfl⟩ : syracuseStep 439339 = 659009) B659009
theorem B2962565 : Blo 346754 2962565 := bstep (se 4 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 2962565 = 555481) B555481
theorem B1324289 : Blo 346754 1324289 := bstep (se 2 (by rfl) ⟨496608, by rfl⟩ : syracuseStep 1324289 = 993217) B993217
theorem B3356225 : Blo 346754 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B2012759 : Blo 346754 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B3356261 : Blo 346754 3356261 := bstep (se 4 (by rfl) ⟨314649, by rfl⟩ : syracuseStep 3356261 = 629299) B629299
theorem B1324745 : Blo 346754 1324745 := bstep (se 2 (by rfl) ⟨496779, by rfl⟩ : syracuseStep 1324745 = 993559) B993559
theorem B2111233 : Blo 346754 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B1685281 : Blo 346754 1685281 := bstep (se 2 (by rfl) ⟨631980, by rfl⟩ : syracuseStep 1685281 = 1263961) B1263961
theorem B2963249 : Blo 346754 2963249 := bstep (se 2 (by rfl) ⟨1111218, by rfl⟩ : syracuseStep 2963249 = 2222437) B2222437
theorem B997181 : Blo 346754 997181 := bstep (se 3 (by rfl) ⟨186971, by rfl⟩ : syracuseStep 997181 = 373943) B373943
theorem B1587059 : Blo 346754 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B440311 : Blo 346754 440311 := bstep (se 1 (by rfl) ⟨330233, by rfl⟩ : syracuseStep 440311 = 660467) B660467
theorem B997409 : Blo 346754 997409 := bstep (se 2 (by rfl) ⟨374028, by rfl⟩ : syracuseStep 997409 = 748057) B748057
theorem B473359 : Blo 346754 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B440635 : Blo 346754 440635 := bstep (se 1 (by rfl) ⟨330476, by rfl⟩ : syracuseStep 440635 = 660953) B660953
theorem B1489211 : Blo 346754 1489211 := bstep (se 1 (by rfl) ⟨1116908, by rfl⟩ : syracuseStep 1489211 = 2233817) B2233817
theorem B997751 : Blo 346754 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B1915289 : Blo 346754 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B1980875 : Blo 346754 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B834337 : Blo 346754 834337 := bstep (se 2 (by rfl) ⟨312876, by rfl⟩ : syracuseStep 834337 = 625753) B625753
theorem B2964275 : Blo 346754 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B5389145 : Blo 346754 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B1981331 : Blo 346754 1981331 := bstep (se 1 (by rfl) ⟨1485998, by rfl⟩ : syracuseStep 1981331 = 2971997) B2971997
theorem B441607 : Blo 346754 441607 := bstep (se 1 (by rfl) ⟨331205, by rfl⟩ : syracuseStep 441607 = 662411) B662411
theorem B3030419 : Blo 346754 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B2571895 : Blo 346754 2571895 := bstep (se 1 (by rfl) ⟨1928921, by rfl⟩ : syracuseStep 2571895 = 3857843) B3857843
theorem B704135 : Blo 346754 704135 := bstep (se 1 (by rfl) ⟨528101, by rfl⟩ : syracuseStep 704135 = 1056203) B1056203
theorem B442027 : Blo 346754 442027 := bstep (se 1 (by rfl) ⟨331520, by rfl⟩ : syracuseStep 442027 = 663041) B663041
theorem B1064765 : Blo 346754 1064765 := bstep (se 3 (by rfl) ⟨199643, by rfl⟩ : syracuseStep 1064765 = 399287) B399287
theorem B442255 : Blo 346754 442255 := bstep (se 1 (by rfl) ⟨331691, by rfl⟩ : syracuseStep 442255 = 663383) B663383
theorem B1490987 : Blo 346754 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B835703 : Blo 346754 835703 := bstep (se 1 (by rfl) ⟨626777, by rfl⟩ : syracuseStep 835703 = 1253555) B1253555
theorem B3784877 : Blo 346754 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B704783 : Blo 346754 704783 := bstep (se 1 (by rfl) ⟨528587, by rfl⟩ : syracuseStep 704783 = 1057175) B1057175
theorem B5030237 : Blo 346754 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B4014521 : Blo 346754 4014521 := bstep (se 2 (by rfl) ⟨1505445, by rfl⟩ : syracuseStep 4014521 = 3010891) B3010891
theorem B836183 : Blo 346754 836183 := bstep (se 1 (by rfl) ⟨627137, by rfl⟩ : syracuseStep 836183 = 1254275) B1254275
theorem B442999 : Blo 346754 442999 := bstep (se 1 (by rfl) ⟨332249, by rfl⟩ : syracuseStep 442999 = 664499) B664499
theorem B1327873 : Blo 346754 1327873 := bstep (se 2 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 1327873 = 995905) B995905
theorem B443323 : Blo 346754 443323 := bstep (se 1 (by rfl) ⟨332492, by rfl⟩ : syracuseStep 443323 = 664985) B664985
theorem B1491979 : Blo 346754 1491979 := bstep (se 1 (by rfl) ⟨1118984, by rfl⟩ : syracuseStep 1491979 = 2237969) B2237969
theorem B1590359 : Blo 346754 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B443819 : Blo 346754 443819 := bstep (se 1 (by rfl) ⟨332864, by rfl⟩ : syracuseStep 443819 = 665729) B665729
theorem B2835971 : Blo 346754 2835971 := bstep (se 1 (by rfl) ⟨2126978, by rfl⟩ : syracuseStep 2835971 = 4253957) B4253957
theorem B2508407 : Blo 346754 2508407 := bstep (se 1 (by rfl) ⟨1881305, by rfl⟩ : syracuseStep 2508407 = 3762611) B3762611
theorem B3983255 : Blo 346754 3983255 := bstep (se 1 (by rfl) ⟨2987441, by rfl⟩ : syracuseStep 3983255 = 5974883) B5974883
theorem B2837035 : Blo 346754 2837035 := bstep (se 1 (by rfl) ⟨2127776, by rfl⟩ : syracuseStep 2837035 = 4255553) B4255553
theorem B4508227 : Blo 346754 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B838259 : Blo 346754 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B346759 : Blo 346754 346759 := bstep (se 1 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 346759 = 520139) B520139
theorem B346767 : Blo 346754 346767 := bstep (se 1 (by rfl) ⟨260075, by rfl⟩ : syracuseStep 346767 = 520151) B520151
theorem B346811 : Blo 346754 346811 := bstep (se 1 (by rfl) ⟨260108, by rfl⟩ : syracuseStep 346811 = 520217) B520217
theorem B1198793 : Blo 346754 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B346887 : Blo 346754 346887 := bstep (se 1 (by rfl) ⟨260165, by rfl⟩ : syracuseStep 346887 = 520331) B520331
theorem B346895 : Blo 346754 346895 := bstep (se 1 (by rfl) ⟨260171, by rfl⟩ : syracuseStep 346895 = 520343) B520343
theorem B346939 : Blo 346754 346939 := bstep (se 1 (by rfl) ⟨260204, by rfl⟩ : syracuseStep 346939 = 520409) B520409
theorem B347015 : Blo 346754 347015 := bstep (se 1 (by rfl) ⟨260261, by rfl⟩ : syracuseStep 347015 = 520523) B520523
theorem B347023 : Blo 346754 347023 := bstep (se 1 (by rfl) ⟨260267, by rfl⟩ : syracuseStep 347023 = 520535) B520535
theorem B347067 : Blo 346754 347067 := bstep (se 1 (by rfl) ⟨260300, by rfl⟩ : syracuseStep 347067 = 520601) B520601
theorem B347143 : Blo 346754 347143 := bstep (se 1 (by rfl) ⟨260357, by rfl⟩ : syracuseStep 347143 = 520715) B520715
theorem B347151 : Blo 346754 347151 := bstep (se 1 (by rfl) ⟨260363, by rfl⟩ : syracuseStep 347151 = 520727) B520727
theorem B347195 : Blo 346754 347195 := bstep (se 1 (by rfl) ⟨260396, by rfl⟩ : syracuseStep 347195 = 520793) B520793
theorem B347271 : Blo 346754 347271 := bstep (se 1 (by rfl) ⟨260453, by rfl⟩ : syracuseStep 347271 = 520907) B520907
theorem B347279 : Blo 346754 347279 := bstep (se 1 (by rfl) ⟨260459, by rfl⟩ : syracuseStep 347279 = 520919) B520919
theorem B347323 : Blo 346754 347323 := bstep (se 1 (by rfl) ⟨260492, by rfl⟩ : syracuseStep 347323 = 520985) B520985
theorem B2018533 : Blo 346754 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B347399 : Blo 346754 347399 := bstep (se 1 (by rfl) ⟨260549, by rfl⟩ : syracuseStep 347399 = 521099) B521099
theorem B347407 : Blo 346754 347407 := bstep (se 1 (by rfl) ⟨260555, by rfl⟩ : syracuseStep 347407 = 521111) B521111
theorem B871723 : Blo 346754 871723 := bstep (se 1 (by rfl) ⟨653792, by rfl⟩ : syracuseStep 871723 = 1307585) B1307585
theorem B347451 : Blo 346754 347451 := bstep (se 1 (by rfl) ⟨260588, by rfl⟩ : syracuseStep 347451 = 521177) B521177
theorem B347527 : Blo 346754 347527 := bstep (se 1 (by rfl) ⟨260645, by rfl⟩ : syracuseStep 347527 = 521291) B521291
theorem B347535 : Blo 346754 347535 := bstep (se 1 (by rfl) ⟨260651, by rfl⟩ : syracuseStep 347535 = 521303) B521303
theorem B347579 : Blo 346754 347579 := bstep (se 1 (by rfl) ⟨260684, by rfl⟩ : syracuseStep 347579 = 521369) B521369
theorem B347655 : Blo 346754 347655 := bstep (se 1 (by rfl) ⟨260741, by rfl⟩ : syracuseStep 347655 = 521483) B521483
theorem B347663 : Blo 346754 347663 := bstep (se 1 (by rfl) ⟨260747, by rfl⟩ : syracuseStep 347663 = 521495) B521495
theorem B347707 : Blo 346754 347707 := bstep (se 1 (by rfl) ⟨260780, by rfl⟩ : syracuseStep 347707 = 521561) B521561
theorem B1330775 : Blo 346754 1330775 := bstep (se 1 (by rfl) ⟨998081, by rfl⟩ : syracuseStep 1330775 = 1996163) B1996163
theorem B740983 : Blo 346754 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B347783 : Blo 346754 347783 := bstep (se 1 (by rfl) ⟨260837, by rfl⟩ : syracuseStep 347783 = 521675) B521675
theorem B347791 : Blo 346754 347791 := bstep (se 1 (by rfl) ⟨260843, by rfl⟩ : syracuseStep 347791 = 521687) B521687
theorem B347835 : Blo 346754 347835 := bstep (se 1 (by rfl) ⟨260876, by rfl⟩ : syracuseStep 347835 = 521753) B521753
theorem B347911 : Blo 346754 347911 := bstep (se 1 (by rfl) ⟨260933, by rfl⟩ : syracuseStep 347911 = 521867) B521867
theorem B347919 : Blo 346754 347919 := bstep (se 1 (by rfl) ⟨260939, by rfl⟩ : syracuseStep 347919 = 521879) B521879
theorem B3821347 : Blo 346754 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B347963 : Blo 346754 347963 := bstep (se 1 (by rfl) ⟨260972, by rfl⟩ : syracuseStep 347963 = 521945) B521945
theorem B348039 : Blo 346754 348039 := bstep (se 1 (by rfl) ⟨261029, by rfl⟩ : syracuseStep 348039 = 522059) B522059
theorem B348047 : Blo 346754 348047 := bstep (se 1 (by rfl) ⟨261035, by rfl⟩ : syracuseStep 348047 = 522071) B522071
theorem B348091 : Blo 346754 348091 := bstep (se 1 (by rfl) ⟨261068, by rfl⟩ : syracuseStep 348091 = 522137) B522137
theorem B348167 : Blo 346754 348167 := bstep (se 1 (by rfl) ⟨261125, by rfl⟩ : syracuseStep 348167 = 522251) B522251
theorem B348175 : Blo 346754 348175 := bstep (se 1 (by rfl) ⟨261131, by rfl⟩ : syracuseStep 348175 = 522263) B522263
theorem B1757213 : Blo 346754 1757213 := bstep (se 3 (by rfl) ⟨329477, by rfl⟩ : syracuseStep 1757213 = 658955) B658955
theorem B348219 : Blo 346754 348219 := bstep (se 1 (by rfl) ⟨261164, by rfl⟩ : syracuseStep 348219 = 522329) B522329
theorem B1331261 : Blo 346754 1331261 := bstep (se 3 (by rfl) ⟨249611, by rfl⟩ : syracuseStep 1331261 = 499223) B499223
theorem B1790039 : Blo 346754 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B348295 : Blo 346754 348295 := bstep (se 1 (by rfl) ⟨261221, by rfl⟩ : syracuseStep 348295 = 522443) B522443
theorem B348303 : Blo 346754 348303 := bstep (se 1 (by rfl) ⟨261227, by rfl⟩ : syracuseStep 348303 = 522455) B522455
theorem B348347 : Blo 346754 348347 := bstep (se 1 (by rfl) ⟨261260, by rfl⟩ : syracuseStep 348347 = 522521) B522521
theorem B348423 : Blo 346754 348423 := bstep (se 1 (by rfl) ⟨261317, by rfl⟩ : syracuseStep 348423 = 522635) B522635
theorem B348431 : Blo 346754 348431 := bstep (se 1 (by rfl) ⟨261323, by rfl⟩ : syracuseStep 348431 = 522647) B522647
theorem B348475 : Blo 346754 348475 := bstep (se 1 (by rfl) ⟨261356, by rfl⟩ : syracuseStep 348475 = 522713) B522713
theorem B348551 : Blo 346754 348551 := bstep (se 1 (by rfl) ⟨261413, by rfl⟩ : syracuseStep 348551 = 522827) B522827
theorem B348559 : Blo 346754 348559 := bstep (se 1 (by rfl) ⟨261419, by rfl⟩ : syracuseStep 348559 = 522839) B522839
theorem B348603 : Blo 346754 348603 := bstep (se 1 (by rfl) ⟨261452, by rfl⟩ : syracuseStep 348603 = 522905) B522905
theorem B1757699 : Blo 346754 1757699 := bstep (se 1 (by rfl) ⟨1318274, by rfl⟩ : syracuseStep 1757699 = 2636549) B2636549
theorem B348679 : Blo 346754 348679 := bstep (se 1 (by rfl) ⟨261509, by rfl⟩ : syracuseStep 348679 = 523019) B523019
theorem B348687 : Blo 346754 348687 := bstep (se 1 (by rfl) ⟨261515, by rfl⟩ : syracuseStep 348687 = 523031) B523031
theorem B18469397 : Blo 346754 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B348731 : Blo 346754 348731 := bstep (se 1 (by rfl) ⟨261548, by rfl⟩ : syracuseStep 348731 = 523097) B523097
theorem B348807 : Blo 346754 348807 := bstep (se 1 (by rfl) ⟨261605, by rfl⟩ : syracuseStep 348807 = 523211) B523211
theorem B381583 : Blo 346754 381583 := bstep (se 1 (by rfl) ⟨286187, by rfl⟩ : syracuseStep 381583 = 572375) B572375
theorem B348815 : Blo 346754 348815 := bstep (se 1 (by rfl) ⟨261611, by rfl⟩ : syracuseStep 348815 = 523223) B523223
theorem B348859 : Blo 346754 348859 := bstep (se 1 (by rfl) ⟨261644, by rfl⟩ : syracuseStep 348859 = 523289) B523289
theorem B348935 : Blo 346754 348935 := bstep (se 1 (by rfl) ⟨261701, by rfl⟩ : syracuseStep 348935 = 523403) B523403
theorem B348943 : Blo 346754 348943 := bstep (se 1 (by rfl) ⟨261707, by rfl⟩ : syracuseStep 348943 = 523415) B523415
theorem B348987 : Blo 346754 348987 := bstep (se 1 (by rfl) ⟨261740, by rfl⟩ : syracuseStep 348987 = 523481) B523481
theorem B349063 : Blo 346754 349063 := bstep (se 1 (by rfl) ⟨261797, by rfl⟩ : syracuseStep 349063 = 523595) B523595
theorem B349071 : Blo 346754 349071 := bstep (se 1 (by rfl) ⟨261803, by rfl⟩ : syracuseStep 349071 = 523607) B523607
theorem B349115 : Blo 346754 349115 := bstep (se 1 (by rfl) ⟨261836, by rfl⟩ : syracuseStep 349115 = 523673) B523673
theorem B1790923 : Blo 346754 1790923 := bstep (se 1 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 1790923 = 2686385) B2686385
theorem B349191 : Blo 346754 349191 := bstep (se 1 (by rfl) ⟨261893, by rfl⟩ : syracuseStep 349191 = 523787) B523787
theorem B349199 : Blo 346754 349199 := bstep (se 1 (by rfl) ⟨261899, by rfl⟩ : syracuseStep 349199 = 523799) B523799
theorem B840719 : Blo 346754 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B349243 : Blo 346754 349243 := bstep (se 1 (by rfl) ⟨261932, by rfl⟩ : syracuseStep 349243 = 523865) B523865
theorem B939095 : Blo 346754 939095 := bstep (se 1 (by rfl) ⟨704321, by rfl⟩ : syracuseStep 939095 = 1408643) B1408643
theorem B349319 : Blo 346754 349319 := bstep (se 1 (by rfl) ⟨261989, by rfl⟩ : syracuseStep 349319 = 523979) B523979
theorem B349327 : Blo 346754 349327 := bstep (se 1 (by rfl) ⟨261995, by rfl⟩ : syracuseStep 349327 = 523991) B523991
theorem B742547 : Blo 346754 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B349371 : Blo 346754 349371 := bstep (se 1 (by rfl) ⟨262028, by rfl⟩ : syracuseStep 349371 = 524057) B524057
theorem B4084937 : Blo 346754 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B349447 : Blo 346754 349447 := bstep (se 1 (by rfl) ⟨262085, by rfl⟩ : syracuseStep 349447 = 524171) B524171
theorem B349455 : Blo 346754 349455 := bstep (se 1 (by rfl) ⟨262091, by rfl⟩ : syracuseStep 349455 = 524183) B524183
theorem B1496353 : Blo 346754 1496353 := bstep (se 2 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 1496353 = 1122265) B1122265
theorem B677179 : Blo 346754 677179 := bstep (se 1 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 677179 = 1015769) B1015769
theorem B349499 : Blo 346754 349499 := bstep (se 1 (by rfl) ⟨262124, by rfl⟩ : syracuseStep 349499 = 524249) B524249
theorem B1889671 : Blo 346754 1889671 := bstep (se 1 (by rfl) ⟨1417253, by rfl⟩ : syracuseStep 1889671 = 2834507) B2834507
theorem B349575 : Blo 346754 349575 := bstep (se 1 (by rfl) ⟨262181, by rfl⟩ : syracuseStep 349575 = 524363) B524363
theorem B349583 : Blo 346754 349583 := bstep (se 1 (by rfl) ⟨262187, by rfl⟩ : syracuseStep 349583 = 524375) B524375
theorem B349627 : Blo 346754 349627 := bstep (se 1 (by rfl) ⟨262220, by rfl⟩ : syracuseStep 349627 = 524441) B524441
theorem B349703 : Blo 346754 349703 := bstep (se 1 (by rfl) ⟨262277, by rfl⟩ : syracuseStep 349703 = 524555) B524555
theorem B349711 : Blo 346754 349711 := bstep (se 1 (by rfl) ⟨262283, by rfl⟩ : syracuseStep 349711 = 524567) B524567
theorem B349755 : Blo 346754 349755 := bstep (se 1 (by rfl) ⟨262316, by rfl⟩ : syracuseStep 349755 = 524633) B524633
theorem B349831 : Blo 346754 349831 := bstep (se 1 (by rfl) ⟨262373, by rfl⟩ : syracuseStep 349831 = 524747) B524747
theorem B349839 : Blo 346754 349839 := bstep (se 1 (by rfl) ⟨262379, by rfl⟩ : syracuseStep 349839 = 524759) B524759
theorem B349883 : Blo 346754 349883 := bstep (se 1 (by rfl) ⟨262412, by rfl⟩ : syracuseStep 349883 = 524825) B524825
theorem B349959 : Blo 346754 349959 := bstep (se 1 (by rfl) ⟨262469, by rfl⟩ : syracuseStep 349959 = 524939) B524939
theorem B349967 : Blo 346754 349967 := bstep (se 1 (by rfl) ⟨262475, by rfl⟩ : syracuseStep 349967 = 524951) B524951
theorem B350011 : Blo 346754 350011 := bstep (se 1 (by rfl) ⟨262508, by rfl⟩ : syracuseStep 350011 = 525017) B525017
theorem B350087 : Blo 346754 350087 := bstep (se 1 (by rfl) ⟨262565, by rfl⟩ : syracuseStep 350087 = 525131) B525131
theorem B350095 : Blo 346754 350095 := bstep (se 1 (by rfl) ⟨262571, by rfl⟩ : syracuseStep 350095 = 525143) B525143
theorem B350139 : Blo 346754 350139 := bstep (se 1 (by rfl) ⟨262604, by rfl⟩ : syracuseStep 350139 = 525209) B525209
theorem B350215 : Blo 346754 350215 := bstep (se 1 (by rfl) ⟨262661, by rfl⟩ : syracuseStep 350215 = 525323) B525323
theorem B350223 : Blo 346754 350223 := bstep (se 1 (by rfl) ⟨262667, by rfl⟩ : syracuseStep 350223 = 525335) B525335
theorem B350267 : Blo 346754 350267 := bstep (se 1 (by rfl) ⟨262700, by rfl⟩ : syracuseStep 350267 = 525401) B525401
theorem B1759319 : Blo 346754 1759319 := bstep (se 1 (by rfl) ⟨1319489, by rfl⟩ : syracuseStep 1759319 = 2638979) B2638979
theorem B350343 : Blo 346754 350343 := bstep (se 1 (by rfl) ⟨262757, by rfl⟩ : syracuseStep 350343 = 525515) B525515
theorem B350351 : Blo 346754 350351 := bstep (se 1 (by rfl) ⟨262763, by rfl⟩ : syracuseStep 350351 = 525527) B525527
theorem B3987629 : Blo 346754 3987629 := bstep (se 3 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 3987629 = 1495361) B1495361
theorem B350395 : Blo 346754 350395 := bstep (se 1 (by rfl) ⟨262796, by rfl⟩ : syracuseStep 350395 = 525593) B525593
theorem B350471 : Blo 346754 350471 := bstep (se 1 (by rfl) ⟨262853, by rfl⟩ : syracuseStep 350471 = 525707) B525707
theorem B350479 : Blo 346754 350479 := bstep (se 1 (by rfl) ⟨262859, by rfl⟩ : syracuseStep 350479 = 525719) B525719
theorem B350523 : Blo 346754 350523 := bstep (se 1 (by rfl) ⟨262892, by rfl⟩ : syracuseStep 350523 = 525785) B525785
theorem B350599 : Blo 346754 350599 := bstep (se 1 (by rfl) ⟨262949, by rfl⟩ : syracuseStep 350599 = 525899) B525899
theorem B350607 : Blo 346754 350607 := bstep (se 1 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 350607 = 525911) B525911
theorem B350651 : Blo 346754 350651 := bstep (se 1 (by rfl) ⟨262988, by rfl⟩ : syracuseStep 350651 = 525977) B525977
theorem B350727 : Blo 346754 350727 := bstep (se 1 (by rfl) ⟨263045, by rfl⟩ : syracuseStep 350727 = 526091) B526091
theorem B1432075 : Blo 346754 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B350735 : Blo 346754 350735 := bstep (se 1 (by rfl) ⟨263051, by rfl⟩ : syracuseStep 350735 = 526103) B526103
theorem B1759805 : Blo 346754 1759805 := bstep (se 3 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 1759805 = 659927) B659927
theorem B3758669 : Blo 346754 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B940859 : Blo 346754 940859 := bstep (se 1 (by rfl) ⟨705644, by rfl⟩ : syracuseStep 940859 = 1411289) B1411289
theorem B1989805 : Blo 346754 1989805 := bstep (se 3 (by rfl) ⟨373088, by rfl⟩ : syracuseStep 1989805 = 746177) B746177
theorem B908489 : Blo 346754 908489 := bstep (se 2 (by rfl) ⟨340683, by rfl⟩ : syracuseStep 908489 = 681367) B681367
theorem B941345 : Blo 346754 941345 := bstep (se 2 (by rfl) ⟨353004, by rfl⟩ : syracuseStep 941345 = 706009) B706009
theorem B6741427 : Blo 346754 6741427 := bstep (se 1 (by rfl) ⟨5056070, by rfl⟩ : syracuseStep 6741427 = 10112141) B10112141
theorem B3333581 : Blo 346754 3333581 := bstep (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) B1250093
theorem B2711069 : Blo 346754 2711069 := bstep (se 3 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 2711069 = 1016651) B1016651
theorem B1171259 : Blo 346754 1171259 := bstep (se 1 (by rfl) ⟨878444, by rfl⟩ : syracuseStep 1171259 = 1756889) B1756889
theorem B3170137 : Blo 346754 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B941959 : Blo 346754 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B1171745 : Blo 346754 1171745 := bstep (se 2 (by rfl) ⟨439404, by rfl⟩ : syracuseStep 1171745 = 878809) B878809
theorem B1761587 : Blo 346754 1761587 := bstep (se 1 (by rfl) ⟨1321190, by rfl⟩ : syracuseStep 1761587 = 2642381) B2642381
theorem B16114211 : Blo 346754 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B2122307 : Blo 346754 2122307 := bstep (se 1 (by rfl) ⟨1591730, by rfl⟩ : syracuseStep 2122307 = 3183461) B3183461
theorem B1761911 : Blo 346754 1761911 := bstep (se 1 (by rfl) ⟨1321433, by rfl⟩ : syracuseStep 1761911 = 2642867) B2642867
theorem B1008413 : Blo 346754 1008413 := bstep (se 3 (by rfl) ⟨189077, by rfl⟩ : syracuseStep 1008413 = 378155) B378155
theorem B1172339 : Blo 346754 1172339 := bstep (se 1 (by rfl) ⟨879254, by rfl⟩ : syracuseStep 1172339 = 1758509) B1758509
theorem B2647241 : Blo 346754 2647241 := bstep (se 2 (by rfl) ⟨992715, by rfl⟩ : syracuseStep 2647241 = 1985431) B1985431
theorem B1697057 : Blo 346754 1697057 := bstep (se 2 (by rfl) ⟨636396, by rfl⟩ : syracuseStep 1697057 = 1272793) B1272793
theorem B1992221 : Blo 346754 1992221 := bstep (se 3 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 1992221 = 747083) B747083
theorem B1762883 : Blo 346754 1762883 := bstep (se 1 (by rfl) ⟨1322162, by rfl⟩ : syracuseStep 1762883 = 2644325) B2644325
theorem B1763207 : Blo 346754 1763207 := bstep (se 1 (by rfl) ⟨1322405, by rfl⟩ : syracuseStep 1763207 = 2644811) B2644811
theorem B780407 : Blo 346754 780407 := bstep (se 1 (by rfl) ⟨585305, by rfl⟩ : syracuseStep 780407 = 1170611) B1170611
theorem B845959 : Blo 346754 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B780587 : Blo 346754 780587 := bstep (se 1 (by rfl) ⟨585440, by rfl⟩ : syracuseStep 780587 = 1170881) B1170881
theorem B354703 : Blo 346754 354703 := bstep (se 1 (by rfl) ⟨266027, by rfl⟩ : syracuseStep 354703 = 532055) B532055
theorem B748091 : Blo 346754 748091 := bstep (se 1 (by rfl) ⟨561068, by rfl⟩ : syracuseStep 748091 = 1122137) B1122137
theorem B780947 : Blo 346754 780947 := bstep (se 1 (by rfl) ⟨585710, by rfl⟩ : syracuseStep 780947 = 1171421) B1171421
theorem B781001 : Blo 346754 781001 := bstep (se 2 (by rfl) ⟨292875, by rfl⟩ : syracuseStep 781001 = 585751) B585751
theorem B879731 : Blo 346754 879731 := bstep (se 1 (by rfl) ⟨659798, by rfl⟩ : syracuseStep 879731 = 1319597) B1319597
theorem B1010873 : Blo 346754 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B1895681 : Blo 346754 1895681 := bstep (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) B1421761
theorem B781703 : Blo 346754 781703 := bstep (se 1 (by rfl) ⟨586277, by rfl⟩ : syracuseStep 781703 = 1172555) B1172555
theorem B1174931 : Blo 346754 1174931 := bstep (se 1 (by rfl) ⟨881198, by rfl⟩ : syracuseStep 1174931 = 1762397) B1762397
theorem B781883 : Blo 346754 781883 := bstep (se 1 (by rfl) ⟨586412, by rfl⟩ : syracuseStep 781883 = 1172825) B1172825
theorem B880247 : Blo 346754 880247 := bstep (se 1 (by rfl) ⟨660185, by rfl⟩ : syracuseStep 880247 = 1320371) B1320371
theorem B782009 : Blo 346754 782009 := bstep (se 2 (by rfl) ⟨293253, by rfl⟩ : syracuseStep 782009 = 586507) B586507
theorem B585515 : Blo 346754 585515 := bstep (se 1 (by rfl) ⟨439136, by rfl⟩ : syracuseStep 585515 = 878273) B878273
theorem B4321073 : Blo 346754 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B1994705 : Blo 346754 1994705 := bstep (se 2 (by rfl) ⟨748014, by rfl⟩ : syracuseStep 1994705 = 1496029) B1496029
theorem B520199 : Blo 346754 520199 := bstep (se 1 (by rfl) ⟨390149, by rfl⟩ : syracuseStep 520199 = 780299) B780299
theorem B782351 : Blo 346754 782351 := bstep (se 1 (by rfl) ⟨586763, by rfl⟩ : syracuseStep 782351 = 1173527) B1173527
theorem B716833 : Blo 346754 716833 := bstep (se 2 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 716833 = 537625) B537625
theorem B782369 : Blo 346754 782369 := bstep (se 2 (by rfl) ⟨293388, by rfl⟩ : syracuseStep 782369 = 586777) B586777
theorem B520235 : Blo 346754 520235 := bstep (se 1 (by rfl) ⟨390176, by rfl⟩ : syracuseStep 520235 = 780353) B780353
theorem B520265 : Blo 346754 520265 := bstep (se 2 (by rfl) ⟨195099, by rfl⟩ : syracuseStep 520265 = 390199) B390199
theorem B585913 : Blo 346754 585913 := bstep (se 2 (by rfl) ⟨219717, by rfl⟩ : syracuseStep 585913 = 439435) B439435
theorem B520379 : Blo 346754 520379 := bstep (se 1 (by rfl) ⟨390284, by rfl⟩ : syracuseStep 520379 = 780569) B780569
theorem B1503469 : Blo 346754 1503469 := bstep (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) B563801
theorem B520439 : Blo 346754 520439 := bstep (se 1 (by rfl) ⟨390329, by rfl⟩ : syracuseStep 520439 = 780659) B780659
theorem B520463 : Blo 346754 520463 := bstep (se 1 (by rfl) ⟨390347, by rfl⟩ : syracuseStep 520463 = 780695) B780695
theorem B520505 : Blo 346754 520505 := bstep (se 2 (by rfl) ⟨195189, by rfl⟩ : syracuseStep 520505 = 390379) B390379
theorem B782711 : Blo 346754 782711 := bstep (se 1 (by rfl) ⟨587033, by rfl⟩ : syracuseStep 782711 = 1174067) B1174067
theorem B520583 : Blo 346754 520583 := bstep (se 1 (by rfl) ⟨390437, by rfl⟩ : syracuseStep 520583 = 780875) B780875
theorem B520619 : Blo 346754 520619 := bstep (se 1 (by rfl) ⟨390464, by rfl⟩ : syracuseStep 520619 = 780929) B780929
theorem B520649 : Blo 346754 520649 := bstep (se 2 (by rfl) ⟨195243, by rfl⟩ : syracuseStep 520649 = 390487) B390487
theorem B782891 : Blo 346754 782891 := bstep (se 1 (by rfl) ⟨587168, by rfl⟩ : syracuseStep 782891 = 1174337) B1174337
theorem B520763 : Blo 346754 520763 := bstep (se 1 (by rfl) ⟨390572, by rfl⟩ : syracuseStep 520763 = 781145) B781145
theorem B881239 : Blo 346754 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B64713329 : Blo 346754 64713329 := bstep (se 2 (by rfl) ⟨24267498, by rfl⟩ : syracuseStep 64713329 = 48534997) B48534997
theorem B520823 : Blo 346754 520823 := bstep (se 1 (by rfl) ⟨390617, by rfl⟩ : syracuseStep 520823 = 781235) B781235
theorem B520847 : Blo 346754 520847 := bstep (se 1 (by rfl) ⟨390635, by rfl⟩ : syracuseStep 520847 = 781271) B781271
theorem B520889 : Blo 346754 520889 := bstep (se 2 (by rfl) ⟨195333, by rfl⟩ : syracuseStep 520889 = 390667) B390667
theorem B520967 : Blo 346754 520967 := bstep (se 1 (by rfl) ⟨390725, by rfl⟩ : syracuseStep 520967 = 781451) B781451
theorem B1176335 : Blo 346754 1176335 := bstep (se 1 (by rfl) ⟨882251, by rfl⟩ : syracuseStep 1176335 = 1764503) B1764503
theorem B521003 : Blo 346754 521003 := bstep (se 1 (by rfl) ⟨390752, by rfl⟩ : syracuseStep 521003 = 781505) B781505
theorem B521033 : Blo 346754 521033 := bstep (se 2 (by rfl) ⟨195387, by rfl⟩ : syracuseStep 521033 = 390775) B390775
theorem B586615 : Blo 346754 586615 := bstep (se 1 (by rfl) ⟨439961, by rfl⟩ : syracuseStep 586615 = 879923) B879923
theorem B881543 : Blo 346754 881543 := bstep (se 1 (by rfl) ⟨661157, by rfl⟩ : syracuseStep 881543 = 1322315) B1322315
theorem B783251 : Blo 346754 783251 := bstep (se 1 (by rfl) ⟨587438, by rfl⟩ : syracuseStep 783251 = 1174877) B1174877
theorem B521147 : Blo 346754 521147 := bstep (se 1 (by rfl) ⟨390860, by rfl⟩ : syracuseStep 521147 = 781721) B781721
theorem B783305 : Blo 346754 783305 := bstep (se 2 (by rfl) ⟨293739, by rfl⟩ : syracuseStep 783305 = 587479) B587479
theorem B521207 : Blo 346754 521207 := bstep (se 1 (by rfl) ⟨390905, by rfl⟩ : syracuseStep 521207 = 781811) B781811
theorem B881675 : Blo 346754 881675 := bstep (se 1 (by rfl) ⟨661256, by rfl⟩ : syracuseStep 881675 = 1322513) B1322513
theorem B521231 : Blo 346754 521231 := bstep (se 1 (by rfl) ⟨390923, by rfl⟩ : syracuseStep 521231 = 781847) B781847
theorem B1176605 : Blo 346754 1176605 := bstep (se 3 (by rfl) ⟨220613, by rfl⟩ : syracuseStep 1176605 = 441227) B441227
theorem B521273 : Blo 346754 521273 := bstep (se 2 (by rfl) ⟨195477, by rfl⟩ : syracuseStep 521273 = 390955) B390955
theorem B586811 : Blo 346754 586811 := bstep (se 1 (by rfl) ⟨440108, by rfl⟩ : syracuseStep 586811 = 880217) B880217
theorem B8975447 : Blo 346754 8975447 := bstep (se 1 (by rfl) ⟨6731585, by rfl⟩ : syracuseStep 8975447 = 13463171) B13463171
theorem B521351 : Blo 346754 521351 := bstep (se 1 (by rfl) ⟨391013, by rfl⟩ : syracuseStep 521351 = 782027) B782027
theorem B521387 : Blo 346754 521387 := bstep (se 1 (by rfl) ⟨391040, by rfl⟩ : syracuseStep 521387 = 782081) B782081
theorem B1668289 : Blo 346754 1668289 := bstep (se 2 (by rfl) ⟨625608, by rfl⟩ : syracuseStep 1668289 = 1251217) B1251217
theorem B521417 : Blo 346754 521417 := bstep (se 2 (by rfl) ⟨195531, by rfl⟩ : syracuseStep 521417 = 391063) B391063
theorem B390415 : Blo 346754 390415 := bstep (se 1 (by rfl) ⟨292811, by rfl⟩ : syracuseStep 390415 = 585623) B585623
theorem B521531 : Blo 346754 521531 := bstep (se 1 (by rfl) ⟨391148, by rfl⟩ : syracuseStep 521531 = 782297) B782297
theorem B1766771 : Blo 346754 1766771 := bstep (se 1 (by rfl) ⟨1325078, by rfl⟩ : syracuseStep 1766771 = 2650157) B2650157
theorem B521591 : Blo 346754 521591 := bstep (se 1 (by rfl) ⟨391193, by rfl⟩ : syracuseStep 521591 = 782387) B782387
theorem B521615 : Blo 346754 521615 := bstep (se 1 (by rfl) ⟨391211, by rfl⟩ : syracuseStep 521615 = 782423) B782423
theorem B521657 : Blo 346754 521657 := bstep (se 2 (by rfl) ⟨195621, by rfl⟩ : syracuseStep 521657 = 391243) B391243
theorem B587209 : Blo 346754 587209 := bstep (se 2 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 587209 = 440407) B440407
theorem B521735 : Blo 346754 521735 := bstep (se 1 (by rfl) ⟨391301, by rfl⟩ : syracuseStep 521735 = 782603) B782603
theorem B882191 : Blo 346754 882191 := bstep (se 1 (by rfl) ⟨661643, by rfl⟩ : syracuseStep 882191 = 1323287) B1323287
theorem B521771 : Blo 346754 521771 := bstep (se 1 (by rfl) ⟨391328, by rfl⟩ : syracuseStep 521771 = 782657) B782657
theorem B521801 : Blo 346754 521801 := bstep (se 2 (by rfl) ⟨195675, by rfl⟩ : syracuseStep 521801 = 391351) B391351
theorem B784007 : Blo 346754 784007 := bstep (se 1 (by rfl) ⟨588005, by rfl⟩ : syracuseStep 784007 = 1176011) B1176011
theorem B882323 : Blo 346754 882323 := bstep (se 1 (by rfl) ⟨661742, by rfl⟩ : syracuseStep 882323 = 1323485) B1323485
theorem B521915 : Blo 346754 521915 := bstep (se 1 (by rfl) ⟨391436, by rfl⟩ : syracuseStep 521915 = 782873) B782873
theorem B521975 : Blo 346754 521975 := bstep (se 1 (by rfl) ⟨391481, by rfl⟩ : syracuseStep 521975 = 782963) B782963
theorem B390919 : Blo 346754 390919 := bstep (se 1 (by rfl) ⟨293189, by rfl⟩ : syracuseStep 390919 = 586379) B586379
theorem B521999 : Blo 346754 521999 := bstep (se 1 (by rfl) ⟨391499, by rfl⟩ : syracuseStep 521999 = 782999) B782999
theorem B1996595 : Blo 346754 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B522041 : Blo 346754 522041 := bstep (se 2 (by rfl) ⟨195765, by rfl⟩ : syracuseStep 522041 = 391531) B391531
theorem B784187 : Blo 346754 784187 := bstep (se 1 (by rfl) ⟨588140, by rfl⟩ : syracuseStep 784187 = 1176281) B1176281
theorem B3766105 : Blo 346754 3766105 := bstep (se 2 (by rfl) ⟨1412289, by rfl⟩ : syracuseStep 3766105 = 2824579) B2824579
theorem B1767257 : Blo 346754 1767257 := bstep (se 2 (by rfl) ⟨662721, by rfl⟩ : syracuseStep 1767257 = 1325443) B1325443
theorem B522119 : Blo 346754 522119 := bstep (se 1 (by rfl) ⟨391589, by rfl⟩ : syracuseStep 522119 = 783179) B783179
theorem B522155 : Blo 346754 522155 := bstep (se 1 (by rfl) ⟨391616, by rfl⟩ : syracuseStep 522155 = 783233) B783233
theorem B784313 : Blo 346754 784313 := bstep (se 2 (by rfl) ⟨294117, by rfl⟩ : syracuseStep 784313 = 588235) B588235
theorem B391099 : Blo 346754 391099 := bstep (se 1 (by rfl) ⟨293324, by rfl⟩ : syracuseStep 391099 = 586649) B586649
theorem B522185 : Blo 346754 522185 := bstep (se 2 (by rfl) ⟨195819, by rfl⟩ : syracuseStep 522185 = 391639) B391639
theorem B2979787 : Blo 346754 2979787 := bstep (se 1 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 2979787 = 4469681) B4469681
theorem B522299 : Blo 346754 522299 := bstep (se 1 (by rfl) ⟨391724, by rfl⟩ : syracuseStep 522299 = 783449) B783449
theorem B1538135 : Blo 346754 1538135 := bstep (se 1 (by rfl) ⟨1153601, by rfl⟩ : syracuseStep 1538135 = 2307203) B2307203
theorem B522359 : Blo 346754 522359 := bstep (se 1 (by rfl) ⟨391769, by rfl⟩ : syracuseStep 522359 = 783539) B783539
theorem B587911 : Blo 346754 587911 := bstep (se 1 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 587911 = 881867) B881867
theorem B522383 : Blo 346754 522383 := bstep (se 1 (by rfl) ⟨391787, by rfl⟩ : syracuseStep 522383 = 783575) B783575
theorem B522425 : Blo 346754 522425 := bstep (se 2 (by rfl) ⟨195909, by rfl⟩ : syracuseStep 522425 = 391819) B391819
theorem B522503 : Blo 346754 522503 := bstep (se 1 (by rfl) ⟨391877, by rfl⟩ : syracuseStep 522503 = 783755) B783755
theorem B784655 : Blo 346754 784655 := bstep (se 1 (by rfl) ⟨588491, by rfl⟩ : syracuseStep 784655 = 1176983) B1176983
theorem B784673 : Blo 346754 784673 := bstep (se 2 (by rfl) ⟨294252, by rfl⟩ : syracuseStep 784673 = 588505) B588505
theorem B522539 : Blo 346754 522539 := bstep (se 1 (by rfl) ⟨391904, by rfl⟩ : syracuseStep 522539 = 783809) B783809
theorem B10090817 : Blo 346754 10090817 := bstep (se 2 (by rfl) ⟨3784056, by rfl⟩ : syracuseStep 10090817 = 7568113) B7568113
theorem B522569 : Blo 346754 522569 := bstep (se 2 (by rfl) ⟨195963, by rfl⟩ : syracuseStep 522569 = 391927) B391927
theorem B391567 : Blo 346754 391567 := bstep (se 1 (by rfl) ⟨293675, by rfl⟩ : syracuseStep 391567 = 587351) B587351
theorem B1178009 : Blo 346754 1178009 := bstep (se 2 (by rfl) ⟨441753, by rfl⟩ : syracuseStep 1178009 = 883507) B883507
theorem B522683 : Blo 346754 522683 := bstep (se 1 (by rfl) ⟨392012, by rfl⟩ : syracuseStep 522683 = 784025) B784025
theorem B522743 : Blo 346754 522743 := bstep (se 1 (by rfl) ⟨392057, by rfl⟩ : syracuseStep 522743 = 784115) B784115
theorem B522767 : Blo 346754 522767 := bstep (se 1 (by rfl) ⟨392075, by rfl⟩ : syracuseStep 522767 = 784151) B784151
theorem B522809 : Blo 346754 522809 := bstep (se 2 (by rfl) ⟨196053, by rfl⟩ : syracuseStep 522809 = 392107) B392107
theorem B785015 : Blo 346754 785015 := bstep (se 1 (by rfl) ⟨588761, by rfl⟩ : syracuseStep 785015 = 1177523) B1177523
theorem B522887 : Blo 346754 522887 := bstep (se 1 (by rfl) ⟨392165, by rfl⟩ : syracuseStep 522887 = 784331) B784331
theorem B522923 : Blo 346754 522923 := bstep (se 1 (by rfl) ⟨392192, by rfl⟩ : syracuseStep 522923 = 784385) B784385
theorem B522953 : Blo 346754 522953 := bstep (se 2 (by rfl) ⟨196107, by rfl⟩ : syracuseStep 522953 = 392215) B392215
theorem B883457 : Blo 346754 883457 := bstep (se 2 (by rfl) ⟨331296, by rfl⟩ : syracuseStep 883457 = 662593) B662593
theorem B588559 : Blo 346754 588559 := bstep (se 1 (by rfl) ⟨441419, by rfl⟩ : syracuseStep 588559 = 882839) B882839
theorem B785195 : Blo 346754 785195 := bstep (se 1 (by rfl) ⟨588896, by rfl⟩ : syracuseStep 785195 = 1177793) B1177793
theorem B523067 : Blo 346754 523067 := bstep (se 1 (by rfl) ⟨392300, by rfl⟩ : syracuseStep 523067 = 784601) B784601
theorem B523127 : Blo 346754 523127 := bstep (se 1 (by rfl) ⟨392345, by rfl⟩ : syracuseStep 523127 = 784691) B784691
theorem B392071 : Blo 346754 392071 := bstep (se 1 (by rfl) ⟨294053, by rfl⟩ : syracuseStep 392071 = 588107) B588107
theorem B523151 : Blo 346754 523151 := bstep (se 1 (by rfl) ⟨392363, by rfl⟩ : syracuseStep 523151 = 784727) B784727
theorem B523193 : Blo 346754 523193 := bstep (se 2 (by rfl) ⟨196197, by rfl⟩ : syracuseStep 523193 = 392395) B392395
theorem B523271 : Blo 346754 523271 := bstep (se 1 (by rfl) ⟨392453, by rfl⟩ : syracuseStep 523271 = 784907) B784907
theorem B523307 : Blo 346754 523307 := bstep (se 1 (by rfl) ⟨392480, by rfl⟩ : syracuseStep 523307 = 784961) B784961
theorem B392251 : Blo 346754 392251 := bstep (se 1 (by rfl) ⟨294188, by rfl⟩ : syracuseStep 392251 = 588377) B588377
theorem B523337 : Blo 346754 523337 := bstep (se 2 (by rfl) ⟨196251, by rfl⟩ : syracuseStep 523337 = 392503) B392503
theorem B1178711 : Blo 346754 1178711 := bstep (se 1 (by rfl) ⟨884033, by rfl⟩ : syracuseStep 1178711 = 1768067) B1768067
theorem B883831 : Blo 346754 883831 := bstep (se 1 (by rfl) ⟨662873, by rfl⟩ : syracuseStep 883831 = 1325747) B1325747
theorem B785555 : Blo 346754 785555 := bstep (se 1 (by rfl) ⟨589166, by rfl⟩ : syracuseStep 785555 = 1178333) B1178333
theorem B523451 : Blo 346754 523451 := bstep (se 1 (by rfl) ⟨392588, by rfl⟩ : syracuseStep 523451 = 785177) B785177
theorem B785609 : Blo 346754 785609 := bstep (se 2 (by rfl) ⟨294603, by rfl⟩ : syracuseStep 785609 = 589207) B589207
theorem B523511 : Blo 346754 523511 := bstep (se 1 (by rfl) ⟨392633, by rfl⟩ : syracuseStep 523511 = 785267) B785267
theorem B523535 : Blo 346754 523535 := bstep (se 1 (by rfl) ⟨392651, by rfl⟩ : syracuseStep 523535 = 785303) B785303
theorem B589099 : Blo 346754 589099 := bstep (se 1 (by rfl) ⟨441824, by rfl⟩ : syracuseStep 589099 = 883649) B883649
theorem B523577 : Blo 346754 523577 := bstep (se 2 (by rfl) ⟨196341, by rfl⟩ : syracuseStep 523577 = 392683) B392683
theorem B4226363 : Blo 346754 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B523655 : Blo 346754 523655 := bstep (se 1 (by rfl) ⟨392741, by rfl⟩ : syracuseStep 523655 = 785483) B785483
theorem B523691 : Blo 346754 523691 := bstep (se 1 (by rfl) ⟨392768, by rfl⟩ : syracuseStep 523691 = 785537) B785537
theorem B589241 : Blo 346754 589241 := bstep (se 2 (by rfl) ⟨220965, by rfl⟩ : syracuseStep 589241 = 441931) B441931
theorem B523721 : Blo 346754 523721 := bstep (se 2 (by rfl) ⟨196395, by rfl⟩ : syracuseStep 523721 = 392791) B392791
theorem B392719 : Blo 346754 392719 := bstep (se 1 (by rfl) ⟨294539, by rfl⟩ : syracuseStep 392719 = 589079) B589079
theorem B884267 : Blo 346754 884267 := bstep (se 1 (by rfl) ⟨663200, by rfl⟩ : syracuseStep 884267 = 1326401) B1326401
theorem B523835 : Blo 346754 523835 := bstep (se 1 (by rfl) ⟨392876, by rfl⟩ : syracuseStep 523835 = 785753) B785753
theorem B1179197 : Blo 346754 1179197 := bstep (se 3 (by rfl) ⟨221099, by rfl⟩ : syracuseStep 1179197 = 442199) B442199
theorem B523895 : Blo 346754 523895 := bstep (se 1 (by rfl) ⟨392921, by rfl⟩ : syracuseStep 523895 = 785843) B785843
theorem B523919 : Blo 346754 523919 := bstep (se 1 (by rfl) ⟨392939, by rfl⟩ : syracuseStep 523919 = 785879) B785879
theorem B851609 : Blo 346754 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B523961 : Blo 346754 523961 := bstep (se 2 (by rfl) ⟨196485, by rfl⟩ : syracuseStep 523961 = 392971) B392971
theorem B2391781 : Blo 346754 2391781 := bstep (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) B448459
theorem B524039 : Blo 346754 524039 := bstep (se 1 (by rfl) ⟨393029, by rfl⟩ : syracuseStep 524039 = 786059) B786059
theorem B524075 : Blo 346754 524075 := bstep (se 1 (by rfl) ⟨393056, by rfl⟩ : syracuseStep 524075 = 786113) B786113
theorem B524105 : Blo 346754 524105 := bstep (se 2 (by rfl) ⟨196539, by rfl⟩ : syracuseStep 524105 = 393079) B393079
theorem B786311 : Blo 346754 786311 := bstep (se 1 (by rfl) ⟨589733, by rfl⟩ : syracuseStep 786311 = 1179467) B1179467
theorem B1769363 : Blo 346754 1769363 := bstep (se 1 (by rfl) ⟨1327022, by rfl⟩ : syracuseStep 1769363 = 2654045) B2654045
theorem B524219 : Blo 346754 524219 := bstep (se 1 (by rfl) ⟨393164, by rfl⟩ : syracuseStep 524219 = 786329) B786329
theorem B524279 : Blo 346754 524279 := bstep (se 1 (by rfl) ⟨393209, by rfl⟩ : syracuseStep 524279 = 786419) B786419
theorem B524297 : Blo 346754 524297 := bstep (se 2 (by rfl) ⟨196611, by rfl⟩ : syracuseStep 524297 = 393223) B393223
theorem B524327 : Blo 346754 524327 := bstep (se 1 (by rfl) ⟨393245, by rfl⟩ : syracuseStep 524327 = 786491) B786491
theorem B557135 : Blo 346754 557135 := bstep (se 1 (by rfl) ⟨417851, by rfl⟩ : syracuseStep 557135 = 835703) B835703
theorem B393295 : Blo 346754 393295 := bstep (se 1 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 393295 = 589943) B589943
theorem B2523251 : Blo 346754 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B524411 : Blo 346754 524411 := bstep (se 1 (by rfl) ⟨393308, by rfl⟩ : syracuseStep 524411 = 786617) B786617
theorem B1409177 : Blo 346754 1409177 := bstep (se 2 (by rfl) ⟨528441, by rfl⟩ : syracuseStep 1409177 = 1056883) B1056883
theorem B590071 : Blo 346754 590071 := bstep (se 1 (by rfl) ⟨442553, by rfl⟩ : syracuseStep 590071 = 885107) B885107
theorem B524537 : Blo 346754 524537 := bstep (se 2 (by rfl) ⟨196701, by rfl⟩ : syracuseStep 524537 = 393403) B393403
theorem B524639 : Blo 346754 524639 := bstep (se 1 (by rfl) ⟨393479, by rfl⟩ : syracuseStep 524639 = 786959) B786959
theorem B524651 : Blo 346754 524651 := bstep (se 1 (by rfl) ⟨393488, by rfl⟩ : syracuseStep 524651 = 786977) B786977
theorem B557455 : Blo 346754 557455 := bstep (se 1 (by rfl) ⟨418091, by rfl⟩ : syracuseStep 557455 = 836183) B836183
theorem B590267 : Blo 346754 590267 := bstep (se 1 (by rfl) ⟨442700, by rfl⟩ : syracuseStep 590267 = 885401) B885401
theorem B393691 : Blo 346754 393691 := bstep (se 1 (by rfl) ⟨295268, by rfl⟩ : syracuseStep 393691 = 590537) B590537
theorem B1180169 : Blo 346754 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B590375 : Blo 346754 590375 := bstep (se 1 (by rfl) ⟨442781, by rfl⟩ : syracuseStep 590375 = 885563) B885563
theorem B2228795 : Blo 346754 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B524879 : Blo 346754 524879 := bstep (se 1 (by rfl) ⟨393659, by rfl⟩ : syracuseStep 524879 = 787319) B787319
theorem B787067 : Blo 346754 787067 := bstep (se 1 (by rfl) ⟨590300, by rfl⟩ : syracuseStep 787067 = 1180601) B1180601
theorem B524999 : Blo 346754 524999 := bstep (se 1 (by rfl) ⟨393749, by rfl⟩ : syracuseStep 524999 = 787499) B787499
theorem B787193 : Blo 346754 787193 := bstep (se 2 (by rfl) ⟨295197, by rfl⟩ : syracuseStep 787193 = 590395) B590395
theorem B590665 : Blo 346754 590665 := bstep (se 2 (by rfl) ⟨221499, by rfl⟩ : syracuseStep 590665 = 442999) B442999
theorem B525161 : Blo 346754 525161 := bstep (se 2 (by rfl) ⟨196935, by rfl⟩ : syracuseStep 525161 = 393871) B393871
theorem B590699 : Blo 346754 590699 := bstep (se 1 (by rfl) ⟨443024, by rfl⟩ : syracuseStep 590699 = 886049) B886049
theorem B394159 : Blo 346754 394159 := bstep (se 1 (by rfl) ⟨295619, by rfl⟩ : syracuseStep 394159 = 591239) B591239
theorem B1115063 : Blo 346754 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B525239 : Blo 346754 525239 := bstep (se 1 (by rfl) ⟨393929, by rfl⟩ : syracuseStep 525239 = 787859) B787859
theorem B525275 : Blo 346754 525275 := bstep (se 1 (by rfl) ⟨393956, by rfl⟩ : syracuseStep 525275 = 787913) B787913
theorem B1770497 : Blo 346754 1770497 := bstep (se 2 (by rfl) ⟨663936, by rfl⟩ : syracuseStep 1770497 = 1327873) B1327873
theorem B787463 : Blo 346754 787463 := bstep (se 1 (by rfl) ⟨590597, by rfl⟩ : syracuseStep 787463 = 1181195) B1181195
theorem B1672271 : Blo 346754 1672271 := bstep (se 1 (by rfl) ⟨1254203, by rfl⟩ : syracuseStep 1672271 = 2508407) B2508407
theorem B787535 : Blo 346754 787535 := bstep (se 1 (by rfl) ⟨590651, by rfl⟩ : syracuseStep 787535 = 1181303) B1181303
theorem B591097 : Blo 346754 591097 := bstep (se 2 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 591097 = 443323) B443323
theorem B2655503 : Blo 346754 2655503 := bstep (se 1 (by rfl) ⟨1991627, by rfl⟩ : syracuseStep 2655503 = 3983255) B3983255
theorem B394591 : Blo 346754 394591 := bstep (se 1 (by rfl) ⟨295943, by rfl⟩ : syracuseStep 394591 = 591887) B591887
theorem B1181033 : Blo 346754 1181033 := bstep (se 2 (by rfl) ⟨442887, by rfl⟩ : syracuseStep 1181033 = 885775) B885775
theorem B525743 : Blo 346754 525743 := bstep (se 1 (by rfl) ⟨394307, by rfl⟩ : syracuseStep 525743 = 788615) B788615
theorem B787931 : Blo 346754 787931 := bstep (se 1 (by rfl) ⟨590948, by rfl⟩ : syracuseStep 787931 = 1181897) B1181897
theorem B591367 : Blo 346754 591367 := bstep (se 1 (by rfl) ⟨443525, by rfl⟩ : syracuseStep 591367 = 887051) B887051
theorem B525833 : Blo 346754 525833 := bstep (se 2 (by rfl) ⟨197187, by rfl⟩ : syracuseStep 525833 = 394375) B394375
theorem B525863 : Blo 346754 525863 := bstep (se 1 (by rfl) ⟨394397, by rfl⟩ : syracuseStep 525863 = 788795) B788795
theorem B525947 : Blo 346754 525947 := bstep (se 1 (by rfl) ⟨394460, by rfl⟩ : syracuseStep 525947 = 788921) B788921
theorem B4458199 : Blo 346754 4458199 := bstep (se 1 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 4458199 = 6687299) B6687299
theorem B558839 : Blo 346754 558839 := bstep (se 1 (by rfl) ⟨419129, by rfl⟩ : syracuseStep 558839 = 838259) B838259
theorem B526073 : Blo 346754 526073 := bstep (se 2 (by rfl) ⟨197277, by rfl⟩ : syracuseStep 526073 = 394555) B394555
theorem B1771307 : Blo 346754 1771307 := bstep (se 1 (by rfl) ⟨1328480, by rfl⟩ : syracuseStep 1771307 = 2656961) B2656961
theorem B15075233 : Blo 346754 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B788399 : Blo 346754 788399 := bstep (se 1 (by rfl) ⟨591299, by rfl⟩ : syracuseStep 788399 = 1182599) B1182599
theorem B591799 : Blo 346754 591799 := bstep (se 1 (by rfl) ⟨443849, by rfl⟩ : syracuseStep 591799 = 887699) B887699
theorem B1181627 : Blo 346754 1181627 := bstep (se 1 (by rfl) ⟨886220, by rfl⟩ : syracuseStep 1181627 = 1772441) B1772441
theorem B788651 : Blo 346754 788651 := bstep (se 1 (by rfl) ⟨591488, by rfl⟩ : syracuseStep 788651 = 1182977) B1182977
theorem B887183 : Blo 346754 887183 := bstep (se 1 (by rfl) ⟨665387, by rfl⟩ : syracuseStep 887183 = 1330775) B1330775
theorem B789191 : Blo 346754 789191 := bstep (se 1 (by rfl) ⟨591893, by rfl⟩ : syracuseStep 789191 = 1183787) B1183787
theorem B887507 : Blo 346754 887507 := bstep (se 1 (by rfl) ⟨665630, by rfl⟩ : syracuseStep 887507 = 1331261) B1331261
theorem B658363 : Blo 346754 658363 := bstep (se 1 (by rfl) ⟨493772, by rfl⟩ : syracuseStep 658363 = 987545) B987545
theorem B658439 : Blo 346754 658439 := bstep (se 1 (by rfl) ⟨493829, by rfl⟩ : syracuseStep 658439 = 987659) B987659
theorem B626063 : Blo 346754 626063 := bstep (se 1 (by rfl) ⟨469547, by rfl⟩ : syracuseStep 626063 = 939095) B939095
theorem B658849 : Blo 346754 658849 := bstep (se 2 (by rfl) ⟨247068, by rfl⟩ : syracuseStep 658849 = 494137) B494137
theorem B2035109 : Blo 346754 2035109 := bstep (se 4 (by rfl) ⟨190791, by rfl⟩ : syracuseStep 2035109 = 381583) B381583
theorem B2723291 : Blo 346754 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B2231819 : Blo 346754 2231819 := bstep (se 1 (by rfl) ⟨1673864, by rfl⟩ : syracuseStep 2231819 = 3347729) B3347729
theorem B1183355 : Blo 346754 1183355 := bstep (se 1 (by rfl) ⟨887516, by rfl⟩ : syracuseStep 1183355 = 1775033) B1775033
theorem B659191 : Blo 346754 659191 := bstep (se 1 (by rfl) ⟨494393, by rfl⟩ : syracuseStep 659191 = 988787) B988787
theorem B1183517 : Blo 346754 1183517 := bstep (se 3 (by rfl) ⟨221909, by rfl⟩ : syracuseStep 1183517 = 443819) B443819
theorem B1773575 : Blo 346754 1773575 := bstep (se 1 (by rfl) ⟨1330181, by rfl⟩ : syracuseStep 1773575 = 2660363) B2660363
theorem B659495 : Blo 346754 659495 := bstep (se 1 (by rfl) ⟨494621, by rfl⟩ : syracuseStep 659495 = 989243) B989243
theorem B2658419 : Blo 346754 2658419 := bstep (se 1 (by rfl) ⟨1993814, by rfl⟩ : syracuseStep 2658419 = 3987629) B3987629
theorem B2691377 : Blo 346754 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B1774061 : Blo 346754 1774061 := bstep (se 3 (by rfl) ⟨332636, by rfl⟩ : syracuseStep 1774061 = 665273) B665273
theorem B627239 : Blo 346754 627239 := bstep (se 1 (by rfl) ⟨470429, by rfl⟩ : syracuseStep 627239 = 940859) B940859
theorem B1675961 : Blo 346754 1675961 := bstep (se 2 (by rfl) ⟨628485, by rfl⟩ : syracuseStep 1675961 = 1256971) B1256971
theorem B987977 : Blo 346754 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B627563 : Blo 346754 627563 := bstep (se 1 (by rfl) ⟨470672, by rfl⟩ : syracuseStep 627563 = 941345) B941345
theorem B1250167 : Blo 346754 1250167 := bstep (se 1 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 1250167 = 1875251) B1875251
theorem B1807379 : Blo 346754 1807379 := bstep (se 1 (by rfl) ⟨1355534, by rfl⟩ : syracuseStep 1807379 = 2711069) B2711069
theorem B1774871 : Blo 346754 1774871 := bstep (se 1 (by rfl) ⟨1331153, by rfl⟩ : syracuseStep 1774871 = 2662307) B2662307
theorem B2004625 : Blo 346754 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B1414871 : Blo 346754 1414871 := bstep (se 1 (by rfl) ⟨1061153, by rfl⟩ : syracuseStep 1414871 = 2122307) B2122307
theorem B1316681 : Blo 346754 1316681 := bstep (se 2 (by rfl) ⟨493755, by rfl⟩ : syracuseStep 1316681 = 987511) B987511
theorem B661355 : Blo 346754 661355 := bstep (se 1 (by rfl) ⟨496016, by rfl⟩ : syracuseStep 661355 = 992033) B992033
theorem B661583 : Blo 346754 661583 := bstep (se 1 (by rfl) ⟨496187, by rfl⟩ : syracuseStep 661583 = 992375) B992375
theorem B1317181 : Blo 346754 1317181 := bstep (se 3 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 1317181 = 493943) B493943
theorem B662023 : Blo 346754 662023 := bstep (se 1 (by rfl) ⟨496517, by rfl⟩ : syracuseStep 662023 = 993035) B993035
theorem B5970509 : Blo 346754 5970509 := bstep (se 3 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 5970509 = 2238941) B2238941
theorem B3611621 : Blo 346754 3611621 := bstep (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) B677179
theorem B498727 : Blo 346754 498727 := bstep (se 1 (by rfl) ⟨374045, by rfl⟩ : syracuseStep 498727 = 748091) B748091
theorem B663079 : Blo 346754 663079 := bstep (se 1 (by rfl) ⟨497309, by rfl⟩ : syracuseStep 663079 = 994619) B994619
theorem B1253063 : Blo 346754 1253063 := bstep (se 1 (by rfl) ⟨939797, by rfl⟩ : syracuseStep 1253063 = 1879595) B1879595
theorem B5021473 : Blo 346754 5021473 := bstep (se 2 (by rfl) ⟨1883052, by rfl⟩ : syracuseStep 5021473 = 3766105) B3766105
theorem B3973049 : Blo 346754 3973049 := bstep (se 2 (by rfl) ⟨1489893, by rfl⟩ : syracuseStep 3973049 = 2979787) B2979787
theorem B1318913 : Blo 346754 1318913 := bstep (se 2 (by rfl) ⟨494592, by rfl⟩ : syracuseStep 1318913 = 989185) B989185
theorem B1188107 : Blo 346754 1188107 := bstep (se 1 (by rfl) ⟨891080, by rfl⟩ : syracuseStep 1188107 = 1782161) B1782161
theorem B631145 : Blo 346754 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B5055149 : Blo 346754 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B1909433 : Blo 346754 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B1975043 : Blo 346754 1975043 := bstep (se 1 (by rfl) ⟨1481282, by rfl⟩ : syracuseStep 1975043 = 2962565) B2962565
theorem B2237483 : Blo 346754 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B2237507 : Blo 346754 2237507 := bstep (se 1 (by rfl) ⟨1678130, by rfl⟩ : syracuseStep 2237507 = 3356261) B3356261
theorem B1975499 : Blo 346754 1975499 := bstep (se 1 (by rfl) ⟨1481624, by rfl⟩ : syracuseStep 1975499 = 2963249) B2963249
theorem B664787 : Blo 346754 664787 := bstep (se 1 (by rfl) ⟨498590, by rfl⟩ : syracuseStep 664787 = 997181) B997181
theorem B1058039 : Blo 346754 1058039 := bstep (se 1 (by rfl) ⟨793529, by rfl⟩ : syracuseStep 1058039 = 1587059) B1587059
theorem B664939 : Blo 346754 664939 := bstep (se 1 (by rfl) ⟨498704, by rfl⟩ : syracuseStep 664939 = 997409) B997409
theorem B1025423 : Blo 346754 1025423 := bstep (se 1 (by rfl) ⟨769067, by rfl⟩ : syracuseStep 1025423 = 1538135) B1538135
theorem B992807 : Blo 346754 992807 := bstep (se 1 (by rfl) ⟨744605, by rfl⟩ : syracuseStep 992807 = 1489211) B1489211
theorem B6727211 : Blo 346754 6727211 := bstep (se 1 (by rfl) ⟨5045408, by rfl⟩ : syracuseStep 6727211 = 10090817) B10090817
theorem B665167 : Blo 346754 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B1320583 : Blo 346754 1320583 := bstep (se 1 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 1320583 = 1980875) B1980875
theorem B1976183 : Blo 346754 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B8988569 : Blo 346754 8988569 := bstep (se 2 (by rfl) ⟨3370713, by rfl⟩ : syracuseStep 8988569 = 6741427) B6741427
theorem B1320887 : Blo 346754 1320887 := bstep (se 1 (by rfl) ⟨990665, by rfl⟩ : syracuseStep 1320887 = 1981331) B1981331
theorem B2500561 : Blo 346754 2500561 := bstep (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) B1875421
theorem B5023781 : Blo 346754 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B15050933 : Blo 346754 15050933 := bstep (se 5 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 15050933 = 1411025) B1411025
theorem B3189041 : Blo 346754 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B797033 : Blo 346754 797033 := bstep (se 2 (by rfl) ⟨298887, by rfl⟩ : syracuseStep 797033 = 597775) B597775
theorem B469423 : Blo 346754 469423 := bstep (se 1 (by rfl) ⟨352067, by rfl⟩ : syracuseStep 469423 = 704135) B704135
theorem B567739 : Blo 346754 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B3975965 : Blo 346754 3975965 := bstep (se 3 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 3975965 = 1490987) B1490987
theorem B1485641 : Blo 346754 1485641 := bstep (se 2 (by rfl) ⟨557115, by rfl⟩ : syracuseStep 1485641 = 1114231) B1114231
theorem B469855 : Blo 346754 469855 := bstep (se 1 (by rfl) ⟨352391, by rfl⟩ : syracuseStep 469855 = 704783) B704783
theorem B371551 : Blo 346754 371551 := bstep (se 1 (by rfl) ⟨278663, by rfl⟩ : syracuseStep 371551 = 557327) B557327
theorem B3353491 : Blo 346754 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B1322041 : Blo 346754 1322041 := bstep (se 2 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 1322041 = 991531) B991531
theorem B2010359 : Blo 346754 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B1322345 : Blo 346754 1322345 := bstep (se 2 (by rfl) ⟨495879, by rfl⟩ : syracuseStep 1322345 = 991759) B991759
theorem B2502089 : Blo 346754 2502089 := bstep (se 2 (by rfl) ⟨938283, by rfl⟩ : syracuseStep 2502089 = 1876567) B1876567
theorem B1257245 : Blo 346754 1257245 := bstep (se 3 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 1257245 = 471467) B471467
theorem B1748803 : Blo 346754 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B2633633 : Blo 346754 2633633 := bstep (se 2 (by rfl) ⟨987612, by rfl⟩ : syracuseStep 2633633 = 1975225) B1975225
theorem B1421243 : Blo 346754 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B1191937 : Blo 346754 1191937 := bstep (se 2 (by rfl) ⟨446976, by rfl⟩ : syracuseStep 1191937 = 893953) B893953
theorem B372935 : Blo 346754 372935 := bstep (se 1 (by rfl) ⟨279701, by rfl⟩ : syracuseStep 372935 = 559403) B559403
theorem B1585469 : Blo 346754 1585469 := bstep (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) B594551
theorem B799195 : Blo 346754 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B2241917 : Blo 346754 2241917 := bstep (se 3 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 2241917 = 840719) B840719
theorem B1127945 : Blo 346754 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B439931 : Blo 346754 439931 := bstep (se 1 (by rfl) ⟨329948, by rfl⟩ : syracuseStep 439931 = 659897) B659897
theorem B1980125 : Blo 346754 1980125 := bstep (se 3 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 1980125 = 742547) B742547
theorem B472937 : Blo 346754 472937 := bstep (se 2 (by rfl) ⟨177351, by rfl⟩ : syracuseStep 472937 = 354703) B354703
theorem B1619975 : Blo 346754 1619975 := bstep (se 1 (by rfl) ⟨1214981, by rfl⟩ : syracuseStep 1619975 = 2429963) B2429963
theorem B3782713 : Blo 346754 3782713 := bstep (se 2 (by rfl) ⟨1418517, by rfl⟩ : syracuseStep 3782713 = 2837035) B2837035
theorem B6010969 : Blo 346754 6010969 := bstep (se 2 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 6010969 = 4508227) B4508227
theorem B2505779 : Blo 346754 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B1162297 : Blo 346754 1162297 := bstep (se 2 (by rfl) ⟨435861, by rfl⟩ : syracuseStep 1162297 = 871723) B871723
theorem B1326233 : Blo 346754 1326233 := bstep (se 2 (by rfl) ⟨497337, by rfl⟩ : syracuseStep 1326233 = 994675) B994675
theorem B1490167 : Blo 346754 1490167 := bstep (se 1 (by rfl) ⟨1117625, by rfl⟩ : syracuseStep 1490167 = 2235251) B2235251
theorem B605659 : Blo 346754 605659 := bstep (se 1 (by rfl) ⟨454244, by rfl⟩ : syracuseStep 605659 = 908489) B908489
theorem B1326689 : Blo 346754 1326689 := bstep (se 2 (by rfl) ⟨497508, by rfl⟩ : syracuseStep 1326689 = 995017) B995017
theorem B638587 : Blo 346754 638587 := bstep (se 1 (by rfl) ⟨478940, by rfl⟩ : syracuseStep 638587 = 957881) B957881
theorem B10141625 : Blo 346754 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B672275 : Blo 346754 672275 := bstep (se 1 (by rfl) ⟨504206, by rfl⟩ : syracuseStep 672275 = 1008413) B1008413
theorem B1131371 : Blo 346754 1131371 := bstep (se 1 (by rfl) ⟨848528, by rfl⟩ : syracuseStep 1131371 = 1697057) B1697057
theorem B1328147 : Blo 346754 1328147 := bstep (se 1 (by rfl) ⟨996110, by rfl⟩ : syracuseStep 1328147 = 1992221) B1992221
theorem B673915 : Blo 346754 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B2247041 : Blo 346754 2247041 := bstep (se 2 (by rfl) ⟨842640, by rfl⟩ : syracuseStep 2247041 = 1685281) B1685281
theorem B21121493 : Blo 346754 21121493 := bstep (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) B495035
theorem B1329803 : Blo 346754 1329803 := bstep (se 1 (by rfl) ⟨997352, by rfl⟩ : syracuseStep 1329803 = 1994705) B1994705
theorem B346799 : Blo 346754 346799 := bstep (se 1 (by rfl) ⟨260099, by rfl⟩ : syracuseStep 346799 = 520199) B520199
theorem B346823 : Blo 346754 346823 := bstep (se 1 (by rfl) ⟨260117, by rfl⟩ : syracuseStep 346823 = 520235) B520235
theorem B346843 : Blo 346754 346843 := bstep (se 1 (by rfl) ⟨260132, by rfl⟩ : syracuseStep 346843 = 520265) B520265
theorem B346919 : Blo 346754 346919 := bstep (se 1 (by rfl) ⟨260189, by rfl⟩ : syracuseStep 346919 = 520379) B520379
theorem B346959 : Blo 346754 346959 := bstep (se 1 (by rfl) ⟨260219, by rfl⟩ : syracuseStep 346959 = 520439) B520439
theorem B346975 : Blo 346754 346975 := bstep (se 1 (by rfl) ⟨260231, by rfl⟩ : syracuseStep 346975 = 520463) B520463
theorem B347003 : Blo 346754 347003 := bstep (se 1 (by rfl) ⟨260252, by rfl⟩ : syracuseStep 347003 = 520505) B520505
theorem B1756079 : Blo 346754 1756079 := bstep (se 1 (by rfl) ⟨1317059, by rfl⟩ : syracuseStep 1756079 = 2634119) B2634119
theorem B347055 : Blo 346754 347055 := bstep (se 1 (by rfl) ⟨260291, by rfl⟩ : syracuseStep 347055 = 520583) B520583
theorem B347079 : Blo 346754 347079 := bstep (se 1 (by rfl) ⟨260309, by rfl⟩ : syracuseStep 347079 = 520619) B520619
theorem B347099 : Blo 346754 347099 := bstep (se 1 (by rfl) ⟨260324, by rfl⟩ : syracuseStep 347099 = 520649) B520649
theorem B347175 : Blo 346754 347175 := bstep (se 1 (by rfl) ⟨260381, by rfl⟩ : syracuseStep 347175 = 520763) B520763
theorem B43142219 : Blo 346754 43142219 := bstep (se 1 (by rfl) ⟨32356664, by rfl⟩ : syracuseStep 43142219 = 64713329) B64713329
theorem B347215 : Blo 346754 347215 := bstep (se 1 (by rfl) ⟨260411, by rfl⟩ : syracuseStep 347215 = 520823) B520823
theorem B347231 : Blo 346754 347231 := bstep (se 1 (by rfl) ⟨260423, by rfl⟩ : syracuseStep 347231 = 520847) B520847
theorem B347259 : Blo 346754 347259 := bstep (se 1 (by rfl) ⟨260444, by rfl⟩ : syracuseStep 347259 = 520889) B520889
theorem B347311 : Blo 346754 347311 := bstep (se 1 (by rfl) ⟨260483, by rfl⟩ : syracuseStep 347311 = 520967) B520967
theorem B347335 : Blo 346754 347335 := bstep (se 1 (by rfl) ⟨260501, by rfl⟩ : syracuseStep 347335 = 521003) B521003
theorem B347355 : Blo 346754 347355 := bstep (se 1 (by rfl) ⟨260516, by rfl⟩ : syracuseStep 347355 = 521033) B521033
theorem B13716773 : Blo 346754 13716773 := bstep (se 4 (by rfl) ⟨1285947, by rfl⟩ : syracuseStep 13716773 = 2571895) B2571895
theorem B347431 : Blo 346754 347431 := bstep (se 1 (by rfl) ⟨260573, by rfl⟩ : syracuseStep 347431 = 521147) B521147
theorem B347471 : Blo 346754 347471 := bstep (se 1 (by rfl) ⟨260603, by rfl⟩ : syracuseStep 347471 = 521207) B521207
theorem B347487 : Blo 346754 347487 := bstep (se 1 (by rfl) ⟨260615, by rfl⟩ : syracuseStep 347487 = 521231) B521231
theorem B347515 : Blo 346754 347515 := bstep (se 1 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 347515 = 521273) B521273
theorem B5983631 : Blo 346754 5983631 := bstep (se 1 (by rfl) ⟨4487723, by rfl⟩ : syracuseStep 5983631 = 8975447) B8975447
theorem B1985957 : Blo 346754 1985957 := bstep (se 4 (by rfl) ⟨186183, by rfl⟩ : syracuseStep 1985957 = 372367) B372367
theorem B347567 : Blo 346754 347567 := bstep (se 1 (by rfl) ⟨260675, by rfl⟩ : syracuseStep 347567 = 521351) B521351
theorem B347591 : Blo 346754 347591 := bstep (se 1 (by rfl) ⟨260693, by rfl⟩ : syracuseStep 347591 = 521387) B521387
theorem B347611 : Blo 346754 347611 := bstep (se 1 (by rfl) ⟨260708, by rfl⟩ : syracuseStep 347611 = 521417) B521417
theorem B347687 : Blo 346754 347687 := bstep (se 1 (by rfl) ⟨260765, by rfl⟩ : syracuseStep 347687 = 521531) B521531
theorem B347727 : Blo 346754 347727 := bstep (se 1 (by rfl) ⟨260795, by rfl⟩ : syracuseStep 347727 = 521591) B521591
theorem B347743 : Blo 346754 347743 := bstep (se 1 (by rfl) ⟨260807, by rfl⟩ : syracuseStep 347743 = 521615) B521615
theorem B347771 : Blo 346754 347771 := bstep (se 1 (by rfl) ⟨260828, by rfl⟩ : syracuseStep 347771 = 521657) B521657
theorem B347823 : Blo 346754 347823 := bstep (se 1 (by rfl) ⟨260867, by rfl⟩ : syracuseStep 347823 = 521735) B521735
theorem B347847 : Blo 346754 347847 := bstep (se 1 (by rfl) ⟨260885, by rfl⟩ : syracuseStep 347847 = 521771) B521771
theorem B347867 : Blo 346754 347867 := bstep (se 1 (by rfl) ⟨260900, by rfl⟩ : syracuseStep 347867 = 521801) B521801
theorem B8081117 : Blo 346754 8081117 := bstep (se 3 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 8081117 = 3030419) B3030419
theorem B4476653 : Blo 346754 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B347943 : Blo 346754 347943 := bstep (se 1 (by rfl) ⟨260957, by rfl⟩ : syracuseStep 347943 = 521915) B521915
theorem B347983 : Blo 346754 347983 := bstep (se 1 (by rfl) ⟨260987, by rfl⟩ : syracuseStep 347983 = 521975) B521975
theorem B347999 : Blo 346754 347999 := bstep (se 1 (by rfl) ⟨260999, by rfl⟩ : syracuseStep 347999 = 521999) B521999
theorem B1331063 : Blo 346754 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B348027 : Blo 346754 348027 := bstep (se 1 (by rfl) ⟨261020, by rfl⟩ : syracuseStep 348027 = 522041) B522041
theorem B348079 : Blo 346754 348079 := bstep (se 1 (by rfl) ⟨261059, by rfl⟩ : syracuseStep 348079 = 522119) B522119
theorem B348103 : Blo 346754 348103 := bstep (se 1 (by rfl) ⟨261077, by rfl⟩ : syracuseStep 348103 = 522155) B522155
theorem B348123 : Blo 346754 348123 := bstep (se 1 (by rfl) ⟨261092, by rfl⟩ : syracuseStep 348123 = 522185) B522185
theorem B348199 : Blo 346754 348199 := bstep (se 1 (by rfl) ⟨261149, by rfl⟩ : syracuseStep 348199 = 522299) B522299
theorem B348239 : Blo 346754 348239 := bstep (se 1 (by rfl) ⟨261179, by rfl⟩ : syracuseStep 348239 = 522359) B522359
theorem B348255 : Blo 346754 348255 := bstep (se 1 (by rfl) ⟨261191, by rfl⟩ : syracuseStep 348255 = 522383) B522383
theorem B348283 : Blo 346754 348283 := bstep (se 1 (by rfl) ⟨261212, by rfl⟩ : syracuseStep 348283 = 522425) B522425
theorem B348335 : Blo 346754 348335 := bstep (se 1 (by rfl) ⟨261251, by rfl⟩ : syracuseStep 348335 = 522503) B522503
theorem B348359 : Blo 346754 348359 := bstep (se 1 (by rfl) ⟨261269, by rfl⟩ : syracuseStep 348359 = 522539) B522539
theorem B348379 : Blo 346754 348379 := bstep (se 1 (by rfl) ⟨261284, by rfl⟩ : syracuseStep 348379 = 522569) B522569
theorem B348455 : Blo 346754 348455 := bstep (se 1 (by rfl) ⟨261341, by rfl⟩ : syracuseStep 348455 = 522683) B522683
theorem B348495 : Blo 346754 348495 := bstep (se 1 (by rfl) ⟨261371, by rfl⟩ : syracuseStep 348495 = 522743) B522743
theorem B348511 : Blo 346754 348511 := bstep (se 1 (by rfl) ⟨261383, by rfl⟩ : syracuseStep 348511 = 522767) B522767
theorem B348539 : Blo 346754 348539 := bstep (se 1 (by rfl) ⟨261404, by rfl⟩ : syracuseStep 348539 = 522809) B522809
theorem B348591 : Blo 346754 348591 := bstep (se 1 (by rfl) ⟨261443, by rfl⟩ : syracuseStep 348591 = 522887) B522887
theorem B348615 : Blo 346754 348615 := bstep (se 1 (by rfl) ⟨261461, by rfl⟩ : syracuseStep 348615 = 522923) B522923
theorem B348635 : Blo 346754 348635 := bstep (se 1 (by rfl) ⟨261476, by rfl⟩ : syracuseStep 348635 = 522953) B522953
theorem B348711 : Blo 346754 348711 := bstep (se 1 (by rfl) ⟨261533, by rfl⟩ : syracuseStep 348711 = 523067) B523067
theorem B3592763 : Blo 346754 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B348751 : Blo 346754 348751 := bstep (se 1 (by rfl) ⟨261563, by rfl⟩ : syracuseStep 348751 = 523127) B523127
theorem B348767 : Blo 346754 348767 := bstep (se 1 (by rfl) ⟨261575, by rfl⟩ : syracuseStep 348767 = 523151) B523151
theorem B348795 : Blo 346754 348795 := bstep (se 1 (by rfl) ⟨261596, by rfl⟩ : syracuseStep 348795 = 523193) B523193
theorem B348847 : Blo 346754 348847 := bstep (se 1 (by rfl) ⟨261635, by rfl⟩ : syracuseStep 348847 = 523271) B523271
theorem B348871 : Blo 346754 348871 := bstep (se 1 (by rfl) ⟨261653, by rfl⟩ : syracuseStep 348871 = 523307) B523307
theorem B348891 : Blo 346754 348891 := bstep (se 1 (by rfl) ⟨261668, by rfl⟩ : syracuseStep 348891 = 523337) B523337
theorem B348967 : Blo 346754 348967 := bstep (se 1 (by rfl) ⟨261725, by rfl⟩ : syracuseStep 348967 = 523451) B523451
theorem B2839373 : Blo 346754 2839373 := bstep (se 3 (by rfl) ⟨532382, by rfl⟩ : syracuseStep 2839373 = 1064765) B1064765
theorem B349007 : Blo 346754 349007 := bstep (se 1 (by rfl) ⟨261755, by rfl⟩ : syracuseStep 349007 = 523511) B523511
theorem B349023 : Blo 346754 349023 := bstep (se 1 (by rfl) ⟨261767, by rfl⟩ : syracuseStep 349023 = 523535) B523535
theorem B349051 : Blo 346754 349051 := bstep (se 1 (by rfl) ⟨261788, by rfl⟩ : syracuseStep 349051 = 523577) B523577
theorem B349103 : Blo 346754 349103 := bstep (se 1 (by rfl) ⟨261827, by rfl⟩ : syracuseStep 349103 = 523655) B523655
theorem B349127 : Blo 346754 349127 := bstep (se 1 (by rfl) ⟨261845, by rfl⟩ : syracuseStep 349127 = 523691) B523691
theorem B349147 : Blo 346754 349147 := bstep (se 1 (by rfl) ⟨261860, by rfl⟩ : syracuseStep 349147 = 523721) B523721
theorem B349223 : Blo 346754 349223 := bstep (se 1 (by rfl) ⟨261917, by rfl⟩ : syracuseStep 349223 = 523835) B523835
theorem B349263 : Blo 346754 349263 := bstep (se 1 (by rfl) ⟨261947, by rfl⟩ : syracuseStep 349263 = 523895) B523895
theorem B349279 : Blo 346754 349279 := bstep (se 1 (by rfl) ⟨261959, by rfl⟩ : syracuseStep 349279 = 523919) B523919
theorem B349307 : Blo 346754 349307 := bstep (se 1 (by rfl) ⟨261980, by rfl⟩ : syracuseStep 349307 = 523961) B523961
theorem B349359 : Blo 346754 349359 := bstep (se 1 (by rfl) ⟨262019, by rfl⟩ : syracuseStep 349359 = 524039) B524039
theorem B349383 : Blo 346754 349383 := bstep (se 1 (by rfl) ⟨262037, by rfl⟩ : syracuseStep 349383 = 524075) B524075
theorem B349403 : Blo 346754 349403 := bstep (se 1 (by rfl) ⟨262052, by rfl⟩ : syracuseStep 349403 = 524105) B524105
theorem B349479 : Blo 346754 349479 := bstep (se 1 (by rfl) ⟨262109, by rfl⟩ : syracuseStep 349479 = 524219) B524219
theorem B349519 : Blo 346754 349519 := bstep (se 1 (by rfl) ⟨262139, by rfl⟩ : syracuseStep 349519 = 524279) B524279
theorem B349535 : Blo 346754 349535 := bstep (se 1 (by rfl) ⟨262151, by rfl⟩ : syracuseStep 349535 = 524303) B524303
theorem B349563 : Blo 346754 349563 := bstep (se 1 (by rfl) ⟨262172, by rfl⟩ : syracuseStep 349563 = 524345) B524345
theorem B349615 : Blo 346754 349615 := bstep (se 1 (by rfl) ⟨262211, by rfl⟩ : syracuseStep 349615 = 524423) B524423
theorem B349639 : Blo 346754 349639 := bstep (se 1 (by rfl) ⟨262229, by rfl⟩ : syracuseStep 349639 = 524459) B524459
theorem B349659 : Blo 346754 349659 := bstep (se 1 (by rfl) ⟨262244, by rfl⟩ : syracuseStep 349659 = 524489) B524489
theorem B5953013 : Blo 346754 5953013 := bstep (se 5 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 5953013 = 558095) B558095
theorem B3823109 : Blo 346754 3823109 := bstep (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) B716833
theorem B349735 : Blo 346754 349735 := bstep (se 1 (by rfl) ⟨262301, by rfl⟩ : syracuseStep 349735 = 524603) B524603
theorem B710201 : Blo 346754 710201 := bstep (se 2 (by rfl) ⟨266325, by rfl⟩ : syracuseStep 710201 = 532651) B532651
theorem B4773437 : Blo 346754 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B349775 : Blo 346754 349775 := bstep (se 1 (by rfl) ⟨262331, by rfl⟩ : syracuseStep 349775 = 524663) B524663
theorem B349791 : Blo 346754 349791 := bstep (se 1 (by rfl) ⟨262343, by rfl⟩ : syracuseStep 349791 = 524687) B524687
theorem B2676347 : Blo 346754 2676347 := bstep (se 1 (by rfl) ⟨2007260, by rfl⟩ : syracuseStep 2676347 = 4014521) B4014521
theorem B349819 : Blo 346754 349819 := bstep (se 1 (by rfl) ⟨262364, by rfl⟩ : syracuseStep 349819 = 524729) B524729
theorem B349871 : Blo 346754 349871 := bstep (se 1 (by rfl) ⟨262403, by rfl⟩ : syracuseStep 349871 = 524807) B524807
theorem B2512583 : Blo 346754 2512583 := bstep (se 1 (by rfl) ⟨1884437, by rfl⟩ : syracuseStep 2512583 = 3768875) B3768875
theorem B349895 : Blo 346754 349895 := bstep (se 1 (by rfl) ⟨262421, by rfl⟩ : syracuseStep 349895 = 524843) B524843
theorem B349915 : Blo 346754 349915 := bstep (se 1 (by rfl) ⟨262436, by rfl⟩ : syracuseStep 349915 = 524873) B524873
theorem B349991 : Blo 346754 349991 := bstep (se 1 (by rfl) ⟨262493, by rfl⟩ : syracuseStep 349991 = 524987) B524987
theorem B350031 : Blo 346754 350031 := bstep (se 1 (by rfl) ⟨262523, by rfl⟩ : syracuseStep 350031 = 525047) B525047
theorem B350047 : Blo 346754 350047 := bstep (se 1 (by rfl) ⟨262535, by rfl⟩ : syracuseStep 350047 = 525071) B525071
theorem B350075 : Blo 346754 350075 := bstep (se 1 (by rfl) ⟨262556, by rfl⟩ : syracuseStep 350075 = 525113) B525113
theorem B350127 : Blo 346754 350127 := bstep (se 1 (by rfl) ⟨262595, by rfl⟩ : syracuseStep 350127 = 525191) B525191
theorem B1595323 : Blo 346754 1595323 := bstep (se 1 (by rfl) ⟨1196492, by rfl⟩ : syracuseStep 1595323 = 2392985) B2392985
theorem B350151 : Blo 346754 350151 := bstep (se 1 (by rfl) ⟨262613, by rfl⟩ : syracuseStep 350151 = 525227) B525227
theorem B350171 : Blo 346754 350171 := bstep (se 1 (by rfl) ⟨262628, by rfl⟩ : syracuseStep 350171 = 525257) B525257
theorem B36591587 : Blo 346754 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B350247 : Blo 346754 350247 := bstep (se 1 (by rfl) ⟨262685, by rfl⟩ : syracuseStep 350247 = 525371) B525371
theorem B350287 : Blo 346754 350287 := bstep (se 1 (by rfl) ⟨262715, by rfl⟩ : syracuseStep 350287 = 525431) B525431
theorem B350303 : Blo 346754 350303 := bstep (se 1 (by rfl) ⟨262727, by rfl⟩ : syracuseStep 350303 = 525455) B525455
theorem B350331 : Blo 346754 350331 := bstep (se 1 (by rfl) ⟨262748, by rfl⟩ : syracuseStep 350331 = 525497) B525497
theorem B350383 : Blo 346754 350383 := bstep (se 1 (by rfl) ⟨262787, by rfl⟩ : syracuseStep 350383 = 525575) B525575
theorem B350407 : Blo 346754 350407 := bstep (se 1 (by rfl) ⟨262805, by rfl⟩ : syracuseStep 350407 = 525611) B525611
theorem B350427 : Blo 346754 350427 := bstep (se 1 (by rfl) ⟨262820, by rfl⟩ : syracuseStep 350427 = 525641) B525641
theorem B16963829 : Blo 346754 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B350503 : Blo 346754 350503 := bstep (se 1 (by rfl) ⟨262877, by rfl⟩ : syracuseStep 350503 = 525755) B525755
theorem B350543 : Blo 346754 350543 := bstep (se 1 (by rfl) ⟨262907, by rfl⟩ : syracuseStep 350543 = 525815) B525815
theorem B1890647 : Blo 346754 1890647 := bstep (se 1 (by rfl) ⟨1417985, by rfl⟩ : syracuseStep 1890647 = 2835971) B2835971
theorem B350559 : Blo 346754 350559 := bstep (se 1 (by rfl) ⟨262919, by rfl⟩ : syracuseStep 350559 = 525839) B525839
theorem B350587 : Blo 346754 350587 := bstep (se 1 (by rfl) ⟨262940, by rfl⟩ : syracuseStep 350587 = 525881) B525881
theorem B350639 : Blo 346754 350639 := bstep (se 1 (by rfl) ⟨262979, by rfl⟩ : syracuseStep 350639 = 525959) B525959
theorem B350663 : Blo 346754 350663 := bstep (se 1 (by rfl) ⟨262997, by rfl⟩ : syracuseStep 350663 = 525995) B525995
theorem B350683 : Blo 346754 350683 := bstep (se 1 (by rfl) ⟨263012, by rfl⟩ : syracuseStep 350683 = 526025) B526025
theorem B744059 : Blo 346754 744059 := bstep (se 1 (by rfl) ⟨558044, by rfl⟩ : syracuseStep 744059 = 1116089) B1116089
theorem B1989305 : Blo 346754 1989305 := bstep (se 2 (by rfl) ⟨745989, by rfl⟩ : syracuseStep 1989305 = 1491979) B1491979
theorem B7167449 : Blo 346754 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B745289 : Blo 346754 745289 := bstep (se 2 (by rfl) ⟨279483, by rfl⟩ : syracuseStep 745289 = 558967) B558967
theorem B2842553 : Blo 346754 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B1171475 : Blo 346754 1171475 := bstep (se 1 (by rfl) ⟨878606, by rfl⟩ : syracuseStep 1171475 = 1757213) B1757213
theorem B2973773 : Blo 346754 2973773 := bstep (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) B1115165
theorem B1794163 : Blo 346754 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B1335467 : Blo 346754 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B1171799 : Blo 346754 1171799 := bstep (se 1 (by rfl) ⟨878849, by rfl⟩ : syracuseStep 1171799 = 1757699) B1757699
theorem B12312931 : Blo 346754 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B10838947 : Blo 346754 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B6382745 : Blo 346754 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B15262937 : Blo 346754 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B1172879 : Blo 346754 1172879 := bstep (se 1 (by rfl) ⟨879659, by rfl⟩ : syracuseStep 1172879 = 1759319) B1759319
theorem B1173203 : Blo 346754 1173203 := bstep (se 1 (by rfl) ⟨879902, by rfl⟩ : syracuseStep 1173203 = 1759805) B1759805
theorem B747767 : Blo 346754 747767 := bstep (se 1 (by rfl) ⟨560825, by rfl⟩ : syracuseStep 747767 = 1121651) B1121651
theorem B2222387 : Blo 346754 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B879113 : Blo 346754 879113 := bstep (se 2 (by rfl) ⟨329667, by rfl⟩ : syracuseStep 879113 = 659335) B659335
theorem B780839 : Blo 346754 780839 := bstep (se 1 (by rfl) ⟨585629, by rfl⟩ : syracuseStep 780839 = 1171259) B1171259
theorem B781163 : Blo 346754 781163 := bstep (se 1 (by rfl) ⟨585872, by rfl⟩ : syracuseStep 781163 = 1171745) B1171745
theorem B1174391 : Blo 346754 1174391 := bstep (se 1 (by rfl) ⟨880793, by rfl⟩ : syracuseStep 1174391 = 1761587) B1761587
theorem B781217 : Blo 346754 781217 := bstep (se 2 (by rfl) ⟨292956, by rfl⟩ : syracuseStep 781217 = 585913) B585913
theorem B10742807 : Blo 346754 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B1174607 : Blo 346754 1174607 := bstep (se 1 (by rfl) ⟨880955, by rfl⟩ : syracuseStep 1174607 = 1761911) B1761911
theorem B781559 : Blo 346754 781559 := bstep (se 1 (by rfl) ⟨586169, by rfl⟩ : syracuseStep 781559 = 1172339) B1172339
theorem B1174985 : Blo 346754 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B1764827 : Blo 346754 1764827 := bstep (se 1 (by rfl) ⟨1323620, by rfl⟩ : syracuseStep 1764827 = 2647241) B2647241
theorem B880267 : Blo 346754 880267 := bstep (se 1 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 880267 = 1320401) B1320401
theorem B1175255 : Blo 346754 1175255 := bstep (se 1 (by rfl) ⟨881441, by rfl⟩ : syracuseStep 1175255 = 1762883) B1762883
theorem B782153 : Blo 346754 782153 := bstep (se 2 (by rfl) ⟨293307, by rfl⟩ : syracuseStep 782153 = 586615) B586615
theorem B1175471 : Blo 346754 1175471 := bstep (se 1 (by rfl) ⟨881603, by rfl⟩ : syracuseStep 1175471 = 1763207) B1763207
theorem B2387897 : Blo 346754 2387897 := bstep (se 2 (by rfl) ⟨895461, by rfl⟩ : syracuseStep 2387897 = 1790923) B1790923
theorem B880571 : Blo 346754 880571 := bstep (se 1 (by rfl) ⟨660428, by rfl⟩ : syracuseStep 880571 = 1320857) B1320857
theorem B1765313 : Blo 346754 1765313 := bstep (se 2 (by rfl) ⟨661992, by rfl⟩ : syracuseStep 1765313 = 1323985) B1323985
theorem B585785 : Blo 346754 585785 := bstep (se 2 (by rfl) ⟨219669, by rfl⟩ : syracuseStep 585785 = 439339) B439339
theorem B520271 : Blo 346754 520271 := bstep (se 1 (by rfl) ⟨390203, by rfl⟩ : syracuseStep 520271 = 780407) B780407
theorem B520391 : Blo 346754 520391 := bstep (se 1 (by rfl) ⟨390293, by rfl⟩ : syracuseStep 520391 = 780587) B780587
theorem B2224385 : Blo 346754 2224385 := bstep (se 2 (by rfl) ⟨834144, by rfl⟩ : syracuseStep 2224385 = 1668289) B1668289
theorem B520553 : Blo 346754 520553 := bstep (se 2 (by rfl) ⟨195207, by rfl⟩ : syracuseStep 520553 = 390415) B390415
theorem B1995137 : Blo 346754 1995137 := bstep (se 2 (by rfl) ⟨748176, by rfl⟩ : syracuseStep 1995137 = 1496353) B1496353
theorem B520631 : Blo 346754 520631 := bstep (se 1 (by rfl) ⟨390473, by rfl⟩ : syracuseStep 520631 = 780947) B780947
theorem B520667 : Blo 346754 520667 := bstep (se 1 (by rfl) ⟨390500, by rfl⟩ : syracuseStep 520667 = 781001) B781001
theorem B2519561 : Blo 346754 2519561 := bstep (se 2 (by rfl) ⟨944835, by rfl⟩ : syracuseStep 2519561 = 1889671) B1889671
theorem B782945 : Blo 346754 782945 := bstep (se 2 (by rfl) ⟨293604, by rfl⟩ : syracuseStep 782945 = 587209) B587209
theorem B356987 : Blo 346754 356987 := bstep (se 1 (by rfl) ⟨267740, by rfl⟩ : syracuseStep 356987 = 535481) B535481
theorem B881351 : Blo 346754 881351 := bstep (se 1 (by rfl) ⟨661013, by rfl⟩ : syracuseStep 881351 = 1322027) B1322027
theorem B586487 : Blo 346754 586487 := bstep (se 1 (by rfl) ⟨439865, by rfl⟩ : syracuseStep 586487 = 879731) B879731
theorem B881401 : Blo 346754 881401 := bstep (se 2 (by rfl) ⟨330525, by rfl⟩ : syracuseStep 881401 = 661051) B661051
theorem B13202189 : Blo 346754 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B521135 : Blo 346754 521135 := bstep (se 1 (by rfl) ⟨390851, by rfl⟩ : syracuseStep 521135 = 781703) B781703
theorem B783287 : Blo 346754 783287 := bstep (se 1 (by rfl) ⟨587465, by rfl⟩ : syracuseStep 783287 = 1174931) B1174931
theorem B2814977 : Blo 346754 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B521225 : Blo 346754 521225 := bstep (se 2 (by rfl) ⟨195459, by rfl⟩ : syracuseStep 521225 = 390919) B390919
theorem B521255 : Blo 346754 521255 := bstep (se 1 (by rfl) ⟨390941, by rfl⟩ : syracuseStep 521255 = 781883) B781883
theorem B586831 : Blo 346754 586831 := bstep (se 1 (by rfl) ⟨440123, by rfl⟩ : syracuseStep 586831 = 880247) B880247
theorem B947279 : Blo 346754 947279 := bstep (se 1 (by rfl) ⟨710459, by rfl⟩ : syracuseStep 947279 = 1420919) B1420919
theorem B521339 : Blo 346754 521339 := bstep (se 1 (by rfl) ⟨391004, by rfl⟩ : syracuseStep 521339 = 782009) B782009
theorem B390343 : Blo 346754 390343 := bstep (se 1 (by rfl) ⟨292757, by rfl⟩ : syracuseStep 390343 = 585515) B585515
theorem B2880715 : Blo 346754 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B521465 : Blo 346754 521465 := bstep (se 2 (by rfl) ⟨195549, by rfl⟩ : syracuseStep 521465 = 391099) B391099
theorem B587081 : Blo 346754 587081 := bstep (se 2 (by rfl) ⟨220155, by rfl⟩ : syracuseStep 587081 = 440311) B440311
theorem B521567 : Blo 346754 521567 := bstep (se 1 (by rfl) ⟨391175, by rfl⟩ : syracuseStep 521567 = 782351) B782351
theorem B521579 : Blo 346754 521579 := bstep (se 1 (by rfl) ⟨391184, by rfl⟩ : syracuseStep 521579 = 782369) B782369
theorem B882049 : Blo 346754 882049 := bstep (se 2 (by rfl) ⟨330768, by rfl⟩ : syracuseStep 882049 = 661537) B661537
theorem B783881 : Blo 346754 783881 := bstep (se 2 (by rfl) ⟨293955, by rfl⟩ : syracuseStep 783881 = 587911) B587911
theorem B1275425 : Blo 346754 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B521807 : Blo 346754 521807 := bstep (se 1 (by rfl) ⟨391355, by rfl⟩ : syracuseStep 521807 = 782711) B782711
theorem B521927 : Blo 346754 521927 := bstep (se 1 (by rfl) ⟨391445, by rfl⟩ : syracuseStep 521927 = 782891) B782891
theorem B587513 : Blo 346754 587513 := bstep (se 2 (by rfl) ⟨220317, by rfl⟩ : syracuseStep 587513 = 440635) B440635
theorem B784223 : Blo 346754 784223 := bstep (se 1 (by rfl) ⟨588167, by rfl⟩ : syracuseStep 784223 = 1176335) B1176335
theorem B522089 : Blo 346754 522089 := bstep (se 2 (by rfl) ⟨195783, by rfl⟩ : syracuseStep 522089 = 391567) B391567
theorem B587695 : Blo 346754 587695 := bstep (se 1 (by rfl) ⟨440771, by rfl⟩ : syracuseStep 587695 = 881543) B881543
theorem B522167 : Blo 346754 522167 := bstep (se 1 (by rfl) ⟨391625, by rfl⟩ : syracuseStep 522167 = 783251) B783251
theorem B522203 : Blo 346754 522203 := bstep (se 1 (by rfl) ⟨391652, by rfl⟩ : syracuseStep 522203 = 783305) B783305
theorem B587783 : Blo 346754 587783 := bstep (se 1 (by rfl) ⟨440837, by rfl⟩ : syracuseStep 587783 = 881675) B881675
theorem B784403 : Blo 346754 784403 := bstep (se 1 (by rfl) ⟨588302, by rfl⟩ : syracuseStep 784403 = 1176605) B1176605
theorem B391207 : Blo 346754 391207 := bstep (se 1 (by rfl) ⟨293405, by rfl⟩ : syracuseStep 391207 = 586811) B586811
theorem B1767581 : Blo 346754 1767581 := bstep (se 3 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 1767581 = 662843) B662843
theorem B882859 : Blo 346754 882859 := bstep (se 1 (by rfl) ⟨662144, by rfl⟩ : syracuseStep 882859 = 1324289) B1324289
theorem B1177847 : Blo 346754 1177847 := bstep (se 1 (by rfl) ⟨883385, by rfl⟩ : syracuseStep 1177847 = 1766771) B1766771
theorem B588127 : Blo 346754 588127 := bstep (se 1 (by rfl) ⟨441095, by rfl⟩ : syracuseStep 588127 = 882191) B882191
theorem B784745 : Blo 346754 784745 := bstep (se 2 (by rfl) ⟨294279, by rfl⟩ : syracuseStep 784745 = 588559) B588559
theorem B1112449 : Blo 346754 1112449 := bstep (se 2 (by rfl) ⟨417168, by rfl⟩ : syracuseStep 1112449 = 834337) B834337
theorem B1341839 : Blo 346754 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B522671 : Blo 346754 522671 := bstep (se 1 (by rfl) ⟨392003, by rfl⟩ : syracuseStep 522671 = 784007) B784007
theorem B588215 : Blo 346754 588215 := bstep (se 1 (by rfl) ⟨441161, by rfl⟩ : syracuseStep 588215 = 882323) B882323
theorem B883163 : Blo 346754 883163 := bstep (se 1 (by rfl) ⟨662372, by rfl⟩ : syracuseStep 883163 = 1324745) B1324745
theorem B522761 : Blo 346754 522761 := bstep (se 2 (by rfl) ⟨196035, by rfl⟩ : syracuseStep 522761 = 392071) B392071
theorem B522791 : Blo 346754 522791 := bstep (se 1 (by rfl) ⟨392093, by rfl⟩ : syracuseStep 522791 = 784187) B784187
theorem B1178171 : Blo 346754 1178171 := bstep (se 1 (by rfl) ⟨883628, by rfl⟩ : syracuseStep 1178171 = 1767257) B1767257
theorem B522875 : Blo 346754 522875 := bstep (se 1 (by rfl) ⟨392156, by rfl⟩ : syracuseStep 522875 = 784313) B784313
theorem B523001 : Blo 346754 523001 := bstep (se 2 (by rfl) ⟨196125, by rfl⟩ : syracuseStep 523001 = 392251) B392251
theorem B1178441 : Blo 346754 1178441 := bstep (se 2 (by rfl) ⟨441915, by rfl⟩ : syracuseStep 1178441 = 883831) B883831
theorem B523103 : Blo 346754 523103 := bstep (se 1 (by rfl) ⟨392327, by rfl⟩ : syracuseStep 523103 = 784655) B784655
theorem B20380517 : Blo 346754 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B523115 : Blo 346754 523115 := bstep (se 1 (by rfl) ⟨392336, by rfl⟩ : syracuseStep 523115 = 784673) B784673
theorem B2653073 : Blo 346754 2653073 := bstep (se 2 (by rfl) ⟨994902, by rfl⟩ : syracuseStep 2653073 = 1989805) B1989805
theorem B785339 : Blo 346754 785339 := bstep (se 1 (by rfl) ⟨589004, by rfl⟩ : syracuseStep 785339 = 1178009) B1178009
theorem B1276859 : Blo 346754 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B588809 : Blo 346754 588809 := bstep (se 2 (by rfl) ⟨220803, by rfl⟩ : syracuseStep 588809 = 441607) B441607
theorem B785465 : Blo 346754 785465 := bstep (se 2 (by rfl) ⟨294549, by rfl⟩ : syracuseStep 785465 = 589099) B589099
theorem B523343 : Blo 346754 523343 := bstep (se 1 (by rfl) ⟨392507, by rfl⟩ : syracuseStep 523343 = 785015) B785015
theorem B588971 : Blo 346754 588971 := bstep (se 1 (by rfl) ⟨441728, by rfl⟩ : syracuseStep 588971 = 883457) B883457
theorem B523463 : Blo 346754 523463 := bstep (se 1 (by rfl) ⟨392597, by rfl⟩ : syracuseStep 523463 = 785195) B785195
theorem B523625 : Blo 346754 523625 := bstep (se 2 (by rfl) ⟨196359, by rfl⟩ : syracuseStep 523625 = 392719) B392719
theorem B785807 : Blo 346754 785807 := bstep (se 1 (by rfl) ⟨589355, by rfl⟩ : syracuseStep 785807 = 1178711) B1178711
theorem B1768877 : Blo 346754 1768877 := bstep (se 3 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 1768877 = 663329) B663329
theorem B523703 : Blo 346754 523703 := bstep (se 1 (by rfl) ⟨392777, by rfl⟩ : syracuseStep 523703 = 785555) B785555
theorem B523739 : Blo 346754 523739 := bstep (se 1 (by rfl) ⟨392804, by rfl⟩ : syracuseStep 523739 = 785609) B785609
theorem B2817575 : Blo 346754 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B589369 : Blo 346754 589369 := bstep (se 2 (by rfl) ⟨221013, by rfl⟩ : syracuseStep 589369 = 442027) B442027
theorem B392827 : Blo 346754 392827 := bstep (se 1 (by rfl) ⟨294620, by rfl⟩ : syracuseStep 392827 = 589241) B589241
theorem B589511 : Blo 346754 589511 := bstep (se 1 (by rfl) ⟨442133, by rfl⟩ : syracuseStep 589511 = 884267) B884267
theorem B786131 : Blo 346754 786131 := bstep (se 1 (by rfl) ⟨589598, by rfl⟩ : syracuseStep 786131 = 1179197) B1179197
theorem B4226849 : Blo 346754 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B589673 : Blo 346754 589673 := bstep (se 2 (by rfl) ⟨221127, by rfl⟩ : syracuseStep 589673 = 442255) B442255
theorem B884641 : Blo 346754 884641 := bstep (se 2 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 884641 = 663481) B663481
theorem B524207 : Blo 346754 524207 := bstep (se 1 (by rfl) ⟨393155, by rfl⟩ : syracuseStep 524207 = 786311) B786311
theorem B1179575 : Blo 346754 1179575 := bstep (se 1 (by rfl) ⟨884681, by rfl⟩ : syracuseStep 1179575 = 1769363) B1769363
theorem B524393 : Blo 346754 524393 := bstep (se 2 (by rfl) ⟨196647, by rfl⟩ : syracuseStep 524393 = 393295) B393295
theorem B2392217 : Blo 346754 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B393511 : Blo 346754 393511 := bstep (se 1 (by rfl) ⟨295133, by rfl⟩ : syracuseStep 393511 = 590267) B590267
theorem B786761 : Blo 346754 786761 := bstep (se 2 (by rfl) ⟨295035, by rfl⟩ : syracuseStep 786761 = 590071) B590071
theorem B786779 : Blo 346754 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B393583 : Blo 346754 393583 := bstep (se 1 (by rfl) ⟨295187, by rfl⟩ : syracuseStep 393583 = 590375) B590375
theorem B524711 : Blo 346754 524711 := bstep (se 1 (by rfl) ⟨393533, by rfl⟩ : syracuseStep 524711 = 787067) B787067
theorem B16417241 : Blo 346754 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B524795 : Blo 346754 524795 := bstep (se 1 (by rfl) ⟨393596, by rfl⟩ : syracuseStep 524795 = 787193) B787193
theorem B754247 : Blo 346754 754247 := bstep (se 1 (by rfl) ⟨565685, by rfl⟩ : syracuseStep 754247 = 1131371) B1131371
theorem B393799 : Blo 346754 393799 := bstep (se 1 (by rfl) ⟨295349, by rfl⟩ : syracuseStep 393799 = 590699) B590699
theorem B524921 : Blo 346754 524921 := bstep (se 2 (by rfl) ⟨196845, by rfl⟩ : syracuseStep 524921 = 393691) B393691
theorem B1180331 : Blo 346754 1180331 := bstep (se 1 (by rfl) ⟨885248, by rfl⟩ : syracuseStep 1180331 = 1770497) B1770497
theorem B524975 : Blo 346754 524975 := bstep (se 1 (by rfl) ⟨393731, by rfl⟩ : syracuseStep 524975 = 787463) B787463
theorem B885431 : Blo 346754 885431 := bstep (se 1 (by rfl) ⟨664073, by rfl⟩ : syracuseStep 885431 = 1328147) B1328147
theorem B1114847 : Blo 346754 1114847 := bstep (se 1 (by rfl) ⟨836135, by rfl⟩ : syracuseStep 1114847 = 1672271) B1672271
theorem B525023 : Blo 346754 525023 := bstep (se 1 (by rfl) ⟨393767, by rfl⟩ : syracuseStep 525023 = 787535) B787535
theorem B1770335 : Blo 346754 1770335 := bstep (se 1 (by rfl) ⟨1327751, by rfl⟩ : syracuseStep 1770335 = 2655503) B2655503
theorem B787355 : Blo 346754 787355 := bstep (se 1 (by rfl) ⟨590516, by rfl⟩ : syracuseStep 787355 = 1181033) B1181033
theorem B525287 : Blo 346754 525287 := bstep (se 1 (by rfl) ⟨393965, by rfl⟩ : syracuseStep 525287 = 787931) B787931
theorem B787553 : Blo 346754 787553 := bstep (se 2 (by rfl) ⟨295332, by rfl⟩ : syracuseStep 787553 = 590665) B590665
theorem B1180871 : Blo 346754 1180871 := bstep (se 1 (by rfl) ⟨885653, by rfl⟩ : syracuseStep 1180871 = 1771307) B1771307
theorem B14451929 : Blo 346754 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B525545 : Blo 346754 525545 := bstep (se 2 (by rfl) ⟨197079, by rfl⟩ : syracuseStep 525545 = 394159) B394159
theorem B525599 : Blo 346754 525599 := bstep (se 1 (by rfl) ⟨394199, by rfl⟩ : syracuseStep 525599 = 788399) B788399
theorem B787751 : Blo 346754 787751 := bstep (se 1 (by rfl) ⟨590813, by rfl⟩ : syracuseStep 787751 = 1181627) B1181627
theorem B525767 : Blo 346754 525767 := bstep (se 1 (by rfl) ⟨394325, by rfl⟩ : syracuseStep 525767 = 788651) B788651
theorem B591455 : Blo 346754 591455 := bstep (se 1 (by rfl) ⟨443591, by rfl⟩ : syracuseStep 591455 = 887183) B887183
theorem B951965 : Blo 346754 951965 := bstep (se 3 (by rfl) ⟨178493, by rfl⟩ : syracuseStep 951965 = 356987) B356987
theorem B788129 : Blo 346754 788129 := bstep (se 2 (by rfl) ⟨295548, by rfl⟩ : syracuseStep 788129 = 591097) B591097
theorem B886535 : Blo 346754 886535 := bstep (se 1 (by rfl) ⟨664901, by rfl⟩ : syracuseStep 886535 = 1329803) B1329803
theorem B526121 : Blo 346754 526121 := bstep (se 2 (by rfl) ⟨197295, by rfl⟩ : syracuseStep 526121 = 394591) B394591
theorem B526127 : Blo 346754 526127 := bstep (se 1 (by rfl) ⟨394595, by rfl⟩ : syracuseStep 526127 = 789191) B789191
theorem B591671 : Blo 346754 591671 := bstep (se 1 (by rfl) ⟨443753, by rfl⟩ : syracuseStep 591671 = 887507) B887507
theorem B886585 : Blo 346754 886585 := bstep (se 2 (by rfl) ⟨332469, by rfl⟩ : syracuseStep 886585 = 664939) B664939
theorem B788489 : Blo 346754 788489 := bstep (se 2 (by rfl) ⟨295683, by rfl⟩ : syracuseStep 788489 = 591367) B591367
theorem B886889 : Blo 346754 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B9144515 : Blo 346754 9144515 := bstep (se 1 (by rfl) ⟨6858386, by rfl⟩ : syracuseStep 9144515 = 13716773) B13716773
theorem B788903 : Blo 346754 788903 := bstep (se 1 (by rfl) ⟨591677, by rfl⟩ : syracuseStep 788903 = 1183355) B1183355
theorem B2984435 : Blo 346754 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B789011 : Blo 346754 789011 := bstep (se 1 (by rfl) ⟨591758, by rfl⟩ : syracuseStep 789011 = 1183517) B1183517
theorem B789065 : Blo 346754 789065 := bstep (se 2 (by rfl) ⟨295899, by rfl⟩ : syracuseStep 789065 = 591799) B591799
theorem B887375 : Blo 346754 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B1182383 : Blo 346754 1182383 := bstep (se 1 (by rfl) ⟨886787, by rfl⟩ : syracuseStep 1182383 = 1773575) B1773575
theorem B1772279 : Blo 346754 1772279 := bstep (se 1 (by rfl) ⟨1329209, by rfl⟩ : syracuseStep 1772279 = 2658419) B2658419
theorem B1182707 : Blo 346754 1182707 := bstep (se 1 (by rfl) ⟨887030, by rfl⟩ : syracuseStep 1182707 = 1774061) B1774061
theorem B2395175 : Blo 346754 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B1117307 : Blo 346754 1117307 := bstep (se 1 (by rfl) ⟨837980, by rfl⟩ : syracuseStep 1117307 = 1675961) B1675961
theorem B1772765 : Blo 346754 1772765 := bstep (se 3 (by rfl) ⟨332393, by rfl⟩ : syracuseStep 1772765 = 664787) B664787
theorem B625897 : Blo 346754 625897 := bstep (se 2 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 625897 = 469423) B469423
theorem B756985 : Blo 346754 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B1183247 : Blo 346754 1183247 := bstep (se 1 (by rfl) ⟨887435, by rfl⟩ : syracuseStep 1183247 = 1774871) B1774871
theorem B3968675 : Blo 346754 3968675 := bstep (se 1 (by rfl) ⟨2976506, by rfl⟩ : syracuseStep 3968675 = 5953013) B5953013
theorem B3182291 : Blo 346754 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B626473 : Blo 346754 626473 := bstep (se 2 (by rfl) ⟨234927, by rfl⟩ : syracuseStep 626473 = 469855) B469855
theorem B495401 : Blo 346754 495401 := bstep (se 2 (by rfl) ⟨185775, by rfl⟩ : syracuseStep 495401 = 371551) B371551
theorem B1675055 : Blo 346754 1675055 := bstep (se 1 (by rfl) ⟨1256291, by rfl⟩ : syracuseStep 1675055 = 2512583) B2512583
theorem B11309219 : Blo 346754 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B496039 : Blo 346754 496039 := bstep (se 1 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 496039 = 744059) B744059
theorem B2331737 : Blo 346754 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B496859 : Blo 346754 496859 := bstep (se 1 (by rfl) ⟨372644, by rfl⟩ : syracuseStep 496859 = 745289) B745289
theorem B890311 : Blo 346754 890311 := bstep (se 1 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 890311 = 1335467) B1335467
theorem B792071 : Blo 346754 792071 := bstep (se 1 (by rfl) ⟨594053, by rfl⟩ : syracuseStep 792071 = 1188107) B1188107
theorem B2659877 : Blo 346754 2659877 := bstep (se 4 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 2659877 = 498727) B498727
theorem B1316695 : Blo 346754 1316695 := bstep (se 1 (by rfl) ⟨987521, by rfl⟩ : syracuseStep 1316695 = 1975043) B1975043
theorem B1316999 : Blo 346754 1316999 := bstep (se 1 (by rfl) ⟨987749, by rfl⟩ : syracuseStep 1316999 = 1975499) B1975499
theorem B661871 : Blo 346754 661871 := bstep (se 1 (by rfl) ⟨496403, by rfl⟩ : syracuseStep 661871 = 992807) B992807
theorem B1317455 : Blo 346754 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B3349187 : Blo 346754 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B10033955 : Blo 346754 10033955 := bstep (se 1 (by rfl) ⟨7525466, by rfl⟩ : syracuseStep 10033955 = 15050933) B15050933
theorem B498511 : Blo 346754 498511 := bstep (se 1 (by rfl) ⟨373883, by rfl⟩ : syracuseStep 498511 = 747767) B747767
theorem B1481591 : Blo 346754 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B531355 : Blo 346754 531355 := bstep (se 1 (by rfl) ⟨398516, by rfl⟩ : syracuseStep 531355 = 797033) B797033
theorem B3840953 : Blo 346754 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B990427 : Blo 346754 990427 := bstep (se 1 (by rfl) ⟨742820, by rfl⟩ : syracuseStep 990427 = 1485641) B1485641
theorem B1482923 : Blo 346754 1482923 := bstep (se 1 (by rfl) ⟨1112192, by rfl⟩ : syracuseStep 1482923 = 2224385) B2224385
theorem B1056979 : Blo 346754 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B1679707 : Blo 346754 1679707 := bstep (se 1 (by rfl) ⟨1259780, by rfl⟩ : syracuseStep 1679707 = 2519561) B2519561
theorem B1483265 : Blo 346754 1483265 := bstep (se 2 (by rfl) ⟨556224, by rfl⟩ : syracuseStep 1483265 = 1112449) B1112449
theorem B1876651 : Blo 346754 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B631519 : Blo 346754 631519 := bstep (se 1 (by rfl) ⟨473639, by rfl⟩ : syracuseStep 631519 = 947279) B947279
theorem B1320083 : Blo 346754 1320083 := bstep (se 1 (by rfl) ⟨990062, by rfl⟩ : syracuseStep 1320083 = 1980125) B1980125
theorem B1549729 : Blo 346754 1549729 := bstep (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) B1162297
theorem B894559 : Blo 346754 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B1878383 : Blo 346754 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B6695297 : Blo 346754 6695297 := bstep (se 2 (by rfl) ⟨2510736, by rfl⟩ : syracuseStep 6695297 = 5021473) B5021473
theorem B7580141 : Blo 346754 7580141 := bstep (se 3 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 7580141 = 2842553) B2842553
theorem B6761083 : Blo 346754 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B371423 : Blo 346754 371423 := bstep (se 1 (by rfl) ⟨278567, by rfl⟩ : syracuseStep 371423 = 557135) B557135
theorem B6728669 : Blo 346754 6728669 := bstep (se 3 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 6728669 = 2523251) B2523251
theorem B1485863 : Blo 346754 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B994493 : Blo 346754 994493 := bstep (se 3 (by rfl) ⟨186467, by rfl⟩ : syracuseStep 994493 = 372935) B372935
theorem B438959 : Blo 346754 438959 := bstep (se 1 (by rfl) ⟨329219, by rfl⟩ : syracuseStep 438959 = 658439) B658439
theorem B2634605 : Blo 346754 2634605 := bstep (se 3 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 2634605 = 987977) B987977
theorem B1323971 : Blo 346754 1323971 := bstep (se 1 (by rfl) ⟨992978, by rfl⟩ : syracuseStep 1323971 = 1985957) B1985957
theorem B5944265 : Blo 346754 5944265 := bstep (se 2 (by rfl) ⟨2229099, by rfl⟩ : syracuseStep 5944265 = 4458199) B4458199
theorem B1815527 : Blo 346754 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B1487879 : Blo 346754 1487879 := bstep (se 1 (by rfl) ⟨1115909, by rfl⟩ : syracuseStep 1487879 = 2231819) B2231819
theorem B5387411 : Blo 346754 5387411 := bstep (se 1 (by rfl) ⟨4040558, by rfl⟩ : syracuseStep 5387411 = 8081117) B8081117
theorem B439663 : Blo 346754 439663 := bstep (se 1 (by rfl) ⟨329747, by rfl⟩ : syracuseStep 439663 = 659495) B659495
theorem B898553 : Blo 346754 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B473467 : Blo 346754 473467 := bstep (se 1 (by rfl) ⟨355100, by rfl⟩ : syracuseStep 473467 = 710201) B710201
theorem B1784231 : Blo 346754 1784231 := bstep (se 1 (by rfl) ⟨1338173, by rfl⟩ : syracuseStep 1784231 = 2676347) B2676347
theorem B4471321 : Blo 346754 4471321 := bstep (se 2 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 4471321 = 3353491) B3353491
theorem B440903 : Blo 346754 440903 := bstep (se 1 (by rfl) ⟨330677, by rfl⟩ : syracuseStep 440903 = 661355) B661355
theorem B24394391 : Blo 346754 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B441055 : Blo 346754 441055 := bstep (se 1 (by rfl) ⟨330791, by rfl⟩ : syracuseStep 441055 = 661583) B661583
theorem B1260431 : Blo 346754 1260431 := bstep (se 1 (by rfl) ⟨945323, by rfl⟩ : syracuseStep 1260431 = 1890647) B1890647
theorem B3980339 : Blo 346754 3980339 := bstep (se 1 (by rfl) ⟨2985254, by rfl⟩ : syracuseStep 3980339 = 5970509) B5970509
theorem B1326203 : Blo 346754 1326203 := bstep (se 1 (by rfl) ⟨994652, by rfl⟩ : syracuseStep 1326203 = 1989305) B1989305
theorem B1490237 : Blo 346754 1490237 := bstep (se 3 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 1490237 = 558839) B558839
theorem B2407747 : Blo 346754 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B1261165 : Blo 346754 1261165 := bstep (se 3 (by rfl) ⟨236468, by rfl⟩ : syracuseStep 1261165 = 472937) B472937
theorem B835375 : Blo 346754 835375 := bstep (se 1 (by rfl) ⟨626531, by rfl⟩ : syracuseStep 835375 = 1253063) B1253063
theorem B1589249 : Blo 346754 1589249 := bstep (se 2 (by rfl) ⟨595968, by rfl⟩ : syracuseStep 1589249 = 1191937) B1191937
theorem B1982515 : Blo 346754 1982515 := bstep (se 1 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 1982515 = 2973773) B2973773
theorem B1065593 : Blo 346754 1065593 := bstep (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) B799195
theorem B1491655 : Blo 346754 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B1491671 : Blo 346754 1491671 := bstep (se 1 (by rfl) ⟨1118753, by rfl⟩ : syracuseStep 1491671 = 2237507) B2237507
theorem B10175291 : Blo 346754 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B705359 : Blo 346754 705359 := bstep (se 1 (by rfl) ⟨529019, by rfl⟩ : syracuseStep 705359 = 1058039) B1058039
theorem B7161871 : Blo 346754 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B2672833 : Blo 346754 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B838163 : Blo 346754 838163 := bstep (se 1 (by rfl) ⟨628622, by rfl⟩ : syracuseStep 838163 = 1257245) B1257245
theorem B1755755 : Blo 346754 1755755 := bstep (se 1 (by rfl) ⟨1316816, by rfl⟩ : syracuseStep 1755755 = 2633633) B2633633
theorem B1591931 : Blo 346754 1591931 := bstep (se 1 (by rfl) ⟨1193948, by rfl⟩ : syracuseStep 1591931 = 2387897) B2387897
theorem B346847 : Blo 346754 346847 := bstep (se 1 (by rfl) ⟨260135, by rfl⟩ : syracuseStep 346847 = 520271) B520271
theorem B8014625 : Blo 346754 8014625 := bstep (se 2 (by rfl) ⟨3005484, by rfl⟩ : syracuseStep 8014625 = 6010969) B6010969
theorem B346927 : Blo 346754 346927 := bstep (se 1 (by rfl) ⟨260195, by rfl⟩ : syracuseStep 346927 = 520391) B520391
theorem B347035 : Blo 346754 347035 := bstep (se 1 (by rfl) ⟨260276, by rfl⟩ : syracuseStep 347035 = 520553) B520553
theorem B1330091 : Blo 346754 1330091 := bstep (se 1 (by rfl) ⟨997568, by rfl⟩ : syracuseStep 1330091 = 1995137) B1995137
theorem B347087 : Blo 346754 347087 := bstep (se 1 (by rfl) ⟨260315, by rfl⟩ : syracuseStep 347087 = 520631) B520631
theorem B347111 : Blo 346754 347111 := bstep (se 1 (by rfl) ⟨260333, by rfl⟩ : syracuseStep 347111 = 520667) B520667
theorem B1756241 : Blo 346754 1756241 := bstep (se 2 (by rfl) ⟨658590, by rfl⟩ : syracuseStep 1756241 = 1317181) B1317181
theorem B8801459 : Blo 346754 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B347423 : Blo 346754 347423 := bstep (se 1 (by rfl) ⟨260567, by rfl⟩ : syracuseStep 347423 = 521135) B521135
theorem B347483 : Blo 346754 347483 := bstep (se 1 (by rfl) ⟨260612, by rfl⟩ : syracuseStep 347483 = 521225) B521225
theorem B347503 : Blo 346754 347503 := bstep (se 1 (by rfl) ⟨260627, by rfl⟩ : syracuseStep 347503 = 521255) B521255
theorem B347559 : Blo 346754 347559 := bstep (se 1 (by rfl) ⟨260669, by rfl⟩ : syracuseStep 347559 = 521339) B521339
theorem B347643 : Blo 346754 347643 := bstep (se 1 (by rfl) ⟨260732, by rfl⟩ : syracuseStep 347643 = 521465) B521465
theorem B347711 : Blo 346754 347711 := bstep (se 1 (by rfl) ⟨260783, by rfl⟩ : syracuseStep 347711 = 521567) B521567
theorem B347719 : Blo 346754 347719 := bstep (se 1 (by rfl) ⟨260789, by rfl⟩ : syracuseStep 347719 = 521579) B521579
theorem B1494611 : Blo 346754 1494611 := bstep (se 1 (by rfl) ⟨1120958, by rfl⟩ : syracuseStep 1494611 = 2241917) B2241917
theorem B347871 : Blo 346754 347871 := bstep (se 1 (by rfl) ⟨260903, by rfl⟩ : syracuseStep 347871 = 521807) B521807
theorem B5426957 : Blo 346754 5426957 := bstep (se 3 (by rfl) ⟨1017554, by rfl⟩ : syracuseStep 5426957 = 2035109) B2035109
theorem B347951 : Blo 346754 347951 := bstep (se 1 (by rfl) ⟨260963, by rfl⟩ : syracuseStep 347951 = 521927) B521927
theorem B348059 : Blo 346754 348059 := bstep (se 1 (by rfl) ⟨261044, by rfl⟩ : syracuseStep 348059 = 522089) B522089
theorem B348111 : Blo 346754 348111 := bstep (se 1 (by rfl) ⟨261083, by rfl⟩ : syracuseStep 348111 = 522167) B522167
theorem B348135 : Blo 346754 348135 := bstep (se 1 (by rfl) ⟨261101, by rfl⟩ : syracuseStep 348135 = 522203) B522203
theorem B348447 : Blo 346754 348447 := bstep (se 1 (by rfl) ⟨261335, by rfl⟩ : syracuseStep 348447 = 522671) B522671
theorem B1986889 : Blo 346754 1986889 := bstep (se 2 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 1986889 = 1490167) B1490167
theorem B348507 : Blo 346754 348507 := bstep (se 1 (by rfl) ⟨261380, by rfl⟩ : syracuseStep 348507 = 522761) B522761
theorem B348527 : Blo 346754 348527 := bstep (se 1 (by rfl) ⟨261395, by rfl⟩ : syracuseStep 348527 = 522791) B522791
theorem B348583 : Blo 346754 348583 := bstep (se 1 (by rfl) ⟨261437, by rfl⟩ : syracuseStep 348583 = 522875) B522875
theorem B348667 : Blo 346754 348667 := bstep (se 1 (by rfl) ⟨261500, by rfl⟩ : syracuseStep 348667 = 523001) B523001
theorem B348735 : Blo 346754 348735 := bstep (se 1 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 348735 = 523103) B523103
theorem B13587011 : Blo 346754 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B348743 : Blo 346754 348743 := bstep (se 1 (by rfl) ⟨261557, by rfl⟩ : syracuseStep 348743 = 523115) B523115
theorem B807545 : Blo 346754 807545 := bstep (se 2 (by rfl) ⟨302829, by rfl⟩ : syracuseStep 807545 = 605659) B605659
theorem B348895 : Blo 346754 348895 := bstep (se 1 (by rfl) ⟨261671, by rfl⟩ : syracuseStep 348895 = 523343) B523343
theorem B348975 : Blo 346754 348975 := bstep (se 1 (by rfl) ⟨261731, by rfl⟩ : syracuseStep 348975 = 523463) B523463
theorem B349083 : Blo 346754 349083 := bstep (se 1 (by rfl) ⟨261812, by rfl⟩ : syracuseStep 349083 = 523625) B523625
theorem B349135 : Blo 346754 349135 := bstep (se 1 (by rfl) ⟨261851, by rfl⟩ : syracuseStep 349135 = 523703) B523703
theorem B349159 : Blo 346754 349159 := bstep (se 1 (by rfl) ⟨261869, by rfl⟩ : syracuseStep 349159 = 523739) B523739
theorem B349471 : Blo 346754 349471 := bstep (se 1 (by rfl) ⟨262103, by rfl⟩ : syracuseStep 349471 = 524207) B524207
theorem B349531 : Blo 346754 349531 := bstep (se 1 (by rfl) ⟨262148, by rfl⟩ : syracuseStep 349531 = 524297) B524297
theorem B349551 : Blo 346754 349551 := bstep (se 1 (by rfl) ⟨262163, by rfl⟩ : syracuseStep 349551 = 524327) B524327
theorem B349607 : Blo 346754 349607 := bstep (se 1 (by rfl) ⟨262205, by rfl⟩ : syracuseStep 349607 = 524411) B524411
theorem B939451 : Blo 346754 939451 := bstep (se 1 (by rfl) ⟨704588, by rfl⟩ : syracuseStep 939451 = 1409177) B1409177
theorem B349691 : Blo 346754 349691 := bstep (se 1 (by rfl) ⟨262268, by rfl⟩ : syracuseStep 349691 = 524537) B524537
theorem B349759 : Blo 346754 349759 := bstep (se 1 (by rfl) ⟨262319, by rfl⟩ : syracuseStep 349759 = 524639) B524639
theorem B349767 : Blo 346754 349767 := bstep (se 1 (by rfl) ⟨262325, by rfl⟩ : syracuseStep 349767 = 524651) B524651
theorem B448183 : Blo 346754 448183 := bstep (se 1 (by rfl) ⟨336137, by rfl⟩ : syracuseStep 448183 = 672275) B672275
theorem B349919 : Blo 346754 349919 := bstep (se 1 (by rfl) ⟨262439, by rfl⟩ : syracuseStep 349919 = 524879) B524879
theorem B349999 : Blo 346754 349999 := bstep (se 1 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 349999 = 524999) B524999
theorem B743273 : Blo 346754 743273 := bstep (se 2 (by rfl) ⟨278727, by rfl⟩ : syracuseStep 743273 = 557455) B557455
theorem B350107 : Blo 346754 350107 := bstep (se 1 (by rfl) ⟨262580, by rfl⟩ : syracuseStep 350107 = 525161) B525161
theorem B743375 : Blo 346754 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B350159 : Blo 346754 350159 := bstep (se 1 (by rfl) ⟨262619, by rfl⟩ : syracuseStep 350159 = 525239) B525239
theorem B350183 : Blo 346754 350183 := bstep (se 1 (by rfl) ⟨262637, by rfl⟩ : syracuseStep 350183 = 525275) B525275
theorem B350495 : Blo 346754 350495 := bstep (se 1 (by rfl) ⟨262871, by rfl⟩ : syracuseStep 350495 = 525743) B525743
theorem B350555 : Blo 346754 350555 := bstep (se 1 (by rfl) ⟨262916, by rfl⟩ : syracuseStep 350555 = 525833) B525833
theorem B350575 : Blo 346754 350575 := bstep (se 1 (by rfl) ⟨262931, by rfl⟩ : syracuseStep 350575 = 525863) B525863
theorem B350631 : Blo 346754 350631 := bstep (se 1 (by rfl) ⟨262973, by rfl⟩ : syracuseStep 350631 = 525947) B525947
theorem B350715 : Blo 346754 350715 := bstep (se 1 (by rfl) ⟨263036, by rfl⟩ : syracuseStep 350715 = 526073) B526073
theorem B10050155 : Blo 346754 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B1498027 : Blo 346754 1498027 := bstep (se 1 (by rfl) ⟨1123520, by rfl⟩ : syracuseStep 1498027 = 2247041) B2247041
theorem B1170719 : Blo 346754 1170719 := bstep (se 1 (by rfl) ⟨878039, by rfl⟩ : syracuseStep 1170719 = 1756079) B1756079
theorem B28761479 : Blo 346754 28761479 := bstep (se 1 (by rfl) ⟨21571109, by rfl⟩ : syracuseStep 28761479 = 43142219) B43142219
theorem B1760777 : Blo 346754 1760777 := bstep (se 2 (by rfl) ⟨660291, by rfl⟩ : syracuseStep 1760777 = 1320583) B1320583
theorem B3989087 : Blo 346754 3989087 := bstep (se 1 (by rfl) ⟨2991815, by rfl⟩ : syracuseStep 3989087 = 5983631) B5983631
theorem B3334081 : Blo 346754 3334081 := bstep (se 2 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 3334081 = 2500561) B2500561
theorem B1794251 : Blo 346754 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B418159 : Blo 346754 418159 := bstep (se 1 (by rfl) ⟨313619, by rfl⟩ : syracuseStep 418159 = 627239) B627239
theorem B1892915 : Blo 346754 1892915 := bstep (se 1 (by rfl) ⟨1419686, by rfl⟩ : syracuseStep 1892915 = 2839373) B2839373
theorem B418375 : Blo 346754 418375 := bstep (se 1 (by rfl) ⟨313781, by rfl⟩ : syracuseStep 418375 = 627563) B627563
theorem B1204919 : Blo 346754 1204919 := bstep (se 1 (by rfl) ⟨903689, by rfl⟩ : syracuseStep 1204919 = 1807379) B1807379
theorem B2548739 : Blo 346754 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B943247 : Blo 346754 943247 := bstep (se 1 (by rfl) ⟨707435, by rfl⟩ : syracuseStep 943247 = 1414871) B1414871
theorem B877787 : Blo 346754 877787 := bstep (se 1 (by rfl) ⟨658340, by rfl⟩ : syracuseStep 877787 = 1316681) B1316681
theorem B877817 : Blo 346754 877817 := bstep (se 2 (by rfl) ⟨329181, by rfl⟩ : syracuseStep 877817 = 658363) B658363
theorem B3007853 : Blo 346754 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B1762721 : Blo 346754 1762721 := bstep (se 2 (by rfl) ⟨661020, by rfl⟩ : syracuseStep 1762721 = 1322041) B1322041
theorem B1173149 : Blo 346754 1173149 := bstep (se 3 (by rfl) ⟨219965, by rfl⟩ : syracuseStep 1173149 = 439931) B439931
theorem B878465 : Blo 346754 878465 := bstep (se 2 (by rfl) ⟨329424, by rfl⟩ : syracuseStep 878465 = 658849) B658849
theorem B1173689 : Blo 346754 1173689 := bstep (se 2 (by rfl) ⟨440133, by rfl⟩ : syracuseStep 1173689 = 880267) B880267
theorem B4778299 : Blo 346754 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B878921 : Blo 346754 878921 := bstep (se 2 (by rfl) ⟨329595, by rfl⟩ : syracuseStep 878921 = 659191) B659191
theorem B2648699 : Blo 346754 2648699 := bstep (se 1 (by rfl) ⟨1986524, by rfl⟩ : syracuseStep 2648699 = 3973049) B3973049
theorem B879275 : Blo 346754 879275 := bstep (se 1 (by rfl) ⟨659456, by rfl⟩ : syracuseStep 879275 = 1318913) B1318913
theorem B780983 : Blo 346754 780983 := bstep (se 1 (by rfl) ⟨585737, by rfl⟩ : syracuseStep 780983 = 1171475) B1171475
theorem B781199 : Blo 346754 781199 := bstep (se 1 (by rfl) ⟨585899, by rfl⟩ : syracuseStep 781199 = 1171799) B1171799
theorem B420763 : Blo 346754 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B3370099 : Blo 346754 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B1272955 : Blo 346754 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B4255163 : Blo 346754 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B781919 : Blo 346754 781919 := bstep (se 1 (by rfl) ⟨586439, by rfl⟩ : syracuseStep 781919 = 1172879) B1172879
theorem B683615 : Blo 346754 683615 := bstep (se 1 (by rfl) ⟨512711, by rfl⟩ : syracuseStep 683615 = 1025423) B1025423
theorem B1175201 : Blo 346754 1175201 := bstep (se 2 (by rfl) ⟨440700, by rfl⟩ : syracuseStep 1175201 = 881401) B881401
theorem B4484807 : Blo 346754 4484807 := bstep (se 1 (by rfl) ⟨3363605, by rfl⟩ : syracuseStep 4484807 = 6727211) B6727211
theorem B782135 : Blo 346754 782135 := bstep (se 1 (by rfl) ⟨586601, by rfl⟩ : syracuseStep 782135 = 1173203) B1173203
theorem B1666889 : Blo 346754 1666889 := bstep (se 2 (by rfl) ⟨625083, by rfl⟩ : syracuseStep 1666889 = 1250167) B1250167
theorem B56323981 : Blo 346754 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B5992379 : Blo 346754 5992379 := bstep (se 1 (by rfl) ⟨4494284, by rfl⟩ : syracuseStep 5992379 = 8988569) B8988569
theorem B880591 : Blo 346754 880591 := bstep (se 1 (by rfl) ⟨660443, by rfl⟩ : syracuseStep 880591 = 1320887) B1320887
theorem B782441 : Blo 346754 782441 := bstep (se 2 (by rfl) ⟨293415, by rfl⟩ : syracuseStep 782441 = 586831) B586831
theorem B2126027 : Blo 346754 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B520457 : Blo 346754 520457 := bstep (se 2 (by rfl) ⟨195171, by rfl⟩ : syracuseStep 520457 = 390343) B390343
theorem B586075 : Blo 346754 586075 := bstep (se 1 (by rfl) ⟨439556, by rfl⟩ : syracuseStep 586075 = 879113) B879113
theorem B520559 : Blo 346754 520559 := bstep (se 1 (by rfl) ⟨390419, by rfl⟩ : syracuseStep 520559 = 780839) B780839
theorem B1176065 : Blo 346754 1176065 := bstep (se 2 (by rfl) ⟨441024, by rfl⟩ : syracuseStep 1176065 = 882049) B882049
theorem B2650643 : Blo 346754 2650643 := bstep (se 1 (by rfl) ⟨1987982, by rfl⟩ : syracuseStep 2650643 = 3975965) B3975965
theorem B520775 : Blo 346754 520775 := bstep (se 1 (by rfl) ⟨390581, by rfl⟩ : syracuseStep 520775 = 781163) B781163
theorem B782927 : Blo 346754 782927 := bstep (se 1 (by rfl) ⟨587195, by rfl⟩ : syracuseStep 782927 = 1174391) B1174391
theorem B520811 : Blo 346754 520811 := bstep (se 1 (by rfl) ⟨390608, by rfl⟩ : syracuseStep 520811 = 781217) B781217
theorem B783071 : Blo 346754 783071 := bstep (se 1 (by rfl) ⟨587303, by rfl⟩ : syracuseStep 783071 = 1174607) B1174607
theorem B521039 : Blo 346754 521039 := bstep (se 1 (by rfl) ⟨390779, by rfl⟩ : syracuseStep 521039 = 781559) B781559
theorem B1340239 : Blo 346754 1340239 := bstep (se 1 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 1340239 = 2010359) B2010359
theorem B881563 : Blo 346754 881563 := bstep (se 1 (by rfl) ⟨661172, by rfl⟩ : syracuseStep 881563 = 1322345) B1322345
theorem B1668059 : Blo 346754 1668059 := bstep (se 1 (by rfl) ⟨1251044, by rfl⟩ : syracuseStep 1668059 = 2502089) B2502089
theorem B783323 : Blo 346754 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B1176551 : Blo 346754 1176551 := bstep (se 1 (by rfl) ⟨882413, by rfl⟩ : syracuseStep 1176551 = 1764827) B1764827
theorem B783503 : Blo 346754 783503 := bstep (se 1 (by rfl) ⟨587627, by rfl⟩ : syracuseStep 783503 = 1175255) B1175255
theorem B521435 : Blo 346754 521435 := bstep (se 1 (by rfl) ⟨391076, by rfl⟩ : syracuseStep 521435 = 782153) B782153
theorem B783593 : Blo 346754 783593 := bstep (se 2 (by rfl) ⟨293847, by rfl⟩ : syracuseStep 783593 = 587695) B587695
theorem B2127097 : Blo 346754 2127097 := bstep (se 2 (by rfl) ⟨797661, by rfl⟩ : syracuseStep 2127097 = 1595323) B1595323
theorem B783647 : Blo 346754 783647 := bstep (se 1 (by rfl) ⟨587735, by rfl⟩ : syracuseStep 783647 = 1175471) B1175471
theorem B587047 : Blo 346754 587047 := bstep (se 1 (by rfl) ⟨440285, by rfl⟩ : syracuseStep 587047 = 880571) B880571
theorem B947495 : Blo 346754 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B1176875 : Blo 346754 1176875 := bstep (se 1 (by rfl) ⟨882656, by rfl⟩ : syracuseStep 1176875 = 1765313) B1765313
theorem B390523 : Blo 346754 390523 := bstep (se 1 (by rfl) ⟨292892, by rfl⟩ : syracuseStep 390523 = 585785) B585785
theorem B521609 : Blo 346754 521609 := bstep (se 2 (by rfl) ⟨195603, by rfl⟩ : syracuseStep 521609 = 391207) B391207
theorem B5043617 : Blo 346754 5043617 := bstep (se 2 (by rfl) ⟨1891356, by rfl⟩ : syracuseStep 5043617 = 3782713) B3782713
theorem B1177145 : Blo 346754 1177145 := bstep (se 2 (by rfl) ⟨441429, by rfl⟩ : syracuseStep 1177145 = 882859) B882859
theorem B521963 : Blo 346754 521963 := bstep (se 1 (by rfl) ⟨391472, by rfl⟩ : syracuseStep 521963 = 782945) B782945
theorem B784169 : Blo 346754 784169 := bstep (se 2 (by rfl) ⟨294063, by rfl⟩ : syracuseStep 784169 = 588127) B588127
theorem B587567 : Blo 346754 587567 := bstep (se 1 (by rfl) ⟨440675, by rfl⟩ : syracuseStep 587567 = 881351) B881351
theorem B390991 : Blo 346754 390991 := bstep (se 1 (by rfl) ⟨293243, by rfl⟩ : syracuseStep 390991 = 586487) B586487
theorem B522191 : Blo 346754 522191 := bstep (se 1 (by rfl) ⟨391643, by rfl⟩ : syracuseStep 522191 = 783287) B783287
theorem B3405797 : Blo 346754 3405797 := bstep (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) B638587
theorem B882697 : Blo 346754 882697 := bstep (se 2 (by rfl) ⟨331011, by rfl⟩ : syracuseStep 882697 = 662023) B662023
theorem B391387 : Blo 346754 391387 := bstep (se 1 (by rfl) ⟨293540, by rfl⟩ : syracuseStep 391387 = 587081) B587081
theorem B522587 : Blo 346754 522587 := bstep (se 1 (by rfl) ⟨391940, by rfl⟩ : syracuseStep 522587 = 783881) B783881
theorem B850283 : Blo 346754 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B1669501 : Blo 346754 1669501 := bstep (se 3 (by rfl) ⟨313031, by rfl⟩ : syracuseStep 1669501 = 626063) B626063
theorem B391675 : Blo 346754 391675 := bstep (se 1 (by rfl) ⟨293756, by rfl⟩ : syracuseStep 391675 = 587513) B587513
theorem B522815 : Blo 346754 522815 := bstep (se 1 (by rfl) ⟨392111, by rfl⟩ : syracuseStep 522815 = 784223) B784223
theorem B391855 : Blo 346754 391855 := bstep (se 1 (by rfl) ⟨293891, by rfl⟩ : syracuseStep 391855 = 587783) B587783
theorem B1079983 : Blo 346754 1079983 := bstep (se 1 (by rfl) ⟨809987, by rfl⟩ : syracuseStep 1079983 = 1619975) B1619975
theorem B522935 : Blo 346754 522935 := bstep (se 1 (by rfl) ⟨392201, by rfl⟩ : syracuseStep 522935 = 784403) B784403
theorem B1178387 : Blo 346754 1178387 := bstep (se 1 (by rfl) ⟨883790, by rfl⟩ : syracuseStep 1178387 = 1767581) B1767581
theorem B785231 : Blo 346754 785231 := bstep (se 1 (by rfl) ⟨588923, by rfl⟩ : syracuseStep 785231 = 1177847) B1177847
theorem B523163 : Blo 346754 523163 := bstep (se 1 (by rfl) ⟨392372, by rfl⟩ : syracuseStep 523163 = 784745) B784745
theorem B392143 : Blo 346754 392143 := bstep (se 1 (by rfl) ⟨294107, by rfl⟩ : syracuseStep 392143 = 588215) B588215
theorem B588775 : Blo 346754 588775 := bstep (se 1 (by rfl) ⟨441581, by rfl⟩ : syracuseStep 588775 = 883163) B883163
theorem B785447 : Blo 346754 785447 := bstep (se 1 (by rfl) ⟨589085, by rfl⟩ : syracuseStep 785447 = 1178171) B1178171
theorem B785627 : Blo 346754 785627 := bstep (se 1 (by rfl) ⟨589220, by rfl⟩ : syracuseStep 785627 = 1178441) B1178441
theorem B1768715 : Blo 346754 1768715 := bstep (se 1 (by rfl) ⟨1326536, by rfl⟩ : syracuseStep 1768715 = 2653073) B2653073
theorem B523559 : Blo 346754 523559 := bstep (se 1 (by rfl) ⟨392669, by rfl⟩ : syracuseStep 523559 = 785339) B785339
theorem B851239 : Blo 346754 851239 := bstep (se 1 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 851239 = 1276859) B1276859
theorem B392539 : Blo 346754 392539 := bstep (se 1 (by rfl) ⟨294404, by rfl⟩ : syracuseStep 392539 = 588809) B588809
theorem B1670519 : Blo 346754 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B523643 : Blo 346754 523643 := bstep (se 1 (by rfl) ⟨392732, by rfl⟩ : syracuseStep 523643 = 785465) B785465
theorem B884105 : Blo 346754 884105 := bstep (se 2 (by rfl) ⟨331539, by rfl⟩ : syracuseStep 884105 = 663079) B663079
theorem B785825 : Blo 346754 785825 := bstep (se 2 (by rfl) ⟨294684, by rfl⟩ : syracuseStep 785825 = 589369) B589369
theorem B884155 : Blo 346754 884155 := bstep (se 1 (by rfl) ⟨663116, by rfl⟩ : syracuseStep 884155 = 1326233) B1326233
theorem B392647 : Blo 346754 392647 := bstep (se 1 (by rfl) ⟨294485, by rfl⟩ : syracuseStep 392647 = 588971) B588971
theorem B523769 : Blo 346754 523769 := bstep (se 2 (by rfl) ⟨196413, by rfl⟩ : syracuseStep 523769 = 392827) B392827
theorem B523871 : Blo 346754 523871 := bstep (se 1 (by rfl) ⟨392903, by rfl⟩ : syracuseStep 523871 = 785807) B785807
theorem B1179251 : Blo 346754 1179251 := bstep (se 1 (by rfl) ⟨884438, by rfl⟩ : syracuseStep 1179251 = 1768877) B1768877
theorem B884459 : Blo 346754 884459 := bstep (se 1 (by rfl) ⟨663344, by rfl⟩ : syracuseStep 884459 = 1326689) B1326689
theorem B393007 : Blo 346754 393007 := bstep (se 1 (by rfl) ⟨294755, by rfl⟩ : syracuseStep 393007 = 589511) B589511
theorem B524087 : Blo 346754 524087 := bstep (se 1 (by rfl) ⟨393065, by rfl⟩ : syracuseStep 524087 = 786131) B786131
theorem B2817899 : Blo 346754 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B1179521 : Blo 346754 1179521 := bstep (se 2 (by rfl) ⟨442320, by rfl⟩ : syracuseStep 1179521 = 884641) B884641
theorem B393115 : Blo 346754 393115 := bstep (se 1 (by rfl) ⟨294836, by rfl⟩ : syracuseStep 393115 = 589673) B589673
theorem B786383 : Blo 346754 786383 := bstep (se 1 (by rfl) ⟨589787, by rfl⟩ : syracuseStep 786383 = 1179575) B1179575
theorem B524507 : Blo 346754 524507 := bstep (se 1 (by rfl) ⟨393380, by rfl⟩ : syracuseStep 524507 = 786761) B786761
theorem B524519 : Blo 346754 524519 := bstep (se 1 (by rfl) ⟨393389, by rfl⟩ : syracuseStep 524519 = 786779) B786779
theorem B10944827 : Blo 346754 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B524681 : Blo 346754 524681 := bstep (se 2 (by rfl) ⟨196755, by rfl⟩ : syracuseStep 524681 = 393511) B393511
theorem B786887 : Blo 346754 786887 := bstep (se 1 (by rfl) ⟨590165, by rfl⟩ : syracuseStep 786887 = 1180331) B1180331
theorem B590287 : Blo 346754 590287 := bstep (se 1 (by rfl) ⟨442715, by rfl⟩ : syracuseStep 590287 = 885431) B885431
theorem B557545 : Blo 346754 557545 := bstep (se 2 (by rfl) ⟨209079, by rfl⟩ : syracuseStep 557545 = 418159) B418159
theorem B524777 : Blo 346754 524777 := bstep (se 2 (by rfl) ⟨196791, by rfl⟩ : syracuseStep 524777 = 393583) B393583
theorem B6783527 : Blo 346754 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B1180223 : Blo 346754 1180223 := bstep (se 1 (by rfl) ⟨885167, by rfl⟩ : syracuseStep 1180223 = 1770335) B1770335
theorem B524903 : Blo 346754 524903 := bstep (se 1 (by rfl) ⟨393677, by rfl⟩ : syracuseStep 524903 = 787355) B787355
theorem B525035 : Blo 346754 525035 := bstep (se 1 (by rfl) ⟨393776, by rfl⟩ : syracuseStep 525035 = 787553) B787553
theorem B525065 : Blo 346754 525065 := bstep (se 2 (by rfl) ⟨196899, by rfl⟩ : syracuseStep 525065 = 393799) B393799
theorem B787247 : Blo 346754 787247 := bstep (se 1 (by rfl) ⟨590435, by rfl⟩ : syracuseStep 787247 = 1180871) B1180871
theorem B9634619 : Blo 346754 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B525167 : Blo 346754 525167 := bstep (se 1 (by rfl) ⟨393875, by rfl⟩ : syracuseStep 525167 = 787751) B787751
theorem B394303 : Blo 346754 394303 := bstep (se 1 (by rfl) ⟨295727, by rfl⟩ : syracuseStep 394303 = 591455) B591455
theorem B5637221 : Blo 346754 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B525419 : Blo 346754 525419 := bstep (se 1 (by rfl) ⟨394064, by rfl⟩ : syracuseStep 525419 = 788129) B788129
theorem B591023 : Blo 346754 591023 := bstep (se 1 (by rfl) ⟨443267, by rfl⟩ : syracuseStep 591023 = 886535) B886535
theorem B394447 : Blo 346754 394447 := bstep (se 1 (by rfl) ⟨295835, by rfl⟩ : syracuseStep 394447 = 591671) B591671
theorem B525659 : Blo 346754 525659 := bstep (se 1 (by rfl) ⟨394244, by rfl⟩ : syracuseStep 525659 = 788489) B788489
theorem B591259 : Blo 346754 591259 := bstep (se 1 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 591259 = 886889) B886889
theorem B6096343 : Blo 346754 6096343 := bstep (se 1 (by rfl) ⟨4572257, by rfl⟩ : syracuseStep 6096343 = 9144515) B9144515
theorem B525935 : Blo 346754 525935 := bstep (se 1 (by rfl) ⟨394451, by rfl⟩ : syracuseStep 525935 = 788903) B788903
theorem B558775 : Blo 346754 558775 := bstep (se 1 (by rfl) ⟨419081, by rfl⟩ : syracuseStep 558775 = 838163) B838163
theorem B526007 : Blo 346754 526007 := bstep (se 1 (by rfl) ⟨394505, by rfl⟩ : syracuseStep 526007 = 789011) B789011
theorem B526043 : Blo 346754 526043 := bstep (se 1 (by rfl) ⟨394532, by rfl⟩ : syracuseStep 526043 = 789065) B789065
theorem B591583 : Blo 346754 591583 := bstep (se 1 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 591583 = 887375) B887375
theorem B788255 : Blo 346754 788255 := bstep (se 1 (by rfl) ⟨591191, by rfl⟩ : syracuseStep 788255 = 1182383) B1182383
theorem B1181519 : Blo 346754 1181519 := bstep (se 1 (by rfl) ⟨886139, by rfl⟩ : syracuseStep 1181519 = 1772279) B1772279
theorem B5343083 : Blo 346754 5343083 := bstep (se 1 (by rfl) ⟨4007312, by rfl⟩ : syracuseStep 5343083 = 8014625) B8014625
theorem B2066305 : Blo 346754 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B886727 : Blo 346754 886727 := bstep (se 1 (by rfl) ⟨665045, by rfl⟩ : syracuseStep 886727 = 1330091) B1330091
theorem B788471 : Blo 346754 788471 := bstep (se 1 (by rfl) ⟨591353, by rfl⟩ : syracuseStep 788471 = 1182707) B1182707
theorem B5867639 : Blo 346754 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B1181843 : Blo 346754 1181843 := bstep (se 1 (by rfl) ⟨886382, by rfl⟩ : syracuseStep 1181843 = 1772765) B1772765
theorem B788831 : Blo 346754 788831 := bstep (se 1 (by rfl) ⟨591623, by rfl⟩ : syracuseStep 788831 = 1183247) B1183247
theorem B1182113 : Blo 346754 1182113 := bstep (se 2 (by rfl) ⟨443292, by rfl⟩ : syracuseStep 1182113 = 886585) B886585
theorem B1116703 : Blo 346754 1116703 := bstep (se 1 (by rfl) ⟨837527, by rfl⟩ : syracuseStep 1116703 = 1675055) B1675055
theorem B7539479 : Blo 346754 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B2231333 : Blo 346754 2231333 := bstep (se 4 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 2231333 = 418375) B418375
theorem B2526653 : Blo 346754 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B9014777 : Blo 346754 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B528047 : Blo 346754 528047 := bstep (se 1 (by rfl) ⟨396035, by rfl⟩ : syracuseStep 528047 = 792071) B792071
theorem B1773251 : Blo 346754 1773251 := bstep (se 1 (by rfl) ⟨1329938, by rfl⟩ : syracuseStep 1773251 = 2659877) B2659877
theorem B561017 : Blo 346754 561017 := bstep (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) B420763
theorem B495515 : Blo 346754 495515 := bstep (se 1 (by rfl) ⟨371636, by rfl⟩ : syracuseStep 495515 = 743273) B743273
theorem B2396141 : Blo 346754 2396141 := bstep (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) B898553
theorem B4493465 : Blo 346754 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B2232791 : Blo 346754 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B6689303 : Blo 346754 6689303 := bstep (se 1 (by rfl) ⟨5016977, by rfl⟩ : syracuseStep 6689303 = 10033955) B10033955
theorem B987727 : Blo 346754 987727 := bstep (se 1 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 987727 = 1481591) B1481591
theorem B19174319 : Blo 346754 19174319 := bstep (se 1 (by rfl) ⟨14380739, by rfl⟩ : syracuseStep 19174319 = 28761479) B28761479
theorem B2659391 : Blo 346754 2659391 := bstep (se 1 (by rfl) ⟨1994543, by rfl⟩ : syracuseStep 2659391 = 3989087) B3989087
theorem B988615 : Blo 346754 988615 := bstep (se 1 (by rfl) ⟨741461, by rfl⟩ : syracuseStep 988615 = 1482923) B1482923
theorem B988843 : Blo 346754 988843 := bstep (se 1 (by rfl) ⟨741632, by rfl⟩ : syracuseStep 988843 = 1483265) B1483265
theorem B661385 : Blo 346754 661385 := bstep (se 2 (by rfl) ⟨248019, by rfl⟩ : syracuseStep 661385 = 496039) B496039
theorem B628831 : Blo 346754 628831 := bstep (se 1 (by rfl) ⟨471623, by rfl⟩ : syracuseStep 628831 = 943247) B943247
theorem B2005235 : Blo 346754 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B1252255 : Blo 346754 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B4463531 : Blo 346754 4463531 := bstep (se 1 (by rfl) ⟨3347648, by rfl⟩ : syracuseStep 4463531 = 6695297) B6695297
theorem B5053427 : Blo 346754 5053427 := bstep (se 1 (by rfl) ⟨3790070, by rfl⟩ : syracuseStep 5053427 = 7580141) B7580141
theorem B1252601 : Blo 346754 1252601 := bstep (se 2 (by rfl) ⟨469725, by rfl⟩ : syracuseStep 1252601 = 939451) B939451
theorem B990461 : Blo 346754 990461 := bstep (se 3 (by rfl) ⟨185711, by rfl⟩ : syracuseStep 990461 = 371423) B371423
theorem B1187081 : Blo 346754 1187081 := bstep (se 2 (by rfl) ⟨445155, by rfl⟩ : syracuseStep 1187081 = 890311) B890311
theorem B990575 : Blo 346754 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B662995 : Blo 346754 662995 := bstep (se 1 (by rfl) ⟨497246, by rfl⟩ : syracuseStep 662995 = 994493) B994493
theorem B2989871 : Blo 346754 2989871 := bstep (se 1 (by rfl) ⟨2242403, by rfl⟩ : syracuseStep 2989871 = 4484807) B4484807
theorem B1417351 : Blo 346754 1417351 := bstep (se 1 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 1417351 = 2126027) B2126027
theorem B631289 : Blo 346754 631289 := bstep (se 2 (by rfl) ⟨236733, by rfl⟩ : syracuseStep 631289 = 473467) B473467
theorem B991919 : Blo 346754 991919 := bstep (se 1 (by rfl) ⟨743939, by rfl⟩ : syracuseStep 991919 = 1487879) B1487879
theorem B664681 : Blo 346754 664681 := bstep (se 2 (by rfl) ⟨249255, by rfl⟩ : syracuseStep 664681 = 498511) B498511
theorem B2270531 : Blo 346754 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B566855 : Blo 346754 566855 := bstep (se 1 (by rfl) ⟨425141, by rfl⟩ : syracuseStep 566855 = 850283) B850283
theorem B1189487 : Blo 346754 1189487 := bstep (se 1 (by rfl) ⟨892115, by rfl⟩ : syracuseStep 1189487 = 1784231) B1784231
theorem B1320569 : Blo 346754 1320569 := bstep (se 2 (by rfl) ⟨495213, by rfl⟩ : syracuseStep 1320569 = 990427) B990427
theorem B16262927 : Blo 346754 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B300394565 : Blo 346754 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B1321069 : Blo 346754 1321069 := bstep (se 3 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 1321069 = 495401) B495401
theorem B1681553 : Blo 346754 1681553 := bstep (se 2 (by rfl) ⟨630582, by rfl⟩ : syracuseStep 1681553 = 1261165) B1261165
theorem B993491 : Blo 346754 993491 := bstep (se 1 (by rfl) ⟨745118, by rfl⟩ : syracuseStep 993491 = 1490237) B1490237
theorem B1878599 : Blo 346754 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B1059499 : Blo 346754 1059499 := bstep (se 1 (by rfl) ⟨794624, by rfl⟩ : syracuseStep 1059499 = 1589249) B1589249
theorem B502831 : Blo 346754 502831 := bstep (se 1 (by rfl) ⟨377123, by rfl⟩ : syracuseStep 502831 = 754247) B754247
theorem B2239609 : Blo 346754 2239609 := bstep (se 2 (by rfl) ⟨839853, by rfl⟩ : syracuseStep 2239609 = 1679707) B1679707
theorem B994447 : Blo 346754 994447 := bstep (se 1 (by rfl) ⟨745835, by rfl⟩ : syracuseStep 994447 = 1491671) B1491671
theorem B634643 : Blo 346754 634643 := bstep (se 1 (by rfl) ⟨475982, by rfl⟩ : syracuseStep 634643 = 951965) B951965
theorem B1192745 : Blo 346754 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B1880957 : Blo 346754 1880957 := bstep (se 3 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 1880957 = 705359) B705359
theorem B996407 : Blo 346754 996407 := bstep (se 1 (by rfl) ⟨747305, by rfl⟩ : syracuseStep 996407 = 1494611) B1494611
theorem B9549161 : Blo 346754 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B9058007 : Blo 346754 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B6371065 : Blo 346754 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B1324957 : Blo 346754 1324957 := bstep (se 3 (by rfl) ⟨248429, by rfl⟩ : syracuseStep 1324957 = 496859) B496859
theorem B1554491 : Blo 346754 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B10008805 : Blo 346754 10008805 := bstep (se 4 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 10008805 = 1876651) B1876651
theorem B834529 : Blo 346754 834529 := bstep (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) B625897
theorem B6700103 : Blo 346754 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B1982333 : Blo 346754 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B1196167 : Blo 346754 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B1261943 : Blo 346754 1261943 := bstep (se 1 (by rfl) ⟨946457, by rfl⟩ : syracuseStep 1261943 = 1892915) B1892915
theorem B803279 : Blo 346754 803279 := bstep (se 1 (by rfl) ⟨602459, by rfl⟩ : syracuseStep 803279 = 1204919) B1204919
theorem B1786985 : Blo 346754 1786985 := bstep (se 2 (by rfl) ⟨670119, by rfl⟩ : syracuseStep 1786985 = 1340239) B1340239
theorem B4245149 : Blo 346754 4245149 := bstep (se 3 (by rfl) ⟨795965, by rfl⟩ : syracuseStep 4245149 = 1591931) B1591931
theorem B2836129 : Blo 346754 2836129 := bstep (se 2 (by rfl) ⟨1063548, by rfl⟩ : syracuseStep 2836129 = 2127097) B2127097
theorem B2836775 : Blo 346754 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B1755593 : Blo 346754 1755593 := bstep (se 2 (by rfl) ⟨658347, by rfl⟩ : syracuseStep 1755593 = 1316695) B1316695
theorem B10242541 : Blo 346754 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B346971 : Blo 346754 346971 := bstep (se 1 (by rfl) ⟨260228, by rfl⟩ : syracuseStep 346971 = 520457) B520457
theorem B347039 : Blo 346754 347039 := bstep (se 1 (by rfl) ⟨260279, by rfl⟩ : syracuseStep 347039 = 520559) B520559
theorem B347183 : Blo 346754 347183 := bstep (se 1 (by rfl) ⟨260387, by rfl⟩ : syracuseStep 347183 = 520775) B520775
theorem B347207 : Blo 346754 347207 := bstep (se 1 (by rfl) ⟨260405, by rfl⟩ : syracuseStep 347207 = 520811) B520811
theorem B347359 : Blo 346754 347359 := bstep (se 1 (by rfl) ⟨260519, by rfl⟩ : syracuseStep 347359 = 521039) B521039
theorem B1756403 : Blo 346754 1756403 := bstep (se 1 (by rfl) ⟨1317302, by rfl⟩ : syracuseStep 1756403 = 2634605) B2634605
theorem B3591607 : Blo 346754 3591607 := bstep (se 1 (by rfl) ⟨2693705, by rfl⟩ : syracuseStep 3591607 = 5387411) B5387411
theorem B347623 : Blo 346754 347623 := bstep (se 1 (by rfl) ⟨260717, by rfl⟩ : syracuseStep 347623 = 521435) B521435
theorem B347739 : Blo 346754 347739 := bstep (se 1 (by rfl) ⟨260804, by rfl⟩ : syracuseStep 347739 = 521609) B521609
theorem B3362411 : Blo 346754 3362411 := bstep (se 1 (by rfl) ⟨2521808, by rfl⟩ : syracuseStep 3362411 = 5043617) B5043617
theorem B347975 : Blo 346754 347975 := bstep (se 1 (by rfl) ⟨260981, by rfl⟩ : syracuseStep 347975 = 521963) B521963
theorem B708473 : Blo 346754 708473 := bstep (se 2 (by rfl) ⟨265677, by rfl⟩ : syracuseStep 708473 = 531355) B531355
theorem B348127 : Blo 346754 348127 := bstep (se 1 (by rfl) ⟨261095, by rfl⟩ : syracuseStep 348127 = 522191) B522191
theorem B348391 : Blo 346754 348391 := bstep (se 1 (by rfl) ⟨261293, by rfl⟩ : syracuseStep 348391 = 522587) B522587
theorem B348543 : Blo 346754 348543 := bstep (se 1 (by rfl) ⟨261407, by rfl⟩ : syracuseStep 348543 = 522815) B522815
theorem B1134985 : Blo 346754 1134985 := bstep (se 2 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 1134985 = 851239) B851239
theorem B348623 : Blo 346754 348623 := bstep (se 1 (by rfl) ⟨261467, by rfl⟩ : syracuseStep 348623 = 522935) B522935
theorem B840287 : Blo 346754 840287 := bstep (se 1 (by rfl) ⟨630215, by rfl⟩ : syracuseStep 840287 = 1260431) B1260431
theorem B348775 : Blo 346754 348775 := bstep (se 1 (by rfl) ⟨261581, by rfl⟩ : syracuseStep 348775 = 523163) B523163
theorem B14471885 : Blo 346754 14471885 := bstep (se 3 (by rfl) ⟨2713478, by rfl⟩ : syracuseStep 14471885 = 5426957) B5426957
theorem B349039 : Blo 346754 349039 := bstep (se 1 (by rfl) ⟨261779, by rfl⟩ : syracuseStep 349039 = 523559) B523559
theorem B349095 : Blo 346754 349095 := bstep (se 1 (by rfl) ⟨261821, by rfl⟩ : syracuseStep 349095 = 523643) B523643
theorem B349179 : Blo 346754 349179 := bstep (se 1 (by rfl) ⟨261884, by rfl⟩ : syracuseStep 349179 = 523769) B523769
theorem B349247 : Blo 346754 349247 := bstep (se 1 (by rfl) ⟨261935, by rfl⟩ : syracuseStep 349247 = 523871) B523871
theorem B349391 : Blo 346754 349391 := bstep (se 1 (by rfl) ⟨262043, by rfl⟩ : syracuseStep 349391 = 524087) B524087
theorem B4445441 : Blo 346754 4445441 := bstep (se 2 (by rfl) ⟨1667040, by rfl⟩ : syracuseStep 4445441 = 3334081) B3334081
theorem B2643353 : Blo 346754 2643353 := bstep (se 2 (by rfl) ⟨991257, by rfl⟩ : syracuseStep 2643353 = 1982515) B1982515
theorem B349595 : Blo 346754 349595 := bstep (se 1 (by rfl) ⟨262196, by rfl⟩ : syracuseStep 349595 = 524393) B524393
theorem B1594811 : Blo 346754 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B349807 : Blo 346754 349807 := bstep (se 1 (by rfl) ⟨262355, by rfl⟩ : syracuseStep 349807 = 524711) B524711
theorem B349863 : Blo 346754 349863 := bstep (se 1 (by rfl) ⟨262397, by rfl⟩ : syracuseStep 349863 = 524795) B524795
theorem B349947 : Blo 346754 349947 := bstep (se 1 (by rfl) ⟨262460, by rfl⟩ : syracuseStep 349947 = 524921) B524921
theorem B349983 : Blo 346754 349983 := bstep (se 1 (by rfl) ⟨262487, by rfl⟩ : syracuseStep 349983 = 524975) B524975
theorem B743231 : Blo 346754 743231 := bstep (se 1 (by rfl) ⟨557423, by rfl⟩ : syracuseStep 743231 = 1114847) B1114847
theorem B350015 : Blo 346754 350015 := bstep (se 1 (by rfl) ⟨262511, by rfl⟩ : syracuseStep 350015 = 525023) B525023
theorem B350191 : Blo 346754 350191 := bstep (se 1 (by rfl) ⟨262643, by rfl⟩ : syracuseStep 350191 = 525287) B525287
theorem B350363 : Blo 346754 350363 := bstep (se 1 (by rfl) ⟨262772, by rfl⟩ : syracuseStep 350363 = 525545) B525545
theorem B350399 : Blo 346754 350399 := bstep (se 1 (by rfl) ⟨262799, by rfl⟩ : syracuseStep 350399 = 525599) B525599
theorem B1988873 : Blo 346754 1988873 := bstep (se 2 (by rfl) ⟨745827, by rfl⟩ : syracuseStep 1988873 = 1491655) B1491655
theorem B350511 : Blo 346754 350511 := bstep (se 1 (by rfl) ⟨262883, by rfl⟩ : syracuseStep 350511 = 525767) B525767
theorem B350747 : Blo 346754 350747 := bstep (se 1 (by rfl) ⟨263060, by rfl⟩ : syracuseStep 350747 = 526121) B526121
theorem B350751 : Blo 346754 350751 := bstep (se 1 (by rfl) ⟨263063, by rfl⟩ : syracuseStep 350751 = 526127) B526127
theorem B2153453 : Blo 346754 2153453 := bstep (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) B807545
theorem B2841581 : Blo 346754 2841581 := bstep (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) B1065593
theorem B1989623 : Blo 346754 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B1170503 : Blo 346754 1170503 := bstep (se 1 (by rfl) ⟨877877, by rfl⟩ : syracuseStep 1170503 = 1755755) B1755755
theorem B1170557 : Blo 346754 1170557 := bstep (se 3 (by rfl) ⟨219479, by rfl⟩ : syracuseStep 1170557 = 438959) B438959
theorem B1170827 : Blo 346754 1170827 := bstep (se 1 (by rfl) ⟨878120, by rfl⟩ : syracuseStep 1170827 = 1756241) B1756241
theorem B744871 : Blo 346754 744871 := bstep (se 1 (by rfl) ⟨558653, by rfl⟩ : syracuseStep 744871 = 1117307) B1117307
theorem B2645783 : Blo 346754 2645783 := bstep (se 1 (by rfl) ⟨1984337, by rfl⟩ : syracuseStep 2645783 = 3968675) B3968675
theorem B2121527 : Blo 346754 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B3563777 : Blo 346754 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B3368101 : Blo 346754 3368101 := bstep (se 4 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 3368101 = 631519) B631519
theorem B877999 : Blo 346754 877999 := bstep (se 1 (by rfl) ⟨658499, by rfl⟩ : syracuseStep 877999 = 1316999) B1316999
theorem B1697273 : Blo 346754 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B1009313 : Blo 346754 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B878303 : Blo 346754 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B780479 : Blo 346754 780479 := bstep (se 1 (by rfl) ⟨585359, by rfl⟩ : syracuseStep 780479 = 1170719) B1170719
theorem B1173851 : Blo 346754 1173851 := bstep (se 1 (by rfl) ⟨880388, by rfl⟩ : syracuseStep 1173851 = 1760777) B1760777
theorem B1174121 : Blo 346754 1174121 := bstep (se 2 (by rfl) ⟨440295, by rfl⟩ : syracuseStep 1174121 = 880591) B880591
theorem B2649185 : Blo 346754 2649185 := bstep (se 2 (by rfl) ⟨993444, by rfl⟩ : syracuseStep 2649185 = 1986889) B1986889
theorem B781433 : Blo 346754 781433 := bstep (se 2 (by rfl) ⟨293037, by rfl⟩ : syracuseStep 781433 = 586075) B586075
theorem B1699159 : Blo 346754 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B880055 : Blo 346754 880055 := bstep (se 1 (by rfl) ⟨660041, by rfl⟩ : syracuseStep 880055 = 1320083) B1320083
theorem B585191 : Blo 346754 585191 := bstep (se 1 (by rfl) ⟨438893, by rfl⟩ : syracuseStep 585191 = 877787) B877787
theorem B585211 : Blo 346754 585211 := bstep (se 1 (by rfl) ⟨438908, by rfl⟩ : syracuseStep 585211 = 877817) B877817
theorem B1175147 : Blo 346754 1175147 := bstep (se 1 (by rfl) ⟨881360, by rfl⟩ : syracuseStep 1175147 = 1762721) B1762721
theorem B1764989 : Blo 346754 1764989 := bstep (se 3 (by rfl) ⟨330935, by rfl⟩ : syracuseStep 1764989 = 661871) B661871
theorem B782099 : Blo 346754 782099 := bstep (se 1 (by rfl) ⟨586574, by rfl⟩ : syracuseStep 782099 = 1173149) B1173149
theorem B1175417 : Blo 346754 1175417 := bstep (se 2 (by rfl) ⟨440781, by rfl⟩ : syracuseStep 1175417 = 881563) B881563
theorem B585643 : Blo 346754 585643 := bstep (se 1 (by rfl) ⟨439232, by rfl⟩ : syracuseStep 585643 = 878465) B878465
theorem B782459 : Blo 346754 782459 := bstep (se 1 (by rfl) ⟨586844, by rfl⟩ : syracuseStep 782459 = 1173689) B1173689
theorem B1175741 : Blo 346754 1175741 := bstep (se 3 (by rfl) ⟨220451, by rfl⟩ : syracuseStep 1175741 = 440903) B440903
theorem B585947 : Blo 346754 585947 := bstep (se 1 (by rfl) ⟨439460, by rfl⟩ : syracuseStep 585947 = 878921) B878921
theorem B782729 : Blo 346754 782729 := bstep (se 2 (by rfl) ⟨293523, by rfl⟩ : syracuseStep 782729 = 587047) B587047
theorem B1765799 : Blo 346754 1765799 := bstep (se 1 (by rfl) ⟨1324349, by rfl⟩ : syracuseStep 1765799 = 2648699) B2648699
theorem B586183 : Blo 346754 586183 := bstep (se 1 (by rfl) ⟨439637, by rfl⟩ : syracuseStep 586183 = 879275) B879275
theorem B520655 : Blo 346754 520655 := bstep (se 1 (by rfl) ⟨390491, by rfl⟩ : syracuseStep 520655 = 780983) B780983
theorem B586217 : Blo 346754 586217 := bstep (se 2 (by rfl) ⟨219831, by rfl⟩ : syracuseStep 586217 = 439663) B439663
theorem B520697 : Blo 346754 520697 := bstep (se 2 (by rfl) ⟨195261, by rfl⟩ : syracuseStep 520697 = 390523) B390523
theorem B520799 : Blo 346754 520799 := bstep (se 1 (by rfl) ⟨390599, by rfl⟩ : syracuseStep 520799 = 781199) B781199
theorem B4485779 : Blo 346754 4485779 := bstep (se 1 (by rfl) ⟨3364334, by rfl⟩ : syracuseStep 4485779 = 6728669) B6728669
theorem B521279 : Blo 346754 521279 := bstep (se 1 (by rfl) ⟨390959, by rfl⟩ : syracuseStep 521279 = 781919) B781919
theorem B455743 : Blo 346754 455743 := bstep (se 1 (by rfl) ⟨341807, by rfl⟩ : syracuseStep 455743 = 683615) B683615
theorem B521321 : Blo 346754 521321 := bstep (se 2 (by rfl) ⟨195495, by rfl⟩ : syracuseStep 521321 = 390991) B390991
theorem B783467 : Blo 346754 783467 := bstep (se 1 (by rfl) ⟨587600, by rfl⟩ : syracuseStep 783467 = 1175201) B1175201
theorem B521423 : Blo 346754 521423 := bstep (se 1 (by rfl) ⟨391067, by rfl⟩ : syracuseStep 521423 = 782135) B782135
theorem B1111259 : Blo 346754 1111259 := bstep (se 1 (by rfl) ⟨833444, by rfl⟩ : syracuseStep 1111259 = 1666889) B1666889
theorem B3994919 : Blo 346754 3994919 := bstep (se 1 (by rfl) ⟨2996189, by rfl⟩ : syracuseStep 3994919 = 5992379) B5992379
theorem B1176929 : Blo 346754 1176929 := bstep (se 2 (by rfl) ⟨441348, by rfl⟩ : syracuseStep 1176929 = 882697) B882697
theorem B521627 : Blo 346754 521627 := bstep (se 1 (by rfl) ⟨391220, by rfl⟩ : syracuseStep 521627 = 782441) B782441
theorem B6387133 : Blo 346754 6387133 := bstep (se 3 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 6387133 = 2395175) B2395175
theorem B521849 : Blo 346754 521849 := bstep (se 2 (by rfl) ⟨195693, by rfl⟩ : syracuseStep 521849 = 391387) B391387
theorem B784043 : Blo 346754 784043 := bstep (se 1 (by rfl) ⟨588032, by rfl⟩ : syracuseStep 784043 = 1176065) B1176065
theorem B1767095 : Blo 346754 1767095 := bstep (se 1 (by rfl) ⟨1325321, by rfl⟩ : syracuseStep 1767095 = 2650643) B2650643
theorem B521951 : Blo 346754 521951 := bstep (se 1 (by rfl) ⟨391463, by rfl⟩ : syracuseStep 521951 = 782927) B782927
theorem B522047 : Blo 346754 522047 := bstep (se 1 (by rfl) ⟨391535, by rfl⟩ : syracuseStep 522047 = 783071) B783071
theorem B2226001 : Blo 346754 2226001 := bstep (se 2 (by rfl) ⟨834750, by rfl⟩ : syracuseStep 2226001 = 1669501) B1669501
theorem B882647 : Blo 346754 882647 := bstep (se 1 (by rfl) ⟨661985, by rfl⟩ : syracuseStep 882647 = 1323971) B1323971
theorem B3962843 : Blo 346754 3962843 := bstep (se 1 (by rfl) ⟨2972132, by rfl⟩ : syracuseStep 3962843 = 5944265) B5944265
theorem B1112039 : Blo 346754 1112039 := bstep (se 1 (by rfl) ⟨834029, by rfl⟩ : syracuseStep 1112039 = 1668059) B1668059
theorem B522215 : Blo 346754 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B784367 : Blo 346754 784367 := bstep (se 1 (by rfl) ⟨588275, by rfl⟩ : syracuseStep 784367 = 1176551) B1176551
theorem B1210351 : Blo 346754 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B522233 : Blo 346754 522233 := bstep (se 2 (by rfl) ⟨195837, by rfl⟩ : syracuseStep 522233 = 391675) B391675
theorem B5961761 : Blo 346754 5961761 := bstep (se 2 (by rfl) ⟨2235660, by rfl⟩ : syracuseStep 5961761 = 4471321) B4471321
theorem B522335 : Blo 346754 522335 := bstep (se 1 (by rfl) ⟨391751, by rfl⟩ : syracuseStep 522335 = 783503) B783503
theorem B522395 : Blo 346754 522395 := bstep (se 1 (by rfl) ⟨391796, by rfl⟩ : syracuseStep 522395 = 783593) B783593
theorem B522431 : Blo 346754 522431 := bstep (se 1 (by rfl) ⟨391823, by rfl⟩ : syracuseStep 522431 = 783647) B783647
theorem B784583 : Blo 346754 784583 := bstep (se 1 (by rfl) ⟨588437, by rfl⟩ : syracuseStep 784583 = 1176875) B1176875
theorem B522473 : Blo 346754 522473 := bstep (se 2 (by rfl) ⟨195927, by rfl⟩ : syracuseStep 522473 = 391855) B391855
theorem B1439977 : Blo 346754 1439977 := bstep (se 2 (by rfl) ⟨539991, by rfl⟩ : syracuseStep 1439977 = 1079983) B1079983
theorem B2390309 : Blo 346754 2390309 := bstep (se 4 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 2390309 = 448183) B448183
theorem B588073 : Blo 346754 588073 := bstep (se 2 (by rfl) ⟨220527, by rfl⟩ : syracuseStep 588073 = 441055) B441055
theorem B784763 : Blo 346754 784763 := bstep (se 1 (by rfl) ⟨588572, by rfl⟩ : syracuseStep 784763 = 1177145) B1177145
theorem B522779 : Blo 346754 522779 := bstep (se 1 (by rfl) ⟨392084, by rfl⟩ : syracuseStep 522779 = 784169) B784169
theorem B391711 : Blo 346754 391711 := bstep (se 1 (by rfl) ⟨293783, by rfl⟩ : syracuseStep 391711 = 587567) B587567
theorem B1997369 : Blo 346754 1997369 := bstep (se 2 (by rfl) ⟨749013, by rfl⟩ : syracuseStep 1997369 = 1498027) B1498027
theorem B522857 : Blo 346754 522857 := bstep (se 2 (by rfl) ⟨196071, by rfl⟩ : syracuseStep 522857 = 392143) B392143
theorem B785033 : Blo 346754 785033 := bstep (se 2 (by rfl) ⟨294387, by rfl⟩ : syracuseStep 785033 = 588775) B588775
theorem B3341189 : Blo 346754 3341189 := bstep (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) B626473
theorem B3210329 : Blo 346754 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B523385 : Blo 346754 523385 := bstep (se 2 (by rfl) ⟨196269, by rfl⟩ : syracuseStep 523385 = 392539) B392539
theorem B785591 : Blo 346754 785591 := bstep (se 1 (by rfl) ⟨589193, by rfl⟩ : syracuseStep 785591 = 1178387) B1178387
theorem B523487 : Blo 346754 523487 := bstep (se 1 (by rfl) ⟨392615, by rfl⟩ : syracuseStep 523487 = 785231) B785231
theorem B1178873 : Blo 346754 1178873 := bstep (se 2 (by rfl) ⟨442077, by rfl⟩ : syracuseStep 1178873 = 884155) B884155
theorem B523529 : Blo 346754 523529 := bstep (se 2 (by rfl) ⟨196323, by rfl⟩ : syracuseStep 523529 = 392647) B392647
theorem B523631 : Blo 346754 523631 := bstep (se 1 (by rfl) ⟨392723, by rfl⟩ : syracuseStep 523631 = 785447) B785447
theorem B2653559 : Blo 346754 2653559 := bstep (se 1 (by rfl) ⟨1990169, by rfl⟩ : syracuseStep 2653559 = 3980339) B3980339
theorem B884135 : Blo 346754 884135 := bstep (se 1 (by rfl) ⟨663101, by rfl⟩ : syracuseStep 884135 = 1326203) B1326203
theorem B523751 : Blo 346754 523751 := bstep (se 1 (by rfl) ⟨392813, by rfl⟩ : syracuseStep 523751 = 785627) B785627
theorem B1179143 : Blo 346754 1179143 := bstep (se 1 (by rfl) ⟨884357, by rfl⟩ : syracuseStep 1179143 = 1768715) B1768715
theorem B1113679 : Blo 346754 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B589403 : Blo 346754 589403 := bstep (se 1 (by rfl) ⟨442052, by rfl⟩ : syracuseStep 589403 = 884105) B884105
theorem B523883 : Blo 346754 523883 := bstep (se 1 (by rfl) ⟨392912, by rfl⟩ : syracuseStep 523883 = 785825) B785825
theorem B1113833 : Blo 346754 1113833 := bstep (se 2 (by rfl) ⟨417687, by rfl⟩ : syracuseStep 1113833 = 835375) B835375
theorem B524009 : Blo 346754 524009 := bstep (se 2 (by rfl) ⟨196503, by rfl⟩ : syracuseStep 524009 = 393007) B393007
theorem B786167 : Blo 346754 786167 := bstep (se 1 (by rfl) ⟨589625, by rfl⟩ : syracuseStep 786167 = 1179251) B1179251
theorem B589639 : Blo 346754 589639 := bstep (se 1 (by rfl) ⟨442229, by rfl⟩ : syracuseStep 589639 = 884459) B884459
theorem B524153 : Blo 346754 524153 := bstep (se 2 (by rfl) ⟨196557, by rfl⟩ : syracuseStep 524153 = 393115) B393115
theorem B786347 : Blo 346754 786347 := bstep (se 1 (by rfl) ⟨589760, by rfl⟩ : syracuseStep 786347 = 1179521) B1179521
theorem B524255 : Blo 346754 524255 := bstep (se 1 (by rfl) ⟨393191, by rfl⟩ : syracuseStep 524255 = 786383) B786383
theorem B524591 : Blo 346754 524591 := bstep (se 1 (by rfl) ⟨393443, by rfl⟩ : syracuseStep 524591 = 786887) B786887
theorem B786815 : Blo 346754 786815 := bstep (se 1 (by rfl) ⟨590111, by rfl⟩ : syracuseStep 786815 = 1180223) B1180223
theorem B524831 : Blo 346754 524831 := bstep (se 1 (by rfl) ⟨393623, by rfl⟩ : syracuseStep 524831 = 787247) B787247
theorem B6423079 : Blo 346754 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B787049 : Blo 346754 787049 := bstep (se 2 (by rfl) ⟨295143, by rfl⟩ : syracuseStep 787049 = 590287) B590287
theorem B9503405 : Blo 346754 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B394015 : Blo 346754 394015 := bstep (se 1 (by rfl) ⟨295511, by rfl⟩ : syracuseStep 394015 = 591023) B591023
theorem B525503 : Blo 346754 525503 := bstep (se 1 (by rfl) ⟨394127, by rfl⟩ : syracuseStep 525503 = 788255) B788255
theorem B787679 : Blo 346754 787679 := bstep (se 1 (by rfl) ⟨590759, by rfl⟩ : syracuseStep 787679 = 1181519) B1181519
theorem B591151 : Blo 346754 591151 := bstep (se 1 (by rfl) ⟨443363, by rfl⟩ : syracuseStep 591151 = 886727) B886727
theorem B525647 : Blo 346754 525647 := bstep (se 1 (by rfl) ⟨394235, by rfl⟩ : syracuseStep 525647 = 788471) B788471
theorem B525737 : Blo 346754 525737 := bstep (se 2 (by rfl) ⟨197151, by rfl⟩ : syracuseStep 525737 = 394303) B394303
theorem B787895 : Blo 346754 787895 := bstep (se 1 (by rfl) ⟨590921, by rfl⟩ : syracuseStep 787895 = 1181843) B1181843
theorem B18089405 : Blo 346754 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B886241 : Blo 346754 886241 := bstep (se 2 (by rfl) ⟨332340, by rfl⟩ : syracuseStep 886241 = 664681) B664681
theorem B4490801 : Blo 346754 4490801 := bstep (se 2 (by rfl) ⟨1684050, by rfl⟩ : syracuseStep 4490801 = 3368101) B3368101
theorem B525887 : Blo 346754 525887 := bstep (se 1 (by rfl) ⟨394415, by rfl⟩ : syracuseStep 525887 = 788831) B788831
theorem B525929 : Blo 346754 525929 := bstep (se 2 (by rfl) ⟨197223, by rfl⟩ : syracuseStep 525929 = 394447) B394447
theorem B788075 : Blo 346754 788075 := bstep (se 1 (by rfl) ⟨591056, by rfl⟩ : syracuseStep 788075 = 1182113) B1182113
theorem B788345 : Blo 346754 788345 := bstep (se 2 (by rfl) ⟨295629, by rfl⟩ : syracuseStep 788345 = 591259) B591259
theorem B8128457 : Blo 346754 8128457 := bstep (se 2 (by rfl) ⟨3048171, by rfl⟩ : syracuseStep 8128457 = 6096343) B6096343
theorem B788777 : Blo 346754 788777 := bstep (se 2 (by rfl) ⟨295791, by rfl⟩ : syracuseStep 788777 = 591583) B591583
theorem B1182167 : Blo 346754 1182167 := bstep (se 1 (by rfl) ⟨886625, by rfl⟩ : syracuseStep 1182167 = 1773251) B1773251
theorem B2755073 : Blo 346754 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B4459535 : Blo 346754 4459535 := bstep (se 1 (by rfl) ⟨3344651, by rfl⟩ : syracuseStep 4459535 = 6689303) B6689303
theorem B560191 : Blo 346754 560191 := bstep (se 1 (by rfl) ⟨420143, by rfl⟩ : syracuseStep 560191 = 840287) B840287
theorem B12782879 : Blo 346754 12782879 := bstep (se 1 (by rfl) ⟨9587159, by rfl⟩ : syracuseStep 12782879 = 19174319) B19174319
theorem B1772927 : Blo 346754 1772927 := bstep (se 1 (by rfl) ⟨1329695, by rfl⟩ : syracuseStep 1772927 = 2659391) B2659391
theorem B495487 : Blo 346754 495487 := bstep (se 1 (by rfl) ⟨371615, by rfl⟩ : syracuseStep 495487 = 743231) B743231
theorem B2986145 : Blo 346754 2986145 := bstep (se 2 (by rfl) ⟨1119804, by rfl⟩ : syracuseStep 2986145 = 2239609) B2239609
theorem B2265545 : Blo 346754 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B24154685 : Blo 346754 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B4788809 : Blo 346754 4788809 := bstep (se 2 (by rfl) ⟨1795803, by rfl⟩ : syracuseStep 4788809 = 3591607) B3591607
theorem B660307 : Blo 346754 660307 := bstep (se 1 (by rfl) ⟨495230, by rfl⟩ : syracuseStep 660307 = 990461) B990461
theorem B791387 : Blo 346754 791387 := bstep (se 1 (by rfl) ⟨593540, by rfl⟩ : syracuseStep 791387 = 1187081) B1187081
theorem B660383 : Blo 346754 660383 := bstep (se 1 (by rfl) ⟨495287, by rfl⟩ : syracuseStep 660383 = 990575) B990575
theorem B1414351 : Blo 346754 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B661279 : Blo 346754 661279 := bstep (se 1 (by rfl) ⟨495959, by rfl⟩ : syracuseStep 661279 = 991919) B991919
theorem B1513313 : Blo 346754 1513313 := bstep (se 2 (by rfl) ⟨567492, by rfl⟩ : syracuseStep 1513313 = 1134985) B1134985
theorem B1316969 : Blo 346754 1316969 := bstep (se 2 (by rfl) ⟨493863, by rfl⟩ : syracuseStep 1316969 = 987727) B987727
theorem B1513687 : Blo 346754 1513687 := bstep (se 1 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 1513687 = 2270531) B2270531
theorem B792991 : Blo 346754 792991 := bstep (se 1 (by rfl) ⟨594743, by rfl⟩ : syracuseStep 792991 = 1189487) B1189487
theorem B1121035 : Blo 346754 1121035 := bstep (se 1 (by rfl) ⟨840776, by rfl⟩ : syracuseStep 1121035 = 1681553) B1681553
theorem B662327 : Blo 346754 662327 := bstep (se 1 (by rfl) ⟨496745, by rfl⟩ : syracuseStep 662327 = 993491) B993491
theorem B1318153 : Blo 346754 1318153 := bstep (se 2 (by rfl) ⟨494307, by rfl⟩ : syracuseStep 1318153 = 988615) B988615
theorem B1318457 : Blo 346754 1318457 := bstep (se 2 (by rfl) ⟨494421, by rfl⟩ : syracuseStep 1318457 = 988843) B988843
theorem B8494753 : Blo 346754 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B5742541 : Blo 346754 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B1613801 : Blo 346754 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B13345073 : Blo 346754 13345073 := bstep (se 2 (by rfl) ⟨5004402, by rfl⟩ : syracuseStep 13345073 = 10008805) B10008805
theorem B2990519 : Blo 346754 2990519 := bstep (se 1 (by rfl) ⟨2242889, by rfl⟩ : syracuseStep 2990519 = 4485779) B4485779
theorem B795163 : Blo 346754 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B1253971 : Blo 346754 1253971 := bstep (se 1 (by rfl) ⟨940478, by rfl⟩ : syracuseStep 1253971 = 1880957) B1880957
theorem B664271 : Blo 346754 664271 := bstep (se 1 (by rfl) ⟨498203, by rfl⟩ : syracuseStep 664271 = 996407) B996407
theorem B2663279 : Blo 346754 2663279 := bstep (se 1 (by rfl) ⟨1997459, by rfl⟩ : syracuseStep 2663279 = 3994919) B3994919
theorem B6366107 : Blo 346754 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B3974507 : Blo 346754 3974507 := bstep (se 1 (by rfl) ⟨2980880, by rfl⟩ : syracuseStep 3974507 = 5961761) B5961761
theorem B993161 : Blo 346754 993161 := bstep (se 2 (by rfl) ⟨372435, by rfl⟩ : syracuseStep 993161 = 744871) B744871
theorem B4466735 : Blo 346754 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B2140219 : Blo 346754 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B1484905 : Blo 346754 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B1321373 : Blo 346754 1321373 := bstep (se 3 (by rfl) ⟨247757, by rfl⟩ : syracuseStep 1321373 = 495515) B495515
theorem B1321555 : Blo 346754 1321555 := bstep (se 1 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 1321555 = 1982333) B1982333
theorem B535519 : Blo 346754 535519 := bstep (se 1 (by rfl) ⟨401639, by rfl⟩ : syracuseStep 535519 = 803279) B803279
theorem B1191323 : Blo 346754 1191323 := bstep (se 1 (by rfl) ⟨893492, by rfl⟩ : syracuseStep 1191323 = 1786985) B1786985
theorem B2830099 : Blo 346754 2830099 := bstep (se 1 (by rfl) ⟨2122574, by rfl⟩ : syracuseStep 2830099 = 4245149) B4245149
theorem B3911759 : Blo 346754 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B5026319 : Blo 346754 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B1487555 : Blo 346754 1487555 := bstep (se 1 (by rfl) ⟨1115666, by rfl⟩ : syracuseStep 1487555 = 2231333) B2231333
theorem B3781505 : Blo 346754 3781505 := bstep (se 2 (by rfl) ⟨1418064, by rfl⟩ : syracuseStep 3781505 = 2836129) B2836129
theorem B1684435 : Blo 346754 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B6009851 : Blo 346754 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B2241607 : Blo 346754 2241607 := bstep (se 1 (by rfl) ⟨1681205, by rfl⟩ : syracuseStep 2241607 = 3362411) B3362411
theorem B2995643 : Blo 346754 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B1488527 : Blo 346754 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B9647923 : Blo 346754 9647923 := bstep (se 1 (by rfl) ⟨7235942, by rfl⟩ : syracuseStep 9647923 = 14471885) B14471885
theorem B1488937 : Blo 346754 1488937 := bstep (se 2 (by rfl) ⟨558351, by rfl⟩ : syracuseStep 1488937 = 1116703) B1116703
theorem B2963627 : Blo 346754 2963627 := bstep (se 1 (by rfl) ⟨2222720, by rfl⟩ : syracuseStep 2963627 = 4445441) B4445441
theorem B5650661 : Blo 346754 5650661 := bstep (se 4 (by rfl) ⟨529749, by rfl⟩ : syracuseStep 5650661 = 1059499) B1059499
theorem B1063207 : Blo 346754 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B670441 : Blo 346754 670441 := bstep (se 2 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 670441 = 502831) B502831
theorem B1325915 : Blo 346754 1325915 := bstep (se 1 (by rfl) ⟨994436, by rfl⟩ : syracuseStep 1325915 = 1988873) B1988873
theorem B1325929 : Blo 346754 1325929 := bstep (se 2 (by rfl) ⟨497223, by rfl⟩ : syracuseStep 1325929 = 994447) B994447
theorem B1326415 : Blo 346754 1326415 := bstep (se 1 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 1326415 = 1989623) B1989623
theorem B835067 : Blo 346754 835067 := bstep (se 1 (by rfl) ⟨626300, by rfl⟩ : syracuseStep 835067 = 1252601) B1252601
theorem B1131515 : Blo 346754 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B377903 : Blo 346754 377903 := bstep (se 1 (by rfl) ⟨283427, by rfl⟩ : syracuseStep 377903 = 566855) B566855
theorem B672875 : Blo 346754 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B200263043 : Blo 346754 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B607657 : Blo 346754 607657 := bstep (se 2 (by rfl) ⟨227871, by rfl⟩ : syracuseStep 607657 = 455743) B455743
theorem B2968001 : Blo 346754 2968001 := bstep (se 2 (by rfl) ⟨1113000, by rfl⟩ : syracuseStep 2968001 = 2226001) B2226001
theorem B838441 : Blo 346754 838441 := bstep (se 2 (by rfl) ⟨314415, by rfl⟩ : syracuseStep 838441 = 628831) B628831
theorem B347103 : Blo 346754 347103 := bstep (se 1 (by rfl) ⟨260327, by rfl⟩ : syracuseStep 347103 = 520655) B520655
theorem B1919969 : Blo 346754 1919969 := bstep (se 2 (by rfl) ⟨719988, by rfl⟩ : syracuseStep 1919969 = 1439977) B1439977
theorem B347131 : Blo 346754 347131 := bstep (se 1 (by rfl) ⟨260348, by rfl⟩ : syracuseStep 347131 = 520697) B520697
theorem B347199 : Blo 346754 347199 := bstep (se 1 (by rfl) ⟨260399, by rfl⟩ : syracuseStep 347199 = 520799) B520799
theorem B347519 : Blo 346754 347519 := bstep (se 1 (by rfl) ⟨260639, by rfl⟩ : syracuseStep 347519 = 521279) B521279
theorem B347547 : Blo 346754 347547 := bstep (se 1 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 347547 = 521321) B521321
theorem B347615 : Blo 346754 347615 := bstep (se 1 (by rfl) ⟨260711, by rfl⟩ : syracuseStep 347615 = 521423) B521423
theorem B740839 : Blo 346754 740839 := bstep (se 1 (by rfl) ⟨555629, by rfl⟩ : syracuseStep 740839 = 1111259) B1111259
theorem B347751 : Blo 346754 347751 := bstep (se 1 (by rfl) ⟨260813, by rfl⟩ : syracuseStep 347751 = 521627) B521627
theorem B347899 : Blo 346754 347899 := bstep (se 1 (by rfl) ⟨260924, by rfl⟩ : syracuseStep 347899 = 521849) B521849
theorem B347967 : Blo 346754 347967 := bstep (se 1 (by rfl) ⟨260975, by rfl⟩ : syracuseStep 347967 = 521951) B521951
theorem B348031 : Blo 346754 348031 := bstep (se 1 (by rfl) ⟨261023, by rfl⟩ : syracuseStep 348031 = 522047) B522047
theorem B2641895 : Blo 346754 2641895 := bstep (se 1 (by rfl) ⟨1981421, by rfl⟩ : syracuseStep 2641895 = 3962843) B3962843
theorem B741359 : Blo 346754 741359 := bstep (se 1 (by rfl) ⟨556019, by rfl⟩ : syracuseStep 741359 = 1112039) B1112039
theorem B348143 : Blo 346754 348143 := bstep (se 1 (by rfl) ⟨261107, by rfl⟩ : syracuseStep 348143 = 522215) B522215
theorem B348155 : Blo 346754 348155 := bstep (se 1 (by rfl) ⟨261116, by rfl⟩ : syracuseStep 348155 = 522233) B522233
theorem B1036327 : Blo 346754 1036327 := bstep (se 1 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 1036327 = 1554491) B1554491
theorem B348223 : Blo 346754 348223 := bstep (se 1 (by rfl) ⟨261167, by rfl⟩ : syracuseStep 348223 = 522335) B522335
theorem B348263 : Blo 346754 348263 := bstep (se 1 (by rfl) ⟨261197, by rfl⟩ : syracuseStep 348263 = 522395) B522395
theorem B348287 : Blo 346754 348287 := bstep (se 1 (by rfl) ⟨261215, by rfl⟩ : syracuseStep 348287 = 522431) B522431
theorem B348315 : Blo 346754 348315 := bstep (se 1 (by rfl) ⟨261236, by rfl⟩ : syracuseStep 348315 = 522473) B522473
theorem B1593539 : Blo 346754 1593539 := bstep (se 1 (by rfl) ⟨1195154, by rfl⟩ : syracuseStep 1593539 = 2390309) B2390309
theorem B348519 : Blo 346754 348519 := bstep (se 1 (by rfl) ⟨261389, by rfl⟩ : syracuseStep 348519 = 522779) B522779
theorem B1331579 : Blo 346754 1331579 := bstep (se 1 (by rfl) ⟨998684, by rfl⟩ : syracuseStep 1331579 = 1997369) B1997369
theorem B348571 : Blo 346754 348571 := bstep (se 1 (by rfl) ⟨261428, by rfl⟩ : syracuseStep 348571 = 522857) B522857
theorem B348923 : Blo 346754 348923 := bstep (se 1 (by rfl) ⟨261692, by rfl⟩ : syracuseStep 348923 = 523385) B523385
theorem B348991 : Blo 346754 348991 := bstep (se 1 (by rfl) ⟨261743, by rfl⟩ : syracuseStep 348991 = 523487) B523487
theorem B349019 : Blo 346754 349019 := bstep (se 1 (by rfl) ⟨261764, by rfl⟩ : syracuseStep 349019 = 523529) B523529
theorem B349087 : Blo 346754 349087 := bstep (se 1 (by rfl) ⟨261815, by rfl⟩ : syracuseStep 349087 = 523631) B523631
theorem B1889261 : Blo 346754 1889261 := bstep (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) B708473
theorem B1496045 : Blo 346754 1496045 := bstep (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) B561017
theorem B349167 : Blo 346754 349167 := bstep (se 1 (by rfl) ⟨261875, by rfl⟩ : syracuseStep 349167 = 523751) B523751
theorem B349255 : Blo 346754 349255 := bstep (se 1 (by rfl) ⟨261941, by rfl⟩ : syracuseStep 349255 = 523883) B523883
theorem B742555 : Blo 346754 742555 := bstep (se 1 (by rfl) ⟨556916, by rfl⟩ : syracuseStep 742555 = 1113833) B1113833
theorem B349339 : Blo 346754 349339 := bstep (se 1 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 349339 = 524009) B524009
theorem B349435 : Blo 346754 349435 := bstep (se 1 (by rfl) ⟨262076, by rfl⟩ : syracuseStep 349435 = 524153) B524153
theorem B349503 : Blo 346754 349503 := bstep (se 1 (by rfl) ⟨262127, by rfl⟩ : syracuseStep 349503 = 524255) B524255
theorem B349671 : Blo 346754 349671 := bstep (se 1 (by rfl) ⟨262253, by rfl⟩ : syracuseStep 349671 = 524507) B524507
theorem B349679 : Blo 346754 349679 := bstep (se 1 (by rfl) ⟨262259, by rfl⟩ : syracuseStep 349679 = 524519) B524519
theorem B1889801 : Blo 346754 1889801 := bstep (se 2 (by rfl) ⟨708675, by rfl⟩ : syracuseStep 1889801 = 1417351) B1417351
theorem B1594889 : Blo 346754 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B7296551 : Blo 346754 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B841295 : Blo 346754 841295 := bstep (se 1 (by rfl) ⟨630971, by rfl⟩ : syracuseStep 841295 = 1261943) B1261943
theorem B349787 : Blo 346754 349787 := bstep (se 1 (by rfl) ⟨262340, by rfl⟩ : syracuseStep 349787 = 524681) B524681
theorem B349851 : Blo 346754 349851 := bstep (se 1 (by rfl) ⟨262388, by rfl⟩ : syracuseStep 349851 = 524777) B524777
theorem B349935 : Blo 346754 349935 := bstep (se 1 (by rfl) ⟨262451, by rfl⟩ : syracuseStep 349935 = 524903) B524903
theorem B350023 : Blo 346754 350023 := bstep (se 1 (by rfl) ⟨262517, by rfl⟩ : syracuseStep 350023 = 525035) B525035
theorem B350043 : Blo 346754 350043 := bstep (se 1 (by rfl) ⟨262532, by rfl⟩ : syracuseStep 350043 = 525065) B525065
theorem B350111 : Blo 346754 350111 := bstep (se 1 (by rfl) ⟨262583, by rfl⟩ : syracuseStep 350111 = 525167) B525167
theorem B743393 : Blo 346754 743393 := bstep (se 2 (by rfl) ⟨278772, by rfl⟩ : syracuseStep 743393 = 557545) B557545
theorem B3758147 : Blo 346754 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B350279 : Blo 346754 350279 := bstep (se 1 (by rfl) ⟨262709, by rfl⟩ : syracuseStep 350279 = 525419) B525419
theorem B350439 : Blo 346754 350439 := bstep (se 1 (by rfl) ⟨262829, by rfl⟩ : syracuseStep 350439 = 525659) B525659
theorem B350623 : Blo 346754 350623 := bstep (se 1 (by rfl) ⟨262967, by rfl⟩ : syracuseStep 350623 = 525935) B525935
theorem B350671 : Blo 346754 350671 := bstep (se 1 (by rfl) ⟨263003, by rfl⟩ : syracuseStep 350671 = 526007) B526007
theorem B350695 : Blo 346754 350695 := bstep (se 1 (by rfl) ⟨263021, by rfl⟩ : syracuseStep 350695 = 526043) B526043
theorem B3562055 : Blo 346754 3562055 := bstep (se 1 (by rfl) ⟨2671541, by rfl⟩ : syracuseStep 3562055 = 5343083) B5343083
theorem B1891183 : Blo 346754 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B1170395 : Blo 346754 1170395 := bstep (se 1 (by rfl) ⟨877796, by rfl⟩ : syracuseStep 1170395 = 1755593) B1755593
theorem B1170665 : Blo 346754 1170665 := bstep (se 2 (by rfl) ⟨438999, by rfl⟩ : syracuseStep 1170665 = 877999) B877999
theorem B1170935 : Blo 346754 1170935 := bstep (se 1 (by rfl) ⟨878201, by rfl⟩ : syracuseStep 1170935 = 1756403) B1756403
theorem B745033 : Blo 346754 745033 := bstep (se 2 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 745033 = 558775) B558775
theorem B352031 : Blo 346754 352031 := bstep (se 1 (by rfl) ⟨264023, by rfl⟩ : syracuseStep 352031 = 528047) B528047
theorem B1597427 : Blo 346754 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B1761425 : Blo 346754 1761425 := bstep (se 2 (by rfl) ⟨660534, by rfl⟩ : syracuseStep 1761425 = 1321069) B1321069
theorem B13656721 : Blo 346754 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B1762235 : Blo 346754 1762235 := bstep (se 1 (by rfl) ⟨1321676, by rfl⟩ : syracuseStep 1762235 = 2643353) B2643353
theorem B1336823 : Blo 346754 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B2975687 : Blo 346754 2975687 := bstep (se 1 (by rfl) ⟨2231765, by rfl⟩ : syracuseStep 2975687 = 4463531) B4463531
theorem B1894387 : Blo 346754 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B3368951 : Blo 346754 3368951 := bstep (se 1 (by rfl) ⟨2526713, by rfl⟩ : syracuseStep 3368951 = 5053427) B5053427
theorem B780281 : Blo 346754 780281 := bstep (se 2 (by rfl) ⟨292605, by rfl⟩ : syracuseStep 780281 = 585211) B585211
theorem B780335 : Blo 346754 780335 := bstep (se 1 (by rfl) ⟨585251, by rfl⟩ : syracuseStep 780335 = 1170503) B1170503
theorem B780371 : Blo 346754 780371 := bstep (se 1 (by rfl) ⟨585278, by rfl⟩ : syracuseStep 780371 = 1170557) B1170557
theorem B780551 : Blo 346754 780551 := bstep (se 1 (by rfl) ⟨585413, by rfl⟩ : syracuseStep 780551 = 1170827) B1170827
theorem B1763693 : Blo 346754 1763693 := bstep (se 3 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 1763693 = 661385) B661385
theorem B1763855 : Blo 346754 1763855 := bstep (se 1 (by rfl) ⟨1322891, by rfl⟩ : syracuseStep 1763855 = 2645783) B2645783
theorem B1993247 : Blo 346754 1993247 := bstep (se 1 (by rfl) ⟨1494935, by rfl⟩ : syracuseStep 1993247 = 2989871) B2989871
theorem B780857 : Blo 346754 780857 := bstep (se 2 (by rfl) ⟨292821, by rfl⟩ : syracuseStep 780857 = 585643) B585643
theorem B420859 : Blo 346754 420859 := bstep (se 1 (by rfl) ⟨315644, by rfl⟩ : syracuseStep 420859 = 631289) B631289
theorem B781577 : Blo 346754 781577 := bstep (se 2 (by rfl) ⟨293091, by rfl⟩ : syracuseStep 781577 = 586183) B586183
theorem B880379 : Blo 346754 880379 := bstep (se 1 (by rfl) ⟨660284, by rfl⟩ : syracuseStep 880379 = 1320569) B1320569
theorem B585535 : Blo 346754 585535 := bstep (se 1 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 585535 = 878303) B878303
theorem B10841951 : Blo 346754 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B520319 : Blo 346754 520319 := bstep (se 1 (by rfl) ⟨390239, by rfl⟩ : syracuseStep 520319 = 780479) B780479
theorem B5009597 : Blo 346754 5009597 := bstep (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) B1878599
theorem B782567 : Blo 346754 782567 := bstep (se 1 (by rfl) ⟨586925, by rfl⟩ : syracuseStep 782567 = 1173851) B1173851
theorem B782747 : Blo 346754 782747 := bstep (se 1 (by rfl) ⟨587060, by rfl⟩ : syracuseStep 782747 = 1174121) B1174121
theorem B8516177 : Blo 346754 8516177 := bstep (se 2 (by rfl) ⟨3193566, by rfl⟩ : syracuseStep 8516177 = 6387133) B6387133
theorem B1766123 : Blo 346754 1766123 := bstep (se 1 (by rfl) ⟨1324592, by rfl⟩ : syracuseStep 1766123 = 2649185) B2649185
theorem B520955 : Blo 346754 520955 := bstep (se 1 (by rfl) ⟨390716, by rfl⟩ : syracuseStep 520955 = 781433) B781433
theorem B586703 : Blo 346754 586703 := bstep (se 1 (by rfl) ⟨440027, by rfl⟩ : syracuseStep 586703 = 880055) B880055
theorem B390127 : Blo 346754 390127 := bstep (se 1 (by rfl) ⟨292595, by rfl⟩ : syracuseStep 390127 = 585191) B585191
theorem B8909837 : Blo 346754 8909837 := bstep (se 3 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 8909837 = 3341189) B3341189
theorem B783431 : Blo 346754 783431 := bstep (se 1 (by rfl) ⟨587573, by rfl⟩ : syracuseStep 783431 = 1175147) B1175147
theorem B1176659 : Blo 346754 1176659 := bstep (se 1 (by rfl) ⟨882494, by rfl⟩ : syracuseStep 1176659 = 1764989) B1764989
theorem B423095 : Blo 346754 423095 := bstep (se 1 (by rfl) ⟨317321, by rfl⟩ : syracuseStep 423095 = 634643) B634643
theorem B521399 : Blo 346754 521399 := bstep (se 1 (by rfl) ⟨391049, by rfl⟩ : syracuseStep 521399 = 782099) B782099
theorem B1766609 : Blo 346754 1766609 := bstep (se 2 (by rfl) ⟨662478, by rfl⟩ : syracuseStep 1766609 = 1324957) B1324957
theorem B783611 : Blo 346754 783611 := bstep (se 1 (by rfl) ⟨587708, by rfl⟩ : syracuseStep 783611 = 1175417) B1175417
theorem B521639 : Blo 346754 521639 := bstep (se 1 (by rfl) ⟨391229, by rfl⟩ : syracuseStep 521639 = 782459) B782459
theorem B783827 : Blo 346754 783827 := bstep (se 1 (by rfl) ⟨587870, by rfl⟩ : syracuseStep 783827 = 1175741) B1175741
theorem B390631 : Blo 346754 390631 := bstep (se 1 (by rfl) ⟨292973, by rfl⟩ : syracuseStep 390631 = 585947) B585947
theorem B521819 : Blo 346754 521819 := bstep (se 1 (by rfl) ⟨391364, by rfl⟩ : syracuseStep 521819 = 782729) B782729
theorem B1177199 : Blo 346754 1177199 := bstep (se 1 (by rfl) ⟨882899, by rfl⟩ : syracuseStep 1177199 = 1765799) B1765799
theorem B390811 : Blo 346754 390811 := bstep (se 1 (by rfl) ⟨293108, by rfl⟩ : syracuseStep 390811 = 586217) B586217
theorem B784097 : Blo 346754 784097 := bstep (se 2 (by rfl) ⟨294036, by rfl⟩ : syracuseStep 784097 = 588073) B588073
theorem B522281 : Blo 346754 522281 := bstep (se 2 (by rfl) ⟨195855, by rfl⟩ : syracuseStep 522281 = 391711) B391711
theorem B522311 : Blo 346754 522311 := bstep (se 1 (by rfl) ⟨391733, by rfl⟩ : syracuseStep 522311 = 783467) B783467
theorem B784619 : Blo 346754 784619 := bstep (se 1 (by rfl) ⟨588464, by rfl⟩ : syracuseStep 784619 = 1176929) B1176929
theorem B522695 : Blo 346754 522695 := bstep (se 1 (by rfl) ⟨392021, by rfl⟩ : syracuseStep 522695 = 784043) B784043
theorem B1178063 : Blo 346754 1178063 := bstep (se 1 (by rfl) ⟨883547, by rfl⟩ : syracuseStep 1178063 = 1767095) B1767095
theorem B1669673 : Blo 346754 1669673 := bstep (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) B1252255
theorem B1112705 : Blo 346754 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B588431 : Blo 346754 588431 := bstep (se 1 (by rfl) ⟨441323, by rfl⟩ : syracuseStep 588431 = 882647) B882647
theorem B522911 : Blo 346754 522911 := bstep (se 1 (by rfl) ⟨392183, by rfl⟩ : syracuseStep 522911 = 784367) B784367
theorem B523055 : Blo 346754 523055 := bstep (se 1 (by rfl) ⟨392291, by rfl⟩ : syracuseStep 523055 = 784583) B784583
theorem B523175 : Blo 346754 523175 := bstep (se 1 (by rfl) ⟨392381, by rfl⟩ : syracuseStep 523175 = 784763) B784763
theorem B523355 : Blo 346754 523355 := bstep (se 1 (by rfl) ⟨392516, by rfl⟩ : syracuseStep 523355 = 785033) B785033
theorem B883993 : Blo 346754 883993 := bstep (se 2 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 883993 = 662995) B662995
theorem B523727 : Blo 346754 523727 := bstep (se 1 (by rfl) ⟨392795, by rfl⟩ : syracuseStep 523727 = 785591) B785591
theorem B785915 : Blo 346754 785915 := bstep (se 1 (by rfl) ⟨589436, by rfl⟩ : syracuseStep 785915 = 1178873) B1178873
theorem B1769039 : Blo 346754 1769039 := bstep (se 1 (by rfl) ⟨1326779, by rfl⟩ : syracuseStep 1769039 = 2653559) B2653559
theorem B589423 : Blo 346754 589423 := bstep (se 1 (by rfl) ⟨442067, by rfl⟩ : syracuseStep 589423 = 884135) B884135
theorem B786095 : Blo 346754 786095 := bstep (se 1 (by rfl) ⟨589571, by rfl⟩ : syracuseStep 786095 = 1179143) B1179143
theorem B392935 : Blo 346754 392935 := bstep (se 1 (by rfl) ⟨294701, by rfl⟩ : syracuseStep 392935 = 589403) B589403
theorem B786185 : Blo 346754 786185 := bstep (se 2 (by rfl) ⟨294819, by rfl⟩ : syracuseStep 786185 = 589639) B589639
theorem B524111 : Blo 346754 524111 := bstep (se 1 (by rfl) ⟨393083, by rfl⟩ : syracuseStep 524111 = 786167) B786167
theorem B524231 : Blo 346754 524231 := bstep (se 1 (by rfl) ⟨393173, by rfl⟩ : syracuseStep 524231 = 786347) B786347
theorem B524543 : Blo 346754 524543 := bstep (se 1 (by rfl) ⟨393407, by rfl⟩ : syracuseStep 524543 = 786815) B786815
theorem B524699 : Blo 346754 524699 := bstep (se 1 (by rfl) ⟨393524, by rfl⟩ : syracuseStep 524699 = 787049) B787049
theorem B754343 : Blo 346754 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B525119 : Blo 346754 525119 := bstep (se 1 (by rfl) ⟨393839, by rfl⟩ : syracuseStep 525119 = 787679) B787679
theorem B525263 : Blo 346754 525263 := bstep (se 1 (by rfl) ⟨393947, by rfl⟩ : syracuseStep 525263 = 787895) B787895
theorem B12059603 : Blo 346754 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B590827 : Blo 346754 590827 := bstep (se 1 (by rfl) ⟨443120, by rfl⟩ : syracuseStep 590827 = 886241) B886241
theorem B525353 : Blo 346754 525353 := bstep (se 2 (by rfl) ⟨197007, by rfl⟩ : syracuseStep 525353 = 394015) B394015
theorem B525383 : Blo 346754 525383 := bstep (se 1 (by rfl) ⟨394037, by rfl⟩ : syracuseStep 525383 = 788075) B788075
theorem B525563 : Blo 346754 525563 := bstep (se 1 (by rfl) ⟨394172, by rfl⟩ : syracuseStep 525563 = 788345) B788345
theorem B525851 : Blo 346754 525851 := bstep (se 1 (by rfl) ⟨394388, by rfl⟩ : syracuseStep 525851 = 788777) B788777
theorem B788111 : Blo 346754 788111 := bstep (se 1 (by rfl) ⟨591083, by rfl⟩ : syracuseStep 788111 = 1182167) B1182167
theorem B1836715 : Blo 346754 1836715 := bstep (se 1 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 1836715 = 2755073) B2755073
theorem B788201 : Blo 346754 788201 := bstep (se 2 (by rfl) ⟨295575, by rfl⟩ : syracuseStep 788201 = 591151) B591151
theorem B1279979 : Blo 346754 1279979 := bstep (se 1 (by rfl) ⟨959984, by rfl⟩ : syracuseStep 1279979 = 1919969) B1919969
theorem B8521919 : Blo 346754 8521919 := bstep (se 1 (by rfl) ⟨6391439, by rfl⟩ : syracuseStep 8521919 = 12782879) B12782879
theorem B1181951 : Blo 346754 1181951 := bstep (se 1 (by rfl) ⟨886463, by rfl⟩ : syracuseStep 1181951 = 1772927) B1772927
theorem B2525849 : Blo 346754 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B2853625 : Blo 346754 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B887719 : Blo 346754 887719 := bstep (se 1 (by rfl) ⟨665789, by rfl⟩ : syracuseStep 887719 = 1331579) B1331579
theorem B1510363 : Blo 346754 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B6687845 : Blo 346754 6687845 := bstep (se 4 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 6687845 = 1253971) B1253971
theorem B527591 : Blo 346754 527591 := bstep (se 1 (by rfl) ⟨395693, by rfl⟩ : syracuseStep 527591 = 791387) B791387
theorem B560863 : Blo 346754 560863 := bstep (se 1 (by rfl) ⟨420647, by rfl⟩ : syracuseStep 560863 = 841295) B841295
theorem B495595 : Blo 346754 495595 := bstep (se 1 (by rfl) ⟨371696, by rfl⟩ : syracuseStep 495595 = 743393) B743393
theorem B987785 : Blo 346754 987785 := bstep (se 2 (by rfl) ⟨370419, by rfl⟩ : syracuseStep 987785 = 740839) B740839
theorem B3773465 : Blo 346754 3773465 := bstep (se 2 (by rfl) ⟨1415049, by rfl⟩ : syracuseStep 3773465 = 2830099) B2830099
theorem B660649 : Blo 346754 660649 := bstep (se 2 (by rfl) ⟨247743, by rfl⟩ : syracuseStep 660649 = 495487) B495487
theorem B1381769 : Blo 346754 1381769 := bstep (se 2 (by rfl) ⟨518163, by rfl⟩ : syracuseStep 1381769 = 1036327) B1036327
theorem B1775519 : Blo 346754 1775519 := bstep (se 1 (by rfl) ⟨1331639, by rfl⟩ : syracuseStep 1775519 = 2663279) B2663279
theorem B891215 : Blo 346754 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B7543205 : Blo 346754 7543205 := bstep (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) B1414351
theorem B662107 : Blo 346754 662107 := bstep (se 1 (by rfl) ⟨496580, by rfl⟩ : syracuseStep 662107 = 993161) B993161
theorem B2988809 : Blo 346754 2988809 := bstep (se 2 (by rfl) ⟨1120803, by rfl⟩ : syracuseStep 2988809 = 2241607) B2241607
theorem B990073 : Blo 346754 990073 := bstep (se 2 (by rfl) ⟨371277, by rfl⟩ : syracuseStep 990073 = 742555) B742555
theorem B794215 : Blo 346754 794215 := bstep (se 1 (by rfl) ⟨595661, by rfl⟩ : syracuseStep 794215 = 1191323) B1191323
theorem B3350879 : Blo 346754 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B1417609 : Blo 346754 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B5677451 : Blo 346754 5677451 := bstep (se 1 (by rfl) ⟨4258088, by rfl⟩ : syracuseStep 5677451 = 8516177) B8516177
theorem B991703 : Blo 346754 991703 := bstep (se 1 (by rfl) ⟨743777, by rfl⟩ : syracuseStep 991703 = 1487555) B1487555
theorem B1057321 : Blo 346754 1057321 := bstep (se 2 (by rfl) ⟨396495, by rfl⟩ : syracuseStep 1057321 = 792991) B792991
theorem B4006567 : Blo 346754 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B5939891 : Blo 346754 5939891 := bstep (se 1 (by rfl) ⟨4454918, by rfl⟩ : syracuseStep 5939891 = 8909837) B8909837
theorem B893921 : Blo 346754 893921 := bstep (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) B670441
theorem B992351 : Blo 346754 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B1975751 : Blo 346754 1975751 := bstep (se 1 (by rfl) ⟨1481813, by rfl⟩ : syracuseStep 1975751 = 2963627) B2963627
theorem B993377 : Blo 346754 993377 := bstep (se 2 (by rfl) ⟨372516, by rfl⟩ : syracuseStep 993377 = 745033) B745033
theorem B4303469 : Blo 346754 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B1976957 : Blo 346754 1976957 := bstep (se 3 (by rfl) ⟨370679, by rfl⟩ : syracuseStep 1976957 = 741359) B741359
theorem B6335603 : Blo 346754 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B1060217 : Blo 346754 1060217 := bstep (se 2 (by rfl) ⟨397581, by rfl⟩ : syracuseStep 1060217 = 795163) B795163
theorem B8564105 : Blo 346754 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B2993867 : Blo 346754 2993867 := bstep (se 1 (by rfl) ⟨2245400, by rfl⟩ : syracuseStep 2993867 = 4490801) B4490801
theorem B5418971 : Blo 346754 5418971 := bstep (se 1 (by rfl) ⟨4064228, by rfl⟩ : syracuseStep 5418971 = 8128457) B8128457
theorem B1978667 : Blo 346754 1978667 := bstep (se 1 (by rfl) ⟨1484000, by rfl⟩ : syracuseStep 1978667 = 2968001) B2968001
theorem B1062359 : Blo 346754 1062359 := bstep (se 1 (by rfl) ⟨796769, by rfl⟩ : syracuseStep 1062359 = 1593539) B1593539
theorem B1979873 : Blo 346754 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B16103123 : Blo 346754 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B3192539 : Blo 346754 3192539 := bstep (se 1 (by rfl) ⟨2394404, by rfl⟩ : syracuseStep 3192539 = 4788809) B4788809
theorem B1128253 : Blo 346754 1128253 := bstep (se 3 (by rfl) ⟨211547, by rfl⟩ : syracuseStep 1128253 = 423095) B423095
theorem B440255 : Blo 346754 440255 := bstep (se 1 (by rfl) ⟨330191, by rfl⟩ : syracuseStep 440255 = 660383) B660383
theorem B1259507 : Blo 346754 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B997363 : Blo 346754 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B1259867 : Blo 346754 1259867 := bstep (se 1 (by rfl) ⟨944900, by rfl⟩ : syracuseStep 1259867 = 1889801) B1889801
theorem B1063259 : Blo 346754 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B534034781 : Blo 346754 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B4864367 : Blo 346754 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B2505431 : Blo 346754 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B4471685 : Blo 346754 4471685 := bstep (se 4 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 4471685 = 838441) B838441
theorem B2374703 : Blo 346754 2374703 := bstep (se 1 (by rfl) ⟨1781027, by rfl⟩ : syracuseStep 2374703 = 3562055) B3562055
theorem B441551 : Blo 346754 441551 := bstep (se 1 (by rfl) ⟨331163, by rfl⟩ : syracuseStep 441551 = 662327) B662327
theorem B2244581 : Blo 346754 2244581 := bstep (se 4 (by rfl) ⟨210429, by rfl⟩ : syracuseStep 2244581 = 420859) B420859
theorem B1064951 : Blo 346754 1064951 := bstep (se 1 (by rfl) ⟨798713, by rfl⟩ : syracuseStep 1064951 = 1597427) B1597427
theorem B8896715 : Blo 346754 8896715 := bstep (se 1 (by rfl) ⟨6672536, by rfl⟩ : syracuseStep 8896715 = 13345073) B13345073
theorem B442847 : Blo 346754 442847 := bstep (se 1 (by rfl) ⟨332135, by rfl⟩ : syracuseStep 442847 = 664271) B664271
theorem B4244071 : Blo 346754 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B2245913 : Blo 346754 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B1983791 : Blo 346754 1983791 := bstep (se 1 (by rfl) ⟨1487843, by rfl⟩ : syracuseStep 1983791 = 2975687) B2975687
theorem B2245967 : Blo 346754 2245967 := bstep (se 1 (by rfl) ⟨1684475, by rfl⟩ : syracuseStep 2245967 = 3368951) B3368951
theorem B1328831 : Blo 346754 1328831 := bstep (se 1 (by rfl) ⟨996623, by rfl⟩ : syracuseStep 1328831 = 1993247) B1993247
theorem B12863897 : Blo 346754 12863897 := bstep (se 2 (by rfl) ⟨4823961, by rfl⟩ : syracuseStep 12863897 = 9647923) B9647923
theorem B7227967 : Blo 346754 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B2607839 : Blo 346754 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B1985249 : Blo 346754 1985249 := bstep (se 2 (by rfl) ⟨744468, by rfl⟩ : syracuseStep 1985249 = 1488937) B1488937
theorem B346879 : Blo 346754 346879 := bstep (se 1 (by rfl) ⟨260159, by rfl⟩ : syracuseStep 346879 = 520319) B520319
theorem B2018249 : Blo 346754 2018249 := bstep (se 2 (by rfl) ⟨756843, by rfl⟩ : syracuseStep 2018249 = 1513687) B1513687
theorem B3754997 : Blo 346754 3754997 := bstep (se 5 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 3754997 = 352031) B352031
theorem B347303 : Blo 346754 347303 := bstep (se 1 (by rfl) ⟨260477, by rfl⟩ : syracuseStep 347303 = 520955) B520955
theorem B347599 : Blo 346754 347599 := bstep (se 1 (by rfl) ⟨260699, by rfl⟩ : syracuseStep 347599 = 521399) B521399
theorem B347759 : Blo 346754 347759 := bstep (se 1 (by rfl) ⟨260819, by rfl⟩ : syracuseStep 347759 = 521639) B521639
theorem B1494713 : Blo 346754 1494713 := bstep (se 2 (by rfl) ⟨560517, by rfl⟩ : syracuseStep 1494713 = 1121035) B1121035
theorem B347879 : Blo 346754 347879 := bstep (se 1 (by rfl) ⟨260909, by rfl⟩ : syracuseStep 347879 = 521819) B521819
theorem B348187 : Blo 346754 348187 := bstep (se 1 (by rfl) ⟨261140, by rfl⟩ : syracuseStep 348187 = 522281) B522281
theorem B348207 : Blo 346754 348207 := bstep (se 1 (by rfl) ⟨261155, by rfl⟩ : syracuseStep 348207 = 522311) B522311
theorem B348463 : Blo 346754 348463 := bstep (se 1 (by rfl) ⟨261347, by rfl⟩ : syracuseStep 348463 = 522695) B522695
theorem B1757537 : Blo 346754 1757537 := bstep (se 2 (by rfl) ⟨659076, by rfl⟩ : syracuseStep 1757537 = 1318153) B1318153
theorem B741803 : Blo 346754 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B348607 : Blo 346754 348607 := bstep (se 1 (by rfl) ⟨261455, by rfl⟩ : syracuseStep 348607 = 522911) B522911
theorem B348703 : Blo 346754 348703 := bstep (se 1 (by rfl) ⟨261527, by rfl⟩ : syracuseStep 348703 = 523055) B523055
theorem B348783 : Blo 346754 348783 := bstep (se 1 (by rfl) ⟨261587, by rfl⟩ : syracuseStep 348783 = 523175) B523175
theorem B348903 : Blo 346754 348903 := bstep (se 1 (by rfl) ⟨261677, by rfl⟩ : syracuseStep 348903 = 523355) B523355
theorem B11326337 : Blo 346754 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B349151 : Blo 346754 349151 := bstep (se 1 (by rfl) ⟨261863, by rfl⟩ : syracuseStep 349151 = 523727) B523727
theorem B30626885 : Blo 346754 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B349407 : Blo 346754 349407 := bstep (se 1 (by rfl) ⟨262055, by rfl⟩ : syracuseStep 349407 = 524111) B524111
theorem B349487 : Blo 346754 349487 := bstep (se 1 (by rfl) ⟨262115, by rfl⟩ : syracuseStep 349487 = 524231) B524231
theorem B349727 : Blo 346754 349727 := bstep (se 1 (by rfl) ⟨262295, by rfl⟩ : syracuseStep 349727 = 524591) B524591
theorem B349887 : Blo 346754 349887 := bstep (se 1 (by rfl) ⟨262415, by rfl⟩ : syracuseStep 349887 = 524831) B524831
theorem B448583 : Blo 346754 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B350335 : Blo 346754 350335 := bstep (se 1 (by rfl) ⟨262751, by rfl⟩ : syracuseStep 350335 = 525503) B525503
theorem B18208961 : Blo 346754 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B350431 : Blo 346754 350431 := bstep (se 1 (by rfl) ⟨262823, by rfl⟩ : syracuseStep 350431 = 525647) B525647
theorem B350491 : Blo 346754 350491 := bstep (se 1 (by rfl) ⟨262868, by rfl⟩ : syracuseStep 350491 = 525737) B525737
theorem B350591 : Blo 346754 350591 := bstep (se 1 (by rfl) ⟨262943, by rfl⟩ : syracuseStep 350591 = 525887) B525887
theorem B350619 : Blo 346754 350619 := bstep (se 1 (by rfl) ⟨262964, by rfl⟩ : syracuseStep 350619 = 525929) B525929
theorem B810209 : Blo 346754 810209 := bstep (se 2 (by rfl) ⟨303828, by rfl⟩ : syracuseStep 810209 = 607657) B607657
theorem B2973023 : Blo 346754 2973023 := bstep (se 1 (by rfl) ⟨2229767, by rfl⟩ : syracuseStep 2973023 = 4459535) B4459535
theorem B1761263 : Blo 346754 1761263 := bstep (se 1 (by rfl) ⟨1320947, by rfl⟩ : syracuseStep 1761263 = 2641895) B2641895
theorem B1990763 : Blo 346754 1990763 := bstep (se 1 (by rfl) ⟨1493072, by rfl⟩ : syracuseStep 1990763 = 2986145) B2986145
theorem B1007741 : Blo 346754 1007741 := bstep (se 3 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 1007741 = 377903) B377903
theorem B1762073 : Blo 346754 1762073 := bstep (se 2 (by rfl) ⟨660777, by rfl⟩ : syracuseStep 1762073 = 1321555) B1321555
theorem B1008875 : Blo 346754 1008875 := bstep (se 1 (by rfl) ⟨756656, by rfl⟩ : syracuseStep 1008875 = 1513313) B1513313
theorem B714025 : Blo 346754 714025 := bstep (se 2 (by rfl) ⟨267759, by rfl⟩ : syracuseStep 714025 = 535519) B535519
theorem B877979 : Blo 346754 877979 := bstep (se 1 (by rfl) ⟨658484, by rfl⟩ : syracuseStep 877979 = 1316969) B1316969
theorem B746921 : Blo 346754 746921 := bstep (se 2 (by rfl) ⟨280095, by rfl⟩ : syracuseStep 746921 = 560191) B560191
theorem B780263 : Blo 346754 780263 := bstep (se 1 (by rfl) ⟨585197, by rfl⟩ : syracuseStep 780263 = 1170395) B1170395
theorem B780443 : Blo 346754 780443 := bstep (se 1 (by rfl) ⟨585332, by rfl⟩ : syracuseStep 780443 = 1170665) B1170665
theorem B780623 : Blo 346754 780623 := bstep (se 1 (by rfl) ⟨585467, by rfl⟩ : syracuseStep 780623 = 1170935) B1170935
theorem B878971 : Blo 346754 878971 := bstep (se 1 (by rfl) ⟨659228, by rfl⟩ : syracuseStep 878971 = 1318457) B1318457
theorem B780713 : Blo 346754 780713 := bstep (se 2 (by rfl) ⟨292767, by rfl⟩ : syracuseStep 780713 = 585535) B585535
theorem B1174283 : Blo 346754 1174283 := bstep (se 1 (by rfl) ⟨880712, by rfl⟩ : syracuseStep 1174283 = 1761425) B1761425
theorem B1993679 : Blo 346754 1993679 := bstep (se 1 (by rfl) ⟨1495259, by rfl⟩ : syracuseStep 1993679 = 2990519) B2990519
theorem B1174823 : Blo 346754 1174823 := bstep (se 1 (by rfl) ⟨881117, by rfl⟩ : syracuseStep 1174823 = 1762235) B1762235
theorem B2649671 : Blo 346754 2649671 := bstep (se 1 (by rfl) ⟨1987253, by rfl⟩ : syracuseStep 2649671 = 3974507) B3974507
theorem B880409 : Blo 346754 880409 := bstep (se 2 (by rfl) ⟨330153, by rfl⟩ : syracuseStep 880409 = 660307) B660307
theorem B520169 : Blo 346754 520169 := bstep (se 2 (by rfl) ⟨195063, by rfl⟩ : syracuseStep 520169 = 390127) B390127
theorem B520187 : Blo 346754 520187 := bstep (se 1 (by rfl) ⟨390140, by rfl⟩ : syracuseStep 520187 = 780281) B780281
theorem B520223 : Blo 346754 520223 := bstep (se 1 (by rfl) ⟨390167, by rfl⟩ : syracuseStep 520223 = 780335) B780335
theorem B2977823 : Blo 346754 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B520247 : Blo 346754 520247 := bstep (se 1 (by rfl) ⟨390185, by rfl⟩ : syracuseStep 520247 = 780371) B780371
theorem B520367 : Blo 346754 520367 := bstep (se 1 (by rfl) ⟨390275, by rfl⟩ : syracuseStep 520367 = 780551) B780551
theorem B1175795 : Blo 346754 1175795 := bstep (se 1 (by rfl) ⟨881846, by rfl⟩ : syracuseStep 1175795 = 1763693) B1763693
theorem B880915 : Blo 346754 880915 := bstep (se 1 (by rfl) ⟨660686, by rfl⟩ : syracuseStep 880915 = 1321373) B1321373
theorem B1175903 : Blo 346754 1175903 := bstep (se 1 (by rfl) ⟨881927, by rfl⟩ : syracuseStep 1175903 = 1763855) B1763855
theorem B520571 : Blo 346754 520571 := bstep (se 1 (by rfl) ⟨390428, by rfl⟩ : syracuseStep 520571 = 780857) B780857
theorem B520841 : Blo 346754 520841 := bstep (se 2 (by rfl) ⟨195315, by rfl⟩ : syracuseStep 520841 = 390631) B390631
theorem B521051 : Blo 346754 521051 := bstep (se 1 (by rfl) ⟨390788, by rfl⟩ : syracuseStep 521051 = 781577) B781577
theorem B521081 : Blo 346754 521081 := bstep (se 2 (by rfl) ⟨195405, by rfl⟩ : syracuseStep 521081 = 390811) B390811
theorem B881705 : Blo 346754 881705 := bstep (se 2 (by rfl) ⟨330639, by rfl⟩ : syracuseStep 881705 = 661279) B661279
theorem B586919 : Blo 346754 586919 := bstep (se 1 (by rfl) ⟨440189, by rfl⟩ : syracuseStep 586919 = 880379) B880379
theorem B3339731 : Blo 346754 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B521711 : Blo 346754 521711 := bstep (se 1 (by rfl) ⟨391283, by rfl⟩ : syracuseStep 521711 = 782567) B782567
theorem B521831 : Blo 346754 521831 := bstep (se 1 (by rfl) ⟨391373, by rfl⟩ : syracuseStep 521831 = 782747) B782747
theorem B1177415 : Blo 346754 1177415 := bstep (se 1 (by rfl) ⟨883061, by rfl⟩ : syracuseStep 1177415 = 1766123) B1766123
theorem B2521003 : Blo 346754 2521003 := bstep (se 1 (by rfl) ⟨1890752, by rfl⟩ : syracuseStep 2521003 = 3781505) B3781505
theorem B391135 : Blo 346754 391135 := bstep (se 1 (by rfl) ⟨293351, by rfl⟩ : syracuseStep 391135 = 586703) B586703
theorem B522287 : Blo 346754 522287 := bstep (se 1 (by rfl) ⟨391715, by rfl⟩ : syracuseStep 522287 = 783431) B783431
theorem B784439 : Blo 346754 784439 := bstep (se 1 (by rfl) ⟨588329, by rfl⟩ : syracuseStep 784439 = 1176659) B1176659
theorem B1177739 : Blo 346754 1177739 := bstep (se 1 (by rfl) ⟨883304, by rfl⟩ : syracuseStep 1177739 = 1766609) B1766609
theorem B522407 : Blo 346754 522407 := bstep (se 1 (by rfl) ⟨391805, by rfl⟩ : syracuseStep 522407 = 783611) B783611
theorem B1997095 : Blo 346754 1997095 := bstep (se 1 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 1997095 = 2995643) B2995643
theorem B522551 : Blo 346754 522551 := bstep (se 1 (by rfl) ⟨391913, by rfl⟩ : syracuseStep 522551 = 783827) B783827
theorem B784799 : Blo 346754 784799 := bstep (se 1 (by rfl) ⟨588599, by rfl⟩ : syracuseStep 784799 = 1177199) B1177199
theorem B1767905 : Blo 346754 1767905 := bstep (se 2 (by rfl) ⟨662964, by rfl⟩ : syracuseStep 1767905 = 1325929) B1325929
theorem B522731 : Blo 346754 522731 := bstep (se 1 (by rfl) ⟨392048, by rfl⟩ : syracuseStep 522731 = 784097) B784097
theorem B2521577 : Blo 346754 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B2226845 : Blo 346754 2226845 := bstep (se 3 (by rfl) ⟨417533, by rfl⟩ : syracuseStep 2226845 = 835067) B835067
theorem B3767107 : Blo 346754 3767107 := bstep (se 1 (by rfl) ⟨2825330, by rfl⟩ : syracuseStep 3767107 = 5650661) B5650661
theorem B523079 : Blo 346754 523079 := bstep (se 1 (by rfl) ⟨392309, by rfl⟩ : syracuseStep 523079 = 784619) B784619
theorem B785375 : Blo 346754 785375 := bstep (se 1 (by rfl) ⟨589031, by rfl⟩ : syracuseStep 785375 = 1178063) B1178063
theorem B1113115 : Blo 346754 1113115 := bstep (se 1 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 1113115 = 1669673) B1669673
theorem B1178657 : Blo 346754 1178657 := bstep (se 2 (by rfl) ⟨441996, by rfl⟩ : syracuseStep 1178657 = 883993) B883993
theorem B392287 : Blo 346754 392287 := bstep (se 1 (by rfl) ⟨294215, by rfl⟩ : syracuseStep 392287 = 588431) B588431
theorem B1768553 : Blo 346754 1768553 := bstep (se 2 (by rfl) ⟨663207, by rfl⟩ : syracuseStep 1768553 = 1326415) B1326415
theorem B883943 : Blo 346754 883943 := bstep (se 1 (by rfl) ⟨662957, by rfl⟩ : syracuseStep 883943 = 1325915) B1325915
theorem B785897 : Blo 346754 785897 := bstep (se 2 (by rfl) ⟨294711, by rfl⟩ : syracuseStep 785897 = 589423) B589423
theorem B523913 : Blo 346754 523913 := bstep (se 2 (by rfl) ⟨196467, by rfl⟩ : syracuseStep 523913 = 392935) B392935
theorem B523943 : Blo 346754 523943 := bstep (se 1 (by rfl) ⟨392957, by rfl⟩ : syracuseStep 523943 = 785915) B785915
theorem B1179359 : Blo 346754 1179359 := bstep (se 1 (by rfl) ⟨884519, by rfl⟩ : syracuseStep 1179359 = 1769039) B1769039
theorem B524063 : Blo 346754 524063 := bstep (se 1 (by rfl) ⟨393047, by rfl⟩ : syracuseStep 524063 = 786095) B786095
theorem B524123 : Blo 346754 524123 := bstep (se 1 (by rfl) ⟨393092, by rfl⟩ : syracuseStep 524123 = 786185) B786185
theorem B5931143 : Blo 346754 5931143 := bstep (se 1 (by rfl) ⟨4448357, by rfl⟩ : syracuseStep 5931143 = 8896715) B8896715
theorem B1409761 : Blo 346754 1409761 := bstep (se 2 (by rfl) ⟨528660, by rfl⟩ : syracuseStep 1409761 = 1057321) B1057321
theorem B525407 : Blo 346754 525407 := bstep (se 1 (by rfl) ⟨394055, by rfl⟩ : syracuseStep 525407 = 788111) B788111
theorem B885887 : Blo 346754 885887 := bstep (se 1 (by rfl) ⟨664415, by rfl⟩ : syracuseStep 885887 = 1328831) B1328831
theorem B525467 : Blo 346754 525467 := bstep (se 1 (by rfl) ⟨394100, by rfl⟩ : syracuseStep 525467 = 788201) B788201
theorem B1180925 : Blo 346754 1180925 := bstep (se 3 (by rfl) ⟨221423, by rfl⟩ : syracuseStep 1180925 = 442847) B442847
theorem B787769 : Blo 346754 787769 := bstep (se 2 (by rfl) ⟨295413, by rfl⟩ : syracuseStep 787769 = 590827) B590827
theorem B853319 : Blo 346754 853319 := bstep (se 1 (by rfl) ⟨639989, by rfl⟩ : syracuseStep 853319 = 1279979) B1279979
theorem B787967 : Blo 346754 787967 := bstep (se 1 (by rfl) ⟨590975, by rfl⟩ : syracuseStep 787967 = 1181951) B1181951
theorem B952033 : Blo 346754 952033 := bstep (se 2 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 952033 = 714025) B714025
theorem B1738559 : Blo 346754 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B1345499 : Blo 346754 1345499 := bstep (se 1 (by rfl) ⟨1009124, by rfl⟩ : syracuseStep 1345499 = 2018249) B2018249
theorem B4458563 : Blo 346754 4458563 := bstep (se 1 (by rfl) ⟨3343922, by rfl⟩ : syracuseStep 4458563 = 6687845) B6687845
theorem B658523 : Blo 346754 658523 := bstep (se 1 (by rfl) ⟨493892, by rfl⟩ : syracuseStep 658523 = 987785) B987785
theorem B20417923 : Blo 346754 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B9637289 : Blo 346754 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B21368357 : Blo 346754 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B921179 : Blo 346754 921179 := bstep (se 1 (by rfl) ⟨690884, by rfl⟩ : syracuseStep 921179 = 1381769) B1381769
theorem B3804833 : Blo 346754 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B1183625 : Blo 346754 1183625 := bstep (se 2 (by rfl) ⟨443859, by rfl⟩ : syracuseStep 1183625 = 887719) B887719
theorem B1183679 : Blo 346754 1183679 := bstep (se 1 (by rfl) ⟨887759, by rfl⟩ : syracuseStep 1183679 = 1775519) B1775519
theorem B594143 : Blo 346754 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B660793 : Blo 346754 660793 := bstep (se 2 (by rfl) ⟨247797, by rfl⟩ : syracuseStep 660793 = 495595) B495595
theorem B2233919 : Blo 346754 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B661135 : Blo 346754 661135 := bstep (se 1 (by rfl) ⟨495851, by rfl⟩ : syracuseStep 661135 = 991703) B991703
theorem B1317167 : Blo 346754 1317167 := bstep (se 1 (by rfl) ⟨987875, by rfl⟩ : syracuseStep 1317167 = 1975751) B1975751
theorem B6724205 : Blo 346754 6724205 := bstep (se 3 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 6724205 = 2521577) B2521577
theorem B662251 : Blo 346754 662251 := bstep (se 1 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 662251 = 993377) B993377
theorem B1317971 : Blo 346754 1317971 := bstep (se 1 (by rfl) ⟨988478, by rfl⟩ : syracuseStep 1317971 = 1976957) B1976957
theorem B5709403 : Blo 346754 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B3612647 : Blo 346754 3612647 := bstep (se 1 (by rfl) ⟨2709485, by rfl⟩ : syracuseStep 3612647 = 5418971) B5418971
theorem B1319111 : Blo 346754 1319111 := bstep (se 1 (by rfl) ⟨989333, by rfl⟩ : syracuseStep 1319111 = 1978667) B1978667
theorem B2662793 : Blo 346754 2662793 := bstep (se 2 (by rfl) ⟨998547, by rfl⟩ : syracuseStep 2662793 = 1997095) B1997095
theorem B1319915 : Blo 346754 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B5022809 : Blo 346754 5022809 := bstep (se 2 (by rfl) ⟨1883553, by rfl⟩ : syracuseStep 5022809 = 3767107) B3767107
theorem B1320097 : Blo 346754 1320097 := bstep (se 2 (by rfl) ⟨495036, by rfl⟩ : syracuseStep 1320097 = 990073) B990073
theorem B2991269 : Blo 346754 2991269 := bstep (se 4 (by rfl) ⟨280431, by rfl⟩ : syracuseStep 2991269 = 560863) B560863
theorem B1484153 : Blo 346754 1484153 := bstep (se 2 (by rfl) ⟨556557, by rfl⟩ : syracuseStep 1484153 = 1113115) B1113115
theorem B1484563 : Blo 346754 1484563 := bstep (se 1 (by rfl) ⟨1113422, by rfl⟩ : syracuseStep 1484563 = 2226845) B2226845
theorem B1583135 : Blo 346754 1583135 := bstep (se 1 (by rfl) ⟨1187351, by rfl⟩ : syracuseStep 1583135 = 2374703) B2374703
theorem B1058953 : Blo 346754 1058953 := bstep (se 2 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 1058953 = 794215) B794215
theorem B7940861 : Blo 346754 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B502895 : Blo 346754 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B8039735 : Blo 346754 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B1322527 : Blo 346754 1322527 := bstep (se 1 (by rfl) ⟨991895, by rfl⟩ : syracuseStep 1322527 = 1983791) B1983791
theorem B1978141 : Blo 346754 1978141 := bstep (se 3 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 1978141 = 741803) B741803
theorem B5681279 : Blo 346754 5681279 := bstep (se 1 (by rfl) ⟨4260959, by rfl⟩ : syracuseStep 5681279 = 8521919) B8521919
theorem B1683899 : Blo 346754 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B1323499 : Blo 346754 1323499 := bstep (se 1 (by rfl) ⟨992624, by rfl⟩ : syracuseStep 1323499 = 1985249) B1985249
theorem B2503331 : Blo 346754 2503331 := bstep (se 1 (by rfl) ⟨1877498, by rfl⟩ : syracuseStep 2503331 = 3754997) B3754997
theorem B996475 : Blo 346754 996475 := bstep (se 1 (by rfl) ⟨747356, by rfl⟩ : syracuseStep 996475 = 1494713) B1494713
theorem B7550891 : Blo 346754 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B2013817 : Blo 346754 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B12139307 : Blo 346754 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B5028803 : Blo 346754 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B1982015 : Blo 346754 1982015 := bstep (se 1 (by rfl) ⟨1486511, by rfl⟩ : syracuseStep 1982015 = 2973023) B2973023
theorem B3358685 : Blo 346754 3358685 := bstep (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) B1259507
theorem B1327175 : Blo 346754 1327175 := bstep (se 1 (by rfl) ⟨995381, by rfl⟩ : syracuseStep 1327175 = 1990763) B1990763
theorem B671827 : Blo 346754 671827 := bstep (se 1 (by rfl) ⟨503870, by rfl⟩ : syracuseStep 671827 = 1007741) B1007741
theorem B1196221 : Blo 346754 1196221 := bstep (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) B448583
theorem B3784967 : Blo 346754 3784967 := bstep (se 1 (by rfl) ⟨2838725, by rfl⟩ : syracuseStep 3784967 = 5677451) B5677451
theorem B672583 : Blo 346754 672583 := bstep (se 1 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 672583 = 1008875) B1008875
theorem B2868979 : Blo 346754 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B1329119 : Blo 346754 1329119 := bstep (se 1 (by rfl) ⟨996839, by rfl⟩ : syracuseStep 1329119 = 1993679) B1993679
theorem B706811 : Blo 346754 706811 := bstep (se 1 (by rfl) ⟨530108, by rfl⟩ : syracuseStep 706811 = 1060217) B1060217
theorem B3361337 : Blo 346754 3361337 := bstep (se 2 (by rfl) ⟨1260501, by rfl⟩ : syracuseStep 3361337 = 2521003) B2521003
theorem B1329817 : Blo 346754 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B346779 : Blo 346754 346779 := bstep (se 1 (by rfl) ⟨260084, by rfl⟩ : syracuseStep 346779 = 520169) B520169
theorem B346791 : Blo 346754 346791 := bstep (se 1 (by rfl) ⟨260093, by rfl⟩ : syracuseStep 346791 = 520187) B520187
theorem B346815 : Blo 346754 346815 := bstep (se 1 (by rfl) ⟨260111, by rfl⟩ : syracuseStep 346815 = 520223) B520223
theorem B346831 : Blo 346754 346831 := bstep (se 1 (by rfl) ⟨260123, by rfl⟩ : syracuseStep 346831 = 520247) B520247
theorem B346911 : Blo 346754 346911 := bstep (se 1 (by rfl) ⟨260183, by rfl⟩ : syracuseStep 346911 = 520367) B520367
theorem B347047 : Blo 346754 347047 := bstep (se 1 (by rfl) ⟨260285, by rfl⟩ : syracuseStep 347047 = 520571) B520571
theorem B347227 : Blo 346754 347227 := bstep (se 1 (by rfl) ⟨260420, by rfl⟩ : syracuseStep 347227 = 520841) B520841
theorem B347367 : Blo 346754 347367 := bstep (se 1 (by rfl) ⟨260525, by rfl⟩ : syracuseStep 347367 = 521051) B521051
theorem B347387 : Blo 346754 347387 := bstep (se 1 (by rfl) ⟨260540, by rfl⟩ : syracuseStep 347387 = 521081) B521081
theorem B708239 : Blo 346754 708239 := bstep (se 1 (by rfl) ⟨531179, by rfl⟩ : syracuseStep 708239 = 1062359) B1062359
theorem B347807 : Blo 346754 347807 := bstep (se 1 (by rfl) ⟨260855, by rfl⟩ : syracuseStep 347807 = 521711) B521711
theorem B347887 : Blo 346754 347887 := bstep (se 1 (by rfl) ⟨260915, by rfl⟩ : syracuseStep 347887 = 521831) B521831
theorem B10735415 : Blo 346754 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B348191 : Blo 346754 348191 := bstep (se 1 (by rfl) ⟨261143, by rfl⟩ : syracuseStep 348191 = 522287) B522287
theorem B348271 : Blo 346754 348271 := bstep (se 1 (by rfl) ⟨261203, by rfl⟩ : syracuseStep 348271 = 522407) B522407
theorem B348367 : Blo 346754 348367 := bstep (se 1 (by rfl) ⟨261275, by rfl⟩ : syracuseStep 348367 = 522551) B522551
theorem B839911 : Blo 346754 839911 := bstep (se 1 (by rfl) ⟨629933, by rfl⟩ : syracuseStep 839911 = 1259867) B1259867
theorem B708839 : Blo 346754 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B348487 : Blo 346754 348487 := bstep (se 1 (by rfl) ⟨261365, by rfl⟩ : syracuseStep 348487 = 522731) B522731
theorem B348719 : Blo 346754 348719 := bstep (se 1 (by rfl) ⟨261539, by rfl⟩ : syracuseStep 348719 = 523079) B523079
theorem B349275 : Blo 346754 349275 := bstep (se 1 (by rfl) ⟨261956, by rfl⟩ : syracuseStep 349275 = 523913) B523913
theorem B349295 : Blo 346754 349295 := bstep (se 1 (by rfl) ⟨261971, by rfl⟩ : syracuseStep 349295 = 523943) B523943
theorem B349375 : Blo 346754 349375 := bstep (se 1 (by rfl) ⟨262031, by rfl⟩ : syracuseStep 349375 = 524063) B524063
theorem B349415 : Blo 346754 349415 := bstep (se 1 (by rfl) ⟨262061, by rfl⟩ : syracuseStep 349415 = 524123) B524123
theorem B1496387 : Blo 346754 1496387 := bstep (se 1 (by rfl) ⟨1122290, by rfl⟩ : syracuseStep 1496387 = 2244581) B2244581
theorem B709967 : Blo 346754 709967 := bstep (se 1 (by rfl) ⟨532475, by rfl⟩ : syracuseStep 709967 = 1064951) B1064951
theorem B349695 : Blo 346754 349695 := bstep (se 1 (by rfl) ⟨262271, by rfl⟩ : syracuseStep 349695 = 524543) B524543
theorem B349799 : Blo 346754 349799 := bstep (se 1 (by rfl) ⟨262349, by rfl⟩ : syracuseStep 349799 = 524699) B524699
theorem B1890145 : Blo 346754 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B350079 : Blo 346754 350079 := bstep (se 1 (by rfl) ⟨262559, by rfl⟩ : syracuseStep 350079 = 525119) B525119
theorem B350175 : Blo 346754 350175 := bstep (se 1 (by rfl) ⟨262631, by rfl⟩ : syracuseStep 350175 = 525263) B525263
theorem B350235 : Blo 346754 350235 := bstep (se 1 (by rfl) ⟨262676, by rfl⟩ : syracuseStep 350235 = 525353) B525353
theorem B350255 : Blo 346754 350255 := bstep (se 1 (by rfl) ⟨262691, by rfl⟩ : syracuseStep 350255 = 525383) B525383
theorem B5658761 : Blo 346754 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B350375 : Blo 346754 350375 := bstep (se 1 (by rfl) ⟨262781, by rfl⟩ : syracuseStep 350375 = 525563) B525563
theorem B1497275 : Blo 346754 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B1497311 : Blo 346754 1497311 := bstep (se 1 (by rfl) ⟨1122983, by rfl⟩ : syracuseStep 1497311 = 2245967) B2245967
theorem B350567 : Blo 346754 350567 := bstep (se 1 (by rfl) ⟨262925, by rfl⟩ : syracuseStep 350567 = 525851) B525851
theorem B8575931 : Blo 346754 8575931 := bstep (se 1 (by rfl) ⟨6431948, by rfl⟩ : syracuseStep 8575931 = 12863897) B12863897
theorem B2448953 : Blo 346754 2448953 := bstep (se 2 (by rfl) ⟨918357, by rfl⟩ : syracuseStep 2448953 = 1836715) B1836715
theorem B2383789 : Blo 346754 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B1171691 : Blo 346754 1171691 := bstep (se 1 (by rfl) ⟨878768, by rfl⟩ : syracuseStep 1171691 = 1757537) B1757537
theorem B2646269 : Blo 346754 2646269 := bstep (se 3 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 2646269 = 992351) B992351
theorem B1171961 : Blo 346754 1171961 := bstep (se 2 (by rfl) ⟨439485, by rfl⟩ : syracuseStep 1171961 = 878971) B878971
theorem B2515643 : Blo 346754 2515643 := bstep (se 1 (by rfl) ⟨1886732, by rfl⟩ : syracuseStep 2515643 = 3773465) B3773465
theorem B1991789 : Blo 346754 1991789 := bstep (se 3 (by rfl) ⟨373460, by rfl⟩ : syracuseStep 1991789 = 746921) B746921
theorem B1992539 : Blo 346754 1992539 := bstep (se 1 (by rfl) ⟨1494404, by rfl⟩ : syracuseStep 1992539 = 2988809) B2988809
theorem B8513437 : Blo 346754 8513437 := bstep (se 3 (by rfl) ⟨1596269, by rfl⟩ : syracuseStep 8513437 = 3192539) B3192539
theorem B1174013 : Blo 346754 1174013 := bstep (se 3 (by rfl) ⟨220127, by rfl⟩ : syracuseStep 1174013 = 440255) B440255
theorem B1174175 : Blo 346754 1174175 := bstep (se 1 (by rfl) ⟨880631, by rfl⟩ : syracuseStep 1174175 = 1761263) B1761263
theorem B1174553 : Blo 346754 1174553 := bstep (se 2 (by rfl) ⟨440457, by rfl⟩ : syracuseStep 1174553 = 880915) B880915
theorem B3959927 : Blo 346754 3959927 := bstep (se 1 (by rfl) ⟨2969945, by rfl⟩ : syracuseStep 3959927 = 5939891) B5939891
theorem B1174715 : Blo 346754 1174715 := bstep (se 1 (by rfl) ⟨881036, by rfl⟩ : syracuseStep 1174715 = 1762073) B1762073
theorem B585319 : Blo 346754 585319 := bstep (se 1 (by rfl) ⟨438989, by rfl⟩ : syracuseStep 585319 = 877979) B877979
theorem B520175 : Blo 346754 520175 := bstep (se 1 (by rfl) ⟨390131, by rfl⟩ : syracuseStep 520175 = 780263) B780263
theorem B520295 : Blo 346754 520295 := bstep (se 1 (by rfl) ⟨390221, by rfl⟩ : syracuseStep 520295 = 780443) B780443
theorem B520415 : Blo 346754 520415 := bstep (se 1 (by rfl) ⟨390311, by rfl⟩ : syracuseStep 520415 = 780623) B780623
theorem B880865 : Blo 346754 880865 := bstep (se 2 (by rfl) ⟨330324, by rfl⟩ : syracuseStep 880865 = 660649) B660649
theorem B520475 : Blo 346754 520475 := bstep (se 1 (by rfl) ⟨390356, by rfl⟩ : syracuseStep 520475 = 780713) B780713
theorem B782855 : Blo 346754 782855 := bstep (se 1 (by rfl) ⟨587141, by rfl⟩ : syracuseStep 782855 = 1174283) B1174283
theorem B6681149 : Blo 346754 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B4223735 : Blo 346754 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B783215 : Blo 346754 783215 := bstep (se 1 (by rfl) ⟨587411, by rfl⟩ : syracuseStep 783215 = 1174823) B1174823
theorem B1766447 : Blo 346754 1766447 := bstep (se 1 (by rfl) ⟨1324835, by rfl⟩ : syracuseStep 1766447 = 2649671) B2649671
theorem B1504337 : Blo 346754 1504337 := bstep (se 2 (by rfl) ⟨564126, by rfl⟩ : syracuseStep 1504337 = 1128253) B1128253
theorem B1995911 : Blo 346754 1995911 := bstep (se 1 (by rfl) ⟨1496933, by rfl⟩ : syracuseStep 1995911 = 2993867) B2993867
theorem B586939 : Blo 346754 586939 := bstep (se 1 (by rfl) ⟨440204, by rfl⟩ : syracuseStep 586939 = 880409) B880409
theorem B521513 : Blo 346754 521513 := bstep (se 2 (by rfl) ⟨195567, by rfl⟩ : syracuseStep 521513 = 391135) B391135
theorem B783863 : Blo 346754 783863 := bstep (se 1 (by rfl) ⟨587897, by rfl⟩ : syracuseStep 783863 = 1175795) B1175795
theorem B783935 : Blo 346754 783935 := bstep (se 1 (by rfl) ⟨587951, by rfl⟩ : syracuseStep 783935 = 1175903) B1175903
theorem B1177469 : Blo 346754 1177469 := bstep (se 3 (by rfl) ⟨220775, by rfl⟩ : syracuseStep 1177469 = 441551) B441551
theorem B2160557 : Blo 346754 2160557 := bstep (se 3 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 2160557 = 810209) B810209
theorem B1406909 : Blo 346754 1406909 := bstep (se 3 (by rfl) ⟨263795, by rfl⟩ : syracuseStep 1406909 = 527591) B527591
theorem B587803 : Blo 346754 587803 := bstep (se 1 (by rfl) ⟨440852, by rfl⟩ : syracuseStep 587803 = 881705) B881705
theorem B391279 : Blo 346754 391279 := bstep (se 1 (by rfl) ⟨293459, by rfl⟩ : syracuseStep 391279 = 586919) B586919
theorem B882809 : Blo 346754 882809 := bstep (se 2 (by rfl) ⟨331053, by rfl⟩ : syracuseStep 882809 = 662107) B662107
theorem B2226487 : Blo 346754 2226487 := bstep (se 1 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 2226487 = 3339731) B3339731
theorem B784943 : Blo 346754 784943 := bstep (se 1 (by rfl) ⟨588707, by rfl⟩ : syracuseStep 784943 = 1177415) B1177415
theorem B522959 : Blo 346754 522959 := bstep (se 1 (by rfl) ⟨392219, by rfl⟩ : syracuseStep 522959 = 784439) B784439
theorem B785159 : Blo 346754 785159 := bstep (se 1 (by rfl) ⟨588869, by rfl⟩ : syracuseStep 785159 = 1177739) B1177739
theorem B523049 : Blo 346754 523049 := bstep (se 2 (by rfl) ⟨196143, by rfl⟩ : syracuseStep 523049 = 392287) B392287
theorem B356023187 : Blo 346754 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B3242911 : Blo 346754 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B523199 : Blo 346754 523199 := bstep (se 1 (by rfl) ⟨392399, by rfl⟩ : syracuseStep 523199 = 784799) B784799
theorem B1178603 : Blo 346754 1178603 := bstep (se 1 (by rfl) ⟨883952, by rfl⟩ : syracuseStep 1178603 = 1767905) B1767905
theorem B2981123 : Blo 346754 2981123 := bstep (se 1 (by rfl) ⟨2235842, by rfl⟩ : syracuseStep 2981123 = 4471685) B4471685
theorem B523583 : Blo 346754 523583 := bstep (se 1 (by rfl) ⟨392687, by rfl⟩ : syracuseStep 523583 = 785375) B785375
theorem B785771 : Blo 346754 785771 := bstep (se 1 (by rfl) ⟨589328, by rfl⟩ : syracuseStep 785771 = 1178657) B1178657
theorem B1179035 : Blo 346754 1179035 := bstep (se 1 (by rfl) ⟨884276, by rfl⟩ : syracuseStep 1179035 = 1768553) B1768553
theorem B589295 : Blo 346754 589295 := bstep (se 1 (by rfl) ⟨441971, by rfl⟩ : syracuseStep 589295 = 883943) B883943
theorem B523931 : Blo 346754 523931 := bstep (se 1 (by rfl) ⟨392948, by rfl⟩ : syracuseStep 523931 = 785897) B785897
theorem B786239 : Blo 346754 786239 := bstep (se 1 (by rfl) ⟨589679, by rfl⟩ : syracuseStep 786239 = 1179359) B1179359
theorem B884783 : Blo 346754 884783 := bstep (se 1 (by rfl) ⟨663587, by rfl⟩ : syracuseStep 884783 = 1327175) B1327175
theorem B2523311 : Blo 346754 2523311 := bstep (se 1 (by rfl) ⟨1892483, by rfl⟩ : syracuseStep 2523311 = 3784967) B3784967
theorem B590591 : Blo 346754 590591 := bstep (se 1 (by rfl) ⟨442943, by rfl⟩ : syracuseStep 590591 = 885887) B885887
theorem B787283 : Blo 346754 787283 := bstep (se 1 (by rfl) ⟨590462, by rfl⟩ : syracuseStep 787283 = 1180925) B1180925
theorem B525179 : Blo 346754 525179 := bstep (se 1 (by rfl) ⟨393884, by rfl⟩ : syracuseStep 525179 = 787769) B787769
theorem B525311 : Blo 346754 525311 := bstep (se 1 (by rfl) ⟨393983, by rfl⟩ : syracuseStep 525311 = 787967) B787967
theorem B886079 : Blo 346754 886079 := bstep (se 1 (by rfl) ⟨664559, by rfl⟩ : syracuseStep 886079 = 1329119) B1329119
theorem B6424859 : Blo 346754 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B789083 : Blo 346754 789083 := bstep (se 1 (by rfl) ⟨591812, by rfl⟩ : syracuseStep 789083 = 1183625) B1183625
theorem B789119 : Blo 346754 789119 := bstep (se 1 (by rfl) ⟨591839, by rfl⟩ : syracuseStep 789119 = 1183679) B1183679
theorem B396095 : Blo 346754 396095 := bstep (se 1 (by rfl) ⟨297071, by rfl⟩ : syracuseStep 396095 = 594143) B594143
theorem B1411937 : Blo 346754 1411937 := bstep (se 2 (by rfl) ⟨529476, by rfl⟩ : syracuseStep 1411937 = 1058953) B1058953
theorem B1773089 : Blo 346754 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B3772507 : Blo 346754 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B1775195 : Blo 346754 1775195 := bstep (se 1 (by rfl) ⟨1331396, by rfl⟩ : syracuseStep 1775195 = 2662793) B2662793
theorem B1119881 : Blo 346754 1119881 := bstep (se 2 (by rfl) ⟨419955, by rfl⟩ : syracuseStep 1119881 = 839911) B839911
theorem B1677095 : Blo 346754 1677095 := bstep (se 1 (by rfl) ⟨1257821, by rfl⟩ : syracuseStep 1677095 = 2515643) B2515643
theorem B3348539 : Blo 346754 3348539 := bstep (se 1 (by rfl) ⟨2511404, by rfl⟩ : syracuseStep 3348539 = 5022809) B5022809
theorem B989435 : Blo 346754 989435 := bstep (se 1 (by rfl) ⟨742076, by rfl⟩ : syracuseStep 989435 = 1484153) B1484153
theorem B1055423 : Blo 346754 1055423 := bstep (se 1 (by rfl) ⟨791567, by rfl⟩ : syracuseStep 1055423 = 1583135) B1583135
theorem B1122599 : Blo 346754 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B237348791 : Blo 346754 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B3352535 : Blo 346754 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B7612537 : Blo 346754 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B1321343 : Blo 346754 1321343 := bstep (se 1 (by rfl) ⟨991007, by rfl⟩ : syracuseStep 1321343 = 1982015) B1982015
theorem B2239123 : Blo 346754 2239123 := bstep (se 1 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 2239123 = 3358685) B3358685
theorem B895769 : Blo 346754 895769 := bstep (se 2 (by rfl) ⟨335913, by rfl⟩ : syracuseStep 895769 = 671827) B671827
theorem B568879 : Blo 346754 568879 := bstep (se 1 (by rfl) ⟨426659, by rfl⟩ : syracuseStep 568879 = 853319) B853319
theorem B1879681 : Blo 346754 1879681 := bstep (se 2 (by rfl) ⟨704880, by rfl⟩ : syracuseStep 1879681 = 1409761) B1409761
theorem B896777 : Blo 346754 896777 := bstep (se 2 (by rfl) ⟨336291, by rfl⟩ : syracuseStep 896777 = 672583) B672583
theorem B1159039 : Blo 346754 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B896999 : Blo 346754 896999 := bstep (se 1 (by rfl) ⟨672749, by rfl⟩ : syracuseStep 896999 = 1345499) B1345499
theorem B2240891 : Blo 346754 2240891 := bstep (se 1 (by rfl) ⟨1680668, by rfl⟩ : syracuseStep 2240891 = 3361337) B3361337
theorem B439015 : Blo 346754 439015 := bstep (se 1 (by rfl) ⟨329261, by rfl⟩ : syracuseStep 439015 = 658523) B658523
theorem B1979417 : Blo 346754 1979417 := bstep (se 2 (by rfl) ⟨742281, by rfl⟩ : syracuseStep 1979417 = 1484563) B1484563
theorem B472159 : Blo 346754 472159 := bstep (se 1 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 472159 = 708239) B708239
theorem B2536555 : Blo 346754 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B7156943 : Blo 346754 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B11351249 : Blo 346754 11351249 := bstep (se 2 (by rfl) ⟨4256718, by rfl⟩ : syracuseStep 11351249 = 8513437) B8513437
theorem B472559 : Blo 346754 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B997591 : Blo 346754 997591 := bstep (se 1 (by rfl) ⟨748193, by rfl⟩ : syracuseStep 997591 = 1496387) B1496387
theorem B473311 : Blo 346754 473311 := bstep (se 1 (by rfl) ⟨354983, by rfl⟩ : syracuseStep 473311 = 709967) B709967
theorem B1489279 : Blo 346754 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B998183 : Blo 346754 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B998207 : Blo 346754 998207 := bstep (se 1 (by rfl) ⟨748655, by rfl⟩ : syracuseStep 998207 = 1497311) B1497311
theorem B5717287 : Blo 346754 5717287 := bstep (se 1 (by rfl) ⟨4287965, by rfl⟩ : syracuseStep 5717287 = 8575931) B8575931
theorem B2637521 : Blo 346754 2637521 := bstep (se 2 (by rfl) ⟨989070, by rfl⟩ : syracuseStep 2637521 = 1978141) B1978141
theorem B1884829 : Blo 346754 1884829 := bstep (se 3 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 1884829 = 706811) B706811
theorem B1327859 : Blo 346754 1327859 := bstep (se 1 (by rfl) ⟨995894, by rfl⟩ : syracuseStep 1327859 = 1991789) B1991789
theorem B1328359 : Blo 346754 1328359 := bstep (se 1 (by rfl) ⟨996269, by rfl⟩ : syracuseStep 1328359 = 1992539) B1992539
theorem B1328633 : Blo 346754 1328633 := bstep (se 2 (by rfl) ⟨498237, by rfl⟩ : syracuseStep 1328633 = 996475) B996475
theorem B5293907 : Blo 346754 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B2639951 : Blo 346754 2639951 := bstep (se 1 (by rfl) ⟨1979963, by rfl⟩ : syracuseStep 2639951 = 3959927) B3959927
theorem B5359823 : Blo 346754 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B346783 : Blo 346754 346783 := bstep (se 1 (by rfl) ⟨260087, by rfl⟩ : syracuseStep 346783 = 520175) B520175
theorem B346863 : Blo 346754 346863 := bstep (se 1 (by rfl) ⟨260147, by rfl⟩ : syracuseStep 346863 = 520295) B520295
theorem B3787519 : Blo 346754 3787519 := bstep (se 1 (by rfl) ⟨2840639, by rfl⟩ : syracuseStep 3787519 = 5681279) B5681279
theorem B346943 : Blo 346754 346943 := bstep (se 1 (by rfl) ⟨260207, by rfl⟩ : syracuseStep 346943 = 520415) B520415
theorem B346983 : Blo 346754 346983 := bstep (se 1 (by rfl) ⟨260237, by rfl⟩ : syracuseStep 346983 = 520475) B520475
theorem B2968649 : Blo 346754 2968649 := bstep (se 2 (by rfl) ⟨1113243, by rfl⟩ : syracuseStep 2968649 = 2226487) B2226487
theorem B1330607 : Blo 346754 1330607 := bstep (se 1 (by rfl) ⟨997955, by rfl⟩ : syracuseStep 1330607 = 1995911) B1995911
theorem B347675 : Blo 346754 347675 := bstep (se 1 (by rfl) ⟨260756, by rfl⟩ : syracuseStep 347675 = 521513) B521513
theorem B5033927 : Blo 346754 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B937939 : Blo 346754 937939 := bstep (se 1 (by rfl) ⟨703454, by rfl⟩ : syracuseStep 937939 = 1406909) B1406909
theorem B348639 : Blo 346754 348639 := bstep (se 1 (by rfl) ⟨261479, by rfl⟩ : syracuseStep 348639 = 522959) B522959
theorem B10080773 : Blo 346754 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B348699 : Blo 346754 348699 := bstep (se 1 (by rfl) ⟨261524, by rfl⟩ : syracuseStep 348699 = 523049) B523049
theorem B348799 : Blo 346754 348799 := bstep (se 1 (by rfl) ⟨261599, by rfl⟩ : syracuseStep 348799 = 523199) B523199
theorem B1987415 : Blo 346754 1987415 := bstep (se 1 (by rfl) ⟨1490561, by rfl⟩ : syracuseStep 1987415 = 2981123) B2981123
theorem B349055 : Blo 346754 349055 := bstep (se 1 (by rfl) ⟨261791, by rfl⟩ : syracuseStep 349055 = 523583) B523583
theorem B349287 : Blo 346754 349287 := bstep (se 1 (by rfl) ⟨261965, by rfl⟩ : syracuseStep 349287 = 523931) B523931
theorem B3954095 : Blo 346754 3954095 := bstep (se 1 (by rfl) ⟨2965571, by rfl⟩ : syracuseStep 3954095 = 5931143) B5931143
theorem B1594961 : Blo 346754 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B350271 : Blo 346754 350271 := bstep (se 1 (by rfl) ⟨262703, by rfl⟩ : syracuseStep 350271 = 525407) B525407
theorem B350311 : Blo 346754 350311 := bstep (se 1 (by rfl) ⟨262733, by rfl⟩ : syracuseStep 350311 = 525467) B525467
theorem B16046261 : Blo 346754 16046261 := bstep (se 5 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 16046261 = 1504337) B1504337
theorem B2972375 : Blo 346754 2972375 := bstep (se 1 (by rfl) ⟨2229281, by rfl⟩ : syracuseStep 2972375 = 4458563) B4458563
theorem B1760129 : Blo 346754 1760129 := bstep (se 2 (by rfl) ⟨660048, by rfl⟩ : syracuseStep 1760129 = 1320097) B1320097
theorem B1269377 : Blo 346754 1269377 := bstep (se 2 (by rfl) ⟨476016, by rfl⟩ : syracuseStep 1269377 = 952033) B952033
theorem B3825305 : Blo 346754 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B14245571 : Blo 346754 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B878111 : Blo 346754 878111 := bstep (se 1 (by rfl) ⟨658583, by rfl⟩ : syracuseStep 878111 = 1317167) B1317167
theorem B4482803 : Blo 346754 4482803 := bstep (se 1 (by rfl) ⟨3362102, by rfl⟩ : syracuseStep 4482803 = 6724205) B6724205
theorem B27223897 : Blo 346754 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B1763369 : Blo 346754 1763369 := bstep (se 2 (by rfl) ⟨661263, by rfl⟩ : syracuseStep 1763369 = 1322527) B1322527
theorem B878647 : Blo 346754 878647 := bstep (se 1 (by rfl) ⟨658985, by rfl⟩ : syracuseStep 878647 = 1317971) B1317971
theorem B780425 : Blo 346754 780425 := bstep (se 2 (by rfl) ⟨292659, by rfl⟩ : syracuseStep 780425 = 585319) B585319
theorem B1632635 : Blo 346754 1632635 := bstep (se 1 (by rfl) ⟨1224476, by rfl⟩ : syracuseStep 1632635 = 2448953) B2448953
theorem B879407 : Blo 346754 879407 := bstep (se 1 (by rfl) ⟨659555, by rfl⟩ : syracuseStep 879407 = 1319111) B1319111
theorem B781127 : Blo 346754 781127 := bstep (se 1 (by rfl) ⟨585845, by rfl⟩ : syracuseStep 781127 = 1171691) B1171691
theorem B1764179 : Blo 346754 1764179 := bstep (se 1 (by rfl) ⟨1323134, by rfl⟩ : syracuseStep 1764179 = 2646269) B2646269
theorem B781307 : Blo 346754 781307 := bstep (se 1 (by rfl) ⟨585980, by rfl⟩ : syracuseStep 781307 = 1171961) B1171961
theorem B1764665 : Blo 346754 1764665 := bstep (se 2 (by rfl) ⟨661749, by rfl⟩ : syracuseStep 1764665 = 1323499) B1323499
theorem B879943 : Blo 346754 879943 := bstep (se 1 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 879943 = 1319915) B1319915
theorem B1994179 : Blo 346754 1994179 := bstep (se 1 (by rfl) ⟨1495634, by rfl⟩ : syracuseStep 1994179 = 2991269) B2991269
theorem B782585 : Blo 346754 782585 := bstep (se 2 (by rfl) ⟨293469, by rfl⟩ : syracuseStep 782585 = 586939) B586939
theorem B782675 : Blo 346754 782675 := bstep (se 1 (by rfl) ⟨587006, by rfl⟩ : syracuseStep 782675 = 1174013) B1174013
theorem B881057 : Blo 346754 881057 := bstep (se 2 (by rfl) ⟨330396, by rfl⟩ : syracuseStep 881057 = 660793) B660793
theorem B782783 : Blo 346754 782783 := bstep (se 1 (by rfl) ⟨587087, by rfl⟩ : syracuseStep 782783 = 1174175) B1174175
theorem B783035 : Blo 346754 783035 := bstep (se 1 (by rfl) ⟨587276, by rfl⟩ : syracuseStep 783035 = 1174553) B1174553
theorem B783143 : Blo 346754 783143 := bstep (se 1 (by rfl) ⟨587357, by rfl⟩ : syracuseStep 783143 = 1174715) B1174715
theorem B881513 : Blo 346754 881513 := bstep (se 2 (by rfl) ⟨330567, by rfl⟩ : syracuseStep 881513 = 661135) B661135
theorem B783737 : Blo 346754 783737 := bstep (se 2 (by rfl) ⟨293901, by rfl⟩ : syracuseStep 783737 = 587803) B587803
theorem B521705 : Blo 346754 521705 := bstep (se 2 (by rfl) ⟨195639, by rfl⟩ : syracuseStep 521705 = 391279) B391279
theorem B587243 : Blo 346754 587243 := bstep (se 1 (by rfl) ⟨440432, by rfl⟩ : syracuseStep 587243 = 880865) B880865
theorem B1341053 : Blo 346754 1341053 := bstep (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) B502895
theorem B521903 : Blo 346754 521903 := bstep (se 1 (by rfl) ⟨391427, by rfl⟩ : syracuseStep 521903 = 782855) B782855
theorem B4454099 : Blo 346754 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B1668887 : Blo 346754 1668887 := bstep (se 1 (by rfl) ⟨1251665, by rfl⟩ : syracuseStep 1668887 = 2503331) B2503331
theorem B2815823 : Blo 346754 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B522143 : Blo 346754 522143 := bstep (se 1 (by rfl) ⟨391607, by rfl⟩ : syracuseStep 522143 = 783215) B783215
theorem B1177631 : Blo 346754 1177631 := bstep (se 1 (by rfl) ⟨883223, by rfl⟩ : syracuseStep 1177631 = 1766447) B1766447
theorem B2685089 : Blo 346754 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B883001 : Blo 346754 883001 := bstep (se 2 (by rfl) ⟨331125, by rfl⟩ : syracuseStep 883001 = 662251) B662251
theorem B522575 : Blo 346754 522575 := bstep (se 1 (by rfl) ⟨391931, by rfl⟩ : syracuseStep 522575 = 783863) B783863
theorem B522623 : Blo 346754 522623 := bstep (se 1 (by rfl) ⟨391967, by rfl⟩ : syracuseStep 522623 = 783935) B783935
theorem B4323881 : Blo 346754 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B784979 : Blo 346754 784979 := bstep (se 1 (by rfl) ⟨588734, by rfl⟩ : syracuseStep 784979 = 1177469) B1177469
theorem B1440371 : Blo 346754 1440371 := bstep (se 1 (by rfl) ⟨1080278, by rfl⟩ : syracuseStep 1440371 = 2160557) B2160557
theorem B588539 : Blo 346754 588539 := bstep (se 1 (by rfl) ⟨441404, by rfl⟩ : syracuseStep 588539 = 882809) B882809
theorem B2456477 : Blo 346754 2456477 := bstep (se 3 (by rfl) ⟨460589, by rfl⟩ : syracuseStep 2456477 = 921179) B921179
theorem B523295 : Blo 346754 523295 := bstep (se 1 (by rfl) ⟨392471, by rfl⟩ : syracuseStep 523295 = 784943) B784943
theorem B523439 : Blo 346754 523439 := bstep (se 1 (by rfl) ⟨392579, by rfl⟩ : syracuseStep 523439 = 785159) B785159
theorem B8092871 : Blo 346754 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B785735 : Blo 346754 785735 := bstep (se 1 (by rfl) ⟨589301, by rfl⟩ : syracuseStep 785735 = 1178603) B1178603
theorem B523847 : Blo 346754 523847 := bstep (se 1 (by rfl) ⟨392885, by rfl⟩ : syracuseStep 523847 = 785771) B785771
theorem B786023 : Blo 346754 786023 := bstep (se 1 (by rfl) ⟨589517, by rfl⟩ : syracuseStep 786023 = 1179035) B1179035
theorem B392863 : Blo 346754 392863 := bstep (se 1 (by rfl) ⟨294647, by rfl⟩ : syracuseStep 392863 = 589295) B589295
theorem B524159 : Blo 346754 524159 := bstep (se 1 (by rfl) ⟨393119, by rfl⟩ : syracuseStep 524159 = 786239) B786239
theorem B3178385 : Blo 346754 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B9633725 : Blo 346754 9633725 := bstep (se 3 (by rfl) ⟨1806323, by rfl⟩ : syracuseStep 9633725 = 3612647) B3612647
theorem B589855 : Blo 346754 589855 := bstep (se 1 (by rfl) ⟨442391, by rfl⟩ : syracuseStep 589855 = 884783) B884783
theorem B885239 : Blo 346754 885239 := bstep (se 1 (by rfl) ⟨663929, by rfl⟩ : syracuseStep 885239 = 1327859) B1327859
theorem B393727 : Blo 346754 393727 := bstep (se 1 (by rfl) ⟨295295, by rfl⟩ : syracuseStep 393727 = 590591) B590591
theorem B524855 : Blo 346754 524855 := bstep (se 1 (by rfl) ⟨393641, by rfl⟩ : syracuseStep 524855 = 787283) B787283
theorem B590719 : Blo 346754 590719 := bstep (se 1 (by rfl) ⟨443039, by rfl⟩ : syracuseStep 590719 = 886079) B886079
theorem B885755 : Blo 346754 885755 := bstep (se 1 (by rfl) ⟨664316, by rfl⟩ : syracuseStep 885755 = 1328633) B1328633
theorem B3573215 : Blo 346754 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B1771145 : Blo 346754 1771145 := bstep (se 2 (by rfl) ⟨664179, by rfl⟩ : syracuseStep 1771145 = 1328359) B1328359
theorem B526055 : Blo 346754 526055 := bstep (se 1 (by rfl) ⟨394541, by rfl⟩ : syracuseStep 526055 = 789083) B789083
theorem B526079 : Blo 346754 526079 := bstep (se 1 (by rfl) ⟨394559, by rfl⟩ : syracuseStep 526079 = 789119) B789119
theorem B887071 : Blo 346754 887071 := bstep (se 1 (by rfl) ⟨665303, by rfl⟩ : syracuseStep 887071 = 1330607) B1330607
theorem B1182059 : Blo 346754 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B6720515 : Blo 346754 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B2985497 : Blo 346754 2985497 := bstep (se 2 (by rfl) ⟨1119561, by rfl⟩ : syracuseStep 2985497 = 2239123) B2239123
theorem B5050025 : Blo 346754 5050025 := bstep (se 2 (by rfl) ⟨1893759, by rfl⟩ : syracuseStep 5050025 = 3787519) B3787519
theorem B1183463 : Blo 346754 1183463 := bstep (se 1 (by rfl) ⟨887597, by rfl⟩ : syracuseStep 1183463 = 1775195) B1775195
theorem B1118063 : Blo 346754 1118063 := bstep (se 1 (by rfl) ⟨838547, by rfl⟩ : syracuseStep 1118063 = 1677095) B1677095
theorem B2232359 : Blo 346754 2232359 := bstep (se 1 (by rfl) ⟨1674269, by rfl⟩ : syracuseStep 2232359 = 3348539) B3348539
theorem B2658905 : Blo 346754 2658905 := bstep (se 2 (by rfl) ⟨997089, by rfl⟩ : syracuseStep 2658905 = 1994179) B1994179
theorem B7508861 : Blo 346754 7508861 := bstep (se 3 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 7508861 = 2815823) B2815823
theorem B1250585 : Blo 346754 1250585 := bstep (se 2 (by rfl) ⟨468969, by rfl⟩ : syracuseStep 1250585 = 937939) B937939
theorem B2988535 : Blo 346754 2988535 := bstep (se 1 (by rfl) ⟨2241401, by rfl⟩ : syracuseStep 2988535 = 4482803) B4482803
theorem B2235023 : Blo 346754 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B629545 : Blo 346754 629545 := bstep (se 2 (by rfl) ⟨236079, by rfl⟩ : syracuseStep 629545 = 472159) B472159
theorem B3382073 : Blo 346754 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B1088423 : Blo 346754 1088423 := bstep (se 1 (by rfl) ⟨816317, by rfl⟩ : syracuseStep 1088423 = 1632635) B1632635
theorem B597179 : Blo 346754 597179 := bstep (se 1 (by rfl) ⟨447884, by rfl⟩ : syracuseStep 597179 = 895769) B895769
theorem B2661821 : Blo 346754 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B1056253 : Blo 346754 1056253 := bstep (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) B396095
theorem B597851 : Blo 346754 597851 := bstep (se 1 (by rfl) ⟨448388, by rfl⟩ : syracuseStep 597851 = 896777) B896777
theorem B631081 : Blo 346754 631081 := bstep (se 2 (by rfl) ⟨236655, by rfl⟩ : syracuseStep 631081 = 473311) B473311
theorem B1319611 : Blo 346754 1319611 := bstep (se 1 (by rfl) ⟨989708, by rfl⟩ : syracuseStep 1319611 = 1979417) B1979417
theorem B894035 : Blo 346754 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B960247 : Blo 346754 960247 := bstep (se 1 (by rfl) ⟨720185, by rfl⟩ : syracuseStep 960247 = 1440371) B1440371
theorem B37988189 : Blo 346754 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B665471 : Blo 346754 665471 := bstep (se 1 (by rfl) ⟨499103, by rfl⟩ : syracuseStep 665471 = 998207) B998207
theorem B1682207 : Blo 346754 1682207 := bstep (se 1 (by rfl) ⟨1261655, by rfl⟩ : syracuseStep 1682207 = 2523311) B2523311
theorem B12136085 : Blo 346754 12136085 := bstep (se 6 (by rfl) ⟨284439, by rfl⟩ : syracuseStep 12136085 = 568879) B568879
theorem B1979099 : Blo 346754 1979099 := bstep (se 1 (by rfl) ⟨1484324, by rfl⟩ : syracuseStep 1979099 = 2968649) B2968649
theorem B1324943 : Blo 346754 1324943 := bstep (se 1 (by rfl) ⟨993707, by rfl⟩ : syracuseStep 1324943 = 1987415) B1987415
theorem B2636063 : Blo 346754 2636063 := bstep (se 1 (by rfl) ⟨1977047, by rfl⟩ : syracuseStep 2636063 = 3954095) B3954095
theorem B1063307 : Blo 346754 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B1260157 : Blo 346754 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B10697507 : Blo 346754 10697507 := bstep (se 1 (by rfl) ⟨8023130, by rfl⟩ : syracuseStep 10697507 = 16046261) B16046261
theorem B703615 : Blo 346754 703615 := bstep (se 1 (by rfl) ⟨527711, by rfl⟩ : syracuseStep 703615 = 1055423) B1055423
theorem B1981583 : Blo 346754 1981583 := bstep (se 1 (by rfl) ⟨1486187, by rfl⟩ : syracuseStep 1981583 = 2972375) B2972375
theorem B2506241 : Blo 346754 2506241 := bstep (se 2 (by rfl) ⟨939840, by rfl⟩ : syracuseStep 2506241 = 1879681) B1879681
theorem B5030009 : Blo 346754 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B7160237 : Blo 346754 7160237 := bstep (se 3 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 7160237 = 2685089) B2685089
theorem B2638493 : Blo 346754 2638493 := bstep (se 3 (by rfl) ⟨494717, by rfl⟩ : syracuseStep 2638493 = 989435) B989435
theorem B30492197 : Blo 346754 30492197 := bstep (se 4 (by rfl) ⟨2858643, by rfl⟩ : syracuseStep 30492197 = 5717287) B5717287
theorem B1493927 : Blo 346754 1493927 := bstep (se 1 (by rfl) ⟨1120445, by rfl⟩ : syracuseStep 1493927 = 2240891) B2240891
theorem B1330121 : Blo 346754 1330121 := bstep (se 2 (by rfl) ⟨498795, by rfl⟩ : syracuseStep 1330121 = 997591) B997591
theorem B1985705 : Blo 346754 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B4771295 : Blo 346754 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B347803 : Blo 346754 347803 := bstep (se 1 (by rfl) ⟨260852, by rfl⟩ : syracuseStep 347803 = 521705) B521705
theorem B347935 : Blo 346754 347935 := bstep (se 1 (by rfl) ⟨260951, by rfl⟩ : syracuseStep 347935 = 521903) B521903
theorem B2969399 : Blo 346754 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B348095 : Blo 346754 348095 := bstep (se 1 (by rfl) ⟨261071, by rfl⟩ : syracuseStep 348095 = 522143) B522143
theorem B348383 : Blo 346754 348383 := bstep (se 1 (by rfl) ⟨261287, by rfl⟩ : syracuseStep 348383 = 522575) B522575
theorem B348415 : Blo 346754 348415 := bstep (se 1 (by rfl) ⟨261311, by rfl⟩ : syracuseStep 348415 = 522623) B522623
theorem B6181541 : Blo 346754 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B348863 : Blo 346754 348863 := bstep (se 1 (by rfl) ⟨261647, by rfl⟩ : syracuseStep 348863 = 523295) B523295
theorem B348959 : Blo 346754 348959 := bstep (se 1 (by rfl) ⟨261719, by rfl⟩ : syracuseStep 348959 = 523439) B523439
theorem B5395247 : Blo 346754 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B349231 : Blo 346754 349231 := bstep (se 1 (by rfl) ⟨261923, by rfl⟩ : syracuseStep 349231 = 523847) B523847
theorem B1758347 : Blo 346754 1758347 := bstep (se 1 (by rfl) ⟨1318760, by rfl⟩ : syracuseStep 1758347 = 2637521) B2637521
theorem B13423805 : Blo 346754 13423805 := bstep (se 3 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 13423805 = 5033927) B5033927
theorem B349439 : Blo 346754 349439 := bstep (se 1 (by rfl) ⟨262079, by rfl⟩ : syracuseStep 349439 = 524159) B524159
theorem B2118923 : Blo 346754 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B350119 : Blo 346754 350119 := bstep (se 1 (by rfl) ⟨262589, by rfl⟩ : syracuseStep 350119 = 525179) B525179
theorem B350207 : Blo 346754 350207 := bstep (se 1 (by rfl) ⟨262655, by rfl⟩ : syracuseStep 350207 = 525311) B525311
theorem B2513105 : Blo 346754 2513105 := bstep (se 2 (by rfl) ⟨942414, by rfl⟩ : syracuseStep 2513105 = 1884829) B1884829
theorem B3529271 : Blo 346754 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B1759967 : Blo 346754 1759967 := bstep (se 1 (by rfl) ⟨1319975, by rfl⟩ : syracuseStep 1759967 = 2639951) B2639951
theorem B4283239 : Blo 346754 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B941291 : Blo 346754 941291 := bstep (se 1 (by rfl) ⟨705968, by rfl⟩ : syracuseStep 941291 = 1411937) B1411937
theorem B36298529 : Blo 346754 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B1171529 : Blo 346754 1171529 := bstep (se 2 (by rfl) ⟨439323, by rfl⟩ : syracuseStep 1171529 = 878647) B878647
theorem B10150049 : Blo 346754 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B746587 : Blo 346754 746587 := bstep (se 1 (by rfl) ⟨559940, by rfl⟩ : syracuseStep 746587 = 1119881) B1119881
theorem B1173257 : Blo 346754 1173257 := bstep (se 2 (by rfl) ⟨439971, by rfl⟩ : syracuseStep 1173257 = 879943) B879943
theorem B1173419 : Blo 346754 1173419 := bstep (se 1 (by rfl) ⟨880064, by rfl⟩ : syracuseStep 1173419 = 1760129) B1760129
theorem B846251 : Blo 346754 846251 := bstep (se 1 (by rfl) ⟨634688, by rfl⟩ : syracuseStep 846251 = 1269377) B1269377
theorem B2550203 : Blo 346754 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B748399 : Blo 346754 748399 := bstep (se 1 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 748399 = 1122599) B1122599
theorem B585353 : Blo 346754 585353 := bstep (se 2 (by rfl) ⟨219507, by rfl⟩ : syracuseStep 585353 = 439015) B439015
theorem B585407 : Blo 346754 585407 := bstep (se 1 (by rfl) ⟨439055, by rfl⟩ : syracuseStep 585407 = 878111) B878111
theorem B158232527 : Blo 346754 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B1175579 : Blo 346754 1175579 := bstep (se 1 (by rfl) ⟨881684, by rfl⟩ : syracuseStep 1175579 = 1763369) B1763369
theorem B520283 : Blo 346754 520283 := bstep (se 1 (by rfl) ⟨390212, by rfl⟩ : syracuseStep 520283 = 780425) B780425
theorem B880895 : Blo 346754 880895 := bstep (se 1 (by rfl) ⟨660671, by rfl⟩ : syracuseStep 880895 = 1321343) B1321343
theorem B586271 : Blo 346754 586271 := bstep (se 1 (by rfl) ⟨439703, by rfl⟩ : syracuseStep 586271 = 879407) B879407
theorem B520751 : Blo 346754 520751 := bstep (se 1 (by rfl) ⟨390563, by rfl⟩ : syracuseStep 520751 = 781127) B781127
theorem B1176119 : Blo 346754 1176119 := bstep (se 1 (by rfl) ⟨882089, by rfl⟩ : syracuseStep 1176119 = 1764179) B1764179
theorem B520871 : Blo 346754 520871 := bstep (se 1 (by rfl) ⟨390653, by rfl⟩ : syracuseStep 520871 = 781307) B781307
theorem B1176443 : Blo 346754 1176443 := bstep (se 1 (by rfl) ⟨882332, by rfl⟩ : syracuseStep 1176443 = 1764665) B1764665
theorem B521723 : Blo 346754 521723 := bstep (se 1 (by rfl) ⟨391292, by rfl⟩ : syracuseStep 521723 = 782585) B782585
theorem B521783 : Blo 346754 521783 := bstep (se 1 (by rfl) ⟨391337, by rfl⟩ : syracuseStep 521783 = 782675) B782675
theorem B587371 : Blo 346754 587371 := bstep (se 1 (by rfl) ⟨440528, by rfl⟩ : syracuseStep 587371 = 881057) B881057
theorem B521855 : Blo 346754 521855 := bstep (se 1 (by rfl) ⟨391391, by rfl⟩ : syracuseStep 521855 = 782783) B782783
theorem B522023 : Blo 346754 522023 := bstep (se 1 (by rfl) ⟨391517, by rfl⟩ : syracuseStep 522023 = 783035) B783035
theorem B522095 : Blo 346754 522095 := bstep (se 1 (by rfl) ⟨391571, by rfl⟩ : syracuseStep 522095 = 783143) B783143
theorem B587675 : Blo 346754 587675 := bstep (se 1 (by rfl) ⟨440756, by rfl⟩ : syracuseStep 587675 = 881513) B881513
theorem B7567499 : Blo 346754 7567499 := bstep (se 1 (by rfl) ⟨5675624, by rfl⟩ : syracuseStep 7567499 = 11351249) B11351249
theorem B522491 : Blo 346754 522491 := bstep (se 1 (by rfl) ⟨391868, by rfl⟩ : syracuseStep 522491 = 783737) B783737
theorem B391495 : Blo 346754 391495 := bstep (se 1 (by rfl) ⟨293621, by rfl⟩ : syracuseStep 391495 = 587243) B587243
theorem B1112591 : Blo 346754 1112591 := bstep (se 1 (by rfl) ⟨834443, by rfl⟩ : syracuseStep 1112591 = 1668887) B1668887
theorem B785087 : Blo 346754 785087 := bstep (se 1 (by rfl) ⟨588815, by rfl⟩ : syracuseStep 785087 = 1177631) B1177631
theorem B588667 : Blo 346754 588667 := bstep (se 1 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 588667 = 883001) B883001
theorem B2882587 : Blo 346754 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B523319 : Blo 346754 523319 := bstep (se 1 (by rfl) ⟨392489, by rfl⟩ : syracuseStep 523319 = 784979) B784979
theorem B392359 : Blo 346754 392359 := bstep (se 1 (by rfl) ⟨294269, by rfl⟩ : syracuseStep 392359 = 588539) B588539
theorem B1637651 : Blo 346754 1637651 := bstep (se 1 (by rfl) ⟨1228238, by rfl⟩ : syracuseStep 1637651 = 2456477) B2456477
theorem B523817 : Blo 346754 523817 := bstep (se 2 (by rfl) ⟨196431, by rfl⟩ : syracuseStep 523817 = 392863) B392863
theorem B523823 : Blo 346754 523823 := bstep (se 1 (by rfl) ⟨392867, by rfl⟩ : syracuseStep 523823 = 785735) B785735
theorem B524015 : Blo 346754 524015 := bstep (se 1 (by rfl) ⟨393011, by rfl⟩ : syracuseStep 524015 = 786023) B786023
theorem B9567989 : Blo 346754 9567989 := bstep (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) B896999
theorem B6422483 : Blo 346754 6422483 := bstep (se 1 (by rfl) ⟨4816862, by rfl⟩ : syracuseStep 6422483 = 9633725) B9633725
theorem B786473 : Blo 346754 786473 := bstep (se 2 (by rfl) ⟨294927, by rfl⟩ : syracuseStep 786473 = 589855) B589855
theorem B590159 : Blo 346754 590159 := bstep (se 1 (by rfl) ⟨442619, by rfl⟩ : syracuseStep 590159 = 885239) B885239
theorem B590503 : Blo 346754 590503 := bstep (se 1 (by rfl) ⟨442877, by rfl⟩ : syracuseStep 590503 = 885755) B885755
theorem B524969 : Blo 346754 524969 := bstep (se 2 (by rfl) ⟨196863, by rfl⟩ : syracuseStep 524969 = 393727) B393727
theorem B1180763 : Blo 346754 1180763 := bstep (se 1 (by rfl) ⟨885572, by rfl⟩ : syracuseStep 1180763 = 1771145) B1771145
theorem B787625 : Blo 346754 787625 := bstep (se 2 (by rfl) ⟨295359, by rfl⟩ : syracuseStep 787625 = 590719) B590719
theorem B788039 : Blo 346754 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B886747 : Blo 346754 886747 := bstep (se 1 (by rfl) ⟨665060, by rfl⟩ : syracuseStep 886747 = 1330121) B1330121
theorem B3180863 : Blo 346754 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B1280329 : Blo 346754 1280329 := bstep (se 2 (by rfl) ⟨480123, by rfl⟩ : syracuseStep 1280329 = 960247) B960247
theorem B788975 : Blo 346754 788975 := bstep (se 1 (by rfl) ⟨591731, by rfl⟩ : syracuseStep 788975 = 1183463) B1183463
theorem B1182761 : Blo 346754 1182761 := bstep (se 2 (by rfl) ⟨443535, by rfl⟩ : syracuseStep 1182761 = 887071) B887071
theorem B1772603 : Blo 346754 1772603 := bstep (se 1 (by rfl) ⟨1329452, by rfl⟩ : syracuseStep 1772603 = 2658905) B2658905
theorem B8949203 : Blo 346754 8949203 := bstep (se 1 (by rfl) ⟨6711902, by rfl⟩ : syracuseStep 8949203 = 13423805) B13423805
theorem B1412615 : Blo 346754 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B1675403 : Blo 346754 1675403 := bstep (se 1 (by rfl) ⟨1256552, by rfl⟩ : syracuseStep 1675403 = 2513105) B2513105
theorem B725615 : Blo 346754 725615 := bstep (se 1 (by rfl) ⟨544211, by rfl⟩ : syracuseStep 725615 = 1088423) B1088423
theorem B398119 : Blo 346754 398119 := bstep (se 1 (by rfl) ⟨298589, by rfl⟩ : syracuseStep 398119 = 597179) B597179
theorem B627527 : Blo 346754 627527 := bstep (se 1 (by rfl) ⟨470645, by rfl⟩ : syracuseStep 627527 = 941291) B941291
theorem B1774547 : Blo 346754 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B398567 : Blo 346754 398567 := bstep (se 1 (by rfl) ⟨298925, by rfl⟩ : syracuseStep 398567 = 597851) B597851
theorem B564167 : Blo 346754 564167 := bstep (se 1 (by rfl) ⟨423125, by rfl⟩ : syracuseStep 564167 = 846251) B846251
theorem B1121471 : Blo 346754 1121471 := bstep (se 1 (by rfl) ⟨841103, by rfl⟩ : syracuseStep 1121471 = 1682207) B1682207
theorem B105488351 : Blo 346754 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B1319399 : Blo 346754 1319399 := bstep (se 1 (by rfl) ⟨989549, by rfl⟩ : syracuseStep 1319399 = 1979099) B1979099
theorem B1680209 : Blo 346754 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B5710985 : Blo 346754 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B3843449 : Blo 346754 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B1321055 : Blo 346754 1321055 := bstep (se 1 (by rfl) ⟨990791, by rfl⟩ : syracuseStep 1321055 = 1981583) B1981583
theorem B1091767 : Blo 346754 1091767 := bstep (se 1 (by rfl) ⟨818825, by rfl⟩ : syracuseStep 1091767 = 1637651) B1637651
theorem B3353339 : Blo 346754 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B20328131 : Blo 346754 20328131 := bstep (se 1 (by rfl) ⟨15246098, by rfl⟩ : syracuseStep 20328131 = 30492197) B30492197
theorem B995951 : Blo 346754 995951 := bstep (se 1 (by rfl) ⟨746963, by rfl⟩ : syracuseStep 995951 = 1493927) B1493927
theorem B1323803 : Blo 346754 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B1979599 : Blo 346754 1979599 := bstep (se 1 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 1979599 = 2969399) B2969399
theorem B1488239 : Blo 346754 1488239 := bstep (se 1 (by rfl) ⟨1116179, by rfl⟩ : syracuseStep 1488239 = 2232359) B2232359
theorem B833723 : Blo 346754 833723 := bstep (se 1 (by rfl) ⟨625292, by rfl⟩ : syracuseStep 833723 = 1250585) B1250585
theorem B997865 : Blo 346754 997865 := bstep (se 2 (by rfl) ⟨374199, by rfl⟩ : syracuseStep 997865 = 748399) B748399
theorem B1490015 : Blo 346754 1490015 := bstep (se 1 (by rfl) ⟨1117511, by rfl⟩ : syracuseStep 1490015 = 2235023) B2235023
theorem B24199019 : Blo 346754 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B6766699 : Blo 346754 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B3981797 : Blo 346754 3981797 := bstep (se 4 (by rfl) ⟨373293, by rfl⟩ : syracuseStep 3981797 = 746587) B746587
theorem B443647 : Blo 346754 443647 := bstep (se 1 (by rfl) ⟨332735, by rfl⟩ : syracuseStep 443647 = 665471) B665471
theorem B346855 : Blo 346754 346855 := bstep (se 1 (by rfl) ⟨260141, by rfl⟩ : syracuseStep 346855 = 520283) B520283
theorem B347167 : Blo 346754 347167 := bstep (se 1 (by rfl) ⟨260375, by rfl⟩ : syracuseStep 347167 = 520751) B520751
theorem B347247 : Blo 346754 347247 := bstep (se 1 (by rfl) ⟨260435, by rfl⟩ : syracuseStep 347247 = 520871) B520871
theorem B3984713 : Blo 346754 3984713 := bstep (se 2 (by rfl) ⟨1494267, by rfl⟩ : syracuseStep 3984713 = 2988535) B2988535
theorem B347815 : Blo 346754 347815 := bstep (se 1 (by rfl) ⟨260861, by rfl⟩ : syracuseStep 347815 = 521723) B521723
theorem B347855 : Blo 346754 347855 := bstep (se 1 (by rfl) ⟨260891, by rfl⟩ : syracuseStep 347855 = 521783) B521783
theorem B839393 : Blo 346754 839393 := bstep (se 2 (by rfl) ⟨314772, by rfl⟩ : syracuseStep 839393 = 629545) B629545
theorem B347903 : Blo 346754 347903 := bstep (se 1 (by rfl) ⟨260927, by rfl⟩ : syracuseStep 347903 = 521855) B521855
theorem B348015 : Blo 346754 348015 := bstep (se 1 (by rfl) ⟨261011, by rfl⟩ : syracuseStep 348015 = 522023) B522023
theorem B348063 : Blo 346754 348063 := bstep (se 1 (by rfl) ⟨261047, by rfl⟩ : syracuseStep 348063 = 522095) B522095
theorem B348327 : Blo 346754 348327 := bstep (se 1 (by rfl) ⟨261245, by rfl⟩ : syracuseStep 348327 = 522491) B522491
theorem B938153 : Blo 346754 938153 := bstep (se 2 (by rfl) ⟨351807, by rfl⟩ : syracuseStep 938153 = 703615) B703615
theorem B1757375 : Blo 346754 1757375 := bstep (se 1 (by rfl) ⟨1318031, by rfl⟩ : syracuseStep 1757375 = 2636063) B2636063
theorem B708871 : Blo 346754 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B741727 : Blo 346754 741727 := bstep (se 1 (by rfl) ⟨556295, by rfl⟩ : syracuseStep 741727 = 1112591) B1112591
theorem B7131671 : Blo 346754 7131671 := bstep (se 1 (by rfl) ⟨5348753, by rfl⟩ : syracuseStep 7131671 = 10697507) B10697507
theorem B348879 : Blo 346754 348879 := bstep (se 1 (by rfl) ⟨261659, by rfl⟩ : syracuseStep 348879 = 523319) B523319
theorem B349211 : Blo 346754 349211 := bstep (se 1 (by rfl) ⟨261908, by rfl⟩ : syracuseStep 349211 = 523817) B523817
theorem B349215 : Blo 346754 349215 := bstep (se 1 (by rfl) ⟨261911, by rfl⟩ : syracuseStep 349215 = 523823) B523823
theorem B349343 : Blo 346754 349343 := bstep (se 1 (by rfl) ⟨262007, by rfl⟩ : syracuseStep 349343 = 524015) B524015
theorem B6378659 : Blo 346754 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B4281655 : Blo 346754 4281655 := bstep (se 1 (by rfl) ⟨3211241, by rfl⟩ : syracuseStep 4281655 = 6422483) B6422483
theorem B4773491 : Blo 346754 4773491 := bstep (se 1 (by rfl) ⟨3580118, by rfl⟩ : syracuseStep 4773491 = 7160237) B7160237
theorem B349903 : Blo 346754 349903 := bstep (se 1 (by rfl) ⟨262427, by rfl⟩ : syracuseStep 349903 = 524855) B524855
theorem B841441 : Blo 346754 841441 := bstep (se 2 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 841441 = 631081) B631081
theorem B1758995 : Blo 346754 1758995 := bstep (se 1 (by rfl) ⟨1319246, by rfl⟩ : syracuseStep 1758995 = 2638493) B2638493
theorem B1759481 : Blo 346754 1759481 := bstep (se 2 (by rfl) ⟨659805, by rfl⟩ : syracuseStep 1759481 = 1319611) B1319611
theorem B2382143 : Blo 346754 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B350703 : Blo 346754 350703 := bstep (se 1 (by rfl) ⟨263027, by rfl⟩ : syracuseStep 350703 = 526055) B526055
theorem B350719 : Blo 346754 350719 := bstep (se 1 (by rfl) ⟨263039, by rfl⟩ : syracuseStep 350719 = 526079) B526079
theorem B4480343 : Blo 346754 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B1990331 : Blo 346754 1990331 := bstep (se 1 (by rfl) ⟨1492748, by rfl⟩ : syracuseStep 1990331 = 2985497) B2985497
theorem B3366683 : Blo 346754 3366683 := bstep (se 1 (by rfl) ⟨2525012, by rfl⟩ : syracuseStep 3366683 = 5050025) B5050025
theorem B745375 : Blo 346754 745375 := bstep (se 1 (by rfl) ⟨559031, by rfl⟩ : syracuseStep 745375 = 1118063) B1118063
theorem B2384093 : Blo 346754 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B4121027 : Blo 346754 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B3596831 : Blo 346754 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B5005907 : Blo 346754 5005907 := bstep (se 1 (by rfl) ⟨3754430, by rfl⟩ : syracuseStep 5005907 = 7508861) B7508861
theorem B1172231 : Blo 346754 1172231 := bstep (se 1 (by rfl) ⟨879173, by rfl⟩ : syracuseStep 1172231 = 1758347) B1758347
theorem B2352847 : Blo 346754 2352847 := bstep (se 1 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 2352847 = 3529271) B3529271
theorem B1173311 : Blo 346754 1173311 := bstep (se 1 (by rfl) ⟨879983, by rfl⟩ : syracuseStep 1173311 = 1759967) B1759967
theorem B2254715 : Blo 346754 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B781019 : Blo 346754 781019 := bstep (se 1 (by rfl) ⟨585764, by rfl⟩ : syracuseStep 781019 = 1171529) B1171529
theorem B782171 : Blo 346754 782171 := bstep (se 1 (by rfl) ⟨586628, by rfl⟩ : syracuseStep 782171 = 1173257) B1173257
theorem B25325459 : Blo 346754 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B782279 : Blo 346754 782279 := bstep (se 1 (by rfl) ⟨586709, by rfl⟩ : syracuseStep 782279 = 1173419) B1173419
theorem B1700135 : Blo 346754 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B783161 : Blo 346754 783161 := bstep (se 2 (by rfl) ⟨293685, by rfl⟩ : syracuseStep 783161 = 587371) B587371
theorem B390235 : Blo 346754 390235 := bstep (se 1 (by rfl) ⟨292676, by rfl⟩ : syracuseStep 390235 = 585353) B585353
theorem B8090723 : Blo 346754 8090723 := bstep (se 1 (by rfl) ⟨6068042, by rfl⟩ : syracuseStep 8090723 = 12136085) B12136085
theorem B390271 : Blo 346754 390271 := bstep (se 1 (by rfl) ⟨292703, by rfl⟩ : syracuseStep 390271 = 585407) B585407
theorem B783719 : Blo 346754 783719 := bstep (se 1 (by rfl) ⟨587789, by rfl⟩ : syracuseStep 783719 = 1175579) B1175579
theorem B587263 : Blo 346754 587263 := bstep (se 1 (by rfl) ⟨440447, by rfl⟩ : syracuseStep 587263 = 880895) B880895
theorem B390847 : Blo 346754 390847 := bstep (se 1 (by rfl) ⟨293135, by rfl⟩ : syracuseStep 390847 = 586271) B586271
theorem B784079 : Blo 346754 784079 := bstep (se 1 (by rfl) ⟨588059, by rfl⟩ : syracuseStep 784079 = 1176119) B1176119
theorem B521993 : Blo 346754 521993 := bstep (se 2 (by rfl) ⟨195747, by rfl⟩ : syracuseStep 521993 = 391495) B391495
theorem B784295 : Blo 346754 784295 := bstep (se 1 (by rfl) ⟨588221, by rfl⟩ : syracuseStep 784295 = 1176443) B1176443
theorem B784889 : Blo 346754 784889 := bstep (se 2 (by rfl) ⟨294333, by rfl⟩ : syracuseStep 784889 = 588667) B588667
theorem B883295 : Blo 346754 883295 := bstep (se 1 (by rfl) ⟨662471, by rfl⟩ : syracuseStep 883295 = 1324943) B1324943
theorem B391783 : Blo 346754 391783 := bstep (se 1 (by rfl) ⟨293837, by rfl⟩ : syracuseStep 391783 = 587675) B587675
theorem B5044999 : Blo 346754 5044999 := bstep (se 1 (by rfl) ⟨3783749, by rfl⟩ : syracuseStep 5044999 = 7567499) B7567499
theorem B523145 : Blo 346754 523145 := bstep (se 2 (by rfl) ⟨196179, by rfl⟩ : syracuseStep 523145 = 392359) B392359
theorem B523391 : Blo 346754 523391 := bstep (se 1 (by rfl) ⟨392543, by rfl⟩ : syracuseStep 523391 = 785087) B785087
theorem B1408337 : Blo 346754 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B1670827 : Blo 346754 1670827 := bstep (se 1 (by rfl) ⟨1253120, by rfl⟩ : syracuseStep 1670827 = 2506241) B2506241
theorem B524315 : Blo 346754 524315 := bstep (se 1 (by rfl) ⟨393236, by rfl⟩ : syracuseStep 524315 = 786473) B786473
theorem B393439 : Blo 346754 393439 := bstep (se 1 (by rfl) ⟨295079, by rfl⟩ : syracuseStep 393439 = 590159) B590159
theorem B2654531 : Blo 346754 2654531 := bstep (se 1 (by rfl) ⟨1990898, by rfl⟩ : syracuseStep 2654531 = 3981797) B3981797
theorem B787175 : Blo 346754 787175 := bstep (se 1 (by rfl) ⟨590381, by rfl⟩ : syracuseStep 787175 = 1180763) B1180763
theorem B525083 : Blo 346754 525083 := bstep (se 1 (by rfl) ⟨393812, by rfl⟩ : syracuseStep 525083 = 787625) B787625
theorem B787337 : Blo 346754 787337 := bstep (se 2 (by rfl) ⟨295251, by rfl⟩ : syracuseStep 787337 = 590503) B590503
theorem B525359 : Blo 346754 525359 := bstep (se 1 (by rfl) ⟨394019, by rfl⟩ : syracuseStep 525359 = 788039) B788039
theorem B525983 : Blo 346754 525983 := bstep (se 1 (by rfl) ⟨394487, by rfl⟩ : syracuseStep 525983 = 788975) B788975
theorem B591529 : Blo 346754 591529 := bstep (se 2 (by rfl) ⟨221823, by rfl⟩ : syracuseStep 591529 = 443647) B443647
theorem B788507 : Blo 346754 788507 := bstep (se 1 (by rfl) ⟨591380, by rfl⟩ : syracuseStep 788507 = 1182761) B1182761
theorem B1181735 : Blo 346754 1181735 := bstep (se 1 (by rfl) ⟨886301, by rfl⟩ : syracuseStep 1181735 = 1772603) B1772603
theorem B1673405 : Blo 346754 1673405 := bstep (se 3 (by rfl) ⟨313763, by rfl⟩ : syracuseStep 1673405 = 627527) B627527
theorem B2656475 : Blo 346754 2656475 := bstep (se 1 (by rfl) ⟨1992356, by rfl⟩ : syracuseStep 2656475 = 3984713) B3984713
theorem B5966135 : Blo 346754 5966135 := bstep (se 1 (by rfl) ⟨4474601, by rfl⟩ : syracuseStep 5966135 = 8949203) B8949203
theorem B559595 : Blo 346754 559595 := bstep (se 1 (by rfl) ⟨419696, by rfl⟩ : syracuseStep 559595 = 839393) B839393
theorem B1182329 : Blo 346754 1182329 := bstep (se 2 (by rfl) ⟨443373, by rfl⟩ : syracuseStep 1182329 = 886747) B886747
theorem B1116935 : Blo 346754 1116935 := bstep (se 1 (by rfl) ⟨837701, by rfl⟩ : syracuseStep 1116935 = 1675403) B1675403
theorem B4754447 : Blo 346754 4754447 := bstep (se 1 (by rfl) ⟨3565835, by rfl⟩ : syracuseStep 4754447 = 7131671) B7131671
theorem B1183031 : Blo 346754 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B3182327 : Blo 346754 3182327 := bstep (se 1 (by rfl) ⟨2386745, by rfl⟩ : syracuseStep 3182327 = 4773491) B4773491
theorem B2986895 : Blo 346754 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B70325567 : Blo 346754 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B2397887 : Blo 346754 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B988969 : Blo 346754 988969 := bstep (se 2 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 988969 = 741727) B741727
theorem B1120139 : Blo 346754 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B3807323 : Blo 346754 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B2562299 : Blo 346754 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B530825 : Blo 346754 530825 := bstep (se 2 (by rfl) ⟨199059, by rfl⟩ : syracuseStep 530825 = 398119) B398119
theorem B5708873 : Blo 346754 5708873 := bstep (se 2 (by rfl) ⟨2140827, by rfl⟩ : syracuseStep 5708873 = 4281655) B4281655
theorem B2235559 : Blo 346754 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B1121921 : Blo 346754 1121921 := bstep (se 2 (by rfl) ⟨420720, by rfl⟩ : syracuseStep 1121921 = 841441) B841441
theorem B16883639 : Blo 346754 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B663967 : Blo 346754 663967 := bstep (se 1 (by rfl) ⟨497975, by rfl⟩ : syracuseStep 663967 = 995951) B995951
theorem B992159 : Blo 346754 992159 := bstep (se 1 (by rfl) ⟨744119, by rfl⟩ : syracuseStep 992159 = 1488239) B1488239
theorem B6726665 : Blo 346754 6726665 := bstep (se 2 (by rfl) ⟨2522499, by rfl⟩ : syracuseStep 6726665 = 5044999) B5044999
theorem B665243 : Blo 346754 665243 := bstep (se 1 (by rfl) ⟨498932, by rfl⟩ : syracuseStep 665243 = 997865) B997865
theorem B54208349 : Blo 346754 54208349 := bstep (se 3 (by rfl) ⟨10164065, by rfl⟩ : syracuseStep 54208349 = 20328131) B20328131
theorem B993343 : Blo 346754 993343 := bstep (se 1 (by rfl) ⟨745007, by rfl⟩ : syracuseStep 993343 = 1490015) B1490015
theorem B993833 : Blo 346754 993833 := bstep (se 2 (by rfl) ⟨372687, by rfl⟩ : syracuseStep 993833 = 745375) B745375
theorem B16132679 : Blo 346754 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B9022265 : Blo 346754 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B2501741 : Blo 346754 2501741 := bstep (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) B938153
theorem B1455689 : Blo 346754 1455689 := bstep (se 2 (by rfl) ⟨545883, by rfl⟩ : syracuseStep 1455689 = 1091767) B1091767
theorem B21575261 : Blo 346754 21575261 := bstep (se 3 (by rfl) ⟨4045361, by rfl⟩ : syracuseStep 21575261 = 8090723) B8090723
theorem B1062845 : Blo 346754 1062845 := bstep (se 3 (by rfl) ⟨199283, by rfl⟩ : syracuseStep 1062845 = 398567) B398567
theorem B376111 : Blo 346754 376111 := bstep (se 1 (by rfl) ⟨282083, by rfl⟩ : syracuseStep 376111 = 564167) B564167
theorem B1326887 : Blo 346754 1326887 := bstep (se 1 (by rfl) ⟨995165, by rfl⟩ : syracuseStep 1326887 = 1990331) B1990331
theorem B2244455 : Blo 346754 2244455 := bstep (se 1 (by rfl) ⟨1683341, by rfl⟩ : syracuseStep 2244455 = 3366683) B3366683
theorem B1589395 : Blo 346754 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B27313685 : Blo 346754 27313685 := bstep (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) B1280329
theorem B2639465 : Blo 346754 2639465 := bstep (se 2 (by rfl) ⟨989799, by rfl⟩ : syracuseStep 2639465 = 1979599) B1979599
theorem B1133423 : Blo 346754 1133423 := bstep (se 1 (by rfl) ⟨850067, by rfl⟩ : syracuseStep 1133423 = 1700135) B1700135
theorem B347995 : Blo 346754 347995 := bstep (se 1 (by rfl) ⟨260996, by rfl⟩ : syracuseStep 347995 = 521993) B521993
theorem B348763 : Blo 346754 348763 := bstep (se 1 (by rfl) ⟨261572, by rfl⟩ : syracuseStep 348763 = 523145) B523145
theorem B348927 : Blo 346754 348927 := bstep (se 1 (by rfl) ⟨261695, by rfl⟩ : syracuseStep 348927 = 523391) B523391
theorem B938891 : Blo 346754 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B349979 : Blo 346754 349979 := bstep (se 1 (by rfl) ⟨262484, by rfl⟩ : syracuseStep 349979 = 524969) B524969
theorem B2120575 : Blo 346754 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B3137129 : Blo 346754 3137129 := bstep (se 2 (by rfl) ⟨1176423, by rfl⟩ : syracuseStep 3137129 = 2352847) B2352847
theorem B941743 : Blo 346754 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B1171583 : Blo 346754 1171583 := bstep (se 1 (by rfl) ⟨878687, by rfl⟩ : syracuseStep 1171583 = 1757375) B1757375
theorem B483743 : Blo 346754 483743 := bstep (se 1 (by rfl) ⟨362807, by rfl⟩ : syracuseStep 483743 = 725615) B725615
theorem B4252439 : Blo 346754 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B1172663 : Blo 346754 1172663 := bstep (se 1 (by rfl) ⟨879497, by rfl⟩ : syracuseStep 1172663 = 1758995) B1758995
theorem B1172987 : Blo 346754 1172987 := bstep (se 1 (by rfl) ⟨879740, by rfl⟩ : syracuseStep 1172987 = 1759481) B1759481
theorem B747647 : Blo 346754 747647 := bstep (se 1 (by rfl) ⟨560735, by rfl⟩ : syracuseStep 747647 = 1121471) B1121471
theorem B2747351 : Blo 346754 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B879599 : Blo 346754 879599 := bstep (se 1 (by rfl) ⟨659699, by rfl⟩ : syracuseStep 879599 = 1319399) B1319399
theorem B945161 : Blo 346754 945161 := bstep (se 2 (by rfl) ⟨354435, by rfl⟩ : syracuseStep 945161 = 708871) B708871
theorem B3337271 : Blo 346754 3337271 := bstep (se 1 (by rfl) ⟨2502953, by rfl⟩ : syracuseStep 3337271 = 5005907) B5005907
theorem B781487 : Blo 346754 781487 := bstep (se 1 (by rfl) ⟨586115, by rfl⟩ : syracuseStep 781487 = 1172231) B1172231
theorem B6352381 : Blo 346754 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B782207 : Blo 346754 782207 := bstep (se 1 (by rfl) ⟨586655, by rfl⟩ : syracuseStep 782207 = 1173311) B1173311
theorem B1503143 : Blo 346754 1503143 := bstep (se 1 (by rfl) ⟨1127357, by rfl⟩ : syracuseStep 1503143 = 2254715) B2254715
theorem B880703 : Blo 346754 880703 := bstep (se 1 (by rfl) ⟨660527, by rfl⟩ : syracuseStep 880703 = 1321055) B1321055
theorem B520313 : Blo 346754 520313 := bstep (se 2 (by rfl) ⟨195117, by rfl⟩ : syracuseStep 520313 = 390235) B390235
theorem B520361 : Blo 346754 520361 := bstep (se 2 (by rfl) ⟨195135, by rfl⟩ : syracuseStep 520361 = 390271) B390271
theorem B520679 : Blo 346754 520679 := bstep (se 1 (by rfl) ⟨390509, by rfl⟩ : syracuseStep 520679 = 781019) B781019
theorem B783017 : Blo 346754 783017 := bstep (se 2 (by rfl) ⟨293631, by rfl⟩ : syracuseStep 783017 = 587263) B587263
theorem B521129 : Blo 346754 521129 := bstep (se 2 (by rfl) ⟨195423, by rfl⟩ : syracuseStep 521129 = 390847) B390847
theorem B521447 : Blo 346754 521447 := bstep (se 1 (by rfl) ⟨391085, by rfl⟩ : syracuseStep 521447 = 782171) B782171
theorem B521519 : Blo 346754 521519 := bstep (se 1 (by rfl) ⟨391139, by rfl⟩ : syracuseStep 521519 = 782279) B782279
theorem B882535 : Blo 346754 882535 := bstep (se 1 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 882535 = 1323803) B1323803
theorem B522107 : Blo 346754 522107 := bstep (se 1 (by rfl) ⟨391580, by rfl⟩ : syracuseStep 522107 = 783161) B783161
theorem B522377 : Blo 346754 522377 := bstep (se 2 (by rfl) ⟨195891, by rfl⟩ : syracuseStep 522377 = 391783) B391783
theorem B522479 : Blo 346754 522479 := bstep (se 1 (by rfl) ⟨391859, by rfl⟩ : syracuseStep 522479 = 783719) B783719
theorem B522719 : Blo 346754 522719 := bstep (se 1 (by rfl) ⟨392039, by rfl⟩ : syracuseStep 522719 = 784079) B784079
theorem B522863 : Blo 346754 522863 := bstep (se 1 (by rfl) ⟨392147, by rfl⟩ : syracuseStep 522863 = 784295) B784295
theorem B555815 : Blo 346754 555815 := bstep (se 1 (by rfl) ⟨416861, by rfl⟩ : syracuseStep 555815 = 833723) B833723
theorem B523259 : Blo 346754 523259 := bstep (se 1 (by rfl) ⟨392444, by rfl⟩ : syracuseStep 523259 = 784889) B784889
theorem B588863 : Blo 346754 588863 := bstep (se 1 (by rfl) ⟨441647, by rfl⟩ : syracuseStep 588863 = 883295) B883295
theorem B2227769 : Blo 346754 2227769 := bstep (se 2 (by rfl) ⟨835413, by rfl⟩ : syracuseStep 2227769 = 1670827) B1670827
theorem B1769687 : Blo 346754 1769687 := bstep (se 1 (by rfl) ⟨1327265, by rfl⟩ : syracuseStep 1769687 = 2654531) B2654531
theorem B524585 : Blo 346754 524585 := bstep (se 2 (by rfl) ⟨196719, by rfl⟩ : syracuseStep 524585 = 393439) B393439
theorem B524783 : Blo 346754 524783 := bstep (se 1 (by rfl) ⟨393587, by rfl⟩ : syracuseStep 524783 = 787175) B787175
theorem B885289 : Blo 346754 885289 := bstep (se 2 (by rfl) ⟨331983, by rfl⟩ : syracuseStep 885289 = 663967) B663967
theorem B524891 : Blo 346754 524891 := bstep (se 1 (by rfl) ⟨393668, by rfl⟩ : syracuseStep 524891 = 787337) B787337
theorem B525671 : Blo 346754 525671 := bstep (se 1 (by rfl) ⟨394253, by rfl⟩ : syracuseStep 525671 = 788507) B788507
theorem B787823 : Blo 346754 787823 := bstep (se 1 (by rfl) ⟨590867, by rfl⟩ : syracuseStep 787823 = 1181735) B1181735
theorem B1115603 : Blo 346754 1115603 := bstep (se 1 (by rfl) ⟨836702, by rfl⟩ : syracuseStep 1115603 = 1673405) B1673405
theorem B1770983 : Blo 346754 1770983 := bstep (se 1 (by rfl) ⟨1328237, by rfl⟩ : syracuseStep 1770983 = 2656475) B2656475
theorem B788219 : Blo 346754 788219 := bstep (se 1 (by rfl) ⟨591164, by rfl⟩ : syracuseStep 788219 = 1182329) B1182329
theorem B755615 : Blo 346754 755615 := bstep (se 1 (by rfl) ⟨566711, by rfl⟩ : syracuseStep 755615 = 1133423) B1133423
theorem B11339837 : Blo 346754 11339837 := bstep (se 3 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 11339837 = 4252439) B4252439
theorem B788687 : Blo 346754 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B788705 : Blo 346754 788705 := bstep (se 2 (by rfl) ⟨295764, by rfl⟩ : syracuseStep 788705 = 591529) B591529
theorem B625927 : Blo 346754 625927 := bstep (se 1 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 625927 = 938891) B938891
theorem B1708199 : Blo 346754 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B3805915 : Blo 346754 3805915 := bstep (se 1 (by rfl) ⟨2854436, by rfl⟩ : syracuseStep 3805915 = 5708873) B5708873
theorem B661439 : Blo 346754 661439 := bstep (se 1 (by rfl) ⟨496079, by rfl⟩ : syracuseStep 661439 = 992159) B992159
theorem B498431 : Blo 346754 498431 := bstep (se 1 (by rfl) ⟨373823, by rfl⟩ : syracuseStep 498431 = 747647) B747647
theorem B662555 : Blo 346754 662555 := bstep (se 1 (by rfl) ⟨496916, by rfl⟩ : syracuseStep 662555 = 993833) B993833
theorem B10755119 : Blo 346754 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B630107 : Blo 346754 630107 := bstep (se 1 (by rfl) ⟨472580, by rfl⟩ : syracuseStep 630107 = 945161) B945161
theorem B1318625 : Blo 346754 1318625 := bstep (se 2 (by rfl) ⟨494484, by rfl⟩ : syracuseStep 1318625 = 988969) B988969
theorem B2827433 : Blo 346754 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B501481 : Blo 346754 501481 := bstep (se 2 (by rfl) ⟨188055, by rfl⟩ : syracuseStep 501481 = 376111) B376111
theorem B370543 : Blo 346754 370543 := bstep (se 1 (by rfl) ⟨277907, by rfl⟩ : syracuseStep 370543 = 555815) B555815
theorem B1255657 : Blo 346754 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B1485179 : Blo 346754 1485179 := bstep (se 1 (by rfl) ⟨1113884, by rfl⟩ : syracuseStep 1485179 = 2227769) B2227769
theorem B1289981 : Blo 346754 1289981 := bstep (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) B483743
theorem B3977423 : Blo 346754 3977423 := bstep (se 1 (by rfl) ⟨2983067, by rfl⟩ : syracuseStep 3977423 = 5966135) B5966135
theorem B1324457 : Blo 346754 1324457 := bstep (se 2 (by rfl) ⟨496671, by rfl⟩ : syracuseStep 1324457 = 993343) B993343
theorem B2538215 : Blo 346754 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B8469841 : Blo 346754 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B11255759 : Blo 346754 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B443495 : Blo 346754 443495 := bstep (se 1 (by rfl) ⟨332621, by rfl⟩ : syracuseStep 443495 = 665243) B665243
theorem B1492253 : Blo 346754 1492253 := bstep (se 3 (by rfl) ⟨279797, by rfl⟩ : syracuseStep 1492253 = 559595) B559595
theorem B6014843 : Blo 346754 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B1002095 : Blo 346754 1002095 := bstep (se 1 (by rfl) ⟨751571, by rfl⟩ : syracuseStep 1002095 = 1503143) B1503143
theorem B346875 : Blo 346754 346875 := bstep (se 1 (by rfl) ⟨260156, by rfl⟩ : syracuseStep 346875 = 520313) B520313
theorem B346907 : Blo 346754 346907 := bstep (se 1 (by rfl) ⟨260180, by rfl⟩ : syracuseStep 346907 = 520361) B520361
theorem B347119 : Blo 346754 347119 := bstep (se 1 (by rfl) ⟨260339, by rfl⟩ : syracuseStep 347119 = 520679) B520679
theorem B347419 : Blo 346754 347419 := bstep (se 1 (by rfl) ⟨260564, by rfl⟩ : syracuseStep 347419 = 521129) B521129
theorem B347631 : Blo 346754 347631 := bstep (se 1 (by rfl) ⟨260723, by rfl⟩ : syracuseStep 347631 = 521447) B521447
theorem B347679 : Blo 346754 347679 := bstep (se 1 (by rfl) ⟨260759, by rfl⟩ : syracuseStep 347679 = 521519) B521519
theorem B970459 : Blo 346754 970459 := bstep (se 1 (by rfl) ⟨727844, by rfl⟩ : syracuseStep 970459 = 1455689) B1455689
theorem B348071 : Blo 346754 348071 := bstep (se 1 (by rfl) ⟨261053, by rfl⟩ : syracuseStep 348071 = 522107) B522107
theorem B708563 : Blo 346754 708563 := bstep (se 1 (by rfl) ⟨531422, by rfl⟩ : syracuseStep 708563 = 1062845) B1062845
theorem B348251 : Blo 346754 348251 := bstep (se 1 (by rfl) ⟨261188, by rfl⟩ : syracuseStep 348251 = 522377) B522377
theorem B348319 : Blo 346754 348319 := bstep (se 1 (by rfl) ⟨261239, by rfl⟩ : syracuseStep 348319 = 522479) B522479
theorem B348479 : Blo 346754 348479 := bstep (se 1 (by rfl) ⟨261359, by rfl⟩ : syracuseStep 348479 = 522719) B522719
theorem B348575 : Blo 346754 348575 := bstep (se 1 (by rfl) ⟨261431, by rfl⟩ : syracuseStep 348575 = 522863) B522863
theorem B348839 : Blo 346754 348839 := bstep (se 1 (by rfl) ⟨261629, by rfl⟩ : syracuseStep 348839 = 523259) B523259
theorem B1496303 : Blo 346754 1496303 := bstep (se 1 (by rfl) ⟨1122227, by rfl⟩ : syracuseStep 1496303 = 2244455) B2244455
theorem B349543 : Blo 346754 349543 := bstep (se 1 (by rfl) ⟨262157, by rfl⟩ : syracuseStep 349543 = 524315) B524315
theorem B2119193 : Blo 346754 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B350055 : Blo 346754 350055 := bstep (se 1 (by rfl) ⟨262541, by rfl⟩ : syracuseStep 350055 = 525083) B525083
theorem B350239 : Blo 346754 350239 := bstep (se 1 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 350239 = 525359) B525359
theorem B18209123 : Blo 346754 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B1759643 : Blo 346754 1759643 := bstep (se 1 (by rfl) ⟨1319732, by rfl⟩ : syracuseStep 1759643 = 2639465) B2639465
theorem B350655 : Blo 346754 350655 := bstep (se 1 (by rfl) ⟨262991, by rfl⟩ : syracuseStep 350655 = 525983) B525983
theorem B744623 : Blo 346754 744623 := bstep (se 1 (by rfl) ⟨558467, by rfl⟩ : syracuseStep 744623 = 1116935) B1116935
theorem B3169631 : Blo 346754 3169631 := bstep (se 1 (by rfl) ⟨2377223, by rfl⟩ : syracuseStep 3169631 = 4754447) B4754447
theorem B2121551 : Blo 346754 2121551 := bstep (se 1 (by rfl) ⟨1591163, by rfl⟩ : syracuseStep 2121551 = 3182327) B3182327
theorem B1991263 : Blo 346754 1991263 := bstep (se 1 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 1991263 = 2986895) B2986895
theorem B46883711 : Blo 346754 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B1598591 : Blo 346754 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B746759 : Blo 346754 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B5662133 : Blo 346754 5662133 := bstep (se 5 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 5662133 = 530825) B530825
theorem B2091419 : Blo 346754 2091419 := bstep (se 1 (by rfl) ⟨1568564, by rfl⟩ : syracuseStep 2091419 = 3137129) B3137129
theorem B747947 : Blo 346754 747947 := bstep (se 1 (by rfl) ⟨560960, by rfl⟩ : syracuseStep 747947 = 1121921) B1121921
theorem B781055 : Blo 346754 781055 := bstep (se 1 (by rfl) ⟨585791, by rfl⟩ : syracuseStep 781055 = 1171583) B1171583
theorem B4484443 : Blo 346754 4484443 := bstep (se 1 (by rfl) ⟨3363332, by rfl⟩ : syracuseStep 4484443 = 6726665) B6726665
theorem B781775 : Blo 346754 781775 := bstep (se 1 (by rfl) ⟨586331, by rfl⟩ : syracuseStep 781775 = 1172663) B1172663
theorem B781991 : Blo 346754 781991 := bstep (se 1 (by rfl) ⟨586493, by rfl⟩ : syracuseStep 781991 = 1172987) B1172987
theorem B36138899 : Blo 346754 36138899 := bstep (se 1 (by rfl) ⟨27104174, by rfl⟩ : syracuseStep 36138899 = 54208349) B54208349
theorem B1831567 : Blo 346754 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B586399 : Blo 346754 586399 := bstep (se 1 (by rfl) ⟨439799, by rfl⟩ : syracuseStep 586399 = 879599) B879599
theorem B2224847 : Blo 346754 2224847 := bstep (se 1 (by rfl) ⟨1668635, by rfl⟩ : syracuseStep 2224847 = 3337271) B3337271
theorem B1667827 : Blo 346754 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B520991 : Blo 346754 520991 := bstep (se 1 (by rfl) ⟨390743, by rfl⟩ : syracuseStep 520991 = 781487) B781487
theorem B1176713 : Blo 346754 1176713 := bstep (se 2 (by rfl) ⟨441267, by rfl⟩ : syracuseStep 1176713 = 882535) B882535
theorem B521471 : Blo 346754 521471 := bstep (se 1 (by rfl) ⟨391103, by rfl⟩ : syracuseStep 521471 = 782207) B782207
theorem B587135 : Blo 346754 587135 := bstep (se 1 (by rfl) ⟨440351, by rfl⟩ : syracuseStep 587135 = 880703) B880703
theorem B522011 : Blo 346754 522011 := bstep (se 1 (by rfl) ⟨391508, by rfl⟩ : syracuseStep 522011 = 783017) B783017
theorem B14383507 : Blo 346754 14383507 := bstep (se 1 (by rfl) ⟨10787630, by rfl⟩ : syracuseStep 14383507 = 21575261) B21575261
theorem B2980745 : Blo 346754 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B392575 : Blo 346754 392575 := bstep (se 1 (by rfl) ⟨294431, by rfl⟩ : syracuseStep 392575 = 588863) B588863
theorem B884591 : Blo 346754 884591 := bstep (se 1 (by rfl) ⟨663443, by rfl⟩ : syracuseStep 884591 = 1326887) B1326887
theorem B1179791 : Blo 346754 1179791 := bstep (se 1 (by rfl) ⟨884843, by rfl⟩ : syracuseStep 1179791 = 1769687) B1769687
theorem B1180385 : Blo 346754 1180385 := bstep (se 2 (by rfl) ⟨442644, by rfl⟩ : syracuseStep 1180385 = 885289) B885289
theorem B2655017 : Blo 346754 2655017 := bstep (se 2 (by rfl) ⟨995631, by rfl⟩ : syracuseStep 2655017 = 1991263) B1991263
theorem B525215 : Blo 346754 525215 := bstep (se 1 (by rfl) ⟨393911, by rfl⟩ : syracuseStep 525215 = 787823) B787823
theorem B1180655 : Blo 346754 1180655 := bstep (se 1 (by rfl) ⟨885491, by rfl⟩ : syracuseStep 1180655 = 1770983) B1770983
theorem B525479 : Blo 346754 525479 := bstep (se 1 (by rfl) ⟨394109, by rfl⟩ : syracuseStep 525479 = 788219) B788219
theorem B525791 : Blo 346754 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B525803 : Blo 346754 525803 := bstep (se 1 (by rfl) ⟨394352, by rfl⟩ : syracuseStep 525803 = 788705) B788705
theorem B494057 : Blo 346754 494057 := bstep (se 2 (by rfl) ⟨185271, by rfl⟩ : syracuseStep 494057 = 370543) B370543
theorem B1182653 : Blo 346754 1182653 := bstep (se 3 (by rfl) ⟨221747, by rfl⟩ : syracuseStep 1182653 = 443495) B443495
theorem B1674209 : Blo 346754 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B1412795 : Blo 346754 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B496415 : Blo 346754 496415 := bstep (se 1 (by rfl) ⟨372311, by rfl⟩ : syracuseStep 496415 = 744623) B744623
theorem B1414367 : Blo 346754 1414367 := bstep (se 1 (by rfl) ⟨1060775, by rfl⟩ : syracuseStep 1414367 = 2121551) B2121551
theorem B497839 : Blo 346754 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B3774755 : Blo 346754 3774755 := bstep (se 1 (by rfl) ⟨2831066, by rfl⟩ : syracuseStep 3774755 = 5662133) B5662133
theorem B990119 : Blo 346754 990119 := bstep (se 1 (by rfl) ⟨742589, by rfl⟩ : syracuseStep 990119 = 1485179) B1485179
theorem B498631 : Blo 346754 498631 := bstep (se 1 (by rfl) ⟨373973, by rfl⟩ : syracuseStep 498631 = 747947) B747947
theorem B28680317 : Blo 346754 28680317 := bstep (se 3 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 28680317 = 10755119) B10755119
theorem B1483231 : Blo 346754 1483231 := bstep (se 1 (by rfl) ⟨1112423, by rfl⟩ : syracuseStep 1483231 = 2224847) B2224847
theorem B19178009 : Blo 346754 19178009 := bstep (se 2 (by rfl) ⟨7191753, by rfl⟩ : syracuseStep 19178009 = 14383507) B14383507
theorem B994835 : Blo 346754 994835 := bstep (se 1 (by rfl) ⟨746126, by rfl⟩ : syracuseStep 994835 = 1492253) B1492253
theorem B4009895 : Blo 346754 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B503743 : Blo 346754 503743 := bstep (se 1 (by rfl) ⟨377807, by rfl⟩ : syracuseStep 503743 = 755615) B755615
theorem B668063 : Blo 346754 668063 := bstep (se 1 (by rfl) ⟨501047, by rfl⟩ : syracuseStep 668063 = 1002095) B1002095
theorem B472375 : Blo 346754 472375 := bstep (se 1 (by rfl) ⟨354281, by rfl⟩ : syracuseStep 472375 = 708563) B708563
theorem B997535 : Blo 346754 997535 := bstep (se 1 (by rfl) ⟨748151, by rfl⟩ : syracuseStep 997535 = 1496303) B1496303
theorem B440959 : Blo 346754 440959 := bstep (se 1 (by rfl) ⟨330719, by rfl⟩ : syracuseStep 440959 = 661439) B661439
theorem B12139415 : Blo 346754 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B834569 : Blo 346754 834569 := bstep (se 2 (by rfl) ⟨312963, by rfl⟩ : syracuseStep 834569 = 625927) B625927
theorem B5979257 : Blo 346754 5979257 := bstep (se 2 (by rfl) ⟨2242221, by rfl⟩ : syracuseStep 5979257 = 4484443) B4484443
theorem B441703 : Blo 346754 441703 := bstep (se 1 (by rfl) ⟨331277, by rfl⟩ : syracuseStep 441703 = 662555) B662555
theorem B2113087 : Blo 346754 2113087 := bstep (se 1 (by rfl) ⟨1584815, by rfl⟩ : syracuseStep 2113087 = 3169631) B3169631
theorem B1065727 : Blo 346754 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B1884955 : Blo 346754 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B2442089 : Blo 346754 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B1394279 : Blo 346754 1394279 := bstep (se 1 (by rfl) ⟨1045709, by rfl⟩ : syracuseStep 1394279 = 2091419) B2091419
theorem B1329149 : Blo 346754 1329149 := bstep (se 3 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 1329149 = 498431) B498431
theorem B347327 : Blo 346754 347327 := bstep (se 1 (by rfl) ⟨260495, by rfl⟩ : syracuseStep 347327 = 520991) B520991
theorem B347647 : Blo 346754 347647 := bstep (se 1 (by rfl) ⟨260735, by rfl⟩ : syracuseStep 347647 = 521471) B521471
theorem B348007 : Blo 346754 348007 := bstep (se 1 (by rfl) ⟨261005, by rfl⟩ : syracuseStep 348007 = 522011) B522011
theorem B2674565 : Blo 346754 2674565 := bstep (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) B501481
theorem B11293121 : Blo 346754 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B1692143 : Blo 346754 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B1987163 : Blo 346754 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B349723 : Blo 346754 349723 := bstep (se 1 (by rfl) ⟨262292, by rfl⟩ : syracuseStep 349723 = 524585) B524585
theorem B349855 : Blo 346754 349855 := bstep (se 1 (by rfl) ⟨262391, by rfl⟩ : syracuseStep 349855 = 524783) B524783
theorem B349927 : Blo 346754 349927 := bstep (se 1 (by rfl) ⟨262445, by rfl⟩ : syracuseStep 349927 = 524891) B524891
theorem B350447 : Blo 346754 350447 := bstep (se 1 (by rfl) ⟨262835, by rfl⟩ : syracuseStep 350447 = 525671) B525671
theorem B743735 : Blo 346754 743735 := bstep (se 1 (by rfl) ⟨557801, by rfl⟩ : syracuseStep 743735 = 1115603) B1115603
theorem B7559891 : Blo 346754 7559891 := bstep (se 1 (by rfl) ⟨5669918, by rfl⟩ : syracuseStep 7559891 = 11339837) B11339837
theorem B1138799 : Blo 346754 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B1173095 : Blo 346754 1173095 := bstep (se 1 (by rfl) ⟨879821, by rfl⟩ : syracuseStep 1173095 = 1759643) B1759643
theorem B20703125 : Blo 346754 20703125 := bstep (se 6 (by rfl) ⟨485229, by rfl⟩ : syracuseStep 20703125 = 970459) B970459
theorem B420071 : Blo 346754 420071 := bstep (se 1 (by rfl) ⟨315053, by rfl⟩ : syracuseStep 420071 = 630107) B630107
theorem B879083 : Blo 346754 879083 := bstep (se 1 (by rfl) ⟨659312, by rfl⟩ : syracuseStep 879083 = 1318625) B1318625
theorem B31255807 : Blo 346754 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B781865 : Blo 346754 781865 := bstep (se 2 (by rfl) ⟨293199, by rfl⟩ : syracuseStep 781865 = 586399) B586399
theorem B5074553 : Blo 346754 5074553 := bstep (se 2 (by rfl) ⟨1902957, by rfl⟩ : syracuseStep 5074553 = 3805915) B3805915
theorem B2223769 : Blo 346754 2223769 := bstep (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) B1667827
theorem B520703 : Blo 346754 520703 := bstep (se 1 (by rfl) ⟨390527, by rfl⟩ : syracuseStep 520703 = 781055) B781055
theorem B521183 : Blo 346754 521183 := bstep (se 1 (by rfl) ⟨390887, by rfl⟩ : syracuseStep 521183 = 781775) B781775
theorem B521327 : Blo 346754 521327 := bstep (se 1 (by rfl) ⟨390995, by rfl⟩ : syracuseStep 521327 = 781991) B781991
theorem B2651615 : Blo 346754 2651615 := bstep (se 1 (by rfl) ⟨1988711, by rfl⟩ : syracuseStep 2651615 = 3977423) B3977423
theorem B784475 : Blo 346754 784475 := bstep (se 1 (by rfl) ⟨588356, by rfl⟩ : syracuseStep 784475 = 1176713) B1176713
theorem B391423 : Blo 346754 391423 := bstep (se 1 (by rfl) ⟨293567, by rfl⟩ : syracuseStep 391423 = 587135) B587135
theorem B882971 : Blo 346754 882971 := bstep (se 1 (by rfl) ⟨662228, by rfl⟩ : syracuseStep 882971 = 1324457) B1324457
theorem B523433 : Blo 346754 523433 := bstep (se 2 (by rfl) ⟨196287, by rfl⟩ : syracuseStep 523433 = 392575) B392575
theorem B3439949 : Blo 346754 3439949 := bstep (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) B1289981
theorem B96370397 : Blo 346754 96370397 := bstep (se 3 (by rfl) ⟨18069449, by rfl⟩ : syracuseStep 96370397 = 36138899) B36138899
theorem B589727 : Blo 346754 589727 := bstep (se 1 (by rfl) ⟨442295, by rfl⟩ : syracuseStep 589727 = 884591) B884591
theorem B7503839 : Blo 346754 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B786527 : Blo 346754 786527 := bstep (se 1 (by rfl) ⟨589895, by rfl⟩ : syracuseStep 786527 = 1179791) B1179791
theorem B786923 : Blo 346754 786923 := bstep (se 1 (by rfl) ⟨590192, by rfl⟩ : syracuseStep 786923 = 1180385) B1180385
theorem B1770011 : Blo 346754 1770011 := bstep (se 1 (by rfl) ⟨1327508, by rfl⟩ : syracuseStep 1770011 = 2655017) B2655017
theorem B787103 : Blo 346754 787103 := bstep (se 1 (by rfl) ⟨590327, by rfl⟩ : syracuseStep 787103 = 1180655) B1180655
theorem B30114989 : Blo 346754 30114989 := bstep (se 3 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 30114989 = 11293121) B11293121
theorem B886099 : Blo 346754 886099 := bstep (se 1 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 886099 = 1329149) B1329149
theorem B788435 : Blo 346754 788435 := bstep (se 1 (by rfl) ⟨591326, by rfl⟩ : syracuseStep 788435 = 1182653) B1182653
theorem B495823 : Blo 346754 495823 := bstep (se 1 (by rfl) ⟨371867, by rfl⟩ : syracuseStep 495823 = 743735) B743735
theorem B660079 : Blo 346754 660079 := bstep (se 1 (by rfl) ⟨495059, by rfl⟩ : syracuseStep 660079 = 990119) B990119
theorem B12785339 : Blo 346754 12785339 := bstep (se 1 (by rfl) ⟨9589004, by rfl⟩ : syracuseStep 12785339 = 19178009) B19178009
theorem B1120189 : Blo 346754 1120189 := bstep (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) B420071
theorem B13802083 : Blo 346754 13802083 := bstep (se 1 (by rfl) ⟨10351562, by rfl⟩ : syracuseStep 13802083 = 20703125) B20703125
theorem B1317485 : Blo 346754 1317485 := bstep (se 3 (by rfl) ⟨247028, by rfl⟩ : syracuseStep 1317485 = 494057) B494057
theorem B663223 : Blo 346754 663223 := bstep (se 1 (by rfl) ⟨497417, by rfl⟩ : syracuseStep 663223 = 994835) B994835
theorem B3383035 : Blo 346754 3383035 := bstep (se 1 (by rfl) ⟨2537276, by rfl⟩ : syracuseStep 3383035 = 5074553) B5074553
theorem B4464557 : Blo 346754 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B663785 : Blo 346754 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B664841 : Blo 346754 664841 := bstep (se 2 (by rfl) ⟨249315, by rfl⟩ : syracuseStep 664841 = 498631) B498631
theorem B665023 : Blo 346754 665023 := bstep (se 1 (by rfl) ⟨498767, by rfl⟩ : syracuseStep 665023 = 997535) B997535
theorem B1977641 : Blo 346754 1977641 := bstep (se 2 (by rfl) ⟨741615, by rfl⟩ : syracuseStep 1977641 = 1483231) B1483231
theorem B929519 : Blo 346754 929519 := bstep (se 1 (by rfl) ⟨697139, by rfl⟩ : syracuseStep 929519 = 1394279) B1394279
theorem B1323773 : Blo 346754 1323773 := bstep (se 3 (by rfl) ⟨248207, by rfl⟩ : syracuseStep 1323773 = 496415) B496415
theorem B1783043 : Blo 346754 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B1128095 : Blo 346754 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B1324775 : Blo 346754 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B5683877 : Blo 346754 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B2965025 : Blo 346754 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B671657 : Blo 346754 671657 := bstep (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) B503743
theorem B19120211 : Blo 346754 19120211 := bstep (se 1 (by rfl) ⟨14340158, by rfl⟩ : syracuseStep 19120211 = 28680317) B28680317
theorem B2673263 : Blo 346754 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B445375 : Blo 346754 445375 := bstep (se 1 (by rfl) ⟨334031, by rfl⟩ : syracuseStep 445375 = 668063) B668063
theorem B347135 : Blo 346754 347135 := bstep (se 1 (by rfl) ⟨260351, by rfl⟩ : syracuseStep 347135 = 520703) B520703
theorem B347455 : Blo 346754 347455 := bstep (se 1 (by rfl) ⟨260591, by rfl⟩ : syracuseStep 347455 = 521183) B521183
theorem B347551 : Blo 346754 347551 := bstep (se 1 (by rfl) ⟨260663, by rfl⟩ : syracuseStep 347551 = 521327) B521327
theorem B3986171 : Blo 346754 3986171 := bstep (se 1 (by rfl) ⟨2989628, by rfl⟩ : syracuseStep 3986171 = 5979257) B5979257
theorem B348955 : Blo 346754 348955 := bstep (se 1 (by rfl) ⟨261716, by rfl⟩ : syracuseStep 348955 = 523433) B523433
theorem B64246931 : Blo 346754 64246931 := bstep (se 1 (by rfl) ⟨48185198, by rfl⟩ : syracuseStep 64246931 = 96370397) B96370397
theorem B5002559 : Blo 346754 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B3036797 : Blo 346754 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B1628059 : Blo 346754 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B350143 : Blo 346754 350143 := bstep (se 1 (by rfl) ⟨262607, by rfl⟩ : syracuseStep 350143 = 525215) B525215
theorem B350319 : Blo 346754 350319 := bstep (se 1 (by rfl) ⟨262739, by rfl⟩ : syracuseStep 350319 = 525479) B525479
theorem B350527 : Blo 346754 350527 := bstep (se 1 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 350527 = 525791) B525791
theorem B350535 : Blo 346754 350535 := bstep (se 1 (by rfl) ⟨262901, by rfl⟩ : syracuseStep 350535 = 525803) B525803
theorem B2513273 : Blo 346754 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B941863 : Blo 346754 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B942911 : Blo 346754 942911 := bstep (se 1 (by rfl) ⟨707183, by rfl⟩ : syracuseStep 942911 = 1414367) B1414367
theorem B2516503 : Blo 346754 2516503 := bstep (se 1 (by rfl) ⟨1887377, by rfl⟩ : syracuseStep 2516503 = 3774755) B3774755
theorem B41674409 : Blo 346754 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B5039927 : Blo 346754 5039927 := bstep (se 1 (by rfl) ⟨3779945, by rfl⟩ : syracuseStep 5039927 = 7559891) B7559891
theorem B782063 : Blo 346754 782063 := bstep (se 1 (by rfl) ⟨586547, by rfl⟩ : syracuseStep 782063 = 1173095) B1173095
theorem B2519333 : Blo 346754 2519333 := bstep (se 4 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 2519333 = 472375) B472375
theorem B586055 : Blo 346754 586055 := bstep (se 1 (by rfl) ⟨439541, by rfl⟩ : syracuseStep 586055 = 879083) B879083
theorem B521243 : Blo 346754 521243 := bstep (se 1 (by rfl) ⟨390932, by rfl⟩ : syracuseStep 521243 = 781865) B781865
theorem B521897 : Blo 346754 521897 := bstep (se 2 (by rfl) ⟨195711, by rfl⟩ : syracuseStep 521897 = 391423) B391423
theorem B587945 : Blo 346754 587945 := bstep (se 2 (by rfl) ⟨220479, by rfl⟩ : syracuseStep 587945 = 440959) B440959
theorem B9173197 : Blo 346754 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B1767743 : Blo 346754 1767743 := bstep (se 1 (by rfl) ⟨1325807, by rfl⟩ : syracuseStep 1767743 = 2651615) B2651615
theorem B522983 : Blo 346754 522983 := bstep (se 1 (by rfl) ⟨392237, by rfl⟩ : syracuseStep 522983 = 784475) B784475
theorem B588647 : Blo 346754 588647 := bstep (se 1 (by rfl) ⟨441485, by rfl⟩ : syracuseStep 588647 = 882971) B882971
theorem B588937 : Blo 346754 588937 := bstep (se 2 (by rfl) ⟨220851, by rfl⟩ : syracuseStep 588937 = 441703) B441703
theorem B8092943 : Blo 346754 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B556379 : Blo 346754 556379 := bstep (se 1 (by rfl) ⟨417284, by rfl⟩ : syracuseStep 556379 = 834569) B834569
theorem B2817449 : Blo 346754 2817449 := bstep (se 2 (by rfl) ⟨1056543, by rfl⟩ : syracuseStep 2817449 = 2113087) B2113087
theorem B393151 : Blo 346754 393151 := bstep (se 1 (by rfl) ⟨294863, by rfl⟩ : syracuseStep 393151 = 589727) B589727
theorem B12746807 : Blo 346754 12746807 := bstep (se 1 (by rfl) ⟨9560105, by rfl⟩ : syracuseStep 12746807 = 19120211) B19120211
theorem B524351 : Blo 346754 524351 := bstep (se 1 (by rfl) ⟨393263, by rfl⟩ : syracuseStep 524351 = 786527) B786527
theorem B524615 : Blo 346754 524615 := bstep (se 1 (by rfl) ⟨393461, by rfl⟩ : syracuseStep 524615 = 786923) B786923
theorem B1180007 : Blo 346754 1180007 := bstep (se 1 (by rfl) ⟨885005, by rfl⟩ : syracuseStep 1180007 = 1770011) B1770011
theorem B524735 : Blo 346754 524735 := bstep (se 1 (by rfl) ⟨393551, by rfl⟩ : syracuseStep 524735 = 787103) B787103
theorem B525623 : Blo 346754 525623 := bstep (se 1 (by rfl) ⟨394217, by rfl⟩ : syracuseStep 525623 = 788435) B788435
theorem B1181465 : Blo 346754 1181465 := bstep (se 2 (by rfl) ⟨443049, by rfl⟩ : syracuseStep 1181465 = 886099) B886099
theorem B886697 : Blo 346754 886697 := bstep (se 2 (by rfl) ⟨332511, by rfl⟩ : syracuseStep 886697 = 665023) B665023
theorem B2657447 : Blo 346754 2657447 := bstep (se 1 (by rfl) ⟨1993085, by rfl⟩ : syracuseStep 2657447 = 3986171) B3986171
theorem B42831287 : Blo 346754 42831287 := bstep (se 1 (by rfl) ⟨32123465, by rfl⟩ : syracuseStep 42831287 = 64246931) B64246931
theorem B8523559 : Blo 346754 8523559 := bstep (se 1 (by rfl) ⟨6392669, by rfl⟩ : syracuseStep 8523559 = 12785339) B12785339
theorem B661097 : Blo 346754 661097 := bstep (se 2 (by rfl) ⟨247911, by rfl⟩ : syracuseStep 661097 = 495823) B495823
theorem B628607 : Blo 346754 628607 := bstep (se 1 (by rfl) ⟨471455, by rfl⟩ : syracuseStep 628607 = 942911) B942911
theorem B1318427 : Blo 346754 1318427 := bstep (se 1 (by rfl) ⟨988820, by rfl⟩ : syracuseStep 1318427 = 1977641) B1977641
theorem B2170745 : Blo 346754 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B1679555 : Blo 346754 1679555 := bstep (se 1 (by rfl) ⟨1259666, by rfl⟩ : syracuseStep 1679555 = 2519333) B2519333
theorem B12230929 : Blo 346754 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B1188695 : Blo 346754 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B370919 : Blo 346754 370919 := bstep (se 1 (by rfl) ⟨278189, by rfl⟩ : syracuseStep 370919 = 556379) B556379
theorem B1878299 : Blo 346754 1878299 := bstep (se 1 (by rfl) ⟨1408724, by rfl⟩ : syracuseStep 1878299 = 2817449) B2817449
theorem B1976683 : Blo 346754 1976683 := bstep (se 1 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 1976683 = 2965025) B2965025
theorem B1255817 : Blo 346754 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B1782175 : Blo 346754 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B3355337 : Blo 346754 3355337 := bstep (se 2 (by rfl) ⟨1258251, by rfl⟩ : syracuseStep 3355337 = 2516503) B2516503
theorem B73611109 : Blo 346754 73611109 := bstep (se 4 (by rfl) ⟨6901041, by rfl⟩ : syracuseStep 73611109 = 13802083) B13802083
theorem B2375333 : Blo 346754 2375333 := bstep (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) B445375
theorem B442523 : Blo 346754 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B443227 : Blo 346754 443227 := bstep (se 1 (by rfl) ⟨332420, by rfl⟩ : syracuseStep 443227 = 664841) B664841
theorem B6702061 : Blo 346754 6702061 := bstep (se 3 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 6702061 = 2513273) B2513273
theorem B3359951 : Blo 346754 3359951 := bstep (se 1 (by rfl) ⟨2519963, by rfl⟩ : syracuseStep 3359951 = 5039927) B5039927
theorem B1493585 : Blo 346754 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B347495 : Blo 346754 347495 := bstep (se 1 (by rfl) ⟨260621, by rfl⟩ : syracuseStep 347495 = 521243) B521243
theorem B347931 : Blo 346754 347931 := bstep (se 1 (by rfl) ⟨260948, by rfl⟩ : syracuseStep 347931 = 521897) B521897
theorem B18042853 : Blo 346754 18042853 := bstep (se 4 (by rfl) ⟨1691517, by rfl⟩ : syracuseStep 18042853 = 3383035) B3383035
theorem B3789251 : Blo 346754 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B348655 : Blo 346754 348655 := bstep (se 1 (by rfl) ⟨261491, by rfl⟩ : syracuseStep 348655 = 522983) B522983
theorem B5395295 : Blo 346754 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B1791085 : Blo 346754 1791085 := bstep (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) B671657
theorem B20076659 : Blo 346754 20076659 := bstep (se 1 (by rfl) ⟨15057494, by rfl⟩ : syracuseStep 20076659 = 30114989) B30114989
theorem B3335039 : Blo 346754 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B2024531 : Blo 346754 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B878323 : Blo 346754 878323 := bstep (se 1 (by rfl) ⟨658742, by rfl⟩ : syracuseStep 878323 = 1317485) B1317485
theorem B2976371 : Blo 346754 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B880105 : Blo 346754 880105 := bstep (se 2 (by rfl) ⟨330039, by rfl⟩ : syracuseStep 880105 = 660079) B660079
theorem B27782939 : Blo 346754 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B521375 : Blo 346754 521375 := bstep (se 1 (by rfl) ⟨391031, by rfl⟩ : syracuseStep 521375 = 782063) B782063
theorem B619679 : Blo 346754 619679 := bstep (se 1 (by rfl) ⟨464759, by rfl⟩ : syracuseStep 619679 = 929519) B929519
theorem B390703 : Blo 346754 390703 := bstep (se 1 (by rfl) ⟨293027, by rfl⟩ : syracuseStep 390703 = 586055) B586055
theorem B882515 : Blo 346754 882515 := bstep (se 1 (by rfl) ⟨661886, by rfl⟩ : syracuseStep 882515 = 1323773) B1323773
theorem B752063 : Blo 346754 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B883183 : Blo 346754 883183 := bstep (se 1 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 883183 = 1324775) B1324775
theorem B391963 : Blo 346754 391963 := bstep (se 1 (by rfl) ⟨293972, by rfl⟩ : syracuseStep 391963 = 587945) B587945
theorem B785249 : Blo 346754 785249 := bstep (se 2 (by rfl) ⟨294468, by rfl⟩ : syracuseStep 785249 = 588937) B588937
theorem B1178495 : Blo 346754 1178495 := bstep (se 1 (by rfl) ⟨883871, by rfl⟩ : syracuseStep 1178495 = 1767743) B1767743
theorem B392431 : Blo 346754 392431 := bstep (se 1 (by rfl) ⟨294323, by rfl⟩ : syracuseStep 392431 = 588647) B588647
theorem B884297 : Blo 346754 884297 := bstep (se 2 (by rfl) ⟨331611, by rfl⟩ : syracuseStep 884297 = 663223) B663223
theorem B524201 : Blo 346754 524201 := bstep (se 2 (by rfl) ⟨196575, by rfl⟩ : syracuseStep 524201 = 393151) B393151
theorem B786671 : Blo 346754 786671 := bstep (se 1 (by rfl) ⟨590003, by rfl⟩ : syracuseStep 786671 = 1180007) B1180007
theorem B1180061 : Blo 346754 1180061 := bstep (se 3 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 1180061 = 442523) B442523
theorem B590969 : Blo 346754 590969 := bstep (se 2 (by rfl) ⟨221613, by rfl⟩ : syracuseStep 590969 = 443227) B443227
theorem B787643 : Blo 346754 787643 := bstep (se 1 (by rfl) ⟨590732, by rfl⟩ : syracuseStep 787643 = 1181465) B1181465
theorem B591131 : Blo 346754 591131 := bstep (se 1 (by rfl) ⟨443348, by rfl⟩ : syracuseStep 591131 = 886697) B886697
theorem B1771631 : Blo 346754 1771631 := bstep (se 1 (by rfl) ⟨1328723, by rfl⟩ : syracuseStep 1771631 = 2657447) B2657447
theorem B14387453 : Blo 346754 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B2526167 : Blo 346754 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B1676285 : Blo 346754 1676285 := bstep (se 3 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 1676285 = 628607) B628607
theorem B1447163 : Blo 346754 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B24057137 : Blo 346754 24057137 := bstep (se 2 (by rfl) ⟨9021426, by rfl⟩ : syracuseStep 24057137 = 18042853) B18042853
theorem B1119703 : Blo 346754 1119703 := bstep (se 1 (by rfl) ⟨839777, by rfl⟩ : syracuseStep 1119703 = 1679555) B1679555
theorem B989117 : Blo 346754 989117 := bstep (se 3 (by rfl) ⟨185459, by rfl⟩ : syracuseStep 989117 = 370919) B370919
theorem B1349687 : Blo 346754 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B2005501 : Blo 346754 2005501 := bstep (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) B752063
theorem B1252199 : Blo 346754 1252199 := bstep (se 1 (by rfl) ⟨939149, by rfl⟩ : syracuseStep 1252199 = 1878299) B1878299
theorem B98148145 : Blo 346754 98148145 := bstep (se 2 (by rfl) ⟨36805554, by rfl⟩ : syracuseStep 98148145 = 73611109) B73611109
theorem B18521959 : Blo 346754 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B2236891 : Blo 346754 2236891 := bstep (se 1 (by rfl) ⟨1677668, by rfl⟩ : syracuseStep 2236891 = 3355337) B3355337
theorem B1583555 : Blo 346754 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B8497871 : Blo 346754 8497871 := bstep (se 1 (by rfl) ⟨6373403, by rfl⟩ : syracuseStep 8497871 = 12746807) B12746807
theorem B2239967 : Blo 346754 2239967 := bstep (se 1 (by rfl) ⟨1679975, by rfl⟩ : syracuseStep 2239967 = 3359951) B3359951
theorem B995723 : Blo 346754 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B28554191 : Blo 346754 28554191 := bstep (se 1 (by rfl) ⟨21415643, by rfl⟩ : syracuseStep 28554191 = 42831287) B42831287
theorem B2635577 : Blo 346754 2635577 := bstep (se 2 (by rfl) ⟨988341, by rfl⟩ : syracuseStep 2635577 = 1976683) B1976683
theorem B440731 : Blo 346754 440731 := bstep (se 1 (by rfl) ⟨330548, by rfl⟩ : syracuseStep 440731 = 661097) B661097
theorem B13384439 : Blo 346754 13384439 := bstep (se 1 (by rfl) ⟨10038329, by rfl⟩ : syracuseStep 13384439 = 20076659) B20076659
theorem B2376233 : Blo 346754 2376233 := bstep (se 2 (by rfl) ⟨891087, by rfl⟩ : syracuseStep 2376233 = 1782175) B1782175
theorem B837211 : Blo 346754 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B1984247 : Blo 346754 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B347583 : Blo 346754 347583 := bstep (se 1 (by rfl) ⟨260687, by rfl⟩ : syracuseStep 347583 = 521375) B521375
theorem B413119 : Blo 346754 413119 := bstep (se 1 (by rfl) ⟨309839, by rfl⟩ : syracuseStep 413119 = 619679) B619679
theorem B349467 : Blo 346754 349467 := bstep (se 1 (by rfl) ⟨262100, by rfl⟩ : syracuseStep 349467 = 524201) B524201
theorem B349567 : Blo 346754 349567 := bstep (se 1 (by rfl) ⟨262175, by rfl⟩ : syracuseStep 349567 = 524351) B524351
theorem B349743 : Blo 346754 349743 := bstep (se 1 (by rfl) ⟨262307, by rfl⟩ : syracuseStep 349743 = 524615) B524615
theorem B349823 : Blo 346754 349823 := bstep (se 1 (by rfl) ⟨262367, by rfl⟩ : syracuseStep 349823 = 524735) B524735
theorem B16307905 : Blo 346754 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B350415 : Blo 346754 350415 := bstep (se 1 (by rfl) ⟨262811, by rfl⟩ : syracuseStep 350415 = 525623) B525623
theorem B8936081 : Blo 346754 8936081 := bstep (se 2 (by rfl) ⟨3351030, by rfl⟩ : syracuseStep 8936081 = 6702061) B6702061
theorem B3169853 : Blo 346754 3169853 := bstep (se 3 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 3169853 = 1188695) B1188695
theorem B1171097 : Blo 346754 1171097 := bstep (se 2 (by rfl) ⟨439161, by rfl⟩ : syracuseStep 1171097 = 878323) B878323
theorem B1173473 : Blo 346754 1173473 := bstep (se 2 (by rfl) ⟨440052, by rfl⟩ : syracuseStep 1173473 = 880105) B880105
theorem B878951 : Blo 346754 878951 := bstep (se 1 (by rfl) ⟨659213, by rfl⟩ : syracuseStep 878951 = 1318427) B1318427
theorem B11364745 : Blo 346754 11364745 := bstep (se 2 (by rfl) ⟨4261779, by rfl⟩ : syracuseStep 11364745 = 8523559) B8523559
theorem B2223359 : Blo 346754 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B2388113 : Blo 346754 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B520937 : Blo 346754 520937 := bstep (se 2 (by rfl) ⟨195351, by rfl⟩ : syracuseStep 520937 = 390703) B390703
theorem B1177577 : Blo 346754 1177577 := bstep (se 2 (by rfl) ⟨441591, by rfl⟩ : syracuseStep 1177577 = 883183) B883183
theorem B522617 : Blo 346754 522617 := bstep (se 2 (by rfl) ⟨195981, by rfl⟩ : syracuseStep 522617 = 391963) B391963
theorem B588343 : Blo 346754 588343 := bstep (se 1 (by rfl) ⟨441257, by rfl⟩ : syracuseStep 588343 = 882515) B882515
theorem B523241 : Blo 346754 523241 := bstep (se 2 (by rfl) ⟨196215, by rfl⟩ : syracuseStep 523241 = 392431) B392431
theorem B523499 : Blo 346754 523499 := bstep (se 1 (by rfl) ⟨392624, by rfl⟩ : syracuseStep 523499 = 785249) B785249
theorem B785663 : Blo 346754 785663 := bstep (se 1 (by rfl) ⟨589247, by rfl⟩ : syracuseStep 785663 = 1178495) B1178495
theorem B589531 : Blo 346754 589531 := bstep (se 1 (by rfl) ⟨442148, by rfl⟩ : syracuseStep 589531 = 884297) B884297
theorem B524447 : Blo 346754 524447 := bstep (se 1 (by rfl) ⟨393335, by rfl⟩ : syracuseStep 524447 = 786671) B786671
theorem B786707 : Blo 346754 786707 := bstep (se 1 (by rfl) ⟨590030, by rfl⟩ : syracuseStep 786707 = 1180061) B1180061
theorem B2982521 : Blo 346754 2982521 := bstep (se 2 (by rfl) ⟨1118445, by rfl⟩ : syracuseStep 2982521 = 2236891) B2236891
theorem B393979 : Blo 346754 393979 := bstep (se 1 (by rfl) ⟨295484, by rfl⟩ : syracuseStep 393979 = 590969) B590969
theorem B525095 : Blo 346754 525095 := bstep (se 1 (by rfl) ⟨393821, by rfl⟩ : syracuseStep 525095 = 787643) B787643
theorem B394087 : Blo 346754 394087 := bstep (se 1 (by rfl) ⟨295565, by rfl⟩ : syracuseStep 394087 = 591131) B591131
theorem B1181087 : Blo 346754 1181087 := bstep (se 1 (by rfl) ⟨885815, by rfl⟩ : syracuseStep 1181087 = 1771631) B1771631
theorem B1116281 : Blo 346754 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B1117523 : Blo 346754 1117523 := bstep (se 1 (by rfl) ⟨838142, by rfl⟩ : syracuseStep 1117523 = 1676285) B1676285
theorem B659411 : Blo 346754 659411 := bstep (se 1 (by rfl) ⟨494558, by rfl⟩ : syracuseStep 659411 = 989117) B989117
theorem B1482239 : Blo 346754 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B2203301 : Blo 346754 2203301 := bstep (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) B413119
theorem B663815 : Blo 346754 663815 := bstep (se 1 (by rfl) ⟨497861, by rfl⟩ : syracuseStep 663815 = 995723) B995723
theorem B8922959 : Blo 346754 8922959 := bstep (se 1 (by rfl) ⟨6692219, by rfl⟩ : syracuseStep 8922959 = 13384439) B13384439
theorem B1584155 : Blo 346754 1584155 := bstep (se 1 (by rfl) ⟨1188116, by rfl⟩ : syracuseStep 1584155 = 2376233) B2376233
theorem B1322831 : Blo 346754 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B1684111 : Blo 346754 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B15152993 : Blo 346754 15152993 := bstep (se 2 (by rfl) ⟨5682372, by rfl⟩ : syracuseStep 15152993 = 11364745) B11364745
theorem B964775 : Blo 346754 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B16038091 : Blo 346754 16038091 := bstep (se 1 (by rfl) ⟨12028568, by rfl⟩ : syracuseStep 16038091 = 24057137) B24057137
theorem B899791 : Blo 346754 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B834799 : Blo 346754 834799 := bstep (se 1 (by rfl) ⟨626099, by rfl⟩ : syracuseStep 834799 = 1252199) B1252199
theorem B2113235 : Blo 346754 2113235 := bstep (se 1 (by rfl) ⟨1584926, by rfl⟩ : syracuseStep 2113235 = 3169853) B3169853
theorem B1492937 : Blo 346754 1492937 := bstep (se 2 (by rfl) ⟨559851, by rfl⟩ : syracuseStep 1492937 = 1119703) B1119703
theorem B21743873 : Blo 346754 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B1493311 : Blo 346754 1493311 := bstep (se 1 (by rfl) ⟨1119983, by rfl⟩ : syracuseStep 1493311 = 2239967) B2239967
theorem B1592075 : Blo 346754 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B347291 : Blo 346754 347291 := bstep (se 1 (by rfl) ⟨260468, by rfl⟩ : syracuseStep 347291 = 520937) B520937
theorem B2674001 : Blo 346754 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B1757051 : Blo 346754 1757051 := bstep (se 1 (by rfl) ⟨1317788, by rfl⟩ : syracuseStep 1757051 = 2635577) B2635577
theorem B348411 : Blo 346754 348411 := bstep (se 1 (by rfl) ⟨261308, by rfl⟩ : syracuseStep 348411 = 522617) B522617
theorem B348827 : Blo 346754 348827 := bstep (se 1 (by rfl) ⟨261620, by rfl⟩ : syracuseStep 348827 = 523241) B523241
theorem B348999 : Blo 346754 348999 := bstep (se 1 (by rfl) ⟨261749, by rfl⟩ : syracuseStep 348999 = 523499) B523499
theorem B130864193 : Blo 346754 130864193 := bstep (se 2 (by rfl) ⟨49074072, by rfl⟩ : syracuseStep 130864193 = 98148145) B98148145
theorem B24695945 : Blo 346754 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B9591635 : Blo 346754 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B5957387 : Blo 346754 5957387 := bstep (se 1 (by rfl) ⟨4468040, by rfl⟩ : syracuseStep 5957387 = 8936081) B8936081
theorem B780731 : Blo 346754 780731 := bstep (se 1 (by rfl) ⟨585548, by rfl⟩ : syracuseStep 780731 = 1171097) B1171097
theorem B4222813 : Blo 346754 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B782315 : Blo 346754 782315 := bstep (se 1 (by rfl) ⟨586736, by rfl⟩ : syracuseStep 782315 = 1173473) B1173473
theorem B585967 : Blo 346754 585967 := bstep (se 1 (by rfl) ⟨439475, by rfl⟩ : syracuseStep 585967 = 878951) B878951
theorem B5665247 : Blo 346754 5665247 := bstep (se 1 (by rfl) ⟨4248935, by rfl⟩ : syracuseStep 5665247 = 8497871) B8497871
theorem B587641 : Blo 346754 587641 := bstep (se 2 (by rfl) ⟨220365, by rfl⟩ : syracuseStep 587641 = 440731) B440731
theorem B19036127 : Blo 346754 19036127 := bstep (se 1 (by rfl) ⟨14277095, by rfl⟩ : syracuseStep 19036127 = 28554191) B28554191
theorem B784457 : Blo 346754 784457 := bstep (se 2 (by rfl) ⟨294171, by rfl⟩ : syracuseStep 784457 = 588343) B588343
theorem B785051 : Blo 346754 785051 := bstep (se 1 (by rfl) ⟨588788, by rfl⟩ : syracuseStep 785051 = 1177577) B1177577
theorem B523775 : Blo 346754 523775 := bstep (se 1 (by rfl) ⟨392831, by rfl⟩ : syracuseStep 523775 = 785663) B785663
theorem B786041 : Blo 346754 786041 := bstep (se 2 (by rfl) ⟨294765, by rfl⟩ : syracuseStep 786041 = 589531) B589531
theorem B524471 : Blo 346754 524471 := bstep (se 1 (by rfl) ⟨393353, by rfl⟩ : syracuseStep 524471 = 786707) B786707
theorem B1770173 : Blo 346754 1770173 := bstep (se 3 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 1770173 = 663815) B663815
theorem B787391 : Blo 346754 787391 := bstep (se 1 (by rfl) ⟨590543, by rfl⟩ : syracuseStep 787391 = 1181087) B1181087
theorem B525305 : Blo 346754 525305 := bstep (se 2 (by rfl) ⟨196989, by rfl⟩ : syracuseStep 525305 = 393979) B393979
theorem B525449 : Blo 346754 525449 := bstep (se 2 (by rfl) ⟨197043, by rfl⟩ : syracuseStep 525449 = 394087) B394087
theorem B6394423 : Blo 346754 6394423 := bstep (se 1 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 6394423 = 9591635) B9591635
theorem B3971591 : Blo 346754 3971591 := bstep (se 1 (by rfl) ⟨2978693, by rfl⟩ : syracuseStep 3971591 = 5957387) B5957387
theorem B3776831 : Blo 346754 3776831 := bstep (se 1 (by rfl) ⟨2832623, by rfl⟩ : syracuseStep 3776831 = 5665247) B5665247
theorem B10101995 : Blo 346754 10101995 := bstep (se 1 (by rfl) ⟨7576496, by rfl⟩ : syracuseStep 10101995 = 15152993) B15152993
theorem B12690751 : Blo 346754 12690751 := bstep (se 1 (by rfl) ⟨9518063, by rfl⟩ : syracuseStep 12690751 = 19036127) B19036127
theorem B995291 : Blo 346754 995291 := bstep (se 1 (by rfl) ⟨746468, by rfl⟩ : syracuseStep 995291 = 1492937) B1492937
theorem B14495915 : Blo 346754 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B1782667 : Blo 346754 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B439607 : Blo 346754 439607 := bstep (se 1 (by rfl) ⟨329705, by rfl⟩ : syracuseStep 439607 = 659411) B659411
theorem B87242795 : Blo 346754 87242795 := bstep (se 1 (by rfl) ⟨65432096, by rfl⟩ : syracuseStep 87242795 = 130864193) B130864193
theorem B16463963 : Blo 346754 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B2245481 : Blo 346754 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B5948639 : Blo 346754 5948639 := bstep (se 1 (by rfl) ⟨4461479, by rfl⟩ : syracuseStep 5948639 = 8922959) B8922959
theorem B4245533 : Blo 346754 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B21384121 : Blo 346754 21384121 := bstep (se 2 (by rfl) ⟨8019045, by rfl⟩ : syracuseStep 21384121 = 16038091) B16038091
theorem B3952637 : Blo 346754 3952637 := bstep (se 3 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 3952637 = 1482239) B1482239
theorem B643183 : Blo 346754 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B349183 : Blo 346754 349183 := bstep (se 1 (by rfl) ⟨261887, by rfl⟩ : syracuseStep 349183 = 523775) B523775
theorem B349631 : Blo 346754 349631 := bstep (se 1 (by rfl) ⟨262223, by rfl⟩ : syracuseStep 349631 = 524447) B524447
theorem B1988347 : Blo 346754 1988347 := bstep (se 1 (by rfl) ⟨1491260, by rfl⟩ : syracuseStep 1988347 = 2982521) B2982521
theorem B350063 : Blo 346754 350063 := bstep (se 1 (by rfl) ⟨262547, by rfl⟩ : syracuseStep 350063 = 525095) B525095
theorem B1171367 : Blo 346754 1171367 := bstep (se 1 (by rfl) ⟨878525, by rfl⟩ : syracuseStep 1171367 = 1757051) B1757051
theorem B1991081 : Blo 346754 1991081 := bstep (se 2 (by rfl) ⟨746655, by rfl⟩ : syracuseStep 1991081 = 1493311) B1493311
theorem B19195541 : Blo 346754 19195541 := bstep (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) B899791
theorem B1468867 : Blo 346754 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B5630417 : Blo 346754 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B781289 : Blo 346754 781289 := bstep (se 2 (by rfl) ⟨292983, by rfl⟩ : syracuseStep 781289 = 585967) B585967
theorem B2976749 : Blo 346754 2976749 := bstep (se 3 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 2976749 = 1116281) B1116281
theorem B520487 : Blo 346754 520487 := bstep (se 1 (by rfl) ⟨390365, by rfl⟩ : syracuseStep 520487 = 780731) B780731
theorem B783521 : Blo 346754 783521 := bstep (se 2 (by rfl) ⟨293820, by rfl⟩ : syracuseStep 783521 = 587641) B587641
theorem B881887 : Blo 346754 881887 := bstep (se 1 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 881887 = 1322831) B1322831
theorem B521543 : Blo 346754 521543 := bstep (se 1 (by rfl) ⟨391157, by rfl⟩ : syracuseStep 521543 = 782315) B782315
theorem B4224413 : Blo 346754 4224413 := bstep (se 3 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 4224413 = 1584155) B1584155
theorem B2980061 : Blo 346754 2980061 := bstep (se 3 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 2980061 = 1117523) B1117523
theorem B522971 : Blo 346754 522971 := bstep (se 1 (by rfl) ⟨392228, by rfl⟩ : syracuseStep 522971 = 784457) B784457
theorem B1113065 : Blo 346754 1113065 := bstep (se 2 (by rfl) ⟨417399, by rfl⟩ : syracuseStep 1113065 = 834799) B834799
theorem B523367 : Blo 346754 523367 := bstep (se 1 (by rfl) ⟨392525, by rfl⟩ : syracuseStep 523367 = 785051) B785051
theorem B524027 : Blo 346754 524027 := bstep (se 1 (by rfl) ⟨393020, by rfl⟩ : syracuseStep 524027 = 786041) B786041
theorem B1408823 : Blo 346754 1408823 := bstep (se 1 (by rfl) ⟨1056617, by rfl⟩ : syracuseStep 1408823 = 2113235) B2113235
theorem B1180115 : Blo 346754 1180115 := bstep (se 1 (by rfl) ⟨885086, by rfl⟩ : syracuseStep 1180115 = 1770173) B1770173
theorem B524927 : Blo 346754 524927 := bstep (se 1 (by rfl) ⟨393695, by rfl⟩ : syracuseStep 524927 = 787391) B787391
theorem B3965759 : Blo 346754 3965759 := bstep (se 1 (by rfl) ⟨2974319, by rfl⟩ : syracuseStep 3965759 = 5948639) B5948639
theorem B28512161 : Blo 346754 28512161 := bstep (se 2 (by rfl) ⟨10692060, by rfl⟩ : syracuseStep 28512161 = 21384121) B21384121
theorem B9507557 : Blo 346754 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B8525897 : Blo 346754 8525897 := bstep (se 2 (by rfl) ⟨3197211, by rfl⟩ : syracuseStep 8525897 = 6394423) B6394423
theorem B663527 : Blo 346754 663527 := bstep (se 1 (by rfl) ⟨497645, by rfl⟩ : syracuseStep 663527 = 995291) B995291
theorem B2830355 : Blo 346754 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B16921001 : Blo 346754 16921001 := bstep (se 2 (by rfl) ⟨6345375, by rfl⟩ : syracuseStep 16921001 = 12690751) B12690751
theorem B2635091 : Blo 346754 2635091 := bstep (se 1 (by rfl) ⟨1976318, by rfl⟩ : syracuseStep 2635091 = 3952637) B3952637
theorem B1327387 : Blo 346754 1327387 := bstep (se 1 (by rfl) ⟨995540, by rfl⟩ : syracuseStep 1327387 = 1991081) B1991081
theorem B6734663 : Blo 346754 6734663 := bstep (se 1 (by rfl) ⟨5050997, by rfl⟩ : syracuseStep 6734663 = 10101995) B10101995
theorem B12797027 : Blo 346754 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B3753611 : Blo 346754 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B1984499 : Blo 346754 1984499 := bstep (se 1 (by rfl) ⟨1488374, by rfl⟩ : syracuseStep 1984499 = 2976749) B2976749
theorem B346991 : Blo 346754 346991 := bstep (se 1 (by rfl) ⟨260243, by rfl⟩ : syracuseStep 346991 = 520487) B520487
theorem B347695 : Blo 346754 347695 := bstep (se 1 (by rfl) ⟨260771, by rfl⟩ : syracuseStep 347695 = 521543) B521543
theorem B1986707 : Blo 346754 1986707 := bstep (se 1 (by rfl) ⟨1490030, by rfl⟩ : syracuseStep 1986707 = 2980061) B2980061
theorem B348647 : Blo 346754 348647 := bstep (se 1 (by rfl) ⟨261485, by rfl⟩ : syracuseStep 348647 = 522971) B522971
theorem B742043 : Blo 346754 742043 := bstep (se 1 (by rfl) ⟨556532, by rfl⟩ : syracuseStep 742043 = 1113065) B1113065
theorem B348911 : Blo 346754 348911 := bstep (se 1 (by rfl) ⟨261683, by rfl⟩ : syracuseStep 348911 = 523367) B523367
theorem B349351 : Blo 346754 349351 := bstep (se 1 (by rfl) ⟨262013, by rfl⟩ : syracuseStep 349351 = 524027) B524027
theorem B939215 : Blo 346754 939215 := bstep (se 1 (by rfl) ⟨704411, by rfl⟩ : syracuseStep 939215 = 1408823) B1408823
theorem B349647 : Blo 346754 349647 := bstep (se 1 (by rfl) ⟨262235, by rfl⟩ : syracuseStep 349647 = 524471) B524471
theorem B1496987 : Blo 346754 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B350203 : Blo 346754 350203 := bstep (se 1 (by rfl) ⟨262652, by rfl⟩ : syracuseStep 350203 = 525305) B525305
theorem B350299 : Blo 346754 350299 := bstep (se 1 (by rfl) ⟨262724, by rfl⟩ : syracuseStep 350299 = 525449) B525449
theorem B13721237 : Blo 346754 13721237 := bstep (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) B643183
theorem B1958489 : Blo 346754 1958489 := bstep (se 2 (by rfl) ⟨734433, by rfl⟩ : syracuseStep 1958489 = 1468867) B1468867
theorem B1172285 : Blo 346754 1172285 := bstep (se 3 (by rfl) ⟨219803, by rfl⟩ : syracuseStep 1172285 = 439607) B439607
theorem B11265101 : Blo 346754 11265101 := bstep (se 3 (by rfl) ⟨2112206, by rfl⟩ : syracuseStep 11265101 = 4224413) B4224413
theorem B2647727 : Blo 346754 2647727 := bstep (se 1 (by rfl) ⟨1985795, by rfl⟩ : syracuseStep 2647727 = 3971591) B3971591
theorem B780911 : Blo 346754 780911 := bstep (se 1 (by rfl) ⟨585683, by rfl⟩ : syracuseStep 780911 = 1171367) B1171367
theorem B2517887 : Blo 346754 2517887 := bstep (se 1 (by rfl) ⟨1888415, by rfl⟩ : syracuseStep 2517887 = 3776831) B3776831
theorem B1175849 : Blo 346754 1175849 := bstep (se 2 (by rfl) ⟨440943, by rfl⟩ : syracuseStep 1175849 = 881887) B881887
theorem B520859 : Blo 346754 520859 := bstep (se 1 (by rfl) ⟨390644, by rfl⟩ : syracuseStep 520859 = 781289) B781289
theorem B2651129 : Blo 346754 2651129 := bstep (se 2 (by rfl) ⟨994173, by rfl⟩ : syracuseStep 2651129 = 1988347) B1988347
theorem B9663943 : Blo 346754 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B522347 : Blo 346754 522347 := bstep (se 1 (by rfl) ⟨391760, by rfl⟩ : syracuseStep 522347 = 783521) B783521
theorem B58161863 : Blo 346754 58161863 := bstep (se 1 (by rfl) ⟨43621397, by rfl⟩ : syracuseStep 58161863 = 87242795) B87242795
theorem B10975975 : Blo 346754 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B786743 : Blo 346754 786743 := bstep (se 1 (by rfl) ⟨590057, by rfl⟩ : syracuseStep 786743 = 1180115) B1180115
theorem B1769849 : Blo 346754 1769849 := bstep (se 2 (by rfl) ⟨663693, by rfl⟩ : syracuseStep 1769849 = 1327387) B1327387
theorem B4489775 : Blo 346754 4489775 := bstep (se 1 (by rfl) ⟨3367331, by rfl⟩ : syracuseStep 4489775 = 6734663) B6734663
theorem B19008107 : Blo 346754 19008107 := bstep (se 1 (by rfl) ⟨14256080, by rfl⟩ : syracuseStep 19008107 = 28512161) B28512161
theorem B494695 : Blo 346754 494695 := bstep (se 1 (by rfl) ⟨371021, by rfl⟩ : syracuseStep 494695 = 742043) B742043
theorem B626143 : Blo 346754 626143 := bstep (se 1 (by rfl) ⟨469607, by rfl⟩ : syracuseStep 626143 = 939215) B939215
theorem B9147491 : Blo 346754 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B7510067 : Blo 346754 7510067 := bstep (se 1 (by rfl) ⟨5632550, by rfl⟩ : syracuseStep 7510067 = 11265101) B11265101
theorem B1678591 : Blo 346754 1678591 := bstep (se 1 (by rfl) ⟨1258943, by rfl⟩ : syracuseStep 1678591 = 2517887) B2517887
theorem B12885257 : Blo 346754 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B11280667 : Blo 346754 11280667 := bstep (se 1 (by rfl) ⟨8460500, by rfl⟩ : syracuseStep 11280667 = 16921001) B16921001
theorem B38774575 : Blo 346754 38774575 := bstep (se 1 (by rfl) ⟨29080931, by rfl⟩ : syracuseStep 38774575 = 58161863) B58161863
theorem B8531351 : Blo 346754 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B2502407 : Blo 346754 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B1322999 : Blo 346754 1322999 := bstep (se 1 (by rfl) ⟨992249, by rfl⟩ : syracuseStep 1322999 = 1984499) B1984499
theorem B1324471 : Blo 346754 1324471 := bstep (se 1 (by rfl) ⟨993353, by rfl⟩ : syracuseStep 1324471 = 1986707) B1986707
theorem B6338371 : Blo 346754 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B58538533 : Blo 346754 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B997991 : Blo 346754 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B5683931 : Blo 346754 5683931 := bstep (se 1 (by rfl) ⟨4262948, by rfl⟩ : syracuseStep 5683931 = 8525897) B8525897
theorem B442351 : Blo 346754 442351 := bstep (se 1 (by rfl) ⟨331763, by rfl⟩ : syracuseStep 442351 = 663527) B663527
theorem B1886903 : Blo 346754 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B347239 : Blo 346754 347239 := bstep (se 1 (by rfl) ⟨260429, by rfl⟩ : syracuseStep 347239 = 520859) B520859
theorem B1756727 : Blo 346754 1756727 := bstep (se 1 (by rfl) ⟨1317545, by rfl⟩ : syracuseStep 1756727 = 2635091) B2635091
theorem B348231 : Blo 346754 348231 := bstep (se 1 (by rfl) ⟨261173, by rfl⟩ : syracuseStep 348231 = 522347) B522347
theorem B349951 : Blo 346754 349951 := bstep (se 1 (by rfl) ⟨262463, by rfl⟩ : syracuseStep 349951 = 524927) B524927
theorem B2643839 : Blo 346754 2643839 := bstep (se 1 (by rfl) ⟨1982879, by rfl⟩ : syracuseStep 2643839 = 3965759) B3965759
theorem B1305659 : Blo 346754 1305659 := bstep (se 1 (by rfl) ⟨979244, by rfl⟩ : syracuseStep 1305659 = 1958489) B1958489
theorem B781523 : Blo 346754 781523 := bstep (se 1 (by rfl) ⟨586142, by rfl⟩ : syracuseStep 781523 = 1172285) B1172285
theorem B1765151 : Blo 346754 1765151 := bstep (se 1 (by rfl) ⟨1323863, by rfl⟩ : syracuseStep 1765151 = 2647727) B2647727
theorem B520607 : Blo 346754 520607 := bstep (se 1 (by rfl) ⟨390455, by rfl⟩ : syracuseStep 520607 = 780911) B780911
theorem B783899 : Blo 346754 783899 := bstep (se 1 (by rfl) ⟨587924, by rfl⟩ : syracuseStep 783899 = 1175849) B1175849
theorem B1767419 : Blo 346754 1767419 := bstep (se 1 (by rfl) ⟨1325564, by rfl⟩ : syracuseStep 1767419 = 2651129) B2651129
theorem B524495 : Blo 346754 524495 := bstep (se 1 (by rfl) ⟨393371, by rfl⟩ : syracuseStep 524495 = 786743) B786743
theorem B1179899 : Blo 346754 1179899 := bstep (se 1 (by rfl) ⟨884924, by rfl⟩ : syracuseStep 1179899 = 1769849) B1769849
theorem B15040889 : Blo 346754 15040889 := bstep (se 2 (by rfl) ⟨5640333, by rfl⟩ : syracuseStep 15040889 = 11280667) B11280667
theorem B6098327 : Blo 346754 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B659593 : Blo 346754 659593 := bstep (se 2 (by rfl) ⟨247347, by rfl⟩ : syracuseStep 659593 = 494695) B494695
theorem B8590171 : Blo 346754 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B2238121 : Blo 346754 2238121 := bstep (se 2 (by rfl) ⟨839295, by rfl⟩ : syracuseStep 2238121 = 1678591) B1678591
theorem B665327 : Blo 346754 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B2993183 : Blo 346754 2993183 := bstep (se 1 (by rfl) ⟨2244887, by rfl⟩ : syracuseStep 2993183 = 4489775) B4489775
theorem B1257935 : Blo 346754 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B834857 : Blo 346754 834857 := bstep (se 2 (by rfl) ⟨313071, by rfl⟩ : syracuseStep 834857 = 626143) B626143
theorem B870439 : Blo 346754 870439 := bstep (se 1 (by rfl) ⟨652829, by rfl⟩ : syracuseStep 870439 = 1305659) B1305659
theorem B5687567 : Blo 346754 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B347071 : Blo 346754 347071 := bstep (se 1 (by rfl) ⟨260303, by rfl⟩ : syracuseStep 347071 = 520607) B520607
theorem B3789287 : Blo 346754 3789287 := bstep (se 1 (by rfl) ⟨2841965, by rfl⟩ : syracuseStep 3789287 = 5683931) B5683931
theorem B12672071 : Blo 346754 12672071 := bstep (se 1 (by rfl) ⟨9504053, by rfl⟩ : syracuseStep 12672071 = 19008107) B19008107
theorem B1171151 : Blo 346754 1171151 := bstep (se 1 (by rfl) ⟨878363, by rfl⟩ : syracuseStep 1171151 = 1756727) B1756727
theorem B51699433 : Blo 346754 51699433 := bstep (se 2 (by rfl) ⟨19387287, by rfl⟩ : syracuseStep 51699433 = 38774575) B38774575
theorem B1762559 : Blo 346754 1762559 := bstep (se 1 (by rfl) ⟨1321919, by rfl⟩ : syracuseStep 1762559 = 2643839) B2643839
theorem B5006711 : Blo 346754 5006711 := bstep (se 1 (by rfl) ⟨3755033, by rfl⟩ : syracuseStep 5006711 = 7510067) B7510067
theorem B1765961 : Blo 346754 1765961 := bstep (se 2 (by rfl) ⟨662235, by rfl⟩ : syracuseStep 1765961 = 1324471) B1324471
theorem B521015 : Blo 346754 521015 := bstep (se 1 (by rfl) ⟨390761, by rfl⟩ : syracuseStep 521015 = 781523) B781523
theorem B8451161 : Blo 346754 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B1668271 : Blo 346754 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B1176767 : Blo 346754 1176767 := bstep (se 1 (by rfl) ⟨882575, by rfl⟩ : syracuseStep 1176767 = 1765151) B1765151
theorem B881999 : Blo 346754 881999 := bstep (se 1 (by rfl) ⟨661499, by rfl⟩ : syracuseStep 881999 = 1322999) B1322999
theorem B78051377 : Blo 346754 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B522599 : Blo 346754 522599 := bstep (se 1 (by rfl) ⟨391949, by rfl⟩ : syracuseStep 522599 = 783899) B783899
theorem B1178279 : Blo 346754 1178279 := bstep (se 1 (by rfl) ⟨883709, by rfl⟩ : syracuseStep 1178279 = 1767419) B1767419
theorem B589801 : Blo 346754 589801 := bstep (se 2 (by rfl) ⟨221175, by rfl⟩ : syracuseStep 589801 = 442351) B442351
theorem B786599 : Blo 346754 786599 := bstep (se 1 (by rfl) ⟨589949, by rfl⟩ : syracuseStep 786599 = 1179899) B1179899
theorem B10027259 : Blo 346754 10027259 := bstep (se 1 (by rfl) ⟨7520444, by rfl⟩ : syracuseStep 10027259 = 15040889) B15040889
theorem B2984161 : Blo 346754 2984161 := bstep (se 2 (by rfl) ⟨1119060, by rfl⟩ : syracuseStep 2984161 = 2238121) B2238121
theorem B4065551 : Blo 346754 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B2526191 : Blo 346754 2526191 := bstep (se 1 (by rfl) ⟨1894643, by rfl⟩ : syracuseStep 2526191 = 3789287) B3789287
theorem B3354493 : Blo 346754 3354493 := bstep (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) B1257935
theorem B1160585 : Blo 346754 1160585 := bstep (se 2 (by rfl) ⟨435219, by rfl⟩ : syracuseStep 1160585 = 870439) B870439
theorem B11453561 : Blo 346754 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B443551 : Blo 346754 443551 := bstep (se 1 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 443551 = 665327) B665327
theorem B347343 : Blo 346754 347343 := bstep (se 1 (by rfl) ⟨260507, by rfl⟩ : syracuseStep 347343 = 521015) B521015
theorem B348399 : Blo 346754 348399 := bstep (se 1 (by rfl) ⟨261299, by rfl⟩ : syracuseStep 348399 = 522599) B522599
theorem B68932577 : Blo 346754 68932577 := bstep (se 2 (by rfl) ⟨25849716, by rfl⟩ : syracuseStep 68932577 = 51699433) B51699433
theorem B349663 : Blo 346754 349663 := bstep (se 1 (by rfl) ⟨262247, by rfl⟩ : syracuseStep 349663 = 524495) B524495
theorem B3791711 : Blo 346754 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B8448047 : Blo 346754 8448047 := bstep (se 1 (by rfl) ⟨6336035, by rfl⟩ : syracuseStep 8448047 = 12672071) B12672071
theorem B780767 : Blo 346754 780767 := bstep (se 1 (by rfl) ⟨585575, by rfl⟩ : syracuseStep 780767 = 1171151) B1171151
theorem B879457 : Blo 346754 879457 := bstep (se 2 (by rfl) ⟨329796, by rfl⟩ : syracuseStep 879457 = 659593) B659593
theorem B1175039 : Blo 346754 1175039 := bstep (se 1 (by rfl) ⟨881279, by rfl⟩ : syracuseStep 1175039 = 1762559) B1762559
theorem B3337807 : Blo 346754 3337807 := bstep (se 1 (by rfl) ⟨2503355, by rfl⟩ : syracuseStep 3337807 = 5006711) B5006711
theorem B2224361 : Blo 346754 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B1995455 : Blo 346754 1995455 := bstep (se 1 (by rfl) ⟨1496591, by rfl⟩ : syracuseStep 1995455 = 2993183) B2993183
theorem B1177307 : Blo 346754 1177307 := bstep (se 1 (by rfl) ⟨882980, by rfl⟩ : syracuseStep 1177307 = 1765961) B1765961
theorem B5634107 : Blo 346754 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B784511 : Blo 346754 784511 := bstep (se 1 (by rfl) ⟨588383, by rfl⟩ : syracuseStep 784511 = 1176767) B1176767
theorem B587999 : Blo 346754 587999 := bstep (se 1 (by rfl) ⟨440999, by rfl⟩ : syracuseStep 587999 = 881999) B881999
theorem B52034251 : Blo 346754 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B785519 : Blo 346754 785519 := bstep (se 1 (by rfl) ⟨589139, by rfl⟩ : syracuseStep 785519 = 1178279) B1178279
theorem B556571 : Blo 346754 556571 := bstep (se 1 (by rfl) ⟨417428, by rfl⟩ : syracuseStep 556571 = 834857) B834857
theorem B786401 : Blo 346754 786401 := bstep (se 2 (by rfl) ⟨294900, by rfl⟩ : syracuseStep 786401 = 589801) B589801
theorem B524399 : Blo 346754 524399 := bstep (se 1 (by rfl) ⟨393299, by rfl⟩ : syracuseStep 524399 = 786599) B786599
theorem B6684839 : Blo 346754 6684839 := bstep (se 1 (by rfl) ⟨5013629, by rfl⟩ : syracuseStep 6684839 = 10027259) B10027259
theorem B7635707 : Blo 346754 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B591401 : Blo 346754 591401 := bstep (se 2 (by rfl) ⟨221775, by rfl⟩ : syracuseStep 591401 = 443551) B443551
theorem B2527807 : Blo 346754 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B1482907 : Blo 346754 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B69379001 : Blo 346754 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B1484189 : Blo 346754 1484189 := bstep (se 3 (by rfl) ⟨278285, by rfl⟩ : syracuseStep 1484189 = 556571) B556571
theorem B1684127 : Blo 346754 1684127 := bstep (se 1 (by rfl) ⟨1263095, by rfl⟩ : syracuseStep 1684127 = 2526191) B2526191
theorem B3978881 : Blo 346754 3978881 := bstep (se 2 (by rfl) ⟨1492080, by rfl⟩ : syracuseStep 3978881 = 2984161) B2984161
theorem B4472657 : Blo 346754 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B1330303 : Blo 346754 1330303 := bstep (se 1 (by rfl) ⟨997727, by rfl⟩ : syracuseStep 1330303 = 1995455) B1995455
theorem B773723 : Blo 346754 773723 := bstep (se 1 (by rfl) ⟨580292, by rfl⟩ : syracuseStep 773723 = 1160585) B1160585
theorem B3756071 : Blo 346754 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B2710367 : Blo 346754 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B183820205 : Blo 346754 183820205 := bstep (se 3 (by rfl) ⟨34466288, by rfl⟩ : syracuseStep 183820205 = 68932577) B68932577
theorem B1172609 : Blo 346754 1172609 := bstep (se 2 (by rfl) ⟨439728, by rfl⟩ : syracuseStep 1172609 = 879457) B879457
theorem B4450409 : Blo 346754 4450409 := bstep (se 2 (by rfl) ⟨1668903, by rfl⟩ : syracuseStep 4450409 = 3337807) B3337807
theorem B5632031 : Blo 346754 5632031 := bstep (se 1 (by rfl) ⟨4224023, by rfl⟩ : syracuseStep 5632031 = 8448047) B8448047
theorem B520511 : Blo 346754 520511 := bstep (se 1 (by rfl) ⟨390383, by rfl⟩ : syracuseStep 520511 = 780767) B780767
theorem B783359 : Blo 346754 783359 := bstep (se 1 (by rfl) ⟨587519, by rfl⟩ : syracuseStep 783359 = 1175039) B1175039
theorem B784871 : Blo 346754 784871 := bstep (se 1 (by rfl) ⟨588653, by rfl⟩ : syracuseStep 784871 = 1177307) B1177307
theorem B523007 : Blo 346754 523007 := bstep (se 1 (by rfl) ⟨392255, by rfl⟩ : syracuseStep 523007 = 784511) B784511
theorem B391999 : Blo 346754 391999 := bstep (se 1 (by rfl) ⟨293999, by rfl⟩ : syracuseStep 391999 = 587999) B587999
theorem B523679 : Blo 346754 523679 := bstep (se 1 (by rfl) ⟨392759, by rfl⟩ : syracuseStep 523679 = 785519) B785519
theorem B524267 : Blo 346754 524267 := bstep (se 1 (by rfl) ⟨393200, by rfl⟩ : syracuseStep 524267 = 786401) B786401
theorem B4456559 : Blo 346754 4456559 := bstep (se 1 (by rfl) ⟨3342419, by rfl⟩ : syracuseStep 4456559 = 6684839) B6684839
theorem B394267 : Blo 346754 394267 := bstep (se 1 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 394267 = 591401) B591401
theorem B1773737 : Blo 346754 1773737 := bstep (se 2 (by rfl) ⟨665151, by rfl⟩ : syracuseStep 1773737 = 1330303) B1330303
theorem B1806911 : Blo 346754 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B989459 : Blo 346754 989459 := bstep (se 1 (by rfl) ⟨742094, by rfl⟩ : syracuseStep 989459 = 1484189) B1484189
theorem B1122751 : Blo 346754 1122751 := bstep (se 1 (by rfl) ⟨842063, by rfl⟩ : syracuseStep 1122751 = 1684127) B1684127
theorem B1977209 : Blo 346754 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B5090471 : Blo 346754 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B2504047 : Blo 346754 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B46252667 : Blo 346754 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B2966939 : Blo 346754 2966939 := bstep (se 1 (by rfl) ⟨2225204, by rfl⟩ : syracuseStep 2966939 = 4450409) B4450409
theorem B3754687 : Blo 346754 3754687 := bstep (se 1 (by rfl) ⟨2816015, by rfl⟩ : syracuseStep 3754687 = 5632031) B5632031
theorem B347007 : Blo 346754 347007 := bstep (se 1 (by rfl) ⟨260255, by rfl⟩ : syracuseStep 347007 = 520511) B520511
theorem B348671 : Blo 346754 348671 := bstep (se 1 (by rfl) ⟨261503, by rfl⟩ : syracuseStep 348671 = 523007) B523007
theorem B349119 : Blo 346754 349119 := bstep (se 1 (by rfl) ⟨261839, by rfl⟩ : syracuseStep 349119 = 523679) B523679
theorem B349511 : Blo 346754 349511 := bstep (se 1 (by rfl) ⟨262133, by rfl⟩ : syracuseStep 349511 = 524267) B524267
theorem B349599 : Blo 346754 349599 := bstep (se 1 (by rfl) ⟨262199, by rfl⟩ : syracuseStep 349599 = 524399) B524399
theorem B122546803 : Blo 346754 122546803 := bstep (se 1 (by rfl) ⟨91910102, by rfl⟩ : syracuseStep 122546803 = 183820205) B183820205
theorem B3370409 : Blo 346754 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B781739 : Blo 346754 781739 := bstep (se 1 (by rfl) ⟨586304, by rfl⟩ : syracuseStep 781739 = 1172609) B1172609
theorem B522239 : Blo 346754 522239 := bstep (se 1 (by rfl) ⟨391679, by rfl⟩ : syracuseStep 522239 = 783359) B783359
theorem B522665 : Blo 346754 522665 := bstep (se 2 (by rfl) ⟨195999, by rfl⟩ : syracuseStep 522665 = 391999) B391999
theorem B2652587 : Blo 346754 2652587 := bstep (se 1 (by rfl) ⟨1989440, by rfl⟩ : syracuseStep 2652587 = 3978881) B3978881
theorem B2063261 : Blo 346754 2063261 := bstep (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) B773723
theorem B523247 : Blo 346754 523247 := bstep (se 1 (by rfl) ⟨392435, by rfl⟩ : syracuseStep 523247 = 784871) B784871
theorem B2981771 : Blo 346754 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B525689 : Blo 346754 525689 := bstep (se 2 (by rfl) ⟨197133, by rfl⟩ : syracuseStep 525689 = 394267) B394267
theorem B123340445 : Blo 346754 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B1182491 : Blo 346754 1182491 := bstep (se 1 (by rfl) ⟨886868, by rfl⟩ : syracuseStep 1182491 = 1773737) B1773737
theorem B659639 : Blo 346754 659639 := bstep (se 1 (by rfl) ⟨494729, by rfl⟩ : syracuseStep 659639 = 989459) B989459
theorem B1318139 : Blo 346754 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B1977959 : Blo 346754 1977959 := bstep (se 1 (by rfl) ⟨1483469, by rfl⟩ : syracuseStep 1977959 = 2966939) B2966939
theorem B163395737 : Blo 346754 163395737 := bstep (se 2 (by rfl) ⟨61273401, by rfl⟩ : syracuseStep 163395737 = 122546803) B122546803
theorem B3393647 : Blo 346754 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B2246939 : Blo 346754 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B348159 : Blo 346754 348159 := bstep (se 1 (by rfl) ⟨261119, by rfl⟩ : syracuseStep 348159 = 522239) B522239
theorem B348443 : Blo 346754 348443 := bstep (se 1 (by rfl) ⟨261332, by rfl⟩ : syracuseStep 348443 = 522665) B522665
theorem B348831 : Blo 346754 348831 := bstep (se 1 (by rfl) ⟨261623, by rfl⟩ : syracuseStep 348831 = 523247) B523247
theorem B1987847 : Blo 346754 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B2971039 : Blo 346754 2971039 := bstep (se 1 (by rfl) ⟨2228279, by rfl⟩ : syracuseStep 2971039 = 4456559) B4456559
theorem B5988005 : Blo 346754 5988005 := bstep (se 4 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 5988005 = 1122751) B1122751
theorem B1204607 : Blo 346754 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B5006249 : Blo 346754 5006249 := bstep (se 2 (by rfl) ⟨1877343, by rfl⟩ : syracuseStep 5006249 = 3754687) B3754687
theorem B3338729 : Blo 346754 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B521159 : Blo 346754 521159 := bstep (se 1 (by rfl) ⟨390869, by rfl⟩ : syracuseStep 521159 = 781739) B781739
theorem B1768391 : Blo 346754 1768391 := bstep (se 1 (by rfl) ⟨1326293, by rfl⟩ : syracuseStep 1768391 = 2652587) B2652587
theorem B1375507 : Blo 346754 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B2262431 : Blo 346754 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B788327 : Blo 346754 788327 := bstep (se 1 (by rfl) ⟨591245, by rfl⟩ : syracuseStep 788327 = 1182491) B1182491
theorem B1318639 : Blo 346754 1318639 := bstep (se 1 (by rfl) ⟨988979, by rfl⟩ : syracuseStep 1318639 = 1977959) B1977959
theorem B108930491 : Blo 346754 108930491 := bstep (se 1 (by rfl) ⟨81697868, by rfl⟩ : syracuseStep 108930491 = 163395737) B163395737
theorem B82226963 : Blo 346754 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B439759 : Blo 346754 439759 := bstep (se 1 (by rfl) ⟨329819, by rfl⟩ : syracuseStep 439759 = 659639) B659639
theorem B1325231 : Blo 346754 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B803071 : Blo 346754 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B347439 : Blo 346754 347439 := bstep (se 1 (by rfl) ⟨260579, by rfl⟩ : syracuseStep 347439 = 521159) B521159
theorem B350459 : Blo 346754 350459 := bstep (se 1 (by rfl) ⟨262844, by rfl⟩ : syracuseStep 350459 = 525689) B525689
theorem B1497959 : Blo 346754 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B878759 : Blo 346754 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B3992003 : Blo 346754 3992003 := bstep (se 1 (by rfl) ⟨2994002, by rfl⟩ : syracuseStep 3992003 = 5988005) B5988005
theorem B3337499 : Blo 346754 3337499 := bstep (se 1 (by rfl) ⟨2503124, by rfl⟩ : syracuseStep 3337499 = 5006249) B5006249
theorem B7336037 : Blo 346754 7336037 := bstep (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) B1375507
theorem B3961385 : Blo 346754 3961385 := bstep (se 2 (by rfl) ⟨1485519, by rfl⟩ : syracuseStep 3961385 = 2971039) B2971039
theorem B2225819 : Blo 346754 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B1178927 : Blo 346754 1178927 := bstep (se 1 (by rfl) ⟨884195, by rfl⟩ : syracuseStep 1178927 = 1768391) B1768391
theorem B525551 : Blo 346754 525551 := bstep (se 1 (by rfl) ⟨394163, by rfl⟩ : syracuseStep 525551 = 788327) B788327
theorem B6033149 : Blo 346754 6033149 := bstep (se 3 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 6033149 = 2262431) B2262431
theorem B5935517 : Blo 346754 5935517 := bstep (se 3 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 5935517 = 2225819) B2225819
theorem B72620327 : Blo 346754 72620327 := bstep (se 1 (by rfl) ⟨54465245, by rfl⟩ : syracuseStep 72620327 = 108930491) B108930491
theorem B2661335 : Blo 346754 2661335 := bstep (se 1 (by rfl) ⟨1996001, by rfl⟩ : syracuseStep 2661335 = 3992003) B3992003
theorem B4890691 : Blo 346754 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B998639 : Blo 346754 998639 := bstep (se 1 (by rfl) ⟨748979, by rfl⟩ : syracuseStep 998639 = 1497959) B1497959
theorem B2640923 : Blo 346754 2640923 := bstep (se 1 (by rfl) ⟨1980692, by rfl⟩ : syracuseStep 2640923 = 3961385) B3961385
theorem B1758185 : Blo 346754 1758185 := bstep (se 2 (by rfl) ⟨659319, by rfl⟩ : syracuseStep 1758185 = 1318639) B1318639
theorem B1070761 : Blo 346754 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B585839 : Blo 346754 585839 := bstep (se 1 (by rfl) ⟨439379, by rfl⟩ : syracuseStep 585839 = 878759) B878759
theorem B586345 : Blo 346754 586345 := bstep (se 2 (by rfl) ⟨219879, by rfl⟩ : syracuseStep 586345 = 439759) B439759
theorem B2224999 : Blo 346754 2224999 := bstep (se 1 (by rfl) ⟨1668749, by rfl⟩ : syracuseStep 2224999 = 3337499) B3337499
theorem B54817975 : Blo 346754 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B883487 : Blo 346754 883487 := bstep (se 1 (by rfl) ⟨662615, by rfl⟩ : syracuseStep 883487 = 1325231) B1325231
theorem B785951 : Blo 346754 785951 := bstep (se 1 (by rfl) ⟨589463, by rfl⟩ : syracuseStep 785951 = 1178927) B1178927
theorem B26083685 : Blo 346754 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B1774223 : Blo 346754 1774223 := bstep (se 1 (by rfl) ⟨1330667, by rfl⟩ : syracuseStep 1774223 = 2661335) B2661335
theorem B665759 : Blo 346754 665759 := bstep (se 1 (by rfl) ⟨499319, by rfl⟩ : syracuseStep 665759 = 998639) B998639
theorem B48413551 : Blo 346754 48413551 := bstep (se 1 (by rfl) ⟨36310163, by rfl⟩ : syracuseStep 48413551 = 72620327) B72620327
theorem B2966665 : Blo 346754 2966665 := bstep (se 2 (by rfl) ⟨1112499, by rfl⟩ : syracuseStep 2966665 = 2224999) B2224999
theorem B73090633 : Blo 346754 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B1427681 : Blo 346754 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B350367 : Blo 346754 350367 := bstep (se 1 (by rfl) ⟨262775, by rfl⟩ : syracuseStep 350367 = 525551) B525551
theorem B1760615 : Blo 346754 1760615 := bstep (se 1 (by rfl) ⟨1320461, by rfl⟩ : syracuseStep 1760615 = 2640923) B2640923
theorem B4022099 : Blo 346754 4022099 := bstep (se 1 (by rfl) ⟨3016574, by rfl⟩ : syracuseStep 4022099 = 6033149) B6033149
theorem B3957011 : Blo 346754 3957011 := bstep (se 1 (by rfl) ⟨2967758, by rfl⟩ : syracuseStep 3957011 = 5935517) B5935517
theorem B1172123 : Blo 346754 1172123 := bstep (se 1 (by rfl) ⟨879092, by rfl⟩ : syracuseStep 1172123 = 1758185) B1758185
theorem B781793 : Blo 346754 781793 := bstep (se 2 (by rfl) ⟨293172, by rfl⟩ : syracuseStep 781793 = 586345) B586345
theorem B390559 : Blo 346754 390559 := bstep (se 1 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 390559 = 585839) B585839
theorem B588991 : Blo 346754 588991 := bstep (se 1 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 588991 = 883487) B883487
theorem B523967 : Blo 346754 523967 := bstep (se 1 (by rfl) ⟨392975, by rfl⟩ : syracuseStep 523967 = 785951) B785951
theorem B951787 : Blo 346754 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B97454177 : Blo 346754 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B1182815 : Blo 346754 1182815 := bstep (se 1 (by rfl) ⟨887111, by rfl⟩ : syracuseStep 1182815 = 1774223) B1774223
theorem B1775357 : Blo 346754 1775357 := bstep (se 3 (by rfl) ⟨332879, by rfl⟩ : syracuseStep 1775357 = 665759) B665759
theorem B2638007 : Blo 346754 2638007 := bstep (se 1 (by rfl) ⟨1978505, by rfl⟩ : syracuseStep 2638007 = 3957011) B3957011
theorem B349311 : Blo 346754 349311 := bstep (se 1 (by rfl) ⟨261983, by rfl⟩ : syracuseStep 349311 = 523967) B523967
theorem B69556493 : Blo 346754 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B3955553 : Blo 346754 3955553 := bstep (se 2 (by rfl) ⟨1483332, by rfl⟩ : syracuseStep 3955553 = 2966665) B2966665
theorem B1173743 : Blo 346754 1173743 := bstep (se 1 (by rfl) ⟨880307, by rfl⟩ : syracuseStep 1173743 = 1760615) B1760615
theorem B2681399 : Blo 346754 2681399 := bstep (se 1 (by rfl) ⟨2011049, by rfl⟩ : syracuseStep 2681399 = 4022099) B4022099
theorem B781415 : Blo 346754 781415 := bstep (se 1 (by rfl) ⟨586061, by rfl⟩ : syracuseStep 781415 = 1172123) B1172123
theorem B520745 : Blo 346754 520745 := bstep (se 2 (by rfl) ⟨195279, by rfl⟩ : syracuseStep 520745 = 390559) B390559
theorem B521195 : Blo 346754 521195 := bstep (se 1 (by rfl) ⟨390896, by rfl⟩ : syracuseStep 521195 = 781793) B781793
theorem B64551401 : Blo 346754 64551401 := bstep (se 2 (by rfl) ⟨24206775, by rfl⟩ : syracuseStep 64551401 = 48413551) B48413551
theorem B785321 : Blo 346754 785321 := bstep (se 2 (by rfl) ⟨294495, by rfl⟩ : syracuseStep 785321 = 588991) B588991
theorem B788543 : Blo 346754 788543 := bstep (se 1 (by rfl) ⟨591407, by rfl⟩ : syracuseStep 788543 = 1182815) B1182815
theorem B1183571 : Blo 346754 1183571 := bstep (se 1 (by rfl) ⟨887678, by rfl⟩ : syracuseStep 1183571 = 1775357) B1775357
theorem B43034267 : Blo 346754 43034267 := bstep (se 1 (by rfl) ⟨32275700, by rfl⟩ : syracuseStep 43034267 = 64551401) B64551401
theorem B2637035 : Blo 346754 2637035 := bstep (se 1 (by rfl) ⟨1977776, by rfl⟩ : syracuseStep 2637035 = 3955553) B3955553
theorem B185483981 : Blo 346754 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B1787599 : Blo 346754 1787599 := bstep (se 1 (by rfl) ⟨1340699, by rfl⟩ : syracuseStep 1787599 = 2681399) B2681399
theorem B347163 : Blo 346754 347163 := bstep (se 1 (by rfl) ⟨260372, by rfl⟩ : syracuseStep 347163 = 520745) B520745
theorem B347463 : Blo 346754 347463 := bstep (se 1 (by rfl) ⟨260597, by rfl⟩ : syracuseStep 347463 = 521195) B521195
theorem B1758671 : Blo 346754 1758671 := bstep (se 1 (by rfl) ⟨1319003, by rfl⟩ : syracuseStep 1758671 = 2638007) B2638007
theorem B64969451 : Blo 346754 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B1269049 : Blo 346754 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B782495 : Blo 346754 782495 := bstep (se 1 (by rfl) ⟨586871, by rfl⟩ : syracuseStep 782495 = 1173743) B1173743
theorem B520943 : Blo 346754 520943 := bstep (se 1 (by rfl) ⟨390707, by rfl⟩ : syracuseStep 520943 = 781415) B781415
theorem B523547 : Blo 346754 523547 := bstep (se 1 (by rfl) ⟨392660, by rfl⟩ : syracuseStep 523547 = 785321) B785321
theorem B525695 : Blo 346754 525695 := bstep (se 1 (by rfl) ⟨394271, by rfl⟩ : syracuseStep 525695 = 788543) B788543
theorem B789047 : Blo 346754 789047 := bstep (se 1 (by rfl) ⟨591785, by rfl⟩ : syracuseStep 789047 = 1183571) B1183571
theorem B28689511 : Blo 346754 28689511 := bstep (se 1 (by rfl) ⟨21517133, by rfl⟩ : syracuseStep 28689511 = 43034267) B43034267
theorem B347295 : Blo 346754 347295 := bstep (se 1 (by rfl) ⟨260471, by rfl⟩ : syracuseStep 347295 = 520943) B520943
theorem B1692065 : Blo 346754 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B1758023 : Blo 346754 1758023 := bstep (se 1 (by rfl) ⟨1318517, by rfl⟩ : syracuseStep 1758023 = 2637035) B2637035
theorem B349031 : Blo 346754 349031 := bstep (se 1 (by rfl) ⟨261773, by rfl⟩ : syracuseStep 349031 = 523547) B523547
theorem B123655987 : Blo 346754 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B2383465 : Blo 346754 2383465 := bstep (se 2 (by rfl) ⟨893799, by rfl⟩ : syracuseStep 2383465 = 1787599) B1787599
theorem B1172447 : Blo 346754 1172447 := bstep (se 1 (by rfl) ⟨879335, by rfl⟩ : syracuseStep 1172447 = 1758671) B1758671
theorem B43312967 : Blo 346754 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B521663 : Blo 346754 521663 := bstep (se 1 (by rfl) ⟨391247, by rfl⟩ : syracuseStep 521663 = 782495) B782495
theorem B526031 : Blo 346754 526031 := bstep (se 1 (by rfl) ⟨394523, by rfl⟩ : syracuseStep 526031 = 789047) B789047
theorem B28875311 : Blo 346754 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B38252681 : Blo 346754 38252681 := bstep (se 2 (by rfl) ⟨14344755, by rfl⟩ : syracuseStep 38252681 = 28689511) B28689511
theorem B1128043 : Blo 346754 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B164874649 : Blo 346754 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B347775 : Blo 346754 347775 := bstep (se 1 (by rfl) ⟨260831, by rfl⟩ : syracuseStep 347775 = 521663) B521663
theorem B350463 : Blo 346754 350463 := bstep (se 1 (by rfl) ⟨262847, by rfl⟩ : syracuseStep 350463 = 525695) B525695
theorem B1172015 : Blo 346754 1172015 := bstep (se 1 (by rfl) ⟨879011, by rfl⟩ : syracuseStep 1172015 = 1758023) B1758023
theorem B781631 : Blo 346754 781631 := bstep (se 1 (by rfl) ⟨586223, by rfl⟩ : syracuseStep 781631 = 1172447) B1172447
theorem B3177953 : Blo 346754 3177953 := bstep (se 2 (by rfl) ⟨1191732, by rfl⟩ : syracuseStep 3177953 = 2383465) B2383465
theorem B25501787 : Blo 346754 25501787 := bstep (se 1 (by rfl) ⟨19126340, by rfl⟩ : syracuseStep 25501787 = 38252681) B38252681
theorem B19250207 : Blo 346754 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B2118635 : Blo 346754 2118635 := bstep (se 1 (by rfl) ⟨1588976, by rfl⟩ : syracuseStep 2118635 = 3177953) B3177953
theorem B350687 : Blo 346754 350687 := bstep (se 1 (by rfl) ⟨263015, by rfl⟩ : syracuseStep 350687 = 526031) B526031
theorem B219832865 : Blo 346754 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B781343 : Blo 346754 781343 := bstep (se 1 (by rfl) ⟨586007, by rfl⟩ : syracuseStep 781343 = 1172015) B1172015
theorem B1504057 : Blo 346754 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B521087 : Blo 346754 521087 := bstep (se 1 (by rfl) ⟨390815, by rfl⟩ : syracuseStep 521087 = 781631) B781631
theorem B1412423 : Blo 346754 1412423 := bstep (se 1 (by rfl) ⟨1059317, by rfl⟩ : syracuseStep 1412423 = 2118635) B2118635
theorem B2005409 : Blo 346754 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B146555243 : Blo 346754 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B347391 : Blo 346754 347391 := bstep (se 1 (by rfl) ⟨260543, by rfl⟩ : syracuseStep 347391 = 521087) B521087
theorem B12833471 : Blo 346754 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B17001191 : Blo 346754 17001191 := bstep (se 1 (by rfl) ⟨12750893, by rfl⟩ : syracuseStep 17001191 = 25501787) B25501787
theorem B520895 : Blo 346754 520895 := bstep (se 1 (by rfl) ⟨390671, by rfl⟩ : syracuseStep 520895 = 781343) B781343
theorem B8555647 : Blo 346754 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B5347757 : Blo 346754 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B347263 : Blo 346754 347263 := bstep (se 1 (by rfl) ⟨260447, by rfl⟩ : syracuseStep 347263 = 520895) B520895
theorem B97703495 : Blo 346754 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B941615 : Blo 346754 941615 := bstep (se 1 (by rfl) ⟨706211, by rfl⟩ : syracuseStep 941615 = 1412423) B1412423
theorem B11334127 : Blo 346754 11334127 := bstep (se 1 (by rfl) ⟨8500595, by rfl⟩ : syracuseStep 11334127 = 17001191) B17001191
theorem B11407529 : Blo 346754 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B627743 : Blo 346754 627743 := bstep (se 1 (by rfl) ⟨470807, by rfl⟩ : syracuseStep 627743 = 941615) B941615
theorem B15112169 : Blo 346754 15112169 := bstep (se 2 (by rfl) ⟨5667063, by rfl⟩ : syracuseStep 15112169 = 11334127) B11334127
theorem B65135663 : Blo 346754 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B3565171 : Blo 346754 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B4753561 : Blo 346754 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B7605019 : Blo 346754 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B43423775 : Blo 346754 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B10074779 : Blo 346754 10074779 := bstep (se 1 (by rfl) ⟨7556084, by rfl⟩ : syracuseStep 10074779 = 15112169) B15112169
theorem B418495 : Blo 346754 418495 := bstep (se 1 (by rfl) ⟨313871, by rfl⟩ : syracuseStep 418495 = 627743) B627743
theorem B557993 : Blo 346754 557993 := bstep (se 2 (by rfl) ⟨209247, by rfl⟩ : syracuseStep 557993 = 418495) B418495
theorem B6338081 : Blo 346754 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B28949183 : Blo 346754 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B40560101 : Blo 346754 40560101 := bstep (se 4 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 40560101 = 7605019) B7605019
theorem B6716519 : Blo 346754 6716519 := bstep (se 1 (by rfl) ⟨5037389, by rfl⟩ : syracuseStep 6716519 = 10074779) B10074779
theorem B27040067 : Blo 346754 27040067 := bstep (se 1 (by rfl) ⟨20280050, by rfl⟩ : syracuseStep 27040067 = 40560101) B40560101
theorem B371995 : Blo 346754 371995 := bstep (se 1 (by rfl) ⟨278996, by rfl⟩ : syracuseStep 371995 = 557993) B557993
theorem B4477679 : Blo 346754 4477679 := bstep (se 1 (by rfl) ⟨3358259, by rfl⟩ : syracuseStep 4477679 = 6716519) B6716519
theorem B4225387 : Blo 346754 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B19299455 : Blo 346754 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B2985119 : Blo 346754 2985119 := bstep (se 1 (by rfl) ⟨2238839, by rfl⟩ : syracuseStep 2985119 = 4477679) B4477679
theorem B18026711 : Blo 346754 18026711 := bstep (se 1 (by rfl) ⟨13520033, by rfl⟩ : syracuseStep 18026711 = 27040067) B27040067
theorem B1983973 : Blo 346754 1983973 := bstep (se 4 (by rfl) ⟨185997, by rfl⟩ : syracuseStep 1983973 = 371995) B371995
theorem B12866303 : Blo 346754 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B5633849 : Blo 346754 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B3755899 : Blo 346754 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B2645297 : Blo 346754 2645297 := bstep (se 2 (by rfl) ⟨991986, by rfl⟩ : syracuseStep 2645297 = 1983973) B1983973
theorem B1990079 : Blo 346754 1990079 := bstep (se 1 (by rfl) ⟨1492559, by rfl⟩ : syracuseStep 1990079 = 2985119) B2985119
theorem B12017807 : Blo 346754 12017807 := bstep (se 1 (by rfl) ⟨9013355, by rfl⟩ : syracuseStep 12017807 = 18026711) B18026711
theorem B8577535 : Blo 346754 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B11436713 : Blo 346754 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B1326719 : Blo 346754 1326719 := bstep (se 1 (by rfl) ⟨995039, by rfl⟩ : syracuseStep 1326719 = 1990079) B1990079
theorem B8011871 : Blo 346754 8011871 := bstep (se 1 (by rfl) ⟨6008903, by rfl⟩ : syracuseStep 8011871 = 12017807) B12017807
theorem B1763531 : Blo 346754 1763531 := bstep (se 1 (by rfl) ⟨1322648, by rfl⟩ : syracuseStep 1763531 = 2645297) B2645297
theorem B5007865 : Blo 346754 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B5341247 : Blo 346754 5341247 := bstep (se 1 (by rfl) ⟨4005935, by rfl⟩ : syracuseStep 5341247 = 8011871) B8011871
theorem B7624475 : Blo 346754 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B6677153 : Blo 346754 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B1175687 : Blo 346754 1175687 := bstep (se 1 (by rfl) ⟨881765, by rfl⟩ : syracuseStep 1175687 = 1763531) B1763531
theorem B884479 : Blo 346754 884479 := bstep (se 1 (by rfl) ⟨663359, by rfl⟩ : syracuseStep 884479 = 1326719) B1326719
theorem B5082983 : Blo 346754 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B3560831 : Blo 346754 3560831 := bstep (se 1 (by rfl) ⟨2670623, by rfl⟩ : syracuseStep 3560831 = 5341247) B5341247
theorem B4451435 : Blo 346754 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B783791 : Blo 346754 783791 := bstep (se 1 (by rfl) ⟨587843, by rfl⟩ : syracuseStep 783791 = 1175687) B1175687
theorem B1179305 : Blo 346754 1179305 := bstep (se 2 (by rfl) ⟨442239, by rfl⟩ : syracuseStep 1179305 = 884479) B884479
theorem B3388655 : Blo 346754 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B2373887 : Blo 346754 2373887 := bstep (se 1 (by rfl) ⟨1780415, by rfl⟩ : syracuseStep 2373887 = 3560831) B3560831
theorem B2967623 : Blo 346754 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B522527 : Blo 346754 522527 := bstep (se 1 (by rfl) ⟨391895, by rfl⟩ : syracuseStep 522527 = 783791) B783791
theorem B786203 : Blo 346754 786203 := bstep (se 1 (by rfl) ⟨589652, by rfl⟩ : syracuseStep 786203 = 1179305) B1179305
theorem B1582591 : Blo 346754 1582591 := bstep (se 1 (by rfl) ⟨1186943, by rfl⟩ : syracuseStep 1582591 = 2373887) B2373887
theorem B1978415 : Blo 346754 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B348351 : Blo 346754 348351 := bstep (se 1 (by rfl) ⟨261263, by rfl⟩ : syracuseStep 348351 = 522527) B522527
theorem B2259103 : Blo 346754 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B524135 : Blo 346754 524135 := bstep (se 1 (by rfl) ⟨393101, by rfl⟩ : syracuseStep 524135 = 786203) B786203
theorem B1318943 : Blo 346754 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B2110121 : Blo 346754 2110121 := bstep (se 2 (by rfl) ⟨791295, by rfl⟩ : syracuseStep 2110121 = 1582591) B1582591
theorem B349423 : Blo 346754 349423 := bstep (se 1 (by rfl) ⟨262067, by rfl⟩ : syracuseStep 349423 = 524135) B524135
theorem B3012137 : Blo 346754 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B2008091 : Blo 346754 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B879295 : Blo 346754 879295 := bstep (se 1 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 879295 = 1318943) B1318943
theorem B1406747 : Blo 346754 1406747 := bstep (se 1 (by rfl) ⟨1055060, by rfl⟩ : syracuseStep 1406747 = 2110121) B2110121
theorem B937831 : Blo 346754 937831 := bstep (se 1 (by rfl) ⟨703373, by rfl⟩ : syracuseStep 937831 = 1406747) B1406747
theorem B1172393 : Blo 346754 1172393 := bstep (se 2 (by rfl) ⟨439647, by rfl⟩ : syracuseStep 1172393 = 879295) B879295
theorem B1338727 : Blo 346754 1338727 := bstep (se 1 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 1338727 = 2008091) B2008091
theorem B1250441 : Blo 346754 1250441 := bstep (se 2 (by rfl) ⟨468915, by rfl⟩ : syracuseStep 1250441 = 937831) B937831
theorem B1784969 : Blo 346754 1784969 := bstep (se 2 (by rfl) ⟨669363, by rfl⟩ : syracuseStep 1784969 = 1338727) B1338727
theorem B781595 : Blo 346754 781595 := bstep (se 1 (by rfl) ⟨586196, by rfl⟩ : syracuseStep 781595 = 1172393) B1172393
theorem B1189979 : Blo 346754 1189979 := bstep (se 1 (by rfl) ⟨892484, by rfl⟩ : syracuseStep 1189979 = 1784969) B1784969
theorem B833627 : Blo 346754 833627 := bstep (se 1 (by rfl) ⟨625220, by rfl⟩ : syracuseStep 833627 = 1250441) B1250441
theorem B521063 : Blo 346754 521063 := bstep (se 1 (by rfl) ⟨390797, by rfl⟩ : syracuseStep 521063 = 781595) B781595
theorem B793319 : Blo 346754 793319 := bstep (se 1 (by rfl) ⟨594989, by rfl⟩ : syracuseStep 793319 = 1189979) B1189979
theorem B347375 : Blo 346754 347375 := bstep (se 1 (by rfl) ⟨260531, by rfl⟩ : syracuseStep 347375 = 521063) B521063
theorem B555751 : Blo 346754 555751 := bstep (se 1 (by rfl) ⟨416813, by rfl⟩ : syracuseStep 555751 = 833627) B833627
theorem B2115517 : Blo 346754 2115517 := bstep (se 3 (by rfl) ⟨396659, by rfl⟩ : syracuseStep 2115517 = 793319) B793319
theorem B741001 : Blo 346754 741001 := bstep (se 2 (by rfl) ⟨277875, by rfl⟩ : syracuseStep 741001 = 555751) B555751
theorem B2820689 : Blo 346754 2820689 := bstep (se 2 (by rfl) ⟨1057758, by rfl⟩ : syracuseStep 2820689 = 2115517) B2115517
theorem B988001 : Blo 346754 988001 := bstep (se 2 (by rfl) ⟨370500, by rfl⟩ : syracuseStep 988001 = 741001) B741001
theorem B658667 : Blo 346754 658667 := bstep (se 1 (by rfl) ⟨494000, by rfl⟩ : syracuseStep 658667 = 988001) B988001
theorem B1880459 : Blo 346754 1880459 := bstep (se 1 (by rfl) ⟨1410344, by rfl⟩ : syracuseStep 1880459 = 2820689) B2820689
theorem B1253639 : Blo 346754 1253639 := bstep (se 1 (by rfl) ⟨940229, by rfl⟩ : syracuseStep 1253639 = 1880459) B1880459
theorem B439111 : Blo 346754 439111 := bstep (se 1 (by rfl) ⟨329333, by rfl⟩ : syracuseStep 439111 = 658667) B658667
theorem B835759 : Blo 346754 835759 := bstep (se 1 (by rfl) ⟨626819, by rfl⟩ : syracuseStep 835759 = 1253639) B1253639
theorem B585481 : Blo 346754 585481 := bstep (se 2 (by rfl) ⟨219555, by rfl⟩ : syracuseStep 585481 = 439111) B439111
theorem B1114345 : Blo 346754 1114345 := bstep (se 2 (by rfl) ⟨417879, by rfl⟩ : syracuseStep 1114345 = 835759) B835759
theorem B780641 : Blo 346754 780641 := bstep (se 2 (by rfl) ⟨292740, by rfl⟩ : syracuseStep 780641 = 585481) B585481
theorem B1485793 : Blo 346754 1485793 := bstep (se 2 (by rfl) ⟨557172, by rfl⟩ : syracuseStep 1485793 = 1114345) B1114345
theorem B520427 : Blo 346754 520427 := bstep (se 1 (by rfl) ⟨390320, by rfl⟩ : syracuseStep 520427 = 780641) B780641
theorem B1981057 : Blo 346754 1981057 := bstep (se 2 (by rfl) ⟨742896, by rfl⟩ : syracuseStep 1981057 = 1485793) B1485793
theorem B346951 : Blo 346754 346951 := bstep (se 1 (by rfl) ⟨260213, by rfl⟩ : syracuseStep 346951 = 520427) B520427
theorem B2641409 : Blo 346754 2641409 := bstep (se 2 (by rfl) ⟨990528, by rfl⟩ : syracuseStep 2641409 = 1981057) B1981057
theorem B1760939 : Blo 346754 1760939 := bstep (se 1 (by rfl) ⟨1320704, by rfl⟩ : syracuseStep 1760939 = 2641409) B2641409
theorem B1173959 : Blo 346754 1173959 := bstep (se 1 (by rfl) ⟨880469, by rfl⟩ : syracuseStep 1173959 = 1760939) B1760939
theorem B782639 : Blo 346754 782639 := bstep (se 1 (by rfl) ⟨586979, by rfl⟩ : syracuseStep 782639 = 1173959) B1173959
theorem B521759 : Blo 346754 521759 := bstep (se 1 (by rfl) ⟨391319, by rfl⟩ : syracuseStep 521759 = 782639) B782639
theorem B347839 : Blo 346754 347839 := bstep (se 1 (by rfl) ⟨260879, by rfl⟩ : syracuseStep 347839 = 521759) B521759

theorem C0 (j : ℕ) (h1 : 86688 ≤ j) (h2 : j ≤ 87387) : Blo 346754 (4 * j + 3) := by
  interval_cases j
  · exact B346755
  · exact B346759
  · exact B346763
  · exact B346767
  · exact B346771
  · exact B346775
  · exact B346779
  · exact B346783
  · exact B346787
  · exact B346791
  · exact B346795
  · exact B346799
  · exact B346803
  · exact B346807
  · exact B346811
  · exact B346815
  · exact B346819
  · exact B346823
  · exact B346827
  · exact B346831
  · exact B346835
  · exact B346839
  · exact B346843
  · exact B346847
  · exact B346851
  · exact B346855
  · exact B346859
  · exact B346863
  · exact B346867
  · exact B346871
  · exact B346875
  · exact B346879
  · exact B346883
  · exact B346887
  · exact B346891
  · exact B346895
  · exact B346899
  · exact B346903
  · exact B346907
  · exact B346911
  · exact B346915
  · exact B346919
  · exact B346923
  · exact B346927
  · exact B346931
  · exact B346935
  · exact B346939
  · exact B346943
  · exact B346947
  · exact B346951
  · exact B346955
  · exact B346959
  · exact B346963
  · exact B346967
  · exact B346971
  · exact B346975
  · exact B346979
  · exact B346983
  · exact B346987
  · exact B346991
  · exact B346995
  · exact B346999
  · exact B347003
  · exact B347007
  · exact B347011
  · exact B347015
  · exact B347019
  · exact B347023
  · exact B347027
  · exact B347031
  · exact B347035
  · exact B347039
  · exact B347043
  · exact B347047
  · exact B347051
  · exact B347055
  · exact B347059
  · exact B347063
  · exact B347067
  · exact B347071
  · exact B347075
  · exact B347079
  · exact B347083
  · exact B347087
  · exact B347091
  · exact B347095
  · exact B347099
  · exact B347103
  · exact B347107
  · exact B347111
  · exact B347115
  · exact B347119
  · exact B347123
  · exact B347127
  · exact B347131
  · exact B347135
  · exact B347139
  · exact B347143
  · exact B347147
  · exact B347151
  · exact B347155
  · exact B347159
  · exact B347163
  · exact B347167
  · exact B347171
  · exact B347175
  · exact B347179
  · exact B347183
  · exact B347187
  · exact B347191
  · exact B347195
  · exact B347199
  · exact B347203
  · exact B347207
  · exact B347211
  · exact B347215
  · exact B347219
  · exact B347223
  · exact B347227
  · exact B347231
  · exact B347235
  · exact B347239
  · exact B347243
  · exact B347247
  · exact B347251
  · exact B347255
  · exact B347259
  · exact B347263
  · exact B347267
  · exact B347271
  · exact B347275
  · exact B347279
  · exact B347283
  · exact B347287
  · exact B347291
  · exact B347295
  · exact B347299
  · exact B347303
  · exact B347307
  · exact B347311
  · exact B347315
  · exact B347319
  · exact B347323
  · exact B347327
  · exact B347331
  · exact B347335
  · exact B347339
  · exact B347343
  · exact B347347
  · exact B347351
  · exact B347355
  · exact B347359
  · exact B347363
  · exact B347367
  · exact B347371
  · exact B347375
  · exact B347379
  · exact B347383
  · exact B347387
  · exact B347391
  · exact B347395
  · exact B347399
  · exact B347403
  · exact B347407
  · exact B347411
  · exact B347415
  · exact B347419
  · exact B347423
  · exact B347427
  · exact B347431
  · exact B347435
  · exact B347439
  · exact B347443
  · exact B347447
  · exact B347451
  · exact B347455
  · exact B347459
  · exact B347463
  · exact B347467
  · exact B347471
  · exact B347475
  · exact B347479
  · exact B347483
  · exact B347487
  · exact B347491
  · exact B347495
  · exact B347499
  · exact B347503
  · exact B347507
  · exact B347511
  · exact B347515
  · exact B347519
  · exact B347523
  · exact B347527
  · exact B347531
  · exact B347535
  · exact B347539
  · exact B347543
  · exact B347547
  · exact B347551
  · exact B347555
  · exact B347559
  · exact B347563
  · exact B347567
  · exact B347571
  · exact B347575
  · exact B347579
  · exact B347583
  · exact B347587
  · exact B347591
  · exact B347595
  · exact B347599
  · exact B347603
  · exact B347607
  · exact B347611
  · exact B347615
  · exact B347619
  · exact B347623
  · exact B347627
  · exact B347631
  · exact B347635
  · exact B347639
  · exact B347643
  · exact B347647
  · exact B347651
  · exact B347655
  · exact B347659
  · exact B347663
  · exact B347667
  · exact B347671
  · exact B347675
  · exact B347679
  · exact B347683
  · exact B347687
  · exact B347691
  · exact B347695
  · exact B347699
  · exact B347703
  · exact B347707
  · exact B347711
  · exact B347715
  · exact B347719
  · exact B347723
  · exact B347727
  · exact B347731
  · exact B347735
  · exact B347739
  · exact B347743
  · exact B347747
  · exact B347751
  · exact B347755
  · exact B347759
  · exact B347763
  · exact B347767
  · exact B347771
  · exact B347775
  · exact B347779
  · exact B347783
  · exact B347787
  · exact B347791
  · exact B347795
  · exact B347799
  · exact B347803
  · exact B347807
  · exact B347811
  · exact B347815
  · exact B347819
  · exact B347823
  · exact B347827
  · exact B347831
  · exact B347835
  · exact B347839
  · exact B347843
  · exact B347847
  · exact B347851
  · exact B347855
  · exact B347859
  · exact B347863
  · exact B347867
  · exact B347871
  · exact B347875
  · exact B347879
  · exact B347883
  · exact B347887
  · exact B347891
  · exact B347895
  · exact B347899
  · exact B347903
  · exact B347907
  · exact B347911
  · exact B347915
  · exact B347919
  · exact B347923
  · exact B347927
  · exact B347931
  · exact B347935
  · exact B347939
  · exact B347943
  · exact B347947
  · exact B347951
  · exact B347955
  · exact B347959
  · exact B347963
  · exact B347967
  · exact B347971
  · exact B347975
  · exact B347979
  · exact B347983
  · exact B347987
  · exact B347991
  · exact B347995
  · exact B347999
  · exact B348003
  · exact B348007
  · exact B348011
  · exact B348015
  · exact B348019
  · exact B348023
  · exact B348027
  · exact B348031
  · exact B348035
  · exact B348039
  · exact B348043
  · exact B348047
  · exact B348051
  · exact B348055
  · exact B348059
  · exact B348063
  · exact B348067
  · exact B348071
  · exact B348075
  · exact B348079
  · exact B348083
  · exact B348087
  · exact B348091
  · exact B348095
  · exact B348099
  · exact B348103
  · exact B348107
  · exact B348111
  · exact B348115
  · exact B348119
  · exact B348123
  · exact B348127
  · exact B348131
  · exact B348135
  · exact B348139
  · exact B348143
  · exact B348147
  · exact B348151
  · exact B348155
  · exact B348159
  · exact B348163
  · exact B348167
  · exact B348171
  · exact B348175
  · exact B348179
  · exact B348183
  · exact B348187
  · exact B348191
  · exact B348195
  · exact B348199
  · exact B348203
  · exact B348207
  · exact B348211
  · exact B348215
  · exact B348219
  · exact B348223
  · exact B348227
  · exact B348231
  · exact B348235
  · exact B348239
  · exact B348243
  · exact B348247
  · exact B348251
  · exact B348255
  · exact B348259
  · exact B348263
  · exact B348267
  · exact B348271
  · exact B348275
  · exact B348279
  · exact B348283
  · exact B348287
  · exact B348291
  · exact B348295
  · exact B348299
  · exact B348303
  · exact B348307
  · exact B348311
  · exact B348315
  · exact B348319
  · exact B348323
  · exact B348327
  · exact B348331
  · exact B348335
  · exact B348339
  · exact B348343
  · exact B348347
  · exact B348351
  · exact B348355
  · exact B348359
  · exact B348363
  · exact B348367
  · exact B348371
  · exact B348375
  · exact B348379
  · exact B348383
  · exact B348387
  · exact B348391
  · exact B348395
  · exact B348399
  · exact B348403
  · exact B348407
  · exact B348411
  · exact B348415
  · exact B348419
  · exact B348423
  · exact B348427
  · exact B348431
  · exact B348435
  · exact B348439
  · exact B348443
  · exact B348447
  · exact B348451
  · exact B348455
  · exact B348459
  · exact B348463
  · exact B348467
  · exact B348471
  · exact B348475
  · exact B348479
  · exact B348483
  · exact B348487
  · exact B348491
  · exact B348495
  · exact B348499
  · exact B348503
  · exact B348507
  · exact B348511
  · exact B348515
  · exact B348519
  · exact B348523
  · exact B348527
  · exact B348531
  · exact B348535
  · exact B348539
  · exact B348543
  · exact B348547
  · exact B348551
  · exact B348555
  · exact B348559
  · exact B348563
  · exact B348567
  · exact B348571
  · exact B348575
  · exact B348579
  · exact B348583
  · exact B348587
  · exact B348591
  · exact B348595
  · exact B348599
  · exact B348603
  · exact B348607
  · exact B348611
  · exact B348615
  · exact B348619
  · exact B348623
  · exact B348627
  · exact B348631
  · exact B348635
  · exact B348639
  · exact B348643
  · exact B348647
  · exact B348651
  · exact B348655
  · exact B348659
  · exact B348663
  · exact B348667
  · exact B348671
  · exact B348675
  · exact B348679
  · exact B348683
  · exact B348687
  · exact B348691
  · exact B348695
  · exact B348699
  · exact B348703
  · exact B348707
  · exact B348711
  · exact B348715
  · exact B348719
  · exact B348723
  · exact B348727
  · exact B348731
  · exact B348735
  · exact B348739
  · exact B348743
  · exact B348747
  · exact B348751
  · exact B348755
  · exact B348759
  · exact B348763
  · exact B348767
  · exact B348771
  · exact B348775
  · exact B348779
  · exact B348783
  · exact B348787
  · exact B348791
  · exact B348795
  · exact B348799
  · exact B348803
  · exact B348807
  · exact B348811
  · exact B348815
  · exact B348819
  · exact B348823
  · exact B348827
  · exact B348831
  · exact B348835
  · exact B348839
  · exact B348843
  · exact B348847
  · exact B348851
  · exact B348855
  · exact B348859
  · exact B348863
  · exact B348867
  · exact B348871
  · exact B348875
  · exact B348879
  · exact B348883
  · exact B348887
  · exact B348891
  · exact B348895
  · exact B348899
  · exact B348903
  · exact B348907
  · exact B348911
  · exact B348915
  · exact B348919
  · exact B348923
  · exact B348927
  · exact B348931
  · exact B348935
  · exact B348939
  · exact B348943
  · exact B348947
  · exact B348951
  · exact B348955
  · exact B348959
  · exact B348963
  · exact B348967
  · exact B348971
  · exact B348975
  · exact B348979
  · exact B348983
  · exact B348987
  · exact B348991
  · exact B348995
  · exact B348999
  · exact B349003
  · exact B349007
  · exact B349011
  · exact B349015
  · exact B349019
  · exact B349023
  · exact B349027
  · exact B349031
  · exact B349035
  · exact B349039
  · exact B349043
  · exact B349047
  · exact B349051
  · exact B349055
  · exact B349059
  · exact B349063
  · exact B349067
  · exact B349071
  · exact B349075
  · exact B349079
  · exact B349083
  · exact B349087
  · exact B349091
  · exact B349095
  · exact B349099
  · exact B349103
  · exact B349107
  · exact B349111
  · exact B349115
  · exact B349119
  · exact B349123
  · exact B349127
  · exact B349131
  · exact B349135
  · exact B349139
  · exact B349143
  · exact B349147
  · exact B349151
  · exact B349155
  · exact B349159
  · exact B349163
  · exact B349167
  · exact B349171
  · exact B349175
  · exact B349179
  · exact B349183
  · exact B349187
  · exact B349191
  · exact B349195
  · exact B349199
  · exact B349203
  · exact B349207
  · exact B349211
  · exact B349215
  · exact B349219
  · exact B349223
  · exact B349227
  · exact B349231
  · exact B349235
  · exact B349239
  · exact B349243
  · exact B349247
  · exact B349251
  · exact B349255
  · exact B349259
  · exact B349263
  · exact B349267
  · exact B349271
  · exact B349275
  · exact B349279
  · exact B349283
  · exact B349287
  · exact B349291
  · exact B349295
  · exact B349299
  · exact B349303
  · exact B349307
  · exact B349311
  · exact B349315
  · exact B349319
  · exact B349323
  · exact B349327
  · exact B349331
  · exact B349335
  · exact B349339
  · exact B349343
  · exact B349347
  · exact B349351
  · exact B349355
  · exact B349359
  · exact B349363
  · exact B349367
  · exact B349371
  · exact B349375
  · exact B349379
  · exact B349383
  · exact B349387
  · exact B349391
  · exact B349395
  · exact B349399
  · exact B349403
  · exact B349407
  · exact B349411
  · exact B349415
  · exact B349419
  · exact B349423
  · exact B349427
  · exact B349431
  · exact B349435
  · exact B349439
  · exact B349443
  · exact B349447
  · exact B349451
  · exact B349455
  · exact B349459
  · exact B349463
  · exact B349467
  · exact B349471
  · exact B349475
  · exact B349479
  · exact B349483
  · exact B349487
  · exact B349491
  · exact B349495
  · exact B349499
  · exact B349503
  · exact B349507
  · exact B349511
  · exact B349515
  · exact B349519
  · exact B349523
  · exact B349527
  · exact B349531
  · exact B349535
  · exact B349539
  · exact B349543
  · exact B349547
  · exact B349551

theorem C1 (j : ℕ) (h1 : 87388 ≤ j) (h2 : j ≤ 87687) : Blo 346754 (4 * j + 3) := by
  interval_cases j
  · exact B349555
  · exact B349559
  · exact B349563
  · exact B349567
  · exact B349571
  · exact B349575
  · exact B349579
  · exact B349583
  · exact B349587
  · exact B349591
  · exact B349595
  · exact B349599
  · exact B349603
  · exact B349607
  · exact B349611
  · exact B349615
  · exact B349619
  · exact B349623
  · exact B349627
  · exact B349631
  · exact B349635
  · exact B349639
  · exact B349643
  · exact B349647
  · exact B349651
  · exact B349655
  · exact B349659
  · exact B349663
  · exact B349667
  · exact B349671
  · exact B349675
  · exact B349679
  · exact B349683
  · exact B349687
  · exact B349691
  · exact B349695
  · exact B349699
  · exact B349703
  · exact B349707
  · exact B349711
  · exact B349715
  · exact B349719
  · exact B349723
  · exact B349727
  · exact B349731
  · exact B349735
  · exact B349739
  · exact B349743
  · exact B349747
  · exact B349751
  · exact B349755
  · exact B349759
  · exact B349763
  · exact B349767
  · exact B349771
  · exact B349775
  · exact B349779
  · exact B349783
  · exact B349787
  · exact B349791
  · exact B349795
  · exact B349799
  · exact B349803
  · exact B349807
  · exact B349811
  · exact B349815
  · exact B349819
  · exact B349823
  · exact B349827
  · exact B349831
  · exact B349835
  · exact B349839
  · exact B349843
  · exact B349847
  · exact B349851
  · exact B349855
  · exact B349859
  · exact B349863
  · exact B349867
  · exact B349871
  · exact B349875
  · exact B349879
  · exact B349883
  · exact B349887
  · exact B349891
  · exact B349895
  · exact B349899
  · exact B349903
  · exact B349907
  · exact B349911
  · exact B349915
  · exact B349919
  · exact B349923
  · exact B349927
  · exact B349931
  · exact B349935
  · exact B349939
  · exact B349943
  · exact B349947
  · exact B349951
  · exact B349955
  · exact B349959
  · exact B349963
  · exact B349967
  · exact B349971
  · exact B349975
  · exact B349979
  · exact B349983
  · exact B349987
  · exact B349991
  · exact B349995
  · exact B349999
  · exact B350003
  · exact B350007
  · exact B350011
  · exact B350015
  · exact B350019
  · exact B350023
  · exact B350027
  · exact B350031
  · exact B350035
  · exact B350039
  · exact B350043
  · exact B350047
  · exact B350051
  · exact B350055
  · exact B350059
  · exact B350063
  · exact B350067
  · exact B350071
  · exact B350075
  · exact B350079
  · exact B350083
  · exact B350087
  · exact B350091
  · exact B350095
  · exact B350099
  · exact B350103
  · exact B350107
  · exact B350111
  · exact B350115
  · exact B350119
  · exact B350123
  · exact B350127
  · exact B350131
  · exact B350135
  · exact B350139
  · exact B350143
  · exact B350147
  · exact B350151
  · exact B350155
  · exact B350159
  · exact B350163
  · exact B350167
  · exact B350171
  · exact B350175
  · exact B350179
  · exact B350183
  · exact B350187
  · exact B350191
  · exact B350195
  · exact B350199
  · exact B350203
  · exact B350207
  · exact B350211
  · exact B350215
  · exact B350219
  · exact B350223
  · exact B350227
  · exact B350231
  · exact B350235
  · exact B350239
  · exact B350243
  · exact B350247
  · exact B350251
  · exact B350255
  · exact B350259
  · exact B350263
  · exact B350267
  · exact B350271
  · exact B350275
  · exact B350279
  · exact B350283
  · exact B350287
  · exact B350291
  · exact B350295
  · exact B350299
  · exact B350303
  · exact B350307
  · exact B350311
  · exact B350315
  · exact B350319
  · exact B350323
  · exact B350327
  · exact B350331
  · exact B350335
  · exact B350339
  · exact B350343
  · exact B350347
  · exact B350351
  · exact B350355
  · exact B350359
  · exact B350363
  · exact B350367
  · exact B350371
  · exact B350375
  · exact B350379
  · exact B350383
  · exact B350387
  · exact B350391
  · exact B350395
  · exact B350399
  · exact B350403
  · exact B350407
  · exact B350411
  · exact B350415
  · exact B350419
  · exact B350423
  · exact B350427
  · exact B350431
  · exact B350435
  · exact B350439
  · exact B350443
  · exact B350447
  · exact B350451
  · exact B350455
  · exact B350459
  · exact B350463
  · exact B350467
  · exact B350471
  · exact B350475
  · exact B350479
  · exact B350483
  · exact B350487
  · exact B350491
  · exact B350495
  · exact B350499
  · exact B350503
  · exact B350507
  · exact B350511
  · exact B350515
  · exact B350519
  · exact B350523
  · exact B350527
  · exact B350531
  · exact B350535
  · exact B350539
  · exact B350543
  · exact B350547
  · exact B350551
  · exact B350555
  · exact B350559
  · exact B350563
  · exact B350567
  · exact B350571
  · exact B350575
  · exact B350579
  · exact B350583
  · exact B350587
  · exact B350591
  · exact B350595
  · exact B350599
  · exact B350603
  · exact B350607
  · exact B350611
  · exact B350615
  · exact B350619
  · exact B350623
  · exact B350627
  · exact B350631
  · exact B350635
  · exact B350639
  · exact B350643
  · exact B350647
  · exact B350651
  · exact B350655
  · exact B350659
  · exact B350663
  · exact B350667
  · exact B350671
  · exact B350675
  · exact B350679
  · exact B350683
  · exact B350687
  · exact B350691
  · exact B350695
  · exact B350699
  · exact B350703
  · exact B350707
  · exact B350711
  · exact B350715
  · exact B350719
  · exact B350723
  · exact B350727
  · exact B350731
  · exact B350735
  · exact B350739
  · exact B350743
  · exact B350747
  · exact B350751

theorem solution (m : ℕ) (hlo : 346754 ≤ m) (hhi : m ≤ 350754) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 86688 ≤ j := by omega
    have hj2 : j ≤ 87687 := by omega
    have hb : Blo 346754 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 87388 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
