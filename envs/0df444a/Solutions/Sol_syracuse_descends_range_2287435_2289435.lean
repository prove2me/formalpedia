-- Prove2me | solution 1 for syracuse_descends_range_2287435_2289435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:44.140741+00:00
-- url     : https://prove2.me/submissions/7af9caa3-9599-41fa-be82-62b224eaf6ea

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

theorem B2573365 : Blo 2287435 2573365 := bbase (se 5 (by rfl) ⟨120626, by rfl⟩ : syracuseStep 2573365 = 241253) (by norm_num)
theorem B3431153 : Blo 2287435 3431153 := bstep (se 2 (by rfl) ⟨1286682, by rfl⟩ : syracuseStep 3431153 = 2573365) B2573365
theorem B2287435 : Blo 2287435 2287435 := bstep (se 1 (by rfl) ⟨1715576, by rfl⟩ : syracuseStep 2287435 = 3431153) B3431153
theorem B2895041 : Blo 2287435 2895041 := bbase (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) (by norm_num)
theorem B7720109 : Blo 2287435 7720109 := bstep (se 3 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 7720109 = 2895041) B2895041
theorem B5146739 : Blo 2287435 5146739 := bstep (se 1 (by rfl) ⟨3860054, by rfl⟩ : syracuseStep 5146739 = 7720109) B7720109
theorem B3431159 : Blo 2287435 3431159 := bstep (se 1 (by rfl) ⟨2573369, by rfl⟩ : syracuseStep 3431159 = 5146739) B5146739
theorem B2287439 : Blo 2287435 2287439 := bstep (se 1 (by rfl) ⟨1715579, by rfl⟩ : syracuseStep 2287439 = 3431159) B3431159
theorem B3431165 : Blo 2287435 3431165 := bbase (se 3 (by rfl) ⟨643343, by rfl⟩ : syracuseStep 3431165 = 1286687) (by norm_num)
theorem B2287443 : Blo 2287435 2287443 := bstep (se 1 (by rfl) ⟨1715582, by rfl⟩ : syracuseStep 2287443 = 3431165) B3431165
theorem B5146757 : Blo 2287435 5146757 := bbase (se 4 (by rfl) ⟨482508, by rfl⟩ : syracuseStep 5146757 = 965017) (by norm_num)
theorem B3431171 : Blo 2287435 3431171 := bstep (se 1 (by rfl) ⟨2573378, by rfl⟩ : syracuseStep 3431171 = 5146757) B5146757
theorem B2287447 : Blo 2287435 2287447 := bstep (se 1 (by rfl) ⟨1715585, by rfl⟩ : syracuseStep 2287447 = 3431171) B3431171
theorem B3091549 : Blo 2287435 3091549 := bbase (se 3 (by rfl) ⟨579665, by rfl⟩ : syracuseStep 3091549 = 1159331) (by norm_num)
theorem B4122065 : Blo 2287435 4122065 := bstep (se 2 (by rfl) ⟨1545774, by rfl⟩ : syracuseStep 4122065 = 3091549) B3091549
theorem B2748043 : Blo 2287435 2748043 := bstep (se 1 (by rfl) ⟨2061032, by rfl⟩ : syracuseStep 2748043 = 4122065) B4122065
theorem B3664057 : Blo 2287435 3664057 := bstep (se 2 (by rfl) ⟨1374021, by rfl⟩ : syracuseStep 3664057 = 2748043) B2748043
theorem B4885409 : Blo 2287435 4885409 := bstep (se 2 (by rfl) ⟨1832028, by rfl⟩ : syracuseStep 4885409 = 3664057) B3664057
theorem B3256939 : Blo 2287435 3256939 := bstep (se 1 (by rfl) ⟨2442704, by rfl⟩ : syracuseStep 3256939 = 4885409) B4885409
theorem B4342585 : Blo 2287435 4342585 := bstep (se 2 (by rfl) ⟨1628469, by rfl⟩ : syracuseStep 4342585 = 3256939) B3256939
theorem B5790113 : Blo 2287435 5790113 := bstep (se 2 (by rfl) ⟨2171292, by rfl⟩ : syracuseStep 5790113 = 4342585) B4342585
theorem B3860075 : Blo 2287435 3860075 := bstep (se 1 (by rfl) ⟨2895056, by rfl⟩ : syracuseStep 3860075 = 5790113) B5790113
theorem B2573383 : Blo 2287435 2573383 := bstep (se 1 (by rfl) ⟨1930037, by rfl⟩ : syracuseStep 2573383 = 3860075) B3860075
theorem B3431177 : Blo 2287435 3431177 := bstep (se 2 (by rfl) ⟨1286691, by rfl⟩ : syracuseStep 3431177 = 2573383) B2573383
theorem B2287451 : Blo 2287435 2287451 := bstep (se 1 (by rfl) ⟨1715588, by rfl⟩ : syracuseStep 2287451 = 3431177) B3431177
theorem B11580245 : Blo 2287435 11580245 := bbase (se 9 (by rfl) ⟨33926, by rfl⟩ : syracuseStep 11580245 = 67853) (by norm_num)
theorem B7720163 : Blo 2287435 7720163 := bstep (se 1 (by rfl) ⟨5790122, by rfl⟩ : syracuseStep 7720163 = 11580245) B11580245
theorem B5146775 : Blo 2287435 5146775 := bstep (se 1 (by rfl) ⟨3860081, by rfl⟩ : syracuseStep 5146775 = 7720163) B7720163
theorem B3431183 : Blo 2287435 3431183 := bstep (se 1 (by rfl) ⟨2573387, by rfl⟩ : syracuseStep 3431183 = 5146775) B5146775
theorem B2287455 : Blo 2287435 2287455 := bstep (se 1 (by rfl) ⟨1715591, by rfl⟩ : syracuseStep 2287455 = 3431183) B3431183
theorem B3431189 : Blo 2287435 3431189 := bbase (se 6 (by rfl) ⟨80418, by rfl⟩ : syracuseStep 3431189 = 160837) (by norm_num)
theorem B2287459 : Blo 2287435 2287459 := bstep (se 1 (by rfl) ⟨1715594, by rfl⟩ : syracuseStep 2287459 = 3431189) B3431189
theorem B34344917 : Blo 2287435 34344917 := bbase (se 7 (by rfl) ⟨402479, by rfl⟩ : syracuseStep 34344917 = 804959) (by norm_num)
theorem B22896611 : Blo 2287435 22896611 := bstep (se 1 (by rfl) ⟨17172458, by rfl⟩ : syracuseStep 22896611 = 34344917) B34344917
theorem B15264407 : Blo 2287435 15264407 := bstep (se 1 (by rfl) ⟨11448305, by rfl⟩ : syracuseStep 15264407 = 22896611) B22896611
theorem B10176271 : Blo 2287435 10176271 := bstep (se 1 (by rfl) ⟨7632203, by rfl⟩ : syracuseStep 10176271 = 15264407) B15264407
theorem B54273445 : Blo 2287435 54273445 := bstep (se 4 (by rfl) ⟨5088135, by rfl⟩ : syracuseStep 54273445 = 10176271) B10176271
theorem B289458373 : Blo 2287435 289458373 := bstep (se 4 (by rfl) ⟨27136722, by rfl⟩ : syracuseStep 289458373 = 54273445) B54273445
theorem B385944497 : Blo 2287435 385944497 := bstep (se 2 (by rfl) ⟨144729186, by rfl⟩ : syracuseStep 385944497 = 289458373) B289458373
theorem B257296331 : Blo 2287435 257296331 := bstep (se 1 (by rfl) ⟨192972248, by rfl⟩ : syracuseStep 257296331 = 385944497) B385944497
theorem B171530887 : Blo 2287435 171530887 := bstep (se 1 (by rfl) ⟨128648165, by rfl⟩ : syracuseStep 171530887 = 257296331) B257296331
theorem B228707849 : Blo 2287435 228707849 := bstep (se 2 (by rfl) ⟨85765443, by rfl⟩ : syracuseStep 228707849 = 171530887) B171530887
theorem B152471899 : Blo 2287435 152471899 := bstep (se 1 (by rfl) ⟨114353924, by rfl⟩ : syracuseStep 152471899 = 228707849) B228707849
theorem B813183461 : Blo 2287435 813183461 := bstep (se 4 (by rfl) ⟨76235949, by rfl⟩ : syracuseStep 813183461 = 152471899) B152471899
theorem B542122307 : Blo 2287435 542122307 := bstep (se 1 (by rfl) ⟨406591730, by rfl⟩ : syracuseStep 542122307 = 813183461) B813183461
theorem B361414871 : Blo 2287435 361414871 := bstep (se 1 (by rfl) ⟨271061153, by rfl⟩ : syracuseStep 361414871 = 542122307) B542122307
theorem B240943247 : Blo 2287435 240943247 := bstep (se 1 (by rfl) ⟨180707435, by rfl⟩ : syracuseStep 240943247 = 361414871) B361414871
theorem B160628831 : Blo 2287435 160628831 := bstep (se 1 (by rfl) ⟨120471623, by rfl⟩ : syracuseStep 160628831 = 240943247) B240943247
theorem B107085887 : Blo 2287435 107085887 := bstep (se 1 (by rfl) ⟨80314415, by rfl⟩ : syracuseStep 107085887 = 160628831) B160628831
theorem B71390591 : Blo 2287435 71390591 := bstep (se 1 (by rfl) ⟨53542943, by rfl⟩ : syracuseStep 71390591 = 107085887) B107085887
theorem B47593727 : Blo 2287435 47593727 := bstep (se 1 (by rfl) ⟨35695295, by rfl⟩ : syracuseStep 47593727 = 71390591) B71390591
theorem B31729151 : Blo 2287435 31729151 := bstep (se 1 (by rfl) ⟨23796863, by rfl⟩ : syracuseStep 31729151 = 47593727) B47593727
theorem B21152767 : Blo 2287435 21152767 := bstep (se 1 (by rfl) ⟨15864575, by rfl⟩ : syracuseStep 21152767 = 31729151) B31729151
theorem B28203689 : Blo 2287435 28203689 := bstep (se 2 (by rfl) ⟨10576383, by rfl⟩ : syracuseStep 28203689 = 21152767) B21152767
theorem B18802459 : Blo 2287435 18802459 := bstep (se 1 (by rfl) ⟨14101844, by rfl⟩ : syracuseStep 18802459 = 28203689) B28203689
theorem B100279781 : Blo 2287435 100279781 := bstep (se 4 (by rfl) ⟨9401229, by rfl⟩ : syracuseStep 100279781 = 18802459) B18802459
theorem B66853187 : Blo 2287435 66853187 := bstep (se 1 (by rfl) ⟨50139890, by rfl⟩ : syracuseStep 66853187 = 100279781) B100279781
theorem B44568791 : Blo 2287435 44568791 := bstep (se 1 (by rfl) ⟨33426593, by rfl⟩ : syracuseStep 44568791 = 66853187) B66853187
theorem B29712527 : Blo 2287435 29712527 := bstep (se 1 (by rfl) ⟨22284395, by rfl⟩ : syracuseStep 29712527 = 44568791) B44568791
theorem B19808351 : Blo 2287435 19808351 := bstep (se 1 (by rfl) ⟨14856263, by rfl⟩ : syracuseStep 19808351 = 29712527) B29712527
theorem B13205567 : Blo 2287435 13205567 := bstep (se 1 (by rfl) ⟨9904175, by rfl⟩ : syracuseStep 13205567 = 19808351) B19808351
theorem B8803711 : Blo 2287435 8803711 := bstep (se 1 (by rfl) ⟨6602783, by rfl⟩ : syracuseStep 8803711 = 13205567) B13205567
theorem B46953125 : Blo 2287435 46953125 := bstep (se 4 (by rfl) ⟨4401855, by rfl⟩ : syracuseStep 46953125 = 8803711) B8803711
theorem B31302083 : Blo 2287435 31302083 := bstep (se 1 (by rfl) ⟨23476562, by rfl⟩ : syracuseStep 31302083 = 46953125) B46953125
theorem B83472221 : Blo 2287435 83472221 := bstep (se 3 (by rfl) ⟨15651041, by rfl⟩ : syracuseStep 83472221 = 31302083) B31302083
theorem B55648147 : Blo 2287435 55648147 := bstep (se 1 (by rfl) ⟨41736110, by rfl⟩ : syracuseStep 55648147 = 83472221) B83472221
theorem B74197529 : Blo 2287435 74197529 := bstep (se 2 (by rfl) ⟨27824073, by rfl⟩ : syracuseStep 74197529 = 55648147) B55648147
theorem B49465019 : Blo 2287435 49465019 := bstep (se 1 (by rfl) ⟨37098764, by rfl⟩ : syracuseStep 49465019 = 74197529) B74197529
theorem B32976679 : Blo 2287435 32976679 := bstep (se 1 (by rfl) ⟨24732509, by rfl⟩ : syracuseStep 32976679 = 49465019) B49465019
theorem B43968905 : Blo 2287435 43968905 := bstep (se 2 (by rfl) ⟨16488339, by rfl⟩ : syracuseStep 43968905 = 32976679) B32976679
theorem B29312603 : Blo 2287435 29312603 := bstep (se 1 (by rfl) ⟨21984452, by rfl⟩ : syracuseStep 29312603 = 43968905) B43968905
theorem B19541735 : Blo 2287435 19541735 := bstep (se 1 (by rfl) ⟨14656301, by rfl⟩ : syracuseStep 19541735 = 29312603) B29312603
theorem B13027823 : Blo 2287435 13027823 := bstep (se 1 (by rfl) ⟨9770867, by rfl⟩ : syracuseStep 13027823 = 19541735) B19541735
theorem B8685215 : Blo 2287435 8685215 := bstep (se 1 (by rfl) ⟨6513911, by rfl⟩ : syracuseStep 8685215 = 13027823) B13027823
theorem B5790143 : Blo 2287435 5790143 := bstep (se 1 (by rfl) ⟨4342607, by rfl⟩ : syracuseStep 5790143 = 8685215) B8685215
theorem B3860095 : Blo 2287435 3860095 := bstep (se 1 (by rfl) ⟨2895071, by rfl⟩ : syracuseStep 3860095 = 5790143) B5790143
theorem B5146793 : Blo 2287435 5146793 := bstep (se 2 (by rfl) ⟨1930047, by rfl⟩ : syracuseStep 5146793 = 3860095) B3860095
theorem B3431195 : Blo 2287435 3431195 := bstep (se 1 (by rfl) ⟨2573396, by rfl⟩ : syracuseStep 3431195 = 5146793) B5146793
theorem B2287463 : Blo 2287435 2287463 := bstep (se 1 (by rfl) ⟨1715597, by rfl⟩ : syracuseStep 2287463 = 3431195) B3431195
theorem B2573401 : Blo 2287435 2573401 := bbase (se 2 (by rfl) ⟨965025, by rfl⟩ : syracuseStep 2573401 = 1930051) (by norm_num)
theorem B3431201 : Blo 2287435 3431201 := bstep (se 2 (by rfl) ⟨1286700, by rfl⟩ : syracuseStep 3431201 = 2573401) B2573401
theorem B2287467 : Blo 2287435 2287467 := bstep (se 1 (by rfl) ⟨1715600, by rfl⟩ : syracuseStep 2287467 = 3431201) B3431201
theorem B5496133 : Blo 2287435 5496133 := bbase (se 4 (by rfl) ⟨515262, by rfl⟩ : syracuseStep 5496133 = 1030525) (by norm_num)
theorem B7328177 : Blo 2287435 7328177 := bstep (se 2 (by rfl) ⟨2748066, by rfl⟩ : syracuseStep 7328177 = 5496133) B5496133
theorem B4885451 : Blo 2287435 4885451 := bstep (se 1 (by rfl) ⟨3664088, by rfl⟩ : syracuseStep 4885451 = 7328177) B7328177
theorem B3256967 : Blo 2287435 3256967 := bstep (se 1 (by rfl) ⟨2442725, by rfl⟩ : syracuseStep 3256967 = 4885451) B4885451
theorem B8685245 : Blo 2287435 8685245 := bstep (se 3 (by rfl) ⟨1628483, by rfl⟩ : syracuseStep 8685245 = 3256967) B3256967
theorem B5790163 : Blo 2287435 5790163 := bstep (se 1 (by rfl) ⟨4342622, by rfl⟩ : syracuseStep 5790163 = 8685245) B8685245
theorem B7720217 : Blo 2287435 7720217 := bstep (se 2 (by rfl) ⟨2895081, by rfl⟩ : syracuseStep 7720217 = 5790163) B5790163
theorem B5146811 : Blo 2287435 5146811 := bstep (se 1 (by rfl) ⟨3860108, by rfl⟩ : syracuseStep 5146811 = 7720217) B7720217
theorem B3431207 : Blo 2287435 3431207 := bstep (se 1 (by rfl) ⟨2573405, by rfl⟩ : syracuseStep 3431207 = 5146811) B5146811
theorem B2287471 : Blo 2287435 2287471 := bstep (se 1 (by rfl) ⟨1715603, by rfl⟩ : syracuseStep 2287471 = 3431207) B3431207
theorem B3431213 : Blo 2287435 3431213 := bbase (se 3 (by rfl) ⟨643352, by rfl⟩ : syracuseStep 3431213 = 1286705) (by norm_num)
theorem B2287475 : Blo 2287435 2287475 := bstep (se 1 (by rfl) ⟨1715606, by rfl⟩ : syracuseStep 2287475 = 3431213) B3431213
theorem B5146829 : Blo 2287435 5146829 := bbase (se 3 (by rfl) ⟨965030, by rfl⟩ : syracuseStep 5146829 = 1930061) (by norm_num)
theorem B3431219 : Blo 2287435 3431219 := bstep (se 1 (by rfl) ⟨2573414, by rfl⟩ : syracuseStep 3431219 = 5146829) B5146829
theorem B2287479 : Blo 2287435 2287479 := bstep (se 1 (by rfl) ⟨1715609, by rfl⟩ : syracuseStep 2287479 = 3431219) B3431219
theorem B2895097 : Blo 2287435 2895097 := bbase (se 2 (by rfl) ⟨1085661, by rfl⟩ : syracuseStep 2895097 = 2171323) (by norm_num)
theorem B3860129 : Blo 2287435 3860129 := bstep (se 2 (by rfl) ⟨1447548, by rfl⟩ : syracuseStep 3860129 = 2895097) B2895097
theorem B2573419 : Blo 2287435 2573419 := bstep (se 1 (by rfl) ⟨1930064, by rfl⟩ : syracuseStep 2573419 = 3860129) B3860129
theorem B3431225 : Blo 2287435 3431225 := bstep (se 2 (by rfl) ⟨1286709, by rfl⟩ : syracuseStep 3431225 = 2573419) B2573419
theorem B2287483 : Blo 2287435 2287483 := bstep (se 1 (by rfl) ⟨1715612, by rfl⟩ : syracuseStep 2287483 = 3431225) B3431225
theorem B10992341 : Blo 2287435 10992341 := bbase (se 7 (by rfl) ⟨128816, by rfl⟩ : syracuseStep 10992341 = 257633) (by norm_num)
theorem B7328227 : Blo 2287435 7328227 := bstep (se 1 (by rfl) ⟨5496170, by rfl⟩ : syracuseStep 7328227 = 10992341) B10992341
theorem B9770969 : Blo 2287435 9770969 := bstep (se 2 (by rfl) ⟨3664113, by rfl⟩ : syracuseStep 9770969 = 7328227) B7328227
theorem B26055917 : Blo 2287435 26055917 := bstep (se 3 (by rfl) ⟨4885484, by rfl⟩ : syracuseStep 26055917 = 9770969) B9770969
theorem B17370611 : Blo 2287435 17370611 := bstep (se 1 (by rfl) ⟨13027958, by rfl⟩ : syracuseStep 17370611 = 26055917) B26055917
theorem B11580407 : Blo 2287435 11580407 := bstep (se 1 (by rfl) ⟨8685305, by rfl⟩ : syracuseStep 11580407 = 17370611) B17370611
theorem B7720271 : Blo 2287435 7720271 := bstep (se 1 (by rfl) ⟨5790203, by rfl⟩ : syracuseStep 7720271 = 11580407) B11580407
theorem B5146847 : Blo 2287435 5146847 := bstep (se 1 (by rfl) ⟨3860135, by rfl⟩ : syracuseStep 5146847 = 7720271) B7720271
theorem B3431231 : Blo 2287435 3431231 := bstep (se 1 (by rfl) ⟨2573423, by rfl⟩ : syracuseStep 3431231 = 5146847) B5146847
theorem B2287487 : Blo 2287435 2287487 := bstep (se 1 (by rfl) ⟨1715615, by rfl⟩ : syracuseStep 2287487 = 3431231) B3431231
theorem B3431237 : Blo 2287435 3431237 := bbase (se 4 (by rfl) ⟨321678, by rfl⟩ : syracuseStep 3431237 = 643357) (by norm_num)
theorem B2287491 : Blo 2287435 2287491 := bstep (se 1 (by rfl) ⟨1715618, by rfl⟩ : syracuseStep 2287491 = 3431237) B3431237
theorem B3860149 : Blo 2287435 3860149 := bbase (se 5 (by rfl) ⟨180944, by rfl⟩ : syracuseStep 3860149 = 361889) (by norm_num)
theorem B5146865 : Blo 2287435 5146865 := bstep (se 2 (by rfl) ⟨1930074, by rfl⟩ : syracuseStep 5146865 = 3860149) B3860149
theorem B3431243 : Blo 2287435 3431243 := bstep (se 1 (by rfl) ⟨2573432, by rfl⟩ : syracuseStep 3431243 = 5146865) B5146865
theorem B2287495 : Blo 2287435 2287495 := bstep (se 1 (by rfl) ⟨1715621, by rfl⟩ : syracuseStep 2287495 = 3431243) B3431243
theorem B2573437 : Blo 2287435 2573437 := bbase (se 3 (by rfl) ⟨482519, by rfl⟩ : syracuseStep 2573437 = 965039) (by norm_num)
theorem B3431249 : Blo 2287435 3431249 := bstep (se 2 (by rfl) ⟨1286718, by rfl⟩ : syracuseStep 3431249 = 2573437) B2573437
theorem B2287499 : Blo 2287435 2287499 := bstep (se 1 (by rfl) ⟨1715624, by rfl⟩ : syracuseStep 2287499 = 3431249) B3431249
theorem B7720325 : Blo 2287435 7720325 := bbase (se 4 (by rfl) ⟨723780, by rfl⟩ : syracuseStep 7720325 = 1447561) (by norm_num)
theorem B5146883 : Blo 2287435 5146883 := bstep (se 1 (by rfl) ⟨3860162, by rfl⟩ : syracuseStep 5146883 = 7720325) B7720325
theorem B3431255 : Blo 2287435 3431255 := bstep (se 1 (by rfl) ⟨2573441, by rfl⟩ : syracuseStep 3431255 = 5146883) B5146883
theorem B2287503 : Blo 2287435 2287503 := bstep (se 1 (by rfl) ⟨1715627, by rfl⟩ : syracuseStep 2287503 = 3431255) B3431255
theorem B3431261 : Blo 2287435 3431261 := bbase (se 3 (by rfl) ⟨643361, by rfl⟩ : syracuseStep 3431261 = 1286723) (by norm_num)
theorem B2287507 : Blo 2287435 2287507 := bstep (se 1 (by rfl) ⟨1715630, by rfl⟩ : syracuseStep 2287507 = 3431261) B3431261
theorem B5146901 : Blo 2287435 5146901 := bbase (se 6 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 5146901 = 241261) (by norm_num)
theorem B3431267 : Blo 2287435 3431267 := bstep (se 1 (by rfl) ⟨2573450, by rfl⟩ : syracuseStep 3431267 = 5146901) B5146901
theorem B2287511 : Blo 2287435 2287511 := bstep (se 1 (by rfl) ⟨1715633, by rfl⟩ : syracuseStep 2287511 = 3431267) B3431267
theorem B8685413 : Blo 2287435 8685413 := bbase (se 4 (by rfl) ⟨814257, by rfl⟩ : syracuseStep 8685413 = 1628515) (by norm_num)
theorem B5790275 : Blo 2287435 5790275 := bstep (se 1 (by rfl) ⟨4342706, by rfl⟩ : syracuseStep 5790275 = 8685413) B8685413
theorem B3860183 : Blo 2287435 3860183 := bstep (se 1 (by rfl) ⟨2895137, by rfl⟩ : syracuseStep 3860183 = 5790275) B5790275
theorem B2573455 : Blo 2287435 2573455 := bstep (se 1 (by rfl) ⟨1930091, by rfl⟩ : syracuseStep 2573455 = 3860183) B3860183
theorem B3431273 : Blo 2287435 3431273 := bstep (se 2 (by rfl) ⟨1286727, by rfl⟩ : syracuseStep 3431273 = 2573455) B2573455
theorem B2287515 : Blo 2287435 2287515 := bstep (se 1 (by rfl) ⟨1715636, by rfl⟩ : syracuseStep 2287515 = 3431273) B3431273
theorem B3664165 : Blo 2287435 3664165 := bbase (se 4 (by rfl) ⟨343515, by rfl⟩ : syracuseStep 3664165 = 687031) (by norm_num)
theorem B4885553 : Blo 2287435 4885553 := bstep (se 2 (by rfl) ⟨1832082, by rfl⟩ : syracuseStep 4885553 = 3664165) B3664165
theorem B13028141 : Blo 2287435 13028141 := bstep (se 3 (by rfl) ⟨2442776, by rfl⟩ : syracuseStep 13028141 = 4885553) B4885553
theorem B8685427 : Blo 2287435 8685427 := bstep (se 1 (by rfl) ⟨6514070, by rfl⟩ : syracuseStep 8685427 = 13028141) B13028141
theorem B11580569 : Blo 2287435 11580569 := bstep (se 2 (by rfl) ⟨4342713, by rfl⟩ : syracuseStep 11580569 = 8685427) B8685427
theorem B7720379 : Blo 2287435 7720379 := bstep (se 1 (by rfl) ⟨5790284, by rfl⟩ : syracuseStep 7720379 = 11580569) B11580569
theorem B5146919 : Blo 2287435 5146919 := bstep (se 1 (by rfl) ⟨3860189, by rfl⟩ : syracuseStep 5146919 = 7720379) B7720379
theorem B3431279 : Blo 2287435 3431279 := bstep (se 1 (by rfl) ⟨2573459, by rfl⟩ : syracuseStep 3431279 = 5146919) B5146919
theorem B2287519 : Blo 2287435 2287519 := bstep (se 1 (by rfl) ⟨1715639, by rfl⟩ : syracuseStep 2287519 = 3431279) B3431279
theorem B3431285 : Blo 2287435 3431285 := bbase (se 5 (by rfl) ⟨160841, by rfl⟩ : syracuseStep 3431285 = 321683) (by norm_num)
theorem B2287523 : Blo 2287435 2287523 := bstep (se 1 (by rfl) ⟨1715642, by rfl⟩ : syracuseStep 2287523 = 3431285) B3431285
theorem B7328357 : Blo 2287435 7328357 := bbase (se 4 (by rfl) ⟨687033, by rfl⟩ : syracuseStep 7328357 = 1374067) (by norm_num)
theorem B4885571 : Blo 2287435 4885571 := bstep (se 1 (by rfl) ⟨3664178, by rfl⟩ : syracuseStep 4885571 = 7328357) B7328357
theorem B3257047 : Blo 2287435 3257047 := bstep (se 1 (by rfl) ⟨2442785, by rfl⟩ : syracuseStep 3257047 = 4885571) B4885571
theorem B4342729 : Blo 2287435 4342729 := bstep (se 2 (by rfl) ⟨1628523, by rfl⟩ : syracuseStep 4342729 = 3257047) B3257047
theorem B5790305 : Blo 2287435 5790305 := bstep (se 2 (by rfl) ⟨2171364, by rfl⟩ : syracuseStep 5790305 = 4342729) B4342729
theorem B3860203 : Blo 2287435 3860203 := bstep (se 1 (by rfl) ⟨2895152, by rfl⟩ : syracuseStep 3860203 = 5790305) B5790305
theorem B5146937 : Blo 2287435 5146937 := bstep (se 2 (by rfl) ⟨1930101, by rfl⟩ : syracuseStep 5146937 = 3860203) B3860203
theorem B3431291 : Blo 2287435 3431291 := bstep (se 1 (by rfl) ⟨2573468, by rfl⟩ : syracuseStep 3431291 = 5146937) B5146937
theorem B2287527 : Blo 2287435 2287527 := bstep (se 1 (by rfl) ⟨1715645, by rfl⟩ : syracuseStep 2287527 = 3431291) B3431291
theorem B2573473 : Blo 2287435 2573473 := bbase (se 2 (by rfl) ⟨965052, by rfl⟩ : syracuseStep 2573473 = 1930105) (by norm_num)
theorem B3431297 : Blo 2287435 3431297 := bstep (se 2 (by rfl) ⟨1286736, by rfl⟩ : syracuseStep 3431297 = 2573473) B2573473
theorem B2287531 : Blo 2287435 2287531 := bstep (se 1 (by rfl) ⟨1715648, by rfl⟩ : syracuseStep 2287531 = 3431297) B3431297
theorem B5790325 : Blo 2287435 5790325 := bbase (se 5 (by rfl) ⟨271421, by rfl⟩ : syracuseStep 5790325 = 542843) (by norm_num)
theorem B7720433 : Blo 2287435 7720433 := bstep (se 2 (by rfl) ⟨2895162, by rfl⟩ : syracuseStep 7720433 = 5790325) B5790325
theorem B5146955 : Blo 2287435 5146955 := bstep (se 1 (by rfl) ⟨3860216, by rfl⟩ : syracuseStep 5146955 = 7720433) B7720433
theorem B3431303 : Blo 2287435 3431303 := bstep (se 1 (by rfl) ⟨2573477, by rfl⟩ : syracuseStep 3431303 = 5146955) B5146955
theorem B2287535 : Blo 2287435 2287535 := bstep (se 1 (by rfl) ⟨1715651, by rfl⟩ : syracuseStep 2287535 = 3431303) B3431303
theorem B3431309 : Blo 2287435 3431309 := bbase (se 3 (by rfl) ⟨643370, by rfl⟩ : syracuseStep 3431309 = 1286741) (by norm_num)
theorem B2287539 : Blo 2287435 2287539 := bstep (se 1 (by rfl) ⟨1715654, by rfl⟩ : syracuseStep 2287539 = 3431309) B3431309
theorem B5146973 : Blo 2287435 5146973 := bbase (se 3 (by rfl) ⟨965057, by rfl⟩ : syracuseStep 5146973 = 1930115) (by norm_num)
theorem B3431315 : Blo 2287435 3431315 := bstep (se 1 (by rfl) ⟨2573486, by rfl⟩ : syracuseStep 3431315 = 5146973) B5146973
theorem B2287543 : Blo 2287435 2287543 := bstep (se 1 (by rfl) ⟨1715657, by rfl⟩ : syracuseStep 2287543 = 3431315) B3431315
theorem B3860237 : Blo 2287435 3860237 := bbase (se 3 (by rfl) ⟨723794, by rfl⟩ : syracuseStep 3860237 = 1447589) (by norm_num)
theorem B2573491 : Blo 2287435 2573491 := bstep (se 1 (by rfl) ⟨1930118, by rfl⟩ : syracuseStep 2573491 = 3860237) B3860237
theorem B3431321 : Blo 2287435 3431321 := bstep (se 2 (by rfl) ⟨1286745, by rfl⟩ : syracuseStep 3431321 = 2573491) B2573491
theorem B2287547 : Blo 2287435 2287547 := bstep (se 1 (by rfl) ⟨1715660, by rfl⟩ : syracuseStep 2287547 = 3431321) B3431321
theorem B19542485 : Blo 2287435 19542485 := bbase (se 7 (by rfl) ⟨229013, by rfl⟩ : syracuseStep 19542485 = 458027) (by norm_num)
theorem B13028323 : Blo 2287435 13028323 := bstep (se 1 (by rfl) ⟨9771242, by rfl⟩ : syracuseStep 13028323 = 19542485) B19542485
theorem B17371097 : Blo 2287435 17371097 := bstep (se 2 (by rfl) ⟨6514161, by rfl⟩ : syracuseStep 17371097 = 13028323) B13028323
theorem B11580731 : Blo 2287435 11580731 := bstep (se 1 (by rfl) ⟨8685548, by rfl⟩ : syracuseStep 11580731 = 17371097) B17371097
theorem B7720487 : Blo 2287435 7720487 := bstep (se 1 (by rfl) ⟨5790365, by rfl⟩ : syracuseStep 7720487 = 11580731) B11580731
theorem B5146991 : Blo 2287435 5146991 := bstep (se 1 (by rfl) ⟨3860243, by rfl⟩ : syracuseStep 5146991 = 7720487) B7720487
theorem B3431327 : Blo 2287435 3431327 := bstep (se 1 (by rfl) ⟨2573495, by rfl⟩ : syracuseStep 3431327 = 5146991) B5146991
theorem B2287551 : Blo 2287435 2287551 := bstep (se 1 (by rfl) ⟨1715663, by rfl⟩ : syracuseStep 2287551 = 3431327) B3431327
theorem B3431333 : Blo 2287435 3431333 := bbase (se 4 (by rfl) ⟨321687, by rfl⟩ : syracuseStep 3431333 = 643375) (by norm_num)
theorem B2287555 : Blo 2287435 2287555 := bstep (se 1 (by rfl) ⟨1715666, by rfl⟩ : syracuseStep 2287555 = 3431333) B3431333
theorem B2895193 : Blo 2287435 2895193 := bbase (se 2 (by rfl) ⟨1085697, by rfl⟩ : syracuseStep 2895193 = 2171395) (by norm_num)
theorem B3860257 : Blo 2287435 3860257 := bstep (se 2 (by rfl) ⟨1447596, by rfl⟩ : syracuseStep 3860257 = 2895193) B2895193
theorem B5147009 : Blo 2287435 5147009 := bstep (se 2 (by rfl) ⟨1930128, by rfl⟩ : syracuseStep 5147009 = 3860257) B3860257
theorem B3431339 : Blo 2287435 3431339 := bstep (se 1 (by rfl) ⟨2573504, by rfl⟩ : syracuseStep 3431339 = 5147009) B5147009
theorem B2287559 : Blo 2287435 2287559 := bstep (se 1 (by rfl) ⟨1715669, by rfl⟩ : syracuseStep 2287559 = 3431339) B3431339
theorem B2573509 : Blo 2287435 2573509 := bbase (se 4 (by rfl) ⟨241266, by rfl⟩ : syracuseStep 2573509 = 482533) (by norm_num)
theorem B3431345 : Blo 2287435 3431345 := bstep (se 2 (by rfl) ⟨1286754, by rfl⟩ : syracuseStep 3431345 = 2573509) B2573509
theorem B2287563 : Blo 2287435 2287563 := bstep (se 1 (by rfl) ⟨1715672, by rfl⟩ : syracuseStep 2287563 = 3431345) B3431345
theorem B4342805 : Blo 2287435 4342805 := bbase (se 6 (by rfl) ⟨101784, by rfl⟩ : syracuseStep 4342805 = 203569) (by norm_num)
theorem B2895203 : Blo 2287435 2895203 := bstep (se 1 (by rfl) ⟨2171402, by rfl⟩ : syracuseStep 2895203 = 4342805) B4342805
theorem B7720541 : Blo 2287435 7720541 := bstep (se 3 (by rfl) ⟨1447601, by rfl⟩ : syracuseStep 7720541 = 2895203) B2895203
theorem B5147027 : Blo 2287435 5147027 := bstep (se 1 (by rfl) ⟨3860270, by rfl⟩ : syracuseStep 5147027 = 7720541) B7720541
theorem B3431351 : Blo 2287435 3431351 := bstep (se 1 (by rfl) ⟨2573513, by rfl⟩ : syracuseStep 3431351 = 5147027) B5147027
theorem B2287567 : Blo 2287435 2287567 := bstep (se 1 (by rfl) ⟨1715675, by rfl⟩ : syracuseStep 2287567 = 3431351) B3431351
theorem B3431357 : Blo 2287435 3431357 := bbase (se 3 (by rfl) ⟨643379, by rfl⟩ : syracuseStep 3431357 = 1286759) (by norm_num)
theorem B2287571 : Blo 2287435 2287571 := bstep (se 1 (by rfl) ⟨1715678, by rfl⟩ : syracuseStep 2287571 = 3431357) B3431357
theorem B5147045 : Blo 2287435 5147045 := bbase (se 4 (by rfl) ⟨482535, by rfl⟩ : syracuseStep 5147045 = 965071) (by norm_num)
theorem B3431363 : Blo 2287435 3431363 := bstep (se 1 (by rfl) ⟨2573522, by rfl⟩ : syracuseStep 3431363 = 5147045) B5147045
theorem B2287575 : Blo 2287435 2287575 := bstep (se 1 (by rfl) ⟨1715681, by rfl⟩ : syracuseStep 2287575 = 3431363) B3431363
theorem B5790437 : Blo 2287435 5790437 := bbase (se 4 (by rfl) ⟨542853, by rfl⟩ : syracuseStep 5790437 = 1085707) (by norm_num)
theorem B3860291 : Blo 2287435 3860291 := bstep (se 1 (by rfl) ⟨2895218, by rfl⟩ : syracuseStep 3860291 = 5790437) B5790437
theorem B2573527 : Blo 2287435 2573527 := bstep (se 1 (by rfl) ⟨1930145, by rfl⟩ : syracuseStep 2573527 = 3860291) B3860291
theorem B3431369 : Blo 2287435 3431369 := bstep (se 2 (by rfl) ⟨1286763, by rfl⟩ : syracuseStep 3431369 = 2573527) B2573527
theorem B2287579 : Blo 2287435 2287579 := bstep (se 1 (by rfl) ⟨1715684, by rfl⟩ : syracuseStep 2287579 = 3431369) B3431369
theorem B2442845 : Blo 2287435 2442845 := bbase (se 3 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 2442845 = 916067) (by norm_num)
theorem B6514253 : Blo 2287435 6514253 := bstep (se 3 (by rfl) ⟨1221422, by rfl⟩ : syracuseStep 6514253 = 2442845) B2442845
theorem B4342835 : Blo 2287435 4342835 := bstep (se 1 (by rfl) ⟨3257126, by rfl⟩ : syracuseStep 4342835 = 6514253) B6514253
theorem B11580893 : Blo 2287435 11580893 := bstep (se 3 (by rfl) ⟨2171417, by rfl⟩ : syracuseStep 11580893 = 4342835) B4342835
theorem B7720595 : Blo 2287435 7720595 := bstep (se 1 (by rfl) ⟨5790446, by rfl⟩ : syracuseStep 7720595 = 11580893) B11580893
theorem B5147063 : Blo 2287435 5147063 := bstep (se 1 (by rfl) ⟨3860297, by rfl⟩ : syracuseStep 5147063 = 7720595) B7720595
theorem B3431375 : Blo 2287435 3431375 := bstep (se 1 (by rfl) ⟨2573531, by rfl⟩ : syracuseStep 3431375 = 5147063) B5147063
theorem B2287583 : Blo 2287435 2287583 := bstep (se 1 (by rfl) ⟨1715687, by rfl⟩ : syracuseStep 2287583 = 3431375) B3431375
theorem B3431381 : Blo 2287435 3431381 := bbase (se 7 (by rfl) ⟨40211, by rfl⟩ : syracuseStep 3431381 = 80423) (by norm_num)
theorem B2287587 : Blo 2287435 2287587 := bstep (se 1 (by rfl) ⟨1715690, by rfl⟩ : syracuseStep 2287587 = 3431381) B3431381
theorem B8685701 : Blo 2287435 8685701 := bbase (se 4 (by rfl) ⟨814284, by rfl⟩ : syracuseStep 8685701 = 1628569) (by norm_num)
theorem B5790467 : Blo 2287435 5790467 := bstep (se 1 (by rfl) ⟨4342850, by rfl⟩ : syracuseStep 5790467 = 8685701) B8685701
theorem B3860311 : Blo 2287435 3860311 := bstep (se 1 (by rfl) ⟨2895233, by rfl⟩ : syracuseStep 3860311 = 5790467) B5790467
theorem B5147081 : Blo 2287435 5147081 := bstep (se 2 (by rfl) ⟨1930155, by rfl⟩ : syracuseStep 5147081 = 3860311) B3860311
theorem B3431387 : Blo 2287435 3431387 := bstep (se 1 (by rfl) ⟨2573540, by rfl⟩ : syracuseStep 3431387 = 5147081) B5147081
theorem B2287591 : Blo 2287435 2287591 := bstep (se 1 (by rfl) ⟨1715693, by rfl⟩ : syracuseStep 2287591 = 3431387) B3431387
theorem B2573545 : Blo 2287435 2573545 := bbase (se 2 (by rfl) ⟨965079, by rfl⟩ : syracuseStep 2573545 = 1930159) (by norm_num)
theorem B3431393 : Blo 2287435 3431393 := bstep (se 2 (by rfl) ⟨1286772, by rfl⟩ : syracuseStep 3431393 = 2573545) B2573545
theorem B2287595 : Blo 2287435 2287595 := bstep (se 1 (by rfl) ⟨1715696, by rfl⟩ : syracuseStep 2287595 = 3431393) B3431393
theorem B13028597 : Blo 2287435 13028597 := bbase (se 5 (by rfl) ⟨610715, by rfl⟩ : syracuseStep 13028597 = 1221431) (by norm_num)
theorem B8685731 : Blo 2287435 8685731 := bstep (se 1 (by rfl) ⟨6514298, by rfl⟩ : syracuseStep 8685731 = 13028597) B13028597
theorem B5790487 : Blo 2287435 5790487 := bstep (se 1 (by rfl) ⟨4342865, by rfl⟩ : syracuseStep 5790487 = 8685731) B8685731
theorem B7720649 : Blo 2287435 7720649 := bstep (se 2 (by rfl) ⟨2895243, by rfl⟩ : syracuseStep 7720649 = 5790487) B5790487
theorem B5147099 : Blo 2287435 5147099 := bstep (se 1 (by rfl) ⟨3860324, by rfl⟩ : syracuseStep 5147099 = 7720649) B7720649
theorem B3431399 : Blo 2287435 3431399 := bstep (se 1 (by rfl) ⟨2573549, by rfl⟩ : syracuseStep 3431399 = 5147099) B5147099
theorem B2287599 : Blo 2287435 2287599 := bstep (se 1 (by rfl) ⟨1715699, by rfl⟩ : syracuseStep 2287599 = 3431399) B3431399
theorem B3431405 : Blo 2287435 3431405 := bbase (se 3 (by rfl) ⟨643388, by rfl⟩ : syracuseStep 3431405 = 1286777) (by norm_num)
theorem B2287603 : Blo 2287435 2287603 := bstep (se 1 (by rfl) ⟨1715702, by rfl⟩ : syracuseStep 2287603 = 3431405) B3431405
theorem B5147117 : Blo 2287435 5147117 := bbase (se 3 (by rfl) ⟨965084, by rfl⟩ : syracuseStep 5147117 = 1930169) (by norm_num)
theorem B3431411 : Blo 2287435 3431411 := bstep (se 1 (by rfl) ⟨2573558, by rfl⟩ : syracuseStep 3431411 = 5147117) B5147117
theorem B2287607 : Blo 2287435 2287607 := bstep (se 1 (by rfl) ⟨1715705, by rfl⟩ : syracuseStep 2287607 = 3431411) B3431411
theorem B3091765 : Blo 2287435 3091765 := bbase (se 5 (by rfl) ⟨144926, by rfl⟩ : syracuseStep 3091765 = 289853) (by norm_num)
theorem B4122353 : Blo 2287435 4122353 := bstep (se 2 (by rfl) ⟨1545882, by rfl⟩ : syracuseStep 4122353 = 3091765) B3091765
theorem B10992941 : Blo 2287435 10992941 := bstep (se 3 (by rfl) ⟨2061176, by rfl⟩ : syracuseStep 10992941 = 4122353) B4122353
theorem B7328627 : Blo 2287435 7328627 := bstep (se 1 (by rfl) ⟨5496470, by rfl⟩ : syracuseStep 7328627 = 10992941) B10992941
theorem B4885751 : Blo 2287435 4885751 := bstep (se 1 (by rfl) ⟨3664313, by rfl⟩ : syracuseStep 4885751 = 7328627) B7328627
theorem B3257167 : Blo 2287435 3257167 := bstep (se 1 (by rfl) ⟨2442875, by rfl⟩ : syracuseStep 3257167 = 4885751) B4885751
theorem B4342889 : Blo 2287435 4342889 := bstep (se 2 (by rfl) ⟨1628583, by rfl⟩ : syracuseStep 4342889 = 3257167) B3257167
theorem B2895259 : Blo 2287435 2895259 := bstep (se 1 (by rfl) ⟨2171444, by rfl⟩ : syracuseStep 2895259 = 4342889) B4342889
theorem B3860345 : Blo 2287435 3860345 := bstep (se 2 (by rfl) ⟨1447629, by rfl⟩ : syracuseStep 3860345 = 2895259) B2895259
theorem B2573563 : Blo 2287435 2573563 := bstep (se 1 (by rfl) ⟨1930172, by rfl⟩ : syracuseStep 2573563 = 3860345) B3860345
theorem B3431417 : Blo 2287435 3431417 := bstep (se 2 (by rfl) ⟨1286781, by rfl⟩ : syracuseStep 3431417 = 2573563) B2573563
theorem B2287611 : Blo 2287435 2287611 := bstep (se 1 (by rfl) ⟨1715708, by rfl⟩ : syracuseStep 2287611 = 3431417) B3431417
theorem B9660149 : Blo 2287435 9660149 := bbase (se 5 (by rfl) ⟨452819, by rfl⟩ : syracuseStep 9660149 = 905639) (by norm_num)
theorem B6440099 : Blo 2287435 6440099 := bstep (se 1 (by rfl) ⟨4830074, by rfl⟩ : syracuseStep 6440099 = 9660149) B9660149
theorem B68694389 : Blo 2287435 68694389 := bstep (se 5 (by rfl) ⟨3220049, by rfl⟩ : syracuseStep 68694389 = 6440099) B6440099
theorem B45796259 : Blo 2287435 45796259 := bstep (se 1 (by rfl) ⟨34347194, by rfl⟩ : syracuseStep 45796259 = 68694389) B68694389
theorem B30530839 : Blo 2287435 30530839 := bstep (se 1 (by rfl) ⟨22898129, by rfl⟩ : syracuseStep 30530839 = 45796259) B45796259
theorem B40707785 : Blo 2287435 40707785 := bstep (se 2 (by rfl) ⟨15265419, by rfl⟩ : syracuseStep 40707785 = 30530839) B30530839
theorem B108554093 : Blo 2287435 108554093 := bstep (se 3 (by rfl) ⟨20353892, by rfl⟩ : syracuseStep 108554093 = 40707785) B40707785
theorem B72369395 : Blo 2287435 72369395 := bstep (se 1 (by rfl) ⟨54277046, by rfl⟩ : syracuseStep 72369395 = 108554093) B108554093
theorem B48246263 : Blo 2287435 48246263 := bstep (se 1 (by rfl) ⟨36184697, by rfl⟩ : syracuseStep 48246263 = 72369395) B72369395
theorem B32164175 : Blo 2287435 32164175 := bstep (se 1 (by rfl) ⟨24123131, by rfl⟩ : syracuseStep 32164175 = 48246263) B48246263
theorem B85771133 : Blo 2287435 85771133 := bstep (se 3 (by rfl) ⟨16082087, by rfl⟩ : syracuseStep 85771133 = 32164175) B32164175
theorem B57180755 : Blo 2287435 57180755 := bstep (se 1 (by rfl) ⟨42885566, by rfl⟩ : syracuseStep 57180755 = 85771133) B85771133
theorem B38120503 : Blo 2287435 38120503 := bstep (se 1 (by rfl) ⟨28590377, by rfl⟩ : syracuseStep 38120503 = 57180755) B57180755
theorem B50827337 : Blo 2287435 50827337 := bstep (se 2 (by rfl) ⟨19060251, by rfl⟩ : syracuseStep 50827337 = 38120503) B38120503
theorem B33884891 : Blo 2287435 33884891 := bstep (se 1 (by rfl) ⟨25413668, by rfl⟩ : syracuseStep 33884891 = 50827337) B50827337
theorem B22589927 : Blo 2287435 22589927 := bstep (se 1 (by rfl) ⟨16942445, by rfl⟩ : syracuseStep 22589927 = 33884891) B33884891
theorem B15059951 : Blo 2287435 15059951 := bstep (se 1 (by rfl) ⟨11294963, by rfl⟩ : syracuseStep 15059951 = 22589927) B22589927
theorem B10039967 : Blo 2287435 10039967 := bstep (se 1 (by rfl) ⟨7529975, by rfl⟩ : syracuseStep 10039967 = 15059951) B15059951
theorem B6693311 : Blo 2287435 6693311 := bstep (se 1 (by rfl) ⟨5019983, by rfl⟩ : syracuseStep 6693311 = 10039967) B10039967
theorem B17848829 : Blo 2287435 17848829 := bstep (se 3 (by rfl) ⟨3346655, by rfl⟩ : syracuseStep 17848829 = 6693311) B6693311
theorem B47596877 : Blo 2287435 47596877 := bstep (se 3 (by rfl) ⟨8924414, by rfl⟩ : syracuseStep 47596877 = 17848829) B17848829
theorem B507700021 : Blo 2287435 507700021 := bstep (se 5 (by rfl) ⟨23798438, by rfl⟩ : syracuseStep 507700021 = 47596877) B47596877
theorem B676933361 : Blo 2287435 676933361 := bstep (se 2 (by rfl) ⟨253850010, by rfl⟩ : syracuseStep 676933361 = 507700021) B507700021
theorem B451288907 : Blo 2287435 451288907 := bstep (se 1 (by rfl) ⟨338466680, by rfl⟩ : syracuseStep 451288907 = 676933361) B676933361
theorem B300859271 : Blo 2287435 300859271 := bstep (se 1 (by rfl) ⟨225644453, by rfl⟩ : syracuseStep 300859271 = 451288907) B451288907
theorem B200572847 : Blo 2287435 200572847 := bstep (se 1 (by rfl) ⟨150429635, by rfl⟩ : syracuseStep 200572847 = 300859271) B300859271
theorem B133715231 : Blo 2287435 133715231 := bstep (se 1 (by rfl) ⟨100286423, by rfl⟩ : syracuseStep 133715231 = 200572847) B200572847
theorem B89143487 : Blo 2287435 89143487 := bstep (se 1 (by rfl) ⟨66857615, by rfl⟩ : syracuseStep 89143487 = 133715231) B133715231
theorem B59428991 : Blo 2287435 59428991 := bstep (se 1 (by rfl) ⟨44571743, by rfl⟩ : syracuseStep 59428991 = 89143487) B89143487
theorem B158477309 : Blo 2287435 158477309 := bstep (se 3 (by rfl) ⟨29714495, by rfl⟩ : syracuseStep 158477309 = 59428991) B59428991
theorem B105651539 : Blo 2287435 105651539 := bstep (se 1 (by rfl) ⟨79238654, by rfl⟩ : syracuseStep 105651539 = 158477309) B158477309
theorem B70434359 : Blo 2287435 70434359 := bstep (se 1 (by rfl) ⟨52825769, by rfl⟩ : syracuseStep 70434359 = 105651539) B105651539
theorem B46956239 : Blo 2287435 46956239 := bstep (se 1 (by rfl) ⟨35217179, by rfl⟩ : syracuseStep 46956239 = 70434359) B70434359
theorem B31304159 : Blo 2287435 31304159 := bstep (se 1 (by rfl) ⟨23478119, by rfl⟩ : syracuseStep 31304159 = 46956239) B46956239
theorem B20869439 : Blo 2287435 20869439 := bstep (se 1 (by rfl) ⟨15652079, by rfl⟩ : syracuseStep 20869439 = 31304159) B31304159
theorem B222607349 : Blo 2287435 222607349 := bstep (se 5 (by rfl) ⟨10434719, by rfl⟩ : syracuseStep 222607349 = 20869439) B20869439
theorem B148404899 : Blo 2287435 148404899 := bstep (se 1 (by rfl) ⟨111303674, by rfl⟩ : syracuseStep 148404899 = 222607349) B222607349
theorem B98936599 : Blo 2287435 98936599 := bstep (se 1 (by rfl) ⟨74202449, by rfl⟩ : syracuseStep 98936599 = 148404899) B148404899
theorem B131915465 : Blo 2287435 131915465 := bstep (se 2 (by rfl) ⟨49468299, by rfl⟩ : syracuseStep 131915465 = 98936599) B98936599
theorem B87943643 : Blo 2287435 87943643 := bstep (se 1 (by rfl) ⟨65957732, by rfl⟩ : syracuseStep 87943643 = 131915465) B131915465
theorem B58629095 : Blo 2287435 58629095 := bstep (se 1 (by rfl) ⟨43971821, by rfl⟩ : syracuseStep 58629095 = 87943643) B87943643
theorem B39086063 : Blo 2287435 39086063 := bstep (se 1 (by rfl) ⟨29314547, by rfl⟩ : syracuseStep 39086063 = 58629095) B58629095
theorem B26057375 : Blo 2287435 26057375 := bstep (se 1 (by rfl) ⟨19543031, by rfl⟩ : syracuseStep 26057375 = 39086063) B39086063
theorem B17371583 : Blo 2287435 17371583 := bstep (se 1 (by rfl) ⟨13028687, by rfl⟩ : syracuseStep 17371583 = 26057375) B26057375
theorem B11581055 : Blo 2287435 11581055 := bstep (se 1 (by rfl) ⟨8685791, by rfl⟩ : syracuseStep 11581055 = 17371583) B17371583
theorem B7720703 : Blo 2287435 7720703 := bstep (se 1 (by rfl) ⟨5790527, by rfl⟩ : syracuseStep 7720703 = 11581055) B11581055
theorem B5147135 : Blo 2287435 5147135 := bstep (se 1 (by rfl) ⟨3860351, by rfl⟩ : syracuseStep 5147135 = 7720703) B7720703
theorem B3431423 : Blo 2287435 3431423 := bstep (se 1 (by rfl) ⟨2573567, by rfl⟩ : syracuseStep 3431423 = 5147135) B5147135
theorem B2287615 : Blo 2287435 2287615 := bstep (se 1 (by rfl) ⟨1715711, by rfl⟩ : syracuseStep 2287615 = 3431423) B3431423
theorem B3431429 : Blo 2287435 3431429 := bbase (se 4 (by rfl) ⟨321696, by rfl⟩ : syracuseStep 3431429 = 643393) (by norm_num)
theorem B2287619 : Blo 2287435 2287619 := bstep (se 1 (by rfl) ⟨1715714, by rfl⟩ : syracuseStep 2287619 = 3431429) B3431429
theorem B3860365 : Blo 2287435 3860365 := bbase (se 3 (by rfl) ⟨723818, by rfl⟩ : syracuseStep 3860365 = 1447637) (by norm_num)
theorem B5147153 : Blo 2287435 5147153 := bstep (se 2 (by rfl) ⟨1930182, by rfl⟩ : syracuseStep 5147153 = 3860365) B3860365
theorem B3431435 : Blo 2287435 3431435 := bstep (se 1 (by rfl) ⟨2573576, by rfl⟩ : syracuseStep 3431435 = 5147153) B5147153
theorem B2287623 : Blo 2287435 2287623 := bstep (se 1 (by rfl) ⟨1715717, by rfl⟩ : syracuseStep 2287623 = 3431435) B3431435
theorem B2573581 : Blo 2287435 2573581 := bbase (se 3 (by rfl) ⟨482546, by rfl⟩ : syracuseStep 2573581 = 965093) (by norm_num)
theorem B3431441 : Blo 2287435 3431441 := bstep (se 2 (by rfl) ⟨1286790, by rfl⟩ : syracuseStep 3431441 = 2573581) B2573581
theorem B2287627 : Blo 2287435 2287627 := bstep (se 1 (by rfl) ⟨1715720, by rfl⟩ : syracuseStep 2287627 = 3431441) B3431441
theorem B7720757 : Blo 2287435 7720757 := bbase (se 5 (by rfl) ⟨361910, by rfl⟩ : syracuseStep 7720757 = 723821) (by norm_num)
theorem B5147171 : Blo 2287435 5147171 := bstep (se 1 (by rfl) ⟨3860378, by rfl⟩ : syracuseStep 5147171 = 7720757) B7720757
theorem B3431447 : Blo 2287435 3431447 := bstep (se 1 (by rfl) ⟨2573585, by rfl⟩ : syracuseStep 3431447 = 5147171) B5147171
theorem B2287631 : Blo 2287435 2287631 := bstep (se 1 (by rfl) ⟨1715723, by rfl⟩ : syracuseStep 2287631 = 3431447) B3431447
theorem B3431453 : Blo 2287435 3431453 := bbase (se 3 (by rfl) ⟨643397, by rfl⟩ : syracuseStep 3431453 = 1286795) (by norm_num)
theorem B2287635 : Blo 2287435 2287635 := bstep (se 1 (by rfl) ⟨1715726, by rfl⟩ : syracuseStep 2287635 = 3431453) B3431453
theorem B5147189 : Blo 2287435 5147189 := bbase (se 5 (by rfl) ⟨241274, by rfl⟩ : syracuseStep 5147189 = 482549) (by norm_num)
theorem B3431459 : Blo 2287435 3431459 := bstep (se 1 (by rfl) ⟨2573594, by rfl⟩ : syracuseStep 3431459 = 5147189) B5147189
theorem B2287639 : Blo 2287435 2287639 := bstep (se 1 (by rfl) ⟨1715729, by rfl⟩ : syracuseStep 2287639 = 3431459) B3431459
theorem B9771637 : Blo 2287435 9771637 := bbase (se 5 (by rfl) ⟨458045, by rfl⟩ : syracuseStep 9771637 = 916091) (by norm_num)
theorem B13028849 : Blo 2287435 13028849 := bstep (se 2 (by rfl) ⟨4885818, by rfl⟩ : syracuseStep 13028849 = 9771637) B9771637
theorem B8685899 : Blo 2287435 8685899 := bstep (se 1 (by rfl) ⟨6514424, by rfl⟩ : syracuseStep 8685899 = 13028849) B13028849
theorem B5790599 : Blo 2287435 5790599 := bstep (se 1 (by rfl) ⟨4342949, by rfl⟩ : syracuseStep 5790599 = 8685899) B8685899
theorem B3860399 : Blo 2287435 3860399 := bstep (se 1 (by rfl) ⟨2895299, by rfl⟩ : syracuseStep 3860399 = 5790599) B5790599
theorem B2573599 : Blo 2287435 2573599 := bstep (se 1 (by rfl) ⟨1930199, by rfl⟩ : syracuseStep 2573599 = 3860399) B3860399
theorem B3431465 : Blo 2287435 3431465 := bstep (se 2 (by rfl) ⟨1286799, by rfl⟩ : syracuseStep 3431465 = 2573599) B2573599
theorem B2287643 : Blo 2287435 2287643 := bstep (se 1 (by rfl) ⟨1715732, by rfl⟩ : syracuseStep 2287643 = 3431465) B3431465
theorem B9771653 : Blo 2287435 9771653 := bbase (se 4 (by rfl) ⟨916092, by rfl⟩ : syracuseStep 9771653 = 1832185) (by norm_num)
theorem B6514435 : Blo 2287435 6514435 := bstep (se 1 (by rfl) ⟨4885826, by rfl⟩ : syracuseStep 6514435 = 9771653) B9771653
theorem B8685913 : Blo 2287435 8685913 := bstep (se 2 (by rfl) ⟨3257217, by rfl⟩ : syracuseStep 8685913 = 6514435) B6514435
theorem B11581217 : Blo 2287435 11581217 := bstep (se 2 (by rfl) ⟨4342956, by rfl⟩ : syracuseStep 11581217 = 8685913) B8685913
theorem B7720811 : Blo 2287435 7720811 := bstep (se 1 (by rfl) ⟨5790608, by rfl⟩ : syracuseStep 7720811 = 11581217) B11581217
theorem B5147207 : Blo 2287435 5147207 := bstep (se 1 (by rfl) ⟨3860405, by rfl⟩ : syracuseStep 5147207 = 7720811) B7720811
theorem B3431471 : Blo 2287435 3431471 := bstep (se 1 (by rfl) ⟨2573603, by rfl⟩ : syracuseStep 3431471 = 5147207) B5147207
theorem B2287647 : Blo 2287435 2287647 := bstep (se 1 (by rfl) ⟨1715735, by rfl⟩ : syracuseStep 2287647 = 3431471) B3431471
theorem B3431477 : Blo 2287435 3431477 := bbase (se 5 (by rfl) ⟨160850, by rfl⟩ : syracuseStep 3431477 = 321701) (by norm_num)
theorem B2287651 : Blo 2287435 2287651 := bstep (se 1 (by rfl) ⟨1715738, by rfl⟩ : syracuseStep 2287651 = 3431477) B3431477
theorem B5790629 : Blo 2287435 5790629 := bbase (se 4 (by rfl) ⟨542871, by rfl⟩ : syracuseStep 5790629 = 1085743) (by norm_num)
theorem B3860419 : Blo 2287435 3860419 := bstep (se 1 (by rfl) ⟨2895314, by rfl⟩ : syracuseStep 3860419 = 5790629) B5790629
theorem B5147225 : Blo 2287435 5147225 := bstep (se 2 (by rfl) ⟨1930209, by rfl⟩ : syracuseStep 5147225 = 3860419) B3860419
theorem B3431483 : Blo 2287435 3431483 := bstep (se 1 (by rfl) ⟨2573612, by rfl⟩ : syracuseStep 3431483 = 5147225) B5147225
theorem B2287655 : Blo 2287435 2287655 := bstep (se 1 (by rfl) ⟨1715741, by rfl⟩ : syracuseStep 2287655 = 3431483) B3431483
theorem B2573617 : Blo 2287435 2573617 := bbase (se 2 (by rfl) ⟨965106, by rfl⟩ : syracuseStep 2573617 = 1930213) (by norm_num)
theorem B3431489 : Blo 2287435 3431489 := bstep (se 2 (by rfl) ⟨1286808, by rfl⟩ : syracuseStep 3431489 = 2573617) B2573617
theorem B2287659 : Blo 2287435 2287659 := bstep (se 1 (by rfl) ⟨1715744, by rfl⟩ : syracuseStep 2287659 = 3431489) B3431489
theorem B4885861 : Blo 2287435 4885861 := bbase (se 4 (by rfl) ⟨458049, by rfl⟩ : syracuseStep 4885861 = 916099) (by norm_num)
theorem B6514481 : Blo 2287435 6514481 := bstep (se 2 (by rfl) ⟨2442930, by rfl⟩ : syracuseStep 6514481 = 4885861) B4885861
theorem B4342987 : Blo 2287435 4342987 := bstep (se 1 (by rfl) ⟨3257240, by rfl⟩ : syracuseStep 4342987 = 6514481) B6514481
theorem B5790649 : Blo 2287435 5790649 := bstep (se 2 (by rfl) ⟨2171493, by rfl⟩ : syracuseStep 5790649 = 4342987) B4342987
theorem B7720865 : Blo 2287435 7720865 := bstep (se 2 (by rfl) ⟨2895324, by rfl⟩ : syracuseStep 7720865 = 5790649) B5790649
theorem B5147243 : Blo 2287435 5147243 := bstep (se 1 (by rfl) ⟨3860432, by rfl⟩ : syracuseStep 5147243 = 7720865) B7720865
theorem B3431495 : Blo 2287435 3431495 := bstep (se 1 (by rfl) ⟨2573621, by rfl⟩ : syracuseStep 3431495 = 5147243) B5147243
theorem B2287663 : Blo 2287435 2287663 := bstep (se 1 (by rfl) ⟨1715747, by rfl⟩ : syracuseStep 2287663 = 3431495) B3431495
theorem B3431501 : Blo 2287435 3431501 := bbase (se 3 (by rfl) ⟨643406, by rfl⟩ : syracuseStep 3431501 = 1286813) (by norm_num)
theorem B2287667 : Blo 2287435 2287667 := bstep (se 1 (by rfl) ⟨1715750, by rfl⟩ : syracuseStep 2287667 = 3431501) B3431501
theorem B5147261 : Blo 2287435 5147261 := bbase (se 3 (by rfl) ⟨965111, by rfl⟩ : syracuseStep 5147261 = 1930223) (by norm_num)
theorem B3431507 : Blo 2287435 3431507 := bstep (se 1 (by rfl) ⟨2573630, by rfl⟩ : syracuseStep 3431507 = 5147261) B5147261
theorem B2287671 : Blo 2287435 2287671 := bstep (se 1 (by rfl) ⟨1715753, by rfl⟩ : syracuseStep 2287671 = 3431507) B3431507
theorem B3860453 : Blo 2287435 3860453 := bbase (se 4 (by rfl) ⟨361917, by rfl⟩ : syracuseStep 3860453 = 723835) (by norm_num)
theorem B2573635 : Blo 2287435 2573635 := bstep (se 1 (by rfl) ⟨1930226, by rfl⟩ : syracuseStep 2573635 = 3860453) B3860453
theorem B3431513 : Blo 2287435 3431513 := bstep (se 2 (by rfl) ⟨1286817, by rfl⟩ : syracuseStep 3431513 = 2573635) B2573635
theorem B2287675 : Blo 2287435 2287675 := bstep (se 1 (by rfl) ⟨1715756, by rfl⟩ : syracuseStep 2287675 = 3431513) B3431513
theorem B8244949 : Blo 2287435 8244949 := bbase (se 7 (by rfl) ⟨96620, by rfl⟩ : syracuseStep 8244949 = 193241) (by norm_num)
theorem B10993265 : Blo 2287435 10993265 := bstep (se 2 (by rfl) ⟨4122474, by rfl⟩ : syracuseStep 10993265 = 8244949) B8244949
theorem B7328843 : Blo 2287435 7328843 := bstep (se 1 (by rfl) ⟨5496632, by rfl⟩ : syracuseStep 7328843 = 10993265) B10993265
theorem B4885895 : Blo 2287435 4885895 := bstep (se 1 (by rfl) ⟨3664421, by rfl⟩ : syracuseStep 4885895 = 7328843) B7328843
theorem B3257263 : Blo 2287435 3257263 := bstep (se 1 (by rfl) ⟨2442947, by rfl⟩ : syracuseStep 3257263 = 4885895) B4885895
theorem B17372069 : Blo 2287435 17372069 := bstep (se 4 (by rfl) ⟨1628631, by rfl⟩ : syracuseStep 17372069 = 3257263) B3257263
theorem B11581379 : Blo 2287435 11581379 := bstep (se 1 (by rfl) ⟨8686034, by rfl⟩ : syracuseStep 11581379 = 17372069) B17372069
theorem B7720919 : Blo 2287435 7720919 := bstep (se 1 (by rfl) ⟨5790689, by rfl⟩ : syracuseStep 7720919 = 11581379) B11581379
theorem B5147279 : Blo 2287435 5147279 := bstep (se 1 (by rfl) ⟨3860459, by rfl⟩ : syracuseStep 5147279 = 7720919) B7720919
theorem B3431519 : Blo 2287435 3431519 := bstep (se 1 (by rfl) ⟨2573639, by rfl⟩ : syracuseStep 3431519 = 5147279) B5147279
theorem B2287679 : Blo 2287435 2287679 := bstep (se 1 (by rfl) ⟨1715759, by rfl⟩ : syracuseStep 2287679 = 3431519) B3431519
theorem B3431525 : Blo 2287435 3431525 := bbase (se 4 (by rfl) ⟨321705, by rfl⟩ : syracuseStep 3431525 = 643411) (by norm_num)
theorem B2287683 : Blo 2287435 2287683 := bstep (se 1 (by rfl) ⟨1715762, by rfl⟩ : syracuseStep 2287683 = 3431525) B3431525
theorem B5496653 : Blo 2287435 5496653 := bbase (se 3 (by rfl) ⟨1030622, by rfl⟩ : syracuseStep 5496653 = 2061245) (by norm_num)
theorem B3664435 : Blo 2287435 3664435 := bstep (se 1 (by rfl) ⟨2748326, by rfl⟩ : syracuseStep 3664435 = 5496653) B5496653
theorem B4885913 : Blo 2287435 4885913 := bstep (se 2 (by rfl) ⟨1832217, by rfl⟩ : syracuseStep 4885913 = 3664435) B3664435
theorem B3257275 : Blo 2287435 3257275 := bstep (se 1 (by rfl) ⟨2442956, by rfl⟩ : syracuseStep 3257275 = 4885913) B4885913
theorem B4343033 : Blo 2287435 4343033 := bstep (se 2 (by rfl) ⟨1628637, by rfl⟩ : syracuseStep 4343033 = 3257275) B3257275
theorem B2895355 : Blo 2287435 2895355 := bstep (se 1 (by rfl) ⟨2171516, by rfl⟩ : syracuseStep 2895355 = 4343033) B4343033
theorem B3860473 : Blo 2287435 3860473 := bstep (se 2 (by rfl) ⟨1447677, by rfl⟩ : syracuseStep 3860473 = 2895355) B2895355
theorem B5147297 : Blo 2287435 5147297 := bstep (se 2 (by rfl) ⟨1930236, by rfl⟩ : syracuseStep 5147297 = 3860473) B3860473
theorem B3431531 : Blo 2287435 3431531 := bstep (se 1 (by rfl) ⟨2573648, by rfl⟩ : syracuseStep 3431531 = 5147297) B5147297
theorem B2287687 : Blo 2287435 2287687 := bstep (se 1 (by rfl) ⟨1715765, by rfl⟩ : syracuseStep 2287687 = 3431531) B3431531
theorem B2573653 : Blo 2287435 2573653 := bbase (se 12 (by rfl) ⟨942, by rfl⟩ : syracuseStep 2573653 = 1885) (by norm_num)
theorem B3431537 : Blo 2287435 3431537 := bstep (se 2 (by rfl) ⟨1286826, by rfl⟩ : syracuseStep 3431537 = 2573653) B2573653
theorem B2287691 : Blo 2287435 2287691 := bstep (se 1 (by rfl) ⟨1715768, by rfl⟩ : syracuseStep 2287691 = 3431537) B3431537
theorem B2895365 : Blo 2287435 2895365 := bbase (se 4 (by rfl) ⟨271440, by rfl⟩ : syracuseStep 2895365 = 542881) (by norm_num)
theorem B7720973 : Blo 2287435 7720973 := bstep (se 3 (by rfl) ⟨1447682, by rfl⟩ : syracuseStep 7720973 = 2895365) B2895365
theorem B5147315 : Blo 2287435 5147315 := bstep (se 1 (by rfl) ⟨3860486, by rfl⟩ : syracuseStep 5147315 = 7720973) B7720973
theorem B3431543 : Blo 2287435 3431543 := bstep (se 1 (by rfl) ⟨2573657, by rfl⟩ : syracuseStep 3431543 = 5147315) B5147315
theorem B2287695 : Blo 2287435 2287695 := bstep (se 1 (by rfl) ⟨1715771, by rfl⟩ : syracuseStep 2287695 = 3431543) B3431543
theorem B3431549 : Blo 2287435 3431549 := bbase (se 3 (by rfl) ⟨643415, by rfl⟩ : syracuseStep 3431549 = 1286831) (by norm_num)
theorem B2287699 : Blo 2287435 2287699 := bstep (se 1 (by rfl) ⟨1715774, by rfl⟩ : syracuseStep 2287699 = 3431549) B3431549
theorem B5147333 : Blo 2287435 5147333 := bbase (se 4 (by rfl) ⟨482562, by rfl⟩ : syracuseStep 5147333 = 965125) (by norm_num)
theorem B3431555 : Blo 2287435 3431555 := bstep (se 1 (by rfl) ⟨2573666, by rfl⟩ : syracuseStep 3431555 = 5147333) B5147333
theorem B2287703 : Blo 2287435 2287703 := bstep (se 1 (by rfl) ⟨1715777, by rfl⟩ : syracuseStep 2287703 = 3431555) B3431555
theorem B16490101 : Blo 2287435 16490101 := bbase (se 5 (by rfl) ⟨772973, by rfl⟩ : syracuseStep 16490101 = 1545947) (by norm_num)
theorem B21986801 : Blo 2287435 21986801 := bstep (se 2 (by rfl) ⟨8245050, by rfl⟩ : syracuseStep 21986801 = 16490101) B16490101
theorem B14657867 : Blo 2287435 14657867 := bstep (se 1 (by rfl) ⟨10993400, by rfl⟩ : syracuseStep 14657867 = 21986801) B21986801
theorem B9771911 : Blo 2287435 9771911 := bstep (se 1 (by rfl) ⟨7328933, by rfl⟩ : syracuseStep 9771911 = 14657867) B14657867
theorem B6514607 : Blo 2287435 6514607 := bstep (se 1 (by rfl) ⟨4885955, by rfl⟩ : syracuseStep 6514607 = 9771911) B9771911
theorem B4343071 : Blo 2287435 4343071 := bstep (se 1 (by rfl) ⟨3257303, by rfl⟩ : syracuseStep 4343071 = 6514607) B6514607
theorem B5790761 : Blo 2287435 5790761 := bstep (se 2 (by rfl) ⟨2171535, by rfl⟩ : syracuseStep 5790761 = 4343071) B4343071
theorem B3860507 : Blo 2287435 3860507 := bstep (se 1 (by rfl) ⟨2895380, by rfl⟩ : syracuseStep 3860507 = 5790761) B5790761
theorem B2573671 : Blo 2287435 2573671 := bstep (se 1 (by rfl) ⟨1930253, by rfl⟩ : syracuseStep 2573671 = 3860507) B3860507
theorem B3431561 : Blo 2287435 3431561 := bstep (se 2 (by rfl) ⟨1286835, by rfl⟩ : syracuseStep 3431561 = 2573671) B2573671
theorem B2287707 : Blo 2287435 2287707 := bstep (se 1 (by rfl) ⟨1715780, by rfl⟩ : syracuseStep 2287707 = 3431561) B3431561
theorem B11581541 : Blo 2287435 11581541 := bbase (se 4 (by rfl) ⟨1085769, by rfl⟩ : syracuseStep 11581541 = 2171539) (by norm_num)
theorem B7721027 : Blo 2287435 7721027 := bstep (se 1 (by rfl) ⟨5790770, by rfl⟩ : syracuseStep 7721027 = 11581541) B11581541
theorem B5147351 : Blo 2287435 5147351 := bstep (se 1 (by rfl) ⟨3860513, by rfl⟩ : syracuseStep 5147351 = 7721027) B7721027
theorem B3431567 : Blo 2287435 3431567 := bstep (se 1 (by rfl) ⟨2573675, by rfl⟩ : syracuseStep 3431567 = 5147351) B5147351
theorem B2287711 : Blo 2287435 2287711 := bstep (se 1 (by rfl) ⟨1715783, by rfl⟩ : syracuseStep 2287711 = 3431567) B3431567
theorem B3431573 : Blo 2287435 3431573 := bbase (se 6 (by rfl) ⟨80427, by rfl⟩ : syracuseStep 3431573 = 160855) (by norm_num)
theorem B2287715 : Blo 2287435 2287715 := bstep (se 1 (by rfl) ⟨1715786, by rfl⟩ : syracuseStep 2287715 = 3431573) B3431573
theorem B8245093 : Blo 2287435 8245093 := bbase (se 4 (by rfl) ⟨772977, by rfl⟩ : syracuseStep 8245093 = 1545955) (by norm_num)
theorem B10993457 : Blo 2287435 10993457 := bstep (se 2 (by rfl) ⟨4122546, by rfl⟩ : syracuseStep 10993457 = 8245093) B8245093
theorem B7328971 : Blo 2287435 7328971 := bstep (se 1 (by rfl) ⟨5496728, by rfl⟩ : syracuseStep 7328971 = 10993457) B10993457
theorem B9771961 : Blo 2287435 9771961 := bstep (se 2 (by rfl) ⟨3664485, by rfl⟩ : syracuseStep 9771961 = 7328971) B7328971
theorem B13029281 : Blo 2287435 13029281 := bstep (se 2 (by rfl) ⟨4885980, by rfl⟩ : syracuseStep 13029281 = 9771961) B9771961
theorem B8686187 : Blo 2287435 8686187 := bstep (se 1 (by rfl) ⟨6514640, by rfl⟩ : syracuseStep 8686187 = 13029281) B13029281
theorem B5790791 : Blo 2287435 5790791 := bstep (se 1 (by rfl) ⟨4343093, by rfl⟩ : syracuseStep 5790791 = 8686187) B8686187
theorem B3860527 : Blo 2287435 3860527 := bstep (se 1 (by rfl) ⟨2895395, by rfl⟩ : syracuseStep 3860527 = 5790791) B5790791
theorem B5147369 : Blo 2287435 5147369 := bstep (se 2 (by rfl) ⟨1930263, by rfl⟩ : syracuseStep 5147369 = 3860527) B3860527
theorem B3431579 : Blo 2287435 3431579 := bstep (se 1 (by rfl) ⟨2573684, by rfl⟩ : syracuseStep 3431579 = 5147369) B5147369
theorem B2287719 : Blo 2287435 2287719 := bstep (se 1 (by rfl) ⟨1715789, by rfl⟩ : syracuseStep 2287719 = 3431579) B3431579
theorem B2573689 : Blo 2287435 2573689 := bbase (se 2 (by rfl) ⟨965133, by rfl⟩ : syracuseStep 2573689 = 1930267) (by norm_num)
theorem B3431585 : Blo 2287435 3431585 := bstep (se 2 (by rfl) ⟨1286844, by rfl⟩ : syracuseStep 3431585 = 2573689) B2573689
theorem B2287723 : Blo 2287435 2287723 := bstep (se 1 (by rfl) ⟨1715792, by rfl⟩ : syracuseStep 2287723 = 3431585) B3431585
theorem B3913213 : Blo 2287435 3913213 := bbase (se 3 (by rfl) ⟨733727, by rfl⟩ : syracuseStep 3913213 = 1467455) (by norm_num)
theorem B5217617 : Blo 2287435 5217617 := bstep (se 2 (by rfl) ⟨1956606, by rfl⟩ : syracuseStep 5217617 = 3913213) B3913213
theorem B3478411 : Blo 2287435 3478411 := bstep (se 1 (by rfl) ⟨2608808, by rfl⟩ : syracuseStep 3478411 = 5217617) B5217617
theorem B4637881 : Blo 2287435 4637881 := bstep (se 2 (by rfl) ⟨1739205, by rfl⟩ : syracuseStep 4637881 = 3478411) B3478411
theorem B24735365 : Blo 2287435 24735365 := bstep (se 4 (by rfl) ⟨2318940, by rfl⟩ : syracuseStep 24735365 = 4637881) B4637881
theorem B16490243 : Blo 2287435 16490243 := bstep (se 1 (by rfl) ⟨12367682, by rfl⟩ : syracuseStep 16490243 = 24735365) B24735365
theorem B10993495 : Blo 2287435 10993495 := bstep (se 1 (by rfl) ⟨8245121, by rfl⟩ : syracuseStep 10993495 = 16490243) B16490243
theorem B14657993 : Blo 2287435 14657993 := bstep (se 2 (by rfl) ⟨5496747, by rfl⟩ : syracuseStep 14657993 = 10993495) B10993495
theorem B9771995 : Blo 2287435 9771995 := bstep (se 1 (by rfl) ⟨7328996, by rfl⟩ : syracuseStep 9771995 = 14657993) B14657993
theorem B6514663 : Blo 2287435 6514663 := bstep (se 1 (by rfl) ⟨4885997, by rfl⟩ : syracuseStep 6514663 = 9771995) B9771995
theorem B8686217 : Blo 2287435 8686217 := bstep (se 2 (by rfl) ⟨3257331, by rfl⟩ : syracuseStep 8686217 = 6514663) B6514663
theorem B5790811 : Blo 2287435 5790811 := bstep (se 1 (by rfl) ⟨4343108, by rfl⟩ : syracuseStep 5790811 = 8686217) B8686217
theorem B7721081 : Blo 2287435 7721081 := bstep (se 2 (by rfl) ⟨2895405, by rfl⟩ : syracuseStep 7721081 = 5790811) B5790811
theorem B5147387 : Blo 2287435 5147387 := bstep (se 1 (by rfl) ⟨3860540, by rfl⟩ : syracuseStep 5147387 = 7721081) B7721081
theorem B3431591 : Blo 2287435 3431591 := bstep (se 1 (by rfl) ⟨2573693, by rfl⟩ : syracuseStep 3431591 = 5147387) B5147387
theorem B2287727 : Blo 2287435 2287727 := bstep (se 1 (by rfl) ⟨1715795, by rfl⟩ : syracuseStep 2287727 = 3431591) B3431591
theorem B3431597 : Blo 2287435 3431597 := bbase (se 3 (by rfl) ⟨643424, by rfl⟩ : syracuseStep 3431597 = 1286849) (by norm_num)
theorem B2287731 : Blo 2287435 2287731 := bstep (se 1 (by rfl) ⟨1715798, by rfl⟩ : syracuseStep 2287731 = 3431597) B3431597
theorem B5147405 : Blo 2287435 5147405 := bbase (se 3 (by rfl) ⟨965138, by rfl⟩ : syracuseStep 5147405 = 1930277) (by norm_num)
theorem B3431603 : Blo 2287435 3431603 := bstep (se 1 (by rfl) ⟨2573702, by rfl⟩ : syracuseStep 3431603 = 5147405) B5147405
theorem B2287735 : Blo 2287435 2287735 := bstep (se 1 (by rfl) ⟨1715801, by rfl⟩ : syracuseStep 2287735 = 3431603) B3431603
theorem B2895421 : Blo 2287435 2895421 := bbase (se 3 (by rfl) ⟨542891, by rfl⟩ : syracuseStep 2895421 = 1085783) (by norm_num)
theorem B3860561 : Blo 2287435 3860561 := bstep (se 2 (by rfl) ⟨1447710, by rfl⟩ : syracuseStep 3860561 = 2895421) B2895421
theorem B2573707 : Blo 2287435 2573707 := bstep (se 1 (by rfl) ⟨1930280, by rfl⟩ : syracuseStep 2573707 = 3860561) B3860561
theorem B3431609 : Blo 2287435 3431609 := bstep (se 2 (by rfl) ⟨1286853, by rfl⟩ : syracuseStep 3431609 = 2573707) B2573707
theorem B2287739 : Blo 2287435 2287739 := bstep (se 1 (by rfl) ⟨1715804, by rfl⟩ : syracuseStep 2287739 = 3431609) B3431609
theorem B16490357 : Blo 2287435 16490357 := bbase (se 5 (by rfl) ⟨772985, by rfl⟩ : syracuseStep 16490357 = 1545971) (by norm_num)
theorem B10993571 : Blo 2287435 10993571 := bstep (se 1 (by rfl) ⟨8245178, by rfl⟩ : syracuseStep 10993571 = 16490357) B16490357
theorem B7329047 : Blo 2287435 7329047 := bstep (se 1 (by rfl) ⟨5496785, by rfl⟩ : syracuseStep 7329047 = 10993571) B10993571
theorem B19544125 : Blo 2287435 19544125 := bstep (se 3 (by rfl) ⟨3664523, by rfl⟩ : syracuseStep 19544125 = 7329047) B7329047
theorem B26058833 : Blo 2287435 26058833 := bstep (se 2 (by rfl) ⟨9772062, by rfl⟩ : syracuseStep 26058833 = 19544125) B19544125
theorem B17372555 : Blo 2287435 17372555 := bstep (se 1 (by rfl) ⟨13029416, by rfl⟩ : syracuseStep 17372555 = 26058833) B26058833
theorem B11581703 : Blo 2287435 11581703 := bstep (se 1 (by rfl) ⟨8686277, by rfl⟩ : syracuseStep 11581703 = 17372555) B17372555
theorem B7721135 : Blo 2287435 7721135 := bstep (se 1 (by rfl) ⟨5790851, by rfl⟩ : syracuseStep 7721135 = 11581703) B11581703
theorem B5147423 : Blo 2287435 5147423 := bstep (se 1 (by rfl) ⟨3860567, by rfl⟩ : syracuseStep 5147423 = 7721135) B7721135
theorem B3431615 : Blo 2287435 3431615 := bstep (se 1 (by rfl) ⟨2573711, by rfl⟩ : syracuseStep 3431615 = 5147423) B5147423
theorem B2287743 : Blo 2287435 2287743 := bstep (se 1 (by rfl) ⟨1715807, by rfl⟩ : syracuseStep 2287743 = 3431615) B3431615
theorem B3431621 : Blo 2287435 3431621 := bbase (se 4 (by rfl) ⟨321714, by rfl⟩ : syracuseStep 3431621 = 643429) (by norm_num)
theorem B2287747 : Blo 2287435 2287747 := bstep (se 1 (by rfl) ⟨1715810, by rfl⟩ : syracuseStep 2287747 = 3431621) B3431621
theorem B3860581 : Blo 2287435 3860581 := bbase (se 4 (by rfl) ⟨361929, by rfl⟩ : syracuseStep 3860581 = 723859) (by norm_num)
theorem B5147441 : Blo 2287435 5147441 := bstep (se 2 (by rfl) ⟨1930290, by rfl⟩ : syracuseStep 5147441 = 3860581) B3860581
theorem B3431627 : Blo 2287435 3431627 := bstep (se 1 (by rfl) ⟨2573720, by rfl⟩ : syracuseStep 3431627 = 5147441) B5147441
theorem B2287751 : Blo 2287435 2287751 := bstep (se 1 (by rfl) ⟨1715813, by rfl⟩ : syracuseStep 2287751 = 3431627) B3431627
theorem B2573725 : Blo 2287435 2573725 := bbase (se 3 (by rfl) ⟨482573, by rfl⟩ : syracuseStep 2573725 = 965147) (by norm_num)
theorem B3431633 : Blo 2287435 3431633 := bstep (se 2 (by rfl) ⟨1286862, by rfl⟩ : syracuseStep 3431633 = 2573725) B2573725
theorem B2287755 : Blo 2287435 2287755 := bstep (se 1 (by rfl) ⟨1715816, by rfl⟩ : syracuseStep 2287755 = 3431633) B3431633
theorem B7721189 : Blo 2287435 7721189 := bbase (se 4 (by rfl) ⟨723861, by rfl⟩ : syracuseStep 7721189 = 1447723) (by norm_num)
theorem B5147459 : Blo 2287435 5147459 := bstep (se 1 (by rfl) ⟨3860594, by rfl⟩ : syracuseStep 5147459 = 7721189) B7721189
theorem B3431639 : Blo 2287435 3431639 := bstep (se 1 (by rfl) ⟨2573729, by rfl⟩ : syracuseStep 3431639 = 5147459) B5147459
theorem B2287759 : Blo 2287435 2287759 := bstep (se 1 (by rfl) ⟨1715819, by rfl⟩ : syracuseStep 2287759 = 3431639) B3431639
theorem B3431645 : Blo 2287435 3431645 := bbase (se 3 (by rfl) ⟨643433, by rfl⟩ : syracuseStep 3431645 = 1286867) (by norm_num)
theorem B2287763 : Blo 2287435 2287763 := bstep (se 1 (by rfl) ⟨1715822, by rfl⟩ : syracuseStep 2287763 = 3431645) B3431645
theorem B5147477 : Blo 2287435 5147477 := bbase (se 9 (by rfl) ⟨15080, by rfl⟩ : syracuseStep 5147477 = 30161) (by norm_num)
theorem B3431651 : Blo 2287435 3431651 := bstep (se 1 (by rfl) ⟨2573738, by rfl⟩ : syracuseStep 3431651 = 5147477) B5147477
theorem B2287767 : Blo 2287435 2287767 := bstep (se 1 (by rfl) ⟨1715825, by rfl⟩ : syracuseStep 2287767 = 3431651) B3431651
theorem B6514789 : Blo 2287435 6514789 := bbase (se 4 (by rfl) ⟨610761, by rfl⟩ : syracuseStep 6514789 = 1221523) (by norm_num)
theorem B8686385 : Blo 2287435 8686385 := bstep (se 2 (by rfl) ⟨3257394, by rfl⟩ : syracuseStep 8686385 = 6514789) B6514789
theorem B5790923 : Blo 2287435 5790923 := bstep (se 1 (by rfl) ⟨4343192, by rfl⟩ : syracuseStep 5790923 = 8686385) B8686385
theorem B3860615 : Blo 2287435 3860615 := bstep (se 1 (by rfl) ⟨2895461, by rfl⟩ : syracuseStep 3860615 = 5790923) B5790923
theorem B2573743 : Blo 2287435 2573743 := bstep (se 1 (by rfl) ⟨1930307, by rfl⟩ : syracuseStep 2573743 = 3860615) B3860615
theorem B3431657 : Blo 2287435 3431657 := bstep (se 2 (by rfl) ⟨1286871, by rfl⟩ : syracuseStep 3431657 = 2573743) B2573743
theorem B2287771 : Blo 2287435 2287771 := bstep (se 1 (by rfl) ⟨1715828, by rfl⟩ : syracuseStep 2287771 = 3431657) B3431657
theorem B6693781 : Blo 2287435 6693781 := bbase (se 6 (by rfl) ⟨156885, by rfl⟩ : syracuseStep 6693781 = 313771) (by norm_num)
theorem B8925041 : Blo 2287435 8925041 := bstep (se 2 (by rfl) ⟨3346890, by rfl⟩ : syracuseStep 8925041 = 6693781) B6693781
theorem B5950027 : Blo 2287435 5950027 := bstep (se 1 (by rfl) ⟨4462520, by rfl⟩ : syracuseStep 5950027 = 8925041) B8925041
theorem B7933369 : Blo 2287435 7933369 := bstep (se 2 (by rfl) ⟨2975013, by rfl⟩ : syracuseStep 7933369 = 5950027) B5950027
theorem B10577825 : Blo 2287435 10577825 := bstep (se 2 (by rfl) ⟨3966684, by rfl⟩ : syracuseStep 10577825 = 7933369) B7933369
theorem B7051883 : Blo 2287435 7051883 := bstep (se 1 (by rfl) ⟨5288912, by rfl⟩ : syracuseStep 7051883 = 10577825) B10577825
theorem B75220085 : Blo 2287435 75220085 := bstep (se 5 (by rfl) ⟨3525941, by rfl⟩ : syracuseStep 75220085 = 7051883) B7051883
theorem B50146723 : Blo 2287435 50146723 := bstep (se 1 (by rfl) ⟨37610042, by rfl⟩ : syracuseStep 50146723 = 75220085) B75220085
theorem B66862297 : Blo 2287435 66862297 := bstep (se 2 (by rfl) ⟨25073361, by rfl⟩ : syracuseStep 66862297 = 50146723) B50146723
theorem B89149729 : Blo 2287435 89149729 := bstep (se 2 (by rfl) ⟨33431148, by rfl⟩ : syracuseStep 89149729 = 66862297) B66862297
theorem B118866305 : Blo 2287435 118866305 := bstep (se 2 (by rfl) ⟨44574864, by rfl⟩ : syracuseStep 118866305 = 89149729) B89149729
theorem B79244203 : Blo 2287435 79244203 := bstep (se 1 (by rfl) ⟨59433152, by rfl⟩ : syracuseStep 79244203 = 118866305) B118866305
theorem B105658937 : Blo 2287435 105658937 := bstep (se 2 (by rfl) ⟨39622101, by rfl⟩ : syracuseStep 105658937 = 79244203) B79244203
theorem B70439291 : Blo 2287435 70439291 := bstep (se 1 (by rfl) ⟨52829468, by rfl⟩ : syracuseStep 70439291 = 105658937) B105658937
theorem B46959527 : Blo 2287435 46959527 := bstep (se 1 (by rfl) ⟨35219645, by rfl⟩ : syracuseStep 46959527 = 70439291) B70439291
theorem B31306351 : Blo 2287435 31306351 := bstep (se 1 (by rfl) ⟨23479763, by rfl⟩ : syracuseStep 31306351 = 46959527) B46959527
theorem B41741801 : Blo 2287435 41741801 := bstep (se 2 (by rfl) ⟨15653175, by rfl⟩ : syracuseStep 41741801 = 31306351) B31306351
theorem B27827867 : Blo 2287435 27827867 := bstep (se 1 (by rfl) ⟨20870900, by rfl⟩ : syracuseStep 27827867 = 41741801) B41741801
theorem B18551911 : Blo 2287435 18551911 := bstep (se 1 (by rfl) ⟨13913933, by rfl⟩ : syracuseStep 18551911 = 27827867) B27827867
theorem B24735881 : Blo 2287435 24735881 := bstep (se 2 (by rfl) ⟨9275955, by rfl⟩ : syracuseStep 24735881 = 18551911) B18551911
theorem B65962349 : Blo 2287435 65962349 := bstep (se 3 (by rfl) ⟨12367940, by rfl⟩ : syracuseStep 65962349 = 24735881) B24735881
theorem B43974899 : Blo 2287435 43974899 := bstep (se 1 (by rfl) ⟨32981174, by rfl⟩ : syracuseStep 43974899 = 65962349) B65962349
theorem B29316599 : Blo 2287435 29316599 := bstep (se 1 (by rfl) ⟨21987449, by rfl⟩ : syracuseStep 29316599 = 43974899) B43974899
theorem B19544399 : Blo 2287435 19544399 := bstep (se 1 (by rfl) ⟨14658299, by rfl⟩ : syracuseStep 19544399 = 29316599) B29316599
theorem B13029599 : Blo 2287435 13029599 := bstep (se 1 (by rfl) ⟨9772199, by rfl⟩ : syracuseStep 13029599 = 19544399) B19544399
theorem B8686399 : Blo 2287435 8686399 := bstep (se 1 (by rfl) ⟨6514799, by rfl⟩ : syracuseStep 8686399 = 13029599) B13029599
theorem B11581865 : Blo 2287435 11581865 := bstep (se 2 (by rfl) ⟨4343199, by rfl⟩ : syracuseStep 11581865 = 8686399) B8686399
theorem B7721243 : Blo 2287435 7721243 := bstep (se 1 (by rfl) ⟨5790932, by rfl⟩ : syracuseStep 7721243 = 11581865) B11581865
theorem B5147495 : Blo 2287435 5147495 := bstep (se 1 (by rfl) ⟨3860621, by rfl⟩ : syracuseStep 5147495 = 7721243) B7721243
theorem B3431663 : Blo 2287435 3431663 := bstep (se 1 (by rfl) ⟨2573747, by rfl⟩ : syracuseStep 3431663 = 5147495) B5147495
theorem B2287775 : Blo 2287435 2287775 := bstep (se 1 (by rfl) ⟨1715831, by rfl⟩ : syracuseStep 2287775 = 3431663) B3431663
theorem B3431669 : Blo 2287435 3431669 := bbase (se 5 (by rfl) ⟨160859, by rfl⟩ : syracuseStep 3431669 = 321719) (by norm_num)
theorem B2287779 : Blo 2287435 2287779 := bstep (se 1 (by rfl) ⟨1715834, by rfl⟩ : syracuseStep 2287779 = 3431669) B3431669
theorem B10993765 : Blo 2287435 10993765 := bbase (se 4 (by rfl) ⟨1030665, by rfl⟩ : syracuseStep 10993765 = 2061331) (by norm_num)
theorem B14658353 : Blo 2287435 14658353 := bstep (se 2 (by rfl) ⟨5496882, by rfl⟩ : syracuseStep 14658353 = 10993765) B10993765
theorem B9772235 : Blo 2287435 9772235 := bstep (se 1 (by rfl) ⟨7329176, by rfl⟩ : syracuseStep 9772235 = 14658353) B14658353
theorem B6514823 : Blo 2287435 6514823 := bstep (se 1 (by rfl) ⟨4886117, by rfl⟩ : syracuseStep 6514823 = 9772235) B9772235
theorem B4343215 : Blo 2287435 4343215 := bstep (se 1 (by rfl) ⟨3257411, by rfl⟩ : syracuseStep 4343215 = 6514823) B6514823
theorem B5790953 : Blo 2287435 5790953 := bstep (se 2 (by rfl) ⟨2171607, by rfl⟩ : syracuseStep 5790953 = 4343215) B4343215
theorem B3860635 : Blo 2287435 3860635 := bstep (se 1 (by rfl) ⟨2895476, by rfl⟩ : syracuseStep 3860635 = 5790953) B5790953
theorem B5147513 : Blo 2287435 5147513 := bstep (se 2 (by rfl) ⟨1930317, by rfl⟩ : syracuseStep 5147513 = 3860635) B3860635
theorem B3431675 : Blo 2287435 3431675 := bstep (se 1 (by rfl) ⟨2573756, by rfl⟩ : syracuseStep 3431675 = 5147513) B5147513
theorem B2287783 : Blo 2287435 2287783 := bstep (se 1 (by rfl) ⟨1715837, by rfl⟩ : syracuseStep 2287783 = 3431675) B3431675
theorem B2573761 : Blo 2287435 2573761 := bbase (se 2 (by rfl) ⟨965160, by rfl⟩ : syracuseStep 2573761 = 1930321) (by norm_num)
theorem B3431681 : Blo 2287435 3431681 := bstep (se 2 (by rfl) ⟨1286880, by rfl⟩ : syracuseStep 3431681 = 2573761) B2573761
theorem B2287787 : Blo 2287435 2287787 := bstep (se 1 (by rfl) ⟨1715840, by rfl⟩ : syracuseStep 2287787 = 3431681) B3431681
theorem B5790973 : Blo 2287435 5790973 := bbase (se 3 (by rfl) ⟨1085807, by rfl⟩ : syracuseStep 5790973 = 2171615) (by norm_num)
theorem B7721297 : Blo 2287435 7721297 := bstep (se 2 (by rfl) ⟨2895486, by rfl⟩ : syracuseStep 7721297 = 5790973) B5790973
theorem B5147531 : Blo 2287435 5147531 := bstep (se 1 (by rfl) ⟨3860648, by rfl⟩ : syracuseStep 5147531 = 7721297) B7721297
theorem B3431687 : Blo 2287435 3431687 := bstep (se 1 (by rfl) ⟨2573765, by rfl⟩ : syracuseStep 3431687 = 5147531) B5147531
theorem B2287791 : Blo 2287435 2287791 := bstep (se 1 (by rfl) ⟨1715843, by rfl⟩ : syracuseStep 2287791 = 3431687) B3431687
theorem B3431693 : Blo 2287435 3431693 := bbase (se 3 (by rfl) ⟨643442, by rfl⟩ : syracuseStep 3431693 = 1286885) (by norm_num)
theorem B2287795 : Blo 2287435 2287795 := bstep (se 1 (by rfl) ⟨1715846, by rfl⟩ : syracuseStep 2287795 = 3431693) B3431693
theorem B5147549 : Blo 2287435 5147549 := bbase (se 3 (by rfl) ⟨965165, by rfl⟩ : syracuseStep 5147549 = 1930331) (by norm_num)
theorem B3431699 : Blo 2287435 3431699 := bstep (se 1 (by rfl) ⟨2573774, by rfl⟩ : syracuseStep 3431699 = 5147549) B5147549
theorem B2287799 : Blo 2287435 2287799 := bstep (se 1 (by rfl) ⟨1715849, by rfl⟩ : syracuseStep 2287799 = 3431699) B3431699
theorem B3860669 : Blo 2287435 3860669 := bbase (se 3 (by rfl) ⟨723875, by rfl⟩ : syracuseStep 3860669 = 1447751) (by norm_num)
theorem B2573779 : Blo 2287435 2573779 := bstep (se 1 (by rfl) ⟨1930334, by rfl⟩ : syracuseStep 2573779 = 3860669) B3860669
theorem B3431705 : Blo 2287435 3431705 := bstep (se 2 (by rfl) ⟨1286889, by rfl⟩ : syracuseStep 3431705 = 2573779) B2573779
theorem B2287803 : Blo 2287435 2287803 := bstep (se 1 (by rfl) ⟨1715852, by rfl⟩ : syracuseStep 2287803 = 3431705) B3431705
theorem B13029781 : Blo 2287435 13029781 := bbase (se 6 (by rfl) ⟨305385, by rfl⟩ : syracuseStep 13029781 = 610771) (by norm_num)
theorem B17373041 : Blo 2287435 17373041 := bstep (se 2 (by rfl) ⟨6514890, by rfl⟩ : syracuseStep 17373041 = 13029781) B13029781
theorem B11582027 : Blo 2287435 11582027 := bstep (se 1 (by rfl) ⟨8686520, by rfl⟩ : syracuseStep 11582027 = 17373041) B17373041
theorem B7721351 : Blo 2287435 7721351 := bstep (se 1 (by rfl) ⟨5791013, by rfl⟩ : syracuseStep 7721351 = 11582027) B11582027
theorem B5147567 : Blo 2287435 5147567 := bstep (se 1 (by rfl) ⟨3860675, by rfl⟩ : syracuseStep 5147567 = 7721351) B7721351
theorem B3431711 : Blo 2287435 3431711 := bstep (se 1 (by rfl) ⟨2573783, by rfl⟩ : syracuseStep 3431711 = 5147567) B5147567
theorem B2287807 : Blo 2287435 2287807 := bstep (se 1 (by rfl) ⟨1715855, by rfl⟩ : syracuseStep 2287807 = 3431711) B3431711
theorem B3431717 : Blo 2287435 3431717 := bbase (se 4 (by rfl) ⟨321723, by rfl⟩ : syracuseStep 3431717 = 643447) (by norm_num)
theorem B2287811 : Blo 2287435 2287811 := bstep (se 1 (by rfl) ⟨1715858, by rfl⟩ : syracuseStep 2287811 = 3431717) B3431717
theorem B2895517 : Blo 2287435 2895517 := bbase (se 3 (by rfl) ⟨542909, by rfl⟩ : syracuseStep 2895517 = 1085819) (by norm_num)
theorem B3860689 : Blo 2287435 3860689 := bstep (se 2 (by rfl) ⟨1447758, by rfl⟩ : syracuseStep 3860689 = 2895517) B2895517
theorem B5147585 : Blo 2287435 5147585 := bstep (se 2 (by rfl) ⟨1930344, by rfl⟩ : syracuseStep 5147585 = 3860689) B3860689
theorem B3431723 : Blo 2287435 3431723 := bstep (se 1 (by rfl) ⟨2573792, by rfl⟩ : syracuseStep 3431723 = 5147585) B5147585
theorem B2287815 : Blo 2287435 2287815 := bstep (se 1 (by rfl) ⟨1715861, by rfl⟩ : syracuseStep 2287815 = 3431723) B3431723
theorem B2573797 : Blo 2287435 2573797 := bbase (se 4 (by rfl) ⟨241293, by rfl⟩ : syracuseStep 2573797 = 482587) (by norm_num)
theorem B3431729 : Blo 2287435 3431729 := bstep (se 2 (by rfl) ⟨1286898, by rfl⟩ : syracuseStep 3431729 = 2573797) B2573797
theorem B2287819 : Blo 2287435 2287819 := bstep (se 1 (by rfl) ⟨1715864, by rfl⟩ : syracuseStep 2287819 = 3431729) B3431729
theorem B4638077 : Blo 2287435 4638077 := bbase (se 3 (by rfl) ⟨869639, by rfl⟩ : syracuseStep 4638077 = 1739279) (by norm_num)
theorem B3092051 : Blo 2287435 3092051 := bstep (se 1 (by rfl) ⟨2319038, by rfl⟩ : syracuseStep 3092051 = 4638077) B4638077
theorem B8245469 : Blo 2287435 8245469 := bstep (se 3 (by rfl) ⟨1546025, by rfl⟩ : syracuseStep 8245469 = 3092051) B3092051
theorem B5496979 : Blo 2287435 5496979 := bstep (se 1 (by rfl) ⟨4122734, by rfl⟩ : syracuseStep 5496979 = 8245469) B8245469
theorem B7329305 : Blo 2287435 7329305 := bstep (se 2 (by rfl) ⟨2748489, by rfl⟩ : syracuseStep 7329305 = 5496979) B5496979
theorem B4886203 : Blo 2287435 4886203 := bstep (se 1 (by rfl) ⟨3664652, by rfl⟩ : syracuseStep 4886203 = 7329305) B7329305
theorem B6514937 : Blo 2287435 6514937 := bstep (se 2 (by rfl) ⟨2443101, by rfl⟩ : syracuseStep 6514937 = 4886203) B4886203
theorem B4343291 : Blo 2287435 4343291 := bstep (se 1 (by rfl) ⟨3257468, by rfl⟩ : syracuseStep 4343291 = 6514937) B6514937
theorem B2895527 : Blo 2287435 2895527 := bstep (se 1 (by rfl) ⟨2171645, by rfl⟩ : syracuseStep 2895527 = 4343291) B4343291
theorem B7721405 : Blo 2287435 7721405 := bstep (se 3 (by rfl) ⟨1447763, by rfl⟩ : syracuseStep 7721405 = 2895527) B2895527
theorem B5147603 : Blo 2287435 5147603 := bstep (se 1 (by rfl) ⟨3860702, by rfl⟩ : syracuseStep 5147603 = 7721405) B7721405
theorem B3431735 : Blo 2287435 3431735 := bstep (se 1 (by rfl) ⟨2573801, by rfl⟩ : syracuseStep 3431735 = 5147603) B5147603
theorem B2287823 : Blo 2287435 2287823 := bstep (se 1 (by rfl) ⟨1715867, by rfl⟩ : syracuseStep 2287823 = 3431735) B3431735
theorem B3431741 : Blo 2287435 3431741 := bbase (se 3 (by rfl) ⟨643451, by rfl⟩ : syracuseStep 3431741 = 1286903) (by norm_num)
theorem B2287827 : Blo 2287435 2287827 := bstep (se 1 (by rfl) ⟨1715870, by rfl⟩ : syracuseStep 2287827 = 3431741) B3431741
theorem B5147621 : Blo 2287435 5147621 := bbase (se 4 (by rfl) ⟨482589, by rfl⟩ : syracuseStep 5147621 = 965179) (by norm_num)
theorem B3431747 : Blo 2287435 3431747 := bstep (se 1 (by rfl) ⟨2573810, by rfl⟩ : syracuseStep 3431747 = 5147621) B5147621
theorem B2287831 : Blo 2287435 2287831 := bstep (se 1 (by rfl) ⟨1715873, by rfl⟩ : syracuseStep 2287831 = 3431747) B3431747
theorem B5791085 : Blo 2287435 5791085 := bbase (se 3 (by rfl) ⟨1085828, by rfl⟩ : syracuseStep 5791085 = 2171657) (by norm_num)
theorem B3860723 : Blo 2287435 3860723 := bstep (se 1 (by rfl) ⟨2895542, by rfl⟩ : syracuseStep 3860723 = 5791085) B5791085
theorem B2573815 : Blo 2287435 2573815 := bstep (se 1 (by rfl) ⟨1930361, by rfl⟩ : syracuseStep 2573815 = 3860723) B3860723
theorem B3431753 : Blo 2287435 3431753 := bstep (se 2 (by rfl) ⟨1286907, by rfl⟩ : syracuseStep 3431753 = 2573815) B2573815
theorem B2287835 : Blo 2287435 2287835 := bstep (se 1 (by rfl) ⟨1715876, by rfl⟩ : syracuseStep 2287835 = 3431753) B3431753
theorem B4886237 : Blo 2287435 4886237 := bbase (se 3 (by rfl) ⟨916169, by rfl⟩ : syracuseStep 4886237 = 1832339) (by norm_num)
theorem B3257491 : Blo 2287435 3257491 := bstep (se 1 (by rfl) ⟨2443118, by rfl⟩ : syracuseStep 3257491 = 4886237) B4886237
theorem B4343321 : Blo 2287435 4343321 := bstep (se 2 (by rfl) ⟨1628745, by rfl⟩ : syracuseStep 4343321 = 3257491) B3257491
theorem B11582189 : Blo 2287435 11582189 := bstep (se 3 (by rfl) ⟨2171660, by rfl⟩ : syracuseStep 11582189 = 4343321) B4343321
theorem B7721459 : Blo 2287435 7721459 := bstep (se 1 (by rfl) ⟨5791094, by rfl⟩ : syracuseStep 7721459 = 11582189) B11582189
theorem B5147639 : Blo 2287435 5147639 := bstep (se 1 (by rfl) ⟨3860729, by rfl⟩ : syracuseStep 5147639 = 7721459) B7721459
theorem B3431759 : Blo 2287435 3431759 := bstep (se 1 (by rfl) ⟨2573819, by rfl⟩ : syracuseStep 3431759 = 5147639) B5147639
theorem B2287839 : Blo 2287435 2287839 := bstep (se 1 (by rfl) ⟨1715879, by rfl⟩ : syracuseStep 2287839 = 3431759) B3431759
theorem B3431765 : Blo 2287435 3431765 := bbase (se 11 (by rfl) ⟨2513, by rfl⟩ : syracuseStep 3431765 = 5027) (by norm_num)
theorem B2287843 : Blo 2287435 2287843 := bstep (se 1 (by rfl) ⟨1715882, by rfl⟩ : syracuseStep 2287843 = 3431765) B3431765
theorem B5497037 : Blo 2287435 5497037 := bbase (se 3 (by rfl) ⟨1030694, by rfl⟩ : syracuseStep 5497037 = 2061389) (by norm_num)
theorem B3664691 : Blo 2287435 3664691 := bstep (se 1 (by rfl) ⟨2748518, by rfl⟩ : syracuseStep 3664691 = 5497037) B5497037
theorem B2443127 : Blo 2287435 2443127 := bstep (se 1 (by rfl) ⟨1832345, by rfl⟩ : syracuseStep 2443127 = 3664691) B3664691
theorem B6515005 : Blo 2287435 6515005 := bstep (se 3 (by rfl) ⟨1221563, by rfl⟩ : syracuseStep 6515005 = 2443127) B2443127
theorem B8686673 : Blo 2287435 8686673 := bstep (se 2 (by rfl) ⟨3257502, by rfl⟩ : syracuseStep 8686673 = 6515005) B6515005
theorem B5791115 : Blo 2287435 5791115 := bstep (se 1 (by rfl) ⟨4343336, by rfl⟩ : syracuseStep 5791115 = 8686673) B8686673
theorem B3860743 : Blo 2287435 3860743 := bstep (se 1 (by rfl) ⟨2895557, by rfl⟩ : syracuseStep 3860743 = 5791115) B5791115
theorem B5147657 : Blo 2287435 5147657 := bstep (se 2 (by rfl) ⟨1930371, by rfl⟩ : syracuseStep 5147657 = 3860743) B3860743
theorem B3431771 : Blo 2287435 3431771 := bstep (se 1 (by rfl) ⟨2573828, by rfl⟩ : syracuseStep 3431771 = 5147657) B5147657
theorem B2287847 : Blo 2287435 2287847 := bstep (se 1 (by rfl) ⟨1715885, by rfl⟩ : syracuseStep 2287847 = 3431771) B3431771
theorem B2573833 : Blo 2287435 2573833 := bbase (se 2 (by rfl) ⟨965187, by rfl⟩ : syracuseStep 2573833 = 1930375) (by norm_num)
theorem B3431777 : Blo 2287435 3431777 := bstep (se 2 (by rfl) ⟨1286916, by rfl⟩ : syracuseStep 3431777 = 2573833) B2573833
theorem B2287851 : Blo 2287435 2287851 := bstep (se 1 (by rfl) ⟨1715888, by rfl⟩ : syracuseStep 2287851 = 3431777) B3431777
theorem B22288213 : Blo 2287435 22288213 := bbase (se 9 (by rfl) ⟨65297, by rfl⟩ : syracuseStep 22288213 = 130595) (by norm_num)
theorem B29717617 : Blo 2287435 29717617 := bstep (se 2 (by rfl) ⟨11144106, by rfl⟩ : syracuseStep 29717617 = 22288213) B22288213
theorem B39623489 : Blo 2287435 39623489 := bstep (se 2 (by rfl) ⟨14858808, by rfl⟩ : syracuseStep 39623489 = 29717617) B29717617
theorem B26415659 : Blo 2287435 26415659 := bstep (se 1 (by rfl) ⟨19811744, by rfl⟩ : syracuseStep 26415659 = 39623489) B39623489
theorem B70441757 : Blo 2287435 70441757 := bstep (se 3 (by rfl) ⟨13207829, by rfl⟩ : syracuseStep 70441757 = 26415659) B26415659
theorem B46961171 : Blo 2287435 46961171 := bstep (se 1 (by rfl) ⟨35220878, by rfl⟩ : syracuseStep 46961171 = 70441757) B70441757
theorem B31307447 : Blo 2287435 31307447 := bstep (se 1 (by rfl) ⟨23480585, by rfl⟩ : syracuseStep 31307447 = 46961171) B46961171
theorem B20871631 : Blo 2287435 20871631 := bstep (se 1 (by rfl) ⟨15653723, by rfl⟩ : syracuseStep 20871631 = 31307447) B31307447
theorem B27828841 : Blo 2287435 27828841 := bstep (se 2 (by rfl) ⟨10435815, by rfl⟩ : syracuseStep 27828841 = 20871631) B20871631
theorem B37105121 : Blo 2287435 37105121 := bstep (se 2 (by rfl) ⟨13914420, by rfl⟩ : syracuseStep 37105121 = 27828841) B27828841
theorem B24736747 : Blo 2287435 24736747 := bstep (se 1 (by rfl) ⟨18552560, by rfl⟩ : syracuseStep 24736747 = 37105121) B37105121
theorem B32982329 : Blo 2287435 32982329 := bstep (se 2 (by rfl) ⟨12368373, by rfl⟩ : syracuseStep 32982329 = 24736747) B24736747
theorem B21988219 : Blo 2287435 21988219 := bstep (se 1 (by rfl) ⟨16491164, by rfl⟩ : syracuseStep 21988219 = 32982329) B32982329
theorem B29317625 : Blo 2287435 29317625 := bstep (se 2 (by rfl) ⟨10994109, by rfl⟩ : syracuseStep 29317625 = 21988219) B21988219
theorem B19545083 : Blo 2287435 19545083 := bstep (se 1 (by rfl) ⟨14658812, by rfl⟩ : syracuseStep 19545083 = 29317625) B29317625
theorem B13030055 : Blo 2287435 13030055 := bstep (se 1 (by rfl) ⟨9772541, by rfl⟩ : syracuseStep 13030055 = 19545083) B19545083
theorem B8686703 : Blo 2287435 8686703 := bstep (se 1 (by rfl) ⟨6515027, by rfl⟩ : syracuseStep 8686703 = 13030055) B13030055
theorem B5791135 : Blo 2287435 5791135 := bstep (se 1 (by rfl) ⟨4343351, by rfl⟩ : syracuseStep 5791135 = 8686703) B8686703
theorem B7721513 : Blo 2287435 7721513 := bstep (se 2 (by rfl) ⟨2895567, by rfl⟩ : syracuseStep 7721513 = 5791135) B5791135
theorem B5147675 : Blo 2287435 5147675 := bstep (se 1 (by rfl) ⟨3860756, by rfl⟩ : syracuseStep 5147675 = 7721513) B7721513
theorem B3431783 : Blo 2287435 3431783 := bstep (se 1 (by rfl) ⟨2573837, by rfl⟩ : syracuseStep 3431783 = 5147675) B5147675
theorem B2287855 : Blo 2287435 2287855 := bstep (se 1 (by rfl) ⟨1715891, by rfl⟩ : syracuseStep 2287855 = 3431783) B3431783
theorem B3431789 : Blo 2287435 3431789 := bbase (se 3 (by rfl) ⟨643460, by rfl⟩ : syracuseStep 3431789 = 1286921) (by norm_num)
theorem B2287859 : Blo 2287435 2287859 := bstep (se 1 (by rfl) ⟨1715894, by rfl⟩ : syracuseStep 2287859 = 3431789) B3431789
theorem B5147693 : Blo 2287435 5147693 := bbase (se 3 (by rfl) ⟨965192, by rfl⟩ : syracuseStep 5147693 = 1930385) (by norm_num)
theorem B3431795 : Blo 2287435 3431795 := bstep (se 1 (by rfl) ⟨2573846, by rfl⟩ : syracuseStep 3431795 = 5147693) B5147693
theorem B2287863 : Blo 2287435 2287863 := bstep (se 1 (by rfl) ⟨1715897, by rfl⟩ : syracuseStep 2287863 = 3431795) B3431795
theorem B5497085 : Blo 2287435 5497085 := bbase (se 3 (by rfl) ⟨1030703, by rfl⟩ : syracuseStep 5497085 = 2061407) (by norm_num)
theorem B14658893 : Blo 2287435 14658893 := bstep (se 3 (by rfl) ⟨2748542, by rfl⟩ : syracuseStep 14658893 = 5497085) B5497085
theorem B9772595 : Blo 2287435 9772595 := bstep (se 1 (by rfl) ⟨7329446, by rfl⟩ : syracuseStep 9772595 = 14658893) B14658893
theorem B6515063 : Blo 2287435 6515063 := bstep (se 1 (by rfl) ⟨4886297, by rfl⟩ : syracuseStep 6515063 = 9772595) B9772595
theorem B4343375 : Blo 2287435 4343375 := bstep (se 1 (by rfl) ⟨3257531, by rfl⟩ : syracuseStep 4343375 = 6515063) B6515063
theorem B2895583 : Blo 2287435 2895583 := bstep (se 1 (by rfl) ⟨2171687, by rfl⟩ : syracuseStep 2895583 = 4343375) B4343375
theorem B3860777 : Blo 2287435 3860777 := bstep (se 2 (by rfl) ⟨1447791, by rfl⟩ : syracuseStep 3860777 = 2895583) B2895583
theorem B2573851 : Blo 2287435 2573851 := bstep (se 1 (by rfl) ⟨1930388, by rfl⟩ : syracuseStep 2573851 = 3860777) B3860777
theorem B3431801 : Blo 2287435 3431801 := bstep (se 2 (by rfl) ⟨1286925, by rfl⟩ : syracuseStep 3431801 = 2573851) B2573851
theorem B2287867 : Blo 2287435 2287867 := bstep (se 1 (by rfl) ⟨1715900, by rfl⟩ : syracuseStep 2287867 = 3431801) B3431801
theorem B5497093 : Blo 2287435 5497093 := bbase (se 4 (by rfl) ⟨515352, by rfl⟩ : syracuseStep 5497093 = 1030705) (by norm_num)
theorem B7329457 : Blo 2287435 7329457 := bstep (se 2 (by rfl) ⟨2748546, by rfl⟩ : syracuseStep 7329457 = 5497093) B5497093
theorem B39090437 : Blo 2287435 39090437 := bstep (se 4 (by rfl) ⟨3664728, by rfl⟩ : syracuseStep 39090437 = 7329457) B7329457
theorem B26060291 : Blo 2287435 26060291 := bstep (se 1 (by rfl) ⟨19545218, by rfl⟩ : syracuseStep 26060291 = 39090437) B39090437
theorem B17373527 : Blo 2287435 17373527 := bstep (se 1 (by rfl) ⟨13030145, by rfl⟩ : syracuseStep 17373527 = 26060291) B26060291
theorem B11582351 : Blo 2287435 11582351 := bstep (se 1 (by rfl) ⟨8686763, by rfl⟩ : syracuseStep 11582351 = 17373527) B17373527
theorem B7721567 : Blo 2287435 7721567 := bstep (se 1 (by rfl) ⟨5791175, by rfl⟩ : syracuseStep 7721567 = 11582351) B11582351
theorem B5147711 : Blo 2287435 5147711 := bstep (se 1 (by rfl) ⟨3860783, by rfl⟩ : syracuseStep 5147711 = 7721567) B7721567
theorem B3431807 : Blo 2287435 3431807 := bstep (se 1 (by rfl) ⟨2573855, by rfl⟩ : syracuseStep 3431807 = 5147711) B5147711
theorem B2287871 : Blo 2287435 2287871 := bstep (se 1 (by rfl) ⟨1715903, by rfl⟩ : syracuseStep 2287871 = 3431807) B3431807
theorem B3431813 : Blo 2287435 3431813 := bbase (se 4 (by rfl) ⟨321732, by rfl⟩ : syracuseStep 3431813 = 643465) (by norm_num)
theorem B2287875 : Blo 2287435 2287875 := bstep (se 1 (by rfl) ⟨1715906, by rfl⟩ : syracuseStep 2287875 = 3431813) B3431813
theorem B3860797 : Blo 2287435 3860797 := bbase (se 3 (by rfl) ⟨723899, by rfl⟩ : syracuseStep 3860797 = 1447799) (by norm_num)
theorem B5147729 : Blo 2287435 5147729 := bstep (se 2 (by rfl) ⟨1930398, by rfl⟩ : syracuseStep 5147729 = 3860797) B3860797
theorem B3431819 : Blo 2287435 3431819 := bstep (se 1 (by rfl) ⟨2573864, by rfl⟩ : syracuseStep 3431819 = 5147729) B5147729
theorem B2287879 : Blo 2287435 2287879 := bstep (se 1 (by rfl) ⟨1715909, by rfl⟩ : syracuseStep 2287879 = 3431819) B3431819
theorem B2573869 : Blo 2287435 2573869 := bbase (se 3 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 2573869 = 965201) (by norm_num)
theorem B3431825 : Blo 2287435 3431825 := bstep (se 2 (by rfl) ⟨1286934, by rfl⟩ : syracuseStep 3431825 = 2573869) B2573869
theorem B2287883 : Blo 2287435 2287883 := bstep (se 1 (by rfl) ⟨1715912, by rfl⟩ : syracuseStep 2287883 = 3431825) B3431825
theorem B7721621 : Blo 2287435 7721621 := bbase (se 6 (by rfl) ⟨180975, by rfl⟩ : syracuseStep 7721621 = 361951) (by norm_num)
theorem B5147747 : Blo 2287435 5147747 := bstep (se 1 (by rfl) ⟨3860810, by rfl⟩ : syracuseStep 5147747 = 7721621) B7721621
theorem B3431831 : Blo 2287435 3431831 := bstep (se 1 (by rfl) ⟨2573873, by rfl⟩ : syracuseStep 3431831 = 5147747) B5147747
theorem B2287887 : Blo 2287435 2287887 := bstep (se 1 (by rfl) ⟨1715915, by rfl⟩ : syracuseStep 2287887 = 3431831) B3431831
theorem B3431837 : Blo 2287435 3431837 := bbase (se 3 (by rfl) ⟨643469, by rfl⟩ : syracuseStep 3431837 = 1286939) (by norm_num)
theorem B2287891 : Blo 2287435 2287891 := bstep (se 1 (by rfl) ⟨1715918, by rfl⟩ : syracuseStep 2287891 = 3431837) B3431837
theorem B5147765 : Blo 2287435 5147765 := bbase (se 5 (by rfl) ⟨241301, by rfl⟩ : syracuseStep 5147765 = 482603) (by norm_num)
theorem B3431843 : Blo 2287435 3431843 := bstep (se 1 (by rfl) ⟨2573882, by rfl⟩ : syracuseStep 3431843 = 5147765) B5147765
theorem B2287895 : Blo 2287435 2287895 := bstep (se 1 (by rfl) ⟨1715921, by rfl⟩ : syracuseStep 2287895 = 3431843) B3431843
theorem B19545461 : Blo 2287435 19545461 := bbase (se 5 (by rfl) ⟨916193, by rfl⟩ : syracuseStep 19545461 = 1832387) (by norm_num)
theorem B13030307 : Blo 2287435 13030307 := bstep (se 1 (by rfl) ⟨9772730, by rfl⟩ : syracuseStep 13030307 = 19545461) B19545461
theorem B8686871 : Blo 2287435 8686871 := bstep (se 1 (by rfl) ⟨6515153, by rfl⟩ : syracuseStep 8686871 = 13030307) B13030307
theorem B5791247 : Blo 2287435 5791247 := bstep (se 1 (by rfl) ⟨4343435, by rfl⟩ : syracuseStep 5791247 = 8686871) B8686871
theorem B3860831 : Blo 2287435 3860831 := bstep (se 1 (by rfl) ⟨2895623, by rfl⟩ : syracuseStep 3860831 = 5791247) B5791247
theorem B2573887 : Blo 2287435 2573887 := bstep (se 1 (by rfl) ⟨1930415, by rfl⟩ : syracuseStep 2573887 = 3860831) B3860831
theorem B3431849 : Blo 2287435 3431849 := bstep (se 2 (by rfl) ⟨1286943, by rfl⟩ : syracuseStep 3431849 = 2573887) B2573887
theorem B2287899 : Blo 2287435 2287899 := bstep (se 1 (by rfl) ⟨1715924, by rfl⟩ : syracuseStep 2287899 = 3431849) B3431849
theorem B8686885 : Blo 2287435 8686885 := bbase (se 4 (by rfl) ⟨814395, by rfl⟩ : syracuseStep 8686885 = 1628791) (by norm_num)
theorem B11582513 : Blo 2287435 11582513 := bstep (se 2 (by rfl) ⟨4343442, by rfl⟩ : syracuseStep 11582513 = 8686885) B8686885
theorem B7721675 : Blo 2287435 7721675 := bstep (se 1 (by rfl) ⟨5791256, by rfl⟩ : syracuseStep 7721675 = 11582513) B11582513
theorem B5147783 : Blo 2287435 5147783 := bstep (se 1 (by rfl) ⟨3860837, by rfl⟩ : syracuseStep 5147783 = 7721675) B7721675
theorem B3431855 : Blo 2287435 3431855 := bstep (se 1 (by rfl) ⟨2573891, by rfl⟩ : syracuseStep 3431855 = 5147783) B5147783
theorem B2287903 : Blo 2287435 2287903 := bstep (se 1 (by rfl) ⟨1715927, by rfl⟩ : syracuseStep 2287903 = 3431855) B3431855
theorem B3431861 : Blo 2287435 3431861 := bbase (se 5 (by rfl) ⟨160868, by rfl⟩ : syracuseStep 3431861 = 321737) (by norm_num)
theorem B2287907 : Blo 2287435 2287907 := bstep (se 1 (by rfl) ⟨1715930, by rfl⟩ : syracuseStep 2287907 = 3431861) B3431861
theorem B5791277 : Blo 2287435 5791277 := bbase (se 3 (by rfl) ⟨1085864, by rfl⟩ : syracuseStep 5791277 = 2171729) (by norm_num)
theorem B3860851 : Blo 2287435 3860851 := bstep (se 1 (by rfl) ⟨2895638, by rfl⟩ : syracuseStep 3860851 = 5791277) B5791277
theorem B5147801 : Blo 2287435 5147801 := bstep (se 2 (by rfl) ⟨1930425, by rfl⟩ : syracuseStep 5147801 = 3860851) B3860851
theorem B3431867 : Blo 2287435 3431867 := bstep (se 1 (by rfl) ⟨2573900, by rfl⟩ : syracuseStep 3431867 = 5147801) B5147801
theorem B2287911 : Blo 2287435 2287911 := bstep (se 1 (by rfl) ⟨1715933, by rfl⟩ : syracuseStep 2287911 = 3431867) B3431867
theorem B2573905 : Blo 2287435 2573905 := bbase (se 2 (by rfl) ⟨965214, by rfl⟩ : syracuseStep 2573905 = 1930429) (by norm_num)
theorem B3431873 : Blo 2287435 3431873 := bstep (se 2 (by rfl) ⟨1286952, by rfl⟩ : syracuseStep 3431873 = 2573905) B2573905
theorem B2287915 : Blo 2287435 2287915 := bstep (se 1 (by rfl) ⟨1715936, by rfl⟩ : syracuseStep 2287915 = 3431873) B3431873
theorem B3257605 : Blo 2287435 3257605 := bbase (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) (by norm_num)
theorem B4343473 : Blo 2287435 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B5791297 : Blo 2287435 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B7721729 : Blo 2287435 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B5147819 : Blo 2287435 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B3431879 : Blo 2287435 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B2287919 : Blo 2287435 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B3431885 : Blo 2287435 3431885 := bbase (se 3 (by rfl) ⟨643478, by rfl⟩ : syracuseStep 3431885 = 1286957) (by norm_num)
theorem B2287923 : Blo 2287435 2287923 := bstep (se 1 (by rfl) ⟨1715942, by rfl⟩ : syracuseStep 2287923 = 3431885) B3431885
theorem B5147837 : Blo 2287435 5147837 := bbase (se 3 (by rfl) ⟨965219, by rfl⟩ : syracuseStep 5147837 = 1930439) (by norm_num)
theorem B3431891 : Blo 2287435 3431891 := bstep (se 1 (by rfl) ⟨2573918, by rfl⟩ : syracuseStep 3431891 = 5147837) B5147837
theorem B2287927 : Blo 2287435 2287927 := bstep (se 1 (by rfl) ⟨1715945, by rfl⟩ : syracuseStep 2287927 = 3431891) B3431891
theorem B3860885 : Blo 2287435 3860885 := bbase (se 6 (by rfl) ⟨90489, by rfl⟩ : syracuseStep 3860885 = 180979) (by norm_num)
theorem B2573923 : Blo 2287435 2573923 := bstep (se 1 (by rfl) ⟨1930442, by rfl⟩ : syracuseStep 2573923 = 3860885) B3860885
theorem B3431897 : Blo 2287435 3431897 := bstep (se 2 (by rfl) ⟨1286961, by rfl⟩ : syracuseStep 3431897 = 2573923) B2573923
theorem B2287931 : Blo 2287435 2287931 := bstep (se 1 (by rfl) ⟨1715948, by rfl⟩ : syracuseStep 2287931 = 3431897) B3431897
theorem B2786125 : Blo 2287435 2786125 := bbase (se 3 (by rfl) ⟨522398, by rfl⟩ : syracuseStep 2786125 = 1044797) (by norm_num)
theorem B3714833 : Blo 2287435 3714833 := bstep (se 2 (by rfl) ⟨1393062, by rfl⟩ : syracuseStep 3714833 = 2786125) B2786125
theorem B2476555 : Blo 2287435 2476555 := bstep (se 1 (by rfl) ⟨1857416, by rfl⟩ : syracuseStep 2476555 = 3714833) B3714833
theorem B13208293 : Blo 2287435 13208293 := bstep (se 4 (by rfl) ⟨1238277, by rfl⟩ : syracuseStep 13208293 = 2476555) B2476555
theorem B17611057 : Blo 2287435 17611057 := bstep (se 2 (by rfl) ⟨6604146, by rfl⟩ : syracuseStep 17611057 = 13208293) B13208293
theorem B23481409 : Blo 2287435 23481409 := bstep (se 2 (by rfl) ⟨8805528, by rfl⟩ : syracuseStep 23481409 = 17611057) B17611057
theorem B31308545 : Blo 2287435 31308545 := bstep (se 2 (by rfl) ⟨11740704, by rfl⟩ : syracuseStep 31308545 = 23481409) B23481409
theorem B20872363 : Blo 2287435 20872363 := bstep (se 1 (by rfl) ⟨15654272, by rfl⟩ : syracuseStep 20872363 = 31308545) B31308545
theorem B27829817 : Blo 2287435 27829817 := bstep (se 2 (by rfl) ⟨10436181, by rfl⟩ : syracuseStep 27829817 = 20872363) B20872363
theorem B18553211 : Blo 2287435 18553211 := bstep (se 1 (by rfl) ⟨13914908, by rfl⟩ : syracuseStep 18553211 = 27829817) B27829817
theorem B12368807 : Blo 2287435 12368807 := bstep (se 1 (by rfl) ⟨9276605, by rfl⟩ : syracuseStep 12368807 = 18553211) B18553211
theorem B8245871 : Blo 2287435 8245871 := bstep (se 1 (by rfl) ⟨6184403, by rfl⟩ : syracuseStep 8245871 = 12368807) B12368807
theorem B5497247 : Blo 2287435 5497247 := bstep (se 1 (by rfl) ⟨4122935, by rfl⟩ : syracuseStep 5497247 = 8245871) B8245871
theorem B14659325 : Blo 2287435 14659325 := bstep (se 3 (by rfl) ⟨2748623, by rfl⟩ : syracuseStep 14659325 = 5497247) B5497247
theorem B9772883 : Blo 2287435 9772883 := bstep (se 1 (by rfl) ⟨7329662, by rfl⟩ : syracuseStep 9772883 = 14659325) B14659325
theorem B6515255 : Blo 2287435 6515255 := bstep (se 1 (by rfl) ⟨4886441, by rfl⟩ : syracuseStep 6515255 = 9772883) B9772883
theorem B17374013 : Blo 2287435 17374013 := bstep (se 3 (by rfl) ⟨3257627, by rfl⟩ : syracuseStep 17374013 = 6515255) B6515255
theorem B11582675 : Blo 2287435 11582675 := bstep (se 1 (by rfl) ⟨8687006, by rfl⟩ : syracuseStep 11582675 = 17374013) B17374013
theorem B7721783 : Blo 2287435 7721783 := bstep (se 1 (by rfl) ⟨5791337, by rfl⟩ : syracuseStep 7721783 = 11582675) B11582675
theorem B5147855 : Blo 2287435 5147855 := bstep (se 1 (by rfl) ⟨3860891, by rfl⟩ : syracuseStep 5147855 = 7721783) B7721783
theorem B3431903 : Blo 2287435 3431903 := bstep (se 1 (by rfl) ⟨2573927, by rfl⟩ : syracuseStep 3431903 = 5147855) B5147855
theorem B2287935 : Blo 2287435 2287935 := bstep (se 1 (by rfl) ⟨1715951, by rfl⟩ : syracuseStep 2287935 = 3431903) B3431903
theorem B3431909 : Blo 2287435 3431909 := bbase (se 4 (by rfl) ⟨321741, by rfl⟩ : syracuseStep 3431909 = 643483) (by norm_num)
theorem B2287939 : Blo 2287435 2287939 := bstep (se 1 (by rfl) ⟨1715954, by rfl⟩ : syracuseStep 2287939 = 3431909) B3431909
theorem B3092213 : Blo 2287435 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B8245901 : Blo 2287435 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B21989069 : Blo 2287435 21989069 := bstep (se 3 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 21989069 = 8245901) B8245901
theorem B14659379 : Blo 2287435 14659379 := bstep (se 1 (by rfl) ⟨10994534, by rfl⟩ : syracuseStep 14659379 = 21989069) B21989069
theorem B9772919 : Blo 2287435 9772919 := bstep (se 1 (by rfl) ⟨7329689, by rfl⟩ : syracuseStep 9772919 = 14659379) B14659379
theorem B6515279 : Blo 2287435 6515279 := bstep (se 1 (by rfl) ⟨4886459, by rfl⟩ : syracuseStep 6515279 = 9772919) B9772919
theorem B4343519 : Blo 2287435 4343519 := bstep (se 1 (by rfl) ⟨3257639, by rfl⟩ : syracuseStep 4343519 = 6515279) B6515279
theorem B2895679 : Blo 2287435 2895679 := bstep (se 1 (by rfl) ⟨2171759, by rfl⟩ : syracuseStep 2895679 = 4343519) B4343519
theorem B3860905 : Blo 2287435 3860905 := bstep (se 2 (by rfl) ⟨1447839, by rfl⟩ : syracuseStep 3860905 = 2895679) B2895679
theorem B5147873 : Blo 2287435 5147873 := bstep (se 2 (by rfl) ⟨1930452, by rfl⟩ : syracuseStep 5147873 = 3860905) B3860905
theorem B3431915 : Blo 2287435 3431915 := bstep (se 1 (by rfl) ⟨2573936, by rfl⟩ : syracuseStep 3431915 = 5147873) B5147873
theorem B2287943 : Blo 2287435 2287943 := bstep (se 1 (by rfl) ⟨1715957, by rfl⟩ : syracuseStep 2287943 = 3431915) B3431915
theorem B2573941 : Blo 2287435 2573941 := bbase (se 5 (by rfl) ⟨120653, by rfl⟩ : syracuseStep 2573941 = 241307) (by norm_num)
theorem B3431921 : Blo 2287435 3431921 := bstep (se 2 (by rfl) ⟨1286970, by rfl⟩ : syracuseStep 3431921 = 2573941) B2573941
theorem B2287947 : Blo 2287435 2287947 := bstep (se 1 (by rfl) ⟨1715960, by rfl⟩ : syracuseStep 2287947 = 3431921) B3431921
theorem B2895689 : Blo 2287435 2895689 := bbase (se 2 (by rfl) ⟨1085883, by rfl⟩ : syracuseStep 2895689 = 2171767) (by norm_num)
theorem B7721837 : Blo 2287435 7721837 := bstep (se 3 (by rfl) ⟨1447844, by rfl⟩ : syracuseStep 7721837 = 2895689) B2895689
theorem B5147891 : Blo 2287435 5147891 := bstep (se 1 (by rfl) ⟨3860918, by rfl⟩ : syracuseStep 5147891 = 7721837) B7721837
theorem B3431927 : Blo 2287435 3431927 := bstep (se 1 (by rfl) ⟨2573945, by rfl⟩ : syracuseStep 3431927 = 5147891) B5147891
theorem B2287951 : Blo 2287435 2287951 := bstep (se 1 (by rfl) ⟨1715963, by rfl⟩ : syracuseStep 2287951 = 3431927) B3431927
theorem B3431933 : Blo 2287435 3431933 := bbase (se 3 (by rfl) ⟨643487, by rfl⟩ : syracuseStep 3431933 = 1286975) (by norm_num)
theorem B2287955 : Blo 2287435 2287955 := bstep (se 1 (by rfl) ⟨1715966, by rfl⟩ : syracuseStep 2287955 = 3431933) B3431933
theorem B5147909 : Blo 2287435 5147909 := bbase (se 4 (by rfl) ⟨482616, by rfl⟩ : syracuseStep 5147909 = 965233) (by norm_num)
theorem B3431939 : Blo 2287435 3431939 := bstep (se 1 (by rfl) ⟨2573954, by rfl⟩ : syracuseStep 3431939 = 5147909) B5147909
theorem B2287959 : Blo 2287435 2287959 := bstep (se 1 (by rfl) ⟨1715969, by rfl⟩ : syracuseStep 2287959 = 3431939) B3431939
theorem B4343557 : Blo 2287435 4343557 := bbase (se 4 (by rfl) ⟨407208, by rfl⟩ : syracuseStep 4343557 = 814417) (by norm_num)
theorem B5791409 : Blo 2287435 5791409 := bstep (se 2 (by rfl) ⟨2171778, by rfl⟩ : syracuseStep 5791409 = 4343557) B4343557
theorem B3860939 : Blo 2287435 3860939 := bstep (se 1 (by rfl) ⟨2895704, by rfl⟩ : syracuseStep 3860939 = 5791409) B5791409
theorem B2573959 : Blo 2287435 2573959 := bstep (se 1 (by rfl) ⟨1930469, by rfl⟩ : syracuseStep 2573959 = 3860939) B3860939
theorem B3431945 : Blo 2287435 3431945 := bstep (se 2 (by rfl) ⟨1286979, by rfl⟩ : syracuseStep 3431945 = 2573959) B2573959
theorem B2287963 : Blo 2287435 2287963 := bstep (se 1 (by rfl) ⟨1715972, by rfl⟩ : syracuseStep 2287963 = 3431945) B3431945
theorem B11582837 : Blo 2287435 11582837 := bbase (se 5 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 11582837 = 1085891) (by norm_num)
theorem B7721891 : Blo 2287435 7721891 := bstep (se 1 (by rfl) ⟨5791418, by rfl⟩ : syracuseStep 7721891 = 11582837) B11582837
theorem B5147927 : Blo 2287435 5147927 := bstep (se 1 (by rfl) ⟨3860945, by rfl⟩ : syracuseStep 5147927 = 7721891) B7721891
theorem B3431951 : Blo 2287435 3431951 := bstep (se 1 (by rfl) ⟨2573963, by rfl⟩ : syracuseStep 3431951 = 5147927) B5147927
theorem B2287967 : Blo 2287435 2287967 := bstep (se 1 (by rfl) ⟨1715975, by rfl⟩ : syracuseStep 2287967 = 3431951) B3431951
theorem B3431957 : Blo 2287435 3431957 := bbase (se 6 (by rfl) ⟨80436, by rfl⟩ : syracuseStep 3431957 = 160873) (by norm_num)
theorem B2287971 : Blo 2287435 2287971 := bstep (se 1 (by rfl) ⟨1715978, by rfl⟩ : syracuseStep 2287971 = 3431957) B3431957
theorem B3439141 : Blo 2287435 3439141 := bbase (se 4 (by rfl) ⟨322419, by rfl⟩ : syracuseStep 3439141 = 644839) (by norm_num)
theorem B18342085 : Blo 2287435 18342085 := bstep (se 4 (by rfl) ⟨1719570, by rfl⟩ : syracuseStep 18342085 = 3439141) B3439141
theorem B24456113 : Blo 2287435 24456113 := bstep (se 2 (by rfl) ⟨9171042, by rfl⟩ : syracuseStep 24456113 = 18342085) B18342085
theorem B16304075 : Blo 2287435 16304075 := bstep (se 1 (by rfl) ⟨12228056, by rfl⟩ : syracuseStep 16304075 = 24456113) B24456113
theorem B10869383 : Blo 2287435 10869383 := bstep (se 1 (by rfl) ⟨8152037, by rfl⟩ : syracuseStep 10869383 = 16304075) B16304075
theorem B7246255 : Blo 2287435 7246255 := bstep (se 1 (by rfl) ⟨5434691, by rfl⟩ : syracuseStep 7246255 = 10869383) B10869383
theorem B9661673 : Blo 2287435 9661673 := bstep (se 2 (by rfl) ⟨3623127, by rfl⟩ : syracuseStep 9661673 = 7246255) B7246255
theorem B6441115 : Blo 2287435 6441115 := bstep (se 1 (by rfl) ⟨4830836, by rfl⟩ : syracuseStep 6441115 = 9661673) B9661673
theorem B8588153 : Blo 2287435 8588153 := bstep (se 2 (by rfl) ⟨3220557, by rfl⟩ : syracuseStep 8588153 = 6441115) B6441115
theorem B22901741 : Blo 2287435 22901741 := bstep (se 3 (by rfl) ⟨4294076, by rfl⟩ : syracuseStep 22901741 = 8588153) B8588153
theorem B15267827 : Blo 2287435 15267827 := bstep (se 1 (by rfl) ⟨11450870, by rfl⟩ : syracuseStep 15267827 = 22901741) B22901741
theorem B10178551 : Blo 2287435 10178551 := bstep (se 1 (by rfl) ⟨7633913, by rfl⟩ : syracuseStep 10178551 = 15267827) B15267827
theorem B13571401 : Blo 2287435 13571401 := bstep (se 2 (by rfl) ⟨5089275, by rfl⟩ : syracuseStep 13571401 = 10178551) B10178551
theorem B18095201 : Blo 2287435 18095201 := bstep (se 2 (by rfl) ⟨6785700, by rfl⟩ : syracuseStep 18095201 = 13571401) B13571401
theorem B12063467 : Blo 2287435 12063467 := bstep (se 1 (by rfl) ⟨9047600, by rfl⟩ : syracuseStep 12063467 = 18095201) B18095201
theorem B8042311 : Blo 2287435 8042311 := bstep (se 1 (by rfl) ⟨6031733, by rfl⟩ : syracuseStep 8042311 = 12063467) B12063467
theorem B42892325 : Blo 2287435 42892325 := bstep (se 4 (by rfl) ⟨4021155, by rfl⟩ : syracuseStep 42892325 = 8042311) B8042311
theorem B28594883 : Blo 2287435 28594883 := bstep (se 1 (by rfl) ⟨21446162, by rfl⟩ : syracuseStep 28594883 = 42892325) B42892325
theorem B76253021 : Blo 2287435 76253021 := bstep (se 3 (by rfl) ⟨14297441, by rfl⟩ : syracuseStep 76253021 = 28594883) B28594883
theorem B50835347 : Blo 2287435 50835347 := bstep (se 1 (by rfl) ⟨38126510, by rfl⟩ : syracuseStep 50835347 = 76253021) B76253021
theorem B33890231 : Blo 2287435 33890231 := bstep (se 1 (by rfl) ⟨25417673, by rfl⟩ : syracuseStep 33890231 = 50835347) B50835347
theorem B22593487 : Blo 2287435 22593487 := bstep (se 1 (by rfl) ⟨16945115, by rfl⟩ : syracuseStep 22593487 = 33890231) B33890231
theorem B30124649 : Blo 2287435 30124649 := bstep (se 2 (by rfl) ⟨11296743, by rfl⟩ : syracuseStep 30124649 = 22593487) B22593487
theorem B20083099 : Blo 2287435 20083099 := bstep (se 1 (by rfl) ⟨15062324, by rfl⟩ : syracuseStep 20083099 = 30124649) B30124649
theorem B26777465 : Blo 2287435 26777465 := bstep (se 2 (by rfl) ⟨10041549, by rfl⟩ : syracuseStep 26777465 = 20083099) B20083099
theorem B17851643 : Blo 2287435 17851643 := bstep (se 1 (by rfl) ⟨13388732, by rfl⟩ : syracuseStep 17851643 = 26777465) B26777465
theorem B11901095 : Blo 2287435 11901095 := bstep (se 1 (by rfl) ⟨8925821, by rfl⟩ : syracuseStep 11901095 = 17851643) B17851643
theorem B7934063 : Blo 2287435 7934063 := bstep (se 1 (by rfl) ⟨5950547, by rfl⟩ : syracuseStep 7934063 = 11901095) B11901095
theorem B84630005 : Blo 2287435 84630005 := bstep (se 5 (by rfl) ⟨3967031, by rfl⟩ : syracuseStep 84630005 = 7934063) B7934063
theorem B56420003 : Blo 2287435 56420003 := bstep (se 1 (by rfl) ⟨42315002, by rfl⟩ : syracuseStep 56420003 = 84630005) B84630005
theorem B37613335 : Blo 2287435 37613335 := bstep (se 1 (by rfl) ⟨28210001, by rfl⟩ : syracuseStep 37613335 = 56420003) B56420003
theorem B50151113 : Blo 2287435 50151113 := bstep (se 2 (by rfl) ⟨18806667, by rfl⟩ : syracuseStep 50151113 = 37613335) B37613335
theorem B33434075 : Blo 2287435 33434075 := bstep (se 1 (by rfl) ⟨25075556, by rfl⟩ : syracuseStep 33434075 = 50151113) B50151113
theorem B22289383 : Blo 2287435 22289383 := bstep (se 1 (by rfl) ⟨16717037, by rfl⟩ : syracuseStep 22289383 = 33434075) B33434075
theorem B118876709 : Blo 2287435 118876709 := bstep (se 4 (by rfl) ⟨11144691, by rfl⟩ : syracuseStep 118876709 = 22289383) B22289383
theorem B79251139 : Blo 2287435 79251139 := bstep (se 1 (by rfl) ⟨59438354, by rfl⟩ : syracuseStep 79251139 = 118876709) B118876709
theorem B422672741 : Blo 2287435 422672741 := bstep (se 4 (by rfl) ⟨39625569, by rfl⟩ : syracuseStep 422672741 = 79251139) B79251139
theorem B281781827 : Blo 2287435 281781827 := bstep (se 1 (by rfl) ⟨211336370, by rfl⟩ : syracuseStep 281781827 = 422672741) B422672741
theorem B187854551 : Blo 2287435 187854551 := bstep (se 1 (by rfl) ⟨140890913, by rfl⟩ : syracuseStep 187854551 = 281781827) B281781827
theorem B125236367 : Blo 2287435 125236367 := bstep (se 1 (by rfl) ⟨93927275, by rfl⟩ : syracuseStep 125236367 = 187854551) B187854551
theorem B83490911 : Blo 2287435 83490911 := bstep (se 1 (by rfl) ⟨62618183, by rfl⟩ : syracuseStep 83490911 = 125236367) B125236367
theorem B55660607 : Blo 2287435 55660607 := bstep (se 1 (by rfl) ⟨41745455, by rfl⟩ : syracuseStep 55660607 = 83490911) B83490911
theorem B37107071 : Blo 2287435 37107071 := bstep (se 1 (by rfl) ⟨27830303, by rfl⟩ : syracuseStep 37107071 = 55660607) B55660607
theorem B24738047 : Blo 2287435 24738047 := bstep (se 1 (by rfl) ⟨18553535, by rfl⟩ : syracuseStep 24738047 = 37107071) B37107071
theorem B16492031 : Blo 2287435 16492031 := bstep (se 1 (by rfl) ⟨12369023, by rfl⟩ : syracuseStep 16492031 = 24738047) B24738047
theorem B10994687 : Blo 2287435 10994687 := bstep (se 1 (by rfl) ⟨8246015, by rfl⟩ : syracuseStep 10994687 = 16492031) B16492031
theorem B7329791 : Blo 2287435 7329791 := bstep (se 1 (by rfl) ⟨5497343, by rfl⟩ : syracuseStep 7329791 = 10994687) B10994687
theorem B19546109 : Blo 2287435 19546109 := bstep (se 3 (by rfl) ⟨3664895, by rfl⟩ : syracuseStep 19546109 = 7329791) B7329791
theorem B13030739 : Blo 2287435 13030739 := bstep (se 1 (by rfl) ⟨9773054, by rfl⟩ : syracuseStep 13030739 = 19546109) B19546109
theorem B8687159 : Blo 2287435 8687159 := bstep (se 1 (by rfl) ⟨6515369, by rfl⟩ : syracuseStep 8687159 = 13030739) B13030739
theorem B5791439 : Blo 2287435 5791439 := bstep (se 1 (by rfl) ⟨4343579, by rfl⟩ : syracuseStep 5791439 = 8687159) B8687159
theorem B3860959 : Blo 2287435 3860959 := bstep (se 1 (by rfl) ⟨2895719, by rfl⟩ : syracuseStep 3860959 = 5791439) B5791439
theorem B5147945 : Blo 2287435 5147945 := bstep (se 2 (by rfl) ⟨1930479, by rfl⟩ : syracuseStep 5147945 = 3860959) B3860959
theorem B3431963 : Blo 2287435 3431963 := bstep (se 1 (by rfl) ⟨2573972, by rfl⟩ : syracuseStep 3431963 = 5147945) B5147945
theorem B2287975 : Blo 2287435 2287975 := bstep (se 1 (by rfl) ⟨1715981, by rfl⟩ : syracuseStep 2287975 = 3431963) B3431963
theorem B2573977 : Blo 2287435 2573977 := bbase (se 2 (by rfl) ⟨965241, by rfl⟩ : syracuseStep 2573977 = 1930483) (by norm_num)
theorem B3431969 : Blo 2287435 3431969 := bstep (se 2 (by rfl) ⟨1286988, by rfl⟩ : syracuseStep 3431969 = 2573977) B2573977
theorem B2287979 : Blo 2287435 2287979 := bstep (se 1 (by rfl) ⟨1715984, by rfl⟩ : syracuseStep 2287979 = 3431969) B3431969
theorem B8687189 : Blo 2287435 8687189 := bbase (se 8 (by rfl) ⟨50901, by rfl⟩ : syracuseStep 8687189 = 101803) (by norm_num)
theorem B5791459 : Blo 2287435 5791459 := bstep (se 1 (by rfl) ⟨4343594, by rfl⟩ : syracuseStep 5791459 = 8687189) B8687189
theorem B7721945 : Blo 2287435 7721945 := bstep (se 2 (by rfl) ⟨2895729, by rfl⟩ : syracuseStep 7721945 = 5791459) B5791459
theorem B5147963 : Blo 2287435 5147963 := bstep (se 1 (by rfl) ⟨3860972, by rfl⟩ : syracuseStep 5147963 = 7721945) B7721945
theorem B3431975 : Blo 2287435 3431975 := bstep (se 1 (by rfl) ⟨2573981, by rfl⟩ : syracuseStep 3431975 = 5147963) B5147963
theorem B2287983 : Blo 2287435 2287983 := bstep (se 1 (by rfl) ⟨1715987, by rfl⟩ : syracuseStep 2287983 = 3431975) B3431975
theorem B3431981 : Blo 2287435 3431981 := bbase (se 3 (by rfl) ⟨643496, by rfl⟩ : syracuseStep 3431981 = 1286993) (by norm_num)
theorem B2287987 : Blo 2287435 2287987 := bstep (se 1 (by rfl) ⟨1715990, by rfl⟩ : syracuseStep 2287987 = 3431981) B3431981
theorem B5147981 : Blo 2287435 5147981 := bbase (se 3 (by rfl) ⟨965246, by rfl⟩ : syracuseStep 5147981 = 1930493) (by norm_num)
theorem B3431987 : Blo 2287435 3431987 := bstep (se 1 (by rfl) ⟨2573990, by rfl⟩ : syracuseStep 3431987 = 5147981) B5147981
theorem B2287991 : Blo 2287435 2287991 := bstep (se 1 (by rfl) ⟨1715993, by rfl⟩ : syracuseStep 2287991 = 3431987) B3431987
theorem B2895745 : Blo 2287435 2895745 := bbase (se 2 (by rfl) ⟨1085904, by rfl⟩ : syracuseStep 2895745 = 2171809) (by norm_num)
theorem B3860993 : Blo 2287435 3860993 := bstep (se 2 (by rfl) ⟨1447872, by rfl⟩ : syracuseStep 3860993 = 2895745) B2895745
theorem B2573995 : Blo 2287435 2573995 := bstep (se 1 (by rfl) ⟨1930496, by rfl⟩ : syracuseStep 2573995 = 3860993) B3860993
theorem B3431993 : Blo 2287435 3431993 := bstep (se 2 (by rfl) ⟨1286997, by rfl⟩ : syracuseStep 3431993 = 2573995) B2573995
theorem B2287995 : Blo 2287435 2287995 := bstep (se 1 (by rfl) ⟨1715996, by rfl⟩ : syracuseStep 2287995 = 3431993) B3431993
theorem B2443289 : Blo 2287435 2443289 := bbase (se 2 (by rfl) ⟨916233, by rfl⟩ : syracuseStep 2443289 = 1832467) (by norm_num)
theorem B26061749 : Blo 2287435 26061749 := bstep (se 5 (by rfl) ⟨1221644, by rfl⟩ : syracuseStep 26061749 = 2443289) B2443289
theorem B17374499 : Blo 2287435 17374499 := bstep (se 1 (by rfl) ⟨13030874, by rfl⟩ : syracuseStep 17374499 = 26061749) B26061749
theorem B11582999 : Blo 2287435 11582999 := bstep (se 1 (by rfl) ⟨8687249, by rfl⟩ : syracuseStep 11582999 = 17374499) B17374499
theorem B7721999 : Blo 2287435 7721999 := bstep (se 1 (by rfl) ⟨5791499, by rfl⟩ : syracuseStep 7721999 = 11582999) B11582999
theorem B5147999 : Blo 2287435 5147999 := bstep (se 1 (by rfl) ⟨3860999, by rfl⟩ : syracuseStep 5147999 = 7721999) B7721999
theorem B3431999 : Blo 2287435 3431999 := bstep (se 1 (by rfl) ⟨2573999, by rfl⟩ : syracuseStep 3431999 = 5147999) B5147999
theorem B2287999 : Blo 2287435 2287999 := bstep (se 1 (by rfl) ⟨1715999, by rfl⟩ : syracuseStep 2287999 = 3431999) B3431999
theorem B3432005 : Blo 2287435 3432005 := bbase (se 4 (by rfl) ⟨321750, by rfl⟩ : syracuseStep 3432005 = 643501) (by norm_num)
theorem B2288003 : Blo 2287435 2288003 := bstep (se 1 (by rfl) ⟨1716002, by rfl⟩ : syracuseStep 2288003 = 3432005) B3432005
theorem B3861013 : Blo 2287435 3861013 := bbase (se 6 (by rfl) ⟨90492, by rfl⟩ : syracuseStep 3861013 = 180985) (by norm_num)
theorem B5148017 : Blo 2287435 5148017 := bstep (se 2 (by rfl) ⟨1930506, by rfl⟩ : syracuseStep 5148017 = 3861013) B3861013
theorem B3432011 : Blo 2287435 3432011 := bstep (se 1 (by rfl) ⟨2574008, by rfl⟩ : syracuseStep 3432011 = 5148017) B5148017
theorem B2288007 : Blo 2287435 2288007 := bstep (se 1 (by rfl) ⟨1716005, by rfl⟩ : syracuseStep 2288007 = 3432011) B3432011
theorem B2574013 : Blo 2287435 2574013 := bbase (se 3 (by rfl) ⟨482627, by rfl⟩ : syracuseStep 2574013 = 965255) (by norm_num)
theorem B3432017 : Blo 2287435 3432017 := bstep (se 2 (by rfl) ⟨1287006, by rfl⟩ : syracuseStep 3432017 = 2574013) B2574013
theorem B2288011 : Blo 2287435 2288011 := bstep (se 1 (by rfl) ⟨1716008, by rfl⟩ : syracuseStep 2288011 = 3432017) B3432017
theorem B7722053 : Blo 2287435 7722053 := bbase (se 4 (by rfl) ⟨723942, by rfl⟩ : syracuseStep 7722053 = 1447885) (by norm_num)
theorem B5148035 : Blo 2287435 5148035 := bstep (se 1 (by rfl) ⟨3861026, by rfl⟩ : syracuseStep 5148035 = 7722053) B7722053
theorem B3432023 : Blo 2287435 3432023 := bstep (se 1 (by rfl) ⟨2574017, by rfl⟩ : syracuseStep 3432023 = 5148035) B5148035
theorem B2288015 : Blo 2287435 2288015 := bstep (se 1 (by rfl) ⟨1716011, by rfl⟩ : syracuseStep 2288015 = 3432023) B3432023
theorem B3432029 : Blo 2287435 3432029 := bbase (se 3 (by rfl) ⟨643505, by rfl⟩ : syracuseStep 3432029 = 1287011) (by norm_num)
theorem B2288019 : Blo 2287435 2288019 := bstep (se 1 (by rfl) ⟨1716014, by rfl⟩ : syracuseStep 2288019 = 3432029) B3432029
theorem B5148053 : Blo 2287435 5148053 := bbase (se 6 (by rfl) ⟨120657, by rfl⟩ : syracuseStep 5148053 = 241315) (by norm_num)
theorem B3432035 : Blo 2287435 3432035 := bstep (se 1 (by rfl) ⟨2574026, by rfl⟩ : syracuseStep 3432035 = 5148053) B5148053
theorem B2288023 : Blo 2287435 2288023 := bstep (se 1 (by rfl) ⟨1716017, by rfl⟩ : syracuseStep 2288023 = 3432035) B3432035
theorem B10041781 : Blo 2287435 10041781 := bbase (se 5 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 10041781 = 941417) (by norm_num)
theorem B13389041 : Blo 2287435 13389041 := bstep (se 2 (by rfl) ⟨5020890, by rfl⟩ : syracuseStep 13389041 = 10041781) B10041781
theorem B8926027 : Blo 2287435 8926027 := bstep (se 1 (by rfl) ⟨6694520, by rfl⟩ : syracuseStep 8926027 = 13389041) B13389041
theorem B47605477 : Blo 2287435 47605477 := bstep (se 4 (by rfl) ⟨4463013, by rfl⟩ : syracuseStep 47605477 = 8926027) B8926027
theorem B63473969 : Blo 2287435 63473969 := bstep (se 2 (by rfl) ⟨23802738, by rfl⟩ : syracuseStep 63473969 = 47605477) B47605477
theorem B42315979 : Blo 2287435 42315979 := bstep (se 1 (by rfl) ⟨31736984, by rfl⟩ : syracuseStep 42315979 = 63473969) B63473969
theorem B56421305 : Blo 2287435 56421305 := bstep (se 2 (by rfl) ⟨21157989, by rfl⟩ : syracuseStep 56421305 = 42315979) B42315979
theorem B37614203 : Blo 2287435 37614203 := bstep (se 1 (by rfl) ⟨28210652, by rfl⟩ : syracuseStep 37614203 = 56421305) B56421305
theorem B25076135 : Blo 2287435 25076135 := bstep (se 1 (by rfl) ⟨18807101, by rfl⟩ : syracuseStep 25076135 = 37614203) B37614203
theorem B16717423 : Blo 2287435 16717423 := bstep (se 1 (by rfl) ⟨12538067, by rfl⟩ : syracuseStep 16717423 = 25076135) B25076135
theorem B22289897 : Blo 2287435 22289897 := bstep (se 2 (by rfl) ⟨8358711, by rfl⟩ : syracuseStep 22289897 = 16717423) B16717423
theorem B14859931 : Blo 2287435 14859931 := bstep (se 1 (by rfl) ⟨11144948, by rfl⟩ : syracuseStep 14859931 = 22289897) B22289897
theorem B19813241 : Blo 2287435 19813241 := bstep (se 2 (by rfl) ⟨7429965, by rfl⟩ : syracuseStep 19813241 = 14859931) B14859931
theorem B13208827 : Blo 2287435 13208827 := bstep (se 1 (by rfl) ⟨9906620, by rfl⟩ : syracuseStep 13208827 = 19813241) B19813241
theorem B17611769 : Blo 2287435 17611769 := bstep (se 2 (by rfl) ⟨6604413, by rfl⟩ : syracuseStep 17611769 = 13208827) B13208827
theorem B46964717 : Blo 2287435 46964717 := bstep (se 3 (by rfl) ⟨8805884, by rfl⟩ : syracuseStep 46964717 = 17611769) B17611769
theorem B31309811 : Blo 2287435 31309811 := bstep (se 1 (by rfl) ⟨23482358, by rfl⟩ : syracuseStep 31309811 = 46964717) B46964717
theorem B20873207 : Blo 2287435 20873207 := bstep (se 1 (by rfl) ⟨15654905, by rfl⟩ : syracuseStep 20873207 = 31309811) B31309811
theorem B13915471 : Blo 2287435 13915471 := bstep (se 1 (by rfl) ⟨10436603, by rfl⟩ : syracuseStep 13915471 = 20873207) B20873207
theorem B18553961 : Blo 2287435 18553961 := bstep (se 2 (by rfl) ⟨6957735, by rfl⟩ : syracuseStep 18553961 = 13915471) B13915471
theorem B12369307 : Blo 2287435 12369307 := bstep (se 1 (by rfl) ⟨9276980, by rfl⟩ : syracuseStep 12369307 = 18553961) B18553961
theorem B16492409 : Blo 2287435 16492409 := bstep (se 2 (by rfl) ⟨6184653, by rfl⟩ : syracuseStep 16492409 = 12369307) B12369307
theorem B10994939 : Blo 2287435 10994939 := bstep (se 1 (by rfl) ⟨8246204, by rfl⟩ : syracuseStep 10994939 = 16492409) B16492409
theorem B7329959 : Blo 2287435 7329959 := bstep (se 1 (by rfl) ⟨5497469, by rfl⟩ : syracuseStep 7329959 = 10994939) B10994939
theorem B4886639 : Blo 2287435 4886639 := bstep (se 1 (by rfl) ⟨3664979, by rfl⟩ : syracuseStep 4886639 = 7329959) B7329959
theorem B3257759 : Blo 2287435 3257759 := bstep (se 1 (by rfl) ⟨2443319, by rfl⟩ : syracuseStep 3257759 = 4886639) B4886639
theorem B8687357 : Blo 2287435 8687357 := bstep (se 3 (by rfl) ⟨1628879, by rfl⟩ : syracuseStep 8687357 = 3257759) B3257759
theorem B5791571 : Blo 2287435 5791571 := bstep (se 1 (by rfl) ⟨4343678, by rfl⟩ : syracuseStep 5791571 = 8687357) B8687357
theorem B3861047 : Blo 2287435 3861047 := bstep (se 1 (by rfl) ⟨2895785, by rfl⟩ : syracuseStep 3861047 = 5791571) B5791571
theorem B2574031 : Blo 2287435 2574031 := bstep (se 1 (by rfl) ⟨1930523, by rfl⟩ : syracuseStep 2574031 = 3861047) B3861047
theorem B3432041 : Blo 2287435 3432041 := bstep (se 2 (by rfl) ⟨1287015, by rfl⟩ : syracuseStep 3432041 = 2574031) B2574031
theorem B2288027 : Blo 2287435 2288027 := bstep (se 1 (by rfl) ⟨1716020, by rfl⟩ : syracuseStep 2288027 = 3432041) B3432041
theorem B4123109 : Blo 2287435 4123109 := bbase (se 4 (by rfl) ⟨386541, by rfl⟩ : syracuseStep 4123109 = 773083) (by norm_num)
theorem B2748739 : Blo 2287435 2748739 := bstep (se 1 (by rfl) ⟨2061554, by rfl⟩ : syracuseStep 2748739 = 4123109) B4123109
theorem B3664985 : Blo 2287435 3664985 := bstep (se 2 (by rfl) ⟨1374369, by rfl⟩ : syracuseStep 3664985 = 2748739) B2748739
theorem B9773293 : Blo 2287435 9773293 := bstep (se 3 (by rfl) ⟨1832492, by rfl⟩ : syracuseStep 9773293 = 3664985) B3664985
theorem B13031057 : Blo 2287435 13031057 := bstep (se 2 (by rfl) ⟨4886646, by rfl⟩ : syracuseStep 13031057 = 9773293) B9773293
theorem B8687371 : Blo 2287435 8687371 := bstep (se 1 (by rfl) ⟨6515528, by rfl⟩ : syracuseStep 8687371 = 13031057) B13031057
theorem B11583161 : Blo 2287435 11583161 := bstep (se 2 (by rfl) ⟨4343685, by rfl⟩ : syracuseStep 11583161 = 8687371) B8687371
theorem B7722107 : Blo 2287435 7722107 := bstep (se 1 (by rfl) ⟨5791580, by rfl⟩ : syracuseStep 7722107 = 11583161) B11583161
theorem B5148071 : Blo 2287435 5148071 := bstep (se 1 (by rfl) ⟨3861053, by rfl⟩ : syracuseStep 5148071 = 7722107) B7722107
theorem B3432047 : Blo 2287435 3432047 := bstep (se 1 (by rfl) ⟨2574035, by rfl⟩ : syracuseStep 3432047 = 5148071) B5148071
theorem B2288031 : Blo 2287435 2288031 := bstep (se 1 (by rfl) ⟨1716023, by rfl⟩ : syracuseStep 2288031 = 3432047) B3432047
theorem B3432053 : Blo 2287435 3432053 := bbase (se 5 (by rfl) ⟨160877, by rfl⟩ : syracuseStep 3432053 = 321755) (by norm_num)
theorem B2288035 : Blo 2287435 2288035 := bstep (se 1 (by rfl) ⟨1716026, by rfl⟩ : syracuseStep 2288035 = 3432053) B3432053
theorem B4343701 : Blo 2287435 4343701 := bbase (se 6 (by rfl) ⟨101805, by rfl⟩ : syracuseStep 4343701 = 203611) (by norm_num)
theorem B5791601 : Blo 2287435 5791601 := bstep (se 2 (by rfl) ⟨2171850, by rfl⟩ : syracuseStep 5791601 = 4343701) B4343701
theorem B3861067 : Blo 2287435 3861067 := bstep (se 1 (by rfl) ⟨2895800, by rfl⟩ : syracuseStep 3861067 = 5791601) B5791601
theorem B5148089 : Blo 2287435 5148089 := bstep (se 2 (by rfl) ⟨1930533, by rfl⟩ : syracuseStep 5148089 = 3861067) B3861067
theorem B3432059 : Blo 2287435 3432059 := bstep (se 1 (by rfl) ⟨2574044, by rfl⟩ : syracuseStep 3432059 = 5148089) B5148089
theorem B2288039 : Blo 2287435 2288039 := bstep (se 1 (by rfl) ⟨1716029, by rfl⟩ : syracuseStep 2288039 = 3432059) B3432059
theorem B2574049 : Blo 2287435 2574049 := bbase (se 2 (by rfl) ⟨965268, by rfl⟩ : syracuseStep 2574049 = 1930537) (by norm_num)
theorem B3432065 : Blo 2287435 3432065 := bstep (se 2 (by rfl) ⟨1287024, by rfl⟩ : syracuseStep 3432065 = 2574049) B2574049
theorem B2288043 : Blo 2287435 2288043 := bstep (se 1 (by rfl) ⟨1716032, by rfl⟩ : syracuseStep 2288043 = 3432065) B3432065
theorem B5791621 : Blo 2287435 5791621 := bbase (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) (by norm_num)
theorem B7722161 : Blo 2287435 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B5148107 : Blo 2287435 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B3432071 : Blo 2287435 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B2288047 : Blo 2287435 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B3432077 : Blo 2287435 3432077 := bbase (se 3 (by rfl) ⟨643514, by rfl⟩ : syracuseStep 3432077 = 1287029) (by norm_num)
theorem B2288051 : Blo 2287435 2288051 := bstep (se 1 (by rfl) ⟨1716038, by rfl⟩ : syracuseStep 2288051 = 3432077) B3432077
theorem B5148125 : Blo 2287435 5148125 := bbase (se 3 (by rfl) ⟨965273, by rfl⟩ : syracuseStep 5148125 = 1930547) (by norm_num)
theorem B3432083 : Blo 2287435 3432083 := bstep (se 1 (by rfl) ⟨2574062, by rfl⟩ : syracuseStep 3432083 = 5148125) B5148125
theorem B2288055 : Blo 2287435 2288055 := bstep (se 1 (by rfl) ⟨1716041, by rfl⟩ : syracuseStep 2288055 = 3432083) B3432083
theorem B3861101 : Blo 2287435 3861101 := bbase (se 3 (by rfl) ⟨723956, by rfl⟩ : syracuseStep 3861101 = 1447913) (by norm_num)
theorem B2574067 : Blo 2287435 2574067 := bstep (se 1 (by rfl) ⟨1930550, by rfl⟩ : syracuseStep 2574067 = 3861101) B3861101
theorem B3432089 : Blo 2287435 3432089 := bstep (se 2 (by rfl) ⟨1287033, by rfl⟩ : syracuseStep 3432089 = 2574067) B2574067
theorem B2288059 : Blo 2287435 2288059 := bstep (se 1 (by rfl) ⟨1716044, by rfl⟩ : syracuseStep 2288059 = 3432089) B3432089
theorem B6604517 : Blo 2287435 6604517 := bbase (se 4 (by rfl) ⟨619173, by rfl⟩ : syracuseStep 6604517 = 1238347) (by norm_num)
theorem B4403011 : Blo 2287435 4403011 := bstep (se 1 (by rfl) ⟨3302258, by rfl⟩ : syracuseStep 4403011 = 6604517) B6604517
theorem B5870681 : Blo 2287435 5870681 := bstep (se 2 (by rfl) ⟨2201505, by rfl⟩ : syracuseStep 5870681 = 4403011) B4403011
theorem B3913787 : Blo 2287435 3913787 := bstep (se 1 (by rfl) ⟨2935340, by rfl⟩ : syracuseStep 3913787 = 5870681) B5870681
theorem B2609191 : Blo 2287435 2609191 := bstep (se 1 (by rfl) ⟨1956893, by rfl⟩ : syracuseStep 2609191 = 3913787) B3913787
theorem B13915685 : Blo 2287435 13915685 := bstep (se 4 (by rfl) ⟨1304595, by rfl⟩ : syracuseStep 13915685 = 2609191) B2609191
theorem B37108493 : Blo 2287435 37108493 := bstep (se 3 (by rfl) ⟨6957842, by rfl⟩ : syracuseStep 37108493 = 13915685) B13915685
theorem B24738995 : Blo 2287435 24738995 := bstep (se 1 (by rfl) ⟨18554246, by rfl⟩ : syracuseStep 24738995 = 37108493) B37108493
theorem B16492663 : Blo 2287435 16492663 := bstep (se 1 (by rfl) ⟨12369497, by rfl⟩ : syracuseStep 16492663 = 24738995) B24738995
theorem B21990217 : Blo 2287435 21990217 := bstep (se 2 (by rfl) ⟨8246331, by rfl⟩ : syracuseStep 21990217 = 16492663) B16492663
theorem B29320289 : Blo 2287435 29320289 := bstep (se 2 (by rfl) ⟨10995108, by rfl⟩ : syracuseStep 29320289 = 21990217) B21990217
theorem B19546859 : Blo 2287435 19546859 := bstep (se 1 (by rfl) ⟨14660144, by rfl⟩ : syracuseStep 19546859 = 29320289) B29320289
theorem B13031239 : Blo 2287435 13031239 := bstep (se 1 (by rfl) ⟨9773429, by rfl⟩ : syracuseStep 13031239 = 19546859) B19546859
theorem B17374985 : Blo 2287435 17374985 := bstep (se 2 (by rfl) ⟨6515619, by rfl⟩ : syracuseStep 17374985 = 13031239) B13031239
theorem B11583323 : Blo 2287435 11583323 := bstep (se 1 (by rfl) ⟨8687492, by rfl⟩ : syracuseStep 11583323 = 17374985) B17374985
theorem B7722215 : Blo 2287435 7722215 := bstep (se 1 (by rfl) ⟨5791661, by rfl⟩ : syracuseStep 7722215 = 11583323) B11583323
theorem B5148143 : Blo 2287435 5148143 := bstep (se 1 (by rfl) ⟨3861107, by rfl⟩ : syracuseStep 5148143 = 7722215) B7722215
theorem B3432095 : Blo 2287435 3432095 := bstep (se 1 (by rfl) ⟨2574071, by rfl⟩ : syracuseStep 3432095 = 5148143) B5148143
theorem B2288063 : Blo 2287435 2288063 := bstep (se 1 (by rfl) ⟨1716047, by rfl⟩ : syracuseStep 2288063 = 3432095) B3432095
theorem B3432101 : Blo 2287435 3432101 := bbase (se 4 (by rfl) ⟨321759, by rfl⟩ : syracuseStep 3432101 = 643519) (by norm_num)
theorem B2288067 : Blo 2287435 2288067 := bstep (se 1 (by rfl) ⟨1716050, by rfl⟩ : syracuseStep 2288067 = 3432101) B3432101
theorem B2895841 : Blo 2287435 2895841 := bbase (se 2 (by rfl) ⟨1085940, by rfl⟩ : syracuseStep 2895841 = 2171881) (by norm_num)
theorem B3861121 : Blo 2287435 3861121 := bstep (se 2 (by rfl) ⟨1447920, by rfl⟩ : syracuseStep 3861121 = 2895841) B2895841
theorem B5148161 : Blo 2287435 5148161 := bstep (se 2 (by rfl) ⟨1930560, by rfl⟩ : syracuseStep 5148161 = 3861121) B3861121
theorem B3432107 : Blo 2287435 3432107 := bstep (se 1 (by rfl) ⟨2574080, by rfl⟩ : syracuseStep 3432107 = 5148161) B5148161
theorem B2288071 : Blo 2287435 2288071 := bstep (se 1 (by rfl) ⟨1716053, by rfl⟩ : syracuseStep 2288071 = 3432107) B3432107
theorem B2574085 : Blo 2287435 2574085 := bbase (se 4 (by rfl) ⟨241320, by rfl⟩ : syracuseStep 2574085 = 482641) (by norm_num)
theorem B3432113 : Blo 2287435 3432113 := bstep (se 2 (by rfl) ⟨1287042, by rfl⟩ : syracuseStep 3432113 = 2574085) B2574085
theorem B2288075 : Blo 2287435 2288075 := bstep (se 1 (by rfl) ⟨1716056, by rfl⟩ : syracuseStep 2288075 = 3432113) B3432113
theorem B11145205 : Blo 2287435 11145205 := bbase (se 5 (by rfl) ⟨522431, by rfl⟩ : syracuseStep 11145205 = 1044863) (by norm_num)
theorem B14860273 : Blo 2287435 14860273 := bstep (se 2 (by rfl) ⟨5572602, by rfl⟩ : syracuseStep 14860273 = 11145205) B11145205
theorem B19813697 : Blo 2287435 19813697 := bstep (se 2 (by rfl) ⟨7430136, by rfl⟩ : syracuseStep 19813697 = 14860273) B14860273
theorem B13209131 : Blo 2287435 13209131 := bstep (se 1 (by rfl) ⟨9906848, by rfl⟩ : syracuseStep 13209131 = 19813697) B19813697
theorem B8806087 : Blo 2287435 8806087 := bstep (se 1 (by rfl) ⟨6604565, by rfl⟩ : syracuseStep 8806087 = 13209131) B13209131
theorem B11741449 : Blo 2287435 11741449 := bstep (se 2 (by rfl) ⟨4403043, by rfl⟩ : syracuseStep 11741449 = 8806087) B8806087
theorem B15655265 : Blo 2287435 15655265 := bstep (se 2 (by rfl) ⟨5870724, by rfl⟩ : syracuseStep 15655265 = 11741449) B11741449
theorem B10436843 : Blo 2287435 10436843 := bstep (se 1 (by rfl) ⟨7827632, by rfl⟩ : syracuseStep 10436843 = 15655265) B15655265
theorem B6957895 : Blo 2287435 6957895 := bstep (se 1 (by rfl) ⟨5218421, by rfl⟩ : syracuseStep 6957895 = 10436843) B10436843
theorem B9277193 : Blo 2287435 9277193 := bstep (se 2 (by rfl) ⟨3478947, by rfl⟩ : syracuseStep 9277193 = 6957895) B6957895
theorem B6184795 : Blo 2287435 6184795 := bstep (se 1 (by rfl) ⟨4638596, by rfl⟩ : syracuseStep 6184795 = 9277193) B9277193
theorem B8246393 : Blo 2287435 8246393 := bstep (se 2 (by rfl) ⟨3092397, by rfl⟩ : syracuseStep 8246393 = 6184795) B6184795
theorem B5497595 : Blo 2287435 5497595 := bstep (se 1 (by rfl) ⟨4123196, by rfl⟩ : syracuseStep 5497595 = 8246393) B8246393
theorem B3665063 : Blo 2287435 3665063 := bstep (se 1 (by rfl) ⟨2748797, by rfl⟩ : syracuseStep 3665063 = 5497595) B5497595
theorem B2443375 : Blo 2287435 2443375 := bstep (se 1 (by rfl) ⟨1832531, by rfl⟩ : syracuseStep 2443375 = 3665063) B3665063
theorem B3257833 : Blo 2287435 3257833 := bstep (se 2 (by rfl) ⟨1221687, by rfl⟩ : syracuseStep 3257833 = 2443375) B2443375
theorem B4343777 : Blo 2287435 4343777 := bstep (se 2 (by rfl) ⟨1628916, by rfl⟩ : syracuseStep 4343777 = 3257833) B3257833
theorem B2895851 : Blo 2287435 2895851 := bstep (se 1 (by rfl) ⟨2171888, by rfl⟩ : syracuseStep 2895851 = 4343777) B4343777
theorem B7722269 : Blo 2287435 7722269 := bstep (se 3 (by rfl) ⟨1447925, by rfl⟩ : syracuseStep 7722269 = 2895851) B2895851
theorem B5148179 : Blo 2287435 5148179 := bstep (se 1 (by rfl) ⟨3861134, by rfl⟩ : syracuseStep 5148179 = 7722269) B7722269
theorem B3432119 : Blo 2287435 3432119 := bstep (se 1 (by rfl) ⟨2574089, by rfl⟩ : syracuseStep 3432119 = 5148179) B5148179
theorem B2288079 : Blo 2287435 2288079 := bstep (se 1 (by rfl) ⟨1716059, by rfl⟩ : syracuseStep 2288079 = 3432119) B3432119
theorem B3432125 : Blo 2287435 3432125 := bbase (se 3 (by rfl) ⟨643523, by rfl⟩ : syracuseStep 3432125 = 1287047) (by norm_num)
theorem B2288083 : Blo 2287435 2288083 := bstep (se 1 (by rfl) ⟨1716062, by rfl⟩ : syracuseStep 2288083 = 3432125) B3432125
theorem B5148197 : Blo 2287435 5148197 := bbase (se 4 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 5148197 = 965287) (by norm_num)
theorem B3432131 : Blo 2287435 3432131 := bstep (se 1 (by rfl) ⟨2574098, by rfl⟩ : syracuseStep 3432131 = 5148197) B5148197
theorem B2288087 : Blo 2287435 2288087 := bstep (se 1 (by rfl) ⟨1716065, by rfl⟩ : syracuseStep 2288087 = 3432131) B3432131
theorem B5791733 : Blo 2287435 5791733 := bbase (se 5 (by rfl) ⟨271487, by rfl⟩ : syracuseStep 5791733 = 542975) (by norm_num)
theorem B3861155 : Blo 2287435 3861155 := bstep (se 1 (by rfl) ⟨2895866, by rfl⟩ : syracuseStep 3861155 = 5791733) B5791733
theorem B2574103 : Blo 2287435 2574103 := bstep (se 1 (by rfl) ⟨1930577, by rfl⟩ : syracuseStep 2574103 = 3861155) B3861155
theorem B3432137 : Blo 2287435 3432137 := bstep (se 2 (by rfl) ⟨1287051, by rfl⟩ : syracuseStep 3432137 = 2574103) B2574103
theorem B2288091 : Blo 2287435 2288091 := bstep (se 1 (by rfl) ⟨1716068, by rfl⟩ : syracuseStep 2288091 = 3432137) B3432137
theorem B5648669 : Blo 2287435 5648669 := bbase (se 3 (by rfl) ⟨1059125, by rfl⟩ : syracuseStep 5648669 = 2118251) (by norm_num)
theorem B3765779 : Blo 2287435 3765779 := bstep (se 1 (by rfl) ⟨2824334, by rfl⟩ : syracuseStep 3765779 = 5648669) B5648669
theorem B2510519 : Blo 2287435 2510519 := bstep (se 1 (by rfl) ⟨1882889, by rfl⟩ : syracuseStep 2510519 = 3765779) B3765779
theorem B6694717 : Blo 2287435 6694717 := bstep (se 3 (by rfl) ⟨1255259, by rfl⟩ : syracuseStep 6694717 = 2510519) B2510519
theorem B8926289 : Blo 2287435 8926289 := bstep (se 2 (by rfl) ⟨3347358, by rfl⟩ : syracuseStep 8926289 = 6694717) B6694717
theorem B5950859 : Blo 2287435 5950859 := bstep (se 1 (by rfl) ⟨4463144, by rfl⟩ : syracuseStep 5950859 = 8926289) B8926289
theorem B15868957 : Blo 2287435 15868957 := bstep (se 3 (by rfl) ⟨2975429, by rfl⟩ : syracuseStep 15868957 = 5950859) B5950859
theorem B21158609 : Blo 2287435 21158609 := bstep (se 2 (by rfl) ⟨7934478, by rfl⟩ : syracuseStep 21158609 = 15868957) B15868957
theorem B225691829 : Blo 2287435 225691829 := bstep (se 5 (by rfl) ⟨10579304, by rfl⟩ : syracuseStep 225691829 = 21158609) B21158609
theorem B150461219 : Blo 2287435 150461219 := bstep (se 1 (by rfl) ⟨112845914, by rfl⟩ : syracuseStep 150461219 = 225691829) B225691829
theorem B100307479 : Blo 2287435 100307479 := bstep (se 1 (by rfl) ⟨75230609, by rfl⟩ : syracuseStep 100307479 = 150461219) B150461219
theorem B133743305 : Blo 2287435 133743305 := bstep (se 2 (by rfl) ⟨50153739, by rfl⟩ : syracuseStep 133743305 = 100307479) B100307479
theorem B89162203 : Blo 2287435 89162203 := bstep (se 1 (by rfl) ⟨66871652, by rfl⟩ : syracuseStep 89162203 = 133743305) B133743305
theorem B118882937 : Blo 2287435 118882937 := bstep (se 2 (by rfl) ⟨44581101, by rfl⟩ : syracuseStep 118882937 = 89162203) B89162203
theorem B317021165 : Blo 2287435 317021165 := bstep (se 3 (by rfl) ⟨59441468, by rfl⟩ : syracuseStep 317021165 = 118882937) B118882937
theorem B211347443 : Blo 2287435 211347443 := bstep (se 1 (by rfl) ⟨158510582, by rfl⟩ : syracuseStep 211347443 = 317021165) B317021165
theorem B140898295 : Blo 2287435 140898295 := bstep (se 1 (by rfl) ⟨105673721, by rfl⟩ : syracuseStep 140898295 = 211347443) B211347443
theorem B187864393 : Blo 2287435 187864393 := bstep (se 2 (by rfl) ⟨70449147, by rfl⟩ : syracuseStep 187864393 = 140898295) B140898295
theorem B250485857 : Blo 2287435 250485857 := bstep (se 2 (by rfl) ⟨93932196, by rfl⟩ : syracuseStep 250485857 = 187864393) B187864393
theorem B166990571 : Blo 2287435 166990571 := bstep (se 1 (by rfl) ⟨125242928, by rfl⟩ : syracuseStep 166990571 = 250485857) B250485857
theorem B111327047 : Blo 2287435 111327047 := bstep (se 1 (by rfl) ⟨83495285, by rfl⟩ : syracuseStep 111327047 = 166990571) B166990571
theorem B74218031 : Blo 2287435 74218031 := bstep (se 1 (by rfl) ⟨55663523, by rfl⟩ : syracuseStep 74218031 = 111327047) B111327047
theorem B49478687 : Blo 2287435 49478687 := bstep (se 1 (by rfl) ⟨37109015, by rfl⟩ : syracuseStep 49478687 = 74218031) B74218031
theorem B32985791 : Blo 2287435 32985791 := bstep (se 1 (by rfl) ⟨24739343, by rfl⟩ : syracuseStep 32985791 = 49478687) B49478687
theorem B21990527 : Blo 2287435 21990527 := bstep (se 1 (by rfl) ⟨16492895, by rfl⟩ : syracuseStep 21990527 = 32985791) B32985791
theorem B14660351 : Blo 2287435 14660351 := bstep (se 1 (by rfl) ⟨10995263, by rfl⟩ : syracuseStep 14660351 = 21990527) B21990527
theorem B9773567 : Blo 2287435 9773567 := bstep (se 1 (by rfl) ⟨7330175, by rfl⟩ : syracuseStep 9773567 = 14660351) B14660351
theorem B6515711 : Blo 2287435 6515711 := bstep (se 1 (by rfl) ⟨4886783, by rfl⟩ : syracuseStep 6515711 = 9773567) B9773567
theorem B4343807 : Blo 2287435 4343807 := bstep (se 1 (by rfl) ⟨3257855, by rfl⟩ : syracuseStep 4343807 = 6515711) B6515711
theorem B11583485 : Blo 2287435 11583485 := bstep (se 3 (by rfl) ⟨2171903, by rfl⟩ : syracuseStep 11583485 = 4343807) B4343807
theorem B7722323 : Blo 2287435 7722323 := bstep (se 1 (by rfl) ⟨5791742, by rfl⟩ : syracuseStep 7722323 = 11583485) B11583485
theorem B5148215 : Blo 2287435 5148215 := bstep (se 1 (by rfl) ⟨3861161, by rfl⟩ : syracuseStep 5148215 = 7722323) B7722323
theorem B3432143 : Blo 2287435 3432143 := bstep (se 1 (by rfl) ⟨2574107, by rfl⟩ : syracuseStep 3432143 = 5148215) B5148215
theorem B2288095 : Blo 2287435 2288095 := bstep (se 1 (by rfl) ⟨1716071, by rfl⟩ : syracuseStep 2288095 = 3432143) B3432143
theorem B3432149 : Blo 2287435 3432149 := bbase (se 7 (by rfl) ⟨40220, by rfl⟩ : syracuseStep 3432149 = 80441) (by norm_num)
theorem B2288099 : Blo 2287435 2288099 := bstep (se 1 (by rfl) ⟨1716074, by rfl⟩ : syracuseStep 2288099 = 3432149) B3432149
theorem B3665101 : Blo 2287435 3665101 := bbase (se 3 (by rfl) ⟨687206, by rfl⟩ : syracuseStep 3665101 = 1374413) (by norm_num)
theorem B4886801 : Blo 2287435 4886801 := bstep (se 2 (by rfl) ⟨1832550, by rfl⟩ : syracuseStep 4886801 = 3665101) B3665101
theorem B3257867 : Blo 2287435 3257867 := bstep (se 1 (by rfl) ⟨2443400, by rfl⟩ : syracuseStep 3257867 = 4886801) B4886801
theorem B8687645 : Blo 2287435 8687645 := bstep (se 3 (by rfl) ⟨1628933, by rfl⟩ : syracuseStep 8687645 = 3257867) B3257867
theorem B5791763 : Blo 2287435 5791763 := bstep (se 1 (by rfl) ⟨4343822, by rfl⟩ : syracuseStep 5791763 = 8687645) B8687645
theorem B3861175 : Blo 2287435 3861175 := bstep (se 1 (by rfl) ⟨2895881, by rfl⟩ : syracuseStep 3861175 = 5791763) B5791763
theorem B5148233 : Blo 2287435 5148233 := bstep (se 2 (by rfl) ⟨1930587, by rfl⟩ : syracuseStep 5148233 = 3861175) B3861175
theorem B3432155 : Blo 2287435 3432155 := bstep (se 1 (by rfl) ⟨2574116, by rfl⟩ : syracuseStep 3432155 = 5148233) B5148233
theorem B2288103 : Blo 2287435 2288103 := bstep (se 1 (by rfl) ⟨1716077, by rfl⟩ : syracuseStep 2288103 = 3432155) B3432155
theorem B2574121 : Blo 2287435 2574121 := bbase (se 2 (by rfl) ⟨965295, by rfl⟩ : syracuseStep 2574121 = 1930591) (by norm_num)
theorem B3432161 : Blo 2287435 3432161 := bstep (se 2 (by rfl) ⟨1287060, by rfl⟩ : syracuseStep 3432161 = 2574121) B2574121
theorem B2288107 : Blo 2287435 2288107 := bstep (se 1 (by rfl) ⟨1716080, by rfl⟩ : syracuseStep 2288107 = 3432161) B3432161
theorem B4123253 : Blo 2287435 4123253 := bbase (se 5 (by rfl) ⟨193277, by rfl⟩ : syracuseStep 4123253 = 386555) (by norm_num)
theorem B2748835 : Blo 2287435 2748835 := bstep (se 1 (by rfl) ⟨2061626, by rfl⟩ : syracuseStep 2748835 = 4123253) B4123253
theorem B14660453 : Blo 2287435 14660453 := bstep (se 4 (by rfl) ⟨1374417, by rfl⟩ : syracuseStep 14660453 = 2748835) B2748835
theorem B9773635 : Blo 2287435 9773635 := bstep (se 1 (by rfl) ⟨7330226, by rfl⟩ : syracuseStep 9773635 = 14660453) B14660453
theorem B13031513 : Blo 2287435 13031513 := bstep (se 2 (by rfl) ⟨4886817, by rfl⟩ : syracuseStep 13031513 = 9773635) B9773635
theorem B8687675 : Blo 2287435 8687675 := bstep (se 1 (by rfl) ⟨6515756, by rfl⟩ : syracuseStep 8687675 = 13031513) B13031513
theorem B5791783 : Blo 2287435 5791783 := bstep (se 1 (by rfl) ⟨4343837, by rfl⟩ : syracuseStep 5791783 = 8687675) B8687675
theorem B7722377 : Blo 2287435 7722377 := bstep (se 2 (by rfl) ⟨2895891, by rfl⟩ : syracuseStep 7722377 = 5791783) B5791783
theorem B5148251 : Blo 2287435 5148251 := bstep (se 1 (by rfl) ⟨3861188, by rfl⟩ : syracuseStep 5148251 = 7722377) B7722377
theorem B3432167 : Blo 2287435 3432167 := bstep (se 1 (by rfl) ⟨2574125, by rfl⟩ : syracuseStep 3432167 = 5148251) B5148251
theorem B2288111 : Blo 2287435 2288111 := bstep (se 1 (by rfl) ⟨1716083, by rfl⟩ : syracuseStep 2288111 = 3432167) B3432167
theorem B3432173 : Blo 2287435 3432173 := bbase (se 3 (by rfl) ⟨643532, by rfl⟩ : syracuseStep 3432173 = 1287065) (by norm_num)
theorem B2288115 : Blo 2287435 2288115 := bstep (se 1 (by rfl) ⟨1716086, by rfl⟩ : syracuseStep 2288115 = 3432173) B3432173
theorem B5148269 : Blo 2287435 5148269 := bbase (se 3 (by rfl) ⟨965300, by rfl⟩ : syracuseStep 5148269 = 1930601) (by norm_num)
theorem B3432179 : Blo 2287435 3432179 := bstep (se 1 (by rfl) ⟨2574134, by rfl⟩ : syracuseStep 3432179 = 5148269) B5148269
theorem B2288119 : Blo 2287435 2288119 := bstep (se 1 (by rfl) ⟨1716089, by rfl⟩ : syracuseStep 2288119 = 3432179) B3432179
theorem B4343861 : Blo 2287435 4343861 := bbase (se 5 (by rfl) ⟨203618, by rfl⟩ : syracuseStep 4343861 = 407237) (by norm_num)
theorem B2895907 : Blo 2287435 2895907 := bstep (se 1 (by rfl) ⟨2171930, by rfl⟩ : syracuseStep 2895907 = 4343861) B4343861
theorem B3861209 : Blo 2287435 3861209 := bstep (se 2 (by rfl) ⟨1447953, by rfl⟩ : syracuseStep 3861209 = 2895907) B2895907
theorem B2574139 : Blo 2287435 2574139 := bstep (se 1 (by rfl) ⟨1930604, by rfl⟩ : syracuseStep 2574139 = 3861209) B3861209
theorem B3432185 : Blo 2287435 3432185 := bstep (se 2 (by rfl) ⟨1287069, by rfl⟩ : syracuseStep 3432185 = 2574139) B2574139
theorem B2288123 : Blo 2287435 2288123 := bstep (se 1 (by rfl) ⟨1716092, by rfl⟩ : syracuseStep 2288123 = 3432185) B3432185
theorem B9403957 : Blo 2287435 9403957 := bbase (se 5 (by rfl) ⟨440810, by rfl⟩ : syracuseStep 9403957 = 881621) (by norm_num)
theorem B50154437 : Blo 2287435 50154437 := bstep (se 4 (by rfl) ⟨4701978, by rfl⟩ : syracuseStep 50154437 = 9403957) B9403957
theorem B133745165 : Blo 2287435 133745165 := bstep (se 3 (by rfl) ⟨25077218, by rfl⟩ : syracuseStep 133745165 = 50154437) B50154437
theorem B89163443 : Blo 2287435 89163443 := bstep (se 1 (by rfl) ⟨66872582, by rfl⟩ : syracuseStep 89163443 = 133745165) B133745165
theorem B59442295 : Blo 2287435 59442295 := bstep (se 1 (by rfl) ⟨44581721, by rfl⟩ : syracuseStep 59442295 = 89163443) B89163443
theorem B79256393 : Blo 2287435 79256393 := bstep (se 2 (by rfl) ⟨29721147, by rfl⟩ : syracuseStep 79256393 = 59442295) B59442295
theorem B52837595 : Blo 2287435 52837595 := bstep (se 1 (by rfl) ⟨39628196, by rfl⟩ : syracuseStep 52837595 = 79256393) B79256393
theorem B35225063 : Blo 2287435 35225063 := bstep (se 1 (by rfl) ⟨26418797, by rfl⟩ : syracuseStep 35225063 = 52837595) B52837595
theorem B23483375 : Blo 2287435 23483375 := bstep (se 1 (by rfl) ⟨17612531, by rfl⟩ : syracuseStep 23483375 = 35225063) B35225063
theorem B15655583 : Blo 2287435 15655583 := bstep (se 1 (by rfl) ⟨11741687, by rfl⟩ : syracuseStep 15655583 = 23483375) B23483375
theorem B10437055 : Blo 2287435 10437055 := bstep (se 1 (by rfl) ⟨7827791, by rfl⟩ : syracuseStep 10437055 = 15655583) B15655583
theorem B222657173 : Blo 2287435 222657173 := bstep (se 6 (by rfl) ⟨5218527, by rfl⟩ : syracuseStep 222657173 = 10437055) B10437055
theorem B148438115 : Blo 2287435 148438115 := bstep (se 1 (by rfl) ⟨111328586, by rfl⟩ : syracuseStep 148438115 = 222657173) B222657173
theorem B98958743 : Blo 2287435 98958743 := bstep (se 1 (by rfl) ⟨74219057, by rfl⟩ : syracuseStep 98958743 = 148438115) B148438115
theorem B65972495 : Blo 2287435 65972495 := bstep (se 1 (by rfl) ⟨49479371, by rfl⟩ : syracuseStep 65972495 = 98958743) B98958743
theorem B43981663 : Blo 2287435 43981663 := bstep (se 1 (by rfl) ⟨32986247, by rfl⟩ : syracuseStep 43981663 = 65972495) B65972495
theorem B58642217 : Blo 2287435 58642217 := bstep (se 2 (by rfl) ⟨21990831, by rfl⟩ : syracuseStep 58642217 = 43981663) B43981663
theorem B39094811 : Blo 2287435 39094811 := bstep (se 1 (by rfl) ⟨29321108, by rfl⟩ : syracuseStep 39094811 = 58642217) B58642217
theorem B26063207 : Blo 2287435 26063207 := bstep (se 1 (by rfl) ⟨19547405, by rfl⟩ : syracuseStep 26063207 = 39094811) B39094811
theorem B17375471 : Blo 2287435 17375471 := bstep (se 1 (by rfl) ⟨13031603, by rfl⟩ : syracuseStep 17375471 = 26063207) B26063207
theorem B11583647 : Blo 2287435 11583647 := bstep (se 1 (by rfl) ⟨8687735, by rfl⟩ : syracuseStep 11583647 = 17375471) B17375471
theorem B7722431 : Blo 2287435 7722431 := bstep (se 1 (by rfl) ⟨5791823, by rfl⟩ : syracuseStep 7722431 = 11583647) B11583647
theorem B5148287 : Blo 2287435 5148287 := bstep (se 1 (by rfl) ⟨3861215, by rfl⟩ : syracuseStep 5148287 = 7722431) B7722431
theorem B3432191 : Blo 2287435 3432191 := bstep (se 1 (by rfl) ⟨2574143, by rfl⟩ : syracuseStep 3432191 = 5148287) B5148287
theorem B2288127 : Blo 2287435 2288127 := bstep (se 1 (by rfl) ⟨1716095, by rfl⟩ : syracuseStep 2288127 = 3432191) B3432191
theorem B3432197 : Blo 2287435 3432197 := bbase (se 4 (by rfl) ⟨321768, by rfl⟩ : syracuseStep 3432197 = 643537) (by norm_num)
theorem B2288131 : Blo 2287435 2288131 := bstep (se 1 (by rfl) ⟨1716098, by rfl⟩ : syracuseStep 2288131 = 3432197) B3432197
theorem B3861229 : Blo 2287435 3861229 := bbase (se 3 (by rfl) ⟨723980, by rfl⟩ : syracuseStep 3861229 = 1447961) (by norm_num)
theorem B5148305 : Blo 2287435 5148305 := bstep (se 2 (by rfl) ⟨1930614, by rfl⟩ : syracuseStep 5148305 = 3861229) B3861229
theorem B3432203 : Blo 2287435 3432203 := bstep (se 1 (by rfl) ⟨2574152, by rfl⟩ : syracuseStep 3432203 = 5148305) B5148305
theorem B2288135 : Blo 2287435 2288135 := bstep (se 1 (by rfl) ⟨1716101, by rfl⟩ : syracuseStep 2288135 = 3432203) B3432203
theorem B2574157 : Blo 2287435 2574157 := bbase (se 3 (by rfl) ⟨482654, by rfl⟩ : syracuseStep 2574157 = 965309) (by norm_num)
theorem B3432209 : Blo 2287435 3432209 := bstep (se 2 (by rfl) ⟨1287078, by rfl⟩ : syracuseStep 3432209 = 2574157) B2574157
theorem B2288139 : Blo 2287435 2288139 := bstep (se 1 (by rfl) ⟨1716104, by rfl⟩ : syracuseStep 2288139 = 3432209) B3432209
theorem B7722485 : Blo 2287435 7722485 := bbase (se 5 (by rfl) ⟨361991, by rfl⟩ : syracuseStep 7722485 = 723983) (by norm_num)
theorem B5148323 : Blo 2287435 5148323 := bstep (se 1 (by rfl) ⟨3861242, by rfl⟩ : syracuseStep 5148323 = 7722485) B7722485
theorem B3432215 : Blo 2287435 3432215 := bstep (se 1 (by rfl) ⟨2574161, by rfl⟩ : syracuseStep 3432215 = 5148323) B5148323
theorem B2288143 : Blo 2287435 2288143 := bstep (se 1 (by rfl) ⟨1716107, by rfl⟩ : syracuseStep 2288143 = 3432215) B3432215
theorem B3432221 : Blo 2287435 3432221 := bbase (se 3 (by rfl) ⟨643541, by rfl⟩ : syracuseStep 3432221 = 1287083) (by norm_num)
theorem B2288147 : Blo 2287435 2288147 := bstep (se 1 (by rfl) ⟨1716110, by rfl⟩ : syracuseStep 2288147 = 3432221) B3432221
theorem B5148341 : Blo 2287435 5148341 := bbase (se 5 (by rfl) ⟨241328, by rfl⟩ : syracuseStep 5148341 = 482657) (by norm_num)
theorem B3432227 : Blo 2287435 3432227 := bstep (se 1 (by rfl) ⟨2574170, by rfl⟩ : syracuseStep 3432227 = 5148341) B5148341
theorem B2288151 : Blo 2287435 2288151 := bstep (se 1 (by rfl) ⟨1716113, by rfl⟩ : syracuseStep 2288151 = 3432227) B3432227
theorem B13031765 : Blo 2287435 13031765 := bbase (se 10 (by rfl) ⟨19089, by rfl⟩ : syracuseStep 13031765 = 38179) (by norm_num)
theorem B8687843 : Blo 2287435 8687843 := bstep (se 1 (by rfl) ⟨6515882, by rfl⟩ : syracuseStep 8687843 = 13031765) B13031765
theorem B5791895 : Blo 2287435 5791895 := bstep (se 1 (by rfl) ⟨4343921, by rfl⟩ : syracuseStep 5791895 = 8687843) B8687843
theorem B3861263 : Blo 2287435 3861263 := bstep (se 1 (by rfl) ⟨2895947, by rfl⟩ : syracuseStep 3861263 = 5791895) B5791895
theorem B2574175 : Blo 2287435 2574175 := bstep (se 1 (by rfl) ⟨1930631, by rfl⟩ : syracuseStep 2574175 = 3861263) B3861263
theorem B3432233 : Blo 2287435 3432233 := bstep (se 2 (by rfl) ⟨1287087, by rfl⟩ : syracuseStep 3432233 = 2574175) B2574175
theorem B2288155 : Blo 2287435 2288155 := bstep (se 1 (by rfl) ⟨1716116, by rfl⟩ : syracuseStep 2288155 = 3432233) B3432233
theorem B6515893 : Blo 2287435 6515893 := bbase (se 5 (by rfl) ⟨305432, by rfl⟩ : syracuseStep 6515893 = 610865) (by norm_num)
theorem B8687857 : Blo 2287435 8687857 := bstep (se 2 (by rfl) ⟨3257946, by rfl⟩ : syracuseStep 8687857 = 6515893) B6515893
theorem B11583809 : Blo 2287435 11583809 := bstep (se 2 (by rfl) ⟨4343928, by rfl⟩ : syracuseStep 11583809 = 8687857) B8687857
theorem B7722539 : Blo 2287435 7722539 := bstep (se 1 (by rfl) ⟨5791904, by rfl⟩ : syracuseStep 7722539 = 11583809) B11583809
theorem B5148359 : Blo 2287435 5148359 := bstep (se 1 (by rfl) ⟨3861269, by rfl⟩ : syracuseStep 5148359 = 7722539) B7722539
theorem B3432239 : Blo 2287435 3432239 := bstep (se 1 (by rfl) ⟨2574179, by rfl⟩ : syracuseStep 3432239 = 5148359) B5148359
theorem B2288159 : Blo 2287435 2288159 := bstep (se 1 (by rfl) ⟨1716119, by rfl⟩ : syracuseStep 2288159 = 3432239) B3432239
theorem B3432245 : Blo 2287435 3432245 := bbase (se 5 (by rfl) ⟨160886, by rfl⟩ : syracuseStep 3432245 = 321773) (by norm_num)
theorem B2288163 : Blo 2287435 2288163 := bstep (se 1 (by rfl) ⟨1716122, by rfl⟩ : syracuseStep 2288163 = 3432245) B3432245
theorem B5791925 : Blo 2287435 5791925 := bbase (se 5 (by rfl) ⟨271496, by rfl⟩ : syracuseStep 5791925 = 542993) (by norm_num)
theorem B3861283 : Blo 2287435 3861283 := bstep (se 1 (by rfl) ⟨2895962, by rfl⟩ : syracuseStep 3861283 = 5791925) B5791925
theorem B5148377 : Blo 2287435 5148377 := bstep (se 2 (by rfl) ⟨1930641, by rfl⟩ : syracuseStep 5148377 = 3861283) B3861283
theorem B3432251 : Blo 2287435 3432251 := bstep (se 1 (by rfl) ⟨2574188, by rfl⟩ : syracuseStep 3432251 = 5148377) B5148377
theorem B2288167 : Blo 2287435 2288167 := bstep (se 1 (by rfl) ⟨1716125, by rfl⟩ : syracuseStep 2288167 = 3432251) B3432251
theorem B2574193 : Blo 2287435 2574193 := bbase (se 2 (by rfl) ⟨965322, by rfl⟩ : syracuseStep 2574193 = 1930645) (by norm_num)
theorem B3432257 : Blo 2287435 3432257 := bstep (se 2 (by rfl) ⟨1287096, by rfl⟩ : syracuseStep 3432257 = 2574193) B2574193
theorem B2288171 : Blo 2287435 2288171 := bstep (se 1 (by rfl) ⟨1716128, by rfl⟩ : syracuseStep 2288171 = 3432257) B3432257
theorem B9773909 : Blo 2287435 9773909 := bbase (se 9 (by rfl) ⟨28634, by rfl⟩ : syracuseStep 9773909 = 57269) (by norm_num)
theorem B6515939 : Blo 2287435 6515939 := bstep (se 1 (by rfl) ⟨4886954, by rfl⟩ : syracuseStep 6515939 = 9773909) B9773909
theorem B4343959 : Blo 2287435 4343959 := bstep (se 1 (by rfl) ⟨3257969, by rfl⟩ : syracuseStep 4343959 = 6515939) B6515939
theorem B5791945 : Blo 2287435 5791945 := bstep (se 2 (by rfl) ⟨2171979, by rfl⟩ : syracuseStep 5791945 = 4343959) B4343959
theorem B7722593 : Blo 2287435 7722593 := bstep (se 2 (by rfl) ⟨2895972, by rfl⟩ : syracuseStep 7722593 = 5791945) B5791945
theorem B5148395 : Blo 2287435 5148395 := bstep (se 1 (by rfl) ⟨3861296, by rfl⟩ : syracuseStep 5148395 = 7722593) B7722593
theorem B3432263 : Blo 2287435 3432263 := bstep (se 1 (by rfl) ⟨2574197, by rfl⟩ : syracuseStep 3432263 = 5148395) B5148395
theorem B2288175 : Blo 2287435 2288175 := bstep (se 1 (by rfl) ⟨1716131, by rfl⟩ : syracuseStep 2288175 = 3432263) B3432263
theorem B3432269 : Blo 2287435 3432269 := bbase (se 3 (by rfl) ⟨643550, by rfl⟩ : syracuseStep 3432269 = 1287101) (by norm_num)
theorem B2288179 : Blo 2287435 2288179 := bstep (se 1 (by rfl) ⟨1716134, by rfl⟩ : syracuseStep 2288179 = 3432269) B3432269
theorem B5148413 : Blo 2287435 5148413 := bbase (se 3 (by rfl) ⟨965327, by rfl⟩ : syracuseStep 5148413 = 1930655) (by norm_num)
theorem B3432275 : Blo 2287435 3432275 := bstep (se 1 (by rfl) ⟨2574206, by rfl⟩ : syracuseStep 3432275 = 5148413) B5148413
theorem B2288183 : Blo 2287435 2288183 := bstep (se 1 (by rfl) ⟨1716137, by rfl⟩ : syracuseStep 2288183 = 3432275) B3432275
theorem B3861317 : Blo 2287435 3861317 := bbase (se 4 (by rfl) ⟨361998, by rfl⟩ : syracuseStep 3861317 = 723997) (by norm_num)
theorem B2574211 : Blo 2287435 2574211 := bstep (se 1 (by rfl) ⟨1930658, by rfl⟩ : syracuseStep 2574211 = 3861317) B3861317
theorem B3432281 : Blo 2287435 3432281 := bstep (se 2 (by rfl) ⟨1287105, by rfl⟩ : syracuseStep 3432281 = 2574211) B2574211
theorem B2288187 : Blo 2287435 2288187 := bstep (se 1 (by rfl) ⟨1716140, by rfl⟩ : syracuseStep 2288187 = 3432281) B3432281
theorem B17375957 : Blo 2287435 17375957 := bbase (se 7 (by rfl) ⟨203624, by rfl⟩ : syracuseStep 17375957 = 407249) (by norm_num)
theorem B11583971 : Blo 2287435 11583971 := bstep (se 1 (by rfl) ⟨8687978, by rfl⟩ : syracuseStep 11583971 = 17375957) B17375957
theorem B7722647 : Blo 2287435 7722647 := bstep (se 1 (by rfl) ⟨5791985, by rfl⟩ : syracuseStep 7722647 = 11583971) B11583971
theorem B5148431 : Blo 2287435 5148431 := bstep (se 1 (by rfl) ⟨3861323, by rfl⟩ : syracuseStep 5148431 = 7722647) B7722647
theorem B3432287 : Blo 2287435 3432287 := bstep (se 1 (by rfl) ⟨2574215, by rfl⟩ : syracuseStep 3432287 = 5148431) B5148431
theorem B2288191 : Blo 2287435 2288191 := bstep (se 1 (by rfl) ⟨1716143, by rfl⟩ : syracuseStep 2288191 = 3432287) B3432287
theorem B3432293 : Blo 2287435 3432293 := bbase (se 4 (by rfl) ⟨321777, by rfl⟩ : syracuseStep 3432293 = 643555) (by norm_num)
theorem B2288195 : Blo 2287435 2288195 := bstep (se 1 (by rfl) ⟨1716146, by rfl⟩ : syracuseStep 2288195 = 3432293) B3432293
theorem B4344005 : Blo 2287435 4344005 := bbase (se 4 (by rfl) ⟨407250, by rfl⟩ : syracuseStep 4344005 = 814501) (by norm_num)
theorem B2896003 : Blo 2287435 2896003 := bstep (se 1 (by rfl) ⟨2172002, by rfl⟩ : syracuseStep 2896003 = 4344005) B4344005
theorem B3861337 : Blo 2287435 3861337 := bstep (se 2 (by rfl) ⟨1448001, by rfl⟩ : syracuseStep 3861337 = 2896003) B2896003
theorem B5148449 : Blo 2287435 5148449 := bstep (se 2 (by rfl) ⟨1930668, by rfl⟩ : syracuseStep 5148449 = 3861337) B3861337
theorem B3432299 : Blo 2287435 3432299 := bstep (se 1 (by rfl) ⟨2574224, by rfl⟩ : syracuseStep 3432299 = 5148449) B5148449
theorem B2288199 : Blo 2287435 2288199 := bstep (se 1 (by rfl) ⟨1716149, by rfl⟩ : syracuseStep 2288199 = 3432299) B3432299
theorem B2574229 : Blo 2287435 2574229 := bbase (se 6 (by rfl) ⟨60333, by rfl⟩ : syracuseStep 2574229 = 120667) (by norm_num)
theorem B3432305 : Blo 2287435 3432305 := bstep (se 2 (by rfl) ⟨1287114, by rfl⟩ : syracuseStep 3432305 = 2574229) B2574229
theorem B2288203 : Blo 2287435 2288203 := bstep (se 1 (by rfl) ⟨1716152, by rfl⟩ : syracuseStep 2288203 = 3432305) B3432305
theorem B2896013 : Blo 2287435 2896013 := bbase (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) (by norm_num)
theorem B7722701 : Blo 2287435 7722701 := bstep (se 3 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 7722701 = 2896013) B2896013
theorem B5148467 : Blo 2287435 5148467 := bstep (se 1 (by rfl) ⟨3861350, by rfl⟩ : syracuseStep 5148467 = 7722701) B7722701
theorem B3432311 : Blo 2287435 3432311 := bstep (se 1 (by rfl) ⟨2574233, by rfl⟩ : syracuseStep 3432311 = 5148467) B5148467
theorem B2288207 : Blo 2287435 2288207 := bstep (se 1 (by rfl) ⟨1716155, by rfl⟩ : syracuseStep 2288207 = 3432311) B3432311
theorem B3432317 : Blo 2287435 3432317 := bbase (se 3 (by rfl) ⟨643559, by rfl⟩ : syracuseStep 3432317 = 1287119) (by norm_num)
theorem B2288211 : Blo 2287435 2288211 := bstep (se 1 (by rfl) ⟨1716158, by rfl⟩ : syracuseStep 2288211 = 3432317) B3432317
theorem B5148485 : Blo 2287435 5148485 := bbase (se 4 (by rfl) ⟨482670, by rfl⟩ : syracuseStep 5148485 = 965341) (by norm_num)
theorem B3432323 : Blo 2287435 3432323 := bstep (se 1 (by rfl) ⟨2574242, by rfl⟩ : syracuseStep 3432323 = 5148485) B5148485
theorem B2288215 : Blo 2287435 2288215 := bstep (se 1 (by rfl) ⟨1716161, by rfl⟩ : syracuseStep 2288215 = 3432323) B3432323
theorem B6185173 : Blo 2287435 6185173 := bbase (se 7 (by rfl) ⟨72482, by rfl⟩ : syracuseStep 6185173 = 144965) (by norm_num)
theorem B8246897 : Blo 2287435 8246897 := bstep (se 2 (by rfl) ⟨3092586, by rfl⟩ : syracuseStep 8246897 = 6185173) B6185173
theorem B5497931 : Blo 2287435 5497931 := bstep (se 1 (by rfl) ⟨4123448, by rfl⟩ : syracuseStep 5497931 = 8246897) B8246897
theorem B3665287 : Blo 2287435 3665287 := bstep (se 1 (by rfl) ⟨2748965, by rfl⟩ : syracuseStep 3665287 = 5497931) B5497931
theorem B4887049 : Blo 2287435 4887049 := bstep (se 2 (by rfl) ⟨1832643, by rfl⟩ : syracuseStep 4887049 = 3665287) B3665287
theorem B6516065 : Blo 2287435 6516065 := bstep (se 2 (by rfl) ⟨2443524, by rfl⟩ : syracuseStep 6516065 = 4887049) B4887049
theorem B4344043 : Blo 2287435 4344043 := bstep (se 1 (by rfl) ⟨3258032, by rfl⟩ : syracuseStep 4344043 = 6516065) B6516065
theorem B5792057 : Blo 2287435 5792057 := bstep (se 2 (by rfl) ⟨2172021, by rfl⟩ : syracuseStep 5792057 = 4344043) B4344043
theorem B3861371 : Blo 2287435 3861371 := bstep (se 1 (by rfl) ⟨2896028, by rfl⟩ : syracuseStep 3861371 = 5792057) B5792057
theorem B2574247 : Blo 2287435 2574247 := bstep (se 1 (by rfl) ⟨1930685, by rfl⟩ : syracuseStep 2574247 = 3861371) B3861371
theorem B3432329 : Blo 2287435 3432329 := bstep (se 2 (by rfl) ⟨1287123, by rfl⟩ : syracuseStep 3432329 = 2574247) B2574247
theorem B2288219 : Blo 2287435 2288219 := bstep (se 1 (by rfl) ⟨1716164, by rfl⟩ : syracuseStep 2288219 = 3432329) B3432329
theorem B11584133 : Blo 2287435 11584133 := bbase (se 4 (by rfl) ⟨1086012, by rfl⟩ : syracuseStep 11584133 = 2172025) (by norm_num)
theorem B7722755 : Blo 2287435 7722755 := bstep (se 1 (by rfl) ⟨5792066, by rfl⟩ : syracuseStep 7722755 = 11584133) B11584133
theorem B5148503 : Blo 2287435 5148503 := bstep (se 1 (by rfl) ⟨3861377, by rfl⟩ : syracuseStep 5148503 = 7722755) B7722755
theorem B3432335 : Blo 2287435 3432335 := bstep (se 1 (by rfl) ⟨2574251, by rfl⟩ : syracuseStep 3432335 = 5148503) B5148503
theorem B2288223 : Blo 2287435 2288223 := bstep (se 1 (by rfl) ⟨1716167, by rfl⟩ : syracuseStep 2288223 = 3432335) B3432335
theorem B3432341 : Blo 2287435 3432341 := bbase (se 6 (by rfl) ⟨80445, by rfl⟩ : syracuseStep 3432341 = 160891) (by norm_num)
theorem B2288227 : Blo 2287435 2288227 := bstep (se 1 (by rfl) ⟨1716170, by rfl⟩ : syracuseStep 2288227 = 3432341) B3432341
theorem B2443537 : Blo 2287435 2443537 := bbase (se 2 (by rfl) ⟨916326, by rfl⟩ : syracuseStep 2443537 = 1832653) (by norm_num)
theorem B13032197 : Blo 2287435 13032197 := bstep (se 4 (by rfl) ⟨1221768, by rfl⟩ : syracuseStep 13032197 = 2443537) B2443537
theorem B8688131 : Blo 2287435 8688131 := bstep (se 1 (by rfl) ⟨6516098, by rfl⟩ : syracuseStep 8688131 = 13032197) B13032197
theorem B5792087 : Blo 2287435 5792087 := bstep (se 1 (by rfl) ⟨4344065, by rfl⟩ : syracuseStep 5792087 = 8688131) B8688131
theorem B3861391 : Blo 2287435 3861391 := bstep (se 1 (by rfl) ⟨2896043, by rfl⟩ : syracuseStep 3861391 = 5792087) B5792087
theorem B5148521 : Blo 2287435 5148521 := bstep (se 2 (by rfl) ⟨1930695, by rfl⟩ : syracuseStep 5148521 = 3861391) B3861391
theorem B3432347 : Blo 2287435 3432347 := bstep (se 1 (by rfl) ⟨2574260, by rfl⟩ : syracuseStep 3432347 = 5148521) B5148521
theorem B2288231 : Blo 2287435 2288231 := bstep (se 1 (by rfl) ⟨1716173, by rfl⟩ : syracuseStep 2288231 = 3432347) B3432347
theorem B2574265 : Blo 2287435 2574265 := bbase (se 2 (by rfl) ⟨965349, by rfl⟩ : syracuseStep 2574265 = 1930699) (by norm_num)
theorem B3432353 : Blo 2287435 3432353 := bstep (se 2 (by rfl) ⟨1287132, by rfl⟩ : syracuseStep 3432353 = 2574265) B2574265
theorem B2288235 : Blo 2287435 2288235 := bstep (se 1 (by rfl) ⟨1716176, by rfl⟩ : syracuseStep 2288235 = 3432353) B3432353
theorem B2748989 : Blo 2287435 2748989 := bbase (se 3 (by rfl) ⟨515435, by rfl⟩ : syracuseStep 2748989 = 1030871) (by norm_num)
theorem B7330637 : Blo 2287435 7330637 := bstep (se 3 (by rfl) ⟨1374494, by rfl⟩ : syracuseStep 7330637 = 2748989) B2748989
theorem B4887091 : Blo 2287435 4887091 := bstep (se 1 (by rfl) ⟨3665318, by rfl⟩ : syracuseStep 4887091 = 7330637) B7330637
theorem B6516121 : Blo 2287435 6516121 := bstep (se 2 (by rfl) ⟨2443545, by rfl⟩ : syracuseStep 6516121 = 4887091) B4887091
theorem B8688161 : Blo 2287435 8688161 := bstep (se 2 (by rfl) ⟨3258060, by rfl⟩ : syracuseStep 8688161 = 6516121) B6516121
theorem B5792107 : Blo 2287435 5792107 := bstep (se 1 (by rfl) ⟨4344080, by rfl⟩ : syracuseStep 5792107 = 8688161) B8688161
theorem B7722809 : Blo 2287435 7722809 := bstep (se 2 (by rfl) ⟨2896053, by rfl⟩ : syracuseStep 7722809 = 5792107) B5792107
theorem B5148539 : Blo 2287435 5148539 := bstep (se 1 (by rfl) ⟨3861404, by rfl⟩ : syracuseStep 5148539 = 7722809) B7722809
theorem B3432359 : Blo 2287435 3432359 := bstep (se 1 (by rfl) ⟨2574269, by rfl⟩ : syracuseStep 3432359 = 5148539) B5148539
theorem B2288239 : Blo 2287435 2288239 := bstep (se 1 (by rfl) ⟨1716179, by rfl⟩ : syracuseStep 2288239 = 3432359) B3432359
theorem B3432365 : Blo 2287435 3432365 := bbase (se 3 (by rfl) ⟨643568, by rfl⟩ : syracuseStep 3432365 = 1287137) (by norm_num)
theorem B2288243 : Blo 2287435 2288243 := bstep (se 1 (by rfl) ⟨1716182, by rfl⟩ : syracuseStep 2288243 = 3432365) B3432365
theorem B5148557 : Blo 2287435 5148557 := bbase (se 3 (by rfl) ⟨965354, by rfl⟩ : syracuseStep 5148557 = 1930709) (by norm_num)
theorem B3432371 : Blo 2287435 3432371 := bstep (se 1 (by rfl) ⟨2574278, by rfl⟩ : syracuseStep 3432371 = 5148557) B5148557
theorem B2288247 : Blo 2287435 2288247 := bstep (se 1 (by rfl) ⟨1716185, by rfl⟩ : syracuseStep 2288247 = 3432371) B3432371
theorem B2896069 : Blo 2287435 2896069 := bbase (se 4 (by rfl) ⟨271506, by rfl⟩ : syracuseStep 2896069 = 543013) (by norm_num)
theorem B3861425 : Blo 2287435 3861425 := bstep (se 2 (by rfl) ⟨1448034, by rfl⟩ : syracuseStep 3861425 = 2896069) B2896069
theorem B2574283 : Blo 2287435 2574283 := bstep (se 1 (by rfl) ⟨1930712, by rfl⟩ : syracuseStep 2574283 = 3861425) B3861425
theorem B3432377 : Blo 2287435 3432377 := bstep (se 2 (by rfl) ⟨1287141, by rfl⟩ : syracuseStep 3432377 = 2574283) B2574283
theorem B2288251 : Blo 2287435 2288251 := bstep (se 1 (by rfl) ⟨1716188, by rfl⟩ : syracuseStep 2288251 = 3432377) B3432377
theorem B2476901 : Blo 2287435 2476901 := bbase (se 4 (by rfl) ⟨232209, by rfl⟩ : syracuseStep 2476901 = 464419) (by norm_num)
theorem B6605069 : Blo 2287435 6605069 := bstep (se 3 (by rfl) ⟨1238450, by rfl⟩ : syracuseStep 6605069 = 2476901) B2476901
theorem B70454069 : Blo 2287435 70454069 := bstep (se 5 (by rfl) ⟨3302534, by rfl⟩ : syracuseStep 70454069 = 6605069) B6605069
theorem B46969379 : Blo 2287435 46969379 := bstep (se 1 (by rfl) ⟨35227034, by rfl⟩ : syracuseStep 46969379 = 70454069) B70454069
theorem B31312919 : Blo 2287435 31312919 := bstep (se 1 (by rfl) ⟨23484689, by rfl⟩ : syracuseStep 31312919 = 46969379) B46969379
theorem B83501117 : Blo 2287435 83501117 := bstep (se 3 (by rfl) ⟨15656459, by rfl⟩ : syracuseStep 83501117 = 31312919) B31312919
theorem B55667411 : Blo 2287435 55667411 := bstep (se 1 (by rfl) ⟨41750558, by rfl⟩ : syracuseStep 55667411 = 83501117) B83501117
theorem B37111607 : Blo 2287435 37111607 := bstep (se 1 (by rfl) ⟨27833705, by rfl⟩ : syracuseStep 37111607 = 55667411) B55667411
theorem B24741071 : Blo 2287435 24741071 := bstep (se 1 (by rfl) ⟨18555803, by rfl⟩ : syracuseStep 24741071 = 37111607) B37111607
theorem B16494047 : Blo 2287435 16494047 := bstep (se 1 (by rfl) ⟨12370535, by rfl⟩ : syracuseStep 16494047 = 24741071) B24741071
theorem B10996031 : Blo 2287435 10996031 := bstep (se 1 (by rfl) ⟨8247023, by rfl⟩ : syracuseStep 10996031 = 16494047) B16494047
theorem B29322749 : Blo 2287435 29322749 := bstep (se 3 (by rfl) ⟨5498015, by rfl⟩ : syracuseStep 29322749 = 10996031) B10996031
theorem B19548499 : Blo 2287435 19548499 := bstep (se 1 (by rfl) ⟨14661374, by rfl⟩ : syracuseStep 19548499 = 29322749) B29322749
theorem B26064665 : Blo 2287435 26064665 := bstep (se 2 (by rfl) ⟨9774249, by rfl⟩ : syracuseStep 26064665 = 19548499) B19548499
theorem B17376443 : Blo 2287435 17376443 := bstep (se 1 (by rfl) ⟨13032332, by rfl⟩ : syracuseStep 17376443 = 26064665) B26064665
theorem B11584295 : Blo 2287435 11584295 := bstep (se 1 (by rfl) ⟨8688221, by rfl⟩ : syracuseStep 11584295 = 17376443) B17376443
theorem B7722863 : Blo 2287435 7722863 := bstep (se 1 (by rfl) ⟨5792147, by rfl⟩ : syracuseStep 7722863 = 11584295) B11584295
theorem B5148575 : Blo 2287435 5148575 := bstep (se 1 (by rfl) ⟨3861431, by rfl⟩ : syracuseStep 5148575 = 7722863) B7722863
theorem B3432383 : Blo 2287435 3432383 := bstep (se 1 (by rfl) ⟨2574287, by rfl⟩ : syracuseStep 3432383 = 5148575) B5148575
theorem B2288255 : Blo 2287435 2288255 := bstep (se 1 (by rfl) ⟨1716191, by rfl⟩ : syracuseStep 2288255 = 3432383) B3432383
theorem B3432389 : Blo 2287435 3432389 := bbase (se 4 (by rfl) ⟨321786, by rfl⟩ : syracuseStep 3432389 = 643573) (by norm_num)
theorem B2288259 : Blo 2287435 2288259 := bstep (se 1 (by rfl) ⟨1716194, by rfl⟩ : syracuseStep 2288259 = 3432389) B3432389
theorem B3861445 : Blo 2287435 3861445 := bbase (se 4 (by rfl) ⟨362010, by rfl⟩ : syracuseStep 3861445 = 724021) (by norm_num)
theorem B5148593 : Blo 2287435 5148593 := bstep (se 2 (by rfl) ⟨1930722, by rfl⟩ : syracuseStep 5148593 = 3861445) B3861445
theorem B3432395 : Blo 2287435 3432395 := bstep (se 1 (by rfl) ⟨2574296, by rfl⟩ : syracuseStep 3432395 = 5148593) B5148593
theorem B2288263 : Blo 2287435 2288263 := bstep (se 1 (by rfl) ⟨1716197, by rfl⟩ : syracuseStep 2288263 = 3432395) B3432395
theorem B2574301 : Blo 2287435 2574301 := bbase (se 3 (by rfl) ⟨482681, by rfl⟩ : syracuseStep 2574301 = 965363) (by norm_num)
theorem B3432401 : Blo 2287435 3432401 := bstep (se 2 (by rfl) ⟨1287150, by rfl⟩ : syracuseStep 3432401 = 2574301) B2574301
theorem B2288267 : Blo 2287435 2288267 := bstep (se 1 (by rfl) ⟨1716200, by rfl⟩ : syracuseStep 2288267 = 3432401) B3432401
theorem B7722917 : Blo 2287435 7722917 := bbase (se 4 (by rfl) ⟨724023, by rfl⟩ : syracuseStep 7722917 = 1448047) (by norm_num)
theorem B5148611 : Blo 2287435 5148611 := bstep (se 1 (by rfl) ⟨3861458, by rfl⟩ : syracuseStep 5148611 = 7722917) B7722917
theorem B3432407 : Blo 2287435 3432407 := bstep (se 1 (by rfl) ⟨2574305, by rfl⟩ : syracuseStep 3432407 = 5148611) B5148611
theorem B2288271 : Blo 2287435 2288271 := bstep (se 1 (by rfl) ⟨1716203, by rfl⟩ : syracuseStep 2288271 = 3432407) B3432407
theorem B3432413 : Blo 2287435 3432413 := bbase (se 3 (by rfl) ⟨643577, by rfl⟩ : syracuseStep 3432413 = 1287155) (by norm_num)
theorem B2288275 : Blo 2287435 2288275 := bstep (se 1 (by rfl) ⟨1716206, by rfl⟩ : syracuseStep 2288275 = 3432413) B3432413
theorem B5148629 : Blo 2287435 5148629 := bbase (se 7 (by rfl) ⟨60335, by rfl⟩ : syracuseStep 5148629 = 120671) (by norm_num)
theorem B3432419 : Blo 2287435 3432419 := bstep (se 1 (by rfl) ⟨2574314, by rfl⟩ : syracuseStep 3432419 = 5148629) B5148629
theorem B2288279 : Blo 2287435 2288279 := bstep (se 1 (by rfl) ⟨1716209, by rfl⟩ : syracuseStep 2288279 = 3432419) B3432419
theorem B14661557 : Blo 2287435 14661557 := bbase (se 5 (by rfl) ⟨687260, by rfl⟩ : syracuseStep 14661557 = 1374521) (by norm_num)
theorem B9774371 : Blo 2287435 9774371 := bstep (se 1 (by rfl) ⟨7330778, by rfl⟩ : syracuseStep 9774371 = 14661557) B14661557
theorem B6516247 : Blo 2287435 6516247 := bstep (se 1 (by rfl) ⟨4887185, by rfl⟩ : syracuseStep 6516247 = 9774371) B9774371
theorem B8688329 : Blo 2287435 8688329 := bstep (se 2 (by rfl) ⟨3258123, by rfl⟩ : syracuseStep 8688329 = 6516247) B6516247
theorem B5792219 : Blo 2287435 5792219 := bstep (se 1 (by rfl) ⟨4344164, by rfl⟩ : syracuseStep 5792219 = 8688329) B8688329
theorem B3861479 : Blo 2287435 3861479 := bstep (se 1 (by rfl) ⟨2896109, by rfl⟩ : syracuseStep 3861479 = 5792219) B5792219
theorem B2574319 : Blo 2287435 2574319 := bstep (se 1 (by rfl) ⟨1930739, by rfl⟩ : syracuseStep 2574319 = 3861479) B3861479
theorem B3432425 : Blo 2287435 3432425 := bstep (se 2 (by rfl) ⟨1287159, by rfl⟩ : syracuseStep 3432425 = 2574319) B2574319
theorem B2288283 : Blo 2287435 2288283 := bstep (se 1 (by rfl) ⟨1716212, by rfl⟩ : syracuseStep 2288283 = 3432425) B3432425
theorem B5498093 : Blo 2287435 5498093 := bbase (se 3 (by rfl) ⟨1030892, by rfl⟩ : syracuseStep 5498093 = 2061785) (by norm_num)
theorem B3665395 : Blo 2287435 3665395 := bstep (se 1 (by rfl) ⟨2749046, by rfl⟩ : syracuseStep 3665395 = 5498093) B5498093
theorem B19548773 : Blo 2287435 19548773 := bstep (se 4 (by rfl) ⟨1832697, by rfl⟩ : syracuseStep 19548773 = 3665395) B3665395
theorem B13032515 : Blo 2287435 13032515 := bstep (se 1 (by rfl) ⟨9774386, by rfl⟩ : syracuseStep 13032515 = 19548773) B19548773
theorem B8688343 : Blo 2287435 8688343 := bstep (se 1 (by rfl) ⟨6516257, by rfl⟩ : syracuseStep 8688343 = 13032515) B13032515
theorem B11584457 : Blo 2287435 11584457 := bstep (se 2 (by rfl) ⟨4344171, by rfl⟩ : syracuseStep 11584457 = 8688343) B8688343
theorem B7722971 : Blo 2287435 7722971 := bstep (se 1 (by rfl) ⟨5792228, by rfl⟩ : syracuseStep 7722971 = 11584457) B11584457
theorem B5148647 : Blo 2287435 5148647 := bstep (se 1 (by rfl) ⟨3861485, by rfl⟩ : syracuseStep 5148647 = 7722971) B7722971
theorem B3432431 : Blo 2287435 3432431 := bstep (se 1 (by rfl) ⟨2574323, by rfl⟩ : syracuseStep 3432431 = 5148647) B5148647
theorem B2288287 : Blo 2287435 2288287 := bstep (se 1 (by rfl) ⟨1716215, by rfl⟩ : syracuseStep 2288287 = 3432431) B3432431
theorem B3432437 : Blo 2287435 3432437 := bbase (se 5 (by rfl) ⟨160895, by rfl⟩ : syracuseStep 3432437 = 321791) (by norm_num)
theorem B2288291 : Blo 2287435 2288291 := bstep (se 1 (by rfl) ⟨1716218, by rfl⟩ : syracuseStep 2288291 = 3432437) B3432437
theorem B2319517 : Blo 2287435 2319517 := bbase (se 3 (by rfl) ⟨434909, by rfl⟩ : syracuseStep 2319517 = 869819) (by norm_num)
theorem B3092689 : Blo 2287435 3092689 := bstep (se 2 (by rfl) ⟨1159758, by rfl⟩ : syracuseStep 3092689 = 2319517) B2319517
theorem B4123585 : Blo 2287435 4123585 := bstep (se 2 (by rfl) ⟨1546344, by rfl⟩ : syracuseStep 4123585 = 3092689) B3092689
theorem B5498113 : Blo 2287435 5498113 := bstep (se 2 (by rfl) ⟨2061792, by rfl⟩ : syracuseStep 5498113 = 4123585) B4123585
theorem B7330817 : Blo 2287435 7330817 := bstep (se 2 (by rfl) ⟨2749056, by rfl⟩ : syracuseStep 7330817 = 5498113) B5498113
theorem B4887211 : Blo 2287435 4887211 := bstep (se 1 (by rfl) ⟨3665408, by rfl⟩ : syracuseStep 4887211 = 7330817) B7330817
theorem B6516281 : Blo 2287435 6516281 := bstep (se 2 (by rfl) ⟨2443605, by rfl⟩ : syracuseStep 6516281 = 4887211) B4887211
theorem B4344187 : Blo 2287435 4344187 := bstep (se 1 (by rfl) ⟨3258140, by rfl⟩ : syracuseStep 4344187 = 6516281) B6516281
theorem B5792249 : Blo 2287435 5792249 := bstep (se 2 (by rfl) ⟨2172093, by rfl⟩ : syracuseStep 5792249 = 4344187) B4344187
theorem B3861499 : Blo 2287435 3861499 := bstep (se 1 (by rfl) ⟨2896124, by rfl⟩ : syracuseStep 3861499 = 5792249) B5792249
theorem B5148665 : Blo 2287435 5148665 := bstep (se 2 (by rfl) ⟨1930749, by rfl⟩ : syracuseStep 5148665 = 3861499) B3861499
theorem B3432443 : Blo 2287435 3432443 := bstep (se 1 (by rfl) ⟨2574332, by rfl⟩ : syracuseStep 3432443 = 5148665) B5148665
theorem B2288295 : Blo 2287435 2288295 := bstep (se 1 (by rfl) ⟨1716221, by rfl⟩ : syracuseStep 2288295 = 3432443) B3432443
theorem B2574337 : Blo 2287435 2574337 := bbase (se 2 (by rfl) ⟨965376, by rfl⟩ : syracuseStep 2574337 = 1930753) (by norm_num)
theorem B3432449 : Blo 2287435 3432449 := bstep (se 2 (by rfl) ⟨1287168, by rfl⟩ : syracuseStep 3432449 = 2574337) B2574337
theorem B2288299 : Blo 2287435 2288299 := bstep (se 1 (by rfl) ⟨1716224, by rfl⟩ : syracuseStep 2288299 = 3432449) B3432449
theorem B5792269 : Blo 2287435 5792269 := bbase (se 3 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 5792269 = 2172101) (by norm_num)
theorem B7723025 : Blo 2287435 7723025 := bstep (se 2 (by rfl) ⟨2896134, by rfl⟩ : syracuseStep 7723025 = 5792269) B5792269
theorem B5148683 : Blo 2287435 5148683 := bstep (se 1 (by rfl) ⟨3861512, by rfl⟩ : syracuseStep 5148683 = 7723025) B7723025
theorem B3432455 : Blo 2287435 3432455 := bstep (se 1 (by rfl) ⟨2574341, by rfl⟩ : syracuseStep 3432455 = 5148683) B5148683
theorem B2288303 : Blo 2287435 2288303 := bstep (se 1 (by rfl) ⟨1716227, by rfl⟩ : syracuseStep 2288303 = 3432455) B3432455
theorem B3432461 : Blo 2287435 3432461 := bbase (se 3 (by rfl) ⟨643586, by rfl⟩ : syracuseStep 3432461 = 1287173) (by norm_num)
theorem B2288307 : Blo 2287435 2288307 := bstep (se 1 (by rfl) ⟨1716230, by rfl⟩ : syracuseStep 2288307 = 3432461) B3432461
theorem B5148701 : Blo 2287435 5148701 := bbase (se 3 (by rfl) ⟨965381, by rfl⟩ : syracuseStep 5148701 = 1930763) (by norm_num)
theorem B3432467 : Blo 2287435 3432467 := bstep (se 1 (by rfl) ⟨2574350, by rfl⟩ : syracuseStep 3432467 = 5148701) B5148701
theorem B2288311 : Blo 2287435 2288311 := bstep (se 1 (by rfl) ⟨1716233, by rfl⟩ : syracuseStep 2288311 = 3432467) B3432467
theorem B3861533 : Blo 2287435 3861533 := bbase (se 3 (by rfl) ⟨724037, by rfl⟩ : syracuseStep 3861533 = 1448075) (by norm_num)
theorem B2574355 : Blo 2287435 2574355 := bstep (se 1 (by rfl) ⟨1930766, by rfl⟩ : syracuseStep 2574355 = 3861533) B3861533
theorem B3432473 : Blo 2287435 3432473 := bstep (se 2 (by rfl) ⟨1287177, by rfl⟩ : syracuseStep 3432473 = 2574355) B2574355
theorem B2288315 : Blo 2287435 2288315 := bstep (se 1 (by rfl) ⟨1716236, by rfl⟩ : syracuseStep 2288315 = 3432473) B3432473
theorem B11742677 : Blo 2287435 11742677 := bbase (se 7 (by rfl) ⟨137609, by rfl⟩ : syracuseStep 11742677 = 275219) (by norm_num)
theorem B7828451 : Blo 2287435 7828451 := bstep (se 1 (by rfl) ⟨5871338, by rfl⟩ : syracuseStep 7828451 = 11742677) B11742677
theorem B5218967 : Blo 2287435 5218967 := bstep (se 1 (by rfl) ⟨3914225, by rfl⟩ : syracuseStep 5218967 = 7828451) B7828451
theorem B3479311 : Blo 2287435 3479311 := bstep (se 1 (by rfl) ⟨2609483, by rfl⟩ : syracuseStep 3479311 = 5218967) B5218967
theorem B4639081 : Blo 2287435 4639081 := bstep (se 2 (by rfl) ⟨1739655, by rfl⟩ : syracuseStep 4639081 = 3479311) B3479311
theorem B6185441 : Blo 2287435 6185441 := bstep (se 2 (by rfl) ⟨2319540, by rfl⟩ : syracuseStep 6185441 = 4639081) B4639081
theorem B16494509 : Blo 2287435 16494509 := bstep (se 3 (by rfl) ⟨3092720, by rfl⟩ : syracuseStep 16494509 = 6185441) B6185441
theorem B10996339 : Blo 2287435 10996339 := bstep (se 1 (by rfl) ⟨8247254, by rfl⟩ : syracuseStep 10996339 = 16494509) B16494509
theorem B14661785 : Blo 2287435 14661785 := bstep (se 2 (by rfl) ⟨5498169, by rfl⟩ : syracuseStep 14661785 = 10996339) B10996339
theorem B9774523 : Blo 2287435 9774523 := bstep (se 1 (by rfl) ⟨7330892, by rfl⟩ : syracuseStep 9774523 = 14661785) B14661785
theorem B13032697 : Blo 2287435 13032697 := bstep (se 2 (by rfl) ⟨4887261, by rfl⟩ : syracuseStep 13032697 = 9774523) B9774523
theorem B17376929 : Blo 2287435 17376929 := bstep (se 2 (by rfl) ⟨6516348, by rfl⟩ : syracuseStep 17376929 = 13032697) B13032697
theorem B11584619 : Blo 2287435 11584619 := bstep (se 1 (by rfl) ⟨8688464, by rfl⟩ : syracuseStep 11584619 = 17376929) B17376929
theorem B7723079 : Blo 2287435 7723079 := bstep (se 1 (by rfl) ⟨5792309, by rfl⟩ : syracuseStep 7723079 = 11584619) B11584619
theorem B5148719 : Blo 2287435 5148719 := bstep (se 1 (by rfl) ⟨3861539, by rfl⟩ : syracuseStep 5148719 = 7723079) B7723079
theorem B3432479 : Blo 2287435 3432479 := bstep (se 1 (by rfl) ⟨2574359, by rfl⟩ : syracuseStep 3432479 = 5148719) B5148719
theorem B2288319 : Blo 2287435 2288319 := bstep (se 1 (by rfl) ⟨1716239, by rfl⟩ : syracuseStep 2288319 = 3432479) B3432479
theorem B3432485 : Blo 2287435 3432485 := bbase (se 4 (by rfl) ⟨321795, by rfl⟩ : syracuseStep 3432485 = 643591) (by norm_num)
theorem B2288323 : Blo 2287435 2288323 := bstep (se 1 (by rfl) ⟨1716242, by rfl⟩ : syracuseStep 2288323 = 3432485) B3432485
theorem B2896165 : Blo 2287435 2896165 := bbase (se 4 (by rfl) ⟨271515, by rfl⟩ : syracuseStep 2896165 = 543031) (by norm_num)
theorem B3861553 : Blo 2287435 3861553 := bstep (se 2 (by rfl) ⟨1448082, by rfl⟩ : syracuseStep 3861553 = 2896165) B2896165
theorem B5148737 : Blo 2287435 5148737 := bstep (se 2 (by rfl) ⟨1930776, by rfl⟩ : syracuseStep 5148737 = 3861553) B3861553
theorem B3432491 : Blo 2287435 3432491 := bstep (se 1 (by rfl) ⟨2574368, by rfl⟩ : syracuseStep 3432491 = 5148737) B5148737
theorem B2288327 : Blo 2287435 2288327 := bstep (se 1 (by rfl) ⟨1716245, by rfl⟩ : syracuseStep 2288327 = 3432491) B3432491
theorem B2574373 : Blo 2287435 2574373 := bbase (se 4 (by rfl) ⟨241347, by rfl⟩ : syracuseStep 2574373 = 482695) (by norm_num)
theorem B3432497 : Blo 2287435 3432497 := bstep (se 2 (by rfl) ⟨1287186, by rfl⟩ : syracuseStep 3432497 = 2574373) B2574373
theorem B2288331 : Blo 2287435 2288331 := bstep (se 1 (by rfl) ⟨1716248, by rfl⟩ : syracuseStep 2288331 = 3432497) B3432497
theorem B5219005 : Blo 2287435 5219005 := bbase (se 3 (by rfl) ⟨978563, by rfl⟩ : syracuseStep 5219005 = 1957127) (by norm_num)
theorem B6958673 : Blo 2287435 6958673 := bstep (se 2 (by rfl) ⟨2609502, by rfl⟩ : syracuseStep 6958673 = 5219005) B5219005
theorem B4639115 : Blo 2287435 4639115 := bstep (se 1 (by rfl) ⟨3479336, by rfl⟩ : syracuseStep 4639115 = 6958673) B6958673
theorem B3092743 : Blo 2287435 3092743 := bstep (se 1 (by rfl) ⟨2319557, by rfl⟩ : syracuseStep 3092743 = 4639115) B4639115
theorem B4123657 : Blo 2287435 4123657 := bstep (se 2 (by rfl) ⟨1546371, by rfl⟩ : syracuseStep 4123657 = 3092743) B3092743
theorem B5498209 : Blo 2287435 5498209 := bstep (se 2 (by rfl) ⟨2061828, by rfl⟩ : syracuseStep 5498209 = 4123657) B4123657
theorem B7330945 : Blo 2287435 7330945 := bstep (se 2 (by rfl) ⟨2749104, by rfl⟩ : syracuseStep 7330945 = 5498209) B5498209
theorem B9774593 : Blo 2287435 9774593 := bstep (se 2 (by rfl) ⟨3665472, by rfl⟩ : syracuseStep 9774593 = 7330945) B7330945
theorem B6516395 : Blo 2287435 6516395 := bstep (se 1 (by rfl) ⟨4887296, by rfl⟩ : syracuseStep 6516395 = 9774593) B9774593
theorem B4344263 : Blo 2287435 4344263 := bstep (se 1 (by rfl) ⟨3258197, by rfl⟩ : syracuseStep 4344263 = 6516395) B6516395
theorem B2896175 : Blo 2287435 2896175 := bstep (se 1 (by rfl) ⟨2172131, by rfl⟩ : syracuseStep 2896175 = 4344263) B4344263
theorem B7723133 : Blo 2287435 7723133 := bstep (se 3 (by rfl) ⟨1448087, by rfl⟩ : syracuseStep 7723133 = 2896175) B2896175
theorem B5148755 : Blo 2287435 5148755 := bstep (se 1 (by rfl) ⟨3861566, by rfl⟩ : syracuseStep 5148755 = 7723133) B7723133
theorem B3432503 : Blo 2287435 3432503 := bstep (se 1 (by rfl) ⟨2574377, by rfl⟩ : syracuseStep 3432503 = 5148755) B5148755
theorem B2288335 : Blo 2287435 2288335 := bstep (se 1 (by rfl) ⟨1716251, by rfl⟩ : syracuseStep 2288335 = 3432503) B3432503
theorem B3432509 : Blo 2287435 3432509 := bbase (se 3 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 3432509 = 1287191) (by norm_num)
theorem B2288339 : Blo 2287435 2288339 := bstep (se 1 (by rfl) ⟨1716254, by rfl⟩ : syracuseStep 2288339 = 3432509) B3432509
theorem B5148773 : Blo 2287435 5148773 := bbase (se 4 (by rfl) ⟨482697, by rfl⟩ : syracuseStep 5148773 = 965395) (by norm_num)
theorem B3432515 : Blo 2287435 3432515 := bstep (se 1 (by rfl) ⟨2574386, by rfl⟩ : syracuseStep 3432515 = 5148773) B5148773
theorem B2288343 : Blo 2287435 2288343 := bstep (se 1 (by rfl) ⟨1716257, by rfl⟩ : syracuseStep 2288343 = 3432515) B3432515
theorem B5792381 : Blo 2287435 5792381 := bbase (se 3 (by rfl) ⟨1086071, by rfl⟩ : syracuseStep 5792381 = 2172143) (by norm_num)
theorem B3861587 : Blo 2287435 3861587 := bstep (se 1 (by rfl) ⟨2896190, by rfl⟩ : syracuseStep 3861587 = 5792381) B5792381
theorem B2574391 : Blo 2287435 2574391 := bstep (se 1 (by rfl) ⟨1930793, by rfl⟩ : syracuseStep 2574391 = 3861587) B3861587
theorem B3432521 : Blo 2287435 3432521 := bstep (se 2 (by rfl) ⟨1287195, by rfl⟩ : syracuseStep 3432521 = 2574391) B2574391
theorem B2288347 : Blo 2287435 2288347 := bstep (se 1 (by rfl) ⟨1716260, by rfl⟩ : syracuseStep 2288347 = 3432521) B3432521
theorem B4344293 : Blo 2287435 4344293 := bbase (se 4 (by rfl) ⟨407277, by rfl⟩ : syracuseStep 4344293 = 814555) (by norm_num)
theorem B11584781 : Blo 2287435 11584781 := bstep (se 3 (by rfl) ⟨2172146, by rfl⟩ : syracuseStep 11584781 = 4344293) B4344293
theorem B7723187 : Blo 2287435 7723187 := bstep (se 1 (by rfl) ⟨5792390, by rfl⟩ : syracuseStep 7723187 = 11584781) B11584781
theorem B5148791 : Blo 2287435 5148791 := bstep (se 1 (by rfl) ⟨3861593, by rfl⟩ : syracuseStep 5148791 = 7723187) B7723187
theorem B3432527 : Blo 2287435 3432527 := bstep (se 1 (by rfl) ⟨2574395, by rfl⟩ : syracuseStep 3432527 = 5148791) B5148791
theorem B2288351 : Blo 2287435 2288351 := bstep (se 1 (by rfl) ⟨1716263, by rfl⟩ : syracuseStep 2288351 = 3432527) B3432527
theorem B3432533 : Blo 2287435 3432533 := bbase (se 8 (by rfl) ⟨20112, by rfl⟩ : syracuseStep 3432533 = 40225) (by norm_num)
theorem B2288355 : Blo 2287435 2288355 := bstep (se 1 (by rfl) ⟨1716266, by rfl⟩ : syracuseStep 2288355 = 3432533) B3432533
theorem B2681221 : Blo 2287435 2681221 := bbase (se 4 (by rfl) ⟨251364, by rfl⟩ : syracuseStep 2681221 = 502729) (by norm_num)
theorem B3574961 : Blo 2287435 3574961 := bstep (se 2 (by rfl) ⟨1340610, by rfl⟩ : syracuseStep 3574961 = 2681221) B2681221
theorem B2383307 : Blo 2287435 2383307 := bstep (se 1 (by rfl) ⟨1787480, by rfl⟩ : syracuseStep 2383307 = 3574961) B3574961
theorem B25421941 : Blo 2287435 25421941 := bstep (se 5 (by rfl) ⟨1191653, by rfl⟩ : syracuseStep 25421941 = 2383307) B2383307
theorem B33895921 : Blo 2287435 33895921 := bstep (se 2 (by rfl) ⟨12710970, by rfl⟩ : syracuseStep 33895921 = 25421941) B25421941
theorem B45194561 : Blo 2287435 45194561 := bstep (se 2 (by rfl) ⟨16947960, by rfl⟩ : syracuseStep 45194561 = 33895921) B33895921
theorem B30129707 : Blo 2287435 30129707 := bstep (se 1 (by rfl) ⟨22597280, by rfl⟩ : syracuseStep 30129707 = 45194561) B45194561
theorem B20086471 : Blo 2287435 20086471 := bstep (se 1 (by rfl) ⟨15064853, by rfl⟩ : syracuseStep 20086471 = 30129707) B30129707
theorem B26781961 : Blo 2287435 26781961 := bstep (se 2 (by rfl) ⟨10043235, by rfl⟩ : syracuseStep 26781961 = 20086471) B20086471
theorem B35709281 : Blo 2287435 35709281 := bstep (se 2 (by rfl) ⟨13390980, by rfl⟩ : syracuseStep 35709281 = 26781961) B26781961
theorem B23806187 : Blo 2287435 23806187 := bstep (se 1 (by rfl) ⟨17854640, by rfl⟩ : syracuseStep 23806187 = 35709281) B35709281
theorem B15870791 : Blo 2287435 15870791 := bstep (se 1 (by rfl) ⟨11903093, by rfl⟩ : syracuseStep 15870791 = 23806187) B23806187
theorem B10580527 : Blo 2287435 10580527 := bstep (se 1 (by rfl) ⟨7935395, by rfl⟩ : syracuseStep 10580527 = 15870791) B15870791
theorem B14107369 : Blo 2287435 14107369 := bstep (se 2 (by rfl) ⟨5290263, by rfl⟩ : syracuseStep 14107369 = 10580527) B10580527
theorem B18809825 : Blo 2287435 18809825 := bstep (se 2 (by rfl) ⟨7053684, by rfl⟩ : syracuseStep 18809825 = 14107369) B14107369
theorem B50159533 : Blo 2287435 50159533 := bstep (se 3 (by rfl) ⟨9404912, by rfl⟩ : syracuseStep 50159533 = 18809825) B18809825
theorem B66879377 : Blo 2287435 66879377 := bstep (se 2 (by rfl) ⟨25079766, by rfl⟩ : syracuseStep 66879377 = 50159533) B50159533
theorem B44586251 : Blo 2287435 44586251 := bstep (se 1 (by rfl) ⟨33439688, by rfl⟩ : syracuseStep 44586251 = 66879377) B66879377
theorem B29724167 : Blo 2287435 29724167 := bstep (se 1 (by rfl) ⟨22293125, by rfl⟩ : syracuseStep 29724167 = 44586251) B44586251
theorem B19816111 : Blo 2287435 19816111 := bstep (se 1 (by rfl) ⟨14862083, by rfl⟩ : syracuseStep 19816111 = 29724167) B29724167
theorem B26421481 : Blo 2287435 26421481 := bstep (se 2 (by rfl) ⟨9908055, by rfl⟩ : syracuseStep 26421481 = 19816111) B19816111
theorem B35228641 : Blo 2287435 35228641 := bstep (se 2 (by rfl) ⟨13210740, by rfl⟩ : syracuseStep 35228641 = 26421481) B26421481
theorem B46971521 : Blo 2287435 46971521 := bstep (se 2 (by rfl) ⟨17614320, by rfl⟩ : syracuseStep 46971521 = 35228641) B35228641
theorem B31314347 : Blo 2287435 31314347 := bstep (se 1 (by rfl) ⟨23485760, by rfl⟩ : syracuseStep 31314347 = 46971521) B46971521
theorem B20876231 : Blo 2287435 20876231 := bstep (se 1 (by rfl) ⟨15657173, by rfl⟩ : syracuseStep 20876231 = 31314347) B31314347
theorem B55669949 : Blo 2287435 55669949 := bstep (se 3 (by rfl) ⟨10438115, by rfl⟩ : syracuseStep 55669949 = 20876231) B20876231
theorem B37113299 : Blo 2287435 37113299 := bstep (se 1 (by rfl) ⟨27834974, by rfl⟩ : syracuseStep 37113299 = 55669949) B55669949
theorem B24742199 : Blo 2287435 24742199 := bstep (se 1 (by rfl) ⟨18556649, by rfl⟩ : syracuseStep 24742199 = 37113299) B37113299
theorem B16494799 : Blo 2287435 16494799 := bstep (se 1 (by rfl) ⟨12371099, by rfl⟩ : syracuseStep 16494799 = 24742199) B24742199
theorem B21993065 : Blo 2287435 21993065 := bstep (se 2 (by rfl) ⟨8247399, by rfl⟩ : syracuseStep 21993065 = 16494799) B16494799
theorem B14662043 : Blo 2287435 14662043 := bstep (se 1 (by rfl) ⟨10996532, by rfl⟩ : syracuseStep 14662043 = 21993065) B21993065
theorem B9774695 : Blo 2287435 9774695 := bstep (se 1 (by rfl) ⟨7331021, by rfl⟩ : syracuseStep 9774695 = 14662043) B14662043
theorem B6516463 : Blo 2287435 6516463 := bstep (se 1 (by rfl) ⟨4887347, by rfl⟩ : syracuseStep 6516463 = 9774695) B9774695
theorem B8688617 : Blo 2287435 8688617 := bstep (se 2 (by rfl) ⟨3258231, by rfl⟩ : syracuseStep 8688617 = 6516463) B6516463
theorem B5792411 : Blo 2287435 5792411 := bstep (se 1 (by rfl) ⟨4344308, by rfl⟩ : syracuseStep 5792411 = 8688617) B8688617
theorem B3861607 : Blo 2287435 3861607 := bstep (se 1 (by rfl) ⟨2896205, by rfl⟩ : syracuseStep 3861607 = 5792411) B5792411
theorem B5148809 : Blo 2287435 5148809 := bstep (se 2 (by rfl) ⟨1930803, by rfl⟩ : syracuseStep 5148809 = 3861607) B3861607
theorem B3432539 : Blo 2287435 3432539 := bstep (se 1 (by rfl) ⟨2574404, by rfl⟩ : syracuseStep 3432539 = 5148809) B5148809
theorem B2288359 : Blo 2287435 2288359 := bstep (se 1 (by rfl) ⟨1716269, by rfl⟩ : syracuseStep 2288359 = 3432539) B3432539
theorem B2574409 : Blo 2287435 2574409 := bbase (se 2 (by rfl) ⟨965403, by rfl⟩ : syracuseStep 2574409 = 1930807) (by norm_num)
theorem B3432545 : Blo 2287435 3432545 := bstep (se 2 (by rfl) ⟨1287204, by rfl⟩ : syracuseStep 3432545 = 2574409) B2574409
theorem B2288363 : Blo 2287435 2288363 := bstep (se 1 (by rfl) ⟨1716272, by rfl⟩ : syracuseStep 2288363 = 3432545) B3432545
theorem B5498285 : Blo 2287435 5498285 := bbase (se 3 (by rfl) ⟨1030928, by rfl⟩ : syracuseStep 5498285 = 2061857) (by norm_num)
theorem B14662093 : Blo 2287435 14662093 := bstep (se 3 (by rfl) ⟨2749142, by rfl⟩ : syracuseStep 14662093 = 5498285) B5498285
theorem B19549457 : Blo 2287435 19549457 := bstep (se 2 (by rfl) ⟨7331046, by rfl⟩ : syracuseStep 19549457 = 14662093) B14662093
theorem B13032971 : Blo 2287435 13032971 := bstep (se 1 (by rfl) ⟨9774728, by rfl⟩ : syracuseStep 13032971 = 19549457) B19549457
theorem B8688647 : Blo 2287435 8688647 := bstep (se 1 (by rfl) ⟨6516485, by rfl⟩ : syracuseStep 8688647 = 13032971) B13032971
theorem B5792431 : Blo 2287435 5792431 := bstep (se 1 (by rfl) ⟨4344323, by rfl⟩ : syracuseStep 5792431 = 8688647) B8688647
theorem B7723241 : Blo 2287435 7723241 := bstep (se 2 (by rfl) ⟨2896215, by rfl⟩ : syracuseStep 7723241 = 5792431) B5792431
theorem B5148827 : Blo 2287435 5148827 := bstep (se 1 (by rfl) ⟨3861620, by rfl⟩ : syracuseStep 5148827 = 7723241) B7723241
theorem B3432551 : Blo 2287435 3432551 := bstep (se 1 (by rfl) ⟨2574413, by rfl⟩ : syracuseStep 3432551 = 5148827) B5148827
theorem B2288367 : Blo 2287435 2288367 := bstep (se 1 (by rfl) ⟨1716275, by rfl⟩ : syracuseStep 2288367 = 3432551) B3432551
theorem B3432557 : Blo 2287435 3432557 := bbase (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) (by norm_num)
theorem B2288371 : Blo 2287435 2288371 := bstep (se 1 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 2288371 = 3432557) B3432557
theorem B5148845 : Blo 2287435 5148845 := bbase (se 3 (by rfl) ⟨965408, by rfl⟩ : syracuseStep 5148845 = 1930817) (by norm_num)
theorem B3432563 : Blo 2287435 3432563 := bstep (se 1 (by rfl) ⟨2574422, by rfl⟩ : syracuseStep 3432563 = 5148845) B5148845
theorem B2288375 : Blo 2287435 2288375 := bstep (se 1 (by rfl) ⟨1716281, by rfl⟩ : syracuseStep 2288375 = 3432563) B3432563
theorem B24742421 : Blo 2287435 24742421 := bbase (se 6 (by rfl) ⟨579900, by rfl⟩ : syracuseStep 24742421 = 1159801) (by norm_num)
theorem B16494947 : Blo 2287435 16494947 := bstep (se 1 (by rfl) ⟨12371210, by rfl⟩ : syracuseStep 16494947 = 24742421) B24742421
theorem B10996631 : Blo 2287435 10996631 := bstep (se 1 (by rfl) ⟨8247473, by rfl⟩ : syracuseStep 10996631 = 16494947) B16494947
theorem B7331087 : Blo 2287435 7331087 := bstep (se 1 (by rfl) ⟨5498315, by rfl⟩ : syracuseStep 7331087 = 10996631) B10996631
theorem B4887391 : Blo 2287435 4887391 := bstep (se 1 (by rfl) ⟨3665543, by rfl⟩ : syracuseStep 4887391 = 7331087) B7331087
theorem B6516521 : Blo 2287435 6516521 := bstep (se 2 (by rfl) ⟨2443695, by rfl⟩ : syracuseStep 6516521 = 4887391) B4887391
theorem B4344347 : Blo 2287435 4344347 := bstep (se 1 (by rfl) ⟨3258260, by rfl⟩ : syracuseStep 4344347 = 6516521) B6516521
theorem B2896231 : Blo 2287435 2896231 := bstep (se 1 (by rfl) ⟨2172173, by rfl⟩ : syracuseStep 2896231 = 4344347) B4344347
theorem B3861641 : Blo 2287435 3861641 := bstep (se 2 (by rfl) ⟨1448115, by rfl⟩ : syracuseStep 3861641 = 2896231) B2896231
theorem B2574427 : Blo 2287435 2574427 := bstep (se 1 (by rfl) ⟨1930820, by rfl⟩ : syracuseStep 2574427 = 3861641) B3861641
theorem B3432569 : Blo 2287435 3432569 := bstep (se 2 (by rfl) ⟨1287213, by rfl⟩ : syracuseStep 3432569 = 2574427) B2574427
theorem B2288379 : Blo 2287435 2288379 := bstep (se 1 (by rfl) ⟨1716284, by rfl⟩ : syracuseStep 2288379 = 3432569) B3432569
theorem B10580645 : Blo 2287435 10580645 := bbase (se 4 (by rfl) ⟨991935, by rfl⟩ : syracuseStep 10580645 = 1983871) (by norm_num)
theorem B7053763 : Blo 2287435 7053763 := bstep (se 1 (by rfl) ⟨5290322, by rfl⟩ : syracuseStep 7053763 = 10580645) B10580645
theorem B9405017 : Blo 2287435 9405017 := bstep (se 2 (by rfl) ⟨3526881, by rfl⟩ : syracuseStep 9405017 = 7053763) B7053763
theorem B6270011 : Blo 2287435 6270011 := bstep (se 1 (by rfl) ⟨4702508, by rfl⟩ : syracuseStep 6270011 = 9405017) B9405017
theorem B4180007 : Blo 2287435 4180007 := bstep (se 1 (by rfl) ⟨3135005, by rfl⟩ : syracuseStep 4180007 = 6270011) B6270011
theorem B2786671 : Blo 2287435 2786671 := bstep (se 1 (by rfl) ⟨2090003, by rfl⟩ : syracuseStep 2786671 = 4180007) B4180007
theorem B3715561 : Blo 2287435 3715561 := bstep (se 2 (by rfl) ⟨1393335, by rfl⟩ : syracuseStep 3715561 = 2786671) B2786671
theorem B19816325 : Blo 2287435 19816325 := bstep (se 4 (by rfl) ⟨1857780, by rfl⟩ : syracuseStep 19816325 = 3715561) B3715561
theorem B13210883 : Blo 2287435 13210883 := bstep (se 1 (by rfl) ⟨9908162, by rfl⟩ : syracuseStep 13210883 = 19816325) B19816325
theorem B8807255 : Blo 2287435 8807255 := bstep (se 1 (by rfl) ⟨6605441, by rfl⟩ : syracuseStep 8807255 = 13210883) B13210883
theorem B5871503 : Blo 2287435 5871503 := bstep (se 1 (by rfl) ⟨4403627, by rfl⟩ : syracuseStep 5871503 = 8807255) B8807255
theorem B3914335 : Blo 2287435 3914335 := bstep (se 1 (by rfl) ⟨2935751, by rfl⟩ : syracuseStep 3914335 = 5871503) B5871503
theorem B5219113 : Blo 2287435 5219113 := bstep (se 2 (by rfl) ⟨1957167, by rfl⟩ : syracuseStep 5219113 = 3914335) B3914335
theorem B6958817 : Blo 2287435 6958817 := bstep (se 2 (by rfl) ⟨2609556, by rfl⟩ : syracuseStep 6958817 = 5219113) B5219113
theorem B4639211 : Blo 2287435 4639211 := bstep (se 1 (by rfl) ⟨3479408, by rfl⟩ : syracuseStep 4639211 = 6958817) B6958817
theorem B3092807 : Blo 2287435 3092807 := bstep (se 1 (by rfl) ⟨2319605, by rfl⟩ : syracuseStep 3092807 = 4639211) B4639211
theorem B8247485 : Blo 2287435 8247485 := bstep (se 3 (by rfl) ⟨1546403, by rfl⟩ : syracuseStep 8247485 = 3092807) B3092807
theorem B5498323 : Blo 2287435 5498323 := bstep (se 1 (by rfl) ⟨4123742, by rfl⟩ : syracuseStep 5498323 = 8247485) B8247485
theorem B29324389 : Blo 2287435 29324389 := bstep (se 4 (by rfl) ⟨2749161, by rfl⟩ : syracuseStep 29324389 = 5498323) B5498323
theorem B39099185 : Blo 2287435 39099185 := bstep (se 2 (by rfl) ⟨14662194, by rfl⟩ : syracuseStep 39099185 = 29324389) B29324389
theorem B26066123 : Blo 2287435 26066123 := bstep (se 1 (by rfl) ⟨19549592, by rfl⟩ : syracuseStep 26066123 = 39099185) B39099185
theorem B17377415 : Blo 2287435 17377415 := bstep (se 1 (by rfl) ⟨13033061, by rfl⟩ : syracuseStep 17377415 = 26066123) B26066123
theorem B11584943 : Blo 2287435 11584943 := bstep (se 1 (by rfl) ⟨8688707, by rfl⟩ : syracuseStep 11584943 = 17377415) B17377415
theorem B7723295 : Blo 2287435 7723295 := bstep (se 1 (by rfl) ⟨5792471, by rfl⟩ : syracuseStep 7723295 = 11584943) B11584943
theorem B5148863 : Blo 2287435 5148863 := bstep (se 1 (by rfl) ⟨3861647, by rfl⟩ : syracuseStep 5148863 = 7723295) B7723295
theorem B3432575 : Blo 2287435 3432575 := bstep (se 1 (by rfl) ⟨2574431, by rfl⟩ : syracuseStep 3432575 = 5148863) B5148863
theorem B2288383 : Blo 2287435 2288383 := bstep (se 1 (by rfl) ⟨1716287, by rfl⟩ : syracuseStep 2288383 = 3432575) B3432575
theorem B3432581 : Blo 2287435 3432581 := bbase (se 4 (by rfl) ⟨321804, by rfl⟩ : syracuseStep 3432581 = 643609) (by norm_num)
theorem B2288387 : Blo 2287435 2288387 := bstep (se 1 (by rfl) ⟨1716290, by rfl⟩ : syracuseStep 2288387 = 3432581) B3432581
theorem B3861661 : Blo 2287435 3861661 := bbase (se 3 (by rfl) ⟨724061, by rfl⟩ : syracuseStep 3861661 = 1448123) (by norm_num)
theorem B5148881 : Blo 2287435 5148881 := bstep (se 2 (by rfl) ⟨1930830, by rfl⟩ : syracuseStep 5148881 = 3861661) B3861661
theorem B3432587 : Blo 2287435 3432587 := bstep (se 1 (by rfl) ⟨2574440, by rfl⟩ : syracuseStep 3432587 = 5148881) B5148881
theorem B2288391 : Blo 2287435 2288391 := bstep (se 1 (by rfl) ⟨1716293, by rfl⟩ : syracuseStep 2288391 = 3432587) B3432587
theorem B2574445 : Blo 2287435 2574445 := bbase (se 3 (by rfl) ⟨482708, by rfl⟩ : syracuseStep 2574445 = 965417) (by norm_num)
theorem B3432593 : Blo 2287435 3432593 := bstep (se 2 (by rfl) ⟨1287222, by rfl⟩ : syracuseStep 3432593 = 2574445) B2574445
theorem B2288395 : Blo 2287435 2288395 := bstep (se 1 (by rfl) ⟨1716296, by rfl⟩ : syracuseStep 2288395 = 3432593) B3432593
theorem B7723349 : Blo 2287435 7723349 := bbase (se 10 (by rfl) ⟨11313, by rfl⟩ : syracuseStep 7723349 = 22627) (by norm_num)
theorem B5148899 : Blo 2287435 5148899 := bstep (se 1 (by rfl) ⟨3861674, by rfl⟩ : syracuseStep 5148899 = 7723349) B7723349
theorem B3432599 : Blo 2287435 3432599 := bstep (se 1 (by rfl) ⟨2574449, by rfl⟩ : syracuseStep 3432599 = 5148899) B5148899
theorem B2288399 : Blo 2287435 2288399 := bstep (se 1 (by rfl) ⟨1716299, by rfl⟩ : syracuseStep 2288399 = 3432599) B3432599
theorem B3432605 : Blo 2287435 3432605 := bbase (se 3 (by rfl) ⟨643613, by rfl⟩ : syracuseStep 3432605 = 1287227) (by norm_num)
theorem B2288403 : Blo 2287435 2288403 := bstep (se 1 (by rfl) ⟨1716302, by rfl⟩ : syracuseStep 2288403 = 3432605) B3432605
theorem B5148917 : Blo 2287435 5148917 := bbase (se 5 (by rfl) ⟨241355, by rfl⟩ : syracuseStep 5148917 = 482711) (by norm_num)
theorem B3432611 : Blo 2287435 3432611 := bstep (se 1 (by rfl) ⟨2574458, by rfl⟩ : syracuseStep 3432611 = 5148917) B5148917
theorem B2288407 : Blo 2287435 2288407 := bstep (se 1 (by rfl) ⟨1716305, by rfl⟩ : syracuseStep 2288407 = 3432611) B3432611
theorem B12371381 : Blo 2287435 12371381 := bbase (se 5 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 12371381 = 1159817) (by norm_num)
theorem B8247587 : Blo 2287435 8247587 := bstep (se 1 (by rfl) ⟨6185690, by rfl⟩ : syracuseStep 8247587 = 12371381) B12371381
theorem B21993565 : Blo 2287435 21993565 := bstep (se 3 (by rfl) ⟨4123793, by rfl⟩ : syracuseStep 21993565 = 8247587) B8247587
theorem B29324753 : Blo 2287435 29324753 := bstep (se 2 (by rfl) ⟨10996782, by rfl⟩ : syracuseStep 29324753 = 21993565) B21993565
theorem B19549835 : Blo 2287435 19549835 := bstep (se 1 (by rfl) ⟨14662376, by rfl⟩ : syracuseStep 19549835 = 29324753) B29324753
theorem B13033223 : Blo 2287435 13033223 := bstep (se 1 (by rfl) ⟨9774917, by rfl⟩ : syracuseStep 13033223 = 19549835) B19549835
theorem B8688815 : Blo 2287435 8688815 := bstep (se 1 (by rfl) ⟨6516611, by rfl⟩ : syracuseStep 8688815 = 13033223) B13033223
theorem B5792543 : Blo 2287435 5792543 := bstep (se 1 (by rfl) ⟨4344407, by rfl⟩ : syracuseStep 5792543 = 8688815) B8688815
theorem B3861695 : Blo 2287435 3861695 := bstep (se 1 (by rfl) ⟨2896271, by rfl⟩ : syracuseStep 3861695 = 5792543) B5792543
theorem B2574463 : Blo 2287435 2574463 := bstep (se 1 (by rfl) ⟨1930847, by rfl⟩ : syracuseStep 2574463 = 3861695) B3861695
theorem B3432617 : Blo 2287435 3432617 := bstep (se 2 (by rfl) ⟨1287231, by rfl⟩ : syracuseStep 3432617 = 2574463) B2574463
theorem B2288411 : Blo 2287435 2288411 := bstep (se 1 (by rfl) ⟨1716308, by rfl⟩ : syracuseStep 2288411 = 3432617) B3432617
theorem B4639277 : Blo 2287435 4639277 := bbase (se 3 (by rfl) ⟨869864, by rfl⟩ : syracuseStep 4639277 = 1739729) (by norm_num)
theorem B3092851 : Blo 2287435 3092851 := bstep (se 1 (by rfl) ⟨2319638, by rfl⟩ : syracuseStep 3092851 = 4639277) B4639277
theorem B4123801 : Blo 2287435 4123801 := bstep (se 2 (by rfl) ⟨1546425, by rfl⟩ : syracuseStep 4123801 = 3092851) B3092851
theorem B5498401 : Blo 2287435 5498401 := bstep (se 2 (by rfl) ⟨2061900, by rfl⟩ : syracuseStep 5498401 = 4123801) B4123801
theorem B7331201 : Blo 2287435 7331201 := bstep (se 2 (by rfl) ⟨2749200, by rfl⟩ : syracuseStep 7331201 = 5498401) B5498401
theorem B4887467 : Blo 2287435 4887467 := bstep (se 1 (by rfl) ⟨3665600, by rfl⟩ : syracuseStep 4887467 = 7331201) B7331201
theorem B3258311 : Blo 2287435 3258311 := bstep (se 1 (by rfl) ⟨2443733, by rfl⟩ : syracuseStep 3258311 = 4887467) B4887467
theorem B8688829 : Blo 2287435 8688829 := bstep (se 3 (by rfl) ⟨1629155, by rfl⟩ : syracuseStep 8688829 = 3258311) B3258311
theorem B11585105 : Blo 2287435 11585105 := bstep (se 2 (by rfl) ⟨4344414, by rfl⟩ : syracuseStep 11585105 = 8688829) B8688829
theorem B7723403 : Blo 2287435 7723403 := bstep (se 1 (by rfl) ⟨5792552, by rfl⟩ : syracuseStep 7723403 = 11585105) B11585105
theorem B5148935 : Blo 2287435 5148935 := bstep (se 1 (by rfl) ⟨3861701, by rfl⟩ : syracuseStep 5148935 = 7723403) B7723403
theorem B3432623 : Blo 2287435 3432623 := bstep (se 1 (by rfl) ⟨2574467, by rfl⟩ : syracuseStep 3432623 = 5148935) B5148935
theorem B2288415 : Blo 2287435 2288415 := bstep (se 1 (by rfl) ⟨1716311, by rfl⟩ : syracuseStep 2288415 = 3432623) B3432623
theorem B3432629 : Blo 2287435 3432629 := bbase (se 5 (by rfl) ⟨160904, by rfl⟩ : syracuseStep 3432629 = 321809) (by norm_num)
theorem B2288419 : Blo 2287435 2288419 := bstep (se 1 (by rfl) ⟨1716314, by rfl⟩ : syracuseStep 2288419 = 3432629) B3432629
theorem B5792573 : Blo 2287435 5792573 := bbase (se 3 (by rfl) ⟨1086107, by rfl⟩ : syracuseStep 5792573 = 2172215) (by norm_num)
theorem B3861715 : Blo 2287435 3861715 := bstep (se 1 (by rfl) ⟨2896286, by rfl⟩ : syracuseStep 3861715 = 5792573) B5792573
theorem B5148953 : Blo 2287435 5148953 := bstep (se 2 (by rfl) ⟨1930857, by rfl⟩ : syracuseStep 5148953 = 3861715) B3861715
theorem B3432635 : Blo 2287435 3432635 := bstep (se 1 (by rfl) ⟨2574476, by rfl⟩ : syracuseStep 3432635 = 5148953) B5148953
theorem B2288423 : Blo 2287435 2288423 := bstep (se 1 (by rfl) ⟨1716317, by rfl⟩ : syracuseStep 2288423 = 3432635) B3432635
theorem B2574481 : Blo 2287435 2574481 := bbase (se 2 (by rfl) ⟨965430, by rfl⟩ : syracuseStep 2574481 = 1930861) (by norm_num)
theorem B3432641 : Blo 2287435 3432641 := bstep (se 2 (by rfl) ⟨1287240, by rfl⟩ : syracuseStep 3432641 = 2574481) B2574481
theorem B2288427 : Blo 2287435 2288427 := bstep (se 1 (by rfl) ⟨1716320, by rfl⟩ : syracuseStep 2288427 = 3432641) B3432641
theorem B4344445 : Blo 2287435 4344445 := bbase (se 3 (by rfl) ⟨814583, by rfl⟩ : syracuseStep 4344445 = 1629167) (by norm_num)
theorem B5792593 : Blo 2287435 5792593 := bstep (se 2 (by rfl) ⟨2172222, by rfl⟩ : syracuseStep 5792593 = 4344445) B4344445
theorem B7723457 : Blo 2287435 7723457 := bstep (se 2 (by rfl) ⟨2896296, by rfl⟩ : syracuseStep 7723457 = 5792593) B5792593
theorem B5148971 : Blo 2287435 5148971 := bstep (se 1 (by rfl) ⟨3861728, by rfl⟩ : syracuseStep 5148971 = 7723457) B7723457
theorem B3432647 : Blo 2287435 3432647 := bstep (se 1 (by rfl) ⟨2574485, by rfl⟩ : syracuseStep 3432647 = 5148971) B5148971
theorem B2288431 : Blo 2287435 2288431 := bstep (se 1 (by rfl) ⟨1716323, by rfl⟩ : syracuseStep 2288431 = 3432647) B3432647
theorem B3432653 : Blo 2287435 3432653 := bbase (se 3 (by rfl) ⟨643622, by rfl⟩ : syracuseStep 3432653 = 1287245) (by norm_num)
theorem B2288435 : Blo 2287435 2288435 := bstep (se 1 (by rfl) ⟨1716326, by rfl⟩ : syracuseStep 2288435 = 3432653) B3432653
theorem B5148989 : Blo 2287435 5148989 := bbase (se 3 (by rfl) ⟨965435, by rfl⟩ : syracuseStep 5148989 = 1930871) (by norm_num)
theorem B3432659 : Blo 2287435 3432659 := bstep (se 1 (by rfl) ⟨2574494, by rfl⟩ : syracuseStep 3432659 = 5148989) B5148989
theorem B2288439 : Blo 2287435 2288439 := bstep (se 1 (by rfl) ⟨1716329, by rfl⟩ : syracuseStep 2288439 = 3432659) B3432659
theorem B3861749 : Blo 2287435 3861749 := bbase (se 5 (by rfl) ⟨181019, by rfl⟩ : syracuseStep 3861749 = 362039) (by norm_num)
theorem B2574499 : Blo 2287435 2574499 := bstep (se 1 (by rfl) ⟨1930874, by rfl⟩ : syracuseStep 2574499 = 3861749) B3861749
theorem B3432665 : Blo 2287435 3432665 := bstep (se 2 (by rfl) ⟨1287249, by rfl⟩ : syracuseStep 3432665 = 2574499) B2574499
theorem B2288443 : Blo 2287435 2288443 := bstep (se 1 (by rfl) ⟨1716332, by rfl⟩ : syracuseStep 2288443 = 3432665) B3432665
theorem B10438517 : Blo 2287435 10438517 := bbase (se 5 (by rfl) ⟨489305, by rfl⟩ : syracuseStep 10438517 = 978611) (by norm_num)
theorem B27836045 : Blo 2287435 27836045 := bstep (se 3 (by rfl) ⟨5219258, by rfl⟩ : syracuseStep 27836045 = 10438517) B10438517
theorem B18557363 : Blo 2287435 18557363 := bstep (se 1 (by rfl) ⟨13918022, by rfl⟩ : syracuseStep 18557363 = 27836045) B27836045
theorem B12371575 : Blo 2287435 12371575 := bstep (se 1 (by rfl) ⟨9278681, by rfl⟩ : syracuseStep 12371575 = 18557363) B18557363
theorem B16495433 : Blo 2287435 16495433 := bstep (se 2 (by rfl) ⟨6185787, by rfl⟩ : syracuseStep 16495433 = 12371575) B12371575
theorem B10996955 : Blo 2287435 10996955 := bstep (se 1 (by rfl) ⟨8247716, by rfl⟩ : syracuseStep 10996955 = 16495433) B16495433
theorem B7331303 : Blo 2287435 7331303 := bstep (se 1 (by rfl) ⟨5498477, by rfl⟩ : syracuseStep 7331303 = 10996955) B10996955
theorem B4887535 : Blo 2287435 4887535 := bstep (se 1 (by rfl) ⟨3665651, by rfl⟩ : syracuseStep 4887535 = 7331303) B7331303
theorem B6516713 : Blo 2287435 6516713 := bstep (se 2 (by rfl) ⟨2443767, by rfl⟩ : syracuseStep 6516713 = 4887535) B4887535
theorem B17377901 : Blo 2287435 17377901 := bstep (se 3 (by rfl) ⟨3258356, by rfl⟩ : syracuseStep 17377901 = 6516713) B6516713
theorem B11585267 : Blo 2287435 11585267 := bstep (se 1 (by rfl) ⟨8688950, by rfl⟩ : syracuseStep 11585267 = 17377901) B17377901
theorem B7723511 : Blo 2287435 7723511 := bstep (se 1 (by rfl) ⟨5792633, by rfl⟩ : syracuseStep 7723511 = 11585267) B11585267
theorem B5149007 : Blo 2287435 5149007 := bstep (se 1 (by rfl) ⟨3861755, by rfl⟩ : syracuseStep 5149007 = 7723511) B7723511
theorem B3432671 : Blo 2287435 3432671 := bstep (se 1 (by rfl) ⟨2574503, by rfl⟩ : syracuseStep 3432671 = 5149007) B5149007
theorem B2288447 : Blo 2287435 2288447 := bstep (se 1 (by rfl) ⟨1716335, by rfl⟩ : syracuseStep 2288447 = 3432671) B3432671
theorem B3432677 : Blo 2287435 3432677 := bbase (se 4 (by rfl) ⟨321813, by rfl⟩ : syracuseStep 3432677 = 643627) (by norm_num)
theorem B2288451 : Blo 2287435 2288451 := bstep (se 1 (by rfl) ⟨1716338, by rfl⟩ : syracuseStep 2288451 = 3432677) B3432677
theorem B2749249 : Blo 2287435 2749249 := bbase (se 2 (by rfl) ⟨1030968, by rfl⟩ : syracuseStep 2749249 = 2061937) (by norm_num)
theorem B3665665 : Blo 2287435 3665665 := bstep (se 2 (by rfl) ⟨1374624, by rfl⟩ : syracuseStep 3665665 = 2749249) B2749249
theorem B4887553 : Blo 2287435 4887553 := bstep (se 2 (by rfl) ⟨1832832, by rfl⟩ : syracuseStep 4887553 = 3665665) B3665665
theorem B6516737 : Blo 2287435 6516737 := bstep (se 2 (by rfl) ⟨2443776, by rfl⟩ : syracuseStep 6516737 = 4887553) B4887553
theorem B4344491 : Blo 2287435 4344491 := bstep (se 1 (by rfl) ⟨3258368, by rfl⟩ : syracuseStep 4344491 = 6516737) B6516737
theorem B2896327 : Blo 2287435 2896327 := bstep (se 1 (by rfl) ⟨2172245, by rfl⟩ : syracuseStep 2896327 = 4344491) B4344491
theorem B3861769 : Blo 2287435 3861769 := bstep (se 2 (by rfl) ⟨1448163, by rfl⟩ : syracuseStep 3861769 = 2896327) B2896327
theorem B5149025 : Blo 2287435 5149025 := bstep (se 2 (by rfl) ⟨1930884, by rfl⟩ : syracuseStep 5149025 = 3861769) B3861769
theorem B3432683 : Blo 2287435 3432683 := bstep (se 1 (by rfl) ⟨2574512, by rfl⟩ : syracuseStep 3432683 = 5149025) B5149025
theorem B2288455 : Blo 2287435 2288455 := bstep (se 1 (by rfl) ⟨1716341, by rfl⟩ : syracuseStep 2288455 = 3432683) B3432683
theorem B2574517 : Blo 2287435 2574517 := bbase (se 5 (by rfl) ⟨120680, by rfl⟩ : syracuseStep 2574517 = 241361) (by norm_num)
theorem B3432689 : Blo 2287435 3432689 := bstep (se 2 (by rfl) ⟨1287258, by rfl⟩ : syracuseStep 3432689 = 2574517) B2574517
theorem B2288459 : Blo 2287435 2288459 := bstep (se 1 (by rfl) ⟨1716344, by rfl⟩ : syracuseStep 2288459 = 3432689) B3432689
theorem B2896337 : Blo 2287435 2896337 := bbase (se 2 (by rfl) ⟨1086126, by rfl⟩ : syracuseStep 2896337 = 2172253) (by norm_num)
theorem B7723565 : Blo 2287435 7723565 := bstep (se 3 (by rfl) ⟨1448168, by rfl⟩ : syracuseStep 7723565 = 2896337) B2896337
theorem B5149043 : Blo 2287435 5149043 := bstep (se 1 (by rfl) ⟨3861782, by rfl⟩ : syracuseStep 5149043 = 7723565) B7723565
theorem B3432695 : Blo 2287435 3432695 := bstep (se 1 (by rfl) ⟨2574521, by rfl⟩ : syracuseStep 3432695 = 5149043) B5149043
theorem B2288463 : Blo 2287435 2288463 := bstep (se 1 (by rfl) ⟨1716347, by rfl⟩ : syracuseStep 2288463 = 3432695) B3432695
theorem B3432701 : Blo 2287435 3432701 := bbase (se 3 (by rfl) ⟨643631, by rfl⟩ : syracuseStep 3432701 = 1287263) (by norm_num)
theorem B2288467 : Blo 2287435 2288467 := bstep (se 1 (by rfl) ⟨1716350, by rfl⟩ : syracuseStep 2288467 = 3432701) B3432701
theorem B5149061 : Blo 2287435 5149061 := bbase (se 4 (by rfl) ⟨482724, by rfl⟩ : syracuseStep 5149061 = 965449) (by norm_num)
theorem B3432707 : Blo 2287435 3432707 := bstep (se 1 (by rfl) ⟨2574530, by rfl⟩ : syracuseStep 3432707 = 5149061) B5149061
theorem B2288471 : Blo 2287435 2288471 := bstep (se 1 (by rfl) ⟨1716353, by rfl⟩ : syracuseStep 2288471 = 3432707) B3432707
theorem B3258397 : Blo 2287435 3258397 := bbase (se 3 (by rfl) ⟨610949, by rfl⟩ : syracuseStep 3258397 = 1221899) (by norm_num)
theorem B4344529 : Blo 2287435 4344529 := bstep (se 2 (by rfl) ⟨1629198, by rfl⟩ : syracuseStep 4344529 = 3258397) B3258397
theorem B5792705 : Blo 2287435 5792705 := bstep (se 2 (by rfl) ⟨2172264, by rfl⟩ : syracuseStep 5792705 = 4344529) B4344529
theorem B3861803 : Blo 2287435 3861803 := bstep (se 1 (by rfl) ⟨2896352, by rfl⟩ : syracuseStep 3861803 = 5792705) B5792705
theorem B2574535 : Blo 2287435 2574535 := bstep (se 1 (by rfl) ⟨1930901, by rfl⟩ : syracuseStep 2574535 = 3861803) B3861803
theorem B3432713 : Blo 2287435 3432713 := bstep (se 2 (by rfl) ⟨1287267, by rfl⟩ : syracuseStep 3432713 = 2574535) B2574535
theorem B2288475 : Blo 2287435 2288475 := bstep (se 1 (by rfl) ⟨1716356, by rfl⟩ : syracuseStep 2288475 = 3432713) B3432713
theorem B11585429 : Blo 2287435 11585429 := bbase (se 6 (by rfl) ⟨271533, by rfl⟩ : syracuseStep 11585429 = 543067) (by norm_num)
theorem B7723619 : Blo 2287435 7723619 := bstep (se 1 (by rfl) ⟨5792714, by rfl⟩ : syracuseStep 7723619 = 11585429) B11585429
theorem B5149079 : Blo 2287435 5149079 := bstep (se 1 (by rfl) ⟨3861809, by rfl⟩ : syracuseStep 5149079 = 7723619) B7723619
theorem B3432719 : Blo 2287435 3432719 := bstep (se 1 (by rfl) ⟨2574539, by rfl⟩ : syracuseStep 3432719 = 5149079) B5149079
theorem B2288479 : Blo 2287435 2288479 := bstep (se 1 (by rfl) ⟨1716359, by rfl⟩ : syracuseStep 2288479 = 3432719) B3432719
theorem B3432725 : Blo 2287435 3432725 := bbase (se 6 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 3432725 = 160909) (by norm_num)
theorem B2288483 : Blo 2287435 2288483 := bstep (se 1 (by rfl) ⟨1716362, by rfl⟩ : syracuseStep 2288483 = 3432725) B3432725
theorem B8807653 : Blo 2287435 8807653 := bbase (se 4 (by rfl) ⟨825717, by rfl⟩ : syracuseStep 8807653 = 1651435) (by norm_num)
theorem B11743537 : Blo 2287435 11743537 := bstep (se 2 (by rfl) ⟨4403826, by rfl⟩ : syracuseStep 11743537 = 8807653) B8807653
theorem B15658049 : Blo 2287435 15658049 := bstep (se 2 (by rfl) ⟨5871768, by rfl⟩ : syracuseStep 15658049 = 11743537) B11743537
theorem B41754797 : Blo 2287435 41754797 := bstep (se 3 (by rfl) ⟨7829024, by rfl⟩ : syracuseStep 41754797 = 15658049) B15658049
theorem B27836531 : Blo 2287435 27836531 := bstep (se 1 (by rfl) ⟨20877398, by rfl⟩ : syracuseStep 27836531 = 41754797) B41754797
theorem B18557687 : Blo 2287435 18557687 := bstep (se 1 (by rfl) ⟨13918265, by rfl⟩ : syracuseStep 18557687 = 27836531) B27836531
theorem B12371791 : Blo 2287435 12371791 := bstep (se 1 (by rfl) ⟨9278843, by rfl⟩ : syracuseStep 12371791 = 18557687) B18557687
theorem B16495721 : Blo 2287435 16495721 := bstep (se 2 (by rfl) ⟨6185895, by rfl⟩ : syracuseStep 16495721 = 12371791) B12371791
theorem B10997147 : Blo 2287435 10997147 := bstep (se 1 (by rfl) ⟨8247860, by rfl⟩ : syracuseStep 10997147 = 16495721) B16495721
theorem B29325725 : Blo 2287435 29325725 := bstep (se 3 (by rfl) ⟨5498573, by rfl⟩ : syracuseStep 29325725 = 10997147) B10997147
theorem B19550483 : Blo 2287435 19550483 := bstep (se 1 (by rfl) ⟨14662862, by rfl⟩ : syracuseStep 19550483 = 29325725) B29325725
theorem B13033655 : Blo 2287435 13033655 := bstep (se 1 (by rfl) ⟨9775241, by rfl⟩ : syracuseStep 13033655 = 19550483) B19550483
theorem B8689103 : Blo 2287435 8689103 := bstep (se 1 (by rfl) ⟨6516827, by rfl⟩ : syracuseStep 8689103 = 13033655) B13033655
theorem B5792735 : Blo 2287435 5792735 := bstep (se 1 (by rfl) ⟨4344551, by rfl⟩ : syracuseStep 5792735 = 8689103) B8689103
theorem B3861823 : Blo 2287435 3861823 := bstep (se 1 (by rfl) ⟨2896367, by rfl⟩ : syracuseStep 3861823 = 5792735) B5792735
theorem B5149097 : Blo 2287435 5149097 := bstep (se 2 (by rfl) ⟨1930911, by rfl⟩ : syracuseStep 5149097 = 3861823) B3861823
theorem B3432731 : Blo 2287435 3432731 := bstep (se 1 (by rfl) ⟨2574548, by rfl⟩ : syracuseStep 3432731 = 5149097) B5149097
theorem B2288487 : Blo 2287435 2288487 := bstep (se 1 (by rfl) ⟨1716365, by rfl⟩ : syracuseStep 2288487 = 3432731) B3432731
theorem B2574553 : Blo 2287435 2574553 := bbase (se 2 (by rfl) ⟨965457, by rfl⟩ : syracuseStep 2574553 = 1930915) (by norm_num)
theorem B3432737 : Blo 2287435 3432737 := bstep (se 2 (by rfl) ⟨1287276, by rfl⟩ : syracuseStep 3432737 = 2574553) B2574553
theorem B2288491 : Blo 2287435 2288491 := bstep (se 1 (by rfl) ⟨1716368, by rfl⟩ : syracuseStep 2288491 = 3432737) B3432737
theorem B2749297 : Blo 2287435 2749297 := bbase (se 2 (by rfl) ⟨1030986, by rfl⟩ : syracuseStep 2749297 = 2061973) (by norm_num)
theorem B3665729 : Blo 2287435 3665729 := bstep (se 2 (by rfl) ⟨1374648, by rfl⟩ : syracuseStep 3665729 = 2749297) B2749297
theorem B2443819 : Blo 2287435 2443819 := bstep (se 1 (by rfl) ⟨1832864, by rfl⟩ : syracuseStep 2443819 = 3665729) B3665729
theorem B3258425 : Blo 2287435 3258425 := bstep (se 2 (by rfl) ⟨1221909, by rfl⟩ : syracuseStep 3258425 = 2443819) B2443819
theorem B8689133 : Blo 2287435 8689133 := bstep (se 3 (by rfl) ⟨1629212, by rfl⟩ : syracuseStep 8689133 = 3258425) B3258425
theorem B5792755 : Blo 2287435 5792755 := bstep (se 1 (by rfl) ⟨4344566, by rfl⟩ : syracuseStep 5792755 = 8689133) B8689133
theorem B7723673 : Blo 2287435 7723673 := bstep (se 2 (by rfl) ⟨2896377, by rfl⟩ : syracuseStep 7723673 = 5792755) B5792755
theorem B5149115 : Blo 2287435 5149115 := bstep (se 1 (by rfl) ⟨3861836, by rfl⟩ : syracuseStep 5149115 = 7723673) B7723673
theorem B3432743 : Blo 2287435 3432743 := bstep (se 1 (by rfl) ⟨2574557, by rfl⟩ : syracuseStep 3432743 = 5149115) B5149115
theorem B2288495 : Blo 2287435 2288495 := bstep (se 1 (by rfl) ⟨1716371, by rfl⟩ : syracuseStep 2288495 = 3432743) B3432743
theorem B3432749 : Blo 2287435 3432749 := bbase (se 3 (by rfl) ⟨643640, by rfl⟩ : syracuseStep 3432749 = 1287281) (by norm_num)
theorem B2288499 : Blo 2287435 2288499 := bstep (se 1 (by rfl) ⟨1716374, by rfl⟩ : syracuseStep 2288499 = 3432749) B3432749
theorem B5149133 : Blo 2287435 5149133 := bbase (se 3 (by rfl) ⟨965462, by rfl⟩ : syracuseStep 5149133 = 1930925) (by norm_num)
theorem B3432755 : Blo 2287435 3432755 := bstep (se 1 (by rfl) ⟨2574566, by rfl⟩ : syracuseStep 3432755 = 5149133) B5149133
theorem B2288503 : Blo 2287435 2288503 := bstep (se 1 (by rfl) ⟨1716377, by rfl⟩ : syracuseStep 2288503 = 3432755) B3432755
theorem B2896393 : Blo 2287435 2896393 := bbase (se 2 (by rfl) ⟨1086147, by rfl⟩ : syracuseStep 2896393 = 2172295) (by norm_num)
theorem B3861857 : Blo 2287435 3861857 := bstep (se 2 (by rfl) ⟨1448196, by rfl⟩ : syracuseStep 3861857 = 2896393) B2896393
theorem B2574571 : Blo 2287435 2574571 := bstep (se 1 (by rfl) ⟨1930928, by rfl⟩ : syracuseStep 2574571 = 3861857) B3861857
theorem B3432761 : Blo 2287435 3432761 := bstep (se 2 (by rfl) ⟨1287285, by rfl⟩ : syracuseStep 3432761 = 2574571) B2574571
theorem B2288507 : Blo 2287435 2288507 := bstep (se 1 (by rfl) ⟨1716380, by rfl⟩ : syracuseStep 2288507 = 3432761) B3432761
theorem B21451189 : Blo 2287435 21451189 := bbase (se 5 (by rfl) ⟨1005524, by rfl⟩ : syracuseStep 21451189 = 2011049) (by norm_num)
theorem B28601585 : Blo 2287435 28601585 := bstep (se 2 (by rfl) ⟨10725594, by rfl⟩ : syracuseStep 28601585 = 21451189) B21451189
theorem B19067723 : Blo 2287435 19067723 := bstep (se 1 (by rfl) ⟨14300792, by rfl⟩ : syracuseStep 19067723 = 28601585) B28601585
theorem B12711815 : Blo 2287435 12711815 := bstep (se 1 (by rfl) ⟨9533861, by rfl⟩ : syracuseStep 12711815 = 19067723) B19067723
theorem B8474543 : Blo 2287435 8474543 := bstep (se 1 (by rfl) ⟨6355907, by rfl⟩ : syracuseStep 8474543 = 12711815) B12711815
theorem B5649695 : Blo 2287435 5649695 := bstep (se 1 (by rfl) ⟨4237271, by rfl⟩ : syracuseStep 5649695 = 8474543) B8474543
theorem B3766463 : Blo 2287435 3766463 := bstep (se 1 (by rfl) ⟨2824847, by rfl⟩ : syracuseStep 3766463 = 5649695) B5649695
theorem B2510975 : Blo 2287435 2510975 := bstep (se 1 (by rfl) ⟨1883231, by rfl⟩ : syracuseStep 2510975 = 3766463) B3766463
theorem B6695933 : Blo 2287435 6695933 := bstep (se 3 (by rfl) ⟨1255487, by rfl⟩ : syracuseStep 6695933 = 2510975) B2510975
theorem B17855821 : Blo 2287435 17855821 := bstep (se 3 (by rfl) ⟨3347966, by rfl⟩ : syracuseStep 17855821 = 6695933) B6695933
theorem B95231045 : Blo 2287435 95231045 := bstep (se 4 (by rfl) ⟨8927910, by rfl⟩ : syracuseStep 95231045 = 17855821) B17855821
theorem B63487363 : Blo 2287435 63487363 := bstep (se 1 (by rfl) ⟨47615522, by rfl⟩ : syracuseStep 63487363 = 95231045) B95231045
theorem B84649817 : Blo 2287435 84649817 := bstep (se 2 (by rfl) ⟨31743681, by rfl⟩ : syracuseStep 84649817 = 63487363) B63487363
theorem B225732845 : Blo 2287435 225732845 := bstep (se 3 (by rfl) ⟨42324908, by rfl⟩ : syracuseStep 225732845 = 84649817) B84649817
theorem B601954253 : Blo 2287435 601954253 := bstep (se 3 (by rfl) ⟨112866422, by rfl⟩ : syracuseStep 601954253 = 225732845) B225732845
theorem B401302835 : Blo 2287435 401302835 := bstep (se 1 (by rfl) ⟨300977126, by rfl⟩ : syracuseStep 401302835 = 601954253) B601954253
theorem B267535223 : Blo 2287435 267535223 := bstep (se 1 (by rfl) ⟨200651417, by rfl⟩ : syracuseStep 267535223 = 401302835) B401302835
theorem B178356815 : Blo 2287435 178356815 := bstep (se 1 (by rfl) ⟨133767611, by rfl⟩ : syracuseStep 178356815 = 267535223) B267535223
theorem B118904543 : Blo 2287435 118904543 := bstep (se 1 (by rfl) ⟨89178407, by rfl⟩ : syracuseStep 118904543 = 178356815) B178356815
theorem B79269695 : Blo 2287435 79269695 := bstep (se 1 (by rfl) ⟨59452271, by rfl⟩ : syracuseStep 79269695 = 118904543) B118904543
theorem B52846463 : Blo 2287435 52846463 := bstep (se 1 (by rfl) ⟨39634847, by rfl⟩ : syracuseStep 52846463 = 79269695) B79269695
theorem B140923901 : Blo 2287435 140923901 := bstep (se 3 (by rfl) ⟨26423231, by rfl⟩ : syracuseStep 140923901 = 52846463) B52846463
theorem B93949267 : Blo 2287435 93949267 := bstep (se 1 (by rfl) ⟨70461950, by rfl⟩ : syracuseStep 93949267 = 140923901) B140923901
theorem B125265689 : Blo 2287435 125265689 := bstep (se 2 (by rfl) ⟨46974633, by rfl⟩ : syracuseStep 125265689 = 93949267) B93949267
theorem B83510459 : Blo 2287435 83510459 := bstep (se 1 (by rfl) ⟨62632844, by rfl⟩ : syracuseStep 83510459 = 125265689) B125265689
theorem B55673639 : Blo 2287435 55673639 := bstep (se 1 (by rfl) ⟨41755229, by rfl⟩ : syracuseStep 55673639 = 83510459) B83510459
theorem B37115759 : Blo 2287435 37115759 := bstep (se 1 (by rfl) ⟨27836819, by rfl⟩ : syracuseStep 37115759 = 55673639) B55673639
theorem B24743839 : Blo 2287435 24743839 := bstep (se 1 (by rfl) ⟨18557879, by rfl⟩ : syracuseStep 24743839 = 37115759) B37115759
theorem B32991785 : Blo 2287435 32991785 := bstep (se 2 (by rfl) ⟨12371919, by rfl⟩ : syracuseStep 32991785 = 24743839) B24743839
theorem B21994523 : Blo 2287435 21994523 := bstep (se 1 (by rfl) ⟨16495892, by rfl⟩ : syracuseStep 21994523 = 32991785) B32991785
theorem B14663015 : Blo 2287435 14663015 := bstep (se 1 (by rfl) ⟨10997261, by rfl⟩ : syracuseStep 14663015 = 21994523) B21994523
theorem B9775343 : Blo 2287435 9775343 := bstep (se 1 (by rfl) ⟨7331507, by rfl⟩ : syracuseStep 9775343 = 14663015) B14663015
theorem B26067581 : Blo 2287435 26067581 := bstep (se 3 (by rfl) ⟨4887671, by rfl⟩ : syracuseStep 26067581 = 9775343) B9775343
theorem B17378387 : Blo 2287435 17378387 := bstep (se 1 (by rfl) ⟨13033790, by rfl⟩ : syracuseStep 17378387 = 26067581) B26067581
theorem B11585591 : Blo 2287435 11585591 := bstep (se 1 (by rfl) ⟨8689193, by rfl⟩ : syracuseStep 11585591 = 17378387) B17378387
theorem B7723727 : Blo 2287435 7723727 := bstep (se 1 (by rfl) ⟨5792795, by rfl⟩ : syracuseStep 7723727 = 11585591) B11585591
theorem B5149151 : Blo 2287435 5149151 := bstep (se 1 (by rfl) ⟨3861863, by rfl⟩ : syracuseStep 5149151 = 7723727) B7723727
theorem B3432767 : Blo 2287435 3432767 := bstep (se 1 (by rfl) ⟨2574575, by rfl⟩ : syracuseStep 3432767 = 5149151) B5149151
theorem B2288511 : Blo 2287435 2288511 := bstep (se 1 (by rfl) ⟨1716383, by rfl⟩ : syracuseStep 2288511 = 3432767) B3432767
theorem B3432773 : Blo 2287435 3432773 := bbase (se 4 (by rfl) ⟨321822, by rfl⟩ : syracuseStep 3432773 = 643645) (by norm_num)
theorem B2288515 : Blo 2287435 2288515 := bstep (se 1 (by rfl) ⟨1716386, by rfl⟩ : syracuseStep 2288515 = 3432773) B3432773
theorem B3861877 : Blo 2287435 3861877 := bbase (se 5 (by rfl) ⟨181025, by rfl⟩ : syracuseStep 3861877 = 362051) (by norm_num)
theorem B5149169 : Blo 2287435 5149169 := bstep (se 2 (by rfl) ⟨1930938, by rfl⟩ : syracuseStep 5149169 = 3861877) B3861877
theorem B3432779 : Blo 2287435 3432779 := bstep (se 1 (by rfl) ⟨2574584, by rfl⟩ : syracuseStep 3432779 = 5149169) B5149169
theorem B2288519 : Blo 2287435 2288519 := bstep (se 1 (by rfl) ⟨1716389, by rfl⟩ : syracuseStep 2288519 = 3432779) B3432779
theorem B2574589 : Blo 2287435 2574589 := bbase (se 3 (by rfl) ⟨482735, by rfl⟩ : syracuseStep 2574589 = 965471) (by norm_num)
theorem B3432785 : Blo 2287435 3432785 := bstep (se 2 (by rfl) ⟨1287294, by rfl⟩ : syracuseStep 3432785 = 2574589) B2574589
theorem B2288523 : Blo 2287435 2288523 := bstep (se 1 (by rfl) ⟨1716392, by rfl⟩ : syracuseStep 2288523 = 3432785) B3432785
theorem B7723781 : Blo 2287435 7723781 := bbase (se 4 (by rfl) ⟨724104, by rfl⟩ : syracuseStep 7723781 = 1448209) (by norm_num)
theorem B5149187 : Blo 2287435 5149187 := bstep (se 1 (by rfl) ⟨3861890, by rfl⟩ : syracuseStep 5149187 = 7723781) B7723781
theorem B3432791 : Blo 2287435 3432791 := bstep (se 1 (by rfl) ⟨2574593, by rfl⟩ : syracuseStep 3432791 = 5149187) B5149187
theorem B2288527 : Blo 2287435 2288527 := bstep (se 1 (by rfl) ⟨1716395, by rfl⟩ : syracuseStep 2288527 = 3432791) B3432791
theorem B3432797 : Blo 2287435 3432797 := bbase (se 3 (by rfl) ⟨643649, by rfl⟩ : syracuseStep 3432797 = 1287299) (by norm_num)
theorem B2288531 : Blo 2287435 2288531 := bstep (se 1 (by rfl) ⟨1716398, by rfl⟩ : syracuseStep 2288531 = 3432797) B3432797
theorem B5149205 : Blo 2287435 5149205 := bbase (se 6 (by rfl) ⟨120684, by rfl⟩ : syracuseStep 5149205 = 241369) (by norm_num)
theorem B3432803 : Blo 2287435 3432803 := bstep (se 1 (by rfl) ⟨2574602, by rfl⟩ : syracuseStep 3432803 = 5149205) B5149205
theorem B2288535 : Blo 2287435 2288535 := bstep (se 1 (by rfl) ⟨1716401, by rfl⟩ : syracuseStep 2288535 = 3432803) B3432803
theorem B8689301 : Blo 2287435 8689301 := bbase (se 6 (by rfl) ⟨203655, by rfl⟩ : syracuseStep 8689301 = 407311) (by norm_num)
theorem B5792867 : Blo 2287435 5792867 := bstep (se 1 (by rfl) ⟨4344650, by rfl⟩ : syracuseStep 5792867 = 8689301) B8689301
theorem B3861911 : Blo 2287435 3861911 := bstep (se 1 (by rfl) ⟨2896433, by rfl⟩ : syracuseStep 3861911 = 5792867) B5792867
theorem B2574607 : Blo 2287435 2574607 := bstep (se 1 (by rfl) ⟨1930955, by rfl⟩ : syracuseStep 2574607 = 3861911) B3861911
theorem B3432809 : Blo 2287435 3432809 := bstep (se 2 (by rfl) ⟨1287303, by rfl⟩ : syracuseStep 3432809 = 2574607) B2574607
theorem B2288539 : Blo 2287435 2288539 := bstep (se 1 (by rfl) ⟨1716404, by rfl⟩ : syracuseStep 2288539 = 3432809) B3432809
theorem B13033973 : Blo 2287435 13033973 := bbase (se 5 (by rfl) ⟨610967, by rfl⟩ : syracuseStep 13033973 = 1221935) (by norm_num)
theorem B8689315 : Blo 2287435 8689315 := bstep (se 1 (by rfl) ⟨6516986, by rfl⟩ : syracuseStep 8689315 = 13033973) B13033973
theorem B11585753 : Blo 2287435 11585753 := bstep (se 2 (by rfl) ⟨4344657, by rfl⟩ : syracuseStep 11585753 = 8689315) B8689315
theorem B7723835 : Blo 2287435 7723835 := bstep (se 1 (by rfl) ⟨5792876, by rfl⟩ : syracuseStep 7723835 = 11585753) B11585753
theorem B5149223 : Blo 2287435 5149223 := bstep (se 1 (by rfl) ⟨3861917, by rfl⟩ : syracuseStep 5149223 = 7723835) B7723835
theorem B3432815 : Blo 2287435 3432815 := bstep (se 1 (by rfl) ⟨2574611, by rfl⟩ : syracuseStep 3432815 = 5149223) B5149223
theorem B2288543 : Blo 2287435 2288543 := bstep (se 1 (by rfl) ⟨1716407, by rfl⟩ : syracuseStep 2288543 = 3432815) B3432815
theorem B3432821 : Blo 2287435 3432821 := bbase (se 5 (by rfl) ⟨160913, by rfl⟩ : syracuseStep 3432821 = 321827) (by norm_num)
theorem B2288547 : Blo 2287435 2288547 := bstep (se 1 (by rfl) ⟨1716410, by rfl⟩ : syracuseStep 2288547 = 3432821) B3432821
theorem B2609749 : Blo 2287435 2609749 := bbase (se 8 (by rfl) ⟨15291, by rfl⟩ : syracuseStep 2609749 = 30583) (by norm_num)
theorem B13918661 : Blo 2287435 13918661 := bstep (se 4 (by rfl) ⟨1304874, by rfl⟩ : syracuseStep 13918661 = 2609749) B2609749
theorem B9279107 : Blo 2287435 9279107 := bstep (se 1 (by rfl) ⟨6959330, by rfl⟩ : syracuseStep 9279107 = 13918661) B13918661
theorem B6186071 : Blo 2287435 6186071 := bstep (se 1 (by rfl) ⟨4639553, by rfl⟩ : syracuseStep 6186071 = 9279107) B9279107
theorem B4124047 : Blo 2287435 4124047 := bstep (se 1 (by rfl) ⟨3093035, by rfl⟩ : syracuseStep 4124047 = 6186071) B6186071
theorem B5498729 : Blo 2287435 5498729 := bstep (se 2 (by rfl) ⟨2062023, by rfl⟩ : syracuseStep 5498729 = 4124047) B4124047
theorem B3665819 : Blo 2287435 3665819 := bstep (se 1 (by rfl) ⟨2749364, by rfl⟩ : syracuseStep 3665819 = 5498729) B5498729
theorem B2443879 : Blo 2287435 2443879 := bstep (se 1 (by rfl) ⟨1832909, by rfl⟩ : syracuseStep 2443879 = 3665819) B3665819
theorem B3258505 : Blo 2287435 3258505 := bstep (se 2 (by rfl) ⟨1221939, by rfl⟩ : syracuseStep 3258505 = 2443879) B2443879
theorem B4344673 : Blo 2287435 4344673 := bstep (se 2 (by rfl) ⟨1629252, by rfl⟩ : syracuseStep 4344673 = 3258505) B3258505
theorem B5792897 : Blo 2287435 5792897 := bstep (se 2 (by rfl) ⟨2172336, by rfl⟩ : syracuseStep 5792897 = 4344673) B4344673
theorem B3861931 : Blo 2287435 3861931 := bstep (se 1 (by rfl) ⟨2896448, by rfl⟩ : syracuseStep 3861931 = 5792897) B5792897
theorem B5149241 : Blo 2287435 5149241 := bstep (se 2 (by rfl) ⟨1930965, by rfl⟩ : syracuseStep 5149241 = 3861931) B3861931
theorem B3432827 : Blo 2287435 3432827 := bstep (se 1 (by rfl) ⟨2574620, by rfl⟩ : syracuseStep 3432827 = 5149241) B5149241
theorem B2288551 : Blo 2287435 2288551 := bstep (se 1 (by rfl) ⟨1716413, by rfl⟩ : syracuseStep 2288551 = 3432827) B3432827
theorem B2574625 : Blo 2287435 2574625 := bbase (se 2 (by rfl) ⟨965484, by rfl⟩ : syracuseStep 2574625 = 1930969) (by norm_num)
theorem B3432833 : Blo 2287435 3432833 := bstep (se 2 (by rfl) ⟨1287312, by rfl⟩ : syracuseStep 3432833 = 2574625) B2574625
theorem B2288555 : Blo 2287435 2288555 := bstep (se 1 (by rfl) ⟨1716416, by rfl⟩ : syracuseStep 2288555 = 3432833) B3432833
theorem B5792917 : Blo 2287435 5792917 := bbase (se 6 (by rfl) ⟨135771, by rfl⟩ : syracuseStep 5792917 = 271543) (by norm_num)
theorem B7723889 : Blo 2287435 7723889 := bstep (se 2 (by rfl) ⟨2896458, by rfl⟩ : syracuseStep 7723889 = 5792917) B5792917
theorem B5149259 : Blo 2287435 5149259 := bstep (se 1 (by rfl) ⟨3861944, by rfl⟩ : syracuseStep 5149259 = 7723889) B7723889
theorem B3432839 : Blo 2287435 3432839 := bstep (se 1 (by rfl) ⟨2574629, by rfl⟩ : syracuseStep 3432839 = 5149259) B5149259
theorem B2288559 : Blo 2287435 2288559 := bstep (se 1 (by rfl) ⟨1716419, by rfl⟩ : syracuseStep 2288559 = 3432839) B3432839
theorem B3432845 : Blo 2287435 3432845 := bbase (se 3 (by rfl) ⟨643658, by rfl⟩ : syracuseStep 3432845 = 1287317) (by norm_num)
theorem B2288563 : Blo 2287435 2288563 := bstep (se 1 (by rfl) ⟨1716422, by rfl⟩ : syracuseStep 2288563 = 3432845) B3432845
theorem B5149277 : Blo 2287435 5149277 := bbase (se 3 (by rfl) ⟨965489, by rfl⟩ : syracuseStep 5149277 = 1930979) (by norm_num)
theorem B3432851 : Blo 2287435 3432851 := bstep (se 1 (by rfl) ⟨2574638, by rfl⟩ : syracuseStep 3432851 = 5149277) B5149277
theorem B2288567 : Blo 2287435 2288567 := bstep (se 1 (by rfl) ⟨1716425, by rfl⟩ : syracuseStep 2288567 = 3432851) B3432851
theorem B3861965 : Blo 2287435 3861965 := bbase (se 3 (by rfl) ⟨724118, by rfl⟩ : syracuseStep 3861965 = 1448237) (by norm_num)
theorem B2574643 : Blo 2287435 2574643 := bstep (se 1 (by rfl) ⟨1930982, by rfl⟩ : syracuseStep 2574643 = 3861965) B3861965
theorem B3432857 : Blo 2287435 3432857 := bstep (se 2 (by rfl) ⟨1287321, by rfl⟩ : syracuseStep 3432857 = 2574643) B2574643
theorem B2288571 : Blo 2287435 2288571 := bstep (se 1 (by rfl) ⟨1716428, by rfl⟩ : syracuseStep 2288571 = 3432857) B3432857
theorem B6186133 : Blo 2287435 6186133 := bbase (se 6 (by rfl) ⟨144987, by rfl⟩ : syracuseStep 6186133 = 289975) (by norm_num)
theorem B8248177 : Blo 2287435 8248177 := bstep (se 2 (by rfl) ⟨3093066, by rfl⟩ : syracuseStep 8248177 = 6186133) B6186133
theorem B10997569 : Blo 2287435 10997569 := bstep (se 2 (by rfl) ⟨4124088, by rfl⟩ : syracuseStep 10997569 = 8248177) B8248177
theorem B14663425 : Blo 2287435 14663425 := bstep (se 2 (by rfl) ⟨5498784, by rfl⟩ : syracuseStep 14663425 = 10997569) B10997569
theorem B19551233 : Blo 2287435 19551233 := bstep (se 2 (by rfl) ⟨7331712, by rfl⟩ : syracuseStep 19551233 = 14663425) B14663425
theorem B13034155 : Blo 2287435 13034155 := bstep (se 1 (by rfl) ⟨9775616, by rfl⟩ : syracuseStep 13034155 = 19551233) B19551233
theorem B17378873 : Blo 2287435 17378873 := bstep (se 2 (by rfl) ⟨6517077, by rfl⟩ : syracuseStep 17378873 = 13034155) B13034155
theorem B11585915 : Blo 2287435 11585915 := bstep (se 1 (by rfl) ⟨8689436, by rfl⟩ : syracuseStep 11585915 = 17378873) B17378873
theorem B7723943 : Blo 2287435 7723943 := bstep (se 1 (by rfl) ⟨5792957, by rfl⟩ : syracuseStep 7723943 = 11585915) B11585915
theorem B5149295 : Blo 2287435 5149295 := bstep (se 1 (by rfl) ⟨3861971, by rfl⟩ : syracuseStep 5149295 = 7723943) B7723943
theorem B3432863 : Blo 2287435 3432863 := bstep (se 1 (by rfl) ⟨2574647, by rfl⟩ : syracuseStep 3432863 = 5149295) B5149295
theorem B2288575 : Blo 2287435 2288575 := bstep (se 1 (by rfl) ⟨1716431, by rfl⟩ : syracuseStep 2288575 = 3432863) B3432863
theorem B3432869 : Blo 2287435 3432869 := bbase (se 4 (by rfl) ⟨321831, by rfl⟩ : syracuseStep 3432869 = 643663) (by norm_num)
theorem B2288579 : Blo 2287435 2288579 := bstep (se 1 (by rfl) ⟨1716434, by rfl⟩ : syracuseStep 2288579 = 3432869) B3432869
theorem B2896489 : Blo 2287435 2896489 := bbase (se 2 (by rfl) ⟨1086183, by rfl⟩ : syracuseStep 2896489 = 2172367) (by norm_num)
theorem B3861985 : Blo 2287435 3861985 := bstep (se 2 (by rfl) ⟨1448244, by rfl⟩ : syracuseStep 3861985 = 2896489) B2896489
theorem B5149313 : Blo 2287435 5149313 := bstep (se 2 (by rfl) ⟨1930992, by rfl⟩ : syracuseStep 5149313 = 3861985) B3861985
theorem B3432875 : Blo 2287435 3432875 := bstep (se 1 (by rfl) ⟨2574656, by rfl⟩ : syracuseStep 3432875 = 5149313) B5149313
theorem B2288583 : Blo 2287435 2288583 := bstep (se 1 (by rfl) ⟨1716437, by rfl⟩ : syracuseStep 2288583 = 3432875) B3432875
theorem B2574661 : Blo 2287435 2574661 := bbase (se 4 (by rfl) ⟨241374, by rfl⟩ : syracuseStep 2574661 = 482749) (by norm_num)
theorem B3432881 : Blo 2287435 3432881 := bstep (se 2 (by rfl) ⟨1287330, by rfl⟩ : syracuseStep 3432881 = 2574661) B2574661
theorem B2288587 : Blo 2287435 2288587 := bstep (se 1 (by rfl) ⟨1716440, by rfl⟩ : syracuseStep 2288587 = 3432881) B3432881
theorem B4344749 : Blo 2287435 4344749 := bbase (se 3 (by rfl) ⟨814640, by rfl⟩ : syracuseStep 4344749 = 1629281) (by norm_num)
theorem B2896499 : Blo 2287435 2896499 := bstep (se 1 (by rfl) ⟨2172374, by rfl⟩ : syracuseStep 2896499 = 4344749) B4344749
theorem B7723997 : Blo 2287435 7723997 := bstep (se 3 (by rfl) ⟨1448249, by rfl⟩ : syracuseStep 7723997 = 2896499) B2896499
theorem B5149331 : Blo 2287435 5149331 := bstep (se 1 (by rfl) ⟨3861998, by rfl⟩ : syracuseStep 5149331 = 7723997) B7723997
theorem B3432887 : Blo 2287435 3432887 := bstep (se 1 (by rfl) ⟨2574665, by rfl⟩ : syracuseStep 3432887 = 5149331) B5149331
theorem B2288591 : Blo 2287435 2288591 := bstep (se 1 (by rfl) ⟨1716443, by rfl⟩ : syracuseStep 2288591 = 3432887) B3432887
theorem B3432893 : Blo 2287435 3432893 := bbase (se 3 (by rfl) ⟨643667, by rfl⟩ : syracuseStep 3432893 = 1287335) (by norm_num)
theorem B2288595 : Blo 2287435 2288595 := bstep (se 1 (by rfl) ⟨1716446, by rfl⟩ : syracuseStep 2288595 = 3432893) B3432893
theorem B5149349 : Blo 2287435 5149349 := bbase (se 4 (by rfl) ⟨482751, by rfl⟩ : syracuseStep 5149349 = 965503) (by norm_num)
theorem B3432899 : Blo 2287435 3432899 := bstep (se 1 (by rfl) ⟨2574674, by rfl⟩ : syracuseStep 3432899 = 5149349) B5149349
theorem B2288599 : Blo 2287435 2288599 := bstep (se 1 (by rfl) ⟨1716449, by rfl⟩ : syracuseStep 2288599 = 3432899) B3432899
theorem B5793029 : Blo 2287435 5793029 := bbase (se 4 (by rfl) ⟨543096, by rfl⟩ : syracuseStep 5793029 = 1086193) (by norm_num)
theorem B3862019 : Blo 2287435 3862019 := bstep (se 1 (by rfl) ⟨2896514, by rfl⟩ : syracuseStep 3862019 = 5793029) B5793029
theorem B2574679 : Blo 2287435 2574679 := bstep (se 1 (by rfl) ⟨1931009, by rfl⟩ : syracuseStep 2574679 = 3862019) B3862019
theorem B3432905 : Blo 2287435 3432905 := bstep (se 2 (by rfl) ⟨1287339, by rfl⟩ : syracuseStep 3432905 = 2574679) B2574679
theorem B2288603 : Blo 2287435 2288603 := bstep (se 1 (by rfl) ⟨1716452, by rfl⟩ : syracuseStep 2288603 = 3432905) B3432905
theorem B4887877 : Blo 2287435 4887877 := bbase (se 4 (by rfl) ⟨458238, by rfl⟩ : syracuseStep 4887877 = 916477) (by norm_num)
theorem B6517169 : Blo 2287435 6517169 := bstep (se 2 (by rfl) ⟨2443938, by rfl⟩ : syracuseStep 6517169 = 4887877) B4887877
theorem B4344779 : Blo 2287435 4344779 := bstep (se 1 (by rfl) ⟨3258584, by rfl⟩ : syracuseStep 4344779 = 6517169) B6517169
theorem B11586077 : Blo 2287435 11586077 := bstep (se 3 (by rfl) ⟨2172389, by rfl⟩ : syracuseStep 11586077 = 4344779) B4344779
theorem B7724051 : Blo 2287435 7724051 := bstep (se 1 (by rfl) ⟨5793038, by rfl⟩ : syracuseStep 7724051 = 11586077) B11586077
theorem B5149367 : Blo 2287435 5149367 := bstep (se 1 (by rfl) ⟨3862025, by rfl⟩ : syracuseStep 5149367 = 7724051) B7724051
theorem B3432911 : Blo 2287435 3432911 := bstep (se 1 (by rfl) ⟨2574683, by rfl⟩ : syracuseStep 3432911 = 5149367) B5149367
theorem B2288607 : Blo 2287435 2288607 := bstep (se 1 (by rfl) ⟨1716455, by rfl⟩ : syracuseStep 2288607 = 3432911) B3432911
theorem B3432917 : Blo 2287435 3432917 := bbase (se 7 (by rfl) ⟨40229, by rfl⟩ : syracuseStep 3432917 = 80459) (by norm_num)
theorem B2288611 : Blo 2287435 2288611 := bstep (se 1 (by rfl) ⟨1716458, by rfl⟩ : syracuseStep 2288611 = 3432917) B3432917
theorem B8689589 : Blo 2287435 8689589 := bbase (se 5 (by rfl) ⟨407324, by rfl⟩ : syracuseStep 8689589 = 814649) (by norm_num)
theorem B5793059 : Blo 2287435 5793059 := bstep (se 1 (by rfl) ⟨4344794, by rfl⟩ : syracuseStep 5793059 = 8689589) B8689589
theorem B3862039 : Blo 2287435 3862039 := bstep (se 1 (by rfl) ⟨2896529, by rfl⟩ : syracuseStep 3862039 = 5793059) B5793059
theorem B5149385 : Blo 2287435 5149385 := bstep (se 2 (by rfl) ⟨1931019, by rfl⟩ : syracuseStep 5149385 = 3862039) B3862039
theorem B3432923 : Blo 2287435 3432923 := bstep (se 1 (by rfl) ⟨2574692, by rfl⟩ : syracuseStep 3432923 = 5149385) B5149385
theorem B2288615 : Blo 2287435 2288615 := bstep (se 1 (by rfl) ⟨1716461, by rfl⟩ : syracuseStep 2288615 = 3432923) B3432923
theorem B2574697 : Blo 2287435 2574697 := bbase (se 2 (by rfl) ⟨965511, by rfl⟩ : syracuseStep 2574697 = 1931023) (by norm_num)
theorem B3432929 : Blo 2287435 3432929 := bstep (se 2 (by rfl) ⟨1287348, by rfl⟩ : syracuseStep 3432929 = 2574697) B2574697
theorem B2288619 : Blo 2287435 2288619 := bstep (se 1 (by rfl) ⟨1716464, by rfl⟩ : syracuseStep 2288619 = 3432929) B3432929
theorem B10581749 : Blo 2287435 10581749 := bbase (se 5 (by rfl) ⟨496019, by rfl⟩ : syracuseStep 10581749 = 992039) (by norm_num)
theorem B7054499 : Blo 2287435 7054499 := bstep (se 1 (by rfl) ⟨5290874, by rfl⟩ : syracuseStep 7054499 = 10581749) B10581749
theorem B18811997 : Blo 2287435 18811997 := bstep (se 3 (by rfl) ⟨3527249, by rfl⟩ : syracuseStep 18811997 = 7054499) B7054499
theorem B12541331 : Blo 2287435 12541331 := bstep (se 1 (by rfl) ⟨9405998, by rfl⟩ : syracuseStep 12541331 = 18811997) B18811997
theorem B33443549 : Blo 2287435 33443549 := bstep (se 3 (by rfl) ⟨6270665, by rfl⟩ : syracuseStep 33443549 = 12541331) B12541331
theorem B22295699 : Blo 2287435 22295699 := bstep (se 1 (by rfl) ⟨16721774, by rfl⟩ : syracuseStep 22295699 = 33443549) B33443549
theorem B14863799 : Blo 2287435 14863799 := bstep (se 1 (by rfl) ⟨11147849, by rfl⟩ : syracuseStep 14863799 = 22295699) B22295699
theorem B9909199 : Blo 2287435 9909199 := bstep (se 1 (by rfl) ⟨7431899, by rfl⟩ : syracuseStep 9909199 = 14863799) B14863799
theorem B52849061 : Blo 2287435 52849061 := bstep (se 4 (by rfl) ⟨4954599, by rfl⟩ : syracuseStep 52849061 = 9909199) B9909199
theorem B35232707 : Blo 2287435 35232707 := bstep (se 1 (by rfl) ⟨26424530, by rfl⟩ : syracuseStep 35232707 = 52849061) B52849061
theorem B23488471 : Blo 2287435 23488471 := bstep (se 1 (by rfl) ⟨17616353, by rfl⟩ : syracuseStep 23488471 = 35232707) B35232707
theorem B31317961 : Blo 2287435 31317961 := bstep (se 2 (by rfl) ⟨11744235, by rfl⟩ : syracuseStep 31317961 = 23488471) B23488471
theorem B41757281 : Blo 2287435 41757281 := bstep (se 2 (by rfl) ⟨15658980, by rfl⟩ : syracuseStep 41757281 = 31317961) B31317961
theorem B27838187 : Blo 2287435 27838187 := bstep (se 1 (by rfl) ⟨20878640, by rfl⟩ : syracuseStep 27838187 = 41757281) B41757281
theorem B18558791 : Blo 2287435 18558791 := bstep (se 1 (by rfl) ⟨13919093, by rfl⟩ : syracuseStep 18558791 = 27838187) B27838187
theorem B12372527 : Blo 2287435 12372527 := bstep (se 1 (by rfl) ⟨9279395, by rfl⟩ : syracuseStep 12372527 = 18558791) B18558791
theorem B8248351 : Blo 2287435 8248351 := bstep (se 1 (by rfl) ⟨6186263, by rfl⟩ : syracuseStep 8248351 = 12372527) B12372527
theorem B10997801 : Blo 2287435 10997801 := bstep (se 2 (by rfl) ⟨4124175, by rfl⟩ : syracuseStep 10997801 = 8248351) B8248351
theorem B7331867 : Blo 2287435 7331867 := bstep (se 1 (by rfl) ⟨5498900, by rfl⟩ : syracuseStep 7331867 = 10997801) B10997801
theorem B4887911 : Blo 2287435 4887911 := bstep (se 1 (by rfl) ⟨3665933, by rfl⟩ : syracuseStep 4887911 = 7331867) B7331867
theorem B13034429 : Blo 2287435 13034429 := bstep (se 3 (by rfl) ⟨2443955, by rfl⟩ : syracuseStep 13034429 = 4887911) B4887911
theorem B8689619 : Blo 2287435 8689619 := bstep (se 1 (by rfl) ⟨6517214, by rfl⟩ : syracuseStep 8689619 = 13034429) B13034429
theorem B5793079 : Blo 2287435 5793079 := bstep (se 1 (by rfl) ⟨4344809, by rfl⟩ : syracuseStep 5793079 = 8689619) B8689619
theorem B7724105 : Blo 2287435 7724105 := bstep (se 2 (by rfl) ⟨2896539, by rfl⟩ : syracuseStep 7724105 = 5793079) B5793079
theorem B5149403 : Blo 2287435 5149403 := bstep (se 1 (by rfl) ⟨3862052, by rfl⟩ : syracuseStep 5149403 = 7724105) B7724105
theorem B3432935 : Blo 2287435 3432935 := bstep (se 1 (by rfl) ⟨2574701, by rfl⟩ : syracuseStep 3432935 = 5149403) B5149403
theorem B2288623 : Blo 2287435 2288623 := bstep (se 1 (by rfl) ⟨1716467, by rfl⟩ : syracuseStep 2288623 = 3432935) B3432935
theorem B3432941 : Blo 2287435 3432941 := bbase (se 3 (by rfl) ⟨643676, by rfl⟩ : syracuseStep 3432941 = 1287353) (by norm_num)
theorem B2288627 : Blo 2287435 2288627 := bstep (se 1 (by rfl) ⟨1716470, by rfl⟩ : syracuseStep 2288627 = 3432941) B3432941
theorem B5149421 : Blo 2287435 5149421 := bbase (se 3 (by rfl) ⟨965516, by rfl⟩ : syracuseStep 5149421 = 1931033) (by norm_num)
theorem B3432947 : Blo 2287435 3432947 := bstep (se 1 (by rfl) ⟨2574710, by rfl⟩ : syracuseStep 3432947 = 5149421) B5149421
theorem B2288631 : Blo 2287435 2288631 := bstep (se 1 (by rfl) ⟨1716473, by rfl⟩ : syracuseStep 2288631 = 3432947) B3432947
theorem B2443969 : Blo 2287435 2443969 := bbase (se 2 (by rfl) ⟨916488, by rfl⟩ : syracuseStep 2443969 = 1832977) (by norm_num)
theorem B3258625 : Blo 2287435 3258625 := bstep (se 2 (by rfl) ⟨1221984, by rfl⟩ : syracuseStep 3258625 = 2443969) B2443969
theorem B4344833 : Blo 2287435 4344833 := bstep (se 2 (by rfl) ⟨1629312, by rfl⟩ : syracuseStep 4344833 = 3258625) B3258625
theorem B2896555 : Blo 2287435 2896555 := bstep (se 1 (by rfl) ⟨2172416, by rfl⟩ : syracuseStep 2896555 = 4344833) B4344833
theorem B3862073 : Blo 2287435 3862073 := bstep (se 2 (by rfl) ⟨1448277, by rfl⟩ : syracuseStep 3862073 = 2896555) B2896555
theorem B2574715 : Blo 2287435 2574715 := bstep (se 1 (by rfl) ⟨1931036, by rfl⟩ : syracuseStep 2574715 = 3862073) B3862073
theorem B3432953 : Blo 2287435 3432953 := bstep (se 2 (by rfl) ⟨1287357, by rfl⟩ : syracuseStep 3432953 = 2574715) B2574715
theorem B2288635 : Blo 2287435 2288635 := bstep (se 1 (by rfl) ⟨1716476, by rfl⟩ : syracuseStep 2288635 = 3432953) B3432953
theorem B6270709 : Blo 2287435 6270709 := bbase (se 5 (by rfl) ⟨293939, by rfl⟩ : syracuseStep 6270709 = 587879) (by norm_num)
theorem B8360945 : Blo 2287435 8360945 := bstep (se 2 (by rfl) ⟨3135354, by rfl⟩ : syracuseStep 8360945 = 6270709) B6270709
theorem B5573963 : Blo 2287435 5573963 := bstep (se 1 (by rfl) ⟨4180472, by rfl⟩ : syracuseStep 5573963 = 8360945) B8360945
theorem B3715975 : Blo 2287435 3715975 := bstep (se 1 (by rfl) ⟨2786981, by rfl⟩ : syracuseStep 3715975 = 5573963) B5573963
theorem B19818533 : Blo 2287435 19818533 := bstep (se 4 (by rfl) ⟨1857987, by rfl⟩ : syracuseStep 19818533 = 3715975) B3715975
theorem B13212355 : Blo 2287435 13212355 := bstep (se 1 (by rfl) ⟨9909266, by rfl⟩ : syracuseStep 13212355 = 19818533) B19818533
theorem B17616473 : Blo 2287435 17616473 := bstep (se 2 (by rfl) ⟨6606177, by rfl⟩ : syracuseStep 17616473 = 13212355) B13212355
theorem B11744315 : Blo 2287435 11744315 := bstep (se 1 (by rfl) ⟨8808236, by rfl⟩ : syracuseStep 11744315 = 17616473) B17616473
theorem B7829543 : Blo 2287435 7829543 := bstep (se 1 (by rfl) ⟨5872157, by rfl⟩ : syracuseStep 7829543 = 11744315) B11744315
theorem B20878781 : Blo 2287435 20878781 := bstep (se 3 (by rfl) ⟨3914771, by rfl⟩ : syracuseStep 20878781 = 7829543) B7829543
theorem B55676749 : Blo 2287435 55676749 := bstep (se 3 (by rfl) ⟨10439390, by rfl⟩ : syracuseStep 55676749 = 20878781) B20878781
theorem B74235665 : Blo 2287435 74235665 := bstep (se 2 (by rfl) ⟨27838374, by rfl⟩ : syracuseStep 74235665 = 55676749) B55676749
theorem B49490443 : Blo 2287435 49490443 := bstep (se 1 (by rfl) ⟨37117832, by rfl⟩ : syracuseStep 49490443 = 74235665) B74235665
theorem B65987257 : Blo 2287435 65987257 := bstep (se 2 (by rfl) ⟨24745221, by rfl⟩ : syracuseStep 65987257 = 49490443) B49490443
theorem B87983009 : Blo 2287435 87983009 := bstep (se 2 (by rfl) ⟨32993628, by rfl⟩ : syracuseStep 87983009 = 65987257) B65987257
theorem B58655339 : Blo 2287435 58655339 := bstep (se 1 (by rfl) ⟨43991504, by rfl⟩ : syracuseStep 58655339 = 87983009) B87983009
theorem B39103559 : Blo 2287435 39103559 := bstep (se 1 (by rfl) ⟨29327669, by rfl⟩ : syracuseStep 39103559 = 58655339) B58655339
theorem B26069039 : Blo 2287435 26069039 := bstep (se 1 (by rfl) ⟨19551779, by rfl⟩ : syracuseStep 26069039 = 39103559) B39103559
theorem B17379359 : Blo 2287435 17379359 := bstep (se 1 (by rfl) ⟨13034519, by rfl⟩ : syracuseStep 17379359 = 26069039) B26069039
theorem B11586239 : Blo 2287435 11586239 := bstep (se 1 (by rfl) ⟨8689679, by rfl⟩ : syracuseStep 11586239 = 17379359) B17379359
theorem B7724159 : Blo 2287435 7724159 := bstep (se 1 (by rfl) ⟨5793119, by rfl⟩ : syracuseStep 7724159 = 11586239) B11586239
theorem B5149439 : Blo 2287435 5149439 := bstep (se 1 (by rfl) ⟨3862079, by rfl⟩ : syracuseStep 5149439 = 7724159) B7724159
theorem B3432959 : Blo 2287435 3432959 := bstep (se 1 (by rfl) ⟨2574719, by rfl⟩ : syracuseStep 3432959 = 5149439) B5149439
theorem B2288639 : Blo 2287435 2288639 := bstep (se 1 (by rfl) ⟨1716479, by rfl⟩ : syracuseStep 2288639 = 3432959) B3432959
theorem B3432965 : Blo 2287435 3432965 := bbase (se 4 (by rfl) ⟨321840, by rfl⟩ : syracuseStep 3432965 = 643681) (by norm_num)
theorem B2288643 : Blo 2287435 2288643 := bstep (se 1 (by rfl) ⟨1716482, by rfl⟩ : syracuseStep 2288643 = 3432965) B3432965
theorem B3862093 : Blo 2287435 3862093 := bbase (se 3 (by rfl) ⟨724142, by rfl⟩ : syracuseStep 3862093 = 1448285) (by norm_num)
theorem B5149457 : Blo 2287435 5149457 := bstep (se 2 (by rfl) ⟨1931046, by rfl⟩ : syracuseStep 5149457 = 3862093) B3862093
theorem B3432971 : Blo 2287435 3432971 := bstep (se 1 (by rfl) ⟨2574728, by rfl⟩ : syracuseStep 3432971 = 5149457) B5149457
theorem B2288647 : Blo 2287435 2288647 := bstep (se 1 (by rfl) ⟨1716485, by rfl⟩ : syracuseStep 2288647 = 3432971) B3432971
theorem B2574733 : Blo 2287435 2574733 := bbase (se 3 (by rfl) ⟨482762, by rfl⟩ : syracuseStep 2574733 = 965525) (by norm_num)
theorem B3432977 : Blo 2287435 3432977 := bstep (se 2 (by rfl) ⟨1287366, by rfl⟩ : syracuseStep 3432977 = 2574733) B2574733
theorem B2288651 : Blo 2287435 2288651 := bstep (se 1 (by rfl) ⟨1716488, by rfl⟩ : syracuseStep 2288651 = 3432977) B3432977
theorem B7724213 : Blo 2287435 7724213 := bbase (se 5 (by rfl) ⟨362072, by rfl⟩ : syracuseStep 7724213 = 724145) (by norm_num)
theorem B5149475 : Blo 2287435 5149475 := bstep (se 1 (by rfl) ⟨3862106, by rfl⟩ : syracuseStep 5149475 = 7724213) B7724213
theorem B3432983 : Blo 2287435 3432983 := bstep (se 1 (by rfl) ⟨2574737, by rfl⟩ : syracuseStep 3432983 = 5149475) B5149475
theorem B2288655 : Blo 2287435 2288655 := bstep (se 1 (by rfl) ⟨1716491, by rfl⟩ : syracuseStep 2288655 = 3432983) B3432983
theorem B3432989 : Blo 2287435 3432989 := bbase (se 3 (by rfl) ⟨643685, by rfl⟩ : syracuseStep 3432989 = 1287371) (by norm_num)
theorem B2288659 : Blo 2287435 2288659 := bstep (se 1 (by rfl) ⟨1716494, by rfl⟩ : syracuseStep 2288659 = 3432989) B3432989
theorem B5149493 : Blo 2287435 5149493 := bbase (se 5 (by rfl) ⟨241382, by rfl⟩ : syracuseStep 5149493 = 482765) (by norm_num)
theorem B3432995 : Blo 2287435 3432995 := bstep (se 1 (by rfl) ⟨2574746, by rfl⟩ : syracuseStep 3432995 = 5149493) B5149493
theorem B2288663 : Blo 2287435 2288663 := bstep (se 1 (by rfl) ⟨1716497, by rfl⟩ : syracuseStep 2288663 = 3432995) B3432995
theorem B3914821 : Blo 2287435 3914821 := bbase (se 4 (by rfl) ⟨367014, by rfl⟩ : syracuseStep 3914821 = 734029) (by norm_num)
theorem B20879045 : Blo 2287435 20879045 := bstep (se 4 (by rfl) ⟨1957410, by rfl⟩ : syracuseStep 20879045 = 3914821) B3914821
theorem B13919363 : Blo 2287435 13919363 := bstep (se 1 (by rfl) ⟨10439522, by rfl⟩ : syracuseStep 13919363 = 20879045) B20879045
theorem B9279575 : Blo 2287435 9279575 := bstep (se 1 (by rfl) ⟨6959681, by rfl⟩ : syracuseStep 9279575 = 13919363) B13919363
theorem B6186383 : Blo 2287435 6186383 := bstep (se 1 (by rfl) ⟨4639787, by rfl⟩ : syracuseStep 6186383 = 9279575) B9279575
theorem B4124255 : Blo 2287435 4124255 := bstep (se 1 (by rfl) ⟨3093191, by rfl⟩ : syracuseStep 4124255 = 6186383) B6186383
theorem B10998013 : Blo 2287435 10998013 := bstep (se 3 (by rfl) ⟨2062127, by rfl⟩ : syracuseStep 10998013 = 4124255) B4124255
theorem B14664017 : Blo 2287435 14664017 := bstep (se 2 (by rfl) ⟨5499006, by rfl⟩ : syracuseStep 14664017 = 10998013) B10998013
theorem B9776011 : Blo 2287435 9776011 := bstep (se 1 (by rfl) ⟨7332008, by rfl⟩ : syracuseStep 9776011 = 14664017) B14664017
theorem B13034681 : Blo 2287435 13034681 := bstep (se 2 (by rfl) ⟨4888005, by rfl⟩ : syracuseStep 13034681 = 9776011) B9776011
theorem B8689787 : Blo 2287435 8689787 := bstep (se 1 (by rfl) ⟨6517340, by rfl⟩ : syracuseStep 8689787 = 13034681) B13034681
theorem B5793191 : Blo 2287435 5793191 := bstep (se 1 (by rfl) ⟨4344893, by rfl⟩ : syracuseStep 5793191 = 8689787) B8689787
theorem B3862127 : Blo 2287435 3862127 := bstep (se 1 (by rfl) ⟨2896595, by rfl⟩ : syracuseStep 3862127 = 5793191) B5793191
theorem B2574751 : Blo 2287435 2574751 := bstep (se 1 (by rfl) ⟨1931063, by rfl⟩ : syracuseStep 2574751 = 3862127) B3862127
theorem B3433001 : Blo 2287435 3433001 := bstep (se 2 (by rfl) ⟨1287375, by rfl⟩ : syracuseStep 3433001 = 2574751) B2574751
theorem B2288667 : Blo 2287435 2288667 := bstep (se 1 (by rfl) ⟨1716500, by rfl⟩ : syracuseStep 2288667 = 3433001) B3433001
theorem B37118357 : Blo 2287435 37118357 := bbase (se 6 (by rfl) ⟨869961, by rfl⟩ : syracuseStep 37118357 = 1739923) (by norm_num)
theorem B24745571 : Blo 2287435 24745571 := bstep (se 1 (by rfl) ⟨18559178, by rfl⟩ : syracuseStep 24745571 = 37118357) B37118357
theorem B16497047 : Blo 2287435 16497047 := bstep (se 1 (by rfl) ⟨12372785, by rfl⟩ : syracuseStep 16497047 = 24745571) B24745571
theorem B10998031 : Blo 2287435 10998031 := bstep (se 1 (by rfl) ⟨8248523, by rfl⟩ : syracuseStep 10998031 = 16497047) B16497047
theorem B14664041 : Blo 2287435 14664041 := bstep (se 2 (by rfl) ⟨5499015, by rfl⟩ : syracuseStep 14664041 = 10998031) B10998031
theorem B9776027 : Blo 2287435 9776027 := bstep (se 1 (by rfl) ⟨7332020, by rfl⟩ : syracuseStep 9776027 = 14664041) B14664041
theorem B6517351 : Blo 2287435 6517351 := bstep (se 1 (by rfl) ⟨4888013, by rfl⟩ : syracuseStep 6517351 = 9776027) B9776027
theorem B8689801 : Blo 2287435 8689801 := bstep (se 2 (by rfl) ⟨3258675, by rfl⟩ : syracuseStep 8689801 = 6517351) B6517351
theorem B11586401 : Blo 2287435 11586401 := bstep (se 2 (by rfl) ⟨4344900, by rfl⟩ : syracuseStep 11586401 = 8689801) B8689801
theorem B7724267 : Blo 2287435 7724267 := bstep (se 1 (by rfl) ⟨5793200, by rfl⟩ : syracuseStep 7724267 = 11586401) B11586401
theorem B5149511 : Blo 2287435 5149511 := bstep (se 1 (by rfl) ⟨3862133, by rfl⟩ : syracuseStep 5149511 = 7724267) B7724267
theorem B3433007 : Blo 2287435 3433007 := bstep (se 1 (by rfl) ⟨2574755, by rfl⟩ : syracuseStep 3433007 = 5149511) B5149511
theorem B2288671 : Blo 2287435 2288671 := bstep (se 1 (by rfl) ⟨1716503, by rfl⟩ : syracuseStep 2288671 = 3433007) B3433007
theorem B3433013 : Blo 2287435 3433013 := bbase (se 5 (by rfl) ⟨160922, by rfl⟩ : syracuseStep 3433013 = 321845) (by norm_num)
theorem B2288675 : Blo 2287435 2288675 := bstep (se 1 (by rfl) ⟨1716506, by rfl⟩ : syracuseStep 2288675 = 3433013) B3433013
theorem B5793221 : Blo 2287435 5793221 := bbase (se 4 (by rfl) ⟨543114, by rfl⟩ : syracuseStep 5793221 = 1086229) (by norm_num)
theorem B3862147 : Blo 2287435 3862147 := bstep (se 1 (by rfl) ⟨2896610, by rfl⟩ : syracuseStep 3862147 = 5793221) B5793221
theorem B5149529 : Blo 2287435 5149529 := bstep (se 2 (by rfl) ⟨1931073, by rfl⟩ : syracuseStep 5149529 = 3862147) B3862147
theorem B3433019 : Blo 2287435 3433019 := bstep (se 1 (by rfl) ⟨2574764, by rfl⟩ : syracuseStep 3433019 = 5149529) B5149529
theorem B2288679 : Blo 2287435 2288679 := bstep (se 1 (by rfl) ⟨1716509, by rfl⟩ : syracuseStep 2288679 = 3433019) B3433019
theorem B2574769 : Blo 2287435 2574769 := bbase (se 2 (by rfl) ⟨965538, by rfl⟩ : syracuseStep 2574769 = 1931077) (by norm_num)
theorem B3433025 : Blo 2287435 3433025 := bstep (se 2 (by rfl) ⟨1287384, by rfl⟩ : syracuseStep 3433025 = 2574769) B2574769
theorem B2288683 : Blo 2287435 2288683 := bstep (se 1 (by rfl) ⟨1716512, by rfl⟩ : syracuseStep 2288683 = 3433025) B3433025
theorem B6517397 : Blo 2287435 6517397 := bbase (se 6 (by rfl) ⟨152751, by rfl⟩ : syracuseStep 6517397 = 305503) (by norm_num)
theorem B4344931 : Blo 2287435 4344931 := bstep (se 1 (by rfl) ⟨3258698, by rfl⟩ : syracuseStep 4344931 = 6517397) B6517397
theorem B5793241 : Blo 2287435 5793241 := bstep (se 2 (by rfl) ⟨2172465, by rfl⟩ : syracuseStep 5793241 = 4344931) B4344931
theorem B7724321 : Blo 2287435 7724321 := bstep (se 2 (by rfl) ⟨2896620, by rfl⟩ : syracuseStep 7724321 = 5793241) B5793241
theorem B5149547 : Blo 2287435 5149547 := bstep (se 1 (by rfl) ⟨3862160, by rfl⟩ : syracuseStep 5149547 = 7724321) B7724321
theorem B3433031 : Blo 2287435 3433031 := bstep (se 1 (by rfl) ⟨2574773, by rfl⟩ : syracuseStep 3433031 = 5149547) B5149547
theorem B2288687 : Blo 2287435 2288687 := bstep (se 1 (by rfl) ⟨1716515, by rfl⟩ : syracuseStep 2288687 = 3433031) B3433031
theorem B3433037 : Blo 2287435 3433037 := bbase (se 3 (by rfl) ⟨643694, by rfl⟩ : syracuseStep 3433037 = 1287389) (by norm_num)
theorem B2288691 : Blo 2287435 2288691 := bstep (se 1 (by rfl) ⟨1716518, by rfl⟩ : syracuseStep 2288691 = 3433037) B3433037
theorem B5149565 : Blo 2287435 5149565 := bbase (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) (by norm_num)
theorem B3433043 : Blo 2287435 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B2288695 : Blo 2287435 2288695 := bstep (se 1 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 2288695 = 3433043) B3433043
theorem B3862181 : Blo 2287435 3862181 := bbase (se 4 (by rfl) ⟨362079, by rfl⟩ : syracuseStep 3862181 = 724159) (by norm_num)
theorem B2574787 : Blo 2287435 2574787 := bstep (se 1 (by rfl) ⟨1931090, by rfl⟩ : syracuseStep 2574787 = 3862181) B3862181
theorem B3433049 : Blo 2287435 3433049 := bstep (se 2 (by rfl) ⟨1287393, by rfl⟩ : syracuseStep 3433049 = 2574787) B2574787
theorem B2288699 : Blo 2287435 2288699 := bstep (se 1 (by rfl) ⟨1716524, by rfl⟩ : syracuseStep 2288699 = 3433049) B3433049
theorem B2444041 : Blo 2287435 2444041 := bbase (se 2 (by rfl) ⟨916515, by rfl⟩ : syracuseStep 2444041 = 1833031) (by norm_num)
theorem B3258721 : Blo 2287435 3258721 := bstep (se 2 (by rfl) ⟨1222020, by rfl⟩ : syracuseStep 3258721 = 2444041) B2444041
theorem B17379845 : Blo 2287435 17379845 := bstep (se 4 (by rfl) ⟨1629360, by rfl⟩ : syracuseStep 17379845 = 3258721) B3258721
theorem B11586563 : Blo 2287435 11586563 := bstep (se 1 (by rfl) ⟨8689922, by rfl⟩ : syracuseStep 11586563 = 17379845) B17379845
theorem B7724375 : Blo 2287435 7724375 := bstep (se 1 (by rfl) ⟨5793281, by rfl⟩ : syracuseStep 7724375 = 11586563) B11586563
theorem B5149583 : Blo 2287435 5149583 := bstep (se 1 (by rfl) ⟨3862187, by rfl⟩ : syracuseStep 5149583 = 7724375) B7724375
theorem B3433055 : Blo 2287435 3433055 := bstep (se 1 (by rfl) ⟨2574791, by rfl⟩ : syracuseStep 3433055 = 5149583) B5149583
theorem B2288703 : Blo 2287435 2288703 := bstep (se 1 (by rfl) ⟨1716527, by rfl⟩ : syracuseStep 2288703 = 3433055) B3433055
theorem B3433061 : Blo 2287435 3433061 := bbase (se 4 (by rfl) ⟨321849, by rfl⟩ : syracuseStep 3433061 = 643699) (by norm_num)
theorem B2288707 : Blo 2287435 2288707 := bstep (se 1 (by rfl) ⟨1716530, by rfl⟩ : syracuseStep 2288707 = 3433061) B3433061
theorem B3258733 : Blo 2287435 3258733 := bbase (se 3 (by rfl) ⟨611012, by rfl⟩ : syracuseStep 3258733 = 1222025) (by norm_num)
theorem B4344977 : Blo 2287435 4344977 := bstep (se 2 (by rfl) ⟨1629366, by rfl⟩ : syracuseStep 4344977 = 3258733) B3258733
theorem B2896651 : Blo 2287435 2896651 := bstep (se 1 (by rfl) ⟨2172488, by rfl⟩ : syracuseStep 2896651 = 4344977) B4344977
theorem B3862201 : Blo 2287435 3862201 := bstep (se 2 (by rfl) ⟨1448325, by rfl⟩ : syracuseStep 3862201 = 2896651) B2896651
theorem B5149601 : Blo 2287435 5149601 := bstep (se 2 (by rfl) ⟨1931100, by rfl⟩ : syracuseStep 5149601 = 3862201) B3862201
theorem B3433067 : Blo 2287435 3433067 := bstep (se 1 (by rfl) ⟨2574800, by rfl⟩ : syracuseStep 3433067 = 5149601) B5149601
theorem B2288711 : Blo 2287435 2288711 := bstep (se 1 (by rfl) ⟨1716533, by rfl⟩ : syracuseStep 2288711 = 3433067) B3433067
theorem B2574805 : Blo 2287435 2574805 := bbase (se 7 (by rfl) ⟨30173, by rfl⟩ : syracuseStep 2574805 = 60347) (by norm_num)
theorem B3433073 : Blo 2287435 3433073 := bstep (se 2 (by rfl) ⟨1287402, by rfl⟩ : syracuseStep 3433073 = 2574805) B2574805
theorem B2288715 : Blo 2287435 2288715 := bstep (se 1 (by rfl) ⟨1716536, by rfl⟩ : syracuseStep 2288715 = 3433073) B3433073
theorem B2896661 : Blo 2287435 2896661 := bbase (se 6 (by rfl) ⟨67890, by rfl⟩ : syracuseStep 2896661 = 135781) (by norm_num)
theorem B7724429 : Blo 2287435 7724429 := bstep (se 3 (by rfl) ⟨1448330, by rfl⟩ : syracuseStep 7724429 = 2896661) B2896661
theorem B5149619 : Blo 2287435 5149619 := bstep (se 1 (by rfl) ⟨3862214, by rfl⟩ : syracuseStep 5149619 = 7724429) B7724429
theorem B3433079 : Blo 2287435 3433079 := bstep (se 1 (by rfl) ⟨2574809, by rfl⟩ : syracuseStep 3433079 = 5149619) B5149619
theorem B2288719 : Blo 2287435 2288719 := bstep (se 1 (by rfl) ⟨1716539, by rfl⟩ : syracuseStep 2288719 = 3433079) B3433079
theorem B3433085 : Blo 2287435 3433085 := bbase (se 3 (by rfl) ⟨643703, by rfl⟩ : syracuseStep 3433085 = 1287407) (by norm_num)
theorem B2288723 : Blo 2287435 2288723 := bstep (se 1 (by rfl) ⟨1716542, by rfl⟩ : syracuseStep 2288723 = 3433085) B3433085
theorem B5149637 : Blo 2287435 5149637 := bbase (se 4 (by rfl) ⟨482778, by rfl⟩ : syracuseStep 5149637 = 965557) (by norm_num)
theorem B3433091 : Blo 2287435 3433091 := bstep (se 1 (by rfl) ⟨2574818, by rfl⟩ : syracuseStep 3433091 = 5149637) B5149637
theorem B2288727 : Blo 2287435 2288727 := bstep (se 1 (by rfl) ⟨1716545, by rfl⟩ : syracuseStep 2288727 = 3433091) B3433091
theorem B5219909 : Blo 2287435 5219909 := bbase (se 4 (by rfl) ⟨489366, by rfl⟩ : syracuseStep 5219909 = 978733) (by norm_num)
theorem B3479939 : Blo 2287435 3479939 := bstep (se 1 (by rfl) ⟨2609954, by rfl⟩ : syracuseStep 3479939 = 5219909) B5219909
theorem B2319959 : Blo 2287435 2319959 := bstep (se 1 (by rfl) ⟨1739969, by rfl⟩ : syracuseStep 2319959 = 3479939) B3479939
theorem B6186557 : Blo 2287435 6186557 := bstep (se 3 (by rfl) ⟨1159979, by rfl⟩ : syracuseStep 6186557 = 2319959) B2319959
theorem B4124371 : Blo 2287435 4124371 := bstep (se 1 (by rfl) ⟨3093278, by rfl⟩ : syracuseStep 4124371 = 6186557) B6186557
theorem B5499161 : Blo 2287435 5499161 := bstep (se 2 (by rfl) ⟨2062185, by rfl⟩ : syracuseStep 5499161 = 4124371) B4124371
theorem B3666107 : Blo 2287435 3666107 := bstep (se 1 (by rfl) ⟨2749580, by rfl⟩ : syracuseStep 3666107 = 5499161) B5499161
theorem B9776285 : Blo 2287435 9776285 := bstep (se 3 (by rfl) ⟨1833053, by rfl⟩ : syracuseStep 9776285 = 3666107) B3666107
theorem B6517523 : Blo 2287435 6517523 := bstep (se 1 (by rfl) ⟨4888142, by rfl⟩ : syracuseStep 6517523 = 9776285) B9776285
theorem B4345015 : Blo 2287435 4345015 := bstep (se 1 (by rfl) ⟨3258761, by rfl⟩ : syracuseStep 4345015 = 6517523) B6517523
theorem B5793353 : Blo 2287435 5793353 := bstep (se 2 (by rfl) ⟨2172507, by rfl⟩ : syracuseStep 5793353 = 4345015) B4345015
theorem B3862235 : Blo 2287435 3862235 := bstep (se 1 (by rfl) ⟨2896676, by rfl⟩ : syracuseStep 3862235 = 5793353) B5793353
theorem B2574823 : Blo 2287435 2574823 := bstep (se 1 (by rfl) ⟨1931117, by rfl⟩ : syracuseStep 2574823 = 3862235) B3862235
theorem B3433097 : Blo 2287435 3433097 := bstep (se 2 (by rfl) ⟨1287411, by rfl⟩ : syracuseStep 3433097 = 2574823) B2574823
theorem B2288731 : Blo 2287435 2288731 := bstep (se 1 (by rfl) ⟨1716548, by rfl⟩ : syracuseStep 2288731 = 3433097) B3433097
theorem B11586725 : Blo 2287435 11586725 := bbase (se 4 (by rfl) ⟨1086255, by rfl⟩ : syracuseStep 11586725 = 2172511) (by norm_num)
theorem B7724483 : Blo 2287435 7724483 := bstep (se 1 (by rfl) ⟨5793362, by rfl⟩ : syracuseStep 7724483 = 11586725) B11586725
theorem B5149655 : Blo 2287435 5149655 := bstep (se 1 (by rfl) ⟨3862241, by rfl⟩ : syracuseStep 5149655 = 7724483) B7724483
theorem B3433103 : Blo 2287435 3433103 := bstep (se 1 (by rfl) ⟨2574827, by rfl⟩ : syracuseStep 3433103 = 5149655) B5149655
theorem B2288735 : Blo 2287435 2288735 := bstep (se 1 (by rfl) ⟨1716551, by rfl⟩ : syracuseStep 2288735 = 3433103) B3433103
theorem B3433109 : Blo 2287435 3433109 := bbase (se 6 (by rfl) ⟨80463, by rfl⟩ : syracuseStep 3433109 = 160927) (by norm_num)
theorem B2288739 : Blo 2287435 2288739 := bstep (se 1 (by rfl) ⟨1716554, by rfl⟩ : syracuseStep 2288739 = 3433109) B3433109
theorem B3968365 : Blo 2287435 3968365 := bbase (se 3 (by rfl) ⟨744068, by rfl⟩ : syracuseStep 3968365 = 1488137) (by norm_num)
theorem B5291153 : Blo 2287435 5291153 := bstep (se 2 (by rfl) ⟨1984182, by rfl⟩ : syracuseStep 5291153 = 3968365) B3968365
theorem B3527435 : Blo 2287435 3527435 := bstep (se 1 (by rfl) ⟨2645576, by rfl⟩ : syracuseStep 3527435 = 5291153) B5291153
theorem B9406493 : Blo 2287435 9406493 := bstep (se 3 (by rfl) ⟨1763717, by rfl⟩ : syracuseStep 9406493 = 3527435) B3527435
theorem B6270995 : Blo 2287435 6270995 := bstep (se 1 (by rfl) ⟨4703246, by rfl⟩ : syracuseStep 6270995 = 9406493) B9406493
theorem B4180663 : Blo 2287435 4180663 := bstep (se 1 (by rfl) ⟨3135497, by rfl⟩ : syracuseStep 4180663 = 6270995) B6270995
theorem B22296869 : Blo 2287435 22296869 := bstep (se 4 (by rfl) ⟨2090331, by rfl⟩ : syracuseStep 22296869 = 4180663) B4180663
theorem B14864579 : Blo 2287435 14864579 := bstep (se 1 (by rfl) ⟨11148434, by rfl⟩ : syracuseStep 14864579 = 22296869) B22296869
theorem B9909719 : Blo 2287435 9909719 := bstep (se 1 (by rfl) ⟨7432289, by rfl⟩ : syracuseStep 9909719 = 14864579) B14864579
theorem B6606479 : Blo 2287435 6606479 := bstep (se 1 (by rfl) ⟨4954859, by rfl⟩ : syracuseStep 6606479 = 9909719) B9909719
theorem B17617277 : Blo 2287435 17617277 := bstep (se 3 (by rfl) ⟨3303239, by rfl⟩ : syracuseStep 17617277 = 6606479) B6606479
theorem B11744851 : Blo 2287435 11744851 := bstep (se 1 (by rfl) ⟨8808638, by rfl⟩ : syracuseStep 11744851 = 17617277) B17617277
theorem B15659801 : Blo 2287435 15659801 := bstep (se 2 (by rfl) ⟨5872425, by rfl⟩ : syracuseStep 15659801 = 11744851) B11744851
theorem B10439867 : Blo 2287435 10439867 := bstep (se 1 (by rfl) ⟨7829900, by rfl⟩ : syracuseStep 10439867 = 15659801) B15659801
theorem B27839645 : Blo 2287435 27839645 := bstep (se 3 (by rfl) ⟨5219933, by rfl⟩ : syracuseStep 27839645 = 10439867) B10439867
theorem B18559763 : Blo 2287435 18559763 := bstep (se 1 (by rfl) ⟨13919822, by rfl⟩ : syracuseStep 18559763 = 27839645) B27839645
theorem B12373175 : Blo 2287435 12373175 := bstep (se 1 (by rfl) ⟨9279881, by rfl⟩ : syracuseStep 12373175 = 18559763) B18559763
theorem B32995133 : Blo 2287435 32995133 := bstep (se 3 (by rfl) ⟨6186587, by rfl⟩ : syracuseStep 32995133 = 12373175) B12373175
theorem B21996755 : Blo 2287435 21996755 := bstep (se 1 (by rfl) ⟨16497566, by rfl⟩ : syracuseStep 21996755 = 32995133) B32995133
theorem B14664503 : Blo 2287435 14664503 := bstep (se 1 (by rfl) ⟨10998377, by rfl⟩ : syracuseStep 14664503 = 21996755) B21996755
theorem B9776335 : Blo 2287435 9776335 := bstep (se 1 (by rfl) ⟨7332251, by rfl⟩ : syracuseStep 9776335 = 14664503) B14664503
theorem B13035113 : Blo 2287435 13035113 := bstep (se 2 (by rfl) ⟨4888167, by rfl⟩ : syracuseStep 13035113 = 9776335) B9776335
theorem B8690075 : Blo 2287435 8690075 := bstep (se 1 (by rfl) ⟨6517556, by rfl⟩ : syracuseStep 8690075 = 13035113) B13035113
theorem B5793383 : Blo 2287435 5793383 := bstep (se 1 (by rfl) ⟨4345037, by rfl⟩ : syracuseStep 5793383 = 8690075) B8690075
theorem B3862255 : Blo 2287435 3862255 := bstep (se 1 (by rfl) ⟨2896691, by rfl⟩ : syracuseStep 3862255 = 5793383) B5793383
theorem B5149673 : Blo 2287435 5149673 := bstep (se 2 (by rfl) ⟨1931127, by rfl⟩ : syracuseStep 5149673 = 3862255) B3862255
theorem B3433115 : Blo 2287435 3433115 := bstep (se 1 (by rfl) ⟨2574836, by rfl⟩ : syracuseStep 3433115 = 5149673) B5149673
theorem B2288743 : Blo 2287435 2288743 := bstep (se 1 (by rfl) ⟨1716557, by rfl⟩ : syracuseStep 2288743 = 3433115) B3433115
theorem B2574841 : Blo 2287435 2574841 := bbase (se 2 (by rfl) ⟨965565, by rfl⟩ : syracuseStep 2574841 = 1931131) (by norm_num)
theorem B3433121 : Blo 2287435 3433121 := bstep (se 2 (by rfl) ⟨1287420, by rfl⟩ : syracuseStep 3433121 = 2574841) B2574841
theorem B2288747 : Blo 2287435 2288747 := bstep (se 1 (by rfl) ⟨1716560, by rfl⟩ : syracuseStep 2288747 = 3433121) B3433121
theorem B7332277 : Blo 2287435 7332277 := bbase (se 5 (by rfl) ⟨343700, by rfl⟩ : syracuseStep 7332277 = 687401) (by norm_num)
theorem B9776369 : Blo 2287435 9776369 := bstep (se 2 (by rfl) ⟨3666138, by rfl⟩ : syracuseStep 9776369 = 7332277) B7332277
theorem B6517579 : Blo 2287435 6517579 := bstep (se 1 (by rfl) ⟨4888184, by rfl⟩ : syracuseStep 6517579 = 9776369) B9776369
theorem B8690105 : Blo 2287435 8690105 := bstep (se 2 (by rfl) ⟨3258789, by rfl⟩ : syracuseStep 8690105 = 6517579) B6517579
theorem B5793403 : Blo 2287435 5793403 := bstep (se 1 (by rfl) ⟨4345052, by rfl⟩ : syracuseStep 5793403 = 8690105) B8690105
theorem B7724537 : Blo 2287435 7724537 := bstep (se 2 (by rfl) ⟨2896701, by rfl⟩ : syracuseStep 7724537 = 5793403) B5793403
theorem B5149691 : Blo 2287435 5149691 := bstep (se 1 (by rfl) ⟨3862268, by rfl⟩ : syracuseStep 5149691 = 7724537) B7724537
theorem B3433127 : Blo 2287435 3433127 := bstep (se 1 (by rfl) ⟨2574845, by rfl⟩ : syracuseStep 3433127 = 5149691) B5149691
theorem B2288751 : Blo 2287435 2288751 := bstep (se 1 (by rfl) ⟨1716563, by rfl⟩ : syracuseStep 2288751 = 3433127) B3433127
theorem B3433133 : Blo 2287435 3433133 := bbase (se 3 (by rfl) ⟨643712, by rfl⟩ : syracuseStep 3433133 = 1287425) (by norm_num)
theorem B2288755 : Blo 2287435 2288755 := bstep (se 1 (by rfl) ⟨1716566, by rfl⟩ : syracuseStep 2288755 = 3433133) B3433133
theorem B5149709 : Blo 2287435 5149709 := bbase (se 3 (by rfl) ⟨965570, by rfl⟩ : syracuseStep 5149709 = 1931141) (by norm_num)
theorem B3433139 : Blo 2287435 3433139 := bstep (se 1 (by rfl) ⟨2574854, by rfl⟩ : syracuseStep 3433139 = 5149709) B5149709
theorem B2288759 : Blo 2287435 2288759 := bstep (se 1 (by rfl) ⟨1716569, by rfl⟩ : syracuseStep 2288759 = 3433139) B3433139
theorem B2896717 : Blo 2287435 2896717 := bbase (se 3 (by rfl) ⟨543134, by rfl⟩ : syracuseStep 2896717 = 1086269) (by norm_num)
theorem B3862289 : Blo 2287435 3862289 := bstep (se 2 (by rfl) ⟨1448358, by rfl⟩ : syracuseStep 3862289 = 2896717) B2896717
theorem B2574859 : Blo 2287435 2574859 := bstep (se 1 (by rfl) ⟨1931144, by rfl⟩ : syracuseStep 2574859 = 3862289) B3862289
theorem B3433145 : Blo 2287435 3433145 := bstep (se 2 (by rfl) ⟨1287429, by rfl⟩ : syracuseStep 3433145 = 2574859) B2574859
theorem B2288763 : Blo 2287435 2288763 := bstep (se 1 (by rfl) ⟨1716572, by rfl⟩ : syracuseStep 2288763 = 3433145) B3433145
theorem B8361413 : Blo 2287435 8361413 := bbase (se 4 (by rfl) ⟨783882, by rfl⟩ : syracuseStep 8361413 = 1567765) (by norm_num)
theorem B5574275 : Blo 2287435 5574275 := bstep (se 1 (by rfl) ⟨4180706, by rfl⟩ : syracuseStep 5574275 = 8361413) B8361413
theorem B3716183 : Blo 2287435 3716183 := bstep (se 1 (by rfl) ⟨2787137, by rfl⟩ : syracuseStep 3716183 = 5574275) B5574275
theorem B9909821 : Blo 2287435 9909821 := bstep (se 3 (by rfl) ⟨1858091, by rfl⟩ : syracuseStep 9909821 = 3716183) B3716183
theorem B26426189 : Blo 2287435 26426189 := bstep (se 3 (by rfl) ⟨4954910, by rfl⟩ : syracuseStep 26426189 = 9909821) B9909821
theorem B17617459 : Blo 2287435 17617459 := bstep (se 1 (by rfl) ⟨13213094, by rfl⟩ : syracuseStep 17617459 = 26426189) B26426189
theorem B23489945 : Blo 2287435 23489945 := bstep (se 2 (by rfl) ⟨8808729, by rfl⟩ : syracuseStep 23489945 = 17617459) B17617459
theorem B15659963 : Blo 2287435 15659963 := bstep (se 1 (by rfl) ⟨11744972, by rfl⟩ : syracuseStep 15659963 = 23489945) B23489945
theorem B10439975 : Blo 2287435 10439975 := bstep (se 1 (by rfl) ⟨7829981, by rfl⟩ : syracuseStep 10439975 = 15659963) B15659963
theorem B27839933 : Blo 2287435 27839933 := bstep (se 3 (by rfl) ⟨5219987, by rfl⟩ : syracuseStep 27839933 = 10439975) B10439975
theorem B18559955 : Blo 2287435 18559955 := bstep (se 1 (by rfl) ⟨13919966, by rfl⟩ : syracuseStep 18559955 = 27839933) B27839933
theorem B49493213 : Blo 2287435 49493213 := bstep (se 3 (by rfl) ⟨9279977, by rfl⟩ : syracuseStep 49493213 = 18559955) B18559955
theorem B32995475 : Blo 2287435 32995475 := bstep (se 1 (by rfl) ⟨24746606, by rfl⟩ : syracuseStep 32995475 = 49493213) B49493213
theorem B21996983 : Blo 2287435 21996983 := bstep (se 1 (by rfl) ⟨16497737, by rfl⟩ : syracuseStep 21996983 = 32995475) B32995475
theorem B14664655 : Blo 2287435 14664655 := bstep (se 1 (by rfl) ⟨10998491, by rfl⟩ : syracuseStep 14664655 = 21996983) B21996983
theorem B19552873 : Blo 2287435 19552873 := bstep (se 2 (by rfl) ⟨7332327, by rfl⟩ : syracuseStep 19552873 = 14664655) B14664655
theorem B26070497 : Blo 2287435 26070497 := bstep (se 2 (by rfl) ⟨9776436, by rfl⟩ : syracuseStep 26070497 = 19552873) B19552873
theorem B17380331 : Blo 2287435 17380331 := bstep (se 1 (by rfl) ⟨13035248, by rfl⟩ : syracuseStep 17380331 = 26070497) B26070497
theorem B11586887 : Blo 2287435 11586887 := bstep (se 1 (by rfl) ⟨8690165, by rfl⟩ : syracuseStep 11586887 = 17380331) B17380331
theorem B7724591 : Blo 2287435 7724591 := bstep (se 1 (by rfl) ⟨5793443, by rfl⟩ : syracuseStep 7724591 = 11586887) B11586887
theorem B5149727 : Blo 2287435 5149727 := bstep (se 1 (by rfl) ⟨3862295, by rfl⟩ : syracuseStep 5149727 = 7724591) B7724591
theorem B3433151 : Blo 2287435 3433151 := bstep (se 1 (by rfl) ⟨2574863, by rfl⟩ : syracuseStep 3433151 = 5149727) B5149727
theorem B2288767 : Blo 2287435 2288767 := bstep (se 1 (by rfl) ⟨1716575, by rfl⟩ : syracuseStep 2288767 = 3433151) B3433151
theorem B3433157 : Blo 2287435 3433157 := bbase (se 4 (by rfl) ⟨321858, by rfl⟩ : syracuseStep 3433157 = 643717) (by norm_num)
theorem B2288771 : Blo 2287435 2288771 := bstep (se 1 (by rfl) ⟨1716578, by rfl⟩ : syracuseStep 2288771 = 3433157) B3433157
theorem B3862309 : Blo 2287435 3862309 := bbase (se 4 (by rfl) ⟨362091, by rfl⟩ : syracuseStep 3862309 = 724183) (by norm_num)
theorem B5149745 : Blo 2287435 5149745 := bstep (se 2 (by rfl) ⟨1931154, by rfl⟩ : syracuseStep 5149745 = 3862309) B3862309
theorem B3433163 : Blo 2287435 3433163 := bstep (se 1 (by rfl) ⟨2574872, by rfl⟩ : syracuseStep 3433163 = 5149745) B5149745
theorem B2288775 : Blo 2287435 2288775 := bstep (se 1 (by rfl) ⟨1716581, by rfl⟩ : syracuseStep 2288775 = 3433163) B3433163
theorem B2574877 : Blo 2287435 2574877 := bbase (se 3 (by rfl) ⟨482789, by rfl⟩ : syracuseStep 2574877 = 965579) (by norm_num)
theorem B3433169 : Blo 2287435 3433169 := bstep (se 2 (by rfl) ⟨1287438, by rfl⟩ : syracuseStep 3433169 = 2574877) B2574877
theorem B2288779 : Blo 2287435 2288779 := bstep (se 1 (by rfl) ⟨1716584, by rfl⟩ : syracuseStep 2288779 = 3433169) B3433169
theorem B7724645 : Blo 2287435 7724645 := bbase (se 4 (by rfl) ⟨724185, by rfl⟩ : syracuseStep 7724645 = 1448371) (by norm_num)
theorem B5149763 : Blo 2287435 5149763 := bstep (se 1 (by rfl) ⟨3862322, by rfl⟩ : syracuseStep 5149763 = 7724645) B7724645
theorem B3433175 : Blo 2287435 3433175 := bstep (se 1 (by rfl) ⟨2574881, by rfl⟩ : syracuseStep 3433175 = 5149763) B5149763
theorem B2288783 : Blo 2287435 2288783 := bstep (se 1 (by rfl) ⟨1716587, by rfl⟩ : syracuseStep 2288783 = 3433175) B3433175
theorem B3433181 : Blo 2287435 3433181 := bbase (se 3 (by rfl) ⟨643721, by rfl⟩ : syracuseStep 3433181 = 1287443) (by norm_num)
theorem B2288787 : Blo 2287435 2288787 := bstep (se 1 (by rfl) ⟨1716590, by rfl⟩ : syracuseStep 2288787 = 3433181) B3433181
theorem B5149781 : Blo 2287435 5149781 := bbase (se 8 (by rfl) ⟨30174, by rfl⟩ : syracuseStep 5149781 = 60349) (by norm_num)
theorem B3433187 : Blo 2287435 3433187 := bstep (se 1 (by rfl) ⟨2574890, by rfl⟩ : syracuseStep 3433187 = 5149781) B5149781
theorem B2288791 : Blo 2287435 2288791 := bstep (se 1 (by rfl) ⟨1716593, by rfl⟩ : syracuseStep 2288791 = 3433187) B3433187
theorem B10998629 : Blo 2287435 10998629 := bbase (se 4 (by rfl) ⟨1031121, by rfl⟩ : syracuseStep 10998629 = 2062243) (by norm_num)
theorem B7332419 : Blo 2287435 7332419 := bstep (se 1 (by rfl) ⟨5499314, by rfl⟩ : syracuseStep 7332419 = 10998629) B10998629
theorem B4888279 : Blo 2287435 4888279 := bstep (se 1 (by rfl) ⟨3666209, by rfl⟩ : syracuseStep 4888279 = 7332419) B7332419
theorem B6517705 : Blo 2287435 6517705 := bstep (se 2 (by rfl) ⟨2444139, by rfl⟩ : syracuseStep 6517705 = 4888279) B4888279
theorem B8690273 : Blo 2287435 8690273 := bstep (se 2 (by rfl) ⟨3258852, by rfl⟩ : syracuseStep 8690273 = 6517705) B6517705
theorem B5793515 : Blo 2287435 5793515 := bstep (se 1 (by rfl) ⟨4345136, by rfl⟩ : syracuseStep 5793515 = 8690273) B8690273
theorem B3862343 : Blo 2287435 3862343 := bstep (se 1 (by rfl) ⟨2896757, by rfl⟩ : syracuseStep 3862343 = 5793515) B5793515
theorem B2574895 : Blo 2287435 2574895 := bstep (se 1 (by rfl) ⟨1931171, by rfl⟩ : syracuseStep 2574895 = 3862343) B3862343
theorem B3433193 : Blo 2287435 3433193 := bstep (se 2 (by rfl) ⟨1287447, by rfl⟩ : syracuseStep 3433193 = 2574895) B2574895
theorem B2288795 : Blo 2287435 2288795 := bstep (se 1 (by rfl) ⟨1716596, by rfl⟩ : syracuseStep 2288795 = 3433193) B3433193
theorem B8808853 : Blo 2287435 8808853 := bbase (se 6 (by rfl) ⟨206457, by rfl⟩ : syracuseStep 8808853 = 412915) (by norm_num)
theorem B11745137 : Blo 2287435 11745137 := bstep (se 2 (by rfl) ⟨4404426, by rfl⟩ : syracuseStep 11745137 = 8808853) B8808853
theorem B7830091 : Blo 2287435 7830091 := bstep (se 1 (by rfl) ⟨5872568, by rfl⟩ : syracuseStep 7830091 = 11745137) B11745137
theorem B41760485 : Blo 2287435 41760485 := bstep (se 4 (by rfl) ⟨3915045, by rfl⟩ : syracuseStep 41760485 = 7830091) B7830091
theorem B27840323 : Blo 2287435 27840323 := bstep (se 1 (by rfl) ⟨20880242, by rfl⟩ : syracuseStep 27840323 = 41760485) B41760485
theorem B18560215 : Blo 2287435 18560215 := bstep (se 1 (by rfl) ⟨13920161, by rfl⟩ : syracuseStep 18560215 = 27840323) B27840323
theorem B24746953 : Blo 2287435 24746953 := bstep (se 2 (by rfl) ⟨9280107, by rfl⟩ : syracuseStep 24746953 = 18560215) B18560215
theorem B32995937 : Blo 2287435 32995937 := bstep (se 2 (by rfl) ⟨12373476, by rfl⟩ : syracuseStep 32995937 = 24746953) B24746953
theorem B21997291 : Blo 2287435 21997291 := bstep (se 1 (by rfl) ⟨16497968, by rfl⟩ : syracuseStep 21997291 = 32995937) B32995937
theorem B29329721 : Blo 2287435 29329721 := bstep (se 2 (by rfl) ⟨10998645, by rfl⟩ : syracuseStep 29329721 = 21997291) B21997291
theorem B19553147 : Blo 2287435 19553147 := bstep (se 1 (by rfl) ⟨14664860, by rfl⟩ : syracuseStep 19553147 = 29329721) B29329721
theorem B13035431 : Blo 2287435 13035431 := bstep (se 1 (by rfl) ⟨9776573, by rfl⟩ : syracuseStep 13035431 = 19553147) B19553147
theorem B8690287 : Blo 2287435 8690287 := bstep (se 1 (by rfl) ⟨6517715, by rfl⟩ : syracuseStep 8690287 = 13035431) B13035431
theorem B11587049 : Blo 2287435 11587049 := bstep (se 2 (by rfl) ⟨4345143, by rfl⟩ : syracuseStep 11587049 = 8690287) B8690287
theorem B7724699 : Blo 2287435 7724699 := bstep (se 1 (by rfl) ⟨5793524, by rfl⟩ : syracuseStep 7724699 = 11587049) B11587049
theorem B5149799 : Blo 2287435 5149799 := bstep (se 1 (by rfl) ⟨3862349, by rfl⟩ : syracuseStep 5149799 = 7724699) B7724699
theorem B3433199 : Blo 2287435 3433199 := bstep (se 1 (by rfl) ⟨2574899, by rfl⟩ : syracuseStep 3433199 = 5149799) B5149799
theorem B2288799 : Blo 2287435 2288799 := bstep (se 1 (by rfl) ⟨1716599, by rfl⟩ : syracuseStep 2288799 = 3433199) B3433199
theorem B3433205 : Blo 2287435 3433205 := bbase (se 5 (by rfl) ⟨160931, by rfl⟩ : syracuseStep 3433205 = 321863) (by norm_num)
theorem B2288803 : Blo 2287435 2288803 := bstep (se 1 (by rfl) ⟨1716602, by rfl⟩ : syracuseStep 2288803 = 3433205) B3433205
theorem B4180781 : Blo 2287435 4180781 := bbase (se 3 (by rfl) ⟨783896, by rfl⟩ : syracuseStep 4180781 = 1567793) (by norm_num)
theorem B11148749 : Blo 2287435 11148749 := bstep (se 3 (by rfl) ⟨2090390, by rfl⟩ : syracuseStep 11148749 = 4180781) B4180781
theorem B7432499 : Blo 2287435 7432499 := bstep (se 1 (by rfl) ⟨5574374, by rfl⟩ : syracuseStep 7432499 = 11148749) B11148749
theorem B19819997 : Blo 2287435 19819997 := bstep (se 3 (by rfl) ⟨3716249, by rfl⟩ : syracuseStep 19819997 = 7432499) B7432499
theorem B13213331 : Blo 2287435 13213331 := bstep (se 1 (by rfl) ⟨9909998, by rfl⟩ : syracuseStep 13213331 = 19819997) B19819997
theorem B8808887 : Blo 2287435 8808887 := bstep (se 1 (by rfl) ⟨6606665, by rfl⟩ : syracuseStep 8808887 = 13213331) B13213331
theorem B5872591 : Blo 2287435 5872591 := bstep (se 1 (by rfl) ⟨4404443, by rfl⟩ : syracuseStep 5872591 = 8808887) B8808887
theorem B7830121 : Blo 2287435 7830121 := bstep (se 2 (by rfl) ⟨2936295, by rfl⟩ : syracuseStep 7830121 = 5872591) B5872591
theorem B10440161 : Blo 2287435 10440161 := bstep (se 2 (by rfl) ⟨3915060, by rfl⟩ : syracuseStep 10440161 = 7830121) B7830121
theorem B6960107 : Blo 2287435 6960107 := bstep (se 1 (by rfl) ⟨5220080, by rfl⟩ : syracuseStep 6960107 = 10440161) B10440161
theorem B18560285 : Blo 2287435 18560285 := bstep (se 3 (by rfl) ⟨3480053, by rfl⟩ : syracuseStep 18560285 = 6960107) B6960107
theorem B12373523 : Blo 2287435 12373523 := bstep (se 1 (by rfl) ⟨9280142, by rfl⟩ : syracuseStep 12373523 = 18560285) B18560285
theorem B8249015 : Blo 2287435 8249015 := bstep (se 1 (by rfl) ⟨6186761, by rfl⟩ : syracuseStep 8249015 = 12373523) B12373523
theorem B5499343 : Blo 2287435 5499343 := bstep (se 1 (by rfl) ⟨4124507, by rfl⟩ : syracuseStep 5499343 = 8249015) B8249015
theorem B7332457 : Blo 2287435 7332457 := bstep (se 2 (by rfl) ⟨2749671, by rfl⟩ : syracuseStep 7332457 = 5499343) B5499343
theorem B9776609 : Blo 2287435 9776609 := bstep (se 2 (by rfl) ⟨3666228, by rfl⟩ : syracuseStep 9776609 = 7332457) B7332457
theorem B6517739 : Blo 2287435 6517739 := bstep (se 1 (by rfl) ⟨4888304, by rfl⟩ : syracuseStep 6517739 = 9776609) B9776609
theorem B4345159 : Blo 2287435 4345159 := bstep (se 1 (by rfl) ⟨3258869, by rfl⟩ : syracuseStep 4345159 = 6517739) B6517739
theorem B5793545 : Blo 2287435 5793545 := bstep (se 2 (by rfl) ⟨2172579, by rfl⟩ : syracuseStep 5793545 = 4345159) B4345159
theorem B3862363 : Blo 2287435 3862363 := bstep (se 1 (by rfl) ⟨2896772, by rfl⟩ : syracuseStep 3862363 = 5793545) B5793545
theorem B5149817 : Blo 2287435 5149817 := bstep (se 2 (by rfl) ⟨1931181, by rfl⟩ : syracuseStep 5149817 = 3862363) B3862363
theorem B3433211 : Blo 2287435 3433211 := bstep (se 1 (by rfl) ⟨2574908, by rfl⟩ : syracuseStep 3433211 = 5149817) B5149817
theorem B2288807 : Blo 2287435 2288807 := bstep (se 1 (by rfl) ⟨1716605, by rfl⟩ : syracuseStep 2288807 = 3433211) B3433211
theorem B2574913 : Blo 2287435 2574913 := bbase (se 2 (by rfl) ⟨965592, by rfl⟩ : syracuseStep 2574913 = 1931185) (by norm_num)
theorem B3433217 : Blo 2287435 3433217 := bstep (se 2 (by rfl) ⟨1287456, by rfl⟩ : syracuseStep 3433217 = 2574913) B2574913
theorem B2288811 : Blo 2287435 2288811 := bstep (se 1 (by rfl) ⟨1716608, by rfl⟩ : syracuseStep 2288811 = 3433217) B3433217
theorem B5793565 : Blo 2287435 5793565 := bbase (se 3 (by rfl) ⟨1086293, by rfl⟩ : syracuseStep 5793565 = 2172587) (by norm_num)
theorem B7724753 : Blo 2287435 7724753 := bstep (se 2 (by rfl) ⟨2896782, by rfl⟩ : syracuseStep 7724753 = 5793565) B5793565
theorem B5149835 : Blo 2287435 5149835 := bstep (se 1 (by rfl) ⟨3862376, by rfl⟩ : syracuseStep 5149835 = 7724753) B7724753
theorem B3433223 : Blo 2287435 3433223 := bstep (se 1 (by rfl) ⟨2574917, by rfl⟩ : syracuseStep 3433223 = 5149835) B5149835
theorem B2288815 : Blo 2287435 2288815 := bstep (se 1 (by rfl) ⟨1716611, by rfl⟩ : syracuseStep 2288815 = 3433223) B3433223
theorem B3433229 : Blo 2287435 3433229 := bbase (se 3 (by rfl) ⟨643730, by rfl⟩ : syracuseStep 3433229 = 1287461) (by norm_num)
theorem B2288819 : Blo 2287435 2288819 := bstep (se 1 (by rfl) ⟨1716614, by rfl⟩ : syracuseStep 2288819 = 3433229) B3433229
theorem B5149853 : Blo 2287435 5149853 := bbase (se 3 (by rfl) ⟨965597, by rfl⟩ : syracuseStep 5149853 = 1931195) (by norm_num)
theorem B3433235 : Blo 2287435 3433235 := bstep (se 1 (by rfl) ⟨2574926, by rfl⟩ : syracuseStep 3433235 = 5149853) B5149853
theorem B2288823 : Blo 2287435 2288823 := bstep (se 1 (by rfl) ⟨1716617, by rfl⟩ : syracuseStep 2288823 = 3433235) B3433235
theorem B3862397 : Blo 2287435 3862397 := bbase (se 3 (by rfl) ⟨724199, by rfl⟩ : syracuseStep 3862397 = 1448399) (by norm_num)
theorem B2574931 : Blo 2287435 2574931 := bstep (se 1 (by rfl) ⟨1931198, by rfl⟩ : syracuseStep 2574931 = 3862397) B3862397
theorem B3433241 : Blo 2287435 3433241 := bstep (se 2 (by rfl) ⟨1287465, by rfl⟩ : syracuseStep 3433241 = 2574931) B2574931
theorem B2288827 : Blo 2287435 2288827 := bstep (se 1 (by rfl) ⟨1716620, by rfl⟩ : syracuseStep 2288827 = 3433241) B3433241
theorem B7332533 : Blo 2287435 7332533 := bbase (se 5 (by rfl) ⟨343712, by rfl⟩ : syracuseStep 7332533 = 687425) (by norm_num)
theorem B4888355 : Blo 2287435 4888355 := bstep (se 1 (by rfl) ⟨3666266, by rfl⟩ : syracuseStep 4888355 = 7332533) B7332533
theorem B13035613 : Blo 2287435 13035613 := bstep (se 3 (by rfl) ⟨2444177, by rfl⟩ : syracuseStep 13035613 = 4888355) B4888355
theorem B17380817 : Blo 2287435 17380817 := bstep (se 2 (by rfl) ⟨6517806, by rfl⟩ : syracuseStep 17380817 = 13035613) B13035613
theorem B11587211 : Blo 2287435 11587211 := bstep (se 1 (by rfl) ⟨8690408, by rfl⟩ : syracuseStep 11587211 = 17380817) B17380817
theorem B7724807 : Blo 2287435 7724807 := bstep (se 1 (by rfl) ⟨5793605, by rfl⟩ : syracuseStep 7724807 = 11587211) B11587211
theorem B5149871 : Blo 2287435 5149871 := bstep (se 1 (by rfl) ⟨3862403, by rfl⟩ : syracuseStep 5149871 = 7724807) B7724807
theorem B3433247 : Blo 2287435 3433247 := bstep (se 1 (by rfl) ⟨2574935, by rfl⟩ : syracuseStep 3433247 = 5149871) B5149871
theorem B2288831 : Blo 2287435 2288831 := bstep (se 1 (by rfl) ⟨1716623, by rfl⟩ : syracuseStep 2288831 = 3433247) B3433247
theorem B3433253 : Blo 2287435 3433253 := bbase (se 4 (by rfl) ⟨321867, by rfl⟩ : syracuseStep 3433253 = 643735) (by norm_num)
theorem B2288835 : Blo 2287435 2288835 := bstep (se 1 (by rfl) ⟨1716626, by rfl⟩ : syracuseStep 2288835 = 3433253) B3433253
theorem B2896813 : Blo 2287435 2896813 := bbase (se 3 (by rfl) ⟨543152, by rfl⟩ : syracuseStep 2896813 = 1086305) (by norm_num)
theorem B3862417 : Blo 2287435 3862417 := bstep (se 2 (by rfl) ⟨1448406, by rfl⟩ : syracuseStep 3862417 = 2896813) B2896813
theorem B5149889 : Blo 2287435 5149889 := bstep (se 2 (by rfl) ⟨1931208, by rfl⟩ : syracuseStep 5149889 = 3862417) B3862417
theorem B3433259 : Blo 2287435 3433259 := bstep (se 1 (by rfl) ⟨2574944, by rfl⟩ : syracuseStep 3433259 = 5149889) B5149889
theorem B2288839 : Blo 2287435 2288839 := bstep (se 1 (by rfl) ⟨1716629, by rfl⟩ : syracuseStep 2288839 = 3433259) B3433259
theorem B2574949 : Blo 2287435 2574949 := bbase (se 4 (by rfl) ⟨241401, by rfl⟩ : syracuseStep 2574949 = 482803) (by norm_num)
theorem B3433265 : Blo 2287435 3433265 := bstep (se 2 (by rfl) ⟨1287474, by rfl⟩ : syracuseStep 3433265 = 2574949) B2574949
theorem B2288843 : Blo 2287435 2288843 := bstep (se 1 (by rfl) ⟨1716632, by rfl⟩ : syracuseStep 2288843 = 3433265) B3433265
theorem B3666293 : Blo 2287435 3666293 := bbase (se 5 (by rfl) ⟨171857, by rfl⟩ : syracuseStep 3666293 = 343715) (by norm_num)
theorem B2444195 : Blo 2287435 2444195 := bstep (se 1 (by rfl) ⟨1833146, by rfl⟩ : syracuseStep 2444195 = 3666293) B3666293
theorem B6517853 : Blo 2287435 6517853 := bstep (se 3 (by rfl) ⟨1222097, by rfl⟩ : syracuseStep 6517853 = 2444195) B2444195
theorem B4345235 : Blo 2287435 4345235 := bstep (se 1 (by rfl) ⟨3258926, by rfl⟩ : syracuseStep 4345235 = 6517853) B6517853
theorem B2896823 : Blo 2287435 2896823 := bstep (se 1 (by rfl) ⟨2172617, by rfl⟩ : syracuseStep 2896823 = 4345235) B4345235
theorem B7724861 : Blo 2287435 7724861 := bstep (se 3 (by rfl) ⟨1448411, by rfl⟩ : syracuseStep 7724861 = 2896823) B2896823
theorem B5149907 : Blo 2287435 5149907 := bstep (se 1 (by rfl) ⟨3862430, by rfl⟩ : syracuseStep 5149907 = 7724861) B7724861
theorem B3433271 : Blo 2287435 3433271 := bstep (se 1 (by rfl) ⟨2574953, by rfl⟩ : syracuseStep 3433271 = 5149907) B5149907
theorem B2288847 : Blo 2287435 2288847 := bstep (se 1 (by rfl) ⟨1716635, by rfl⟩ : syracuseStep 2288847 = 3433271) B3433271
theorem B3433277 : Blo 2287435 3433277 := bbase (se 3 (by rfl) ⟨643739, by rfl⟩ : syracuseStep 3433277 = 1287479) (by norm_num)
theorem B2288851 : Blo 2287435 2288851 := bstep (se 1 (by rfl) ⟨1716638, by rfl⟩ : syracuseStep 2288851 = 3433277) B3433277
theorem B5149925 : Blo 2287435 5149925 := bbase (se 4 (by rfl) ⟨482805, by rfl⟩ : syracuseStep 5149925 = 965611) (by norm_num)
theorem B3433283 : Blo 2287435 3433283 := bstep (se 1 (by rfl) ⟨2574962, by rfl⟩ : syracuseStep 3433283 = 5149925) B5149925
theorem B2288855 : Blo 2287435 2288855 := bstep (se 1 (by rfl) ⟨1716641, by rfl⟩ : syracuseStep 2288855 = 3433283) B3433283
theorem B5793677 : Blo 2287435 5793677 := bbase (se 3 (by rfl) ⟨1086314, by rfl⟩ : syracuseStep 5793677 = 2172629) (by norm_num)
theorem B3862451 : Blo 2287435 3862451 := bstep (se 1 (by rfl) ⟨2896838, by rfl⟩ : syracuseStep 3862451 = 5793677) B5793677
theorem B2574967 : Blo 2287435 2574967 := bstep (se 1 (by rfl) ⟨1931225, by rfl⟩ : syracuseStep 2574967 = 3862451) B3862451
theorem B3433289 : Blo 2287435 3433289 := bstep (se 2 (by rfl) ⟨1287483, by rfl⟩ : syracuseStep 3433289 = 2574967) B2574967
theorem B2288859 : Blo 2287435 2288859 := bstep (se 1 (by rfl) ⟨1716644, by rfl⟩ : syracuseStep 2288859 = 3433289) B3433289
theorem B3258949 : Blo 2287435 3258949 := bbase (se 4 (by rfl) ⟨305526, by rfl⟩ : syracuseStep 3258949 = 611053) (by norm_num)
theorem B4345265 : Blo 2287435 4345265 := bstep (se 2 (by rfl) ⟨1629474, by rfl⟩ : syracuseStep 4345265 = 3258949) B3258949
theorem B11587373 : Blo 2287435 11587373 := bstep (se 3 (by rfl) ⟨2172632, by rfl⟩ : syracuseStep 11587373 = 4345265) B4345265
theorem B7724915 : Blo 2287435 7724915 := bstep (se 1 (by rfl) ⟨5793686, by rfl⟩ : syracuseStep 7724915 = 11587373) B11587373
theorem B5149943 : Blo 2287435 5149943 := bstep (se 1 (by rfl) ⟨3862457, by rfl⟩ : syracuseStep 5149943 = 7724915) B7724915
theorem B3433295 : Blo 2287435 3433295 := bstep (se 1 (by rfl) ⟨2574971, by rfl⟩ : syracuseStep 3433295 = 5149943) B5149943
theorem B2288863 : Blo 2287435 2288863 := bstep (se 1 (by rfl) ⟨1716647, by rfl⟩ : syracuseStep 2288863 = 3433295) B3433295
theorem B3433301 : Blo 2287435 3433301 := bbase (se 9 (by rfl) ⟨10058, by rfl⟩ : syracuseStep 3433301 = 20117) (by norm_num)
theorem B2288867 : Blo 2287435 2288867 := bstep (se 1 (by rfl) ⟨1716650, by rfl⟩ : syracuseStep 2288867 = 3433301) B3433301
theorem B7830341 : Blo 2287435 7830341 := bbase (se 4 (by rfl) ⟨734094, by rfl⟩ : syracuseStep 7830341 = 1468189) (by norm_num)
theorem B5220227 : Blo 2287435 5220227 := bstep (se 1 (by rfl) ⟨3915170, by rfl⟩ : syracuseStep 5220227 = 7830341) B7830341
theorem B13920605 : Blo 2287435 13920605 := bstep (se 3 (by rfl) ⟨2610113, by rfl⟩ : syracuseStep 13920605 = 5220227) B5220227
theorem B9280403 : Blo 2287435 9280403 := bstep (se 1 (by rfl) ⟨6960302, by rfl⟩ : syracuseStep 9280403 = 13920605) B13920605
theorem B6186935 : Blo 2287435 6186935 := bstep (se 1 (by rfl) ⟨4640201, by rfl⟩ : syracuseStep 6186935 = 9280403) B9280403
theorem B4124623 : Blo 2287435 4124623 := bstep (se 1 (by rfl) ⟨3093467, by rfl⟩ : syracuseStep 4124623 = 6186935) B6186935
theorem B5499497 : Blo 2287435 5499497 := bstep (se 2 (by rfl) ⟨2062311, by rfl⟩ : syracuseStep 5499497 = 4124623) B4124623
theorem B3666331 : Blo 2287435 3666331 := bstep (se 1 (by rfl) ⟨2749748, by rfl⟩ : syracuseStep 3666331 = 5499497) B5499497
theorem B4888441 : Blo 2287435 4888441 := bstep (se 2 (by rfl) ⟨1833165, by rfl⟩ : syracuseStep 4888441 = 3666331) B3666331
theorem B6517921 : Blo 2287435 6517921 := bstep (se 2 (by rfl) ⟨2444220, by rfl⟩ : syracuseStep 6517921 = 4888441) B4888441
theorem B8690561 : Blo 2287435 8690561 := bstep (se 2 (by rfl) ⟨3258960, by rfl⟩ : syracuseStep 8690561 = 6517921) B6517921
theorem B5793707 : Blo 2287435 5793707 := bstep (se 1 (by rfl) ⟨4345280, by rfl⟩ : syracuseStep 5793707 = 8690561) B8690561
theorem B3862471 : Blo 2287435 3862471 := bstep (se 1 (by rfl) ⟨2896853, by rfl⟩ : syracuseStep 3862471 = 5793707) B5793707
theorem B5149961 : Blo 2287435 5149961 := bstep (se 2 (by rfl) ⟨1931235, by rfl⟩ : syracuseStep 5149961 = 3862471) B3862471
theorem B3433307 : Blo 2287435 3433307 := bstep (se 1 (by rfl) ⟨2574980, by rfl⟩ : syracuseStep 3433307 = 5149961) B5149961
theorem B2288871 : Blo 2287435 2288871 := bstep (se 1 (by rfl) ⟨1716653, by rfl⟩ : syracuseStep 2288871 = 3433307) B3433307
theorem B2574985 : Blo 2287435 2574985 := bbase (se 2 (by rfl) ⟨965619, by rfl⟩ : syracuseStep 2574985 = 1931239) (by norm_num)
theorem B3433313 : Blo 2287435 3433313 := bstep (se 2 (by rfl) ⟨1287492, by rfl⟩ : syracuseStep 3433313 = 2574985) B2574985
theorem B2288875 : Blo 2287435 2288875 := bstep (se 1 (by rfl) ⟨1716656, by rfl⟩ : syracuseStep 2288875 = 3433313) B3433313
theorem B49495637 : Blo 2287435 49495637 := bbase (se 8 (by rfl) ⟨290013, by rfl⟩ : syracuseStep 49495637 = 580027) (by norm_num)
theorem B32997091 : Blo 2287435 32997091 := bstep (se 1 (by rfl) ⟨24747818, by rfl⟩ : syracuseStep 32997091 = 49495637) B49495637
theorem B43996121 : Blo 2287435 43996121 := bstep (se 2 (by rfl) ⟨16498545, by rfl⟩ : syracuseStep 43996121 = 32997091) B32997091
theorem B29330747 : Blo 2287435 29330747 := bstep (se 1 (by rfl) ⟨21998060, by rfl⟩ : syracuseStep 29330747 = 43996121) B43996121
theorem B19553831 : Blo 2287435 19553831 := bstep (se 1 (by rfl) ⟨14665373, by rfl⟩ : syracuseStep 19553831 = 29330747) B29330747
theorem B13035887 : Blo 2287435 13035887 := bstep (se 1 (by rfl) ⟨9776915, by rfl⟩ : syracuseStep 13035887 = 19553831) B19553831
theorem B8690591 : Blo 2287435 8690591 := bstep (se 1 (by rfl) ⟨6517943, by rfl⟩ : syracuseStep 8690591 = 13035887) B13035887
theorem B5793727 : Blo 2287435 5793727 := bstep (se 1 (by rfl) ⟨4345295, by rfl⟩ : syracuseStep 5793727 = 8690591) B8690591
theorem B7724969 : Blo 2287435 7724969 := bstep (se 2 (by rfl) ⟨2896863, by rfl⟩ : syracuseStep 7724969 = 5793727) B5793727
theorem B5149979 : Blo 2287435 5149979 := bstep (se 1 (by rfl) ⟨3862484, by rfl⟩ : syracuseStep 5149979 = 7724969) B7724969
theorem B3433319 : Blo 2287435 3433319 := bstep (se 1 (by rfl) ⟨2574989, by rfl⟩ : syracuseStep 3433319 = 5149979) B5149979
theorem B2288879 : Blo 2287435 2288879 := bstep (se 1 (by rfl) ⟨1716659, by rfl⟩ : syracuseStep 2288879 = 3433319) B3433319
theorem B3433325 : Blo 2287435 3433325 := bbase (se 3 (by rfl) ⟨643748, by rfl⟩ : syracuseStep 3433325 = 1287497) (by norm_num)
theorem B2288883 : Blo 2287435 2288883 := bstep (se 1 (by rfl) ⟨1716662, by rfl⟩ : syracuseStep 2288883 = 3433325) B3433325
theorem B5149997 : Blo 2287435 5149997 := bbase (se 3 (by rfl) ⟨965624, by rfl⟩ : syracuseStep 5149997 = 1931249) (by norm_num)
theorem B3433331 : Blo 2287435 3433331 := bstep (se 1 (by rfl) ⟨2574998, by rfl⟩ : syracuseStep 3433331 = 5149997) B5149997
theorem B2288887 : Blo 2287435 2288887 := bstep (se 1 (by rfl) ⟨1716665, by rfl⟩ : syracuseStep 2288887 = 3433331) B3433331
theorem B2320121 : Blo 2287435 2320121 := bbase (se 2 (by rfl) ⟨870045, by rfl⟩ : syracuseStep 2320121 = 1740091) (by norm_num)
theorem B6186989 : Blo 2287435 6186989 := bstep (se 3 (by rfl) ⟨1160060, by rfl⟩ : syracuseStep 6186989 = 2320121) B2320121
theorem B16498637 : Blo 2287435 16498637 := bstep (se 3 (by rfl) ⟨3093494, by rfl⟩ : syracuseStep 16498637 = 6186989) B6186989
theorem B10999091 : Blo 2287435 10999091 := bstep (se 1 (by rfl) ⟨8249318, by rfl⟩ : syracuseStep 10999091 = 16498637) B16498637
theorem B7332727 : Blo 2287435 7332727 := bstep (se 1 (by rfl) ⟨5499545, by rfl⟩ : syracuseStep 7332727 = 10999091) B10999091
theorem B9776969 : Blo 2287435 9776969 := bstep (se 2 (by rfl) ⟨3666363, by rfl⟩ : syracuseStep 9776969 = 7332727) B7332727
theorem B6517979 : Blo 2287435 6517979 := bstep (se 1 (by rfl) ⟨4888484, by rfl⟩ : syracuseStep 6517979 = 9776969) B9776969
theorem B4345319 : Blo 2287435 4345319 := bstep (se 1 (by rfl) ⟨3258989, by rfl⟩ : syracuseStep 4345319 = 6517979) B6517979
theorem B2896879 : Blo 2287435 2896879 := bstep (se 1 (by rfl) ⟨2172659, by rfl⟩ : syracuseStep 2896879 = 4345319) B4345319
theorem B3862505 : Blo 2287435 3862505 := bstep (se 2 (by rfl) ⟨1448439, by rfl⟩ : syracuseStep 3862505 = 2896879) B2896879
theorem B2575003 : Blo 2287435 2575003 := bstep (se 1 (by rfl) ⟨1931252, by rfl⟩ : syracuseStep 2575003 = 3862505) B3862505
theorem B3433337 : Blo 2287435 3433337 := bstep (se 2 (by rfl) ⟨1287501, by rfl⟩ : syracuseStep 3433337 = 2575003) B2575003
theorem B2288891 : Blo 2287435 2288891 := bstep (se 1 (by rfl) ⟨1716668, by rfl⟩ : syracuseStep 2288891 = 3433337) B3433337
theorem B4404613 : Blo 2287435 4404613 := bbase (se 4 (by rfl) ⟨412932, by rfl⟩ : syracuseStep 4404613 = 825865) (by norm_num)
theorem B5872817 : Blo 2287435 5872817 := bstep (se 2 (by rfl) ⟨2202306, by rfl⟩ : syracuseStep 5872817 = 4404613) B4404613
theorem B3915211 : Blo 2287435 3915211 := bstep (se 1 (by rfl) ⟨2936408, by rfl⟩ : syracuseStep 3915211 = 5872817) B5872817
theorem B5220281 : Blo 2287435 5220281 := bstep (se 2 (by rfl) ⟨1957605, by rfl⟩ : syracuseStep 5220281 = 3915211) B3915211
theorem B3480187 : Blo 2287435 3480187 := bstep (se 1 (by rfl) ⟨2610140, by rfl⟩ : syracuseStep 3480187 = 5220281) B5220281
theorem B4640249 : Blo 2287435 4640249 := bstep (se 2 (by rfl) ⟨1740093, by rfl⟩ : syracuseStep 4640249 = 3480187) B3480187
theorem B3093499 : Blo 2287435 3093499 := bstep (se 1 (by rfl) ⟨2320124, by rfl⟩ : syracuseStep 3093499 = 4640249) B4640249
theorem B4124665 : Blo 2287435 4124665 := bstep (se 2 (by rfl) ⟨1546749, by rfl⟩ : syracuseStep 4124665 = 3093499) B3093499
theorem B21998213 : Blo 2287435 21998213 := bstep (se 4 (by rfl) ⟨2062332, by rfl⟩ : syracuseStep 21998213 = 4124665) B4124665
theorem B14665475 : Blo 2287435 14665475 := bstep (se 1 (by rfl) ⟨10999106, by rfl⟩ : syracuseStep 14665475 = 21998213) B21998213
theorem B39107933 : Blo 2287435 39107933 := bstep (se 3 (by rfl) ⟨7332737, by rfl⟩ : syracuseStep 39107933 = 14665475) B14665475
theorem B26071955 : Blo 2287435 26071955 := bstep (se 1 (by rfl) ⟨19553966, by rfl⟩ : syracuseStep 26071955 = 39107933) B39107933
theorem B17381303 : Blo 2287435 17381303 := bstep (se 1 (by rfl) ⟨13035977, by rfl⟩ : syracuseStep 17381303 = 26071955) B26071955
theorem B11587535 : Blo 2287435 11587535 := bstep (se 1 (by rfl) ⟨8690651, by rfl⟩ : syracuseStep 11587535 = 17381303) B17381303
theorem B7725023 : Blo 2287435 7725023 := bstep (se 1 (by rfl) ⟨5793767, by rfl⟩ : syracuseStep 7725023 = 11587535) B11587535
theorem B5150015 : Blo 2287435 5150015 := bstep (se 1 (by rfl) ⟨3862511, by rfl⟩ : syracuseStep 5150015 = 7725023) B7725023
theorem B3433343 : Blo 2287435 3433343 := bstep (se 1 (by rfl) ⟨2575007, by rfl⟩ : syracuseStep 3433343 = 5150015) B5150015
theorem B2288895 : Blo 2287435 2288895 := bstep (se 1 (by rfl) ⟨1716671, by rfl⟩ : syracuseStep 2288895 = 3433343) B3433343
theorem B3433349 : Blo 2287435 3433349 := bbase (se 4 (by rfl) ⟨321876, by rfl⟩ : syracuseStep 3433349 = 643753) (by norm_num)
theorem B2288899 : Blo 2287435 2288899 := bstep (se 1 (by rfl) ⟨1716674, by rfl⟩ : syracuseStep 2288899 = 3433349) B3433349
theorem B3862525 : Blo 2287435 3862525 := bbase (se 3 (by rfl) ⟨724223, by rfl⟩ : syracuseStep 3862525 = 1448447) (by norm_num)
theorem B5150033 : Blo 2287435 5150033 := bstep (se 2 (by rfl) ⟨1931262, by rfl⟩ : syracuseStep 5150033 = 3862525) B3862525
theorem B3433355 : Blo 2287435 3433355 := bstep (se 1 (by rfl) ⟨2575016, by rfl⟩ : syracuseStep 3433355 = 5150033) B5150033
theorem B2288903 : Blo 2287435 2288903 := bstep (se 1 (by rfl) ⟨1716677, by rfl⟩ : syracuseStep 2288903 = 3433355) B3433355
theorem B2575021 : Blo 2287435 2575021 := bbase (se 3 (by rfl) ⟨482816, by rfl⟩ : syracuseStep 2575021 = 965633) (by norm_num)
theorem B3433361 : Blo 2287435 3433361 := bstep (se 2 (by rfl) ⟨1287510, by rfl⟩ : syracuseStep 3433361 = 2575021) B2575021
theorem B2288907 : Blo 2287435 2288907 := bstep (se 1 (by rfl) ⟨1716680, by rfl⟩ : syracuseStep 2288907 = 3433361) B3433361
theorem B7725077 : Blo 2287435 7725077 := bbase (se 6 (by rfl) ⟨181056, by rfl⟩ : syracuseStep 7725077 = 362113) (by norm_num)
theorem B5150051 : Blo 2287435 5150051 := bstep (se 1 (by rfl) ⟨3862538, by rfl⟩ : syracuseStep 5150051 = 7725077) B7725077
theorem B3433367 : Blo 2287435 3433367 := bstep (se 1 (by rfl) ⟨2575025, by rfl⟩ : syracuseStep 3433367 = 5150051) B5150051
theorem B2288911 : Blo 2287435 2288911 := bstep (se 1 (by rfl) ⟨1716683, by rfl⟩ : syracuseStep 2288911 = 3433367) B3433367
theorem B3433373 : Blo 2287435 3433373 := bbase (se 3 (by rfl) ⟨643757, by rfl⟩ : syracuseStep 3433373 = 1287515) (by norm_num)
theorem B2288915 : Blo 2287435 2288915 := bstep (se 1 (by rfl) ⟨1716686, by rfl⟩ : syracuseStep 2288915 = 3433373) B3433373
theorem B5150069 : Blo 2287435 5150069 := bbase (se 5 (by rfl) ⟨241409, by rfl⟩ : syracuseStep 5150069 = 482819) (by norm_num)
theorem B3433379 : Blo 2287435 3433379 := bstep (se 1 (by rfl) ⟨2575034, by rfl⟩ : syracuseStep 3433379 = 5150069) B5150069
theorem B2288919 : Blo 2287435 2288919 := bstep (se 1 (by rfl) ⟨1716689, by rfl⟩ : syracuseStep 2288919 = 3433379) B3433379
theorem B2320153 : Blo 2287435 2320153 := bbase (se 2 (by rfl) ⟨870057, by rfl⟩ : syracuseStep 2320153 = 1740115) (by norm_num)
theorem B12374149 : Blo 2287435 12374149 := bstep (se 4 (by rfl) ⟨1160076, by rfl⟩ : syracuseStep 12374149 = 2320153) B2320153
theorem B16498865 : Blo 2287435 16498865 := bstep (se 2 (by rfl) ⟨6187074, by rfl⟩ : syracuseStep 16498865 = 12374149) B12374149
theorem B10999243 : Blo 2287435 10999243 := bstep (se 1 (by rfl) ⟨8249432, by rfl⟩ : syracuseStep 10999243 = 16498865) B16498865
theorem B14665657 : Blo 2287435 14665657 := bstep (se 2 (by rfl) ⟨5499621, by rfl⟩ : syracuseStep 14665657 = 10999243) B10999243
theorem B19554209 : Blo 2287435 19554209 := bstep (se 2 (by rfl) ⟨7332828, by rfl⟩ : syracuseStep 19554209 = 14665657) B14665657
theorem B13036139 : Blo 2287435 13036139 := bstep (se 1 (by rfl) ⟨9777104, by rfl⟩ : syracuseStep 13036139 = 19554209) B19554209
theorem B8690759 : Blo 2287435 8690759 := bstep (se 1 (by rfl) ⟨6518069, by rfl⟩ : syracuseStep 8690759 = 13036139) B13036139
theorem B5793839 : Blo 2287435 5793839 := bstep (se 1 (by rfl) ⟨4345379, by rfl⟩ : syracuseStep 5793839 = 8690759) B8690759
theorem B3862559 : Blo 2287435 3862559 := bstep (se 1 (by rfl) ⟨2896919, by rfl⟩ : syracuseStep 3862559 = 5793839) B5793839
theorem B2575039 : Blo 2287435 2575039 := bstep (se 1 (by rfl) ⟨1931279, by rfl⟩ : syracuseStep 2575039 = 3862559) B3862559
theorem B3433385 : Blo 2287435 3433385 := bstep (se 2 (by rfl) ⟨1287519, by rfl⟩ : syracuseStep 3433385 = 2575039) B2575039
theorem B2288923 : Blo 2287435 2288923 := bstep (se 1 (by rfl) ⟨1716692, by rfl⟩ : syracuseStep 2288923 = 3433385) B3433385
theorem B8690773 : Blo 2287435 8690773 := bbase (se 8 (by rfl) ⟨50922, by rfl⟩ : syracuseStep 8690773 = 101845) (by norm_num)
theorem B11587697 : Blo 2287435 11587697 := bstep (se 2 (by rfl) ⟨4345386, by rfl⟩ : syracuseStep 11587697 = 8690773) B8690773
theorem B7725131 : Blo 2287435 7725131 := bstep (se 1 (by rfl) ⟨5793848, by rfl⟩ : syracuseStep 7725131 = 11587697) B11587697
theorem B5150087 : Blo 2287435 5150087 := bstep (se 1 (by rfl) ⟨3862565, by rfl⟩ : syracuseStep 5150087 = 7725131) B7725131
theorem B3433391 : Blo 2287435 3433391 := bstep (se 1 (by rfl) ⟨2575043, by rfl⟩ : syracuseStep 3433391 = 5150087) B5150087
theorem B2288927 : Blo 2287435 2288927 := bstep (se 1 (by rfl) ⟨1716695, by rfl⟩ : syracuseStep 2288927 = 3433391) B3433391
theorem B3433397 : Blo 2287435 3433397 := bbase (se 5 (by rfl) ⟨160940, by rfl⟩ : syracuseStep 3433397 = 321881) (by norm_num)
theorem B2288931 : Blo 2287435 2288931 := bstep (se 1 (by rfl) ⟨1716698, by rfl⟩ : syracuseStep 2288931 = 3433397) B3433397
theorem B5793869 : Blo 2287435 5793869 := bbase (se 3 (by rfl) ⟨1086350, by rfl⟩ : syracuseStep 5793869 = 2172701) (by norm_num)
theorem B3862579 : Blo 2287435 3862579 := bstep (se 1 (by rfl) ⟨2896934, by rfl⟩ : syracuseStep 3862579 = 5793869) B5793869
theorem B5150105 : Blo 2287435 5150105 := bstep (se 2 (by rfl) ⟨1931289, by rfl⟩ : syracuseStep 5150105 = 3862579) B3862579
theorem B3433403 : Blo 2287435 3433403 := bstep (se 1 (by rfl) ⟨2575052, by rfl⟩ : syracuseStep 3433403 = 5150105) B5150105
theorem B2288935 : Blo 2287435 2288935 := bstep (se 1 (by rfl) ⟨1716701, by rfl⟩ : syracuseStep 2288935 = 3433403) B3433403
theorem B2575057 : Blo 2287435 2575057 := bbase (se 2 (by rfl) ⟨965646, by rfl⟩ : syracuseStep 2575057 = 1931293) (by norm_num)
theorem B3433409 : Blo 2287435 3433409 := bstep (se 2 (by rfl) ⟨1287528, by rfl⟩ : syracuseStep 3433409 = 2575057) B2575057
theorem B2288939 : Blo 2287435 2288939 := bstep (se 1 (by rfl) ⟨1716704, by rfl⟩ : syracuseStep 2288939 = 3433409) B3433409
theorem B3093565 : Blo 2287435 3093565 := bbase (se 3 (by rfl) ⟨580043, by rfl⟩ : syracuseStep 3093565 = 1160087) (by norm_num)
theorem B4124753 : Blo 2287435 4124753 := bstep (se 2 (by rfl) ⟨1546782, by rfl⟩ : syracuseStep 4124753 = 3093565) B3093565
theorem B2749835 : Blo 2287435 2749835 := bstep (se 1 (by rfl) ⟨2062376, by rfl⟩ : syracuseStep 2749835 = 4124753) B4124753
theorem B7332893 : Blo 2287435 7332893 := bstep (se 3 (by rfl) ⟨1374917, by rfl⟩ : syracuseStep 7332893 = 2749835) B2749835
theorem B4888595 : Blo 2287435 4888595 := bstep (se 1 (by rfl) ⟨3666446, by rfl⟩ : syracuseStep 4888595 = 7332893) B7332893
theorem B3259063 : Blo 2287435 3259063 := bstep (se 1 (by rfl) ⟨2444297, by rfl⟩ : syracuseStep 3259063 = 4888595) B4888595
theorem B4345417 : Blo 2287435 4345417 := bstep (se 2 (by rfl) ⟨1629531, by rfl⟩ : syracuseStep 4345417 = 3259063) B3259063
theorem B5793889 : Blo 2287435 5793889 := bstep (se 2 (by rfl) ⟨2172708, by rfl⟩ : syracuseStep 5793889 = 4345417) B4345417
theorem B7725185 : Blo 2287435 7725185 := bstep (se 2 (by rfl) ⟨2896944, by rfl⟩ : syracuseStep 7725185 = 5793889) B5793889
theorem B5150123 : Blo 2287435 5150123 := bstep (se 1 (by rfl) ⟨3862592, by rfl⟩ : syracuseStep 5150123 = 7725185) B7725185
theorem B3433415 : Blo 2287435 3433415 := bstep (se 1 (by rfl) ⟨2575061, by rfl⟩ : syracuseStep 3433415 = 5150123) B5150123
theorem B2288943 : Blo 2287435 2288943 := bstep (se 1 (by rfl) ⟨1716707, by rfl⟩ : syracuseStep 2288943 = 3433415) B3433415
theorem B3433421 : Blo 2287435 3433421 := bbase (se 3 (by rfl) ⟨643766, by rfl⟩ : syracuseStep 3433421 = 1287533) (by norm_num)
theorem B2288947 : Blo 2287435 2288947 := bstep (se 1 (by rfl) ⟨1716710, by rfl⟩ : syracuseStep 2288947 = 3433421) B3433421
theorem B5150141 : Blo 2287435 5150141 := bbase (se 3 (by rfl) ⟨965651, by rfl⟩ : syracuseStep 5150141 = 1931303) (by norm_num)
theorem B3433427 : Blo 2287435 3433427 := bstep (se 1 (by rfl) ⟨2575070, by rfl⟩ : syracuseStep 3433427 = 5150141) B5150141
theorem B2288951 : Blo 2287435 2288951 := bstep (se 1 (by rfl) ⟨1716713, by rfl⟩ : syracuseStep 2288951 = 3433427) B3433427
theorem B3862613 : Blo 2287435 3862613 := bbase (se 8 (by rfl) ⟨22632, by rfl⟩ : syracuseStep 3862613 = 45265) (by norm_num)
theorem B2575075 : Blo 2287435 2575075 := bstep (se 1 (by rfl) ⟨1931306, by rfl⟩ : syracuseStep 2575075 = 3862613) B3862613
theorem B3433433 : Blo 2287435 3433433 := bstep (se 2 (by rfl) ⟨1287537, by rfl⟩ : syracuseStep 3433433 = 2575075) B2575075
theorem B2288955 : Blo 2287435 2288955 := bstep (se 1 (by rfl) ⟨1716716, by rfl⟩ : syracuseStep 2288955 = 3433433) B3433433
theorem B9280757 : Blo 2287435 9280757 := bbase (se 5 (by rfl) ⟨435035, by rfl⟩ : syracuseStep 9280757 = 870071) (by norm_num)
theorem B24748685 : Blo 2287435 24748685 := bstep (se 3 (by rfl) ⟨4640378, by rfl⟩ : syracuseStep 24748685 = 9280757) B9280757
theorem B16499123 : Blo 2287435 16499123 := bstep (se 1 (by rfl) ⟨12374342, by rfl⟩ : syracuseStep 16499123 = 24748685) B24748685
theorem B10999415 : Blo 2287435 10999415 := bstep (se 1 (by rfl) ⟨8249561, by rfl⟩ : syracuseStep 10999415 = 16499123) B16499123
theorem B7332943 : Blo 2287435 7332943 := bstep (se 1 (by rfl) ⟨5499707, by rfl⟩ : syracuseStep 7332943 = 10999415) B10999415
theorem B9777257 : Blo 2287435 9777257 := bstep (se 2 (by rfl) ⟨3666471, by rfl⟩ : syracuseStep 9777257 = 7332943) B7332943
theorem B6518171 : Blo 2287435 6518171 := bstep (se 1 (by rfl) ⟨4888628, by rfl⟩ : syracuseStep 6518171 = 9777257) B9777257
theorem B17381789 : Blo 2287435 17381789 := bstep (se 3 (by rfl) ⟨3259085, by rfl⟩ : syracuseStep 17381789 = 6518171) B6518171
theorem B11587859 : Blo 2287435 11587859 := bstep (se 1 (by rfl) ⟨8690894, by rfl⟩ : syracuseStep 11587859 = 17381789) B17381789
theorem B7725239 : Blo 2287435 7725239 := bstep (se 1 (by rfl) ⟨5793929, by rfl⟩ : syracuseStep 7725239 = 11587859) B11587859
theorem B5150159 : Blo 2287435 5150159 := bstep (se 1 (by rfl) ⟨3862619, by rfl⟩ : syracuseStep 5150159 = 7725239) B7725239
theorem B3433439 : Blo 2287435 3433439 := bstep (se 1 (by rfl) ⟨2575079, by rfl⟩ : syracuseStep 3433439 = 5150159) B5150159
theorem B2288959 : Blo 2287435 2288959 := bstep (se 1 (by rfl) ⟨1716719, by rfl⟩ : syracuseStep 2288959 = 3433439) B3433439
theorem B3433445 : Blo 2287435 3433445 := bbase (se 4 (by rfl) ⟨321885, by rfl⟩ : syracuseStep 3433445 = 643771) (by norm_num)
theorem B2288963 : Blo 2287435 2288963 := bstep (se 1 (by rfl) ⟨1716722, by rfl⟩ : syracuseStep 2288963 = 3433445) B3433445
theorem B3666485 : Blo 2287435 3666485 := bbase (se 5 (by rfl) ⟨171866, by rfl⟩ : syracuseStep 3666485 = 343733) (by norm_num)
theorem B9777293 : Blo 2287435 9777293 := bstep (se 3 (by rfl) ⟨1833242, by rfl⟩ : syracuseStep 9777293 = 3666485) B3666485
theorem B6518195 : Blo 2287435 6518195 := bstep (se 1 (by rfl) ⟨4888646, by rfl⟩ : syracuseStep 6518195 = 9777293) B9777293
theorem B4345463 : Blo 2287435 4345463 := bstep (se 1 (by rfl) ⟨3259097, by rfl⟩ : syracuseStep 4345463 = 6518195) B6518195
theorem B2896975 : Blo 2287435 2896975 := bstep (se 1 (by rfl) ⟨2172731, by rfl⟩ : syracuseStep 2896975 = 4345463) B4345463
theorem B3862633 : Blo 2287435 3862633 := bstep (se 2 (by rfl) ⟨1448487, by rfl⟩ : syracuseStep 3862633 = 2896975) B2896975
theorem B5150177 : Blo 2287435 5150177 := bstep (se 2 (by rfl) ⟨1931316, by rfl⟩ : syracuseStep 5150177 = 3862633) B3862633
theorem B3433451 : Blo 2287435 3433451 := bstep (se 1 (by rfl) ⟨2575088, by rfl⟩ : syracuseStep 3433451 = 5150177) B5150177
theorem B2288967 : Blo 2287435 2288967 := bstep (se 1 (by rfl) ⟨1716725, by rfl⟩ : syracuseStep 2288967 = 3433451) B3433451
theorem B2575093 : Blo 2287435 2575093 := bbase (se 5 (by rfl) ⟨120707, by rfl⟩ : syracuseStep 2575093 = 241415) (by norm_num)
theorem B3433457 : Blo 2287435 3433457 := bstep (se 2 (by rfl) ⟨1287546, by rfl⟩ : syracuseStep 3433457 = 2575093) B2575093
theorem B2288971 : Blo 2287435 2288971 := bstep (se 1 (by rfl) ⟨1716728, by rfl⟩ : syracuseStep 2288971 = 3433457) B3433457
theorem B2896985 : Blo 2287435 2896985 := bbase (se 2 (by rfl) ⟨1086369, by rfl⟩ : syracuseStep 2896985 = 2172739) (by norm_num)
theorem B7725293 : Blo 2287435 7725293 := bstep (se 3 (by rfl) ⟨1448492, by rfl⟩ : syracuseStep 7725293 = 2896985) B2896985
theorem B5150195 : Blo 2287435 5150195 := bstep (se 1 (by rfl) ⟨3862646, by rfl⟩ : syracuseStep 5150195 = 7725293) B7725293
theorem B3433463 : Blo 2287435 3433463 := bstep (se 1 (by rfl) ⟨2575097, by rfl⟩ : syracuseStep 3433463 = 5150195) B5150195
theorem B2288975 : Blo 2287435 2288975 := bstep (se 1 (by rfl) ⟨1716731, by rfl⟩ : syracuseStep 2288975 = 3433463) B3433463
theorem B3433469 : Blo 2287435 3433469 := bbase (se 3 (by rfl) ⟨643775, by rfl⟩ : syracuseStep 3433469 = 1287551) (by norm_num)
theorem B2288979 : Blo 2287435 2288979 := bstep (se 1 (by rfl) ⟨1716734, by rfl⟩ : syracuseStep 2288979 = 3433469) B3433469
theorem B5150213 : Blo 2287435 5150213 := bbase (se 4 (by rfl) ⟨482832, by rfl⟩ : syracuseStep 5150213 = 965665) (by norm_num)
theorem B3433475 : Blo 2287435 3433475 := bstep (se 1 (by rfl) ⟨2575106, by rfl⟩ : syracuseStep 3433475 = 5150213) B5150213
theorem B2288983 : Blo 2287435 2288983 := bstep (se 1 (by rfl) ⟨1716737, by rfl⟩ : syracuseStep 2288983 = 3433475) B3433475
theorem B4345501 : Blo 2287435 4345501 := bbase (se 3 (by rfl) ⟨814781, by rfl⟩ : syracuseStep 4345501 = 1629563) (by norm_num)
theorem B5794001 : Blo 2287435 5794001 := bstep (se 2 (by rfl) ⟨2172750, by rfl⟩ : syracuseStep 5794001 = 4345501) B4345501
theorem B3862667 : Blo 2287435 3862667 := bstep (se 1 (by rfl) ⟨2897000, by rfl⟩ : syracuseStep 3862667 = 5794001) B5794001
theorem B2575111 : Blo 2287435 2575111 := bstep (se 1 (by rfl) ⟨1931333, by rfl⟩ : syracuseStep 2575111 = 3862667) B3862667
theorem B3433481 : Blo 2287435 3433481 := bstep (se 2 (by rfl) ⟨1287555, by rfl⟩ : syracuseStep 3433481 = 2575111) B2575111
theorem B2288987 : Blo 2287435 2288987 := bstep (se 1 (by rfl) ⟨1716740, by rfl⟩ : syracuseStep 2288987 = 3433481) B3433481
theorem B11588021 : Blo 2287435 11588021 := bbase (se 5 (by rfl) ⟨543188, by rfl⟩ : syracuseStep 11588021 = 1086377) (by norm_num)
theorem B7725347 : Blo 2287435 7725347 := bstep (se 1 (by rfl) ⟨5794010, by rfl⟩ : syracuseStep 7725347 = 11588021) B11588021
theorem B5150231 : Blo 2287435 5150231 := bstep (se 1 (by rfl) ⟨3862673, by rfl⟩ : syracuseStep 5150231 = 7725347) B7725347
theorem B3433487 : Blo 2287435 3433487 := bstep (se 1 (by rfl) ⟨2575115, by rfl⟩ : syracuseStep 3433487 = 5150231) B5150231
theorem B2288991 : Blo 2287435 2288991 := bstep (se 1 (by rfl) ⟨1716743, by rfl⟩ : syracuseStep 2288991 = 3433487) B3433487
theorem B3433493 : Blo 2287435 3433493 := bbase (se 6 (by rfl) ⟨80472, by rfl⟩ : syracuseStep 3433493 = 160945) (by norm_num)
theorem B2288995 : Blo 2287435 2288995 := bstep (se 1 (by rfl) ⟨1716746, by rfl⟩ : syracuseStep 2288995 = 3433493) B3433493
theorem B20092085 : Blo 2287435 20092085 := bbase (se 5 (by rfl) ⟨941816, by rfl⟩ : syracuseStep 20092085 = 1883633) (by norm_num)
theorem B13394723 : Blo 2287435 13394723 := bstep (se 1 (by rfl) ⟨10046042, by rfl⟩ : syracuseStep 13394723 = 20092085) B20092085
theorem B35719261 : Blo 2287435 35719261 := bstep (se 3 (by rfl) ⟨6697361, by rfl⟩ : syracuseStep 35719261 = 13394723) B13394723
theorem B190502725 : Blo 2287435 190502725 := bstep (se 4 (by rfl) ⟨17859630, by rfl⟩ : syracuseStep 190502725 = 35719261) B35719261
theorem B254003633 : Blo 2287435 254003633 := bstep (se 2 (by rfl) ⟨95251362, by rfl⟩ : syracuseStep 254003633 = 190502725) B190502725
theorem B169335755 : Blo 2287435 169335755 := bstep (se 1 (by rfl) ⟨127001816, by rfl⟩ : syracuseStep 169335755 = 254003633) B254003633
theorem B112890503 : Blo 2287435 112890503 := bstep (se 1 (by rfl) ⟨84667877, by rfl⟩ : syracuseStep 112890503 = 169335755) B169335755
theorem B75260335 : Blo 2287435 75260335 := bstep (se 1 (by rfl) ⟨56445251, by rfl⟩ : syracuseStep 75260335 = 112890503) B112890503
theorem B100347113 : Blo 2287435 100347113 := bstep (se 2 (by rfl) ⟨37630167, by rfl⟩ : syracuseStep 100347113 = 75260335) B75260335
theorem B66898075 : Blo 2287435 66898075 := bstep (se 1 (by rfl) ⟨50173556, by rfl⟩ : syracuseStep 66898075 = 100347113) B100347113
theorem B89197433 : Blo 2287435 89197433 := bstep (se 2 (by rfl) ⟨33449037, by rfl⟩ : syracuseStep 89197433 = 66898075) B66898075
theorem B59464955 : Blo 2287435 59464955 := bstep (se 1 (by rfl) ⟨44598716, by rfl⟩ : syracuseStep 59464955 = 89197433) B89197433
theorem B39643303 : Blo 2287435 39643303 := bstep (se 1 (by rfl) ⟨29732477, by rfl⟩ : syracuseStep 39643303 = 59464955) B59464955
theorem B52857737 : Blo 2287435 52857737 := bstep (se 2 (by rfl) ⟨19821651, by rfl⟩ : syracuseStep 52857737 = 39643303) B39643303
theorem B35238491 : Blo 2287435 35238491 := bstep (se 1 (by rfl) ⟨26428868, by rfl⟩ : syracuseStep 35238491 = 52857737) B52857737
theorem B23492327 : Blo 2287435 23492327 := bstep (se 1 (by rfl) ⟨17619245, by rfl⟩ : syracuseStep 23492327 = 35238491) B35238491
theorem B62646205 : Blo 2287435 62646205 := bstep (se 3 (by rfl) ⟨11746163, by rfl⟩ : syracuseStep 62646205 = 23492327) B23492327
theorem B83528273 : Blo 2287435 83528273 := bstep (se 2 (by rfl) ⟨31323102, by rfl⟩ : syracuseStep 83528273 = 62646205) B62646205
theorem B55685515 : Blo 2287435 55685515 := bstep (se 1 (by rfl) ⟨41764136, by rfl⟩ : syracuseStep 55685515 = 83528273) B83528273
theorem B74247353 : Blo 2287435 74247353 := bstep (se 2 (by rfl) ⟨27842757, by rfl⟩ : syracuseStep 74247353 = 55685515) B55685515
theorem B49498235 : Blo 2287435 49498235 := bstep (se 1 (by rfl) ⟨37123676, by rfl⟩ : syracuseStep 49498235 = 74247353) B74247353
theorem B32998823 : Blo 2287435 32998823 := bstep (se 1 (by rfl) ⟨24749117, by rfl⟩ : syracuseStep 32998823 = 49498235) B49498235
theorem B21999215 : Blo 2287435 21999215 := bstep (se 1 (by rfl) ⟨16499411, by rfl⟩ : syracuseStep 21999215 = 32998823) B32998823
theorem B14666143 : Blo 2287435 14666143 := bstep (se 1 (by rfl) ⟨10999607, by rfl⟩ : syracuseStep 14666143 = 21999215) B21999215
theorem B19554857 : Blo 2287435 19554857 := bstep (se 2 (by rfl) ⟨7333071, by rfl⟩ : syracuseStep 19554857 = 14666143) B14666143
theorem B13036571 : Blo 2287435 13036571 := bstep (se 1 (by rfl) ⟨9777428, by rfl⟩ : syracuseStep 13036571 = 19554857) B19554857
theorem B8691047 : Blo 2287435 8691047 := bstep (se 1 (by rfl) ⟨6518285, by rfl⟩ : syracuseStep 8691047 = 13036571) B13036571
theorem B5794031 : Blo 2287435 5794031 := bstep (se 1 (by rfl) ⟨4345523, by rfl⟩ : syracuseStep 5794031 = 8691047) B8691047
theorem B3862687 : Blo 2287435 3862687 := bstep (se 1 (by rfl) ⟨2897015, by rfl⟩ : syracuseStep 3862687 = 5794031) B5794031
theorem B5150249 : Blo 2287435 5150249 := bstep (se 2 (by rfl) ⟨1931343, by rfl⟩ : syracuseStep 5150249 = 3862687) B3862687
theorem B3433499 : Blo 2287435 3433499 := bstep (se 1 (by rfl) ⟨2575124, by rfl⟩ : syracuseStep 3433499 = 5150249) B5150249
theorem B2288999 : Blo 2287435 2288999 := bstep (se 1 (by rfl) ⟨1716749, by rfl⟩ : syracuseStep 2288999 = 3433499) B3433499
theorem B2575129 : Blo 2287435 2575129 := bbase (se 2 (by rfl) ⟨965673, by rfl⟩ : syracuseStep 2575129 = 1931347) (by norm_num)
theorem B3433505 : Blo 2287435 3433505 := bstep (se 2 (by rfl) ⟨1287564, by rfl⟩ : syracuseStep 3433505 = 2575129) B2575129
theorem B2289003 : Blo 2287435 2289003 := bstep (se 1 (by rfl) ⟨1716752, by rfl⟩ : syracuseStep 2289003 = 3433505) B3433505
theorem B8691077 : Blo 2287435 8691077 := bbase (se 4 (by rfl) ⟨814788, by rfl⟩ : syracuseStep 8691077 = 1629577) (by norm_num)
theorem B5794051 : Blo 2287435 5794051 := bstep (se 1 (by rfl) ⟨4345538, by rfl⟩ : syracuseStep 5794051 = 8691077) B8691077
theorem B7725401 : Blo 2287435 7725401 := bstep (se 2 (by rfl) ⟨2897025, by rfl⟩ : syracuseStep 7725401 = 5794051) B5794051
theorem B5150267 : Blo 2287435 5150267 := bstep (se 1 (by rfl) ⟨3862700, by rfl⟩ : syracuseStep 5150267 = 7725401) B7725401
theorem B3433511 : Blo 2287435 3433511 := bstep (se 1 (by rfl) ⟨2575133, by rfl⟩ : syracuseStep 3433511 = 5150267) B5150267
theorem B2289007 : Blo 2287435 2289007 := bstep (se 1 (by rfl) ⟨1716755, by rfl⟩ : syracuseStep 2289007 = 3433511) B3433511
theorem B3433517 : Blo 2287435 3433517 := bbase (se 3 (by rfl) ⟨643784, by rfl⟩ : syracuseStep 3433517 = 1287569) (by norm_num)
theorem B2289011 : Blo 2287435 2289011 := bstep (se 1 (by rfl) ⟨1716758, by rfl⟩ : syracuseStep 2289011 = 3433517) B3433517
theorem B5150285 : Blo 2287435 5150285 := bbase (se 3 (by rfl) ⟨965678, by rfl⟩ : syracuseStep 5150285 = 1931357) (by norm_num)
theorem B3433523 : Blo 2287435 3433523 := bstep (se 1 (by rfl) ⟨2575142, by rfl⟩ : syracuseStep 3433523 = 5150285) B5150285
theorem B2289015 : Blo 2287435 2289015 := bstep (se 1 (by rfl) ⟨1716761, by rfl⟩ : syracuseStep 2289015 = 3433523) B3433523
theorem B2897041 : Blo 2287435 2897041 := bbase (se 2 (by rfl) ⟨1086390, by rfl⟩ : syracuseStep 2897041 = 2172781) (by norm_num)
theorem B3862721 : Blo 2287435 3862721 := bstep (se 2 (by rfl) ⟨1448520, by rfl⟩ : syracuseStep 3862721 = 2897041) B2897041
theorem B2575147 : Blo 2287435 2575147 := bstep (se 1 (by rfl) ⟨1931360, by rfl⟩ : syracuseStep 2575147 = 3862721) B3862721
theorem B3433529 : Blo 2287435 3433529 := bstep (se 2 (by rfl) ⟨1287573, by rfl⟩ : syracuseStep 3433529 = 2575147) B2575147
theorem B2289019 : Blo 2287435 2289019 := bstep (se 1 (by rfl) ⟨1716764, by rfl⟩ : syracuseStep 2289019 = 3433529) B3433529
theorem B4888765 : Blo 2287435 4888765 := bbase (se 3 (by rfl) ⟨916643, by rfl⟩ : syracuseStep 4888765 = 1833287) (by norm_num)
theorem B26073413 : Blo 2287435 26073413 := bstep (se 4 (by rfl) ⟨2444382, by rfl⟩ : syracuseStep 26073413 = 4888765) B4888765
theorem B17382275 : Blo 2287435 17382275 := bstep (se 1 (by rfl) ⟨13036706, by rfl⟩ : syracuseStep 17382275 = 26073413) B26073413
theorem B11588183 : Blo 2287435 11588183 := bstep (se 1 (by rfl) ⟨8691137, by rfl⟩ : syracuseStep 11588183 = 17382275) B17382275
theorem B7725455 : Blo 2287435 7725455 := bstep (se 1 (by rfl) ⟨5794091, by rfl⟩ : syracuseStep 7725455 = 11588183) B11588183
theorem B5150303 : Blo 2287435 5150303 := bstep (se 1 (by rfl) ⟨3862727, by rfl⟩ : syracuseStep 5150303 = 7725455) B7725455
theorem B3433535 : Blo 2287435 3433535 := bstep (se 1 (by rfl) ⟨2575151, by rfl⟩ : syracuseStep 3433535 = 5150303) B5150303
theorem B2289023 : Blo 2287435 2289023 := bstep (se 1 (by rfl) ⟨1716767, by rfl⟩ : syracuseStep 2289023 = 3433535) B3433535
theorem B3433541 : Blo 2287435 3433541 := bbase (se 4 (by rfl) ⟨321894, by rfl⟩ : syracuseStep 3433541 = 643789) (by norm_num)
theorem B2289027 : Blo 2287435 2289027 := bstep (se 1 (by rfl) ⟨1716770, by rfl⟩ : syracuseStep 2289027 = 3433541) B3433541
theorem B3862741 : Blo 2287435 3862741 := bbase (se 7 (by rfl) ⟨45266, by rfl⟩ : syracuseStep 3862741 = 90533) (by norm_num)
theorem B5150321 : Blo 2287435 5150321 := bstep (se 2 (by rfl) ⟨1931370, by rfl⟩ : syracuseStep 5150321 = 3862741) B3862741
theorem B3433547 : Blo 2287435 3433547 := bstep (se 1 (by rfl) ⟨2575160, by rfl⟩ : syracuseStep 3433547 = 5150321) B5150321
theorem B2289031 : Blo 2287435 2289031 := bstep (se 1 (by rfl) ⟨1716773, by rfl⟩ : syracuseStep 2289031 = 3433547) B3433547
theorem B2575165 : Blo 2287435 2575165 := bbase (se 3 (by rfl) ⟨482843, by rfl⟩ : syracuseStep 2575165 = 965687) (by norm_num)
theorem B3433553 : Blo 2287435 3433553 := bstep (se 2 (by rfl) ⟨1287582, by rfl⟩ : syracuseStep 3433553 = 2575165) B2575165
theorem B2289035 : Blo 2287435 2289035 := bstep (se 1 (by rfl) ⟨1716776, by rfl⟩ : syracuseStep 2289035 = 3433553) B3433553
theorem B7725509 : Blo 2287435 7725509 := bbase (se 4 (by rfl) ⟨724266, by rfl⟩ : syracuseStep 7725509 = 1448533) (by norm_num)
theorem B5150339 : Blo 2287435 5150339 := bstep (se 1 (by rfl) ⟨3862754, by rfl⟩ : syracuseStep 5150339 = 7725509) B7725509
theorem B3433559 : Blo 2287435 3433559 := bstep (se 1 (by rfl) ⟨2575169, by rfl⟩ : syracuseStep 3433559 = 5150339) B5150339
theorem B2289039 : Blo 2287435 2289039 := bstep (se 1 (by rfl) ⟨1716779, by rfl⟩ : syracuseStep 2289039 = 3433559) B3433559
theorem B3433565 : Blo 2287435 3433565 := bbase (se 3 (by rfl) ⟨643793, by rfl⟩ : syracuseStep 3433565 = 1287587) (by norm_num)
theorem B2289043 : Blo 2287435 2289043 := bstep (se 1 (by rfl) ⟨1716782, by rfl⟩ : syracuseStep 2289043 = 3433565) B3433565
theorem B5150357 : Blo 2287435 5150357 := bbase (se 6 (by rfl) ⟨120711, by rfl⟩ : syracuseStep 5150357 = 241423) (by norm_num)
theorem B3433571 : Blo 2287435 3433571 := bstep (se 1 (by rfl) ⟨2575178, by rfl⟩ : syracuseStep 3433571 = 5150357) B5150357
theorem B2289047 : Blo 2287435 2289047 := bstep (se 1 (by rfl) ⟨1716785, by rfl⟩ : syracuseStep 2289047 = 3433571) B3433571
theorem B2444413 : Blo 2287435 2444413 := bbase (se 3 (by rfl) ⟨458327, by rfl⟩ : syracuseStep 2444413 = 916655) (by norm_num)
theorem B3259217 : Blo 2287435 3259217 := bstep (se 2 (by rfl) ⟨1222206, by rfl⟩ : syracuseStep 3259217 = 2444413) B2444413
theorem B8691245 : Blo 2287435 8691245 := bstep (se 3 (by rfl) ⟨1629608, by rfl⟩ : syracuseStep 8691245 = 3259217) B3259217
theorem B5794163 : Blo 2287435 5794163 := bstep (se 1 (by rfl) ⟨4345622, by rfl⟩ : syracuseStep 5794163 = 8691245) B8691245
theorem B3862775 : Blo 2287435 3862775 := bstep (se 1 (by rfl) ⟨2897081, by rfl⟩ : syracuseStep 3862775 = 5794163) B5794163
theorem B2575183 : Blo 2287435 2575183 := bstep (se 1 (by rfl) ⟨1931387, by rfl⟩ : syracuseStep 2575183 = 3862775) B3862775
theorem B3433577 : Blo 2287435 3433577 := bstep (se 2 (by rfl) ⟨1287591, by rfl⟩ : syracuseStep 3433577 = 2575183) B2575183
theorem B2289051 : Blo 2287435 2289051 := bstep (se 1 (by rfl) ⟨1716788, by rfl⟩ : syracuseStep 2289051 = 3433577) B3433577
theorem B2749969 : Blo 2287435 2749969 := bbase (se 2 (by rfl) ⟨1031238, by rfl⟩ : syracuseStep 2749969 = 2062477) (by norm_num)
theorem B14666501 : Blo 2287435 14666501 := bstep (se 4 (by rfl) ⟨1374984, by rfl⟩ : syracuseStep 14666501 = 2749969) B2749969
theorem B9777667 : Blo 2287435 9777667 := bstep (se 1 (by rfl) ⟨7333250, by rfl⟩ : syracuseStep 9777667 = 14666501) B14666501
theorem B13036889 : Blo 2287435 13036889 := bstep (se 2 (by rfl) ⟨4888833, by rfl⟩ : syracuseStep 13036889 = 9777667) B9777667
theorem B8691259 : Blo 2287435 8691259 := bstep (se 1 (by rfl) ⟨6518444, by rfl⟩ : syracuseStep 8691259 = 13036889) B13036889
theorem B11588345 : Blo 2287435 11588345 := bstep (se 2 (by rfl) ⟨4345629, by rfl⟩ : syracuseStep 11588345 = 8691259) B8691259
theorem B7725563 : Blo 2287435 7725563 := bstep (se 1 (by rfl) ⟨5794172, by rfl⟩ : syracuseStep 7725563 = 11588345) B11588345
theorem B5150375 : Blo 2287435 5150375 := bstep (se 1 (by rfl) ⟨3862781, by rfl⟩ : syracuseStep 5150375 = 7725563) B7725563
theorem B3433583 : Blo 2287435 3433583 := bstep (se 1 (by rfl) ⟨2575187, by rfl⟩ : syracuseStep 3433583 = 5150375) B5150375
theorem B2289055 : Blo 2287435 2289055 := bstep (se 1 (by rfl) ⟨1716791, by rfl⟩ : syracuseStep 2289055 = 3433583) B3433583
theorem B3433589 : Blo 2287435 3433589 := bbase (se 5 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 3433589 = 321899) (by norm_num)
theorem B2289059 : Blo 2287435 2289059 := bstep (se 1 (by rfl) ⟨1716794, by rfl⟩ : syracuseStep 2289059 = 3433589) B3433589
theorem B4345645 : Blo 2287435 4345645 := bbase (se 3 (by rfl) ⟨814808, by rfl⟩ : syracuseStep 4345645 = 1629617) (by norm_num)
theorem B5794193 : Blo 2287435 5794193 := bstep (se 2 (by rfl) ⟨2172822, by rfl⟩ : syracuseStep 5794193 = 4345645) B4345645
theorem B3862795 : Blo 2287435 3862795 := bstep (se 1 (by rfl) ⟨2897096, by rfl⟩ : syracuseStep 3862795 = 5794193) B5794193
theorem B5150393 : Blo 2287435 5150393 := bstep (se 2 (by rfl) ⟨1931397, by rfl⟩ : syracuseStep 5150393 = 3862795) B3862795
theorem B3433595 : Blo 2287435 3433595 := bstep (se 1 (by rfl) ⟨2575196, by rfl⟩ : syracuseStep 3433595 = 5150393) B5150393
theorem B2289063 : Blo 2287435 2289063 := bstep (se 1 (by rfl) ⟨1716797, by rfl⟩ : syracuseStep 2289063 = 3433595) B3433595
theorem B2575201 : Blo 2287435 2575201 := bbase (se 2 (by rfl) ⟨965700, by rfl⟩ : syracuseStep 2575201 = 1931401) (by norm_num)
theorem B3433601 : Blo 2287435 3433601 := bstep (se 2 (by rfl) ⟨1287600, by rfl⟩ : syracuseStep 3433601 = 2575201) B2575201
theorem B2289067 : Blo 2287435 2289067 := bstep (se 1 (by rfl) ⟨1716800, by rfl⟩ : syracuseStep 2289067 = 3433601) B3433601
theorem B5794213 : Blo 2287435 5794213 := bbase (se 4 (by rfl) ⟨543207, by rfl⟩ : syracuseStep 5794213 = 1086415) (by norm_num)
theorem B7725617 : Blo 2287435 7725617 := bstep (se 2 (by rfl) ⟨2897106, by rfl⟩ : syracuseStep 7725617 = 5794213) B5794213
theorem B5150411 : Blo 2287435 5150411 := bstep (se 1 (by rfl) ⟨3862808, by rfl⟩ : syracuseStep 5150411 = 7725617) B7725617
theorem B3433607 : Blo 2287435 3433607 := bstep (se 1 (by rfl) ⟨2575205, by rfl⟩ : syracuseStep 3433607 = 5150411) B5150411
theorem B2289071 : Blo 2287435 2289071 := bstep (se 1 (by rfl) ⟨1716803, by rfl⟩ : syracuseStep 2289071 = 3433607) B3433607
theorem B3433613 : Blo 2287435 3433613 := bbase (se 3 (by rfl) ⟨643802, by rfl⟩ : syracuseStep 3433613 = 1287605) (by norm_num)
theorem B2289075 : Blo 2287435 2289075 := bstep (se 1 (by rfl) ⟨1716806, by rfl⟩ : syracuseStep 2289075 = 3433613) B3433613
theorem B5150429 : Blo 2287435 5150429 := bbase (se 3 (by rfl) ⟨965705, by rfl⟩ : syracuseStep 5150429 = 1931411) (by norm_num)
theorem B3433619 : Blo 2287435 3433619 := bstep (se 1 (by rfl) ⟨2575214, by rfl⟩ : syracuseStep 3433619 = 5150429) B5150429
theorem B2289079 : Blo 2287435 2289079 := bstep (se 1 (by rfl) ⟨1716809, by rfl⟩ : syracuseStep 2289079 = 3433619) B3433619
theorem B3862829 : Blo 2287435 3862829 := bbase (se 3 (by rfl) ⟨724280, by rfl⟩ : syracuseStep 3862829 = 1448561) (by norm_num)
theorem B2575219 : Blo 2287435 2575219 := bstep (se 1 (by rfl) ⟨1931414, by rfl⟩ : syracuseStep 2575219 = 3862829) B3862829
theorem B3433625 : Blo 2287435 3433625 := bstep (se 2 (by rfl) ⟨1287609, by rfl⟩ : syracuseStep 3433625 = 2575219) B2575219
theorem B2289083 : Blo 2287435 2289083 := bstep (se 1 (by rfl) ⟨1716812, by rfl⟩ : syracuseStep 2289083 = 3433625) B3433625
theorem B19822421 : Blo 2287435 19822421 := bbase (se 9 (by rfl) ⟨58073, by rfl⟩ : syracuseStep 19822421 = 116147) (by norm_num)
theorem B13214947 : Blo 2287435 13214947 := bstep (se 1 (by rfl) ⟨9911210, by rfl⟩ : syracuseStep 13214947 = 19822421) B19822421
theorem B17619929 : Blo 2287435 17619929 := bstep (se 2 (by rfl) ⟨6607473, by rfl⟩ : syracuseStep 17619929 = 13214947) B13214947
theorem B11746619 : Blo 2287435 11746619 := bstep (se 1 (by rfl) ⟨8809964, by rfl⟩ : syracuseStep 11746619 = 17619929) B17619929
theorem B7831079 : Blo 2287435 7831079 := bstep (se 1 (by rfl) ⟨5873309, by rfl⟩ : syracuseStep 7831079 = 11746619) B11746619
theorem B5220719 : Blo 2287435 5220719 := bstep (se 1 (by rfl) ⟨3915539, by rfl⟩ : syracuseStep 5220719 = 7831079) B7831079
theorem B3480479 : Blo 2287435 3480479 := bstep (se 1 (by rfl) ⟨2610359, by rfl⟩ : syracuseStep 3480479 = 5220719) B5220719
theorem B2320319 : Blo 2287435 2320319 := bstep (se 1 (by rfl) ⟨1740239, by rfl⟩ : syracuseStep 2320319 = 3480479) B3480479
theorem B6187517 : Blo 2287435 6187517 := bstep (se 3 (by rfl) ⟨1160159, by rfl⟩ : syracuseStep 6187517 = 2320319) B2320319
theorem B4125011 : Blo 2287435 4125011 := bstep (se 1 (by rfl) ⟨3093758, by rfl⟩ : syracuseStep 4125011 = 6187517) B6187517
theorem B44000117 : Blo 2287435 44000117 := bstep (se 5 (by rfl) ⟨2062505, by rfl⟩ : syracuseStep 44000117 = 4125011) B4125011
theorem B29333411 : Blo 2287435 29333411 := bstep (se 1 (by rfl) ⟨22000058, by rfl⟩ : syracuseStep 29333411 = 44000117) B44000117
theorem B19555607 : Blo 2287435 19555607 := bstep (se 1 (by rfl) ⟨14666705, by rfl⟩ : syracuseStep 19555607 = 29333411) B29333411
theorem B13037071 : Blo 2287435 13037071 := bstep (se 1 (by rfl) ⟨9777803, by rfl⟩ : syracuseStep 13037071 = 19555607) B19555607
theorem B17382761 : Blo 2287435 17382761 := bstep (se 2 (by rfl) ⟨6518535, by rfl⟩ : syracuseStep 17382761 = 13037071) B13037071
theorem B11588507 : Blo 2287435 11588507 := bstep (se 1 (by rfl) ⟨8691380, by rfl⟩ : syracuseStep 11588507 = 17382761) B17382761
theorem B7725671 : Blo 2287435 7725671 := bstep (se 1 (by rfl) ⟨5794253, by rfl⟩ : syracuseStep 7725671 = 11588507) B11588507
theorem B5150447 : Blo 2287435 5150447 := bstep (se 1 (by rfl) ⟨3862835, by rfl⟩ : syracuseStep 5150447 = 7725671) B7725671
theorem B3433631 : Blo 2287435 3433631 := bstep (se 1 (by rfl) ⟨2575223, by rfl⟩ : syracuseStep 3433631 = 5150447) B5150447
theorem B2289087 : Blo 2287435 2289087 := bstep (se 1 (by rfl) ⟨1716815, by rfl⟩ : syracuseStep 2289087 = 3433631) B3433631
theorem B3433637 : Blo 2287435 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B2289091 : Blo 2287435 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B2897137 : Blo 2287435 2897137 := bbase (se 2 (by rfl) ⟨1086426, by rfl⟩ : syracuseStep 2897137 = 2172853) (by norm_num)
theorem B3862849 : Blo 2287435 3862849 := bstep (se 2 (by rfl) ⟨1448568, by rfl⟩ : syracuseStep 3862849 = 2897137) B2897137
theorem B5150465 : Blo 2287435 5150465 := bstep (se 2 (by rfl) ⟨1931424, by rfl⟩ : syracuseStep 5150465 = 3862849) B3862849
theorem B3433643 : Blo 2287435 3433643 := bstep (se 1 (by rfl) ⟨2575232, by rfl⟩ : syracuseStep 3433643 = 5150465) B5150465
theorem B2289095 : Blo 2287435 2289095 := bstep (se 1 (by rfl) ⟨1716821, by rfl⟩ : syracuseStep 2289095 = 3433643) B3433643
theorem B2575237 : Blo 2287435 2575237 := bbase (se 4 (by rfl) ⟨241428, by rfl⟩ : syracuseStep 2575237 = 482857) (by norm_num)
theorem B3433649 : Blo 2287435 3433649 := bstep (se 2 (by rfl) ⟨1287618, by rfl⟩ : syracuseStep 3433649 = 2575237) B2575237
theorem B2289099 : Blo 2287435 2289099 := bstep (se 1 (by rfl) ⟨1716824, by rfl⟩ : syracuseStep 2289099 = 3433649) B3433649
theorem B12375125 : Blo 2287435 12375125 := bbase (se 8 (by rfl) ⟨72510, by rfl⟩ : syracuseStep 12375125 = 145021) (by norm_num)
theorem B8250083 : Blo 2287435 8250083 := bstep (se 1 (by rfl) ⟨6187562, by rfl⟩ : syracuseStep 8250083 = 12375125) B12375125
theorem B5500055 : Blo 2287435 5500055 := bstep (se 1 (by rfl) ⟨4125041, by rfl⟩ : syracuseStep 5500055 = 8250083) B8250083
theorem B3666703 : Blo 2287435 3666703 := bstep (se 1 (by rfl) ⟨2750027, by rfl⟩ : syracuseStep 3666703 = 5500055) B5500055
theorem B4888937 : Blo 2287435 4888937 := bstep (se 2 (by rfl) ⟨1833351, by rfl⟩ : syracuseStep 4888937 = 3666703) B3666703
theorem B3259291 : Blo 2287435 3259291 := bstep (se 1 (by rfl) ⟨2444468, by rfl⟩ : syracuseStep 3259291 = 4888937) B4888937
theorem B4345721 : Blo 2287435 4345721 := bstep (se 2 (by rfl) ⟨1629645, by rfl⟩ : syracuseStep 4345721 = 3259291) B3259291
theorem B2897147 : Blo 2287435 2897147 := bstep (se 1 (by rfl) ⟨2172860, by rfl⟩ : syracuseStep 2897147 = 4345721) B4345721
theorem B7725725 : Blo 2287435 7725725 := bstep (se 3 (by rfl) ⟨1448573, by rfl⟩ : syracuseStep 7725725 = 2897147) B2897147
theorem B5150483 : Blo 2287435 5150483 := bstep (se 1 (by rfl) ⟨3862862, by rfl⟩ : syracuseStep 5150483 = 7725725) B7725725
theorem B3433655 : Blo 2287435 3433655 := bstep (se 1 (by rfl) ⟨2575241, by rfl⟩ : syracuseStep 3433655 = 5150483) B5150483
theorem B2289103 : Blo 2287435 2289103 := bstep (se 1 (by rfl) ⟨1716827, by rfl⟩ : syracuseStep 2289103 = 3433655) B3433655
theorem B3433661 : Blo 2287435 3433661 := bbase (se 3 (by rfl) ⟨643811, by rfl⟩ : syracuseStep 3433661 = 1287623) (by norm_num)
theorem B2289107 : Blo 2287435 2289107 := bstep (se 1 (by rfl) ⟨1716830, by rfl⟩ : syracuseStep 2289107 = 3433661) B3433661
theorem B5150501 : Blo 2287435 5150501 := bbase (se 4 (by rfl) ⟨482859, by rfl⟩ : syracuseStep 5150501 = 965719) (by norm_num)
theorem B3433667 : Blo 2287435 3433667 := bstep (se 1 (by rfl) ⟨2575250, by rfl⟩ : syracuseStep 3433667 = 5150501) B5150501
theorem B2289111 : Blo 2287435 2289111 := bstep (se 1 (by rfl) ⟨1716833, by rfl⟩ : syracuseStep 2289111 = 3433667) B3433667
theorem B5794325 : Blo 2287435 5794325 := bbase (se 6 (by rfl) ⟨135804, by rfl⟩ : syracuseStep 5794325 = 271609) (by norm_num)
theorem B3862883 : Blo 2287435 3862883 := bstep (se 1 (by rfl) ⟨2897162, by rfl⟩ : syracuseStep 3862883 = 5794325) B5794325
theorem B2575255 : Blo 2287435 2575255 := bstep (se 1 (by rfl) ⟨1931441, by rfl⟩ : syracuseStep 2575255 = 3862883) B3862883
theorem B3433673 : Blo 2287435 3433673 := bstep (se 2 (by rfl) ⟨1287627, by rfl⟩ : syracuseStep 3433673 = 2575255) B2575255
theorem B2289115 : Blo 2287435 2289115 := bstep (se 1 (by rfl) ⟨1716836, by rfl⟩ : syracuseStep 2289115 = 3433673) B3433673
theorem B9777941 : Blo 2287435 9777941 := bbase (se 6 (by rfl) ⟨229170, by rfl⟩ : syracuseStep 9777941 = 458341) (by norm_num)
theorem B6518627 : Blo 2287435 6518627 := bstep (se 1 (by rfl) ⟨4888970, by rfl⟩ : syracuseStep 6518627 = 9777941) B9777941
theorem B4345751 : Blo 2287435 4345751 := bstep (se 1 (by rfl) ⟨3259313, by rfl⟩ : syracuseStep 4345751 = 6518627) B6518627
theorem B11588669 : Blo 2287435 11588669 := bstep (se 3 (by rfl) ⟨2172875, by rfl⟩ : syracuseStep 11588669 = 4345751) B4345751
theorem B7725779 : Blo 2287435 7725779 := bstep (se 1 (by rfl) ⟨5794334, by rfl⟩ : syracuseStep 7725779 = 11588669) B11588669
theorem B5150519 : Blo 2287435 5150519 := bstep (se 1 (by rfl) ⟨3862889, by rfl⟩ : syracuseStep 5150519 = 7725779) B7725779
theorem B3433679 : Blo 2287435 3433679 := bstep (se 1 (by rfl) ⟨2575259, by rfl⟩ : syracuseStep 3433679 = 5150519) B5150519
theorem B2289119 : Blo 2287435 2289119 := bstep (se 1 (by rfl) ⟨1716839, by rfl⟩ : syracuseStep 2289119 = 3433679) B3433679
theorem B3433685 : Blo 2287435 3433685 := bbase (se 7 (by rfl) ⟨40238, by rfl⟩ : syracuseStep 3433685 = 80477) (by norm_num)
theorem B2289123 : Blo 2287435 2289123 := bstep (se 1 (by rfl) ⟨1716842, by rfl⟩ : syracuseStep 2289123 = 3433685) B3433685
theorem B3259325 : Blo 2287435 3259325 := bbase (se 3 (by rfl) ⟨611123, by rfl⟩ : syracuseStep 3259325 = 1222247) (by norm_num)
theorem B8691533 : Blo 2287435 8691533 := bstep (se 3 (by rfl) ⟨1629662, by rfl⟩ : syracuseStep 8691533 = 3259325) B3259325
theorem B5794355 : Blo 2287435 5794355 := bstep (se 1 (by rfl) ⟨4345766, by rfl⟩ : syracuseStep 5794355 = 8691533) B8691533
theorem B3862903 : Blo 2287435 3862903 := bstep (se 1 (by rfl) ⟨2897177, by rfl⟩ : syracuseStep 3862903 = 5794355) B5794355
theorem B5150537 : Blo 2287435 5150537 := bstep (se 2 (by rfl) ⟨1931451, by rfl⟩ : syracuseStep 5150537 = 3862903) B3862903
theorem B3433691 : Blo 2287435 3433691 := bstep (se 1 (by rfl) ⟨2575268, by rfl⟩ : syracuseStep 3433691 = 5150537) B5150537
theorem B2289127 : Blo 2287435 2289127 := bstep (se 1 (by rfl) ⟨1716845, by rfl⟩ : syracuseStep 2289127 = 3433691) B3433691
theorem B2575273 : Blo 2287435 2575273 := bbase (se 2 (by rfl) ⟨965727, by rfl⟩ : syracuseStep 2575273 = 1931455) (by norm_num)
theorem B3433697 : Blo 2287435 3433697 := bstep (se 2 (by rfl) ⟨1287636, by rfl⟩ : syracuseStep 3433697 = 2575273) B2575273
theorem B2289131 : Blo 2287435 2289131 := bstep (se 1 (by rfl) ⟨1716848, by rfl⟩ : syracuseStep 2289131 = 3433697) B3433697
theorem B11000261 : Blo 2287435 11000261 := bbase (se 4 (by rfl) ⟨1031274, by rfl⟩ : syracuseStep 11000261 = 2062549) (by norm_num)
theorem B7333507 : Blo 2287435 7333507 := bstep (se 1 (by rfl) ⟨5500130, by rfl⟩ : syracuseStep 7333507 = 11000261) B11000261
theorem B9778009 : Blo 2287435 9778009 := bstep (se 2 (by rfl) ⟨3666753, by rfl⟩ : syracuseStep 9778009 = 7333507) B7333507
theorem B13037345 : Blo 2287435 13037345 := bstep (se 2 (by rfl) ⟨4889004, by rfl⟩ : syracuseStep 13037345 = 9778009) B9778009
theorem B8691563 : Blo 2287435 8691563 := bstep (se 1 (by rfl) ⟨6518672, by rfl⟩ : syracuseStep 8691563 = 13037345) B13037345
theorem B5794375 : Blo 2287435 5794375 := bstep (se 1 (by rfl) ⟨4345781, by rfl⟩ : syracuseStep 5794375 = 8691563) B8691563
theorem B7725833 : Blo 2287435 7725833 := bstep (se 2 (by rfl) ⟨2897187, by rfl⟩ : syracuseStep 7725833 = 5794375) B5794375
theorem B5150555 : Blo 2287435 5150555 := bstep (se 1 (by rfl) ⟨3862916, by rfl⟩ : syracuseStep 5150555 = 7725833) B7725833
theorem B3433703 : Blo 2287435 3433703 := bstep (se 1 (by rfl) ⟨2575277, by rfl⟩ : syracuseStep 3433703 = 5150555) B5150555
theorem B2289135 : Blo 2287435 2289135 := bstep (se 1 (by rfl) ⟨1716851, by rfl⟩ : syracuseStep 2289135 = 3433703) B3433703
theorem B3433709 : Blo 2287435 3433709 := bbase (se 3 (by rfl) ⟨643820, by rfl⟩ : syracuseStep 3433709 = 1287641) (by norm_num)
theorem B2289139 : Blo 2287435 2289139 := bstep (se 1 (by rfl) ⟨1716854, by rfl⟩ : syracuseStep 2289139 = 3433709) B3433709
theorem B5150573 : Blo 2287435 5150573 := bbase (se 3 (by rfl) ⟨965732, by rfl⟩ : syracuseStep 5150573 = 1931465) (by norm_num)
theorem B3433715 : Blo 2287435 3433715 := bstep (se 1 (by rfl) ⟨2575286, by rfl⟩ : syracuseStep 3433715 = 5150573) B5150573
theorem B2289143 : Blo 2287435 2289143 := bstep (se 1 (by rfl) ⟨1716857, by rfl⟩ : syracuseStep 2289143 = 3433715) B3433715
theorem B4345805 : Blo 2287435 4345805 := bbase (se 3 (by rfl) ⟨814838, by rfl⟩ : syracuseStep 4345805 = 1629677) (by norm_num)
theorem B2897203 : Blo 2287435 2897203 := bstep (se 1 (by rfl) ⟨2172902, by rfl⟩ : syracuseStep 2897203 = 4345805) B4345805
theorem B3862937 : Blo 2287435 3862937 := bstep (se 2 (by rfl) ⟨1448601, by rfl⟩ : syracuseStep 3862937 = 2897203) B2897203
theorem B2575291 : Blo 2287435 2575291 := bstep (se 1 (by rfl) ⟨1931468, by rfl⟩ : syracuseStep 2575291 = 3862937) B3862937
theorem B3433721 : Blo 2287435 3433721 := bstep (se 2 (by rfl) ⟨1287645, by rfl⟩ : syracuseStep 3433721 = 2575291) B2575291
theorem B2289147 : Blo 2287435 2289147 := bstep (se 1 (by rfl) ⟨1716860, by rfl⟩ : syracuseStep 2289147 = 3433721) B3433721
theorem B10183781 : Blo 2287435 10183781 := bbase (se 4 (by rfl) ⟨954729, by rfl⟩ : syracuseStep 10183781 = 1909459) (by norm_num)
theorem B6789187 : Blo 2287435 6789187 := bstep (se 1 (by rfl) ⟨5091890, by rfl⟩ : syracuseStep 6789187 = 10183781) B10183781
theorem B9052249 : Blo 2287435 9052249 := bstep (se 2 (by rfl) ⟨3394593, by rfl⟩ : syracuseStep 9052249 = 6789187) B6789187
theorem B12069665 : Blo 2287435 12069665 := bstep (se 2 (by rfl) ⟨4526124, by rfl⟩ : syracuseStep 12069665 = 9052249) B9052249
theorem B8046443 : Blo 2287435 8046443 := bstep (se 1 (by rfl) ⟨6034832, by rfl⟩ : syracuseStep 8046443 = 12069665) B12069665
theorem B21457181 : Blo 2287435 21457181 := bstep (se 3 (by rfl) ⟨4023221, by rfl⟩ : syracuseStep 21457181 = 8046443) B8046443
theorem B57219149 : Blo 2287435 57219149 := bstep (se 3 (by rfl) ⟨10728590, by rfl⟩ : syracuseStep 57219149 = 21457181) B21457181
theorem B152584397 : Blo 2287435 152584397 := bstep (se 3 (by rfl) ⟨28609574, by rfl⟩ : syracuseStep 152584397 = 57219149) B57219149
theorem B101722931 : Blo 2287435 101722931 := bstep (se 1 (by rfl) ⟨76292198, by rfl⟩ : syracuseStep 101722931 = 152584397) B152584397
theorem B67815287 : Blo 2287435 67815287 := bstep (se 1 (by rfl) ⟨50861465, by rfl⟩ : syracuseStep 67815287 = 101722931) B101722931
theorem B45210191 : Blo 2287435 45210191 := bstep (se 1 (by rfl) ⟨33907643, by rfl⟩ : syracuseStep 45210191 = 67815287) B67815287
theorem B120560509 : Blo 2287435 120560509 := bstep (se 3 (by rfl) ⟨22605095, by rfl⟩ : syracuseStep 120560509 = 45210191) B45210191
theorem B160747345 : Blo 2287435 160747345 := bstep (se 2 (by rfl) ⟨60280254, by rfl⟩ : syracuseStep 160747345 = 120560509) B120560509
theorem B857319173 : Blo 2287435 857319173 := bstep (se 4 (by rfl) ⟨80373672, by rfl⟩ : syracuseStep 857319173 = 160747345) B160747345
theorem B571546115 : Blo 2287435 571546115 := bstep (se 1 (by rfl) ⟨428659586, by rfl⟩ : syracuseStep 571546115 = 857319173) B857319173
theorem B381030743 : Blo 2287435 381030743 := bstep (se 1 (by rfl) ⟨285773057, by rfl⟩ : syracuseStep 381030743 = 571546115) B571546115
theorem B254020495 : Blo 2287435 254020495 := bstep (se 1 (by rfl) ⟨190515371, by rfl⟩ : syracuseStep 254020495 = 381030743) B381030743
theorem B338693993 : Blo 2287435 338693993 := bstep (se 2 (by rfl) ⟨127010247, by rfl⟩ : syracuseStep 338693993 = 254020495) B254020495
theorem B225795995 : Blo 2287435 225795995 := bstep (se 1 (by rfl) ⟨169346996, by rfl⟩ : syracuseStep 225795995 = 338693993) B338693993
theorem B150530663 : Blo 2287435 150530663 := bstep (se 1 (by rfl) ⟨112897997, by rfl⟩ : syracuseStep 150530663 = 225795995) B225795995
theorem B401415101 : Blo 2287435 401415101 := bstep (se 3 (by rfl) ⟨75265331, by rfl⟩ : syracuseStep 401415101 = 150530663) B150530663
theorem B267610067 : Blo 2287435 267610067 := bstep (se 1 (by rfl) ⟨200707550, by rfl⟩ : syracuseStep 267610067 = 401415101) B401415101
theorem B178406711 : Blo 2287435 178406711 := bstep (se 1 (by rfl) ⟨133805033, by rfl⟩ : syracuseStep 178406711 = 267610067) B267610067
theorem B118937807 : Blo 2287435 118937807 := bstep (se 1 (by rfl) ⟨89203355, by rfl⟩ : syracuseStep 118937807 = 178406711) B178406711
theorem B79291871 : Blo 2287435 79291871 := bstep (se 1 (by rfl) ⟨59468903, by rfl⟩ : syracuseStep 79291871 = 118937807) B118937807
theorem B52861247 : Blo 2287435 52861247 := bstep (se 1 (by rfl) ⟨39645935, by rfl⟩ : syracuseStep 52861247 = 79291871) B79291871
theorem B35240831 : Blo 2287435 35240831 := bstep (se 1 (by rfl) ⟨26430623, by rfl⟩ : syracuseStep 35240831 = 52861247) B52861247
theorem B23493887 : Blo 2287435 23493887 := bstep (se 1 (by rfl) ⟨17620415, by rfl⟩ : syracuseStep 23493887 = 35240831) B35240831
theorem B15662591 : Blo 2287435 15662591 := bstep (se 1 (by rfl) ⟨11746943, by rfl⟩ : syracuseStep 15662591 = 23493887) B23493887
theorem B10441727 : Blo 2287435 10441727 := bstep (se 1 (by rfl) ⟨7831295, by rfl⟩ : syracuseStep 10441727 = 15662591) B15662591
theorem B6961151 : Blo 2287435 6961151 := bstep (se 1 (by rfl) ⟨5220863, by rfl⟩ : syracuseStep 6961151 = 10441727) B10441727
theorem B18563069 : Blo 2287435 18563069 := bstep (se 3 (by rfl) ⟨3480575, by rfl⟩ : syracuseStep 18563069 = 6961151) B6961151
theorem B12375379 : Blo 2287435 12375379 := bstep (se 1 (by rfl) ⟨9281534, by rfl⟩ : syracuseStep 12375379 = 18563069) B18563069
theorem B16500505 : Blo 2287435 16500505 := bstep (se 2 (by rfl) ⟨6187689, by rfl⟩ : syracuseStep 16500505 = 12375379) B12375379
theorem B22000673 : Blo 2287435 22000673 := bstep (se 2 (by rfl) ⟨8250252, by rfl⟩ : syracuseStep 22000673 = 16500505) B16500505
theorem B58668461 : Blo 2287435 58668461 := bstep (se 3 (by rfl) ⟨11000336, by rfl⟩ : syracuseStep 58668461 = 22000673) B22000673
theorem B39112307 : Blo 2287435 39112307 := bstep (se 1 (by rfl) ⟨29334230, by rfl⟩ : syracuseStep 39112307 = 58668461) B58668461
theorem B26074871 : Blo 2287435 26074871 := bstep (se 1 (by rfl) ⟨19556153, by rfl⟩ : syracuseStep 26074871 = 39112307) B39112307
theorem B17383247 : Blo 2287435 17383247 := bstep (se 1 (by rfl) ⟨13037435, by rfl⟩ : syracuseStep 17383247 = 26074871) B26074871
theorem B11588831 : Blo 2287435 11588831 := bstep (se 1 (by rfl) ⟨8691623, by rfl⟩ : syracuseStep 11588831 = 17383247) B17383247
theorem B7725887 : Blo 2287435 7725887 := bstep (se 1 (by rfl) ⟨5794415, by rfl⟩ : syracuseStep 7725887 = 11588831) B11588831
theorem B5150591 : Blo 2287435 5150591 := bstep (se 1 (by rfl) ⟨3862943, by rfl⟩ : syracuseStep 5150591 = 7725887) B7725887
theorem B3433727 : Blo 2287435 3433727 := bstep (se 1 (by rfl) ⟨2575295, by rfl⟩ : syracuseStep 3433727 = 5150591) B5150591
theorem B2289151 : Blo 2287435 2289151 := bstep (se 1 (by rfl) ⟨1716863, by rfl⟩ : syracuseStep 2289151 = 3433727) B3433727
theorem B3433733 : Blo 2287435 3433733 := bbase (se 4 (by rfl) ⟨321912, by rfl⟩ : syracuseStep 3433733 = 643825) (by norm_num)
theorem B2289155 : Blo 2287435 2289155 := bstep (se 1 (by rfl) ⟨1716866, by rfl⟩ : syracuseStep 2289155 = 3433733) B3433733
theorem B3862957 : Blo 2287435 3862957 := bbase (se 3 (by rfl) ⟨724304, by rfl⟩ : syracuseStep 3862957 = 1448609) (by norm_num)
theorem B5150609 : Blo 2287435 5150609 := bstep (se 2 (by rfl) ⟨1931478, by rfl⟩ : syracuseStep 5150609 = 3862957) B3862957
theorem B3433739 : Blo 2287435 3433739 := bstep (se 1 (by rfl) ⟨2575304, by rfl⟩ : syracuseStep 3433739 = 5150609) B5150609
theorem B2289159 : Blo 2287435 2289159 := bstep (se 1 (by rfl) ⟨1716869, by rfl⟩ : syracuseStep 2289159 = 3433739) B3433739
theorem B2575309 : Blo 2287435 2575309 := bbase (se 3 (by rfl) ⟨482870, by rfl⟩ : syracuseStep 2575309 = 965741) (by norm_num)
theorem B3433745 : Blo 2287435 3433745 := bstep (se 2 (by rfl) ⟨1287654, by rfl⟩ : syracuseStep 3433745 = 2575309) B2575309
theorem B2289163 : Blo 2287435 2289163 := bstep (se 1 (by rfl) ⟨1716872, by rfl⟩ : syracuseStep 2289163 = 3433745) B3433745
theorem B7725941 : Blo 2287435 7725941 := bbase (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) (by norm_num)
theorem B5150627 : Blo 2287435 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B3433751 : Blo 2287435 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B2289167 : Blo 2287435 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B3433757 : Blo 2287435 3433757 := bbase (se 3 (by rfl) ⟨643829, by rfl⟩ : syracuseStep 3433757 = 1287659) (by norm_num)
theorem B2289171 : Blo 2287435 2289171 := bstep (se 1 (by rfl) ⟨1716878, by rfl⟩ : syracuseStep 2289171 = 3433757) B3433757
theorem B5150645 : Blo 2287435 5150645 := bbase (se 5 (by rfl) ⟨241436, by rfl⟩ : syracuseStep 5150645 = 482873) (by norm_num)
theorem B3433763 : Blo 2287435 3433763 := bstep (se 1 (by rfl) ⟨2575322, by rfl⟩ : syracuseStep 3433763 = 5150645) B5150645
theorem B2289175 : Blo 2287435 2289175 := bstep (se 1 (by rfl) ⟨1716881, by rfl⟩ : syracuseStep 2289175 = 3433763) B3433763
theorem B5500237 : Blo 2287435 5500237 := bbase (se 3 (by rfl) ⟨1031294, by rfl⟩ : syracuseStep 5500237 = 2062589) (by norm_num)
theorem B7333649 : Blo 2287435 7333649 := bstep (se 2 (by rfl) ⟨2750118, by rfl⟩ : syracuseStep 7333649 = 5500237) B5500237
theorem B4889099 : Blo 2287435 4889099 := bstep (se 1 (by rfl) ⟨3666824, by rfl⟩ : syracuseStep 4889099 = 7333649) B7333649
theorem B13037597 : Blo 2287435 13037597 := bstep (se 3 (by rfl) ⟨2444549, by rfl⟩ : syracuseStep 13037597 = 4889099) B4889099
theorem B8691731 : Blo 2287435 8691731 := bstep (se 1 (by rfl) ⟨6518798, by rfl⟩ : syracuseStep 8691731 = 13037597) B13037597
theorem B5794487 : Blo 2287435 5794487 := bstep (se 1 (by rfl) ⟨4345865, by rfl⟩ : syracuseStep 5794487 = 8691731) B8691731
theorem B3862991 : Blo 2287435 3862991 := bstep (se 1 (by rfl) ⟨2897243, by rfl⟩ : syracuseStep 3862991 = 5794487) B5794487
theorem B2575327 : Blo 2287435 2575327 := bstep (se 1 (by rfl) ⟨1931495, by rfl⟩ : syracuseStep 2575327 = 3862991) B3862991
theorem B3433769 : Blo 2287435 3433769 := bstep (se 2 (by rfl) ⟨1287663, by rfl⟩ : syracuseStep 3433769 = 2575327) B2575327
theorem B2289179 : Blo 2287435 2289179 := bstep (se 1 (by rfl) ⟨1716884, by rfl⟩ : syracuseStep 2289179 = 3433769) B3433769
theorem B2320417 : Blo 2287435 2320417 := bbase (se 2 (by rfl) ⟨870156, by rfl⟩ : syracuseStep 2320417 = 1740313) (by norm_num)
theorem B3093889 : Blo 2287435 3093889 := bstep (se 2 (by rfl) ⟨1160208, by rfl⟩ : syracuseStep 3093889 = 2320417) B2320417
theorem B4125185 : Blo 2287435 4125185 := bstep (se 2 (by rfl) ⟨1546944, by rfl⟩ : syracuseStep 4125185 = 3093889) B3093889
theorem B2750123 : Blo 2287435 2750123 := bstep (se 1 (by rfl) ⟨2062592, by rfl⟩ : syracuseStep 2750123 = 4125185) B4125185
theorem B7333661 : Blo 2287435 7333661 := bstep (se 3 (by rfl) ⟨1375061, by rfl⟩ : syracuseStep 7333661 = 2750123) B2750123
theorem B4889107 : Blo 2287435 4889107 := bstep (se 1 (by rfl) ⟨3666830, by rfl⟩ : syracuseStep 4889107 = 7333661) B7333661
theorem B6518809 : Blo 2287435 6518809 := bstep (se 2 (by rfl) ⟨2444553, by rfl⟩ : syracuseStep 6518809 = 4889107) B4889107
theorem B8691745 : Blo 2287435 8691745 := bstep (se 2 (by rfl) ⟨3259404, by rfl⟩ : syracuseStep 8691745 = 6518809) B6518809
theorem B11588993 : Blo 2287435 11588993 := bstep (se 2 (by rfl) ⟨4345872, by rfl⟩ : syracuseStep 11588993 = 8691745) B8691745
theorem B7725995 : Blo 2287435 7725995 := bstep (se 1 (by rfl) ⟨5794496, by rfl⟩ : syracuseStep 7725995 = 11588993) B11588993
theorem B5150663 : Blo 2287435 5150663 := bstep (se 1 (by rfl) ⟨3862997, by rfl⟩ : syracuseStep 5150663 = 7725995) B7725995
theorem B3433775 : Blo 2287435 3433775 := bstep (se 1 (by rfl) ⟨2575331, by rfl⟩ : syracuseStep 3433775 = 5150663) B5150663
theorem B2289183 : Blo 2287435 2289183 := bstep (se 1 (by rfl) ⟨1716887, by rfl⟩ : syracuseStep 2289183 = 3433775) B3433775
theorem B3433781 : Blo 2287435 3433781 := bbase (se 5 (by rfl) ⟨160958, by rfl⟩ : syracuseStep 3433781 = 321917) (by norm_num)
theorem B2289187 : Blo 2287435 2289187 := bstep (se 1 (by rfl) ⟨1716890, by rfl⟩ : syracuseStep 2289187 = 3433781) B3433781
theorem B5794517 : Blo 2287435 5794517 := bbase (se 7 (by rfl) ⟨67904, by rfl⟩ : syracuseStep 5794517 = 135809) (by norm_num)
theorem B3863011 : Blo 2287435 3863011 := bstep (se 1 (by rfl) ⟨2897258, by rfl⟩ : syracuseStep 3863011 = 5794517) B5794517
theorem B5150681 : Blo 2287435 5150681 := bstep (se 2 (by rfl) ⟨1931505, by rfl⟩ : syracuseStep 5150681 = 3863011) B3863011
theorem B3433787 : Blo 2287435 3433787 := bstep (se 1 (by rfl) ⟨2575340, by rfl⟩ : syracuseStep 3433787 = 5150681) B5150681
theorem B2289191 : Blo 2287435 2289191 := bstep (se 1 (by rfl) ⟨1716893, by rfl⟩ : syracuseStep 2289191 = 3433787) B3433787
theorem B2575345 : Blo 2287435 2575345 := bbase (se 2 (by rfl) ⟨965754, by rfl⟩ : syracuseStep 2575345 = 1931509) (by norm_num)
theorem B3433793 : Blo 2287435 3433793 := bstep (se 2 (by rfl) ⟨1287672, by rfl⟩ : syracuseStep 3433793 = 2575345) B2575345
theorem B2289195 : Blo 2287435 2289195 := bstep (se 1 (by rfl) ⟨1716896, by rfl⟩ : syracuseStep 2289195 = 3433793) B3433793
theorem B5873597 : Blo 2287435 5873597 := bbase (se 3 (by rfl) ⟨1101299, by rfl⟩ : syracuseStep 5873597 = 2202599) (by norm_num)
theorem B3915731 : Blo 2287435 3915731 := bstep (se 1 (by rfl) ⟨2936798, by rfl⟩ : syracuseStep 3915731 = 5873597) B5873597
theorem B2610487 : Blo 2287435 2610487 := bstep (se 1 (by rfl) ⟨1957865, by rfl⟩ : syracuseStep 2610487 = 3915731) B3915731
theorem B13922597 : Blo 2287435 13922597 := bstep (se 4 (by rfl) ⟨1305243, by rfl⟩ : syracuseStep 13922597 = 2610487) B2610487
theorem B9281731 : Blo 2287435 9281731 := bstep (se 1 (by rfl) ⟨6961298, by rfl⟩ : syracuseStep 9281731 = 13922597) B13922597
theorem B12375641 : Blo 2287435 12375641 := bstep (se 2 (by rfl) ⟨4640865, by rfl⟩ : syracuseStep 12375641 = 9281731) B9281731
theorem B8250427 : Blo 2287435 8250427 := bstep (se 1 (by rfl) ⟨6187820, by rfl⟩ : syracuseStep 8250427 = 12375641) B12375641
theorem B11000569 : Blo 2287435 11000569 := bstep (se 2 (by rfl) ⟨4125213, by rfl⟩ : syracuseStep 11000569 = 8250427) B8250427
theorem B14667425 : Blo 2287435 14667425 := bstep (se 2 (by rfl) ⟨5500284, by rfl⟩ : syracuseStep 14667425 = 11000569) B11000569
theorem B9778283 : Blo 2287435 9778283 := bstep (se 1 (by rfl) ⟨7333712, by rfl⟩ : syracuseStep 9778283 = 14667425) B14667425
theorem B6518855 : Blo 2287435 6518855 := bstep (se 1 (by rfl) ⟨4889141, by rfl⟩ : syracuseStep 6518855 = 9778283) B9778283
theorem B4345903 : Blo 2287435 4345903 := bstep (se 1 (by rfl) ⟨3259427, by rfl⟩ : syracuseStep 4345903 = 6518855) B6518855
theorem B5794537 : Blo 2287435 5794537 := bstep (se 2 (by rfl) ⟨2172951, by rfl⟩ : syracuseStep 5794537 = 4345903) B4345903
theorem B7726049 : Blo 2287435 7726049 := bstep (se 2 (by rfl) ⟨2897268, by rfl⟩ : syracuseStep 7726049 = 5794537) B5794537
theorem B5150699 : Blo 2287435 5150699 := bstep (se 1 (by rfl) ⟨3863024, by rfl⟩ : syracuseStep 5150699 = 7726049) B7726049
theorem B3433799 : Blo 2287435 3433799 := bstep (se 1 (by rfl) ⟨2575349, by rfl⟩ : syracuseStep 3433799 = 5150699) B5150699
theorem B2289199 : Blo 2287435 2289199 := bstep (se 1 (by rfl) ⟨1716899, by rfl⟩ : syracuseStep 2289199 = 3433799) B3433799
theorem B3433805 : Blo 2287435 3433805 := bbase (se 3 (by rfl) ⟨643838, by rfl⟩ : syracuseStep 3433805 = 1287677) (by norm_num)
theorem B2289203 : Blo 2287435 2289203 := bstep (se 1 (by rfl) ⟨1716902, by rfl⟩ : syracuseStep 2289203 = 3433805) B3433805
theorem B5150717 : Blo 2287435 5150717 := bbase (se 3 (by rfl) ⟨965759, by rfl⟩ : syracuseStep 5150717 = 1931519) (by norm_num)
theorem B3433811 : Blo 2287435 3433811 := bstep (se 1 (by rfl) ⟨2575358, by rfl⟩ : syracuseStep 3433811 = 5150717) B5150717
theorem B2289207 : Blo 2287435 2289207 := bstep (se 1 (by rfl) ⟨1716905, by rfl⟩ : syracuseStep 2289207 = 3433811) B3433811
theorem B3863045 : Blo 2287435 3863045 := bbase (se 4 (by rfl) ⟨362160, by rfl⟩ : syracuseStep 3863045 = 724321) (by norm_num)
theorem B2575363 : Blo 2287435 2575363 := bstep (se 1 (by rfl) ⟨1931522, by rfl⟩ : syracuseStep 2575363 = 3863045) B3863045
theorem B3433817 : Blo 2287435 3433817 := bstep (se 2 (by rfl) ⟨1287681, by rfl⟩ : syracuseStep 3433817 = 2575363) B2575363
theorem B2289211 : Blo 2287435 2289211 := bstep (se 1 (by rfl) ⟨1716908, by rfl⟩ : syracuseStep 2289211 = 3433817) B3433817
theorem B17383733 : Blo 2287435 17383733 := bbase (se 5 (by rfl) ⟨814862, by rfl⟩ : syracuseStep 17383733 = 1629725) (by norm_num)
theorem B11589155 : Blo 2287435 11589155 := bstep (se 1 (by rfl) ⟨8691866, by rfl⟩ : syracuseStep 11589155 = 17383733) B17383733
theorem B7726103 : Blo 2287435 7726103 := bstep (se 1 (by rfl) ⟨5794577, by rfl⟩ : syracuseStep 7726103 = 11589155) B11589155
theorem B5150735 : Blo 2287435 5150735 := bstep (se 1 (by rfl) ⟨3863051, by rfl⟩ : syracuseStep 5150735 = 7726103) B7726103
theorem B3433823 : Blo 2287435 3433823 := bstep (se 1 (by rfl) ⟨2575367, by rfl⟩ : syracuseStep 3433823 = 5150735) B5150735
theorem B2289215 : Blo 2287435 2289215 := bstep (se 1 (by rfl) ⟨1716911, by rfl⟩ : syracuseStep 2289215 = 3433823) B3433823
theorem B3433829 : Blo 2287435 3433829 := bbase (se 4 (by rfl) ⟨321921, by rfl⟩ : syracuseStep 3433829 = 643843) (by norm_num)
theorem B2289219 : Blo 2287435 2289219 := bstep (se 1 (by rfl) ⟨1716914, by rfl⟩ : syracuseStep 2289219 = 3433829) B3433829
theorem B4345949 : Blo 2287435 4345949 := bbase (se 3 (by rfl) ⟨814865, by rfl⟩ : syracuseStep 4345949 = 1629731) (by norm_num)
theorem B2897299 : Blo 2287435 2897299 := bstep (se 1 (by rfl) ⟨2172974, by rfl⟩ : syracuseStep 2897299 = 4345949) B4345949
theorem B3863065 : Blo 2287435 3863065 := bstep (se 2 (by rfl) ⟨1448649, by rfl⟩ : syracuseStep 3863065 = 2897299) B2897299
theorem B5150753 : Blo 2287435 5150753 := bstep (se 2 (by rfl) ⟨1931532, by rfl⟩ : syracuseStep 5150753 = 3863065) B3863065
theorem B3433835 : Blo 2287435 3433835 := bstep (se 1 (by rfl) ⟨2575376, by rfl⟩ : syracuseStep 3433835 = 5150753) B5150753
theorem B2289223 : Blo 2287435 2289223 := bstep (se 1 (by rfl) ⟨1716917, by rfl⟩ : syracuseStep 2289223 = 3433835) B3433835
theorem B2575381 : Blo 2287435 2575381 := bbase (se 6 (by rfl) ⟨60360, by rfl⟩ : syracuseStep 2575381 = 120721) (by norm_num)
theorem B3433841 : Blo 2287435 3433841 := bstep (se 2 (by rfl) ⟨1287690, by rfl⟩ : syracuseStep 3433841 = 2575381) B2575381
theorem B2289227 : Blo 2287435 2289227 := bstep (se 1 (by rfl) ⟨1716920, by rfl⟩ : syracuseStep 2289227 = 3433841) B3433841
theorem B2897309 : Blo 2287435 2897309 := bbase (se 3 (by rfl) ⟨543245, by rfl⟩ : syracuseStep 2897309 = 1086491) (by norm_num)
theorem B7726157 : Blo 2287435 7726157 := bstep (se 3 (by rfl) ⟨1448654, by rfl⟩ : syracuseStep 7726157 = 2897309) B2897309
theorem B5150771 : Blo 2287435 5150771 := bstep (se 1 (by rfl) ⟨3863078, by rfl⟩ : syracuseStep 5150771 = 7726157) B7726157
theorem B3433847 : Blo 2287435 3433847 := bstep (se 1 (by rfl) ⟨2575385, by rfl⟩ : syracuseStep 3433847 = 5150771) B5150771
theorem B2289231 : Blo 2287435 2289231 := bstep (se 1 (by rfl) ⟨1716923, by rfl⟩ : syracuseStep 2289231 = 3433847) B3433847
theorem B3433853 : Blo 2287435 3433853 := bbase (se 3 (by rfl) ⟨643847, by rfl⟩ : syracuseStep 3433853 = 1287695) (by norm_num)
theorem B2289235 : Blo 2287435 2289235 := bstep (se 1 (by rfl) ⟨1716926, by rfl⟩ : syracuseStep 2289235 = 3433853) B3433853
theorem B5150789 : Blo 2287435 5150789 := bbase (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) (by norm_num)
theorem B3433859 : Blo 2287435 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B2289239 : Blo 2287435 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B6518981 : Blo 2287435 6518981 := bbase (se 4 (by rfl) ⟨611154, by rfl⟩ : syracuseStep 6518981 = 1222309) (by norm_num)
theorem B4345987 : Blo 2287435 4345987 := bstep (se 1 (by rfl) ⟨3259490, by rfl⟩ : syracuseStep 4345987 = 6518981) B6518981
theorem B5794649 : Blo 2287435 5794649 := bstep (se 2 (by rfl) ⟨2172993, by rfl⟩ : syracuseStep 5794649 = 4345987) B4345987
theorem B3863099 : Blo 2287435 3863099 := bstep (se 1 (by rfl) ⟨2897324, by rfl⟩ : syracuseStep 3863099 = 5794649) B5794649
theorem B2575399 : Blo 2287435 2575399 := bstep (se 1 (by rfl) ⟨1931549, by rfl⟩ : syracuseStep 2575399 = 3863099) B3863099
theorem B3433865 : Blo 2287435 3433865 := bstep (se 2 (by rfl) ⟨1287699, by rfl⟩ : syracuseStep 3433865 = 2575399) B2575399
theorem B2289243 : Blo 2287435 2289243 := bstep (se 1 (by rfl) ⟨1716932, by rfl⟩ : syracuseStep 2289243 = 3433865) B3433865
theorem B11589317 : Blo 2287435 11589317 := bbase (se 4 (by rfl) ⟨1086498, by rfl⟩ : syracuseStep 11589317 = 2172997) (by norm_num)
theorem B7726211 : Blo 2287435 7726211 := bstep (se 1 (by rfl) ⟨5794658, by rfl⟩ : syracuseStep 7726211 = 11589317) B11589317
theorem B5150807 : Blo 2287435 5150807 := bstep (se 1 (by rfl) ⟨3863105, by rfl⟩ : syracuseStep 5150807 = 7726211) B7726211
theorem B3433871 : Blo 2287435 3433871 := bstep (se 1 (by rfl) ⟨2575403, by rfl⟩ : syracuseStep 3433871 = 5150807) B5150807
theorem B2289247 : Blo 2287435 2289247 := bstep (se 1 (by rfl) ⟨1716935, by rfl⟩ : syracuseStep 2289247 = 3433871) B3433871
theorem B3433877 : Blo 2287435 3433877 := bbase (se 6 (by rfl) ⟨80481, by rfl⟩ : syracuseStep 3433877 = 160963) (by norm_num)
theorem B2289251 : Blo 2287435 2289251 := bstep (se 1 (by rfl) ⟨1716938, by rfl⟩ : syracuseStep 2289251 = 3433877) B3433877
theorem B4889261 : Blo 2287435 4889261 := bbase (se 3 (by rfl) ⟨916736, by rfl⟩ : syracuseStep 4889261 = 1833473) (by norm_num)
theorem B13038029 : Blo 2287435 13038029 := bstep (se 3 (by rfl) ⟨2444630, by rfl⟩ : syracuseStep 13038029 = 4889261) B4889261
theorem B8692019 : Blo 2287435 8692019 := bstep (se 1 (by rfl) ⟨6519014, by rfl⟩ : syracuseStep 8692019 = 13038029) B13038029
theorem B5794679 : Blo 2287435 5794679 := bstep (se 1 (by rfl) ⟨4346009, by rfl⟩ : syracuseStep 5794679 = 8692019) B8692019
theorem B3863119 : Blo 2287435 3863119 := bstep (se 1 (by rfl) ⟨2897339, by rfl⟩ : syracuseStep 3863119 = 5794679) B5794679
theorem B5150825 : Blo 2287435 5150825 := bstep (se 2 (by rfl) ⟨1931559, by rfl⟩ : syracuseStep 5150825 = 3863119) B3863119
theorem B3433883 : Blo 2287435 3433883 := bstep (se 1 (by rfl) ⟨2575412, by rfl⟩ : syracuseStep 3433883 = 5150825) B5150825
theorem B2289255 : Blo 2287435 2289255 := bstep (se 1 (by rfl) ⟨1716941, by rfl⟩ : syracuseStep 2289255 = 3433883) B3433883
theorem B2575417 : Blo 2287435 2575417 := bbase (se 2 (by rfl) ⟨965781, by rfl⟩ : syracuseStep 2575417 = 1931563) (by norm_num)
theorem B3433889 : Blo 2287435 3433889 := bstep (se 2 (by rfl) ⟨1287708, by rfl⟩ : syracuseStep 3433889 = 2575417) B2575417
theorem B2289259 : Blo 2287435 2289259 := bstep (se 1 (by rfl) ⟨1716944, by rfl⟩ : syracuseStep 2289259 = 3433889) B3433889
theorem B12375989 : Blo 2287435 12375989 := bbase (se 5 (by rfl) ⟨580124, by rfl⟩ : syracuseStep 12375989 = 1160249) (by norm_num)
theorem B8250659 : Blo 2287435 8250659 := bstep (se 1 (by rfl) ⟨6187994, by rfl⟩ : syracuseStep 8250659 = 12375989) B12375989
theorem B5500439 : Blo 2287435 5500439 := bstep (se 1 (by rfl) ⟨4125329, by rfl⟩ : syracuseStep 5500439 = 8250659) B8250659
theorem B3666959 : Blo 2287435 3666959 := bstep (se 1 (by rfl) ⟨2750219, by rfl⟩ : syracuseStep 3666959 = 5500439) B5500439
theorem B2444639 : Blo 2287435 2444639 := bstep (se 1 (by rfl) ⟨1833479, by rfl⟩ : syracuseStep 2444639 = 3666959) B3666959
theorem B6519037 : Blo 2287435 6519037 := bstep (se 3 (by rfl) ⟨1222319, by rfl⟩ : syracuseStep 6519037 = 2444639) B2444639
theorem B8692049 : Blo 2287435 8692049 := bstep (se 2 (by rfl) ⟨3259518, by rfl⟩ : syracuseStep 8692049 = 6519037) B6519037
theorem B5794699 : Blo 2287435 5794699 := bstep (se 1 (by rfl) ⟨4346024, by rfl⟩ : syracuseStep 5794699 = 8692049) B8692049
theorem B7726265 : Blo 2287435 7726265 := bstep (se 2 (by rfl) ⟨2897349, by rfl⟩ : syracuseStep 7726265 = 5794699) B5794699
theorem B5150843 : Blo 2287435 5150843 := bstep (se 1 (by rfl) ⟨3863132, by rfl⟩ : syracuseStep 5150843 = 7726265) B7726265
theorem B3433895 : Blo 2287435 3433895 := bstep (se 1 (by rfl) ⟨2575421, by rfl⟩ : syracuseStep 3433895 = 5150843) B5150843
theorem B2289263 : Blo 2287435 2289263 := bstep (se 1 (by rfl) ⟨1716947, by rfl⟩ : syracuseStep 2289263 = 3433895) B3433895
theorem B3433901 : Blo 2287435 3433901 := bbase (se 3 (by rfl) ⟨643856, by rfl⟩ : syracuseStep 3433901 = 1287713) (by norm_num)
theorem B2289267 : Blo 2287435 2289267 := bstep (se 1 (by rfl) ⟨1716950, by rfl⟩ : syracuseStep 2289267 = 3433901) B3433901
theorem B5150861 : Blo 2287435 5150861 := bbase (se 3 (by rfl) ⟨965786, by rfl⟩ : syracuseStep 5150861 = 1931573) (by norm_num)
theorem B3433907 : Blo 2287435 3433907 := bstep (se 1 (by rfl) ⟨2575430, by rfl⟩ : syracuseStep 3433907 = 5150861) B5150861
theorem B2289271 : Blo 2287435 2289271 := bstep (se 1 (by rfl) ⟨1716953, by rfl⟩ : syracuseStep 2289271 = 3433907) B3433907
theorem B2897365 : Blo 2287435 2897365 := bbase (se 7 (by rfl) ⟨33953, by rfl⟩ : syracuseStep 2897365 = 67907) (by norm_num)
theorem B3863153 : Blo 2287435 3863153 := bstep (se 2 (by rfl) ⟨1448682, by rfl⟩ : syracuseStep 3863153 = 2897365) B2897365
theorem B2575435 : Blo 2287435 2575435 := bstep (se 1 (by rfl) ⟨1931576, by rfl⟩ : syracuseStep 2575435 = 3863153) B3863153
theorem B3433913 : Blo 2287435 3433913 := bstep (se 2 (by rfl) ⟨1287717, by rfl⟩ : syracuseStep 3433913 = 2575435) B2575435
theorem B2289275 : Blo 2287435 2289275 := bstep (se 1 (by rfl) ⟨1716956, by rfl⟩ : syracuseStep 2289275 = 3433913) B3433913
theorem B17861813 : Blo 2287435 17861813 := bbase (se 5 (by rfl) ⟨837272, by rfl⟩ : syracuseStep 17861813 = 1674545) (by norm_num)
theorem B11907875 : Blo 2287435 11907875 := bstep (se 1 (by rfl) ⟨8930906, by rfl⟩ : syracuseStep 11907875 = 17861813) B17861813
theorem B7938583 : Blo 2287435 7938583 := bstep (se 1 (by rfl) ⟨5953937, by rfl⟩ : syracuseStep 7938583 = 11907875) B11907875
theorem B169356437 : Blo 2287435 169356437 := bstep (se 6 (by rfl) ⟨3969291, by rfl⟩ : syracuseStep 169356437 = 7938583) B7938583
theorem B112904291 : Blo 2287435 112904291 := bstep (se 1 (by rfl) ⟨84678218, by rfl⟩ : syracuseStep 112904291 = 169356437) B169356437
theorem B301078109 : Blo 2287435 301078109 := bstep (se 3 (by rfl) ⟨56452145, by rfl⟩ : syracuseStep 301078109 = 112904291) B112904291
theorem B200718739 : Blo 2287435 200718739 := bstep (se 1 (by rfl) ⟨150539054, by rfl⟩ : syracuseStep 200718739 = 301078109) B301078109
theorem B267624985 : Blo 2287435 267624985 := bstep (se 2 (by rfl) ⟨100359369, by rfl⟩ : syracuseStep 267624985 = 200718739) B200718739
theorem B356833313 : Blo 2287435 356833313 := bstep (se 2 (by rfl) ⟨133812492, by rfl⟩ : syracuseStep 356833313 = 267624985) B267624985
theorem B237888875 : Blo 2287435 237888875 := bstep (se 1 (by rfl) ⟨178416656, by rfl⟩ : syracuseStep 237888875 = 356833313) B356833313
theorem B158592583 : Blo 2287435 158592583 := bstep (se 1 (by rfl) ⟨118944437, by rfl⟩ : syracuseStep 158592583 = 237888875) B237888875
theorem B211456777 : Blo 2287435 211456777 := bstep (se 2 (by rfl) ⟨79296291, by rfl⟩ : syracuseStep 211456777 = 158592583) B158592583
theorem B281942369 : Blo 2287435 281942369 := bstep (se 2 (by rfl) ⟨105728388, by rfl⟩ : syracuseStep 281942369 = 211456777) B211456777
theorem B187961579 : Blo 2287435 187961579 := bstep (se 1 (by rfl) ⟨140971184, by rfl⟩ : syracuseStep 187961579 = 281942369) B281942369
theorem B125307719 : Blo 2287435 125307719 := bstep (se 1 (by rfl) ⟨93980789, by rfl⟩ : syracuseStep 125307719 = 187961579) B187961579
theorem B83538479 : Blo 2287435 83538479 := bstep (se 1 (by rfl) ⟨62653859, by rfl⟩ : syracuseStep 83538479 = 125307719) B125307719
theorem B222769277 : Blo 2287435 222769277 := bstep (se 3 (by rfl) ⟨41769239, by rfl⟩ : syracuseStep 222769277 = 83538479) B83538479
theorem B148512851 : Blo 2287435 148512851 := bstep (se 1 (by rfl) ⟨111384638, by rfl⟩ : syracuseStep 148512851 = 222769277) B222769277
theorem B99008567 : Blo 2287435 99008567 := bstep (se 1 (by rfl) ⟨74256425, by rfl⟩ : syracuseStep 99008567 = 148512851) B148512851
theorem B66005711 : Blo 2287435 66005711 := bstep (se 1 (by rfl) ⟨49504283, by rfl⟩ : syracuseStep 66005711 = 99008567) B99008567
theorem B44003807 : Blo 2287435 44003807 := bstep (se 1 (by rfl) ⟨33002855, by rfl⟩ : syracuseStep 44003807 = 66005711) B66005711
theorem B29335871 : Blo 2287435 29335871 := bstep (se 1 (by rfl) ⟨22001903, by rfl⟩ : syracuseStep 29335871 = 44003807) B44003807
theorem B19557247 : Blo 2287435 19557247 := bstep (se 1 (by rfl) ⟨14667935, by rfl⟩ : syracuseStep 19557247 = 29335871) B29335871
theorem B26076329 : Blo 2287435 26076329 := bstep (se 2 (by rfl) ⟨9778623, by rfl⟩ : syracuseStep 26076329 = 19557247) B19557247
theorem B17384219 : Blo 2287435 17384219 := bstep (se 1 (by rfl) ⟨13038164, by rfl⟩ : syracuseStep 17384219 = 26076329) B26076329
theorem B11589479 : Blo 2287435 11589479 := bstep (se 1 (by rfl) ⟨8692109, by rfl⟩ : syracuseStep 11589479 = 17384219) B17384219
theorem B7726319 : Blo 2287435 7726319 := bstep (se 1 (by rfl) ⟨5794739, by rfl⟩ : syracuseStep 7726319 = 11589479) B11589479
theorem B5150879 : Blo 2287435 5150879 := bstep (se 1 (by rfl) ⟨3863159, by rfl⟩ : syracuseStep 5150879 = 7726319) B7726319
theorem B3433919 : Blo 2287435 3433919 := bstep (se 1 (by rfl) ⟨2575439, by rfl⟩ : syracuseStep 3433919 = 5150879) B5150879
theorem B2289279 : Blo 2287435 2289279 := bstep (se 1 (by rfl) ⟨1716959, by rfl⟩ : syracuseStep 2289279 = 3433919) B3433919
theorem B3433925 : Blo 2287435 3433925 := bbase (se 4 (by rfl) ⟨321930, by rfl⟩ : syracuseStep 3433925 = 643861) (by norm_num)
theorem B2289283 : Blo 2287435 2289283 := bstep (se 1 (by rfl) ⟨1716962, by rfl⟩ : syracuseStep 2289283 = 3433925) B3433925
theorem B3863173 : Blo 2287435 3863173 := bbase (se 4 (by rfl) ⟨362172, by rfl⟩ : syracuseStep 3863173 = 724345) (by norm_num)
theorem B5150897 : Blo 2287435 5150897 := bstep (se 2 (by rfl) ⟨1931586, by rfl⟩ : syracuseStep 5150897 = 3863173) B3863173
theorem B3433931 : Blo 2287435 3433931 := bstep (se 1 (by rfl) ⟨2575448, by rfl⟩ : syracuseStep 3433931 = 5150897) B5150897
theorem B2289287 : Blo 2287435 2289287 := bstep (se 1 (by rfl) ⟨1716965, by rfl⟩ : syracuseStep 2289287 = 3433931) B3433931
theorem B2575453 : Blo 2287435 2575453 := bbase (se 3 (by rfl) ⟨482897, by rfl⟩ : syracuseStep 2575453 = 965795) (by norm_num)
theorem B3433937 : Blo 2287435 3433937 := bstep (se 2 (by rfl) ⟨1287726, by rfl⟩ : syracuseStep 3433937 = 2575453) B2575453
theorem B2289291 : Blo 2287435 2289291 := bstep (se 1 (by rfl) ⟨1716968, by rfl⟩ : syracuseStep 2289291 = 3433937) B3433937
theorem B7726373 : Blo 2287435 7726373 := bbase (se 4 (by rfl) ⟨724347, by rfl⟩ : syracuseStep 7726373 = 1448695) (by norm_num)
theorem B5150915 : Blo 2287435 5150915 := bstep (se 1 (by rfl) ⟨3863186, by rfl⟩ : syracuseStep 5150915 = 7726373) B7726373
theorem B3433943 : Blo 2287435 3433943 := bstep (se 1 (by rfl) ⟨2575457, by rfl⟩ : syracuseStep 3433943 = 5150915) B5150915
theorem B2289295 : Blo 2287435 2289295 := bstep (se 1 (by rfl) ⟨1716971, by rfl⟩ : syracuseStep 2289295 = 3433943) B3433943
theorem B3433949 : Blo 2287435 3433949 := bbase (se 3 (by rfl) ⟨643865, by rfl⟩ : syracuseStep 3433949 = 1287731) (by norm_num)
theorem B2289299 : Blo 2287435 2289299 := bstep (se 1 (by rfl) ⟨1716974, by rfl⟩ : syracuseStep 2289299 = 3433949) B3433949
theorem B5150933 : Blo 2287435 5150933 := bbase (se 7 (by rfl) ⟨60362, by rfl⟩ : syracuseStep 5150933 = 120725) (by norm_num)
theorem B3433955 : Blo 2287435 3433955 := bstep (se 1 (by rfl) ⟨2575466, by rfl⟩ : syracuseStep 3433955 = 5150933) B5150933
theorem B2289303 : Blo 2287435 2289303 := bstep (se 1 (by rfl) ⟨1716977, by rfl⟩ : syracuseStep 2289303 = 3433955) B3433955
theorem B4641085 : Blo 2287435 4641085 := bbase (se 3 (by rfl) ⟨870203, by rfl⟩ : syracuseStep 4641085 = 1740407) (by norm_num)
theorem B6188113 : Blo 2287435 6188113 := bstep (se 2 (by rfl) ⟨2320542, by rfl⟩ : syracuseStep 6188113 = 4641085) B4641085
theorem B8250817 : Blo 2287435 8250817 := bstep (se 2 (by rfl) ⟨3094056, by rfl⟩ : syracuseStep 8250817 = 6188113) B6188113
theorem B11001089 : Blo 2287435 11001089 := bstep (se 2 (by rfl) ⟨4125408, by rfl⟩ : syracuseStep 11001089 = 8250817) B8250817
theorem B7334059 : Blo 2287435 7334059 := bstep (se 1 (by rfl) ⟨5500544, by rfl⟩ : syracuseStep 7334059 = 11001089) B11001089
theorem B9778745 : Blo 2287435 9778745 := bstep (se 2 (by rfl) ⟨3667029, by rfl⟩ : syracuseStep 9778745 = 7334059) B7334059
theorem B6519163 : Blo 2287435 6519163 := bstep (se 1 (by rfl) ⟨4889372, by rfl⟩ : syracuseStep 6519163 = 9778745) B9778745
theorem B8692217 : Blo 2287435 8692217 := bstep (se 2 (by rfl) ⟨3259581, by rfl⟩ : syracuseStep 8692217 = 6519163) B6519163
theorem B5794811 : Blo 2287435 5794811 := bstep (se 1 (by rfl) ⟨4346108, by rfl⟩ : syracuseStep 5794811 = 8692217) B8692217
theorem B3863207 : Blo 2287435 3863207 := bstep (se 1 (by rfl) ⟨2897405, by rfl⟩ : syracuseStep 3863207 = 5794811) B5794811
theorem B2575471 : Blo 2287435 2575471 := bstep (se 1 (by rfl) ⟨1931603, by rfl⟩ : syracuseStep 2575471 = 3863207) B3863207
theorem B3433961 : Blo 2287435 3433961 := bstep (se 2 (by rfl) ⟨1287735, by rfl⟩ : syracuseStep 3433961 = 2575471) B2575471
theorem B2289307 : Blo 2287435 2289307 := bstep (se 1 (by rfl) ⟨1716980, by rfl⟩ : syracuseStep 2289307 = 3433961) B3433961
theorem B4181701 : Blo 2287435 4181701 := bbase (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) (by norm_num)
theorem B5575601 : Blo 2287435 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B14868269 : Blo 2287435 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B9912179 : Blo 2287435 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B26432477 : Blo 2287435 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B17621651 : Blo 2287435 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B11747767 : Blo 2287435 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B15663689 : Blo 2287435 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B10442459 : Blo 2287435 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B6961639 : Blo 2287435 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B9282185 : Blo 2287435 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B6188123 : Blo 2287435 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B4125415 : Blo 2287435 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B5500553 : Blo 2287435 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B14668141 : Blo 2287435 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B19557521 : Blo 2287435 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B13038347 : Blo 2287435 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B8692231 : Blo 2287435 8692231 := bstep (se 1 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 8692231 = 13038347) B13038347
theorem B11589641 : Blo 2287435 11589641 := bstep (se 2 (by rfl) ⟨4346115, by rfl⟩ : syracuseStep 11589641 = 8692231) B8692231
theorem B7726427 : Blo 2287435 7726427 := bstep (se 1 (by rfl) ⟨5794820, by rfl⟩ : syracuseStep 7726427 = 11589641) B11589641
theorem B5150951 : Blo 2287435 5150951 := bstep (se 1 (by rfl) ⟨3863213, by rfl⟩ : syracuseStep 5150951 = 7726427) B7726427
theorem B3433967 : Blo 2287435 3433967 := bstep (se 1 (by rfl) ⟨2575475, by rfl⟩ : syracuseStep 3433967 = 5150951) B5150951
theorem B2289311 : Blo 2287435 2289311 := bstep (se 1 (by rfl) ⟨1716983, by rfl⟩ : syracuseStep 2289311 = 3433967) B3433967
theorem B3433973 : Blo 2287435 3433973 := bbase (se 5 (by rfl) ⟨160967, by rfl⟩ : syracuseStep 3433973 = 321935) (by norm_num)
theorem B2289315 : Blo 2287435 2289315 := bstep (se 1 (by rfl) ⟨1716986, by rfl⟩ : syracuseStep 2289315 = 3433973) B3433973
theorem B2610625 : Blo 2287435 2610625 := bbase (se 2 (by rfl) ⟨978984, by rfl⟩ : syracuseStep 2610625 = 1957969) (by norm_num)
theorem B3480833 : Blo 2287435 3480833 := bstep (se 2 (by rfl) ⟨1305312, by rfl⟩ : syracuseStep 3480833 = 2610625) B2610625
theorem B9282221 : Blo 2287435 9282221 := bstep (se 3 (by rfl) ⟨1740416, by rfl⟩ : syracuseStep 9282221 = 3480833) B3480833
theorem B6188147 : Blo 2287435 6188147 := bstep (se 1 (by rfl) ⟨4641110, by rfl⟩ : syracuseStep 6188147 = 9282221) B9282221
theorem B4125431 : Blo 2287435 4125431 := bstep (se 1 (by rfl) ⟨3094073, by rfl⟩ : syracuseStep 4125431 = 6188147) B6188147
theorem B2750287 : Blo 2287435 2750287 := bstep (se 1 (by rfl) ⟨2062715, by rfl⟩ : syracuseStep 2750287 = 4125431) B4125431
theorem B3667049 : Blo 2287435 3667049 := bstep (se 2 (by rfl) ⟨1375143, by rfl⟩ : syracuseStep 3667049 = 2750287) B2750287
theorem B2444699 : Blo 2287435 2444699 := bstep (se 1 (by rfl) ⟨1833524, by rfl⟩ : syracuseStep 2444699 = 3667049) B3667049
theorem B6519197 : Blo 2287435 6519197 := bstep (se 3 (by rfl) ⟨1222349, by rfl⟩ : syracuseStep 6519197 = 2444699) B2444699
theorem B4346131 : Blo 2287435 4346131 := bstep (se 1 (by rfl) ⟨3259598, by rfl⟩ : syracuseStep 4346131 = 6519197) B6519197
theorem B5794841 : Blo 2287435 5794841 := bstep (se 2 (by rfl) ⟨2173065, by rfl⟩ : syracuseStep 5794841 = 4346131) B4346131
theorem B3863227 : Blo 2287435 3863227 := bstep (se 1 (by rfl) ⟨2897420, by rfl⟩ : syracuseStep 3863227 = 5794841) B5794841
theorem B5150969 : Blo 2287435 5150969 := bstep (se 2 (by rfl) ⟨1931613, by rfl⟩ : syracuseStep 5150969 = 3863227) B3863227
theorem B3433979 : Blo 2287435 3433979 := bstep (se 1 (by rfl) ⟨2575484, by rfl⟩ : syracuseStep 3433979 = 5150969) B5150969
theorem B2289319 : Blo 2287435 2289319 := bstep (se 1 (by rfl) ⟨1716989, by rfl⟩ : syracuseStep 2289319 = 3433979) B3433979
theorem B2575489 : Blo 2287435 2575489 := bbase (se 2 (by rfl) ⟨965808, by rfl⟩ : syracuseStep 2575489 = 1931617) (by norm_num)
theorem B3433985 : Blo 2287435 3433985 := bstep (se 2 (by rfl) ⟨1287744, by rfl⟩ : syracuseStep 3433985 = 2575489) B2575489
theorem B2289323 : Blo 2287435 2289323 := bstep (se 1 (by rfl) ⟨1716992, by rfl⟩ : syracuseStep 2289323 = 3433985) B3433985
theorem B5794861 : Blo 2287435 5794861 := bbase (se 3 (by rfl) ⟨1086536, by rfl⟩ : syracuseStep 5794861 = 2173073) (by norm_num)
theorem B7726481 : Blo 2287435 7726481 := bstep (se 2 (by rfl) ⟨2897430, by rfl⟩ : syracuseStep 7726481 = 5794861) B5794861
theorem B5150987 : Blo 2287435 5150987 := bstep (se 1 (by rfl) ⟨3863240, by rfl⟩ : syracuseStep 5150987 = 7726481) B7726481
theorem B3433991 : Blo 2287435 3433991 := bstep (se 1 (by rfl) ⟨2575493, by rfl⟩ : syracuseStep 3433991 = 5150987) B5150987
theorem B2289327 : Blo 2287435 2289327 := bstep (se 1 (by rfl) ⟨1716995, by rfl⟩ : syracuseStep 2289327 = 3433991) B3433991
theorem B3433997 : Blo 2287435 3433997 := bbase (se 3 (by rfl) ⟨643874, by rfl⟩ : syracuseStep 3433997 = 1287749) (by norm_num)
theorem B2289331 : Blo 2287435 2289331 := bstep (se 1 (by rfl) ⟨1716998, by rfl⟩ : syracuseStep 2289331 = 3433997) B3433997
theorem B5151005 : Blo 2287435 5151005 := bbase (se 3 (by rfl) ⟨965813, by rfl⟩ : syracuseStep 5151005 = 1931627) (by norm_num)
theorem B3434003 : Blo 2287435 3434003 := bstep (se 1 (by rfl) ⟨2575502, by rfl⟩ : syracuseStep 3434003 = 5151005) B5151005
theorem B2289335 : Blo 2287435 2289335 := bstep (se 1 (by rfl) ⟨1717001, by rfl⟩ : syracuseStep 2289335 = 3434003) B3434003
theorem B3863261 : Blo 2287435 3863261 := bbase (se 3 (by rfl) ⟨724361, by rfl⟩ : syracuseStep 3863261 = 1448723) (by norm_num)
theorem B2575507 : Blo 2287435 2575507 := bstep (se 1 (by rfl) ⟨1931630, by rfl⟩ : syracuseStep 2575507 = 3863261) B3863261
theorem B3434009 : Blo 2287435 3434009 := bstep (se 2 (by rfl) ⟨1287753, by rfl⟩ : syracuseStep 3434009 = 2575507) B2575507
theorem B2289339 : Blo 2287435 2289339 := bstep (se 1 (by rfl) ⟨1717004, by rfl⟩ : syracuseStep 2289339 = 3434009) B3434009
theorem B3480869 : Blo 2287435 3480869 := bbase (se 4 (by rfl) ⟨326331, by rfl⟩ : syracuseStep 3480869 = 652663) (by norm_num)
theorem B2320579 : Blo 2287435 2320579 := bstep (se 1 (by rfl) ⟨1740434, by rfl⟩ : syracuseStep 2320579 = 3480869) B3480869
theorem B3094105 : Blo 2287435 3094105 := bstep (se 2 (by rfl) ⟨1160289, by rfl⟩ : syracuseStep 3094105 = 2320579) B2320579
theorem B4125473 : Blo 2287435 4125473 := bstep (se 2 (by rfl) ⟨1547052, by rfl⟩ : syracuseStep 4125473 = 3094105) B3094105
theorem B2750315 : Blo 2287435 2750315 := bstep (se 1 (by rfl) ⟨2062736, by rfl⟩ : syracuseStep 2750315 = 4125473) B4125473
theorem B7334173 : Blo 2287435 7334173 := bstep (se 3 (by rfl) ⟨1375157, by rfl⟩ : syracuseStep 7334173 = 2750315) B2750315
theorem B9778897 : Blo 2287435 9778897 := bstep (se 2 (by rfl) ⟨3667086, by rfl⟩ : syracuseStep 9778897 = 7334173) B7334173
theorem B13038529 : Blo 2287435 13038529 := bstep (se 2 (by rfl) ⟨4889448, by rfl⟩ : syracuseStep 13038529 = 9778897) B9778897
theorem B17384705 : Blo 2287435 17384705 := bstep (se 2 (by rfl) ⟨6519264, by rfl⟩ : syracuseStep 17384705 = 13038529) B13038529
theorem B11589803 : Blo 2287435 11589803 := bstep (se 1 (by rfl) ⟨8692352, by rfl⟩ : syracuseStep 11589803 = 17384705) B17384705
theorem B7726535 : Blo 2287435 7726535 := bstep (se 1 (by rfl) ⟨5794901, by rfl⟩ : syracuseStep 7726535 = 11589803) B11589803
theorem B5151023 : Blo 2287435 5151023 := bstep (se 1 (by rfl) ⟨3863267, by rfl⟩ : syracuseStep 5151023 = 7726535) B7726535
theorem B3434015 : Blo 2287435 3434015 := bstep (se 1 (by rfl) ⟨2575511, by rfl⟩ : syracuseStep 3434015 = 5151023) B5151023
theorem B2289343 : Blo 2287435 2289343 := bstep (se 1 (by rfl) ⟨1717007, by rfl⟩ : syracuseStep 2289343 = 3434015) B3434015
theorem B3434021 : Blo 2287435 3434021 := bbase (se 4 (by rfl) ⟨321939, by rfl⟩ : syracuseStep 3434021 = 643879) (by norm_num)
theorem B2289347 : Blo 2287435 2289347 := bstep (se 1 (by rfl) ⟨1717010, by rfl⟩ : syracuseStep 2289347 = 3434021) B3434021
theorem B2897461 : Blo 2287435 2897461 := bbase (se 5 (by rfl) ⟨135818, by rfl⟩ : syracuseStep 2897461 = 271637) (by norm_num)
theorem B3863281 : Blo 2287435 3863281 := bstep (se 2 (by rfl) ⟨1448730, by rfl⟩ : syracuseStep 3863281 = 2897461) B2897461
theorem B5151041 : Blo 2287435 5151041 := bstep (se 2 (by rfl) ⟨1931640, by rfl⟩ : syracuseStep 5151041 = 3863281) B3863281
theorem B3434027 : Blo 2287435 3434027 := bstep (se 1 (by rfl) ⟨2575520, by rfl⟩ : syracuseStep 3434027 = 5151041) B5151041
theorem B2289351 : Blo 2287435 2289351 := bstep (se 1 (by rfl) ⟨1717013, by rfl⟩ : syracuseStep 2289351 = 3434027) B3434027
theorem B2575525 : Blo 2287435 2575525 := bbase (se 4 (by rfl) ⟨241455, by rfl⟩ : syracuseStep 2575525 = 482911) (by norm_num)
theorem B3434033 : Blo 2287435 3434033 := bstep (se 2 (by rfl) ⟨1287762, by rfl⟩ : syracuseStep 3434033 = 2575525) B2575525
theorem B2289355 : Blo 2287435 2289355 := bstep (se 1 (by rfl) ⟨1717016, by rfl⟩ : syracuseStep 2289355 = 3434033) B3434033
theorem B22002677 : Blo 2287435 22002677 := bbase (se 5 (by rfl) ⟨1031375, by rfl⟩ : syracuseStep 22002677 = 2062751) (by norm_num)
theorem B14668451 : Blo 2287435 14668451 := bstep (se 1 (by rfl) ⟨11001338, by rfl⟩ : syracuseStep 14668451 = 22002677) B22002677
theorem B9778967 : Blo 2287435 9778967 := bstep (se 1 (by rfl) ⟨7334225, by rfl⟩ : syracuseStep 9778967 = 14668451) B14668451
theorem B6519311 : Blo 2287435 6519311 := bstep (se 1 (by rfl) ⟨4889483, by rfl⟩ : syracuseStep 6519311 = 9778967) B9778967
theorem B4346207 : Blo 2287435 4346207 := bstep (se 1 (by rfl) ⟨3259655, by rfl⟩ : syracuseStep 4346207 = 6519311) B6519311
theorem B2897471 : Blo 2287435 2897471 := bstep (se 1 (by rfl) ⟨2173103, by rfl⟩ : syracuseStep 2897471 = 4346207) B4346207
theorem B7726589 : Blo 2287435 7726589 := bstep (se 3 (by rfl) ⟨1448735, by rfl⟩ : syracuseStep 7726589 = 2897471) B2897471
theorem B5151059 : Blo 2287435 5151059 := bstep (se 1 (by rfl) ⟨3863294, by rfl⟩ : syracuseStep 5151059 = 7726589) B7726589
theorem B3434039 : Blo 2287435 3434039 := bstep (se 1 (by rfl) ⟨2575529, by rfl⟩ : syracuseStep 3434039 = 5151059) B5151059
theorem B2289359 : Blo 2287435 2289359 := bstep (se 1 (by rfl) ⟨1717019, by rfl⟩ : syracuseStep 2289359 = 3434039) B3434039
theorem B3434045 : Blo 2287435 3434045 := bbase (se 3 (by rfl) ⟨643883, by rfl⟩ : syracuseStep 3434045 = 1287767) (by norm_num)
theorem B2289363 : Blo 2287435 2289363 := bstep (se 1 (by rfl) ⟨1717022, by rfl⟩ : syracuseStep 2289363 = 3434045) B3434045
theorem B5151077 : Blo 2287435 5151077 := bbase (se 4 (by rfl) ⟨482913, by rfl⟩ : syracuseStep 5151077 = 965827) (by norm_num)
theorem B3434051 : Blo 2287435 3434051 := bstep (se 1 (by rfl) ⟨2575538, by rfl⟩ : syracuseStep 3434051 = 5151077) B5151077
theorem B2289367 : Blo 2287435 2289367 := bstep (se 1 (by rfl) ⟨1717025, by rfl⟩ : syracuseStep 2289367 = 3434051) B3434051
theorem B5794973 : Blo 2287435 5794973 := bbase (se 3 (by rfl) ⟨1086557, by rfl⟩ : syracuseStep 5794973 = 2173115) (by norm_num)
theorem B3863315 : Blo 2287435 3863315 := bstep (se 1 (by rfl) ⟨2897486, by rfl⟩ : syracuseStep 3863315 = 5794973) B5794973
theorem B2575543 : Blo 2287435 2575543 := bstep (se 1 (by rfl) ⟨1931657, by rfl⟩ : syracuseStep 2575543 = 3863315) B3863315
theorem B3434057 : Blo 2287435 3434057 := bstep (se 2 (by rfl) ⟨1287771, by rfl⟩ : syracuseStep 3434057 = 2575543) B2575543
theorem B2289371 : Blo 2287435 2289371 := bstep (se 1 (by rfl) ⟨1717028, by rfl⟩ : syracuseStep 2289371 = 3434057) B3434057
theorem B4346237 : Blo 2287435 4346237 := bbase (se 3 (by rfl) ⟨814919, by rfl⟩ : syracuseStep 4346237 = 1629839) (by norm_num)
theorem B11589965 : Blo 2287435 11589965 := bstep (se 3 (by rfl) ⟨2173118, by rfl⟩ : syracuseStep 11589965 = 4346237) B4346237
theorem B7726643 : Blo 2287435 7726643 := bstep (se 1 (by rfl) ⟨5794982, by rfl⟩ : syracuseStep 7726643 = 11589965) B11589965
theorem B5151095 : Blo 2287435 5151095 := bstep (se 1 (by rfl) ⟨3863321, by rfl⟩ : syracuseStep 5151095 = 7726643) B7726643
theorem B3434063 : Blo 2287435 3434063 := bstep (se 1 (by rfl) ⟨2575547, by rfl⟩ : syracuseStep 3434063 = 5151095) B5151095
theorem B2289375 : Blo 2287435 2289375 := bstep (se 1 (by rfl) ⟨1717031, by rfl⟩ : syracuseStep 2289375 = 3434063) B3434063
theorem B3434069 : Blo 2287435 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B2289379 : Blo 2287435 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B10442789 : Blo 2287435 10442789 := bbase (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) (by norm_num)
theorem B6961859 : Blo 2287435 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B4641239 : Blo 2287435 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B12376637 : Blo 2287435 12376637 := bstep (se 3 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 12376637 = 4641239) B4641239
theorem B8251091 : Blo 2287435 8251091 := bstep (se 1 (by rfl) ⟨6188318, by rfl⟩ : syracuseStep 8251091 = 12376637) B12376637
theorem B5500727 : Blo 2287435 5500727 := bstep (se 1 (by rfl) ⟨4125545, by rfl⟩ : syracuseStep 5500727 = 8251091) B8251091
theorem B3667151 : Blo 2287435 3667151 := bstep (se 1 (by rfl) ⟨2750363, by rfl⟩ : syracuseStep 3667151 = 5500727) B5500727
theorem B9779069 : Blo 2287435 9779069 := bstep (se 3 (by rfl) ⟨1833575, by rfl⟩ : syracuseStep 9779069 = 3667151) B3667151
theorem B6519379 : Blo 2287435 6519379 := bstep (se 1 (by rfl) ⟨4889534, by rfl⟩ : syracuseStep 6519379 = 9779069) B9779069
theorem B8692505 : Blo 2287435 8692505 := bstep (se 2 (by rfl) ⟨3259689, by rfl⟩ : syracuseStep 8692505 = 6519379) B6519379
theorem B5795003 : Blo 2287435 5795003 := bstep (se 1 (by rfl) ⟨4346252, by rfl⟩ : syracuseStep 5795003 = 8692505) B8692505
theorem B3863335 : Blo 2287435 3863335 := bstep (se 1 (by rfl) ⟨2897501, by rfl⟩ : syracuseStep 3863335 = 5795003) B5795003
theorem B5151113 : Blo 2287435 5151113 := bstep (se 2 (by rfl) ⟨1931667, by rfl⟩ : syracuseStep 5151113 = 3863335) B3863335
theorem B3434075 : Blo 2287435 3434075 := bstep (se 1 (by rfl) ⟨2575556, by rfl⟩ : syracuseStep 3434075 = 5151113) B5151113
theorem B2289383 : Blo 2287435 2289383 := bstep (se 1 (by rfl) ⟨1717037, by rfl⟩ : syracuseStep 2289383 = 3434075) B3434075
theorem B2575561 : Blo 2287435 2575561 := bbase (se 2 (by rfl) ⟨965835, by rfl⟩ : syracuseStep 2575561 = 1931671) (by norm_num)
theorem B3434081 : Blo 2287435 3434081 := bstep (se 2 (by rfl) ⟨1287780, by rfl⟩ : syracuseStep 3434081 = 2575561) B2575561
theorem B2289387 : Blo 2287435 2289387 := bstep (se 1 (by rfl) ⟨1717040, by rfl⟩ : syracuseStep 2289387 = 3434081) B3434081
theorem B3480941 : Blo 2287435 3480941 := bbase (se 3 (by rfl) ⟨652676, by rfl⟩ : syracuseStep 3480941 = 1305353) (by norm_num)
theorem B9282509 : Blo 2287435 9282509 := bstep (se 3 (by rfl) ⟨1740470, by rfl⟩ : syracuseStep 9282509 = 3480941) B3480941
theorem B6188339 : Blo 2287435 6188339 := bstep (se 1 (by rfl) ⟨4641254, by rfl⟩ : syracuseStep 6188339 = 9282509) B9282509
theorem B16502237 : Blo 2287435 16502237 := bstep (se 3 (by rfl) ⟨3094169, by rfl⟩ : syracuseStep 16502237 = 6188339) B6188339
theorem B11001491 : Blo 2287435 11001491 := bstep (se 1 (by rfl) ⟨8251118, by rfl⟩ : syracuseStep 11001491 = 16502237) B16502237
theorem B7334327 : Blo 2287435 7334327 := bstep (se 1 (by rfl) ⟨5500745, by rfl⟩ : syracuseStep 7334327 = 11001491) B11001491
theorem B19558205 : Blo 2287435 19558205 := bstep (se 3 (by rfl) ⟨3667163, by rfl⟩ : syracuseStep 19558205 = 7334327) B7334327
theorem B13038803 : Blo 2287435 13038803 := bstep (se 1 (by rfl) ⟨9779102, by rfl⟩ : syracuseStep 13038803 = 19558205) B19558205
theorem B8692535 : Blo 2287435 8692535 := bstep (se 1 (by rfl) ⟨6519401, by rfl⟩ : syracuseStep 8692535 = 13038803) B13038803
theorem B5795023 : Blo 2287435 5795023 := bstep (se 1 (by rfl) ⟨4346267, by rfl⟩ : syracuseStep 5795023 = 8692535) B8692535
theorem B7726697 : Blo 2287435 7726697 := bstep (se 2 (by rfl) ⟨2897511, by rfl⟩ : syracuseStep 7726697 = 5795023) B5795023
theorem B5151131 : Blo 2287435 5151131 := bstep (se 1 (by rfl) ⟨3863348, by rfl⟩ : syracuseStep 5151131 = 7726697) B7726697
theorem B3434087 : Blo 2287435 3434087 := bstep (se 1 (by rfl) ⟨2575565, by rfl⟩ : syracuseStep 3434087 = 5151131) B5151131
theorem B2289391 : Blo 2287435 2289391 := bstep (se 1 (by rfl) ⟨1717043, by rfl⟩ : syracuseStep 2289391 = 3434087) B3434087
theorem B3434093 : Blo 2287435 3434093 := bbase (se 3 (by rfl) ⟨643892, by rfl⟩ : syracuseStep 3434093 = 1287785) (by norm_num)
theorem B2289395 : Blo 2287435 2289395 := bstep (se 1 (by rfl) ⟨1717046, by rfl⟩ : syracuseStep 2289395 = 3434093) B3434093
theorem B5151149 : Blo 2287435 5151149 := bbase (se 3 (by rfl) ⟨965840, by rfl⟩ : syracuseStep 5151149 = 1931681) (by norm_num)
theorem B3434099 : Blo 2287435 3434099 := bstep (se 1 (by rfl) ⟨2575574, by rfl⟩ : syracuseStep 3434099 = 5151149) B5151149
theorem B2289399 : Blo 2287435 2289399 := bstep (se 1 (by rfl) ⟨1717049, by rfl⟩ : syracuseStep 2289399 = 3434099) B3434099
theorem B2444789 : Blo 2287435 2444789 := bbase (se 5 (by rfl) ⟨114599, by rfl⟩ : syracuseStep 2444789 = 229199) (by norm_num)
theorem B6519437 : Blo 2287435 6519437 := bstep (se 3 (by rfl) ⟨1222394, by rfl⟩ : syracuseStep 6519437 = 2444789) B2444789
theorem B4346291 : Blo 2287435 4346291 := bstep (se 1 (by rfl) ⟨3259718, by rfl⟩ : syracuseStep 4346291 = 6519437) B6519437
theorem B2897527 : Blo 2287435 2897527 := bstep (se 1 (by rfl) ⟨2173145, by rfl⟩ : syracuseStep 2897527 = 4346291) B4346291
theorem B3863369 : Blo 2287435 3863369 := bstep (se 2 (by rfl) ⟨1448763, by rfl⟩ : syracuseStep 3863369 = 2897527) B2897527
theorem B2575579 : Blo 2287435 2575579 := bstep (se 1 (by rfl) ⟨1931684, by rfl⟩ : syracuseStep 2575579 = 3863369) B3863369
theorem B3434105 : Blo 2287435 3434105 := bstep (se 2 (by rfl) ⟨1287789, by rfl⟩ : syracuseStep 3434105 = 2575579) B2575579
theorem B2289403 : Blo 2287435 2289403 := bstep (se 1 (by rfl) ⟨1717052, by rfl⟩ : syracuseStep 2289403 = 3434105) B3434105
theorem B5292685 : Blo 2287435 5292685 := bbase (se 3 (by rfl) ⟨992378, by rfl⟩ : syracuseStep 5292685 = 1984757) (by norm_num)
theorem B28227653 : Blo 2287435 28227653 := bstep (se 4 (by rfl) ⟨2646342, by rfl⟩ : syracuseStep 28227653 = 5292685) B5292685
theorem B18818435 : Blo 2287435 18818435 := bstep (se 1 (by rfl) ⟨14113826, by rfl⟩ : syracuseStep 18818435 = 28227653) B28227653
theorem B12545623 : Blo 2287435 12545623 := bstep (se 1 (by rfl) ⟨9409217, by rfl⟩ : syracuseStep 12545623 = 18818435) B18818435
theorem B66909989 : Blo 2287435 66909989 := bstep (se 4 (by rfl) ⟨6272811, by rfl⟩ : syracuseStep 66909989 = 12545623) B12545623
theorem B178426637 : Blo 2287435 178426637 := bstep (se 3 (by rfl) ⟨33454994, by rfl⟩ : syracuseStep 178426637 = 66909989) B66909989
theorem B118951091 : Blo 2287435 118951091 := bstep (se 1 (by rfl) ⟨89213318, by rfl⟩ : syracuseStep 118951091 = 178426637) B178426637
theorem B79300727 : Blo 2287435 79300727 := bstep (se 1 (by rfl) ⟨59475545, by rfl⟩ : syracuseStep 79300727 = 118951091) B118951091
theorem B52867151 : Blo 2287435 52867151 := bstep (se 1 (by rfl) ⟨39650363, by rfl⟩ : syracuseStep 52867151 = 79300727) B79300727
theorem B35244767 : Blo 2287435 35244767 := bstep (se 1 (by rfl) ⟨26433575, by rfl⟩ : syracuseStep 35244767 = 52867151) B52867151
theorem B93986045 : Blo 2287435 93986045 := bstep (se 3 (by rfl) ⟨17622383, by rfl⟩ : syracuseStep 93986045 = 35244767) B35244767
theorem B62657363 : Blo 2287435 62657363 := bstep (se 1 (by rfl) ⟨46993022, by rfl⟩ : syracuseStep 62657363 = 93986045) B93986045
theorem B41771575 : Blo 2287435 41771575 := bstep (se 1 (by rfl) ⟨31328681, by rfl⟩ : syracuseStep 41771575 = 62657363) B62657363
theorem B55695433 : Blo 2287435 55695433 := bstep (se 2 (by rfl) ⟨20885787, by rfl⟩ : syracuseStep 55695433 = 41771575) B41771575
theorem B74260577 : Blo 2287435 74260577 := bstep (se 2 (by rfl) ⟨27847716, by rfl⟩ : syracuseStep 74260577 = 55695433) B55695433
theorem B49507051 : Blo 2287435 49507051 := bstep (se 1 (by rfl) ⟨37130288, by rfl⟩ : syracuseStep 49507051 = 74260577) B74260577
theorem B66009401 : Blo 2287435 66009401 := bstep (se 2 (by rfl) ⟨24753525, by rfl⟩ : syracuseStep 66009401 = 49507051) B49507051
theorem B44006267 : Blo 2287435 44006267 := bstep (se 1 (by rfl) ⟨33004700, by rfl⟩ : syracuseStep 44006267 = 66009401) B66009401
theorem B29337511 : Blo 2287435 29337511 := bstep (se 1 (by rfl) ⟨22003133, by rfl⟩ : syracuseStep 29337511 = 44006267) B44006267
theorem B39116681 : Blo 2287435 39116681 := bstep (se 2 (by rfl) ⟨14668755, by rfl⟩ : syracuseStep 39116681 = 29337511) B29337511
theorem B26077787 : Blo 2287435 26077787 := bstep (se 1 (by rfl) ⟨19558340, by rfl⟩ : syracuseStep 26077787 = 39116681) B39116681
theorem B17385191 : Blo 2287435 17385191 := bstep (se 1 (by rfl) ⟨13038893, by rfl⟩ : syracuseStep 17385191 = 26077787) B26077787
theorem B11590127 : Blo 2287435 11590127 := bstep (se 1 (by rfl) ⟨8692595, by rfl⟩ : syracuseStep 11590127 = 17385191) B17385191
theorem B7726751 : Blo 2287435 7726751 := bstep (se 1 (by rfl) ⟨5795063, by rfl⟩ : syracuseStep 7726751 = 11590127) B11590127
theorem B5151167 : Blo 2287435 5151167 := bstep (se 1 (by rfl) ⟨3863375, by rfl⟩ : syracuseStep 5151167 = 7726751) B7726751
theorem B3434111 : Blo 2287435 3434111 := bstep (se 1 (by rfl) ⟨2575583, by rfl⟩ : syracuseStep 3434111 = 5151167) B5151167
theorem B2289407 : Blo 2287435 2289407 := bstep (se 1 (by rfl) ⟨1717055, by rfl⟩ : syracuseStep 2289407 = 3434111) B3434111
theorem B3434117 : Blo 2287435 3434117 := bbase (se 4 (by rfl) ⟨321948, by rfl⟩ : syracuseStep 3434117 = 643897) (by norm_num)
theorem B2289411 : Blo 2287435 2289411 := bstep (se 1 (by rfl) ⟨1717058, by rfl⟩ : syracuseStep 2289411 = 3434117) B3434117
theorem B3863389 : Blo 2287435 3863389 := bbase (se 3 (by rfl) ⟨724385, by rfl⟩ : syracuseStep 3863389 = 1448771) (by norm_num)
theorem B5151185 : Blo 2287435 5151185 := bstep (se 2 (by rfl) ⟨1931694, by rfl⟩ : syracuseStep 5151185 = 3863389) B3863389
theorem B3434123 : Blo 2287435 3434123 := bstep (se 1 (by rfl) ⟨2575592, by rfl⟩ : syracuseStep 3434123 = 5151185) B5151185
theorem B2289415 : Blo 2287435 2289415 := bstep (se 1 (by rfl) ⟨1717061, by rfl⟩ : syracuseStep 2289415 = 3434123) B3434123
theorem B2575597 : Blo 2287435 2575597 := bbase (se 3 (by rfl) ⟨482924, by rfl⟩ : syracuseStep 2575597 = 965849) (by norm_num)
theorem B3434129 : Blo 2287435 3434129 := bstep (se 2 (by rfl) ⟨1287798, by rfl⟩ : syracuseStep 3434129 = 2575597) B2575597
theorem B2289419 : Blo 2287435 2289419 := bstep (se 1 (by rfl) ⟨1717064, by rfl⟩ : syracuseStep 2289419 = 3434129) B3434129
theorem B7726805 : Blo 2287435 7726805 := bbase (se 7 (by rfl) ⟨90548, by rfl⟩ : syracuseStep 7726805 = 181097) (by norm_num)
theorem B5151203 : Blo 2287435 5151203 := bstep (se 1 (by rfl) ⟨3863402, by rfl⟩ : syracuseStep 5151203 = 7726805) B7726805
theorem B3434135 : Blo 2287435 3434135 := bstep (se 1 (by rfl) ⟨2575601, by rfl⟩ : syracuseStep 3434135 = 5151203) B5151203
theorem B2289423 : Blo 2287435 2289423 := bstep (se 1 (by rfl) ⟨1717067, by rfl⟩ : syracuseStep 2289423 = 3434135) B3434135
theorem B3434141 : Blo 2287435 3434141 := bbase (se 3 (by rfl) ⟨643901, by rfl⟩ : syracuseStep 3434141 = 1287803) (by norm_num)
theorem B2289427 : Blo 2287435 2289427 := bstep (se 1 (by rfl) ⟨1717070, by rfl⟩ : syracuseStep 2289427 = 3434141) B3434141
theorem B5151221 : Blo 2287435 5151221 := bbase (se 5 (by rfl) ⟨241463, by rfl⟩ : syracuseStep 5151221 = 482927) (by norm_num)
theorem B3434147 : Blo 2287435 3434147 := bstep (se 1 (by rfl) ⟨2575610, by rfl⟩ : syracuseStep 3434147 = 5151221) B5151221
theorem B2289431 : Blo 2287435 2289431 := bstep (se 1 (by rfl) ⟨1717073, by rfl⟩ : syracuseStep 2289431 = 3434147) B3434147
theorem B7153285 : Blo 2287435 7153285 := bbase (se 4 (by rfl) ⟨670620, by rfl⟩ : syracuseStep 7153285 = 1341241) (by norm_num)
theorem B9537713 : Blo 2287435 9537713 := bstep (se 2 (by rfl) ⟨3576642, by rfl⟩ : syracuseStep 9537713 = 7153285) B7153285
theorem B6358475 : Blo 2287435 6358475 := bstep (se 1 (by rfl) ⟨4768856, by rfl⟩ : syracuseStep 6358475 = 9537713) B9537713
theorem B4238983 : Blo 2287435 4238983 := bstep (se 1 (by rfl) ⟨3179237, by rfl⟩ : syracuseStep 4238983 = 6358475) B6358475
theorem B22607909 : Blo 2287435 22607909 := bstep (se 4 (by rfl) ⟨2119491, by rfl⟩ : syracuseStep 22607909 = 4238983) B4238983
theorem B15071939 : Blo 2287435 15071939 := bstep (se 1 (by rfl) ⟨11303954, by rfl⟩ : syracuseStep 15071939 = 22607909) B22607909
theorem B10047959 : Blo 2287435 10047959 := bstep (se 1 (by rfl) ⟨7535969, by rfl⟩ : syracuseStep 10047959 = 15071939) B15071939
theorem B6698639 : Blo 2287435 6698639 := bstep (se 1 (by rfl) ⟨5023979, by rfl⟩ : syracuseStep 6698639 = 10047959) B10047959
theorem B17863037 : Blo 2287435 17863037 := bstep (se 3 (by rfl) ⟨3349319, by rfl⟩ : syracuseStep 17863037 = 6698639) B6698639
theorem B11908691 : Blo 2287435 11908691 := bstep (se 1 (by rfl) ⟨8931518, by rfl⟩ : syracuseStep 11908691 = 17863037) B17863037
theorem B7939127 : Blo 2287435 7939127 := bstep (se 1 (by rfl) ⟨5954345, by rfl⟩ : syracuseStep 7939127 = 11908691) B11908691
theorem B5292751 : Blo 2287435 5292751 := bstep (se 1 (by rfl) ⟨3969563, by rfl⟩ : syracuseStep 5292751 = 7939127) B7939127
theorem B7057001 : Blo 2287435 7057001 := bstep (se 2 (by rfl) ⟨2646375, by rfl⟩ : syracuseStep 7057001 = 5292751) B5292751
theorem B18818669 : Blo 2287435 18818669 := bstep (se 3 (by rfl) ⟨3528500, by rfl⟩ : syracuseStep 18818669 = 7057001) B7057001
theorem B50183117 : Blo 2287435 50183117 := bstep (se 3 (by rfl) ⟨9409334, by rfl⟩ : syracuseStep 50183117 = 18818669) B18818669
theorem B33455411 : Blo 2287435 33455411 := bstep (se 1 (by rfl) ⟨25091558, by rfl⟩ : syracuseStep 33455411 = 50183117) B50183117
theorem B22303607 : Blo 2287435 22303607 := bstep (se 1 (by rfl) ⟨16727705, by rfl⟩ : syracuseStep 22303607 = 33455411) B33455411
theorem B59476285 : Blo 2287435 59476285 := bstep (se 3 (by rfl) ⟨11151803, by rfl⟩ : syracuseStep 59476285 = 22303607) B22303607
theorem B317206853 : Blo 2287435 317206853 := bstep (se 4 (by rfl) ⟨29738142, by rfl⟩ : syracuseStep 317206853 = 59476285) B59476285
theorem B211471235 : Blo 2287435 211471235 := bstep (se 1 (by rfl) ⟨158603426, by rfl⟩ : syracuseStep 211471235 = 317206853) B317206853
theorem B140980823 : Blo 2287435 140980823 := bstep (se 1 (by rfl) ⟨105735617, by rfl⟩ : syracuseStep 140980823 = 211471235) B211471235
theorem B93987215 : Blo 2287435 93987215 := bstep (se 1 (by rfl) ⟨70490411, by rfl⟩ : syracuseStep 93987215 = 140980823) B140980823
theorem B62658143 : Blo 2287435 62658143 := bstep (se 1 (by rfl) ⟨46993607, by rfl⟩ : syracuseStep 62658143 = 93987215) B93987215
theorem B41772095 : Blo 2287435 41772095 := bstep (se 1 (by rfl) ⟨31329071, by rfl⟩ : syracuseStep 41772095 = 62658143) B62658143
theorem B27848063 : Blo 2287435 27848063 := bstep (se 1 (by rfl) ⟨20886047, by rfl⟩ : syracuseStep 27848063 = 41772095) B41772095
theorem B18565375 : Blo 2287435 18565375 := bstep (se 1 (by rfl) ⟨13924031, by rfl⟩ : syracuseStep 18565375 = 27848063) B27848063
theorem B24753833 : Blo 2287435 24753833 := bstep (se 2 (by rfl) ⟨9282687, by rfl⟩ : syracuseStep 24753833 = 18565375) B18565375
theorem B16502555 : Blo 2287435 16502555 := bstep (se 1 (by rfl) ⟨12376916, by rfl⟩ : syracuseStep 16502555 = 24753833) B24753833
theorem B44006813 : Blo 2287435 44006813 := bstep (se 3 (by rfl) ⟨8251277, by rfl⟩ : syracuseStep 44006813 = 16502555) B16502555
theorem B29337875 : Blo 2287435 29337875 := bstep (se 1 (by rfl) ⟨22003406, by rfl⟩ : syracuseStep 29337875 = 44006813) B44006813
theorem B19558583 : Blo 2287435 19558583 := bstep (se 1 (by rfl) ⟨14668937, by rfl⟩ : syracuseStep 19558583 = 29337875) B29337875
theorem B13039055 : Blo 2287435 13039055 := bstep (se 1 (by rfl) ⟨9779291, by rfl⟩ : syracuseStep 13039055 = 19558583) B19558583
theorem B8692703 : Blo 2287435 8692703 := bstep (se 1 (by rfl) ⟨6519527, by rfl⟩ : syracuseStep 8692703 = 13039055) B13039055
theorem B5795135 : Blo 2287435 5795135 := bstep (se 1 (by rfl) ⟨4346351, by rfl⟩ : syracuseStep 5795135 = 8692703) B8692703
theorem B3863423 : Blo 2287435 3863423 := bstep (se 1 (by rfl) ⟨2897567, by rfl⟩ : syracuseStep 3863423 = 5795135) B5795135
theorem B2575615 : Blo 2287435 2575615 := bstep (se 1 (by rfl) ⟨1931711, by rfl⟩ : syracuseStep 2575615 = 3863423) B3863423
theorem B3434153 : Blo 2287435 3434153 := bstep (se 2 (by rfl) ⟨1287807, by rfl⟩ : syracuseStep 3434153 = 2575615) B2575615
theorem B2289435 : Blo 2287435 2289435 := bstep (se 1 (by rfl) ⟨1717076, by rfl⟩ : syracuseStep 2289435 = 3434153) B3434153
theorem C0 (j : ℕ) (h1 : 571858 ≤ j) (h2 : j ≤ 572358) : Blo 2287435 (4 * j + 3) := by
  interval_cases j
  · exact B2287435
  · exact B2287439
  · exact B2287443
  · exact B2287447
  · exact B2287451
  · exact B2287455
  · exact B2287459
  · exact B2287463
  · exact B2287467
  · exact B2287471
  · exact B2287475
  · exact B2287479
  · exact B2287483
  · exact B2287487
  · exact B2287491
  · exact B2287495
  · exact B2287499
  · exact B2287503
  · exact B2287507
  · exact B2287511
  · exact B2287515
  · exact B2287519
  · exact B2287523
  · exact B2287527
  · exact B2287531
  · exact B2287535
  · exact B2287539
  · exact B2287543
  · exact B2287547
  · exact B2287551
  · exact B2287555
  · exact B2287559
  · exact B2287563
  · exact B2287567
  · exact B2287571
  · exact B2287575
  · exact B2287579
  · exact B2287583
  · exact B2287587
  · exact B2287591
  · exact B2287595
  · exact B2287599
  · exact B2287603
  · exact B2287607
  · exact B2287611
  · exact B2287615
  · exact B2287619
  · exact B2287623
  · exact B2287627
  · exact B2287631
  · exact B2287635
  · exact B2287639
  · exact B2287643
  · exact B2287647
  · exact B2287651
  · exact B2287655
  · exact B2287659
  · exact B2287663
  · exact B2287667
  · exact B2287671
  · exact B2287675
  · exact B2287679
  · exact B2287683
  · exact B2287687
  · exact B2287691
  · exact B2287695
  · exact B2287699
  · exact B2287703
  · exact B2287707
  · exact B2287711
  · exact B2287715
  · exact B2287719
  · exact B2287723
  · exact B2287727
  · exact B2287731
  · exact B2287735
  · exact B2287739
  · exact B2287743
  · exact B2287747
  · exact B2287751
  · exact B2287755
  · exact B2287759
  · exact B2287763
  · exact B2287767
  · exact B2287771
  · exact B2287775
  · exact B2287779
  · exact B2287783
  · exact B2287787
  · exact B2287791
  · exact B2287795
  · exact B2287799
  · exact B2287803
  · exact B2287807
  · exact B2287811
  · exact B2287815
  · exact B2287819
  · exact B2287823
  · exact B2287827
  · exact B2287831
  · exact B2287835
  · exact B2287839
  · exact B2287843
  · exact B2287847
  · exact B2287851
  · exact B2287855
  · exact B2287859
  · exact B2287863
  · exact B2287867
  · exact B2287871
  · exact B2287875
  · exact B2287879
  · exact B2287883
  · exact B2287887
  · exact B2287891
  · exact B2287895
  · exact B2287899
  · exact B2287903
  · exact B2287907
  · exact B2287911
  · exact B2287915
  · exact B2287919
  · exact B2287923
  · exact B2287927
  · exact B2287931
  · exact B2287935
  · exact B2287939
  · exact B2287943
  · exact B2287947
  · exact B2287951
  · exact B2287955
  · exact B2287959
  · exact B2287963
  · exact B2287967
  · exact B2287971
  · exact B2287975
  · exact B2287979
  · exact B2287983
  · exact B2287987
  · exact B2287991
  · exact B2287995
  · exact B2287999
  · exact B2288003
  · exact B2288007
  · exact B2288011
  · exact B2288015
  · exact B2288019
  · exact B2288023
  · exact B2288027
  · exact B2288031
  · exact B2288035
  · exact B2288039
  · exact B2288043
  · exact B2288047
  · exact B2288051
  · exact B2288055
  · exact B2288059
  · exact B2288063
  · exact B2288067
  · exact B2288071
  · exact B2288075
  · exact B2288079
  · exact B2288083
  · exact B2288087
  · exact B2288091
  · exact B2288095
  · exact B2288099
  · exact B2288103
  · exact B2288107
  · exact B2288111
  · exact B2288115
  · exact B2288119
  · exact B2288123
  · exact B2288127
  · exact B2288131
  · exact B2288135
  · exact B2288139
  · exact B2288143
  · exact B2288147
  · exact B2288151
  · exact B2288155
  · exact B2288159
  · exact B2288163
  · exact B2288167
  · exact B2288171
  · exact B2288175
  · exact B2288179
  · exact B2288183
  · exact B2288187
  · exact B2288191
  · exact B2288195
  · exact B2288199
  · exact B2288203
  · exact B2288207
  · exact B2288211
  · exact B2288215
  · exact B2288219
  · exact B2288223
  · exact B2288227
  · exact B2288231
  · exact B2288235
  · exact B2288239
  · exact B2288243
  · exact B2288247
  · exact B2288251
  · exact B2288255
  · exact B2288259
  · exact B2288263
  · exact B2288267
  · exact B2288271
  · exact B2288275
  · exact B2288279
  · exact B2288283
  · exact B2288287
  · exact B2288291
  · exact B2288295
  · exact B2288299
  · exact B2288303
  · exact B2288307
  · exact B2288311
  · exact B2288315
  · exact B2288319
  · exact B2288323
  · exact B2288327
  · exact B2288331
  · exact B2288335
  · exact B2288339
  · exact B2288343
  · exact B2288347
  · exact B2288351
  · exact B2288355
  · exact B2288359
  · exact B2288363
  · exact B2288367
  · exact B2288371
  · exact B2288375
  · exact B2288379
  · exact B2288383
  · exact B2288387
  · exact B2288391
  · exact B2288395
  · exact B2288399
  · exact B2288403
  · exact B2288407
  · exact B2288411
  · exact B2288415
  · exact B2288419
  · exact B2288423
  · exact B2288427
  · exact B2288431
  · exact B2288435
  · exact B2288439
  · exact B2288443
  · exact B2288447
  · exact B2288451
  · exact B2288455
  · exact B2288459
  · exact B2288463
  · exact B2288467
  · exact B2288471
  · exact B2288475
  · exact B2288479
  · exact B2288483
  · exact B2288487
  · exact B2288491
  · exact B2288495
  · exact B2288499
  · exact B2288503
  · exact B2288507
  · exact B2288511
  · exact B2288515
  · exact B2288519
  · exact B2288523
  · exact B2288527
  · exact B2288531
  · exact B2288535
  · exact B2288539
  · exact B2288543
  · exact B2288547
  · exact B2288551
  · exact B2288555
  · exact B2288559
  · exact B2288563
  · exact B2288567
  · exact B2288571
  · exact B2288575
  · exact B2288579
  · exact B2288583
  · exact B2288587
  · exact B2288591
  · exact B2288595
  · exact B2288599
  · exact B2288603
  · exact B2288607
  · exact B2288611
  · exact B2288615
  · exact B2288619
  · exact B2288623
  · exact B2288627
  · exact B2288631
  · exact B2288635
  · exact B2288639
  · exact B2288643
  · exact B2288647
  · exact B2288651
  · exact B2288655
  · exact B2288659
  · exact B2288663
  · exact B2288667
  · exact B2288671
  · exact B2288675
  · exact B2288679
  · exact B2288683
  · exact B2288687
  · exact B2288691
  · exact B2288695
  · exact B2288699
  · exact B2288703
  · exact B2288707
  · exact B2288711
  · exact B2288715
  · exact B2288719
  · exact B2288723
  · exact B2288727
  · exact B2288731
  · exact B2288735
  · exact B2288739
  · exact B2288743
  · exact B2288747
  · exact B2288751
  · exact B2288755
  · exact B2288759
  · exact B2288763
  · exact B2288767
  · exact B2288771
  · exact B2288775
  · exact B2288779
  · exact B2288783
  · exact B2288787
  · exact B2288791
  · exact B2288795
  · exact B2288799
  · exact B2288803
  · exact B2288807
  · exact B2288811
  · exact B2288815
  · exact B2288819
  · exact B2288823
  · exact B2288827
  · exact B2288831
  · exact B2288835
  · exact B2288839
  · exact B2288843
  · exact B2288847
  · exact B2288851
  · exact B2288855
  · exact B2288859
  · exact B2288863
  · exact B2288867
  · exact B2288871
  · exact B2288875
  · exact B2288879
  · exact B2288883
  · exact B2288887
  · exact B2288891
  · exact B2288895
  · exact B2288899
  · exact B2288903
  · exact B2288907
  · exact B2288911
  · exact B2288915
  · exact B2288919
  · exact B2288923
  · exact B2288927
  · exact B2288931
  · exact B2288935
  · exact B2288939
  · exact B2288943
  · exact B2288947
  · exact B2288951
  · exact B2288955
  · exact B2288959
  · exact B2288963
  · exact B2288967
  · exact B2288971
  · exact B2288975
  · exact B2288979
  · exact B2288983
  · exact B2288987
  · exact B2288991
  · exact B2288995
  · exact B2288999
  · exact B2289003
  · exact B2289007
  · exact B2289011
  · exact B2289015
  · exact B2289019
  · exact B2289023
  · exact B2289027
  · exact B2289031
  · exact B2289035
  · exact B2289039
  · exact B2289043
  · exact B2289047
  · exact B2289051
  · exact B2289055
  · exact B2289059
  · exact B2289063
  · exact B2289067
  · exact B2289071
  · exact B2289075
  · exact B2289079
  · exact B2289083
  · exact B2289087
  · exact B2289091
  · exact B2289095
  · exact B2289099
  · exact B2289103
  · exact B2289107
  · exact B2289111
  · exact B2289115
  · exact B2289119
  · exact B2289123
  · exact B2289127
  · exact B2289131
  · exact B2289135
  · exact B2289139
  · exact B2289143
  · exact B2289147
  · exact B2289151
  · exact B2289155
  · exact B2289159
  · exact B2289163
  · exact B2289167
  · exact B2289171
  · exact B2289175
  · exact B2289179
  · exact B2289183
  · exact B2289187
  · exact B2289191
  · exact B2289195
  · exact B2289199
  · exact B2289203
  · exact B2289207
  · exact B2289211
  · exact B2289215
  · exact B2289219
  · exact B2289223
  · exact B2289227
  · exact B2289231
  · exact B2289235
  · exact B2289239
  · exact B2289243
  · exact B2289247
  · exact B2289251
  · exact B2289255
  · exact B2289259
  · exact B2289263
  · exact B2289267
  · exact B2289271
  · exact B2289275
  · exact B2289279
  · exact B2289283
  · exact B2289287
  · exact B2289291
  · exact B2289295
  · exact B2289299
  · exact B2289303
  · exact B2289307
  · exact B2289311
  · exact B2289315
  · exact B2289319
  · exact B2289323
  · exact B2289327
  · exact B2289331
  · exact B2289335
  · exact B2289339
  · exact B2289343
  · exact B2289347
  · exact B2289351
  · exact B2289355
  · exact B2289359
  · exact B2289363
  · exact B2289367
  · exact B2289371
  · exact B2289375
  · exact B2289379
  · exact B2289383
  · exact B2289387
  · exact B2289391
  · exact B2289395
  · exact B2289399
  · exact B2289403
  · exact B2289407
  · exact B2289411
  · exact B2289415
  · exact B2289419
  · exact B2289423
  · exact B2289427
  · exact B2289431
  · exact B2289435
theorem solution (m : ℕ) (hlo : 2287435 ≤ m) (hhi : m ≤ 2289435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 571858 ≤ j := by omega
    have hj2 : j ≤ 572358 := by omega
    have hb : Blo 2287435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
