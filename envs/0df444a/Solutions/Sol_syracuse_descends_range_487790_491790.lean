-- Prove2me | solution 1 for syracuse_descends_range_487790_491790
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:08.420901+00:00
-- url     : https://prove2.me/submissions/8a5d7da5-6427-4bfd-b069-45b4fc3070c9

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


theorem B589837 : Blo 487790 589837 := bbase (se 3 (by rfl) ⟨110594, by rfl⟩ : syracuseStep 589837 = 221189) (by norm_num)
theorem B1572949 : Blo 487790 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B1409125 : Blo 487790 1409125 := bbase (se 4 (by rfl) ⟨132105, by rfl⟩ : syracuseStep 1409125 = 264211) (by norm_num)
theorem B589933 : Blo 487790 589933 := bbase (se 3 (by rfl) ⟨110612, by rfl⟩ : syracuseStep 589933 = 221225) (by norm_num)
theorem B524453 : Blo 487790 524453 := bbase (se 4 (by rfl) ⟨49167, by rfl⟩ : syracuseStep 524453 = 98335) (by norm_num)
theorem B524513 : Blo 487790 524513 := bbase (se 2 (by rfl) ⟨196692, by rfl⟩ : syracuseStep 524513 = 393385) (by norm_num)
theorem B2359637 : Blo 487790 2359637 := bbase (se 10 (by rfl) ⟨3456, by rfl⟩ : syracuseStep 2359637 = 6913) (by norm_num)
theorem B524641 : Blo 487790 524641 := bbase (se 2 (by rfl) ⟨196740, by rfl⟩ : syracuseStep 524641 = 393481) (by norm_num)
theorem B885101 : Blo 487790 885101 := bbase (se 3 (by rfl) ⟨165956, by rfl⟩ : syracuseStep 885101 = 331913) (by norm_num)
theorem B10584533 : Blo 487790 10584533 := bbase (se 7 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 10584533 = 248075) (by norm_num)
theorem B885269 : Blo 487790 885269 := bbase (se 6 (by rfl) ⟨20748, by rfl⟩ : syracuseStep 885269 = 41497) (by norm_num)
theorem B787013 : Blo 487790 787013 := bbase (se 4 (by rfl) ⟨73782, by rfl⟩ : syracuseStep 787013 = 147565) (by norm_num)
theorem B557641 : Blo 487790 557641 := bbase (se 2 (by rfl) ⟨209115, by rfl⟩ : syracuseStep 557641 = 418231) (by norm_num)
theorem B2425589 : Blo 487790 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B7144213 : Blo 487790 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B525085 : Blo 487790 525085 := bbase (se 3 (by rfl) ⟨98453, by rfl⟩ : syracuseStep 525085 = 196907) (by norm_num)
theorem B1049453 : Blo 487790 1049453 := bbase (se 3 (by rfl) ⟨196772, by rfl⟩ : syracuseStep 1049453 = 393545) (by norm_num)
theorem B1049573 : Blo 487790 1049573 := bbase (se 4 (by rfl) ⟨98397, by rfl⟩ : syracuseStep 1049573 = 196795) (by norm_num)
theorem B787525 : Blo 487790 787525 := bbase (se 4 (by rfl) ⟨73830, by rfl⟩ : syracuseStep 787525 = 147661) (by norm_num)
theorem B1115245 : Blo 487790 1115245 := bbase (se 3 (by rfl) ⟨209108, by rfl⟩ : syracuseStep 1115245 = 418217) (by norm_num)
theorem B2098325 : Blo 487790 2098325 := bbase (se 6 (by rfl) ⟨49179, by rfl⟩ : syracuseStep 2098325 = 98359) (by norm_num)
theorem B558289 : Blo 487790 558289 := bbase (se 2 (by rfl) ⟨209358, by rfl⟩ : syracuseStep 558289 = 418717) (by norm_num)
theorem B1574117 : Blo 487790 1574117 := bbase (se 4 (by rfl) ⟨147573, by rfl⟩ : syracuseStep 1574117 = 295147) (by norm_num)
theorem B918821 : Blo 487790 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B1180973 : Blo 487790 1180973 := bbase (se 3 (by rfl) ⟨221432, by rfl⟩ : syracuseStep 1180973 = 442865) (by norm_num)
theorem B1050205 : Blo 487790 1050205 := bbase (se 3 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 1050205 = 393827) (by norm_num)
theorem B1181357 : Blo 487790 1181357 := bbase (se 3 (by rfl) ⟨221504, by rfl⟩ : syracuseStep 1181357 = 443009) (by norm_num)
theorem B558881 : Blo 487790 558881 := bbase (se 2 (by rfl) ⟨209580, by rfl⟩ : syracuseStep 558881 = 419161) (by norm_num)
theorem B952141 : Blo 487790 952141 := bbase (se 3 (by rfl) ⟨178526, by rfl⟩ : syracuseStep 952141 = 357053) (by norm_num)
theorem B1181557 : Blo 487790 1181557 := bbase (se 5 (by rfl) ⟨55385, by rfl⟩ : syracuseStep 1181557 = 110771) (by norm_num)
theorem B559045 : Blo 487790 559045 := bbase (se 4 (by rfl) ⟨52410, by rfl⟩ : syracuseStep 559045 = 104821) (by norm_num)
theorem B1771573 : Blo 487790 1771573 := bbase (se 5 (by rfl) ⟨83042, by rfl⟩ : syracuseStep 1771573 = 166085) (by norm_num)
theorem B1411253 : Blo 487790 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B1771733 : Blo 487790 1771733 := bbase (se 7 (by rfl) ⟨20762, by rfl⟩ : syracuseStep 1771733 = 41525) (by norm_num)
theorem B1116413 : Blo 487790 1116413 := bbase (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) (by norm_num)
theorem B2787605 : Blo 487790 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B2361653 : Blo 487790 2361653 := bbase (se 5 (by rfl) ⟨110702, by rfl⟩ : syracuseStep 2361653 = 221405) (by norm_num)
theorem B559921 : Blo 487790 559921 := bbase (se 2 (by rfl) ⟨209970, by rfl⟩ : syracuseStep 559921 = 419941) (by norm_num)
theorem B3705749 : Blo 487790 3705749 := bbase (se 6 (by rfl) ⟨86853, by rfl⟩ : syracuseStep 3705749 = 173707) (by norm_num)
theorem B2362405 : Blo 487790 2362405 := bbase (se 4 (by rfl) ⟨221475, by rfl⟩ : syracuseStep 2362405 = 442951) (by norm_num)
theorem B756797 : Blo 487790 756797 := bbase (se 3 (by rfl) ⟨141899, by rfl⟩ : syracuseStep 756797 = 283799) (by norm_num)
theorem B2788789 : Blo 487790 2788789 := bbase (se 5 (by rfl) ⟨130724, by rfl⟩ : syracuseStep 2788789 = 261449) (by norm_num)
theorem B495145 : Blo 487790 495145 := bbase (se 2 (by rfl) ⟨185679, by rfl⟩ : syracuseStep 495145 = 371359) (by norm_num)
theorem B15109973 : Blo 487790 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B823189 : Blo 487790 823189 := bbase (se 6 (by rfl) ⟨19293, by rfl⟩ : syracuseStep 823189 = 38587) (by norm_num)
theorem B823277 : Blo 487790 823277 := bbase (se 3 (by rfl) ⟨154364, by rfl⟩ : syracuseStep 823277 = 308729) (by norm_num)
theorem B823405 : Blo 487790 823405 := bbase (se 3 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 823405 = 308777) (by norm_num)
theorem B495761 : Blo 487790 495761 := bbase (se 2 (by rfl) ⟨185910, by rfl⟩ : syracuseStep 495761 = 371821) (by norm_num)
theorem B823493 : Blo 487790 823493 := bbase (se 4 (by rfl) ⟨77202, by rfl⟩ : syracuseStep 823493 = 154405) (by norm_num)
theorem B659669 : Blo 487790 659669 := bbase (se 7 (by rfl) ⟨7730, by rfl⟩ : syracuseStep 659669 = 15461) (by norm_num)
theorem B823621 : Blo 487790 823621 := bbase (se 4 (by rfl) ⟨77214, by rfl⟩ : syracuseStep 823621 = 154429) (by norm_num)
theorem B823709 : Blo 487790 823709 := bbase (se 3 (by rfl) ⟨154445, by rfl⟩ : syracuseStep 823709 = 308891) (by norm_num)
theorem B823837 : Blo 487790 823837 := bbase (se 3 (by rfl) ⟨154469, by rfl⟩ : syracuseStep 823837 = 308939) (by norm_num)
theorem B823925 : Blo 487790 823925 := bbase (se 5 (by rfl) ⟨38621, by rfl⟩ : syracuseStep 823925 = 77243) (by norm_num)
theorem B5083829 : Blo 487790 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B824053 : Blo 487790 824053 := bbase (se 5 (by rfl) ⟨38627, by rfl⟩ : syracuseStep 824053 = 77255) (by norm_num)
theorem B824141 : Blo 487790 824141 := bbase (se 3 (by rfl) ⟨154526, by rfl⟩ : syracuseStep 824141 = 309053) (by norm_num)
theorem B529237 : Blo 487790 529237 := bbase (se 9 (by rfl) ⟨1550, by rfl⟩ : syracuseStep 529237 = 3101) (by norm_num)
theorem B824269 : Blo 487790 824269 := bbase (se 3 (by rfl) ⟨154550, by rfl⟩ : syracuseStep 824269 = 309101) (by norm_num)
theorem B496669 : Blo 487790 496669 := bbase (se 3 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 496669 = 186251) (by norm_num)
theorem B824357 : Blo 487790 824357 := bbase (se 4 (by rfl) ⟨77283, by rfl⟩ : syracuseStep 824357 = 154567) (by norm_num)
theorem B824485 : Blo 487790 824485 := bbase (se 4 (by rfl) ⟨77295, by rfl⟩ : syracuseStep 824485 = 154591) (by norm_num)
theorem B824573 : Blo 487790 824573 := bbase (se 3 (by rfl) ⟨154607, by rfl⟩ : syracuseStep 824573 = 309215) (by norm_num)
theorem B628085 : Blo 487790 628085 := bbase (se 5 (by rfl) ⟨29441, by rfl⟩ : syracuseStep 628085 = 58883) (by norm_num)
theorem B2790773 : Blo 487790 2790773 := bbase (se 5 (by rfl) ⟨130817, by rfl⟩ : syracuseStep 2790773 = 261635) (by norm_num)
theorem B824701 : Blo 487790 824701 := bbase (se 3 (by rfl) ⟨154631, by rfl⟩ : syracuseStep 824701 = 309263) (by norm_num)
theorem B628105 : Blo 487790 628105 := bbase (se 2 (by rfl) ⟨235539, by rfl⟩ : syracuseStep 628105 = 471079) (by norm_num)
theorem B824789 : Blo 487790 824789 := bbase (se 7 (by rfl) ⟨9665, by rfl⟩ : syracuseStep 824789 = 19331) (by norm_num)
theorem B1676837 : Blo 487790 1676837 := bbase (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) (by norm_num)
theorem B824917 : Blo 487790 824917 := bbase (se 8 (by rfl) ⟨4833, by rfl⟩ : syracuseStep 824917 = 9667) (by norm_num)
theorem B825005 : Blo 487790 825005 := bbase (se 3 (by rfl) ⟨154688, by rfl⟩ : syracuseStep 825005 = 309377) (by norm_num)
theorem B595741 : Blo 487790 595741 := bbase (se 3 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 595741 = 223403) (by norm_num)
theorem B825133 : Blo 487790 825133 := bbase (se 3 (by rfl) ⟨154712, by rfl⟩ : syracuseStep 825133 = 309425) (by norm_num)
theorem B1677125 : Blo 487790 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B497513 : Blo 487790 497513 := bbase (se 2 (by rfl) ⟨186567, by rfl⟩ : syracuseStep 497513 = 373135) (by norm_num)
theorem B825221 : Blo 487790 825221 := bbase (se 4 (by rfl) ⟨77364, by rfl⟩ : syracuseStep 825221 = 154729) (by norm_num)
theorem B1120133 : Blo 487790 1120133 := bbase (se 4 (by rfl) ⟨105012, by rfl⟩ : syracuseStep 1120133 = 210025) (by norm_num)
theorem B825349 : Blo 487790 825349 := bbase (se 4 (by rfl) ⟨77376, by rfl⟩ : syracuseStep 825349 = 154753) (by norm_num)
theorem B825437 : Blo 487790 825437 := bbase (se 3 (by rfl) ⟨154769, by rfl⟩ : syracuseStep 825437 = 309539) (by norm_num)
theorem B661621 : Blo 487790 661621 := bbase (se 5 (by rfl) ⟨31013, by rfl⟩ : syracuseStep 661621 = 62027) (by norm_num)
theorem B825565 : Blo 487790 825565 := bbase (se 3 (by rfl) ⟨154793, by rfl⟩ : syracuseStep 825565 = 309587) (by norm_num)
theorem B2005301 : Blo 487790 2005301 := bbase (se 5 (by rfl) ⟨93998, by rfl⟩ : syracuseStep 2005301 = 187997) (by norm_num)
theorem B825653 : Blo 487790 825653 := bbase (se 5 (by rfl) ⟨38702, by rfl⟩ : syracuseStep 825653 = 77405) (by norm_num)
theorem B694669 : Blo 487790 694669 := bbase (se 3 (by rfl) ⟨130250, by rfl⟩ : syracuseStep 694669 = 260501) (by norm_num)
theorem B498097 : Blo 487790 498097 := bbase (se 2 (by rfl) ⟨186786, by rfl⟩ : syracuseStep 498097 = 373573) (by norm_num)
theorem B825781 : Blo 487790 825781 := bbase (se 5 (by rfl) ⟨38708, by rfl⟩ : syracuseStep 825781 = 77417) (by norm_num)
theorem B825869 : Blo 487790 825869 := bbase (se 3 (by rfl) ⟨154850, by rfl⟩ : syracuseStep 825869 = 309701) (by norm_num)
theorem B825997 : Blo 487790 825997 := bbase (se 3 (by rfl) ⟨154874, by rfl⟩ : syracuseStep 825997 = 309749) (by norm_num)
theorem B498397 : Blo 487790 498397 := bbase (se 3 (by rfl) ⟨93449, by rfl⟩ : syracuseStep 498397 = 186899) (by norm_num)
theorem B826085 : Blo 487790 826085 := bbase (se 4 (by rfl) ⟨77445, by rfl⟩ : syracuseStep 826085 = 154891) (by norm_num)
theorem B989965 : Blo 487790 989965 := bbase (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) (by norm_num)
theorem B826213 : Blo 487790 826213 := bbase (se 4 (by rfl) ⟨77457, by rfl⟩ : syracuseStep 826213 = 154915) (by norm_num)
theorem B662437 : Blo 487790 662437 := bbase (se 4 (by rfl) ⟨62103, by rfl⟩ : syracuseStep 662437 = 124207) (by norm_num)
theorem B826301 : Blo 487790 826301 := bbase (se 3 (by rfl) ⟨154931, by rfl⟩ : syracuseStep 826301 = 309863) (by norm_num)
theorem B695261 : Blo 487790 695261 := bbase (se 3 (by rfl) ⟨130361, by rfl⟩ : syracuseStep 695261 = 260723) (by norm_num)
theorem B695341 : Blo 487790 695341 := bbase (se 3 (by rfl) ⟨130376, by rfl⟩ : syracuseStep 695341 = 260753) (by norm_num)
theorem B826429 : Blo 487790 826429 := bbase (se 3 (by rfl) ⟨154955, by rfl⟩ : syracuseStep 826429 = 309911) (by norm_num)
theorem B564305 : Blo 487790 564305 := bbase (se 2 (by rfl) ⟨211614, by rfl⟩ : syracuseStep 564305 = 423229) (by norm_num)
theorem B826517 : Blo 487790 826517 := bbase (se 6 (by rfl) ⟨19371, by rfl⟩ : syracuseStep 826517 = 38743) (by norm_num)
theorem B695461 : Blo 487790 695461 := bbase (se 4 (by rfl) ⟨65199, by rfl⟩ : syracuseStep 695461 = 130399) (by norm_num)
theorem B695557 : Blo 487790 695557 := bbase (se 4 (by rfl) ⟨65208, by rfl⟩ : syracuseStep 695557 = 130417) (by norm_num)
theorem B826645 : Blo 487790 826645 := bbase (se 6 (by rfl) ⟨19374, by rfl⟩ : syracuseStep 826645 = 38749) (by norm_num)
theorem B826733 : Blo 487790 826733 := bbase (se 3 (by rfl) ⟨155012, by rfl⟩ : syracuseStep 826733 = 310025) (by norm_num)
theorem B663005 : Blo 487790 663005 := bbase (se 3 (by rfl) ⟨124313, by rfl⟩ : syracuseStep 663005 = 248627) (by norm_num)
theorem B826861 : Blo 487790 826861 := bbase (se 3 (by rfl) ⟨155036, by rfl⟩ : syracuseStep 826861 = 310073) (by norm_num)
theorem B2792981 : Blo 487790 2792981 := bbase (se 6 (by rfl) ⟨65460, by rfl⟩ : syracuseStep 2792981 = 130921) (by norm_num)
theorem B826949 : Blo 487790 826949 := bbase (se 4 (by rfl) ⟨77526, by rfl⟩ : syracuseStep 826949 = 155053) (by norm_num)
theorem B630373 : Blo 487790 630373 := bbase (se 4 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 630373 = 118195) (by norm_num)
theorem B958133 : Blo 487790 958133 := bbase (se 5 (by rfl) ⟨44912, by rfl⟩ : syracuseStep 958133 = 89825) (by norm_num)
theorem B827077 : Blo 487790 827077 := bbase (se 4 (by rfl) ⟨77538, by rfl⟩ : syracuseStep 827077 = 155077) (by norm_num)
theorem B696053 : Blo 487790 696053 := bbase (se 5 (by rfl) ⟨32627, by rfl⟩ : syracuseStep 696053 = 65255) (by norm_num)
theorem B4693781 : Blo 487790 4693781 := bbase (se 6 (by rfl) ⟨110010, by rfl⟩ : syracuseStep 4693781 = 220021) (by norm_num)
theorem B827165 : Blo 487790 827165 := bbase (se 3 (by rfl) ⟨155093, by rfl⟩ : syracuseStep 827165 = 310187) (by norm_num)
theorem B1646405 : Blo 487790 1646405 := bbase (se 4 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 1646405 = 308701) (by norm_num)
theorem B663437 : Blo 487790 663437 := bbase (se 3 (by rfl) ⟨124394, by rfl⟩ : syracuseStep 663437 = 248789) (by norm_num)
theorem B827293 : Blo 487790 827293 := bbase (se 3 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 827293 = 310235) (by norm_num)
theorem B16981973 : Blo 487790 16981973 := bbase (se 7 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 16981973 = 398015) (by norm_num)
theorem B827381 : Blo 487790 827381 := bbase (se 5 (by rfl) ⟨38783, by rfl⟩ : syracuseStep 827381 = 77567) (by norm_num)
theorem B16162901 : Blo 487790 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B827509 : Blo 487790 827509 := bbase (se 5 (by rfl) ⟨38789, by rfl⟩ : syracuseStep 827509 = 77579) (by norm_num)
theorem B827597 : Blo 487790 827597 := bbase (se 3 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 827597 = 310349) (by norm_num)
theorem B1646837 : Blo 487790 1646837 := bbase (se 5 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 1646837 = 154391) (by norm_num)
theorem B696605 : Blo 487790 696605 := bbase (se 3 (by rfl) ⟨130613, by rfl⟩ : syracuseStep 696605 = 261227) (by norm_num)
theorem B827725 : Blo 487790 827725 := bbase (se 3 (by rfl) ⟨155198, by rfl⟩ : syracuseStep 827725 = 310397) (by norm_num)
theorem B827813 : Blo 487790 827813 := bbase (se 4 (by rfl) ⟨77607, by rfl⟩ : syracuseStep 827813 = 155215) (by norm_num)
theorem B926149 : Blo 487790 926149 := bbase (se 4 (by rfl) ⟨86826, by rfl⟩ : syracuseStep 926149 = 173653) (by norm_num)
theorem B827941 : Blo 487790 827941 := bbase (se 4 (by rfl) ⟨77619, by rfl⟩ : syracuseStep 827941 = 155239) (by norm_num)
theorem B926309 : Blo 487790 926309 := bbase (se 4 (by rfl) ⟨86841, by rfl⟩ : syracuseStep 926309 = 173683) (by norm_num)
theorem B828029 : Blo 487790 828029 := bbase (se 3 (by rfl) ⟨155255, by rfl⟩ : syracuseStep 828029 = 310511) (by norm_num)
theorem B1647269 : Blo 487790 1647269 := bbase (se 4 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 1647269 = 308863) (by norm_num)
theorem B959197 : Blo 487790 959197 := bbase (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) (by norm_num)
theorem B926453 : Blo 487790 926453 := bbase (se 5 (by rfl) ⟨43427, by rfl⟩ : syracuseStep 926453 = 86855) (by norm_num)
theorem B828157 : Blo 487790 828157 := bbase (se 3 (by rfl) ⟨155279, by rfl⟩ : syracuseStep 828157 = 310559) (by norm_num)
theorem B828245 : Blo 487790 828245 := bbase (se 9 (by rfl) ⟨2426, by rfl⟩ : syracuseStep 828245 = 4853) (by norm_num)
theorem B828373 : Blo 487790 828373 := bbase (se 7 (by rfl) ⟨9707, by rfl⟩ : syracuseStep 828373 = 19415) (by norm_num)
theorem B697357 : Blo 487790 697357 := bbase (se 3 (by rfl) ⟨130754, by rfl⟩ : syracuseStep 697357 = 261509) (by norm_num)
theorem B926741 : Blo 487790 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B828461 : Blo 487790 828461 := bbase (se 3 (by rfl) ⟨155336, by rfl⟩ : syracuseStep 828461 = 310673) (by norm_num)
theorem B1647701 : Blo 487790 1647701 := bbase (se 8 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 1647701 = 19309) (by norm_num)
theorem B926893 : Blo 487790 926893 := bbase (se 3 (by rfl) ⟨173792, by rfl⟩ : syracuseStep 926893 = 347585) (by norm_num)
theorem B828589 : Blo 487790 828589 := bbase (se 3 (by rfl) ⟨155360, by rfl⟩ : syracuseStep 828589 = 310721) (by norm_num)
theorem B828677 : Blo 487790 828677 := bbase (se 4 (by rfl) ⟨77688, by rfl⟩ : syracuseStep 828677 = 155377) (by norm_num)
theorem B828805 : Blo 487790 828805 := bbase (se 4 (by rfl) ⟨77700, by rfl⟩ : syracuseStep 828805 = 155401) (by norm_num)
theorem B927197 : Blo 487790 927197 := bbase (se 3 (by rfl) ⟨173849, by rfl⟩ : syracuseStep 927197 = 347699) (by norm_num)
theorem B828893 : Blo 487790 828893 := bbase (se 3 (by rfl) ⟨155417, by rfl⟩ : syracuseStep 828893 = 310835) (by norm_num)
theorem B894461 : Blo 487790 894461 := bbase (se 3 (by rfl) ⟨167711, by rfl⟩ : syracuseStep 894461 = 335423) (by norm_num)
theorem B1648133 : Blo 487790 1648133 := bbase (se 4 (by rfl) ⟨154512, by rfl⟩ : syracuseStep 1648133 = 309025) (by norm_num)
theorem B1058333 : Blo 487790 1058333 := bbase (se 3 (by rfl) ⟨198437, by rfl⟩ : syracuseStep 1058333 = 396875) (by norm_num)
theorem B829021 : Blo 487790 829021 := bbase (se 3 (by rfl) ⟨155441, by rfl⟩ : syracuseStep 829021 = 310883) (by norm_num)
theorem B501373 : Blo 487790 501373 := bbase (se 3 (by rfl) ⟨94007, by rfl⟩ : syracuseStep 501373 = 188015) (by norm_num)
theorem B1320581 : Blo 487790 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B1255061 : Blo 487790 1255061 := bbase (se 6 (by rfl) ⟨29415, by rfl⟩ : syracuseStep 1255061 = 58831) (by norm_num)
theorem B829109 : Blo 487790 829109 := bbase (se 5 (by rfl) ⟨38864, by rfl⟩ : syracuseStep 829109 = 77729) (by norm_num)
theorem B698149 : Blo 487790 698149 := bbase (se 4 (by rfl) ⟨65451, by rfl⟩ : syracuseStep 698149 = 130903) (by norm_num)
theorem B829237 : Blo 487790 829237 := bbase (se 5 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 829237 = 77741) (by norm_num)
theorem B829325 : Blo 487790 829325 := bbase (se 3 (by rfl) ⟨155498, by rfl⟩ : syracuseStep 829325 = 310997) (by norm_num)
theorem B1288109 : Blo 487790 1288109 := bbase (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) (by norm_num)
theorem B1648565 : Blo 487790 1648565 := bbase (se 5 (by rfl) ⟨77276, by rfl⟩ : syracuseStep 1648565 = 154553) (by norm_num)
theorem B829453 : Blo 487790 829453 := bbase (se 3 (by rfl) ⟨155522, by rfl⟩ : syracuseStep 829453 = 311045) (by norm_num)
theorem B1255493 : Blo 487790 1255493 := bbase (se 4 (by rfl) ⟨117702, by rfl⟩ : syracuseStep 1255493 = 235405) (by norm_num)
theorem B829541 : Blo 487790 829541 := bbase (se 4 (by rfl) ⟨77769, by rfl⟩ : syracuseStep 829541 = 155539) (by norm_num)
theorem B698485 : Blo 487790 698485 := bbase (se 5 (by rfl) ⟨32741, by rfl⟩ : syracuseStep 698485 = 65483) (by norm_num)
theorem B927949 : Blo 487790 927949 := bbase (se 3 (by rfl) ⟨173990, by rfl⟩ : syracuseStep 927949 = 347981) (by norm_num)
theorem B829669 : Blo 487790 829669 := bbase (se 4 (by rfl) ⟨77781, by rfl⟩ : syracuseStep 829669 = 155563) (by norm_num)
theorem B3352853 : Blo 487790 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B829757 : Blo 487790 829757 := bbase (se 3 (by rfl) ⟨155579, by rfl⟩ : syracuseStep 829757 = 311159) (by norm_num)
theorem B698701 : Blo 487790 698701 := bbase (se 3 (by rfl) ⟨131006, by rfl⟩ : syracuseStep 698701 = 262013) (by norm_num)
theorem B928093 : Blo 487790 928093 := bbase (se 3 (by rfl) ⟨174017, by rfl⟩ : syracuseStep 928093 = 348035) (by norm_num)
theorem B1648997 : Blo 487790 1648997 := bbase (se 4 (by rfl) ⟨154593, by rfl⟩ : syracuseStep 1648997 = 309187) (by norm_num)
theorem B829885 : Blo 487790 829885 := bbase (se 3 (by rfl) ⟨155603, by rfl⟩ : syracuseStep 829885 = 311207) (by norm_num)
theorem B3713525 : Blo 487790 3713525 := bbase (se 5 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 3713525 = 348143) (by norm_num)
theorem B928253 : Blo 487790 928253 := bbase (se 3 (by rfl) ⟨174047, by rfl⟩ : syracuseStep 928253 = 348095) (by norm_num)
theorem B1190413 : Blo 487790 1190413 := bbase (se 3 (by rfl) ⟨223202, by rfl⟩ : syracuseStep 1190413 = 446405) (by norm_num)
theorem B731693 : Blo 487790 731693 := bbase (se 3 (by rfl) ⟨137192, by rfl⟩ : syracuseStep 731693 = 274385) (by norm_num)
theorem B731717 : Blo 487790 731717 := bbase (se 4 (by rfl) ⟨68598, by rfl⟩ : syracuseStep 731717 = 137197) (by norm_num)
theorem B731741 : Blo 487790 731741 := bbase (se 3 (by rfl) ⟨137201, by rfl⟩ : syracuseStep 731741 = 274403) (by norm_num)
theorem B731765 : Blo 487790 731765 := bbase (se 5 (by rfl) ⟨34301, by rfl⟩ : syracuseStep 731765 = 68603) (by norm_num)
theorem B2894453 : Blo 487790 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B731789 : Blo 487790 731789 := bbase (se 3 (by rfl) ⟨137210, by rfl⟩ : syracuseStep 731789 = 274421) (by norm_num)
theorem B928397 : Blo 487790 928397 := bbase (se 3 (by rfl) ⟨174074, by rfl⟩ : syracuseStep 928397 = 348149) (by norm_num)
theorem B731813 : Blo 487790 731813 := bbase (se 4 (by rfl) ⟨68607, by rfl⟩ : syracuseStep 731813 = 137215) (by norm_num)
theorem B731837 : Blo 487790 731837 := bbase (se 3 (by rfl) ⟨137219, by rfl⟩ : syracuseStep 731837 = 274439) (by norm_num)
theorem B699077 : Blo 487790 699077 := bbase (se 4 (by rfl) ⟨65538, by rfl⟩ : syracuseStep 699077 = 131077) (by norm_num)
theorem B731861 : Blo 487790 731861 := bbase (se 7 (by rfl) ⟨8576, by rfl⟩ : syracuseStep 731861 = 17153) (by norm_num)
theorem B731885 : Blo 487790 731885 := bbase (se 3 (by rfl) ⟨137228, by rfl⟩ : syracuseStep 731885 = 274457) (by norm_num)
theorem B731909 : Blo 487790 731909 := bbase (se 4 (by rfl) ⟨68616, by rfl⟩ : syracuseStep 731909 = 137233) (by norm_num)
theorem B1649429 : Blo 487790 1649429 := bbase (se 6 (by rfl) ⟨38658, by rfl⟩ : syracuseStep 1649429 = 77317) (by norm_num)
theorem B994069 : Blo 487790 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B731933 : Blo 487790 731933 := bbase (se 3 (by rfl) ⟨137237, by rfl⟩ : syracuseStep 731933 = 274475) (by norm_num)
theorem B731957 : Blo 487790 731957 := bbase (se 5 (by rfl) ⟨34310, by rfl⟩ : syracuseStep 731957 = 68621) (by norm_num)
theorem B994117 : Blo 487790 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B731981 : Blo 487790 731981 := bbase (se 3 (by rfl) ⟨137246, by rfl⟩ : syracuseStep 731981 = 274493) (by norm_num)
theorem B732005 : Blo 487790 732005 := bbase (se 4 (by rfl) ⟨68625, by rfl⟩ : syracuseStep 732005 = 137251) (by norm_num)
theorem B502633 : Blo 487790 502633 := bbase (se 2 (by rfl) ⟨188487, by rfl⟩ : syracuseStep 502633 = 376975) (by norm_num)
theorem B732029 : Blo 487790 732029 := bbase (se 3 (by rfl) ⟨137255, by rfl⟩ : syracuseStep 732029 = 274511) (by norm_num)
theorem B732053 : Blo 487790 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B732077 : Blo 487790 732077 := bbase (se 3 (by rfl) ⟨137264, by rfl⟩ : syracuseStep 732077 = 274529) (by norm_num)
theorem B928685 : Blo 487790 928685 := bbase (se 3 (by rfl) ⟨174128, by rfl⟩ : syracuseStep 928685 = 348257) (by norm_num)
theorem B732101 : Blo 487790 732101 := bbase (se 4 (by rfl) ⟨68634, by rfl⟩ : syracuseStep 732101 = 137269) (by norm_num)
theorem B732125 : Blo 487790 732125 := bbase (se 3 (by rfl) ⟨137273, by rfl⟩ : syracuseStep 732125 = 274547) (by norm_num)
theorem B732149 : Blo 487790 732149 := bbase (se 5 (by rfl) ⟨34319, by rfl⟩ : syracuseStep 732149 = 68639) (by norm_num)
theorem B732173 : Blo 487790 732173 := bbase (se 3 (by rfl) ⟨137282, by rfl⟩ : syracuseStep 732173 = 274565) (by norm_num)
theorem B732197 : Blo 487790 732197 := bbase (se 4 (by rfl) ⟨68643, by rfl⟩ : syracuseStep 732197 = 137287) (by norm_num)
theorem B732221 : Blo 487790 732221 := bbase (se 3 (by rfl) ⟨137291, by rfl⟩ : syracuseStep 732221 = 274583) (by norm_num)
theorem B928837 : Blo 487790 928837 := bbase (se 4 (by rfl) ⟨87078, by rfl⟩ : syracuseStep 928837 = 174157) (by norm_num)
theorem B732245 : Blo 487790 732245 := bbase (se 8 (by rfl) ⟨4290, by rfl⟩ : syracuseStep 732245 = 8581) (by norm_num)
theorem B732269 : Blo 487790 732269 := bbase (se 3 (by rfl) ⟨137300, by rfl⟩ : syracuseStep 732269 = 274601) (by norm_num)
theorem B732293 : Blo 487790 732293 := bbase (se 4 (by rfl) ⟨68652, by rfl⟩ : syracuseStep 732293 = 137305) (by norm_num)
theorem B732317 : Blo 487790 732317 := bbase (se 3 (by rfl) ⟨137309, by rfl⟩ : syracuseStep 732317 = 274619) (by norm_num)
theorem B732341 : Blo 487790 732341 := bbase (se 5 (by rfl) ⟨34328, by rfl⟩ : syracuseStep 732341 = 68657) (by norm_num)
theorem B1486021 : Blo 487790 1486021 := bbase (se 4 (by rfl) ⟨139314, by rfl⟩ : syracuseStep 1486021 = 278629) (by norm_num)
theorem B1649861 : Blo 487790 1649861 := bbase (se 4 (by rfl) ⟨154674, by rfl⟩ : syracuseStep 1649861 = 309349) (by norm_num)
theorem B732365 : Blo 487790 732365 := bbase (se 3 (by rfl) ⟨137318, by rfl⟩ : syracuseStep 732365 = 274637) (by norm_num)
theorem B732389 : Blo 487790 732389 := bbase (se 4 (by rfl) ⟨68661, by rfl⟩ : syracuseStep 732389 = 137323) (by norm_num)
theorem B732413 : Blo 487790 732413 := bbase (se 3 (by rfl) ⟨137327, by rfl⟩ : syracuseStep 732413 = 274655) (by norm_num)
theorem B732437 : Blo 487790 732437 := bbase (se 6 (by rfl) ⟨17166, by rfl⟩ : syracuseStep 732437 = 34333) (by norm_num)
theorem B732461 : Blo 487790 732461 := bbase (se 3 (by rfl) ⟨137336, by rfl⟩ : syracuseStep 732461 = 274673) (by norm_num)
theorem B732485 : Blo 487790 732485 := bbase (se 4 (by rfl) ⟨68670, by rfl⟩ : syracuseStep 732485 = 137341) (by norm_num)
theorem B732509 : Blo 487790 732509 := bbase (se 3 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 732509 = 274691) (by norm_num)
theorem B732533 : Blo 487790 732533 := bbase (se 5 (by rfl) ⟨34337, by rfl⟩ : syracuseStep 732533 = 68675) (by norm_num)
theorem B929141 : Blo 487790 929141 := bbase (se 5 (by rfl) ⟨43553, by rfl⟩ : syracuseStep 929141 = 87107) (by norm_num)
theorem B732557 : Blo 487790 732557 := bbase (se 3 (by rfl) ⟨137354, by rfl⟩ : syracuseStep 732557 = 274709) (by norm_num)
theorem B732581 : Blo 487790 732581 := bbase (se 4 (by rfl) ⟨68679, by rfl⟩ : syracuseStep 732581 = 137359) (by norm_num)
theorem B732605 : Blo 487790 732605 := bbase (se 3 (by rfl) ⟨137363, by rfl⟩ : syracuseStep 732605 = 274727) (by norm_num)
theorem B732629 : Blo 487790 732629 := bbase (se 7 (by rfl) ⟨8585, by rfl⟩ : syracuseStep 732629 = 17171) (by norm_num)
theorem B732653 : Blo 487790 732653 := bbase (se 3 (by rfl) ⟨137372, by rfl⟩ : syracuseStep 732653 = 274745) (by norm_num)
theorem B732677 : Blo 487790 732677 := bbase (se 4 (by rfl) ⟨68688, by rfl⟩ : syracuseStep 732677 = 137377) (by norm_num)
theorem B732701 : Blo 487790 732701 := bbase (se 3 (by rfl) ⟨137381, by rfl⟩ : syracuseStep 732701 = 274763) (by norm_num)
theorem B732725 : Blo 487790 732725 := bbase (se 5 (by rfl) ⟨34346, by rfl⟩ : syracuseStep 732725 = 68693) (by norm_num)
theorem B732749 : Blo 487790 732749 := bbase (se 3 (by rfl) ⟨137390, by rfl⟩ : syracuseStep 732749 = 274781) (by norm_num)
theorem B732773 : Blo 487790 732773 := bbase (se 4 (by rfl) ⟨68697, by rfl⟩ : syracuseStep 732773 = 137395) (by norm_num)
theorem B1650293 : Blo 487790 1650293 := bbase (se 5 (by rfl) ⟨77357, by rfl⟩ : syracuseStep 1650293 = 154715) (by norm_num)
theorem B732797 : Blo 487790 732797 := bbase (se 3 (by rfl) ⟨137399, by rfl⟩ : syracuseStep 732797 = 274799) (by norm_num)
theorem B732821 : Blo 487790 732821 := bbase (se 6 (by rfl) ⟨17175, by rfl⟩ : syracuseStep 732821 = 34351) (by norm_num)
theorem B732845 : Blo 487790 732845 := bbase (se 3 (by rfl) ⟨137408, by rfl⟩ : syracuseStep 732845 = 274817) (by norm_num)
theorem B732869 : Blo 487790 732869 := bbase (se 4 (by rfl) ⟨68706, by rfl⟩ : syracuseStep 732869 = 137413) (by norm_num)
theorem B732893 : Blo 487790 732893 := bbase (se 3 (by rfl) ⟨137417, by rfl⟩ : syracuseStep 732893 = 274835) (by norm_num)
theorem B732917 : Blo 487790 732917 := bbase (se 5 (by rfl) ⟨34355, by rfl⟩ : syracuseStep 732917 = 68711) (by norm_num)
theorem B732941 : Blo 487790 732941 := bbase (se 3 (by rfl) ⟨137426, by rfl⟩ : syracuseStep 732941 = 274853) (by norm_num)
theorem B6893333 : Blo 487790 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B732965 : Blo 487790 732965 := bbase (se 4 (by rfl) ⟨68715, by rfl⟩ : syracuseStep 732965 = 137431) (by norm_num)
theorem B3518261 : Blo 487790 3518261 := bbase (se 5 (by rfl) ⟨164918, by rfl⟩ : syracuseStep 3518261 = 329837) (by norm_num)
theorem B732989 : Blo 487790 732989 := bbase (se 3 (by rfl) ⟨137435, by rfl⟩ : syracuseStep 732989 = 274871) (by norm_num)
theorem B2273093 : Blo 487790 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B733013 : Blo 487790 733013 := bbase (se 9 (by rfl) ⟨2147, by rfl⟩ : syracuseStep 733013 = 4295) (by norm_num)
theorem B733037 : Blo 487790 733037 := bbase (se 3 (by rfl) ⟨137444, by rfl⟩ : syracuseStep 733037 = 274889) (by norm_num)
theorem B733061 : Blo 487790 733061 := bbase (se 4 (by rfl) ⟨68724, by rfl⟩ : syracuseStep 733061 = 137449) (by norm_num)
theorem B733085 : Blo 487790 733085 := bbase (se 3 (by rfl) ⟨137453, by rfl⟩ : syracuseStep 733085 = 274907) (by norm_num)
theorem B733109 : Blo 487790 733109 := bbase (se 5 (by rfl) ⟨34364, by rfl⟩ : syracuseStep 733109 = 68729) (by norm_num)
theorem B733133 : Blo 487790 733133 := bbase (se 3 (by rfl) ⟨137462, by rfl⟩ : syracuseStep 733133 = 274925) (by norm_num)
theorem B733157 : Blo 487790 733157 := bbase (se 4 (by rfl) ⟨68733, by rfl⟩ : syracuseStep 733157 = 137467) (by norm_num)
theorem B733181 : Blo 487790 733181 := bbase (se 3 (by rfl) ⟨137471, by rfl⟩ : syracuseStep 733181 = 274943) (by norm_num)
theorem B1978373 : Blo 487790 1978373 := bbase (se 4 (by rfl) ⟨185472, by rfl⟩ : syracuseStep 1978373 = 370945) (by norm_num)
theorem B733205 : Blo 487790 733205 := bbase (se 6 (by rfl) ⟨17184, by rfl⟩ : syracuseStep 733205 = 34369) (by norm_num)
theorem B1650725 : Blo 487790 1650725 := bbase (se 4 (by rfl) ⟨154755, by rfl⟩ : syracuseStep 1650725 = 309511) (by norm_num)
theorem B733229 : Blo 487790 733229 := bbase (se 3 (by rfl) ⟨137480, by rfl⟩ : syracuseStep 733229 = 274961) (by norm_num)
theorem B733253 : Blo 487790 733253 := bbase (se 4 (by rfl) ⟨68742, by rfl⟩ : syracuseStep 733253 = 137485) (by norm_num)
theorem B733277 : Blo 487790 733277 := bbase (se 3 (by rfl) ⟨137489, by rfl⟩ : syracuseStep 733277 = 274979) (by norm_num)
theorem B929893 : Blo 487790 929893 := bbase (se 4 (by rfl) ⟨87177, by rfl⟩ : syracuseStep 929893 = 174355) (by norm_num)
theorem B733301 : Blo 487790 733301 := bbase (se 5 (by rfl) ⟨34373, by rfl⟩ : syracuseStep 733301 = 68747) (by norm_num)
theorem B733325 : Blo 487790 733325 := bbase (se 3 (by rfl) ⟨137498, by rfl⟩ : syracuseStep 733325 = 274997) (by norm_num)
theorem B897173 : Blo 487790 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B733349 : Blo 487790 733349 := bbase (se 4 (by rfl) ⟨68751, by rfl⟩ : syracuseStep 733349 = 137503) (by norm_num)
theorem B733373 : Blo 487790 733373 := bbase (se 3 (by rfl) ⟨137507, by rfl⟩ : syracuseStep 733373 = 275015) (by norm_num)
theorem B733397 : Blo 487790 733397 := bbase (se 7 (by rfl) ⟨8594, by rfl⟩ : syracuseStep 733397 = 17189) (by norm_num)
theorem B733421 : Blo 487790 733421 := bbase (se 3 (by rfl) ⟨137516, by rfl⟩ : syracuseStep 733421 = 275033) (by norm_num)
theorem B930037 : Blo 487790 930037 := bbase (se 5 (by rfl) ⟨43595, by rfl⟩ : syracuseStep 930037 = 87191) (by norm_num)
theorem B733445 : Blo 487790 733445 := bbase (se 4 (by rfl) ⟨68760, by rfl⟩ : syracuseStep 733445 = 137521) (by norm_num)
theorem B733469 : Blo 487790 733469 := bbase (se 3 (by rfl) ⟨137525, by rfl⟩ : syracuseStep 733469 = 275051) (by norm_num)
theorem B733493 : Blo 487790 733493 := bbase (se 5 (by rfl) ⟨34382, by rfl⟩ : syracuseStep 733493 = 68765) (by norm_num)
theorem B504137 : Blo 487790 504137 := bbase (se 2 (by rfl) ⟨189051, by rfl⟩ : syracuseStep 504137 = 378103) (by norm_num)
theorem B733517 : Blo 487790 733517 := bbase (se 3 (by rfl) ⟨137534, by rfl⟩ : syracuseStep 733517 = 275069) (by norm_num)
theorem B733541 : Blo 487790 733541 := bbase (se 4 (by rfl) ⟨68769, by rfl⟩ : syracuseStep 733541 = 137539) (by norm_num)
theorem B733565 : Blo 487790 733565 := bbase (se 3 (by rfl) ⟨137543, by rfl⟩ : syracuseStep 733565 = 275087) (by norm_num)
theorem B733589 : Blo 487790 733589 := bbase (se 6 (by rfl) ⟨17193, by rfl⟩ : syracuseStep 733589 = 34387) (by norm_num)
theorem B930197 : Blo 487790 930197 := bbase (se 6 (by rfl) ⟨21801, by rfl⟩ : syracuseStep 930197 = 43603) (by norm_num)
theorem B733613 : Blo 487790 733613 := bbase (se 3 (by rfl) ⟨137552, by rfl⟩ : syracuseStep 733613 = 275105) (by norm_num)
theorem B733637 : Blo 487790 733637 := bbase (se 4 (by rfl) ⟨68778, by rfl⟩ : syracuseStep 733637 = 137557) (by norm_num)
theorem B1651157 : Blo 487790 1651157 := bbase (se 7 (by rfl) ⟨19349, by rfl⟩ : syracuseStep 1651157 = 38699) (by norm_num)
theorem B733661 : Blo 487790 733661 := bbase (se 3 (by rfl) ⟨137561, by rfl⟩ : syracuseStep 733661 = 275123) (by norm_num)
theorem B733685 : Blo 487790 733685 := bbase (se 5 (by rfl) ⟨34391, by rfl⟩ : syracuseStep 733685 = 68783) (by norm_num)
theorem B733709 : Blo 487790 733709 := bbase (se 3 (by rfl) ⟨137570, by rfl⟩ : syracuseStep 733709 = 275141) (by norm_num)
theorem B733733 : Blo 487790 733733 := bbase (se 4 (by rfl) ⟨68787, by rfl⟩ : syracuseStep 733733 = 137575) (by norm_num)
theorem B930341 : Blo 487790 930341 := bbase (se 4 (by rfl) ⟨87219, by rfl⟩ : syracuseStep 930341 = 174439) (by norm_num)
theorem B733757 : Blo 487790 733757 := bbase (se 3 (by rfl) ⟨137579, by rfl⟩ : syracuseStep 733757 = 275159) (by norm_num)
theorem B733781 : Blo 487790 733781 := bbase (se 8 (by rfl) ⟨4299, by rfl⟩ : syracuseStep 733781 = 8599) (by norm_num)
theorem B733805 : Blo 487790 733805 := bbase (se 3 (by rfl) ⟨137588, by rfl⟩ : syracuseStep 733805 = 275177) (by norm_num)
theorem B733829 : Blo 487790 733829 := bbase (se 4 (by rfl) ⟨68796, by rfl⟩ : syracuseStep 733829 = 137593) (by norm_num)
theorem B733853 : Blo 487790 733853 := bbase (se 3 (by rfl) ⟨137597, by rfl⟩ : syracuseStep 733853 = 275195) (by norm_num)
theorem B733877 : Blo 487790 733877 := bbase (se 5 (by rfl) ⟨34400, by rfl⟩ : syracuseStep 733877 = 68801) (by norm_num)
theorem B733901 : Blo 487790 733901 := bbase (se 3 (by rfl) ⟨137606, by rfl⟩ : syracuseStep 733901 = 275213) (by norm_num)
theorem B733925 : Blo 487790 733925 := bbase (se 4 (by rfl) ⟨68805, by rfl⟩ : syracuseStep 733925 = 137611) (by norm_num)
theorem B733949 : Blo 487790 733949 := bbase (se 3 (by rfl) ⟨137615, by rfl⟩ : syracuseStep 733949 = 275231) (by norm_num)
theorem B2470661 : Blo 487790 2470661 := bbase (se 4 (by rfl) ⟨231624, by rfl⟩ : syracuseStep 2470661 = 463249) (by norm_num)
theorem B733973 : Blo 487790 733973 := bbase (se 6 (by rfl) ⟨17202, by rfl⟩ : syracuseStep 733973 = 34405) (by norm_num)
theorem B733997 : Blo 487790 733997 := bbase (se 3 (by rfl) ⟨137624, by rfl⟩ : syracuseStep 733997 = 275249) (by norm_num)
theorem B930629 : Blo 487790 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B734021 : Blo 487790 734021 := bbase (se 4 (by rfl) ⟨68814, by rfl⟩ : syracuseStep 734021 = 137629) (by norm_num)
theorem B734045 : Blo 487790 734045 := bbase (se 3 (by rfl) ⟨137633, by rfl⟩ : syracuseStep 734045 = 275267) (by norm_num)
theorem B734069 : Blo 487790 734069 := bbase (se 5 (by rfl) ⟨34409, by rfl⟩ : syracuseStep 734069 = 68819) (by norm_num)
theorem B1651589 : Blo 487790 1651589 := bbase (se 4 (by rfl) ⟨154836, by rfl⟩ : syracuseStep 1651589 = 309673) (by norm_num)
theorem B734093 : Blo 487790 734093 := bbase (se 3 (by rfl) ⟨137642, by rfl⟩ : syracuseStep 734093 = 275285) (by norm_num)
theorem B734117 : Blo 487790 734117 := bbase (se 4 (by rfl) ⟨68823, by rfl⟩ : syracuseStep 734117 = 137647) (by norm_num)
theorem B734141 : Blo 487790 734141 := bbase (se 3 (by rfl) ⟨137651, by rfl⟩ : syracuseStep 734141 = 275303) (by norm_num)
theorem B12530645 : Blo 487790 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B734165 : Blo 487790 734165 := bbase (se 7 (by rfl) ⟨8603, by rfl⟩ : syracuseStep 734165 = 17207) (by norm_num)
theorem B930781 : Blo 487790 930781 := bbase (se 3 (by rfl) ⟨174521, by rfl⟩ : syracuseStep 930781 = 349043) (by norm_num)
theorem B734189 : Blo 487790 734189 := bbase (se 3 (by rfl) ⟨137660, by rfl⟩ : syracuseStep 734189 = 275321) (by norm_num)
theorem B734213 : Blo 487790 734213 := bbase (se 4 (by rfl) ⟨68832, by rfl⟩ : syracuseStep 734213 = 137665) (by norm_num)
theorem B734237 : Blo 487790 734237 := bbase (se 3 (by rfl) ⟨137669, by rfl⟩ : syracuseStep 734237 = 275339) (by norm_num)
theorem B734261 : Blo 487790 734261 := bbase (se 5 (by rfl) ⟨34418, by rfl⟩ : syracuseStep 734261 = 68837) (by norm_num)
theorem B734285 : Blo 487790 734285 := bbase (se 3 (by rfl) ⟨137678, by rfl⟩ : syracuseStep 734285 = 275357) (by norm_num)
theorem B734309 : Blo 487790 734309 := bbase (se 4 (by rfl) ⟨68841, by rfl⟩ : syracuseStep 734309 = 137683) (by norm_num)
theorem B734333 : Blo 487790 734333 := bbase (se 3 (by rfl) ⟨137687, by rfl⟩ : syracuseStep 734333 = 275375) (by norm_num)
theorem B734357 : Blo 487790 734357 := bbase (se 6 (by rfl) ⟨17211, by rfl⟩ : syracuseStep 734357 = 34423) (by norm_num)
theorem B734381 : Blo 487790 734381 := bbase (se 3 (by rfl) ⟨137696, by rfl⟩ : syracuseStep 734381 = 275393) (by norm_num)
theorem B1881269 : Blo 487790 1881269 := bbase (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) (by norm_num)
theorem B734405 : Blo 487790 734405 := bbase (se 4 (by rfl) ⟨68850, by rfl⟩ : syracuseStep 734405 = 137701) (by norm_num)
theorem B734429 : Blo 487790 734429 := bbase (se 3 (by rfl) ⟨137705, by rfl⟩ : syracuseStep 734429 = 275411) (by norm_num)
theorem B1193197 : Blo 487790 1193197 := bbase (se 3 (by rfl) ⟨223724, by rfl⟩ : syracuseStep 1193197 = 447449) (by norm_num)
theorem B734453 : Blo 487790 734453 := bbase (se 5 (by rfl) ⟨34427, by rfl⟩ : syracuseStep 734453 = 68855) (by norm_num)
theorem B734477 : Blo 487790 734477 := bbase (se 3 (by rfl) ⟨137714, by rfl⟩ : syracuseStep 734477 = 275429) (by norm_num)
theorem B931085 : Blo 487790 931085 := bbase (se 3 (by rfl) ⟨174578, by rfl⟩ : syracuseStep 931085 = 349157) (by norm_num)
theorem B734501 : Blo 487790 734501 := bbase (se 4 (by rfl) ⟨68859, by rfl⟩ : syracuseStep 734501 = 137719) (by norm_num)
theorem B1652021 : Blo 487790 1652021 := bbase (se 5 (by rfl) ⟨77438, by rfl⟩ : syracuseStep 1652021 = 154877) (by norm_num)
theorem B734525 : Blo 487790 734525 := bbase (se 3 (by rfl) ⟨137723, by rfl⟩ : syracuseStep 734525 = 275447) (by norm_num)
theorem B734549 : Blo 487790 734549 := bbase (se 13 (by rfl) ⟨134, by rfl⟩ : syracuseStep 734549 = 269) (by norm_num)
theorem B734573 : Blo 487790 734573 := bbase (se 3 (by rfl) ⟨137732, by rfl⟩ : syracuseStep 734573 = 275465) (by norm_num)
theorem B734597 : Blo 487790 734597 := bbase (se 4 (by rfl) ⟨68868, by rfl⟩ : syracuseStep 734597 = 137737) (by norm_num)
theorem B734621 : Blo 487790 734621 := bbase (se 3 (by rfl) ⟨137741, by rfl⟩ : syracuseStep 734621 = 275483) (by norm_num)
theorem B734645 : Blo 487790 734645 := bbase (se 5 (by rfl) ⟨34436, by rfl⟩ : syracuseStep 734645 = 68873) (by norm_num)
theorem B734669 : Blo 487790 734669 := bbase (se 3 (by rfl) ⟨137750, by rfl⟩ : syracuseStep 734669 = 275501) (by norm_num)
theorem B734693 : Blo 487790 734693 := bbase (se 4 (by rfl) ⟨68877, by rfl⟩ : syracuseStep 734693 = 137755) (by norm_num)
theorem B734717 : Blo 487790 734717 := bbase (se 3 (by rfl) ⟨137759, by rfl⟩ : syracuseStep 734717 = 275519) (by norm_num)
theorem B734741 : Blo 487790 734741 := bbase (se 6 (by rfl) ⟨17220, by rfl⟩ : syracuseStep 734741 = 34441) (by norm_num)
theorem B8402453 : Blo 487790 8402453 := bbase (se 6 (by rfl) ⟨196932, by rfl⟩ : syracuseStep 8402453 = 393865) (by norm_num)
theorem B734765 : Blo 487790 734765 := bbase (se 3 (by rfl) ⟨137768, by rfl⟩ : syracuseStep 734765 = 275537) (by norm_num)
theorem B734789 : Blo 487790 734789 := bbase (se 4 (by rfl) ⟨68886, by rfl⟩ : syracuseStep 734789 = 137773) (by norm_num)
theorem B734813 : Blo 487790 734813 := bbase (se 3 (by rfl) ⟨137777, by rfl⟩ : syracuseStep 734813 = 275555) (by norm_num)
theorem B996965 : Blo 487790 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B734837 : Blo 487790 734837 := bbase (se 5 (by rfl) ⟨34445, by rfl⟩ : syracuseStep 734837 = 68891) (by norm_num)
theorem B734861 : Blo 487790 734861 := bbase (se 3 (by rfl) ⟨137786, by rfl⟩ : syracuseStep 734861 = 275573) (by norm_num)
theorem B734885 : Blo 487790 734885 := bbase (se 4 (by rfl) ⟨68895, by rfl⟩ : syracuseStep 734885 = 137791) (by norm_num)
theorem B734909 : Blo 487790 734909 := bbase (se 3 (by rfl) ⟨137795, by rfl⟩ : syracuseStep 734909 = 275591) (by norm_num)
theorem B734933 : Blo 487790 734933 := bbase (se 7 (by rfl) ⟨8612, by rfl⟩ : syracuseStep 734933 = 17225) (by norm_num)
theorem B1652453 : Blo 487790 1652453 := bbase (se 4 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 1652453 = 309835) (by norm_num)
theorem B734957 : Blo 487790 734957 := bbase (se 3 (by rfl) ⟨137804, by rfl⟩ : syracuseStep 734957 = 275609) (by norm_num)
theorem B734981 : Blo 487790 734981 := bbase (se 4 (by rfl) ⟨68904, by rfl⟩ : syracuseStep 734981 = 137809) (by norm_num)
theorem B735005 : Blo 487790 735005 := bbase (se 3 (by rfl) ⟨137813, by rfl⟩ : syracuseStep 735005 = 275627) (by norm_num)
theorem B735029 : Blo 487790 735029 := bbase (se 5 (by rfl) ⟨34454, by rfl⟩ : syracuseStep 735029 = 68909) (by norm_num)
theorem B735053 : Blo 487790 735053 := bbase (se 3 (by rfl) ⟨137822, by rfl⟩ : syracuseStep 735053 = 275645) (by norm_num)
theorem B735077 : Blo 487790 735077 := bbase (se 4 (by rfl) ⟨68913, by rfl⟩ : syracuseStep 735077 = 137827) (by norm_num)
theorem B735101 : Blo 487790 735101 := bbase (se 3 (by rfl) ⟨137831, by rfl⟩ : syracuseStep 735101 = 275663) (by norm_num)
theorem B735125 : Blo 487790 735125 := bbase (se 6 (by rfl) ⟨17229, by rfl⟩ : syracuseStep 735125 = 34459) (by norm_num)
theorem B735149 : Blo 487790 735149 := bbase (se 3 (by rfl) ⟨137840, by rfl⟩ : syracuseStep 735149 = 275681) (by norm_num)
theorem B735173 : Blo 487790 735173 := bbase (se 4 (by rfl) ⟨68922, by rfl⟩ : syracuseStep 735173 = 137845) (by norm_num)
theorem B735197 : Blo 487790 735197 := bbase (se 3 (by rfl) ⟨137849, by rfl⟩ : syracuseStep 735197 = 275699) (by norm_num)
theorem B735221 : Blo 487790 735221 := bbase (se 5 (by rfl) ⟨34463, by rfl⟩ : syracuseStep 735221 = 68927) (by norm_num)
theorem B931837 : Blo 487790 931837 := bbase (se 3 (by rfl) ⟨174719, by rfl⟩ : syracuseStep 931837 = 349439) (by norm_num)
theorem B735245 : Blo 487790 735245 := bbase (se 3 (by rfl) ⟨137858, by rfl⟩ : syracuseStep 735245 = 275717) (by norm_num)
theorem B2471957 : Blo 487790 2471957 := bbase (se 6 (by rfl) ⟨57936, by rfl⟩ : syracuseStep 2471957 = 115873) (by norm_num)
theorem B735269 : Blo 487790 735269 := bbase (se 4 (by rfl) ⟨68931, by rfl⟩ : syracuseStep 735269 = 137863) (by norm_num)
theorem B735293 : Blo 487790 735293 := bbase (se 3 (by rfl) ⟨137867, by rfl⟩ : syracuseStep 735293 = 275735) (by norm_num)
theorem B735317 : Blo 487790 735317 := bbase (se 8 (by rfl) ⟨4308, by rfl⟩ : syracuseStep 735317 = 8617) (by norm_num)
theorem B735341 : Blo 487790 735341 := bbase (se 3 (by rfl) ⟨137876, by rfl⟩ : syracuseStep 735341 = 275753) (by norm_num)
theorem B768125 : Blo 487790 768125 := bbase (se 3 (by rfl) ⟨144023, by rfl⟩ : syracuseStep 768125 = 288047) (by norm_num)
theorem B735365 : Blo 487790 735365 := bbase (se 4 (by rfl) ⟨68940, by rfl⟩ : syracuseStep 735365 = 137881) (by norm_num)
theorem B931981 : Blo 487790 931981 := bbase (se 3 (by rfl) ⟨174746, by rfl⟩ : syracuseStep 931981 = 349493) (by norm_num)
theorem B1652885 : Blo 487790 1652885 := bbase (se 6 (by rfl) ⟨38739, by rfl⟩ : syracuseStep 1652885 = 77479) (by norm_num)
theorem B735389 : Blo 487790 735389 := bbase (se 3 (by rfl) ⟨137885, by rfl⟩ : syracuseStep 735389 = 275771) (by norm_num)
theorem B735413 : Blo 487790 735413 := bbase (se 5 (by rfl) ⟨34472, by rfl⟩ : syracuseStep 735413 = 68945) (by norm_num)
theorem B735437 : Blo 487790 735437 := bbase (se 3 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 735437 = 275789) (by norm_num)
theorem B735461 : Blo 487790 735461 := bbase (se 4 (by rfl) ⟨68949, by rfl⟩ : syracuseStep 735461 = 137899) (by norm_num)
theorem B735485 : Blo 487790 735485 := bbase (se 3 (by rfl) ⟨137903, by rfl⟩ : syracuseStep 735485 = 275807) (by norm_num)
theorem B1325317 : Blo 487790 1325317 := bbase (se 4 (by rfl) ⟨124248, by rfl⟩ : syracuseStep 1325317 = 248497) (by norm_num)
theorem B735509 : Blo 487790 735509 := bbase (se 6 (by rfl) ⟨17238, by rfl⟩ : syracuseStep 735509 = 34477) (by norm_num)
theorem B735533 : Blo 487790 735533 := bbase (se 3 (by rfl) ⟨137912, by rfl⟩ : syracuseStep 735533 = 275825) (by norm_num)
theorem B932141 : Blo 487790 932141 := bbase (se 3 (by rfl) ⟨174776, by rfl⟩ : syracuseStep 932141 = 349553) (by norm_num)
theorem B735557 : Blo 487790 735557 := bbase (se 4 (by rfl) ⟨68958, by rfl⟩ : syracuseStep 735557 = 137917) (by norm_num)
theorem B735581 : Blo 487790 735581 := bbase (se 3 (by rfl) ⟨137921, by rfl⟩ : syracuseStep 735581 = 275843) (by norm_num)
theorem B735605 : Blo 487790 735605 := bbase (se 5 (by rfl) ⟨34481, by rfl⟩ : syracuseStep 735605 = 68963) (by norm_num)
theorem B735629 : Blo 487790 735629 := bbase (se 3 (by rfl) ⟨137930, by rfl⟩ : syracuseStep 735629 = 275861) (by norm_num)
theorem B735653 : Blo 487790 735653 := bbase (se 4 (by rfl) ⟨68967, by rfl⟩ : syracuseStep 735653 = 137935) (by norm_num)
theorem B735677 : Blo 487790 735677 := bbase (se 3 (by rfl) ⟨137939, by rfl⟩ : syracuseStep 735677 = 275879) (by norm_num)
theorem B932285 : Blo 487790 932285 := bbase (se 3 (by rfl) ⟨174803, by rfl⟩ : syracuseStep 932285 = 349607) (by norm_num)
theorem B735701 : Blo 487790 735701 := bbase (se 7 (by rfl) ⟨8621, by rfl⟩ : syracuseStep 735701 = 17243) (by norm_num)
theorem B735725 : Blo 487790 735725 := bbase (se 3 (by rfl) ⟨137948, by rfl⟩ : syracuseStep 735725 = 275897) (by norm_num)
theorem B735749 : Blo 487790 735749 := bbase (se 4 (by rfl) ⟨68976, by rfl⟩ : syracuseStep 735749 = 137953) (by norm_num)
theorem B735773 : Blo 487790 735773 := bbase (se 3 (by rfl) ⟨137957, by rfl⟩ : syracuseStep 735773 = 275915) (by norm_num)
theorem B735797 : Blo 487790 735797 := bbase (se 5 (by rfl) ⟨34490, by rfl⟩ : syracuseStep 735797 = 68981) (by norm_num)
theorem B1653317 : Blo 487790 1653317 := bbase (se 4 (by rfl) ⟨154998, by rfl⟩ : syracuseStep 1653317 = 309997) (by norm_num)
theorem B735821 : Blo 487790 735821 := bbase (se 3 (by rfl) ⟨137966, by rfl⟩ : syracuseStep 735821 = 275933) (by norm_num)
theorem B735845 : Blo 487790 735845 := bbase (se 4 (by rfl) ⟨68985, by rfl⟩ : syracuseStep 735845 = 137971) (by norm_num)
theorem B735869 : Blo 487790 735869 := bbase (se 3 (by rfl) ⟨137975, by rfl⟩ : syracuseStep 735869 = 275951) (by norm_num)
theorem B735893 : Blo 487790 735893 := bbase (se 6 (by rfl) ⟨17247, by rfl⟩ : syracuseStep 735893 = 34495) (by norm_num)
theorem B735917 : Blo 487790 735917 := bbase (se 3 (by rfl) ⟨137984, by rfl⟩ : syracuseStep 735917 = 275969) (by norm_num)
theorem B735941 : Blo 487790 735941 := bbase (se 4 (by rfl) ⟨68994, by rfl⟩ : syracuseStep 735941 = 137989) (by norm_num)
theorem B735965 : Blo 487790 735965 := bbase (se 3 (by rfl) ⟨137993, by rfl⟩ : syracuseStep 735965 = 275987) (by norm_num)
theorem B932573 : Blo 487790 932573 := bbase (se 3 (by rfl) ⟨174857, by rfl⟩ : syracuseStep 932573 = 349715) (by norm_num)
theorem B735989 : Blo 487790 735989 := bbase (se 5 (by rfl) ⟨34499, by rfl⟩ : syracuseStep 735989 = 68999) (by norm_num)
theorem B736013 : Blo 487790 736013 := bbase (se 3 (by rfl) ⟨138002, by rfl⟩ : syracuseStep 736013 = 276005) (by norm_num)
theorem B736037 : Blo 487790 736037 := bbase (se 4 (by rfl) ⟨69003, by rfl⟩ : syracuseStep 736037 = 138007) (by norm_num)
theorem B736061 : Blo 487790 736061 := bbase (se 3 (by rfl) ⟨138011, by rfl⟩ : syracuseStep 736061 = 276023) (by norm_num)
theorem B736085 : Blo 487790 736085 := bbase (se 9 (by rfl) ⟨2156, by rfl⟩ : syracuseStep 736085 = 4313) (by norm_num)
theorem B736109 : Blo 487790 736109 := bbase (se 3 (by rfl) ⟨138020, by rfl⟩ : syracuseStep 736109 = 276041) (by norm_num)
theorem B932725 : Blo 487790 932725 := bbase (se 5 (by rfl) ⟨43721, by rfl⟩ : syracuseStep 932725 = 87443) (by norm_num)
theorem B736133 : Blo 487790 736133 := bbase (se 4 (by rfl) ⟨69012, by rfl⟩ : syracuseStep 736133 = 138025) (by norm_num)
theorem B736157 : Blo 487790 736157 := bbase (se 3 (by rfl) ⟨138029, by rfl⟩ : syracuseStep 736157 = 276059) (by norm_num)
theorem B1391525 : Blo 487790 1391525 := bbase (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) (by norm_num)
theorem B736181 : Blo 487790 736181 := bbase (se 5 (by rfl) ⟨34508, by rfl⟩ : syracuseStep 736181 = 69017) (by norm_num)
theorem B736205 : Blo 487790 736205 := bbase (se 3 (by rfl) ⟨138038, by rfl⟩ : syracuseStep 736205 = 276077) (by norm_num)
theorem B736229 : Blo 487790 736229 := bbase (se 4 (by rfl) ⟨69021, by rfl⟩ : syracuseStep 736229 = 138043) (by norm_num)
theorem B1653749 : Blo 487790 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B736253 : Blo 487790 736253 := bbase (se 3 (by rfl) ⟨138047, by rfl⟩ : syracuseStep 736253 = 276095) (by norm_num)
theorem B1195013 : Blo 487790 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B736277 : Blo 487790 736277 := bbase (se 6 (by rfl) ⟨17256, by rfl⟩ : syracuseStep 736277 = 34513) (by norm_num)
theorem B736301 : Blo 487790 736301 := bbase (se 3 (by rfl) ⟨138056, by rfl⟩ : syracuseStep 736301 = 276113) (by norm_num)
theorem B736325 : Blo 487790 736325 := bbase (se 4 (by rfl) ⟨69030, by rfl⟩ : syracuseStep 736325 = 138061) (by norm_num)
theorem B736349 : Blo 487790 736349 := bbase (se 3 (by rfl) ⟨138065, by rfl⟩ : syracuseStep 736349 = 276131) (by norm_num)
theorem B1326181 : Blo 487790 1326181 := bbase (se 4 (by rfl) ⟨124329, by rfl⟩ : syracuseStep 1326181 = 248659) (by norm_num)
theorem B736373 : Blo 487790 736373 := bbase (se 5 (by rfl) ⟨34517, by rfl⟩ : syracuseStep 736373 = 69035) (by norm_num)
theorem B736397 : Blo 487790 736397 := bbase (se 3 (by rfl) ⟨138074, by rfl⟩ : syracuseStep 736397 = 276149) (by norm_num)
theorem B736421 : Blo 487790 736421 := bbase (se 4 (by rfl) ⟨69039, by rfl⟩ : syracuseStep 736421 = 138079) (by norm_num)
theorem B933029 : Blo 487790 933029 := bbase (se 4 (by rfl) ⟨87471, by rfl⟩ : syracuseStep 933029 = 174943) (by norm_num)
theorem B736445 : Blo 487790 736445 := bbase (se 3 (by rfl) ⟨138083, by rfl⟩ : syracuseStep 736445 = 276167) (by norm_num)
theorem B736469 : Blo 487790 736469 := bbase (se 7 (by rfl) ⟨8630, by rfl⟩ : syracuseStep 736469 = 17261) (by norm_num)
theorem B736493 : Blo 487790 736493 := bbase (se 3 (by rfl) ⟨138092, by rfl⟩ : syracuseStep 736493 = 276185) (by norm_num)
theorem B1981685 : Blo 487790 1981685 := bbase (se 5 (by rfl) ⟨92891, by rfl⟩ : syracuseStep 1981685 = 185783) (by norm_num)
theorem B933125 : Blo 487790 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B736517 : Blo 487790 736517 := bbase (se 4 (by rfl) ⟨69048, by rfl⟩ : syracuseStep 736517 = 138097) (by norm_num)
theorem B638237 : Blo 487790 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B736541 : Blo 487790 736541 := bbase (se 3 (by rfl) ⟨138101, by rfl⟩ : syracuseStep 736541 = 276203) (by norm_num)
theorem B2473253 : Blo 487790 2473253 := bbase (se 4 (by rfl) ⟨231867, by rfl⟩ : syracuseStep 2473253 = 463735) (by norm_num)
theorem B736565 : Blo 487790 736565 := bbase (se 5 (by rfl) ⟨34526, by rfl⟩ : syracuseStep 736565 = 69053) (by norm_num)
theorem B736589 : Blo 487790 736589 := bbase (se 3 (by rfl) ⟨138110, by rfl⟩ : syracuseStep 736589 = 276221) (by norm_num)
theorem B736613 : Blo 487790 736613 := bbase (se 4 (by rfl) ⟨69057, by rfl⟩ : syracuseStep 736613 = 138115) (by norm_num)
theorem B736637 : Blo 487790 736637 := bbase (se 3 (by rfl) ⟨138119, by rfl⟩ : syracuseStep 736637 = 276239) (by norm_num)
theorem B736661 : Blo 487790 736661 := bbase (se 6 (by rfl) ⟨17265, by rfl⟩ : syracuseStep 736661 = 34531) (by norm_num)
theorem B1654181 : Blo 487790 1654181 := bbase (se 4 (by rfl) ⟨155079, by rfl⟩ : syracuseStep 1654181 = 310159) (by norm_num)
theorem B736685 : Blo 487790 736685 := bbase (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) (by norm_num)
theorem B736709 : Blo 487790 736709 := bbase (se 4 (by rfl) ⟨69066, by rfl⟩ : syracuseStep 736709 = 138133) (by norm_num)
theorem B736733 : Blo 487790 736733 := bbase (se 3 (by rfl) ⟨138137, by rfl⟩ : syracuseStep 736733 = 276275) (by norm_num)
theorem B736757 : Blo 487790 736757 := bbase (se 5 (by rfl) ⟨34535, by rfl⟩ : syracuseStep 736757 = 69071) (by norm_num)
theorem B736781 : Blo 487790 736781 := bbase (se 3 (by rfl) ⟨138146, by rfl⟩ : syracuseStep 736781 = 276293) (by norm_num)
theorem B736805 : Blo 487790 736805 := bbase (se 4 (by rfl) ⟨69075, by rfl⟩ : syracuseStep 736805 = 138151) (by norm_num)
theorem B736829 : Blo 487790 736829 := bbase (se 3 (by rfl) ⟨138155, by rfl⟩ : syracuseStep 736829 = 276311) (by norm_num)
theorem B736853 : Blo 487790 736853 := bbase (se 8 (by rfl) ⟨4317, by rfl⟩ : syracuseStep 736853 = 8635) (by norm_num)
theorem B736877 : Blo 487790 736877 := bbase (se 3 (by rfl) ⟨138164, by rfl⟩ : syracuseStep 736877 = 276329) (by norm_num)
theorem B736901 : Blo 487790 736901 := bbase (se 4 (by rfl) ⟨69084, by rfl⟩ : syracuseStep 736901 = 138169) (by norm_num)
theorem B736925 : Blo 487790 736925 := bbase (se 3 (by rfl) ⟨138173, by rfl⟩ : syracuseStep 736925 = 276347) (by norm_num)
theorem B736949 : Blo 487790 736949 := bbase (se 5 (by rfl) ⟨34544, by rfl⟩ : syracuseStep 736949 = 69089) (by norm_num)
theorem B736973 : Blo 487790 736973 := bbase (se 3 (by rfl) ⟨138182, by rfl⟩ : syracuseStep 736973 = 276365) (by norm_num)
theorem B1261261 : Blo 487790 1261261 := bbase (se 3 (by rfl) ⟨236486, by rfl⟩ : syracuseStep 1261261 = 472973) (by norm_num)
theorem B736997 : Blo 487790 736997 := bbase (se 4 (by rfl) ⟨69093, by rfl⟩ : syracuseStep 736997 = 138187) (by norm_num)
theorem B737021 : Blo 487790 737021 := bbase (se 3 (by rfl) ⟨138191, by rfl⟩ : syracuseStep 737021 = 276383) (by norm_num)
theorem B737045 : Blo 487790 737045 := bbase (se 6 (by rfl) ⟨17274, by rfl⟩ : syracuseStep 737045 = 34549) (by norm_num)
theorem B737069 : Blo 487790 737069 := bbase (se 3 (by rfl) ⟨138200, by rfl⟩ : syracuseStep 737069 = 276401) (by norm_num)
theorem B638777 : Blo 487790 638777 := bbase (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) (by norm_num)
theorem B737093 : Blo 487790 737093 := bbase (se 4 (by rfl) ⟨69102, by rfl⟩ : syracuseStep 737093 = 138205) (by norm_num)
theorem B1097549 : Blo 487790 1097549 := bbase (se 3 (by rfl) ⟨205790, by rfl⟩ : syracuseStep 1097549 = 411581) (by norm_num)
theorem B1654613 : Blo 487790 1654613 := bbase (se 9 (by rfl) ⟨4847, by rfl⟩ : syracuseStep 1654613 = 9695) (by norm_num)
theorem B737117 : Blo 487790 737117 := bbase (se 3 (by rfl) ⟨138209, by rfl⟩ : syracuseStep 737117 = 276419) (by norm_num)
theorem B737141 : Blo 487790 737141 := bbase (se 5 (by rfl) ⟨34553, by rfl⟩ : syracuseStep 737141 = 69107) (by norm_num)
theorem B737165 : Blo 487790 737165 := bbase (se 3 (by rfl) ⟨138218, by rfl⟩ : syracuseStep 737165 = 276437) (by norm_num)
theorem B1097621 : Blo 487790 1097621 := bbase (se 6 (by rfl) ⟨25725, by rfl⟩ : syracuseStep 1097621 = 51451) (by norm_num)
theorem B737189 : Blo 487790 737189 := bbase (se 4 (by rfl) ⟨69111, by rfl⟩ : syracuseStep 737189 = 138223) (by norm_num)
theorem B737213 : Blo 487790 737213 := bbase (se 3 (by rfl) ⟨138227, by rfl⟩ : syracuseStep 737213 = 276455) (by norm_num)
theorem B737237 : Blo 487790 737237 := bbase (se 7 (by rfl) ⟨8639, by rfl⟩ : syracuseStep 737237 = 17279) (by norm_num)
theorem B1097693 : Blo 487790 1097693 := bbase (se 3 (by rfl) ⟨205817, by rfl⟩ : syracuseStep 1097693 = 411635) (by norm_num)
theorem B737261 : Blo 487790 737261 := bbase (se 3 (by rfl) ⟨138236, by rfl⟩ : syracuseStep 737261 = 276473) (by norm_num)
theorem B737285 : Blo 487790 737285 := bbase (se 4 (by rfl) ⟨69120, by rfl⟩ : syracuseStep 737285 = 138241) (by norm_num)
theorem B737309 : Blo 487790 737309 := bbase (se 3 (by rfl) ⟨138245, by rfl⟩ : syracuseStep 737309 = 276491) (by norm_num)
theorem B1097765 : Blo 487790 1097765 := bbase (se 4 (by rfl) ⟨102915, by rfl⟩ : syracuseStep 1097765 = 205831) (by norm_num)
theorem B737333 : Blo 487790 737333 := bbase (se 5 (by rfl) ⟨34562, by rfl⟩ : syracuseStep 737333 = 69125) (by norm_num)
theorem B1392709 : Blo 487790 1392709 := bbase (se 4 (by rfl) ⟨130566, by rfl⟩ : syracuseStep 1392709 = 261133) (by norm_num)
theorem B835661 : Blo 487790 835661 := bbase (se 3 (by rfl) ⟨156686, by rfl⟩ : syracuseStep 835661 = 313373) (by norm_num)
theorem B737357 : Blo 487790 737357 := bbase (se 3 (by rfl) ⟨138254, by rfl⟩ : syracuseStep 737357 = 276509) (by norm_num)
theorem B737381 : Blo 487790 737381 := bbase (se 4 (by rfl) ⟨69129, by rfl⟩ : syracuseStep 737381 = 138259) (by norm_num)
theorem B1097837 : Blo 487790 1097837 := bbase (se 3 (by rfl) ⟨205844, by rfl⟩ : syracuseStep 1097837 = 411689) (by norm_num)
theorem B737405 : Blo 487790 737405 := bbase (se 3 (by rfl) ⟨138263, by rfl⟩ : syracuseStep 737405 = 276527) (by norm_num)
theorem B737429 : Blo 487790 737429 := bbase (se 6 (by rfl) ⟨17283, by rfl⟩ : syracuseStep 737429 = 34567) (by norm_num)
theorem B737453 : Blo 487790 737453 := bbase (se 3 (by rfl) ⟨138272, by rfl⟩ : syracuseStep 737453 = 276545) (by norm_num)
theorem B1097909 : Blo 487790 1097909 := bbase (se 5 (by rfl) ⟨51464, by rfl⟩ : syracuseStep 1097909 = 102929) (by norm_num)
theorem B737477 : Blo 487790 737477 := bbase (se 4 (by rfl) ⟨69138, by rfl⟩ : syracuseStep 737477 = 138277) (by norm_num)
theorem B737501 : Blo 487790 737501 := bbase (se 3 (by rfl) ⟨138281, by rfl⟩ : syracuseStep 737501 = 276563) (by norm_num)
theorem B1392869 : Blo 487790 1392869 := bbase (se 4 (by rfl) ⟨130581, by rfl⟩ : syracuseStep 1392869 = 261163) (by norm_num)
theorem B737525 : Blo 487790 737525 := bbase (se 5 (by rfl) ⟨34571, by rfl⟩ : syracuseStep 737525 = 69143) (by norm_num)
theorem B1097981 : Blo 487790 1097981 := bbase (se 3 (by rfl) ⟨205871, by rfl⟩ : syracuseStep 1097981 = 411743) (by norm_num)
theorem B1655045 : Blo 487790 1655045 := bbase (se 4 (by rfl) ⟨155160, by rfl⟩ : syracuseStep 1655045 = 310321) (by norm_num)
theorem B737549 : Blo 487790 737549 := bbase (se 3 (by rfl) ⟨138290, by rfl⟩ : syracuseStep 737549 = 276581) (by norm_num)
theorem B737573 : Blo 487790 737573 := bbase (se 4 (by rfl) ⟨69147, by rfl⟩ : syracuseStep 737573 = 138295) (by norm_num)
theorem B737597 : Blo 487790 737597 := bbase (se 3 (by rfl) ⟨138299, by rfl⟩ : syracuseStep 737597 = 276599) (by norm_num)
theorem B1098053 : Blo 487790 1098053 := bbase (se 4 (by rfl) ⟨102942, by rfl⟩ : syracuseStep 1098053 = 205885) (by norm_num)
theorem B737621 : Blo 487790 737621 := bbase (se 10 (by rfl) ⟨1080, by rfl⟩ : syracuseStep 737621 = 2161) (by norm_num)
theorem B737645 : Blo 487790 737645 := bbase (se 3 (by rfl) ⟨138308, by rfl⟩ : syracuseStep 737645 = 276617) (by norm_num)
theorem B737669 : Blo 487790 737669 := bbase (se 4 (by rfl) ⟨69156, by rfl⟩ : syracuseStep 737669 = 138313) (by norm_num)
theorem B1098125 : Blo 487790 1098125 := bbase (se 3 (by rfl) ⟨205898, by rfl⟩ : syracuseStep 1098125 = 411797) (by norm_num)
theorem B1130917 : Blo 487790 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B1098197 : Blo 487790 1098197 := bbase (se 7 (by rfl) ⟨12869, by rfl⟩ : syracuseStep 1098197 = 25739) (by norm_num)
theorem B1393109 : Blo 487790 1393109 := bbase (se 7 (by rfl) ⟨16325, by rfl⟩ : syracuseStep 1393109 = 32651) (by norm_num)
theorem B1098269 : Blo 487790 1098269 := bbase (se 3 (by rfl) ⟨205925, by rfl⟩ : syracuseStep 1098269 = 411851) (by norm_num)
theorem B2474549 : Blo 487790 2474549 := bbase (se 5 (by rfl) ⟨115994, by rfl⟩ : syracuseStep 2474549 = 231989) (by norm_num)
theorem B1098341 : Blo 487790 1098341 := bbase (se 4 (by rfl) ⟨102969, by rfl⟩ : syracuseStep 1098341 = 205939) (by norm_num)
theorem B606853 : Blo 487790 606853 := bbase (se 4 (by rfl) ⟨56892, by rfl⟩ : syracuseStep 606853 = 113785) (by norm_num)
theorem B1393301 : Blo 487790 1393301 := bbase (se 6 (by rfl) ⟨32655, by rfl⟩ : syracuseStep 1393301 = 65311) (by norm_num)
theorem B1098413 : Blo 487790 1098413 := bbase (se 3 (by rfl) ⟨205952, by rfl⟩ : syracuseStep 1098413 = 411905) (by norm_num)
theorem B1852085 : Blo 487790 1852085 := bbase (se 5 (by rfl) ⟨86816, by rfl⟩ : syracuseStep 1852085 = 173633) (by norm_num)
theorem B1655477 : Blo 487790 1655477 := bbase (se 5 (by rfl) ⟨77600, by rfl⟩ : syracuseStep 1655477 = 155201) (by norm_num)
theorem B1098485 : Blo 487790 1098485 := bbase (se 5 (by rfl) ⟨51491, by rfl⟩ : syracuseStep 1098485 = 102983) (by norm_num)
theorem B1884917 : Blo 487790 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B1098557 : Blo 487790 1098557 := bbase (se 3 (by rfl) ⟨205979, by rfl⟩ : syracuseStep 1098557 = 411959) (by norm_num)
theorem B1098629 : Blo 487790 1098629 := bbase (se 4 (by rfl) ⟨102996, by rfl⟩ : syracuseStep 1098629 = 205993) (by norm_num)
theorem B1098701 : Blo 487790 1098701 := bbase (se 3 (by rfl) ⟨206006, by rfl⟩ : syracuseStep 1098701 = 412013) (by norm_num)
theorem B1098773 : Blo 487790 1098773 := bbase (se 6 (by rfl) ⟨25752, by rfl⟩ : syracuseStep 1098773 = 51505) (by norm_num)
theorem B1098845 : Blo 487790 1098845 := bbase (se 3 (by rfl) ⟨206033, by rfl⟩ : syracuseStep 1098845 = 412067) (by norm_num)
theorem B1655909 : Blo 487790 1655909 := bbase (se 4 (by rfl) ⟨155241, by rfl⟩ : syracuseStep 1655909 = 310483) (by norm_num)
theorem B1098917 : Blo 487790 1098917 := bbase (se 4 (by rfl) ⟨103023, by rfl⟩ : syracuseStep 1098917 = 206047) (by norm_num)
theorem B1098989 : Blo 487790 1098989 := bbase (se 3 (by rfl) ⟨206060, by rfl⟩ : syracuseStep 1098989 = 412121) (by norm_num)
theorem B4179221 : Blo 487790 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B1099061 : Blo 487790 1099061 := bbase (se 5 (by rfl) ⟨51518, by rfl⟩ : syracuseStep 1099061 = 103037) (by norm_num)
theorem B2344277 : Blo 487790 2344277 := bbase (se 12 (by rfl) ⟨858, by rfl⟩ : syracuseStep 2344277 = 1717) (by norm_num)
theorem B1099133 : Blo 487790 1099133 := bbase (se 3 (by rfl) ⟨206087, by rfl⟩ : syracuseStep 1099133 = 412175) (by norm_num)
theorem B705925 : Blo 487790 705925 := bbase (se 4 (by rfl) ⟨66180, by rfl⟩ : syracuseStep 705925 = 132361) (by norm_num)
theorem B1099205 : Blo 487790 1099205 := bbase (se 4 (by rfl) ⟨103050, by rfl⟩ : syracuseStep 1099205 = 206101) (by norm_num)
theorem B1099277 : Blo 487790 1099277 := bbase (se 3 (by rfl) ⟨206114, by rfl⟩ : syracuseStep 1099277 = 412229) (by norm_num)
theorem B1656341 : Blo 487790 1656341 := bbase (se 6 (by rfl) ⟨38820, by rfl⟩ : syracuseStep 1656341 = 77641) (by norm_num)
theorem B1099349 : Blo 487790 1099349 := bbase (se 8 (by rfl) ⟨6441, by rfl⟩ : syracuseStep 1099349 = 12883) (by norm_num)
theorem B1394293 : Blo 487790 1394293 := bbase (se 5 (by rfl) ⟨65357, by rfl⟩ : syracuseStep 1394293 = 130715) (by norm_num)
theorem B1099421 : Blo 487790 1099421 := bbase (se 3 (by rfl) ⟨206141, by rfl⟩ : syracuseStep 1099421 = 412283) (by norm_num)
theorem B1492661 : Blo 487790 1492661 := bbase (se 5 (by rfl) ⟨69968, by rfl⟩ : syracuseStep 1492661 = 139937) (by norm_num)
theorem B1099493 : Blo 487790 1099493 := bbase (se 4 (by rfl) ⟨103077, by rfl⟩ : syracuseStep 1099493 = 206155) (by norm_num)
theorem B1099565 : Blo 487790 1099565 := bbase (se 3 (by rfl) ⟨206168, by rfl⟩ : syracuseStep 1099565 = 412337) (by norm_num)
theorem B2475845 : Blo 487790 2475845 := bbase (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) (by norm_num)
theorem B1099637 : Blo 487790 1099637 := bbase (se 5 (by rfl) ⟨51545, by rfl⟩ : syracuseStep 1099637 = 103091) (by norm_num)
theorem B1099709 : Blo 487790 1099709 := bbase (se 3 (by rfl) ⟨206195, by rfl⟩ : syracuseStep 1099709 = 412391) (by norm_num)
theorem B1656773 : Blo 487790 1656773 := bbase (se 4 (by rfl) ⟨155322, by rfl⟩ : syracuseStep 1656773 = 310645) (by norm_num)
theorem B1099781 : Blo 487790 1099781 := bbase (se 4 (by rfl) ⟨103104, by rfl⟩ : syracuseStep 1099781 = 206209) (by norm_num)
theorem B1099853 : Blo 487790 1099853 := bbase (se 3 (by rfl) ⟨206222, by rfl⟩ : syracuseStep 1099853 = 412445) (by norm_num)
theorem B3721301 : Blo 487790 3721301 := bbase (se 8 (by rfl) ⟨21804, by rfl⟩ : syracuseStep 3721301 = 43609) (by norm_num)
theorem B1099925 : Blo 487790 1099925 := bbase (se 6 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 1099925 = 51559) (by norm_num)
theorem B5556437 : Blo 487790 5556437 := bbase (se 7 (by rfl) ⟨65114, by rfl⟩ : syracuseStep 5556437 = 130229) (by norm_num)
theorem B1099997 : Blo 487790 1099997 := bbase (se 3 (by rfl) ⟨206249, by rfl⟩ : syracuseStep 1099997 = 412499) (by norm_num)
theorem B1100069 : Blo 487790 1100069 := bbase (se 4 (by rfl) ⟨103131, by rfl⟩ : syracuseStep 1100069 = 206263) (by norm_num)
theorem B1100141 : Blo 487790 1100141 := bbase (se 3 (by rfl) ⟨206276, by rfl⟩ : syracuseStep 1100141 = 412553) (by norm_num)
theorem B1657205 : Blo 487790 1657205 := bbase (se 5 (by rfl) ⟨77681, by rfl⟩ : syracuseStep 1657205 = 155363) (by norm_num)
theorem B1886597 : Blo 487790 1886597 := bbase (se 4 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 1886597 = 353737) (by norm_num)
theorem B575905 : Blo 487790 575905 := bbase (se 2 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 575905 = 431929) (by norm_num)
theorem B1100213 : Blo 487790 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B1100285 : Blo 487790 1100285 := bbase (se 3 (by rfl) ⟨206303, by rfl⟩ : syracuseStep 1100285 = 412607) (by norm_num)
theorem B1100357 : Blo 487790 1100357 := bbase (se 4 (by rfl) ⟨103158, by rfl⟩ : syracuseStep 1100357 = 206317) (by norm_num)
theorem B707149 : Blo 487790 707149 := bbase (se 3 (by rfl) ⟨132590, by rfl⟩ : syracuseStep 707149 = 265181) (by norm_num)
theorem B510557 : Blo 487790 510557 := bbase (se 3 (by rfl) ⟨95729, by rfl⟩ : syracuseStep 510557 = 191459) (by norm_num)
theorem B1100429 : Blo 487790 1100429 := bbase (se 3 (by rfl) ⟨206330, by rfl⟩ : syracuseStep 1100429 = 412661) (by norm_num)
theorem B1395397 : Blo 487790 1395397 := bbase (se 4 (by rfl) ⟨130818, by rfl⟩ : syracuseStep 1395397 = 261637) (by norm_num)
theorem B1100501 : Blo 487790 1100501 := bbase (se 7 (by rfl) ⟨12896, by rfl⟩ : syracuseStep 1100501 = 25793) (by norm_num)
theorem B1854197 : Blo 487790 1854197 := bbase (se 5 (by rfl) ⟨86915, by rfl⟩ : syracuseStep 1854197 = 173831) (by norm_num)
theorem B1100573 : Blo 487790 1100573 := bbase (se 3 (by rfl) ⟨206357, by rfl⟩ : syracuseStep 1100573 = 412715) (by norm_num)
theorem B1657637 : Blo 487790 1657637 := bbase (se 4 (by rfl) ⟨155403, by rfl⟩ : syracuseStep 1657637 = 310807) (by norm_num)
theorem B1100645 : Blo 487790 1100645 := bbase (se 4 (by rfl) ⟨103185, by rfl⟩ : syracuseStep 1100645 = 206371) (by norm_num)
theorem B1100717 : Blo 487790 1100717 := bbase (se 3 (by rfl) ⟨206384, by rfl⟩ : syracuseStep 1100717 = 412769) (by norm_num)
theorem B1100789 : Blo 487790 1100789 := bbase (se 5 (by rfl) ⟨51599, by rfl⟩ : syracuseStep 1100789 = 103199) (by norm_num)
theorem B1854485 : Blo 487790 1854485 := bbase (se 6 (by rfl) ⟨43464, by rfl⟩ : syracuseStep 1854485 = 86929) (by norm_num)
theorem B1100861 : Blo 487790 1100861 := bbase (se 3 (by rfl) ⟨206411, by rfl⟩ : syracuseStep 1100861 = 412823) (by norm_num)
theorem B2477141 : Blo 487790 2477141 := bbase (se 8 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 2477141 = 29029) (by norm_num)
theorem B1100933 : Blo 487790 1100933 := bbase (se 4 (by rfl) ⟨103212, by rfl⟩ : syracuseStep 1100933 = 206425) (by norm_num)
theorem B1101005 : Blo 487790 1101005 := bbase (se 3 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 1101005 = 412877) (by norm_num)
theorem B1658069 : Blo 487790 1658069 := bbase (se 7 (by rfl) ⟨19430, by rfl⟩ : syracuseStep 1658069 = 38861) (by norm_num)
theorem B1101077 : Blo 487790 1101077 := bbase (se 6 (by rfl) ⟨25806, by rfl⟩ : syracuseStep 1101077 = 51613) (by norm_num)
theorem B1101149 : Blo 487790 1101149 := bbase (se 3 (by rfl) ⟨206465, by rfl⟩ : syracuseStep 1101149 = 412931) (by norm_num)
theorem B1494389 : Blo 487790 1494389 := bbase (se 5 (by rfl) ⟨70049, by rfl⟩ : syracuseStep 1494389 = 140099) (by norm_num)
theorem B1101221 : Blo 487790 1101221 := bbase (se 4 (by rfl) ⟨103239, by rfl⟩ : syracuseStep 1101221 = 206479) (by norm_num)
theorem B1101293 : Blo 487790 1101293 := bbase (se 3 (by rfl) ⟨206492, by rfl⟩ : syracuseStep 1101293 = 412985) (by norm_num)
theorem B1101365 : Blo 487790 1101365 := bbase (se 5 (by rfl) ⟨51626, by rfl⟩ : syracuseStep 1101365 = 103253) (by norm_num)
theorem B1101437 : Blo 487790 1101437 := bbase (se 3 (by rfl) ⟨206519, by rfl⟩ : syracuseStep 1101437 = 413039) (by norm_num)
theorem B1658501 : Blo 487790 1658501 := bbase (se 4 (by rfl) ⟨155484, by rfl⟩ : syracuseStep 1658501 = 310969) (by norm_num)
theorem B708277 : Blo 487790 708277 := bbase (se 5 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 708277 = 66401) (by norm_num)
theorem B1101509 : Blo 487790 1101509 := bbase (se 4 (by rfl) ⟨103266, by rfl⟩ : syracuseStep 1101509 = 206533) (by norm_num)
theorem B1101581 : Blo 487790 1101581 := bbase (se 3 (by rfl) ⟨206546, by rfl⟩ : syracuseStep 1101581 = 413093) (by norm_num)
theorem B1101653 : Blo 487790 1101653 := bbase (se 9 (by rfl) ⟨3227, by rfl⟩ : syracuseStep 1101653 = 6455) (by norm_num)
theorem B1101725 : Blo 487790 1101725 := bbase (se 3 (by rfl) ⟨206573, by rfl⟩ : syracuseStep 1101725 = 413147) (by norm_num)
theorem B1101797 : Blo 487790 1101797 := bbase (se 4 (by rfl) ⟨103293, by rfl⟩ : syracuseStep 1101797 = 206587) (by norm_num)
theorem B1101869 : Blo 487790 1101869 := bbase (se 3 (by rfl) ⟨206600, by rfl⟩ : syracuseStep 1101869 = 413201) (by norm_num)
theorem B1658933 : Blo 487790 1658933 := bbase (se 5 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 1658933 = 155525) (by norm_num)
theorem B1101941 : Blo 487790 1101941 := bbase (se 5 (by rfl) ⟨51653, by rfl⟩ : syracuseStep 1101941 = 103307) (by norm_num)
theorem B2871413 : Blo 487790 2871413 := bbase (se 5 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 2871413 = 269195) (by norm_num)
theorem B1396901 : Blo 487790 1396901 := bbase (se 4 (by rfl) ⟨130959, by rfl⟩ : syracuseStep 1396901 = 261919) (by norm_num)
theorem B1855669 : Blo 487790 1855669 := bbase (se 5 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 1855669 = 173969) (by norm_num)
theorem B1102013 : Blo 487790 1102013 := bbase (se 3 (by rfl) ⟨206627, by rfl⟩ : syracuseStep 1102013 = 413255) (by norm_num)
theorem B1102085 : Blo 487790 1102085 := bbase (se 4 (by rfl) ⟨103320, by rfl⟩ : syracuseStep 1102085 = 206641) (by norm_num)
theorem B3232021 : Blo 487790 3232021 := bbase (se 6 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 3232021 = 151501) (by norm_num)
theorem B3985685 : Blo 487790 3985685 := bbase (se 6 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 3985685 = 186829) (by norm_num)
theorem B1102157 : Blo 487790 1102157 := bbase (se 3 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 1102157 = 413309) (by norm_num)
theorem B2478437 : Blo 487790 2478437 := bbase (se 4 (by rfl) ⟨232353, by rfl⟩ : syracuseStep 2478437 = 464707) (by norm_num)
theorem B840061 : Blo 487790 840061 := bbase (se 3 (by rfl) ⟨157511, by rfl⟩ : syracuseStep 840061 = 315023) (by norm_num)
theorem B708997 : Blo 487790 708997 := bbase (se 4 (by rfl) ⟨66468, by rfl⟩ : syracuseStep 708997 = 132937) (by norm_num)
theorem B1102229 : Blo 487790 1102229 := bbase (se 6 (by rfl) ⟨25833, by rfl⟩ : syracuseStep 1102229 = 51667) (by norm_num)
theorem B1102301 : Blo 487790 1102301 := bbase (se 3 (by rfl) ⟨206681, by rfl⟩ : syracuseStep 1102301 = 413363) (by norm_num)
theorem B1855973 : Blo 487790 1855973 := bbase (se 4 (by rfl) ⟨173997, by rfl⟩ : syracuseStep 1855973 = 347995) (by norm_num)
theorem B1659365 : Blo 487790 1659365 := bbase (se 4 (by rfl) ⟨155565, by rfl⟩ : syracuseStep 1659365 = 311131) (by norm_num)
theorem B1102373 : Blo 487790 1102373 := bbase (se 4 (by rfl) ⟨103347, by rfl⟩ : syracuseStep 1102373 = 206695) (by norm_num)
theorem B1102445 : Blo 487790 1102445 := bbase (se 3 (by rfl) ⟨206708, by rfl⟩ : syracuseStep 1102445 = 413417) (by norm_num)
theorem B1102517 : Blo 487790 1102517 := bbase (se 5 (by rfl) ⟨51680, by rfl⟩ : syracuseStep 1102517 = 103361) (by norm_num)
theorem B742085 : Blo 487790 742085 := bbase (se 4 (by rfl) ⟨69570, by rfl⟩ : syracuseStep 742085 = 139141) (by norm_num)
theorem B1102589 : Blo 487790 1102589 := bbase (se 3 (by rfl) ⟨206735, by rfl⟩ : syracuseStep 1102589 = 413471) (by norm_num)
theorem B2347813 : Blo 487790 2347813 := bbase (se 4 (by rfl) ⟨220107, by rfl⟩ : syracuseStep 2347813 = 440215) (by norm_num)
theorem B1102661 : Blo 487790 1102661 := bbase (se 4 (by rfl) ⟨103374, by rfl⟩ : syracuseStep 1102661 = 206749) (by norm_num)
theorem B1102733 : Blo 487790 1102733 := bbase (se 3 (by rfl) ⟨206762, by rfl⟩ : syracuseStep 1102733 = 413525) (by norm_num)
theorem B1102805 : Blo 487790 1102805 := bbase (se 7 (by rfl) ⟨12923, by rfl⟩ : syracuseStep 1102805 = 25847) (by norm_num)
theorem B1102877 : Blo 487790 1102877 := bbase (se 3 (by rfl) ⟨206789, by rfl⟩ : syracuseStep 1102877 = 413579) (by norm_num)
theorem B1102949 : Blo 487790 1102949 := bbase (se 4 (by rfl) ⟨103401, by rfl⟩ : syracuseStep 1102949 = 206803) (by norm_num)
theorem B939133 : Blo 487790 939133 := bbase (se 3 (by rfl) ⟨176087, by rfl⟩ : syracuseStep 939133 = 352175) (by norm_num)
theorem B1103021 : Blo 487790 1103021 := bbase (se 3 (by rfl) ⟨206816, by rfl⟩ : syracuseStep 1103021 = 413633) (by norm_num)
theorem B742621 : Blo 487790 742621 := bbase (se 3 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 742621 = 278483) (by norm_num)
theorem B1103093 : Blo 487790 1103093 := bbase (se 5 (by rfl) ⟨51707, by rfl⟩ : syracuseStep 1103093 = 103415) (by norm_num)
theorem B1758469 : Blo 487790 1758469 := bbase (se 4 (by rfl) ⟨164856, by rfl⟩ : syracuseStep 1758469 = 329713) (by norm_num)
theorem B3626293 : Blo 487790 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B1103165 : Blo 487790 1103165 := bbase (se 3 (by rfl) ⟨206843, by rfl⟩ : syracuseStep 1103165 = 413687) (by norm_num)
theorem B1103237 : Blo 487790 1103237 := bbase (se 4 (by rfl) ⟨103428, by rfl⟩ : syracuseStep 1103237 = 206857) (by norm_num)
theorem B1103309 : Blo 487790 1103309 := bbase (se 3 (by rfl) ⟨206870, by rfl⟩ : syracuseStep 1103309 = 413741) (by norm_num)
theorem B1103381 : Blo 487790 1103381 := bbase (se 6 (by rfl) ⟨25860, by rfl⟩ : syracuseStep 1103381 = 51721) (by norm_num)
theorem B1103453 : Blo 487790 1103453 := bbase (se 3 (by rfl) ⟨206897, by rfl⟩ : syracuseStep 1103453 = 413795) (by norm_num)
theorem B2479733 : Blo 487790 2479733 := bbase (se 5 (by rfl) ⟨116237, by rfl⟩ : syracuseStep 2479733 = 232475) (by norm_num)
theorem B1103525 : Blo 487790 1103525 := bbase (se 4 (by rfl) ⟨103455, by rfl⟩ : syracuseStep 1103525 = 206911) (by norm_num)
theorem B1398485 : Blo 487790 1398485 := bbase (se 7 (by rfl) ⟨16388, by rfl⟩ : syracuseStep 1398485 = 32777) (by norm_num)
theorem B1103597 : Blo 487790 1103597 := bbase (se 3 (by rfl) ⟨206924, by rfl⟩ : syracuseStep 1103597 = 413849) (by norm_num)
theorem B612145 : Blo 487790 612145 := bbase (se 2 (by rfl) ⟨229554, by rfl⟩ : syracuseStep 612145 = 459109) (by norm_num)
theorem B1103669 : Blo 487790 1103669 := bbase (se 5 (by rfl) ⟨51734, by rfl⟩ : syracuseStep 1103669 = 103469) (by norm_num)
theorem B1103741 : Blo 487790 1103741 := bbase (se 3 (by rfl) ⟨206951, by rfl⟩ : syracuseStep 1103741 = 413903) (by norm_num)
theorem B1234885 : Blo 487790 1234885 := bbase (se 4 (by rfl) ⟨115770, by rfl⟩ : syracuseStep 1234885 = 231541) (by norm_num)
theorem B1103813 : Blo 487790 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B1103885 : Blo 487790 1103885 := bbase (se 3 (by rfl) ⟨206978, by rfl⟩ : syracuseStep 1103885 = 413957) (by norm_num)
theorem B1234997 : Blo 487790 1234997 := bbase (se 5 (by rfl) ⟨57890, by rfl⟩ : syracuseStep 1234997 = 115781) (by norm_num)
theorem B1103957 : Blo 487790 1103957 := bbase (se 8 (by rfl) ⟨6468, by rfl⟩ : syracuseStep 1103957 = 12937) (by norm_num)
theorem B1104029 : Blo 487790 1104029 := bbase (se 3 (by rfl) ⟨207005, by rfl⟩ : syracuseStep 1104029 = 414011) (by norm_num)
theorem B1104101 : Blo 487790 1104101 := bbase (se 4 (by rfl) ⟨103509, by rfl⟩ : syracuseStep 1104101 = 207019) (by norm_num)
theorem B1235189 : Blo 487790 1235189 := bbase (se 5 (by rfl) ⟨57899, by rfl⟩ : syracuseStep 1235189 = 115799) (by norm_num)
theorem B1104173 : Blo 487790 1104173 := bbase (se 3 (by rfl) ⟨207032, by rfl⟩ : syracuseStep 1104173 = 414065) (by norm_num)
theorem B1431893 : Blo 487790 1431893 := bbase (se 10 (by rfl) ⟨2097, by rfl⟩ : syracuseStep 1431893 = 4195) (by norm_num)
theorem B1104245 : Blo 487790 1104245 := bbase (se 5 (by rfl) ⟨51761, by rfl⟩ : syracuseStep 1104245 = 103523) (by norm_num)
theorem B1399157 : Blo 487790 1399157 := bbase (se 5 (by rfl) ⟨65585, by rfl⟩ : syracuseStep 1399157 = 131171) (by norm_num)
theorem B1104317 : Blo 487790 1104317 := bbase (se 3 (by rfl) ⟨207059, by rfl⟩ : syracuseStep 1104317 = 414119) (by norm_num)
theorem B4708853 : Blo 487790 4708853 := bbase (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) (by norm_num)
theorem B1104389 : Blo 487790 1104389 := bbase (se 4 (by rfl) ⟨103536, by rfl⟩ : syracuseStep 1104389 = 207073) (by norm_num)
theorem B1858085 : Blo 487790 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B2087477 : Blo 487790 2087477 := bbase (se 5 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 2087477 = 195701) (by norm_num)
theorem B1235533 : Blo 487790 1235533 := bbase (se 3 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 1235533 = 463325) (by norm_num)
theorem B1104461 : Blo 487790 1104461 := bbase (se 3 (by rfl) ⟨207086, by rfl⟩ : syracuseStep 1104461 = 414173) (by norm_num)
theorem B1104533 : Blo 487790 1104533 := bbase (se 6 (by rfl) ⟨25887, by rfl⟩ : syracuseStep 1104533 = 51775) (by norm_num)
theorem B1235645 : Blo 487790 1235645 := bbase (se 3 (by rfl) ⟨231683, by rfl⟩ : syracuseStep 1235645 = 463367) (by norm_num)
theorem B1104605 : Blo 487790 1104605 := bbase (se 3 (by rfl) ⟨207113, by rfl⟩ : syracuseStep 1104605 = 414227) (by norm_num)
theorem B1104677 : Blo 487790 1104677 := bbase (se 4 (by rfl) ⟨103563, by rfl⟩ : syracuseStep 1104677 = 207127) (by norm_num)
theorem B1399589 : Blo 487790 1399589 := bbase (se 4 (by rfl) ⟨131211, by rfl⟩ : syracuseStep 1399589 = 262423) (by norm_num)
theorem B1858373 : Blo 487790 1858373 := bbase (se 4 (by rfl) ⟨174222, by rfl⟩ : syracuseStep 1858373 = 348445) (by norm_num)
theorem B2087765 : Blo 487790 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B1104749 : Blo 487790 1104749 := bbase (se 3 (by rfl) ⟨207140, by rfl⟩ : syracuseStep 1104749 = 414281) (by norm_num)
theorem B1235837 : Blo 487790 1235837 := bbase (se 3 (by rfl) ⟨231719, by rfl⟩ : syracuseStep 1235837 = 463439) (by norm_num)
theorem B2481029 : Blo 487790 2481029 := bbase (se 4 (by rfl) ⟨232596, by rfl⟩ : syracuseStep 2481029 = 465193) (by norm_num)
theorem B1104821 : Blo 487790 1104821 := bbase (se 5 (by rfl) ⟨51788, by rfl⟩ : syracuseStep 1104821 = 103577) (by norm_num)
theorem B1104893 : Blo 487790 1104893 := bbase (se 3 (by rfl) ⟨207167, by rfl⟩ : syracuseStep 1104893 = 414335) (by norm_num)
theorem B1104965 : Blo 487790 1104965 := bbase (se 4 (by rfl) ⟨103590, by rfl⟩ : syracuseStep 1104965 = 207181) (by norm_num)
theorem B1105037 : Blo 487790 1105037 := bbase (se 3 (by rfl) ⟨207194, by rfl⟩ : syracuseStep 1105037 = 414389) (by norm_num)
theorem B3529909 : Blo 487790 3529909 := bbase (se 5 (by rfl) ⟨165464, by rfl⟩ : syracuseStep 3529909 = 330929) (by norm_num)
theorem B1236181 : Blo 487790 1236181 := bbase (se 7 (by rfl) ⟨14486, by rfl⟩ : syracuseStep 1236181 = 28973) (by norm_num)
theorem B1105109 : Blo 487790 1105109 := bbase (se 7 (by rfl) ⟨12950, by rfl⟩ : syracuseStep 1105109 = 25901) (by norm_num)
theorem B1760501 : Blo 487790 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B744725 : Blo 487790 744725 := bbase (se 6 (by rfl) ⟨17454, by rfl⟩ : syracuseStep 744725 = 34909) (by norm_num)
theorem B1105181 : Blo 487790 1105181 := bbase (se 3 (by rfl) ⟨207221, by rfl⟩ : syracuseStep 1105181 = 414443) (by norm_num)
theorem B1236293 : Blo 487790 1236293 := bbase (se 4 (by rfl) ⟨115902, by rfl⟩ : syracuseStep 1236293 = 231805) (by norm_num)
theorem B13557077 : Blo 487790 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B1105253 : Blo 487790 1105253 := bbase (se 4 (by rfl) ⟨103617, by rfl⟩ : syracuseStep 1105253 = 207235) (by norm_num)
theorem B1105325 : Blo 487790 1105325 := bbase (se 3 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 1105325 = 414497) (by norm_num)
theorem B1105397 : Blo 487790 1105397 := bbase (se 5 (by rfl) ⟨51815, by rfl⟩ : syracuseStep 1105397 = 103631) (by norm_num)
theorem B1236485 : Blo 487790 1236485 := bbase (se 4 (by rfl) ⟨115920, by rfl⟩ : syracuseStep 1236485 = 231841) (by norm_num)
theorem B1400341 : Blo 487790 1400341 := bbase (se 6 (by rfl) ⟨32820, by rfl⟩ : syracuseStep 1400341 = 65641) (by norm_num)
theorem B1105469 : Blo 487790 1105469 := bbase (se 3 (by rfl) ⟨207275, by rfl⟩ : syracuseStep 1105469 = 414551) (by norm_num)
theorem B2088517 : Blo 487790 2088517 := bbase (se 4 (by rfl) ⟨195798, by rfl⟩ : syracuseStep 2088517 = 391597) (by norm_num)
theorem B1105541 : Blo 487790 1105541 := bbase (se 4 (by rfl) ⟨103644, by rfl⟩ : syracuseStep 1105541 = 207289) (by norm_num)
theorem B1105613 : Blo 487790 1105613 := bbase (se 3 (by rfl) ⟨207302, by rfl⟩ : syracuseStep 1105613 = 414605) (by norm_num)
theorem B3137237 : Blo 487790 3137237 := bbase (se 7 (by rfl) ⟨36764, by rfl⟩ : syracuseStep 3137237 = 73529) (by norm_num)
theorem B1105685 : Blo 487790 1105685 := bbase (se 6 (by rfl) ⟨25914, by rfl⟩ : syracuseStep 1105685 = 51829) (by norm_num)
theorem B1236829 : Blo 487790 1236829 := bbase (se 3 (by rfl) ⟨231905, by rfl⟩ : syracuseStep 1236829 = 463811) (by norm_num)
theorem B1105757 : Blo 487790 1105757 := bbase (se 3 (by rfl) ⟨207329, by rfl⟩ : syracuseStep 1105757 = 414659) (by norm_num)
theorem B1105829 : Blo 487790 1105829 := bbase (se 4 (by rfl) ⟨103671, by rfl⟩ : syracuseStep 1105829 = 207343) (by norm_num)
theorem B548797 : Blo 487790 548797 := bbase (se 3 (by rfl) ⟨102899, by rfl⟩ : syracuseStep 548797 = 205799) (by norm_num)
theorem B1236941 : Blo 487790 1236941 := bbase (se 3 (by rfl) ⟨231926, by rfl⟩ : syracuseStep 1236941 = 463853) (by norm_num)
theorem B548833 : Blo 487790 548833 := bbase (se 2 (by rfl) ⟨205812, by rfl⟩ : syracuseStep 548833 = 411625) (by norm_num)
theorem B1859557 : Blo 487790 1859557 := bbase (se 4 (by rfl) ⟨174333, by rfl⟩ : syracuseStep 1859557 = 348667) (by norm_num)
theorem B1105901 : Blo 487790 1105901 := bbase (se 3 (by rfl) ⟨207356, by rfl⟩ : syracuseStep 1105901 = 414713) (by norm_num)
theorem B548869 : Blo 487790 548869 := bbase (se 4 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 548869 = 102913) (by norm_num)
theorem B2154533 : Blo 487790 2154533 := bbase (se 4 (by rfl) ⟨201987, by rfl⟩ : syracuseStep 2154533 = 403975) (by norm_num)
theorem B548905 : Blo 487790 548905 := bbase (se 2 (by rfl) ⟨205839, by rfl⟩ : syracuseStep 548905 = 411679) (by norm_num)
theorem B1105973 : Blo 487790 1105973 := bbase (se 5 (by rfl) ⟨51842, by rfl⟩ : syracuseStep 1105973 = 103685) (by norm_num)
theorem B548941 : Blo 487790 548941 := bbase (se 3 (by rfl) ⟨102926, by rfl⟩ : syracuseStep 548941 = 205853) (by norm_num)
theorem B548977 : Blo 487790 548977 := bbase (se 2 (by rfl) ⟨205866, by rfl⟩ : syracuseStep 548977 = 411733) (by norm_num)
theorem B1106045 : Blo 487790 1106045 := bbase (se 3 (by rfl) ⟨207383, by rfl⟩ : syracuseStep 1106045 = 414767) (by norm_num)
theorem B1237133 : Blo 487790 1237133 := bbase (se 3 (by rfl) ⟨231962, by rfl⟩ : syracuseStep 1237133 = 463925) (by norm_num)
theorem B549013 : Blo 487790 549013 := bbase (se 6 (by rfl) ⟨12867, by rfl⟩ : syracuseStep 549013 = 25735) (by norm_num)
theorem B2482325 : Blo 487790 2482325 := bbase (se 6 (by rfl) ⟨58179, by rfl⟩ : syracuseStep 2482325 = 116359) (by norm_num)
theorem B549049 : Blo 487790 549049 := bbase (se 2 (by rfl) ⟨205893, by rfl⟩ : syracuseStep 549049 = 411787) (by norm_num)
theorem B1106117 : Blo 487790 1106117 := bbase (se 4 (by rfl) ⟨103698, by rfl⟩ : syracuseStep 1106117 = 207397) (by norm_num)
theorem B549085 : Blo 487790 549085 := bbase (se 3 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 549085 = 205907) (by norm_num)
theorem B549121 : Blo 487790 549121 := bbase (se 2 (by rfl) ⟨205920, by rfl⟩ : syracuseStep 549121 = 411841) (by norm_num)
theorem B1106189 : Blo 487790 1106189 := bbase (se 3 (by rfl) ⟨207410, by rfl⟩ : syracuseStep 1106189 = 414821) (by norm_num)
theorem B1859861 : Blo 487790 1859861 := bbase (se 6 (by rfl) ⟨43590, by rfl⟩ : syracuseStep 1859861 = 87181) (by norm_num)
theorem B549157 : Blo 487790 549157 := bbase (se 4 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 549157 = 102967) (by norm_num)
theorem B2089253 : Blo 487790 2089253 := bbase (se 4 (by rfl) ⟨195867, by rfl⟩ : syracuseStep 2089253 = 391735) (by norm_num)
theorem B2351429 : Blo 487790 2351429 := bbase (se 4 (by rfl) ⟨220446, by rfl⟩ : syracuseStep 2351429 = 440893) (by norm_num)
theorem B549193 : Blo 487790 549193 := bbase (se 2 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 549193 = 411895) (by norm_num)
theorem B1106261 : Blo 487790 1106261 := bbase (se 10 (by rfl) ⟨1620, by rfl⟩ : syracuseStep 1106261 = 3241) (by norm_num)
theorem B549229 : Blo 487790 549229 := bbase (se 3 (by rfl) ⟨102980, by rfl⟩ : syracuseStep 549229 = 205961) (by norm_num)
theorem B549265 : Blo 487790 549265 := bbase (se 2 (by rfl) ⟨205974, by rfl⟩ : syracuseStep 549265 = 411949) (by norm_num)
theorem B1106333 : Blo 487790 1106333 := bbase (se 3 (by rfl) ⟨207437, by rfl⟩ : syracuseStep 1106333 = 414875) (by norm_num)
theorem B549301 : Blo 487790 549301 := bbase (se 5 (by rfl) ⟨25748, by rfl⟩ : syracuseStep 549301 = 51497) (by norm_num)
theorem B549337 : Blo 487790 549337 := bbase (se 2 (by rfl) ⟨206001, by rfl⟩ : syracuseStep 549337 = 412003) (by norm_num)
theorem B1237477 : Blo 487790 1237477 := bbase (se 4 (by rfl) ⟨116013, by rfl⟩ : syracuseStep 1237477 = 232027) (by norm_num)
theorem B1106405 : Blo 487790 1106405 := bbase (se 4 (by rfl) ⟨103725, by rfl⟩ : syracuseStep 1106405 = 207451) (by norm_num)
theorem B549373 : Blo 487790 549373 := bbase (se 3 (by rfl) ⟨103007, by rfl⟩ : syracuseStep 549373 = 206015) (by norm_num)
theorem B549409 : Blo 487790 549409 := bbase (se 2 (by rfl) ⟨206028, by rfl⟩ : syracuseStep 549409 = 412057) (by norm_num)
theorem B1106477 : Blo 487790 1106477 := bbase (se 3 (by rfl) ⟨207464, by rfl⟩ : syracuseStep 1106477 = 414929) (by norm_num)
theorem B549445 : Blo 487790 549445 := bbase (se 4 (by rfl) ⟨51510, by rfl⟩ : syracuseStep 549445 = 103021) (by norm_num)
theorem B1237589 : Blo 487790 1237589 := bbase (se 8 (by rfl) ⟨7251, by rfl⟩ : syracuseStep 1237589 = 14503) (by norm_num)
theorem B549481 : Blo 487790 549481 := bbase (se 2 (by rfl) ⟨206055, by rfl⟩ : syracuseStep 549481 = 412111) (by norm_num)
theorem B549517 : Blo 487790 549517 := bbase (se 3 (by rfl) ⟨103034, by rfl⟩ : syracuseStep 549517 = 206069) (by norm_num)
theorem B549553 : Blo 487790 549553 := bbase (se 2 (by rfl) ⟨206082, by rfl⟩ : syracuseStep 549553 = 412165) (by norm_num)
theorem B549589 : Blo 487790 549589 := bbase (se 7 (by rfl) ⟨6440, by rfl⟩ : syracuseStep 549589 = 12881) (by norm_num)
theorem B549625 : Blo 487790 549625 := bbase (se 2 (by rfl) ⟨206109, by rfl⟩ : syracuseStep 549625 = 412219) (by norm_num)
theorem B1237781 : Blo 487790 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B549661 : Blo 487790 549661 := bbase (se 3 (by rfl) ⟨103061, by rfl⟩ : syracuseStep 549661 = 206123) (by norm_num)
theorem B549697 : Blo 487790 549697 := bbase (se 2 (by rfl) ⟨206136, by rfl⟩ : syracuseStep 549697 = 412273) (by norm_num)
theorem B549733 : Blo 487790 549733 := bbase (se 4 (by rfl) ⟨51537, by rfl⟩ : syracuseStep 549733 = 103075) (by norm_num)
theorem B549769 : Blo 487790 549769 := bbase (se 2 (by rfl) ⟨206163, by rfl⟩ : syracuseStep 549769 = 412327) (by norm_num)
theorem B549805 : Blo 487790 549805 := bbase (se 3 (by rfl) ⟨103088, by rfl⟩ : syracuseStep 549805 = 206177) (by norm_num)
theorem B549841 : Blo 487790 549841 := bbase (se 2 (by rfl) ⟨206190, by rfl⟩ : syracuseStep 549841 = 412381) (by norm_num)
theorem B549877 : Blo 487790 549877 := bbase (se 5 (by rfl) ⟨25775, by rfl⟩ : syracuseStep 549877 = 51551) (by norm_num)
theorem B1172485 : Blo 487790 1172485 := bbase (se 4 (by rfl) ⟨109920, by rfl⟩ : syracuseStep 1172485 = 219841) (by norm_num)
theorem B549913 : Blo 487790 549913 := bbase (se 2 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 549913 = 412435) (by norm_num)
theorem B549949 : Blo 487790 549949 := bbase (se 3 (by rfl) ⟨103115, by rfl⟩ : syracuseStep 549949 = 206231) (by norm_num)
theorem B549985 : Blo 487790 549985 := bbase (se 2 (by rfl) ⟨206244, by rfl⟩ : syracuseStep 549985 = 412489) (by norm_num)
theorem B1238125 : Blo 487790 1238125 := bbase (se 3 (by rfl) ⟨232148, by rfl⟩ : syracuseStep 1238125 = 464297) (by norm_num)
theorem B550021 : Blo 487790 550021 := bbase (se 4 (by rfl) ⟨51564, by rfl⟩ : syracuseStep 550021 = 103129) (by norm_num)
theorem B4187285 : Blo 487790 4187285 := bbase (se 6 (by rfl) ⟨98139, by rfl⟩ : syracuseStep 4187285 = 196279) (by norm_num)
theorem B550057 : Blo 487790 550057 := bbase (se 2 (by rfl) ⟨206271, by rfl⟩ : syracuseStep 550057 = 412543) (by norm_num)
theorem B550093 : Blo 487790 550093 := bbase (se 3 (by rfl) ⟨103142, by rfl⟩ : syracuseStep 550093 = 206285) (by norm_num)
theorem B1238237 : Blo 487790 1238237 := bbase (se 3 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 1238237 = 464339) (by norm_num)
theorem B550129 : Blo 487790 550129 := bbase (se 2 (by rfl) ⟨206298, by rfl⟩ : syracuseStep 550129 = 412597) (by norm_num)
theorem B550165 : Blo 487790 550165 := bbase (se 6 (by rfl) ⟨12894, by rfl⟩ : syracuseStep 550165 = 25789) (by norm_num)
theorem B2647349 : Blo 487790 2647349 := bbase (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) (by norm_num)
theorem B550201 : Blo 487790 550201 := bbase (se 2 (by rfl) ⟨206325, by rfl⟩ : syracuseStep 550201 = 412651) (by norm_num)
theorem B550237 : Blo 487790 550237 := bbase (se 3 (by rfl) ⟨103169, by rfl⟩ : syracuseStep 550237 = 206339) (by norm_num)
theorem B550273 : Blo 487790 550273 := bbase (se 2 (by rfl) ⟨206352, by rfl⟩ : syracuseStep 550273 = 412705) (by norm_num)
theorem B1238429 : Blo 487790 1238429 := bbase (se 3 (by rfl) ⟨232205, by rfl⟩ : syracuseStep 1238429 = 464411) (by norm_num)
theorem B550309 : Blo 487790 550309 := bbase (se 4 (by rfl) ⟨51591, by rfl⟩ : syracuseStep 550309 = 103183) (by norm_num)
theorem B2483621 : Blo 487790 2483621 := bbase (se 4 (by rfl) ⟨232839, by rfl⟩ : syracuseStep 2483621 = 465679) (by norm_num)
theorem B550345 : Blo 487790 550345 := bbase (se 2 (by rfl) ⟨206379, by rfl⟩ : syracuseStep 550345 = 412759) (by norm_num)
theorem B1041893 : Blo 487790 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B550381 : Blo 487790 550381 := bbase (se 3 (by rfl) ⟨103196, by rfl⟩ : syracuseStep 550381 = 206393) (by norm_num)
theorem B550417 : Blo 487790 550417 := bbase (se 2 (by rfl) ⟨206406, by rfl⟩ : syracuseStep 550417 = 412813) (by norm_num)
theorem B550453 : Blo 487790 550453 := bbase (se 5 (by rfl) ⟨25802, by rfl⟩ : syracuseStep 550453 = 51605) (by norm_num)
theorem B550489 : Blo 487790 550489 := bbase (se 2 (by rfl) ⟨206433, by rfl⟩ : syracuseStep 550489 = 412867) (by norm_num)
theorem B550525 : Blo 487790 550525 := bbase (se 3 (by rfl) ⟨103223, by rfl⟩ : syracuseStep 550525 = 206447) (by norm_num)
theorem B550561 : Blo 487790 550561 := bbase (se 2 (by rfl) ⟨206460, by rfl⟩ : syracuseStep 550561 = 412921) (by norm_num)
theorem B3729077 : Blo 487790 3729077 := bbase (se 5 (by rfl) ⟨174800, by rfl⟩ : syracuseStep 3729077 = 349601) (by norm_num)
theorem B550597 : Blo 487790 550597 := bbase (se 4 (by rfl) ⟨51618, by rfl⟩ : syracuseStep 550597 = 103237) (by norm_num)
theorem B550633 : Blo 487790 550633 := bbase (se 2 (by rfl) ⟨206487, by rfl⟩ : syracuseStep 550633 = 412975) (by norm_num)
theorem B1238773 : Blo 487790 1238773 := bbase (se 5 (by rfl) ⟨58067, by rfl⟩ : syracuseStep 1238773 = 116135) (by norm_num)
theorem B550669 : Blo 487790 550669 := bbase (se 3 (by rfl) ⟨103250, by rfl⟩ : syracuseStep 550669 = 206501) (by norm_num)
theorem B550705 : Blo 487790 550705 := bbase (se 2 (by rfl) ⟨206514, by rfl⟩ : syracuseStep 550705 = 413029) (by norm_num)
theorem B550741 : Blo 487790 550741 := bbase (se 9 (by rfl) ⟨1613, by rfl⟩ : syracuseStep 550741 = 3227) (by norm_num)
theorem B1238885 : Blo 487790 1238885 := bbase (se 4 (by rfl) ⟨116145, by rfl⟩ : syracuseStep 1238885 = 232291) (by norm_num)
theorem B550777 : Blo 487790 550777 := bbase (se 2 (by rfl) ⟨206541, by rfl⟩ : syracuseStep 550777 = 413083) (by norm_num)
theorem B747389 : Blo 487790 747389 := bbase (se 3 (by rfl) ⟨140135, by rfl⟩ : syracuseStep 747389 = 280271) (by norm_num)
theorem B550813 : Blo 487790 550813 := bbase (se 3 (by rfl) ⟨103277, by rfl⟩ : syracuseStep 550813 = 206555) (by norm_num)
theorem B550849 : Blo 487790 550849 := bbase (se 2 (by rfl) ⟨206568, by rfl⟩ : syracuseStep 550849 = 413137) (by norm_num)
theorem B550885 : Blo 487790 550885 := bbase (se 4 (by rfl) ⟨51645, by rfl⟩ : syracuseStep 550885 = 103291) (by norm_num)
theorem B550921 : Blo 487790 550921 := bbase (se 2 (by rfl) ⟨206595, by rfl⟩ : syracuseStep 550921 = 413191) (by norm_num)
theorem B1239077 : Blo 487790 1239077 := bbase (se 4 (by rfl) ⟨116163, by rfl⟩ : syracuseStep 1239077 = 232327) (by norm_num)
theorem B550957 : Blo 487790 550957 := bbase (se 3 (by rfl) ⟨103304, by rfl⟩ : syracuseStep 550957 = 206609) (by norm_num)
theorem B1566773 : Blo 487790 1566773 := bbase (se 5 (by rfl) ⟨73442, by rfl⟩ : syracuseStep 1566773 = 146885) (by norm_num)
theorem B550993 : Blo 487790 550993 := bbase (se 2 (by rfl) ⟨206622, by rfl⟩ : syracuseStep 550993 = 413245) (by norm_num)
theorem B551029 : Blo 487790 551029 := bbase (se 5 (by rfl) ⟨25829, by rfl⟩ : syracuseStep 551029 = 51659) (by norm_num)
theorem B2648213 : Blo 487790 2648213 := bbase (se 6 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 2648213 = 124135) (by norm_num)
theorem B551065 : Blo 487790 551065 := bbase (se 2 (by rfl) ⟨206649, by rfl⟩ : syracuseStep 551065 = 413299) (by norm_num)
theorem B2353333 : Blo 487790 2353333 := bbase (se 5 (by rfl) ⟨110312, by rfl⟩ : syracuseStep 2353333 = 220625) (by norm_num)
theorem B551101 : Blo 487790 551101 := bbase (se 3 (by rfl) ⟨103331, by rfl⟩ : syracuseStep 551101 = 206663) (by norm_num)
theorem B2353349 : Blo 487790 2353349 := bbase (se 4 (by rfl) ⟨220626, by rfl⟩ : syracuseStep 2353349 = 441253) (by norm_num)
theorem B1042645 : Blo 487790 1042645 := bbase (se 7 (by rfl) ⟨12218, by rfl⟩ : syracuseStep 1042645 = 24437) (by norm_num)
theorem B551137 : Blo 487790 551137 := bbase (se 2 (by rfl) ⟨206676, by rfl⟩ : syracuseStep 551137 = 413353) (by norm_num)
theorem B551173 : Blo 487790 551173 := bbase (se 4 (by rfl) ⟨51672, by rfl⟩ : syracuseStep 551173 = 103345) (by norm_num)
theorem B551209 : Blo 487790 551209 := bbase (se 2 (by rfl) ⟨206703, by rfl⟩ : syracuseStep 551209 = 413407) (by norm_num)
theorem B551245 : Blo 487790 551245 := bbase (se 3 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 551245 = 206717) (by norm_num)
theorem B1861973 : Blo 487790 1861973 := bbase (se 10 (by rfl) ⟨2727, by rfl⟩ : syracuseStep 1861973 = 5455) (by norm_num)
theorem B1042789 : Blo 487790 1042789 := bbase (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) (by norm_num)
theorem B1173869 : Blo 487790 1173869 := bbase (se 3 (by rfl) ⟨220100, by rfl⟩ : syracuseStep 1173869 = 440201) (by norm_num)
theorem B551281 : Blo 487790 551281 := bbase (se 2 (by rfl) ⟨206730, by rfl⟩ : syracuseStep 551281 = 413461) (by norm_num)
theorem B1239421 : Blo 487790 1239421 := bbase (se 3 (by rfl) ⟨232391, by rfl⟩ : syracuseStep 1239421 = 464783) (by norm_num)
theorem B2779541 : Blo 487790 2779541 := bbase (se 6 (by rfl) ⟨65145, by rfl⟩ : syracuseStep 2779541 = 130291) (by norm_num)
theorem B551317 : Blo 487790 551317 := bbase (se 6 (by rfl) ⟨12921, by rfl⟩ : syracuseStep 551317 = 25843) (by norm_num)
theorem B551353 : Blo 487790 551353 := bbase (se 2 (by rfl) ⟨206757, by rfl⟩ : syracuseStep 551353 = 413515) (by norm_num)
theorem B551389 : Blo 487790 551389 := bbase (se 3 (by rfl) ⟨103385, by rfl⟩ : syracuseStep 551389 = 206771) (by norm_num)
theorem B1239533 : Blo 487790 1239533 := bbase (se 3 (by rfl) ⟨232412, by rfl⟩ : syracuseStep 1239533 = 464825) (by norm_num)
theorem B551425 : Blo 487790 551425 := bbase (se 2 (by rfl) ⟨206784, by rfl⟩ : syracuseStep 551425 = 413569) (by norm_num)
theorem B551461 : Blo 487790 551461 := bbase (se 4 (by rfl) ⟨51699, by rfl⟩ : syracuseStep 551461 = 103399) (by norm_num)
theorem B1174061 : Blo 487790 1174061 := bbase (se 3 (by rfl) ⟨220136, by rfl⟩ : syracuseStep 1174061 = 440273) (by norm_num)
theorem B551497 : Blo 487790 551497 := bbase (se 2 (by rfl) ⟨206811, by rfl⟩ : syracuseStep 551497 = 413623) (by norm_num)
theorem B551533 : Blo 487790 551533 := bbase (se 3 (by rfl) ⟨103412, by rfl⟩ : syracuseStep 551533 = 206825) (by norm_num)
theorem B1862261 : Blo 487790 1862261 := bbase (se 5 (by rfl) ⟨87293, by rfl⟩ : syracuseStep 1862261 = 174587) (by norm_num)
theorem B551569 : Blo 487790 551569 := bbase (se 2 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 551569 = 413677) (by norm_num)
theorem B1239725 : Blo 487790 1239725 := bbase (se 3 (by rfl) ⟨232448, by rfl⟩ : syracuseStep 1239725 = 464897) (by norm_num)
theorem B551605 : Blo 487790 551605 := bbase (se 5 (by rfl) ⟨25856, by rfl⟩ : syracuseStep 551605 = 51713) (by norm_num)
theorem B2484917 : Blo 487790 2484917 := bbase (se 5 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 2484917 = 232961) (by norm_num)
theorem B551641 : Blo 487790 551641 := bbase (se 2 (by rfl) ⟨206865, by rfl⟩ : syracuseStep 551641 = 413731) (by norm_num)
theorem B1043165 : Blo 487790 1043165 := bbase (se 3 (by rfl) ⟨195593, by rfl⟩ : syracuseStep 1043165 = 391187) (by norm_num)
theorem B551677 : Blo 487790 551677 := bbase (se 3 (by rfl) ⟨103439, by rfl⟩ : syracuseStep 551677 = 206879) (by norm_num)
theorem B551713 : Blo 487790 551713 := bbase (se 2 (by rfl) ⟨206892, by rfl⟩ : syracuseStep 551713 = 413785) (by norm_num)
theorem B551749 : Blo 487790 551749 := bbase (se 4 (by rfl) ⟨51726, by rfl⟩ : syracuseStep 551749 = 103453) (by norm_num)
theorem B551785 : Blo 487790 551785 := bbase (se 2 (by rfl) ⟨206919, by rfl⟩ : syracuseStep 551785 = 413839) (by norm_num)
theorem B551821 : Blo 487790 551821 := bbase (se 3 (by rfl) ⟨103466, by rfl⟩ : syracuseStep 551821 = 206933) (by norm_num)
theorem B617377 : Blo 487790 617377 := bbase (se 2 (by rfl) ⟨231516, by rfl⟩ : syracuseStep 617377 = 463033) (by norm_num)
theorem B551857 : Blo 487790 551857 := bbase (se 2 (by rfl) ⟨206946, by rfl⟩ : syracuseStep 551857 = 413893) (by norm_num)
theorem B1567669 : Blo 487790 1567669 := bbase (se 5 (by rfl) ⟨73484, by rfl⟩ : syracuseStep 1567669 = 146969) (by norm_num)
theorem B551893 : Blo 487790 551893 := bbase (se 7 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 551893 = 12935) (by norm_num)
theorem B879581 : Blo 487790 879581 := bbase (se 3 (by rfl) ⟨164921, by rfl⟩ : syracuseStep 879581 = 329843) (by norm_num)
theorem B551929 : Blo 487790 551929 := bbase (se 2 (by rfl) ⟨206973, by rfl⟩ : syracuseStep 551929 = 413947) (by norm_num)
theorem B617473 : Blo 487790 617473 := bbase (se 2 (by rfl) ⟨231552, by rfl⟩ : syracuseStep 617473 = 463105) (by norm_num)
theorem B1240069 : Blo 487790 1240069 := bbase (se 4 (by rfl) ⟨116256, by rfl⟩ : syracuseStep 1240069 = 232513) (by norm_num)
theorem B551965 : Blo 487790 551965 := bbase (se 3 (by rfl) ⟨103493, by rfl⟩ : syracuseStep 551965 = 206987) (by norm_num)
theorem B879653 : Blo 487790 879653 := bbase (se 4 (by rfl) ⟨82467, by rfl⟩ : syracuseStep 879653 = 164935) (by norm_num)
theorem B552001 : Blo 487790 552001 := bbase (se 2 (by rfl) ⟨207000, by rfl⟩ : syracuseStep 552001 = 414001) (by norm_num)
theorem B1043533 : Blo 487790 1043533 := bbase (se 3 (by rfl) ⟨195662, by rfl⟩ : syracuseStep 1043533 = 391325) (by norm_num)
theorem B552037 : Blo 487790 552037 := bbase (se 4 (by rfl) ⟨51753, by rfl⟩ : syracuseStep 552037 = 103507) (by norm_num)
theorem B1240181 : Blo 487790 1240181 := bbase (se 5 (by rfl) ⟨58133, by rfl⟩ : syracuseStep 1240181 = 116267) (by norm_num)
theorem B552073 : Blo 487790 552073 := bbase (se 2 (by rfl) ⟨207027, by rfl⟩ : syracuseStep 552073 = 414055) (by norm_num)
theorem B617645 : Blo 487790 617645 := bbase (se 3 (by rfl) ⟨115808, by rfl⟩ : syracuseStep 617645 = 231617) (by norm_num)
theorem B552109 : Blo 487790 552109 := bbase (se 3 (by rfl) ⟨103520, by rfl⟩ : syracuseStep 552109 = 207041) (by norm_num)
theorem B879797 : Blo 487790 879797 := bbase (se 5 (by rfl) ⟨41240, by rfl⟩ : syracuseStep 879797 = 82481) (by norm_num)
theorem B552145 : Blo 487790 552145 := bbase (se 2 (by rfl) ⟨207054, by rfl⟩ : syracuseStep 552145 = 414109) (by norm_num)
theorem B617701 : Blo 487790 617701 := bbase (se 4 (by rfl) ⟨57909, by rfl⟩ : syracuseStep 617701 = 115819) (by norm_num)
theorem B552181 : Blo 487790 552181 := bbase (se 5 (by rfl) ⟨25883, by rfl⟩ : syracuseStep 552181 = 51767) (by norm_num)
theorem B879869 : Blo 487790 879869 := bbase (se 3 (by rfl) ⟨164975, by rfl⟩ : syracuseStep 879869 = 329951) (by norm_num)
theorem B945413 : Blo 487790 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B552217 : Blo 487790 552217 := bbase (se 2 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 552217 = 414163) (by norm_num)
theorem B1174829 : Blo 487790 1174829 := bbase (se 3 (by rfl) ⟨220280, by rfl⟩ : syracuseStep 1174829 = 440561) (by norm_num)
theorem B1240373 : Blo 487790 1240373 := bbase (se 5 (by rfl) ⟨58142, by rfl⟩ : syracuseStep 1240373 = 116285) (by norm_num)
theorem B552253 : Blo 487790 552253 := bbase (se 3 (by rfl) ⟨103547, by rfl⟩ : syracuseStep 552253 = 207095) (by norm_num)
theorem B617797 : Blo 487790 617797 := bbase (se 4 (by rfl) ⟨57918, by rfl⟩ : syracuseStep 617797 = 115837) (by norm_num)
theorem B1568069 : Blo 487790 1568069 := bbase (se 4 (by rfl) ⟨147006, by rfl⟩ : syracuseStep 1568069 = 294013) (by norm_num)
theorem B552289 : Blo 487790 552289 := bbase (se 2 (by rfl) ⟨207108, by rfl⟩ : syracuseStep 552289 = 414217) (by norm_num)
theorem B552325 : Blo 487790 552325 := bbase (se 4 (by rfl) ⟨51780, by rfl⟩ : syracuseStep 552325 = 103561) (by norm_num)
theorem B552361 : Blo 487790 552361 := bbase (se 2 (by rfl) ⟨207135, by rfl⟩ : syracuseStep 552361 = 414271) (by norm_num)
theorem B552397 : Blo 487790 552397 := bbase (se 3 (by rfl) ⟨103574, by rfl⟩ : syracuseStep 552397 = 207149) (by norm_num)
theorem B617969 : Blo 487790 617969 := bbase (se 2 (by rfl) ⟨231738, by rfl⟩ : syracuseStep 617969 = 463477) (by norm_num)
theorem B552433 : Blo 487790 552433 := bbase (se 2 (by rfl) ⟨207162, by rfl⟩ : syracuseStep 552433 = 414325) (by norm_num)
theorem B2092549 : Blo 487790 2092549 := bbase (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) (by norm_num)
theorem B552469 : Blo 487790 552469 := bbase (se 6 (by rfl) ⟨12948, by rfl⟩ : syracuseStep 552469 = 25897) (by norm_num)
theorem B847397 : Blo 487790 847397 := bbase (se 4 (by rfl) ⟨79443, by rfl⟩ : syracuseStep 847397 = 158887) (by norm_num)
theorem B618025 : Blo 487790 618025 := bbase (se 2 (by rfl) ⟨231759, by rfl⟩ : syracuseStep 618025 = 463519) (by norm_num)
theorem B552505 : Blo 487790 552505 := bbase (se 2 (by rfl) ⟨207189, by rfl⟩ : syracuseStep 552505 = 414379) (by norm_num)
theorem B552541 : Blo 487790 552541 := bbase (se 3 (by rfl) ⟨103601, by rfl⟩ : syracuseStep 552541 = 207203) (by norm_num)
theorem B552577 : Blo 487790 552577 := bbase (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) (by norm_num)
theorem B618121 : Blo 487790 618121 := bbase (se 2 (by rfl) ⟨231795, by rfl⟩ : syracuseStep 618121 = 463591) (by norm_num)
theorem B1240717 : Blo 487790 1240717 := bbase (se 3 (by rfl) ⟨232634, by rfl⟩ : syracuseStep 1240717 = 465269) (by norm_num)
theorem B552613 : Blo 487790 552613 := bbase (se 4 (by rfl) ⟨51807, by rfl⟩ : syracuseStep 552613 = 103615) (by norm_num)
theorem B552649 : Blo 487790 552649 := bbase (se 2 (by rfl) ⟨207243, by rfl⟩ : syracuseStep 552649 = 414487) (by norm_num)
theorem B552685 : Blo 487790 552685 := bbase (se 3 (by rfl) ⟨103628, by rfl⟩ : syracuseStep 552685 = 207257) (by norm_num)
theorem B1240829 : Blo 487790 1240829 := bbase (se 3 (by rfl) ⟨232655, by rfl⟩ : syracuseStep 1240829 = 465311) (by norm_num)
theorem B552721 : Blo 487790 552721 := bbase (se 2 (by rfl) ⟨207270, by rfl⟩ : syracuseStep 552721 = 414541) (by norm_num)
theorem B1863445 : Blo 487790 1863445 := bbase (se 6 (by rfl) ⟨43674, by rfl⟩ : syracuseStep 1863445 = 87349) (by norm_num)
theorem B618293 : Blo 487790 618293 := bbase (se 5 (by rfl) ⟨28982, by rfl⟩ : syracuseStep 618293 = 57965) (by norm_num)
theorem B552757 : Blo 487790 552757 := bbase (se 5 (by rfl) ⟨25910, by rfl⟩ : syracuseStep 552757 = 51821) (by norm_num)
theorem B2649941 : Blo 487790 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B552793 : Blo 487790 552793 := bbase (se 2 (by rfl) ⟨207297, by rfl⟩ : syracuseStep 552793 = 414595) (by norm_num)
theorem B618349 : Blo 487790 618349 := bbase (se 3 (by rfl) ⟨115940, by rfl⟩ : syracuseStep 618349 = 231881) (by norm_num)
theorem B552829 : Blo 487790 552829 := bbase (se 3 (by rfl) ⟨103655, by rfl⟩ : syracuseStep 552829 = 207311) (by norm_num)
theorem B552865 : Blo 487790 552865 := bbase (se 2 (by rfl) ⟨207324, by rfl⟩ : syracuseStep 552865 = 414649) (by norm_num)
theorem B1241021 : Blo 487790 1241021 := bbase (se 3 (by rfl) ⟨232691, by rfl⟩ : syracuseStep 1241021 = 465383) (by norm_num)
theorem B2486213 : Blo 487790 2486213 := bbase (se 4 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 2486213 = 466165) (by norm_num)
theorem B552901 : Blo 487790 552901 := bbase (se 4 (by rfl) ⟨51834, by rfl⟩ : syracuseStep 552901 = 103669) (by norm_num)
theorem B618445 : Blo 487790 618445 := bbase (se 3 (by rfl) ⟨115958, by rfl⟩ : syracuseStep 618445 = 231917) (by norm_num)
theorem B552937 : Blo 487790 552937 := bbase (se 2 (by rfl) ⟨207351, by rfl⟩ : syracuseStep 552937 = 414703) (by norm_num)
theorem B552973 : Blo 487790 552973 := bbase (se 3 (by rfl) ⟨103682, by rfl⟩ : syracuseStep 552973 = 207365) (by norm_num)
theorem B880661 : Blo 487790 880661 := bbase (se 6 (by rfl) ⟨20640, by rfl⟩ : syracuseStep 880661 = 41281) (by norm_num)
theorem B553009 : Blo 487790 553009 := bbase (se 2 (by rfl) ⟨207378, by rfl⟩ : syracuseStep 553009 = 414757) (by norm_num)
theorem B1863749 : Blo 487790 1863749 := bbase (se 4 (by rfl) ⟨174726, by rfl⟩ : syracuseStep 1863749 = 349453) (by norm_num)
theorem B553045 : Blo 487790 553045 := bbase (se 8 (by rfl) ⟨3240, by rfl⟩ : syracuseStep 553045 = 6481) (by norm_num)
theorem B618617 : Blo 487790 618617 := bbase (se 2 (by rfl) ⟨231981, by rfl⟩ : syracuseStep 618617 = 463963) (by norm_num)
theorem B553081 : Blo 487790 553081 := bbase (se 2 (by rfl) ⟨207405, by rfl⟩ : syracuseStep 553081 = 414811) (by norm_num)
theorem B782477 : Blo 487790 782477 := bbase (se 3 (by rfl) ⟨146714, by rfl⟩ : syracuseStep 782477 = 293429) (by norm_num)
theorem B553117 : Blo 487790 553117 := bbase (se 3 (by rfl) ⟨103709, by rfl⟩ : syracuseStep 553117 = 207419) (by norm_num)
theorem B618673 : Blo 487790 618673 := bbase (se 2 (by rfl) ⟨232002, by rfl⟩ : syracuseStep 618673 = 464005) (by norm_num)
theorem B553153 : Blo 487790 553153 := bbase (se 2 (by rfl) ⟨207432, by rfl⟩ : syracuseStep 553153 = 414865) (by norm_num)
theorem B553189 : Blo 487790 553189 := bbase (se 4 (by rfl) ⟨51861, by rfl⟩ : syracuseStep 553189 = 103723) (by norm_num)
theorem B553225 : Blo 487790 553225 := bbase (se 2 (by rfl) ⟨207459, by rfl⟩ : syracuseStep 553225 = 414919) (by norm_num)
theorem B618769 : Blo 487790 618769 := bbase (se 2 (by rfl) ⟨232038, by rfl⟩ : syracuseStep 618769 = 464077) (by norm_num)
theorem B1241365 : Blo 487790 1241365 := bbase (se 6 (by rfl) ⟨29094, by rfl⟩ : syracuseStep 1241365 = 58189) (by norm_num)
theorem B553261 : Blo 487790 553261 := bbase (se 3 (by rfl) ⟨103736, by rfl⟩ : syracuseStep 553261 = 207473) (by norm_num)
theorem B782669 : Blo 487790 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B1241477 : Blo 487790 1241477 := bbase (se 4 (by rfl) ⟨116388, by rfl⟩ : syracuseStep 1241477 = 232777) (by norm_num)
theorem B618941 : Blo 487790 618941 := bbase (se 3 (by rfl) ⟨116051, by rfl⟩ : syracuseStep 618941 = 232103) (by norm_num)
theorem B618997 : Blo 487790 618997 := bbase (se 5 (by rfl) ⟨29015, by rfl⟩ : syracuseStep 618997 = 58031) (by norm_num)
theorem B2355733 : Blo 487790 2355733 := bbase (se 6 (by rfl) ⟨55212, by rfl⟩ : syracuseStep 2355733 = 110425) (by norm_num)
theorem B1045037 : Blo 487790 1045037 := bbase (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) (by norm_num)
theorem B1241669 : Blo 487790 1241669 := bbase (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) (by norm_num)
theorem B619093 : Blo 487790 619093 := bbase (se 8 (by rfl) ⟨3627, by rfl⟩ : syracuseStep 619093 = 7255) (by norm_num)
theorem B1045181 : Blo 487790 1045181 := bbase (se 3 (by rfl) ⟨195971, by rfl⟩ : syracuseStep 1045181 = 391943) (by norm_num)
theorem B619265 : Blo 487790 619265 := bbase (se 2 (by rfl) ⟨232224, by rfl⟩ : syracuseStep 619265 = 464449) (by norm_num)
theorem B619321 : Blo 487790 619321 := bbase (se 2 (by rfl) ⟨232245, by rfl⟩ : syracuseStep 619321 = 464491) (by norm_num)
theorem B619417 : Blo 487790 619417 := bbase (se 2 (by rfl) ⟨232281, by rfl⟩ : syracuseStep 619417 = 464563) (by norm_num)
theorem B1242013 : Blo 487790 1242013 := bbase (se 3 (by rfl) ⟨232877, by rfl⟩ : syracuseStep 1242013 = 465755) (by norm_num)
theorem B1242125 : Blo 487790 1242125 := bbase (se 3 (by rfl) ⟨232898, by rfl⟩ : syracuseStep 1242125 = 465797) (by norm_num)
theorem B1045541 : Blo 487790 1045541 := bbase (se 4 (by rfl) ⟨98019, by rfl⟩ : syracuseStep 1045541 = 196039) (by norm_num)
theorem B619589 : Blo 487790 619589 := bbase (se 4 (by rfl) ⟨58086, by rfl⟩ : syracuseStep 619589 = 116173) (by norm_num)
theorem B619645 : Blo 487790 619645 := bbase (se 3 (by rfl) ⟨116183, by rfl⟩ : syracuseStep 619645 = 232367) (by norm_num)
theorem B1242317 : Blo 487790 1242317 := bbase (se 3 (by rfl) ⟨232934, by rfl⟩ : syracuseStep 1242317 = 465869) (by norm_num)
theorem B521425 : Blo 487790 521425 := bbase (se 2 (by rfl) ⟨195534, by rfl⟩ : syracuseStep 521425 = 391069) (by norm_num)
theorem B2487509 : Blo 487790 2487509 := bbase (se 7 (by rfl) ⟨29150, by rfl⟩ : syracuseStep 2487509 = 58301) (by norm_num)
theorem B619741 : Blo 487790 619741 := bbase (se 3 (by rfl) ⟨116201, by rfl⟩ : syracuseStep 619741 = 232403) (by norm_num)
theorem B3142901 : Blo 487790 3142901 := bbase (se 5 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 3142901 = 294647) (by norm_num)
theorem B521497 : Blo 487790 521497 := bbase (se 2 (by rfl) ⟨195561, by rfl⟩ : syracuseStep 521497 = 391123) (by norm_num)
theorem B1176925 : Blo 487790 1176925 := bbase (se 3 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 1176925 = 441347) (by norm_num)
theorem B619913 : Blo 487790 619913 := bbase (se 2 (by rfl) ⟨232467, by rfl⟩ : syracuseStep 619913 = 464935) (by norm_num)
theorem B1701269 : Blo 487790 1701269 := bbase (se 6 (by rfl) ⟨39873, by rfl⟩ : syracuseStep 1701269 = 79747) (by norm_num)
theorem B619969 : Blo 487790 619969 := bbase (se 2 (by rfl) ⟨232488, by rfl⟩ : syracuseStep 619969 = 464977) (by norm_num)
theorem B521677 : Blo 487790 521677 := bbase (se 3 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 521677 = 195629) (by norm_num)
theorem B2258405 : Blo 487790 2258405 := bbase (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) (by norm_num)
theorem B587261 : Blo 487790 587261 := bbase (se 3 (by rfl) ⟨110111, by rfl⟩ : syracuseStep 587261 = 220223) (by norm_num)
theorem B620065 : Blo 487790 620065 := bbase (se 2 (by rfl) ⟨232524, by rfl⟩ : syracuseStep 620065 = 465049) (by norm_num)
theorem B1242661 : Blo 487790 1242661 := bbase (se 4 (by rfl) ⟨116499, by rfl⟩ : syracuseStep 1242661 = 232999) (by norm_num)
theorem B2979413 : Blo 487790 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B783989 : Blo 487790 783989 := bbase (se 5 (by rfl) ⟨36749, by rfl⟩ : syracuseStep 783989 = 73499) (by norm_num)
theorem B1275517 : Blo 487790 1275517 := bbase (se 3 (by rfl) ⟨239159, by rfl⟩ : syracuseStep 1275517 = 478319) (by norm_num)
theorem B6256277 : Blo 487790 6256277 := bbase (se 6 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 6256277 = 293263) (by norm_num)
theorem B1242773 : Blo 487790 1242773 := bbase (se 6 (by rfl) ⟨29127, by rfl⟩ : syracuseStep 1242773 = 58255) (by norm_num)
theorem B587449 : Blo 487790 587449 := bbase (se 2 (by rfl) ⟨220293, by rfl⟩ : syracuseStep 587449 = 440587) (by norm_num)
theorem B620237 : Blo 487790 620237 := bbase (se 3 (by rfl) ⟨116294, by rfl⟩ : syracuseStep 620237 = 232589) (by norm_num)
theorem B784085 : Blo 487790 784085 := bbase (se 7 (by rfl) ⟨9188, by rfl⟩ : syracuseStep 784085 = 18377) (by norm_num)
theorem B784117 : Blo 487790 784117 := bbase (se 5 (by rfl) ⟨36755, by rfl⟩ : syracuseStep 784117 = 73511) (by norm_num)
theorem B620293 : Blo 487790 620293 := bbase (se 4 (by rfl) ⟨58152, by rfl⟩ : syracuseStep 620293 = 116305) (by norm_num)
theorem B1242965 : Blo 487790 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B620389 : Blo 487790 620389 := bbase (se 4 (by rfl) ⟨58161, by rfl⟩ : syracuseStep 620389 = 116323) (by norm_num)
theorem B522121 : Blo 487790 522121 := bbase (se 2 (by rfl) ⟨195795, by rfl⟩ : syracuseStep 522121 = 391591) (by norm_num)
theorem B587665 : Blo 487790 587665 := bbase (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) (by norm_num)
theorem B1046429 : Blo 487790 1046429 := bbase (se 3 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 1046429 = 392411) (by norm_num)
theorem B1177541 : Blo 487790 1177541 := bbase (se 4 (by rfl) ⟨110394, by rfl⟩ : syracuseStep 1177541 = 220789) (by norm_num)
theorem B1177597 : Blo 487790 1177597 := bbase (se 3 (by rfl) ⟨220799, by rfl⟩ : syracuseStep 1177597 = 441599) (by norm_num)
theorem B522245 : Blo 487790 522245 := bbase (se 4 (by rfl) ⟨48960, by rfl⟩ : syracuseStep 522245 = 97921) (by norm_num)
theorem B620561 : Blo 487790 620561 := bbase (se 2 (by rfl) ⟨232710, by rfl⟩ : syracuseStep 620561 = 465421) (by norm_num)
theorem B620617 : Blo 487790 620617 := bbase (se 2 (by rfl) ⟨232731, by rfl⟩ : syracuseStep 620617 = 465463) (by norm_num)
theorem B2652277 : Blo 487790 2652277 := bbase (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) (by norm_num)
theorem B1865861 : Blo 487790 1865861 := bbase (se 4 (by rfl) ⟨174924, by rfl⟩ : syracuseStep 1865861 = 349849) (by norm_num)
theorem B1046677 : Blo 487790 1046677 := bbase (se 6 (by rfl) ⟨24531, by rfl⟩ : syracuseStep 1046677 = 49063) (by norm_num)
theorem B620713 : Blo 487790 620713 := bbase (se 2 (by rfl) ⟨232767, by rfl⟩ : syracuseStep 620713 = 465535) (by norm_num)
theorem B1243309 : Blo 487790 1243309 := bbase (se 3 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 1243309 = 466241) (by norm_num)
theorem B587953 : Blo 487790 587953 := bbase (se 2 (by rfl) ⟨220482, by rfl⟩ : syracuseStep 587953 = 440965) (by norm_num)
theorem B522497 : Blo 487790 522497 := bbase (se 2 (by rfl) ⟨195936, by rfl⟩ : syracuseStep 522497 = 391873) (by norm_num)
theorem B1243421 : Blo 487790 1243421 := bbase (se 3 (by rfl) ⟨233141, by rfl⟩ : syracuseStep 1243421 = 466283) (by norm_num)
theorem B620885 : Blo 487790 620885 := bbase (se 10 (by rfl) ⟨909, by rfl⟩ : syracuseStep 620885 = 1819) (by norm_num)
theorem B620941 : Blo 487790 620941 := bbase (se 3 (by rfl) ⟨116426, by rfl⟩ : syracuseStep 620941 = 232853) (by norm_num)
theorem B1866149 : Blo 487790 1866149 := bbase (se 4 (by rfl) ⟨174951, by rfl⟩ : syracuseStep 1866149 = 349903) (by norm_num)
theorem B2095541 : Blo 487790 2095541 := bbase (se 5 (by rfl) ⟨98228, by rfl⟩ : syracuseStep 2095541 = 196457) (by norm_num)
theorem B1243613 : Blo 487790 1243613 := bbase (se 3 (by rfl) ⟨233177, by rfl⟩ : syracuseStep 1243613 = 466355) (by norm_num)
theorem B2488805 : Blo 487790 2488805 := bbase (se 4 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 2488805 = 466651) (by norm_num)
theorem B621037 : Blo 487790 621037 := bbase (se 3 (by rfl) ⟨116444, by rfl⟩ : syracuseStep 621037 = 232889) (by norm_num)
theorem B1047181 : Blo 487790 1047181 := bbase (se 3 (by rfl) ⟨196346, by rfl⟩ : syracuseStep 1047181 = 392693) (by norm_num)
theorem B621209 : Blo 487790 621209 := bbase (se 2 (by rfl) ⟨232953, by rfl⟩ : syracuseStep 621209 = 465907) (by norm_num)
theorem B522941 : Blo 487790 522941 := bbase (se 3 (by rfl) ⟨98051, by rfl⟩ : syracuseStep 522941 = 196103) (by norm_num)
theorem B621265 : Blo 487790 621265 := bbase (se 2 (by rfl) ⟨232974, by rfl⟩ : syracuseStep 621265 = 465949) (by norm_num)
theorem B4193045 : Blo 487790 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B621361 : Blo 487790 621361 := bbase (se 2 (by rfl) ⟨233010, by rfl⟩ : syracuseStep 621361 = 466021) (by norm_num)
theorem B1243957 : Blo 487790 1243957 := bbase (se 5 (by rfl) ⟨58310, by rfl⟩ : syracuseStep 1243957 = 116621) (by norm_num)
theorem B1244069 : Blo 487790 1244069 := bbase (se 4 (by rfl) ⟨116631, by rfl⟩ : syracuseStep 1244069 = 233263) (by norm_num)
theorem B523189 : Blo 487790 523189 := bbase (se 5 (by rfl) ⟨24524, by rfl⟩ : syracuseStep 523189 = 49049) (by norm_num)
theorem B621533 : Blo 487790 621533 := bbase (se 3 (by rfl) ⟨116537, by rfl⟩ : syracuseStep 621533 = 233075) (by norm_num)
theorem B1178597 : Blo 487790 1178597 := bbase (se 4 (by rfl) ⟨110493, by rfl⟩ : syracuseStep 1178597 = 220987) (by norm_num)
theorem B1571861 : Blo 487790 1571861 := bbase (se 6 (by rfl) ⟨36840, by rfl⟩ : syracuseStep 1571861 = 73681) (by norm_num)
theorem B621589 : Blo 487790 621589 := bbase (se 6 (by rfl) ⟨14568, by rfl⟩ : syracuseStep 621589 = 29137) (by norm_num)
theorem B1244261 : Blo 487790 1244261 := bbase (se 4 (by rfl) ⟨116649, by rfl⟩ : syracuseStep 1244261 = 233299) (by norm_num)
theorem B621685 : Blo 487790 621685 := bbase (se 5 (by rfl) ⟨29141, by rfl⟩ : syracuseStep 621685 = 58283) (by norm_num)
theorem B883885 : Blo 487790 883885 := bbase (se 3 (by rfl) ⟨165728, by rfl⟩ : syracuseStep 883885 = 331457) (by norm_num)
theorem B1768645 : Blo 487790 1768645 := bbase (se 4 (by rfl) ⟨165810, by rfl⟩ : syracuseStep 1768645 = 331621) (by norm_num)
theorem B785629 : Blo 487790 785629 := bbase (se 3 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 785629 = 294611) (by norm_num)
theorem B621857 : Blo 487790 621857 := bbase (se 2 (by rfl) ⟨233196, by rfl⟩ : syracuseStep 621857 = 466393) (by norm_num)
theorem B556345 : Blo 487790 556345 := bbase (se 2 (by rfl) ⟨208629, by rfl⟩ : syracuseStep 556345 = 417259) (by norm_num)
theorem B1670485 : Blo 487790 1670485 := bbase (se 11 (by rfl) ⟨1223, by rfl⟩ : syracuseStep 1670485 = 2447) (by norm_num)
theorem B621913 : Blo 487790 621913 := bbase (se 2 (by rfl) ⟨233217, by rfl⟩ : syracuseStep 621913 = 466435) (by norm_num)
theorem B1768805 : Blo 487790 1768805 := bbase (se 4 (by rfl) ⟨165825, by rfl⟩ : syracuseStep 1768805 = 331651) (by norm_num)
theorem B523633 : Blo 487790 523633 := bbase (se 2 (by rfl) ⟨196362, by rfl⟩ : syracuseStep 523633 = 392725) (by norm_num)
theorem B2096549 : Blo 487790 2096549 := bbase (se 4 (by rfl) ⟨196551, by rfl⟩ : syracuseStep 2096549 = 393103) (by norm_num)
theorem B523693 : Blo 487790 523693 := bbase (se 3 (by rfl) ⟨98192, by rfl⟩ : syracuseStep 523693 = 196385) (by norm_num)
theorem B589241 : Blo 487790 589241 := bbase (se 2 (by rfl) ⟨220965, by rfl⟩ : syracuseStep 589241 = 441931) (by norm_num)
theorem B622009 : Blo 487790 622009 := bbase (se 2 (by rfl) ⟨233253, by rfl⟩ : syracuseStep 622009 = 466507) (by norm_num)
theorem B1244605 : Blo 487790 1244605 := bbase (se 3 (by rfl) ⟨233363, by rfl⟩ : syracuseStep 1244605 = 466727) (by norm_num)
theorem B1048069 : Blo 487790 1048069 := bbase (se 4 (by rfl) ⟨98256, by rfl⟩ : syracuseStep 1048069 = 196513) (by norm_num)
theorem B1244717 : Blo 487790 1244717 := bbase (se 3 (by rfl) ⟨233384, by rfl⟩ : syracuseStep 1244717 = 466769) (by norm_num)
theorem B622181 : Blo 487790 622181 := bbase (se 4 (by rfl) ⟨58329, by rfl⟩ : syracuseStep 622181 = 116659) (by norm_num)
theorem B622237 : Blo 487790 622237 := bbase (se 3 (by rfl) ⟨116669, by rfl⟩ : syracuseStep 622237 = 233339) (by norm_num)
theorem B524009 : Blo 487790 524009 := bbase (se 2 (by rfl) ⟨196503, by rfl⟩ : syracuseStep 524009 = 393007) (by norm_num)
theorem B1408757 : Blo 487790 1408757 := bbase (se 5 (by rfl) ⟨66035, by rfl⟩ : syracuseStep 1408757 = 132071) (by norm_num)
theorem B622333 : Blo 487790 622333 := bbase (se 3 (by rfl) ⟨116687, by rfl⟩ : syracuseStep 622333 = 233375) (by norm_num)
theorem B786341 : Blo 487790 786341 := bbase (se 4 (by rfl) ⟨73719, by rfl⟩ : syracuseStep 786341 = 147439) (by norm_num)
theorem B1048565 : Blo 487790 1048565 := bbase (se 5 (by rfl) ⟨49151, by rfl⟩ : syracuseStep 1048565 = 98303) (by norm_num)
theorem B491523 : Blo 487790 491523 := bstep (se 1 (by rfl) ⟨368642, by rfl⟩ : syracuseStep 491523 = 737285) B737285
theorem B786449 : Blo 487790 786449 := bstep (se 2 (by rfl) ⟨294918, by rfl⟩ : syracuseStep 786449 = 589837) B589837
theorem B491539 : Blo 487790 491539 := bstep (se 1 (by rfl) ⟨368654, by rfl⟩ : syracuseStep 491539 = 737309) B737309
theorem B491555 : Blo 487790 491555 := bstep (se 1 (by rfl) ⟨368666, by rfl⟩ : syracuseStep 491555 = 737333) B737333
theorem B557107 : Blo 487790 557107 := bstep (se 1 (by rfl) ⟨417830, by rfl⟩ : syracuseStep 557107 = 835661) B835661
theorem B491571 : Blo 487790 491571 := bstep (se 1 (by rfl) ⟨368678, by rfl⟩ : syracuseStep 491571 = 737357) B737357
theorem B491587 : Blo 487790 491587 := bstep (se 1 (by rfl) ⟨368690, by rfl⟩ : syracuseStep 491587 = 737381) B737381
theorem B491603 : Blo 487790 491603 := bstep (se 1 (by rfl) ⟨368702, by rfl⟩ : syracuseStep 491603 = 737405) B737405
theorem B491619 : Blo 487790 491619 := bstep (se 1 (by rfl) ⟨368714, by rfl⟩ : syracuseStep 491619 = 737429) B737429
theorem B2097265 : Blo 487790 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B491635 : Blo 487790 491635 := bstep (se 1 (by rfl) ⟨368726, by rfl⟩ : syracuseStep 491635 = 737453) B737453
theorem B491651 : Blo 487790 491651 := bstep (se 1 (by rfl) ⟨368738, by rfl⟩ : syracuseStep 491651 = 737477) B737477
theorem B491667 : Blo 487790 491667 := bstep (se 1 (by rfl) ⟨368750, by rfl⟩ : syracuseStep 491667 = 737501) B737501
theorem B491683 : Blo 487790 491683 := bstep (se 1 (by rfl) ⟨368762, by rfl⟩ : syracuseStep 491683 = 737525) B737525
theorem B491699 : Blo 487790 491699 := bstep (se 1 (by rfl) ⟨368774, by rfl⟩ : syracuseStep 491699 = 737549) B737549
theorem B491715 : Blo 487790 491715 := bstep (se 1 (by rfl) ⟨368786, by rfl⟩ : syracuseStep 491715 = 737573) B737573
theorem B491731 : Blo 487790 491731 := bstep (se 1 (by rfl) ⟨368798, by rfl⟩ : syracuseStep 491731 = 737597) B737597
theorem B40337621 : Blo 487790 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B1573091 : Blo 487790 1573091 := bstep (se 1 (by rfl) ⟨1179818, by rfl⟩ : syracuseStep 1573091 = 2359637) B2359637
theorem B491747 : Blo 487790 491747 := bstep (se 1 (by rfl) ⟨368810, by rfl⟩ : syracuseStep 491747 = 737621) B737621
theorem B491763 : Blo 487790 491763 := bstep (se 1 (by rfl) ⟨368822, by rfl⟩ : syracuseStep 491763 = 737645) B737645
theorem B491779 : Blo 487790 491779 := bstep (se 1 (by rfl) ⟨368834, by rfl⟩ : syracuseStep 491779 = 737669) B737669
theorem B590179 : Blo 487790 590179 := bstep (se 1 (by rfl) ⟨442634, by rfl⟩ : syracuseStep 590179 = 885269) B885269
theorem B524675 : Blo 487790 524675 := bstep (se 1 (by rfl) ⟨393506, by rfl⟩ : syracuseStep 524675 = 787013) B787013
theorem B1507889 : Blo 487790 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B3146309 : Blo 487790 3146309 := bstep (se 4 (by rfl) ⟨294966, by rfl⟩ : syracuseStep 3146309 = 589933) B589933
theorem B1049411 : Blo 487790 1049411 := bstep (se 1 (by rfl) ⟨787058, by rfl⟩ : syracuseStep 1049411 = 1574117) B1574117
theorem B2786147 : Blo 487790 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B1344365 : Blo 487790 1344365 := bstep (se 3 (by rfl) ⟨252068, by rfl⟩ : syracuseStep 1344365 = 504137) B504137
theorem B787315 : Blo 487790 787315 := bstep (se 1 (by rfl) ⟨590486, by rfl⟩ : syracuseStep 787315 = 1180973) B1180973
theorem B2360269 : Blo 487790 2360269 := bstep (se 3 (by rfl) ⟨442550, by rfl⟩ : syracuseStep 2360269 = 885101) B885101
theorem B1278929 : Blo 487790 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B787571 : Blo 487790 787571 := bstep (se 1 (by rfl) ⟨590678, by rfl⟩ : syracuseStep 787571 = 1181357) B1181357
theorem B3704291 : Blo 487790 3704291 := bstep (se 1 (by rfl) ⟨2778218, by rfl⟩ : syracuseStep 3704291 = 5556437) B5556437
theorem B1181155 : Blo 487790 1181155 := bstep (se 1 (by rfl) ⟨885866, by rfl⟩ : syracuseStep 1181155 = 1771733) B1771733
theorem B1574435 : Blo 487790 1574435 := bstep (se 1 (by rfl) ⟨1180826, by rfl⟩ : syracuseStep 1574435 = 2361653) B2361653
theorem B2787149 : Blo 487790 2787149 := bstep (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) B1045181
theorem B2362097 : Blo 487790 2362097 := bstep (se 2 (by rfl) ⟨885786, by rfl⟩ : syracuseStep 2362097 = 1771573) B1771573
theorem B2657123 : Blo 487790 2657123 := bstep (se 1 (by rfl) ⟨1992842, by rfl⟩ : syracuseStep 2657123 = 3985685) B3985685
theorem B3771461 : Blo 487790 3771461 := bstep (se 4 (by rfl) ⟨353574, by rfl⟩ : syracuseStep 3771461 = 707149) B707149
theorem B494723 : Blo 487790 494723 := bstep (se 1 (by rfl) ⟨371042, by rfl⟩ : syracuseStep 494723 = 742085) B742085
theorem B1674893 : Blo 487790 1674893 := bstep (se 3 (by rfl) ⟨314042, by rfl⟩ : syracuseStep 1674893 = 628085) B628085
theorem B1117891 : Blo 487790 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B823169 : Blo 487790 823169 := bstep (se 2 (by rfl) ⟨308688, by rfl⟩ : syracuseStep 823169 = 617377) B617377
theorem B823297 : Blo 487790 823297 := bstep (se 2 (by rfl) ⟨308736, by rfl⟩ : syracuseStep 823297 = 617473) B617473
theorem B823331 : Blo 487790 823331 := bstep (se 1 (by rfl) ⟨617498, by rfl⟩ : syracuseStep 823331 = 1234997) B1234997
theorem B3149873 : Blo 487790 3149873 := bstep (se 2 (by rfl) ⟨1181202, by rfl⟩ : syracuseStep 3149873 = 2362405) B2362405
theorem B5279813 : Blo 487790 5279813 := bstep (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) B989965
theorem B2822221 : Blo 487790 2822221 := bstep (se 3 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 2822221 = 1058333) B1058333
theorem B823459 : Blo 487790 823459 := bstep (se 1 (by rfl) ⟨617594, by rfl⟩ : syracuseStep 823459 = 1235189) B1235189
theorem B954595 : Blo 487790 954595 := bstep (se 1 (by rfl) ⟨715946, by rfl⟩ : syracuseStep 954595 = 1431893) B1431893
theorem B823601 : Blo 487790 823601 := bstep (se 2 (by rfl) ⟨308850, by rfl⟩ : syracuseStep 823601 = 617701) B617701
theorem B3346829 : Blo 487790 3346829 := bstep (se 3 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 3346829 = 1255061) B1255061
theorem B823729 : Blo 487790 823729 := bstep (se 2 (by rfl) ⟨308898, by rfl⟩ : syracuseStep 823729 = 617797) B617797
theorem B2822597 : Blo 487790 2822597 := bstep (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) B529237
theorem B823763 : Blo 487790 823763 := bstep (se 1 (by rfl) ⟨617822, by rfl⟩ : syracuseStep 823763 = 1235645) B1235645
theorem B823891 : Blo 487790 823891 := bstep (se 1 (by rfl) ⟨617918, by rfl⟩ : syracuseStep 823891 = 1235837) B1235837
theorem B2790065 : Blo 487790 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B824033 : Blo 487790 824033 := bstep (se 2 (by rfl) ⟨309012, by rfl⟩ : syracuseStep 824033 = 618025) B618025
theorem B660193 : Blo 487790 660193 := bstep (se 2 (by rfl) ⟨247572, by rfl⟩ : syracuseStep 660193 = 495145) B495145
theorem B824161 : Blo 487790 824161 := bstep (se 2 (by rfl) ⟨309060, by rfl⟩ : syracuseStep 824161 = 618121) B618121
theorem B824195 : Blo 487790 824195 := bstep (se 1 (by rfl) ⟨618146, by rfl⟩ : syracuseStep 824195 = 1236293) B1236293
theorem B824323 : Blo 487790 824323 := bstep (se 1 (by rfl) ⟨618242, by rfl⟩ : syracuseStep 824323 = 1236485) B1236485
theorem B2987021 : Blo 487790 2987021 := bstep (se 3 (by rfl) ⟨560066, by rfl⟩ : syracuseStep 2987021 = 1120133) B1120133
theorem B824465 : Blo 487790 824465 := bstep (se 2 (by rfl) ⟨309174, by rfl⟩ : syracuseStep 824465 = 618349) B618349
theorem B824593 : Blo 487790 824593 := bstep (se 2 (by rfl) ⟨309222, by rfl⟩ : syracuseStep 824593 = 618445) B618445
theorem B824627 : Blo 487790 824627 := bstep (se 1 (by rfl) ⟨618470, by rfl⟩ : syracuseStep 824627 = 1236941) B1236941
theorem B824755 : Blo 487790 824755 := bstep (se 1 (by rfl) ⟨618566, by rfl⟩ : syracuseStep 824755 = 1237133) B1237133
theorem B824897 : Blo 487790 824897 := bstep (se 2 (by rfl) ⟨309336, by rfl⟩ : syracuseStep 824897 = 618673) B618673
theorem B825025 : Blo 487790 825025 := bstep (se 2 (by rfl) ⟨309384, by rfl⟩ : syracuseStep 825025 = 618769) B618769
theorem B4200133 : Blo 487790 4200133 := bstep (se 4 (by rfl) ⟨393762, by rfl⟩ : syracuseStep 4200133 = 787525) B787525
theorem B825059 : Blo 487790 825059 := bstep (se 1 (by rfl) ⟨618794, by rfl⟩ : syracuseStep 825059 = 1237589) B1237589
theorem B1120081 : Blo 487790 1120081 := bstep (se 2 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 1120081 = 840061) B840061
theorem B825187 : Blo 487790 825187 := bstep (se 1 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 825187 = 1237781) B1237781
theorem B825329 : Blo 487790 825329 := bstep (se 2 (by rfl) ⟨309498, by rfl⟩ : syracuseStep 825329 = 618997) B618997
theorem B2791523 : Blo 487790 2791523 := bstep (se 1 (by rfl) ⟨2093642, by rfl⟩ : syracuseStep 2791523 = 4187285) B4187285
theorem B825457 : Blo 487790 825457 := bstep (se 2 (by rfl) ⟨309546, by rfl⟩ : syracuseStep 825457 = 619093) B619093
theorem B825491 : Blo 487790 825491 := bstep (se 1 (by rfl) ⟨619118, by rfl⟩ : syracuseStep 825491 = 1238237) B1238237
theorem B825619 : Blo 487790 825619 := bstep (se 1 (by rfl) ⟨619214, by rfl⟩ : syracuseStep 825619 = 1238429) B1238429
theorem B694595 : Blo 487790 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B825761 : Blo 487790 825761 := bstep (se 2 (by rfl) ⟨309660, by rfl⟩ : syracuseStep 825761 = 619321) B619321
theorem B825889 : Blo 487790 825889 := bstep (se 2 (by rfl) ⟨309708, by rfl⟩ : syracuseStep 825889 = 619417) B619417
theorem B825923 : Blo 487790 825923 := bstep (se 1 (by rfl) ⟨619442, by rfl⟩ : syracuseStep 825923 = 1238885) B1238885
theorem B498259 : Blo 487790 498259 := bstep (se 1 (by rfl) ⟨373694, by rfl⟩ : syracuseStep 498259 = 747389) B747389
theorem B826051 : Blo 487790 826051 := bstep (se 1 (by rfl) ⟨619538, by rfl⟩ : syracuseStep 826051 = 1239077) B1239077
theorem B3709637 : Blo 487790 3709637 := bstep (se 4 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 3709637 = 695557) B695557
theorem B826193 : Blo 487790 826193 := bstep (se 2 (by rfl) ⟨309822, by rfl⟩ : syracuseStep 826193 = 619645) B619645
theorem B2235235 : Blo 487790 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B695233 : Blo 487790 695233 := bstep (se 2 (by rfl) ⟨260712, by rfl⟩ : syracuseStep 695233 = 521425) B521425
theorem B990161 : Blo 487790 990161 := bstep (se 2 (by rfl) ⟨371310, by rfl⟩ : syracuseStep 990161 = 742621) B742621
theorem B826321 : Blo 487790 826321 := bstep (se 2 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 826321 = 619741) B619741
theorem B826355 : Blo 487790 826355 := bstep (se 1 (by rfl) ⟨619766, by rfl⟩ : syracuseStep 826355 = 1239533) B1239533
theorem B826483 : Blo 487790 826483 := bstep (se 1 (by rfl) ⟨619862, by rfl⟩ : syracuseStep 826483 = 1239725) B1239725
theorem B826625 : Blo 487790 826625 := bstep (se 2 (by rfl) ⟨309984, by rfl⟩ : syracuseStep 826625 = 619969) B619969
theorem B695569 : Blo 487790 695569 := bstep (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) B521677
theorem B826753 : Blo 487790 826753 := bstep (se 2 (by rfl) ⟨310032, by rfl⟩ : syracuseStep 826753 = 620065) B620065
theorem B826787 : Blo 487790 826787 := bstep (se 1 (by rfl) ⟨620090, by rfl⟩ : syracuseStep 826787 = 1240181) B1240181
theorem B826915 : Blo 487790 826915 := bstep (se 1 (by rfl) ⟨620186, by rfl⟩ : syracuseStep 826915 = 1240373) B1240373
theorem B827057 : Blo 487790 827057 := bstep (se 2 (by rfl) ⟨310146, by rfl⟩ : syracuseStep 827057 = 620293) B620293
theorem B564931 : Blo 487790 564931 := bstep (se 1 (by rfl) ⟨423698, by rfl⟩ : syracuseStep 564931 = 847397) B847397
theorem B794321 : Blo 487790 794321 := bstep (se 2 (by rfl) ⟨297870, by rfl⟩ : syracuseStep 794321 = 595741) B595741
theorem B827185 : Blo 487790 827185 := bstep (se 2 (by rfl) ⟨310194, by rfl⟩ : syracuseStep 827185 = 620389) B620389
theorem B827219 : Blo 487790 827219 := bstep (se 1 (by rfl) ⟨620414, by rfl⟩ : syracuseStep 827219 = 1240829) B1240829
theorem B696161 : Blo 487790 696161 := bstep (se 2 (by rfl) ⟨261060, by rfl⟩ : syracuseStep 696161 = 522121) B522121
theorem B4595555 : Blo 487790 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B1515395 : Blo 487790 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B1646513 : Blo 487790 1646513 := bstep (se 2 (by rfl) ⟨617442, by rfl⟩ : syracuseStep 1646513 = 1234885) B1234885
theorem B827347 : Blo 487790 827347 := bstep (se 1 (by rfl) ⟨620510, by rfl⟩ : syracuseStep 827347 = 1241021) B1241021
theorem B1318915 : Blo 487790 1318915 := bstep (se 1 (by rfl) ⟨989186, by rfl⟩ : syracuseStep 1318915 = 1978373) B1978373
theorem B3186701 : Blo 487790 3186701 := bstep (se 3 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 3186701 = 1195013) B1195013
theorem B827489 : Blo 487790 827489 := bstep (se 2 (by rfl) ⟨310308, by rfl⟩ : syracuseStep 827489 = 620617) B620617
theorem B598115 : Blo 487790 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B827617 : Blo 487790 827617 := bstep (se 2 (by rfl) ⟨310356, by rfl⟩ : syracuseStep 827617 = 620713) B620713
theorem B827651 : Blo 487790 827651 := bstep (se 1 (by rfl) ⟨620738, by rfl⟩ : syracuseStep 827651 = 1241477) B1241477
theorem B696691 : Blo 487790 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B827779 : Blo 487790 827779 := bstep (se 1 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 827779 = 1241669) B1241669
theorem B1647053 : Blo 487790 1647053 := bstep (se 3 (by rfl) ⟨308822, by rfl⟩ : syracuseStep 1647053 = 617645) B617645
theorem B1647107 : Blo 487790 1647107 := bstep (se 1 (by rfl) ⟨1235330, by rfl⟩ : syracuseStep 1647107 = 2470661) B2470661
theorem B926225 : Blo 487790 926225 := bstep (se 2 (by rfl) ⟨347334, by rfl⟩ : syracuseStep 926225 = 694669) B694669
theorem B827921 : Blo 487790 827921 := bstep (se 2 (by rfl) ⟨310470, by rfl⟩ : syracuseStep 827921 = 620941) B620941
theorem B664129 : Blo 487790 664129 := bstep (se 2 (by rfl) ⟨249048, by rfl⟩ : syracuseStep 664129 = 498097) B498097
theorem B4694669 : Blo 487790 4694669 := bstep (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) B1760501
theorem B828049 : Blo 487790 828049 := bstep (se 2 (by rfl) ⟨310518, by rfl⟩ : syracuseStep 828049 = 621037) B621037
theorem B828083 : Blo 487790 828083 := bstep (se 1 (by rfl) ⟨621062, by rfl⟩ : syracuseStep 828083 = 1242125) B1242125
theorem B697027 : Blo 487790 697027 := bstep (se 1 (by rfl) ⟨522770, by rfl⟩ : syracuseStep 697027 = 1045541) B1045541
theorem B1647377 : Blo 487790 1647377 := bstep (se 2 (by rfl) ⟨617766, by rfl⟩ : syracuseStep 1647377 = 1235533) B1235533
theorem B1254179 : Blo 487790 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B828211 : Blo 487790 828211 := bstep (se 1 (by rfl) ⟨621158, by rfl⟩ : syracuseStep 828211 = 1242317) B1242317
theorem B828353 : Blo 487790 828353 := bstep (se 2 (by rfl) ⟨310632, by rfl⟩ : syracuseStep 828353 = 621265) B621265
theorem B664529 : Blo 487790 664529 := bstep (se 2 (by rfl) ⟨249198, by rfl⟩ : syracuseStep 664529 = 498397) B498397
theorem B828481 : Blo 487790 828481 := bstep (se 2 (by rfl) ⟨310680, by rfl⟩ : syracuseStep 828481 = 621361) B621361
theorem B664643 : Blo 487790 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B4170851 : Blo 487790 4170851 := bstep (se 1 (by rfl) ⟨3128138, by rfl⟩ : syracuseStep 4170851 = 6256277) B6256277
theorem B828515 : Blo 487790 828515 := bstep (se 1 (by rfl) ⟨621386, by rfl⟩ : syracuseStep 828515 = 1242773) B1242773
theorem B828643 : Blo 487790 828643 := bstep (se 1 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 828643 = 1242965) B1242965
theorem B697585 : Blo 487790 697585 := bstep (se 2 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 697585 = 523189) B523189
theorem B697619 : Blo 487790 697619 := bstep (se 1 (by rfl) ⟨523214, by rfl⟩ : syracuseStep 697619 = 1046429) B1046429
theorem B1647917 : Blo 487790 1647917 := bstep (se 3 (by rfl) ⟨308984, by rfl⟩ : syracuseStep 1647917 = 617969) B617969
theorem B1647971 : Blo 487790 1647971 := bstep (se 1 (by rfl) ⟨1235978, by rfl⟩ : syracuseStep 1647971 = 2471957) B2471957
theorem B828785 : Blo 487790 828785 := bstep (se 2 (by rfl) ⟨310794, by rfl⟩ : syracuseStep 828785 = 621589) B621589
theorem B927121 : Blo 487790 927121 := bstep (se 2 (by rfl) ⟨347670, by rfl⟩ : syracuseStep 927121 = 695341) B695341
theorem B828913 : Blo 487790 828913 := bstep (se 2 (by rfl) ⟨310842, by rfl⟩ : syracuseStep 828913 = 621685) B621685
theorem B828947 : Blo 487790 828947 := bstep (se 1 (by rfl) ⟨621710, by rfl⟩ : syracuseStep 828947 = 1243421) B1243421
theorem B927281 : Blo 487790 927281 := bstep (se 2 (by rfl) ⟨347730, by rfl⟩ : syracuseStep 927281 = 695461) B695461
theorem B1648241 : Blo 487790 1648241 := bstep (se 2 (by rfl) ⟨618090, by rfl⟩ : syracuseStep 1648241 = 1236181) B1236181
theorem B829075 : Blo 487790 829075 := bstep (se 1 (by rfl) ⟨621806, by rfl⟩ : syracuseStep 829075 = 1243613) B1243613
theorem B829217 : Blo 487790 829217 := bstep (se 2 (by rfl) ⟨310956, by rfl⟩ : syracuseStep 829217 = 621913) B621913
theorem B698177 : Blo 487790 698177 := bstep (se 2 (by rfl) ⟨261816, by rfl⟩ : syracuseStep 698177 = 523633) B523633
theorem B2795363 : Blo 487790 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B698257 : Blo 487790 698257 := bstep (se 2 (by rfl) ⟨261846, by rfl⟩ : syracuseStep 698257 = 523693) B523693
theorem B829345 : Blo 487790 829345 := bstep (se 2 (by rfl) ⟨311004, by rfl⟩ : syracuseStep 829345 = 622009) B622009
theorem B927683 : Blo 487790 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B829379 : Blo 487790 829379 := bstep (se 1 (by rfl) ⟨622034, by rfl⟩ : syracuseStep 829379 = 1244069) B1244069
theorem B6301637 : Blo 487790 6301637 := bstep (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) B1181557
theorem B829507 : Blo 487790 829507 := bstep (se 1 (by rfl) ⟨622130, by rfl⟩ : syracuseStep 829507 = 1244261) B1244261
theorem B1648781 : Blo 487790 1648781 := bstep (se 3 (by rfl) ⟨309146, by rfl⟩ : syracuseStep 1648781 = 618293) B618293
theorem B1321123 : Blo 487790 1321123 := bstep (se 1 (by rfl) ⟨990842, by rfl⟩ : syracuseStep 1321123 = 1981685) B1981685
theorem B1648835 : Blo 487790 1648835 := bstep (se 1 (by rfl) ⟨1236626, by rfl⟩ : syracuseStep 1648835 = 2473253) B2473253
theorem B829649 : Blo 487790 829649 := bstep (se 2 (by rfl) ⟨311118, by rfl⟩ : syracuseStep 829649 = 622237) B622237
theorem B1681681 : Blo 487790 1681681 := bstep (se 2 (by rfl) ⟨630630, by rfl⟩ : syracuseStep 1681681 = 1261261) B1261261
theorem B829777 : Blo 487790 829777 := bstep (se 2 (by rfl) ⟨311166, by rfl⟩ : syracuseStep 829777 = 622333) B622333
theorem B829811 : Blo 487790 829811 := bstep (se 1 (by rfl) ⟨622358, by rfl⟩ : syracuseStep 829811 = 1244717) B1244717
theorem B1649105 : Blo 487790 1649105 := bstep (se 2 (by rfl) ⟨618414, by rfl⟩ : syracuseStep 1649105 = 1236829) B1236829
theorem B731699 : Blo 487790 731699 := bstep (se 1 (by rfl) ⟨548774, by rfl⟩ : syracuseStep 731699 = 1097549) B1097549
theorem B731729 : Blo 487790 731729 := bstep (se 2 (by rfl) ⟨274398, by rfl⟩ : syracuseStep 731729 = 548797) B548797
theorem B731747 : Blo 487790 731747 := bstep (se 1 (by rfl) ⟨548810, by rfl⟩ : syracuseStep 731747 = 1097621) B1097621
theorem B731777 : Blo 487790 731777 := bstep (se 2 (by rfl) ⟨274416, by rfl⟩ : syracuseStep 731777 = 548833) B548833
theorem B731795 : Blo 487790 731795 := bstep (se 1 (by rfl) ⟨548846, by rfl⟩ : syracuseStep 731795 = 1097693) B1097693
theorem B699043 : Blo 487790 699043 := bstep (se 1 (by rfl) ⟨524282, by rfl⟩ : syracuseStep 699043 = 1048565) B1048565
theorem B731825 : Blo 487790 731825 := bstep (se 2 (by rfl) ⟨274434, by rfl⟩ : syracuseStep 731825 = 548869) B548869
theorem B731843 : Blo 487790 731843 := bstep (se 1 (by rfl) ⟨548882, by rfl⟩ : syracuseStep 731843 = 1097765) B1097765
theorem B731873 : Blo 487790 731873 := bstep (se 2 (by rfl) ⟨274452, by rfl⟩ : syracuseStep 731873 = 548905) B548905
theorem B731891 : Blo 487790 731891 := bstep (se 1 (by rfl) ⟨548918, by rfl⟩ : syracuseStep 731891 = 1097837) B1097837
theorem B5745421 : Blo 487790 5745421 := bstep (se 3 (by rfl) ⟨1077266, by rfl⟩ : syracuseStep 5745421 = 2154533) B2154533
theorem B731921 : Blo 487790 731921 := bstep (se 2 (by rfl) ⟨274470, by rfl⟩ : syracuseStep 731921 = 548941) B548941
theorem B731939 : Blo 487790 731939 := bstep (se 1 (by rfl) ⟨548954, by rfl⟩ : syracuseStep 731939 = 1097909) B1097909
theorem B1878833 : Blo 487790 1878833 := bstep (se 2 (by rfl) ⟨704562, by rfl⟩ : syracuseStep 1878833 = 1409125) B1409125
theorem B731969 : Blo 487790 731969 := bstep (se 2 (by rfl) ⟨274488, by rfl⟩ : syracuseStep 731969 = 548977) B548977
theorem B928579 : Blo 487790 928579 := bstep (se 1 (by rfl) ⟨696434, by rfl⟩ : syracuseStep 928579 = 1392869) B1392869
theorem B731987 : Blo 487790 731987 := bstep (se 1 (by rfl) ⟨548990, by rfl⟩ : syracuseStep 731987 = 1097981) B1097981
theorem B732017 : Blo 487790 732017 := bstep (se 2 (by rfl) ⟨274506, by rfl⟩ : syracuseStep 732017 = 549013) B549013
theorem B732035 : Blo 487790 732035 := bstep (se 1 (by rfl) ⟨549026, by rfl⟩ : syracuseStep 732035 = 1098053) B1098053
theorem B732065 : Blo 487790 732065 := bstep (se 2 (by rfl) ⟨274524, by rfl⟩ : syracuseStep 732065 = 549049) B549049
theorem B732083 : Blo 487790 732083 := bstep (se 1 (by rfl) ⟨549062, by rfl⟩ : syracuseStep 732083 = 1098125) B1098125
theorem B732113 : Blo 487790 732113 := bstep (se 2 (by rfl) ⟨274542, by rfl⟩ : syracuseStep 732113 = 549085) B549085
theorem B732131 : Blo 487790 732131 := bstep (se 1 (by rfl) ⟨549098, by rfl⟩ : syracuseStep 732131 = 1098197) B1098197
theorem B928739 : Blo 487790 928739 := bstep (se 1 (by rfl) ⟨696554, by rfl⟩ : syracuseStep 928739 = 1393109) B1393109
theorem B1649645 : Blo 487790 1649645 := bstep (se 3 (by rfl) ⟨309308, by rfl⟩ : syracuseStep 1649645 = 618617) B618617
theorem B732161 : Blo 487790 732161 := bstep (se 2 (by rfl) ⟨274560, by rfl⟩ : syracuseStep 732161 = 549121) B549121
theorem B732179 : Blo 487790 732179 := bstep (se 1 (by rfl) ⟨549134, by rfl⟩ : syracuseStep 732179 = 1098269) B1098269
theorem B1649699 : Blo 487790 1649699 := bstep (se 1 (by rfl) ⟨1237274, by rfl⟩ : syracuseStep 1649699 = 2474549) B2474549
theorem B1322029 : Blo 487790 1322029 := bstep (se 3 (by rfl) ⟨247880, by rfl⟩ : syracuseStep 1322029 = 495761) B495761
theorem B732209 : Blo 487790 732209 := bstep (se 2 (by rfl) ⟨274578, by rfl⟩ : syracuseStep 732209 = 549157) B549157
theorem B732227 : Blo 487790 732227 := bstep (se 1 (by rfl) ⟨549170, by rfl⟩ : syracuseStep 732227 = 1098341) B1098341
theorem B732257 : Blo 487790 732257 := bstep (se 2 (by rfl) ⟨274596, by rfl⟩ : syracuseStep 732257 = 549193) B549193
theorem B732275 : Blo 487790 732275 := bstep (se 1 (by rfl) ⟨549206, by rfl⟩ : syracuseStep 732275 = 1098413) B1098413
theorem B699521 : Blo 487790 699521 := bstep (se 2 (by rfl) ⟨262320, by rfl⟩ : syracuseStep 699521 = 524641) B524641
theorem B732305 : Blo 487790 732305 := bstep (se 2 (by rfl) ⟨274614, by rfl⟩ : syracuseStep 732305 = 549229) B549229
theorem B732323 : Blo 487790 732323 := bstep (se 1 (by rfl) ⟨549242, by rfl⟩ : syracuseStep 732323 = 1098485) B1098485
theorem B1617059 : Blo 487790 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B732353 : Blo 487790 732353 := bstep (se 2 (by rfl) ⟨274632, by rfl⟩ : syracuseStep 732353 = 549265) B549265
theorem B732371 : Blo 487790 732371 := bstep (se 1 (by rfl) ⟨549278, by rfl⟩ : syracuseStep 732371 = 1098557) B1098557
theorem B732401 : Blo 487790 732401 := bstep (se 2 (by rfl) ⟨274650, by rfl⟩ : syracuseStep 732401 = 549301) B549301
theorem B699635 : Blo 487790 699635 := bstep (se 1 (by rfl) ⟨524726, by rfl⟩ : syracuseStep 699635 = 1049453) B1049453
theorem B732419 : Blo 487790 732419 := bstep (se 1 (by rfl) ⟨549314, by rfl⟩ : syracuseStep 732419 = 1098629) B1098629
theorem B10595605 : Blo 487790 10595605 := bstep (se 6 (by rfl) ⟨248334, by rfl⟩ : syracuseStep 10595605 = 496669) B496669
theorem B732449 : Blo 487790 732449 := bstep (se 2 (by rfl) ⟨274668, by rfl⟩ : syracuseStep 732449 = 549337) B549337
theorem B1649969 : Blo 487790 1649969 := bstep (se 2 (by rfl) ⟨618738, by rfl⟩ : syracuseStep 1649969 = 1237477) B1237477
theorem B732467 : Blo 487790 732467 := bstep (se 1 (by rfl) ⟨549350, by rfl⟩ : syracuseStep 732467 = 1098701) B1098701
theorem B699715 : Blo 487790 699715 := bstep (se 1 (by rfl) ⟨524786, by rfl⟩ : syracuseStep 699715 = 1049573) B1049573
theorem B732497 : Blo 487790 732497 := bstep (se 2 (by rfl) ⟨274686, by rfl⟩ : syracuseStep 732497 = 549373) B549373
theorem B732515 : Blo 487790 732515 := bstep (se 1 (by rfl) ⟨549386, by rfl⟩ : syracuseStep 732515 = 1098773) B1098773
theorem B732545 : Blo 487790 732545 := bstep (se 2 (by rfl) ⟨274704, by rfl⟩ : syracuseStep 732545 = 549409) B549409
theorem B732563 : Blo 487790 732563 := bstep (se 1 (by rfl) ⟨549422, by rfl⟩ : syracuseStep 732563 = 1098845) B1098845
theorem B732593 : Blo 487790 732593 := bstep (se 2 (by rfl) ⟨274722, by rfl⟩ : syracuseStep 732593 = 549445) B549445
theorem B732611 : Blo 487790 732611 := bstep (se 1 (by rfl) ⟨549458, by rfl⟩ : syracuseStep 732611 = 1098917) B1098917
theorem B732641 : Blo 487790 732641 := bstep (se 2 (by rfl) ⟨274740, by rfl⟩ : syracuseStep 732641 = 549481) B549481
theorem B732659 : Blo 487790 732659 := bstep (se 1 (by rfl) ⟨549494, by rfl⟩ : syracuseStep 732659 = 1098989) B1098989
theorem B732689 : Blo 487790 732689 := bstep (se 2 (by rfl) ⟨274758, by rfl⟩ : syracuseStep 732689 = 549517) B549517
theorem B732707 : Blo 487790 732707 := bstep (se 1 (by rfl) ⟨549530, by rfl⟩ : syracuseStep 732707 = 1099061) B1099061
theorem B732737 : Blo 487790 732737 := bstep (se 2 (by rfl) ⟨274776, by rfl⟩ : syracuseStep 732737 = 549553) B549553
theorem B732755 : Blo 487790 732755 := bstep (se 1 (by rfl) ⟨549566, by rfl⟩ : syracuseStep 732755 = 1099133) B1099133
theorem B732785 : Blo 487790 732785 := bstep (se 2 (by rfl) ⟨274794, by rfl⟩ : syracuseStep 732785 = 549589) B549589
theorem B732803 : Blo 487790 732803 := bstep (se 1 (by rfl) ⟨549602, by rfl⟩ : syracuseStep 732803 = 1099205) B1099205
theorem B732833 : Blo 487790 732833 := bstep (se 2 (by rfl) ⟨274812, by rfl⟩ : syracuseStep 732833 = 549625) B549625
theorem B732851 : Blo 487790 732851 := bstep (se 1 (by rfl) ⟨549638, by rfl⟩ : syracuseStep 732851 = 1099277) B1099277
theorem B732881 : Blo 487790 732881 := bstep (se 2 (by rfl) ⟨274830, by rfl⟩ : syracuseStep 732881 = 549661) B549661
theorem B732899 : Blo 487790 732899 := bstep (se 1 (by rfl) ⟨549674, by rfl⟩ : syracuseStep 732899 = 1099349) B1099349
theorem B732929 : Blo 487790 732929 := bstep (se 2 (by rfl) ⟨274848, by rfl⟩ : syracuseStep 732929 = 549697) B549697
theorem B732947 : Blo 487790 732947 := bstep (se 1 (by rfl) ⟨549710, by rfl⟩ : syracuseStep 732947 = 1099421) B1099421
theorem B995107 : Blo 487790 995107 := bstep (se 1 (by rfl) ⟨746330, by rfl⟩ : syracuseStep 995107 = 1492661) B1492661
theorem B732977 : Blo 487790 732977 := bstep (se 2 (by rfl) ⟨274866, by rfl⟩ : syracuseStep 732977 = 549733) B549733
theorem B732995 : Blo 487790 732995 := bstep (se 1 (by rfl) ⟨549746, by rfl⟩ : syracuseStep 732995 = 1099493) B1099493
theorem B1650509 : Blo 487790 1650509 := bstep (se 3 (by rfl) ⟨309470, by rfl⟩ : syracuseStep 1650509 = 618941) B618941
theorem B733025 : Blo 487790 733025 := bstep (se 2 (by rfl) ⟨274884, by rfl⟩ : syracuseStep 733025 = 549769) B549769
theorem B733043 : Blo 487790 733043 := bstep (se 1 (by rfl) ⟨549782, by rfl⟩ : syracuseStep 733043 = 1099565) B1099565
theorem B1650563 : Blo 487790 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B28225421 : Blo 487790 28225421 := bstep (se 3 (by rfl) ⟨5292266, by rfl⟩ : syracuseStep 28225421 = 10584533) B10584533
theorem B733073 : Blo 487790 733073 := bstep (se 2 (by rfl) ⟨274902, by rfl⟩ : syracuseStep 733073 = 549805) B549805
theorem B733091 : Blo 487790 733091 := bstep (se 1 (by rfl) ⟨549818, by rfl⟩ : syracuseStep 733091 = 1099637) B1099637
theorem B733121 : Blo 487790 733121 := bstep (se 2 (by rfl) ⟨274920, by rfl⟩ : syracuseStep 733121 = 549841) B549841
theorem B733139 : Blo 487790 733139 := bstep (se 1 (by rfl) ⟨549854, by rfl⟩ : syracuseStep 733139 = 1099709) B1099709
theorem B733169 : Blo 487790 733169 := bstep (se 2 (by rfl) ⟨274938, by rfl⟩ : syracuseStep 733169 = 549877) B549877
theorem B733187 : Blo 487790 733187 := bstep (se 1 (by rfl) ⟨549890, by rfl⟩ : syracuseStep 733187 = 1099781) B1099781
theorem B929809 : Blo 487790 929809 := bstep (se 2 (by rfl) ⟨348678, by rfl⟩ : syracuseStep 929809 = 697357) B697357
theorem B733217 : Blo 487790 733217 := bstep (se 2 (by rfl) ⟨274956, by rfl⟩ : syracuseStep 733217 = 549913) B549913
theorem B733235 : Blo 487790 733235 := bstep (se 1 (by rfl) ⟨549926, by rfl⟩ : syracuseStep 733235 = 1099853) B1099853
theorem B733265 : Blo 487790 733265 := bstep (se 2 (by rfl) ⟨274974, by rfl⟩ : syracuseStep 733265 = 549949) B549949
theorem B733283 : Blo 487790 733283 := bstep (se 1 (by rfl) ⟨549962, by rfl⟩ : syracuseStep 733283 = 1099925) B1099925
theorem B733313 : Blo 487790 733313 := bstep (se 2 (by rfl) ⟨274992, by rfl⟩ : syracuseStep 733313 = 549985) B549985
theorem B1486993 : Blo 487790 1486993 := bstep (se 2 (by rfl) ⟨557622, by rfl⟩ : syracuseStep 1486993 = 1115245) B1115245
theorem B1650833 : Blo 487790 1650833 := bstep (se 2 (by rfl) ⟨619062, by rfl⟩ : syracuseStep 1650833 = 1238125) B1238125
theorem B733331 : Blo 487790 733331 := bstep (se 1 (by rfl) ⟨549998, by rfl⟩ : syracuseStep 733331 = 1099997) B1099997
theorem B733361 : Blo 487790 733361 := bstep (se 2 (by rfl) ⟨275010, by rfl⟩ : syracuseStep 733361 = 550021) B550021
theorem B733379 : Blo 487790 733379 := bstep (se 1 (by rfl) ⟨550034, by rfl⟩ : syracuseStep 733379 = 1100069) B1100069
theorem B733409 : Blo 487790 733409 := bstep (se 2 (by rfl) ⟨275028, by rfl⟩ : syracuseStep 733409 = 550057) B550057
theorem B733427 : Blo 487790 733427 := bstep (se 1 (by rfl) ⟨550070, by rfl⟩ : syracuseStep 733427 = 1100141) B1100141
theorem B1257731 : Blo 487790 1257731 := bstep (se 1 (by rfl) ⟨943298, by rfl⟩ : syracuseStep 1257731 = 1886597) B1886597
theorem B733457 : Blo 487790 733457 := bstep (se 2 (by rfl) ⟨275046, by rfl⟩ : syracuseStep 733457 = 550093) B550093
theorem B733475 : Blo 487790 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B733505 : Blo 487790 733505 := bstep (se 2 (by rfl) ⟨275064, by rfl⟩ : syracuseStep 733505 = 550129) B550129
theorem B733523 : Blo 487790 733523 := bstep (se 1 (by rfl) ⟨550142, by rfl⟩ : syracuseStep 733523 = 1100285) B1100285
theorem B733553 : Blo 487790 733553 := bstep (se 2 (by rfl) ⟨275082, by rfl⟩ : syracuseStep 733553 = 550165) B550165
theorem B733571 : Blo 487790 733571 := bstep (se 1 (by rfl) ⟨550178, by rfl⟩ : syracuseStep 733571 = 1100357) B1100357
theorem B3715469 : Blo 487790 3715469 := bstep (se 3 (by rfl) ⟨696650, by rfl⟩ : syracuseStep 3715469 = 1393301) B1393301
theorem B733601 : Blo 487790 733601 := bstep (se 2 (by rfl) ⟨275100, by rfl⟩ : syracuseStep 733601 = 550201) B550201
theorem B733619 : Blo 487790 733619 := bstep (se 1 (by rfl) ⟨550214, by rfl⟩ : syracuseStep 733619 = 1100429) B1100429
theorem B733649 : Blo 487790 733649 := bstep (se 2 (by rfl) ⟨275118, by rfl⟩ : syracuseStep 733649 = 550237) B550237
theorem B733667 : Blo 487790 733667 := bstep (se 1 (by rfl) ⟨550250, by rfl⟩ : syracuseStep 733667 = 1100501) B1100501
theorem B733697 : Blo 487790 733697 := bstep (se 2 (by rfl) ⟨275136, by rfl⟩ : syracuseStep 733697 = 550273) B550273
theorem B733715 : Blo 487790 733715 := bstep (se 1 (by rfl) ⟨550286, by rfl⟩ : syracuseStep 733715 = 1100573) B1100573
theorem B733745 : Blo 487790 733745 := bstep (se 2 (by rfl) ⟨275154, by rfl⟩ : syracuseStep 733745 = 550309) B550309
theorem B733763 : Blo 487790 733763 := bstep (se 1 (by rfl) ⟨550322, by rfl⟩ : syracuseStep 733763 = 1100645) B1100645
theorem B733793 : Blo 487790 733793 := bstep (se 2 (by rfl) ⟨275172, by rfl⟩ : syracuseStep 733793 = 550345) B550345
theorem B2470499 : Blo 487790 2470499 := bstep (se 1 (by rfl) ⟨1852874, by rfl⟩ : syracuseStep 2470499 = 3705749) B3705749
theorem B733811 : Blo 487790 733811 := bstep (se 1 (by rfl) ⟨550358, by rfl⟩ : syracuseStep 733811 = 1100717) B1100717
theorem B5026445 : Blo 487790 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B733841 : Blo 487790 733841 := bstep (se 2 (by rfl) ⟨275190, by rfl⟩ : syracuseStep 733841 = 550381) B550381
theorem B733859 : Blo 487790 733859 := bstep (se 1 (by rfl) ⟨550394, by rfl⟩ : syracuseStep 733859 = 1100789) B1100789
theorem B1651373 : Blo 487790 1651373 := bstep (se 3 (by rfl) ⟨309632, by rfl⟩ : syracuseStep 1651373 = 619265) B619265
theorem B733889 : Blo 487790 733889 := bstep (se 2 (by rfl) ⟨275208, by rfl⟩ : syracuseStep 733889 = 550417) B550417
theorem B733907 : Blo 487790 733907 := bstep (se 1 (by rfl) ⟨550430, by rfl⟩ : syracuseStep 733907 = 1100861) B1100861
theorem B1651427 : Blo 487790 1651427 := bstep (se 1 (by rfl) ⟨1238570, by rfl⟩ : syracuseStep 1651427 = 2477141) B2477141
theorem B733937 : Blo 487790 733937 := bstep (se 2 (by rfl) ⟨275226, by rfl⟩ : syracuseStep 733937 = 550453) B550453
theorem B733955 : Blo 487790 733955 := bstep (se 1 (by rfl) ⟨550466, by rfl⟩ : syracuseStep 733955 = 1100933) B1100933
theorem B733985 : Blo 487790 733985 := bstep (se 2 (by rfl) ⟨275244, by rfl⟩ : syracuseStep 733985 = 550489) B550489
theorem B734003 : Blo 487790 734003 := bstep (se 1 (by rfl) ⟨550502, by rfl⟩ : syracuseStep 734003 = 1101005) B1101005
theorem B668497 : Blo 487790 668497 := bstep (se 2 (by rfl) ⟨250686, by rfl⟩ : syracuseStep 668497 = 501373) B501373
theorem B734033 : Blo 487790 734033 := bstep (se 2 (by rfl) ⟨275262, by rfl⟩ : syracuseStep 734033 = 550525) B550525
theorem B734051 : Blo 487790 734051 := bstep (se 1 (by rfl) ⟨550538, by rfl⟩ : syracuseStep 734051 = 1101077) B1101077
theorem B734081 : Blo 487790 734081 := bstep (se 2 (by rfl) ⟨275280, by rfl⟩ : syracuseStep 734081 = 550561) B550561
theorem B734099 : Blo 487790 734099 := bstep (se 1 (by rfl) ⟨550574, by rfl⟩ : syracuseStep 734099 = 1101149) B1101149
theorem B996259 : Blo 487790 996259 := bstep (se 1 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 996259 = 1494389) B1494389
theorem B734129 : Blo 487790 734129 := bstep (se 2 (by rfl) ⟨275298, by rfl⟩ : syracuseStep 734129 = 550597) B550597
theorem B734147 : Blo 487790 734147 := bstep (se 1 (by rfl) ⟨550610, by rfl⟩ : syracuseStep 734147 = 1101221) B1101221
theorem B734177 : Blo 487790 734177 := bstep (se 2 (by rfl) ⟨275316, by rfl⟩ : syracuseStep 734177 = 550633) B550633
theorem B1651697 : Blo 487790 1651697 := bstep (se 2 (by rfl) ⟨619386, by rfl⟩ : syracuseStep 1651697 = 1238773) B1238773
theorem B734195 : Blo 487790 734195 := bstep (se 1 (by rfl) ⟨550646, by rfl⟩ : syracuseStep 734195 = 1101293) B1101293
theorem B734225 : Blo 487790 734225 := bstep (se 2 (by rfl) ⟨275334, by rfl⟩ : syracuseStep 734225 = 550669) B550669
theorem B734243 : Blo 487790 734243 := bstep (se 1 (by rfl) ⟨550682, by rfl⟩ : syracuseStep 734243 = 1101365) B1101365
theorem B930865 : Blo 487790 930865 := bstep (se 2 (by rfl) ⟨349074, by rfl⟩ : syracuseStep 930865 = 698149) B698149
theorem B734273 : Blo 487790 734273 := bstep (se 2 (by rfl) ⟨275352, by rfl⟩ : syracuseStep 734273 = 550705) B550705
theorem B734291 : Blo 487790 734291 := bstep (se 1 (by rfl) ⟨550718, by rfl⟩ : syracuseStep 734291 = 1101437) B1101437
theorem B734321 : Blo 487790 734321 := bstep (se 2 (by rfl) ⟨275370, by rfl⟩ : syracuseStep 734321 = 550741) B550741
theorem B734339 : Blo 487790 734339 := bstep (se 1 (by rfl) ⟨550754, by rfl⟩ : syracuseStep 734339 = 1101509) B1101509
theorem B734369 : Blo 487790 734369 := bstep (se 2 (by rfl) ⟨275388, by rfl⟩ : syracuseStep 734369 = 550777) B550777
theorem B734387 : Blo 487790 734387 := bstep (se 1 (by rfl) ⟨550790, by rfl⟩ : syracuseStep 734387 = 1101581) B1101581
theorem B734417 : Blo 487790 734417 := bstep (se 2 (by rfl) ⟨275406, by rfl⟩ : syracuseStep 734417 = 550813) B550813
theorem B734435 : Blo 487790 734435 := bstep (se 1 (by rfl) ⟨550826, by rfl⟩ : syracuseStep 734435 = 1101653) B1101653
theorem B10073315 : Blo 487790 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B734465 : Blo 487790 734465 := bstep (se 2 (by rfl) ⟨275424, by rfl⟩ : syracuseStep 734465 = 550849) B550849
theorem B734483 : Blo 487790 734483 := bstep (se 1 (by rfl) ⟨550862, by rfl⟩ : syracuseStep 734483 = 1101725) B1101725
theorem B734513 : Blo 487790 734513 := bstep (se 2 (by rfl) ⟨275442, by rfl⟩ : syracuseStep 734513 = 550885) B550885
theorem B734531 : Blo 487790 734531 := bstep (se 1 (by rfl) ⟨550898, by rfl⟩ : syracuseStep 734531 = 1101797) B1101797
theorem B734561 : Blo 487790 734561 := bstep (se 2 (by rfl) ⟨275460, by rfl⟩ : syracuseStep 734561 = 550921) B550921
theorem B734579 : Blo 487790 734579 := bstep (se 1 (by rfl) ⟨550934, by rfl⟩ : syracuseStep 734579 = 1101869) B1101869
theorem B2471309 : Blo 487790 2471309 := bstep (se 3 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 2471309 = 926741) B926741
theorem B734609 : Blo 487790 734609 := bstep (se 2 (by rfl) ⟨275478, by rfl⟩ : syracuseStep 734609 = 550957) B550957
theorem B734627 : Blo 487790 734627 := bstep (se 1 (by rfl) ⟨550970, by rfl⟩ : syracuseStep 734627 = 1101941) B1101941
theorem B1914275 : Blo 487790 1914275 := bstep (se 1 (by rfl) ⟨1435706, by rfl⟩ : syracuseStep 1914275 = 2871413) B2871413
theorem B734657 : Blo 487790 734657 := bstep (se 2 (by rfl) ⟨275496, by rfl⟩ : syracuseStep 734657 = 550993) B550993
theorem B931267 : Blo 487790 931267 := bstep (se 1 (by rfl) ⟨698450, by rfl⟩ : syracuseStep 931267 = 1396901) B1396901
theorem B734675 : Blo 487790 734675 := bstep (se 1 (by rfl) ⟨551006, by rfl⟩ : syracuseStep 734675 = 1102013) B1102013
theorem B734705 : Blo 487790 734705 := bstep (se 2 (by rfl) ⟨275514, by rfl⟩ : syracuseStep 734705 = 551029) B551029
theorem B931313 : Blo 487790 931313 := bstep (se 2 (by rfl) ⟨349242, by rfl⟩ : syracuseStep 931313 = 698485) B698485
theorem B734723 : Blo 487790 734723 := bstep (se 1 (by rfl) ⟨551042, by rfl⟩ : syracuseStep 734723 = 1102085) B1102085
theorem B1652237 : Blo 487790 1652237 := bstep (se 3 (by rfl) ⟨309794, by rfl⟩ : syracuseStep 1652237 = 619589) B619589
theorem B734753 : Blo 487790 734753 := bstep (se 2 (by rfl) ⟨275532, by rfl⟩ : syracuseStep 734753 = 551065) B551065
theorem B734771 : Blo 487790 734771 := bstep (se 1 (by rfl) ⟨551078, by rfl⟩ : syracuseStep 734771 = 1102157) B1102157
theorem B1652291 : Blo 487790 1652291 := bstep (se 1 (by rfl) ⟨1239218, by rfl⟩ : syracuseStep 1652291 = 2478437) B2478437
theorem B734801 : Blo 487790 734801 := bstep (se 2 (by rfl) ⟨275550, by rfl⟩ : syracuseStep 734801 = 551101) B551101
theorem B734819 : Blo 487790 734819 := bstep (se 1 (by rfl) ⟨551114, by rfl⟩ : syracuseStep 734819 = 1102229) B1102229
theorem B1390193 : Blo 487790 1390193 := bstep (se 2 (by rfl) ⟨521322, by rfl⟩ : syracuseStep 1390193 = 1042645) B1042645
theorem B734849 : Blo 487790 734849 := bstep (se 2 (by rfl) ⟨275568, by rfl⟩ : syracuseStep 734849 = 551137) B551137
theorem B734867 : Blo 487790 734867 := bstep (se 1 (by rfl) ⟨551150, by rfl⟩ : syracuseStep 734867 = 1102301) B1102301
theorem B734897 : Blo 487790 734897 := bstep (se 2 (by rfl) ⟨275586, by rfl⟩ : syracuseStep 734897 = 551173) B551173
theorem B734915 : Blo 487790 734915 := bstep (se 1 (by rfl) ⟨551186, by rfl⟩ : syracuseStep 734915 = 1102373) B1102373
theorem B734945 : Blo 487790 734945 := bstep (se 2 (by rfl) ⟨275604, by rfl⟩ : syracuseStep 734945 = 551209) B551209
theorem B734963 : Blo 487790 734963 := bstep (se 1 (by rfl) ⟨551222, by rfl⟩ : syracuseStep 734963 = 1102445) B1102445
theorem B734993 : Blo 487790 734993 := bstep (se 2 (by rfl) ⟨275622, by rfl⟩ : syracuseStep 734993 = 551245) B551245
theorem B931601 : Blo 487790 931601 := bstep (se 2 (by rfl) ⟨349350, by rfl⟩ : syracuseStep 931601 = 698701) B698701
theorem B3389219 : Blo 487790 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B735011 : Blo 487790 735011 := bstep (se 1 (by rfl) ⟨551258, by rfl⟩ : syracuseStep 735011 = 1102517) B1102517
theorem B1390385 : Blo 487790 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B12531509 : Blo 487790 12531509 := bstep (se 5 (by rfl) ⟨587414, by rfl⟩ : syracuseStep 12531509 = 1174829) B1174829
theorem B735041 : Blo 487790 735041 := bstep (se 2 (by rfl) ⟨275640, by rfl⟩ : syracuseStep 735041 = 551281) B551281
theorem B1652561 : Blo 487790 1652561 := bstep (se 2 (by rfl) ⟨619710, by rfl⟩ : syracuseStep 1652561 = 1239421) B1239421
theorem B735059 : Blo 487790 735059 := bstep (se 1 (by rfl) ⟨551294, by rfl⟩ : syracuseStep 735059 = 1102589) B1102589
theorem B735089 : Blo 487790 735089 := bstep (se 2 (by rfl) ⟨275658, by rfl⟩ : syracuseStep 735089 = 551317) B551317
theorem B767873 : Blo 487790 767873 := bstep (se 2 (by rfl) ⟨287952, by rfl⟩ : syracuseStep 767873 = 575905) B575905
theorem B735107 : Blo 487790 735107 := bstep (se 1 (by rfl) ⟨551330, by rfl⟩ : syracuseStep 735107 = 1102661) B1102661
theorem B735137 : Blo 487790 735137 := bstep (se 2 (by rfl) ⟨275676, by rfl⟩ : syracuseStep 735137 = 551353) B551353
theorem B735155 : Blo 487790 735155 := bstep (se 1 (by rfl) ⟨551366, by rfl⟩ : syracuseStep 735155 = 1102733) B1102733
theorem B735185 : Blo 487790 735185 := bstep (se 2 (by rfl) ⟨275694, by rfl⟩ : syracuseStep 735185 = 551389) B551389
theorem B735203 : Blo 487790 735203 := bstep (se 1 (by rfl) ⟨551402, by rfl⟩ : syracuseStep 735203 = 1102805) B1102805
theorem B735233 : Blo 487790 735233 := bstep (se 2 (by rfl) ⟨275712, by rfl⟩ : syracuseStep 735233 = 551425) B551425
theorem B1587217 : Blo 487790 1587217 := bstep (se 2 (by rfl) ⟨595206, by rfl⟩ : syracuseStep 1587217 = 1190413) B1190413
theorem B735251 : Blo 487790 735251 := bstep (se 1 (by rfl) ⟨551438, by rfl⟩ : syracuseStep 735251 = 1102877) B1102877
theorem B735281 : Blo 487790 735281 := bstep (se 2 (by rfl) ⟨275730, by rfl⟩ : syracuseStep 735281 = 551461) B551461
theorem B735299 : Blo 487790 735299 := bstep (se 1 (by rfl) ⟨551474, by rfl⟩ : syracuseStep 735299 = 1102949) B1102949
theorem B735329 : Blo 487790 735329 := bstep (se 2 (by rfl) ⟨275748, by rfl⟩ : syracuseStep 735329 = 551497) B551497
theorem B735347 : Blo 487790 735347 := bstep (se 1 (by rfl) ⟨551510, by rfl⟩ : syracuseStep 735347 = 1103021) B1103021
theorem B735377 : Blo 487790 735377 := bstep (se 2 (by rfl) ⟨275766, by rfl⟩ : syracuseStep 735377 = 551533) B551533
theorem B735395 : Blo 487790 735395 := bstep (se 1 (by rfl) ⟨551546, by rfl⟩ : syracuseStep 735395 = 1103093) B1103093
theorem B735425 : Blo 487790 735425 := bstep (se 2 (by rfl) ⟨275784, by rfl⟩ : syracuseStep 735425 = 551569) B551569
theorem B735443 : Blo 487790 735443 := bstep (se 1 (by rfl) ⟨551582, by rfl⟩ : syracuseStep 735443 = 1103165) B1103165
theorem B735473 : Blo 487790 735473 := bstep (se 2 (by rfl) ⟨275802, by rfl⟩ : syracuseStep 735473 = 551605) B551605
theorem B735491 : Blo 487790 735491 := bstep (se 1 (by rfl) ⟨551618, by rfl⟩ : syracuseStep 735491 = 1103237) B1103237
theorem B735521 : Blo 487790 735521 := bstep (se 2 (by rfl) ⟨275820, by rfl⟩ : syracuseStep 735521 = 551641) B551641
theorem B735539 : Blo 487790 735539 := bstep (se 1 (by rfl) ⟨551654, by rfl⟩ : syracuseStep 735539 = 1103309) B1103309
theorem B735569 : Blo 487790 735569 := bstep (se 2 (by rfl) ⟨275838, by rfl⟩ : syracuseStep 735569 = 551677) B551677
theorem B735587 : Blo 487790 735587 := bstep (se 1 (by rfl) ⟨551690, by rfl⟩ : syracuseStep 735587 = 1103381) B1103381
theorem B1653101 : Blo 487790 1653101 := bstep (se 3 (by rfl) ⟨309956, by rfl⟩ : syracuseStep 1653101 = 619913) B619913
theorem B1325425 : Blo 487790 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B735617 : Blo 487790 735617 := bstep (se 2 (by rfl) ⟨275856, by rfl⟩ : syracuseStep 735617 = 551713) B551713
theorem B735635 : Blo 487790 735635 := bstep (se 1 (by rfl) ⟨551726, by rfl⟩ : syracuseStep 735635 = 1103453) B1103453
theorem B1653155 : Blo 487790 1653155 := bstep (se 1 (by rfl) ⟨1239866, by rfl⟩ : syracuseStep 1653155 = 2479733) B2479733
theorem B1325489 : Blo 487790 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B735665 : Blo 487790 735665 := bstep (se 2 (by rfl) ⟨275874, by rfl⟩ : syracuseStep 735665 = 551749) B551749
theorem B735683 : Blo 487790 735683 := bstep (se 1 (by rfl) ⟨551762, by rfl⟩ : syracuseStep 735683 = 1103525) B1103525
theorem B670177 : Blo 487790 670177 := bstep (se 2 (by rfl) ⟨251316, by rfl⟩ : syracuseStep 670177 = 502633) B502633
theorem B735713 : Blo 487790 735713 := bstep (se 2 (by rfl) ⟨275892, by rfl⟩ : syracuseStep 735713 = 551785) B551785
theorem B932323 : Blo 487790 932323 := bstep (se 1 (by rfl) ⟨699242, by rfl⟩ : syracuseStep 932323 = 1398485) B1398485
theorem B735731 : Blo 487790 735731 := bstep (se 1 (by rfl) ⟨551798, by rfl⟩ : syracuseStep 735731 = 1103597) B1103597
theorem B735761 : Blo 487790 735761 := bstep (se 2 (by rfl) ⟨275910, by rfl⟩ : syracuseStep 735761 = 551821) B551821
theorem B735779 : Blo 487790 735779 := bstep (se 1 (by rfl) ⟨551834, by rfl⟩ : syracuseStep 735779 = 1103669) B1103669
theorem B735809 : Blo 487790 735809 := bstep (se 2 (by rfl) ⟨275928, by rfl⟩ : syracuseStep 735809 = 551857) B551857
theorem B735827 : Blo 487790 735827 := bstep (se 1 (by rfl) ⟨551870, by rfl⟩ : syracuseStep 735827 = 1103741) B1103741
theorem B735857 : Blo 487790 735857 := bstep (se 2 (by rfl) ⟨275946, by rfl⟩ : syracuseStep 735857 = 551893) B551893
theorem B735875 : Blo 487790 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B735905 : Blo 487790 735905 := bstep (se 2 (by rfl) ⟨275964, by rfl⟩ : syracuseStep 735905 = 551929) B551929
theorem B1653425 : Blo 487790 1653425 := bstep (se 2 (by rfl) ⟨620034, by rfl⟩ : syracuseStep 1653425 = 1240069) B1240069
theorem B735923 : Blo 487790 735923 := bstep (se 1 (by rfl) ⟨551942, by rfl⟩ : syracuseStep 735923 = 1103885) B1103885
theorem B735953 : Blo 487790 735953 := bstep (se 2 (by rfl) ⟨275982, by rfl⟩ : syracuseStep 735953 = 551965) B551965
theorem B735971 : Blo 487790 735971 := bstep (se 1 (by rfl) ⟨551978, by rfl⟩ : syracuseStep 735971 = 1103957) B1103957
theorem B736001 : Blo 487790 736001 := bstep (se 2 (by rfl) ⟨276000, by rfl⟩ : syracuseStep 736001 = 552001) B552001
theorem B1391377 : Blo 487790 1391377 := bstep (se 2 (by rfl) ⟨521766, by rfl⟩ : syracuseStep 1391377 = 1043533) B1043533
theorem B736019 : Blo 487790 736019 := bstep (se 1 (by rfl) ⟨552014, by rfl⟩ : syracuseStep 736019 = 1104029) B1104029
theorem B736049 : Blo 487790 736049 := bstep (se 2 (by rfl) ⟨276018, by rfl⟩ : syracuseStep 736049 = 552037) B552037
theorem B736067 : Blo 487790 736067 := bstep (se 1 (by rfl) ⟨552050, by rfl⟩ : syracuseStep 736067 = 1104101) B1104101
theorem B2800453 : Blo 487790 2800453 := bstep (se 4 (by rfl) ⟨262542, by rfl⟩ : syracuseStep 2800453 = 525085) B525085
theorem B736097 : Blo 487790 736097 := bstep (se 2 (by rfl) ⟨276036, by rfl⟩ : syracuseStep 736097 = 552073) B552073
theorem B736115 : Blo 487790 736115 := bstep (se 1 (by rfl) ⟨552086, by rfl⟩ : syracuseStep 736115 = 1104173) B1104173
theorem B736145 : Blo 487790 736145 := bstep (se 2 (by rfl) ⟨276054, by rfl⟩ : syracuseStep 736145 = 552109) B552109
theorem B736163 : Blo 487790 736163 := bstep (se 1 (by rfl) ⟨552122, by rfl⟩ : syracuseStep 736163 = 1104245) B1104245
theorem B932771 : Blo 487790 932771 := bstep (se 1 (by rfl) ⟨699578, by rfl⟩ : syracuseStep 932771 = 1399157) B1399157
theorem B1981361 : Blo 487790 1981361 := bstep (se 2 (by rfl) ⟨743010, by rfl⟩ : syracuseStep 1981361 = 1486021) B1486021
theorem B736193 : Blo 487790 736193 := bstep (se 2 (by rfl) ⟨276072, by rfl⟩ : syracuseStep 736193 = 552145) B552145
theorem B736211 : Blo 487790 736211 := bstep (se 1 (by rfl) ⟨552158, by rfl⟩ : syracuseStep 736211 = 1104317) B1104317
theorem B736241 : Blo 487790 736241 := bstep (se 2 (by rfl) ⟨276090, by rfl⟩ : syracuseStep 736241 = 552181) B552181
theorem B736259 : Blo 487790 736259 := bstep (se 1 (by rfl) ⟨552194, by rfl⟩ : syracuseStep 736259 = 1104389) B1104389
theorem B3521549 : Blo 487790 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B736289 : Blo 487790 736289 := bstep (se 2 (by rfl) ⟨276108, by rfl⟩ : syracuseStep 736289 = 552217) B552217
theorem B1391651 : Blo 487790 1391651 := bstep (se 1 (by rfl) ⟨1043738, by rfl⟩ : syracuseStep 1391651 = 2087477) B2087477
theorem B736307 : Blo 487790 736307 := bstep (se 1 (by rfl) ⟨552230, by rfl⟩ : syracuseStep 736307 = 1104461) B1104461
theorem B736337 : Blo 487790 736337 := bstep (se 2 (by rfl) ⟨276126, by rfl⟩ : syracuseStep 736337 = 552253) B552253
theorem B736355 : Blo 487790 736355 := bstep (se 1 (by rfl) ⟨552266, by rfl⟩ : syracuseStep 736355 = 1104533) B1104533
theorem B736385 : Blo 487790 736385 := bstep (se 2 (by rfl) ⟨276144, by rfl⟩ : syracuseStep 736385 = 552289) B552289
theorem B736403 : Blo 487790 736403 := bstep (se 1 (by rfl) ⟨552302, by rfl⟩ : syracuseStep 736403 = 1104605) B1104605
theorem B736433 : Blo 487790 736433 := bstep (se 2 (by rfl) ⟨276162, by rfl⟩ : syracuseStep 736433 = 552325) B552325
theorem B736451 : Blo 487790 736451 := bstep (se 1 (by rfl) ⟨552338, by rfl⟩ : syracuseStep 736451 = 1104677) B1104677
theorem B933059 : Blo 487790 933059 := bstep (se 1 (by rfl) ⟨699794, by rfl⟩ : syracuseStep 933059 = 1399589) B1399589
theorem B1653965 : Blo 487790 1653965 := bstep (se 3 (by rfl) ⟨310118, by rfl⟩ : syracuseStep 1653965 = 620237) B620237
theorem B736481 : Blo 487790 736481 := bstep (se 2 (by rfl) ⟨276180, by rfl⟩ : syracuseStep 736481 = 552361) B552361
theorem B1391843 : Blo 487790 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B3718385 : Blo 487790 3718385 := bstep (se 2 (by rfl) ⟨1394394, by rfl⟩ : syracuseStep 3718385 = 2788789) B2788789
theorem B736499 : Blo 487790 736499 := bstep (se 1 (by rfl) ⟨552374, by rfl⟩ : syracuseStep 736499 = 1104749) B1104749
theorem B1654019 : Blo 487790 1654019 := bstep (se 1 (by rfl) ⟨1240514, by rfl⟩ : syracuseStep 1654019 = 2481029) B2481029
theorem B736529 : Blo 487790 736529 := bstep (se 2 (by rfl) ⟨276198, by rfl⟩ : syracuseStep 736529 = 552397) B552397
theorem B736547 : Blo 487790 736547 := bstep (se 1 (by rfl) ⟨552410, by rfl⟩ : syracuseStep 736547 = 1104821) B1104821
theorem B736577 : Blo 487790 736577 := bstep (se 2 (by rfl) ⟨276216, by rfl⟩ : syracuseStep 736577 = 552433) B552433
theorem B736595 : Blo 487790 736595 := bstep (se 1 (by rfl) ⟨552446, by rfl⟩ : syracuseStep 736595 = 1104893) B1104893
theorem B736625 : Blo 487790 736625 := bstep (se 2 (by rfl) ⟨276234, by rfl⟩ : syracuseStep 736625 = 552469) B552469
theorem B736643 : Blo 487790 736643 := bstep (se 1 (by rfl) ⟨552482, by rfl⟩ : syracuseStep 736643 = 1104965) B1104965
theorem B736673 : Blo 487790 736673 := bstep (se 2 (by rfl) ⟨276252, by rfl⟩ : syracuseStep 736673 = 552505) B552505
theorem B736691 : Blo 487790 736691 := bstep (se 1 (by rfl) ⟨552518, by rfl⟩ : syracuseStep 736691 = 1105037) B1105037
theorem B736721 : Blo 487790 736721 := bstep (se 2 (by rfl) ⟨276270, by rfl⟩ : syracuseStep 736721 = 552541) B552541
theorem B736739 : Blo 487790 736739 := bstep (se 1 (by rfl) ⟨552554, by rfl⟩ : syracuseStep 736739 = 1105109) B1105109
theorem B736769 : Blo 487790 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B4472333 : Blo 487790 4472333 := bstep (se 3 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 4472333 = 1677125) B1677125
theorem B1654289 : Blo 487790 1654289 := bstep (se 2 (by rfl) ⟨620358, by rfl⟩ : syracuseStep 1654289 = 1240717) B1240717
theorem B736787 : Blo 487790 736787 := bstep (se 1 (by rfl) ⟨552590, by rfl⟩ : syracuseStep 736787 = 1105181) B1105181
theorem B736817 : Blo 487790 736817 := bstep (se 2 (by rfl) ⟨276306, by rfl⟩ : syracuseStep 736817 = 552613) B552613
theorem B736835 : Blo 487790 736835 := bstep (se 1 (by rfl) ⟨552626, by rfl⟩ : syracuseStep 736835 = 1105253) B1105253
theorem B736865 : Blo 487790 736865 := bstep (se 2 (by rfl) ⟨276324, by rfl⟩ : syracuseStep 736865 = 552649) B552649
theorem B1326701 : Blo 487790 1326701 := bstep (se 3 (by rfl) ⟨248756, by rfl⟩ : syracuseStep 1326701 = 497513) B497513
theorem B736883 : Blo 487790 736883 := bstep (se 1 (by rfl) ⟨552662, by rfl⟩ : syracuseStep 736883 = 1105325) B1105325
theorem B736913 : Blo 487790 736913 := bstep (se 2 (by rfl) ⟨276342, by rfl⟩ : syracuseStep 736913 = 552685) B552685
theorem B736931 : Blo 487790 736931 := bstep (se 1 (by rfl) ⟨552698, by rfl⟩ : syracuseStep 736931 = 1105397) B1105397
theorem B736961 : Blo 487790 736961 := bstep (se 2 (by rfl) ⟨276360, by rfl⟩ : syracuseStep 736961 = 552721) B552721
theorem B736979 : Blo 487790 736979 := bstep (se 1 (by rfl) ⟨552734, by rfl⟩ : syracuseStep 736979 = 1105469) B1105469
theorem B737009 : Blo 487790 737009 := bstep (se 2 (by rfl) ⟨276378, by rfl⟩ : syracuseStep 737009 = 552757) B552757
theorem B737027 : Blo 487790 737027 := bstep (se 1 (by rfl) ⟨552770, by rfl⟩ : syracuseStep 737027 = 1105541) B1105541
theorem B737057 : Blo 487790 737057 := bstep (se 2 (by rfl) ⟨276396, by rfl⟩ : syracuseStep 737057 = 552793) B552793
theorem B638755 : Blo 487790 638755 := bstep (se 1 (by rfl) ⟨479066, by rfl⟩ : syracuseStep 638755 = 958133) B958133
theorem B737075 : Blo 487790 737075 := bstep (se 1 (by rfl) ⟨552806, by rfl⟩ : syracuseStep 737075 = 1105613) B1105613
theorem B737105 : Blo 487790 737105 := bstep (se 2 (by rfl) ⟨276414, by rfl⟩ : syracuseStep 737105 = 552829) B552829
theorem B3129187 : Blo 487790 3129187 := bstep (se 1 (by rfl) ⟨2346890, by rfl⟩ : syracuseStep 3129187 = 4693781) B4693781
theorem B737123 : Blo 487790 737123 := bstep (se 1 (by rfl) ⟨552842, by rfl⟩ : syracuseStep 737123 = 1105685) B1105685
theorem B1097585 : Blo 487790 1097585 := bstep (se 2 (by rfl) ⟨411594, by rfl⟩ : syracuseStep 1097585 = 823189) B823189
theorem B737153 : Blo 487790 737153 := bstep (se 2 (by rfl) ⟨276432, by rfl⟩ : syracuseStep 737153 = 552865) B552865
theorem B1097603 : Blo 487790 1097603 := bstep (se 1 (by rfl) ⟨823202, by rfl⟩ : syracuseStep 1097603 = 1646405) B1646405
theorem B737171 : Blo 487790 737171 := bstep (se 1 (by rfl) ⟨552878, by rfl⟩ : syracuseStep 737171 = 1105757) B1105757
theorem B737201 : Blo 487790 737201 := bstep (se 2 (by rfl) ⟨276450, by rfl⟩ : syracuseStep 737201 = 552901) B552901
theorem B737219 : Blo 487790 737219 := bstep (se 1 (by rfl) ⟨552914, by rfl⟩ : syracuseStep 737219 = 1105829) B1105829
theorem B737249 : Blo 487790 737249 := bstep (se 2 (by rfl) ⟨276468, by rfl⟩ : syracuseStep 737249 = 552937) B552937
theorem B11321315 : Blo 487790 11321315 := bstep (se 1 (by rfl) ⟨8490986, by rfl⟩ : syracuseStep 11321315 = 16981973) B16981973
theorem B737267 : Blo 487790 737267 := bstep (se 1 (by rfl) ⟨552950, by rfl⟩ : syracuseStep 737267 = 1105901) B1105901
theorem B1392653 : Blo 487790 1392653 := bstep (se 3 (by rfl) ⟨261122, by rfl⟩ : syracuseStep 1392653 = 522245) B522245
theorem B737297 : Blo 487790 737297 := bstep (se 2 (by rfl) ⟨276486, by rfl⟩ : syracuseStep 737297 = 552973) B552973
theorem B737315 : Blo 487790 737315 := bstep (se 1 (by rfl) ⟨552986, by rfl⟩ : syracuseStep 737315 = 1105973) B1105973
theorem B1654829 : Blo 487790 1654829 := bstep (se 3 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 1654829 = 620561) B620561
theorem B737345 : Blo 487790 737345 := bstep (se 2 (by rfl) ⟨276504, by rfl⟩ : syracuseStep 737345 = 553009) B553009
theorem B737363 : Blo 487790 737363 := bstep (se 1 (by rfl) ⟨553022, by rfl⟩ : syracuseStep 737363 = 1106045) B1106045
theorem B1654883 : Blo 487790 1654883 := bstep (se 1 (by rfl) ⟨1241162, by rfl⟩ : syracuseStep 1654883 = 2482325) B2482325
theorem B737393 : Blo 487790 737393 := bstep (se 2 (by rfl) ⟨276522, by rfl⟩ : syracuseStep 737393 = 553045) B553045
theorem B737411 : Blo 487790 737411 := bstep (se 1 (by rfl) ⟨553058, by rfl⟩ : syracuseStep 737411 = 1106117) B1106117
theorem B1097873 : Blo 487790 1097873 := bstep (se 2 (by rfl) ⟨411702, by rfl⟩ : syracuseStep 1097873 = 823405) B823405
theorem B737441 : Blo 487790 737441 := bstep (se 2 (by rfl) ⟨276540, by rfl⟩ : syracuseStep 737441 = 553081) B553081
theorem B1097891 : Blo 487790 1097891 := bstep (se 1 (by rfl) ⟨823418, by rfl⟩ : syracuseStep 1097891 = 1646837) B1646837
theorem B737459 : Blo 487790 737459 := bstep (se 1 (by rfl) ⟨553094, by rfl⟩ : syracuseStep 737459 = 1106189) B1106189
theorem B1392835 : Blo 487790 1392835 := bstep (se 1 (by rfl) ⟨1044626, by rfl⟩ : syracuseStep 1392835 = 2089253) B2089253
theorem B737489 : Blo 487790 737489 := bstep (se 2 (by rfl) ⟨276558, by rfl⟩ : syracuseStep 737489 = 553117) B553117
theorem B737507 : Blo 487790 737507 := bstep (se 1 (by rfl) ⟨553130, by rfl⟩ : syracuseStep 737507 = 1106261) B1106261
theorem B2474225 : Blo 487790 2474225 := bstep (se 2 (by rfl) ⟨927834, by rfl⟩ : syracuseStep 2474225 = 1855669) B1855669
theorem B737537 : Blo 487790 737537 := bstep (se 2 (by rfl) ⟨276576, by rfl⟩ : syracuseStep 737537 = 553153) B553153
theorem B737555 : Blo 487790 737555 := bstep (se 1 (by rfl) ⟨553166, by rfl⟩ : syracuseStep 737555 = 1106333) B1106333
theorem B737585 : Blo 487790 737585 := bstep (se 2 (by rfl) ⟨276594, by rfl⟩ : syracuseStep 737585 = 553189) B553189
theorem B737603 : Blo 487790 737603 := bstep (se 1 (by rfl) ⟨553202, by rfl⟩ : syracuseStep 737603 = 1106405) B1106405
theorem B737633 : Blo 487790 737633 := bstep (se 2 (by rfl) ⟨276612, by rfl⟩ : syracuseStep 737633 = 553225) B553225
theorem B1655153 : Blo 487790 1655153 := bstep (se 2 (by rfl) ⟨620682, by rfl⟩ : syracuseStep 1655153 = 1241365) B1241365
theorem B4309361 : Blo 487790 4309361 := bstep (se 2 (by rfl) ⟨1616010, by rfl⟩ : syracuseStep 4309361 = 3232021) B3232021
theorem B737651 : Blo 487790 737651 := bstep (se 1 (by rfl) ⟨553238, by rfl⟩ : syracuseStep 737651 = 1106477) B1106477
theorem B737681 : Blo 487790 737681 := bstep (se 2 (by rfl) ⟨276630, by rfl⟩ : syracuseStep 737681 = 553261) B553261
theorem B1098161 : Blo 487790 1098161 := bstep (se 2 (by rfl) ⟨411810, by rfl⟩ : syracuseStep 1098161 = 823621) B823621
theorem B1098179 : Blo 487790 1098179 := bstep (se 1 (by rfl) ⟨823634, by rfl⟩ : syracuseStep 1098179 = 1647269) B1647269
theorem B1393325 : Blo 487790 1393325 := bstep (se 3 (by rfl) ⟨261248, by rfl⟩ : syracuseStep 1393325 = 522497) B522497
theorem B1098449 : Blo 487790 1098449 := bstep (se 2 (by rfl) ⟨411918, by rfl⟩ : syracuseStep 1098449 = 823837) B823837
theorem B1098467 : Blo 487790 1098467 := bstep (se 1 (by rfl) ⟨823850, by rfl⟩ : syracuseStep 1098467 = 1647701) B1647701
theorem B1655693 : Blo 487790 1655693 := bstep (se 3 (by rfl) ⟨310442, by rfl⟩ : syracuseStep 1655693 = 620885) B620885
theorem B1655747 : Blo 487790 1655747 := bstep (se 1 (by rfl) ⟨1241810, by rfl⟩ : syracuseStep 1655747 = 2483621) B2483621
theorem B1098737 : Blo 487790 1098737 := bstep (se 2 (by rfl) ⟨412026, by rfl⟩ : syracuseStep 1098737 = 824053) B824053
theorem B1098755 : Blo 487790 1098755 := bstep (se 1 (by rfl) ⟨824066, by rfl⟩ : syracuseStep 1098755 = 1648133) B1648133
theorem B3130417 : Blo 487790 3130417 := bstep (se 2 (by rfl) ⟨1173906, by rfl⟩ : syracuseStep 3130417 = 2347813) B2347813
theorem B1656017 : Blo 487790 1656017 := bstep (se 2 (by rfl) ⟨621006, by rfl⟩ : syracuseStep 1656017 = 1242013) B1242013
theorem B1099025 : Blo 487790 1099025 := bstep (se 2 (by rfl) ⟨412134, by rfl⟩ : syracuseStep 1099025 = 824269) B824269
theorem B1099043 : Blo 487790 1099043 := bstep (se 1 (by rfl) ⟨824282, by rfl⟩ : syracuseStep 1099043 = 1648565) B1648565
theorem B836995 : Blo 487790 836995 := bstep (se 1 (by rfl) ⟨627746, by rfl⟩ : syracuseStep 836995 = 1255493) B1255493
theorem B1099313 : Blo 487790 1099313 := bstep (se 2 (by rfl) ⟨412242, by rfl⟩ : syracuseStep 1099313 = 824485) B824485
theorem B1099331 : Blo 487790 1099331 := bstep (se 1 (by rfl) ⟨824498, by rfl⟩ : syracuseStep 1099331 = 1648997) B1648997
theorem B1361485 : Blo 487790 1361485 := bstep (se 3 (by rfl) ⟨255278, by rfl⟩ : syracuseStep 1361485 = 510557) B510557
theorem B1853027 : Blo 487790 1853027 := bstep (se 1 (by rfl) ⟨1389770, by rfl⟩ : syracuseStep 1853027 = 2779541) B2779541
theorem B1590929 : Blo 487790 1590929 := bstep (se 2 (by rfl) ⟨596598, by rfl⟩ : syracuseStep 1590929 = 1193197) B1193197
theorem B2475683 : Blo 487790 2475683 := bstep (se 1 (by rfl) ⟨1856762, by rfl⟩ : syracuseStep 2475683 = 3713525) B3713525
theorem B2344625 : Blo 487790 2344625 := bstep (se 2 (by rfl) ⟨879234, by rfl⟩ : syracuseStep 2344625 = 1758469) B1758469
theorem B1656557 : Blo 487790 1656557 := bstep (se 3 (by rfl) ⟨310604, by rfl⟩ : syracuseStep 1656557 = 621209) B621209
theorem B4835057 : Blo 487790 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B1656611 : Blo 487790 1656611 := bstep (se 1 (by rfl) ⟨1242458, by rfl⟩ : syracuseStep 1656611 = 2484917) B2484917
theorem B1394509 : Blo 487790 1394509 := bstep (se 3 (by rfl) ⟨261470, by rfl⟩ : syracuseStep 1394509 = 522941) B522941
theorem B1099601 : Blo 487790 1099601 := bstep (se 2 (by rfl) ⟨412350, by rfl⟩ : syracuseStep 1099601 = 824701) B824701
theorem B837473 : Blo 487790 837473 := bstep (se 2 (by rfl) ⟨314052, by rfl⟩ : syracuseStep 837473 = 628105) B628105
theorem B1099619 : Blo 487790 1099619 := bstep (se 1 (by rfl) ⟨824714, by rfl⟩ : syracuseStep 1099619 = 1649429) B1649429
theorem B1656881 : Blo 487790 1656881 := bstep (se 2 (by rfl) ⟨621330, by rfl⟩ : syracuseStep 1656881 = 1242661) B1242661
theorem B1099889 : Blo 487790 1099889 := bstep (se 2 (by rfl) ⟨412458, by rfl⟩ : syracuseStep 1099889 = 824917) B824917
theorem B1099907 : Blo 487790 1099907 := bstep (se 1 (by rfl) ⟨824930, by rfl⟩ : syracuseStep 1099907 = 1649861) B1649861
theorem B1100177 : Blo 487790 1100177 := bstep (se 2 (by rfl) ⟨412566, by rfl⟩ : syracuseStep 1100177 = 825133) B825133
theorem B1100195 : Blo 487790 1100195 := bstep (se 1 (by rfl) ⟨825146, by rfl⟩ : syracuseStep 1100195 = 1650293) B1650293
theorem B2476493 : Blo 487790 2476493 := bstep (se 3 (by rfl) ⟨464342, by rfl⟩ : syracuseStep 2476493 = 928685) B928685
theorem B2345507 : Blo 487790 2345507 := bstep (se 1 (by rfl) ⟨1759130, by rfl⟩ : syracuseStep 2345507 = 3518261) B3518261
theorem B15026741 : Blo 487790 15026741 := bstep (se 5 (by rfl) ⟨704378, by rfl⟩ : syracuseStep 15026741 = 1408757) B1408757
theorem B1854029 : Blo 487790 1854029 := bstep (se 3 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 1854029 = 695261) B695261
theorem B1657421 : Blo 487790 1657421 := bstep (se 3 (by rfl) ⟨310766, by rfl⟩ : syracuseStep 1657421 = 621533) B621533
theorem B1657475 : Blo 487790 1657475 := bstep (se 1 (by rfl) ⟨1243106, by rfl⟩ : syracuseStep 1657475 = 2486213) B2486213
theorem B1100465 : Blo 487790 1100465 := bstep (se 2 (by rfl) ⟨412674, by rfl⟩ : syracuseStep 1100465 = 825349) B825349
theorem B1100483 : Blo 487790 1100483 := bstep (se 1 (by rfl) ⟨825362, by rfl⟩ : syracuseStep 1100483 = 1650725) B1650725
theorem B2018125 : Blo 487790 2018125 := bstep (se 3 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 2018125 = 756797) B756797
theorem B1395569 : Blo 487790 1395569 := bstep (se 2 (by rfl) ⟨523338, by rfl⟩ : syracuseStep 1395569 = 1046677) B1046677
theorem B1657745 : Blo 487790 1657745 := bstep (se 2 (by rfl) ⟨621654, by rfl⟩ : syracuseStep 1657745 = 1243309) B1243309
theorem B1100753 : Blo 487790 1100753 := bstep (se 2 (by rfl) ⟨412782, by rfl⟩ : syracuseStep 1100753 = 825565) B825565
theorem B1100771 : Blo 487790 1100771 := bstep (se 1 (by rfl) ⟨825578, by rfl⟩ : syracuseStep 1100771 = 1651157) B1651157
theorem B1101041 : Blo 487790 1101041 := bstep (se 2 (by rfl) ⟨412890, by rfl⟩ : syracuseStep 1101041 = 825781) B825781
theorem B1101059 : Blo 487790 1101059 := bstep (se 1 (by rfl) ⟨825794, by rfl⟩ : syracuseStep 1101059 = 1651589) B1651589
theorem B2346317 : Blo 487790 2346317 := bstep (se 3 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 2346317 = 879869) B879869
theorem B1985933 : Blo 487790 1985933 := bstep (se 3 (by rfl) ⟨372362, by rfl⟩ : syracuseStep 1985933 = 744725) B744725
theorem B1658285 : Blo 487790 1658285 := bstep (se 3 (by rfl) ⟨310928, by rfl⟩ : syracuseStep 1658285 = 621857) B621857
theorem B1658339 : Blo 487790 1658339 := bstep (se 1 (by rfl) ⟨1243754, by rfl⟩ : syracuseStep 1658339 = 2487509) B2487509
theorem B1101329 : Blo 487790 1101329 := bstep (se 2 (by rfl) ⟨412998, by rfl⟩ : syracuseStep 1101329 = 825997) B825997
theorem B1396241 : Blo 487790 1396241 := bstep (se 2 (by rfl) ⟨523590, by rfl⟩ : syracuseStep 1396241 = 1047181) B1047181
theorem B1101347 : Blo 487790 1101347 := bstep (se 1 (by rfl) ⟨826010, by rfl⟩ : syracuseStep 1101347 = 1652021) B1652021
theorem B1134179 : Blo 487790 1134179 := bstep (se 1 (by rfl) ⟨850634, by rfl⟩ : syracuseStep 1134179 = 1701269) B1701269
theorem B1986275 : Blo 487790 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B1658609 : Blo 487790 1658609 := bstep (se 2 (by rfl) ⟨621978, by rfl⟩ : syracuseStep 1658609 = 1243957) B1243957
theorem B1101617 : Blo 487790 1101617 := bstep (se 2 (by rfl) ⟨413106, by rfl⟩ : syracuseStep 1101617 = 826213) B826213
theorem B1101635 : Blo 487790 1101635 := bstep (se 1 (by rfl) ⟨826226, by rfl⟩ : syracuseStep 1101635 = 1652453) B1652453
theorem B1101905 : Blo 487790 1101905 := bstep (se 2 (by rfl) ⟨413214, by rfl⟩ : syracuseStep 1101905 = 826429) B826429
theorem B512083 : Blo 487790 512083 := bstep (se 1 (by rfl) ⟨384062, by rfl⟩ : syracuseStep 512083 = 768125) B768125
theorem B1101923 : Blo 487790 1101923 := bstep (se 1 (by rfl) ⟨826442, by rfl⟩ : syracuseStep 1101923 = 1652885) B1652885
theorem B4706545 : Blo 487790 4706545 := bstep (se 2 (by rfl) ⟨1764954, by rfl⟩ : syracuseStep 4706545 = 3529909) B3529909
theorem B1659149 : Blo 487790 1659149 := bstep (se 3 (by rfl) ⟨311090, by rfl⟩ : syracuseStep 1659149 = 622181) B622181
theorem B1397027 : Blo 487790 1397027 := bstep (se 1 (by rfl) ⟨1047770, by rfl⟩ : syracuseStep 1397027 = 2095541) B2095541
theorem B1659203 : Blo 487790 1659203 := bstep (se 1 (by rfl) ⟨1244402, by rfl⟩ : syracuseStep 1659203 = 2488805) B2488805
theorem B1102193 : Blo 487790 1102193 := bstep (se 2 (by rfl) ⟨413322, by rfl⟩ : syracuseStep 1102193 = 826645) B826645
theorem B1102211 : Blo 487790 1102211 := bstep (se 1 (by rfl) ⟨826658, by rfl⟩ : syracuseStep 1102211 = 1653317) B1653317
theorem B741793 : Blo 487790 741793 := bstep (se 2 (by rfl) ⟨278172, by rfl⟩ : syracuseStep 741793 = 556345) B556345
theorem B1659473 : Blo 487790 1659473 := bstep (se 2 (by rfl) ⟨622302, by rfl⟩ : syracuseStep 1659473 = 1244605) B1244605
theorem B1397357 : Blo 487790 1397357 := bstep (se 3 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 1397357 = 524009) B524009
theorem B1856141 : Blo 487790 1856141 := bstep (se 3 (by rfl) ⟨348026, by rfl⟩ : syracuseStep 1856141 = 696053) B696053
theorem B1102481 : Blo 487790 1102481 := bstep (se 2 (by rfl) ⟨413430, by rfl⟩ : syracuseStep 1102481 = 826861) B826861
theorem B1102499 : Blo 487790 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B1397425 : Blo 487790 1397425 := bstep (se 2 (by rfl) ⟨524034, by rfl⟩ : syracuseStep 1397425 = 1048069) B1048069
theorem B3134213 : Blo 487790 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B840497 : Blo 487790 840497 := bstep (se 2 (by rfl) ⟨315186, by rfl⟩ : syracuseStep 840497 = 630373) B630373
theorem B1102769 : Blo 487790 1102769 := bstep (se 2 (by rfl) ⟨413538, by rfl⟩ : syracuseStep 1102769 = 827077) B827077
theorem B1397699 : Blo 487790 1397699 := bstep (se 1 (by rfl) ⟨1048274, by rfl⟩ : syracuseStep 1397699 = 2096549) B2096549
theorem B1102787 : Blo 487790 1102787 := bstep (se 1 (by rfl) ⟨827090, by rfl⟩ : syracuseStep 1102787 = 1654181) B1654181
theorem B1103057 : Blo 487790 1103057 := bstep (se 2 (by rfl) ⟨413646, by rfl⟩ : syracuseStep 1103057 = 827293) B827293
theorem B1103075 : Blo 487790 1103075 := bstep (se 1 (by rfl) ⟨827306, by rfl⟩ : syracuseStep 1103075 = 1654613) B1654613
theorem B2479409 : Blo 487790 2479409 := bstep (se 2 (by rfl) ⟨929778, by rfl⟩ : syracuseStep 2479409 = 1859557) B1859557
theorem B6280517 : Blo 487790 6280517 := bstep (se 4 (by rfl) ⟨588798, by rfl⟩ : syracuseStep 6280517 = 1177597) B1177597
theorem B1856945 : Blo 487790 1856945 := bstep (se 2 (by rfl) ⟨696354, by rfl⟩ : syracuseStep 1856945 = 1392709) B1392709
theorem B1103345 : Blo 487790 1103345 := bstep (se 2 (by rfl) ⟨413754, by rfl⟩ : syracuseStep 1103345 = 827509) B827509
theorem B1103363 : Blo 487790 1103363 := bstep (se 1 (by rfl) ⟨827522, by rfl⟩ : syracuseStep 1103363 = 1655045) B1655045
theorem B1398541 : Blo 487790 1398541 := bstep (se 3 (by rfl) ⟨262226, by rfl⟩ : syracuseStep 1398541 = 524453) B524453
theorem B1103633 : Blo 487790 1103633 := bstep (se 2 (by rfl) ⟨413862, by rfl⟩ : syracuseStep 1103633 = 827725) B827725
theorem B1234723 : Blo 487790 1234723 := bstep (se 1 (by rfl) ⟨926042, by rfl⟩ : syracuseStep 1234723 = 1852085) B1852085
theorem B1103651 : Blo 487790 1103651 := bstep (se 1 (by rfl) ⟨827738, by rfl⟩ : syracuseStep 1103651 = 1655477) B1655477
theorem B1398701 : Blo 487790 1398701 := bstep (se 3 (by rfl) ⟨262256, by rfl⟩ : syracuseStep 1398701 = 524513) B524513
theorem B1234865 : Blo 487790 1234865 := bstep (se 2 (by rfl) ⟨463074, by rfl⟩ : syracuseStep 1234865 = 926149) B926149
theorem B1103921 : Blo 487790 1103921 := bstep (se 2 (by rfl) ⟨413970, by rfl⟩ : syracuseStep 1103921 = 827941) B827941
theorem B1103939 : Blo 487790 1103939 := bstep (se 1 (by rfl) ⟨827954, by rfl⟩ : syracuseStep 1103939 = 1655909) B1655909
theorem B1857613 : Blo 487790 1857613 := bstep (se 3 (by rfl) ⟨348302, by rfl⟩ : syracuseStep 1857613 = 696605) B696605
theorem B743521 : Blo 487790 743521 := bstep (se 2 (by rfl) ⟨278820, by rfl⟩ : syracuseStep 743521 = 557641) B557641
theorem B1398883 : Blo 487790 1398883 := bstep (se 1 (by rfl) ⟨1049162, by rfl⟩ : syracuseStep 1398883 = 2098325) B2098325
theorem B809137 : Blo 487790 809137 := bstep (se 2 (by rfl) ⟨303426, by rfl⟩ : syracuseStep 809137 = 606853) B606853
theorem B2087117 : Blo 487790 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B1562851 : Blo 487790 1562851 := bstep (se 1 (by rfl) ⟨1172138, by rfl⟩ : syracuseStep 1562851 = 2344277) B2344277
theorem B1104209 : Blo 487790 1104209 := bstep (se 2 (by rfl) ⟨414078, by rfl⟩ : syracuseStep 1104209 = 828157) B828157
theorem B1104227 : Blo 487790 1104227 := bstep (se 1 (by rfl) ⟨828170, by rfl⟩ : syracuseStep 1104227 = 1656341) B1656341
theorem B9525617 : Blo 487790 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B1104497 : Blo 487790 1104497 := bstep (se 2 (by rfl) ⟨414186, by rfl⟩ : syracuseStep 1104497 = 828373) B828373
theorem B1104515 : Blo 487790 1104515 := bstep (se 1 (by rfl) ⟨828386, by rfl⟩ : syracuseStep 1104515 = 1656773) B1656773
theorem B1563313 : Blo 487790 1563313 := bstep (se 2 (by rfl) ⟨586242, by rfl⟩ : syracuseStep 1563313 = 1172485) B1172485
theorem B2480867 : Blo 487790 2480867 := bstep (se 1 (by rfl) ⟨1860650, by rfl⟩ : syracuseStep 2480867 = 3721301) B3721301
theorem B940835 : Blo 487790 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B744275 : Blo 487790 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B1858403 : Blo 487790 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B1235857 : Blo 487790 1235857 := bstep (se 2 (by rfl) ⟨463446, by rfl⟩ : syracuseStep 1235857 = 926893) B926893
theorem B1104785 : Blo 487790 1104785 := bstep (se 2 (by rfl) ⟨414294, by rfl⟩ : syracuseStep 1104785 = 828589) B828589
theorem B1104803 : Blo 487790 1104803 := bstep (se 1 (by rfl) ⟨828602, by rfl⟩ : syracuseStep 1104803 = 1657205) B1657205
theorem B744385 : Blo 487790 744385 := bstep (se 2 (by rfl) ⟨279144, by rfl⟩ : syracuseStep 744385 = 558289) B558289
theorem B1236131 : Blo 487790 1236131 := bstep (se 1 (by rfl) ⟨927098, by rfl⟩ : syracuseStep 1236131 = 1854197) B1854197
theorem B1105073 : Blo 487790 1105073 := bstep (se 2 (by rfl) ⟨414402, by rfl⟩ : syracuseStep 1105073 = 828805) B828805
theorem B1105091 : Blo 487790 1105091 := bstep (se 1 (by rfl) ⟨828818, by rfl⟩ : syracuseStep 1105091 = 1657637) B1657637
theorem B1236323 : Blo 487790 1236323 := bstep (se 1 (by rfl) ⟨927242, by rfl⟩ : syracuseStep 1236323 = 1854485) B1854485
theorem B1105361 : Blo 487790 1105361 := bstep (se 2 (by rfl) ⟨414510, by rfl⟩ : syracuseStep 1105361 = 829021) B829021
theorem B1400273 : Blo 487790 1400273 := bstep (se 2 (by rfl) ⟨525102, by rfl⟩ : syracuseStep 1400273 = 1050205) B1050205
theorem B1105379 : Blo 487790 1105379 := bstep (se 1 (by rfl) ⟨829034, by rfl⟩ : syracuseStep 1105379 = 1658069) B1658069
theorem B1859057 : Blo 487790 1859057 := bstep (se 2 (by rfl) ⟨697146, by rfl⟩ : syracuseStep 1859057 = 1394293) B1394293
theorem B2481677 : Blo 487790 2481677 := bstep (se 3 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 2481677 = 930629) B930629
theorem B7036469 : Blo 487790 7036469 := bstep (se 5 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 7036469 = 659669) B659669
theorem B1105649 : Blo 487790 1105649 := bstep (se 2 (by rfl) ⟨414618, by rfl⟩ : syracuseStep 1105649 = 829237) B829237
theorem B1105667 : Blo 487790 1105667 := bstep (se 1 (by rfl) ⟨829250, by rfl⟩ : syracuseStep 1105667 = 1658501) B1658501
theorem B1269521 : Blo 487790 1269521 := bstep (se 2 (by rfl) ⟨476070, by rfl⟩ : syracuseStep 1269521 = 952141) B952141
theorem B548851 : Blo 487790 548851 := bstep (se 1 (by rfl) ⟨411638, by rfl⟩ : syracuseStep 548851 = 823277) B823277
theorem B1105937 : Blo 487790 1105937 := bstep (se 2 (by rfl) ⟨414726, by rfl⟩ : syracuseStep 1105937 = 829453) B829453
theorem B1105955 : Blo 487790 1105955 := bstep (se 1 (by rfl) ⟨829466, by rfl⟩ : syracuseStep 1105955 = 1658933) B1658933
theorem B548995 : Blo 487790 548995 := bstep (se 1 (by rfl) ⟨411746, by rfl⟩ : syracuseStep 548995 = 823493) B823493
theorem B3137777 : Blo 487790 3137777 := bstep (se 2 (by rfl) ⟨1176666, by rfl⟩ : syracuseStep 3137777 = 2353333) B2353333
theorem B1237265 : Blo 487790 1237265 := bstep (se 2 (by rfl) ⟨463974, by rfl⟩ : syracuseStep 1237265 = 927949) B927949
theorem B549139 : Blo 487790 549139 := bstep (se 1 (by rfl) ⟨411854, by rfl⟩ : syracuseStep 549139 = 823709) B823709
theorem B1106225 : Blo 487790 1106225 := bstep (se 2 (by rfl) ⟨414834, by rfl⟩ : syracuseStep 1106225 = 829669) B829669
theorem B1237315 : Blo 487790 1237315 := bstep (se 1 (by rfl) ⟨927986, by rfl⟩ : syracuseStep 1237315 = 1855973) B1855973
theorem B1106243 : Blo 487790 1106243 := bstep (se 1 (by rfl) ⟨829682, by rfl⟩ : syracuseStep 1106243 = 1659365) B1659365
theorem B549283 : Blo 487790 549283 := bstep (se 1 (by rfl) ⟨411962, by rfl⟩ : syracuseStep 549283 = 823925) B823925
theorem B1237457 : Blo 487790 1237457 := bstep (se 2 (by rfl) ⟨464046, by rfl⟩ : syracuseStep 1237457 = 928093) B928093
theorem B549427 : Blo 487790 549427 := bstep (se 1 (by rfl) ⟨412070, by rfl⟩ : syracuseStep 549427 = 824141) B824141
theorem B1106513 : Blo 487790 1106513 := bstep (se 2 (by rfl) ⟨414942, by rfl⟩ : syracuseStep 1106513 = 829885) B829885
theorem B549571 : Blo 487790 549571 := bstep (se 1 (by rfl) ⟨412178, by rfl⟩ : syracuseStep 549571 = 824357) B824357
theorem B2450189 : Blo 487790 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B549715 : Blo 487790 549715 := bstep (se 1 (by rfl) ⟨412286, by rfl⟩ : syracuseStep 549715 = 824573) B824573
theorem B1860515 : Blo 487790 1860515 := bstep (se 1 (by rfl) ⟨1395386, by rfl⟩ : syracuseStep 1860515 = 2790773) B2790773
theorem B1860529 : Blo 487790 1860529 := bstep (se 2 (by rfl) ⟨697698, by rfl⟩ : syracuseStep 1860529 = 1395397) B1395397
theorem B549859 : Blo 487790 549859 := bstep (se 1 (by rfl) ⟨412394, by rfl⟩ : syracuseStep 549859 = 824789) B824789
theorem B746561 : Blo 487790 746561 := bstep (se 2 (by rfl) ⟨279960, by rfl⟩ : syracuseStep 746561 = 559921) B559921
theorem B550003 : Blo 487790 550003 := bstep (se 1 (by rfl) ⟨412502, by rfl⟩ : syracuseStep 550003 = 825005) B825005
theorem B2090225 : Blo 487790 2090225 := bstep (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) B1567669
theorem B550147 : Blo 487790 550147 := bstep (se 1 (by rfl) ⟨412610, by rfl⟩ : syracuseStep 550147 = 825221) B825221
theorem B1566029 : Blo 487790 1566029 := bstep (se 3 (by rfl) ⟨293630, by rfl⟩ : syracuseStep 1566029 = 587261) B587261
theorem B2385229 : Blo 487790 2385229 := bstep (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) B894461
theorem B550291 : Blo 487790 550291 := bstep (se 1 (by rfl) ⟨412718, by rfl⟩ : syracuseStep 550291 = 825437) B825437
theorem B1238449 : Blo 487790 1238449 := bstep (se 2 (by rfl) ⟨464418, by rfl⟩ : syracuseStep 1238449 = 928837) B928837
theorem B1336867 : Blo 487790 1336867 := bstep (se 1 (by rfl) ⟨1002650, by rfl⟩ : syracuseStep 1336867 = 2005301) B2005301
theorem B550435 : Blo 487790 550435 := bstep (se 1 (by rfl) ⟨412826, by rfl⟩ : syracuseStep 550435 = 825653) B825653
theorem B3139235 : Blo 487790 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B550579 : Blo 487790 550579 := bstep (se 1 (by rfl) ⟨412934, by rfl⟩ : syracuseStep 550579 = 825869) B825869
theorem B1238723 : Blo 487790 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B550723 : Blo 487790 550723 := bstep (se 1 (by rfl) ⟨413042, by rfl⟩ : syracuseStep 550723 = 826085) B826085
theorem B1238915 : Blo 487790 1238915 := bstep (se 1 (by rfl) ⟨929186, by rfl⟩ : syracuseStep 1238915 = 1858373) B1858373
theorem B2090893 : Blo 487790 2090893 := bstep (se 3 (by rfl) ⟨392042, by rfl⟩ : syracuseStep 2090893 = 784085) B784085
theorem B550867 : Blo 487790 550867 := bstep (se 1 (by rfl) ⟨413150, by rfl⟩ : syracuseStep 550867 = 826301) B826301
theorem B551011 : Blo 487790 551011 := bstep (se 1 (by rfl) ⟨413258, by rfl⟩ : syracuseStep 551011 = 826517) B826517
theorem B3532997 : Blo 487790 3532997 := bstep (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) B662437
theorem B9038051 : Blo 487790 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B944369 : Blo 487790 944369 := bstep (se 2 (by rfl) ⟨354138, by rfl⟩ : syracuseStep 944369 = 708277) B708277
theorem B551155 : Blo 487790 551155 := bstep (se 1 (by rfl) ⟨413366, by rfl⟩ : syracuseStep 551155 = 826733) B826733
theorem B1861987 : Blo 487790 1861987 := bstep (se 1 (by rfl) ⟨1396490, by rfl⟩ : syracuseStep 1861987 = 2792981) B2792981
theorem B2484593 : Blo 487790 2484593 := bstep (se 2 (by rfl) ⟨931722, by rfl⟩ : syracuseStep 2484593 = 1863445) B1863445
theorem B551299 : Blo 487790 551299 := bstep (se 1 (by rfl) ⟨413474, by rfl⟩ : syracuseStep 551299 = 826949) B826949
theorem B3434957 : Blo 487790 3434957 := bstep (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) B1288109
theorem B2091491 : Blo 487790 2091491 := bstep (se 1 (by rfl) ⟨1568618, by rfl⟩ : syracuseStep 2091491 = 3137237) B3137237
theorem B551443 : Blo 487790 551443 := bstep (se 1 (by rfl) ⟨413582, by rfl⟩ : syracuseStep 551443 = 827165) B827165
theorem B551587 : Blo 487790 551587 := bstep (se 1 (by rfl) ⟨413690, by rfl⟩ : syracuseStep 551587 = 827381) B827381
theorem B10775267 : Blo 487790 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B1239857 : Blo 487790 1239857 := bstep (se 2 (by rfl) ⟨464946, by rfl⟩ : syracuseStep 1239857 = 929893) B929893
theorem B551731 : Blo 487790 551731 := bstep (se 1 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 551731 = 827597) B827597
theorem B1239907 : Blo 487790 1239907 := bstep (se 1 (by rfl) ⟨929930, by rfl⟩ : syracuseStep 1239907 = 1859861) B1859861
theorem B1567619 : Blo 487790 1567619 := bstep (se 1 (by rfl) ⟨1175714, by rfl⟩ : syracuseStep 1567619 = 2351429) B2351429
theorem B551875 : Blo 487790 551875 := bstep (se 1 (by rfl) ⟨413906, by rfl⟩ : syracuseStep 551875 = 827813) B827813
theorem B1240049 : Blo 487790 1240049 := bstep (se 2 (by rfl) ⟨465018, by rfl⟩ : syracuseStep 1240049 = 930037) B930037
theorem B617539 : Blo 487790 617539 := bstep (se 1 (by rfl) ⟨463154, by rfl⟩ : syracuseStep 617539 = 926309) B926309
theorem B552019 : Blo 487790 552019 := bstep (se 1 (by rfl) ⟨414014, by rfl⟩ : syracuseStep 552019 = 828029) B828029
theorem B617635 : Blo 487790 617635 := bstep (se 1 (by rfl) ⟨463226, by rfl⟩ : syracuseStep 617635 = 926453) B926453
theorem B945329 : Blo 487790 945329 := bstep (se 2 (by rfl) ⟨354498, by rfl⟩ : syracuseStep 945329 = 708997) B708997
theorem B552163 : Blo 487790 552163 := bstep (se 1 (by rfl) ⟨414122, by rfl⟩ : syracuseStep 552163 = 828245) B828245
theorem B5008709 : Blo 487790 5008709 := bstep (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) B939133
theorem B3140977 : Blo 487790 3140977 := bstep (se 2 (by rfl) ⟨1177866, by rfl⟩ : syracuseStep 3140977 = 2355733) B2355733
theorem B552307 : Blo 487790 552307 := bstep (se 1 (by rfl) ⟨414230, by rfl⟩ : syracuseStep 552307 = 828461) B828461
theorem B552451 : Blo 487790 552451 := bstep (se 1 (by rfl) ⟨414338, by rfl⟩ : syracuseStep 552451 = 828677) B828677
theorem B1764899 : Blo 487790 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B618131 : Blo 487790 618131 := bstep (se 1 (by rfl) ⟨463598, by rfl⟩ : syracuseStep 618131 = 927197) B927197
theorem B552595 : Blo 487790 552595 := bstep (se 1 (by rfl) ⟨414446, by rfl⟩ : syracuseStep 552595 = 828893) B828893
theorem B9432773 : Blo 487790 9432773 := bstep (se 4 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 9432773 = 1768645) B1768645
theorem B2486051 : Blo 487790 2486051 := bstep (se 1 (by rfl) ⟨1864538, by rfl⟩ : syracuseStep 2486051 = 3729077) B3729077
theorem B552739 : Blo 487790 552739 := bstep (se 1 (by rfl) ⟨414554, by rfl⟩ : syracuseStep 552739 = 829109) B829109
theorem B552883 : Blo 487790 552883 := bstep (se 1 (by rfl) ⟨414662, by rfl⟩ : syracuseStep 552883 = 829325) B829325
theorem B1241041 : Blo 487790 1241041 := bstep (se 2 (by rfl) ⟨465390, by rfl⟩ : syracuseStep 1241041 = 930781) B930781
theorem B1044515 : Blo 487790 1044515 := bstep (se 1 (by rfl) ⟨783386, by rfl⟩ : syracuseStep 1044515 = 1566773) B1566773
theorem B553027 : Blo 487790 553027 := bstep (se 1 (by rfl) ⟨414770, by rfl⟩ : syracuseStep 553027 = 829541) B829541
theorem B1765475 : Blo 487790 1765475 := bstep (se 1 (by rfl) ⟨1324106, by rfl⟩ : syracuseStep 1765475 = 2648213) B2648213
theorem B1568899 : Blo 487790 1568899 := bstep (se 1 (by rfl) ⟨1176674, by rfl⟩ : syracuseStep 1568899 = 2353349) B2353349
theorem B2781317 : Blo 487790 2781317 := bstep (se 4 (by rfl) ⟨260748, by rfl⟩ : syracuseStep 2781317 = 521497) B521497
theorem B553171 : Blo 487790 553171 := bstep (se 1 (by rfl) ⟨414878, by rfl⟩ : syracuseStep 553171 = 829757) B829757
theorem B1241315 : Blo 487790 1241315 := bstep (se 1 (by rfl) ⟨930986, by rfl⟩ : syracuseStep 1241315 = 1861973) B1861973
theorem B782579 : Blo 487790 782579 := bstep (se 1 (by rfl) ⟨586934, by rfl⟩ : syracuseStep 782579 = 1173869) B1173869
theorem B618835 : Blo 487790 618835 := bstep (se 1 (by rfl) ⟨464126, by rfl⟩ : syracuseStep 618835 = 928253) B928253
theorem B487795 : Blo 487790 487795 := bstep (se 1 (by rfl) ⟨365846, by rfl⟩ : syracuseStep 487795 = 731693) B731693
theorem B782707 : Blo 487790 782707 := bstep (se 1 (by rfl) ⟨587030, by rfl⟩ : syracuseStep 782707 = 1174061) B1174061
theorem B487811 : Blo 487790 487811 := bstep (se 1 (by rfl) ⟨365858, by rfl⟩ : syracuseStep 487811 = 731717) B731717
theorem B487827 : Blo 487790 487827 := bstep (se 1 (by rfl) ⟨365870, by rfl⟩ : syracuseStep 487827 = 731741) B731741
theorem B487843 : Blo 487790 487843 := bstep (se 1 (by rfl) ⟨365882, by rfl⟩ : syracuseStep 487843 = 731765) B731765
theorem B1929635 : Blo 487790 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B1241507 : Blo 487790 1241507 := bstep (se 1 (by rfl) ⟨931130, by rfl⟩ : syracuseStep 1241507 = 1862261) B1862261
theorem B487859 : Blo 487790 487859 := bstep (se 1 (by rfl) ⟨365894, by rfl⟩ : syracuseStep 487859 = 731789) B731789
theorem B618931 : Blo 487790 618931 := bstep (se 1 (by rfl) ⟨464198, by rfl⟩ : syracuseStep 618931 = 928397) B928397
theorem B487875 : Blo 487790 487875 := bstep (se 1 (by rfl) ⟨365906, by rfl⟩ : syracuseStep 487875 = 731813) B731813
theorem B1569233 : Blo 487790 1569233 := bstep (se 2 (by rfl) ⟨588462, by rfl⟩ : syracuseStep 1569233 = 1176925) B1176925
theorem B487891 : Blo 487790 487891 := bstep (se 1 (by rfl) ⟨365918, by rfl⟩ : syracuseStep 487891 = 731837) B731837
theorem B487907 : Blo 487790 487907 := bstep (se 1 (by rfl) ⟨365930, by rfl⟩ : syracuseStep 487907 = 731861) B731861
theorem B487923 : Blo 487790 487923 := bstep (se 1 (by rfl) ⟨365942, by rfl⟩ : syracuseStep 487923 = 731885) B731885
theorem B487939 : Blo 487790 487939 := bstep (se 1 (by rfl) ⟨365954, by rfl⟩ : syracuseStep 487939 = 731909) B731909
theorem B1864205 : Blo 487790 1864205 := bstep (se 3 (by rfl) ⟨349538, by rfl⟩ : syracuseStep 1864205 = 699077) B699077
theorem B487955 : Blo 487790 487955 := bstep (se 1 (by rfl) ⟨365966, by rfl⟩ : syracuseStep 487955 = 731933) B731933
theorem B487971 : Blo 487790 487971 := bstep (se 1 (by rfl) ⟨365978, by rfl⟩ : syracuseStep 487971 = 731957) B731957
theorem B487987 : Blo 487790 487987 := bstep (se 1 (by rfl) ⟨365990, by rfl⟩ : syracuseStep 487987 = 731981) B731981
theorem B488003 : Blo 487790 488003 := bstep (se 1 (by rfl) ⟨366002, by rfl⟩ : syracuseStep 488003 = 732005) B732005
theorem B2781773 : Blo 487790 2781773 := bstep (se 3 (by rfl) ⟨521582, by rfl⟩ : syracuseStep 2781773 = 1043165) B1043165
theorem B2486861 : Blo 487790 2486861 := bstep (se 3 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 2486861 = 932573) B932573
theorem B488019 : Blo 487790 488019 := bstep (se 1 (by rfl) ⟨366014, by rfl⟩ : syracuseStep 488019 = 732029) B732029
theorem B488035 : Blo 487790 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B488051 : Blo 487790 488051 := bstep (se 1 (by rfl) ⟨366038, by rfl⟩ : syracuseStep 488051 = 732077) B732077
theorem B488067 : Blo 487790 488067 := bstep (se 1 (by rfl) ⟨366050, by rfl⟩ : syracuseStep 488067 = 732101) B732101
theorem B488083 : Blo 487790 488083 := bstep (se 1 (by rfl) ⟨366062, by rfl⟩ : syracuseStep 488083 = 732125) B732125
theorem B586387 : Blo 487790 586387 := bstep (se 1 (by rfl) ⟨439790, by rfl⟩ : syracuseStep 586387 = 879581) B879581
theorem B488099 : Blo 487790 488099 := bstep (se 1 (by rfl) ⟨366074, by rfl⟩ : syracuseStep 488099 = 732149) B732149
theorem B488115 : Blo 487790 488115 := bstep (se 1 (by rfl) ⟨366086, by rfl⟩ : syracuseStep 488115 = 732173) B732173
theorem B488131 : Blo 487790 488131 := bstep (se 1 (by rfl) ⟨366098, by rfl⟩ : syracuseStep 488131 = 732197) B732197
theorem B586435 : Blo 487790 586435 := bstep (se 1 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 586435 = 879653) B879653
theorem B3764933 : Blo 487790 3764933 := bstep (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) B705925
theorem B488147 : Blo 487790 488147 := bstep (se 1 (by rfl) ⟨366110, by rfl⟩ : syracuseStep 488147 = 732221) B732221
theorem B488163 : Blo 487790 488163 := bstep (se 1 (by rfl) ⟨366122, by rfl⟩ : syracuseStep 488163 = 732245) B732245
theorem B488179 : Blo 487790 488179 := bstep (se 1 (by rfl) ⟨366134, by rfl⟩ : syracuseStep 488179 = 732269) B732269
theorem B488195 : Blo 487790 488195 := bstep (se 1 (by rfl) ⟨366146, by rfl⟩ : syracuseStep 488195 = 732293) B732293
theorem B488211 : Blo 487790 488211 := bstep (se 1 (by rfl) ⟨366158, by rfl⟩ : syracuseStep 488211 = 732317) B732317
theorem B586531 : Blo 487790 586531 := bstep (se 1 (by rfl) ⟨439898, by rfl⟩ : syracuseStep 586531 = 879797) B879797
theorem B488227 : Blo 487790 488227 := bstep (se 1 (by rfl) ⟨366170, by rfl⟩ : syracuseStep 488227 = 732341) B732341
theorem B488243 : Blo 487790 488243 := bstep (se 1 (by rfl) ⟨366182, by rfl⟩ : syracuseStep 488243 = 732365) B732365
theorem B488259 : Blo 487790 488259 := bstep (se 1 (by rfl) ⟨366194, by rfl⟩ : syracuseStep 488259 = 732389) B732389
theorem B1700689 : Blo 487790 1700689 := bstep (se 2 (by rfl) ⟨637758, by rfl⟩ : syracuseStep 1700689 = 1275517) B1275517
theorem B488275 : Blo 487790 488275 := bstep (se 1 (by rfl) ⟨366206, by rfl⟩ : syracuseStep 488275 = 732413) B732413
theorem B488291 : Blo 487790 488291 := bstep (se 1 (by rfl) ⟨366218, by rfl⟩ : syracuseStep 488291 = 732437) B732437
theorem B488307 : Blo 487790 488307 := bstep (se 1 (by rfl) ⟨366230, by rfl⟩ : syracuseStep 488307 = 732461) B732461
theorem B488323 : Blo 487790 488323 := bstep (se 1 (by rfl) ⟨366242, by rfl⟩ : syracuseStep 488323 = 732485) B732485
theorem B1045379 : Blo 487790 1045379 := bstep (se 1 (by rfl) ⟨784034, by rfl⟩ : syracuseStep 1045379 = 1568069) B1568069
theorem B488339 : Blo 487790 488339 := bstep (se 1 (by rfl) ⟨366254, by rfl⟩ : syracuseStep 488339 = 732509) B732509
theorem B783265 : Blo 487790 783265 := bstep (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) B587449
theorem B488355 : Blo 487790 488355 := bstep (se 1 (by rfl) ⟨366266, by rfl⟩ : syracuseStep 488355 = 732533) B732533
theorem B619427 : Blo 487790 619427 := bstep (se 1 (by rfl) ⟨464570, by rfl⟩ : syracuseStep 619427 = 929141) B929141
theorem B488371 : Blo 487790 488371 := bstep (se 1 (by rfl) ⟨366278, by rfl⟩ : syracuseStep 488371 = 732557) B732557
theorem B488387 : Blo 487790 488387 := bstep (se 1 (by rfl) ⟨366290, by rfl⟩ : syracuseStep 488387 = 732581) B732581
theorem B488403 : Blo 487790 488403 := bstep (se 1 (by rfl) ⟨366302, by rfl⟩ : syracuseStep 488403 = 732605) B732605
theorem B488419 : Blo 487790 488419 := bstep (se 1 (by rfl) ⟨366314, by rfl⟩ : syracuseStep 488419 = 732629) B732629
theorem B1045489 : Blo 487790 1045489 := bstep (se 2 (by rfl) ⟨392058, by rfl⟩ : syracuseStep 1045489 = 784117) B784117
theorem B488435 : Blo 487790 488435 := bstep (se 1 (by rfl) ⟨366326, by rfl⟩ : syracuseStep 488435 = 732653) B732653
theorem B488451 : Blo 487790 488451 := bstep (se 1 (by rfl) ⟨366338, by rfl⟩ : syracuseStep 488451 = 732677) B732677
theorem B488467 : Blo 487790 488467 := bstep (se 1 (by rfl) ⟨366350, by rfl⟩ : syracuseStep 488467 = 732701) B732701
theorem B488483 : Blo 487790 488483 := bstep (se 1 (by rfl) ⟨366362, by rfl⟩ : syracuseStep 488483 = 732725) B732725
theorem B488499 : Blo 487790 488499 := bstep (se 1 (by rfl) ⟨366374, by rfl⟩ : syracuseStep 488499 = 732749) B732749
theorem B816193 : Blo 487790 816193 := bstep (se 2 (by rfl) ⟨306072, by rfl⟩ : syracuseStep 816193 = 612145) B612145
theorem B488515 : Blo 487790 488515 := bstep (se 1 (by rfl) ⟨366386, by rfl⟩ : syracuseStep 488515 = 732773) B732773
theorem B488531 : Blo 487790 488531 := bstep (se 1 (by rfl) ⟨366398, by rfl⟩ : syracuseStep 488531 = 732797) B732797
theorem B488547 : Blo 487790 488547 := bstep (se 1 (by rfl) ⟨366410, by rfl⟩ : syracuseStep 488547 = 732821) B732821
theorem B488563 : Blo 487790 488563 := bstep (se 1 (by rfl) ⟨366422, by rfl⟩ : syracuseStep 488563 = 732845) B732845
theorem B488579 : Blo 487790 488579 := bstep (se 1 (by rfl) ⟨366434, by rfl⟩ : syracuseStep 488579 = 732869) B732869
theorem B488595 : Blo 487790 488595 := bstep (se 1 (by rfl) ⟨366446, by rfl⟩ : syracuseStep 488595 = 732893) B732893
theorem B488611 : Blo 487790 488611 := bstep (se 1 (by rfl) ⟨366458, by rfl⟩ : syracuseStep 488611 = 732917) B732917
theorem B488627 : Blo 487790 488627 := bstep (se 1 (by rfl) ⟨366470, by rfl⟩ : syracuseStep 488627 = 732941) B732941
theorem B488643 : Blo 487790 488643 := bstep (se 1 (by rfl) ⟨366482, by rfl⟩ : syracuseStep 488643 = 732965) B732965
theorem B488659 : Blo 487790 488659 := bstep (se 1 (by rfl) ⟨366494, by rfl⟩ : syracuseStep 488659 = 732989) B732989
theorem B1766627 : Blo 487790 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B488675 : Blo 487790 488675 := bstep (se 1 (by rfl) ⟨366506, by rfl⟩ : syracuseStep 488675 = 733013) B733013
theorem B488691 : Blo 487790 488691 := bstep (se 1 (by rfl) ⟨366518, by rfl⟩ : syracuseStep 488691 = 733037) B733037
theorem B488707 : Blo 487790 488707 := bstep (se 1 (by rfl) ⟨366530, by rfl⟩ : syracuseStep 488707 = 733061) B733061
theorem B3142925 : Blo 487790 3142925 := bstep (se 3 (by rfl) ⟨589298, by rfl⟩ : syracuseStep 3142925 = 1178597) B1178597
theorem B488723 : Blo 487790 488723 := bstep (se 1 (by rfl) ⟨366542, by rfl⟩ : syracuseStep 488723 = 733085) B733085
theorem B488739 : Blo 487790 488739 := bstep (se 1 (by rfl) ⟨366554, by rfl⟩ : syracuseStep 488739 = 733109) B733109
theorem B488755 : Blo 487790 488755 := bstep (se 1 (by rfl) ⟨366566, by rfl⟩ : syracuseStep 488755 = 733133) B733133
theorem B488771 : Blo 487790 488771 := bstep (se 1 (by rfl) ⟨366578, by rfl⟩ : syracuseStep 488771 = 733157) B733157
theorem B1242449 : Blo 487790 1242449 := bstep (se 2 (by rfl) ⟨465918, by rfl⟩ : syracuseStep 1242449 = 931837) B931837
theorem B488787 : Blo 487790 488787 := bstep (se 1 (by rfl) ⟨366590, by rfl⟩ : syracuseStep 488787 = 733181) B733181
theorem B587107 : Blo 487790 587107 := bstep (se 1 (by rfl) ⟨440330, by rfl⟩ : syracuseStep 587107 = 880661) B880661
theorem B488803 : Blo 487790 488803 := bstep (se 1 (by rfl) ⟨366602, by rfl⟩ : syracuseStep 488803 = 733205) B733205
theorem B488819 : Blo 487790 488819 := bstep (se 1 (by rfl) ⟨366614, by rfl⟩ : syracuseStep 488819 = 733229) B733229
theorem B1242499 : Blo 487790 1242499 := bstep (se 1 (by rfl) ⟨931874, by rfl⟩ : syracuseStep 1242499 = 1863749) B1863749
theorem B488835 : Blo 487790 488835 := bstep (se 1 (by rfl) ⟨366626, by rfl⟩ : syracuseStep 488835 = 733253) B733253
theorem B488851 : Blo 487790 488851 := bstep (se 1 (by rfl) ⟨366638, by rfl⟩ : syracuseStep 488851 = 733277) B733277
theorem B488867 : Blo 487790 488867 := bstep (se 1 (by rfl) ⟨366650, by rfl⟩ : syracuseStep 488867 = 733301) B733301
theorem B521651 : Blo 487790 521651 := bstep (se 1 (by rfl) ⟨391238, by rfl⟩ : syracuseStep 521651 = 782477) B782477
theorem B488883 : Blo 487790 488883 := bstep (se 1 (by rfl) ⟨366662, by rfl⟩ : syracuseStep 488883 = 733325) B733325
theorem B488899 : Blo 487790 488899 := bstep (se 1 (by rfl) ⟨366674, by rfl⟩ : syracuseStep 488899 = 733349) B733349
theorem B488915 : Blo 487790 488915 := bstep (se 1 (by rfl) ⟨366686, by rfl⟩ : syracuseStep 488915 = 733373) B733373
theorem B488931 : Blo 487790 488931 := bstep (se 1 (by rfl) ⟨366698, by rfl⟩ : syracuseStep 488931 = 733397) B733397
theorem B882161 : Blo 487790 882161 := bstep (se 2 (by rfl) ⟨330810, by rfl⟩ : syracuseStep 882161 = 661621) B661621
theorem B3536369 : Blo 487790 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B488947 : Blo 487790 488947 := bstep (se 1 (by rfl) ⟨366710, by rfl⟩ : syracuseStep 488947 = 733421) B733421
theorem B488963 : Blo 487790 488963 := bstep (se 1 (by rfl) ⟨366722, by rfl⟩ : syracuseStep 488963 = 733445) B733445
theorem B1242641 : Blo 487790 1242641 := bstep (se 2 (by rfl) ⟨465990, by rfl⟩ : syracuseStep 1242641 = 931981) B931981
theorem B488979 : Blo 487790 488979 := bstep (se 1 (by rfl) ⟨366734, by rfl⟩ : syracuseStep 488979 = 733469) B733469
theorem B488995 : Blo 487790 488995 := bstep (se 1 (by rfl) ⟨366746, by rfl⟩ : syracuseStep 488995 = 733493) B733493
theorem B1504813 : Blo 487790 1504813 := bstep (se 3 (by rfl) ⟨282152, by rfl⟩ : syracuseStep 1504813 = 564305) B564305
theorem B489011 : Blo 487790 489011 := bstep (se 1 (by rfl) ⟨366758, by rfl⟩ : syracuseStep 489011 = 733517) B733517
theorem B783937 : Blo 487790 783937 := bstep (se 2 (by rfl) ⟨293976, by rfl⟩ : syracuseStep 783937 = 587953) B587953
theorem B489027 : Blo 487790 489027 := bstep (se 1 (by rfl) ⟨366770, by rfl⟩ : syracuseStep 489027 = 733541) B733541
theorem B489043 : Blo 487790 489043 := bstep (se 1 (by rfl) ⟨366782, by rfl⟩ : syracuseStep 489043 = 733565) B733565
theorem B489059 : Blo 487790 489059 := bstep (se 1 (by rfl) ⟨366794, by rfl⟩ : syracuseStep 489059 = 733589) B733589
theorem B620131 : Blo 487790 620131 := bstep (se 1 (by rfl) ⟨465098, by rfl⟩ : syracuseStep 620131 = 930197) B930197
theorem B489075 : Blo 487790 489075 := bstep (se 1 (by rfl) ⟨366806, by rfl⟩ : syracuseStep 489075 = 733613) B733613
theorem B489091 : Blo 487790 489091 := bstep (se 1 (by rfl) ⟨366818, by rfl⟩ : syracuseStep 489091 = 733637) B733637
theorem B489107 : Blo 487790 489107 := bstep (se 1 (by rfl) ⟨366830, by rfl⟩ : syracuseStep 489107 = 733661) B733661
theorem B489123 : Blo 487790 489123 := bstep (se 1 (by rfl) ⟨366842, by rfl⟩ : syracuseStep 489123 = 733685) B733685
theorem B1767089 : Blo 487790 1767089 := bstep (se 2 (by rfl) ⟨662658, by rfl⟩ : syracuseStep 1767089 = 1325317) B1325317
theorem B489139 : Blo 487790 489139 := bstep (se 1 (by rfl) ⟨366854, by rfl⟩ : syracuseStep 489139 = 733709) B733709
theorem B5961397 : Blo 487790 5961397 := bstep (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) B558881
theorem B489155 : Blo 487790 489155 := bstep (se 1 (by rfl) ⟨366866, by rfl⟩ : syracuseStep 489155 = 733733) B733733
theorem B620227 : Blo 487790 620227 := bstep (se 1 (by rfl) ⟨465170, by rfl⟩ : syracuseStep 620227 = 930341) B930341
theorem B489171 : Blo 487790 489171 := bstep (se 1 (by rfl) ⟨366878, by rfl⟩ : syracuseStep 489171 = 733757) B733757
theorem B489187 : Blo 487790 489187 := bstep (se 1 (by rfl) ⟨366890, by rfl⟩ : syracuseStep 489187 = 733781) B733781
theorem B489203 : Blo 487790 489203 := bstep (se 1 (by rfl) ⟨366902, by rfl⟩ : syracuseStep 489203 = 733805) B733805
theorem B489219 : Blo 487790 489219 := bstep (se 1 (by rfl) ⟨366914, by rfl⟩ : syracuseStep 489219 = 733829) B733829
theorem B489235 : Blo 487790 489235 := bstep (se 1 (by rfl) ⟨366926, by rfl⟩ : syracuseStep 489235 = 733853) B733853
theorem B489251 : Blo 487790 489251 := bstep (se 1 (by rfl) ⟨366938, by rfl⟩ : syracuseStep 489251 = 733877) B733877
theorem B489267 : Blo 487790 489267 := bstep (se 1 (by rfl) ⟨366950, by rfl⟩ : syracuseStep 489267 = 733901) B733901
theorem B489283 : Blo 487790 489283 := bstep (se 1 (by rfl) ⟨366962, by rfl⟩ : syracuseStep 489283 = 733925) B733925
theorem B489299 : Blo 487790 489299 := bstep (se 1 (by rfl) ⟨366974, by rfl⟩ : syracuseStep 489299 = 733949) B733949
theorem B489315 : Blo 487790 489315 := bstep (se 1 (by rfl) ⟨366986, by rfl⟩ : syracuseStep 489315 = 733973) B733973
theorem B489331 : Blo 487790 489331 := bstep (se 1 (by rfl) ⟨366998, by rfl⟩ : syracuseStep 489331 = 733997) B733997
theorem B489347 : Blo 487790 489347 := bstep (se 1 (by rfl) ⟨367010, by rfl⟩ : syracuseStep 489347 = 734021) B734021
theorem B489363 : Blo 487790 489363 := bstep (se 1 (by rfl) ⟨367022, by rfl⟩ : syracuseStep 489363 = 734045) B734045
theorem B489379 : Blo 487790 489379 := bstep (se 1 (by rfl) ⟨367034, by rfl⟩ : syracuseStep 489379 = 734069) B734069
theorem B489395 : Blo 487790 489395 := bstep (se 1 (by rfl) ⟨367046, by rfl⟩ : syracuseStep 489395 = 734093) B734093
theorem B489411 : Blo 487790 489411 := bstep (se 1 (by rfl) ⟨367058, by rfl⟩ : syracuseStep 489411 = 734117) B734117
theorem B489427 : Blo 487790 489427 := bstep (se 1 (by rfl) ⟨367070, by rfl⟩ : syracuseStep 489427 = 734141) B734141
theorem B8353763 : Blo 487790 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B489443 : Blo 487790 489443 := bstep (se 1 (by rfl) ⟨367082, by rfl⟩ : syracuseStep 489443 = 734165) B734165
theorem B489459 : Blo 487790 489459 := bstep (se 1 (by rfl) ⟨367094, by rfl⟩ : syracuseStep 489459 = 734189) B734189
theorem B489475 : Blo 487790 489475 := bstep (se 1 (by rfl) ⟨367106, by rfl⟩ : syracuseStep 489475 = 734213) B734213
theorem B2488333 : Blo 487790 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B489491 : Blo 487790 489491 := bstep (se 1 (by rfl) ⟨367118, by rfl⟩ : syracuseStep 489491 = 734237) B734237
theorem B489507 : Blo 487790 489507 := bstep (se 1 (by rfl) ⟨367130, by rfl⟩ : syracuseStep 489507 = 734261) B734261
theorem B489523 : Blo 487790 489523 := bstep (se 1 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 489523 = 734285) B734285
theorem B489539 : Blo 487790 489539 := bstep (se 1 (by rfl) ⟨367154, by rfl⟩ : syracuseStep 489539 = 734309) B734309
theorem B1701965 : Blo 487790 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B489555 : Blo 487790 489555 := bstep (se 1 (by rfl) ⟨367166, by rfl⟩ : syracuseStep 489555 = 734333) B734333
theorem B489571 : Blo 487790 489571 := bstep (se 1 (by rfl) ⟨367178, by rfl⟩ : syracuseStep 489571 = 734357) B734357
theorem B489587 : Blo 487790 489587 := bstep (se 1 (by rfl) ⟨367190, by rfl⟩ : syracuseStep 489587 = 734381) B734381
theorem B489603 : Blo 487790 489603 := bstep (se 1 (by rfl) ⟨367202, by rfl⟩ : syracuseStep 489603 = 734405) B734405
theorem B489619 : Blo 487790 489619 := bstep (se 1 (by rfl) ⟨367214, by rfl⟩ : syracuseStep 489619 = 734429) B734429
theorem B489635 : Blo 487790 489635 := bstep (se 1 (by rfl) ⟨367226, by rfl⟩ : syracuseStep 489635 = 734453) B734453
theorem B2095267 : Blo 487790 2095267 := bstep (se 1 (by rfl) ⟨1571450, by rfl⟩ : syracuseStep 2095267 = 3142901) B3142901
theorem B489651 : Blo 487790 489651 := bstep (se 1 (by rfl) ⟨367238, by rfl⟩ : syracuseStep 489651 = 734477) B734477
theorem B620723 : Blo 487790 620723 := bstep (se 1 (by rfl) ⟨465542, by rfl⟩ : syracuseStep 620723 = 931085) B931085
theorem B489667 : Blo 487790 489667 := bstep (se 1 (by rfl) ⟨367250, by rfl⟩ : syracuseStep 489667 = 734501) B734501
theorem B489683 : Blo 487790 489683 := bstep (se 1 (by rfl) ⟨367262, by rfl⟩ : syracuseStep 489683 = 734525) B734525
theorem B489699 : Blo 487790 489699 := bstep (se 1 (by rfl) ⟨367274, by rfl⟩ : syracuseStep 489699 = 734549) B734549
theorem B489715 : Blo 487790 489715 := bstep (se 1 (by rfl) ⟨367286, by rfl⟩ : syracuseStep 489715 = 734573) B734573
theorem B489731 : Blo 487790 489731 := bstep (se 1 (by rfl) ⟨367298, by rfl⟩ : syracuseStep 489731 = 734597) B734597
theorem B489747 : Blo 487790 489747 := bstep (se 1 (by rfl) ⟨367310, by rfl⟩ : syracuseStep 489747 = 734621) B734621
theorem B489763 : Blo 487790 489763 := bstep (se 1 (by rfl) ⟨367322, by rfl⟩ : syracuseStep 489763 = 734645) B734645
theorem B489779 : Blo 487790 489779 := bstep (se 1 (by rfl) ⟨367334, by rfl⟩ : syracuseStep 489779 = 734669) B734669
theorem B1505603 : Blo 487790 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B489795 : Blo 487790 489795 := bstep (se 1 (by rfl) ⟨367346, by rfl⟩ : syracuseStep 489795 = 734693) B734693
theorem B489811 : Blo 487790 489811 := bstep (se 1 (by rfl) ⟨367358, by rfl⟩ : syracuseStep 489811 = 734717) B734717
theorem B489827 : Blo 487790 489827 := bstep (se 1 (by rfl) ⟨367370, by rfl⟩ : syracuseStep 489827 = 734741) B734741
theorem B5601635 : Blo 487790 5601635 := bstep (se 1 (by rfl) ⟨4201226, by rfl⟩ : syracuseStep 5601635 = 8402453) B8402453
theorem B489843 : Blo 487790 489843 := bstep (se 1 (by rfl) ⟨367382, by rfl⟩ : syracuseStep 489843 = 734765) B734765
theorem B489859 : Blo 487790 489859 := bstep (se 1 (by rfl) ⟨367394, by rfl⟩ : syracuseStep 489859 = 734789) B734789
theorem B489875 : Blo 487790 489875 := bstep (se 1 (by rfl) ⟨367406, by rfl⟩ : syracuseStep 489875 = 734813) B734813
theorem B522659 : Blo 487790 522659 := bstep (se 1 (by rfl) ⟨391994, by rfl⟩ : syracuseStep 522659 = 783989) B783989
theorem B489891 : Blo 487790 489891 := bstep (se 1 (by rfl) ⟨367418, by rfl⟩ : syracuseStep 489891 = 734837) B734837
theorem B489907 : Blo 487790 489907 := bstep (se 1 (by rfl) ⟨367430, by rfl⟩ : syracuseStep 489907 = 734861) B734861
theorem B489923 : Blo 487790 489923 := bstep (se 1 (by rfl) ⟨367442, by rfl⟩ : syracuseStep 489923 = 734885) B734885
theorem B489939 : Blo 487790 489939 := bstep (se 1 (by rfl) ⟨367454, by rfl⟩ : syracuseStep 489939 = 734909) B734909
theorem B489955 : Blo 487790 489955 := bstep (se 1 (by rfl) ⟨367466, by rfl⟩ : syracuseStep 489955 = 734933) B734933
theorem B1571309 : Blo 487790 1571309 := bstep (se 3 (by rfl) ⟨294620, by rfl⟩ : syracuseStep 1571309 = 589241) B589241
theorem B1243633 : Blo 487790 1243633 := bstep (se 2 (by rfl) ⟨466362, by rfl⟩ : syracuseStep 1243633 = 932725) B932725
theorem B489971 : Blo 487790 489971 := bstep (se 1 (by rfl) ⟨367478, by rfl⟩ : syracuseStep 489971 = 734957) B734957
theorem B489987 : Blo 487790 489987 := bstep (se 1 (by rfl) ⟨367490, by rfl⟩ : syracuseStep 489987 = 734981) B734981
theorem B490003 : Blo 487790 490003 := bstep (se 1 (by rfl) ⟨367502, by rfl⟩ : syracuseStep 490003 = 735005) B735005
theorem B490019 : Blo 487790 490019 := bstep (se 1 (by rfl) ⟨367514, by rfl⟩ : syracuseStep 490019 = 735029) B735029
theorem B490035 : Blo 487790 490035 := bstep (se 1 (by rfl) ⟨367526, by rfl⟩ : syracuseStep 490035 = 735053) B735053
theorem B490051 : Blo 487790 490051 := bstep (se 1 (by rfl) ⟨367538, by rfl⟩ : syracuseStep 490051 = 735077) B735077
theorem B1768013 : Blo 487790 1768013 := bstep (se 3 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 1768013 = 663005) B663005
theorem B490067 : Blo 487790 490067 := bstep (se 1 (by rfl) ⟨367550, by rfl⟩ : syracuseStep 490067 = 735101) B735101
theorem B490083 : Blo 487790 490083 := bstep (se 1 (by rfl) ⟨367562, by rfl⟩ : syracuseStep 490083 = 735125) B735125
theorem B490099 : Blo 487790 490099 := bstep (se 1 (by rfl) ⟨367574, by rfl⟩ : syracuseStep 490099 = 735149) B735149
theorem B785027 : Blo 487790 785027 := bstep (se 1 (by rfl) ⟨588770, by rfl⟩ : syracuseStep 785027 = 1177541) B1177541
theorem B490115 : Blo 487790 490115 := bstep (se 1 (by rfl) ⟨367586, by rfl⟩ : syracuseStep 490115 = 735173) B735173
theorem B490131 : Blo 487790 490131 := bstep (se 1 (by rfl) ⟨367598, by rfl⟩ : syracuseStep 490131 = 735197) B735197
theorem B490147 : Blo 487790 490147 := bstep (se 1 (by rfl) ⟨367610, by rfl⟩ : syracuseStep 490147 = 735221) B735221
theorem B490163 : Blo 487790 490163 := bstep (se 1 (by rfl) ⟨367622, by rfl⟩ : syracuseStep 490163 = 735245) B735245
theorem B490179 : Blo 487790 490179 := bstep (se 1 (by rfl) ⟨367634, by rfl⟩ : syracuseStep 490179 = 735269) B735269
theorem B490195 : Blo 487790 490195 := bstep (se 1 (by rfl) ⟨367646, by rfl⟩ : syracuseStep 490195 = 735293) B735293
theorem B490211 : Blo 487790 490211 := bstep (se 1 (by rfl) ⟨367658, by rfl⟩ : syracuseStep 490211 = 735317) B735317
theorem B490227 : Blo 487790 490227 := bstep (se 1 (by rfl) ⟨367670, by rfl⟩ : syracuseStep 490227 = 735341) B735341
theorem B490243 : Blo 487790 490243 := bstep (se 1 (by rfl) ⟨367682, by rfl⟩ : syracuseStep 490243 = 735365) B735365
theorem B1243907 : Blo 487790 1243907 := bstep (se 1 (by rfl) ⟨932930, by rfl⟩ : syracuseStep 1243907 = 1865861) B1865861
theorem B490259 : Blo 487790 490259 := bstep (se 1 (by rfl) ⟨367694, by rfl⟩ : syracuseStep 490259 = 735389) B735389
theorem B490275 : Blo 487790 490275 := bstep (se 1 (by rfl) ⟨367706, by rfl⟩ : syracuseStep 490275 = 735413) B735413
theorem B1768241 : Blo 487790 1768241 := bstep (se 2 (by rfl) ⟨663090, by rfl⟩ : syracuseStep 1768241 = 1326181) B1326181
theorem B490291 : Blo 487790 490291 := bstep (se 1 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 490291 = 735437) B735437
theorem B490307 : Blo 487790 490307 := bstep (se 1 (by rfl) ⟨367730, by rfl⟩ : syracuseStep 490307 = 735461) B735461
theorem B490323 : Blo 487790 490323 := bstep (se 1 (by rfl) ⟨367742, by rfl⟩ : syracuseStep 490323 = 735485) B735485
theorem B490339 : Blo 487790 490339 := bstep (se 1 (by rfl) ⟨367754, by rfl⟩ : syracuseStep 490339 = 735509) B735509
theorem B490355 : Blo 487790 490355 := bstep (se 1 (by rfl) ⟨367766, by rfl⟩ : syracuseStep 490355 = 735533) B735533
theorem B621427 : Blo 487790 621427 := bstep (se 1 (by rfl) ⟨466070, by rfl⟩ : syracuseStep 621427 = 932141) B932141
theorem B490371 : Blo 487790 490371 := bstep (se 1 (by rfl) ⟨367778, by rfl⟩ : syracuseStep 490371 = 735557) B735557
theorem B1178513 : Blo 487790 1178513 := bstep (se 2 (by rfl) ⟨441942, by rfl⟩ : syracuseStep 1178513 = 883885) B883885
theorem B490387 : Blo 487790 490387 := bstep (se 1 (by rfl) ⟨367790, by rfl⟩ : syracuseStep 490387 = 735581) B735581
theorem B490403 : Blo 487790 490403 := bstep (se 1 (by rfl) ⟨367802, by rfl⟩ : syracuseStep 490403 = 735605) B735605
theorem B490419 : Blo 487790 490419 := bstep (se 1 (by rfl) ⟨367814, by rfl⟩ : syracuseStep 490419 = 735629) B735629
theorem B490435 : Blo 487790 490435 := bstep (se 1 (by rfl) ⟨367826, by rfl⟩ : syracuseStep 490435 = 735653) B735653
theorem B1244099 : Blo 487790 1244099 := bstep (se 1 (by rfl) ⟨933074, by rfl⟩ : syracuseStep 1244099 = 1866149) B1866149
theorem B1047505 : Blo 487790 1047505 := bstep (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) B785629
theorem B490451 : Blo 487790 490451 := bstep (se 1 (by rfl) ⟨367838, by rfl⟩ : syracuseStep 490451 = 735677) B735677
theorem B621523 : Blo 487790 621523 := bstep (se 1 (by rfl) ⟨466142, by rfl⟩ : syracuseStep 621523 = 932285) B932285
theorem B490467 : Blo 487790 490467 := bstep (se 1 (by rfl) ⟨367850, by rfl⟩ : syracuseStep 490467 = 735701) B735701
theorem B490483 : Blo 487790 490483 := bstep (se 1 (by rfl) ⟨367862, by rfl⟩ : syracuseStep 490483 = 735725) B735725
theorem B490499 : Blo 487790 490499 := bstep (se 1 (by rfl) ⟨367874, by rfl⟩ : syracuseStep 490499 = 735749) B735749
theorem B490515 : Blo 487790 490515 := bstep (se 1 (by rfl) ⟨367886, by rfl⟩ : syracuseStep 490515 = 735773) B735773
theorem B490531 : Blo 487790 490531 := bstep (se 1 (by rfl) ⟨367898, by rfl⟩ : syracuseStep 490531 = 735797) B735797
theorem B490547 : Blo 487790 490547 := bstep (se 1 (by rfl) ⟨367910, by rfl⟩ : syracuseStep 490547 = 735821) B735821
theorem B490563 : Blo 487790 490563 := bstep (se 1 (by rfl) ⟨367922, by rfl⟩ : syracuseStep 490563 = 735845) B735845
theorem B490579 : Blo 487790 490579 := bstep (se 1 (by rfl) ⟨367934, by rfl⟩ : syracuseStep 490579 = 735869) B735869
theorem B490595 : Blo 487790 490595 := bstep (se 1 (by rfl) ⟨367946, by rfl⟩ : syracuseStep 490595 = 735893) B735893
theorem B2227313 : Blo 487790 2227313 := bstep (se 2 (by rfl) ⟨835242, by rfl⟩ : syracuseStep 2227313 = 1670485) B1670485
theorem B490611 : Blo 487790 490611 := bstep (se 1 (by rfl) ⟨367958, by rfl⟩ : syracuseStep 490611 = 735917) B735917
theorem B490627 : Blo 487790 490627 := bstep (se 1 (by rfl) ⟨367970, by rfl⟩ : syracuseStep 490627 = 735941) B735941
theorem B490643 : Blo 487790 490643 := bstep (se 1 (by rfl) ⟨367982, by rfl⟩ : syracuseStep 490643 = 735965) B735965
theorem B490659 : Blo 487790 490659 := bstep (se 1 (by rfl) ⟨367994, by rfl⟩ : syracuseStep 490659 = 735989) B735989
theorem B490675 : Blo 487790 490675 := bstep (se 1 (by rfl) ⟨368006, by rfl⟩ : syracuseStep 490675 = 736013) B736013
theorem B490691 : Blo 487790 490691 := bstep (se 1 (by rfl) ⟨368018, by rfl⟩ : syracuseStep 490691 = 736037) B736037
theorem B490707 : Blo 487790 490707 := bstep (se 1 (by rfl) ⟨368030, by rfl⟩ : syracuseStep 490707 = 736061) B736061
theorem B490723 : Blo 487790 490723 := bstep (se 1 (by rfl) ⟨368042, by rfl⟩ : syracuseStep 490723 = 736085) B736085
theorem B490739 : Blo 487790 490739 := bstep (se 1 (by rfl) ⟨368054, by rfl⟩ : syracuseStep 490739 = 736109) B736109
theorem B490755 : Blo 487790 490755 := bstep (se 1 (by rfl) ⟨368066, by rfl⟩ : syracuseStep 490755 = 736133) B736133
theorem B490771 : Blo 487790 490771 := bstep (se 1 (by rfl) ⟨368078, by rfl⟩ : syracuseStep 490771 = 736157) B736157
theorem B490787 : Blo 487790 490787 := bstep (se 1 (by rfl) ⟨368090, by rfl⟩ : syracuseStep 490787 = 736181) B736181
theorem B490803 : Blo 487790 490803 := bstep (se 1 (by rfl) ⟨368102, by rfl⟩ : syracuseStep 490803 = 736205) B736205
theorem B490819 : Blo 487790 490819 := bstep (se 1 (by rfl) ⟨368114, by rfl⟩ : syracuseStep 490819 = 736229) B736229
theorem B490835 : Blo 487790 490835 := bstep (se 1 (by rfl) ⟨368126, by rfl⟩ : syracuseStep 490835 = 736253) B736253
theorem B1047907 : Blo 487790 1047907 := bstep (se 1 (by rfl) ⟨785930, by rfl⟩ : syracuseStep 1047907 = 1571861) B1571861
theorem B490851 : Blo 487790 490851 := bstep (se 1 (by rfl) ⟨368138, by rfl⟩ : syracuseStep 490851 = 736277) B736277
theorem B1867121 : Blo 487790 1867121 := bstep (se 2 (by rfl) ⟨700170, by rfl⟩ : syracuseStep 1867121 = 1400341) B1400341
theorem B490867 : Blo 487790 490867 := bstep (se 1 (by rfl) ⟨368150, by rfl⟩ : syracuseStep 490867 = 736301) B736301
theorem B490883 : Blo 487790 490883 := bstep (se 1 (by rfl) ⟨368162, by rfl⟩ : syracuseStep 490883 = 736325) B736325
theorem B490899 : Blo 487790 490899 := bstep (se 1 (by rfl) ⟨368174, by rfl⟩ : syracuseStep 490899 = 736349) B736349
theorem B490915 : Blo 487790 490915 := bstep (se 1 (by rfl) ⟨368186, by rfl⟩ : syracuseStep 490915 = 736373) B736373
theorem B2784689 : Blo 487790 2784689 := bstep (se 2 (by rfl) ⟨1044258, by rfl⟩ : syracuseStep 2784689 = 2088517) B2088517
theorem B490931 : Blo 487790 490931 := bstep (se 1 (by rfl) ⟨368198, by rfl⟩ : syracuseStep 490931 = 736397) B736397
theorem B490947 : Blo 487790 490947 := bstep (se 1 (by rfl) ⟨368210, by rfl⟩ : syracuseStep 490947 = 736421) B736421
theorem B622019 : Blo 487790 622019 := bstep (se 1 (by rfl) ⟨466514, by rfl⟩ : syracuseStep 622019 = 933029) B933029
theorem B490963 : Blo 487790 490963 := bstep (se 1 (by rfl) ⟨368222, by rfl⟩ : syracuseStep 490963 = 736445) B736445
theorem B490979 : Blo 487790 490979 := bstep (se 1 (by rfl) ⟨368234, by rfl⟩ : syracuseStep 490979 = 736469) B736469
theorem B1703405 : Blo 487790 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B490995 : Blo 487790 490995 := bstep (se 1 (by rfl) ⟨368246, by rfl⟩ : syracuseStep 490995 = 736493) B736493
theorem B491011 : Blo 487790 491011 := bstep (se 1 (by rfl) ⟨368258, by rfl⟩ : syracuseStep 491011 = 736517) B736517
theorem B491027 : Blo 487790 491027 := bstep (se 1 (by rfl) ⟨368270, by rfl⟩ : syracuseStep 491027 = 736541) B736541
theorem B491043 : Blo 487790 491043 := bstep (se 1 (by rfl) ⟨368282, by rfl⟩ : syracuseStep 491043 = 736565) B736565
theorem B491059 : Blo 487790 491059 := bstep (se 1 (by rfl) ⟨368294, by rfl⟩ : syracuseStep 491059 = 736589) B736589
theorem B1179203 : Blo 487790 1179203 := bstep (se 1 (by rfl) ⟨884402, by rfl⟩ : syracuseStep 1179203 = 1768805) B1768805
theorem B491075 : Blo 487790 491075 := bstep (se 1 (by rfl) ⟨368306, by rfl⟩ : syracuseStep 491075 = 736613) B736613
theorem B491091 : Blo 487790 491091 := bstep (se 1 (by rfl) ⟨368318, by rfl⟩ : syracuseStep 491091 = 736637) B736637
theorem B491107 : Blo 487790 491107 := bstep (se 1 (by rfl) ⟨368330, by rfl⟩ : syracuseStep 491107 = 736661) B736661
theorem B491123 : Blo 487790 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B491139 : Blo 487790 491139 := bstep (se 1 (by rfl) ⟨368354, by rfl⟩ : syracuseStep 491139 = 736709) B736709
theorem B491155 : Blo 487790 491155 := bstep (se 1 (by rfl) ⟨368366, by rfl⟩ : syracuseStep 491155 = 736733) B736733
theorem B491171 : Blo 487790 491171 := bstep (se 1 (by rfl) ⟨368378, by rfl⟩ : syracuseStep 491171 = 736757) B736757
theorem B491187 : Blo 487790 491187 := bstep (se 1 (by rfl) ⟨368390, by rfl⟩ : syracuseStep 491187 = 736781) B736781
theorem B491203 : Blo 487790 491203 := bstep (se 1 (by rfl) ⟨368402, by rfl⟩ : syracuseStep 491203 = 736805) B736805
theorem B2981573 : Blo 487790 2981573 := bstep (se 4 (by rfl) ⟨279522, by rfl⟩ : syracuseStep 2981573 = 559045) B559045
theorem B1769165 : Blo 487790 1769165 := bstep (se 3 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 1769165 = 663437) B663437
theorem B491219 : Blo 487790 491219 := bstep (se 1 (by rfl) ⟨368414, by rfl⟩ : syracuseStep 491219 = 736829) B736829
theorem B491235 : Blo 487790 491235 := bstep (se 1 (by rfl) ⟨368426, by rfl⟩ : syracuseStep 491235 = 736853) B736853
theorem B491251 : Blo 487790 491251 := bstep (se 1 (by rfl) ⟨368438, by rfl⟩ : syracuseStep 491251 = 736877) B736877
theorem B491267 : Blo 487790 491267 := bstep (se 1 (by rfl) ⟨368450, by rfl⟩ : syracuseStep 491267 = 736901) B736901
theorem B491283 : Blo 487790 491283 := bstep (se 1 (by rfl) ⟨368462, by rfl⟩ : syracuseStep 491283 = 736925) B736925
theorem B491299 : Blo 487790 491299 := bstep (se 1 (by rfl) ⟨368474, by rfl⟩ : syracuseStep 491299 = 736949) B736949
theorem B491315 : Blo 487790 491315 := bstep (se 1 (by rfl) ⟨368486, by rfl⟩ : syracuseStep 491315 = 736973) B736973
theorem B491331 : Blo 487790 491331 := bstep (se 1 (by rfl) ⟨368498, by rfl⟩ : syracuseStep 491331 = 736997) B736997
theorem B491347 : Blo 487790 491347 := bstep (se 1 (by rfl) ⟨368510, by rfl⟩ : syracuseStep 491347 = 737021) B737021
theorem B491363 : Blo 487790 491363 := bstep (se 1 (by rfl) ⟨368522, by rfl⟩ : syracuseStep 491363 = 737045) B737045
theorem B491379 : Blo 487790 491379 := bstep (se 1 (by rfl) ⟨368534, by rfl⟩ : syracuseStep 491379 = 737069) B737069
theorem B491395 : Blo 487790 491395 := bstep (se 1 (by rfl) ⟨368546, by rfl⟩ : syracuseStep 491395 = 737093) B737093
theorem B491411 : Blo 487790 491411 := bstep (se 1 (by rfl) ⟨368558, by rfl⟩ : syracuseStep 491411 = 737117) B737117
theorem B491427 : Blo 487790 491427 := bstep (se 1 (by rfl) ⟨368570, by rfl⟩ : syracuseStep 491427 = 737141) B737141
theorem B491443 : Blo 487790 491443 := bstep (se 1 (by rfl) ⟨368582, by rfl⟩ : syracuseStep 491443 = 737165) B737165
theorem B524227 : Blo 487790 524227 := bstep (se 1 (by rfl) ⟨393170, by rfl⟩ : syracuseStep 524227 = 786341) B786341
theorem B491459 : Blo 487790 491459 := bstep (se 1 (by rfl) ⟨368594, by rfl⟩ : syracuseStep 491459 = 737189) B737189
theorem B491475 : Blo 487790 491475 := bstep (se 1 (by rfl) ⟨368606, by rfl⟩ : syracuseStep 491475 = 737213) B737213
theorem B491491 : Blo 487790 491491 := bstep (se 1 (by rfl) ⟨368618, by rfl⟩ : syracuseStep 491491 = 737237) B737237
theorem B491507 : Blo 487790 491507 := bstep (se 1 (by rfl) ⟨368630, by rfl⟩ : syracuseStep 491507 = 737261) B737261
theorem B491531 : Blo 487790 491531 := bstep (se 1 (by rfl) ⟨368648, by rfl⟩ : syracuseStep 491531 = 737297) B737297
theorem B491543 : Blo 487790 491543 := bstep (se 1 (by rfl) ⟨368657, by rfl⟩ : syracuseStep 491543 = 737315) B737315
theorem B491563 : Blo 487790 491563 := bstep (se 1 (by rfl) ⟨368672, by rfl⟩ : syracuseStep 491563 = 737345) B737345
theorem B2097197 : Blo 487790 2097197 := bstep (se 3 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 2097197 = 786449) B786449
theorem B491575 : Blo 487790 491575 := bstep (se 1 (by rfl) ⟨368681, by rfl⟩ : syracuseStep 491575 = 737363) B737363
theorem B491595 : Blo 487790 491595 := bstep (se 1 (by rfl) ⟨368696, by rfl⟩ : syracuseStep 491595 = 737393) B737393
theorem B491607 : Blo 487790 491607 := bstep (se 1 (by rfl) ⟨368705, by rfl⟩ : syracuseStep 491607 = 737411) B737411
theorem B2785373 : Blo 487790 2785373 := bstep (se 3 (by rfl) ⟨522257, by rfl⟩ : syracuseStep 2785373 = 1044515) B1044515
theorem B491627 : Blo 487790 491627 := bstep (se 1 (by rfl) ⟨368720, by rfl⟩ : syracuseStep 491627 = 737441) B737441
theorem B491639 : Blo 487790 491639 := bstep (se 1 (by rfl) ⟨368729, by rfl⟩ : syracuseStep 491639 = 737459) B737459
theorem B491659 : Blo 487790 491659 := bstep (se 1 (by rfl) ⟨368744, by rfl⟩ : syracuseStep 491659 = 737489) B737489
theorem B1048727 : Blo 487790 1048727 := bstep (se 1 (by rfl) ⟨786545, by rfl⟩ : syracuseStep 1048727 = 1573091) B1573091
theorem B491671 : Blo 487790 491671 := bstep (se 1 (by rfl) ⟨368753, by rfl⟩ : syracuseStep 491671 = 737507) B737507
theorem B491691 : Blo 487790 491691 := bstep (se 1 (by rfl) ⟨368768, by rfl⟩ : syracuseStep 491691 = 737537) B737537
theorem B491703 : Blo 487790 491703 := bstep (se 1 (by rfl) ⟨368777, by rfl⟩ : syracuseStep 491703 = 737555) B737555
theorem B491723 : Blo 487790 491723 := bstep (se 1 (by rfl) ⟨368792, by rfl⟩ : syracuseStep 491723 = 737585) B737585
theorem B491735 : Blo 487790 491735 := bstep (se 1 (by rfl) ⟨368801, by rfl⟩ : syracuseStep 491735 = 737603) B737603
theorem B491755 : Blo 487790 491755 := bstep (se 1 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 491755 = 737633) B737633
theorem B491767 : Blo 487790 491767 := bstep (se 1 (by rfl) ⟨368825, by rfl⟩ : syracuseStep 491767 = 737651) B737651
theorem B491787 : Blo 487790 491787 := bstep (se 1 (by rfl) ⟨368840, by rfl⟩ : syracuseStep 491787 = 737681) B737681
theorem B2097539 : Blo 487790 2097539 := bstep (se 1 (by rfl) ⟨1573154, by rfl⟩ : syracuseStep 2097539 = 3146309) B3146309
theorem B786905 : Blo 487790 786905 := bstep (se 2 (by rfl) ⟨295089, by rfl⟩ : syracuseStep 786905 = 590179) B590179
theorem B852619 : Blo 487790 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B525047 : Blo 487790 525047 := bstep (se 1 (by rfl) ⟨393785, by rfl⟩ : syracuseStep 525047 = 787571) B787571
theorem B885505 : Blo 487790 885505 := bstep (se 2 (by rfl) ⟨332064, by rfl⟩ : syracuseStep 885505 = 664129) B664129
theorem B1049753 : Blo 487790 1049753 := bstep (se 2 (by rfl) ⟨393657, by rfl⟩ : syracuseStep 1049753 = 787315) B787315
theorem B3147025 : Blo 487790 3147025 := bstep (se 2 (by rfl) ⟨1180134, by rfl⟩ : syracuseStep 3147025 = 2360269) B2360269
theorem B3180305 : Blo 487790 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B1574731 : Blo 487790 1574731 := bstep (se 1 (by rfl) ⟨1181048, by rfl⟩ : syracuseStep 1574731 = 2362097) B2362097
theorem B1115993 : Blo 487790 1115993 := bstep (se 2 (by rfl) ⟨418497, by rfl⟩ : syracuseStep 1115993 = 836995) B836995
theorem B1771415 : Blo 487790 1771415 := bstep (se 1 (by rfl) ⟨1328561, by rfl⟩ : syracuseStep 1771415 = 2657123) B2657123
theorem B1574873 : Blo 487790 1574873 := bstep (se 2 (by rfl) ⟨590577, by rfl⟩ : syracuseStep 1574873 = 1181155) B1181155
theorem B756119 : Blo 487790 756119 := bstep (se 1 (by rfl) ⟨567089, by rfl⟩ : syracuseStep 756119 = 1134179) B1134179
theorem B1116595 : Blo 487790 1116595 := bstep (se 1 (by rfl) ⟨837446, by rfl⟩ : syracuseStep 1116595 = 1674893) B1674893
theorem B3574277 : Blo 487790 3574277 := bstep (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) B670177
theorem B2787857 : Blo 487790 2787857 := bstep (se 2 (by rfl) ⟨1045446, by rfl⟩ : syracuseStep 2787857 = 2090893) B2090893
theorem B2099915 : Blo 487790 2099915 := bstep (se 1 (by rfl) ⟨1574936, by rfl⟩ : syracuseStep 2099915 = 3149873) B3149873
theorem B1772381 : Blo 487790 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B2231219 : Blo 487790 2231219 := bstep (se 1 (by rfl) ⟨1673414, by rfl⟩ : syracuseStep 2231219 = 3346829) B3346829
theorem B5573933 : Blo 487790 5573933 := bstep (se 3 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 5573933 = 2090225) B2090225
theorem B2690833 : Blo 487790 2690833 := bstep (se 2 (by rfl) ⟨1009062, by rfl⟩ : syracuseStep 2690833 = 2018125) B2018125
theorem B823243 : Blo 487790 823243 := bstep (se 1 (by rfl) ⟨617432, by rfl⟩ : syracuseStep 823243 = 1234865) B1234865
theorem B30642245 : Blo 487790 30642245 := bstep (se 4 (by rfl) ⟨2872710, by rfl⟩ : syracuseStep 30642245 = 5745421) B5745421
theorem B823385 : Blo 487790 823385 := bstep (se 2 (by rfl) ⟨308769, by rfl⟩ : syracuseStep 823385 = 617539) B617539
theorem B4198493 : Blo 487790 4198493 := bstep (se 3 (by rfl) ⟨787217, by rfl⟩ : syracuseStep 4198493 = 1574435) B1574435
theorem B823513 : Blo 487790 823513 := bstep (se 2 (by rfl) ⟨308817, by rfl⟩ : syracuseStep 823513 = 617635) B617635
theorem B14127473 : Blo 487790 14127473 := bstep (se 2 (by rfl) ⟨5297802, by rfl⟩ : syracuseStep 14127473 = 10595605) B10595605
theorem B660107 : Blo 487790 660107 := bstep (se 1 (by rfl) ⟨495080, by rfl⟩ : syracuseStep 660107 = 990161) B990161
theorem B824087 : Blo 487790 824087 := bstep (se 1 (by rfl) ⟨618065, by rfl⟩ : syracuseStep 824087 = 1236131) B1236131
theorem B3707693 : Blo 487790 3707693 := bstep (se 3 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 3707693 = 1390385) B1390385
theorem B824215 : Blo 487790 824215 := bstep (se 1 (by rfl) ⟨618161, by rfl⟩ : syracuseStep 824215 = 1236323) B1236323
theorem B2233261 : Blo 487790 2233261 := bstep (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) B837473
theorem B4690979 : Blo 487790 4690979 := bstep (se 1 (by rfl) ⟨3518234, by rfl⟩ : syracuseStep 4690979 = 7036469) B7036469
theorem B824843 : Blo 487790 824843 := bstep (se 1 (by rfl) ⟨618632, by rfl⟩ : syracuseStep 824843 = 1237265) B1237265
theorem B824971 : Blo 487790 824971 := bstep (se 1 (by rfl) ⟨618728, by rfl⟩ : syracuseStep 824971 = 1237457) B1237457
theorem B825113 : Blo 487790 825113 := bstep (se 2 (by rfl) ⟨309417, by rfl⟩ : syracuseStep 825113 = 618835) B618835
theorem B989057 : Blo 487790 989057 := bstep (se 2 (by rfl) ⟨370896, by rfl⟩ : syracuseStep 989057 = 741793) B741793
theorem B825241 : Blo 487790 825241 := bstep (se 2 (by rfl) ⟨309465, by rfl⟩ : syracuseStep 825241 = 618931) B618931
theorem B497707 : Blo 487790 497707 := bstep (se 1 (by rfl) ⟨373280, by rfl⟩ : syracuseStep 497707 = 746561) B746561
theorem B891329 : Blo 487790 891329 := bstep (se 2 (by rfl) ⟨334248, by rfl⟩ : syracuseStep 891329 = 668497) B668497
theorem B2267585 : Blo 487790 2267585 := bstep (se 2 (by rfl) ⟨850344, by rfl⟩ : syracuseStep 2267585 = 1700689) B1700689
theorem B825815 : Blo 487790 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B825943 : Blo 487790 825943 := bstep (se 1 (by rfl) ⟨619457, by rfl⟩ : syracuseStep 825943 = 1238915) B1238915
theorem B4201091 : Blo 487790 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B1088257 : Blo 487790 1088257 := bstep (se 2 (by rfl) ⟨408096, by rfl⟩ : syracuseStep 1088257 = 816193) B816193
theorem B629579 : Blo 487790 629579 := bstep (se 1 (by rfl) ⟨472184, by rfl⟩ : syracuseStep 629579 = 944369) B944369
theorem B7183511 : Blo 487790 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B826571 : Blo 487790 826571 := bstep (se 1 (by rfl) ⟨619928, by rfl⟩ : syracuseStep 826571 = 1239857) B1239857
theorem B826699 : Blo 487790 826699 := bstep (se 1 (by rfl) ⟨620024, by rfl⟩ : syracuseStep 826699 = 1240049) B1240049
theorem B2006417 : Blo 487790 2006417 := bstep (se 2 (by rfl) ⟨752406, by rfl⟩ : syracuseStep 2006417 = 1504813) B1504813
theorem B826841 : Blo 487790 826841 := bstep (se 2 (by rfl) ⟨310065, by rfl⟩ : syracuseStep 826841 = 620131) B620131
theorem B826969 : Blo 487790 826969 := bstep (se 2 (by rfl) ⟨310113, by rfl⟩ : syracuseStep 826969 = 620227) B620227
theorem B1646297 : Blo 487790 1646297 := bstep (se 2 (by rfl) ⟨617361, by rfl⟩ : syracuseStep 1646297 = 1234723) B1234723
theorem B18816947 : Blo 487790 18816947 := bstep (se 1 (by rfl) ⟨14112710, by rfl⟩ : syracuseStep 18816947 = 28225421) B28225421
theorem B3317777 : Blo 487790 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B991361 : Blo 487790 991361 := bstep (se 2 (by rfl) ⟨371760, by rfl⟩ : syracuseStep 991361 = 743521) B743521
theorem B827543 : Blo 487790 827543 := bstep (se 1 (by rfl) ⟨620657, by rfl⟩ : syracuseStep 827543 = 1241315) B1241315
theorem B2793689 : Blo 487790 2793689 := bstep (se 2 (by rfl) ⟨1047633, by rfl⟩ : syracuseStep 2793689 = 2095267) B2095267
theorem B1286423 : Blo 487790 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B827671 : Blo 487790 827671 := bstep (se 1 (by rfl) ⟨620753, by rfl⟩ : syracuseStep 827671 = 1241507) B1241507
theorem B1319261 : Blo 487790 1319261 := bstep (se 3 (by rfl) ⟨247361, by rfl⟩ : syracuseStep 1319261 = 494723) B494723
theorem B1646999 : Blo 487790 1646999 := bstep (se 1 (by rfl) ⟨1235249, by rfl⟩ : syracuseStep 1646999 = 2470499) B2470499
theorem B3350963 : Blo 487790 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B696919 : Blo 487790 696919 := bstep (se 1 (by rfl) ⟨522689, by rfl⟩ : syracuseStep 696919 = 1045379) B1045379
theorem B3711581 : Blo 487790 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B664345 : Blo 487790 664345 := bstep (se 2 (by rfl) ⟨249129, by rfl⟩ : syracuseStep 664345 = 498259) B498259
theorem B828299 : Blo 487790 828299 := bstep (se 1 (by rfl) ⟨621224, by rfl⟩ : syracuseStep 828299 = 1242449) B1242449
theorem B1647539 : Blo 487790 1647539 := bstep (se 1 (by rfl) ⟨1235654, by rfl⟩ : syracuseStep 1647539 = 2471309) B2471309
theorem B828427 : Blo 487790 828427 := bstep (se 1 (by rfl) ⟨621320, by rfl⟩ : syracuseStep 828427 = 1242641) B1242641
theorem B926795 : Blo 487790 926795 := bstep (se 1 (by rfl) ⟨695096, by rfl⟩ : syracuseStep 926795 = 1390193) B1390193
theorem B828569 : Blo 487790 828569 := bstep (se 2 (by rfl) ⟨310713, by rfl⟩ : syracuseStep 828569 = 621427) B621427
theorem B1647809 : Blo 487790 1647809 := bstep (se 2 (by rfl) ⟨617928, by rfl⟩ : syracuseStep 1647809 = 1235857) B1235857
theorem B926977 : Blo 487790 926977 := bstep (se 2 (by rfl) ⟨347616, by rfl⟩ : syracuseStep 926977 = 695233) B695233
theorem B992513 : Blo 487790 992513 := bstep (se 2 (by rfl) ⟨372192, by rfl⟩ : syracuseStep 992513 = 744385) B744385
theorem B828697 : Blo 487790 828697 := bstep (se 2 (by rfl) ⟨310761, by rfl⟩ : syracuseStep 828697 = 621523) B621523
theorem B927425 : Blo 487790 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B1648349 : Blo 487790 1648349 := bstep (se 3 (by rfl) ⟨309065, by rfl⟩ : syracuseStep 1648349 = 618131) B618131
theorem B829271 : Blo 487790 829271 := bstep (se 1 (by rfl) ⟨621953, by rfl⟩ : syracuseStep 829271 = 1243907) B1243907
theorem B1320907 : Blo 487790 1320907 := bstep (se 1 (by rfl) ⟨990680, by rfl⟩ : syracuseStep 1320907 = 1981361) B1981361
theorem B829399 : Blo 487790 829399 := bstep (se 1 (by rfl) ⟨622049, by rfl⟩ : syracuseStep 829399 = 1244099) B1244099
theorem B927767 : Blo 487790 927767 := bstep (se 1 (by rfl) ⟨695825, by rfl⟩ : syracuseStep 927767 = 1391651) B1391651
theorem B1484875 : Blo 487790 1484875 := bstep (se 1 (by rfl) ⟨1113656, by rfl⟩ : syracuseStep 1484875 = 2227313) B2227313
theorem B7088309 : Blo 487790 7088309 := bstep (se 5 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 7088309 = 664529) B664529
theorem B4172249 : Blo 487790 4172249 := bstep (se 2 (by rfl) ⟨1564593, by rfl⟩ : syracuseStep 4172249 = 3129187) B3129187
theorem B731723 : Blo 487790 731723 := bstep (se 1 (by rfl) ⟨548792, by rfl⟩ : syracuseStep 731723 = 1097585) B1097585
theorem B731735 : Blo 487790 731735 := bstep (se 1 (by rfl) ⟨548801, by rfl⟩ : syracuseStep 731735 = 1097603) B1097603
theorem B698969 : Blo 487790 698969 := bstep (se 2 (by rfl) ⟨262113, by rfl⟩ : syracuseStep 698969 = 524227) B524227
theorem B7547543 : Blo 487790 7547543 := bstep (se 1 (by rfl) ⟨5660657, by rfl⟩ : syracuseStep 7547543 = 11321315) B11321315
theorem B731801 : Blo 487790 731801 := bstep (se 2 (by rfl) ⟨274425, by rfl⟩ : syracuseStep 731801 = 548851) B548851
theorem B928435 : Blo 487790 928435 := bstep (se 1 (by rfl) ⟨696326, by rfl⟩ : syracuseStep 928435 = 1392653) B1392653
theorem B731915 : Blo 487790 731915 := bstep (se 1 (by rfl) ⟨548936, by rfl⟩ : syracuseStep 731915 = 1097873) B1097873
theorem B731927 : Blo 487790 731927 := bstep (se 1 (by rfl) ⟨548945, by rfl⟩ : syracuseStep 731927 = 1097891) B1097891
theorem B2796353 : Blo 487790 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B1649483 : Blo 487790 1649483 := bstep (se 1 (by rfl) ⟨1237112, by rfl⟩ : syracuseStep 1649483 = 2474225) B2474225
theorem B731993 : Blo 487790 731993 := bstep (se 2 (by rfl) ⟨274497, by rfl⟩ : syracuseStep 731993 = 548995) B548995
theorem B732107 : Blo 487790 732107 := bstep (se 1 (by rfl) ⟨549080, by rfl⟩ : syracuseStep 732107 = 1098161) B1098161
theorem B732119 : Blo 487790 732119 := bstep (se 1 (by rfl) ⟨549089, by rfl⟩ : syracuseStep 732119 = 1098179) B1098179
theorem B732185 : Blo 487790 732185 := bstep (se 2 (by rfl) ⟨274569, by rfl⟩ : syracuseStep 732185 = 549139) B549139
theorem B15051845 : Blo 487790 15051845 := bstep (se 4 (by rfl) ⟨1411110, by rfl⟩ : syracuseStep 15051845 = 2822221) B2822221
theorem B1649753 : Blo 487790 1649753 := bstep (se 2 (by rfl) ⟨618657, by rfl⟩ : syracuseStep 1649753 = 1237315) B1237315
theorem B928883 : Blo 487790 928883 := bstep (se 1 (by rfl) ⟨696662, by rfl⟩ : syracuseStep 928883 = 1393325) B1393325
theorem B732299 : Blo 487790 732299 := bstep (se 1 (by rfl) ⟨549224, by rfl⟩ : syracuseStep 732299 = 1098449) B1098449
theorem B732311 : Blo 487790 732311 := bstep (se 1 (by rfl) ⟨549233, by rfl⟩ : syracuseStep 732311 = 1098467) B1098467
theorem B928921 : Blo 487790 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B699607 : Blo 487790 699607 := bstep (se 1 (by rfl) ⟨524705, by rfl⟩ : syracuseStep 699607 = 1049411) B1049411
theorem B732377 : Blo 487790 732377 := bstep (se 2 (by rfl) ⟨274641, by rfl⟩ : syracuseStep 732377 = 549283) B549283
theorem B896243 : Blo 487790 896243 := bstep (se 1 (by rfl) ⟨672182, by rfl⟩ : syracuseStep 896243 = 1344365) B1344365
theorem B732491 : Blo 487790 732491 := bstep (se 1 (by rfl) ⟨549368, by rfl⟩ : syracuseStep 732491 = 1098737) B1098737
theorem B732503 : Blo 487790 732503 := bstep (se 1 (by rfl) ⟨549377, by rfl⟩ : syracuseStep 732503 = 1098755) B1098755
theorem B8367461 : Blo 487790 8367461 := bstep (se 4 (by rfl) ⟨784449, by rfl⟩ : syracuseStep 8367461 = 1568899) B1568899
theorem B732569 : Blo 487790 732569 := bstep (se 2 (by rfl) ⟨274713, by rfl⟩ : syracuseStep 732569 = 549427) B549427
theorem B732683 : Blo 487790 732683 := bstep (se 1 (by rfl) ⟨549512, by rfl⟩ : syracuseStep 732683 = 1099025) B1099025
theorem B732695 : Blo 487790 732695 := bstep (se 1 (by rfl) ⟨549521, by rfl⟩ : syracuseStep 732695 = 1099043) B1099043
theorem B732761 : Blo 487790 732761 := bstep (se 2 (by rfl) ⟨274785, by rfl⟩ : syracuseStep 732761 = 549571) B549571
theorem B929369 : Blo 487790 929369 := bstep (se 2 (by rfl) ⟨348513, by rfl⟩ : syracuseStep 929369 = 697027) B697027
theorem B2469527 : Blo 487790 2469527 := bstep (se 1 (by rfl) ⟨1852145, by rfl⟩ : syracuseStep 2469527 = 3704291) B3704291
theorem B732875 : Blo 487790 732875 := bstep (se 1 (by rfl) ⟨549656, by rfl⟩ : syracuseStep 732875 = 1099313) B1099313
theorem B732887 : Blo 487790 732887 := bstep (se 1 (by rfl) ⟨549665, by rfl⟩ : syracuseStep 732887 = 1099331) B1099331
theorem B1060619 : Blo 487790 1060619 := bstep (se 1 (by rfl) ⟨795464, by rfl⟩ : syracuseStep 1060619 = 1590929) B1590929
theorem B1650455 : Blo 487790 1650455 := bstep (se 1 (by rfl) ⟨1237841, by rfl⟩ : syracuseStep 1650455 = 2475683) B2475683
theorem B732953 : Blo 487790 732953 := bstep (se 2 (by rfl) ⟨274857, by rfl⟩ : syracuseStep 732953 = 549715) B549715
theorem B733067 : Blo 487790 733067 := bstep (se 1 (by rfl) ⟨549800, by rfl⟩ : syracuseStep 733067 = 1099601) B1099601
theorem B733079 : Blo 487790 733079 := bstep (se 1 (by rfl) ⟨549809, by rfl⟩ : syracuseStep 733079 = 1099619) B1099619
theorem B733145 : Blo 487790 733145 := bstep (se 2 (by rfl) ⟨274929, by rfl⟩ : syracuseStep 733145 = 549859) B549859
theorem B4173889 : Blo 487790 4173889 := bstep (se 2 (by rfl) ⟨1565208, by rfl⟩ : syracuseStep 4173889 = 3130417) B3130417
theorem B733259 : Blo 487790 733259 := bstep (se 1 (by rfl) ⟨549944, by rfl⟩ : syracuseStep 733259 = 1099889) B1099889
theorem B733271 : Blo 487790 733271 := bstep (se 1 (by rfl) ⟨549953, by rfl⟩ : syracuseStep 733271 = 1099907) B1099907
theorem B733337 : Blo 487790 733337 := bstep (se 2 (by rfl) ⟨275001, by rfl⟩ : syracuseStep 733337 = 550003) B550003
theorem B733451 : Blo 487790 733451 := bstep (se 1 (by rfl) ⟨550088, by rfl⟩ : syracuseStep 733451 = 1100177) B1100177
theorem B733463 : Blo 487790 733463 := bstep (se 1 (by rfl) ⟨550097, by rfl⟩ : syracuseStep 733463 = 1100195) B1100195
theorem B1650995 : Blo 487790 1650995 := bstep (se 1 (by rfl) ⟨1238246, by rfl⟩ : syracuseStep 1650995 = 2476493) B2476493
theorem B930113 : Blo 487790 930113 := bstep (se 2 (by rfl) ⟨348792, by rfl⟩ : syracuseStep 930113 = 697585) B697585
theorem B733529 : Blo 487790 733529 := bstep (se 2 (by rfl) ⟨275073, by rfl⟩ : syracuseStep 733529 = 550147) B550147
theorem B733643 : Blo 487790 733643 := bstep (se 1 (by rfl) ⟨550232, by rfl⟩ : syracuseStep 733643 = 1100465) B1100465
theorem B733655 : Blo 487790 733655 := bstep (se 1 (by rfl) ⟨550241, by rfl⟩ : syracuseStep 733655 = 1100483) B1100483
theorem B733721 : Blo 487790 733721 := bstep (se 2 (by rfl) ⟨275145, by rfl⟩ : syracuseStep 733721 = 550291) B550291
theorem B1651265 : Blo 487790 1651265 := bstep (se 2 (by rfl) ⟨619224, by rfl⟩ : syracuseStep 1651265 = 1238449) B1238449
theorem B930379 : Blo 487790 930379 := bstep (se 1 (by rfl) ⟨697784, by rfl⟩ : syracuseStep 930379 = 1395569) B1395569
theorem B733835 : Blo 487790 733835 := bstep (se 1 (by rfl) ⟨550376, by rfl⟩ : syracuseStep 733835 = 1100753) B1100753
theorem B733847 : Blo 487790 733847 := bstep (se 1 (by rfl) ⟨550385, by rfl⟩ : syracuseStep 733847 = 1100771) B1100771
theorem B733913 : Blo 487790 733913 := bstep (se 2 (by rfl) ⟨275217, by rfl⟩ : syracuseStep 733913 = 550435) B550435
theorem B1815313 : Blo 487790 1815313 := bstep (se 2 (by rfl) ⟨680742, by rfl⟩ : syracuseStep 1815313 = 1361485) B1361485
theorem B2241325 : Blo 487790 2241325 := bstep (se 3 (by rfl) ⟨420248, by rfl⟩ : syracuseStep 2241325 = 840497) B840497
theorem B734027 : Blo 487790 734027 := bstep (se 1 (by rfl) ⟨550520, by rfl⟩ : syracuseStep 734027 = 1101041) B1101041
theorem B734039 : Blo 487790 734039 := bstep (se 1 (by rfl) ⟨550529, by rfl⟩ : syracuseStep 734039 = 1101059) B1101059
theorem B734105 : Blo 487790 734105 := bstep (se 2 (by rfl) ⟨275289, by rfl⟩ : syracuseStep 734105 = 550579) B550579
theorem B1323955 : Blo 487790 1323955 := bstep (se 1 (by rfl) ⟨992966, by rfl⟩ : syracuseStep 1323955 = 1985933) B1985933
theorem B734219 : Blo 487790 734219 := bstep (se 1 (by rfl) ⟨550664, by rfl⟩ : syracuseStep 734219 = 1101329) B1101329
theorem B930827 : Blo 487790 930827 := bstep (se 1 (by rfl) ⟨698120, by rfl⟩ : syracuseStep 930827 = 1396241) B1396241
theorem B734231 : Blo 487790 734231 := bstep (se 1 (by rfl) ⟨550673, by rfl⟩ : syracuseStep 734231 = 1101347) B1101347
theorem B734297 : Blo 487790 734297 := bstep (se 2 (by rfl) ⟨275361, by rfl⟩ : syracuseStep 734297 = 550723) B550723
theorem B1651805 : Blo 487790 1651805 := bstep (se 3 (by rfl) ⟨309713, by rfl⟩ : syracuseStep 1651805 = 619427) B619427
theorem B1324183 : Blo 487790 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B931009 : Blo 487790 931009 := bstep (se 2 (by rfl) ⟨349128, by rfl⟩ : syracuseStep 931009 = 698257) B698257
theorem B734411 : Blo 487790 734411 := bstep (se 1 (by rfl) ⟨550808, by rfl⟩ : syracuseStep 734411 = 1101617) B1101617
theorem B734423 : Blo 487790 734423 := bstep (se 1 (by rfl) ⟨550817, by rfl⟩ : syracuseStep 734423 = 1101635) B1101635
theorem B734489 : Blo 487790 734489 := bstep (se 2 (by rfl) ⟨275433, by rfl⟩ : syracuseStep 734489 = 550867) B550867
theorem B3519875 : Blo 487790 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B734603 : Blo 487790 734603 := bstep (se 1 (by rfl) ⟨550952, by rfl⟩ : syracuseStep 734603 = 1101905) B1101905
theorem B734615 : Blo 487790 734615 := bstep (se 1 (by rfl) ⟨550961, by rfl⟩ : syracuseStep 734615 = 1101923) B1101923
theorem B734681 : Blo 487790 734681 := bstep (se 2 (by rfl) ⟨275505, by rfl⟩ : syracuseStep 734681 = 551011) B551011
theorem B931351 : Blo 487790 931351 := bstep (se 1 (by rfl) ⟨698513, by rfl⟩ : syracuseStep 931351 = 1397027) B1397027
theorem B734795 : Blo 487790 734795 := bstep (se 1 (by rfl) ⟨551096, by rfl⟩ : syracuseStep 734795 = 1102193) B1102193
theorem B734807 : Blo 487790 734807 := bstep (se 1 (by rfl) ⟨551105, by rfl⟩ : syracuseStep 734807 = 1102211) B1102211
theorem B1881731 : Blo 487790 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B734873 : Blo 487790 734873 := bstep (se 2 (by rfl) ⟨275577, by rfl⟩ : syracuseStep 734873 = 551155) B551155
theorem B2242241 : Blo 487790 2242241 := bstep (se 2 (by rfl) ⟨840840, by rfl⟩ : syracuseStep 2242241 = 1681681) B1681681
theorem B931571 : Blo 487790 931571 := bstep (se 1 (by rfl) ⟨698678, by rfl⟩ : syracuseStep 931571 = 1397357) B1397357
theorem B734987 : Blo 487790 734987 := bstep (se 1 (by rfl) ⟨551240, by rfl⟩ : syracuseStep 734987 = 1102481) B1102481
theorem B734999 : Blo 487790 734999 := bstep (se 1 (by rfl) ⟨551249, by rfl⟩ : syracuseStep 734999 = 1102499) B1102499
theorem B735065 : Blo 487790 735065 := bstep (se 2 (by rfl) ⟨275649, by rfl⟩ : syracuseStep 735065 = 551299) B551299
theorem B735179 : Blo 487790 735179 := bstep (se 1 (by rfl) ⟨551384, by rfl⟩ : syracuseStep 735179 = 1102769) B1102769
theorem B735191 : Blo 487790 735191 := bstep (se 1 (by rfl) ⟨551393, by rfl⟩ : syracuseStep 735191 = 1102787) B1102787
theorem B931799 : Blo 487790 931799 := bstep (se 1 (by rfl) ⟨698849, by rfl⟩ : syracuseStep 931799 = 1397699) B1397699
theorem B735257 : Blo 487790 735257 := bstep (se 2 (by rfl) ⟨275721, by rfl⟩ : syracuseStep 735257 = 551443) B551443
theorem B735371 : Blo 487790 735371 := bstep (se 1 (by rfl) ⟨551528, by rfl⟩ : syracuseStep 735371 = 1103057) B1103057
theorem B735383 : Blo 487790 735383 := bstep (se 1 (by rfl) ⟨551537, by rfl⟩ : syracuseStep 735383 = 1103075) B1103075
theorem B1652939 : Blo 487790 1652939 := bstep (se 1 (by rfl) ⟨1239704, by rfl⟩ : syracuseStep 1652939 = 2479409) B2479409
theorem B735449 : Blo 487790 735449 := bstep (se 2 (by rfl) ⟨275793, by rfl⟩ : syracuseStep 735449 = 551587) B551587
theorem B932057 : Blo 487790 932057 := bstep (se 2 (by rfl) ⟨349521, by rfl⟩ : syracuseStep 932057 = 699043) B699043
theorem B735563 : Blo 487790 735563 := bstep (se 1 (by rfl) ⟨551672, by rfl⟩ : syracuseStep 735563 = 1103345) B1103345
theorem B735575 : Blo 487790 735575 := bstep (se 1 (by rfl) ⟨551681, by rfl⟩ : syracuseStep 735575 = 1103363) B1103363
theorem B735641 : Blo 487790 735641 := bstep (se 2 (by rfl) ⟨275865, by rfl⟩ : syracuseStep 735641 = 551731) B551731
theorem B1653209 : Blo 487790 1653209 := bstep (se 2 (by rfl) ⟨619953, by rfl⟩ : syracuseStep 1653209 = 1239907) B1239907
theorem B1391069 : Blo 487790 1391069 := bstep (se 3 (by rfl) ⟨260825, by rfl⟩ : syracuseStep 1391069 = 521651) B521651
theorem B3521029 : Blo 487790 3521029 := bstep (se 4 (by rfl) ⟨330096, by rfl⟩ : syracuseStep 3521029 = 660193) B660193
theorem B735755 : Blo 487790 735755 := bstep (se 1 (by rfl) ⟨551816, by rfl⟩ : syracuseStep 735755 = 1103633) B1103633
theorem B735767 : Blo 487790 735767 := bstep (se 1 (by rfl) ⟨551825, by rfl⟩ : syracuseStep 735767 = 1103651) B1103651
theorem B735833 : Blo 487790 735833 := bstep (se 2 (by rfl) ⟨275937, by rfl⟩ : syracuseStep 735833 = 551875) B551875
theorem B932467 : Blo 487790 932467 := bstep (se 1 (by rfl) ⟨699350, by rfl⟩ : syracuseStep 932467 = 1398701) B1398701
theorem B735947 : Blo 487790 735947 := bstep (se 1 (by rfl) ⟨551960, by rfl⟩ : syracuseStep 735947 = 1103921) B1103921
theorem B735959 : Blo 487790 735959 := bstep (se 1 (by rfl) ⟨551969, by rfl⟩ : syracuseStep 735959 = 1103939) B1103939
theorem B736025 : Blo 487790 736025 := bstep (se 2 (by rfl) ⟨276009, by rfl⟩ : syracuseStep 736025 = 552019) B552019
theorem B1391411 : Blo 487790 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B736139 : Blo 487790 736139 := bstep (se 1 (by rfl) ⟨552104, by rfl⟩ : syracuseStep 736139 = 1104209) B1104209
theorem B736151 : Blo 487790 736151 := bstep (se 1 (by rfl) ⟨552113, by rfl⟩ : syracuseStep 736151 = 1104227) B1104227
theorem B736217 : Blo 487790 736217 := bstep (se 2 (by rfl) ⟨276081, by rfl⟩ : syracuseStep 736217 = 552163) B552163
theorem B736331 : Blo 487790 736331 := bstep (se 1 (by rfl) ⟨552248, by rfl⟩ : syracuseStep 736331 = 1104497) B1104497
theorem B736343 : Blo 487790 736343 := bstep (se 1 (by rfl) ⟨552257, by rfl⟩ : syracuseStep 736343 = 1104515) B1104515
theorem B932953 : Blo 487790 932953 := bstep (se 2 (by rfl) ⟨349857, by rfl⟩ : syracuseStep 932953 = 699715) B699715
theorem B2473091 : Blo 487790 2473091 := bstep (se 1 (by rfl) ⟨1854818, by rfl⟩ : syracuseStep 2473091 = 3709637) B3709637
theorem B1653911 : Blo 487790 1653911 := bstep (se 1 (by rfl) ⟨1240433, by rfl⟩ : syracuseStep 1653911 = 2480867) B2480867
theorem B736409 : Blo 487790 736409 := bstep (se 2 (by rfl) ⟨276153, by rfl⟩ : syracuseStep 736409 = 552307) B552307
theorem B736523 : Blo 487790 736523 := bstep (se 1 (by rfl) ⟨552392, by rfl⟩ : syracuseStep 736523 = 1104785) B1104785
theorem B736535 : Blo 487790 736535 := bstep (se 1 (by rfl) ⟨552401, by rfl⟩ : syracuseStep 736535 = 1104803) B1104803
theorem B736601 : Blo 487790 736601 := bstep (se 2 (by rfl) ⟨276225, by rfl⟩ : syracuseStep 736601 = 552451) B552451
theorem B736715 : Blo 487790 736715 := bstep (se 1 (by rfl) ⟨552536, by rfl⟩ : syracuseStep 736715 = 1105073) B1105073
theorem B736727 : Blo 487790 736727 := bstep (se 1 (by rfl) ⟨552545, by rfl⟩ : syracuseStep 736727 = 1105091) B1105091
theorem B736793 : Blo 487790 736793 := bstep (se 2 (by rfl) ⟨276297, by rfl⟩ : syracuseStep 736793 = 552595) B552595
theorem B1490521 : Blo 487790 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B736907 : Blo 487790 736907 := bstep (se 1 (by rfl) ⟨552680, by rfl⟩ : syracuseStep 736907 = 1105361) B1105361
theorem B933515 : Blo 487790 933515 := bstep (se 1 (by rfl) ⟨700136, by rfl⟩ : syracuseStep 933515 = 1400273) B1400273
theorem B736919 : Blo 487790 736919 := bstep (se 1 (by rfl) ⟨552689, by rfl⟩ : syracuseStep 736919 = 1105379) B1105379
theorem B1654451 : Blo 487790 1654451 := bstep (se 1 (by rfl) ⟨1240838, by rfl⟩ : syracuseStep 1654451 = 2481677) B2481677
theorem B1326809 : Blo 487790 1326809 := bstep (se 2 (by rfl) ⟨497553, by rfl⟩ : syracuseStep 1326809 = 995107) B995107
theorem B736985 : Blo 487790 736985 := bstep (se 2 (by rfl) ⟨276369, by rfl⟩ : syracuseStep 736985 = 552739) B552739
theorem B737099 : Blo 487790 737099 := bstep (se 1 (by rfl) ⟨552824, by rfl⟩ : syracuseStep 737099 = 1105649) B1105649
theorem B737111 : Blo 487790 737111 := bstep (se 1 (by rfl) ⟨552833, by rfl⟩ : syracuseStep 737111 = 1105667) B1105667
theorem B3063703 : Blo 487790 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B737177 : Blo 487790 737177 := bstep (se 2 (by rfl) ⟨276441, by rfl⟩ : syracuseStep 737177 = 552883) B552883
theorem B1654721 : Blo 487790 1654721 := bstep (se 2 (by rfl) ⟨620520, by rfl⟩ : syracuseStep 1654721 = 1241041) B1241041
theorem B1097675 : Blo 487790 1097675 := bstep (se 1 (by rfl) ⟨823256, by rfl⟩ : syracuseStep 1097675 = 1646513) B1646513
theorem B1097729 : Blo 487790 1097729 := bstep (se 2 (by rfl) ⟨411648, by rfl⟩ : syracuseStep 1097729 = 823297) B823297
theorem B737291 : Blo 487790 737291 := bstep (se 1 (by rfl) ⟨552968, by rfl⟩ : syracuseStep 737291 = 1105937) B1105937
theorem B737303 : Blo 487790 737303 := bstep (se 1 (by rfl) ⟨552977, by rfl⟩ : syracuseStep 737303 = 1105955) B1105955
theorem B737369 : Blo 487790 737369 := bstep (se 2 (by rfl) ⟨276513, by rfl⟩ : syracuseStep 737369 = 553027) B553027
theorem B1982657 : Blo 487790 1982657 := bstep (se 2 (by rfl) ⟨743496, by rfl⟩ : syracuseStep 1982657 = 1486993) B1486993
theorem B737483 : Blo 487790 737483 := bstep (se 1 (by rfl) ⟨553112, by rfl⟩ : syracuseStep 737483 = 1106225) B1106225
theorem B737495 : Blo 487790 737495 := bstep (se 1 (by rfl) ⟨553121, by rfl⟩ : syracuseStep 737495 = 1106243) B1106243
theorem B1097945 : Blo 487790 1097945 := bstep (se 2 (by rfl) ⟨411729, by rfl⟩ : syracuseStep 1097945 = 823459) B823459
theorem B737561 : Blo 487790 737561 := bstep (se 2 (by rfl) ⟨276585, by rfl⟩ : syracuseStep 737561 = 553171) B553171
theorem B1098035 : Blo 487790 1098035 := bstep (se 1 (by rfl) ⟨823526, by rfl⟩ : syracuseStep 1098035 = 1647053) B1647053
theorem B6275393 : Blo 487790 6275393 := bstep (se 2 (by rfl) ⟨2353272, by rfl⟩ : syracuseStep 6275393 = 4706545) B4706545
theorem B1098071 : Blo 487790 1098071 := bstep (se 1 (by rfl) ⟨823553, by rfl⟩ : syracuseStep 1098071 = 1647107) B1647107
theorem B737675 : Blo 487790 737675 := bstep (se 1 (by rfl) ⟨553256, by rfl⟩ : syracuseStep 737675 = 1106513) B1106513
theorem B3129779 : Blo 487790 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B1655261 : Blo 487790 1655261 := bstep (se 3 (by rfl) ⟨310361, by rfl⟩ : syracuseStep 1655261 = 620723) B620723
theorem B1098251 : Blo 487790 1098251 := bstep (se 1 (by rfl) ⟨823688, by rfl⟩ : syracuseStep 1098251 = 1647377) B1647377
theorem B836119 : Blo 487790 836119 := bstep (se 1 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 836119 = 1254179) B1254179
theorem B1098305 : Blo 487790 1098305 := bstep (se 2 (by rfl) ⟨411864, by rfl⟩ : syracuseStep 1098305 = 823729) B823729
theorem B1098521 : Blo 487790 1098521 := bstep (se 2 (by rfl) ⟨411945, by rfl⟩ : syracuseStep 1098521 = 823891) B823891
theorem B1852253 : Blo 487790 1852253 := bstep (se 3 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 1852253 = 694595) B694595
theorem B1098611 : Blo 487790 1098611 := bstep (se 1 (by rfl) ⟨823958, by rfl⟩ : syracuseStep 1098611 = 1647917) B1647917
theorem B1098647 : Blo 487790 1098647 := bstep (se 1 (by rfl) ⟨823985, by rfl⟩ : syracuseStep 1098647 = 1647971) B1647971
theorem B1098827 : Blo 487790 1098827 := bstep (se 1 (by rfl) ⟨824120, by rfl⟩ : syracuseStep 1098827 = 1648241) B1648241
theorem B1393757 : Blo 487790 1393757 := bstep (se 3 (by rfl) ⟨261329, by rfl⟩ : syracuseStep 1393757 = 522659) B522659
theorem B1098881 : Blo 487790 1098881 := bstep (se 2 (by rfl) ⟨412080, by rfl⟩ : syracuseStep 1098881 = 824161) B824161
theorem B1328345 : Blo 487790 1328345 := bstep (se 2 (by rfl) ⟨498129, by rfl⟩ : syracuseStep 1328345 = 996259) B996259
theorem B1393985 : Blo 487790 1393985 := bstep (se 2 (by rfl) ⟨522744, by rfl⟩ : syracuseStep 1393985 = 1045489) B1045489
theorem B1099097 : Blo 487790 1099097 := bstep (se 2 (by rfl) ⟨412161, by rfl⟩ : syracuseStep 1099097 = 824323) B824323
theorem B1099187 : Blo 487790 1099187 := bstep (se 1 (by rfl) ⟨824390, by rfl⟩ : syracuseStep 1099187 = 1648781) B1648781
theorem B1099223 : Blo 487790 1099223 := bstep (se 1 (by rfl) ⟨824417, by rfl⟩ : syracuseStep 1099223 = 1648835) B1648835
theorem B1656395 : Blo 487790 1656395 := bstep (se 1 (by rfl) ⟨1242296, by rfl⟩ : syracuseStep 1656395 = 2484593) B2484593
theorem B1099403 : Blo 487790 1099403 := bstep (se 1 (by rfl) ⟨824552, by rfl⟩ : syracuseStep 1099403 = 1649105) B1649105
theorem B1394327 : Blo 487790 1394327 := bstep (se 1 (by rfl) ⟨1045745, by rfl⟩ : syracuseStep 1394327 = 2091491) B2091491
theorem B1099457 : Blo 487790 1099457 := bstep (se 2 (by rfl) ⟨412296, by rfl⟩ : syracuseStep 1099457 = 824593) B824593
theorem B1656665 : Blo 487790 1656665 := bstep (se 2 (by rfl) ⟨621249, by rfl⟩ : syracuseStep 1656665 = 1242499) B1242499
theorem B3131237 : Blo 487790 3131237 := bstep (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) B587107
theorem B1099673 : Blo 487790 1099673 := bstep (se 2 (by rfl) ⟨412377, by rfl⟩ : syracuseStep 1099673 = 824755) B824755
theorem B1099763 : Blo 487790 1099763 := bstep (se 1 (by rfl) ⟨824822, by rfl⟩ : syracuseStep 1099763 = 1649645) B1649645
theorem B1099799 : Blo 487790 1099799 := bstep (se 1 (by rfl) ⟨824849, by rfl⟩ : syracuseStep 1099799 = 1649699) B1649699
theorem B2508893 : Blo 487790 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B8472757 : Blo 487790 8472757 := bstep (se 5 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 8472757 = 794321) B794321
theorem B1099979 : Blo 487790 1099979 := bstep (se 1 (by rfl) ⟨824984, by rfl⟩ : syracuseStep 1099979 = 1649969) B1649969
theorem B1984733 : Blo 487790 1984733 := bstep (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) B744275
theorem B7948529 : Blo 487790 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B1100033 : Blo 487790 1100033 := bstep (se 2 (by rfl) ⟨412512, by rfl⟩ : syracuseStep 1100033 = 825025) B825025
theorem B1493441 : Blo 487790 1493441 := bstep (se 2 (by rfl) ⟨560040, by rfl⟩ : syracuseStep 1493441 = 1120081) B1120081
theorem B1100249 : Blo 487790 1100249 := bstep (se 2 (by rfl) ⟨412593, by rfl⟩ : syracuseStep 1100249 = 825187) B825187
theorem B1657367 : Blo 487790 1657367 := bstep (se 1 (by rfl) ⟨1243025, by rfl⟩ : syracuseStep 1657367 = 2486051) B2486051
theorem B1100339 : Blo 487790 1100339 := bstep (se 1 (by rfl) ⟨825254, by rfl⟩ : syracuseStep 1100339 = 1650509) B1650509
theorem B1100375 : Blo 487790 1100375 := bstep (se 1 (by rfl) ⟨825281, by rfl⟩ : syracuseStep 1100375 = 1650563) B1650563
theorem B2116289 : Blo 487790 2116289 := bstep (se 2 (by rfl) ⟨793608, by rfl⟩ : syracuseStep 2116289 = 1587217) B1587217
theorem B1854211 : Blo 487790 1854211 := bstep (se 1 (by rfl) ⟨1390658, by rfl⟩ : syracuseStep 1854211 = 2781317) B2781317
theorem B1100555 : Blo 487790 1100555 := bstep (se 1 (by rfl) ⟨825416, by rfl⟩ : syracuseStep 1100555 = 1650833) B1650833
theorem B2476817 : Blo 487790 2476817 := bstep (se 2 (by rfl) ⟨928806, by rfl⟩ : syracuseStep 2476817 = 1857613) B1857613
theorem B1100609 : Blo 487790 1100609 := bstep (se 2 (by rfl) ⟨412728, by rfl⟩ : syracuseStep 1100609 = 825457) B825457
theorem B838487 : Blo 487790 838487 := bstep (se 1 (by rfl) ⟨628865, by rfl⟩ : syracuseStep 838487 = 1257731) B1257731
theorem B7129957 : Blo 487790 7129957 := bstep (se 4 (by rfl) ⟨668433, by rfl⟩ : syracuseStep 7129957 = 1336867) B1336867
theorem B2476979 : Blo 487790 2476979 := bstep (se 1 (by rfl) ⟨1857734, by rfl⟩ : syracuseStep 2476979 = 3715469) B3715469
theorem B2083801 : Blo 487790 2083801 := bstep (se 2 (by rfl) ⟨781425, by rfl⟩ : syracuseStep 2083801 = 1562851) B1562851
theorem B4180997 : Blo 487790 4180997 := bstep (se 4 (by rfl) ⟨391968, by rfl⟩ : syracuseStep 4180997 = 783937) B783937
theorem B1100825 : Blo 487790 1100825 := bstep (se 2 (by rfl) ⟨412809, by rfl⟩ : syracuseStep 1100825 = 825619) B825619
theorem B1854515 : Blo 487790 1854515 := bstep (se 1 (by rfl) ⟨1390886, by rfl⟩ : syracuseStep 1854515 = 2781773) B2781773
theorem B1657907 : Blo 487790 1657907 := bstep (se 1 (by rfl) ⟨1243430, by rfl⟩ : syracuseStep 1657907 = 2486861) B2486861
theorem B1100915 : Blo 487790 1100915 := bstep (se 1 (by rfl) ⟨825686, by rfl⟩ : syracuseStep 1100915 = 1651373) B1651373
theorem B2509955 : Blo 487790 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B1100951 : Blo 487790 1100951 := bstep (se 1 (by rfl) ⟨825713, by rfl⟩ : syracuseStep 1100951 = 1651427) B1651427
theorem B1658177 : Blo 487790 1658177 := bstep (se 2 (by rfl) ⟨621816, by rfl⟩ : syracuseStep 1658177 = 1243633) B1243633
theorem B1101131 : Blo 487790 1101131 := bstep (se 1 (by rfl) ⟨825848, by rfl⟩ : syracuseStep 1101131 = 1651697) B1651697
theorem B1101185 : Blo 487790 1101185 := bstep (se 2 (by rfl) ⟨412944, by rfl⟩ : syracuseStep 1101185 = 825889) B825889
theorem B2084417 : Blo 487790 2084417 := bstep (se 2 (by rfl) ⟨781656, by rfl⟩ : syracuseStep 2084417 = 1563313) B1563313
theorem B1101401 : Blo 487790 1101401 := bstep (se 2 (by rfl) ⟨413025, by rfl⟩ : syracuseStep 1101401 = 826051) B826051
theorem B1101491 : Blo 487790 1101491 := bstep (se 1 (by rfl) ⟨826118, by rfl⟩ : syracuseStep 1101491 = 1652237) B1652237
theorem B1855169 : Blo 487790 1855169 := bstep (se 2 (by rfl) ⟨695688, by rfl⟩ : syracuseStep 1855169 = 1391377) B1391377
theorem B1101527 : Blo 487790 1101527 := bstep (se 1 (by rfl) ⟨826145, by rfl⟩ : syracuseStep 1101527 = 1652291) B1652291
theorem B1658717 : Blo 487790 1658717 := bstep (se 3 (by rfl) ⟨311009, by rfl⟩ : syracuseStep 1658717 = 622019) B622019
theorem B1101707 : Blo 487790 1101707 := bstep (se 1 (by rfl) ⟨826280, by rfl⟩ : syracuseStep 1101707 = 1652561) B1652561
theorem B511915 : Blo 487790 511915 := bstep (se 1 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 511915 = 767873) B767873
theorem B1101761 : Blo 487790 1101761 := bstep (se 2 (by rfl) ⟨413160, by rfl⟩ : syracuseStep 1101761 = 826321) B826321
theorem B1396673 : Blo 487790 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B1134643 : Blo 487790 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B1101977 : Blo 487790 1101977 := bstep (se 2 (by rfl) ⟨413241, by rfl⟩ : syracuseStep 1101977 = 826483) B826483
theorem B1003735 : Blo 487790 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B1102067 : Blo 487790 1102067 := bstep (se 1 (by rfl) ⟨826550, by rfl⟩ : syracuseStep 1102067 = 1653101) B1653101
theorem B1102103 : Blo 487790 1102103 := bstep (se 1 (by rfl) ⟨826577, by rfl⟩ : syracuseStep 1102103 = 1653155) B1653155
theorem B1102283 : Blo 487790 1102283 := bstep (se 1 (by rfl) ⟨826712, by rfl⟩ : syracuseStep 1102283 = 1653425) B1653425
theorem B1397209 : Blo 487790 1397209 := bstep (se 2 (by rfl) ⟨523953, by rfl⟩ : syracuseStep 1397209 = 1047907) B1047907
theorem B1102337 : Blo 487790 1102337 := bstep (se 2 (by rfl) ⟨413376, by rfl⟩ : syracuseStep 1102337 = 826753) B826753
theorem B2347699 : Blo 487790 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B1102553 : Blo 487790 1102553 := bstep (se 2 (by rfl) ⟨413457, by rfl⟩ : syracuseStep 1102553 = 826915) B826915
theorem B1102643 : Blo 487790 1102643 := bstep (se 1 (by rfl) ⟨826982, by rfl⟩ : syracuseStep 1102643 = 1653965) B1653965
theorem B2478923 : Blo 487790 2478923 := bstep (se 1 (by rfl) ⟨1859192, by rfl⟩ : syracuseStep 2478923 = 3718385) B3718385
theorem B1102679 : Blo 487790 1102679 := bstep (se 1 (by rfl) ⟨827009, by rfl⟩ : syracuseStep 1102679 = 1654019) B1654019
theorem B1856429 : Blo 487790 1856429 := bstep (se 3 (by rfl) ⟨348080, by rfl⟩ : syracuseStep 1856429 = 696161) B696161
theorem B1856459 : Blo 487790 1856459 := bstep (se 1 (by rfl) ⟨1392344, by rfl⟩ : syracuseStep 1856459 = 2784689) B2784689
theorem B1135603 : Blo 487790 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B1102859 : Blo 487790 1102859 := bstep (se 1 (by rfl) ⟨827144, by rfl⟩ : syracuseStep 1102859 = 1654289) B1654289
theorem B1102913 : Blo 487790 1102913 := bstep (se 2 (by rfl) ⟨413592, by rfl⟩ : syracuseStep 1102913 = 827185) B827185
theorem B1987715 : Blo 487790 1987715 := bstep (se 1 (by rfl) ⟨1490786, by rfl⟩ : syracuseStep 1987715 = 2981573) B2981573
theorem B1103129 : Blo 487790 1103129 := bstep (se 2 (by rfl) ⟨413673, by rfl⟩ : syracuseStep 1103129 = 827347) B827347
theorem B1758553 : Blo 487790 1758553 := bstep (se 2 (by rfl) ⟨659457, by rfl⟩ : syracuseStep 1758553 = 1318915) B1318915
theorem B1103219 : Blo 487790 1103219 := bstep (se 1 (by rfl) ⟨827414, by rfl⟩ : syracuseStep 1103219 = 1654829) B1654829
theorem B1103255 : Blo 487790 1103255 := bstep (se 1 (by rfl) ⟨827441, by rfl⟩ : syracuseStep 1103255 = 1654883) B1654883
theorem B26891747 : Blo 487790 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B1103435 : Blo 487790 1103435 := bstep (se 1 (by rfl) ⟨827576, by rfl⟩ : syracuseStep 1103435 = 1655153) B1655153
theorem B2872907 : Blo 487790 2872907 := bstep (se 1 (by rfl) ⟨2154680, by rfl⟩ : syracuseStep 2872907 = 4309361) B4309361
theorem B1857113 : Blo 487790 1857113 := bstep (se 2 (by rfl) ⟨696417, by rfl⟩ : syracuseStep 1857113 = 1392835) B1392835
theorem B1594973 : Blo 487790 1594973 := bstep (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) B598115
theorem B2971237 : Blo 487790 2971237 := bstep (se 4 (by rfl) ⟨278553, by rfl⟩ : syracuseStep 2971237 = 557107) B557107
theorem B1103489 : Blo 487790 1103489 := bstep (se 2 (by rfl) ⟨413808, by rfl⟩ : syracuseStep 1103489 = 827617) B827617
theorem B1005259 : Blo 487790 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B1103705 : Blo 487790 1103705 := bstep (se 2 (by rfl) ⟨413889, by rfl⟩ : syracuseStep 1103705 = 827779) B827779
theorem B1857431 : Blo 487790 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B1103795 : Blo 487790 1103795 := bstep (se 1 (by rfl) ⟨827846, by rfl⟩ : syracuseStep 1103795 = 1655693) B1655693
theorem B1103831 : Blo 487790 1103831 := bstep (se 1 (by rfl) ⟨827873, by rfl⟩ : syracuseStep 1103831 = 1655747) B1655747
theorem B2086877 : Blo 487790 2086877 := bstep (se 3 (by rfl) ⟨391289, by rfl⟩ : syracuseStep 2086877 = 782579) B782579
theorem B1104011 : Blo 487790 1104011 := bstep (se 1 (by rfl) ⟨828008, by rfl⟩ : syracuseStep 1104011 = 1656017) B1656017
theorem B1104065 : Blo 487790 1104065 := bstep (se 2 (by rfl) ⟨414024, by rfl⟩ : syracuseStep 1104065 = 828049) B828049
theorem B1399133 : Blo 487790 1399133 := bstep (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) B524675
theorem B1235351 : Blo 487790 1235351 := bstep (se 1 (by rfl) ⟨926513, by rfl⟩ : syracuseStep 1235351 = 1853027) B1853027
theorem B1104281 : Blo 487790 1104281 := bstep (se 2 (by rfl) ⟨414105, by rfl⟩ : syracuseStep 1104281 = 828211) B828211
theorem B1563083 : Blo 487790 1563083 := bstep (se 1 (by rfl) ⟨1172312, by rfl⟩ : syracuseStep 1563083 = 2344625) B2344625
theorem B1104371 : Blo 487790 1104371 := bstep (se 1 (by rfl) ⟨828278, by rfl⟩ : syracuseStep 1104371 = 1656557) B1656557
theorem B1104407 : Blo 487790 1104407 := bstep (se 1 (by rfl) ⟨828305, by rfl⟩ : syracuseStep 1104407 = 1656611) B1656611
theorem B4184621 : Blo 487790 4184621 := bstep (se 3 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 4184621 = 1569233) B1569233
theorem B1858099 : Blo 487790 1858099 := bstep (se 1 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 1858099 = 2787149) B2787149
theorem B2480705 : Blo 487790 2480705 := bstep (se 2 (by rfl) ⟨930264, by rfl⟩ : syracuseStep 2480705 = 1860529) B1860529
theorem B1104587 : Blo 487790 1104587 := bstep (se 1 (by rfl) ⟨828440, by rfl⟩ : syracuseStep 1104587 = 1656881) B1656881
theorem B1104641 : Blo 487790 1104641 := bstep (se 2 (by rfl) ⟨414240, by rfl⟩ : syracuseStep 1104641 = 828481) B828481
theorem B1104857 : Blo 487790 1104857 := bstep (se 2 (by rfl) ⟨414321, by rfl⟩ : syracuseStep 1104857 = 828643) B828643
theorem B1563671 : Blo 487790 1563671 := bstep (se 1 (by rfl) ⟨1172753, by rfl⟩ : syracuseStep 1563671 = 2345507) B2345507
theorem B10017827 : Blo 487790 10017827 := bstep (se 1 (by rfl) ⟨7513370, by rfl⟩ : syracuseStep 10017827 = 15026741) B15026741
theorem B1236019 : Blo 487790 1236019 := bstep (se 1 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 1236019 = 1854029) B1854029
theorem B1104947 : Blo 487790 1104947 := bstep (se 1 (by rfl) ⟨828710, by rfl⟩ : syracuseStep 1104947 = 1657421) B1657421
theorem B1104983 : Blo 487790 1104983 := bstep (se 1 (by rfl) ⟨828737, by rfl⟩ : syracuseStep 1104983 = 1657475) B1657475
theorem B1236161 : Blo 487790 1236161 := bstep (se 2 (by rfl) ⟨463560, by rfl⟩ : syracuseStep 1236161 = 927121) B927121
theorem B1105163 : Blo 487790 1105163 := bstep (se 1 (by rfl) ⟨828872, by rfl⟩ : syracuseStep 1105163 = 1657745) B1657745
theorem B1105217 : Blo 487790 1105217 := bstep (se 2 (by rfl) ⟨414456, by rfl⟩ : syracuseStep 1105217 = 828913) B828913
theorem B1105433 : Blo 487790 1105433 := bstep (se 2 (by rfl) ⟨414537, by rfl⟩ : syracuseStep 1105433 = 829075) B829075
theorem B1564211 : Blo 487790 1564211 := bstep (se 1 (by rfl) ⟨1173158, by rfl⟩ : syracuseStep 1564211 = 2346317) B2346317
theorem B1105523 : Blo 487790 1105523 := bstep (se 1 (by rfl) ⟨829142, by rfl⟩ : syracuseStep 1105523 = 1658285) B1658285
theorem B1105559 : Blo 487790 1105559 := bstep (se 1 (by rfl) ⟨829169, by rfl⟩ : syracuseStep 1105559 = 1658339) B1658339
theorem B1859345 : Blo 487790 1859345 := bstep (se 2 (by rfl) ⟨697254, by rfl⟩ : syracuseStep 1859345 = 1394509) B1394509
theorem B1105739 : Blo 487790 1105739 := bstep (se 1 (by rfl) ⟨829304, by rfl⟩ : syracuseStep 1105739 = 1658609) B1658609
theorem B1105793 : Blo 487790 1105793 := bstep (se 2 (by rfl) ⟨414672, by rfl⟩ : syracuseStep 1105793 = 829345) B829345
theorem B548779 : Blo 487790 548779 := bstep (se 1 (by rfl) ⟨411584, by rfl⟩ : syracuseStep 548779 = 823169) B823169
theorem B548887 : Blo 487790 548887 := bstep (se 1 (by rfl) ⟨411665, by rfl⟩ : syracuseStep 548887 = 823331) B823331
theorem B1106009 : Blo 487790 1106009 := bstep (se 2 (by rfl) ⟨414753, by rfl⟩ : syracuseStep 1106009 = 829507) B829507
theorem B1106099 : Blo 487790 1106099 := bstep (se 1 (by rfl) ⟨829574, by rfl⟩ : syracuseStep 1106099 = 1659149) B1659149
theorem B549067 : Blo 487790 549067 := bstep (se 1 (by rfl) ⟨411800, by rfl⟩ : syracuseStep 549067 = 823601) B823601
theorem B1106135 : Blo 487790 1106135 := bstep (se 1 (by rfl) ⟨829601, by rfl⟩ : syracuseStep 1106135 = 1659203) B1659203
theorem B1761497 : Blo 487790 1761497 := bstep (se 2 (by rfl) ⟨660561, by rfl⟩ : syracuseStep 1761497 = 1321123) B1321123
theorem B549175 : Blo 487790 549175 := bstep (se 1 (by rfl) ⟨411881, by rfl⟩ : syracuseStep 549175 = 823763) B823763
theorem B1106315 : Blo 487790 1106315 := bstep (se 1 (by rfl) ⟨829736, by rfl⟩ : syracuseStep 1106315 = 1659473) B1659473
theorem B1237427 : Blo 487790 1237427 := bstep (se 1 (by rfl) ⟨928070, by rfl⟩ : syracuseStep 1237427 = 1856141) B1856141
theorem B1106369 : Blo 487790 1106369 := bstep (se 2 (by rfl) ⟨414888, by rfl⟩ : syracuseStep 1106369 = 829777) B829777
theorem B1860043 : Blo 487790 1860043 := bstep (se 1 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 1860043 = 2790065) B2790065
theorem B2482649 : Blo 487790 2482649 := bstep (se 2 (by rfl) ⟨930993, by rfl⟩ : syracuseStep 2482649 = 1861987) B1861987
theorem B549355 : Blo 487790 549355 := bstep (se 1 (by rfl) ⟨412016, by rfl⟩ : syracuseStep 549355 = 824033) B824033
theorem B2089475 : Blo 487790 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B549463 : Blo 487790 549463 := bstep (se 1 (by rfl) ⟨412097, by rfl⟩ : syracuseStep 549463 = 824195) B824195
theorem B1991347 : Blo 487790 1991347 := bstep (se 1 (by rfl) ⟨1493510, by rfl⟩ : syracuseStep 1991347 = 2987021) B2987021
theorem B1860317 : Blo 487790 1860317 := bstep (se 3 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 1860317 = 697619) B697619
theorem B549643 : Blo 487790 549643 := bstep (se 1 (by rfl) ⟨412232, by rfl⟩ : syracuseStep 549643 = 824465) B824465
theorem B549751 : Blo 487790 549751 := bstep (se 1 (by rfl) ⟨412313, by rfl⟩ : syracuseStep 549751 = 824627) B824627
theorem B4187011 : Blo 487790 4187011 := bstep (se 1 (by rfl) ⟨3140258, by rfl⟩ : syracuseStep 4187011 = 6280517) B6280517
theorem B1237963 : Blo 487790 1237963 := bstep (se 1 (by rfl) ⟨928472, by rfl⟩ : syracuseStep 1237963 = 1856945) B1856945
theorem B549931 : Blo 487790 549931 := bstep (se 1 (by rfl) ⟨412448, by rfl⟩ : syracuseStep 549931 = 824897) B824897
theorem B1238105 : Blo 487790 1238105 := bstep (se 2 (by rfl) ⟨464289, by rfl⟩ : syracuseStep 1238105 = 928579) B928579
theorem B550039 : Blo 487790 550039 := bstep (se 1 (by rfl) ⟨412529, by rfl⟩ : syracuseStep 550039 = 825059) B825059
theorem B550219 : Blo 487790 550219 := bstep (se 1 (by rfl) ⟨412664, by rfl⟩ : syracuseStep 550219 = 825329) B825329
theorem B1762705 : Blo 487790 1762705 := bstep (se 2 (by rfl) ⟨661014, by rfl⟩ : syracuseStep 1762705 = 1322029) B1322029
theorem B1861015 : Blo 487790 1861015 := bstep (se 1 (by rfl) ⟨1395761, by rfl⟩ : syracuseStep 1861015 = 2791523) B2791523
theorem B550327 : Blo 487790 550327 := bstep (se 1 (by rfl) ⟨412745, by rfl⟩ : syracuseStep 550327 = 825491) B825491
theorem B6350411 : Blo 487790 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B550507 : Blo 487790 550507 := bstep (se 1 (by rfl) ⟨412880, by rfl⟩ : syracuseStep 550507 = 825761) B825761
theorem B550615 : Blo 487790 550615 := bstep (se 1 (by rfl) ⟨412961, by rfl⟩ : syracuseStep 550615 = 825923) B825923
theorem B4187969 : Blo 487790 4187969 := bstep (se 2 (by rfl) ⟨1570488, by rfl⟩ : syracuseStep 4187969 = 3140977) B3140977
theorem B550795 : Blo 487790 550795 := bstep (se 1 (by rfl) ⟨413096, by rfl⟩ : syracuseStep 550795 = 826193) B826193
theorem B1238935 : Blo 487790 1238935 := bstep (se 1 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 1238935 = 1858403) B1858403
theorem B550903 : Blo 487790 550903 := bstep (se 1 (by rfl) ⟨413177, by rfl⟩ : syracuseStep 550903 = 826355) B826355
theorem B2484269 : Blo 487790 2484269 := bstep (se 3 (by rfl) ⟨465800, by rfl⟩ : syracuseStep 2484269 = 931601) B931601
theorem B551083 : Blo 487790 551083 := bstep (se 1 (by rfl) ⟨413312, by rfl⟩ : syracuseStep 551083 = 826625) B826625
theorem B1861805 : Blo 487790 1861805 := bstep (se 3 (by rfl) ⟨349088, by rfl⟩ : syracuseStep 1861805 = 698177) B698177
theorem B551191 : Blo 487790 551191 := bstep (se 1 (by rfl) ⟨413393, by rfl⟩ : syracuseStep 551191 = 826787) B826787
theorem B1239371 : Blo 487790 1239371 := bstep (se 1 (by rfl) ⟨929528, by rfl⟩ : syracuseStep 1239371 = 1859057) B1859057
theorem B551371 : Blo 487790 551371 := bstep (se 1 (by rfl) ⟨413528, by rfl⟩ : syracuseStep 551371 = 827057) B827057
theorem B846347 : Blo 487790 846347 := bstep (se 1 (by rfl) ⟨634760, by rfl⟩ : syracuseStep 846347 = 1269521) B1269521
theorem B551479 : Blo 487790 551479 := bstep (se 1 (by rfl) ⟨413609, by rfl⟩ : syracuseStep 551479 = 827219) B827219
theorem B1010263 : Blo 487790 1010263 := bstep (se 1 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 1010263 = 1515395) B1515395
theorem B2124467 : Blo 487790 2124467 := bstep (se 1 (by rfl) ⟨1593350, by rfl⟩ : syracuseStep 2124467 = 3186701) B3186701
theorem B1239745 : Blo 487790 1239745 := bstep (se 2 (by rfl) ⟨464904, by rfl⟩ : syracuseStep 1239745 = 929809) B929809
theorem B551659 : Blo 487790 551659 := bstep (se 1 (by rfl) ⟨413744, by rfl⟩ : syracuseStep 551659 = 827489) B827489
theorem B682777 : Blo 487790 682777 := bstep (se 2 (by rfl) ⟨256041, by rfl⟩ : syracuseStep 682777 = 512083) B512083
theorem B2091851 : Blo 487790 2091851 := bstep (se 1 (by rfl) ⟨1568888, by rfl⟩ : syracuseStep 2091851 = 3137777) B3137777
theorem B551767 : Blo 487790 551767 := bstep (se 1 (by rfl) ⟨413825, by rfl⟩ : syracuseStep 551767 = 827651) B827651
theorem B1272793 : Blo 487790 1272793 := bstep (se 2 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 1272793 = 954595) B954595
theorem B617483 : Blo 487790 617483 := bstep (se 1 (by rfl) ⟨463112, by rfl⟩ : syracuseStep 617483 = 926225) B926225
theorem B551947 : Blo 487790 551947 := bstep (se 1 (by rfl) ⟨413960, by rfl⟩ : syracuseStep 551947 = 827921) B827921
theorem B552055 : Blo 487790 552055 := bstep (se 1 (by rfl) ⟨414041, by rfl⟩ : syracuseStep 552055 = 828083) B828083
theorem B1043609 : Blo 487790 1043609 := bstep (se 2 (by rfl) ⟨391353, by rfl⟩ : syracuseStep 1043609 = 782707) B782707
theorem B1633459 : Blo 487790 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B1240343 : Blo 487790 1240343 := bstep (se 1 (by rfl) ⟨930257, by rfl⟩ : syracuseStep 1240343 = 1860515) B1860515
theorem B552235 : Blo 487790 552235 := bstep (se 1 (by rfl) ⟨414176, by rfl⟩ : syracuseStep 552235 = 828353) B828353
theorem B2780567 : Blo 487790 2780567 := bstep (se 1 (by rfl) ⟨2085425, by rfl⟩ : syracuseStep 2780567 = 4170851) B4170851
theorem B552343 : Blo 487790 552343 := bstep (se 1 (by rfl) ⟨414257, by rfl⟩ : syracuseStep 552343 = 828515) B828515
theorem B781849 : Blo 487790 781849 := bstep (se 2 (by rfl) ⟨293193, by rfl⟩ : syracuseStep 781849 = 586387) B586387
theorem B1044019 : Blo 487790 1044019 := bstep (se 1 (by rfl) ⟨783014, by rfl⟩ : syracuseStep 1044019 = 1566029) B1566029
theorem B1863233 : Blo 487790 1863233 := bstep (se 2 (by rfl) ⟨698712, by rfl⟩ : syracuseStep 1863233 = 1397425) B1397425
theorem B552523 : Blo 487790 552523 := bstep (se 1 (by rfl) ⟨414392, by rfl⟩ : syracuseStep 552523 = 828785) B828785
theorem B781913 : Blo 487790 781913 := bstep (se 2 (by rfl) ⟨293217, by rfl⟩ : syracuseStep 781913 = 586435) B586435
theorem B552631 : Blo 487790 552631 := bstep (se 1 (by rfl) ⟨414473, by rfl⟩ : syracuseStep 552631 = 828947) B828947
theorem B618187 : Blo 487790 618187 := bstep (se 1 (by rfl) ⟨463640, by rfl⟩ : syracuseStep 618187 = 927281) B927281
theorem B782041 : Blo 487790 782041 := bstep (se 2 (by rfl) ⟨293265, by rfl⟩ : syracuseStep 782041 = 586531) B586531
theorem B2092823 : Blo 487790 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B3534637 : Blo 487790 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B552811 : Blo 487790 552811 := bstep (se 1 (by rfl) ⟨414608, by rfl⟩ : syracuseStep 552811 = 829217) B829217
theorem B1044353 : Blo 487790 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B1863575 : Blo 487790 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B618455 : Blo 487790 618455 := bstep (se 1 (by rfl) ⟨463841, by rfl⟩ : syracuseStep 618455 = 927683) B927683
theorem B552919 : Blo 487790 552919 := bstep (se 1 (by rfl) ⟨414689, by rfl⟩ : syracuseStep 552919 = 829379) B829379
theorem B1241153 : Blo 487790 1241153 := bstep (se 2 (by rfl) ⟨465432, by rfl⟩ : syracuseStep 1241153 = 930865) B930865
theorem B2355331 : Blo 487790 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B553099 : Blo 487790 553099 := bstep (se 1 (by rfl) ⟨414824, by rfl⟩ : syracuseStep 553099 = 829649) B829649
theorem B6025367 : Blo 487790 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B553207 : Blo 487790 553207 := bstep (se 1 (by rfl) ⟨414905, by rfl⟩ : syracuseStep 553207 = 829811) B829811
theorem B2289971 : Blo 487790 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B487799 : Blo 487790 487799 := bstep (se 1 (by rfl) ⟨365849, by rfl⟩ : syracuseStep 487799 = 731699) B731699
theorem B487819 : Blo 487790 487819 := bstep (se 1 (by rfl) ⟨365864, by rfl⟩ : syracuseStep 487819 = 731729) B731729
theorem B487831 : Blo 487790 487831 := bstep (se 1 (by rfl) ⟨365873, by rfl⟩ : syracuseStep 487831 = 731747) B731747
theorem B487851 : Blo 487790 487851 := bstep (se 1 (by rfl) ⟨365888, by rfl⟩ : syracuseStep 487851 = 731777) B731777
theorem B487863 : Blo 487790 487863 := bstep (se 1 (by rfl) ⟨365897, by rfl⟩ : syracuseStep 487863 = 731795) B731795
theorem B487883 : Blo 487790 487883 := bstep (se 1 (by rfl) ⟨365912, by rfl⟩ : syracuseStep 487883 = 731825) B731825
theorem B487895 : Blo 487790 487895 := bstep (se 1 (by rfl) ⟨365921, by rfl⟩ : syracuseStep 487895 = 731843) B731843
theorem B487915 : Blo 487790 487915 := bstep (se 1 (by rfl) ⟨365936, by rfl⟩ : syracuseStep 487915 = 731873) B731873
theorem B487927 : Blo 487790 487927 := bstep (se 1 (by rfl) ⟨365945, by rfl⟩ : syracuseStep 487927 = 731891) B731891
theorem B487947 : Blo 487790 487947 := bstep (se 1 (by rfl) ⟨365960, by rfl⟩ : syracuseStep 487947 = 731921) B731921
theorem B487959 : Blo 487790 487959 := bstep (se 1 (by rfl) ⟨365969, by rfl⟩ : syracuseStep 487959 = 731939) B731939
theorem B487979 : Blo 487790 487979 := bstep (se 1 (by rfl) ⟨365984, by rfl⟩ : syracuseStep 487979 = 731969) B731969
theorem B487991 : Blo 487790 487991 := bstep (se 1 (by rfl) ⟨365993, by rfl⟩ : syracuseStep 487991 = 731987) B731987
theorem B488011 : Blo 487790 488011 := bstep (se 1 (by rfl) ⟨366008, by rfl⟩ : syracuseStep 488011 = 732017) B732017
theorem B488023 : Blo 487790 488023 := bstep (se 1 (by rfl) ⟨366017, by rfl⟩ : syracuseStep 488023 = 732035) B732035
theorem B1045079 : Blo 487790 1045079 := bstep (se 1 (by rfl) ⟨783809, by rfl⟩ : syracuseStep 1045079 = 1567619) B1567619
theorem B1241689 : Blo 487790 1241689 := bstep (se 2 (by rfl) ⟨465633, by rfl⟩ : syracuseStep 1241689 = 931267) B931267
theorem B488043 : Blo 487790 488043 := bstep (se 1 (by rfl) ⟨366032, by rfl⟩ : syracuseStep 488043 = 732065) B732065
theorem B488055 : Blo 487790 488055 := bstep (se 1 (by rfl) ⟨366041, by rfl⟩ : syracuseStep 488055 = 732083) B732083
theorem B488075 : Blo 487790 488075 := bstep (se 1 (by rfl) ⟨366056, by rfl⟩ : syracuseStep 488075 = 732113) B732113
theorem B488087 : Blo 487790 488087 := bstep (se 1 (by rfl) ⟨366065, by rfl⟩ : syracuseStep 488087 = 732131) B732131
theorem B619159 : Blo 487790 619159 := bstep (se 1 (by rfl) ⟨464369, by rfl⟩ : syracuseStep 619159 = 928739) B928739
theorem B488107 : Blo 487790 488107 := bstep (se 1 (by rfl) ⟨366080, by rfl⟩ : syracuseStep 488107 = 732161) B732161
theorem B488119 : Blo 487790 488119 := bstep (se 1 (by rfl) ⟨366089, by rfl⟩ : syracuseStep 488119 = 732179) B732179
theorem B488139 : Blo 487790 488139 := bstep (se 1 (by rfl) ⟨366104, by rfl⟩ : syracuseStep 488139 = 732209) B732209
theorem B488151 : Blo 487790 488151 := bstep (se 1 (by rfl) ⟨366113, by rfl⟩ : syracuseStep 488151 = 732227) B732227
theorem B488171 : Blo 487790 488171 := bstep (se 1 (by rfl) ⟨366128, by rfl⟩ : syracuseStep 488171 = 732257) B732257
theorem B488183 : Blo 487790 488183 := bstep (se 1 (by rfl) ⟨366137, by rfl⟩ : syracuseStep 488183 = 732275) B732275
theorem B488203 : Blo 487790 488203 := bstep (se 1 (by rfl) ⟨366152, by rfl⟩ : syracuseStep 488203 = 732305) B732305
theorem B488215 : Blo 487790 488215 := bstep (se 1 (by rfl) ⟨366161, by rfl⟩ : syracuseStep 488215 = 732323) B732323
theorem B1078039 : Blo 487790 1078039 := bstep (se 1 (by rfl) ⟨808529, by rfl⟩ : syracuseStep 1078039 = 1617059) B1617059
theorem B488235 : Blo 487790 488235 := bstep (se 1 (by rfl) ⟨366176, by rfl⟩ : syracuseStep 488235 = 732353) B732353
theorem B5010221 : Blo 487790 5010221 := bstep (se 3 (by rfl) ⟨939416, by rfl⟩ : syracuseStep 5010221 = 1878833) B1878833
theorem B4715309 : Blo 487790 4715309 := bstep (se 3 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 4715309 = 1768241) B1768241
theorem B488247 : Blo 487790 488247 := bstep (se 1 (by rfl) ⟨366185, by rfl⟩ : syracuseStep 488247 = 732371) B732371
theorem B488267 : Blo 487790 488267 := bstep (se 1 (by rfl) ⟨366200, by rfl⟩ : syracuseStep 488267 = 732401) B732401
theorem B488279 : Blo 487790 488279 := bstep (se 1 (by rfl) ⟨366209, by rfl⟩ : syracuseStep 488279 = 732419) B732419
theorem B488299 : Blo 487790 488299 := bstep (se 1 (by rfl) ⟨366224, by rfl⟩ : syracuseStep 488299 = 732449) B732449
theorem B488311 : Blo 487790 488311 := bstep (se 1 (by rfl) ⟨366233, by rfl⟩ : syracuseStep 488311 = 732467) B732467
theorem B3339139 : Blo 487790 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B488331 : Blo 487790 488331 := bstep (se 1 (by rfl) ⟨366248, by rfl⟩ : syracuseStep 488331 = 732497) B732497
theorem B488343 : Blo 487790 488343 := bstep (se 1 (by rfl) ⟨366257, by rfl⟩ : syracuseStep 488343 = 732515) B732515
theorem B488363 : Blo 487790 488363 := bstep (se 1 (by rfl) ⟨366272, by rfl⟩ : syracuseStep 488363 = 732545) B732545
theorem B5600177 : Blo 487790 5600177 := bstep (se 2 (by rfl) ⟨2100066, by rfl⟩ : syracuseStep 5600177 = 4200133) B4200133
theorem B488375 : Blo 487790 488375 := bstep (se 1 (by rfl) ⟨366281, by rfl⟩ : syracuseStep 488375 = 732563) B732563
theorem B488395 : Blo 487790 488395 := bstep (se 1 (by rfl) ⟨366296, by rfl⟩ : syracuseStep 488395 = 732593) B732593
theorem B488407 : Blo 487790 488407 := bstep (se 1 (by rfl) ⟨366305, by rfl⟩ : syracuseStep 488407 = 732611) B732611
theorem B488427 : Blo 487790 488427 := bstep (se 1 (by rfl) ⟨366320, by rfl⟩ : syracuseStep 488427 = 732641) B732641
theorem B488439 : Blo 487790 488439 := bstep (se 1 (by rfl) ⟨366329, by rfl⟩ : syracuseStep 488439 = 732659) B732659
theorem B488459 : Blo 487790 488459 := bstep (se 1 (by rfl) ⟨366344, by rfl⟩ : syracuseStep 488459 = 732689) B732689
theorem B1864721 : Blo 487790 1864721 := bstep (se 2 (by rfl) ⟨699270, by rfl⟩ : syracuseStep 1864721 = 1398541) B1398541
theorem B488471 : Blo 487790 488471 := bstep (se 1 (by rfl) ⟨366353, by rfl⟩ : syracuseStep 488471 = 732707) B732707
theorem B1176599 : Blo 487790 1176599 := bstep (se 1 (by rfl) ⟨882449, by rfl⟩ : syracuseStep 1176599 = 1764899) B1764899
theorem B488491 : Blo 487790 488491 := bstep (se 1 (by rfl) ⟨366368, by rfl⟩ : syracuseStep 488491 = 732737) B732737
theorem B488503 : Blo 487790 488503 := bstep (se 1 (by rfl) ⟨366377, by rfl⟩ : syracuseStep 488503 = 732755) B732755
theorem B488523 : Blo 487790 488523 := bstep (se 1 (by rfl) ⟨366392, by rfl⟩ : syracuseStep 488523 = 732785) B732785
theorem B488535 : Blo 487790 488535 := bstep (se 1 (by rfl) ⟨366401, by rfl⟩ : syracuseStep 488535 = 732803) B732803
theorem B488555 : Blo 487790 488555 := bstep (se 1 (by rfl) ⟨366416, by rfl⟩ : syracuseStep 488555 = 732833) B732833
theorem B488567 : Blo 487790 488567 := bstep (se 1 (by rfl) ⟨366425, by rfl⟩ : syracuseStep 488567 = 732851) B732851
theorem B6288515 : Blo 487790 6288515 := bstep (se 1 (by rfl) ⟨4716386, by rfl⟩ : syracuseStep 6288515 = 9432773) B9432773
theorem B488587 : Blo 487790 488587 := bstep (se 1 (by rfl) ⟨366440, by rfl⟩ : syracuseStep 488587 = 732881) B732881
theorem B488599 : Blo 487790 488599 := bstep (se 1 (by rfl) ⟨366449, by rfl⟩ : syracuseStep 488599 = 732899) B732899
theorem B488619 : Blo 487790 488619 := bstep (se 1 (by rfl) ⟨366464, by rfl⟩ : syracuseStep 488619 = 732929) B732929
theorem B51573941 : Blo 487790 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B488631 : Blo 487790 488631 := bstep (se 1 (by rfl) ⟨366473, by rfl⟩ : syracuseStep 488631 = 732947) B732947
theorem B488651 : Blo 487790 488651 := bstep (se 1 (by rfl) ⟨366488, by rfl⟩ : syracuseStep 488651 = 732977) B732977
theorem B488663 : Blo 487790 488663 := bstep (se 1 (by rfl) ⟨366497, by rfl⟩ : syracuseStep 488663 = 732995) B732995
theorem B488683 : Blo 487790 488683 := bstep (se 1 (by rfl) ⟨366512, by rfl⟩ : syracuseStep 488683 = 733025) B733025
theorem B488695 : Blo 487790 488695 := bstep (se 1 (by rfl) ⟨366521, by rfl⟩ : syracuseStep 488695 = 733043) B733043
theorem B488715 : Blo 487790 488715 := bstep (se 1 (by rfl) ⟨366536, by rfl⟩ : syracuseStep 488715 = 733073) B733073
theorem B488727 : Blo 487790 488727 := bstep (se 1 (by rfl) ⟨366545, by rfl⟩ : syracuseStep 488727 = 733091) B733091
theorem B488747 : Blo 487790 488747 := bstep (se 1 (by rfl) ⟨366560, by rfl⟩ : syracuseStep 488747 = 733121) B733121
theorem B488759 : Blo 487790 488759 := bstep (se 1 (by rfl) ⟨366569, by rfl⟩ : syracuseStep 488759 = 733139) B733139
theorem B488779 : Blo 487790 488779 := bstep (se 1 (by rfl) ⟨366584, by rfl⟩ : syracuseStep 488779 = 733169) B733169
theorem B488791 : Blo 487790 488791 := bstep (se 1 (by rfl) ⟨366593, by rfl⟩ : syracuseStep 488791 = 733187) B733187
theorem B488811 : Blo 487790 488811 := bstep (se 1 (by rfl) ⟨366608, by rfl⟩ : syracuseStep 488811 = 733217) B733217
theorem B488823 : Blo 487790 488823 := bstep (se 1 (by rfl) ⟨366617, by rfl⟩ : syracuseStep 488823 = 733235) B733235
theorem B488843 : Blo 487790 488843 := bstep (se 1 (by rfl) ⟨366632, by rfl⟩ : syracuseStep 488843 = 733265) B733265
theorem B488855 : Blo 487790 488855 := bstep (se 1 (by rfl) ⟨366641, by rfl⟩ : syracuseStep 488855 = 733283) B733283
theorem B1176983 : Blo 487790 1176983 := bstep (se 1 (by rfl) ⟨882737, by rfl⟩ : syracuseStep 1176983 = 1765475) B1765475
theorem B488875 : Blo 487790 488875 := bstep (se 1 (by rfl) ⟨366656, by rfl⟩ : syracuseStep 488875 = 733313) B733313
theorem B488887 : Blo 487790 488887 := bstep (se 1 (by rfl) ⟨366665, by rfl⟩ : syracuseStep 488887 = 733331) B733331
theorem B488907 : Blo 487790 488907 := bstep (se 1 (by rfl) ⟨366680, by rfl⟩ : syracuseStep 488907 = 733361) B733361
theorem B488919 : Blo 487790 488919 := bstep (se 1 (by rfl) ⟨366689, by rfl⟩ : syracuseStep 488919 = 733379) B733379
theorem B1865177 : Blo 487790 1865177 := bstep (se 2 (by rfl) ⟨699441, by rfl⟩ : syracuseStep 1865177 = 1398883) B1398883
theorem B488939 : Blo 487790 488939 := bstep (se 1 (by rfl) ⟨366704, by rfl⟩ : syracuseStep 488939 = 733409) B733409
theorem B488951 : Blo 487790 488951 := bstep (se 1 (by rfl) ⟨366713, by rfl⟩ : syracuseStep 488951 = 733427) B733427
theorem B488971 : Blo 487790 488971 := bstep (se 1 (by rfl) ⟨366728, by rfl⟩ : syracuseStep 488971 = 733457) B733457
theorem B10057229 : Blo 487790 10057229 := bstep (se 3 (by rfl) ⟨1885730, by rfl⟩ : syracuseStep 10057229 = 3771461) B3771461
theorem B488983 : Blo 487790 488983 := bstep (se 1 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 488983 = 733475) B733475
theorem B489003 : Blo 487790 489003 := bstep (se 1 (by rfl) ⟨366752, by rfl⟩ : syracuseStep 489003 = 733505) B733505
theorem B489015 : Blo 487790 489015 := bstep (se 1 (by rfl) ⟨366761, by rfl⟩ : syracuseStep 489015 = 733523) B733523
theorem B1078849 : Blo 487790 1078849 := bstep (se 2 (by rfl) ⟨404568, by rfl⟩ : syracuseStep 1078849 = 809137) B809137
theorem B489035 : Blo 487790 489035 := bstep (se 1 (by rfl) ⟨366776, by rfl⟩ : syracuseStep 489035 = 733553) B733553
theorem B489047 : Blo 487790 489047 := bstep (se 1 (by rfl) ⟨366785, by rfl⟩ : syracuseStep 489047 = 733571) B733571
theorem B489067 : Blo 487790 489067 := bstep (se 1 (by rfl) ⟨366800, by rfl⟩ : syracuseStep 489067 = 733601) B733601
theorem B489079 : Blo 487790 489079 := bstep (se 1 (by rfl) ⟨366809, by rfl⟩ : syracuseStep 489079 = 733619) B733619
theorem B489099 : Blo 487790 489099 := bstep (se 1 (by rfl) ⟨366824, by rfl⟩ : syracuseStep 489099 = 733649) B733649
theorem B489111 : Blo 487790 489111 := bstep (se 1 (by rfl) ⟨366833, by rfl⟩ : syracuseStep 489111 = 733667) B733667
theorem B489131 : Blo 487790 489131 := bstep (se 1 (by rfl) ⟨366848, by rfl⟩ : syracuseStep 489131 = 733697) B733697
theorem B1865389 : Blo 487790 1865389 := bstep (se 3 (by rfl) ⟨349760, by rfl⟩ : syracuseStep 1865389 = 699521) B699521
theorem B1242803 : Blo 487790 1242803 := bstep (se 1 (by rfl) ⟨932102, by rfl⟩ : syracuseStep 1242803 = 1864205) B1864205
theorem B489143 : Blo 487790 489143 := bstep (se 1 (by rfl) ⟨366857, by rfl⟩ : syracuseStep 489143 = 733715) B733715
theorem B489163 : Blo 487790 489163 := bstep (se 1 (by rfl) ⟨366872, by rfl⟩ : syracuseStep 489163 = 733745) B733745
theorem B489175 : Blo 487790 489175 := bstep (se 1 (by rfl) ⟨366881, by rfl⟩ : syracuseStep 489175 = 733763) B733763
theorem B489195 : Blo 487790 489195 := bstep (se 1 (by rfl) ⟨366896, by rfl⟩ : syracuseStep 489195 = 733793) B733793
theorem B489207 : Blo 487790 489207 := bstep (se 1 (by rfl) ⟨366905, by rfl⟩ : syracuseStep 489207 = 733811) B733811
theorem B489227 : Blo 487790 489227 := bstep (se 1 (by rfl) ⟨366920, by rfl⟩ : syracuseStep 489227 = 733841) B733841
theorem B489239 : Blo 487790 489239 := bstep (se 1 (by rfl) ⟨366929, by rfl⟩ : syracuseStep 489239 = 733859) B733859
theorem B489259 : Blo 487790 489259 := bstep (se 1 (by rfl) ⟨366944, by rfl⟩ : syracuseStep 489259 = 733889) B733889
theorem B2520877 : Blo 487790 2520877 := bstep (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) B945329
theorem B489271 : Blo 487790 489271 := bstep (se 1 (by rfl) ⟨366953, by rfl⟩ : syracuseStep 489271 = 733907) B733907
theorem B1767233 : Blo 487790 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B489291 : Blo 487790 489291 := bstep (se 1 (by rfl) ⟨366968, by rfl⟩ : syracuseStep 489291 = 733937) B733937
theorem B489303 : Blo 487790 489303 := bstep (se 1 (by rfl) ⟨366977, by rfl⟩ : syracuseStep 489303 = 733955) B733955
theorem B2488157 : Blo 487790 2488157 := bstep (se 3 (by rfl) ⟨466529, by rfl⟩ : syracuseStep 2488157 = 933059) B933059
theorem B489323 : Blo 487790 489323 := bstep (se 1 (by rfl) ⟨366992, by rfl⟩ : syracuseStep 489323 = 733985) B733985
theorem B489335 : Blo 487790 489335 := bstep (se 1 (by rfl) ⟨367001, by rfl⟩ : syracuseStep 489335 = 734003) B734003
theorem B489355 : Blo 487790 489355 := bstep (se 1 (by rfl) ⟨367016, by rfl⟩ : syracuseStep 489355 = 734033) B734033
theorem B489367 : Blo 487790 489367 := bstep (se 1 (by rfl) ⟨367025, by rfl⟩ : syracuseStep 489367 = 734051) B734051
theorem B489387 : Blo 487790 489387 := bstep (se 1 (by rfl) ⟨367040, by rfl⟩ : syracuseStep 489387 = 734081) B734081
theorem B489399 : Blo 487790 489399 := bstep (se 1 (by rfl) ⟨367049, by rfl⟩ : syracuseStep 489399 = 734099) B734099
theorem B489419 : Blo 487790 489419 := bstep (se 1 (by rfl) ⟨367064, by rfl⟩ : syracuseStep 489419 = 734129) B734129
theorem B489431 : Blo 487790 489431 := bstep (se 1 (by rfl) ⟨367073, by rfl⟩ : syracuseStep 489431 = 734147) B734147
theorem B1243097 : Blo 487790 1243097 := bstep (se 2 (by rfl) ⟨466161, by rfl⟩ : syracuseStep 1243097 = 932323) B932323
theorem B1865693 : Blo 487790 1865693 := bstep (se 3 (by rfl) ⟨349817, by rfl⟩ : syracuseStep 1865693 = 699635) B699635
theorem B489451 : Blo 487790 489451 := bstep (se 1 (by rfl) ⟨367088, by rfl⟩ : syracuseStep 489451 = 734177) B734177
theorem B489463 : Blo 487790 489463 := bstep (se 1 (by rfl) ⟨367097, by rfl⟩ : syracuseStep 489463 = 734195) B734195
theorem B489483 : Blo 487790 489483 := bstep (se 1 (by rfl) ⟨367112, by rfl⟩ : syracuseStep 489483 = 734225) B734225
theorem B489495 : Blo 487790 489495 := bstep (se 1 (by rfl) ⟨367121, by rfl⟩ : syracuseStep 489495 = 734243) B734243
theorem B489515 : Blo 487790 489515 := bstep (se 1 (by rfl) ⟨367136, by rfl⟩ : syracuseStep 489515 = 734273) B734273
theorem B489527 : Blo 487790 489527 := bstep (se 1 (by rfl) ⟨367145, by rfl⟩ : syracuseStep 489527 = 734291) B734291
theorem B489547 : Blo 487790 489547 := bstep (se 1 (by rfl) ⟨367160, by rfl⟩ : syracuseStep 489547 = 734321) B734321
theorem B489559 : Blo 487790 489559 := bstep (se 1 (by rfl) ⟨367169, by rfl⟩ : syracuseStep 489559 = 734339) B734339
theorem B489579 : Blo 487790 489579 := bstep (se 1 (by rfl) ⟨367184, by rfl⟩ : syracuseStep 489579 = 734369) B734369
theorem B489591 : Blo 487790 489591 := bstep (se 1 (by rfl) ⟨367193, by rfl⟩ : syracuseStep 489591 = 734387) B734387
theorem B489611 : Blo 487790 489611 := bstep (se 1 (by rfl) ⟨367208, by rfl⟩ : syracuseStep 489611 = 734417) B734417
theorem B489623 : Blo 487790 489623 := bstep (se 1 (by rfl) ⟨367217, by rfl⟩ : syracuseStep 489623 = 734435) B734435
theorem B1177751 : Blo 487790 1177751 := bstep (se 1 (by rfl) ⟨883313, by rfl⟩ : syracuseStep 1177751 = 1766627) B1766627
theorem B6715543 : Blo 487790 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B489643 : Blo 487790 489643 := bstep (se 1 (by rfl) ⟨367232, by rfl⟩ : syracuseStep 489643 = 734465) B734465
theorem B2095283 : Blo 487790 2095283 := bstep (se 1 (by rfl) ⟨1571462, by rfl⟩ : syracuseStep 2095283 = 3142925) B3142925
theorem B489655 : Blo 487790 489655 := bstep (se 1 (by rfl) ⟨367241, by rfl⟩ : syracuseStep 489655 = 734483) B734483
theorem B489675 : Blo 487790 489675 := bstep (se 1 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 489675 = 734513) B734513
theorem B489687 : Blo 487790 489687 := bstep (se 1 (by rfl) ⟨367265, by rfl⟩ : syracuseStep 489687 = 734531) B734531
theorem B489707 : Blo 487790 489707 := bstep (se 1 (by rfl) ⟨367280, by rfl⟩ : syracuseStep 489707 = 734561) B734561
theorem B489719 : Blo 487790 489719 := bstep (se 1 (by rfl) ⟨367289, by rfl⟩ : syracuseStep 489719 = 734579) B734579
theorem B489739 : Blo 487790 489739 := bstep (se 1 (by rfl) ⟨367304, by rfl⟩ : syracuseStep 489739 = 734609) B734609
theorem B489751 : Blo 487790 489751 := bstep (se 1 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 489751 = 734627) B734627
theorem B1276183 : Blo 487790 1276183 := bstep (se 1 (by rfl) ⟨957137, by rfl⟩ : syracuseStep 1276183 = 1914275) B1914275
theorem B489771 : Blo 487790 489771 := bstep (se 1 (by rfl) ⟨367328, by rfl⟩ : syracuseStep 489771 = 734657) B734657
theorem B489783 : Blo 487790 489783 := bstep (se 1 (by rfl) ⟨367337, by rfl⟩ : syracuseStep 489783 = 734675) B734675
theorem B588107 : Blo 487790 588107 := bstep (se 1 (by rfl) ⟨441080, by rfl⟩ : syracuseStep 588107 = 882161) B882161
theorem B489803 : Blo 487790 489803 := bstep (se 1 (by rfl) ⟨367352, by rfl⟩ : syracuseStep 489803 = 734705) B734705
theorem B620875 : Blo 487790 620875 := bstep (se 1 (by rfl) ⟨465656, by rfl⟩ : syracuseStep 620875 = 931313) B931313
theorem B2357579 : Blo 487790 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B489815 : Blo 487790 489815 := bstep (se 1 (by rfl) ⟨367361, by rfl⟩ : syracuseStep 489815 = 734723) B734723
theorem B489835 : Blo 487790 489835 := bstep (se 1 (by rfl) ⟨367376, by rfl⟩ : syracuseStep 489835 = 734753) B734753
theorem B489847 : Blo 487790 489847 := bstep (se 1 (by rfl) ⟨367385, by rfl⟩ : syracuseStep 489847 = 734771) B734771
theorem B489867 : Blo 487790 489867 := bstep (se 1 (by rfl) ⟨367400, by rfl⟩ : syracuseStep 489867 = 734801) B734801
theorem B489879 : Blo 487790 489879 := bstep (se 1 (by rfl) ⟨367409, by rfl⟩ : syracuseStep 489879 = 734819) B734819
theorem B489899 : Blo 487790 489899 := bstep (se 1 (by rfl) ⟨367424, by rfl⟩ : syracuseStep 489899 = 734849) B734849
theorem B3733937 : Blo 487790 3733937 := bstep (se 2 (by rfl) ⟨1400226, by rfl⟩ : syracuseStep 3733937 = 2800453) B2800453
theorem B489911 : Blo 487790 489911 := bstep (se 1 (by rfl) ⟨367433, by rfl⟩ : syracuseStep 489911 = 734867) B734867
theorem B489931 : Blo 487790 489931 := bstep (se 1 (by rfl) ⟨367448, by rfl⟩ : syracuseStep 489931 = 734897) B734897
theorem B1178059 : Blo 487790 1178059 := bstep (se 1 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 1178059 = 1767089) B1767089
theorem B489943 : Blo 487790 489943 := bstep (se 1 (by rfl) ⟨367457, by rfl⟩ : syracuseStep 489943 = 734915) B734915
theorem B2980313 : Blo 487790 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B489963 : Blo 487790 489963 := bstep (se 1 (by rfl) ⟨367472, by rfl⟩ : syracuseStep 489963 = 734945) B734945
theorem B489975 : Blo 487790 489975 := bstep (se 1 (by rfl) ⟨367481, by rfl⟩ : syracuseStep 489975 = 734963) B734963
theorem B489995 : Blo 487790 489995 := bstep (se 1 (by rfl) ⟨367496, by rfl⟩ : syracuseStep 489995 = 734993) B734993
theorem B2259479 : Blo 487790 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B490007 : Blo 487790 490007 := bstep (se 1 (by rfl) ⟨367505, by rfl⟩ : syracuseStep 490007 = 735011) B735011
theorem B8354339 : Blo 487790 8354339 := bstep (se 1 (by rfl) ⟨6265754, by rfl⟩ : syracuseStep 8354339 = 12531509) B12531509
theorem B490027 : Blo 487790 490027 := bstep (se 1 (by rfl) ⟨367520, by rfl⟩ : syracuseStep 490027 = 735041) B735041
theorem B490039 : Blo 487790 490039 := bstep (se 1 (by rfl) ⟨367529, by rfl⟩ : syracuseStep 490039 = 735059) B735059
theorem B490059 : Blo 487790 490059 := bstep (se 1 (by rfl) ⟨367544, by rfl⟩ : syracuseStep 490059 = 735089) B735089
theorem B490071 : Blo 487790 490071 := bstep (se 1 (by rfl) ⟨367553, by rfl⟩ : syracuseStep 490071 = 735107) B735107
theorem B490091 : Blo 487790 490091 := bstep (se 1 (by rfl) ⟨367568, by rfl⟩ : syracuseStep 490091 = 735137) B735137
theorem B490103 : Blo 487790 490103 := bstep (se 1 (by rfl) ⟨367577, by rfl⟩ : syracuseStep 490103 = 735155) B735155
theorem B490123 : Blo 487790 490123 := bstep (se 1 (by rfl) ⟨367592, by rfl⟩ : syracuseStep 490123 = 735185) B735185
theorem B5569175 : Blo 487790 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B490135 : Blo 487790 490135 := bstep (se 1 (by rfl) ⟨367601, by rfl⟩ : syracuseStep 490135 = 735203) B735203
theorem B490155 : Blo 487790 490155 := bstep (se 1 (by rfl) ⟨367616, by rfl⟩ : syracuseStep 490155 = 735233) B735233
theorem B490167 : Blo 487790 490167 := bstep (se 1 (by rfl) ⟨367625, by rfl⟩ : syracuseStep 490167 = 735251) B735251
theorem B490187 : Blo 487790 490187 := bstep (se 1 (by rfl) ⟨367640, by rfl⟩ : syracuseStep 490187 = 735281) B735281
theorem B490199 : Blo 487790 490199 := bstep (se 1 (by rfl) ⟨367649, by rfl⟩ : syracuseStep 490199 = 735299) B735299
theorem B490219 : Blo 487790 490219 := bstep (se 1 (by rfl) ⟨367664, by rfl⟩ : syracuseStep 490219 = 735329) B735329
theorem B490231 : Blo 487790 490231 := bstep (se 1 (by rfl) ⟨367673, by rfl⟩ : syracuseStep 490231 = 735347) B735347
theorem B490251 : Blo 487790 490251 := bstep (se 1 (by rfl) ⟨367688, by rfl⟩ : syracuseStep 490251 = 735377) B735377
theorem B490263 : Blo 487790 490263 := bstep (se 1 (by rfl) ⟨367697, by rfl⟩ : syracuseStep 490263 = 735395) B735395
theorem B490283 : Blo 487790 490283 := bstep (se 1 (by rfl) ⟨367712, by rfl⟩ : syracuseStep 490283 = 735425) B735425
theorem B490295 : Blo 487790 490295 := bstep (se 1 (by rfl) ⟨367721, by rfl⟩ : syracuseStep 490295 = 735443) B735443
theorem B490315 : Blo 487790 490315 := bstep (se 1 (by rfl) ⟨367736, by rfl⟩ : syracuseStep 490315 = 735473) B735473
theorem B490327 : Blo 487790 490327 := bstep (se 1 (by rfl) ⟨367745, by rfl⟩ : syracuseStep 490327 = 735491) B735491
theorem B3144541 : Blo 487790 3144541 := bstep (se 3 (by rfl) ⟨589601, by rfl⟩ : syracuseStep 3144541 = 1179203) B1179203
theorem B3406693 : Blo 487790 3406693 := bstep (se 4 (by rfl) ⟨319377, by rfl⟩ : syracuseStep 3406693 = 638755) B638755
theorem B490347 : Blo 487790 490347 := bstep (se 1 (by rfl) ⟨367760, by rfl⟩ : syracuseStep 490347 = 735521) B735521
theorem B490359 : Blo 487790 490359 := bstep (se 1 (by rfl) ⟨367769, by rfl⟩ : syracuseStep 490359 = 735539) B735539
theorem B490379 : Blo 487790 490379 := bstep (se 1 (by rfl) ⟨367784, by rfl⟩ : syracuseStep 490379 = 735569) B735569
theorem B490391 : Blo 487790 490391 := bstep (se 1 (by rfl) ⟨367793, by rfl⟩ : syracuseStep 490391 = 735587) B735587
theorem B3734423 : Blo 487790 3734423 := bstep (se 1 (by rfl) ⟨2800817, by rfl⟩ : syracuseStep 3734423 = 5601635) B5601635
theorem B490411 : Blo 487790 490411 := bstep (se 1 (by rfl) ⟨367808, by rfl⟩ : syracuseStep 490411 = 735617) B735617
theorem B490423 : Blo 487790 490423 := bstep (se 1 (by rfl) ⟨367817, by rfl⟩ : syracuseStep 490423 = 735635) B735635
theorem B490443 : Blo 487790 490443 := bstep (se 1 (by rfl) ⟨367832, by rfl⟩ : syracuseStep 490443 = 735665) B735665
theorem B490455 : Blo 487790 490455 := bstep (se 1 (by rfl) ⟨367841, by rfl⟩ : syracuseStep 490455 = 735683) B735683
theorem B490475 : Blo 487790 490475 := bstep (se 1 (by rfl) ⟨367856, by rfl⟩ : syracuseStep 490475 = 735713) B735713
theorem B1047539 : Blo 487790 1047539 := bstep (se 1 (by rfl) ⟨785654, by rfl⟩ : syracuseStep 1047539 = 1571309) B1571309
theorem B490487 : Blo 487790 490487 := bstep (se 1 (by rfl) ⟨367865, by rfl⟩ : syracuseStep 490487 = 735731) B735731
theorem B490507 : Blo 487790 490507 := bstep (se 1 (by rfl) ⟨367880, by rfl⟩ : syracuseStep 490507 = 735761) B735761
theorem B490519 : Blo 487790 490519 := bstep (se 1 (by rfl) ⟨367889, by rfl⟩ : syracuseStep 490519 = 735779) B735779
theorem B490539 : Blo 487790 490539 := bstep (se 1 (by rfl) ⟨367904, by rfl⟩ : syracuseStep 490539 = 735809) B735809
theorem B1178675 : Blo 487790 1178675 := bstep (se 1 (by rfl) ⟨884006, by rfl⟩ : syracuseStep 1178675 = 1768013) B1768013
theorem B490551 : Blo 487790 490551 := bstep (se 1 (by rfl) ⟨367913, by rfl⟩ : syracuseStep 490551 = 735827) B735827
theorem B490571 : Blo 487790 490571 := bstep (se 1 (by rfl) ⟨367928, by rfl⟩ : syracuseStep 490571 = 735857) B735857
theorem B523351 : Blo 487790 523351 := bstep (se 1 (by rfl) ⟨392513, by rfl⟩ : syracuseStep 523351 = 785027) B785027
theorem B490583 : Blo 487790 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B490603 : Blo 487790 490603 := bstep (se 1 (by rfl) ⟨367952, by rfl⟩ : syracuseStep 490603 = 735905) B735905
theorem B490615 : Blo 487790 490615 := bstep (se 1 (by rfl) ⟨367961, by rfl⟩ : syracuseStep 490615 = 735923) B735923
theorem B490635 : Blo 487790 490635 := bstep (se 1 (by rfl) ⟨367976, by rfl⟩ : syracuseStep 490635 = 735953) B735953
theorem B490647 : Blo 487790 490647 := bstep (se 1 (by rfl) ⟨367985, by rfl⟩ : syracuseStep 490647 = 735971) B735971
theorem B490667 : Blo 487790 490667 := bstep (se 1 (by rfl) ⟨368000, by rfl⟩ : syracuseStep 490667 = 736001) B736001
theorem B490679 : Blo 487790 490679 := bstep (se 1 (by rfl) ⟨368009, by rfl⟩ : syracuseStep 490679 = 736019) B736019
theorem B490699 : Blo 487790 490699 := bstep (se 1 (by rfl) ⟨368024, by rfl⟩ : syracuseStep 490699 = 736049) B736049
theorem B490711 : Blo 487790 490711 := bstep (se 1 (by rfl) ⟨368033, by rfl⟩ : syracuseStep 490711 = 736067) B736067
theorem B490731 : Blo 487790 490731 := bstep (se 1 (by rfl) ⟨368048, by rfl⟩ : syracuseStep 490731 = 736097) B736097
theorem B490743 : Blo 487790 490743 := bstep (se 1 (by rfl) ⟨368057, by rfl⟩ : syracuseStep 490743 = 736115) B736115
theorem B785675 : Blo 487790 785675 := bstep (se 1 (by rfl) ⟨589256, by rfl⟩ : syracuseStep 785675 = 1178513) B1178513
theorem B490763 : Blo 487790 490763 := bstep (se 1 (by rfl) ⟨368072, by rfl⟩ : syracuseStep 490763 = 736145) B736145
theorem B490775 : Blo 487790 490775 := bstep (se 1 (by rfl) ⟨368081, by rfl⟩ : syracuseStep 490775 = 736163) B736163
theorem B621847 : Blo 487790 621847 := bstep (se 1 (by rfl) ⟨466385, by rfl⟩ : syracuseStep 621847 = 932771) B932771
theorem B490795 : Blo 487790 490795 := bstep (se 1 (by rfl) ⟨368096, by rfl⟩ : syracuseStep 490795 = 736193) B736193
theorem B490807 : Blo 487790 490807 := bstep (se 1 (by rfl) ⟨368105, by rfl⟩ : syracuseStep 490807 = 736211) B736211
theorem B490827 : Blo 487790 490827 := bstep (se 1 (by rfl) ⟨368120, by rfl⟩ : syracuseStep 490827 = 736241) B736241
theorem B490839 : Blo 487790 490839 := bstep (se 1 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 490839 = 736259) B736259
theorem B490859 : Blo 487790 490859 := bstep (se 1 (by rfl) ⟨368144, by rfl⟩ : syracuseStep 490859 = 736289) B736289
theorem B490871 : Blo 487790 490871 := bstep (se 1 (by rfl) ⟨368153, by rfl⟩ : syracuseStep 490871 = 736307) B736307
theorem B490891 : Blo 487790 490891 := bstep (se 1 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 490891 = 736337) B736337
theorem B490903 : Blo 487790 490903 := bstep (se 1 (by rfl) ⟨368177, by rfl⟩ : syracuseStep 490903 = 736355) B736355
theorem B490923 : Blo 487790 490923 := bstep (se 1 (by rfl) ⟨368192, by rfl⟩ : syracuseStep 490923 = 736385) B736385
theorem B490935 : Blo 487790 490935 := bstep (se 1 (by rfl) ⟨368201, by rfl⟩ : syracuseStep 490935 = 736403) B736403
theorem B490955 : Blo 487790 490955 := bstep (se 1 (by rfl) ⟨368216, by rfl⟩ : syracuseStep 490955 = 736433) B736433
theorem B490967 : Blo 487790 490967 := bstep (se 1 (by rfl) ⟨368225, by rfl⟩ : syracuseStep 490967 = 736451) B736451
theorem B490987 : Blo 487790 490987 := bstep (se 1 (by rfl) ⟨368240, by rfl⟩ : syracuseStep 490987 = 736481) B736481
theorem B490999 : Blo 487790 490999 := bstep (se 1 (by rfl) ⟨368249, by rfl⟩ : syracuseStep 490999 = 736499) B736499
theorem B491019 : Blo 487790 491019 := bstep (se 1 (by rfl) ⟨368264, by rfl⟩ : syracuseStep 491019 = 736529) B736529
theorem B491031 : Blo 487790 491031 := bstep (se 1 (by rfl) ⟨368273, by rfl⟩ : syracuseStep 491031 = 736547) B736547
theorem B491051 : Blo 487790 491051 := bstep (se 1 (by rfl) ⟨368288, by rfl⟩ : syracuseStep 491051 = 736577) B736577
theorem B491063 : Blo 487790 491063 := bstep (se 1 (by rfl) ⟨368297, by rfl⟩ : syracuseStep 491063 = 736595) B736595
theorem B491083 : Blo 487790 491083 := bstep (se 1 (by rfl) ⟨368312, by rfl⟩ : syracuseStep 491083 = 736625) B736625
theorem B1244747 : Blo 487790 1244747 := bstep (se 1 (by rfl) ⟨933560, by rfl⟩ : syracuseStep 1244747 = 1867121) B1867121
theorem B491095 : Blo 487790 491095 := bstep (se 1 (by rfl) ⟨368321, by rfl⟩ : syracuseStep 491095 = 736643) B736643
theorem B753241 : Blo 487790 753241 := bstep (se 2 (by rfl) ⟨282465, by rfl⟩ : syracuseStep 753241 = 564931) B564931
theorem B491115 : Blo 487790 491115 := bstep (se 1 (by rfl) ⟨368336, by rfl⟩ : syracuseStep 491115 = 736673) B736673
theorem B491127 : Blo 487790 491127 := bstep (se 1 (by rfl) ⟨368345, by rfl⟩ : syracuseStep 491127 = 736691) B736691
theorem B491147 : Blo 487790 491147 := bstep (se 1 (by rfl) ⟨368360, by rfl⟩ : syracuseStep 491147 = 736721) B736721
theorem B491159 : Blo 487790 491159 := bstep (se 1 (by rfl) ⟨368369, by rfl⟩ : syracuseStep 491159 = 736739) B736739
theorem B491179 : Blo 487790 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B2981555 : Blo 487790 2981555 := bstep (se 1 (by rfl) ⟨2236166, by rfl⟩ : syracuseStep 2981555 = 4472333) B4472333
theorem B491191 : Blo 487790 491191 := bstep (se 1 (by rfl) ⟨368393, by rfl⟩ : syracuseStep 491191 = 736787) B736787
theorem B491211 : Blo 487790 491211 := bstep (se 1 (by rfl) ⟨368408, by rfl⟩ : syracuseStep 491211 = 736817) B736817
theorem B491223 : Blo 487790 491223 := bstep (se 1 (by rfl) ⟨368417, by rfl⟩ : syracuseStep 491223 = 736835) B736835
theorem B491243 : Blo 487790 491243 := bstep (se 1 (by rfl) ⟨368432, by rfl⟩ : syracuseStep 491243 = 736865) B736865
theorem B884467 : Blo 487790 884467 := bstep (se 1 (by rfl) ⟨663350, by rfl⟩ : syracuseStep 884467 = 1326701) B1326701
theorem B491255 : Blo 487790 491255 := bstep (se 1 (by rfl) ⟨368441, by rfl⟩ : syracuseStep 491255 = 736883) B736883
theorem B491275 : Blo 487790 491275 := bstep (se 1 (by rfl) ⟨368456, by rfl⟩ : syracuseStep 491275 = 736913) B736913
theorem B491287 : Blo 487790 491287 := bstep (se 1 (by rfl) ⟨368465, by rfl⟩ : syracuseStep 491287 = 736931) B736931
theorem B491307 : Blo 487790 491307 := bstep (se 1 (by rfl) ⟨368480, by rfl⟩ : syracuseStep 491307 = 736961) B736961
theorem B1179443 : Blo 487790 1179443 := bstep (se 1 (by rfl) ⟨884582, by rfl⟩ : syracuseStep 1179443 = 1769165) B1769165
theorem B491319 : Blo 487790 491319 := bstep (se 1 (by rfl) ⟨368489, by rfl⟩ : syracuseStep 491319 = 736979) B736979
theorem B491339 : Blo 487790 491339 := bstep (se 1 (by rfl) ⟨368504, by rfl⟩ : syracuseStep 491339 = 737009) B737009
theorem B491351 : Blo 487790 491351 := bstep (se 1 (by rfl) ⟨368513, by rfl⟩ : syracuseStep 491351 = 737027) B737027
theorem B491371 : Blo 487790 491371 := bstep (se 1 (by rfl) ⟨368528, by rfl⟩ : syracuseStep 491371 = 737057) B737057
theorem B491383 : Blo 487790 491383 := bstep (se 1 (by rfl) ⟨368537, by rfl⟩ : syracuseStep 491383 = 737075) B737075
theorem B491403 : Blo 487790 491403 := bstep (se 1 (by rfl) ⟨368552, by rfl⟩ : syracuseStep 491403 = 737105) B737105
theorem B491415 : Blo 487790 491415 := bstep (se 1 (by rfl) ⟨368561, by rfl⟩ : syracuseStep 491415 = 737123) B737123
theorem B491435 : Blo 487790 491435 := bstep (se 1 (by rfl) ⟨368576, by rfl⟩ : syracuseStep 491435 = 737153) B737153
theorem B491447 : Blo 487790 491447 := bstep (se 1 (by rfl) ⟨368585, by rfl⟩ : syracuseStep 491447 = 737171) B737171
theorem B491467 : Blo 487790 491467 := bstep (se 1 (by rfl) ⟨368600, by rfl⟩ : syracuseStep 491467 = 737201) B737201
theorem B491479 : Blo 487790 491479 := bstep (se 1 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 491479 = 737219) B737219
theorem B491499 : Blo 487790 491499 := bstep (se 1 (by rfl) ⟨368624, by rfl⟩ : syracuseStep 491499 = 737249) B737249
theorem B491511 : Blo 487790 491511 := bstep (se 1 (by rfl) ⟨368633, by rfl⟩ : syracuseStep 491511 = 737267) B737267
theorem B491527 : Blo 487790 491527 := bstep (se 1 (by rfl) ⟨368645, by rfl⟩ : syracuseStep 491527 = 737291) B737291
theorem B491535 : Blo 487790 491535 := bstep (se 1 (by rfl) ⟨368651, by rfl⟩ : syracuseStep 491535 = 737303) B737303
theorem B491579 : Blo 487790 491579 := bstep (se 1 (by rfl) ⟨368684, by rfl⟩ : syracuseStep 491579 = 737369) B737369
theorem B491655 : Blo 487790 491655 := bstep (se 1 (by rfl) ⟨368741, by rfl⟩ : syracuseStep 491655 = 737483) B737483
theorem B491663 : Blo 487790 491663 := bstep (se 1 (by rfl) ⟨368747, by rfl⟩ : syracuseStep 491663 = 737495) B737495
theorem B491707 : Blo 487790 491707 := bstep (se 1 (by rfl) ⟨368780, by rfl⟩ : syracuseStep 491707 = 737561) B737561
theorem B491783 : Blo 487790 491783 := bstep (se 1 (by rfl) ⟨368837, by rfl⟩ : syracuseStep 491783 = 737675) B737675
theorem B524603 : Blo 487790 524603 := bstep (se 1 (by rfl) ⟨393452, by rfl⟩ : syracuseStep 524603 = 786905) B786905
theorem B1114825 : Blo 487790 1114825 := bstep (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) B836119
theorem B885563 : Blo 487790 885563 := bstep (se 1 (by rfl) ⟨664172, by rfl⟩ : syracuseStep 885563 = 1328345) B1328345
theorem B10617749 : Blo 487790 10617749 := bstep (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) B497707
theorem B54887381 : Blo 487790 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B1180673 : Blo 487790 1180673 := bstep (se 2 (by rfl) ⟨442752, by rfl⟩ : syracuseStep 1180673 = 885505) B885505
theorem B1180943 : Blo 487790 1180943 := bstep (se 1 (by rfl) ⟨885707, by rfl⟩ : syracuseStep 1180943 = 1771415) B1771415
theorem B1049915 : Blo 487790 1049915 := bstep (se 1 (by rfl) ⟨787436, by rfl⟩ : syracuseStep 1049915 = 1574873) B1574873
theorem B1672595 : Blo 487790 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B4196033 : Blo 487790 4196033 := bstep (se 2 (by rfl) ⟨1573512, by rfl⟩ : syracuseStep 4196033 = 3147025) B3147025
theorem B1410859 : Blo 487790 1410859 := bstep (se 1 (by rfl) ⟨1058144, by rfl⟩ : syracuseStep 1410859 = 2116289) B2116289
theorem B558991 : Blo 487790 558991 := bstep (se 1 (by rfl) ⟨419243, by rfl⟩ : syracuseStep 558991 = 838487) B838487
theorem B2787331 : Blo 487790 2787331 := bstep (se 1 (by rfl) ⟨2090498, by rfl⟩ : syracuseStep 2787331 = 4180997) B4180997
theorem B1673303 : Blo 487790 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B2099641 : Blo 487790 2099641 := bstep (se 2 (by rfl) ⟨787365, by rfl⟩ : syracuseStep 2099641 = 1574731) B1574731
theorem B1347017 : Blo 487790 1347017 := bstep (se 2 (by rfl) ⟨505131, by rfl⟩ : syracuseStep 1347017 = 1010263) B1010263
theorem B10620517 : Blo 487790 10620517 := bstep (se 4 (by rfl) ⟨995673, by rfl⟩ : syracuseStep 10620517 = 1991347) B1991347
theorem B17927831 : Blo 487790 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B9506609 : Blo 487790 9506609 := bstep (se 2 (by rfl) ⟨3564978, by rfl⟩ : syracuseStep 9506609 = 7129957) B7129957
theorem B3543173 : Blo 487790 3543173 := bstep (se 4 (by rfl) ⟨332172, by rfl⟩ : syracuseStep 3543173 = 664345) B664345
theorem B823567 : Blo 487790 823567 := bstep (se 1 (by rfl) ⟨617675, by rfl⟩ : syracuseStep 823567 = 1235351) B1235351
theorem B1511723 : Blo 487790 1511723 := bstep (se 1 (by rfl) ⟨1133792, by rfl⟩ : syracuseStep 1511723 = 2267585) B2267585
theorem B5017949 : Blo 487790 5017949 := bstep (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) B1881731
theorem B2789747 : Blo 487790 2789747 := bstep (se 1 (by rfl) ⟨2092310, by rfl⟩ : syracuseStep 2789747 = 4184621) B4184621
theorem B4789007 : Blo 487790 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B824107 : Blo 487790 824107 := bstep (se 1 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 824107 = 1236161) B1236161
theorem B824249 : Blo 487790 824249 := bstep (se 2 (by rfl) ⟨309093, by rfl⟩ : syracuseStep 824249 = 618187) B618187
theorem B1512857 : Blo 487790 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B660907 : Blo 487790 660907 := bstep (se 1 (by rfl) ⟨495680, by rfl⟩ : syracuseStep 660907 = 991361) B991361
theorem B824951 : Blo 487790 824951 := bstep (se 1 (by rfl) ⟨618713, by rfl⟩ : syracuseStep 824951 = 1237427) B1237427
theorem B2233975 : Blo 487790 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B2791205 : Blo 487790 2791205 := bstep (se 4 (by rfl) ⟨261675, by rfl⟩ : syracuseStep 2791205 = 523351) B523351
theorem B825403 : Blo 487790 825403 := bstep (se 1 (by rfl) ⟨619052, by rfl⟩ : syracuseStep 825403 = 1238105) B1238105
theorem B661675 : Blo 487790 661675 := bstep (se 1 (by rfl) ⟨496256, by rfl⟩ : syracuseStep 661675 = 992513) B992513
theorem B825545 : Blo 487790 825545 := bstep (se 2 (by rfl) ⟨309579, by rfl⟩ : syracuseStep 825545 = 619159) B619159
theorem B2988433 : Blo 487790 2988433 := bstep (se 2 (by rfl) ⟨1120662, by rfl⟩ : syracuseStep 2988433 = 2241325) B2241325
theorem B2791979 : Blo 487790 2791979 := bstep (se 1 (by rfl) ⟨2093984, by rfl⟩ : syracuseStep 2791979 = 4187969) B4187969
theorem B1514137 : Blo 487790 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B4725539 : Blo 487790 4725539 := bstep (se 1 (by rfl) ⟨3544154, by rfl⟩ : syracuseStep 4725539 = 7088309) B7088309
theorem B826247 : Blo 487790 826247 := bstep (se 1 (by rfl) ⟨619685, by rfl⟩ : syracuseStep 826247 = 1239371) B1239371
theorem B14851133 : Blo 487790 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B1416311 : Blo 487790 1416311 := bstep (se 1 (by rfl) ⟨1062233, by rfl⟩ : syracuseStep 1416311 = 2124467) B2124467
theorem B9378949 : Blo 487790 9378949 := bstep (se 4 (by rfl) ⟨879276, by rfl⟩ : syracuseStep 9378949 = 1758553) B1758553
theorem B826895 : Blo 487790 826895 := bstep (se 1 (by rfl) ⟨620171, by rfl⟩ : syracuseStep 826895 = 1240343) B1240343
theorem B1678877 : Blo 487790 1678877 := bstep (se 3 (by rfl) ⟨314789, by rfl⟩ : syracuseStep 1678877 = 629579) B629579
theorem B5578307 : Blo 487790 5578307 := bstep (se 1 (by rfl) ⟨4183730, by rfl⟩ : syracuseStep 5578307 = 8367461) B8367461
theorem B4726349 : Blo 487790 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B1646351 : Blo 487790 1646351 := bstep (se 1 (by rfl) ⟨1234763, by rfl⟩ : syracuseStep 1646351 = 2469527) B2469527
theorem B2793437 : Blo 487790 2793437 := bstep (se 3 (by rfl) ⟨523769, by rfl⟩ : syracuseStep 2793437 = 1047539) B1047539
theorem B1646621 : Blo 487790 1646621 := bstep (se 3 (by rfl) ⟨308741, by rfl⟩ : syracuseStep 1646621 = 617483) B617483
theorem B827435 : Blo 487790 827435 := bstep (se 1 (by rfl) ⟨620576, by rfl⟩ : syracuseStep 827435 = 1241153) B1241153
theorem B4169789 : Blo 487790 4169789 := bstep (se 3 (by rfl) ⟨781835, by rfl⟩ : syracuseStep 4169789 = 1563671) B1563671
theorem B8954057 : Blo 487790 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B696719 : Blo 487790 696719 := bstep (se 1 (by rfl) ⟨522539, by rfl⟩ : syracuseStep 696719 = 1045079) B1045079
theorem B827833 : Blo 487790 827833 := bstep (se 2 (by rfl) ⟨310437, by rfl⟩ : syracuseStep 827833 = 620875) B620875
theorem B4694705 : Blo 487790 4694705 := bstep (se 2 (by rfl) ⟨1760514, by rfl⟩ : syracuseStep 4694705 = 3521029) B3521029
theorem B34382627 : Blo 487790 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B1451009 : Blo 487790 1451009 := bstep (se 2 (by rfl) ⟨544128, by rfl⟩ : syracuseStep 1451009 = 1088257) B1088257
theorem B5350445 : Blo 487790 5350445 := bstep (se 3 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 5350445 = 2006417) B2006417
theorem B828535 : Blo 487790 828535 := bstep (se 1 (by rfl) ⟨621401, by rfl⟩ : syracuseStep 828535 = 1242803) B1242803
theorem B828731 : Blo 487790 828731 := bstep (se 1 (by rfl) ⟨621548, by rfl⟩ : syracuseStep 828731 = 1243097) B1243097
theorem B1648025 : Blo 487790 1648025 := bstep (se 2 (by rfl) ⟨618009, by rfl⟩ : syracuseStep 1648025 = 1236019) B1236019
theorem B927379 : Blo 487790 927379 := bstep (se 1 (by rfl) ⟨695534, by rfl⟩ : syracuseStep 927379 = 1391069) B1391069
theorem B829129 : Blo 487790 829129 := bstep (se 2 (by rfl) ⟨310923, by rfl⟩ : syracuseStep 829129 = 621847) B621847
theorem B927607 : Blo 487790 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B2828317 : Blo 487790 2828317 := bstep (se 3 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 2828317 = 1060619) B1060619
theorem B1648727 : Blo 487790 1648727 := bstep (se 1 (by rfl) ⟨1236545, by rfl⟩ : syracuseStep 1648727 = 2473091) B2473091
theorem B829831 : Blo 487790 829831 := bstep (se 1 (by rfl) ⟨622373, by rfl⟩ : syracuseStep 829831 = 1244747) B1244747
theorem B731705 : Blo 487790 731705 := bstep (se 2 (by rfl) ⟨274389, by rfl⟩ : syracuseStep 731705 = 548779) B548779
theorem B1649213 : Blo 487790 1649213 := bstep (se 3 (by rfl) ⟨309227, by rfl⟩ : syracuseStep 1649213 = 618455) B618455
theorem B731783 : Blo 487790 731783 := bstep (se 1 (by rfl) ⟨548837, by rfl⟩ : syracuseStep 731783 = 1097675) B1097675
theorem B731819 : Blo 487790 731819 := bstep (se 1 (by rfl) ⟨548864, by rfl⟩ : syracuseStep 731819 = 1097729) B1097729
theorem B731849 : Blo 487790 731849 := bstep (se 2 (by rfl) ⟨274443, by rfl⟩ : syracuseStep 731849 = 548887) B548887
theorem B1321771 : Blo 487790 1321771 := bstep (se 1 (by rfl) ⟨991328, by rfl⟩ : syracuseStep 1321771 = 1982657) B1982657
theorem B731963 : Blo 487790 731963 := bstep (se 1 (by rfl) ⟨548972, by rfl⟩ : syracuseStep 731963 = 1097945) B1097945
theorem B732023 : Blo 487790 732023 := bstep (se 1 (by rfl) ⟨549017, by rfl⟩ : syracuseStep 732023 = 1098035) B1098035
theorem B732047 : Blo 487790 732047 := bstep (se 1 (by rfl) ⟨549035, by rfl⟩ : syracuseStep 732047 = 1098071) B1098071
theorem B732089 : Blo 487790 732089 := bstep (se 2 (by rfl) ⟨274533, by rfl⟩ : syracuseStep 732089 = 549067) B549067
theorem B732167 : Blo 487790 732167 := bstep (se 1 (by rfl) ⟨549125, by rfl⟩ : syracuseStep 732167 = 1098251) B1098251
theorem B732203 : Blo 487790 732203 := bstep (se 1 (by rfl) ⟨549152, by rfl⟩ : syracuseStep 732203 = 1098305) B1098305
theorem B16067645 : Blo 487790 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B2796605 : Blo 487790 2796605 := bstep (se 3 (by rfl) ⟨524363, by rfl⟩ : syracuseStep 2796605 = 1048727) B1048727
theorem B732233 : Blo 487790 732233 := bstep (se 2 (by rfl) ⟨274587, by rfl⟩ : syracuseStep 732233 = 549175) B549175
theorem B732347 : Blo 487790 732347 := bstep (se 1 (by rfl) ⟨549260, by rfl⟩ : syracuseStep 732347 = 1098521) B1098521
theorem B732407 : Blo 487790 732407 := bstep (se 1 (by rfl) ⟨549305, by rfl⟩ : syracuseStep 732407 = 1098611) B1098611
theorem B732431 : Blo 487790 732431 := bstep (se 1 (by rfl) ⟨549323, by rfl⟩ : syracuseStep 732431 = 1098647) B1098647
theorem B732473 : Blo 487790 732473 := bstep (se 2 (by rfl) ⟨274677, by rfl⟩ : syracuseStep 732473 = 549355) B549355
theorem B732551 : Blo 487790 732551 := bstep (se 1 (by rfl) ⟨549413, by rfl⟩ : syracuseStep 732551 = 1098827) B1098827
theorem B929171 : Blo 487790 929171 := bstep (se 1 (by rfl) ⟨696878, by rfl⟩ : syracuseStep 929171 = 1393757) B1393757
theorem B732587 : Blo 487790 732587 := bstep (se 1 (by rfl) ⟨549440, by rfl⟩ : syracuseStep 732587 = 1098881) B1098881
theorem B699835 : Blo 487790 699835 := bstep (se 1 (by rfl) ⟨524876, by rfl⟩ : syracuseStep 699835 = 1049753) B1049753
theorem B732617 : Blo 487790 732617 := bstep (se 2 (by rfl) ⟨274731, by rfl⟩ : syracuseStep 732617 = 549463) B549463
theorem B929225 : Blo 487790 929225 := bstep (se 2 (by rfl) ⟨348459, by rfl⟩ : syracuseStep 929225 = 696919) B696919
theorem B929323 : Blo 487790 929323 := bstep (se 1 (by rfl) ⟨696992, by rfl⟩ : syracuseStep 929323 = 1393985) B1393985
theorem B732731 : Blo 487790 732731 := bstep (se 1 (by rfl) ⟨549548, by rfl⟩ : syracuseStep 732731 = 1099097) B1099097
theorem B3518029 : Blo 487790 3518029 := bstep (se 3 (by rfl) ⟨659630, by rfl⟩ : syracuseStep 3518029 = 1319261) B1319261
theorem B732791 : Blo 487790 732791 := bstep (se 1 (by rfl) ⟨549593, by rfl⟩ : syracuseStep 732791 = 1099187) B1099187
theorem B732815 : Blo 487790 732815 := bstep (se 1 (by rfl) ⟨549611, by rfl⟩ : syracuseStep 732815 = 1099223) B1099223
theorem B732857 : Blo 487790 732857 := bstep (se 2 (by rfl) ⟨274821, by rfl⟩ : syracuseStep 732857 = 549643) B549643
theorem B732935 : Blo 487790 732935 := bstep (se 1 (by rfl) ⟨549701, by rfl⟩ : syracuseStep 732935 = 1099403) B1099403
theorem B929551 : Blo 487790 929551 := bstep (se 1 (by rfl) ⟨697163, by rfl⟩ : syracuseStep 929551 = 1394327) B1394327
theorem B5353253 : Blo 487790 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B732971 : Blo 487790 732971 := bstep (se 1 (by rfl) ⟨549728, by rfl⟩ : syracuseStep 732971 = 1099457) B1099457
theorem B733001 : Blo 487790 733001 := bstep (se 2 (by rfl) ⟨274875, by rfl⟩ : syracuseStep 733001 = 549751) B549751
theorem B5582681 : Blo 487790 5582681 := bstep (se 2 (by rfl) ⟨2093505, by rfl⟩ : syracuseStep 5582681 = 4187011) B4187011
theorem B1650617 : Blo 487790 1650617 := bstep (se 2 (by rfl) ⟨618981, by rfl⟩ : syracuseStep 1650617 = 1237963) B1237963
theorem B733115 : Blo 487790 733115 := bstep (se 1 (by rfl) ⟨549836, by rfl⟩ : syracuseStep 733115 = 1099673) B1099673
theorem B733175 : Blo 487790 733175 := bstep (se 1 (by rfl) ⟨549881, by rfl⟩ : syracuseStep 733175 = 1099763) B1099763
theorem B733199 : Blo 487790 733199 := bstep (se 1 (by rfl) ⟨549899, by rfl⟩ : syracuseStep 733199 = 1099799) B1099799
theorem B733241 : Blo 487790 733241 := bstep (se 2 (by rfl) ⟨274965, by rfl⟩ : syracuseStep 733241 = 549931) B549931
theorem B733319 : Blo 487790 733319 := bstep (se 1 (by rfl) ⟨549989, by rfl⟩ : syracuseStep 733319 = 1099979) B1099979
theorem B1323155 : Blo 487790 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B733355 : Blo 487790 733355 := bstep (se 1 (by rfl) ⟨550016, by rfl⟩ : syracuseStep 733355 = 1100033) B1100033
theorem B733385 : Blo 487790 733385 := bstep (se 2 (by rfl) ⟨275019, by rfl⟩ : syracuseStep 733385 = 550039) B550039
theorem B504079 : Blo 487790 504079 := bstep (se 1 (by rfl) ⟨378059, by rfl⟩ : syracuseStep 504079 = 756119) B756119
theorem B995627 : Blo 487790 995627 := bstep (se 1 (by rfl) ⟨746720, by rfl⟩ : syracuseStep 995627 = 1493441) B1493441
theorem B733499 : Blo 487790 733499 := bstep (se 1 (by rfl) ⟨550124, by rfl⟩ : syracuseStep 733499 = 1100249) B1100249
theorem B733559 : Blo 487790 733559 := bstep (se 1 (by rfl) ⟨550169, by rfl⟩ : syracuseStep 733559 = 1100339) B1100339
theorem B733583 : Blo 487790 733583 := bstep (se 1 (by rfl) ⟨550187, by rfl⟩ : syracuseStep 733583 = 1100375) B1100375
theorem B733625 : Blo 487790 733625 := bstep (se 2 (by rfl) ⟨275109, by rfl⟩ : syracuseStep 733625 = 550219) B550219
theorem B733703 : Blo 487790 733703 := bstep (se 1 (by rfl) ⟨550277, by rfl⟩ : syracuseStep 733703 = 1100555) B1100555
theorem B1651211 : Blo 487790 1651211 := bstep (se 1 (by rfl) ⟨1238408, by rfl⟩ : syracuseStep 1651211 = 2476817) B2476817
theorem B733739 : Blo 487790 733739 := bstep (se 1 (by rfl) ⟨550304, by rfl⟩ : syracuseStep 733739 = 1100609) B1100609
theorem B733769 : Blo 487790 733769 := bstep (se 2 (by rfl) ⟨275163, by rfl⟩ : syracuseStep 733769 = 550327) B550327
theorem B1487479 : Blo 487790 1487479 := bstep (se 1 (by rfl) ⟨1115609, by rfl⟩ : syracuseStep 1487479 = 2231219) B2231219
theorem B1651319 : Blo 487790 1651319 := bstep (se 1 (by rfl) ⟨1238489, by rfl⟩ : syracuseStep 1651319 = 2476979) B2476979
theorem B733883 : Blo 487790 733883 := bstep (se 1 (by rfl) ⟨550412, by rfl⟩ : syracuseStep 733883 = 1100825) B1100825
theorem B733943 : Blo 487790 733943 := bstep (se 1 (by rfl) ⟨550457, by rfl⟩ : syracuseStep 733943 = 1100915) B1100915
theorem B733967 : Blo 487790 733967 := bstep (se 1 (by rfl) ⟨550475, by rfl⟩ : syracuseStep 733967 = 1100951) B1100951
theorem B734009 : Blo 487790 734009 := bstep (se 2 (by rfl) ⟨275253, by rfl⟩ : syracuseStep 734009 = 550507) B550507
theorem B3715955 : Blo 487790 3715955 := bstep (se 1 (by rfl) ⟨2786966, by rfl⟩ : syracuseStep 3715955 = 5573933) B5573933
theorem B734087 : Blo 487790 734087 := bstep (se 1 (by rfl) ⟨550565, by rfl⟩ : syracuseStep 734087 = 1101131) B1101131
theorem B734123 : Blo 487790 734123 := bstep (se 1 (by rfl) ⟨550592, by rfl⟩ : syracuseStep 734123 = 1101185) B1101185
theorem B734153 : Blo 487790 734153 := bstep (se 2 (by rfl) ⟨275307, by rfl⟩ : syracuseStep 734153 = 550615) B550615
theorem B1389611 : Blo 487790 1389611 := bstep (se 1 (by rfl) ⟨1042208, by rfl⟩ : syracuseStep 1389611 = 2084417) B2084417
theorem B734267 : Blo 487790 734267 := bstep (se 1 (by rfl) ⟨550700, by rfl⟩ : syracuseStep 734267 = 1101401) B1101401
theorem B734327 : Blo 487790 734327 := bstep (se 1 (by rfl) ⟨550745, by rfl⟩ : syracuseStep 734327 = 1101491) B1101491
theorem B734351 : Blo 487790 734351 := bstep (se 1 (by rfl) ⟨550763, by rfl⟩ : syracuseStep 734351 = 1101527) B1101527
theorem B734393 : Blo 487790 734393 := bstep (se 2 (by rfl) ⟨275397, by rfl⟩ : syracuseStep 734393 = 550795) B550795
theorem B1651913 : Blo 487790 1651913 := bstep (se 2 (by rfl) ⟨619467, by rfl⟩ : syracuseStep 1651913 = 1238935) B1238935
theorem B734471 : Blo 487790 734471 := bstep (se 1 (by rfl) ⟨550853, by rfl⟩ : syracuseStep 734471 = 1101707) B1101707
theorem B734507 : Blo 487790 734507 := bstep (se 1 (by rfl) ⟨550880, by rfl⟩ : syracuseStep 734507 = 1101761) B1101761
theorem B931115 : Blo 487790 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B734537 : Blo 487790 734537 := bstep (se 2 (by rfl) ⟨275451, by rfl⟩ : syracuseStep 734537 = 550903) B550903
theorem B20428163 : Blo 487790 20428163 := bstep (se 1 (by rfl) ⟨15321122, by rfl⟩ : syracuseStep 20428163 = 30642245) B30642245
theorem B2798995 : Blo 487790 2798995 := bstep (se 1 (by rfl) ⟨2099246, by rfl⟩ : syracuseStep 2798995 = 4198493) B4198493
theorem B734651 : Blo 487790 734651 := bstep (se 1 (by rfl) ⟨550988, by rfl⟩ : syracuseStep 734651 = 1101977) B1101977
theorem B734711 : Blo 487790 734711 := bstep (se 1 (by rfl) ⟨551033, by rfl⟩ : syracuseStep 734711 = 1102067) B1102067
theorem B734735 : Blo 487790 734735 := bstep (se 1 (by rfl) ⟨551051, by rfl⟩ : syracuseStep 734735 = 1102103) B1102103
theorem B734777 : Blo 487790 734777 := bstep (se 2 (by rfl) ⟨275541, by rfl⟩ : syracuseStep 734777 = 551083) B551083
theorem B9418315 : Blo 487790 9418315 := bstep (se 1 (by rfl) ⟨7063736, by rfl⟩ : syracuseStep 9418315 = 14127473) B14127473
theorem B734855 : Blo 487790 734855 := bstep (se 1 (by rfl) ⟨551141, by rfl⟩ : syracuseStep 734855 = 1102283) B1102283
theorem B734891 : Blo 487790 734891 := bstep (se 1 (by rfl) ⟨551168, by rfl⟩ : syracuseStep 734891 = 1102337) B1102337
theorem B734921 : Blo 487790 734921 := bstep (se 2 (by rfl) ⟨275595, by rfl⟩ : syracuseStep 734921 = 551191) B551191
theorem B735035 : Blo 487790 735035 := bstep (se 1 (by rfl) ⟨551276, by rfl⟩ : syracuseStep 735035 = 1102553) B1102553
theorem B2471795 : Blo 487790 2471795 := bstep (se 1 (by rfl) ⟨1853846, by rfl⟩ : syracuseStep 2471795 = 3707693) B3707693
theorem B735095 : Blo 487790 735095 := bstep (se 1 (by rfl) ⟨551321, by rfl⟩ : syracuseStep 735095 = 1102643) B1102643
theorem B1652615 : Blo 487790 1652615 := bstep (se 1 (by rfl) ⟨1239461, by rfl⟩ : syracuseStep 1652615 = 2478923) B2478923
theorem B735119 : Blo 487790 735119 := bstep (se 1 (by rfl) ⟨551339, by rfl⟩ : syracuseStep 735119 = 1102679) B1102679
theorem B1488793 : Blo 487790 1488793 := bstep (se 2 (by rfl) ⟨558297, by rfl⟩ : syracuseStep 1488793 = 1116595) B1116595
theorem B735161 : Blo 487790 735161 := bstep (se 2 (by rfl) ⟨275685, by rfl⟩ : syracuseStep 735161 = 551371) B551371
theorem B735239 : Blo 487790 735239 := bstep (se 1 (by rfl) ⟨551429, by rfl⟩ : syracuseStep 735239 = 1102859) B1102859
theorem B3127319 : Blo 487790 3127319 := bstep (se 1 (by rfl) ⟨2345489, by rfl⟩ : syracuseStep 3127319 = 4690979) B4690979
theorem B735275 : Blo 487790 735275 := bstep (se 1 (by rfl) ⟨551456, by rfl⟩ : syracuseStep 735275 = 1102913) B1102913
theorem B735305 : Blo 487790 735305 := bstep (se 2 (by rfl) ⟨275739, by rfl⟩ : syracuseStep 735305 = 551479) B551479
theorem B1325143 : Blo 487790 1325143 := bstep (se 1 (by rfl) ⟨993857, by rfl⟩ : syracuseStep 1325143 = 1987715) B1987715
theorem B735419 : Blo 487790 735419 := bstep (se 1 (by rfl) ⟨551564, by rfl⟩ : syracuseStep 735419 = 1103129) B1103129
theorem B735479 : Blo 487790 735479 := bstep (se 1 (by rfl) ⟨551609, by rfl⟩ : syracuseStep 735479 = 1103219) B1103219
theorem B1652993 : Blo 487790 1652993 := bstep (se 2 (by rfl) ⟨619872, by rfl⟩ : syracuseStep 1652993 = 1239745) B1239745
theorem B735503 : Blo 487790 735503 := bstep (se 1 (by rfl) ⟨551627, by rfl⟩ : syracuseStep 735503 = 1103255) B1103255
theorem B735545 : Blo 487790 735545 := bstep (se 2 (by rfl) ⟨275829, by rfl⟩ : syracuseStep 735545 = 551659) B551659
theorem B2472281 : Blo 487790 2472281 := bstep (se 2 (by rfl) ⟨927105, by rfl⟩ : syracuseStep 2472281 = 1854211) B1854211
theorem B735623 : Blo 487790 735623 := bstep (se 1 (by rfl) ⟨551717, by rfl⟩ : syracuseStep 735623 = 1103435) B1103435
theorem B1915271 : Blo 487790 1915271 := bstep (se 1 (by rfl) ⟨1436453, by rfl⟩ : syracuseStep 1915271 = 2872907) B2872907
theorem B1063315 : Blo 487790 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B735659 : Blo 487790 735659 := bstep (se 1 (by rfl) ⟨551744, by rfl⟩ : syracuseStep 735659 = 1103489) B1103489
theorem B735689 : Blo 487790 735689 := bstep (se 2 (by rfl) ⟨275883, by rfl⟩ : syracuseStep 735689 = 551767) B551767
theorem B735803 : Blo 487790 735803 := bstep (se 1 (by rfl) ⟨551852, by rfl⟩ : syracuseStep 735803 = 1103705) B1103705
theorem B735863 : Blo 487790 735863 := bstep (se 1 (by rfl) ⟨551897, by rfl⟩ : syracuseStep 735863 = 1103795) B1103795
theorem B735887 : Blo 487790 735887 := bstep (se 1 (by rfl) ⟨551915, by rfl⟩ : syracuseStep 735887 = 1103831) B1103831
theorem B1391251 : Blo 487790 1391251 := bstep (se 1 (by rfl) ⟨1043438, by rfl⟩ : syracuseStep 1391251 = 2086877) B2086877
theorem B735929 : Blo 487790 735929 := bstep (se 2 (by rfl) ⟨275973, by rfl⟩ : syracuseStep 735929 = 551947) B551947
theorem B736007 : Blo 487790 736007 := bstep (se 1 (by rfl) ⟨552005, by rfl⟩ : syracuseStep 736007 = 1104011) B1104011
theorem B736043 : Blo 487790 736043 := bstep (se 1 (by rfl) ⟨552032, by rfl⟩ : syracuseStep 736043 = 1104065) B1104065
theorem B736073 : Blo 487790 736073 := bstep (se 2 (by rfl) ⟨276027, by rfl⟩ : syracuseStep 736073 = 552055) B552055
theorem B2177945 : Blo 487790 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B736187 : Blo 487790 736187 := bstep (se 1 (by rfl) ⟨552140, by rfl⟩ : syracuseStep 736187 = 1104281) B1104281
theorem B932809 : Blo 487790 932809 := bstep (se 2 (by rfl) ⟨349803, by rfl⟩ : syracuseStep 932809 = 699607) B699607
theorem B736247 : Blo 487790 736247 := bstep (se 1 (by rfl) ⟨552185, by rfl⟩ : syracuseStep 736247 = 1104371) B1104371
theorem B736271 : Blo 487790 736271 := bstep (se 1 (by rfl) ⟨552203, by rfl⟩ : syracuseStep 736271 = 1104407) B1104407
theorem B1653803 : Blo 487790 1653803 := bstep (se 1 (by rfl) ⟨1240352, by rfl⟩ : syracuseStep 1653803 = 2480705) B2480705
theorem B736313 : Blo 487790 736313 := bstep (se 2 (by rfl) ⟨276117, by rfl⟩ : syracuseStep 736313 = 552235) B552235
theorem B2800727 : Blo 487790 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B736391 : Blo 487790 736391 := bstep (se 1 (by rfl) ⟨552293, by rfl⟩ : syracuseStep 736391 = 1104587) B1104587
theorem B736427 : Blo 487790 736427 := bstep (se 1 (by rfl) ⟨552320, by rfl⟩ : syracuseStep 736427 = 1104641) B1104641
theorem B736457 : Blo 487790 736457 := bstep (se 2 (by rfl) ⟨276171, by rfl⟩ : syracuseStep 736457 = 552343) B552343
theorem B736571 : Blo 487790 736571 := bstep (se 1 (by rfl) ⟨552428, by rfl⟩ : syracuseStep 736571 = 1104857) B1104857
theorem B736631 : Blo 487790 736631 := bstep (se 1 (by rfl) ⟨552473, by rfl⟩ : syracuseStep 736631 = 1104947) B1104947
theorem B736655 : Blo 487790 736655 := bstep (se 1 (by rfl) ⟨552491, by rfl⟩ : syracuseStep 736655 = 1104983) B1104983
theorem B736697 : Blo 487790 736697 := bstep (se 2 (by rfl) ⟨276261, by rfl⟩ : syracuseStep 736697 = 552523) B552523
theorem B736775 : Blo 487790 736775 := bstep (se 1 (by rfl) ⟨552581, by rfl⟩ : syracuseStep 736775 = 1105163) B1105163
theorem B736811 : Blo 487790 736811 := bstep (se 1 (by rfl) ⟨552608, by rfl⟩ : syracuseStep 736811 = 1105217) B1105217
theorem B736841 : Blo 487790 736841 := bstep (se 2 (by rfl) ⟨276315, by rfl⟩ : syracuseStep 736841 = 552631) B552631
theorem B7061093 : Blo 487790 7061093 := bstep (se 4 (by rfl) ⟨661977, by rfl⟩ : syracuseStep 7061093 = 1323955) B1323955
theorem B2637485 : Blo 487790 2637485 := bstep (se 3 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 2637485 = 989057) B989057
theorem B736955 : Blo 487790 736955 := bstep (se 1 (by rfl) ⟨552716, by rfl⟩ : syracuseStep 736955 = 1105433) B1105433
theorem B3587777 : Blo 487790 3587777 := bstep (se 2 (by rfl) ⟨1345416, by rfl⟩ : syracuseStep 3587777 = 2690833) B2690833
theorem B737015 : Blo 487790 737015 := bstep (se 1 (by rfl) ⟨552761, by rfl⟩ : syracuseStep 737015 = 1105523) B1105523
theorem B737039 : Blo 487790 737039 := bstep (se 1 (by rfl) ⟨552779, by rfl⟩ : syracuseStep 737039 = 1105559) B1105559
theorem B737081 : Blo 487790 737081 := bstep (se 2 (by rfl) ⟨276405, by rfl⟩ : syracuseStep 737081 = 552811) B552811
theorem B1097531 : Blo 487790 1097531 := bstep (se 1 (by rfl) ⟨823148, by rfl⟩ : syracuseStep 1097531 = 1646297) B1646297
theorem B737159 : Blo 487790 737159 := bstep (se 1 (by rfl) ⟨552869, by rfl⟩ : syracuseStep 737159 = 1105739) B1105739
theorem B737195 : Blo 487790 737195 := bstep (se 1 (by rfl) ⟨552896, by rfl⟩ : syracuseStep 737195 = 1105793) B1105793
theorem B1097657 : Blo 487790 1097657 := bstep (se 2 (by rfl) ⟨411621, by rfl⟩ : syracuseStep 1097657 = 823243) B823243
theorem B737225 : Blo 487790 737225 := bstep (se 2 (by rfl) ⟨276459, by rfl⟩ : syracuseStep 737225 = 552919) B552919
theorem B2211851 : Blo 487790 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B737339 : Blo 487790 737339 := bstep (se 1 (by rfl) ⟨553004, by rfl⟩ : syracuseStep 737339 = 1106009) B1106009
theorem B737399 : Blo 487790 737399 := bstep (se 1 (by rfl) ⟨553049, by rfl⟩ : syracuseStep 737399 = 1106099) B1106099
theorem B737423 : Blo 487790 737423 := bstep (se 1 (by rfl) ⟨553067, by rfl⟩ : syracuseStep 737423 = 1106135) B1106135
theorem B737465 : Blo 487790 737465 := bstep (se 2 (by rfl) ⟨276549, by rfl⟩ : syracuseStep 737465 = 553099) B553099
theorem B737543 : Blo 487790 737543 := bstep (se 1 (by rfl) ⟨553157, by rfl⟩ : syracuseStep 737543 = 1106315) B1106315
theorem B1097999 : Blo 487790 1097999 := bstep (se 1 (by rfl) ⟨823499, by rfl⟩ : syracuseStep 1097999 = 1646999) B1646999
theorem B1098017 : Blo 487790 1098017 := bstep (se 2 (by rfl) ⟨411756, by rfl⟩ : syracuseStep 1098017 = 823513) B823513
theorem B737579 : Blo 487790 737579 := bstep (se 1 (by rfl) ⟨553184, by rfl⟩ : syracuseStep 737579 = 1106369) B1106369
theorem B1655099 : Blo 487790 1655099 := bstep (se 1 (by rfl) ⟨1241324, by rfl⟩ : syracuseStep 1655099 = 2482649) B2482649
theorem B737609 : Blo 487790 737609 := bstep (se 2 (by rfl) ⟨276603, by rfl⟩ : syracuseStep 737609 = 553207) B553207
theorem B1392983 : Blo 487790 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B2474387 : Blo 487790 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B1098359 : Blo 487790 1098359 := bstep (se 1 (by rfl) ⟨823769, by rfl⟩ : syracuseStep 1098359 = 1647539) B1647539
theorem B1655585 : Blo 487790 1655585 := bstep (se 2 (by rfl) ⟨620844, by rfl⟩ : syracuseStep 1655585 = 1241689) B1241689
theorem B1098539 : Blo 487790 1098539 := bstep (se 1 (by rfl) ⟨823904, by rfl⟩ : syracuseStep 1098539 = 1647809) B1647809
theorem B3130265 : Blo 487790 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B1098899 : Blo 487790 1098899 := bstep (se 1 (by rfl) ⟨824174, by rfl⟩ : syracuseStep 1098899 = 1648349) B1648349
theorem B2376877 : Blo 487790 2376877 := bstep (se 3 (by rfl) ⟨445664, by rfl⟩ : syracuseStep 2376877 = 891329) B891329
theorem B1098953 : Blo 487790 1098953 := bstep (se 2 (by rfl) ⟨412107, by rfl⟩ : syracuseStep 1098953 = 824215) B824215
theorem B1656179 : Blo 487790 1656179 := bstep (se 1 (by rfl) ⟨1242134, by rfl⟩ : syracuseStep 1656179 = 2484269) B2484269
theorem B5031695 : Blo 487790 5031695 := bstep (se 1 (by rfl) ⟨3773771, by rfl⟩ : syracuseStep 5031695 = 7547543) B7547543
theorem B1099655 : Blo 487790 1099655 := bstep (se 1 (by rfl) ⟨824741, by rfl⟩ : syracuseStep 1099655 = 1649483) B1649483
theorem B1394567 : Blo 487790 1394567 := bstep (se 1 (by rfl) ⟨1045925, by rfl⟩ : syracuseStep 1394567 = 2091851) B2091851
theorem B1099835 : Blo 487790 1099835 := bstep (se 1 (by rfl) ⟨824876, by rfl⟩ : syracuseStep 1099835 = 1649753) B1649753
theorem B1099961 : Blo 487790 1099961 := bstep (se 2 (by rfl) ⟨412485, by rfl⟩ : syracuseStep 1099961 = 824971) B824971
theorem B1853711 : Blo 487790 1853711 := bstep (se 1 (by rfl) ⟨1390283, by rfl⟩ : syracuseStep 1853711 = 2780567) B2780567
theorem B3361169 : Blo 487790 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B1100303 : Blo 487790 1100303 := bstep (se 1 (by rfl) ⟨825227, by rfl⟩ : syracuseStep 1100303 = 1650455) B1650455
theorem B1395215 : Blo 487790 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B1100321 : Blo 487790 1100321 := bstep (se 2 (by rfl) ⟨412620, by rfl⟩ : syracuseStep 1100321 = 825241) B825241
theorem B1526647 : Blo 487790 1526647 := bstep (se 1 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 1526647 = 2289971) B2289971
theorem B1100663 : Blo 487790 1100663 := bstep (se 1 (by rfl) ⟨825497, by rfl⟩ : syracuseStep 1100663 = 1650995) B1650995
theorem B5753861 : Blo 487790 5753861 := bstep (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) B1078849
theorem B1100843 : Blo 487790 1100843 := bstep (se 1 (by rfl) ⟨825632, by rfl⟩ : syracuseStep 1100843 = 1651265) B1651265
theorem B1101203 : Blo 487790 1101203 := bstep (se 1 (by rfl) ⟨825902, by rfl⟩ : syracuseStep 1101203 = 1651805) B1651805
theorem B2477465 : Blo 487790 2477465 := bstep (se 2 (by rfl) ⟨929049, by rfl⟩ : syracuseStep 2477465 = 1858099) B1858099
theorem B1101257 : Blo 487790 1101257 := bstep (se 2 (by rfl) ⟨412971, by rfl⟩ : syracuseStep 1101257 = 825943) B825943
theorem B2346583 : Blo 487790 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B6704819 : Blo 487790 6704819 := bstep (se 1 (by rfl) ⟨5028614, by rfl⟩ : syracuseStep 6704819 = 10057229) B10057229
theorem B1494827 : Blo 487790 1494827 := bstep (se 1 (by rfl) ⟨1121120, by rfl⟩ : syracuseStep 1494827 = 2242241) B2242241
theorem B4542257 : Blo 487790 4542257 := bstep (se 2 (by rfl) ⟨1703346, by rfl⟩ : syracuseStep 4542257 = 3406693) B3406693
theorem B1658771 : Blo 487790 1658771 := bstep (se 1 (by rfl) ⟨1244078, by rfl⟩ : syracuseStep 1658771 = 2488157) B2488157
theorem B1396855 : Blo 487790 1396855 := bstep (se 1 (by rfl) ⟨1047641, by rfl⟩ : syracuseStep 1396855 = 2095283) B2095283
theorem B1101959 : Blo 487790 1101959 := bstep (se 1 (by rfl) ⟨826469, by rfl⟩ : syracuseStep 1101959 = 1652939) B1652939
theorem B2085101 : Blo 487790 2085101 := bstep (se 3 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 2085101 = 781913) B781913
theorem B1102139 : Blo 487790 1102139 := bstep (se 1 (by rfl) ⟨826604, by rfl⟩ : syracuseStep 1102139 = 1653209) B1653209
theorem B1986875 : Blo 487790 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B1102265 : Blo 487790 1102265 := bstep (se 2 (by rfl) ⟨413349, by rfl⟩ : syracuseStep 1102265 = 826699) B826699
theorem B1102607 : Blo 487790 1102607 := bstep (se 1 (by rfl) ⟨826955, by rfl⟩ : syracuseStep 1102607 = 1653911) B1653911
theorem B1004321 : Blo 487790 1004321 := bstep (se 2 (by rfl) ⟨376620, by rfl⟩ : syracuseStep 1004321 = 753241) B753241
theorem B1102625 : Blo 487790 1102625 := bstep (se 2 (by rfl) ⟨413484, by rfl⟩ : syracuseStep 1102625 = 826969) B826969
theorem B1987361 : Blo 487790 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B1102967 : Blo 487790 1102967 := bstep (se 1 (by rfl) ⟨827225, by rfl⟩ : syracuseStep 1102967 = 1654451) B1654451
theorem B1987703 : Blo 487790 1987703 := bstep (se 1 (by rfl) ⟨1490777, by rfl⟩ : syracuseStep 1987703 = 2981555) B2981555
theorem B4084937 : Blo 487790 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B1103147 : Blo 487790 1103147 := bstep (se 1 (by rfl) ⟨827360, by rfl⟩ : syracuseStep 1103147 = 1654721) B1654721
theorem B1398131 : Blo 487790 1398131 := bstep (se 1 (by rfl) ⟨1048598, by rfl⟩ : syracuseStep 1398131 = 2097197) B2097197
theorem B1856915 : Blo 487790 1856915 := bstep (se 1 (by rfl) ⟨1392686, by rfl⟩ : syracuseStep 1856915 = 2785373) B2785373
theorem B4183595 : Blo 487790 4183595 := bstep (se 1 (by rfl) ⟨3137696, by rfl⟩ : syracuseStep 4183595 = 6275393) B6275393
theorem B1398359 : Blo 487790 1398359 := bstep (se 1 (by rfl) ⟨1048769, by rfl⟩ : syracuseStep 1398359 = 2097539) B2097539
theorem B2086519 : Blo 487790 2086519 := bstep (se 1 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 2086519 = 3129779) B3129779
theorem B1103507 : Blo 487790 1103507 := bstep (se 1 (by rfl) ⟨827630, by rfl⟩ : syracuseStep 1103507 = 1655261) B1655261
theorem B1103561 : Blo 487790 1103561 := bstep (se 2 (by rfl) ⟨413835, by rfl⟩ : syracuseStep 1103561 = 827671) B827671
theorem B7919333 : Blo 487790 7919333 := bstep (se 4 (by rfl) ⟨742437, by rfl⟩ : syracuseStep 7919333 = 1484875) B1484875
theorem B1234835 : Blo 487790 1234835 := bstep (se 1 (by rfl) ⟨926126, by rfl⟩ : syracuseStep 1234835 = 1852253) B1852253
theorem B2480057 : Blo 487790 2480057 := bstep (se 2 (by rfl) ⟨930021, by rfl⟩ : syracuseStep 2480057 = 1860043) B1860043
theorem B1136825 : Blo 487790 1136825 := bstep (se 2 (by rfl) ⟨426309, by rfl⟩ : syracuseStep 1136825 = 852619) B852619
theorem B1104263 : Blo 487790 1104263 := bstep (se 1 (by rfl) ⟨828197, by rfl⟩ : syracuseStep 1104263 = 1656395) B1656395
theorem B2120203 : Blo 487790 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B743995 : Blo 487790 743995 := bstep (se 1 (by rfl) ⟨557996, by rfl⟩ : syracuseStep 743995 = 1115993) B1115993
theorem B1104443 : Blo 487790 1104443 := bstep (se 1 (by rfl) ⟨828332, by rfl⟩ : syracuseStep 1104443 = 1656665) B1656665
theorem B1104569 : Blo 487790 1104569 := bstep (se 2 (by rfl) ⟨414213, by rfl⟩ : syracuseStep 1104569 = 828427) B828427
theorem B5299019 : Blo 487790 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B1235969 : Blo 487790 1235969 := bstep (se 2 (by rfl) ⟨463488, by rfl⟩ : syracuseStep 1235969 = 926977) B926977
theorem B2382851 : Blo 487790 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B1858571 : Blo 487790 1858571 := bstep (se 1 (by rfl) ⟨1393928, by rfl⟩ : syracuseStep 1858571 = 2787857) B2787857
theorem B1104911 : Blo 487790 1104911 := bstep (se 1 (by rfl) ⟨828683, by rfl⟩ : syracuseStep 1104911 = 1657367) B1657367
theorem B1760285 : Blo 487790 1760285 := bstep (se 3 (by rfl) ⟨330053, by rfl⟩ : syracuseStep 1760285 = 660107) B660107
theorem B1104929 : Blo 487790 1104929 := bstep (se 2 (by rfl) ⟨414348, by rfl⟩ : syracuseStep 1104929 = 828697) B828697
theorem B1399943 : Blo 487790 1399943 := bstep (se 1 (by rfl) ⟨1049957, by rfl⟩ : syracuseStep 1399943 = 2099915) B2099915
theorem B2481353 : Blo 487790 2481353 := bstep (se 2 (by rfl) ⟨930507, by rfl⟩ : syracuseStep 2481353 = 1861015) B1861015
theorem B1400125 : Blo 487790 1400125 := bstep (se 3 (by rfl) ⟨262523, by rfl⟩ : syracuseStep 1400125 = 525047) B525047
theorem B1236343 : Blo 487790 1236343 := bstep (se 1 (by rfl) ⟨927257, by rfl⟩ : syracuseStep 1236343 = 1854515) B1854515
theorem B1105271 : Blo 487790 1105271 := bstep (se 1 (by rfl) ⟨828953, by rfl⟩ : syracuseStep 1105271 = 1657907) B1657907
theorem B13360589 : Blo 487790 13360589 := bstep (se 3 (by rfl) ⟨2505110, by rfl⟩ : syracuseStep 13360589 = 5010221) B5010221
theorem B1105451 : Blo 487790 1105451 := bstep (se 1 (by rfl) ⟨829088, by rfl⟩ : syracuseStep 1105451 = 1658177) B1658177
theorem B1236779 : Blo 487790 1236779 := bstep (se 1 (by rfl) ⟨927584, by rfl⟩ : syracuseStep 1236779 = 1855169) B1855169
theorem B1105811 : Blo 487790 1105811 := bstep (se 1 (by rfl) ⟨829358, by rfl⟩ : syracuseStep 1105811 = 1658717) B1658717
theorem B1761209 : Blo 487790 1761209 := bstep (se 2 (by rfl) ⟨660453, by rfl⟩ : syracuseStep 1761209 = 1320907) B1320907
theorem B1105865 : Blo 487790 1105865 := bstep (se 2 (by rfl) ⟨414699, by rfl⟩ : syracuseStep 1105865 = 829399) B829399
theorem B548923 : Blo 487790 548923 := bstep (se 1 (by rfl) ⟨411692, by rfl⟩ : syracuseStep 548923 = 823385) B823385
theorem B11297009 : Blo 487790 11297009 := bstep (se 2 (by rfl) ⟨4236378, by rfl⟩ : syracuseStep 11297009 = 8472757) B8472757
theorem B549391 : Blo 487790 549391 := bstep (se 1 (by rfl) ⟨412043, by rfl⟩ : syracuseStep 549391 = 824087) B824087
theorem B1237619 : Blo 487790 1237619 := bstep (se 1 (by rfl) ⟨928214, by rfl⟩ : syracuseStep 1237619 = 1856429) B1856429
theorem B1237639 : Blo 487790 1237639 := bstep (se 1 (by rfl) ⟨928229, by rfl⟩ : syracuseStep 1237639 = 1856459) B1856459
theorem B1237913 : Blo 487790 1237913 := bstep (se 2 (by rfl) ⟨464217, by rfl⟩ : syracuseStep 1237913 = 928435) B928435
theorem B549895 : Blo 487790 549895 := bstep (se 1 (by rfl) ⟨412421, by rfl⟩ : syracuseStep 549895 = 824843) B824843
theorem B910369 : Blo 487790 910369 := bstep (se 2 (by rfl) ⟨341388, by rfl⟩ : syracuseStep 910369 = 682777) B682777
theorem B1238075 : Blo 487790 1238075 := bstep (se 1 (by rfl) ⟨928556, by rfl⟩ : syracuseStep 1238075 = 1857113) B1857113
theorem B550075 : Blo 487790 550075 := bstep (se 1 (by rfl) ⟨412556, by rfl⟩ : syracuseStep 550075 = 825113) B825113
theorem B1238287 : Blo 487790 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B2778401 : Blo 487790 2778401 := bstep (se 2 (by rfl) ⟨1041900, by rfl⟩ : syracuseStep 2778401 = 2083801) B2083801
theorem B1697057 : Blo 487790 1697057 := bstep (se 2 (by rfl) ⟨636396, by rfl⟩ : syracuseStep 1697057 = 1272793) B1272793
theorem B16934429 : Blo 487790 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B1238561 : Blo 487790 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B1042055 : Blo 487790 1042055 := bstep (se 1 (by rfl) ⟨781541, by rfl⟩ : syracuseStep 1042055 = 1563083) B1563083
theorem B550543 : Blo 487790 550543 := bstep (se 1 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 550543 = 825815) B825815
theorem B6678551 : Blo 487790 6678551 := bstep (se 1 (by rfl) ⟨5008913, by rfl⟩ : syracuseStep 6678551 = 10017827) B10017827
theorem B1042465 : Blo 487790 1042465 := bstep (se 2 (by rfl) ⟨390924, by rfl⟩ : syracuseStep 1042465 = 781849) B781849
theorem B551047 : Blo 487790 551047 := bstep (se 1 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 551047 = 826571) B826571
theorem B8349965 : Blo 487790 8349965 := bstep (se 3 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 8349965 = 3131237) B3131237
theorem B1042721 : Blo 487790 1042721 := bstep (se 2 (by rfl) ⟨391020, by rfl⟩ : syracuseStep 1042721 = 782041) B782041
theorem B551227 : Blo 487790 551227 := bstep (se 1 (by rfl) ⟨413420, by rfl⟩ : syracuseStep 551227 = 826841) B826841
theorem B1042807 : Blo 487790 1042807 := bstep (se 1 (by rfl) ⟨782105, by rfl⟩ : syracuseStep 1042807 = 1564211) B1564211
theorem B4712849 : Blo 487790 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B1239563 : Blo 487790 1239563 := bstep (se 1 (by rfl) ⟨929672, by rfl⟩ : syracuseStep 1239563 = 1859345) B1859345
theorem B682553 : Blo 487790 682553 := bstep (se 2 (by rfl) ⟨255957, by rfl⟩ : syracuseStep 682553 = 511915) B511915
theorem B12544631 : Blo 487790 12544631 := bstep (se 1 (by rfl) ⟨9408473, by rfl⟩ : syracuseStep 12544631 = 18816947) B18816947
theorem B5565185 : Blo 487790 5565185 := bstep (se 2 (by rfl) ⟨2086944, by rfl⟩ : syracuseStep 5565185 = 4173889) B4173889
theorem B551695 : Blo 487790 551695 := bstep (se 1 (by rfl) ⟨413771, by rfl⟩ : syracuseStep 551695 = 827543) B827543
theorem B1174331 : Blo 487790 1174331 := bstep (se 1 (by rfl) ⟨880748, by rfl⟩ : syracuseStep 1174331 = 1761497) B1761497
theorem B1862459 : Blo 487790 1862459 := bstep (se 1 (by rfl) ⟨1396844, by rfl⟩ : syracuseStep 1862459 = 2793689) B2793689
theorem B3140441 : Blo 487790 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B3140669 : Blo 487790 3140669 := bstep (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) B1177751
theorem B1240211 : Blo 487790 1240211 := bstep (se 1 (by rfl) ⟨930158, by rfl⟩ : syracuseStep 1240211 = 1860317) B1860317
theorem B552199 : Blo 487790 552199 := bstep (se 1 (by rfl) ⟨414149, by rfl⟩ : syracuseStep 552199 = 828299) B828299
theorem B1862945 : Blo 487790 1862945 := bstep (se 2 (by rfl) ⟨698604, by rfl⟩ : syracuseStep 1862945 = 1397209) B1397209
theorem B617863 : Blo 487790 617863 := bstep (se 1 (by rfl) ⟨463397, by rfl⟩ : syracuseStep 617863 = 926795) B926795
theorem B1240505 : Blo 487790 1240505 := bstep (se 2 (by rfl) ⟨465189, by rfl⟩ : syracuseStep 1240505 = 930379) B930379
theorem B552379 : Blo 487790 552379 := bstep (se 1 (by rfl) ⟨414284, by rfl⟩ : syracuseStep 552379 = 828569) B828569
theorem B1568285 : Blo 487790 1568285 := bstep (se 3 (by rfl) ⟨294053, by rfl⟩ : syracuseStep 1568285 = 588107) B588107
theorem B3731021 : Blo 487790 3731021 := bstep (se 3 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 3731021 = 1399133) B1399133
theorem B2420417 : Blo 487790 2420417 := bstep (se 2 (by rfl) ⟨907656, by rfl⟩ : syracuseStep 2420417 = 1815313) B1815313
theorem B1437385 : Blo 487790 1437385 := bstep (se 2 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 1437385 = 1078039) B1078039
theorem B618283 : Blo 487790 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B4452185 : Blo 487790 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B552847 : Blo 487790 552847 := bstep (se 1 (by rfl) ⟨414635, by rfl⟩ : syracuseStep 552847 = 829271) B829271
theorem B2977681 : Blo 487790 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B618511 : Blo 487790 618511 := bstep (se 1 (by rfl) ⟨463883, by rfl⟩ : syracuseStep 618511 = 927767) B927767
theorem B2256925 : Blo 487790 2256925 := bstep (se 3 (by rfl) ⟨423173, by rfl⟩ : syracuseStep 2256925 = 846347) B846347
theorem B1241203 : Blo 487790 1241203 := bstep (se 1 (by rfl) ⟨930902, by rfl⟩ : syracuseStep 1241203 = 1861805) B1861805
theorem B1765577 : Blo 487790 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B1863917 : Blo 487790 1863917 := bstep (se 3 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 1863917 = 698969) B698969
theorem B1241345 : Blo 487790 1241345 := bstep (se 2 (by rfl) ⟨465504, by rfl⟩ : syracuseStep 1241345 = 931009) B931009
theorem B2781499 : Blo 487790 2781499 := bstep (se 1 (by rfl) ⟨2086124, by rfl⟩ : syracuseStep 2781499 = 4172249) B4172249
theorem B487815 : Blo 487790 487815 := bstep (se 1 (by rfl) ⟨365861, by rfl⟩ : syracuseStep 487815 = 731723) B731723
theorem B487823 : Blo 487790 487823 := bstep (se 1 (by rfl) ⟨365867, by rfl⟩ : syracuseStep 487823 = 731735) B731735
theorem B487867 : Blo 487790 487867 := bstep (se 1 (by rfl) ⟨365900, by rfl⟩ : syracuseStep 487867 = 731801) B731801
theorem B487943 : Blo 487790 487943 := bstep (se 1 (by rfl) ⟨365957, by rfl⟩ : syracuseStep 487943 = 731915) B731915
theorem B487951 : Blo 487790 487951 := bstep (se 1 (by rfl) ⟨365963, by rfl⟩ : syracuseStep 487951 = 731927) B731927
theorem B1864235 : Blo 487790 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B487995 : Blo 487790 487995 := bstep (se 1 (by rfl) ⟨365996, by rfl⟩ : syracuseStep 487995 = 731993) B731993
theorem B488071 : Blo 487790 488071 := bstep (se 1 (by rfl) ⟨366053, by rfl⟩ : syracuseStep 488071 = 732107) B732107
theorem B488079 : Blo 487790 488079 := bstep (se 1 (by rfl) ⟨366059, by rfl⟩ : syracuseStep 488079 = 732119) B732119
theorem B488123 : Blo 487790 488123 := bstep (se 1 (by rfl) ⟨366092, by rfl⟩ : syracuseStep 488123 = 732185) B732185
theorem B1241801 : Blo 487790 1241801 := bstep (se 2 (by rfl) ⟨465675, by rfl⟩ : syracuseStep 1241801 = 931351) B931351
theorem B619255 : Blo 487790 619255 := bstep (se 1 (by rfl) ⟨464441, by rfl⟩ : syracuseStep 619255 = 928883) B928883
theorem B9401093 : Blo 487790 9401093 := bstep (se 4 (by rfl) ⟨881352, by rfl⟩ : syracuseStep 9401093 = 1762705) B1762705
theorem B488199 : Blo 487790 488199 := bstep (se 1 (by rfl) ⟨366149, by rfl⟩ : syracuseStep 488199 = 732299) B732299
theorem B488207 : Blo 487790 488207 := bstep (se 1 (by rfl) ⟨366155, by rfl⟩ : syracuseStep 488207 = 732311) B732311
theorem B3961649 : Blo 487790 3961649 := bstep (se 2 (by rfl) ⟨1485618, by rfl⟩ : syracuseStep 3961649 = 2971237) B2971237
theorem B488251 : Blo 487790 488251 := bstep (se 1 (by rfl) ⟨366188, by rfl⟩ : syracuseStep 488251 = 732377) B732377
theorem B488327 : Blo 487790 488327 := bstep (se 1 (by rfl) ⟨366245, by rfl⟩ : syracuseStep 488327 = 732491) B732491
theorem B488335 : Blo 487790 488335 := bstep (se 1 (by rfl) ⟨366251, by rfl⟩ : syracuseStep 488335 = 732503) B732503
theorem B2487185 : Blo 487790 2487185 := bstep (se 2 (by rfl) ⟨932694, by rfl⟩ : syracuseStep 2487185 = 1865389) B1865389
theorem B1340345 : Blo 487790 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B488379 : Blo 487790 488379 := bstep (se 1 (by rfl) ⟨366284, by rfl⟩ : syracuseStep 488379 = 732569) B732569
theorem B488455 : Blo 487790 488455 := bstep (se 1 (by rfl) ⟨366341, by rfl⟩ : syracuseStep 488455 = 732683) B732683
theorem B488463 : Blo 487790 488463 := bstep (se 1 (by rfl) ⟨366347, by rfl⟩ : syracuseStep 488463 = 732695) B732695
theorem B1242155 : Blo 487790 1242155 := bstep (se 1 (by rfl) ⟨931616, by rfl⟩ : syracuseStep 1242155 = 1863233) B1863233
theorem B488507 : Blo 487790 488507 := bstep (se 1 (by rfl) ⟨366380, by rfl⟩ : syracuseStep 488507 = 732761) B732761
theorem B619579 : Blo 487790 619579 := bstep (se 1 (by rfl) ⟨464684, by rfl⟩ : syracuseStep 619579 = 929369) B929369
theorem B488583 : Blo 487790 488583 := bstep (se 1 (by rfl) ⟨366437, by rfl⟩ : syracuseStep 488583 = 732875) B732875
theorem B488591 : Blo 487790 488591 := bstep (se 1 (by rfl) ⟨366443, by rfl⟩ : syracuseStep 488591 = 732887) B732887
theorem B488635 : Blo 487790 488635 := bstep (se 1 (by rfl) ⟨366476, by rfl⟩ : syracuseStep 488635 = 732953) B732953
theorem B488711 : Blo 487790 488711 := bstep (se 1 (by rfl) ⟨366533, by rfl⟩ : syracuseStep 488711 = 733067) B733067
theorem B488719 : Blo 487790 488719 := bstep (se 1 (by rfl) ⟨366539, by rfl⟩ : syracuseStep 488719 = 733079) B733079
theorem B1242383 : Blo 487790 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B488763 : Blo 487790 488763 := bstep (se 1 (by rfl) ⟨366572, by rfl⟩ : syracuseStep 488763 = 733145) B733145
theorem B488839 : Blo 487790 488839 := bstep (se 1 (by rfl) ⟨366629, by rfl⟩ : syracuseStep 488839 = 733259) B733259
theorem B488847 : Blo 487790 488847 := bstep (se 1 (by rfl) ⟨366635, by rfl⟩ : syracuseStep 488847 = 733271) B733271
theorem B488891 : Blo 487790 488891 := bstep (se 1 (by rfl) ⟨366668, by rfl⟩ : syracuseStep 488891 = 733337) B733337
theorem B488967 : Blo 487790 488967 := bstep (se 1 (by rfl) ⟨366725, by rfl⟩ : syracuseStep 488967 = 733451) B733451
theorem B40138253 : Blo 487790 40138253 := bstep (se 3 (by rfl) ⟨7525922, by rfl⟩ : syracuseStep 40138253 = 15051845) B15051845
theorem B488975 : Blo 487790 488975 := bstep (se 1 (by rfl) ⟨366731, by rfl⟩ : syracuseStep 488975 = 733463) B733463
theorem B620075 : Blo 487790 620075 := bstep (se 1 (by rfl) ⟨465056, by rfl⟩ : syracuseStep 620075 = 930113) B930113
theorem B489019 : Blo 487790 489019 := bstep (se 1 (by rfl) ⟨366764, by rfl⟩ : syracuseStep 489019 = 733529) B733529
theorem B5568101 : Blo 487790 5568101 := bstep (se 4 (by rfl) ⟨522009, by rfl⟩ : syracuseStep 5568101 = 1044019) B1044019
theorem B489095 : Blo 487790 489095 := bstep (se 1 (by rfl) ⟨366821, by rfl⟩ : syracuseStep 489095 = 733643) B733643
theorem B489103 : Blo 487790 489103 := bstep (se 1 (by rfl) ⟨366827, by rfl⟩ : syracuseStep 489103 = 733655) B733655
theorem B489147 : Blo 487790 489147 := bstep (se 1 (by rfl) ⟨366860, by rfl⟩ : syracuseStep 489147 = 733721) B733721
theorem B1701577 : Blo 487790 1701577 := bstep (se 2 (by rfl) ⟨638091, by rfl⟩ : syracuseStep 1701577 = 1276183) B1276183
theorem B2782957 : Blo 487790 2782957 := bstep (se 3 (by rfl) ⟨521804, by rfl⟩ : syracuseStep 2782957 = 1043609) B1043609
theorem B489223 : Blo 487790 489223 := bstep (se 1 (by rfl) ⟨366917, by rfl⟩ : syracuseStep 489223 = 733835) B733835
theorem B489231 : Blo 487790 489231 := bstep (se 1 (by rfl) ⟨366923, by rfl⟩ : syracuseStep 489231 = 733847) B733847
theorem B489275 : Blo 487790 489275 := bstep (se 1 (by rfl) ⟨366956, by rfl⟩ : syracuseStep 489275 = 733913) B733913
theorem B3143539 : Blo 487790 3143539 := bstep (se 1 (by rfl) ⟨2357654, by rfl⟩ : syracuseStep 3143539 = 4715309) B4715309
theorem B489351 : Blo 487790 489351 := bstep (se 1 (by rfl) ⟨367013, by rfl⟩ : syracuseStep 489351 = 734027) B734027
theorem B489359 : Blo 487790 489359 := bstep (se 1 (by rfl) ⟨367019, by rfl⟩ : syracuseStep 489359 = 734039) B734039
theorem B1570745 : Blo 487790 1570745 := bstep (se 2 (by rfl) ⟨589029, by rfl⟩ : syracuseStep 1570745 = 1178059) B1178059
theorem B489403 : Blo 487790 489403 := bstep (se 1 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 489403 = 734105) B734105
theorem B3733451 : Blo 487790 3733451 := bstep (se 1 (by rfl) ⟨2800088, by rfl⟩ : syracuseStep 3733451 = 5600177) B5600177
theorem B2389981 : Blo 487790 2389981 := bstep (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) B896243
theorem B489479 : Blo 487790 489479 := bstep (se 1 (by rfl) ⟨367109, by rfl⟩ : syracuseStep 489479 = 734219) B734219
theorem B620551 : Blo 487790 620551 := bstep (se 1 (by rfl) ⟨465413, by rfl⟩ : syracuseStep 620551 = 930827) B930827
theorem B1243147 : Blo 487790 1243147 := bstep (se 1 (by rfl) ⟨932360, by rfl⟩ : syracuseStep 1243147 = 1864721) B1864721
theorem B489487 : Blo 487790 489487 := bstep (se 1 (by rfl) ⟨367115, by rfl⟩ : syracuseStep 489487 = 734231) B734231
theorem B784399 : Blo 487790 784399 := bstep (se 1 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 784399 = 1176599) B1176599
theorem B489531 : Blo 487790 489531 := bstep (se 1 (by rfl) ⟨367148, by rfl⟩ : syracuseStep 489531 = 734297) B734297
theorem B4192343 : Blo 487790 4192343 := bstep (se 1 (by rfl) ⟨3144257, by rfl⟩ : syracuseStep 4192343 = 6288515) B6288515
theorem B489607 : Blo 487790 489607 := bstep (se 1 (by rfl) ⟨367205, by rfl⟩ : syracuseStep 489607 = 734411) B734411
theorem B489615 : Blo 487790 489615 := bstep (se 1 (by rfl) ⟨367211, by rfl⟩ : syracuseStep 489615 = 734423) B734423
theorem B1243289 : Blo 487790 1243289 := bstep (se 2 (by rfl) ⟨466233, by rfl⟩ : syracuseStep 1243289 = 932467) B932467
theorem B489659 : Blo 487790 489659 := bstep (se 1 (by rfl) ⟨367244, by rfl⟩ : syracuseStep 489659 = 734489) B734489
theorem B489735 : Blo 487790 489735 := bstep (se 1 (by rfl) ⟨367301, by rfl⟩ : syracuseStep 489735 = 734603) B734603
theorem B489743 : Blo 487790 489743 := bstep (se 1 (by rfl) ⟨367307, by rfl⟩ : syracuseStep 489743 = 734615) B734615
theorem B784655 : Blo 487790 784655 := bstep (se 1 (by rfl) ⟨588491, by rfl⟩ : syracuseStep 784655 = 1176983) B1176983
theorem B489787 : Blo 487790 489787 := bstep (se 1 (by rfl) ⟨367340, by rfl⟩ : syracuseStep 489787 = 734681) B734681
theorem B1243451 : Blo 487790 1243451 := bstep (se 1 (by rfl) ⟨932588, by rfl⟩ : syracuseStep 1243451 = 1865177) B1865177
theorem B489863 : Blo 487790 489863 := bstep (se 1 (by rfl) ⟨367397, by rfl⟩ : syracuseStep 489863 = 734795) B734795
theorem B489871 : Blo 487790 489871 := bstep (se 1 (by rfl) ⟨367403, by rfl⟩ : syracuseStep 489871 = 734807) B734807
theorem B489915 : Blo 487790 489915 := bstep (se 1 (by rfl) ⟨367436, by rfl⟩ : syracuseStep 489915 = 734873) B734873
theorem B4192721 : Blo 487790 4192721 := bstep (se 2 (by rfl) ⟨1572270, by rfl⟩ : syracuseStep 4192721 = 3144541) B3144541
theorem B621047 : Blo 487790 621047 := bstep (se 1 (by rfl) ⟨465785, by rfl⟩ : syracuseStep 621047 = 931571) B931571
theorem B489991 : Blo 487790 489991 := bstep (se 1 (by rfl) ⟨367493, by rfl⟩ : syracuseStep 489991 = 734987) B734987
theorem B489999 : Blo 487790 489999 := bstep (se 1 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 489999 = 734999) B734999
theorem B1178155 : Blo 487790 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B490043 : Blo 487790 490043 := bstep (se 1 (by rfl) ⟨367532, by rfl⟩ : syracuseStep 490043 = 735065) B735065
theorem B490119 : Blo 487790 490119 := bstep (se 1 (by rfl) ⟨367589, by rfl⟩ : syracuseStep 490119 = 735179) B735179
theorem B490127 : Blo 487790 490127 := bstep (se 1 (by rfl) ⟨367595, by rfl⟩ : syracuseStep 490127 = 735191) B735191
theorem B621199 : Blo 487790 621199 := bstep (se 1 (by rfl) ⟨465899, by rfl⟩ : syracuseStep 621199 = 931799) B931799
theorem B1243795 : Blo 487790 1243795 := bstep (se 1 (by rfl) ⟨932846, by rfl⟩ : syracuseStep 1243795 = 1865693) B1865693
theorem B490171 : Blo 487790 490171 := bstep (se 1 (by rfl) ⟨367628, by rfl⟩ : syracuseStep 490171 = 735257) B735257
theorem B490247 : Blo 487790 490247 := bstep (se 1 (by rfl) ⟨367685, by rfl⟩ : syracuseStep 490247 = 735371) B735371
theorem B490255 : Blo 487790 490255 := bstep (se 1 (by rfl) ⟨367691, by rfl⟩ : syracuseStep 490255 = 735383) B735383
theorem B1243937 : Blo 487790 1243937 := bstep (se 2 (by rfl) ⟨466476, by rfl⟩ : syracuseStep 1243937 = 932953) B932953
theorem B490299 : Blo 487790 490299 := bstep (se 1 (by rfl) ⟨367724, by rfl⟩ : syracuseStep 490299 = 735449) B735449
theorem B621371 : Blo 487790 621371 := bstep (se 1 (by rfl) ⟨466028, by rfl⟩ : syracuseStep 621371 = 932057) B932057
theorem B490375 : Blo 487790 490375 := bstep (se 1 (by rfl) ⟨367781, by rfl⟩ : syracuseStep 490375 = 735563) B735563
theorem B1571719 : Blo 487790 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B490383 : Blo 487790 490383 := bstep (se 1 (by rfl) ⟨367787, by rfl⟩ : syracuseStep 490383 = 735575) B735575
theorem B490427 : Blo 487790 490427 := bstep (se 1 (by rfl) ⟨367820, by rfl⟩ : syracuseStep 490427 = 735641) B735641
theorem B2489291 : Blo 487790 2489291 := bstep (se 1 (by rfl) ⟨1866968, by rfl⟩ : syracuseStep 2489291 = 3733937) B3733937
theorem B490503 : Blo 487790 490503 := bstep (se 1 (by rfl) ⟨367877, by rfl⟩ : syracuseStep 490503 = 735755) B735755
theorem B1506319 : Blo 487790 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B490511 : Blo 487790 490511 := bstep (se 1 (by rfl) ⟨367883, by rfl⟩ : syracuseStep 490511 = 735767) B735767
theorem B5569559 : Blo 487790 5569559 := bstep (se 1 (by rfl) ⟨4177169, by rfl⟩ : syracuseStep 5569559 = 8354339) B8354339
theorem B490555 : Blo 487790 490555 := bstep (se 1 (by rfl) ⟨367916, by rfl⟩ : syracuseStep 490555 = 735833) B735833
theorem B490631 : Blo 487790 490631 := bstep (se 1 (by rfl) ⟨367973, by rfl⟩ : syracuseStep 490631 = 735947) B735947
theorem B490639 : Blo 487790 490639 := bstep (se 1 (by rfl) ⟨367979, by rfl⟩ : syracuseStep 490639 = 735959) B735959
theorem B490683 : Blo 487790 490683 := bstep (se 1 (by rfl) ⟨368012, by rfl⟩ : syracuseStep 490683 = 736025) B736025
theorem B490759 : Blo 487790 490759 := bstep (se 1 (by rfl) ⟨368069, by rfl⟩ : syracuseStep 490759 = 736139) B736139
theorem B490767 : Blo 487790 490767 := bstep (se 1 (by rfl) ⟨368075, by rfl⟩ : syracuseStep 490767 = 736151) B736151
theorem B2489615 : Blo 487790 2489615 := bstep (se 1 (by rfl) ⟨1867211, by rfl⟩ : syracuseStep 2489615 = 3734423) B3734423
theorem B490811 : Blo 487790 490811 := bstep (se 1 (by rfl) ⟨368108, by rfl⟩ : syracuseStep 490811 = 736217) B736217
theorem B785783 : Blo 487790 785783 := bstep (se 1 (by rfl) ⟨589337, by rfl⟩ : syracuseStep 785783 = 1178675) B1178675
theorem B490887 : Blo 487790 490887 := bstep (se 1 (by rfl) ⟨368165, by rfl⟩ : syracuseStep 490887 = 736331) B736331
theorem B490895 : Blo 487790 490895 := bstep (se 1 (by rfl) ⟨368171, by rfl⟩ : syracuseStep 490895 = 736343) B736343
theorem B490939 : Blo 487790 490939 := bstep (se 1 (by rfl) ⟨368204, by rfl⟩ : syracuseStep 490939 = 736409) B736409
theorem B523783 : Blo 487790 523783 := bstep (se 1 (by rfl) ⟨392837, by rfl⟩ : syracuseStep 523783 = 785675) B785675
theorem B491015 : Blo 487790 491015 := bstep (se 1 (by rfl) ⟨368261, by rfl⟩ : syracuseStep 491015 = 736523) B736523
theorem B491023 : Blo 487790 491023 := bstep (se 1 (by rfl) ⟨368267, by rfl⟩ : syracuseStep 491023 = 736535) B736535
theorem B491067 : Blo 487790 491067 := bstep (se 1 (by rfl) ⟨368300, by rfl⟩ : syracuseStep 491067 = 736601) B736601
theorem B491143 : Blo 487790 491143 := bstep (se 1 (by rfl) ⟨368357, by rfl⟩ : syracuseStep 491143 = 736715) B736715
theorem B491151 : Blo 487790 491151 := bstep (se 1 (by rfl) ⟨368363, by rfl⟩ : syracuseStep 491151 = 736727) B736727
theorem B1179289 : Blo 487790 1179289 := bstep (se 2 (by rfl) ⟨442233, by rfl⟩ : syracuseStep 1179289 = 884467) B884467
theorem B2784941 : Blo 487790 2784941 := bstep (se 3 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 2784941 = 1044353) B1044353
theorem B491195 : Blo 487790 491195 := bstep (se 1 (by rfl) ⟨368396, by rfl⟩ : syracuseStep 491195 = 736793) B736793
theorem B491271 : Blo 487790 491271 := bstep (se 1 (by rfl) ⟨368453, by rfl⟩ : syracuseStep 491271 = 736907) B736907
theorem B622343 : Blo 487790 622343 := bstep (se 1 (by rfl) ⟨466757, by rfl⟩ : syracuseStep 622343 = 933515) B933515
theorem B491279 : Blo 487790 491279 := bstep (se 1 (by rfl) ⟨368459, by rfl⟩ : syracuseStep 491279 = 736919) B736919
theorem B884539 : Blo 487790 884539 := bstep (se 1 (by rfl) ⟨663404, by rfl⟩ : syracuseStep 884539 = 1326809) B1326809
theorem B491323 : Blo 487790 491323 := bstep (se 1 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 491323 = 736985) B736985
theorem B786295 : Blo 487790 786295 := bstep (se 1 (by rfl) ⟨589721, by rfl⟩ : syracuseStep 786295 = 1179443) B1179443
theorem B491399 : Blo 487790 491399 := bstep (se 1 (by rfl) ⟨368549, by rfl⟩ : syracuseStep 491399 = 737099) B737099
theorem B491407 : Blo 487790 491407 := bstep (se 1 (by rfl) ⟨368555, by rfl⟩ : syracuseStep 491407 = 737111) B737111
theorem B491451 : Blo 487790 491451 := bstep (se 1 (by rfl) ⟨368588, by rfl⟩ : syracuseStep 491451 = 737177) B737177
theorem B5898269 : Blo 487790 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B491559 : Blo 487790 491559 := bstep (se 1 (by rfl) ⟨368669, by rfl⟩ : syracuseStep 491559 = 737339) B737339
theorem B491599 : Blo 487790 491599 := bstep (se 1 (by rfl) ⟨368699, by rfl⟩ : syracuseStep 491599 = 737399) B737399
theorem B491615 : Blo 487790 491615 := bstep (se 1 (by rfl) ⟨368711, by rfl⟩ : syracuseStep 491615 = 737423) B737423
theorem B491643 : Blo 487790 491643 := bstep (se 1 (by rfl) ⟨368732, by rfl⟩ : syracuseStep 491643 = 737465) B737465
theorem B491695 : Blo 487790 491695 := bstep (se 1 (by rfl) ⟨368771, by rfl⟩ : syracuseStep 491695 = 737543) B737543
theorem B491719 : Blo 487790 491719 := bstep (se 1 (by rfl) ⟨368789, by rfl⟩ : syracuseStep 491719 = 737579) B737579
theorem B491739 : Blo 487790 491739 := bstep (se 1 (by rfl) ⟨368804, by rfl⟩ : syracuseStep 491739 = 737609) B737609
theorem B590375 : Blo 487790 590375 := bstep (se 1 (by rfl) ⟨442781, by rfl⟩ : syracuseStep 590375 = 885563) B885563
theorem B7078499 : Blo 487790 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B787115 : Blo 487790 787115 := bstep (se 1 (by rfl) ⟨590336, by rfl⟩ : syracuseStep 787115 = 1180673) B1180673
theorem B787295 : Blo 487790 787295 := bstep (se 1 (by rfl) ⟨590471, by rfl⟩ : syracuseStep 787295 = 1180943) B1180943
theorem B1115063 : Blo 487790 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B3835907 : Blo 487790 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B3574253 : Blo 487790 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B3771089 : Blo 487790 3771089 := bstep (se 2 (by rfl) ⟨1414158, by rfl⟩ : syracuseStep 3771089 = 2828317) B2828317
theorem B2362115 : Blo 487790 2362115 := bstep (se 1 (by rfl) ⟨1771586, by rfl⟩ : syracuseStep 2362115 = 3543173) B3543173
theorem B3345299 : Blo 487790 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B3313021 : Blo 487790 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B2723291 : Blo 487790 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B2789063 : Blo 487790 2789063 := bstep (se 1 (by rfl) ⟨2091797, by rfl⟩ : syracuseStep 2789063 = 4183595) B4183595
theorem B4034285 : Blo 487790 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B5279555 : Blo 487790 5279555 := bstep (se 1 (by rfl) ⟨3959666, by rfl⟩ : syracuseStep 5279555 = 7919333) B7919333
theorem B2035529 : Blo 487790 2035529 := bstep (se 2 (by rfl) ⟨763323, by rfl⟩ : syracuseStep 2035529 = 1526647) B1526647
theorem B823223 : Blo 487790 823223 := bstep (se 1 (by rfl) ⟨617417, by rfl⟩ : syracuseStep 823223 = 1234835) B1234835
theorem B757883 : Blo 487790 757883 := bstep (se 1 (by rfl) ⟨568412, by rfl⟩ : syracuseStep 757883 = 1136825) B1136825
theorem B823817 : Blo 487790 823817 := bstep (se 2 (by rfl) ⟨308931, by rfl⟩ : syracuseStep 823817 = 617863) B617863
theorem B3150359 : Blo 487790 3150359 := bstep (se 1 (by rfl) ⟨2362769, by rfl⟩ : syracuseStep 3150359 = 4725539) B4725539
theorem B823979 : Blo 487790 823979 := bstep (se 1 (by rfl) ⟨617984, by rfl⟩ : syracuseStep 823979 = 1235969) B1235969
theorem B9900755 : Blo 487790 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B4690705 : Blo 487790 4690705 := bstep (se 2 (by rfl) ⟨1759014, by rfl⟩ : syracuseStep 4690705 = 3518029) B3518029
theorem B14160689 : Blo 487790 14160689 := bstep (se 2 (by rfl) ⟨5310258, by rfl⟩ : syracuseStep 14160689 = 10620517) B10620517
theorem B1119251 : Blo 487790 1119251 := bstep (se 1 (by rfl) ⟨839438, by rfl⟩ : syracuseStep 1119251 = 1678877) B1678877
theorem B3150899 : Blo 487790 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B824377 : Blo 487790 824377 := bstep (se 2 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 824377 = 618283) B618283
theorem B3970241 : Blo 487790 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B824519 : Blo 487790 824519 := bstep (se 1 (by rfl) ⟨618389, by rfl⟩ : syracuseStep 824519 = 1236779) B1236779
theorem B824681 : Blo 487790 824681 := bstep (se 2 (by rfl) ⟨309255, by rfl⟩ : syracuseStep 824681 = 618511) B618511
theorem B8033701 : Blo 487790 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B5969371 : Blo 487790 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B4855301 : Blo 487790 4855301 := bstep (se 4 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 4855301 = 910369) B910369
theorem B4462141 : Blo 487790 4462141 := bstep (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) B1673303
theorem B10753685 : Blo 487790 10753685 := bstep (se 6 (by rfl) ⟨252039, by rfl⟩ : syracuseStep 10753685 = 504079) B504079
theorem B825079 : Blo 487790 825079 := bstep (se 1 (by rfl) ⟨618809, by rfl⟩ : syracuseStep 825079 = 1237619) B1237619
theorem B3708665 : Blo 487790 3708665 := bstep (se 2 (by rfl) ⟨1390749, by rfl⟩ : syracuseStep 3708665 = 2781499) B2781499
theorem B825275 : Blo 487790 825275 := bstep (se 1 (by rfl) ⟨618956, by rfl⟩ : syracuseStep 825275 = 1237913) B1237913
theorem B825383 : Blo 487790 825383 := bstep (se 1 (by rfl) ⟨619037, by rfl⟩ : syracuseStep 825383 = 1238075) B1238075
theorem B825673 : Blo 487790 825673 := bstep (se 2 (by rfl) ⟨309627, by rfl⟩ : syracuseStep 825673 = 619255) B619255
theorem B825707 : Blo 487790 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B694703 : Blo 487790 694703 := bstep (se 1 (by rfl) ⟨521027, by rfl⟩ : syracuseStep 694703 = 1042055) B1042055
theorem B826105 : Blo 487790 826105 := bstep (se 2 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 826105 = 619579) B619579
theorem B695147 : Blo 487790 695147 := bstep (se 1 (by rfl) ⟨521360, by rfl⟩ : syracuseStep 695147 = 1042721) B1042721
theorem B826375 : Blo 487790 826375 := bstep (se 1 (by rfl) ⟨619781, by rfl⟩ : syracuseStep 826375 = 1239563) B1239563
theorem B8363087 : Blo 487790 8363087 := bstep (se 1 (by rfl) ⟨6272315, by rfl⟩ : syracuseStep 8363087 = 12544631) B12544631
theorem B3710123 : Blo 487790 3710123 := bstep (se 1 (by rfl) ⟨2782592, by rfl⟩ : syracuseStep 3710123 = 5565185) B5565185
theorem B826807 : Blo 487790 826807 := bstep (se 1 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 826807 = 1240211) B1240211
theorem B12557753 : Blo 487790 12557753 := bstep (se 2 (by rfl) ⟨4709157, by rfl⟩ : syracuseStep 12557753 = 9418315) B9418315
theorem B2268769 : Blo 487790 2268769 := bstep (se 2 (by rfl) ⟨850788, by rfl⟩ : syracuseStep 2268769 = 1701577) B1701577
theorem B827003 : Blo 487790 827003 := bstep (se 1 (by rfl) ⟨620252, by rfl⟩ : syracuseStep 827003 = 1240505) B1240505
theorem B3710609 : Blo 487790 3710609 := bstep (se 2 (by rfl) ⟨1391478, by rfl⟩ : syracuseStep 3710609 = 2782957) B2782957
theorem B1613611 : Blo 487790 1613611 := bstep (se 1 (by rfl) ⟨1210208, by rfl⟩ : syracuseStep 1613611 = 2420417) B2420417
theorem B3186641 : Blo 487790 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B827401 : Blo 487790 827401 := bstep (se 2 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 827401 = 620551) B620551
theorem B827563 : Blo 487790 827563 := bstep (se 1 (by rfl) ⟨620672, by rfl⟩ : syracuseStep 827563 = 1241345) B1241345
theorem B663751 : Blo 487790 663751 := bstep (se 1 (by rfl) ⟨497813, by rfl⟩ : syracuseStep 663751 = 995627) B995627
theorem B827867 : Blo 487790 827867 := bstep (se 1 (by rfl) ⟨620900, by rfl⟩ : syracuseStep 827867 = 1241801) B1241801
theorem B6267395 : Blo 487790 6267395 := bstep (se 1 (by rfl) ⟨4700546, by rfl⟩ : syracuseStep 6267395 = 9401093) B9401093
theorem B1417753 : Blo 487790 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B2826937 : Blo 487790 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B926407 : Blo 487790 926407 := bstep (se 1 (by rfl) ⟨694805, by rfl⟩ : syracuseStep 926407 = 1389611) B1389611
theorem B828103 : Blo 487790 828103 := bstep (se 1 (by rfl) ⟨621077, by rfl⟩ : syracuseStep 828103 = 1242155) B1242155
theorem B991993 : Blo 487790 991993 := bstep (se 2 (by rfl) ⟨371997, by rfl⟩ : syracuseStep 991993 = 743995) B743995
theorem B828265 : Blo 487790 828265 := bstep (se 2 (by rfl) ⟨310599, by rfl⟩ : syracuseStep 828265 = 621199) B621199
theorem B3712067 : Blo 487790 3712067 := bstep (se 1 (by rfl) ⟨2784050, by rfl⟩ : syracuseStep 3712067 = 5568101) B5568101
theorem B1647863 : Blo 487790 1647863 := bstep (se 1 (by rfl) ⟨1235897, by rfl⟩ : syracuseStep 1647863 = 2471795) B2471795
theorem B2794895 : Blo 487790 2794895 := bstep (se 1 (by rfl) ⟨2096171, by rfl⟩ : syracuseStep 2794895 = 4192343) B4192343
theorem B828859 : Blo 487790 828859 := bstep (se 1 (by rfl) ⟨621644, by rfl⟩ : syracuseStep 828859 = 1243289) B1243289
theorem B828967 : Blo 487790 828967 := bstep (se 1 (by rfl) ⟨621725, by rfl⟩ : syracuseStep 828967 = 1243451) B1243451
theorem B1648187 : Blo 487790 1648187 := bstep (se 1 (by rfl) ⟨1236140, by rfl⟩ : syracuseStep 1648187 = 2472281) B2472281
theorem B2795147 : Blo 487790 2795147 := bstep (se 1 (by rfl) ⟨2096360, by rfl⟩ : syracuseStep 2795147 = 4192721) B4192721
theorem B1648457 : Blo 487790 1648457 := bstep (se 2 (by rfl) ⟨618171, by rfl⟩ : syracuseStep 1648457 = 1236343) B1236343
theorem B829291 : Blo 487790 829291 := bstep (se 1 (by rfl) ⟨621968, by rfl⟩ : syracuseStep 829291 = 1243937) B1243937
theorem B1451963 : Blo 487790 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B698377 : Blo 487790 698377 := bstep (se 2 (by rfl) ⟨261891, by rfl⟩ : syracuseStep 698377 = 523783) B523783
theorem B3713039 : Blo 487790 3713039 := bstep (se 1 (by rfl) ⟨2784779, by rfl⟩ : syracuseStep 3713039 = 5569559) B5569559
theorem B11872493 : Blo 487790 11872493 := bstep (se 3 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 11872493 = 4452185) B4452185
theorem B731687 : Blo 487790 731687 := bstep (se 1 (by rfl) ⟨548765, by rfl⟩ : syracuseStep 731687 = 1097531) B1097531
theorem B731771 : Blo 487790 731771 := bstep (se 1 (by rfl) ⟨548828, by rfl⟩ : syracuseStep 731771 = 1097657) B1097657
theorem B731897 : Blo 487790 731897 := bstep (se 2 (by rfl) ⟨274461, by rfl⟩ : syracuseStep 731897 = 548923) B548923
theorem B731999 : Blo 487790 731999 := bstep (se 1 (by rfl) ⟨548999, by rfl⟩ : syracuseStep 731999 = 1097999) B1097999
theorem B732011 : Blo 487790 732011 := bstep (se 1 (by rfl) ⟨549008, by rfl⟩ : syracuseStep 732011 = 1098017) B1098017
theorem B928655 : Blo 487790 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B1649591 : Blo 487790 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B732239 : Blo 487790 732239 := bstep (se 1 (by rfl) ⟨549179, by rfl⟩ : syracuseStep 732239 = 1098359) B1098359
theorem B732359 : Blo 487790 732359 := bstep (se 1 (by rfl) ⟨549269, by rfl⟩ : syracuseStep 732359 = 1098539) B1098539
theorem B30125357 : Blo 487790 30125357 := bstep (se 3 (by rfl) ⟨5648504, by rfl⟩ : syracuseStep 30125357 = 11297009) B11297009
theorem B732521 : Blo 487790 732521 := bstep (se 2 (by rfl) ⟨274695, by rfl⟩ : syracuseStep 732521 = 549391) B549391
theorem B732599 : Blo 487790 732599 := bstep (se 1 (by rfl) ⟨549449, by rfl⟩ : syracuseStep 732599 = 1098899) B1098899
theorem B732635 : Blo 487790 732635 := bstep (se 1 (by rfl) ⟨549476, by rfl⟩ : syracuseStep 732635 = 1098953) B1098953
theorem B1650185 : Blo 487790 1650185 := bstep (se 2 (by rfl) ⟨618819, by rfl⟩ : syracuseStep 1650185 = 1237639) B1237639
theorem B699943 : Blo 487790 699943 := bstep (se 1 (by rfl) ⟨524957, by rfl⟩ : syracuseStep 699943 = 1049915) B1049915
theorem B1486433 : Blo 487790 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B2797355 : Blo 487790 2797355 := bstep (se 1 (by rfl) ⟨2098016, by rfl⟩ : syracuseStep 2797355 = 4196033) B4196033
theorem B3354463 : Blo 487790 3354463 := bstep (se 1 (by rfl) ⟨2515847, by rfl⟩ : syracuseStep 3354463 = 5031695) B5031695
theorem B733103 : Blo 487790 733103 := bstep (se 1 (by rfl) ⟨549827, by rfl⟩ : syracuseStep 733103 = 1099655) B1099655
theorem B929711 : Blo 487790 929711 := bstep (se 1 (by rfl) ⟨697283, by rfl⟩ : syracuseStep 929711 = 1394567) B1394567
theorem B733193 : Blo 487790 733193 := bstep (se 2 (by rfl) ⟨274947, by rfl⟩ : syracuseStep 733193 = 549895) B549895
theorem B733223 : Blo 487790 733223 := bstep (se 1 (by rfl) ⟨549917, by rfl⟩ : syracuseStep 733223 = 1099835) B1099835
theorem B733307 : Blo 487790 733307 := bstep (se 1 (by rfl) ⟨549980, by rfl⟩ : syracuseStep 733307 = 1099961) B1099961
theorem B733433 : Blo 487790 733433 := bstep (se 2 (by rfl) ⟨275037, by rfl⟩ : syracuseStep 733433 = 550075) B550075
theorem B2240779 : Blo 487790 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B733535 : Blo 487790 733535 := bstep (se 1 (by rfl) ⟨550151, by rfl⟩ : syracuseStep 733535 = 1100303) B1100303
theorem B930143 : Blo 487790 930143 := bstep (se 1 (by rfl) ⟨697607, by rfl⟩ : syracuseStep 930143 = 1395215) B1395215
theorem B1651049 : Blo 487790 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B733547 : Blo 487790 733547 := bstep (se 1 (by rfl) ⟨550160, by rfl⟩ : syracuseStep 733547 = 1100321) B1100321
theorem B733775 : Blo 487790 733775 := bstep (se 1 (by rfl) ⟨550331, by rfl⟩ : syracuseStep 733775 = 1100663) B1100663
theorem B733895 : Blo 487790 733895 := bstep (se 1 (by rfl) ⟨550421, by rfl⟩ : syracuseStep 733895 = 1100843) B1100843
theorem B15938309 : Blo 487790 15938309 := bstep (se 4 (by rfl) ⟨1494216, by rfl⟩ : syracuseStep 15938309 = 2988433) B2988433
theorem B734057 : Blo 487790 734057 := bstep (se 2 (by rfl) ⟨275271, by rfl⟩ : syracuseStep 734057 = 550543) B550543
theorem B734135 : Blo 487790 734135 := bstep (se 1 (by rfl) ⟨550601, by rfl⟩ : syracuseStep 734135 = 1101203) B1101203
theorem B1651643 : Blo 487790 1651643 := bstep (se 1 (by rfl) ⟨1238732, by rfl⟩ : syracuseStep 1651643 = 2477465) B2477465
theorem B734171 : Blo 487790 734171 := bstep (se 1 (by rfl) ⟨550628, by rfl⟩ : syracuseStep 734171 = 1101257) B1101257
theorem B1881145 : Blo 487790 1881145 := bstep (se 2 (by rfl) ⟨705429, by rfl⟩ : syracuseStep 1881145 = 1410859) B1410859
theorem B4469879 : Blo 487790 4469879 := bstep (se 1 (by rfl) ⟨3352409, by rfl⟩ : syracuseStep 4469879 = 6704819) B6704819
theorem B996551 : Blo 487790 996551 := bstep (se 1 (by rfl) ⟨747413, by rfl⟩ : syracuseStep 996551 = 1494827) B1494827
theorem B6337739 : Blo 487790 6337739 := bstep (se 1 (by rfl) ⟨4753304, by rfl⟩ : syracuseStep 6337739 = 9506609) B9506609
theorem B3716441 : Blo 487790 3716441 := bstep (se 2 (by rfl) ⟨1393665, by rfl⟩ : syracuseStep 3716441 = 2787331) B2787331
theorem B1389953 : Blo 487790 1389953 := bstep (se 2 (by rfl) ⟨521232, by rfl⟩ : syracuseStep 1389953 = 1042465) B1042465
theorem B734639 : Blo 487790 734639 := bstep (se 1 (by rfl) ⟨550979, by rfl⟩ : syracuseStep 734639 = 1101959) B1101959
theorem B1390067 : Blo 487790 1390067 := bstep (se 1 (by rfl) ⟨1042550, by rfl⟩ : syracuseStep 1390067 = 2085101) B2085101
theorem B734729 : Blo 487790 734729 := bstep (se 2 (by rfl) ⟨275523, by rfl⟩ : syracuseStep 734729 = 551047) B551047
theorem B734759 : Blo 487790 734759 := bstep (se 1 (by rfl) ⟨551069, by rfl⟩ : syracuseStep 734759 = 1102139) B1102139
theorem B1324583 : Blo 487790 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B734843 : Blo 487790 734843 := bstep (se 1 (by rfl) ⟨551132, by rfl⟩ : syracuseStep 734843 = 1102265) B1102265
theorem B734969 : Blo 487790 734969 := bstep (se 2 (by rfl) ⟨275613, by rfl⟩ : syracuseStep 734969 = 551227) B551227
theorem B1390409 : Blo 487790 1390409 := bstep (se 2 (by rfl) ⟨521403, by rfl⟩ : syracuseStep 1390409 = 1042807) B1042807
theorem B735071 : Blo 487790 735071 := bstep (se 1 (by rfl) ⟨551303, by rfl⟩ : syracuseStep 735071 = 1102607) B1102607
theorem B3192671 : Blo 487790 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B669547 : Blo 487790 669547 := bstep (se 1 (by rfl) ⟨502160, by rfl⟩ : syracuseStep 669547 = 1004321) B1004321
theorem B735083 : Blo 487790 735083 := bstep (se 1 (by rfl) ⟨551312, by rfl⟩ : syracuseStep 735083 = 1102625) B1102625
theorem B1324907 : Blo 487790 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B2799521 : Blo 487790 2799521 := bstep (se 2 (by rfl) ⟨1049820, by rfl⟩ : syracuseStep 2799521 = 2099641) B2099641
theorem B735311 : Blo 487790 735311 := bstep (se 1 (by rfl) ⟨551483, by rfl⟩ : syracuseStep 735311 = 1102967) B1102967
theorem B1325135 : Blo 487790 1325135 := bstep (se 1 (by rfl) ⟨993851, by rfl⟩ : syracuseStep 1325135 = 1987703) B1987703
theorem B735431 : Blo 487790 735431 := bstep (se 1 (by rfl) ⟨551573, by rfl⟩ : syracuseStep 735431 = 1103147) B1103147
theorem B932087 : Blo 487790 932087 := bstep (se 1 (by rfl) ⟨699065, by rfl⟩ : syracuseStep 932087 = 1398131) B1398131
theorem B735593 : Blo 487790 735593 := bstep (se 2 (by rfl) ⟨275847, by rfl⟩ : syracuseStep 735593 = 551695) B551695
theorem B932239 : Blo 487790 932239 := bstep (se 1 (by rfl) ⟨699179, by rfl⟩ : syracuseStep 932239 = 1398359) B1398359
theorem B735671 : Blo 487790 735671 := bstep (se 1 (by rfl) ⟨551753, by rfl⟩ : syracuseStep 735671 = 1103507) B1103507
theorem B735707 : Blo 487790 735707 := bstep (se 1 (by rfl) ⟨551780, by rfl⟩ : syracuseStep 735707 = 1103561) B1103561
theorem B1653371 : Blo 487790 1653371 := bstep (se 1 (by rfl) ⟨1240028, by rfl⟩ : syracuseStep 1653371 = 2480057) B2480057
theorem B1653533 : Blo 487790 1653533 := bstep (se 3 (by rfl) ⟨310037, by rfl⟩ : syracuseStep 1653533 = 620075) B620075
theorem B736175 : Blo 487790 736175 := bstep (se 1 (by rfl) ⟨552131, by rfl⟩ : syracuseStep 736175 = 1104263) B1104263
theorem B736265 : Blo 487790 736265 := bstep (se 2 (by rfl) ⟨276099, by rfl⟩ : syracuseStep 736265 = 552199) B552199
theorem B736295 : Blo 487790 736295 := bstep (se 1 (by rfl) ⟨552221, by rfl⟩ : syracuseStep 736295 = 1104443) B1104443
theorem B736379 : Blo 487790 736379 := bstep (se 1 (by rfl) ⟨552284, by rfl⟩ : syracuseStep 736379 = 1104569) B1104569
theorem B736505 : Blo 487790 736505 := bstep (se 2 (by rfl) ⟨276189, by rfl⟩ : syracuseStep 736505 = 552379) B552379
theorem B933113 : Blo 487790 933113 := bstep (se 2 (by rfl) ⟨349917, by rfl⟩ : syracuseStep 933113 = 699835) B699835
theorem B1588567 : Blo 487790 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B736607 : Blo 487790 736607 := bstep (se 1 (by rfl) ⟨552455, by rfl⟩ : syracuseStep 736607 = 1104911) B1104911
theorem B736619 : Blo 487790 736619 := bstep (se 1 (by rfl) ⟨552464, by rfl⟩ : syracuseStep 736619 = 1104929) B1104929
theorem B933295 : Blo 487790 933295 := bstep (se 1 (by rfl) ⟨699971, by rfl⟩ : syracuseStep 933295 = 1399943) B1399943
theorem B3128777 : Blo 487790 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B1654235 : Blo 487790 1654235 := bstep (se 1 (by rfl) ⟨1240676, by rfl⟩ : syracuseStep 1654235 = 2481353) B2481353
theorem B736847 : Blo 487790 736847 := bstep (se 1 (by rfl) ⟨552635, by rfl⟩ : syracuseStep 736847 = 1105271) B1105271
theorem B1916513 : Blo 487790 1916513 := bstep (se 2 (by rfl) ⟨718692, by rfl⟩ : syracuseStep 1916513 = 1437385) B1437385
theorem B736967 : Blo 487790 736967 := bstep (se 1 (by rfl) ⟨552725, by rfl⟩ : syracuseStep 736967 = 1105451) B1105451
theorem B3718871 : Blo 487790 3718871 := bstep (se 1 (by rfl) ⟨2789153, by rfl⟩ : syracuseStep 3718871 = 5578307) B5578307
theorem B1097567 : Blo 487790 1097567 := bstep (se 1 (by rfl) ⟨823175, by rfl⟩ : syracuseStep 1097567 = 1646351) B1646351
theorem B737129 : Blo 487790 737129 := bstep (se 2 (by rfl) ⟨276423, by rfl⟩ : syracuseStep 737129 = 552847) B552847
theorem B737207 : Blo 487790 737207 := bstep (se 1 (by rfl) ⟨552905, by rfl⟩ : syracuseStep 737207 = 1105811) B1105811
theorem B737243 : Blo 487790 737243 := bstep (se 1 (by rfl) ⟨552932, by rfl⟩ : syracuseStep 737243 = 1105865) B1105865
theorem B1097747 : Blo 487790 1097747 := bstep (se 1 (by rfl) ⟨823310, by rfl⟩ : syracuseStep 1097747 = 1646621) B1646621
theorem B1654937 : Blo 487790 1654937 := bstep (se 2 (by rfl) ⟨620601, by rfl⟩ : syracuseStep 1654937 = 1241203) B1241203
theorem B1098089 : Blo 487790 1098089 := bstep (se 2 (by rfl) ⟨411783, by rfl⟩ : syracuseStep 1098089 = 823567) B823567
theorem B3129803 : Blo 487790 3129803 := bstep (se 1 (by rfl) ⟨2347352, by rfl⟩ : syracuseStep 3129803 = 4694705) B4694705
theorem B22921751 : Blo 487790 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B967339 : Blo 487790 967339 := bstep (se 1 (by rfl) ⟨725504, by rfl⟩ : syracuseStep 967339 = 1451009) B1451009
theorem B1983305 : Blo 487790 1983305 := bstep (se 2 (by rfl) ⟨743739, by rfl⟩ : syracuseStep 1983305 = 1487479) B1487479
theorem B1852267 : Blo 487790 1852267 := bstep (se 1 (by rfl) ⟨1389200, by rfl⟩ : syracuseStep 1852267 = 2778401) B2778401
theorem B1131371 : Blo 487790 1131371 := bstep (se 1 (by rfl) ⟨848528, by rfl⟩ : syracuseStep 1131371 = 1697057) B1697057
theorem B1098683 : Blo 487790 1098683 := bstep (se 1 (by rfl) ⟨824012, by rfl⟩ : syracuseStep 1098683 = 1648025) B1648025
theorem B11289619 : Blo 487790 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B1098809 : Blo 487790 1098809 := bstep (se 2 (by rfl) ⟨412053, by rfl⟩ : syracuseStep 1098809 = 824107) B824107
theorem B1656125 : Blo 487790 1656125 := bstep (se 3 (by rfl) ⟨310523, by rfl⟩ : syracuseStep 1656125 = 621047) B621047
theorem B1099151 : Blo 487790 1099151 := bstep (se 1 (by rfl) ⟨824363, by rfl⟩ : syracuseStep 1099151 = 1648727) B1648727
theorem B1820141 : Blo 487790 1820141 := bstep (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) B682553
theorem B1099475 : Blo 487790 1099475 := bstep (se 1 (by rfl) ⟨824606, by rfl⟩ : syracuseStep 1099475 = 1649213) B1649213
theorem B1656989 : Blo 487790 1656989 := bstep (se 3 (by rfl) ⟨310685, by rfl⟩ : syracuseStep 1656989 = 621371) B621371
theorem B1985057 : Blo 487790 1985057 := bstep (se 2 (by rfl) ⟨744396, by rfl⟩ : syracuseStep 1985057 = 1488793) B1488793
theorem B3721787 : Blo 487790 3721787 := bstep (se 1 (by rfl) ⟨2791340, by rfl⟩ : syracuseStep 3721787 = 5582681) B5582681
theorem B1100411 : Blo 487790 1100411 := bstep (se 1 (by rfl) ⟨825308, by rfl⟩ : syracuseStep 1100411 = 1650617) B1650617
theorem B1657529 : Blo 487790 1657529 := bstep (se 2 (by rfl) ⟨621573, by rfl⟩ : syracuseStep 1657529 = 1243147) B1243147
theorem B1100537 : Blo 487790 1100537 := bstep (se 2 (by rfl) ⟨412701, by rfl⟩ : syracuseStep 1100537 = 825403) B825403
theorem B1100807 : Blo 487790 1100807 := bstep (se 1 (by rfl) ⟨825605, by rfl⟩ : syracuseStep 1100807 = 1651211) B1651211
theorem B1100879 : Blo 487790 1100879 := bstep (se 1 (by rfl) ⟨825659, by rfl⟩ : syracuseStep 1100879 = 1651319) B1651319
theorem B2641099 : Blo 487790 2641099 := bstep (se 1 (by rfl) ⟨1980824, by rfl⟩ : syracuseStep 2641099 = 3961649) B3961649
theorem B2477303 : Blo 487790 2477303 := bstep (se 1 (by rfl) ⟨1857977, by rfl⟩ : syracuseStep 2477303 = 3715955) B3715955
theorem B1658123 : Blo 487790 1658123 := bstep (se 1 (by rfl) ⟨1243592, by rfl⟩ : syracuseStep 1658123 = 2487185) B2487185
theorem B1101275 : Blo 487790 1101275 := bstep (se 1 (by rfl) ⟨825956, by rfl⟩ : syracuseStep 1101275 = 1651913) B1651913
theorem B1855001 : Blo 487790 1855001 := bstep (se 2 (by rfl) ⟨695625, by rfl⟩ : syracuseStep 1855001 = 1391251) B1391251
theorem B1658393 : Blo 487790 1658393 := bstep (se 2 (by rfl) ⟨621897, by rfl⟩ : syracuseStep 1658393 = 1243795) B1243795
theorem B2018849 : Blo 487790 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B13618775 : Blo 487790 13618775 := bstep (se 1 (by rfl) ⟨10214081, by rfl⟩ : syracuseStep 13618775 = 20428163) B20428163
theorem B26758835 : Blo 487790 26758835 := bstep (se 1 (by rfl) ⟨20069126, by rfl⟩ : syracuseStep 26758835 = 40138253) B40138253
theorem B2477789 : Blo 487790 2477789 := bstep (se 3 (by rfl) ⟨464585, by rfl⟩ : syracuseStep 2477789 = 929171) B929171
theorem B3592045 : Blo 487790 3592045 := bstep (se 3 (by rfl) ⟨673508, by rfl⟩ : syracuseStep 3592045 = 1347017) B1347017
theorem B1101743 : Blo 487790 1101743 := bstep (se 1 (by rfl) ⟨826307, by rfl⟩ : syracuseStep 1101743 = 1652615) B1652615
theorem B2084879 : Blo 487790 2084879 := bstep (se 1 (by rfl) ⟨1563659, by rfl⟩ : syracuseStep 2084879 = 3127319) B3127319
theorem B1101995 : Blo 487790 1101995 := bstep (se 1 (by rfl) ⟨826496, by rfl⟩ : syracuseStep 1101995 = 1652993) B1652993
theorem B12505265 : Blo 487790 12505265 := bstep (se 2 (by rfl) ⟨4689474, by rfl⟩ : syracuseStep 12505265 = 9378949) B9378949
theorem B1659527 : Blo 487790 1659527 := bstep (se 1 (by rfl) ⟨1244645, by rfl⟩ : syracuseStep 1659527 = 2489291) B2489291
theorem B1659581 : Blo 487790 1659581 := bstep (se 3 (by rfl) ⟨311171, by rfl⟩ : syracuseStep 1659581 = 622343) B622343
theorem B1102535 : Blo 487790 1102535 := bstep (se 1 (by rfl) ⟨826901, by rfl⟩ : syracuseStep 1102535 = 1653803) B1653803
theorem B12112685 : Blo 487790 12112685 := bstep (se 3 (by rfl) ⟨2271128, by rfl⟩ : syracuseStep 12112685 = 4542257) B4542257
theorem B1659743 : Blo 487790 1659743 := bstep (se 1 (by rfl) ⟨1244807, by rfl⟩ : syracuseStep 1659743 = 2489615) B2489615
theorem B4707395 : Blo 487790 4707395 := bstep (se 1 (by rfl) ⟨3530546, by rfl⟩ : syracuseStep 4707395 = 7061093) B7061093
theorem B1758323 : Blo 487790 1758323 := bstep (se 1 (by rfl) ⟨1318742, by rfl⟩ : syracuseStep 1758323 = 2637485) B2637485
theorem B1856627 : Blo 487790 1856627 := bstep (se 1 (by rfl) ⟨1392470, by rfl⟩ : syracuseStep 1856627 = 2784941) B2784941
theorem B1103399 : Blo 487790 1103399 := bstep (se 1 (by rfl) ⟨827549, by rfl⟩ : syracuseStep 1103399 = 1655099) B1655099
theorem B1103723 : Blo 487790 1103723 := bstep (se 1 (by rfl) ⟨827792, by rfl⟩ : syracuseStep 1103723 = 1655585) B1655585
theorem B1103777 : Blo 487790 1103777 := bstep (se 2 (by rfl) ⟨413916, by rfl⟩ : syracuseStep 1103777 = 827833) B827833
theorem B2086843 : Blo 487790 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B36591587 : Blo 487790 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B1398941 : Blo 487790 1398941 := bstep (se 3 (by rfl) ⟨262301, by rfl⟩ : syracuseStep 1398941 = 524603) B524603
theorem B1104119 : Blo 487790 1104119 := bstep (se 1 (by rfl) ⟨828089, by rfl⟩ : syracuseStep 1104119 = 1656179) B1656179
theorem B1857917 : Blo 487790 1857917 := bstep (se 3 (by rfl) ⟨348359, by rfl⟩ : syracuseStep 1857917 = 696719) B696719
theorem B1104713 : Blo 487790 1104713 := bstep (se 2 (by rfl) ⟨414267, by rfl⟩ : syracuseStep 1104713 = 828535) B828535
theorem B1235807 : Blo 487790 1235807 := bstep (se 1 (by rfl) ⟨926855, by rfl⟩ : syracuseStep 1235807 = 1853711) B1853711
theorem B3169169 : Blo 487790 3169169 := bstep (se 2 (by rfl) ⟨1188438, by rfl⟩ : syracuseStep 3169169 = 2376877) B2376877
theorem B1236505 : Blo 487790 1236505 := bstep (se 2 (by rfl) ⟨463689, by rfl⟩ : syracuseStep 1236505 = 927379) B927379
theorem B1105505 : Blo 487790 1105505 := bstep (se 2 (by rfl) ⟨414564, by rfl⟩ : syracuseStep 1105505 = 829129) B829129
theorem B11951887 : Blo 487790 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B1236809 : Blo 487790 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B1105847 : Blo 487790 1105847 := bstep (se 1 (by rfl) ⟨829385, by rfl⟩ : syracuseStep 1105847 = 1658771) B1658771
theorem B1007815 : Blo 487790 1007815 := bstep (se 1 (by rfl) ⟨755861, by rfl⟩ : syracuseStep 1007815 = 1511723) B1511723
theorem B6283493 : Blo 487790 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B1859831 : Blo 487790 1859831 := bstep (se 1 (by rfl) ⟨1394873, by rfl⟩ : syracuseStep 1859831 = 2789747) B2789747
theorem B1106441 : Blo 487790 1106441 := bstep (se 2 (by rfl) ⟨414915, by rfl⟩ : syracuseStep 1106441 = 829831) B829831
theorem B549499 : Blo 487790 549499 := bstep (se 1 (by rfl) ⟨412124, by rfl⟩ : syracuseStep 549499 = 824249) B824249
theorem B2482973 : Blo 487790 2482973 := bstep (se 3 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 2482973 = 931115) B931115
theorem B1237943 : Blo 487790 1237943 := bstep (se 1 (by rfl) ⟨928457, by rfl⟩ : syracuseStep 1237943 = 1856915) B1856915
theorem B1762361 : Blo 487790 1762361 := bstep (se 2 (by rfl) ⟨660885, by rfl⟩ : syracuseStep 1762361 = 1321771) B1321771
theorem B549967 : Blo 487790 549967 := bstep (se 1 (by rfl) ⟨412475, by rfl⟩ : syracuseStep 549967 = 824951) B824951
theorem B1860803 : Blo 487790 1860803 := bstep (se 1 (by rfl) ⟨1395602, by rfl⟩ : syracuseStep 1860803 = 2791205) B2791205
theorem B550363 : Blo 487790 550363 := bstep (se 1 (by rfl) ⟨412772, by rfl⟩ : syracuseStep 550363 = 825545) B825545
theorem B1861319 : Blo 487790 1861319 := bstep (se 1 (by rfl) ⟨1395989, by rfl⟩ : syracuseStep 1861319 = 2791979) B2791979
theorem B3532679 : Blo 487790 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B550831 : Blo 487790 550831 := bstep (se 1 (by rfl) ⟨413123, by rfl⟩ : syracuseStep 550831 = 826247) B826247
theorem B1239047 : Blo 487790 1239047 := bstep (se 1 (by rfl) ⟨929285, by rfl⟩ : syracuseStep 1239047 = 1858571) B1858571
theorem B1173523 : Blo 487790 1173523 := bstep (se 1 (by rfl) ⟨880142, by rfl⟩ : syracuseStep 1173523 = 1760285) B1760285
theorem B1239097 : Blo 487790 1239097 := bstep (se 2 (by rfl) ⟨464661, by rfl⟩ : syracuseStep 1239097 = 929323) B929323
theorem B944207 : Blo 487790 944207 := bstep (se 1 (by rfl) ⟨708155, by rfl⟩ : syracuseStep 944207 = 1416311) B1416311
theorem B8907059 : Blo 487790 8907059 := bstep (se 1 (by rfl) ⟨6680294, by rfl⟩ : syracuseStep 8907059 = 13360589) B13360589
theorem B551263 : Blo 487790 551263 := bstep (se 1 (by rfl) ⟨413447, by rfl⟩ : syracuseStep 551263 = 826895) B826895
theorem B1239401 : Blo 487790 1239401 := bstep (se 2 (by rfl) ⟨464775, by rfl⟩ : syracuseStep 1239401 = 929551) B929551
theorem B1174139 : Blo 487790 1174139 := bstep (se 1 (by rfl) ⟨880604, by rfl⟩ : syracuseStep 1174139 = 1761209) B1761209
theorem B1862291 : Blo 487790 1862291 := bstep (se 1 (by rfl) ⟨1396718, by rfl⟩ : syracuseStep 1862291 = 2793437) B2793437
theorem B551623 : Blo 487790 551623 := bstep (se 1 (by rfl) ⟨413717, by rfl⟩ : syracuseStep 551623 = 827435) B827435
theorem B3009233 : Blo 487790 3009233 := bstep (se 2 (by rfl) ⟨1128462, by rfl⟩ : syracuseStep 3009233 = 2256925) B2256925
theorem B2779859 : Blo 487790 2779859 := bstep (se 1 (by rfl) ⟨2084894, by rfl⟩ : syracuseStep 2779859 = 4169789) B4169789
theorem B1862473 : Blo 487790 1862473 := bstep (se 2 (by rfl) ⟨698427, by rfl⟩ : syracuseStep 1862473 = 1396855) B1396855
theorem B3566963 : Blo 487790 3566963 := bstep (se 1 (by rfl) ⟨2675222, by rfl⟩ : syracuseStep 3566963 = 5350445) B5350445
theorem B552487 : Blo 487790 552487 := bstep (se 1 (by rfl) ⟨414365, by rfl⟩ : syracuseStep 552487 = 828731) B828731
theorem B4452367 : Blo 487790 4452367 := bstep (se 1 (by rfl) ⟨3339275, by rfl⟩ : syracuseStep 4452367 = 6678551) B6678551
theorem B5566643 : Blo 487790 5566643 := bstep (se 1 (by rfl) ⟨4174982, by rfl⟩ : syracuseStep 5566643 = 8349965) B8349965
theorem B3141899 : Blo 487790 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B487803 : Blo 487790 487803 := bstep (se 1 (by rfl) ⟨365852, by rfl⟩ : syracuseStep 487803 = 731705) B731705
theorem B487855 : Blo 487790 487855 := bstep (se 1 (by rfl) ⟨365891, by rfl⟩ : syracuseStep 487855 = 731783) B731783
theorem B487879 : Blo 487790 487879 := bstep (se 1 (by rfl) ⟨365909, by rfl⟩ : syracuseStep 487879 = 731819) B731819
theorem B487899 : Blo 487790 487899 := bstep (se 1 (by rfl) ⟨365924, by rfl⟩ : syracuseStep 487899 = 731849) B731849
theorem B3731993 : Blo 487790 3731993 := bstep (se 2 (by rfl) ⟨1399497, by rfl⟩ : syracuseStep 3731993 = 2798995) B2798995
theorem B487975 : Blo 487790 487975 := bstep (se 1 (by rfl) ⟨365981, by rfl⟩ : syracuseStep 487975 = 731963) B731963
theorem B782887 : Blo 487790 782887 := bstep (se 1 (by rfl) ⟨587165, by rfl⟩ : syracuseStep 782887 = 1174331) B1174331
theorem B1241639 : Blo 487790 1241639 := bstep (se 1 (by rfl) ⟨931229, by rfl⟩ : syracuseStep 1241639 = 1862459) B1862459
theorem B881209 : Blo 487790 881209 := bstep (se 2 (by rfl) ⟨330453, by rfl⟩ : syracuseStep 881209 = 660907) B660907
theorem B2093627 : Blo 487790 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B488015 : Blo 487790 488015 := bstep (se 1 (by rfl) ⟨366011, by rfl⟩ : syracuseStep 488015 = 732023) B732023
theorem B488031 : Blo 487790 488031 := bstep (se 1 (by rfl) ⟨366023, by rfl⟩ : syracuseStep 488031 = 732047) B732047
theorem B488059 : Blo 487790 488059 := bstep (se 1 (by rfl) ⟨366044, by rfl⟩ : syracuseStep 488059 = 732089) B732089
theorem B488111 : Blo 487790 488111 := bstep (se 1 (by rfl) ⟨366083, by rfl⟩ : syracuseStep 488111 = 732167) B732167
theorem B488135 : Blo 487790 488135 := bstep (se 1 (by rfl) ⟨366101, by rfl⟩ : syracuseStep 488135 = 732203) B732203
theorem B10711763 : Blo 487790 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B2093779 : Blo 487790 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B1864403 : Blo 487790 1864403 := bstep (se 1 (by rfl) ⟨1398302, by rfl⟩ : syracuseStep 1864403 = 2796605) B2796605
theorem B488155 : Blo 487790 488155 := bstep (se 1 (by rfl) ⟨366116, by rfl⟩ : syracuseStep 488155 = 732233) B732233
theorem B488231 : Blo 487790 488231 := bstep (se 1 (by rfl) ⟨366173, by rfl⟩ : syracuseStep 488231 = 732347) B732347
theorem B2782025 : Blo 487790 2782025 := bstep (se 2 (by rfl) ⟨1043259, by rfl⟩ : syracuseStep 2782025 = 2086519) B2086519
theorem B2978633 : Blo 487790 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B488271 : Blo 487790 488271 := bstep (se 1 (by rfl) ⟨366203, by rfl⟩ : syracuseStep 488271 = 732407) B732407
theorem B488287 : Blo 487790 488287 := bstep (se 1 (by rfl) ⟨366215, by rfl⟩ : syracuseStep 488287 = 732431) B732431
theorem B1241963 : Blo 487790 1241963 := bstep (se 1 (by rfl) ⟨931472, by rfl⟩ : syracuseStep 1241963 = 1862945) B1862945
theorem B488315 : Blo 487790 488315 := bstep (se 1 (by rfl) ⟨366236, by rfl⟩ : syracuseStep 488315 = 732473) B732473
theorem B488367 : Blo 487790 488367 := bstep (se 1 (by rfl) ⟨366275, by rfl⟩ : syracuseStep 488367 = 732551) B732551
theorem B488391 : Blo 487790 488391 := bstep (se 1 (by rfl) ⟨366293, by rfl⟩ : syracuseStep 488391 = 732587) B732587
theorem B488411 : Blo 487790 488411 := bstep (se 1 (by rfl) ⟨366308, by rfl⟩ : syracuseStep 488411 = 732617) B732617
theorem B619483 : Blo 487790 619483 := bstep (se 1 (by rfl) ⟨464612, by rfl⟩ : syracuseStep 619483 = 929225) B929225
theorem B1045523 : Blo 487790 1045523 := bstep (se 1 (by rfl) ⟨784142, by rfl⟩ : syracuseStep 1045523 = 1568285) B1568285
theorem B488487 : Blo 487790 488487 := bstep (se 1 (by rfl) ⟨366365, by rfl⟩ : syracuseStep 488487 = 732731) B732731
theorem B2487347 : Blo 487790 2487347 := bstep (se 1 (by rfl) ⟨1865510, by rfl⟩ : syracuseStep 2487347 = 3731021) B3731021
theorem B488527 : Blo 487790 488527 := bstep (se 1 (by rfl) ⟨366395, by rfl⟩ : syracuseStep 488527 = 732791) B732791
theorem B488543 : Blo 487790 488543 := bstep (se 1 (by rfl) ⟨366407, by rfl⟩ : syracuseStep 488543 = 732815) B732815
theorem B488571 : Blo 487790 488571 := bstep (se 1 (by rfl) ⟨366428, by rfl⟩ : syracuseStep 488571 = 732857) B732857
theorem B4191385 : Blo 487790 4191385 := bstep (se 2 (by rfl) ⟨1571769, by rfl⟩ : syracuseStep 4191385 = 3143539) B3143539
theorem B488623 : Blo 487790 488623 := bstep (se 1 (by rfl) ⟨366467, by rfl⟩ : syracuseStep 488623 = 732935) B732935
theorem B3568835 : Blo 487790 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B488647 : Blo 487790 488647 := bstep (se 1 (by rfl) ⟨366485, by rfl⟩ : syracuseStep 488647 = 732971) B732971
theorem B488667 : Blo 487790 488667 := bstep (se 1 (by rfl) ⟨366500, by rfl⟩ : syracuseStep 488667 = 733001) B733001
theorem B488743 : Blo 487790 488743 := bstep (se 1 (by rfl) ⟨366557, by rfl⟩ : syracuseStep 488743 = 733115) B733115
theorem B488783 : Blo 487790 488783 := bstep (se 1 (by rfl) ⟨366587, by rfl⟩ : syracuseStep 488783 = 733175) B733175
theorem B488799 : Blo 487790 488799 := bstep (se 1 (by rfl) ⟨366599, by rfl⟩ : syracuseStep 488799 = 733199) B733199
theorem B1045865 : Blo 487790 1045865 := bstep (se 2 (by rfl) ⟨392199, by rfl⟩ : syracuseStep 1045865 = 784399) B784399
theorem B488827 : Blo 487790 488827 := bstep (se 1 (by rfl) ⟨366620, by rfl⟩ : syracuseStep 488827 = 733241) B733241
theorem B488879 : Blo 487790 488879 := bstep (se 1 (by rfl) ⟨366659, by rfl⟩ : syracuseStep 488879 = 733319) B733319
theorem B882103 : Blo 487790 882103 := bstep (se 1 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 882103 = 1323155) B1323155
theorem B488903 : Blo 487790 488903 := bstep (se 1 (by rfl) ⟨366677, by rfl⟩ : syracuseStep 488903 = 733355) B733355
theorem B1766857 : Blo 487790 1766857 := bstep (se 2 (by rfl) ⟨662571, by rfl⟩ : syracuseStep 1766857 = 1325143) B1325143
theorem B488923 : Blo 487790 488923 := bstep (se 1 (by rfl) ⟨366692, by rfl⟩ : syracuseStep 488923 = 733385) B733385
theorem B1177051 : Blo 487790 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B1242611 : Blo 487790 1242611 := bstep (se 1 (by rfl) ⟨931958, by rfl⟩ : syracuseStep 1242611 = 1863917) B1863917
theorem B488999 : Blo 487790 488999 := bstep (se 1 (by rfl) ⟨366749, by rfl⟩ : syracuseStep 488999 = 733499) B733499
theorem B882233 : Blo 487790 882233 := bstep (se 2 (by rfl) ⟨330837, by rfl⟩ : syracuseStep 882233 = 661675) B661675
theorem B489039 : Blo 487790 489039 := bstep (se 1 (by rfl) ⟨366779, by rfl⟩ : syracuseStep 489039 = 733559) B733559
theorem B489055 : Blo 487790 489055 := bstep (se 1 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 489055 = 733583) B733583
theorem B489083 : Blo 487790 489083 := bstep (se 1 (by rfl) ⟨366812, by rfl⟩ : syracuseStep 489083 = 733625) B733625
theorem B489135 : Blo 487790 489135 := bstep (se 1 (by rfl) ⟨366851, by rfl⟩ : syracuseStep 489135 = 733703) B733703
theorem B489159 : Blo 487790 489159 := bstep (se 1 (by rfl) ⟨366869, by rfl⟩ : syracuseStep 489159 = 733739) B733739
theorem B1242823 : Blo 487790 1242823 := bstep (se 1 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 1242823 = 1864235) B1864235
theorem B489179 : Blo 487790 489179 := bstep (se 1 (by rfl) ⟨366884, by rfl⟩ : syracuseStep 489179 = 733769) B733769
theorem B489255 : Blo 487790 489255 := bstep (se 1 (by rfl) ⟨366941, by rfl⟩ : syracuseStep 489255 = 733883) B733883
theorem B489295 : Blo 487790 489295 := bstep (se 1 (by rfl) ⟨366971, by rfl⟩ : syracuseStep 489295 = 733943) B733943
theorem B489311 : Blo 487790 489311 := bstep (se 1 (by rfl) ⟨366983, by rfl⟩ : syracuseStep 489311 = 733967) B733967
theorem B489339 : Blo 487790 489339 := bstep (se 1 (by rfl) ⟨367004, by rfl⟩ : syracuseStep 489339 = 734009) B734009
theorem B489391 : Blo 487790 489391 := bstep (se 1 (by rfl) ⟨367043, by rfl⟩ : syracuseStep 489391 = 734087) B734087
theorem B489415 : Blo 487790 489415 := bstep (se 1 (by rfl) ⟨367061, by rfl⟩ : syracuseStep 489415 = 734123) B734123
theorem B489435 : Blo 487790 489435 := bstep (se 1 (by rfl) ⟨367076, by rfl⟩ : syracuseStep 489435 = 734153) B734153
theorem B489511 : Blo 487790 489511 := bstep (se 1 (by rfl) ⟨367133, by rfl⟩ : syracuseStep 489511 = 734267) B734267
theorem B489551 : Blo 487790 489551 := bstep (se 1 (by rfl) ⟨367163, by rfl⟩ : syracuseStep 489551 = 734327) B734327
theorem B489567 : Blo 487790 489567 := bstep (se 1 (by rfl) ⟨367175, by rfl⟩ : syracuseStep 489567 = 734351) B734351
theorem B489595 : Blo 487790 489595 := bstep (se 1 (by rfl) ⟨367196, by rfl⟩ : syracuseStep 489595 = 734393) B734393
theorem B489647 : Blo 487790 489647 := bstep (se 1 (by rfl) ⟨367235, by rfl⟩ : syracuseStep 489647 = 734471) B734471
theorem B489671 : Blo 487790 489671 := bstep (se 1 (by rfl) ⟨367253, by rfl⟩ : syracuseStep 489671 = 734507) B734507
theorem B489691 : Blo 487790 489691 := bstep (se 1 (by rfl) ⟨367268, by rfl⟩ : syracuseStep 489691 = 734537) B734537
theorem B489767 : Blo 487790 489767 := bstep (se 1 (by rfl) ⟨367325, by rfl⟩ : syracuseStep 489767 = 734651) B734651
theorem B489807 : Blo 487790 489807 := bstep (se 1 (by rfl) ⟨367355, by rfl⟩ : syracuseStep 489807 = 734711) B734711
theorem B489823 : Blo 487790 489823 := bstep (se 1 (by rfl) ⟨367367, by rfl⟩ : syracuseStep 489823 = 734735) B734735
theorem B489851 : Blo 487790 489851 := bstep (se 1 (by rfl) ⟨367388, by rfl⟩ : syracuseStep 489851 = 734777) B734777
theorem B489903 : Blo 487790 489903 := bstep (se 1 (by rfl) ⟨367427, by rfl⟩ : syracuseStep 489903 = 734855) B734855
theorem B489927 : Blo 487790 489927 := bstep (se 1 (by rfl) ⟨367445, by rfl⟩ : syracuseStep 489927 = 734891) B734891
theorem B489947 : Blo 487790 489947 := bstep (se 1 (by rfl) ⟨367460, by rfl⟩ : syracuseStep 489947 = 734921) B734921
theorem B2095625 : Blo 487790 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B490023 : Blo 487790 490023 := bstep (se 1 (by rfl) ⟨367517, by rfl⟩ : syracuseStep 490023 = 735035) B735035
theorem B490063 : Blo 487790 490063 := bstep (se 1 (by rfl) ⟨367547, by rfl⟩ : syracuseStep 490063 = 735095) B735095
theorem B490079 : Blo 487790 490079 := bstep (se 1 (by rfl) ⟨367559, by rfl⟩ : syracuseStep 490079 = 735119) B735119
theorem B1243745 : Blo 487790 1243745 := bstep (se 2 (by rfl) ⟨466404, by rfl⟩ : syracuseStep 1243745 = 932809) B932809
theorem B490107 : Blo 487790 490107 := bstep (se 1 (by rfl) ⟨367580, by rfl⟩ : syracuseStep 490107 = 735161) B735161
theorem B1047163 : Blo 487790 1047163 := bstep (se 1 (by rfl) ⟨785372, by rfl⟩ : syracuseStep 1047163 = 1570745) B1570745
theorem B2488967 : Blo 487790 2488967 := bstep (se 1 (by rfl) ⟨1866725, by rfl⟩ : syracuseStep 2488967 = 3733451) B3733451
theorem B490159 : Blo 487790 490159 := bstep (se 1 (by rfl) ⟨367619, by rfl⟩ : syracuseStep 490159 = 735239) B735239
theorem B490183 : Blo 487790 490183 := bstep (se 1 (by rfl) ⟨367637, by rfl⟩ : syracuseStep 490183 = 735275) B735275
theorem B490203 : Blo 487790 490203 := bstep (se 1 (by rfl) ⟨367652, by rfl⟩ : syracuseStep 490203 = 735305) B735305
theorem B490279 : Blo 487790 490279 := bstep (se 1 (by rfl) ⟨367709, by rfl⟩ : syracuseStep 490279 = 735419) B735419
theorem B490319 : Blo 487790 490319 := bstep (se 1 (by rfl) ⟨367739, by rfl⟩ : syracuseStep 490319 = 735479) B735479
theorem B523103 : Blo 487790 523103 := bstep (se 1 (by rfl) ⟨392327, by rfl⟩ : syracuseStep 523103 = 784655) B784655
theorem B490335 : Blo 487790 490335 := bstep (se 1 (by rfl) ⟨367751, by rfl⟩ : syracuseStep 490335 = 735503) B735503
theorem B490363 : Blo 487790 490363 := bstep (se 1 (by rfl) ⟨367772, by rfl⟩ : syracuseStep 490363 = 735545) B735545
theorem B490415 : Blo 487790 490415 := bstep (se 1 (by rfl) ⟨367811, by rfl⟩ : syracuseStep 490415 = 735623) B735623
theorem B1276847 : Blo 487790 1276847 := bstep (se 1 (by rfl) ⟨957635, by rfl⟩ : syracuseStep 1276847 = 1915271) B1915271
theorem B490439 : Blo 487790 490439 := bstep (se 1 (by rfl) ⟨367829, by rfl⟩ : syracuseStep 490439 = 735659) B735659
theorem B490459 : Blo 487790 490459 := bstep (se 1 (by rfl) ⟨367844, by rfl⟩ : syracuseStep 490459 = 735689) B735689
theorem B4717541 : Blo 487790 4717541 := bstep (se 4 (by rfl) ⟨442269, by rfl⟩ : syracuseStep 4717541 = 884539) B884539
theorem B490535 : Blo 487790 490535 := bstep (se 1 (by rfl) ⟨367901, by rfl⟩ : syracuseStep 490535 = 735803) B735803
theorem B490575 : Blo 487790 490575 := bstep (se 1 (by rfl) ⟨367931, by rfl⟩ : syracuseStep 490575 = 735863) B735863
theorem B1866833 : Blo 487790 1866833 := bstep (se 2 (by rfl) ⟨700062, by rfl⟩ : syracuseStep 1866833 = 1400125) B1400125
theorem B490591 : Blo 487790 490591 := bstep (se 1 (by rfl) ⟨367943, by rfl⟩ : syracuseStep 490591 = 735887) B735887
theorem B490619 : Blo 487790 490619 := bstep (se 1 (by rfl) ⟨367964, by rfl⟩ : syracuseStep 490619 = 735929) B735929
theorem B490671 : Blo 487790 490671 := bstep (se 1 (by rfl) ⟨368003, by rfl⟩ : syracuseStep 490671 = 736007) B736007
theorem B490695 : Blo 487790 490695 := bstep (se 1 (by rfl) ⟨368021, by rfl⟩ : syracuseStep 490695 = 736043) B736043
theorem B490715 : Blo 487790 490715 := bstep (se 1 (by rfl) ⟨368036, by rfl⟩ : syracuseStep 490715 = 736073) B736073
theorem B490791 : Blo 487790 490791 := bstep (se 1 (by rfl) ⟨368093, by rfl⟩ : syracuseStep 490791 = 736187) B736187
theorem B490831 : Blo 487790 490831 := bstep (se 1 (by rfl) ⟨368123, by rfl⟩ : syracuseStep 490831 = 736247) B736247
theorem B490847 : Blo 487790 490847 := bstep (se 1 (by rfl) ⟨368135, by rfl⟩ : syracuseStep 490847 = 736271) B736271
theorem B490875 : Blo 487790 490875 := bstep (se 1 (by rfl) ⟨368156, by rfl⟩ : syracuseStep 490875 = 736313) B736313
theorem B1867151 : Blo 487790 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B2981285 : Blo 487790 2981285 := bstep (se 4 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 2981285 = 558991) B558991
theorem B490927 : Blo 487790 490927 := bstep (se 1 (by rfl) ⟨368195, by rfl⟩ : syracuseStep 490927 = 736391) B736391
theorem B490951 : Blo 487790 490951 := bstep (se 1 (by rfl) ⟨368213, by rfl⟩ : syracuseStep 490951 = 736427) B736427
theorem B490971 : Blo 487790 490971 := bstep (se 1 (by rfl) ⟨368228, by rfl⟩ : syracuseStep 490971 = 736457) B736457
theorem B1572385 : Blo 487790 1572385 := bstep (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) B1179289
theorem B491047 : Blo 487790 491047 := bstep (se 1 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 491047 = 736571) B736571
theorem B523855 : Blo 487790 523855 := bstep (se 1 (by rfl) ⟨392891, by rfl⟩ : syracuseStep 523855 = 785783) B785783
theorem B491087 : Blo 487790 491087 := bstep (se 1 (by rfl) ⟨368315, by rfl⟩ : syracuseStep 491087 = 736631) B736631
theorem B491103 : Blo 487790 491103 := bstep (se 1 (by rfl) ⟨368327, by rfl⟩ : syracuseStep 491103 = 736655) B736655
theorem B491131 : Blo 487790 491131 := bstep (se 1 (by rfl) ⟨368348, by rfl⟩ : syracuseStep 491131 = 736697) B736697
theorem B491183 : Blo 487790 491183 := bstep (se 1 (by rfl) ⟨368387, by rfl⟩ : syracuseStep 491183 = 736775) B736775
theorem B491207 : Blo 487790 491207 := bstep (se 1 (by rfl) ⟨368405, by rfl⟩ : syracuseStep 491207 = 736811) B736811
theorem B491227 : Blo 487790 491227 := bstep (se 1 (by rfl) ⟨368420, by rfl⟩ : syracuseStep 491227 = 736841) B736841
theorem B491303 : Blo 487790 491303 := bstep (se 1 (by rfl) ⟨368477, by rfl⟩ : syracuseStep 491303 = 736955) B736955
theorem B2391851 : Blo 487790 2391851 := bstep (se 1 (by rfl) ⟨1793888, by rfl⟩ : syracuseStep 2391851 = 3587777) B3587777
theorem B1048393 : Blo 487790 1048393 := bstep (se 2 (by rfl) ⟨393147, by rfl⟩ : syracuseStep 1048393 = 786295) B786295
theorem B491343 : Blo 487790 491343 := bstep (se 1 (by rfl) ⟨368507, by rfl⟩ : syracuseStep 491343 = 737015) B737015
theorem B491359 : Blo 487790 491359 := bstep (se 1 (by rfl) ⟨368519, by rfl⟩ : syracuseStep 491359 = 737039) B737039
theorem B491387 : Blo 487790 491387 := bstep (se 1 (by rfl) ⟨368540, by rfl⟩ : syracuseStep 491387 = 737081) B737081
theorem B491439 : Blo 487790 491439 := bstep (se 1 (by rfl) ⟨368579, by rfl⟩ : syracuseStep 491439 = 737159) B737159
theorem B491463 : Blo 487790 491463 := bstep (se 1 (by rfl) ⟨368597, by rfl⟩ : syracuseStep 491463 = 737195) B737195
theorem B491483 : Blo 487790 491483 := bstep (se 1 (by rfl) ⟨368612, by rfl⟩ : syracuseStep 491483 = 737225) B737225
theorem B15728717 : Blo 487790 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B1343753 : Blo 487790 1343753 := bstep (se 2 (by rfl) ⟨503907, by rfl⟩ : syracuseStep 1343753 = 1007815) B1007815
theorem B885001 : Blo 487790 885001 := bstep (se 2 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 885001 = 663751) B663751
theorem B4718999 : Blo 487790 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B524863 : Blo 487790 524863 := bstep (se 1 (by rfl) ⟨393647, by rfl⟩ : syracuseStep 524863 = 787295) B787295
theorem B754247 : Blo 487790 754247 := bstep (se 1 (by rfl) ⟨565685, by rfl⟩ : syracuseStep 754247 = 1131371) B1131371
theorem B3769249 : Blo 487790 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B1213427 : Blo 487790 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B2557271 : Blo 487790 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B1574333 : Blo 487790 1574333 := bstep (se 3 (by rfl) ⟨295187, by rfl⟩ : syracuseStep 1574333 = 590375) B590375
theorem B2098973 : Blo 487790 2098973 := bstep (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) B787115
theorem B1574743 : Blo 487790 1574743 := bstep (se 1 (by rfl) ⟨1181057, by rfl⟩ : syracuseStep 1574743 = 2362115) B2362115
theorem B2230199 : Blo 487790 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B9079183 : Blo 487790 9079183 := bstep (se 1 (by rfl) ⟨6809387, by rfl⟩ : syracuseStep 9079183 = 13618775) B13618775
theorem B2689523 : Blo 487790 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B2100239 : Blo 487790 2100239 := bstep (se 1 (by rfl) ⟨1575179, by rfl⟩ : syracuseStep 2100239 = 3150359) B3150359
theorem B9440459 : Blo 487790 9440459 := bstep (se 1 (by rfl) ⟨7080344, by rfl⟩ : syracuseStep 9440459 = 14160689) B14160689
theorem B2100599 : Blo 487790 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B823871 : Blo 487790 823871 := bstep (se 1 (by rfl) ⟨617903, by rfl⟩ : syracuseStep 823871 = 1235807) B1235807
theorem B5575391 : Blo 487790 5575391 := bstep (se 1 (by rfl) ⟨4181543, by rfl⟩ : syracuseStep 5575391 = 8363087) B8363087
theorem B3871901 : Blo 487790 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B824539 : Blo 487790 824539 := bstep (se 1 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 824539 = 1236809) B1236809
theorem B5936489 : Blo 487790 5936489 := bstep (se 2 (by rfl) ⟨2226183, by rfl⟩ : syracuseStep 5936489 = 4452367) B4452367
theorem B2987705 : Blo 487790 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B825295 : Blo 487790 825295 := bstep (se 1 (by rfl) ⟨618971, by rfl⟩ : syracuseStep 825295 = 1237943) B1237943
theorem B2791705 : Blo 487790 2791705 := bstep (se 2 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 2791705 = 2093779) B2093779
theorem B825977 : Blo 487790 825977 := bstep (se 2 (by rfl) ⟨309741, by rfl⟩ : syracuseStep 825977 = 619483) B619483
theorem B826031 : Blo 487790 826031 := bstep (se 1 (by rfl) ⟨619523, by rfl⟩ : syracuseStep 826031 = 1239047) B1239047
theorem B629471 : Blo 487790 629471 := bstep (se 1 (by rfl) ⟨472103, by rfl⟩ : syracuseStep 629471 = 944207) B944207
theorem B5938039 : Blo 487790 5938039 := bstep (se 1 (by rfl) ⟨4453529, by rfl⟩ : syracuseStep 5938039 = 8907059) B8907059
theorem B826267 : Blo 487790 826267 := bstep (se 1 (by rfl) ⟨619700, by rfl⟩ : syracuseStep 826267 = 1239401) B1239401
theorem B2006155 : Blo 487790 2006155 := bstep (se 1 (by rfl) ⟨1504616, by rfl⟩ : syracuseStep 2006155 = 3009233) B3009233
theorem B990955 : Blo 487790 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B892729 : Blo 487790 892729 := bstep (se 2 (by rfl) ⟨334773, by rfl⟩ : syracuseStep 892729 = 669547) B669547
theorem B3711095 : Blo 487790 3711095 := bstep (se 1 (by rfl) ⟨2783321, by rfl⟩ : syracuseStep 3711095 = 5566643) B5566643
theorem B827759 : Blo 487790 827759 := bstep (se 1 (by rfl) ⟨620819, by rfl⟩ : syracuseStep 827759 = 1241639) B1241639
theorem B10625539 : Blo 487790 10625539 := bstep (se 1 (by rfl) ⟨7969154, by rfl⟩ : syracuseStep 10625539 = 15938309) B15938309
theorem B827975 : Blo 487790 827975 := bstep (se 1 (by rfl) ⟨620981, by rfl⟩ : syracuseStep 827975 = 1241963) B1241963
theorem B697015 : Blo 487790 697015 := bstep (se 1 (by rfl) ⟨522761, by rfl⟩ : syracuseStep 697015 = 1045523) B1045523
theorem B664367 : Blo 487790 664367 := bstep (se 1 (by rfl) ⟨498275, by rfl⟩ : syracuseStep 664367 = 996551) B996551
theorem B697243 : Blo 487790 697243 := bstep (se 1 (by rfl) ⟨522932, by rfl⟩ : syracuseStep 697243 = 1045865) B1045865
theorem B926635 : Blo 487790 926635 := bstep (se 1 (by rfl) ⟨694976, by rfl⟩ : syracuseStep 926635 = 1389953) B1389953
theorem B9511901 : Blo 487790 9511901 := bstep (se 3 (by rfl) ⟨1783481, by rfl⟩ : syracuseStep 9511901 = 3566963) B3566963
theorem B5579765 : Blo 487790 5579765 := bstep (se 5 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 5579765 = 523103) B523103
theorem B926711 : Blo 487790 926711 := bstep (se 1 (by rfl) ⟨695033, by rfl⟩ : syracuseStep 926711 = 1390067) B1390067
theorem B828407 : Blo 487790 828407 := bstep (se 1 (by rfl) ⟨621305, by rfl⟩ : syracuseStep 828407 = 1242611) B1242611
theorem B926939 : Blo 487790 926939 := bstep (se 1 (by rfl) ⟨695204, by rfl⟩ : syracuseStep 926939 = 1390409) B1390409
theorem B5383597 : Blo 487790 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B829163 : Blo 487790 829163 := bstep (se 1 (by rfl) ⟨621872, by rfl⟩ : syracuseStep 829163 = 1243745) B1243745
theorem B1648673 : Blo 487790 1648673 := bstep (se 2 (by rfl) ⟨618252, by rfl⟩ : syracuseStep 1648673 = 1236505) B1236505
theorem B698473 : Blo 487790 698473 := bstep (se 2 (by rfl) ⟨261927, by rfl⟩ : syracuseStep 698473 = 523855) B523855
theorem B3025025 : Blo 487790 3025025 := bstep (se 2 (by rfl) ⟨1134384, by rfl⟩ : syracuseStep 3025025 = 2268769) B2268769
theorem B15935849 : Blo 487790 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B731711 : Blo 487790 731711 := bstep (se 1 (by rfl) ⟨548783, by rfl⟩ : syracuseStep 731711 = 1097567) B1097567
theorem B731831 : Blo 487790 731831 := bstep (se 1 (by rfl) ⟨548873, by rfl⟩ : syracuseStep 731831 = 1097747) B1097747
theorem B732059 : Blo 487790 732059 := bstep (se 1 (by rfl) ⟨549044, by rfl⟩ : syracuseStep 732059 = 1098089) B1098089
theorem B15281167 : Blo 487790 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B1322203 : Blo 487790 1322203 := bstep (se 1 (by rfl) ⟨991652, by rfl⟩ : syracuseStep 1322203 = 1983305) B1983305
theorem B732455 : Blo 487790 732455 := bstep (se 1 (by rfl) ⟨549341, by rfl⟩ : syracuseStep 732455 = 1098683) B1098683
theorem B732539 : Blo 487790 732539 := bstep (se 1 (by rfl) ⟨549404, by rfl⟩ : syracuseStep 732539 = 1098809) B1098809
theorem B732665 : Blo 487790 732665 := bstep (se 2 (by rfl) ⟨274749, by rfl⟩ : syracuseStep 732665 = 549499) B549499
theorem B1289785 : Blo 487790 1289785 := bstep (se 2 (by rfl) ⟨483669, by rfl⟩ : syracuseStep 1289785 = 967339) B967339
theorem B732767 : Blo 487790 732767 := bstep (se 1 (by rfl) ⟨549575, by rfl⟩ : syracuseStep 732767 = 1099151) B1099151
theorem B1322657 : Blo 487790 1322657 := bstep (se 2 (by rfl) ⟨495996, by rfl⟩ : syracuseStep 1322657 = 991993) B991993
theorem B732983 : Blo 487790 732983 := bstep (se 1 (by rfl) ⟨549737, by rfl⟩ : syracuseStep 732983 = 1099475) B1099475
theorem B2469689 : Blo 487790 2469689 := bstep (se 2 (by rfl) ⟨926133, by rfl⟩ : syracuseStep 2469689 = 1852267) B1852267
theorem B15052825 : Blo 487790 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B733289 : Blo 487790 733289 := bstep (se 2 (by rfl) ⟨274983, by rfl⟩ : syracuseStep 733289 = 549967) B549967
theorem B1323371 : Blo 487790 1323371 := bstep (se 1 (by rfl) ⟨992528, by rfl⟩ : syracuseStep 1323371 = 1985057) B1985057
theorem B733607 : Blo 487790 733607 := bstep (se 1 (by rfl) ⟨550205, by rfl⟩ : syracuseStep 733607 = 1100411) B1100411
theorem B733691 : Blo 487790 733691 := bstep (se 1 (by rfl) ⟨550268, by rfl⟩ : syracuseStep 733691 = 1100537) B1100537
theorem B733817 : Blo 487790 733817 := bstep (se 2 (by rfl) ⟨275181, by rfl⟩ : syracuseStep 733817 = 550363) B550363
theorem B733871 : Blo 487790 733871 := bstep (se 1 (by rfl) ⟨550403, by rfl⟩ : syracuseStep 733871 = 1100807) B1100807
theorem B733919 : Blo 487790 733919 := bstep (se 1 (by rfl) ⟨550439, by rfl⟩ : syracuseStep 733919 = 1100879) B1100879
theorem B1651535 : Blo 487790 1651535 := bstep (se 1 (by rfl) ⟨1238651, by rfl⟩ : syracuseStep 1651535 = 2477303) B2477303
theorem B734183 : Blo 487790 734183 := bstep (se 1 (by rfl) ⟨550637, by rfl⟩ : syracuseStep 734183 = 1101275) B1101275
theorem B1815527 : Blo 487790 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B17839223 : Blo 487790 17839223 := bstep (se 1 (by rfl) ⟨13379417, by rfl⟩ : syracuseStep 17839223 = 26758835) B26758835
theorem B1651859 : Blo 487790 1651859 := bstep (se 1 (by rfl) ⟨1238894, by rfl⟩ : syracuseStep 1651859 = 2477789) B2477789
theorem B3519703 : Blo 487790 3519703 := bstep (se 1 (by rfl) ⟨2639777, by rfl⟩ : syracuseStep 3519703 = 5279555) B5279555
theorem B1357019 : Blo 487790 1357019 := bstep (se 1 (by rfl) ⟨1017764, by rfl⟩ : syracuseStep 1357019 = 2035529) B2035529
theorem B734441 : Blo 487790 734441 := bstep (se 2 (by rfl) ⟨275415, by rfl⟩ : syracuseStep 734441 = 550831) B550831
theorem B734495 : Blo 487790 734495 := bstep (se 1 (by rfl) ⟨550871, by rfl⟩ : syracuseStep 734495 = 1101743) B1101743
theorem B1389919 : Blo 487790 1389919 := bstep (se 1 (by rfl) ⟨1042439, by rfl⟩ : syracuseStep 1389919 = 2084879) B2084879
theorem B931169 : Blo 487790 931169 := bstep (se 2 (by rfl) ⟨349188, by rfl⟩ : syracuseStep 931169 = 698377) B698377
theorem B1652129 : Blo 487790 1652129 := bstep (se 2 (by rfl) ⟨619548, by rfl⟩ : syracuseStep 1652129 = 1239097) B1239097
theorem B734663 : Blo 487790 734663 := bstep (se 1 (by rfl) ⟨550997, by rfl⟩ : syracuseStep 734663 = 1101995) B1101995
theorem B8336843 : Blo 487790 8336843 := bstep (se 1 (by rfl) ⟨6252632, by rfl⟩ : syracuseStep 8336843 = 12505265) B12505265
theorem B4699781 : Blo 487790 4699781 := bstep (se 4 (by rfl) ⟨440604, by rfl⟩ : syracuseStep 4699781 = 881209) B881209
theorem B735017 : Blo 487790 735017 := bstep (se 2 (by rfl) ⟨275631, by rfl⟩ : syracuseStep 735017 = 551263) B551263
theorem B735023 : Blo 487790 735023 := bstep (se 1 (by rfl) ⟨551267, by rfl⟩ : syracuseStep 735023 = 1102535) B1102535
theorem B6600503 : Blo 487790 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B8075123 : Blo 487790 8075123 := bstep (se 1 (by rfl) ⟨6056342, by rfl⟩ : syracuseStep 8075123 = 12112685) B12112685
theorem B735497 : Blo 487790 735497 := bstep (se 2 (by rfl) ⟨275811, by rfl⟩ : syracuseStep 735497 = 551623) B551623
theorem B735599 : Blo 487790 735599 := bstep (se 1 (by rfl) ⟨551699, by rfl⟩ : syracuseStep 735599 = 1103399) B1103399
theorem B2472443 : Blo 487790 2472443 := bstep (se 1 (by rfl) ⟨1854332, by rfl⟩ : syracuseStep 2472443 = 3708665) B3708665
theorem B735815 : Blo 487790 735815 := bstep (se 1 (by rfl) ⟨551861, by rfl⟩ : syracuseStep 735815 = 1103723) B1103723
theorem B735851 : Blo 487790 735851 := bstep (se 1 (by rfl) ⟨551888, by rfl⟩ : syracuseStep 735851 = 1103777) B1103777
theorem B24394391 : Blo 487790 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B932627 : Blo 487790 932627 := bstep (se 1 (by rfl) ⟨699470, by rfl⟩ : syracuseStep 932627 = 1398941) B1398941
theorem B736079 : Blo 487790 736079 := bstep (se 1 (by rfl) ⟨552059, by rfl⟩ : syracuseStep 736079 = 1104119) B1104119
theorem B3521465 : Blo 487790 3521465 := bstep (se 2 (by rfl) ⟨1320549, by rfl⟩ : syracuseStep 3521465 = 2641099) B2641099
theorem B736475 : Blo 487790 736475 := bstep (se 1 (by rfl) ⟨552356, by rfl⟩ : syracuseStep 736475 = 1104713) B1104713
theorem B2112779 : Blo 487790 2112779 := bstep (se 1 (by rfl) ⟨1584584, by rfl⟩ : syracuseStep 2112779 = 3169169) B3169169
theorem B736649 : Blo 487790 736649 := bstep (se 2 (by rfl) ⟨276243, by rfl⟩ : syracuseStep 736649 = 552487) B552487
theorem B933257 : Blo 487790 933257 := bstep (se 2 (by rfl) ⟨349971, by rfl⟩ : syracuseStep 933257 = 699943) B699943
theorem B2473415 : Blo 487790 2473415 := bstep (se 1 (by rfl) ⟨1855061, by rfl⟩ : syracuseStep 2473415 = 3710123) B3710123
theorem B8371835 : Blo 487790 8371835 := bstep (se 1 (by rfl) ⟨6278876, by rfl⟩ : syracuseStep 8371835 = 12557753) B12557753
theorem B737003 : Blo 487790 737003 := bstep (se 1 (by rfl) ⟨552752, by rfl⟩ : syracuseStep 737003 = 1105505) B1105505
theorem B2473739 : Blo 487790 2473739 := bstep (se 1 (by rfl) ⟨1855304, by rfl⟩ : syracuseStep 2473739 = 3710609) B3710609
theorem B4472617 : Blo 487790 4472617 := bstep (se 2 (by rfl) ⟨1677231, by rfl⟩ : syracuseStep 4472617 = 3354463) B3354463
theorem B737231 : Blo 487790 737231 := bstep (se 1 (by rfl) ⟨552923, by rfl⟩ : syracuseStep 737231 = 1105847) B1105847
theorem B4178263 : Blo 487790 4178263 := bstep (se 1 (by rfl) ⟨3133697, by rfl⟩ : syracuseStep 4178263 = 6267395) B6267395
theorem B737627 : Blo 487790 737627 := bstep (se 1 (by rfl) ⟨553220, by rfl⟩ : syracuseStep 737627 = 1106441) B1106441
theorem B1655315 : Blo 487790 1655315 := bstep (se 1 (by rfl) ⟨1241486, by rfl⟩ : syracuseStep 1655315 = 2482973) B2482973
theorem B2474711 : Blo 487790 2474711 := bstep (se 1 (by rfl) ⟨1856033, by rfl⟩ : syracuseStep 2474711 = 3712067) B3712067
theorem B1098575 : Blo 487790 1098575 := bstep (se 1 (by rfl) ⟨823931, by rfl⟩ : syracuseStep 1098575 = 1647863) B1647863
theorem B1098791 : Blo 487790 1098791 := bstep (se 1 (by rfl) ⟨824093, by rfl⟩ : syracuseStep 1098791 = 1648187) B1648187
theorem B1852541 : Blo 487790 1852541 := bstep (se 3 (by rfl) ⟨347351, by rfl⟩ : syracuseStep 1852541 = 694703) B694703
theorem B1098971 : Blo 487790 1098971 := bstep (se 1 (by rfl) ⟨824228, by rfl⟩ : syracuseStep 1098971 = 1648457) B1648457
theorem B2475359 : Blo 487790 2475359 := bstep (se 1 (by rfl) ⟨1856519, by rfl⟩ : syracuseStep 2475359 = 3713039) B3713039
theorem B1099169 : Blo 487790 1099169 := bstep (se 2 (by rfl) ⟨412188, by rfl⟩ : syracuseStep 1099169 = 824377) B824377
theorem B2508193 : Blo 487790 2508193 := bstep (se 2 (by rfl) ⟨940572, by rfl⟩ : syracuseStep 2508193 = 1881145) B1881145
theorem B7914995 : Blo 487790 7914995 := bstep (se 1 (by rfl) ⟨5936246, by rfl⟩ : syracuseStep 7914995 = 11872493) B11872493
theorem B5588513 : Blo 487790 5588513 := bstep (se 2 (by rfl) ⟨2095692, by rfl⟩ : syracuseStep 5588513 = 4191385) B4191385
theorem B1853239 : Blo 487790 1853239 := bstep (se 1 (by rfl) ⟨1389929, by rfl⟩ : syracuseStep 1853239 = 2779859) B2779859
theorem B1099727 : Blo 487790 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B5949521 : Blo 487790 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B1657097 : Blo 487790 1657097 := bstep (se 2 (by rfl) ⟨621411, by rfl⟩ : syracuseStep 1657097 = 1242823) B1242823
theorem B1853725 : Blo 487790 1853725 := bstep (se 3 (by rfl) ⟨347573, by rfl⟩ : syracuseStep 1853725 = 695147) B695147
theorem B1100105 : Blo 487790 1100105 := bstep (se 2 (by rfl) ⟨412539, by rfl⟩ : syracuseStep 1100105 = 825079) B825079
theorem B1100123 : Blo 487790 1100123 := bstep (se 1 (by rfl) ⟨825092, by rfl⟩ : syracuseStep 1100123 = 1650185) B1650185
theorem B1100699 : Blo 487790 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B1395751 : Blo 487790 1395751 := bstep (se 1 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 1395751 = 2093627) B2093627
theorem B1100897 : Blo 487790 1100897 := bstep (se 2 (by rfl) ⟨412836, by rfl⟩ : syracuseStep 1100897 = 825673) B825673
theorem B1854683 : Blo 487790 1854683 := bstep (se 1 (by rfl) ⟨1391012, by rfl⟩ : syracuseStep 1854683 = 2782025) B2782025
theorem B1985755 : Blo 487790 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B1101095 : Blo 487790 1101095 := bstep (se 1 (by rfl) ⟨825821, by rfl⟩ : syracuseStep 1101095 = 1651643) B1651643
theorem B1658231 : Blo 487790 1658231 := bstep (se 1 (by rfl) ⟨1243673, by rfl⟩ : syracuseStep 1658231 = 2487347) B2487347
theorem B2379223 : Blo 487790 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B1396217 : Blo 487790 1396217 := bstep (se 2 (by rfl) ⟨523581, by rfl⟩ : syracuseStep 1396217 = 1047163) B1047163
theorem B2477627 : Blo 487790 2477627 := bstep (se 1 (by rfl) ⟨1858220, by rfl⟩ : syracuseStep 2477627 = 3716441) B3716441
theorem B1101473 : Blo 487790 1101473 := bstep (se 2 (by rfl) ⟨413052, by rfl⟩ : syracuseStep 1101473 = 826105) B826105
theorem B1101833 : Blo 487790 1101833 := bstep (se 2 (by rfl) ⟨413187, by rfl⟩ : syracuseStep 1101833 = 826375) B826375
theorem B1397083 : Blo 487790 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B5591429 : Blo 487790 5591429 := bstep (se 4 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 5591429 = 1048393) B1048393
theorem B1102247 : Blo 487790 1102247 := bstep (se 1 (by rfl) ⟨826685, by rfl⟩ : syracuseStep 1102247 = 1653371) B1653371
theorem B1659311 : Blo 487790 1659311 := bstep (se 1 (by rfl) ⟨1244483, by rfl⟩ : syracuseStep 1659311 = 2488967) B2488967
theorem B2118089 : Blo 487790 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B1102355 : Blo 487790 1102355 := bstep (se 1 (by rfl) ⟨826766, by rfl⟩ : syracuseStep 1102355 = 1653533) B1653533
theorem B19157573 : Blo 487790 19157573 := bstep (se 4 (by rfl) ⟨1796022, by rfl⟩ : syracuseStep 19157573 = 3592045) B3592045
theorem B1102409 : Blo 487790 1102409 := bstep (se 2 (by rfl) ⟨413403, by rfl⟩ : syracuseStep 1102409 = 826807) B826807
theorem B1987523 : Blo 487790 1987523 := bstep (se 1 (by rfl) ⟨1490642, by rfl⟩ : syracuseStep 1987523 = 2981285) B2981285
theorem B2085851 : Blo 487790 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B1102823 : Blo 487790 1102823 := bstep (se 1 (by rfl) ⟨827117, by rfl⟩ : syracuseStep 1102823 = 1654235) B1654235
theorem B2151481 : Blo 487790 2151481 := bstep (se 2 (by rfl) ⟨806805, by rfl⟩ : syracuseStep 2151481 = 1613611) B1613611
theorem B2479247 : Blo 487790 2479247 := bstep (se 1 (by rfl) ⟨1859435, by rfl⟩ : syracuseStep 2479247 = 3718871) B3718871
theorem B1594567 : Blo 487790 1594567 := bstep (se 1 (by rfl) ⟨1195925, by rfl⟩ : syracuseStep 1594567 = 2391851) B2391851
theorem B1103201 : Blo 487790 1103201 := bstep (se 2 (by rfl) ⟨413700, by rfl⟩ : syracuseStep 1103201 = 827401) B827401
theorem B1103291 : Blo 487790 1103291 := bstep (se 1 (by rfl) ⟨827468, by rfl⟩ : syracuseStep 1103291 = 1654937) B1654937
theorem B1103417 : Blo 487790 1103417 := bstep (se 2 (by rfl) ⟨413781, by rfl⟩ : syracuseStep 1103417 = 827563) B827563
theorem B2086535 : Blo 487790 2086535 := bstep (se 1 (by rfl) ⟨1564901, by rfl⟩ : syracuseStep 2086535 = 3129803) B3129803
theorem B2021021 : Blo 487790 2021021 := bstep (se 3 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 2021021 = 757883) B757883
theorem B743375 : Blo 487790 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B1104083 : Blo 487790 1104083 := bstep (se 1 (by rfl) ⟨828062, by rfl⟩ : syracuseStep 1104083 = 1656125) B1656125
theorem B2480381 : Blo 487790 2480381 := bstep (se 3 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 2480381 = 930143) B930143
theorem B1235209 : Blo 487790 1235209 := bstep (se 2 (by rfl) ⟨463203, by rfl⟩ : syracuseStep 1235209 = 926407) B926407
theorem B1104137 : Blo 487790 1104137 := bstep (se 2 (by rfl) ⟨414051, by rfl⟩ : syracuseStep 1104137 = 828103) B828103
theorem B1104353 : Blo 487790 1104353 := bstep (se 2 (by rfl) ⟨414132, by rfl⟩ : syracuseStep 1104353 = 828265) B828265
theorem B1104659 : Blo 487790 1104659 := bstep (se 1 (by rfl) ⟨828494, by rfl⟩ : syracuseStep 1104659 = 1656989) B1656989
theorem B2481191 : Blo 487790 2481191 := bstep (se 1 (by rfl) ⟨1860893, by rfl⟩ : syracuseStep 2481191 = 3721787) B3721787
theorem B1105019 : Blo 487790 1105019 := bstep (se 1 (by rfl) ⟨828764, by rfl⟩ : syracuseStep 1105019 = 1657529) B1657529
theorem B2514059 : Blo 487790 2514059 := bstep (se 1 (by rfl) ⟨1885544, by rfl⟩ : syracuseStep 2514059 = 3771089) B3771089
theorem B1105145 : Blo 487790 1105145 := bstep (se 2 (by rfl) ⟨414429, by rfl⟩ : syracuseStep 1105145 = 828859) B828859
theorem B1105289 : Blo 487790 1105289 := bstep (se 2 (by rfl) ⟨414483, by rfl⟩ : syracuseStep 1105289 = 828967) B828967
theorem B1105415 : Blo 487790 1105415 := bstep (se 1 (by rfl) ⟨829061, by rfl⟩ : syracuseStep 1105415 = 1658123) B1658123
theorem B1236667 : Blo 487790 1236667 := bstep (se 1 (by rfl) ⟨927500, by rfl⟩ : syracuseStep 1236667 = 1855001) B1855001
theorem B1105595 : Blo 487790 1105595 := bstep (se 1 (by rfl) ⟨829196, by rfl⟩ : syracuseStep 1105595 = 1658393) B1658393
theorem B1859375 : Blo 487790 1859375 := bstep (se 1 (by rfl) ⟨1394531, by rfl⟩ : syracuseStep 1859375 = 2789063) B2789063
theorem B1105721 : Blo 487790 1105721 := bstep (se 2 (by rfl) ⟨414645, by rfl⟩ : syracuseStep 1105721 = 829291) B829291
theorem B548815 : Blo 487790 548815 := bstep (se 1 (by rfl) ⟨411611, by rfl⟩ : syracuseStep 548815 = 823223) B823223
theorem B1564697 : Blo 487790 1564697 := bstep (se 2 (by rfl) ⟨586761, by rfl⟩ : syracuseStep 1564697 = 1173523) B1173523
theorem B7561349 : Blo 487790 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B549211 : Blo 487790 549211 := bstep (se 1 (by rfl) ⟨411908, by rfl⟩ : syracuseStep 549211 = 823817) B823817
theorem B1106351 : Blo 487790 1106351 := bstep (se 1 (by rfl) ⟨829763, by rfl⟩ : syracuseStep 1106351 = 1659527) B1659527
theorem B549319 : Blo 487790 549319 := bstep (se 1 (by rfl) ⟨411989, by rfl⟩ : syracuseStep 549319 = 823979) B823979
theorem B1106387 : Blo 487790 1106387 := bstep (se 1 (by rfl) ⟨829790, by rfl⟩ : syracuseStep 1106387 = 1659581) B1659581
theorem B1106495 : Blo 487790 1106495 := bstep (se 1 (by rfl) ⟨829871, by rfl⟩ : syracuseStep 1106495 = 1659743) B1659743
theorem B746167 : Blo 487790 746167 := bstep (se 1 (by rfl) ⟨559625, by rfl⟩ : syracuseStep 746167 = 1119251) B1119251
theorem B3138263 : Blo 487790 3138263 := bstep (se 1 (by rfl) ⟨2353697, by rfl⟩ : syracuseStep 3138263 = 4707395) B4707395
theorem B1172215 : Blo 487790 1172215 := bstep (se 1 (by rfl) ⟨879161, by rfl⟩ : syracuseStep 1172215 = 1758323) B1758323
theorem B1237751 : Blo 487790 1237751 := bstep (se 1 (by rfl) ⟨928313, by rfl⟩ : syracuseStep 1237751 = 1856627) B1856627
theorem B2646827 : Blo 487790 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B549679 : Blo 487790 549679 := bstep (se 1 (by rfl) ⟨412259, by rfl⟩ : syracuseStep 549679 = 824519) B824519
theorem B549787 : Blo 487790 549787 := bstep (se 1 (by rfl) ⟨412340, by rfl⟩ : syracuseStep 549787 = 824681) B824681
theorem B3236867 : Blo 487790 3236867 := bstep (se 1 (by rfl) ⟨2427650, by rfl⟩ : syracuseStep 3236867 = 4855301) B4855301
theorem B2483297 : Blo 487790 2483297 := bstep (se 2 (by rfl) ⟨931236, by rfl⟩ : syracuseStep 2483297 = 1862473) B1862473
theorem B7169123 : Blo 487790 7169123 := bstep (se 1 (by rfl) ⟨5376842, by rfl⟩ : syracuseStep 7169123 = 10753685) B10753685
theorem B550183 : Blo 487790 550183 := bstep (se 1 (by rfl) ⟨412637, by rfl⟩ : syracuseStep 550183 = 825275) B825275
theorem B550255 : Blo 487790 550255 := bstep (se 1 (by rfl) ⟨412691, by rfl⟩ : syracuseStep 550255 = 825383) B825383
theorem B550471 : Blo 487790 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B1238611 : Blo 487790 1238611 := bstep (se 1 (by rfl) ⟨928958, by rfl⟩ : syracuseStep 1238611 = 1857917) B1857917
theorem B4417361 : Blo 487790 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B551335 : Blo 487790 551335 := bstep (se 1 (by rfl) ⟨413501, by rfl⟩ : syracuseStep 551335 = 827003) B827003
theorem B2124427 : Blo 487790 2124427 := bstep (se 1 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 2124427 = 3186641) B3186641
theorem B4188995 : Blo 487790 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B1239887 : Blo 487790 1239887 := bstep (se 1 (by rfl) ⟨929915, by rfl⟩ : syracuseStep 1239887 = 1859831) B1859831
theorem B551911 : Blo 487790 551911 := bstep (se 1 (by rfl) ⟨413933, by rfl⟩ : syracuseStep 551911 = 827867) B827867
theorem B2485565 : Blo 487790 2485565 := bstep (se 3 (by rfl) ⟨466043, by rfl⟩ : syracuseStep 2485565 = 932087) B932087
theorem B1174907 : Blo 487790 1174907 := bstep (se 1 (by rfl) ⟨881180, by rfl⟩ : syracuseStep 1174907 = 1762361) B1762361
theorem B1043849 : Blo 487790 1043849 := bstep (se 2 (by rfl) ⟨391443, by rfl⟩ : syracuseStep 1043849 = 782887) B782887
theorem B1240535 : Blo 487790 1240535 := bstep (se 1 (by rfl) ⟨930401, by rfl⟩ : syracuseStep 1240535 = 1860803) B1860803
theorem B1863263 : Blo 487790 1863263 := bstep (se 1 (by rfl) ⟨1397447, by rfl⟩ : syracuseStep 1863263 = 2794895) B2794895
theorem B6254273 : Blo 487790 6254273 := bstep (se 2 (by rfl) ⟨2345352, by rfl⟩ : syracuseStep 6254273 = 4690705) B4690705
theorem B1863431 : Blo 487790 1863431 := bstep (se 1 (by rfl) ⟨1397573, by rfl⟩ : syracuseStep 1863431 = 2795147) B2795147
theorem B1240879 : Blo 487790 1240879 := bstep (se 1 (by rfl) ⟨930659, by rfl⟩ : syracuseStep 1240879 = 1861319) B1861319
theorem B2355119 : Blo 487790 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B9531341 : Blo 487790 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B487791 : Blo 487790 487791 := bstep (se 1 (by rfl) ⟨365843, by rfl⟩ : syracuseStep 487791 = 731687) B731687
theorem B487847 : Blo 487790 487847 := bstep (se 1 (by rfl) ⟨365885, by rfl⟩ : syracuseStep 487847 = 731771) B731771
theorem B782759 : Blo 487790 782759 := bstep (se 1 (by rfl) ⟨587069, by rfl⟩ : syracuseStep 782759 = 1174139) B1174139
theorem B1241527 : Blo 487790 1241527 := bstep (se 1 (by rfl) ⟨931145, by rfl⟩ : syracuseStep 1241527 = 1862291) B1862291
theorem B487931 : Blo 487790 487931 := bstep (se 1 (by rfl) ⟨365948, by rfl⟩ : syracuseStep 487931 = 731897) B731897
theorem B10711601 : Blo 487790 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B487999 : Blo 487790 487999 := bstep (se 1 (by rfl) ⟨365999, by rfl⟩ : syracuseStep 487999 = 731999) B731999
theorem B488007 : Blo 487790 488007 := bstep (se 1 (by rfl) ⟨366005, by rfl⟩ : syracuseStep 488007 = 732011) B732011
theorem B1176137 : Blo 487790 1176137 := bstep (se 2 (by rfl) ⟨441051, by rfl⟩ : syracuseStep 1176137 = 882103) B882103
theorem B619103 : Blo 487790 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B2355809 : Blo 487790 2355809 := bstep (se 2 (by rfl) ⟨883428, by rfl⟩ : syracuseStep 2355809 = 1766857) B1766857
theorem B1569401 : Blo 487790 1569401 := bstep (se 2 (by rfl) ⟨588525, by rfl⟩ : syracuseStep 1569401 = 1177051) B1177051
theorem B7959161 : Blo 487790 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B488159 : Blo 487790 488159 := bstep (se 1 (by rfl) ⟨366119, by rfl⟩ : syracuseStep 488159 = 732239) B732239
theorem B488239 : Blo 487790 488239 := bstep (se 1 (by rfl) ⟨366179, by rfl⟩ : syracuseStep 488239 = 732359) B732359
theorem B20083571 : Blo 487790 20083571 := bstep (se 1 (by rfl) ⟨15062678, by rfl⟩ : syracuseStep 20083571 = 30125357) B30125357
theorem B488347 : Blo 487790 488347 := bstep (se 1 (by rfl) ⟨366260, by rfl⟩ : syracuseStep 488347 = 732521) B732521
theorem B488399 : Blo 487790 488399 := bstep (se 1 (by rfl) ⟨366299, by rfl⟩ : syracuseStep 488399 = 732599) B732599
theorem B488423 : Blo 487790 488423 := bstep (se 1 (by rfl) ⟨366317, by rfl⟩ : syracuseStep 488423 = 732635) B732635
theorem B1864903 : Blo 487790 1864903 := bstep (se 1 (by rfl) ⟨1398677, by rfl⟩ : syracuseStep 1864903 = 2797355) B2797355
theorem B2782457 : Blo 487790 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B488735 : Blo 487790 488735 := bstep (se 1 (by rfl) ⟨366551, by rfl⟩ : syracuseStep 488735 = 733103) B733103
theorem B619807 : Blo 487790 619807 := bstep (se 1 (by rfl) ⟨464855, by rfl⟩ : syracuseStep 619807 = 929711) B929711
theorem B488795 : Blo 487790 488795 := bstep (se 1 (by rfl) ⟨366596, by rfl⟩ : syracuseStep 488795 = 733193) B733193
theorem B488815 : Blo 487790 488815 := bstep (se 1 (by rfl) ⟨366611, by rfl⟩ : syracuseStep 488815 = 733223) B733223
theorem B488871 : Blo 487790 488871 := bstep (se 1 (by rfl) ⟨366653, by rfl⟩ : syracuseStep 488871 = 733307) B733307
theorem B488955 : Blo 487790 488955 := bstep (se 1 (by rfl) ⟨366716, by rfl⟩ : syracuseStep 488955 = 733433) B733433
theorem B2094599 : Blo 487790 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B489023 : Blo 487790 489023 := bstep (se 1 (by rfl) ⟨366767, by rfl⟩ : syracuseStep 489023 = 733535) B733535
theorem B489031 : Blo 487790 489031 := bstep (se 1 (by rfl) ⟨366773, by rfl⟩ : syracuseStep 489031 = 733547) B733547
theorem B2487995 : Blo 487790 2487995 := bstep (se 1 (by rfl) ⟨1865996, by rfl⟩ : syracuseStep 2487995 = 3731993) B3731993
theorem B489183 : Blo 487790 489183 := bstep (se 1 (by rfl) ⟨366887, by rfl⟩ : syracuseStep 489183 = 733775) B733775
theorem B489263 : Blo 487790 489263 := bstep (se 1 (by rfl) ⟨366947, by rfl⟩ : syracuseStep 489263 = 733895) B733895
theorem B7141175 : Blo 487790 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B1242935 : Blo 487790 1242935 := bstep (se 1 (by rfl) ⟨932201, by rfl⟩ : syracuseStep 1242935 = 1864403) B1864403
theorem B1242985 : Blo 487790 1242985 := bstep (se 2 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 1242985 = 932239) B932239
theorem B489371 : Blo 487790 489371 := bstep (se 1 (by rfl) ⟨367028, by rfl⟩ : syracuseStep 489371 = 734057) B734057
theorem B489423 : Blo 487790 489423 := bstep (se 1 (by rfl) ⟨367067, by rfl⟩ : syracuseStep 489423 = 734135) B734135
theorem B489447 : Blo 487790 489447 := bstep (se 1 (by rfl) ⟨367085, by rfl⟩ : syracuseStep 489447 = 734171) B734171
theorem B2979919 : Blo 487790 2979919 := bstep (se 1 (by rfl) ⟨2234939, by rfl⟩ : syracuseStep 2979919 = 4469879) B4469879
theorem B4225159 : Blo 487790 4225159 := bstep (se 1 (by rfl) ⟨3168869, by rfl⟩ : syracuseStep 4225159 = 6337739) B6337739
theorem B489759 : Blo 487790 489759 := bstep (se 1 (by rfl) ⟨367319, by rfl⟩ : syracuseStep 489759 = 734639) B734639
theorem B489819 : Blo 487790 489819 := bstep (se 1 (by rfl) ⟨367364, by rfl⟩ : syracuseStep 489819 = 734729) B734729
theorem B489839 : Blo 487790 489839 := bstep (se 1 (by rfl) ⟨367379, by rfl⟩ : syracuseStep 489839 = 734759) B734759
theorem B883055 : Blo 487790 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B588155 : Blo 487790 588155 := bstep (se 1 (by rfl) ⟨441116, by rfl⟩ : syracuseStep 588155 = 882233) B882233
theorem B489895 : Blo 487790 489895 := bstep (se 1 (by rfl) ⟨367421, by rfl⟩ : syracuseStep 489895 = 734843) B734843
theorem B489979 : Blo 487790 489979 := bstep (se 1 (by rfl) ⟨367484, by rfl⟩ : syracuseStep 489979 = 734969) B734969
theorem B490047 : Blo 487790 490047 := bstep (se 1 (by rfl) ⟨367535, by rfl⟩ : syracuseStep 490047 = 735071) B735071
theorem B2128447 : Blo 487790 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B490055 : Blo 487790 490055 := bstep (se 1 (by rfl) ⟨367541, by rfl⟩ : syracuseStep 490055 = 735083) B735083
theorem B883271 : Blo 487790 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B1866347 : Blo 487790 1866347 := bstep (se 1 (by rfl) ⟨1399760, by rfl⟩ : syracuseStep 1866347 = 2799521) B2799521
theorem B490207 : Blo 487790 490207 := bstep (se 1 (by rfl) ⟨367655, by rfl⟩ : syracuseStep 490207 = 735311) B735311
theorem B883423 : Blo 487790 883423 := bstep (se 1 (by rfl) ⟨662567, by rfl⟩ : syracuseStep 883423 = 1325135) B1325135
theorem B490287 : Blo 487790 490287 := bstep (se 1 (by rfl) ⟨367715, by rfl⟩ : syracuseStep 490287 = 735431) B735431
theorem B490395 : Blo 487790 490395 := bstep (se 1 (by rfl) ⟨367796, by rfl⟩ : syracuseStep 490395 = 735593) B735593
theorem B490447 : Blo 487790 490447 := bstep (se 1 (by rfl) ⟨367835, by rfl⟩ : syracuseStep 490447 = 735671) B735671
theorem B490471 : Blo 487790 490471 := bstep (se 1 (by rfl) ⟨367853, by rfl⟩ : syracuseStep 490471 = 735707) B735707
theorem B1244393 : Blo 487790 1244393 := bstep (se 2 (by rfl) ⟨466647, by rfl⟩ : syracuseStep 1244393 = 933295) B933295
theorem B490783 : Blo 487790 490783 := bstep (se 1 (by rfl) ⟨368087, by rfl⟩ : syracuseStep 490783 = 736175) B736175
theorem B851231 : Blo 487790 851231 := bstep (se 1 (by rfl) ⟨638423, by rfl⟩ : syracuseStep 851231 = 1276847) B1276847
theorem B3145027 : Blo 487790 3145027 := bstep (se 1 (by rfl) ⟨2358770, by rfl⟩ : syracuseStep 3145027 = 4717541) B4717541
theorem B490843 : Blo 487790 490843 := bstep (se 1 (by rfl) ⟨368132, by rfl⟩ : syracuseStep 490843 = 736265) B736265
theorem B490863 : Blo 487790 490863 := bstep (se 1 (by rfl) ⟨368147, by rfl⟩ : syracuseStep 490863 = 736295) B736295
theorem B2096513 : Blo 487790 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B1244555 : Blo 487790 1244555 := bstep (se 1 (by rfl) ⟨933416, by rfl⟩ : syracuseStep 1244555 = 1866833) B1866833
theorem B490919 : Blo 487790 490919 := bstep (se 1 (by rfl) ⟨368189, by rfl⟩ : syracuseStep 490919 = 736379) B736379
theorem B491003 : Blo 487790 491003 := bstep (se 1 (by rfl) ⟨368252, by rfl⟩ : syracuseStep 491003 = 736505) B736505
theorem B622075 : Blo 487790 622075 := bstep (se 1 (by rfl) ⟨466556, by rfl⟩ : syracuseStep 622075 = 933113) B933113
theorem B491071 : Blo 487790 491071 := bstep (se 1 (by rfl) ⟨368303, by rfl⟩ : syracuseStep 491071 = 736607) B736607
theorem B491079 : Blo 487790 491079 := bstep (se 1 (by rfl) ⟨368309, by rfl⟩ : syracuseStep 491079 = 736619) B736619
theorem B1244767 : Blo 487790 1244767 := bstep (se 1 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 1244767 = 1867151) B1867151
theorem B491231 : Blo 487790 491231 := bstep (se 1 (by rfl) ⟨368423, by rfl⟩ : syracuseStep 491231 = 736847) B736847
theorem B1277675 : Blo 487790 1277675 := bstep (se 1 (by rfl) ⟨958256, by rfl⟩ : syracuseStep 1277675 = 1916513) B1916513
theorem B491311 : Blo 487790 491311 := bstep (se 1 (by rfl) ⟨368483, by rfl⟩ : syracuseStep 491311 = 736967) B736967
theorem B491419 : Blo 487790 491419 := bstep (se 1 (by rfl) ⟨368564, by rfl⟩ : syracuseStep 491419 = 737129) B737129
theorem B491471 : Blo 487790 491471 := bstep (se 1 (by rfl) ⟨368603, by rfl⟩ : syracuseStep 491471 = 737207) B737207
theorem B491495 : Blo 487790 491495 := bstep (se 1 (by rfl) ⟨368621, by rfl⟩ : syracuseStep 491495 = 737243) B737243
theorem B10485811 : Blo 487790 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B491751 : Blo 487790 491751 := bstep (se 1 (by rfl) ⟨368813, by rfl⟩ : syracuseStep 491751 = 737627) B737627
theorem B1180001 : Blo 487790 1180001 := bstep (se 2 (by rfl) ⟨442500, by rfl⟩ : syracuseStep 1180001 = 885001) B885001
theorem B5571017 : Blo 487790 5571017 := bstep (se 2 (by rfl) ⟨2089131, by rfl⟩ : syracuseStep 5571017 = 4178263) B4178263
theorem B1704847 : Blo 487790 1704847 := bstep (se 1 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 1704847 = 2557271) B2557271
theorem B1049555 : Blo 487790 1049555 := bstep (se 1 (by rfl) ⟨787166, by rfl⟩ : syracuseStep 1049555 = 1574333) B1574333
theorem B5276663 : Blo 487790 5276663 := bstep (se 1 (by rfl) ⟨3957497, by rfl⟩ : syracuseStep 5276663 = 7914995) B7914995
theorem B12583997 : Blo 487790 12583997 := bstep (se 3 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 12583997 = 4718999) B4718999
theorem B3966347 : Blo 487790 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B3344257 : Blo 487790 3344257 := bstep (se 2 (by rfl) ⟨1254096, by rfl⟩ : syracuseStep 3344257 = 2508193) B2508193
theorem B7178129 : Blo 487790 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B1771645 : Blo 487790 1771645 := bstep (se 3 (by rfl) ⟨332183, by rfl⟩ : syracuseStep 1771645 = 664367) B664367
theorem B6293639 : Blo 487790 6293639 := bstep (se 1 (by rfl) ⟨4720229, by rfl⟩ : syracuseStep 6293639 = 9440459) B9440459
theorem B2099657 : Blo 487790 2099657 := bstep (se 2 (by rfl) ⟨787371, by rfl⟩ : syracuseStep 2099657 = 1574743) B1574743
theorem B10325069 : Blo 487790 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B1347347 : Blo 487790 1347347 := bstep (se 1 (by rfl) ⟨1010510, by rfl⟩ : syracuseStep 1347347 = 2021021) B2021021
theorem B825167 : Blo 487790 825167 := bstep (se 1 (by rfl) ⟨618875, by rfl⟩ : syracuseStep 825167 = 1237751) B1237751
theorem B10623899 : Blo 487790 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B4692937 : Blo 487790 4692937 := bstep (se 2 (by rfl) ⟨1759851, by rfl⟩ : syracuseStep 4692937 = 3519703) B3519703
theorem B826409 : Blo 487790 826409 := bstep (se 2 (by rfl) ⟨309903, by rfl⟩ : syracuseStep 826409 = 619807) B619807
theorem B2792663 : Blo 487790 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B826591 : Blo 487790 826591 := bstep (se 1 (by rfl) ⟨619943, by rfl⟩ : syracuseStep 826591 = 1239887) B1239887
theorem B1678589 : Blo 487790 1678589 := bstep (se 3 (by rfl) ⟨314735, by rfl⟩ : syracuseStep 1678589 = 629471) B629471
theorem B695899 : Blo 487790 695899 := bstep (se 1 (by rfl) ⟨521924, by rfl⟩ : syracuseStep 695899 = 1043849) B1043849
theorem B827023 : Blo 487790 827023 := bstep (se 1 (by rfl) ⟨620267, by rfl⟩ : syracuseStep 827023 = 1240535) B1240535
theorem B4169515 : Blo 487790 4169515 := bstep (se 1 (by rfl) ⟨3127136, by rfl⟩ : syracuseStep 4169515 = 6254273) B6254273
theorem B1646459 : Blo 487790 1646459 := bstep (se 1 (by rfl) ⟨1234844, by rfl⟩ : syracuseStep 1646459 = 2469689) B2469689
theorem B3973225 : Blo 487790 3973225 := bstep (se 2 (by rfl) ⟨1489959, by rfl⟩ : syracuseStep 3973225 = 2979919) B2979919
theorem B1646945 : Blo 487790 1646945 := bstep (se 2 (by rfl) ⟨617604, by rfl⟩ : syracuseStep 1646945 = 1235209) B1235209
theorem B4400335 : Blo 487790 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B4760783 : Blo 487790 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B828623 : Blo 487790 828623 := bstep (se 1 (by rfl) ⟨621467, by rfl⟩ : syracuseStep 828623 = 1242935) B1242935
theorem B5383415 : Blo 487790 5383415 := bstep (se 1 (by rfl) ⟨4037561, by rfl⟩ : syracuseStep 5383415 = 8075123) B8075123
theorem B1648295 : Blo 487790 1648295 := bstep (se 1 (by rfl) ⟨1236221, by rfl⟩ : syracuseStep 1648295 = 2472443) B2472443
theorem B16262927 : Blo 487790 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B829433 : Blo 487790 829433 := bstep (se 2 (by rfl) ⟨311037, by rfl⟩ : syracuseStep 829433 = 622075) B622075
theorem B829595 : Blo 487790 829595 := bstep (se 1 (by rfl) ⟨622196, by rfl⟩ : syracuseStep 829595 = 1244393) B1244393
theorem B567487 : Blo 487790 567487 := bstep (se 1 (by rfl) ⟨425615, by rfl⟩ : syracuseStep 567487 = 851231) B851231
theorem B1648889 : Blo 487790 1648889 := bstep (se 2 (by rfl) ⟨618333, by rfl⟩ : syracuseStep 1648889 = 1236667) B1236667
theorem B829703 : Blo 487790 829703 := bstep (se 1 (by rfl) ⟨622277, by rfl⟩ : syracuseStep 829703 = 1244555) B1244555
theorem B1648943 : Blo 487790 1648943 := bstep (se 1 (by rfl) ⟨1236707, by rfl⟩ : syracuseStep 1648943 = 2473415) B2473415
theorem B1321273 : Blo 487790 1321273 := bstep (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) B990955
theorem B1190305 : Blo 487790 1190305 := bstep (se 2 (by rfl) ⟨446364, by rfl⟩ : syracuseStep 1190305 = 892729) B892729
theorem B5581223 : Blo 487790 5581223 := bstep (se 1 (by rfl) ⟨4185917, by rfl⟩ : syracuseStep 5581223 = 8371835) B8371835
theorem B1649159 : Blo 487790 1649159 := bstep (se 1 (by rfl) ⟨1236869, by rfl⟩ : syracuseStep 1649159 = 2473739) B2473739
theorem B731753 : Blo 487790 731753 := bstep (se 2 (by rfl) ⟨274407, by rfl⟩ : syracuseStep 731753 = 548815) B548815
theorem B895835 : Blo 487790 895835 := bstep (se 1 (by rfl) ⟨671876, by rfl⟩ : syracuseStep 895835 = 1343753) B1343753
theorem B502831 : Blo 487790 502831 := bstep (se 1 (by rfl) ⟨377123, by rfl⟩ : syracuseStep 502831 = 754247) B754247
theorem B732281 : Blo 487790 732281 := bstep (se 2 (by rfl) ⟨274605, by rfl⟩ : syracuseStep 732281 = 549211) B549211
theorem B1649807 : Blo 487790 1649807 := bstep (se 1 (by rfl) ⟨1237355, by rfl⟩ : syracuseStep 1649807 = 2474711) B2474711
theorem B732383 : Blo 487790 732383 := bstep (se 1 (by rfl) ⟨549287, by rfl⟩ : syracuseStep 732383 = 1098575) B1098575
theorem B732425 : Blo 487790 732425 := bstep (se 2 (by rfl) ⟨274659, by rfl⟩ : syracuseStep 732425 = 549319) B549319
theorem B14167385 : Blo 487790 14167385 := bstep (se 2 (by rfl) ⟨5312769, by rfl⟩ : syracuseStep 14167385 = 10625539) B10625539
theorem B732527 : Blo 487790 732527 := bstep (se 1 (by rfl) ⟨549395, by rfl⟩ : syracuseStep 732527 = 1098791) B1098791
theorem B732647 : Blo 487790 732647 := bstep (se 1 (by rfl) ⟨549485, by rfl⟩ : syracuseStep 732647 = 1098971) B1098971
theorem B1650239 : Blo 487790 1650239 := bstep (se 1 (by rfl) ⟨1237679, by rfl⟩ : syracuseStep 1650239 = 2475359) B2475359
theorem B994889 : Blo 487790 994889 := bstep (se 2 (by rfl) ⟨373083, by rfl⟩ : syracuseStep 994889 = 746167) B746167
theorem B732779 : Blo 487790 732779 := bstep (se 1 (by rfl) ⟨549584, by rfl⟩ : syracuseStep 732779 = 1099169) B1099169
theorem B732905 : Blo 487790 732905 := bstep (se 2 (by rfl) ⟨274839, by rfl⟩ : syracuseStep 732905 = 549679) B549679
theorem B5648237 : Blo 487790 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B733049 : Blo 487790 733049 := bstep (se 2 (by rfl) ⟨274893, by rfl⟩ : syracuseStep 733049 = 549787) B549787
theorem B929657 : Blo 487790 929657 := bstep (se 2 (by rfl) ⟨348621, by rfl⟩ : syracuseStep 929657 = 697243) B697243
theorem B5025665 : Blo 487790 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B1486799 : Blo 487790 1486799 := bstep (se 1 (by rfl) ⟨1115099, by rfl⟩ : syracuseStep 1486799 = 2230199) B2230199
theorem B733151 : Blo 487790 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B26816629 : Blo 487790 26816629 := bstep (se 5 (by rfl) ⟨1257029, by rfl⟩ : syracuseStep 26816629 = 2514059) B2514059
theorem B733403 : Blo 487790 733403 := bstep (se 1 (by rfl) ⟨550052, by rfl⟩ : syracuseStep 733403 = 1100105) B1100105
theorem B733415 : Blo 487790 733415 := bstep (se 1 (by rfl) ⟨550061, by rfl⟩ : syracuseStep 733415 = 1100123) B1100123
theorem B1650941 : Blo 487790 1650941 := bstep (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) B619103
theorem B733577 : Blo 487790 733577 := bstep (se 2 (by rfl) ⟨275091, by rfl⟩ : syracuseStep 733577 = 550183) B550183
theorem B733673 : Blo 487790 733673 := bstep (se 2 (by rfl) ⟨275127, by rfl⟩ : syracuseStep 733673 = 550255) B550255
theorem B733799 : Blo 487790 733799 := bstep (se 1 (by rfl) ⟨550349, by rfl⟩ : syracuseStep 733799 = 1100699) B1100699
theorem B733931 : Blo 487790 733931 := bstep (se 1 (by rfl) ⟨550448, by rfl⟩ : syracuseStep 733931 = 1100897) B1100897
theorem B733961 : Blo 487790 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B1651481 : Blo 487790 1651481 := bstep (se 2 (by rfl) ⟨619305, by rfl⟩ : syracuseStep 1651481 = 1238611) B1238611
theorem B734063 : Blo 487790 734063 := bstep (se 1 (by rfl) ⟨550547, by rfl⟩ : syracuseStep 734063 = 1101095) B1101095
theorem B1651751 : Blo 487790 1651751 := bstep (se 1 (by rfl) ⟨1238813, by rfl⟩ : syracuseStep 1651751 = 2477627) B2477627
theorem B2470985 : Blo 487790 2470985 := bstep (se 2 (by rfl) ⟨926619, by rfl⟩ : syracuseStep 2470985 = 1853239) B1853239
theorem B734315 : Blo 487790 734315 := bstep (se 1 (by rfl) ⟨550736, by rfl⟩ : syracuseStep 734315 = 1101473) B1101473
theorem B734555 : Blo 487790 734555 := bstep (se 1 (by rfl) ⟨550916, by rfl⟩ : syracuseStep 734555 = 1101833) B1101833
theorem B734831 : Blo 487790 734831 := bstep (se 1 (by rfl) ⟨551123, by rfl⟩ : syracuseStep 734831 = 1102247) B1102247
theorem B2799269 : Blo 487790 2799269 := bstep (se 4 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 2799269 = 524863) B524863
theorem B734903 : Blo 487790 734903 := bstep (se 1 (by rfl) ⟨551177, by rfl⟩ : syracuseStep 734903 = 1102355) B1102355
theorem B2471633 : Blo 487790 2471633 := bstep (se 2 (by rfl) ⟨926862, by rfl⟩ : syracuseStep 2471633 = 1853725) B1853725
theorem B734939 : Blo 487790 734939 := bstep (se 1 (by rfl) ⟨551204, by rfl⟩ : syracuseStep 734939 = 1102409) B1102409
theorem B3716927 : Blo 487790 3716927 := bstep (se 1 (by rfl) ⟨2787695, by rfl⟩ : syracuseStep 3716927 = 5575391) B5575391
theorem B12105577 : Blo 487790 12105577 := bstep (se 2 (by rfl) ⟨4539591, by rfl⟩ : syracuseStep 12105577 = 9079183) B9079183
theorem B735113 : Blo 487790 735113 := bstep (se 2 (by rfl) ⟨275667, by rfl⟩ : syracuseStep 735113 = 551335) B551335
theorem B1325015 : Blo 487790 1325015 := bstep (se 1 (by rfl) ⟨993761, by rfl⟩ : syracuseStep 1325015 = 1987523) B1987523
theorem B735215 : Blo 487790 735215 := bstep (se 1 (by rfl) ⟨551411, by rfl⟩ : syracuseStep 735215 = 1102823) B1102823
theorem B1652831 : Blo 487790 1652831 := bstep (se 1 (by rfl) ⟨1239623, by rfl⟩ : syracuseStep 1652831 = 2479247) B2479247
theorem B2832569 : Blo 487790 2832569 := bstep (se 2 (by rfl) ⟨1062213, by rfl⟩ : syracuseStep 2832569 = 2124427) B2124427
theorem B735467 : Blo 487790 735467 := bstep (se 1 (by rfl) ⟨551600, by rfl⟩ : syracuseStep 735467 = 1103201) B1103201
theorem B3717413 : Blo 487790 3717413 := bstep (se 4 (by rfl) ⟨348507, by rfl⟩ : syracuseStep 3717413 = 697015) B697015
theorem B735527 : Blo 487790 735527 := bstep (se 1 (by rfl) ⟨551645, by rfl⟩ : syracuseStep 735527 = 1103291) B1103291
theorem B735611 : Blo 487790 735611 := bstep (se 1 (by rfl) ⟨551708, by rfl⟩ : syracuseStep 735611 = 1103417) B1103417
theorem B1391023 : Blo 487790 1391023 := bstep (se 1 (by rfl) ⟨1043267, by rfl⟩ : syracuseStep 1391023 = 2086535) B2086535
theorem B735881 : Blo 487790 735881 := bstep (se 2 (by rfl) ⟨275955, by rfl⟩ : syracuseStep 735881 = 551911) B551911
theorem B5585597 : Blo 487790 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B736055 : Blo 487790 736055 := bstep (se 1 (by rfl) ⟨552041, by rfl⟩ : syracuseStep 736055 = 1104083) B1104083
theorem B1653587 : Blo 487790 1653587 := bstep (se 1 (by rfl) ⟨1240190, by rfl⟩ : syracuseStep 1653587 = 2480381) B2480381
theorem B736091 : Blo 487790 736091 := bstep (se 1 (by rfl) ⟨552068, by rfl⟩ : syracuseStep 736091 = 1104137) B1104137
theorem B736235 : Blo 487790 736235 := bstep (se 1 (by rfl) ⟨552176, by rfl⟩ : syracuseStep 736235 = 1104353) B1104353
theorem B736439 : Blo 487790 736439 := bstep (se 1 (by rfl) ⟨552329, by rfl⟩ : syracuseStep 736439 = 1104659) B1104659
theorem B1654127 : Blo 487790 1654127 := bstep (se 1 (by rfl) ⟨1240595, by rfl⟩ : syracuseStep 1654127 = 2481191) B2481191
theorem B1719713 : Blo 487790 1719713 := bstep (se 2 (by rfl) ⟨644892, by rfl⟩ : syracuseStep 1719713 = 1289785) B1289785
theorem B736679 : Blo 487790 736679 := bstep (se 1 (by rfl) ⟨552509, by rfl⟩ : syracuseStep 736679 = 1105019) B1105019
theorem B736763 : Blo 487790 736763 := bstep (se 1 (by rfl) ⟨552572, by rfl⟩ : syracuseStep 736763 = 1105145) B1105145
theorem B736859 : Blo 487790 736859 := bstep (se 1 (by rfl) ⟨552644, by rfl⟩ : syracuseStep 736859 = 1105289) B1105289
theorem B736943 : Blo 487790 736943 := bstep (se 1 (by rfl) ⟨552707, by rfl⟩ : syracuseStep 736943 = 1105415) B1105415
theorem B1654505 : Blo 487790 1654505 := bstep (se 2 (by rfl) ⟨620439, by rfl⟩ : syracuseStep 1654505 = 1240879) B1240879
theorem B737063 : Blo 487790 737063 := bstep (se 1 (by rfl) ⟨552797, by rfl⟩ : syracuseStep 737063 = 1105595) B1105595
theorem B737147 : Blo 487790 737147 := bstep (se 1 (by rfl) ⟨552860, by rfl⟩ : syracuseStep 737147 = 1105721) B1105721
theorem B1982333 : Blo 487790 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B20070433 : Blo 487790 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B2474063 : Blo 487790 2474063 := bstep (se 1 (by rfl) ⟨1855547, by rfl⟩ : syracuseStep 2474063 = 3711095) B3711095
theorem B737567 : Blo 487790 737567 := bstep (se 1 (by rfl) ⟨553175, by rfl⟩ : syracuseStep 737567 = 1106351) B1106351
theorem B737591 : Blo 487790 737591 := bstep (se 1 (by rfl) ⟨553193, by rfl⟩ : syracuseStep 737591 = 1106387) B1106387
theorem B737663 : Blo 487790 737663 := bstep (se 1 (by rfl) ⟨553247, by rfl⟩ : syracuseStep 737663 = 1106495) B1106495
theorem B1655369 : Blo 487790 1655369 := bstep (se 2 (by rfl) ⟨620763, by rfl⟩ : syracuseStep 1655369 = 1241527) B1241527
theorem B6341267 : Blo 487790 6341267 := bstep (se 1 (by rfl) ⟨4755950, by rfl⟩ : syracuseStep 6341267 = 9511901) B9511901
theorem B3719843 : Blo 487790 3719843 := bstep (se 1 (by rfl) ⟨2789882, by rfl⟩ : syracuseStep 3719843 = 5579765) B5579765
theorem B1655531 : Blo 487790 1655531 := bstep (se 1 (by rfl) ⟨1241648, by rfl⟩ : syracuseStep 1655531 = 2483297) B2483297
theorem B1099115 : Blo 487790 1099115 := bstep (se 1 (by rfl) ⟨824336, by rfl⟩ : syracuseStep 1099115 = 1648673) B1648673
theorem B2868641 : Blo 487790 2868641 := bstep (se 2 (by rfl) ⟨1075740, by rfl⟩ : syracuseStep 2868641 = 2151481) B2151481
theorem B2016683 : Blo 487790 2016683 := bstep (se 1 (by rfl) ⟨1512512, by rfl⟩ : syracuseStep 2016683 = 3025025) B3025025
theorem B1099385 : Blo 487790 1099385 := bstep (se 2 (by rfl) ⟨412269, by rfl⟩ : syracuseStep 1099385 = 824539) B824539
theorem B1853225 : Blo 487790 1853225 := bstep (se 2 (by rfl) ⟨694959, by rfl⟩ : syracuseStep 1853225 = 1389919) B1389919
theorem B1657043 : Blo 487790 1657043 := bstep (se 1 (by rfl) ⟨1242782, by rfl⟩ : syracuseStep 1657043 = 2485565) B2485565
theorem B1657313 : Blo 487790 1657313 := bstep (se 2 (by rfl) ⟨621492, by rfl⟩ : syracuseStep 1657313 = 1242985) B1242985
theorem B1100393 : Blo 487790 1100393 := bstep (se 2 (by rfl) ⟨412647, by rfl⟩ : syracuseStep 1100393 = 825295) B825295
theorem B3722273 : Blo 487790 3722273 := bstep (se 2 (by rfl) ⟨1395852, by rfl⟩ : syracuseStep 3722273 = 2791705) B2791705
theorem B1101023 : Blo 487790 1101023 := bstep (se 1 (by rfl) ⟨825767, by rfl⟩ : syracuseStep 1101023 = 1651535) B1651535
theorem B13389047 : Blo 487790 13389047 := bstep (se 1 (by rfl) ⟨10041785, by rfl⟩ : syracuseStep 13389047 = 20083571) B20083571
theorem B2837929 : Blo 487790 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B1101239 : Blo 487790 1101239 := bstep (se 1 (by rfl) ⟨825929, by rfl⟩ : syracuseStep 1101239 = 1651859) B1651859
theorem B904679 : Blo 487790 904679 := bstep (se 1 (by rfl) ⟨678509, by rfl⟩ : syracuseStep 904679 = 1357019) B1357019
theorem B1854971 : Blo 487790 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B1101419 : Blo 487790 1101419 := bstep (se 1 (by rfl) ⟨826064, by rfl⟩ : syracuseStep 1101419 = 1652129) B1652129
theorem B5557895 : Blo 487790 5557895 := bstep (se 1 (by rfl) ⟨4168421, by rfl⟩ : syracuseStep 5557895 = 8336843) B8336843
theorem B3133187 : Blo 487790 3133187 := bstep (se 1 (by rfl) ⟨2349890, by rfl⟩ : syracuseStep 3133187 = 4699781) B4699781
theorem B1658663 : Blo 487790 1658663 := bstep (se 1 (by rfl) ⟨1243997, by rfl⟩ : syracuseStep 1658663 = 2487995) B2487995
theorem B7917385 : Blo 487790 7917385 := bstep (se 2 (by rfl) ⟨2969019, by rfl⟩ : syracuseStep 7917385 = 5938039) B5938039
theorem B1101689 : Blo 487790 1101689 := bstep (se 2 (by rfl) ⟨413133, by rfl⟩ : syracuseStep 1101689 = 826267) B826267
theorem B3723245 : Blo 487790 3723245 := bstep (se 3 (by rfl) ⟨698108, by rfl⟩ : syracuseStep 3723245 = 1396217) B1396217
theorem B2674873 : Blo 487790 2674873 := bstep (se 2 (by rfl) ⟨1003077, by rfl⟩ : syracuseStep 2674873 = 2006155) B2006155
theorem B54514133 : Blo 487790 54514133 := bstep (se 7 (by rfl) ⟨638837, by rfl⟩ : syracuseStep 54514133 = 1277675) B1277675
theorem B2347643 : Blo 487790 2347643 := bstep (se 1 (by rfl) ⟨1760732, by rfl⟩ : syracuseStep 2347643 = 3521465) B3521465
theorem B1659689 : Blo 487790 1659689 := bstep (se 2 (by rfl) ⟨622383, by rfl⟩ : syracuseStep 1659689 = 1244767) B1244767
theorem B1397675 : Blo 487790 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B325998229 : Blo 487790 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B1103543 : Blo 487790 1103543 := bstep (se 1 (by rfl) ⟨827657, by rfl⟩ : syracuseStep 1103543 = 1655315) B1655315
theorem B3725189 : Blo 487790 3725189 := bstep (se 4 (by rfl) ⟨349236, by rfl⟩ : syracuseStep 3725189 = 698473) B698473
theorem B808951 : Blo 487790 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B1235027 : Blo 487790 1235027 := bstep (se 1 (by rfl) ⟨926270, by rfl⟩ : syracuseStep 1235027 = 1852541) B1852541
theorem B3725675 : Blo 487790 3725675 := bstep (se 1 (by rfl) ⟨2794256, by rfl⟩ : syracuseStep 3725675 = 5588513) B5588513
theorem B1235513 : Blo 487790 1235513 := bstep (se 2 (by rfl) ⟨463317, by rfl⟩ : syracuseStep 1235513 = 926635) B926635
theorem B1104731 : Blo 487790 1104731 := bstep (se 1 (by rfl) ⟨828548, by rfl⟩ : syracuseStep 1104731 = 1657097) B1657097
theorem B6282157 : Blo 487790 6282157 := bstep (se 3 (by rfl) ⟨1177904, by rfl⟩ : syracuseStep 6282157 = 2355809) B2355809
theorem B1793015 : Blo 487790 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B1400159 : Blo 487790 1400159 := bstep (se 1 (by rfl) ⟨1050119, by rfl⟩ : syracuseStep 1400159 = 2100239) B2100239
theorem B1236455 : Blo 487790 1236455 := bstep (se 1 (by rfl) ⟨927341, by rfl⟩ : syracuseStep 1236455 = 1854683) B1854683
theorem B1105487 : Blo 487790 1105487 := bstep (se 1 (by rfl) ⟨829115, by rfl⟩ : syracuseStep 1105487 = 1658231) B1658231
theorem B1400399 : Blo 487790 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B5562269 : Blo 487790 5562269 := bstep (se 3 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 5562269 = 2085851) B2085851
theorem B3727619 : Blo 487790 3727619 := bstep (se 1 (by rfl) ⟨2795714, by rfl⟩ : syracuseStep 3727619 = 5591429) B5591429
theorem B1106207 : Blo 487790 1106207 := bstep (se 1 (by rfl) ⟨829655, by rfl⟩ : syracuseStep 1106207 = 1659311) B1659311
theorem B549247 : Blo 487790 549247 := bstep (se 1 (by rfl) ⟨411935, by rfl⟩ : syracuseStep 549247 = 823871) B823871
theorem B12771715 : Blo 487790 12771715 := bstep (se 1 (by rfl) ⟨9578786, by rfl⟩ : syracuseStep 12771715 = 19157573) B19157573
theorem B3957659 : Blo 487790 3957659 := bstep (se 1 (by rfl) ⟨2968244, by rfl⟩ : syracuseStep 3957659 = 5936489) B5936489
theorem B1991803 : Blo 487790 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B6251813 : Blo 487790 6251813 := bstep (se 4 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 6251813 = 1172215) B1172215
theorem B1861001 : Blo 487790 1861001 := bstep (se 2 (by rfl) ⟨697875, by rfl⟩ : syracuseStep 1861001 = 1395751) B1395751
theorem B1762937 : Blo 487790 1762937 := bstep (se 2 (by rfl) ⟨661101, by rfl⟩ : syracuseStep 1762937 = 1322203) B1322203
theorem B2647673 : Blo 487790 2647673 := bstep (se 2 (by rfl) ⟨992877, by rfl⟩ : syracuseStep 2647673 = 1985755) B1985755
theorem B550651 : Blo 487790 550651 := bstep (se 1 (by rfl) ⟨412988, by rfl⟩ : syracuseStep 550651 = 825977) B825977
theorem B550687 : Blo 487790 550687 := bstep (se 1 (by rfl) ⟨413015, by rfl⟩ : syracuseStep 550687 = 826031) B826031
theorem B3172297 : Blo 487790 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B5597261 : Blo 487790 5597261 := bstep (se 3 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 5597261 = 2098973) B2098973
theorem B1239583 : Blo 487790 1239583 := bstep (se 1 (by rfl) ⟨929687, by rfl⟩ : syracuseStep 1239583 = 1859375) B1859375
theorem B1043131 : Blo 487790 1043131 := bstep (se 1 (by rfl) ⟨782348, by rfl⟩ : syracuseStep 1043131 = 1564697) B1564697
theorem B5040899 : Blo 487790 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B551839 : Blo 487790 551839 := bstep (se 1 (by rfl) ⟨413879, by rfl⟩ : syracuseStep 551839 = 827759) B827759
theorem B551983 : Blo 487790 551983 := bstep (se 1 (by rfl) ⟨413987, by rfl⟩ : syracuseStep 551983 = 827975) B827975
theorem B1862777 : Blo 487790 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B2092175 : Blo 487790 2092175 := bstep (se 1 (by rfl) ⟨1569131, by rfl⟩ : syracuseStep 2092175 = 3138263) B3138263
theorem B1764551 : Blo 487790 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B617807 : Blo 487790 617807 := bstep (se 1 (by rfl) ⟨463355, by rfl⟩ : syracuseStep 617807 = 926711) B926711
theorem B552271 : Blo 487790 552271 := bstep (se 1 (by rfl) ⟨414203, by rfl⟩ : syracuseStep 552271 = 828407) B828407
theorem B2157911 : Blo 487790 2157911 := bstep (se 1 (by rfl) ⟨1618433, by rfl⟩ : syracuseStep 2157911 = 3236867) B3236867
theorem B4779415 : Blo 487790 4779415 := bstep (se 1 (by rfl) ⟨3584561, by rfl⟩ : syracuseStep 4779415 = 7169123) B7169123
theorem B617959 : Blo 487790 617959 := bstep (se 1 (by rfl) ⟨463469, by rfl⟩ : syracuseStep 617959 = 926939) B926939
theorem B1568413 : Blo 487790 1568413 := bstep (se 3 (by rfl) ⟨294077, by rfl⟩ : syracuseStep 1568413 = 588155) B588155
theorem B552775 : Blo 487790 552775 := bstep (se 1 (by rfl) ⟨414581, by rfl⟩ : syracuseStep 552775 = 829163) B829163
theorem B2944907 : Blo 487790 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B2355389 : Blo 487790 2355389 := bstep (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) B883271
theorem B2126089 : Blo 487790 2126089 := bstep (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) B1594567
theorem B2486537 : Blo 487790 2486537 := bstep (se 2 (by rfl) ⟨932451, by rfl⟩ : syracuseStep 2486537 = 1864903) B1864903
theorem B487807 : Blo 487790 487807 := bstep (se 1 (by rfl) ⟨365855, by rfl⟩ : syracuseStep 487807 = 731711) B731711
theorem B487887 : Blo 487790 487887 := bstep (se 1 (by rfl) ⟨365915, by rfl⟩ : syracuseStep 487887 = 731831) B731831
theorem B488039 : Blo 487790 488039 := bstep (se 1 (by rfl) ⟨366029, by rfl⟩ : syracuseStep 488039 = 732059) B732059
theorem B488303 : Blo 487790 488303 := bstep (se 1 (by rfl) ⟨366227, by rfl⟩ : syracuseStep 488303 = 732455) B732455
theorem B488359 : Blo 487790 488359 := bstep (se 1 (by rfl) ⟨366269, by rfl⟩ : syracuseStep 488359 = 732539) B732539
theorem B783271 : Blo 487790 783271 := bstep (se 1 (by rfl) ⟨587453, by rfl⟩ : syracuseStep 783271 = 1174907) B1174907
theorem B488443 : Blo 487790 488443 := bstep (se 1 (by rfl) ⟨366332, by rfl⟩ : syracuseStep 488443 = 732665) B732665
theorem B488511 : Blo 487790 488511 := bstep (se 1 (by rfl) ⟨366383, by rfl⟩ : syracuseStep 488511 = 732767) B732767
theorem B1242175 : Blo 487790 1242175 := bstep (se 1 (by rfl) ⟨931631, by rfl⟩ : syracuseStep 1242175 = 1863263) B1863263
theorem B881771 : Blo 487790 881771 := bstep (se 1 (by rfl) ⟨661328, by rfl⟩ : syracuseStep 881771 = 1322657) B1322657
theorem B1242287 : Blo 487790 1242287 := bstep (se 1 (by rfl) ⟨931715, by rfl⟩ : syracuseStep 1242287 = 1863431) B1863431
theorem B488655 : Blo 487790 488655 := bstep (se 1 (by rfl) ⟨366491, by rfl⟩ : syracuseStep 488655 = 732983) B732983
theorem B1570079 : Blo 487790 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B6354227 : Blo 487790 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B488859 : Blo 487790 488859 := bstep (se 1 (by rfl) ⟨366644, by rfl⟩ : syracuseStep 488859 = 733289) B733289
theorem B5633545 : Blo 487790 5633545 := bstep (se 2 (by rfl) ⟨2112579, by rfl⟩ : syracuseStep 5633545 = 4225159) B4225159
theorem B882247 : Blo 487790 882247 := bstep (se 1 (by rfl) ⟨661685, by rfl⟩ : syracuseStep 882247 = 1323371) B1323371
theorem B521839 : Blo 487790 521839 := bstep (se 1 (by rfl) ⟨391379, by rfl⟩ : syracuseStep 521839 = 782759) B782759
theorem B489071 : Blo 487790 489071 := bstep (se 1 (by rfl) ⟨366803, by rfl⟩ : syracuseStep 489071 = 733607) B733607
theorem B489127 : Blo 487790 489127 := bstep (se 1 (by rfl) ⟨366845, by rfl⟩ : syracuseStep 489127 = 733691) B733691
theorem B7141067 : Blo 487790 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B784091 : Blo 487790 784091 := bstep (se 1 (by rfl) ⟨588068, by rfl⟩ : syracuseStep 784091 = 1176137) B1176137
theorem B489211 : Blo 487790 489211 := bstep (se 1 (by rfl) ⟨366908, by rfl⟩ : syracuseStep 489211 = 733817) B733817
theorem B1046267 : Blo 487790 1046267 := bstep (se 1 (by rfl) ⟨784700, by rfl⟩ : syracuseStep 1046267 = 1569401) B1569401
theorem B5306107 : Blo 487790 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B489247 : Blo 487790 489247 := bstep (se 1 (by rfl) ⟨366935, by rfl⟩ : syracuseStep 489247 = 733871) B733871
theorem B489279 : Blo 487790 489279 := bstep (se 1 (by rfl) ⟨366959, by rfl⟩ : syracuseStep 489279 = 733919) B733919
theorem B489455 : Blo 487790 489455 := bstep (se 1 (by rfl) ⟨367091, by rfl⟩ : syracuseStep 489455 = 734183) B734183
theorem B1210351 : Blo 487790 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B11892815 : Blo 487790 11892815 := bstep (se 1 (by rfl) ⟨8919611, by rfl⟩ : syracuseStep 11892815 = 17839223) B17839223
theorem B489627 : Blo 487790 489627 := bstep (se 1 (by rfl) ⟨367220, by rfl⟩ : syracuseStep 489627 = 734441) B734441
theorem B489663 : Blo 487790 489663 := bstep (se 1 (by rfl) ⟨367247, by rfl⟩ : syracuseStep 489663 = 734495) B734495
theorem B620779 : Blo 487790 620779 := bstep (se 1 (by rfl) ⟨465584, by rfl⟩ : syracuseStep 620779 = 931169) B931169
theorem B1177897 : Blo 487790 1177897 := bstep (se 2 (by rfl) ⟨441711, by rfl⟩ : syracuseStep 1177897 = 883423) B883423
theorem B489775 : Blo 487790 489775 := bstep (se 1 (by rfl) ⟨367331, by rfl⟩ : syracuseStep 489775 = 734663) B734663
theorem B490011 : Blo 487790 490011 := bstep (se 1 (by rfl) ⟨367508, by rfl⟩ : syracuseStep 490011 = 735017) B735017
theorem B490015 : Blo 487790 490015 := bstep (se 1 (by rfl) ⟨367511, by rfl⟩ : syracuseStep 490015 = 735023) B735023
theorem B490331 : Blo 487790 490331 := bstep (se 1 (by rfl) ⟨367748, by rfl⟩ : syracuseStep 490331 = 735497) B735497
theorem B588703 : Blo 487790 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B490399 : Blo 487790 490399 := bstep (se 1 (by rfl) ⟨367799, by rfl⟩ : syracuseStep 490399 = 735599) B735599
theorem B490543 : Blo 487790 490543 := bstep (se 1 (by rfl) ⟨367907, by rfl⟩ : syracuseStep 490543 = 735815) B735815
theorem B490567 : Blo 487790 490567 := bstep (se 1 (by rfl) ⟨367925, by rfl⟩ : syracuseStep 490567 = 735851) B735851
theorem B1244231 : Blo 487790 1244231 := bstep (se 1 (by rfl) ⟨933173, by rfl⟩ : syracuseStep 1244231 = 1866347) B1866347
theorem B4193369 : Blo 487790 4193369 := bstep (se 2 (by rfl) ⟨1572513, by rfl⟩ : syracuseStep 4193369 = 3145027) B3145027
theorem B621751 : Blo 487790 621751 := bstep (se 1 (by rfl) ⟨466313, by rfl⟩ : syracuseStep 621751 = 932627) B932627
theorem B490719 : Blo 487790 490719 := bstep (se 1 (by rfl) ⟨368039, by rfl⟩ : syracuseStep 490719 = 736079) B736079
theorem B490983 : Blo 487790 490983 := bstep (se 1 (by rfl) ⟨368237, by rfl⟩ : syracuseStep 490983 = 736475) B736475
theorem B1408519 : Blo 487790 1408519 := bstep (se 1 (by rfl) ⟨1056389, by rfl⟩ : syracuseStep 1408519 = 2112779) B2112779
theorem B491099 : Blo 487790 491099 := bstep (se 1 (by rfl) ⟨368324, by rfl⟩ : syracuseStep 491099 = 736649) B736649
theorem B622171 : Blo 487790 622171 := bstep (se 1 (by rfl) ⟨466628, by rfl⟩ : syracuseStep 622171 = 933257) B933257
theorem B5963489 : Blo 487790 5963489 := bstep (se 2 (by rfl) ⟨2236308, by rfl⟩ : syracuseStep 5963489 = 4472617) B4472617
theorem B491335 : Blo 487790 491335 := bstep (se 1 (by rfl) ⟨368501, by rfl⟩ : syracuseStep 491335 = 737003) B737003
theorem B491487 : Blo 487790 491487 := bstep (se 1 (by rfl) ⟨368615, by rfl⟩ : syracuseStep 491487 = 737231) B737231
theorem B491711 : Blo 487790 491711 := bstep (se 1 (by rfl) ⟨368783, by rfl⟩ : syracuseStep 491711 = 737567) B737567
theorem B491727 : Blo 487790 491727 := bstep (se 1 (by rfl) ⟨368795, by rfl⟩ : syracuseStep 491727 = 737591) B737591
theorem B786667 : Blo 487790 786667 := bstep (se 1 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 786667 = 1180001) B1180001
theorem B491775 : Blo 487790 491775 := bstep (se 1 (by rfl) ⟨368831, by rfl⟩ : syracuseStep 491775 = 737663) B737663
theorem B8389331 : Blo 487790 8389331 := bstep (se 1 (by rfl) ⟨6291998, by rfl⟩ : syracuseStep 8389331 = 12583997) B12583997
theorem B1344455 : Blo 487790 1344455 := bstep (se 1 (by rfl) ⟨1008341, by rfl⟩ : syracuseStep 1344455 = 2016683) B2016683
theorem B9405557 : Blo 487790 9405557 := bstep (se 5 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 9405557 = 881771) B881771
theorem B4785419 : Blo 487790 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B4195759 : Blo 487790 4195759 := bstep (se 1 (by rfl) ⟨3146819, by rfl⟩ : syracuseStep 4195759 = 6293639) B6293639
theorem B2655737 : Blo 487790 2655737 := bstep (se 2 (by rfl) ⟨995901, by rfl⟩ : syracuseStep 2655737 = 1991803) B1991803
theorem B5867113 : Blo 487790 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B16910045 : Blo 487790 16910045 := bstep (se 3 (by rfl) ⟨3170633, by rfl⟩ : syracuseStep 16910045 = 6341267) B6341267
theorem B6883379 : Blo 487790 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B3705263 : Blo 487790 3705263 := bstep (se 1 (by rfl) ⟨2778947, by rfl⟩ : syracuseStep 3705263 = 5557895) B5557895
theorem B4459009 : Blo 487790 4459009 := bstep (se 2 (by rfl) ⟨1672128, by rfl⟩ : syracuseStep 4459009 = 3344257) B3344257
theorem B4229729 : Blo 487790 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B2362193 : Blo 487790 2362193 := bstep (se 2 (by rfl) ⟨885822, by rfl⟩ : syracuseStep 2362193 = 1771645) B1771645
theorem B756649 : Blo 487790 756649 := bstep (se 2 (by rfl) ⟨283743, by rfl⟩ : syracuseStep 756649 = 567487) B567487
theorem B36342755 : Blo 487790 36342755 := bstep (se 1 (by rfl) ⟨27257066, by rfl⟩ : syracuseStep 36342755 = 54514133) B54514133
theorem B823351 : Blo 487790 823351 := bstep (se 1 (by rfl) ⟨617513, by rfl⟩ : syracuseStep 823351 = 1235027) B1235027
theorem B823675 : Blo 487790 823675 := bstep (se 1 (by rfl) ⟨617756, by rfl⟩ : syracuseStep 823675 = 1235513) B1235513
theorem B7082599 : Blo 487790 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B823945 : Blo 487790 823945 := bstep (se 2 (by rfl) ⟨308979, by rfl⟩ : syracuseStep 823945 = 617959) B617959
theorem B1119059 : Blo 487790 1119059 := bstep (se 1 (by rfl) ⟨839294, by rfl⟩ : syracuseStep 1119059 = 1678589) B1678589
theorem B824303 : Blo 487790 824303 := bstep (se 1 (by rfl) ⟨618227, by rfl⟩ : syracuseStep 824303 = 1236455) B1236455
theorem B10556513 : Blo 487790 10556513 := bstep (se 2 (by rfl) ⟨3958692, by rfl⟩ : syracuseStep 10556513 = 7917385) B7917385
theorem B3708179 : Blo 487790 3708179 := bstep (se 1 (by rfl) ⟨2781134, by rfl⟩ : syracuseStep 3708179 = 5562269) B5562269
theorem B35755505 : Blo 487790 35755505 := bstep (se 2 (by rfl) ⟨13408314, by rfl⟩ : syracuseStep 35755505 = 26816629) B26816629
theorem B4167875 : Blo 487790 4167875 := bstep (se 1 (by rfl) ⟨3125906, by rfl⟩ : syracuseStep 4167875 = 6251813) B6251813
theorem B597223 : Blo 487790 597223 := bstep (se 1 (by rfl) ⟨447917, by rfl⟩ : syracuseStep 597223 = 895835) B895835
theorem B7511393 : Blo 487790 7511393 := bstep (se 2 (by rfl) ⟨2816772, by rfl⟩ : syracuseStep 7511393 = 5633545) B5633545
theorem B695785 : Blo 487790 695785 := bstep (se 2 (by rfl) ⟨260919, by rfl⟩ : syracuseStep 695785 = 521839) B521839
theorem B9444923 : Blo 487790 9444923 := bstep (se 1 (by rfl) ⟨7083692, by rfl⟩ : syracuseStep 9444923 = 14167385) B14167385
theorem B3350443 : Blo 487790 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B991199 : Blo 487790 991199 := bstep (se 1 (by rfl) ⟨743399, by rfl⟩ : syracuseStep 991199 = 1486799) B1486799
theorem B1613801 : Blo 487790 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B827705 : Blo 487790 827705 := bstep (se 2 (by rfl) ⟨310389, by rfl⟩ : syracuseStep 827705 = 620779) B620779
theorem B1647323 : Blo 487790 1647323 := bstep (se 1 (by rfl) ⟨1235492, by rfl⟩ : syracuseStep 1647323 = 2470985) B2470985
theorem B828191 : Blo 487790 828191 := bstep (se 1 (by rfl) ⟨621143, by rfl⟩ : syracuseStep 828191 = 1242287) B1242287
theorem B4236151 : Blo 487790 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B1647485 : Blo 487790 1647485 := bstep (se 3 (by rfl) ⟨308903, by rfl⟩ : syracuseStep 1647485 = 617807) B617807
theorem B4760711 : Blo 487790 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B1647755 : Blo 487790 1647755 := bstep (se 1 (by rfl) ⟨1235816, by rfl⟩ : syracuseStep 1647755 = 2471633) B2471633
theorem B697511 : Blo 487790 697511 := bstep (se 1 (by rfl) ⟨523133, by rfl⟩ : syracuseStep 697511 = 1046267) B1046267
theorem B829001 : Blo 487790 829001 := bstep (se 2 (by rfl) ⟨310875, by rfl⟩ : syracuseStep 829001 = 621751) B621751
theorem B64563077 : Blo 487790 64563077 := bstep (se 4 (by rfl) ⟨6052788, by rfl⟩ : syracuseStep 64563077 = 12105577) B12105577
theorem B1878025 : Blo 487790 1878025 := bstep (se 2 (by rfl) ⟨704259, by rfl⟩ : syracuseStep 1878025 = 1408519) B1408519
theorem B829487 : Blo 487790 829487 := bstep (se 1 (by rfl) ⟨622115, by rfl⟩ : syracuseStep 829487 = 1244231) B1244231
theorem B2795579 : Blo 487790 2795579 := bstep (se 1 (by rfl) ⟨2096684, by rfl⟩ : syracuseStep 2795579 = 4193369) B4193369
theorem B927865 : Blo 487790 927865 := bstep (se 2 (by rfl) ⟨347949, by rfl⟩ : syracuseStep 927865 = 695899) B695899
theorem B829561 : Blo 487790 829561 := bstep (se 2 (by rfl) ⟨311085, by rfl⟩ : syracuseStep 829561 = 622171) B622171
theorem B5286221 : Blo 487790 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B3975659 : Blo 487790 3975659 := bstep (se 1 (by rfl) ⟨2981744, by rfl⟩ : syracuseStep 3975659 = 5963489) B5963489
theorem B1649375 : Blo 487790 1649375 := bstep (se 1 (by rfl) ⟨1237031, by rfl⟩ : syracuseStep 1649375 = 2474063) B2474063
theorem B3714011 : Blo 487790 3714011 := bstep (se 1 (by rfl) ⟨2785508, by rfl⟩ : syracuseStep 3714011 = 5571017) B5571017
theorem B732329 : Blo 487790 732329 := bstep (se 2 (by rfl) ⟨274623, by rfl⟩ : syracuseStep 732329 = 549247) B549247
theorem B3517775 : Blo 487790 3517775 := bstep (se 1 (by rfl) ⟨2638331, by rfl⟩ : syracuseStep 3517775 = 5276663) B5276663
theorem B732743 : Blo 487790 732743 := bstep (se 1 (by rfl) ⟨549557, by rfl⟩ : syracuseStep 732743 = 1099115) B1099115
theorem B1912427 : Blo 487790 1912427 := bstep (se 1 (by rfl) ⟨1434320, by rfl⟩ : syracuseStep 1912427 = 2868641) B2868641
theorem B732923 : Blo 487790 732923 := bstep (se 1 (by rfl) ⟨549692, by rfl⟩ : syracuseStep 732923 = 1099385) B1099385
theorem B2273129 : Blo 487790 2273129 := bstep (se 2 (by rfl) ⟨852423, by rfl⟩ : syracuseStep 2273129 = 1704847) B1704847
theorem B733595 : Blo 487790 733595 := bstep (se 1 (by rfl) ⟨550196, by rfl⟩ : syracuseStep 733595 = 1100393) B1100393
theorem B734015 : Blo 487790 734015 := bstep (se 1 (by rfl) ⟨550511, by rfl⟩ : syracuseStep 734015 = 1101023) B1101023
theorem B8926031 : Blo 487790 8926031 := bstep (se 1 (by rfl) ⟨6694523, by rfl⟩ : syracuseStep 8926031 = 13389047) B13389047
theorem B734159 : Blo 487790 734159 := bstep (se 1 (by rfl) ⟨550619, by rfl⟩ : syracuseStep 734159 = 1101239) B1101239
theorem B603119 : Blo 487790 603119 := bstep (se 1 (by rfl) ⟨452339, by rfl⟩ : syracuseStep 603119 = 904679) B904679
theorem B734201 : Blo 487790 734201 := bstep (se 2 (by rfl) ⟨275325, by rfl⟩ : syracuseStep 734201 = 550651) B550651
theorem B734249 : Blo 487790 734249 := bstep (se 2 (by rfl) ⟨275343, by rfl⟩ : syracuseStep 734249 = 550687) B550687
theorem B734279 : Blo 487790 734279 := bstep (se 1 (by rfl) ⟨550709, by rfl⟩ : syracuseStep 734279 = 1101419) B1101419
theorem B898231 : Blo 487790 898231 := bstep (se 1 (by rfl) ⟨673673, by rfl⟩ : syracuseStep 898231 = 1347347) B1347347
theorem B2798813 : Blo 487790 2798813 := bstep (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) B1049555
theorem B734459 : Blo 487790 734459 := bstep (se 1 (by rfl) ⟨550844, by rfl⟩ : syracuseStep 734459 = 1101689) B1101689
theorem B1587073 : Blo 487790 1587073 := bstep (se 2 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 1587073 = 1190305) B1190305
theorem B1652777 : Blo 487790 1652777 := bstep (se 2 (by rfl) ⟨619791, by rfl⟩ : syracuseStep 1652777 = 1239583) B1239583
theorem B1390841 : Blo 487790 1390841 := bstep (se 2 (by rfl) ⟨521565, by rfl⟩ : syracuseStep 1390841 = 1043131) B1043131
theorem B735695 : Blo 487790 735695 := bstep (se 1 (by rfl) ⟨551771, by rfl⟩ : syracuseStep 735695 = 1103543) B1103543
theorem B735785 : Blo 487790 735785 := bstep (se 2 (by rfl) ⟨275919, by rfl⟩ : syracuseStep 735785 = 551839) B551839
theorem B670441 : Blo 487790 670441 := bstep (se 2 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 670441 = 502831) B502831
theorem B735977 : Blo 487790 735977 := bstep (se 2 (by rfl) ⟨275991, by rfl⟩ : syracuseStep 735977 = 551983) B551983
theorem B736361 : Blo 487790 736361 := bstep (se 2 (by rfl) ⟨276135, by rfl⟩ : syracuseStep 736361 = 552271) B552271
theorem B6372553 : Blo 487790 6372553 := bstep (se 2 (by rfl) ⟨2389707, by rfl⟩ : syracuseStep 6372553 = 4779415) B4779415
theorem B3783905 : Blo 487790 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B736487 : Blo 487790 736487 := bstep (se 1 (by rfl) ⟨552365, by rfl⟩ : syracuseStep 736487 = 1104731) B1104731
theorem B1195343 : Blo 487790 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B933439 : Blo 487790 933439 := bstep (se 1 (by rfl) ⟨700079, by rfl⟩ : syracuseStep 933439 = 1400159) B1400159
theorem B736991 : Blo 487790 736991 := bstep (se 1 (by rfl) ⟨552743, by rfl⟩ : syracuseStep 736991 = 1105487) B1105487
theorem B933599 : Blo 487790 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B737033 : Blo 487790 737033 := bstep (se 2 (by rfl) ⟨276387, by rfl⟩ : syracuseStep 737033 = 552775) B552775
theorem B1097639 : Blo 487790 1097639 := bstep (se 1 (by rfl) ⟨823229, by rfl⟩ : syracuseStep 1097639 = 1646459) B1646459
theorem B737471 : Blo 487790 737471 := bstep (se 1 (by rfl) ⟨553103, by rfl⟩ : syracuseStep 737471 = 1106207) B1106207
theorem B1097963 : Blo 487790 1097963 := bstep (se 1 (by rfl) ⟨823472, by rfl⟩ : syracuseStep 1097963 = 1646945) B1646945
theorem B2834785 : Blo 487790 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B2638439 : Blo 487790 2638439 := bstep (se 1 (by rfl) ⟨1978829, by rfl⟩ : syracuseStep 2638439 = 3957659) B3957659
theorem B3588943 : Blo 487790 3588943 := bstep (se 1 (by rfl) ⟨2691707, by rfl⟩ : syracuseStep 3588943 = 5383415) B5383415
theorem B1098863 : Blo 487790 1098863 := bstep (se 1 (by rfl) ⟨824147, by rfl⟩ : syracuseStep 1098863 = 1648295) B1648295
theorem B1656233 : Blo 487790 1656233 := bstep (se 2 (by rfl) ⟨621087, by rfl⟩ : syracuseStep 1656233 = 1242175) B1242175
theorem B1099259 : Blo 487790 1099259 := bstep (se 1 (by rfl) ⟨824444, by rfl⟩ : syracuseStep 1099259 = 1648889) B1648889
theorem B1099295 : Blo 487790 1099295 := bstep (se 1 (by rfl) ⟨824471, by rfl⟩ : syracuseStep 1099295 = 1648943) B1648943
theorem B3720815 : Blo 487790 3720815 := bstep (se 1 (by rfl) ⟨2790611, by rfl⟩ : syracuseStep 3720815 = 5581223) B5581223
theorem B1099439 : Blo 487790 1099439 := bstep (se 1 (by rfl) ⟨824579, by rfl⟩ : syracuseStep 1099439 = 1649159) B1649159
theorem B3360599 : Blo 487790 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B1099871 : Blo 487790 1099871 := bstep (se 1 (by rfl) ⟨824903, by rfl⟩ : syracuseStep 1099871 = 1649807) B1649807
theorem B1394783 : Blo 487790 1394783 := bstep (se 1 (by rfl) ⟨1046087, by rfl⟩ : syracuseStep 1394783 = 2092175) B2092175
theorem B1100159 : Blo 487790 1100159 := bstep (se 1 (by rfl) ⟨825119, by rfl⟩ : syracuseStep 1100159 = 1650239) B1650239
theorem B1100627 : Blo 487790 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B1657691 : Blo 487790 1657691 := bstep (se 1 (by rfl) ⟨1243268, by rfl⟩ : syracuseStep 1657691 = 2486537) B2486537
theorem B1100987 : Blo 487790 1100987 := bstep (se 1 (by rfl) ⟨825740, by rfl⟩ : syracuseStep 1100987 = 1651481) B1651481
theorem B1854697 : Blo 487790 1854697 := bstep (se 2 (by rfl) ⟨695511, by rfl⟩ : syracuseStep 1854697 = 1391023) B1391023
theorem B1101167 : Blo 487790 1101167 := bstep (se 1 (by rfl) ⟨825875, by rfl⟩ : syracuseStep 1101167 = 1651751) B1651751
theorem B2477951 : Blo 487790 2477951 := bstep (se 1 (by rfl) ⟨1858463, by rfl⟩ : syracuseStep 2477951 = 3716927) B3716927
theorem B8376209 : Blo 487790 8376209 := bstep (se 2 (by rfl) ⟨3141078, by rfl⟩ : syracuseStep 8376209 = 6282157) B6282157
theorem B1101887 : Blo 487790 1101887 := bstep (se 1 (by rfl) ⟨826415, by rfl⟩ : syracuseStep 1101887 = 1652831) B1652831
theorem B1888379 : Blo 487790 1888379 := bstep (se 1 (by rfl) ⟨1416284, by rfl⟩ : syracuseStep 1888379 = 2832569) B2832569
theorem B2478275 : Blo 487790 2478275 := bstep (se 1 (by rfl) ⟨1858706, by rfl⟩ : syracuseStep 2478275 = 3717413) B3717413
theorem B1102121 : Blo 487790 1102121 := bstep (se 2 (by rfl) ⟨413295, by rfl⟩ : syracuseStep 1102121 = 826591) B826591
theorem B3723731 : Blo 487790 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B1102391 : Blo 487790 1102391 := bstep (se 1 (by rfl) ⟨826793, by rfl⟩ : syracuseStep 1102391 = 1653587) B1653587
theorem B1102697 : Blo 487790 1102697 := bstep (se 2 (by rfl) ⟨413511, by rfl⟩ : syracuseStep 1102697 = 827023) B827023
theorem B1102751 : Blo 487790 1102751 := bstep (se 1 (by rfl) ⟨827063, by rfl⟩ : syracuseStep 1102751 = 1654127) B1654127
theorem B2479085 : Blo 487790 2479085 := bstep (se 3 (by rfl) ⟨464828, by rfl⟩ : syracuseStep 2479085 = 929657) B929657
theorem B5559353 : Blo 487790 5559353 := bstep (se 2 (by rfl) ⟨2084757, by rfl⟩ : syracuseStep 5559353 = 4169515) B4169515
theorem B1103003 : Blo 487790 1103003 := bstep (se 1 (by rfl) ⟨827252, by rfl⟩ : syracuseStep 1103003 = 1654505) B1654505
theorem B26760577 : Blo 487790 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B13981081 : Blo 487790 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B5297633 : Blo 487790 5297633 := bstep (se 2 (by rfl) ⟨1986612, by rfl⟩ : syracuseStep 5297633 = 3973225) B3973225
theorem B1103579 : Blo 487790 1103579 := bstep (se 1 (by rfl) ⟨827684, by rfl⟩ : syracuseStep 1103579 = 1655369) B1655369
theorem B2479895 : Blo 487790 2479895 := bstep (se 1 (by rfl) ⟨1859921, by rfl⟩ : syracuseStep 2479895 = 3719843) B3719843
theorem B1103687 : Blo 487790 1103687 := bstep (se 1 (by rfl) ⟨827765, by rfl⟩ : syracuseStep 1103687 = 1655531) B1655531
theorem B17028953 : Blo 487790 17028953 := bstep (se 2 (by rfl) ⟨6385857, by rfl⟩ : syracuseStep 17028953 = 12771715) B12771715
theorem B1235483 : Blo 487790 1235483 := bstep (se 1 (by rfl) ⟨926612, by rfl⟩ : syracuseStep 1235483 = 1853225) B1853225
theorem B1104695 : Blo 487790 1104695 := bstep (se 1 (by rfl) ⟨828521, by rfl⟩ : syracuseStep 1104695 = 1657043) B1657043
theorem B1399771 : Blo 487790 1399771 := bstep (se 1 (by rfl) ⟨1049828, by rfl⟩ : syracuseStep 1399771 = 2099657) B2099657
theorem B1104875 : Blo 487790 1104875 := bstep (se 1 (by rfl) ⟨828656, by rfl⟩ : syracuseStep 1104875 = 1657313) B1657313
theorem B2481515 : Blo 487790 2481515 := bstep (se 1 (by rfl) ⟨1861136, by rfl⟩ : syracuseStep 2481515 = 3722273) B3722273
theorem B1236647 : Blo 487790 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B3727133 : Blo 487790 3727133 := bstep (se 3 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 3727133 = 1397675) B1397675
theorem B2088791 : Blo 487790 2088791 := bstep (se 1 (by rfl) ⟨1566593, by rfl⟩ : syracuseStep 2088791 = 3133187) B3133187
theorem B1105775 : Blo 487790 1105775 := bstep (se 1 (by rfl) ⟨829331, by rfl⟩ : syracuseStep 1105775 = 1658663) B1658663
theorem B2482163 : Blo 487790 2482163 := bstep (se 1 (by rfl) ⟨1861622, by rfl⟩ : syracuseStep 2482163 = 3723245) B3723245
theorem B1761697 : Blo 487790 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B1565095 : Blo 487790 1565095 := bstep (se 1 (by rfl) ⟨1173821, by rfl⟩ : syracuseStep 1565095 = 2347643) B2347643
theorem B1106459 : Blo 487790 1106459 := bstep (se 1 (by rfl) ⟨829844, by rfl⟩ : syracuseStep 1106459 = 1659689) B1659689
theorem B10576925 : Blo 487790 10576925 := bstep (se 3 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 10576925 = 3966347) B3966347
theorem B550111 : Blo 487790 550111 := bstep (se 1 (by rfl) ⟨412583, by rfl⟩ : syracuseStep 550111 = 825167) B825167
theorem B2483459 : Blo 487790 2483459 := bstep (se 1 (by rfl) ⟨1862594, by rfl⟩ : syracuseStep 2483459 = 3725189) B3725189
theorem B2483783 : Blo 487790 2483783 := bstep (se 1 (by rfl) ⟨1862837, by rfl⟩ : syracuseStep 2483783 = 3725675) B3725675
theorem B2090909 : Blo 487790 2090909 := bstep (se 3 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 2090909 = 784091) B784091
theorem B550939 : Blo 487790 550939 := bstep (se 1 (by rfl) ⟨413204, by rfl⟩ : syracuseStep 550939 = 826409) B826409
theorem B1861775 : Blo 487790 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B2091217 : Blo 487790 2091217 := bstep (se 2 (by rfl) ⟨784206, by rfl⟩ : syracuseStep 2091217 = 1568413) B1568413
theorem B2485079 : Blo 487790 2485079 := bstep (se 1 (by rfl) ⟨1863809, by rfl⟩ : syracuseStep 2485079 = 3727619) B3727619
theorem B3566497 : Blo 487790 3566497 := bstep (se 2 (by rfl) ⟨1337436, by rfl⟩ : syracuseStep 3566497 = 2674873) B2674873
theorem B3173855 : Blo 487790 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B552415 : Blo 487790 552415 := bstep (se 1 (by rfl) ⟨414311, by rfl⟩ : syracuseStep 552415 = 828623) B828623
theorem B1240667 : Blo 487790 1240667 := bstep (se 1 (by rfl) ⟨930500, by rfl⟩ : syracuseStep 1240667 = 1861001) B1861001
theorem B1175291 : Blo 487790 1175291 := bstep (se 1 (by rfl) ⟨881468, by rfl⟩ : syracuseStep 1175291 = 1762937) B1762937
theorem B1765115 : Blo 487790 1765115 := bstep (se 1 (by rfl) ⟨1323836, by rfl⟩ : syracuseStep 1765115 = 2647673) B2647673
theorem B10841951 : Blo 487790 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B1044361 : Blo 487790 1044361 := bstep (se 2 (by rfl) ⟨391635, by rfl⟩ : syracuseStep 1044361 = 783271) B783271
theorem B552955 : Blo 487790 552955 := bstep (se 1 (by rfl) ⟨414716, by rfl⟩ : syracuseStep 552955 = 829433) B829433
theorem B3731507 : Blo 487790 3731507 := bstep (se 1 (by rfl) ⟨2798630, by rfl⟩ : syracuseStep 3731507 = 5597261) B5597261
theorem B553063 : Blo 487790 553063 := bstep (se 1 (by rfl) ⟨414797, by rfl⟩ : syracuseStep 553063 = 829595) B829595
theorem B553135 : Blo 487790 553135 := bstep (se 1 (by rfl) ⟨414851, by rfl⟩ : syracuseStep 553135 = 829703) B829703
theorem B487835 : Blo 487790 487835 := bstep (se 1 (by rfl) ⟨365876, by rfl⟩ : syracuseStep 487835 = 731753) B731753
theorem B488187 : Blo 487790 488187 := bstep (se 1 (by rfl) ⟨366140, by rfl⟩ : syracuseStep 488187 = 732281) B732281
theorem B1241851 : Blo 487790 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B1176329 : Blo 487790 1176329 := bstep (se 2 (by rfl) ⟨441123, by rfl⟩ : syracuseStep 1176329 = 882247) B882247
theorem B1176367 : Blo 487790 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B488255 : Blo 487790 488255 := bstep (se 1 (by rfl) ⟨366191, by rfl⟩ : syracuseStep 488255 = 732383) B732383
theorem B488283 : Blo 487790 488283 := bstep (se 1 (by rfl) ⟨366212, by rfl⟩ : syracuseStep 488283 = 732425) B732425
theorem B434664305 : Blo 487790 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B1438607 : Blo 487790 1438607 := bstep (se 1 (by rfl) ⟨1078955, by rfl⟩ : syracuseStep 1438607 = 2157911) B2157911
theorem B488351 : Blo 487790 488351 := bstep (se 1 (by rfl) ⟨366263, by rfl⟩ : syracuseStep 488351 = 732527) B732527
theorem B488431 : Blo 487790 488431 := bstep (se 1 (by rfl) ⟨366323, by rfl⟩ : syracuseStep 488431 = 732647) B732647
theorem B7074809 : Blo 487790 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B488519 : Blo 487790 488519 := bstep (se 1 (by rfl) ⟨366389, by rfl⟩ : syracuseStep 488519 = 732779) B732779
theorem B488603 : Blo 487790 488603 := bstep (se 1 (by rfl) ⟨366452, by rfl⟩ : syracuseStep 488603 = 732905) B732905
theorem B3765491 : Blo 487790 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B488699 : Blo 487790 488699 := bstep (se 1 (by rfl) ⟨366524, by rfl⟩ : syracuseStep 488699 = 733049) B733049
theorem B1963271 : Blo 487790 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B488767 : Blo 487790 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B1078601 : Blo 487790 1078601 := bstep (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) B808951
theorem B1570259 : Blo 487790 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B488935 : Blo 487790 488935 := bstep (se 1 (by rfl) ⟨366701, by rfl⟩ : syracuseStep 488935 = 733403) B733403
theorem B488943 : Blo 487790 488943 := bstep (se 1 (by rfl) ⟨366707, by rfl⟩ : syracuseStep 488943 = 733415) B733415
theorem B489051 : Blo 487790 489051 := bstep (se 1 (by rfl) ⟨366788, by rfl⟩ : syracuseStep 489051 = 733577) B733577
theorem B489115 : Blo 487790 489115 := bstep (se 1 (by rfl) ⟨366836, by rfl⟩ : syracuseStep 489115 = 733673) B733673
theorem B1570529 : Blo 487790 1570529 := bstep (se 2 (by rfl) ⟨588948, by rfl⟩ : syracuseStep 1570529 = 1177897) B1177897
theorem B489199 : Blo 487790 489199 := bstep (se 1 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 489199 = 733799) B733799
theorem B489287 : Blo 487790 489287 := bstep (se 1 (by rfl) ⟨366965, by rfl⟩ : syracuseStep 489287 = 733931) B733931
theorem B489307 : Blo 487790 489307 := bstep (se 1 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 489307 = 733961) B733961
theorem B489375 : Blo 487790 489375 := bstep (se 1 (by rfl) ⟨367031, by rfl⟩ : syracuseStep 489375 = 734063) B734063
theorem B489543 : Blo 487790 489543 := bstep (se 1 (by rfl) ⟨367157, by rfl⟩ : syracuseStep 489543 = 734315) B734315
theorem B1046719 : Blo 487790 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B489703 : Blo 487790 489703 := bstep (se 1 (by rfl) ⟨367277, by rfl⟩ : syracuseStep 489703 = 734555) B734555
theorem B489887 : Blo 487790 489887 := bstep (se 1 (by rfl) ⟨367415, by rfl⟩ : syracuseStep 489887 = 734831) B734831
theorem B1866179 : Blo 487790 1866179 := bstep (se 1 (by rfl) ⟨1399634, by rfl⟩ : syracuseStep 1866179 = 2799269) B2799269
theorem B489935 : Blo 487790 489935 := bstep (se 1 (by rfl) ⟨367451, by rfl⟩ : syracuseStep 489935 = 734903) B734903
theorem B489959 : Blo 487790 489959 := bstep (se 1 (by rfl) ⟨367469, by rfl⟩ : syracuseStep 489959 = 734939) B734939
theorem B784937 : Blo 487790 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B490075 : Blo 487790 490075 := bstep (se 1 (by rfl) ⟨367556, by rfl⟩ : syracuseStep 490075 = 735113) B735113
theorem B6257249 : Blo 487790 6257249 := bstep (se 2 (by rfl) ⟨2346468, by rfl⟩ : syracuseStep 6257249 = 4692937) B4692937
theorem B883343 : Blo 487790 883343 := bstep (se 1 (by rfl) ⟨662507, by rfl⟩ : syracuseStep 883343 = 1325015) B1325015
theorem B490143 : Blo 487790 490143 := bstep (se 1 (by rfl) ⟨367607, by rfl⟩ : syracuseStep 490143 = 735215) B735215
theorem B7928543 : Blo 487790 7928543 := bstep (se 1 (by rfl) ⟨5946407, by rfl⟩ : syracuseStep 7928543 = 11892815) B11892815
theorem B490311 : Blo 487790 490311 := bstep (se 1 (by rfl) ⟨367733, by rfl⟩ : syracuseStep 490311 = 735467) B735467
theorem B2653037 : Blo 487790 2653037 := bstep (se 3 (by rfl) ⟨497444, by rfl⟩ : syracuseStep 2653037 = 994889) B994889
theorem B490351 : Blo 487790 490351 := bstep (se 1 (by rfl) ⟨367763, by rfl⟩ : syracuseStep 490351 = 735527) B735527
theorem B490407 : Blo 487790 490407 := bstep (se 1 (by rfl) ⟨367805, by rfl⟩ : syracuseStep 490407 = 735611) B735611
theorem B490587 : Blo 487790 490587 := bstep (se 1 (by rfl) ⟨367940, by rfl⟩ : syracuseStep 490587 = 735881) B735881
theorem B490703 : Blo 487790 490703 := bstep (se 1 (by rfl) ⟨368027, by rfl⟩ : syracuseStep 490703 = 736055) B736055
theorem B490727 : Blo 487790 490727 := bstep (se 1 (by rfl) ⟨368045, by rfl⟩ : syracuseStep 490727 = 736091) B736091
theorem B490823 : Blo 487790 490823 := bstep (se 1 (by rfl) ⟨368117, by rfl⟩ : syracuseStep 490823 = 736235) B736235
theorem B490959 : Blo 487790 490959 := bstep (se 1 (by rfl) ⟨368219, by rfl⟩ : syracuseStep 490959 = 736439) B736439
theorem B1146475 : Blo 487790 1146475 := bstep (se 1 (by rfl) ⟨859856, by rfl⟩ : syracuseStep 1146475 = 1719713) B1719713
theorem B491119 : Blo 487790 491119 := bstep (se 1 (by rfl) ⟨368339, by rfl⟩ : syracuseStep 491119 = 736679) B736679
theorem B491175 : Blo 487790 491175 := bstep (se 1 (by rfl) ⟨368381, by rfl⟩ : syracuseStep 491175 = 736763) B736763
theorem B491239 : Blo 487790 491239 := bstep (se 1 (by rfl) ⟨368429, by rfl⟩ : syracuseStep 491239 = 736859) B736859
theorem B491295 : Blo 487790 491295 := bstep (se 1 (by rfl) ⟨368471, by rfl⟩ : syracuseStep 491295 = 736943) B736943
theorem B491375 : Blo 487790 491375 := bstep (se 1 (by rfl) ⟨368531, by rfl⟩ : syracuseStep 491375 = 737063) B737063
theorem B491431 : Blo 487790 491431 := bstep (se 1 (by rfl) ⟨368573, by rfl⟩ : syracuseStep 491431 = 737147) B737147
theorem B491647 : Blo 487790 491647 := bstep (se 1 (by rfl) ⟨368735, by rfl⟩ : syracuseStep 491647 = 737471) B737471
theorem B1048889 : Blo 487790 1048889 := bstep (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) B786667
theorem B1770491 : Blo 487790 1770491 := bstep (se 1 (by rfl) ⟨1327868, by rfl⟩ : syracuseStep 1770491 = 2655737) B2655737
theorem B4785257 : Blo 487790 4785257 := bstep (se 2 (by rfl) ⟨1794471, by rfl⟩ : syracuseStep 4785257 = 3588943) B3588943
theorem B11273363 : Blo 487790 11273363 := bstep (se 1 (by rfl) ⟨8455022, by rfl⟩ : syracuseStep 11273363 = 16910045) B16910045
theorem B4588919 : Blo 487790 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B2819819 : Blo 487790 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B1574795 : Blo 487790 1574795 := bstep (se 1 (by rfl) ⟨1181096, by rfl⟩ : syracuseStep 1574795 = 2362193) B2362193
theorem B1608317 : Blo 487790 1608317 := bstep (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) B603119
theorem B2788289 : Blo 487790 2788289 := bstep (se 2 (by rfl) ⟨1045608, by rfl⟩ : syracuseStep 2788289 = 2091217) B2091217
theorem B3706235 : Blo 487790 3706235 := bstep (se 1 (by rfl) ⟨2779676, by rfl⟩ : syracuseStep 3706235 = 5559353) B5559353
theorem B11505077 : Blo 487790 11505077 := bstep (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) B1078601
theorem B4755329 : Blo 487790 4755329 := bstep (se 2 (by rfl) ⟨1783248, by rfl⟩ : syracuseStep 4755329 = 3566497) B3566497
theorem B823655 : Blo 487790 823655 := bstep (se 1 (by rfl) ⟨617741, by rfl⟩ : syracuseStep 823655 = 1235483) B1235483
theorem B33854453 : Blo 487790 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B6296615 : Blo 487790 6296615 := bstep (se 1 (by rfl) ⟨4722461, by rfl⟩ : syracuseStep 6296615 = 9444923) B9444923
theorem B824431 : Blo 487790 824431 := bstep (se 1 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 824431 = 1236647) B1236647
theorem B660799 : Blo 487790 660799 := bstep (se 1 (by rfl) ⟨495599, by rfl⟩ : syracuseStep 660799 = 991199) B991199
theorem B7051283 : Blo 487790 7051283 := bstep (se 1 (by rfl) ⟨5288462, by rfl⟩ : syracuseStep 7051283 = 10576925) B10576925
theorem B9443465 : Blo 487790 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B3185189 : Blo 487790 3185189 := bstep (se 4 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 3185189 = 597223) B597223
theorem B827111 : Blo 487790 827111 := bstep (se 1 (by rfl) ⟨620333, by rfl⟩ : syracuseStep 827111 = 1240667) B1240667
theorem B1515419 : Blo 487790 1515419 := bstep (se 1 (by rfl) ⟨1136564, by rfl⟩ : syracuseStep 1515419 = 2273129) B2273129
theorem B289776203 : Blo 487790 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B959071 : Blo 487790 959071 := bstep (se 1 (by rfl) ⟨719303, by rfl⟩ : syracuseStep 959071 = 1438607) B1438607
theorem B893921 : Blo 487790 893921 := bstep (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) B670441
theorem B927227 : Blo 487790 927227 := bstep (se 1 (by rfl) ⟨695420, by rfl⟩ : syracuseStep 927227 = 1390841) B1390841
theorem B8496737 : Blo 487790 8496737 := bstep (se 2 (by rfl) ⟨3186276, by rfl⟩ : syracuseStep 8496737 = 6372553) B6372553
theorem B4171499 : Blo 487790 4171499 := bstep (se 1 (by rfl) ⟨3128624, by rfl⟩ : syracuseStep 4171499 = 6257249) B6257249
theorem B5285695 : Blo 487790 5285695 := bstep (se 1 (by rfl) ⟨3964271, by rfl⟩ : syracuseStep 5285695 = 7928543) B7928543
theorem B927713 : Blo 487790 927713 := bstep (se 2 (by rfl) ⟨347892, by rfl⟩ : syracuseStep 927713 = 695785) B695785
theorem B796895 : Blo 487790 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B4467257 : Blo 487790 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B4303469 : Blo 487790 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B731759 : Blo 487790 731759 := bstep (se 1 (by rfl) ⟨548819, by rfl⟩ : syracuseStep 731759 = 1097639) B1097639
theorem B731975 : Blo 487790 731975 := bstep (se 1 (by rfl) ⟨548981, by rfl⟩ : syracuseStep 731975 = 1097963) B1097963
theorem B3779713 : Blo 487790 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B896303 : Blo 487790 896303 := bstep (se 1 (by rfl) ⟨672227, by rfl⟩ : syracuseStep 896303 = 1344455) B1344455
theorem B732575 : Blo 487790 732575 := bstep (se 1 (by rfl) ⟨549431, by rfl⟩ : syracuseStep 732575 = 1098863) B1098863
theorem B6270371 : Blo 487790 6270371 := bstep (se 1 (by rfl) ⟨4702778, by rfl⟩ : syracuseStep 6270371 = 9405557) B9405557
theorem B3190279 : Blo 487790 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B732839 : Blo 487790 732839 := bstep (se 1 (by rfl) ⟨549629, by rfl⟩ : syracuseStep 732839 = 1099259) B1099259
theorem B732863 : Blo 487790 732863 := bstep (se 1 (by rfl) ⟨549647, by rfl⟩ : syracuseStep 732863 = 1099295) B1099295
theorem B732959 : Blo 487790 732959 := bstep (se 1 (by rfl) ⟨549719, by rfl⟩ : syracuseStep 732959 = 1099439) B1099439
theorem B5648201 : Blo 487790 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B2240399 : Blo 487790 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B733247 : Blo 487790 733247 := bstep (se 1 (by rfl) ⟨549935, by rfl⟩ : syracuseStep 733247 = 1099871) B1099871
theorem B929855 : Blo 487790 929855 := bstep (se 1 (by rfl) ⟨697391, by rfl⟩ : syracuseStep 929855 = 1394783) B1394783
theorem B733439 : Blo 487790 733439 := bstep (se 1 (by rfl) ⟨550079, by rfl⟩ : syracuseStep 733439 = 1100159) B1100159
theorem B2470175 : Blo 487790 2470175 := bstep (se 1 (by rfl) ⟨1852631, by rfl⟩ : syracuseStep 2470175 = 3705263) B3705263
theorem B733481 : Blo 487790 733481 := bstep (se 2 (by rfl) ⟨275055, by rfl⟩ : syracuseStep 733481 = 550111) B550111
theorem B733751 : Blo 487790 733751 := bstep (se 1 (by rfl) ⟨550313, by rfl⟩ : syracuseStep 733751 = 1100627) B1100627
theorem B24228503 : Blo 487790 24228503 := bstep (se 1 (by rfl) ⟨18171377, by rfl⟩ : syracuseStep 24228503 = 36342755) B36342755
theorem B733991 : Blo 487790 733991 := bstep (se 1 (by rfl) ⟨550493, by rfl⟩ : syracuseStep 733991 = 1100987) B1100987
theorem B734111 : Blo 487790 734111 := bstep (se 1 (by rfl) ⟨550583, by rfl⟩ : syracuseStep 734111 = 1101167) B1101167
theorem B1651967 : Blo 487790 1651967 := bstep (se 1 (by rfl) ⟨1238975, by rfl⟩ : syracuseStep 1651967 = 2477951) B2477951
theorem B5584139 : Blo 487790 5584139 := bstep (se 1 (by rfl) ⟨4188104, by rfl⟩ : syracuseStep 5584139 = 8376209) B8376209
theorem B2504033 : Blo 487790 2504033 := bstep (se 2 (by rfl) ⟨939012, by rfl⟩ : syracuseStep 2504033 = 1878025) B1878025
theorem B734585 : Blo 487790 734585 := bstep (se 2 (by rfl) ⟨275469, by rfl⟩ : syracuseStep 734585 = 550939) B550939
theorem B734591 : Blo 487790 734591 := bstep (se 1 (by rfl) ⟨550943, by rfl⟩ : syracuseStep 734591 = 1101887) B1101887
theorem B1258919 : Blo 487790 1258919 := bstep (se 1 (by rfl) ⟨944189, by rfl⟩ : syracuseStep 1258919 = 1888379) B1888379
theorem B1652183 : Blo 487790 1652183 := bstep (se 1 (by rfl) ⟨1239137, by rfl⟩ : syracuseStep 1652183 = 2478275) B2478275
theorem B734747 : Blo 487790 734747 := bstep (se 1 (by rfl) ⟨551060, by rfl⟩ : syracuseStep 734747 = 1102121) B1102121
theorem B734927 : Blo 487790 734927 := bstep (se 1 (by rfl) ⟨551195, by rfl⟩ : syracuseStep 734927 = 1102391) B1102391
theorem B735131 : Blo 487790 735131 := bstep (se 1 (by rfl) ⟨551348, by rfl⟩ : syracuseStep 735131 = 1102697) B1102697
theorem B735167 : Blo 487790 735167 := bstep (se 1 (by rfl) ⟨551375, by rfl⟩ : syracuseStep 735167 = 1102751) B1102751
theorem B1652723 : Blo 487790 1652723 := bstep (se 1 (by rfl) ⟨1239542, by rfl⟩ : syracuseStep 1652723 = 2479085) B2479085
theorem B5945345 : Blo 487790 5945345 := bstep (se 2 (by rfl) ⟨2229504, by rfl⟩ : syracuseStep 5945345 = 4459009) B4459009
theorem B735335 : Blo 487790 735335 := bstep (se 1 (by rfl) ⟨551501, by rfl⟩ : syracuseStep 735335 = 1103003) B1103003
theorem B2472119 : Blo 487790 2472119 := bstep (se 1 (by rfl) ⟨1854089, by rfl⟩ : syracuseStep 2472119 = 3708179) B3708179
theorem B23837003 : Blo 487790 23837003 := bstep (se 1 (by rfl) ⟨17877752, by rfl⟩ : syracuseStep 23837003 = 35755505) B35755505
theorem B735719 : Blo 487790 735719 := bstep (se 1 (by rfl) ⟨551789, by rfl⟩ : syracuseStep 735719 = 1103579) B1103579
theorem B1653263 : Blo 487790 1653263 := bstep (se 1 (by rfl) ⟨1239947, by rfl⟩ : syracuseStep 1653263 = 2479895) B2479895
theorem B735791 : Blo 487790 735791 := bstep (se 1 (by rfl) ⟨551843, by rfl⟩ : syracuseStep 735791 = 1103687) B1103687
theorem B11352635 : Blo 487790 11352635 := bstep (se 1 (by rfl) ⟨8514476, by rfl⟩ : syracuseStep 11352635 = 17028953) B17028953
theorem B2472929 : Blo 487790 2472929 := bstep (se 2 (by rfl) ⟨927348, by rfl⟩ : syracuseStep 2472929 = 1854697) B1854697
theorem B736463 : Blo 487790 736463 := bstep (se 1 (by rfl) ⟨552347, by rfl⟩ : syracuseStep 736463 = 1104695) B1104695
theorem B736553 : Blo 487790 736553 := bstep (se 2 (by rfl) ⟨276207, by rfl⟩ : syracuseStep 736553 = 552415) B552415
theorem B736583 : Blo 487790 736583 := bstep (se 1 (by rfl) ⟨552437, by rfl⟩ : syracuseStep 736583 = 1104875) B1104875
theorem B1654343 : Blo 487790 1654343 := bstep (se 1 (by rfl) ⟨1240757, by rfl⟩ : syracuseStep 1654343 = 2481515) B2481515
theorem B1392481 : Blo 487790 1392481 := bstep (se 2 (by rfl) ⟨522180, by rfl⟩ : syracuseStep 1392481 = 1044361) B1044361
theorem B1392527 : Blo 487790 1392527 := bstep (se 1 (by rfl) ⟨1044395, by rfl⟩ : syracuseStep 1392527 = 2088791) B2088791
theorem B737183 : Blo 487790 737183 := bstep (se 1 (by rfl) ⟨552887, by rfl⟩ : syracuseStep 737183 = 1105775) B1105775
theorem B1654775 : Blo 487790 1654775 := bstep (se 1 (by rfl) ⟨1241081, by rfl⟩ : syracuseStep 1654775 = 2482163) B2482163
theorem B737273 : Blo 487790 737273 := bstep (se 2 (by rfl) ⟨276477, by rfl⟩ : syracuseStep 737273 = 552955) B552955
theorem B1097801 : Blo 487790 1097801 := bstep (se 2 (by rfl) ⟨411675, by rfl⟩ : syracuseStep 1097801 = 823351) B823351
theorem B737417 : Blo 487790 737417 := bstep (se 2 (by rfl) ⟨276531, by rfl⟩ : syracuseStep 737417 = 553063) B553063
theorem B737513 : Blo 487790 737513 := bstep (se 2 (by rfl) ⟨276567, by rfl⟩ : syracuseStep 737513 = 553135) B553135
theorem B737639 : Blo 487790 737639 := bstep (se 1 (by rfl) ⟨553229, by rfl⟩ : syracuseStep 737639 = 1106459) B1106459
theorem B1098215 : Blo 487790 1098215 := bstep (se 1 (by rfl) ⟨823661, by rfl⟩ : syracuseStep 1098215 = 1647323) B1647323
theorem B1098233 : Blo 487790 1098233 := bstep (se 2 (by rfl) ⟨411837, by rfl⟩ : syracuseStep 1098233 = 823675) B823675
theorem B1098323 : Blo 487790 1098323 := bstep (se 1 (by rfl) ⟨823742, by rfl⟩ : syracuseStep 1098323 = 1647485) B1647485
theorem B1098503 : Blo 487790 1098503 := bstep (se 1 (by rfl) ⟨823877, by rfl⟩ : syracuseStep 1098503 = 1647755) B1647755
theorem B1655639 : Blo 487790 1655639 := bstep (se 1 (by rfl) ⟨1241729, by rfl⟩ : syracuseStep 1655639 = 2483459) B2483459
theorem B1098593 : Blo 487790 1098593 := bstep (se 2 (by rfl) ⟨411972, by rfl⟩ : syracuseStep 1098593 = 823945) B823945
theorem B1655801 : Blo 487790 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B1655855 : Blo 487790 1655855 := bstep (se 1 (by rfl) ⟨1241891, by rfl⟩ : syracuseStep 1655855 = 2483783) B2483783
theorem B43042051 : Blo 487790 43042051 := bstep (se 1 (by rfl) ⟨32281538, by rfl⟩ : syracuseStep 43042051 = 64563077) B64563077
theorem B1393939 : Blo 487790 1393939 := bstep (se 1 (by rfl) ⟨1045454, by rfl⟩ : syracuseStep 1393939 = 2090909) B2090909
theorem B3524147 : Blo 487790 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B1197641 : Blo 487790 1197641 := bstep (se 2 (by rfl) ⟨449115, by rfl⟩ : syracuseStep 1197641 = 898231) B898231
theorem B1099583 : Blo 487790 1099583 := bstep (se 1 (by rfl) ⟨824687, by rfl⟩ : syracuseStep 1099583 = 1649375) B1649375
theorem B1656719 : Blo 487790 1656719 := bstep (se 1 (by rfl) ⟨1242539, by rfl⟩ : syracuseStep 1656719 = 2485079) B2485079
theorem B2476007 : Blo 487790 2476007 := bstep (se 1 (by rfl) ⟨1857005, by rfl⟩ : syracuseStep 2476007 = 3714011) B3714011
theorem B2345183 : Blo 487790 2345183 := bstep (se 1 (by rfl) ⟨1758887, by rfl⟩ : syracuseStep 2345183 = 3517775) B3517775
theorem B2116097 : Blo 487790 2116097 := bstep (se 2 (by rfl) ⟨793536, by rfl⟩ : syracuseStep 2116097 = 1587073) B1587073
theorem B7227967 : Blo 487790 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B1395625 : Blo 487790 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B5950687 : Blo 487790 5950687 := bstep (se 1 (by rfl) ⟨4463015, by rfl⟩ : syracuseStep 5950687 = 8926031) B8926031
theorem B2510327 : Blo 487790 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B1101851 : Blo 487790 1101851 := bstep (se 1 (by rfl) ⟨826388, by rfl⟩ : syracuseStep 1101851 = 1652777) B1652777
theorem B1528633 : Blo 487790 1528633 := bstep (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) B1146475
theorem B1758959 : Blo 487790 1758959 := bstep (se 1 (by rfl) ⟨1319219, by rfl⟩ : syracuseStep 1758959 = 2638439) B2638439
theorem B5592887 : Blo 487790 5592887 := bstep (se 1 (by rfl) ⟨4194665, by rfl⟩ : syracuseStep 5592887 = 8389331) B8389331
theorem B2348929 : Blo 487790 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B2086793 : Blo 487790 2086793 := bstep (se 2 (by rfl) ⟨782547, by rfl⟩ : syracuseStep 2086793 = 1565095) B1565095
theorem B1104155 : Blo 487790 1104155 := bstep (se 1 (by rfl) ⟨828116, by rfl⟩ : syracuseStep 1104155 = 1656233) B1656233
theorem B2480543 : Blo 487790 2480543 := bstep (se 1 (by rfl) ⟨1860407, by rfl⟩ : syracuseStep 2480543 = 3720815) B3720815
theorem B1105127 : Blo 487790 1105127 := bstep (se 1 (by rfl) ⟨828845, by rfl⟩ : syracuseStep 1105127 = 1657691) B1657691
theorem B5594345 : Blo 487790 5594345 := bstep (se 2 (by rfl) ⟨2097879, by rfl⟩ : syracuseStep 5594345 = 4195759) B4195759
theorem B3136877 : Blo 487790 3136877 := bstep (se 3 (by rfl) ⟨588164, by rfl⟩ : syracuseStep 3136877 = 1176329) B1176329
theorem B7822817 : Blo 487790 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B1237153 : Blo 487790 1237153 := bstep (se 2 (by rfl) ⟨463932, by rfl⟩ : syracuseStep 1237153 = 927865) B927865
theorem B1106081 : Blo 487790 1106081 := bstep (se 2 (by rfl) ⟨414780, by rfl⟩ : syracuseStep 1106081 = 829561) B829561
theorem B2482487 : Blo 487790 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B1860029 : Blo 487790 1860029 := bstep (se 3 (by rfl) ⟨348755, by rfl⟩ : syracuseStep 1860029 = 697511) B697511
theorem B746039 : Blo 487790 746039 := bstep (se 1 (by rfl) ⟨559529, by rfl⟩ : syracuseStep 746039 = 1119059) B1119059
theorem B549535 : Blo 487790 549535 := bstep (se 1 (by rfl) ⟨412151, by rfl⟩ : syracuseStep 549535 = 824303) B824303
theorem B7037675 : Blo 487790 7037675 := bstep (se 1 (by rfl) ⟨5278256, by rfl⟩ : syracuseStep 7037675 = 10556513) B10556513
theorem B3531755 : Blo 487790 3531755 := bstep (se 1 (by rfl) ⟨2648816, by rfl⟩ : syracuseStep 3531755 = 5297633) B5297633
theorem B1008865 : Blo 487790 1008865 := bstep (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) B756649
theorem B2778583 : Blo 487790 2778583 := bstep (se 1 (by rfl) ⟨2083937, by rfl⟩ : syracuseStep 2778583 = 4167875) B4167875
theorem B5007595 : Blo 487790 5007595 := bstep (se 1 (by rfl) ⟨3755696, by rfl⟩ : syracuseStep 5007595 = 7511393) B7511393
theorem B2484755 : Blo 487790 2484755 := bstep (se 1 (by rfl) ⟨1863566, by rfl⟩ : syracuseStep 2484755 = 3727133) B3727133
theorem B551803 : Blo 487790 551803 := bstep (se 1 (by rfl) ⟨413852, by rfl⟩ : syracuseStep 551803 = 827705) B827705
theorem B552127 : Blo 487790 552127 := bstep (se 1 (by rfl) ⟨414095, by rfl⟩ : syracuseStep 552127 = 828191) B828191
theorem B3173807 : Blo 487790 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B552667 : Blo 487790 552667 := bstep (se 1 (by rfl) ⟨414500, by rfl⟩ : syracuseStep 552667 = 829001) B829001
theorem B1568489 : Blo 487790 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B552991 : Blo 487790 552991 := bstep (se 1 (by rfl) ⟨414743, by rfl⟩ : syracuseStep 552991 = 829487) B829487
theorem B1863719 : Blo 487790 1863719 := bstep (se 1 (by rfl) ⟨1397789, by rfl⟩ : syracuseStep 1863719 = 2795579) B2795579
theorem B1241183 : Blo 487790 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B2093165 : Blo 487790 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B2650439 : Blo 487790 2650439 := bstep (se 1 (by rfl) ⟨1987829, by rfl⟩ : syracuseStep 2650439 = 3975659) B3975659
theorem B2355581 : Blo 487790 2355581 := bstep (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) B883343
theorem B35680769 : Blo 487790 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B18641441 : Blo 487790 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B488219 : Blo 487790 488219 := bstep (se 1 (by rfl) ⟨366164, by rfl⟩ : syracuseStep 488219 = 732329) B732329
theorem B488495 : Blo 487790 488495 := bstep (se 1 (by rfl) ⟨366371, by rfl⟩ : syracuseStep 488495 = 732743) B732743
theorem B1274951 : Blo 487790 1274951 := bstep (se 1 (by rfl) ⟨956213, by rfl⟩ : syracuseStep 1274951 = 1912427) B1912427
theorem B488615 : Blo 487790 488615 := bstep (se 1 (by rfl) ⟨366461, by rfl⟩ : syracuseStep 488615 = 732923) B732923
theorem B783527 : Blo 487790 783527 := bstep (se 1 (by rfl) ⟨587645, by rfl⟩ : syracuseStep 783527 = 1175291) B1175291
theorem B1176743 : Blo 487790 1176743 := bstep (se 1 (by rfl) ⟨882557, by rfl⟩ : syracuseStep 1176743 = 1765115) B1765115
theorem B2487671 : Blo 487790 2487671 := bstep (se 1 (by rfl) ⟨1865753, by rfl⟩ : syracuseStep 2487671 = 3731507) B3731507
theorem B489063 : Blo 487790 489063 := bstep (se 1 (by rfl) ⟨366797, by rfl⟩ : syracuseStep 489063 = 733595) B733595
theorem B489343 : Blo 487790 489343 := bstep (se 1 (by rfl) ⟨367007, by rfl⟩ : syracuseStep 489343 = 734015) B734015
theorem B489439 : Blo 487790 489439 := bstep (se 1 (by rfl) ⟨367079, by rfl⟩ : syracuseStep 489439 = 734159) B734159
theorem B4716539 : Blo 487790 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B489467 : Blo 487790 489467 := bstep (se 1 (by rfl) ⟨367100, by rfl⟩ : syracuseStep 489467 = 734201) B734201
theorem B489499 : Blo 487790 489499 := bstep (se 1 (by rfl) ⟨367124, by rfl⟩ : syracuseStep 489499 = 734249) B734249
theorem B489519 : Blo 487790 489519 := bstep (se 1 (by rfl) ⟨367139, by rfl⟩ : syracuseStep 489519 = 734279) B734279
theorem B1865875 : Blo 487790 1865875 := bstep (se 1 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 1865875 = 2798813) B2798813
theorem B489639 : Blo 487790 489639 := bstep (se 1 (by rfl) ⟨367229, by rfl⟩ : syracuseStep 489639 = 734459) B734459
theorem B1308847 : Blo 487790 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B1046839 : Blo 487790 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B1047019 : Blo 487790 1047019 := bstep (se 1 (by rfl) ⟨785264, by rfl⟩ : syracuseStep 1047019 = 1570529) B1570529
theorem B1866361 : Blo 487790 1866361 := bstep (se 2 (by rfl) ⟨699885, by rfl⟩ : syracuseStep 1866361 = 1399771) B1399771
theorem B1244119 : Blo 487790 1244119 := bstep (se 1 (by rfl) ⟨933089, by rfl⟩ : syracuseStep 1244119 = 1866179) B1866179
theorem B490463 : Blo 487790 490463 := bstep (se 1 (by rfl) ⟨367847, by rfl⟩ : syracuseStep 490463 = 735695) B735695
theorem B490523 : Blo 487790 490523 := bstep (se 1 (by rfl) ⟨367892, by rfl⟩ : syracuseStep 490523 = 735785) B735785
theorem B490651 : Blo 487790 490651 := bstep (se 1 (by rfl) ⟨367988, by rfl⟩ : syracuseStep 490651 = 735977) B735977
theorem B1768691 : Blo 487790 1768691 := bstep (se 1 (by rfl) ⟨1326518, by rfl⟩ : syracuseStep 1768691 = 2653037) B2653037
theorem B490907 : Blo 487790 490907 := bstep (se 1 (by rfl) ⟨368180, by rfl⟩ : syracuseStep 490907 = 736361) B736361
theorem B1244585 : Blo 487790 1244585 := bstep (se 2 (by rfl) ⟨466719, by rfl⟩ : syracuseStep 1244585 = 933439) B933439
theorem B2522603 : Blo 487790 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B490991 : Blo 487790 490991 := bstep (se 1 (by rfl) ⟨368243, by rfl⟩ : syracuseStep 490991 = 736487) B736487
theorem B491327 : Blo 487790 491327 := bstep (se 1 (by rfl) ⟨368495, by rfl⟩ : syracuseStep 491327 = 736991) B736991
theorem B622399 : Blo 487790 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B491355 : Blo 487790 491355 := bstep (se 1 (by rfl) ⟨368516, by rfl⟩ : syracuseStep 491355 = 737033) B737033
theorem B491611 : Blo 487790 491611 := bstep (se 1 (by rfl) ⟨368708, by rfl⟩ : syracuseStep 491611 = 737417) B737417
theorem B491675 : Blo 487790 491675 := bstep (se 1 (by rfl) ⟨368756, by rfl⟩ : syracuseStep 491675 = 737513) B737513
theorem B491759 : Blo 487790 491759 := bstep (se 1 (by rfl) ⟨368819, by rfl⟩ : syracuseStep 491759 = 737639) B737639
theorem B1180327 : Blo 487790 1180327 := bstep (se 1 (by rfl) ⟨885245, by rfl⟩ : syracuseStep 1180327 = 1770491) B1770491
theorem B1278761 : Blo 487790 1278761 := bstep (se 2 (by rfl) ⟨479535, by rfl⟩ : syracuseStep 1278761 = 959071) B959071
theorem B1049863 : Blo 487790 1049863 := bstep (se 1 (by rfl) ⟨787397, by rfl⟩ : syracuseStep 1049863 = 1574795) B1574795
theorem B1410731 : Blo 487790 1410731 := bstep (se 1 (by rfl) ⟨1058048, by rfl⟩ : syracuseStep 1410731 = 2116097) B2116097
theorem B3704777 : Blo 487790 3704777 := bstep (se 2 (by rfl) ⟨1389291, by rfl⟩ : syracuseStep 3704777 = 2778583) B2778583
theorem B7670051 : Blo 487790 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B1673551 : Blo 487790 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B7047593 : Blo 487790 7047593 := bstep (se 2 (by rfl) ⟨2642847, by rfl⟩ : syracuseStep 7047593 = 5285695) B5285695
theorem B4197743 : Blo 487790 4197743 := bstep (se 1 (by rfl) ⟨3148307, by rfl⟩ : syracuseStep 4197743 = 6296615) B6296615
theorem B9637289 : Blo 487790 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B6295643 : Blo 487790 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B7934249 : Blo 487790 7934249 := bstep (se 2 (by rfl) ⟨2975343, by rfl⟩ : syracuseStep 7934249 = 5950687) B5950687
theorem B5215211 : Blo 487790 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B497359 : Blo 487790 497359 := bstep (se 1 (by rfl) ⟨373019, by rfl⟩ : syracuseStep 497359 = 746039) B746039
theorem B4691783 : Blo 487790 4691783 := bstep (se 1 (by rfl) ⟨3518837, by rfl⟩ : syracuseStep 4691783 = 7037675) B7037675
theorem B20158469 : Blo 487790 20158469 := bstep (se 4 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 20158469 = 3779713) B3779713
theorem B5380613 : Blo 487790 5380613 := bstep (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) B1008865
theorem B531263 : Blo 487790 531263 := bstep (se 1 (by rfl) ⟨398447, by rfl⟩ : syracuseStep 531263 = 796895) B796895
theorem B827455 : Blo 487790 827455 := bstep (se 1 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 827455 = 1241183) B1241183
theorem B1646783 : Blo 487790 1646783 := bstep (se 1 (by rfl) ⟨1235087, by rfl⟩ : syracuseStep 1646783 = 2470175) B2470175
theorem B1745129 : Blo 487790 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B12427627 : Blo 487790 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B8463485 : Blo 487790 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B1648079 : Blo 487790 1648079 := bstep (se 1 (by rfl) ⟨1236059, by rfl⟩ : syracuseStep 1648079 = 2472119) B2472119
theorem B1648619 : Blo 487790 1648619 := bstep (se 1 (by rfl) ⟨1236464, by rfl⟩ : syracuseStep 1648619 = 2472929) B2472929
theorem B829723 : Blo 487790 829723 := bstep (se 1 (by rfl) ⟨622292, by rfl⟩ : syracuseStep 829723 = 1244585) B1244585
theorem B1681735 : Blo 487790 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B829865 : Blo 487790 829865 := bstep (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) B622399
theorem B928351 : Blo 487790 928351 := bstep (se 1 (by rfl) ⟨696263, by rfl⟩ : syracuseStep 928351 = 1392527) B1392527
theorem B731867 : Blo 487790 731867 := bstep (se 1 (by rfl) ⟨548900, by rfl⟩ : syracuseStep 731867 = 1097801) B1097801
theorem B1649537 : Blo 487790 1649537 := bstep (se 2 (by rfl) ⟨618576, by rfl⟩ : syracuseStep 1649537 = 1237153) B1237153
theorem B732143 : Blo 487790 732143 := bstep (se 1 (by rfl) ⟨549107, by rfl⟩ : syracuseStep 732143 = 1098215) B1098215
theorem B732155 : Blo 487790 732155 := bstep (se 1 (by rfl) ⟨549116, by rfl⟩ : syracuseStep 732155 = 1098233) B1098233
theorem B732215 : Blo 487790 732215 := bstep (se 1 (by rfl) ⟨549161, by rfl⟩ : syracuseStep 732215 = 1098323) B1098323
theorem B732335 : Blo 487790 732335 := bstep (se 1 (by rfl) ⟨549251, by rfl⟩ : syracuseStep 732335 = 1098503) B1098503
theorem B732395 : Blo 487790 732395 := bstep (se 1 (by rfl) ⟨549296, by rfl⟩ : syracuseStep 732395 = 1098593) B1098593
theorem B7515575 : Blo 487790 7515575 := bstep (se 1 (by rfl) ⟨5636681, by rfl⟩ : syracuseStep 7515575 = 11273363) B11273363
theorem B2797037 : Blo 487790 2797037 := bstep (se 3 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 2797037 = 1048889) B1048889
theorem B732713 : Blo 487790 732713 := bstep (se 2 (by rfl) ⟨274767, by rfl⟩ : syracuseStep 732713 = 549535) B549535
theorem B3059279 : Blo 487790 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B798427 : Blo 487790 798427 := bstep (se 1 (by rfl) ⟨598820, by rfl⟩ : syracuseStep 798427 = 1197641) B1197641
theorem B733055 : Blo 487790 733055 := bstep (se 1 (by rfl) ⟨549791, by rfl⟩ : syracuseStep 733055 = 1099583) B1099583
theorem B1650671 : Blo 487790 1650671 := bstep (se 1 (by rfl) ⟨1238003, by rfl⟩ : syracuseStep 1650671 = 2476007) B2476007
theorem B57389401 : Blo 487790 57389401 := bstep (se 2 (by rfl) ⟨21521025, by rfl⟩ : syracuseStep 57389401 = 43042051) B43042051
theorem B2470823 : Blo 487790 2470823 := bstep (se 1 (by rfl) ⟨1853117, by rfl⟩ : syracuseStep 2470823 = 3706235) B3706235
theorem B734567 : Blo 487790 734567 := bstep (se 1 (by rfl) ⟨550925, by rfl⟩ : syracuseStep 734567 = 1101851) B1101851
theorem B12760685 : Blo 487790 12760685 := bstep (se 3 (by rfl) ⟨2392628, by rfl⟩ : syracuseStep 12760685 = 4785257) B4785257
theorem B735737 : Blo 487790 735737 := bstep (se 2 (by rfl) ⟨275901, by rfl⟩ : syracuseStep 735737 = 551803) B551803
theorem B1391195 : Blo 487790 1391195 := bstep (se 1 (by rfl) ⟨1043396, by rfl⟩ : syracuseStep 1391195 = 2086793) B2086793
theorem B2472605 : Blo 487790 2472605 := bstep (se 3 (by rfl) ⟨463613, by rfl⟩ : syracuseStep 2472605 = 927227) B927227
theorem B4700855 : Blo 487790 4700855 := bstep (se 1 (by rfl) ⟨3525641, by rfl⟩ : syracuseStep 4700855 = 7051283) B7051283
theorem B736103 : Blo 487790 736103 := bstep (se 1 (by rfl) ⟨552077, by rfl⟩ : syracuseStep 736103 = 1104155) B1104155
theorem B736169 : Blo 487790 736169 := bstep (se 2 (by rfl) ⟨276063, by rfl⟩ : syracuseStep 736169 = 552127) B552127
theorem B1653695 : Blo 487790 1653695 := bstep (se 1 (by rfl) ⟨1240271, by rfl⟩ : syracuseStep 1653695 = 2480543) B2480543
theorem B7519517 : Blo 487790 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B736751 : Blo 487790 736751 := bstep (se 1 (by rfl) ⟨552563, by rfl⟩ : syracuseStep 736751 = 1105127) B1105127
theorem B736889 : Blo 487790 736889 := bstep (se 2 (by rfl) ⟨276333, by rfl⟩ : syracuseStep 736889 = 552667) B552667
theorem B2473901 : Blo 487790 2473901 := bstep (se 3 (by rfl) ⟨463856, by rfl⟩ : syracuseStep 2473901 = 927713) B927713
theorem B737321 : Blo 487790 737321 := bstep (se 2 (by rfl) ⟨276495, by rfl⟩ : syracuseStep 737321 = 552991) B552991
theorem B737387 : Blo 487790 737387 := bstep (se 1 (by rfl) ⟨553040, by rfl⟩ : syracuseStep 737387 = 1106081) B1106081
theorem B1654991 : Blo 487790 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B193184135 : Blo 487790 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B1099241 : Blo 487790 1099241 := bstep (se 2 (by rfl) ⟨412215, by rfl⟩ : syracuseStep 1099241 = 824431) B824431
theorem B1656503 : Blo 487790 1656503 := bstep (se 1 (by rfl) ⟨1242377, by rfl⟩ : syracuseStep 1656503 = 2484755) B2484755
theorem B2868979 : Blo 487790 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B4180247 : Blo 487790 4180247 := bstep (se 1 (by rfl) ⟨3135185, by rfl⟩ : syracuseStep 4180247 = 6270371) B6270371
theorem B3131905 : Blo 487790 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B1493599 : Blo 487790 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B1395443 : Blo 487790 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B1395785 : Blo 487790 1395785 := bstep (se 2 (by rfl) ⟨523419, by rfl⟩ : syracuseStep 1395785 = 1046839) B1046839
theorem B1396025 : Blo 487790 1396025 := bstep (se 2 (by rfl) ⟨523509, by rfl⟩ : syracuseStep 1396025 = 1047019) B1047019
theorem B1101311 : Blo 487790 1101311 := bstep (se 1 (by rfl) ⟨825983, by rfl⟩ : syracuseStep 1101311 = 1651967) B1651967
theorem B3722759 : Blo 487790 3722759 := bstep (se 1 (by rfl) ⟨2792069, by rfl⟩ : syracuseStep 3722759 = 5584139) B5584139
theorem B1658447 : Blo 487790 1658447 := bstep (se 1 (by rfl) ⟨1243835, by rfl⟩ : syracuseStep 1658447 = 2487671) B2487671
theorem B839279 : Blo 487790 839279 := bstep (se 1 (by rfl) ⟨629459, by rfl⟩ : syracuseStep 839279 = 1258919) B1258919
theorem B1101455 : Blo 487790 1101455 := bstep (se 1 (by rfl) ⟨826091, by rfl⟩ : syracuseStep 1101455 = 1652183) B1652183
theorem B1658825 : Blo 487790 1658825 := bstep (se 2 (by rfl) ⟨622059, by rfl⟩ : syracuseStep 1658825 = 1244119) B1244119
theorem B1101815 : Blo 487790 1101815 := bstep (se 1 (by rfl) ⟨826361, by rfl⟩ : syracuseStep 1101815 = 1652723) B1652723
theorem B1102175 : Blo 487790 1102175 := bstep (se 1 (by rfl) ⟨826631, by rfl⟩ : syracuseStep 1102175 = 1653263) B1653263
theorem B4182637 : Blo 487790 4182637 := bstep (se 3 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 4182637 = 1568489) B1568489
theorem B1102895 : Blo 487790 1102895 := bstep (se 1 (by rfl) ⟨827171, by rfl⟩ : syracuseStep 1102895 = 1654343) B1654343
theorem B1856641 : Blo 487790 1856641 := bstep (se 2 (by rfl) ⟨696240, by rfl⟩ : syracuseStep 1856641 = 1392481) B1392481
theorem B1103183 : Blo 487790 1103183 := bstep (se 1 (by rfl) ⟨827387, by rfl⟩ : syracuseStep 1103183 = 1654775) B1654775
theorem B1103759 : Blo 487790 1103759 := bstep (se 1 (by rfl) ⟨827819, by rfl⟩ : syracuseStep 1103759 = 1655639) B1655639
theorem B1103867 : Blo 487790 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B1103903 : Blo 487790 1103903 := bstep (se 1 (by rfl) ⟨827927, by rfl⟩ : syracuseStep 1103903 = 1655855) B1655855
theorem B7067837 : Blo 487790 7067837 := bstep (se 3 (by rfl) ⟨1325219, by rfl⟩ : syracuseStep 7067837 = 2650439) B2650439
theorem B2349431 : Blo 487790 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B1104479 : Blo 487790 1104479 := bstep (se 1 (by rfl) ⟨828359, by rfl⟩ : syracuseStep 1104479 = 1656719) B1656719
theorem B1563455 : Blo 487790 1563455 := bstep (se 1 (by rfl) ⟨1172591, by rfl⟩ : syracuseStep 1563455 = 2345183) B2345183
theorem B1858585 : Blo 487790 1858585 := bstep (se 2 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 1858585 = 1393939) B1393939
theorem B1072211 : Blo 487790 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B1858859 : Blo 487790 1858859 := bstep (se 1 (by rfl) ⟨1394144, by rfl⟩ : syracuseStep 1858859 = 2788289) B2788289
theorem B3170219 : Blo 487790 3170219 := bstep (se 1 (by rfl) ⟨2377664, by rfl⟩ : syracuseStep 3170219 = 4755329) B4755329
theorem B2383789 : Blo 487790 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B549103 : Blo 487790 549103 := bstep (se 1 (by rfl) ⟨411827, by rfl⟩ : syracuseStep 549103 = 823655) B823655
theorem B6676793 : Blo 487790 6676793 := bstep (se 2 (by rfl) ⟨2503797, by rfl⟩ : syracuseStep 6676793 = 5007595) B5007595
theorem B2089405 : Blo 487790 2089405 := bstep (se 3 (by rfl) ⟨391763, by rfl⟩ : syracuseStep 2089405 = 783527) B783527
theorem B22569635 : Blo 487790 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B1172639 : Blo 487790 1172639 := bstep (se 1 (by rfl) ⟨879479, by rfl⟩ : syracuseStep 1172639 = 1758959) B1758959
theorem B3728591 : Blo 487790 3728591 := bstep (se 1 (by rfl) ⟨2796443, by rfl⟩ : syracuseStep 3728591 = 5592887) B5592887
theorem B1860833 : Blo 487790 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B8152709 : Blo 487790 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B2123459 : Blo 487790 2123459 := bstep (se 1 (by rfl) ⟨1592594, by rfl⟩ : syracuseStep 2123459 = 3185189) B3185189
theorem B4253705 : Blo 487790 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B3729563 : Blo 487790 3729563 := bstep (se 1 (by rfl) ⟨2797172, by rfl⟩ : syracuseStep 3729563 = 5594345) B5594345
theorem B2091251 : Blo 487790 2091251 := bstep (se 1 (by rfl) ⟨1568438, by rfl⟩ : syracuseStep 2091251 = 3136877) B3136877
theorem B551407 : Blo 487790 551407 := bstep (se 1 (by rfl) ⟨413555, by rfl⟩ : syracuseStep 551407 = 827111) B827111
theorem B1010279 : Blo 487790 1010279 := bstep (se 1 (by rfl) ⟨757709, by rfl⟩ : syracuseStep 1010279 = 1515419) B1515419
theorem B1240019 : Blo 487790 1240019 := bstep (se 1 (by rfl) ⟨930014, by rfl⟩ : syracuseStep 1240019 = 1860029) B1860029
theorem B2354503 : Blo 487790 2354503 := bstep (se 1 (by rfl) ⟨1765877, by rfl⟩ : syracuseStep 2354503 = 3531755) B3531755
theorem B5664491 : Blo 487790 5664491 := bstep (se 1 (by rfl) ⟨4248368, by rfl⟩ : syracuseStep 5664491 = 8496737) B8496737
theorem B2780999 : Blo 487790 2780999 := bstep (se 1 (by rfl) ⟨2085749, by rfl⟩ : syracuseStep 2780999 = 4171499) B4171499
theorem B2978171 : Blo 487790 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B487839 : Blo 487790 487839 := bstep (se 1 (by rfl) ⟨365879, by rfl⟩ : syracuseStep 487839 = 731759) B731759
theorem B881065 : Blo 487790 881065 := bstep (se 2 (by rfl) ⟨330399, by rfl⟩ : syracuseStep 881065 = 660799) B660799
theorem B487983 : Blo 487790 487983 := bstep (se 1 (by rfl) ⟨365987, by rfl⟩ : syracuseStep 487983 = 731975) B731975
theorem B488383 : Blo 487790 488383 := bstep (se 1 (by rfl) ⟨366287, by rfl⟩ : syracuseStep 488383 = 732575) B732575
theorem B488559 : Blo 487790 488559 := bstep (se 1 (by rfl) ⟨366419, by rfl⟩ : syracuseStep 488559 = 732839) B732839
theorem B488575 : Blo 487790 488575 := bstep (se 1 (by rfl) ⟨366431, by rfl⟩ : syracuseStep 488575 = 732863) B732863
theorem B488639 : Blo 487790 488639 := bstep (se 1 (by rfl) ⟨366479, by rfl⟩ : syracuseStep 488639 = 732959) B732959
theorem B3765467 : Blo 487790 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B1242479 : Blo 487790 1242479 := bstep (se 1 (by rfl) ⟨931859, by rfl⟩ : syracuseStep 1242479 = 1863719) B1863719
theorem B488831 : Blo 487790 488831 := bstep (se 1 (by rfl) ⟨366623, by rfl⟩ : syracuseStep 488831 = 733247) B733247
theorem B619903 : Blo 487790 619903 := bstep (se 1 (by rfl) ⟨464927, by rfl⟩ : syracuseStep 619903 = 929855) B929855
theorem B488959 : Blo 487790 488959 := bstep (se 1 (by rfl) ⟨366719, by rfl⟩ : syracuseStep 488959 = 733439) B733439
theorem B2487833 : Blo 487790 2487833 := bstep (se 2 (by rfl) ⟨932937, by rfl⟩ : syracuseStep 2487833 = 1865875) B1865875
theorem B488987 : Blo 487790 488987 := bstep (se 1 (by rfl) ⟨366740, by rfl⟩ : syracuseStep 488987 = 733481) B733481
theorem B1570387 : Blo 487790 1570387 := bstep (se 1 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 1570387 = 2355581) B2355581
theorem B23787179 : Blo 487790 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B489167 : Blo 487790 489167 := bstep (se 1 (by rfl) ⟨366875, by rfl⟩ : syracuseStep 489167 = 733751) B733751
theorem B16152335 : Blo 487790 16152335 := bstep (se 1 (by rfl) ⟨12114251, by rfl⟩ : syracuseStep 16152335 = 24228503) B24228503
theorem B489327 : Blo 487790 489327 := bstep (se 1 (by rfl) ⟨366995, by rfl⟩ : syracuseStep 489327 = 733991) B733991
theorem B489407 : Blo 487790 489407 := bstep (se 1 (by rfl) ⟨367055, by rfl⟩ : syracuseStep 489407 = 734111) B734111
theorem B849967 : Blo 487790 849967 := bstep (se 1 (by rfl) ⟨637475, by rfl⟩ : syracuseStep 849967 = 1274951) B1274951
theorem B784495 : Blo 487790 784495 := bstep (se 1 (by rfl) ⟨588371, by rfl⟩ : syracuseStep 784495 = 1176743) B1176743
theorem B2390141 : Blo 487790 2390141 := bstep (se 3 (by rfl) ⟨448151, by rfl⟩ : syracuseStep 2390141 = 896303) B896303
theorem B2488481 : Blo 487790 2488481 := bstep (se 2 (by rfl) ⟨933180, by rfl⟩ : syracuseStep 2488481 = 1866361) B1866361
theorem B1669355 : Blo 487790 1669355 := bstep (se 1 (by rfl) ⟨1252016, by rfl⟩ : syracuseStep 1669355 = 2504033) B2504033
theorem B489723 : Blo 487790 489723 := bstep (se 1 (by rfl) ⟨367292, by rfl⟩ : syracuseStep 489723 = 734585) B734585
theorem B489727 : Blo 487790 489727 := bstep (se 1 (by rfl) ⟨367295, by rfl⟩ : syracuseStep 489727 = 734591) B734591
theorem B489831 : Blo 487790 489831 := bstep (se 1 (by rfl) ⟨367373, by rfl⟩ : syracuseStep 489831 = 734747) B734747
theorem B489951 : Blo 487790 489951 := bstep (se 1 (by rfl) ⟨367463, by rfl⟩ : syracuseStep 489951 = 734927) B734927
theorem B490087 : Blo 487790 490087 := bstep (se 1 (by rfl) ⟨367565, by rfl⟩ : syracuseStep 490087 = 735131) B735131
theorem B490111 : Blo 487790 490111 := bstep (se 1 (by rfl) ⟨367583, by rfl⟩ : syracuseStep 490111 = 735167) B735167
theorem B3144359 : Blo 487790 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B3963563 : Blo 487790 3963563 := bstep (se 1 (by rfl) ⟨2972672, by rfl⟩ : syracuseStep 3963563 = 5945345) B5945345
theorem B490223 : Blo 487790 490223 := bstep (se 1 (by rfl) ⟨367667, by rfl⟩ : syracuseStep 490223 = 735335) B735335
theorem B15891335 : Blo 487790 15891335 := bstep (se 1 (by rfl) ⟨11918501, by rfl⟩ : syracuseStep 15891335 = 23837003) B23837003
theorem B490479 : Blo 487790 490479 := bstep (se 1 (by rfl) ⟨367859, by rfl⟩ : syracuseStep 490479 = 735719) B735719
theorem B490527 : Blo 487790 490527 := bstep (se 1 (by rfl) ⟨367895, by rfl⟩ : syracuseStep 490527 = 735791) B735791
theorem B7568423 : Blo 487790 7568423 := bstep (se 1 (by rfl) ⟨5676317, by rfl⟩ : syracuseStep 7568423 = 11352635) B11352635
theorem B490975 : Blo 487790 490975 := bstep (se 1 (by rfl) ⟨368231, by rfl⟩ : syracuseStep 490975 = 736463) B736463
theorem B1179127 : Blo 487790 1179127 := bstep (se 1 (by rfl) ⟨884345, by rfl⟩ : syracuseStep 1179127 = 1768691) B1768691
theorem B491035 : Blo 487790 491035 := bstep (se 1 (by rfl) ⟨368276, by rfl⟩ : syracuseStep 491035 = 736553) B736553
theorem B491055 : Blo 487790 491055 := bstep (se 1 (by rfl) ⟨368291, by rfl⟩ : syracuseStep 491055 = 736583) B736583
theorem B491455 : Blo 487790 491455 := bstep (se 1 (by rfl) ⟨368591, by rfl⟩ : syracuseStep 491455 = 737183) B737183
theorem B491515 : Blo 487790 491515 := bstep (se 1 (by rfl) ⟨368636, by rfl⟩ : syracuseStep 491515 = 737273) B737273
theorem B491547 : Blo 487790 491547 := bstep (se 1 (by rfl) ⟨368660, by rfl⟩ : syracuseStep 491547 = 737321) B737321
theorem B491591 : Blo 487790 491591 := bstep (se 1 (by rfl) ⟨368693, by rfl⟩ : syracuseStep 491591 = 737387) B737387
theorem B2785873 : Blo 487790 2785873 := bstep (se 2 (by rfl) ⟨1044702, by rfl⟩ : syracuseStep 2785873 = 2089405) B2089405
theorem B4653677 : Blo 487790 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B1573769 : Blo 487790 1573769 := bstep (se 2 (by rfl) ⟨590163, by rfl⟩ : syracuseStep 1573769 = 1180327) B1180327
theorem B2786831 : Blo 487790 2786831 := bstep (se 1 (by rfl) ⟨2090123, by rfl⟩ : syracuseStep 2786831 = 4180247) B4180247
theorem B5113367 : Blo 487790 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B3410029 : Blo 487790 3410029 := bstep (se 3 (by rfl) ⟨639380, by rfl⟩ : syracuseStep 3410029 = 1278761) B1278761
theorem B6424859 : Blo 487790 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B4197095 : Blo 487790 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B2231401 : Blo 487790 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B3476807 : Blo 487790 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B13438979 : Blo 487790 13438979 := bstep (se 1 (by rfl) ⟨10079234, by rfl⟩ : syracuseStep 13438979 = 20158469) B20158469
theorem B76519201 : Blo 487790 76519201 := bstep (se 2 (by rfl) ⟨28694700, by rfl⟩ : syracuseStep 76519201 = 57389401) B57389401
theorem B5576849 : Blo 487790 5576849 := bstep (se 2 (by rfl) ⟨2091318, by rfl⟩ : syracuseStep 5576849 = 4182637) B4182637
theorem B1415639 : Blo 487790 1415639 := bstep (se 1 (by rfl) ⟨1061729, by rfl⟩ : syracuseStep 1415639 = 2123459) B2123459
theorem B2694077 : Blo 487790 2694077 := bstep (se 3 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 2694077 = 1010279) B1010279
theorem B826537 : Blo 487790 826537 := bstep (se 2 (by rfl) ⟨309951, by rfl⟩ : syracuseStep 826537 = 619903) B619903
theorem B826679 : Blo 487790 826679 := bstep (se 1 (by rfl) ⟨620009, by rfl⟩ : syracuseStep 826679 = 1240019) B1240019
theorem B1416701 : Blo 487790 1416701 := bstep (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) B531263
theorem B2039519 : Blo 487790 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B3776327 : Blo 487790 3776327 := bstep (se 1 (by rfl) ⟨2832245, by rfl⟩ : syracuseStep 3776327 = 5664491) B5664491
theorem B2859229 : Blo 487790 2859229 := bstep (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) B1072211
theorem B1647215 : Blo 487790 1647215 := bstep (se 1 (by rfl) ⟨1235411, by rfl⟩ : syracuseStep 1647215 = 2470823) B2470823
theorem B828319 : Blo 487790 828319 := bstep (se 1 (by rfl) ⟨621239, by rfl⟩ : syracuseStep 828319 = 1242479) B1242479
theorem B2238077 : Blo 487790 2238077 := bstep (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) B839279
theorem B927463 : Blo 487790 927463 := bstep (se 1 (by rfl) ⟨695597, by rfl⟩ : syracuseStep 927463 = 1391195) B1391195
theorem B1648403 : Blo 487790 1648403 := bstep (se 1 (by rfl) ⟨1236302, by rfl⟩ : syracuseStep 1648403 = 2472605) B2472605
theorem B10594223 : Blo 487790 10594223 := bstep (se 1 (by rfl) ⟨7945667, by rfl⟩ : syracuseStep 10594223 = 15891335) B15891335
theorem B1649267 : Blo 487790 1649267 := bstep (se 1 (by rfl) ⟨1236950, by rfl⟩ : syracuseStep 1649267 = 2473901) B2473901
theorem B4533157 : Blo 487790 4533157 := bstep (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) B849967
theorem B128789423 : Blo 487790 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B732137 : Blo 487790 732137 := bstep (se 2 (by rfl) ⟨274551, by rfl⟩ : syracuseStep 732137 = 549103) B549103
theorem B732827 : Blo 487790 732827 := bstep (se 1 (by rfl) ⟨549620, by rfl⟩ : syracuseStep 732827 = 1099241) B1099241
theorem B2469851 : Blo 487790 2469851 := bstep (se 1 (by rfl) ⟨1852388, by rfl⟩ : syracuseStep 2469851 = 3704777) B3704777
theorem B4698395 : Blo 487790 4698395 := bstep (se 1 (by rfl) ⟨3523796, by rfl⟩ : syracuseStep 4698395 = 7047593) B7047593
theorem B930295 : Blo 487790 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B930523 : Blo 487790 930523 := bstep (se 1 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 930523 = 1395785) B1395785
theorem B930683 : Blo 487790 930683 := bstep (se 1 (by rfl) ⟨698012, by rfl⟩ : syracuseStep 930683 = 1396025) B1396025
theorem B2798495 : Blo 487790 2798495 := bstep (se 1 (by rfl) ⟨2098871, by rfl⟩ : syracuseStep 2798495 = 4197743) B4197743
theorem B734207 : Blo 487790 734207 := bstep (se 1 (by rfl) ⟨550655, by rfl⟩ : syracuseStep 734207 = 1101311) B1101311
theorem B734303 : Blo 487790 734303 := bstep (se 1 (by rfl) ⟨550727, by rfl⟩ : syracuseStep 734303 = 1101455) B1101455
theorem B734543 : Blo 487790 734543 := bstep (se 1 (by rfl) ⟨550907, by rfl⟩ : syracuseStep 734543 = 1101815) B1101815
theorem B5289499 : Blo 487790 5289499 := bstep (se 1 (by rfl) ⟨3967124, by rfl⟩ : syracuseStep 5289499 = 7934249) B7934249
theorem B734783 : Blo 487790 734783 := bstep (se 1 (by rfl) ⟨551087, by rfl⟩ : syracuseStep 734783 = 1102175) B1102175
theorem B2242313 : Blo 487790 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B10041245 : Blo 487790 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B735209 : Blo 487790 735209 := bstep (se 2 (by rfl) ⟨275703, by rfl⟩ : syracuseStep 735209 = 551407) B551407
theorem B4175873 : Blo 487790 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B735263 : Blo 487790 735263 := bstep (se 1 (by rfl) ⟨551447, by rfl⟩ : syracuseStep 735263 = 1102895) B1102895
theorem B735455 : Blo 487790 735455 := bstep (se 1 (by rfl) ⟨551591, by rfl⟩ : syracuseStep 735455 = 1103183) B1103183
theorem B3127855 : Blo 487790 3127855 := bstep (se 1 (by rfl) ⟨2345891, by rfl⟩ : syracuseStep 3127855 = 4691783) B4691783
theorem B735839 : Blo 487790 735839 := bstep (se 1 (by rfl) ⟨551879, by rfl⟩ : syracuseStep 735839 = 1103759) B1103759
theorem B735911 : Blo 487790 735911 := bstep (se 1 (by rfl) ⟨551933, by rfl⟩ : syracuseStep 735911 = 1103867) B1103867
theorem B735935 : Blo 487790 735935 := bstep (se 1 (by rfl) ⟨551951, by rfl⟩ : syracuseStep 735935 = 1103903) B1103903
theorem B3587075 : Blo 487790 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B21740557 : Blo 487790 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B736319 : Blo 487790 736319 := bstep (se 1 (by rfl) ⟨552239, by rfl⟩ : syracuseStep 736319 = 1104479) B1104479
theorem B1064569 : Blo 487790 1064569 := bstep (se 2 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 1064569 = 798427) B798427
theorem B1097855 : Blo 487790 1097855 := bstep (se 1 (by rfl) ⟨823391, by rfl⟩ : syracuseStep 1097855 = 1646783) B1646783
theorem B1098719 : Blo 487790 1098719 := bstep (se 1 (by rfl) ⟨824039, by rfl⟩ : syracuseStep 1098719 = 1648079) B1648079
theorem B1099079 : Blo 487790 1099079 := bstep (se 1 (by rfl) ⟨824309, by rfl⟩ : syracuseStep 1099079 = 1648619) B1648619
theorem B2835803 : Blo 487790 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B1394167 : Blo 487790 1394167 := bstep (se 1 (by rfl) ⟨1045625, by rfl⟩ : syracuseStep 1394167 = 2091251) B2091251
theorem B2475521 : Blo 487790 2475521 := bstep (se 2 (by rfl) ⟨928320, by rfl⟩ : syracuseStep 2475521 = 1856641) B1856641
theorem B1099691 : Blo 487790 1099691 := bstep (se 1 (by rfl) ⟨824768, by rfl⟩ : syracuseStep 1099691 = 1649537) B1649537
theorem B1853999 : Blo 487790 1853999 := bstep (se 1 (by rfl) ⟨1390499, by rfl⟩ : syracuseStep 1853999 = 2780999) B2780999
theorem B1100447 : Blo 487790 1100447 := bstep (se 1 (by rfl) ⟨825335, by rfl⟩ : syracuseStep 1100447 = 1650671) B1650671
theorem B1985447 : Blo 487790 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B1658555 : Blo 487790 1658555 := bstep (se 1 (by rfl) ⟨1243916, by rfl⟩ : syracuseStep 1658555 = 2487833) B2487833
theorem B8507123 : Blo 487790 8507123 := bstep (se 1 (by rfl) ⟨6380342, by rfl⟩ : syracuseStep 8507123 = 12760685) B12760685
theorem B10768223 : Blo 487790 10768223 := bstep (se 1 (by rfl) ⟨8076167, by rfl⟩ : syracuseStep 10768223 = 16152335) B16152335
theorem B2478113 : Blo 487790 2478113 := bstep (se 2 (by rfl) ⟨929292, by rfl⟩ : syracuseStep 2478113 = 1858585) B1858585
theorem B1593427 : Blo 487790 1593427 := bstep (se 1 (by rfl) ⟨1195070, by rfl⟩ : syracuseStep 1593427 = 2390141) B2390141
theorem B1658987 : Blo 487790 1658987 := bstep (se 1 (by rfl) ⟨1244240, by rfl⟩ : syracuseStep 1658987 = 2488481) B2488481
theorem B2642375 : Blo 487790 2642375 := bstep (se 1 (by rfl) ⟨1981781, by rfl⟩ : syracuseStep 2642375 = 3963563) B3963563
theorem B3133903 : Blo 487790 3133903 := bstep (se 1 (by rfl) ⟨2350427, by rfl⟩ : syracuseStep 3133903 = 4700855) B4700855
theorem B1102463 : Blo 487790 1102463 := bstep (se 1 (by rfl) ⟨826847, by rfl⟩ : syracuseStep 1102463 = 1653695) B1653695
theorem B1103273 : Blo 487790 1103273 := bstep (se 2 (by rfl) ⟨413727, by rfl⟩ : syracuseStep 1103273 = 827455) B827455
theorem B1103327 : Blo 487790 1103327 := bstep (se 1 (by rfl) ⟨827495, by rfl⟩ : syracuseStep 1103327 = 1654991) B1654991
theorem B16570169 : Blo 487790 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B4183973 : Blo 487790 4183973 := bstep (se 4 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 4183973 = 784495) B784495
theorem B940487 : Blo 487790 940487 := bstep (se 1 (by rfl) ⟨705365, by rfl⟩ : syracuseStep 940487 = 1410731) B1410731
theorem B1104335 : Blo 487790 1104335 := bstep (se 1 (by rfl) ⟨828251, by rfl⟩ : syracuseStep 1104335 = 1656503) B1656503
theorem B1399817 : Blo 487790 1399817 := bstep (se 2 (by rfl) ⟨524931, by rfl⟩ : syracuseStep 1399817 = 1049863) B1049863
theorem B60185693 : Blo 487790 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B3825305 : Blo 487790 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B2481839 : Blo 487790 2481839 := bstep (se 1 (by rfl) ⟨1861379, by rfl⟩ : syracuseStep 2481839 = 3722759) B3722759
theorem B1105631 : Blo 487790 1105631 := bstep (se 1 (by rfl) ⟨829223, by rfl⟩ : syracuseStep 1105631 = 1658447) B1658447
theorem B1105883 : Blo 487790 1105883 := bstep (se 1 (by rfl) ⟨829412, by rfl⟩ : syracuseStep 1105883 = 1658825) B1658825
theorem B22569293 : Blo 487790 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B1106297 : Blo 487790 1106297 := bstep (se 2 (by rfl) ⟨414861, by rfl⟩ : syracuseStep 1106297 = 829723) B829723
theorem B1237801 : Blo 487790 1237801 := bstep (se 2 (by rfl) ⟨464175, by rfl⟩ : syracuseStep 1237801 = 928351) B928351
theorem B1991465 : Blo 487790 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B4711891 : Blo 487790 4711891 := bstep (se 1 (by rfl) ⟨3533918, by rfl⟩ : syracuseStep 4711891 = 7067837) B7067837
theorem B1566287 : Blo 487790 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B3139337 : Blo 487790 3139337 := bstep (se 2 (by rfl) ⟨1177251, by rfl⟩ : syracuseStep 3139337 = 2354503) B2354503
theorem B1042303 : Blo 487790 1042303 := bstep (se 1 (by rfl) ⟨781727, by rfl⟩ : syracuseStep 1042303 = 1563455) B1563455
theorem B1239239 : Blo 487790 1239239 := bstep (se 1 (by rfl) ⟨929429, by rfl⟩ : syracuseStep 1239239 = 1858859) B1858859
theorem B4451195 : Blo 487790 4451195 := bstep (se 1 (by rfl) ⟨3338396, by rfl⟩ : syracuseStep 4451195 = 6676793) B6676793
theorem B1174753 : Blo 487790 1174753 := bstep (se 2 (by rfl) ⟨440532, by rfl⟩ : syracuseStep 1174753 = 881065) B881065
theorem B781759 : Blo 487790 781759 := bstep (se 1 (by rfl) ⟨586319, by rfl⟩ : syracuseStep 781759 = 1172639) B1172639
theorem B2485727 : Blo 487790 2485727 := bstep (se 1 (by rfl) ⟨1864295, by rfl⟩ : syracuseStep 2485727 = 3728591) B3728591
theorem B1240555 : Blo 487790 1240555 := bstep (se 1 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 1240555 = 1860833) B1860833
theorem B2486375 : Blo 487790 2486375 := bstep (se 1 (by rfl) ⟨1864781, by rfl⟩ : syracuseStep 2486375 = 3729563) B3729563
theorem B553243 : Blo 487790 553243 := bstep (se 1 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 553243 = 829865) B829865
theorem B8384957 : Blo 487790 8384957 := bstep (se 3 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 8384957 = 3144359) B3144359
theorem B487911 : Blo 487790 487911 := bstep (se 1 (by rfl) ⟨365933, by rfl⟩ : syracuseStep 487911 = 731867) B731867
theorem B488095 : Blo 487790 488095 := bstep (se 1 (by rfl) ⟨366071, by rfl⟩ : syracuseStep 488095 = 732143) B732143
theorem B488103 : Blo 487790 488103 := bstep (se 1 (by rfl) ⟨366077, by rfl⟩ : syracuseStep 488103 = 732155) B732155
theorem B488143 : Blo 487790 488143 := bstep (se 1 (by rfl) ⟨366107, by rfl⟩ : syracuseStep 488143 = 732215) B732215
theorem B2093849 : Blo 487790 2093849 := bstep (se 2 (by rfl) ⟨785193, by rfl⟩ : syracuseStep 2093849 = 1570387) B1570387
theorem B488223 : Blo 487790 488223 := bstep (se 1 (by rfl) ⟨366167, by rfl⟩ : syracuseStep 488223 = 732335) B732335
theorem B488263 : Blo 487790 488263 := bstep (se 1 (by rfl) ⟨366197, by rfl⟩ : syracuseStep 488263 = 732395) B732395
theorem B5010383 : Blo 487790 5010383 := bstep (se 1 (by rfl) ⟨3757787, by rfl⟩ : syracuseStep 5010383 = 7515575) B7515575
theorem B1864691 : Blo 487790 1864691 := bstep (se 1 (by rfl) ⟨1398518, by rfl⟩ : syracuseStep 1864691 = 2797037) B2797037
theorem B488475 : Blo 487790 488475 := bstep (se 1 (by rfl) ⟨366356, by rfl⟩ : syracuseStep 488475 = 732713) B732713
theorem B488703 : Blo 487790 488703 := bstep (se 1 (by rfl) ⟨366527, by rfl⟩ : syracuseStep 488703 = 733055) B733055
theorem B489711 : Blo 487790 489711 := bstep (se 1 (by rfl) ⟨367283, by rfl⟩ : syracuseStep 489711 = 734567) B734567
theorem B2652581 : Blo 487790 2652581 := bstep (se 4 (by rfl) ⟨248679, by rfl⟩ : syracuseStep 2652581 = 497359) B497359
theorem B15858119 : Blo 487790 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B1112903 : Blo 487790 1112903 := bstep (se 1 (by rfl) ⟨834677, by rfl⟩ : syracuseStep 1112903 = 1669355) B1669355
theorem B490491 : Blo 487790 490491 := bstep (se 1 (by rfl) ⟨367868, by rfl⟩ : syracuseStep 490491 = 735737) B735737
theorem B490735 : Blo 487790 490735 := bstep (se 1 (by rfl) ⟨368051, by rfl⟩ : syracuseStep 490735 = 736103) B736103
theorem B490779 : Blo 487790 490779 := bstep (se 1 (by rfl) ⟨368084, by rfl⟩ : syracuseStep 490779 = 736169) B736169
theorem B1572169 : Blo 487790 1572169 := bstep (se 2 (by rfl) ⟨589563, by rfl⟩ : syracuseStep 1572169 = 1179127) B1179127
theorem B5045615 : Blo 487790 5045615 := bstep (se 1 (by rfl) ⟨3784211, by rfl⟩ : syracuseStep 5045615 = 7568423) B7568423
theorem B5013011 : Blo 487790 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B491167 : Blo 487790 491167 := bstep (se 1 (by rfl) ⟨368375, by rfl⟩ : syracuseStep 491167 = 736751) B736751
theorem B491259 : Blo 487790 491259 := bstep (se 1 (by rfl) ⟨368444, by rfl⟩ : syracuseStep 491259 = 736889) B736889
theorem B8453917 : Blo 487790 8453917 := bstep (se 3 (by rfl) ⟨1585109, by rfl⟩ : syracuseStep 8453917 = 3170219) B3170219
theorem B3178385 : Blo 487790 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B3408911 : Blo 487790 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B4196717 : Blo 487790 4196717 := bstep (se 3 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 4196717 = 1573769) B1573769
theorem B5671415 : Blo 487790 5671415 := bstep (se 1 (by rfl) ⟨4253561, by rfl⟩ : syracuseStep 5671415 = 8507123) B8507123
theorem B7178815 : Blo 487790 7178815 := bstep (se 1 (by rfl) ⟨5384111, by rfl⟩ : syracuseStep 7178815 = 10768223) B10768223
theorem B11046779 : Blo 487790 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B2789315 : Blo 487790 2789315 := bstep (se 1 (by rfl) ⟨2091986, by rfl⟩ : syracuseStep 2789315 = 4183973) B4183973
theorem B5968205 : Blo 487790 5968205 := bstep (se 3 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 5968205 = 2238077) B2238077
theorem B15046195 : Blo 487790 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B826159 : Blo 487790 826159 := bstep (se 1 (by rfl) ⟨619619, by rfl⟩ : syracuseStep 826159 = 1239239) B1239239
theorem B85859615 : Blo 487790 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B7052665 : Blo 487790 7052665 := bstep (se 2 (by rfl) ⟨2644749, by rfl⟩ : syracuseStep 7052665 = 5289499) B5289499
theorem B1646567 : Blo 487790 1646567 := bstep (se 1 (by rfl) ⟨1234925, by rfl⟩ : syracuseStep 1646567 = 2469851) B2469851
theorem B4170473 : Blo 487790 4170473 := bstep (se 2 (by rfl) ⟨1563927, by rfl⟩ : syracuseStep 4170473 = 3127855) B3127855
theorem B6694163 : Blo 487790 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B1419425 : Blo 487790 1419425 := bstep (se 2 (by rfl) ⟨532284, by rfl⟩ : syracuseStep 1419425 = 1064569) B1064569
theorem B731903 : Blo 487790 731903 := bstep (se 1 (by rfl) ⟨548927, by rfl⟩ : syracuseStep 731903 = 1097855) B1097855
theorem B732479 : Blo 487790 732479 := bstep (se 1 (by rfl) ⟨549359, by rfl⟩ : syracuseStep 732479 = 1098719) B1098719
theorem B3714497 : Blo 487790 3714497 := bstep (se 2 (by rfl) ⟨1392936, by rfl⟩ : syracuseStep 3714497 = 2785873) B2785873
theorem B732719 : Blo 487790 732719 := bstep (se 1 (by rfl) ⟨549539, by rfl⟩ : syracuseStep 732719 = 1099079) B1099079
theorem B1650347 : Blo 487790 1650347 := bstep (se 1 (by rfl) ⟨1237760, by rfl⟩ : syracuseStep 1650347 = 2475521) B2475521
theorem B1650401 : Blo 487790 1650401 := bstep (se 2 (by rfl) ⟨618900, by rfl⟩ : syracuseStep 1650401 = 1237801) B1237801
theorem B15249221 : Blo 487790 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B733127 : Blo 487790 733127 := bstep (se 1 (by rfl) ⟨549845, by rfl⟩ : syracuseStep 733127 = 1099691) B1099691
theorem B733631 : Blo 487790 733631 := bstep (se 1 (by rfl) ⟨550223, by rfl⟩ : syracuseStep 733631 = 1100447) B1100447
theorem B2798063 : Blo 487790 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B1323631 : Blo 487790 1323631 := bstep (se 1 (by rfl) ⟨992723, by rfl⟩ : syracuseStep 1323631 = 1985447) B1985447
theorem B1389737 : Blo 487790 1389737 := bstep (se 2 (by rfl) ⟨521151, by rfl⟩ : syracuseStep 1389737 = 1042303) B1042303
theorem B8959319 : Blo 487790 8959319 := bstep (se 1 (by rfl) ⟨6719489, by rfl⟩ : syracuseStep 8959319 = 13438979) B13438979
theorem B1652075 : Blo 487790 1652075 := bstep (se 1 (by rfl) ⟨1239056, by rfl⟩ : syracuseStep 1652075 = 2478113) B2478113
theorem B734975 : Blo 487790 734975 := bstep (se 1 (by rfl) ⟨551231, by rfl⟩ : syracuseStep 734975 = 1102463) B1102463
theorem B735515 : Blo 487790 735515 := bstep (se 1 (by rfl) ⟨551636, by rfl⟩ : syracuseStep 735515 = 1103273) B1103273
theorem B735551 : Blo 487790 735551 := bstep (se 1 (by rfl) ⟨551663, by rfl⟩ : syracuseStep 735551 = 1103327) B1103327
theorem B3717899 : Blo 487790 3717899 := bstep (se 1 (by rfl) ⟨2788424, by rfl⟩ : syracuseStep 3717899 = 5576849) B5576849
theorem B736223 : Blo 487790 736223 := bstep (se 1 (by rfl) ⟨552167, by rfl⟩ : syracuseStep 736223 = 1104335) B1104335
theorem B1654073 : Blo 487790 1654073 := bstep (se 2 (by rfl) ⟨620277, by rfl⟩ : syracuseStep 1654073 = 1240555) B1240555
theorem B933211 : Blo 487790 933211 := bstep (se 1 (by rfl) ⟨699908, by rfl⟩ : syracuseStep 933211 = 1399817) B1399817
theorem B1654559 : Blo 487790 1654559 := bstep (se 1 (by rfl) ⟨1240919, by rfl⟩ : syracuseStep 1654559 = 2481839) B2481839
theorem B1359679 : Blo 487790 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B737087 : Blo 487790 737087 := bstep (se 1 (by rfl) ⟨552815, by rfl⟩ : syracuseStep 737087 = 1105631) B1105631
theorem B737255 : Blo 487790 737255 := bstep (se 1 (by rfl) ⟨552941, by rfl⟩ : syracuseStep 737255 = 1105883) B1105883
theorem B737531 : Blo 487790 737531 := bstep (se 1 (by rfl) ⟨553148, by rfl⟩ : syracuseStep 737531 = 1106297) B1106297
theorem B737657 : Blo 487790 737657 := bstep (se 2 (by rfl) ⟨276621, by rfl⟩ : syracuseStep 737657 = 553243) B553243
theorem B1098143 : Blo 487790 1098143 := bstep (se 1 (by rfl) ⟨823607, by rfl⟩ : syracuseStep 1098143 = 1647215) B1647215
theorem B1327643 : Blo 487790 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B4178537 : Blo 487790 4178537 := bstep (se 2 (by rfl) ⟨1566951, by rfl⟩ : syracuseStep 4178537 = 3133903) B3133903
theorem B1098935 : Blo 487790 1098935 := bstep (se 1 (by rfl) ⟨824201, by rfl⟩ : syracuseStep 1098935 = 1648403) B1648403
theorem B2507965 : Blo 487790 2507965 := bstep (se 3 (by rfl) ⟨470243, by rfl⟩ : syracuseStep 2507965 = 940487) B940487
theorem B7062815 : Blo 487790 7062815 := bstep (se 1 (by rfl) ⟨5297111, by rfl⟩ : syracuseStep 7062815 = 10594223) B10594223
theorem B1099511 : Blo 487790 1099511 := bstep (se 1 (by rfl) ⟨824633, by rfl⟩ : syracuseStep 1099511 = 1649267) B1649267
theorem B2967463 : Blo 487790 2967463 := bstep (se 1 (by rfl) ⟨2225597, by rfl⟩ : syracuseStep 2967463 = 4451195) B4451195
theorem B1657151 : Blo 487790 1657151 := bstep (se 1 (by rfl) ⟨1242863, by rfl⟩ : syracuseStep 1657151 = 2485727) B2485727
theorem B102025601 : Blo 487790 102025601 := bstep (se 2 (by rfl) ⟨38259600, by rfl⟩ : syracuseStep 102025601 = 76519201) B76519201
theorem B1657583 : Blo 487790 1657583 := bstep (se 1 (by rfl) ⟨1243187, by rfl⟩ : syracuseStep 1657583 = 2486375) B2486375
theorem B3132263 : Blo 487790 3132263 := bstep (se 1 (by rfl) ⟨2349197, by rfl⟩ : syracuseStep 3132263 = 4698395) B4698395
theorem B5589971 : Blo 487790 5589971 := bstep (se 1 (by rfl) ⟨4192478, by rfl⟩ : syracuseStep 5589971 = 8384957) B8384957
theorem B1395899 : Blo 487790 1395899 := bstep (se 1 (by rfl) ⟨1046924, by rfl⟩ : syracuseStep 1395899 = 2093849) B2093849
theorem B1494875 : Blo 487790 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B28987409 : Blo 487790 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B1102049 : Blo 487790 1102049 := bstep (se 2 (by rfl) ⟨413268, by rfl⟩ : syracuseStep 1102049 = 826537) B826537
theorem B10572079 : Blo 487790 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B741935 : Blo 487790 741935 := bstep (se 1 (by rfl) ⟨556451, by rfl⟩ : syracuseStep 741935 = 1112903) B1112903
theorem B3363743 : Blo 487790 3363743 := bstep (se 1 (by rfl) ⟨2522807, by rfl⟩ : syracuseStep 3363743 = 5045615) B5045615
theorem B2118923 : Blo 487790 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B1890535 : Blo 487790 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B1857887 : Blo 487790 1857887 := bstep (se 1 (by rfl) ⟨1393415, by rfl⟩ : syracuseStep 1857887 = 2786831) B2786831
theorem B1104425 : Blo 487790 1104425 := bstep (se 2 (by rfl) ⟨414159, by rfl⟩ : syracuseStep 1104425 = 828319) B828319
theorem B4283239 : Blo 487790 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B12409805 : Blo 487790 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B1235999 : Blo 487790 1235999 := bstep (se 1 (by rfl) ⟨926999, by rfl⟩ : syracuseStep 1235999 = 1853999) B1853999
theorem B6282521 : Blo 487790 6282521 := bstep (se 2 (by rfl) ⟨2355945, by rfl⟩ : syracuseStep 6282521 = 4711891) B4711891
theorem B1858889 : Blo 487790 1858889 := bstep (se 2 (by rfl) ⟨697083, by rfl⟩ : syracuseStep 1858889 = 1394167) B1394167
theorem B2317871 : Blo 487790 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B1236617 : Blo 487790 1236617 := bstep (se 2 (by rfl) ⟨463731, by rfl⟩ : syracuseStep 1236617 = 927463) B927463
theorem B1105703 : Blo 487790 1105703 := bstep (se 1 (by rfl) ⟨829277, by rfl⟩ : syracuseStep 1105703 = 1658555) B1658555
theorem B13361021 : Blo 487790 13361021 := bstep (se 3 (by rfl) ⟨2505191, by rfl⟩ : syracuseStep 13361021 = 5010383) B5010383
theorem B1105991 : Blo 487790 1105991 := bstep (se 1 (by rfl) ⟨829493, by rfl⟩ : syracuseStep 1105991 = 1658987) B1658987
theorem B4546705 : Blo 487790 4546705 := bstep (se 2 (by rfl) ⟨1705014, by rfl⟩ : syracuseStep 4546705 = 3410029) B3410029
theorem B1761583 : Blo 487790 1761583 := bstep (se 1 (by rfl) ⟨1321187, by rfl⟩ : syracuseStep 1761583 = 2642375) B2642375
theorem B2975201 : Blo 487790 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B1566337 : Blo 487790 1566337 := bstep (se 2 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 1566337 = 1174753) B1174753
theorem B943759 : Blo 487790 943759 := bstep (se 1 (by rfl) ⟨707819, by rfl⟩ : syracuseStep 943759 = 1415639) B1415639
theorem B1042345 : Blo 487790 1042345 := bstep (se 2 (by rfl) ⟨390879, by rfl⟩ : syracuseStep 1042345 = 781759) B781759
theorem B1796051 : Blo 487790 1796051 := bstep (se 1 (by rfl) ⟨1347038, by rfl⟩ : syracuseStep 1796051 = 2694077) B2694077
theorem B24176837 : Blo 487790 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B551119 : Blo 487790 551119 := bstep (se 1 (by rfl) ⟨413339, by rfl⟩ : syracuseStep 551119 = 826679) B826679
theorem B944467 : Blo 487790 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B2550203 : Blo 487790 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B2517551 : Blo 487790 2517551 := bstep (se 1 (by rfl) ⟨1888163, by rfl⟩ : syracuseStep 2517551 = 3776327) B3776327
theorem B2124569 : Blo 487790 2124569 := bstep (se 2 (by rfl) ⟨796713, by rfl⟩ : syracuseStep 2124569 = 1593427) B1593427
theorem B1240393 : Blo 487790 1240393 := bstep (se 2 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 1240393 = 930295) B930295
theorem B1240697 : Blo 487790 1240697 := bstep (se 2 (by rfl) ⟨465261, by rfl⟩ : syracuseStep 1240697 = 930523) B930523
theorem B1044191 : Blo 487790 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B2092891 : Blo 487790 2092891 := bstep (se 1 (by rfl) ⟨1569668, by rfl⟩ : syracuseStep 2092891 = 3139337) B3139337
theorem B488091 : Blo 487790 488091 := bstep (se 1 (by rfl) ⟨366068, by rfl⟩ : syracuseStep 488091 = 732137) B732137
theorem B488551 : Blo 487790 488551 := bstep (se 1 (by rfl) ⟨366413, by rfl⟩ : syracuseStep 488551 = 732827) B732827
theorem B160495181 : Blo 487790 160495181 := bstep (se 3 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 160495181 = 60185693) B60185693
theorem B620455 : Blo 487790 620455 := bstep (se 1 (by rfl) ⟨465341, by rfl⟩ : syracuseStep 620455 = 930683) B930683
theorem B1865663 : Blo 487790 1865663 := bstep (se 1 (by rfl) ⟨1399247, by rfl⟩ : syracuseStep 1865663 = 2798495) B2798495
theorem B1243127 : Blo 487790 1243127 := bstep (se 1 (by rfl) ⟨932345, by rfl⟩ : syracuseStep 1243127 = 1864691) B1864691
theorem B489471 : Blo 487790 489471 := bstep (se 1 (by rfl) ⟨367103, by rfl⟩ : syracuseStep 489471 = 734207) B734207
theorem B489535 : Blo 487790 489535 := bstep (se 1 (by rfl) ⟨367151, by rfl⟩ : syracuseStep 489535 = 734303) B734303
theorem B489695 : Blo 487790 489695 := bstep (se 1 (by rfl) ⟨367271, by rfl⟩ : syracuseStep 489695 = 734543) B734543
theorem B489855 : Blo 487790 489855 := bstep (se 1 (by rfl) ⟨367391, by rfl⟩ : syracuseStep 489855 = 734783) B734783
theorem B490139 : Blo 487790 490139 := bstep (se 1 (by rfl) ⟨367604, by rfl⟩ : syracuseStep 490139 = 735209) B735209
theorem B2783915 : Blo 487790 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B490175 : Blo 487790 490175 := bstep (se 1 (by rfl) ⟨367631, by rfl⟩ : syracuseStep 490175 = 735263) B735263
theorem B490303 : Blo 487790 490303 := bstep (se 1 (by rfl) ⟨367727, by rfl⟩ : syracuseStep 490303 = 735455) B735455
theorem B1768387 : Blo 487790 1768387 := bstep (se 1 (by rfl) ⟨1326290, by rfl⟩ : syracuseStep 1768387 = 2652581) B2652581
theorem B490559 : Blo 487790 490559 := bstep (se 1 (by rfl) ⟨367919, by rfl⟩ : syracuseStep 490559 = 735839) B735839
theorem B2096225 : Blo 487790 2096225 := bstep (se 2 (by rfl) ⟨786084, by rfl⟩ : syracuseStep 2096225 = 1572169) B1572169
theorem B490607 : Blo 487790 490607 := bstep (se 1 (by rfl) ⟨367955, by rfl⟩ : syracuseStep 490607 = 735911) B735911
theorem B490623 : Blo 487790 490623 := bstep (se 1 (by rfl) ⟨367967, by rfl⟩ : syracuseStep 490623 = 735935) B735935
theorem B2391383 : Blo 487790 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B490879 : Blo 487790 490879 := bstep (se 1 (by rfl) ⟨368159, by rfl⟩ : syracuseStep 490879 = 736319) B736319
theorem B3342007 : Blo 487790 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B11271889 : Blo 487790 11271889 := bstep (se 2 (by rfl) ⟨4226958, by rfl⟩ : syracuseStep 11271889 = 8453917) B8453917
theorem B77299757 : Blo 487790 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B491687 : Blo 487790 491687 := bstep (se 1 (by rfl) ⟨368765, by rfl⟩ : syracuseStep 491687 = 737531) B737531
theorem B6062273 : Blo 487790 6062273 := bstep (se 2 (by rfl) ⟨2273352, by rfl⟩ : syracuseStep 6062273 = 4546705) B4546705
theorem B491771 : Blo 487790 491771 := bstep (se 1 (by rfl) ⟨368828, by rfl⟩ : syracuseStep 491771 = 737657) B737657
theorem B885095 : Blo 487790 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B2785691 : Blo 487790 2785691 := bstep (se 1 (by rfl) ⟨2089268, by rfl⟩ : syracuseStep 2785691 = 4178537) B4178537
theorem B15140533 : Blo 487790 15140533 := bstep (se 5 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 15140533 = 1419425) B1419425
theorem B494623 : Blo 487790 494623 := bstep (se 1 (by rfl) ⟨370967, by rfl⟩ : syracuseStep 494623 = 741935) B741935
theorem B9571753 : Blo 487790 9571753 := bstep (se 2 (by rfl) ⟨3589407, by rfl⟩ : syracuseStep 9571753 = 7178815) B7178815
theorem B1412615 : Blo 487790 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B823999 : Blo 487790 823999 := bstep (se 1 (by rfl) ⟨617999, by rfl⟩ : syracuseStep 823999 = 1235999) B1235999
theorem B1545247 : Blo 487790 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B824411 : Blo 487790 824411 := bstep (se 1 (by rfl) ⟨618308, by rfl⟩ : syracuseStep 824411 = 1236617) B1236617
theorem B2790521 : Blo 487790 2790521 := bstep (se 2 (by rfl) ⟨1046445, by rfl⟩ : syracuseStep 2790521 = 2092891) B2092891
theorem B4789469 : Blo 487790 4789469 := bstep (se 3 (by rfl) ⟨898025, by rfl⟩ : syracuseStep 4789469 = 1796051) B1796051
theorem B14096105 : Blo 487790 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B4462775 : Blo 487790 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B13375813 : Blo 487790 13375813 := bstep (se 4 (by rfl) ⟨1253982, by rfl⟩ : syracuseStep 13375813 = 2507965) B2507965
theorem B1678367 : Blo 487790 1678367 := bstep (se 1 (by rfl) ⟨1258775, by rfl⟩ : syracuseStep 1678367 = 2517551) B2517551
theorem B1416379 : Blo 487790 1416379 := bstep (se 1 (by rfl) ⟨1062284, by rfl⟩ : syracuseStep 1416379 = 2124569) B2124569
theorem B20061593 : Blo 487790 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B827131 : Blo 487790 827131 := bstep (se 1 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 827131 = 1240697) B1240697
theorem B696127 : Blo 487790 696127 := bstep (se 1 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 696127 = 1044191) B1044191
theorem B10166147 : Blo 487790 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B827273 : Blo 487790 827273 := bstep (se 2 (by rfl) ⟨310227, by rfl⟩ : syracuseStep 827273 = 620455) B620455
theorem B926491 : Blo 487790 926491 := bstep (se 1 (by rfl) ⟨694868, by rfl⟩ : syracuseStep 926491 = 1389737) B1389737
theorem B5972879 : Blo 487790 5972879 := bstep (se 1 (by rfl) ⟨4479659, by rfl⟩ : syracuseStep 5972879 = 8959319) B8959319
theorem B106996787 : Blo 487790 106996787 := bstep (se 1 (by rfl) ⟨80247590, by rfl⟩ : syracuseStep 106996787 = 160495181) B160495181
theorem B5710985 : Blo 487790 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B828751 : Blo 487790 828751 := bstep (se 1 (by rfl) ⟨621563, by rfl⟩ : syracuseStep 828751 = 1243127) B1243127
theorem B1812905 : Blo 487790 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B732095 : Blo 487790 732095 := bstep (se 1 (by rfl) ⟨549071, by rfl⟩ : syracuseStep 732095 = 1098143) B1098143
theorem B2272607 : Blo 487790 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B732623 : Blo 487790 732623 := bstep (se 1 (by rfl) ⟨549467, by rfl⟩ : syracuseStep 732623 = 1098935) B1098935
theorem B733007 : Blo 487790 733007 := bstep (se 1 (by rfl) ⟨549755, by rfl⟩ : syracuseStep 733007 = 1099511) B1099511
theorem B2797811 : Blo 487790 2797811 := bstep (se 1 (by rfl) ⟨2098358, by rfl⟩ : syracuseStep 2797811 = 4196717) B4196717
theorem B930599 : Blo 487790 930599 := bstep (se 1 (by rfl) ⟨697949, by rfl⟩ : syracuseStep 930599 = 1395899) B1395899
theorem B1258345 : Blo 487790 1258345 := bstep (se 2 (by rfl) ⟨471879, by rfl⟩ : syracuseStep 1258345 = 943759) B943759
theorem B1389793 : Blo 487790 1389793 := bstep (se 2 (by rfl) ⟨521172, by rfl⟩ : syracuseStep 1389793 = 1042345) B1042345
theorem B734699 : Blo 487790 734699 := bstep (se 1 (by rfl) ⟨551024, by rfl⟩ : syracuseStep 734699 = 1102049) B1102049
theorem B3978803 : Blo 487790 3978803 := bstep (se 1 (by rfl) ⟨2984102, by rfl⟩ : syracuseStep 3978803 = 5968205) B5968205
theorem B734825 : Blo 487790 734825 := bstep (se 2 (by rfl) ⟨275559, by rfl⟩ : syracuseStep 734825 = 551119) B551119
theorem B2242495 : Blo 487790 2242495 := bstep (se 1 (by rfl) ⟨1681871, by rfl⟩ : syracuseStep 2242495 = 3363743) B3363743
theorem B736283 : Blo 487790 736283 := bstep (se 1 (by rfl) ⟨552212, by rfl⟩ : syracuseStep 736283 = 1104425) B1104425
theorem B1653857 : Blo 487790 1653857 := bstep (se 2 (by rfl) ⟨620196, by rfl⟩ : syracuseStep 1653857 = 1240393) B1240393
theorem B737135 : Blo 487790 737135 := bstep (se 1 (by rfl) ⟨552851, by rfl⟩ : syracuseStep 737135 = 1105703) B1105703
theorem B1097711 : Blo 487790 1097711 := bstep (se 1 (by rfl) ⟨823283, by rfl⟩ : syracuseStep 1097711 = 1646567) B1646567
theorem B737327 : Blo 487790 737327 := bstep (se 1 (by rfl) ⟨552995, by rfl⟩ : syracuseStep 737327 = 1105991) B1105991
theorem B64471565 : Blo 487790 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B1983467 : Blo 487790 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B15123773 : Blo 487790 15123773 := bstep (se 3 (by rfl) ⟨2835707, by rfl⟩ : syracuseStep 15123773 = 5671415) B5671415
theorem B2476331 : Blo 487790 2476331 := bstep (se 1 (by rfl) ⟨1857248, by rfl⟩ : syracuseStep 2476331 = 3714497) B3714497
theorem B1100231 : Blo 487790 1100231 := bstep (se 1 (by rfl) ⟨825173, by rfl⟩ : syracuseStep 1100231 = 1650347) B1650347
theorem B1100267 : Blo 487790 1100267 := bstep (se 1 (by rfl) ⟨825200, by rfl⟩ : syracuseStep 1100267 = 1650401) B1650401
theorem B1101383 : Blo 487790 1101383 := bstep (se 1 (by rfl) ⟨826037, by rfl⟩ : syracuseStep 1101383 = 1652075) B1652075
theorem B1101545 : Blo 487790 1101545 := bstep (se 2 (by rfl) ⟨413079, by rfl⟩ : syracuseStep 1101545 = 826159) B826159
theorem B1855943 : Blo 487790 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B2478599 : Blo 487790 2478599 := bstep (se 1 (by rfl) ⟨1858949, by rfl⟩ : syracuseStep 2478599 = 3717899) B3717899
theorem B1397483 : Blo 487790 1397483 := bstep (se 1 (by rfl) ⟨1048112, by rfl⟩ : syracuseStep 1397483 = 2096225) B2096225
theorem B1102715 : Blo 487790 1102715 := bstep (se 1 (by rfl) ⟨827036, by rfl⟩ : syracuseStep 1102715 = 1654073) B1654073
theorem B1594255 : Blo 487790 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B3986333 : Blo 487790 3986333 := bstep (se 3 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 3986333 = 1494875) B1494875
theorem B15029185 : Blo 487790 15029185 := bstep (se 2 (by rfl) ⟨5635944, by rfl⟩ : syracuseStep 15029185 = 11271889) B11271889
theorem B1103039 : Blo 487790 1103039 := bstep (se 1 (by rfl) ⟨827279, by rfl⟩ : syracuseStep 1103039 = 1654559) B1654559
theorem B2348777 : Blo 487790 2348777 := bstep (se 2 (by rfl) ⟨880791, by rfl⟩ : syracuseStep 2348777 = 1761583) B1761583
theorem B4708543 : Blo 487790 4708543 := bstep (se 1 (by rfl) ⟨3531407, by rfl⟩ : syracuseStep 4708543 = 7062815) B7062815
theorem B1104767 : Blo 487790 1104767 := bstep (se 1 (by rfl) ⟨828575, by rfl⟩ : syracuseStep 1104767 = 1657151) B1657151
theorem B68017067 : Blo 487790 68017067 := bstep (se 1 (by rfl) ⟨51012800, by rfl⟩ : syracuseStep 68017067 = 102025601) B102025601
theorem B5037157 : Blo 487790 5037157 := bstep (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) B944467
theorem B1105055 : Blo 487790 1105055 := bstep (se 1 (by rfl) ⟨828791, by rfl⟩ : syracuseStep 1105055 = 1657583) B1657583
theorem B2088175 : Blo 487790 2088175 := bstep (se 1 (by rfl) ⟨1566131, by rfl⟩ : syracuseStep 2088175 = 3132263) B3132263
theorem B3726647 : Blo 487790 3726647 := bstep (se 1 (by rfl) ⟨2794985, by rfl⟩ : syracuseStep 3726647 = 5589971) B5589971
theorem B2088449 : Blo 487790 2088449 := bstep (se 2 (by rfl) ⟨783168, by rfl⟩ : syracuseStep 2088449 = 1566337) B1566337
theorem B3956617 : Blo 487790 3956617 := bstep (se 2 (by rfl) ⟨1483731, by rfl⟩ : syracuseStep 3956617 = 2967463) B2967463
theorem B7364519 : Blo 487790 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B1859543 : Blo 487790 1859543 := bstep (se 1 (by rfl) ⟨1394657, by rfl⟩ : syracuseStep 1859543 = 2789315) B2789315
theorem B1238591 : Blo 487790 1238591 := bstep (se 1 (by rfl) ⟨928943, by rfl⟩ : syracuseStep 1238591 = 1857887) B1857887
theorem B4188347 : Blo 487790 4188347 := bstep (se 1 (by rfl) ⟨3141260, by rfl⟩ : syracuseStep 4188347 = 6282521) B6282521
theorem B57239743 : Blo 487790 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B1239259 : Blo 487790 1239259 := bstep (se 1 (by rfl) ⟨929444, by rfl⟩ : syracuseStep 1239259 = 1858889) B1858889
theorem B8907347 : Blo 487790 8907347 := bstep (se 1 (by rfl) ⟨6680510, by rfl⟩ : syracuseStep 8907347 = 13361021) B13361021
theorem B2780315 : Blo 487790 2780315 := bstep (se 1 (by rfl) ⟨2085236, by rfl⟩ : syracuseStep 2780315 = 4170473) B4170473
theorem B1764841 : Blo 487790 1764841 := bstep (se 2 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 1764841 = 1323631) B1323631
theorem B1700135 : Blo 487790 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B487935 : Blo 487790 487935 := bstep (se 1 (by rfl) ⟨365951, by rfl⟩ : syracuseStep 487935 = 731903) B731903
theorem B488319 : Blo 487790 488319 := bstep (se 1 (by rfl) ⟨366239, by rfl⟩ : syracuseStep 488319 = 732479) B732479
theorem B488479 : Blo 487790 488479 := bstep (se 1 (by rfl) ⟨366359, by rfl⟩ : syracuseStep 488479 = 732719) B732719
theorem B33092813 : Blo 487790 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B488751 : Blo 487790 488751 := bstep (se 1 (by rfl) ⟨366563, by rfl⟩ : syracuseStep 488751 = 733127) B733127
theorem B489087 : Blo 487790 489087 := bstep (se 1 (by rfl) ⟨366815, by rfl⟩ : syracuseStep 489087 = 733631) B733631
theorem B2520713 : Blo 487790 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B1865375 : Blo 487790 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B489983 : Blo 487790 489983 := bstep (se 1 (by rfl) ⟨367487, by rfl⟩ : syracuseStep 489983 = 734975) B734975
theorem B2357849 : Blo 487790 2357849 := bstep (se 2 (by rfl) ⟨884193, by rfl⟩ : syracuseStep 2357849 = 1768387) B1768387
theorem B1243775 : Blo 487790 1243775 := bstep (se 1 (by rfl) ⟨932831, by rfl⟩ : syracuseStep 1243775 = 1865663) B1865663
theorem B490343 : Blo 487790 490343 := bstep (se 1 (by rfl) ⟨367757, by rfl⟩ : syracuseStep 490343 = 735515) B735515
theorem B490367 : Blo 487790 490367 := bstep (se 1 (by rfl) ⟨367775, by rfl⟩ : syracuseStep 490367 = 735551) B735551
theorem B1244281 : Blo 487790 1244281 := bstep (se 2 (by rfl) ⟨466605, by rfl⟩ : syracuseStep 1244281 = 933211) B933211
theorem B9403553 : Blo 487790 9403553 := bstep (se 2 (by rfl) ⟨3526332, by rfl⟩ : syracuseStep 9403553 = 7052665) B7052665
theorem B490815 : Blo 487790 490815 := bstep (se 1 (by rfl) ⟨368111, by rfl⟩ : syracuseStep 490815 = 736223) B736223
theorem B4456009 : Blo 487790 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B491391 : Blo 487790 491391 := bstep (se 1 (by rfl) ⟨368543, by rfl⟩ : syracuseStep 491391 = 737087) B737087
theorem B491503 : Blo 487790 491503 := bstep (se 1 (by rfl) ⟨368627, by rfl⟩ : syracuseStep 491503 = 737255) B737255
theorem B491551 : Blo 487790 491551 := bstep (se 1 (by rfl) ⟨368663, by rfl⟩ : syracuseStep 491551 = 737327) B737327
theorem B590063 : Blo 487790 590063 := bstep (se 1 (by rfl) ⟨442547, by rfl⟩ : syracuseStep 590063 = 885095) B885095
theorem B20187377 : Blo 487790 20187377 := bstep (se 2 (by rfl) ⟨7570266, by rfl⟩ : syracuseStep 20187377 = 15140533) B15140533
theorem B76319657 : Blo 487790 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B88247501 : Blo 487790 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B2657555 : Blo 487790 2657555 := bstep (se 1 (by rfl) ⟨1993166, by rfl⟩ : syracuseStep 2657555 = 3986333) B3986333
theorem B659497 : Blo 487790 659497 := bstep (se 2 (by rfl) ⟨247311, by rfl⟩ : syracuseStep 659497 = 494623) B494623
theorem B13374395 : Blo 487790 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B3807323 : Blo 487790 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B825727 : Blo 487790 825727 := bstep (se 1 (by rfl) ⟨619295, by rfl⟩ : syracuseStep 825727 = 1238591) B1238591
theorem B2792231 : Blo 487790 2792231 := bstep (se 1 (by rfl) ⟨2094173, by rfl⟩ : syracuseStep 2792231 = 4188347) B4188347
theorem B1515071 : Blo 487790 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B2989993 : Blo 487790 2989993 := bstep (se 2 (by rfl) ⟨1121247, by rfl⟩ : syracuseStep 2989993 = 2242495) B2242495
theorem B17834417 : Blo 487790 17834417 := bstep (se 2 (by rfl) ⟨6687906, by rfl⟩ : syracuseStep 17834417 = 13375813) B13375813
theorem B1680475 : Blo 487790 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B829183 : Blo 487790 829183 := bstep (se 1 (by rfl) ⟨621887, by rfl⟩ : syracuseStep 829183 = 1243775) B1243775
theorem B5941345 : Blo 487790 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B6269035 : Blo 487790 6269035 := bstep (se 1 (by rfl) ⟨4701776, by rfl⟩ : syracuseStep 6269035 = 9403553) B9403553
theorem B928169 : Blo 487790 928169 := bstep (se 2 (by rfl) ⟨348063, by rfl⟩ : syracuseStep 928169 = 696127) B696127
theorem B731807 : Blo 487790 731807 := bstep (se 1 (by rfl) ⟨548855, by rfl⟩ : syracuseStep 731807 = 1097711) B1097711
theorem B4041515 : Blo 487790 4041515 := bstep (se 1 (by rfl) ⟨3031136, by rfl⟩ : syracuseStep 4041515 = 6062273) B6062273
theorem B1650887 : Blo 487790 1650887 := bstep (se 1 (by rfl) ⟨1238165, by rfl⟩ : syracuseStep 1650887 = 2476331) B2476331
theorem B733487 : Blo 487790 733487 := bstep (se 1 (by rfl) ⟨550115, by rfl⟩ : syracuseStep 733487 = 1100231) B1100231
theorem B733511 : Blo 487790 733511 := bstep (se 1 (by rfl) ⟨550133, by rfl⟩ : syracuseStep 733511 = 1100267) B1100267
theorem B734255 : Blo 487790 734255 := bstep (se 1 (by rfl) ⟨550691, by rfl⟩ : syracuseStep 734255 = 1101383) B1101383
theorem B734363 : Blo 487790 734363 := bstep (se 1 (by rfl) ⟨550772, by rfl⟩ : syracuseStep 734363 = 1101545) B1101545
theorem B5289245 : Blo 487790 5289245 := bstep (se 3 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 5289245 = 1983467) B1983467
theorem B1652345 : Blo 487790 1652345 := bstep (se 2 (by rfl) ⟨619629, by rfl⟩ : syracuseStep 1652345 = 1239259) B1239259
theorem B1652399 : Blo 487790 1652399 := bstep (se 1 (by rfl) ⟨1239299, by rfl⟩ : syracuseStep 1652399 = 2478599) B2478599
theorem B931655 : Blo 487790 931655 := bstep (se 1 (by rfl) ⟨698741, by rfl⟩ : syracuseStep 931655 = 1397483) B1397483
theorem B735143 : Blo 487790 735143 := bstep (se 1 (by rfl) ⟨551357, by rfl⟩ : syracuseStep 735143 = 1102715) B1102715
theorem B735359 : Blo 487790 735359 := bstep (se 1 (by rfl) ⟨551519, by rfl⟩ : syracuseStep 735359 = 1103039) B1103039
theorem B3192979 : Blo 487790 3192979 := bstep (se 1 (by rfl) ⟨2394734, by rfl⟩ : syracuseStep 3192979 = 4789469) B4789469
theorem B736511 : Blo 487790 736511 := bstep (se 1 (by rfl) ⟨552383, by rfl⟩ : syracuseStep 736511 = 1104767) B1104767
theorem B736703 : Blo 487790 736703 := bstep (se 1 (by rfl) ⟨552527, by rfl⟩ : syracuseStep 736703 = 1105055) B1105055
theorem B1392299 : Blo 487790 1392299 := bstep (se 1 (by rfl) ⟨1044224, by rfl⟩ : syracuseStep 1392299 = 2088449) B2088449
theorem B3981919 : Blo 487790 3981919 := bstep (se 1 (by rfl) ⟨2986439, by rfl⟩ : syracuseStep 3981919 = 5972879) B5972879
theorem B1098665 : Blo 487790 1098665 := bstep (se 2 (by rfl) ⟨411999, by rfl⟩ : syracuseStep 1098665 = 823999) B823999
theorem B20038913 : Blo 487790 20038913 := bstep (se 2 (by rfl) ⟨7514592, by rfl⟩ : syracuseStep 20038913 = 15029185) B15029185
theorem B1853057 : Blo 487790 1853057 := bstep (se 2 (by rfl) ⟨694896, by rfl⟩ : syracuseStep 1853057 = 1389793) B1389793
theorem B1853543 : Blo 487790 1853543 := bstep (se 1 (by rfl) ⟨1390157, by rfl⟩ : syracuseStep 1853543 = 2780315) B2780315
theorem B4475645 : Blo 487790 4475645 := bstep (se 3 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 4475645 = 1678367) B1678367
theorem B1133423 : Blo 487790 1133423 := bstep (se 1 (by rfl) ⟨850067, by rfl⟩ : syracuseStep 1133423 = 1700135) B1700135
theorem B6278057 : Blo 487790 6278057 := bstep (se 2 (by rfl) ⟨2354271, by rfl⟩ : syracuseStep 6278057 = 4708543) B4708543
theorem B1659041 : Blo 487790 1659041 := bstep (se 2 (by rfl) ⟨622140, by rfl⟩ : syracuseStep 1659041 = 1244281) B1244281
theorem B1888505 : Blo 487790 1888505 := bstep (se 2 (by rfl) ⟨708189, by rfl⟩ : syracuseStep 1888505 = 1416379) B1416379
theorem B1102571 : Blo 487790 1102571 := bstep (se 1 (by rfl) ⟨826928, by rfl⟩ : syracuseStep 1102571 = 1653857) B1653857
theorem B1102841 : Blo 487790 1102841 := bstep (se 2 (by rfl) ⟨413565, by rfl⟩ : syracuseStep 1102841 = 827131) B827131
theorem B51533171 : Blo 487790 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B1857127 : Blo 487790 1857127 := bstep (se 1 (by rfl) ⟨1392845, by rfl⟩ : syracuseStep 1857127 = 2785691) B2785691
theorem B42981043 : Blo 487790 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B10082515 : Blo 487790 10082515 := bstep (se 1 (by rfl) ⟨7561886, by rfl⟩ : syracuseStep 10082515 = 15123773) B15123773
theorem B1235321 : Blo 487790 1235321 := bstep (se 2 (by rfl) ⟨463245, by rfl⟩ : syracuseStep 1235321 = 926491) B926491
theorem B1105001 : Blo 487790 1105001 := bstep (se 2 (by rfl) ⟨414375, by rfl⟩ : syracuseStep 1105001 = 828751) B828751
theorem B941743 : Blo 487790 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B1237295 : Blo 487790 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B549607 : Blo 487790 549607 := bstep (se 1 (by rfl) ⟨412205, by rfl⟩ : syracuseStep 549607 = 824411) B824411
theorem B1860347 : Blo 487790 1860347 := bstep (se 1 (by rfl) ⟨1395260, by rfl⟩ : syracuseStep 1860347 = 2790521) B2790521
theorem B1565851 : Blo 487790 1565851 := bstep (se 1 (by rfl) ⟨1174388, by rfl⟩ : syracuseStep 1565851 = 2348777) B2348777
theorem B9397403 : Blo 487790 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B2975183 : Blo 487790 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B6711173 : Blo 487790 6711173 := bstep (se 4 (by rfl) ⟨629172, by rfl⟩ : syracuseStep 6711173 = 1258345) B1258345
theorem B45344711 : Blo 487790 45344711 := bstep (se 1 (by rfl) ⟨34008533, by rfl⟩ : syracuseStep 45344711 = 68017067) B68017067
theorem B2353121 : Blo 487790 2353121 := bstep (se 2 (by rfl) ⟨882420, by rfl⟩ : syracuseStep 2353121 = 1764841) B1764841
theorem B2484431 : Blo 487790 2484431 := bstep (se 1 (by rfl) ⟨1863323, by rfl⟩ : syracuseStep 2484431 = 3726647) B3726647
theorem B6777431 : Blo 487790 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B551515 : Blo 487790 551515 := bstep (se 1 (by rfl) ⟨413636, by rfl⟩ : syracuseStep 551515 = 827273) B827273
theorem B4909679 : Blo 487790 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B1239695 : Blo 487790 1239695 := bstep (se 1 (by rfl) ⟨929771, by rfl⟩ : syracuseStep 1239695 = 1859543) B1859543
theorem B71331191 : Blo 487790 71331191 := bstep (se 1 (by rfl) ⟨53498393, by rfl⟩ : syracuseStep 71331191 = 106996787) B106996787
theorem B2125673 : Blo 487790 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B2060329 : Blo 487790 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B23752925 : Blo 487790 23752925 := bstep (se 3 (by rfl) ⟨4453673, by rfl⟩ : syracuseStep 23752925 = 8907347) B8907347
theorem B1208603 : Blo 487790 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B488063 : Blo 487790 488063 := bstep (se 1 (by rfl) ⟨366047, by rfl⟩ : syracuseStep 488063 = 732095) B732095
theorem B51049349 : Blo 487790 51049349 := bstep (se 4 (by rfl) ⟨4785876, by rfl⟩ : syracuseStep 51049349 = 9571753) B9571753
theorem B488415 : Blo 487790 488415 := bstep (se 1 (by rfl) ⟨366311, by rfl⟩ : syracuseStep 488415 = 732623) B732623
theorem B488671 : Blo 487790 488671 := bstep (se 1 (by rfl) ⟨366503, by rfl⟩ : syracuseStep 488671 = 733007) B733007
theorem B1865207 : Blo 487790 1865207 := bstep (se 1 (by rfl) ⟨1398905, by rfl⟩ : syracuseStep 1865207 = 2797811) B2797811
theorem B620399 : Blo 487790 620399 := bstep (se 1 (by rfl) ⟨465299, by rfl⟩ : syracuseStep 620399 = 930599) B930599
theorem B489799 : Blo 487790 489799 := bstep (se 1 (by rfl) ⟨367349, by rfl⟩ : syracuseStep 489799 = 734699) B734699
theorem B2652535 : Blo 487790 2652535 := bstep (se 1 (by rfl) ⟨1989401, by rfl⟩ : syracuseStep 2652535 = 3978803) B3978803
theorem B489883 : Blo 487790 489883 := bstep (se 1 (by rfl) ⟨367412, by rfl⟩ : syracuseStep 489883 = 734825) B734825
theorem B1243583 : Blo 487790 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B6716209 : Blo 487790 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B2784233 : Blo 487790 2784233 := bstep (se 2 (by rfl) ⟨1044087, by rfl⟩ : syracuseStep 2784233 = 2088175) B2088175
theorem B1571899 : Blo 487790 1571899 := bstep (se 1 (by rfl) ⟨1178924, by rfl⟩ : syracuseStep 1571899 = 2357849) B2357849
theorem B490855 : Blo 487790 490855 := bstep (se 1 (by rfl) ⟨368141, by rfl⟩ : syracuseStep 490855 = 736283) B736283
theorem B5275489 : Blo 487790 5275489 := bstep (se 2 (by rfl) ⟨1978308, by rfl⟩ : syracuseStep 5275489 = 3956617) B3956617
theorem B491423 : Blo 487790 491423 := bstep (se 1 (by rfl) ⟨368567, by rfl⟩ : syracuseStep 491423 = 737135) B737135
theorem B1573501 : Blo 487790 1573501 := bstep (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) B590063
theorem B5309225 : Blo 487790 5309225 := bstep (se 2 (by rfl) ⟨1990959, by rfl⟩ : syracuseStep 5309225 = 3981919) B3981919
theorem B2983763 : Blo 487790 2983763 := bstep (se 1 (by rfl) ⟨2237822, by rfl⟩ : syracuseStep 2983763 = 4475645) B4475645
theorem B755615 : Blo 487790 755615 := bstep (se 1 (by rfl) ⟨566711, by rfl⟩ : syracuseStep 755615 = 1133423) B1133423
theorem B1771703 : Blo 487790 1771703 := bstep (se 1 (by rfl) ⟨1328777, by rfl⟩ : syracuseStep 1771703 = 2657555) B2657555
theorem B8358713 : Blo 487790 8358713 := bstep (se 2 (by rfl) ⟨3134517, by rfl⟩ : syracuseStep 8358713 = 6269035) B6269035
theorem B8916263 : Blo 487790 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B823547 : Blo 487790 823547 := bstep (se 1 (by rfl) ⟨617660, by rfl⟩ : syracuseStep 823547 = 1235321) B1235321
theorem B824863 : Blo 487790 824863 := bstep (se 1 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 824863 = 1237295) B1237295
theorem B6264935 : Blo 487790 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B826463 : Blo 487790 826463 := bstep (se 1 (by rfl) ⟨619847, by rfl⟩ : syracuseStep 826463 = 1239695) B1239695
theorem B2694343 : Blo 487790 2694343 := bstep (se 1 (by rfl) ⟨2020757, by rfl⟩ : syracuseStep 2694343 = 4041515) B4041515
theorem B47554127 : Blo 487790 47554127 := bstep (se 1 (by rfl) ⟨35665595, by rfl⟩ : syracuseStep 47554127 = 71331191) B71331191
theorem B1417115 : Blo 487790 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B15835283 : Blo 487790 15835283 := bstep (se 1 (by rfl) ⟨11876462, by rfl⟩ : syracuseStep 15835283 = 23752925) B23752925
theorem B13443353 : Blo 487790 13443353 := bstep (se 2 (by rfl) ⟨5041257, by rfl⟩ : syracuseStep 13443353 = 10082515) B10082515
theorem B8954945 : Blo 487790 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B4040189 : Blo 487790 4040189 := bstep (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) B1515071
theorem B829055 : Blo 487790 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B1255657 : Blo 487790 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B928199 : Blo 487790 928199 := bstep (se 1 (by rfl) ⟨696149, by rfl⟩ : syracuseStep 928199 = 1392299) B1392299
theorem B732443 : Blo 487790 732443 := bstep (se 1 (by rfl) ⟨549332, by rfl⟩ : syracuseStep 732443 = 1098665) B1098665
theorem B732809 : Blo 487790 732809 := bstep (se 2 (by rfl) ⟨274803, by rfl⟩ : syracuseStep 732809 = 549607) B549607
theorem B2240633 : Blo 487790 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B58831667 : Blo 487790 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B1259003 : Blo 487790 1259003 := bstep (se 1 (by rfl) ⟨944252, by rfl⟩ : syracuseStep 1259003 = 1888505) B1888505
theorem B735047 : Blo 487790 735047 := bstep (se 1 (by rfl) ⟨551285, by rfl⟩ : syracuseStep 735047 = 1102571) B1102571
theorem B735227 : Blo 487790 735227 := bstep (se 1 (by rfl) ⟨551420, by rfl⟩ : syracuseStep 735227 = 1102841) B1102841
theorem B735353 : Blo 487790 735353 := bstep (se 2 (by rfl) ⟨275757, by rfl⟩ : syracuseStep 735353 = 551515) B551515
theorem B34355447 : Blo 487790 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B2538215 : Blo 487790 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B736667 : Blo 487790 736667 := bstep (se 1 (by rfl) ⟨552500, by rfl⟩ : syracuseStep 736667 = 1105001) B1105001
theorem B1654397 : Blo 487790 1654397 := bstep (se 3 (by rfl) ⟨310199, by rfl⟩ : syracuseStep 1654397 = 620399) B620399
theorem B1983455 : Blo 487790 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B4474115 : Blo 487790 4474115 := bstep (se 1 (by rfl) ⟨3355586, by rfl⟩ : syracuseStep 4474115 = 6711173) B6711173
theorem B30229807 : Blo 487790 30229807 := bstep (se 1 (by rfl) ⟨22672355, by rfl⟩ : syracuseStep 30229807 = 45344711) B45344711
theorem B1656287 : Blo 487790 1656287 := bstep (se 1 (by rfl) ⟨1242215, by rfl⟩ : syracuseStep 1656287 = 2484431) B2484431
theorem B2476169 : Blo 487790 2476169 := bstep (se 2 (by rfl) ⟨928563, by rfl⟩ : syracuseStep 2476169 = 1857127) B1857127
theorem B1100591 : Blo 487790 1100591 := bstep (se 1 (by rfl) ⟨825443, by rfl⟩ : syracuseStep 1100591 = 1650887) B1650887
theorem B805735 : Blo 487790 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B1100969 : Blo 487790 1100969 := bstep (se 2 (by rfl) ⟨412863, by rfl⟩ : syracuseStep 1100969 = 825727) B825727
theorem B34032899 : Blo 487790 34032899 := bstep (se 1 (by rfl) ⟨25524674, by rfl⟩ : syracuseStep 34032899 = 51049349) B51049349
theorem B3526163 : Blo 487790 3526163 := bstep (se 1 (by rfl) ⟨2644622, by rfl⟩ : syracuseStep 3526163 = 5289245) B5289245
theorem B1101563 : Blo 487790 1101563 := bstep (se 1 (by rfl) ⟨826172, by rfl⟩ : syracuseStep 1101563 = 1652345) B1652345
theorem B1101599 : Blo 487790 1101599 := bstep (se 1 (by rfl) ⟨826199, by rfl⟩ : syracuseStep 1101599 = 1652399) B1652399
theorem B1856155 : Blo 487790 1856155 := bstep (se 1 (by rfl) ⟨1392116, by rfl⟩ : syracuseStep 1856155 = 2784233) B2784233
theorem B7033985 : Blo 487790 7033985 := bstep (se 2 (by rfl) ⟨2637744, by rfl⟩ : syracuseStep 7033985 = 5275489) B5275489
theorem B3986657 : Blo 487790 3986657 := bstep (se 2 (by rfl) ⟨1494996, by rfl⟩ : syracuseStep 3986657 = 2989993) B2989993
theorem B13359275 : Blo 487790 13359275 := bstep (se 1 (by rfl) ⟨10019456, by rfl⟩ : syracuseStep 13359275 = 20038913) B20038913
theorem B1235371 : Blo 487790 1235371 := bstep (se 1 (by rfl) ⟨926528, by rfl⟩ : syracuseStep 1235371 = 1853057) B1853057
theorem B1235695 : Blo 487790 1235695 := bstep (se 1 (by rfl) ⟨926771, by rfl⟩ : syracuseStep 1235695 = 1853543) B1853543
theorem B13458251 : Blo 487790 13458251 := bstep (se 1 (by rfl) ⟨10093688, by rfl⟩ : syracuseStep 13458251 = 20187377) B20187377
theorem B2087801 : Blo 487790 2087801 := bstep (se 2 (by rfl) ⟨782925, by rfl⟩ : syracuseStep 2087801 = 1565851) B1565851
theorem B50879771 : Blo 487790 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B4185371 : Blo 487790 4185371 := bstep (se 1 (by rfl) ⟨3139028, by rfl⟩ : syracuseStep 4185371 = 6278057) B6278057
theorem B1105577 : Blo 487790 1105577 := bstep (se 2 (by rfl) ⟨414591, by rfl⟩ : syracuseStep 1105577 = 829183) B829183
theorem B1106027 : Blo 487790 1106027 := bstep (se 1 (by rfl) ⟨829520, by rfl⟩ : syracuseStep 1106027 = 1659041) B1659041
theorem B7921793 : Blo 487790 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B1861487 : Blo 487790 1861487 := bstep (se 1 (by rfl) ⟨1396115, by rfl⟩ : syracuseStep 1861487 = 2792231) B2792231
theorem B2747105 : Blo 487790 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B879329 : Blo 487790 879329 := bstep (se 2 (by rfl) ⟨329748, by rfl⟩ : syracuseStep 879329 = 659497) B659497
theorem B11889611 : Blo 487790 11889611 := bstep (se 1 (by rfl) ⟨8917208, by rfl⟩ : syracuseStep 11889611 = 17834417) B17834417
theorem B1240231 : Blo 487790 1240231 := bstep (se 1 (by rfl) ⟨930173, by rfl⟩ : syracuseStep 1240231 = 1860347) B1860347
theorem B1568747 : Blo 487790 1568747 := bstep (se 1 (by rfl) ⟨1176560, by rfl⟩ : syracuseStep 1568747 = 2353121) B2353121
theorem B618779 : Blo 487790 618779 := bstep (se 1 (by rfl) ⟨464084, by rfl⟩ : syracuseStep 618779 = 928169) B928169
theorem B4518287 : Blo 487790 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B3273119 : Blo 487790 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B487871 : Blo 487790 487871 := bstep (se 1 (by rfl) ⟨365903, by rfl⟩ : syracuseStep 487871 = 731807) B731807
theorem B57308057 : Blo 487790 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B4257305 : Blo 487790 4257305 := bstep (se 2 (by rfl) ⟨1596489, by rfl⟩ : syracuseStep 4257305 = 3192979) B3192979
theorem B488991 : Blo 487790 488991 := bstep (se 1 (by rfl) ⟨366743, by rfl⟩ : syracuseStep 488991 = 733487) B733487
theorem B489007 : Blo 487790 489007 := bstep (se 1 (by rfl) ⟨366755, by rfl⟩ : syracuseStep 489007 = 733511) B733511
theorem B3536713 : Blo 487790 3536713 := bstep (se 2 (by rfl) ⟨1326267, by rfl⟩ : syracuseStep 3536713 = 2652535) B2652535
theorem B489503 : Blo 487790 489503 := bstep (se 1 (by rfl) ⟨367127, by rfl⟩ : syracuseStep 489503 = 734255) B734255
theorem B489575 : Blo 487790 489575 := bstep (se 1 (by rfl) ⟨367181, by rfl⟩ : syracuseStep 489575 = 734363) B734363
theorem B1243471 : Blo 487790 1243471 := bstep (se 1 (by rfl) ⟨932603, by rfl⟩ : syracuseStep 1243471 = 1865207) B1865207
theorem B621103 : Blo 487790 621103 := bstep (se 1 (by rfl) ⟨465827, by rfl⟩ : syracuseStep 621103 = 931655) B931655
theorem B490095 : Blo 487790 490095 := bstep (se 1 (by rfl) ⟨367571, by rfl⟩ : syracuseStep 490095 = 735143) B735143
theorem B2095865 : Blo 487790 2095865 := bstep (se 2 (by rfl) ⟨785949, by rfl⟩ : syracuseStep 2095865 = 1571899) B1571899
theorem B490239 : Blo 487790 490239 := bstep (se 1 (by rfl) ⟨367679, by rfl⟩ : syracuseStep 490239 = 735359) B735359
theorem B491007 : Blo 487790 491007 := bstep (se 1 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 491007 = 736511) B736511
theorem B491135 : Blo 487790 491135 := bstep (se 1 (by rfl) ⟨368351, by rfl⟩ : syracuseStep 491135 = 736703) B736703
theorem B3539483 : Blo 487790 3539483 := bstep (se 1 (by rfl) ⟨2654612, by rfl⟩ : syracuseStep 3539483 = 5309225) B5309225
theorem B2098001 : Blo 487790 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B2982743 : Blo 487790 2982743 := bstep (se 1 (by rfl) ⟨2237057, by rfl⟩ : syracuseStep 2982743 = 4474115) B4474115
theorem B1181135 : Blo 487790 1181135 := bstep (se 1 (by rfl) ⟨885851, by rfl⟩ : syracuseStep 1181135 = 1771703) B1771703
theorem B40306409 : Blo 487790 40306409 := bstep (se 2 (by rfl) ⟨15114903, by rfl⟩ : syracuseStep 40306409 = 30229807) B30229807
theorem B5572475 : Blo 487790 5572475 := bstep (se 1 (by rfl) ⟨4179356, by rfl⟩ : syracuseStep 5572475 = 8358713) B8358713
theorem B1674209 : Blo 487790 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B4689323 : Blo 487790 4689323 := bstep (se 1 (by rfl) ⟨3516992, by rfl⟩ : syracuseStep 4689323 = 7033985) B7033985
theorem B2657771 : Blo 487790 2657771 := bstep (se 1 (by rfl) ⟨1993328, by rfl⟩ : syracuseStep 2657771 = 3986657) B3986657
theorem B33919847 : Blo 487790 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B2790247 : Blo 487790 2790247 := bstep (se 1 (by rfl) ⟨2092685, by rfl⟩ : syracuseStep 2790247 = 4185371) B4185371
theorem B5281195 : Blo 487790 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B10556855 : Blo 487790 10556855 := bstep (se 1 (by rfl) ⟨7917641, by rfl⟩ : syracuseStep 10556855 = 15835283) B15835283
theorem B5969963 : Blo 487790 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B2693459 : Blo 487790 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B1647161 : Blo 487790 1647161 := bstep (se 2 (by rfl) ⟨617685, by rfl⟩ : syracuseStep 1647161 = 1235371) B1235371
theorem B828137 : Blo 487790 828137 := bstep (se 2 (by rfl) ⟨310551, by rfl⟩ : syracuseStep 828137 = 621103) B621103
theorem B1647593 : Blo 487790 1647593 := bstep (se 2 (by rfl) ⟨617847, by rfl⟩ : syracuseStep 1647593 = 1235695) B1235695
theorem B3778973 : Blo 487790 3778973 := bstep (se 3 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 3778973 = 1417115) B1417115
theorem B5975021 : Blo 487790 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B1322303 : Blo 487790 1322303 := bstep (se 1 (by rfl) ⟨991727, by rfl⟩ : syracuseStep 1322303 = 1983455) B1983455
theorem B1650077 : Blo 487790 1650077 := bstep (se 3 (by rfl) ⟨309389, by rfl⟩ : syracuseStep 1650077 = 618779) B618779
theorem B503743 : Blo 487790 503743 := bstep (se 1 (by rfl) ⟨377807, by rfl⟩ : syracuseStep 503743 = 755615) B755615
theorem B1650779 : Blo 487790 1650779 := bstep (se 1 (by rfl) ⟨1238084, by rfl⟩ : syracuseStep 1650779 = 2476169) B2476169
theorem B733727 : Blo 487790 733727 := bstep (se 1 (by rfl) ⟨550295, by rfl⟩ : syracuseStep 733727 = 1100591) B1100591
theorem B733979 : Blo 487790 733979 := bstep (se 1 (by rfl) ⟨550484, by rfl⟩ : syracuseStep 733979 = 1100969) B1100969
theorem B22688599 : Blo 487790 22688599 := bstep (se 1 (by rfl) ⟨17016449, by rfl⟩ : syracuseStep 22688599 = 34032899) B34032899
theorem B5944175 : Blo 487790 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B734375 : Blo 487790 734375 := bstep (se 1 (by rfl) ⟨550781, by rfl⟩ : syracuseStep 734375 = 1101563) B1101563
theorem B734399 : Blo 487790 734399 := bstep (se 1 (by rfl) ⟨550799, by rfl⟩ : syracuseStep 734399 = 1101599) B1101599
theorem B4176623 : Blo 487790 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B1653641 : Blo 487790 1653641 := bstep (se 2 (by rfl) ⟨620115, by rfl⟩ : syracuseStep 1653641 = 1240231) B1240231
theorem B1391867 : Blo 487790 1391867 := bstep (se 1 (by rfl) ⟨1043900, by rfl⟩ : syracuseStep 1391867 = 2087801) B2087801
theorem B31702751 : Blo 487790 31702751 := bstep (se 1 (by rfl) ⟨23777063, by rfl⟩ : syracuseStep 31702751 = 47554127) B47554127
theorem B737051 : Blo 487790 737051 := bstep (se 1 (by rfl) ⟨552788, by rfl⟩ : syracuseStep 737051 = 1105577) B1105577
theorem B737351 : Blo 487790 737351 := bstep (se 1 (by rfl) ⟨553013, by rfl⟩ : syracuseStep 737351 = 1106027) B1106027
theorem B8962235 : Blo 487790 8962235 := bstep (se 1 (by rfl) ⟨6721676, by rfl⟩ : syracuseStep 8962235 = 13443353) B13443353
theorem B2474873 : Blo 487790 2474873 := bstep (se 2 (by rfl) ⟨928077, by rfl⟩ : syracuseStep 2474873 = 1856155) B1856155
theorem B2475197 : Blo 487790 2475197 := bstep (se 3 (by rfl) ⟨464099, by rfl⟩ : syracuseStep 2475197 = 928199) B928199
theorem B1099817 : Blo 487790 1099817 := bstep (se 2 (by rfl) ⟨412431, by rfl⟩ : syracuseStep 1099817 = 824863) B824863
theorem B2182079 : Blo 487790 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B1657961 : Blo 487790 1657961 := bstep (se 2 (by rfl) ⟨621735, by rfl⟩ : syracuseStep 1657961 = 1243471) B1243471
theorem B839335 : Blo 487790 839335 := bstep (se 1 (by rfl) ⟨629501, by rfl⟩ : syracuseStep 839335 = 1259003) B1259003
theorem B2838203 : Blo 487790 2838203 := bstep (se 1 (by rfl) ⟨2128652, by rfl⟩ : syracuseStep 2838203 = 4257305) B4257305
theorem B3592457 : Blo 487790 3592457 := bstep (se 2 (by rfl) ⟨1347171, by rfl⟩ : syracuseStep 3592457 = 2694343) B2694343
theorem B1692143 : Blo 487790 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B1397243 : Blo 487790 1397243 := bstep (se 1 (by rfl) ⟨1047932, by rfl⟩ : syracuseStep 1397243 = 2095865) B2095865
theorem B1102931 : Blo 487790 1102931 := bstep (se 1 (by rfl) ⟨827198, by rfl⟩ : syracuseStep 1102931 = 1654397) B1654397
theorem B1104191 : Blo 487790 1104191 := bstep (se 1 (by rfl) ⟨828143, by rfl⟩ : syracuseStep 1104191 = 1656287) B1656287
theorem B2350775 : Blo 487790 2350775 := bstep (se 1 (by rfl) ⟨1763081, by rfl⟩ : syracuseStep 2350775 = 3526163) B3526163
theorem B549031 : Blo 487790 549031 := bstep (se 1 (by rfl) ⟨411773, by rfl⟩ : syracuseStep 549031 = 823547) B823547
theorem B1074313 : Blo 487790 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B8906183 : Blo 487790 8906183 := bstep (se 1 (by rfl) ⟨6679637, by rfl⟩ : syracuseStep 8906183 = 13359275) B13359275
theorem B8972167 : Blo 487790 8972167 := bstep (se 1 (by rfl) ⟨6729125, by rfl⟩ : syracuseStep 8972167 = 13458251) B13458251
theorem B550975 : Blo 487790 550975 := bstep (se 1 (by rfl) ⟨413231, by rfl⟩ : syracuseStep 550975 = 826463) B826463
theorem B7956701 : Blo 487790 7956701 := bstep (se 3 (by rfl) ⟨1491881, by rfl⟩ : syracuseStep 7956701 = 2983763) B2983763
theorem B552703 : Blo 487790 552703 := bstep (se 1 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 552703 = 829055) B829055
theorem B1240991 : Blo 487790 1240991 := bstep (se 1 (by rfl) ⟨930743, by rfl⟩ : syracuseStep 1240991 = 1861487) B1861487
theorem B1831403 : Blo 487790 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B586219 : Blo 487790 586219 := bstep (se 1 (by rfl) ⟨439664, by rfl⟩ : syracuseStep 586219 = 879329) B879329
theorem B7926407 : Blo 487790 7926407 := bstep (se 1 (by rfl) ⟨5944805, by rfl⟩ : syracuseStep 7926407 = 11889611) B11889611
theorem B488295 : Blo 487790 488295 := bstep (se 1 (by rfl) ⟨366221, by rfl⟩ : syracuseStep 488295 = 732443) B732443
theorem B488539 : Blo 487790 488539 := bstep (se 1 (by rfl) ⟨366404, by rfl⟩ : syracuseStep 488539 = 732809) B732809
theorem B4715617 : Blo 487790 4715617 := bstep (se 2 (by rfl) ⟨1768356, by rfl⟩ : syracuseStep 4715617 = 3536713) B3536713
theorem B1045831 : Blo 487790 1045831 := bstep (se 1 (by rfl) ⟨784373, by rfl⟩ : syracuseStep 1045831 = 1568747) B1568747
theorem B3012191 : Blo 487790 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B39221111 : Blo 487790 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B38205371 : Blo 487790 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B490031 : Blo 487790 490031 := bstep (se 1 (by rfl) ⟨367523, by rfl⟩ : syracuseStep 490031 = 735047) B735047
theorem B490151 : Blo 487790 490151 := bstep (se 1 (by rfl) ⟨367613, by rfl⟩ : syracuseStep 490151 = 735227) B735227
theorem B490235 : Blo 487790 490235 := bstep (se 1 (by rfl) ⟨367676, by rfl⟩ : syracuseStep 490235 = 735353) B735353
theorem B22903631 : Blo 487790 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B491111 : Blo 487790 491111 := bstep (se 1 (by rfl) ⟨368333, by rfl⟩ : syracuseStep 491111 = 736667) B736667
theorem B491567 : Blo 487790 491567 := bstep (se 1 (by rfl) ⟨368675, by rfl⟩ : syracuseStep 491567 = 737351) B737351
theorem B2359655 : Blo 487790 2359655 := bstep (se 1 (by rfl) ⟨1769741, by rfl⟩ : syracuseStep 2359655 = 3539483) B3539483
theorem B787423 : Blo 487790 787423 := bstep (se 1 (by rfl) ⟨590567, by rfl⟩ : syracuseStep 787423 = 1181135) B1181135
theorem B26870939 : Blo 487790 26870939 := bstep (se 1 (by rfl) ⟨20153204, by rfl⟩ : syracuseStep 26870939 = 40306409) B40306409
theorem B1771847 : Blo 487790 1771847 := bstep (se 1 (by rfl) ⟨1328885, by rfl⟩ : syracuseStep 1771847 = 2657771) B2657771
theorem B11962889 : Blo 487790 11962889 := bstep (se 2 (by rfl) ⟨4486083, by rfl⟩ : syracuseStep 11962889 = 8972167) B8972167
theorem B2394971 : Blo 487790 2394971 := bstep (se 1 (by rfl) ⟨1796228, by rfl⟩ : syracuseStep 2394971 = 3592457) B3592457
theorem B22613231 : Blo 487790 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B1119113 : Blo 487790 1119113 := bstep (se 2 (by rfl) ⟨419667, by rfl⟩ : syracuseStep 1119113 = 839335) B839335
theorem B7182557 : Blo 487790 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B5937455 : Blo 487790 5937455 := bstep (se 1 (by rfl) ⟨4453091, by rfl⟩ : syracuseStep 5937455 = 8906183) B8906183
theorem B30251465 : Blo 487790 30251465 := bstep (se 2 (by rfl) ⟨11344299, by rfl⟩ : syracuseStep 30251465 = 22688599) B22688599
theorem B4464557 : Blo 487790 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B827327 : Blo 487790 827327 := bstep (se 1 (by rfl) ⟨620495, by rfl⟩ : syracuseStep 827327 = 1240991) B1240991
theorem B1220935 : Blo 487790 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B5284271 : Blo 487790 5284271 := bstep (se 1 (by rfl) ⟨3963203, by rfl⟩ : syracuseStep 5284271 = 7926407) B7926407
theorem B2008127 : Blo 487790 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B25470247 : Blo 487790 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B927911 : Blo 487790 927911 := bstep (se 1 (by rfl) ⟨695933, by rfl⟩ : syracuseStep 927911 = 1391867) B1391867
theorem B5974823 : Blo 487790 5974823 := bstep (se 1 (by rfl) ⟨4481117, by rfl⟩ : syracuseStep 5974823 = 8962235) B8962235
theorem B732041 : Blo 487790 732041 := bstep (se 2 (by rfl) ⟨274515, by rfl⟩ : syracuseStep 732041 = 549031) B549031
theorem B1649915 : Blo 487790 1649915 := bstep (se 1 (by rfl) ⟨1237436, by rfl⟩ : syracuseStep 1649915 = 2474873) B2474873
theorem B1650131 : Blo 487790 1650131 := bstep (se 1 (by rfl) ⟨1237598, by rfl⟩ : syracuseStep 1650131 = 2475197) B2475197
theorem B3714983 : Blo 487790 3714983 := bstep (se 1 (by rfl) ⟨2786237, by rfl⟩ : syracuseStep 3714983 = 5572475) B5572475
theorem B733211 : Blo 487790 733211 := bstep (se 1 (by rfl) ⟨549908, by rfl⟩ : syracuseStep 733211 = 1099817) B1099817
theorem B3126215 : Blo 487790 3126215 := bstep (se 1 (by rfl) ⟨2344661, by rfl⟩ : syracuseStep 3126215 = 4689323) B4689323
theorem B734633 : Blo 487790 734633 := bstep (se 2 (by rfl) ⟨275487, by rfl⟩ : syracuseStep 734633 = 550975) B550975
theorem B1128095 : Blo 487790 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B931495 : Blo 487790 931495 := bstep (se 1 (by rfl) ⟨698621, by rfl⟩ : syracuseStep 931495 = 1397243) B1397243
theorem B735287 : Blo 487790 735287 := bstep (se 1 (by rfl) ⟨551465, by rfl⟩ : syracuseStep 735287 = 1102931) B1102931
theorem B3979975 : Blo 487790 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B736127 : Blo 487790 736127 := bstep (se 1 (by rfl) ⟨552095, by rfl⟩ : syracuseStep 736127 = 1104191) B1104191
theorem B736937 : Blo 487790 736937 := bstep (se 2 (by rfl) ⟨276351, by rfl⟩ : syracuseStep 736937 = 552703) B552703
theorem B671657 : Blo 487790 671657 := bstep (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) B503743
theorem B1098107 : Blo 487790 1098107 := bstep (se 1 (by rfl) ⟨823580, by rfl⟩ : syracuseStep 1098107 = 1647161) B1647161
theorem B1098395 : Blo 487790 1098395 := bstep (se 1 (by rfl) ⟨823796, by rfl⟩ : syracuseStep 1098395 = 1647593) B1647593
theorem B3720329 : Blo 487790 3720329 := bstep (se 2 (by rfl) ⟨1395123, by rfl⟩ : syracuseStep 3720329 = 2790247) B2790247
theorem B1394441 : Blo 487790 1394441 := bstep (se 2 (by rfl) ⟨522915, by rfl⟩ : syracuseStep 1394441 = 1045831) B1045831
theorem B3983347 : Blo 487790 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B1100051 : Blo 487790 1100051 := bstep (se 1 (by rfl) ⟨825038, by rfl⟩ : syracuseStep 1100051 = 1650077) B1650077
theorem B5818877 : Blo 487790 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B1100519 : Blo 487790 1100519 := bstep (se 1 (by rfl) ⟨825389, by rfl⟩ : syracuseStep 1100519 = 1650779) B1650779
theorem B3526141 : Blo 487790 3526141 := bstep (se 3 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 3526141 = 1322303) B1322303
theorem B1102427 : Blo 487790 1102427 := bstep (se 1 (by rfl) ⟨826820, by rfl⟩ : syracuseStep 1102427 = 1653641) B1653641
theorem B1398667 : Blo 487790 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B1988495 : Blo 487790 1988495 := bstep (se 1 (by rfl) ⟨1491371, by rfl⟩ : syracuseStep 1988495 = 2982743) B2982743
theorem B1432417 : Blo 487790 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B1105307 : Blo 487790 1105307 := bstep (se 1 (by rfl) ⟨828980, by rfl⟩ : syracuseStep 1105307 = 1657961) B1657961
theorem B1892135 : Blo 487790 1892135 := bstep (se 1 (by rfl) ⟨1419101, by rfl⟩ : syracuseStep 1892135 = 2838203) B2838203
theorem B7037903 : Blo 487790 7037903 := bstep (se 1 (by rfl) ⟨5278427, by rfl⟩ : syracuseStep 7037903 = 10556855) B10556855
theorem B1567183 : Blo 487790 1567183 := bstep (se 1 (by rfl) ⟨1175387, by rfl⟩ : syracuseStep 1567183 = 2350775) B2350775
theorem B552091 : Blo 487790 552091 := bstep (se 1 (by rfl) ⟨414068, by rfl⟩ : syracuseStep 552091 = 828137) B828137
theorem B781625 : Blo 487790 781625 := bstep (se 2 (by rfl) ⟨293109, by rfl⟩ : syracuseStep 781625 = 586219) B586219
theorem B6287489 : Blo 487790 6287489 := bstep (se 2 (by rfl) ⟨2357808, by rfl⟩ : syracuseStep 6287489 = 4715617) B4715617
theorem B5304467 : Blo 487790 5304467 := bstep (se 1 (by rfl) ⟨3978350, by rfl⟩ : syracuseStep 5304467 = 7956701) B7956701
theorem B2519315 : Blo 487790 2519315 := bstep (se 1 (by rfl) ⟨1889486, by rfl⟩ : syracuseStep 2519315 = 3778973) B3778973
theorem B7041593 : Blo 487790 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B489151 : Blo 487790 489151 := bstep (se 1 (by rfl) ⟨366863, by rfl⟩ : syracuseStep 489151 = 733727) B733727
theorem B489319 : Blo 487790 489319 := bstep (se 1 (by rfl) ⟨366989, by rfl⟩ : syracuseStep 489319 = 733979) B733979
theorem B3962783 : Blo 487790 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B489583 : Blo 487790 489583 := bstep (se 1 (by rfl) ⟨367187, by rfl⟩ : syracuseStep 489583 = 734375) B734375
theorem B489599 : Blo 487790 489599 := bstep (se 1 (by rfl) ⟨367199, by rfl⟩ : syracuseStep 489599 = 734399) B734399
theorem B26147407 : Blo 487790 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B2784415 : Blo 487790 2784415 := bstep (se 1 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 2784415 = 4176623) B4176623
theorem B15269087 : Blo 487790 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B21135167 : Blo 487790 21135167 := bstep (se 1 (by rfl) ⟨15851375, by rfl⟩ : syracuseStep 21135167 = 31702751) B31702751
theorem B491367 : Blo 487790 491367 := bstep (se 1 (by rfl) ⟨368525, by rfl⟩ : syracuseStep 491367 = 737051) B737051
theorem B1573103 : Blo 487790 1573103 := bstep (se 1 (by rfl) ⟨1179827, by rfl⟩ : syracuseStep 1573103 = 2359655) B2359655
theorem B1049897 : Blo 487790 1049897 := bstep (se 2 (by rfl) ⟨393711, by rfl⟩ : syracuseStep 1049897 = 787423) B787423
theorem B18777581 : Blo 487790 18777581 := bstep (se 3 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 18777581 = 7041593) B7041593
theorem B1181231 : Blo 487790 1181231 := bstep (se 1 (by rfl) ⟨885923, by rfl⟩ : syracuseStep 1181231 = 1771847) B1771847
theorem B15075487 : Blo 487790 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B5311129 : Blo 487790 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B4788371 : Blo 487790 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B4691935 : Blo 487790 4691935 := bstep (se 1 (by rfl) ⟨3518951, by rfl⟩ : syracuseStep 4691935 = 7037903) B7037903
theorem B1679543 : Blo 487790 1679543 := bstep (se 1 (by rfl) ⟨1259657, by rfl⟩ : syracuseStep 1679543 = 2519315) B2519315
theorem B1909889 : Blo 487790 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B3712553 : Blo 487790 3712553 := bstep (se 2 (by rfl) ⟨1392207, by rfl⟩ : syracuseStep 3712553 = 2784415) B2784415
theorem B732071 : Blo 487790 732071 := bstep (se 1 (by rfl) ⟨549053, by rfl⟩ : syracuseStep 732071 = 1098107) B1098107
theorem B732263 : Blo 487790 732263 := bstep (se 1 (by rfl) ⟨549197, by rfl⟩ : syracuseStep 732263 = 1098395) B1098395
theorem B929627 : Blo 487790 929627 := bstep (se 1 (by rfl) ⟨697220, by rfl⟩ : syracuseStep 929627 = 1394441) B1394441
theorem B733367 : Blo 487790 733367 := bstep (se 1 (by rfl) ⟨550025, by rfl⟩ : syracuseStep 733367 = 1100051) B1100051
theorem B3879251 : Blo 487790 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B7975259 : Blo 487790 7975259 := bstep (se 1 (by rfl) ⟨5981444, by rfl⟩ : syracuseStep 7975259 = 11962889) B11962889
theorem B33960329 : Blo 487790 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B733679 : Blo 487790 733679 := bstep (se 1 (by rfl) ⟨550259, by rfl⟩ : syracuseStep 733679 = 1100519) B1100519
theorem B5355005 : Blo 487790 5355005 := bstep (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) B2008127
theorem B734951 : Blo 487790 734951 := bstep (se 1 (by rfl) ⟨551213, by rfl⟩ : syracuseStep 734951 = 1102427) B1102427
theorem B1325663 : Blo 487790 1325663 := bstep (se 1 (by rfl) ⟨994247, by rfl⟩ : syracuseStep 1325663 = 1988495) B1988495
theorem B736121 : Blo 487790 736121 := bstep (se 2 (by rfl) ⟨276045, by rfl⟩ : syracuseStep 736121 = 552091) B552091
theorem B20167643 : Blo 487790 20167643 := bstep (se 1 (by rfl) ⟨15125732, by rfl⟩ : syracuseStep 20167643 = 30251465) B30251465
theorem B4701521 : Blo 487790 4701521 := bstep (se 2 (by rfl) ⟨1763070, by rfl⟩ : syracuseStep 4701521 = 3526141) B3526141
theorem B736871 : Blo 487790 736871 := bstep (se 1 (by rfl) ⟨552653, by rfl⟩ : syracuseStep 736871 = 1105307) B1105307
theorem B1261423 : Blo 487790 1261423 := bstep (se 1 (by rfl) ⟨946067, by rfl⟩ : syracuseStep 1261423 = 1892135) B1892135
theorem B3522847 : Blo 487790 3522847 := bstep (se 1 (by rfl) ⟨2642135, by rfl⟩ : syracuseStep 3522847 = 5284271) B5284271
theorem B3983215 : Blo 487790 3983215 := bstep (se 1 (by rfl) ⟨2987411, by rfl⟩ : syracuseStep 3983215 = 5974823) B5974823
theorem B1099943 : Blo 487790 1099943 := bstep (se 1 (by rfl) ⟨824957, by rfl⟩ : syracuseStep 1099943 = 1649915) B1649915
theorem B1100087 : Blo 487790 1100087 := bstep (se 1 (by rfl) ⟨825065, by rfl⟩ : syracuseStep 1100087 = 1650131) B1650131
theorem B2476655 : Blo 487790 2476655 := bstep (se 1 (by rfl) ⟨1857491, by rfl⟩ : syracuseStep 2476655 = 3714983) B3714983
theorem B40717565 : Blo 487790 40717565 := bstep (se 3 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 40717565 = 15269087) B15269087
theorem B2084143 : Blo 487790 2084143 := bstep (se 1 (by rfl) ⟨1563107, by rfl⟩ : syracuseStep 2084143 = 3126215) B3126215
theorem B2641855 : Blo 487790 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B1791085 : Blo 487790 1791085 := bstep (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) B671657
theorem B1627913 : Blo 487790 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B2480219 : Blo 487790 2480219 := bstep (se 1 (by rfl) ⟨1860164, by rfl⟩ : syracuseStep 2480219 = 3720329) B3720329
theorem B17913959 : Blo 487790 17913959 := bstep (se 1 (by rfl) ⟨13435469, by rfl⟩ : syracuseStep 17913959 = 26870939) B26870939
theorem B1596647 : Blo 487790 1596647 := bstep (se 1 (by rfl) ⟨1197485, by rfl⟩ : syracuseStep 1596647 = 2394971) B2394971
theorem B746075 : Blo 487790 746075 := bstep (se 1 (by rfl) ⟨559556, by rfl⟩ : syracuseStep 746075 = 1119113) B1119113
theorem B2089577 : Blo 487790 2089577 := bstep (se 2 (by rfl) ⟨783591, by rfl⟩ : syracuseStep 2089577 = 1567183) B1567183
theorem B3958303 : Blo 487790 3958303 := bstep (se 1 (by rfl) ⟨2968727, by rfl⟩ : syracuseStep 3958303 = 5937455) B5937455
theorem B2976371 : Blo 487790 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B551551 : Blo 487790 551551 := bstep (se 1 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 551551 = 827327) B827327
theorem B618607 : Blo 487790 618607 := bstep (se 1 (by rfl) ⟨463955, by rfl⟩ : syracuseStep 618607 = 927911) B927911
theorem B488027 : Blo 487790 488027 := bstep (se 1 (by rfl) ⟨366020, by rfl⟩ : syracuseStep 488027 = 732041) B732041
theorem B521083 : Blo 487790 521083 := bstep (se 1 (by rfl) ⟨390812, by rfl⟩ : syracuseStep 521083 = 781625) B781625
theorem B1241993 : Blo 487790 1241993 := bstep (se 2 (by rfl) ⟨465747, by rfl⟩ : syracuseStep 1241993 = 931495) B931495
theorem B1864889 : Blo 487790 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B488807 : Blo 487790 488807 := bstep (se 1 (by rfl) ⟨366605, by rfl⟩ : syracuseStep 488807 = 733211) B733211
theorem B4191659 : Blo 487790 4191659 := bstep (se 1 (by rfl) ⟨3143744, by rfl⟩ : syracuseStep 4191659 = 6287489) B6287489
theorem B3536311 : Blo 487790 3536311 := bstep (se 1 (by rfl) ⟨2652233, by rfl⟩ : syracuseStep 3536311 = 5304467) B5304467
theorem B34863209 : Blo 487790 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B5306633 : Blo 487790 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B489755 : Blo 487790 489755 := bstep (se 1 (by rfl) ⟨367316, by rfl⟩ : syracuseStep 489755 = 734633) B734633
theorem B752063 : Blo 487790 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B490191 : Blo 487790 490191 := bstep (se 1 (by rfl) ⟨367643, by rfl⟩ : syracuseStep 490191 = 735287) B735287
theorem B490751 : Blo 487790 490751 := bstep (se 1 (by rfl) ⟨368063, by rfl⟩ : syracuseStep 490751 = 736127) B736127
theorem B491291 : Blo 487790 491291 := bstep (se 1 (by rfl) ⟨368468, by rfl⟩ : syracuseStep 491291 = 736937) B736937
theorem B14090111 : Blo 487790 14090111 := bstep (se 1 (by rfl) ⟨10567583, by rfl⟩ : syracuseStep 14090111 = 21135167) B21135167
theorem B1048735 : Blo 487790 1048735 := bstep (se 1 (by rfl) ⟨786551, by rfl⟩ : syracuseStep 1048735 = 1573103) B1573103
theorem B12518387 : Blo 487790 12518387 := bstep (se 1 (by rfl) ⟨9388790, by rfl⟩ : syracuseStep 12518387 = 18777581) B18777581
theorem B787487 : Blo 487790 787487 := bstep (se 1 (by rfl) ⟨590615, by rfl⟩ : syracuseStep 787487 = 1181231) B1181231
theorem B5277737 : Blo 487790 5277737 := bstep (se 2 (by rfl) ⟨1979151, by rfl⟩ : syracuseStep 5277737 = 3958303) B3958303
theorem B5310953 : Blo 487790 5310953 := bstep (se 2 (by rfl) ⟨1991607, by rfl⟩ : syracuseStep 5310953 = 3983215) B3983215
theorem B7081505 : Blo 487790 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B1085275 : Blo 487790 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B1119695 : Blo 487790 1119695 := bstep (se 1 (by rfl) ⟨839771, by rfl⟩ : syracuseStep 1119695 = 1679543) B1679543
theorem B824809 : Blo 487790 824809 := bstep (se 2 (by rfl) ⟨309303, by rfl⟩ : syracuseStep 824809 = 618607) B618607
theorem B497383 : Blo 487790 497383 := bstep (se 1 (by rfl) ⟨373037, by rfl⟩ : syracuseStep 497383 = 746075) B746075
theorem B2005501 : Blo 487790 2005501 := bstep (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) B752063
theorem B53780381 : Blo 487790 53780381 := bstep (se 3 (by rfl) ⟨10083821, by rfl⟩ : syracuseStep 53780381 = 20167643) B20167643
theorem B5316839 : Blo 487790 5316839 := bstep (se 1 (by rfl) ⟨3987629, by rfl⟩ : syracuseStep 5316839 = 7975259) B7975259
theorem B827995 : Blo 487790 827995 := bstep (se 1 (by rfl) ⟨620996, by rfl⟩ : syracuseStep 827995 = 1241993) B1241993
theorem B2794439 : Blo 487790 2794439 := bstep (se 1 (by rfl) ⟨2095829, by rfl⟩ : syracuseStep 2794439 = 4191659) B4191659
theorem B23242139 : Blo 487790 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B6727589 : Blo 487790 6727589 := bstep (se 4 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 6727589 = 1261423) B1261423
theorem B4697129 : Blo 487790 4697129 := bstep (se 2 (by rfl) ⟨1761423, by rfl⟩ : syracuseStep 4697129 = 3522847) B3522847
theorem B699931 : Blo 487790 699931 := bstep (se 1 (by rfl) ⟨524948, by rfl⟩ : syracuseStep 699931 = 1049897) B1049897
theorem B733295 : Blo 487790 733295 := bstep (se 1 (by rfl) ⟨549971, by rfl⟩ : syracuseStep 733295 = 1099943) B1099943
theorem B733391 : Blo 487790 733391 := bstep (se 1 (by rfl) ⟨550043, by rfl⟩ : syracuseStep 733391 = 1100087) B1100087
theorem B1651103 : Blo 487790 1651103 := bstep (se 1 (by rfl) ⟨1238327, by rfl⟩ : syracuseStep 1651103 = 2476655) B2476655
theorem B27145043 : Blo 487790 27145043 := bstep (se 1 (by rfl) ⟨20358782, by rfl⟩ : syracuseStep 27145043 = 40717565) B40717565
theorem B3192247 : Blo 487790 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B20100649 : Blo 487790 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B735401 : Blo 487790 735401 := bstep (se 2 (by rfl) ⟨275775, by rfl⟩ : syracuseStep 735401 = 551551) B551551
theorem B1653479 : Blo 487790 1653479 := bstep (se 1 (by rfl) ⟨1240109, by rfl⟩ : syracuseStep 1653479 = 2480219) B2480219
theorem B11942639 : Blo 487790 11942639 := bstep (se 1 (by rfl) ⟨8956979, by rfl⟩ : syracuseStep 11942639 = 17913959) B17913959
theorem B1064431 : Blo 487790 1064431 := bstep (se 1 (by rfl) ⟨798323, by rfl⟩ : syracuseStep 1064431 = 1596647) B1596647
theorem B3522473 : Blo 487790 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B1393051 : Blo 487790 1393051 := bstep (se 1 (by rfl) ⟨1044788, by rfl⟩ : syracuseStep 1393051 = 2089577) B2089577
theorem B2475035 : Blo 487790 2475035 := bstep (se 1 (by rfl) ⟨1856276, by rfl⟩ : syracuseStep 2475035 = 3712553) B3712553
theorem B1984247 : Blo 487790 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B12537389 : Blo 487790 12537389 := bstep (se 3 (by rfl) ⟨2350760, by rfl⟩ : syracuseStep 12537389 = 4701521) B4701521
theorem B9393407 : Blo 487790 9393407 := bstep (se 1 (by rfl) ⟨7045055, by rfl⟩ : syracuseStep 9393407 = 14090111) B14090111
theorem B14280013 : Blo 487790 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B2778857 : Blo 487790 2778857 := bstep (se 2 (by rfl) ⟨1042071, by rfl⟩ : syracuseStep 2778857 = 2084143) B2084143
theorem B2779109 : Blo 487790 2779109 := bstep (se 4 (by rfl) ⟨260541, by rfl⟩ : syracuseStep 2779109 = 521083) B521083
theorem B1273259 : Blo 487790 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B2388113 : Blo 487790 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B4715081 : Blo 487790 4715081 := bstep (se 2 (by rfl) ⟨1768155, by rfl⟩ : syracuseStep 4715081 = 3536311) B3536311
theorem B488047 : Blo 487790 488047 := bstep (se 1 (by rfl) ⟨366035, by rfl⟩ : syracuseStep 488047 = 732071) B732071
theorem B488175 : Blo 487790 488175 := bstep (se 1 (by rfl) ⟨366131, by rfl⟩ : syracuseStep 488175 = 732263) B732263
theorem B619751 : Blo 487790 619751 := bstep (se 1 (by rfl) ⟨464813, by rfl⟩ : syracuseStep 619751 = 929627) B929627
theorem B6255913 : Blo 487790 6255913 := bstep (se 2 (by rfl) ⟨2345967, by rfl⟩ : syracuseStep 6255913 = 4691935) B4691935
theorem B488911 : Blo 487790 488911 := bstep (se 1 (by rfl) ⟨366683, by rfl⟩ : syracuseStep 488911 = 733367) B733367
theorem B2586167 : Blo 487790 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B22640219 : Blo 487790 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B489119 : Blo 487790 489119 := bstep (se 1 (by rfl) ⟨366839, by rfl⟩ : syracuseStep 489119 = 733679) B733679
theorem B1243259 : Blo 487790 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B489967 : Blo 487790 489967 := bstep (se 1 (by rfl) ⟨367475, by rfl⟩ : syracuseStep 489967 = 734951) B734951
theorem B3537755 : Blo 487790 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B883775 : Blo 487790 883775 := bstep (se 1 (by rfl) ⟨662831, by rfl⟩ : syracuseStep 883775 = 1325663) B1325663
theorem B490747 : Blo 487790 490747 := bstep (se 1 (by rfl) ⟨368060, by rfl⟩ : syracuseStep 490747 = 736121) B736121
theorem B491247 : Blo 487790 491247 := bstep (se 1 (by rfl) ⟨368435, by rfl⟩ : syracuseStep 491247 = 736871) B736871
theorem B3540635 : Blo 487790 3540635 := bstep (se 1 (by rfl) ⟨2655476, by rfl⟩ : syracuseStep 3540635 = 5310953) B5310953
theorem B19040017 : Blo 487790 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B4721003 : Blo 487790 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B2099965 : Blo 487790 2099965 := bstep (se 3 (by rfl) ⟨393743, by rfl⟩ : syracuseStep 2099965 = 787487) B787487
theorem B6262271 : Blo 487790 6262271 := bstep (se 1 (by rfl) ⟨4696703, by rfl⟩ : syracuseStep 6262271 = 9393407) B9393407
theorem B1447033 : Blo 487790 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B35853587 : Blo 487790 35853587 := bstep (se 1 (by rfl) ⟨26890190, by rfl⟩ : syracuseStep 35853587 = 53780381) B53780381
theorem B3544559 : Blo 487790 3544559 := bstep (se 1 (by rfl) ⟨2658419, by rfl⟩ : syracuseStep 3544559 = 5316839) B5316839
theorem B18096695 : Blo 487790 18096695 := bstep (se 1 (by rfl) ⟨13572521, by rfl⟩ : syracuseStep 18096695 = 27145043) B27145043
theorem B828839 : Blo 487790 828839 := bstep (se 1 (by rfl) ⟨621629, by rfl⟩ : syracuseStep 828839 = 1243259) B1243259
theorem B33433037 : Blo 487790 33433037 := bstep (se 3 (by rfl) ⟨6268694, by rfl⟩ : syracuseStep 33433037 = 12537389) B12537389
theorem B1419241 : Blo 487790 1419241 := bstep (se 2 (by rfl) ⟨532215, by rfl⟩ : syracuseStep 1419241 = 1064431) B1064431
theorem B1650023 : Blo 487790 1650023 := bstep (se 1 (by rfl) ⟨1237517, by rfl⟩ : syracuseStep 1650023 = 2475035) B2475035
theorem B1322831 : Blo 487790 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B3518491 : Blo 487790 3518491 := bstep (se 1 (by rfl) ⟨2638868, by rfl⟩ : syracuseStep 3518491 = 5277737) B5277737
theorem B1652669 : Blo 487790 1652669 := bstep (se 3 (by rfl) ⟨309875, by rfl⟩ : syracuseStep 1652669 = 619751) B619751
theorem B11943413 : Blo 487790 11943413 := bstep (se 5 (by rfl) ⟨559847, by rfl⟩ : syracuseStep 11943413 = 1119695) B1119695
theorem B1852571 : Blo 487790 1852571 := bstep (se 1 (by rfl) ⟨1389428, by rfl⟩ : syracuseStep 1852571 = 2778857) B2778857
theorem B1852739 : Blo 487790 1852739 := bstep (se 1 (by rfl) ⟨1389554, by rfl⟩ : syracuseStep 1852739 = 2779109) B2779109
theorem B8341217 : Blo 487790 8341217 := bstep (se 2 (by rfl) ⟨3127956, by rfl⟩ : syracuseStep 8341217 = 6255913) B6255913
theorem B1099745 : Blo 487790 1099745 := bstep (se 2 (by rfl) ⟨412404, by rfl⟩ : syracuseStep 1099745 = 824809) B824809
theorem B3131419 : Blo 487790 3131419 := bstep (se 1 (by rfl) ⟨2348564, by rfl⟩ : syracuseStep 3131419 = 4697129) B4697129
theorem B1592075 : Blo 487790 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B1100735 : Blo 487790 1100735 := bstep (se 1 (by rfl) ⟨825551, by rfl⟩ : syracuseStep 1100735 = 1651103) B1651103
theorem B2674001 : Blo 487790 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B1724111 : Blo 487790 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B15093479 : Blo 487790 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B1102319 : Blo 487790 1102319 := bstep (se 1 (by rfl) ⟨826739, by rfl⟩ : syracuseStep 1102319 = 1653479) B1653479
theorem B2348315 : Blo 487790 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B1398313 : Blo 487790 1398313 := bstep (se 2 (by rfl) ⟨524367, by rfl⟩ : syracuseStep 1398313 = 1048735) B1048735
theorem B1857401 : Blo 487790 1857401 := bstep (se 2 (by rfl) ⟨696525, by rfl⟩ : syracuseStep 1857401 = 1393051) B1393051
theorem B8345591 : Blo 487790 8345591 := bstep (se 1 (by rfl) ⟨6259193, by rfl⟩ : syracuseStep 8345591 = 12518387) B12518387
theorem B1103993 : Blo 487790 1103993 := bstep (se 2 (by rfl) ⟨413997, by rfl⟩ : syracuseStep 1103993 = 827995) B827995
theorem B1862959 : Blo 487790 1862959 := bstep (se 1 (by rfl) ⟨1397219, by rfl⟩ : syracuseStep 1862959 = 2794439) B2794439
theorem B15494759 : Blo 487790 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B4485059 : Blo 487790 4485059 := bstep (se 1 (by rfl) ⟨3363794, by rfl⟩ : syracuseStep 4485059 = 6727589) B6727589
theorem B4256329 : Blo 487790 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B26800865 : Blo 487790 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B848839 : Blo 487790 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B488863 : Blo 487790 488863 := bstep (se 1 (by rfl) ⟨366647, by rfl⟩ : syracuseStep 488863 = 733295) B733295
theorem B488927 : Blo 487790 488927 := bstep (se 1 (by rfl) ⟨366695, by rfl⟩ : syracuseStep 488927 = 733391) B733391
theorem B3732965 : Blo 487790 3732965 := bstep (se 4 (by rfl) ⟨349965, by rfl⟩ : syracuseStep 3732965 = 699931) B699931
theorem B3143387 : Blo 487790 3143387 := bstep (se 1 (by rfl) ⟨2357540, by rfl⟩ : syracuseStep 3143387 = 4715081) B4715081
theorem B2652709 : Blo 487790 2652709 := bstep (se 4 (by rfl) ⟨248691, by rfl⟩ : syracuseStep 2652709 = 497383) B497383
theorem B490267 : Blo 487790 490267 := bstep (se 1 (by rfl) ⟨367700, by rfl⟩ : syracuseStep 490267 = 735401) B735401
theorem B7961759 : Blo 487790 7961759 := bstep (se 1 (by rfl) ⟨5971319, by rfl⟩ : syracuseStep 7961759 = 11942639) B11942639
theorem B2358503 : Blo 487790 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B589183 : Blo 487790 589183 := bstep (se 1 (by rfl) ⟨441887, by rfl⟩ : syracuseStep 589183 = 883775) B883775
theorem B2360423 : Blo 487790 2360423 := bstep (se 1 (by rfl) ⟨1770317, by rfl⟩ : syracuseStep 2360423 = 3540635) B3540635
theorem B3147335 : Blo 487790 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B1149407 : Blo 487790 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B10062319 : Blo 487790 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B2363039 : Blo 487790 2363039 := bstep (se 1 (by rfl) ⟨1772279, by rfl⟩ : syracuseStep 2363039 = 3544559) B3544559
theorem B4691321 : Blo 487790 4691321 := bstep (se 2 (by rfl) ⟨1759245, by rfl⟩ : syracuseStep 4691321 = 3518491) B3518491
theorem B12064463 : Blo 487790 12064463 := bstep (se 1 (by rfl) ⟨9048347, by rfl⟩ : syracuseStep 12064463 = 18096695) B18096695
theorem B5675105 : Blo 487790 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B22288691 : Blo 487790 22288691 := bstep (se 1 (by rfl) ⟨16716518, by rfl⟩ : syracuseStep 22288691 = 33433037) B33433037
theorem B10329839 : Blo 487790 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B2990039 : Blo 487790 2990039 := bstep (se 1 (by rfl) ⟨2242529, by rfl⟩ : syracuseStep 2990039 = 4485059) B4485059
theorem B17867243 : Blo 487790 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B733163 : Blo 487790 733163 := bstep (se 1 (by rfl) ⟨549872, by rfl⟩ : syracuseStep 733163 = 1099745) B1099745
theorem B733823 : Blo 487790 733823 := bstep (se 1 (by rfl) ⟨550367, by rfl⟩ : syracuseStep 733823 = 1100735) B1100735
theorem B1782667 : Blo 487790 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B4174847 : Blo 487790 4174847 := bstep (se 1 (by rfl) ⟨3131135, by rfl⟩ : syracuseStep 4174847 = 6262271) B6262271
theorem B4175225 : Blo 487790 4175225 := bstep (se 2 (by rfl) ⟨1565709, by rfl⟩ : syracuseStep 4175225 = 3131419) B3131419
theorem B734879 : Blo 487790 734879 := bstep (se 1 (by rfl) ⟨551159, by rfl⟩ : syracuseStep 734879 = 1102319) B1102319
theorem B23902391 : Blo 487790 23902391 := bstep (se 1 (by rfl) ⟨17926793, by rfl⟩ : syracuseStep 23902391 = 35853587) B35853587
theorem B2799953 : Blo 487790 2799953 := bstep (se 2 (by rfl) ⟨1049982, by rfl⟩ : syracuseStep 2799953 = 2099965) B2099965
theorem B735995 : Blo 487790 735995 := bstep (se 1 (by rfl) ⟨551996, by rfl⟩ : syracuseStep 735995 = 1103993) B1103993
theorem B1131785 : Blo 487790 1131785 := bstep (se 2 (by rfl) ⟨424419, by rfl⟩ : syracuseStep 1131785 = 848839) B848839
theorem B4245533 : Blo 487790 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B1100015 : Blo 487790 1100015 := bstep (se 1 (by rfl) ⟨825011, by rfl⟩ : syracuseStep 1100015 = 1650023) B1650023
theorem B1101779 : Blo 487790 1101779 := bstep (se 1 (by rfl) ⟨826334, by rfl⟩ : syracuseStep 1101779 = 1652669) B1652669
theorem B3527549 : Blo 487790 3527549 := bstep (se 3 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 3527549 = 1322831) B1322831
theorem B1235047 : Blo 487790 1235047 := bstep (se 1 (by rfl) ⟨926285, by rfl⟩ : syracuseStep 1235047 = 1852571) B1852571
theorem B1235159 : Blo 487790 1235159 := bstep (se 1 (by rfl) ⟨926369, by rfl⟩ : syracuseStep 1235159 = 1852739) B1852739
theorem B5560811 : Blo 487790 5560811 := bstep (se 1 (by rfl) ⟨4170608, by rfl⟩ : syracuseStep 5560811 = 8341217) B8341217
theorem B25386689 : Blo 487790 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B1892321 : Blo 487790 1892321 := bstep (se 2 (by rfl) ⟨709620, by rfl⟩ : syracuseStep 1892321 = 1419241) B1419241
theorem B1565543 : Blo 487790 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B1238267 : Blo 487790 1238267 := bstep (se 1 (by rfl) ⟨928700, by rfl⟩ : syracuseStep 1238267 = 1857401) B1857401
theorem B5563727 : Blo 487790 5563727 := bstep (se 1 (by rfl) ⟨4172795, by rfl⟩ : syracuseStep 5563727 = 8345591) B8345591
theorem B2483945 : Blo 487790 2483945 := bstep (se 2 (by rfl) ⟨931479, by rfl⟩ : syracuseStep 2483945 = 1862959) B1862959
theorem B552559 : Blo 487790 552559 := bstep (se 1 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 552559 = 828839) B828839
theorem B1929377 : Blo 487790 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B3142309 : Blo 487790 3142309 := bstep (se 4 (by rfl) ⟨294591, by rfl⟩ : syracuseStep 3142309 = 589183) B589183
theorem B1864417 : Blo 487790 1864417 := bstep (se 2 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 1864417 = 1398313) B1398313
theorem B3536945 : Blo 487790 3536945 := bstep (se 2 (by rfl) ⟨1326354, by rfl⟩ : syracuseStep 3536945 = 2652709) B2652709
theorem B2488643 : Blo 487790 2488643 := bstep (se 1 (by rfl) ⟨1866482, by rfl⟩ : syracuseStep 2488643 = 3732965) B3732965
theorem B2095591 : Blo 487790 2095591 := bstep (se 1 (by rfl) ⟨1571693, by rfl⟩ : syracuseStep 2095591 = 3143387) B3143387
theorem B5307839 : Blo 487790 5307839 := bstep (se 1 (by rfl) ⟨3980879, by rfl⟩ : syracuseStep 5307839 = 7961759) B7961759
theorem B1572335 : Blo 487790 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B7962275 : Blo 487790 7962275 := bstep (se 1 (by rfl) ⟨5971706, by rfl⟩ : syracuseStep 7962275 = 11943413) B11943413
theorem B5145005 : Blo 487790 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B1573615 : Blo 487790 1573615 := bstep (se 1 (by rfl) ⟨1180211, by rfl⟩ : syracuseStep 1573615 = 2360423) B2360423
theorem B754523 : Blo 487790 754523 := bstep (se 1 (by rfl) ⟨565892, by rfl⟩ : syracuseStep 754523 = 1131785) B1131785
theorem B2098223 : Blo 487790 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B47645981 : Blo 487790 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B1575359 : Blo 487790 1575359 := bstep (se 1 (by rfl) ⟨1181519, by rfl⟩ : syracuseStep 1575359 = 2363039) B2363039
theorem B823439 : Blo 487790 823439 := bstep (se 1 (by rfl) ⟨617579, by rfl⟩ : syracuseStep 823439 = 1235159) B1235159
theorem B3707207 : Blo 487790 3707207 := bstep (se 1 (by rfl) ⟨2780405, by rfl⟩ : syracuseStep 3707207 = 5560811) B5560811
theorem B9507557 : Blo 487790 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B6886559 : Blo 487790 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B825511 : Blo 487790 825511 := bstep (se 1 (by rfl) ⟨619133, by rfl⟩ : syracuseStep 825511 = 1238267) B1238267
theorem B3709151 : Blo 487790 3709151 := bstep (se 1 (by rfl) ⟨2781863, by rfl⟩ : syracuseStep 3709151 = 5563727) B5563727
theorem B1646729 : Blo 487790 1646729 := bstep (se 2 (by rfl) ⟨617523, by rfl⟩ : syracuseStep 1646729 = 1235047) B1235047
theorem B2794121 : Blo 487790 2794121 := bstep (se 2 (by rfl) ⟨1047795, by rfl⟩ : syracuseStep 2794121 = 2095591) B2095591
theorem B15934927 : Blo 487790 15934927 := bstep (se 1 (by rfl) ⟨11951195, by rfl⟩ : syracuseStep 15934927 = 23902391) B23902391
theorem B7973437 : Blo 487790 7973437 := bstep (se 3 (by rfl) ⟨1495019, by rfl⟩ : syracuseStep 7973437 = 2990039) B2990039
theorem B2830355 : Blo 487790 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B733343 : Blo 487790 733343 := bstep (se 1 (by rfl) ⟨550007, by rfl⟩ : syracuseStep 733343 = 1100015) B1100015
theorem B766271 : Blo 487790 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B734519 : Blo 487790 734519 := bstep (se 1 (by rfl) ⟨550889, by rfl⟩ : syracuseStep 734519 = 1101779) B1101779
theorem B13416425 : Blo 487790 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B3127547 : Blo 487790 3127547 := bstep (se 1 (by rfl) ⟨2345660, by rfl⟩ : syracuseStep 3127547 = 4691321) B4691321
theorem B8042975 : Blo 487790 8042975 := bstep (se 1 (by rfl) ⟨6032231, by rfl⟩ : syracuseStep 8042975 = 12064463) B12064463
theorem B736745 : Blo 487790 736745 := bstep (se 2 (by rfl) ⟨276279, by rfl⟩ : syracuseStep 736745 = 552559) B552559
theorem B16924459 : Blo 487790 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B1261547 : Blo 487790 1261547 := bstep (se 1 (by rfl) ⟨946160, by rfl⟩ : syracuseStep 1261547 = 1892321) B1892321
theorem B1655963 : Blo 487790 1655963 := bstep (se 1 (by rfl) ⟨1241972, by rfl⟩ : syracuseStep 1655963 = 2483945) B2483945
theorem B1659095 : Blo 487790 1659095 := bstep (se 1 (by rfl) ⟨1244321, by rfl⟩ : syracuseStep 1659095 = 2488643) B2488643
theorem B2351699 : Blo 487790 2351699 := bstep (se 1 (by rfl) ⟨1763774, by rfl⟩ : syracuseStep 2351699 = 3527549) B3527549
theorem B15133613 : Blo 487790 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B1043695 : Blo 487790 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B59436509 : Blo 487790 59436509 := bstep (se 3 (by rfl) ⟨11144345, by rfl⟩ : syracuseStep 59436509 = 22288691) B22288691
theorem B4189745 : Blo 487790 4189745 := bstep (se 2 (by rfl) ⟨1571154, by rfl⟩ : syracuseStep 4189745 = 3142309) B3142309
theorem B2485889 : Blo 487790 2485889 := bstep (se 2 (by rfl) ⟨932208, by rfl⟩ : syracuseStep 2485889 = 1864417) B1864417
theorem B488775 : Blo 487790 488775 := bstep (se 1 (by rfl) ⟨366581, by rfl⟩ : syracuseStep 488775 = 733163) B733163
theorem B489215 : Blo 487790 489215 := bstep (se 1 (by rfl) ⟨366911, by rfl⟩ : syracuseStep 489215 = 733823) B733823
theorem B2783231 : Blo 487790 2783231 := bstep (se 1 (by rfl) ⟨2087423, by rfl⟩ : syracuseStep 2783231 = 4174847) B4174847
theorem B2783483 : Blo 487790 2783483 := bstep (se 1 (by rfl) ⟨2087612, by rfl⟩ : syracuseStep 2783483 = 4175225) B4175225
theorem B489919 : Blo 487790 489919 := bstep (se 1 (by rfl) ⟨367439, by rfl⟩ : syracuseStep 489919 = 734879) B734879
theorem B2357963 : Blo 487790 2357963 := bstep (se 1 (by rfl) ⟨1768472, by rfl⟩ : syracuseStep 2357963 = 3536945) B3536945
theorem B1866635 : Blo 487790 1866635 := bstep (se 1 (by rfl) ⟨1399976, by rfl⟩ : syracuseStep 1866635 = 2799953) B2799953
theorem B490663 : Blo 487790 490663 := bstep (se 1 (by rfl) ⟨367997, by rfl⟩ : syracuseStep 490663 = 735995) B735995
theorem B3538559 : Blo 487790 3538559 := bstep (se 1 (by rfl) ⟨2653919, by rfl⟩ : syracuseStep 3538559 = 5307839) B5307839
theorem B1048223 : Blo 487790 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B5308183 : Blo 487790 5308183 := bstep (se 1 (by rfl) ⟨3981137, by rfl⟩ : syracuseStep 5308183 = 7962275) B7962275
theorem B2098153 : Blo 487790 2098153 := bstep (se 2 (by rfl) ⟨786807, by rfl⟩ : syracuseStep 2098153 = 1573615) B1573615
theorem B1050239 : Blo 487790 1050239 := bstep (se 1 (by rfl) ⟨787679, by rfl⟩ : syracuseStep 1050239 = 1575359) B1575359
theorem B2793163 : Blo 487790 2793163 := bstep (se 1 (by rfl) ⟨2094872, by rfl⟩ : syracuseStep 2793163 = 4189745) B4189745
theorem B698815 : Blo 487790 698815 := bstep (se 1 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 698815 = 1048223) B1048223
theorem B503015 : Blo 487790 503015 := bstep (se 1 (by rfl) ⟨377261, by rfl⟩ : syracuseStep 503015 = 754523) B754523
theorem B2043389 : Blo 487790 2043389 := bstep (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) B766271
theorem B31763987 : Blo 487790 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B21246569 : Blo 487790 21246569 := bstep (se 2 (by rfl) ⟨7967463, by rfl⟩ : syracuseStep 21246569 = 15934927) B15934927
theorem B2471471 : Blo 487790 2471471 := bstep (se 1 (by rfl) ⟨1853603, by rfl⟩ : syracuseStep 2471471 = 3707207) B3707207
theorem B18364157 : Blo 487790 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B6338371 : Blo 487790 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B10631249 : Blo 487790 10631249 := bstep (se 2 (by rfl) ⟨3986718, by rfl⟩ : syracuseStep 10631249 = 7973437) B7973437
theorem B2472767 : Blo 487790 2472767 := bstep (se 1 (by rfl) ⟨1854575, by rfl⟩ : syracuseStep 2472767 = 3709151) B3709151
theorem B1391593 : Blo 487790 1391593 := bstep (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) B1043695
theorem B1097819 : Blo 487790 1097819 := bstep (se 1 (by rfl) ⟨823364, by rfl⟩ : syracuseStep 1097819 = 1646729) B1646729
theorem B1657259 : Blo 487790 1657259 := bstep (se 1 (by rfl) ⟨1242944, by rfl⟩ : syracuseStep 1657259 = 2485889) B2485889
theorem B40356301 : Blo 487790 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B1886903 : Blo 487790 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B1100681 : Blo 487790 1100681 := bstep (se 2 (by rfl) ⟨412755, by rfl⟩ : syracuseStep 1100681 = 825511) B825511
theorem B1855487 : Blo 487790 1855487 := bstep (se 1 (by rfl) ⟨1391615, by rfl⟩ : syracuseStep 1855487 = 2783231) B2783231
theorem B2085031 : Blo 487790 2085031 := bstep (se 1 (by rfl) ⟨1563773, by rfl⟩ : syracuseStep 2085031 = 3127547) B3127547
theorem B1855655 : Blo 487790 1855655 := bstep (se 1 (by rfl) ⟨1391741, by rfl⟩ : syracuseStep 1855655 = 2783483) B2783483
theorem B5361983 : Blo 487790 5361983 := bstep (se 1 (by rfl) ⟨4021487, by rfl⟩ : syracuseStep 5361983 = 8042975) B8042975
theorem B22565945 : Blo 487790 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B841031 : Blo 487790 841031 := bstep (se 1 (by rfl) ⟨630773, by rfl⟩ : syracuseStep 841031 = 1261547) B1261547
theorem B1398815 : Blo 487790 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B1103975 : Blo 487790 1103975 := bstep (se 1 (by rfl) ⟨827981, by rfl⟩ : syracuseStep 1103975 = 1655963) B1655963
theorem B13720013 : Blo 487790 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B548959 : Blo 487790 548959 := bstep (se 1 (by rfl) ⟨411719, by rfl⟩ : syracuseStep 548959 = 823439) B823439
theorem B1106063 : Blo 487790 1106063 := bstep (se 1 (by rfl) ⟨829547, by rfl⟩ : syracuseStep 1106063 = 1659095) B1659095
theorem B1567799 : Blo 487790 1567799 := bstep (se 1 (by rfl) ⟨1175849, by rfl⟩ : syracuseStep 1567799 = 2351699) B2351699
theorem B1862747 : Blo 487790 1862747 := bstep (se 1 (by rfl) ⟨1397060, by rfl⟩ : syracuseStep 1862747 = 2794121) B2794121
theorem B488895 : Blo 487790 488895 := bstep (se 1 (by rfl) ⟨366671, by rfl⟩ : syracuseStep 488895 = 733343) B733343
theorem B489679 : Blo 487790 489679 := bstep (se 1 (by rfl) ⟨367259, by rfl⟩ : syracuseStep 489679 = 734519) B734519
theorem B158497357 : Blo 487790 158497357 := bstep (se 3 (by rfl) ⟨29718254, by rfl⟩ : syracuseStep 158497357 = 59436509) B59436509
theorem B8944283 : Blo 487790 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B1571975 : Blo 487790 1571975 := bstep (se 1 (by rfl) ⟨1178981, by rfl⟩ : syracuseStep 1571975 = 2357963) B2357963
theorem B1244423 : Blo 487790 1244423 := bstep (se 1 (by rfl) ⟨933317, by rfl⟩ : syracuseStep 1244423 = 1866635) B1866635
theorem B491163 : Blo 487790 491163 := bstep (se 1 (by rfl) ⟨368372, by rfl⟩ : syracuseStep 491163 = 736745) B736745
theorem B7077577 : Blo 487790 7077577 := bstep (se 2 (by rfl) ⟨2654091, by rfl⟩ : syracuseStep 7077577 = 5308183) B5308183
theorem B2359039 : Blo 487790 2359039 := bstep (se 1 (by rfl) ⟨1769279, by rfl⟩ : syracuseStep 2359039 = 3538559) B3538559
theorem B3574655 : Blo 487790 3574655 := bstep (se 1 (by rfl) ⟨2680991, by rfl⟩ : syracuseStep 3574655 = 5361983) B5361983
theorem B53808401 : Blo 487790 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B15043963 : Blo 487790 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B560687 : Blo 487790 560687 := bstep (se 1 (by rfl) ⟨420515, by rfl⟩ : syracuseStep 560687 = 841031) B841031
theorem B9146675 : Blo 487790 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B21175991 : Blo 487790 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B14164379 : Blo 487790 14164379 := bstep (se 1 (by rfl) ⟨10623284, by rfl⟩ : syracuseStep 14164379 = 21246569) B21246569
theorem B211329809 : Blo 487790 211329809 := bstep (se 2 (by rfl) ⟨79248678, by rfl⟩ : syracuseStep 211329809 = 158497357) B158497357
theorem B1647647 : Blo 487790 1647647 := bstep (se 1 (by rfl) ⟨1235735, by rfl⟩ : syracuseStep 1647647 = 2471471) B2471471
theorem B5449037 : Blo 487790 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B7087499 : Blo 487790 7087499 := bstep (se 1 (by rfl) ⟨5315624, by rfl⟩ : syracuseStep 7087499 = 10631249) B10631249
theorem B1648511 : Blo 487790 1648511 := bstep (se 1 (by rfl) ⟨1236383, by rfl⟩ : syracuseStep 1648511 = 2472767) B2472767
theorem B829615 : Blo 487790 829615 := bstep (se 1 (by rfl) ⟨622211, by rfl⟩ : syracuseStep 829615 = 1244423) B1244423
theorem B731879 : Blo 487790 731879 := bstep (se 1 (by rfl) ⟨548909, by rfl⟩ : syracuseStep 731879 = 1097819) B1097819
theorem B731945 : Blo 487790 731945 := bstep (se 2 (by rfl) ⟨274479, by rfl⟩ : syracuseStep 731945 = 548959) B548959
theorem B700159 : Blo 487790 700159 := bstep (se 1 (by rfl) ⟨525119, by rfl⟩ : syracuseStep 700159 = 1050239) B1050239
theorem B2797537 : Blo 487790 2797537 := bstep (se 2 (by rfl) ⟨1049076, by rfl⟩ : syracuseStep 2797537 = 2098153) B2098153
theorem B1257935 : Blo 487790 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B733787 : Blo 487790 733787 := bstep (se 1 (by rfl) ⟨550340, by rfl⟩ : syracuseStep 733787 = 1100681) B1100681
theorem B931753 : Blo 487790 931753 := bstep (se 2 (by rfl) ⟨349407, by rfl⟩ : syracuseStep 931753 = 698815) B698815
theorem B932543 : Blo 487790 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B735983 : Blo 487790 735983 := bstep (se 1 (by rfl) ⟨551987, by rfl⟩ : syracuseStep 735983 = 1103975) B1103975
theorem B737375 : Blo 487790 737375 := bstep (se 1 (by rfl) ⟨553031, by rfl⟩ : syracuseStep 737375 = 1106063) B1106063
theorem B12242771 : Blo 487790 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B1855457 : Blo 487790 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B3724217 : Blo 487790 3724217 := bstep (se 2 (by rfl) ⟨1396581, by rfl⟩ : syracuseStep 3724217 = 2793163) B2793163
theorem B1104839 : Blo 487790 1104839 := bstep (se 1 (by rfl) ⟨828629, by rfl⟩ : syracuseStep 1104839 = 1657259) B1657259
theorem B1236991 : Blo 487790 1236991 := bstep (se 1 (by rfl) ⟨927743, by rfl⟩ : syracuseStep 1236991 = 1855487) B1855487
theorem B1237103 : Blo 487790 1237103 := bstep (se 1 (by rfl) ⟨927827, by rfl⟩ : syracuseStep 1237103 = 1855655) B1855655
theorem B2780041 : Blo 487790 2780041 := bstep (se 2 (by rfl) ⟨1042515, by rfl⟩ : syracuseStep 2780041 = 2085031) B2085031
theorem B23851421 : Blo 487790 23851421 := bstep (se 3 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 23851421 = 8944283) B8944283
theorem B1045199 : Blo 487790 1045199 := bstep (se 1 (by rfl) ⟨783899, by rfl⟩ : syracuseStep 1045199 = 1567799) B1567799
theorem B1241831 : Blo 487790 1241831 := bstep (se 1 (by rfl) ⟨931373, by rfl⟩ : syracuseStep 1241831 = 1862747) B1862747
theorem B8451161 : Blo 487790 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B1341373 : Blo 487790 1341373 := bstep (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) B503015
theorem B1047983 : Blo 487790 1047983 := bstep (se 1 (by rfl) ⟨785987, by rfl⟩ : syracuseStep 1047983 = 1571975) B1571975
theorem B9436769 : Blo 487790 9436769 := bstep (se 2 (by rfl) ⟨3538788, by rfl⟩ : syracuseStep 9436769 = 7077577) B7077577
theorem B3145385 : Blo 487790 3145385 := bstep (se 2 (by rfl) ⟨1179519, by rfl⟩ : syracuseStep 3145385 = 2359039) B2359039
theorem B491583 : Blo 487790 491583 := bstep (se 1 (by rfl) ⟨368687, by rfl⟩ : syracuseStep 491583 = 737375) B737375
theorem B8161847 : Blo 487790 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B6097783 : Blo 487790 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B3706721 : Blo 487790 3706721 := bstep (se 2 (by rfl) ⟨1390020, by rfl⟩ : syracuseStep 3706721 = 2780041) B2780041
theorem B20058617 : Blo 487790 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B824735 : Blo 487790 824735 := bstep (se 1 (by rfl) ⟨618551, by rfl⟩ : syracuseStep 824735 = 1237103) B1237103
theorem B9442919 : Blo 487790 9442919 := bstep (se 1 (by rfl) ⟨7082189, by rfl⟩ : syracuseStep 9442919 = 14164379) B14164379
theorem B4724999 : Blo 487790 4724999 := bstep (se 1 (by rfl) ⟨3543749, by rfl⟩ : syracuseStep 4724999 = 7087499) B7087499
theorem B15900947 : Blo 487790 15900947 := bstep (se 1 (by rfl) ⟨11925710, by rfl⟩ : syracuseStep 15900947 = 23851421) B23851421
theorem B696799 : Blo 487790 696799 := bstep (se 1 (by rfl) ⟨522599, by rfl⟩ : syracuseStep 696799 = 1045199) B1045199
theorem B827887 : Blo 487790 827887 := bstep (se 1 (by rfl) ⟨620915, by rfl⟩ : syracuseStep 827887 = 1241831) B1241831
theorem B2794621 : Blo 487790 2794621 := bstep (se 3 (by rfl) ⟨523991, by rfl⟩ : syracuseStep 2794621 = 1047983) B1047983
theorem B1649321 : Blo 487790 1649321 := bstep (se 2 (by rfl) ⟨618495, by rfl⟩ : syracuseStep 1649321 = 1236991) B1236991
theorem B3354493 : Blo 487790 3354493 := bstep (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) B1257935
theorem B14530765 : Blo 487790 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B736559 : Blo 487790 736559 := bstep (se 1 (by rfl) ⟨552419, by rfl⟩ : syracuseStep 736559 = 1104839) B1104839
theorem B933545 : Blo 487790 933545 := bstep (se 2 (by rfl) ⟨350079, by rfl⟩ : syracuseStep 933545 = 700159) B700159
theorem B5980661 : Blo 487790 5980661 := bstep (se 5 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 5980661 = 560687) B560687
theorem B140886539 : Blo 487790 140886539 := bstep (se 1 (by rfl) ⟨105664904, by rfl⟩ : syracuseStep 140886539 = 211329809) B211329809
theorem B1098431 : Blo 487790 1098431 := bstep (se 1 (by rfl) ⟨823823, by rfl⟩ : syracuseStep 1098431 = 1647647) B1647647
theorem B1099007 : Blo 487790 1099007 := bstep (se 1 (by rfl) ⟨824255, by rfl⟩ : syracuseStep 1099007 = 1648511) B1648511
theorem B1788497 : Blo 487790 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B2383103 : Blo 487790 2383103 := bstep (se 1 (by rfl) ⟨1787327, by rfl⟩ : syracuseStep 2383103 = 3574655) B3574655
theorem B1236971 : Blo 487790 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B1106153 : Blo 487790 1106153 := bstep (se 2 (by rfl) ⟨414807, by rfl⟩ : syracuseStep 1106153 = 829615) B829615
theorem B2482811 : Blo 487790 2482811 := bstep (se 1 (by rfl) ⟨1862108, by rfl⟩ : syracuseStep 2482811 = 3724217) B3724217
theorem B14117327 : Blo 487790 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B3730049 : Blo 487790 3730049 := bstep (se 2 (by rfl) ⟨1398768, by rfl⟩ : syracuseStep 3730049 = 2797537) B2797537
theorem B487919 : Blo 487790 487919 := bstep (se 1 (by rfl) ⟨365939, by rfl⟩ : syracuseStep 487919 = 731879) B731879
theorem B487963 : Blo 487790 487963 := bstep (se 1 (by rfl) ⟨365972, by rfl⟩ : syracuseStep 487963 = 731945) B731945
theorem B1242337 : Blo 487790 1242337 := bstep (se 2 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 1242337 = 931753) B931753
theorem B489191 : Blo 487790 489191 := bstep (se 1 (by rfl) ⟨366893, by rfl⟩ : syracuseStep 489191 = 733787) B733787
theorem B143489069 : Blo 487790 143489069 := bstep (se 3 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 143489069 = 53808401) B53808401
theorem B5634107 : Blo 487790 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B621695 : Blo 487790 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B490655 : Blo 487790 490655 := bstep (se 1 (by rfl) ⟨367991, by rfl⟩ : syracuseStep 490655 = 735983) B735983
theorem B6291179 : Blo 487790 6291179 := bstep (se 1 (by rfl) ⟨4718384, by rfl⟩ : syracuseStep 6291179 = 9436769) B9436769
theorem B2096923 : Blo 487790 2096923 := bstep (se 1 (by rfl) ⟨1572692, by rfl⟩ : syracuseStep 2096923 = 3145385) B3145385
theorem B5441231 : Blo 487790 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B13372411 : Blo 487790 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B6295279 : Blo 487790 6295279 := bstep (se 1 (by rfl) ⟨4721459, by rfl⟩ : syracuseStep 6295279 = 9442919) B9442919
theorem B8130377 : Blo 487790 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B3149999 : Blo 487790 3149999 := bstep (se 1 (by rfl) ⟨2362499, by rfl⟩ : syracuseStep 3149999 = 4724999) B4724999
theorem B824647 : Blo 487790 824647 := bstep (se 1 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 824647 = 1236971) B1236971
theorem B9411551 : Blo 487790 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B19374353 : Blo 487790 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B95659379 : Blo 487790 95659379 := bstep (se 1 (by rfl) ⟨71744534, by rfl⟩ : syracuseStep 95659379 = 143489069) B143489069
theorem B2795897 : Blo 487790 2795897 := bstep (se 2 (by rfl) ⟨1048461, by rfl⟩ : syracuseStep 2795897 = 2096923) B2096923
theorem B93924359 : Blo 487790 93924359 := bstep (se 1 (by rfl) ⟨70443269, by rfl⟩ : syracuseStep 93924359 = 140886539) B140886539
theorem B732287 : Blo 487790 732287 := bstep (se 1 (by rfl) ⟨549215, by rfl⟩ : syracuseStep 732287 = 1098431) B1098431
theorem B929065 : Blo 487790 929065 := bstep (se 2 (by rfl) ⟨348399, by rfl⟩ : syracuseStep 929065 = 696799) B696799
theorem B732671 : Blo 487790 732671 := bstep (se 1 (by rfl) ⟨549503, by rfl⟩ : syracuseStep 732671 = 1099007) B1099007
theorem B1192331 : Blo 487790 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B2471147 : Blo 487790 2471147 := bstep (se 1 (by rfl) ⟨1853360, by rfl⟩ : syracuseStep 2471147 = 3706721) B3706721
theorem B1588735 : Blo 487790 1588735 := bstep (se 1 (by rfl) ⟨1191551, by rfl⟩ : syracuseStep 1588735 = 2383103) B2383103
theorem B4472657 : Blo 487790 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B737435 : Blo 487790 737435 := bstep (se 1 (by rfl) ⟨553076, by rfl⟩ : syracuseStep 737435 = 1106153) B1106153
theorem B10600631 : Blo 487790 10600631 := bstep (se 1 (by rfl) ⟨7950473, by rfl⟩ : syracuseStep 10600631 = 15900947) B15900947
theorem B1655207 : Blo 487790 1655207 := bstep (se 1 (by rfl) ⟨1241405, by rfl⟩ : syracuseStep 1655207 = 2482811) B2482811
theorem B1656449 : Blo 487790 1656449 := bstep (se 2 (by rfl) ⟨621168, by rfl⟩ : syracuseStep 1656449 = 1242337) B1242337
theorem B1099547 : Blo 487790 1099547 := bstep (se 1 (by rfl) ⟨824660, by rfl⟩ : syracuseStep 1099547 = 1649321) B1649321
theorem B1657853 : Blo 487790 1657853 := bstep (se 3 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 1657853 = 621695) B621695
theorem B3756071 : Blo 487790 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B3987107 : Blo 487790 3987107 := bstep (se 1 (by rfl) ⟨2990330, by rfl⟩ : syracuseStep 3987107 = 5980661) B5980661
theorem B1103849 : Blo 487790 1103849 := bstep (se 2 (by rfl) ⟨413943, by rfl⟩ : syracuseStep 1103849 = 827887) B827887
theorem B3726161 : Blo 487790 3726161 := bstep (se 2 (by rfl) ⟨1397310, by rfl⟩ : syracuseStep 3726161 = 2794621) B2794621
theorem B549823 : Blo 487790 549823 := bstep (se 1 (by rfl) ⟨412367, by rfl⟩ : syracuseStep 549823 = 824735) B824735
theorem B2486699 : Blo 487790 2486699 := bstep (se 1 (by rfl) ⟨1865024, by rfl⟩ : syracuseStep 2486699 = 3730049) B3730049
theorem B2489453 : Blo 487790 2489453 := bstep (se 3 (by rfl) ⟨466772, by rfl⟩ : syracuseStep 2489453 = 933545) B933545
theorem B491039 : Blo 487790 491039 := bstep (se 1 (by rfl) ⟨368279, by rfl⟩ : syracuseStep 491039 = 736559) B736559
theorem B4194119 : Blo 487790 4194119 := bstep (se 1 (by rfl) ⟨3145589, by rfl⟩ : syracuseStep 4194119 = 6291179) B6291179
theorem B491623 : Blo 487790 491623 := bstep (se 1 (by rfl) ⟨368717, by rfl⟩ : syracuseStep 491623 = 737435) B737435
theorem B2099999 : Blo 487790 2099999 := bstep (se 1 (by rfl) ⟨1574999, by rfl⟩ : syracuseStep 2099999 = 3149999) B3149999
theorem B2658071 : Blo 487790 2658071 := bstep (se 1 (by rfl) ⟨1993553, by rfl⟩ : syracuseStep 2658071 = 3987107) B3987107
theorem B17829881 : Blo 487790 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B8393705 : Blo 487790 8393705 := bstep (se 2 (by rfl) ⟨3147639, by rfl⟩ : syracuseStep 8393705 = 6295279) B6295279
theorem B12916235 : Blo 487790 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B63772919 : Blo 487790 63772919 := bstep (se 1 (by rfl) ⟨47829689, by rfl⟩ : syracuseStep 63772919 = 95659379) B95659379
theorem B794887 : Blo 487790 794887 := bstep (se 1 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 794887 = 1192331) B1192331
theorem B1647431 : Blo 487790 1647431 := bstep (se 1 (by rfl) ⟨1235573, by rfl⟩ : syracuseStep 1647431 = 2471147) B2471147
theorem B2796079 : Blo 487790 2796079 := bstep (se 1 (by rfl) ⟨2097059, by rfl⟩ : syracuseStep 2796079 = 4194119) B4194119
theorem B733031 : Blo 487790 733031 := bstep (se 1 (by rfl) ⟨549773, by rfl⟩ : syracuseStep 733031 = 1099547) B1099547
theorem B733097 : Blo 487790 733097 := bstep (se 2 (by rfl) ⟨274911, by rfl⟩ : syracuseStep 733097 = 549823) B549823
theorem B5420251 : Blo 487790 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B2504047 : Blo 487790 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B735899 : Blo 487790 735899 := bstep (se 1 (by rfl) ⟨551924, by rfl⟩ : syracuseStep 735899 = 1103849) B1103849
theorem B6274367 : Blo 487790 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B1099529 : Blo 487790 1099529 := bstep (se 2 (by rfl) ⟨412323, by rfl⟩ : syracuseStep 1099529 = 824647) B824647
theorem B1657799 : Blo 487790 1657799 := bstep (se 1 (by rfl) ⟨1243349, by rfl⟩ : syracuseStep 1657799 = 2486699) B2486699
theorem B2118313 : Blo 487790 2118313 := bstep (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) B1588735
theorem B1659635 : Blo 487790 1659635 := bstep (se 1 (by rfl) ⟨1244726, by rfl⟩ : syracuseStep 1659635 = 2489453) B2489453
theorem B7067087 : Blo 487790 7067087 := bstep (se 1 (by rfl) ⟨5300315, by rfl⟩ : syracuseStep 7067087 = 10600631) B10600631
theorem B1103471 : Blo 487790 1103471 := bstep (se 1 (by rfl) ⟨827603, by rfl⟩ : syracuseStep 1103471 = 1655207) B1655207
theorem B1104299 : Blo 487790 1104299 := bstep (se 1 (by rfl) ⟨828224, by rfl⟩ : syracuseStep 1104299 = 1656449) B1656449
theorem B3627487 : Blo 487790 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B1105235 : Blo 487790 1105235 := bstep (se 1 (by rfl) ⟨828926, by rfl⟩ : syracuseStep 1105235 = 1657853) B1657853
theorem B1238753 : Blo 487790 1238753 := bstep (se 2 (by rfl) ⟨464532, by rfl⟩ : syracuseStep 1238753 = 929065) B929065
theorem B2484107 : Blo 487790 2484107 := bstep (se 1 (by rfl) ⟨1863080, by rfl⟩ : syracuseStep 2484107 = 3726161) B3726161
theorem B1863931 : Blo 487790 1863931 := bstep (se 1 (by rfl) ⟨1397948, by rfl⟩ : syracuseStep 1863931 = 2795897) B2795897
theorem B62616239 : Blo 487790 62616239 := bstep (se 1 (by rfl) ⟨46962179, by rfl⟩ : syracuseStep 62616239 = 93924359) B93924359
theorem B488191 : Blo 487790 488191 := bstep (se 1 (by rfl) ⟨366143, by rfl⟩ : syracuseStep 488191 = 732287) B732287
theorem B488447 : Blo 487790 488447 := bstep (se 1 (by rfl) ⟨366335, by rfl⟩ : syracuseStep 488447 = 732671) B732671
theorem B2981771 : Blo 487790 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B1772047 : Blo 487790 1772047 := bstep (se 1 (by rfl) ⟨1329035, by rfl⟩ : syracuseStep 1772047 = 2658071) B2658071
theorem B2824417 : Blo 487790 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B825835 : Blo 487790 825835 := bstep (se 1 (by rfl) ⟨619376, by rfl⟩ : syracuseStep 825835 = 1238753) B1238753
theorem B733019 : Blo 487790 733019 := bstep (se 1 (by rfl) ⟨549764, by rfl⟩ : syracuseStep 733019 = 1099529) B1099529
theorem B4239397 : Blo 487790 4239397 := bstep (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) B794887
theorem B19346597 : Blo 487790 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B735647 : Blo 487790 735647 := bstep (se 1 (by rfl) ⟨551735, by rfl⟩ : syracuseStep 735647 = 1103471) B1103471
theorem B42515279 : Blo 487790 42515279 := bstep (se 1 (by rfl) ⟨31886459, by rfl⟩ : syracuseStep 42515279 = 63772919) B63772919
theorem B736199 : Blo 487790 736199 := bstep (se 1 (by rfl) ⟨552149, by rfl⟩ : syracuseStep 736199 = 1104299) B1104299
theorem B736823 : Blo 487790 736823 := bstep (se 1 (by rfl) ⟨552617, by rfl⟩ : syracuseStep 736823 = 1105235) B1105235
theorem B1098287 : Blo 487790 1098287 := bstep (se 1 (by rfl) ⟨823715, by rfl⟩ : syracuseStep 1098287 = 1647431) B1647431
theorem B1656071 : Blo 487790 1656071 := bstep (se 1 (by rfl) ⟨1242053, by rfl⟩ : syracuseStep 1656071 = 2484107) B2484107
theorem B7227001 : Blo 487790 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B4182911 : Blo 487790 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B1987847 : Blo 487790 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B1399999 : Blo 487790 1399999 := bstep (se 1 (by rfl) ⟨1049999, by rfl⟩ : syracuseStep 1399999 = 2099999) B2099999
theorem B1105199 : Blo 487790 1105199 := bstep (se 1 (by rfl) ⟨828899, by rfl⟩ : syracuseStep 1105199 = 1657799) B1657799
theorem B11886587 : Blo 487790 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B1106423 : Blo 487790 1106423 := bstep (se 1 (by rfl) ⟨829817, by rfl⟩ : syracuseStep 1106423 = 1659635) B1659635
theorem B5595803 : Blo 487790 5595803 := bstep (se 1 (by rfl) ⟨4196852, by rfl⟩ : syracuseStep 5595803 = 8393705) B8393705
theorem B3728105 : Blo 487790 3728105 := bstep (se 2 (by rfl) ⟨1398039, by rfl⟩ : syracuseStep 3728105 = 2796079) B2796079
theorem B4711391 : Blo 487790 4711391 := bstep (se 1 (by rfl) ⟨3533543, by rfl⟩ : syracuseStep 4711391 = 7067087) B7067087
theorem B8610823 : Blo 487790 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B2485241 : Blo 487790 2485241 := bstep (se 2 (by rfl) ⟨931965, by rfl⟩ : syracuseStep 2485241 = 1863931) B1863931
theorem B3338729 : Blo 487790 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B488687 : Blo 487790 488687 := bstep (se 1 (by rfl) ⟨366515, by rfl⟩ : syracuseStep 488687 = 733031) B733031
theorem B488731 : Blo 487790 488731 := bstep (se 1 (by rfl) ⟨366548, by rfl⟩ : syracuseStep 488731 = 733097) B733097
theorem B41744159 : Blo 487790 41744159 := bstep (se 1 (by rfl) ⟨31308119, by rfl⟩ : syracuseStep 41744159 = 62616239) B62616239
theorem B490599 : Blo 487790 490599 := bstep (se 1 (by rfl) ⟨367949, by rfl⟩ : syracuseStep 490599 = 735899) B735899
theorem B22610117 : Blo 487790 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B2788607 : Blo 487790 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B38544005 : Blo 487790 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B27829439 : Blo 487790 27829439 := bstep (se 1 (by rfl) ⟨20872079, by rfl⟩ : syracuseStep 27829439 = 41744159) B41744159
theorem B732191 : Blo 487790 732191 := bstep (se 1 (by rfl) ⟨549143, by rfl⟩ : syracuseStep 732191 = 1098287) B1098287
theorem B11481097 : Blo 487790 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B9450917 : Blo 487790 9450917 := bstep (se 4 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 9450917 = 1772047) B1772047
theorem B1325231 : Blo 487790 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B736799 : Blo 487790 736799 := bstep (se 1 (by rfl) ⟨552599, by rfl⟩ : syracuseStep 736799 = 1105199) B1105199
theorem B737615 : Blo 487790 737615 := bstep (se 1 (by rfl) ⟨553211, by rfl⟩ : syracuseStep 737615 = 1106423) B1106423
theorem B1656827 : Blo 487790 1656827 := bstep (se 1 (by rfl) ⟨1242620, by rfl⟩ : syracuseStep 1656827 = 2485241) B2485241
theorem B1101113 : Blo 487790 1101113 := bstep (se 2 (by rfl) ⟨412917, by rfl⟩ : syracuseStep 1101113 = 825835) B825835
theorem B12897731 : Blo 487790 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B1104047 : Blo 487790 1104047 := bstep (se 1 (by rfl) ⟨828035, by rfl⟩ : syracuseStep 1104047 = 1656071) B1656071
theorem B7924391 : Blo 487790 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B3730535 : Blo 487790 3730535 := bstep (se 1 (by rfl) ⟨2797901, by rfl⟩ : syracuseStep 3730535 = 5595803) B5595803
theorem B2485403 : Blo 487790 2485403 := bstep (se 1 (by rfl) ⟨1864052, by rfl⟩ : syracuseStep 2485403 = 3728105) B3728105
theorem B3140927 : Blo 487790 3140927 := bstep (se 1 (by rfl) ⟨2355695, by rfl⟩ : syracuseStep 3140927 = 4711391) B4711391
theorem B488679 : Blo 487790 488679 := bstep (se 1 (by rfl) ⟨366509, by rfl⟩ : syracuseStep 488679 = 733019) B733019
theorem B3765889 : Blo 487790 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B2225819 : Blo 487790 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B1866665 : Blo 487790 1866665 := bstep (se 2 (by rfl) ⟨699999, by rfl⟩ : syracuseStep 1866665 = 1399999) B1399999
theorem B490431 : Blo 487790 490431 := bstep (se 1 (by rfl) ⟨367823, by rfl⟩ : syracuseStep 490431 = 735647) B735647
theorem B28343519 : Blo 487790 28343519 := bstep (se 1 (by rfl) ⟨21257639, by rfl⟩ : syracuseStep 28343519 = 42515279) B42515279
theorem B490799 : Blo 487790 490799 := bstep (se 1 (by rfl) ⟨368099, by rfl⟩ : syracuseStep 490799 = 736199) B736199
theorem B491215 : Blo 487790 491215 := bstep (se 1 (by rfl) ⟨368411, by rfl⟩ : syracuseStep 491215 = 736823) B736823
theorem B491743 : Blo 487790 491743 := bstep (se 1 (by rfl) ⟨368807, by rfl⟩ : syracuseStep 491743 = 737615) B737615
theorem B60293645 : Blo 487790 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B5935517 : Blo 487790 5935517 := bstep (se 3 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 5935517 = 2225819) B2225819
theorem B15308129 : Blo 487790 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B25696003 : Blo 487790 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B18552959 : Blo 487790 18552959 := bstep (se 1 (by rfl) ⟨13914719, by rfl⟩ : syracuseStep 18552959 = 27829439) B27829439
theorem B5282927 : Blo 487790 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B5021185 : Blo 487790 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B6300611 : Blo 487790 6300611 := bstep (se 1 (by rfl) ⟨4725458, by rfl⟩ : syracuseStep 6300611 = 9450917) B9450917
theorem B734075 : Blo 487790 734075 := bstep (se 1 (by rfl) ⟨550556, by rfl⟩ : syracuseStep 734075 = 1101113) B1101113
theorem B8598487 : Blo 487790 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B736031 : Blo 487790 736031 := bstep (se 1 (by rfl) ⟨552023, by rfl⟩ : syracuseStep 736031 = 1104047) B1104047
theorem B1656935 : Blo 487790 1656935 := bstep (se 1 (by rfl) ⟨1242701, by rfl⟩ : syracuseStep 1656935 = 2485403) B2485403
theorem B18895679 : Blo 487790 18895679 := bstep (se 1 (by rfl) ⟨14171759, by rfl⟩ : syracuseStep 18895679 = 28343519) B28343519
theorem B1104551 : Blo 487790 1104551 := bstep (se 1 (by rfl) ⟨828413, by rfl⟩ : syracuseStep 1104551 = 1656827) B1656827
theorem B1859071 : Blo 487790 1859071 := bstep (se 1 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 1859071 = 2788607) B2788607
theorem B488127 : Blo 487790 488127 := bstep (se 1 (by rfl) ⟨366095, by rfl⟩ : syracuseStep 488127 = 732191) B732191
theorem B2487023 : Blo 487790 2487023 := bstep (se 1 (by rfl) ⟨1865267, by rfl⟩ : syracuseStep 2487023 = 3730535) B3730535
theorem B2093951 : Blo 487790 2093951 := bstep (se 1 (by rfl) ⟨1570463, by rfl⟩ : syracuseStep 2093951 = 3140927) B3140927
theorem B883487 : Blo 487790 883487 := bstep (se 1 (by rfl) ⟨662615, by rfl⟩ : syracuseStep 883487 = 1325231) B1325231
theorem B1244443 : Blo 487790 1244443 := bstep (se 1 (by rfl) ⟨933332, by rfl⟩ : syracuseStep 1244443 = 1866665) B1866665
theorem B491199 : Blo 487790 491199 := bstep (se 1 (by rfl) ⟨368399, by rfl⟩ : syracuseStep 491199 = 736799) B736799
theorem B4200407 : Blo 487790 4200407 := bstep (se 1 (by rfl) ⟨3150305, by rfl⟩ : syracuseStep 4200407 = 6300611) B6300611
theorem B6694913 : Blo 487790 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B12597119 : Blo 487790 12597119 := bstep (se 1 (by rfl) ⟨9447839, by rfl⟩ : syracuseStep 12597119 = 18895679) B18895679
theorem B12368639 : Blo 487790 12368639 := bstep (se 1 (by rfl) ⟨9276479, by rfl⟩ : syracuseStep 12368639 = 18552959) B18552959
theorem B736367 : Blo 487790 736367 := bstep (se 1 (by rfl) ⟨552275, by rfl⟩ : syracuseStep 736367 = 1104551) B1104551
theorem B3521951 : Blo 487790 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B34261337 : Blo 487790 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B1658015 : Blo 487790 1658015 := bstep (se 1 (by rfl) ⟨1243511, by rfl⟩ : syracuseStep 1658015 = 2487023) B2487023
theorem B1395967 : Blo 487790 1395967 := bstep (se 1 (by rfl) ⟨1046975, by rfl⟩ : syracuseStep 1395967 = 2093951) B2093951
theorem B1659257 : Blo 487790 1659257 := bstep (se 2 (by rfl) ⟨622221, by rfl⟩ : syracuseStep 1659257 = 1244443) B1244443
theorem B2478761 : Blo 487790 2478761 := bstep (se 2 (by rfl) ⟨929535, by rfl⟩ : syracuseStep 2478761 = 1859071) B1859071
theorem B40195763 : Blo 487790 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B1104623 : Blo 487790 1104623 := bstep (se 1 (by rfl) ⟨828467, by rfl⟩ : syracuseStep 1104623 = 1656935) B1656935
theorem B3957011 : Blo 487790 3957011 := bstep (se 1 (by rfl) ⟨2967758, by rfl⟩ : syracuseStep 3957011 = 5935517) B5935517
theorem B40821677 : Blo 487790 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B11464649 : Blo 487790 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B2355965 : Blo 487790 2355965 := bstep (se 3 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 2355965 = 883487) B883487
theorem B489383 : Blo 487790 489383 := bstep (se 1 (by rfl) ⟨367037, by rfl⟩ : syracuseStep 489383 = 734075) B734075
theorem B490687 : Blo 487790 490687 := bstep (se 1 (by rfl) ⟨368015, by rfl⟩ : syracuseStep 490687 = 736031) B736031
theorem B91363565 : Blo 487790 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B4463275 : Blo 487790 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B7643099 : Blo 487790 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B8398079 : Blo 487790 8398079 := bstep (se 1 (by rfl) ⟨6298559, by rfl⟩ : syracuseStep 8398079 = 12597119) B12597119
theorem B1652507 : Blo 487790 1652507 := bstep (se 1 (by rfl) ⟨1239380, by rfl⟩ : syracuseStep 1652507 = 2478761) B2478761
theorem B2800271 : Blo 487790 2800271 := bstep (se 1 (by rfl) ⟨2100203, by rfl⟩ : syracuseStep 2800271 = 4200407) B4200407
theorem B736415 : Blo 487790 736415 := bstep (se 1 (by rfl) ⟨552311, by rfl⟩ : syracuseStep 736415 = 1104623) B1104623
theorem B2638007 : Blo 487790 2638007 := bstep (se 1 (by rfl) ⟨1978505, by rfl⟩ : syracuseStep 2638007 = 3957011) B3957011
theorem B27214451 : Blo 487790 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B32983037 : Blo 487790 32983037 := bstep (se 3 (by rfl) ⟨6184319, by rfl⟩ : syracuseStep 32983037 = 12368639) B12368639
theorem B2347967 : Blo 487790 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B1105343 : Blo 487790 1105343 := bstep (se 1 (by rfl) ⟨829007, by rfl⟩ : syracuseStep 1105343 = 1658015) B1658015
theorem B1106171 : Blo 487790 1106171 := bstep (se 1 (by rfl) ⟨829628, by rfl⟩ : syracuseStep 1106171 = 1659257) B1659257
theorem B26797175 : Blo 487790 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B1861289 : Blo 487790 1861289 := bstep (se 2 (by rfl) ⟨697983, by rfl⟩ : syracuseStep 1861289 = 1395967) B1395967
theorem B1570643 : Blo 487790 1570643 := bstep (se 1 (by rfl) ⟨1177982, by rfl⟩ : syracuseStep 1570643 = 2355965) B2355965
theorem B490911 : Blo 487790 490911 := bstep (se 1 (by rfl) ⟨368183, by rfl⟩ : syracuseStep 490911 = 736367) B736367
theorem B21988691 : Blo 487790 21988691 := bstep (se 1 (by rfl) ⟨16491518, by rfl⟩ : syracuseStep 21988691 = 32983037) B32983037
theorem B6261245 : Blo 487790 6261245 := bstep (se 3 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 6261245 = 2347967) B2347967
theorem B17864783 : Blo 487790 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B736895 : Blo 487790 736895 := bstep (se 1 (by rfl) ⟨552671, by rfl⟩ : syracuseStep 736895 = 1105343) B1105343
theorem B5095399 : Blo 487790 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B737447 : Blo 487790 737447 := bstep (se 1 (by rfl) ⟨553085, by rfl⟩ : syracuseStep 737447 = 1106171) B1106171
theorem B5951033 : Blo 487790 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B1101671 : Blo 487790 1101671 := bstep (se 1 (by rfl) ⟨826253, by rfl⟩ : syracuseStep 1101671 = 1652507) B1652507
theorem B1758671 : Blo 487790 1758671 := bstep (se 1 (by rfl) ⟨1319003, by rfl⟩ : syracuseStep 1758671 = 2638007) B2638007
theorem B18142967 : Blo 487790 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B60909043 : Blo 487790 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B5598719 : Blo 487790 5598719 := bstep (se 1 (by rfl) ⟨4199039, by rfl⟩ : syracuseStep 5598719 = 8398079) B8398079
theorem B1240859 : Blo 487790 1240859 := bstep (se 1 (by rfl) ⟨930644, by rfl⟩ : syracuseStep 1240859 = 1861289) B1861289
theorem B1047095 : Blo 487790 1047095 := bstep (se 1 (by rfl) ⟨785321, by rfl⟩ : syracuseStep 1047095 = 1570643) B1570643
theorem B1866847 : Blo 487790 1866847 := bstep (se 1 (by rfl) ⟨1400135, by rfl⟩ : syracuseStep 1866847 = 2800271) B2800271
theorem B490943 : Blo 487790 490943 := bstep (se 1 (by rfl) ⟨368207, by rfl⟩ : syracuseStep 490943 = 736415) B736415
theorem B491631 : Blo 487790 491631 := bstep (se 1 (by rfl) ⟨368723, by rfl⟩ : syracuseStep 491631 = 737447) B737447
theorem B3967355 : Blo 487790 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B827239 : Blo 487790 827239 := bstep (se 1 (by rfl) ⟨620429, by rfl⟩ : syracuseStep 827239 = 1240859) B1240859
theorem B698063 : Blo 487790 698063 := bstep (se 1 (by rfl) ⟨523547, by rfl⟩ : syracuseStep 698063 = 1047095) B1047095
theorem B6793865 : Blo 487790 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B14659127 : Blo 487790 14659127 := bstep (se 1 (by rfl) ⟨10994345, by rfl⟩ : syracuseStep 14659127 = 21988691) B21988691
theorem B4174163 : Blo 487790 4174163 := bstep (se 1 (by rfl) ⟨3130622, by rfl⟩ : syracuseStep 4174163 = 6261245) B6261245
theorem B81212057 : Blo 487790 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B734447 : Blo 487790 734447 := bstep (se 1 (by rfl) ⟨550835, by rfl⟩ : syracuseStep 734447 = 1101671) B1101671
theorem B11909855 : Blo 487790 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B48381245 : Blo 487790 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B1172447 : Blo 487790 1172447 := bstep (se 1 (by rfl) ⟨879335, by rfl⟩ : syracuseStep 1172447 = 1758671) B1758671
theorem B3732479 : Blo 487790 3732479 := bstep (se 1 (by rfl) ⟨2799359, by rfl⟩ : syracuseStep 3732479 = 5598719) B5598719
theorem B2489129 : Blo 487790 2489129 := bstep (se 2 (by rfl) ⟨933423, by rfl⟩ : syracuseStep 2489129 = 1866847) B1866847
theorem B491263 : Blo 487790 491263 := bstep (se 1 (by rfl) ⟨368447, by rfl⟩ : syracuseStep 491263 = 736895) B736895
theorem B4529243 : Blo 487790 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B9772751 : Blo 487790 9772751 := bstep (se 1 (by rfl) ⟨7329563, by rfl⟩ : syracuseStep 9772751 = 14659127) B14659127
theorem B54141371 : Blo 487790 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B7939903 : Blo 487790 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B32254163 : Blo 487790 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B1659419 : Blo 487790 1659419 := bstep (se 1 (by rfl) ⟨1244564, by rfl⟩ : syracuseStep 1659419 = 2489129) B2489129
theorem B1102985 : Blo 487790 1102985 := bstep (se 2 (by rfl) ⟨413619, by rfl⟩ : syracuseStep 1102985 = 827239) B827239
theorem B2644903 : Blo 487790 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B1861501 : Blo 487790 1861501 := bstep (se 3 (by rfl) ⟨349031, by rfl⟩ : syracuseStep 1861501 = 698063) B698063
theorem B781631 : Blo 487790 781631 := bstep (se 1 (by rfl) ⟨586223, by rfl⟩ : syracuseStep 781631 = 1172447) B1172447
theorem B2782775 : Blo 487790 2782775 := bstep (se 1 (by rfl) ⟨2087081, by rfl⟩ : syracuseStep 2782775 = 4174163) B4174163
theorem B2488319 : Blo 487790 2488319 := bstep (se 1 (by rfl) ⟨1866239, by rfl⟩ : syracuseStep 2488319 = 3732479) B3732479
theorem B489631 : Blo 487790 489631 := bstep (se 1 (by rfl) ⟨367223, by rfl⟩ : syracuseStep 489631 = 734447) B734447
theorem B10586537 : Blo 487790 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B21502775 : Blo 487790 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B26060669 : Blo 487790 26060669 := bstep (se 3 (by rfl) ⟨4886375, by rfl⟩ : syracuseStep 26060669 = 9772751) B9772751
theorem B735323 : Blo 487790 735323 := bstep (se 1 (by rfl) ⟨551492, by rfl⟩ : syracuseStep 735323 = 1102985) B1102985
theorem B14106149 : Blo 487790 14106149 := bstep (se 4 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 14106149 = 2644903) B2644903
theorem B36094247 : Blo 487790 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B12077981 : Blo 487790 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B1855183 : Blo 487790 1855183 := bstep (se 1 (by rfl) ⟨1391387, by rfl⟩ : syracuseStep 1855183 = 2782775) B2782775
theorem B1658879 : Blo 487790 1658879 := bstep (se 1 (by rfl) ⟨1244159, by rfl⟩ : syracuseStep 1658879 = 2488319) B2488319
theorem B2482001 : Blo 487790 2482001 := bstep (se 2 (by rfl) ⟨930750, by rfl⟩ : syracuseStep 2482001 = 1861501) B1861501
theorem B1106279 : Blo 487790 1106279 := bstep (se 1 (by rfl) ⟨829709, by rfl⟩ : syracuseStep 1106279 = 1659419) B1659419
theorem B521087 : Blo 487790 521087 := bstep (se 1 (by rfl) ⟨390815, by rfl⟩ : syracuseStep 521087 = 781631) B781631
theorem B17373779 : Blo 487790 17373779 := bstep (se 1 (by rfl) ⟨13030334, by rfl⟩ : syracuseStep 17373779 = 26060669) B26060669
theorem B24062831 : Blo 487790 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B7057691 : Blo 487790 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B1389565 : Blo 487790 1389565 := bstep (se 3 (by rfl) ⟨260543, by rfl⟩ : syracuseStep 1389565 = 521087) B521087
theorem B14335183 : Blo 487790 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B2473577 : Blo 487790 2473577 := bstep (se 2 (by rfl) ⟨927591, by rfl⟩ : syracuseStep 2473577 = 1855183) B1855183
theorem B1654667 : Blo 487790 1654667 := bstep (se 1 (by rfl) ⟨1241000, by rfl⟩ : syracuseStep 1654667 = 2482001) B2482001
theorem B737519 : Blo 487790 737519 := bstep (se 1 (by rfl) ⟨553139, by rfl⟩ : syracuseStep 737519 = 1106279) B1106279
theorem B8051987 : Blo 487790 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B1105919 : Blo 487790 1105919 := bstep (se 1 (by rfl) ⟨829439, by rfl⟩ : syracuseStep 1105919 = 1658879) B1658879
theorem B490215 : Blo 487790 490215 := bstep (se 1 (by rfl) ⟨367661, by rfl⟩ : syracuseStep 490215 = 735323) B735323
theorem B9404099 : Blo 487790 9404099 := bstep (se 1 (by rfl) ⟨7053074, by rfl⟩ : syracuseStep 9404099 = 14106149) B14106149
theorem B491679 : Blo 487790 491679 := bstep (se 1 (by rfl) ⟨368759, by rfl⟩ : syracuseStep 491679 = 737519) B737519
theorem B19113577 : Blo 487790 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B1649051 : Blo 487790 1649051 := bstep (se 1 (by rfl) ⟨1236788, by rfl⟩ : syracuseStep 1649051 = 2473577) B2473577
theorem B6269399 : Blo 487790 6269399 := bstep (se 1 (by rfl) ⟨4702049, by rfl⟩ : syracuseStep 6269399 = 9404099) B9404099
theorem B11582519 : Blo 487790 11582519 := bstep (se 1 (by rfl) ⟨8686889, by rfl⟩ : syracuseStep 11582519 = 17373779) B17373779
theorem B737279 : Blo 487790 737279 := bstep (se 1 (by rfl) ⟨552959, by rfl⟩ : syracuseStep 737279 = 1105919) B1105919
theorem B1852753 : Blo 487790 1852753 := bstep (se 2 (by rfl) ⟨694782, by rfl⟩ : syracuseStep 1852753 = 1389565) B1389565
theorem B16041887 : Blo 487790 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B4705127 : Blo 487790 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B1103111 : Blo 487790 1103111 := bstep (se 1 (by rfl) ⟨827333, by rfl⟩ : syracuseStep 1103111 = 1654667) B1654667
theorem B5367991 : Blo 487790 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B123546869 : Blo 487790 123546869 := bstep (se 5 (by rfl) ⟨5791259, by rfl⟩ : syracuseStep 123546869 = 11582519) B11582519
theorem B10694591 : Blo 487790 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B2470337 : Blo 487790 2470337 := bstep (se 2 (by rfl) ⟨926376, by rfl⟩ : syracuseStep 2470337 = 1852753) B1852753
theorem B7157321 : Blo 487790 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B735407 : Blo 487790 735407 := bstep (se 1 (by rfl) ⟨551555, by rfl⟩ : syracuseStep 735407 = 1103111) B1103111
theorem B1099367 : Blo 487790 1099367 := bstep (se 1 (by rfl) ⟨824525, by rfl⟩ : syracuseStep 1099367 = 1649051) B1649051
theorem B4179599 : Blo 487790 4179599 := bstep (se 1 (by rfl) ⟨3134699, by rfl⟩ : syracuseStep 4179599 = 6269399) B6269399
theorem B3136751 : Blo 487790 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B101939077 : Blo 487790 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B491519 : Blo 487790 491519 := bstep (se 1 (by rfl) ⟨368639, by rfl⟩ : syracuseStep 491519 = 737279) B737279
theorem B2786399 : Blo 487790 2786399 := bstep (se 1 (by rfl) ⟨2089799, by rfl⟩ : syracuseStep 2786399 = 4179599) B4179599
theorem B1646891 : Blo 487790 1646891 := bstep (se 1 (by rfl) ⟨1235168, by rfl⟩ : syracuseStep 1646891 = 2470337) B2470337
theorem B732911 : Blo 487790 732911 := bstep (se 1 (by rfl) ⟨549683, by rfl⟩ : syracuseStep 732911 = 1099367) B1099367
theorem B82364579 : Blo 487790 82364579 := bstep (se 1 (by rfl) ⟨61773434, by rfl⟩ : syracuseStep 82364579 = 123546869) B123546869
theorem B7129727 : Blo 487790 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B4771547 : Blo 487790 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B2091167 : Blo 487790 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B135918769 : Blo 487790 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B490271 : Blo 487790 490271 := bstep (se 1 (by rfl) ⟨367703, by rfl⟩ : syracuseStep 490271 = 735407) B735407
theorem B4753151 : Blo 487790 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B3181031 : Blo 487790 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B1097927 : Blo 487790 1097927 := bstep (se 1 (by rfl) ⟨823445, by rfl⟩ : syracuseStep 1097927 = 1646891) B1646891
theorem B1394111 : Blo 487790 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B181225025 : Blo 487790 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B1857599 : Blo 487790 1857599 := bstep (se 1 (by rfl) ⟨1393199, by rfl⟩ : syracuseStep 1857599 = 2786399) B2786399
theorem B54909719 : Blo 487790 54909719 := bstep (se 1 (by rfl) ⟨41182289, by rfl⟩ : syracuseStep 54909719 = 82364579) B82364579
theorem B488607 : Blo 487790 488607 := bstep (se 1 (by rfl) ⟨366455, by rfl⟩ : syracuseStep 488607 = 732911) B732911
theorem B120816683 : Blo 487790 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B36606479 : Blo 487790 36606479 := bstep (se 1 (by rfl) ⟨27454859, by rfl⟩ : syracuseStep 36606479 = 54909719) B54909719
theorem B731951 : Blo 487790 731951 := bstep (se 1 (by rfl) ⟨548963, by rfl⟩ : syracuseStep 731951 = 1097927) B1097927
theorem B929407 : Blo 487790 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B3168767 : Blo 487790 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B2120687 : Blo 487790 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B1238399 : Blo 487790 1238399 := bstep (se 1 (by rfl) ⟨928799, by rfl⟩ : syracuseStep 1238399 = 1857599) B1857599
theorem B80544455 : Blo 487790 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B97617277 : Blo 487790 97617277 := bstep (se 3 (by rfl) ⟨18303239, by rfl⟩ : syracuseStep 97617277 = 36606479) B36606479
theorem B1413791 : Blo 487790 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B825599 : Blo 487790 825599 := bstep (se 1 (by rfl) ⟨619199, by rfl⟩ : syracuseStep 825599 = 1238399) B1238399
theorem B1239209 : Blo 487790 1239209 := bstep (se 2 (by rfl) ⟨464703, by rfl⟩ : syracuseStep 1239209 = 929407) B929407
theorem B8450045 : Blo 487790 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B487967 : Blo 487790 487967 := bstep (se 1 (by rfl) ⟨365975, by rfl⟩ : syracuseStep 487967 = 731951) B731951
theorem B826139 : Blo 487790 826139 := bstep (se 1 (by rfl) ⟨619604, by rfl⟩ : syracuseStep 826139 = 1239209) B1239209
theorem B520625477 : Blo 487790 520625477 := bstep (se 4 (by rfl) ⟨48808638, by rfl⟩ : syracuseStep 520625477 = 97617277) B97617277
theorem B53696303 : Blo 487790 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B942527 : Blo 487790 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B550399 : Blo 487790 550399 := bstep (se 1 (by rfl) ⟨412799, by rfl⟩ : syracuseStep 550399 = 825599) B825599
theorem B5633363 : Blo 487790 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B347083651 : Blo 487790 347083651 := bstep (se 1 (by rfl) ⟨260312738, by rfl⟩ : syracuseStep 347083651 = 520625477) B520625477
theorem B733865 : Blo 487790 733865 := bstep (se 2 (by rfl) ⟨275199, by rfl⟩ : syracuseStep 733865 = 550399) B550399
theorem B35797535 : Blo 487790 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B3755575 : Blo 487790 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B2513405 : Blo 487790 2513405 := bstep (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) B942527
theorem B550759 : Blo 487790 550759 := bstep (se 1 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 550759 = 826139) B826139
theorem B1675603 : Blo 487790 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B23865023 : Blo 487790 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B734345 : Blo 487790 734345 := bstep (se 2 (by rfl) ⟨275379, by rfl⟩ : syracuseStep 734345 = 550759) B550759
theorem B5007433 : Blo 487790 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B462778201 : Blo 487790 462778201 := bstep (se 2 (by rfl) ⟨173541825, by rfl⟩ : syracuseStep 462778201 = 347083651) B347083651
theorem B489243 : Blo 487790 489243 := bstep (se 1 (by rfl) ⟨366932, by rfl⟩ : syracuseStep 489243 = 733865) B733865
theorem B2234137 : Blo 487790 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B617037601 : Blo 487790 617037601 := bstep (se 2 (by rfl) ⟨231389100, by rfl⟩ : syracuseStep 617037601 = 462778201) B462778201
theorem B15910015 : Blo 487790 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B6676577 : Blo 487790 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B489563 : Blo 487790 489563 := bstep (se 1 (by rfl) ⟨367172, by rfl⟩ : syracuseStep 489563 = 734345) B734345
theorem B822716801 : Blo 487790 822716801 := bstep (se 2 (by rfl) ⟨308518800, by rfl⟩ : syracuseStep 822716801 = 617037601) B617037601
theorem B21213353 : Blo 487790 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B4451051 : Blo 487790 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B2978849 : Blo 487790 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B548477867 : Blo 487790 548477867 := bstep (se 1 (by rfl) ⟨411358400, by rfl⟩ : syracuseStep 548477867 = 822716801) B822716801
theorem B2967367 : Blo 487790 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B14142235 : Blo 487790 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B1985899 : Blo 487790 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B18856313 : Blo 487790 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B3956489 : Blo 487790 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B2647865 : Blo 487790 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B365651911 : Blo 487790 365651911 := bstep (se 1 (by rfl) ⟨274238933, by rfl⟩ : syracuseStep 365651911 = 548477867) B548477867
theorem B487535881 : Blo 487790 487535881 := bstep (se 2 (by rfl) ⟨182825955, by rfl⟩ : syracuseStep 487535881 = 365651911) B365651911
theorem B2637659 : Blo 487790 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B12570875 : Blo 487790 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B1765243 : Blo 487790 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B1758439 : Blo 487790 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B8380583 : Blo 487790 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B2353657 : Blo 487790 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B650047841 : Blo 487790 650047841 := bstep (se 2 (by rfl) ⟨243767940, by rfl⟩ : syracuseStep 650047841 = 487535881) B487535881
theorem B433365227 : Blo 487790 433365227 := bstep (se 1 (by rfl) ⟨325023920, by rfl⟩ : syracuseStep 433365227 = 650047841) B650047841
theorem B5587055 : Blo 487790 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B2344585 : Blo 487790 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B3138209 : Blo 487790 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B3126113 : Blo 487790 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B3724703 : Blo 487790 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B288910151 : Blo 487790 288910151 := bstep (se 1 (by rfl) ⟨216682613, by rfl⟩ : syracuseStep 288910151 = 433365227) B433365227
theorem B2092139 : Blo 487790 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B1394759 : Blo 487790 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B2084075 : Blo 487790 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B2483135 : Blo 487790 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B192606767 : Blo 487790 192606767 := bstep (se 1 (by rfl) ⟨144455075, by rfl⟩ : syracuseStep 192606767 = 288910151) B288910151
theorem B1389383 : Blo 487790 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B3719357 : Blo 487790 3719357 := bstep (se 3 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 3719357 = 1394759) B1394759
theorem B1655423 : Blo 487790 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B128404511 : Blo 487790 128404511 := bstep (se 1 (by rfl) ⟨96303383, by rfl⟩ : syracuseStep 128404511 = 192606767) B192606767
theorem B926255 : Blo 487790 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B85603007 : Blo 487790 85603007 := bstep (se 1 (by rfl) ⟨64202255, by rfl⟩ : syracuseStep 85603007 = 128404511) B128404511
theorem B2479571 : Blo 487790 2479571 := bstep (se 1 (by rfl) ⟨1859678, by rfl⟩ : syracuseStep 2479571 = 3719357) B3719357
theorem B1103615 : Blo 487790 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B2470013 : Blo 487790 2470013 := bstep (se 3 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 2470013 = 926255) B926255
theorem B1653047 : Blo 487790 1653047 := bstep (se 1 (by rfl) ⟨1239785, by rfl⟩ : syracuseStep 1653047 = 2479571) B2479571
theorem B735743 : Blo 487790 735743 := bstep (se 1 (by rfl) ⟨551807, by rfl⟩ : syracuseStep 735743 = 1103615) B1103615
theorem B57068671 : Blo 487790 57068671 := bstep (se 1 (by rfl) ⟨42801503, by rfl⟩ : syracuseStep 57068671 = 85603007) B85603007
theorem B76091561 : Blo 487790 76091561 := bstep (se 2 (by rfl) ⟨28534335, by rfl⟩ : syracuseStep 76091561 = 57068671) B57068671
theorem B1646675 : Blo 487790 1646675 := bstep (se 1 (by rfl) ⟨1235006, by rfl⟩ : syracuseStep 1646675 = 2470013) B2470013
theorem B1102031 : Blo 487790 1102031 := bstep (se 1 (by rfl) ⟨826523, by rfl⟩ : syracuseStep 1102031 = 1653047) B1653047
theorem B490495 : Blo 487790 490495 := bstep (se 1 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 490495 = 735743) B735743
theorem B50727707 : Blo 487790 50727707 := bstep (se 1 (by rfl) ⟨38045780, by rfl⟩ : syracuseStep 50727707 = 76091561) B76091561
theorem B734687 : Blo 487790 734687 := bstep (se 1 (by rfl) ⟨551015, by rfl⟩ : syracuseStep 734687 = 1102031) B1102031
theorem B1097783 : Blo 487790 1097783 := bstep (se 1 (by rfl) ⟨823337, by rfl⟩ : syracuseStep 1097783 = 1646675) B1646675
theorem B33818471 : Blo 487790 33818471 := bstep (se 1 (by rfl) ⟨25363853, by rfl⟩ : syracuseStep 33818471 = 50727707) B50727707
theorem B731855 : Blo 487790 731855 := bstep (se 1 (by rfl) ⟨548891, by rfl⟩ : syracuseStep 731855 = 1097783) B1097783
theorem B489791 : Blo 487790 489791 := bstep (se 1 (by rfl) ⟨367343, by rfl⟩ : syracuseStep 489791 = 734687) B734687
theorem B22545647 : Blo 487790 22545647 := bstep (se 1 (by rfl) ⟨16909235, by rfl⟩ : syracuseStep 22545647 = 33818471) B33818471
theorem B487903 : Blo 487790 487903 := bstep (se 1 (by rfl) ⟨365927, by rfl⟩ : syracuseStep 487903 = 731855) B731855
theorem B15030431 : Blo 487790 15030431 := bstep (se 1 (by rfl) ⟨11272823, by rfl⟩ : syracuseStep 15030431 = 22545647) B22545647
theorem B10020287 : Blo 487790 10020287 := bstep (se 1 (by rfl) ⟨7515215, by rfl⟩ : syracuseStep 10020287 = 15030431) B15030431
theorem B6680191 : Blo 487790 6680191 := bstep (se 1 (by rfl) ⟨5010143, by rfl⟩ : syracuseStep 6680191 = 10020287) B10020287
theorem B8906921 : Blo 487790 8906921 := bstep (se 2 (by rfl) ⟨3340095, by rfl⟩ : syracuseStep 8906921 = 6680191) B6680191
theorem B5937947 : Blo 487790 5937947 := bstep (se 1 (by rfl) ⟨4453460, by rfl⟩ : syracuseStep 5937947 = 8906921) B8906921
theorem B3958631 : Blo 487790 3958631 := bstep (se 1 (by rfl) ⟨2968973, by rfl⟩ : syracuseStep 3958631 = 5937947) B5937947
theorem B2639087 : Blo 487790 2639087 := bstep (se 1 (by rfl) ⟨1979315, by rfl⟩ : syracuseStep 2639087 = 3958631) B3958631
theorem B1759391 : Blo 487790 1759391 := bstep (se 1 (by rfl) ⟨1319543, by rfl⟩ : syracuseStep 1759391 = 2639087) B2639087
theorem B1172927 : Blo 487790 1172927 := bstep (se 1 (by rfl) ⟨879695, by rfl⟩ : syracuseStep 1172927 = 1759391) B1759391
theorem B3127805 : Blo 487790 3127805 := bstep (se 3 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 3127805 = 1172927) B1172927
theorem B2085203 : Blo 487790 2085203 := bstep (se 1 (by rfl) ⟨1563902, by rfl⟩ : syracuseStep 2085203 = 3127805) B3127805
theorem B1390135 : Blo 487790 1390135 := bstep (se 1 (by rfl) ⟨1042601, by rfl⟩ : syracuseStep 1390135 = 2085203) B2085203
theorem B1853513 : Blo 487790 1853513 := bstep (se 2 (by rfl) ⟨695067, by rfl⟩ : syracuseStep 1853513 = 1390135) B1390135
theorem B1235675 : Blo 487790 1235675 := bstep (se 1 (by rfl) ⟨926756, by rfl⟩ : syracuseStep 1235675 = 1853513) B1853513
theorem B823783 : Blo 487790 823783 := bstep (se 1 (by rfl) ⟨617837, by rfl⟩ : syracuseStep 823783 = 1235675) B1235675
theorem B1098377 : Blo 487790 1098377 := bstep (se 2 (by rfl) ⟨411891, by rfl⟩ : syracuseStep 1098377 = 823783) B823783
theorem B732251 : Blo 487790 732251 := bstep (se 1 (by rfl) ⟨549188, by rfl⟩ : syracuseStep 732251 = 1098377) B1098377
theorem B488167 : Blo 487790 488167 := bstep (se 1 (by rfl) ⟨366125, by rfl⟩ : syracuseStep 488167 = 732251) B732251

theorem C0 (j : ℕ) (h1 : 121947 ≤ j) (h2 : j ≤ 122646) : Blo 487790 (4 * j + 3) := by
  interval_cases j
  · exact B487791
  · exact B487795
  · exact B487799
  · exact B487803
  · exact B487807
  · exact B487811
  · exact B487815
  · exact B487819
  · exact B487823
  · exact B487827
  · exact B487831
  · exact B487835
  · exact B487839
  · exact B487843
  · exact B487847
  · exact B487851
  · exact B487855
  · exact B487859
  · exact B487863
  · exact B487867
  · exact B487871
  · exact B487875
  · exact B487879
  · exact B487883
  · exact B487887
  · exact B487891
  · exact B487895
  · exact B487899
  · exact B487903
  · exact B487907
  · exact B487911
  · exact B487915
  · exact B487919
  · exact B487923
  · exact B487927
  · exact B487931
  · exact B487935
  · exact B487939
  · exact B487943
  · exact B487947
  · exact B487951
  · exact B487955
  · exact B487959
  · exact B487963
  · exact B487967
  · exact B487971
  · exact B487975
  · exact B487979
  · exact B487983
  · exact B487987
  · exact B487991
  · exact B487995
  · exact B487999
  · exact B488003
  · exact B488007
  · exact B488011
  · exact B488015
  · exact B488019
  · exact B488023
  · exact B488027
  · exact B488031
  · exact B488035
  · exact B488039
  · exact B488043
  · exact B488047
  · exact B488051
  · exact B488055
  · exact B488059
  · exact B488063
  · exact B488067
  · exact B488071
  · exact B488075
  · exact B488079
  · exact B488083
  · exact B488087
  · exact B488091
  · exact B488095
  · exact B488099
  · exact B488103
  · exact B488107
  · exact B488111
  · exact B488115
  · exact B488119
  · exact B488123
  · exact B488127
  · exact B488131
  · exact B488135
  · exact B488139
  · exact B488143
  · exact B488147
  · exact B488151
  · exact B488155
  · exact B488159
  · exact B488163
  · exact B488167
  · exact B488171
  · exact B488175
  · exact B488179
  · exact B488183
  · exact B488187
  · exact B488191
  · exact B488195
  · exact B488199
  · exact B488203
  · exact B488207
  · exact B488211
  · exact B488215
  · exact B488219
  · exact B488223
  · exact B488227
  · exact B488231
  · exact B488235
  · exact B488239
  · exact B488243
  · exact B488247
  · exact B488251
  · exact B488255
  · exact B488259
  · exact B488263
  · exact B488267
  · exact B488271
  · exact B488275
  · exact B488279
  · exact B488283
  · exact B488287
  · exact B488291
  · exact B488295
  · exact B488299
  · exact B488303
  · exact B488307
  · exact B488311
  · exact B488315
  · exact B488319
  · exact B488323
  · exact B488327
  · exact B488331
  · exact B488335
  · exact B488339
  · exact B488343
  · exact B488347
  · exact B488351
  · exact B488355
  · exact B488359
  · exact B488363
  · exact B488367
  · exact B488371
  · exact B488375
  · exact B488379
  · exact B488383
  · exact B488387
  · exact B488391
  · exact B488395
  · exact B488399
  · exact B488403
  · exact B488407
  · exact B488411
  · exact B488415
  · exact B488419
  · exact B488423
  · exact B488427
  · exact B488431
  · exact B488435
  · exact B488439
  · exact B488443
  · exact B488447
  · exact B488451
  · exact B488455
  · exact B488459
  · exact B488463
  · exact B488467
  · exact B488471
  · exact B488475
  · exact B488479
  · exact B488483
  · exact B488487
  · exact B488491
  · exact B488495
  · exact B488499
  · exact B488503
  · exact B488507
  · exact B488511
  · exact B488515
  · exact B488519
  · exact B488523
  · exact B488527
  · exact B488531
  · exact B488535
  · exact B488539
  · exact B488543
  · exact B488547
  · exact B488551
  · exact B488555
  · exact B488559
  · exact B488563
  · exact B488567
  · exact B488571
  · exact B488575
  · exact B488579
  · exact B488583
  · exact B488587
  · exact B488591
  · exact B488595
  · exact B488599
  · exact B488603
  · exact B488607
  · exact B488611
  · exact B488615
  · exact B488619
  · exact B488623
  · exact B488627
  · exact B488631
  · exact B488635
  · exact B488639
  · exact B488643
  · exact B488647
  · exact B488651
  · exact B488655
  · exact B488659
  · exact B488663
  · exact B488667
  · exact B488671
  · exact B488675
  · exact B488679
  · exact B488683
  · exact B488687
  · exact B488691
  · exact B488695
  · exact B488699
  · exact B488703
  · exact B488707
  · exact B488711
  · exact B488715
  · exact B488719
  · exact B488723
  · exact B488727
  · exact B488731
  · exact B488735
  · exact B488739
  · exact B488743
  · exact B488747
  · exact B488751
  · exact B488755
  · exact B488759
  · exact B488763
  · exact B488767
  · exact B488771
  · exact B488775
  · exact B488779
  · exact B488783
  · exact B488787
  · exact B488791
  · exact B488795
  · exact B488799
  · exact B488803
  · exact B488807
  · exact B488811
  · exact B488815
  · exact B488819
  · exact B488823
  · exact B488827
  · exact B488831
  · exact B488835
  · exact B488839
  · exact B488843
  · exact B488847
  · exact B488851
  · exact B488855
  · exact B488859
  · exact B488863
  · exact B488867
  · exact B488871
  · exact B488875
  · exact B488879
  · exact B488883
  · exact B488887
  · exact B488891
  · exact B488895
  · exact B488899
  · exact B488903
  · exact B488907
  · exact B488911
  · exact B488915
  · exact B488919
  · exact B488923
  · exact B488927
  · exact B488931
  · exact B488935
  · exact B488939
  · exact B488943
  · exact B488947
  · exact B488951
  · exact B488955
  · exact B488959
  · exact B488963
  · exact B488967
  · exact B488971
  · exact B488975
  · exact B488979
  · exact B488983
  · exact B488987
  · exact B488991
  · exact B488995
  · exact B488999
  · exact B489003
  · exact B489007
  · exact B489011
  · exact B489015
  · exact B489019
  · exact B489023
  · exact B489027
  · exact B489031
  · exact B489035
  · exact B489039
  · exact B489043
  · exact B489047
  · exact B489051
  · exact B489055
  · exact B489059
  · exact B489063
  · exact B489067
  · exact B489071
  · exact B489075
  · exact B489079
  · exact B489083
  · exact B489087
  · exact B489091
  · exact B489095
  · exact B489099
  · exact B489103
  · exact B489107
  · exact B489111
  · exact B489115
  · exact B489119
  · exact B489123
  · exact B489127
  · exact B489131
  · exact B489135
  · exact B489139
  · exact B489143
  · exact B489147
  · exact B489151
  · exact B489155
  · exact B489159
  · exact B489163
  · exact B489167
  · exact B489171
  · exact B489175
  · exact B489179
  · exact B489183
  · exact B489187
  · exact B489191
  · exact B489195
  · exact B489199
  · exact B489203
  · exact B489207
  · exact B489211
  · exact B489215
  · exact B489219
  · exact B489223
  · exact B489227
  · exact B489231
  · exact B489235
  · exact B489239
  · exact B489243
  · exact B489247
  · exact B489251
  · exact B489255
  · exact B489259
  · exact B489263
  · exact B489267
  · exact B489271
  · exact B489275
  · exact B489279
  · exact B489283
  · exact B489287
  · exact B489291
  · exact B489295
  · exact B489299
  · exact B489303
  · exact B489307
  · exact B489311
  · exact B489315
  · exact B489319
  · exact B489323
  · exact B489327
  · exact B489331
  · exact B489335
  · exact B489339
  · exact B489343
  · exact B489347
  · exact B489351
  · exact B489355
  · exact B489359
  · exact B489363
  · exact B489367
  · exact B489371
  · exact B489375
  · exact B489379
  · exact B489383
  · exact B489387
  · exact B489391
  · exact B489395
  · exact B489399
  · exact B489403
  · exact B489407
  · exact B489411
  · exact B489415
  · exact B489419
  · exact B489423
  · exact B489427
  · exact B489431
  · exact B489435
  · exact B489439
  · exact B489443
  · exact B489447
  · exact B489451
  · exact B489455
  · exact B489459
  · exact B489463
  · exact B489467
  · exact B489471
  · exact B489475
  · exact B489479
  · exact B489483
  · exact B489487
  · exact B489491
  · exact B489495
  · exact B489499
  · exact B489503
  · exact B489507
  · exact B489511
  · exact B489515
  · exact B489519
  · exact B489523
  · exact B489527
  · exact B489531
  · exact B489535
  · exact B489539
  · exact B489543
  · exact B489547
  · exact B489551
  · exact B489555
  · exact B489559
  · exact B489563
  · exact B489567
  · exact B489571
  · exact B489575
  · exact B489579
  · exact B489583
  · exact B489587
  · exact B489591
  · exact B489595
  · exact B489599
  · exact B489603
  · exact B489607
  · exact B489611
  · exact B489615
  · exact B489619
  · exact B489623
  · exact B489627
  · exact B489631
  · exact B489635
  · exact B489639
  · exact B489643
  · exact B489647
  · exact B489651
  · exact B489655
  · exact B489659
  · exact B489663
  · exact B489667
  · exact B489671
  · exact B489675
  · exact B489679
  · exact B489683
  · exact B489687
  · exact B489691
  · exact B489695
  · exact B489699
  · exact B489703
  · exact B489707
  · exact B489711
  · exact B489715
  · exact B489719
  · exact B489723
  · exact B489727
  · exact B489731
  · exact B489735
  · exact B489739
  · exact B489743
  · exact B489747
  · exact B489751
  · exact B489755
  · exact B489759
  · exact B489763
  · exact B489767
  · exact B489771
  · exact B489775
  · exact B489779
  · exact B489783
  · exact B489787
  · exact B489791
  · exact B489795
  · exact B489799
  · exact B489803
  · exact B489807
  · exact B489811
  · exact B489815
  · exact B489819
  · exact B489823
  · exact B489827
  · exact B489831
  · exact B489835
  · exact B489839
  · exact B489843
  · exact B489847
  · exact B489851
  · exact B489855
  · exact B489859
  · exact B489863
  · exact B489867
  · exact B489871
  · exact B489875
  · exact B489879
  · exact B489883
  · exact B489887
  · exact B489891
  · exact B489895
  · exact B489899
  · exact B489903
  · exact B489907
  · exact B489911
  · exact B489915
  · exact B489919
  · exact B489923
  · exact B489927
  · exact B489931
  · exact B489935
  · exact B489939
  · exact B489943
  · exact B489947
  · exact B489951
  · exact B489955
  · exact B489959
  · exact B489963
  · exact B489967
  · exact B489971
  · exact B489975
  · exact B489979
  · exact B489983
  · exact B489987
  · exact B489991
  · exact B489995
  · exact B489999
  · exact B490003
  · exact B490007
  · exact B490011
  · exact B490015
  · exact B490019
  · exact B490023
  · exact B490027
  · exact B490031
  · exact B490035
  · exact B490039
  · exact B490043
  · exact B490047
  · exact B490051
  · exact B490055
  · exact B490059
  · exact B490063
  · exact B490067
  · exact B490071
  · exact B490075
  · exact B490079
  · exact B490083
  · exact B490087
  · exact B490091
  · exact B490095
  · exact B490099
  · exact B490103
  · exact B490107
  · exact B490111
  · exact B490115
  · exact B490119
  · exact B490123
  · exact B490127
  · exact B490131
  · exact B490135
  · exact B490139
  · exact B490143
  · exact B490147
  · exact B490151
  · exact B490155
  · exact B490159
  · exact B490163
  · exact B490167
  · exact B490171
  · exact B490175
  · exact B490179
  · exact B490183
  · exact B490187
  · exact B490191
  · exact B490195
  · exact B490199
  · exact B490203
  · exact B490207
  · exact B490211
  · exact B490215
  · exact B490219
  · exact B490223
  · exact B490227
  · exact B490231
  · exact B490235
  · exact B490239
  · exact B490243
  · exact B490247
  · exact B490251
  · exact B490255
  · exact B490259
  · exact B490263
  · exact B490267
  · exact B490271
  · exact B490275
  · exact B490279
  · exact B490283
  · exact B490287
  · exact B490291
  · exact B490295
  · exact B490299
  · exact B490303
  · exact B490307
  · exact B490311
  · exact B490315
  · exact B490319
  · exact B490323
  · exact B490327
  · exact B490331
  · exact B490335
  · exact B490339
  · exact B490343
  · exact B490347
  · exact B490351
  · exact B490355
  · exact B490359
  · exact B490363
  · exact B490367
  · exact B490371
  · exact B490375
  · exact B490379
  · exact B490383
  · exact B490387
  · exact B490391
  · exact B490395
  · exact B490399
  · exact B490403
  · exact B490407
  · exact B490411
  · exact B490415
  · exact B490419
  · exact B490423
  · exact B490427
  · exact B490431
  · exact B490435
  · exact B490439
  · exact B490443
  · exact B490447
  · exact B490451
  · exact B490455
  · exact B490459
  · exact B490463
  · exact B490467
  · exact B490471
  · exact B490475
  · exact B490479
  · exact B490483
  · exact B490487
  · exact B490491
  · exact B490495
  · exact B490499
  · exact B490503
  · exact B490507
  · exact B490511
  · exact B490515
  · exact B490519
  · exact B490523
  · exact B490527
  · exact B490531
  · exact B490535
  · exact B490539
  · exact B490543
  · exact B490547
  · exact B490551
  · exact B490555
  · exact B490559
  · exact B490563
  · exact B490567
  · exact B490571
  · exact B490575
  · exact B490579
  · exact B490583
  · exact B490587

theorem C1 (j : ℕ) (h1 : 122647 ≤ j) (h2 : j ≤ 122946) : Blo 487790 (4 * j + 3) := by
  interval_cases j
  · exact B490591
  · exact B490595
  · exact B490599
  · exact B490603
  · exact B490607
  · exact B490611
  · exact B490615
  · exact B490619
  · exact B490623
  · exact B490627
  · exact B490631
  · exact B490635
  · exact B490639
  · exact B490643
  · exact B490647
  · exact B490651
  · exact B490655
  · exact B490659
  · exact B490663
  · exact B490667
  · exact B490671
  · exact B490675
  · exact B490679
  · exact B490683
  · exact B490687
  · exact B490691
  · exact B490695
  · exact B490699
  · exact B490703
  · exact B490707
  · exact B490711
  · exact B490715
  · exact B490719
  · exact B490723
  · exact B490727
  · exact B490731
  · exact B490735
  · exact B490739
  · exact B490743
  · exact B490747
  · exact B490751
  · exact B490755
  · exact B490759
  · exact B490763
  · exact B490767
  · exact B490771
  · exact B490775
  · exact B490779
  · exact B490783
  · exact B490787
  · exact B490791
  · exact B490795
  · exact B490799
  · exact B490803
  · exact B490807
  · exact B490811
  · exact B490815
  · exact B490819
  · exact B490823
  · exact B490827
  · exact B490831
  · exact B490835
  · exact B490839
  · exact B490843
  · exact B490847
  · exact B490851
  · exact B490855
  · exact B490859
  · exact B490863
  · exact B490867
  · exact B490871
  · exact B490875
  · exact B490879
  · exact B490883
  · exact B490887
  · exact B490891
  · exact B490895
  · exact B490899
  · exact B490903
  · exact B490907
  · exact B490911
  · exact B490915
  · exact B490919
  · exact B490923
  · exact B490927
  · exact B490931
  · exact B490935
  · exact B490939
  · exact B490943
  · exact B490947
  · exact B490951
  · exact B490955
  · exact B490959
  · exact B490963
  · exact B490967
  · exact B490971
  · exact B490975
  · exact B490979
  · exact B490983
  · exact B490987
  · exact B490991
  · exact B490995
  · exact B490999
  · exact B491003
  · exact B491007
  · exact B491011
  · exact B491015
  · exact B491019
  · exact B491023
  · exact B491027
  · exact B491031
  · exact B491035
  · exact B491039
  · exact B491043
  · exact B491047
  · exact B491051
  · exact B491055
  · exact B491059
  · exact B491063
  · exact B491067
  · exact B491071
  · exact B491075
  · exact B491079
  · exact B491083
  · exact B491087
  · exact B491091
  · exact B491095
  · exact B491099
  · exact B491103
  · exact B491107
  · exact B491111
  · exact B491115
  · exact B491119
  · exact B491123
  · exact B491127
  · exact B491131
  · exact B491135
  · exact B491139
  · exact B491143
  · exact B491147
  · exact B491151
  · exact B491155
  · exact B491159
  · exact B491163
  · exact B491167
  · exact B491171
  · exact B491175
  · exact B491179
  · exact B491183
  · exact B491187
  · exact B491191
  · exact B491195
  · exact B491199
  · exact B491203
  · exact B491207
  · exact B491211
  · exact B491215
  · exact B491219
  · exact B491223
  · exact B491227
  · exact B491231
  · exact B491235
  · exact B491239
  · exact B491243
  · exact B491247
  · exact B491251
  · exact B491255
  · exact B491259
  · exact B491263
  · exact B491267
  · exact B491271
  · exact B491275
  · exact B491279
  · exact B491283
  · exact B491287
  · exact B491291
  · exact B491295
  · exact B491299
  · exact B491303
  · exact B491307
  · exact B491311
  · exact B491315
  · exact B491319
  · exact B491323
  · exact B491327
  · exact B491331
  · exact B491335
  · exact B491339
  · exact B491343
  · exact B491347
  · exact B491351
  · exact B491355
  · exact B491359
  · exact B491363
  · exact B491367
  · exact B491371
  · exact B491375
  · exact B491379
  · exact B491383
  · exact B491387
  · exact B491391
  · exact B491395
  · exact B491399
  · exact B491403
  · exact B491407
  · exact B491411
  · exact B491415
  · exact B491419
  · exact B491423
  · exact B491427
  · exact B491431
  · exact B491435
  · exact B491439
  · exact B491443
  · exact B491447
  · exact B491451
  · exact B491455
  · exact B491459
  · exact B491463
  · exact B491467
  · exact B491471
  · exact B491475
  · exact B491479
  · exact B491483
  · exact B491487
  · exact B491491
  · exact B491495
  · exact B491499
  · exact B491503
  · exact B491507
  · exact B491511
  · exact B491515
  · exact B491519
  · exact B491523
  · exact B491527
  · exact B491531
  · exact B491535
  · exact B491539
  · exact B491543
  · exact B491547
  · exact B491551
  · exact B491555
  · exact B491559
  · exact B491563
  · exact B491567
  · exact B491571
  · exact B491575
  · exact B491579
  · exact B491583
  · exact B491587
  · exact B491591
  · exact B491595
  · exact B491599
  · exact B491603
  · exact B491607
  · exact B491611
  · exact B491615
  · exact B491619
  · exact B491623
  · exact B491627
  · exact B491631
  · exact B491635
  · exact B491639
  · exact B491643
  · exact B491647
  · exact B491651
  · exact B491655
  · exact B491659
  · exact B491663
  · exact B491667
  · exact B491671
  · exact B491675
  · exact B491679
  · exact B491683
  · exact B491687
  · exact B491691
  · exact B491695
  · exact B491699
  · exact B491703
  · exact B491707
  · exact B491711
  · exact B491715
  · exact B491719
  · exact B491723
  · exact B491727
  · exact B491731
  · exact B491735
  · exact B491739
  · exact B491743
  · exact B491747
  · exact B491751
  · exact B491755
  · exact B491759
  · exact B491763
  · exact B491767
  · exact B491771
  · exact B491775
  · exact B491779
  · exact B491783
  · exact B491787

theorem solution (m : ℕ) (hlo : 487790 ≤ m) (hhi : m ≤ 491790) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 121947 ≤ j := by omega
    have hj2 : j ≤ 122946 := by omega
    have hb : Blo 487790 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 122647 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
