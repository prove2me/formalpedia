-- Prove2me | solution 1 for syracuse_descends_range_1108626_1112626
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:39.692383+00:00
-- url     : https://prove2.me/submissions/ab697b99-1cc7-4372-aa10-153076145941

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


theorem B1998901 : Blo 1108626 1998901 := bbase (se 5 (by rfl) ⟨93698, by rfl⟩ : syracuseStep 1998901 = 187397) (by norm_num)
theorem B1998989 : Blo 1108626 1998989 := bbase (se 3 (by rfl) ⟨374810, by rfl⟩ : syracuseStep 1998989 = 749621) (by norm_num)
theorem B8552789 : Blo 1108626 8552789 := bbase (se 10 (by rfl) ⟨12528, by rfl⟩ : syracuseStep 8552789 = 25057) (by norm_num)
theorem B1999421 : Blo 1108626 1999421 := bbase (se 3 (by rfl) ⟨374891, by rfl⟩ : syracuseStep 1999421 = 749783) (by norm_num)
theorem B4751941 : Blo 1108626 4751941 := bbase (se 4 (by rfl) ⟨445494, by rfl⟩ : syracuseStep 4751941 = 890989) (by norm_num)
theorem B9011893 : Blo 1108626 9011893 := bbase (se 5 (by rfl) ⟨422432, by rfl⟩ : syracuseStep 9011893 = 844865) (by norm_num)
theorem B1999709 : Blo 1108626 1999709 := bbase (se 3 (by rfl) ⟨374945, by rfl⟩ : syracuseStep 1999709 = 749891) (by norm_num)
theorem B10683413 : Blo 1108626 10683413 := bbase (se 6 (by rfl) ⟨250392, by rfl⟩ : syracuseStep 10683413 = 500785) (by norm_num)
theorem B58491989 : Blo 1108626 58491989 := bbase (se 8 (by rfl) ⟨342726, by rfl⟩ : syracuseStep 58491989 = 685453) (by norm_num)
theorem B6325397 : Blo 1108626 6325397 := bbase (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) (by norm_num)
theorem B1247233 : Blo 1108626 1247233 := bbase (se 2 (by rfl) ⟨467712, by rfl⟩ : syracuseStep 1247233 = 935425) (by norm_num)
theorem B1247269 : Blo 1108626 1247269 := bbase (se 4 (by rfl) ⟨116931, by rfl⟩ : syracuseStep 1247269 = 233863) (by norm_num)
theorem B1247305 : Blo 1108626 1247305 := bbase (se 2 (by rfl) ⟨467739, by rfl⟩ : syracuseStep 1247305 = 935479) (by norm_num)
theorem B1247341 : Blo 1108626 1247341 := bbase (se 3 (by rfl) ⟨233876, by rfl⟩ : syracuseStep 1247341 = 467753) (by norm_num)
theorem B1247377 : Blo 1108626 1247377 := bbase (se 2 (by rfl) ⟨467766, by rfl⟩ : syracuseStep 1247377 = 935533) (by norm_num)
theorem B1247413 : Blo 1108626 1247413 := bbase (se 5 (by rfl) ⟨58472, by rfl⟩ : syracuseStep 1247413 = 116945) (by norm_num)
theorem B1247449 : Blo 1108626 1247449 := bbase (se 2 (by rfl) ⟨467793, by rfl⟩ : syracuseStep 1247449 = 935587) (by norm_num)
theorem B1247485 : Blo 1108626 1247485 := bbase (se 3 (by rfl) ⟨233903, by rfl⟩ : syracuseStep 1247485 = 467807) (by norm_num)
theorem B1247521 : Blo 1108626 1247521 := bbase (se 2 (by rfl) ⟨467820, by rfl⟩ : syracuseStep 1247521 = 935641) (by norm_num)
theorem B1247557 : Blo 1108626 1247557 := bbase (se 4 (by rfl) ⟨116958, by rfl⟩ : syracuseStep 1247557 = 233917) (by norm_num)
theorem B1247593 : Blo 1108626 1247593 := bbase (se 2 (by rfl) ⟨467847, by rfl⟩ : syracuseStep 1247593 = 935695) (by norm_num)
theorem B1247629 : Blo 1108626 1247629 := bbase (se 3 (by rfl) ⟨233930, by rfl⟩ : syracuseStep 1247629 = 467861) (by norm_num)
theorem B1247665 : Blo 1108626 1247665 := bbase (se 2 (by rfl) ⟨467874, by rfl⟩ : syracuseStep 1247665 = 935749) (by norm_num)
theorem B2853317 : Blo 1108626 2853317 := bbase (se 4 (by rfl) ⟨267498, by rfl⟩ : syracuseStep 2853317 = 534997) (by norm_num)
theorem B1247701 : Blo 1108626 1247701 := bbase (se 7 (by rfl) ⟨14621, by rfl⟩ : syracuseStep 1247701 = 29243) (by norm_num)
theorem B1903061 : Blo 1108626 1903061 := bbase (se 7 (by rfl) ⟨22301, by rfl⟩ : syracuseStep 1903061 = 44603) (by norm_num)
theorem B1247737 : Blo 1108626 1247737 := bbase (se 2 (by rfl) ⟨467901, by rfl⟩ : syracuseStep 1247737 = 935803) (by norm_num)
theorem B1247773 : Blo 1108626 1247773 := bbase (se 3 (by rfl) ⟨233957, by rfl⟩ : syracuseStep 1247773 = 467915) (by norm_num)
theorem B1247809 : Blo 1108626 1247809 := bbase (se 2 (by rfl) ⟨467928, by rfl⟩ : syracuseStep 1247809 = 935857) (by norm_num)
theorem B1247845 : Blo 1108626 1247845 := bbase (se 4 (by rfl) ⟨116985, by rfl⟩ : syracuseStep 1247845 = 233971) (by norm_num)
theorem B1247881 : Blo 1108626 1247881 := bbase (se 2 (by rfl) ⟨467955, by rfl⟩ : syracuseStep 1247881 = 935911) (by norm_num)
theorem B1247917 : Blo 1108626 1247917 := bbase (se 3 (by rfl) ⟨233984, by rfl⟩ : syracuseStep 1247917 = 467969) (by norm_num)
theorem B1247953 : Blo 1108626 1247953 := bbase (se 2 (by rfl) ⟨467982, by rfl⟩ : syracuseStep 1247953 = 935965) (by norm_num)
theorem B1247989 : Blo 1108626 1247989 := bbase (se 5 (by rfl) ⟨58499, by rfl⟩ : syracuseStep 1247989 = 116999) (by norm_num)
theorem B1248025 : Blo 1108626 1248025 := bbase (se 2 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 1248025 = 936019) (by norm_num)
theorem B1248061 : Blo 1108626 1248061 := bbase (se 3 (by rfl) ⟨234011, by rfl⟩ : syracuseStep 1248061 = 468023) (by norm_num)
theorem B1248097 : Blo 1108626 1248097 := bbase (se 2 (by rfl) ⟨468036, by rfl⟩ : syracuseStep 1248097 = 936073) (by norm_num)
theorem B1248133 : Blo 1108626 1248133 := bbase (se 4 (by rfl) ⟨117012, by rfl⟩ : syracuseStep 1248133 = 234025) (by norm_num)
theorem B1248169 : Blo 1108626 1248169 := bbase (se 2 (by rfl) ⟨468063, by rfl⟩ : syracuseStep 1248169 = 936127) (by norm_num)
theorem B1248205 : Blo 1108626 1248205 := bbase (se 3 (by rfl) ⟨234038, by rfl⟩ : syracuseStep 1248205 = 468077) (by norm_num)
theorem B1248241 : Blo 1108626 1248241 := bbase (se 2 (by rfl) ⟨468090, by rfl⟩ : syracuseStep 1248241 = 936181) (by norm_num)
theorem B1248277 : Blo 1108626 1248277 := bbase (se 6 (by rfl) ⟨29256, by rfl⟩ : syracuseStep 1248277 = 58513) (by norm_num)
theorem B1870877 : Blo 1108626 1870877 := bbase (se 3 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 1870877 = 701579) (by norm_num)
theorem B1248313 : Blo 1108626 1248313 := bbase (se 2 (by rfl) ⟨468117, by rfl⟩ : syracuseStep 1248313 = 936235) (by norm_num)
theorem B1248349 : Blo 1108626 1248349 := bbase (se 3 (by rfl) ⟨234065, by rfl⟩ : syracuseStep 1248349 = 468131) (by norm_num)
theorem B1248385 : Blo 1108626 1248385 := bbase (se 2 (by rfl) ⟨468144, by rfl⟩ : syracuseStep 1248385 = 936289) (by norm_num)
theorem B1871005 : Blo 1108626 1871005 := bbase (se 3 (by rfl) ⟨350813, by rfl⟩ : syracuseStep 1871005 = 701627) (by norm_num)
theorem B1248421 : Blo 1108626 1248421 := bbase (se 4 (by rfl) ⟨117039, by rfl⟩ : syracuseStep 1248421 = 234079) (by norm_num)
theorem B5409989 : Blo 1108626 5409989 := bbase (se 4 (by rfl) ⟨507186, by rfl⟩ : syracuseStep 5409989 = 1014373) (by norm_num)
theorem B1248457 : Blo 1108626 1248457 := bbase (se 2 (by rfl) ⟨468171, by rfl⟩ : syracuseStep 1248457 = 936343) (by norm_num)
theorem B1248493 : Blo 1108626 1248493 := bbase (se 3 (by rfl) ⟨234092, by rfl⟩ : syracuseStep 1248493 = 468185) (by norm_num)
theorem B1871093 : Blo 1108626 1871093 := bbase (se 5 (by rfl) ⟨87707, by rfl⟩ : syracuseStep 1871093 = 175415) (by norm_num)
theorem B1248529 : Blo 1108626 1248529 := bbase (se 2 (by rfl) ⟨468198, by rfl⟩ : syracuseStep 1248529 = 936397) (by norm_num)
theorem B1248565 : Blo 1108626 1248565 := bbase (se 5 (by rfl) ⟨58526, by rfl⟩ : syracuseStep 1248565 = 117053) (by norm_num)
theorem B1248601 : Blo 1108626 1248601 := bbase (se 2 (by rfl) ⟨468225, by rfl⟩ : syracuseStep 1248601 = 936451) (by norm_num)
theorem B1871221 : Blo 1108626 1871221 := bbase (se 5 (by rfl) ⟨87713, by rfl⟩ : syracuseStep 1871221 = 175427) (by norm_num)
theorem B1248637 : Blo 1108626 1248637 := bbase (se 3 (by rfl) ⟨234119, by rfl⟩ : syracuseStep 1248637 = 468239) (by norm_num)
theorem B2002333 : Blo 1108626 2002333 := bbase (se 3 (by rfl) ⟨375437, by rfl⟩ : syracuseStep 2002333 = 750875) (by norm_num)
theorem B1248673 : Blo 1108626 1248673 := bbase (se 2 (by rfl) ⟨468252, by rfl⟩ : syracuseStep 1248673 = 936505) (by norm_num)
theorem B1248709 : Blo 1108626 1248709 := bbase (se 4 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 1248709 = 234133) (by norm_num)
theorem B1871309 : Blo 1108626 1871309 := bbase (se 3 (by rfl) ⟨350870, by rfl⟩ : syracuseStep 1871309 = 701741) (by norm_num)
theorem B1445333 : Blo 1108626 1445333 := bbase (se 7 (by rfl) ⟨16937, by rfl⟩ : syracuseStep 1445333 = 33875) (by norm_num)
theorem B1248745 : Blo 1108626 1248745 := bbase (se 2 (by rfl) ⟨468279, by rfl⟩ : syracuseStep 1248745 = 936559) (by norm_num)
theorem B7114229 : Blo 1108626 7114229 := bbase (se 5 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 7114229 = 666959) (by norm_num)
theorem B1248781 : Blo 1108626 1248781 := bbase (se 3 (by rfl) ⟨234146, by rfl⟩ : syracuseStep 1248781 = 468293) (by norm_num)
theorem B2002477 : Blo 1108626 2002477 := bbase (se 3 (by rfl) ⟨375464, by rfl⟩ : syracuseStep 2002477 = 750929) (by norm_num)
theorem B1248817 : Blo 1108626 1248817 := bbase (se 2 (by rfl) ⟨468306, by rfl⟩ : syracuseStep 1248817 = 936613) (by norm_num)
theorem B1871437 : Blo 1108626 1871437 := bbase (se 3 (by rfl) ⟨350894, by rfl⟩ : syracuseStep 1871437 = 701789) (by norm_num)
theorem B1248853 : Blo 1108626 1248853 := bbase (se 8 (by rfl) ⟨7317, by rfl⟩ : syracuseStep 1248853 = 14635) (by norm_num)
theorem B45649493 : Blo 1108626 45649493 := bbase (se 8 (by rfl) ⟨267477, by rfl⟩ : syracuseStep 45649493 = 534955) (by norm_num)
theorem B1248889 : Blo 1108626 1248889 := bbase (se 2 (by rfl) ⟨468333, by rfl⟩ : syracuseStep 1248889 = 936667) (by norm_num)
theorem B1248925 : Blo 1108626 1248925 := bbase (se 3 (by rfl) ⟨234173, by rfl⟩ : syracuseStep 1248925 = 468347) (by norm_num)
theorem B1805981 : Blo 1108626 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B1871525 : Blo 1108626 1871525 := bbase (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) (by norm_num)
theorem B1248961 : Blo 1108626 1248961 := bbase (se 2 (by rfl) ⟨468360, by rfl⟩ : syracuseStep 1248961 = 936721) (by norm_num)
theorem B1248997 : Blo 1108626 1248997 := bbase (se 4 (by rfl) ⟨117093, by rfl⟩ : syracuseStep 1248997 = 234187) (by norm_num)
theorem B1249033 : Blo 1108626 1249033 := bbase (se 2 (by rfl) ⟨468387, by rfl⟩ : syracuseStep 1249033 = 936775) (by norm_num)
theorem B1871653 : Blo 1108626 1871653 := bbase (se 4 (by rfl) ⟨175467, by rfl⟩ : syracuseStep 1871653 = 350935) (by norm_num)
theorem B1249069 : Blo 1108626 1249069 := bbase (se 3 (by rfl) ⟨234200, by rfl⟩ : syracuseStep 1249069 = 468401) (by norm_num)
theorem B1806149 : Blo 1108626 1806149 := bbase (se 4 (by rfl) ⟨169326, by rfl⟩ : syracuseStep 1806149 = 338653) (by norm_num)
theorem B1249105 : Blo 1108626 1249105 := bbase (se 2 (by rfl) ⟨468414, by rfl⟩ : syracuseStep 1249105 = 936829) (by norm_num)
theorem B1249141 : Blo 1108626 1249141 := bbase (se 5 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 1249141 = 117107) (by norm_num)
theorem B1871741 : Blo 1108626 1871741 := bbase (se 3 (by rfl) ⟨350951, by rfl⟩ : syracuseStep 1871741 = 701903) (by norm_num)
theorem B4001669 : Blo 1108626 4001669 := bbase (se 4 (by rfl) ⟨375156, by rfl⟩ : syracuseStep 4001669 = 750313) (by norm_num)
theorem B1249177 : Blo 1108626 1249177 := bbase (se 2 (by rfl) ⟨468441, by rfl⟩ : syracuseStep 1249177 = 936883) (by norm_num)
theorem B1249213 : Blo 1108626 1249213 := bbase (se 3 (by rfl) ⟨234227, by rfl⟩ : syracuseStep 1249213 = 468455) (by norm_num)
theorem B2494421 : Blo 1108626 2494421 := bbase (se 7 (by rfl) ⟨29231, by rfl⟩ : syracuseStep 2494421 = 58463) (by norm_num)
theorem B1249249 : Blo 1108626 1249249 := bbase (se 2 (by rfl) ⟨468468, by rfl⟩ : syracuseStep 1249249 = 936937) (by norm_num)
theorem B1871869 : Blo 1108626 1871869 := bbase (se 3 (by rfl) ⟨350975, by rfl⟩ : syracuseStep 1871869 = 701951) (by norm_num)
theorem B1249285 : Blo 1108626 1249285 := bbase (se 4 (by rfl) ⟨117120, by rfl⟩ : syracuseStep 1249285 = 234241) (by norm_num)
theorem B2494493 : Blo 1108626 2494493 := bbase (se 3 (by rfl) ⟨467717, by rfl⟩ : syracuseStep 2494493 = 935435) (by norm_num)
theorem B1249321 : Blo 1108626 1249321 := bbase (se 2 (by rfl) ⟨468495, by rfl⟩ : syracuseStep 1249321 = 936991) (by norm_num)
theorem B1249357 : Blo 1108626 1249357 := bbase (se 3 (by rfl) ⟨234254, by rfl⟩ : syracuseStep 1249357 = 468509) (by norm_num)
theorem B1871957 : Blo 1108626 1871957 := bbase (se 8 (by rfl) ⟨10968, by rfl⟩ : syracuseStep 1871957 = 21937) (by norm_num)
theorem B2494565 : Blo 1108626 2494565 := bbase (se 4 (by rfl) ⟨233865, by rfl⟩ : syracuseStep 2494565 = 467731) (by norm_num)
theorem B2003053 : Blo 1108626 2003053 := bbase (se 3 (by rfl) ⟨375572, by rfl⟩ : syracuseStep 2003053 = 751145) (by norm_num)
theorem B1249393 : Blo 1108626 1249393 := bbase (se 2 (by rfl) ⟨468522, by rfl⟩ : syracuseStep 1249393 = 937045) (by norm_num)
theorem B1216657 : Blo 1108626 1216657 := bbase (se 2 (by rfl) ⟨456246, by rfl⟩ : syracuseStep 1216657 = 912493) (by norm_num)
theorem B1249429 : Blo 1108626 1249429 := bbase (se 6 (by rfl) ⟨29283, by rfl⟩ : syracuseStep 1249429 = 58567) (by norm_num)
theorem B2494637 : Blo 1108626 2494637 := bbase (se 3 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 2494637 = 935489) (by norm_num)
theorem B1249465 : Blo 1108626 1249465 := bbase (se 2 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 1249465 = 937099) (by norm_num)
theorem B1872085 : Blo 1108626 1872085 := bbase (se 7 (by rfl) ⟨21938, by rfl⟩ : syracuseStep 1872085 = 43877) (by norm_num)
theorem B1249501 : Blo 1108626 1249501 := bbase (se 3 (by rfl) ⟨234281, by rfl⟩ : syracuseStep 1249501 = 468563) (by norm_num)
theorem B2494709 : Blo 1108626 2494709 := bbase (se 5 (by rfl) ⟨116939, by rfl⟩ : syracuseStep 2494709 = 233879) (by norm_num)
theorem B1249537 : Blo 1108626 1249537 := bbase (se 2 (by rfl) ⟨468576, by rfl⟩ : syracuseStep 1249537 = 937153) (by norm_num)
theorem B1249573 : Blo 1108626 1249573 := bbase (se 4 (by rfl) ⟨117147, by rfl⟩ : syracuseStep 1249573 = 234295) (by norm_num)
theorem B1872173 : Blo 1108626 1872173 := bbase (se 3 (by rfl) ⟨351032, by rfl⟩ : syracuseStep 1872173 = 702065) (by norm_num)
theorem B8425781 : Blo 1108626 8425781 := bbase (se 5 (by rfl) ⟨394958, by rfl⟩ : syracuseStep 8425781 = 789917) (by norm_num)
theorem B2494781 : Blo 1108626 2494781 := bbase (se 3 (by rfl) ⟨467771, by rfl⟩ : syracuseStep 2494781 = 935543) (by norm_num)
theorem B1249609 : Blo 1108626 1249609 := bbase (se 2 (by rfl) ⟨468603, by rfl⟩ : syracuseStep 1249609 = 937207) (by norm_num)
theorem B1249645 : Blo 1108626 1249645 := bbase (se 3 (by rfl) ⟨234308, by rfl⟩ : syracuseStep 1249645 = 468617) (by norm_num)
theorem B2494853 : Blo 1108626 2494853 := bbase (se 4 (by rfl) ⟨233892, by rfl⟩ : syracuseStep 2494853 = 467785) (by norm_num)
theorem B1249681 : Blo 1108626 1249681 := bbase (se 2 (by rfl) ⟨468630, by rfl⟩ : syracuseStep 1249681 = 937261) (by norm_num)
theorem B1872301 : Blo 1108626 1872301 := bbase (se 3 (by rfl) ⟨351056, by rfl⟩ : syracuseStep 1872301 = 702113) (by norm_num)
theorem B1249717 : Blo 1108626 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B2494925 : Blo 1108626 2494925 := bbase (se 3 (by rfl) ⟨467798, by rfl⟩ : syracuseStep 2494925 = 935597) (by norm_num)
theorem B1249753 : Blo 1108626 1249753 := bbase (se 2 (by rfl) ⟨468657, by rfl⟩ : syracuseStep 1249753 = 937315) (by norm_num)
theorem B2003429 : Blo 1108626 2003429 := bbase (se 4 (by rfl) ⟨187821, by rfl⟩ : syracuseStep 2003429 = 375643) (by norm_num)
theorem B2888173 : Blo 1108626 2888173 := bbase (se 3 (by rfl) ⟨541532, by rfl⟩ : syracuseStep 2888173 = 1083065) (by norm_num)
theorem B1249789 : Blo 1108626 1249789 := bbase (se 3 (by rfl) ⟨234335, by rfl⟩ : syracuseStep 1249789 = 468671) (by norm_num)
theorem B1184257 : Blo 1108626 1184257 := bbase (se 2 (by rfl) ⟨444096, by rfl⟩ : syracuseStep 1184257 = 888193) (by norm_num)
theorem B1872389 : Blo 1108626 1872389 := bbase (se 4 (by rfl) ⟨175536, by rfl⟩ : syracuseStep 1872389 = 351073) (by norm_num)
theorem B2494997 : Blo 1108626 2494997 := bbase (se 6 (by rfl) ⟨58476, by rfl⟩ : syracuseStep 2494997 = 116953) (by norm_num)
theorem B1249825 : Blo 1108626 1249825 := bbase (se 2 (by rfl) ⟨468684, by rfl⟩ : syracuseStep 1249825 = 937369) (by norm_num)
theorem B3379765 : Blo 1108626 3379765 := bbase (se 5 (by rfl) ⟨158426, by rfl⟩ : syracuseStep 3379765 = 316853) (by norm_num)
theorem B1249861 : Blo 1108626 1249861 := bbase (se 4 (by rfl) ⟨117174, by rfl⟩ : syracuseStep 1249861 = 234349) (by norm_num)
theorem B1184329 : Blo 1108626 1184329 := bbase (se 2 (by rfl) ⟨444123, by rfl⟩ : syracuseStep 1184329 = 888247) (by norm_num)
theorem B2495069 : Blo 1108626 2495069 := bbase (se 3 (by rfl) ⟨467825, by rfl⟩ : syracuseStep 2495069 = 935651) (by norm_num)
theorem B1249897 : Blo 1108626 1249897 := bbase (se 2 (by rfl) ⟨468711, by rfl⟩ : syracuseStep 1249897 = 937423) (by norm_num)
theorem B1872517 : Blo 1108626 1872517 := bbase (se 4 (by rfl) ⟨175548, by rfl⟩ : syracuseStep 1872517 = 351097) (by norm_num)
theorem B1249933 : Blo 1108626 1249933 := bbase (se 3 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 1249933 = 468725) (by norm_num)
theorem B2495141 : Blo 1108626 2495141 := bbase (se 4 (by rfl) ⟨233919, by rfl⟩ : syracuseStep 2495141 = 467839) (by norm_num)
theorem B1249969 : Blo 1108626 1249969 := bbase (se 2 (by rfl) ⟨468738, by rfl⟩ : syracuseStep 1249969 = 937477) (by norm_num)
theorem B1250005 : Blo 1108626 1250005 := bbase (se 7 (by rfl) ⟨14648, by rfl⟩ : syracuseStep 1250005 = 29297) (by norm_num)
theorem B1872605 : Blo 1108626 1872605 := bbase (se 3 (by rfl) ⟨351113, by rfl⟩ : syracuseStep 1872605 = 702227) (by norm_num)
theorem B4002533 : Blo 1108626 4002533 := bbase (se 4 (by rfl) ⟨375237, by rfl⟩ : syracuseStep 4002533 = 750475) (by norm_num)
theorem B2495213 : Blo 1108626 2495213 := bbase (se 3 (by rfl) ⟨467852, by rfl⟩ : syracuseStep 2495213 = 935705) (by norm_num)
theorem B1250041 : Blo 1108626 1250041 := bbase (se 2 (by rfl) ⟨468765, by rfl⟩ : syracuseStep 1250041 = 937531) (by norm_num)
theorem B2003717 : Blo 1108626 2003717 := bbase (se 4 (by rfl) ⟨187848, by rfl⟩ : syracuseStep 2003717 = 375697) (by norm_num)
theorem B1250077 : Blo 1108626 1250077 := bbase (se 3 (by rfl) ⟨234389, by rfl⟩ : syracuseStep 1250077 = 468779) (by norm_num)
theorem B2495285 : Blo 1108626 2495285 := bbase (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) (by norm_num)
theorem B1250113 : Blo 1108626 1250113 := bbase (se 2 (by rfl) ⟨468792, by rfl⟩ : syracuseStep 1250113 = 937585) (by norm_num)
theorem B28840789 : Blo 1108626 28840789 := bbase (se 9 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 28840789 = 168989) (by norm_num)
theorem B1872733 : Blo 1108626 1872733 := bbase (se 3 (by rfl) ⟨351137, by rfl⟩ : syracuseStep 1872733 = 702275) (by norm_num)
theorem B1250149 : Blo 1108626 1250149 := bbase (se 4 (by rfl) ⟨117201, by rfl⟩ : syracuseStep 1250149 = 234403) (by norm_num)
theorem B2495357 : Blo 1108626 2495357 := bbase (se 3 (by rfl) ⟨467879, by rfl⟩ : syracuseStep 2495357 = 935759) (by norm_num)
theorem B1250185 : Blo 1108626 1250185 := bbase (se 2 (by rfl) ⟨468819, by rfl⟩ : syracuseStep 1250185 = 937639) (by norm_num)
theorem B2003861 : Blo 1108626 2003861 := bbase (se 6 (by rfl) ⟨46965, by rfl⟩ : syracuseStep 2003861 = 93931) (by norm_num)
theorem B1250221 : Blo 1108626 1250221 := bbase (se 3 (by rfl) ⟨234416, by rfl⟩ : syracuseStep 1250221 = 468833) (by norm_num)
theorem B1872821 : Blo 1108626 1872821 := bbase (se 5 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 1872821 = 175577) (by norm_num)
theorem B1184701 : Blo 1108626 1184701 := bbase (se 3 (by rfl) ⟨222131, by rfl⟩ : syracuseStep 1184701 = 444263) (by norm_num)
theorem B2495429 : Blo 1108626 2495429 := bbase (se 4 (by rfl) ⟨233946, by rfl⟩ : syracuseStep 2495429 = 467893) (by norm_num)
theorem B1250257 : Blo 1108626 1250257 := bbase (se 2 (by rfl) ⟨468846, by rfl⟩ : syracuseStep 1250257 = 937693) (by norm_num)
theorem B3085285 : Blo 1108626 3085285 := bbase (se 4 (by rfl) ⟨289245, by rfl⟩ : syracuseStep 3085285 = 578491) (by norm_num)
theorem B1250293 : Blo 1108626 1250293 := bbase (se 5 (by rfl) ⟨58607, by rfl⟩ : syracuseStep 1250293 = 117215) (by norm_num)
theorem B4002821 : Blo 1108626 4002821 := bbase (se 4 (by rfl) ⟨375264, by rfl⟩ : syracuseStep 4002821 = 750529) (by norm_num)
theorem B2495501 : Blo 1108626 2495501 := bbase (se 3 (by rfl) ⟨467906, by rfl⟩ : syracuseStep 2495501 = 935813) (by norm_num)
theorem B1250329 : Blo 1108626 1250329 := bbase (se 2 (by rfl) ⟨468873, by rfl⟩ : syracuseStep 1250329 = 937747) (by norm_num)
theorem B1872949 : Blo 1108626 1872949 := bbase (se 5 (by rfl) ⟨87794, by rfl⟩ : syracuseStep 1872949 = 175589) (by norm_num)
theorem B1250365 : Blo 1108626 1250365 := bbase (se 3 (by rfl) ⟨234443, by rfl⟩ : syracuseStep 1250365 = 468887) (by norm_num)
theorem B2495573 : Blo 1108626 2495573 := bbase (se 8 (by rfl) ⟨14622, by rfl⟩ : syracuseStep 2495573 = 29245) (by norm_num)
theorem B1250401 : Blo 1108626 1250401 := bbase (se 2 (by rfl) ⟨468900, by rfl⟩ : syracuseStep 1250401 = 937801) (by norm_num)
theorem B1250437 : Blo 1108626 1250437 := bbase (se 4 (by rfl) ⟨117228, by rfl⟩ : syracuseStep 1250437 = 234457) (by norm_num)
theorem B1873037 : Blo 1108626 1873037 := bbase (se 3 (by rfl) ⟨351194, by rfl⟩ : syracuseStep 1873037 = 702389) (by norm_num)
theorem B2495645 : Blo 1108626 2495645 := bbase (se 3 (by rfl) ⟨467933, by rfl⟩ : syracuseStep 2495645 = 935867) (by norm_num)
theorem B1250473 : Blo 1108626 1250473 := bbase (se 2 (by rfl) ⟨468927, by rfl⟩ : syracuseStep 1250473 = 937855) (by norm_num)
theorem B1250509 : Blo 1108626 1250509 := bbase (se 3 (by rfl) ⟨234470, by rfl⟩ : syracuseStep 1250509 = 468941) (by norm_num)
theorem B2495717 : Blo 1108626 2495717 := bbase (se 4 (by rfl) ⟨233973, by rfl⟩ : syracuseStep 2495717 = 467947) (by norm_num)
theorem B1250545 : Blo 1108626 1250545 := bbase (se 2 (by rfl) ⟨468954, by rfl⟩ : syracuseStep 1250545 = 937909) (by norm_num)
theorem B1873165 : Blo 1108626 1873165 := bbase (se 3 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 1873165 = 702437) (by norm_num)
theorem B1250581 : Blo 1108626 1250581 := bbase (se 6 (by rfl) ⟨29310, by rfl⟩ : syracuseStep 1250581 = 58621) (by norm_num)
theorem B2495789 : Blo 1108626 2495789 := bbase (se 3 (by rfl) ⟨467960, by rfl⟩ : syracuseStep 2495789 = 935921) (by norm_num)
theorem B1185077 : Blo 1108626 1185077 := bbase (se 5 (by rfl) ⟨55550, by rfl⟩ : syracuseStep 1185077 = 111101) (by norm_num)
theorem B1250617 : Blo 1108626 1250617 := bbase (se 2 (by rfl) ⟨468981, by rfl⟩ : syracuseStep 1250617 = 937963) (by norm_num)
theorem B1250653 : Blo 1108626 1250653 := bbase (se 3 (by rfl) ⟨234497, by rfl⟩ : syracuseStep 1250653 = 468995) (by norm_num)
theorem B1873253 : Blo 1108626 1873253 := bbase (se 4 (by rfl) ⟨175617, by rfl⟩ : syracuseStep 1873253 = 351235) (by norm_num)
theorem B2495861 : Blo 1108626 2495861 := bbase (se 5 (by rfl) ⟨116993, by rfl⟩ : syracuseStep 2495861 = 233987) (by norm_num)
theorem B1185149 : Blo 1108626 1185149 := bbase (se 3 (by rfl) ⟨222215, by rfl⟩ : syracuseStep 1185149 = 444431) (by norm_num)
theorem B1250689 : Blo 1108626 1250689 := bbase (se 2 (by rfl) ⟨469008, by rfl⟩ : syracuseStep 1250689 = 938017) (by norm_num)
theorem B1250725 : Blo 1108626 1250725 := bbase (se 4 (by rfl) ⟨117255, by rfl⟩ : syracuseStep 1250725 = 234511) (by norm_num)
theorem B4003253 : Blo 1108626 4003253 := bbase (se 5 (by rfl) ⟨187652, by rfl⟩ : syracuseStep 4003253 = 375305) (by norm_num)
theorem B2495933 : Blo 1108626 2495933 := bbase (se 3 (by rfl) ⟨467987, by rfl⟩ : syracuseStep 2495933 = 935975) (by norm_num)
theorem B1250761 : Blo 1108626 1250761 := bbase (se 2 (by rfl) ⟨469035, by rfl⟩ : syracuseStep 1250761 = 938071) (by norm_num)
theorem B2004437 : Blo 1108626 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B1873381 : Blo 1108626 1873381 := bbase (se 4 (by rfl) ⟨175629, by rfl⟩ : syracuseStep 1873381 = 351259) (by norm_num)
theorem B1250797 : Blo 1108626 1250797 := bbase (se 3 (by rfl) ⟨234524, by rfl⟩ : syracuseStep 1250797 = 469049) (by norm_num)
theorem B2496005 : Blo 1108626 2496005 := bbase (se 4 (by rfl) ⟨234000, by rfl⟩ : syracuseStep 2496005 = 468001) (by norm_num)
theorem B1250833 : Blo 1108626 1250833 := bbase (se 2 (by rfl) ⟨469062, by rfl⟩ : syracuseStep 1250833 = 938125) (by norm_num)
theorem B1250869 : Blo 1108626 1250869 := bbase (se 5 (by rfl) ⟨58634, by rfl⟩ : syracuseStep 1250869 = 117269) (by norm_num)
theorem B1185337 : Blo 1108626 1185337 := bbase (se 2 (by rfl) ⟨444501, by rfl⟩ : syracuseStep 1185337 = 889003) (by norm_num)
theorem B1873469 : Blo 1108626 1873469 := bbase (se 3 (by rfl) ⟨351275, by rfl⟩ : syracuseStep 1873469 = 702551) (by norm_num)
theorem B2496077 : Blo 1108626 2496077 := bbase (se 3 (by rfl) ⟨468014, by rfl⟩ : syracuseStep 2496077 = 936029) (by norm_num)
theorem B1250905 : Blo 1108626 1250905 := bbase (se 2 (by rfl) ⟨469089, by rfl⟩ : syracuseStep 1250905 = 938179) (by norm_num)
theorem B1250941 : Blo 1108626 1250941 := bbase (se 3 (by rfl) ⟨234551, by rfl⟩ : syracuseStep 1250941 = 469103) (by norm_num)
theorem B2496149 : Blo 1108626 2496149 := bbase (se 6 (by rfl) ⟨58503, by rfl⟩ : syracuseStep 2496149 = 117007) (by norm_num)
theorem B1250977 : Blo 1108626 1250977 := bbase (se 2 (by rfl) ⟨469116, by rfl⟩ : syracuseStep 1250977 = 938233) (by norm_num)
theorem B1873597 : Blo 1108626 1873597 := bbase (se 3 (by rfl) ⟨351299, by rfl⟩ : syracuseStep 1873597 = 702599) (by norm_num)
theorem B1251013 : Blo 1108626 1251013 := bbase (se 4 (by rfl) ⟨117282, by rfl⟩ : syracuseStep 1251013 = 234565) (by norm_num)
theorem B2496221 : Blo 1108626 2496221 := bbase (se 3 (by rfl) ⟨468041, by rfl⟩ : syracuseStep 2496221 = 936083) (by norm_num)
theorem B1251049 : Blo 1108626 1251049 := bbase (se 2 (by rfl) ⟨469143, by rfl⟩ : syracuseStep 1251049 = 938287) (by norm_num)
theorem B1185521 : Blo 1108626 1185521 := bbase (se 2 (by rfl) ⟨444570, by rfl⟩ : syracuseStep 1185521 = 889141) (by norm_num)
theorem B1251085 : Blo 1108626 1251085 := bbase (se 3 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 1251085 = 469157) (by norm_num)
theorem B1873685 : Blo 1108626 1873685 := bbase (se 6 (by rfl) ⟨43914, by rfl⟩ : syracuseStep 1873685 = 87829) (by norm_num)
theorem B1578781 : Blo 1108626 1578781 := bbase (se 3 (by rfl) ⟨296021, by rfl⟩ : syracuseStep 1578781 = 592043) (by norm_num)
theorem B2496293 : Blo 1108626 2496293 := bbase (se 4 (by rfl) ⟨234027, by rfl⟩ : syracuseStep 2496293 = 468055) (by norm_num)
theorem B1251121 : Blo 1108626 1251121 := bbase (se 2 (by rfl) ⟨469170, by rfl⟩ : syracuseStep 1251121 = 938341) (by norm_num)
theorem B4331317 : Blo 1108626 4331317 := bbase (se 5 (by rfl) ⟨203030, by rfl⟩ : syracuseStep 4331317 = 406061) (by norm_num)
theorem B1251157 : Blo 1108626 1251157 := bbase (se 9 (by rfl) ⟨3665, by rfl⟩ : syracuseStep 1251157 = 7331) (by norm_num)
theorem B2496365 : Blo 1108626 2496365 := bbase (se 3 (by rfl) ⟨468068, by rfl⟩ : syracuseStep 2496365 = 936137) (by norm_num)
theorem B1251193 : Blo 1108626 1251193 := bbase (se 2 (by rfl) ⟨469197, by rfl⟩ : syracuseStep 1251193 = 938395) (by norm_num)
theorem B1873813 : Blo 1108626 1873813 := bbase (se 6 (by rfl) ⟨43917, by rfl⟩ : syracuseStep 1873813 = 87835) (by norm_num)
theorem B1251229 : Blo 1108626 1251229 := bbase (se 3 (by rfl) ⟨234605, by rfl⟩ : syracuseStep 1251229 = 469211) (by norm_num)
theorem B2496437 : Blo 1108626 2496437 := bbase (se 5 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 2496437 = 234041) (by norm_num)
theorem B1251265 : Blo 1108626 1251265 := bbase (se 2 (by rfl) ⟨469224, by rfl⟩ : syracuseStep 1251265 = 938449) (by norm_num)
theorem B1251301 : Blo 1108626 1251301 := bbase (se 4 (by rfl) ⟨117309, by rfl⟩ : syracuseStep 1251301 = 234619) (by norm_num)
theorem B1873901 : Blo 1108626 1873901 := bbase (se 3 (by rfl) ⟨351356, by rfl⟩ : syracuseStep 1873901 = 702713) (by norm_num)
theorem B2496509 : Blo 1108626 2496509 := bbase (se 3 (by rfl) ⟨468095, by rfl⟩ : syracuseStep 2496509 = 936191) (by norm_num)
theorem B1251337 : Blo 1108626 1251337 := bbase (se 2 (by rfl) ⟨469251, by rfl⟩ : syracuseStep 1251337 = 938503) (by norm_num)
theorem B1251373 : Blo 1108626 1251373 := bbase (se 3 (by rfl) ⟨234632, by rfl⟩ : syracuseStep 1251373 = 469265) (by norm_num)
theorem B2529349 : Blo 1108626 2529349 := bbase (se 4 (by rfl) ⟨237126, by rfl⟩ : syracuseStep 2529349 = 474253) (by norm_num)
theorem B2496581 : Blo 1108626 2496581 := bbase (se 4 (by rfl) ⟨234054, by rfl⟩ : syracuseStep 2496581 = 468109) (by norm_num)
theorem B1251409 : Blo 1108626 1251409 := bbase (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) (by norm_num)
theorem B1579117 : Blo 1108626 1579117 := bbase (se 3 (by rfl) ⟨296084, by rfl⟩ : syracuseStep 1579117 = 592169) (by norm_num)
theorem B1874029 : Blo 1108626 1874029 := bbase (se 3 (by rfl) ⟨351380, by rfl⟩ : syracuseStep 1874029 = 702761) (by norm_num)
theorem B1251445 : Blo 1108626 1251445 := bbase (se 5 (by rfl) ⟨58661, by rfl⟩ : syracuseStep 1251445 = 117323) (by norm_num)
theorem B2496653 : Blo 1108626 2496653 := bbase (se 3 (by rfl) ⟨468122, by rfl⟩ : syracuseStep 2496653 = 936245) (by norm_num)
theorem B1251481 : Blo 1108626 1251481 := bbase (se 2 (by rfl) ⟨469305, by rfl⟩ : syracuseStep 1251481 = 938611) (by norm_num)
theorem B1251517 : Blo 1108626 1251517 := bbase (se 3 (by rfl) ⟨234659, by rfl⟩ : syracuseStep 1251517 = 469319) (by norm_num)
theorem B1874117 : Blo 1108626 1874117 := bbase (se 4 (by rfl) ⟨175698, by rfl⟩ : syracuseStep 1874117 = 351397) (by norm_num)
theorem B2496725 : Blo 1108626 2496725 := bbase (se 7 (by rfl) ⟨29258, by rfl⟩ : syracuseStep 2496725 = 58517) (by norm_num)
theorem B1251553 : Blo 1108626 1251553 := bbase (se 2 (by rfl) ⟨469332, by rfl⟩ : syracuseStep 1251553 = 938665) (by norm_num)
theorem B1251589 : Blo 1108626 1251589 := bbase (se 4 (by rfl) ⟨117336, by rfl⟩ : syracuseStep 1251589 = 234673) (by norm_num)
theorem B2496797 : Blo 1108626 2496797 := bbase (se 3 (by rfl) ⟨468149, by rfl⟩ : syracuseStep 2496797 = 936299) (by norm_num)
theorem B1251625 : Blo 1108626 1251625 := bbase (se 2 (by rfl) ⟨469359, by rfl⟩ : syracuseStep 1251625 = 938719) (by norm_num)
theorem B1579333 : Blo 1108626 1579333 := bbase (se 4 (by rfl) ⟨148062, by rfl⟩ : syracuseStep 1579333 = 296125) (by norm_num)
theorem B1874245 : Blo 1108626 1874245 := bbase (se 4 (by rfl) ⟨175710, by rfl⟩ : syracuseStep 1874245 = 351421) (by norm_num)
theorem B1251661 : Blo 1108626 1251661 := bbase (se 3 (by rfl) ⟨234686, by rfl⟩ : syracuseStep 1251661 = 469373) (by norm_num)
theorem B3742037 : Blo 1108626 3742037 := bbase (se 10 (by rfl) ⟨5481, by rfl⟩ : syracuseStep 3742037 = 10963) (by norm_num)
theorem B2496869 : Blo 1108626 2496869 := bbase (se 4 (by rfl) ⟨234081, by rfl⟩ : syracuseStep 2496869 = 468163) (by norm_num)
theorem B1251697 : Blo 1108626 1251697 := bbase (se 2 (by rfl) ⟨469386, by rfl⟩ : syracuseStep 1251697 = 938773) (by norm_num)
theorem B1874333 : Blo 1108626 1874333 := bbase (se 3 (by rfl) ⟨351437, by rfl⟩ : syracuseStep 1874333 = 702875) (by norm_num)
theorem B2496941 : Blo 1108626 2496941 := bbase (se 3 (by rfl) ⟨468176, by rfl⟩ : syracuseStep 2496941 = 936353) (by norm_num)
theorem B1710533 : Blo 1108626 1710533 := bbase (se 4 (by rfl) ⟨160362, by rfl⟩ : syracuseStep 1710533 = 320725) (by norm_num)
theorem B1186273 : Blo 1108626 1186273 := bbase (se 2 (by rfl) ⟨444852, by rfl⟩ : syracuseStep 1186273 = 889705) (by norm_num)
theorem B2497013 : Blo 1108626 2497013 := bbase (se 5 (by rfl) ⟨117047, by rfl⟩ : syracuseStep 2497013 = 234095) (by norm_num)
theorem B1874461 : Blo 1108626 1874461 := bbase (se 3 (by rfl) ⟨351461, by rfl⟩ : syracuseStep 1874461 = 702923) (by norm_num)
theorem B1186345 : Blo 1108626 1186345 := bbase (se 2 (by rfl) ⟨444879, by rfl⟩ : syracuseStep 1186345 = 889759) (by norm_num)
theorem B2497085 : Blo 1108626 2497085 := bbase (se 3 (by rfl) ⟨468203, by rfl⟩ : syracuseStep 2497085 = 936407) (by norm_num)
theorem B1874549 : Blo 1108626 1874549 := bbase (se 5 (by rfl) ⟨87869, by rfl⟩ : syracuseStep 1874549 = 175739) (by norm_num)
theorem B2497157 : Blo 1108626 2497157 := bbase (se 4 (by rfl) ⟨234108, by rfl⟩ : syracuseStep 2497157 = 468217) (by norm_num)
theorem B1579709 : Blo 1108626 1579709 := bbase (se 3 (by rfl) ⟨296195, by rfl⟩ : syracuseStep 1579709 = 592391) (by norm_num)
theorem B2497229 : Blo 1108626 2497229 := bbase (se 3 (by rfl) ⟨468230, by rfl⟩ : syracuseStep 2497229 = 936461) (by norm_num)
theorem B1186525 : Blo 1108626 1186525 := bbase (se 3 (by rfl) ⟨222473, by rfl⟩ : syracuseStep 1186525 = 444947) (by norm_num)
theorem B1874677 : Blo 1108626 1874677 := bbase (se 5 (by rfl) ⟨87875, by rfl⟩ : syracuseStep 1874677 = 175751) (by norm_num)
theorem B3742469 : Blo 1108626 3742469 := bbase (se 4 (by rfl) ⟨350856, by rfl⟩ : syracuseStep 3742469 = 701713) (by norm_num)
theorem B2497301 : Blo 1108626 2497301 := bbase (se 6 (by rfl) ⟨58530, by rfl⟩ : syracuseStep 2497301 = 117061) (by norm_num)
theorem B1874765 : Blo 1108626 1874765 := bbase (se 3 (by rfl) ⟨351518, by rfl⟩ : syracuseStep 1874765 = 703037) (by norm_num)
theorem B2497373 : Blo 1108626 2497373 := bbase (se 3 (by rfl) ⟨468257, by rfl⟩ : syracuseStep 2497373 = 936515) (by norm_num)
theorem B2497445 : Blo 1108626 2497445 := bbase (se 4 (by rfl) ⟨234135, by rfl⟩ : syracuseStep 2497445 = 468271) (by norm_num)
theorem B1874893 : Blo 1108626 1874893 := bbase (se 3 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 1874893 = 703085) (by norm_num)
theorem B2497517 : Blo 1108626 2497517 := bbase (se 3 (by rfl) ⟨468284, by rfl⟩ : syracuseStep 2497517 = 936569) (by norm_num)
theorem B1874981 : Blo 1108626 1874981 := bbase (se 4 (by rfl) ⟨175779, by rfl⟩ : syracuseStep 1874981 = 351559) (by norm_num)
theorem B2497589 : Blo 1108626 2497589 := bbase (se 5 (by rfl) ⟨117074, by rfl⟩ : syracuseStep 2497589 = 234149) (by norm_num)
theorem B1776725 : Blo 1108626 1776725 := bbase (se 8 (by rfl) ⟨10410, by rfl⟩ : syracuseStep 1776725 = 20821) (by norm_num)
theorem B2497661 : Blo 1108626 2497661 := bbase (se 3 (by rfl) ⟨468311, by rfl⟩ : syracuseStep 2497661 = 936623) (by norm_num)
theorem B1186969 : Blo 1108626 1186969 := bbase (se 2 (by rfl) ⟨445113, by rfl⟩ : syracuseStep 1186969 = 890227) (by norm_num)
theorem B1875109 : Blo 1108626 1875109 := bbase (se 4 (by rfl) ⟨175791, by rfl⟩ : syracuseStep 1875109 = 351583) (by norm_num)
theorem B3742901 : Blo 1108626 3742901 := bbase (se 5 (by rfl) ⟨175448, by rfl⟩ : syracuseStep 3742901 = 350897) (by norm_num)
theorem B2497733 : Blo 1108626 2497733 := bbase (se 4 (by rfl) ⟨234162, by rfl⟩ : syracuseStep 2497733 = 468325) (by norm_num)
theorem B1875197 : Blo 1108626 1875197 := bbase (se 3 (by rfl) ⟨351599, by rfl⟩ : syracuseStep 1875197 = 703199) (by norm_num)
theorem B2497805 : Blo 1108626 2497805 := bbase (se 3 (by rfl) ⟨468338, by rfl⟩ : syracuseStep 2497805 = 936677) (by norm_num)
theorem B1776917 : Blo 1108626 1776917 := bbase (se 6 (by rfl) ⟨41646, by rfl⟩ : syracuseStep 1776917 = 83293) (by norm_num)
theorem B1187093 : Blo 1108626 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B2497877 : Blo 1108626 2497877 := bbase (se 11 (by rfl) ⟨1829, by rfl⟩ : syracuseStep 2497877 = 3659) (by norm_num)
theorem B1351037 : Blo 1108626 1351037 := bbase (se 3 (by rfl) ⟨253319, by rfl⟩ : syracuseStep 1351037 = 506639) (by norm_num)
theorem B1875325 : Blo 1108626 1875325 := bbase (se 3 (by rfl) ⟨351623, by rfl⟩ : syracuseStep 1875325 = 703247) (by norm_num)
theorem B3612053 : Blo 1108626 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B2497949 : Blo 1108626 2497949 := bbase (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) (by norm_num)
theorem B1875413 : Blo 1108626 1875413 := bbase (se 7 (by rfl) ⟨21977, by rfl⟩ : syracuseStep 1875413 = 43955) (by norm_num)
theorem B2104805 : Blo 1108626 2104805 := bbase (se 4 (by rfl) ⟨197325, by rfl⟩ : syracuseStep 2104805 = 394651) (by norm_num)
theorem B2498021 : Blo 1108626 2498021 := bbase (se 4 (by rfl) ⟨234189, by rfl⟩ : syracuseStep 2498021 = 468379) (by norm_num)
theorem B1187345 : Blo 1108626 1187345 := bbase (se 2 (by rfl) ⟨445254, by rfl⟩ : syracuseStep 1187345 = 890509) (by norm_num)
theorem B2498093 : Blo 1108626 2498093 := bbase (se 3 (by rfl) ⟨468392, by rfl⟩ : syracuseStep 2498093 = 936785) (by norm_num)
theorem B4005445 : Blo 1108626 4005445 := bbase (se 4 (by rfl) ⟨375510, by rfl⟩ : syracuseStep 4005445 = 751021) (by norm_num)
theorem B1875541 : Blo 1108626 1875541 := bbase (se 8 (by rfl) ⟨10989, by rfl⟩ : syracuseStep 1875541 = 21979) (by norm_num)
theorem B3743333 : Blo 1108626 3743333 := bbase (se 4 (by rfl) ⟨350937, by rfl⟩ : syracuseStep 3743333 = 701875) (by norm_num)
theorem B2498165 : Blo 1108626 2498165 := bbase (se 5 (by rfl) ⟨117101, by rfl⟩ : syracuseStep 2498165 = 234203) (by norm_num)
theorem B2104957 : Blo 1108626 2104957 := bbase (se 3 (by rfl) ⟨394679, by rfl⟩ : syracuseStep 2104957 = 789359) (by norm_num)
theorem B1875629 : Blo 1108626 1875629 := bbase (se 3 (by rfl) ⟨351680, by rfl⟩ : syracuseStep 1875629 = 703361) (by norm_num)
theorem B9608885 : Blo 1108626 9608885 := bbase (se 5 (by rfl) ⟨450416, by rfl⟩ : syracuseStep 9608885 = 900833) (by norm_num)
theorem B2498237 : Blo 1108626 2498237 := bbase (se 3 (by rfl) ⟨468419, by rfl⟩ : syracuseStep 2498237 = 936839) (by norm_num)
theorem B6004469 : Blo 1108626 6004469 := bbase (se 5 (by rfl) ⟨281459, by rfl⟩ : syracuseStep 6004469 = 562919) (by norm_num)
theorem B2498309 : Blo 1108626 2498309 := bbase (se 4 (by rfl) ⟨234216, by rfl⟩ : syracuseStep 2498309 = 468433) (by norm_num)
theorem B1875757 : Blo 1108626 1875757 := bbase (se 3 (by rfl) ⟨351704, by rfl⟩ : syracuseStep 1875757 = 703409) (by norm_num)
theorem B2498381 : Blo 1108626 2498381 := bbase (se 3 (by rfl) ⟨468446, by rfl⟩ : syracuseStep 2498381 = 936893) (by norm_num)
theorem B1875845 : Blo 1108626 1875845 := bbase (se 4 (by rfl) ⟨175860, by rfl⟩ : syracuseStep 1875845 = 351721) (by norm_num)
theorem B2498453 : Blo 1108626 2498453 := bbase (se 6 (by rfl) ⟨58557, by rfl⟩ : syracuseStep 2498453 = 117115) (by norm_num)
theorem B21372821 : Blo 1108626 21372821 := bbase (se 6 (by rfl) ⟨500925, by rfl⟩ : syracuseStep 21372821 = 1001851) (by norm_num)
theorem B2105261 : Blo 1108626 2105261 := bbase (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) (by norm_num)
theorem B1187789 : Blo 1108626 1187789 := bbase (se 3 (by rfl) ⟨222710, by rfl⟩ : syracuseStep 1187789 = 445421) (by norm_num)
theorem B2498525 : Blo 1108626 2498525 := bbase (se 3 (by rfl) ⟨468473, by rfl⟩ : syracuseStep 2498525 = 936947) (by norm_num)
theorem B1875973 : Blo 1108626 1875973 := bbase (se 4 (by rfl) ⟨175872, by rfl⟩ : syracuseStep 1875973 = 351745) (by norm_num)
theorem B3743765 : Blo 1108626 3743765 := bbase (se 6 (by rfl) ⟨87744, by rfl⟩ : syracuseStep 3743765 = 175489) (by norm_num)
theorem B2498597 : Blo 1108626 2498597 := bbase (se 4 (by rfl) ⟨234243, by rfl⟩ : syracuseStep 2498597 = 468487) (by norm_num)
theorem B1581133 : Blo 1108626 1581133 := bbase (se 3 (by rfl) ⟨296462, by rfl⟩ : syracuseStep 1581133 = 592925) (by norm_num)
theorem B1876061 : Blo 1108626 1876061 := bbase (se 3 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 1876061 = 703523) (by norm_num)
theorem B2498669 : Blo 1108626 2498669 := bbase (se 3 (by rfl) ⟨468500, by rfl⟩ : syracuseStep 2498669 = 937001) (by norm_num)
theorem B2498741 : Blo 1108626 2498741 := bbase (se 5 (by rfl) ⟨117128, by rfl⟩ : syracuseStep 2498741 = 234257) (by norm_num)
theorem B1188037 : Blo 1108626 1188037 := bbase (se 4 (by rfl) ⟨111378, by rfl⟩ : syracuseStep 1188037 = 222757) (by norm_num)
theorem B1876189 : Blo 1108626 1876189 := bbase (se 3 (by rfl) ⟨351785, by rfl⟩ : syracuseStep 1876189 = 703571) (by norm_num)
theorem B2498813 : Blo 1108626 2498813 := bbase (se 3 (by rfl) ⟨468527, by rfl⟩ : syracuseStep 2498813 = 937055) (by norm_num)
theorem B1876277 : Blo 1108626 1876277 := bbase (se 5 (by rfl) ⟨87950, by rfl⟩ : syracuseStep 1876277 = 175901) (by norm_num)
theorem B2498885 : Blo 1108626 2498885 := bbase (se 4 (by rfl) ⟨234270, by rfl⟩ : syracuseStep 2498885 = 468541) (by norm_num)
theorem B2531677 : Blo 1108626 2531677 := bbase (se 3 (by rfl) ⟨474689, by rfl⟩ : syracuseStep 2531677 = 949379) (by norm_num)
theorem B2498957 : Blo 1108626 2498957 := bbase (se 3 (by rfl) ⟨468554, by rfl⟩ : syracuseStep 2498957 = 937109) (by norm_num)
theorem B1876405 : Blo 1108626 1876405 := bbase (se 5 (by rfl) ⟨87956, by rfl⟩ : syracuseStep 1876405 = 175913) (by norm_num)
theorem B3744197 : Blo 1108626 3744197 := bbase (se 4 (by rfl) ⟨351018, by rfl⟩ : syracuseStep 3744197 = 702037) (by norm_num)
theorem B8102357 : Blo 1108626 8102357 := bbase (se 7 (by rfl) ⟨94949, by rfl⟩ : syracuseStep 8102357 = 189899) (by norm_num)
theorem B2499029 : Blo 1108626 2499029 := bbase (se 7 (by rfl) ⟨29285, by rfl⟩ : syracuseStep 2499029 = 58571) (by norm_num)
theorem B1876493 : Blo 1108626 1876493 := bbase (se 3 (by rfl) ⟨351842, by rfl⟩ : syracuseStep 1876493 = 703685) (by norm_num)
theorem B2499101 : Blo 1108626 2499101 := bbase (se 3 (by rfl) ⟨468581, by rfl⟩ : syracuseStep 2499101 = 937163) (by norm_num)
theorem B2499173 : Blo 1108626 2499173 := bbase (se 4 (by rfl) ⟨234297, by rfl⟩ : syracuseStep 2499173 = 468595) (by norm_num)
theorem B1876621 : Blo 1108626 1876621 := bbase (se 3 (by rfl) ⟨351866, by rfl⟩ : syracuseStep 1876621 = 703733) (by norm_num)
theorem B1352341 : Blo 1108626 1352341 := bbase (se 6 (by rfl) ⟨31695, by rfl⟩ : syracuseStep 1352341 = 63391) (by norm_num)
theorem B2106013 : Blo 1108626 2106013 := bbase (se 3 (by rfl) ⟨394877, by rfl⟩ : syracuseStep 2106013 = 789755) (by norm_num)
theorem B1581725 : Blo 1108626 1581725 := bbase (se 3 (by rfl) ⟨296573, by rfl⟩ : syracuseStep 1581725 = 593147) (by norm_num)
theorem B2499245 : Blo 1108626 2499245 := bbase (se 3 (by rfl) ⟨468608, by rfl⟩ : syracuseStep 2499245 = 937217) (by norm_num)
theorem B1778365 : Blo 1108626 1778365 := bbase (se 3 (by rfl) ⟨333443, by rfl⟩ : syracuseStep 1778365 = 666887) (by norm_num)
theorem B1876709 : Blo 1108626 1876709 := bbase (se 4 (by rfl) ⟨175941, by rfl⟩ : syracuseStep 1876709 = 351883) (by norm_num)
theorem B1581805 : Blo 1108626 1581805 := bbase (se 3 (by rfl) ⟨296588, by rfl⟩ : syracuseStep 1581805 = 593177) (by norm_num)
theorem B2499317 : Blo 1108626 2499317 := bbase (se 5 (by rfl) ⟨117155, by rfl⟩ : syracuseStep 2499317 = 234311) (by norm_num)
theorem B2106157 : Blo 1108626 2106157 := bbase (se 3 (by rfl) ⟨394904, by rfl⟩ : syracuseStep 2106157 = 789809) (by norm_num)
theorem B2499389 : Blo 1108626 2499389 := bbase (se 3 (by rfl) ⟨468635, by rfl⟩ : syracuseStep 2499389 = 937271) (by norm_num)
theorem B2532197 : Blo 1108626 2532197 := bbase (se 4 (by rfl) ⟨237393, by rfl⟩ : syracuseStep 2532197 = 474787) (by norm_num)
theorem B1581925 : Blo 1108626 1581925 := bbase (se 4 (by rfl) ⟨148305, by rfl⟩ : syracuseStep 1581925 = 296611) (by norm_num)
theorem B1876837 : Blo 1108626 1876837 := bbase (se 4 (by rfl) ⟨175953, by rfl⟩ : syracuseStep 1876837 = 351907) (by norm_num)
theorem B3744629 : Blo 1108626 3744629 := bbase (se 5 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 3744629 = 351059) (by norm_num)
theorem B2499461 : Blo 1108626 2499461 := bbase (se 4 (by rfl) ⟨234324, by rfl⟩ : syracuseStep 2499461 = 468649) (by norm_num)
theorem B2139061 : Blo 1108626 2139061 := bbase (se 5 (by rfl) ⟨100268, by rfl⟩ : syracuseStep 2139061 = 200537) (by norm_num)
theorem B1876925 : Blo 1108626 1876925 := bbase (se 3 (by rfl) ⟨351923, by rfl⟩ : syracuseStep 1876925 = 703847) (by norm_num)
theorem B2368453 : Blo 1108626 2368453 := bbase (se 4 (by rfl) ⟨222042, by rfl⟩ : syracuseStep 2368453 = 444085) (by norm_num)
theorem B1582021 : Blo 1108626 1582021 := bbase (se 4 (by rfl) ⟨148314, by rfl⟩ : syracuseStep 1582021 = 296629) (by norm_num)
theorem B2106317 : Blo 1108626 2106317 := bbase (se 3 (by rfl) ⟨394934, by rfl⟩ : syracuseStep 2106317 = 789869) (by norm_num)
theorem B2499533 : Blo 1108626 2499533 := bbase (se 3 (by rfl) ⟨468662, by rfl⟩ : syracuseStep 2499533 = 937325) (by norm_num)
theorem B2499605 : Blo 1108626 2499605 := bbase (se 6 (by rfl) ⟨58584, by rfl⟩ : syracuseStep 2499605 = 117169) (by norm_num)
theorem B6333461 : Blo 1108626 6333461 := bbase (se 6 (by rfl) ⟨148440, by rfl⟩ : syracuseStep 6333461 = 296881) (by norm_num)
theorem B1877053 : Blo 1108626 1877053 := bbase (se 3 (by rfl) ⟨351947, by rfl⟩ : syracuseStep 1877053 = 703895) (by norm_num)
theorem B2106461 : Blo 1108626 2106461 := bbase (se 3 (by rfl) ⟨394961, by rfl⟩ : syracuseStep 2106461 = 789923) (by norm_num)
theorem B2499677 : Blo 1108626 2499677 := bbase (se 3 (by rfl) ⟨468689, by rfl⟩ : syracuseStep 2499677 = 937379) (by norm_num)
theorem B1877141 : Blo 1108626 1877141 := bbase (se 6 (by rfl) ⟨43995, by rfl⟩ : syracuseStep 1877141 = 87991) (by norm_num)
theorem B2499749 : Blo 1108626 2499749 := bbase (se 4 (by rfl) ⟨234351, by rfl⟩ : syracuseStep 2499749 = 468703) (by norm_num)
theorem B4334789 : Blo 1108626 4334789 := bbase (se 4 (by rfl) ⟨406386, by rfl⟩ : syracuseStep 4334789 = 812773) (by norm_num)
theorem B2499821 : Blo 1108626 2499821 := bbase (se 3 (by rfl) ⟨468716, by rfl⟩ : syracuseStep 2499821 = 937433) (by norm_num)
theorem B1877269 : Blo 1108626 1877269 := bbase (se 6 (by rfl) ⟨43998, by rfl⟩ : syracuseStep 1877269 = 87997) (by norm_num)
theorem B3745061 : Blo 1108626 3745061 := bbase (se 4 (by rfl) ⟨351099, by rfl⟩ : syracuseStep 3745061 = 702199) (by norm_num)
theorem B2499893 : Blo 1108626 2499893 := bbase (se 5 (by rfl) ⟨117182, by rfl⟩ : syracuseStep 2499893 = 234365) (by norm_num)
theorem B2663741 : Blo 1108626 2663741 := bbase (se 3 (by rfl) ⟨499451, by rfl⟩ : syracuseStep 2663741 = 998903) (by norm_num)
theorem B1877357 : Blo 1108626 1877357 := bbase (se 3 (by rfl) ⟨352004, by rfl⟩ : syracuseStep 1877357 = 704009) (by norm_num)
theorem B2106749 : Blo 1108626 2106749 := bbase (se 3 (by rfl) ⟨395015, by rfl⟩ : syracuseStep 2106749 = 790031) (by norm_num)
theorem B2499965 : Blo 1108626 2499965 := bbase (se 3 (by rfl) ⟨468743, by rfl⟩ : syracuseStep 2499965 = 937487) (by norm_num)
theorem B1582517 : Blo 1108626 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B2500037 : Blo 1108626 2500037 := bbase (se 4 (by rfl) ⟨234378, by rfl⟩ : syracuseStep 2500037 = 468757) (by norm_num)
theorem B1877485 : Blo 1108626 1877485 := bbase (se 3 (by rfl) ⟨352028, by rfl⟩ : syracuseStep 1877485 = 704057) (by norm_num)
theorem B2663933 : Blo 1108626 2663933 := bbase (se 3 (by rfl) ⟨499487, by rfl⟩ : syracuseStep 2663933 = 998975) (by norm_num)
theorem B2500109 : Blo 1108626 2500109 := bbase (se 3 (by rfl) ⟨468770, by rfl⟩ : syracuseStep 2500109 = 937541) (by norm_num)
theorem B2106901 : Blo 1108626 2106901 := bbase (se 6 (by rfl) ⟨49380, by rfl⟩ : syracuseStep 2106901 = 98761) (by norm_num)
theorem B2500181 : Blo 1108626 2500181 := bbase (se 8 (by rfl) ⟨14649, by rfl⟩ : syracuseStep 2500181 = 29299) (by norm_num)
theorem B2500253 : Blo 1108626 2500253 := bbase (se 3 (by rfl) ⟨468797, by rfl⟩ : syracuseStep 2500253 = 937595) (by norm_num)
theorem B3745493 : Blo 1108626 3745493 := bbase (se 7 (by rfl) ⟨43892, by rfl⟩ : syracuseStep 3745493 = 87785) (by norm_num)
theorem B32057045 : Blo 1108626 32057045 := bbase (se 7 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 32057045 = 751337) (by norm_num)
theorem B2926309 : Blo 1108626 2926309 := bbase (se 4 (by rfl) ⟨274341, by rfl⟩ : syracuseStep 2926309 = 548683) (by norm_num)
theorem B2500325 : Blo 1108626 2500325 := bbase (se 4 (by rfl) ⟨234405, by rfl⟩ : syracuseStep 2500325 = 468811) (by norm_num)
theorem B10397429 : Blo 1108626 10397429 := bbase (se 5 (by rfl) ⟨487379, by rfl⟩ : syracuseStep 10397429 = 974759) (by norm_num)
theorem B2500397 : Blo 1108626 2500397 := bbase (se 3 (by rfl) ⟨468824, by rfl⟩ : syracuseStep 2500397 = 937649) (by norm_num)
theorem B2369341 : Blo 1108626 2369341 := bbase (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) (by norm_num)
theorem B2107205 : Blo 1108626 2107205 := bbase (se 4 (by rfl) ⟨197550, by rfl⟩ : syracuseStep 2107205 = 395101) (by norm_num)
theorem B2500469 : Blo 1108626 2500469 := bbase (se 5 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 2500469 = 234419) (by norm_num)
theorem B5613461 : Blo 1108626 5613461 := bbase (se 6 (by rfl) ⟨131565, by rfl⟩ : syracuseStep 5613461 = 263131) (by norm_num)
theorem B2500541 : Blo 1108626 2500541 := bbase (se 3 (by rfl) ⟨468851, by rfl⟩ : syracuseStep 2500541 = 937703) (by norm_num)
theorem B1583069 : Blo 1108626 1583069 := bbase (se 3 (by rfl) ⟨296825, by rfl⟩ : syracuseStep 1583069 = 593651) (by norm_num)
theorem B2500613 : Blo 1108626 2500613 := bbase (se 4 (by rfl) ⟨234432, by rfl⟩ : syracuseStep 2500613 = 468865) (by norm_num)
theorem B1779749 : Blo 1108626 1779749 := bbase (se 4 (by rfl) ⟨166851, by rfl⟩ : syracuseStep 1779749 = 333703) (by norm_num)
theorem B4499509 : Blo 1108626 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B2500685 : Blo 1108626 2500685 := bbase (se 3 (by rfl) ⟨468878, by rfl⟩ : syracuseStep 2500685 = 937757) (by norm_num)
theorem B3745925 : Blo 1108626 3745925 := bbase (se 4 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 3745925 = 702361) (by norm_num)
theorem B2500757 : Blo 1108626 2500757 := bbase (se 6 (by rfl) ⟨58611, by rfl⟩ : syracuseStep 2500757 = 117223) (by norm_num)
theorem B6334645 : Blo 1108626 6334645 := bbase (se 5 (by rfl) ⟨296936, by rfl⟩ : syracuseStep 6334645 = 593873) (by norm_num)
theorem B2500829 : Blo 1108626 2500829 := bbase (se 3 (by rfl) ⟨468905, by rfl⟩ : syracuseStep 2500829 = 937811) (by norm_num)
theorem B1779941 : Blo 1108626 1779941 := bbase (se 4 (by rfl) ⟨166869, by rfl⟩ : syracuseStep 1779941 = 333739) (by norm_num)
theorem B2500901 : Blo 1108626 2500901 := bbase (se 4 (by rfl) ⟨234459, by rfl⟩ : syracuseStep 2500901 = 468919) (by norm_num)
theorem B2369837 : Blo 1108626 2369837 := bbase (se 3 (by rfl) ⟨444344, by rfl⟩ : syracuseStep 2369837 = 888689) (by norm_num)
theorem B7317845 : Blo 1108626 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B2500973 : Blo 1108626 2500973 := bbase (se 3 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 2500973 = 937865) (by norm_num)
theorem B2501045 : Blo 1108626 2501045 := bbase (se 5 (by rfl) ⟨117236, by rfl⟩ : syracuseStep 2501045 = 234473) (by norm_num)
theorem B1124813 : Blo 1108626 1124813 := bbase (se 3 (by rfl) ⟨210902, by rfl⟩ : syracuseStep 1124813 = 421805) (by norm_num)
theorem B2501117 : Blo 1108626 2501117 := bbase (se 3 (by rfl) ⟨468959, by rfl⟩ : syracuseStep 2501117 = 937919) (by norm_num)
theorem B1124885 : Blo 1108626 1124885 := bbase (se 6 (by rfl) ⟨26364, by rfl⟩ : syracuseStep 1124885 = 52729) (by norm_num)
theorem B3746357 : Blo 1108626 3746357 := bbase (se 5 (by rfl) ⟨175610, by rfl⟩ : syracuseStep 3746357 = 351221) (by norm_num)
theorem B2107957 : Blo 1108626 2107957 := bbase (se 5 (by rfl) ⟨98810, by rfl⟩ : syracuseStep 2107957 = 197621) (by norm_num)
theorem B5057093 : Blo 1108626 5057093 := bbase (se 4 (by rfl) ⟨474102, by rfl⟩ : syracuseStep 5057093 = 948205) (by norm_num)
theorem B2501189 : Blo 1108626 2501189 := bbase (se 4 (by rfl) ⟨234486, by rfl⟩ : syracuseStep 2501189 = 468973) (by norm_num)
theorem B2534021 : Blo 1108626 2534021 := bbase (se 4 (by rfl) ⟨237564, by rfl⟩ : syracuseStep 2534021 = 475129) (by norm_num)
theorem B2501261 : Blo 1108626 2501261 := bbase (se 3 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 2501261 = 937973) (by norm_num)
theorem B2108101 : Blo 1108626 2108101 := bbase (se 4 (by rfl) ⟨197634, by rfl⟩ : syracuseStep 2108101 = 395269) (by norm_num)
theorem B1583821 : Blo 1108626 1583821 := bbase (se 3 (by rfl) ⟨296966, by rfl⟩ : syracuseStep 1583821 = 593933) (by norm_num)
theorem B2501333 : Blo 1108626 2501333 := bbase (se 7 (by rfl) ⟨29312, by rfl⟩ : syracuseStep 2501333 = 58625) (by norm_num)
theorem B2501405 : Blo 1108626 2501405 := bbase (se 3 (by rfl) ⟨469013, by rfl⟩ : syracuseStep 2501405 = 938027) (by norm_num)
theorem B2108261 : Blo 1108626 2108261 := bbase (se 4 (by rfl) ⟨197649, by rfl⟩ : syracuseStep 2108261 = 395299) (by norm_num)
theorem B2501477 : Blo 1108626 2501477 := bbase (se 4 (by rfl) ⟨234513, by rfl⟩ : syracuseStep 2501477 = 469027) (by norm_num)
theorem B2501549 : Blo 1108626 2501549 := bbase (se 3 (by rfl) ⟨469040, by rfl⟩ : syracuseStep 2501549 = 938081) (by norm_num)
theorem B3746789 : Blo 1108626 3746789 := bbase (se 4 (by rfl) ⟨351261, by rfl⟩ : syracuseStep 3746789 = 702523) (by norm_num)
theorem B2108405 : Blo 1108626 2108405 := bbase (se 5 (by rfl) ⟨98831, by rfl⟩ : syracuseStep 2108405 = 197663) (by norm_num)
theorem B2501621 : Blo 1108626 2501621 := bbase (se 5 (by rfl) ⟨117263, by rfl⟩ : syracuseStep 2501621 = 234527) (by norm_num)
theorem B1354757 : Blo 1108626 1354757 := bbase (se 4 (by rfl) ⟨127008, by rfl⟩ : syracuseStep 1354757 = 254017) (by norm_num)
theorem B2501693 : Blo 1108626 2501693 := bbase (se 3 (by rfl) ⟨469067, by rfl⟩ : syracuseStep 2501693 = 938135) (by norm_num)
theorem B2501765 : Blo 1108626 2501765 := bbase (se 4 (by rfl) ⟨234540, by rfl⟩ : syracuseStep 2501765 = 469081) (by norm_num)
theorem B2370701 : Blo 1108626 2370701 := bbase (se 3 (by rfl) ⟨444506, by rfl⟩ : syracuseStep 2370701 = 889013) (by norm_num)
theorem B5614757 : Blo 1108626 5614757 := bbase (se 4 (by rfl) ⟨526383, by rfl⟩ : syracuseStep 5614757 = 1052767) (by norm_num)
theorem B2501837 : Blo 1108626 2501837 := bbase (se 3 (by rfl) ⟨469094, by rfl⟩ : syracuseStep 2501837 = 938189) (by norm_num)
theorem B2108693 : Blo 1108626 2108693 := bbase (se 6 (by rfl) ⟨49422, by rfl⟩ : syracuseStep 2108693 = 98845) (by norm_num)
theorem B2501909 : Blo 1108626 2501909 := bbase (se 6 (by rfl) ⟨58638, by rfl⟩ : syracuseStep 2501909 = 117277) (by norm_num)
theorem B2370845 : Blo 1108626 2370845 := bbase (se 3 (by rfl) ⟨444533, by rfl⟩ : syracuseStep 2370845 = 889067) (by norm_num)
theorem B2501981 : Blo 1108626 2501981 := bbase (se 3 (by rfl) ⟨469121, by rfl⟩ : syracuseStep 2501981 = 938243) (by norm_num)
theorem B3747221 : Blo 1108626 3747221 := bbase (se 6 (by rfl) ⟨87825, by rfl⟩ : syracuseStep 3747221 = 175651) (by norm_num)
theorem B2665885 : Blo 1108626 2665885 := bbase (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) (by norm_num)
theorem B2502053 : Blo 1108626 2502053 := bbase (se 4 (by rfl) ⟨234567, by rfl⟩ : syracuseStep 2502053 = 469135) (by norm_num)
theorem B2108845 : Blo 1108626 2108845 := bbase (se 3 (by rfl) ⟨395408, by rfl⟩ : syracuseStep 2108845 = 790817) (by norm_num)
theorem B2502125 : Blo 1108626 2502125 := bbase (se 3 (by rfl) ⟨469148, by rfl⟩ : syracuseStep 2502125 = 938297) (by norm_num)
theorem B1781261 : Blo 1108626 1781261 := bbase (se 3 (by rfl) ⟨333986, by rfl⟩ : syracuseStep 1781261 = 667973) (by norm_num)
theorem B2502197 : Blo 1108626 2502197 := bbase (se 5 (by rfl) ⟨117290, by rfl⟩ : syracuseStep 2502197 = 234581) (by norm_num)
theorem B1781357 : Blo 1108626 1781357 := bbase (se 3 (by rfl) ⟨334004, by rfl⟩ : syracuseStep 1781357 = 668009) (by norm_num)
theorem B2502269 : Blo 1108626 2502269 := bbase (se 3 (by rfl) ⟨469175, by rfl⟩ : syracuseStep 2502269 = 938351) (by norm_num)
theorem B1781389 : Blo 1108626 1781389 := bbase (se 3 (by rfl) ⟨334010, by rfl⟩ : syracuseStep 1781389 = 668021) (by norm_num)
theorem B2502341 : Blo 1108626 2502341 := bbase (se 4 (by rfl) ⟨234594, by rfl⟩ : syracuseStep 2502341 = 469189) (by norm_num)
theorem B2109149 : Blo 1108626 2109149 := bbase (se 3 (by rfl) ⟨395465, by rfl⟩ : syracuseStep 2109149 = 790931) (by norm_num)
theorem B2502413 : Blo 1108626 2502413 := bbase (se 3 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 2502413 = 938405) (by norm_num)
theorem B3747653 : Blo 1108626 3747653 := bbase (se 4 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 3747653 = 702685) (by norm_num)
theorem B2502485 : Blo 1108626 2502485 := bbase (se 9 (by rfl) ⟨7331, by rfl⟩ : syracuseStep 2502485 = 14663) (by norm_num)
theorem B8433557 : Blo 1108626 8433557 := bbase (se 6 (by rfl) ⟨197661, by rfl⟩ : syracuseStep 8433557 = 395323) (by norm_num)
theorem B2502557 : Blo 1108626 2502557 := bbase (se 3 (by rfl) ⟨469229, by rfl⟩ : syracuseStep 2502557 = 938459) (by norm_num)
theorem B2502629 : Blo 1108626 2502629 := bbase (se 4 (by rfl) ⟨234621, by rfl⟩ : syracuseStep 2502629 = 469243) (by norm_num)
theorem B2371589 : Blo 1108626 2371589 := bbase (se 4 (by rfl) ⟨222336, by rfl⟩ : syracuseStep 2371589 = 444673) (by norm_num)
theorem B2502701 : Blo 1108626 2502701 := bbase (se 3 (by rfl) ⟨469256, by rfl⟩ : syracuseStep 2502701 = 938513) (by norm_num)
theorem B2502773 : Blo 1108626 2502773 := bbase (se 5 (by rfl) ⟨117317, by rfl⟩ : syracuseStep 2502773 = 234635) (by norm_num)
theorem B6336629 : Blo 1108626 6336629 := bbase (se 5 (by rfl) ⟨297029, by rfl⟩ : syracuseStep 6336629 = 594059) (by norm_num)
theorem B3158165 : Blo 1108626 3158165 := bbase (se 6 (by rfl) ⟨74019, by rfl⟩ : syracuseStep 3158165 = 148039) (by norm_num)
theorem B2502845 : Blo 1108626 2502845 := bbase (se 3 (by rfl) ⟨469283, by rfl⟩ : syracuseStep 2502845 = 938567) (by norm_num)
theorem B3748085 : Blo 1108626 3748085 := bbase (se 5 (by rfl) ⟨175691, by rfl⟩ : syracuseStep 3748085 = 351383) (by norm_num)
theorem B2502917 : Blo 1108626 2502917 := bbase (se 4 (by rfl) ⟨234648, by rfl⟩ : syracuseStep 2502917 = 469297) (by norm_num)
theorem B2502989 : Blo 1108626 2502989 := bbase (se 3 (by rfl) ⟨469310, by rfl⟩ : syracuseStep 2502989 = 938621) (by norm_num)
theorem B2666837 : Blo 1108626 2666837 := bbase (se 10 (by rfl) ⟨3906, by rfl⟩ : syracuseStep 2666837 = 7813) (by norm_num)
theorem B2666893 : Blo 1108626 2666893 := bbase (se 3 (by rfl) ⟨500042, by rfl⟩ : syracuseStep 2666893 = 1000085) (by norm_num)
theorem B2503061 : Blo 1108626 2503061 := bbase (se 6 (by rfl) ⟨58665, by rfl⟩ : syracuseStep 2503061 = 117331) (by norm_num)
theorem B5616053 : Blo 1108626 5616053 := bbase (se 5 (by rfl) ⟨263252, by rfl⟩ : syracuseStep 5616053 = 526505) (by norm_num)
theorem B2109901 : Blo 1108626 2109901 := bbase (se 3 (by rfl) ⟨395606, by rfl⟩ : syracuseStep 2109901 = 791213) (by norm_num)
theorem B2503133 : Blo 1108626 2503133 := bbase (se 3 (by rfl) ⟨469337, by rfl⟩ : syracuseStep 2503133 = 938675) (by norm_num)
theorem B2503205 : Blo 1108626 2503205 := bbase (se 4 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 2503205 = 469351) (by norm_num)
theorem B2110045 : Blo 1108626 2110045 := bbase (se 3 (by rfl) ⟨395633, by rfl⟩ : syracuseStep 2110045 = 791267) (by norm_num)
theorem B2503277 : Blo 1108626 2503277 := bbase (se 3 (by rfl) ⟨469364, by rfl⟩ : syracuseStep 2503277 = 938729) (by norm_num)
theorem B3748517 : Blo 1108626 3748517 := bbase (se 4 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 3748517 = 702847) (by norm_num)
theorem B2503349 : Blo 1108626 2503349 := bbase (se 5 (by rfl) ⟨117344, by rfl⟩ : syracuseStep 2503349 = 234689) (by norm_num)
theorem B2372341 : Blo 1108626 2372341 := bbase (se 5 (by rfl) ⟨111203, by rfl⟩ : syracuseStep 2372341 = 222407) (by norm_num)
theorem B2110205 : Blo 1108626 2110205 := bbase (se 3 (by rfl) ⟨395663, by rfl⟩ : syracuseStep 2110205 = 791327) (by norm_num)
theorem B2667269 : Blo 1108626 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B14234453 : Blo 1108626 14234453 := bbase (se 9 (by rfl) ⟨41702, by rfl⟩ : syracuseStep 14234453 = 83405) (by norm_num)
theorem B2372485 : Blo 1108626 2372485 := bbase (se 4 (by rfl) ⟨222420, by rfl⟩ : syracuseStep 2372485 = 444841) (by norm_num)
theorem B2110349 : Blo 1108626 2110349 := bbase (se 3 (by rfl) ⟨395690, by rfl⟩ : syracuseStep 2110349 = 791381) (by norm_num)
theorem B2667509 : Blo 1108626 2667509 := bbase (se 5 (by rfl) ⟨125039, by rfl⟩ : syracuseStep 2667509 = 250079) (by norm_num)
theorem B2536493 : Blo 1108626 2536493 := bbase (se 3 (by rfl) ⟨475592, by rfl⟩ : syracuseStep 2536493 = 951185) (by norm_num)
theorem B6403157 : Blo 1108626 6403157 := bbase (se 8 (by rfl) ⟨37518, by rfl⟩ : syracuseStep 6403157 = 75037) (by norm_num)
theorem B3748949 : Blo 1108626 3748949 := bbase (se 8 (by rfl) ⟨21966, by rfl⟩ : syracuseStep 3748949 = 43933) (by norm_num)
theorem B1127525 : Blo 1108626 1127525 := bbase (se 4 (by rfl) ⟨105705, by rfl⟩ : syracuseStep 1127525 = 211411) (by norm_num)
theorem B1127561 : Blo 1108626 1127561 := bbase (se 2 (by rfl) ⟨422835, by rfl⟩ : syracuseStep 1127561 = 845671) (by norm_num)
theorem B2110637 : Blo 1108626 2110637 := bbase (se 3 (by rfl) ⟨395744, by rfl⟩ : syracuseStep 2110637 = 791489) (by norm_num)
theorem B2372861 : Blo 1108626 2372861 := bbase (se 3 (by rfl) ⟨444911, by rfl⟩ : syracuseStep 2372861 = 889823) (by norm_num)
theorem B2110789 : Blo 1108626 2110789 := bbase (se 4 (by rfl) ⟨197886, by rfl⟩ : syracuseStep 2110789 = 395773) (by norm_num)
theorem B3421685 : Blo 1108626 3421685 := bbase (se 5 (by rfl) ⟨160391, by rfl⟩ : syracuseStep 3421685 = 320783) (by norm_num)
theorem B3749381 : Blo 1108626 3749381 := bbase (se 4 (by rfl) ⟨351504, by rfl⟩ : syracuseStep 3749381 = 703009) (by norm_num)
theorem B2373229 : Blo 1108626 2373229 := bbase (se 3 (by rfl) ⟨444980, by rfl⟩ : syracuseStep 2373229 = 889961) (by norm_num)
theorem B2111093 : Blo 1108626 2111093 := bbase (se 5 (by rfl) ⟨98957, by rfl⟩ : syracuseStep 2111093 = 197915) (by norm_num)
theorem B9483925 : Blo 1108626 9483925 := bbase (se 6 (by rfl) ⟨222279, by rfl⟩ : syracuseStep 9483925 = 444559) (by norm_num)
theorem B3159749 : Blo 1108626 3159749 := bbase (se 4 (by rfl) ⟨296226, by rfl⟩ : syracuseStep 3159749 = 592453) (by norm_num)
theorem B5617349 : Blo 1108626 5617349 := bbase (se 4 (by rfl) ⟨526626, by rfl⟩ : syracuseStep 5617349 = 1053253) (by norm_num)
theorem B4274005 : Blo 1108626 4274005 := bbase (se 9 (by rfl) ⟨12521, by rfl⟩ : syracuseStep 4274005 = 25043) (by norm_num)
theorem B3553141 : Blo 1108626 3553141 := bbase (se 5 (by rfl) ⟨166553, by rfl⟩ : syracuseStep 3553141 = 333107) (by norm_num)
theorem B3749813 : Blo 1108626 3749813 := bbase (se 5 (by rfl) ⟨175772, by rfl⟩ : syracuseStep 3749813 = 351545) (by norm_num)
theorem B2701253 : Blo 1108626 2701253 := bbase (se 4 (by rfl) ⟨253242, by rfl⟩ : syracuseStep 2701253 = 506485) (by norm_num)
theorem B8992853 : Blo 1108626 8992853 := bbase (se 8 (by rfl) ⟨52692, by rfl⟩ : syracuseStep 8992853 = 105385) (by norm_num)
theorem B3553397 : Blo 1108626 3553397 := bbase (se 5 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 3553397 = 333131) (by norm_num)
theorem B2406725 : Blo 1108626 2406725 := bbase (se 4 (by rfl) ⟨225630, by rfl⟩ : syracuseStep 2406725 = 451261) (by norm_num)
theorem B3160421 : Blo 1108626 3160421 := bbase (se 4 (by rfl) ⟨296289, by rfl⟩ : syracuseStep 3160421 = 592579) (by norm_num)
theorem B3750245 : Blo 1108626 3750245 := bbase (se 4 (by rfl) ⟨351585, by rfl⟩ : syracuseStep 3750245 = 703171) (by norm_num)
theorem B2111845 : Blo 1108626 2111845 := bbase (se 4 (by rfl) ⟨197985, by rfl⟩ : syracuseStep 2111845 = 395971) (by norm_num)
theorem B1849717 : Blo 1108626 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B8010197 : Blo 1108626 8010197 := bbase (se 7 (by rfl) ⟨93869, by rfl⟩ : syracuseStep 8010197 = 187739) (by norm_num)
theorem B2111989 : Blo 1108626 2111989 := bbase (se 5 (by rfl) ⟨98999, by rfl⟩ : syracuseStep 2111989 = 197999) (by norm_num)
theorem B1423909 : Blo 1108626 1423909 := bbase (se 4 (by rfl) ⟨133491, by rfl⟩ : syracuseStep 1423909 = 266983) (by norm_num)
theorem B2112149 : Blo 1108626 2112149 := bbase (se 6 (by rfl) ⟨49503, by rfl⟩ : syracuseStep 2112149 = 99007) (by norm_num)
theorem B1424125 : Blo 1108626 1424125 := bbase (se 3 (by rfl) ⟨267023, by rfl⟩ : syracuseStep 1424125 = 534047) (by norm_num)
theorem B3160853 : Blo 1108626 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B3750677 : Blo 1108626 3750677 := bbase (se 6 (by rfl) ⟨87906, by rfl⟩ : syracuseStep 3750677 = 175813) (by norm_num)
theorem B5618645 : Blo 1108626 5618645 := bbase (se 7 (by rfl) ⟨65843, by rfl⟩ : syracuseStep 5618645 = 131687) (by norm_num)
theorem B7322581 : Blo 1108626 7322581 := bbase (se 7 (by rfl) ⟨85811, by rfl⟩ : syracuseStep 7322581 = 171623) (by norm_num)
theorem B2374733 : Blo 1108626 2374733 := bbase (se 3 (by rfl) ⟨445262, by rfl⟩ : syracuseStep 2374733 = 890525) (by norm_num)
theorem B3751109 : Blo 1108626 3751109 := bbase (se 4 (by rfl) ⟨351666, by rfl⟩ : syracuseStep 3751109 = 703333) (by norm_num)
theorem B2374877 : Blo 1108626 2374877 := bbase (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) (by norm_num)
theorem B10665269 : Blo 1108626 10665269 := bbase (se 5 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 10665269 = 999869) (by norm_num)
theorem B7126325 : Blo 1108626 7126325 := bbase (se 5 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 7126325 = 668093) (by norm_num)
theorem B3161605 : Blo 1108626 3161605 := bbase (se 4 (by rfl) ⟨296400, by rfl⟩ : syracuseStep 3161605 = 592801) (by norm_num)
theorem B2375237 : Blo 1108626 2375237 := bbase (se 4 (by rfl) ⟨222678, by rfl⟩ : syracuseStep 2375237 = 445357) (by norm_num)
theorem B9485909 : Blo 1108626 9485909 := bbase (se 8 (by rfl) ⟨55581, by rfl⟩ : syracuseStep 9485909 = 111163) (by norm_num)
theorem B3751541 : Blo 1108626 3751541 := bbase (se 5 (by rfl) ⟨175853, by rfl⟩ : syracuseStep 3751541 = 351707) (by norm_num)
theorem B4210325 : Blo 1108626 4210325 := bbase (se 6 (by rfl) ⟨98679, by rfl⟩ : syracuseStep 4210325 = 197359) (by norm_num)
theorem B1425181 : Blo 1108626 1425181 := bbase (se 3 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 1425181 = 534443) (by norm_num)
theorem B4210613 : Blo 1108626 4210613 := bbase (se 5 (by rfl) ⟨197372, by rfl⟩ : syracuseStep 4210613 = 394745) (by norm_num)
theorem B2408381 : Blo 1108626 2408381 := bbase (se 3 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 2408381 = 903143) (by norm_num)
theorem B1687493 : Blo 1108626 1687493 := bbase (se 4 (by rfl) ⟨158202, by rfl⟩ : syracuseStep 1687493 = 316405) (by norm_num)
theorem B3751973 : Blo 1108626 3751973 := bbase (se 4 (by rfl) ⟨351747, by rfl⟩ : syracuseStep 3751973 = 703495) (by norm_num)
theorem B2670661 : Blo 1108626 2670661 := bbase (se 4 (by rfl) ⟨250374, by rfl⟩ : syracuseStep 2670661 = 500749) (by norm_num)
theorem B5619941 : Blo 1108626 5619941 := bbase (se 4 (by rfl) ⟨526869, by rfl⟩ : syracuseStep 5619941 = 1053739) (by norm_num)
theorem B2703709 : Blo 1108626 2703709 := bbase (se 3 (by rfl) ⟨506945, by rfl⟩ : syracuseStep 2703709 = 1013891) (by norm_num)
theorem B1687997 : Blo 1108626 1687997 := bbase (se 3 (by rfl) ⟨316499, by rfl⟩ : syracuseStep 1687997 = 632999) (by norm_num)
theorem B2376125 : Blo 1108626 2376125 := bbase (se 3 (by rfl) ⟨445523, by rfl⟩ : syracuseStep 2376125 = 891047) (by norm_num)
theorem B3752405 : Blo 1108626 3752405 := bbase (se 7 (by rfl) ⟨43973, by rfl⟩ : syracuseStep 3752405 = 87947) (by norm_num)
theorem B1688125 : Blo 1108626 1688125 := bbase (se 3 (by rfl) ⟨316523, by rfl⟩ : syracuseStep 1688125 = 633047) (by norm_num)
theorem B4276901 : Blo 1108626 4276901 := bbase (se 4 (by rfl) ⟨400959, by rfl⟩ : syracuseStep 4276901 = 801919) (by norm_num)
theorem B1622749 : Blo 1108626 1622749 := bbase (se 3 (by rfl) ⟨304265, by rfl⟩ : syracuseStep 1622749 = 608531) (by norm_num)
theorem B3556165 : Blo 1108626 3556165 := bbase (se 4 (by rfl) ⟨333390, by rfl⟩ : syracuseStep 3556165 = 666781) (by norm_num)
theorem B1426249 : Blo 1108626 1426249 := bbase (se 2 (by rfl) ⟨534843, by rfl⟩ : syracuseStep 1426249 = 1069687) (by norm_num)
theorem B3752837 : Blo 1108626 3752837 := bbase (se 4 (by rfl) ⟨351828, by rfl⟩ : syracuseStep 3752837 = 703657) (by norm_num)
theorem B4211797 : Blo 1108626 4211797 := bbase (se 8 (by rfl) ⟨24678, by rfl⟩ : syracuseStep 4211797 = 49357) (by norm_num)
theorem B2999477 : Blo 1108626 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B3753269 : Blo 1108626 3753269 := bbase (se 5 (by rfl) ⟨175934, by rfl⟩ : syracuseStep 3753269 = 351869) (by norm_num)
theorem B4212101 : Blo 1108626 4212101 := bbase (se 4 (by rfl) ⟨394884, by rfl⟩ : syracuseStep 4212101 = 789769) (by norm_num)
theorem B2672045 : Blo 1108626 2672045 := bbase (se 3 (by rfl) ⟨501008, by rfl⟩ : syracuseStep 2672045 = 1002017) (by norm_num)
theorem B5621237 : Blo 1108626 5621237 := bbase (se 5 (by rfl) ⟨263495, by rfl⟩ : syracuseStep 5621237 = 526991) (by norm_num)
theorem B2672237 : Blo 1108626 2672237 := bbase (se 3 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 2672237 = 1002089) (by norm_num)
theorem B3753701 : Blo 1108626 3753701 := bbase (se 4 (by rfl) ⟨351909, by rfl⟩ : syracuseStep 3753701 = 703819) (by norm_num)
theorem B1689341 : Blo 1108626 1689341 := bbase (se 3 (by rfl) ⟨316751, by rfl⟩ : syracuseStep 1689341 = 633503) (by norm_num)
theorem B1689493 : Blo 1108626 1689493 := bbase (se 6 (by rfl) ⟨39597, by rfl⟩ : syracuseStep 1689493 = 79195) (by norm_num)
theorem B1689541 : Blo 1108626 1689541 := bbase (se 4 (by rfl) ⟨158394, by rfl⟩ : syracuseStep 1689541 = 316789) (by norm_num)
theorem B3754133 : Blo 1108626 3754133 := bbase (se 6 (by rfl) ⟨87987, by rfl⟩ : syracuseStep 3754133 = 175975) (by norm_num)
theorem B3164453 : Blo 1108626 3164453 := bbase (se 4 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 3164453 = 593335) (by norm_num)
theorem B21121493 : Blo 1108626 21121493 := bbase (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) (by norm_num)
theorem B3754565 : Blo 1108626 3754565 := bbase (se 4 (by rfl) ⟨351990, by rfl⟩ : syracuseStep 3754565 = 703981) (by norm_num)
theorem B2312813 : Blo 1108626 2312813 := bbase (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) (by norm_num)
theorem B11389621 : Blo 1108626 11389621 := bbase (se 5 (by rfl) ⟨533888, by rfl⟩ : syracuseStep 11389621 = 1067777) (by norm_num)
theorem B5622533 : Blo 1108626 5622533 := bbase (se 4 (by rfl) ⟨527112, by rfl⟩ : syracuseStep 5622533 = 1054225) (by norm_num)
theorem B1264465 : Blo 1108626 1264465 := bbase (se 2 (by rfl) ⟨474174, by rfl⟩ : syracuseStep 1264465 = 948349) (by norm_num)
theorem B13519829 : Blo 1108626 13519829 := bbase (se 7 (by rfl) ⟨158435, by rfl⟩ : syracuseStep 13519829 = 316871) (by norm_num)
theorem B3754997 : Blo 1108626 3754997 := bbase (se 5 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 3754997 = 352031) (by norm_num)
theorem B7588981 : Blo 1108626 7588981 := bbase (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) (by norm_num)
theorem B2248069 : Blo 1108626 2248069 := bbase (se 4 (by rfl) ⟨210756, by rfl⟩ : syracuseStep 2248069 = 421513) (by norm_num)
theorem B3165637 : Blo 1108626 3165637 := bbase (se 4 (by rfl) ⟨296778, by rfl⟩ : syracuseStep 3165637 = 593557) (by norm_num)
theorem B4214213 : Blo 1108626 4214213 := bbase (se 4 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 4214213 = 790165) (by norm_num)
theorem B4050389 : Blo 1108626 4050389 := bbase (se 7 (by rfl) ⟨47465, by rfl⟩ : syracuseStep 4050389 = 94931) (by norm_num)
theorem B8441333 : Blo 1108626 8441333 := bbase (se 5 (by rfl) ⟨395687, by rfl⟩ : syracuseStep 8441333 = 791375) (by norm_num)
theorem B1265149 : Blo 1108626 1265149 := bbase (se 3 (by rfl) ⟨237215, by rfl⟩ : syracuseStep 1265149 = 474431) (by norm_num)
theorem B3165797 : Blo 1108626 3165797 := bbase (se 4 (by rfl) ⟨296793, by rfl⟩ : syracuseStep 3165797 = 593587) (by norm_num)
theorem B8113877 : Blo 1108626 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B4214501 : Blo 1108626 4214501 := bbase (se 4 (by rfl) ⟨395109, by rfl⟩ : syracuseStep 4214501 = 790219) (by norm_num)
theorem B3166037 : Blo 1108626 3166037 := bbase (se 9 (by rfl) ⟨9275, by rfl⟩ : syracuseStep 3166037 = 18551) (by norm_num)
theorem B2248717 : Blo 1108626 2248717 := bbase (se 3 (by rfl) ⟨421634, by rfl⟩ : syracuseStep 2248717 = 843269) (by norm_num)
theorem B4739093 : Blo 1108626 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B5623829 : Blo 1108626 5623829 := bbase (se 6 (by rfl) ⟨131808, by rfl⟩ : syracuseStep 5623829 = 263617) (by norm_num)
theorem B3166229 : Blo 1108626 3166229 := bbase (se 6 (by rfl) ⟨74208, by rfl⟩ : syracuseStep 3166229 = 148417) (by norm_num)
theorem B5689541 : Blo 1108626 5689541 := bbase (se 4 (by rfl) ⟨533394, by rfl⟩ : syracuseStep 5689541 = 1066789) (by norm_num)
theorem B25972949 : Blo 1108626 25972949 := bbase (se 7 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 25972949 = 608741) (by norm_num)
theorem B3658133 : Blo 1108626 3658133 := bbase (se 6 (by rfl) ⟨85737, by rfl⟩ : syracuseStep 3658133 = 171475) (by norm_num)
theorem B2806285 : Blo 1108626 2806285 := bbase (se 3 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 2806285 = 1052357) (by norm_num)
theorem B2806397 : Blo 1108626 2806397 := bbase (se 3 (by rfl) ⟨526199, by rfl⟩ : syracuseStep 2806397 = 1052399) (by norm_num)
theorem B2249381 : Blo 1108626 2249381 := bbase (se 4 (by rfl) ⟨210879, by rfl⟩ : syracuseStep 2249381 = 421759) (by norm_num)
theorem B1266445 : Blo 1108626 1266445 := bbase (se 3 (by rfl) ⟨237458, by rfl⟩ : syracuseStep 1266445 = 474917) (by norm_num)
theorem B2806589 : Blo 1108626 2806589 := bbase (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) (by norm_num)
theorem B1332073 : Blo 1108626 1332073 := bbase (se 2 (by rfl) ⟨499527, by rfl⟩ : syracuseStep 1332073 = 999055) (by norm_num)
theorem B4215685 : Blo 1108626 4215685 := bbase (se 4 (by rfl) ⟨395220, by rfl⟩ : syracuseStep 4215685 = 790441) (by norm_num)
theorem B1332121 : Blo 1108626 1332121 := bbase (se 2 (by rfl) ⟨499545, by rfl⟩ : syracuseStep 1332121 = 999091) (by norm_num)
theorem B3167221 : Blo 1108626 3167221 := bbase (se 5 (by rfl) ⟨148463, by rfl⟩ : syracuseStep 3167221 = 296927) (by norm_num)
theorem B5329925 : Blo 1108626 5329925 := bbase (se 4 (by rfl) ⟨499680, by rfl⟩ : syracuseStep 5329925 = 999361) (by norm_num)
theorem B5067893 : Blo 1108626 5067893 := bbase (se 5 (by rfl) ⟨237557, by rfl⟩ : syracuseStep 5067893 = 475115) (by norm_num)
theorem B2249869 : Blo 1108626 2249869 := bbase (se 3 (by rfl) ⟨421850, by rfl⟩ : syracuseStep 2249869 = 843701) (by norm_num)
theorem B2806933 : Blo 1108626 2806933 := bbase (se 6 (by rfl) ⟨65787, by rfl⟩ : syracuseStep 2806933 = 131575) (by norm_num)
theorem B4215989 : Blo 1108626 4215989 := bbase (se 5 (by rfl) ⟨197624, by rfl⟩ : syracuseStep 4215989 = 395249) (by norm_num)
theorem B2807045 : Blo 1108626 2807045 := bbase (se 4 (by rfl) ⟨263160, by rfl⟩ : syracuseStep 2807045 = 526321) (by norm_num)
theorem B5625125 : Blo 1108626 5625125 := bbase (se 4 (by rfl) ⟨527355, by rfl⟩ : syracuseStep 5625125 = 1054711) (by norm_num)
theorem B2807237 : Blo 1108626 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B1332793 : Blo 1108626 1332793 := bbase (se 2 (by rfl) ⟨499797, by rfl⟩ : syracuseStep 1332793 = 999595) (by norm_num)
theorem B4740869 : Blo 1108626 4740869 := bbase (se 4 (by rfl) ⟨444456, by rfl⟩ : syracuseStep 4740869 = 888913) (by norm_num)
theorem B2807581 : Blo 1108626 2807581 := bbase (se 3 (by rfl) ⟨526421, by rfl⟩ : syracuseStep 2807581 = 1052843) (by norm_num)
theorem B3561317 : Blo 1108626 3561317 := bbase (se 4 (by rfl) ⟨333873, by rfl⟩ : syracuseStep 3561317 = 667747) (by norm_num)
theorem B2807693 : Blo 1108626 2807693 := bbase (se 3 (by rfl) ⟨526442, by rfl⟩ : syracuseStep 2807693 = 1052885) (by norm_num)
theorem B22763477 : Blo 1108626 22763477 := bbase (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) (by norm_num)
theorem B3168325 : Blo 1108626 3168325 := bbase (se 4 (by rfl) ⟨297030, by rfl⟩ : syracuseStep 3168325 = 594061) (by norm_num)
theorem B2807885 : Blo 1108626 2807885 := bbase (se 3 (by rfl) ⟨526478, by rfl⟩ : syracuseStep 2807885 = 1052957) (by norm_num)
theorem B1267849 : Blo 1108626 1267849 := bbase (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) (by norm_num)
theorem B2283869 : Blo 1108626 2283869 := bbase (se 3 (by rfl) ⟨428225, by rfl⟩ : syracuseStep 2283869 = 856451) (by norm_num)
theorem B2251165 : Blo 1108626 2251165 := bbase (se 3 (by rfl) ⟨422093, by rfl⟩ : syracuseStep 2251165 = 844187) (by norm_num)
theorem B2808229 : Blo 1108626 2808229 := bbase (se 4 (by rfl) ⟨263271, by rfl⟩ : syracuseStep 2808229 = 526543) (by norm_num)
theorem B2808341 : Blo 1108626 2808341 := bbase (se 6 (by rfl) ⟨65820, by rfl⟩ : syracuseStep 2808341 = 131641) (by norm_num)
theorem B1333793 : Blo 1108626 1333793 := bbase (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) (by norm_num)
theorem B5626421 : Blo 1108626 5626421 := bbase (se 5 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 5626421 = 527477) (by norm_num)
theorem B5331557 : Blo 1108626 5331557 := bbase (se 4 (by rfl) ⟨499833, by rfl⟩ : syracuseStep 5331557 = 999667) (by norm_num)
theorem B1333865 : Blo 1108626 1333865 := bbase (se 2 (by rfl) ⟨500199, by rfl⟩ : syracuseStep 1333865 = 1000399) (by norm_num)
theorem B2808533 : Blo 1108626 2808533 := bbase (se 7 (by rfl) ⟨32912, by rfl⟩ : syracuseStep 2808533 = 65825) (by norm_num)
theorem B4741861 : Blo 1108626 4741861 := bbase (se 4 (by rfl) ⟨444549, by rfl⟩ : syracuseStep 4741861 = 889099) (by norm_num)
theorem B3562213 : Blo 1108626 3562213 := bbase (se 4 (by rfl) ⟨333957, by rfl⟩ : syracuseStep 3562213 = 667915) (by norm_num)
theorem B1334173 : Blo 1108626 1334173 := bbase (se 3 (by rfl) ⟨250157, by rfl⟩ : syracuseStep 1334173 = 500315) (by norm_num)
theorem B2808877 : Blo 1108626 2808877 := bbase (se 3 (by rfl) ⟨526664, by rfl⟩ : syracuseStep 2808877 = 1053329) (by norm_num)
theorem B5135413 : Blo 1108626 5135413 := bbase (se 5 (by rfl) ⟨240722, by rfl⟩ : syracuseStep 5135413 = 481445) (by norm_num)
theorem B1334341 : Blo 1108626 1334341 := bbase (se 4 (by rfl) ⟨125094, by rfl⟩ : syracuseStep 1334341 = 250189) (by norm_num)
theorem B5692517 : Blo 1108626 5692517 := bbase (se 4 (by rfl) ⟨533673, by rfl⟩ : syracuseStep 5692517 = 1067347) (by norm_num)
theorem B1334389 : Blo 1108626 1334389 := bbase (se 5 (by rfl) ⟨62549, by rfl⟩ : syracuseStep 1334389 = 125099) (by norm_num)
theorem B3562613 : Blo 1108626 3562613 := bbase (se 5 (by rfl) ⟨166997, by rfl⟩ : syracuseStep 3562613 = 333995) (by norm_num)
theorem B2808989 : Blo 1108626 2808989 := bbase (se 3 (by rfl) ⟨526685, by rfl⟩ : syracuseStep 2808989 = 1053371) (by norm_num)
theorem B1334485 : Blo 1108626 1334485 := bbase (se 7 (by rfl) ⟨15638, by rfl⟩ : syracuseStep 1334485 = 31277) (by norm_num)
theorem B4218101 : Blo 1108626 4218101 := bbase (se 5 (by rfl) ⟨197723, by rfl⟩ : syracuseStep 4218101 = 395447) (by norm_num)
theorem B2809181 : Blo 1108626 2809181 := bbase (se 3 (by rfl) ⟨526721, by rfl⟩ : syracuseStep 2809181 = 1053443) (by norm_num)
theorem B6315509 : Blo 1108626 6315509 := bbase (se 5 (by rfl) ⟨296039, by rfl⟩ : syracuseStep 6315509 = 592079) (by norm_num)
theorem B4218389 : Blo 1108626 4218389 := bbase (se 6 (by rfl) ⟨98868, by rfl⟩ : syracuseStep 4218389 = 197737) (by norm_num)
theorem B2252333 : Blo 1108626 2252333 := bbase (se 3 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 2252333 = 844625) (by norm_num)
theorem B2809525 : Blo 1108626 2809525 := bbase (se 5 (by rfl) ⟨131696, by rfl⟩ : syracuseStep 2809525 = 263393) (by norm_num)
theorem B1335061 : Blo 1108626 1335061 := bbase (se 6 (by rfl) ⟨31290, by rfl⟩ : syracuseStep 1335061 = 62581) (by norm_num)
theorem B2809637 : Blo 1108626 2809637 := bbase (se 4 (by rfl) ⟨263403, by rfl⟩ : syracuseStep 2809637 = 526807) (by norm_num)
theorem B5627717 : Blo 1108626 5627717 := bbase (se 4 (by rfl) ⟨527598, by rfl⟩ : syracuseStep 5627717 = 1055197) (by norm_num)
theorem B1662941 : Blo 1108626 1662941 := bbase (se 3 (by rfl) ⟨311801, by rfl⟩ : syracuseStep 1662941 = 623603) (by norm_num)
theorem B2809829 : Blo 1108626 2809829 := bbase (se 4 (by rfl) ⟨263421, by rfl⟩ : syracuseStep 2809829 = 526843) (by norm_num)
theorem B1662965 : Blo 1108626 1662965 := bbase (se 5 (by rfl) ⟨77951, by rfl⟩ : syracuseStep 1662965 = 155903) (by norm_num)
theorem B1662989 : Blo 1108626 1662989 := bbase (se 3 (by rfl) ⟨311810, by rfl⟩ : syracuseStep 1662989 = 623621) (by norm_num)
theorem B1663013 : Blo 1108626 1663013 := bbase (se 4 (by rfl) ⟨155907, by rfl⟩ : syracuseStep 1663013 = 311815) (by norm_num)
theorem B1663037 : Blo 1108626 1663037 := bbase (se 3 (by rfl) ⟨311819, by rfl⟩ : syracuseStep 1663037 = 623639) (by norm_num)
theorem B1663061 : Blo 1108626 1663061 := bbase (se 8 (by rfl) ⟨9744, by rfl⟩ : syracuseStep 1663061 = 19489) (by norm_num)
theorem B1663085 : Blo 1108626 1663085 := bbase (se 3 (by rfl) ⟨311828, by rfl⟩ : syracuseStep 1663085 = 623657) (by norm_num)
theorem B1663109 : Blo 1108626 1663109 := bbase (se 4 (by rfl) ⟨155916, by rfl⟩ : syracuseStep 1663109 = 311833) (by norm_num)
theorem B1663133 : Blo 1108626 1663133 := bbase (se 3 (by rfl) ⟨311837, by rfl⟩ : syracuseStep 1663133 = 623675) (by norm_num)
theorem B1663157 : Blo 1108626 1663157 := bbase (se 5 (by rfl) ⟨77960, by rfl⟩ : syracuseStep 1663157 = 155921) (by norm_num)
theorem B1663181 : Blo 1108626 1663181 := bbase (se 3 (by rfl) ⟨311846, by rfl⟩ : syracuseStep 1663181 = 623693) (by norm_num)
theorem B1663205 : Blo 1108626 1663205 := bbase (se 4 (by rfl) ⟨155925, by rfl⟩ : syracuseStep 1663205 = 311851) (by norm_num)
theorem B1663229 : Blo 1108626 1663229 := bbase (se 3 (by rfl) ⟨311855, by rfl⟩ : syracuseStep 1663229 = 623711) (by norm_num)
theorem B1663253 : Blo 1108626 1663253 := bbase (se 6 (by rfl) ⟨38982, by rfl⟩ : syracuseStep 1663253 = 77965) (by norm_num)
theorem B1564949 : Blo 1108626 1564949 := bbase (se 6 (by rfl) ⟨36678, by rfl⟩ : syracuseStep 1564949 = 73357) (by norm_num)
theorem B1663277 : Blo 1108626 1663277 := bbase (se 3 (by rfl) ⟨311864, by rfl⟩ : syracuseStep 1663277 = 623729) (by norm_num)
theorem B2810173 : Blo 1108626 2810173 := bbase (se 3 (by rfl) ⟨526907, by rfl⟩ : syracuseStep 2810173 = 1053815) (by norm_num)
theorem B1663301 : Blo 1108626 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B1663325 : Blo 1108626 1663325 := bbase (se 3 (by rfl) ⟨311873, by rfl⟩ : syracuseStep 1663325 = 623747) (by norm_num)
theorem B1663349 : Blo 1108626 1663349 := bbase (se 5 (by rfl) ⟨77969, by rfl⟩ : syracuseStep 1663349 = 155939) (by norm_num)
theorem B1663373 : Blo 1108626 1663373 := bbase (se 3 (by rfl) ⟨311882, by rfl⟩ : syracuseStep 1663373 = 623765) (by norm_num)
theorem B1663397 : Blo 1108626 1663397 := bbase (se 4 (by rfl) ⟨155943, by rfl⟩ : syracuseStep 1663397 = 311887) (by norm_num)
theorem B2810285 : Blo 1108626 2810285 := bbase (se 3 (by rfl) ⟨526928, by rfl⟩ : syracuseStep 2810285 = 1053857) (by norm_num)
theorem B1663421 : Blo 1108626 1663421 := bbase (se 3 (by rfl) ⟨311891, by rfl⟩ : syracuseStep 1663421 = 623783) (by norm_num)
theorem B1663445 : Blo 1108626 1663445 := bbase (se 7 (by rfl) ⟨19493, by rfl⟩ : syracuseStep 1663445 = 38987) (by norm_num)
theorem B1663469 : Blo 1108626 1663469 := bbase (se 3 (by rfl) ⟨311900, by rfl⟩ : syracuseStep 1663469 = 623801) (by norm_num)
theorem B1663493 : Blo 1108626 1663493 := bbase (se 4 (by rfl) ⟨155952, by rfl⟩ : syracuseStep 1663493 = 311905) (by norm_num)
theorem B1663517 : Blo 1108626 1663517 := bbase (se 3 (by rfl) ⟨311909, by rfl⟩ : syracuseStep 1663517 = 623819) (by norm_num)
theorem B1663541 : Blo 1108626 1663541 := bbase (se 5 (by rfl) ⟨77978, by rfl⟩ : syracuseStep 1663541 = 155957) (by norm_num)
theorem B1663565 : Blo 1108626 1663565 := bbase (se 3 (by rfl) ⟨311918, by rfl⟩ : syracuseStep 1663565 = 623837) (by norm_num)
theorem B1663589 : Blo 1108626 1663589 := bbase (se 4 (by rfl) ⟨155961, by rfl⟩ : syracuseStep 1663589 = 311923) (by norm_num)
theorem B2810477 : Blo 1108626 2810477 := bbase (se 3 (by rfl) ⟨526964, by rfl⟩ : syracuseStep 2810477 = 1053929) (by norm_num)
theorem B1663613 : Blo 1108626 1663613 := bbase (se 3 (by rfl) ⟨311927, by rfl⟩ : syracuseStep 1663613 = 623855) (by norm_num)
theorem B1663637 : Blo 1108626 1663637 := bbase (se 6 (by rfl) ⟨38991, by rfl⟩ : syracuseStep 1663637 = 77983) (by norm_num)
theorem B4809365 : Blo 1108626 4809365 := bbase (se 6 (by rfl) ⟨112719, by rfl⟩ : syracuseStep 4809365 = 225439) (by norm_num)
theorem B1663661 : Blo 1108626 1663661 := bbase (se 3 (by rfl) ⟨311936, by rfl⟩ : syracuseStep 1663661 = 623873) (by norm_num)
theorem B4219573 : Blo 1108626 4219573 := bbase (se 5 (by rfl) ⟨197792, by rfl⟩ : syracuseStep 4219573 = 395585) (by norm_num)
theorem B1663685 : Blo 1108626 1663685 := bbase (se 4 (by rfl) ⟨155970, by rfl⟩ : syracuseStep 1663685 = 311941) (by norm_num)
theorem B1663709 : Blo 1108626 1663709 := bbase (se 3 (by rfl) ⟨311945, by rfl⟩ : syracuseStep 1663709 = 623891) (by norm_num)
theorem B1663733 : Blo 1108626 1663733 := bbase (se 5 (by rfl) ⟨77987, by rfl⟩ : syracuseStep 1663733 = 155975) (by norm_num)
theorem B1336061 : Blo 1108626 1336061 := bbase (se 3 (by rfl) ⟨250511, by rfl⟩ : syracuseStep 1336061 = 501023) (by norm_num)
theorem B1663757 : Blo 1108626 1663757 := bbase (se 3 (by rfl) ⟨311954, by rfl⟩ : syracuseStep 1663757 = 623909) (by norm_num)
theorem B1663781 : Blo 1108626 1663781 := bbase (se 4 (by rfl) ⟨155979, by rfl⟩ : syracuseStep 1663781 = 311959) (by norm_num)
theorem B1336109 : Blo 1108626 1336109 := bbase (se 3 (by rfl) ⟨250520, by rfl⟩ : syracuseStep 1336109 = 501041) (by norm_num)
theorem B7103285 : Blo 1108626 7103285 := bbase (se 5 (by rfl) ⟨332966, by rfl⟩ : syracuseStep 7103285 = 665933) (by norm_num)
theorem B1663805 : Blo 1108626 1663805 := bbase (se 3 (by rfl) ⟨311963, by rfl⟩ : syracuseStep 1663805 = 623927) (by norm_num)
theorem B1663829 : Blo 1108626 1663829 := bbase (se 9 (by rfl) ⟨4874, by rfl⟩ : syracuseStep 1663829 = 9749) (by norm_num)
theorem B1663853 : Blo 1108626 1663853 := bbase (se 3 (by rfl) ⟨311972, by rfl⟩ : syracuseStep 1663853 = 623945) (by norm_num)
theorem B1663877 : Blo 1108626 1663877 := bbase (se 4 (by rfl) ⟨155988, by rfl⟩ : syracuseStep 1663877 = 311977) (by norm_num)
theorem B1663901 : Blo 1108626 1663901 := bbase (se 3 (by rfl) ⟨311981, by rfl⟩ : syracuseStep 1663901 = 623963) (by norm_num)
theorem B1663925 : Blo 1108626 1663925 := bbase (se 5 (by rfl) ⟨77996, by rfl⟩ : syracuseStep 1663925 = 155993) (by norm_num)
theorem B2810821 : Blo 1108626 2810821 := bbase (se 4 (by rfl) ⟨263514, by rfl⟩ : syracuseStep 2810821 = 527029) (by norm_num)
theorem B1663949 : Blo 1108626 1663949 := bbase (se 3 (by rfl) ⟨311990, by rfl⟩ : syracuseStep 1663949 = 623981) (by norm_num)
theorem B1663973 : Blo 1108626 1663973 := bbase (se 4 (by rfl) ⟨155997, by rfl⟩ : syracuseStep 1663973 = 311995) (by norm_num)
theorem B4219877 : Blo 1108626 4219877 := bbase (se 4 (by rfl) ⟨395613, by rfl⟩ : syracuseStep 4219877 = 791227) (by norm_num)
theorem B1663997 : Blo 1108626 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B1664021 : Blo 1108626 1664021 := bbase (se 6 (by rfl) ⟨39000, by rfl⟩ : syracuseStep 1664021 = 78001) (by norm_num)
theorem B1664045 : Blo 1108626 1664045 := bbase (se 3 (by rfl) ⟨312008, by rfl⟩ : syracuseStep 1664045 = 624017) (by norm_num)
theorem B2810933 : Blo 1108626 2810933 := bbase (se 5 (by rfl) ⟨131762, by rfl⟩ : syracuseStep 2810933 = 263525) (by norm_num)
theorem B1664069 : Blo 1108626 1664069 := bbase (se 4 (by rfl) ⟨156006, by rfl⟩ : syracuseStep 1664069 = 312013) (by norm_num)
theorem B5629013 : Blo 1108626 5629013 := bbase (se 8 (by rfl) ⟨32982, by rfl⟩ : syracuseStep 5629013 = 65965) (by norm_num)
theorem B1664093 : Blo 1108626 1664093 := bbase (se 3 (by rfl) ⟨312017, by rfl⟩ : syracuseStep 1664093 = 624035) (by norm_num)
theorem B1664117 : Blo 1108626 1664117 := bbase (se 5 (by rfl) ⟨78005, by rfl⟩ : syracuseStep 1664117 = 156011) (by norm_num)
theorem B1664141 : Blo 1108626 1664141 := bbase (se 3 (by rfl) ⟨312026, by rfl⟩ : syracuseStep 1664141 = 624053) (by norm_num)
theorem B1664165 : Blo 1108626 1664165 := bbase (se 4 (by rfl) ⟨156015, by rfl⟩ : syracuseStep 1664165 = 312031) (by norm_num)
theorem B1664189 : Blo 1108626 1664189 := bbase (se 3 (by rfl) ⟨312035, by rfl⟩ : syracuseStep 1664189 = 624071) (by norm_num)
theorem B1664213 : Blo 1108626 1664213 := bbase (se 7 (by rfl) ⟨19502, by rfl⟩ : syracuseStep 1664213 = 39005) (by norm_num)
theorem B1664237 : Blo 1108626 1664237 := bbase (se 3 (by rfl) ⟨312044, by rfl⟩ : syracuseStep 1664237 = 624089) (by norm_num)
theorem B2811125 : Blo 1108626 2811125 := bbase (se 5 (by rfl) ⟨131771, by rfl⟩ : syracuseStep 2811125 = 263543) (by norm_num)
theorem B1664261 : Blo 1108626 1664261 := bbase (se 4 (by rfl) ⟨156024, by rfl⟩ : syracuseStep 1664261 = 312049) (by norm_num)
theorem B1664285 : Blo 1108626 1664285 := bbase (se 3 (by rfl) ⟨312053, by rfl⟩ : syracuseStep 1664285 = 624107) (by norm_num)
theorem B1664309 : Blo 1108626 1664309 := bbase (se 5 (by rfl) ⟨78014, by rfl⟩ : syracuseStep 1664309 = 156029) (by norm_num)
theorem B1664333 : Blo 1108626 1664333 := bbase (se 3 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 1664333 = 624125) (by norm_num)
theorem B1336657 : Blo 1108626 1336657 := bbase (se 2 (by rfl) ⟨501246, by rfl⟩ : syracuseStep 1336657 = 1002493) (by norm_num)
theorem B1664357 : Blo 1108626 1664357 := bbase (se 4 (by rfl) ⟨156033, by rfl⟩ : syracuseStep 1664357 = 312067) (by norm_num)
theorem B1664381 : Blo 1108626 1664381 := bbase (se 3 (by rfl) ⟨312071, by rfl⟩ : syracuseStep 1664381 = 624143) (by norm_num)
theorem B1664405 : Blo 1108626 1664405 := bbase (se 6 (by rfl) ⟨39009, by rfl⟩ : syracuseStep 1664405 = 78019) (by norm_num)
theorem B1664429 : Blo 1108626 1664429 := bbase (se 3 (by rfl) ⟨312080, by rfl⟩ : syracuseStep 1664429 = 624161) (by norm_num)
theorem B1664453 : Blo 1108626 1664453 := bbase (se 4 (by rfl) ⟨156042, by rfl⟩ : syracuseStep 1664453 = 312085) (by norm_num)
theorem B1664477 : Blo 1108626 1664477 := bbase (se 3 (by rfl) ⟨312089, by rfl⟩ : syracuseStep 1664477 = 624179) (by norm_num)
theorem B1664501 : Blo 1108626 1664501 := bbase (se 5 (by rfl) ⟨78023, by rfl⟩ : syracuseStep 1664501 = 156047) (by norm_num)
theorem B1664525 : Blo 1108626 1664525 := bbase (se 3 (by rfl) ⟨312098, by rfl⟩ : syracuseStep 1664525 = 624197) (by norm_num)
theorem B1664549 : Blo 1108626 1664549 := bbase (se 4 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 1664549 = 312103) (by norm_num)
theorem B2745893 : Blo 1108626 2745893 := bbase (se 4 (by rfl) ⟨257427, by rfl⟩ : syracuseStep 2745893 = 514855) (by norm_num)
theorem B1664573 : Blo 1108626 1664573 := bbase (se 3 (by rfl) ⟨312107, by rfl⟩ : syracuseStep 1664573 = 624215) (by norm_num)
theorem B2811469 : Blo 1108626 2811469 := bbase (se 3 (by rfl) ⟨527150, by rfl⟩ : syracuseStep 2811469 = 1054301) (by norm_num)
theorem B1664597 : Blo 1108626 1664597 := bbase (se 8 (by rfl) ⟨9753, by rfl⟩ : syracuseStep 1664597 = 19507) (by norm_num)
theorem B1664621 : Blo 1108626 1664621 := bbase (se 3 (by rfl) ⟨312116, by rfl⟩ : syracuseStep 1664621 = 624233) (by norm_num)
theorem B1664645 : Blo 1108626 1664645 := bbase (se 4 (by rfl) ⟨156060, by rfl⟩ : syracuseStep 1664645 = 312121) (by norm_num)
theorem B1926805 : Blo 1108626 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B1664669 : Blo 1108626 1664669 := bbase (se 3 (by rfl) ⟨312125, by rfl⟩ : syracuseStep 1664669 = 624251) (by norm_num)
theorem B1664693 : Blo 1108626 1664693 := bbase (se 5 (by rfl) ⟨78032, by rfl⟩ : syracuseStep 1664693 = 156065) (by norm_num)
theorem B2811581 : Blo 1108626 2811581 := bbase (se 3 (by rfl) ⟨527171, by rfl⟩ : syracuseStep 2811581 = 1054343) (by norm_num)
theorem B1664717 : Blo 1108626 1664717 := bbase (se 3 (by rfl) ⟨312134, by rfl⟩ : syracuseStep 1664717 = 624269) (by norm_num)
theorem B1664741 : Blo 1108626 1664741 := bbase (se 4 (by rfl) ⟨156069, by rfl⟩ : syracuseStep 1664741 = 312139) (by norm_num)
theorem B1664765 : Blo 1108626 1664765 := bbase (se 3 (by rfl) ⟨312143, by rfl⟩ : syracuseStep 1664765 = 624287) (by norm_num)
theorem B1664789 : Blo 1108626 1664789 := bbase (se 6 (by rfl) ⟨39018, by rfl⟩ : syracuseStep 1664789 = 78037) (by norm_num)
theorem B1664813 : Blo 1108626 1664813 := bbase (se 3 (by rfl) ⟨312152, by rfl⟩ : syracuseStep 1664813 = 624305) (by norm_num)
theorem B1664837 : Blo 1108626 1664837 := bbase (se 4 (by rfl) ⟨156078, by rfl⟩ : syracuseStep 1664837 = 312157) (by norm_num)
theorem B1664861 : Blo 1108626 1664861 := bbase (se 3 (by rfl) ⟨312161, by rfl⟩ : syracuseStep 1664861 = 624323) (by norm_num)
theorem B1664885 : Blo 1108626 1664885 := bbase (se 5 (by rfl) ⟨78041, by rfl⟩ : syracuseStep 1664885 = 156083) (by norm_num)
theorem B2811773 : Blo 1108626 2811773 := bbase (se 3 (by rfl) ⟨527207, by rfl⟩ : syracuseStep 2811773 = 1054415) (by norm_num)
theorem B1664909 : Blo 1108626 1664909 := bbase (se 3 (by rfl) ⟨312170, by rfl⟩ : syracuseStep 1664909 = 624341) (by norm_num)
theorem B2254733 : Blo 1108626 2254733 := bbase (se 3 (by rfl) ⟨422762, by rfl⟩ : syracuseStep 2254733 = 845525) (by norm_num)
theorem B1664933 : Blo 1108626 1664933 := bbase (se 4 (by rfl) ⟨156087, by rfl⟩ : syracuseStep 1664933 = 312175) (by norm_num)
theorem B1664957 : Blo 1108626 1664957 := bbase (se 3 (by rfl) ⟨312179, by rfl⟩ : syracuseStep 1664957 = 624359) (by norm_num)
theorem B1664981 : Blo 1108626 1664981 := bbase (se 7 (by rfl) ⟨19511, by rfl⟩ : syracuseStep 1664981 = 39023) (by norm_num)
theorem B1665005 : Blo 1108626 1665005 := bbase (se 3 (by rfl) ⟨312188, by rfl⟩ : syracuseStep 1665005 = 624377) (by norm_num)
theorem B1665029 : Blo 1108626 1665029 := bbase (se 4 (by rfl) ⟨156096, by rfl⟩ : syracuseStep 1665029 = 312193) (by norm_num)
theorem B1665053 : Blo 1108626 1665053 := bbase (se 3 (by rfl) ⟨312197, by rfl⟩ : syracuseStep 1665053 = 624395) (by norm_num)
theorem B1665077 : Blo 1108626 1665077 := bbase (se 5 (by rfl) ⟨78050, by rfl⟩ : syracuseStep 1665077 = 156101) (by norm_num)
theorem B1665101 : Blo 1108626 1665101 := bbase (se 3 (by rfl) ⟨312206, by rfl⟩ : syracuseStep 1665101 = 624413) (by norm_num)
theorem B1665125 : Blo 1108626 1665125 := bbase (se 4 (by rfl) ⟨156105, by rfl⟩ : syracuseStep 1665125 = 312211) (by norm_num)
theorem B1665149 : Blo 1108626 1665149 := bbase (se 3 (by rfl) ⟨312215, by rfl⟩ : syracuseStep 1665149 = 624431) (by norm_num)
theorem B1665173 : Blo 1108626 1665173 := bbase (se 6 (by rfl) ⟨39027, by rfl⟩ : syracuseStep 1665173 = 78055) (by norm_num)
theorem B1665197 : Blo 1108626 1665197 := bbase (se 3 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 1665197 = 624449) (by norm_num)
theorem B1665221 : Blo 1108626 1665221 := bbase (se 4 (by rfl) ⟨156114, by rfl⟩ : syracuseStep 1665221 = 312229) (by norm_num)
theorem B2812117 : Blo 1108626 2812117 := bbase (se 7 (by rfl) ⟨32954, by rfl⟩ : syracuseStep 2812117 = 65909) (by norm_num)
theorem B1665245 : Blo 1108626 1665245 := bbase (se 3 (by rfl) ⟨312233, by rfl⟩ : syracuseStep 1665245 = 624467) (by norm_num)
theorem B1665269 : Blo 1108626 1665269 := bbase (se 5 (by rfl) ⟨78059, by rfl⟩ : syracuseStep 1665269 = 156119) (by norm_num)
theorem B1665293 : Blo 1108626 1665293 := bbase (se 3 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 1665293 = 624485) (by norm_num)
theorem B1403173 : Blo 1108626 1403173 := bbase (se 4 (by rfl) ⟨131547, by rfl⟩ : syracuseStep 1403173 = 263095) (by norm_num)
theorem B1665317 : Blo 1108626 1665317 := bbase (se 4 (by rfl) ⟨156123, by rfl⟩ : syracuseStep 1665317 = 312247) (by norm_num)
theorem B1665341 : Blo 1108626 1665341 := bbase (se 3 (by rfl) ⟨312251, by rfl⟩ : syracuseStep 1665341 = 624503) (by norm_num)
theorem B2812229 : Blo 1108626 2812229 := bbase (se 4 (by rfl) ⟨263646, by rfl⟩ : syracuseStep 2812229 = 527293) (by norm_num)
theorem B1665365 : Blo 1108626 1665365 := bbase (se 10 (by rfl) ⟨2439, by rfl⟩ : syracuseStep 1665365 = 4879) (by norm_num)
theorem B5630309 : Blo 1108626 5630309 := bbase (se 4 (by rfl) ⟨527841, by rfl⟩ : syracuseStep 5630309 = 1055683) (by norm_num)
theorem B1665389 : Blo 1108626 1665389 := bbase (se 3 (by rfl) ⟨312260, by rfl⟩ : syracuseStep 1665389 = 624521) (by norm_num)
theorem B1665413 : Blo 1108626 1665413 := bbase (se 4 (by rfl) ⟨156132, by rfl⟩ : syracuseStep 1665413 = 312265) (by norm_num)
theorem B1665437 : Blo 1108626 1665437 := bbase (se 3 (by rfl) ⟨312269, by rfl⟩ : syracuseStep 1665437 = 624539) (by norm_num)
theorem B1665461 : Blo 1108626 1665461 := bbase (se 5 (by rfl) ⟨78068, by rfl⟩ : syracuseStep 1665461 = 156137) (by norm_num)
theorem B1665485 : Blo 1108626 1665485 := bbase (se 3 (by rfl) ⟨312278, by rfl⟩ : syracuseStep 1665485 = 624557) (by norm_num)
theorem B1403345 : Blo 1108626 1403345 := bbase (se 2 (by rfl) ⟨526254, by rfl⟩ : syracuseStep 1403345 = 1052509) (by norm_num)
theorem B1665509 : Blo 1108626 1665509 := bbase (se 4 (by rfl) ⟨156141, by rfl⟩ : syracuseStep 1665509 = 312283) (by norm_num)
theorem B1665533 : Blo 1108626 1665533 := bbase (se 3 (by rfl) ⟨312287, by rfl⟩ : syracuseStep 1665533 = 624575) (by norm_num)
theorem B2812421 : Blo 1108626 2812421 := bbase (se 4 (by rfl) ⟨263664, by rfl⟩ : syracuseStep 2812421 = 527329) (by norm_num)
theorem B1403401 : Blo 1108626 1403401 := bbase (se 2 (by rfl) ⟨526275, by rfl⟩ : syracuseStep 1403401 = 1052551) (by norm_num)
theorem B1665557 : Blo 1108626 1665557 := bbase (se 6 (by rfl) ⟨39036, by rfl⟩ : syracuseStep 1665557 = 78073) (by norm_num)
theorem B1665581 : Blo 1108626 1665581 := bbase (se 3 (by rfl) ⟨312296, by rfl⟩ : syracuseStep 1665581 = 624593) (by norm_num)
theorem B1141301 : Blo 1108626 1141301 := bbase (se 5 (by rfl) ⟨53498, by rfl⟩ : syracuseStep 1141301 = 106997) (by norm_num)
theorem B1665605 : Blo 1108626 1665605 := bbase (se 4 (by rfl) ⟨156150, by rfl⟩ : syracuseStep 1665605 = 312301) (by norm_num)
theorem B1665629 : Blo 1108626 1665629 := bbase (se 3 (by rfl) ⟨312305, by rfl⟩ : syracuseStep 1665629 = 624611) (by norm_num)
theorem B1403497 : Blo 1108626 1403497 := bbase (se 2 (by rfl) ⟨526311, by rfl⟩ : syracuseStep 1403497 = 1052623) (by norm_num)
theorem B1665653 : Blo 1108626 1665653 := bbase (se 5 (by rfl) ⟨78077, by rfl⟩ : syracuseStep 1665653 = 156155) (by norm_num)
theorem B1665677 : Blo 1108626 1665677 := bbase (se 3 (by rfl) ⟨312314, by rfl⟩ : syracuseStep 1665677 = 624629) (by norm_num)
theorem B1665701 : Blo 1108626 1665701 := bbase (se 4 (by rfl) ⟨156159, by rfl⟩ : syracuseStep 1665701 = 312319) (by norm_num)
theorem B1665725 : Blo 1108626 1665725 := bbase (se 3 (by rfl) ⟨312323, by rfl⟩ : syracuseStep 1665725 = 624647) (by norm_num)
theorem B1665749 : Blo 1108626 1665749 := bbase (se 7 (by rfl) ⟨19520, by rfl⟩ : syracuseStep 1665749 = 39041) (by norm_num)
theorem B1665773 : Blo 1108626 1665773 := bbase (se 3 (by rfl) ⟨312332, by rfl⟩ : syracuseStep 1665773 = 624665) (by norm_num)
theorem B1665797 : Blo 1108626 1665797 := bbase (se 4 (by rfl) ⟨156168, by rfl⟩ : syracuseStep 1665797 = 312337) (by norm_num)
theorem B1403669 : Blo 1108626 1403669 := bbase (se 6 (by rfl) ⟨32898, by rfl⟩ : syracuseStep 1403669 = 65797) (by norm_num)
theorem B1665821 : Blo 1108626 1665821 := bbase (se 3 (by rfl) ⟨312341, by rfl⟩ : syracuseStep 1665821 = 624683) (by norm_num)
theorem B1665845 : Blo 1108626 1665845 := bbase (se 5 (by rfl) ⟨78086, by rfl⟩ : syracuseStep 1665845 = 156173) (by norm_num)
theorem B1403725 : Blo 1108626 1403725 := bbase (se 3 (by rfl) ⟨263198, by rfl⟩ : syracuseStep 1403725 = 526397) (by norm_num)
theorem B1665869 : Blo 1108626 1665869 := bbase (se 3 (by rfl) ⟨312350, by rfl⟩ : syracuseStep 1665869 = 624701) (by norm_num)
theorem B2812765 : Blo 1108626 2812765 := bbase (se 3 (by rfl) ⟨527393, by rfl⟩ : syracuseStep 2812765 = 1054787) (by norm_num)
theorem B1665893 : Blo 1108626 1665893 := bbase (se 4 (by rfl) ⟨156177, by rfl⟩ : syracuseStep 1665893 = 312355) (by norm_num)
theorem B1665917 : Blo 1108626 1665917 := bbase (se 3 (by rfl) ⟨312359, by rfl⟩ : syracuseStep 1665917 = 624719) (by norm_num)
theorem B1665941 : Blo 1108626 1665941 := bbase (se 6 (by rfl) ⟨39045, by rfl⟩ : syracuseStep 1665941 = 78091) (by norm_num)
theorem B1403821 : Blo 1108626 1403821 := bbase (se 3 (by rfl) ⟨263216, by rfl⟩ : syracuseStep 1403821 = 526433) (by norm_num)
theorem B1665965 : Blo 1108626 1665965 := bbase (se 3 (by rfl) ⟨312368, by rfl⟩ : syracuseStep 1665965 = 624737) (by norm_num)
theorem B1665989 : Blo 1108626 1665989 := bbase (se 4 (by rfl) ⟨156186, by rfl⟩ : syracuseStep 1665989 = 312373) (by norm_num)
theorem B2812877 : Blo 1108626 2812877 := bbase (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) (by norm_num)
theorem B1666013 : Blo 1108626 1666013 := bbase (se 3 (by rfl) ⟨312377, by rfl⟩ : syracuseStep 1666013 = 624755) (by norm_num)
theorem B1666037 : Blo 1108626 1666037 := bbase (se 5 (by rfl) ⟨78095, by rfl⟩ : syracuseStep 1666037 = 156191) (by norm_num)
theorem B1666061 : Blo 1108626 1666061 := bbase (se 3 (by rfl) ⟨312386, by rfl⟩ : syracuseStep 1666061 = 624773) (by norm_num)
theorem B1666085 : Blo 1108626 1666085 := bbase (se 4 (by rfl) ⟨156195, by rfl⟩ : syracuseStep 1666085 = 312391) (by norm_num)
theorem B4221989 : Blo 1108626 4221989 := bbase (se 4 (by rfl) ⟨395811, by rfl⟩ : syracuseStep 4221989 = 791623) (by norm_num)
theorem B1666109 : Blo 1108626 1666109 := bbase (se 3 (by rfl) ⟨312395, by rfl⟩ : syracuseStep 1666109 = 624791) (by norm_num)
theorem B1666133 : Blo 1108626 1666133 := bbase (se 8 (by rfl) ⟨9762, by rfl⟩ : syracuseStep 1666133 = 19525) (by norm_num)
theorem B1403993 : Blo 1108626 1403993 := bbase (se 2 (by rfl) ⟨526497, by rfl⟩ : syracuseStep 1403993 = 1052995) (by norm_num)
theorem B1666157 : Blo 1108626 1666157 := bbase (se 3 (by rfl) ⟨312404, by rfl⟩ : syracuseStep 1666157 = 624809) (by norm_num)
theorem B1666181 : Blo 1108626 1666181 := bbase (se 4 (by rfl) ⟨156204, by rfl⟩ : syracuseStep 1666181 = 312409) (by norm_num)
theorem B2813069 : Blo 1108626 2813069 := bbase (se 3 (by rfl) ⟨527450, by rfl⟩ : syracuseStep 2813069 = 1054901) (by norm_num)
theorem B1404049 : Blo 1108626 1404049 := bbase (se 2 (by rfl) ⟨526518, by rfl⟩ : syracuseStep 1404049 = 1053037) (by norm_num)
theorem B1666205 : Blo 1108626 1666205 := bbase (se 3 (by rfl) ⟨312413, by rfl⟩ : syracuseStep 1666205 = 624827) (by norm_num)
theorem B1666229 : Blo 1108626 1666229 := bbase (se 5 (by rfl) ⟨78104, by rfl⟩ : syracuseStep 1666229 = 156209) (by norm_num)
theorem B1666253 : Blo 1108626 1666253 := bbase (se 3 (by rfl) ⟨312422, by rfl⟩ : syracuseStep 1666253 = 624845) (by norm_num)
theorem B6745301 : Blo 1108626 6745301 := bbase (se 7 (by rfl) ⟨79046, by rfl⟩ : syracuseStep 6745301 = 158093) (by norm_num)
theorem B1666277 : Blo 1108626 1666277 := bbase (se 4 (by rfl) ⟨156213, by rfl⟩ : syracuseStep 1666277 = 312427) (by norm_num)
theorem B1404145 : Blo 1108626 1404145 := bbase (se 2 (by rfl) ⟨526554, by rfl⟩ : syracuseStep 1404145 = 1053109) (by norm_num)
theorem B1666301 : Blo 1108626 1666301 := bbase (se 3 (by rfl) ⟨312431, by rfl⟩ : syracuseStep 1666301 = 624863) (by norm_num)
theorem B1666325 : Blo 1108626 1666325 := bbase (se 6 (by rfl) ⟨39054, by rfl⟩ : syracuseStep 1666325 = 78109) (by norm_num)
theorem B1666349 : Blo 1108626 1666349 := bbase (se 3 (by rfl) ⟨312440, by rfl⟩ : syracuseStep 1666349 = 624881) (by norm_num)
theorem B1666373 : Blo 1108626 1666373 := bbase (se 4 (by rfl) ⟨156222, by rfl⟩ : syracuseStep 1666373 = 312445) (by norm_num)
theorem B4222277 : Blo 1108626 4222277 := bbase (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) (by norm_num)
theorem B1666397 : Blo 1108626 1666397 := bbase (se 3 (by rfl) ⟨312449, by rfl⟩ : syracuseStep 1666397 = 624899) (by norm_num)
theorem B1666421 : Blo 1108626 1666421 := bbase (se 5 (by rfl) ⟨78113, by rfl⟩ : syracuseStep 1666421 = 156227) (by norm_num)
theorem B1666445 : Blo 1108626 1666445 := bbase (se 3 (by rfl) ⟨312458, by rfl⟩ : syracuseStep 1666445 = 624917) (by norm_num)
theorem B9498005 : Blo 1108626 9498005 := bbase (se 6 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 9498005 = 445219) (by norm_num)
theorem B1404317 : Blo 1108626 1404317 := bbase (se 3 (by rfl) ⟨263309, by rfl⟩ : syracuseStep 1404317 = 526619) (by norm_num)
theorem B1666469 : Blo 1108626 1666469 := bbase (se 4 (by rfl) ⟨156231, by rfl⟩ : syracuseStep 1666469 = 312463) (by norm_num)
theorem B1666493 : Blo 1108626 1666493 := bbase (se 3 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 1666493 = 624935) (by norm_num)
theorem B1404373 : Blo 1108626 1404373 := bbase (se 7 (by rfl) ⟨16457, by rfl⟩ : syracuseStep 1404373 = 32915) (by norm_num)
theorem B1666517 : Blo 1108626 1666517 := bbase (se 7 (by rfl) ⟨19529, by rfl⟩ : syracuseStep 1666517 = 39059) (by norm_num)
theorem B2813413 : Blo 1108626 2813413 := bbase (se 4 (by rfl) ⟨263757, by rfl⟩ : syracuseStep 2813413 = 527515) (by norm_num)
theorem B1666541 : Blo 1108626 1666541 := bbase (se 3 (by rfl) ⟨312476, by rfl⟩ : syracuseStep 1666541 = 624953) (by norm_num)
theorem B1666565 : Blo 1108626 1666565 := bbase (se 4 (by rfl) ⟨156240, by rfl⟩ : syracuseStep 1666565 = 312481) (by norm_num)
theorem B1666589 : Blo 1108626 1666589 := bbase (se 3 (by rfl) ⟨312485, by rfl⟩ : syracuseStep 1666589 = 624971) (by norm_num)
theorem B1404469 : Blo 1108626 1404469 := bbase (se 5 (by rfl) ⟨65834, by rfl⟩ : syracuseStep 1404469 = 131669) (by norm_num)
theorem B1666613 : Blo 1108626 1666613 := bbase (se 5 (by rfl) ⟨78122, by rfl⟩ : syracuseStep 1666613 = 156245) (by norm_num)
theorem B1666637 : Blo 1108626 1666637 := bbase (se 3 (by rfl) ⟨312494, by rfl⟩ : syracuseStep 1666637 = 624989) (by norm_num)
theorem B2813525 : Blo 1108626 2813525 := bbase (se 8 (by rfl) ⟨16485, by rfl⟩ : syracuseStep 2813525 = 32971) (by norm_num)
theorem B1666661 : Blo 1108626 1666661 := bbase (se 4 (by rfl) ⟨156249, by rfl⟩ : syracuseStep 1666661 = 312499) (by norm_num)
theorem B4746869 : Blo 1108626 4746869 := bbase (se 5 (by rfl) ⟨222509, by rfl⟩ : syracuseStep 4746869 = 445019) (by norm_num)
theorem B5631605 : Blo 1108626 5631605 := bbase (se 5 (by rfl) ⟨263981, by rfl⟩ : syracuseStep 5631605 = 527963) (by norm_num)
theorem B1666685 : Blo 1108626 1666685 := bbase (se 3 (by rfl) ⟨312503, by rfl⟩ : syracuseStep 1666685 = 625007) (by norm_num)
theorem B1666709 : Blo 1108626 1666709 := bbase (se 6 (by rfl) ⟨39063, by rfl⟩ : syracuseStep 1666709 = 78127) (by norm_num)
theorem B1666733 : Blo 1108626 1666733 := bbase (se 3 (by rfl) ⟨312512, by rfl⟩ : syracuseStep 1666733 = 625025) (by norm_num)
theorem B1666757 : Blo 1108626 1666757 := bbase (se 4 (by rfl) ⟨156258, by rfl⟩ : syracuseStep 1666757 = 312517) (by norm_num)
theorem B1666781 : Blo 1108626 1666781 := bbase (se 3 (by rfl) ⟨312521, by rfl⟩ : syracuseStep 1666781 = 625043) (by norm_num)
theorem B1404641 : Blo 1108626 1404641 := bbase (se 2 (by rfl) ⟨526740, by rfl⟩ : syracuseStep 1404641 = 1053481) (by norm_num)
theorem B1666805 : Blo 1108626 1666805 := bbase (se 5 (by rfl) ⟨78131, by rfl⟩ : syracuseStep 1666805 = 156263) (by norm_num)
theorem B1666829 : Blo 1108626 1666829 := bbase (se 3 (by rfl) ⟨312530, by rfl⟩ : syracuseStep 1666829 = 625061) (by norm_num)
theorem B2813717 : Blo 1108626 2813717 := bbase (se 6 (by rfl) ⟨65946, by rfl⟩ : syracuseStep 2813717 = 131893) (by norm_num)
theorem B1404697 : Blo 1108626 1404697 := bbase (se 2 (by rfl) ⟨526761, by rfl⟩ : syracuseStep 1404697 = 1053523) (by norm_num)
theorem B1666853 : Blo 1108626 1666853 := bbase (se 4 (by rfl) ⟨156267, by rfl⟩ : syracuseStep 1666853 = 312535) (by norm_num)
theorem B1666877 : Blo 1108626 1666877 := bbase (se 3 (by rfl) ⟨312539, by rfl⟩ : syracuseStep 1666877 = 625079) (by norm_num)
theorem B5074757 : Blo 1108626 5074757 := bbase (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) (by norm_num)
theorem B1666901 : Blo 1108626 1666901 := bbase (se 9 (by rfl) ⟨4883, by rfl⟩ : syracuseStep 1666901 = 9767) (by norm_num)
theorem B1929053 : Blo 1108626 1929053 := bbase (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) (by norm_num)
theorem B1666925 : Blo 1108626 1666925 := bbase (se 3 (by rfl) ⟨312548, by rfl⟩ : syracuseStep 1666925 = 625097) (by norm_num)
theorem B1404793 : Blo 1108626 1404793 := bbase (se 2 (by rfl) ⟨526797, by rfl⟩ : syracuseStep 1404793 = 1053595) (by norm_num)
theorem B1666949 : Blo 1108626 1666949 := bbase (se 4 (by rfl) ⟨156276, by rfl⟩ : syracuseStep 1666949 = 312553) (by norm_num)
theorem B4747157 : Blo 1108626 4747157 := bbase (se 6 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 4747157 = 222523) (by norm_num)
theorem B1666973 : Blo 1108626 1666973 := bbase (se 3 (by rfl) ⟨312557, by rfl⟩ : syracuseStep 1666973 = 625115) (by norm_num)
theorem B1666997 : Blo 1108626 1666997 := bbase (se 5 (by rfl) ⟨78140, by rfl⟩ : syracuseStep 1666997 = 156281) (by norm_num)
theorem B1667021 : Blo 1108626 1667021 := bbase (se 3 (by rfl) ⟨312566, by rfl⟩ : syracuseStep 1667021 = 625133) (by norm_num)
theorem B1667045 : Blo 1108626 1667045 := bbase (se 4 (by rfl) ⟨156285, by rfl⟩ : syracuseStep 1667045 = 312571) (by norm_num)
theorem B1667069 : Blo 1108626 1667069 := bbase (se 3 (by rfl) ⟨312575, by rfl⟩ : syracuseStep 1667069 = 625151) (by norm_num)
theorem B1667093 : Blo 1108626 1667093 := bbase (se 6 (by rfl) ⟨39072, by rfl⟩ : syracuseStep 1667093 = 78145) (by norm_num)
theorem B2846749 : Blo 1108626 2846749 := bbase (se 3 (by rfl) ⟨533765, by rfl⟩ : syracuseStep 2846749 = 1067531) (by norm_num)
theorem B1404965 : Blo 1108626 1404965 := bbase (se 4 (by rfl) ⟨131715, by rfl⟩ : syracuseStep 1404965 = 263431) (by norm_num)
theorem B1667117 : Blo 1108626 1667117 := bbase (se 3 (by rfl) ⟨312584, by rfl⟩ : syracuseStep 1667117 = 625169) (by norm_num)
theorem B1667141 : Blo 1108626 1667141 := bbase (se 4 (by rfl) ⟨156294, by rfl⟩ : syracuseStep 1667141 = 312589) (by norm_num)
theorem B1405021 : Blo 1108626 1405021 := bbase (se 3 (by rfl) ⟨263441, by rfl⟩ : syracuseStep 1405021 = 526883) (by norm_num)
theorem B1667165 : Blo 1108626 1667165 := bbase (se 3 (by rfl) ⟨312593, by rfl⟩ : syracuseStep 1667165 = 625187) (by norm_num)
theorem B2814061 : Blo 1108626 2814061 := bbase (se 3 (by rfl) ⟨527636, by rfl⟩ : syracuseStep 2814061 = 1055273) (by norm_num)
theorem B1667189 : Blo 1108626 1667189 := bbase (se 5 (by rfl) ⟨78149, by rfl⟩ : syracuseStep 1667189 = 156299) (by norm_num)
theorem B1667213 : Blo 1108626 1667213 := bbase (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) (by norm_num)
theorem B1667237 : Blo 1108626 1667237 := bbase (se 4 (by rfl) ⟨156303, by rfl⟩ : syracuseStep 1667237 = 312607) (by norm_num)
theorem B1896629 : Blo 1108626 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B1405117 : Blo 1108626 1405117 := bbase (se 3 (by rfl) ⟨263459, by rfl⟩ : syracuseStep 1405117 = 526919) (by norm_num)
theorem B1667261 : Blo 1108626 1667261 := bbase (se 3 (by rfl) ⟨312611, by rfl⟩ : syracuseStep 1667261 = 625223) (by norm_num)
theorem B1667285 : Blo 1108626 1667285 := bbase (se 7 (by rfl) ⟨19538, by rfl⟩ : syracuseStep 1667285 = 39077) (by norm_num)
theorem B2814173 : Blo 1108626 2814173 := bbase (se 3 (by rfl) ⟨527657, by rfl⟩ : syracuseStep 2814173 = 1055315) (by norm_num)
theorem B1667309 : Blo 1108626 1667309 := bbase (se 3 (by rfl) ⟨312620, by rfl⟩ : syracuseStep 1667309 = 625241) (by norm_num)
theorem B1503469 : Blo 1108626 1503469 := bbase (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) (by norm_num)
theorem B1667333 : Blo 1108626 1667333 := bbase (se 4 (by rfl) ⟨156312, by rfl⟩ : syracuseStep 1667333 = 312625) (by norm_num)
theorem B1667357 : Blo 1108626 1667357 := bbase (se 3 (by rfl) ⟨312629, by rfl⟩ : syracuseStep 1667357 = 625259) (by norm_num)
theorem B1667381 : Blo 1108626 1667381 := bbase (se 5 (by rfl) ⟨78158, by rfl⟩ : syracuseStep 1667381 = 156317) (by norm_num)
theorem B1667405 : Blo 1108626 1667405 := bbase (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) (by norm_num)
theorem B1667429 : Blo 1108626 1667429 := bbase (se 4 (by rfl) ⟨156321, by rfl⟩ : syracuseStep 1667429 = 312643) (by norm_num)
theorem B1405289 : Blo 1108626 1405289 := bbase (se 2 (by rfl) ⟨526983, by rfl⟩ : syracuseStep 1405289 = 1053967) (by norm_num)
theorem B1667453 : Blo 1108626 1667453 := bbase (se 3 (by rfl) ⟨312647, by rfl⟩ : syracuseStep 1667453 = 625295) (by norm_num)
theorem B1667477 : Blo 1108626 1667477 := bbase (se 6 (by rfl) ⟨39081, by rfl⟩ : syracuseStep 1667477 = 78163) (by norm_num)
theorem B2814365 : Blo 1108626 2814365 := bbase (se 3 (by rfl) ⟨527693, by rfl⟩ : syracuseStep 2814365 = 1055387) (by norm_num)
theorem B1405345 : Blo 1108626 1405345 := bbase (se 2 (by rfl) ⟨527004, by rfl⟩ : syracuseStep 1405345 = 1054009) (by norm_num)
theorem B1667501 : Blo 1108626 1667501 := bbase (se 3 (by rfl) ⟨312656, by rfl⟩ : syracuseStep 1667501 = 625313) (by norm_num)
theorem B1667525 : Blo 1108626 1667525 := bbase (se 4 (by rfl) ⟨156330, by rfl⟩ : syracuseStep 1667525 = 312661) (by norm_num)
theorem B1667549 : Blo 1108626 1667549 := bbase (se 3 (by rfl) ⟨312665, by rfl⟩ : syracuseStep 1667549 = 625331) (by norm_num)
theorem B4223461 : Blo 1108626 4223461 := bbase (se 4 (by rfl) ⟨395949, by rfl⟩ : syracuseStep 4223461 = 791899) (by norm_num)
theorem B1667573 : Blo 1108626 1667573 := bbase (se 5 (by rfl) ⟨78167, by rfl⟩ : syracuseStep 1667573 = 156335) (by norm_num)
theorem B1405441 : Blo 1108626 1405441 := bbase (se 2 (by rfl) ⟨527040, by rfl⟩ : syracuseStep 1405441 = 1054081) (by norm_num)
theorem B1667597 : Blo 1108626 1667597 := bbase (se 3 (by rfl) ⟨312674, by rfl⟩ : syracuseStep 1667597 = 625349) (by norm_num)
theorem B1667621 : Blo 1108626 1667621 := bbase (se 4 (by rfl) ⟨156339, by rfl⟩ : syracuseStep 1667621 = 312679) (by norm_num)
theorem B1667645 : Blo 1108626 1667645 := bbase (se 3 (by rfl) ⟨312683, by rfl⟩ : syracuseStep 1667645 = 625367) (by norm_num)
theorem B1667669 : Blo 1108626 1667669 := bbase (se 8 (by rfl) ⟨9771, by rfl⟩ : syracuseStep 1667669 = 19543) (by norm_num)
theorem B1667693 : Blo 1108626 1667693 := bbase (se 3 (by rfl) ⟨312692, by rfl⟩ : syracuseStep 1667693 = 625385) (by norm_num)
theorem B5403269 : Blo 1108626 5403269 := bbase (se 4 (by rfl) ⟨506556, by rfl⟩ : syracuseStep 5403269 = 1013113) (by norm_num)
theorem B4747909 : Blo 1108626 4747909 := bbase (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) (by norm_num)
theorem B1667717 : Blo 1108626 1667717 := bbase (se 4 (by rfl) ⟨156348, by rfl⟩ : syracuseStep 1667717 = 312697) (by norm_num)
theorem B1667741 : Blo 1108626 1667741 := bbase (se 3 (by rfl) ⟨312701, by rfl⟩ : syracuseStep 1667741 = 625403) (by norm_num)
theorem B1405613 : Blo 1108626 1405613 := bbase (se 3 (by rfl) ⟨263552, by rfl⟩ : syracuseStep 1405613 = 527105) (by norm_num)
theorem B1667765 : Blo 1108626 1667765 := bbase (se 5 (by rfl) ⟨78176, by rfl⟩ : syracuseStep 1667765 = 156353) (by norm_num)
theorem B1667789 : Blo 1108626 1667789 := bbase (se 3 (by rfl) ⟨312710, by rfl⟩ : syracuseStep 1667789 = 625421) (by norm_num)
theorem B1405669 : Blo 1108626 1405669 := bbase (se 4 (by rfl) ⟨131781, by rfl⟩ : syracuseStep 1405669 = 263563) (by norm_num)
theorem B1667813 : Blo 1108626 1667813 := bbase (se 4 (by rfl) ⟨156357, by rfl⟩ : syracuseStep 1667813 = 312715) (by norm_num)
theorem B2814709 : Blo 1108626 2814709 := bbase (se 5 (by rfl) ⟨131939, by rfl⟩ : syracuseStep 2814709 = 263879) (by norm_num)
theorem B1667837 : Blo 1108626 1667837 := bbase (se 3 (by rfl) ⟨312719, by rfl⟩ : syracuseStep 1667837 = 625439) (by norm_num)
theorem B1667861 : Blo 1108626 1667861 := bbase (se 6 (by rfl) ⟨39090, by rfl⟩ : syracuseStep 1667861 = 78181) (by norm_num)
theorem B4223765 : Blo 1108626 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B1667885 : Blo 1108626 1667885 := bbase (se 3 (by rfl) ⟨312728, by rfl⟩ : syracuseStep 1667885 = 625457) (by norm_num)
theorem B5206837 : Blo 1108626 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B1405765 : Blo 1108626 1405765 := bbase (se 4 (by rfl) ⟨131790, by rfl⟩ : syracuseStep 1405765 = 263581) (by norm_num)
theorem B1667909 : Blo 1108626 1667909 := bbase (se 4 (by rfl) ⟨156366, by rfl⟩ : syracuseStep 1667909 = 312733) (by norm_num)
theorem B1667933 : Blo 1108626 1667933 := bbase (se 3 (by rfl) ⟨312737, by rfl⟩ : syracuseStep 1667933 = 625475) (by norm_num)
theorem B2814821 : Blo 1108626 2814821 := bbase (se 4 (by rfl) ⟨263889, by rfl⟩ : syracuseStep 2814821 = 527779) (by norm_num)
theorem B1667957 : Blo 1108626 1667957 := bbase (se 5 (by rfl) ⟨78185, by rfl⟩ : syracuseStep 1667957 = 156371) (by norm_num)
theorem B1667981 : Blo 1108626 1667981 := bbase (se 3 (by rfl) ⟨312746, by rfl⟩ : syracuseStep 1667981 = 625493) (by norm_num)
theorem B1668005 : Blo 1108626 1668005 := bbase (se 4 (by rfl) ⟨156375, by rfl⟩ : syracuseStep 1668005 = 312751) (by norm_num)
theorem B1668029 : Blo 1108626 1668029 := bbase (se 3 (by rfl) ⟨312755, by rfl⟩ : syracuseStep 1668029 = 625511) (by norm_num)
theorem B3601349 : Blo 1108626 3601349 := bbase (se 4 (by rfl) ⟨337626, by rfl⟩ : syracuseStep 3601349 = 675253) (by norm_num)
theorem B1668053 : Blo 1108626 1668053 := bbase (se 7 (by rfl) ⟨19547, by rfl⟩ : syracuseStep 1668053 = 39095) (by norm_num)
theorem B1668077 : Blo 1108626 1668077 := bbase (se 3 (by rfl) ⟨312764, by rfl⟩ : syracuseStep 1668077 = 625529) (by norm_num)
theorem B1405937 : Blo 1108626 1405937 := bbase (se 2 (by rfl) ⟨527226, by rfl⟩ : syracuseStep 1405937 = 1054453) (by norm_num)
theorem B1668101 : Blo 1108626 1668101 := bbase (se 4 (by rfl) ⟨156384, by rfl⟩ : syracuseStep 1668101 = 312769) (by norm_num)
theorem B5338133 : Blo 1108626 5338133 := bbase (se 6 (by rfl) ⟨125112, by rfl⟩ : syracuseStep 5338133 = 250225) (by norm_num)
theorem B1668125 : Blo 1108626 1668125 := bbase (se 3 (by rfl) ⟨312773, by rfl⟩ : syracuseStep 1668125 = 625547) (by norm_num)
theorem B2815013 : Blo 1108626 2815013 := bbase (se 4 (by rfl) ⟨263907, by rfl⟩ : syracuseStep 2815013 = 527815) (by norm_num)
theorem B1405993 : Blo 1108626 1405993 := bbase (se 2 (by rfl) ⟨527247, by rfl⟩ : syracuseStep 1405993 = 1054495) (by norm_num)
theorem B1668149 : Blo 1108626 1668149 := bbase (se 5 (by rfl) ⟨78194, by rfl⟩ : syracuseStep 1668149 = 156389) (by norm_num)
theorem B1668173 : Blo 1108626 1668173 := bbase (se 3 (by rfl) ⟨312782, by rfl⟩ : syracuseStep 1668173 = 625565) (by norm_num)
theorem B1897573 : Blo 1108626 1897573 := bbase (se 4 (by rfl) ⟨177897, by rfl⟩ : syracuseStep 1897573 = 355795) (by norm_num)
theorem B1668197 : Blo 1108626 1668197 := bbase (se 4 (by rfl) ⟨156393, by rfl⟩ : syracuseStep 1668197 = 312787) (by norm_num)
theorem B1668221 : Blo 1108626 1668221 := bbase (se 3 (by rfl) ⟨312791, by rfl⟩ : syracuseStep 1668221 = 625583) (by norm_num)
theorem B1406089 : Blo 1108626 1406089 := bbase (se 2 (by rfl) ⟨527283, by rfl⟩ : syracuseStep 1406089 = 1054567) (by norm_num)
theorem B1668245 : Blo 1108626 1668245 := bbase (se 6 (by rfl) ⟨39099, by rfl⟩ : syracuseStep 1668245 = 78199) (by norm_num)
theorem B1668269 : Blo 1108626 1668269 := bbase (se 3 (by rfl) ⟨312800, by rfl⟩ : syracuseStep 1668269 = 625601) (by norm_num)
theorem B1668293 : Blo 1108626 1668293 := bbase (se 4 (by rfl) ⟨156402, by rfl⟩ : syracuseStep 1668293 = 312805) (by norm_num)
theorem B1668317 : Blo 1108626 1668317 := bbase (se 3 (by rfl) ⟨312809, by rfl⟩ : syracuseStep 1668317 = 625619) (by norm_num)
theorem B1668341 : Blo 1108626 1668341 := bbase (se 5 (by rfl) ⟨78203, by rfl⟩ : syracuseStep 1668341 = 156407) (by norm_num)
theorem B1668365 : Blo 1108626 1668365 := bbase (se 3 (by rfl) ⟨312818, by rfl⟩ : syracuseStep 1668365 = 625637) (by norm_num)
theorem B1668389 : Blo 1108626 1668389 := bbase (se 4 (by rfl) ⟨156411, by rfl⟩ : syracuseStep 1668389 = 312823) (by norm_num)
theorem B1406261 : Blo 1108626 1406261 := bbase (se 5 (by rfl) ⟨65918, by rfl⟩ : syracuseStep 1406261 = 131837) (by norm_num)
theorem B1668413 : Blo 1108626 1668413 := bbase (se 3 (by rfl) ⟨312827, by rfl⟩ : syracuseStep 1668413 = 625655) (by norm_num)
theorem B1668437 : Blo 1108626 1668437 := bbase (se 13 (by rfl) ⟨305, by rfl⟩ : syracuseStep 1668437 = 611) (by norm_num)
theorem B4748645 : Blo 1108626 4748645 := bbase (se 4 (by rfl) ⟨445185, by rfl⟩ : syracuseStep 4748645 = 890371) (by norm_num)
theorem B1406317 : Blo 1108626 1406317 := bbase (se 3 (by rfl) ⟨263684, by rfl⟩ : syracuseStep 1406317 = 527369) (by norm_num)
theorem B1668461 : Blo 1108626 1668461 := bbase (se 3 (by rfl) ⟨312836, by rfl⟩ : syracuseStep 1668461 = 625673) (by norm_num)
theorem B2815357 : Blo 1108626 2815357 := bbase (se 3 (by rfl) ⟨527879, by rfl⟩ : syracuseStep 2815357 = 1055759) (by norm_num)
theorem B1668485 : Blo 1108626 1668485 := bbase (se 4 (by rfl) ⟨156420, by rfl⟩ : syracuseStep 1668485 = 312841) (by norm_num)
theorem B1668509 : Blo 1108626 1668509 := bbase (se 3 (by rfl) ⟨312845, by rfl⟩ : syracuseStep 1668509 = 625691) (by norm_num)
theorem B1668533 : Blo 1108626 1668533 := bbase (se 5 (by rfl) ⟨78212, by rfl⟩ : syracuseStep 1668533 = 156425) (by norm_num)
theorem B1406413 : Blo 1108626 1406413 := bbase (se 3 (by rfl) ⟨263702, by rfl⟩ : syracuseStep 1406413 = 527405) (by norm_num)
theorem B1668557 : Blo 1108626 1668557 := bbase (se 3 (by rfl) ⟨312854, by rfl⟩ : syracuseStep 1668557 = 625709) (by norm_num)
theorem B1668581 : Blo 1108626 1668581 := bbase (se 4 (by rfl) ⟨156429, by rfl⟩ : syracuseStep 1668581 = 312859) (by norm_num)
theorem B2815469 : Blo 1108626 2815469 := bbase (se 3 (by rfl) ⟨527900, by rfl⟩ : syracuseStep 2815469 = 1055801) (by norm_num)
theorem B1668605 : Blo 1108626 1668605 := bbase (se 3 (by rfl) ⟨312863, by rfl⟩ : syracuseStep 1668605 = 625727) (by norm_num)
theorem B1668629 : Blo 1108626 1668629 := bbase (se 6 (by rfl) ⟨39108, by rfl⟩ : syracuseStep 1668629 = 78217) (by norm_num)
theorem B1668653 : Blo 1108626 1668653 := bbase (se 3 (by rfl) ⟨312872, by rfl⟩ : syracuseStep 1668653 = 625745) (by norm_num)
theorem B1668677 : Blo 1108626 1668677 := bbase (se 4 (by rfl) ⟨156438, by rfl⟩ : syracuseStep 1668677 = 312877) (by norm_num)
theorem B1668701 : Blo 1108626 1668701 := bbase (se 3 (by rfl) ⟨312881, by rfl⟩ : syracuseStep 1668701 = 625763) (by norm_num)
theorem B1898101 : Blo 1108626 1898101 := bbase (se 5 (by rfl) ⟨88973, by rfl⟩ : syracuseStep 1898101 = 177947) (by norm_num)
theorem B1668725 : Blo 1108626 1668725 := bbase (se 5 (by rfl) ⟨78221, by rfl⟩ : syracuseStep 1668725 = 156443) (by norm_num)
theorem B1406585 : Blo 1108626 1406585 := bbase (se 2 (by rfl) ⟨527469, by rfl⟩ : syracuseStep 1406585 = 1054939) (by norm_num)
theorem B1668749 : Blo 1108626 1668749 := bbase (se 3 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 1668749 = 625781) (by norm_num)
theorem B1668773 : Blo 1108626 1668773 := bbase (se 4 (by rfl) ⟨156447, by rfl⟩ : syracuseStep 1668773 = 312895) (by norm_num)
theorem B2815661 : Blo 1108626 2815661 := bbase (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) (by norm_num)
theorem B1406641 : Blo 1108626 1406641 := bbase (se 2 (by rfl) ⟨527490, by rfl⟩ : syracuseStep 1406641 = 1054981) (by norm_num)
theorem B1668797 : Blo 1108626 1668797 := bbase (se 3 (by rfl) ⟨312899, by rfl⟩ : syracuseStep 1668797 = 625799) (by norm_num)
theorem B1668821 : Blo 1108626 1668821 := bbase (se 7 (by rfl) ⟨19556, by rfl⟩ : syracuseStep 1668821 = 39113) (by norm_num)
theorem B1668845 : Blo 1108626 1668845 := bbase (se 3 (by rfl) ⟨312908, by rfl⟩ : syracuseStep 1668845 = 625817) (by norm_num)
theorem B1668869 : Blo 1108626 1668869 := bbase (se 4 (by rfl) ⟨156456, by rfl⟩ : syracuseStep 1668869 = 312913) (by norm_num)
theorem B1406737 : Blo 1108626 1406737 := bbase (se 2 (by rfl) ⟨527526, by rfl⟩ : syracuseStep 1406737 = 1055053) (by norm_num)
theorem B1668893 : Blo 1108626 1668893 := bbase (se 3 (by rfl) ⟨312917, by rfl⟩ : syracuseStep 1668893 = 625835) (by norm_num)
theorem B1668917 : Blo 1108626 1668917 := bbase (se 5 (by rfl) ⟨78230, by rfl⟩ : syracuseStep 1668917 = 156461) (by norm_num)
theorem B1406909 : Blo 1108626 1406909 := bbase (se 3 (by rfl) ⟨263795, by rfl⟩ : syracuseStep 1406909 = 527591) (by norm_num)
theorem B1406965 : Blo 1108626 1406965 := bbase (se 5 (by rfl) ⟨65951, by rfl⟩ : syracuseStep 1406965 = 131903) (by norm_num)
theorem B2816005 : Blo 1108626 2816005 := bbase (se 4 (by rfl) ⟨264000, by rfl⟩ : syracuseStep 2816005 = 528001) (by norm_num)
theorem B1407061 : Blo 1108626 1407061 := bbase (se 8 (by rfl) ⟨8244, by rfl⟩ : syracuseStep 1407061 = 16489) (by norm_num)
theorem B2816117 : Blo 1108626 2816117 := bbase (se 5 (by rfl) ⟨132005, by rfl⟩ : syracuseStep 2816117 = 264011) (by norm_num)
theorem B1407233 : Blo 1108626 1407233 := bbase (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) (by norm_num)
theorem B3995957 : Blo 1108626 3995957 := bbase (se 5 (by rfl) ⟨187310, by rfl⟩ : syracuseStep 3995957 = 374621) (by norm_num)
theorem B2816309 : Blo 1108626 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B1407289 : Blo 1108626 1407289 := bbase (se 2 (by rfl) ⟨527733, by rfl⟩ : syracuseStep 1407289 = 1055467) (by norm_num)
theorem B1407385 : Blo 1108626 1407385 := bbase (se 2 (by rfl) ⟨527769, by rfl⟩ : syracuseStep 1407385 = 1055539) (by norm_num)
theorem B2849213 : Blo 1108626 2849213 := bbase (se 3 (by rfl) ⟨534227, by rfl⟩ : syracuseStep 2849213 = 1068455) (by norm_num)
theorem B1407557 : Blo 1108626 1407557 := bbase (se 4 (by rfl) ⟨131958, by rfl⟩ : syracuseStep 1407557 = 263917) (by norm_num)
theorem B1800797 : Blo 1108626 1800797 := bbase (se 3 (by rfl) ⟨337649, by rfl⟩ : syracuseStep 1800797 = 675299) (by norm_num)
theorem B1407613 : Blo 1108626 1407613 := bbase (se 3 (by rfl) ⟨263927, by rfl⟩ : syracuseStep 1407613 = 527855) (by norm_num)
theorem B1407709 : Blo 1108626 1407709 := bbase (se 3 (by rfl) ⟨263945, by rfl⟩ : syracuseStep 1407709 = 527891) (by norm_num)
theorem B1604437 : Blo 1108626 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B1407881 : Blo 1108626 1407881 := bbase (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) (by norm_num)
theorem B1407937 : Blo 1108626 1407937 := bbase (se 2 (by rfl) ⟨527976, by rfl⟩ : syracuseStep 1407937 = 1055953) (by norm_num)
theorem B1997821 : Blo 1108626 1997821 := bbase (se 3 (by rfl) ⟨374591, by rfl⟩ : syracuseStep 1997821 = 749183) (by norm_num)
theorem B1408033 : Blo 1108626 1408033 := bbase (se 2 (by rfl) ⟨528012, by rfl⟩ : syracuseStep 1408033 = 1056025) (by norm_num)
theorem B1997893 : Blo 1108626 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B2849869 : Blo 1108626 2849869 := bbase (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) (by norm_num)
theorem B1998037 : Blo 1108626 1998037 := bbase (se 7 (by rfl) ⟨23414, by rfl⟩ : syracuseStep 1998037 = 46829) (by norm_num)
theorem B3604117 : Blo 1108626 3604117 := bbase (se 6 (by rfl) ⟨84471, by rfl⟩ : syracuseStep 3604117 = 168943) (by norm_num)
theorem B3374789 : Blo 1108626 3374789 := bbase (se 4 (by rfl) ⟨316386, by rfl⟩ : syracuseStep 3374789 = 632773) (by norm_num)
theorem B12648149 : Blo 1108626 12648149 := bbase (se 7 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 12648149 = 296441) (by norm_num)
theorem B3211093 : Blo 1108626 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B12189653 : Blo 1108626 12189653 := bbase (se 7 (by rfl) ⟨142847, by rfl⟩ : syracuseStep 12189653 = 285695) (by norm_num)
theorem B5701859 : Blo 1108626 5701859 := bstep (se 1 (by rfl) ⟨4276394, by rfl⟩ : syracuseStep 5701859 = 8552789) B8552789
theorem B3375569 : Blo 1108626 3375569 := bstep (se 2 (by rfl) ⟨1265838, by rfl⟩ : syracuseStep 3375569 = 2531677) B2531677
theorem B15172109 : Blo 1108626 15172109 := bstep (se 3 (by rfl) ⟨2844770, by rfl⟩ : syracuseStep 15172109 = 5689541) B5689541
theorem B38994659 : Blo 1108626 38994659 := bstep (se 1 (by rfl) ⟨29245994, by rfl⟩ : syracuseStep 38994659 = 58491989) B58491989
theorem B1999651 : Blo 1108626 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B2163665 : Blo 1108626 2163665 := bstep (se 2 (by rfl) ⟨811374, by rfl⟩ : syracuseStep 2163665 = 1622749) B1622749
theorem B1901665 : Blo 1108626 1901665 := bstep (se 2 (by rfl) ⟨713124, by rfl⟩ : syracuseStep 1901665 = 1426249) B1426249
theorem B2852081 : Blo 1108626 2852081 := bstep (se 2 (by rfl) ⟨1069530, by rfl⟩ : syracuseStep 2852081 = 2139061) B2139061
theorem B5998349 : Blo 1108626 5998349 := bstep (se 3 (by rfl) ⟨1124690, by rfl⟩ : syracuseStep 5998349 = 2249381) B2249381
theorem B11405069 : Blo 1108626 11405069 := bstep (se 3 (by rfl) ⟨2138450, by rfl⟩ : syracuseStep 11405069 = 4276901) B4276901
theorem B14419781 : Blo 1108626 14419781 := bstep (se 4 (by rfl) ⟨1351854, by rfl⟩ : syracuseStep 14419781 = 2703709) B2703709
theorem B7112717 : Blo 1108626 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B5343245 : Blo 1108626 5343245 := bstep (se 3 (by rfl) ⟨1001858, by rfl⟩ : syracuseStep 5343245 = 2003717) B2003717
theorem B1247251 : Blo 1108626 1247251 := bstep (se 1 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 1247251 = 1870877) B1870877
theorem B3606659 : Blo 1108626 3606659 := bstep (se 1 (by rfl) ⟨2704994, by rfl⟩ : syracuseStep 3606659 = 5409989) B5409989
theorem B1247395 : Blo 1108626 1247395 := bstep (se 1 (by rfl) ⟨935546, by rfl⟩ : syracuseStep 1247395 = 1871093) B1871093
theorem B3901745 : Blo 1108626 3901745 := bstep (se 2 (by rfl) ⟨1463154, by rfl⟩ : syracuseStep 3901745 = 2926309) B2926309
theorem B1247539 : Blo 1108626 1247539 := bstep (se 1 (by rfl) ⟨935654, by rfl⟩ : syracuseStep 1247539 = 1871309) B1871309
theorem B1247683 : Blo 1108626 1247683 := bstep (se 1 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 1247683 = 1871525) B1871525
theorem B5409251 : Blo 1108626 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B1247827 : Blo 1108626 1247827 := bstep (se 1 (by rfl) ⟨935870, by rfl⟩ : syracuseStep 1247827 = 1871741) B1871741
theorem B1247971 : Blo 1108626 1247971 := bstep (se 1 (by rfl) ⟨935978, by rfl⟩ : syracuseStep 1247971 = 1871957) B1871957
theorem B5999345 : Blo 1108626 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B1248115 : Blo 1108626 1248115 := bstep (se 1 (by rfl) ⟨936086, by rfl⟩ : syracuseStep 1248115 = 1872173) B1872173
theorem B6327173 : Blo 1108626 6327173 := bstep (se 4 (by rfl) ⟨593172, by rfl⟩ : syracuseStep 6327173 = 1186345) B1186345
theorem B1248259 : Blo 1108626 1248259 := bstep (se 1 (by rfl) ⟨936194, by rfl⟩ : syracuseStep 1248259 = 1872389) B1872389
theorem B1870897 : Blo 1108626 1870897 := bstep (se 2 (by rfl) ⟨701586, by rfl⟩ : syracuseStep 1870897 = 1403173) B1403173
theorem B1870931 : Blo 1108626 1870931 := bstep (se 1 (by rfl) ⟨1403198, by rfl⟩ : syracuseStep 1870931 = 2806397) B2806397
theorem B1248403 : Blo 1108626 1248403 := bstep (se 1 (by rfl) ⟨936302, by rfl⟩ : syracuseStep 1248403 = 1872605) B1872605
theorem B1871059 : Blo 1108626 1871059 := bstep (se 1 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 1871059 = 2806589) B2806589
theorem B1248547 : Blo 1108626 1248547 := bstep (se 1 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 1248547 = 1872821) B1872821
theorem B6327629 : Blo 1108626 6327629 := bstep (se 3 (by rfl) ⟨1186430, by rfl⟩ : syracuseStep 6327629 = 2372861) B2372861
theorem B1871201 : Blo 1108626 1871201 := bstep (se 2 (by rfl) ⟨701700, by rfl⟩ : syracuseStep 1871201 = 1403401) B1403401
theorem B3378595 : Blo 1108626 3378595 := bstep (se 1 (by rfl) ⟨2533946, by rfl⟩ : syracuseStep 3378595 = 5067893) B5067893
theorem B1248691 : Blo 1108626 1248691 := bstep (se 1 (by rfl) ⟨936518, by rfl⟩ : syracuseStep 1248691 = 1873037) B1873037
theorem B7212485 : Blo 1108626 7212485 := bstep (se 4 (by rfl) ⟨676170, by rfl⟩ : syracuseStep 7212485 = 1352341) B1352341
theorem B1871329 : Blo 1108626 1871329 := bstep (se 2 (by rfl) ⟨701748, by rfl⟩ : syracuseStep 1871329 = 1403497) B1403497
theorem B1871363 : Blo 1108626 1871363 := bstep (se 1 (by rfl) ⟨1403522, by rfl⟩ : syracuseStep 1871363 = 2807045) B2807045
theorem B1248835 : Blo 1108626 1248835 := bstep (se 1 (by rfl) ⟨936626, by rfl⟩ : syracuseStep 1248835 = 1873253) B1873253
theorem B1871491 : Blo 1108626 1871491 := bstep (se 1 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 1871491 = 2807237) B2807237
theorem B1248979 : Blo 1108626 1248979 := bstep (se 1 (by rfl) ⟨936734, by rfl⟩ : syracuseStep 1248979 = 1873469) B1873469
theorem B1871633 : Blo 1108626 1871633 := bstep (se 2 (by rfl) ⟨701862, by rfl⟩ : syracuseStep 1871633 = 1403725) B1403725
theorem B1249123 : Blo 1108626 1249123 := bstep (se 1 (by rfl) ⟨936842, by rfl⟩ : syracuseStep 1249123 = 1873685) B1873685
theorem B5345165 : Blo 1108626 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B1871761 : Blo 1108626 1871761 := bstep (se 2 (by rfl) ⟨701910, by rfl⟩ : syracuseStep 1871761 = 1403821) B1403821
theorem B1871795 : Blo 1108626 1871795 := bstep (se 1 (by rfl) ⟨1403846, by rfl⟩ : syracuseStep 1871795 = 2807693) B2807693
theorem B1249267 : Blo 1108626 1249267 := bstep (se 1 (by rfl) ⟨936950, by rfl⟩ : syracuseStep 1249267 = 1873901) B1873901
theorem B1871923 : Blo 1108626 1871923 := bstep (se 1 (by rfl) ⟨1403942, by rfl⟩ : syracuseStep 1871923 = 2807885) B2807885
theorem B6754373 : Blo 1108626 6754373 := bstep (se 4 (by rfl) ⟨633222, by rfl⟩ : syracuseStep 6754373 = 1266445) B1266445
theorem B1249411 : Blo 1108626 1249411 := bstep (se 1 (by rfl) ⟨937058, by rfl⟩ : syracuseStep 1249411 = 1874117) B1874117
theorem B1872065 : Blo 1108626 1872065 := bstep (se 2 (by rfl) ⟨702024, by rfl⟩ : syracuseStep 1872065 = 1404049) B1404049
theorem B2494673 : Blo 1108626 2494673 := bstep (se 2 (by rfl) ⟨935502, by rfl⟩ : syracuseStep 2494673 = 1871005) B1871005
theorem B2494691 : Blo 1108626 2494691 := bstep (se 1 (by rfl) ⟨1871018, by rfl⟩ : syracuseStep 2494691 = 3742037) B3742037
theorem B1249555 : Blo 1108626 1249555 := bstep (se 1 (by rfl) ⟨937166, by rfl⟩ : syracuseStep 1249555 = 1874333) B1874333
theorem B1872193 : Blo 1108626 1872193 := bstep (se 2 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 1872193 = 1404145) B1404145
theorem B1872227 : Blo 1108626 1872227 := bstep (se 1 (by rfl) ⟨1404170, by rfl⟩ : syracuseStep 1872227 = 2808341) B2808341
theorem B1249699 : Blo 1108626 1249699 := bstep (se 1 (by rfl) ⟨937274, by rfl⟩ : syracuseStep 1249699 = 1874549) B1874549
theorem B153817541 : Blo 1108626 153817541 := bstep (se 4 (by rfl) ⟨14420394, by rfl⟩ : syracuseStep 153817541 = 28840789) B28840789
theorem B8556997 : Blo 1108626 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B1872355 : Blo 1108626 1872355 := bstep (se 1 (by rfl) ⟨1404266, by rfl⟩ : syracuseStep 1872355 = 2808533) B2808533
theorem B2494961 : Blo 1108626 2494961 := bstep (se 2 (by rfl) ⟨935610, by rfl⟩ : syracuseStep 2494961 = 1871221) B1871221
theorem B2494979 : Blo 1108626 2494979 := bstep (se 1 (by rfl) ⟨1871234, by rfl⟩ : syracuseStep 2494979 = 3742469) B3742469
theorem B1249843 : Blo 1108626 1249843 := bstep (se 1 (by rfl) ⟨937382, by rfl⟩ : syracuseStep 1249843 = 1874765) B1874765
theorem B1872497 : Blo 1108626 1872497 := bstep (se 2 (by rfl) ⟨702186, by rfl⟩ : syracuseStep 1872497 = 1404373) B1404373
theorem B1249987 : Blo 1108626 1249987 := bstep (se 1 (by rfl) ⟨937490, by rfl⟩ : syracuseStep 1249987 = 1874981) B1874981
theorem B1184483 : Blo 1108626 1184483 := bstep (se 1 (by rfl) ⟨888362, by rfl⟩ : syracuseStep 1184483 = 1776725) B1776725
theorem B1872625 : Blo 1108626 1872625 := bstep (se 2 (by rfl) ⟨702234, by rfl⟩ : syracuseStep 1872625 = 1404469) B1404469
theorem B2495249 : Blo 1108626 2495249 := bstep (se 2 (by rfl) ⟨935718, by rfl⟩ : syracuseStep 2495249 = 1871437) B1871437
theorem B1872659 : Blo 1108626 1872659 := bstep (se 1 (by rfl) ⟨1404494, by rfl⟩ : syracuseStep 1872659 = 2808989) B2808989
theorem B2495267 : Blo 1108626 2495267 := bstep (se 1 (by rfl) ⟨1871450, by rfl⟩ : syracuseStep 2495267 = 3742901) B3742901
theorem B1250131 : Blo 1108626 1250131 := bstep (se 1 (by rfl) ⟨937598, by rfl⟩ : syracuseStep 1250131 = 1875197) B1875197
theorem B1872787 : Blo 1108626 1872787 := bstep (se 1 (by rfl) ⟨1404590, by rfl⟩ : syracuseStep 1872787 = 2809181) B2809181
theorem B1250275 : Blo 1108626 1250275 := bstep (se 1 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 1250275 = 1875413) B1875413
theorem B1872929 : Blo 1108626 1872929 := bstep (se 2 (by rfl) ⟨702348, by rfl⟩ : syracuseStep 1872929 = 1404697) B1404697
theorem B2495537 : Blo 1108626 2495537 := bstep (se 2 (by rfl) ⟨935826, by rfl⟩ : syracuseStep 2495537 = 1871653) B1871653
theorem B2495555 : Blo 1108626 2495555 := bstep (se 1 (by rfl) ⟨1871666, by rfl⟩ : syracuseStep 2495555 = 3743333) B3743333
theorem B1250419 : Blo 1108626 1250419 := bstep (se 1 (by rfl) ⟨937814, by rfl⟩ : syracuseStep 1250419 = 1875629) B1875629
theorem B1873057 : Blo 1108626 1873057 := bstep (se 2 (by rfl) ⟨702396, by rfl⟩ : syracuseStep 1873057 = 1404793) B1404793
theorem B1873091 : Blo 1108626 1873091 := bstep (se 1 (by rfl) ⟨1404818, by rfl⟩ : syracuseStep 1873091 = 2809637) B2809637
theorem B1250563 : Blo 1108626 1250563 := bstep (se 1 (by rfl) ⟨937922, by rfl⟩ : syracuseStep 1250563 = 1875845) B1875845
theorem B1873219 : Blo 1108626 1873219 := bstep (se 1 (by rfl) ⟨1404914, by rfl⟩ : syracuseStep 1873219 = 2809829) B2809829
theorem B2495825 : Blo 1108626 2495825 := bstep (se 2 (by rfl) ⟨935934, by rfl⟩ : syracuseStep 2495825 = 1871869) B1871869
theorem B2495843 : Blo 1108626 2495843 := bstep (se 1 (by rfl) ⟨1871882, by rfl⟩ : syracuseStep 2495843 = 3743765) B3743765
theorem B1250707 : Blo 1108626 1250707 := bstep (se 1 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 1250707 = 1876061) B1876061
theorem B1873361 : Blo 1108626 1873361 := bstep (se 2 (by rfl) ⟨702510, by rfl⟩ : syracuseStep 1873361 = 1405021) B1405021
theorem B1250851 : Blo 1108626 1250851 := bstep (se 1 (by rfl) ⟨938138, by rfl⟩ : syracuseStep 1250851 = 1876277) B1876277
theorem B1873489 : Blo 1108626 1873489 := bstep (se 2 (by rfl) ⟨702558, by rfl⟩ : syracuseStep 1873489 = 1405117) B1405117
theorem B2496113 : Blo 1108626 2496113 := bstep (se 2 (by rfl) ⟨936042, by rfl⟩ : syracuseStep 2496113 = 1872085) B1872085
theorem B1873523 : Blo 1108626 1873523 := bstep (se 1 (by rfl) ⟨1405142, by rfl⟩ : syracuseStep 1873523 = 2810285) B2810285
theorem B2496131 : Blo 1108626 2496131 := bstep (se 1 (by rfl) ⟨1872098, by rfl⟩ : syracuseStep 2496131 = 3744197) B3744197
theorem B2004625 : Blo 1108626 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B1250995 : Blo 1108626 1250995 := bstep (se 1 (by rfl) ⟨938246, by rfl⟩ : syracuseStep 1250995 = 1876493) B1876493
theorem B1873651 : Blo 1108626 1873651 := bstep (se 1 (by rfl) ⟨1405238, by rfl⟩ : syracuseStep 1873651 = 2810477) B2810477
theorem B1251139 : Blo 1108626 1251139 := bstep (se 1 (by rfl) ⟨938354, by rfl⟩ : syracuseStep 1251139 = 1876709) B1876709
theorem B1873793 : Blo 1108626 1873793 := bstep (se 2 (by rfl) ⟨702672, by rfl⟩ : syracuseStep 1873793 = 1405345) B1405345
theorem B2496401 : Blo 1108626 2496401 := bstep (se 2 (by rfl) ⟨936150, by rfl⟩ : syracuseStep 2496401 = 1872301) B1872301
theorem B2496419 : Blo 1108626 2496419 := bstep (se 1 (by rfl) ⟨1872314, by rfl⟩ : syracuseStep 2496419 = 3744629) B3744629
theorem B1251283 : Blo 1108626 1251283 := bstep (se 1 (by rfl) ⟨938462, by rfl⟩ : syracuseStep 1251283 = 1876925) B1876925
theorem B1579009 : Blo 1108626 1579009 := bstep (se 2 (by rfl) ⟨592128, by rfl⟩ : syracuseStep 1579009 = 1184257) B1184257
theorem B1873921 : Blo 1108626 1873921 := bstep (se 2 (by rfl) ⟨702720, by rfl⟩ : syracuseStep 1873921 = 1405441) B1405441
theorem B3741713 : Blo 1108626 3741713 := bstep (se 2 (by rfl) ⟨1403142, by rfl⟩ : syracuseStep 3741713 = 2806285) B2806285
theorem B1873955 : Blo 1108626 1873955 := bstep (se 1 (by rfl) ⟨1405466, by rfl⟩ : syracuseStep 1873955 = 2810933) B2810933
theorem B1579105 : Blo 1108626 1579105 := bstep (se 2 (by rfl) ⟨592164, by rfl⟩ : syracuseStep 1579105 = 1184329) B1184329
theorem B1251427 : Blo 1108626 1251427 := bstep (se 1 (by rfl) ⟨938570, by rfl⟩ : syracuseStep 1251427 = 1877141) B1877141
theorem B2889859 : Blo 1108626 2889859 := bstep (se 1 (by rfl) ⟨2167394, by rfl⟩ : syracuseStep 2889859 = 4334789) B4334789
theorem B1874083 : Blo 1108626 1874083 := bstep (se 1 (by rfl) ⟨1405562, by rfl⟩ : syracuseStep 1874083 = 2811125) B2811125
theorem B2496689 : Blo 1108626 2496689 := bstep (se 2 (by rfl) ⟨936258, by rfl⟩ : syracuseStep 2496689 = 1872517) B1872517
theorem B6330545 : Blo 1108626 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B2496707 : Blo 1108626 2496707 := bstep (se 1 (by rfl) ⟨1872530, by rfl⟩ : syracuseStep 2496707 = 3745061) B3745061
theorem B1775827 : Blo 1108626 1775827 := bstep (se 1 (by rfl) ⟨1331870, by rfl⟩ : syracuseStep 1775827 = 2663741) B2663741
theorem B1251571 : Blo 1108626 1251571 := bstep (se 1 (by rfl) ⟨938678, by rfl⟩ : syracuseStep 1251571 = 1877357) B1877357
theorem B1874225 : Blo 1108626 1874225 := bstep (se 2 (by rfl) ⟨702834, by rfl⟩ : syracuseStep 1874225 = 1405669) B1405669
theorem B1874353 : Blo 1108626 1874353 := bstep (se 2 (by rfl) ⟨702882, by rfl⟩ : syracuseStep 1874353 = 1405765) B1405765
theorem B2496977 : Blo 1108626 2496977 := bstep (se 2 (by rfl) ⟨936366, by rfl⟩ : syracuseStep 2496977 = 1872733) B1872733
theorem B1874387 : Blo 1108626 1874387 := bstep (se 1 (by rfl) ⟨1405790, by rfl⟩ : syracuseStep 1874387 = 2811581) B2811581
theorem B1776097 : Blo 1108626 1776097 := bstep (se 2 (by rfl) ⟨666036, by rfl⟩ : syracuseStep 1776097 = 1332073) B1332073
theorem B2496995 : Blo 1108626 2496995 := bstep (se 1 (by rfl) ⟨1872746, by rfl⟩ : syracuseStep 2496995 = 3745493) B3745493
theorem B21371363 : Blo 1108626 21371363 := bstep (se 1 (by rfl) ⟨16028522, by rfl⟩ : syracuseStep 21371363 = 32057045) B32057045
theorem B7608845 : Blo 1108626 7608845 := bstep (se 3 (by rfl) ⟨1426658, by rfl⟩ : syracuseStep 7608845 = 2853317) B2853317
theorem B1776161 : Blo 1108626 1776161 := bstep (se 2 (by rfl) ⟨666060, by rfl⟩ : syracuseStep 1776161 = 1332121) B1332121
theorem B3742253 : Blo 1108626 3742253 := bstep (se 3 (by rfl) ⟨701672, by rfl⟩ : syracuseStep 3742253 = 1403345) B1403345
theorem B1579601 : Blo 1108626 1579601 := bstep (se 2 (by rfl) ⟨592350, by rfl⟩ : syracuseStep 1579601 = 1184701) B1184701
theorem B1874515 : Blo 1108626 1874515 := bstep (se 1 (by rfl) ⟨1405886, by rfl⟩ : syracuseStep 1874515 = 2811773) B2811773
theorem B3742307 : Blo 1108626 3742307 := bstep (se 1 (by rfl) ⟨2806730, by rfl⟩ : syracuseStep 3742307 = 5613461) B5613461
theorem B1186499 : Blo 1108626 1186499 := bstep (se 1 (by rfl) ⟨889874, by rfl⟩ : syracuseStep 1186499 = 1779749) B1779749
theorem B1874657 : Blo 1108626 1874657 := bstep (se 2 (by rfl) ⟨702996, by rfl⟩ : syracuseStep 1874657 = 1405993) B1405993
theorem B2497265 : Blo 1108626 2497265 := bstep (se 2 (by rfl) ⟨936474, by rfl⟩ : syracuseStep 2497265 = 1872949) B1872949
theorem B2497283 : Blo 1108626 2497283 := bstep (se 1 (by rfl) ⟨1872962, by rfl⟩ : syracuseStep 2497283 = 3745925) B3745925
theorem B2530097 : Blo 1108626 2530097 := bstep (se 2 (by rfl) ⟨948786, by rfl⟩ : syracuseStep 2530097 = 1897573) B1897573
theorem B1874785 : Blo 1108626 1874785 := bstep (se 2 (by rfl) ⟨703044, by rfl⟩ : syracuseStep 1874785 = 1406089) B1406089
theorem B3742577 : Blo 1108626 3742577 := bstep (se 2 (by rfl) ⟨1403466, by rfl⟩ : syracuseStep 3742577 = 2806933) B2806933
theorem B1874819 : Blo 1108626 1874819 := bstep (se 1 (by rfl) ⟨1406114, by rfl⟩ : syracuseStep 1874819 = 2812229) B2812229
theorem B6167501 : Blo 1108626 6167501 := bstep (se 3 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 6167501 = 2312813) B2312813
theorem B1874947 : Blo 1108626 1874947 := bstep (se 1 (by rfl) ⟨1406210, by rfl⟩ : syracuseStep 1874947 = 2812421) B2812421
theorem B2497553 : Blo 1108626 2497553 := bstep (se 2 (by rfl) ⟨936582, by rfl⟩ : syracuseStep 2497553 = 1873165) B1873165
theorem B2497571 : Blo 1108626 2497571 := bstep (se 1 (by rfl) ⟨1873178, by rfl⟩ : syracuseStep 2497571 = 3746357) B3746357
theorem B1875089 : Blo 1108626 1875089 := bstep (se 2 (by rfl) ⟨703158, by rfl⟩ : syracuseStep 1875089 = 1406317) B1406317
theorem B1875217 : Blo 1108626 1875217 := bstep (se 2 (by rfl) ⟨703206, by rfl⟩ : syracuseStep 1875217 = 1406413) B1406413
theorem B2497841 : Blo 1108626 2497841 := bstep (se 2 (by rfl) ⟨936690, by rfl⟩ : syracuseStep 2497841 = 1873381) B1873381
theorem B1875251 : Blo 1108626 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B2497859 : Blo 1108626 2497859 := bstep (se 1 (by rfl) ⟨1873394, by rfl⟩ : syracuseStep 2497859 = 3746789) B3746789
theorem B3743117 : Blo 1108626 3743117 := bstep (se 3 (by rfl) ⟨701834, by rfl⟩ : syracuseStep 3743117 = 1403669) B1403669
theorem B1580467 : Blo 1108626 1580467 := bstep (se 1 (by rfl) ⟨1185350, by rfl⟩ : syracuseStep 1580467 = 2370701) B2370701
theorem B1875379 : Blo 1108626 1875379 := bstep (se 1 (by rfl) ⟨1406534, by rfl⟩ : syracuseStep 1875379 = 2813069) B2813069
theorem B3743171 : Blo 1108626 3743171 := bstep (se 1 (by rfl) ⟨2807378, by rfl⟩ : syracuseStep 3743171 = 5614757) B5614757
theorem B4496867 : Blo 1108626 4496867 := bstep (se 1 (by rfl) ⟨3372650, by rfl⟩ : syracuseStep 4496867 = 6745301) B6745301
theorem B2530801 : Blo 1108626 2530801 := bstep (se 2 (by rfl) ⟨949050, by rfl⟩ : syracuseStep 2530801 = 1898101) B1898101
theorem B1580563 : Blo 1108626 1580563 := bstep (se 1 (by rfl) ⟨1185422, by rfl⟩ : syracuseStep 1580563 = 2370845) B2370845
theorem B1875521 : Blo 1108626 1875521 := bstep (se 2 (by rfl) ⟨703320, by rfl⟩ : syracuseStep 1875521 = 1406641) B1406641
theorem B2498129 : Blo 1108626 2498129 := bstep (se 2 (by rfl) ⟨936798, by rfl⟩ : syracuseStep 2498129 = 1873597) B1873597
theorem B2498147 : Blo 1108626 2498147 := bstep (se 1 (by rfl) ⟨1873610, by rfl⟩ : syracuseStep 2498147 = 3747221) B3747221
theorem B6332003 : Blo 1108626 6332003 := bstep (se 1 (by rfl) ⟨4749002, by rfl⟩ : syracuseStep 6332003 = 9498005) B9498005
theorem B1187507 : Blo 1108626 1187507 := bstep (se 1 (by rfl) ⟨890630, by rfl⟩ : syracuseStep 1187507 = 1781261) B1781261
theorem B1875649 : Blo 1108626 1875649 := bstep (se 2 (by rfl) ⟨703368, by rfl⟩ : syracuseStep 1875649 = 1406737) B1406737
theorem B2105041 : Blo 1108626 2105041 := bstep (se 2 (by rfl) ⟨789390, by rfl⟩ : syracuseStep 2105041 = 1578781) B1578781
theorem B3743441 : Blo 1108626 3743441 := bstep (se 2 (by rfl) ⟨1403790, by rfl⟩ : syracuseStep 3743441 = 2807581) B2807581
theorem B1875683 : Blo 1108626 1875683 := bstep (se 1 (by rfl) ⟨1406762, by rfl⟩ : syracuseStep 1875683 = 2813525) B2813525
theorem B5775089 : Blo 1108626 5775089 := bstep (se 2 (by rfl) ⟨2165658, by rfl⟩ : syracuseStep 5775089 = 4331317) B4331317
theorem B1875811 : Blo 1108626 1875811 := bstep (se 1 (by rfl) ⟨1406858, by rfl⟩ : syracuseStep 1875811 = 2813717) B2813717
theorem B2498417 : Blo 1108626 2498417 := bstep (se 2 (by rfl) ⟨936906, by rfl⟩ : syracuseStep 2498417 = 1873813) B1873813
theorem B2498435 : Blo 1108626 2498435 := bstep (se 1 (by rfl) ⟨1873826, by rfl⟩ : syracuseStep 2498435 = 3747653) B3747653
theorem B3383171 : Blo 1108626 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B36052877 : Blo 1108626 36052877 := bstep (se 3 (by rfl) ⟨6759914, by rfl⟩ : syracuseStep 36052877 = 13519829) B13519829
theorem B1875953 : Blo 1108626 1875953 := bstep (se 2 (by rfl) ⟨703482, by rfl⟩ : syracuseStep 1875953 = 1406965) B1406965
theorem B1581059 : Blo 1108626 1581059 := bstep (se 1 (by rfl) ⟨1185794, by rfl⟩ : syracuseStep 1581059 = 2371589) B2371589
theorem B3612685 : Blo 1108626 3612685 := bstep (se 3 (by rfl) ⟨677378, by rfl⟩ : syracuseStep 3612685 = 1354757) B1354757
theorem B2105443 : Blo 1108626 2105443 := bstep (se 1 (by rfl) ⟨1579082, by rfl⟩ : syracuseStep 2105443 = 3158165) B3158165
theorem B1876081 : Blo 1108626 1876081 := bstep (se 2 (by rfl) ⟨703530, by rfl⟩ : syracuseStep 1876081 = 1407061) B1407061
theorem B2105489 : Blo 1108626 2105489 := bstep (se 2 (by rfl) ⟨789558, by rfl⟩ : syracuseStep 2105489 = 1579117) B1579117
theorem B2498705 : Blo 1108626 2498705 := bstep (se 2 (by rfl) ⟨937014, by rfl⟩ : syracuseStep 2498705 = 1874029) B1874029
theorem B1876115 : Blo 1108626 1876115 := bstep (se 1 (by rfl) ⟨1407086, by rfl⟩ : syracuseStep 1876115 = 2814173) B2814173
theorem B2498723 : Blo 1108626 2498723 := bstep (se 1 (by rfl) ⟨1874042, by rfl⟩ : syracuseStep 2498723 = 3748085) B3748085
theorem B72982741 : Blo 1108626 72982741 := bstep (se 7 (by rfl) ⟨855266, by rfl⟩ : syracuseStep 72982741 = 1710533) B1710533
theorem B1777891 : Blo 1108626 1777891 := bstep (se 1 (by rfl) ⟨1333418, by rfl⟩ : syracuseStep 1777891 = 2666837) B2666837
theorem B3743981 : Blo 1108626 3743981 := bstep (se 3 (by rfl) ⟨701996, by rfl⟩ : syracuseStep 3743981 = 1403993) B1403993
theorem B1876243 : Blo 1108626 1876243 := bstep (se 1 (by rfl) ⟨1407182, by rfl⟩ : syracuseStep 1876243 = 2814365) B2814365
theorem B3744035 : Blo 1108626 3744035 := bstep (se 1 (by rfl) ⟨2808026, by rfl⟩ : syracuseStep 3744035 = 5616053) B5616053
theorem B1876385 : Blo 1108626 1876385 := bstep (se 2 (by rfl) ⟨703644, by rfl⟩ : syracuseStep 1876385 = 1407289) B1407289
theorem B2105777 : Blo 1108626 2105777 := bstep (se 2 (by rfl) ⟨789666, by rfl⟩ : syracuseStep 2105777 = 1579333) B1579333
theorem B2498993 : Blo 1108626 2498993 := bstep (se 2 (by rfl) ⟨937122, by rfl⟩ : syracuseStep 2498993 = 1874245) B1874245
theorem B2499011 : Blo 1108626 2499011 := bstep (se 1 (by rfl) ⟨1874258, by rfl⟩ : syracuseStep 2499011 = 3748517) B3748517
theorem B2466289 : Blo 1108626 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B1876513 : Blo 1108626 1876513 := bstep (se 2 (by rfl) ⟨703692, by rfl⟩ : syracuseStep 1876513 = 1407385) B1407385
theorem B3744305 : Blo 1108626 3744305 := bstep (se 2 (by rfl) ⟨1404114, by rfl⟩ : syracuseStep 3744305 = 2808229) B2808229
theorem B1876547 : Blo 1108626 1876547 := bstep (se 1 (by rfl) ⟨1407410, by rfl⟩ : syracuseStep 1876547 = 2814821) B2814821
theorem B6333005 : Blo 1108626 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B1581697 : Blo 1108626 1581697 := bstep (se 2 (by rfl) ⟨593136, by rfl⟩ : syracuseStep 1581697 = 1186273) B1186273
theorem B2400899 : Blo 1108626 2400899 := bstep (se 1 (by rfl) ⟨1800674, by rfl⟩ : syracuseStep 2400899 = 3601349) B3601349
theorem B1778339 : Blo 1108626 1778339 := bstep (se 1 (by rfl) ⟨1333754, by rfl⟩ : syracuseStep 1778339 = 2667509) B2667509
theorem B1876675 : Blo 1108626 1876675 := bstep (se 1 (by rfl) ⟨1407506, by rfl⟩ : syracuseStep 1876675 = 2815013) B2815013
theorem B2499281 : Blo 1108626 2499281 := bstep (se 2 (by rfl) ⟨937230, by rfl⟩ : syracuseStep 2499281 = 1874461) B1874461
theorem B4268771 : Blo 1108626 4268771 := bstep (se 1 (by rfl) ⟨3201578, by rfl⟩ : syracuseStep 4268771 = 6403157) B6403157
theorem B2499299 : Blo 1108626 2499299 := bstep (se 1 (by rfl) ⟨1874474, by rfl⟩ : syracuseStep 2499299 = 3748949) B3748949
theorem B1876817 : Blo 1108626 1876817 := bstep (se 2 (by rfl) ⟨703806, by rfl⟩ : syracuseStep 1876817 = 1407613) B1407613
theorem B1582033 : Blo 1108626 1582033 := bstep (se 2 (by rfl) ⟨593262, by rfl⟩ : syracuseStep 1582033 = 1186525) B1186525
theorem B1876945 : Blo 1108626 1876945 := bstep (se 2 (by rfl) ⟨703854, by rfl⟩ : syracuseStep 1876945 = 1407709) B1407709
theorem B2499569 : Blo 1108626 2499569 := bstep (se 2 (by rfl) ⟨937338, by rfl⟩ : syracuseStep 2499569 = 1874677) B1874677
theorem B1876979 : Blo 1108626 1876979 := bstep (se 1 (by rfl) ⟨1407734, by rfl⟩ : syracuseStep 1876979 = 2815469) B2815469
theorem B2499587 : Blo 1108626 2499587 := bstep (se 1 (by rfl) ⟨1874690, by rfl⟩ : syracuseStep 2499587 = 3749381) B3749381
theorem B3744845 : Blo 1108626 3744845 := bstep (se 3 (by rfl) ⟨702158, by rfl⟩ : syracuseStep 3744845 = 1404317) B1404317
theorem B1877107 : Blo 1108626 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B2106499 : Blo 1108626 2106499 := bstep (se 1 (by rfl) ⟨1579874, by rfl⟩ : syracuseStep 2106499 = 3159749) B3159749
theorem B3744899 : Blo 1108626 3744899 := bstep (se 1 (by rfl) ⟨2808674, by rfl⟩ : syracuseStep 3744899 = 5617349) B5617349
theorem B1778897 : Blo 1108626 1778897 := bstep (se 2 (by rfl) ⟨667086, by rfl⟩ : syracuseStep 1778897 = 1334173) B1334173
theorem B1877249 : Blo 1108626 1877249 := bstep (se 2 (by rfl) ⟨703968, by rfl⟩ : syracuseStep 1877249 = 1407937) B1407937
theorem B5612813 : Blo 1108626 5612813 := bstep (se 3 (by rfl) ⟨1052402, by rfl⟩ : syracuseStep 5612813 = 2104805) B2104805
theorem B2499857 : Blo 1108626 2499857 := bstep (se 2 (by rfl) ⟨937446, by rfl⟩ : syracuseStep 2499857 = 1874893) B1874893
theorem B2499875 : Blo 1108626 2499875 := bstep (se 1 (by rfl) ⟨1874906, by rfl⟩ : syracuseStep 2499875 = 3749813) B3749813
theorem B2663761 : Blo 1108626 2663761 := bstep (se 2 (by rfl) ⟨998910, by rfl⟩ : syracuseStep 2663761 = 1997821) B1997821
theorem B1877377 : Blo 1108626 1877377 := bstep (se 2 (by rfl) ⟨704016, by rfl⟩ : syracuseStep 1877377 = 1408033) B1408033
theorem B3745169 : Blo 1108626 3745169 := bstep (se 2 (by rfl) ⟨1404438, by rfl⟩ : syracuseStep 3745169 = 2808877) B2808877
theorem B2368931 : Blo 1108626 2368931 := bstep (se 1 (by rfl) ⟨1776698, by rfl⟩ : syracuseStep 2368931 = 3553397) B3553397
theorem B1877411 : Blo 1108626 1877411 := bstep (se 1 (by rfl) ⟨1408058, by rfl⟩ : syracuseStep 1877411 = 2816117) B2816117
theorem B2663857 : Blo 1108626 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B1779121 : Blo 1108626 1779121 := bstep (se 2 (by rfl) ⟨667170, by rfl⟩ : syracuseStep 1779121 = 1334341) B1334341
theorem B7120325 : Blo 1108626 7120325 := bstep (se 4 (by rfl) ⟨667530, by rfl⟩ : syracuseStep 7120325 = 1335061) B1335061
theorem B6006221 : Blo 1108626 6006221 := bstep (se 3 (by rfl) ⟨1126166, by rfl⟩ : syracuseStep 6006221 = 2252333) B2252333
theorem B1779185 : Blo 1108626 1779185 := bstep (se 2 (by rfl) ⟨667194, by rfl⟩ : syracuseStep 1779185 = 1334389) B1334389
theorem B1582625 : Blo 1108626 1582625 := bstep (se 2 (by rfl) ⟨593484, by rfl⟩ : syracuseStep 1582625 = 1186969) B1186969
theorem B2663971 : Blo 1108626 2663971 := bstep (se 1 (by rfl) ⟨1997978, by rfl⟩ : syracuseStep 2663971 = 3995957) B3995957
theorem B1877539 : Blo 1108626 1877539 := bstep (se 1 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 1877539 = 2816309) B2816309
theorem B2500145 : Blo 1108626 2500145 := bstep (se 2 (by rfl) ⟨937554, by rfl⟩ : syracuseStep 2500145 = 1875109) B1875109
theorem B2106947 : Blo 1108626 2106947 := bstep (se 1 (by rfl) ⟨1580210, by rfl⟩ : syracuseStep 2106947 = 3160421) B3160421
theorem B2500163 : Blo 1108626 2500163 := bstep (se 1 (by rfl) ⟨1875122, by rfl⟩ : syracuseStep 2500163 = 3750245) B3750245
theorem B2664049 : Blo 1108626 2664049 := bstep (se 2 (by rfl) ⟨999018, by rfl⟩ : syracuseStep 2664049 = 1998037) B1998037
theorem B1779313 : Blo 1108626 1779313 := bstep (se 2 (by rfl) ⟨667242, by rfl⟩ : syracuseStep 1779313 = 1334485) B1334485
theorem B2500433 : Blo 1108626 2500433 := bstep (se 2 (by rfl) ⟨937662, by rfl⟩ : syracuseStep 2500433 = 1875325) B1875325
theorem B2107235 : Blo 1108626 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B2500451 : Blo 1108626 2500451 := bstep (se 1 (by rfl) ⟨1875338, by rfl⟩ : syracuseStep 2500451 = 3750677) B3750677
theorem B3745709 : Blo 1108626 3745709 := bstep (se 3 (by rfl) ⟨702320, by rfl⟩ : syracuseStep 3745709 = 1404641) B1404641
theorem B3745763 : Blo 1108626 3745763 := bstep (se 1 (by rfl) ⟨2809322, by rfl⟩ : syracuseStep 3745763 = 5618645) B5618645
theorem B1583155 : Blo 1108626 1583155 := bstep (se 1 (by rfl) ⟨1187366, by rfl⟩ : syracuseStep 1583155 = 2374733) B2374733
theorem B2500721 : Blo 1108626 2500721 := bstep (se 2 (by rfl) ⟨937770, by rfl⟩ : syracuseStep 2500721 = 1875541) B1875541
theorem B2500739 : Blo 1108626 2500739 := bstep (se 1 (by rfl) ⟨1875554, by rfl⟩ : syracuseStep 2500739 = 3751109) B3751109
theorem B3746033 : Blo 1108626 3746033 := bstep (se 2 (by rfl) ⟨1404762, by rfl⟩ : syracuseStep 3746033 = 2809525) B2809525
theorem B1583491 : Blo 1108626 1583491 := bstep (se 1 (by rfl) ⟨1187618, by rfl⟩ : syracuseStep 1583491 = 2375237) B2375237
theorem B2501009 : Blo 1108626 2501009 := bstep (se 2 (by rfl) ⟨937878, by rfl⟩ : syracuseStep 2501009 = 1875757) B1875757
theorem B2501027 : Blo 1108626 2501027 := bstep (se 1 (by rfl) ⟨1875770, by rfl⟩ : syracuseStep 2501027 = 3751541) B3751541
theorem B8432099 : Blo 1108626 8432099 := bstep (se 1 (by rfl) ⟨6324074, by rfl⟩ : syracuseStep 8432099 = 12648149) B12648149
theorem B4499981 : Blo 1108626 4499981 := bstep (se 3 (by rfl) ⟨843746, by rfl⟩ : syracuseStep 4499981 = 1687493) B1687493
theorem B2501297 : Blo 1108626 2501297 := bstep (se 2 (by rfl) ⟨937986, by rfl⟩ : syracuseStep 2501297 = 1875973) B1875973
theorem B2501315 : Blo 1108626 2501315 := bstep (se 1 (by rfl) ⟨1875986, by rfl⟩ : syracuseStep 2501315 = 3751973) B3751973
theorem B3746573 : Blo 1108626 3746573 := bstep (se 3 (by rfl) ⟨702482, by rfl⟩ : syracuseStep 3746573 = 1404965) B1404965
theorem B2108177 : Blo 1108626 2108177 := bstep (se 2 (by rfl) ⟨790566, by rfl⟩ : syracuseStep 2108177 = 1581133) B1581133
theorem B3746627 : Blo 1108626 3746627 := bstep (se 1 (by rfl) ⟨2809970, by rfl⟩ : syracuseStep 3746627 = 5619941) B5619941
theorem B1584049 : Blo 1108626 1584049 := bstep (se 2 (by rfl) ⟨594018, by rfl⟩ : syracuseStep 1584049 = 1188037) B1188037
theorem B10660805 : Blo 1108626 10660805 := bstep (se 4 (by rfl) ⟨999450, by rfl⟩ : syracuseStep 10660805 = 1998901) B1998901
theorem B2501585 : Blo 1108626 2501585 := bstep (se 2 (by rfl) ⟨938094, by rfl⟩ : syracuseStep 2501585 = 1876189) B1876189
theorem B1584083 : Blo 1108626 1584083 := bstep (se 1 (by rfl) ⟨1188062, by rfl⟩ : syracuseStep 1584083 = 2376125) B2376125
theorem B2501603 : Blo 1108626 2501603 := bstep (se 1 (by rfl) ⟨1876202, by rfl⟩ : syracuseStep 2501603 = 3752405) B3752405
theorem B3746897 : Blo 1108626 3746897 := bstep (se 2 (by rfl) ⟨1405086, by rfl⟩ : syracuseStep 3746897 = 2810173) B2810173
theorem B5057677 : Blo 1108626 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B2501873 : Blo 1108626 2501873 := bstep (se 2 (by rfl) ⟨938202, by rfl⟩ : syracuseStep 2501873 = 1876405) B1876405
theorem B2501891 : Blo 1108626 2501891 := bstep (se 1 (by rfl) ⟨1876418, by rfl⟩ : syracuseStep 2501891 = 3752837) B3752837
theorem B7122275 : Blo 1108626 7122275 := bstep (se 1 (by rfl) ⟨5341706, by rfl⟩ : syracuseStep 7122275 = 10683413) B10683413
theorem B6761861 : Blo 1108626 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B6335921 : Blo 1108626 6335921 := bstep (se 2 (by rfl) ⟨2375970, by rfl⟩ : syracuseStep 6335921 = 4751941) B4751941
theorem B2502161 : Blo 1108626 2502161 := bstep (se 2 (by rfl) ⟨938310, by rfl⟩ : syracuseStep 2502161 = 1876621) B1876621
theorem B2502179 : Blo 1108626 2502179 := bstep (se 1 (by rfl) ⟨1876634, by rfl⟩ : syracuseStep 2502179 = 3753269) B3753269
theorem B2371153 : Blo 1108626 2371153 := bstep (se 2 (by rfl) ⟨889182, by rfl⟩ : syracuseStep 2371153 = 1778365) B1778365
theorem B3747437 : Blo 1108626 3747437 := bstep (se 3 (by rfl) ⟨702644, by rfl⟩ : syracuseStep 3747437 = 1405289) B1405289
theorem B1781363 : Blo 1108626 1781363 := bstep (se 1 (by rfl) ⟨1336022, by rfl⟩ : syracuseStep 1781363 = 2672045) B2672045
theorem B2109073 : Blo 1108626 2109073 := bstep (se 2 (by rfl) ⟨790902, by rfl⟩ : syracuseStep 2109073 = 1581805) B1581805
theorem B3747491 : Blo 1108626 3747491 := bstep (se 1 (by rfl) ⟨2810618, by rfl⟩ : syracuseStep 3747491 = 5621237) B5621237
theorem B2109233 : Blo 1108626 2109233 := bstep (se 2 (by rfl) ⟨790962, by rfl⟩ : syracuseStep 2109233 = 1581925) B1581925
theorem B2502449 : Blo 1108626 2502449 := bstep (se 2 (by rfl) ⟨938418, by rfl⟩ : syracuseStep 2502449 = 1876837) B1876837
theorem B2502467 : Blo 1108626 2502467 := bstep (se 1 (by rfl) ⟨1876850, by rfl⟩ : syracuseStep 2502467 = 3753701) B3753701
theorem B4501325 : Blo 1108626 4501325 := bstep (se 3 (by rfl) ⟨843998, by rfl⟩ : syracuseStep 4501325 = 1687997) B1687997
theorem B3157937 : Blo 1108626 3157937 := bstep (se 2 (by rfl) ⟨1184226, by rfl⟩ : syracuseStep 3157937 = 2368453) B2368453
theorem B3747761 : Blo 1108626 3747761 := bstep (se 2 (by rfl) ⟨1405410, by rfl⟩ : syracuseStep 3747761 = 2810821) B2810821
theorem B2502737 : Blo 1108626 2502737 := bstep (se 2 (by rfl) ⟨938526, by rfl⟩ : syracuseStep 2502737 = 1877053) B1877053
theorem B2502755 : Blo 1108626 2502755 := bstep (se 1 (by rfl) ⟨1877066, by rfl⟩ : syracuseStep 2502755 = 3754133) B3754133
theorem B5615729 : Blo 1108626 5615729 := bstep (se 2 (by rfl) ⟨2105898, by rfl⟩ : syracuseStep 5615729 = 4211797) B4211797
theorem B2109635 : Blo 1108626 2109635 := bstep (se 1 (by rfl) ⟨1582226, by rfl⟩ : syracuseStep 2109635 = 3164453) B3164453
theorem B2503025 : Blo 1108626 2503025 := bstep (se 2 (by rfl) ⟨938634, by rfl⟩ : syracuseStep 2503025 = 1877269) B1877269
theorem B2503043 : Blo 1108626 2503043 := bstep (se 1 (by rfl) ⟨1877282, by rfl⟩ : syracuseStep 2503043 = 3754565) B3754565
theorem B1782209 : Blo 1108626 1782209 := bstep (se 2 (by rfl) ⟨668328, by rfl⟩ : syracuseStep 1782209 = 1336657) B1336657
theorem B3748301 : Blo 1108626 3748301 := bstep (se 3 (by rfl) ⟨702806, by rfl⟩ : syracuseStep 3748301 = 1405613) B1405613
theorem B3748355 : Blo 1108626 3748355 := bstep (se 1 (by rfl) ⟨2811266, by rfl⟩ : syracuseStep 3748355 = 5622533) B5622533
theorem B2503313 : Blo 1108626 2503313 := bstep (se 2 (by rfl) ⟨938742, by rfl⟩ : syracuseStep 2503313 = 1877485) B1877485
theorem B2503331 : Blo 1108626 2503331 := bstep (se 1 (by rfl) ⟨1877498, by rfl⟩ : syracuseStep 2503331 = 3754997) B3754997
theorem B3748625 : Blo 1108626 3748625 := bstep (se 2 (by rfl) ⟨1405734, by rfl⟩ : syracuseStep 3748625 = 2811469) B2811469
theorem B2569073 : Blo 1108626 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B2110531 : Blo 1108626 2110531 := bstep (se 1 (by rfl) ⟨1582898, by rfl⟩ : syracuseStep 2110531 = 3165797) B3165797
theorem B2110691 : Blo 1108626 2110691 := bstep (se 1 (by rfl) ⟨1583018, by rfl⟩ : syracuseStep 2110691 = 3166037) B3166037
theorem B2667779 : Blo 1108626 2667779 := bstep (se 1 (by rfl) ⟨2000834, by rfl⟩ : syracuseStep 2667779 = 4001669) B4001669
theorem B3749165 : Blo 1108626 3749165 := bstep (se 3 (by rfl) ⟨702968, by rfl⟩ : syracuseStep 3749165 = 1405937) B1405937
theorem B3159395 : Blo 1108626 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B3749219 : Blo 1108626 3749219 := bstep (se 1 (by rfl) ⟨2811914, by rfl⟩ : syracuseStep 3749219 = 5623829) B5623829
theorem B6763981 : Blo 1108626 6763981 := bstep (se 3 (by rfl) ⟨1268246, by rfl⟩ : syracuseStep 6763981 = 2536493) B2536493
theorem B17315299 : Blo 1108626 17315299 := bstep (se 1 (by rfl) ⟨12986474, by rfl⟩ : syracuseStep 17315299 = 25972949) B25972949
theorem B5617187 : Blo 1108626 5617187 := bstep (se 1 (by rfl) ⟨4212890, by rfl⟩ : syracuseStep 5617187 = 8425781) B8425781
theorem B2438755 : Blo 1108626 2438755 := bstep (se 1 (by rfl) ⟨1829066, by rfl⟩ : syracuseStep 2438755 = 3658133) B3658133
theorem B3749489 : Blo 1108626 3749489 := bstep (se 2 (by rfl) ⟨1406058, by rfl⟩ : syracuseStep 3749489 = 2812117) B2812117
theorem B2668355 : Blo 1108626 2668355 := bstep (se 1 (by rfl) ⟨2001266, by rfl⟩ : syracuseStep 2668355 = 4002533) B4002533
theorem B3553283 : Blo 1108626 3553283 := bstep (se 1 (by rfl) ⟨2664962, by rfl⟩ : syracuseStep 3553283 = 5329925) B5329925
theorem B2668547 : Blo 1108626 2668547 := bstep (se 1 (by rfl) ⟨2001410, by rfl⟩ : syracuseStep 2668547 = 4002821) B4002821
theorem B3160205 : Blo 1108626 3160205 := bstep (se 3 (by rfl) ⟨592538, by rfl⟩ : syracuseStep 3160205 = 1185077) B1185077
theorem B3750029 : Blo 1108626 3750029 := bstep (se 3 (by rfl) ⟨703130, by rfl⟩ : syracuseStep 3750029 = 1406261) B1406261
theorem B3750083 : Blo 1108626 3750083 := bstep (se 1 (by rfl) ⟨2812562, by rfl⟩ : syracuseStep 3750083 = 5625125) B5625125
theorem B15186161 : Blo 1108626 15186161 := bstep (se 2 (by rfl) ⟨5694810, by rfl⟩ : syracuseStep 15186161 = 11389621) B11389621
theorem B2111761 : Blo 1108626 2111761 := bstep (se 2 (by rfl) ⟨791910, by rfl⟩ : syracuseStep 2111761 = 1583821) B1583821
theorem B2668835 : Blo 1108626 2668835 := bstep (se 1 (by rfl) ⟨2001626, by rfl⟩ : syracuseStep 2668835 = 4003253) B4003253
theorem B5617997 : Blo 1108626 5617997 := bstep (se 3 (by rfl) ⟨1053374, by rfl⟩ : syracuseStep 5617997 = 2106749) B2106749
theorem B3160397 : Blo 1108626 3160397 := bstep (se 3 (by rfl) ⟨592574, by rfl⟩ : syracuseStep 3160397 = 1185149) B1185149
theorem B1685953 : Blo 1108626 1685953 := bstep (se 2 (by rfl) ⟨632232, by rfl⟩ : syracuseStep 1685953 = 1264465) B1264465
theorem B3750353 : Blo 1108626 3750353 := bstep (se 2 (by rfl) ⟨1406382, by rfl⟩ : syracuseStep 3750353 = 2812765) B2812765
theorem B2374211 : Blo 1108626 2374211 := bstep (se 1 (by rfl) ⟨1780658, by rfl⟩ : syracuseStep 2374211 = 3561317) B3561317
theorem B9124493 : Blo 1108626 9124493 := bstep (se 3 (by rfl) ⟨1710842, by rfl⟩ : syracuseStep 9124493 = 3421685) B3421685
theorem B7125965 : Blo 1108626 7125965 := bstep (se 3 (by rfl) ⟨1336118, by rfl⟩ : syracuseStep 7125965 = 2672237) B2672237
theorem B3750893 : Blo 1108626 3750893 := bstep (se 3 (by rfl) ⟨703292, by rfl⟩ : syracuseStep 3750893 = 1406585) B1406585
theorem B3750947 : Blo 1108626 3750947 := bstep (se 1 (by rfl) ⟨2813210, by rfl⟩ : syracuseStep 3750947 = 5626421) B5626421
theorem B3554371 : Blo 1108626 3554371 := bstep (se 1 (by rfl) ⟨2665778, by rfl⟩ : syracuseStep 3554371 = 5331557) B5331557
theorem B2997425 : Blo 1108626 2997425 := bstep (se 2 (by rfl) ⟨1124034, by rfl⟩ : syracuseStep 2997425 = 2248069) B2248069
theorem B3554513 : Blo 1108626 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B2669777 : Blo 1108626 2669777 := bstep (se 2 (by rfl) ⟨1001166, by rfl⟩ : syracuseStep 2669777 = 2002333) B2002333
theorem B3161389 : Blo 1108626 3161389 := bstep (se 3 (by rfl) ⟨592760, by rfl⟩ : syracuseStep 3161389 = 1185521) B1185521
theorem B3751217 : Blo 1108626 3751217 := bstep (se 2 (by rfl) ⟨1406706, by rfl⟩ : syracuseStep 3751217 = 2813413) B2813413
theorem B4504909 : Blo 1108626 4504909 := bstep (se 3 (by rfl) ⟨844670, by rfl⟩ : syracuseStep 4504909 = 1689341) B1689341
theorem B2669969 : Blo 1108626 2669969 := bstep (se 2 (by rfl) ⟨1001238, by rfl⟩ : syracuseStep 2669969 = 2002477) B2002477
theorem B2375075 : Blo 1108626 2375075 := bstep (se 1 (by rfl) ⟨1781306, by rfl⟩ : syracuseStep 2375075 = 3562613) B3562613
theorem B2375185 : Blo 1108626 2375185 := bstep (se 2 (by rfl) ⟨890694, by rfl⟩ : syracuseStep 2375185 = 1781389) B1781389
theorem B15416885 : Blo 1108626 15416885 := bstep (se 5 (by rfl) ⟨722666, by rfl⟩ : syracuseStep 15416885 = 1445333) B1445333
theorem B4210339 : Blo 1108626 4210339 := bstep (se 1 (by rfl) ⟨3157754, by rfl⟩ : syracuseStep 4210339 = 6315509) B6315509
theorem B8437445 : Blo 1108626 8437445 := bstep (se 4 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 8437445 = 1582021) B1582021
theorem B6405923 : Blo 1108626 6405923 := bstep (se 1 (by rfl) ⟨4804442, by rfl⟩ : syracuseStep 6405923 = 9608885) B9608885
theorem B3751757 : Blo 1108626 3751757 := bstep (se 3 (by rfl) ⟨703454, by rfl⟩ : syracuseStep 3751757 = 1406909) B1406909
theorem B3751811 : Blo 1108626 3751811 := bstep (se 1 (by rfl) ⟨2813858, by rfl⟩ : syracuseStep 3751811 = 5627717) B5627717
theorem B60702605 : Blo 1108626 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B2998289 : Blo 1108626 2998289 := bstep (se 2 (by rfl) ⟨1124358, by rfl⟩ : syracuseStep 2998289 = 2248717) B2248717
theorem B2670737 : Blo 1108626 2670737 := bstep (se 2 (by rfl) ⟨1001526, by rfl⟩ : syracuseStep 2670737 = 2003053) B2003053
theorem B3752081 : Blo 1108626 3752081 := bstep (se 2 (by rfl) ⟨1407030, by rfl⟩ : syracuseStep 3752081 = 2814061) B2814061
theorem B1622209 : Blo 1108626 1622209 := bstep (se 2 (by rfl) ⟨608328, by rfl⟩ : syracuseStep 1622209 = 1216657) B1216657
theorem B3555857 : Blo 1108626 3555857 := bstep (se 2 (by rfl) ⟨1333446, by rfl⟩ : syracuseStep 3555857 = 2666893) B2666893
theorem B4735523 : Blo 1108626 4735523 := bstep (se 1 (by rfl) ⟨3551642, by rfl⟩ : syracuseStep 4735523 = 7103285) B7103285
theorem B1688131 : Blo 1108626 1688131 := bstep (se 1 (by rfl) ⟨1266098, by rfl⟩ : syracuseStep 1688131 = 2532197) B2532197
theorem B3850897 : Blo 1108626 3850897 := bstep (se 2 (by rfl) ⟨1444086, by rfl⟩ : syracuseStep 3850897 = 2888173) B2888173
theorem B3752621 : Blo 1108626 3752621 := bstep (se 3 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 3752621 = 1407233) B1407233
theorem B3752675 : Blo 1108626 3752675 := bstep (se 1 (by rfl) ⟨2814506, by rfl⟩ : syracuseStep 3752675 = 5629013) B5629013
theorem B4506353 : Blo 1108626 4506353 := bstep (se 2 (by rfl) ⟨1689882, by rfl⟩ : syracuseStep 4506353 = 3379765) B3379765
theorem B3163121 : Blo 1108626 3163121 := bstep (se 2 (by rfl) ⟨1186170, by rfl⟩ : syracuseStep 3163121 = 2372341) B2372341
theorem B3752945 : Blo 1108626 3752945 := bstep (se 2 (by rfl) ⟨1407354, by rfl⟩ : syracuseStep 3752945 = 2814709) B2814709
theorem B6931619 : Blo 1108626 6931619 := bstep (se 1 (by rfl) ⟨5198714, by rfl⟩ : syracuseStep 6931619 = 10397429) B10397429
theorem B5620913 : Blo 1108626 5620913 := bstep (se 2 (by rfl) ⟨2107842, by rfl⟩ : syracuseStep 5620913 = 4215685) B4215685
theorem B3163313 : Blo 1108626 3163313 := bstep (se 2 (by rfl) ⟨1186242, by rfl⟩ : syracuseStep 3163313 = 2372485) B2372485
theorem B2999501 : Blo 1108626 2999501 := bstep (se 3 (by rfl) ⟨562406, by rfl⟩ : syracuseStep 2999501 = 1124813) B1124813
theorem B4113713 : Blo 1108626 4113713 := bstep (se 2 (by rfl) ⟨1542642, by rfl⟩ : syracuseStep 4113713 = 3085285) B3085285
theorem B2999693 : Blo 1108626 2999693 := bstep (se 3 (by rfl) ⟨562442, by rfl⟩ : syracuseStep 2999693 = 1124885) B1124885
theorem B3556781 : Blo 1108626 3556781 := bstep (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) B1333793
theorem B3753485 : Blo 1108626 3753485 := bstep (se 3 (by rfl) ⟨703778, by rfl⟩ : syracuseStep 3753485 = 1407557) B1407557
theorem B2999825 : Blo 1108626 2999825 := bstep (se 2 (by rfl) ⟨1124934, by rfl⟩ : syracuseStep 2999825 = 2249869) B2249869
theorem B3753539 : Blo 1108626 3753539 := bstep (se 1 (by rfl) ⟨2815154, by rfl⟩ : syracuseStep 3753539 = 5630309) B5630309
theorem B4802125 : Blo 1108626 4802125 := bstep (se 3 (by rfl) ⟨900398, by rfl⟩ : syracuseStep 4802125 = 1800797) B1800797
theorem B3556973 : Blo 1108626 3556973 := bstep (se 3 (by rfl) ⟨666932, by rfl⟩ : syracuseStep 3556973 = 1333865) B1333865
theorem B1689347 : Blo 1108626 1689347 := bstep (se 1 (by rfl) ⟨1267010, by rfl⟩ : syracuseStep 1689347 = 2534021) B2534021
theorem B4212557 : Blo 1108626 4212557 := bstep (se 3 (by rfl) ⟨789854, by rfl⟩ : syracuseStep 4212557 = 1579709) B1579709
theorem B3753809 : Blo 1108626 3753809 := bstep (se 2 (by rfl) ⟨1407678, by rfl⟩ : syracuseStep 3753809 = 2815357) B2815357
theorem B3164305 : Blo 1108626 3164305 := bstep (se 2 (by rfl) ⟨1186614, by rfl⟩ : syracuseStep 3164305 = 2373229) B2373229
theorem B3754349 : Blo 1108626 3754349 := bstep (se 3 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 3754349 = 1407881) B1407881
theorem B3164579 : Blo 1108626 3164579 := bstep (se 1 (by rfl) ⟨2373434, by rfl⟩ : syracuseStep 3164579 = 4746869) B4746869
theorem B3754403 : Blo 1108626 3754403 := bstep (se 1 (by rfl) ⟨2815802, by rfl⟩ : syracuseStep 3754403 = 5631605) B5631605
theorem B4737521 : Blo 1108626 4737521 := bstep (se 2 (by rfl) ⟨1776570, by rfl⟩ : syracuseStep 4737521 = 3553141) B3553141
theorem B5622371 : Blo 1108626 5622371 := bstep (se 1 (by rfl) ⟨4216778, by rfl⟩ : syracuseStep 5622371 = 8433557) B8433557
theorem B3164771 : Blo 1108626 3164771 := bstep (se 1 (by rfl) ⟨2373578, by rfl⟩ : syracuseStep 3164771 = 4747157) B4747157
theorem B3754673 : Blo 1108626 3754673 := bstep (se 2 (by rfl) ⟨1408002, by rfl⟩ : syracuseStep 3754673 = 2816005) B2816005
theorem B3001553 : Blo 1108626 3001553 := bstep (se 2 (by rfl) ⟨1125582, by rfl⟩ : syracuseStep 3001553 = 2251165) B2251165
theorem B9489635 : Blo 1108626 9489635 := bstep (se 1 (by rfl) ⟨7117226, by rfl⟩ : syracuseStep 9489635 = 14234453) B14234453
theorem B3558755 : Blo 1108626 3558755 := bstep (se 1 (by rfl) ⟨2669066, by rfl⟩ : syracuseStep 3558755 = 5338133) B5338133
theorem B3165581 : Blo 1108626 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B4738445 : Blo 1108626 4738445 := bstep (se 3 (by rfl) ⟨888458, by rfl⟩ : syracuseStep 4738445 = 1776917) B1776917
theorem B5623181 : Blo 1108626 5623181 := bstep (se 3 (by rfl) ⟨1054346, by rfl⟩ : syracuseStep 5623181 = 2108693) B2108693
theorem B3165763 : Blo 1108626 3165763 := bstep (se 1 (by rfl) ⟨2374322, by rfl⟩ : syracuseStep 3165763 = 4748645) B4748645
theorem B10801037 : Blo 1108626 10801037 := bstep (se 3 (by rfl) ⟨2025194, by rfl⟩ : syracuseStep 10801037 = 4050389) B4050389
theorem B3166253 : Blo 1108626 3166253 := bstep (se 3 (by rfl) ⟨593672, by rfl⟩ : syracuseStep 3166253 = 1187345) B1187345
theorem B12636485 : Blo 1108626 12636485 := bstep (se 4 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 12636485 = 2369341) B2369341
theorem B17125829 : Blo 1108626 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B8999437 : Blo 1108626 8999437 := bstep (se 3 (by rfl) ⟨1687394, by rfl⟩ : syracuseStep 8999437 = 3374789) B3374789
theorem B16011917 : Blo 1108626 16011917 := bstep (se 3 (by rfl) ⟨3002234, by rfl⟩ : syracuseStep 16011917 = 6004469) B6004469
theorem B4215473 : Blo 1108626 4215473 := bstep (se 2 (by rfl) ⟨1580802, by rfl⟩ : syracuseStep 4215473 = 3161605) B3161605
theorem B2806609 : Blo 1108626 2806609 := bstep (se 2 (by rfl) ⟨1052478, by rfl⟩ : syracuseStep 2806609 = 2104957) B2104957
theorem B4805489 : Blo 1108626 4805489 := bstep (se 2 (by rfl) ⟨1802058, by rfl⟩ : syracuseStep 4805489 = 3604117) B3604117
theorem B2806883 : Blo 1108626 2806883 := bstep (se 1 (by rfl) ⟨2105162, by rfl⟩ : syracuseStep 2806883 = 4210325) B4210325
theorem B3167437 : Blo 1108626 3167437 := bstep (se 3 (by rfl) ⟨593894, by rfl⟩ : syracuseStep 3167437 = 1187789) B1187789
theorem B2807075 : Blo 1108626 2807075 := bstep (se 1 (by rfl) ⟨2105306, by rfl⟩ : syracuseStep 2807075 = 4210613) B4210613
theorem B8443277 : Blo 1108626 8443277 := bstep (se 3 (by rfl) ⟨1583114, by rfl⟩ : syracuseStep 8443277 = 3166229) B3166229
theorem B3560881 : Blo 1108626 3560881 := bstep (se 2 (by rfl) ⟨1335330, by rfl⟩ : syracuseStep 3560881 = 2670661) B2670661
theorem B1332659 : Blo 1108626 1332659 := bstep (se 1 (by rfl) ⟨999494, by rfl⟩ : syracuseStep 1332659 = 1998989) B1998989
theorem B13489861 : Blo 1108626 13489861 := bstep (se 4 (by rfl) ⟨1264674, by rfl⟩ : syracuseStep 13489861 = 2529349) B2529349
theorem B1332947 : Blo 1108626 1332947 := bstep (se 1 (by rfl) ⟨999710, by rfl⟩ : syracuseStep 1332947 = 1999421) B1999421
theorem B1333139 : Blo 1108626 1333139 := bstep (se 1 (by rfl) ⟨999854, by rfl⟩ : syracuseStep 1333139 = 1999709) B1999709
theorem B2250833 : Blo 1108626 2250833 := bstep (se 2 (by rfl) ⟨844062, by rfl⟩ : syracuseStep 2250833 = 1688125) B1688125
theorem B4216931 : Blo 1108626 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B2808017 : Blo 1108626 2808017 := bstep (se 2 (by rfl) ⟨1053006, by rfl⟩ : syracuseStep 2808017 = 2106013) B2106013
theorem B66771157 : Blo 1108626 66771157 := bstep (se 7 (by rfl) ⟨782474, by rfl⟩ : syracuseStep 66771157 = 1564949) B1564949
theorem B12015857 : Blo 1108626 12015857 := bstep (se 2 (by rfl) ⟨4505946, by rfl⟩ : syracuseStep 12015857 = 9011893) B9011893
theorem B5626097 : Blo 1108626 5626097 := bstep (se 2 (by rfl) ⟨2109786, by rfl⟩ : syracuseStep 5626097 = 4219573) B4219573
theorem B2808067 : Blo 1108626 2808067 := bstep (se 1 (by rfl) ⟨2106050, by rfl⟩ : syracuseStep 2808067 = 4212101) B4212101
theorem B2808209 : Blo 1108626 2808209 := bstep (se 2 (by rfl) ⟨1053078, by rfl⟩ : syracuseStep 2808209 = 2106157) B2106157
theorem B4741553 : Blo 1108626 4741553 := bstep (se 2 (by rfl) ⟨1778082, by rfl⟩ : syracuseStep 4741553 = 3556165) B3556165
theorem B1268707 : Blo 1108626 1268707 := bstep (se 1 (by rfl) ⟨951530, by rfl⟩ : syracuseStep 1268707 = 1903061) B1903061
theorem B4217933 : Blo 1108626 4217933 := bstep (se 3 (by rfl) ⟨790862, by rfl⟩ : syracuseStep 4217933 = 1581725) B1581725
theorem B3562829 : Blo 1108626 3562829 := bstep (se 3 (by rfl) ⟨668030, by rfl⟩ : syracuseStep 3562829 = 1336061) B1336061
theorem B2809201 : Blo 1108626 2809201 := bstep (se 2 (by rfl) ⟨1053450, by rfl⟩ : syracuseStep 2809201 = 2106901) B2106901
theorem B3562957 : Blo 1108626 3562957 := bstep (se 3 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 3562957 = 1336109) B1336109
theorem B2809475 : Blo 1108626 2809475 := bstep (se 1 (by rfl) ⟨2107106, by rfl⟩ : syracuseStep 2809475 = 4214213) B4214213
theorem B4742819 : Blo 1108626 4742819 := bstep (se 1 (by rfl) ⟨3557114, by rfl⟩ : syracuseStep 4742819 = 7114229) B7114229
theorem B5627555 : Blo 1108626 5627555 := bstep (se 1 (by rfl) ⟨4220666, by rfl⟩ : syracuseStep 5627555 = 8441333) B8441333
theorem B30432995 : Blo 1108626 30432995 := bstep (se 1 (by rfl) ⟨22824746, by rfl⟩ : syracuseStep 30432995 = 45649493) B45649493
theorem B2809667 : Blo 1108626 2809667 := bstep (se 1 (by rfl) ⟨2107250, by rfl⟩ : syracuseStep 2809667 = 4214501) B4214501
theorem B2252657 : Blo 1108626 2252657 := bstep (se 2 (by rfl) ⟨844746, by rfl⟩ : syracuseStep 2252657 = 1689493) B1689493
theorem B1662947 : Blo 1108626 1662947 := bstep (se 1 (by rfl) ⟨1247210, by rfl⟩ : syracuseStep 1662947 = 2494421) B2494421
theorem B1662977 : Blo 1108626 1662977 := bstep (se 2 (by rfl) ⟨623616, by rfl⟩ : syracuseStep 1662977 = 1247233) B1247233
theorem B1662995 : Blo 1108626 1662995 := bstep (se 1 (by rfl) ⟨1247246, by rfl⟩ : syracuseStep 1662995 = 2494493) B2494493
theorem B1663025 : Blo 1108626 1663025 := bstep (se 2 (by rfl) ⟨623634, by rfl⟩ : syracuseStep 1663025 = 1247269) B1247269
theorem B1663043 : Blo 1108626 1663043 := bstep (se 1 (by rfl) ⟨1247282, by rfl⟩ : syracuseStep 1663043 = 2494565) B2494565
theorem B1663073 : Blo 1108626 1663073 := bstep (se 2 (by rfl) ⟨623652, by rfl⟩ : syracuseStep 1663073 = 1247305) B1247305
theorem B1663091 : Blo 1108626 1663091 := bstep (se 1 (by rfl) ⟨1247318, by rfl⟩ : syracuseStep 1663091 = 2494637) B2494637
theorem B1663121 : Blo 1108626 1663121 := bstep (se 2 (by rfl) ⟨623670, by rfl⟩ : syracuseStep 1663121 = 1247341) B1247341
theorem B1663139 : Blo 1108626 1663139 := bstep (se 1 (by rfl) ⟨1247354, by rfl⟩ : syracuseStep 1663139 = 2494709) B2494709
theorem B1663169 : Blo 1108626 1663169 := bstep (se 2 (by rfl) ⟨623688, by rfl⟩ : syracuseStep 1663169 = 1247377) B1247377
theorem B7594181 : Blo 1108626 7594181 := bstep (se 4 (by rfl) ⟨711954, by rfl⟩ : syracuseStep 7594181 = 1423909) B1423909
theorem B1663187 : Blo 1108626 1663187 := bstep (se 1 (by rfl) ⟨1247390, by rfl⟩ : syracuseStep 1663187 = 2494781) B2494781
theorem B1663217 : Blo 1108626 1663217 := bstep (se 2 (by rfl) ⟨623706, by rfl⟩ : syracuseStep 1663217 = 1247413) B1247413
theorem B8446193 : Blo 1108626 8446193 := bstep (se 2 (by rfl) ⟨3167322, by rfl⟩ : syracuseStep 8446193 = 6334645) B6334645
theorem B1663235 : Blo 1108626 1663235 := bstep (se 1 (by rfl) ⟨1247426, by rfl⟩ : syracuseStep 1663235 = 2494853) B2494853
theorem B3006733 : Blo 1108626 3006733 := bstep (se 3 (by rfl) ⟨563762, by rfl⟩ : syracuseStep 3006733 = 1127525) B1127525
theorem B1663265 : Blo 1108626 1663265 := bstep (se 2 (by rfl) ⟨623724, by rfl⟩ : syracuseStep 1663265 = 1247449) B1247449
theorem B1663283 : Blo 1108626 1663283 := bstep (se 1 (by rfl) ⟨1247462, by rfl⟩ : syracuseStep 1663283 = 2494925) B2494925
theorem B1335619 : Blo 1108626 1335619 := bstep (se 1 (by rfl) ⟨1001714, by rfl⟩ : syracuseStep 1335619 = 2003429) B2003429
theorem B1663313 : Blo 1108626 1663313 := bstep (se 2 (by rfl) ⟨623742, by rfl⟩ : syracuseStep 1663313 = 1247485) B1247485
theorem B1663331 : Blo 1108626 1663331 := bstep (se 1 (by rfl) ⟨1247498, by rfl⟩ : syracuseStep 1663331 = 2494997) B2494997
theorem B3006829 : Blo 1108626 3006829 := bstep (se 3 (by rfl) ⟨563780, by rfl⟩ : syracuseStep 3006829 = 1127561) B1127561
theorem B1663361 : Blo 1108626 1663361 := bstep (se 2 (by rfl) ⟨623760, by rfl⟩ : syracuseStep 1663361 = 1247521) B1247521
theorem B1663379 : Blo 1108626 1663379 := bstep (se 1 (by rfl) ⟨1247534, by rfl⟩ : syracuseStep 1663379 = 2495069) B2495069
theorem B1663409 : Blo 1108626 1663409 := bstep (se 2 (by rfl) ⟨623778, by rfl⟩ : syracuseStep 1663409 = 1247557) B1247557
theorem B1663427 : Blo 1108626 1663427 := bstep (se 1 (by rfl) ⟨1247570, by rfl⟩ : syracuseStep 1663427 = 2495141) B2495141
theorem B5628365 : Blo 1108626 5628365 := bstep (se 3 (by rfl) ⟨1055318, by rfl⟩ : syracuseStep 5628365 = 2110637) B2110637
theorem B1663457 : Blo 1108626 1663457 := bstep (se 2 (by rfl) ⟨623796, by rfl⟩ : syracuseStep 1663457 = 1247593) B1247593
theorem B1663475 : Blo 1108626 1663475 := bstep (se 1 (by rfl) ⟨1247606, by rfl⟩ : syracuseStep 1663475 = 2495213) B2495213
theorem B1663505 : Blo 1108626 1663505 := bstep (se 2 (by rfl) ⟨623814, by rfl⟩ : syracuseStep 1663505 = 1247629) B1247629
theorem B1663523 : Blo 1108626 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B1663553 : Blo 1108626 1663553 := bstep (se 2 (by rfl) ⟨623832, by rfl⟩ : syracuseStep 1663553 = 1247665) B1247665
theorem B1663571 : Blo 1108626 1663571 := bstep (se 1 (by rfl) ⟨1247678, by rfl⟩ : syracuseStep 1663571 = 2495357) B2495357
theorem B1335907 : Blo 1108626 1335907 := bstep (se 1 (by rfl) ⟨1001930, by rfl⟩ : syracuseStep 1335907 = 2003861) B2003861
theorem B1663601 : Blo 1108626 1663601 := bstep (se 2 (by rfl) ⟨623850, by rfl⟩ : syracuseStep 1663601 = 1247701) B1247701
theorem B1663619 : Blo 1108626 1663619 := bstep (se 1 (by rfl) ⟨1247714, by rfl⟩ : syracuseStep 1663619 = 2495429) B2495429
theorem B1663649 : Blo 1108626 1663649 := bstep (se 2 (by rfl) ⟨623868, by rfl⟩ : syracuseStep 1663649 = 1247737) B1247737
theorem B1663667 : Blo 1108626 1663667 := bstep (se 1 (by rfl) ⟨1247750, by rfl⟩ : syracuseStep 1663667 = 2495501) B2495501
theorem B1663697 : Blo 1108626 1663697 := bstep (se 2 (by rfl) ⟨623886, by rfl⟩ : syracuseStep 1663697 = 1247773) B1247773
theorem B1663715 : Blo 1108626 1663715 := bstep (se 1 (by rfl) ⟨1247786, by rfl⟩ : syracuseStep 1663715 = 2495573) B2495573
theorem B2810609 : Blo 1108626 2810609 := bstep (se 2 (by rfl) ⟨1053978, by rfl⟩ : syracuseStep 2810609 = 2107957) B2107957
theorem B1663745 : Blo 1108626 1663745 := bstep (se 2 (by rfl) ⟨623904, by rfl⟩ : syracuseStep 1663745 = 1247809) B1247809
theorem B1663763 : Blo 1108626 1663763 := bstep (se 1 (by rfl) ⟨1247822, by rfl⟩ : syracuseStep 1663763 = 2495645) B2495645
theorem B2810659 : Blo 1108626 2810659 := bstep (se 1 (by rfl) ⟨2107994, by rfl⟩ : syracuseStep 2810659 = 4215989) B4215989
theorem B1663793 : Blo 1108626 1663793 := bstep (se 2 (by rfl) ⟨623922, by rfl⟩ : syracuseStep 1663793 = 1247845) B1247845
theorem B1663811 : Blo 1108626 1663811 := bstep (se 1 (by rfl) ⟨1247858, by rfl⟩ : syracuseStep 1663811 = 2495717) B2495717
theorem B1663841 : Blo 1108626 1663841 := bstep (se 2 (by rfl) ⟨623940, by rfl⟩ : syracuseStep 1663841 = 1247881) B1247881
theorem B1663859 : Blo 1108626 1663859 := bstep (se 1 (by rfl) ⟨1247894, by rfl⟩ : syracuseStep 1663859 = 2495789) B2495789
theorem B1663889 : Blo 1108626 1663889 := bstep (se 2 (by rfl) ⟨623958, by rfl⟩ : syracuseStep 1663889 = 1247917) B1247917
theorem B1663907 : Blo 1108626 1663907 := bstep (se 1 (by rfl) ⟨1247930, by rfl⟩ : syracuseStep 1663907 = 2495861) B2495861
theorem B2810801 : Blo 1108626 2810801 := bstep (se 2 (by rfl) ⟨1054050, by rfl⟩ : syracuseStep 2810801 = 2108101) B2108101
theorem B1663937 : Blo 1108626 1663937 := bstep (se 2 (by rfl) ⟨623976, by rfl⟩ : syracuseStep 1663937 = 1247953) B1247953
theorem B1663955 : Blo 1108626 1663955 := bstep (se 1 (by rfl) ⟨1247966, by rfl⟩ : syracuseStep 1663955 = 2495933) B2495933
theorem B1663985 : Blo 1108626 1663985 := bstep (se 2 (by rfl) ⟨623994, by rfl⟩ : syracuseStep 1663985 = 1247989) B1247989
theorem B1664003 : Blo 1108626 1664003 := bstep (se 1 (by rfl) ⟨1248002, by rfl⟩ : syracuseStep 1664003 = 2496005) B2496005
theorem B1664033 : Blo 1108626 1664033 := bstep (se 2 (by rfl) ⟨624012, by rfl⟩ : syracuseStep 1664033 = 1248025) B1248025
theorem B1664051 : Blo 1108626 1664051 := bstep (se 1 (by rfl) ⟨1248038, by rfl⟩ : syracuseStep 1664051 = 2496077) B2496077
theorem B1664081 : Blo 1108626 1664081 := bstep (se 2 (by rfl) ⟨624030, by rfl⟩ : syracuseStep 1664081 = 1248061) B1248061
theorem B1664099 : Blo 1108626 1664099 := bstep (se 1 (by rfl) ⟨1248074, by rfl⟩ : syracuseStep 1664099 = 2496149) B2496149
theorem B1664129 : Blo 1108626 1664129 := bstep (se 2 (by rfl) ⟨624048, by rfl⟩ : syracuseStep 1664129 = 1248097) B1248097
theorem B4220045 : Blo 1108626 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B1664147 : Blo 1108626 1664147 := bstep (se 1 (by rfl) ⟨1248110, by rfl⟩ : syracuseStep 1664147 = 2496221) B2496221
theorem B1664177 : Blo 1108626 1664177 := bstep (se 2 (by rfl) ⟨624066, by rfl⟩ : syracuseStep 1664177 = 1248133) B1248133
theorem B1664195 : Blo 1108626 1664195 := bstep (se 1 (by rfl) ⟨1248146, by rfl⟩ : syracuseStep 1664195 = 2496293) B2496293
theorem B1664225 : Blo 1108626 1664225 := bstep (se 2 (by rfl) ⟨624084, by rfl⟩ : syracuseStep 1664225 = 1248169) B1248169
theorem B1664243 : Blo 1108626 1664243 := bstep (se 1 (by rfl) ⟨1248182, by rfl⟩ : syracuseStep 1664243 = 2496365) B2496365
theorem B1664273 : Blo 1108626 1664273 := bstep (se 2 (by rfl) ⟨624102, by rfl⟩ : syracuseStep 1664273 = 1248205) B1248205
theorem B1664291 : Blo 1108626 1664291 := bstep (se 1 (by rfl) ⟨1248218, by rfl⟩ : syracuseStep 1664291 = 2496437) B2496437
theorem B1664321 : Blo 1108626 1664321 := bstep (se 2 (by rfl) ⟨624120, by rfl⟩ : syracuseStep 1664321 = 1248241) B1248241
theorem B7595333 : Blo 1108626 7595333 := bstep (se 4 (by rfl) ⟨712062, by rfl⟩ : syracuseStep 7595333 = 1424125) B1424125
theorem B7103821 : Blo 1108626 7103821 := bstep (se 3 (by rfl) ⟨1331966, by rfl⟩ : syracuseStep 7103821 = 2663933) B2663933
theorem B1664339 : Blo 1108626 1664339 := bstep (se 1 (by rfl) ⟨1248254, by rfl⟩ : syracuseStep 1664339 = 2496509) B2496509
theorem B1664369 : Blo 1108626 1664369 := bstep (se 2 (by rfl) ⟨624138, by rfl⟩ : syracuseStep 1664369 = 1248277) B1248277
theorem B1664387 : Blo 1108626 1664387 := bstep (se 1 (by rfl) ⟨1248290, by rfl⟩ : syracuseStep 1664387 = 2496581) B2496581
theorem B1664417 : Blo 1108626 1664417 := bstep (se 2 (by rfl) ⟨624156, by rfl⟩ : syracuseStep 1664417 = 1248313) B1248313
theorem B1664435 : Blo 1108626 1664435 := bstep (se 1 (by rfl) ⟨1248326, by rfl⟩ : syracuseStep 1664435 = 2496653) B2496653
theorem B1664465 : Blo 1108626 1664465 := bstep (se 2 (by rfl) ⟨624174, by rfl⟩ : syracuseStep 1664465 = 1248349) B1248349
theorem B1664483 : Blo 1108626 1664483 := bstep (se 1 (by rfl) ⟨1248362, by rfl⟩ : syracuseStep 1664483 = 2496725) B2496725
theorem B10118641 : Blo 1108626 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B1664513 : Blo 1108626 1664513 := bstep (se 2 (by rfl) ⟨624192, by rfl⟩ : syracuseStep 1664513 = 1248385) B1248385
theorem B1664531 : Blo 1108626 1664531 := bstep (se 1 (by rfl) ⟨1248398, by rfl⟩ : syracuseStep 1664531 = 2496797) B2496797
theorem B1664561 : Blo 1108626 1664561 := bstep (se 2 (by rfl) ⟨624210, by rfl⟩ : syracuseStep 1664561 = 1248421) B1248421
theorem B1664579 : Blo 1108626 1664579 := bstep (se 1 (by rfl) ⟨1248434, by rfl⟩ : syracuseStep 1664579 = 2496869) B2496869
theorem B1664609 : Blo 1108626 1664609 := bstep (se 2 (by rfl) ⟨624228, by rfl⟩ : syracuseStep 1664609 = 1248457) B1248457
theorem B1664627 : Blo 1108626 1664627 := bstep (se 1 (by rfl) ⟨1248470, by rfl⟩ : syracuseStep 1664627 = 2496941) B2496941
theorem B1664657 : Blo 1108626 1664657 := bstep (se 2 (by rfl) ⟨624246, by rfl⟩ : syracuseStep 1664657 = 1248493) B1248493
theorem B1664675 : Blo 1108626 1664675 := bstep (se 1 (by rfl) ⟨1248506, by rfl⟩ : syracuseStep 1664675 = 2497013) B2497013
theorem B1664705 : Blo 1108626 1664705 := bstep (se 2 (by rfl) ⟨624264, by rfl⟩ : syracuseStep 1664705 = 1248529) B1248529
theorem B1664723 : Blo 1108626 1664723 := bstep (se 1 (by rfl) ⟨1248542, by rfl⟩ : syracuseStep 1664723 = 2497085) B2497085
theorem B1664753 : Blo 1108626 1664753 := bstep (se 2 (by rfl) ⟨624282, by rfl⟩ : syracuseStep 1664753 = 1248565) B1248565
theorem B1664771 : Blo 1108626 1664771 := bstep (se 1 (by rfl) ⟨1248578, by rfl⟩ : syracuseStep 1664771 = 2497157) B2497157
theorem B1664801 : Blo 1108626 1664801 := bstep (se 2 (by rfl) ⟨624300, by rfl⟩ : syracuseStep 1664801 = 1248601) B1248601
theorem B1664819 : Blo 1108626 1664819 := bstep (se 1 (by rfl) ⟨1248614, by rfl⟩ : syracuseStep 1664819 = 2497229) B2497229
theorem B1664849 : Blo 1108626 1664849 := bstep (se 2 (by rfl) ⟨624318, by rfl⟩ : syracuseStep 1664849 = 1248637) B1248637
theorem B1664867 : Blo 1108626 1664867 := bstep (se 1 (by rfl) ⟨1248650, by rfl⟩ : syracuseStep 1664867 = 2497301) B2497301
theorem B1664897 : Blo 1108626 1664897 := bstep (se 2 (by rfl) ⟨624336, by rfl⟩ : syracuseStep 1664897 = 1248673) B1248673
theorem B2811793 : Blo 1108626 2811793 := bstep (se 2 (by rfl) ⟨1054422, by rfl⟩ : syracuseStep 2811793 = 2108845) B2108845
theorem B1664915 : Blo 1108626 1664915 := bstep (se 1 (by rfl) ⟨1248686, by rfl⟩ : syracuseStep 1664915 = 2497373) B2497373
theorem B1664945 : Blo 1108626 1664945 := bstep (se 2 (by rfl) ⟨624354, by rfl⟩ : syracuseStep 1664945 = 1248709) B1248709
theorem B4220849 : Blo 1108626 4220849 := bstep (se 2 (by rfl) ⟨1582818, by rfl⟩ : syracuseStep 4220849 = 3165637) B3165637
theorem B1664963 : Blo 1108626 1664963 := bstep (se 1 (by rfl) ⟨1248722, by rfl⟩ : syracuseStep 1664963 = 2497445) B2497445
theorem B1664993 : Blo 1108626 1664993 := bstep (se 2 (by rfl) ⟨624372, by rfl⟩ : syracuseStep 1664993 = 1248745) B1248745
theorem B1665011 : Blo 1108626 1665011 := bstep (se 1 (by rfl) ⟨1248758, by rfl⟩ : syracuseStep 1665011 = 2497517) B2497517
theorem B12642317 : Blo 1108626 12642317 := bstep (se 3 (by rfl) ⟨2370434, by rfl⟩ : syracuseStep 12642317 = 4740869) B4740869
theorem B1665041 : Blo 1108626 1665041 := bstep (se 2 (by rfl) ⟨624390, by rfl⟩ : syracuseStep 1665041 = 1248781) B1248781
theorem B1665059 : Blo 1108626 1665059 := bstep (se 1 (by rfl) ⟨1248794, by rfl⟩ : syracuseStep 1665059 = 2497589) B2497589
theorem B1665089 : Blo 1108626 1665089 := bstep (se 2 (by rfl) ⟨624408, by rfl⟩ : syracuseStep 1665089 = 1248817) B1248817
theorem B3795011 : Blo 1108626 3795011 := bstep (se 1 (by rfl) ⟨2846258, by rfl⟩ : syracuseStep 3795011 = 5692517) B5692517
theorem B1665107 : Blo 1108626 1665107 := bstep (se 1 (by rfl) ⟨1248830, by rfl⟩ : syracuseStep 1665107 = 2497661) B2497661
theorem B1665137 : Blo 1108626 1665137 := bstep (se 2 (by rfl) ⟨624426, by rfl⟩ : syracuseStep 1665137 = 1248853) B1248853
theorem B1665155 : Blo 1108626 1665155 := bstep (se 1 (by rfl) ⟨1248866, by rfl⟩ : syracuseStep 1665155 = 2497733) B2497733
theorem B1665185 : Blo 1108626 1665185 := bstep (se 2 (by rfl) ⟨624444, by rfl⟩ : syracuseStep 1665185 = 1248889) B1248889
theorem B2812067 : Blo 1108626 2812067 := bstep (se 1 (by rfl) ⟨2109050, by rfl⟩ : syracuseStep 2812067 = 4218101) B4218101
theorem B1665203 : Blo 1108626 1665203 := bstep (se 1 (by rfl) ⟨1248902, by rfl⟩ : syracuseStep 1665203 = 2497805) B2497805
theorem B1665233 : Blo 1108626 1665233 := bstep (se 2 (by rfl) ⟨624462, by rfl⟩ : syracuseStep 1665233 = 1248925) B1248925
theorem B1665251 : Blo 1108626 1665251 := bstep (se 1 (by rfl) ⟨1248938, by rfl⟩ : syracuseStep 1665251 = 2497877) B2497877
theorem B1665281 : Blo 1108626 1665281 := bstep (se 2 (by rfl) ⟨624480, by rfl⟩ : syracuseStep 1665281 = 1248961) B1248961
theorem B1665299 : Blo 1108626 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B1665329 : Blo 1108626 1665329 := bstep (se 2 (by rfl) ⟨624498, by rfl⟩ : syracuseStep 1665329 = 1248997) B1248997
theorem B1665347 : Blo 1108626 1665347 := bstep (se 1 (by rfl) ⟨1249010, by rfl⟩ : syracuseStep 1665347 = 2498021) B2498021
theorem B1665377 : Blo 1108626 1665377 := bstep (se 2 (by rfl) ⟨624516, by rfl⟩ : syracuseStep 1665377 = 1249033) B1249033
theorem B2812259 : Blo 1108626 2812259 := bstep (se 1 (by rfl) ⟨2109194, by rfl⟩ : syracuseStep 2812259 = 4218389) B4218389
theorem B1665395 : Blo 1108626 1665395 := bstep (se 1 (by rfl) ⟨1249046, by rfl⟩ : syracuseStep 1665395 = 2498093) B2498093
theorem B1665425 : Blo 1108626 1665425 := bstep (se 2 (by rfl) ⟨624534, by rfl⟩ : syracuseStep 1665425 = 1249069) B1249069
theorem B1665443 : Blo 1108626 1665443 := bstep (se 1 (by rfl) ⟨1249082, by rfl⟩ : syracuseStep 1665443 = 2498165) B2498165
theorem B1665473 : Blo 1108626 1665473 := bstep (se 2 (by rfl) ⟨624552, by rfl⟩ : syracuseStep 1665473 = 1249105) B1249105
theorem B39053765 : Blo 1108626 39053765 := bstep (se 4 (by rfl) ⟨3661290, by rfl⟩ : syracuseStep 39053765 = 7322581) B7322581
theorem B1665491 : Blo 1108626 1665491 := bstep (se 1 (by rfl) ⟨1249118, by rfl⟩ : syracuseStep 1665491 = 2498237) B2498237
theorem B1665521 : Blo 1108626 1665521 := bstep (se 2 (by rfl) ⟨624570, by rfl⟩ : syracuseStep 1665521 = 1249141) B1249141
theorem B1665539 : Blo 1108626 1665539 := bstep (se 1 (by rfl) ⟨1249154, by rfl⟩ : syracuseStep 1665539 = 2498309) B2498309
theorem B1665569 : Blo 1108626 1665569 := bstep (se 2 (by rfl) ⟨624588, by rfl⟩ : syracuseStep 1665569 = 1249177) B1249177
theorem B1665587 : Blo 1108626 1665587 := bstep (se 1 (by rfl) ⟨1249190, by rfl⟩ : syracuseStep 1665587 = 2498381) B2498381
theorem B4221517 : Blo 1108626 4221517 := bstep (se 3 (by rfl) ⟨791534, by rfl⟩ : syracuseStep 4221517 = 1583069) B1583069
theorem B1665617 : Blo 1108626 1665617 := bstep (se 2 (by rfl) ⟨624606, by rfl⟩ : syracuseStep 1665617 = 1249213) B1249213
theorem B1665635 : Blo 1108626 1665635 := bstep (se 1 (by rfl) ⟨1249226, by rfl⟩ : syracuseStep 1665635 = 2498453) B2498453
theorem B14248547 : Blo 1108626 14248547 := bstep (se 1 (by rfl) ⟨10686410, by rfl⟩ : syracuseStep 14248547 = 21372821) B21372821
theorem B1403507 : Blo 1108626 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B1665665 : Blo 1108626 1665665 := bstep (se 2 (by rfl) ⟨624624, by rfl⟩ : syracuseStep 1665665 = 1249249) B1249249
theorem B1108627 : Blo 1108626 1108627 := bstep (se 1 (by rfl) ⟨831470, by rfl⟩ : syracuseStep 1108627 = 1662941) B1662941
theorem B1665683 : Blo 1108626 1665683 := bstep (se 1 (by rfl) ⟨1249262, by rfl⟩ : syracuseStep 1665683 = 2498525) B2498525
theorem B1108643 : Blo 1108626 1108643 := bstep (se 1 (by rfl) ⟨831482, by rfl⟩ : syracuseStep 1108643 = 1662965) B1662965
theorem B1665713 : Blo 1108626 1665713 := bstep (se 2 (by rfl) ⟨624642, by rfl⟩ : syracuseStep 1665713 = 1249285) B1249285
theorem B1108659 : Blo 1108626 1108659 := bstep (se 1 (by rfl) ⟨831494, by rfl⟩ : syracuseStep 1108659 = 1662989) B1662989
theorem B1108675 : Blo 1108626 1108675 := bstep (se 1 (by rfl) ⟨831506, by rfl⟩ : syracuseStep 1108675 = 1663013) B1663013
theorem B1665731 : Blo 1108626 1665731 := bstep (se 1 (by rfl) ⟨1249298, by rfl⟩ : syracuseStep 1665731 = 2498597) B2498597
theorem B3795665 : Blo 1108626 3795665 := bstep (se 2 (by rfl) ⟨1423374, by rfl⟩ : syracuseStep 3795665 = 2846749) B2846749
theorem B1108691 : Blo 1108626 1108691 := bstep (se 1 (by rfl) ⟨831518, by rfl⟩ : syracuseStep 1108691 = 1663037) B1663037
theorem B1665761 : Blo 1108626 1665761 := bstep (se 2 (by rfl) ⟨624660, by rfl⟩ : syracuseStep 1665761 = 1249321) B1249321
theorem B1108707 : Blo 1108626 1108707 := bstep (se 1 (by rfl) ⟨831530, by rfl⟩ : syracuseStep 1108707 = 1663061) B1663061
theorem B1108723 : Blo 1108626 1108723 := bstep (se 1 (by rfl) ⟨831542, by rfl⟩ : syracuseStep 1108723 = 1663085) B1663085
theorem B1665779 : Blo 1108626 1665779 := bstep (se 1 (by rfl) ⟨1249334, by rfl⟩ : syracuseStep 1665779 = 2498669) B2498669
theorem B1108739 : Blo 1108626 1108739 := bstep (se 1 (by rfl) ⟨831554, by rfl⟩ : syracuseStep 1108739 = 1663109) B1663109
theorem B1665809 : Blo 1108626 1665809 := bstep (se 2 (by rfl) ⟨624678, by rfl⟩ : syracuseStep 1665809 = 1249357) B1249357
theorem B1108755 : Blo 1108626 1108755 := bstep (se 1 (by rfl) ⟨831566, by rfl⟩ : syracuseStep 1108755 = 1663133) B1663133
theorem B1108771 : Blo 1108626 1108771 := bstep (se 1 (by rfl) ⟨831578, by rfl⟩ : syracuseStep 1108771 = 1663157) B1663157
theorem B1665827 : Blo 1108626 1665827 := bstep (se 1 (by rfl) ⟨1249370, by rfl⟩ : syracuseStep 1665827 = 2498741) B2498741
theorem B1108787 : Blo 1108626 1108787 := bstep (se 1 (by rfl) ⟨831590, by rfl⟩ : syracuseStep 1108787 = 1663181) B1663181
theorem B1665857 : Blo 1108626 1665857 := bstep (se 2 (by rfl) ⟨624696, by rfl⟩ : syracuseStep 1665857 = 1249393) B1249393
theorem B1108803 : Blo 1108626 1108803 := bstep (se 1 (by rfl) ⟨831602, by rfl⟩ : syracuseStep 1108803 = 1663205) B1663205
theorem B1108819 : Blo 1108626 1108819 := bstep (se 1 (by rfl) ⟨831614, by rfl⟩ : syracuseStep 1108819 = 1663229) B1663229
theorem B1665875 : Blo 1108626 1665875 := bstep (se 1 (by rfl) ⟨1249406, by rfl⟩ : syracuseStep 1665875 = 2498813) B2498813
theorem B1108835 : Blo 1108626 1108835 := bstep (se 1 (by rfl) ⟨831626, by rfl⟩ : syracuseStep 1108835 = 1663253) B1663253
theorem B1665905 : Blo 1108626 1665905 := bstep (se 2 (by rfl) ⟨624714, by rfl⟩ : syracuseStep 1665905 = 1249429) B1249429
theorem B1108851 : Blo 1108626 1108851 := bstep (se 1 (by rfl) ⟨831638, by rfl⟩ : syracuseStep 1108851 = 1663277) B1663277
theorem B1108867 : Blo 1108626 1108867 := bstep (se 1 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 1108867 = 1663301) B1663301
theorem B1665923 : Blo 1108626 1665923 := bstep (se 1 (by rfl) ⟨1249442, by rfl⟩ : syracuseStep 1665923 = 2498885) B2498885
theorem B1108883 : Blo 1108626 1108883 := bstep (se 1 (by rfl) ⟨831662, by rfl⟩ : syracuseStep 1108883 = 1663325) B1663325
theorem B1665953 : Blo 1108626 1665953 := bstep (se 2 (by rfl) ⟨624732, by rfl⟩ : syracuseStep 1665953 = 1249465) B1249465
theorem B1108899 : Blo 1108626 1108899 := bstep (se 1 (by rfl) ⟨831674, by rfl⟩ : syracuseStep 1108899 = 1663349) B1663349
theorem B1108915 : Blo 1108626 1108915 := bstep (se 1 (by rfl) ⟨831686, by rfl⟩ : syracuseStep 1108915 = 1663373) B1663373
theorem B1665971 : Blo 1108626 1665971 := bstep (se 1 (by rfl) ⟨1249478, by rfl⟩ : syracuseStep 1665971 = 2498957) B2498957
theorem B1108931 : Blo 1108626 1108931 := bstep (se 1 (by rfl) ⟨831698, by rfl⟩ : syracuseStep 1108931 = 1663397) B1663397
theorem B1666001 : Blo 1108626 1666001 := bstep (se 2 (by rfl) ⟨624750, by rfl⟩ : syracuseStep 1666001 = 1249501) B1249501
theorem B1108947 : Blo 1108626 1108947 := bstep (se 1 (by rfl) ⟨831710, by rfl⟩ : syracuseStep 1108947 = 1663421) B1663421
theorem B5401571 : Blo 1108626 5401571 := bstep (se 1 (by rfl) ⟨4051178, by rfl⟩ : syracuseStep 5401571 = 8102357) B8102357
theorem B1108963 : Blo 1108626 1108963 := bstep (se 1 (by rfl) ⟨831722, by rfl⟩ : syracuseStep 1108963 = 1663445) B1663445
theorem B1666019 : Blo 1108626 1666019 := bstep (se 1 (by rfl) ⟨1249514, by rfl⟩ : syracuseStep 1666019 = 2499029) B2499029
theorem B1108979 : Blo 1108626 1108979 := bstep (se 1 (by rfl) ⟨831734, by rfl⟩ : syracuseStep 1108979 = 1663469) B1663469
theorem B1666049 : Blo 1108626 1666049 := bstep (se 2 (by rfl) ⟨624768, by rfl⟩ : syracuseStep 1666049 = 1249537) B1249537
theorem B1108995 : Blo 1108626 1108995 := bstep (se 1 (by rfl) ⟨831746, by rfl⟩ : syracuseStep 1108995 = 1663493) B1663493
theorem B1109011 : Blo 1108626 1109011 := bstep (se 1 (by rfl) ⟨831758, by rfl⟩ : syracuseStep 1109011 = 1663517) B1663517
theorem B1666067 : Blo 1108626 1666067 := bstep (se 1 (by rfl) ⟨1249550, by rfl⟩ : syracuseStep 1666067 = 2499101) B2499101
theorem B1109027 : Blo 1108626 1109027 := bstep (se 1 (by rfl) ⟨831770, by rfl⟩ : syracuseStep 1109027 = 1663541) B1663541
theorem B1666097 : Blo 1108626 1666097 := bstep (se 2 (by rfl) ⟨624786, by rfl⟩ : syracuseStep 1666097 = 1249573) B1249573
theorem B1109043 : Blo 1108626 1109043 := bstep (se 1 (by rfl) ⟨831782, by rfl⟩ : syracuseStep 1109043 = 1663565) B1663565
theorem B1109059 : Blo 1108626 1109059 := bstep (se 1 (by rfl) ⟨831794, by rfl⟩ : syracuseStep 1109059 = 1663589) B1663589
theorem B1666115 : Blo 1108626 1666115 := bstep (se 1 (by rfl) ⟨1249586, by rfl⟩ : syracuseStep 1666115 = 2499173) B2499173
theorem B15199301 : Blo 1108626 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B1109075 : Blo 1108626 1109075 := bstep (se 1 (by rfl) ⟨831806, by rfl⟩ : syracuseStep 1109075 = 1663613) B1663613
theorem B1666145 : Blo 1108626 1666145 := bstep (se 2 (by rfl) ⟨624804, by rfl⟩ : syracuseStep 1666145 = 1249609) B1249609
theorem B1109091 : Blo 1108626 1109091 := bstep (se 1 (by rfl) ⟨831818, by rfl⟩ : syracuseStep 1109091 = 1663637) B1663637
theorem B3206243 : Blo 1108626 3206243 := bstep (se 1 (by rfl) ⟨2404682, by rfl⟩ : syracuseStep 3206243 = 4809365) B4809365
theorem B1109107 : Blo 1108626 1109107 := bstep (se 1 (by rfl) ⟨831830, by rfl⟩ : syracuseStep 1109107 = 1663661) B1663661
theorem B1666163 : Blo 1108626 1666163 := bstep (se 1 (by rfl) ⟨1249622, by rfl⟩ : syracuseStep 1666163 = 2499245) B2499245
theorem B1109123 : Blo 1108626 1109123 := bstep (se 1 (by rfl) ⟨831842, by rfl⟩ : syracuseStep 1109123 = 1663685) B1663685
theorem B1666193 : Blo 1108626 1666193 := bstep (se 2 (by rfl) ⟨624822, by rfl⟩ : syracuseStep 1666193 = 1249645) B1249645
theorem B1109139 : Blo 1108626 1109139 := bstep (se 1 (by rfl) ⟨831854, by rfl⟩ : syracuseStep 1109139 = 1663709) B1663709
theorem B1109155 : Blo 1108626 1109155 := bstep (se 1 (by rfl) ⟨831866, by rfl⟩ : syracuseStep 1109155 = 1663733) B1663733
theorem B1666211 : Blo 1108626 1666211 := bstep (se 1 (by rfl) ⟨1249658, by rfl⟩ : syracuseStep 1666211 = 2499317) B2499317
theorem B1109171 : Blo 1108626 1109171 := bstep (se 1 (by rfl) ⟨831878, by rfl⟩ : syracuseStep 1109171 = 1663757) B1663757
theorem B1666241 : Blo 1108626 1666241 := bstep (se 2 (by rfl) ⟨624840, by rfl⟩ : syracuseStep 1666241 = 1249681) B1249681
theorem B1109187 : Blo 1108626 1109187 := bstep (se 1 (by rfl) ⟨831890, by rfl⟩ : syracuseStep 1109187 = 1663781) B1663781
theorem B1109203 : Blo 1108626 1109203 := bstep (se 1 (by rfl) ⟨831902, by rfl⟩ : syracuseStep 1109203 = 1663805) B1663805
theorem B1666259 : Blo 1108626 1666259 := bstep (se 1 (by rfl) ⟨1249694, by rfl⟩ : syracuseStep 1666259 = 2499389) B2499389
theorem B1109219 : Blo 1108626 1109219 := bstep (se 1 (by rfl) ⟨831914, by rfl⟩ : syracuseStep 1109219 = 1663829) B1663829
theorem B1666289 : Blo 1108626 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B1109235 : Blo 1108626 1109235 := bstep (se 1 (by rfl) ⟨831926, by rfl⟩ : syracuseStep 1109235 = 1663853) B1663853
theorem B1109251 : Blo 1108626 1109251 := bstep (se 1 (by rfl) ⟨831938, by rfl⟩ : syracuseStep 1109251 = 1663877) B1663877
theorem B1666307 : Blo 1108626 1666307 := bstep (se 1 (by rfl) ⟨1249730, by rfl⟩ : syracuseStep 1666307 = 2499461) B2499461
theorem B4746509 : Blo 1108626 4746509 := bstep (se 3 (by rfl) ⟨889970, by rfl⟩ : syracuseStep 4746509 = 1779941) B1779941
theorem B2813201 : Blo 1108626 2813201 := bstep (se 2 (by rfl) ⟨1054950, by rfl⟩ : syracuseStep 2813201 = 2109901) B2109901
theorem B1109267 : Blo 1108626 1109267 := bstep (se 1 (by rfl) ⟨831950, by rfl⟩ : syracuseStep 1109267 = 1663901) B1663901
theorem B1666337 : Blo 1108626 1666337 := bstep (se 2 (by rfl) ⟨624876, by rfl⟩ : syracuseStep 1666337 = 1249753) B1249753
theorem B1109283 : Blo 1108626 1109283 := bstep (se 1 (by rfl) ⟨831962, by rfl⟩ : syracuseStep 1109283 = 1663925) B1663925
theorem B5631281 : Blo 1108626 5631281 := bstep (se 2 (by rfl) ⟨2111730, by rfl⟩ : syracuseStep 5631281 = 4223461) B4223461
theorem B1109299 : Blo 1108626 1109299 := bstep (se 1 (by rfl) ⟨831974, by rfl⟩ : syracuseStep 1109299 = 1663949) B1663949
theorem B1404211 : Blo 1108626 1404211 := bstep (se 1 (by rfl) ⟨1053158, by rfl⟩ : syracuseStep 1404211 = 2106317) B2106317
theorem B1666355 : Blo 1108626 1666355 := bstep (se 1 (by rfl) ⟨1249766, by rfl⟩ : syracuseStep 1666355 = 2499533) B2499533
theorem B1109315 : Blo 1108626 1109315 := bstep (se 1 (by rfl) ⟨831986, by rfl⟩ : syracuseStep 1109315 = 1663973) B1663973
theorem B2813251 : Blo 1108626 2813251 := bstep (se 1 (by rfl) ⟨2109938, by rfl⟩ : syracuseStep 2813251 = 4219877) B4219877
theorem B1666385 : Blo 1108626 1666385 := bstep (se 2 (by rfl) ⟨624894, by rfl⟩ : syracuseStep 1666385 = 1249789) B1249789
theorem B1109331 : Blo 1108626 1109331 := bstep (se 1 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 1109331 = 1663997) B1663997
theorem B1109347 : Blo 1108626 1109347 := bstep (se 1 (by rfl) ⟨832010, by rfl⟩ : syracuseStep 1109347 = 1664021) B1664021
theorem B1666403 : Blo 1108626 1666403 := bstep (se 1 (by rfl) ⟨1249802, by rfl⟩ : syracuseStep 1666403 = 2499605) B2499605
theorem B4222307 : Blo 1108626 4222307 := bstep (se 1 (by rfl) ⟨3166730, by rfl⟩ : syracuseStep 4222307 = 6333461) B6333461
theorem B1109363 : Blo 1108626 1109363 := bstep (se 1 (by rfl) ⟨832022, by rfl⟩ : syracuseStep 1109363 = 1664045) B1664045
theorem B1666433 : Blo 1108626 1666433 := bstep (se 2 (by rfl) ⟨624912, by rfl⟩ : syracuseStep 1666433 = 1249825) B1249825
theorem B1109379 : Blo 1108626 1109379 := bstep (se 1 (by rfl) ⟨832034, by rfl⟩ : syracuseStep 1109379 = 1664069) B1664069
theorem B1109395 : Blo 1108626 1109395 := bstep (se 1 (by rfl) ⟨832046, by rfl⟩ : syracuseStep 1109395 = 1664093) B1664093
theorem B1404307 : Blo 1108626 1404307 := bstep (se 1 (by rfl) ⟨1053230, by rfl⟩ : syracuseStep 1404307 = 2106461) B2106461
theorem B1666451 : Blo 1108626 1666451 := bstep (se 1 (by rfl) ⟨1249838, by rfl⟩ : syracuseStep 1666451 = 2499677) B2499677
theorem B1109411 : Blo 1108626 1109411 := bstep (se 1 (by rfl) ⟨832058, by rfl⟩ : syracuseStep 1109411 = 1664117) B1664117
theorem B1666481 : Blo 1108626 1666481 := bstep (se 2 (by rfl) ⟨624930, by rfl⟩ : syracuseStep 1666481 = 1249861) B1249861
theorem B1109427 : Blo 1108626 1109427 := bstep (se 1 (by rfl) ⟨832070, by rfl⟩ : syracuseStep 1109427 = 1664141) B1664141
theorem B1109443 : Blo 1108626 1109443 := bstep (se 1 (by rfl) ⟨832082, by rfl⟩ : syracuseStep 1109443 = 1664165) B1664165
theorem B1666499 : Blo 1108626 1666499 := bstep (se 1 (by rfl) ⟨1249874, by rfl⟩ : syracuseStep 1666499 = 2499749) B2499749
theorem B6319565 : Blo 1108626 6319565 := bstep (se 3 (by rfl) ⟨1184918, by rfl⟩ : syracuseStep 6319565 = 2369837) B2369837
theorem B2813393 : Blo 1108626 2813393 := bstep (se 2 (by rfl) ⟨1055022, by rfl⟩ : syracuseStep 2813393 = 2110045) B2110045
theorem B1109459 : Blo 1108626 1109459 := bstep (se 1 (by rfl) ⟨832094, by rfl⟩ : syracuseStep 1109459 = 1664189) B1664189
theorem B1666529 : Blo 1108626 1666529 := bstep (se 2 (by rfl) ⟨624948, by rfl⟩ : syracuseStep 1666529 = 1249897) B1249897
theorem B1109475 : Blo 1108626 1109475 := bstep (se 1 (by rfl) ⟨832106, by rfl⟩ : syracuseStep 1109475 = 1664213) B1664213
theorem B1109491 : Blo 1108626 1109491 := bstep (se 1 (by rfl) ⟨832118, by rfl⟩ : syracuseStep 1109491 = 1664237) B1664237
theorem B1666547 : Blo 1108626 1666547 := bstep (se 1 (by rfl) ⟨1249910, by rfl⟩ : syracuseStep 1666547 = 2499821) B2499821
theorem B1109507 : Blo 1108626 1109507 := bstep (se 1 (by rfl) ⟨832130, by rfl⟩ : syracuseStep 1109507 = 1664261) B1664261
theorem B1666577 : Blo 1108626 1666577 := bstep (se 2 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 1666577 = 1249933) B1249933
theorem B1109523 : Blo 1108626 1109523 := bstep (se 1 (by rfl) ⟨832142, by rfl⟩ : syracuseStep 1109523 = 1664285) B1664285
theorem B1109539 : Blo 1108626 1109539 := bstep (se 1 (by rfl) ⟨832154, by rfl⟩ : syracuseStep 1109539 = 1664309) B1664309
theorem B1666595 : Blo 1108626 1666595 := bstep (se 1 (by rfl) ⟨1249946, by rfl⟩ : syracuseStep 1666595 = 2499893) B2499893
theorem B1109555 : Blo 1108626 1109555 := bstep (se 1 (by rfl) ⟨832166, by rfl⟩ : syracuseStep 1109555 = 1664333) B1664333
theorem B1666625 : Blo 1108626 1666625 := bstep (se 2 (by rfl) ⟨624984, by rfl⟩ : syracuseStep 1666625 = 1249969) B1249969
theorem B1109571 : Blo 1108626 1109571 := bstep (se 1 (by rfl) ⟨832178, by rfl⟩ : syracuseStep 1109571 = 1664357) B1664357
theorem B6090317 : Blo 1108626 6090317 := bstep (se 3 (by rfl) ⟨1141934, by rfl⟩ : syracuseStep 6090317 = 2283869) B2283869
theorem B1109587 : Blo 1108626 1109587 := bstep (se 1 (by rfl) ⟨832190, by rfl⟩ : syracuseStep 1109587 = 1664381) B1664381
theorem B1666643 : Blo 1108626 1666643 := bstep (se 1 (by rfl) ⟨1249982, by rfl⟩ : syracuseStep 1666643 = 2499965) B2499965
theorem B1109603 : Blo 1108626 1109603 := bstep (se 1 (by rfl) ⟨832202, by rfl⟩ : syracuseStep 1109603 = 1664405) B1664405
theorem B1666673 : Blo 1108626 1666673 := bstep (se 2 (by rfl) ⟨625002, by rfl⟩ : syracuseStep 1666673 = 1250005) B1250005
theorem B1109619 : Blo 1108626 1109619 := bstep (se 1 (by rfl) ⟨832214, by rfl⟩ : syracuseStep 1109619 = 1664429) B1664429
theorem B1109635 : Blo 1108626 1109635 := bstep (se 1 (by rfl) ⟨832226, by rfl⟩ : syracuseStep 1109635 = 1664453) B1664453
theorem B1666691 : Blo 1108626 1666691 := bstep (se 1 (by rfl) ⟨1250018, by rfl⟩ : syracuseStep 1666691 = 2500037) B2500037
theorem B1109651 : Blo 1108626 1109651 := bstep (se 1 (by rfl) ⟨832238, by rfl⟩ : syracuseStep 1109651 = 1664477) B1664477
theorem B1666721 : Blo 1108626 1666721 := bstep (se 2 (by rfl) ⟨625020, by rfl⟩ : syracuseStep 1666721 = 1250041) B1250041
theorem B1109667 : Blo 1108626 1109667 := bstep (se 1 (by rfl) ⟨832250, by rfl⟩ : syracuseStep 1109667 = 1664501) B1664501
theorem B1109683 : Blo 1108626 1109683 := bstep (se 1 (by rfl) ⟨832262, by rfl⟩ : syracuseStep 1109683 = 1664525) B1664525
theorem B1666739 : Blo 1108626 1666739 := bstep (se 1 (by rfl) ⟨1250054, by rfl⟩ : syracuseStep 1666739 = 2500109) B2500109
theorem B1109699 : Blo 1108626 1109699 := bstep (se 1 (by rfl) ⟨832274, by rfl⟩ : syracuseStep 1109699 = 1664549) B1664549
theorem B1830595 : Blo 1108626 1830595 := bstep (se 1 (by rfl) ⟨1372946, by rfl⟩ : syracuseStep 1830595 = 2745893) B2745893
theorem B1666769 : Blo 1108626 1666769 := bstep (se 2 (by rfl) ⟨625038, by rfl⟩ : syracuseStep 1666769 = 1250077) B1250077
theorem B1109715 : Blo 1108626 1109715 := bstep (se 1 (by rfl) ⟨832286, by rfl⟩ : syracuseStep 1109715 = 1664573) B1664573
theorem B1109731 : Blo 1108626 1109731 := bstep (se 1 (by rfl) ⟨832298, by rfl⟩ : syracuseStep 1109731 = 1664597) B1664597
theorem B1666787 : Blo 1108626 1666787 := bstep (se 1 (by rfl) ⟨1250090, by rfl⟩ : syracuseStep 1666787 = 2500181) B2500181
theorem B6942449 : Blo 1108626 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B1109747 : Blo 1108626 1109747 := bstep (se 1 (by rfl) ⟨832310, by rfl⟩ : syracuseStep 1109747 = 1664621) B1664621
theorem B1666817 : Blo 1108626 1666817 := bstep (se 2 (by rfl) ⟨625056, by rfl⟩ : syracuseStep 1666817 = 1250113) B1250113
theorem B1109763 : Blo 1108626 1109763 := bstep (se 1 (by rfl) ⟨832322, by rfl⟩ : syracuseStep 1109763 = 1664645) B1664645
theorem B1109779 : Blo 1108626 1109779 := bstep (se 1 (by rfl) ⟨832334, by rfl⟩ : syracuseStep 1109779 = 1664669) B1664669
theorem B1666835 : Blo 1108626 1666835 := bstep (se 1 (by rfl) ⟨1250126, by rfl⟩ : syracuseStep 1666835 = 2500253) B2500253
theorem B1109795 : Blo 1108626 1109795 := bstep (se 1 (by rfl) ⟨832346, by rfl⟩ : syracuseStep 1109795 = 1664693) B1664693
theorem B1666865 : Blo 1108626 1666865 := bstep (se 2 (by rfl) ⟨625074, by rfl⟩ : syracuseStep 1666865 = 1250149) B1250149
theorem B1109811 : Blo 1108626 1109811 := bstep (se 1 (by rfl) ⟨832358, by rfl⟩ : syracuseStep 1109811 = 1664717) B1664717
theorem B1109827 : Blo 1108626 1109827 := bstep (se 1 (by rfl) ⟨832370, by rfl⟩ : syracuseStep 1109827 = 1664741) B1664741
theorem B1666883 : Blo 1108626 1666883 := bstep (se 1 (by rfl) ⟨1250162, by rfl⟩ : syracuseStep 1666883 = 2500325) B2500325
theorem B7597901 : Blo 1108626 7597901 := bstep (se 3 (by rfl) ⟨1424606, by rfl⟩ : syracuseStep 7597901 = 2849213) B2849213
theorem B1109843 : Blo 1108626 1109843 := bstep (se 1 (by rfl) ⟨832382, by rfl⟩ : syracuseStep 1109843 = 1664765) B1664765
theorem B1666913 : Blo 1108626 1666913 := bstep (se 2 (by rfl) ⟨625092, by rfl⟩ : syracuseStep 1666913 = 1250185) B1250185
theorem B1109859 : Blo 1108626 1109859 := bstep (se 1 (by rfl) ⟨832394, by rfl⟩ : syracuseStep 1109859 = 1664789) B1664789
theorem B1109875 : Blo 1108626 1109875 := bstep (se 1 (by rfl) ⟨832406, by rfl⟩ : syracuseStep 1109875 = 1664813) B1664813
theorem B1666931 : Blo 1108626 1666931 := bstep (se 1 (by rfl) ⟨1250198, by rfl⟩ : syracuseStep 1666931 = 2500397) B2500397
theorem B1109891 : Blo 1108626 1109891 := bstep (se 1 (by rfl) ⟨832418, by rfl⟩ : syracuseStep 1109891 = 1664837) B1664837
theorem B1404803 : Blo 1108626 1404803 := bstep (se 1 (by rfl) ⟨1053602, by rfl⟩ : syracuseStep 1404803 = 2107205) B2107205
theorem B56323981 : Blo 1108626 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B1666961 : Blo 1108626 1666961 := bstep (se 2 (by rfl) ⟨625110, by rfl⟩ : syracuseStep 1666961 = 1250221) B1250221
theorem B1109907 : Blo 1108626 1109907 := bstep (se 1 (by rfl) ⟨832430, by rfl⟩ : syracuseStep 1109907 = 1664861) B1664861
theorem B1109923 : Blo 1108626 1109923 := bstep (se 1 (by rfl) ⟨832442, by rfl⟩ : syracuseStep 1109923 = 1664885) B1664885
theorem B1666979 : Blo 1108626 1666979 := bstep (se 1 (by rfl) ⟨1250234, by rfl⟩ : syracuseStep 1666979 = 2500469) B2500469
theorem B1109939 : Blo 1108626 1109939 := bstep (se 1 (by rfl) ⟨832454, by rfl⟩ : syracuseStep 1109939 = 1664909) B1664909
theorem B1503155 : Blo 1108626 1503155 := bstep (se 1 (by rfl) ⟨1127366, by rfl⟩ : syracuseStep 1503155 = 2254733) B2254733
theorem B1667009 : Blo 1108626 1667009 := bstep (se 2 (by rfl) ⟨625128, by rfl⟩ : syracuseStep 1667009 = 1250257) B1250257
theorem B1109955 : Blo 1108626 1109955 := bstep (se 1 (by rfl) ⟨832466, by rfl⟩ : syracuseStep 1109955 = 1664933) B1664933
theorem B1109971 : Blo 1108626 1109971 := bstep (se 1 (by rfl) ⟨832478, by rfl⟩ : syracuseStep 1109971 = 1664957) B1664957
theorem B1667027 : Blo 1108626 1667027 := bstep (se 1 (by rfl) ⟨1250270, by rfl⟩ : syracuseStep 1667027 = 2500541) B2500541
theorem B1109987 : Blo 1108626 1109987 := bstep (se 1 (by rfl) ⟨832490, by rfl⟩ : syracuseStep 1109987 = 1664981) B1664981
theorem B1667057 : Blo 1108626 1667057 := bstep (se 2 (by rfl) ⟨625146, by rfl⟩ : syracuseStep 1667057 = 1250293) B1250293
theorem B4222961 : Blo 1108626 4222961 := bstep (se 2 (by rfl) ⟨1583610, by rfl⟩ : syracuseStep 4222961 = 3167221) B3167221
theorem B1110003 : Blo 1108626 1110003 := bstep (se 1 (by rfl) ⟨832502, by rfl⟩ : syracuseStep 1110003 = 1665005) B1665005
theorem B1110019 : Blo 1108626 1110019 := bstep (se 1 (by rfl) ⟨832514, by rfl⟩ : syracuseStep 1110019 = 1665029) B1665029
theorem B1667075 : Blo 1108626 1667075 := bstep (se 1 (by rfl) ⟨1250306, by rfl⟩ : syracuseStep 1667075 = 2500613) B2500613
theorem B1110035 : Blo 1108626 1110035 := bstep (se 1 (by rfl) ⟨832526, by rfl⟩ : syracuseStep 1110035 = 1665053) B1665053
theorem B1667105 : Blo 1108626 1667105 := bstep (se 2 (by rfl) ⟨625164, by rfl⟩ : syracuseStep 1667105 = 1250329) B1250329
theorem B1110051 : Blo 1108626 1110051 := bstep (se 1 (by rfl) ⟨832538, by rfl⟩ : syracuseStep 1110051 = 1665077) B1665077
theorem B1110067 : Blo 1108626 1110067 := bstep (se 1 (by rfl) ⟨832550, by rfl⟩ : syracuseStep 1110067 = 1665101) B1665101
theorem B1667123 : Blo 1108626 1667123 := bstep (se 1 (by rfl) ⟨1250342, by rfl⟩ : syracuseStep 1667123 = 2500685) B2500685
theorem B1110083 : Blo 1108626 1110083 := bstep (se 1 (by rfl) ⟨832562, by rfl⟩ : syracuseStep 1110083 = 1665125) B1665125
theorem B1667153 : Blo 1108626 1667153 := bstep (se 2 (by rfl) ⟨625182, by rfl⟩ : syracuseStep 1667153 = 1250365) B1250365
theorem B1110099 : Blo 1108626 1110099 := bstep (se 1 (by rfl) ⟨832574, by rfl⟩ : syracuseStep 1110099 = 1665149) B1665149
theorem B1110115 : Blo 1108626 1110115 := bstep (se 1 (by rfl) ⟨832586, by rfl⟩ : syracuseStep 1110115 = 1665173) B1665173
theorem B1667171 : Blo 1108626 1667171 := bstep (se 1 (by rfl) ⟨1250378, by rfl⟩ : syracuseStep 1667171 = 2500757) B2500757
theorem B1110131 : Blo 1108626 1110131 := bstep (se 1 (by rfl) ⟨832598, by rfl⟩ : syracuseStep 1110131 = 1665197) B1665197
theorem B1667201 : Blo 1108626 1667201 := bstep (se 2 (by rfl) ⟨625200, by rfl⟩ : syracuseStep 1667201 = 1250401) B1250401
theorem B1110147 : Blo 1108626 1110147 := bstep (se 1 (by rfl) ⟨832610, by rfl⟩ : syracuseStep 1110147 = 1665221) B1665221
theorem B3043469 : Blo 1108626 3043469 := bstep (se 3 (by rfl) ⟨570650, by rfl⟩ : syracuseStep 3043469 = 1141301) B1141301
theorem B1110163 : Blo 1108626 1110163 := bstep (se 1 (by rfl) ⟨832622, by rfl⟩ : syracuseStep 1110163 = 1665245) B1665245
theorem B1667219 : Blo 1108626 1667219 := bstep (se 1 (by rfl) ⟨1250414, by rfl⟩ : syracuseStep 1667219 = 2500829) B2500829
theorem B1110179 : Blo 1108626 1110179 := bstep (se 1 (by rfl) ⟨832634, by rfl⟩ : syracuseStep 1110179 = 1665269) B1665269
theorem B1667249 : Blo 1108626 1667249 := bstep (se 2 (by rfl) ⟨625218, by rfl⟩ : syracuseStep 1667249 = 1250437) B1250437
theorem B1110195 : Blo 1108626 1110195 := bstep (se 1 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 1110195 = 1665293) B1665293
theorem B1110211 : Blo 1108626 1110211 := bstep (se 1 (by rfl) ⟨832658, by rfl⟩ : syracuseStep 1110211 = 1665317) B1665317
theorem B1667267 : Blo 1108626 1667267 := bstep (se 1 (by rfl) ⟨1250450, by rfl⟩ : syracuseStep 1667267 = 2500901) B2500901
theorem B1110227 : Blo 1108626 1110227 := bstep (se 1 (by rfl) ⟨832670, by rfl⟩ : syracuseStep 1110227 = 1665341) B1665341
theorem B1667297 : Blo 1108626 1667297 := bstep (se 2 (by rfl) ⟨625236, by rfl⟩ : syracuseStep 1667297 = 1250473) B1250473
theorem B1110243 : Blo 1108626 1110243 := bstep (se 1 (by rfl) ⟨832682, by rfl⟩ : syracuseStep 1110243 = 1665365) B1665365
theorem B4878563 : Blo 1108626 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B1110259 : Blo 1108626 1110259 := bstep (se 1 (by rfl) ⟨832694, by rfl⟩ : syracuseStep 1110259 = 1665389) B1665389
theorem B1667315 : Blo 1108626 1667315 := bstep (se 1 (by rfl) ⟨1250486, by rfl⟩ : syracuseStep 1667315 = 2500973) B2500973
theorem B1110275 : Blo 1108626 1110275 := bstep (se 1 (by rfl) ⟨832706, by rfl⟩ : syracuseStep 1110275 = 1665413) B1665413
theorem B1667345 : Blo 1108626 1667345 := bstep (se 2 (by rfl) ⟨625254, by rfl⟩ : syracuseStep 1667345 = 1250509) B1250509
theorem B1110291 : Blo 1108626 1110291 := bstep (se 1 (by rfl) ⟨832718, by rfl⟩ : syracuseStep 1110291 = 1665437) B1665437
theorem B1110307 : Blo 1108626 1110307 := bstep (se 1 (by rfl) ⟨832730, by rfl⟩ : syracuseStep 1110307 = 1665461) B1665461
theorem B1667363 : Blo 1108626 1667363 := bstep (se 1 (by rfl) ⟨1250522, by rfl⟩ : syracuseStep 1667363 = 2501045) B2501045
theorem B1110323 : Blo 1108626 1110323 := bstep (se 1 (by rfl) ⟨832742, by rfl⟩ : syracuseStep 1110323 = 1665485) B1665485
theorem B1667393 : Blo 1108626 1667393 := bstep (se 2 (by rfl) ⟨625272, by rfl⟩ : syracuseStep 1667393 = 1250545) B1250545
theorem B1110339 : Blo 1108626 1110339 := bstep (se 1 (by rfl) ⟨832754, by rfl⟩ : syracuseStep 1110339 = 1665509) B1665509
theorem B1110355 : Blo 1108626 1110355 := bstep (se 1 (by rfl) ⟨832766, by rfl⟩ : syracuseStep 1110355 = 1665533) B1665533
theorem B1667411 : Blo 1108626 1667411 := bstep (se 1 (by rfl) ⟨1250558, by rfl⟩ : syracuseStep 1667411 = 2501117) B2501117
theorem B1110371 : Blo 1108626 1110371 := bstep (se 1 (by rfl) ⟨832778, by rfl⟩ : syracuseStep 1110371 = 1665557) B1665557
theorem B1667441 : Blo 1108626 1667441 := bstep (se 2 (by rfl) ⟨625290, by rfl⟩ : syracuseStep 1667441 = 1250581) B1250581
theorem B1110387 : Blo 1108626 1110387 := bstep (se 1 (by rfl) ⟨832790, by rfl⟩ : syracuseStep 1110387 = 1665581) B1665581
theorem B3371395 : Blo 1108626 3371395 := bstep (se 1 (by rfl) ⟨2528546, by rfl⟩ : syracuseStep 3371395 = 5057093) B5057093
theorem B1110403 : Blo 1108626 1110403 := bstep (se 1 (by rfl) ⟨832802, by rfl⟩ : syracuseStep 1110403 = 1665605) B1665605
theorem B1667459 : Blo 1108626 1667459 := bstep (se 1 (by rfl) ⟨1250594, by rfl⟩ : syracuseStep 1667459 = 2501189) B2501189
theorem B1110419 : Blo 1108626 1110419 := bstep (se 1 (by rfl) ⟨832814, by rfl⟩ : syracuseStep 1110419 = 1665629) B1665629
theorem B1667489 : Blo 1108626 1667489 := bstep (se 2 (by rfl) ⟨625308, by rfl⟩ : syracuseStep 1667489 = 1250617) B1250617
theorem B1110435 : Blo 1108626 1110435 := bstep (se 1 (by rfl) ⟨832826, by rfl⟩ : syracuseStep 1110435 = 1665653) B1665653
theorem B2814385 : Blo 1108626 2814385 := bstep (se 2 (by rfl) ⟨1055394, by rfl⟩ : syracuseStep 2814385 = 2110789) B2110789
theorem B1110451 : Blo 1108626 1110451 := bstep (se 1 (by rfl) ⟨832838, by rfl⟩ : syracuseStep 1110451 = 1665677) B1665677
theorem B1667507 : Blo 1108626 1667507 := bstep (se 1 (by rfl) ⟨1250630, by rfl⟩ : syracuseStep 1667507 = 2501261) B2501261
theorem B1110467 : Blo 1108626 1110467 := bstep (se 1 (by rfl) ⟨832850, by rfl⟩ : syracuseStep 1110467 = 1665701) B1665701
theorem B1667537 : Blo 1108626 1667537 := bstep (se 2 (by rfl) ⟨625326, by rfl⟩ : syracuseStep 1667537 = 1250653) B1250653
theorem B1110483 : Blo 1108626 1110483 := bstep (se 1 (by rfl) ⟨832862, by rfl⟩ : syracuseStep 1110483 = 1665725) B1665725
theorem B1110499 : Blo 1108626 1110499 := bstep (se 1 (by rfl) ⟨832874, by rfl⟩ : syracuseStep 1110499 = 1665749) B1665749
theorem B1667555 : Blo 1108626 1667555 := bstep (se 1 (by rfl) ⟨1250666, by rfl⟩ : syracuseStep 1667555 = 2501333) B2501333
theorem B1110515 : Blo 1108626 1110515 := bstep (se 1 (by rfl) ⟨832886, by rfl⟩ : syracuseStep 1110515 = 1665773) B1665773
theorem B1667585 : Blo 1108626 1667585 := bstep (se 2 (by rfl) ⟨625344, by rfl⟩ : syracuseStep 1667585 = 1250689) B1250689
theorem B1110531 : Blo 1108626 1110531 := bstep (se 1 (by rfl) ⟨832898, by rfl⟩ : syracuseStep 1110531 = 1665797) B1665797
theorem B1110547 : Blo 1108626 1110547 := bstep (se 1 (by rfl) ⟨832910, by rfl⟩ : syracuseStep 1110547 = 1665821) B1665821
theorem B1667603 : Blo 1108626 1667603 := bstep (se 1 (by rfl) ⟨1250702, by rfl⟩ : syracuseStep 1667603 = 2501405) B2501405
theorem B1110563 : Blo 1108626 1110563 := bstep (se 1 (by rfl) ⟨832922, by rfl⟩ : syracuseStep 1110563 = 1665845) B1665845
theorem B1667633 : Blo 1108626 1667633 := bstep (se 2 (by rfl) ⟨625362, by rfl⟩ : syracuseStep 1667633 = 1250725) B1250725
theorem B1110579 : Blo 1108626 1110579 := bstep (se 1 (by rfl) ⟨832934, by rfl⟩ : syracuseStep 1110579 = 1665869) B1665869
theorem B1405507 : Blo 1108626 1405507 := bstep (se 1 (by rfl) ⟨1054130, by rfl⟩ : syracuseStep 1405507 = 2108261) B2108261
theorem B1110595 : Blo 1108626 1110595 := bstep (se 1 (by rfl) ⟨832946, by rfl⟩ : syracuseStep 1110595 = 1665893) B1665893
theorem B1667651 : Blo 1108626 1667651 := bstep (se 1 (by rfl) ⟨1250738, by rfl⟩ : syracuseStep 1667651 = 2501477) B2501477
theorem B1110611 : Blo 1108626 1110611 := bstep (se 1 (by rfl) ⟨832958, by rfl⟩ : syracuseStep 1110611 = 1665917) B1665917
theorem B1667681 : Blo 1108626 1667681 := bstep (se 2 (by rfl) ⟨625380, by rfl⟩ : syracuseStep 1667681 = 1250761) B1250761
theorem B1110627 : Blo 1108626 1110627 := bstep (se 1 (by rfl) ⟨832970, by rfl⟩ : syracuseStep 1110627 = 1665941) B1665941
theorem B1110643 : Blo 1108626 1110643 := bstep (se 1 (by rfl) ⟨832982, by rfl⟩ : syracuseStep 1110643 = 1665965) B1665965
theorem B1667699 : Blo 1108626 1667699 := bstep (se 1 (by rfl) ⟨1250774, by rfl⟩ : syracuseStep 1667699 = 2501549) B2501549
theorem B1110659 : Blo 1108626 1110659 := bstep (se 1 (by rfl) ⟨832994, by rfl⟩ : syracuseStep 1110659 = 1665989) B1665989
theorem B1667729 : Blo 1108626 1667729 := bstep (se 2 (by rfl) ⟨625398, by rfl⟩ : syracuseStep 1667729 = 1250797) B1250797
theorem B1110675 : Blo 1108626 1110675 := bstep (se 1 (by rfl) ⟨833006, by rfl⟩ : syracuseStep 1110675 = 1666013) B1666013
theorem B1667747 : Blo 1108626 1667747 := bstep (se 1 (by rfl) ⟨1250810, by rfl⟩ : syracuseStep 1667747 = 2501621) B2501621
theorem B1405603 : Blo 1108626 1405603 := bstep (se 1 (by rfl) ⟨1054202, by rfl⟩ : syracuseStep 1405603 = 2108405) B2108405
theorem B1110691 : Blo 1108626 1110691 := bstep (se 1 (by rfl) ⟨833018, by rfl⟩ : syracuseStep 1110691 = 1666037) B1666037
theorem B1110707 : Blo 1108626 1110707 := bstep (se 1 (by rfl) ⟨833030, by rfl⟩ : syracuseStep 1110707 = 1666061) B1666061
theorem B1667777 : Blo 1108626 1667777 := bstep (se 2 (by rfl) ⟨625416, by rfl⟩ : syracuseStep 1667777 = 1250833) B1250833
theorem B1110723 : Blo 1108626 1110723 := bstep (se 1 (by rfl) ⟨833042, by rfl⟩ : syracuseStep 1110723 = 1666085) B1666085
theorem B2814659 : Blo 1108626 2814659 := bstep (se 1 (by rfl) ⟨2110994, by rfl⟩ : syracuseStep 2814659 = 4221989) B4221989
theorem B1110739 : Blo 1108626 1110739 := bstep (se 1 (by rfl) ⟨833054, by rfl⟩ : syracuseStep 1110739 = 1666109) B1666109
theorem B1667795 : Blo 1108626 1667795 := bstep (se 1 (by rfl) ⟨1250846, by rfl⟩ : syracuseStep 1667795 = 2501693) B2501693
theorem B1110755 : Blo 1108626 1110755 := bstep (se 1 (by rfl) ⟨833066, by rfl⟩ : syracuseStep 1110755 = 1666133) B1666133
theorem B1667825 : Blo 1108626 1667825 := bstep (se 2 (by rfl) ⟨625434, by rfl⟩ : syracuseStep 1667825 = 1250869) B1250869
theorem B1110771 : Blo 1108626 1110771 := bstep (se 1 (by rfl) ⟨833078, by rfl⟩ : syracuseStep 1110771 = 1666157) B1666157
theorem B1110787 : Blo 1108626 1110787 := bstep (se 1 (by rfl) ⟨833090, by rfl⟩ : syracuseStep 1110787 = 1666181) B1666181
theorem B1667843 : Blo 1108626 1667843 := bstep (se 1 (by rfl) ⟨1250882, by rfl⟩ : syracuseStep 1667843 = 2501765) B2501765
theorem B1110803 : Blo 1108626 1110803 := bstep (se 1 (by rfl) ⟨833102, by rfl⟩ : syracuseStep 1110803 = 1666205) B1666205
theorem B1667873 : Blo 1108626 1667873 := bstep (se 2 (by rfl) ⟨625452, by rfl⟩ : syracuseStep 1667873 = 1250905) B1250905
theorem B1110819 : Blo 1108626 1110819 := bstep (se 1 (by rfl) ⟨833114, by rfl⟩ : syracuseStep 1110819 = 1666229) B1666229
theorem B1110835 : Blo 1108626 1110835 := bstep (se 1 (by rfl) ⟨833126, by rfl⟩ : syracuseStep 1110835 = 1666253) B1666253
theorem B1667891 : Blo 1108626 1667891 := bstep (se 1 (by rfl) ⟨1250918, by rfl⟩ : syracuseStep 1667891 = 2501837) B2501837
theorem B1110851 : Blo 1108626 1110851 := bstep (se 1 (by rfl) ⟨833138, by rfl⟩ : syracuseStep 1110851 = 1666277) B1666277
theorem B1667921 : Blo 1108626 1667921 := bstep (se 2 (by rfl) ⟨625470, by rfl⟩ : syracuseStep 1667921 = 1250941) B1250941
theorem B1110867 : Blo 1108626 1110867 := bstep (se 1 (by rfl) ⟨833150, by rfl⟩ : syracuseStep 1110867 = 1666301) B1666301
theorem B1110883 : Blo 1108626 1110883 := bstep (se 1 (by rfl) ⟨833162, by rfl⟩ : syracuseStep 1110883 = 1666325) B1666325
theorem B1667939 : Blo 1108626 1667939 := bstep (se 1 (by rfl) ⟨1250954, by rfl⟩ : syracuseStep 1667939 = 2501909) B2501909
theorem B12645233 : Blo 1108626 12645233 := bstep (se 2 (by rfl) ⟨4741962, by rfl⟩ : syracuseStep 12645233 = 9483925) B9483925
theorem B1110899 : Blo 1108626 1110899 := bstep (se 1 (by rfl) ⟨833174, by rfl⟩ : syracuseStep 1110899 = 1666349) B1666349
theorem B1667969 : Blo 1108626 1667969 := bstep (se 2 (by rfl) ⟨625488, by rfl⟩ : syracuseStep 1667969 = 1250977) B1250977
theorem B1110915 : Blo 1108626 1110915 := bstep (se 1 (by rfl) ⟨833186, by rfl⟩ : syracuseStep 1110915 = 1666373) B1666373
theorem B2814851 : Blo 1108626 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B1110931 : Blo 1108626 1110931 := bstep (se 1 (by rfl) ⟨833198, by rfl⟩ : syracuseStep 1110931 = 1666397) B1666397
theorem B1667987 : Blo 1108626 1667987 := bstep (se 1 (by rfl) ⟨1250990, by rfl⟩ : syracuseStep 1667987 = 2501981) B2501981
theorem B1110947 : Blo 1108626 1110947 := bstep (se 1 (by rfl) ⟨833210, by rfl⟩ : syracuseStep 1110947 = 1666421) B1666421
theorem B1668017 : Blo 1108626 1668017 := bstep (se 2 (by rfl) ⟨625506, by rfl⟩ : syracuseStep 1668017 = 1251013) B1251013
theorem B1110963 : Blo 1108626 1110963 := bstep (se 1 (by rfl) ⟨833222, by rfl⟩ : syracuseStep 1110963 = 1666445) B1666445
theorem B1110979 : Blo 1108626 1110979 := bstep (se 1 (by rfl) ⟨833234, by rfl⟩ : syracuseStep 1110979 = 1666469) B1666469
theorem B1668035 : Blo 1108626 1668035 := bstep (se 1 (by rfl) ⟨1251026, by rfl⟩ : syracuseStep 1668035 = 2502053) B2502053
theorem B1110995 : Blo 1108626 1110995 := bstep (se 1 (by rfl) ⟨833246, by rfl⟩ : syracuseStep 1110995 = 1666493) B1666493
theorem B1668065 : Blo 1108626 1668065 := bstep (se 2 (by rfl) ⟨625524, by rfl⟩ : syracuseStep 1668065 = 1251049) B1251049
theorem B1111011 : Blo 1108626 1111011 := bstep (se 1 (by rfl) ⟨833258, by rfl⟩ : syracuseStep 1111011 = 1666517) B1666517
theorem B1111027 : Blo 1108626 1111027 := bstep (se 1 (by rfl) ⟨833270, by rfl⟩ : syracuseStep 1111027 = 1666541) B1666541
theorem B1668083 : Blo 1108626 1668083 := bstep (se 1 (by rfl) ⟨1251062, by rfl⟩ : syracuseStep 1668083 = 2502125) B2502125
theorem B1111043 : Blo 1108626 1111043 := bstep (se 1 (by rfl) ⟨833282, by rfl⟩ : syracuseStep 1111043 = 1666565) B1666565
theorem B1668113 : Blo 1108626 1668113 := bstep (se 2 (by rfl) ⟨625542, by rfl⟩ : syracuseStep 1668113 = 1251085) B1251085
theorem B1111059 : Blo 1108626 1111059 := bstep (se 1 (by rfl) ⟨833294, by rfl⟩ : syracuseStep 1111059 = 1666589) B1666589
theorem B1111075 : Blo 1108626 1111075 := bstep (se 1 (by rfl) ⟨833306, by rfl⟩ : syracuseStep 1111075 = 1666613) B1666613
theorem B1668131 : Blo 1108626 1668131 := bstep (se 1 (by rfl) ⟨1251098, by rfl⟩ : syracuseStep 1668131 = 2502197) B2502197
theorem B1111091 : Blo 1108626 1111091 := bstep (se 1 (by rfl) ⟨833318, by rfl⟩ : syracuseStep 1111091 = 1666637) B1666637
theorem B1668161 : Blo 1108626 1668161 := bstep (se 2 (by rfl) ⟨625560, by rfl⟩ : syracuseStep 1668161 = 1251121) B1251121
theorem B1111107 : Blo 1108626 1111107 := bstep (se 1 (by rfl) ⟨833330, by rfl⟩ : syracuseStep 1111107 = 1666661) B1666661
theorem B1111123 : Blo 1108626 1111123 := bstep (se 1 (by rfl) ⟨833342, by rfl⟩ : syracuseStep 1111123 = 1666685) B1666685
theorem B1668179 : Blo 1108626 1668179 := bstep (se 1 (by rfl) ⟨1251134, by rfl⟩ : syracuseStep 1668179 = 2502269) B2502269
theorem B1111139 : Blo 1108626 1111139 := bstep (se 1 (by rfl) ⟨833354, by rfl⟩ : syracuseStep 1111139 = 1666709) B1666709
theorem B5698673 : Blo 1108626 5698673 := bstep (se 2 (by rfl) ⟨2137002, by rfl⟩ : syracuseStep 5698673 = 4274005) B4274005
theorem B1668209 : Blo 1108626 1668209 := bstep (se 2 (by rfl) ⟨625578, by rfl⟩ : syracuseStep 1668209 = 1251157) B1251157
theorem B1111155 : Blo 1108626 1111155 := bstep (se 1 (by rfl) ⟨833366, by rfl⟩ : syracuseStep 1111155 = 1666733) B1666733
theorem B1111171 : Blo 1108626 1111171 := bstep (se 1 (by rfl) ⟨833378, by rfl⟩ : syracuseStep 1111171 = 1666757) B1666757
theorem B1668227 : Blo 1108626 1668227 := bstep (se 1 (by rfl) ⟨1251170, by rfl⟩ : syracuseStep 1668227 = 2502341) B2502341
theorem B1406099 : Blo 1108626 1406099 := bstep (se 1 (by rfl) ⟨1054574, by rfl⟩ : syracuseStep 1406099 = 2109149) B2109149
theorem B1111187 : Blo 1108626 1111187 := bstep (se 1 (by rfl) ⟨833390, by rfl⟩ : syracuseStep 1111187 = 1666781) B1666781
theorem B1668257 : Blo 1108626 1668257 := bstep (se 2 (by rfl) ⟨625596, by rfl⟩ : syracuseStep 1668257 = 1251193) B1251193
theorem B1111203 : Blo 1108626 1111203 := bstep (se 1 (by rfl) ⟨833402, by rfl⟩ : syracuseStep 1111203 = 1666805) B1666805
theorem B1111219 : Blo 1108626 1111219 := bstep (se 1 (by rfl) ⟨833414, by rfl⟩ : syracuseStep 1111219 = 1666829) B1666829
theorem B1668275 : Blo 1108626 1668275 := bstep (se 1 (by rfl) ⟨1251206, by rfl⟩ : syracuseStep 1668275 = 2502413) B2502413
theorem B1111235 : Blo 1108626 1111235 := bstep (se 1 (by rfl) ⟨833426, by rfl⟩ : syracuseStep 1111235 = 1666853) B1666853
theorem B1668305 : Blo 1108626 1668305 := bstep (se 2 (by rfl) ⟨625614, by rfl⟩ : syracuseStep 1668305 = 1251229) B1251229
theorem B1111251 : Blo 1108626 1111251 := bstep (se 1 (by rfl) ⟨833438, by rfl⟩ : syracuseStep 1111251 = 1666877) B1666877
theorem B1111267 : Blo 1108626 1111267 := bstep (se 1 (by rfl) ⟨833450, by rfl⟩ : syracuseStep 1111267 = 1666901) B1666901
theorem B1668323 : Blo 1108626 1668323 := bstep (se 1 (by rfl) ⟨1251242, by rfl⟩ : syracuseStep 1668323 = 2502485) B2502485
theorem B1111283 : Blo 1108626 1111283 := bstep (se 1 (by rfl) ⟨833462, by rfl⟩ : syracuseStep 1111283 = 1666925) B1666925
theorem B1668353 : Blo 1108626 1668353 := bstep (se 2 (by rfl) ⟨625632, by rfl⟩ : syracuseStep 1668353 = 1251265) B1251265
theorem B1111299 : Blo 1108626 1111299 := bstep (se 1 (by rfl) ⟨833474, by rfl⟩ : syracuseStep 1111299 = 1666949) B1666949
theorem B1111315 : Blo 1108626 1111315 := bstep (se 1 (by rfl) ⟨833486, by rfl⟩ : syracuseStep 1111315 = 1666973) B1666973
theorem B1668371 : Blo 1108626 1668371 := bstep (se 1 (by rfl) ⟨1251278, by rfl⟩ : syracuseStep 1668371 = 2502557) B2502557
theorem B1111331 : Blo 1108626 1111331 := bstep (se 1 (by rfl) ⟨833498, by rfl⟩ : syracuseStep 1111331 = 1666997) B1666997
theorem B1668401 : Blo 1108626 1668401 := bstep (se 2 (by rfl) ⟨625650, by rfl⟩ : syracuseStep 1668401 = 1251301) B1251301
theorem B1111347 : Blo 1108626 1111347 := bstep (se 1 (by rfl) ⟨833510, by rfl⟩ : syracuseStep 1111347 = 1667021) B1667021
theorem B1111363 : Blo 1108626 1111363 := bstep (se 1 (by rfl) ⟨833522, by rfl⟩ : syracuseStep 1111363 = 1667045) B1667045
theorem B1668419 : Blo 1108626 1668419 := bstep (se 1 (by rfl) ⟨1251314, by rfl⟩ : syracuseStep 1668419 = 2502629) B2502629
theorem B6747461 : Blo 1108626 6747461 := bstep (se 4 (by rfl) ⟨632574, by rfl⟩ : syracuseStep 6747461 = 1265149) B1265149
theorem B1111379 : Blo 1108626 1111379 := bstep (se 1 (by rfl) ⟨833534, by rfl⟩ : syracuseStep 1111379 = 1667069) B1667069
theorem B1668449 : Blo 1108626 1668449 := bstep (se 2 (by rfl) ⟨625668, by rfl⟩ : syracuseStep 1668449 = 1251337) B1251337
theorem B1111395 : Blo 1108626 1111395 := bstep (se 1 (by rfl) ⟨833546, by rfl⟩ : syracuseStep 1111395 = 1667093) B1667093
theorem B1111411 : Blo 1108626 1111411 := bstep (se 1 (by rfl) ⟨833558, by rfl⟩ : syracuseStep 1111411 = 1667117) B1667117
theorem B1668467 : Blo 1108626 1668467 := bstep (se 1 (by rfl) ⟨1251350, by rfl⟩ : syracuseStep 1668467 = 2502701) B2502701
theorem B1111427 : Blo 1108626 1111427 := bstep (se 1 (by rfl) ⟨833570, by rfl⟩ : syracuseStep 1111427 = 1667141) B1667141
theorem B1668497 : Blo 1108626 1668497 := bstep (se 2 (by rfl) ⟨625686, by rfl⟩ : syracuseStep 1668497 = 1251373) B1251373
theorem B1111443 : Blo 1108626 1111443 := bstep (se 1 (by rfl) ⟨833582, by rfl⟩ : syracuseStep 1111443 = 1667165) B1667165
theorem B1111459 : Blo 1108626 1111459 := bstep (se 1 (by rfl) ⟨833594, by rfl⟩ : syracuseStep 1111459 = 1667189) B1667189
theorem B1668515 : Blo 1108626 1668515 := bstep (se 1 (by rfl) ⟨1251386, by rfl⟩ : syracuseStep 1668515 = 2502773) B2502773
theorem B4224419 : Blo 1108626 4224419 := bstep (se 1 (by rfl) ⟨3168314, by rfl⟩ : syracuseStep 4224419 = 6336629) B6336629
theorem B4224433 : Blo 1108626 4224433 := bstep (se 2 (by rfl) ⟨1584162, by rfl⟩ : syracuseStep 4224433 = 3168325) B3168325
theorem B1111475 : Blo 1108626 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B1668545 : Blo 1108626 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B1111491 : Blo 1108626 1111491 := bstep (se 1 (by rfl) ⟨833618, by rfl⟩ : syracuseStep 1111491 = 1667237) B1667237
theorem B1111507 : Blo 1108626 1111507 := bstep (se 1 (by rfl) ⟨833630, by rfl⟩ : syracuseStep 1111507 = 1667261) B1667261
theorem B1668563 : Blo 1108626 1668563 := bstep (se 1 (by rfl) ⟨1251422, by rfl⟩ : syracuseStep 1668563 = 2502845) B2502845
theorem B1111523 : Blo 1108626 1111523 := bstep (se 1 (by rfl) ⟨833642, by rfl⟩ : syracuseStep 1111523 = 1667285) B1667285
theorem B1668593 : Blo 1108626 1668593 := bstep (se 2 (by rfl) ⟨625722, by rfl⟩ : syracuseStep 1668593 = 1251445) B1251445
theorem B1111539 : Blo 1108626 1111539 := bstep (se 1 (by rfl) ⟨833654, by rfl⟩ : syracuseStep 1111539 = 1667309) B1667309
theorem B1111555 : Blo 1108626 1111555 := bstep (se 1 (by rfl) ⟨833666, by rfl⟩ : syracuseStep 1111555 = 1667333) B1667333
theorem B1668611 : Blo 1108626 1668611 := bstep (se 1 (by rfl) ⟨1251458, by rfl⟩ : syracuseStep 1668611 = 2502917) B2502917
theorem B1111571 : Blo 1108626 1111571 := bstep (se 1 (by rfl) ⟨833678, by rfl⟩ : syracuseStep 1111571 = 1667357) B1667357
theorem B1668641 : Blo 1108626 1668641 := bstep (se 2 (by rfl) ⟨625740, by rfl⟩ : syracuseStep 1668641 = 1251481) B1251481
theorem B1111587 : Blo 1108626 1111587 := bstep (se 1 (by rfl) ⟨833690, by rfl⟩ : syracuseStep 1111587 = 1667381) B1667381
theorem B1111603 : Blo 1108626 1111603 := bstep (se 1 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 1111603 = 1667405) B1667405
theorem B1668659 : Blo 1108626 1668659 := bstep (se 1 (by rfl) ⟨1251494, by rfl⟩ : syracuseStep 1668659 = 2502989) B2502989
theorem B1111619 : Blo 1108626 1111619 := bstep (se 1 (by rfl) ⟨833714, by rfl⟩ : syracuseStep 1111619 = 1667429) B1667429
theorem B1668689 : Blo 1108626 1668689 := bstep (se 2 (by rfl) ⟨625758, by rfl⟩ : syracuseStep 1668689 = 1251517) B1251517
theorem B1111635 : Blo 1108626 1111635 := bstep (se 1 (by rfl) ⟨833726, by rfl⟩ : syracuseStep 1111635 = 1667453) B1667453
theorem B1111651 : Blo 1108626 1111651 := bstep (se 1 (by rfl) ⟨833738, by rfl⟩ : syracuseStep 1111651 = 1667477) B1667477
theorem B1668707 : Blo 1108626 1668707 := bstep (se 1 (by rfl) ⟨1251530, by rfl⟩ : syracuseStep 1668707 = 2503061) B2503061
theorem B1111667 : Blo 1108626 1111667 := bstep (se 1 (by rfl) ⟨833750, by rfl⟩ : syracuseStep 1111667 = 1667501) B1667501
theorem B1668737 : Blo 1108626 1668737 := bstep (se 2 (by rfl) ⟨625776, by rfl⟩ : syracuseStep 1668737 = 1251553) B1251553
theorem B1111683 : Blo 1108626 1111683 := bstep (se 1 (by rfl) ⟨833762, by rfl⟩ : syracuseStep 1111683 = 1667525) B1667525
theorem B7108229 : Blo 1108626 7108229 := bstep (se 4 (by rfl) ⟨666396, by rfl⟩ : syracuseStep 7108229 = 1332793) B1332793
theorem B6321797 : Blo 1108626 6321797 := bstep (se 4 (by rfl) ⟨592668, by rfl⟩ : syracuseStep 6321797 = 1185337) B1185337
theorem B1111699 : Blo 1108626 1111699 := bstep (se 1 (by rfl) ⟨833774, by rfl⟩ : syracuseStep 1111699 = 1667549) B1667549
theorem B1668755 : Blo 1108626 1668755 := bstep (se 1 (by rfl) ⟨1251566, by rfl⟩ : syracuseStep 1668755 = 2503133) B2503133
theorem B1111715 : Blo 1108626 1111715 := bstep (se 1 (by rfl) ⟨833786, by rfl⟩ : syracuseStep 1111715 = 1667573) B1667573
theorem B1668785 : Blo 1108626 1668785 := bstep (se 2 (by rfl) ⟨625794, by rfl⟩ : syracuseStep 1668785 = 1251589) B1251589
theorem B1111731 : Blo 1108626 1111731 := bstep (se 1 (by rfl) ⟨833798, by rfl⟩ : syracuseStep 1111731 = 1667597) B1667597
theorem B1111747 : Blo 1108626 1111747 := bstep (se 1 (by rfl) ⟨833810, by rfl⟩ : syracuseStep 1111747 = 1667621) B1667621
theorem B1668803 : Blo 1108626 1668803 := bstep (se 1 (by rfl) ⟨1251602, by rfl⟩ : syracuseStep 1668803 = 2503205) B2503205
theorem B1111763 : Blo 1108626 1111763 := bstep (se 1 (by rfl) ⟨833822, by rfl⟩ : syracuseStep 1111763 = 1667645) B1667645
theorem B1668833 : Blo 1108626 1668833 := bstep (se 2 (by rfl) ⟨625812, by rfl⟩ : syracuseStep 1668833 = 1251625) B1251625
theorem B1111779 : Blo 1108626 1111779 := bstep (se 1 (by rfl) ⟨833834, by rfl⟩ : syracuseStep 1111779 = 1667669) B1667669
theorem B1111795 : Blo 1108626 1111795 := bstep (se 1 (by rfl) ⟨833846, by rfl⟩ : syracuseStep 1111795 = 1667693) B1667693
theorem B1668851 : Blo 1108626 1668851 := bstep (se 1 (by rfl) ⟨1251638, by rfl⟩ : syracuseStep 1668851 = 2503277) B2503277
theorem B3602179 : Blo 1108626 3602179 := bstep (se 1 (by rfl) ⟨2701634, by rfl⟩ : syracuseStep 3602179 = 5403269) B5403269
theorem B1111811 : Blo 1108626 1111811 := bstep (se 1 (by rfl) ⟨833858, by rfl⟩ : syracuseStep 1111811 = 1667717) B1667717
theorem B1668881 : Blo 1108626 1668881 := bstep (se 2 (by rfl) ⟨625830, by rfl⟩ : syracuseStep 1668881 = 1251661) B1251661
theorem B1111827 : Blo 1108626 1111827 := bstep (se 1 (by rfl) ⟨833870, by rfl⟩ : syracuseStep 1111827 = 1667741) B1667741
theorem B1111843 : Blo 1108626 1111843 := bstep (se 1 (by rfl) ⟨833882, by rfl⟩ : syracuseStep 1111843 = 1667765) B1667765
theorem B1668899 : Blo 1108626 1668899 := bstep (se 1 (by rfl) ⟨1251674, by rfl⟩ : syracuseStep 1668899 = 2503349) B2503349
theorem B2815793 : Blo 1108626 2815793 := bstep (se 2 (by rfl) ⟨1055922, by rfl⟩ : syracuseStep 2815793 = 2111845) B2111845
theorem B1111859 : Blo 1108626 1111859 := bstep (se 1 (by rfl) ⟨833894, by rfl⟩ : syracuseStep 1111859 = 1667789) B1667789
theorem B1668929 : Blo 1108626 1668929 := bstep (se 2 (by rfl) ⟨625848, by rfl⟩ : syracuseStep 1668929 = 1251697) B1251697
theorem B1111875 : Blo 1108626 1111875 := bstep (se 1 (by rfl) ⟨833906, by rfl⟩ : syracuseStep 1111875 = 1667813) B1667813
theorem B1406803 : Blo 1108626 1406803 := bstep (se 1 (by rfl) ⟨1055102, by rfl⟩ : syracuseStep 1406803 = 2110205) B2110205
theorem B1111891 : Blo 1108626 1111891 := bstep (se 1 (by rfl) ⟨833918, by rfl⟩ : syracuseStep 1111891 = 1667837) B1667837
theorem B1111907 : Blo 1108626 1111907 := bstep (se 1 (by rfl) ⟨833930, by rfl⟩ : syracuseStep 1111907 = 1667861) B1667861
theorem B2815843 : Blo 1108626 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B1111923 : Blo 1108626 1111923 := bstep (se 1 (by rfl) ⟨833942, by rfl⟩ : syracuseStep 1111923 = 1667885) B1667885
theorem B1111939 : Blo 1108626 1111939 := bstep (se 1 (by rfl) ⟨833954, by rfl⟩ : syracuseStep 1111939 = 1667909) B1667909
theorem B1111955 : Blo 1108626 1111955 := bstep (se 1 (by rfl) ⟨833966, by rfl⟩ : syracuseStep 1111955 = 1667933) B1667933
theorem B1111971 : Blo 1108626 1111971 := bstep (se 1 (by rfl) ⟨833978, by rfl⟩ : syracuseStep 1111971 = 1667957) B1667957
theorem B1406899 : Blo 1108626 1406899 := bstep (se 1 (by rfl) ⟨1055174, by rfl⟩ : syracuseStep 1406899 = 2110349) B2110349
theorem B1111987 : Blo 1108626 1111987 := bstep (se 1 (by rfl) ⟨833990, by rfl⟩ : syracuseStep 1111987 = 1667981) B1667981
theorem B1112003 : Blo 1108626 1112003 := bstep (se 1 (by rfl) ⟨834002, by rfl⟩ : syracuseStep 1112003 = 1668005) B1668005
theorem B1112019 : Blo 1108626 1112019 := bstep (se 1 (by rfl) ⟨834014, by rfl⟩ : syracuseStep 1112019 = 1668029) B1668029
theorem B1112035 : Blo 1108626 1112035 := bstep (se 1 (by rfl) ⟨834026, by rfl⟩ : syracuseStep 1112035 = 1668053) B1668053
theorem B2815985 : Blo 1108626 2815985 := bstep (se 2 (by rfl) ⟨1055994, by rfl⟩ : syracuseStep 2815985 = 2111989) B2111989
theorem B1112051 : Blo 1108626 1112051 := bstep (se 1 (by rfl) ⟨834038, by rfl⟩ : syracuseStep 1112051 = 1668077) B1668077
theorem B1112067 : Blo 1108626 1112067 := bstep (se 1 (by rfl) ⟨834050, by rfl⟩ : syracuseStep 1112067 = 1668101) B1668101
theorem B1112083 : Blo 1108626 1112083 := bstep (se 1 (by rfl) ⟨834062, by rfl⟩ : syracuseStep 1112083 = 1668125) B1668125
theorem B1112099 : Blo 1108626 1112099 := bstep (se 1 (by rfl) ⟨834074, by rfl⟩ : syracuseStep 1112099 = 1668149) B1668149
theorem B1112115 : Blo 1108626 1112115 := bstep (se 1 (by rfl) ⟨834086, by rfl⟩ : syracuseStep 1112115 = 1668173) B1668173
theorem B1112131 : Blo 1108626 1112131 := bstep (se 1 (by rfl) ⟨834098, by rfl⟩ : syracuseStep 1112131 = 1668197) B1668197
theorem B1112147 : Blo 1108626 1112147 := bstep (se 1 (by rfl) ⟨834110, by rfl⟩ : syracuseStep 1112147 = 1668221) B1668221
theorem B1112163 : Blo 1108626 1112163 := bstep (se 1 (by rfl) ⟨834122, by rfl⟩ : syracuseStep 1112163 = 1668245) B1668245
theorem B1112179 : Blo 1108626 1112179 := bstep (se 1 (by rfl) ⟨834134, by rfl⟩ : syracuseStep 1112179 = 1668269) B1668269
theorem B1112195 : Blo 1108626 1112195 := bstep (se 1 (by rfl) ⟨834146, by rfl⟩ : syracuseStep 1112195 = 1668293) B1668293
theorem B1112211 : Blo 1108626 1112211 := bstep (se 1 (by rfl) ⟨834158, by rfl⟩ : syracuseStep 1112211 = 1668317) B1668317
theorem B1112227 : Blo 1108626 1112227 := bstep (se 1 (by rfl) ⟨834170, by rfl⟩ : syracuseStep 1112227 = 1668341) B1668341
theorem B1112243 : Blo 1108626 1112243 := bstep (se 1 (by rfl) ⟨834182, by rfl⟩ : syracuseStep 1112243 = 1668365) B1668365
theorem B1112259 : Blo 1108626 1112259 := bstep (se 1 (by rfl) ⟨834194, by rfl⟩ : syracuseStep 1112259 = 1668389) B1668389
theorem B1112275 : Blo 1108626 1112275 := bstep (se 1 (by rfl) ⟨834206, by rfl⟩ : syracuseStep 1112275 = 1668413) B1668413
theorem B1112291 : Blo 1108626 1112291 := bstep (se 1 (by rfl) ⟨834218, by rfl⟩ : syracuseStep 1112291 = 1668437) B1668437
theorem B1112307 : Blo 1108626 1112307 := bstep (se 1 (by rfl) ⟨834230, by rfl⟩ : syracuseStep 1112307 = 1668461) B1668461
theorem B1112323 : Blo 1108626 1112323 := bstep (se 1 (by rfl) ⟨834242, by rfl⟩ : syracuseStep 1112323 = 1668485) B1668485
theorem B1112339 : Blo 1108626 1112339 := bstep (se 1 (by rfl) ⟨834254, by rfl⟩ : syracuseStep 1112339 = 1668509) B1668509
theorem B1112355 : Blo 1108626 1112355 := bstep (se 1 (by rfl) ⟨834266, by rfl⟩ : syracuseStep 1112355 = 1668533) B1668533
theorem B6322481 : Blo 1108626 6322481 := bstep (se 2 (by rfl) ⟨2370930, by rfl⟩ : syracuseStep 6322481 = 4741861) B4741861
theorem B4749617 : Blo 1108626 4749617 := bstep (se 2 (by rfl) ⟨1781106, by rfl⟩ : syracuseStep 4749617 = 3562213) B3562213
theorem B1112371 : Blo 1108626 1112371 := bstep (se 1 (by rfl) ⟨834278, by rfl⟩ : syracuseStep 1112371 = 1668557) B1668557
theorem B1112387 : Blo 1108626 1112387 := bstep (se 1 (by rfl) ⟨834290, by rfl⟩ : syracuseStep 1112387 = 1668581) B1668581
theorem B3602765 : Blo 1108626 3602765 := bstep (se 3 (by rfl) ⟨675518, by rfl⟩ : syracuseStep 3602765 = 1351037) B1351037
theorem B1112403 : Blo 1108626 1112403 := bstep (se 1 (by rfl) ⟨834302, by rfl⟩ : syracuseStep 1112403 = 1668605) B1668605
theorem B1112419 : Blo 1108626 1112419 := bstep (se 1 (by rfl) ⟨834314, by rfl⟩ : syracuseStep 1112419 = 1668629) B1668629
theorem B1112435 : Blo 1108626 1112435 := bstep (se 1 (by rfl) ⟨834326, by rfl⟩ : syracuseStep 1112435 = 1668653) B1668653
theorem B1112451 : Blo 1108626 1112451 := bstep (se 1 (by rfl) ⟨834338, by rfl⟩ : syracuseStep 1112451 = 1668677) B1668677
theorem B9632141 : Blo 1108626 9632141 := bstep (se 3 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 9632141 = 3612053) B3612053
theorem B1112467 : Blo 1108626 1112467 := bstep (se 1 (by rfl) ⟨834350, by rfl⟩ : syracuseStep 1112467 = 1668701) B1668701
theorem B1407395 : Blo 1108626 1407395 := bstep (se 1 (by rfl) ⟨1055546, by rfl⟩ : syracuseStep 1407395 = 2111093) B2111093
theorem B1112483 : Blo 1108626 1112483 := bstep (se 1 (by rfl) ⟨834362, by rfl⟩ : syracuseStep 1112483 = 1668725) B1668725
theorem B1112499 : Blo 1108626 1112499 := bstep (se 1 (by rfl) ⟨834374, by rfl⟩ : syracuseStep 1112499 = 1668749) B1668749
theorem B1112515 : Blo 1108626 1112515 := bstep (se 1 (by rfl) ⟨834386, by rfl⟩ : syracuseStep 1112515 = 1668773) B1668773
theorem B1112531 : Blo 1108626 1112531 := bstep (se 1 (by rfl) ⟨834398, by rfl⟩ : syracuseStep 1112531 = 1668797) B1668797
theorem B1112547 : Blo 1108626 1112547 := bstep (se 1 (by rfl) ⟨834410, by rfl⟩ : syracuseStep 1112547 = 1668821) B1668821
theorem B1112563 : Blo 1108626 1112563 := bstep (se 1 (by rfl) ⟨834422, by rfl⟩ : syracuseStep 1112563 = 1668845) B1668845
theorem B1112579 : Blo 1108626 1112579 := bstep (se 1 (by rfl) ⟨834434, by rfl⟩ : syracuseStep 1112579 = 1668869) B1668869
theorem B1112595 : Blo 1108626 1112595 := bstep (se 1 (by rfl) ⟨834446, by rfl⟩ : syracuseStep 1112595 = 1668893) B1668893
theorem B1112611 : Blo 1108626 1112611 := bstep (se 1 (by rfl) ⟨834458, by rfl⟩ : syracuseStep 1112611 = 1668917) B1668917
theorem B1800835 : Blo 1108626 1800835 := bstep (se 1 (by rfl) ⟨1350626, by rfl⟩ : syracuseStep 1800835 = 2701253) B2701253
theorem B5995235 : Blo 1108626 5995235 := bstep (se 1 (by rfl) ⟨4496426, by rfl⟩ : syracuseStep 5995235 = 8992853) B8992853
theorem B6847217 : Blo 1108626 6847217 := bstep (se 2 (by rfl) ⟨2567706, by rfl⟩ : syracuseStep 6847217 = 5135413) B5135413
theorem B1604483 : Blo 1108626 1604483 := bstep (se 1 (by rfl) ⟨1203362, by rfl⟩ : syracuseStep 1604483 = 2406725) B2406725
theorem B4750285 : Blo 1108626 4750285 := bstep (se 3 (by rfl) ⟨890678, by rfl⟩ : syracuseStep 4750285 = 1781357) B1781357
theorem B5340131 : Blo 1108626 5340131 := bstep (se 1 (by rfl) ⟨4005098, by rfl⟩ : syracuseStep 5340131 = 8010197) B8010197
theorem B4815949 : Blo 1108626 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B1408099 : Blo 1108626 1408099 := bstep (se 1 (by rfl) ⟨1056074, by rfl⟩ : syracuseStep 1408099 = 2112149) B2112149
theorem B5340593 : Blo 1108626 5340593 := bstep (se 2 (by rfl) ⟨2002722, by rfl⟩ : syracuseStep 5340593 = 4005445) B4005445
theorem B4816397 : Blo 1108626 4816397 := bstep (se 3 (by rfl) ⟨903074, by rfl⟩ : syracuseStep 4816397 = 1806149) B1806149
theorem B7110179 : Blo 1108626 7110179 := bstep (se 1 (by rfl) ⟨5332634, by rfl⟩ : syracuseStep 7110179 = 10665269) B10665269
theorem B4750883 : Blo 1108626 4750883 := bstep (se 1 (by rfl) ⟨3563162, by rfl⟩ : syracuseStep 4750883 = 7126325) B7126325
theorem B5144141 : Blo 1108626 5144141 := bstep (se 3 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 5144141 = 1929053) B1929053
theorem B9010885 : Blo 1108626 9010885 := bstep (se 4 (by rfl) ⟨844770, by rfl⟩ : syracuseStep 9010885 = 1689541) B1689541
theorem B1900241 : Blo 1108626 1900241 := bstep (se 2 (by rfl) ⟨712590, by rfl⟩ : syracuseStep 1900241 = 1425181) B1425181
theorem B6323939 : Blo 1108626 6323939 := bstep (se 1 (by rfl) ⟨4742954, by rfl⟩ : syracuseStep 6323939 = 9485909) B9485909
theorem B1605587 : Blo 1108626 1605587 := bstep (se 1 (by rfl) ⟨1204190, by rfl⟩ : syracuseStep 1605587 = 2408381) B2408381
theorem B8126435 : Blo 1108626 8126435 := bstep (se 1 (by rfl) ⟨6094826, by rfl⟩ : syracuseStep 8126435 = 12189653) B12189653
theorem B1998859 : Blo 1108626 1998859 := bstep (se 1 (by rfl) ⟨1499144, by rfl⟩ : syracuseStep 1998859 = 2998289) B2998289
theorem B4816913 : Blo 1108626 4816913 := bstep (se 2 (by rfl) ⟨1806342, by rfl⟩ : syracuseStep 4816913 = 3612685) B3612685
theorem B3801239 : Blo 1108626 3801239 := bstep (se 1 (by rfl) ⟨2850929, by rfl⟩ : syracuseStep 3801239 = 5701859) B5701859
theorem B2162945 : Blo 1108626 2162945 := bstep (se 2 (by rfl) ⟨811104, by rfl⟩ : syracuseStep 2162945 = 1622209) B1622209
theorem B8421893 : Blo 1108626 8421893 := bstep (se 4 (by rfl) ⟨789552, by rfl⟩ : syracuseStep 8421893 = 1579105) B1579105
theorem B13009501 : Blo 1108626 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B1442443 : Blo 1108626 1442443 := bstep (se 1 (by rfl) ⟨1081832, by rfl⟩ : syracuseStep 1442443 = 2163665) B2163665
theorem B4621079 : Blo 1108626 4621079 := bstep (se 1 (by rfl) ⟨3465809, by rfl⟩ : syracuseStep 4621079 = 6931619) B6931619
theorem B1999667 : Blo 1108626 1999667 := bstep (se 1 (by rfl) ⟨1499750, by rfl⟩ : syracuseStep 1999667 = 2999501) B2999501
theorem B1901387 : Blo 1108626 1901387 := bstep (se 1 (by rfl) ⟨1426040, by rfl⟩ : syracuseStep 1901387 = 2852081) B2852081
theorem B1999883 : Blo 1108626 1999883 := bstep (se 1 (by rfl) ⟨1499912, by rfl⟩ : syracuseStep 1999883 = 2999825) B2999825
theorem B9471077 : Blo 1108626 9471077 := bstep (se 4 (by rfl) ⟨887913, by rfl⟩ : syracuseStep 9471077 = 1775827) B1775827
theorem B4752557 : Blo 1108626 4752557 := bstep (se 3 (by rfl) ⟨891104, by rfl⟩ : syracuseStep 4752557 = 1782209) B1782209
theorem B3998899 : Blo 1108626 3998899 := bstep (se 1 (by rfl) ⟨2999174, by rfl⟩ : syracuseStep 3998899 = 5998349) B5998349
theorem B7603379 : Blo 1108626 7603379 := bstep (se 1 (by rfl) ⟨5702534, by rfl⟩ : syracuseStep 7603379 = 11405069) B11405069
theorem B3606167 : Blo 1108626 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B9471761 : Blo 1108626 9471761 := bstep (se 2 (by rfl) ⟨3551910, by rfl⟩ : syracuseStep 9471761 = 7103821) B7103821
theorem B3999563 : Blo 1108626 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B1247287 : Blo 1108626 1247287 := bstep (se 1 (by rfl) ⟨935465, by rfl⟩ : syracuseStep 1247287 = 1870931) B1870931
theorem B2001035 : Blo 1108626 2001035 := bstep (se 1 (by rfl) ⟨1500776, by rfl⟩ : syracuseStep 2001035 = 3001553) B3001553
theorem B6326423 : Blo 1108626 6326423 := bstep (se 1 (by rfl) ⟨4744817, by rfl⟩ : syracuseStep 6326423 = 9489635) B9489635
theorem B1247467 : Blo 1108626 1247467 := bstep (se 1 (by rfl) ⟨935600, by rfl⟩ : syracuseStep 1247467 = 1871201) B1871201
theorem B6850861 : Blo 1108626 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B1247575 : Blo 1108626 1247575 := bstep (se 1 (by rfl) ⟨935681, by rfl⟩ : syracuseStep 1247575 = 1871363) B1871363
theorem B1247755 : Blo 1108626 1247755 := bstep (se 1 (by rfl) ⟨935816, by rfl⟩ : syracuseStep 1247755 = 1871633) B1871633
theorem B1247863 : Blo 1108626 1247863 := bstep (se 1 (by rfl) ⟨935897, by rfl⟩ : syracuseStep 1247863 = 1871795) B1871795
theorem B1248043 : Blo 1108626 1248043 := bstep (se 1 (by rfl) ⟨936032, by rfl⟩ : syracuseStep 1248043 = 1872065) B1872065
theorem B8424323 : Blo 1108626 8424323 := bstep (se 1 (by rfl) ⟨6318242, by rfl⟩ : syracuseStep 8424323 = 12636485) B12636485
theorem B1248151 : Blo 1108626 1248151 := bstep (se 1 (by rfl) ⟨936113, by rfl⟩ : syracuseStep 1248151 = 1872227) B1872227
theorem B1248331 : Blo 1108626 1248331 := bstep (se 1 (by rfl) ⟨936248, by rfl⟩ : syracuseStep 1248331 = 1872497) B1872497
theorem B1248439 : Blo 1108626 1248439 := bstep (se 1 (by rfl) ⟨936329, by rfl⟩ : syracuseStep 1248439 = 1872659) B1872659
theorem B1248619 : Blo 1108626 1248619 := bstep (se 1 (by rfl) ⟨936464, by rfl⟩ : syracuseStep 1248619 = 1872929) B1872929
theorem B1871255 : Blo 1108626 1871255 := bstep (se 1 (by rfl) ⟨1403441, by rfl⟩ : syracuseStep 1871255 = 2806883) B2806883
theorem B1248727 : Blo 1108626 1248727 := bstep (se 1 (by rfl) ⟨936545, by rfl⟩ : syracuseStep 1248727 = 1873091) B1873091
theorem B1871383 : Blo 1108626 1871383 := bstep (se 1 (by rfl) ⟨1403537, by rfl⟩ : syracuseStep 1871383 = 2807075) B2807075
theorem B1248907 : Blo 1108626 1248907 := bstep (se 1 (by rfl) ⟨936680, by rfl⟩ : syracuseStep 1248907 = 1873361) B1873361
theorem B7999181 : Blo 1108626 7999181 := bstep (se 3 (by rfl) ⟨1499846, by rfl⟩ : syracuseStep 7999181 = 2999693) B2999693
theorem B1249015 : Blo 1108626 1249015 := bstep (se 1 (by rfl) ⟨936761, by rfl⟩ : syracuseStep 1249015 = 1873523) B1873523
theorem B1249195 : Blo 1108626 1249195 := bstep (se 1 (by rfl) ⟨936896, by rfl⟩ : syracuseStep 1249195 = 1873793) B1873793
theorem B2494475 : Blo 1108626 2494475 := bstep (se 1 (by rfl) ⟨1870856, by rfl⟩ : syracuseStep 2494475 = 3741713) B3741713
theorem B1249303 : Blo 1108626 1249303 := bstep (se 1 (by rfl) ⟨936977, by rfl⟩ : syracuseStep 1249303 = 1873955) B1873955
theorem B2494529 : Blo 1108626 2494529 := bstep (se 2 (by rfl) ⟨935448, by rfl⟩ : syracuseStep 2494529 = 1870897) B1870897
theorem B1872011 : Blo 1108626 1872011 := bstep (se 1 (by rfl) ⟨1404008, by rfl⟩ : syracuseStep 1872011 = 2808017) B2808017
theorem B1249483 : Blo 1108626 1249483 := bstep (se 1 (by rfl) ⟨937112, by rfl⟩ : syracuseStep 1249483 = 1874225) B1874225
theorem B1872139 : Blo 1108626 1872139 := bstep (se 1 (by rfl) ⟨1404104, by rfl⟩ : syracuseStep 1872139 = 2808209) B2808209
theorem B2494745 : Blo 1108626 2494745 := bstep (se 2 (by rfl) ⟨935529, by rfl⟩ : syracuseStep 2494745 = 1871059) B1871059
theorem B1249591 : Blo 1108626 1249591 := bstep (se 1 (by rfl) ⟨937193, by rfl⟩ : syracuseStep 1249591 = 1874387) B1874387
theorem B1184107 : Blo 1108626 1184107 := bstep (se 1 (by rfl) ⟨888080, by rfl⟩ : syracuseStep 1184107 = 1776161) B1776161
theorem B2494835 : Blo 1108626 2494835 := bstep (se 1 (by rfl) ⟨1871126, by rfl⟩ : syracuseStep 2494835 = 3742253) B3742253
theorem B2494871 : Blo 1108626 2494871 := bstep (se 1 (by rfl) ⟨1871153, by rfl⟩ : syracuseStep 2494871 = 3742307) B3742307
theorem B1872281 : Blo 1108626 1872281 := bstep (se 2 (by rfl) ⟨702105, by rfl⟩ : syracuseStep 1872281 = 1404211) B1404211
theorem B1249771 : Blo 1108626 1249771 := bstep (se 1 (by rfl) ⟨937328, by rfl⟩ : syracuseStep 1249771 = 1874657) B1874657
theorem B1872409 : Blo 1108626 1872409 := bstep (se 2 (by rfl) ⟨702153, by rfl⟩ : syracuseStep 1872409 = 1404307) B1404307
theorem B2495051 : Blo 1108626 2495051 := bstep (se 1 (by rfl) ⟨1871288, by rfl⟩ : syracuseStep 2495051 = 3742577) B3742577
theorem B1249879 : Blo 1108626 1249879 := bstep (se 1 (by rfl) ⟨937409, by rfl⟩ : syracuseStep 1249879 = 1874819) B1874819
theorem B2495105 : Blo 1108626 2495105 := bstep (se 2 (by rfl) ⟨935664, by rfl⟩ : syracuseStep 2495105 = 1871329) B1871329
theorem B1250059 : Blo 1108626 1250059 := bstep (se 1 (by rfl) ⟨937544, by rfl⟩ : syracuseStep 1250059 = 1875089) B1875089
theorem B2495321 : Blo 1108626 2495321 := bstep (se 2 (by rfl) ⟨935745, by rfl⟩ : syracuseStep 2495321 = 1871491) B1871491
theorem B1250167 : Blo 1108626 1250167 := bstep (se 1 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 1250167 = 1875251) B1875251
theorem B2495411 : Blo 1108626 2495411 := bstep (se 1 (by rfl) ⟨1871558, by rfl⟩ : syracuseStep 2495411 = 3743117) B3743117
theorem B2495447 : Blo 1108626 2495447 := bstep (se 1 (by rfl) ⟨1871585, by rfl⟩ : syracuseStep 2495447 = 3743171) B3743171
theorem B1250347 : Blo 1108626 1250347 := bstep (se 1 (by rfl) ⟨937760, by rfl⟩ : syracuseStep 1250347 = 1875521) B1875521
theorem B1872983 : Blo 1108626 1872983 := bstep (se 1 (by rfl) ⟨1404737, by rfl⟩ : syracuseStep 1872983 = 2809475) B2809475
theorem B2495627 : Blo 1108626 2495627 := bstep (se 1 (by rfl) ⟨1871720, by rfl⟩ : syracuseStep 2495627 = 3743441) B3743441
theorem B1250455 : Blo 1108626 1250455 := bstep (se 1 (by rfl) ⟨937841, by rfl⟩ : syracuseStep 1250455 = 1875683) B1875683
theorem B20288663 : Blo 1108626 20288663 := bstep (se 1 (by rfl) ⟨15216497, by rfl⟩ : syracuseStep 20288663 = 30432995) B30432995
theorem B2495681 : Blo 1108626 2495681 := bstep (se 2 (by rfl) ⟨935880, by rfl⟩ : syracuseStep 2495681 = 1871761) B1871761
theorem B1873111 : Blo 1108626 1873111 := bstep (se 1 (by rfl) ⟨1404833, by rfl⟩ : syracuseStep 1873111 = 2809667) B2809667
theorem B1250635 : Blo 1108626 1250635 := bstep (se 1 (by rfl) ⟨937976, by rfl⟩ : syracuseStep 1250635 = 1875953) B1875953
theorem B2495897 : Blo 1108626 2495897 := bstep (se 2 (by rfl) ⟨935961, by rfl⟩ : syracuseStep 2495897 = 1871923) B1871923
theorem B1250743 : Blo 1108626 1250743 := bstep (se 1 (by rfl) ⟨938057, by rfl⟩ : syracuseStep 1250743 = 1876115) B1876115
theorem B2495987 : Blo 1108626 2495987 := bstep (se 1 (by rfl) ⟨1871990, by rfl⟩ : syracuseStep 2495987 = 3743981) B3743981
theorem B2496023 : Blo 1108626 2496023 := bstep (se 1 (by rfl) ⟨1872017, by rfl⟩ : syracuseStep 2496023 = 3744035) B3744035
theorem B1250923 : Blo 1108626 1250923 := bstep (se 1 (by rfl) ⟨938192, by rfl⟩ : syracuseStep 1250923 = 1876385) B1876385
theorem B2496203 : Blo 1108626 2496203 := bstep (se 1 (by rfl) ⟨1872152, by rfl⟩ : syracuseStep 2496203 = 3744305) B3744305
theorem B1251031 : Blo 1108626 1251031 := bstep (se 1 (by rfl) ⟨938273, by rfl⟩ : syracuseStep 1251031 = 1876547) B1876547
theorem B2496257 : Blo 1108626 2496257 := bstep (se 2 (by rfl) ⟨936096, by rfl⟩ : syracuseStep 2496257 = 1872193) B1872193
theorem B1185559 : Blo 1108626 1185559 := bstep (se 1 (by rfl) ⟨889169, by rfl⟩ : syracuseStep 1185559 = 1778339) B1778339
theorem B1873739 : Blo 1108626 1873739 := bstep (se 1 (by rfl) ⟨1405304, by rfl⟩ : syracuseStep 1873739 = 2810609) B2810609
theorem B4495193 : Blo 1108626 4495193 := bstep (se 2 (by rfl) ⟨1685697, by rfl⟩ : syracuseStep 4495193 = 3371395) B3371395
theorem B1251211 : Blo 1108626 1251211 := bstep (se 1 (by rfl) ⟨938408, by rfl⟩ : syracuseStep 1251211 = 1876817) B1876817
theorem B11409329 : Blo 1108626 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B1873867 : Blo 1108626 1873867 := bstep (se 1 (by rfl) ⟨1405400, by rfl⟩ : syracuseStep 1873867 = 2810801) B2810801
theorem B2496473 : Blo 1108626 2496473 := bstep (se 2 (by rfl) ⟨936177, by rfl⟩ : syracuseStep 2496473 = 1872355) B1872355
theorem B1251319 : Blo 1108626 1251319 := bstep (se 1 (by rfl) ⟨938489, by rfl⟩ : syracuseStep 1251319 = 1876979) B1876979
theorem B11999249 : Blo 1108626 11999249 := bstep (se 2 (by rfl) ⟨4499718, by rfl⟩ : syracuseStep 11999249 = 8999437) B8999437
theorem B2496563 : Blo 1108626 2496563 := bstep (se 1 (by rfl) ⟨1872422, by rfl⟩ : syracuseStep 2496563 = 3744845) B3744845
theorem B2496599 : Blo 1108626 2496599 := bstep (se 1 (by rfl) ⟨1872449, by rfl⟩ : syracuseStep 2496599 = 3744899) B3744899
theorem B1874009 : Blo 1108626 1874009 := bstep (se 2 (by rfl) ⟨702753, by rfl⟩ : syracuseStep 1874009 = 1405507) B1405507
theorem B7116893 : Blo 1108626 7116893 := bstep (se 3 (by rfl) ⟨1334417, by rfl⟩ : syracuseStep 7116893 = 2668835) B2668835
theorem B1185931 : Blo 1108626 1185931 := bstep (se 1 (by rfl) ⟨889448, by rfl⟩ : syracuseStep 1185931 = 1778897) B1778897
theorem B1251499 : Blo 1108626 1251499 := bstep (se 1 (by rfl) ⟨938624, by rfl⟩ : syracuseStep 1251499 = 1877249) B1877249
theorem B3741875 : Blo 1108626 3741875 := bstep (se 1 (by rfl) ⟨2806406, by rfl⟩ : syracuseStep 3741875 = 5612813) B5612813
theorem B9607373 : Blo 1108626 9607373 := bstep (se 3 (by rfl) ⟨1801382, by rfl⟩ : syracuseStep 9607373 = 3602765) B3602765
theorem B8427725 : Blo 1108626 8427725 := bstep (se 3 (by rfl) ⟨1580198, by rfl⟩ : syracuseStep 8427725 = 3160397) B3160397
theorem B1874137 : Blo 1108626 1874137 := bstep (se 2 (by rfl) ⟨702801, by rfl⟩ : syracuseStep 1874137 = 1405603) B1405603
theorem B2496779 : Blo 1108626 2496779 := bstep (se 1 (by rfl) ⟨1872584, by rfl⟩ : syracuseStep 2496779 = 3745169) B3745169
theorem B1251607 : Blo 1108626 1251607 := bstep (se 1 (by rfl) ⟨938705, by rfl⟩ : syracuseStep 1251607 = 1877411) B1877411
theorem B4004147 : Blo 1108626 4004147 := bstep (se 1 (by rfl) ⟨3003110, by rfl⟩ : syracuseStep 4004147 = 6006221) B6006221
theorem B2496833 : Blo 1108626 2496833 := bstep (se 2 (by rfl) ⟨936312, by rfl⟩ : syracuseStep 2496833 = 1872625) B1872625
theorem B3742145 : Blo 1108626 3742145 := bstep (se 2 (by rfl) ⟨1403304, by rfl⟩ : syracuseStep 3742145 = 2806609) B2806609
theorem B2497049 : Blo 1108626 2497049 := bstep (se 2 (by rfl) ⟨936393, by rfl⟩ : syracuseStep 2497049 = 1872787) B1872787
theorem B2497139 : Blo 1108626 2497139 := bstep (se 1 (by rfl) ⟨1872854, by rfl⟩ : syracuseStep 2497139 = 3745709) B3745709
theorem B2497175 : Blo 1108626 2497175 := bstep (se 1 (by rfl) ⟨1872881, by rfl⟩ : syracuseStep 2497175 = 3745763) B3745763
theorem B8428211 : Blo 1108626 8428211 := bstep (se 1 (by rfl) ⟨6321158, by rfl⟩ : syracuseStep 8428211 = 12642317) B12642317
theorem B2530007 : Blo 1108626 2530007 := bstep (se 1 (by rfl) ⟨1897505, by rfl⟩ : syracuseStep 2530007 = 3795011) B3795011
theorem B1874711 : Blo 1108626 1874711 := bstep (se 1 (by rfl) ⟨1406033, by rfl⟩ : syracuseStep 1874711 = 2812067) B2812067
theorem B97327925 : Blo 1108626 97327925 := bstep (se 5 (by rfl) ⟨4562246, by rfl⟩ : syracuseStep 97327925 = 9124493) B9124493
theorem B2497355 : Blo 1108626 2497355 := bstep (se 1 (by rfl) ⟨1873016, by rfl⟩ : syracuseStep 2497355 = 3746033) B3746033
theorem B6331229 : Blo 1108626 6331229 := bstep (se 3 (by rfl) ⟨1187105, by rfl⟩ : syracuseStep 6331229 = 2374211) B2374211
theorem B2497409 : Blo 1108626 2497409 := bstep (se 2 (by rfl) ⟨936528, by rfl⟩ : syracuseStep 2497409 = 1873057) B1873057
theorem B1874839 : Blo 1108626 1874839 := bstep (se 1 (by rfl) ⟨1406129, by rfl⟩ : syracuseStep 1874839 = 2812259) B2812259
theorem B3742685 : Blo 1108626 3742685 := bstep (se 3 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 3742685 = 1403507) B1403507
theorem B2497625 : Blo 1108626 2497625 := bstep (se 2 (by rfl) ⟨936609, by rfl⟩ : syracuseStep 2497625 = 1873219) B1873219
theorem B2497715 : Blo 1108626 2497715 := bstep (se 1 (by rfl) ⟨1873286, by rfl⟩ : syracuseStep 2497715 = 3746573) B3746573
theorem B2497751 : Blo 1108626 2497751 := bstep (se 1 (by rfl) ⟨1873313, by rfl⟩ : syracuseStep 2497751 = 3746627) B3746627
theorem B9018641 : Blo 1108626 9018641 := bstep (se 2 (by rfl) ⟨3381990, by rfl⟩ : syracuseStep 9018641 = 6763981) B6763981
theorem B10132867 : Blo 1108626 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B2497931 : Blo 1108626 2497931 := bstep (se 1 (by rfl) ⟨1873448, by rfl⟩ : syracuseStep 2497931 = 3746897) B3746897
theorem B2137495 : Blo 1108626 2137495 := bstep (se 1 (by rfl) ⟨1603121, by rfl⟩ : syracuseStep 2137495 = 3206243) B3206243
theorem B2497985 : Blo 1108626 2497985 := bstep (se 2 (by rfl) ⟨936744, by rfl⟩ : syracuseStep 2497985 = 1873489) B1873489
theorem B1875467 : Blo 1108626 1875467 := bstep (se 1 (by rfl) ⟨1406600, by rfl⟩ : syracuseStep 1875467 = 2813201) B2813201
theorem B1875595 : Blo 1108626 1875595 := bstep (se 1 (by rfl) ⟨1406696, by rfl⟩ : syracuseStep 1875595 = 2813393) B2813393
theorem B2498201 : Blo 1108626 2498201 := bstep (se 2 (by rfl) ⟨936825, by rfl⟩ : syracuseStep 2498201 = 1873651) B1873651
theorem B2498291 : Blo 1108626 2498291 := bstep (se 1 (by rfl) ⟨1873718, by rfl⟩ : syracuseStep 2498291 = 3747437) B3747437
theorem B2498327 : Blo 1108626 2498327 := bstep (se 1 (by rfl) ⟨1873745, by rfl⟩ : syracuseStep 2498327 = 3747491) B3747491
theorem B1875737 : Blo 1108626 1875737 := bstep (se 2 (by rfl) ⟨703401, by rfl⟩ : syracuseStep 1875737 = 1406803) B1406803
theorem B92348261 : Blo 1108626 92348261 := bstep (se 4 (by rfl) ⟨8657649, by rfl⟩ : syracuseStep 92348261 = 17315299) B17315299
theorem B1875865 : Blo 1108626 1875865 := bstep (se 2 (by rfl) ⟨703449, by rfl⟩ : syracuseStep 1875865 = 1406899) B1406899
theorem B2105291 : Blo 1108626 2105291 := bstep (se 1 (by rfl) ⟨1578968, by rfl⟩ : syracuseStep 2105291 = 3157937) B3157937
theorem B2498507 : Blo 1108626 2498507 := bstep (se 1 (by rfl) ⟨1873880, by rfl⟩ : syracuseStep 2498507 = 3747761) B3747761
theorem B2105345 : Blo 1108626 2105345 := bstep (se 2 (by rfl) ⟨789504, by rfl⟩ : syracuseStep 2105345 = 1579009) B1579009
theorem B2498561 : Blo 1108626 2498561 := bstep (se 2 (by rfl) ⟨936960, by rfl⟩ : syracuseStep 2498561 = 1873921) B1873921
theorem B3743819 : Blo 1108626 3743819 := bstep (se 1 (by rfl) ⟨2807864, by rfl⟩ : syracuseStep 3743819 = 5615729) B5615729
theorem B8429669 : Blo 1108626 8429669 := bstep (se 4 (by rfl) ⟨790281, by rfl⟩ : syracuseStep 8429669 = 1580563) B1580563
theorem B2498777 : Blo 1108626 2498777 := bstep (se 2 (by rfl) ⟨937041, by rfl⟩ : syracuseStep 2498777 = 1874083) B1874083
theorem B2498867 : Blo 1108626 2498867 := bstep (se 1 (by rfl) ⟨1874150, by rfl⟩ : syracuseStep 2498867 = 3748301) B3748301
theorem B2498903 : Blo 1108626 2498903 := bstep (se 1 (by rfl) ⟨1874177, by rfl⟩ : syracuseStep 2498903 = 3748355) B3748355
theorem B3744089 : Blo 1108626 3744089 := bstep (se 2 (by rfl) ⟨1404033, by rfl⟩ : syracuseStep 3744089 = 2808067) B2808067
theorem B1876439 : Blo 1108626 1876439 := bstep (se 1 (by rfl) ⟨1407329, by rfl⟩ : syracuseStep 1876439 = 2814659) B2814659
theorem B2499083 : Blo 1108626 2499083 := bstep (se 1 (by rfl) ⟨1874312, by rfl⟩ : syracuseStep 2499083 = 3748625) B3748625
theorem B2499137 : Blo 1108626 2499137 := bstep (se 2 (by rfl) ⟨937176, by rfl⟩ : syracuseStep 2499137 = 1874353) B1874353
theorem B8430155 : Blo 1108626 8430155 := bstep (se 1 (by rfl) ⟨6322616, by rfl⟩ : syracuseStep 8430155 = 12645233) B12645233
theorem B1876567 : Blo 1108626 1876567 := bstep (se 1 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 1876567 = 2814851) B2814851
theorem B2368129 : Blo 1108626 2368129 := bstep (se 2 (by rfl) ⟨888048, by rfl⟩ : syracuseStep 2368129 = 1776097) B1776097
theorem B2499353 : Blo 1108626 2499353 := bstep (se 2 (by rfl) ⟨937257, by rfl⟩ : syracuseStep 2499353 = 1874515) B1874515
theorem B1778519 : Blo 1108626 1778519 := bstep (se 1 (by rfl) ⟨1333889, by rfl⟩ : syracuseStep 1778519 = 2667779) B2667779
theorem B2499443 : Blo 1108626 2499443 := bstep (se 1 (by rfl) ⟨1874582, by rfl⟩ : syracuseStep 2499443 = 3749165) B3749165
theorem B4498307 : Blo 1108626 4498307 := bstep (se 1 (by rfl) ⟨3373730, by rfl⟩ : syracuseStep 4498307 = 6747461) B6747461
theorem B2106263 : Blo 1108626 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B2499479 : Blo 1108626 2499479 := bstep (se 1 (by rfl) ⟨1874609, by rfl⟩ : syracuseStep 2499479 = 3749219) B3749219
theorem B3744791 : Blo 1108626 3744791 := bstep (se 1 (by rfl) ⟨2808593, by rfl⟩ : syracuseStep 3744791 = 5617187) B5617187
theorem B2499659 : Blo 1108626 2499659 := bstep (se 1 (by rfl) ⟨1874744, by rfl⟩ : syracuseStep 2499659 = 3749489) B3749489
theorem B2499713 : Blo 1108626 2499713 := bstep (se 2 (by rfl) ⟨937392, by rfl⟩ : syracuseStep 2499713 = 1874785) B1874785
theorem B1877195 : Blo 1108626 1877195 := bstep (se 1 (by rfl) ⟨1407896, by rfl⟩ : syracuseStep 1877195 = 2815793) B2815793
theorem B1778903 : Blo 1108626 1778903 := bstep (se 1 (by rfl) ⟨1334177, by rfl⟩ : syracuseStep 1778903 = 2668355) B2668355
theorem B6333713 : Blo 1108626 6333713 := bstep (se 2 (by rfl) ⟨2375142, by rfl⟩ : syracuseStep 6333713 = 4750285) B4750285
theorem B1877323 : Blo 1108626 1877323 := bstep (se 1 (by rfl) ⟨1407992, by rfl⟩ : syracuseStep 1877323 = 2815985) B2815985
theorem B2368855 : Blo 1108626 2368855 := bstep (se 1 (by rfl) ⟨1776641, by rfl⟩ : syracuseStep 2368855 = 3553283) B3553283
theorem B1779031 : Blo 1108626 1779031 := bstep (se 1 (by rfl) ⟨1334273, by rfl⟩ : syracuseStep 1779031 = 2668547) B2668547
theorem B2499929 : Blo 1108626 2499929 := bstep (se 2 (by rfl) ⟨937473, by rfl⟩ : syracuseStep 2499929 = 1874947) B1874947
theorem B17114485 : Blo 1108626 17114485 := bstep (se 5 (by rfl) ⟨802241, by rfl⟩ : syracuseStep 17114485 = 1604483) B1604483
theorem B2106803 : Blo 1108626 2106803 := bstep (se 1 (by rfl) ⟨1580102, by rfl⟩ : syracuseStep 2106803 = 3160205) B3160205
theorem B2500019 : Blo 1108626 2500019 := bstep (se 1 (by rfl) ⟨1875014, by rfl⟩ : syracuseStep 2500019 = 3750029) B3750029
theorem B2500055 : Blo 1108626 2500055 := bstep (se 1 (by rfl) ⟨1875041, by rfl⟩ : syracuseStep 2500055 = 3750083) B3750083
theorem B1877465 : Blo 1108626 1877465 := bstep (se 2 (by rfl) ⟨704049, by rfl⟩ : syracuseStep 1877465 = 1408099) B1408099
theorem B3745331 : Blo 1108626 3745331 := bstep (se 1 (by rfl) ⟨2808998, by rfl⟩ : syracuseStep 3745331 = 5617997) B5617997
theorem B2500235 : Blo 1108626 2500235 := bstep (se 1 (by rfl) ⟨1875176, by rfl⟩ : syracuseStep 2500235 = 3750353) B3750353
theorem B2500289 : Blo 1108626 2500289 := bstep (se 2 (by rfl) ⟨937608, by rfl⟩ : syracuseStep 2500289 = 1875217) B1875217
theorem B6006545 : Blo 1108626 6006545 := bstep (se 2 (by rfl) ⟨2252454, by rfl⟩ : syracuseStep 6006545 = 4504909) B4504909
theorem B3745601 : Blo 1108626 3745601 := bstep (se 2 (by rfl) ⟨1404600, by rfl⟩ : syracuseStep 3745601 = 2809201) B2809201
theorem B4564811 : Blo 1108626 4564811 := bstep (se 1 (by rfl) ⟨3423608, by rfl⟩ : syracuseStep 4564811 = 6847217) B6847217
theorem B2107289 : Blo 1108626 2107289 := bstep (se 2 (by rfl) ⟨790233, by rfl⟩ : syracuseStep 2107289 = 1580467) B1580467
theorem B2500505 : Blo 1108626 2500505 := bstep (se 2 (by rfl) ⟨937689, by rfl⟩ : syracuseStep 2500505 = 1875379) B1875379
theorem B2500595 : Blo 1108626 2500595 := bstep (se 1 (by rfl) ⟨1875446, by rfl⟩ : syracuseStep 2500595 = 3750893) B3750893
theorem B2500631 : Blo 1108626 2500631 := bstep (se 1 (by rfl) ⟨1875473, by rfl⟩ : syracuseStep 2500631 = 3750947) B3750947
theorem B300394565 : Blo 1108626 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B17082461 : Blo 1108626 17082461 := bstep (se 3 (by rfl) ⟨3202961, by rfl⟩ : syracuseStep 17082461 = 6405923) B6405923
theorem B2369675 : Blo 1108626 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B1779851 : Blo 1108626 1779851 := bstep (se 1 (by rfl) ⟨1334888, by rfl⟩ : syracuseStep 1779851 = 2669777) B2669777
theorem B2500811 : Blo 1108626 2500811 := bstep (se 1 (by rfl) ⟨1875608, by rfl⟩ : syracuseStep 2500811 = 3751217) B3751217
theorem B5613785 : Blo 1108626 5613785 := bstep (se 2 (by rfl) ⟨2105169, by rfl⟩ : syracuseStep 5613785 = 4210339) B4210339
theorem B2500865 : Blo 1108626 2500865 := bstep (se 2 (by rfl) ⟨937824, by rfl⟩ : syracuseStep 2500865 = 1875649) B1875649
theorem B1779979 : Blo 1108626 1779979 := bstep (se 1 (by rfl) ⟨1334984, by rfl⟩ : syracuseStep 1779979 = 2669969) B2669969
theorem B1583383 : Blo 1108626 1583383 := bstep (se 1 (by rfl) ⟨1187537, by rfl⟩ : syracuseStep 1583383 = 2375075) B2375075
theorem B3746141 : Blo 1108626 3746141 := bstep (se 3 (by rfl) ⟨702401, by rfl⟩ : syracuseStep 3746141 = 1404803) B1404803
theorem B57616757 : Blo 1108626 57616757 := bstep (se 5 (by rfl) ⟨2700785, by rfl⟩ : syracuseStep 57616757 = 5401571) B5401571
theorem B2501081 : Blo 1108626 2501081 := bstep (se 2 (by rfl) ⟨937905, by rfl⟩ : syracuseStep 2501081 = 1875811) B1875811
theorem B4008413 : Blo 1108626 4008413 := bstep (se 3 (by rfl) ⟨751577, by rfl⟩ : syracuseStep 4008413 = 1503155) B1503155
theorem B2501171 : Blo 1108626 2501171 := bstep (se 1 (by rfl) ⟨1875878, by rfl⟩ : syracuseStep 2501171 = 3751757) B3751757
theorem B2501207 : Blo 1108626 2501207 := bstep (se 1 (by rfl) ⟨1875905, by rfl⟩ : syracuseStep 2501207 = 3751811) B3751811
theorem B21670493 : Blo 1108626 21670493 := bstep (se 3 (by rfl) ⟨4063217, by rfl⟩ : syracuseStep 21670493 = 8126435) B8126435
theorem B2501387 : Blo 1108626 2501387 := bstep (se 1 (by rfl) ⟨1876040, by rfl⟩ : syracuseStep 2501387 = 3752081) B3752081
theorem B2501441 : Blo 1108626 2501441 := bstep (se 2 (by rfl) ⟨938040, by rfl⟩ : syracuseStep 2501441 = 1876081) B1876081
theorem B2370521 : Blo 1108626 2370521 := bstep (se 2 (by rfl) ⟨888945, by rfl⟩ : syracuseStep 2370521 = 1777891) B1777891
theorem B4008977 : Blo 1108626 4008977 := bstep (se 2 (by rfl) ⟨1503366, by rfl⟩ : syracuseStep 4008977 = 3006733) B3006733
theorem B3157015 : Blo 1108626 3157015 := bstep (se 1 (by rfl) ⟨2367761, by rfl⟩ : syracuseStep 3157015 = 4735523) B4735523
theorem B2501657 : Blo 1108626 2501657 := bstep (se 2 (by rfl) ⟨938121, by rfl⟩ : syracuseStep 2501657 = 1876243) B1876243
theorem B2501747 : Blo 1108626 2501747 := bstep (se 1 (by rfl) ⟨1876310, by rfl⟩ : syracuseStep 2501747 = 3752621) B3752621
theorem B4009105 : Blo 1108626 4009105 := bstep (se 2 (by rfl) ⟨1503414, by rfl⟩ : syracuseStep 4009105 = 3006829) B3006829
theorem B25996439 : Blo 1108626 25996439 := bstep (se 1 (by rfl) ⟨19497329, by rfl⟩ : syracuseStep 25996439 = 38994659) B38994659
theorem B2501783 : Blo 1108626 2501783 := bstep (se 1 (by rfl) ⟨1876337, by rfl⟩ : syracuseStep 2501783 = 3752675) B3752675
theorem B3288385 : Blo 1108626 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B2108747 : Blo 1108626 2108747 := bstep (se 1 (by rfl) ⟨1581560, by rfl⟩ : syracuseStep 2108747 = 3163121) B3163121
theorem B2501963 : Blo 1108626 2501963 := bstep (se 1 (by rfl) ⟨1876472, by rfl⟩ : syracuseStep 2501963 = 3752945) B3752945
theorem B2502017 : Blo 1108626 2502017 := bstep (se 2 (by rfl) ⟨938256, by rfl⟩ : syracuseStep 2502017 = 1876513) B1876513
theorem B3747275 : Blo 1108626 3747275 := bstep (se 1 (by rfl) ⟨2810456, by rfl⟩ : syracuseStep 3747275 = 5620913) B5620913
theorem B1781209 : Blo 1108626 1781209 := bstep (se 2 (by rfl) ⟨667953, by rfl⟩ : syracuseStep 1781209 = 1335907) B1335907
theorem B2108929 : Blo 1108626 2108929 := bstep (se 2 (by rfl) ⟨790848, by rfl⟩ : syracuseStep 2108929 = 1581697) B1581697
theorem B2502233 : Blo 1108626 2502233 := bstep (se 2 (by rfl) ⟨938337, by rfl⟩ : syracuseStep 2502233 = 1876675) B1876675
theorem B2371187 : Blo 1108626 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B2502323 : Blo 1108626 2502323 := bstep (se 1 (by rfl) ⟨1876742, by rfl⟩ : syracuseStep 2502323 = 3753485) B3753485
theorem B2502359 : Blo 1108626 2502359 := bstep (se 1 (by rfl) ⟨1876769, by rfl⟩ : syracuseStep 2502359 = 3753539) B3753539
theorem B2666201 : Blo 1108626 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B3747545 : Blo 1108626 3747545 := bstep (se 2 (by rfl) ⟨1405329, by rfl⟩ : syracuseStep 3747545 = 2810659) B2810659
theorem B5615405 : Blo 1108626 5615405 := bstep (se 3 (by rfl) ⟨1052888, by rfl⟩ : syracuseStep 5615405 = 2105777) B2105777
theorem B1126231 : Blo 1108626 1126231 := bstep (se 1 (by rfl) ⟨844673, by rfl⟩ : syracuseStep 1126231 = 1689347) B1689347
theorem B9613187 : Blo 1108626 9613187 := bstep (se 1 (by rfl) ⟨7209890, by rfl⟩ : syracuseStep 9613187 = 14419781) B14419781
theorem B2502539 : Blo 1108626 2502539 := bstep (se 1 (by rfl) ⟨1876904, by rfl⟩ : syracuseStep 2502539 = 3753809) B3753809
theorem B2109377 : Blo 1108626 2109377 := bstep (se 2 (by rfl) ⟨791016, by rfl⟩ : syracuseStep 2109377 = 1582033) B1582033
theorem B2502593 : Blo 1108626 2502593 := bstep (se 2 (by rfl) ⟨938472, by rfl⟩ : syracuseStep 2502593 = 1876945) B1876945
theorem B9482285 : Blo 1108626 9482285 := bstep (se 3 (by rfl) ⟨1777928, by rfl⟩ : syracuseStep 9482285 = 3555857) B3555857
theorem B2404439 : Blo 1108626 2404439 := bstep (se 1 (by rfl) ⟨1803329, by rfl⟩ : syracuseStep 2404439 = 3606659) B3606659
theorem B2535553 : Blo 1108626 2535553 := bstep (se 2 (by rfl) ⟨950832, by rfl⟩ : syracuseStep 2535553 = 1901665) B1901665
theorem B2502809 : Blo 1108626 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B28487861 : Blo 1108626 28487861 := bstep (se 5 (by rfl) ⟨1335368, by rfl⟩ : syracuseStep 28487861 = 2670737) B2670737
theorem B2601163 : Blo 1108626 2601163 := bstep (se 1 (by rfl) ⟨1950872, by rfl⟩ : syracuseStep 2601163 = 3901745) B3901745
theorem B2502899 : Blo 1108626 2502899 := bstep (se 1 (by rfl) ⟨1877174, by rfl⟩ : syracuseStep 2502899 = 3754349) B3754349
theorem B2109719 : Blo 1108626 2109719 := bstep (se 1 (by rfl) ⟨1582289, by rfl⟩ : syracuseStep 2109719 = 3164579) B3164579
theorem B2502935 : Blo 1108626 2502935 := bstep (se 1 (by rfl) ⟨1877201, by rfl⟩ : syracuseStep 2502935 = 3754403) B3754403
theorem B3158347 : Blo 1108626 3158347 := bstep (se 1 (by rfl) ⟨2368760, by rfl⟩ : syracuseStep 3158347 = 4737521) B4737521
theorem B6402397 : Blo 1108626 6402397 := bstep (se 3 (by rfl) ⟨1200449, by rfl⟩ : syracuseStep 6402397 = 2400899) B2400899
theorem B7123301 : Blo 1108626 7123301 := bstep (se 4 (by rfl) ⟨667809, by rfl⟩ : syracuseStep 7123301 = 1335619) B1335619
theorem B3748247 : Blo 1108626 3748247 := bstep (se 1 (by rfl) ⟨2811185, by rfl⟩ : syracuseStep 3748247 = 5622371) B5622371
theorem B3551681 : Blo 1108626 3551681 := bstep (se 2 (by rfl) ⟨1331880, by rfl⟩ : syracuseStep 3551681 = 2663761) B2663761
theorem B2503115 : Blo 1108626 2503115 := bstep (se 1 (by rfl) ⟨1877336, by rfl⟩ : syracuseStep 2503115 = 3754673) B3754673
theorem B2503169 : Blo 1108626 2503169 := bstep (se 2 (by rfl) ⟨938688, by rfl⟩ : syracuseStep 2503169 = 1877377) B1877377
theorem B3551809 : Blo 1108626 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B2372161 : Blo 1108626 2372161 := bstep (se 2 (by rfl) ⟨889560, by rfl⟩ : syracuseStep 2372161 = 1779121) B1779121
theorem B3158621 : Blo 1108626 3158621 := bstep (se 3 (by rfl) ⟨592241, by rfl⟩ : syracuseStep 3158621 = 1184483) B1184483
theorem B2503385 : Blo 1108626 2503385 := bstep (se 2 (by rfl) ⟨938769, by rfl⟩ : syracuseStep 2503385 = 1877539) B1877539
theorem B6402833 : Blo 1108626 6402833 := bstep (se 2 (by rfl) ⟨2401062, by rfl⟩ : syracuseStep 6402833 = 4802125) B4802125
theorem B3552065 : Blo 1108626 3552065 := bstep (se 2 (by rfl) ⟨1332024, by rfl⟩ : syracuseStep 3552065 = 2664049) B2664049
theorem B2372417 : Blo 1108626 2372417 := bstep (se 2 (by rfl) ⟨889656, by rfl⟩ : syracuseStep 2372417 = 1779313) B1779313
theorem B2372503 : Blo 1108626 2372503 := bstep (se 1 (by rfl) ⟨1779377, by rfl⟩ : syracuseStep 2372503 = 3558755) B3558755
theorem B3158963 : Blo 1108626 3158963 := bstep (se 1 (by rfl) ⟨2369222, by rfl⟩ : syracuseStep 3158963 = 4738445) B4738445
theorem B3748787 : Blo 1108626 3748787 := bstep (se 1 (by rfl) ⟨2811590, by rfl⟩ : syracuseStep 3748787 = 5623181) B5623181
theorem B2110387 : Blo 1108626 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B8991749 : Blo 1108626 8991749 := bstep (se 4 (by rfl) ⟨842976, by rfl⟩ : syracuseStep 8991749 = 1685953) B1685953
theorem B3749057 : Blo 1108626 3749057 := bstep (se 2 (by rfl) ⟨1405896, by rfl⟩ : syracuseStep 3749057 = 2811793) B2811793
theorem B2110835 : Blo 1108626 2110835 := bstep (se 1 (by rfl) ⟨1583126, by rfl⟩ : syracuseStep 2110835 = 3166253) B3166253
theorem B4502915 : Blo 1108626 4502915 := bstep (se 1 (by rfl) ⟨3377186, by rfl⟩ : syracuseStep 4502915 = 6754373) B6754373
theorem B38417813 : Blo 1108626 38417813 := bstep (se 6 (by rfl) ⟨900417, by rfl⟩ : syracuseStep 38417813 = 1800835) B1800835
theorem B2110873 : Blo 1108626 2110873 := bstep (se 2 (by rfl) ⟨791577, by rfl⟩ : syracuseStep 2110873 = 1583155) B1583155
theorem B102545027 : Blo 1108626 102545027 := bstep (se 1 (by rfl) ⟨76908770, by rfl⟩ : syracuseStep 102545027 = 153817541) B153817541
theorem B11417219 : Blo 1108626 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B3749597 : Blo 1108626 3749597 := bstep (se 3 (by rfl) ⟨703049, by rfl⟩ : syracuseStep 3749597 = 1406099) B1406099
theorem B8435501 : Blo 1108626 8435501 := bstep (se 3 (by rfl) ⟨1581656, by rfl⟩ : syracuseStep 8435501 = 3163313) B3163313
theorem B2111321 : Blo 1108626 2111321 := bstep (se 2 (by rfl) ⟨791745, by rfl⟩ : syracuseStep 2111321 = 1583491) B1583491
theorem B3553757 : Blo 1108626 3553757 := bstep (se 3 (by rfl) ⟨666329, by rfl⟩ : syracuseStep 3553757 = 1332659) B1332659
theorem B18987533 : Blo 1108626 18987533 := bstep (se 3 (by rfl) ⟨3560162, by rfl⟩ : syracuseStep 18987533 = 7120325) B7120325
theorem B2112065 : Blo 1108626 2112065 := bstep (se 2 (by rfl) ⟨792024, by rfl⟩ : syracuseStep 2112065 = 1584049) B1584049
theorem B8010571 : Blo 1108626 8010571 := bstep (se 1 (by rfl) ⟨6007928, by rfl⟩ : syracuseStep 8010571 = 12015857) B12015857
theorem B3750731 : Blo 1108626 3750731 := bstep (se 1 (by rfl) ⟨2813048, by rfl⟩ : syracuseStep 3750731 = 5626097) B5626097
theorem B3161035 : Blo 1108626 3161035 := bstep (se 1 (by rfl) ⟨2370776, by rfl⟩ : syracuseStep 3161035 = 4741553) B4741553
theorem B9485261 : Blo 1108626 9485261 := bstep (se 3 (by rfl) ⟨1778486, by rfl⟩ : syracuseStep 9485261 = 3556973) B3556973
theorem B3751001 : Blo 1108626 3751001 := bstep (se 2 (by rfl) ⟨1406625, by rfl⟩ : syracuseStep 3751001 = 2813251) B2813251
theorem B4504793 : Blo 1108626 4504793 := bstep (se 2 (by rfl) ⟨1689297, by rfl⟩ : syracuseStep 4504793 = 3378595) B3378595
theorem B3554525 : Blo 1108626 3554525 := bstep (se 3 (by rfl) ⟨666473, by rfl⟩ : syracuseStep 3554525 = 1332947) B1332947
theorem B4111667 : Blo 1108626 4111667 := bstep (se 1 (by rfl) ⟨3083750, by rfl⟩ : syracuseStep 4111667 = 6167501) B6167501
theorem B3161537 : Blo 1108626 3161537 := bstep (se 2 (by rfl) ⟨1185576, by rfl⟩ : syracuseStep 3161537 = 2371153) B2371153
theorem B2375219 : Blo 1108626 2375219 := bstep (se 1 (by rfl) ⟨1781414, by rfl⟩ : syracuseStep 2375219 = 3562829) B3562829
theorem B2440793 : Blo 1108626 2440793 := bstep (se 2 (by rfl) ⟨915297, by rfl⟩ : syracuseStep 2440793 = 1830595) B1830595
theorem B5619293 : Blo 1108626 5619293 := bstep (se 3 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 5619293 = 2107235) B2107235
theorem B2997911 : Blo 1108626 2997911 := bstep (se 1 (by rfl) ⟨2248433, by rfl⟩ : syracuseStep 2997911 = 4496867) B4496867
theorem B3555037 : Blo 1108626 3555037 := bstep (se 3 (by rfl) ⟨666569, by rfl⟩ : syracuseStep 3555037 = 1333139) B1333139
theorem B3161879 : Blo 1108626 3161879 := bstep (se 1 (by rfl) ⟨2371409, by rfl⟩ : syracuseStep 3161879 = 4742819) B4742819
theorem B3751703 : Blo 1108626 3751703 := bstep (se 1 (by rfl) ⟨2813777, by rfl⟩ : syracuseStep 3751703 = 5627555) B5627555
theorem B24035251 : Blo 1108626 24035251 := bstep (se 1 (by rfl) ⟨18026438, by rfl⟩ : syracuseStep 24035251 = 36052877) B36052877
theorem B5062787 : Blo 1108626 5062787 := bstep (se 1 (by rfl) ⟨3797090, by rfl⟩ : syracuseStep 5062787 = 7594181) B7594181
theorem B3752243 : Blo 1108626 3752243 := bstep (se 1 (by rfl) ⟨2814182, by rfl⟩ : syracuseStep 3752243 = 5628365) B5628365
theorem B3752513 : Blo 1108626 3752513 := bstep (se 2 (by rfl) ⟨1407192, by rfl⟩ : syracuseStep 3752513 = 2814385) B2814385
theorem B12665645 : Blo 1108626 12665645 := bstep (se 3 (by rfl) ⟨2374808, by rfl⟩ : syracuseStep 12665645 = 4749617) B4749617
theorem B5063555 : Blo 1108626 5063555 := bstep (se 1 (by rfl) ⟨3797666, by rfl⟩ : syracuseStep 5063555 = 7595333) B7595333
theorem B3753053 : Blo 1108626 3753053 := bstep (se 3 (by rfl) ⟨703697, by rfl⟩ : syracuseStep 3753053 = 1407395) B1407395
theorem B4212269 : Blo 1108626 4212269 := bstep (se 3 (by rfl) ⟨789800, by rfl⟩ : syracuseStep 4212269 = 1579601) B1579601
theorem B8439389 : Blo 1108626 8439389 := bstep (se 3 (by rfl) ⟨1582385, by rfl⟩ : syracuseStep 8439389 = 3164771) B3164771
theorem B26035843 : Blo 1108626 26035843 := bstep (se 1 (by rfl) ⟨19526882, by rfl⟩ : syracuseStep 26035843 = 39053765) B39053765
theorem B5621399 : Blo 1108626 5621399 := bstep (se 1 (by rfl) ⟨4216049, by rfl⟩ : syracuseStep 5621399 = 8432099) B8432099
theorem B2999987 : Blo 1108626 2999987 := bstep (se 1 (by rfl) ⟨2249990, by rfl⟩ : syracuseStep 2999987 = 4499981) B4499981
theorem B3163997 : Blo 1108626 3163997 := bstep (se 3 (by rfl) ⟨593249, by rfl⟩ : syracuseStep 3163997 = 1186499) B1186499
theorem B3164339 : Blo 1108626 3164339 := bstep (se 1 (by rfl) ⟨2373254, by rfl⟩ : syracuseStep 3164339 = 4746509) B4746509
theorem B20269237 : Blo 1108626 20269237 := bstep (se 5 (by rfl) ⟨950120, by rfl⟩ : syracuseStep 20269237 = 1900241) B1900241
theorem B2672833 : Blo 1108626 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B3754187 : Blo 1108626 3754187 := bstep (se 1 (by rfl) ⟨2815640, by rfl⟩ : syracuseStep 3754187 = 5631281) B5631281
theorem B4507907 : Blo 1108626 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B4213043 : Blo 1108626 4213043 := bstep (se 1 (by rfl) ⟨3159782, by rfl⟩ : syracuseStep 4213043 = 6319565) B6319565
theorem B4802905 : Blo 1108626 4802905 := bstep (se 2 (by rfl) ⟨1801089, by rfl⟩ : syracuseStep 4802905 = 3602179) B3602179
theorem B3754457 : Blo 1108626 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B3000883 : Blo 1108626 3000883 := bstep (se 1 (by rfl) ⟨2250662, by rfl⟩ : syracuseStep 3000883 = 4501325) B4501325
theorem B5065267 : Blo 1108626 5065267 := bstep (se 1 (by rfl) ⟨3798950, by rfl⟩ : syracuseStep 5065267 = 7597901) B7597901
theorem B3853145 : Blo 1108626 3853145 := bstep (se 2 (by rfl) ⟨1444929, by rfl⟩ : syracuseStep 3853145 = 2889859) B2889859
theorem B14207845 : Blo 1108626 14207845 := bstep (se 4 (by rfl) ⟨1331985, by rfl⟩ : syracuseStep 14207845 = 2663971) B2663971
theorem B26987701 : Blo 1108626 26987701 := bstep (se 5 (by rfl) ⟨1265048, by rfl⟩ : syracuseStep 26987701 = 2530097) B2530097
theorem B4738819 : Blo 1108626 4738819 := bstep (se 1 (by rfl) ⟨3554114, by rfl⟩ : syracuseStep 4738819 = 7108229) B7108229
theorem B4214531 : Blo 1108626 4214531 := bstep (se 1 (by rfl) ⟨3160898, by rfl⟩ : syracuseStep 4214531 = 6321797) B6321797
theorem B1691609 : Blo 1108626 1691609 := bstep (se 2 (by rfl) ⟨634353, by rfl⟩ : syracuseStep 1691609 = 1268707) B1268707
theorem B4739161 : Blo 1108626 4739161 := bstep (se 2 (by rfl) ⟨1777185, by rfl⟩ : syracuseStep 4739161 = 3554371) B3554371
theorem B4214987 : Blo 1108626 4214987 := bstep (se 1 (by rfl) ⟨3161240, by rfl⟩ : syracuseStep 4214987 = 6322481) B6322481
theorem B4215185 : Blo 1108626 4215185 := bstep (se 2 (by rfl) ⟨1580694, by rfl⟩ : syracuseStep 4215185 = 3161389) B3161389
theorem B3166685 : Blo 1108626 3166685 := bstep (se 3 (by rfl) ⟨593753, by rfl⟩ : syracuseStep 3166685 = 1187507) B1187507
theorem B3560087 : Blo 1108626 3560087 := bstep (se 1 (by rfl) ⟨2670065, by rfl⟩ : syracuseStep 3560087 = 5340131) B5340131
theorem B3166913 : Blo 1108626 3166913 := bstep (se 2 (by rfl) ⟨1187592, by rfl⟩ : syracuseStep 3166913 = 2375185) B2375185
theorem B17126261 : Blo 1108626 17126261 := bstep (se 5 (by rfl) ⟨802793, by rfl⟩ : syracuseStep 17126261 = 1605587) B1605587
theorem B12014513 : Blo 1108626 12014513 := bstep (se 2 (by rfl) ⟨4505442, by rfl⟩ : syracuseStep 12014513 = 9010885) B9010885
theorem B2806721 : Blo 1108626 2806721 := bstep (se 2 (by rfl) ⟨1052520, by rfl⟩ : syracuseStep 2806721 = 2105041) B2105041
theorem B3560395 : Blo 1108626 3560395 := bstep (se 1 (by rfl) ⟨2670296, by rfl⟩ : syracuseStep 3560395 = 5340593) B5340593
theorem B4740119 : Blo 1108626 4740119 := bstep (se 1 (by rfl) ⟨3555089, by rfl⟩ : syracuseStep 4740119 = 7110179) B7110179
theorem B3167255 : Blo 1108626 3167255 := bstep (se 1 (by rfl) ⟨2375441, by rfl⟩ : syracuseStep 3167255 = 4750883) B4750883
theorem B10277923 : Blo 1108626 10277923 := bstep (se 1 (by rfl) ⟨7708442, by rfl⟩ : syracuseStep 10277923 = 15416885) B15416885
theorem B3429427 : Blo 1108626 3429427 := bstep (se 1 (by rfl) ⟨2572070, by rfl⟩ : syracuseStep 3429427 = 5144141) B5144141
theorem B5624963 : Blo 1108626 5624963 := bstep (se 1 (by rfl) ⟨4218722, by rfl⟩ : syracuseStep 5624963 = 8437445) B8437445
theorem B4215959 : Blo 1108626 4215959 := bstep (se 1 (by rfl) ⟨3161969, by rfl⟩ : syracuseStep 4215959 = 6323939) B6323939
theorem B4216157 : Blo 1108626 4216157 := bstep (se 3 (by rfl) ⟨790529, by rfl⟩ : syracuseStep 4216157 = 1581059) B1581059
theorem B2807257 : Blo 1108626 2807257 := bstep (se 2 (by rfl) ⟨1052721, by rfl⟩ : syracuseStep 2807257 = 2105443) B2105443
theorem B97310321 : Blo 1108626 97310321 := bstep (se 2 (by rfl) ⟨36491370, by rfl⟩ : syracuseStep 97310321 = 72982741) B72982741
theorem B2250379 : Blo 1108626 2250379 := bstep (se 1 (by rfl) ⟨1687784, by rfl⟩ : syracuseStep 2250379 = 3375569) B3375569
theorem B10114739 : Blo 1108626 10114739 := bstep (se 1 (by rfl) ⟨7586054, by rfl⟩ : syracuseStep 10114739 = 15172109) B15172109
theorem B3004235 : Blo 1108626 3004235 := bstep (se 1 (by rfl) ⟨2253176, by rfl⟩ : syracuseStep 3004235 = 4506353) B4506353
theorem B2250841 : Blo 1108626 2250841 := bstep (se 2 (by rfl) ⟨844065, by rfl⟩ : syracuseStep 2250841 = 1688131) B1688131
theorem B24008885 : Blo 1108626 24008885 := bstep (se 5 (by rfl) ⟨1125416, by rfl⟩ : syracuseStep 24008885 = 2250833) B2250833
theorem B5134529 : Blo 1108626 5134529 := bstep (se 2 (by rfl) ⟨1925448, by rfl⟩ : syracuseStep 5134529 = 3850897) B3850897
theorem B2808371 : Blo 1108626 2808371 := bstep (se 1 (by rfl) ⟨2106278, by rfl⟩ : syracuseStep 2808371 = 4212557) B4212557
theorem B4741811 : Blo 1108626 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B3562163 : Blo 1108626 3562163 := bstep (se 1 (by rfl) ⟨2671622, by rfl⟩ : syracuseStep 3562163 = 5343245) B5343245
theorem B2808665 : Blo 1108626 2808665 := bstep (se 2 (by rfl) ⟨1053249, by rfl⟩ : syracuseStep 2808665 = 2106499) B2106499
theorem B4218115 : Blo 1108626 4218115 := bstep (se 1 (by rfl) ⟨3163586, by rfl⟩ : syracuseStep 4218115 = 6327173) B6327173
theorem B13491521 : Blo 1108626 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B4218419 : Blo 1108626 4218419 := bstep (se 1 (by rfl) ⟨3163814, by rfl⟩ : syracuseStep 4218419 = 6327629) B6327629
theorem B4808323 : Blo 1108626 4808323 := bstep (se 1 (by rfl) ⟨3606242, by rfl⟩ : syracuseStep 4808323 = 7212485) B7212485
theorem B3563443 : Blo 1108626 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B1663001 : Blo 1108626 1663001 := bstep (se 2 (by rfl) ⟨623625, by rfl⟩ : syracuseStep 1663001 = 1247251) B1247251
theorem B1663115 : Blo 1108626 1663115 := bstep (se 1 (by rfl) ⟨1247336, by rfl⟩ : syracuseStep 1663115 = 2494673) B2494673
theorem B1663127 : Blo 1108626 1663127 := bstep (se 1 (by rfl) ⟨1247345, by rfl⟩ : syracuseStep 1663127 = 2494691) B2494691
theorem B4219073 : Blo 1108626 4219073 := bstep (se 2 (by rfl) ⟨1582152, by rfl⟩ : syracuseStep 4219073 = 3164305) B3164305
theorem B1663193 : Blo 1108626 1663193 := bstep (se 2 (by rfl) ⟨623697, by rfl⟩ : syracuseStep 1663193 = 1247395) B1247395
theorem B1663307 : Blo 1108626 1663307 := bstep (se 1 (by rfl) ⟨1247480, by rfl⟩ : syracuseStep 1663307 = 2494961) B2494961
theorem B1663319 : Blo 1108626 1663319 := bstep (se 1 (by rfl) ⟨1247489, by rfl⟩ : syracuseStep 1663319 = 2494979) B2494979
theorem B1663385 : Blo 1108626 1663385 := bstep (se 2 (by rfl) ⟨623769, by rfl⟩ : syracuseStep 1663385 = 1247539) B1247539
theorem B10674611 : Blo 1108626 10674611 := bstep (se 1 (by rfl) ⟨8005958, by rfl⟩ : syracuseStep 10674611 = 16011917) B16011917
theorem B2810315 : Blo 1108626 2810315 := bstep (se 1 (by rfl) ⟨2107736, by rfl⟩ : syracuseStep 2810315 = 4215473) B4215473
theorem B1663499 : Blo 1108626 1663499 := bstep (se 1 (by rfl) ⟨1247624, by rfl⟩ : syracuseStep 1663499 = 2495249) B2495249
theorem B1663511 : Blo 1108626 1663511 := bstep (se 1 (by rfl) ⟨1247633, by rfl⟩ : syracuseStep 1663511 = 2495267) B2495267
theorem B3203659 : Blo 1108626 3203659 := bstep (se 1 (by rfl) ⟨2402744, by rfl⟩ : syracuseStep 3203659 = 4805489) B4805489
theorem B1663577 : Blo 1108626 1663577 := bstep (se 2 (by rfl) ⟨623841, by rfl⟩ : syracuseStep 1663577 = 1247683) B1247683
theorem B1663691 : Blo 1108626 1663691 := bstep (se 1 (by rfl) ⟨1247768, by rfl⟩ : syracuseStep 1663691 = 2495537) B2495537
theorem B1663703 : Blo 1108626 1663703 := bstep (se 1 (by rfl) ⟨1247777, by rfl⟩ : syracuseStep 1663703 = 2495555) B2495555
theorem B5628689 : Blo 1108626 5628689 := bstep (se 2 (by rfl) ⟨2110758, by rfl⟩ : syracuseStep 5628689 = 4221517) B4221517
theorem B1663769 : Blo 1108626 1663769 := bstep (se 2 (by rfl) ⟨623913, by rfl⟩ : syracuseStep 1663769 = 1247827) B1247827
theorem B10969901 : Blo 1108626 10969901 := bstep (se 3 (by rfl) ⟨2056856, by rfl⟩ : syracuseStep 10969901 = 4113713) B4113713
theorem B1663883 : Blo 1108626 1663883 := bstep (se 1 (by rfl) ⟨1247912, by rfl⟩ : syracuseStep 1663883 = 2495825) B2495825
theorem B1663895 : Blo 1108626 1663895 := bstep (se 1 (by rfl) ⟨1247921, by rfl⟩ : syracuseStep 1663895 = 2495843) B2495843
theorem B5628851 : Blo 1108626 5628851 := bstep (se 1 (by rfl) ⟨4221638, by rfl⟩ : syracuseStep 5628851 = 8443277) B8443277
theorem B1663961 : Blo 1108626 1663961 := bstep (se 2 (by rfl) ⟨623985, by rfl⟩ : syracuseStep 1663961 = 1247971) B1247971
theorem B1664075 : Blo 1108626 1664075 := bstep (se 1 (by rfl) ⟨1248056, by rfl⟩ : syracuseStep 1664075 = 2496113) B2496113
theorem B1664087 : Blo 1108626 1664087 := bstep (se 1 (by rfl) ⟨1248065, by rfl⟩ : syracuseStep 1664087 = 2496131) B2496131
theorem B6317149 : Blo 1108626 6317149 := bstep (se 3 (by rfl) ⟨1184465, by rfl⟩ : syracuseStep 6317149 = 2368931) B2368931
theorem B1664153 : Blo 1108626 1664153 := bstep (se 2 (by rfl) ⟨624057, by rfl⟩ : syracuseStep 1664153 = 1248115) B1248115
theorem B1664267 : Blo 1108626 1664267 := bstep (se 1 (by rfl) ⟨1248200, by rfl⟩ : syracuseStep 1664267 = 2496401) B2496401
theorem B1664279 : Blo 1108626 1664279 := bstep (se 1 (by rfl) ⟨1248209, by rfl⟩ : syracuseStep 1664279 = 2496419) B2496419
theorem B4744493 : Blo 1108626 4744493 := bstep (se 3 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 4744493 = 1779185) B1779185
theorem B1664345 : Blo 1108626 1664345 := bstep (se 2 (by rfl) ⟨624129, by rfl⟩ : syracuseStep 1664345 = 1248259) B1248259
theorem B2811287 : Blo 1108626 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B4220333 : Blo 1108626 4220333 := bstep (se 3 (by rfl) ⟨791312, by rfl⟩ : syracuseStep 4220333 = 1582625) B1582625
theorem B1664459 : Blo 1108626 1664459 := bstep (se 1 (by rfl) ⟨1248344, by rfl⟩ : syracuseStep 1664459 = 2496689) B2496689
theorem B4220363 : Blo 1108626 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B1664471 : Blo 1108626 1664471 := bstep (se 1 (by rfl) ⟨1248353, by rfl⟩ : syracuseStep 1664471 = 2496707) B2496707
theorem B6743569 : Blo 1108626 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B1664537 : Blo 1108626 1664537 := bstep (se 2 (by rfl) ⟨624201, by rfl⟩ : syracuseStep 1664537 = 1248403) B1248403
theorem B1664651 : Blo 1108626 1664651 := bstep (se 1 (by rfl) ⟨1248488, by rfl⟩ : syracuseStep 1664651 = 2496977) B2496977
theorem B1664663 : Blo 1108626 1664663 := bstep (se 1 (by rfl) ⟨1248497, by rfl⟩ : syracuseStep 1664663 = 2496995) B2496995
theorem B14247575 : Blo 1108626 14247575 := bstep (se 1 (by rfl) ⟨10685681, by rfl⟩ : syracuseStep 14247575 = 21371363) B21371363
theorem B5072563 : Blo 1108626 5072563 := bstep (se 1 (by rfl) ⟨3804422, by rfl⟩ : syracuseStep 5072563 = 7608845) B7608845
theorem B1664729 : Blo 1108626 1664729 := bstep (se 2 (by rfl) ⟨624273, by rfl⟩ : syracuseStep 1664729 = 1248547) B1248547
theorem B1664843 : Blo 1108626 1664843 := bstep (se 1 (by rfl) ⟨1248632, by rfl⟩ : syracuseStep 1664843 = 2497265) B2497265
theorem B1664855 : Blo 1108626 1664855 := bstep (se 1 (by rfl) ⟨1248641, by rfl⟩ : syracuseStep 1664855 = 2497283) B2497283
theorem B1664921 : Blo 1108626 1664921 := bstep (se 2 (by rfl) ⟨624345, by rfl⟩ : syracuseStep 1664921 = 1248691) B1248691
theorem B1665035 : Blo 1108626 1665035 := bstep (se 1 (by rfl) ⟨1248776, by rfl⟩ : syracuseStep 1665035 = 2497553) B2497553
theorem B1665047 : Blo 1108626 1665047 := bstep (se 1 (by rfl) ⟨1248785, by rfl⟩ : syracuseStep 1665047 = 2497571) B2497571
theorem B2811955 : Blo 1108626 2811955 := bstep (se 1 (by rfl) ⟨2108966, by rfl⟩ : syracuseStep 2811955 = 4217933) B4217933
theorem B1665113 : Blo 1108626 1665113 := bstep (se 2 (by rfl) ⟨624417, by rfl⟩ : syracuseStep 1665113 = 1248835) B1248835
theorem B4221017 : Blo 1108626 4221017 := bstep (se 2 (by rfl) ⟨1582881, by rfl⟩ : syracuseStep 4221017 = 3165763) B3165763
theorem B2812097 : Blo 1108626 2812097 := bstep (se 2 (by rfl) ⟨1054536, by rfl⟩ : syracuseStep 2812097 = 2109073) B2109073
theorem B1665227 : Blo 1108626 1665227 := bstep (se 1 (by rfl) ⟨1248920, by rfl⟩ : syracuseStep 1665227 = 2497841) B2497841
theorem B1665239 : Blo 1108626 1665239 := bstep (se 1 (by rfl) ⟨1248929, by rfl⟩ : syracuseStep 1665239 = 2497859) B2497859
theorem B1665305 : Blo 1108626 1665305 := bstep (se 2 (by rfl) ⟨624489, by rfl⟩ : syracuseStep 1665305 = 1248979) B1248979
theorem B1665419 : Blo 1108626 1665419 := bstep (se 1 (by rfl) ⟨1249064, by rfl⟩ : syracuseStep 1665419 = 2498129) B2498129
theorem B1665431 : Blo 1108626 1665431 := bstep (se 1 (by rfl) ⟨1249073, by rfl⟩ : syracuseStep 1665431 = 2498147) B2498147
theorem B4221335 : Blo 1108626 4221335 := bstep (se 1 (by rfl) ⟨3166001, by rfl⟩ : syracuseStep 4221335 = 6332003) B6332003
theorem B1665497 : Blo 1108626 1665497 := bstep (se 2 (by rfl) ⟨624561, by rfl⟩ : syracuseStep 1665497 = 1249123) B1249123
theorem B1665611 : Blo 1108626 1665611 := bstep (se 1 (by rfl) ⟨1249208, by rfl⟩ : syracuseStep 1665611 = 2498417) B2498417
theorem B1501771 : Blo 1108626 1501771 := bstep (se 1 (by rfl) ⟨1126328, by rfl⟩ : syracuseStep 1501771 = 2252657) B2252657
theorem B1665623 : Blo 1108626 1665623 := bstep (se 1 (by rfl) ⟨1249217, by rfl⟩ : syracuseStep 1665623 = 2498435) B2498435
theorem B2255447 : Blo 1108626 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B1108631 : Blo 1108626 1108631 := bstep (se 1 (by rfl) ⟨831473, by rfl⟩ : syracuseStep 1108631 = 1662947) B1662947
theorem B1665689 : Blo 1108626 1665689 := bstep (se 2 (by rfl) ⟨624633, by rfl⟩ : syracuseStep 1665689 = 1249267) B1249267
theorem B1108651 : Blo 1108626 1108651 := bstep (se 1 (by rfl) ⟨831488, by rfl⟩ : syracuseStep 1108651 = 1662977) B1662977
theorem B1108663 : Blo 1108626 1108663 := bstep (se 1 (by rfl) ⟨831497, by rfl⟩ : syracuseStep 1108663 = 1662995) B1662995
theorem B1108683 : Blo 1108626 1108683 := bstep (se 1 (by rfl) ⟨831512, by rfl⟩ : syracuseStep 1108683 = 1663025) B1663025
theorem B1108695 : Blo 1108626 1108695 := bstep (se 1 (by rfl) ⟨831521, by rfl⟩ : syracuseStep 1108695 = 1663043) B1663043
theorem B1108715 : Blo 1108626 1108715 := bstep (se 1 (by rfl) ⟨831536, by rfl⟩ : syracuseStep 1108715 = 1663073) B1663073
theorem B1108727 : Blo 1108626 1108727 := bstep (se 1 (by rfl) ⟨831545, by rfl⟩ : syracuseStep 1108727 = 1663091) B1663091
theorem B1108747 : Blo 1108626 1108747 := bstep (se 1 (by rfl) ⟨831560, by rfl⟩ : syracuseStep 1108747 = 1663121) B1663121
theorem B1403659 : Blo 1108626 1403659 := bstep (se 1 (by rfl) ⟨1052744, by rfl⟩ : syracuseStep 1403659 = 2105489) B2105489
theorem B1665803 : Blo 1108626 1665803 := bstep (se 1 (by rfl) ⟨1249352, by rfl⟩ : syracuseStep 1665803 = 2498705) B2498705
theorem B1108759 : Blo 1108626 1108759 := bstep (se 1 (by rfl) ⟨831569, by rfl⟩ : syracuseStep 1108759 = 1663139) B1663139
theorem B1665815 : Blo 1108626 1665815 := bstep (se 1 (by rfl) ⟨1249361, by rfl⟩ : syracuseStep 1665815 = 2498723) B2498723
theorem B1108779 : Blo 1108626 1108779 := bstep (se 1 (by rfl) ⟨831584, by rfl⟩ : syracuseStep 1108779 = 1663169) B1663169
theorem B1108791 : Blo 1108626 1108791 := bstep (se 1 (by rfl) ⟨831593, by rfl⟩ : syracuseStep 1108791 = 1663187) B1663187
theorem B1108811 : Blo 1108626 1108811 := bstep (se 1 (by rfl) ⟨831608, by rfl⟩ : syracuseStep 1108811 = 1663217) B1663217
theorem B5630795 : Blo 1108626 5630795 := bstep (se 1 (by rfl) ⟨4223096, by rfl⟩ : syracuseStep 5630795 = 8446193) B8446193
theorem B1108823 : Blo 1108626 1108823 := bstep (se 1 (by rfl) ⟨831617, by rfl⟩ : syracuseStep 1108823 = 1663235) B1663235
theorem B1665881 : Blo 1108626 1665881 := bstep (se 2 (by rfl) ⟨624705, by rfl⟩ : syracuseStep 1665881 = 1249411) B1249411
theorem B1108843 : Blo 1108626 1108843 := bstep (se 1 (by rfl) ⟨831632, by rfl⟩ : syracuseStep 1108843 = 1663265) B1663265
theorem B1108855 : Blo 1108626 1108855 := bstep (se 1 (by rfl) ⟨831641, by rfl⟩ : syracuseStep 1108855 = 1663283) B1663283
theorem B1108875 : Blo 1108626 1108875 := bstep (se 1 (by rfl) ⟨831656, by rfl⟩ : syracuseStep 1108875 = 1663313) B1663313
theorem B1108887 : Blo 1108626 1108887 := bstep (se 1 (by rfl) ⟨831665, by rfl⟩ : syracuseStep 1108887 = 1663331) B1663331
theorem B1108907 : Blo 1108626 1108907 := bstep (se 1 (by rfl) ⟨831680, by rfl⟩ : syracuseStep 1108907 = 1663361) B1663361
theorem B1108919 : Blo 1108626 1108919 := bstep (se 1 (by rfl) ⟨831689, by rfl⟩ : syracuseStep 1108919 = 1663379) B1663379
theorem B1108939 : Blo 1108626 1108939 := bstep (se 1 (by rfl) ⟨831704, by rfl⟩ : syracuseStep 1108939 = 1663409) B1663409
theorem B1665995 : Blo 1108626 1665995 := bstep (se 1 (by rfl) ⟨1249496, by rfl⟩ : syracuseStep 1665995 = 2498993) B2498993
theorem B1108951 : Blo 1108626 1108951 := bstep (se 1 (by rfl) ⟨831713, by rfl⟩ : syracuseStep 1108951 = 1663427) B1663427
theorem B1666007 : Blo 1108626 1666007 := bstep (se 1 (by rfl) ⟨1249505, by rfl⟩ : syracuseStep 1666007 = 2499011) B2499011
theorem B1108971 : Blo 1108626 1108971 := bstep (se 1 (by rfl) ⟨831728, by rfl⟩ : syracuseStep 1108971 = 1663457) B1663457
theorem B1108983 : Blo 1108626 1108983 := bstep (se 1 (by rfl) ⟨831737, by rfl⟩ : syracuseStep 1108983 = 1663475) B1663475
theorem B1109003 : Blo 1108626 1109003 := bstep (se 1 (by rfl) ⟨831752, by rfl⟩ : syracuseStep 1109003 = 1663505) B1663505
theorem B1109015 : Blo 1108626 1109015 := bstep (se 1 (by rfl) ⟨831761, by rfl⟩ : syracuseStep 1109015 = 1663523) B1663523
theorem B1666073 : Blo 1108626 1666073 := bstep (se 2 (by rfl) ⟨624777, by rfl⟩ : syracuseStep 1666073 = 1249555) B1249555
theorem B1109035 : Blo 1108626 1109035 := bstep (se 1 (by rfl) ⟨831776, by rfl⟩ : syracuseStep 1109035 = 1663553) B1663553
theorem B4222003 : Blo 1108626 4222003 := bstep (se 1 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 4222003 = 6333005) B6333005
theorem B1109047 : Blo 1108626 1109047 := bstep (se 1 (by rfl) ⟨831785, by rfl⟩ : syracuseStep 1109047 = 1663571) B1663571
theorem B1109067 : Blo 1108626 1109067 := bstep (se 1 (by rfl) ⟨831800, by rfl⟩ : syracuseStep 1109067 = 1663601) B1663601
theorem B1109079 : Blo 1108626 1109079 := bstep (se 1 (by rfl) ⟨831809, by rfl⟩ : syracuseStep 1109079 = 1663619) B1663619
theorem B1109099 : Blo 1108626 1109099 := bstep (se 1 (by rfl) ⟨831824, by rfl⟩ : syracuseStep 1109099 = 1663649) B1663649
theorem B1109111 : Blo 1108626 1109111 := bstep (se 1 (by rfl) ⟨831833, by rfl⟩ : syracuseStep 1109111 = 1663667) B1663667
theorem B1109131 : Blo 1108626 1109131 := bstep (se 1 (by rfl) ⟨831848, by rfl⟩ : syracuseStep 1109131 = 1663697) B1663697
theorem B1666187 : Blo 1108626 1666187 := bstep (se 1 (by rfl) ⟨1249640, by rfl⟩ : syracuseStep 1666187 = 2499281) B2499281
theorem B1109143 : Blo 1108626 1109143 := bstep (se 1 (by rfl) ⟨831857, by rfl⟩ : syracuseStep 1109143 = 1663715) B1663715
theorem B2845847 : Blo 1108626 2845847 := bstep (se 1 (by rfl) ⟨2134385, by rfl⟩ : syracuseStep 2845847 = 4268771) B4268771
theorem B1666199 : Blo 1108626 1666199 := bstep (se 1 (by rfl) ⟨1249649, by rfl⟩ : syracuseStep 1666199 = 2499299) B2499299
theorem B1109163 : Blo 1108626 1109163 := bstep (se 1 (by rfl) ⟨831872, by rfl⟩ : syracuseStep 1109163 = 1663745) B1663745
theorem B1109175 : Blo 1108626 1109175 := bstep (se 1 (by rfl) ⟨831881, by rfl⟩ : syracuseStep 1109175 = 1663763) B1663763
theorem B1109195 : Blo 1108626 1109195 := bstep (se 1 (by rfl) ⟨831896, by rfl⟩ : syracuseStep 1109195 = 1663793) B1663793
theorem B1109207 : Blo 1108626 1109207 := bstep (se 1 (by rfl) ⟨831905, by rfl⟩ : syracuseStep 1109207 = 1663811) B1663811
theorem B1666265 : Blo 1108626 1666265 := bstep (se 2 (by rfl) ⟨624849, by rfl⟩ : syracuseStep 1666265 = 1249699) B1249699
theorem B1109227 : Blo 1108626 1109227 := bstep (se 1 (by rfl) ⟨831920, by rfl⟩ : syracuseStep 1109227 = 1663841) B1663841
theorem B1109239 : Blo 1108626 1109239 := bstep (se 1 (by rfl) ⟨831929, by rfl⟩ : syracuseStep 1109239 = 1663859) B1663859
theorem B1109259 : Blo 1108626 1109259 := bstep (se 1 (by rfl) ⟨831944, by rfl⟩ : syracuseStep 1109259 = 1663889) B1663889
theorem B1109271 : Blo 1108626 1109271 := bstep (se 1 (by rfl) ⟨831953, by rfl⟩ : syracuseStep 1109271 = 1663907) B1663907
theorem B1109291 : Blo 1108626 1109291 := bstep (se 1 (by rfl) ⟨831968, by rfl⟩ : syracuseStep 1109291 = 1663937) B1663937
theorem B40496429 : Blo 1108626 40496429 := bstep (se 3 (by rfl) ⟨7593080, by rfl⟩ : syracuseStep 40496429 = 15186161) B15186161
theorem B1109303 : Blo 1108626 1109303 := bstep (se 1 (by rfl) ⟨831977, by rfl⟩ : syracuseStep 1109303 = 1663955) B1663955
theorem B1109323 : Blo 1108626 1109323 := bstep (se 1 (by rfl) ⟨831992, by rfl⟩ : syracuseStep 1109323 = 1663985) B1663985
theorem B1666379 : Blo 1108626 1666379 := bstep (se 1 (by rfl) ⟨1249784, by rfl⟩ : syracuseStep 1666379 = 2499569) B2499569
theorem B1109335 : Blo 1108626 1109335 := bstep (se 1 (by rfl) ⟨832001, by rfl⟩ : syracuseStep 1109335 = 1664003) B1664003
theorem B1666391 : Blo 1108626 1666391 := bstep (se 1 (by rfl) ⟨1249793, by rfl⟩ : syracuseStep 1666391 = 2499587) B2499587
theorem B1109355 : Blo 1108626 1109355 := bstep (se 1 (by rfl) ⟨832016, by rfl⟩ : syracuseStep 1109355 = 1664033) B1664033
theorem B1109367 : Blo 1108626 1109367 := bstep (se 1 (by rfl) ⟨832025, by rfl⟩ : syracuseStep 1109367 = 1664051) B1664051
theorem B1109387 : Blo 1108626 1109387 := bstep (se 1 (by rfl) ⟨832040, by rfl⟩ : syracuseStep 1109387 = 1664081) B1664081
theorem B1109399 : Blo 1108626 1109399 := bstep (se 1 (by rfl) ⟨832049, by rfl⟩ : syracuseStep 1109399 = 1664099) B1664099
theorem B1666457 : Blo 1108626 1666457 := bstep (se 2 (by rfl) ⟨624921, by rfl⟩ : syracuseStep 1666457 = 1249843) B1249843
theorem B1109419 : Blo 1108626 1109419 := bstep (se 1 (by rfl) ⟨832064, by rfl⟩ : syracuseStep 1109419 = 1664129) B1664129
theorem B2813363 : Blo 1108626 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B1109431 : Blo 1108626 1109431 := bstep (se 1 (by rfl) ⟨832073, by rfl⟩ : syracuseStep 1109431 = 1664147) B1664147
theorem B1109451 : Blo 1108626 1109451 := bstep (se 1 (by rfl) ⟨832088, by rfl⟩ : syracuseStep 1109451 = 1664177) B1664177
theorem B1109463 : Blo 1108626 1109463 := bstep (se 1 (by rfl) ⟨832097, by rfl⟩ : syracuseStep 1109463 = 1664195) B1664195
theorem B1109483 : Blo 1108626 1109483 := bstep (se 1 (by rfl) ⟨832112, by rfl⟩ : syracuseStep 1109483 = 1664225) B1664225
theorem B1109495 : Blo 1108626 1109495 := bstep (se 1 (by rfl) ⟨832121, by rfl⟩ : syracuseStep 1109495 = 1664243) B1664243
theorem B1109515 : Blo 1108626 1109515 := bstep (se 1 (by rfl) ⟨832136, by rfl⟩ : syracuseStep 1109515 = 1664273) B1664273
theorem B1666571 : Blo 1108626 1666571 := bstep (se 1 (by rfl) ⟨1249928, by rfl⟩ : syracuseStep 1666571 = 2499857) B2499857
theorem B1109527 : Blo 1108626 1109527 := bstep (se 1 (by rfl) ⟨832145, by rfl⟩ : syracuseStep 1109527 = 1664291) B1664291
theorem B1666583 : Blo 1108626 1666583 := bstep (se 1 (by rfl) ⟨1249937, by rfl⟩ : syracuseStep 1666583 = 2499875) B2499875
theorem B1109547 : Blo 1108626 1109547 := bstep (se 1 (by rfl) ⟨832160, by rfl⟩ : syracuseStep 1109547 = 1664321) B1664321
theorem B1109559 : Blo 1108626 1109559 := bstep (se 1 (by rfl) ⟨832169, by rfl⟩ : syracuseStep 1109559 = 1664339) B1664339
theorem B1109579 : Blo 1108626 1109579 := bstep (se 1 (by rfl) ⟨832184, by rfl⟩ : syracuseStep 1109579 = 1664369) B1664369
theorem B1109591 : Blo 1108626 1109591 := bstep (se 1 (by rfl) ⟨832193, by rfl⟩ : syracuseStep 1109591 = 1664387) B1664387
theorem B1666649 : Blo 1108626 1666649 := bstep (se 2 (by rfl) ⟨624993, by rfl⟩ : syracuseStep 1666649 = 1249987) B1249987
theorem B1109611 : Blo 1108626 1109611 := bstep (se 1 (by rfl) ⟨832208, by rfl⟩ : syracuseStep 1109611 = 1664417) B1664417
theorem B1109623 : Blo 1108626 1109623 := bstep (se 1 (by rfl) ⟨832217, by rfl⟩ : syracuseStep 1109623 = 1664435) B1664435
theorem B1109643 : Blo 1108626 1109643 := bstep (se 1 (by rfl) ⟨832232, by rfl⟩ : syracuseStep 1109643 = 1664465) B1664465
theorem B1109655 : Blo 1108626 1109655 := bstep (se 1 (by rfl) ⟨832241, by rfl⟩ : syracuseStep 1109655 = 1664483) B1664483
theorem B1109675 : Blo 1108626 1109675 := bstep (se 1 (by rfl) ⟨832256, by rfl⟩ : syracuseStep 1109675 = 1664513) B1664513
theorem B1109687 : Blo 1108626 1109687 := bstep (se 1 (by rfl) ⟨832265, by rfl⟩ : syracuseStep 1109687 = 1664531) B1664531
theorem B1109707 : Blo 1108626 1109707 := bstep (se 1 (by rfl) ⟨832280, by rfl⟩ : syracuseStep 1109707 = 1664561) B1664561
theorem B1666763 : Blo 1108626 1666763 := bstep (se 1 (by rfl) ⟨1250072, by rfl⟩ : syracuseStep 1666763 = 2500145) B2500145
theorem B1109719 : Blo 1108626 1109719 := bstep (se 1 (by rfl) ⟨832289, by rfl⟩ : syracuseStep 1109719 = 1664579) B1664579
theorem B1404631 : Blo 1108626 1404631 := bstep (se 1 (by rfl) ⟨1053473, by rfl⟩ : syracuseStep 1404631 = 2106947) B2106947
theorem B1666775 : Blo 1108626 1666775 := bstep (se 1 (by rfl) ⟨1250081, by rfl⟩ : syracuseStep 1666775 = 2500163) B2500163
theorem B1109739 : Blo 1108626 1109739 := bstep (se 1 (by rfl) ⟨832304, by rfl⟩ : syracuseStep 1109739 = 1664609) B1664609
theorem B1109751 : Blo 1108626 1109751 := bstep (se 1 (by rfl) ⟨832313, by rfl⟩ : syracuseStep 1109751 = 1664627) B1664627
theorem B1109771 : Blo 1108626 1109771 := bstep (se 1 (by rfl) ⟨832328, by rfl⟩ : syracuseStep 1109771 = 1664657) B1664657
theorem B1109783 : Blo 1108626 1109783 := bstep (se 1 (by rfl) ⟨832337, by rfl⟩ : syracuseStep 1109783 = 1664675) B1664675
theorem B1666841 : Blo 1108626 1666841 := bstep (se 2 (by rfl) ⟨625065, by rfl⟩ : syracuseStep 1666841 = 1250131) B1250131
theorem B1109803 : Blo 1108626 1109803 := bstep (se 1 (by rfl) ⟨832352, by rfl⟩ : syracuseStep 1109803 = 1664705) B1664705
theorem B1109815 : Blo 1108626 1109815 := bstep (se 1 (by rfl) ⟨832361, by rfl⟩ : syracuseStep 1109815 = 1664723) B1664723
theorem B1109835 : Blo 1108626 1109835 := bstep (se 1 (by rfl) ⟨832376, by rfl⟩ : syracuseStep 1109835 = 1664753) B1664753
theorem B1109847 : Blo 1108626 1109847 := bstep (se 1 (by rfl) ⟨832385, by rfl⟩ : syracuseStep 1109847 = 1664771) B1664771
theorem B1109867 : Blo 1108626 1109867 := bstep (se 1 (by rfl) ⟨832400, by rfl⟩ : syracuseStep 1109867 = 1664801) B1664801
theorem B1109879 : Blo 1108626 1109879 := bstep (se 1 (by rfl) ⟨832409, by rfl⟩ : syracuseStep 1109879 = 1664819) B1664819
theorem B1109899 : Blo 1108626 1109899 := bstep (se 1 (by rfl) ⟨832424, by rfl⟩ : syracuseStep 1109899 = 1664849) B1664849
theorem B1666955 : Blo 1108626 1666955 := bstep (se 1 (by rfl) ⟨1250216, by rfl⟩ : syracuseStep 1666955 = 2500433) B2500433
theorem B1109911 : Blo 1108626 1109911 := bstep (se 1 (by rfl) ⟨832433, by rfl⟩ : syracuseStep 1109911 = 1664867) B1664867
theorem B1666967 : Blo 1108626 1666967 := bstep (se 1 (by rfl) ⟨1250225, by rfl⟩ : syracuseStep 1666967 = 2500451) B2500451
theorem B1109931 : Blo 1108626 1109931 := bstep (se 1 (by rfl) ⟨832448, by rfl⟩ : syracuseStep 1109931 = 1664897) B1664897
theorem B1109943 : Blo 1108626 1109943 := bstep (se 1 (by rfl) ⟨832457, by rfl⟩ : syracuseStep 1109943 = 1664915) B1664915
theorem B1109963 : Blo 1108626 1109963 := bstep (se 1 (by rfl) ⟨832472, by rfl⟩ : syracuseStep 1109963 = 1664945) B1664945
theorem B2813899 : Blo 1108626 2813899 := bstep (se 1 (by rfl) ⟨2110424, by rfl⟩ : syracuseStep 2813899 = 4220849) B4220849
theorem B1109975 : Blo 1108626 1109975 := bstep (se 1 (by rfl) ⟨832481, by rfl⟩ : syracuseStep 1109975 = 1664963) B1664963
theorem B1667033 : Blo 1108626 1667033 := bstep (se 2 (by rfl) ⟨625137, by rfl⟩ : syracuseStep 1667033 = 1250275) B1250275
theorem B1109995 : Blo 1108626 1109995 := bstep (se 1 (by rfl) ⟨832496, by rfl⟩ : syracuseStep 1109995 = 1664993) B1664993
theorem B1110007 : Blo 1108626 1110007 := bstep (se 1 (by rfl) ⟨832505, by rfl⟩ : syracuseStep 1110007 = 1665011) B1665011
theorem B1110027 : Blo 1108626 1110027 := bstep (se 1 (by rfl) ⟨832520, by rfl⟩ : syracuseStep 1110027 = 1665041) B1665041
theorem B1110039 : Blo 1108626 1110039 := bstep (se 1 (by rfl) ⟨832529, by rfl⟩ : syracuseStep 1110039 = 1665059) B1665059
theorem B1110059 : Blo 1108626 1110059 := bstep (se 1 (by rfl) ⟨832544, by rfl⟩ : syracuseStep 1110059 = 1665089) B1665089
theorem B1110071 : Blo 1108626 1110071 := bstep (se 1 (by rfl) ⟨832553, by rfl⟩ : syracuseStep 1110071 = 1665107) B1665107
theorem B1110091 : Blo 1108626 1110091 := bstep (se 1 (by rfl) ⟨832568, by rfl⟩ : syracuseStep 1110091 = 1665137) B1665137
theorem B1667147 : Blo 1108626 1667147 := bstep (se 1 (by rfl) ⟨1250360, by rfl⟩ : syracuseStep 1667147 = 2500721) B2500721
theorem B1110103 : Blo 1108626 1110103 := bstep (se 1 (by rfl) ⟨832577, by rfl⟩ : syracuseStep 1110103 = 1665155) B1665155
theorem B1667159 : Blo 1108626 1667159 := bstep (se 1 (by rfl) ⟨1250369, by rfl⟩ : syracuseStep 1667159 = 2500739) B2500739
theorem B2814041 : Blo 1108626 2814041 := bstep (se 2 (by rfl) ⟨1055265, by rfl⟩ : syracuseStep 2814041 = 2110531) B2110531
theorem B1110123 : Blo 1108626 1110123 := bstep (se 1 (by rfl) ⟨832592, by rfl⟩ : syracuseStep 1110123 = 1665185) B1665185
theorem B1110135 : Blo 1108626 1110135 := bstep (se 1 (by rfl) ⟨832601, by rfl⟩ : syracuseStep 1110135 = 1665203) B1665203
theorem B1110155 : Blo 1108626 1110155 := bstep (se 1 (by rfl) ⟨832616, by rfl⟩ : syracuseStep 1110155 = 1665233) B1665233
theorem B1110167 : Blo 1108626 1110167 := bstep (se 1 (by rfl) ⟨832625, by rfl⟩ : syracuseStep 1110167 = 1665251) B1665251
theorem B1667225 : Blo 1108626 1667225 := bstep (se 2 (by rfl) ⟨625209, by rfl⟩ : syracuseStep 1667225 = 1250419) B1250419
theorem B1110187 : Blo 1108626 1110187 := bstep (se 1 (by rfl) ⟨832640, by rfl⟩ : syracuseStep 1110187 = 1665281) B1665281
theorem B1110199 : Blo 1108626 1110199 := bstep (se 1 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 1110199 = 1665299) B1665299
theorem B1110219 : Blo 1108626 1110219 := bstep (se 1 (by rfl) ⟨832664, by rfl⟩ : syracuseStep 1110219 = 1665329) B1665329
theorem B1110231 : Blo 1108626 1110231 := bstep (se 1 (by rfl) ⟨832673, by rfl⟩ : syracuseStep 1110231 = 1665347) B1665347
theorem B1110251 : Blo 1108626 1110251 := bstep (se 1 (by rfl) ⟨832688, by rfl⟩ : syracuseStep 1110251 = 1665377) B1665377
theorem B1110263 : Blo 1108626 1110263 := bstep (se 1 (by rfl) ⟨832697, by rfl⟩ : syracuseStep 1110263 = 1665395) B1665395
theorem B1110283 : Blo 1108626 1110283 := bstep (se 1 (by rfl) ⟨832712, by rfl⟩ : syracuseStep 1110283 = 1665425) B1665425
theorem B1667339 : Blo 1108626 1667339 := bstep (se 1 (by rfl) ⟨1250504, by rfl⟩ : syracuseStep 1667339 = 2501009) B2501009
theorem B4223249 : Blo 1108626 4223249 := bstep (se 2 (by rfl) ⟨1583718, by rfl⟩ : syracuseStep 4223249 = 3167437) B3167437
theorem B1110295 : Blo 1108626 1110295 := bstep (se 1 (by rfl) ⟨832721, by rfl⟩ : syracuseStep 1110295 = 1665443) B1665443
theorem B1667351 : Blo 1108626 1667351 := bstep (se 1 (by rfl) ⟨1250513, by rfl⟩ : syracuseStep 1667351 = 2501027) B2501027
theorem B1110315 : Blo 1108626 1110315 := bstep (se 1 (by rfl) ⟨832736, by rfl⟩ : syracuseStep 1110315 = 1665473) B1665473
theorem B1110327 : Blo 1108626 1110327 := bstep (se 1 (by rfl) ⟨832745, by rfl⟩ : syracuseStep 1110327 = 1665491) B1665491
theorem B1110347 : Blo 1108626 1110347 := bstep (se 1 (by rfl) ⟨832760, by rfl⟩ : syracuseStep 1110347 = 1665521) B1665521
theorem B1110359 : Blo 1108626 1110359 := bstep (se 1 (by rfl) ⟨832769, by rfl⟩ : syracuseStep 1110359 = 1665539) B1665539
theorem B1667417 : Blo 1108626 1667417 := bstep (se 2 (by rfl) ⟨625281, by rfl⟩ : syracuseStep 1667417 = 1250563) B1250563
theorem B1110379 : Blo 1108626 1110379 := bstep (se 1 (by rfl) ⟨832784, by rfl⟩ : syracuseStep 1110379 = 1665569) B1665569
theorem B1110391 : Blo 1108626 1110391 := bstep (se 1 (by rfl) ⟨832793, by rfl⟩ : syracuseStep 1110391 = 1665587) B1665587
theorem B1110411 : Blo 1108626 1110411 := bstep (se 1 (by rfl) ⟨832808, by rfl⟩ : syracuseStep 1110411 = 1665617) B1665617
theorem B1110423 : Blo 1108626 1110423 := bstep (se 1 (by rfl) ⟨832817, by rfl⟩ : syracuseStep 1110423 = 1665635) B1665635
theorem B9499031 : Blo 1108626 9499031 := bstep (se 1 (by rfl) ⟨7124273, by rfl⟩ : syracuseStep 9499031 = 14248547) B14248547
theorem B1110443 : Blo 1108626 1110443 := bstep (se 1 (by rfl) ⟨832832, by rfl⟩ : syracuseStep 1110443 = 1665665) B1665665
theorem B1110455 : Blo 1108626 1110455 := bstep (se 1 (by rfl) ⟨832841, by rfl⟩ : syracuseStep 1110455 = 1665683) B1665683
theorem B1667531 : Blo 1108626 1667531 := bstep (se 1 (by rfl) ⟨1250648, by rfl⟩ : syracuseStep 1667531 = 2501297) B2501297
theorem B1110475 : Blo 1108626 1110475 := bstep (se 1 (by rfl) ⟨832856, by rfl⟩ : syracuseStep 1110475 = 1665713) B1665713
theorem B1110487 : Blo 1108626 1110487 := bstep (se 1 (by rfl) ⟨832865, by rfl⟩ : syracuseStep 1110487 = 1665731) B1665731
theorem B1667543 : Blo 1108626 1667543 := bstep (se 1 (by rfl) ⟨1250657, by rfl⟩ : syracuseStep 1667543 = 2501315) B2501315
theorem B1110507 : Blo 1108626 1110507 := bstep (se 1 (by rfl) ⟨832880, by rfl⟩ : syracuseStep 1110507 = 1665761) B1665761
theorem B1110519 : Blo 1108626 1110519 := bstep (se 1 (by rfl) ⟨832889, by rfl⟩ : syracuseStep 1110519 = 1665779) B1665779
theorem B1405451 : Blo 1108626 1405451 := bstep (se 1 (by rfl) ⟨1054088, by rfl⟩ : syracuseStep 1405451 = 2108177) B2108177
theorem B1110539 : Blo 1108626 1110539 := bstep (se 1 (by rfl) ⟨832904, by rfl⟩ : syracuseStep 1110539 = 1665809) B1665809
theorem B1110551 : Blo 1108626 1110551 := bstep (se 1 (by rfl) ⟨832913, by rfl⟩ : syracuseStep 1110551 = 1665827) B1665827
theorem B1667609 : Blo 1108626 1667609 := bstep (se 2 (by rfl) ⟨625353, by rfl⟩ : syracuseStep 1667609 = 1250707) B1250707
theorem B1110571 : Blo 1108626 1110571 := bstep (se 1 (by rfl) ⟨832928, by rfl⟩ : syracuseStep 1110571 = 1665857) B1665857
theorem B10121773 : Blo 1108626 10121773 := bstep (se 3 (by rfl) ⟨1897832, by rfl⟩ : syracuseStep 10121773 = 3795665) B3795665
theorem B1110583 : Blo 1108626 1110583 := bstep (se 1 (by rfl) ⟨832937, by rfl⟩ : syracuseStep 1110583 = 1665875) B1665875
theorem B4747841 : Blo 1108626 4747841 := bstep (se 2 (by rfl) ⟨1780440, by rfl⟩ : syracuseStep 4747841 = 3560881) B3560881
theorem B5632577 : Blo 1108626 5632577 := bstep (se 2 (by rfl) ⟨2112216, by rfl⟩ : syracuseStep 5632577 = 4224433) B4224433
theorem B1110603 : Blo 1108626 1110603 := bstep (se 1 (by rfl) ⟨832952, by rfl⟩ : syracuseStep 1110603 = 1665905) B1665905
theorem B1110615 : Blo 1108626 1110615 := bstep (se 1 (by rfl) ⟨832961, by rfl⟩ : syracuseStep 1110615 = 1665923) B1665923
theorem B1110635 : Blo 1108626 1110635 := bstep (se 1 (by rfl) ⟨832976, by rfl⟩ : syracuseStep 1110635 = 1665953) B1665953
theorem B1110647 : Blo 1108626 1110647 := bstep (se 1 (by rfl) ⟨832985, by rfl⟩ : syracuseStep 1110647 = 1665971) B1665971
theorem B7107203 : Blo 1108626 7107203 := bstep (se 1 (by rfl) ⟨5330402, by rfl⟩ : syracuseStep 7107203 = 10660805) B10660805
theorem B1110667 : Blo 1108626 1110667 := bstep (se 1 (by rfl) ⟨833000, by rfl⟩ : syracuseStep 1110667 = 1666001) B1666001
theorem B1667723 : Blo 1108626 1667723 := bstep (se 1 (by rfl) ⟨1250792, by rfl⟩ : syracuseStep 1667723 = 2501585) B2501585
theorem B1110679 : Blo 1108626 1110679 := bstep (se 1 (by rfl) ⟨833009, by rfl⟩ : syracuseStep 1110679 = 1666019) B1666019
theorem B1667735 : Blo 1108626 1667735 := bstep (se 1 (by rfl) ⟨1250801, by rfl⟩ : syracuseStep 1667735 = 2501603) B2501603
theorem B1110699 : Blo 1108626 1110699 := bstep (se 1 (by rfl) ⟨833024, by rfl⟩ : syracuseStep 1110699 = 1666049) B1666049
theorem B1110711 : Blo 1108626 1110711 := bstep (se 1 (by rfl) ⟨833033, by rfl⟩ : syracuseStep 1110711 = 1666067) B1666067
theorem B1110731 : Blo 1108626 1110731 := bstep (se 1 (by rfl) ⟨833048, by rfl⟩ : syracuseStep 1110731 = 1666097) B1666097
theorem B1110743 : Blo 1108626 1110743 := bstep (se 1 (by rfl) ⟨833057, by rfl⟩ : syracuseStep 1110743 = 1666115) B1666115
theorem B1667801 : Blo 1108626 1667801 := bstep (se 2 (by rfl) ⟨625425, by rfl⟩ : syracuseStep 1667801 = 1250851) B1250851
theorem B1110763 : Blo 1108626 1110763 := bstep (se 1 (by rfl) ⟨833072, by rfl⟩ : syracuseStep 1110763 = 1666145) B1666145
theorem B1110775 : Blo 1108626 1110775 := bstep (se 1 (by rfl) ⟨833081, by rfl⟩ : syracuseStep 1110775 = 1666163) B1666163
theorem B1110795 : Blo 1108626 1110795 := bstep (se 1 (by rfl) ⟨833096, by rfl⟩ : syracuseStep 1110795 = 1666193) B1666193
theorem B1110807 : Blo 1108626 1110807 := bstep (se 1 (by rfl) ⟨833105, by rfl⟩ : syracuseStep 1110807 = 1666211) B1666211
theorem B1110827 : Blo 1108626 1110827 := bstep (se 1 (by rfl) ⟨833120, by rfl⟩ : syracuseStep 1110827 = 1666241) B1666241
theorem B1110839 : Blo 1108626 1110839 := bstep (se 1 (by rfl) ⟨833129, by rfl⟩ : syracuseStep 1110839 = 1666259) B1666259
theorem B1110859 : Blo 1108626 1110859 := bstep (se 1 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 1110859 = 1666289) B1666289
theorem B1667915 : Blo 1108626 1667915 := bstep (se 1 (by rfl) ⟨1250936, by rfl⟩ : syracuseStep 1667915 = 2501873) B2501873
theorem B1110871 : Blo 1108626 1110871 := bstep (se 1 (by rfl) ⟨833153, by rfl⟩ : syracuseStep 1110871 = 1666307) B1666307
theorem B1667927 : Blo 1108626 1667927 := bstep (se 1 (by rfl) ⟨1250945, by rfl⟩ : syracuseStep 1667927 = 2501891) B2501891
theorem B1110891 : Blo 1108626 1110891 := bstep (se 1 (by rfl) ⟨833168, by rfl⟩ : syracuseStep 1110891 = 1666337) B1666337
theorem B1110903 : Blo 1108626 1110903 := bstep (se 1 (by rfl) ⟨833177, by rfl⟩ : syracuseStep 1110903 = 1666355) B1666355
theorem B1110923 : Blo 1108626 1110923 := bstep (se 1 (by rfl) ⟨833192, by rfl⟩ : syracuseStep 1110923 = 1666385) B1666385
theorem B1110935 : Blo 1108626 1110935 := bstep (se 1 (by rfl) ⟨833201, by rfl⟩ : syracuseStep 1110935 = 1666403) B1666403
theorem B4748183 : Blo 1108626 4748183 := bstep (se 1 (by rfl) ⟨3561137, by rfl⟩ : syracuseStep 4748183 = 7122275) B7122275
theorem B1667993 : Blo 1108626 1667993 := bstep (se 2 (by rfl) ⟨625497, by rfl⟩ : syracuseStep 1667993 = 1250995) B1250995
theorem B2814871 : Blo 1108626 2814871 := bstep (se 1 (by rfl) ⟨2111153, by rfl⟩ : syracuseStep 2814871 = 4222307) B4222307
theorem B1110955 : Blo 1108626 1110955 := bstep (se 1 (by rfl) ⟨833216, by rfl⟩ : syracuseStep 1110955 = 1666433) B1666433
theorem B17986481 : Blo 1108626 17986481 := bstep (se 2 (by rfl) ⟨6744930, by rfl⟩ : syracuseStep 17986481 = 13489861) B13489861
theorem B1110967 : Blo 1108626 1110967 := bstep (se 1 (by rfl) ⟨833225, by rfl⟩ : syracuseStep 1110967 = 1666451) B1666451
theorem B1110987 : Blo 1108626 1110987 := bstep (se 1 (by rfl) ⟨833240, by rfl⟩ : syracuseStep 1110987 = 1666481) B1666481
theorem B4223947 : Blo 1108626 4223947 := bstep (se 1 (by rfl) ⟨3167960, by rfl⟩ : syracuseStep 4223947 = 6335921) B6335921
theorem B1110999 : Blo 1108626 1110999 := bstep (se 1 (by rfl) ⟨833249, by rfl⟩ : syracuseStep 1110999 = 1666499) B1666499
theorem B1111019 : Blo 1108626 1111019 := bstep (se 1 (by rfl) ⟨833264, by rfl⟩ : syracuseStep 1111019 = 1666529) B1666529
theorem B1111031 : Blo 1108626 1111031 := bstep (se 1 (by rfl) ⟨833273, by rfl⟩ : syracuseStep 1111031 = 1666547) B1666547
theorem B1111051 : Blo 1108626 1111051 := bstep (se 1 (by rfl) ⟨833288, by rfl⟩ : syracuseStep 1111051 = 1666577) B1666577
theorem B1668107 : Blo 1108626 1668107 := bstep (se 1 (by rfl) ⟨1251080, by rfl⟩ : syracuseStep 1668107 = 2502161) B2502161
theorem B1111063 : Blo 1108626 1111063 := bstep (se 1 (by rfl) ⟨833297, by rfl⟩ : syracuseStep 1111063 = 1666595) B1666595
theorem B1668119 : Blo 1108626 1668119 := bstep (se 1 (by rfl) ⟨1251089, by rfl⟩ : syracuseStep 1668119 = 2502179) B2502179
theorem B1111083 : Blo 1108626 1111083 := bstep (se 1 (by rfl) ⟨833312, by rfl⟩ : syracuseStep 1111083 = 1666625) B1666625
theorem B4060211 : Blo 1108626 4060211 := bstep (se 1 (by rfl) ⟨3045158, by rfl⟩ : syracuseStep 4060211 = 6090317) B6090317
theorem B1111095 : Blo 1108626 1111095 := bstep (se 1 (by rfl) ⟨833321, by rfl⟩ : syracuseStep 1111095 = 1666643) B1666643
theorem B1111115 : Blo 1108626 1111115 := bstep (se 1 (by rfl) ⟨833336, by rfl⟩ : syracuseStep 1111115 = 1666673) B1666673
theorem B1111127 : Blo 1108626 1111127 := bstep (se 1 (by rfl) ⟨833345, by rfl⟩ : syracuseStep 1111127 = 1666691) B1666691
theorem B1668185 : Blo 1108626 1668185 := bstep (se 2 (by rfl) ⟨625569, by rfl⟩ : syracuseStep 1668185 = 1251139) B1251139
theorem B1111147 : Blo 1108626 1111147 := bstep (se 1 (by rfl) ⟨833360, by rfl⟩ : syracuseStep 1111147 = 1666721) B1666721
theorem B1111159 : Blo 1108626 1111159 := bstep (se 1 (by rfl) ⟨833369, by rfl⟩ : syracuseStep 1111159 = 1666739) B1666739
theorem B1111179 : Blo 1108626 1111179 := bstep (se 1 (by rfl) ⟨833384, by rfl⟩ : syracuseStep 1111179 = 1666769) B1666769
theorem B1111191 : Blo 1108626 1111191 := bstep (se 1 (by rfl) ⟨833393, by rfl⟩ : syracuseStep 1111191 = 1666787) B1666787
theorem B1111211 : Blo 1108626 1111211 := bstep (se 1 (by rfl) ⟨833408, by rfl⟩ : syracuseStep 1111211 = 1666817) B1666817
theorem B61600949 : Blo 1108626 61600949 := bstep (se 5 (by rfl) ⟨2887544, by rfl⟩ : syracuseStep 61600949 = 5775089) B5775089
theorem B1111223 : Blo 1108626 1111223 := bstep (se 1 (by rfl) ⟨833417, by rfl⟩ : syracuseStep 1111223 = 1666835) B1666835
theorem B1406155 : Blo 1108626 1406155 := bstep (se 1 (by rfl) ⟨1054616, by rfl⟩ : syracuseStep 1406155 = 2109233) B2109233
theorem B1111243 : Blo 1108626 1111243 := bstep (se 1 (by rfl) ⟨833432, by rfl⟩ : syracuseStep 1111243 = 1666865) B1666865
theorem B1668299 : Blo 1108626 1668299 := bstep (se 1 (by rfl) ⟨1251224, by rfl⟩ : syracuseStep 1668299 = 2502449) B2502449
theorem B1111255 : Blo 1108626 1111255 := bstep (se 1 (by rfl) ⟨833441, by rfl⟩ : syracuseStep 1111255 = 1666883) B1666883
theorem B1668311 : Blo 1108626 1668311 := bstep (se 1 (by rfl) ⟨1251233, by rfl⟩ : syracuseStep 1668311 = 2502467) B2502467
theorem B4224221 : Blo 1108626 4224221 := bstep (se 3 (by rfl) ⟨792041, by rfl⟩ : syracuseStep 4224221 = 1584083) B1584083
theorem B1111275 : Blo 1108626 1111275 := bstep (se 1 (by rfl) ⟨833456, by rfl⟩ : syracuseStep 1111275 = 1666913) B1666913
theorem B1111287 : Blo 1108626 1111287 := bstep (se 1 (by rfl) ⟨833465, by rfl⟩ : syracuseStep 1111287 = 1666931) B1666931
theorem B1111307 : Blo 1108626 1111307 := bstep (se 1 (by rfl) ⟨833480, by rfl⟩ : syracuseStep 1111307 = 1666961) B1666961
theorem B1111319 : Blo 1108626 1111319 := bstep (se 1 (by rfl) ⟨833489, by rfl⟩ : syracuseStep 1111319 = 1666979) B1666979
theorem B1668377 : Blo 1108626 1668377 := bstep (se 2 (by rfl) ⟨625641, by rfl⟩ : syracuseStep 1668377 = 1251283) B1251283
theorem B1111339 : Blo 1108626 1111339 := bstep (se 1 (by rfl) ⟨833504, by rfl⟩ : syracuseStep 1111339 = 1667009) B1667009
theorem B1111351 : Blo 1108626 1111351 := bstep (se 1 (by rfl) ⟨833513, by rfl⟩ : syracuseStep 1111351 = 1667027) B1667027
theorem B1111371 : Blo 1108626 1111371 := bstep (se 1 (by rfl) ⟨833528, by rfl⟩ : syracuseStep 1111371 = 1667057) B1667057
theorem B2815307 : Blo 1108626 2815307 := bstep (se 1 (by rfl) ⟨2111480, by rfl⟩ : syracuseStep 2815307 = 4222961) B4222961
theorem B1111383 : Blo 1108626 1111383 := bstep (se 1 (by rfl) ⟨833537, by rfl⟩ : syracuseStep 1111383 = 1667075) B1667075
theorem B1111403 : Blo 1108626 1111403 := bstep (se 1 (by rfl) ⟨833552, by rfl⟩ : syracuseStep 1111403 = 1667105) B1667105
theorem B1111415 : Blo 1108626 1111415 := bstep (se 1 (by rfl) ⟨833561, by rfl⟩ : syracuseStep 1111415 = 1667123) B1667123
theorem B1111435 : Blo 1108626 1111435 := bstep (se 1 (by rfl) ⟨833576, by rfl⟩ : syracuseStep 1111435 = 1667153) B1667153
theorem B1668491 : Blo 1108626 1668491 := bstep (se 1 (by rfl) ⟨1251368, by rfl⟩ : syracuseStep 1668491 = 2502737) B2502737
theorem B1111447 : Blo 1108626 1111447 := bstep (se 1 (by rfl) ⟨833585, by rfl⟩ : syracuseStep 1111447 = 1667171) B1667171
theorem B1668503 : Blo 1108626 1668503 := bstep (se 1 (by rfl) ⟨1251377, by rfl⟩ : syracuseStep 1668503 = 2502755) B2502755
theorem B1111467 : Blo 1108626 1111467 := bstep (se 1 (by rfl) ⟨833600, by rfl⟩ : syracuseStep 1111467 = 1667201) B1667201
theorem B2028979 : Blo 1108626 2028979 := bstep (se 1 (by rfl) ⟨1521734, by rfl⟩ : syracuseStep 2028979 = 3043469) B3043469
theorem B1111479 : Blo 1108626 1111479 := bstep (se 1 (by rfl) ⟨833609, by rfl⟩ : syracuseStep 1111479 = 1667219) B1667219
theorem B1111499 : Blo 1108626 1111499 := bstep (se 1 (by rfl) ⟨833624, by rfl⟩ : syracuseStep 1111499 = 1667249) B1667249
theorem B1406423 : Blo 1108626 1406423 := bstep (se 1 (by rfl) ⟨1054817, by rfl⟩ : syracuseStep 1406423 = 2109635) B2109635
theorem B1111511 : Blo 1108626 1111511 := bstep (se 1 (by rfl) ⟨833633, by rfl⟩ : syracuseStep 1111511 = 1667267) B1667267
theorem B1668569 : Blo 1108626 1668569 := bstep (se 2 (by rfl) ⟨625713, by rfl⟩ : syracuseStep 1668569 = 1251427) B1251427
theorem B1111531 : Blo 1108626 1111531 := bstep (se 1 (by rfl) ⟨833648, by rfl⟩ : syracuseStep 1111531 = 1667297) B1667297
theorem B1111543 : Blo 1108626 1111543 := bstep (se 1 (by rfl) ⟨833657, by rfl⟩ : syracuseStep 1111543 = 1667315) B1667315
theorem B1111563 : Blo 1108626 1111563 := bstep (se 1 (by rfl) ⟨833672, by rfl⟩ : syracuseStep 1111563 = 1667345) B1667345
theorem B1111575 : Blo 1108626 1111575 := bstep (se 1 (by rfl) ⟨833681, by rfl⟩ : syracuseStep 1111575 = 1667363) B1667363
theorem B1111595 : Blo 1108626 1111595 := bstep (se 1 (by rfl) ⟨833696, by rfl⟩ : syracuseStep 1111595 = 1667393) B1667393
theorem B1111607 : Blo 1108626 1111607 := bstep (se 1 (by rfl) ⟨833705, by rfl⟩ : syracuseStep 1111607 = 1667411) B1667411
theorem B1111627 : Blo 1108626 1111627 := bstep (se 1 (by rfl) ⟨833720, by rfl⟩ : syracuseStep 1111627 = 1667441) B1667441
theorem B1668683 : Blo 1108626 1668683 := bstep (se 1 (by rfl) ⟨1251512, by rfl⟩ : syracuseStep 1668683 = 2503025) B2503025
theorem B1111639 : Blo 1108626 1111639 := bstep (se 1 (by rfl) ⟨833729, by rfl⟩ : syracuseStep 1111639 = 1667459) B1667459
theorem B1668695 : Blo 1108626 1668695 := bstep (se 1 (by rfl) ⟨1251521, by rfl⟩ : syracuseStep 1668695 = 2503043) B2503043
theorem B1111659 : Blo 1108626 1111659 := bstep (se 1 (by rfl) ⟨833744, by rfl⟩ : syracuseStep 1111659 = 1667489) B1667489
theorem B89028209 : Blo 1108626 89028209 := bstep (se 2 (by rfl) ⟨33385578, by rfl⟩ : syracuseStep 89028209 = 66771157) B66771157
theorem B1111671 : Blo 1108626 1111671 := bstep (se 1 (by rfl) ⟨833753, by rfl⟩ : syracuseStep 1111671 = 1667507) B1667507
theorem B1111691 : Blo 1108626 1111691 := bstep (se 1 (by rfl) ⟨833768, by rfl⟩ : syracuseStep 1111691 = 1667537) B1667537
theorem B1111703 : Blo 1108626 1111703 := bstep (se 1 (by rfl) ⟨833777, by rfl⟩ : syracuseStep 1111703 = 1667555) B1667555
theorem B1668761 : Blo 1108626 1668761 := bstep (se 2 (by rfl) ⟨625785, by rfl⟩ : syracuseStep 1668761 = 1251571) B1251571
theorem B1111723 : Blo 1108626 1111723 := bstep (se 1 (by rfl) ⟨833792, by rfl⟩ : syracuseStep 1111723 = 1667585) B1667585
theorem B1111735 : Blo 1108626 1111735 := bstep (se 1 (by rfl) ⟨833801, by rfl⟩ : syracuseStep 1111735 = 1667603) B1667603
theorem B2815681 : Blo 1108626 2815681 := bstep (se 2 (by rfl) ⟨1055880, by rfl⟩ : syracuseStep 2815681 = 2111761) B2111761
theorem B1111755 : Blo 1108626 1111755 := bstep (se 1 (by rfl) ⟨833816, by rfl⟩ : syracuseStep 1111755 = 1667633) B1667633
theorem B1111767 : Blo 1108626 1111767 := bstep (se 1 (by rfl) ⟨833825, by rfl⟩ : syracuseStep 1111767 = 1667651) B1667651
theorem B1111787 : Blo 1108626 1111787 := bstep (se 1 (by rfl) ⟨833840, by rfl⟩ : syracuseStep 1111787 = 1667681) B1667681
theorem B1111799 : Blo 1108626 1111799 := bstep (se 1 (by rfl) ⟨833849, by rfl⟩ : syracuseStep 1111799 = 1667699) B1667699
theorem B1111819 : Blo 1108626 1111819 := bstep (se 1 (by rfl) ⟨833864, by rfl⟩ : syracuseStep 1111819 = 1667729) B1667729
theorem B1668875 : Blo 1108626 1668875 := bstep (se 1 (by rfl) ⟨1251656, by rfl⟩ : syracuseStep 1668875 = 2503313) B2503313
theorem B1111831 : Blo 1108626 1111831 := bstep (se 1 (by rfl) ⟨833873, by rfl⟩ : syracuseStep 1111831 = 1667747) B1667747
theorem B1668887 : Blo 1108626 1668887 := bstep (se 1 (by rfl) ⟨1251665, by rfl⟩ : syracuseStep 1668887 = 2503331) B2503331
theorem B1111851 : Blo 1108626 1111851 := bstep (se 1 (by rfl) ⟨833888, by rfl⟩ : syracuseStep 1111851 = 1667777) B1667777
theorem B1111863 : Blo 1108626 1111863 := bstep (se 1 (by rfl) ⟨833897, by rfl⟩ : syracuseStep 1111863 = 1667795) B1667795
theorem B1111883 : Blo 1108626 1111883 := bstep (se 1 (by rfl) ⟨833912, by rfl⟩ : syracuseStep 1111883 = 1667825) B1667825
theorem B1111895 : Blo 1108626 1111895 := bstep (se 1 (by rfl) ⟨833921, by rfl⟩ : syracuseStep 1111895 = 1667843) B1667843
theorem B13006693 : Blo 1108626 13006693 := bstep (se 4 (by rfl) ⟨1219377, by rfl⟩ : syracuseStep 13006693 = 2438755) B2438755
theorem B1111915 : Blo 1108626 1111915 := bstep (se 1 (by rfl) ⟨833936, by rfl⟩ : syracuseStep 1111915 = 1667873) B1667873
theorem B1111927 : Blo 1108626 1111927 := bstep (se 1 (by rfl) ⟨833945, by rfl⟩ : syracuseStep 1111927 = 1667891) B1667891
theorem B1111947 : Blo 1108626 1111947 := bstep (se 1 (by rfl) ⟨833960, by rfl⟩ : syracuseStep 1111947 = 1667921) B1667921
theorem B1111959 : Blo 1108626 1111959 := bstep (se 1 (by rfl) ⟨833969, by rfl⟩ : syracuseStep 1111959 = 1667939) B1667939
theorem B1111979 : Blo 1108626 1111979 := bstep (se 1 (by rfl) ⟨833984, by rfl⟩ : syracuseStep 1111979 = 1667969) B1667969
theorem B1111991 : Blo 1108626 1111991 := bstep (se 1 (by rfl) ⟨833993, by rfl⟩ : syracuseStep 1111991 = 1667987) B1667987
theorem B1112011 : Blo 1108626 1112011 := bstep (se 1 (by rfl) ⟨834008, by rfl⟩ : syracuseStep 1112011 = 1668017) B1668017
theorem B1112023 : Blo 1108626 1112023 := bstep (se 1 (by rfl) ⟨834017, by rfl⟩ : syracuseStep 1112023 = 1668035) B1668035
theorem B1112043 : Blo 1108626 1112043 := bstep (se 1 (by rfl) ⟨834032, by rfl⟩ : syracuseStep 1112043 = 1668065) B1668065
theorem B1112055 : Blo 1108626 1112055 := bstep (se 1 (by rfl) ⟨834041, by rfl⟩ : syracuseStep 1112055 = 1668083) B1668083
theorem B1112075 : Blo 1108626 1112075 := bstep (se 1 (by rfl) ⟨834056, by rfl⟩ : syracuseStep 1112075 = 1668113) B1668113
theorem B1112087 : Blo 1108626 1112087 := bstep (se 1 (by rfl) ⟨834065, by rfl⟩ : syracuseStep 1112087 = 1668131) B1668131
theorem B1112107 : Blo 1108626 1112107 := bstep (se 1 (by rfl) ⟨834080, by rfl⟩ : syracuseStep 1112107 = 1668161) B1668161
theorem B1112119 : Blo 1108626 1112119 := bstep (se 1 (by rfl) ⟨834089, by rfl⟩ : syracuseStep 1112119 = 1668179) B1668179
theorem B3799115 : Blo 1108626 3799115 := bstep (se 1 (by rfl) ⟨2849336, by rfl⟩ : syracuseStep 3799115 = 5698673) B5698673
theorem B1112139 : Blo 1108626 1112139 := bstep (se 1 (by rfl) ⟨834104, by rfl⟩ : syracuseStep 1112139 = 1668209) B1668209
theorem B1112151 : Blo 1108626 1112151 := bstep (se 1 (by rfl) ⟨834113, by rfl⟩ : syracuseStep 1112151 = 1668227) B1668227
theorem B1112171 : Blo 1108626 1112171 := bstep (se 1 (by rfl) ⟨834128, by rfl⟩ : syracuseStep 1112171 = 1668257) B1668257
theorem B1112183 : Blo 1108626 1112183 := bstep (se 1 (by rfl) ⟨834137, by rfl⟩ : syracuseStep 1112183 = 1668275) B1668275
theorem B1112203 : Blo 1108626 1112203 := bstep (se 1 (by rfl) ⟨834152, by rfl⟩ : syracuseStep 1112203 = 1668305) B1668305
theorem B1407127 : Blo 1108626 1407127 := bstep (se 1 (by rfl) ⟨1055345, by rfl⟩ : syracuseStep 1407127 = 2110691) B2110691
theorem B1112215 : Blo 1108626 1112215 := bstep (se 1 (by rfl) ⟨834161, by rfl⟩ : syracuseStep 1112215 = 1668323) B1668323
theorem B1112235 : Blo 1108626 1112235 := bstep (se 1 (by rfl) ⟨834176, by rfl⟩ : syracuseStep 1112235 = 1668353) B1668353
theorem B1112247 : Blo 1108626 1112247 := bstep (se 1 (by rfl) ⟨834185, by rfl⟩ : syracuseStep 1112247 = 1668371) B1668371
theorem B1112267 : Blo 1108626 1112267 := bstep (se 1 (by rfl) ⟨834200, by rfl⟩ : syracuseStep 1112267 = 1668401) B1668401
theorem B1112279 : Blo 1108626 1112279 := bstep (se 1 (by rfl) ⟨834209, by rfl⟩ : syracuseStep 1112279 = 1668419) B1668419
theorem B1112299 : Blo 1108626 1112299 := bstep (se 1 (by rfl) ⟨834224, by rfl⟩ : syracuseStep 1112299 = 1668449) B1668449
theorem B1112311 : Blo 1108626 1112311 := bstep (se 1 (by rfl) ⟨834233, by rfl⟩ : syracuseStep 1112311 = 1668467) B1668467
theorem B1112331 : Blo 1108626 1112331 := bstep (se 1 (by rfl) ⟨834248, by rfl⟩ : syracuseStep 1112331 = 1668497) B1668497
theorem B1112343 : Blo 1108626 1112343 := bstep (se 1 (by rfl) ⟨834257, by rfl⟩ : syracuseStep 1112343 = 1668515) B1668515
theorem B2816279 : Blo 1108626 2816279 := bstep (se 1 (by rfl) ⟨2112209, by rfl⟩ : syracuseStep 2816279 = 4224419) B4224419
theorem B1112363 : Blo 1108626 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B1112375 : Blo 1108626 1112375 := bstep (se 1 (by rfl) ⟨834281, by rfl⟩ : syracuseStep 1112375 = 1668563) B1668563
theorem B1112395 : Blo 1108626 1112395 := bstep (se 1 (by rfl) ⟨834296, by rfl⟩ : syracuseStep 1112395 = 1668593) B1668593
theorem B1112407 : Blo 1108626 1112407 := bstep (se 1 (by rfl) ⟨834305, by rfl⟩ : syracuseStep 1112407 = 1668611) B1668611
theorem B1112427 : Blo 1108626 1112427 := bstep (se 1 (by rfl) ⟨834320, by rfl⟩ : syracuseStep 1112427 = 1668641) B1668641
theorem B1112439 : Blo 1108626 1112439 := bstep (se 1 (by rfl) ⟨834329, by rfl⟩ : syracuseStep 1112439 = 1668659) B1668659
theorem B1112459 : Blo 1108626 1112459 := bstep (se 1 (by rfl) ⟨834344, by rfl⟩ : syracuseStep 1112459 = 1668689) B1668689
theorem B1112471 : Blo 1108626 1112471 := bstep (se 1 (by rfl) ⟨834353, by rfl⟩ : syracuseStep 1112471 = 1668707) B1668707
theorem B1112491 : Blo 1108626 1112491 := bstep (se 1 (by rfl) ⟨834368, by rfl⟩ : syracuseStep 1112491 = 1668737) B1668737
theorem B1112503 : Blo 1108626 1112503 := bstep (se 1 (by rfl) ⟨834377, by rfl⟩ : syracuseStep 1112503 = 1668755) B1668755
theorem B1112523 : Blo 1108626 1112523 := bstep (se 1 (by rfl) ⟨834392, by rfl⟩ : syracuseStep 1112523 = 1668785) B1668785
theorem B1112535 : Blo 1108626 1112535 := bstep (se 1 (by rfl) ⟨834401, by rfl⟩ : syracuseStep 1112535 = 1668803) B1668803
theorem B1112555 : Blo 1108626 1112555 := bstep (se 1 (by rfl) ⟨834416, by rfl⟩ : syracuseStep 1112555 = 1668833) B1668833
theorem B1112567 : Blo 1108626 1112567 := bstep (se 1 (by rfl) ⟨834425, by rfl⟩ : syracuseStep 1112567 = 1668851) B1668851
theorem B1112587 : Blo 1108626 1112587 := bstep (se 1 (by rfl) ⟨834440, by rfl⟩ : syracuseStep 1112587 = 1668881) B1668881
theorem B1112599 : Blo 1108626 1112599 := bstep (se 1 (by rfl) ⟨834449, by rfl⟩ : syracuseStep 1112599 = 1668899) B1668899
theorem B1112619 : Blo 1108626 1112619 := bstep (se 1 (by rfl) ⟨834464, by rfl⟩ : syracuseStep 1112619 = 1668929) B1668929
theorem B6421265 : Blo 1108626 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B6421427 : Blo 1108626 6421427 := bstep (se 1 (by rfl) ⟨4816070, by rfl⟩ : syracuseStep 6421427 = 9632141) B9632141
theorem B4750301 : Blo 1108626 4750301 := bstep (se 3 (by rfl) ⟨890681, by rfl⟩ : syracuseStep 4750301 = 1781363) B1781363
theorem B3996823 : Blo 1108626 3996823 := bstep (se 1 (by rfl) ⟨2997617, by rfl⟩ : syracuseStep 3996823 = 5995235) B5995235
theorem B4750609 : Blo 1108626 4750609 := bstep (se 2 (by rfl) ⟨1781478, by rfl⟩ : syracuseStep 4750609 = 3562957) B3562957
theorem B18513197 : Blo 1108626 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B4750643 : Blo 1108626 4750643 := bstep (se 1 (by rfl) ⟨3562982, by rfl⟩ : syracuseStep 4750643 = 7125965) B7125965
theorem B3374401 : Blo 1108626 3374401 := bstep (se 2 (by rfl) ⟨1265400, by rfl⟩ : syracuseStep 3374401 = 2530801) B2530801
theorem B1998283 : Blo 1108626 1998283 := bstep (se 1 (by rfl) ⟨1498712, by rfl⟩ : syracuseStep 1998283 = 2997425) B2997425
theorem B3210931 : Blo 1108626 3210931 := bstep (se 1 (by rfl) ⟨2408198, by rfl⟩ : syracuseStep 3210931 = 4816397) B4816397
theorem B28802765 : Blo 1108626 28802765 := bstep (se 3 (by rfl) ⟨5400518, by rfl⟩ : syracuseStep 28802765 = 10801037) B10801037
theorem B40468403 : Blo 1108626 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B12845101 : Blo 1108626 12845101 := bstep (se 3 (by rfl) ⟨2408456, by rfl⟩ : syracuseStep 12845101 = 4816913) B4816913
theorem B3375191 : Blo 1108626 3375191 := bstep (se 1 (by rfl) ⟨2531393, by rfl⟩ : syracuseStep 3375191 = 5062787) B5062787
theorem B1441963 : Blo 1108626 1441963 := bstep (se 1 (by rfl) ⟨1081472, by rfl⟩ : syracuseStep 1441963 = 2162945) B2162945
theorem B3080719 : Blo 1108626 3080719 := bstep (se 1 (by rfl) ⟨2310539, by rfl⟩ : syracuseStep 3080719 = 4621079) B4621079
theorem B3375703 : Blo 1108626 3375703 := bstep (se 1 (by rfl) ⟨2531777, by rfl⟩ : syracuseStep 3375703 = 5063555) B5063555
theorem B6324965 : Blo 1108626 6324965 := bstep (se 4 (by rfl) ⟨592965, by rfl⟩ : syracuseStep 6324965 = 1185931) B1185931
theorem B1999991 : Blo 1108626 1999991 := bstep (se 1 (by rfl) ⟨1499993, by rfl⟩ : syracuseStep 1999991 = 2999987) B2999987
theorem B8422865 : Blo 1108626 8422865 := bstep (se 2 (by rfl) ⟨3158574, by rfl⟩ : syracuseStep 8422865 = 6317149) B6317149
theorem B36537925 : Blo 1108626 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B1247503 : Blo 1108626 1247503 := bstep (se 1 (by rfl) ⟨935627, by rfl⟩ : syracuseStep 1247503 = 1871255) B1871255
theorem B1248007 : Blo 1108626 1248007 := bstep (se 1 (by rfl) ⟨936005, by rfl⟩ : syracuseStep 1248007 = 1872011) B1872011
theorem B1248187 : Blo 1108626 1248187 := bstep (se 1 (by rfl) ⟨936140, by rfl⟩ : syracuseStep 1248187 = 1872281) B1872281
theorem B1871147 : Blo 1108626 1871147 := bstep (se 1 (by rfl) ⟨1403360, by rfl⟩ : syracuseStep 1871147 = 2806721) B2806721
theorem B1248655 : Blo 1108626 1248655 := bstep (se 1 (by rfl) ⟨936491, by rfl⟩ : syracuseStep 1248655 = 1872983) B1872983
theorem B4001177 : Blo 1108626 4001177 := bstep (se 2 (by rfl) ⟨1500441, by rfl⟩ : syracuseStep 4001177 = 3000883) B3000883
theorem B6753689 : Blo 1108626 6753689 := bstep (se 2 (by rfl) ⟨2532633, by rfl⟩ : syracuseStep 6753689 = 5065267) B5065267
theorem B2002361 : Blo 1108626 2002361 := bstep (se 2 (by rfl) ⟨750885, by rfl⟩ : syracuseStep 2002361 = 1501771) B1501771
theorem B1871545 : Blo 1108626 1871545 := bstep (se 2 (by rfl) ⟨701829, by rfl⟩ : syracuseStep 1871545 = 1403659) B1403659
theorem B18943793 : Blo 1108626 18943793 := bstep (se 2 (by rfl) ⟨7103922, by rfl⟩ : syracuseStep 18943793 = 14207845) B14207845
theorem B1249159 : Blo 1108626 1249159 := bstep (se 1 (by rfl) ⟨936869, by rfl⟩ : syracuseStep 1249159 = 1873739) B1873739
theorem B2002823 : Blo 1108626 2002823 := bstep (se 1 (by rfl) ⟨1502117, by rfl⟩ : syracuseStep 2002823 = 3004235) B3004235
theorem B7606219 : Blo 1108626 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B7999499 : Blo 1108626 7999499 := bstep (se 1 (by rfl) ⟨5999624, by rfl⟩ : syracuseStep 7999499 = 11999249) B11999249
theorem B1249339 : Blo 1108626 1249339 := bstep (se 1 (by rfl) ⟨937004, by rfl⟩ : syracuseStep 1249339 = 1874009) B1874009
theorem B2494583 : Blo 1108626 2494583 := bstep (se 1 (by rfl) ⟨1870937, by rfl⟩ : syracuseStep 2494583 = 3741875) B3741875
theorem B5345473 : Blo 1108626 5345473 := bstep (se 2 (by rfl) ⟨2004552, by rfl⟩ : syracuseStep 5345473 = 4009105) B4009105
theorem B35983601 : Blo 1108626 35983601 := bstep (se 2 (by rfl) ⟨13493850, by rfl⟩ : syracuseStep 35983601 = 26987701) B26987701
theorem B2494763 : Blo 1108626 2494763 := bstep (se 1 (by rfl) ⟨1871072, by rfl⟩ : syracuseStep 2494763 = 3742145) B3742145
theorem B1872247 : Blo 1108626 1872247 := bstep (se 1 (by rfl) ⟨1404185, by rfl⟩ : syracuseStep 1872247 = 2808371) B2808371
theorem B1249807 : Blo 1108626 1249807 := bstep (se 1 (by rfl) ⟨937355, by rfl⟩ : syracuseStep 1249807 = 1874711) B1874711
theorem B64885283 : Blo 1108626 64885283 := bstep (se 1 (by rfl) ⟨48663962, by rfl⟩ : syracuseStep 64885283 = 97327925) B97327925
theorem B1872443 : Blo 1108626 1872443 := bstep (se 1 (by rfl) ⟨1404332, by rfl⟩ : syracuseStep 1872443 = 2808665) B2808665
theorem B2495123 : Blo 1108626 2495123 := bstep (se 1 (by rfl) ⟨1871342, by rfl⟩ : syracuseStep 2495123 = 3742685) B3742685
theorem B2495177 : Blo 1108626 2495177 := bstep (se 2 (by rfl) ⟨935691, by rfl⟩ : syracuseStep 2495177 = 1871383) B1871383
theorem B1872841 : Blo 1108626 1872841 := bstep (se 2 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 1872841 = 1404631) B1404631
theorem B1250311 : Blo 1108626 1250311 := bstep (se 1 (by rfl) ⟨937733, by rfl⟩ : syracuseStep 1250311 = 1875467) B1875467
theorem B1250491 : Blo 1108626 1250491 := bstep (se 1 (by rfl) ⟨937868, by rfl⟩ : syracuseStep 1250491 = 1875737) B1875737
theorem B2495879 : Blo 1108626 2495879 := bstep (se 1 (by rfl) ⟨1871909, by rfl⟩ : syracuseStep 2495879 = 3743819) B3743819
theorem B2496059 : Blo 1108626 2496059 := bstep (se 1 (by rfl) ⟨1872044, by rfl⟩ : syracuseStep 2496059 = 3744089) B3744089
theorem B45553229 : Blo 1108626 45553229 := bstep (se 3 (by rfl) ⟨8541230, by rfl⟩ : syracuseStep 45553229 = 17082461) B17082461
theorem B7116407 : Blo 1108626 7116407 := bstep (se 1 (by rfl) ⟨5337305, by rfl⟩ : syracuseStep 7116407 = 10674611) B10674611
theorem B1873543 : Blo 1108626 1873543 := bstep (se 1 (by rfl) ⟨1405157, by rfl⟩ : syracuseStep 1873543 = 2810315) B2810315
theorem B1250959 : Blo 1108626 1250959 := bstep (se 1 (by rfl) ⟨938219, by rfl⟩ : syracuseStep 1250959 = 1876439) B1876439
theorem B2496185 : Blo 1108626 2496185 := bstep (se 2 (by rfl) ⟨936069, by rfl⟩ : syracuseStep 2496185 = 1872139) B1872139
theorem B1578809 : Blo 1108626 1578809 := bstep (se 2 (by rfl) ⟨592053, by rfl⟩ : syracuseStep 1578809 = 1184107) B1184107
theorem B7313267 : Blo 1108626 7313267 := bstep (se 1 (by rfl) ⟨5484950, by rfl⟩ : syracuseStep 7313267 = 10969901) B10969901
theorem B1185679 : Blo 1108626 1185679 := bstep (se 1 (by rfl) ⟨889259, by rfl⟩ : syracuseStep 1185679 = 1778519) B1778519
theorem B2496527 : Blo 1108626 2496527 := bstep (se 1 (by rfl) ⟨1872395, by rfl⟩ : syracuseStep 2496527 = 3744791) B3744791
theorem B2496545 : Blo 1108626 2496545 := bstep (se 2 (by rfl) ⟨936204, by rfl⟩ : syracuseStep 2496545 = 1872409) B1872409
theorem B1251463 : Blo 1108626 1251463 := bstep (se 1 (by rfl) ⟨938597, by rfl⟩ : syracuseStep 1251463 = 1877195) B1877195
theorem B1185935 : Blo 1108626 1185935 := bstep (se 1 (by rfl) ⟨889451, by rfl⟩ : syracuseStep 1185935 = 1778903) B1778903
theorem B1874191 : Blo 1108626 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B1251643 : Blo 1108626 1251643 := bstep (se 1 (by rfl) ⟨938732, by rfl⟩ : syracuseStep 1251643 = 1877465) B1877465
theorem B2496887 : Blo 1108626 2496887 := bstep (se 1 (by rfl) ⟨1872665, by rfl⟩ : syracuseStep 2496887 = 3745331) B3745331
theorem B4004363 : Blo 1108626 4004363 := bstep (se 1 (by rfl) ⟨3003272, by rfl⟩ : syracuseStep 4004363 = 6006545) B6006545
theorem B2497067 : Blo 1108626 2497067 := bstep (se 1 (by rfl) ⟨1872800, by rfl⟩ : syracuseStep 2497067 = 3745601) B3745601
theorem B13703897 : Blo 1108626 13703897 := bstep (se 2 (by rfl) ⟨5138961, by rfl⟩ : syracuseStep 13703897 = 10277923) B10277923
theorem B1874731 : Blo 1108626 1874731 := bstep (se 1 (by rfl) ⟨1406048, by rfl⟩ : syracuseStep 1874731 = 2812097) B2812097
theorem B3742523 : Blo 1108626 3742523 := bstep (se 1 (by rfl) ⟨2806892, by rfl⟩ : syracuseStep 3742523 = 5613785) B5613785
theorem B2497427 : Blo 1108626 2497427 := bstep (se 1 (by rfl) ⟨1873070, by rfl⟩ : syracuseStep 2497427 = 3746141) B3746141
theorem B38411171 : Blo 1108626 38411171 := bstep (se 1 (by rfl) ⟨28808378, by rfl⟩ : syracuseStep 38411171 = 57616757) B57616757
theorem B1874873 : Blo 1108626 1874873 := bstep (se 2 (by rfl) ⟨703077, by rfl⟩ : syracuseStep 1874873 = 1406155) B1406155
theorem B2497481 : Blo 1108626 2497481 := bstep (se 2 (by rfl) ⟨936555, by rfl⟩ : syracuseStep 2497481 = 1873111) B1873111
theorem B17538053 : Blo 1108626 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B3743009 : Blo 1108626 3743009 := bstep (se 2 (by rfl) ⟨1403628, by rfl⟩ : syracuseStep 3743009 = 2807257) B2807257
theorem B1580347 : Blo 1108626 1580347 := bstep (se 1 (by rfl) ⟨1185260, by rfl⟩ : syracuseStep 1580347 = 2370521) B2370521
theorem B10821221 : Blo 1108626 10821221 := bstep (se 4 (by rfl) ⟨1014489, by rfl⟩ : syracuseStep 10821221 = 2028979) B2028979
theorem B1875575 : Blo 1108626 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B2498183 : Blo 1108626 2498183 := bstep (se 1 (by rfl) ⟨1873637, by rfl⟩ : syracuseStep 2498183 = 3747275) B3747275
theorem B1580791 : Blo 1108626 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B17342257 : Blo 1108626 17342257 := bstep (se 2 (by rfl) ⟨6503346, by rfl⟩ : syracuseStep 17342257 = 13006693) B13006693
theorem B2498363 : Blo 1108626 2498363 := bstep (se 1 (by rfl) ⟨1873772, by rfl⟩ : syracuseStep 2498363 = 3747545) B3747545
theorem B3743603 : Blo 1108626 3743603 := bstep (se 1 (by rfl) ⟨2807702, by rfl⟩ : syracuseStep 3743603 = 5615405) B5615405
theorem B2498489 : Blo 1108626 2498489 := bstep (se 2 (by rfl) ⟨936933, by rfl⟩ : syracuseStep 2498489 = 1873867) B1873867
theorem B1876027 : Blo 1108626 1876027 := bstep (se 1 (by rfl) ⟨1407020, by rfl⟩ : syracuseStep 1876027 = 2814041) B2814041
theorem B1876169 : Blo 1108626 1876169 := bstep (se 2 (by rfl) ⟨703563, by rfl⟩ : syracuseStep 1876169 = 1407127) B1407127
theorem B2498831 : Blo 1108626 2498831 := bstep (se 1 (by rfl) ⟨1874123, by rfl⟩ : syracuseStep 2498831 = 3748247) B3748247
theorem B6332687 : Blo 1108626 6332687 := bstep (se 1 (by rfl) ⟨4749515, by rfl⟩ : syracuseStep 6332687 = 9499031) B9499031
theorem B2498849 : Blo 1108626 2498849 := bstep (se 2 (by rfl) ⟨937068, by rfl⟩ : syracuseStep 2498849 = 1874137) B1874137
theorem B2367787 : Blo 1108626 2367787 := bstep (se 1 (by rfl) ⟨1775840, by rfl⟩ : syracuseStep 2367787 = 3551681) B3551681
theorem B2105747 : Blo 1108626 2105747 := bstep (se 1 (by rfl) ⟨1579310, by rfl⟩ : syracuseStep 2105747 = 3158621) B3158621
theorem B4268555 : Blo 1108626 4268555 := bstep (se 1 (by rfl) ⟨3201416, by rfl⟩ : syracuseStep 4268555 = 6402833) B6402833
theorem B2368043 : Blo 1108626 2368043 := bstep (se 1 (by rfl) ⟨1776032, by rfl⟩ : syracuseStep 2368043 = 3552065) B3552065
theorem B1581611 : Blo 1108626 1581611 := bstep (se 1 (by rfl) ⟨1186208, by rfl⟩ : syracuseStep 1581611 = 2372417) B2372417
theorem B2105975 : Blo 1108626 2105975 := bstep (se 1 (by rfl) ⟨1579481, by rfl⟩ : syracuseStep 2105975 = 3158963) B3158963
theorem B2499191 : Blo 1108626 2499191 := bstep (se 1 (by rfl) ⟨1874393, by rfl⟩ : syracuseStep 2499191 = 3748787) B3748787
theorem B41067299 : Blo 1108626 41067299 := bstep (se 1 (by rfl) ⟨30800474, by rfl⟩ : syracuseStep 41067299 = 61600949) B61600949
theorem B2499371 : Blo 1108626 2499371 := bstep (se 1 (by rfl) ⟨1874528, by rfl⟩ : syracuseStep 2499371 = 3749057) B3749057
theorem B1876871 : Blo 1108626 1876871 := bstep (se 1 (by rfl) ⟨1407653, by rfl⟩ : syracuseStep 1876871 = 2815307) B2815307
theorem B59352139 : Blo 1108626 59352139 := bstep (se 1 (by rfl) ⟨44514104, by rfl⟩ : syracuseStep 59352139 = 89028209) B89028209
theorem B68363351 : Blo 1108626 68363351 := bstep (se 1 (by rfl) ⟨51272513, by rfl⟩ : syracuseStep 68363351 = 102545027) B102545027
theorem B7611479 : Blo 1108626 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B2499731 : Blo 1108626 2499731 := bstep (se 1 (by rfl) ⟨1874798, by rfl⟩ : syracuseStep 2499731 = 3749597) B3749597
theorem B2499785 : Blo 1108626 2499785 := bstep (se 2 (by rfl) ⟨937419, by rfl⟩ : syracuseStep 2499785 = 1874839) B1874839
theorem B2532743 : Blo 1108626 2532743 := bstep (se 1 (by rfl) ⟨1899557, by rfl⟩ : syracuseStep 2532743 = 3799115) B3799115
theorem B1877519 : Blo 1108626 1877519 := bstep (se 1 (by rfl) ⟨1408139, by rfl⟩ : syracuseStep 1877519 = 2816279) B2816279
theorem B2369171 : Blo 1108626 2369171 := bstep (se 1 (by rfl) ⟨1776878, by rfl⟩ : syracuseStep 2369171 = 3553757) B3553757
theorem B12658355 : Blo 1108626 12658355 := bstep (se 1 (by rfl) ⟨9493766, by rfl⟩ : syracuseStep 12658355 = 18987533) B18987533
theorem B6334145 : Blo 1108626 6334145 := bstep (se 2 (by rfl) ⟨2375304, by rfl⟩ : syracuseStep 6334145 = 4750609) B4750609
theorem B4499201 : Blo 1108626 4499201 := bstep (se 2 (by rfl) ⟨1687200, by rfl⟩ : syracuseStep 4499201 = 3374401) B3374401
theorem B6006565 : Blo 1108626 6006565 := bstep (se 4 (by rfl) ⟨563115, by rfl⟩ : syracuseStep 6006565 = 1126231) B1126231
theorem B13510489 : Blo 1108626 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B2500487 : Blo 1108626 2500487 := bstep (se 1 (by rfl) ⟨1875365, by rfl⟩ : syracuseStep 2500487 = 3750731) B3750731
theorem B2664377 : Blo 1108626 2664377 := bstep (se 2 (by rfl) ⟨999141, by rfl⟩ : syracuseStep 2664377 = 1998283) B1998283
theorem B2500667 : Blo 1108626 2500667 := bstep (se 1 (by rfl) ⟨1875500, by rfl⟩ : syracuseStep 2500667 = 3751001) B3751001
theorem B2369683 : Blo 1108626 2369683 := bstep (se 1 (by rfl) ⟨1777262, by rfl⟩ : syracuseStep 2369683 = 3554525) B3554525
theorem B2500793 : Blo 1108626 2500793 := bstep (se 2 (by rfl) ⟨937797, by rfl⟩ : syracuseStep 2500793 = 1875595) B1875595
theorem B2107691 : Blo 1108626 2107691 := bstep (se 1 (by rfl) ⟨1580768, by rfl⟩ : syracuseStep 2107691 = 3161537) B3161537
theorem B1583479 : Blo 1108626 1583479 := bstep (se 1 (by rfl) ⟨1187609, by rfl⟩ : syracuseStep 1583479 = 2375219) B2375219
theorem B3746195 : Blo 1108626 3746195 := bstep (se 1 (by rfl) ⟨2809646, by rfl⟩ : syracuseStep 3746195 = 5619293) B5619293
theorem B2107919 : Blo 1108626 2107919 := bstep (se 1 (by rfl) ⟨1580939, by rfl⟩ : syracuseStep 2107919 = 3161879) B3161879
theorem B2501135 : Blo 1108626 2501135 := bstep (se 1 (by rfl) ⟨1875851, by rfl⟩ : syracuseStep 2501135 = 3751703) B3751703
theorem B5614109 : Blo 1108626 5614109 := bstep (se 3 (by rfl) ⟨1052645, by rfl⟩ : syracuseStep 5614109 = 2105291) B2105291
theorem B2501153 : Blo 1108626 2501153 := bstep (se 2 (by rfl) ⟨937932, by rfl⟩ : syracuseStep 2501153 = 1875865) B1875865
theorem B26978935 : Blo 1108626 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B2665145 : Blo 1108626 2665145 := bstep (se 2 (by rfl) ⟨999429, by rfl⟩ : syracuseStep 2665145 = 1998859) B1998859
theorem B2534159 : Blo 1108626 2534159 := bstep (se 1 (by rfl) ⟨1900619, by rfl⟩ : syracuseStep 2534159 = 3801239) B3801239
theorem B2501495 : Blo 1108626 2501495 := bstep (se 1 (by rfl) ⟨1876121, by rfl⟩ : syracuseStep 2501495 = 3752243) B3752243
theorem B5614595 : Blo 1108626 5614595 := bstep (se 1 (by rfl) ⟨4210946, by rfl⟩ : syracuseStep 5614595 = 8421893) B8421893
theorem B2501675 : Blo 1108626 2501675 := bstep (se 1 (by rfl) ⟨1876256, by rfl⟩ : syracuseStep 2501675 = 3752513) B3752513
theorem B2502035 : Blo 1108626 2502035 := bstep (se 1 (by rfl) ⟨1876526, by rfl⟩ : syracuseStep 2502035 = 3753053) B3753053
theorem B4271545 : Blo 1108626 4271545 := bstep (se 2 (by rfl) ⟨1601829, by rfl⟩ : syracuseStep 4271545 = 3203659) B3203659
theorem B2502089 : Blo 1108626 2502089 := bstep (se 2 (by rfl) ⟨938283, by rfl⟩ : syracuseStep 2502089 = 1876567) B1876567
theorem B17346001 : Blo 1108626 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B3157505 : Blo 1108626 3157505 := bstep (se 2 (by rfl) ⟨1184064, by rfl⟩ : syracuseStep 3157505 = 2368129) B2368129
theorem B13872869 : Blo 1108626 13872869 := bstep (se 4 (by rfl) ⟨1300581, by rfl⟩ : syracuseStep 13872869 = 2601163) B2601163
theorem B3747599 : Blo 1108626 3747599 := bstep (se 1 (by rfl) ⟨2810699, by rfl⟩ : syracuseStep 3747599 = 5621399) B5621399
theorem B2666375 : Blo 1108626 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B2109331 : Blo 1108626 2109331 := bstep (se 1 (by rfl) ⟨1581998, by rfl⟩ : syracuseStep 2109331 = 3163997) B3163997
theorem B3747869 : Blo 1108626 3747869 := bstep (se 3 (by rfl) ⟨702725, by rfl⟩ : syracuseStep 3747869 = 1405451) B1405451
theorem B2109559 : Blo 1108626 2109559 := bstep (se 1 (by rfl) ⟨1582169, by rfl⟩ : syracuseStep 2109559 = 3164339) B3164339
theorem B2502791 : Blo 1108626 2502791 := bstep (se 1 (by rfl) ⟨1877093, by rfl⟩ : syracuseStep 2502791 = 3754187) B3754187
theorem B2502971 : Blo 1108626 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B18952541 : Blo 1108626 18952541 := bstep (se 3 (by rfl) ⟨3553601, by rfl⟩ : syracuseStep 18952541 = 7107203) B7107203
theorem B2503097 : Blo 1108626 2503097 := bstep (se 2 (by rfl) ⟨938661, by rfl⟩ : syracuseStep 2503097 = 1877323) B1877323
theorem B3158473 : Blo 1108626 3158473 := bstep (se 2 (by rfl) ⟨1184427, by rfl⟩ : syracuseStep 3158473 = 2368855) B2368855
theorem B2372041 : Blo 1108626 2372041 := bstep (se 2 (by rfl) ⟨889515, by rfl⟩ : syracuseStep 2372041 = 1779031) B1779031
theorem B22819313 : Blo 1108626 22819313 := bstep (se 2 (by rfl) ⟨8557242, by rfl⟩ : syracuseStep 22819313 = 17114485) B17114485
theorem B2568763 : Blo 1108626 2568763 := bstep (se 1 (by rfl) ⟨1926572, by rfl⟩ : syracuseStep 2568763 = 3853145) B3853145
theorem B5616215 : Blo 1108626 5616215 := bstep (se 1 (by rfl) ⟨4212161, by rfl⟩ : syracuseStep 5616215 = 8424323) B8424323
theorem B8991425 : Blo 1108626 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B34714457 : Blo 1108626 34714457 := bstep (se 2 (by rfl) ⟨13017921, by rfl⟩ : syracuseStep 34714457 = 26035843) B26035843
theorem B5616701 : Blo 1108626 5616701 := bstep (se 3 (by rfl) ⟨1053131, by rfl⟩ : syracuseStep 5616701 = 2106263) B2106263
theorem B3749273 : Blo 1108626 3749273 := bstep (se 2 (by rfl) ⟨1405977, by rfl⟩ : syracuseStep 3749273 = 2811955) B2811955
theorem B10827229 : Blo 1108626 10827229 := bstep (se 3 (by rfl) ⟨2030105, by rfl⟩ : syracuseStep 10827229 = 4060211) B4060211
theorem B2111123 : Blo 1108626 2111123 := bstep (se 1 (by rfl) ⟨1583342, by rfl⟩ : syracuseStep 2111123 = 3166685) B3166685
theorem B2373305 : Blo 1108626 2373305 := bstep (se 2 (by rfl) ⟨889989, by rfl⟩ : syracuseStep 2373305 = 1779979) B1779979
theorem B2111177 : Blo 1108626 2111177 := bstep (se 2 (by rfl) ⟨791691, by rfl⟩ : syracuseStep 2111177 = 1583383) B1583383
theorem B2373391 : Blo 1108626 2373391 := bstep (se 1 (by rfl) ⟨1780043, by rfl⟩ : syracuseStep 2373391 = 3560087) B3560087
theorem B6403873 : Blo 1108626 6403873 := bstep (se 2 (by rfl) ⟨2401452, by rfl⟩ : syracuseStep 6403873 = 4802905) B4802905
theorem B2111275 : Blo 1108626 2111275 := bstep (se 1 (by rfl) ⟨1583456, by rfl⟩ : syracuseStep 2111275 = 3166913) B3166913
theorem B11417507 : Blo 1108626 11417507 := bstep (se 1 (by rfl) ⟨8563130, by rfl⟩ : syracuseStep 11417507 = 17126261) B17126261
theorem B8009675 : Blo 1108626 8009675 := bstep (se 1 (by rfl) ⟨6007256, by rfl⟩ : syracuseStep 8009675 = 12014513) B12014513
theorem B3160079 : Blo 1108626 3160079 := bstep (se 1 (by rfl) ⟨2370059, by rfl⟩ : syracuseStep 3160079 = 4740119) B4740119
theorem B2111503 : Blo 1108626 2111503 := bstep (se 1 (by rfl) ⟨1583627, by rfl⟩ : syracuseStep 2111503 = 3167255) B3167255
theorem B3749975 : Blo 1108626 3749975 := bstep (se 1 (by rfl) ⟨2812481, by rfl⟩ : syracuseStep 3749975 = 5624963) B5624963
theorem B2996795 : Blo 1108626 2996795 := bstep (se 1 (by rfl) ⟨2247596, by rfl⟩ : syracuseStep 2996795 = 4495193) B4495193
theorem B3750461 : Blo 1108626 3750461 := bstep (se 3 (by rfl) ⟨703211, by rfl⟩ : syracuseStep 3750461 = 1406423) B1406423
theorem B4209353 : Blo 1108626 4209353 := bstep (se 2 (by rfl) ⟨1578507, by rfl⟩ : syracuseStep 4209353 = 3157015) B3157015
theorem B16005923 : Blo 1108626 16005923 := bstep (se 1 (by rfl) ⟨12004442, by rfl⟩ : syracuseStep 16005923 = 24008885) B24008885
theorem B6404915 : Blo 1108626 6404915 := bstep (se 1 (by rfl) ⟨4803686, by rfl⟩ : syracuseStep 6404915 = 9607373) B9607373
theorem B5618483 : Blo 1108626 5618483 := bstep (se 1 (by rfl) ⟨4213862, by rfl⟩ : syracuseStep 5618483 = 8427725) B8427725
theorem B2669431 : Blo 1108626 2669431 := bstep (se 1 (by rfl) ⟨2002073, by rfl⟩ : syracuseStep 2669431 = 4004147) B4004147
theorem B9616445 : Blo 1108626 9616445 := bstep (se 3 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 9616445 = 3606167) B3606167
theorem B5618807 : Blo 1108626 5618807 := bstep (se 1 (by rfl) ⟨4214105, by rfl⟩ : syracuseStep 5618807 = 8428211) B8428211
theorem B3161207 : Blo 1108626 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B2374775 : Blo 1108626 2374775 := bstep (se 1 (by rfl) ⟨1781081, by rfl⟩ : syracuseStep 2374775 = 3562163) B3562163
theorem B1686671 : Blo 1108626 1686671 := bstep (se 1 (by rfl) ⟨1265003, by rfl⟩ : syracuseStep 1686671 = 2530007) B2530007
theorem B8994347 : Blo 1108626 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B3751865 : Blo 1108626 3751865 := bstep (se 2 (by rfl) ⟨1406949, by rfl⟩ : syracuseStep 3751865 = 2813899) B2813899
theorem B5619779 : Blo 1108626 5619779 := bstep (se 1 (by rfl) ⟨4214834, by rfl⟩ : syracuseStep 5619779 = 8429669) B8429669
theorem B5620103 : Blo 1108626 5620103 := bstep (se 1 (by rfl) ⟨4215077, by rfl⟩ : syracuseStep 5620103 = 8430155) B8430155
theorem B4211129 : Blo 1108626 4211129 := bstep (se 2 (by rfl) ⟨1579173, by rfl⟩ : syracuseStep 4211129 = 3158347) B3158347
theorem B8536529 : Blo 1108626 8536529 := bstep (se 2 (by rfl) ⟨3201198, by rfl⟩ : syracuseStep 8536529 = 6402397) B6402397
theorem B3752459 : Blo 1108626 3752459 := bstep (se 1 (by rfl) ⟨2814344, by rfl⟩ : syracuseStep 3752459 = 5628689) B5628689
theorem B2998871 : Blo 1108626 2998871 := bstep (se 1 (by rfl) ⟨2249153, by rfl⟩ : syracuseStep 2998871 = 4498307) B4498307
theorem B3752567 : Blo 1108626 3752567 := bstep (se 1 (by rfl) ⟨2814425, by rfl⟩ : syracuseStep 3752567 = 5628851) B5628851
theorem B4735745 : Blo 1108626 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B3162881 : Blo 1108626 3162881 := bstep (se 2 (by rfl) ⟨1186080, by rfl⟩ : syracuseStep 3162881 = 2372161) B2372161
theorem B3162995 : Blo 1108626 3162995 := bstep (se 1 (by rfl) ⟨2372246, by rfl⟩ : syracuseStep 3162995 = 4744493) B4744493
theorem B3163337 : Blo 1108626 3163337 := bstep (se 2 (by rfl) ⟨1186251, by rfl⟩ : syracuseStep 3163337 = 2372503) B2372503
theorem B3753161 : Blo 1108626 3753161 := bstep (se 2 (by rfl) ⟨1407435, by rfl⟩ : syracuseStep 3753161 = 2814871) B2814871
theorem B200263043 : Blo 1108626 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B4572569 : Blo 1108626 4572569 := bstep (se 2 (by rfl) ⟨1714713, by rfl⟩ : syracuseStep 4572569 = 3429427) B3429427
theorem B57787981 : Blo 1108626 57787981 := bstep (se 3 (by rfl) ⟨10835246, by rfl⟩ : syracuseStep 57787981 = 21670493) B21670493
theorem B2672275 : Blo 1108626 2672275 := bstep (se 1 (by rfl) ⟨2004206, by rfl⟩ : syracuseStep 2672275 = 4008413) B4008413
theorem B3753863 : Blo 1108626 3753863 := bstep (se 1 (by rfl) ⟨2815397, by rfl⟩ : syracuseStep 3753863 = 5630795) B5630795
theorem B2672651 : Blo 1108626 2672651 := bstep (se 1 (by rfl) ⟨2004488, by rfl⟩ : syracuseStep 2672651 = 4008977) B4008977
theorem B3000505 : Blo 1108626 3000505 := bstep (se 2 (by rfl) ⟨1125189, by rfl⟩ : syracuseStep 3000505 = 2250379) B2250379
theorem B3754241 : Blo 1108626 3754241 := bstep (se 2 (by rfl) ⟨1407840, by rfl⟩ : syracuseStep 3754241 = 2815681) B2815681
theorem B6408791 : Blo 1108626 6408791 := bstep (se 1 (by rfl) ⟨4806593, by rfl⟩ : syracuseStep 6408791 = 9613187) B9613187
theorem B3001121 : Blo 1108626 3001121 := bstep (se 2 (by rfl) ⟨1125420, by rfl⟩ : syracuseStep 3001121 = 2250841) B2250841
theorem B18991907 : Blo 1108626 18991907 := bstep (se 1 (by rfl) ⟨14243930, by rfl⟩ : syracuseStep 18991907 = 28487861) B28487861
theorem B3165227 : Blo 1108626 3165227 := bstep (se 1 (by rfl) ⟨2373920, by rfl⟩ : syracuseStep 3165227 = 4747841) B4747841
theorem B3755051 : Blo 1108626 3755051 := bstep (se 1 (by rfl) ⟨2816288, by rfl⟩ : syracuseStep 3755051 = 5632577) B5632577
theorem B12012781 : Blo 1108626 12012781 := bstep (se 3 (by rfl) ⟨2252396, by rfl⟩ : syracuseStep 12012781 = 4504793) B4504793
theorem B3165455 : Blo 1108626 3165455 := bstep (se 1 (by rfl) ⟨2374091, by rfl⟩ : syracuseStep 3165455 = 4748183) B4748183
theorem B3001943 : Blo 1108626 3001943 := bstep (se 1 (by rfl) ⟨2251457, by rfl⟩ : syracuseStep 3001943 = 4502915) B4502915
theorem B25611875 : Blo 1108626 25611875 := bstep (se 1 (by rfl) ⟨19208906, by rfl⟩ : syracuseStep 25611875 = 38417813) B38417813
theorem B27053669 : Blo 1108626 27053669 := bstep (se 4 (by rfl) ⟨2536281, by rfl⟩ : syracuseStep 27053669 = 5072563) B5072563
theorem B5623667 : Blo 1108626 5623667 := bstep (se 1 (by rfl) ⟨4217750, by rfl⟩ : syracuseStep 5623667 = 8435501) B8435501
theorem B4214713 : Blo 1108626 4214713 := bstep (se 2 (by rfl) ⟨1580517, by rfl⟩ : syracuseStep 4214713 = 3161035) B3161035
theorem B5329097 : Blo 1108626 5329097 := bstep (se 2 (by rfl) ⟨1998411, by rfl⟩ : syracuseStep 5329097 = 3996823) B3996823
theorem B5624153 : Blo 1108626 5624153 := bstep (se 2 (by rfl) ⟨2109057, by rfl⟩ : syracuseStep 5624153 = 4218115) B4218115
theorem B4280843 : Blo 1108626 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B4280951 : Blo 1108626 4280951 := bstep (se 1 (by rfl) ⟨3210713, by rfl⟩ : syracuseStep 4280951 = 6421427) B6421427
theorem B3166867 : Blo 1108626 3166867 := bstep (se 1 (by rfl) ⟨2375150, by rfl⟩ : syracuseStep 3166867 = 4750301) B4750301
theorem B6411097 : Blo 1108626 6411097 := bstep (se 2 (by rfl) ⟨2404161, by rfl⟩ : syracuseStep 6411097 = 4808323) B4808323
theorem B12342131 : Blo 1108626 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B2741111 : Blo 1108626 2741111 := bstep (se 1 (by rfl) ⟨2055833, by rfl⟩ : syracuseStep 2741111 = 4111667) B4111667
theorem B3167095 : Blo 1108626 3167095 := bstep (se 1 (by rfl) ⟨2375321, by rfl⟩ : syracuseStep 3167095 = 4750643) B4750643
theorem B4281241 : Blo 1108626 4281241 := bstep (se 2 (by rfl) ⟨1605465, by rfl⟩ : syracuseStep 4281241 = 3210931) B3210931
theorem B18043829 : Blo 1108626 18043829 := bstep (se 5 (by rfl) ⟨845804, by rfl⟩ : syracuseStep 18043829 = 1691609) B1691609
theorem B4740049 : Blo 1108626 4740049 := bstep (se 2 (by rfl) ⟨1777518, by rfl⟩ : syracuseStep 4740049 = 3555037) B3555037
theorem B1627195 : Blo 1108626 1627195 := bstep (se 1 (by rfl) ⟨1220396, by rfl⟩ : syracuseStep 1627195 = 2440793) B2440793
theorem B8443763 : Blo 1108626 8443763 := bstep (se 1 (by rfl) ⟨6332822, by rfl⟩ : syracuseStep 8443763 = 12665645) B12665645
theorem B1333111 : Blo 1108626 1333111 := bstep (se 1 (by rfl) ⟨999833, by rfl⟩ : syracuseStep 1333111 = 1999667) B1999667
theorem B1267591 : Blo 1108626 1267591 := bstep (se 1 (by rfl) ⟨950693, by rfl⟩ : syracuseStep 1267591 = 1901387) B1901387
theorem B13522949 : Blo 1108626 13522949 := bstep (se 4 (by rfl) ⟨1267776, by rfl⟩ : syracuseStep 13522949 = 2535553) B2535553
theorem B1333255 : Blo 1108626 1333255 := bstep (se 1 (by rfl) ⟨999941, by rfl⟩ : syracuseStep 1333255 = 1999883) B1999883
theorem B6314051 : Blo 1108626 6314051 := bstep (se 1 (by rfl) ⟨4735538, by rfl⟩ : syracuseStep 6314051 = 9471077) B9471077
theorem B3168371 : Blo 1108626 3168371 := bstep (se 1 (by rfl) ⟨2376278, by rfl⟩ : syracuseStep 3168371 = 4752557) B4752557
theorem B5068919 : Blo 1108626 5068919 := bstep (se 1 (by rfl) ⟨3801689, by rfl⟩ : syracuseStep 5068919 = 7603379) B7603379
theorem B1923257 : Blo 1108626 1923257 := bstep (se 2 (by rfl) ⟨721221, by rfl⟩ : syracuseStep 1923257 = 1442443) B1442443
theorem B2808179 : Blo 1108626 2808179 := bstep (se 1 (by rfl) ⟨2106134, by rfl⟩ : syracuseStep 2808179 = 4212269) B4212269
theorem B5626259 : Blo 1108626 5626259 := bstep (se 1 (by rfl) ⟨4219694, by rfl⟩ : syracuseStep 5626259 = 8439389) B8439389
theorem B6314507 : Blo 1108626 6314507 := bstep (se 1 (by rfl) ⟨4735880, by rfl⟩ : syracuseStep 6314507 = 9471761) B9471761
theorem B4217615 : Blo 1108626 4217615 := bstep (se 1 (by rfl) ⟨3163211, by rfl⟩ : syracuseStep 4217615 = 6326423) B6326423
theorem B2808695 : Blo 1108626 2808695 := bstep (se 1 (by rfl) ⟨2106521, by rfl⟩ : syracuseStep 2808695 = 4213043) B4213043
theorem B5331865 : Blo 1108626 5331865 := bstep (se 2 (by rfl) ⟨1999449, by rfl⟩ : syracuseStep 5331865 = 3998899) B3998899
theorem B5332787 : Blo 1108626 5332787 := bstep (se 1 (by rfl) ⟨3999590, by rfl⟩ : syracuseStep 5332787 = 7999181) B7999181
theorem B2809687 : Blo 1108626 2809687 := bstep (se 1 (by rfl) ⟨2107265, by rfl⟩ : syracuseStep 2809687 = 4214531) B4214531
theorem B1662983 : Blo 1108626 1662983 := bstep (se 1 (by rfl) ⟨1247237, by rfl⟩ : syracuseStep 1662983 = 2494475) B2494475
theorem B1663019 : Blo 1108626 1663019 := bstep (se 1 (by rfl) ⟨1247264, by rfl⟩ : syracuseStep 1663019 = 2494529) B2494529
theorem B1663049 : Blo 1108626 1663049 := bstep (se 2 (by rfl) ⟨623643, by rfl⟩ : syracuseStep 1663049 = 1247287) B1247287
theorem B2809991 : Blo 1108626 2809991 := bstep (se 1 (by rfl) ⟨2107493, by rfl⟩ : syracuseStep 2809991 = 4214987) B4214987
theorem B1663163 : Blo 1108626 1663163 := bstep (se 1 (by rfl) ⟨1247372, by rfl⟩ : syracuseStep 1663163 = 2494745) B2494745
theorem B27025649 : Blo 1108626 27025649 := bstep (se 2 (by rfl) ⟨10134618, by rfl⟩ : syracuseStep 27025649 = 20269237) B20269237
theorem B1663223 : Blo 1108626 1663223 := bstep (se 1 (by rfl) ⟨1247417, by rfl⟩ : syracuseStep 1663223 = 2494835) B2494835
theorem B3563777 : Blo 1108626 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B2810123 : Blo 1108626 2810123 := bstep (se 1 (by rfl) ⟨2107592, by rfl⟩ : syracuseStep 2810123 = 4215185) B4215185
theorem B1663247 : Blo 1108626 1663247 := bstep (se 1 (by rfl) ⟨1247435, by rfl⟩ : syracuseStep 1663247 = 2494871) B2494871
theorem B1663289 : Blo 1108626 1663289 := bstep (se 2 (by rfl) ⟨623733, by rfl⟩ : syracuseStep 1663289 = 1247467) B1247467
theorem B1663367 : Blo 1108626 1663367 := bstep (se 1 (by rfl) ⟨1247525, by rfl⟩ : syracuseStep 1663367 = 2495051) B2495051
theorem B1663403 : Blo 1108626 1663403 := bstep (se 1 (by rfl) ⟨1247552, by rfl⟩ : syracuseStep 1663403 = 2495105) B2495105
theorem B1663433 : Blo 1108626 1663433 := bstep (se 2 (by rfl) ⟨623787, by rfl⟩ : syracuseStep 1663433 = 1247575) B1247575
theorem B1663547 : Blo 1108626 1663547 := bstep (se 1 (by rfl) ⟨1247660, by rfl⟩ : syracuseStep 1663547 = 2495321) B2495321
theorem B1663607 : Blo 1108626 1663607 := bstep (se 1 (by rfl) ⟨1247705, by rfl⟩ : syracuseStep 1663607 = 2495411) B2495411
theorem B1663631 : Blo 1108626 1663631 := bstep (se 1 (by rfl) ⟨1247723, by rfl⟩ : syracuseStep 1663631 = 2495447) B2495447
theorem B1663673 : Blo 1108626 1663673 := bstep (se 2 (by rfl) ⟨623877, by rfl⟩ : syracuseStep 1663673 = 1247755) B1247755
theorem B1663751 : Blo 1108626 1663751 := bstep (se 1 (by rfl) ⟨1247813, by rfl⟩ : syracuseStep 1663751 = 2495627) B2495627
theorem B2810639 : Blo 1108626 2810639 := bstep (se 1 (by rfl) ⟨2107979, by rfl⟩ : syracuseStep 2810639 = 4215959) B4215959
theorem B13525775 : Blo 1108626 13525775 := bstep (se 1 (by rfl) ⟨10144331, by rfl⟩ : syracuseStep 13525775 = 20288663) B20288663
theorem B1663787 : Blo 1108626 1663787 := bstep (se 1 (by rfl) ⟨1247840, by rfl⟩ : syracuseStep 1663787 = 2495681) B2495681
theorem B1663817 : Blo 1108626 1663817 := bstep (se 2 (by rfl) ⟨623931, by rfl⟩ : syracuseStep 1663817 = 1247863) B1247863
theorem B2810771 : Blo 1108626 2810771 := bstep (se 1 (by rfl) ⟨2108078, by rfl⟩ : syracuseStep 2810771 = 4216157) B4216157
theorem B1663931 : Blo 1108626 1663931 := bstep (se 1 (by rfl) ⟨1247948, by rfl⟩ : syracuseStep 1663931 = 2495897) B2495897
theorem B1663991 : Blo 1108626 1663991 := bstep (se 1 (by rfl) ⟨1247993, by rfl⟩ : syracuseStep 1663991 = 2495987) B2495987
theorem B1664015 : Blo 1108626 1664015 := bstep (se 1 (by rfl) ⟨1248011, by rfl⟩ : syracuseStep 1664015 = 2496023) B2496023
theorem B1664057 : Blo 1108626 1664057 := bstep (se 2 (by rfl) ⟨624021, by rfl⟩ : syracuseStep 1664057 = 1248043) B1248043
theorem B64873547 : Blo 1108626 64873547 := bstep (se 1 (by rfl) ⟨48655160, by rfl⟩ : syracuseStep 64873547 = 97310321) B97310321
theorem B6743159 : Blo 1108626 6743159 := bstep (se 1 (by rfl) ⟨5057369, by rfl⟩ : syracuseStep 6743159 = 10114739) B10114739
theorem B1664135 : Blo 1108626 1664135 := bstep (se 1 (by rfl) ⟨1248101, by rfl⟩ : syracuseStep 1664135 = 2496203) B2496203
theorem B1664171 : Blo 1108626 1664171 := bstep (se 1 (by rfl) ⟨1248128, by rfl⟩ : syracuseStep 1664171 = 2496257) B2496257
theorem B1664201 : Blo 1108626 1664201 := bstep (se 2 (by rfl) ⟨624075, by rfl⟩ : syracuseStep 1664201 = 1248151) B1248151
theorem B1664315 : Blo 1108626 1664315 := bstep (se 1 (by rfl) ⟨1248236, by rfl⟩ : syracuseStep 1664315 = 2496473) B2496473
theorem B1664375 : Blo 1108626 1664375 := bstep (se 1 (by rfl) ⟨1248281, by rfl⟩ : syracuseStep 1664375 = 2496563) B2496563
theorem B1664399 : Blo 1108626 1664399 := bstep (se 1 (by rfl) ⟨1248299, by rfl⟩ : syracuseStep 1664399 = 2496599) B2496599
theorem B4744595 : Blo 1108626 4744595 := bstep (se 1 (by rfl) ⟨3558446, by rfl⟩ : syracuseStep 4744595 = 7116893) B7116893
theorem B5629337 : Blo 1108626 5629337 := bstep (se 2 (by rfl) ⟨2111001, by rfl⟩ : syracuseStep 5629337 = 4222003) B4222003
theorem B1664441 : Blo 1108626 1664441 := bstep (se 2 (by rfl) ⟨624165, by rfl⟩ : syracuseStep 1664441 = 1248331) B1248331
theorem B1664519 : Blo 1108626 1664519 := bstep (se 1 (by rfl) ⟨1248389, by rfl⟩ : syracuseStep 1664519 = 2496779) B2496779
theorem B1664555 : Blo 1108626 1664555 := bstep (se 1 (by rfl) ⟨1248416, by rfl⟩ : syracuseStep 1664555 = 2496833) B2496833
theorem B1664585 : Blo 1108626 1664585 := bstep (se 2 (by rfl) ⟨624219, by rfl⟩ : syracuseStep 1664585 = 1248439) B1248439
theorem B1664699 : Blo 1108626 1664699 := bstep (se 1 (by rfl) ⟨1248524, by rfl⟩ : syracuseStep 1664699 = 2497049) B2497049
theorem B1664759 : Blo 1108626 1664759 := bstep (se 1 (by rfl) ⟨1248569, by rfl⟩ : syracuseStep 1664759 = 2497139) B2497139
theorem B1664783 : Blo 1108626 1664783 := bstep (se 1 (by rfl) ⟨1248587, by rfl⟩ : syracuseStep 1664783 = 2497175) B2497175
theorem B1664825 : Blo 1108626 1664825 := bstep (se 2 (by rfl) ⟨624309, by rfl⟩ : syracuseStep 1664825 = 1248619) B1248619
theorem B1664903 : Blo 1108626 1664903 := bstep (se 1 (by rfl) ⟨1248677, by rfl⟩ : syracuseStep 1664903 = 2497355) B2497355
theorem B4220819 : Blo 1108626 4220819 := bstep (se 1 (by rfl) ⟨3165614, by rfl⟩ : syracuseStep 4220819 = 6331229) B6331229
theorem B1664939 : Blo 1108626 1664939 := bstep (se 1 (by rfl) ⟨1248704, by rfl⟩ : syracuseStep 1664939 = 2497409) B2497409
theorem B1664969 : Blo 1108626 1664969 := bstep (se 2 (by rfl) ⟨624363, by rfl⟩ : syracuseStep 1664969 = 1248727) B1248727
theorem B2811905 : Blo 1108626 2811905 := bstep (se 2 (by rfl) ⟨1054464, by rfl⟩ : syracuseStep 2811905 = 2108929) B2108929
theorem B1665083 : Blo 1108626 1665083 := bstep (se 1 (by rfl) ⟨1248812, by rfl⟩ : syracuseStep 1665083 = 2497625) B2497625
theorem B1665143 : Blo 1108626 1665143 := bstep (se 1 (by rfl) ⟨1248857, by rfl⟩ : syracuseStep 1665143 = 2497715) B2497715
theorem B1665167 : Blo 1108626 1665167 := bstep (se 1 (by rfl) ⟨1248875, by rfl⟩ : syracuseStep 1665167 = 2497751) B2497751
theorem B1665209 : Blo 1108626 1665209 := bstep (se 2 (by rfl) ⟨624453, by rfl⟩ : syracuseStep 1665209 = 1248907) B1248907
theorem B1665287 : Blo 1108626 1665287 := bstep (se 1 (by rfl) ⟨1248965, by rfl⟩ : syracuseStep 1665287 = 2497931) B2497931
theorem B1665323 : Blo 1108626 1665323 := bstep (se 1 (by rfl) ⟨1248992, by rfl⟩ : syracuseStep 1665323 = 2497985) B2497985
theorem B1665353 : Blo 1108626 1665353 := bstep (se 2 (by rfl) ⟨624507, by rfl⟩ : syracuseStep 1665353 = 1249015) B1249015
theorem B6318425 : Blo 1108626 6318425 := bstep (se 2 (by rfl) ⟨2369409, by rfl⟩ : syracuseStep 6318425 = 4738819) B4738819
theorem B2812279 : Blo 1108626 2812279 := bstep (se 1 (by rfl) ⟨2109209, by rfl⟩ : syracuseStep 2812279 = 4218419) B4218419
theorem B1665467 : Blo 1108626 1665467 := bstep (se 1 (by rfl) ⟨1249100, by rfl⟩ : syracuseStep 1665467 = 2498201) B2498201
theorem B1665527 : Blo 1108626 1665527 := bstep (se 1 (by rfl) ⟨1249145, by rfl⟩ : syracuseStep 1665527 = 2498291) B2498291
theorem B1665551 : Blo 1108626 1665551 := bstep (se 1 (by rfl) ⟨1249163, by rfl⟩ : syracuseStep 1665551 = 2498327) B2498327
theorem B1665593 : Blo 1108626 1665593 := bstep (se 2 (by rfl) ⟨624597, by rfl⟩ : syracuseStep 1665593 = 1249195) B1249195
theorem B61565507 : Blo 1108626 61565507 := bstep (se 1 (by rfl) ⟨46174130, by rfl⟩ : syracuseStep 61565507 = 92348261) B92348261
theorem B1665671 : Blo 1108626 1665671 := bstep (se 1 (by rfl) ⟨1249253, by rfl⟩ : syracuseStep 1665671 = 2498507) B2498507
theorem B1403563 : Blo 1108626 1403563 := bstep (se 1 (by rfl) ⟨1052672, by rfl⟩ : syracuseStep 1403563 = 2105345) B2105345
theorem B1665707 : Blo 1108626 1665707 := bstep (se 1 (by rfl) ⟨1249280, by rfl⟩ : syracuseStep 1665707 = 2498561) B2498561
theorem B1108667 : Blo 1108626 1108667 := bstep (se 1 (by rfl) ⟨831500, by rfl⟩ : syracuseStep 1108667 = 1663001) B1663001
theorem B1665737 : Blo 1108626 1665737 := bstep (se 2 (by rfl) ⟨624651, by rfl⟩ : syracuseStep 1665737 = 1249303) B1249303
theorem B1108743 : Blo 1108626 1108743 := bstep (se 1 (by rfl) ⟨831557, by rfl⟩ : syracuseStep 1108743 = 1663115) B1663115
theorem B1108751 : Blo 1108626 1108751 := bstep (se 1 (by rfl) ⟨831563, by rfl⟩ : syracuseStep 1108751 = 1663127) B1663127
theorem B6318881 : Blo 1108626 6318881 := bstep (se 2 (by rfl) ⟨2369580, by rfl⟩ : syracuseStep 6318881 = 4739161) B4739161
theorem B2812715 : Blo 1108626 2812715 := bstep (se 1 (by rfl) ⟨2109536, by rfl⟩ : syracuseStep 2812715 = 4219073) B4219073
theorem B1108795 : Blo 1108626 1108795 := bstep (se 1 (by rfl) ⟨831596, by rfl⟩ : syracuseStep 1108795 = 1663193) B1663193
theorem B1665851 : Blo 1108626 1665851 := bstep (se 1 (by rfl) ⟨1249388, by rfl⟩ : syracuseStep 1665851 = 2498777) B2498777
theorem B1665911 : Blo 1108626 1665911 := bstep (se 1 (by rfl) ⟨1249433, by rfl⟩ : syracuseStep 1665911 = 2498867) B2498867
theorem B1108871 : Blo 1108626 1108871 := bstep (se 1 (by rfl) ⟨831653, by rfl⟩ : syracuseStep 1108871 = 1663307) B1663307
theorem B1108879 : Blo 1108626 1108879 := bstep (se 1 (by rfl) ⟨831659, by rfl⟩ : syracuseStep 1108879 = 1663319) B1663319
theorem B1665935 : Blo 1108626 1665935 := bstep (se 1 (by rfl) ⟨1249451, by rfl⟩ : syracuseStep 1665935 = 2498903) B2498903
theorem B1665977 : Blo 1108626 1665977 := bstep (se 2 (by rfl) ⟨624741, by rfl⟩ : syracuseStep 1665977 = 1249483) B1249483
theorem B1108923 : Blo 1108626 1108923 := bstep (se 1 (by rfl) ⟨831692, by rfl⟩ : syracuseStep 1108923 = 1663385) B1663385
theorem B1108999 : Blo 1108626 1108999 := bstep (se 1 (by rfl) ⟨831749, by rfl⟩ : syracuseStep 1108999 = 1663499) B1663499
theorem B1666055 : Blo 1108626 1666055 := bstep (se 1 (by rfl) ⟨1249541, by rfl⟩ : syracuseStep 1666055 = 2499083) B2499083
theorem B1109007 : Blo 1108626 1109007 := bstep (se 1 (by rfl) ⟨831755, by rfl⟩ : syracuseStep 1109007 = 1663511) B1663511
theorem B6319133 : Blo 1108626 6319133 := bstep (se 3 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 6319133 = 2369675) B2369675
theorem B5336093 : Blo 1108626 5336093 := bstep (se 3 (by rfl) ⟨1000517, by rfl⟩ : syracuseStep 5336093 = 2001035) B2001035
theorem B4746269 : Blo 1108626 4746269 := bstep (se 3 (by rfl) ⟨889925, by rfl⟩ : syracuseStep 4746269 = 1779851) B1779851
theorem B1666091 : Blo 1108626 1666091 := bstep (se 1 (by rfl) ⟨1249568, by rfl⟩ : syracuseStep 1666091 = 2499137) B2499137
theorem B1109051 : Blo 1108626 1109051 := bstep (se 1 (by rfl) ⟨831788, by rfl⟩ : syracuseStep 1109051 = 1663577) B1663577
theorem B1666121 : Blo 1108626 1666121 := bstep (se 2 (by rfl) ⟨624795, by rfl⟩ : syracuseStep 1666121 = 1249591) B1249591
theorem B1109127 : Blo 1108626 1109127 := bstep (se 1 (by rfl) ⟨831845, by rfl⟩ : syracuseStep 1109127 = 1663691) B1663691
theorem B1109135 : Blo 1108626 1109135 := bstep (se 1 (by rfl) ⟨831851, by rfl⟩ : syracuseStep 1109135 = 1663703) B1663703
theorem B13692077 : Blo 1108626 13692077 := bstep (se 3 (by rfl) ⟨2567264, by rfl⟩ : syracuseStep 13692077 = 5134529) B5134529
theorem B1109179 : Blo 1108626 1109179 := bstep (se 1 (by rfl) ⟨831884, by rfl⟩ : syracuseStep 1109179 = 1663769) B1663769
theorem B1666235 : Blo 1108626 1666235 := bstep (se 1 (by rfl) ⟨1249676, by rfl⟩ : syracuseStep 1666235 = 2499353) B2499353
theorem B1666295 : Blo 1108626 1666295 := bstep (se 1 (by rfl) ⟨1249721, by rfl⟩ : syracuseStep 1666295 = 2499443) B2499443
theorem B1109255 : Blo 1108626 1109255 := bstep (se 1 (by rfl) ⟨831941, by rfl⟩ : syracuseStep 1109255 = 1663883) B1663883
theorem B1109263 : Blo 1108626 1109263 := bstep (se 1 (by rfl) ⟨831947, by rfl⟩ : syracuseStep 1109263 = 1663895) B1663895
theorem B1666319 : Blo 1108626 1666319 := bstep (se 1 (by rfl) ⟨1249739, by rfl⟩ : syracuseStep 1666319 = 2499479) B2499479
theorem B1109307 : Blo 1108626 1109307 := bstep (se 1 (by rfl) ⟨831980, by rfl⟩ : syracuseStep 1109307 = 1663961) B1663961
theorem B1666361 : Blo 1108626 1666361 := bstep (se 2 (by rfl) ⟨624885, by rfl⟩ : syracuseStep 1666361 = 1249771) B1249771
theorem B12021085 : Blo 1108626 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B1109383 : Blo 1108626 1109383 := bstep (se 1 (by rfl) ⟨832037, by rfl⟩ : syracuseStep 1109383 = 1664075) B1664075
theorem B1666439 : Blo 1108626 1666439 := bstep (se 1 (by rfl) ⟨1249829, by rfl⟩ : syracuseStep 1666439 = 2499659) B2499659
theorem B1109391 : Blo 1108626 1109391 := bstep (se 1 (by rfl) ⟨832043, by rfl⟩ : syracuseStep 1109391 = 1664087) B1664087
theorem B13495697 : Blo 1108626 13495697 := bstep (se 2 (by rfl) ⟨5060886, by rfl⟩ : syracuseStep 13495697 = 10121773) B10121773
theorem B1666475 : Blo 1108626 1666475 := bstep (se 1 (by rfl) ⟨1249856, by rfl⟩ : syracuseStep 1666475 = 2499713) B2499713
theorem B1109435 : Blo 1108626 1109435 := bstep (se 1 (by rfl) ⟨832076, by rfl⟩ : syracuseStep 1109435 = 1664153) B1664153
theorem B1666505 : Blo 1108626 1666505 := bstep (se 2 (by rfl) ⟨624939, by rfl⟩ : syracuseStep 1666505 = 1249879) B1249879
theorem B1109511 : Blo 1108626 1109511 := bstep (se 1 (by rfl) ⟨832133, by rfl⟩ : syracuseStep 1109511 = 1664267) B1664267
theorem B4222475 : Blo 1108626 4222475 := bstep (se 1 (by rfl) ⟨3166856, by rfl⟩ : syracuseStep 4222475 = 6333713) B6333713
theorem B1109519 : Blo 1108626 1109519 := bstep (se 1 (by rfl) ⟨832139, by rfl⟩ : syracuseStep 1109519 = 1664279) B1664279
theorem B1109563 : Blo 1108626 1109563 := bstep (se 1 (by rfl) ⟨832172, by rfl⟩ : syracuseStep 1109563 = 1664345) B1664345
theorem B1666619 : Blo 1108626 1666619 := bstep (se 1 (by rfl) ⟨1249964, by rfl⟩ : syracuseStep 1666619 = 2499929) B2499929
theorem B2813555 : Blo 1108626 2813555 := bstep (se 1 (by rfl) ⟨2110166, by rfl⟩ : syracuseStep 2813555 = 4220333) B4220333
theorem B1404535 : Blo 1108626 1404535 := bstep (se 1 (by rfl) ⟨1053401, by rfl⟩ : syracuseStep 1404535 = 2106803) B2106803
theorem B1666679 : Blo 1108626 1666679 := bstep (se 1 (by rfl) ⟨1250009, by rfl⟩ : syracuseStep 1666679 = 2500019) B2500019
theorem B1109639 : Blo 1108626 1109639 := bstep (se 1 (by rfl) ⟨832229, by rfl⟩ : syracuseStep 1109639 = 1664459) B1664459
theorem B2813575 : Blo 1108626 2813575 := bstep (se 1 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 2813575 = 4220363) B4220363
theorem B1109647 : Blo 1108626 1109647 := bstep (se 1 (by rfl) ⟨832235, by rfl⟩ : syracuseStep 1109647 = 1664471) B1664471
theorem B1666703 : Blo 1108626 1666703 := bstep (se 1 (by rfl) ⟨1250027, by rfl⟩ : syracuseStep 1666703 = 2500055) B2500055
theorem B1666745 : Blo 1108626 1666745 := bstep (se 2 (by rfl) ⟨625029, by rfl⟩ : syracuseStep 1666745 = 1250059) B1250059
theorem B1109691 : Blo 1108626 1109691 := bstep (se 1 (by rfl) ⟨832268, by rfl⟩ : syracuseStep 1109691 = 1664537) B1664537
theorem B1109767 : Blo 1108626 1109767 := bstep (se 1 (by rfl) ⟨832325, by rfl⟩ : syracuseStep 1109767 = 1664651) B1664651
theorem B1666823 : Blo 1108626 1666823 := bstep (se 1 (by rfl) ⟨1250117, by rfl⟩ : syracuseStep 1666823 = 2500235) B2500235
theorem B1109775 : Blo 1108626 1109775 := bstep (se 1 (by rfl) ⟨832331, by rfl⟩ : syracuseStep 1109775 = 1664663) B1664663
theorem B9498383 : Blo 1108626 9498383 := bstep (se 1 (by rfl) ⟨7123787, by rfl⟩ : syracuseStep 9498383 = 14247575) B14247575
theorem B1666859 : Blo 1108626 1666859 := bstep (se 1 (by rfl) ⟨1250144, by rfl⟩ : syracuseStep 1666859 = 2500289) B2500289
theorem B1109819 : Blo 1108626 1109819 := bstep (se 1 (by rfl) ⟨832364, by rfl⟩ : syracuseStep 1109819 = 1664729) B1664729
theorem B1666889 : Blo 1108626 1666889 := bstep (se 2 (by rfl) ⟨625083, by rfl⟩ : syracuseStep 1666889 = 1250167) B1250167
theorem B1109895 : Blo 1108626 1109895 := bstep (se 1 (by rfl) ⟨832421, by rfl⟩ : syracuseStep 1109895 = 1664843) B1664843
theorem B3043207 : Blo 1108626 3043207 := bstep (se 1 (by rfl) ⟨2282405, by rfl⟩ : syracuseStep 3043207 = 4564811) B4564811
theorem B1109903 : Blo 1108626 1109903 := bstep (se 1 (by rfl) ⟨832427, by rfl⟩ : syracuseStep 1109903 = 1664855) B1664855
theorem B2813849 : Blo 1108626 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B4747193 : Blo 1108626 4747193 := bstep (se 2 (by rfl) ⟨1780197, by rfl⟩ : syracuseStep 4747193 = 3560395) B3560395
theorem B5631929 : Blo 1108626 5631929 := bstep (se 2 (by rfl) ⟨2111973, by rfl⟩ : syracuseStep 5631929 = 4223947) B4223947
theorem B1109947 : Blo 1108626 1109947 := bstep (se 1 (by rfl) ⟨832460, by rfl⟩ : syracuseStep 1109947 = 1664921) B1664921
theorem B1404859 : Blo 1108626 1404859 := bstep (se 1 (by rfl) ⟨1053644, by rfl⟩ : syracuseStep 1404859 = 2107289) B2107289
theorem B1667003 : Blo 1108626 1667003 := bstep (se 1 (by rfl) ⟨1250252, by rfl⟩ : syracuseStep 1667003 = 2500505) B2500505
theorem B1667063 : Blo 1108626 1667063 := bstep (se 1 (by rfl) ⟨1250297, by rfl⟩ : syracuseStep 1667063 = 2500595) B2500595
theorem B1110023 : Blo 1108626 1110023 := bstep (se 1 (by rfl) ⟨832517, by rfl⟩ : syracuseStep 1110023 = 1665035) B1665035
theorem B1110031 : Blo 1108626 1110031 := bstep (se 1 (by rfl) ⟨832523, by rfl⟩ : syracuseStep 1110031 = 1665047) B1665047
theorem B1667087 : Blo 1108626 1667087 := bstep (se 1 (by rfl) ⟨1250315, by rfl⟩ : syracuseStep 1667087 = 2500631) B2500631
theorem B1667129 : Blo 1108626 1667129 := bstep (se 2 (by rfl) ⟨625173, by rfl⟩ : syracuseStep 1667129 = 1250347) B1250347
theorem B1110075 : Blo 1108626 1110075 := bstep (se 1 (by rfl) ⟨832556, by rfl⟩ : syracuseStep 1110075 = 1665113) B1665113
theorem B2814011 : Blo 1108626 2814011 := bstep (se 1 (by rfl) ⟨2110508, by rfl⟩ : syracuseStep 2814011 = 4221017) B4221017
theorem B1110151 : Blo 1108626 1110151 := bstep (se 1 (by rfl) ⟨832613, by rfl⟩ : syracuseStep 1110151 = 1665227) B1665227
theorem B1667207 : Blo 1108626 1667207 := bstep (se 1 (by rfl) ⟨1250405, by rfl⟩ : syracuseStep 1667207 = 2500811) B2500811
theorem B1110159 : Blo 1108626 1110159 := bstep (se 1 (by rfl) ⟨832619, by rfl⟩ : syracuseStep 1110159 = 1665239) B1665239
theorem B1667243 : Blo 1108626 1667243 := bstep (se 1 (by rfl) ⟨1250432, by rfl⟩ : syracuseStep 1667243 = 2500865) B2500865
theorem B1110203 : Blo 1108626 1110203 := bstep (se 1 (by rfl) ⟨832652, by rfl⟩ : syracuseStep 1110203 = 1665305) B1665305
theorem B1667273 : Blo 1108626 1667273 := bstep (se 2 (by rfl) ⟨625227, by rfl⟩ : syracuseStep 1667273 = 1250455) B1250455
theorem B1110279 : Blo 1108626 1110279 := bstep (se 1 (by rfl) ⟨832709, by rfl⟩ : syracuseStep 1110279 = 1665419) B1665419
theorem B1110287 : Blo 1108626 1110287 := bstep (se 1 (by rfl) ⟨832715, by rfl⟩ : syracuseStep 1110287 = 1665431) B1665431
theorem B2814223 : Blo 1108626 2814223 := bstep (se 1 (by rfl) ⟨2110667, by rfl⟩ : syracuseStep 2814223 = 4221335) B4221335
theorem B1110331 : Blo 1108626 1110331 := bstep (se 1 (by rfl) ⟨832748, by rfl⟩ : syracuseStep 1110331 = 1665497) B1665497
theorem B1667387 : Blo 1108626 1667387 := bstep (se 1 (by rfl) ⟨1250540, by rfl⟩ : syracuseStep 1667387 = 2501081) B2501081
theorem B1667447 : Blo 1108626 1667447 := bstep (se 1 (by rfl) ⟨1250585, by rfl⟩ : syracuseStep 1667447 = 2501171) B2501171
theorem B1110407 : Blo 1108626 1110407 := bstep (se 1 (by rfl) ⟨832805, by rfl⟩ : syracuseStep 1110407 = 1665611) B1665611
theorem B1110415 : Blo 1108626 1110415 := bstep (se 1 (by rfl) ⟨832811, by rfl⟩ : syracuseStep 1110415 = 1665623) B1665623
theorem B1667471 : Blo 1108626 1667471 := bstep (se 1 (by rfl) ⟨1250603, by rfl⟩ : syracuseStep 1667471 = 2501207) B2501207
theorem B1503631 : Blo 1108626 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B1667513 : Blo 1108626 1667513 := bstep (se 2 (by rfl) ⟨625317, by rfl⟩ : syracuseStep 1667513 = 1250635) B1250635
theorem B1110459 : Blo 1108626 1110459 := bstep (se 1 (by rfl) ⟨832844, by rfl⟩ : syracuseStep 1110459 = 1665689) B1665689
theorem B1110535 : Blo 1108626 1110535 := bstep (se 1 (by rfl) ⟨832901, by rfl⟩ : syracuseStep 1110535 = 1665803) B1665803
theorem B1667591 : Blo 1108626 1667591 := bstep (se 1 (by rfl) ⟨1250693, by rfl⟩ : syracuseStep 1667591 = 2501387) B2501387
theorem B1110543 : Blo 1108626 1110543 := bstep (se 1 (by rfl) ⟨832907, by rfl⟩ : syracuseStep 1110543 = 1665815) B1665815
theorem B2814497 : Blo 1108626 2814497 := bstep (se 2 (by rfl) ⟨1055436, by rfl⟩ : syracuseStep 2814497 = 2110873) B2110873
theorem B1667627 : Blo 1108626 1667627 := bstep (se 1 (by rfl) ⟨1250720, by rfl⟩ : syracuseStep 1667627 = 2501441) B2501441
theorem B1110587 : Blo 1108626 1110587 := bstep (se 1 (by rfl) ⟨832940, by rfl⟩ : syracuseStep 1110587 = 1665881) B1665881
theorem B1667657 : Blo 1108626 1667657 := bstep (se 2 (by rfl) ⟨625371, by rfl⟩ : syracuseStep 1667657 = 1250743) B1250743
theorem B1110663 : Blo 1108626 1110663 := bstep (se 1 (by rfl) ⟨832997, by rfl⟩ : syracuseStep 1110663 = 1665995) B1665995
theorem B1110671 : Blo 1108626 1110671 := bstep (se 1 (by rfl) ⟨833003, by rfl⟩ : syracuseStep 1110671 = 1666007) B1666007
theorem B1110715 : Blo 1108626 1110715 := bstep (se 1 (by rfl) ⟨833036, by rfl⟩ : syracuseStep 1110715 = 1666073) B1666073
theorem B1667771 : Blo 1108626 1667771 := bstep (se 1 (by rfl) ⟨1250828, by rfl⟩ : syracuseStep 1667771 = 2501657) B2501657
theorem B1667831 : Blo 1108626 1667831 := bstep (se 1 (by rfl) ⟨1250873, by rfl⟩ : syracuseStep 1667831 = 2501747) B2501747
theorem B1110791 : Blo 1108626 1110791 := bstep (se 1 (by rfl) ⟨833093, by rfl⟩ : syracuseStep 1110791 = 1666187) B1666187
theorem B1897231 : Blo 1108626 1897231 := bstep (se 1 (by rfl) ⟨1422923, by rfl⟩ : syracuseStep 1897231 = 2845847) B2845847
theorem B17330959 : Blo 1108626 17330959 := bstep (se 1 (by rfl) ⟨12998219, by rfl⟩ : syracuseStep 17330959 = 25996439) B25996439
theorem B1110799 : Blo 1108626 1110799 := bstep (se 1 (by rfl) ⟨833099, by rfl⟩ : syracuseStep 1110799 = 1666199) B1666199
theorem B1667855 : Blo 1108626 1667855 := bstep (se 1 (by rfl) ⟨1250891, by rfl⟩ : syracuseStep 1667855 = 2501783) B2501783
theorem B1667897 : Blo 1108626 1667897 := bstep (se 2 (by rfl) ⟨625461, by rfl⟩ : syracuseStep 1667897 = 1250923) B1250923
theorem B1110843 : Blo 1108626 1110843 := bstep (se 1 (by rfl) ⟨833132, by rfl⟩ : syracuseStep 1110843 = 1666265) B1666265
theorem B26997619 : Blo 1108626 26997619 := bstep (se 1 (by rfl) ⟨20248214, by rfl⟩ : syracuseStep 26997619 = 40496429) B40496429
theorem B1405831 : Blo 1108626 1405831 := bstep (se 1 (by rfl) ⟨1054373, by rfl⟩ : syracuseStep 1405831 = 2108747) B2108747
theorem B1110919 : Blo 1108626 1110919 := bstep (se 1 (by rfl) ⟨833189, by rfl⟩ : syracuseStep 1110919 = 1666379) B1666379
theorem B1667975 : Blo 1108626 1667975 := bstep (se 1 (by rfl) ⟨1250981, by rfl⟩ : syracuseStep 1667975 = 2501963) B2501963
theorem B1110927 : Blo 1108626 1110927 := bstep (se 1 (by rfl) ⟨833195, by rfl⟩ : syracuseStep 1110927 = 1666391) B1666391
theorem B1668011 : Blo 1108626 1668011 := bstep (se 1 (by rfl) ⟨1251008, by rfl⟩ : syracuseStep 1668011 = 2502017) B2502017
theorem B1110971 : Blo 1108626 1110971 := bstep (se 1 (by rfl) ⟨833228, by rfl⟩ : syracuseStep 1110971 = 1666457) B1666457
theorem B1668041 : Blo 1108626 1668041 := bstep (se 2 (by rfl) ⟨625515, by rfl⟩ : syracuseStep 1668041 = 1251031) B1251031
theorem B1111047 : Blo 1108626 1111047 := bstep (se 1 (by rfl) ⟨833285, by rfl⟩ : syracuseStep 1111047 = 1666571) B1666571
theorem B1111055 : Blo 1108626 1111055 := bstep (se 1 (by rfl) ⟨833291, by rfl⟩ : syracuseStep 1111055 = 1666583) B1666583
theorem B1111099 : Blo 1108626 1111099 := bstep (se 1 (by rfl) ⟨833324, by rfl⟩ : syracuseStep 1111099 = 1666649) B1666649
theorem B1668155 : Blo 1108626 1668155 := bstep (se 1 (by rfl) ⟨1251116, by rfl⟩ : syracuseStep 1668155 = 2502233) B2502233
theorem B1668215 : Blo 1108626 1668215 := bstep (se 1 (by rfl) ⟨1251161, by rfl⟩ : syracuseStep 1668215 = 2502323) B2502323
theorem B9499781 : Blo 1108626 9499781 := bstep (se 4 (by rfl) ⟨890604, by rfl⟩ : syracuseStep 9499781 = 1781209) B1781209
theorem B1111175 : Blo 1108626 1111175 := bstep (se 1 (by rfl) ⟨833381, by rfl⟩ : syracuseStep 1111175 = 1666763) B1666763
theorem B1111183 : Blo 1108626 1111183 := bstep (se 1 (by rfl) ⟨833387, by rfl⟩ : syracuseStep 1111183 = 1666775) B1666775
theorem B1668239 : Blo 1108626 1668239 := bstep (se 1 (by rfl) ⟨1251179, by rfl⟩ : syracuseStep 1668239 = 2502359) B2502359
theorem B1668281 : Blo 1108626 1668281 := bstep (se 2 (by rfl) ⟨625605, by rfl⟩ : syracuseStep 1668281 = 1251211) B1251211
theorem B1111227 : Blo 1108626 1111227 := bstep (se 1 (by rfl) ⟨833420, by rfl⟩ : syracuseStep 1111227 = 1666841) B1666841
theorem B1111303 : Blo 1108626 1111303 := bstep (se 1 (by rfl) ⟨833477, by rfl⟩ : syracuseStep 1111303 = 1666955) B1666955
theorem B1668359 : Blo 1108626 1668359 := bstep (se 1 (by rfl) ⟨1251269, by rfl⟩ : syracuseStep 1668359 = 2502539) B2502539
theorem B1111311 : Blo 1108626 1111311 := bstep (se 1 (by rfl) ⟨833483, by rfl⟩ : syracuseStep 1111311 = 1666967) B1666967
theorem B1406251 : Blo 1108626 1406251 := bstep (se 1 (by rfl) ⟨1054688, by rfl⟩ : syracuseStep 1406251 = 2109377) B2109377
theorem B1668395 : Blo 1108626 1668395 := bstep (se 1 (by rfl) ⟨1251296, by rfl⟩ : syracuseStep 1668395 = 2502593) B2502593
theorem B1111355 : Blo 1108626 1111355 := bstep (se 1 (by rfl) ⟨833516, by rfl⟩ : syracuseStep 1111355 = 1667033) B1667033
theorem B1668425 : Blo 1108626 1668425 := bstep (se 2 (by rfl) ⟨625659, by rfl⟩ : syracuseStep 1668425 = 1251319) B1251319
theorem B6321523 : Blo 1108626 6321523 := bstep (se 1 (by rfl) ⟨4741142, by rfl⟩ : syracuseStep 6321523 = 9482285) B9482285
theorem B1111431 : Blo 1108626 1111431 := bstep (se 1 (by rfl) ⟨833573, by rfl⟩ : syracuseStep 1111431 = 1667147) B1667147
theorem B1602959 : Blo 1108626 1602959 := bstep (se 1 (by rfl) ⟨1202219, by rfl⟩ : syracuseStep 1602959 = 2404439) B2404439
theorem B1111439 : Blo 1108626 1111439 := bstep (se 1 (by rfl) ⟨833579, by rfl⟩ : syracuseStep 1111439 = 1667159) B1667159
theorem B1111483 : Blo 1108626 1111483 := bstep (se 1 (by rfl) ⟨833612, by rfl⟩ : syracuseStep 1111483 = 1667225) B1667225
theorem B1668539 : Blo 1108626 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B1668599 : Blo 1108626 1668599 := bstep (se 1 (by rfl) ⟨1251449, by rfl⟩ : syracuseStep 1668599 = 2502899) B2502899
theorem B1111559 : Blo 1108626 1111559 := bstep (se 1 (by rfl) ⟨833669, by rfl⟩ : syracuseStep 1111559 = 1667339) B1667339
theorem B2815499 : Blo 1108626 2815499 := bstep (se 1 (by rfl) ⟨2111624, by rfl⟩ : syracuseStep 2815499 = 4223249) B4223249
theorem B1406479 : Blo 1108626 1406479 := bstep (se 1 (by rfl) ⟨1054859, by rfl⟩ : syracuseStep 1406479 = 2109719) B2109719
theorem B1111567 : Blo 1108626 1111567 := bstep (se 1 (by rfl) ⟨833675, by rfl⟩ : syracuseStep 1111567 = 1667351) B1667351
theorem B1668623 : Blo 1108626 1668623 := bstep (se 1 (by rfl) ⟨1251467, by rfl⟩ : syracuseStep 1668623 = 2502935) B2502935
theorem B1668665 : Blo 1108626 1668665 := bstep (se 2 (by rfl) ⟨625749, by rfl⟩ : syracuseStep 1668665 = 1251499) B1251499
theorem B1111611 : Blo 1108626 1111611 := bstep (se 1 (by rfl) ⟨833708, by rfl⟩ : syracuseStep 1111611 = 1667417) B1667417
theorem B4748867 : Blo 1108626 4748867 := bstep (se 1 (by rfl) ⟨3561650, by rfl⟩ : syracuseStep 4748867 = 7123301) B7123301
theorem B1111687 : Blo 1108626 1111687 := bstep (se 1 (by rfl) ⟨833765, by rfl⟩ : syracuseStep 1111687 = 1667531) B1667531
theorem B1668743 : Blo 1108626 1668743 := bstep (se 1 (by rfl) ⟨1251557, by rfl⟩ : syracuseStep 1668743 = 2503115) B2503115
theorem B1111695 : Blo 1108626 1111695 := bstep (se 1 (by rfl) ⟨833771, by rfl⟩ : syracuseStep 1111695 = 1667543) B1667543
theorem B1668779 : Blo 1108626 1668779 := bstep (se 1 (by rfl) ⟨1251584, by rfl⟩ : syracuseStep 1668779 = 2503169) B2503169
theorem B1111739 : Blo 1108626 1111739 := bstep (se 1 (by rfl) ⟨833804, by rfl⟩ : syracuseStep 1111739 = 1667609) B1667609
theorem B1668809 : Blo 1108626 1668809 := bstep (se 2 (by rfl) ⟨625803, by rfl⟩ : syracuseStep 1668809 = 1251607) B1251607
theorem B1111815 : Blo 1108626 1111815 := bstep (se 1 (by rfl) ⟨833861, by rfl⟩ : syracuseStep 1111815 = 1667723) B1667723
theorem B1111823 : Blo 1108626 1111823 := bstep (se 1 (by rfl) ⟨833867, by rfl⟩ : syracuseStep 1111823 = 1667735) B1667735
theorem B1111867 : Blo 1108626 1111867 := bstep (se 1 (by rfl) ⟨833900, by rfl⟩ : syracuseStep 1111867 = 1667801) B1667801
theorem B1668923 : Blo 1108626 1668923 := bstep (se 1 (by rfl) ⟨1251692, by rfl⟩ : syracuseStep 1668923 = 2503385) B2503385
theorem B1111943 : Blo 1108626 1111943 := bstep (se 1 (by rfl) ⟨833957, by rfl⟩ : syracuseStep 1111943 = 1667915) B1667915
theorem B1111951 : Blo 1108626 1111951 := bstep (se 1 (by rfl) ⟨833963, by rfl⟩ : syracuseStep 1111951 = 1667927) B1667927
theorem B1111995 : Blo 1108626 1111995 := bstep (se 1 (by rfl) ⟨833996, by rfl⟩ : syracuseStep 1111995 = 1667993) B1667993
theorem B11990987 : Blo 1108626 11990987 := bstep (se 1 (by rfl) ⟨8993240, by rfl⟩ : syracuseStep 11990987 = 17986481) B17986481
theorem B5994499 : Blo 1108626 5994499 := bstep (se 1 (by rfl) ⟨4495874, by rfl⟩ : syracuseStep 5994499 = 8991749) B8991749
theorem B1112071 : Blo 1108626 1112071 := bstep (se 1 (by rfl) ⟨834053, by rfl⟩ : syracuseStep 1112071 = 1668107) B1668107
theorem B1112079 : Blo 1108626 1112079 := bstep (se 1 (by rfl) ⟨834059, by rfl⟩ : syracuseStep 1112079 = 1668119) B1668119
theorem B24049709 : Blo 1108626 24049709 := bstep (se 3 (by rfl) ⟨4509320, by rfl⟩ : syracuseStep 24049709 = 9018641) B9018641
theorem B1112123 : Blo 1108626 1112123 := bstep (se 1 (by rfl) ⟨834092, by rfl⟩ : syracuseStep 1112123 = 1668185) B1668185
theorem B1112199 : Blo 1108626 1112199 := bstep (se 1 (by rfl) ⟨834149, by rfl⟩ : syracuseStep 1112199 = 1668299) B1668299
theorem B1112207 : Blo 1108626 1112207 := bstep (se 1 (by rfl) ⟨834155, by rfl⟩ : syracuseStep 1112207 = 1668311) B1668311
theorem B2816147 : Blo 1108626 2816147 := bstep (se 1 (by rfl) ⟨2112110, by rfl⟩ : syracuseStep 2816147 = 4224221) B4224221
theorem B1112251 : Blo 1108626 1112251 := bstep (se 1 (by rfl) ⟨834188, by rfl⟩ : syracuseStep 1112251 = 1668377) B1668377
theorem B1407223 : Blo 1108626 1407223 := bstep (se 1 (by rfl) ⟨1055417, by rfl⟩ : syracuseStep 1407223 = 2110835) B2110835
theorem B1112327 : Blo 1108626 1112327 := bstep (se 1 (by rfl) ⟨834245, by rfl⟩ : syracuseStep 1112327 = 1668491) B1668491
theorem B1112335 : Blo 1108626 1112335 := bstep (se 1 (by rfl) ⟨834251, by rfl⟩ : syracuseStep 1112335 = 1668503) B1668503
theorem B1112379 : Blo 1108626 1112379 := bstep (se 1 (by rfl) ⟨834284, by rfl⟩ : syracuseStep 1112379 = 1668569) B1668569
theorem B1112455 : Blo 1108626 1112455 := bstep (se 1 (by rfl) ⟨834341, by rfl⟩ : syracuseStep 1112455 = 1668683) B1668683
theorem B1112463 : Blo 1108626 1112463 := bstep (se 1 (by rfl) ⟨834347, by rfl⟩ : syracuseStep 1112463 = 1668695) B1668695
theorem B10680761 : Blo 1108626 10680761 := bstep (se 2 (by rfl) ⟨4005285, by rfl⟩ : syracuseStep 10680761 = 8010571) B8010571
theorem B1112507 : Blo 1108626 1112507 := bstep (se 1 (by rfl) ⟨834380, by rfl⟩ : syracuseStep 1112507 = 1668761) B1668761
theorem B1112583 : Blo 1108626 1112583 := bstep (se 1 (by rfl) ⟨834437, by rfl⟩ : syracuseStep 1112583 = 1668875) B1668875
theorem B1112591 : Blo 1108626 1112591 := bstep (se 1 (by rfl) ⟨834443, by rfl⟩ : syracuseStep 1112591 = 1668887) B1668887
theorem B1407547 : Blo 1108626 1407547 := bstep (se 1 (by rfl) ⟨1055660, by rfl⟩ : syracuseStep 1407547 = 2111321) B2111321
theorem B6322981 : Blo 1108626 6322981 := bstep (se 4 (by rfl) ⟨592779, by rfl⟩ : syracuseStep 6322981 = 1185559) B1185559
theorem B1408043 : Blo 1108626 1408043 := bstep (se 1 (by rfl) ⟨1056032, by rfl⟩ : syracuseStep 1408043 = 2112065) B2112065
theorem B2849993 : Blo 1108626 2849993 := bstep (se 2 (by rfl) ⟨1068747, by rfl⟩ : syracuseStep 2849993 = 2137495) B2137495
theorem B7109869 : Blo 1108626 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B6323507 : Blo 1108626 6323507 := bstep (se 1 (by rfl) ⟨4742630, by rfl⟩ : syracuseStep 6323507 = 9485261) B9485261
theorem B19005029 : Blo 1108626 19005029 := bstep (se 4 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 19005029 = 3563443) B3563443
theorem B1998607 : Blo 1108626 1998607 := bstep (se 1 (by rfl) ⟨1498955, by rfl⟩ : syracuseStep 1998607 = 2997911) B2997911
theorem B19201843 : Blo 1108626 19201843 := bstep (se 1 (by rfl) ⟨14401382, by rfl⟩ : syracuseStep 19201843 = 28802765) B28802765
theorem B32047001 : Blo 1108626 32047001 := bstep (se 2 (by rfl) ⟨12017625, by rfl⟩ : syracuseStep 32047001 = 24035251) B24035251
theorem B21331997 : Blo 1108626 21331997 := bstep (se 3 (by rfl) ⟨3999749, by rfl⟩ : syracuseStep 21331997 = 7999499) B7999499
theorem B1999247 : Blo 1108626 1999247 := bstep (se 1 (by rfl) ⟨1499435, by rfl⟩ : syracuseStep 1999247 = 2998871) B2998871
theorem B9503405 : Blo 1108626 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B79136185 : Blo 1108626 79136185 := bstep (se 2 (by rfl) ⟨29676069, by rfl⟩ : syracuseStep 79136185 = 59352139) B59352139
theorem B2000747 : Blo 1108626 2000747 := bstep (se 1 (by rfl) ⟨1500560, by rfl⟩ : syracuseStep 2000747 = 3001121) B3001121
theorem B1247431 : Blo 1108626 1247431 := bstep (se 1 (by rfl) ⟨935573, by rfl⟩ : syracuseStep 1247431 = 1871147) B1871147
theorem B2001295 : Blo 1108626 2001295 := bstep (se 1 (by rfl) ⟨1500971, by rfl⟩ : syracuseStep 2001295 = 3001943) B3001943
theorem B17074583 : Blo 1108626 17074583 := bstep (se 1 (by rfl) ⟨12805937, by rfl⟩ : syracuseStep 17074583 = 25611875) B25611875
theorem B23989067 : Blo 1108626 23989067 := bstep (se 1 (by rfl) ⟨17991800, by rfl⟩ : syracuseStep 23989067 = 35983601) B35983601
theorem B4000673 : Blo 1108626 4000673 := bstep (se 2 (by rfl) ⟨1500252, by rfl⟩ : syracuseStep 4000673 = 3000505) B3000505
theorem B2853895 : Blo 1108626 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B43256855 : Blo 1108626 43256855 := bstep (se 1 (by rfl) ⟨32442641, by rfl⟩ : syracuseStep 43256855 = 64885283) B64885283
theorem B1248295 : Blo 1108626 1248295 := bstep (se 1 (by rfl) ⟨936221, by rfl⟩ : syracuseStep 1248295 = 1872443) B1872443
theorem B2853967 : Blo 1108626 2853967 := bstep (se 1 (by rfl) ⟨2140475, by rfl⟩ : syracuseStep 2853967 = 4280951) B4280951
theorem B8228087 : Blo 1108626 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B12029219 : Blo 1108626 12029219 := bstep (se 1 (by rfl) ⟨9021914, by rfl⟩ : syracuseStep 12029219 = 18043829) B18043829
theorem B1871417 : Blo 1108626 1871417 := bstep (se 2 (by rfl) ⟨701781, by rfl⟩ : syracuseStep 1871417 = 1403563) B1403563
theorem B12193517 : Blo 1108626 12193517 := bstep (se 3 (by rfl) ⟨2286284, by rfl⟩ : syracuseStep 12193517 = 4572569) B4572569
theorem B9015299 : Blo 1108626 9015299 := bstep (se 1 (by rfl) ⟨6761474, by rfl⟩ : syracuseStep 9015299 = 13522949) B13522949
theorem B1282171 : Blo 1108626 1282171 := bstep (se 1 (by rfl) ⟨961628, by rfl⟩ : syracuseStep 1282171 = 1923257) B1923257
theorem B1872119 : Blo 1108626 1872119 := bstep (se 1 (by rfl) ⟨1404089, by rfl⟩ : syracuseStep 1872119 = 2808179) B2808179
theorem B16028113 : Blo 1108626 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B6328813 : Blo 1108626 6328813 := bstep (se 3 (by rfl) ⟨1186652, by rfl⟩ : syracuseStep 6328813 = 2373305) B2373305
theorem B2495015 : Blo 1108626 2495015 := bstep (se 1 (by rfl) ⟨1871261, by rfl⟩ : syracuseStep 2495015 = 3742523) B3742523
theorem B1872463 : Blo 1108626 1872463 := bstep (se 1 (by rfl) ⟨1404347, by rfl⟩ : syracuseStep 1872463 = 2808695) B2808695
theorem B1249915 : Blo 1108626 1249915 := bstep (se 1 (by rfl) ⟨937436, by rfl⟩ : syracuseStep 1249915 = 1874873) B1874873
theorem B1872713 : Blo 1108626 1872713 := bstep (se 2 (by rfl) ⟨702267, by rfl⟩ : syracuseStep 1872713 = 1404535) B1404535
theorem B2495339 : Blo 1108626 2495339 := bstep (se 1 (by rfl) ⟨1871504, by rfl⟩ : syracuseStep 2495339 = 3743009) B3743009
theorem B2495393 : Blo 1108626 2495393 := bstep (se 2 (by rfl) ⟨935772, by rfl⟩ : syracuseStep 2495393 = 1871545) B1871545
theorem B19502045 : Blo 1108626 19502045 := bstep (se 3 (by rfl) ⟨3656633, by rfl⟩ : syracuseStep 19502045 = 7313267) B7313267
theorem B7214147 : Blo 1108626 7214147 := bstep (se 1 (by rfl) ⟨5410610, by rfl⟩ : syracuseStep 7214147 = 10821221) B10821221
theorem B1250383 : Blo 1108626 1250383 := bstep (se 1 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 1250383 = 1875575) B1875575
theorem B2495735 : Blo 1108626 2495735 := bstep (se 1 (by rfl) ⟨1871801, by rfl⟩ : syracuseStep 2495735 = 3743603) B3743603
theorem B1873145 : Blo 1108626 1873145 := bstep (se 2 (by rfl) ⟨702429, by rfl⟩ : syracuseStep 1873145 = 1404859) B1404859
theorem B1873327 : Blo 1108626 1873327 := bstep (se 1 (by rfl) ⟨1404995, by rfl⟩ : syracuseStep 1873327 = 2809991) B2809991
theorem B1250779 : Blo 1108626 1250779 := bstep (se 1 (by rfl) ⟨938084, by rfl⟩ : syracuseStep 1250779 = 1876169) B1876169
theorem B1873415 : Blo 1108626 1873415 := bstep (se 1 (by rfl) ⟨1405061, by rfl⟩ : syracuseStep 1873415 = 2810123) B2810123
theorem B1578695 : Blo 1108626 1578695 := bstep (se 1 (by rfl) ⟨1184021, by rfl⟩ : syracuseStep 1578695 = 2368043) B2368043
theorem B2496329 : Blo 1108626 2496329 := bstep (se 2 (by rfl) ⟨936123, by rfl⟩ : syracuseStep 2496329 = 1872247) B1872247
theorem B1873759 : Blo 1108626 1873759 := bstep (se 1 (by rfl) ⟨1405319, by rfl⟩ : syracuseStep 1873759 = 2810639) B2810639
theorem B9017183 : Blo 1108626 9017183 := bstep (se 1 (by rfl) ⟨6762887, by rfl⟩ : syracuseStep 9017183 = 13525775) B13525775
theorem B2004841 : Blo 1108626 2004841 := bstep (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) B1503631
theorem B1251247 : Blo 1108626 1251247 := bstep (se 1 (by rfl) ⟨938435, by rfl⟩ : syracuseStep 1251247 = 1876871) B1876871
theorem B1873847 : Blo 1108626 1873847 := bstep (se 1 (by rfl) ⟨1405385, by rfl⟩ : syracuseStep 1873847 = 2810771) B2810771
theorem B4495439 : Blo 1108626 4495439 := bstep (se 1 (by rfl) ⟨3371579, by rfl⟩ : syracuseStep 4495439 = 6743159) B6743159
theorem B1251679 : Blo 1108626 1251679 := bstep (se 1 (by rfl) ⟨938759, by rfl⟩ : syracuseStep 1251679 = 1877519) B1877519
theorem B2529641 : Blo 1108626 2529641 := bstep (se 2 (by rfl) ⟨948615, by rfl⟩ : syracuseStep 2529641 = 1897231) B1897231
theorem B23107945 : Blo 1108626 23107945 := bstep (se 2 (by rfl) ⟨8665479, by rfl⟩ : syracuseStep 23107945 = 17330959) B17330959
theorem B1579447 : Blo 1108626 1579447 := bstep (se 1 (by rfl) ⟨1184585, by rfl⟩ : syracuseStep 1579447 = 2369171) B2369171
theorem B1874441 : Blo 1108626 1874441 := bstep (se 2 (by rfl) ⟨702915, by rfl⟩ : syracuseStep 1874441 = 1405831) B1405831
theorem B5708321 : Blo 1108626 5708321 := bstep (se 2 (by rfl) ⟨2140620, by rfl⟩ : syracuseStep 5708321 = 4281241) B4281241
theorem B2497121 : Blo 1108626 2497121 := bstep (se 2 (by rfl) ⟨936420, by rfl⟩ : syracuseStep 2497121 = 1872841) B1872841
theorem B1776251 : Blo 1108626 1776251 := bstep (se 1 (by rfl) ⟨1332188, by rfl⟩ : syracuseStep 1776251 = 2664377) B2664377
theorem B1874603 : Blo 1108626 1874603 := bstep (se 1 (by rfl) ⟨1405952, by rfl⟩ : syracuseStep 1874603 = 2811905) B2811905
theorem B2169593 : Blo 1108626 2169593 := bstep (se 2 (by rfl) ⟨813597, by rfl⟩ : syracuseStep 2169593 = 1627195) B1627195
theorem B2497463 : Blo 1108626 2497463 := bstep (se 1 (by rfl) ⟨1873097, by rfl⟩ : syracuseStep 2497463 = 3746195) B3746195
theorem B3742739 : Blo 1108626 3742739 := bstep (se 1 (by rfl) ⟨2807054, by rfl⟩ : syracuseStep 3742739 = 5614109) B5614109
theorem B1875001 : Blo 1108626 1875001 := bstep (se 2 (by rfl) ⟨703125, by rfl⟩ : syracuseStep 1875001 = 1406251) B1406251
theorem B1776763 : Blo 1108626 1776763 := bstep (se 1 (by rfl) ⟨1332572, by rfl⟩ : syracuseStep 1776763 = 2665145) B2665145
theorem B8428697 : Blo 1108626 8428697 := bstep (se 2 (by rfl) ⟨3160761, by rfl⟩ : syracuseStep 8428697 = 6321523) B6321523
theorem B1875143 : Blo 1108626 1875143 := bstep (se 1 (by rfl) ⟨1406357, by rfl⟩ : syracuseStep 1875143 = 2812715) B2812715
theorem B3743063 : Blo 1108626 3743063 := bstep (se 1 (by rfl) ⟨2807297, by rfl⟩ : syracuseStep 3743063 = 5614595) B5614595
theorem B1875305 : Blo 1108626 1875305 := bstep (se 2 (by rfl) ⟨703239, by rfl⟩ : syracuseStep 1875305 = 1406479) B1406479
theorem B2498057 : Blo 1108626 2498057 := bstep (se 2 (by rfl) ⟨936771, by rfl⟩ : syracuseStep 2498057 = 1873543) B1873543
theorem B2105003 : Blo 1108626 2105003 := bstep (se 1 (by rfl) ⟨1578752, by rfl⟩ : syracuseStep 2105003 = 3157505) B3157505
theorem B1875703 : Blo 1108626 1875703 := bstep (se 1 (by rfl) ⟨1406777, by rfl⟩ : syracuseStep 1875703 = 2813555) B2813555
theorem B9248579 : Blo 1108626 9248579 := bstep (se 1 (by rfl) ⟨6936434, by rfl⟩ : syracuseStep 9248579 = 13872869) B13872869
theorem B1777481 : Blo 1108626 1777481 := bstep (se 2 (by rfl) ⟨666555, by rfl⟩ : syracuseStep 1777481 = 1333111) B1333111
theorem B2498399 : Blo 1108626 2498399 := bstep (se 1 (by rfl) ⟨1873799, by rfl⟩ : syracuseStep 2498399 = 3747599) B3747599
theorem B6332255 : Blo 1108626 6332255 := bstep (se 1 (by rfl) ⟨4749191, by rfl⟩ : syracuseStep 6332255 = 9498383) B9498383
theorem B1580905 : Blo 1108626 1580905 := bstep (se 2 (by rfl) ⟨592839, by rfl⟩ : syracuseStep 1580905 = 1185679) B1185679
theorem B1777583 : Blo 1108626 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B1875899 : Blo 1108626 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B1777673 : Blo 1108626 1777673 := bstep (se 2 (by rfl) ⟨666627, by rfl⟩ : syracuseStep 1777673 = 1333255) B1333255
theorem B46768141 : Blo 1108626 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B2498579 : Blo 1108626 2498579 := bstep (se 1 (by rfl) ⟨1873934, by rfl⟩ : syracuseStep 2498579 = 3747869) B3747869
theorem B1876007 : Blo 1108626 1876007 := bstep (se 1 (by rfl) ⟨1407005, by rfl⟩ : syracuseStep 1876007 = 2814011) B2814011
theorem B1876297 : Blo 1108626 1876297 := bstep (se 2 (by rfl) ⟨703611, by rfl⟩ : syracuseStep 1876297 = 1407223) B1407223
theorem B15212875 : Blo 1108626 15212875 := bstep (se 1 (by rfl) ⟨11409656, by rfl⟩ : syracuseStep 15212875 = 22819313) B22819313
theorem B2498921 : Blo 1108626 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B1876331 : Blo 1108626 1876331 := bstep (se 1 (by rfl) ⟨1407248, by rfl⟩ : syracuseStep 1876331 = 2814497) B2814497
theorem B3744143 : Blo 1108626 3744143 := bstep (se 1 (by rfl) ⟨2808107, by rfl⟩ : syracuseStep 3744143 = 5616215) B5616215
theorem B23142971 : Blo 1108626 23142971 := bstep (se 1 (by rfl) ⟨17357228, by rfl⟩ : syracuseStep 23142971 = 34714457) B34714457
theorem B3744467 : Blo 1108626 3744467 := bstep (se 1 (by rfl) ⟨2808350, by rfl⟩ : syracuseStep 3744467 = 5616701) B5616701
theorem B1876729 : Blo 1108626 1876729 := bstep (se 2 (by rfl) ⟨703773, by rfl⟩ : syracuseStep 1876729 = 1407547) B1407547
theorem B6333187 : Blo 1108626 6333187 := bstep (se 1 (by rfl) ⟨4749890, by rfl⟩ : syracuseStep 6333187 = 9499781) B9499781
theorem B2499515 : Blo 1108626 2499515 := bstep (se 1 (by rfl) ⟨1874636, by rfl⟩ : syracuseStep 2499515 = 3749273) B3749273
theorem B1876999 : Blo 1108626 1876999 := bstep (se 1 (by rfl) ⟨1407749, by rfl⟩ : syracuseStep 1876999 = 2815499) B2815499
theorem B8430641 : Blo 1108626 8430641 := bstep (se 2 (by rfl) ⟨3161490, by rfl⟩ : syracuseStep 8430641 = 6322981) B6322981
theorem B2499641 : Blo 1108626 2499641 := bstep (se 2 (by rfl) ⟨937365, by rfl⟩ : syracuseStep 2499641 = 1874731) B1874731
theorem B7611671 : Blo 1108626 7611671 := bstep (se 1 (by rfl) ⟨5708753, by rfl⟩ : syracuseStep 7611671 = 11417507) B11417507
theorem B2106719 : Blo 1108626 2106719 := bstep (se 1 (by rfl) ⟨1580039, by rfl⟩ : syracuseStep 2106719 = 3160079) B3160079
theorem B16033139 : Blo 1108626 16033139 := bstep (se 1 (by rfl) ⟨12024854, by rfl⟩ : syracuseStep 16033139 = 24049709) B24049709
theorem B2499983 : Blo 1108626 2499983 := bstep (se 1 (by rfl) ⟨1874987, by rfl⟩ : syracuseStep 2499983 = 3749975) B3749975
theorem B1877431 : Blo 1108626 1877431 := bstep (se 1 (by rfl) ⟨1408073, by rfl⟩ : syracuseStep 1877431 = 2816147) B2816147
theorem B102409829 : Blo 1108626 102409829 := bstep (se 4 (by rfl) ⟨9600921, by rfl⟩ : syracuseStep 102409829 = 19201843) B19201843
theorem B7120507 : Blo 1108626 7120507 := bstep (se 1 (by rfl) ⟨5340380, by rfl⟩ : syracuseStep 7120507 = 10680761) B10680761
theorem B9479825 : Blo 1108626 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B2500307 : Blo 1108626 2500307 := bstep (se 1 (by rfl) ⟨1875230, by rfl⟩ : syracuseStep 2500307 = 3750461) B3750461
theorem B2107129 : Blo 1108626 2107129 := bstep (se 2 (by rfl) ⟨790173, by rfl⟩ : syracuseStep 2107129 = 1580347) B1580347
theorem B4269943 : Blo 1108626 4269943 := bstep (se 1 (by rfl) ⟨3202457, by rfl⟩ : syracuseStep 4269943 = 6404915) B6404915
theorem B3745655 : Blo 1108626 3745655 := bstep (se 1 (by rfl) ⟨2809241, by rfl⟩ : syracuseStep 3745655 = 5618483) B5618483
theorem B3745871 : Blo 1108626 3745871 := bstep (se 1 (by rfl) ⟨2809403, by rfl⟩ : syracuseStep 3745871 = 5618807) B5618807
theorem B2107471 : Blo 1108626 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B1583183 : Blo 1108626 1583183 := bstep (se 1 (by rfl) ⟨1187387, by rfl⟩ : syracuseStep 1583183 = 2374775) B2374775
theorem B1124447 : Blo 1108626 1124447 := bstep (se 1 (by rfl) ⟨843335, by rfl⟩ : syracuseStep 1124447 = 1686671) B1686671
theorem B2107721 : Blo 1108626 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B2664809 : Blo 1108626 2664809 := bstep (se 2 (by rfl) ⟨999303, by rfl⟩ : syracuseStep 2664809 = 1998607) B1998607
theorem B3746249 : Blo 1108626 3746249 := bstep (se 2 (by rfl) ⟨1404843, by rfl⟩ : syracuseStep 3746249 = 2809687) B2809687
theorem B2501243 : Blo 1108626 2501243 := bstep (se 1 (by rfl) ⟨1875932, by rfl⟩ : syracuseStep 2501243 = 3751865) B3751865
theorem B3746519 : Blo 1108626 3746519 := bstep (se 1 (by rfl) ⟨2809889, by rfl⟩ : syracuseStep 3746519 = 5619779) B5619779
theorem B2501369 : Blo 1108626 2501369 := bstep (se 2 (by rfl) ⟨938013, by rfl⟩ : syracuseStep 2501369 = 1876027) B1876027
theorem B3746735 : Blo 1108626 3746735 := bstep (se 1 (by rfl) ⟨2810051, by rfl⟩ : syracuseStep 3746735 = 5620103) B5620103
theorem B2501639 : Blo 1108626 2501639 := bstep (se 1 (by rfl) ⟨1876229, by rfl⟩ : syracuseStep 2501639 = 3752459) B3752459
theorem B3157049 : Blo 1108626 3157049 := bstep (se 2 (by rfl) ⟨1183893, by rfl⟩ : syracuseStep 3157049 = 2367787) B2367787
theorem B2501711 : Blo 1108626 2501711 := bstep (se 1 (by rfl) ⟨1876283, by rfl⟩ : syracuseStep 2501711 = 3752567) B3752567
theorem B3157163 : Blo 1108626 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B2108587 : Blo 1108626 2108587 := bstep (se 1 (by rfl) ⟨1581440, by rfl⟩ : syracuseStep 2108587 = 3162881) B3162881
theorem B2108663 : Blo 1108626 2108663 := bstep (se 1 (by rfl) ⟨1581497, by rfl⟩ : syracuseStep 2108663 = 3162995) B3162995
theorem B4500937 : Blo 1108626 4500937 := bstep (se 2 (by rfl) ⟨1687851, by rfl⟩ : syracuseStep 4500937 = 3375703) B3375703
theorem B2108891 : Blo 1108626 2108891 := bstep (se 1 (by rfl) ⟨1581668, by rfl⟩ : syracuseStep 2108891 = 3163337) B3163337
theorem B2502107 : Blo 1108626 2502107 := bstep (se 1 (by rfl) ⟨1876580, by rfl⟩ : syracuseStep 2502107 = 3753161) B3753161
theorem B5615243 : Blo 1108626 5615243 := bstep (se 1 (by rfl) ⟨4211432, by rfl⟩ : syracuseStep 5615243 = 8422865) B8422865
theorem B2502575 : Blo 1108626 2502575 := bstep (se 1 (by rfl) ⟨1876931, by rfl⟩ : syracuseStep 2502575 = 3753863) B3753863
theorem B1781767 : Blo 1108626 1781767 := bstep (se 1 (by rfl) ⟨1336325, by rfl⟩ : syracuseStep 1781767 = 2672651) B2672651
theorem B2502827 : Blo 1108626 2502827 := bstep (se 1 (by rfl) ⟨1877120, by rfl⟩ : syracuseStep 2502827 = 3754241) B3754241
theorem B4272527 : Blo 1108626 4272527 := bstep (se 1 (by rfl) ⟨3204395, by rfl⟩ : syracuseStep 4272527 = 6408791) B6408791
theorem B12661271 : Blo 1108626 12661271 := bstep (se 1 (by rfl) ⟨9495953, by rfl⟩ : syracuseStep 12661271 = 18991907) B18991907
theorem B2110151 : Blo 1108626 2110151 := bstep (se 1 (by rfl) ⟨1582613, by rfl⟩ : syracuseStep 2110151 = 3165227) B3165227
theorem B2503367 : Blo 1108626 2503367 := bstep (se 1 (by rfl) ⟨1877525, by rfl⟩ : syracuseStep 2503367 = 3755051) B3755051
theorem B2110303 : Blo 1108626 2110303 := bstep (se 1 (by rfl) ⟨1582727, by rfl⟩ : syracuseStep 2110303 = 3165455) B3165455
theorem B4502459 : Blo 1108626 4502459 := bstep (se 1 (by rfl) ⟨3376844, by rfl⟩ : syracuseStep 4502459 = 6753689) B6753689
theorem B8008753 : Blo 1108626 8008753 := bstep (se 2 (by rfl) ⟨3003282, by rfl⟩ : syracuseStep 8008753 = 6006565) B6006565
theorem B18035779 : Blo 1108626 18035779 := bstep (se 1 (by rfl) ⟨13526834, by rfl⟩ : syracuseStep 18035779 = 27053669) B27053669
theorem B12629195 : Blo 1108626 12629195 := bstep (se 1 (by rfl) ⟨9471896, by rfl⟩ : syracuseStep 12629195 = 18943793) B18943793
theorem B3749111 : Blo 1108626 3749111 := bstep (se 1 (by rfl) ⟨2811833, by rfl⟩ : syracuseStep 3749111 = 5623667) B5623667
theorem B16430501 : Blo 1108626 16430501 := bstep (se 4 (by rfl) ⟨1540359, by rfl⟩ : syracuseStep 16430501 = 3080719) B3080719
theorem B3552731 : Blo 1108626 3552731 := bstep (se 1 (by rfl) ⟨2664548, by rfl⟩ : syracuseStep 3552731 = 5329097) B5329097
theorem B3159577 : Blo 1108626 3159577 := bstep (se 2 (by rfl) ⟨1184841, by rfl⟩ : syracuseStep 3159577 = 2369683) B2369683
theorem B3749435 : Blo 1108626 3749435 := bstep (se 1 (by rfl) ⟨2812076, by rfl⟩ : syracuseStep 3749435 = 5624153) B5624153
theorem B3749705 : Blo 1108626 3749705 := bstep (se 2 (by rfl) ⟨1406139, by rfl⟩ : syracuseStep 3749705 = 2812279) B2812279
theorem B534034781 : Blo 1108626 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B4209367 : Blo 1108626 4209367 := bstep (se 1 (by rfl) ⟨3157025, by rfl⟩ : syracuseStep 4209367 = 6314051) B6314051
theorem B2112247 : Blo 1108626 2112247 := bstep (se 1 (by rfl) ⟨1584185, by rfl⟩ : syracuseStep 2112247 = 3168371) B3168371
theorem B3750839 : Blo 1108626 3750839 := bstep (se 1 (by rfl) ⟨2813129, by rfl⟩ : syracuseStep 3750839 = 5626259) B5626259
theorem B4209671 : Blo 1108626 4209671 := bstep (se 1 (by rfl) ⟨3157253, by rfl⟩ : syracuseStep 4209671 = 6314507) B6314507
theorem B25607447 : Blo 1108626 25607447 := bstep (se 1 (by rfl) ⟨19205585, by rfl⟩ : syracuseStep 25607447 = 38411171) B38411171
theorem B4210157 : Blo 1108626 4210157 := bstep (se 3 (by rfl) ⟨789404, by rfl⟩ : syracuseStep 4210157 = 1578809) B1578809
theorem B3751433 : Blo 1108626 3751433 := bstep (se 2 (by rfl) ⟨1406787, by rfl⟩ : syracuseStep 3751433 = 2813575) B2813575
theorem B3555191 : Blo 1108626 3555191 := bstep (se 1 (by rfl) ⟨2666393, by rfl⟩ : syracuseStep 3555191 = 5332787) B5332787
theorem B5619617 : Blo 1108626 5619617 := bstep (se 2 (by rfl) ⟨2107356, by rfl⟩ : syracuseStep 5619617 = 4214713) B4214713
theorem B10141625 : Blo 1108626 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B7127297 : Blo 1108626 7127297 := bstep (se 2 (by rfl) ⟨2672736, by rfl⟩ : syracuseStep 7127297 = 5345473) B5345473
theorem B13517117 : Blo 1108626 13517117 := bstep (se 3 (by rfl) ⟨2534459, by rfl⟩ : syracuseStep 13517117 = 5068919) B5068919
theorem B3752297 : Blo 1108626 3752297 := bstep (se 2 (by rfl) ⟨1407111, by rfl⟩ : syracuseStep 3752297 = 2814223) B2814223
theorem B3162493 : Blo 1108626 3162493 := bstep (se 3 (by rfl) ⟨592967, by rfl⟩ : syracuseStep 3162493 = 1185935) B1185935
theorem B27378199 : Blo 1108626 27378199 := bstep (se 1 (by rfl) ⟨20533649, by rfl⟩ : syracuseStep 27378199 = 41067299) B41067299
theorem B4211297 : Blo 1108626 4211297 := bstep (se 2 (by rfl) ⟨1579236, by rfl⟩ : syracuseStep 4211297 = 3158473) B3158473
theorem B3162721 : Blo 1108626 3162721 := bstep (se 2 (by rfl) ⟨1186020, by rfl⟩ : syracuseStep 3162721 = 2372041) B2372041
theorem B3425017 : Blo 1108626 3425017 := bstep (se 2 (by rfl) ⟨1284381, by rfl⟩ : syracuseStep 3425017 = 2568763) B2568763
theorem B1688495 : Blo 1108626 1688495 := bstep (se 1 (by rfl) ⟨1266371, by rfl⟩ : syracuseStep 1688495 = 2532743) B2532743
theorem B3163063 : Blo 1108626 3163063 := bstep (se 1 (by rfl) ⟨2372297, by rfl⟩ : syracuseStep 3163063 = 4744595) B4744595
theorem B3752891 : Blo 1108626 3752891 := bstep (se 1 (by rfl) ⟨2814668, by rfl⟩ : syracuseStep 3752891 = 5629337) B5629337
theorem B8438903 : Blo 1108626 8438903 := bstep (se 1 (by rfl) ⟨6329177, by rfl⟩ : syracuseStep 8438903 = 12658355) B12658355
theorem B35996825 : Blo 1108626 35996825 := bstep (se 2 (by rfl) ⟨13498809, by rfl⟩ : syracuseStep 35996825 = 26997619) B26997619
theorem B2999467 : Blo 1108626 2999467 := bstep (se 1 (by rfl) ⟨2249600, by rfl⟩ : syracuseStep 2999467 = 4499201) B4499201
theorem B4212283 : Blo 1108626 4212283 := bstep (se 1 (by rfl) ⟨3159212, by rfl⟩ : syracuseStep 4212283 = 6318425) B6318425
theorem B41043671 : Blo 1108626 41043671 := bstep (se 1 (by rfl) ⟨30782753, by rfl⟩ : syracuseStep 41043671 = 61565507) B61565507
theorem B1689439 : Blo 1108626 1689439 := bstep (se 1 (by rfl) ⟨1267079, by rfl⟩ : syracuseStep 1689439 = 2534159) B2534159
theorem B4212587 : Blo 1108626 4212587 := bstep (se 1 (by rfl) ⟨3159440, by rfl⟩ : syracuseStep 4212587 = 6318881) B6318881
theorem B14436305 : Blo 1108626 14436305 := bstep (se 2 (by rfl) ⟨5413614, by rfl⟩ : syracuseStep 14436305 = 10827229) B10827229
theorem B4212755 : Blo 1108626 4212755 := bstep (se 1 (by rfl) ⟨3159566, by rfl⟩ : syracuseStep 4212755 = 6319133) B6319133
theorem B3557395 : Blo 1108626 3557395 := bstep (se 1 (by rfl) ⟨2668046, by rfl⟩ : syracuseStep 3557395 = 5336093) B5336093
theorem B3164179 : Blo 1108626 3164179 := bstep (se 1 (by rfl) ⟨2373134, by rfl⟩ : syracuseStep 3164179 = 4746269) B4746269
theorem B9128051 : Blo 1108626 9128051 := bstep (se 1 (by rfl) ⟨6846038, by rfl⟩ : syracuseStep 9128051 = 13692077) B13692077
theorem B8997131 : Blo 1108626 8997131 := bstep (se 1 (by rfl) ⟨6747848, by rfl⟩ : syracuseStep 8997131 = 13495697) B13495697
theorem B3164521 : Blo 1108626 3164521 := bstep (se 2 (by rfl) ⟨1186695, by rfl⟩ : syracuseStep 3164521 = 2373391) B2373391
theorem B8538497 : Blo 1108626 8538497 := bstep (se 2 (by rfl) ⟨3201936, by rfl⟩ : syracuseStep 8538497 = 6403873) B6403873
theorem B1690121 : Blo 1108626 1690121 := bstep (se 2 (by rfl) ⟨633795, by rfl⟩ : syracuseStep 1690121 = 1267591) B1267591
theorem B3164795 : Blo 1108626 3164795 := bstep (se 1 (by rfl) ⟨2373596, by rfl⟩ : syracuseStep 3164795 = 4747193) B4747193
theorem B3754619 : Blo 1108626 3754619 := bstep (se 1 (by rfl) ⟨2815964, by rfl⟩ : syracuseStep 3754619 = 5631929) B5631929
theorem B3754781 : Blo 1108626 3754781 := bstep (se 3 (by rfl) ⟨704021, by rfl⟩ : syracuseStep 3754781 = 1408043) B1408043
theorem B12635027 : Blo 1108626 12635027 := bstep (se 1 (by rfl) ⟨9476270, by rfl⟩ : syracuseStep 12635027 = 18952541) B18952541
theorem B308202565 : Blo 1108626 308202565 := bstep (se 4 (by rfl) ⟨28893990, by rfl⟩ : syracuseStep 308202565 = 57787981) B57787981
theorem B3165911 : Blo 1108626 3165911 := bstep (se 1 (by rfl) ⟨2374433, by rfl⟩ : syracuseStep 3165911 = 4748867) B4748867
theorem B10669805 : Blo 1108626 10669805 := bstep (se 3 (by rfl) ⟨2000588, by rfl⟩ : syracuseStep 10669805 = 4001177) B4001177
theorem B3559241 : Blo 1108626 3559241 := bstep (se 2 (by rfl) ⟨1334715, by rfl⟩ : syracuseStep 3559241 = 2669431) B2669431
theorem B2806235 : Blo 1108626 2806235 := bstep (se 1 (by rfl) ⟨2104676, by rfl⟩ : syracuseStep 2806235 = 4209353) B4209353
theorem B10670615 : Blo 1108626 10670615 := bstep (se 1 (by rfl) ⟨8002961, by rfl⟩ : syracuseStep 10670615 = 16005923) B16005923
theorem B6410963 : Blo 1108626 6410963 := bstep (se 1 (by rfl) ⟨4808222, by rfl⟩ : syracuseStep 6410963 = 9616445) B9616445
theorem B4215671 : Blo 1108626 4215671 := bstep (se 1 (by rfl) ⟨3161753, by rfl⟩ : syracuseStep 4215671 = 6323507) B6323507
theorem B23123009 : Blo 1108626 23123009 := bstep (se 2 (by rfl) ⟨8671128, by rfl⟩ : syracuseStep 23123009 = 17342257) B17342257
theorem B12670019 : Blo 1108626 12670019 := bstep (se 1 (by rfl) ⟨9502514, by rfl⟩ : syracuseStep 12670019 = 19005029) B19005029
theorem B2250127 : Blo 1108626 2250127 := bstep (se 1 (by rfl) ⟨1687595, by rfl⟩ : syracuseStep 2250127 = 3375191) B3375191
theorem B17126801 : Blo 1108626 17126801 := bstep (se 2 (by rfl) ⟨6422550, by rfl⟩ : syracuseStep 17126801 = 12845101) B12845101
theorem B1922617 : Blo 1108626 1922617 := bstep (se 2 (by rfl) ⟨720981, by rfl⟩ : syracuseStep 1922617 = 1441963) B1441963
theorem B2807419 : Blo 1108626 2807419 := bstep (se 1 (by rfl) ⟨2105564, by rfl⟩ : syracuseStep 2807419 = 4211129) B4211129
theorem B5691019 : Blo 1108626 5691019 := bstep (se 1 (by rfl) ⟨4268264, by rfl⟩ : syracuseStep 5691019 = 8536529) B8536529
theorem B4216643 : Blo 1108626 4216643 := bstep (se 1 (by rfl) ⟨3162482, by rfl⟩ : syracuseStep 4216643 = 6324965) B6324965
theorem B4217629 : Blo 1108626 4217629 := bstep (se 3 (by rfl) ⟨790805, by rfl⟩ : syracuseStep 4217629 = 1581611) B1581611
theorem B8445221 : Blo 1108626 8445221 := bstep (se 4 (by rfl) ⟨791739, by rfl⟩ : syracuseStep 8445221 = 1583479) B1583479
theorem B48717233 : Blo 1108626 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B3563033 : Blo 1108626 3563033 := bstep (se 2 (by rfl) ⟨1336137, by rfl⟩ : syracuseStep 3563033 = 2672275) B2672275
theorem B18013985 : Blo 1108626 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B1335215 : Blo 1108626 1335215 := bstep (se 1 (by rfl) ⟨1001411, by rfl⟩ : syracuseStep 1335215 = 2002823) B2002823
theorem B1663055 : Blo 1108626 1663055 := bstep (se 1 (by rfl) ⟨1247291, by rfl⟩ : syracuseStep 1663055 = 2494583) B2494583
theorem B1663175 : Blo 1108626 1663175 := bstep (se 1 (by rfl) ⟨1247381, by rfl⟩ : syracuseStep 1663175 = 2494763) B2494763
theorem B5333309 : Blo 1108626 5333309 := bstep (se 3 (by rfl) ⟨999995, by rfl⟩ : syracuseStep 5333309 = 1999991) B1999991
theorem B1663337 : Blo 1108626 1663337 := bstep (se 2 (by rfl) ⟨623751, by rfl⟩ : syracuseStep 1663337 = 1247503) B1247503
theorem B1663415 : Blo 1108626 1663415 := bstep (se 1 (by rfl) ⟨1247561, by rfl⟩ : syracuseStep 1663415 = 2495123) B2495123
theorem B1663451 : Blo 1108626 1663451 := bstep (se 1 (by rfl) ⟨1247588, by rfl⟩ : syracuseStep 1663451 = 2495177) B2495177
theorem B1827407 : Blo 1108626 1827407 := bstep (se 1 (by rfl) ⟨1370555, by rfl⟩ : syracuseStep 1827407 = 2741111) B2741111
theorem B35971913 : Blo 1108626 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B1663919 : Blo 1108626 1663919 := bstep (se 1 (by rfl) ⟨1247939, by rfl⟩ : syracuseStep 1663919 = 2495879) B2495879
theorem B1664009 : Blo 1108626 1664009 := bstep (se 2 (by rfl) ⟨624003, by rfl⟩ : syracuseStep 1664009 = 1248007) B1248007
theorem B1664039 : Blo 1108626 1664039 := bstep (se 1 (by rfl) ⟨1248029, by rfl⟩ : syracuseStep 1664039 = 2496059) B2496059
theorem B30368819 : Blo 1108626 30368819 := bstep (se 1 (by rfl) ⟨22776614, by rfl⟩ : syracuseStep 30368819 = 45553229) B45553229
theorem B4744271 : Blo 1108626 4744271 := bstep (se 1 (by rfl) ⟨3558203, by rfl⟩ : syracuseStep 4744271 = 7116407) B7116407
theorem B1664123 : Blo 1108626 1664123 := bstep (se 1 (by rfl) ⟨1248092, by rfl⟩ : syracuseStep 1664123 = 2496185) B2496185
theorem B5629175 : Blo 1108626 5629175 := bstep (se 1 (by rfl) ⟨4221881, by rfl⟩ : syracuseStep 5629175 = 8443763) B8443763
theorem B1664249 : Blo 1108626 1664249 := bstep (se 2 (by rfl) ⟨624093, by rfl⟩ : syracuseStep 1664249 = 1248187) B1248187
theorem B1664351 : Blo 1108626 1664351 := bstep (se 1 (by rfl) ⟨1248263, by rfl⟩ : syracuseStep 1664351 = 2496527) B2496527
theorem B1664363 : Blo 1108626 1664363 := bstep (se 1 (by rfl) ⟨1248272, by rfl⟩ : syracuseStep 1664363 = 2496545) B2496545
theorem B17098229 : Blo 1108626 17098229 := bstep (se 5 (by rfl) ⟨801479, by rfl⟩ : syracuseStep 17098229 = 1602959) B1602959
theorem B1664591 : Blo 1108626 1664591 := bstep (se 1 (by rfl) ⟨1248443, by rfl⟩ : syracuseStep 1664591 = 2496887) B2496887
theorem B16017041 : Blo 1108626 16017041 := bstep (se 2 (by rfl) ⟨6006390, by rfl⟩ : syracuseStep 16017041 = 12012781) B12012781
theorem B1664711 : Blo 1108626 1664711 := bstep (se 1 (by rfl) ⟨1248533, by rfl⟩ : syracuseStep 1664711 = 2497067) B2497067
theorem B5629661 : Blo 1108626 5629661 := bstep (se 3 (by rfl) ⟨1055561, by rfl⟩ : syracuseStep 5629661 = 2111123) B2111123
theorem B9135931 : Blo 1108626 9135931 := bstep (se 1 (by rfl) ⟨6851948, by rfl⟩ : syracuseStep 9135931 = 13703897) B13703897
theorem B2811743 : Blo 1108626 2811743 := bstep (se 1 (by rfl) ⟨2108807, by rfl⟩ : syracuseStep 2811743 = 4217615) B4217615
theorem B1664873 : Blo 1108626 1664873 := bstep (se 2 (by rfl) ⟨624327, by rfl⟩ : syracuseStep 1664873 = 1248655) B1248655
theorem B5695393 : Blo 1108626 5695393 := bstep (se 2 (by rfl) ⟨2135772, by rfl⟩ : syracuseStep 5695393 = 4271545) B4271545
theorem B1664951 : Blo 1108626 1664951 := bstep (se 1 (by rfl) ⟨1248713, by rfl⟩ : syracuseStep 1664951 = 2497427) B2497427
theorem B23128001 : Blo 1108626 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B1664987 : Blo 1108626 1664987 := bstep (se 1 (by rfl) ⟨1248740, by rfl⟩ : syracuseStep 1664987 = 2497481) B2497481
theorem B1665455 : Blo 1108626 1665455 := bstep (se 1 (by rfl) ⟨1249091, by rfl⟩ : syracuseStep 1665455 = 2498183) B2498183
theorem B1665545 : Blo 1108626 1665545 := bstep (se 2 (by rfl) ⟨624579, by rfl⟩ : syracuseStep 1665545 = 1249159) B1249159
theorem B4057609 : Blo 1108626 4057609 := bstep (se 2 (by rfl) ⟨1521603, by rfl⟩ : syracuseStep 4057609 = 3043207) B3043207
theorem B2812441 : Blo 1108626 2812441 := bstep (se 2 (by rfl) ⟨1054665, by rfl⟩ : syracuseStep 2812441 = 2109331) B2109331
theorem B1665575 : Blo 1108626 1665575 := bstep (se 1 (by rfl) ⟨1249181, by rfl⟩ : syracuseStep 1665575 = 2498363) B2498363
theorem B1665659 : Blo 1108626 1665659 := bstep (se 1 (by rfl) ⟨1249244, by rfl⟩ : syracuseStep 1665659 = 2498489) B2498489
theorem B1108655 : Blo 1108626 1108655 := bstep (se 1 (by rfl) ⟨831491, by rfl⟩ : syracuseStep 1108655 = 1662983) B1662983
theorem B1108679 : Blo 1108626 1108679 := bstep (se 1 (by rfl) ⟨831509, by rfl⟩ : syracuseStep 1108679 = 1663019) B1663019
theorem B1108699 : Blo 1108626 1108699 := bstep (se 1 (by rfl) ⟨831524, by rfl⟩ : syracuseStep 1108699 = 1663049) B1663049
theorem B1665785 : Blo 1108626 1665785 := bstep (se 2 (by rfl) ⟨624669, by rfl⟩ : syracuseStep 1665785 = 1249339) B1249339
theorem B1108775 : Blo 1108626 1108775 := bstep (se 1 (by rfl) ⟨831581, by rfl⟩ : syracuseStep 1108775 = 1663163) B1663163
theorem B2812745 : Blo 1108626 2812745 := bstep (se 2 (by rfl) ⟨1054779, by rfl⟩ : syracuseStep 2812745 = 2109559) B2109559
theorem B18017099 : Blo 1108626 18017099 := bstep (se 1 (by rfl) ⟨13512824, by rfl⟩ : syracuseStep 18017099 = 27025649) B27025649
theorem B1108815 : Blo 1108626 1108815 := bstep (se 1 (by rfl) ⟨831611, by rfl⟩ : syracuseStep 1108815 = 1663223) B1663223
theorem B1108831 : Blo 1108626 1108831 := bstep (se 1 (by rfl) ⟨831623, by rfl⟩ : syracuseStep 1108831 = 1663247) B1663247
theorem B1665887 : Blo 1108626 1665887 := bstep (se 1 (by rfl) ⟨1249415, by rfl⟩ : syracuseStep 1665887 = 2498831) B2498831
theorem B4221791 : Blo 1108626 4221791 := bstep (se 1 (by rfl) ⟨3166343, by rfl⟩ : syracuseStep 4221791 = 6332687) B6332687
theorem B1665899 : Blo 1108626 1665899 := bstep (se 1 (by rfl) ⟨1249424, by rfl⟩ : syracuseStep 1665899 = 2498849) B2498849
theorem B1108859 : Blo 1108626 1108859 := bstep (se 1 (by rfl) ⟨831644, by rfl⟩ : syracuseStep 1108859 = 1663289) B1663289
theorem B1108911 : Blo 1108626 1108911 := bstep (se 1 (by rfl) ⟨831683, by rfl⟩ : syracuseStep 1108911 = 1663367) B1663367
theorem B1403831 : Blo 1108626 1403831 := bstep (se 1 (by rfl) ⟨1052873, by rfl⟩ : syracuseStep 1403831 = 2105747) B2105747
theorem B1108935 : Blo 1108626 1108935 := bstep (se 1 (by rfl) ⟨831701, by rfl⟩ : syracuseStep 1108935 = 1663403) B1663403
theorem B1108955 : Blo 1108626 1108955 := bstep (se 1 (by rfl) ⟨831716, by rfl⟩ : syracuseStep 1108955 = 1663433) B1663433
theorem B2845703 : Blo 1108626 2845703 := bstep (se 1 (by rfl) ⟨2134277, by rfl⟩ : syracuseStep 2845703 = 4268555) B4268555
theorem B1109031 : Blo 1108626 1109031 := bstep (se 1 (by rfl) ⟨831773, by rfl⟩ : syracuseStep 1109031 = 1663547) B1663547
theorem B1109071 : Blo 1108626 1109071 := bstep (se 1 (by rfl) ⟨831803, by rfl⟩ : syracuseStep 1109071 = 1663607) B1663607
theorem B1403983 : Blo 1108626 1403983 := bstep (se 1 (by rfl) ⟨1052987, by rfl⟩ : syracuseStep 1403983 = 2105975) B2105975
theorem B1666127 : Blo 1108626 1666127 := bstep (se 1 (by rfl) ⟨1249595, by rfl⟩ : syracuseStep 1666127 = 2499191) B2499191
theorem B1109087 : Blo 1108626 1109087 := bstep (se 1 (by rfl) ⟨831815, by rfl⟩ : syracuseStep 1109087 = 1663631) B1663631
theorem B1109115 : Blo 1108626 1109115 := bstep (se 1 (by rfl) ⟨831836, by rfl⟩ : syracuseStep 1109115 = 1663673) B1663673
theorem B1109167 : Blo 1108626 1109167 := bstep (se 1 (by rfl) ⟨831875, by rfl⟩ : syracuseStep 1109167 = 1663751) B1663751
theorem B1109191 : Blo 1108626 1109191 := bstep (se 1 (by rfl) ⟨831893, by rfl⟩ : syracuseStep 1109191 = 1663787) B1663787
theorem B1666247 : Blo 1108626 1666247 := bstep (se 1 (by rfl) ⟨1249685, by rfl⟩ : syracuseStep 1666247 = 2499371) B2499371
theorem B1109211 : Blo 1108626 1109211 := bstep (se 1 (by rfl) ⟨831908, by rfl⟩ : syracuseStep 1109211 = 1663817) B1663817
theorem B1109287 : Blo 1108626 1109287 := bstep (se 1 (by rfl) ⟨831965, by rfl⟩ : syracuseStep 1109287 = 1663931) B1663931
theorem B1109327 : Blo 1108626 1109327 := bstep (se 1 (by rfl) ⟨831995, by rfl⟩ : syracuseStep 1109327 = 1663991) B1663991
theorem B1109343 : Blo 1108626 1109343 := bstep (se 1 (by rfl) ⟨832007, by rfl⟩ : syracuseStep 1109343 = 1664015) B1664015
theorem B1666409 : Blo 1108626 1666409 := bstep (se 2 (by rfl) ⟨624903, by rfl⟩ : syracuseStep 1666409 = 1249807) B1249807
theorem B1109371 : Blo 1108626 1109371 := bstep (se 1 (by rfl) ⟨832028, by rfl⟩ : syracuseStep 1109371 = 1664057) B1664057
theorem B43249031 : Blo 1108626 43249031 := bstep (se 1 (by rfl) ⟨32436773, by rfl⟩ : syracuseStep 43249031 = 64873547) B64873547
theorem B45575567 : Blo 1108626 45575567 := bstep (se 1 (by rfl) ⟨34181675, by rfl⟩ : syracuseStep 45575567 = 68363351) B68363351
theorem B5074319 : Blo 1108626 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B1109423 : Blo 1108626 1109423 := bstep (se 1 (by rfl) ⟨832067, by rfl⟩ : syracuseStep 1109423 = 1664135) B1664135
theorem B1666487 : Blo 1108626 1666487 := bstep (se 1 (by rfl) ⟨1249865, by rfl⟩ : syracuseStep 1666487 = 2499731) B2499731
theorem B1109447 : Blo 1108626 1109447 := bstep (se 1 (by rfl) ⟨832085, by rfl⟩ : syracuseStep 1109447 = 1664171) B1664171
theorem B1109467 : Blo 1108626 1109467 := bstep (se 1 (by rfl) ⟨832100, by rfl⟩ : syracuseStep 1109467 = 1664201) B1664201
theorem B1666523 : Blo 1108626 1666523 := bstep (se 1 (by rfl) ⟨1249892, by rfl⟩ : syracuseStep 1666523 = 2499785) B2499785
theorem B4222489 : Blo 1108626 4222489 := bstep (se 2 (by rfl) ⟨1583433, by rfl⟩ : syracuseStep 4222489 = 3166867) B3166867
theorem B1109543 : Blo 1108626 1109543 := bstep (se 1 (by rfl) ⟨832157, by rfl⟩ : syracuseStep 1109543 = 1664315) B1664315
theorem B1109583 : Blo 1108626 1109583 := bstep (se 1 (by rfl) ⟨832187, by rfl⟩ : syracuseStep 1109583 = 1664375) B1664375
theorem B1109599 : Blo 1108626 1109599 := bstep (se 1 (by rfl) ⟨832199, by rfl⟩ : syracuseStep 1109599 = 1664399) B1664399
theorem B1109627 : Blo 1108626 1109627 := bstep (se 1 (by rfl) ⟨832220, by rfl⟩ : syracuseStep 1109627 = 1664441) B1664441
theorem B1109679 : Blo 1108626 1109679 := bstep (se 1 (by rfl) ⟨832259, by rfl⟩ : syracuseStep 1109679 = 1664519) B1664519
theorem B1109703 : Blo 1108626 1109703 := bstep (se 1 (by rfl) ⟨832277, by rfl⟩ : syracuseStep 1109703 = 1664555) B1664555
theorem B1109723 : Blo 1108626 1109723 := bstep (se 1 (by rfl) ⟨832292, by rfl⟩ : syracuseStep 1109723 = 1664585) B1664585
theorem B8548129 : Blo 1108626 8548129 := bstep (se 2 (by rfl) ⟨3205548, by rfl⟩ : syracuseStep 8548129 = 6411097) B6411097
theorem B1109799 : Blo 1108626 1109799 := bstep (se 1 (by rfl) ⟨832349, by rfl⟩ : syracuseStep 1109799 = 1664699) B1664699
theorem B4222763 : Blo 1108626 4222763 := bstep (se 1 (by rfl) ⟨3167072, by rfl⟩ : syracuseStep 4222763 = 6334145) B6334145
theorem B4222793 : Blo 1108626 4222793 := bstep (se 2 (by rfl) ⟨1583547, by rfl⟩ : syracuseStep 4222793 = 3167095) B3167095
theorem B1109839 : Blo 1108626 1109839 := bstep (se 1 (by rfl) ⟨832379, by rfl⟩ : syracuseStep 1109839 = 1664759) B1664759
theorem B1109855 : Blo 1108626 1109855 := bstep (se 1 (by rfl) ⟨832391, by rfl⟩ : syracuseStep 1109855 = 1664783) B1664783
theorem B1109883 : Blo 1108626 1109883 := bstep (se 1 (by rfl) ⟨832412, by rfl⟩ : syracuseStep 1109883 = 1664825) B1664825
theorem B1109935 : Blo 1108626 1109935 := bstep (se 1 (by rfl) ⟨832451, by rfl⟩ : syracuseStep 1109935 = 1664903) B1664903
theorem B1666991 : Blo 1108626 1666991 := bstep (se 1 (by rfl) ⟨1250243, by rfl⟩ : syracuseStep 1666991 = 2500487) B2500487
theorem B2813879 : Blo 1108626 2813879 := bstep (se 1 (by rfl) ⟨2110409, by rfl⟩ : syracuseStep 2813879 = 4220819) B4220819
theorem B6320065 : Blo 1108626 6320065 := bstep (se 2 (by rfl) ⟨2370024, by rfl⟩ : syracuseStep 6320065 = 4740049) B4740049
theorem B1109959 : Blo 1108626 1109959 := bstep (se 1 (by rfl) ⟨832469, by rfl⟩ : syracuseStep 1109959 = 1664939) B1664939
theorem B1109979 : Blo 1108626 1109979 := bstep (se 1 (by rfl) ⟨832484, by rfl⟩ : syracuseStep 1109979 = 1664969) B1664969
theorem B1667081 : Blo 1108626 1667081 := bstep (se 2 (by rfl) ⟨625155, by rfl⟩ : syracuseStep 1667081 = 1250311) B1250311
theorem B10678301 : Blo 1108626 10678301 := bstep (se 3 (by rfl) ⟨2002181, by rfl⟩ : syracuseStep 10678301 = 4004363) B4004363
theorem B1110055 : Blo 1108626 1110055 := bstep (se 1 (by rfl) ⟨832541, by rfl⟩ : syracuseStep 1110055 = 1665083) B1665083
theorem B1667111 : Blo 1108626 1667111 := bstep (se 1 (by rfl) ⟨1250333, by rfl⟩ : syracuseStep 1667111 = 2500667) B2500667
theorem B1110095 : Blo 1108626 1110095 := bstep (se 1 (by rfl) ⟨832571, by rfl⟩ : syracuseStep 1110095 = 1665143) B1665143
theorem B1110111 : Blo 1108626 1110111 := bstep (se 1 (by rfl) ⟨832583, by rfl⟩ : syracuseStep 1110111 = 1665167) B1665167
theorem B1110139 : Blo 1108626 1110139 := bstep (se 1 (by rfl) ⟨832604, by rfl⟩ : syracuseStep 1110139 = 1665209) B1665209
theorem B1667195 : Blo 1108626 1667195 := bstep (se 1 (by rfl) ⟨1250396, by rfl⟩ : syracuseStep 1667195 = 2500793) B2500793
theorem B7991453 : Blo 1108626 7991453 := bstep (se 3 (by rfl) ⟨1498397, by rfl⟩ : syracuseStep 7991453 = 2996795) B2996795
theorem B1110191 : Blo 1108626 1110191 := bstep (se 1 (by rfl) ⟨832643, by rfl⟩ : syracuseStep 1110191 = 1665287) B1665287
theorem B1110215 : Blo 1108626 1110215 := bstep (se 1 (by rfl) ⟨832661, by rfl⟩ : syracuseStep 1110215 = 1665323) B1665323
theorem B1405127 : Blo 1108626 1405127 := bstep (se 1 (by rfl) ⟨1053845, by rfl⟩ : syracuseStep 1405127 = 2107691) B2107691
theorem B1110235 : Blo 1108626 1110235 := bstep (se 1 (by rfl) ⟨832676, by rfl⟩ : syracuseStep 1110235 = 1665353) B1665353
theorem B1667321 : Blo 1108626 1667321 := bstep (se 2 (by rfl) ⟨625245, by rfl⟩ : syracuseStep 1667321 = 1250491) B1250491
theorem B1110311 : Blo 1108626 1110311 := bstep (se 1 (by rfl) ⟨832733, by rfl⟩ : syracuseStep 1110311 = 1665467) B1665467
theorem B1110351 : Blo 1108626 1110351 := bstep (se 1 (by rfl) ⟨832763, by rfl⟩ : syracuseStep 1110351 = 1665527) B1665527
theorem B1405279 : Blo 1108626 1405279 := bstep (se 1 (by rfl) ⟨1053959, by rfl⟩ : syracuseStep 1405279 = 2107919) B2107919
theorem B1110367 : Blo 1108626 1110367 := bstep (se 1 (by rfl) ⟨832775, by rfl⟩ : syracuseStep 1110367 = 1665551) B1665551
theorem B1667423 : Blo 1108626 1667423 := bstep (se 1 (by rfl) ⟨1250567, by rfl⟩ : syracuseStep 1667423 = 2501135) B2501135
theorem B1667435 : Blo 1108626 1667435 := bstep (se 1 (by rfl) ⟨1250576, by rfl⟩ : syracuseStep 1667435 = 2501153) B2501153
theorem B1110395 : Blo 1108626 1110395 := bstep (se 1 (by rfl) ⟨832796, by rfl⟩ : syracuseStep 1110395 = 1665593) B1665593
theorem B1110447 : Blo 1108626 1110447 := bstep (se 1 (by rfl) ⟨832835, by rfl⟩ : syracuseStep 1110447 = 1665671) B1665671
theorem B1110471 : Blo 1108626 1110471 := bstep (se 1 (by rfl) ⟨832853, by rfl⟩ : syracuseStep 1110471 = 1665707) B1665707
theorem B1110491 : Blo 1108626 1110491 := bstep (se 1 (by rfl) ⟨832868, by rfl⟩ : syracuseStep 1110491 = 1665737) B1665737
theorem B1110567 : Blo 1108626 1110567 := bstep (se 1 (by rfl) ⟨832925, by rfl⟩ : syracuseStep 1110567 = 1665851) B1665851
theorem B1110607 : Blo 1108626 1110607 := bstep (se 1 (by rfl) ⟨832955, by rfl⟩ : syracuseStep 1110607 = 1665911) B1665911
theorem B1667663 : Blo 1108626 1667663 := bstep (se 1 (by rfl) ⟨1250747, by rfl⟩ : syracuseStep 1667663 = 2501495) B2501495
theorem B1110623 : Blo 1108626 1110623 := bstep (se 1 (by rfl) ⟨832967, by rfl⟩ : syracuseStep 1110623 = 1665935) B1665935
theorem B1110651 : Blo 1108626 1110651 := bstep (se 1 (by rfl) ⟨832988, by rfl⟩ : syracuseStep 1110651 = 1665977) B1665977
theorem B1110703 : Blo 1108626 1110703 := bstep (se 1 (by rfl) ⟨833027, by rfl⟩ : syracuseStep 1110703 = 1666055) B1666055
theorem B1110727 : Blo 1108626 1110727 := bstep (se 1 (by rfl) ⟨833045, by rfl⟩ : syracuseStep 1110727 = 1666091) B1666091
theorem B1667783 : Blo 1108626 1667783 := bstep (se 1 (by rfl) ⟨1250837, by rfl⟩ : syracuseStep 1667783 = 2501675) B2501675
theorem B1110747 : Blo 1108626 1110747 := bstep (se 1 (by rfl) ⟨833060, by rfl⟩ : syracuseStep 1110747 = 1666121) B1666121
theorem B1110823 : Blo 1108626 1110823 := bstep (se 1 (by rfl) ⟨833117, by rfl⟩ : syracuseStep 1110823 = 1666235) B1666235
theorem B1110863 : Blo 1108626 1110863 := bstep (se 1 (by rfl) ⟨833147, by rfl⟩ : syracuseStep 1110863 = 1666295) B1666295
theorem B1110879 : Blo 1108626 1110879 := bstep (se 1 (by rfl) ⟨833159, by rfl⟩ : syracuseStep 1110879 = 1666319) B1666319
theorem B1667945 : Blo 1108626 1667945 := bstep (se 2 (by rfl) ⟨625479, by rfl⟩ : syracuseStep 1667945 = 1250959) B1250959
theorem B1110907 : Blo 1108626 1110907 := bstep (se 1 (by rfl) ⟨833180, by rfl⟩ : syracuseStep 1110907 = 1666361) B1666361
theorem B1110959 : Blo 1108626 1110959 := bstep (se 1 (by rfl) ⟨833219, by rfl⟩ : syracuseStep 1110959 = 1666439) B1666439
theorem B1668023 : Blo 1108626 1668023 := bstep (se 1 (by rfl) ⟨1251017, by rfl⟩ : syracuseStep 1668023 = 2502035) B2502035
theorem B1110983 : Blo 1108626 1110983 := bstep (se 1 (by rfl) ⟨833237, by rfl⟩ : syracuseStep 1110983 = 1666475) B1666475
theorem B1111003 : Blo 1108626 1111003 := bstep (se 1 (by rfl) ⟨833252, by rfl⟩ : syracuseStep 1111003 = 1666505) B1666505
theorem B1668059 : Blo 1108626 1668059 := bstep (se 1 (by rfl) ⟨1251044, by rfl⟩ : syracuseStep 1668059 = 2502089) B2502089
theorem B2814983 : Blo 1108626 2814983 := bstep (se 1 (by rfl) ⟨2111237, by rfl⟩ : syracuseStep 2814983 = 4222475) B4222475
theorem B1111079 : Blo 1108626 1111079 := bstep (se 1 (by rfl) ⟨833309, by rfl⟩ : syracuseStep 1111079 = 1666619) B1666619
theorem B2815033 : Blo 1108626 2815033 := bstep (se 2 (by rfl) ⟨1055637, by rfl⟩ : syracuseStep 2815033 = 2111275) B2111275
theorem B1111119 : Blo 1108626 1111119 := bstep (se 1 (by rfl) ⟨833339, by rfl⟩ : syracuseStep 1111119 = 1666679) B1666679
theorem B1111135 : Blo 1108626 1111135 := bstep (se 1 (by rfl) ⟨833351, by rfl⟩ : syracuseStep 1111135 = 1666703) B1666703
theorem B1111163 : Blo 1108626 1111163 := bstep (se 1 (by rfl) ⟨833372, by rfl⟩ : syracuseStep 1111163 = 1666745) B1666745
theorem B1111215 : Blo 1108626 1111215 := bstep (se 1 (by rfl) ⟨833411, by rfl⟩ : syracuseStep 1111215 = 1666823) B1666823
theorem B1111239 : Blo 1108626 1111239 := bstep (se 1 (by rfl) ⟨833429, by rfl⟩ : syracuseStep 1111239 = 1666859) B1666859
theorem B1111259 : Blo 1108626 1111259 := bstep (se 1 (by rfl) ⟨833444, by rfl⟩ : syracuseStep 1111259 = 1666889) B1666889
theorem B1111335 : Blo 1108626 1111335 := bstep (se 1 (by rfl) ⟨833501, by rfl⟩ : syracuseStep 1111335 = 1667003) B1667003
theorem B1111375 : Blo 1108626 1111375 := bstep (se 1 (by rfl) ⟨833531, by rfl⟩ : syracuseStep 1111375 = 1667063) B1667063
theorem B7992665 : Blo 1108626 7992665 := bstep (se 2 (by rfl) ⟨2997249, by rfl⟩ : syracuseStep 7992665 = 5994499) B5994499
theorem B1111391 : Blo 1108626 1111391 := bstep (se 1 (by rfl) ⟨833543, by rfl⟩ : syracuseStep 1111391 = 1667087) B1667087
theorem B2815337 : Blo 1108626 2815337 := bstep (se 2 (by rfl) ⟨1055751, by rfl⟩ : syracuseStep 2815337 = 2111503) B2111503
theorem B1111419 : Blo 1108626 1111419 := bstep (se 1 (by rfl) ⟨833564, by rfl⟩ : syracuseStep 1111419 = 1667129) B1667129
theorem B1111471 : Blo 1108626 1111471 := bstep (se 1 (by rfl) ⟨833603, by rfl⟩ : syracuseStep 1111471 = 1667207) B1667207
theorem B1668527 : Blo 1108626 1668527 := bstep (se 1 (by rfl) ⟨1251395, by rfl⟩ : syracuseStep 1668527 = 2502791) B2502791
theorem B1111495 : Blo 1108626 1111495 := bstep (se 1 (by rfl) ⟨833621, by rfl⟩ : syracuseStep 1111495 = 1667243) B1667243
theorem B1111515 : Blo 1108626 1111515 := bstep (se 1 (by rfl) ⟨833636, by rfl⟩ : syracuseStep 1111515 = 1667273) B1667273
theorem B1668617 : Blo 1108626 1668617 := bstep (se 2 (by rfl) ⟨625731, by rfl⟩ : syracuseStep 1668617 = 1251463) B1251463
theorem B1111591 : Blo 1108626 1111591 := bstep (se 1 (by rfl) ⟨833693, by rfl⟩ : syracuseStep 1111591 = 1667387) B1667387
theorem B1668647 : Blo 1108626 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B1111631 : Blo 1108626 1111631 := bstep (se 1 (by rfl) ⟨833723, by rfl⟩ : syracuseStep 1111631 = 1667447) B1667447
theorem B1111647 : Blo 1108626 1111647 := bstep (se 1 (by rfl) ⟨833735, by rfl⟩ : syracuseStep 1111647 = 1667471) B1667471
theorem B1111675 : Blo 1108626 1111675 := bstep (se 1 (by rfl) ⟨833756, by rfl⟩ : syracuseStep 1111675 = 1667513) B1667513
theorem B1668731 : Blo 1108626 1668731 := bstep (se 1 (by rfl) ⟨1251548, by rfl⟩ : syracuseStep 1668731 = 2503097) B2503097
theorem B1111727 : Blo 1108626 1111727 := bstep (se 1 (by rfl) ⟨833795, by rfl⟩ : syracuseStep 1111727 = 1667591) B1667591
theorem B1111751 : Blo 1108626 1111751 := bstep (se 1 (by rfl) ⟨833813, by rfl⟩ : syracuseStep 1111751 = 1667627) B1667627
theorem B1111771 : Blo 1108626 1111771 := bstep (se 1 (by rfl) ⟨833828, by rfl⟩ : syracuseStep 1111771 = 1667657) B1667657
theorem B1668857 : Blo 1108626 1668857 := bstep (se 2 (by rfl) ⟨625821, by rfl⟩ : syracuseStep 1668857 = 1251643) B1251643
theorem B1111847 : Blo 1108626 1111847 := bstep (se 1 (by rfl) ⟨833885, by rfl⟩ : syracuseStep 1111847 = 1667771) B1667771
theorem B5994283 : Blo 1108626 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B1111887 : Blo 1108626 1111887 := bstep (se 1 (by rfl) ⟨833915, by rfl⟩ : syracuseStep 1111887 = 1667831) B1667831
theorem B1111903 : Blo 1108626 1111903 := bstep (se 1 (by rfl) ⟨833927, by rfl⟩ : syracuseStep 1111903 = 1667855) B1667855
theorem B1111931 : Blo 1108626 1111931 := bstep (se 1 (by rfl) ⟨833948, by rfl⟩ : syracuseStep 1111931 = 1667897) B1667897
theorem B1111983 : Blo 1108626 1111983 := bstep (se 1 (by rfl) ⟨833987, by rfl⟩ : syracuseStep 1111983 = 1667975) B1667975
theorem B1112007 : Blo 1108626 1112007 := bstep (se 1 (by rfl) ⟨834005, by rfl⟩ : syracuseStep 1112007 = 1668011) B1668011
theorem B1112027 : Blo 1108626 1112027 := bstep (se 1 (by rfl) ⟨834020, by rfl⟩ : syracuseStep 1112027 = 1668041) B1668041
theorem B1112103 : Blo 1108626 1112103 := bstep (se 1 (by rfl) ⟨834077, by rfl⟩ : syracuseStep 1112103 = 1668155) B1668155
theorem B1112143 : Blo 1108626 1112143 := bstep (se 1 (by rfl) ⟨834107, by rfl⟩ : syracuseStep 1112143 = 1668215) B1668215
theorem B1112159 : Blo 1108626 1112159 := bstep (se 1 (by rfl) ⟨834119, by rfl⟩ : syracuseStep 1112159 = 1668239) B1668239
theorem B1112187 : Blo 1108626 1112187 := bstep (se 1 (by rfl) ⟨834140, by rfl⟩ : syracuseStep 1112187 = 1668281) B1668281
theorem B1112239 : Blo 1108626 1112239 := bstep (se 1 (by rfl) ⟨834179, by rfl⟩ : syracuseStep 1112239 = 1668359) B1668359
theorem B1112263 : Blo 1108626 1112263 := bstep (se 1 (by rfl) ⟨834197, by rfl⟩ : syracuseStep 1112263 = 1668395) B1668395
theorem B1112283 : Blo 1108626 1112283 := bstep (se 1 (by rfl) ⟨834212, by rfl⟩ : syracuseStep 1112283 = 1668425) B1668425
theorem B1112359 : Blo 1108626 1112359 := bstep (se 1 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 1112359 = 1668539) B1668539
theorem B1112399 : Blo 1108626 1112399 := bstep (se 1 (by rfl) ⟨834299, by rfl⟩ : syracuseStep 1112399 = 1668599) B1668599
theorem B1112415 : Blo 1108626 1112415 := bstep (se 1 (by rfl) ⟨834311, by rfl⟩ : syracuseStep 1112415 = 1668623) B1668623
theorem B1112443 : Blo 1108626 1112443 := bstep (se 1 (by rfl) ⟨834332, by rfl⟩ : syracuseStep 1112443 = 1668665) B1668665
theorem B1112495 : Blo 1108626 1112495 := bstep (se 1 (by rfl) ⟨834371, by rfl⟩ : syracuseStep 1112495 = 1668743) B1668743
theorem B1112519 : Blo 1108626 1112519 := bstep (se 1 (by rfl) ⟨834389, by rfl⟩ : syracuseStep 1112519 = 1668779) B1668779
theorem B1407451 : Blo 1108626 1407451 := bstep (se 1 (by rfl) ⟨1055588, by rfl⟩ : syracuseStep 1407451 = 2111177) B2111177
theorem B1112539 : Blo 1108626 1112539 := bstep (se 1 (by rfl) ⟨834404, by rfl⟩ : syracuseStep 1112539 = 1668809) B1668809
theorem B5339629 : Blo 1108626 5339629 := bstep (se 3 (by rfl) ⟨1001180, by rfl⟩ : syracuseStep 5339629 = 2002361) B2002361
theorem B7109153 : Blo 1108626 7109153 := bstep (se 2 (by rfl) ⟨2665932, by rfl⟩ : syracuseStep 7109153 = 5331865) B5331865
theorem B1112615 : Blo 1108626 1112615 := bstep (se 1 (by rfl) ⟨834461, by rfl⟩ : syracuseStep 1112615 = 1668923) B1668923
theorem B7993991 : Blo 1108626 7993991 := bstep (se 1 (by rfl) ⟨5995493, by rfl⟩ : syracuseStep 7993991 = 11990987) B11990987
theorem B5339783 : Blo 1108626 5339783 := bstep (se 1 (by rfl) ⟨4004837, by rfl⟩ : syracuseStep 5339783 = 8009675) B8009675
theorem B1899995 : Blo 1108626 1899995 := bstep (se 1 (by rfl) ⟨1424996, by rfl⟩ : syracuseStep 1899995 = 2849993) B2849993
theorem B5996231 : Blo 1108626 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B21364667 : Blo 1108626 21364667 := bstep (se 1 (by rfl) ⟨16023500, by rfl⟩ : syracuseStep 21364667 = 32047001) B32047001
theorem B62357521 : Blo 1108626 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B14221331 : Blo 1108626 14221331 := bstep (se 1 (by rfl) ⟨10665998, by rfl⟩ : syracuseStep 14221331 = 21331997) B21331997
theorem B9502757 : Blo 1108626 9502757 := bstep (se 4 (by rfl) ⟨890883, by rfl⟩ : syracuseStep 9502757 = 1781767) B1781767
theorem B4751531 : Blo 1108626 4751531 := bstep (se 1 (by rfl) ⟨3563648, by rfl⟩ : syracuseStep 4751531 = 7127297) B7127297
theorem B9011411 : Blo 1108626 9011411 := bstep (se 1 (by rfl) ⟨6758558, by rfl⟩ : syracuseStep 9011411 = 13517117) B13517117
theorem B20283833 : Blo 1108626 20283833 := bstep (se 2 (by rfl) ⟨7606437, by rfl⟩ : syracuseStep 20283833 = 15212875) B15212875
theorem B36504265 : Blo 1108626 36504265 := bstep (se 2 (by rfl) ⟨13689099, by rfl⟩ : syracuseStep 36504265 = 27378199) B27378199
theorem B11994101 : Blo 1108626 11994101 := bstep (se 5 (by rfl) ⟨562223, by rfl⟩ : syracuseStep 11994101 = 1124447) B1124447
theorem B27362447 : Blo 1108626 27362447 := bstep (se 1 (by rfl) ⟨20521835, by rfl⟩ : syracuseStep 27362447 = 41043671) B41043671
theorem B5998087 : Blo 1108626 5998087 := bstep (se 1 (by rfl) ⟨4498565, by rfl⟩ : syracuseStep 5998087 = 8997131) B8997131
theorem B3999289 : Blo 1108626 3999289 := bstep (se 2 (by rfl) ⟨1499733, by rfl⟩ : syracuseStep 3999289 = 2999467) B2999467
theorem B15992711 : Blo 1108626 15992711 := bstep (se 1 (by rfl) ⟨11994533, by rfl⟩ : syracuseStep 15992711 = 23989067) B23989067
theorem B105514913 : Blo 1108626 105514913 := bstep (se 2 (by rfl) ⟨39568092, by rfl⟩ : syracuseStep 105514913 = 79136185) B79136185
theorem B8423351 : Blo 1108626 8423351 := bstep (se 1 (by rfl) ⟨6317513, by rfl⟩ : syracuseStep 8423351 = 12635027) B12635027
theorem B28837903 : Blo 1108626 28837903 := bstep (se 1 (by rfl) ⟨21628427, by rfl⟩ : syracuseStep 28837903 = 43256855) B43256855
theorem B1247611 : Blo 1108626 1247611 := bstep (se 1 (by rfl) ⟨935708, by rfl⟩ : syracuseStep 1247611 = 1871417) B1871417
theorem B7113203 : Blo 1108626 7113203 := bstep (se 1 (by rfl) ⟨5334902, by rfl⟩ : syracuseStep 7113203 = 10669805) B10669805
theorem B8129011 : Blo 1108626 8129011 := bstep (se 1 (by rfl) ⟨6096758, by rfl⟩ : syracuseStep 8129011 = 12193517) B12193517
theorem B1248079 : Blo 1108626 1248079 := bstep (se 1 (by rfl) ⟨936059, by rfl⟩ : syracuseStep 1248079 = 1872119) B1872119
theorem B1870823 : Blo 1108626 1870823 := bstep (se 1 (by rfl) ⟨1403117, by rfl⟩ : syracuseStep 1870823 = 2806235) B2806235
theorem B7113743 : Blo 1108626 7113743 := bstep (se 1 (by rfl) ⟨5335307, by rfl⟩ : syracuseStep 7113743 = 10670615) B10670615
theorem B1248475 : Blo 1108626 1248475 := bstep (se 1 (by rfl) ⟨936356, by rfl⟩ : syracuseStep 1248475 = 1872713) B1872713
theorem B5410145 : Blo 1108626 5410145 := bstep (se 2 (by rfl) ⟨2028804, by rfl⟩ : syracuseStep 5410145 = 4057609) B4057609
theorem B1248763 : Blo 1108626 1248763 := bstep (se 1 (by rfl) ⟨936572, by rfl⟩ : syracuseStep 1248763 = 1873145) B1873145
theorem B1248943 : Blo 1108626 1248943 := bstep (se 1 (by rfl) ⟨936707, by rfl⟩ : syracuseStep 1248943 = 1873415) B1873415
theorem B1249231 : Blo 1108626 1249231 := bstep (se 1 (by rfl) ⟨936923, by rfl⟩ : syracuseStep 1249231 = 1873847) B1873847
theorem B3805193 : Blo 1108626 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B1871977 : Blo 1108626 1871977 := bstep (se 2 (by rfl) ⟨701991, by rfl⟩ : syracuseStep 1871977 = 1403983) B1403983
theorem B3805289 : Blo 1108626 3805289 := bstep (se 2 (by rfl) ⟨1426983, by rfl⟩ : syracuseStep 3805289 = 2853967) B2853967
theorem B1249627 : Blo 1108626 1249627 := bstep (se 1 (by rfl) ⟨937220, by rfl⟩ : syracuseStep 1249627 = 1874441) B1874441
theorem B3805547 : Blo 1108626 3805547 := bstep (se 1 (by rfl) ⟨2854160, by rfl⟩ : syracuseStep 3805547 = 5708321) B5708321
theorem B1184167 : Blo 1108626 1184167 := bstep (se 1 (by rfl) ⟨888125, by rfl⟩ : syracuseStep 1184167 = 1776251) B1776251
theorem B1249735 : Blo 1108626 1249735 := bstep (se 1 (by rfl) ⟨937301, by rfl⟩ : syracuseStep 1249735 = 1874603) B1874603
theorem B1446395 : Blo 1108626 1446395 := bstep (se 1 (by rfl) ⟨1084796, by rfl⟩ : syracuseStep 1446395 = 2169593) B2169593
theorem B6001249 : Blo 1108626 6001249 := bstep (se 2 (by rfl) ⟨2250468, by rfl⟩ : syracuseStep 6001249 = 4500937) B4500937
theorem B2495159 : Blo 1108626 2495159 := bstep (se 1 (by rfl) ⟨1871369, by rfl⟩ : syracuseStep 2495159 = 3742739) B3742739
theorem B1250095 : Blo 1108626 1250095 := bstep (se 1 (by rfl) ⟨937571, by rfl⟩ : syracuseStep 1250095 = 1875143) B1875143
theorem B2495375 : Blo 1108626 2495375 := bstep (se 1 (by rfl) ⟨1871531, by rfl⟩ : syracuseStep 2495375 = 3743063) B3743063
theorem B1250203 : Blo 1108626 1250203 := bstep (se 1 (by rfl) ⟨937652, by rfl⟩ : syracuseStep 1250203 = 1875305) B1875305
theorem B32478155 : Blo 1108626 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B6165719 : Blo 1108626 6165719 := bstep (se 1 (by rfl) ⟨4624289, by rfl⟩ : syracuseStep 6165719 = 9248579) B9248579
theorem B1184987 : Blo 1108626 1184987 := bstep (se 1 (by rfl) ⟨888740, by rfl⟩ : syracuseStep 1184987 = 1777481) B1777481
theorem B8426753 : Blo 1108626 8426753 := bstep (se 2 (by rfl) ⟨3160032, by rfl⟩ : syracuseStep 8426753 = 6320065) B6320065
theorem B1250599 : Blo 1108626 1250599 := bstep (se 1 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 1250599 = 1875899) B1875899
theorem B1185115 : Blo 1108626 1185115 := bstep (se 1 (by rfl) ⟨888836, by rfl⟩ : syracuseStep 1185115 = 1777673) B1777673
theorem B1250671 : Blo 1108626 1250671 := bstep (se 1 (by rfl) ⟨938003, by rfl⟩ : syracuseStep 1250671 = 1876007) B1876007
theorem B1709561 : Blo 1108626 1709561 := bstep (se 2 (by rfl) ⟨641085, by rfl⟩ : syracuseStep 1709561 = 1282171) B1282171
theorem B1250887 : Blo 1108626 1250887 := bstep (se 1 (by rfl) ⟨938165, by rfl⟩ : syracuseStep 1250887 = 1876331) B1876331
theorem B2496095 : Blo 1108626 2496095 := bstep (se 1 (by rfl) ⟨1872071, by rfl⟩ : syracuseStep 2496095 = 3744143) B3744143
theorem B1873705 : Blo 1108626 1873705 := bstep (se 2 (by rfl) ⟨702639, by rfl⟩ : syracuseStep 1873705 = 1405279) B1405279
theorem B2496311 : Blo 1108626 2496311 := bstep (se 1 (by rfl) ⟨1872233, by rfl⟩ : syracuseStep 2496311 = 3744467) B3744467
theorem B21370817 : Blo 1108626 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B2496617 : Blo 1108626 2496617 := bstep (se 2 (by rfl) ⟨936231, by rfl⟩ : syracuseStep 2496617 = 1872463) B1872463
theorem B10688759 : Blo 1108626 10688759 := bstep (se 1 (by rfl) ⟨8016569, by rfl⟩ : syracuseStep 10688759 = 16033139) B16033139
theorem B1874495 : Blo 1108626 1874495 := bstep (se 1 (by rfl) ⟨1405871, by rfl⟩ : syracuseStep 1874495 = 2811743) B2811743
theorem B2497103 : Blo 1108626 2497103 := bstep (se 1 (by rfl) ⟨1872827, by rfl⟩ : syracuseStep 2497103 = 3745655) B3745655
theorem B2497247 : Blo 1108626 2497247 := bstep (se 1 (by rfl) ⟨1872935, by rfl⟩ : syracuseStep 2497247 = 3745871) B3745871
theorem B1776539 : Blo 1108626 1776539 := bstep (se 1 (by rfl) ⟨1332404, by rfl⟩ : syracuseStep 1776539 = 2664809) B2664809
theorem B2497499 : Blo 1108626 2497499 := bstep (se 1 (by rfl) ⟨1873124, by rfl⟩ : syracuseStep 2497499 = 3746249) B3746249
theorem B2497679 : Blo 1108626 2497679 := bstep (se 1 (by rfl) ⟨1873259, by rfl⟩ : syracuseStep 2497679 = 3746519) B3746519
theorem B1875163 : Blo 1108626 1875163 := bstep (se 1 (by rfl) ⟨1406372, by rfl⟩ : syracuseStep 1875163 = 2812745) B2812745
theorem B2497769 : Blo 1108626 2497769 := bstep (se 2 (by rfl) ⟨936663, by rfl⟩ : syracuseStep 2497769 = 1873327) B1873327
theorem B2497823 : Blo 1108626 2497823 := bstep (se 1 (by rfl) ⟨1873367, by rfl⟩ : syracuseStep 2497823 = 3746735) B3746735
theorem B2104699 : Blo 1108626 2104699 := bstep (se 1 (by rfl) ⟨1578524, by rfl⟩ : syracuseStep 2104699 = 3157049) B3157049
theorem B2563489 : Blo 1108626 2563489 := bstep (se 2 (by rfl) ⟨961308, by rfl⟩ : syracuseStep 2563489 = 1922617) B1922617
theorem B2104775 : Blo 1108626 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B3743225 : Blo 1108626 3743225 := bstep (se 2 (by rfl) ⟨1403709, by rfl⟩ : syracuseStep 3743225 = 2807419) B2807419
theorem B30383711 : Blo 1108626 30383711 := bstep (se 1 (by rfl) ⟨22787783, by rfl⟩ : syracuseStep 30383711 = 45575567) B45575567
theorem B3382879 : Blo 1108626 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B3743495 : Blo 1108626 3743495 := bstep (se 1 (by rfl) ⟨2807621, by rfl⟩ : syracuseStep 3743495 = 5615243) B5615243
theorem B2498345 : Blo 1108626 2498345 := bstep (se 2 (by rfl) ⟨936879, by rfl⟩ : syracuseStep 2498345 = 1873759) B1873759
theorem B3743549 : Blo 1108626 3743549 := bstep (se 3 (by rfl) ⟨701915, by rfl⟩ : syracuseStep 3743549 = 1403831) B1403831
theorem B1875919 : Blo 1108626 1875919 := bstep (se 1 (by rfl) ⟨1406939, by rfl⟩ : syracuseStep 1875919 = 2813879) B2813879
theorem B7118867 : Blo 1108626 7118867 := bstep (se 1 (by rfl) ⟨5339150, by rfl⟩ : syracuseStep 7118867 = 10678301) B10678301
theorem B30810593 : Blo 1108626 30810593 := bstep (se 2 (by rfl) ⟨11553972, by rfl⟩ : syracuseStep 30810593 = 23107945) B23107945
theorem B2105929 : Blo 1108626 2105929 := bstep (se 2 (by rfl) ⟨789723, by rfl⟩ : syracuseStep 2105929 = 1579447) B1579447
theorem B1876601 : Blo 1108626 1876601 := bstep (se 2 (by rfl) ⟨703725, by rfl⟩ : syracuseStep 1876601 = 1407451) B1407451
theorem B7119505 : Blo 1108626 7119505 := bstep (se 2 (by rfl) ⟨2669814, by rfl⟩ : syracuseStep 7119505 = 5339629) B5339629
theorem B1876655 : Blo 1108626 1876655 := bstep (se 1 (by rfl) ⟨1407491, by rfl⟩ : syracuseStep 1876655 = 2814983) B2814983
theorem B2499407 : Blo 1108626 2499407 := bstep (se 1 (by rfl) ⟨1874555, by rfl⟩ : syracuseStep 2499407 = 3749111) B3749111
theorem B1876891 : Blo 1108626 1876891 := bstep (se 1 (by rfl) ⟨1407668, by rfl⟩ : syracuseStep 1876891 = 2815337) B2815337
theorem B10953667 : Blo 1108626 10953667 := bstep (se 1 (by rfl) ⟨8215250, by rfl⟩ : syracuseStep 10953667 = 16430501) B16430501
theorem B5612489 : Blo 1108626 5612489 := bstep (se 2 (by rfl) ⟨2104683, by rfl⟩ : syracuseStep 5612489 = 4209367) B4209367
theorem B2368487 : Blo 1108626 2368487 := bstep (se 1 (by rfl) ⟨1776365, by rfl⟩ : syracuseStep 2368487 = 3552731) B3552731
theorem B2499623 : Blo 1108626 2499623 := bstep (se 1 (by rfl) ⟨1874717, by rfl⟩ : syracuseStep 2499623 = 3749435) B3749435
theorem B2499803 : Blo 1108626 2499803 := bstep (se 1 (by rfl) ⟨1874852, by rfl⟩ : syracuseStep 2499803 = 3749705) B3749705
theorem B2500001 : Blo 1108626 2500001 := bstep (se 2 (by rfl) ⟨937500, by rfl⟩ : syracuseStep 2500001 = 1875001) B1875001
theorem B2369017 : Blo 1108626 2369017 := bstep (se 2 (by rfl) ⟨888381, by rfl⟩ : syracuseStep 2369017 = 1776763) B1776763
theorem B10692485 : Blo 1108626 10692485 := bstep (se 4 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 10692485 = 2004841) B2004841
theorem B2500559 : Blo 1108626 2500559 := bstep (se 1 (by rfl) ⟨1875419, by rfl⟩ : syracuseStep 2500559 = 3750839) B3750839
theorem B9480509 : Blo 1108626 9480509 := bstep (se 3 (by rfl) ⟨1777595, by rfl⟩ : syracuseStep 9480509 = 3555191) B3555191
theorem B2500937 : Blo 1108626 2500937 := bstep (se 2 (by rfl) ⟨937851, by rfl⟩ : syracuseStep 2500937 = 1875703) B1875703
theorem B2500955 : Blo 1108626 2500955 := bstep (se 1 (by rfl) ⟨1875716, by rfl⟩ : syracuseStep 2500955 = 3751433) B3751433
theorem B2107873 : Blo 1108626 2107873 := bstep (se 2 (by rfl) ⟨790452, by rfl⟩ : syracuseStep 2107873 = 1580905) B1580905
theorem B3746411 : Blo 1108626 3746411 := bstep (se 1 (by rfl) ⟨2809808, by rfl⟩ : syracuseStep 3746411 = 5619617) B5619617
theorem B6761083 : Blo 1108626 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B2501531 : Blo 1108626 2501531 := bstep (se 1 (by rfl) ⟨1876148, by rfl⟩ : syracuseStep 2501531 = 3752297) B3752297
theorem B2501729 : Blo 1108626 2501729 := bstep (se 2 (by rfl) ⟨938148, by rfl⟩ : syracuseStep 2501729 = 1876297) B1876297
theorem B6335603 : Blo 1108626 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B3747005 : Blo 1108626 3747005 := bstep (se 3 (by rfl) ⟨702563, by rfl⟩ : syracuseStep 3747005 = 1405127) B1405127
theorem B2501927 : Blo 1108626 2501927 := bstep (se 1 (by rfl) ⟨1876445, by rfl⟩ : syracuseStep 2501927 = 3752891) B3752891
theorem B23997883 : Blo 1108626 23997883 := bstep (se 1 (by rfl) ⟨17998412, by rfl⟩ : syracuseStep 23997883 = 35996825) B35996825
theorem B4566689 : Blo 1108626 4566689 := bstep (se 2 (by rfl) ⟨1712508, by rfl⟩ : syracuseStep 4566689 = 3425017) B3425017
theorem B2502305 : Blo 1108626 2502305 := bstep (se 2 (by rfl) ⟨938364, by rfl⟩ : syracuseStep 2502305 = 1876729) B1876729
theorem B2502665 : Blo 1108626 2502665 := bstep (se 2 (by rfl) ⟨938499, by rfl⟩ : syracuseStep 2502665 = 1876999) B1876999
theorem B11383055 : Blo 1108626 11383055 := bstep (se 1 (by rfl) ⟨8537291, by rfl⟩ : syracuseStep 11383055 = 17074583) B17074583
theorem B1126747 : Blo 1108626 1126747 := bstep (se 1 (by rfl) ⟨845060, by rfl⟩ : syracuseStep 1126747 = 1690121) B1690121
theorem B2109863 : Blo 1108626 2109863 := bstep (se 1 (by rfl) ⟨1582397, by rfl⟩ : syracuseStep 2109863 = 3164795) B3164795
theorem B2503079 : Blo 1108626 2503079 := bstep (se 1 (by rfl) ⟨1877309, by rfl⟩ : syracuseStep 2503079 = 3754619) B3754619
theorem B2503187 : Blo 1108626 2503187 := bstep (se 1 (by rfl) ⟨1877390, by rfl⟩ : syracuseStep 2503187 = 3754781) B3754781
theorem B2503241 : Blo 1108626 2503241 := bstep (se 2 (by rfl) ⟨938715, by rfl⟩ : syracuseStep 2503241 = 1877431) B1877431
theorem B2667115 : Blo 1108626 2667115 := bstep (se 1 (by rfl) ⟨2000336, by rfl⟩ : syracuseStep 2667115 = 4000673) B4000673
theorem B5616377 : Blo 1108626 5616377 := bstep (se 2 (by rfl) ⟨2106141, by rfl⟩ : syracuseStep 5616377 = 4212283) B4212283
theorem B5485391 : Blo 1108626 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B2110607 : Blo 1108626 2110607 := bstep (se 1 (by rfl) ⟨1582955, by rfl⟩ : syracuseStep 2110607 = 3165911) B3165911
theorem B2372827 : Blo 1108626 2372827 := bstep (se 1 (by rfl) ⟨1779620, by rfl⟩ : syracuseStep 2372827 = 3559241) B3559241
theorem B6010199 : Blo 1108626 6010199 := bstep (se 1 (by rfl) ⟨4507649, by rfl⟩ : syracuseStep 6010199 = 9015299) B9015299
theorem B4273975 : Blo 1108626 4273975 := bstep (se 1 (by rfl) ⟨3205481, by rfl⟩ : syracuseStep 4273975 = 6410963) B6410963
theorem B2668393 : Blo 1108626 2668393 := bstep (se 2 (by rfl) ⟨1000647, by rfl⟩ : syracuseStep 2668393 = 2001295) B2001295
theorem B3749921 : Blo 1108626 3749921 := bstep (se 2 (by rfl) ⟨1406220, by rfl⟩ : syracuseStep 3749921 = 2812441) B2812441
theorem B20297789 : Blo 1108626 20297789 := bstep (se 3 (by rfl) ⟨3805835, by rfl⟩ : syracuseStep 20297789 = 7611671) B7611671
theorem B11417867 : Blo 1108626 11417867 := bstep (se 1 (by rfl) ⟨8563400, by rfl⟩ : syracuseStep 11417867 = 17126801) B17126801
theorem B6011455 : Blo 1108626 6011455 := bstep (se 1 (by rfl) ⟨4508591, by rfl⟩ : syracuseStep 6011455 = 9017183) B9017183
theorem B1686427 : Blo 1108626 1686427 := bstep (se 1 (by rfl) ⟨1264820, by rfl⟩ : syracuseStep 1686427 = 2529641) B2529641
theorem B42712109 : Blo 1108626 42712109 := bstep (se 3 (by rfl) ⟨8008520, by rfl⟩ : syracuseStep 42712109 = 16017041) B16017041
theorem B4209853 : Blo 1108626 4209853 := bstep (se 3 (by rfl) ⟨789347, by rfl⟩ : syracuseStep 4209853 = 1578695) B1578695
theorem B5619131 : Blo 1108626 5619131 := bstep (se 1 (by rfl) ⟨4214348, by rfl⟩ : syracuseStep 5619131 = 8428697) B8428697
theorem B12009323 : Blo 1108626 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B3555539 : Blo 1108626 3555539 := bstep (se 1 (by rfl) ⟨2666654, by rfl⟩ : syracuseStep 3555539 = 5333309) B5333309
theorem B8438417 : Blo 1108626 8438417 := bstep (se 2 (by rfl) ⟨3164406, by rfl⟩ : syracuseStep 8438417 = 6328813) B6328813
theorem B5620427 : Blo 1108626 5620427 := bstep (se 1 (by rfl) ⟨4215320, by rfl⟩ : syracuseStep 5620427 = 8430641) B8430641
theorem B3162847 : Blo 1108626 3162847 := bstep (se 1 (by rfl) ⟨2372135, by rfl⟩ : syracuseStep 3162847 = 4744271) B4744271
theorem B3752783 : Blo 1108626 3752783 := bstep (se 1 (by rfl) ⟨2814587, by rfl⟩ : syracuseStep 3752783 = 5629175) B5629175
theorem B5620589 : Blo 1108626 5620589 := bstep (se 3 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 5620589 = 2107721) B2107721
theorem B68273219 : Blo 1108626 68273219 := bstep (se 1 (by rfl) ⟨51204914, by rfl⟩ : syracuseStep 68273219 = 102409829) B102409829
theorem B3753107 : Blo 1108626 3753107 := bstep (se 1 (by rfl) ⟨2814830, by rfl⟩ : syracuseStep 3753107 = 5629661) B5629661
theorem B15418667 : Blo 1108626 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B3753377 : Blo 1108626 3753377 := bstep (se 2 (by rfl) ⟨1407516, by rfl⟩ : syracuseStep 3753377 = 2815033) B2815033
theorem B14239421 : Blo 1108626 14239421 := bstep (se 3 (by rfl) ⟨2669891, by rfl⟩ : syracuseStep 14239421 = 5339783) B5339783
theorem B3000169 : Blo 1108626 3000169 := bstep (se 2 (by rfl) ⟨1125063, by rfl⟩ : syracuseStep 3000169 = 2250127) B2250127
theorem B12011399 : Blo 1108626 12011399 := bstep (se 1 (by rfl) ⟨9008549, by rfl⟩ : syracuseStep 12011399 = 18017099) B18017099
theorem B4212769 : Blo 1108626 4212769 := bstep (se 2 (by rfl) ⟨1579788, by rfl⟩ : syracuseStep 4212769 = 3159577) B3159577
theorem B7588025 : Blo 1108626 7588025 := bstep (se 2 (by rfl) ⟨2845509, by rfl⟩ : syracuseStep 7588025 = 5691019) B5691019
theorem B7588541 : Blo 1108626 7588541 := bstep (se 3 (by rfl) ⟨1422851, by rfl⟩ : syracuseStep 7588541 = 2845703) B2845703
theorem B5327635 : Blo 1108626 5327635 := bstep (se 1 (by rfl) ⟨3995726, by rfl⟩ : syracuseStep 5327635 = 7991453) B7991453
theorem B8440847 : Blo 1108626 8440847 := bstep (se 1 (by rfl) ⟨6330635, by rfl⟩ : syracuseStep 8440847 = 12661271) B12661271
theorem B3001639 : Blo 1108626 3001639 := bstep (se 1 (by rfl) ⟨2251229, by rfl⟩ : syracuseStep 3001639 = 4502459) B4502459
theorem B5328443 : Blo 1108626 5328443 := bstep (se 1 (by rfl) ⟨3996332, by rfl⟩ : syracuseStep 5328443 = 7992665) B7992665
theorem B5623505 : Blo 1108626 5623505 := bstep (se 2 (by rfl) ⟨2108814, by rfl⟩ : syracuseStep 5623505 = 4217629) B4217629
theorem B5066653 : Blo 1108626 5066653 := bstep (se 3 (by rfl) ⟨949997, by rfl⟩ : syracuseStep 5066653 = 1899995) B1899995
theorem B4739435 : Blo 1108626 4739435 := bstep (se 1 (by rfl) ⟨3554576, by rfl⟩ : syracuseStep 4739435 = 7109153) B7109153
theorem B5329327 : Blo 1108626 5329327 := bstep (se 1 (by rfl) ⟨3996995, by rfl⟩ : syracuseStep 5329327 = 7993991) B7993991
theorem B18010613 : Blo 1108626 18010613 := bstep (se 5 (by rfl) ⟨844247, by rfl⟩ : syracuseStep 18010613 = 1688495) B1688495
theorem B2806447 : Blo 1108626 2806447 := bstep (se 1 (by rfl) ⟨2104835, by rfl⟩ : syracuseStep 2806447 = 4209671) B4209671
theorem B2806771 : Blo 1108626 2806771 := bstep (se 1 (by rfl) ⟨2105078, by rfl⟩ : syracuseStep 2806771 = 4210157) B4210157
theorem B4740221 : Blo 1108626 4740221 := bstep (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) B1777583
theorem B3560573 : Blo 1108626 3560573 := bstep (se 3 (by rfl) ⟨667607, by rfl⟩ : syracuseStep 3560573 = 1335215) B1335215
theorem B14243111 : Blo 1108626 14243111 := bstep (se 1 (by rfl) ⟨10682333, by rfl⟩ : syracuseStep 14243111 = 21364667) B21364667
theorem B2807531 : Blo 1108626 2807531 := bstep (se 1 (by rfl) ⟨2105648, by rfl⟩ : syracuseStep 2807531 = 4211297) B4211297
theorem B4216657 : Blo 1108626 4216657 := bstep (se 2 (by rfl) ⟨1581246, by rfl⟩ : syracuseStep 4216657 = 3162493) B3162493
theorem B5625935 : Blo 1108626 5625935 := bstep (se 1 (by rfl) ⟨4219451, by rfl⟩ : syracuseStep 5625935 = 8438903) B8438903
theorem B4216961 : Blo 1108626 4216961 := bstep (se 2 (by rfl) ⟨1581360, by rfl⟩ : syracuseStep 4216961 = 3162721) B3162721
theorem B8444249 : Blo 1108626 8444249 := bstep (se 2 (by rfl) ⟨3166593, by rfl⟩ : syracuseStep 8444249 = 6333187) B6333187
theorem B11393405 : Blo 1108626 11393405 := bstep (se 3 (by rfl) ⟨2136263, by rfl⟩ : syracuseStep 11393405 = 4272527) B4272527
theorem B2808391 : Blo 1108626 2808391 := bstep (se 1 (by rfl) ⟨2106293, by rfl⟩ : syracuseStep 2808391 = 4212587) B4212587
theorem B1333831 : Blo 1108626 1333831 := bstep (se 1 (by rfl) ⟨1000373, by rfl⟩ : syracuseStep 1333831 = 2000747) B2000747
theorem B4217417 : Blo 1108626 4217417 := bstep (se 2 (by rfl) ⟨1581531, by rfl⟩ : syracuseStep 4217417 = 3163063) B3163063
theorem B9624203 : Blo 1108626 9624203 := bstep (se 1 (by rfl) ⟨7218152, by rfl⟩ : syracuseStep 9624203 = 14436305) B14436305
theorem B2808503 : Blo 1108626 2808503 := bstep (se 1 (by rfl) ⟨2106377, by rfl⟩ : syracuseStep 2808503 = 4212755) B4212755
theorem B6085367 : Blo 1108626 6085367 := bstep (se 1 (by rfl) ⟨4564025, by rfl⟩ : syracuseStep 6085367 = 9128051) B9128051
theorem B4873085 : Blo 1108626 4873085 := bstep (se 3 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 4873085 = 1827407) B1827407
theorem B5692331 : Blo 1108626 5692331 := bstep (se 1 (by rfl) ⟨4269248, by rfl⟩ : syracuseStep 5692331 = 8538497) B8538497
theorem B5627069 : Blo 1108626 5627069 := bstep (se 3 (by rfl) ⟨1055075, by rfl⟩ : syracuseStep 5627069 = 2110151) B2110151
theorem B9494009 : Blo 1108626 9494009 := bstep (se 2 (by rfl) ⟨3560253, by rfl⟩ : syracuseStep 9494009 = 7120507) B7120507
theorem B8019479 : Blo 1108626 8019479 := bstep (se 1 (by rfl) ⟨6014609, by rfl⟩ : syracuseStep 8019479 = 12029219) B12029219
theorem B2809505 : Blo 1108626 2809505 := bstep (se 2 (by rfl) ⟨1053564, by rfl⟩ : syracuseStep 2809505 = 2107129) B2107129
theorem B12181241 : Blo 1108626 12181241 := bstep (se 2 (by rfl) ⟨4567965, by rfl⟩ : syracuseStep 12181241 = 9135931) B9135931
theorem B2252585 : Blo 1108626 2252585 := bstep (se 2 (by rfl) ⟨844719, by rfl⟩ : syracuseStep 2252585 = 1689439) B1689439
theorem B5693257 : Blo 1108626 5693257 := bstep (se 2 (by rfl) ⟨2134971, by rfl⟩ : syracuseStep 5693257 = 4269943) B4269943
theorem B7593857 : Blo 1108626 7593857 := bstep (se 2 (by rfl) ⟨2847696, by rfl⟩ : syracuseStep 7593857 = 5695393) B5695393
theorem B4743193 : Blo 1108626 4743193 := bstep (se 2 (by rfl) ⟨1778697, by rfl⟩ : syracuseStep 4743193 = 3557395) B3557395
theorem B4218905 : Blo 1108626 4218905 := bstep (se 2 (by rfl) ⟨1582089, by rfl⟩ : syracuseStep 4218905 = 3164179) B3164179
theorem B2809961 : Blo 1108626 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B61661357 : Blo 1108626 61661357 := bstep (se 3 (by rfl) ⟨11561504, by rfl⟩ : syracuseStep 61661357 = 23123009) B23123009
theorem B1663241 : Blo 1108626 1663241 := bstep (se 2 (by rfl) ⟨623715, by rfl⟩ : syracuseStep 1663241 = 1247431) B1247431
theorem B1663343 : Blo 1108626 1663343 := bstep (se 1 (by rfl) ⟨1247507, by rfl⟩ : syracuseStep 1663343 = 2495015) B2495015
theorem B4219361 : Blo 1108626 4219361 := bstep (se 2 (by rfl) ⟨1582260, by rfl⟩ : syracuseStep 4219361 = 3164521) B3164521
theorem B1663559 : Blo 1108626 1663559 := bstep (se 1 (by rfl) ⟨1247669, by rfl⟩ : syracuseStep 1663559 = 2495339) B2495339
theorem B2810447 : Blo 1108626 2810447 := bstep (se 1 (by rfl) ⟨2107835, by rfl⟩ : syracuseStep 2810447 = 4215671) B4215671
theorem B1663595 : Blo 1108626 1663595 := bstep (se 1 (by rfl) ⟨1247696, by rfl⟩ : syracuseStep 1663595 = 2495393) B2495393
theorem B13001363 : Blo 1108626 13001363 := bstep (se 1 (by rfl) ⟨9751022, by rfl⟩ : syracuseStep 13001363 = 19502045) B19502045
theorem B4809431 : Blo 1108626 4809431 := bstep (se 1 (by rfl) ⟨3607073, by rfl⟩ : syracuseStep 4809431 = 7214147) B7214147
theorem B8446679 : Blo 1108626 8446679 := bstep (se 1 (by rfl) ⟨6335009, by rfl⟩ : syracuseStep 8446679 = 12670019) B12670019
theorem B1663823 : Blo 1108626 1663823 := bstep (se 1 (by rfl) ⟨1247867, by rfl⟩ : syracuseStep 1663823 = 2495735) B2495735
theorem B2811095 : Blo 1108626 2811095 := bstep (se 1 (by rfl) ⟨2108321, by rfl⟩ : syracuseStep 2811095 = 4216643) B4216643
theorem B1664219 : Blo 1108626 1664219 := bstep (se 1 (by rfl) ⟨1248164, by rfl⟩ : syracuseStep 1664219 = 2496329) B2496329
theorem B1664393 : Blo 1108626 1664393 := bstep (se 2 (by rfl) ⟨624147, by rfl⟩ : syracuseStep 1664393 = 1248295) B1248295
theorem B410936753 : Blo 1108626 410936753 := bstep (se 2 (by rfl) ⟨154101282, by rfl⟩ : syracuseStep 410936753 = 308202565) B308202565
theorem B21325301 : Blo 1108626 21325301 := bstep (se 5 (by rfl) ⟨999623, by rfl⟩ : syracuseStep 21325301 = 1999247) B1999247
theorem B2811449 : Blo 1108626 2811449 := bstep (se 2 (by rfl) ⟨1054293, by rfl⟩ : syracuseStep 2811449 = 2108587) B2108587
theorem B1664747 : Blo 1108626 1664747 := bstep (se 1 (by rfl) ⟨1248560, by rfl⟩ : syracuseStep 1664747 = 2497121) B2497121
theorem B1664975 : Blo 1108626 1664975 := bstep (se 1 (by rfl) ⟨1248731, by rfl⟩ : syracuseStep 1664975 = 2497463) B2497463
theorem B5629985 : Blo 1108626 5629985 := bstep (se 2 (by rfl) ⟨2111244, by rfl⟩ : syracuseStep 5629985 = 4222489) B4222489
theorem B5630147 : Blo 1108626 5630147 := bstep (se 1 (by rfl) ⟨4222610, by rfl⟩ : syracuseStep 5630147 = 8445221) B8445221
theorem B1665371 : Blo 1108626 1665371 := bstep (se 1 (by rfl) ⟨1249028, by rfl⟩ : syracuseStep 1665371 = 2498057) B2498057
theorem B11397505 : Blo 1108626 11397505 := bstep (se 2 (by rfl) ⟨4274064, by rfl⟩ : syracuseStep 11397505 = 8548129) B8548129
theorem B1403335 : Blo 1108626 1403335 := bstep (se 1 (by rfl) ⟨1052501, by rfl⟩ : syracuseStep 1403335 = 2105003) B2105003
theorem B1665599 : Blo 1108626 1665599 := bstep (se 1 (by rfl) ⟨1249199, by rfl⟩ : syracuseStep 1665599 = 2498399) B2498399
theorem B4221503 : Blo 1108626 4221503 := bstep (se 1 (by rfl) ⟨3166127, by rfl⟩ : syracuseStep 4221503 = 6332255) B6332255
theorem B1665719 : Blo 1108626 1665719 := bstep (se 1 (by rfl) ⟨1249289, by rfl⟩ : syracuseStep 1665719 = 2498579) B2498579
theorem B1108703 : Blo 1108626 1108703 := bstep (se 1 (by rfl) ⟨831527, by rfl⟩ : syracuseStep 1108703 = 1663055) B1663055
theorem B1108783 : Blo 1108626 1108783 := bstep (se 1 (by rfl) ⟨831587, by rfl⟩ : syracuseStep 1108783 = 1663175) B1663175
theorem B11987837 : Blo 1108626 11987837 := bstep (se 3 (by rfl) ⟨2247719, by rfl⟩ : syracuseStep 11987837 = 4495439) B4495439
theorem B4221821 : Blo 1108626 4221821 := bstep (se 3 (by rfl) ⟨791591, by rfl⟩ : syracuseStep 4221821 = 1583183) B1583183
theorem B1108891 : Blo 1108626 1108891 := bstep (se 1 (by rfl) ⟨831668, by rfl⟩ : syracuseStep 1108891 = 1663337) B1663337
theorem B1665947 : Blo 1108626 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B1108943 : Blo 1108626 1108943 := bstep (se 1 (by rfl) ⟨831707, by rfl⟩ : syracuseStep 1108943 = 1663415) B1663415
theorem B1108967 : Blo 1108626 1108967 := bstep (se 1 (by rfl) ⟨831725, by rfl⟩ : syracuseStep 1108967 = 1663451) B1663451
theorem B15428647 : Blo 1108626 15428647 := bstep (se 1 (by rfl) ⟨11571485, by rfl⟩ : syracuseStep 15428647 = 23142971) B23142971
theorem B23981275 : Blo 1108626 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B1109279 : Blo 1108626 1109279 := bstep (se 1 (by rfl) ⟨831959, by rfl⟩ : syracuseStep 1109279 = 1663919) B1663919
theorem B1666343 : Blo 1108626 1666343 := bstep (se 1 (by rfl) ⟨1249757, by rfl⟩ : syracuseStep 1666343 = 2499515) B2499515
theorem B1109339 : Blo 1108626 1109339 := bstep (se 1 (by rfl) ⟨832004, by rfl⟩ : syracuseStep 1109339 = 1664009) B1664009
theorem B1109359 : Blo 1108626 1109359 := bstep (se 1 (by rfl) ⟨832019, by rfl⟩ : syracuseStep 1109359 = 1664039) B1664039
theorem B20245879 : Blo 1108626 20245879 := bstep (se 1 (by rfl) ⟨15184409, by rfl⟩ : syracuseStep 20245879 = 30368819) B30368819
theorem B1666427 : Blo 1108626 1666427 := bstep (se 1 (by rfl) ⟨1249820, by rfl⟩ : syracuseStep 1666427 = 2499641) B2499641
theorem B1109415 : Blo 1108626 1109415 := bstep (se 1 (by rfl) ⟨832061, by rfl⟩ : syracuseStep 1109415 = 1664123) B1664123
theorem B1666553 : Blo 1108626 1666553 := bstep (se 2 (by rfl) ⟨624957, by rfl⟩ : syracuseStep 1666553 = 1249915) B1249915
theorem B1109499 : Blo 1108626 1109499 := bstep (se 1 (by rfl) ⟨832124, by rfl⟩ : syracuseStep 1109499 = 1664249) B1664249
theorem B1109567 : Blo 1108626 1109567 := bstep (se 1 (by rfl) ⟨832175, by rfl⟩ : syracuseStep 1109567 = 1664351) B1664351
theorem B1404479 : Blo 1108626 1404479 := bstep (se 1 (by rfl) ⟨1053359, by rfl⟩ : syracuseStep 1404479 = 2106719) B2106719
theorem B1109575 : Blo 1108626 1109575 := bstep (se 1 (by rfl) ⟨832181, by rfl⟩ : syracuseStep 1109575 = 1664363) B1664363
theorem B1666655 : Blo 1108626 1666655 := bstep (se 1 (by rfl) ⟨1249991, by rfl⟩ : syracuseStep 1666655 = 2499983) B2499983
theorem B11398819 : Blo 1108626 11398819 := bstep (se 1 (by rfl) ⟨8549114, by rfl⟩ : syracuseStep 11398819 = 17098229) B17098229
theorem B1109727 : Blo 1108626 1109727 := bstep (se 1 (by rfl) ⟨832295, by rfl⟩ : syracuseStep 1109727 = 1664591) B1664591
theorem B6319883 : Blo 1108626 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B2813737 : Blo 1108626 2813737 := bstep (se 2 (by rfl) ⟨1055151, by rfl⟩ : syracuseStep 2813737 = 2110303) B2110303
theorem B1109807 : Blo 1108626 1109807 := bstep (se 1 (by rfl) ⟨832355, by rfl⟩ : syracuseStep 1109807 = 1664711) B1664711
theorem B1666871 : Blo 1108626 1666871 := bstep (se 1 (by rfl) ⟨1250153, by rfl⟩ : syracuseStep 1666871 = 2500307) B2500307
theorem B1109915 : Blo 1108626 1109915 := bstep (se 1 (by rfl) ⟨832436, by rfl⟩ : syracuseStep 1109915 = 1664873) B1664873
theorem B1109967 : Blo 1108626 1109967 := bstep (se 1 (by rfl) ⟨832475, by rfl⟩ : syracuseStep 1109967 = 1664951) B1664951
theorem B1109991 : Blo 1108626 1109991 := bstep (se 1 (by rfl) ⟨832493, by rfl⟩ : syracuseStep 1109991 = 1664987) B1664987
theorem B10678337 : Blo 1108626 10678337 := bstep (se 2 (by rfl) ⟨4004376, by rfl⟩ : syracuseStep 10678337 = 8008753) B8008753
theorem B24047705 : Blo 1108626 24047705 := bstep (se 2 (by rfl) ⟨9017889, by rfl⟩ : syracuseStep 24047705 = 18035779) B18035779
theorem B1667177 : Blo 1108626 1667177 := bstep (se 2 (by rfl) ⟨625191, by rfl⟩ : syracuseStep 1667177 = 1250383) B1250383
theorem B1110303 : Blo 1108626 1110303 := bstep (se 1 (by rfl) ⟨832727, by rfl⟩ : syracuseStep 1110303 = 1665455) B1665455
theorem B1110363 : Blo 1108626 1110363 := bstep (se 1 (by rfl) ⟨832772, by rfl⟩ : syracuseStep 1110363 = 1665545) B1665545
theorem B1110383 : Blo 1108626 1110383 := bstep (se 1 (by rfl) ⟨832787, by rfl⟩ : syracuseStep 1110383 = 1665575) B1665575
theorem B1110439 : Blo 1108626 1110439 := bstep (se 1 (by rfl) ⟨832829, by rfl⟩ : syracuseStep 1110439 = 1665659) B1665659
theorem B1667495 : Blo 1108626 1667495 := bstep (se 1 (by rfl) ⟨1250621, by rfl⟩ : syracuseStep 1667495 = 2501243) B2501243
theorem B1110523 : Blo 1108626 1110523 := bstep (se 1 (by rfl) ⟨832892, by rfl⟩ : syracuseStep 1110523 = 1665785) B1665785
theorem B1667579 : Blo 1108626 1667579 := bstep (se 1 (by rfl) ⟨1250684, by rfl⟩ : syracuseStep 1667579 = 2501369) B2501369
theorem B1110591 : Blo 1108626 1110591 := bstep (se 1 (by rfl) ⟨832943, by rfl⟩ : syracuseStep 1110591 = 1665887) B1665887
theorem B2814527 : Blo 1108626 2814527 := bstep (se 1 (by rfl) ⟨2110895, by rfl⟩ : syracuseStep 2814527 = 4221791) B4221791
theorem B1110599 : Blo 1108626 1110599 := bstep (se 1 (by rfl) ⟨832949, by rfl⟩ : syracuseStep 1110599 = 1665899) B1665899
theorem B1667705 : Blo 1108626 1667705 := bstep (se 2 (by rfl) ⟨625389, by rfl⟩ : syracuseStep 1667705 = 1250779) B1250779
theorem B1667759 : Blo 1108626 1667759 := bstep (se 1 (by rfl) ⟨1250819, by rfl⟩ : syracuseStep 1667759 = 2501639) B2501639
theorem B1110751 : Blo 1108626 1110751 := bstep (se 1 (by rfl) ⟨833063, by rfl⟩ : syracuseStep 1110751 = 1666127) B1666127
theorem B1667807 : Blo 1108626 1667807 := bstep (se 1 (by rfl) ⟨1250855, by rfl⟩ : syracuseStep 1667807 = 2501711) B2501711
theorem B1110831 : Blo 1108626 1110831 := bstep (se 1 (by rfl) ⟨833123, by rfl⟩ : syracuseStep 1110831 = 1666247) B1666247
theorem B1405775 : Blo 1108626 1405775 := bstep (se 1 (by rfl) ⟨1054331, by rfl⟩ : syracuseStep 1405775 = 2108663) B2108663
theorem B1110939 : Blo 1108626 1110939 := bstep (se 1 (by rfl) ⟨833204, by rfl⟩ : syracuseStep 1110939 = 1666409) B1666409
theorem B28832687 : Blo 1108626 28832687 := bstep (se 1 (by rfl) ⟨21624515, by rfl⟩ : syracuseStep 28832687 = 43249031) B43249031
theorem B1110991 : Blo 1108626 1110991 := bstep (se 1 (by rfl) ⟨833243, by rfl⟩ : syracuseStep 1110991 = 1666487) B1666487
theorem B1405927 : Blo 1108626 1405927 := bstep (se 1 (by rfl) ⟨1054445, by rfl⟩ : syracuseStep 1405927 = 2108891) B2108891
theorem B1111015 : Blo 1108626 1111015 := bstep (se 1 (by rfl) ⟨833261, by rfl⟩ : syracuseStep 1111015 = 1666523) B1666523
theorem B1668071 : Blo 1108626 1668071 := bstep (se 1 (by rfl) ⟨1251053, by rfl⟩ : syracuseStep 1668071 = 2502107) B2502107
theorem B7992377 : Blo 1108626 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B2815175 : Blo 1108626 2815175 := bstep (se 1 (by rfl) ⟨2111381, by rfl⟩ : syracuseStep 2815175 = 4222763) B4222763
theorem B2815195 : Blo 1108626 2815195 := bstep (se 1 (by rfl) ⟨2111396, by rfl⟩ : syracuseStep 2815195 = 4222793) B4222793
theorem B1668329 : Blo 1108626 1668329 := bstep (se 2 (by rfl) ⟨625623, by rfl⟩ : syracuseStep 1668329 = 1251247) B1251247
theorem B1111327 : Blo 1108626 1111327 := bstep (se 1 (by rfl) ⟨833495, by rfl⟩ : syracuseStep 1111327 = 1666991) B1666991
theorem B1668383 : Blo 1108626 1668383 := bstep (se 1 (by rfl) ⟨1251287, by rfl⟩ : syracuseStep 1668383 = 2502575) B2502575
theorem B1111387 : Blo 1108626 1111387 := bstep (se 1 (by rfl) ⟨833540, by rfl⟩ : syracuseStep 1111387 = 1667081) B1667081
theorem B1111407 : Blo 1108626 1111407 := bstep (se 1 (by rfl) ⟨833555, by rfl⟩ : syracuseStep 1111407 = 1667111) B1667111
theorem B1111463 : Blo 1108626 1111463 := bstep (se 1 (by rfl) ⟨833597, by rfl⟩ : syracuseStep 1111463 = 1667195) B1667195
theorem B1668551 : Blo 1108626 1668551 := bstep (se 1 (by rfl) ⟨1251413, by rfl⟩ : syracuseStep 1668551 = 2502827) B2502827
theorem B1111547 : Blo 1108626 1111547 := bstep (se 1 (by rfl) ⟨833660, by rfl⟩ : syracuseStep 1111547 = 1667321) B1667321
theorem B1111615 : Blo 1108626 1111615 := bstep (se 1 (by rfl) ⟨833711, by rfl⟩ : syracuseStep 1111615 = 1667423) B1667423
theorem B1111623 : Blo 1108626 1111623 := bstep (se 1 (by rfl) ⟨833717, by rfl⟩ : syracuseStep 1111623 = 1667435) B1667435
theorem B1111775 : Blo 1108626 1111775 := bstep (se 1 (by rfl) ⟨833831, by rfl⟩ : syracuseStep 1111775 = 1667663) B1667663
theorem B1668905 : Blo 1108626 1668905 := bstep (se 2 (by rfl) ⟨625839, by rfl⟩ : syracuseStep 1668905 = 1251679) B1251679
theorem B1111855 : Blo 1108626 1111855 := bstep (se 1 (by rfl) ⟨833891, by rfl⟩ : syracuseStep 1111855 = 1667783) B1667783
theorem B1668911 : Blo 1108626 1668911 := bstep (se 1 (by rfl) ⟨1251683, by rfl⟩ : syracuseStep 1668911 = 2503367) B2503367
theorem B1111963 : Blo 1108626 1111963 := bstep (se 1 (by rfl) ⟨833972, by rfl⟩ : syracuseStep 1111963 = 1667945) B1667945
theorem B1112015 : Blo 1108626 1112015 := bstep (se 1 (by rfl) ⟨834011, by rfl⟩ : syracuseStep 1112015 = 1668023) B1668023
theorem B1112039 : Blo 1108626 1112039 := bstep (se 1 (by rfl) ⟨834029, by rfl⟩ : syracuseStep 1112039 = 1668059) B1668059
theorem B8419463 : Blo 1108626 8419463 := bstep (se 1 (by rfl) ⟨6314597, by rfl⟩ : syracuseStep 8419463 = 12629195) B12629195
theorem B1112351 : Blo 1108626 1112351 := bstep (se 1 (by rfl) ⟨834263, by rfl⟩ : syracuseStep 1112351 = 1668527) B1668527
theorem B2816329 : Blo 1108626 2816329 := bstep (se 2 (by rfl) ⟨1056123, by rfl⟩ : syracuseStep 2816329 = 2112247) B2112247
theorem B1112411 : Blo 1108626 1112411 := bstep (se 1 (by rfl) ⟨834308, by rfl⟩ : syracuseStep 1112411 = 1668617) B1668617
theorem B1112431 : Blo 1108626 1112431 := bstep (se 1 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 1112431 = 1668647) B1668647
theorem B1112487 : Blo 1108626 1112487 := bstep (se 1 (by rfl) ⟨834365, by rfl⟩ : syracuseStep 1112487 = 1668731) B1668731
theorem B1112571 : Blo 1108626 1112571 := bstep (se 1 (by rfl) ⟨834428, by rfl⟩ : syracuseStep 1112571 = 1668857) B1668857
theorem B9501421 : Blo 1108626 9501421 := bstep (se 3 (by rfl) ⟨1781516, by rfl⟩ : syracuseStep 9501421 = 3563033) B3563033
theorem B356023187 : Blo 1108626 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B17071631 : Blo 1108626 17071631 := bstep (se 1 (by rfl) ⟨12803723, by rfl⟩ : syracuseStep 17071631 = 25607447) B25607447
theorem B3997487 : Blo 1108626 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B6324257 : Blo 1108626 6324257 := bstep (se 2 (by rfl) ⟨2371596, by rfl⟩ : syracuseStep 6324257 = 4743193) B4743193
theorem B64127213 : Blo 1108626 64127213 := bstep (se 3 (by rfl) ⟨12023852, by rfl⟩ : syracuseStep 64127213 = 24047705) B24047705
theorem B7996067 : Blo 1108626 7996067 := bstep (se 1 (by rfl) ⟨5997050, by rfl⟩ : syracuseStep 7996067 = 11994101) B11994101
theorem B45515479 : Blo 1108626 45515479 := bstep (se 1 (by rfl) ⟨34136609, by rfl⟩ : syracuseStep 45515479 = 68273219) B68273219
theorem B1247215 : Blo 1108626 1247215 := bstep (se 1 (by rfl) ⟨935411, by rfl⟩ : syracuseStep 1247215 = 1870823) B1870823
theorem B7997449 : Blo 1108626 7997449 := bstep (se 2 (by rfl) ⟨2999043, by rfl⟩ : syracuseStep 7997449 = 5998087) B5998087
theorem B3606763 : Blo 1108626 3606763 := bstep (se 1 (by rfl) ⟨2705072, by rfl⟩ : syracuseStep 3606763 = 5410145) B5410145
theorem B4000225 : Blo 1108626 4000225 := bstep (se 2 (by rfl) ⟨1500084, by rfl⟩ : syracuseStep 4000225 = 3000169) B3000169
theorem B1871113 : Blo 1108626 1871113 := bstep (se 2 (by rfl) ⟨701667, by rfl⟩ : syracuseStep 1871113 = 1403335) B1403335
theorem B9014777 : Blo 1108626 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B1871687 : Blo 1108626 1871687 := bstep (se 1 (by rfl) ⟨1403765, by rfl⟩ : syracuseStep 1871687 = 2807531) B2807531
theorem B1249663 : Blo 1108626 1249663 := bstep (se 1 (by rfl) ⟨937247, by rfl⟩ : syracuseStep 1249663 = 1874495) B1874495
theorem B4002185 : Blo 1108626 4002185 := bstep (se 2 (by rfl) ⟨1500819, by rfl⟩ : syracuseStep 4002185 = 3001639) B3001639
theorem B1872335 : Blo 1108626 1872335 := bstep (se 1 (by rfl) ⟨1404251, by rfl⟩ : syracuseStep 1872335 = 2808503) B2808503
theorem B3248723 : Blo 1108626 3248723 := bstep (se 1 (by rfl) ⟨2436542, by rfl⟩ : syracuseStep 3248723 = 4873085) B4873085
theorem B2495483 : Blo 1108626 2495483 := bstep (se 1 (by rfl) ⟨1871612, by rfl⟩ : syracuseStep 2495483 = 3743225) B3743225
theorem B6329339 : Blo 1108626 6329339 := bstep (se 1 (by rfl) ⟨4747004, by rfl⟩ : syracuseStep 6329339 = 9494009) B9494009
theorem B5346319 : Blo 1108626 5346319 := bstep (se 1 (by rfl) ⟨4009739, by rfl⟩ : syracuseStep 5346319 = 8019479) B8019479
theorem B20255807 : Blo 1108626 20255807 := bstep (se 1 (by rfl) ⟨15191855, by rfl⟩ : syracuseStep 20255807 = 30383711) B30383711
theorem B1873003 : Blo 1108626 1873003 := bstep (se 1 (by rfl) ⟨1404752, by rfl⟩ : syracuseStep 1873003 = 2809505) B2809505
theorem B2495663 : Blo 1108626 2495663 := bstep (se 1 (by rfl) ⟨1871747, by rfl⟩ : syracuseStep 2495663 = 3743495) B3743495
theorem B6755537 : Blo 1108626 6755537 := bstep (se 2 (by rfl) ⟨2533326, by rfl⟩ : syracuseStep 6755537 = 5066653) B5066653
theorem B2495699 : Blo 1108626 2495699 := bstep (se 1 (by rfl) ⟨1871774, by rfl⟩ : syracuseStep 2495699 = 3743549) B3743549
theorem B1873307 : Blo 1108626 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B2495969 : Blo 1108626 2495969 := bstep (se 2 (by rfl) ⟨935988, by rfl⟩ : syracuseStep 2495969 = 1871977) B1871977
theorem B82286117 : Blo 1108626 82286117 := bstep (se 4 (by rfl) ⟨7714323, by rfl⟩ : syracuseStep 82286117 = 15428647) B15428647
theorem B1873631 : Blo 1108626 1873631 := bstep (se 1 (by rfl) ⟨1405223, by rfl⟩ : syracuseStep 1873631 = 2810447) B2810447
theorem B1251067 : Blo 1108626 1251067 := bstep (se 1 (by rfl) ⟨938300, by rfl⟩ : syracuseStep 1251067 = 1876601) B1876601
theorem B1251103 : Blo 1108626 1251103 := bstep (se 1 (by rfl) ⟨938327, by rfl⟩ : syracuseStep 1251103 = 1876655) B1876655
theorem B1578889 : Blo 1108626 1578889 := bstep (se 2 (by rfl) ⟨592083, by rfl⟩ : syracuseStep 1578889 = 1184167) B1184167
theorem B3741659 : Blo 1108626 3741659 := bstep (se 1 (by rfl) ⟨2806244, by rfl⟩ : syracuseStep 3741659 = 5612489) B5612489
theorem B8001665 : Blo 1108626 8001665 := bstep (se 2 (by rfl) ⟨3000624, by rfl⟩ : syracuseStep 8001665 = 6001249) B6001249
theorem B1874063 : Blo 1108626 1874063 := bstep (se 1 (by rfl) ⟨1405547, by rfl⟩ : syracuseStep 1874063 = 2811095) B2811095
theorem B3741929 : Blo 1108626 3741929 := bstep (se 2 (by rfl) ⟨1403223, by rfl⟩ : syracuseStep 3741929 = 2806447) B2806447
theorem B1874299 : Blo 1108626 1874299 := bstep (se 1 (by rfl) ⟨1405724, by rfl⟩ : syracuseStep 1874299 = 2811449) B2811449
theorem B1874569 : Blo 1108626 1874569 := bstep (se 2 (by rfl) ⟨702963, by rfl⟩ : syracuseStep 1874569 = 1405927) B1405927
theorem B3742361 : Blo 1108626 3742361 := bstep (se 2 (by rfl) ⟨1403385, by rfl⟩ : syracuseStep 3742361 = 2806771) B2806771
theorem B2497607 : Blo 1108626 2497607 := bstep (se 1 (by rfl) ⟨1873205, by rfl⟩ : syracuseStep 2497607 = 3746411) B3746411
theorem B1580153 : Blo 1108626 1580153 := bstep (se 2 (by rfl) ⟨592557, by rfl⟩ : syracuseStep 1580153 = 1185115) B1185115
theorem B107978021 : Blo 1108626 107978021 := bstep (se 4 (by rfl) ⟨10122939, by rfl⟩ : syracuseStep 107978021 = 20245879) B20245879
theorem B2498003 : Blo 1108626 2498003 := bstep (se 1 (by rfl) ⟨1873502, by rfl⟩ : syracuseStep 2498003 = 3747005) B3747005
theorem B2498273 : Blo 1108626 2498273 := bstep (se 2 (by rfl) ⟨936852, by rfl⟩ : syracuseStep 2498273 = 1873705) B1873705
theorem B7118891 : Blo 1108626 7118891 := bstep (se 1 (by rfl) ⟨5339168, by rfl⟩ : syracuseStep 7118891 = 10678337) B10678337
theorem B1876351 : Blo 1108626 1876351 := bstep (se 1 (by rfl) ⟨1407263, by rfl⟩ : syracuseStep 1876351 = 2814527) B2814527
theorem B3744251 : Blo 1108626 3744251 := bstep (se 1 (by rfl) ⟨2808188, by rfl⟩ : syracuseStep 3744251 = 5616377) B5616377
theorem B3744521 : Blo 1108626 3744521 := bstep (se 2 (by rfl) ⟨1404195, by rfl⟩ : syracuseStep 3744521 = 2808391) B2808391
theorem B1778441 : Blo 1108626 1778441 := bstep (se 2 (by rfl) ⟨666915, by rfl⟩ : syracuseStep 1778441 = 1333831) B1333831
theorem B1876783 : Blo 1108626 1876783 := bstep (se 1 (by rfl) ⟨1407587, by rfl⟩ : syracuseStep 1876783 = 2815175) B2815175
theorem B4006799 : Blo 1108626 4006799 := bstep (se 1 (by rfl) ⟨3005099, by rfl⟩ : syracuseStep 4006799 = 6010199) B6010199
theorem B2499947 : Blo 1108626 2499947 := bstep (se 1 (by rfl) ⟨1874960, by rfl⟩ : syracuseStep 2499947 = 3749921) B3749921
theorem B5612975 : Blo 1108626 5612975 := bstep (se 1 (by rfl) ⟨4209731, by rfl⟩ : syracuseStep 5612975 = 8419463) B8419463
theorem B3745277 : Blo 1108626 3745277 := bstep (se 3 (by rfl) ⟨702239, by rfl⟩ : syracuseStep 3745277 = 1404479) B1404479
theorem B7611911 : Blo 1108626 7611911 := bstep (se 1 (by rfl) ⟨5708933, by rfl⟩ : syracuseStep 7611911 = 11417867) B11417867
theorem B5613137 : Blo 1108626 5613137 := bstep (se 2 (by rfl) ⟨2104926, by rfl⟩ : syracuseStep 5613137 = 4209853) B4209853
theorem B2500217 : Blo 1108626 2500217 := bstep (se 2 (by rfl) ⟨937581, by rfl⟩ : syracuseStep 2500217 = 1875163) B1875163
theorem B3417985 : Blo 1108626 3417985 := bstep (se 2 (by rfl) ⟨1281744, by rfl⟩ : syracuseStep 3417985 = 2563489) B2563489
theorem B237348791 : Blo 1108626 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B3746087 : Blo 1108626 3746087 := bstep (se 1 (by rfl) ⟨2809565, by rfl⟩ : syracuseStep 3746087 = 5619131) B5619131
theorem B11381087 : Blo 1108626 11381087 := bstep (se 1 (by rfl) ⟨8535815, by rfl⟩ : syracuseStep 11381087 = 17071631) B17071631
theorem B2664991 : Blo 1108626 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B8006215 : Blo 1108626 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B2501225 : Blo 1108626 2501225 := bstep (se 2 (by rfl) ⟨937959, by rfl⟩ : syracuseStep 2501225 = 1875919) B1875919
theorem B9480887 : Blo 1108626 9480887 := bstep (se 1 (by rfl) ⟨7110665, by rfl⟩ : syracuseStep 9480887 = 14221331) B14221331
theorem B83143361 : Blo 1108626 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B6335171 : Blo 1108626 6335171 := bstep (se 1 (by rfl) ⟨4751378, by rfl⟩ : syracuseStep 6335171 = 9502757) B9502757
theorem B2370359 : Blo 1108626 2370359 := bstep (se 1 (by rfl) ⟨1777769, by rfl⟩ : syracuseStep 2370359 = 3555539) B3555539
theorem B6007607 : Blo 1108626 6007607 := bstep (se 1 (by rfl) ⟨4505705, by rfl⟩ : syracuseStep 6007607 = 9011411) B9011411
theorem B3746951 : Blo 1108626 3746951 := bstep (se 1 (by rfl) ⟨2810213, by rfl⟩ : syracuseStep 3746951 = 5620427) B5620427
theorem B2501855 : Blo 1108626 2501855 := bstep (se 1 (by rfl) ⟨1876391, by rfl⟩ : syracuseStep 2501855 = 3752783) B3752783
theorem B3747059 : Blo 1108626 3747059 := bstep (se 1 (by rfl) ⟨2810294, by rfl⟩ : syracuseStep 3747059 = 5620589) B5620589
theorem B2502071 : Blo 1108626 2502071 := bstep (se 1 (by rfl) ⟨1876553, by rfl⟩ : syracuseStep 2502071 = 3753107) B3753107
theorem B48672353 : Blo 1108626 48672353 := bstep (se 2 (by rfl) ⟨18252132, by rfl⟩ : syracuseStep 48672353 = 36504265) B36504265
theorem B2502251 : Blo 1108626 2502251 := bstep (se 1 (by rfl) ⟨1876688, by rfl⟩ : syracuseStep 2502251 = 3753377) B3753377
theorem B2502521 : Blo 1108626 2502521 := bstep (se 2 (by rfl) ⟨938445, by rfl⟩ : syracuseStep 2502521 = 1876891) B1876891
theorem B10661807 : Blo 1108626 10661807 := bstep (se 1 (by rfl) ⟨7996355, by rfl⟩ : syracuseStep 10661807 = 15992711) B15992711
theorem B8007599 : Blo 1108626 8007599 := bstep (se 1 (by rfl) ⟨6005699, by rfl⟩ : syracuseStep 8007599 = 12011399) B12011399
theorem B5615567 : Blo 1108626 5615567 := bstep (se 1 (by rfl) ⟨4211675, by rfl⟩ : syracuseStep 5615567 = 8423351) B8423351
theorem B5058683 : Blo 1108626 5058683 := bstep (se 1 (by rfl) ⟨3794012, by rfl⟩ : syracuseStep 5058683 = 7588025) B7588025
theorem B5059027 : Blo 1108626 5059027 := bstep (se 1 (by rfl) ⟨3794270, by rfl⟩ : syracuseStep 5059027 = 7588541) B7588541
theorem B3158689 : Blo 1108626 3158689 := bstep (se 2 (by rfl) ⟨1184508, by rfl⟩ : syracuseStep 3158689 = 2369017) B2369017
theorem B3748733 : Blo 1108626 3748733 := bstep (se 3 (by rfl) ⟨702887, by rfl⟩ : syracuseStep 3748733 = 1405775) B1405775
theorem B3749003 : Blo 1108626 3749003 := bstep (se 1 (by rfl) ⟨2811752, by rfl⟩ : syracuseStep 3749003 = 5623505) B5623505
theorem B2536795 : Blo 1108626 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B38450537 : Blo 1108626 38450537 := bstep (se 2 (by rfl) ⟨14418951, by rfl⟩ : syracuseStep 38450537 = 28837903) B28837903
theorem B5617025 : Blo 1108626 5617025 := bstep (se 2 (by rfl) ⟨2106384, by rfl⟩ : syracuseStep 5617025 = 4212769) B4212769
theorem B2536859 : Blo 1108626 2536859 := bstep (se 1 (by rfl) ⟨1902644, by rfl⟩ : syracuseStep 2536859 = 3805289) B3805289
theorem B3159623 : Blo 1108626 3159623 := bstep (se 1 (by rfl) ⟨2369717, by rfl⟩ : syracuseStep 3159623 = 4739435) B4739435
theorem B12007075 : Blo 1108626 12007075 := bstep (se 1 (by rfl) ⟨9005306, by rfl⟩ : syracuseStep 12007075 = 18010613) B18010613
theorem B3159965 : Blo 1108626 3159965 := bstep (se 3 (by rfl) ⟨592493, by rfl⟩ : syracuseStep 3159965 = 1184987) B1184987
theorem B3160147 : Blo 1108626 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B2373715 : Blo 1108626 2373715 := bstep (se 1 (by rfl) ⟨1780286, by rfl⟩ : syracuseStep 2373715 = 3560573) B3560573
theorem B4110479 : Blo 1108626 4110479 := bstep (se 1 (by rfl) ⟨3082859, by rfl⟩ : syracuseStep 4110479 = 6165719) B6165719
theorem B5617835 : Blo 1108626 5617835 := bstep (se 1 (by rfl) ⟨4213376, by rfl⟩ : syracuseStep 5617835 = 8426753) B8426753
theorem B3750623 : Blo 1108626 3750623 := bstep (se 1 (by rfl) ⟨2812967, by rfl⟩ : syracuseStep 3750623 = 5625935) B5625935
theorem B7125839 : Blo 1108626 7125839 := bstep (se 1 (by rfl) ⟨5344379, by rfl⟩ : syracuseStep 7125839 = 10688759) B10688759
theorem B31997177 : Blo 1108626 31997177 := bstep (se 2 (by rfl) ⟨11998941, by rfl⟩ : syracuseStep 31997177 = 23997883) B23997883
theorem B3751379 : Blo 1108626 3751379 := bstep (se 1 (by rfl) ⟨2813534, by rfl⟩ : syracuseStep 3751379 = 5627069) B5627069
theorem B8994277 : Blo 1108626 8994277 := bstep (se 4 (by rfl) ⟨843213, by rfl⟩ : syracuseStep 8994277 = 1686427) B1686427
theorem B3751649 : Blo 1108626 3751649 := bstep (se 2 (by rfl) ⟨1406868, by rfl⟩ : syracuseStep 3751649 = 2813737) B2813737
theorem B5062571 : Blo 1108626 5062571 := bstep (se 1 (by rfl) ⟨3796928, by rfl⟩ : syracuseStep 5062571 = 7593857) B7593857
theorem B41107571 : Blo 1108626 41107571 := bstep (se 1 (by rfl) ⟨30830678, by rfl⟩ : syracuseStep 41107571 = 61661357) B61661357
theorem B8667575 : Blo 1108626 8667575 := bstep (se 1 (by rfl) ⟨6500681, by rfl⟩ : syracuseStep 8667575 = 13001363) B13001363
theorem B3556153 : Blo 1108626 3556153 := bstep (se 2 (by rfl) ⟨1333557, by rfl⟩ : syracuseStep 3556153 = 2667115) B2667115
theorem B273957835 : Blo 1108626 273957835 := bstep (se 1 (by rfl) ⟨205468376, by rfl⟩ : syracuseStep 273957835 = 410936753) B410936753
theorem B7128323 : Blo 1108626 7128323 := bstep (se 1 (by rfl) ⟨5346242, by rfl⟩ : syracuseStep 7128323 = 10692485) B10692485
theorem B3753323 : Blo 1108626 3753323 := bstep (se 1 (by rfl) ⟨2814992, by rfl⟩ : syracuseStep 3753323 = 5629985) B5629985
theorem B3753431 : Blo 1108626 3753431 := bstep (se 1 (by rfl) ⟨2815073, by rfl⟩ : syracuseStep 3753431 = 5630147) B5630147
theorem B3163769 : Blo 1108626 3163769 := bstep (se 2 (by rfl) ⟨1186413, by rfl⟩ : syracuseStep 3163769 = 2372827) B2372827
theorem B3753593 : Blo 1108626 3753593 := bstep (se 2 (by rfl) ⟨1407597, by rfl⟩ : syracuseStep 3753593 = 2815195) B2815195
theorem B4737437 : Blo 1108626 4737437 := bstep (se 3 (by rfl) ⟨888269, by rfl⟩ : syracuseStep 4737437 = 1776539) B1776539
theorem B5622209 : Blo 1108626 5622209 := bstep (se 2 (by rfl) ⟨2108328, by rfl⟩ : syracuseStep 5622209 = 4216657) B4216657
theorem B3557857 : Blo 1108626 3557857 := bstep (se 2 (by rfl) ⟨1334196, by rfl⟩ : syracuseStep 3557857 = 2668393) B2668393
theorem B4213255 : Blo 1108626 4213255 := bstep (se 1 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 4213255 = 6319883) B6319883
theorem B7588703 : Blo 1108626 7588703 := bstep (se 1 (by rfl) ⟨5691527, by rfl⟩ : syracuseStep 7588703 = 11383055) B11383055
theorem B3755105 : Blo 1108626 3755105 := bstep (se 2 (by rfl) ⟨1408164, by rfl⟩ : syracuseStep 3755105 = 2816329) B2816329
theorem B3656927 : Blo 1108626 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B19221791 : Blo 1108626 19221791 := bstep (se 1 (by rfl) ⟨14416343, by rfl⟩ : syracuseStep 19221791 = 28832687) B28832687
theorem B5328251 : Blo 1108626 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B8015273 : Blo 1108626 8015273 := bstep (se 2 (by rfl) ⟨3005727, by rfl⟩ : syracuseStep 8015273 = 6011455) B6011455
theorem B12668561 : Blo 1108626 12668561 := bstep (se 2 (by rfl) ⟨4750710, by rfl⟩ : syracuseStep 12668561 = 9501421) B9501421
theorem B14209181 : Blo 1108626 14209181 := bstep (se 3 (by rfl) ⟨2664221, by rfl⟩ : syracuseStep 14209181 = 5328443) B5328443
theorem B22794533 : Blo 1108626 22794533 := bstep (se 4 (by rfl) ⟨2136987, by rfl⟩ : syracuseStep 22794533 = 4273975) B4273975
theorem B2806265 : Blo 1108626 2806265 := bstep (se 2 (by rfl) ⟨1052349, by rfl⟩ : syracuseStep 2806265 = 2104699) B2104699
theorem B4510505 : Blo 1108626 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B7591009 : Blo 1108626 7591009 := bstep (se 2 (by rfl) ⟨2846628, by rfl⟩ : syracuseStep 7591009 = 5693257) B5693257
theorem B3167687 : Blo 1108626 3167687 := bstep (se 1 (by rfl) ⟨2375765, by rfl⟩ : syracuseStep 3167687 = 4751531) B4751531
theorem B13522555 : Blo 1108626 13522555 := bstep (se 1 (by rfl) ⟨10141916, by rfl⟩ : syracuseStep 13522555 = 20283833) B20283833
theorem B5625611 : Blo 1108626 5625611 := bstep (se 1 (by rfl) ⟨4219208, by rfl⟩ : syracuseStep 5625611 = 8438417) B8438417
theorem B18241631 : Blo 1108626 18241631 := bstep (se 1 (by rfl) ⟨13681223, by rfl⟩ : syracuseStep 18241631 = 27362447) B27362447
theorem B2807905 : Blo 1108626 2807905 := bstep (se 2 (by rfl) ⟨1052964, by rfl⟩ : syracuseStep 2807905 = 2105929) B2105929
theorem B9492673 : Blo 1108626 9492673 := bstep (se 2 (by rfl) ⟨3559752, by rfl⟩ : syracuseStep 9492673 = 7119505) B7119505
theorem B10279111 : Blo 1108626 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B10148125 : Blo 1108626 10148125 := bstep (se 3 (by rfl) ⟨1902773, by rfl⟩ : syracuseStep 10148125 = 3805547) B3805547
theorem B4217129 : Blo 1108626 4217129 := bstep (se 2 (by rfl) ⟨1581423, by rfl⟩ : syracuseStep 4217129 = 3162847) B3162847
theorem B9492947 : Blo 1108626 9492947 := bstep (se 1 (by rfl) ⟨7119710, by rfl⟩ : syracuseStep 9492947 = 14239421) B14239421
theorem B14604889 : Blo 1108626 14604889 := bstep (se 2 (by rfl) ⟨5476833, by rfl⟩ : syracuseStep 14604889 = 10953667) B10953667
theorem B3857053 : Blo 1108626 3857053 := bstep (se 3 (by rfl) ⟨723197, by rfl⟩ : syracuseStep 3857053 = 1446395) B1446395
theorem B4742135 : Blo 1108626 4742135 := bstep (se 1 (by rfl) ⟨3556601, by rfl⟩ : syracuseStep 4742135 = 7113203) B7113203
theorem B4742495 : Blo 1108626 4742495 := bstep (se 1 (by rfl) ⟨3556871, by rfl⟩ : syracuseStep 4742495 = 7113743) B7113743
theorem B5627231 : Blo 1108626 5627231 := bstep (se 1 (by rfl) ⟨4220423, by rfl⟩ : syracuseStep 5627231 = 8440847) B8440847
theorem B5332385 : Blo 1108626 5332385 := bstep (se 2 (by rfl) ⟨1999644, by rfl⟩ : syracuseStep 5332385 = 3999289) B3999289
theorem B6315965 : Blo 1108626 6315965 := bstep (se 3 (by rfl) ⟨1184243, by rfl⟩ : syracuseStep 6315965 = 2368487) B2368487
theorem B1663439 : Blo 1108626 1663439 := bstep (se 1 (by rfl) ⟨1247579, by rfl⟩ : syracuseStep 1663439 = 2495159) B2495159
theorem B1663481 : Blo 1108626 1663481 := bstep (se 2 (by rfl) ⟨623805, by rfl⟩ : syracuseStep 1663481 = 1247611) B1247611
theorem B15196673 : Blo 1108626 15196673 := bstep (se 2 (by rfl) ⟨5698752, by rfl⟩ : syracuseStep 15196673 = 11397505) B11397505
theorem B1663583 : Blo 1108626 1663583 := bstep (se 1 (by rfl) ⟨1247687, by rfl⟩ : syracuseStep 1663583 = 2495375) B2495375
theorem B2810497 : Blo 1108626 2810497 := bstep (se 2 (by rfl) ⟨1053936, by rfl⟩ : syracuseStep 2810497 = 2107873) B2107873
theorem B21652103 : Blo 1108626 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B10838681 : Blo 1108626 10838681 := bstep (se 2 (by rfl) ⟨4064505, by rfl⟩ : syracuseStep 10838681 = 8129011) B8129011
theorem B9495407 : Blo 1108626 9495407 := bstep (se 1 (by rfl) ⟨7121555, by rfl⟩ : syracuseStep 9495407 = 14243111) B14243111
theorem B1139707 : Blo 1108626 1139707 := bstep (se 1 (by rfl) ⟨854780, by rfl⟩ : syracuseStep 1139707 = 1709561) B1709561
theorem B7103513 : Blo 1108626 7103513 := bstep (se 2 (by rfl) ⟨2663817, by rfl⟩ : syracuseStep 7103513 = 5327635) B5327635
theorem B1664063 : Blo 1108626 1664063 := bstep (se 1 (by rfl) ⟨1248047, by rfl⟩ : syracuseStep 1664063 = 2496095) B2496095
theorem B1664105 : Blo 1108626 1664105 := bstep (se 2 (by rfl) ⟨624039, by rfl⟩ : syracuseStep 1664105 = 1248079) B1248079
theorem B1664207 : Blo 1108626 1664207 := bstep (se 1 (by rfl) ⟨1248155, by rfl⟩ : syracuseStep 1664207 = 2496311) B2496311
theorem B14247211 : Blo 1108626 14247211 := bstep (se 1 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 14247211 = 21370817) B21370817
theorem B1664411 : Blo 1108626 1664411 := bstep (se 1 (by rfl) ⟨1248308, by rfl⟩ : syracuseStep 1664411 = 2496617) B2496617
theorem B2811307 : Blo 1108626 2811307 := bstep (se 1 (by rfl) ⟨2108480, by rfl⟩ : syracuseStep 2811307 = 4216961) B4216961
theorem B5629499 : Blo 1108626 5629499 := bstep (se 1 (by rfl) ⟨4222124, by rfl⟩ : syracuseStep 5629499 = 8444249) B8444249
theorem B7595603 : Blo 1108626 7595603 := bstep (se 1 (by rfl) ⟨5696702, by rfl⟩ : syracuseStep 7595603 = 11393405) B11393405
theorem B31975033 : Blo 1108626 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B1664633 : Blo 1108626 1664633 := bstep (se 2 (by rfl) ⟨624237, by rfl⟩ : syracuseStep 1664633 = 1248475) B1248475
theorem B2811611 : Blo 1108626 2811611 := bstep (se 1 (by rfl) ⟨2108708, by rfl⟩ : syracuseStep 2811611 = 4217417) B4217417
theorem B1664735 : Blo 1108626 1664735 := bstep (se 1 (by rfl) ⟨1248551, by rfl⟩ : syracuseStep 1664735 = 2497103) B2497103
theorem B6416135 : Blo 1108626 6416135 := bstep (se 1 (by rfl) ⟨4812101, by rfl⟩ : syracuseStep 6416135 = 9624203) B9624203
theorem B1664831 : Blo 1108626 1664831 := bstep (se 1 (by rfl) ⟨1248623, by rfl⟩ : syracuseStep 1664831 = 2497247) B2497247
theorem B4056911 : Blo 1108626 4056911 := bstep (se 1 (by rfl) ⟨3042683, by rfl⟩ : syracuseStep 4056911 = 6085367) B6085367
theorem B3794887 : Blo 1108626 3794887 := bstep (se 1 (by rfl) ⟨2846165, by rfl⟩ : syracuseStep 3794887 = 5692331) B5692331
theorem B1664999 : Blo 1108626 1664999 := bstep (se 1 (by rfl) ⟨1248749, by rfl⟩ : syracuseStep 1664999 = 2497499) B2497499
theorem B1665017 : Blo 1108626 1665017 := bstep (se 2 (by rfl) ⟨624381, by rfl⟩ : syracuseStep 1665017 = 1248763) B1248763
theorem B1665119 : Blo 1108626 1665119 := bstep (se 1 (by rfl) ⟨1248839, by rfl⟩ : syracuseStep 1665119 = 2497679) B2497679
theorem B1665179 : Blo 1108626 1665179 := bstep (se 1 (by rfl) ⟨1248884, by rfl⟩ : syracuseStep 1665179 = 2497769) B2497769
theorem B1665215 : Blo 1108626 1665215 := bstep (se 1 (by rfl) ⟨1248911, by rfl⟩ : syracuseStep 1665215 = 2497823) B2497823
theorem B15198425 : Blo 1108626 15198425 := bstep (se 2 (by rfl) ⟨5699409, by rfl⟩ : syracuseStep 15198425 = 11398819) B11398819
theorem B1665257 : Blo 1108626 1665257 := bstep (se 2 (by rfl) ⟨624471, by rfl⟩ : syracuseStep 1665257 = 1248943) B1248943
theorem B1403183 : Blo 1108626 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B281373101 : Blo 1108626 281373101 := bstep (se 3 (by rfl) ⟨52757456, by rfl⟩ : syracuseStep 281373101 = 105514913) B105514913
theorem B8120827 : Blo 1108626 8120827 := bstep (se 1 (by rfl) ⟨6090620, by rfl⟩ : syracuseStep 8120827 = 12181241) B12181241
theorem B1665563 : Blo 1108626 1665563 := bstep (se 1 (by rfl) ⟨1249172, by rfl⟩ : syracuseStep 1665563 = 2498345) B2498345
theorem B1501723 : Blo 1108626 1501723 := bstep (se 1 (by rfl) ⟨1126292, by rfl⟩ : syracuseStep 1501723 = 2252585) B2252585
theorem B1665641 : Blo 1108626 1665641 := bstep (se 2 (by rfl) ⟨624615, by rfl⟩ : syracuseStep 1665641 = 1249231) B1249231
theorem B4745911 : Blo 1108626 4745911 := bstep (se 1 (by rfl) ⟨3559433, by rfl⟩ : syracuseStep 4745911 = 7118867) B7118867
theorem B2812603 : Blo 1108626 2812603 := bstep (se 1 (by rfl) ⟨2109452, by rfl⟩ : syracuseStep 2812603 = 4218905) B4218905
theorem B1108827 : Blo 1108626 1108827 := bstep (se 1 (by rfl) ⟨831620, by rfl⟩ : syracuseStep 1108827 = 1663241) B1663241
theorem B1108895 : Blo 1108626 1108895 := bstep (se 1 (by rfl) ⟨831671, by rfl⟩ : syracuseStep 1108895 = 1663343) B1663343
theorem B20540395 : Blo 1108626 20540395 := bstep (se 1 (by rfl) ⟨15405296, by rfl⟩ : syracuseStep 20540395 = 30810593) B30810593
theorem B2812907 : Blo 1108626 2812907 := bstep (se 1 (by rfl) ⟨2109680, by rfl⟩ : syracuseStep 2812907 = 4219361) B4219361
theorem B1109039 : Blo 1108626 1109039 := bstep (se 1 (by rfl) ⟨831779, by rfl⟩ : syracuseStep 1109039 = 1663559) B1663559
theorem B1109063 : Blo 1108626 1109063 := bstep (se 1 (by rfl) ⟨831797, by rfl⟩ : syracuseStep 1109063 = 1663595) B1663595
theorem B1666169 : Blo 1108626 1666169 := bstep (se 2 (by rfl) ⟨624813, by rfl⟩ : syracuseStep 1666169 = 1249627) B1249627
theorem B1502329 : Blo 1108626 1502329 := bstep (se 2 (by rfl) ⟨563373, by rfl⟩ : syracuseStep 1502329 = 1126747) B1126747
theorem B3206287 : Blo 1108626 3206287 := bstep (se 1 (by rfl) ⟨2404715, by rfl⟩ : syracuseStep 3206287 = 4809431) B4809431
theorem B5631119 : Blo 1108626 5631119 := bstep (se 1 (by rfl) ⟨4223339, by rfl⟩ : syracuseStep 5631119 = 8446679) B8446679
theorem B1109215 : Blo 1108626 1109215 := bstep (se 1 (by rfl) ⟨831911, by rfl⟩ : syracuseStep 1109215 = 1663823) B1663823
theorem B1666271 : Blo 1108626 1666271 := bstep (se 1 (by rfl) ⟨1249703, by rfl⟩ : syracuseStep 1666271 = 2499407) B2499407
theorem B7105769 : Blo 1108626 7105769 := bstep (se 2 (by rfl) ⟨2664663, by rfl⟩ : syracuseStep 7105769 = 5329327) B5329327
theorem B1666313 : Blo 1108626 1666313 := bstep (se 2 (by rfl) ⟨624867, by rfl⟩ : syracuseStep 1666313 = 1249735) B1249735
theorem B1666415 : Blo 1108626 1666415 := bstep (se 1 (by rfl) ⟨1249811, by rfl⟩ : syracuseStep 1666415 = 2499623) B2499623
theorem B1109479 : Blo 1108626 1109479 := bstep (se 1 (by rfl) ⟨832109, by rfl⟩ : syracuseStep 1109479 = 1664219) B1664219
theorem B1666535 : Blo 1108626 1666535 := bstep (se 1 (by rfl) ⟨1249901, by rfl⟩ : syracuseStep 1666535 = 2499803) B2499803
theorem B1109595 : Blo 1108626 1109595 := bstep (se 1 (by rfl) ⟨832196, by rfl⟩ : syracuseStep 1109595 = 1664393) B1664393
theorem B1666667 : Blo 1108626 1666667 := bstep (se 1 (by rfl) ⟨1250000, by rfl⟩ : syracuseStep 1666667 = 2500001) B2500001
theorem B14216867 : Blo 1108626 14216867 := bstep (se 1 (by rfl) ⟨10662650, by rfl⟩ : syracuseStep 14216867 = 21325301) B21325301
theorem B1666793 : Blo 1108626 1666793 := bstep (se 2 (by rfl) ⟨625047, by rfl⟩ : syracuseStep 1666793 = 1250095) B1250095
theorem B1109831 : Blo 1108626 1109831 := bstep (se 1 (by rfl) ⟨832373, by rfl⟩ : syracuseStep 1109831 = 1664747) B1664747
theorem B1666937 : Blo 1108626 1666937 := bstep (se 2 (by rfl) ⟨625101, by rfl⟩ : syracuseStep 1666937 = 1250203) B1250203
theorem B1109983 : Blo 1108626 1109983 := bstep (se 1 (by rfl) ⟨832487, by rfl⟩ : syracuseStep 1109983 = 1664975) B1664975
theorem B1667039 : Blo 1108626 1667039 := bstep (se 1 (by rfl) ⟨1250279, by rfl⟩ : syracuseStep 1667039 = 2500559) B2500559
theorem B6320339 : Blo 1108626 6320339 := bstep (se 1 (by rfl) ⟨4740254, by rfl⟩ : syracuseStep 6320339 = 9480509) B9480509
theorem B1667291 : Blo 1108626 1667291 := bstep (se 1 (by rfl) ⟨1250468, by rfl⟩ : syracuseStep 1667291 = 2500937) B2500937
theorem B1110247 : Blo 1108626 1110247 := bstep (se 1 (by rfl) ⟨832685, by rfl⟩ : syracuseStep 1110247 = 1665371) B1665371
theorem B1667303 : Blo 1108626 1667303 := bstep (se 1 (by rfl) ⟨1250477, by rfl⟩ : syracuseStep 1667303 = 2500955) B2500955
theorem B1110399 : Blo 1108626 1110399 := bstep (se 1 (by rfl) ⟨832799, by rfl⟩ : syracuseStep 1110399 = 1665599) B1665599
theorem B2814335 : Blo 1108626 2814335 := bstep (se 1 (by rfl) ⟨2110751, by rfl⟩ : syracuseStep 2814335 = 4221503) B4221503
theorem B1667465 : Blo 1108626 1667465 := bstep (se 2 (by rfl) ⟨625299, by rfl⟩ : syracuseStep 1667465 = 1250599) B1250599
theorem B1110479 : Blo 1108626 1110479 := bstep (se 1 (by rfl) ⟨832859, by rfl⟩ : syracuseStep 1110479 = 1665719) B1665719
theorem B1667561 : Blo 1108626 1667561 := bstep (se 2 (by rfl) ⟨625335, by rfl⟩ : syracuseStep 1667561 = 1250671) B1250671
theorem B7991891 : Blo 1108626 7991891 := bstep (se 1 (by rfl) ⟨5993918, by rfl⟩ : syracuseStep 7991891 = 11987837) B11987837
theorem B2814547 : Blo 1108626 2814547 := bstep (se 1 (by rfl) ⟨2110910, by rfl⟩ : syracuseStep 2814547 = 4221821) B4221821
theorem B1110631 : Blo 1108626 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B1667687 : Blo 1108626 1667687 := bstep (se 1 (by rfl) ⟨1250765, by rfl⟩ : syracuseStep 1667687 = 2501531) B2501531
theorem B1667819 : Blo 1108626 1667819 := bstep (se 1 (by rfl) ⟨1250864, by rfl⟩ : syracuseStep 1667819 = 2501729) B2501729
theorem B4223735 : Blo 1108626 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B1667849 : Blo 1108626 1667849 := bstep (se 2 (by rfl) ⟨625443, by rfl⟩ : syracuseStep 1667849 = 1250887) B1250887
theorem B1110895 : Blo 1108626 1110895 := bstep (se 1 (by rfl) ⟨833171, by rfl⟩ : syracuseStep 1110895 = 1666343) B1666343
theorem B1667951 : Blo 1108626 1667951 := bstep (se 1 (by rfl) ⟨1250963, by rfl⟩ : syracuseStep 1667951 = 2501927) B2501927
theorem B1110951 : Blo 1108626 1110951 := bstep (se 1 (by rfl) ⟨833213, by rfl⟩ : syracuseStep 1110951 = 1666427) B1666427
theorem B1111035 : Blo 1108626 1111035 := bstep (se 1 (by rfl) ⟨833276, by rfl⟩ : syracuseStep 1111035 = 1666553) B1666553
theorem B1111103 : Blo 1108626 1111103 := bstep (se 1 (by rfl) ⟨833327, by rfl⟩ : syracuseStep 1111103 = 1666655) B1666655
theorem B3044459 : Blo 1108626 3044459 := bstep (se 1 (by rfl) ⟨2283344, by rfl⟩ : syracuseStep 3044459 = 4566689) B4566689
theorem B1668203 : Blo 1108626 1668203 := bstep (se 1 (by rfl) ⟨1251152, by rfl⟩ : syracuseStep 1668203 = 2502305) B2502305
theorem B1111247 : Blo 1108626 1111247 := bstep (se 1 (by rfl) ⟨833435, by rfl⟩ : syracuseStep 1111247 = 1666871) B1666871
theorem B1668443 : Blo 1108626 1668443 := bstep (se 1 (by rfl) ⟨1251332, by rfl⟩ : syracuseStep 1668443 = 2502665) B2502665
theorem B1111451 : Blo 1108626 1111451 := bstep (se 1 (by rfl) ⟨833588, by rfl⟩ : syracuseStep 1111451 = 1667177) B1667177
theorem B1406575 : Blo 1108626 1406575 := bstep (se 1 (by rfl) ⟨1054931, by rfl⟩ : syracuseStep 1406575 = 2109863) B2109863
theorem B1111663 : Blo 1108626 1111663 := bstep (se 1 (by rfl) ⟨833747, by rfl⟩ : syracuseStep 1111663 = 1667495) B1667495
theorem B1668719 : Blo 1108626 1668719 := bstep (se 1 (by rfl) ⟨1251539, by rfl⟩ : syracuseStep 1668719 = 2503079) B2503079
theorem B1111719 : Blo 1108626 1111719 := bstep (se 1 (by rfl) ⟨833789, by rfl⟩ : syracuseStep 1111719 = 1667579) B1667579
theorem B1668791 : Blo 1108626 1668791 := bstep (se 1 (by rfl) ⟨1251593, by rfl⟩ : syracuseStep 1668791 = 2503187) B2503187
theorem B1668827 : Blo 1108626 1668827 := bstep (se 1 (by rfl) ⟨1251620, by rfl⟩ : syracuseStep 1668827 = 2503241) B2503241
theorem B1111803 : Blo 1108626 1111803 := bstep (se 1 (by rfl) ⟨833852, by rfl⟩ : syracuseStep 1111803 = 1667705) B1667705
theorem B1111839 : Blo 1108626 1111839 := bstep (se 1 (by rfl) ⟨833879, by rfl⟩ : syracuseStep 1111839 = 1667759) B1667759
theorem B1111871 : Blo 1108626 1111871 := bstep (se 1 (by rfl) ⟨833903, by rfl⟩ : syracuseStep 1111871 = 1667807) B1667807
theorem B1112047 : Blo 1108626 1112047 := bstep (se 1 (by rfl) ⟨834035, by rfl⟩ : syracuseStep 1112047 = 1668071) B1668071
theorem B1407071 : Blo 1108626 1407071 := bstep (se 1 (by rfl) ⟨1055303, by rfl⟩ : syracuseStep 1407071 = 2110607) B2110607
theorem B1112219 : Blo 1108626 1112219 := bstep (se 1 (by rfl) ⟨834164, by rfl⟩ : syracuseStep 1112219 = 1668329) B1668329
theorem B1112255 : Blo 1108626 1112255 := bstep (se 1 (by rfl) ⟨834191, by rfl⟩ : syracuseStep 1112255 = 1668383) B1668383
theorem B1112367 : Blo 1108626 1112367 := bstep (se 1 (by rfl) ⟨834275, by rfl⟩ : syracuseStep 1112367 = 1668551) B1668551
theorem B1112603 : Blo 1108626 1112603 := bstep (se 1 (by rfl) ⟨834452, by rfl⟩ : syracuseStep 1112603 = 1668905) B1668905
theorem B1112607 : Blo 1108626 1112607 := bstep (se 1 (by rfl) ⟨834455, by rfl⟩ : syracuseStep 1112607 = 1668911) B1668911
theorem B13531859 : Blo 1108626 13531859 := bstep (se 1 (by rfl) ⟨10148894, by rfl⟩ : syracuseStep 13531859 = 20297789) B20297789
theorem B28474739 : Blo 1108626 28474739 := bstep (se 1 (by rfl) ⟨21356054, by rfl⟩ : syracuseStep 28474739 = 42712109) B42712109
theorem B4752215 : Blo 1108626 4752215 := bstep (se 1 (by rfl) ⟨3564161, by rfl⟩ : syracuseStep 4752215 = 7128323) B7128323
theorem B60687305 : Blo 1108626 60687305 := bstep (se 2 (by rfl) ⟨22757739, by rfl⟩ : syracuseStep 60687305 = 45515479) B45515479
theorem B42633377 : Blo 1108626 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B5343515 : Blo 1108626 5343515 := bstep (se 1 (by rfl) ⟨4007636, by rfl⟩ : syracuseStep 5343515 = 8015273) B8015273
theorem B4557313 : Blo 1108626 4557313 := bstep (se 2 (by rfl) ⟨1708992, by rfl⟩ : syracuseStep 4557313 = 3417985) B3417985
theorem B1247791 : Blo 1108626 1247791 := bstep (se 1 (by rfl) ⟨935843, by rfl⟩ : syracuseStep 1247791 = 1871687) B1871687
theorem B9472787 : Blo 1108626 9472787 := bstep (se 1 (by rfl) ⟨7104590, by rfl⟩ : syracuseStep 9472787 = 14209181) B14209181
theorem B1248223 : Blo 1108626 1248223 := bstep (se 1 (by rfl) ⟨936167, by rfl⟩ : syracuseStep 1248223 = 1872335) B1872335
theorem B1870843 : Blo 1108626 1870843 := bstep (se 1 (by rfl) ⟨1403132, by rfl⟩ : syracuseStep 1870843 = 2806265) B2806265
theorem B2165815 : Blo 1108626 2165815 := bstep (se 1 (by rfl) ⟨1624361, by rfl⟩ : syracuseStep 2165815 = 3248723) B3248723
theorem B13503871 : Blo 1108626 13503871 := bstep (se 1 (by rfl) ⟨10127903, by rfl⟩ : syracuseStep 13503871 = 20255807) B20255807
theorem B6327881 : Blo 1108626 6327881 := bstep (se 2 (by rfl) ⟨2372955, by rfl⟩ : syracuseStep 6327881 = 4745911) B4745911
theorem B1248871 : Blo 1108626 1248871 := bstep (se 1 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 1248871 = 1873307) B1873307
theorem B54857411 : Blo 1108626 54857411 := bstep (se 1 (by rfl) ⟨41143058, by rfl⟩ : syracuseStep 54857411 = 82286117) B82286117
theorem B1249087 : Blo 1108626 1249087 := bstep (se 1 (by rfl) ⟨936815, by rfl⟩ : syracuseStep 1249087 = 1873631) B1873631
theorem B2494439 : Blo 1108626 2494439 := bstep (se 1 (by rfl) ⟨1870829, by rfl⟩ : syracuseStep 2494439 = 3741659) B3741659
theorem B12161087 : Blo 1108626 12161087 := bstep (se 1 (by rfl) ⟨9120815, by rfl⟩ : syracuseStep 12161087 = 18241631) B18241631
theorem B1249375 : Blo 1108626 1249375 := bstep (se 1 (by rfl) ⟨937031, by rfl⟩ : syracuseStep 1249375 = 1874063) B1874063
theorem B2494619 : Blo 1108626 2494619 := bstep (se 1 (by rfl) ⟨1870964, by rfl⟩ : syracuseStep 2494619 = 3741929) B3741929
theorem B2003105 : Blo 1108626 2003105 := bstep (se 2 (by rfl) ⟨751164, by rfl⟩ : syracuseStep 2003105 = 1502329) B1502329
theorem B6328631 : Blo 1108626 6328631 := bstep (se 1 (by rfl) ⟨4746473, by rfl⟩ : syracuseStep 6328631 = 9492947) B9492947
theorem B2494817 : Blo 1108626 2494817 := bstep (se 2 (by rfl) ⟨935556, by rfl⟩ : syracuseStep 2494817 = 1871113) B1871113
theorem B2494907 : Blo 1108626 2494907 := bstep (se 1 (by rfl) ⟨1871180, by rfl⟩ : syracuseStep 2494907 = 3742361) B3742361
theorem B2496167 : Blo 1108626 2496167 := bstep (se 1 (by rfl) ⟨1872125, by rfl⟩ : syracuseStep 2496167 = 3744251) B3744251
theorem B10131115 : Blo 1108626 10131115 := bstep (se 1 (by rfl) ⟨7598336, by rfl⟩ : syracuseStep 10131115 = 15196673) B15196673
theorem B2496347 : Blo 1108626 2496347 := bstep (se 1 (by rfl) ⟨1872260, by rfl⟩ : syracuseStep 2496347 = 3744521) B3744521
theorem B6330271 : Blo 1108626 6330271 := bstep (se 1 (by rfl) ⟨4747703, by rfl⟩ : syracuseStep 6330271 = 9495407) B9495407
theorem B3741821 : Blo 1108626 3741821 := bstep (se 3 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 3741821 = 1403183) B1403183
theorem B3741983 : Blo 1108626 3741983 := bstep (se 1 (by rfl) ⟨2806487, by rfl⟩ : syracuseStep 3741983 = 5612975) B5612975
theorem B2496851 : Blo 1108626 2496851 := bstep (se 1 (by rfl) ⟨1872638, by rfl⟩ : syracuseStep 2496851 = 3745277) B3745277
theorem B3742091 : Blo 1108626 3742091 := bstep (se 1 (by rfl) ⟨2806568, by rfl⟩ : syracuseStep 3742091 = 5613137) B5613137
theorem B1874407 : Blo 1108626 1874407 := bstep (se 1 (by rfl) ⟨1405805, by rfl⟩ : syracuseStep 1874407 = 2811611) B2811611
theorem B2497337 : Blo 1108626 2497337 := bstep (se 2 (by rfl) ⟨936501, by rfl⟩ : syracuseStep 2497337 = 1873003) B1873003
theorem B10132283 : Blo 1108626 10132283 := bstep (se 1 (by rfl) ⟨7599212, by rfl⟩ : syracuseStep 10132283 = 15198425) B15198425
theorem B2497391 : Blo 1108626 2497391 := bstep (se 1 (by rfl) ⟨1873043, by rfl⟩ : syracuseStep 2497391 = 3746087) B3746087
theorem B3382393 : Blo 1108626 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B1580239 : Blo 1108626 1580239 := bstep (se 1 (by rfl) ⟨1185179, by rfl⟩ : syracuseStep 1580239 = 2370359) B2370359
theorem B4005071 : Blo 1108626 4005071 := bstep (se 1 (by rfl) ⟨3003803, by rfl⟩ : syracuseStep 4005071 = 6007607) B6007607
theorem B1875271 : Blo 1108626 1875271 := bstep (se 1 (by rfl) ⟨1406453, by rfl⟩ : syracuseStep 1875271 = 2812907) B2812907
theorem B2497967 : Blo 1108626 2497967 := bstep (se 1 (by rfl) ⟨1873475, by rfl⟩ : syracuseStep 2497967 = 3746951) B3746951
theorem B1875433 : Blo 1108626 1875433 := bstep (se 2 (by rfl) ⟨703287, by rfl⟩ : syracuseStep 1875433 = 1406575) B1406575
theorem B2498039 : Blo 1108626 2498039 := bstep (se 1 (by rfl) ⟨1873529, by rfl⟩ : syracuseStep 2498039 = 3747059) B3747059
theorem B18030073 : Blo 1108626 18030073 := bstep (se 2 (by rfl) ⟨6761277, by rfl⟩ : syracuseStep 18030073 = 13522555) B13522555
theorem B32448235 : Blo 1108626 32448235 := bstep (se 1 (by rfl) ⟨24336176, by rfl⟩ : syracuseStep 32448235 = 48672353) B48672353
theorem B9477911 : Blo 1108626 9477911 := bstep (se 1 (by rfl) ⟨7108433, by rfl⟩ : syracuseStep 9477911 = 14216867) B14216867
theorem B2105185 : Blo 1108626 2105185 := bstep (se 2 (by rfl) ⟨789444, by rfl⟩ : syracuseStep 2105185 = 1578889) B1578889
theorem B3743711 : Blo 1108626 3743711 := bstep (se 1 (by rfl) ⟨2807783, by rfl⟩ : syracuseStep 3743711 = 5615567) B5615567
theorem B3743873 : Blo 1108626 3743873 := bstep (se 2 (by rfl) ⟨1403952, by rfl⟩ : syracuseStep 3743873 = 2807905) B2807905
theorem B1876223 : Blo 1108626 1876223 := bstep (se 1 (by rfl) ⟨1407167, by rfl⟩ : syracuseStep 1876223 = 2814335) B2814335
theorem B12656897 : Blo 1108626 12656897 := bstep (se 2 (by rfl) ⟨4746336, by rfl⟩ : syracuseStep 12656897 = 9492673) B9492673
theorem B13705481 : Blo 1108626 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B2499065 : Blo 1108626 2499065 := bstep (se 2 (by rfl) ⟨937149, by rfl⟩ : syracuseStep 2499065 = 1874299) B1874299
theorem B2499155 : Blo 1108626 2499155 := bstep (se 1 (by rfl) ⟨1874366, by rfl⟩ : syracuseStep 2499155 = 3748733) B3748733
theorem B51258109 : Blo 1108626 51258109 := bstep (se 3 (by rfl) ⟨9610895, by rfl⟩ : syracuseStep 51258109 = 19221791) B19221791
theorem B2499335 : Blo 1108626 2499335 := bstep (se 1 (by rfl) ⟨1874501, by rfl⟩ : syracuseStep 2499335 = 3749003) B3749003
theorem B19473185 : Blo 1108626 19473185 := bstep (se 2 (by rfl) ⟨7302444, by rfl⟩ : syracuseStep 19473185 = 14604889) B14604889
theorem B2499425 : Blo 1108626 2499425 := bstep (se 2 (by rfl) ⟨937284, by rfl⟩ : syracuseStep 2499425 = 1874569) B1874569
theorem B25633691 : Blo 1108626 25633691 := bstep (se 1 (by rfl) ⟨19225268, by rfl⟩ : syracuseStep 25633691 = 38450537) B38450537
theorem B3744683 : Blo 1108626 3744683 := bstep (se 1 (by rfl) ⟨2808512, by rfl⟩ : syracuseStep 3744683 = 5617025) B5617025
theorem B2106415 : Blo 1108626 2106415 := bstep (se 1 (by rfl) ⟨1579811, by rfl⟩ : syracuseStep 2106415 = 3159623) B3159623
theorem B2106643 : Blo 1108626 2106643 := bstep (se 1 (by rfl) ⟨1579982, by rfl⟩ : syracuseStep 2106643 = 3159965) B3159965
theorem B3745223 : Blo 1108626 3745223 := bstep (se 1 (by rfl) ⟨2808917, by rfl⟩ : syracuseStep 3745223 = 5617835) B5617835
theorem B9021239 : Blo 1108626 9021239 := bstep (se 1 (by rfl) ⟨6765929, by rfl⟩ : syracuseStep 9021239 = 13531859) B13531859
theorem B2500415 : Blo 1108626 2500415 := bstep (se 1 (by rfl) ⟨1875311, by rfl⟩ : syracuseStep 2500415 = 3750623) B3750623
theorem B18983159 : Blo 1108626 18983159 := bstep (se 1 (by rfl) ⟨14237369, by rfl⟩ : syracuseStep 18983159 = 28474739) B28474739
theorem B2500919 : Blo 1108626 2500919 := bstep (se 1 (by rfl) ⟨1875689, by rfl⟩ : syracuseStep 2500919 = 3751379) B3751379
theorem B2501099 : Blo 1108626 2501099 := bstep (se 1 (by rfl) ⟨1875824, by rfl⟩ : syracuseStep 2501099 = 3751649) B3751649
theorem B27405047 : Blo 1108626 27405047 := bstep (se 1 (by rfl) ⟨20553785, by rfl⟩ : syracuseStep 27405047 = 41107571) B41107571
theorem B5778383 : Blo 1108626 5778383 := bstep (se 1 (by rfl) ⟨4333787, by rfl⟩ : syracuseStep 5778383 = 8667575) B8667575
theorem B12659813 : Blo 1108626 12659813 := bstep (se 4 (by rfl) ⟨1186857, by rfl⟩ : syracuseStep 12659813 = 2373715) B2373715
theorem B2501801 : Blo 1108626 2501801 := bstep (se 2 (by rfl) ⟨938175, by rfl⟩ : syracuseStep 2501801 = 1876351) B1876351
theorem B3747329 : Blo 1108626 3747329 := bstep (se 2 (by rfl) ⟨1405248, by rfl⟩ : syracuseStep 3747329 = 2810497) B2810497
theorem B2502215 : Blo 1108626 2502215 := bstep (se 1 (by rfl) ⟨1876661, by rfl⟩ : syracuseStep 2502215 = 3753323) B3753323
theorem B2502287 : Blo 1108626 2502287 := bstep (se 1 (by rfl) ⟨1876715, by rfl⟩ : syracuseStep 2502287 = 3753431) B3753431
theorem B2502377 : Blo 1108626 2502377 := bstep (se 2 (by rfl) ⟨938391, by rfl⟩ : syracuseStep 2502377 = 1876783) B1876783
theorem B2109179 : Blo 1108626 2109179 := bstep (se 1 (by rfl) ⟨1581884, by rfl⟩ : syracuseStep 2109179 = 3163769) B3163769
theorem B2502395 : Blo 1108626 2502395 := bstep (se 1 (by rfl) ⟨1876796, by rfl⟩ : syracuseStep 2502395 = 3753593) B3753593
theorem B365277113 : Blo 1108626 365277113 := bstep (se 2 (by rfl) ⟨136978917, by rfl⟩ : syracuseStep 365277113 = 273957835) B273957835
theorem B1519609 : Blo 1108626 1519609 := bstep (se 2 (by rfl) ⟨569853, by rfl⟩ : syracuseStep 1519609 = 1139707) B1139707
theorem B3158291 : Blo 1108626 3158291 := bstep (se 1 (by rfl) ⟨2368718, by rfl⟩ : syracuseStep 3158291 = 4737437) B4737437
theorem B3748139 : Blo 1108626 3748139 := bstep (se 1 (by rfl) ⟨2811104, by rfl⟩ : syracuseStep 3748139 = 5622209) B5622209
theorem B3748409 : Blo 1108626 3748409 := bstep (se 2 (by rfl) ⟨1405653, by rfl⟩ : syracuseStep 3748409 = 2811307) B2811307
theorem B5059135 : Blo 1108626 5059135 := bstep (se 1 (by rfl) ⟨3794351, by rfl⟩ : syracuseStep 5059135 = 7588703) B7588703
theorem B2503403 : Blo 1108626 2503403 := bstep (se 1 (by rfl) ⟨1877552, by rfl⟩ : syracuseStep 2503403 = 3755105) B3755105
theorem B2437951 : Blo 1108626 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B3552167 : Blo 1108626 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B6009851 : Blo 1108626 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B5059849 : Blo 1108626 5059849 := bstep (se 2 (by rfl) ⟨1897443, by rfl⟩ : syracuseStep 5059849 = 3794887) B3794887
theorem B10663265 : Blo 1108626 10663265 := bstep (se 2 (by rfl) ⟨3998724, by rfl⟩ : syracuseStep 10663265 = 7997449) B7997449
theorem B8009189 : Blo 1108626 8009189 := bstep (se 4 (by rfl) ⟨750861, by rfl⟩ : syracuseStep 8009189 = 1501723) B1501723
theorem B2668123 : Blo 1108626 2668123 := bstep (se 1 (by rfl) ⟨2001092, by rfl⟩ : syracuseStep 2668123 = 4002185) B4002185
theorem B10827769 : Blo 1108626 10827769 := bstep (se 2 (by rfl) ⟨4060413, by rfl⟩ : syracuseStep 10827769 = 8120827) B8120827
theorem B5617673 : Blo 1108626 5617673 := bstep (se 2 (by rfl) ⟨2106627, by rfl⟩ : syracuseStep 5617673 = 4213255) B4213255
theorem B3553321 : Blo 1108626 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B4503691 : Blo 1108626 4503691 := bstep (se 1 (by rfl) ⟨3377768, by rfl⟩ : syracuseStep 4503691 = 6755537) B6755537
theorem B3750137 : Blo 1108626 3750137 := bstep (se 2 (by rfl) ⟨1406301, by rfl⟩ : syracuseStep 3750137 = 2812603) B2812603
theorem B6764957 : Blo 1108626 6764957 := bstep (se 3 (by rfl) ⟨1268429, by rfl⟩ : syracuseStep 6764957 = 2536859) B2536859
theorem B3750407 : Blo 1108626 3750407 := bstep (se 1 (by rfl) ⟨2812805, by rfl⟩ : syracuseStep 3750407 = 5625611) B5625611
theorem B3161423 : Blo 1108626 3161423 := bstep (se 1 (by rfl) ⟨2371067, by rfl⟩ : syracuseStep 3161423 = 4742135) B4742135
theorem B3161663 : Blo 1108626 3161663 := bstep (se 1 (by rfl) ⟨2371247, by rfl⟩ : syracuseStep 3161663 = 4742495) B4742495
theorem B3751487 : Blo 1108626 3751487 := bstep (se 1 (by rfl) ⟨2813615, by rfl⟩ : syracuseStep 3751487 = 5627231) B5627231
theorem B3554923 : Blo 1108626 3554923 := bstep (se 1 (by rfl) ⟨2666192, by rfl⟩ : syracuseStep 3554923 = 5332385) B5332385
theorem B4210643 : Blo 1108626 4210643 := bstep (se 1 (by rfl) ⟨3157982, by rfl⟩ : syracuseStep 4210643 = 6315965) B6315965
theorem B3752189 : Blo 1108626 3752189 := bstep (se 3 (by rfl) ⟨703535, by rfl⟩ : syracuseStep 3752189 = 1407071) B1407071
theorem B14434735 : Blo 1108626 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B7225787 : Blo 1108626 7225787 := bstep (se 1 (by rfl) ⟨5419340, by rfl⟩ : syracuseStep 7225787 = 10838681) B10838681
theorem B2671199 : Blo 1108626 2671199 := bstep (se 1 (by rfl) ⟨2003399, by rfl⟩ : syracuseStep 2671199 = 4006799) B4006799
theorem B4735675 : Blo 1108626 4735675 := bstep (se 1 (by rfl) ⟨3551756, by rfl⟩ : syracuseStep 4735675 = 7103513) B7103513
theorem B3752729 : Blo 1108626 3752729 := bstep (se 2 (by rfl) ⟨1407273, by rfl⟩ : syracuseStep 3752729 = 2814547) B2814547
theorem B4211585 : Blo 1108626 4211585 := bstep (se 2 (by rfl) ⟨1579344, by rfl⟩ : syracuseStep 4211585 = 3158689) B3158689
theorem B3752999 : Blo 1108626 3752999 := bstep (se 1 (by rfl) ⟨2814749, by rfl⟩ : syracuseStep 3752999 = 5629499) B5629499
theorem B5063735 : Blo 1108626 5063735 := bstep (se 1 (by rfl) ⟨3797801, by rfl⟩ : syracuseStep 5063735 = 7595603) B7595603
theorem B4277423 : Blo 1108626 4277423 := bstep (se 1 (by rfl) ⟨3208067, by rfl⟩ : syracuseStep 4277423 = 6416135) B6416135
theorem B2704607 : Blo 1108626 2704607 := bstep (se 1 (by rfl) ⟨2028455, by rfl⟩ : syracuseStep 2704607 = 4056911) B4056911
theorem B7128425 : Blo 1108626 7128425 := bstep (se 2 (by rfl) ⟨2673159, by rfl⟩ : syracuseStep 7128425 = 5346319) B5346319
theorem B7587391 : Blo 1108626 7587391 := bstep (se 1 (by rfl) ⟨5690543, by rfl⟩ : syracuseStep 7587391 = 11381087) B11381087
theorem B187582067 : Blo 1108626 187582067 := bstep (se 1 (by rfl) ⟨140686550, by rfl⟩ : syracuseStep 187582067 = 281373101) B281373101
theorem B55428907 : Blo 1108626 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B3754079 : Blo 1108626 3754079 := bstep (se 1 (by rfl) ⟨2815559, by rfl⟩ : syracuseStep 3754079 = 5631119) B5631119
theorem B4737179 : Blo 1108626 4737179 := bstep (se 1 (by rfl) ⟨3552884, by rfl⟩ : syracuseStep 4737179 = 7105769) B7105769
theorem B16009433 : Blo 1108626 16009433 := bstep (se 2 (by rfl) ⟨6003537, by rfl⟩ : syracuseStep 16009433 = 12007075) B12007075
theorem B4213529 : Blo 1108626 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B4213559 : Blo 1108626 4213559 := bstep (se 1 (by rfl) ⟨3160169, by rfl⟩ : syracuseStep 4213559 = 6320339) B6320339
theorem B4213741 : Blo 1108626 4213741 := bstep (se 3 (by rfl) ⟨790076, by rfl⟩ : syracuseStep 4213741 = 1580153) B1580153
theorem B5327927 : Blo 1108626 5327927 := bstep (se 1 (by rfl) ⟨3995945, by rfl⟩ : syracuseStep 5327927 = 7991891) B7991891
theorem B2740319 : Blo 1108626 2740319 := bstep (se 1 (by rfl) ⟨2055239, by rfl⟩ : syracuseStep 2740319 = 4110479) B4110479
theorem B4216171 : Blo 1108626 4216171 := bstep (se 1 (by rfl) ⟨3162128, by rfl⟩ : syracuseStep 4216171 = 6324257) B6324257
theorem B42751475 : Blo 1108626 42751475 := bstep (se 1 (by rfl) ⟨32063606, by rfl⟩ : syracuseStep 42751475 = 64127213) B64127213
theorem B5330711 : Blo 1108626 5330711 := bstep (se 1 (by rfl) ⟨3998033, by rfl⟩ : syracuseStep 5330711 = 7996067) B7996067
theorem B4741537 : Blo 1108626 4741537 := bstep (se 2 (by rfl) ⟨1778076, by rfl⟩ : syracuseStep 4741537 = 3556153) B3556153
theorem B18996281 : Blo 1108626 18996281 := bstep (se 2 (by rfl) ⟨7123605, by rfl⟩ : syracuseStep 18996281 = 14247211) B14247211
theorem B8445707 : Blo 1108626 8445707 := bstep (se 1 (by rfl) ⟨6334280, by rfl⟩ : syracuseStep 8445707 = 12668561) B12668561
theorem B1662953 : Blo 1108626 1662953 := bstep (se 2 (by rfl) ⟨623607, by rfl⟩ : syracuseStep 1662953 = 1247215) B1247215
theorem B15196355 : Blo 1108626 15196355 := bstep (se 1 (by rfl) ⟨11397266, by rfl⟩ : syracuseStep 15196355 = 22794533) B22794533
theorem B4809017 : Blo 1108626 4809017 := bstep (se 2 (by rfl) ⟨1803381, by rfl⟩ : syracuseStep 4809017 = 3606763) B3606763
theorem B3007003 : Blo 1108626 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B5333633 : Blo 1108626 5333633 := bstep (se 2 (by rfl) ⟨2000112, by rfl⟩ : syracuseStep 5333633 = 4000225) B4000225
theorem B4743809 : Blo 1108626 4743809 := bstep (se 2 (by rfl) ⟨1778928, by rfl⟩ : syracuseStep 4743809 = 3557857) B3557857
theorem B1663655 : Blo 1108626 1663655 := bstep (se 1 (by rfl) ⟨1247741, by rfl⟩ : syracuseStep 1663655 = 2495483) B2495483
theorem B4219559 : Blo 1108626 4219559 := bstep (se 1 (by rfl) ⟨3164669, by rfl⟩ : syracuseStep 4219559 = 6329339) B6329339
theorem B10674953 : Blo 1108626 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B1663775 : Blo 1108626 1663775 := bstep (se 1 (by rfl) ⟨1247831, by rfl⟩ : syracuseStep 1663775 = 2495663) B2495663
theorem B1663799 : Blo 1108626 1663799 := bstep (se 1 (by rfl) ⟨1247849, by rfl⟩ : syracuseStep 1663799 = 2495699) B2495699
theorem B1663979 : Blo 1108626 1663979 := bstep (se 1 (by rfl) ⟨1247984, by rfl⟩ : syracuseStep 1663979 = 2495969) B2495969
theorem B8447165 : Blo 1108626 8447165 := bstep (se 3 (by rfl) ⟨1583843, by rfl⟩ : syracuseStep 8447165 = 3167687) B3167687
theorem B27387193 : Blo 1108626 27387193 := bstep (se 2 (by rfl) ⟨10270197, by rfl⟩ : syracuseStep 27387193 = 20540395) B20540395
theorem B5334443 : Blo 1108626 5334443 := bstep (se 1 (by rfl) ⟨4000832, by rfl⟩ : syracuseStep 5334443 = 8001665) B8001665
theorem B2811419 : Blo 1108626 2811419 := bstep (se 1 (by rfl) ⟨2108564, by rfl⟩ : syracuseStep 2811419 = 4217129) B4217129
theorem B1665071 : Blo 1108626 1665071 := bstep (se 1 (by rfl) ⟨1248803, by rfl⟩ : syracuseStep 1665071 = 2497607) B2497607
theorem B71985347 : Blo 1108626 71985347 := bstep (se 1 (by rfl) ⟨53989010, by rfl⟩ : syracuseStep 71985347 = 107978021) B107978021
theorem B1665335 : Blo 1108626 1665335 := bstep (se 1 (by rfl) ⟨1249001, by rfl⟩ : syracuseStep 1665335 = 2498003) B2498003
theorem B1665515 : Blo 1108626 1665515 := bstep (se 1 (by rfl) ⟨1249136, by rfl⟩ : syracuseStep 1665515 = 2498273) B2498273
theorem B4745927 : Blo 1108626 4745927 := bstep (se 1 (by rfl) ⟨3559445, by rfl⟩ : syracuseStep 4745927 = 7118891) B7118891
theorem B1108959 : Blo 1108626 1108959 := bstep (se 1 (by rfl) ⟨831719, by rfl⟩ : syracuseStep 1108959 = 1663439) B1663439
theorem B1108987 : Blo 1108626 1108987 := bstep (se 1 (by rfl) ⟨831740, by rfl⟩ : syracuseStep 1108987 = 1663481) B1663481
theorem B1109055 : Blo 1108626 1109055 := bstep (se 1 (by rfl) ⟨831791, by rfl⟩ : syracuseStep 1109055 = 1663583) B1663583
theorem B1666217 : Blo 1108626 1666217 := bstep (se 2 (by rfl) ⟨624831, by rfl⟩ : syracuseStep 1666217 = 1249663) B1249663
theorem B6745369 : Blo 1108626 6745369 := bstep (se 2 (by rfl) ⟨2529513, by rfl⟩ : syracuseStep 6745369 = 5059027) B5059027
theorem B1109375 : Blo 1108626 1109375 := bstep (se 1 (by rfl) ⟨832031, by rfl⟩ : syracuseStep 1109375 = 1664063) B1664063
theorem B1109403 : Blo 1108626 1109403 := bstep (se 1 (by rfl) ⟨832052, by rfl⟩ : syracuseStep 1109403 = 1664105) B1664105
theorem B17100197 : Blo 1108626 17100197 := bstep (se 4 (by rfl) ⟨1603143, by rfl⟩ : syracuseStep 17100197 = 3206287) B3206287
theorem B1109471 : Blo 1108626 1109471 := bstep (se 1 (by rfl) ⟨832103, by rfl⟩ : syracuseStep 1109471 = 1664207) B1664207
theorem B1666631 : Blo 1108626 1666631 := bstep (se 1 (by rfl) ⟨1249973, by rfl⟩ : syracuseStep 1666631 = 2499947) B2499947
theorem B1109607 : Blo 1108626 1109607 := bstep (se 1 (by rfl) ⟨832205, by rfl⟩ : syracuseStep 1109607 = 1664411) B1664411
theorem B5074607 : Blo 1108626 5074607 := bstep (se 1 (by rfl) ⟨3805955, by rfl⟩ : syracuseStep 5074607 = 7611911) B7611911
theorem B1109755 : Blo 1108626 1109755 := bstep (se 1 (by rfl) ⟨832316, by rfl⟩ : syracuseStep 1109755 = 1664633) B1664633
theorem B1666811 : Blo 1108626 1666811 := bstep (se 1 (by rfl) ⟨1250108, by rfl⟩ : syracuseStep 1666811 = 2500217) B2500217
theorem B1109823 : Blo 1108626 1109823 := bstep (se 1 (by rfl) ⟨832367, by rfl⟩ : syracuseStep 1109823 = 1664735) B1664735
theorem B1109887 : Blo 1108626 1109887 := bstep (se 1 (by rfl) ⟨832415, by rfl⟩ : syracuseStep 1109887 = 1664831) B1664831
theorem B158232527 : Blo 1108626 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B1109999 : Blo 1108626 1109999 := bstep (se 1 (by rfl) ⟨832499, by rfl⟩ : syracuseStep 1109999 = 1664999) B1664999
theorem B1110011 : Blo 1108626 1110011 := bstep (se 1 (by rfl) ⟨832508, by rfl⟩ : syracuseStep 1110011 = 1665017) B1665017
theorem B1110079 : Blo 1108626 1110079 := bstep (se 1 (by rfl) ⟨832559, by rfl⟩ : syracuseStep 1110079 = 1665119) B1665119
theorem B1110119 : Blo 1108626 1110119 := bstep (se 1 (by rfl) ⟨832589, by rfl⟩ : syracuseStep 1110119 = 1665179) B1665179
theorem B1110143 : Blo 1108626 1110143 := bstep (se 1 (by rfl) ⟨832607, by rfl⟩ : syracuseStep 1110143 = 1665215) B1665215
theorem B10121345 : Blo 1108626 10121345 := bstep (se 2 (by rfl) ⟨3795504, by rfl⟩ : syracuseStep 10121345 = 7591009) B7591009
theorem B1110171 : Blo 1108626 1110171 := bstep (se 1 (by rfl) ⟨832628, by rfl⟩ : syracuseStep 1110171 = 1665257) B1665257
theorem B1110375 : Blo 1108626 1110375 := bstep (se 1 (by rfl) ⟨832781, by rfl⟩ : syracuseStep 1110375 = 1665563) B1665563
theorem B1110427 : Blo 1108626 1110427 := bstep (se 1 (by rfl) ⟨832820, by rfl⟩ : syracuseStep 1110427 = 1665641) B1665641
theorem B1667483 : Blo 1108626 1667483 := bstep (se 1 (by rfl) ⟨1250612, by rfl⟩ : syracuseStep 1667483 = 2501225) B2501225
theorem B6320591 : Blo 1108626 6320591 := bstep (se 1 (by rfl) ⟨4740443, by rfl⟩ : syracuseStep 6320591 = 9480887) B9480887
theorem B4223447 : Blo 1108626 4223447 := bstep (se 1 (by rfl) ⟨3167585, by rfl⟩ : syracuseStep 4223447 = 6335171) B6335171
theorem B1110779 : Blo 1108626 1110779 := bstep (se 1 (by rfl) ⟨833084, by rfl⟩ : syracuseStep 1110779 = 1666169) B1666169
theorem B1110847 : Blo 1108626 1110847 := bstep (se 1 (by rfl) ⟨833135, by rfl⟩ : syracuseStep 1110847 = 1666271) B1666271
theorem B1667903 : Blo 1108626 1667903 := bstep (se 1 (by rfl) ⟨1250927, by rfl⟩ : syracuseStep 1667903 = 2501855) B2501855
theorem B1110875 : Blo 1108626 1110875 := bstep (se 1 (by rfl) ⟨833156, by rfl⟩ : syracuseStep 1110875 = 1666313) B1666313
theorem B1110943 : Blo 1108626 1110943 := bstep (se 1 (by rfl) ⟨833207, by rfl⟩ : syracuseStep 1110943 = 1666415) B1666415
theorem B1668047 : Blo 1108626 1668047 := bstep (se 1 (by rfl) ⟨1251035, by rfl⟩ : syracuseStep 1668047 = 2502071) B2502071
theorem B1111023 : Blo 1108626 1111023 := bstep (se 1 (by rfl) ⟨833267, by rfl⟩ : syracuseStep 1111023 = 1666535) B1666535
theorem B1668089 : Blo 1108626 1668089 := bstep (se 2 (by rfl) ⟨625533, by rfl⟩ : syracuseStep 1668089 = 1251067) B1251067
theorem B1668137 : Blo 1108626 1668137 := bstep (se 2 (by rfl) ⟨625551, by rfl⟩ : syracuseStep 1668137 = 1251103) B1251103
theorem B1111111 : Blo 1108626 1111111 := bstep (se 1 (by rfl) ⟨833333, by rfl⟩ : syracuseStep 1111111 = 1666667) B1666667
theorem B1668167 : Blo 1108626 1668167 := bstep (se 1 (by rfl) ⟨1251125, by rfl⟩ : syracuseStep 1668167 = 2502251) B2502251
theorem B1111195 : Blo 1108626 1111195 := bstep (se 1 (by rfl) ⟨833396, by rfl⟩ : syracuseStep 1111195 = 1666793) B1666793
theorem B1111291 : Blo 1108626 1111291 := bstep (se 1 (by rfl) ⟨833468, by rfl⟩ : syracuseStep 1111291 = 1666937) B1666937
theorem B1668347 : Blo 1108626 1668347 := bstep (se 1 (by rfl) ⟨1251260, by rfl⟩ : syracuseStep 1668347 = 2502521) B2502521
theorem B7107871 : Blo 1108626 7107871 := bstep (se 1 (by rfl) ⟨5330903, by rfl⟩ : syracuseStep 7107871 = 10661807) B10661807
theorem B5338399 : Blo 1108626 5338399 := bstep (se 1 (by rfl) ⟨4003799, by rfl⟩ : syracuseStep 5338399 = 8007599) B8007599
theorem B1111359 : Blo 1108626 1111359 := bstep (se 1 (by rfl) ⟨833519, by rfl⟩ : syracuseStep 1111359 = 1667039) B1667039
theorem B3372455 : Blo 1108626 3372455 := bstep (se 1 (by rfl) ⟨2529341, by rfl⟩ : syracuseStep 3372455 = 5058683) B5058683
theorem B18970037 : Blo 1108626 18970037 := bstep (se 5 (by rfl) ⟨889220, by rfl⟩ : syracuseStep 18970037 = 1778441) B1778441
theorem B1111527 : Blo 1108626 1111527 := bstep (se 1 (by rfl) ⟨833645, by rfl⟩ : syracuseStep 1111527 = 1667291) B1667291
theorem B1111535 : Blo 1108626 1111535 := bstep (se 1 (by rfl) ⟨833651, by rfl⟩ : syracuseStep 1111535 = 1667303) B1667303
theorem B1111643 : Blo 1108626 1111643 := bstep (se 1 (by rfl) ⟨833732, by rfl⟩ : syracuseStep 1111643 = 1667465) B1667465
theorem B1111707 : Blo 1108626 1111707 := bstep (se 1 (by rfl) ⟨833780, by rfl⟩ : syracuseStep 1111707 = 1667561) B1667561
theorem B13530833 : Blo 1108626 13530833 := bstep (se 2 (by rfl) ⟨5074062, by rfl⟩ : syracuseStep 13530833 = 10148125) B10148125
theorem B1111791 : Blo 1108626 1111791 := bstep (se 1 (by rfl) ⟨833843, by rfl⟩ : syracuseStep 1111791 = 1667687) B1667687
theorem B1111879 : Blo 1108626 1111879 := bstep (se 1 (by rfl) ⟨833909, by rfl⟩ : syracuseStep 1111879 = 1667819) B1667819
theorem B2815823 : Blo 1108626 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B1111899 : Blo 1108626 1111899 := bstep (se 1 (by rfl) ⟨833924, by rfl⟩ : syracuseStep 1111899 = 1667849) B1667849
theorem B1111967 : Blo 1108626 1111967 := bstep (se 1 (by rfl) ⟨833975, by rfl⟩ : syracuseStep 1111967 = 1667951) B1667951
theorem B2029639 : Blo 1108626 2029639 := bstep (se 1 (by rfl) ⟨1522229, by rfl⟩ : syracuseStep 2029639 = 3044459) B3044459
theorem B1112135 : Blo 1108626 1112135 := bstep (se 1 (by rfl) ⟨834101, by rfl⟩ : syracuseStep 1112135 = 1668203) B1668203
theorem B5142737 : Blo 1108626 5142737 := bstep (se 2 (by rfl) ⟨1928526, by rfl⟩ : syracuseStep 5142737 = 3857053) B3857053
theorem B1112295 : Blo 1108626 1112295 := bstep (se 1 (by rfl) ⟨834221, by rfl⟩ : syracuseStep 1112295 = 1668443) B1668443
theorem B1112479 : Blo 1108626 1112479 := bstep (se 1 (by rfl) ⟨834359, by rfl⟩ : syracuseStep 1112479 = 1668719) B1668719
theorem B1112527 : Blo 1108626 1112527 := bstep (se 1 (by rfl) ⟨834395, by rfl⟩ : syracuseStep 1112527 = 1668791) B1668791
theorem B1112551 : Blo 1108626 1112551 := bstep (se 1 (by rfl) ⟨834413, by rfl⟩ : syracuseStep 1112551 = 1668827) B1668827
theorem B4750559 : Blo 1108626 4750559 := bstep (se 1 (by rfl) ⟨3562919, by rfl⟩ : syracuseStep 4750559 = 7125839) B7125839
theorem B11992369 : Blo 1108626 11992369 := bstep (se 2 (by rfl) ⟨4497138, by rfl⟩ : syracuseStep 11992369 = 8994277) B8994277
theorem B21331451 : Blo 1108626 21331451 := bstep (se 1 (by rfl) ⟨15998588, by rfl⟩ : syracuseStep 21331451 = 31997177) B31997177
theorem B3375047 : Blo 1108626 3375047 := bstep (se 1 (by rfl) ⟨2531285, by rfl⟩ : syracuseStep 3375047 = 5062571) B5062571
theorem B4817191 : Blo 1108626 4817191 := bstep (se 1 (by rfl) ⟨3612893, by rfl⟩ : syracuseStep 4817191 = 7225787) B7225787
theorem B3375823 : Blo 1108626 3375823 := bstep (se 1 (by rfl) ⟨2531867, by rfl⟩ : syracuseStep 3375823 = 5063735) B5063735
theorem B24019685 : Blo 1108626 24019685 := bstep (se 4 (by rfl) ⟨2251845, by rfl⟩ : syracuseStep 24019685 = 4503691) B4503691
theorem B2851615 : Blo 1108626 2851615 := bstep (se 1 (by rfl) ⟨2138711, by rfl⟩ : syracuseStep 2851615 = 4277423) B4277423
theorem B1803071 : Blo 1108626 1803071 := bstep (se 1 (by rfl) ⟨1352303, by rfl⟩ : syracuseStep 1803071 = 2704607) B2704607
theorem B4752283 : Blo 1108626 4752283 := bstep (se 1 (by rfl) ⟨3564212, by rfl⟩ : syracuseStep 4752283 = 7128425) B7128425
theorem B36571607 : Blo 1108626 36571607 := bstep (se 1 (by rfl) ⟨27428705, by rfl⟩ : syracuseStep 36571607 = 54857411) B54857411
theorem B2494457 : Blo 1108626 2494457 := bstep (se 2 (by rfl) ⟨935421, by rfl⟩ : syracuseStep 2494457 = 1870843) B1870843
theorem B2887753 : Blo 1108626 2887753 := bstep (se 2 (by rfl) ⟨1082907, by rfl⟩ : syracuseStep 2887753 = 2165815) B2165815
theorem B2494547 : Blo 1108626 2494547 := bstep (se 1 (by rfl) ⟨1870910, by rfl⟩ : syracuseStep 2494547 = 3741821) B3741821
theorem B2494655 : Blo 1108626 2494655 := bstep (se 1 (by rfl) ⟨1870991, by rfl⟩ : syracuseStep 2494655 = 3741983) B3741983
theorem B2494727 : Blo 1108626 2494727 := bstep (se 1 (by rfl) ⟨1871045, by rfl⟩ : syracuseStep 2494727 = 3742091) B3742091
theorem B6754855 : Blo 1108626 6754855 := bstep (se 1 (by rfl) ⟨5066141, by rfl⟩ : syracuseStep 6754855 = 10132283) B10132283
theorem B2495807 : Blo 1108626 2495807 := bstep (se 1 (by rfl) ⟨1871855, by rfl⟩ : syracuseStep 2495807 = 3743711) B3743711
theorem B2495915 : Blo 1108626 2495915 := bstep (se 1 (by rfl) ⟨1871936, by rfl⟩ : syracuseStep 2495915 = 3743873) B3743873
theorem B10130903 : Blo 1108626 10130903 := bstep (se 1 (by rfl) ⟨7598177, by rfl⟩ : syracuseStep 10130903 = 15196355) B15196355
theorem B1250815 : Blo 1108626 1250815 := bstep (se 1 (by rfl) ⟨938111, by rfl⟩ : syracuseStep 1250815 = 1876223) B1876223
theorem B7116635 : Blo 1108626 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B12982123 : Blo 1108626 12982123 := bstep (se 1 (by rfl) ⟨9736592, by rfl⟩ : syracuseStep 12982123 = 19473185) B19473185
theorem B2496455 : Blo 1108626 2496455 := bstep (se 1 (by rfl) ⟨1872341, by rfl⟩ : syracuseStep 2496455 = 3744683) B3744683
theorem B2496815 : Blo 1108626 2496815 := bstep (se 1 (by rfl) ⟨1872611, by rfl⟩ : syracuseStep 2496815 = 3745223) B3745223
theorem B1874279 : Blo 1108626 1874279 := bstep (se 1 (by rfl) ⟨1405709, by rfl⟩ : syracuseStep 1874279 = 2811419) B2811419
theorem B3250601 : Blo 1108626 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B12655439 : Blo 1108626 12655439 := bstep (se 1 (by rfl) ⟨9491579, by rfl⟩ : syracuseStep 12655439 = 18983159) B18983159
theorem B9477161 : Blo 1108626 9477161 := bstep (se 2 (by rfl) ⟨3553935, by rfl⟩ : syracuseStep 9477161 = 7107871) B7107871
theorem B7117865 : Blo 1108626 7117865 := bstep (se 2 (by rfl) ⟨2669199, by rfl⟩ : syracuseStep 7117865 = 5338399) B5338399
theorem B13508153 : Blo 1108626 13508153 := bstep (se 2 (by rfl) ⟨5065557, by rfl⟩ : syracuseStep 13508153 = 10131115) B10131115
theorem B2498219 : Blo 1108626 2498219 := bstep (se 1 (by rfl) ⟨1873664, by rfl⟩ : syracuseStep 2498219 = 3747329) B3747329
theorem B105488351 : Blo 1108626 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B2105527 : Blo 1108626 2105527 := bstep (se 1 (by rfl) ⟨1579145, by rfl⟩ : syracuseStep 2105527 = 3158291) B3158291
theorem B2498759 : Blo 1108626 2498759 := bstep (se 1 (by rfl) ⟨1874069, by rfl⟩ : syracuseStep 2498759 = 3748139) B3748139
theorem B2498939 : Blo 1108626 2498939 := bstep (se 1 (by rfl) ⟨1874204, by rfl⟩ : syracuseStep 2498939 = 3748409) B3748409
theorem B14229989 : Blo 1108626 14229989 := bstep (se 4 (by rfl) ⟨1334061, by rfl⟩ : syracuseStep 14229989 = 2668123) B2668123
theorem B2368111 : Blo 1108626 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B2499209 : Blo 1108626 2499209 := bstep (se 2 (by rfl) ⟨937203, by rfl⟩ : syracuseStep 2499209 = 1874407) B1874407
theorem B4006567 : Blo 1108626 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B9020555 : Blo 1108626 9020555 := bstep (se 1 (by rfl) ⟨6765416, by rfl⟩ : syracuseStep 9020555 = 13530833) B13530833
theorem B1877215 : Blo 1108626 1877215 := bstep (se 1 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 1877215 = 2815823) B2815823
theorem B3745115 : Blo 1108626 3745115 := bstep (se 1 (by rfl) ⟨2808836, by rfl⟩ : syracuseStep 3745115 = 5617673) B5617673
theorem B2500091 : Blo 1108626 2500091 := bstep (se 1 (by rfl) ⟨1875068, by rfl⟩ : syracuseStep 2500091 = 3750137) B3750137
theorem B2106985 : Blo 1108626 2106985 := bstep (se 2 (by rfl) ⟨790119, by rfl⟩ : syracuseStep 2106985 = 1580239) B1580239
theorem B2500271 : Blo 1108626 2500271 := bstep (se 1 (by rfl) ⟨1875203, by rfl⟩ : syracuseStep 2500271 = 3750407) B3750407
theorem B2500361 : Blo 1108626 2500361 := bstep (se 2 (by rfl) ⟨937635, by rfl⟩ : syracuseStep 2500361 = 1875271) B1875271
theorem B2500577 : Blo 1108626 2500577 := bstep (se 2 (by rfl) ⟨937716, by rfl⟩ : syracuseStep 2500577 = 1875433) B1875433
theorem B2107615 : Blo 1108626 2107615 := bstep (se 1 (by rfl) ⟨1580711, by rfl⟩ : syracuseStep 2107615 = 3161423) B3161423
theorem B43264313 : Blo 1108626 43264313 := bstep (se 2 (by rfl) ⟨16224117, by rfl⟩ : syracuseStep 43264313 = 32448235) B32448235
theorem B2107775 : Blo 1108626 2107775 := bstep (se 1 (by rfl) ⟨1580831, by rfl⟩ : syracuseStep 2107775 = 3161663) B3161663
theorem B2500991 : Blo 1108626 2500991 := bstep (se 1 (by rfl) ⟨1875743, by rfl⟩ : syracuseStep 2500991 = 3751487) B3751487
theorem B2501459 : Blo 1108626 2501459 := bstep (se 1 (by rfl) ⟨1876094, by rfl⟩ : syracuseStep 2501459 = 3752189) B3752189
theorem B1780799 : Blo 1108626 1780799 := bstep (se 1 (by rfl) ⟨1335599, by rfl⟩ : syracuseStep 1780799 = 2671199) B2671199
theorem B2501819 : Blo 1108626 2501819 := bstep (se 1 (by rfl) ⟨1876364, by rfl⟩ : syracuseStep 2501819 = 3752729) B3752729
theorem B19246313 : Blo 1108626 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B36547949 : Blo 1108626 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B2501999 : Blo 1108626 2501999 := bstep (se 1 (by rfl) ⟨1876499, by rfl⟩ : syracuseStep 2501999 = 3752999) B3752999
theorem B4009337 : Blo 1108626 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B12824045 : Blo 1108626 12824045 := bstep (se 3 (by rfl) ⟨2404508, by rfl⟩ : syracuseStep 12824045 = 4809017) B4809017
theorem B125054711 : Blo 1108626 125054711 := bstep (se 1 (by rfl) ⟨93791033, by rfl⟩ : syracuseStep 125054711 = 187582067) B187582067
theorem B2502719 : Blo 1108626 2502719 := bstep (se 1 (by rfl) ⟨1877039, by rfl⟩ : syracuseStep 2502719 = 3754079) B3754079
theorem B3158119 : Blo 1108626 3158119 := bstep (se 1 (by rfl) ⟨2368589, by rfl⟩ : syracuseStep 3158119 = 4737179) B4737179
theorem B28422251 : Blo 1108626 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B36516257 : Blo 1108626 36516257 := bstep (se 2 (by rfl) ⟨13693596, by rfl⟩ : syracuseStep 36516257 = 27387193) B27387193
theorem B3551951 : Blo 1108626 3551951 := bstep (se 1 (by rfl) ⟨2663963, by rfl⟩ : syracuseStep 3551951 = 5327927) B5327927
theorem B73905209 : Blo 1108626 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B8107391 : Blo 1108626 8107391 := bstep (se 1 (by rfl) ⟨6080543, by rfl⟩ : syracuseStep 8107391 = 12161087) B12161087
theorem B6076417 : Blo 1108626 6076417 := bstep (se 2 (by rfl) ⟨2278656, by rfl⟩ : syracuseStep 6076417 = 4557313) B4557313
theorem B3553807 : Blo 1108626 3553807 := bstep (se 1 (by rfl) ⟨2665355, by rfl⟩ : syracuseStep 3553807 = 5330711) B5330711
theorem B5618321 : Blo 1108626 5618321 := bstep (se 2 (by rfl) ⟨2106870, by rfl⟩ : syracuseStep 5618321 = 4213741) B4213741
theorem B8993825 : Blo 1108626 8993825 := bstep (se 2 (by rfl) ⟨3372684, by rfl⟩ : syracuseStep 8993825 = 6745369) B6745369
theorem B18005161 : Blo 1108626 18005161 := bstep (se 2 (by rfl) ⟨6751935, by rfl⟩ : syracuseStep 18005161 = 13503871) B13503871
theorem B12664187 : Blo 1108626 12664187 := bstep (se 1 (by rfl) ⟨9498140, by rfl⟩ : syracuseStep 12664187 = 18996281) B18996281
theorem B2670047 : Blo 1108626 2670047 := bstep (se 1 (by rfl) ⟨2002535, by rfl⟩ : syracuseStep 2670047 = 4005071) B4005071
theorem B8437931 : Blo 1108626 8437931 := bstep (se 1 (by rfl) ⟨6328448, by rfl⟩ : syracuseStep 8437931 = 12656897) B12656897
theorem B3555755 : Blo 1108626 3555755 := bstep (se 1 (by rfl) ⟨2666816, by rfl⟩ : syracuseStep 3555755 = 5333633) B5333633
theorem B3162539 : Blo 1108626 3162539 := bstep (se 1 (by rfl) ⟨2371904, by rfl⟩ : syracuseStep 3162539 = 4743809) B4743809
theorem B17089127 : Blo 1108626 17089127 := bstep (se 1 (by rfl) ⟨12816845, by rfl⟩ : syracuseStep 17089127 = 25633691) B25633691
theorem B3556295 : Blo 1108626 3556295 := bstep (se 1 (by rfl) ⟨2667221, by rfl⟩ : syracuseStep 3556295 = 5334443) B5334443
theorem B6014159 : Blo 1108626 6014159 := bstep (se 1 (by rfl) ⟨4510619, by rfl⟩ : syracuseStep 6014159 = 9021239) B9021239
theorem B47990231 : Blo 1108626 47990231 := bstep (se 1 (by rfl) ⟨35992673, by rfl⟩ : syracuseStep 47990231 = 71985347) B71985347
theorem B3163951 : Blo 1108626 3163951 := bstep (se 1 (by rfl) ⟨2372963, by rfl⟩ : syracuseStep 3163951 = 4745927) B4745927
theorem B5621561 : Blo 1108626 5621561 := bstep (se 2 (by rfl) ⟨2108085, by rfl⟩ : syracuseStep 5621561 = 4216171) B4216171
theorem B18270031 : Blo 1108626 18270031 := bstep (se 1 (by rfl) ⟨13702523, by rfl⟩ : syracuseStep 18270031 = 27405047) B27405047
theorem B8439875 : Blo 1108626 8439875 := bstep (se 1 (by rfl) ⟨6329906, by rfl⟩ : syracuseStep 8439875 = 12659813) B12659813
theorem B8440361 : Blo 1108626 8440361 := bstep (se 2 (by rfl) ⟨3165135, by rfl⟩ : syracuseStep 8440361 = 6330271) B6330271
theorem B243518075 : Blo 1108626 243518075 := bstep (se 1 (by rfl) ⟨182638556, by rfl⟩ : syracuseStep 243518075 = 365277113) B365277113
theorem B14437025 : Blo 1108626 14437025 := bstep (se 2 (by rfl) ⟨5413884, by rfl⟩ : syracuseStep 14437025 = 10827769) B10827769
theorem B4737761 : Blo 1108626 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B2706185 : Blo 1108626 2706185 := bstep (se 2 (by rfl) ⟨1014819, by rfl⟩ : syracuseStep 2706185 = 2029639) B2029639
theorem B4213727 : Blo 1108626 4213727 := bstep (se 1 (by rfl) ⟨3160295, by rfl⟩ : syracuseStep 4213727 = 6320591) B6320591
theorem B2248303 : Blo 1108626 2248303 := bstep (se 1 (by rfl) ⟨1686227, by rfl⟩ : syracuseStep 2248303 = 3372455) B3372455
theorem B3428491 : Blo 1108626 3428491 := bstep (se 1 (by rfl) ⟨2571368, by rfl⟩ : syracuseStep 3428491 = 5142737) B5142737
theorem B4509857 : Blo 1108626 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B4509971 : Blo 1108626 4509971 := bstep (se 1 (by rfl) ⟨3382478, by rfl⟩ : syracuseStep 4509971 = 6764957) B6764957
theorem B5624477 : Blo 1108626 5624477 := bstep (se 3 (by rfl) ⟨1054589, by rfl⟩ : syracuseStep 5624477 = 2109179) B2109179
theorem B24040097 : Blo 1108626 24040097 := bstep (se 2 (by rfl) ⟨9015036, by rfl⟩ : syracuseStep 24040097 = 18030073) B18030073
theorem B4739897 : Blo 1108626 4739897 := bstep (se 2 (by rfl) ⟨1777461, by rfl⟩ : syracuseStep 4739897 = 3554923) B3554923
theorem B3167039 : Blo 1108626 3167039 := bstep (se 1 (by rfl) ⟨2375279, by rfl⟩ : syracuseStep 3167039 = 4750559) B4750559
theorem B2806913 : Blo 1108626 2806913 := bstep (se 2 (by rfl) ⟨1052592, by rfl⟩ : syracuseStep 2806913 = 2105185) B2105185
theorem B2250031 : Blo 1108626 2250031 := bstep (se 1 (by rfl) ⟨1687523, by rfl⟩ : syracuseStep 2250031 = 3375047) B3375047
theorem B2807095 : Blo 1108626 2807095 := bstep (se 1 (by rfl) ⟨2105321, by rfl⟩ : syracuseStep 2807095 = 4210643) B4210643
theorem B3168143 : Blo 1108626 3168143 := bstep (se 1 (by rfl) ⟨2376107, by rfl⟩ : syracuseStep 3168143 = 4752215) B4752215
theorem B2807723 : Blo 1108626 2807723 := bstep (se 1 (by rfl) ⟨2105792, by rfl⟩ : syracuseStep 2807723 = 4211585) B4211585
theorem B40458203 : Blo 1108626 40458203 := bstep (se 1 (by rfl) ⟨30343652, by rfl⟩ : syracuseStep 40458203 = 60687305) B60687305
theorem B6314233 : Blo 1108626 6314233 := bstep (se 2 (by rfl) ⟨2367837, by rfl⟩ : syracuseStep 6314233 = 4735675) B4735675
theorem B68344145 : Blo 1108626 68344145 := bstep (se 2 (by rfl) ⟨25629054, by rfl⟩ : syracuseStep 68344145 = 51258109) B51258109
theorem B2808553 : Blo 1108626 2808553 := bstep (se 2 (by rfl) ⟨1053207, by rfl⟩ : syracuseStep 2808553 = 2106415) B2106415
theorem B10672955 : Blo 1108626 10672955 := bstep (se 1 (by rfl) ⟨8004716, by rfl⟩ : syracuseStep 10672955 = 16009433) B16009433
theorem B3562343 : Blo 1108626 3562343 := bstep (se 1 (by rfl) ⟨2671757, by rfl⟩ : syracuseStep 3562343 = 5343515) B5343515
theorem B2808857 : Blo 1108626 2808857 := bstep (se 2 (by rfl) ⟨1053321, by rfl⟩ : syracuseStep 2808857 = 2106643) B2106643
theorem B6315191 : Blo 1108626 6315191 := bstep (se 1 (by rfl) ⟨4736393, by rfl⟩ : syracuseStep 6315191 = 9472787) B9472787
theorem B2809019 : Blo 1108626 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B2809039 : Blo 1108626 2809039 := bstep (se 1 (by rfl) ⟨2106779, by rfl⟩ : syracuseStep 2809039 = 4213559) B4213559
theorem B10116521 : Blo 1108626 10116521 := bstep (se 2 (by rfl) ⟨3793695, by rfl⟩ : syracuseStep 10116521 = 7587391) B7587391
theorem B4218587 : Blo 1108626 4218587 := bstep (se 1 (by rfl) ⟨3163940, by rfl⟩ : syracuseStep 4218587 = 6327881) B6327881
theorem B1662959 : Blo 1108626 1662959 := bstep (se 1 (by rfl) ⟨1247219, by rfl⟩ : syracuseStep 1662959 = 2494439) B2494439
theorem B1826879 : Blo 1108626 1826879 := bstep (se 1 (by rfl) ⟨1370159, by rfl⟩ : syracuseStep 1826879 = 2740319) B2740319
theorem B1663079 : Blo 1108626 1663079 := bstep (se 1 (by rfl) ⟨1247309, by rfl⟩ : syracuseStep 1663079 = 2494619) B2494619
theorem B1335403 : Blo 1108626 1335403 := bstep (se 1 (by rfl) ⟨1001552, by rfl⟩ : syracuseStep 1335403 = 2003105) B2003105
theorem B4219087 : Blo 1108626 4219087 := bstep (se 1 (by rfl) ⟨3164315, by rfl⟩ : syracuseStep 4219087 = 6328631) B6328631
theorem B1663211 : Blo 1108626 1663211 := bstep (se 1 (by rfl) ⟨1247408, by rfl⟩ : syracuseStep 1663211 = 2494817) B2494817
theorem B1663271 : Blo 1108626 1663271 := bstep (se 1 (by rfl) ⟨1247453, by rfl⟩ : syracuseStep 1663271 = 2494907) B2494907
theorem B1663721 : Blo 1108626 1663721 := bstep (se 2 (by rfl) ⟨623895, by rfl⟩ : syracuseStep 1663721 = 1247791) B1247791
theorem B28435373 : Blo 1108626 28435373 := bstep (se 3 (by rfl) ⟨5331632, by rfl⟩ : syracuseStep 28435373 = 10663265) B10663265
theorem B28500983 : Blo 1108626 28500983 := bstep (se 1 (by rfl) ⟨21375737, by rfl⟩ : syracuseStep 28500983 = 42751475) B42751475
theorem B1664111 : Blo 1108626 1664111 := bstep (se 1 (by rfl) ⟨1248083, by rfl⟩ : syracuseStep 1664111 = 2496167) B2496167
theorem B1664231 : Blo 1108626 1664231 := bstep (se 1 (by rfl) ⟨1248173, by rfl⟩ : syracuseStep 1664231 = 2496347) B2496347
theorem B1664297 : Blo 1108626 1664297 := bstep (se 2 (by rfl) ⟨624111, by rfl⟩ : syracuseStep 1664297 = 1248223) B1248223
theorem B1664567 : Blo 1108626 1664567 := bstep (se 1 (by rfl) ⟨1248425, by rfl⟩ : syracuseStep 1664567 = 2496851) B2496851
theorem B1664891 : Blo 1108626 1664891 := bstep (se 1 (by rfl) ⟨1248668, by rfl⟩ : syracuseStep 1664891 = 2497337) B2497337
theorem B1664927 : Blo 1108626 1664927 := bstep (se 1 (by rfl) ⟨1248695, by rfl⟩ : syracuseStep 1664927 = 2497391) B2497391
theorem B1665161 : Blo 1108626 1665161 := bstep (se 2 (by rfl) ⟨624435, by rfl⟩ : syracuseStep 1665161 = 1248871) B1248871
theorem B1665311 : Blo 1108626 1665311 := bstep (se 1 (by rfl) ⟨1248983, by rfl⟩ : syracuseStep 1665311 = 2497967) B2497967
theorem B1665359 : Blo 1108626 1665359 := bstep (se 1 (by rfl) ⟨1249019, by rfl⟩ : syracuseStep 1665359 = 2498039) B2498039
theorem B1665449 : Blo 1108626 1665449 := bstep (se 2 (by rfl) ⟨624543, by rfl⟩ : syracuseStep 1665449 = 1249087) B1249087
theorem B5630471 : Blo 1108626 5630471 := bstep (se 1 (by rfl) ⟨4222853, by rfl⟩ : syracuseStep 5630471 = 8445707) B8445707
theorem B6318607 : Blo 1108626 6318607 := bstep (se 1 (by rfl) ⟨4738955, by rfl⟩ : syracuseStep 6318607 = 9477911) B9477911
theorem B1108635 : Blo 1108626 1108635 := bstep (se 1 (by rfl) ⟨831476, by rfl⟩ : syracuseStep 1108635 = 1662953) B1662953
theorem B2026145 : Blo 1108626 2026145 := bstep (se 2 (by rfl) ⟨759804, by rfl⟩ : syracuseStep 2026145 = 1519609) B1519609
theorem B1665833 : Blo 1108626 1665833 := bstep (se 2 (by rfl) ⟨624687, by rfl⟩ : syracuseStep 1665833 = 1249375) B1249375
theorem B1666043 : Blo 1108626 1666043 := bstep (se 1 (by rfl) ⟨1249532, by rfl⟩ : syracuseStep 1666043 = 2499065) B2499065
theorem B1666103 : Blo 1108626 1666103 := bstep (se 1 (by rfl) ⟨1249577, by rfl⟩ : syracuseStep 1666103 = 2499155) B2499155
theorem B1109103 : Blo 1108626 1109103 := bstep (se 1 (by rfl) ⟨831827, by rfl⟩ : syracuseStep 1109103 = 1663655) B1663655
theorem B2813039 : Blo 1108626 2813039 := bstep (se 1 (by rfl) ⟨2109779, by rfl⟩ : syracuseStep 2813039 = 4219559) B4219559
theorem B1666223 : Blo 1108626 1666223 := bstep (se 1 (by rfl) ⟨1249667, by rfl⟩ : syracuseStep 1666223 = 2499335) B2499335
theorem B1109183 : Blo 1108626 1109183 := bstep (se 1 (by rfl) ⟨831887, by rfl⟩ : syracuseStep 1109183 = 1663775) B1663775
theorem B1109199 : Blo 1108626 1109199 := bstep (se 1 (by rfl) ⟨831899, by rfl⟩ : syracuseStep 1109199 = 1663799) B1663799
theorem B1666283 : Blo 1108626 1666283 := bstep (se 1 (by rfl) ⟨1249712, by rfl⟩ : syracuseStep 1666283 = 2499425) B2499425
theorem B1109319 : Blo 1108626 1109319 := bstep (se 1 (by rfl) ⟨831989, by rfl⟩ : syracuseStep 1109319 = 1663979) B1663979
theorem B6745513 : Blo 1108626 6745513 := bstep (se 2 (by rfl) ⟨2529567, by rfl⟩ : syracuseStep 6745513 = 5059135) B5059135
theorem B5631443 : Blo 1108626 5631443 := bstep (se 1 (by rfl) ⟨4223582, by rfl⟩ : syracuseStep 5631443 = 8447165) B8447165
theorem B1666943 : Blo 1108626 1666943 := bstep (se 1 (by rfl) ⟨1250207, by rfl⟩ : syracuseStep 1666943 = 2500415) B2500415
theorem B1110047 : Blo 1108626 1110047 := bstep (se 1 (by rfl) ⟨832535, by rfl⟩ : syracuseStep 1110047 = 1665071) B1665071
theorem B1110223 : Blo 1108626 1110223 := bstep (se 1 (by rfl) ⟨832667, by rfl⟩ : syracuseStep 1110223 = 1665335) B1665335
theorem B1667279 : Blo 1108626 1667279 := bstep (se 1 (by rfl) ⟨1250459, by rfl⟩ : syracuseStep 1667279 = 2500919) B2500919
theorem B1110343 : Blo 1108626 1110343 := bstep (se 1 (by rfl) ⟨832757, by rfl⟩ : syracuseStep 1110343 = 1665515) B1665515
theorem B1667399 : Blo 1108626 1667399 := bstep (se 1 (by rfl) ⟨1250549, by rfl⟩ : syracuseStep 1667399 = 2501099) B2501099
theorem B6746465 : Blo 1108626 6746465 := bstep (se 2 (by rfl) ⟨2529924, by rfl⟩ : syracuseStep 6746465 = 5059849) B5059849
theorem B1110811 : Blo 1108626 1110811 := bstep (se 1 (by rfl) ⟨833108, by rfl⟩ : syracuseStep 1110811 = 1666217) B1666217
theorem B1667867 : Blo 1108626 1667867 := bstep (se 1 (by rfl) ⟨1250900, by rfl⟩ : syracuseStep 1667867 = 2501801) B2501801
theorem B11400131 : Blo 1108626 11400131 := bstep (se 1 (by rfl) ⟨8550098, by rfl⟩ : syracuseStep 11400131 = 17100197) B17100197
theorem B1111087 : Blo 1108626 1111087 := bstep (se 1 (by rfl) ⟨833315, by rfl⟩ : syracuseStep 1111087 = 1666631) B1666631
theorem B1668143 : Blo 1108626 1668143 := bstep (se 1 (by rfl) ⟨1251107, by rfl⟩ : syracuseStep 1668143 = 2502215) B2502215
theorem B1668191 : Blo 1108626 1668191 := bstep (se 1 (by rfl) ⟨1251143, by rfl⟩ : syracuseStep 1668191 = 2502287) B2502287
theorem B1668251 : Blo 1108626 1668251 := bstep (se 1 (by rfl) ⟨1251188, by rfl⟩ : syracuseStep 1668251 = 2502377) B2502377
theorem B1111207 : Blo 1108626 1111207 := bstep (se 1 (by rfl) ⟨833405, by rfl⟩ : syracuseStep 1111207 = 1666811) B1666811
theorem B1668263 : Blo 1108626 1668263 := bstep (se 1 (by rfl) ⟨1251197, by rfl⟩ : syracuseStep 1668263 = 2502395) B2502395
theorem B6747563 : Blo 1108626 6747563 := bstep (se 1 (by rfl) ⟨5060672, by rfl⟩ : syracuseStep 6747563 = 10121345) B10121345
theorem B1111655 : Blo 1108626 1111655 := bstep (se 1 (by rfl) ⟨833741, by rfl⟩ : syracuseStep 1111655 = 1667483) B1667483
theorem B2815631 : Blo 1108626 2815631 := bstep (se 1 (by rfl) ⟨2111723, by rfl⟩ : syracuseStep 2815631 = 4223447) B4223447
theorem B1668935 : Blo 1108626 1668935 := bstep (se 1 (by rfl) ⟨1251701, by rfl⟩ : syracuseStep 1668935 = 2503403) B2503403
theorem B1111935 : Blo 1108626 1111935 := bstep (se 1 (by rfl) ⟨833951, by rfl⟩ : syracuseStep 1111935 = 1667903) B1667903
theorem B6322049 : Blo 1108626 6322049 := bstep (se 2 (by rfl) ⟨2370768, by rfl⟩ : syracuseStep 6322049 = 4741537) B4741537
theorem B1112031 : Blo 1108626 1112031 := bstep (se 1 (by rfl) ⟨834023, by rfl⟩ : syracuseStep 1112031 = 1668047) B1668047
theorem B1112059 : Blo 1108626 1112059 := bstep (se 1 (by rfl) ⟨834044, by rfl⟩ : syracuseStep 1112059 = 1668089) B1668089
theorem B1112091 : Blo 1108626 1112091 := bstep (se 1 (by rfl) ⟨834068, by rfl⟩ : syracuseStep 1112091 = 1668137) B1668137
theorem B1112111 : Blo 1108626 1112111 := bstep (se 1 (by rfl) ⟨834083, by rfl⟩ : syracuseStep 1112111 = 1668167) B1668167
theorem B1112231 : Blo 1108626 1112231 := bstep (se 1 (by rfl) ⟨834173, by rfl⟩ : syracuseStep 1112231 = 1668347) B1668347
theorem B12646691 : Blo 1108626 12646691 := bstep (se 1 (by rfl) ⟨9485018, by rfl⟩ : syracuseStep 12646691 = 18970037) B18970037
theorem B5339459 : Blo 1108626 5339459 := bstep (se 1 (by rfl) ⟨4004594, by rfl⟩ : syracuseStep 5339459 = 8009189) B8009189
theorem B15989825 : Blo 1108626 15989825 := bstep (se 2 (by rfl) ⟨5996184, by rfl⟩ : syracuseStep 15989825 = 11992369) B11992369
theorem B13532285 : Blo 1108626 13532285 := bstep (se 3 (by rfl) ⟨2537303, by rfl⟩ : syracuseStep 13532285 = 5074607) B5074607
theorem B61636085 : Blo 1108626 61636085 := bstep (se 5 (by rfl) ⟨2889191, by rfl⟩ : syracuseStep 61636085 = 5778383) B5778383
theorem B14220967 : Blo 1108626 14220967 := bstep (se 1 (by rfl) ⟨10665725, by rfl⟩ : syracuseStep 14220967 = 21331451) B21331451
theorem B6422921 : Blo 1108626 6422921 := bstep (se 2 (by rfl) ⟨2408595, by rfl⟩ : syracuseStep 6422921 = 4817191) B4817191
theorem B3802153 : Blo 1108626 3802153 := bstep (se 2 (by rfl) ⟨1425807, by rfl⟩ : syracuseStep 3802153 = 2851615) B2851615
theorem B24381071 : Blo 1108626 24381071 := bstep (se 1 (by rfl) ⟨18285803, by rfl⟩ : syracuseStep 24381071 = 36571607) B36571607
theorem B1804123 : Blo 1108626 1804123 := bstep (se 1 (by rfl) ⟨1353092, by rfl⟩ : syracuseStep 1804123 = 2706185) B2706185
theorem B16026731 : Blo 1108626 16026731 := bstep (se 1 (by rfl) ⟨12020048, by rfl⟩ : syracuseStep 16026731 = 24040097) B24040097
theorem B8424809 : Blo 1108626 8424809 := bstep (se 2 (by rfl) ⟨3159303, by rfl⟩ : syracuseStep 8424809 = 6318607) B6318607
theorem B1871275 : Blo 1108626 1871275 := bstep (se 1 (by rfl) ⟨1403456, by rfl⟩ : syracuseStep 1871275 = 2806913) B2806913
theorem B21368357 : Blo 1108626 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B6753935 : Blo 1108626 6753935 := bstep (se 1 (by rfl) ⟨5065451, by rfl⟩ : syracuseStep 6753935 = 10130903) B10130903
theorem B1871815 : Blo 1108626 1871815 := bstep (se 1 (by rfl) ⟨1403861, by rfl⟩ : syracuseStep 1871815 = 2807723) B2807723
theorem B26972135 : Blo 1108626 26972135 := bstep (se 1 (by rfl) ⟨20229101, by rfl⟩ : syracuseStep 26972135 = 40458203) B40458203
theorem B1249519 : Blo 1108626 1249519 := bstep (se 1 (by rfl) ⟨937139, by rfl⟩ : syracuseStep 1249519 = 1874279) B1874279
theorem B2167067 : Blo 1108626 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B7115303 : Blo 1108626 7115303 := bstep (se 1 (by rfl) ⟨5336477, by rfl⟩ : syracuseStep 7115303 = 10672955) B10672955
theorem B1872571 : Blo 1108626 1872571 := bstep (se 1 (by rfl) ⟨1404428, by rfl⟩ : syracuseStep 1872571 = 2808857) B2808857
theorem B1872679 : Blo 1108626 1872679 := bstep (se 1 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 1872679 = 2809019) B2809019
theorem B70325567 : Blo 1108626 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B2496743 : Blo 1108626 2496743 := bstep (se 1 (by rfl) ⟨1872557, by rfl⟩ : syracuseStep 2496743 = 3745115) B3745115
theorem B28842875 : Blo 1108626 28842875 := bstep (se 1 (by rfl) ⟨21632156, by rfl⟩ : syracuseStep 28842875 = 43264313) B43264313
theorem B3742793 : Blo 1108626 3742793 := bstep (se 2 (by rfl) ⟨1403547, by rfl⟩ : syracuseStep 3742793 = 2807095) B2807095
theorem B1350763 : Blo 1108626 1350763 := bstep (se 1 (by rfl) ⟨1013072, by rfl⟩ : syracuseStep 1350763 = 2026145) B2026145
theorem B1875359 : Blo 1108626 1875359 := bstep (se 1 (by rfl) ⟨1406519, by rfl⟩ : syracuseStep 1875359 = 2813039) B2813039
theorem B17309497 : Blo 1108626 17309497 := bstep (se 2 (by rfl) ⟨6491061, by rfl⟩ : syracuseStep 17309497 = 12982123) B12982123
theorem B83369807 : Blo 1108626 83369807 := bstep (se 1 (by rfl) ⟨62527355, by rfl⟩ : syracuseStep 83369807 = 125054711) B125054711
theorem B8101889 : Blo 1108626 8101889 := bstep (se 2 (by rfl) ⟨3038208, by rfl⟩ : syracuseStep 8101889 = 6076417) B6076417
theorem B18948167 : Blo 1108626 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B4497643 : Blo 1108626 4497643 := bstep (se 1 (by rfl) ⟨3373232, by rfl⟩ : syracuseStep 4497643 = 6746465) B6746465
theorem B36086093 : Blo 1108626 36086093 := bstep (se 3 (by rfl) ⟨6766142, by rfl⟩ : syracuseStep 36086093 = 13532285) B13532285
theorem B2367967 : Blo 1108626 2367967 := bstep (se 1 (by rfl) ⟨1775975, by rfl⟩ : syracuseStep 2367967 = 3551951) B3551951
theorem B4498375 : Blo 1108626 4498375 := bstep (se 1 (by rfl) ⟨3373781, by rfl⟩ : syracuseStep 4498375 = 6747563) B6747563
theorem B3744737 : Blo 1108626 3744737 := bstep (se 2 (by rfl) ⟨1404276, by rfl⟩ : syracuseStep 3744737 = 2808553) B2808553
theorem B1877087 : Blo 1108626 1877087 := bstep (se 1 (by rfl) ⟨1407815, by rfl⟩ : syracuseStep 1877087 = 2815631) B2815631
theorem B8431127 : Blo 1108626 8431127 := bstep (se 1 (by rfl) ⟨6323345, by rfl⟩ : syracuseStep 8431127 = 12646691) B12646691
theorem B3745385 : Blo 1108626 3745385 := bstep (se 2 (by rfl) ⟨1404519, by rfl⟩ : syracuseStep 3745385 = 2809039) B2809039
theorem B3745547 : Blo 1108626 3745547 := bstep (se 1 (by rfl) ⟨2809160, by rfl⟩ : syracuseStep 3745547 = 5618321) B5618321
theorem B10659883 : Blo 1108626 10659883 := bstep (se 1 (by rfl) ⟨7994912, by rfl⟩ : syracuseStep 10659883 = 15989825) B15989825
theorem B1780031 : Blo 1108626 1780031 := bstep (se 1 (by rfl) ⟨1335023, by rfl⟩ : syracuseStep 1780031 = 2670047) B2670047
theorem B1780537 : Blo 1108626 1780537 := bstep (se 2 (by rfl) ⟨667701, by rfl⟩ : syracuseStep 1780537 = 1335403) B1335403
theorem B2370503 : Blo 1108626 2370503 := bstep (se 1 (by rfl) ⟨1777877, by rfl⟩ : syracuseStep 2370503 = 3555755) B3555755
theorem B2108359 : Blo 1108626 2108359 := bstep (se 1 (by rfl) ⟨1581269, by rfl⟩ : syracuseStep 2108359 = 3162539) B3162539
theorem B2370863 : Blo 1108626 2370863 := bstep (se 1 (by rfl) ⟨1778147, by rfl⟩ : syracuseStep 2370863 = 3556295) B3556295
theorem B4009439 : Blo 1108626 4009439 := bstep (se 1 (by rfl) ⟨3007079, by rfl⟩ : syracuseStep 4009439 = 6014159) B6014159
theorem B3157481 : Blo 1108626 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B4501097 : Blo 1108626 4501097 := bstep (se 2 (by rfl) ⟨1687911, by rfl⟩ : syracuseStep 4501097 = 3375823) B3375823
theorem B31993487 : Blo 1108626 31993487 := bstep (se 1 (by rfl) ⟨23995115, by rfl⟩ : syracuseStep 31993487 = 47990231) B47990231
theorem B6336377 : Blo 1108626 6336377 := bstep (se 2 (by rfl) ⟨2376141, by rfl⟩ : syracuseStep 6336377 = 4752283) B4752283
theorem B3747707 : Blo 1108626 3747707 := bstep (se 1 (by rfl) ⟨2810780, by rfl⟩ : syracuseStep 3747707 = 5621561) B5621561
theorem B2502953 : Blo 1108626 2502953 := bstep (se 2 (by rfl) ⟨938607, by rfl⟩ : syracuseStep 2502953 = 1877215) B1877215
theorem B162345383 : Blo 1108626 162345383 := bstep (se 1 (by rfl) ⟨121759037, by rfl⟩ : syracuseStep 162345383 = 243518075) B243518075
theorem B3158507 : Blo 1108626 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B24360041 : Blo 1108626 24360041 := bstep (se 2 (by rfl) ⟨9135015, by rfl⟩ : syracuseStep 24360041 = 18270031) B18270031
theorem B3749651 : Blo 1108626 3749651 := bstep (se 1 (by rfl) ⟨2812238, by rfl⟩ : syracuseStep 3749651 = 5624477) B5624477
theorem B3159931 : Blo 1108626 3159931 := bstep (se 1 (by rfl) ⟨2369948, by rfl⟩ : syracuseStep 3159931 = 4739897) B4739897
theorem B2111359 : Blo 1108626 2111359 := bstep (se 1 (by rfl) ⟨1583519, by rfl⟩ : syracuseStep 2111359 = 3167039) B3167039
theorem B2112095 : Blo 1108626 2112095 := bstep (se 1 (by rfl) ⟨1584071, by rfl⟩ : syracuseStep 2112095 = 3168143) B3168143
theorem B45562763 : Blo 1108626 45562763 := bstep (se 1 (by rfl) ⟨34172072, by rfl⟩ : syracuseStep 45562763 = 68344145) B68344145
theorem B8436959 : Blo 1108626 8436959 := bstep (se 1 (by rfl) ⟨6327719, by rfl⟩ : syracuseStep 8436959 = 12655439) B12655439
theorem B8994017 : Blo 1108626 8994017 := bstep (se 2 (by rfl) ⟨3372756, by rfl⟩ : syracuseStep 8994017 = 6745513) B6745513
theorem B2374895 : Blo 1108626 2374895 := bstep (se 1 (by rfl) ⟨1781171, by rfl⟩ : syracuseStep 2374895 = 3562343) B3562343
theorem B4210127 : Blo 1108626 4210127 := bstep (se 1 (by rfl) ⟨3157595, by rfl⟩ : syracuseStep 4210127 = 6315191) B6315191
theorem B2997737 : Blo 1108626 2997737 := bstep (se 2 (by rfl) ⟨1124151, by rfl⟩ : syracuseStep 2997737 = 2248303) B2248303
theorem B3850337 : Blo 1108626 3850337 := bstep (se 2 (by rfl) ⟨1443876, by rfl⟩ : syracuseStep 3850337 = 2887753) B2887753
theorem B4210825 : Blo 1108626 4210825 := bstep (se 2 (by rfl) ⟨1579059, by rfl⟩ : syracuseStep 4210825 = 3158119) B3158119
theorem B4571321 : Blo 1108626 4571321 := bstep (se 2 (by rfl) ⟨1714245, by rfl⟩ : syracuseStep 4571321 = 3428491) B3428491
theorem B9486659 : Blo 1108626 9486659 := bstep (se 1 (by rfl) ⟨7114994, by rfl⟩ : syracuseStep 9486659 = 14229989) B14229989
theorem B18956915 : Blo 1108626 18956915 := bstep (se 1 (by rfl) ⟨14217686, by rfl⟩ : syracuseStep 18956915 = 28435373) B28435373
theorem B6013703 : Blo 1108626 6013703 := bstep (se 1 (by rfl) ⟨4510277, by rfl⟩ : syracuseStep 6013703 = 9020555) B9020555
theorem B3753647 : Blo 1108626 3753647 := bstep (se 1 (by rfl) ⟨2815235, by rfl⟩ : syracuseStep 3753647 = 5630471) B5630471
theorem B3000041 : Blo 1108626 3000041 := bstep (se 2 (by rfl) ⟨1125015, by rfl⟩ : syracuseStep 3000041 = 2250031) B2250031
theorem B12830875 : Blo 1108626 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B24365299 : Blo 1108626 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B2672891 : Blo 1108626 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B3754295 : Blo 1108626 3754295 := bstep (se 1 (by rfl) ⟨2815721, by rfl⟩ : syracuseStep 3754295 = 5631443) B5631443
theorem B4738409 : Blo 1108626 4738409 := bstep (se 2 (by rfl) ⟨1776903, by rfl⟩ : syracuseStep 4738409 = 3553807) B3553807
theorem B49270139 : Blo 1108626 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B4214699 : Blo 1108626 4214699 := bstep (se 1 (by rfl) ⟨3161024, by rfl⟩ : syracuseStep 4214699 = 6322049) B6322049
theorem B3559639 : Blo 1108626 3559639 := bstep (se 1 (by rfl) ⟨2669729, by rfl⟩ : syracuseStep 3559639 = 5339459) B5339459
theorem B24006881 : Blo 1108626 24006881 := bstep (se 2 (by rfl) ⟨9002580, by rfl⟩ : syracuseStep 24006881 = 18005161) B18005161
theorem B18961289 : Blo 1108626 18961289 := bstep (se 2 (by rfl) ⟨7110483, by rfl⟩ : syracuseStep 18961289 = 14220967) B14220967
theorem B8442791 : Blo 1108626 8442791 := bstep (se 1 (by rfl) ⟨6332093, by rfl⟩ : syracuseStep 8442791 = 12664187) B12664187
theorem B5625287 : Blo 1108626 5625287 := bstep (se 1 (by rfl) ⟨4218965, by rfl⟩ : syracuseStep 5625287 = 8437931) B8437931
theorem B4871677 : Blo 1108626 4871677 := bstep (se 3 (by rfl) ⟨913439, by rfl⟩ : syracuseStep 4871677 = 1826879) B1826879
theorem B2807369 : Blo 1108626 2807369 := bstep (se 2 (by rfl) ⟨1052763, by rfl⟩ : syracuseStep 2807369 = 2105527) B2105527
theorem B5625449 : Blo 1108626 5625449 := bstep (se 2 (by rfl) ⟨2109543, by rfl⟩ : syracuseStep 5625449 = 4219087) B4219087
theorem B11392751 : Blo 1108626 11392751 := bstep (se 1 (by rfl) ⟨8544563, by rfl⟩ : syracuseStep 11392751 = 17089127) B17089127
theorem B16013123 : Blo 1108626 16013123 := bstep (se 1 (by rfl) ⟨12009842, by rfl⟩ : syracuseStep 16013123 = 24019685) B24019685
theorem B1202047 : Blo 1108626 1202047 := bstep (se 1 (by rfl) ⟨901535, by rfl⟩ : syracuseStep 1202047 = 1803071) B1803071
theorem B5626583 : Blo 1108626 5626583 := bstep (se 1 (by rfl) ⟨4219937, by rfl⟩ : syracuseStep 5626583 = 8439875) B8439875
theorem B5626907 : Blo 1108626 5626907 := bstep (se 1 (by rfl) ⟨4220180, by rfl⟩ : syracuseStep 5626907 = 8440361) B8440361
theorem B9624683 : Blo 1108626 9624683 := bstep (se 1 (by rfl) ⟨7218512, by rfl⟩ : syracuseStep 9624683 = 14437025) B14437025
theorem B2809151 : Blo 1108626 2809151 := bstep (se 1 (by rfl) ⟨2106863, by rfl⟩ : syracuseStep 2809151 = 4213727) B4213727
theorem B2809313 : Blo 1108626 2809313 := bstep (se 2 (by rfl) ⟨1053492, by rfl⟩ : syracuseStep 2809313 = 2106985) B2106985
theorem B4218601 : Blo 1108626 4218601 := bstep (se 2 (by rfl) ⟨1581975, by rfl⟩ : syracuseStep 4218601 = 3163951) B3163951
theorem B1662971 : Blo 1108626 1662971 := bstep (se 1 (by rfl) ⟨1247228, by rfl⟩ : syracuseStep 1662971 = 2494457) B2494457
theorem B1663031 : Blo 1108626 1663031 := bstep (se 1 (by rfl) ⟨1247273, by rfl⟩ : syracuseStep 1663031 = 2494547) B2494547
theorem B3006571 : Blo 1108626 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B1663103 : Blo 1108626 1663103 := bstep (se 1 (by rfl) ⟨1247327, by rfl⟩ : syracuseStep 1663103 = 2494655) B2494655
theorem B1663151 : Blo 1108626 1663151 := bstep (se 1 (by rfl) ⟨1247363, by rfl⟩ : syracuseStep 1663151 = 2494727) B2494727
theorem B3006647 : Blo 1108626 3006647 := bstep (se 1 (by rfl) ⟨2254985, by rfl⟩ : syracuseStep 3006647 = 4509971) B4509971
theorem B2810153 : Blo 1108626 2810153 := bstep (se 2 (by rfl) ⟨1053807, by rfl⟩ : syracuseStep 2810153 = 2107615) B2107615
theorem B1663871 : Blo 1108626 1663871 := bstep (se 1 (by rfl) ⟨1247903, by rfl⟩ : syracuseStep 1663871 = 2495807) B2495807
theorem B1663943 : Blo 1108626 1663943 := bstep (se 1 (by rfl) ⟨1247957, by rfl⟩ : syracuseStep 1663943 = 2495915) B2495915
theorem B4744423 : Blo 1108626 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B1664303 : Blo 1108626 1664303 := bstep (se 1 (by rfl) ⟨1248227, by rfl⟩ : syracuseStep 1664303 = 2496455) B2496455
theorem B1664543 : Blo 1108626 1664543 := bstep (se 1 (by rfl) ⟨1248407, by rfl⟩ : syracuseStep 1664543 = 2496815) B2496815
theorem B6318107 : Blo 1108626 6318107 := bstep (se 1 (by rfl) ⟨4738580, by rfl⟩ : syracuseStep 6318107 = 9477161) B9477161
theorem B4745243 : Blo 1108626 4745243 := bstep (se 1 (by rfl) ⟨3558932, by rfl⟩ : syracuseStep 4745243 = 7117865) B7117865
theorem B6744347 : Blo 1108626 6744347 := bstep (se 1 (by rfl) ⟨5058260, by rfl⟩ : syracuseStep 6744347 = 10116521) B10116521
theorem B9005435 : Blo 1108626 9005435 := bstep (se 1 (by rfl) ⟨6754076, by rfl⟩ : syracuseStep 9005435 = 13508153) B13508153
theorem B1665479 : Blo 1108626 1665479 := bstep (se 1 (by rfl) ⟨1249109, by rfl⟩ : syracuseStep 1665479 = 2498219) B2498219
theorem B2812391 : Blo 1108626 2812391 := bstep (se 1 (by rfl) ⟨2109293, by rfl⟩ : syracuseStep 2812391 = 4218587) B4218587
theorem B1108639 : Blo 1108626 1108639 := bstep (se 1 (by rfl) ⟨831479, by rfl⟩ : syracuseStep 1108639 = 1662959) B1662959
theorem B1108719 : Blo 1108626 1108719 := bstep (se 1 (by rfl) ⟨831539, by rfl⟩ : syracuseStep 1108719 = 1663079) B1663079
theorem B1665839 : Blo 1108626 1665839 := bstep (se 1 (by rfl) ⟨1249379, by rfl⟩ : syracuseStep 1665839 = 2498759) B2498759
theorem B1108807 : Blo 1108626 1108807 := bstep (se 1 (by rfl) ⟨831605, by rfl⟩ : syracuseStep 1108807 = 1663211) B1663211
theorem B1108847 : Blo 1108626 1108847 := bstep (se 1 (by rfl) ⟨831635, by rfl⟩ : syracuseStep 1108847 = 1663271) B1663271
theorem B1665959 : Blo 1108626 1665959 := bstep (se 1 (by rfl) ⟨1249469, by rfl⟩ : syracuseStep 1665959 = 2498939) B2498939
theorem B1666139 : Blo 1108626 1666139 := bstep (se 1 (by rfl) ⟨1249604, by rfl⟩ : syracuseStep 1666139 = 2499209) B2499209
theorem B1109147 : Blo 1108626 1109147 := bstep (se 1 (by rfl) ⟨831860, by rfl⟩ : syracuseStep 1109147 = 1663721) B1663721
theorem B19000655 : Blo 1108626 19000655 := bstep (se 1 (by rfl) ⟨14250491, by rfl⟩ : syracuseStep 19000655 = 28500983) B28500983
theorem B9006473 : Blo 1108626 9006473 := bstep (se 2 (by rfl) ⟨3377427, by rfl⟩ : syracuseStep 9006473 = 6754855) B6754855
theorem B1109407 : Blo 1108626 1109407 := bstep (se 1 (by rfl) ⟨832055, by rfl⟩ : syracuseStep 1109407 = 1664111) B1664111
theorem B1109487 : Blo 1108626 1109487 := bstep (se 1 (by rfl) ⟨832115, by rfl⟩ : syracuseStep 1109487 = 1664231) B1664231
theorem B1109531 : Blo 1108626 1109531 := bstep (se 1 (by rfl) ⟨832148, by rfl⟩ : syracuseStep 1109531 = 1664297) B1664297
theorem B1666727 : Blo 1108626 1666727 := bstep (se 1 (by rfl) ⟨1250045, by rfl⟩ : syracuseStep 1666727 = 2500091) B2500091
theorem B1109711 : Blo 1108626 1109711 := bstep (se 1 (by rfl) ⟨832283, by rfl⟩ : syracuseStep 1109711 = 1664567) B1664567
theorem B1666847 : Blo 1108626 1666847 := bstep (se 1 (by rfl) ⟨1250135, by rfl⟩ : syracuseStep 1666847 = 2500271) B2500271
theorem B1666907 : Blo 1108626 1666907 := bstep (se 1 (by rfl) ⟨1250180, by rfl⟩ : syracuseStep 1666907 = 2500361) B2500361
theorem B1109927 : Blo 1108626 1109927 := bstep (se 1 (by rfl) ⟨832445, by rfl⟩ : syracuseStep 1109927 = 1664891) B1664891
theorem B1109951 : Blo 1108626 1109951 := bstep (se 1 (by rfl) ⟨832463, by rfl⟩ : syracuseStep 1109951 = 1664927) B1664927
theorem B1667051 : Blo 1108626 1667051 := bstep (se 1 (by rfl) ⟨1250288, by rfl⟩ : syracuseStep 1667051 = 2500577) B2500577
theorem B1110107 : Blo 1108626 1110107 := bstep (se 1 (by rfl) ⟨832580, by rfl⟩ : syracuseStep 1110107 = 1665161) B1665161
theorem B1110207 : Blo 1108626 1110207 := bstep (se 1 (by rfl) ⟨832655, by rfl⟩ : syracuseStep 1110207 = 1665311) B1665311
theorem B1110239 : Blo 1108626 1110239 := bstep (se 1 (by rfl) ⟨832679, by rfl⟩ : syracuseStep 1110239 = 1665359) B1665359
theorem B1405183 : Blo 1108626 1405183 := bstep (se 1 (by rfl) ⟨1053887, by rfl⟩ : syracuseStep 1405183 = 2107775) B2107775
theorem B1667327 : Blo 1108626 1667327 := bstep (se 1 (by rfl) ⟨1250495, by rfl⟩ : syracuseStep 1667327 = 2500991) B2500991
theorem B1110299 : Blo 1108626 1110299 := bstep (se 1 (by rfl) ⟨832724, by rfl⟩ : syracuseStep 1110299 = 1665449) B1665449
theorem B1110555 : Blo 1108626 1110555 := bstep (se 1 (by rfl) ⟨832916, by rfl⟩ : syracuseStep 1110555 = 1665833) B1665833
theorem B1667639 : Blo 1108626 1667639 := bstep (se 1 (by rfl) ⟨1250729, by rfl⟩ : syracuseStep 1667639 = 2501459) B2501459
theorem B1110695 : Blo 1108626 1110695 := bstep (se 1 (by rfl) ⟨833021, by rfl⟩ : syracuseStep 1110695 = 1666043) B1666043
theorem B1667753 : Blo 1108626 1667753 := bstep (se 2 (by rfl) ⟨625407, by rfl⟩ : syracuseStep 1667753 = 1250815) B1250815
theorem B1110735 : Blo 1108626 1110735 := bstep (se 1 (by rfl) ⟨833051, by rfl⟩ : syracuseStep 1110735 = 1666103) B1666103
theorem B1110815 : Blo 1108626 1110815 := bstep (se 1 (by rfl) ⟨833111, by rfl⟩ : syracuseStep 1110815 = 1666223) B1666223
theorem B1667879 : Blo 1108626 1667879 := bstep (se 1 (by rfl) ⟨1250909, by rfl⟩ : syracuseStep 1667879 = 2501819) B2501819
theorem B1110855 : Blo 1108626 1110855 := bstep (se 1 (by rfl) ⟨833141, by rfl⟩ : syracuseStep 1110855 = 1666283) B1666283
theorem B1667999 : Blo 1108626 1667999 := bstep (se 1 (by rfl) ⟨1250999, by rfl⟩ : syracuseStep 1667999 = 2501999) B2501999
theorem B8549363 : Blo 1108626 8549363 := bstep (se 1 (by rfl) ⟨6412022, by rfl⟩ : syracuseStep 8549363 = 12824045) B12824045
theorem B1111295 : Blo 1108626 1111295 := bstep (se 1 (by rfl) ⟨833471, by rfl⟩ : syracuseStep 1111295 = 1666943) B1666943
theorem B1668479 : Blo 1108626 1668479 := bstep (se 1 (by rfl) ⟨1251359, by rfl⟩ : syracuseStep 1668479 = 2502719) B2502719
theorem B1111519 : Blo 1108626 1111519 := bstep (se 1 (by rfl) ⟨833639, by rfl⟩ : syracuseStep 1111519 = 1667279) B1667279
theorem B4748797 : Blo 1108626 4748797 := bstep (se 3 (by rfl) ⟨890399, by rfl⟩ : syracuseStep 4748797 = 1780799) B1780799
theorem B1111599 : Blo 1108626 1111599 := bstep (se 1 (by rfl) ⟨833699, by rfl⟩ : syracuseStep 1111599 = 1667399) B1667399
theorem B24344171 : Blo 1108626 24344171 := bstep (se 1 (by rfl) ⟨18258128, by rfl⟩ : syracuseStep 24344171 = 36516257) B36516257
theorem B8418977 : Blo 1108626 8418977 := bstep (se 2 (by rfl) ⟨3157116, by rfl⟩ : syracuseStep 8418977 = 6314233) B6314233
theorem B1111911 : Blo 1108626 1111911 := bstep (se 1 (by rfl) ⟨833933, by rfl⟩ : syracuseStep 1111911 = 1667867) B1667867
theorem B7600087 : Blo 1108626 7600087 := bstep (se 1 (by rfl) ⟨5700065, by rfl⟩ : syracuseStep 7600087 = 11400131) B11400131
theorem B1112095 : Blo 1108626 1112095 := bstep (se 1 (by rfl) ⟨834071, by rfl⟩ : syracuseStep 1112095 = 1668143) B1668143
theorem B1112127 : Blo 1108626 1112127 := bstep (se 1 (by rfl) ⟨834095, by rfl⟩ : syracuseStep 1112127 = 1668191) B1668191
theorem B1112167 : Blo 1108626 1112167 := bstep (se 1 (by rfl) ⟨834125, by rfl⟩ : syracuseStep 1112167 = 1668251) B1668251
theorem B1112175 : Blo 1108626 1112175 := bstep (se 1 (by rfl) ⟨834131, by rfl⟩ : syracuseStep 1112175 = 1668263) B1668263
theorem B5404927 : Blo 1108626 5404927 := bstep (se 1 (by rfl) ⟨4053695, by rfl⟩ : syracuseStep 5404927 = 8107391) B8107391
theorem B1112623 : Blo 1108626 1112623 := bstep (se 1 (by rfl) ⟨834467, by rfl⟩ : syracuseStep 1112623 = 1668935) B1668935
theorem B5995883 : Blo 1108626 5995883 := bstep (se 1 (by rfl) ⟨4496912, by rfl⟩ : syracuseStep 5995883 = 8993825) B8993825
theorem B41090723 : Blo 1108626 41090723 := bstep (se 1 (by rfl) ⟨30818042, by rfl⟩ : syracuseStep 41090723 = 61636085) B61636085
theorem B6324439 : Blo 1108626 6324439 := bstep (se 1 (by rfl) ⟨4743329, by rfl⟩ : syracuseStep 6324439 = 9486659) B9486659
theorem B5996857 : Blo 1108626 5996857 := bstep (se 2 (by rfl) ⟨2248821, by rfl⟩ : syracuseStep 5996857 = 4497643) B4497643
theorem B12190189 : Blo 1108626 12190189 := bstep (se 3 (by rfl) ⟨2285660, by rfl⟩ : syracuseStep 12190189 = 4571321) B4571321
theorem B16254047 : Blo 1108626 16254047 := bstep (se 1 (by rfl) ⟨12190535, by rfl⟩ : syracuseStep 16254047 = 24381071) B24381071
theorem B2000027 : Blo 1108626 2000027 := bstep (se 1 (by rfl) ⟨1500020, by rfl⟩ : syracuseStep 2000027 = 3000041) B3000041
theorem B5997833 : Blo 1108626 5997833 := bstep (se 2 (by rfl) ⟨2249187, by rfl⟩ : syracuseStep 5997833 = 4498375) B4498375
theorem B6325897 : Blo 1108626 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B10684487 : Blo 1108626 10684487 := bstep (se 1 (by rfl) ⟨8013365, by rfl⟩ : syracuseStep 10684487 = 16026731) B16026731
theorem B1444711 : Blo 1108626 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B1871579 : Blo 1108626 1871579 := bstep (se 1 (by rfl) ⟨1403684, by rfl⟩ : syracuseStep 1871579 = 2807369) B2807369
theorem B2495033 : Blo 1108626 2495033 := bstep (se 2 (by rfl) ⟨935637, by rfl⟩ : syracuseStep 2495033 = 1871275) B1871275
theorem B2495195 : Blo 1108626 2495195 := bstep (se 1 (by rfl) ⟨1871396, by rfl⟩ : syracuseStep 2495195 = 3742793) B3742793
theorem B1872767 : Blo 1108626 1872767 := bstep (se 1 (by rfl) ⟨1404575, by rfl⟩ : syracuseStep 1872767 = 2809151) B2809151
theorem B1250239 : Blo 1108626 1250239 := bstep (se 1 (by rfl) ⟨937679, by rfl⟩ : syracuseStep 1250239 = 1875359) B1875359
theorem B1872875 : Blo 1108626 1872875 := bstep (se 1 (by rfl) ⟨1404656, by rfl⟩ : syracuseStep 1872875 = 2809313) B2809313
theorem B55579871 : Blo 1108626 55579871 := bstep (se 1 (by rfl) ⟨41684903, by rfl⟩ : syracuseStep 55579871 = 83369807) B83369807
theorem B2495753 : Blo 1108626 2495753 := bstep (se 2 (by rfl) ⟨935907, by rfl⟩ : syracuseStep 2495753 = 1871815) B1871815
theorem B12653981 : Blo 1108626 12653981 := bstep (se 3 (by rfl) ⟨2372621, by rfl⟩ : syracuseStep 12653981 = 4745243) B4745243
theorem B2004431 : Blo 1108626 2004431 := bstep (se 1 (by rfl) ⟨1503323, by rfl⟩ : syracuseStep 2004431 = 3006647) B3006647
theorem B1873435 : Blo 1108626 1873435 := bstep (se 1 (by rfl) ⟨1405076, by rfl⟩ : syracuseStep 1873435 = 2810153) B2810153
theorem B24057395 : Blo 1108626 24057395 := bstep (se 1 (by rfl) ⟨18043046, by rfl⟩ : syracuseStep 24057395 = 36086093) B36086093
theorem B1873577 : Blo 1108626 1873577 := bstep (se 2 (by rfl) ⟨702591, by rfl⟩ : syracuseStep 1873577 = 1405183) B1405183
theorem B2496491 : Blo 1108626 2496491 := bstep (se 1 (by rfl) ⟨1872368, by rfl⟩ : syracuseStep 2496491 = 3744737) B3744737
theorem B1251391 : Blo 1108626 1251391 := bstep (se 1 (by rfl) ⟨938543, by rfl⟩ : syracuseStep 1251391 = 1877087) B1877087
theorem B2496761 : Blo 1108626 2496761 := bstep (se 2 (by rfl) ⟨936285, by rfl⟩ : syracuseStep 2496761 = 1872571) B1872571
theorem B2496905 : Blo 1108626 2496905 := bstep (se 2 (by rfl) ⟨936339, by rfl⟩ : syracuseStep 2496905 = 1872679) B1872679
theorem B2496923 : Blo 1108626 2496923 := bstep (se 1 (by rfl) ⟨1872692, by rfl⟩ : syracuseStep 2496923 = 3745385) B3745385
theorem B2497031 : Blo 1108626 2497031 := bstep (se 1 (by rfl) ⟨1872773, by rfl⟩ : syracuseStep 2497031 = 3745547) B3745547
theorem B4496231 : Blo 1108626 4496231 := bstep (se 1 (by rfl) ⟨3372173, by rfl⟩ : syracuseStep 4496231 = 6744347) B6744347
theorem B1186687 : Blo 1108626 1186687 := bstep (se 1 (by rfl) ⟨890015, by rfl⟩ : syracuseStep 1186687 = 1780031) B1780031
theorem B6003623 : Blo 1108626 6003623 := bstep (se 1 (by rfl) ⟨4502717, by rfl⟩ : syracuseStep 6003623 = 9005435) B9005435
theorem B1874927 : Blo 1108626 1874927 := bstep (se 1 (by rfl) ⟨1406195, by rfl⟩ : syracuseStep 1874927 = 2812391) B2812391
theorem B6495569 : Blo 1108626 6495569 := bstep (se 2 (by rfl) ⟨2435838, by rfl⟩ : syracuseStep 6495569 = 4871677) B4871677
theorem B6331729 : Blo 1108626 6331729 := bstep (se 2 (by rfl) ⟨2374398, by rfl⟩ : syracuseStep 6331729 = 4748797) B4748797
theorem B1580575 : Blo 1108626 1580575 := bstep (se 1 (by rfl) ⟨1185431, by rfl⟩ : syracuseStep 1580575 = 2370863) B2370863
theorem B6004315 : Blo 1108626 6004315 := bstep (se 1 (by rfl) ⟨4503236, by rfl⟩ : syracuseStep 6004315 = 9006473) B9006473
theorem B2498471 : Blo 1108626 2498471 := bstep (se 1 (by rfl) ⟨1873853, by rfl⟩ : syracuseStep 2498471 = 3747707) B3747707
theorem B25665821 : Blo 1108626 25665821 := bstep (se 3 (by rfl) ⟨4812341, by rfl⟩ : syracuseStep 25665821 = 9624683) B9624683
theorem B2105671 : Blo 1108626 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B16229447 : Blo 1108626 16229447 := bstep (se 1 (by rfl) ⟨12172085, by rfl⟩ : syracuseStep 16229447 = 24344171) B24344171
theorem B5612651 : Blo 1108626 5612651 := bstep (se 1 (by rfl) ⟨4209488, by rfl⟩ : syracuseStep 5612651 = 8418977) B8418977
theorem B2499767 : Blo 1108626 2499767 := bstep (se 1 (by rfl) ⟨1874825, by rfl⟩ : syracuseStep 2499767 = 3749651) B3749651
theorem B1583263 : Blo 1108626 1583263 := bstep (se 1 (by rfl) ⟨1187447, by rfl⟩ : syracuseStep 1583263 = 2374895) B2374895
theorem B23079329 : Blo 1108626 23079329 := bstep (se 2 (by rfl) ⟨8654748, by rfl⟩ : syracuseStep 23079329 = 17309497) B17309497
theorem B2566891 : Blo 1108626 2566891 := bstep (se 1 (by rfl) ⟨1925168, by rfl⟩ : syracuseStep 2566891 = 3850337) B3850337
theorem B4008761 : Blo 1108626 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B5614433 : Blo 1108626 5614433 := bstep (se 2 (by rfl) ⟨2105412, by rfl⟩ : syracuseStep 5614433 = 4210825) B4210825
theorem B3157289 : Blo 1108626 3157289 := bstep (se 2 (by rfl) ⟨1183983, by rfl⟩ : syracuseStep 3157289 = 2367967) B2367967
theorem B68431333 : Blo 1108626 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B2502431 : Blo 1108626 2502431 := bstep (se 1 (by rfl) ⟨1876823, by rfl⟩ : syracuseStep 2502431 = 3753647) B3753647
theorem B1781927 : Blo 1108626 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B2502863 : Blo 1108626 2502863 := bstep (se 1 (by rfl) ⟨1877147, by rfl⟩ : syracuseStep 2502863 = 3754295) B3754295
theorem B16036541 : Blo 1108626 16036541 := bstep (se 3 (by rfl) ⟨3006851, by rfl⟩ : syracuseStep 16036541 = 6013703) B6013703
theorem B3158939 : Blo 1108626 3158939 := bstep (se 1 (by rfl) ⟨2369204, by rfl⟩ : syracuseStep 3158939 = 4738409) B4738409
theorem B5616539 : Blo 1108626 5616539 := bstep (se 1 (by rfl) ⟨4212404, by rfl⟩ : syracuseStep 5616539 = 8424809) B8424809
theorem B32846759 : Blo 1108626 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B4502623 : Blo 1108626 4502623 := bstep (se 1 (by rfl) ⟨3376967, by rfl⟩ : syracuseStep 4502623 = 6753935) B6753935
theorem B2405497 : Blo 1108626 2405497 := bstep (se 2 (by rfl) ⟨902061, by rfl⟩ : syracuseStep 2405497 = 1804123) B1804123
theorem B16004587 : Blo 1108626 16004587 := bstep (se 1 (by rfl) ⟨12003440, by rfl⟩ : syracuseStep 16004587 = 24006881) B24006881
theorem B32487065 : Blo 1108626 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B3750191 : Blo 1108626 3750191 := bstep (se 1 (by rfl) ⟨2812643, by rfl⟩ : syracuseStep 3750191 = 5625287) B5625287
theorem B3750299 : Blo 1108626 3750299 := bstep (se 1 (by rfl) ⟨2812724, by rfl⟩ : syracuseStep 3750299 = 5625449) B5625449
theorem B2374049 : Blo 1108626 2374049 := bstep (se 2 (by rfl) ⟨890268, by rfl⟩ : syracuseStep 2374049 = 1780537) B1780537
theorem B3751055 : Blo 1108626 3751055 := bstep (se 1 (by rfl) ⟨2813291, by rfl⟩ : syracuseStep 3751055 = 5626583) B5626583
theorem B3751271 : Blo 1108626 3751271 := bstep (se 1 (by rfl) ⟨2813453, by rfl⟩ : syracuseStep 3751271 = 5626907) B5626907
theorem B12632111 : Blo 1108626 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B5620751 : Blo 1108626 5620751 := bstep (se 1 (by rfl) ⟨4215563, by rfl⟩ : syracuseStep 5620751 = 8431127) B8431127
theorem B4212071 : Blo 1108626 4212071 := bstep (se 1 (by rfl) ⟨3159053, by rfl⟩ : syracuseStep 4212071 = 6318107) B6318107
theorem B12667103 : Blo 1108626 12667103 := bstep (se 1 (by rfl) ⟨9500327, by rfl⟩ : syracuseStep 12667103 = 19000655) B19000655
theorem B2672959 : Blo 1108626 2672959 := bstep (se 1 (by rfl) ⟨2004719, by rfl⟩ : syracuseStep 2672959 = 4009439) B4009439
theorem B3000731 : Blo 1108626 3000731 := bstep (se 1 (by rfl) ⟨2250548, by rfl⟩ : syracuseStep 3000731 = 4501097) B4501097
theorem B4213241 : Blo 1108626 4213241 := bstep (se 2 (by rfl) ⟨1579965, by rfl⟩ : syracuseStep 4213241 = 3159931) B3159931
theorem B16240027 : Blo 1108626 16240027 := bstep (se 1 (by rfl) ⟨12180020, by rfl⟩ : syracuseStep 16240027 = 24360041) B24360041
theorem B6410917 : Blo 1108626 6410917 := bstep (se 4 (by rfl) ⟨601023, by rfl⟩ : syracuseStep 6410917 = 1202047) B1202047
theorem B5624639 : Blo 1108626 5624639 := bstep (se 1 (by rfl) ⟨4218479, by rfl⟩ : syracuseStep 5624639 = 8436959) B8436959
theorem B2806751 : Blo 1108626 2806751 := bstep (se 1 (by rfl) ⟨2105063, by rfl⟩ : syracuseStep 2806751 = 4210127) B4210127
theorem B5624801 : Blo 1108626 5624801 := bstep (se 2 (by rfl) ⟨2109300, by rfl⟩ : syracuseStep 5624801 = 4218601) B4218601
theorem B4281947 : Blo 1108626 4281947 := bstep (se 1 (by rfl) ⟨3211460, by rfl⟩ : syracuseStep 4281947 = 6422921) B6422921
theorem B12637943 : Blo 1108626 12637943 := bstep (se 1 (by rfl) ⟨9478457, by rfl⟩ : syracuseStep 12637943 = 18956915) B18956915
theorem B5069537 : Blo 1108626 5069537 := bstep (se 2 (by rfl) ⟨1901076, by rfl⟩ : syracuseStep 5069537 = 3802153) B3802153
theorem B14245571 : Blo 1108626 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B2809799 : Blo 1108626 2809799 := bstep (se 1 (by rfl) ⟨2107349, by rfl⟩ : syracuseStep 2809799 = 4214699) B4214699
theorem B17981423 : Blo 1108626 17981423 := bstep (se 1 (by rfl) ⟨13486067, by rfl⟩ : syracuseStep 17981423 = 26972135) B26972135
theorem B14213177 : Blo 1108626 14213177 := bstep (se 2 (by rfl) ⟨5329941, by rfl⟩ : syracuseStep 14213177 = 10659883) B10659883
theorem B4743535 : Blo 1108626 4743535 := bstep (se 1 (by rfl) ⟨3557651, by rfl⟩ : syracuseStep 4743535 = 7115303) B7115303
theorem B12640859 : Blo 1108626 12640859 := bstep (se 1 (by rfl) ⟨9480644, by rfl⟩ : syracuseStep 12640859 = 18961289) B18961289
theorem B5628527 : Blo 1108626 5628527 := bstep (se 1 (by rfl) ⟨4221395, by rfl⟩ : syracuseStep 5628527 = 8442791) B8442791
theorem B46883711 : Blo 1108626 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B7595167 : Blo 1108626 7595167 := bstep (se 1 (by rfl) ⟨5696375, by rfl⟩ : syracuseStep 7595167 = 11392751) B11392751
theorem B10675415 : Blo 1108626 10675415 := bstep (se 1 (by rfl) ⟨8006561, by rfl⟩ : syracuseStep 10675415 = 16013123) B16013123
theorem B2811145 : Blo 1108626 2811145 := bstep (se 2 (by rfl) ⟨1054179, by rfl⟩ : syracuseStep 2811145 = 2108359) B2108359
theorem B1664495 : Blo 1108626 1664495 := bstep (se 1 (by rfl) ⟨1248371, by rfl⟩ : syracuseStep 1664495 = 2496743) B2496743
theorem B19228583 : Blo 1108626 19228583 := bstep (se 1 (by rfl) ⟨14421437, by rfl⟩ : syracuseStep 19228583 = 28842875) B28842875
theorem B1108647 : Blo 1108626 1108647 := bstep (se 1 (by rfl) ⟨831485, by rfl⟩ : syracuseStep 1108647 = 1662971) B1662971
theorem B5401259 : Blo 1108626 5401259 := bstep (se 1 (by rfl) ⟨4050944, by rfl⟩ : syracuseStep 5401259 = 8101889) B8101889
theorem B1108687 : Blo 1108626 1108687 := bstep (se 1 (by rfl) ⟨831515, by rfl⟩ : syracuseStep 1108687 = 1663031) B1663031
theorem B1108735 : Blo 1108626 1108735 := bstep (se 1 (by rfl) ⟨831551, by rfl⟩ : syracuseStep 1108735 = 1663103) B1663103
theorem B1108767 : Blo 1108626 1108767 := bstep (se 1 (by rfl) ⟨831575, by rfl⟩ : syracuseStep 1108767 = 1663151) B1663151
theorem B4746185 : Blo 1108626 4746185 := bstep (se 2 (by rfl) ⟨1779819, by rfl⟩ : syracuseStep 4746185 = 3559639) B3559639
theorem B1666025 : Blo 1108626 1666025 := bstep (se 2 (by rfl) ⟨624759, by rfl⟩ : syracuseStep 1666025 = 1249519) B1249519
theorem B7204069 : Blo 1108626 7204069 := bstep (se 4 (by rfl) ⟨675381, by rfl⟩ : syracuseStep 7204069 = 1350763) B1350763
theorem B1109247 : Blo 1108626 1109247 := bstep (se 1 (by rfl) ⟨831935, by rfl⟩ : syracuseStep 1109247 = 1663871) B1663871
theorem B1109295 : Blo 1108626 1109295 := bstep (se 1 (by rfl) ⟨831971, by rfl⟩ : syracuseStep 1109295 = 1663943) B1663943
theorem B1109535 : Blo 1108626 1109535 := bstep (se 1 (by rfl) ⟨832151, by rfl⟩ : syracuseStep 1109535 = 1664303) B1664303
theorem B1109695 : Blo 1108626 1109695 := bstep (se 1 (by rfl) ⟨832271, by rfl⟩ : syracuseStep 1109695 = 1664543) B1664543
theorem B5632253 : Blo 1108626 5632253 := bstep (se 3 (by rfl) ⟨1056047, by rfl⟩ : syracuseStep 5632253 = 2112095) B2112095
theorem B1110319 : Blo 1108626 1110319 := bstep (se 1 (by rfl) ⟨832739, by rfl⟩ : syracuseStep 1110319 = 1665479) B1665479
theorem B1110559 : Blo 1108626 1110559 := bstep (se 1 (by rfl) ⟨832919, by rfl⟩ : syracuseStep 1110559 = 1665839) B1665839
theorem B1110639 : Blo 1108626 1110639 := bstep (se 1 (by rfl) ⟨832979, by rfl⟩ : syracuseStep 1110639 = 1665959) B1665959
theorem B1110759 : Blo 1108626 1110759 := bstep (se 1 (by rfl) ⟨833069, by rfl⟩ : syracuseStep 1110759 = 1666139) B1666139
theorem B21328991 : Blo 1108626 21328991 := bstep (se 1 (by rfl) ⟨15996743, by rfl⟩ : syracuseStep 21328991 = 31993487) B31993487
theorem B1111151 : Blo 1108626 1111151 := bstep (se 1 (by rfl) ⟨833363, by rfl⟩ : syracuseStep 1111151 = 1666727) B1666727
theorem B2815145 : Blo 1108626 2815145 := bstep (se 2 (by rfl) ⟨1055679, by rfl⟩ : syracuseStep 2815145 = 2111359) B2111359
theorem B6321341 : Blo 1108626 6321341 := bstep (se 3 (by rfl) ⟨1185251, by rfl⟩ : syracuseStep 6321341 = 2370503) B2370503
theorem B1111231 : Blo 1108626 1111231 := bstep (se 1 (by rfl) ⟨833423, by rfl⟩ : syracuseStep 1111231 = 1666847) B1666847
theorem B1111271 : Blo 1108626 1111271 := bstep (se 1 (by rfl) ⟨833453, by rfl⟩ : syracuseStep 1111271 = 1666907) B1666907
theorem B4224251 : Blo 1108626 4224251 := bstep (se 1 (by rfl) ⟨3168188, by rfl⟩ : syracuseStep 4224251 = 6336377) B6336377
theorem B1111367 : Blo 1108626 1111367 := bstep (se 1 (by rfl) ⟨833525, by rfl⟩ : syracuseStep 1111367 = 1667051) B1667051
theorem B1111551 : Blo 1108626 1111551 := bstep (se 1 (by rfl) ⟨833663, by rfl⟩ : syracuseStep 1111551 = 1667327) B1667327
theorem B1668635 : Blo 1108626 1668635 := bstep (se 1 (by rfl) ⟨1251476, by rfl⟩ : syracuseStep 1668635 = 2502953) B2502953
theorem B108230255 : Blo 1108626 108230255 := bstep (se 1 (by rfl) ⟨81172691, by rfl⟩ : syracuseStep 108230255 = 162345383) B162345383
theorem B7206569 : Blo 1108626 7206569 := bstep (se 2 (by rfl) ⟨2702463, by rfl⟩ : syracuseStep 7206569 = 5404927) B5404927
theorem B1111759 : Blo 1108626 1111759 := bstep (se 1 (by rfl) ⟨833819, by rfl⟩ : syracuseStep 1111759 = 1667639) B1667639
theorem B1111835 : Blo 1108626 1111835 := bstep (se 1 (by rfl) ⟨833876, by rfl⟩ : syracuseStep 1111835 = 1667753) B1667753
theorem B1111919 : Blo 1108626 1111919 := bstep (se 1 (by rfl) ⟨833939, by rfl⟩ : syracuseStep 1111919 = 1667879) B1667879
theorem B23984045 : Blo 1108626 23984045 := bstep (se 3 (by rfl) ⟨4497008, by rfl⟩ : syracuseStep 23984045 = 8994017) B8994017
theorem B1111999 : Blo 1108626 1111999 := bstep (se 1 (by rfl) ⟨833999, by rfl⟩ : syracuseStep 1111999 = 1667999) B1667999
theorem B5699575 : Blo 1108626 5699575 := bstep (se 1 (by rfl) ⟨4274681, by rfl⟩ : syracuseStep 5699575 = 8549363) B8549363
theorem B1112319 : Blo 1108626 1112319 := bstep (se 1 (by rfl) ⟨834239, by rfl⟩ : syracuseStep 1112319 = 1668479) B1668479
theorem B15989021 : Blo 1108626 15989021 := bstep (se 3 (by rfl) ⟨2997941, by rfl⟩ : syracuseStep 15989021 = 5995883) B5995883
theorem B8419949 : Blo 1108626 8419949 := bstep (se 3 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 8419949 = 3157481) B3157481
theorem B30375175 : Blo 1108626 30375175 := bstep (se 1 (by rfl) ⟨22781381, by rfl⟩ : syracuseStep 30375175 = 45562763) B45562763
theorem B1998491 : Blo 1108626 1998491 := bstep (se 1 (by rfl) ⟨1498868, by rfl⟩ : syracuseStep 1998491 = 2997737) B2997737
theorem B27393815 : Blo 1108626 27393815 := bstep (se 1 (by rfl) ⟨20545361, by rfl⟩ : syracuseStep 27393815 = 41090723) B41090723
theorem B40533797 : Blo 1108626 40533797 := bstep (se 4 (by rfl) ⟨3800043, by rfl⟩ : syracuseStep 40533797 = 7600087) B7600087
theorem B8421407 : Blo 1108626 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B7995809 : Blo 1108626 7995809 := bstep (se 2 (by rfl) ⟨2998428, by rfl⟩ : syracuseStep 7995809 = 5996857) B5996857
theorem B6324713 : Blo 1108626 6324713 := bstep (se 2 (by rfl) ⟨2371767, by rfl⟩ : syracuseStep 6324713 = 4743535) B4743535
theorem B16253585 : Blo 1108626 16253585 := bstep (se 2 (by rfl) ⟨6095094, by rfl⟩ : syracuseStep 16253585 = 12190189) B12190189
theorem B3998555 : Blo 1108626 3998555 := bstep (se 1 (by rfl) ⟨2998916, by rfl⟩ : syracuseStep 3998555 = 5997833) B5997833
theorem B10126889 : Blo 1108626 10126889 := bstep (se 2 (by rfl) ⟨3797583, by rfl⟩ : syracuseStep 10126889 = 7595167) B7595167
theorem B8423837 : Blo 1108626 8423837 := bstep (se 3 (by rfl) ⟨1579469, by rfl⟩ : syracuseStep 8423837 = 3158939) B3158939
theorem B1247719 : Blo 1108626 1247719 := bstep (se 1 (by rfl) ⟨935789, by rfl⟩ : syracuseStep 1247719 = 1871579) B1871579
theorem B1248511 : Blo 1108626 1248511 := bstep (se 1 (by rfl) ⟨936383, by rfl⟩ : syracuseStep 1248511 = 1872767) B1872767
theorem B1871167 : Blo 1108626 1871167 := bstep (se 1 (by rfl) ⟨1403375, by rfl⟩ : syracuseStep 1871167 = 2806751) B2806751
theorem B1248583 : Blo 1108626 1248583 := bstep (se 1 (by rfl) ⟨936437, by rfl⟩ : syracuseStep 1248583 = 1872875) B1872875
theorem B2854631 : Blo 1108626 2854631 := bstep (se 1 (by rfl) ⟨2140973, by rfl⟩ : syracuseStep 2854631 = 4281947) B4281947
theorem B1249051 : Blo 1108626 1249051 := bstep (se 1 (by rfl) ⟨936788, by rfl⟩ : syracuseStep 1249051 = 1873577) B1873577
theorem B8425295 : Blo 1108626 8425295 := bstep (se 1 (by rfl) ⟨6318971, by rfl⟩ : syracuseStep 8425295 = 12637943) B12637943
theorem B5345149 : Blo 1108626 5345149 := bstep (se 3 (by rfl) ⟨1002215, by rfl⟩ : syracuseStep 5345149 = 2004431) B2004431
theorem B9605425 : Blo 1108626 9605425 := bstep (se 2 (by rfl) ⟨3602034, by rfl⟩ : syracuseStep 9605425 = 7204069) B7204069
theorem B3379691 : Blo 1108626 3379691 := bstep (se 1 (by rfl) ⟨2534768, by rfl⟩ : syracuseStep 3379691 = 5069537) B5069537
theorem B4002415 : Blo 1108626 4002415 := bstep (se 1 (by rfl) ⟨3001811, by rfl⟩ : syracuseStep 4002415 = 6003623) B6003623
theorem B1249951 : Blo 1108626 1249951 := bstep (se 1 (by rfl) ⟨937463, by rfl⟩ : syracuseStep 1249951 = 1874927) B1874927
theorem B4330379 : Blo 1108626 4330379 := bstep (se 1 (by rfl) ⟨3247784, by rfl⟩ : syracuseStep 4330379 = 6495569) B6495569
theorem B1873199 : Blo 1108626 1873199 := bstep (se 1 (by rfl) ⟨1404899, by rfl⟩ : syracuseStep 1873199 = 2809799) B2809799
theorem B9475451 : Blo 1108626 9475451 := bstep (se 1 (by rfl) ⟨7106588, by rfl⟩ : syracuseStep 9475451 = 14213177) B14213177
theorem B17110547 : Blo 1108626 17110547 := bstep (se 1 (by rfl) ⟨12832910, by rfl⟩ : syracuseStep 17110547 = 25665821) B25665821
theorem B8427239 : Blo 1108626 8427239 := bstep (se 1 (by rfl) ⟨6320429, by rfl⟩ : syracuseStep 8427239 = 12640859) B12640859
theorem B10819631 : Blo 1108626 10819631 := bstep (se 1 (by rfl) ⟨8114723, by rfl⟩ : syracuseStep 10819631 = 16229447) B16229447
theorem B3741767 : Blo 1108626 3741767 := bstep (se 1 (by rfl) ⟨2806325, by rfl⟩ : syracuseStep 3741767 = 5612651) B5612651
theorem B7116943 : Blo 1108626 7116943 := bstep (se 1 (by rfl) ⟨5337707, by rfl⟩ : syracuseStep 7116943 = 10675415) B10675415
theorem B8001949 : Blo 1108626 8001949 := bstep (se 3 (by rfl) ⟨1500365, by rfl⟩ : syracuseStep 8001949 = 3000731) B3000731
theorem B6330797 : Blo 1108626 6330797 := bstep (se 3 (by rfl) ⟨1187024, by rfl⟩ : syracuseStep 6330797 = 2374049) B2374049
theorem B12819055 : Blo 1108626 12819055 := bstep (se 1 (by rfl) ⟨9614291, by rfl⟩ : syracuseStep 12819055 = 19228583) B19228583
theorem B6003497 : Blo 1108626 6003497 := bstep (se 2 (by rfl) ⟨2251311, by rfl⟩ : syracuseStep 6003497 = 4502623) B4502623
theorem B3742955 : Blo 1108626 3742955 := bstep (se 1 (by rfl) ⟨2807216, by rfl⟩ : syracuseStep 3742955 = 5614433) B5614433
theorem B21339449 : Blo 1108626 21339449 := bstep (se 2 (by rfl) ⟨8002293, by rfl⟩ : syracuseStep 21339449 = 16004587) B16004587
theorem B2497913 : Blo 1108626 2497913 := bstep (se 2 (by rfl) ⟨936717, by rfl⟩ : syracuseStep 2497913 = 1873435) B1873435
theorem B2104859 : Blo 1108626 2104859 := bstep (se 1 (by rfl) ⟨1578644, by rfl⟩ : syracuseStep 2104859 = 3157289) B3157289
theorem B1187951 : Blo 1108626 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B10691027 : Blo 1108626 10691027 := bstep (se 1 (by rfl) ⟨8018270, by rfl⟩ : syracuseStep 10691027 = 16036541) B16036541
theorem B3744359 : Blo 1108626 3744359 := bstep (se 1 (by rfl) ⟨2808269, by rfl⟩ : syracuseStep 3744359 = 5616539) B5616539
theorem B21897839 : Blo 1108626 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B1876763 : Blo 1108626 1876763 := bstep (se 1 (by rfl) ⟨1407572, by rfl⟩ : syracuseStep 1876763 = 2815145) B2815145
theorem B1582249 : Blo 1108626 1582249 := bstep (se 2 (by rfl) ⟨593343, by rfl⟩ : syracuseStep 1582249 = 1186687) B1186687
theorem B10659347 : Blo 1108626 10659347 := bstep (se 1 (by rfl) ⟨7994510, by rfl⟩ : syracuseStep 10659347 = 15989021) B15989021
theorem B2500127 : Blo 1108626 2500127 := bstep (se 1 (by rfl) ⟨1875095, by rfl⟩ : syracuseStep 2500127 = 3750191) B3750191
theorem B2500199 : Blo 1108626 2500199 := bstep (se 1 (by rfl) ⟨1875149, by rfl⟩ : syracuseStep 2500199 = 3750299) B3750299
theorem B5613299 : Blo 1108626 5613299 := bstep (se 1 (by rfl) ⟨4209974, by rfl⟩ : syracuseStep 5613299 = 8419949) B8419949
theorem B2107433 : Blo 1108626 2107433 := bstep (se 2 (by rfl) ⟨790287, by rfl⟩ : syracuseStep 2107433 = 1580575) B1580575
theorem B2500703 : Blo 1108626 2500703 := bstep (se 1 (by rfl) ⟨1875527, by rfl⟩ : syracuseStep 2500703 = 3751055) B3751055
theorem B8005753 : Blo 1108626 8005753 := bstep (se 2 (by rfl) ⟨3002157, by rfl⟩ : syracuseStep 8005753 = 6004315) B6004315
theorem B2500847 : Blo 1108626 2500847 := bstep (se 1 (by rfl) ⟨1875635, by rfl⟩ : syracuseStep 2500847 = 3751271) B3751271
theorem B18262543 : Blo 1108626 18262543 := bstep (se 1 (by rfl) ⟨13696907, by rfl⟩ : syracuseStep 18262543 = 27393815) B27393815
theorem B8432585 : Blo 1108626 8432585 := bstep (se 2 (by rfl) ⟨3162219, by rfl⟩ : syracuseStep 8432585 = 6324439) B6324439
theorem B3747167 : Blo 1108626 3747167 := bstep (se 1 (by rfl) ⟨2810375, by rfl⟩ : syracuseStep 3747167 = 5620751) B5620751
theorem B7122991 : Blo 1108626 7122991 := bstep (se 1 (by rfl) ⟨5342243, by rfl⟩ : syracuseStep 7122991 = 10684487) B10684487
theorem B3748193 : Blo 1108626 3748193 := bstep (se 2 (by rfl) ⟨1405572, by rfl⟩ : syracuseStep 3748193 = 2811145) B2811145
theorem B8434529 : Blo 1108626 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B2111017 : Blo 1108626 2111017 := bstep (se 2 (by rfl) ⟨791631, by rfl⟩ : syracuseStep 2111017 = 1583263) B1583263
theorem B3749759 : Blo 1108626 3749759 := bstep (se 1 (by rfl) ⟨2812319, by rfl⟩ : syracuseStep 3749759 = 5624639) B5624639
theorem B3749867 : Blo 1108626 3749867 := bstep (se 1 (by rfl) ⟨2812400, by rfl⟩ : syracuseStep 3749867 = 5624801) B5624801
theorem B8435987 : Blo 1108626 8435987 := bstep (se 1 (by rfl) ⟨6326990, by rfl⟩ : syracuseStep 8435987 = 12653981) B12653981
theorem B3422521 : Blo 1108626 3422521 := bstep (se 2 (by rfl) ⟨1283445, by rfl⟩ : syracuseStep 3422521 = 2566891) B2566891
theorem B16038263 : Blo 1108626 16038263 := bstep (se 1 (by rfl) ⟨12028697, by rfl⟩ : syracuseStep 16038263 = 24057395) B24057395
theorem B2997487 : Blo 1108626 2997487 := bstep (se 1 (by rfl) ⟨2248115, by rfl⟩ : syracuseStep 2997487 = 4496231) B4496231
theorem B91241777 : Blo 1108626 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B3752351 : Blo 1108626 3752351 := bstep (se 1 (by rfl) ⟨2814263, by rfl⟩ : syracuseStep 3752351 = 5628527) B5628527
theorem B15386219 : Blo 1108626 15386219 := bstep (se 1 (by rfl) ⟨11539664, by rfl⟩ : syracuseStep 15386219 = 23079329) B23079329
theorem B2672507 : Blo 1108626 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B3164123 : Blo 1108626 3164123 := bstep (se 1 (by rfl) ⟨2373092, by rfl⟩ : syracuseStep 3164123 = 4746185) B4746185
theorem B3754835 : Blo 1108626 3754835 := bstep (se 1 (by rfl) ⟨2816126, by rfl⟩ : syracuseStep 3754835 = 5632253) B5632253
theorem B4214227 : Blo 1108626 4214227 := bstep (se 1 (by rfl) ⟨3160670, by rfl⟩ : syracuseStep 4214227 = 6321341) B6321341
theorem B4804379 : Blo 1108626 4804379 := bstep (se 1 (by rfl) ⟨3603284, by rfl⟩ : syracuseStep 4804379 = 7206569) B7206569
theorem B5329309 : Blo 1108626 5329309 := bstep (se 3 (by rfl) ⟨999245, by rfl⟩ : syracuseStep 5329309 = 1998491) B1998491
theorem B8442305 : Blo 1108626 8442305 := bstep (se 2 (by rfl) ⟨3165864, by rfl⟩ : syracuseStep 8442305 = 6331729) B6331729
theorem B27022531 : Blo 1108626 27022531 := bstep (se 1 (by rfl) ⟨20266898, by rfl⟩ : syracuseStep 27022531 = 40533797) B40533797
theorem B2807561 : Blo 1108626 2807561 := bstep (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) B2105671
theorem B10836031 : Blo 1108626 10836031 := bstep (se 1 (by rfl) ⟨8127023, by rfl⟩ : syracuseStep 10836031 = 16254047) B16254047
theorem B1333351 : Blo 1108626 1333351 := bstep (se 1 (by rfl) ⟨1000013, by rfl⟩ : syracuseStep 1333351 = 2000027) B2000027
theorem B2808047 : Blo 1108626 2808047 := bstep (se 1 (by rfl) ⟨2106035, by rfl⟩ : syracuseStep 2808047 = 4212071) B4212071
theorem B8444735 : Blo 1108626 8444735 := bstep (se 1 (by rfl) ⟨6333551, by rfl⟩ : syracuseStep 8444735 = 12667103) B12667103
theorem B2808827 : Blo 1108626 2808827 := bstep (se 1 (by rfl) ⟨2106620, by rfl⟩ : syracuseStep 2808827 = 4213241) B4213241
theorem B1663355 : Blo 1108626 1663355 := bstep (se 1 (by rfl) ⟨1247516, by rfl⟩ : syracuseStep 1663355 = 2495033) B2495033
theorem B3563945 : Blo 1108626 3563945 := bstep (se 2 (by rfl) ⟨1336479, by rfl⟩ : syracuseStep 3563945 = 2672959) B2672959
theorem B1663463 : Blo 1108626 1663463 := bstep (se 1 (by rfl) ⟨1247597, by rfl⟩ : syracuseStep 1663463 = 2495195) B2495195
theorem B37053247 : Blo 1108626 37053247 := bstep (se 1 (by rfl) ⟨27789935, by rfl⟩ : syracuseStep 37053247 = 55579871) B55579871
theorem B1663835 : Blo 1108626 1663835 := bstep (se 1 (by rfl) ⟨1247876, by rfl⟩ : syracuseStep 1663835 = 2495753) B2495753
theorem B1926281 : Blo 1108626 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B1664327 : Blo 1108626 1664327 := bstep (se 1 (by rfl) ⟨1248245, by rfl⟩ : syracuseStep 1664327 = 2496491) B2496491
theorem B1664507 : Blo 1108626 1664507 := bstep (se 1 (by rfl) ⟨1248380, by rfl⟩ : syracuseStep 1664507 = 2496761) B2496761
theorem B1664603 : Blo 1108626 1664603 := bstep (se 1 (by rfl) ⟨1248452, by rfl⟩ : syracuseStep 1664603 = 2496905) B2496905
theorem B1664615 : Blo 1108626 1664615 := bstep (se 1 (by rfl) ⟨1248461, by rfl⟩ : syracuseStep 1664615 = 2496923) B2496923
theorem B1664687 : Blo 1108626 1664687 := bstep (se 1 (by rfl) ⟨1248515, by rfl⟩ : syracuseStep 1664687 = 2497031) B2497031
theorem B21653369 : Blo 1108626 21653369 := bstep (se 2 (by rfl) ⟨8120013, by rfl⟩ : syracuseStep 21653369 = 16240027) B16240027
theorem B9497047 : Blo 1108626 9497047 := bstep (se 1 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 9497047 = 14245571) B14245571
theorem B1665647 : Blo 1108626 1665647 := bstep (se 1 (by rfl) ⟨1249235, by rfl⟩ : syracuseStep 1665647 = 2498471) B2498471
theorem B11987615 : Blo 1108626 11987615 := bstep (se 1 (by rfl) ⟨8990711, by rfl⟩ : syracuseStep 11987615 = 17981423) B17981423
theorem B31255807 : Blo 1108626 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B1666511 : Blo 1108626 1666511 := bstep (se 1 (by rfl) ⟨1249883, by rfl⟩ : syracuseStep 1666511 = 2499767) B2499767
theorem B8547889 : Blo 1108626 8547889 := bstep (se 2 (by rfl) ⟨3205458, by rfl⟩ : syracuseStep 8547889 = 6410917) B6410917
theorem B1109663 : Blo 1108626 1109663 := bstep (se 1 (by rfl) ⟨832247, by rfl⟩ : syracuseStep 1109663 = 1664495) B1664495
theorem B1666985 : Blo 1108626 1666985 := bstep (se 2 (by rfl) ⟨625119, by rfl⟩ : syracuseStep 1666985 = 1250239) B1250239
theorem B3207329 : Blo 1108626 3207329 := bstep (se 2 (by rfl) ⟨1202748, by rfl⟩ : syracuseStep 3207329 = 2405497) B2405497
theorem B3600839 : Blo 1108626 3600839 := bstep (se 1 (by rfl) ⟨2700629, by rfl⟩ : syracuseStep 3600839 = 5401259) B5401259
theorem B1110683 : Blo 1108626 1110683 := bstep (se 1 (by rfl) ⟨833012, by rfl⟩ : syracuseStep 1110683 = 1666025) B1666025
theorem B1668287 : Blo 1108626 1668287 := bstep (se 1 (by rfl) ⟨1251215, by rfl⟩ : syracuseStep 1668287 = 2502431) B2502431
theorem B7599433 : Blo 1108626 7599433 := bstep (se 2 (by rfl) ⟨2849787, by rfl⟩ : syracuseStep 7599433 = 5699575) B5699575
theorem B1668521 : Blo 1108626 1668521 := bstep (se 2 (by rfl) ⟨625695, by rfl⟩ : syracuseStep 1668521 = 1251391) B1251391
theorem B1668575 : Blo 1108626 1668575 := bstep (se 1 (by rfl) ⟨1251431, by rfl⟩ : syracuseStep 1668575 = 2502863) B2502863
theorem B14219327 : Blo 1108626 14219327 := bstep (se 1 (by rfl) ⟨10664495, by rfl⟩ : syracuseStep 14219327 = 21328991) B21328991
theorem B2816167 : Blo 1108626 2816167 := bstep (se 1 (by rfl) ⟨2112125, by rfl⟩ : syracuseStep 2816167 = 4224251) B4224251
theorem B1112423 : Blo 1108626 1112423 := bstep (se 1 (by rfl) ⟨834317, by rfl⟩ : syracuseStep 1112423 = 1668635) B1668635
theorem B72153503 : Blo 1108626 72153503 := bstep (se 1 (by rfl) ⟨54115127, by rfl⟩ : syracuseStep 72153503 = 108230255) B108230255
theorem B21658043 : Blo 1108626 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B15989363 : Blo 1108626 15989363 := bstep (se 1 (by rfl) ⟨11992022, by rfl⟩ : syracuseStep 15989363 = 23984045) B23984045
theorem B40500233 : Blo 1108626 40500233 := bstep (se 2 (by rfl) ⟨15187587, by rfl⟩ : syracuseStep 40500233 = 30375175) B30375175
theorem B6751259 : Blo 1108626 6751259 := bstep (se 1 (by rfl) ⟨5063444, by rfl⟩ : syracuseStep 6751259 = 10126889) B10126889
theorem B10257479 : Blo 1108626 10257479 := bstep (se 1 (by rfl) ⟨7693109, by rfl⟩ : syracuseStep 10257479 = 15386219) B15386219
theorem B9012509 : Blo 1108626 9012509 := bstep (se 3 (by rfl) ⟨1689845, by rfl⟩ : syracuseStep 9012509 = 3379691) B3379691
theorem B1903087 : Blo 1108626 1903087 := bstep (se 1 (by rfl) ⟨1427315, by rfl⟩ : syracuseStep 1903087 = 2854631) B2854631
theorem B24350057 : Blo 1108626 24350057 := bstep (se 2 (by rfl) ⟨9131271, by rfl⟩ : syracuseStep 24350057 = 18262543) B18262543
theorem B1248799 : Blo 1108626 1248799 := bstep (se 1 (by rfl) ⟨936599, by rfl⟩ : syracuseStep 1248799 = 1873199) B1873199
theorem B11407031 : Blo 1108626 11407031 := bstep (se 1 (by rfl) ⟨8555273, by rfl⟩ : syracuseStep 11407031 = 17110547) B17110547
theorem B1871707 : Blo 1108626 1871707 := bstep (se 1 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 1871707 = 2807561) B2807561
theorem B7213087 : Blo 1108626 7213087 := bstep (se 1 (by rfl) ⟨5409815, by rfl⟩ : syracuseStep 7213087 = 10819631) B10819631
theorem B2494511 : Blo 1108626 2494511 := bstep (se 1 (by rfl) ⟨1870883, by rfl⟩ : syracuseStep 2494511 = 3741767) B3741767
theorem B1872031 : Blo 1108626 1872031 := bstep (se 1 (by rfl) ⟨1404023, by rfl⟩ : syracuseStep 1872031 = 2808047) B2808047
theorem B2494889 : Blo 1108626 2494889 := bstep (se 2 (by rfl) ⟨935583, by rfl⟩ : syracuseStep 2494889 = 1871167) B1871167
theorem B4002331 : Blo 1108626 4002331 := bstep (se 1 (by rfl) ⟨3001748, by rfl⟩ : syracuseStep 4002331 = 6003497) B6003497
theorem B1872551 : Blo 1108626 1872551 := bstep (se 1 (by rfl) ⟨1404413, by rfl⟩ : syracuseStep 1872551 = 2808827) B2808827
theorem B2495303 : Blo 1108626 2495303 := bstep (se 1 (by rfl) ⟨1871477, by rfl⟩ : syracuseStep 2495303 = 3742955) B3742955
theorem B14226299 : Blo 1108626 14226299 := bstep (se 1 (by rfl) ⟨10669724, by rfl⟩ : syracuseStep 14226299 = 21339449) B21339449
theorem B2496239 : Blo 1108626 2496239 := bstep (se 1 (by rfl) ⟨1872179, by rfl⟩ : syracuseStep 2496239 = 3744359) B3744359
theorem B1251175 : Blo 1108626 1251175 := bstep (se 1 (by rfl) ⟨938381, by rfl⟩ : syracuseStep 1251175 = 1876763) B1876763
theorem B1284187 : Blo 1108626 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B3742199 : Blo 1108626 3742199 := bstep (se 1 (by rfl) ⟨2806649, by rfl⟩ : syracuseStep 3742199 = 5613299) B5613299
theorem B10132577 : Blo 1108626 10132577 := bstep (se 2 (by rfl) ⟨3799716, by rfl⟩ : syracuseStep 10132577 = 7599433) B7599433
theorem B2498111 : Blo 1108626 2498111 := bstep (se 1 (by rfl) ⟨1873583, by rfl⟩ : syracuseStep 2498111 = 3747167) B3747167
theorem B2138219 : Blo 1108626 2138219 := bstep (se 1 (by rfl) ⟨1603664, by rfl⟩ : syracuseStep 2138219 = 3207329) B3207329
theorem B1777801 : Blo 1108626 1777801 := bstep (se 2 (by rfl) ⟨666675, by rfl⟩ : syracuseStep 1777801 = 1333351) B1333351
theorem B2498795 : Blo 1108626 2498795 := bstep (se 1 (by rfl) ⟨1874096, by rfl⟩ : syracuseStep 2498795 = 3748193) B3748193
theorem B2400559 : Blo 1108626 2400559 := bstep (se 1 (by rfl) ⟨1800419, by rfl⟩ : syracuseStep 2400559 = 3600839) B3600839
theorem B4563361 : Blo 1108626 4563361 := bstep (se 2 (by rfl) ⟨1711260, by rfl⟩ : syracuseStep 4563361 = 3422521) B3422521
theorem B2499839 : Blo 1108626 2499839 := bstep (se 1 (by rfl) ⟨1874879, by rfl⟩ : syracuseStep 2499839 = 3749759) B3749759
theorem B2499911 : Blo 1108626 2499911 := bstep (se 1 (by rfl) ⟨1874933, by rfl⟩ : syracuseStep 2499911 = 3749867) B3749867
theorem B9479551 : Blo 1108626 9479551 := bstep (se 1 (by rfl) ⟨7109663, by rfl⟩ : syracuseStep 9479551 = 14219327) B14219327
theorem B10692175 : Blo 1108626 10692175 := bstep (se 1 (by rfl) ⟨8019131, by rfl⟩ : syracuseStep 10692175 = 16038263) B16038263
theorem B10659575 : Blo 1108626 10659575 := bstep (se 1 (by rfl) ⟨7994681, by rfl⟩ : syracuseStep 10659575 = 15989363) B15989363
theorem B60827851 : Blo 1108626 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B5614271 : Blo 1108626 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B2501567 : Blo 1108626 2501567 := bstep (se 1 (by rfl) ⟨1876175, by rfl⟩ : syracuseStep 2501567 = 3752351) B3752351
theorem B2665703 : Blo 1108626 2665703 := bstep (se 1 (by rfl) ⟨1999277, by rfl⟩ : syracuseStep 2665703 = 3998555) B3998555
theorem B1781671 : Blo 1108626 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B2109415 : Blo 1108626 2109415 := bstep (se 1 (by rfl) ⟨1582061, by rfl⟩ : syracuseStep 2109415 = 3164123) B3164123
theorem B2109665 : Blo 1108626 2109665 := bstep (se 2 (by rfl) ⟨791124, by rfl⟩ : syracuseStep 2109665 = 1582249) B1582249
theorem B5615891 : Blo 1108626 5615891 := bstep (se 1 (by rfl) ⟨4211918, by rfl⟩ : syracuseStep 5615891 = 8423837) B8423837
theorem B2503223 : Blo 1108626 2503223 := bstep (se 1 (by rfl) ⟨1877417, by rfl⟩ : syracuseStep 2503223 = 3754835) B3754835
theorem B11547677 : Blo 1108626 11547677 := bstep (se 3 (by rfl) ⟨2165189, by rfl⟩ : syracuseStep 11547677 = 4330379) B4330379
theorem B5616863 : Blo 1108626 5616863 := bstep (se 1 (by rfl) ⟨4212647, by rfl⟩ : syracuseStep 5616863 = 8425295) B8425295
theorem B21346213 : Blo 1108626 21346213 := bstep (se 4 (by rfl) ⟨2001207, by rfl⟩ : syracuseStep 21346213 = 4002415) B4002415
theorem B12662729 : Blo 1108626 12662729 := bstep (se 2 (by rfl) ⟨4748523, by rfl⟩ : syracuseStep 12662729 = 9497047) B9497047
theorem B5618159 : Blo 1108626 5618159 := bstep (se 1 (by rfl) ⟨4213619, by rfl⟩ : syracuseStep 5618159 = 8427239) B8427239
theorem B5618969 : Blo 1108626 5618969 := bstep (se 2 (by rfl) ⟨2107113, by rfl⟩ : syracuseStep 5618969 = 4214227) B4214227
theorem B7126865 : Blo 1108626 7126865 := bstep (se 2 (by rfl) ⟨2672574, by rfl⟩ : syracuseStep 7126865 = 5345149) B5345149
theorem B2375963 : Blo 1108626 2375963 := bstep (se 1 (by rfl) ⟨1781972, by rfl⟩ : syracuseStep 2375963 = 3563945) B3563945
theorem B7127351 : Blo 1108626 7127351 := bstep (se 1 (by rfl) ⟨5345513, by rfl⟩ : syracuseStep 7127351 = 10691027) B10691027
theorem B14598559 : Blo 1108626 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B14435579 : Blo 1108626 14435579 := bstep (se 1 (by rfl) ⟨10826684, by rfl⟩ : syracuseStep 14435579 = 21653369) B21653369
theorem B36030041 : Blo 1108626 36030041 := bstep (se 2 (by rfl) ⟨13511265, by rfl⟩ : syracuseStep 36030041 = 27022531) B27022531
theorem B5621723 : Blo 1108626 5621723 := bstep (se 1 (by rfl) ⟨4216292, by rfl⟩ : syracuseStep 5621723 = 8432585) B8432585
theorem B9489257 : Blo 1108626 9489257 := bstep (se 2 (by rfl) ⟨3558471, by rfl⟩ : syracuseStep 9489257 = 7116943) B7116943
theorem B3754889 : Blo 1108626 3754889 := bstep (se 2 (by rfl) ⟨1408083, by rfl⟩ : syracuseStep 3754889 = 2816167) B2816167
theorem B10669265 : Blo 1108626 10669265 := bstep (se 2 (by rfl) ⟨4000974, by rfl⟩ : syracuseStep 10669265 = 8001949) B8001949
theorem B5623019 : Blo 1108626 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B17092073 : Blo 1108626 17092073 := bstep (se 2 (by rfl) ⟨6409527, by rfl⟩ : syracuseStep 17092073 = 12819055) B12819055
theorem B5623991 : Blo 1108626 5623991 := bstep (se 1 (by rfl) ⟨4217993, by rfl⟩ : syracuseStep 5623991 = 8435987) B8435987
theorem B14438695 : Blo 1108626 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B5330539 : Blo 1108626 5330539 := bstep (se 1 (by rfl) ⟨3997904, by rfl⟩ : syracuseStep 5330539 = 7995809) B7995809
theorem B4216475 : Blo 1108626 4216475 := bstep (se 1 (by rfl) ⟨3162356, by rfl⟩ : syracuseStep 4216475 = 6324713) B6324713
theorem B10835723 : Blo 1108626 10835723 := bstep (se 1 (by rfl) ⟨8126792, by rfl⟩ : syracuseStep 10835723 = 16253585) B16253585
theorem B49404329 : Blo 1108626 49404329 := bstep (se 2 (by rfl) ⟨18526623, by rfl⟩ : syracuseStep 49404329 = 37053247) B37053247
theorem B12671477 : Blo 1108626 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B3202919 : Blo 1108626 3202919 := bstep (se 1 (by rfl) ⟨2402189, by rfl⟩ : syracuseStep 3202919 = 4804379) B4804379
theorem B10674337 : Blo 1108626 10674337 := bstep (se 2 (by rfl) ⟨4002876, by rfl⟩ : syracuseStep 10674337 = 8005753) B8005753
theorem B5628203 : Blo 1108626 5628203 := bstep (se 1 (by rfl) ⟨4221152, by rfl⟩ : syracuseStep 5628203 = 8442305) B8442305
theorem B1663625 : Blo 1108626 1663625 := bstep (se 2 (by rfl) ⟨623859, by rfl⟩ : syracuseStep 1663625 = 1247719) B1247719
theorem B6316967 : Blo 1108626 6316967 := bstep (se 1 (by rfl) ⟨4737725, by rfl⟩ : syracuseStep 6316967 = 9475451) B9475451
theorem B4220531 : Blo 1108626 4220531 := bstep (se 1 (by rfl) ⟨3165398, by rfl⟩ : syracuseStep 4220531 = 6330797) B6330797
theorem B1664681 : Blo 1108626 1664681 := bstep (se 2 (by rfl) ⟨624255, by rfl⟩ : syracuseStep 1664681 = 1248511) B1248511
theorem B41674409 : Blo 1108626 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B1664777 : Blo 1108626 1664777 := bstep (se 2 (by rfl) ⟨624291, by rfl⟩ : syracuseStep 1664777 = 1248583) B1248583
theorem B5629823 : Blo 1108626 5629823 := bstep (se 1 (by rfl) ⟨4222367, by rfl⟩ : syracuseStep 5629823 = 8444735) B8444735
theorem B11397185 : Blo 1108626 11397185 := bstep (se 2 (by rfl) ⟨4273944, by rfl⟩ : syracuseStep 11397185 = 8547889) B8547889
theorem B1665275 : Blo 1108626 1665275 := bstep (se 1 (by rfl) ⟨1248956, by rfl⟩ : syracuseStep 1665275 = 2497913) B2497913
theorem B1403239 : Blo 1108626 1403239 := bstep (se 1 (by rfl) ⟨1052429, by rfl⟩ : syracuseStep 1403239 = 2104859) B2104859
theorem B1665401 : Blo 1108626 1665401 := bstep (se 2 (by rfl) ⟨624525, by rfl⟩ : syracuseStep 1665401 = 1249051) B1249051
theorem B9497321 : Blo 1108626 9497321 := bstep (se 2 (by rfl) ⟨3561495, by rfl⟩ : syracuseStep 9497321 = 7122991) B7122991
theorem B1108903 : Blo 1108626 1108903 := bstep (se 1 (by rfl) ⟨831677, by rfl⟩ : syracuseStep 1108903 = 1663355) B1663355
theorem B1108975 : Blo 1108626 1108975 := bstep (se 1 (by rfl) ⟨831731, by rfl⟩ : syracuseStep 1108975 = 1663463) B1663463
theorem B12807233 : Blo 1108626 12807233 := bstep (se 2 (by rfl) ⟨4802712, by rfl⟩ : syracuseStep 12807233 = 9605425) B9605425
theorem B7105745 : Blo 1108626 7105745 := bstep (se 2 (by rfl) ⟨2664654, by rfl⟩ : syracuseStep 7105745 = 5329309) B5329309
theorem B1109223 : Blo 1108626 1109223 := bstep (se 1 (by rfl) ⟨831917, by rfl⟩ : syracuseStep 1109223 = 1663835) B1663835
theorem B1666601 : Blo 1108626 1666601 := bstep (se 2 (by rfl) ⟨624975, by rfl⟩ : syracuseStep 1666601 = 1249951) B1249951
theorem B1109551 : Blo 1108626 1109551 := bstep (se 1 (by rfl) ⟨832163, by rfl⟩ : syracuseStep 1109551 = 1664327) B1664327
theorem B1109671 : Blo 1108626 1109671 := bstep (se 1 (by rfl) ⟨832253, by rfl⟩ : syracuseStep 1109671 = 1664507) B1664507
theorem B7106231 : Blo 1108626 7106231 := bstep (se 1 (by rfl) ⟨5329673, by rfl⟩ : syracuseStep 7106231 = 10659347) B10659347
theorem B1666751 : Blo 1108626 1666751 := bstep (se 1 (by rfl) ⟨1250063, by rfl⟩ : syracuseStep 1666751 = 2500127) B2500127
theorem B1109735 : Blo 1108626 1109735 := bstep (se 1 (by rfl) ⟨832301, by rfl⟩ : syracuseStep 1109735 = 1664603) B1664603
theorem B1109743 : Blo 1108626 1109743 := bstep (se 1 (by rfl) ⟨832307, by rfl⟩ : syracuseStep 1109743 = 1664615) B1664615
theorem B1666799 : Blo 1108626 1666799 := bstep (se 1 (by rfl) ⟨1250099, by rfl⟩ : syracuseStep 1666799 = 2500199) B2500199
theorem B1109791 : Blo 1108626 1109791 := bstep (se 1 (by rfl) ⟨832343, by rfl⟩ : syracuseStep 1109791 = 1664687) B1664687
theorem B1404955 : Blo 1108626 1404955 := bstep (se 1 (by rfl) ⟨1053716, by rfl⟩ : syracuseStep 1404955 = 2107433) B2107433
theorem B1667135 : Blo 1108626 1667135 := bstep (se 1 (by rfl) ⟨1250351, by rfl⟩ : syracuseStep 1667135 = 2500703) B2500703
theorem B1667231 : Blo 1108626 1667231 := bstep (se 1 (by rfl) ⟨1250423, by rfl⟩ : syracuseStep 1667231 = 2500847) B2500847
theorem B1110431 : Blo 1108626 1110431 := bstep (se 1 (by rfl) ⟨832823, by rfl⟩ : syracuseStep 1110431 = 1665647) B1665647
theorem B7991743 : Blo 1108626 7991743 := bstep (se 1 (by rfl) ⟨5993807, by rfl⟩ : syracuseStep 7991743 = 11987615) B11987615
theorem B2814689 : Blo 1108626 2814689 := bstep (se 2 (by rfl) ⟨1055508, by rfl⟩ : syracuseStep 2814689 = 2111017) B2111017
theorem B1111007 : Blo 1108626 1111007 := bstep (se 1 (by rfl) ⟨833255, by rfl⟩ : syracuseStep 1111007 = 1666511) B1666511
theorem B1111323 : Blo 1108626 1111323 := bstep (se 1 (by rfl) ⟨833492, by rfl⟩ : syracuseStep 1111323 = 1666985) B1666985
theorem B14448041 : Blo 1108626 14448041 := bstep (se 2 (by rfl) ⟨5418015, by rfl⟩ : syracuseStep 14448041 = 10836031) B10836031
theorem B1112191 : Blo 1108626 1112191 := bstep (se 1 (by rfl) ⟨834143, by rfl⟩ : syracuseStep 1112191 = 1668287) B1668287
theorem B1112347 : Blo 1108626 1112347 := bstep (se 1 (by rfl) ⟨834260, by rfl⟩ : syracuseStep 1112347 = 1668521) B1668521
theorem B1112383 : Blo 1108626 1112383 := bstep (se 1 (by rfl) ⟨834287, by rfl⟩ : syracuseStep 1112383 = 1668575) B1668575
theorem B48102335 : Blo 1108626 48102335 := bstep (se 1 (by rfl) ⟨36076751, by rfl⟩ : syracuseStep 48102335 = 72153503) B72153503
theorem B3996649 : Blo 1108626 3996649 := bstep (se 2 (by rfl) ⟨1498743, by rfl⟩ : syracuseStep 3996649 = 2997487) B2997487
theorem B27000155 : Blo 1108626 27000155 := bstep (se 1 (by rfl) ⟨20250116, by rfl⟩ : syracuseStep 27000155 = 40500233) B40500233
theorem B4751567 : Blo 1108626 4751567 := bstep (se 1 (by rfl) ⟨3563675, by rfl⟩ : syracuseStep 4751567 = 7127351) B7127351
theorem B19464745 : Blo 1108626 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B24020027 : Blo 1108626 24020027 := bstep (se 1 (by rfl) ⟨18015020, by rfl⟩ : syracuseStep 24020027 = 36030041) B36030041
theorem B6326171 : Blo 1108626 6326171 := bstep (se 1 (by rfl) ⟨4744628, by rfl⟩ : syracuseStep 6326171 = 9489257) B9489257
theorem B14256233 : Blo 1108626 14256233 := bstep (se 2 (by rfl) ⟨5346087, by rfl⟩ : syracuseStep 14256233 = 10692175) B10692175
theorem B7112843 : Blo 1108626 7112843 := bstep (se 1 (by rfl) ⟨5334632, by rfl⟩ : syracuseStep 7112843 = 10669265) B10669265
theorem B7604687 : Blo 1108626 7604687 := bstep (se 1 (by rfl) ⟨5703515, by rfl⟩ : syracuseStep 7604687 = 11407031) B11407031
theorem B81103801 : Blo 1108626 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B1248367 : Blo 1108626 1248367 := bstep (se 1 (by rfl) ⟨936275, by rfl⟩ : syracuseStep 1248367 = 1872551) B1872551
theorem B1870985 : Blo 1108626 1870985 := bstep (se 2 (by rfl) ⟨701619, by rfl⟩ : syracuseStep 1870985 = 1403239) B1403239
theorem B32936219 : Blo 1108626 32936219 := bstep (se 1 (by rfl) ⟨24702164, by rfl⟩ : syracuseStep 32936219 = 49404329) B49404329
theorem B2494799 : Blo 1108626 2494799 := bstep (se 1 (by rfl) ⟨1871099, by rfl⟩ : syracuseStep 2494799 = 3742199) B3742199
theorem B6755051 : Blo 1108626 6755051 := bstep (se 1 (by rfl) ⟨5066288, by rfl⟩ : syracuseStep 6755051 = 10132577) B10132577
theorem B2495609 : Blo 1108626 2495609 := bstep (se 2 (by rfl) ⟨935853, by rfl⟩ : syracuseStep 2495609 = 1871707) B1871707
theorem B2135279 : Blo 1108626 2135279 := bstep (se 1 (by rfl) ⟨1601459, by rfl⟩ : syracuseStep 2135279 = 3202919) B3202919
theorem B1873273 : Blo 1108626 1873273 := bstep (se 2 (by rfl) ⟨702477, by rfl⟩ : syracuseStep 1873273 = 1404955) B1404955
theorem B2496041 : Blo 1108626 2496041 := bstep (se 2 (by rfl) ⟨936015, by rfl⟩ : syracuseStep 2496041 = 1872031) B1872031
theorem B10655657 : Blo 1108626 10655657 := bstep (se 2 (by rfl) ⟨3995871, by rfl⟩ : syracuseStep 10655657 = 7991743) B7991743
theorem B3742847 : Blo 1108626 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B6331547 : Blo 1108626 6331547 := bstep (se 1 (by rfl) ⟨4748660, by rfl⟩ : syracuseStep 6331547 = 9497321) B9497321
theorem B1777135 : Blo 1108626 1777135 := bstep (se 1 (by rfl) ⟨1332851, by rfl⟩ : syracuseStep 1777135 = 2665703) B2665703
theorem B1712249 : Blo 1108626 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B3743927 : Blo 1108626 3743927 := bstep (se 1 (by rfl) ⟨2807945, by rfl⟩ : syracuseStep 3743927 = 5615891) B5615891
theorem B1876459 : Blo 1108626 1876459 := bstep (se 1 (by rfl) ⟨1407344, by rfl⟩ : syracuseStep 1876459 = 2814689) B2814689
theorem B3744575 : Blo 1108626 3744575 := bstep (se 1 (by rfl) ⟨2808431, by rfl⟩ : syracuseStep 3744575 = 5616863) B5616863
theorem B72000413 : Blo 1108626 72000413 := bstep (se 3 (by rfl) ⟨13500077, by rfl⟩ : syracuseStep 72000413 = 27000155) B27000155
theorem B3745439 : Blo 1108626 3745439 := bstep (se 1 (by rfl) ⟨2809079, by rfl⟩ : syracuseStep 3745439 = 5618159) B5618159
theorem B3745979 : Blo 1108626 3745979 := bstep (se 1 (by rfl) ⟨2809484, by rfl⟩ : syracuseStep 3745979 = 5618969) B5618969
theorem B2370401 : Blo 1108626 2370401 := bstep (se 2 (by rfl) ⟨888900, by rfl⟩ : syracuseStep 2370401 = 1777801) B1777801
theorem B1583975 : Blo 1108626 1583975 := bstep (se 1 (by rfl) ⟨1187981, by rfl⟩ : syracuseStep 1583975 = 2375963) B2375963
theorem B14232449 : Blo 1108626 14232449 := bstep (se 2 (by rfl) ⟨5337168, by rfl⟩ : syracuseStep 14232449 = 10674337) B10674337
theorem B4500839 : Blo 1108626 4500839 := bstep (se 1 (by rfl) ⟨3375629, by rfl⟩ : syracuseStep 4500839 = 6751259) B6751259
theorem B6008339 : Blo 1108626 6008339 := bstep (se 1 (by rfl) ⟨4506254, by rfl⟩ : syracuseStep 6008339 = 9012509) B9012509
theorem B3747815 : Blo 1108626 3747815 := bstep (se 1 (by rfl) ⟨2810861, by rfl⟩ : syracuseStep 3747815 = 5621723) B5621723
theorem B2503259 : Blo 1108626 2503259 := bstep (se 1 (by rfl) ⟨1877444, by rfl⟩ : syracuseStep 2503259 = 3754889) B3754889
theorem B3748679 : Blo 1108626 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B16233371 : Blo 1108626 16233371 := bstep (se 1 (by rfl) ⟨12175028, by rfl⟩ : syracuseStep 16233371 = 24350057) B24350057
theorem B3749327 : Blo 1108626 3749327 := bstep (se 1 (by rfl) ⟨2811995, by rfl⟩ : syracuseStep 3749327 = 5623991) B5623991
theorem B9484199 : Blo 1108626 9484199 := bstep (se 1 (by rfl) ⟨7113149, by rfl⟩ : syracuseStep 9484199 = 14226299) B14226299
theorem B7223815 : Blo 1108626 7223815 := bstep (se 1 (by rfl) ⟨5417861, by rfl⟩ : syracuseStep 7223815 = 10835723) B10835723
theorem B2375561 : Blo 1108626 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B9617449 : Blo 1108626 9617449 := bstep (se 2 (by rfl) ⟨3606543, by rfl⟩ : syracuseStep 9617449 = 7213087) B7213087
theorem B1425479 : Blo 1108626 1425479 := bstep (se 1 (by rfl) ⟨1069109, by rfl⟩ : syracuseStep 1425479 = 2138219) B2138219
theorem B3752135 : Blo 1108626 3752135 := bstep (se 1 (by rfl) ⟨2814101, by rfl⟩ : syracuseStep 3752135 = 5628203) B5628203
theorem B19251593 : Blo 1108626 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B4211311 : Blo 1108626 4211311 := bstep (se 1 (by rfl) ⟨3158483, by rfl⟩ : syracuseStep 4211311 = 6316967) B6316967
theorem B3753215 : Blo 1108626 3753215 := bstep (se 1 (by rfl) ⟨2814911, by rfl⟩ : syracuseStep 3753215 = 5629823) B5629823
theorem B8538155 : Blo 1108626 8538155 := bstep (se 1 (by rfl) ⟨6403616, by rfl⟩ : syracuseStep 8538155 = 12807233) B12807233
theorem B4737163 : Blo 1108626 4737163 := bstep (se 1 (by rfl) ⟨3552872, by rfl⟩ : syracuseStep 4737163 = 7105745) B7105745
theorem B4737487 : Blo 1108626 4737487 := bstep (se 1 (by rfl) ⟨3553115, by rfl⟩ : syracuseStep 4737487 = 7106231) B7106231
theorem B28461617 : Blo 1108626 28461617 := bstep (se 2 (by rfl) ⟨10673106, by rfl⟩ : syracuseStep 28461617 = 21346213) B21346213
theorem B8441819 : Blo 1108626 8441819 := bstep (se 1 (by rfl) ⟨6331364, by rfl⟩ : syracuseStep 8441819 = 12662729) B12662729
theorem B5328865 : Blo 1108626 5328865 := bstep (se 2 (by rfl) ⟨1998324, by rfl⟩ : syracuseStep 5328865 = 3996649) B3996649
theorem B32068223 : Blo 1108626 32068223 := bstep (se 1 (by rfl) ⟨24051167, by rfl⟩ : syracuseStep 32068223 = 48102335) B48102335
theorem B5625773 : Blo 1108626 5625773 := bstep (se 3 (by rfl) ⟨1054832, by rfl⟩ : syracuseStep 5625773 = 2109665) B2109665
theorem B6838319 : Blo 1108626 6838319 := bstep (se 1 (by rfl) ⟨5128739, by rfl⟩ : syracuseStep 6838319 = 10257479) B10257479
theorem B9623719 : Blo 1108626 9623719 := bstep (se 1 (by rfl) ⟨7217789, by rfl⟩ : syracuseStep 9623719 = 14435579) B14435579
theorem B12802981 : Blo 1108626 12802981 := bstep (se 4 (by rfl) ⟨1200279, by rfl⟩ : syracuseStep 12802981 = 2400559) B2400559
theorem B12639401 : Blo 1108626 12639401 := bstep (se 2 (by rfl) ⟨4739775, by rfl⟩ : syracuseStep 12639401 = 9479551) B9479551
theorem B24337925 : Blo 1108626 24337925 := bstep (se 4 (by rfl) ⟨2281680, by rfl⟩ : syracuseStep 24337925 = 4563361) B4563361
theorem B11394715 : Blo 1108626 11394715 := bstep (se 1 (by rfl) ⟨8546036, by rfl⟩ : syracuseStep 11394715 = 17092073) B17092073
theorem B10149797 : Blo 1108626 10149797 := bstep (se 4 (by rfl) ⟨951543, by rfl⟩ : syracuseStep 10149797 = 1903087) B1903087
theorem B1663007 : Blo 1108626 1663007 := bstep (se 1 (by rfl) ⟨1247255, by rfl⟩ : syracuseStep 1663007 = 2494511) B2494511
theorem B1663259 : Blo 1108626 1663259 := bstep (se 1 (by rfl) ⟨1247444, by rfl⟩ : syracuseStep 1663259 = 2494889) B2494889
theorem B1663535 : Blo 1108626 1663535 := bstep (se 1 (by rfl) ⟨1247651, by rfl⟩ : syracuseStep 1663535 = 2495303) B2495303
theorem B2810983 : Blo 1108626 2810983 := bstep (se 1 (by rfl) ⟨2108237, by rfl⟩ : syracuseStep 2810983 = 4216475) B4216475
theorem B1664159 : Blo 1108626 1664159 := bstep (se 1 (by rfl) ⟨1248119, by rfl⟩ : syracuseStep 1664159 = 2496239) B2496239
theorem B8447651 : Blo 1108626 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B1665065 : Blo 1108626 1665065 := bstep (se 2 (by rfl) ⟨624399, by rfl⟩ : syracuseStep 1665065 = 1248799) B1248799
theorem B1665407 : Blo 1108626 1665407 := bstep (se 1 (by rfl) ⟨1249055, by rfl⟩ : syracuseStep 1665407 = 2498111) B2498111
theorem B2812553 : Blo 1108626 2812553 := bstep (se 2 (by rfl) ⟨1054707, by rfl⟩ : syracuseStep 2812553 = 2109415) B2109415
theorem B1665863 : Blo 1108626 1665863 := bstep (se 1 (by rfl) ⟨1249397, by rfl⟩ : syracuseStep 1665863 = 2498795) B2498795
theorem B1109083 : Blo 1108626 1109083 := bstep (se 1 (by rfl) ⟨831812, by rfl⟩ : syracuseStep 1109083 = 1663625) B1663625
theorem B5336441 : Blo 1108626 5336441 := bstep (se 2 (by rfl) ⟨2001165, by rfl⟩ : syracuseStep 5336441 = 4002331) B4002331
theorem B1666559 : Blo 1108626 1666559 := bstep (se 1 (by rfl) ⟨1249919, by rfl⟩ : syracuseStep 1666559 = 2499839) B2499839
theorem B1666607 : Blo 1108626 1666607 := bstep (se 1 (by rfl) ⟨1249955, by rfl⟩ : syracuseStep 1666607 = 2499911) B2499911
theorem B2813687 : Blo 1108626 2813687 := bstep (se 1 (by rfl) ⟨2110265, by rfl⟩ : syracuseStep 2813687 = 4220531) B4220531
theorem B1109787 : Blo 1108626 1109787 := bstep (se 1 (by rfl) ⟨832340, by rfl⟩ : syracuseStep 1109787 = 1664681) B1664681
theorem B27782939 : Blo 1108626 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B7106383 : Blo 1108626 7106383 := bstep (se 1 (by rfl) ⟨5329787, by rfl⟩ : syracuseStep 7106383 = 10659575) B10659575
theorem B1109851 : Blo 1108626 1109851 := bstep (se 1 (by rfl) ⟨832388, by rfl⟩ : syracuseStep 1109851 = 1664777) B1664777
theorem B7598123 : Blo 1108626 7598123 := bstep (se 1 (by rfl) ⟨5698592, by rfl⟩ : syracuseStep 7598123 = 11397185) B11397185
theorem B1110183 : Blo 1108626 1110183 := bstep (se 1 (by rfl) ⟨832637, by rfl⟩ : syracuseStep 1110183 = 1665275) B1665275
theorem B1110267 : Blo 1108626 1110267 := bstep (se 1 (by rfl) ⟨832700, by rfl⟩ : syracuseStep 1110267 = 1665401) B1665401
theorem B1667711 : Blo 1108626 1667711 := bstep (se 1 (by rfl) ⟨1250783, by rfl⟩ : syracuseStep 1667711 = 2501567) B2501567
theorem B7107385 : Blo 1108626 7107385 := bstep (se 2 (by rfl) ⟨2665269, by rfl⟩ : syracuseStep 7107385 = 5330539) B5330539
theorem B1111067 : Blo 1108626 1111067 := bstep (se 1 (by rfl) ⟨833300, by rfl⟩ : syracuseStep 1111067 = 1666601) B1666601
theorem B1111167 : Blo 1108626 1111167 := bstep (se 1 (by rfl) ⟨833375, by rfl⟩ : syracuseStep 1111167 = 1666751) B1666751
theorem B1668233 : Blo 1108626 1668233 := bstep (se 2 (by rfl) ⟨625587, by rfl⟩ : syracuseStep 1668233 = 1251175) B1251175
theorem B1111199 : Blo 1108626 1111199 := bstep (se 1 (by rfl) ⟨833399, by rfl⟩ : syracuseStep 1111199 = 1666799) B1666799
theorem B1111423 : Blo 1108626 1111423 := bstep (se 1 (by rfl) ⟨833567, by rfl⟩ : syracuseStep 1111423 = 1667135) B1667135
theorem B1111487 : Blo 1108626 1111487 := bstep (se 1 (by rfl) ⟨833615, by rfl⟩ : syracuseStep 1111487 = 1667231) B1667231
theorem B1668815 : Blo 1108626 1668815 := bstep (se 1 (by rfl) ⟨1251611, by rfl⟩ : syracuseStep 1668815 = 2503223) B2503223
theorem B7698451 : Blo 1108626 7698451 := bstep (se 1 (by rfl) ⟨5773838, by rfl⟩ : syracuseStep 7698451 = 11547677) B11547677
theorem B9632027 : Blo 1108626 9632027 := bstep (se 1 (by rfl) ⟨7224020, by rfl⟩ : syracuseStep 9632027 = 14448041) B14448041
theorem B4751243 : Blo 1108626 4751243 := bstep (se 1 (by rfl) ⟨3563432, by rfl⟩ : syracuseStep 4751243 = 7126865) B7126865
theorem B3801277 : Blo 1108626 3801277 := bstep (se 3 (by rfl) ⟨712739, by rfl⟩ : syracuseStep 3801277 = 1425479) B1425479
theorem B25952993 : Blo 1108626 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B9504155 : Blo 1108626 9504155 := bstep (se 1 (by rfl) ⟨7128116, by rfl⟩ : syracuseStep 9504155 = 14256233) B14256233
theorem B18974411 : Blo 1108626 18974411 := bstep (se 1 (by rfl) ⟨14230808, by rfl⟩ : syracuseStep 18974411 = 28461617) B28461617
theorem B1247323 : Blo 1108626 1247323 := bstep (se 1 (by rfl) ⟨935492, by rfl⟩ : syracuseStep 1247323 = 1870985) B1870985
theorem B21957479 : Blo 1108626 21957479 := bstep (se 1 (by rfl) ⟨16468109, by rfl⟩ : syracuseStep 21957479 = 32936219) B32936219
theorem B108138401 : Blo 1108626 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B4558879 : Blo 1108626 4558879 := bstep (se 1 (by rfl) ⟨3419159, by rfl⟩ : syracuseStep 4558879 = 6838319) B6838319
theorem B2495231 : Blo 1108626 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B8426267 : Blo 1108626 8426267 := bstep (se 1 (by rfl) ⟨6319700, by rfl⟩ : syracuseStep 8426267 = 12639401) B12639401
theorem B16225283 : Blo 1108626 16225283 := bstep (se 1 (by rfl) ⟨12168962, by rfl⟩ : syracuseStep 16225283 = 24337925) B24337925
theorem B9475177 : Blo 1108626 9475177 := bstep (se 2 (by rfl) ⟨3553191, by rfl⟩ : syracuseStep 9475177 = 7106383) B7106383
theorem B2495951 : Blo 1108626 2495951 := bstep (se 1 (by rfl) ⟨1871963, by rfl⟩ : syracuseStep 2495951 = 3743927) B3743927
theorem B2496383 : Blo 1108626 2496383 := bstep (se 1 (by rfl) ⟨1872287, by rfl⟩ : syracuseStep 2496383 = 3744575) B3744575
theorem B9476513 : Blo 1108626 9476513 := bstep (se 2 (by rfl) ⟨3553692, by rfl⟩ : syracuseStep 9476513 = 7107385) B7107385
theorem B2496959 : Blo 1108626 2496959 := bstep (se 1 (by rfl) ⟨1872719, by rfl⟩ : syracuseStep 2496959 = 3745439) B3745439
theorem B2497319 : Blo 1108626 2497319 := bstep (se 1 (by rfl) ⟨1872989, by rfl⟩ : syracuseStep 2497319 = 3745979) B3745979
theorem B1875035 : Blo 1108626 1875035 := bstep (se 1 (by rfl) ⟨1406276, by rfl⟩ : syracuseStep 1875035 = 2812553) B2812553
theorem B2497697 : Blo 1108626 2497697 := bstep (se 2 (by rfl) ⟨936636, by rfl⟩ : syracuseStep 2497697 = 1873273) B1873273
theorem B1580267 : Blo 1108626 1580267 := bstep (se 1 (by rfl) ⟨1185200, by rfl⟩ : syracuseStep 1580267 = 2370401) B2370401
theorem B4005559 : Blo 1108626 4005559 := bstep (se 1 (by rfl) ⟨3004169, by rfl⟩ : syracuseStep 4005559 = 6008339) B6008339
theorem B1875791 : Blo 1108626 1875791 := bstep (se 1 (by rfl) ⟨1406843, by rfl⟩ : syracuseStep 1875791 = 2813687) B2813687
theorem B18521959 : Blo 1108626 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B2498543 : Blo 1108626 2498543 := bstep (se 1 (by rfl) ⟨1873907, by rfl⟩ : syracuseStep 2498543 = 3747815) B3747815
theorem B10264601 : Blo 1108626 10264601 := bstep (se 2 (by rfl) ⟨3849225, by rfl⟩ : syracuseStep 10264601 = 7698451) B7698451
theorem B2499119 : Blo 1108626 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B10822247 : Blo 1108626 10822247 := bstep (se 1 (by rfl) ⟨8116685, by rfl⟩ : syracuseStep 10822247 = 16233371) B16233371
theorem B2499551 : Blo 1108626 2499551 := bstep (se 1 (by rfl) ⟨1874663, by rfl⟩ : syracuseStep 2499551 = 3749327) B3749327
theorem B2369513 : Blo 1108626 2369513 := bstep (se 2 (by rfl) ⟨888567, by rfl⟩ : syracuseStep 2369513 = 1777135) B1777135
theorem B1583707 : Blo 1108626 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B12823265 : Blo 1108626 12823265 := bstep (se 2 (by rfl) ⟨4808724, by rfl⟩ : syracuseStep 12823265 = 9617449) B9617449
theorem B2501423 : Blo 1108626 2501423 := bstep (se 1 (by rfl) ⟨1876067, by rfl⟩ : syracuseStep 2501423 = 3752135) B3752135
theorem B2501945 : Blo 1108626 2501945 := bstep (se 2 (by rfl) ⟨938229, by rfl⟩ : syracuseStep 2501945 = 1876459) B1876459
theorem B5615081 : Blo 1108626 5615081 := bstep (se 2 (by rfl) ⟨2105655, by rfl⟩ : syracuseStep 5615081 = 4211311) B4211311
theorem B2502143 : Blo 1108626 2502143 := bstep (se 1 (by rfl) ⟨1876607, by rfl⟩ : syracuseStep 2502143 = 3753215) B3753215
theorem B3747977 : Blo 1108626 3747977 := bstep (se 2 (by rfl) ⟨1405491, by rfl⟩ : syracuseStep 3747977 = 2810983) B2810983
theorem B21378815 : Blo 1108626 21378815 := bstep (se 1 (by rfl) ⟨16034111, by rfl⟩ : syracuseStep 21378815 = 32068223) B32068223
theorem B4503367 : Blo 1108626 4503367 := bstep (se 1 (by rfl) ⟨3377525, by rfl⟩ : syracuseStep 4503367 = 6755051) B6755051
theorem B3750515 : Blo 1108626 3750515 := bstep (se 1 (by rfl) ⟨2812886, by rfl⟩ : syracuseStep 3750515 = 5625773) B5625773
theorem B9488299 : Blo 1108626 9488299 := bstep (se 1 (by rfl) ⟨7116224, by rfl⟩ : syracuseStep 9488299 = 14232449) B14232449
theorem B3000559 : Blo 1108626 3000559 := bstep (se 1 (by rfl) ⟨2250419, by rfl⟩ : syracuseStep 3000559 = 4500839) B4500839
theorem B3557627 : Blo 1108626 3557627 := bstep (se 1 (by rfl) ⟨2668220, by rfl⟩ : syracuseStep 3557627 = 5336441) B5336441
theorem B5065415 : Blo 1108626 5065415 := bstep (se 1 (by rfl) ⟨3799061, by rfl⟩ : syracuseStep 5065415 = 7598123) B7598123
theorem B12831625 : Blo 1108626 12831625 := bstep (se 2 (by rfl) ⟨4811859, by rfl⟩ : syracuseStep 12831625 = 9623719) B9623719
theorem B15192953 : Blo 1108626 15192953 := bstep (se 2 (by rfl) ⟨5697357, by rfl⟩ : syracuseStep 15192953 = 11394715) B11394715
theorem B3167495 : Blo 1108626 3167495 := bstep (se 1 (by rfl) ⟨2375621, by rfl⟩ : syracuseStep 3167495 = 4751243) B4751243
theorem B3167711 : Blo 1108626 3167711 := bstep (se 1 (by rfl) ⟨2375783, by rfl⟩ : syracuseStep 3167711 = 4751567) B4751567
theorem B12834395 : Blo 1108626 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B16013351 : Blo 1108626 16013351 := bstep (se 1 (by rfl) ⟨12010013, by rfl⟩ : syracuseStep 16013351 = 24020027) B24020027
theorem B4217447 : Blo 1108626 4217447 := bstep (se 1 (by rfl) ⟨3163085, by rfl⟩ : syracuseStep 4217447 = 6326171) B6326171
theorem B5692103 : Blo 1108626 5692103 := bstep (se 1 (by rfl) ⟨4269077, by rfl⟩ : syracuseStep 5692103 = 8538155) B8538155
theorem B4741895 : Blo 1108626 4741895 := bstep (se 1 (by rfl) ⟨3556421, by rfl⟩ : syracuseStep 4741895 = 7112843) B7112843
theorem B5069791 : Blo 1108626 5069791 := bstep (se 1 (by rfl) ⟨3802343, by rfl⟩ : syracuseStep 5069791 = 7604687) B7604687
theorem B5627879 : Blo 1108626 5627879 := bstep (se 1 (by rfl) ⟨4220909, by rfl⟩ : syracuseStep 5627879 = 8441819) B8441819
theorem B6316217 : Blo 1108626 6316217 := bstep (se 2 (by rfl) ⟨2368581, by rfl⟩ : syracuseStep 6316217 = 4737163) B4737163
theorem B1663199 : Blo 1108626 1663199 := bstep (se 1 (by rfl) ⟨1247399, by rfl⟩ : syracuseStep 1663199 = 2494799) B2494799
theorem B6316649 : Blo 1108626 6316649 := bstep (se 2 (by rfl) ⟨2368743, by rfl⟩ : syracuseStep 6316649 = 4737487) B4737487
theorem B5694077 : Blo 1108626 5694077 := bstep (se 3 (by rfl) ⟨1067639, by rfl⟩ : syracuseStep 5694077 = 2135279) B2135279
theorem B1663739 : Blo 1108626 1663739 := bstep (se 1 (by rfl) ⟨1247804, by rfl⟩ : syracuseStep 1663739 = 2495609) B2495609
theorem B1664027 : Blo 1108626 1664027 := bstep (se 1 (by rfl) ⟨1248020, by rfl⟩ : syracuseStep 1664027 = 2496041) B2496041
theorem B7103771 : Blo 1108626 7103771 := bstep (se 1 (by rfl) ⟨5327828, by rfl⟩ : syracuseStep 7103771 = 10655657) B10655657
theorem B1664489 : Blo 1108626 1664489 := bstep (se 2 (by rfl) ⟨624183, by rfl⟩ : syracuseStep 1664489 = 1248367) B1248367
theorem B4221031 : Blo 1108626 4221031 := bstep (se 1 (by rfl) ⟨3165773, by rfl⟩ : syracuseStep 4221031 = 6331547) B6331547
theorem B7105153 : Blo 1108626 7105153 := bstep (se 2 (by rfl) ⟨2664432, by rfl⟩ : syracuseStep 7105153 = 5328865) B5328865
theorem B1108671 : Blo 1108626 1108671 := bstep (se 1 (by rfl) ⟨831503, by rfl⟩ : syracuseStep 1108671 = 1663007) B1663007
theorem B1141499 : Blo 1108626 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B1108839 : Blo 1108626 1108839 := bstep (se 1 (by rfl) ⟨831629, by rfl⟩ : syracuseStep 1108839 = 1663259) B1663259
theorem B1109023 : Blo 1108626 1109023 := bstep (se 1 (by rfl) ⟨831767, by rfl⟩ : syracuseStep 1109023 = 1663535) B1663535
theorem B48000275 : Blo 1108626 48000275 := bstep (se 1 (by rfl) ⟨36000206, by rfl⟩ : syracuseStep 48000275 = 72000413) B72000413
theorem B1109439 : Blo 1108626 1109439 := bstep (se 1 (by rfl) ⟨832079, by rfl⟩ : syracuseStep 1109439 = 1664159) B1664159
theorem B5631767 : Blo 1108626 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B1110043 : Blo 1108626 1110043 := bstep (se 1 (by rfl) ⟨832532, by rfl⟩ : syracuseStep 1110043 = 1665065) B1665065
theorem B1110271 : Blo 1108626 1110271 := bstep (se 1 (by rfl) ⟨832703, by rfl⟩ : syracuseStep 1110271 = 1665407) B1665407
theorem B1110575 : Blo 1108626 1110575 := bstep (se 1 (by rfl) ⟨832931, by rfl⟩ : syracuseStep 1110575 = 1665863) B1665863
theorem B4223933 : Blo 1108626 4223933 := bstep (se 3 (by rfl) ⟨791987, by rfl⟩ : syracuseStep 4223933 = 1583975) B1583975
theorem B1111039 : Blo 1108626 1111039 := bstep (se 1 (by rfl) ⟨833279, by rfl⟩ : syracuseStep 1111039 = 1666559) B1666559
theorem B1111071 : Blo 1108626 1111071 := bstep (se 1 (by rfl) ⟨833303, by rfl⟩ : syracuseStep 1111071 = 1666607) B1666607
theorem B1668839 : Blo 1108626 1668839 := bstep (se 1 (by rfl) ⟨1251629, by rfl⟩ : syracuseStep 1668839 = 2503259) B2503259
theorem B1111807 : Blo 1108626 1111807 := bstep (se 1 (by rfl) ⟨833855, by rfl⟩ : syracuseStep 1111807 = 1667711) B1667711
theorem B9631753 : Blo 1108626 9631753 := bstep (se 2 (by rfl) ⟨3611907, by rfl⟩ : syracuseStep 9631753 = 7223815) B7223815
theorem B1112155 : Blo 1108626 1112155 := bstep (se 1 (by rfl) ⟨834116, by rfl⟩ : syracuseStep 1112155 = 1668233) B1668233
theorem B1112543 : Blo 1108626 1112543 := bstep (se 1 (by rfl) ⟨834407, by rfl⟩ : syracuseStep 1112543 = 1668815) B1668815
theorem B17070641 : Blo 1108626 17070641 := bstep (se 2 (by rfl) ⟨6401490, by rfl⟩ : syracuseStep 17070641 = 12802981) B12802981
theorem B6322799 : Blo 1108626 6322799 := bstep (se 1 (by rfl) ⟨4742099, by rfl⟩ : syracuseStep 6322799 = 9484199) B9484199
theorem B6421351 : Blo 1108626 6421351 := bstep (se 1 (by rfl) ⟨4816013, by rfl⟩ : syracuseStep 6421351 = 9632027) B9632027
theorem B27066125 : Blo 1108626 27066125 := bstep (se 3 (by rfl) ⟨5074898, by rfl⟩ : syracuseStep 27066125 = 10149797) B10149797
theorem B17301995 : Blo 1108626 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B12649607 : Blo 1108626 12649607 := bstep (se 1 (by rfl) ⟨9487205, by rfl⟩ : syracuseStep 12649607 = 18974411) B18974411
theorem B3376943 : Blo 1108626 3376943 := bstep (se 1 (by rfl) ⟨2532707, by rfl⟩ : syracuseStep 3376943 = 5065415) B5065415
theorem B12651065 : Blo 1108626 12651065 := bstep (se 2 (by rfl) ⟨4744149, by rfl⟩ : syracuseStep 12651065 = 9488299) B9488299
theorem B72092267 : Blo 1108626 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B4000745 : Blo 1108626 4000745 := bstep (se 2 (by rfl) ⟨1500279, by rfl⟩ : syracuseStep 4000745 = 3000559) B3000559
theorem B10128635 : Blo 1108626 10128635 := bstep (se 1 (by rfl) ⟨7596476, by rfl⟩ : syracuseStep 10128635 = 15192953) B15192953
theorem B9473537 : Blo 1108626 9473537 := bstep (se 2 (by rfl) ⟨3552576, by rfl⟩ : syracuseStep 9473537 = 7105153) B7105153
theorem B8556263 : Blo 1108626 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B17108833 : Blo 1108626 17108833 := bstep (se 2 (by rfl) ⟨6415812, by rfl⟩ : syracuseStep 17108833 = 12831625) B12831625
theorem B1250023 : Blo 1108626 1250023 := bstep (se 1 (by rfl) ⟨937517, by rfl⟩ : syracuseStep 1250023 = 1875035) B1875035
theorem B1250527 : Blo 1108626 1250527 := bstep (se 1 (by rfl) ⟨937895, by rfl⟩ : syracuseStep 1250527 = 1875791) B1875791
theorem B7214831 : Blo 1108626 7214831 := bstep (se 1 (by rfl) ⟨5411123, by rfl⟩ : syracuseStep 7214831 = 10822247) B10822247
theorem B1579675 : Blo 1108626 1579675 := bstep (se 1 (by rfl) ⟨1184756, by rfl⟩ : syracuseStep 1579675 = 2369513) B2369513
theorem B3743387 : Blo 1108626 3743387 := bstep (se 1 (by rfl) ⟨2807540, by rfl⟩ : syracuseStep 3743387 = 5615081) B5615081
theorem B6004489 : Blo 1108626 6004489 := bstep (se 2 (by rfl) ⟨2251683, by rfl⟩ : syracuseStep 6004489 = 4503367) B4503367
theorem B2498651 : Blo 1108626 2498651 := bstep (se 1 (by rfl) ⟨1873988, by rfl⟩ : syracuseStep 2498651 = 3747977) B3747977
theorem B8561801 : Blo 1108626 8561801 := bstep (se 2 (by rfl) ⟨3210675, by rfl⟩ : syracuseStep 8561801 = 6421351) B6421351
theorem B6759721 : Blo 1108626 6759721 := bstep (se 2 (by rfl) ⟨2534895, by rfl⟩ : syracuseStep 6759721 = 5069791) B5069791
theorem B11380427 : Blo 1108626 11380427 := bstep (se 1 (by rfl) ⟨8535320, by rfl⟩ : syracuseStep 11380427 = 17070641) B17070641
theorem B2500343 : Blo 1108626 2500343 := bstep (se 1 (by rfl) ⟨1875257, by rfl⟩ : syracuseStep 2500343 = 3750515) B3750515
theorem B6336103 : Blo 1108626 6336103 := bstep (se 1 (by rfl) ⟨4752077, by rfl⟩ : syracuseStep 6336103 = 9504155) B9504155
theorem B2371751 : Blo 1108626 2371751 := bstep (se 1 (by rfl) ⟨1778813, by rfl⟩ : syracuseStep 2371751 = 3557627) B3557627
theorem B15184205 : Blo 1108626 15184205 := bstep (se 3 (by rfl) ⟨2847038, by rfl⟩ : syracuseStep 15184205 = 5694077) B5694077
theorem B43267421 : Blo 1108626 43267421 := bstep (se 3 (by rfl) ⟨8112641, by rfl⟩ : syracuseStep 43267421 = 16225283) B16225283
theorem B5617511 : Blo 1108626 5617511 := bstep (se 1 (by rfl) ⟨4213133, by rfl⟩ : syracuseStep 5617511 = 8426267) B8426267
theorem B2111609 : Blo 1108626 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B2111663 : Blo 1108626 2111663 := bstep (se 1 (by rfl) ⟨1583747, by rfl⟩ : syracuseStep 2111663 = 3167495) B3167495
theorem B2111807 : Blo 1108626 2111807 := bstep (se 1 (by rfl) ⟨1583855, by rfl⟩ : syracuseStep 2111807 = 3167711) B3167711
theorem B3161263 : Blo 1108626 3161263 := bstep (se 1 (by rfl) ⟨2370947, by rfl⟩ : syracuseStep 3161263 = 4741895) B4741895
theorem B3751919 : Blo 1108626 3751919 := bstep (se 1 (by rfl) ⟨2813939, by rfl⟩ : syracuseStep 3751919 = 5627879) B5627879
theorem B6078505 : Blo 1108626 6078505 := bstep (se 2 (by rfl) ⟨2279439, by rfl⟩ : syracuseStep 6078505 = 4558879) B4558879
theorem B4210811 : Blo 1108626 4210811 := bstep (se 1 (by rfl) ⟨3158108, by rfl⟩ : syracuseStep 4210811 = 6316217) B6316217
theorem B4211099 : Blo 1108626 4211099 := bstep (se 1 (by rfl) ⟨3158324, by rfl⟩ : syracuseStep 4211099 = 6316649) B6316649
theorem B4735847 : Blo 1108626 4735847 := bstep (se 1 (by rfl) ⟨3551885, by rfl⟩ : syracuseStep 4735847 = 7103771) B7103771
theorem B12633569 : Blo 1108626 12633569 := bstep (se 2 (by rfl) ⟨4737588, by rfl⟩ : syracuseStep 12633569 = 9475177) B9475177
theorem B32000183 : Blo 1108626 32000183 := bstep (se 1 (by rfl) ⟨24000137, by rfl⟩ : syracuseStep 32000183 = 48000275) B48000275
theorem B3754511 : Blo 1108626 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B4214045 : Blo 1108626 4214045 := bstep (se 3 (by rfl) ⟨790133, by rfl⟩ : syracuseStep 4214045 = 1580267) B1580267
theorem B4215199 : Blo 1108626 4215199 := bstep (se 1 (by rfl) ⟨3161399, by rfl⟩ : syracuseStep 4215199 = 6322799) B6322799
theorem B24695945 : Blo 1108626 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B18044083 : Blo 1108626 18044083 := bstep (se 1 (by rfl) ⟨13533062, by rfl⟩ : syracuseStep 18044083 = 27066125) B27066125
theorem B51369349 : Blo 1108626 51369349 := bstep (se 4 (by rfl) ⟨4815876, by rfl⟩ : syracuseStep 51369349 = 9631753) B9631753
theorem B5068369 : Blo 1108626 5068369 := bstep (se 2 (by rfl) ⟨1900638, by rfl⟩ : syracuseStep 5068369 = 3801277) B3801277
theorem B14638319 : Blo 1108626 14638319 := bstep (se 1 (by rfl) ⟨10978739, by rfl⟩ : syracuseStep 14638319 = 21957479) B21957479
theorem B1663097 : Blo 1108626 1663097 := bstep (se 2 (by rfl) ⟨623661, by rfl⟩ : syracuseStep 1663097 = 1247323) B1247323
theorem B5628041 : Blo 1108626 5628041 := bstep (se 2 (by rfl) ⟨2110515, by rfl⟩ : syracuseStep 5628041 = 4221031) B4221031
theorem B1663487 : Blo 1108626 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B1663967 : Blo 1108626 1663967 := bstep (se 1 (by rfl) ⟨1247975, by rfl⟩ : syracuseStep 1663967 = 2495951) B2495951
theorem B1664255 : Blo 1108626 1664255 := bstep (se 1 (by rfl) ⟨1248191, by rfl⟩ : syracuseStep 1664255 = 2496383) B2496383
theorem B10675567 : Blo 1108626 10675567 := bstep (se 1 (by rfl) ⟨8006675, by rfl⟩ : syracuseStep 10675567 = 16013351) B16013351
theorem B6317675 : Blo 1108626 6317675 := bstep (se 1 (by rfl) ⟨4738256, by rfl⟩ : syracuseStep 6317675 = 9476513) B9476513
theorem B1664639 : Blo 1108626 1664639 := bstep (se 1 (by rfl) ⟨1248479, by rfl⟩ : syracuseStep 1664639 = 2496959) B2496959
theorem B2811631 : Blo 1108626 2811631 := bstep (se 1 (by rfl) ⟨2108723, by rfl⟩ : syracuseStep 2811631 = 4217447) B4217447
theorem B3794735 : Blo 1108626 3794735 := bstep (se 1 (by rfl) ⟨2846051, by rfl⟩ : syracuseStep 3794735 = 5692103) B5692103
theorem B1664879 : Blo 1108626 1664879 := bstep (se 1 (by rfl) ⟨1248659, by rfl⟩ : syracuseStep 1664879 = 2497319) B2497319
theorem B1665131 : Blo 1108626 1665131 := bstep (se 1 (by rfl) ⟨1248848, by rfl⟩ : syracuseStep 1665131 = 2497697) B2497697
theorem B1665695 : Blo 1108626 1665695 := bstep (se 1 (by rfl) ⟨1249271, by rfl⟩ : syracuseStep 1665695 = 2498543) B2498543
theorem B6843067 : Blo 1108626 6843067 := bstep (se 1 (by rfl) ⟨5132300, by rfl⟩ : syracuseStep 6843067 = 10264601) B10264601
theorem B1108799 : Blo 1108626 1108799 := bstep (se 1 (by rfl) ⟨831599, by rfl⟩ : syracuseStep 1108799 = 1663199) B1663199
theorem B1666079 : Blo 1108626 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B1109159 : Blo 1108626 1109159 := bstep (se 1 (by rfl) ⟨831869, by rfl⟩ : syracuseStep 1109159 = 1663739) B1663739
theorem B1666367 : Blo 1108626 1666367 := bstep (se 1 (by rfl) ⟨1249775, by rfl⟩ : syracuseStep 1666367 = 2499551) B2499551
theorem B1109351 : Blo 1108626 1109351 := bstep (se 1 (by rfl) ⟨832013, by rfl⟩ : syracuseStep 1109351 = 1664027) B1664027
theorem B1109659 : Blo 1108626 1109659 := bstep (se 1 (by rfl) ⟨832244, by rfl⟩ : syracuseStep 1109659 = 1664489) B1664489
theorem B8548843 : Blo 1108626 8548843 := bstep (se 1 (by rfl) ⟨6411632, by rfl⟩ : syracuseStep 8548843 = 12823265) B12823265
theorem B1667615 : Blo 1108626 1667615 := bstep (se 1 (by rfl) ⟨1250711, by rfl⟩ : syracuseStep 1667615 = 2501423) B2501423
theorem B3043997 : Blo 1108626 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B1667963 : Blo 1108626 1667963 := bstep (se 1 (by rfl) ⟨1250972, by rfl⟩ : syracuseStep 1667963 = 2501945) B2501945
theorem B1668095 : Blo 1108626 1668095 := bstep (se 1 (by rfl) ⟨1251071, by rfl⟩ : syracuseStep 1668095 = 2502143) B2502143
theorem B2815955 : Blo 1108626 2815955 := bstep (se 1 (by rfl) ⟨2111966, by rfl⟩ : syracuseStep 2815955 = 4223933) B4223933
theorem B1112559 : Blo 1108626 1112559 := bstep (se 1 (by rfl) ⟨834419, by rfl⟩ : syracuseStep 1112559 = 1668839) B1668839
theorem B14252543 : Blo 1108626 14252543 := bstep (se 1 (by rfl) ⟨10689407, by rfl⟩ : syracuseStep 14252543 = 21378815) B21378815
theorem B5340745 : Blo 1108626 5340745 := bstep (se 2 (by rfl) ⟨2002779, by rfl⟩ : syracuseStep 5340745 = 4005559) B4005559
theorem B11534663 : Blo 1108626 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B8422379 : Blo 1108626 8422379 := bstep (se 1 (by rfl) ⟨6316784, by rfl⟩ : syracuseStep 8422379 = 12633569) B12633569
theorem B21333455 : Blo 1108626 21333455 := bstep (se 1 (by rfl) ⟨16000091, by rfl⟩ : syracuseStep 21333455 = 32000183) B32000183
theorem B9012961 : Blo 1108626 9012961 := bstep (se 2 (by rfl) ⟨3379860, by rfl⟩ : syracuseStep 9012961 = 6759721) B6759721
theorem B6752423 : Blo 1108626 6752423 := bstep (se 1 (by rfl) ⟨5064317, by rfl⟩ : syracuseStep 6752423 = 10128635) B10128635
theorem B5704175 : Blo 1108626 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B145985429 : Blo 1108626 145985429 := bstep (se 6 (by rfl) ⟨3421533, by rfl⟩ : syracuseStep 145985429 = 6843067) B6843067
theorem B2495591 : Blo 1108626 2495591 := bstep (se 1 (by rfl) ⟨1871693, by rfl⟩ : syracuseStep 2495591 = 3743387) B3743387
theorem B22811777 : Blo 1108626 22811777 := bstep (se 2 (by rfl) ⟨8554416, by rfl⟩ : syracuseStep 22811777 = 17108833) B17108833
theorem B24058777 : Blo 1108626 24058777 := bstep (se 2 (by rfl) ⟨9022041, by rfl⟩ : syracuseStep 24058777 = 18044083) B18044083
theorem B68492465 : Blo 1108626 68492465 := bstep (se 2 (by rfl) ⟨25684674, by rfl⟩ : syracuseStep 68492465 = 51369349) B51369349
theorem B6757825 : Blo 1108626 6757825 := bstep (se 2 (by rfl) ⟨2534184, by rfl⟩ : syracuseStep 6757825 = 5068369) B5068369
theorem B1581167 : Blo 1108626 1581167 := bstep (se 1 (by rfl) ⟨1185875, by rfl⟩ : syracuseStep 1581167 = 2371751) B2371751
theorem B2106233 : Blo 1108626 2106233 := bstep (se 2 (by rfl) ⟨789837, by rfl⟩ : syracuseStep 2106233 = 1579675) B1579675
theorem B28844947 : Blo 1108626 28844947 := bstep (se 1 (by rfl) ⟨21633710, by rfl⟩ : syracuseStep 28844947 = 43267421) B43267421
theorem B3745007 : Blo 1108626 3745007 := bstep (se 1 (by rfl) ⟨2808755, by rfl⟩ : syracuseStep 3745007 = 5617511) B5617511
theorem B1877303 : Blo 1108626 1877303 := bstep (se 1 (by rfl) ⟨1407977, by rfl⟩ : syracuseStep 1877303 = 2815955) B2815955
theorem B7120993 : Blo 1108626 7120993 := bstep (se 2 (by rfl) ⟨2670372, by rfl⟩ : syracuseStep 7120993 = 5340745) B5340745
theorem B8005985 : Blo 1108626 8005985 := bstep (se 2 (by rfl) ⟨3002244, by rfl⟩ : syracuseStep 8005985 = 6004489) B6004489
theorem B2501279 : Blo 1108626 2501279 := bstep (se 1 (by rfl) ⟨1875959, by rfl⟩ : syracuseStep 2501279 = 3751919) B3751919
theorem B8104673 : Blo 1108626 8104673 := bstep (se 2 (by rfl) ⟨3039252, by rfl⟩ : syracuseStep 8104673 = 6078505) B6078505
theorem B3157231 : Blo 1108626 3157231 := bstep (se 1 (by rfl) ⟨2367923, by rfl⟩ : syracuseStep 3157231 = 4735847) B4735847
theorem B8433071 : Blo 1108626 8433071 := bstep (se 1 (by rfl) ⟨6324803, by rfl⟩ : syracuseStep 8433071 = 12649607) B12649607
theorem B2503007 : Blo 1108626 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B8434043 : Blo 1108626 8434043 := bstep (se 1 (by rfl) ⟨6325532, by rfl⟩ : syracuseStep 8434043 = 12651065) B12651065
theorem B14234089 : Blo 1108626 14234089 := bstep (se 2 (by rfl) ⟨5337783, by rfl⟩ : syracuseStep 14234089 = 10675567) B10675567
theorem B2667163 : Blo 1108626 2667163 := bstep (se 1 (by rfl) ⟨2000372, by rfl⟩ : syracuseStep 2667163 = 4000745) B4000745
theorem B3748841 : Blo 1108626 3748841 := bstep (se 2 (by rfl) ⟨1405815, by rfl⟩ : syracuseStep 3748841 = 2811631) B2811631
theorem B16463963 : Blo 1108626 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B3752027 : Blo 1108626 3752027 := bstep (se 1 (by rfl) ⟨2814020, by rfl⟩ : syracuseStep 3752027 = 5628041) B5628041
theorem B5620265 : Blo 1108626 5620265 := bstep (se 2 (by rfl) ⟨2107599, by rfl⟩ : syracuseStep 5620265 = 4215199) B4215199
theorem B4211783 : Blo 1108626 4211783 := bstep (se 1 (by rfl) ⟨3158837, by rfl⟩ : syracuseStep 4211783 = 6317675) B6317675
theorem B7586951 : Blo 1108626 7586951 := bstep (se 1 (by rfl) ⟨5690213, by rfl⟩ : syracuseStep 7586951 = 11380427) B11380427
theorem B4215017 : Blo 1108626 4215017 := bstep (se 2 (by rfl) ⟨1580631, by rfl⟩ : syracuseStep 4215017 = 3161263) B3161263
theorem B2807207 : Blo 1108626 2807207 := bstep (se 1 (by rfl) ⟨2105405, by rfl⟩ : syracuseStep 2807207 = 4210811) B4210811
theorem B2807399 : Blo 1108626 2807399 := bstep (se 1 (by rfl) ⟨2105549, by rfl⟩ : syracuseStep 2807399 = 4211099) B4211099
theorem B2251295 : Blo 1108626 2251295 := bstep (se 1 (by rfl) ⟨1688471, by rfl⟩ : syracuseStep 2251295 = 3376943) B3376943
theorem B48061511 : Blo 1108626 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B2809363 : Blo 1108626 2809363 := bstep (se 1 (by rfl) ⟨2107022, by rfl⟩ : syracuseStep 2809363 = 4214045) B4214045
theorem B6315691 : Blo 1108626 6315691 := bstep (se 1 (by rfl) ⟨4736768, by rfl⟩ : syracuseStep 6315691 = 9473537) B9473537
theorem B22831469 : Blo 1108626 22831469 := bstep (se 3 (by rfl) ⟨4280900, by rfl⟩ : syracuseStep 22831469 = 8561801) B8561801
theorem B4809887 : Blo 1108626 4809887 := bstep (se 1 (by rfl) ⟨3607415, by rfl⟩ : syracuseStep 4809887 = 7214831) B7214831
theorem B10119293 : Blo 1108626 10119293 := bstep (se 3 (by rfl) ⟨1897367, by rfl⟩ : syracuseStep 10119293 = 3794735) B3794735
theorem B8448137 : Blo 1108626 8448137 := bstep (se 2 (by rfl) ⟨3168051, by rfl⟩ : syracuseStep 8448137 = 6336103) B6336103
theorem B9758879 : Blo 1108626 9758879 := bstep (se 1 (by rfl) ⟨7319159, by rfl⟩ : syracuseStep 9758879 = 14638319) B14638319
theorem B1665767 : Blo 1108626 1665767 := bstep (se 1 (by rfl) ⟨1249325, by rfl⟩ : syracuseStep 1665767 = 2498651) B2498651
theorem B1108731 : Blo 1108626 1108731 := bstep (se 1 (by rfl) ⟨831548, by rfl⟩ : syracuseStep 1108731 = 1663097) B1663097
theorem B5630957 : Blo 1108626 5630957 := bstep (se 3 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 5630957 = 2111609) B2111609
theorem B1108991 : Blo 1108626 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B11398457 : Blo 1108626 11398457 := bstep (se 2 (by rfl) ⟨4274421, by rfl⟩ : syracuseStep 11398457 = 8548843) B8548843
theorem B1109311 : Blo 1108626 1109311 := bstep (se 1 (by rfl) ⟨831983, by rfl⟩ : syracuseStep 1109311 = 1663967) B1663967
theorem B1109503 : Blo 1108626 1109503 := bstep (se 1 (by rfl) ⟨832127, by rfl⟩ : syracuseStep 1109503 = 1664255) B1664255
theorem B1666697 : Blo 1108626 1666697 := bstep (se 2 (by rfl) ⟨625011, by rfl⟩ : syracuseStep 1666697 = 1250023) B1250023
theorem B1109759 : Blo 1108626 1109759 := bstep (se 1 (by rfl) ⟨832319, by rfl⟩ : syracuseStep 1109759 = 1664639) B1664639
theorem B1666895 : Blo 1108626 1666895 := bstep (se 1 (by rfl) ⟨1250171, by rfl⟩ : syracuseStep 1666895 = 2500343) B2500343
theorem B1109919 : Blo 1108626 1109919 := bstep (se 1 (by rfl) ⟨832439, by rfl⟩ : syracuseStep 1109919 = 1664879) B1664879
theorem B1110087 : Blo 1108626 1110087 := bstep (se 1 (by rfl) ⟨832565, by rfl⟩ : syracuseStep 1110087 = 1665131) B1665131
theorem B1667369 : Blo 1108626 1667369 := bstep (se 2 (by rfl) ⟨625263, by rfl⟩ : syracuseStep 1667369 = 1250527) B1250527
theorem B1110463 : Blo 1108626 1110463 := bstep (se 1 (by rfl) ⟨832847, by rfl⟩ : syracuseStep 1110463 = 1665695) B1665695
theorem B1110719 : Blo 1108626 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B1110911 : Blo 1108626 1110911 := bstep (se 1 (by rfl) ⟨833183, by rfl⟩ : syracuseStep 1110911 = 1666367) B1666367
theorem B10122803 : Blo 1108626 10122803 := bstep (se 1 (by rfl) ⟨7592102, by rfl⟩ : syracuseStep 10122803 = 15184205) B15184205
theorem B1111743 : Blo 1108626 1111743 := bstep (se 1 (by rfl) ⟨833807, by rfl⟩ : syracuseStep 1111743 = 1667615) B1667615
theorem B2029331 : Blo 1108626 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B1111975 : Blo 1108626 1111975 := bstep (se 1 (by rfl) ⟨833981, by rfl⟩ : syracuseStep 1111975 = 1667963) B1667963
theorem B1112063 : Blo 1108626 1112063 := bstep (se 1 (by rfl) ⟨834047, by rfl⟩ : syracuseStep 1112063 = 1668095) B1668095
theorem B1407775 : Blo 1108626 1407775 := bstep (se 1 (by rfl) ⟨1055831, by rfl⟩ : syracuseStep 1407775 = 2111663) B2111663
theorem B1407871 : Blo 1108626 1407871 := bstep (se 1 (by rfl) ⟨1055903, by rfl⟩ : syracuseStep 1407871 = 2111807) B2111807
theorem B9501695 : Blo 1108626 9501695 := bstep (se 1 (by rfl) ⟨7126271, by rfl⟩ : syracuseStep 9501695 = 14252543) B14252543
theorem B14222303 : Blo 1108626 14222303 := bstep (se 1 (by rfl) ⟨10666727, by rfl⟩ : syracuseStep 14222303 = 21333455) B21333455
theorem B3802783 : Blo 1108626 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B97323619 : Blo 1108626 97323619 := bstep (se 1 (by rfl) ⟨72992714, by rfl⟩ : syracuseStep 97323619 = 145985429) B145985429
theorem B15207851 : Blo 1108626 15207851 := bstep (se 1 (by rfl) ⟨11405888, by rfl⟩ : syracuseStep 15207851 = 22811777) B22811777
theorem B1871471 : Blo 1108626 1871471 := bstep (se 1 (by rfl) ⟨1403603, by rfl⟩ : syracuseStep 1871471 = 2807207) B2807207
theorem B1871599 : Blo 1108626 1871599 := bstep (se 1 (by rfl) ⟨1403699, by rfl⟩ : syracuseStep 1871599 = 2807399) B2807399
theorem B5411549 : Blo 1108626 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B18978785 : Blo 1108626 18978785 := bstep (se 2 (by rfl) ⟨7117044, by rfl⟩ : syracuseStep 18978785 = 14234089) B14234089
theorem B2496671 : Blo 1108626 2496671 := bstep (se 1 (by rfl) ⟨1872503, by rfl⟩ : syracuseStep 2496671 = 3745007) B3745007
theorem B1251535 : Blo 1108626 1251535 := bstep (se 1 (by rfl) ⟨938651, by rfl⟩ : syracuseStep 1251535 = 1877303) B1877303
theorem B2499227 : Blo 1108626 2499227 := bstep (se 1 (by rfl) ⟨1874420, by rfl⟩ : syracuseStep 2499227 = 3748841) B3748841
theorem B1877033 : Blo 1108626 1877033 := bstep (se 2 (by rfl) ⟨703887, by rfl⟩ : syracuseStep 1877033 = 1407775) B1407775
theorem B1877161 : Blo 1108626 1877161 := bstep (se 2 (by rfl) ⟨703935, by rfl⟩ : syracuseStep 1877161 = 1407871) B1407871
theorem B6334463 : Blo 1108626 6334463 := bstep (se 1 (by rfl) ⟨4750847, by rfl⟩ : syracuseStep 6334463 = 9501695) B9501695
theorem B3745817 : Blo 1108626 3745817 := bstep (se 2 (by rfl) ⟨1404681, by rfl⟩ : syracuseStep 3745817 = 2809363) B2809363
theorem B2501351 : Blo 1108626 2501351 := bstep (se 1 (by rfl) ⟨1876013, by rfl⟩ : syracuseStep 2501351 = 3752027) B3752027
theorem B3746843 : Blo 1108626 3746843 := bstep (se 1 (by rfl) ⟨2810132, by rfl⟩ : syracuseStep 3746843 = 5620265) B5620265
theorem B5614919 : Blo 1108626 5614919 := bstep (se 1 (by rfl) ⟨4211189, by rfl⟩ : syracuseStep 5614919 = 8422379) B8422379
theorem B20231869 : Blo 1108626 20231869 := bstep (se 3 (by rfl) ⟨3793475, by rfl⟩ : syracuseStep 20231869 = 7586951) B7586951
theorem B4209641 : Blo 1108626 4209641 := bstep (se 2 (by rfl) ⟨1578615, by rfl⟩ : syracuseStep 4209641 = 3157231) B3157231
theorem B45661643 : Blo 1108626 45661643 := bstep (se 1 (by rfl) ⟨34246232, by rfl⟩ : syracuseStep 45661643 = 68492465) B68492465
theorem B15220979 : Blo 1108626 15220979 := bstep (se 1 (by rfl) ⟨11415734, by rfl⟩ : syracuseStep 15220979 = 22831469) B22831469
theorem B18006461 : Blo 1108626 18006461 := bstep (se 3 (by rfl) ⟨3376211, by rfl⟩ : syracuseStep 18006461 = 6752423) B6752423
theorem B3556217 : Blo 1108626 3556217 := bstep (se 2 (by rfl) ⟨1333581, by rfl⟩ : syracuseStep 3556217 = 2667163) B2667163
theorem B6505919 : Blo 1108626 6505919 := bstep (se 1 (by rfl) ⟨4879439, by rfl⟩ : syracuseStep 6505919 = 9758879) B9758879
theorem B3753971 : Blo 1108626 3753971 := bstep (se 1 (by rfl) ⟨2815478, by rfl⟩ : syracuseStep 3753971 = 5630957) B5630957
theorem B5622047 : Blo 1108626 5622047 := bstep (se 1 (by rfl) ⟨4216535, by rfl⟩ : syracuseStep 5622047 = 8433071) B8433071
theorem B5622695 : Blo 1108626 5622695 := bstep (se 1 (by rfl) ⟨4217021, by rfl⟩ : syracuseStep 5622695 = 8434043) B8434043
theorem B7689775 : Blo 1108626 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B4216445 : Blo 1108626 4216445 := bstep (se 3 (by rfl) ⟨790583, by rfl⟩ : syracuseStep 4216445 = 1581167) B1581167
theorem B2807855 : Blo 1108626 2807855 := bstep (se 1 (by rfl) ⟨2105891, by rfl⟩ : syracuseStep 2807855 = 4211783) B4211783
theorem B38459929 : Blo 1108626 38459929 := bstep (se 2 (by rfl) ⟨14422473, by rfl⟩ : syracuseStep 38459929 = 28844947) B28844947
theorem B12017281 : Blo 1108626 12017281 := bstep (se 2 (by rfl) ⟨4506480, by rfl⟩ : syracuseStep 12017281 = 9012961) B9012961
theorem B9494657 : Blo 1108626 9494657 := bstep (se 2 (by rfl) ⟨3560496, by rfl⟩ : syracuseStep 9494657 = 7120993) B7120993
theorem B2810011 : Blo 1108626 2810011 := bstep (se 1 (by rfl) ⟨2107508, by rfl⟩ : syracuseStep 2810011 = 4215017) B4215017
theorem B1663727 : Blo 1108626 1663727 := bstep (se 1 (by rfl) ⟨1247795, by rfl⟩ : syracuseStep 1663727 = 2495591) B2495591
theorem B1500863 : Blo 1108626 1500863 := bstep (se 1 (by rfl) ⟨1125647, by rfl⟩ : syracuseStep 1500863 = 2251295) B2251295
theorem B32041007 : Blo 1108626 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B1404155 : Blo 1108626 1404155 := bstep (se 1 (by rfl) ⟨1053116, by rfl⟩ : syracuseStep 1404155 = 2106233) B2106233
theorem B3206591 : Blo 1108626 3206591 := bstep (se 1 (by rfl) ⟨2404943, by rfl⟩ : syracuseStep 3206591 = 4809887) B4809887
theorem B6746195 : Blo 1108626 6746195 := bstep (se 1 (by rfl) ⟨5059646, by rfl⟩ : syracuseStep 6746195 = 10119293) B10119293
theorem B5632091 : Blo 1108626 5632091 := bstep (se 1 (by rfl) ⟨4224068, by rfl⟩ : syracuseStep 5632091 = 8448137) B8448137
theorem B5337323 : Blo 1108626 5337323 := bstep (se 1 (by rfl) ⟨4002992, by rfl⟩ : syracuseStep 5337323 = 8005985) B8005985
theorem B1667519 : Blo 1108626 1667519 := bstep (se 1 (by rfl) ⟨1250639, by rfl⟩ : syracuseStep 1667519 = 2501279) B2501279
theorem B5403115 : Blo 1108626 5403115 := bstep (se 1 (by rfl) ⟨4052336, by rfl⟩ : syracuseStep 5403115 = 8104673) B8104673
theorem B1110511 : Blo 1108626 1110511 := bstep (se 1 (by rfl) ⟨832883, by rfl⟩ : syracuseStep 1110511 = 1665767) B1665767
theorem B7598971 : Blo 1108626 7598971 := bstep (se 1 (by rfl) ⟨5699228, by rfl⟩ : syracuseStep 7598971 = 11398457) B11398457
theorem B1111131 : Blo 1108626 1111131 := bstep (se 1 (by rfl) ⟨833348, by rfl⟩ : syracuseStep 1111131 = 1666697) B1666697
theorem B1111263 : Blo 1108626 1111263 := bstep (se 1 (by rfl) ⟨833447, by rfl⟩ : syracuseStep 1111263 = 1666895) B1666895
theorem B1111579 : Blo 1108626 1111579 := bstep (se 1 (by rfl) ⟨833684, by rfl⟩ : syracuseStep 1111579 = 1667369) B1667369
theorem B1668671 : Blo 1108626 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B6748535 : Blo 1108626 6748535 := bstep (se 1 (by rfl) ⟨5061401, by rfl⟩ : syracuseStep 6748535 = 10122803) B10122803
theorem B32078369 : Blo 1108626 32078369 := bstep (se 2 (by rfl) ⟨12029388, by rfl⟩ : syracuseStep 32078369 = 24058777) B24058777
theorem B10975975 : Blo 1108626 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B9010433 : Blo 1108626 9010433 := bstep (se 2 (by rfl) ⟨3378912, by rfl⟩ : syracuseStep 9010433 = 6757825) B6757825
theorem B8420921 : Blo 1108626 8420921 := bstep (se 2 (by rfl) ⟨3157845, by rfl⟩ : syracuseStep 8420921 = 6315691) B6315691
theorem B1247647 : Blo 1108626 1247647 := bstep (se 1 (by rfl) ⟨935735, by rfl⟩ : syracuseStep 1247647 = 1871471) B1871471
theorem B129764825 : Blo 1108626 129764825 := bstep (se 2 (by rfl) ⟨48661809, by rfl⟩ : syracuseStep 129764825 = 97323619) B97323619
theorem B12652523 : Blo 1108626 12652523 := bstep (se 1 (by rfl) ⟨9489392, by rfl⟩ : syracuseStep 12652523 = 18978785) B18978785
theorem B1871903 : Blo 1108626 1871903 := bstep (se 1 (by rfl) ⟨1403927, by rfl⟩ : syracuseStep 1871903 = 2807855) B2807855
theorem B4002301 : Blo 1108626 4002301 := bstep (se 3 (by rfl) ⟨750431, by rfl⟩ : syracuseStep 4002301 = 1500863) B1500863
theorem B2495465 : Blo 1108626 2495465 := bstep (se 2 (by rfl) ⟨935799, by rfl⟩ : syracuseStep 2495465 = 1871599) B1871599
theorem B6329771 : Blo 1108626 6329771 := bstep (se 1 (by rfl) ⟨4747328, by rfl⟩ : syracuseStep 6329771 = 9494657) B9494657
theorem B1251355 : Blo 1108626 1251355 := bstep (se 1 (by rfl) ⟨938516, by rfl⟩ : syracuseStep 1251355 = 1877033) B1877033
theorem B10131961 : Blo 1108626 10131961 := bstep (se 2 (by rfl) ⟨3799485, by rfl⟩ : syracuseStep 10131961 = 7598971) B7598971
theorem B2497211 : Blo 1108626 2497211 := bstep (se 1 (by rfl) ⟨1872908, by rfl⟩ : syracuseStep 2497211 = 3745817) B3745817
theorem B2497895 : Blo 1108626 2497895 := bstep (se 1 (by rfl) ⟨1873421, by rfl⟩ : syracuseStep 2497895 = 3746843) B3746843
theorem B3743279 : Blo 1108626 3743279 := bstep (se 1 (by rfl) ⟨2807459, by rfl⟩ : syracuseStep 3743279 = 5614919) B5614919
theorem B26975825 : Blo 1108626 26975825 := bstep (se 2 (by rfl) ⟨10115934, by rfl⟩ : syracuseStep 26975825 = 20231869) B20231869
theorem B2137727 : Blo 1108626 2137727 := bstep (se 1 (by rfl) ⟨1603295, by rfl⟩ : syracuseStep 2137727 = 3206591) B3206591
theorem B4497463 : Blo 1108626 4497463 := bstep (se 1 (by rfl) ⟨3373097, by rfl⟩ : syracuseStep 4497463 = 6746195) B6746195
theorem B3744413 : Blo 1108626 3744413 := bstep (se 3 (by rfl) ⟨702077, by rfl⟩ : syracuseStep 3744413 = 1404155) B1404155
theorem B4499023 : Blo 1108626 4499023 := bstep (se 1 (by rfl) ⟨3374267, by rfl⟩ : syracuseStep 4499023 = 6748535) B6748535
theorem B6006955 : Blo 1108626 6006955 := bstep (se 1 (by rfl) ⟨4505216, by rfl⟩ : syracuseStep 6006955 = 9010433) B9010433
theorem B5613947 : Blo 1108626 5613947 := bstep (se 1 (by rfl) ⟨4210460, by rfl⟩ : syracuseStep 5613947 = 8420921) B8420921
theorem B3746681 : Blo 1108626 3746681 := bstep (se 2 (by rfl) ⟨1405005, by rfl⟩ : syracuseStep 3746681 = 2810011) B2810011
theorem B12004307 : Blo 1108626 12004307 := bstep (se 1 (by rfl) ⟨9003230, by rfl⟩ : syracuseStep 12004307 = 18006461) B18006461
theorem B2370811 : Blo 1108626 2370811 := bstep (se 1 (by rfl) ⟨1778108, by rfl⟩ : syracuseStep 2370811 = 3556217) B3556217
theorem B9481535 : Blo 1108626 9481535 := bstep (se 1 (by rfl) ⟨7111151, by rfl⟩ : syracuseStep 9481535 = 14222303) B14222303
theorem B4337279 : Blo 1108626 4337279 := bstep (se 1 (by rfl) ⟨3252959, by rfl⟩ : syracuseStep 4337279 = 6505919) B6505919
theorem B2502647 : Blo 1108626 2502647 := bstep (se 1 (by rfl) ⟨1876985, by rfl⟩ : syracuseStep 2502647 = 3753971) B3753971
theorem B3748031 : Blo 1108626 3748031 := bstep (se 1 (by rfl) ⟨2811023, by rfl⟩ : syracuseStep 3748031 = 5622047) B5622047
theorem B2502881 : Blo 1108626 2502881 := bstep (se 2 (by rfl) ⟨938580, by rfl⟩ : syracuseStep 2502881 = 1877161) B1877161
theorem B14430797 : Blo 1108626 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B3748463 : Blo 1108626 3748463 := bstep (se 1 (by rfl) ⟨2811347, by rfl⟩ : syracuseStep 3748463 = 5622695) B5622695
theorem B10138567 : Blo 1108626 10138567 := bstep (se 1 (by rfl) ⟨7603925, by rfl⟩ : syracuseStep 10138567 = 15207851) B15207851
theorem B58538533 : Blo 1108626 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B3754727 : Blo 1108626 3754727 := bstep (se 1 (by rfl) ⟨2816045, by rfl⟩ : syracuseStep 3754727 = 5632091) B5632091
theorem B3558215 : Blo 1108626 3558215 := bstep (se 1 (by rfl) ⟨2668661, by rfl⟩ : syracuseStep 3558215 = 5337323) B5337323
theorem B21385579 : Blo 1108626 21385579 := bstep (se 1 (by rfl) ⟨16039184, by rfl⟩ : syracuseStep 21385579 = 32078369) B32078369
theorem B2806427 : Blo 1108626 2806427 := bstep (se 1 (by rfl) ⟨2104820, by rfl⟩ : syracuseStep 2806427 = 4209641) B4209641
theorem B10147319 : Blo 1108626 10147319 := bstep (se 1 (by rfl) ⟨7610489, by rfl⟩ : syracuseStep 10147319 = 15220979) B15220979
theorem B5070377 : Blo 1108626 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B2810963 : Blo 1108626 2810963 := bstep (se 1 (by rfl) ⟨2108222, by rfl⟩ : syracuseStep 2810963 = 4216445) B4216445
theorem B1664447 : Blo 1108626 1664447 := bstep (se 1 (by rfl) ⟨1248335, by rfl⟩ : syracuseStep 1664447 = 2496671) B2496671
theorem B1666151 : Blo 1108626 1666151 := bstep (se 1 (by rfl) ⟨1249613, by rfl⟩ : syracuseStep 1666151 = 2499227) B2499227
theorem B1109151 : Blo 1108626 1109151 := bstep (se 1 (by rfl) ⟨831863, by rfl⟩ : syracuseStep 1109151 = 1663727) B1663727
theorem B7204153 : Blo 1108626 7204153 := bstep (se 2 (by rfl) ⟨2701557, by rfl⟩ : syracuseStep 7204153 = 5403115) B5403115
theorem B4222975 : Blo 1108626 4222975 := bstep (se 1 (by rfl) ⟨3167231, by rfl⟩ : syracuseStep 4222975 = 6334463) B6334463
theorem B21360671 : Blo 1108626 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B1667567 : Blo 1108626 1667567 := bstep (se 1 (by rfl) ⟨1250675, by rfl⟩ : syracuseStep 1667567 = 2501351) B2501351
theorem B10253033 : Blo 1108626 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B1668713 : Blo 1108626 1668713 := bstep (se 2 (by rfl) ⟨625767, by rfl⟩ : syracuseStep 1668713 = 1251535) B1251535
theorem B1111679 : Blo 1108626 1111679 := bstep (se 1 (by rfl) ⟨833759, by rfl⟩ : syracuseStep 1111679 = 1667519) B1667519
theorem B51279905 : Blo 1108626 51279905 := bstep (se 2 (by rfl) ⟨19229964, by rfl⟩ : syracuseStep 51279905 = 38459929) B38459929
theorem B1112447 : Blo 1108626 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B16023041 : Blo 1108626 16023041 := bstep (se 2 (by rfl) ⟨6008640, by rfl⟩ : syracuseStep 16023041 = 12017281) B12017281
theorem B30441095 : Blo 1108626 30441095 := bstep (se 1 (by rfl) ⟨22830821, by rfl⟩ : syracuseStep 30441095 = 45661643) B45661643
theorem B23986469 : Blo 1108626 23986469 := bstep (se 4 (by rfl) ⟨2248731, by rfl⟩ : syracuseStep 23986469 = 4497463) B4497463
theorem B5998697 : Blo 1108626 5998697 := bstep (se 2 (by rfl) ⟨2249511, by rfl⟩ : syracuseStep 5998697 = 4499023) B4499023
theorem B86509883 : Blo 1108626 86509883 := bstep (se 1 (by rfl) ⟨64882412, by rfl⟩ : syracuseStep 86509883 = 129764825) B129764825
theorem B1247935 : Blo 1108626 1247935 := bstep (se 1 (by rfl) ⟨935951, by rfl⟩ : syracuseStep 1247935 = 1871903) B1871903
theorem B1870951 : Blo 1108626 1870951 := bstep (se 1 (by rfl) ⟨1403213, by rfl⟩ : syracuseStep 1870951 = 2806427) B2806427
theorem B9605537 : Blo 1108626 9605537 := bstep (se 2 (by rfl) ⟨3602076, by rfl⟩ : syracuseStep 9605537 = 7204153) B7204153
theorem B2495519 : Blo 1108626 2495519 := bstep (se 1 (by rfl) ⟨1871639, by rfl⟩ : syracuseStep 2495519 = 3743279) B3743279
theorem B136746413 : Blo 1108626 136746413 := bstep (se 3 (by rfl) ⟨25639952, by rfl⟩ : syracuseStep 136746413 = 51279905) B51279905
theorem B2496275 : Blo 1108626 2496275 := bstep (se 1 (by rfl) ⟨1872206, by rfl⟩ : syracuseStep 2496275 = 3744413) B3744413
theorem B28514105 : Blo 1108626 28514105 := bstep (se 2 (by rfl) ⟨10692789, by rfl⟩ : syracuseStep 28514105 = 21385579) B21385579
theorem B1873975 : Blo 1108626 1873975 := bstep (se 1 (by rfl) ⟨1405481, by rfl⟩ : syracuseStep 1873975 = 2810963) B2810963
theorem B3742631 : Blo 1108626 3742631 := bstep (se 1 (by rfl) ⟨2806973, by rfl⟩ : syracuseStep 3742631 = 5613947) B5613947
theorem B2497787 : Blo 1108626 2497787 := bstep (se 1 (by rfl) ⟨1873340, by rfl⟩ : syracuseStep 2497787 = 3746681) B3746681
theorem B8002871 : Blo 1108626 8002871 := bstep (se 1 (by rfl) ⟨6002153, by rfl⟩ : syracuseStep 8002871 = 12004307) B12004307
theorem B2891519 : Blo 1108626 2891519 := bstep (se 1 (by rfl) ⟨2168639, by rfl⟩ : syracuseStep 2891519 = 4337279) B4337279
theorem B2498687 : Blo 1108626 2498687 := bstep (se 1 (by rfl) ⟨1874015, by rfl⟩ : syracuseStep 2498687 = 3748031) B3748031
theorem B2498975 : Blo 1108626 2498975 := bstep (se 1 (by rfl) ⟨1874231, by rfl⟩ : syracuseStep 2498975 = 3748463) B3748463
theorem B13509281 : Blo 1108626 13509281 := bstep (se 2 (by rfl) ⟨5065980, by rfl⟩ : syracuseStep 13509281 = 10131961) B10131961
theorem B20294063 : Blo 1108626 20294063 := bstep (se 1 (by rfl) ⟨15220547, by rfl⟩ : syracuseStep 20294063 = 30441095) B30441095
theorem B2503151 : Blo 1108626 2503151 := bstep (se 1 (by rfl) ⟨1877363, by rfl⟩ : syracuseStep 2503151 = 3754727) B3754727
theorem B8435015 : Blo 1108626 8435015 := bstep (se 1 (by rfl) ⟨6326261, by rfl⟩ : syracuseStep 8435015 = 12652523) B12652523
theorem B8009273 : Blo 1108626 8009273 := bstep (se 2 (by rfl) ⟨3003477, by rfl⟩ : syracuseStep 8009273 = 6006955) B6006955
theorem B6764879 : Blo 1108626 6764879 := bstep (se 1 (by rfl) ⟨5073659, by rfl⟩ : syracuseStep 6764879 = 10147319) B10147319
theorem B3161081 : Blo 1108626 3161081 := bstep (se 2 (by rfl) ⟨1185405, by rfl⟩ : syracuseStep 3161081 = 2370811) B2370811
theorem B1425151 : Blo 1108626 1425151 := bstep (se 1 (by rfl) ⟨1068863, by rfl⟩ : syracuseStep 1425151 = 2137727) B2137727
theorem B13518089 : Blo 1108626 13518089 := bstep (se 2 (by rfl) ⟨5069283, by rfl⟩ : syracuseStep 13518089 = 10138567) B10138567
theorem B9488573 : Blo 1108626 9488573 := bstep (se 3 (by rfl) ⟨1779107, by rfl⟩ : syracuseStep 9488573 = 3558215) B3558215
theorem B14240447 : Blo 1108626 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B9620531 : Blo 1108626 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B6835355 : Blo 1108626 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B13521005 : Blo 1108626 13521005 := bstep (se 3 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 13521005 = 5070377) B5070377
theorem B1663529 : Blo 1108626 1663529 := bstep (se 2 (by rfl) ⟨623823, by rfl⟩ : syracuseStep 1663529 = 1247647) B1247647
theorem B1663643 : Blo 1108626 1663643 := bstep (se 1 (by rfl) ⟨1247732, by rfl⟩ : syracuseStep 1663643 = 2495465) B2495465
theorem B4219847 : Blo 1108626 4219847 := bstep (se 1 (by rfl) ⟨3164885, by rfl⟩ : syracuseStep 4219847 = 6329771) B6329771
theorem B1664807 : Blo 1108626 1664807 := bstep (se 1 (by rfl) ⟨1248605, by rfl⟩ : syracuseStep 1664807 = 2497211) B2497211
theorem B1665263 : Blo 1108626 1665263 := bstep (se 1 (by rfl) ⟨1248947, by rfl⟩ : syracuseStep 1665263 = 2497895) B2497895
theorem B17983883 : Blo 1108626 17983883 := bstep (se 1 (by rfl) ⟨13487912, by rfl⟩ : syracuseStep 17983883 = 26975825) B26975825
theorem B5630633 : Blo 1108626 5630633 := bstep (se 2 (by rfl) ⟨2111487, by rfl⟩ : syracuseStep 5630633 = 4222975) B4222975
theorem B5336401 : Blo 1108626 5336401 := bstep (se 2 (by rfl) ⟨2001150, by rfl⟩ : syracuseStep 5336401 = 4002301) B4002301
theorem B1109631 : Blo 1108626 1109631 := bstep (se 1 (by rfl) ⟨832223, by rfl⟩ : syracuseStep 1109631 = 1664447) B1664447
theorem B1110767 : Blo 1108626 1110767 := bstep (se 1 (by rfl) ⟨833075, by rfl⟩ : syracuseStep 1110767 = 1666151) B1666151
theorem B6321023 : Blo 1108626 6321023 := bstep (se 1 (by rfl) ⟨4740767, by rfl⟩ : syracuseStep 6321023 = 9481535) B9481535
theorem B1668431 : Blo 1108626 1668431 := bstep (se 1 (by rfl) ⟨1251323, by rfl⟩ : syracuseStep 1668431 = 2502647) B2502647
theorem B1668473 : Blo 1108626 1668473 := bstep (se 2 (by rfl) ⟨625677, by rfl⟩ : syracuseStep 1668473 = 1251355) B1251355
theorem B1668587 : Blo 1108626 1668587 := bstep (se 1 (by rfl) ⟨1251440, by rfl⟩ : syracuseStep 1668587 = 2502881) B2502881
theorem B1111711 : Blo 1108626 1111711 := bstep (se 1 (by rfl) ⟨833783, by rfl⟩ : syracuseStep 1111711 = 1667567) B1667567
theorem B78051377 : Blo 1108626 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B1112475 : Blo 1108626 1112475 := bstep (se 1 (by rfl) ⟨834356, by rfl⟩ : syracuseStep 1112475 = 1668713) B1668713
theorem B10682027 : Blo 1108626 10682027 := bstep (se 1 (by rfl) ⟨8011520, by rfl⟩ : syracuseStep 10682027 = 16023041) B16023041
theorem B15990979 : Blo 1108626 15990979 := bstep (se 1 (by rfl) ⟨11993234, by rfl⟩ : syracuseStep 15990979 = 23986469) B23986469
theorem B9012059 : Blo 1108626 9012059 := bstep (se 1 (by rfl) ⟨6759044, by rfl⟩ : syracuseStep 9012059 = 13518089) B13518089
theorem B3999131 : Blo 1108626 3999131 := bstep (se 1 (by rfl) ⟨2999348, by rfl⟩ : syracuseStep 3999131 = 5998697) B5998697
theorem B6325715 : Blo 1108626 6325715 := bstep (se 1 (by rfl) ⟨4744286, by rfl⟩ : syracuseStep 6325715 = 9488573) B9488573
theorem B57673255 : Blo 1108626 57673255 := bstep (se 1 (by rfl) ⟨43254941, by rfl⟩ : syracuseStep 57673255 = 86509883) B86509883
theorem B4556903 : Blo 1108626 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B9014003 : Blo 1108626 9014003 := bstep (se 1 (by rfl) ⟨6760502, by rfl⟩ : syracuseStep 9014003 = 13521005) B13521005
theorem B91164275 : Blo 1108626 91164275 := bstep (se 1 (by rfl) ⟨68373206, by rfl⟩ : syracuseStep 91164275 = 136746413) B136746413
theorem B19009403 : Blo 1108626 19009403 := bstep (se 1 (by rfl) ⟨14257052, by rfl⟩ : syracuseStep 19009403 = 28514105) B28514105
theorem B2494601 : Blo 1108626 2494601 := bstep (se 2 (by rfl) ⟨935475, by rfl⟩ : syracuseStep 2494601 = 1870951) B1870951
theorem B7115201 : Blo 1108626 7115201 := bstep (se 2 (by rfl) ⟨2668200, by rfl⟩ : syracuseStep 7115201 = 5336401) B5336401
theorem B2495087 : Blo 1108626 2495087 := bstep (se 1 (by rfl) ⟨1871315, by rfl⟩ : syracuseStep 2495087 = 3742631) B3742631
theorem B30842869 : Blo 1108626 30842869 := bstep (se 5 (by rfl) ⟨1445759, by rfl⟩ : syracuseStep 30842869 = 2891519) B2891519
theorem B2498633 : Blo 1108626 2498633 := bstep (se 2 (by rfl) ⟨936987, by rfl⟩ : syracuseStep 2498633 = 1873975) B1873975
theorem B2107387 : Blo 1108626 2107387 := bstep (se 1 (by rfl) ⟨1580540, by rfl⟩ : syracuseStep 2107387 = 3161081) B3161081
theorem B7121351 : Blo 1108626 7121351 := bstep (se 1 (by rfl) ⟨5341013, by rfl⟩ : syracuseStep 7121351 = 10682027) B10682027
theorem B6403691 : Blo 1108626 6403691 := bstep (se 1 (by rfl) ⟨4802768, by rfl⟩ : syracuseStep 6403691 = 9605537) B9605537
theorem B3753755 : Blo 1108626 3753755 := bstep (se 1 (by rfl) ⟨2815316, by rfl⟩ : syracuseStep 3753755 = 5630633) B5630633
theorem B4214015 : Blo 1108626 4214015 := bstep (se 1 (by rfl) ⟨3160511, by rfl⟩ : syracuseStep 4214015 = 6321023) B6321023
theorem B5623343 : Blo 1108626 5623343 := bstep (se 1 (by rfl) ⟨4217507, by rfl⟩ : syracuseStep 5623343 = 8435015) B8435015
theorem B4509919 : Blo 1108626 4509919 := bstep (se 1 (by rfl) ⟨3382439, by rfl⟩ : syracuseStep 4509919 = 6764879) B6764879
theorem B9493631 : Blo 1108626 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B6413687 : Blo 1108626 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B1663679 : Blo 1108626 1663679 := bstep (se 1 (by rfl) ⟨1247759, by rfl⟩ : syracuseStep 1663679 = 2495519) B2495519
theorem B1663913 : Blo 1108626 1663913 := bstep (se 2 (by rfl) ⟨623967, by rfl⟩ : syracuseStep 1663913 = 1247935) B1247935
theorem B1664183 : Blo 1108626 1664183 := bstep (se 1 (by rfl) ⟨1248137, by rfl⟩ : syracuseStep 1664183 = 2496275) B2496275
theorem B1665191 : Blo 1108626 1665191 := bstep (se 1 (by rfl) ⟨1248893, by rfl⟩ : syracuseStep 1665191 = 2497787) B2497787
theorem B5335247 : Blo 1108626 5335247 := bstep (se 1 (by rfl) ⟨4001435, by rfl⟩ : syracuseStep 5335247 = 8002871) B8002871
theorem B1665791 : Blo 1108626 1665791 := bstep (se 1 (by rfl) ⟨1249343, by rfl⟩ : syracuseStep 1665791 = 2498687) B2498687
theorem B1665983 : Blo 1108626 1665983 := bstep (se 1 (by rfl) ⟨1249487, by rfl⟩ : syracuseStep 1665983 = 2498975) B2498975
theorem B1109019 : Blo 1108626 1109019 := bstep (se 1 (by rfl) ⟨831764, by rfl⟩ : syracuseStep 1109019 = 1663529) B1663529
theorem B1109095 : Blo 1108626 1109095 := bstep (se 1 (by rfl) ⟨831821, by rfl⟩ : syracuseStep 1109095 = 1663643) B1663643
theorem B9006187 : Blo 1108626 9006187 := bstep (se 1 (by rfl) ⟨6754640, by rfl⟩ : syracuseStep 9006187 = 13509281) B13509281
theorem B2813231 : Blo 1108626 2813231 := bstep (se 1 (by rfl) ⟨2109923, by rfl⟩ : syracuseStep 2813231 = 4219847) B4219847
theorem B1109871 : Blo 1108626 1109871 := bstep (se 1 (by rfl) ⟨832403, by rfl⟩ : syracuseStep 1109871 = 1664807) B1664807
theorem B1110175 : Blo 1108626 1110175 := bstep (se 1 (by rfl) ⟨832631, by rfl⟩ : syracuseStep 1110175 = 1665263) B1665263
theorem B11989255 : Blo 1108626 11989255 := bstep (se 1 (by rfl) ⟨8991941, by rfl⟩ : syracuseStep 11989255 = 17983883) B17983883
theorem B13529375 : Blo 1108626 13529375 := bstep (se 1 (by rfl) ⟨10147031, by rfl⟩ : syracuseStep 13529375 = 20294063) B20294063
theorem B1668767 : Blo 1108626 1668767 := bstep (se 1 (by rfl) ⟨1251575, by rfl⟩ : syracuseStep 1668767 = 2503151) B2503151
theorem B1112287 : Blo 1108626 1112287 := bstep (se 1 (by rfl) ⟨834215, by rfl⟩ : syracuseStep 1112287 = 1668431) B1668431
theorem B1112315 : Blo 1108626 1112315 := bstep (se 1 (by rfl) ⟨834236, by rfl⟩ : syracuseStep 1112315 = 1668473) B1668473
theorem B1112391 : Blo 1108626 1112391 := bstep (se 1 (by rfl) ⟨834293, by rfl⟩ : syracuseStep 1112391 = 1668587) B1668587
theorem B5339515 : Blo 1108626 5339515 := bstep (se 1 (by rfl) ⟨4004636, by rfl⟩ : syracuseStep 5339515 = 8009273) B8009273
theorem B52034251 : Blo 1108626 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B1900201 : Blo 1108626 1900201 := bstep (se 2 (by rfl) ⟨712575, by rfl⟩ : syracuseStep 1900201 = 1425151) B1425151
theorem B6329087 : Blo 1108626 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B14227325 : Blo 1108626 14227325 := bstep (se 3 (by rfl) ⟨2667623, by rfl⟩ : syracuseStep 14227325 = 5335247) B5335247
theorem B1875487 : Blo 1108626 1875487 := bstep (se 1 (by rfl) ⟨1406615, by rfl⟩ : syracuseStep 1875487 = 2813231) B2813231
theorem B9019583 : Blo 1108626 9019583 := bstep (se 1 (by rfl) ⟨6764687, by rfl⟩ : syracuseStep 9019583 = 13529375) B13529375
theorem B7119353 : Blo 1108626 7119353 := bstep (se 2 (by rfl) ⟨2669757, by rfl⟩ : syracuseStep 7119353 = 5339515) B5339515
theorem B69379001 : Blo 1108626 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B4269127 : Blo 1108626 4269127 := bstep (se 1 (by rfl) ⟨3201845, by rfl⟩ : syracuseStep 4269127 = 6403691) B6403691
theorem B2533601 : Blo 1108626 2533601 := bstep (se 2 (by rfl) ⟨950100, by rfl⟩ : syracuseStep 2533601 = 1900201) B1900201
theorem B6008039 : Blo 1108626 6008039 := bstep (se 1 (by rfl) ⟨4506029, by rfl⟩ : syracuseStep 6008039 = 9012059) B9012059
theorem B2666087 : Blo 1108626 2666087 := bstep (se 1 (by rfl) ⟨1999565, by rfl⟩ : syracuseStep 2666087 = 3999131) B3999131
theorem B48606965 : Blo 1108626 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B2502503 : Blo 1108626 2502503 := bstep (se 1 (by rfl) ⟨1876877, by rfl⟩ : syracuseStep 2502503 = 3753755) B3753755
theorem B6009335 : Blo 1108626 6009335 := bstep (se 1 (by rfl) ⟨4507001, by rfl⟩ : syracuseStep 6009335 = 9014003) B9014003
theorem B3748895 : Blo 1108626 3748895 := bstep (se 1 (by rfl) ⟨2811671, by rfl⟩ : syracuseStep 3748895 = 5623343) B5623343
theorem B12008249 : Blo 1108626 12008249 := bstep (se 2 (by rfl) ⟨4503093, by rfl⟩ : syracuseStep 12008249 = 9006187) B9006187
theorem B4275791 : Blo 1108626 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B6013225 : Blo 1108626 6013225 := bstep (se 2 (by rfl) ⟨2254959, by rfl⟩ : syracuseStep 6013225 = 4509919) B4509919
theorem B21321305 : Blo 1108626 21321305 := bstep (se 2 (by rfl) ⟨7995489, by rfl⟩ : syracuseStep 21321305 = 15990979) B15990979
theorem B4217143 : Blo 1108626 4217143 := bstep (se 1 (by rfl) ⟨3162857, by rfl⟩ : syracuseStep 4217143 = 6325715) B6325715
theorem B76897673 : Blo 1108626 76897673 := bstep (se 2 (by rfl) ⟨28836627, by rfl⟩ : syracuseStep 76897673 = 57673255) B57673255
theorem B2809343 : Blo 1108626 2809343 := bstep (se 1 (by rfl) ⟨2107007, by rfl⟩ : syracuseStep 2809343 = 4214015) B4214015
theorem B60776183 : Blo 1108626 60776183 := bstep (se 1 (by rfl) ⟨45582137, by rfl⟩ : syracuseStep 60776183 = 91164275) B91164275
theorem B12672935 : Blo 1108626 12672935 := bstep (se 1 (by rfl) ⟨9504701, by rfl⟩ : syracuseStep 12672935 = 19009403) B19009403
theorem B2809849 : Blo 1108626 2809849 := bstep (se 2 (by rfl) ⟨1053693, by rfl⟩ : syracuseStep 2809849 = 2107387) B2107387
theorem B1663067 : Blo 1108626 1663067 := bstep (se 1 (by rfl) ⟨1247300, by rfl⟩ : syracuseStep 1663067 = 2494601) B2494601
theorem B4743467 : Blo 1108626 4743467 := bstep (se 1 (by rfl) ⟨3557600, by rfl⟩ : syracuseStep 4743467 = 7115201) B7115201
theorem B1663391 : Blo 1108626 1663391 := bstep (se 1 (by rfl) ⟨1247543, by rfl⟩ : syracuseStep 1663391 = 2495087) B2495087
theorem B1665755 : Blo 1108626 1665755 := bstep (se 1 (by rfl) ⟨1249316, by rfl⟩ : syracuseStep 1665755 = 2498633) B2498633
theorem B15985673 : Blo 1108626 15985673 := bstep (se 2 (by rfl) ⟨5994627, by rfl⟩ : syracuseStep 15985673 = 11989255) B11989255
theorem B1109119 : Blo 1108626 1109119 := bstep (se 1 (by rfl) ⟨831839, by rfl⟩ : syracuseStep 1109119 = 1663679) B1663679
theorem B1109275 : Blo 1108626 1109275 := bstep (se 1 (by rfl) ⟨831956, by rfl⟩ : syracuseStep 1109275 = 1663913) B1663913
theorem B1109455 : Blo 1108626 1109455 := bstep (se 1 (by rfl) ⟨832091, by rfl⟩ : syracuseStep 1109455 = 1664183) B1664183
theorem B1110127 : Blo 1108626 1110127 := bstep (se 1 (by rfl) ⟨832595, by rfl⟩ : syracuseStep 1110127 = 1665191) B1665191
theorem B4747567 : Blo 1108626 4747567 := bstep (se 1 (by rfl) ⟨3560675, by rfl⟩ : syracuseStep 4747567 = 7121351) B7121351
theorem B1110527 : Blo 1108626 1110527 := bstep (se 1 (by rfl) ⟨832895, by rfl⟩ : syracuseStep 1110527 = 1665791) B1665791
theorem B1110655 : Blo 1108626 1110655 := bstep (se 1 (by rfl) ⟨832991, by rfl⟩ : syracuseStep 1110655 = 1665983) B1665983
theorem B1112511 : Blo 1108626 1112511 := bstep (se 1 (by rfl) ⟨834383, by rfl⟩ : syracuseStep 1112511 = 1668767) B1668767
theorem B41123825 : Blo 1108626 41123825 := bstep (se 2 (by rfl) ⟨15421434, by rfl⟩ : syracuseStep 41123825 = 30842869) B30842869
theorem B1872895 : Blo 1108626 1872895 := bstep (se 1 (by rfl) ⟨1404671, by rfl⟩ : syracuseStep 1872895 = 2809343) B2809343
theorem B6330089 : Blo 1108626 6330089 := bstep (se 2 (by rfl) ⟨2373783, by rfl⟩ : syracuseStep 6330089 = 4747567) B4747567
theorem B10657115 : Blo 1108626 10657115 := bstep (se 1 (by rfl) ⟨7992836, by rfl⟩ : syracuseStep 10657115 = 15985673) B15985673
theorem B4005359 : Blo 1108626 4005359 := bstep (se 1 (by rfl) ⟨3004019, by rfl⟩ : syracuseStep 4005359 = 6008039) B6008039
theorem B1777391 : Blo 1108626 1777391 := bstep (se 1 (by rfl) ⟨1333043, by rfl⟩ : syracuseStep 1777391 = 2666087) B2666087
theorem B4006223 : Blo 1108626 4006223 := bstep (se 1 (by rfl) ⟨3004667, by rfl⟩ : syracuseStep 4006223 = 6009335) B6009335
theorem B2499263 : Blo 1108626 2499263 := bstep (se 1 (by rfl) ⟨1874447, by rfl⟩ : syracuseStep 2499263 = 3748895) B3748895
theorem B8005499 : Blo 1108626 8005499 := bstep (se 1 (by rfl) ⟨6004124, by rfl⟩ : syracuseStep 8005499 = 12008249) B12008249
theorem B2500649 : Blo 1108626 2500649 := bstep (se 2 (by rfl) ⟨937743, by rfl⟩ : syracuseStep 2500649 = 1875487) B1875487
theorem B3746465 : Blo 1108626 3746465 := bstep (se 2 (by rfl) ⟨1404924, by rfl⟩ : syracuseStep 3746465 = 2809849) B2809849
theorem B9484883 : Blo 1108626 9484883 := bstep (se 1 (by rfl) ⟨7113662, by rfl⟩ : syracuseStep 9484883 = 14227325) B14227325
theorem B51265115 : Blo 1108626 51265115 := bstep (se 1 (by rfl) ⟨38448836, by rfl⟩ : syracuseStep 51265115 = 76897673) B76897673
theorem B40517455 : Blo 1108626 40517455 := bstep (se 1 (by rfl) ⟨30388091, by rfl⟩ : syracuseStep 40517455 = 60776183) B60776183
theorem B6013055 : Blo 1108626 6013055 := bstep (se 1 (by rfl) ⟨4509791, by rfl⟩ : syracuseStep 6013055 = 9019583) B9019583
theorem B3162311 : Blo 1108626 3162311 := bstep (se 1 (by rfl) ⟨2371733, by rfl⟩ : syracuseStep 3162311 = 4743467) B4743467
theorem B46252667 : Blo 1108626 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B1689067 : Blo 1108626 1689067 := bstep (se 1 (by rfl) ⟨1266800, by rfl⟩ : syracuseStep 1689067 = 2533601) B2533601
theorem B5622857 : Blo 1108626 5622857 := bstep (se 2 (by rfl) ⟨2108571, by rfl⟩ : syracuseStep 5622857 = 4217143) B4217143
theorem B27415883 : Blo 1108626 27415883 := bstep (se 1 (by rfl) ⟨20561912, by rfl⟩ : syracuseStep 27415883 = 41123825) B41123825
theorem B8017633 : Blo 1108626 8017633 := bstep (se 2 (by rfl) ⟨3006612, by rfl⟩ : syracuseStep 8017633 = 6013225) B6013225
theorem B5692169 : Blo 1108626 5692169 := bstep (se 2 (by rfl) ⟨2134563, by rfl⟩ : syracuseStep 5692169 = 4269127) B4269127
theorem B4219391 : Blo 1108626 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B14214203 : Blo 1108626 14214203 := bstep (se 1 (by rfl) ⟨10660652, by rfl⟩ : syracuseStep 14214203 = 21321305) B21321305
theorem B8448623 : Blo 1108626 8448623 := bstep (se 1 (by rfl) ⟨6336467, by rfl⟩ : syracuseStep 8448623 = 12672935) B12672935
theorem B1108711 : Blo 1108626 1108711 := bstep (se 1 (by rfl) ⟨831533, by rfl⟩ : syracuseStep 1108711 = 1663067) B1663067
theorem B1108927 : Blo 1108626 1108927 := bstep (se 1 (by rfl) ⟨831695, by rfl⟩ : syracuseStep 1108927 = 1663391) B1663391
theorem B4746235 : Blo 1108626 4746235 := bstep (se 1 (by rfl) ⟨3559676, by rfl⟩ : syracuseStep 4746235 = 7119353) B7119353
theorem B1110503 : Blo 1108626 1110503 := bstep (se 1 (by rfl) ⟨832877, by rfl⟩ : syracuseStep 1110503 = 1665755) B1665755
theorem B32404643 : Blo 1108626 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B1668335 : Blo 1108626 1668335 := bstep (se 1 (by rfl) ⟨1251251, by rfl⟩ : syracuseStep 1668335 = 2502503) B2502503
theorem B2850527 : Blo 1108626 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B123340445 : Blo 1108626 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B6328313 : Blo 1108626 6328313 := bstep (se 2 (by rfl) ⟨2373117, by rfl⟩ : syracuseStep 6328313 = 4746235) B4746235
theorem B1184927 : Blo 1108626 1184927 := bstep (se 1 (by rfl) ⟨888695, by rfl⟩ : syracuseStep 1184927 = 1777391) B1777391
theorem B9476135 : Blo 1108626 9476135 := bstep (se 1 (by rfl) ⟨7107101, by rfl⟩ : syracuseStep 9476135 = 14214203) B14214203
theorem B2497193 : Blo 1108626 2497193 := bstep (se 2 (by rfl) ⟨936447, by rfl⟩ : syracuseStep 2497193 = 1872895) B1872895
theorem B2497643 : Blo 1108626 2497643 := bstep (se 1 (by rfl) ⟨1873232, by rfl⟩ : syracuseStep 2497643 = 3746465) B3746465
theorem B10690177 : Blo 1108626 10690177 := bstep (se 2 (by rfl) ⟨4008816, by rfl⟩ : syracuseStep 10690177 = 8017633) B8017633
theorem B21603095 : Blo 1108626 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B4008703 : Blo 1108626 4008703 := bstep (se 1 (by rfl) ⟨3006527, by rfl⟩ : syracuseStep 4008703 = 6013055) B6013055
theorem B2108207 : Blo 1108626 2108207 := bstep (se 1 (by rfl) ⟨1581155, by rfl⟩ : syracuseStep 2108207 = 3162311) B3162311
theorem B3748571 : Blo 1108626 3748571 := bstep (se 1 (by rfl) ⟨2811428, by rfl⟩ : syracuseStep 3748571 = 5622857) B5622857
theorem B2670239 : Blo 1108626 2670239 := bstep (se 1 (by rfl) ⟨2002679, by rfl⟩ : syracuseStep 2670239 = 4005359) B4005359
theorem B2670815 : Blo 1108626 2670815 := bstep (se 1 (by rfl) ⟨2003111, by rfl⟩ : syracuseStep 2670815 = 4006223) B4006223
theorem B54023273 : Blo 1108626 54023273 := bstep (se 2 (by rfl) ⟨20258727, by rfl⟩ : syracuseStep 54023273 = 40517455) B40517455
theorem B2252089 : Blo 1108626 2252089 := bstep (se 2 (by rfl) ⟨844533, by rfl⟩ : syracuseStep 2252089 = 1689067) B1689067
theorem B18277255 : Blo 1108626 18277255 := bstep (se 1 (by rfl) ⟨13707941, by rfl⟩ : syracuseStep 18277255 = 27415883) B27415883
theorem B4220059 : Blo 1108626 4220059 := bstep (se 1 (by rfl) ⟨3165044, by rfl⟩ : syracuseStep 4220059 = 6330089) B6330089
theorem B3794779 : Blo 1108626 3794779 := bstep (se 1 (by rfl) ⟨2846084, by rfl⟩ : syracuseStep 3794779 = 5692169) B5692169
theorem B7104743 : Blo 1108626 7104743 := bstep (se 1 (by rfl) ⟨5328557, by rfl⟩ : syracuseStep 7104743 = 10657115) B10657115
theorem B2812927 : Blo 1108626 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B1666175 : Blo 1108626 1666175 := bstep (se 1 (by rfl) ⟨1249631, by rfl⟩ : syracuseStep 1666175 = 2499263) B2499263
theorem B5336999 : Blo 1108626 5336999 := bstep (se 1 (by rfl) ⟨4002749, by rfl⟩ : syracuseStep 5336999 = 8005499) B8005499
theorem B1667099 : Blo 1108626 1667099 := bstep (se 1 (by rfl) ⟨1250324, by rfl⟩ : syracuseStep 1667099 = 2500649) B2500649
theorem B5632415 : Blo 1108626 5632415 := bstep (se 1 (by rfl) ⟨4224311, by rfl⟩ : syracuseStep 5632415 = 8448623) B8448623
theorem B1112223 : Blo 1108626 1112223 := bstep (se 1 (by rfl) ⟨834167, by rfl⟩ : syracuseStep 1112223 = 1668335) B1668335
theorem B6323255 : Blo 1108626 6323255 := bstep (se 1 (by rfl) ⟨4742441, by rfl⟩ : syracuseStep 6323255 = 9484883) B9484883
theorem B34176743 : Blo 1108626 34176743 := bstep (se 1 (by rfl) ⟨25632557, by rfl⟩ : syracuseStep 34176743 = 51265115) B51265115
theorem B1900351 : Blo 1108626 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B36015515 : Blo 1108626 36015515 := bstep (se 1 (by rfl) ⟨27011636, by rfl⟩ : syracuseStep 36015515 = 54023273) B54023273
theorem B5344937 : Blo 1108626 5344937 := bstep (se 2 (by rfl) ⟨2004351, by rfl⟩ : syracuseStep 5344937 = 4008703) B4008703
theorem B2499047 : Blo 1108626 2499047 := bstep (se 1 (by rfl) ⟨1874285, by rfl⟩ : syracuseStep 2499047 = 3748571) B3748571
theorem B10135205 : Blo 1108626 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B1780159 : Blo 1108626 1780159 := bstep (se 1 (by rfl) ⟨1335119, by rfl⟩ : syracuseStep 1780159 = 2670239) B2670239
theorem B22784495 : Blo 1108626 22784495 := bstep (se 1 (by rfl) ⟨17088371, by rfl⟩ : syracuseStep 22784495 = 34176743) B34176743
theorem B1780543 : Blo 1108626 1780543 := bstep (se 1 (by rfl) ⟨1335407, by rfl⟩ : syracuseStep 1780543 = 2670815) B2670815
theorem B82226963 : Blo 1108626 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B5059705 : Blo 1108626 5059705 := bstep (se 2 (by rfl) ⟨1897389, by rfl⟩ : syracuseStep 5059705 = 3794779) B3794779
theorem B3159805 : Blo 1108626 3159805 := bstep (se 3 (by rfl) ⟨592463, by rfl⟩ : syracuseStep 3159805 = 1184927) B1184927
theorem B3750569 : Blo 1108626 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B14402063 : Blo 1108626 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B4736495 : Blo 1108626 4736495 := bstep (se 1 (by rfl) ⟨3552371, by rfl⟩ : syracuseStep 4736495 = 7104743) B7104743
theorem B12011141 : Blo 1108626 12011141 := bstep (se 4 (by rfl) ⟨1126044, by rfl⟩ : syracuseStep 12011141 = 2252089) B2252089
theorem B5621885 : Blo 1108626 5621885 := bstep (se 3 (by rfl) ⟨1054103, by rfl⟩ : syracuseStep 5621885 = 2108207) B2108207
theorem B3557999 : Blo 1108626 3557999 := bstep (se 1 (by rfl) ⟨2668499, by rfl⟩ : syracuseStep 3557999 = 5336999) B5336999
theorem B3754943 : Blo 1108626 3754943 := bstep (se 1 (by rfl) ⟨2816207, by rfl⟩ : syracuseStep 3754943 = 5632415) B5632415
theorem B4215503 : Blo 1108626 4215503 := bstep (se 1 (by rfl) ⟨3161627, by rfl⟩ : syracuseStep 4215503 = 6323255) B6323255
theorem B24369673 : Blo 1108626 24369673 := bstep (se 2 (by rfl) ⟨9138627, by rfl⟩ : syracuseStep 24369673 = 18277255) B18277255
theorem B5626745 : Blo 1108626 5626745 := bstep (se 2 (by rfl) ⟨2110029, by rfl⟩ : syracuseStep 5626745 = 4220059) B4220059
theorem B4218875 : Blo 1108626 4218875 := bstep (se 1 (by rfl) ⟨3164156, by rfl⟩ : syracuseStep 4218875 = 6328313) B6328313
theorem B6317423 : Blo 1108626 6317423 := bstep (se 1 (by rfl) ⟨4738067, by rfl⟩ : syracuseStep 6317423 = 9476135) B9476135
theorem B1664795 : Blo 1108626 1664795 := bstep (se 1 (by rfl) ⟨1248596, by rfl⟩ : syracuseStep 1664795 = 2497193) B2497193
theorem B1665095 : Blo 1108626 1665095 := bstep (se 1 (by rfl) ⟨1248821, by rfl⟩ : syracuseStep 1665095 = 2497643) B2497643
theorem B1110783 : Blo 1108626 1110783 := bstep (se 1 (by rfl) ⟨833087, by rfl⟩ : syracuseStep 1110783 = 1666175) B1666175
theorem B1111399 : Blo 1108626 1111399 := bstep (se 1 (by rfl) ⟨833549, by rfl⟩ : syracuseStep 1111399 = 1667099) B1667099
theorem B14253569 : Blo 1108626 14253569 := bstep (se 2 (by rfl) ⟨5345088, by rfl⟩ : syracuseStep 14253569 = 10690177) B10690177
theorem B9601375 : Blo 1108626 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B6756803 : Blo 1108626 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B2500379 : Blo 1108626 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B8007427 : Blo 1108626 8007427 := bstep (se 1 (by rfl) ⟨6005570, by rfl⟩ : syracuseStep 8007427 = 12011141) B12011141
theorem B3747923 : Blo 1108626 3747923 := bstep (se 1 (by rfl) ⟨2810942, by rfl⟩ : syracuseStep 3747923 = 5621885) B5621885
theorem B2371999 : Blo 1108626 2371999 := bstep (se 1 (by rfl) ⟨1778999, by rfl⟩ : syracuseStep 2371999 = 3557999) B3557999
theorem B2503295 : Blo 1108626 2503295 := bstep (se 1 (by rfl) ⟨1877471, by rfl⟩ : syracuseStep 2503295 = 3754943) B3754943
theorem B2373545 : Blo 1108626 2373545 := bstep (se 2 (by rfl) ⟨890079, by rfl⟩ : syracuseStep 2373545 = 1780159) B1780159
theorem B2374057 : Blo 1108626 2374057 := bstep (se 2 (by rfl) ⟨890271, by rfl⟩ : syracuseStep 2374057 = 1780543) B1780543
theorem B12630653 : Blo 1108626 12630653 := bstep (se 3 (by rfl) ⟨2368247, by rfl⟩ : syracuseStep 12630653 = 4736495) B4736495
theorem B3751163 : Blo 1108626 3751163 := bstep (se 1 (by rfl) ⟨2813372, by rfl⟩ : syracuseStep 3751163 = 5626745) B5626745
theorem B4211615 : Blo 1108626 4211615 := bstep (se 1 (by rfl) ⟨3158711, by rfl⟩ : syracuseStep 4211615 = 6317423) B6317423
theorem B4213073 : Blo 1108626 4213073 := bstep (se 2 (by rfl) ⟨1579902, by rfl⟩ : syracuseStep 4213073 = 3159805) B3159805
theorem B32492897 : Blo 1108626 32492897 := bstep (se 2 (by rfl) ⟨12184836, by rfl⟩ : syracuseStep 32492897 = 24369673) B24369673
theorem B24010343 : Blo 1108626 24010343 := bstep (se 1 (by rfl) ⟨18007757, by rfl⟩ : syracuseStep 24010343 = 36015515) B36015515
theorem B3563291 : Blo 1108626 3563291 := bstep (se 1 (by rfl) ⟨2672468, by rfl⟩ : syracuseStep 3563291 = 5344937) B5344937
theorem B2810335 : Blo 1108626 2810335 := bstep (se 1 (by rfl) ⟨2107751, by rfl⟩ : syracuseStep 2810335 = 4215503) B4215503
theorem B243034613 : Blo 1108626 243034613 := bstep (se 5 (by rfl) ⟨11392247, by rfl⟩ : syracuseStep 243034613 = 22784495) B22784495
theorem B2812583 : Blo 1108626 2812583 := bstep (se 1 (by rfl) ⟨2109437, by rfl⟩ : syracuseStep 2812583 = 4218875) B4218875
theorem B1666031 : Blo 1108626 1666031 := bstep (se 1 (by rfl) ⟨1249523, by rfl⟩ : syracuseStep 1666031 = 2499047) B2499047
theorem B1109863 : Blo 1108626 1109863 := bstep (se 1 (by rfl) ⟨832397, by rfl⟩ : syracuseStep 1109863 = 1664795) B1664795
theorem B1110063 : Blo 1108626 1110063 := bstep (se 1 (by rfl) ⟨832547, by rfl⟩ : syracuseStep 1110063 = 1665095) B1665095
theorem B6746273 : Blo 1108626 6746273 := bstep (se 2 (by rfl) ⟨2529852, by rfl⟩ : syracuseStep 6746273 = 5059705) B5059705
theorem B54817975 : Blo 1108626 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B9502379 : Blo 1108626 9502379 := bstep (se 1 (by rfl) ⟨7126784, by rfl⟩ : syracuseStep 9502379 = 14253569) B14253569
theorem B21661931 : Blo 1108626 21661931 := bstep (se 1 (by rfl) ⟨16246448, by rfl⟩ : syracuseStep 21661931 = 32492897) B32492897
theorem B1875055 : Blo 1108626 1875055 := bstep (se 1 (by rfl) ⟨1406291, by rfl⟩ : syracuseStep 1875055 = 2812583) B2812583
theorem B2498615 : Blo 1108626 2498615 := bstep (se 1 (by rfl) ⟨1873961, by rfl⟩ : syracuseStep 2498615 = 3747923) B3747923
theorem B4497515 : Blo 1108626 4497515 := bstep (se 1 (by rfl) ⟨3373136, by rfl⟩ : syracuseStep 4497515 = 6746273) B6746273
theorem B1582363 : Blo 1108626 1582363 := bstep (se 1 (by rfl) ⟨1186772, by rfl⟩ : syracuseStep 1582363 = 2373545) B2373545
theorem B2500775 : Blo 1108626 2500775 := bstep (se 1 (by rfl) ⟨1875581, by rfl⟩ : syracuseStep 2500775 = 3751163) B3751163
theorem B6334919 : Blo 1108626 6334919 := bstep (se 1 (by rfl) ⟨4751189, by rfl⟩ : syracuseStep 6334919 = 9502379) B9502379
theorem B3747113 : Blo 1108626 3747113 := bstep (se 2 (by rfl) ⟨1405167, by rfl⟩ : syracuseStep 3747113 = 2810335) B2810335
theorem B4504535 : Blo 1108626 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B16006895 : Blo 1108626 16006895 := bstep (se 1 (by rfl) ⟨12005171, by rfl⟩ : syracuseStep 16006895 = 24010343) B24010343
theorem B2375527 : Blo 1108626 2375527 := bstep (se 1 (by rfl) ⟨1781645, by rfl⟩ : syracuseStep 2375527 = 3563291) B3563291
theorem B3162665 : Blo 1108626 3162665 := bstep (se 2 (by rfl) ⟨1185999, by rfl⟩ : syracuseStep 3162665 = 2371999) B2371999
theorem B73090633 : Blo 1108626 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B162023075 : Blo 1108626 162023075 := bstep (se 1 (by rfl) ⟨121517306, by rfl⟩ : syracuseStep 162023075 = 243034613) B243034613
theorem B3165409 : Blo 1108626 3165409 := bstep (se 2 (by rfl) ⟨1187028, by rfl⟩ : syracuseStep 3165409 = 2374057) B2374057
theorem B12801833 : Blo 1108626 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B2807743 : Blo 1108626 2807743 := bstep (se 1 (by rfl) ⟨2105807, by rfl⟩ : syracuseStep 2807743 = 4211615) B4211615
theorem B2808715 : Blo 1108626 2808715 := bstep (se 1 (by rfl) ⟨2106536, by rfl⟩ : syracuseStep 2808715 = 4213073) B4213073
theorem B10676569 : Blo 1108626 10676569 := bstep (se 2 (by rfl) ⟨4003713, by rfl⟩ : syracuseStep 10676569 = 8007427) B8007427
theorem B1666919 : Blo 1108626 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B1110687 : Blo 1108626 1110687 := bstep (se 1 (by rfl) ⟨833015, by rfl⟩ : syracuseStep 1110687 = 1666031) B1666031
theorem B1668863 : Blo 1108626 1668863 := bstep (se 1 (by rfl) ⟨1251647, by rfl⟩ : syracuseStep 1668863 = 2503295) B2503295
theorem B8420435 : Blo 1108626 8420435 := bstep (se 1 (by rfl) ⟨6315326, by rfl⟩ : syracuseStep 8420435 = 12630653) B12630653
theorem B97454177 : Blo 1108626 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B2498075 : Blo 1108626 2498075 := bstep (se 1 (by rfl) ⟨1873556, by rfl⟩ : syracuseStep 2498075 = 3747113) B3747113
theorem B3743657 : Blo 1108626 3743657 := bstep (se 2 (by rfl) ⟨1403871, by rfl⟩ : syracuseStep 3743657 = 2807743) B2807743
theorem B3744953 : Blo 1108626 3744953 := bstep (se 2 (by rfl) ⟨1404357, by rfl⟩ : syracuseStep 3744953 = 2808715) B2808715
theorem B2500073 : Blo 1108626 2500073 := bstep (se 2 (by rfl) ⟨937527, by rfl⟩ : syracuseStep 2500073 = 1875055) B1875055
theorem B5613623 : Blo 1108626 5613623 := bstep (se 1 (by rfl) ⟨4210217, by rfl⟩ : syracuseStep 5613623 = 8420435) B8420435
theorem B2108443 : Blo 1108626 2108443 := bstep (se 1 (by rfl) ⟨1581332, by rfl⟩ : syracuseStep 2108443 = 3162665) B3162665
theorem B108015383 : Blo 1108626 108015383 := bstep (se 1 (by rfl) ⟨81011537, by rfl⟩ : syracuseStep 108015383 = 162023075) B162023075
theorem B2109817 : Blo 1108626 2109817 := bstep (se 2 (by rfl) ⟨791181, by rfl⟩ : syracuseStep 2109817 = 1582363) B1582363
theorem B14235425 : Blo 1108626 14235425 := bstep (se 2 (by rfl) ⟨5338284, by rfl⟩ : syracuseStep 14235425 = 10676569) B10676569
theorem B8534555 : Blo 1108626 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B2998343 : Blo 1108626 2998343 := bstep (se 1 (by rfl) ⟨2248757, by rfl⟩ : syracuseStep 2998343 = 4497515) B4497515
theorem B3003023 : Blo 1108626 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B3167369 : Blo 1108626 3167369 := bstep (se 2 (by rfl) ⟨1187763, by rfl⟩ : syracuseStep 3167369 = 2375527) B2375527
theorem B10671263 : Blo 1108626 10671263 := bstep (se 1 (by rfl) ⟨8003447, by rfl⟩ : syracuseStep 10671263 = 16006895) B16006895
theorem B4220545 : Blo 1108626 4220545 := bstep (se 2 (by rfl) ⟨1582704, by rfl⟩ : syracuseStep 4220545 = 3165409) B3165409
theorem B1665743 : Blo 1108626 1665743 := bstep (se 1 (by rfl) ⟨1249307, by rfl⟩ : syracuseStep 1665743 = 2498615) B2498615
theorem B57765149 : Blo 1108626 57765149 := bstep (se 3 (by rfl) ⟨10830965, by rfl⟩ : syracuseStep 57765149 = 21661931) B21661931
theorem B1667183 : Blo 1108626 1667183 := bstep (se 1 (by rfl) ⟨1250387, by rfl⟩ : syracuseStep 1667183 = 2500775) B2500775
theorem B4223279 : Blo 1108626 4223279 := bstep (se 1 (by rfl) ⟨3167459, by rfl⟩ : syracuseStep 4223279 = 6334919) B6334919
theorem B1111279 : Blo 1108626 1111279 := bstep (se 1 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 1111279 = 1666919) B1666919
theorem B1112575 : Blo 1108626 1112575 := bstep (se 1 (by rfl) ⟨834431, by rfl⟩ : syracuseStep 1112575 = 1668863) B1668863
theorem B7995581 : Blo 1108626 7995581 := bstep (se 3 (by rfl) ⟨1499171, by rfl⟩ : syracuseStep 7995581 = 2998343) B2998343
theorem B2002015 : Blo 1108626 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B7114175 : Blo 1108626 7114175 := bstep (se 1 (by rfl) ⟨5335631, by rfl⟩ : syracuseStep 7114175 = 10671263) B10671263
theorem B2495771 : Blo 1108626 2495771 := bstep (se 1 (by rfl) ⟨1871828, by rfl⟩ : syracuseStep 2495771 = 3743657) B3743657
theorem B2496635 : Blo 1108626 2496635 := bstep (se 1 (by rfl) ⟨1872476, by rfl⟩ : syracuseStep 2496635 = 3744953) B3744953
theorem B3742415 : Blo 1108626 3742415 := bstep (se 1 (by rfl) ⟨2806811, by rfl⟩ : syracuseStep 3742415 = 5613623) B5613623
theorem B38510099 : Blo 1108626 38510099 := bstep (se 1 (by rfl) ⟨28882574, by rfl⟩ : syracuseStep 38510099 = 57765149) B57765149
theorem B2111579 : Blo 1108626 2111579 := bstep (se 1 (by rfl) ⟨1583684, by rfl⟩ : syracuseStep 2111579 = 3167369) B3167369
theorem B72010255 : Blo 1108626 72010255 := bstep (se 1 (by rfl) ⟨54007691, by rfl⟩ : syracuseStep 72010255 = 108015383) B108015383
theorem B9490283 : Blo 1108626 9490283 := bstep (se 1 (by rfl) ⟨7117712, by rfl⟩ : syracuseStep 9490283 = 14235425) B14235425
theorem B5689703 : Blo 1108626 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B64969451 : Blo 1108626 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B5627393 : Blo 1108626 5627393 := bstep (se 2 (by rfl) ⟨2110272, by rfl⟩ : syracuseStep 5627393 = 4220545) B4220545
theorem B2811257 : Blo 1108626 2811257 := bstep (se 2 (by rfl) ⟨1054221, by rfl⟩ : syracuseStep 2811257 = 2108443) B2108443
theorem B1665383 : Blo 1108626 1665383 := bstep (se 1 (by rfl) ⟨1249037, by rfl⟩ : syracuseStep 1665383 = 2498075) B2498075
theorem B2813089 : Blo 1108626 2813089 := bstep (se 2 (by rfl) ⟨1054908, by rfl⟩ : syracuseStep 2813089 = 2109817) B2109817
theorem B1666715 : Blo 1108626 1666715 := bstep (se 1 (by rfl) ⟨1250036, by rfl⟩ : syracuseStep 1666715 = 2500073) B2500073
theorem B1110495 : Blo 1108626 1110495 := bstep (se 1 (by rfl) ⟨832871, by rfl⟩ : syracuseStep 1110495 = 1665743) B1665743
theorem B1111455 : Blo 1108626 1111455 := bstep (se 1 (by rfl) ⟨833591, by rfl⟩ : syracuseStep 1111455 = 1667183) B1667183
theorem B2815519 : Blo 1108626 2815519 := bstep (se 1 (by rfl) ⟨2111639, by rfl⟩ : syracuseStep 2815519 = 4223279) B4223279
theorem B15172541 : Blo 1108626 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B6326855 : Blo 1108626 6326855 := bstep (se 1 (by rfl) ⟨4745141, by rfl⟩ : syracuseStep 6326855 = 9490283) B9490283
theorem B96013673 : Blo 1108626 96013673 := bstep (se 2 (by rfl) ⟨36005127, by rfl⟩ : syracuseStep 96013673 = 72010255) B72010255
theorem B2494943 : Blo 1108626 2494943 := bstep (se 1 (by rfl) ⟨1871207, by rfl⟩ : syracuseStep 2494943 = 3742415) B3742415
theorem B1874171 : Blo 1108626 1874171 := bstep (se 1 (by rfl) ⟨1405628, by rfl⟩ : syracuseStep 1874171 = 2811257) B2811257
theorem B3750785 : Blo 1108626 3750785 := bstep (se 2 (by rfl) ⟨1406544, by rfl⟩ : syracuseStep 3750785 = 2813089) B2813089
theorem B3751595 : Blo 1108626 3751595 := bstep (se 1 (by rfl) ⟨2813696, by rfl⟩ : syracuseStep 3751595 = 5627393) B5627393
theorem B25673399 : Blo 1108626 25673399 := bstep (se 1 (by rfl) ⟨19255049, by rfl⟩ : syracuseStep 25673399 = 38510099) B38510099
theorem B3754025 : Blo 1108626 3754025 := bstep (se 2 (by rfl) ⟨1407759, by rfl⟩ : syracuseStep 3754025 = 2815519) B2815519
theorem B5330387 : Blo 1108626 5330387 := bstep (se 1 (by rfl) ⟨3997790, by rfl⟩ : syracuseStep 5330387 = 7995581) B7995581
theorem B4742783 : Blo 1108626 4742783 := bstep (se 1 (by rfl) ⟨3557087, by rfl⟩ : syracuseStep 4742783 = 7114175) B7114175
theorem B1663847 : Blo 1108626 1663847 := bstep (se 1 (by rfl) ⟨1247885, by rfl⟩ : syracuseStep 1663847 = 2495771) B2495771
theorem B1664423 : Blo 1108626 1664423 := bstep (se 1 (by rfl) ⟨1248317, by rfl⟩ : syracuseStep 1664423 = 2496635) B2496635
theorem B43312967 : Blo 1108626 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B10677413 : Blo 1108626 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B1110255 : Blo 1108626 1110255 := bstep (se 1 (by rfl) ⟨832691, by rfl⟩ : syracuseStep 1110255 = 1665383) B1665383
theorem B1111143 : Blo 1108626 1111143 := bstep (se 1 (by rfl) ⟨833357, by rfl⟩ : syracuseStep 1111143 = 1666715) B1666715
theorem B1407719 : Blo 1108626 1407719 := bstep (se 1 (by rfl) ⟨1055789, by rfl⟩ : syracuseStep 1407719 = 2111579) B2111579
theorem B1249447 : Blo 1108626 1249447 := bstep (se 1 (by rfl) ⟨937085, by rfl⟩ : syracuseStep 1249447 = 1874171) B1874171
theorem B28875311 : Blo 1108626 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B7118275 : Blo 1108626 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B2500523 : Blo 1108626 2500523 := bstep (se 1 (by rfl) ⟨1875392, by rfl⟩ : syracuseStep 2500523 = 3750785) B3750785
theorem B2501063 : Blo 1108626 2501063 := bstep (se 1 (by rfl) ⟨1875797, by rfl⟩ : syracuseStep 2501063 = 3751595) B3751595
theorem B17115599 : Blo 1108626 17115599 := bstep (se 1 (by rfl) ⟨12836699, by rfl⟩ : syracuseStep 17115599 = 25673399) B25673399
theorem B2502683 : Blo 1108626 2502683 := bstep (se 1 (by rfl) ⟨1877012, by rfl⟩ : syracuseStep 2502683 = 3754025) B3754025
theorem B64009115 : Blo 1108626 64009115 := bstep (se 1 (by rfl) ⟨48006836, by rfl⟩ : syracuseStep 64009115 = 96013673) B96013673
theorem B3553591 : Blo 1108626 3553591 := bstep (se 1 (by rfl) ⟨2665193, by rfl⟩ : syracuseStep 3553591 = 5330387) B5330387
theorem B3161855 : Blo 1108626 3161855 := bstep (se 1 (by rfl) ⟨2371391, by rfl⟩ : syracuseStep 3161855 = 4742783) B4742783
theorem B3753917 : Blo 1108626 3753917 := bstep (se 3 (by rfl) ⟨703859, by rfl⟩ : syracuseStep 3753917 = 1407719) B1407719
theorem B10115027 : Blo 1108626 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B4217903 : Blo 1108626 4217903 := bstep (se 1 (by rfl) ⟨3163427, by rfl⟩ : syracuseStep 4217903 = 6326855) B6326855
theorem B1663295 : Blo 1108626 1663295 := bstep (se 1 (by rfl) ⟨1247471, by rfl⟩ : syracuseStep 1663295 = 2494943) B2494943
theorem B1109231 : Blo 1108626 1109231 := bstep (se 1 (by rfl) ⟨831923, by rfl⟩ : syracuseStep 1109231 = 1663847) B1663847
theorem B1109615 : Blo 1108626 1109615 := bstep (se 1 (by rfl) ⟨832211, by rfl⟩ : syracuseStep 1109615 = 1664423) B1664423
theorem B11410399 : Blo 1108626 11410399 := bstep (se 1 (by rfl) ⟨8557799, by rfl⟩ : syracuseStep 11410399 = 17115599) B17115599
theorem B42672743 : Blo 1108626 42672743 := bstep (se 1 (by rfl) ⟨32004557, by rfl⟩ : syracuseStep 42672743 = 64009115) B64009115
theorem B8431613 : Blo 1108626 8431613 := bstep (se 3 (by rfl) ⟨1580927, by rfl⟩ : syracuseStep 8431613 = 3161855) B3161855
theorem B2502611 : Blo 1108626 2502611 := bstep (se 1 (by rfl) ⟨1876958, by rfl⟩ : syracuseStep 2502611 = 3753917) B3753917
theorem B19250207 : Blo 1108626 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B4738121 : Blo 1108626 4738121 := bstep (se 2 (by rfl) ⟨1776795, by rfl⟩ : syracuseStep 4738121 = 3553591) B3553591
theorem B9491033 : Blo 1108626 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B6743351 : Blo 1108626 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B2811935 : Blo 1108626 2811935 := bstep (se 1 (by rfl) ⟨2108951, by rfl⟩ : syracuseStep 2811935 = 4217903) B4217903
theorem B1108863 : Blo 1108626 1108863 := bstep (se 1 (by rfl) ⟨831647, by rfl⟩ : syracuseStep 1108863 = 1663295) B1663295
theorem B1665929 : Blo 1108626 1665929 := bstep (se 2 (by rfl) ⟨624723, by rfl⟩ : syracuseStep 1665929 = 1249447) B1249447
theorem B1667015 : Blo 1108626 1667015 := bstep (se 1 (by rfl) ⟨1250261, by rfl⟩ : syracuseStep 1667015 = 2500523) B2500523
theorem B1667375 : Blo 1108626 1667375 := bstep (se 1 (by rfl) ⟨1250531, by rfl⟩ : syracuseStep 1667375 = 2501063) B2501063
theorem B1668455 : Blo 1108626 1668455 := bstep (se 1 (by rfl) ⟨1251341, by rfl⟩ : syracuseStep 1668455 = 2502683) B2502683
theorem B6327355 : Blo 1108626 6327355 := bstep (se 1 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 6327355 = 9491033) B9491033
theorem B60855461 : Blo 1108626 60855461 := bstep (se 4 (by rfl) ⟨5705199, by rfl⟩ : syracuseStep 60855461 = 11410399) B11410399
theorem B28448495 : Blo 1108626 28448495 := bstep (se 1 (by rfl) ⟨21336371, by rfl⟩ : syracuseStep 28448495 = 42672743) B42672743
theorem B4495567 : Blo 1108626 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B1874623 : Blo 1108626 1874623 := bstep (se 1 (by rfl) ⟨1405967, by rfl⟩ : syracuseStep 1874623 = 2811935) B2811935
theorem B3158747 : Blo 1108626 3158747 := bstep (se 1 (by rfl) ⟨2369060, by rfl⟩ : syracuseStep 3158747 = 4738121) B4738121
theorem B5621075 : Blo 1108626 5621075 := bstep (se 1 (by rfl) ⟨4215806, by rfl⟩ : syracuseStep 5621075 = 8431613) B8431613
theorem B12833471 : Blo 1108626 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B1110619 : Blo 1108626 1110619 := bstep (se 1 (by rfl) ⟨832964, by rfl⟩ : syracuseStep 1110619 = 1665929) B1665929
theorem B1111343 : Blo 1108626 1111343 := bstep (se 1 (by rfl) ⟨833507, by rfl⟩ : syracuseStep 1111343 = 1667015) B1667015
theorem B1668407 : Blo 1108626 1668407 := bstep (se 1 (by rfl) ⟨1251305, by rfl⟩ : syracuseStep 1668407 = 2502611) B2502611
theorem B1111583 : Blo 1108626 1111583 := bstep (se 1 (by rfl) ⟨833687, by rfl⟩ : syracuseStep 1111583 = 1667375) B1667375
theorem B1112303 : Blo 1108626 1112303 := bstep (se 1 (by rfl) ⟨834227, by rfl⟩ : syracuseStep 1112303 = 1668455) B1668455
theorem B8555647 : Blo 1108626 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B40570307 : Blo 1108626 40570307 := bstep (se 1 (by rfl) ⟨30427730, by rfl⟩ : syracuseStep 40570307 = 60855461) B60855461
theorem B2105831 : Blo 1108626 2105831 := bstep (se 1 (by rfl) ⟨1579373, by rfl⟩ : syracuseStep 2105831 = 3158747) B3158747
theorem B2499497 : Blo 1108626 2499497 := bstep (se 2 (by rfl) ⟨937311, by rfl⟩ : syracuseStep 2499497 = 1874623) B1874623
theorem B3747383 : Blo 1108626 3747383 := bstep (se 1 (by rfl) ⟨2810537, by rfl⟩ : syracuseStep 3747383 = 5621075) B5621075
theorem B8436473 : Blo 1108626 8436473 := bstep (se 2 (by rfl) ⟨3163677, by rfl⟩ : syracuseStep 8436473 = 6327355) B6327355
theorem B18965663 : Blo 1108626 18965663 := bstep (se 1 (by rfl) ⟨14224247, by rfl⟩ : syracuseStep 18965663 = 28448495) B28448495
theorem B5994089 : Blo 1108626 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B1112271 : Blo 1108626 1112271 := bstep (se 1 (by rfl) ⟨834203, by rfl⟩ : syracuseStep 1112271 = 1668407) B1668407
theorem B11407529 : Blo 1108626 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B2498255 : Blo 1108626 2498255 := bstep (se 1 (by rfl) ⟨1873691, by rfl⟩ : syracuseStep 2498255 = 3747383) B3747383
theorem B27046871 : Blo 1108626 27046871 := bstep (se 1 (by rfl) ⟨20285153, by rfl⟩ : syracuseStep 27046871 = 40570307) B40570307
theorem B5624315 : Blo 1108626 5624315 := bstep (se 1 (by rfl) ⟨4218236, by rfl⟩ : syracuseStep 5624315 = 8436473) B8436473
theorem B1403887 : Blo 1108626 1403887 := bstep (se 1 (by rfl) ⟨1052915, by rfl⟩ : syracuseStep 1403887 = 2105831) B2105831
theorem B1666331 : Blo 1108626 1666331 := bstep (se 1 (by rfl) ⟨1249748, by rfl⟩ : syracuseStep 1666331 = 2499497) B2499497
theorem B12643775 : Blo 1108626 12643775 := bstep (se 1 (by rfl) ⟨9482831, by rfl⟩ : syracuseStep 12643775 = 18965663) B18965663
theorem B3996059 : Blo 1108626 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B7605019 : Blo 1108626 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B1871849 : Blo 1108626 1871849 := bstep (se 2 (by rfl) ⟨701943, by rfl⟩ : syracuseStep 1871849 = 1403887) B1403887
theorem B10656157 : Blo 1108626 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B8429183 : Blo 1108626 8429183 := bstep (se 1 (by rfl) ⟨6321887, by rfl⟩ : syracuseStep 8429183 = 12643775) B12643775
theorem B18031247 : Blo 1108626 18031247 := bstep (se 1 (by rfl) ⟨13523435, by rfl⟩ : syracuseStep 18031247 = 27046871) B27046871
theorem B3749543 : Blo 1108626 3749543 := bstep (se 1 (by rfl) ⟨2812157, by rfl⟩ : syracuseStep 3749543 = 5624315) B5624315
theorem B1665503 : Blo 1108626 1665503 := bstep (se 1 (by rfl) ⟨1249127, by rfl⟩ : syracuseStep 1665503 = 2498255) B2498255
theorem B1110887 : Blo 1108626 1110887 := bstep (se 1 (by rfl) ⟨833165, by rfl⟩ : syracuseStep 1110887 = 1666331) B1666331
theorem B1247899 : Blo 1108626 1247899 := bstep (se 1 (by rfl) ⟨935924, by rfl⟩ : syracuseStep 1247899 = 1871849) B1871849
theorem B2499695 : Blo 1108626 2499695 := bstep (se 1 (by rfl) ⟨1874771, by rfl⟩ : syracuseStep 2499695 = 3749543) B3749543
theorem B5619455 : Blo 1108626 5619455 := bstep (se 1 (by rfl) ⟨4214591, by rfl⟩ : syracuseStep 5619455 = 8429183) B8429183
theorem B14208209 : Blo 1108626 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B40560101 : Blo 1108626 40560101 := bstep (se 4 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 40560101 = 7605019) B7605019
theorem B12020831 : Blo 1108626 12020831 := bstep (se 1 (by rfl) ⟨9015623, by rfl⟩ : syracuseStep 12020831 = 18031247) B18031247
theorem B1110335 : Blo 1108626 1110335 := bstep (se 1 (by rfl) ⟨832751, by rfl⟩ : syracuseStep 1110335 = 1665503) B1665503
theorem B9472139 : Blo 1108626 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B27040067 : Blo 1108626 27040067 := bstep (se 1 (by rfl) ⟨20280050, by rfl⟩ : syracuseStep 27040067 = 40560101) B40560101
theorem B3746303 : Blo 1108626 3746303 := bstep (se 1 (by rfl) ⟨2809727, by rfl⟩ : syracuseStep 3746303 = 5619455) B5619455
theorem B8013887 : Blo 1108626 8013887 := bstep (se 1 (by rfl) ⟨6010415, by rfl⟩ : syracuseStep 8013887 = 12020831) B12020831
theorem B1663865 : Blo 1108626 1663865 := bstep (se 2 (by rfl) ⟨623949, by rfl⟩ : syracuseStep 1663865 = 1247899) B1247899
theorem B1666463 : Blo 1108626 1666463 := bstep (se 1 (by rfl) ⟨1249847, by rfl⟩ : syracuseStep 1666463 = 2499695) B2499695
theorem B5342591 : Blo 1108626 5342591 := bstep (se 1 (by rfl) ⟨4006943, by rfl⟩ : syracuseStep 5342591 = 8013887) B8013887
theorem B18026711 : Blo 1108626 18026711 := bstep (se 1 (by rfl) ⟨13520033, by rfl⟩ : syracuseStep 18026711 = 27040067) B27040067
theorem B2497535 : Blo 1108626 2497535 := bstep (se 1 (by rfl) ⟨1873151, by rfl⟩ : syracuseStep 2497535 = 3746303) B3746303
theorem B6314759 : Blo 1108626 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B1109243 : Blo 1108626 1109243 := bstep (se 1 (by rfl) ⟨831932, by rfl⟩ : syracuseStep 1109243 = 1663865) B1663865
theorem B1110975 : Blo 1108626 1110975 := bstep (se 1 (by rfl) ⟨833231, by rfl⟩ : syracuseStep 1110975 = 1666463) B1666463
theorem B4209839 : Blo 1108626 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B3561727 : Blo 1108626 3561727 := bstep (se 1 (by rfl) ⟨2671295, by rfl⟩ : syracuseStep 3561727 = 5342591) B5342591
theorem B12017807 : Blo 1108626 12017807 := bstep (se 1 (by rfl) ⟨9013355, by rfl⟩ : syracuseStep 12017807 = 18026711) B18026711
theorem B1665023 : Blo 1108626 1665023 := bstep (se 1 (by rfl) ⟨1248767, by rfl⟩ : syracuseStep 1665023 = 2497535) B2497535
theorem B8011871 : Blo 1108626 8011871 := bstep (se 1 (by rfl) ⟨6008903, by rfl⟩ : syracuseStep 8011871 = 12017807) B12017807
theorem B2806559 : Blo 1108626 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B1110015 : Blo 1108626 1110015 := bstep (se 1 (by rfl) ⟨832511, by rfl⟩ : syracuseStep 1110015 = 1665023) B1665023
theorem B4748969 : Blo 1108626 4748969 := bstep (se 2 (by rfl) ⟨1780863, by rfl⟩ : syracuseStep 4748969 = 3561727) B3561727
theorem B5341247 : Blo 1108626 5341247 := bstep (se 1 (by rfl) ⟨4005935, by rfl⟩ : syracuseStep 5341247 = 8011871) B8011871
theorem B1871039 : Blo 1108626 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B3165979 : Blo 1108626 3165979 := bstep (se 1 (by rfl) ⟨2374484, by rfl⟩ : syracuseStep 3165979 = 4748969) B4748969
theorem B1247359 : Blo 1108626 1247359 := bstep (se 1 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 1247359 = 1871039) B1871039
theorem B3560831 : Blo 1108626 3560831 := bstep (se 1 (by rfl) ⟨2670623, by rfl⟩ : syracuseStep 3560831 = 5341247) B5341247
theorem B4221305 : Blo 1108626 4221305 := bstep (se 2 (by rfl) ⟨1582989, by rfl⟩ : syracuseStep 4221305 = 3165979) B3165979
theorem B2373887 : Blo 1108626 2373887 := bstep (se 1 (by rfl) ⟨1780415, by rfl⟩ : syracuseStep 2373887 = 3560831) B3560831
theorem B1663145 : Blo 1108626 1663145 := bstep (se 2 (by rfl) ⟨623679, by rfl⟩ : syracuseStep 1663145 = 1247359) B1247359
theorem B2814203 : Blo 1108626 2814203 := bstep (se 1 (by rfl) ⟨2110652, by rfl⟩ : syracuseStep 2814203 = 4221305) B4221305
theorem B1876135 : Blo 1108626 1876135 := bstep (se 1 (by rfl) ⟨1407101, by rfl⟩ : syracuseStep 1876135 = 2814203) B2814203
theorem B1582591 : Blo 1108626 1582591 := bstep (se 1 (by rfl) ⟨1186943, by rfl⟩ : syracuseStep 1582591 = 2373887) B2373887
theorem B1108763 : Blo 1108626 1108763 := bstep (se 1 (by rfl) ⟨831572, by rfl⟩ : syracuseStep 1108763 = 1663145) B1663145
theorem B2501513 : Blo 1108626 2501513 := bstep (se 2 (by rfl) ⟨938067, by rfl⟩ : syracuseStep 2501513 = 1876135) B1876135
theorem B2110121 : Blo 1108626 2110121 := bstep (se 2 (by rfl) ⟨791295, by rfl⟩ : syracuseStep 2110121 = 1582591) B1582591
theorem B1667675 : Blo 1108626 1667675 := bstep (se 1 (by rfl) ⟨1250756, by rfl⟩ : syracuseStep 1667675 = 2501513) B2501513
theorem B1406747 : Blo 1108626 1406747 := bstep (se 1 (by rfl) ⟨1055060, by rfl⟩ : syracuseStep 1406747 = 2110121) B2110121
theorem B3751325 : Blo 1108626 3751325 := bstep (se 3 (by rfl) ⟨703373, by rfl⟩ : syracuseStep 3751325 = 1406747) B1406747
theorem B1111783 : Blo 1108626 1111783 := bstep (se 1 (by rfl) ⟨833837, by rfl⟩ : syracuseStep 1111783 = 1667675) B1667675
theorem B2500883 : Blo 1108626 2500883 := bstep (se 1 (by rfl) ⟨1875662, by rfl⟩ : syracuseStep 2500883 = 3751325) B3751325
theorem B1667255 : Blo 1108626 1667255 := bstep (se 1 (by rfl) ⟨1250441, by rfl⟩ : syracuseStep 1667255 = 2500883) B2500883
theorem B1111503 : Blo 1108626 1111503 := bstep (se 1 (by rfl) ⟨833627, by rfl⟩ : syracuseStep 1111503 = 1667255) B1667255

theorem C0 (j : ℕ) (h1 : 277156 ≤ j) (h2 : j ≤ 277855) : Blo 1108626 (4 * j + 3) := by
  interval_cases j
  · exact B1108627
  · exact B1108631
  · exact B1108635
  · exact B1108639
  · exact B1108643
  · exact B1108647
  · exact B1108651
  · exact B1108655
  · exact B1108659
  · exact B1108663
  · exact B1108667
  · exact B1108671
  · exact B1108675
  · exact B1108679
  · exact B1108683
  · exact B1108687
  · exact B1108691
  · exact B1108695
  · exact B1108699
  · exact B1108703
  · exact B1108707
  · exact B1108711
  · exact B1108715
  · exact B1108719
  · exact B1108723
  · exact B1108727
  · exact B1108731
  · exact B1108735
  · exact B1108739
  · exact B1108743
  · exact B1108747
  · exact B1108751
  · exact B1108755
  · exact B1108759
  · exact B1108763
  · exact B1108767
  · exact B1108771
  · exact B1108775
  · exact B1108779
  · exact B1108783
  · exact B1108787
  · exact B1108791
  · exact B1108795
  · exact B1108799
  · exact B1108803
  · exact B1108807
  · exact B1108811
  · exact B1108815
  · exact B1108819
  · exact B1108823
  · exact B1108827
  · exact B1108831
  · exact B1108835
  · exact B1108839
  · exact B1108843
  · exact B1108847
  · exact B1108851
  · exact B1108855
  · exact B1108859
  · exact B1108863
  · exact B1108867
  · exact B1108871
  · exact B1108875
  · exact B1108879
  · exact B1108883
  · exact B1108887
  · exact B1108891
  · exact B1108895
  · exact B1108899
  · exact B1108903
  · exact B1108907
  · exact B1108911
  · exact B1108915
  · exact B1108919
  · exact B1108923
  · exact B1108927
  · exact B1108931
  · exact B1108935
  · exact B1108939
  · exact B1108943
  · exact B1108947
  · exact B1108951
  · exact B1108955
  · exact B1108959
  · exact B1108963
  · exact B1108967
  · exact B1108971
  · exact B1108975
  · exact B1108979
  · exact B1108983
  · exact B1108987
  · exact B1108991
  · exact B1108995
  · exact B1108999
  · exact B1109003
  · exact B1109007
  · exact B1109011
  · exact B1109015
  · exact B1109019
  · exact B1109023
  · exact B1109027
  · exact B1109031
  · exact B1109035
  · exact B1109039
  · exact B1109043
  · exact B1109047
  · exact B1109051
  · exact B1109055
  · exact B1109059
  · exact B1109063
  · exact B1109067
  · exact B1109071
  · exact B1109075
  · exact B1109079
  · exact B1109083
  · exact B1109087
  · exact B1109091
  · exact B1109095
  · exact B1109099
  · exact B1109103
  · exact B1109107
  · exact B1109111
  · exact B1109115
  · exact B1109119
  · exact B1109123
  · exact B1109127
  · exact B1109131
  · exact B1109135
  · exact B1109139
  · exact B1109143
  · exact B1109147
  · exact B1109151
  · exact B1109155
  · exact B1109159
  · exact B1109163
  · exact B1109167
  · exact B1109171
  · exact B1109175
  · exact B1109179
  · exact B1109183
  · exact B1109187
  · exact B1109191
  · exact B1109195
  · exact B1109199
  · exact B1109203
  · exact B1109207
  · exact B1109211
  · exact B1109215
  · exact B1109219
  · exact B1109223
  · exact B1109227
  · exact B1109231
  · exact B1109235
  · exact B1109239
  · exact B1109243
  · exact B1109247
  · exact B1109251
  · exact B1109255
  · exact B1109259
  · exact B1109263
  · exact B1109267
  · exact B1109271
  · exact B1109275
  · exact B1109279
  · exact B1109283
  · exact B1109287
  · exact B1109291
  · exact B1109295
  · exact B1109299
  · exact B1109303
  · exact B1109307
  · exact B1109311
  · exact B1109315
  · exact B1109319
  · exact B1109323
  · exact B1109327
  · exact B1109331
  · exact B1109335
  · exact B1109339
  · exact B1109343
  · exact B1109347
  · exact B1109351
  · exact B1109355
  · exact B1109359
  · exact B1109363
  · exact B1109367
  · exact B1109371
  · exact B1109375
  · exact B1109379
  · exact B1109383
  · exact B1109387
  · exact B1109391
  · exact B1109395
  · exact B1109399
  · exact B1109403
  · exact B1109407
  · exact B1109411
  · exact B1109415
  · exact B1109419
  · exact B1109423
  · exact B1109427
  · exact B1109431
  · exact B1109435
  · exact B1109439
  · exact B1109443
  · exact B1109447
  · exact B1109451
  · exact B1109455
  · exact B1109459
  · exact B1109463
  · exact B1109467
  · exact B1109471
  · exact B1109475
  · exact B1109479
  · exact B1109483
  · exact B1109487
  · exact B1109491
  · exact B1109495
  · exact B1109499
  · exact B1109503
  · exact B1109507
  · exact B1109511
  · exact B1109515
  · exact B1109519
  · exact B1109523
  · exact B1109527
  · exact B1109531
  · exact B1109535
  · exact B1109539
  · exact B1109543
  · exact B1109547
  · exact B1109551
  · exact B1109555
  · exact B1109559
  · exact B1109563
  · exact B1109567
  · exact B1109571
  · exact B1109575
  · exact B1109579
  · exact B1109583
  · exact B1109587
  · exact B1109591
  · exact B1109595
  · exact B1109599
  · exact B1109603
  · exact B1109607
  · exact B1109611
  · exact B1109615
  · exact B1109619
  · exact B1109623
  · exact B1109627
  · exact B1109631
  · exact B1109635
  · exact B1109639
  · exact B1109643
  · exact B1109647
  · exact B1109651
  · exact B1109655
  · exact B1109659
  · exact B1109663
  · exact B1109667
  · exact B1109671
  · exact B1109675
  · exact B1109679
  · exact B1109683
  · exact B1109687
  · exact B1109691
  · exact B1109695
  · exact B1109699
  · exact B1109703
  · exact B1109707
  · exact B1109711
  · exact B1109715
  · exact B1109719
  · exact B1109723
  · exact B1109727
  · exact B1109731
  · exact B1109735
  · exact B1109739
  · exact B1109743
  · exact B1109747
  · exact B1109751
  · exact B1109755
  · exact B1109759
  · exact B1109763
  · exact B1109767
  · exact B1109771
  · exact B1109775
  · exact B1109779
  · exact B1109783
  · exact B1109787
  · exact B1109791
  · exact B1109795
  · exact B1109799
  · exact B1109803
  · exact B1109807
  · exact B1109811
  · exact B1109815
  · exact B1109819
  · exact B1109823
  · exact B1109827
  · exact B1109831
  · exact B1109835
  · exact B1109839
  · exact B1109843
  · exact B1109847
  · exact B1109851
  · exact B1109855
  · exact B1109859
  · exact B1109863
  · exact B1109867
  · exact B1109871
  · exact B1109875
  · exact B1109879
  · exact B1109883
  · exact B1109887
  · exact B1109891
  · exact B1109895
  · exact B1109899
  · exact B1109903
  · exact B1109907
  · exact B1109911
  · exact B1109915
  · exact B1109919
  · exact B1109923
  · exact B1109927
  · exact B1109931
  · exact B1109935
  · exact B1109939
  · exact B1109943
  · exact B1109947
  · exact B1109951
  · exact B1109955
  · exact B1109959
  · exact B1109963
  · exact B1109967
  · exact B1109971
  · exact B1109975
  · exact B1109979
  · exact B1109983
  · exact B1109987
  · exact B1109991
  · exact B1109995
  · exact B1109999
  · exact B1110003
  · exact B1110007
  · exact B1110011
  · exact B1110015
  · exact B1110019
  · exact B1110023
  · exact B1110027
  · exact B1110031
  · exact B1110035
  · exact B1110039
  · exact B1110043
  · exact B1110047
  · exact B1110051
  · exact B1110055
  · exact B1110059
  · exact B1110063
  · exact B1110067
  · exact B1110071
  · exact B1110075
  · exact B1110079
  · exact B1110083
  · exact B1110087
  · exact B1110091
  · exact B1110095
  · exact B1110099
  · exact B1110103
  · exact B1110107
  · exact B1110111
  · exact B1110115
  · exact B1110119
  · exact B1110123
  · exact B1110127
  · exact B1110131
  · exact B1110135
  · exact B1110139
  · exact B1110143
  · exact B1110147
  · exact B1110151
  · exact B1110155
  · exact B1110159
  · exact B1110163
  · exact B1110167
  · exact B1110171
  · exact B1110175
  · exact B1110179
  · exact B1110183
  · exact B1110187
  · exact B1110191
  · exact B1110195
  · exact B1110199
  · exact B1110203
  · exact B1110207
  · exact B1110211
  · exact B1110215
  · exact B1110219
  · exact B1110223
  · exact B1110227
  · exact B1110231
  · exact B1110235
  · exact B1110239
  · exact B1110243
  · exact B1110247
  · exact B1110251
  · exact B1110255
  · exact B1110259
  · exact B1110263
  · exact B1110267
  · exact B1110271
  · exact B1110275
  · exact B1110279
  · exact B1110283
  · exact B1110287
  · exact B1110291
  · exact B1110295
  · exact B1110299
  · exact B1110303
  · exact B1110307
  · exact B1110311
  · exact B1110315
  · exact B1110319
  · exact B1110323
  · exact B1110327
  · exact B1110331
  · exact B1110335
  · exact B1110339
  · exact B1110343
  · exact B1110347
  · exact B1110351
  · exact B1110355
  · exact B1110359
  · exact B1110363
  · exact B1110367
  · exact B1110371
  · exact B1110375
  · exact B1110379
  · exact B1110383
  · exact B1110387
  · exact B1110391
  · exact B1110395
  · exact B1110399
  · exact B1110403
  · exact B1110407
  · exact B1110411
  · exact B1110415
  · exact B1110419
  · exact B1110423
  · exact B1110427
  · exact B1110431
  · exact B1110435
  · exact B1110439
  · exact B1110443
  · exact B1110447
  · exact B1110451
  · exact B1110455
  · exact B1110459
  · exact B1110463
  · exact B1110467
  · exact B1110471
  · exact B1110475
  · exact B1110479
  · exact B1110483
  · exact B1110487
  · exact B1110491
  · exact B1110495
  · exact B1110499
  · exact B1110503
  · exact B1110507
  · exact B1110511
  · exact B1110515
  · exact B1110519
  · exact B1110523
  · exact B1110527
  · exact B1110531
  · exact B1110535
  · exact B1110539
  · exact B1110543
  · exact B1110547
  · exact B1110551
  · exact B1110555
  · exact B1110559
  · exact B1110563
  · exact B1110567
  · exact B1110571
  · exact B1110575
  · exact B1110579
  · exact B1110583
  · exact B1110587
  · exact B1110591
  · exact B1110595
  · exact B1110599
  · exact B1110603
  · exact B1110607
  · exact B1110611
  · exact B1110615
  · exact B1110619
  · exact B1110623
  · exact B1110627
  · exact B1110631
  · exact B1110635
  · exact B1110639
  · exact B1110643
  · exact B1110647
  · exact B1110651
  · exact B1110655
  · exact B1110659
  · exact B1110663
  · exact B1110667
  · exact B1110671
  · exact B1110675
  · exact B1110679
  · exact B1110683
  · exact B1110687
  · exact B1110691
  · exact B1110695
  · exact B1110699
  · exact B1110703
  · exact B1110707
  · exact B1110711
  · exact B1110715
  · exact B1110719
  · exact B1110723
  · exact B1110727
  · exact B1110731
  · exact B1110735
  · exact B1110739
  · exact B1110743
  · exact B1110747
  · exact B1110751
  · exact B1110755
  · exact B1110759
  · exact B1110763
  · exact B1110767
  · exact B1110771
  · exact B1110775
  · exact B1110779
  · exact B1110783
  · exact B1110787
  · exact B1110791
  · exact B1110795
  · exact B1110799
  · exact B1110803
  · exact B1110807
  · exact B1110811
  · exact B1110815
  · exact B1110819
  · exact B1110823
  · exact B1110827
  · exact B1110831
  · exact B1110835
  · exact B1110839
  · exact B1110843
  · exact B1110847
  · exact B1110851
  · exact B1110855
  · exact B1110859
  · exact B1110863
  · exact B1110867
  · exact B1110871
  · exact B1110875
  · exact B1110879
  · exact B1110883
  · exact B1110887
  · exact B1110891
  · exact B1110895
  · exact B1110899
  · exact B1110903
  · exact B1110907
  · exact B1110911
  · exact B1110915
  · exact B1110919
  · exact B1110923
  · exact B1110927
  · exact B1110931
  · exact B1110935
  · exact B1110939
  · exact B1110943
  · exact B1110947
  · exact B1110951
  · exact B1110955
  · exact B1110959
  · exact B1110963
  · exact B1110967
  · exact B1110971
  · exact B1110975
  · exact B1110979
  · exact B1110983
  · exact B1110987
  · exact B1110991
  · exact B1110995
  · exact B1110999
  · exact B1111003
  · exact B1111007
  · exact B1111011
  · exact B1111015
  · exact B1111019
  · exact B1111023
  · exact B1111027
  · exact B1111031
  · exact B1111035
  · exact B1111039
  · exact B1111043
  · exact B1111047
  · exact B1111051
  · exact B1111055
  · exact B1111059
  · exact B1111063
  · exact B1111067
  · exact B1111071
  · exact B1111075
  · exact B1111079
  · exact B1111083
  · exact B1111087
  · exact B1111091
  · exact B1111095
  · exact B1111099
  · exact B1111103
  · exact B1111107
  · exact B1111111
  · exact B1111115
  · exact B1111119
  · exact B1111123
  · exact B1111127
  · exact B1111131
  · exact B1111135
  · exact B1111139
  · exact B1111143
  · exact B1111147
  · exact B1111151
  · exact B1111155
  · exact B1111159
  · exact B1111163
  · exact B1111167
  · exact B1111171
  · exact B1111175
  · exact B1111179
  · exact B1111183
  · exact B1111187
  · exact B1111191
  · exact B1111195
  · exact B1111199
  · exact B1111203
  · exact B1111207
  · exact B1111211
  · exact B1111215
  · exact B1111219
  · exact B1111223
  · exact B1111227
  · exact B1111231
  · exact B1111235
  · exact B1111239
  · exact B1111243
  · exact B1111247
  · exact B1111251
  · exact B1111255
  · exact B1111259
  · exact B1111263
  · exact B1111267
  · exact B1111271
  · exact B1111275
  · exact B1111279
  · exact B1111283
  · exact B1111287
  · exact B1111291
  · exact B1111295
  · exact B1111299
  · exact B1111303
  · exact B1111307
  · exact B1111311
  · exact B1111315
  · exact B1111319
  · exact B1111323
  · exact B1111327
  · exact B1111331
  · exact B1111335
  · exact B1111339
  · exact B1111343
  · exact B1111347
  · exact B1111351
  · exact B1111355
  · exact B1111359
  · exact B1111363
  · exact B1111367
  · exact B1111371
  · exact B1111375
  · exact B1111379
  · exact B1111383
  · exact B1111387
  · exact B1111391
  · exact B1111395
  · exact B1111399
  · exact B1111403
  · exact B1111407
  · exact B1111411
  · exact B1111415
  · exact B1111419
  · exact B1111423

theorem C1 (j : ℕ) (h1 : 277856 ≤ j) (h2 : j ≤ 278155) : Blo 1108626 (4 * j + 3) := by
  interval_cases j
  · exact B1111427
  · exact B1111431
  · exact B1111435
  · exact B1111439
  · exact B1111443
  · exact B1111447
  · exact B1111451
  · exact B1111455
  · exact B1111459
  · exact B1111463
  · exact B1111467
  · exact B1111471
  · exact B1111475
  · exact B1111479
  · exact B1111483
  · exact B1111487
  · exact B1111491
  · exact B1111495
  · exact B1111499
  · exact B1111503
  · exact B1111507
  · exact B1111511
  · exact B1111515
  · exact B1111519
  · exact B1111523
  · exact B1111527
  · exact B1111531
  · exact B1111535
  · exact B1111539
  · exact B1111543
  · exact B1111547
  · exact B1111551
  · exact B1111555
  · exact B1111559
  · exact B1111563
  · exact B1111567
  · exact B1111571
  · exact B1111575
  · exact B1111579
  · exact B1111583
  · exact B1111587
  · exact B1111591
  · exact B1111595
  · exact B1111599
  · exact B1111603
  · exact B1111607
  · exact B1111611
  · exact B1111615
  · exact B1111619
  · exact B1111623
  · exact B1111627
  · exact B1111631
  · exact B1111635
  · exact B1111639
  · exact B1111643
  · exact B1111647
  · exact B1111651
  · exact B1111655
  · exact B1111659
  · exact B1111663
  · exact B1111667
  · exact B1111671
  · exact B1111675
  · exact B1111679
  · exact B1111683
  · exact B1111687
  · exact B1111691
  · exact B1111695
  · exact B1111699
  · exact B1111703
  · exact B1111707
  · exact B1111711
  · exact B1111715
  · exact B1111719
  · exact B1111723
  · exact B1111727
  · exact B1111731
  · exact B1111735
  · exact B1111739
  · exact B1111743
  · exact B1111747
  · exact B1111751
  · exact B1111755
  · exact B1111759
  · exact B1111763
  · exact B1111767
  · exact B1111771
  · exact B1111775
  · exact B1111779
  · exact B1111783
  · exact B1111787
  · exact B1111791
  · exact B1111795
  · exact B1111799
  · exact B1111803
  · exact B1111807
  · exact B1111811
  · exact B1111815
  · exact B1111819
  · exact B1111823
  · exact B1111827
  · exact B1111831
  · exact B1111835
  · exact B1111839
  · exact B1111843
  · exact B1111847
  · exact B1111851
  · exact B1111855
  · exact B1111859
  · exact B1111863
  · exact B1111867
  · exact B1111871
  · exact B1111875
  · exact B1111879
  · exact B1111883
  · exact B1111887
  · exact B1111891
  · exact B1111895
  · exact B1111899
  · exact B1111903
  · exact B1111907
  · exact B1111911
  · exact B1111915
  · exact B1111919
  · exact B1111923
  · exact B1111927
  · exact B1111931
  · exact B1111935
  · exact B1111939
  · exact B1111943
  · exact B1111947
  · exact B1111951
  · exact B1111955
  · exact B1111959
  · exact B1111963
  · exact B1111967
  · exact B1111971
  · exact B1111975
  · exact B1111979
  · exact B1111983
  · exact B1111987
  · exact B1111991
  · exact B1111995
  · exact B1111999
  · exact B1112003
  · exact B1112007
  · exact B1112011
  · exact B1112015
  · exact B1112019
  · exact B1112023
  · exact B1112027
  · exact B1112031
  · exact B1112035
  · exact B1112039
  · exact B1112043
  · exact B1112047
  · exact B1112051
  · exact B1112055
  · exact B1112059
  · exact B1112063
  · exact B1112067
  · exact B1112071
  · exact B1112075
  · exact B1112079
  · exact B1112083
  · exact B1112087
  · exact B1112091
  · exact B1112095
  · exact B1112099
  · exact B1112103
  · exact B1112107
  · exact B1112111
  · exact B1112115
  · exact B1112119
  · exact B1112123
  · exact B1112127
  · exact B1112131
  · exact B1112135
  · exact B1112139
  · exact B1112143
  · exact B1112147
  · exact B1112151
  · exact B1112155
  · exact B1112159
  · exact B1112163
  · exact B1112167
  · exact B1112171
  · exact B1112175
  · exact B1112179
  · exact B1112183
  · exact B1112187
  · exact B1112191
  · exact B1112195
  · exact B1112199
  · exact B1112203
  · exact B1112207
  · exact B1112211
  · exact B1112215
  · exact B1112219
  · exact B1112223
  · exact B1112227
  · exact B1112231
  · exact B1112235
  · exact B1112239
  · exact B1112243
  · exact B1112247
  · exact B1112251
  · exact B1112255
  · exact B1112259
  · exact B1112263
  · exact B1112267
  · exact B1112271
  · exact B1112275
  · exact B1112279
  · exact B1112283
  · exact B1112287
  · exact B1112291
  · exact B1112295
  · exact B1112299
  · exact B1112303
  · exact B1112307
  · exact B1112311
  · exact B1112315
  · exact B1112319
  · exact B1112323
  · exact B1112327
  · exact B1112331
  · exact B1112335
  · exact B1112339
  · exact B1112343
  · exact B1112347
  · exact B1112351
  · exact B1112355
  · exact B1112359
  · exact B1112363
  · exact B1112367
  · exact B1112371
  · exact B1112375
  · exact B1112379
  · exact B1112383
  · exact B1112387
  · exact B1112391
  · exact B1112395
  · exact B1112399
  · exact B1112403
  · exact B1112407
  · exact B1112411
  · exact B1112415
  · exact B1112419
  · exact B1112423
  · exact B1112427
  · exact B1112431
  · exact B1112435
  · exact B1112439
  · exact B1112443
  · exact B1112447
  · exact B1112451
  · exact B1112455
  · exact B1112459
  · exact B1112463
  · exact B1112467
  · exact B1112471
  · exact B1112475
  · exact B1112479
  · exact B1112483
  · exact B1112487
  · exact B1112491
  · exact B1112495
  · exact B1112499
  · exact B1112503
  · exact B1112507
  · exact B1112511
  · exact B1112515
  · exact B1112519
  · exact B1112523
  · exact B1112527
  · exact B1112531
  · exact B1112535
  · exact B1112539
  · exact B1112543
  · exact B1112547
  · exact B1112551
  · exact B1112555
  · exact B1112559
  · exact B1112563
  · exact B1112567
  · exact B1112571
  · exact B1112575
  · exact B1112579
  · exact B1112583
  · exact B1112587
  · exact B1112591
  · exact B1112595
  · exact B1112599
  · exact B1112603
  · exact B1112607
  · exact B1112611
  · exact B1112615
  · exact B1112619
  · exact B1112623

theorem solution (m : ℕ) (hlo : 1108626 ≤ m) (hhi : m ≤ 1112626) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 277156 ≤ j := by omega
    have hj2 : j ≤ 278155 := by omega
    have hb : Blo 1108626 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 277856 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
