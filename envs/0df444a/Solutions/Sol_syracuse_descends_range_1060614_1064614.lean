-- Prove2me | solution 1 for syracuse_descends_range_1060614_1064614
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:28.589059+00:00
-- url     : https://prove2.me/submissions/8cf947cf-a0fa-4d5a-8e85-0dcac1d92297

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


theorem B2392109 : Blo 1060614 2392109 := bbase (se 3 (by rfl) ⟨448520, by rfl⟩ : syracuseStep 2392109 = 897041) (by norm_num)
theorem B2555965 : Blo 1060614 2555965 := bbase (se 3 (by rfl) ⟨479243, by rfl⟩ : syracuseStep 2555965 = 958487) (by norm_num)
theorem B1343557 : Blo 1060614 1343557 := bbase (se 4 (by rfl) ⟨125958, by rfl⟩ : syracuseStep 1343557 = 251917) (by norm_num)
theorem B2687053 : Blo 1060614 2687053 := bbase (se 3 (by rfl) ⟨503822, by rfl⟩ : syracuseStep 2687053 = 1007645) (by norm_num)
theorem B1966189 : Blo 1060614 1966189 := bbase (se 3 (by rfl) ⟨368660, by rfl⟩ : syracuseStep 1966189 = 737321) (by norm_num)
theorem B2392181 : Blo 1060614 2392181 := bbase (se 5 (by rfl) ⟨112133, by rfl⟩ : syracuseStep 2392181 = 224267) (by norm_num)
theorem B2687165 : Blo 1060614 2687165 := bbase (se 3 (by rfl) ⟨503843, by rfl⟩ : syracuseStep 2687165 = 1007687) (by norm_num)
theorem B2392253 : Blo 1060614 2392253 := bbase (se 3 (by rfl) ⟨448547, by rfl⟩ : syracuseStep 2392253 = 897095) (by norm_num)
theorem B4849861 : Blo 1060614 4849861 := bbase (se 4 (by rfl) ⟨454674, by rfl⟩ : syracuseStep 4849861 = 909349) (by norm_num)
theorem B1343729 : Blo 1060614 1343729 := bbase (se 2 (by rfl) ⟨503898, by rfl⟩ : syracuseStep 1343729 = 1007797) (by norm_num)
theorem B2392325 : Blo 1060614 2392325 := bbase (se 4 (by rfl) ⟨224280, by rfl⟩ : syracuseStep 2392325 = 448561) (by norm_num)
theorem B1343785 : Blo 1060614 1343785 := bbase (se 2 (by rfl) ⟨503919, by rfl⟩ : syracuseStep 1343785 = 1007839) (by norm_num)
theorem B2392397 : Blo 1060614 2392397 := bbase (se 3 (by rfl) ⟨448574, by rfl⟩ : syracuseStep 2392397 = 897149) (by norm_num)
theorem B2687357 : Blo 1060614 2687357 := bbase (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) (by norm_num)
theorem B1343881 : Blo 1060614 1343881 := bbase (se 2 (by rfl) ⟨503955, by rfl⟩ : syracuseStep 1343881 = 1007911) (by norm_num)
theorem B1278353 : Blo 1060614 1278353 := bbase (se 2 (by rfl) ⟨479382, by rfl⟩ : syracuseStep 1278353 = 958765) (by norm_num)
theorem B2392469 : Blo 1060614 2392469 := bbase (se 6 (by rfl) ⟨56073, by rfl⟩ : syracuseStep 2392469 = 112147) (by norm_num)
theorem B2425277 : Blo 1060614 2425277 := bbase (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) (by norm_num)
theorem B2392541 : Blo 1060614 2392541 := bbase (se 3 (by rfl) ⟨448601, by rfl⟩ : syracuseStep 2392541 = 897203) (by norm_num)
theorem B3408389 : Blo 1060614 3408389 := bbase (se 4 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 3408389 = 639073) (by norm_num)
theorem B11502101 : Blo 1060614 11502101 := bbase (se 6 (by rfl) ⟨269580, by rfl⟩ : syracuseStep 11502101 = 539161) (by norm_num)
theorem B2392613 : Blo 1060614 2392613 := bbase (se 4 (by rfl) ⟨224307, by rfl⟩ : syracuseStep 2392613 = 448615) (by norm_num)
theorem B1344053 : Blo 1060614 1344053 := bbase (se 5 (by rfl) ⟨63002, by rfl⟩ : syracuseStep 1344053 = 126005) (by norm_num)
theorem B2556485 : Blo 1060614 2556485 := bbase (se 4 (by rfl) ⟨239670, by rfl⟩ : syracuseStep 2556485 = 479341) (by norm_num)
theorem B1344109 : Blo 1060614 1344109 := bbase (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) (by norm_num)
theorem B2392685 : Blo 1060614 2392685 := bbase (se 3 (by rfl) ⟨448628, by rfl⟩ : syracuseStep 2392685 = 897257) (by norm_num)
theorem B6128245 : Blo 1060614 6128245 := bbase (se 5 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 6128245 = 574523) (by norm_num)
theorem B3834485 : Blo 1060614 3834485 := bbase (se 5 (by rfl) ⟨179741, by rfl⟩ : syracuseStep 3834485 = 359483) (by norm_num)
theorem B2392757 : Blo 1060614 2392757 := bbase (se 5 (by rfl) ⟨112160, by rfl⟩ : syracuseStep 2392757 = 224321) (by norm_num)
theorem B1278661 : Blo 1060614 1278661 := bbase (se 4 (by rfl) ⟨119874, by rfl⟩ : syracuseStep 1278661 = 239749) (by norm_num)
theorem B1344205 : Blo 1060614 1344205 := bbase (se 3 (by rfl) ⟨252038, by rfl⟩ : syracuseStep 1344205 = 504077) (by norm_num)
theorem B2687701 : Blo 1060614 2687701 := bbase (se 7 (by rfl) ⟨31496, by rfl⟩ : syracuseStep 2687701 = 62993) (by norm_num)
theorem B6816469 : Blo 1060614 6816469 := bbase (se 7 (by rfl) ⟨79880, by rfl⟩ : syracuseStep 6816469 = 159761) (by norm_num)
theorem B2425589 : Blo 1060614 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B2392829 : Blo 1060614 2392829 := bbase (se 3 (by rfl) ⟨448655, by rfl⟩ : syracuseStep 2392829 = 897311) (by norm_num)
theorem B1278761 : Blo 1060614 1278761 := bbase (se 2 (by rfl) ⟨479535, by rfl⟩ : syracuseStep 1278761 = 959071) (by norm_num)
theorem B2687813 : Blo 1060614 2687813 := bbase (se 4 (by rfl) ⟨251982, by rfl⟩ : syracuseStep 2687813 = 503965) (by norm_num)
theorem B2392901 : Blo 1060614 2392901 := bbase (se 4 (by rfl) ⟨224334, by rfl⟩ : syracuseStep 2392901 = 448669) (by norm_num)
theorem B1344377 : Blo 1060614 1344377 := bbase (se 2 (by rfl) ⟨504141, by rfl⟩ : syracuseStep 1344377 = 1008283) (by norm_num)
theorem B2392973 : Blo 1060614 2392973 := bbase (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) (by norm_num)
theorem B1344433 : Blo 1060614 1344433 := bbase (se 2 (by rfl) ⟨504162, by rfl⟩ : syracuseStep 1344433 = 1008325) (by norm_num)
theorem B2393045 : Blo 1060614 2393045 := bbase (se 7 (by rfl) ⟨28043, by rfl⟩ : syracuseStep 2393045 = 56087) (by norm_num)
theorem B4031477 : Blo 1060614 4031477 := bbase (se 5 (by rfl) ⟨188975, by rfl⟩ : syracuseStep 4031477 = 377951) (by norm_num)
theorem B2688005 : Blo 1060614 2688005 := bbase (se 4 (by rfl) ⟨252000, by rfl⟩ : syracuseStep 2688005 = 504001) (by norm_num)
theorem B1344529 : Blo 1060614 1344529 := bbase (se 2 (by rfl) ⟨504198, by rfl⟩ : syracuseStep 1344529 = 1008397) (by norm_num)
theorem B5374997 : Blo 1060614 5374997 := bbase (se 6 (by rfl) ⟨125976, by rfl⟩ : syracuseStep 5374997 = 251953) (by norm_num)
theorem B2393117 : Blo 1060614 2393117 := bbase (se 3 (by rfl) ⟨448709, by rfl⟩ : syracuseStep 2393117 = 897419) (by norm_num)
theorem B1704989 : Blo 1060614 1704989 := bbase (se 3 (by rfl) ⟨319685, by rfl⟩ : syracuseStep 1704989 = 639371) (by norm_num)
theorem B2557013 : Blo 1060614 2557013 := bbase (se 8 (by rfl) ⟨14982, by rfl⟩ : syracuseStep 2557013 = 29965) (by norm_num)
theorem B2393189 : Blo 1060614 2393189 := bbase (se 4 (by rfl) ⟨224361, by rfl⟩ : syracuseStep 2393189 = 448723) (by norm_num)
theorem B2393261 : Blo 1060614 2393261 := bbase (se 3 (by rfl) ⟨448736, by rfl⟩ : syracuseStep 2393261 = 897473) (by norm_num)
theorem B1344701 : Blo 1060614 1344701 := bbase (se 3 (by rfl) ⟨252131, by rfl⟩ : syracuseStep 1344701 = 504263) (by norm_num)
theorem B4359413 : Blo 1060614 4359413 := bbase (se 5 (by rfl) ⟨204347, by rfl⟩ : syracuseStep 4359413 = 408695) (by norm_num)
theorem B1344757 : Blo 1060614 1344757 := bbase (se 5 (by rfl) ⟨63035, by rfl⟩ : syracuseStep 1344757 = 126071) (by norm_num)
theorem B2393333 : Blo 1060614 2393333 := bbase (se 5 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 2393333 = 224375) (by norm_num)
theorem B4031765 : Blo 1060614 4031765 := bbase (se 6 (by rfl) ⟨94494, by rfl⟩ : syracuseStep 4031765 = 188989) (by norm_num)
theorem B2458925 : Blo 1060614 2458925 := bbase (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) (by norm_num)
theorem B2393405 : Blo 1060614 2393405 := bbase (se 3 (by rfl) ⟨448763, by rfl⟩ : syracuseStep 2393405 = 897527) (by norm_num)
theorem B2557253 : Blo 1060614 2557253 := bbase (se 4 (by rfl) ⟨239742, by rfl⟩ : syracuseStep 2557253 = 479485) (by norm_num)
theorem B1344853 : Blo 1060614 1344853 := bbase (se 12 (by rfl) ⟨492, by rfl⟩ : syracuseStep 1344853 = 985) (by norm_num)
theorem B9078101 : Blo 1060614 9078101 := bbase (se 12 (by rfl) ⟨3324, by rfl⟩ : syracuseStep 9078101 = 6649) (by norm_num)
theorem B2688349 : Blo 1060614 2688349 := bbase (se 3 (by rfl) ⟨504065, by rfl⟩ : syracuseStep 2688349 = 1008131) (by norm_num)
theorem B2393477 : Blo 1060614 2393477 := bbase (se 4 (by rfl) ⟨224388, by rfl⟩ : syracuseStep 2393477 = 448777) (by norm_num)
theorem B2688461 : Blo 1060614 2688461 := bbase (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) (by norm_num)
theorem B2393549 : Blo 1060614 2393549 := bbase (se 3 (by rfl) ⟨448790, by rfl⟩ : syracuseStep 2393549 = 897581) (by norm_num)
theorem B1345025 : Blo 1060614 1345025 := bbase (se 2 (by rfl) ⟨504384, by rfl⟩ : syracuseStep 1345025 = 1008769) (by norm_num)
theorem B2393621 : Blo 1060614 2393621 := bbase (se 6 (by rfl) ⟨56100, by rfl⟩ : syracuseStep 2393621 = 112201) (by norm_num)
theorem B1345081 : Blo 1060614 1345081 := bbase (se 2 (by rfl) ⟨504405, by rfl⟩ : syracuseStep 1345081 = 1008811) (by norm_num)
theorem B2393693 : Blo 1060614 2393693 := bbase (se 3 (by rfl) ⟨448817, by rfl⟩ : syracuseStep 2393693 = 897635) (by norm_num)
theorem B2688653 : Blo 1060614 2688653 := bbase (se 3 (by rfl) ⟨504122, by rfl⟩ : syracuseStep 2688653 = 1008245) (by norm_num)
theorem B1345177 : Blo 1060614 1345177 := bbase (se 2 (by rfl) ⟨504441, by rfl⟩ : syracuseStep 1345177 = 1008883) (by norm_num)
theorem B2590373 : Blo 1060614 2590373 := bbase (se 4 (by rfl) ⟨242847, by rfl⟩ : syracuseStep 2590373 = 485695) (by norm_num)
theorem B2393765 : Blo 1060614 2393765 := bbase (se 4 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 2393765 = 448831) (by norm_num)
theorem B2393837 : Blo 1060614 2393837 := bbase (se 3 (by rfl) ⟨448844, by rfl⟩ : syracuseStep 2393837 = 897689) (by norm_num)
theorem B2393909 : Blo 1060614 2393909 := bbase (se 5 (by rfl) ⟨112214, by rfl⟩ : syracuseStep 2393909 = 224429) (by norm_num)
theorem B1345349 : Blo 1060614 1345349 := bbase (se 4 (by rfl) ⟨126126, by rfl⟩ : syracuseStep 1345349 = 252253) (by norm_num)
theorem B1148773 : Blo 1060614 1148773 := bbase (se 4 (by rfl) ⟨107697, by rfl⟩ : syracuseStep 1148773 = 215395) (by norm_num)
theorem B1345405 : Blo 1060614 1345405 := bbase (se 3 (by rfl) ⟨252263, by rfl⟩ : syracuseStep 1345405 = 504527) (by norm_num)
theorem B2393981 : Blo 1060614 2393981 := bbase (se 3 (by rfl) ⟨448871, by rfl⟩ : syracuseStep 2393981 = 897743) (by norm_num)
theorem B2394053 : Blo 1060614 2394053 := bbase (se 4 (by rfl) ⟨224442, by rfl⟩ : syracuseStep 2394053 = 448885) (by norm_num)
theorem B1345501 : Blo 1060614 1345501 := bbase (se 3 (by rfl) ⟨252281, by rfl⟩ : syracuseStep 1345501 = 504563) (by norm_num)
theorem B2688997 : Blo 1060614 2688997 := bbase (se 4 (by rfl) ⟨252093, by rfl⟩ : syracuseStep 2688997 = 504187) (by norm_num)
theorem B2394125 : Blo 1060614 2394125 := bbase (se 3 (by rfl) ⟨448898, by rfl⟩ : syracuseStep 2394125 = 897797) (by norm_num)
theorem B2689109 : Blo 1060614 2689109 := bbase (se 8 (by rfl) ⟨15756, by rfl⟩ : syracuseStep 2689109 = 31513) (by norm_num)
theorem B2394197 : Blo 1060614 2394197 := bbase (se 8 (by rfl) ⟨14028, by rfl⟩ : syracuseStep 2394197 = 28057) (by norm_num)
theorem B2492549 : Blo 1060614 2492549 := bbase (se 4 (by rfl) ⟨233676, by rfl⟩ : syracuseStep 2492549 = 467353) (by norm_num)
theorem B1345673 : Blo 1060614 1345673 := bbase (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) (by norm_num)
theorem B1149085 : Blo 1060614 1149085 := bbase (se 3 (by rfl) ⟨215453, by rfl⟩ : syracuseStep 1149085 = 430907) (by norm_num)
theorem B2394269 : Blo 1060614 2394269 := bbase (se 3 (by rfl) ⟨448925, by rfl⟩ : syracuseStep 2394269 = 897851) (by norm_num)
theorem B1345729 : Blo 1060614 1345729 := bbase (se 2 (by rfl) ⟨504648, by rfl⟩ : syracuseStep 1345729 = 1009297) (by norm_num)
theorem B2427101 : Blo 1060614 2427101 := bbase (se 3 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 2427101 = 910163) (by norm_num)
theorem B2394341 : Blo 1060614 2394341 := bbase (se 4 (by rfl) ⟨224469, by rfl⟩ : syracuseStep 2394341 = 448939) (by norm_num)
theorem B2689301 : Blo 1060614 2689301 := bbase (se 6 (by rfl) ⟨63030, by rfl⟩ : syracuseStep 2689301 = 126061) (by norm_num)
theorem B1345825 : Blo 1060614 1345825 := bbase (se 2 (by rfl) ⟨504684, by rfl⟩ : syracuseStep 1345825 = 1009369) (by norm_num)
theorem B5376293 : Blo 1060614 5376293 := bbase (se 4 (by rfl) ⟨504027, by rfl⟩ : syracuseStep 5376293 = 1008055) (by norm_num)
theorem B2394413 : Blo 1060614 2394413 := bbase (se 3 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 2394413 = 897905) (by norm_num)
theorem B2394485 : Blo 1060614 2394485 := bbase (se 5 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 2394485 = 224483) (by norm_num)
theorem B4032949 : Blo 1060614 4032949 := bbase (se 5 (by rfl) ⟨189044, by rfl⟩ : syracuseStep 4032949 = 378089) (by norm_num)
theorem B2722237 : Blo 1060614 2722237 := bbase (se 3 (by rfl) ⟨510419, by rfl⟩ : syracuseStep 2722237 = 1020839) (by norm_num)
theorem B2394557 : Blo 1060614 2394557 := bbase (se 3 (by rfl) ⟨448979, by rfl⟩ : syracuseStep 2394557 = 897959) (by norm_num)
theorem B1345997 : Blo 1060614 1345997 := bbase (se 3 (by rfl) ⟨252374, by rfl⟩ : syracuseStep 1345997 = 504749) (by norm_num)
theorem B1346053 : Blo 1060614 1346053 := bbase (se 4 (by rfl) ⟨126192, by rfl⟩ : syracuseStep 1346053 = 252385) (by norm_num)
theorem B2394629 : Blo 1060614 2394629 := bbase (se 4 (by rfl) ⟨224496, by rfl⟩ : syracuseStep 2394629 = 448993) (by norm_num)
theorem B2394701 : Blo 1060614 2394701 := bbase (se 3 (by rfl) ⟨449006, by rfl⟩ : syracuseStep 2394701 = 898013) (by norm_num)
theorem B1346149 : Blo 1060614 1346149 := bbase (se 4 (by rfl) ⟨126201, by rfl⟩ : syracuseStep 1346149 = 252403) (by norm_num)
theorem B2689645 : Blo 1060614 2689645 := bbase (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) (by norm_num)
theorem B1149553 : Blo 1060614 1149553 := bbase (se 2 (by rfl) ⟨431082, by rfl⟩ : syracuseStep 1149553 = 862165) (by norm_num)
theorem B2394773 : Blo 1060614 2394773 := bbase (se 6 (by rfl) ⟨56127, by rfl⟩ : syracuseStep 2394773 = 112255) (by norm_num)
theorem B3410581 : Blo 1060614 3410581 := bbase (se 6 (by rfl) ⟨79935, by rfl⟩ : syracuseStep 3410581 = 159871) (by norm_num)
theorem B2689757 : Blo 1060614 2689757 := bbase (se 3 (by rfl) ⟨504329, by rfl⟩ : syracuseStep 2689757 = 1008659) (by norm_num)
theorem B2394845 : Blo 1060614 2394845 := bbase (se 3 (by rfl) ⟨449033, by rfl⟩ : syracuseStep 2394845 = 898067) (by norm_num)
theorem B4033253 : Blo 1060614 4033253 := bbase (se 4 (by rfl) ⟨378117, by rfl⟩ : syracuseStep 4033253 = 756235) (by norm_num)
theorem B1346321 : Blo 1060614 1346321 := bbase (se 2 (by rfl) ⟨504870, by rfl⟩ : syracuseStep 1346321 = 1009741) (by norm_num)
theorem B2394917 : Blo 1060614 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B3640133 : Blo 1060614 3640133 := bbase (se 4 (by rfl) ⟨341262, by rfl⟩ : syracuseStep 3640133 = 682525) (by norm_num)
theorem B1346377 : Blo 1060614 1346377 := bbase (se 2 (by rfl) ⟨504891, by rfl⟩ : syracuseStep 1346377 = 1009783) (by norm_num)
theorem B2394989 : Blo 1060614 2394989 := bbase (se 3 (by rfl) ⟨449060, by rfl⟩ : syracuseStep 2394989 = 898121) (by norm_num)
theorem B10226549 : Blo 1060614 10226549 := bbase (se 5 (by rfl) ⟨479369, by rfl⟩ : syracuseStep 10226549 = 958739) (by norm_num)
theorem B2689949 : Blo 1060614 2689949 := bbase (se 3 (by rfl) ⟨504365, by rfl⟩ : syracuseStep 2689949 = 1008731) (by norm_num)
theorem B1346473 : Blo 1060614 1346473 := bbase (se 2 (by rfl) ⟨504927, by rfl⟩ : syracuseStep 1346473 = 1009855) (by norm_num)
theorem B2395061 : Blo 1060614 2395061 := bbase (se 5 (by rfl) ⟨112268, by rfl⟩ : syracuseStep 2395061 = 224537) (by norm_num)
theorem B3836917 : Blo 1060614 3836917 := bbase (se 5 (by rfl) ⟨179855, by rfl⟩ : syracuseStep 3836917 = 359711) (by norm_num)
theorem B2395133 : Blo 1060614 2395133 := bbase (se 3 (by rfl) ⟨449087, by rfl⟩ : syracuseStep 2395133 = 898175) (by norm_num)
theorem B2395205 : Blo 1060614 2395205 := bbase (se 4 (by rfl) ⟨224550, by rfl⟩ : syracuseStep 2395205 = 449101) (by norm_num)
theorem B1346645 : Blo 1060614 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B1346701 : Blo 1060614 1346701 := bbase (se 3 (by rfl) ⟨252506, by rfl⟩ : syracuseStep 1346701 = 505013) (by norm_num)
theorem B2395277 : Blo 1060614 2395277 := bbase (se 3 (by rfl) ⟨449114, by rfl⟩ : syracuseStep 2395277 = 898229) (by norm_num)
theorem B2395349 : Blo 1060614 2395349 := bbase (se 7 (by rfl) ⟨28070, by rfl⟩ : syracuseStep 2395349 = 56141) (by norm_num)
theorem B1346797 : Blo 1060614 1346797 := bbase (se 3 (by rfl) ⟨252524, by rfl⟩ : syracuseStep 1346797 = 505049) (by norm_num)
theorem B2690293 : Blo 1060614 2690293 := bbase (se 5 (by rfl) ⟨126107, by rfl⟩ : syracuseStep 2690293 = 252215) (by norm_num)
theorem B2690405 : Blo 1060614 2690405 := bbase (se 4 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 2690405 = 504451) (by norm_num)
theorem B1346969 : Blo 1060614 1346969 := bbase (se 2 (by rfl) ⟨505113, by rfl⟩ : syracuseStep 1346969 = 1010227) (by norm_num)
theorem B1347025 : Blo 1060614 1347025 := bbase (se 2 (by rfl) ⟨505134, by rfl⟩ : syracuseStep 1347025 = 1010269) (by norm_num)
theorem B2690597 : Blo 1060614 2690597 := bbase (se 4 (by rfl) ⟨252243, by rfl⟩ : syracuseStep 2690597 = 504487) (by norm_num)
theorem B1347121 : Blo 1060614 1347121 := bbase (se 2 (by rfl) ⟨505170, by rfl⟩ : syracuseStep 1347121 = 1010341) (by norm_num)
theorem B5377589 : Blo 1060614 5377589 := bbase (se 5 (by rfl) ⟨252074, by rfl⟩ : syracuseStep 5377589 = 504149) (by norm_num)
theorem B5738165 : Blo 1060614 5738165 := bbase (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) (by norm_num)
theorem B1347293 : Blo 1060614 1347293 := bbase (se 3 (by rfl) ⟨252617, by rfl⟩ : syracuseStep 1347293 = 505235) (by norm_num)
theorem B1511149 : Blo 1060614 1511149 := bbase (se 3 (by rfl) ⟨283340, by rfl⟩ : syracuseStep 1511149 = 566681) (by norm_num)
theorem B1347349 : Blo 1060614 1347349 := bbase (se 6 (by rfl) ⟨31578, by rfl⟩ : syracuseStep 1347349 = 63157) (by norm_num)
theorem B2690941 : Blo 1060614 2690941 := bbase (se 3 (by rfl) ⟨504551, by rfl⟩ : syracuseStep 2690941 = 1009103) (by norm_num)
theorem B2691053 : Blo 1060614 2691053 := bbase (se 3 (by rfl) ⟨504572, by rfl⟩ : syracuseStep 2691053 = 1009145) (by norm_num)
theorem B2691245 : Blo 1060614 2691245 := bbase (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) (by norm_num)
theorem B7671989 : Blo 1060614 7671989 := bbase (se 5 (by rfl) ⟨359624, by rfl⟩ : syracuseStep 7671989 = 719249) (by norm_num)
theorem B1511741 : Blo 1060614 1511741 := bbase (se 3 (by rfl) ⟨283451, by rfl⟩ : syracuseStep 1511741 = 566903) (by norm_num)
theorem B1511821 : Blo 1060614 1511821 := bbase (se 3 (by rfl) ⟨283466, by rfl⟩ : syracuseStep 1511821 = 566933) (by norm_num)
theorem B1511941 : Blo 1060614 1511941 := bbase (se 4 (by rfl) ⟨141744, by rfl⟩ : syracuseStep 1511941 = 283489) (by norm_num)
theorem B2691589 : Blo 1060614 2691589 := bbase (se 4 (by rfl) ⟨252336, by rfl⟩ : syracuseStep 2691589 = 504673) (by norm_num)
theorem B1512037 : Blo 1060614 1512037 := bbase (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) (by norm_num)
theorem B2691701 : Blo 1060614 2691701 := bbase (se 5 (by rfl) ⟨126173, by rfl⟩ : syracuseStep 2691701 = 252347) (by norm_num)
theorem B6820469 : Blo 1060614 6820469 := bbase (se 5 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 6820469 = 639419) (by norm_num)
theorem B2265725 : Blo 1060614 2265725 := bbase (se 3 (by rfl) ⟨424823, by rfl⟩ : syracuseStep 2265725 = 849647) (by norm_num)
theorem B2265869 : Blo 1060614 2265869 := bbase (se 3 (by rfl) ⟨424850, by rfl⟩ : syracuseStep 2265869 = 849701) (by norm_num)
theorem B4035365 : Blo 1060614 4035365 := bbase (se 4 (by rfl) ⟨378315, by rfl⟩ : syracuseStep 4035365 = 756631) (by norm_num)
theorem B2691893 : Blo 1060614 2691893 := bbase (se 5 (by rfl) ⟨126182, by rfl⟩ : syracuseStep 2691893 = 252365) (by norm_num)
theorem B5378885 : Blo 1060614 5378885 := bbase (se 4 (by rfl) ⟨504270, by rfl⟩ : syracuseStep 5378885 = 1008541) (by norm_num)
theorem B1151821 : Blo 1060614 1151821 := bbase (se 3 (by rfl) ⟨215966, by rfl⟩ : syracuseStep 1151821 = 431933) (by norm_num)
theorem B2331701 : Blo 1060614 2331701 := bbase (se 5 (by rfl) ⟨109298, by rfl⟩ : syracuseStep 2331701 = 218597) (by norm_num)
theorem B4035653 : Blo 1060614 4035653 := bbase (se 4 (by rfl) ⟨378342, by rfl⟩ : syracuseStep 4035653 = 756685) (by norm_num)
theorem B1512533 : Blo 1060614 1512533 := bbase (se 8 (by rfl) ⟨8862, by rfl⟩ : syracuseStep 1512533 = 17725) (by norm_num)
theorem B2692237 : Blo 1060614 2692237 := bbase (se 3 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 2692237 = 1009589) (by norm_num)
theorem B2692349 : Blo 1060614 2692349 := bbase (se 3 (by rfl) ⟨504815, by rfl⟩ : syracuseStep 2692349 = 1009631) (by norm_num)
theorem B2692541 : Blo 1060614 2692541 := bbase (se 3 (by rfl) ⟨504851, by rfl⟩ : syracuseStep 2692541 = 1009703) (by norm_num)
theorem B1938901 : Blo 1060614 1938901 := bbase (se 7 (by rfl) ⟨22721, by rfl⟩ : syracuseStep 1938901 = 45443) (by norm_num)
theorem B2266613 : Blo 1060614 2266613 := bbase (se 5 (by rfl) ⟨106247, by rfl⟩ : syracuseStep 2266613 = 212495) (by norm_num)
theorem B2659837 : Blo 1060614 2659837 := bbase (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) (by norm_num)
theorem B1513085 : Blo 1060614 1513085 := bbase (se 3 (by rfl) ⟨283703, by rfl⟩ : syracuseStep 1513085 = 567407) (by norm_num)
theorem B3020453 : Blo 1060614 3020453 := bbase (se 4 (by rfl) ⟨283167, by rfl⟩ : syracuseStep 3020453 = 566335) (by norm_num)
theorem B2692885 : Blo 1060614 2692885 := bbase (se 6 (by rfl) ⟨63114, by rfl⟩ : syracuseStep 2692885 = 126229) (by norm_num)
theorem B2692997 : Blo 1060614 2692997 := bbase (se 4 (by rfl) ⟨252468, by rfl⟩ : syracuseStep 2692997 = 504937) (by norm_num)
theorem B2693189 : Blo 1060614 2693189 := bbase (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) (by norm_num)
theorem B3020885 : Blo 1060614 3020885 := bbase (se 8 (by rfl) ⟨17700, by rfl⟩ : syracuseStep 3020885 = 35401) (by norm_num)
theorem B5380181 : Blo 1060614 5380181 := bbase (se 8 (by rfl) ⟨31524, by rfl⟩ : syracuseStep 5380181 = 63049) (by norm_num)
theorem B25860181 : Blo 1060614 25860181 := bbase (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) (by norm_num)
theorem B2267365 : Blo 1060614 2267365 := bbase (se 4 (by rfl) ⟨212565, by rfl⟩ : syracuseStep 2267365 = 425131) (by norm_num)
theorem B4036837 : Blo 1060614 4036837 := bbase (se 4 (by rfl) ⟨378453, by rfl⟩ : syracuseStep 4036837 = 756907) (by norm_num)
theorem B1513837 : Blo 1060614 1513837 := bbase (se 3 (by rfl) ⟨283844, by rfl⟩ : syracuseStep 1513837 = 567689) (by norm_num)
theorem B2267509 : Blo 1060614 2267509 := bbase (se 5 (by rfl) ⟨106289, by rfl⟩ : syracuseStep 2267509 = 212579) (by norm_num)
theorem B8624501 : Blo 1060614 8624501 := bbase (se 5 (by rfl) ⟨404273, by rfl⟩ : syracuseStep 8624501 = 808547) (by norm_num)
theorem B2693533 : Blo 1060614 2693533 := bbase (se 3 (by rfl) ⟨505037, by rfl⟩ : syracuseStep 2693533 = 1010075) (by norm_num)
theorem B2693645 : Blo 1060614 2693645 := bbase (se 3 (by rfl) ⟨505058, by rfl⟩ : syracuseStep 2693645 = 1010117) (by norm_num)
theorem B4037141 : Blo 1060614 4037141 := bbase (se 6 (by rfl) ⟨94620, by rfl⟩ : syracuseStep 4037141 = 189241) (by norm_num)
theorem B2693837 : Blo 1060614 2693837 := bbase (se 3 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 2693837 = 1010189) (by norm_num)
theorem B2267885 : Blo 1060614 2267885 := bbase (se 3 (by rfl) ⟨425228, by rfl⟩ : syracuseStep 2267885 = 850457) (by norm_num)
theorem B2333461 : Blo 1060614 2333461 := bbase (se 6 (by rfl) ⟨54690, by rfl⟩ : syracuseStep 2333461 = 109381) (by norm_num)
theorem B3021637 : Blo 1060614 3021637 := bbase (se 4 (by rfl) ⟨283278, by rfl⟩ : syracuseStep 3021637 = 566557) (by norm_num)
theorem B2726837 : Blo 1060614 2726837 := bbase (se 5 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 2726837 = 255641) (by norm_num)
theorem B8068085 : Blo 1060614 8068085 := bbase (se 5 (by rfl) ⟨378191, by rfl⟩ : syracuseStep 8068085 = 756383) (by norm_num)
theorem B2694181 : Blo 1060614 2694181 := bbase (se 4 (by rfl) ⟨252579, by rfl⟩ : syracuseStep 2694181 = 505159) (by norm_num)
theorem B2268253 : Blo 1060614 2268253 := bbase (se 3 (by rfl) ⟨425297, by rfl⟩ : syracuseStep 2268253 = 850595) (by norm_num)
theorem B1514629 : Blo 1060614 1514629 := bbase (se 4 (by rfl) ⟨141996, by rfl⟩ : syracuseStep 1514629 = 283993) (by norm_num)
theorem B2694293 : Blo 1060614 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B2694485 : Blo 1060614 2694485 := bbase (se 11 (by rfl) ⟨1973, by rfl⟩ : syracuseStep 2694485 = 3947) (by norm_num)
theorem B5381477 : Blo 1060614 5381477 := bbase (se 4 (by rfl) ⟨504513, by rfl⟩ : syracuseStep 5381477 = 1009027) (by norm_num)
theorem B1514965 : Blo 1060614 1514965 := bbase (se 7 (by rfl) ⟨17753, by rfl⟩ : syracuseStep 1514965 = 35507) (by norm_num)
theorem B1515181 : Blo 1060614 1515181 := bbase (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) (by norm_num)
theorem B3546821 : Blo 1060614 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B3579605 : Blo 1060614 3579605 := bbase (se 7 (by rfl) ⟨41948, by rfl⟩ : syracuseStep 3579605 = 83897) (by norm_num)
theorem B20455253 : Blo 1060614 20455253 := bbase (se 9 (by rfl) ⟨59927, by rfl⟩ : syracuseStep 20455253 = 119855) (by norm_num)
theorem B1515557 : Blo 1060614 1515557 := bbase (se 4 (by rfl) ⟨142083, by rfl⟩ : syracuseStep 1515557 = 284167) (by norm_num)
theorem B3580037 : Blo 1060614 3580037 := bbase (se 4 (by rfl) ⟨335628, by rfl⟩ : syracuseStep 3580037 = 671257) (by norm_num)
theorem B4301093 : Blo 1060614 4301093 := bbase (se 4 (by rfl) ⟨403227, by rfl⟩ : syracuseStep 4301093 = 806455) (by norm_num)
theorem B3580469 : Blo 1060614 3580469 := bbase (se 5 (by rfl) ⟨167834, by rfl⟩ : syracuseStep 3580469 = 335669) (by norm_num)
theorem B2269757 : Blo 1060614 2269757 := bbase (se 3 (by rfl) ⟨425579, by rfl⟩ : syracuseStep 2269757 = 851159) (by norm_num)
theorem B2728517 : Blo 1060614 2728517 := bbase (se 4 (by rfl) ⟨255798, by rfl⟩ : syracuseStep 2728517 = 511597) (by norm_num)
theorem B4039253 : Blo 1060614 4039253 := bbase (se 8 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 4039253 = 47335) (by norm_num)
theorem B5382773 : Blo 1060614 5382773 := bbase (se 5 (by rfl) ⟨252317, by rfl⟩ : syracuseStep 5382773 = 504635) (by norm_num)
theorem B2269901 : Blo 1060614 2269901 := bbase (se 3 (by rfl) ⟨425606, by rfl⟩ : syracuseStep 2269901 = 851213) (by norm_num)
theorem B4530917 : Blo 1060614 4530917 := bbase (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) (by norm_num)
theorem B14754581 : Blo 1060614 14754581 := bbase (se 6 (by rfl) ⟨345810, by rfl⟩ : syracuseStep 14754581 = 691621) (by norm_num)
theorem B2073373 : Blo 1060614 2073373 := bbase (se 3 (by rfl) ⟨388757, by rfl⟩ : syracuseStep 2073373 = 777515) (by norm_num)
theorem B4039541 : Blo 1060614 4039541 := bbase (se 5 (by rfl) ⟨189353, by rfl⟩ : syracuseStep 4039541 = 378707) (by norm_num)
theorem B3449749 : Blo 1060614 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B20423573 : Blo 1060614 20423573 := bbase (se 6 (by rfl) ⟨478677, by rfl⟩ : syracuseStep 20423573 = 957355) (by norm_num)
theorem B3580901 : Blo 1060614 3580901 := bbase (se 4 (by rfl) ⟨335709, by rfl⟩ : syracuseStep 3580901 = 671419) (by norm_num)
theorem B2270261 : Blo 1060614 2270261 := bbase (se 5 (by rfl) ⟨106418, by rfl⟩ : syracuseStep 2270261 = 212837) (by norm_num)
theorem B9086165 : Blo 1060614 9086165 := bbase (se 7 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 9086165 = 212957) (by norm_num)
theorem B2336125 : Blo 1060614 2336125 := bbase (se 3 (by rfl) ⟨438023, by rfl⟩ : syracuseStep 2336125 = 876047) (by norm_num)
theorem B3581333 : Blo 1060614 3581333 := bbase (se 6 (by rfl) ⟨83937, by rfl⟩ : syracuseStep 3581333 = 167875) (by norm_num)
theorem B4302325 : Blo 1060614 4302325 := bbase (se 5 (by rfl) ⟨201671, by rfl⟩ : syracuseStep 4302325 = 403343) (by norm_num)
theorem B3024485 : Blo 1060614 3024485 := bbase (se 4 (by rfl) ⟨283545, by rfl⟩ : syracuseStep 3024485 = 567091) (by norm_num)
theorem B4531909 : Blo 1060614 4531909 := bbase (se 4 (by rfl) ⟨424866, by rfl⟩ : syracuseStep 4531909 = 849733) (by norm_num)
theorem B3581765 : Blo 1060614 3581765 := bbase (se 4 (by rfl) ⟨335790, by rfl⟩ : syracuseStep 3581765 = 671581) (by norm_num)
theorem B5384069 : Blo 1060614 5384069 := bbase (se 4 (by rfl) ⟨504756, by rfl⟩ : syracuseStep 5384069 = 1009513) (by norm_num)
theorem B2271149 : Blo 1060614 2271149 := bbase (se 3 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 2271149 = 851681) (by norm_num)
theorem B7645205 : Blo 1060614 7645205 := bbase (se 6 (by rfl) ⟨179184, by rfl⟩ : syracuseStep 7645205 = 358369) (by norm_num)
theorem B4040725 : Blo 1060614 4040725 := bbase (se 6 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 4040725 = 189409) (by norm_num)
theorem B2271397 : Blo 1060614 2271397 := bbase (se 4 (by rfl) ⟨212943, by rfl⟩ : syracuseStep 2271397 = 425887) (by norm_num)
theorem B3582197 : Blo 1060614 3582197 := bbase (se 5 (by rfl) ⟨167915, by rfl⟩ : syracuseStep 3582197 = 335831) (by norm_num)
theorem B4041029 : Blo 1060614 4041029 := bbase (se 4 (by rfl) ⟨378846, by rfl⟩ : syracuseStep 4041029 = 757693) (by norm_num)
theorem B1845605 : Blo 1060614 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B2271901 : Blo 1060614 2271901 := bbase (se 3 (by rfl) ⟨425981, by rfl⟩ : syracuseStep 2271901 = 851963) (by norm_num)
theorem B3582629 : Blo 1060614 3582629 := bbase (se 4 (by rfl) ⟨335871, by rfl⟩ : syracuseStep 3582629 = 671743) (by norm_num)
theorem B3025669 : Blo 1060614 3025669 := bbase (se 4 (by rfl) ⟨283656, by rfl⟩ : syracuseStep 3025669 = 567313) (by norm_num)
theorem B1682317 : Blo 1060614 1682317 := bbase (se 3 (by rfl) ⟨315434, by rfl⟩ : syracuseStep 1682317 = 630869) (by norm_num)
theorem B1092509 : Blo 1060614 1092509 := bbase (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) (by norm_num)
theorem B3025829 : Blo 1060614 3025829 := bbase (se 4 (by rfl) ⟨283671, by rfl⟩ : syracuseStep 3025829 = 567343) (by norm_num)
theorem B3583061 : Blo 1060614 3583061 := bbase (se 8 (by rfl) ⟨20994, by rfl⟩ : syracuseStep 3583061 = 41989) (by norm_num)
theorem B10890389 : Blo 1060614 10890389 := bbase (se 6 (by rfl) ⟨255243, by rfl⟩ : syracuseStep 10890389 = 510487) (by norm_num)
theorem B3026069 : Blo 1060614 3026069 := bbase (se 6 (by rfl) ⟨70923, by rfl⟩ : syracuseStep 3026069 = 141847) (by norm_num)
theorem B5385365 : Blo 1060614 5385365 := bbase (se 6 (by rfl) ⟨126219, by rfl⟩ : syracuseStep 5385365 = 252439) (by norm_num)
theorem B2731229 : Blo 1060614 2731229 := bbase (se 3 (by rfl) ⟨512105, by rfl⟩ : syracuseStep 2731229 = 1024211) (by norm_num)
theorem B3026261 : Blo 1060614 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B1912261 : Blo 1060614 1912261 := bbase (se 4 (by rfl) ⟨179274, by rfl⟩ : syracuseStep 1912261 = 358549) (by norm_num)
theorem B3583493 : Blo 1060614 3583493 := bbase (se 4 (by rfl) ⟨335952, by rfl⟩ : syracuseStep 3583493 = 671905) (by norm_num)
theorem B15314453 : Blo 1060614 15314453 := bbase (se 6 (by rfl) ⟨358932, by rfl⟩ : syracuseStep 15314453 = 717865) (by norm_num)
theorem B2272789 : Blo 1060614 2272789 := bbase (se 6 (by rfl) ⟨53268, by rfl⟩ : syracuseStep 2272789 = 106537) (by norm_num)
theorem B1912693 : Blo 1060614 1912693 := bbase (se 5 (by rfl) ⟨89657, by rfl⟩ : syracuseStep 1912693 = 179315) (by norm_num)
theorem B3583925 : Blo 1060614 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B1912837 : Blo 1060614 1912837 := bbase (se 4 (by rfl) ⟨179328, by rfl⟩ : syracuseStep 1912837 = 358657) (by norm_num)
theorem B5451781 : Blo 1060614 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B2273285 : Blo 1060614 2273285 := bbase (se 4 (by rfl) ⟨213120, by rfl⟩ : syracuseStep 2273285 = 426241) (by norm_num)
theorem B1814717 : Blo 1060614 1814717 := bbase (se 3 (by rfl) ⟨340259, by rfl⟩ : syracuseStep 1814717 = 680519) (by norm_num)
theorem B1913053 : Blo 1060614 1913053 := bbase (se 3 (by rfl) ⟨358697, by rfl⟩ : syracuseStep 1913053 = 717395) (by norm_num)
theorem B1618141 : Blo 1060614 1618141 := bbase (se 3 (by rfl) ⟨303401, by rfl⟩ : syracuseStep 1618141 = 606803) (by norm_num)
theorem B1618165 : Blo 1060614 1618165 := bbase (se 5 (by rfl) ⟨75851, by rfl⟩ : syracuseStep 1618165 = 151703) (by norm_num)
theorem B3027253 : Blo 1060614 3027253 := bbase (se 5 (by rfl) ⟨141902, by rfl⟩ : syracuseStep 3027253 = 283805) (by norm_num)
theorem B3584357 : Blo 1060614 3584357 := bbase (se 4 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 3584357 = 672067) (by norm_num)
theorem B18428309 : Blo 1060614 18428309 := bbase (se 6 (by rfl) ⟨431913, by rfl⟩ : syracuseStep 18428309 = 863827) (by norm_num)
theorem B5386661 : Blo 1060614 5386661 := bbase (se 4 (by rfl) ⟨504999, by rfl⟩ : syracuseStep 5386661 = 1009999) (by norm_num)
theorem B3584789 : Blo 1060614 3584789 := bbase (se 6 (by rfl) ⟨84018, by rfl⟩ : syracuseStep 3584789 = 168037) (by norm_num)
theorem B1913645 : Blo 1060614 1913645 := bbase (se 3 (by rfl) ⟨358808, by rfl⟩ : syracuseStep 1913645 = 717617) (by norm_num)
theorem B3683141 : Blo 1060614 3683141 := bbase (se 4 (by rfl) ⟨345294, by rfl⟩ : syracuseStep 3683141 = 690589) (by norm_num)
theorem B5747573 : Blo 1060614 5747573 := bbase (se 5 (by rfl) ⟨269417, by rfl⟩ : syracuseStep 5747573 = 538835) (by norm_num)
theorem B1455013 : Blo 1060614 1455013 := bbase (se 4 (by rfl) ⟨136407, by rfl⟩ : syracuseStep 1455013 = 272815) (by norm_num)
theorem B1913861 : Blo 1060614 1913861 := bbase (se 4 (by rfl) ⟨179424, by rfl⟩ : syracuseStep 1913861 = 358849) (by norm_num)
theorem B3585221 : Blo 1060614 3585221 := bbase (se 4 (by rfl) ⟨336114, by rfl⟩ : syracuseStep 3585221 = 672229) (by norm_num)
theorem B1193197 : Blo 1060614 1193197 := bbase (se 3 (by rfl) ⟨223724, by rfl⟩ : syracuseStep 1193197 = 447449) (by norm_num)
theorem B1193233 : Blo 1060614 1193233 := bbase (se 2 (by rfl) ⟨447462, by rfl⟩ : syracuseStep 1193233 = 894925) (by norm_num)
theorem B1914149 : Blo 1060614 1914149 := bbase (se 4 (by rfl) ⟨179451, by rfl⟩ : syracuseStep 1914149 = 358903) (by norm_num)
theorem B1193269 : Blo 1060614 1193269 := bbase (se 5 (by rfl) ⟨55934, by rfl⟩ : syracuseStep 1193269 = 111869) (by norm_num)
theorem B1193305 : Blo 1060614 1193305 := bbase (se 2 (by rfl) ⟨447489, by rfl⟩ : syracuseStep 1193305 = 894979) (by norm_num)
theorem B1193341 : Blo 1060614 1193341 := bbase (se 3 (by rfl) ⟨223751, by rfl⟩ : syracuseStep 1193341 = 447503) (by norm_num)
theorem B3028357 : Blo 1060614 3028357 := bbase (se 4 (by rfl) ⟨283908, by rfl⟩ : syracuseStep 3028357 = 567817) (by norm_num)
theorem B1193377 : Blo 1060614 1193377 := bbase (se 2 (by rfl) ⟨447516, by rfl⟩ : syracuseStep 1193377 = 895033) (by norm_num)
theorem B1193413 : Blo 1060614 1193413 := bbase (se 4 (by rfl) ⟨111882, by rfl⟩ : syracuseStep 1193413 = 223765) (by norm_num)
theorem B1193449 : Blo 1060614 1193449 := bbase (se 2 (by rfl) ⟨447543, by rfl⟩ : syracuseStep 1193449 = 895087) (by norm_num)
theorem B1193485 : Blo 1060614 1193485 := bbase (se 3 (by rfl) ⟨223778, by rfl⟩ : syracuseStep 1193485 = 447557) (by norm_num)
theorem B1193521 : Blo 1060614 1193521 := bbase (se 2 (by rfl) ⟨447570, by rfl⟩ : syracuseStep 1193521 = 895141) (by norm_num)
theorem B1193557 : Blo 1060614 1193557 := bbase (se 8 (by rfl) ⟨6993, by rfl⟩ : syracuseStep 1193557 = 13987) (by norm_num)
theorem B3585653 : Blo 1060614 3585653 := bbase (se 5 (by rfl) ⟨168077, by rfl⟩ : syracuseStep 3585653 = 336155) (by norm_num)
theorem B1193593 : Blo 1060614 1193593 := bbase (se 2 (by rfl) ⟨447597, by rfl⟩ : syracuseStep 1193593 = 895195) (by norm_num)
theorem B1193629 : Blo 1060614 1193629 := bbase (se 3 (by rfl) ⟨223805, by rfl⟩ : syracuseStep 1193629 = 447611) (by norm_num)
theorem B5387957 : Blo 1060614 5387957 := bbase (se 5 (by rfl) ⟨252560, by rfl⟩ : syracuseStep 5387957 = 505121) (by norm_num)
theorem B1193665 : Blo 1060614 1193665 := bbase (se 2 (by rfl) ⟨447624, by rfl⟩ : syracuseStep 1193665 = 895249) (by norm_num)
theorem B1193701 : Blo 1060614 1193701 := bbase (se 4 (by rfl) ⟨111909, by rfl⟩ : syracuseStep 1193701 = 223819) (by norm_num)
theorem B1193737 : Blo 1060614 1193737 := bbase (se 2 (by rfl) ⟨447651, by rfl⟩ : syracuseStep 1193737 = 895303) (by norm_num)
theorem B1292069 : Blo 1060614 1292069 := bbase (se 4 (by rfl) ⟨121131, by rfl⟩ : syracuseStep 1292069 = 242263) (by norm_num)
theorem B1193773 : Blo 1060614 1193773 := bbase (se 3 (by rfl) ⟨223832, by rfl⟩ : syracuseStep 1193773 = 447665) (by norm_num)
theorem B1193809 : Blo 1060614 1193809 := bbase (se 2 (by rfl) ⟨447678, by rfl⟩ : syracuseStep 1193809 = 895357) (by norm_num)
theorem B1193845 : Blo 1060614 1193845 := bbase (se 5 (by rfl) ⟨55961, by rfl⟩ : syracuseStep 1193845 = 111923) (by norm_num)
theorem B1193881 : Blo 1060614 1193881 := bbase (se 2 (by rfl) ⟨447705, by rfl⟩ : syracuseStep 1193881 = 895411) (by norm_num)
theorem B1193917 : Blo 1060614 1193917 := bbase (se 3 (by rfl) ⟨223859, by rfl⟩ : syracuseStep 1193917 = 447719) (by norm_num)
theorem B1193953 : Blo 1060614 1193953 := bbase (se 2 (by rfl) ⟨447732, by rfl⟩ : syracuseStep 1193953 = 895465) (by norm_num)
theorem B1193989 : Blo 1060614 1193989 := bbase (se 4 (by rfl) ⟨111936, by rfl⟩ : syracuseStep 1193989 = 223873) (by norm_num)
theorem B3586085 : Blo 1060614 3586085 := bbase (se 4 (by rfl) ⟨336195, by rfl⟩ : syracuseStep 3586085 = 672391) (by norm_num)
theorem B1194025 : Blo 1060614 1194025 := bbase (se 2 (by rfl) ⟨447759, by rfl⟩ : syracuseStep 1194025 = 895519) (by norm_num)
theorem B2799677 : Blo 1060614 2799677 := bbase (se 3 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 2799677 = 1049879) (by norm_num)
theorem B3881029 : Blo 1060614 3881029 := bbase (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) (by norm_num)
theorem B1194061 : Blo 1060614 1194061 := bbase (se 3 (by rfl) ⟨223886, by rfl⟩ : syracuseStep 1194061 = 447773) (by norm_num)
theorem B1194097 : Blo 1060614 1194097 := bbase (se 2 (by rfl) ⟨447786, by rfl⟩ : syracuseStep 1194097 = 895573) (by norm_num)
theorem B1194133 : Blo 1060614 1194133 := bbase (se 6 (by rfl) ⟨27987, by rfl⟩ : syracuseStep 1194133 = 55975) (by norm_num)
theorem B1194169 : Blo 1060614 1194169 := bbase (se 2 (by rfl) ⟨447813, by rfl⟩ : syracuseStep 1194169 = 895627) (by norm_num)
theorem B1194205 : Blo 1060614 1194205 := bbase (se 3 (by rfl) ⟨223913, by rfl⟩ : syracuseStep 1194205 = 447827) (by norm_num)
theorem B1194241 : Blo 1060614 1194241 := bbase (se 2 (by rfl) ⟨447840, by rfl⟩ : syracuseStep 1194241 = 895681) (by norm_num)
theorem B1194277 : Blo 1060614 1194277 := bbase (se 4 (by rfl) ⟨111963, by rfl⟩ : syracuseStep 1194277 = 223927) (by norm_num)
theorem B1194313 : Blo 1060614 1194313 := bbase (se 2 (by rfl) ⟨447867, by rfl⟩ : syracuseStep 1194313 = 895735) (by norm_num)
theorem B1194349 : Blo 1060614 1194349 := bbase (se 3 (by rfl) ⟨223940, by rfl⟩ : syracuseStep 1194349 = 447881) (by norm_num)
theorem B1194385 : Blo 1060614 1194385 := bbase (se 2 (by rfl) ⟨447894, by rfl⟩ : syracuseStep 1194385 = 895789) (by norm_num)
theorem B2013589 : Blo 1060614 2013589 := bbase (se 6 (by rfl) ⟨47193, by rfl⟩ : syracuseStep 2013589 = 94387) (by norm_num)
theorem B1194421 : Blo 1060614 1194421 := bbase (se 5 (by rfl) ⟨55988, by rfl⟩ : syracuseStep 1194421 = 111977) (by norm_num)
theorem B3586517 : Blo 1060614 3586517 := bbase (se 7 (by rfl) ⟨42029, by rfl⟩ : syracuseStep 3586517 = 84059) (by norm_num)
theorem B1194457 : Blo 1060614 1194457 := bbase (se 2 (by rfl) ⟨447921, by rfl⟩ : syracuseStep 1194457 = 895843) (by norm_num)
theorem B1194493 : Blo 1060614 1194493 := bbase (se 3 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 1194493 = 447935) (by norm_num)
theorem B1915397 : Blo 1060614 1915397 := bbase (se 4 (by rfl) ⟨179568, by rfl⟩ : syracuseStep 1915397 = 359137) (by norm_num)
theorem B1194529 : Blo 1060614 1194529 := bbase (se 2 (by rfl) ⟨447948, by rfl⟩ : syracuseStep 1194529 = 895897) (by norm_num)
theorem B1194565 : Blo 1060614 1194565 := bbase (se 4 (by rfl) ⟨111990, by rfl⟩ : syracuseStep 1194565 = 223981) (by norm_num)
theorem B4536917 : Blo 1060614 4536917 := bbase (se 8 (by rfl) ⟨26583, by rfl⟩ : syracuseStep 4536917 = 53167) (by norm_num)
theorem B8075861 : Blo 1060614 8075861 := bbase (se 8 (by rfl) ⟨47319, by rfl⟩ : syracuseStep 8075861 = 94639) (by norm_num)
theorem B1194601 : Blo 1060614 1194601 := bbase (se 2 (by rfl) ⟨447975, by rfl⟩ : syracuseStep 1194601 = 895951) (by norm_num)
theorem B1194637 : Blo 1060614 1194637 := bbase (se 3 (by rfl) ⟨223994, by rfl⟩ : syracuseStep 1194637 = 447989) (by norm_num)
theorem B2046605 : Blo 1060614 2046605 := bbase (se 3 (by rfl) ⟨383738, by rfl⟩ : syracuseStep 2046605 = 767477) (by norm_num)
theorem B1194673 : Blo 1060614 1194673 := bbase (se 2 (by rfl) ⟨448002, by rfl⟩ : syracuseStep 1194673 = 896005) (by norm_num)
theorem B2013893 : Blo 1060614 2013893 := bbase (se 4 (by rfl) ⟨188802, by rfl⟩ : syracuseStep 2013893 = 377605) (by norm_num)
theorem B10205909 : Blo 1060614 10205909 := bbase (se 7 (by rfl) ⟨119600, by rfl⟩ : syracuseStep 10205909 = 239201) (by norm_num)
theorem B1194709 : Blo 1060614 1194709 := bbase (se 7 (by rfl) ⟨14000, by rfl⟩ : syracuseStep 1194709 = 28001) (by norm_num)
theorem B1194745 : Blo 1060614 1194745 := bbase (se 2 (by rfl) ⟨448029, by rfl⟩ : syracuseStep 1194745 = 896059) (by norm_num)
theorem B1194781 : Blo 1060614 1194781 := bbase (se 3 (by rfl) ⟨224021, by rfl⟩ : syracuseStep 1194781 = 448043) (by norm_num)
theorem B1194817 : Blo 1060614 1194817 := bbase (se 2 (by rfl) ⟨448056, by rfl⟩ : syracuseStep 1194817 = 896113) (by norm_num)
theorem B1194853 : Blo 1060614 1194853 := bbase (se 4 (by rfl) ⟨112017, by rfl⟩ : syracuseStep 1194853 = 224035) (by norm_num)
theorem B3029861 : Blo 1060614 3029861 := bbase (se 4 (by rfl) ⟨284049, by rfl⟩ : syracuseStep 3029861 = 568099) (by norm_num)
theorem B4537205 : Blo 1060614 4537205 := bbase (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) (by norm_num)
theorem B3586949 : Blo 1060614 3586949 := bbase (se 4 (by rfl) ⟨336276, by rfl⟩ : syracuseStep 3586949 = 672553) (by norm_num)
theorem B1194889 : Blo 1060614 1194889 := bbase (se 2 (by rfl) ⟨448083, by rfl⟩ : syracuseStep 1194889 = 896167) (by norm_num)
theorem B1194925 : Blo 1060614 1194925 := bbase (se 3 (by rfl) ⟨224048, by rfl⟩ : syracuseStep 1194925 = 448097) (by norm_num)
theorem B5389253 : Blo 1060614 5389253 := bbase (se 4 (by rfl) ⟨505242, by rfl⟩ : syracuseStep 5389253 = 1010485) (by norm_num)
theorem B1194961 : Blo 1060614 1194961 := bbase (se 2 (by rfl) ⟨448110, by rfl⟩ : syracuseStep 1194961 = 896221) (by norm_num)
theorem B1194997 : Blo 1060614 1194997 := bbase (se 5 (by rfl) ⟨56015, by rfl⟩ : syracuseStep 1194997 = 112031) (by norm_num)
theorem B1195033 : Blo 1060614 1195033 := bbase (se 2 (by rfl) ⟨448137, by rfl⟩ : syracuseStep 1195033 = 896275) (by norm_num)
theorem B1195069 : Blo 1060614 1195069 := bbase (se 3 (by rfl) ⟨224075, by rfl⟩ : syracuseStep 1195069 = 448151) (by norm_num)
theorem B1195105 : Blo 1060614 1195105 := bbase (se 2 (by rfl) ⟨448164, by rfl⟩ : syracuseStep 1195105 = 896329) (by norm_num)
theorem B1195141 : Blo 1060614 1195141 := bbase (se 4 (by rfl) ⟨112044, by rfl⟩ : syracuseStep 1195141 = 224089) (by norm_num)
theorem B1195177 : Blo 1060614 1195177 := bbase (se 2 (by rfl) ⟨448191, by rfl⟩ : syracuseStep 1195177 = 896383) (by norm_num)
theorem B1195213 : Blo 1060614 1195213 := bbase (se 3 (by rfl) ⟨224102, by rfl⟩ : syracuseStep 1195213 = 448205) (by norm_num)
theorem B1195249 : Blo 1060614 1195249 := bbase (se 2 (by rfl) ⟨448218, by rfl⟩ : syracuseStep 1195249 = 896437) (by norm_num)
theorem B1195285 : Blo 1060614 1195285 := bbase (se 6 (by rfl) ⟨28014, by rfl⟩ : syracuseStep 1195285 = 56029) (by norm_num)
theorem B3587381 : Blo 1060614 3587381 := bbase (se 5 (by rfl) ⟨168158, by rfl⟩ : syracuseStep 3587381 = 336317) (by norm_num)
theorem B1195321 : Blo 1060614 1195321 := bbase (se 2 (by rfl) ⟨448245, by rfl⟩ : syracuseStep 1195321 = 896491) (by norm_num)
theorem B1195357 : Blo 1060614 1195357 := bbase (se 3 (by rfl) ⟨224129, by rfl⟩ : syracuseStep 1195357 = 448259) (by norm_num)
theorem B1195393 : Blo 1060614 1195393 := bbase (se 2 (by rfl) ⟨448272, by rfl⟩ : syracuseStep 1195393 = 896545) (by norm_num)
theorem B1195429 : Blo 1060614 1195429 := bbase (se 4 (by rfl) ⟨112071, by rfl⟩ : syracuseStep 1195429 = 224143) (by norm_num)
theorem B2014645 : Blo 1060614 2014645 := bbase (se 5 (by rfl) ⟨94436, by rfl⟩ : syracuseStep 2014645 = 188873) (by norm_num)
theorem B1195465 : Blo 1060614 1195465 := bbase (se 2 (by rfl) ⟨448299, by rfl⟩ : syracuseStep 1195465 = 896599) (by norm_num)
theorem B1195501 : Blo 1060614 1195501 := bbase (se 3 (by rfl) ⟨224156, by rfl⟩ : syracuseStep 1195501 = 448313) (by norm_num)
theorem B1195537 : Blo 1060614 1195537 := bbase (se 2 (by rfl) ⟨448326, by rfl⟩ : syracuseStep 1195537 = 896653) (by norm_num)
theorem B1195573 : Blo 1060614 1195573 := bbase (se 5 (by rfl) ⟨56042, by rfl⟩ : syracuseStep 1195573 = 112085) (by norm_num)
theorem B2014789 : Blo 1060614 2014789 := bbase (se 4 (by rfl) ⟨188886, by rfl⟩ : syracuseStep 2014789 = 377773) (by norm_num)
theorem B1195609 : Blo 1060614 1195609 := bbase (se 2 (by rfl) ⟨448353, by rfl⟩ : syracuseStep 1195609 = 896707) (by norm_num)
theorem B4537957 : Blo 1060614 4537957 := bbase (se 4 (by rfl) ⟨425433, by rfl⟩ : syracuseStep 4537957 = 850867) (by norm_num)
theorem B1195645 : Blo 1060614 1195645 := bbase (se 3 (by rfl) ⟨224183, by rfl⟩ : syracuseStep 1195645 = 448367) (by norm_num)
theorem B1195681 : Blo 1060614 1195681 := bbase (se 2 (by rfl) ⟨448380, by rfl⟩ : syracuseStep 1195681 = 896761) (by norm_num)
theorem B1195717 : Blo 1060614 1195717 := bbase (se 4 (by rfl) ⟨112098, by rfl⟩ : syracuseStep 1195717 = 224197) (by norm_num)
theorem B2014949 : Blo 1060614 2014949 := bbase (se 4 (by rfl) ⟨188901, by rfl⟩ : syracuseStep 2014949 = 377803) (by norm_num)
theorem B3587813 : Blo 1060614 3587813 := bbase (se 4 (by rfl) ⟨336357, by rfl⟩ : syracuseStep 3587813 = 672715) (by norm_num)
theorem B1195753 : Blo 1060614 1195753 := bbase (se 2 (by rfl) ⟨448407, by rfl⟩ : syracuseStep 1195753 = 896815) (by norm_num)
theorem B1195789 : Blo 1060614 1195789 := bbase (se 3 (by rfl) ⟨224210, by rfl⟩ : syracuseStep 1195789 = 448421) (by norm_num)
theorem B6045461 : Blo 1060614 6045461 := bbase (se 6 (by rfl) ⟨141690, by rfl⟩ : syracuseStep 6045461 = 283381) (by norm_num)
theorem B1195825 : Blo 1060614 1195825 := bbase (se 2 (by rfl) ⟨448434, by rfl⟩ : syracuseStep 1195825 = 896869) (by norm_num)
theorem B20954965 : Blo 1060614 20954965 := bbase (se 9 (by rfl) ⟨61391, by rfl⟩ : syracuseStep 20954965 = 122783) (by norm_num)
theorem B1195861 : Blo 1060614 1195861 := bbase (se 9 (by rfl) ⟨3503, by rfl⟩ : syracuseStep 1195861 = 7007) (by norm_num)
theorem B2015093 : Blo 1060614 2015093 := bbase (se 5 (by rfl) ⟨94457, by rfl⟩ : syracuseStep 2015093 = 188915) (by norm_num)
theorem B1195897 : Blo 1060614 1195897 := bbase (se 2 (by rfl) ⟨448461, by rfl⟩ : syracuseStep 1195897 = 896923) (by norm_num)
theorem B1195933 : Blo 1060614 1195933 := bbase (se 3 (by rfl) ⟨224237, by rfl⟩ : syracuseStep 1195933 = 448475) (by norm_num)
theorem B1195969 : Blo 1060614 1195969 := bbase (se 2 (by rfl) ⟨448488, by rfl⟩ : syracuseStep 1195969 = 896977) (by norm_num)
theorem B1196005 : Blo 1060614 1196005 := bbase (se 4 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 1196005 = 224251) (by norm_num)
theorem B1196041 : Blo 1060614 1196041 := bbase (se 2 (by rfl) ⟨448515, by rfl⟩ : syracuseStep 1196041 = 897031) (by norm_num)
theorem B1196077 : Blo 1060614 1196077 := bbase (se 3 (by rfl) ⟨224264, by rfl⟩ : syracuseStep 1196077 = 448529) (by norm_num)
theorem B1196113 : Blo 1060614 1196113 := bbase (se 2 (by rfl) ⟨448542, by rfl⟩ : syracuseStep 1196113 = 897085) (by norm_num)
theorem B1196149 : Blo 1060614 1196149 := bbase (se 5 (by rfl) ⟨56069, by rfl⟩ : syracuseStep 1196149 = 112139) (by norm_num)
theorem B2015381 : Blo 1060614 2015381 := bbase (se 6 (by rfl) ⟨47235, by rfl⟩ : syracuseStep 2015381 = 94471) (by norm_num)
theorem B3588245 : Blo 1060614 3588245 := bbase (se 6 (by rfl) ⟨84099, by rfl⟩ : syracuseStep 3588245 = 168199) (by norm_num)
theorem B1196185 : Blo 1060614 1196185 := bbase (se 2 (by rfl) ⟨448569, by rfl⟩ : syracuseStep 1196185 = 897139) (by norm_num)
theorem B1196221 : Blo 1060614 1196221 := bbase (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) (by norm_num)
theorem B1196257 : Blo 1060614 1196257 := bbase (se 2 (by rfl) ⟨448596, by rfl⟩ : syracuseStep 1196257 = 897193) (by norm_num)
theorem B1196293 : Blo 1060614 1196293 := bbase (se 4 (by rfl) ⟨112152, by rfl⟩ : syracuseStep 1196293 = 224305) (by norm_num)
theorem B1196329 : Blo 1060614 1196329 := bbase (se 2 (by rfl) ⟨448623, by rfl⟩ : syracuseStep 1196329 = 897247) (by norm_num)
theorem B2015533 : Blo 1060614 2015533 := bbase (se 3 (by rfl) ⟨377912, by rfl⟩ : syracuseStep 2015533 = 755825) (by norm_num)
theorem B4309301 : Blo 1060614 4309301 := bbase (se 5 (by rfl) ⟨201998, by rfl⟩ : syracuseStep 4309301 = 403997) (by norm_num)
theorem B4538693 : Blo 1060614 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B1196365 : Blo 1060614 1196365 := bbase (se 3 (by rfl) ⟨224318, by rfl⟩ : syracuseStep 1196365 = 448637) (by norm_num)
theorem B1196401 : Blo 1060614 1196401 := bbase (se 2 (by rfl) ⟨448650, by rfl⟩ : syracuseStep 1196401 = 897301) (by norm_num)
theorem B4604309 : Blo 1060614 4604309 := bbase (se 6 (by rfl) ⟨107913, by rfl⟩ : syracuseStep 4604309 = 215827) (by norm_num)
theorem B1196437 : Blo 1060614 1196437 := bbase (se 6 (by rfl) ⟨28041, by rfl⟩ : syracuseStep 1196437 = 56083) (by norm_num)
theorem B3031445 : Blo 1060614 3031445 := bbase (se 6 (by rfl) ⟨71049, by rfl⟩ : syracuseStep 3031445 = 142099) (by norm_num)
theorem B1196473 : Blo 1060614 1196473 := bbase (se 2 (by rfl) ⟨448677, by rfl⟩ : syracuseStep 1196473 = 897355) (by norm_num)
theorem B1196509 : Blo 1060614 1196509 := bbase (se 3 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 1196509 = 448691) (by norm_num)
theorem B1196545 : Blo 1060614 1196545 := bbase (se 2 (by rfl) ⟨448704, by rfl⟩ : syracuseStep 1196545 = 897409) (by norm_num)
theorem B1196581 : Blo 1060614 1196581 := bbase (se 4 (by rfl) ⟨112179, by rfl⟩ : syracuseStep 1196581 = 224359) (by norm_num)
theorem B3588677 : Blo 1060614 3588677 := bbase (se 4 (by rfl) ⟨336438, by rfl⟩ : syracuseStep 3588677 = 672877) (by norm_num)
theorem B1196617 : Blo 1060614 1196617 := bbase (se 2 (by rfl) ⟨448731, by rfl⟩ : syracuseStep 1196617 = 897463) (by norm_num)
theorem B1229401 : Blo 1060614 1229401 := bbase (se 2 (by rfl) ⟨461025, by rfl⟩ : syracuseStep 1229401 = 922051) (by norm_num)
theorem B2015837 : Blo 1060614 2015837 := bbase (se 3 (by rfl) ⟨377969, by rfl⟩ : syracuseStep 2015837 = 755939) (by norm_num)
theorem B1196653 : Blo 1060614 1196653 := bbase (se 3 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 1196653 = 448745) (by norm_num)
theorem B1196689 : Blo 1060614 1196689 := bbase (se 2 (by rfl) ⟨448758, by rfl⟩ : syracuseStep 1196689 = 897517) (by norm_num)
theorem B1196725 : Blo 1060614 1196725 := bbase (se 5 (by rfl) ⟨56096, by rfl⟩ : syracuseStep 1196725 = 112193) (by norm_num)
theorem B1196761 : Blo 1060614 1196761 := bbase (se 2 (by rfl) ⟨448785, by rfl⟩ : syracuseStep 1196761 = 897571) (by norm_num)
theorem B1196797 : Blo 1060614 1196797 := bbase (se 3 (by rfl) ⟨224399, by rfl⟩ : syracuseStep 1196797 = 448799) (by norm_num)
theorem B3228437 : Blo 1060614 3228437 := bbase (se 6 (by rfl) ⟨75666, by rfl⟩ : syracuseStep 3228437 = 151333) (by norm_num)
theorem B1196833 : Blo 1060614 1196833 := bbase (se 2 (by rfl) ⟨448812, by rfl⟩ : syracuseStep 1196833 = 897625) (by norm_num)
theorem B1196869 : Blo 1060614 1196869 := bbase (se 4 (by rfl) ⟨112206, by rfl⟩ : syracuseStep 1196869 = 224413) (by norm_num)
theorem B1196905 : Blo 1060614 1196905 := bbase (se 2 (by rfl) ⟨448839, by rfl⟩ : syracuseStep 1196905 = 897679) (by norm_num)
theorem B1196941 : Blo 1060614 1196941 := bbase (se 3 (by rfl) ⟨224426, by rfl⟩ : syracuseStep 1196941 = 448853) (by norm_num)
theorem B1196977 : Blo 1060614 1196977 := bbase (se 2 (by rfl) ⟨448866, by rfl⟩ : syracuseStep 1196977 = 897733) (by norm_num)
theorem B1197013 : Blo 1060614 1197013 := bbase (se 7 (by rfl) ⟨14027, by rfl⟩ : syracuseStep 1197013 = 28055) (by norm_num)
theorem B3589109 : Blo 1060614 3589109 := bbase (se 5 (by rfl) ⟨168239, by rfl⟩ : syracuseStep 3589109 = 336479) (by norm_num)
theorem B1197049 : Blo 1060614 1197049 := bbase (se 2 (by rfl) ⟨448893, by rfl⟩ : syracuseStep 1197049 = 897787) (by norm_num)
theorem B1197085 : Blo 1060614 1197085 := bbase (se 3 (by rfl) ⟨224453, by rfl⟩ : syracuseStep 1197085 = 448907) (by norm_num)
theorem B1197121 : Blo 1060614 1197121 := bbase (se 2 (by rfl) ⟨448920, by rfl⟩ : syracuseStep 1197121 = 897841) (by norm_num)
theorem B1197157 : Blo 1060614 1197157 := bbase (se 4 (by rfl) ⟨112233, by rfl⟩ : syracuseStep 1197157 = 224467) (by norm_num)
theorem B1197193 : Blo 1060614 1197193 := bbase (se 2 (by rfl) ⟨448947, by rfl⟩ : syracuseStep 1197193 = 897895) (by norm_num)
theorem B1197229 : Blo 1060614 1197229 := bbase (se 3 (by rfl) ⟨224480, by rfl⟩ : syracuseStep 1197229 = 448961) (by norm_num)
theorem B1197265 : Blo 1060614 1197265 := bbase (se 2 (by rfl) ⟨448974, by rfl⟩ : syracuseStep 1197265 = 897949) (by norm_num)
theorem B1197301 : Blo 1060614 1197301 := bbase (se 5 (by rfl) ⟨56123, by rfl⟩ : syracuseStep 1197301 = 112247) (by norm_num)
theorem B1197337 : Blo 1060614 1197337 := bbase (se 2 (by rfl) ⟨449001, by rfl⟩ : syracuseStep 1197337 = 898003) (by norm_num)
theorem B1197373 : Blo 1060614 1197373 := bbase (se 3 (by rfl) ⟨224507, by rfl⟩ : syracuseStep 1197373 = 449015) (by norm_num)
theorem B2016589 : Blo 1060614 2016589 := bbase (se 3 (by rfl) ⟨378110, by rfl⟩ : syracuseStep 2016589 = 756221) (by norm_num)
theorem B1197409 : Blo 1060614 1197409 := bbase (se 2 (by rfl) ⟨449028, by rfl⟩ : syracuseStep 1197409 = 898057) (by norm_num)
theorem B1197445 : Blo 1060614 1197445 := bbase (se 4 (by rfl) ⟨112260, by rfl⟩ : syracuseStep 1197445 = 224521) (by norm_num)
theorem B3589541 : Blo 1060614 3589541 := bbase (se 4 (by rfl) ⟨336519, by rfl⟩ : syracuseStep 3589541 = 673039) (by norm_num)
theorem B1197481 : Blo 1060614 1197481 := bbase (se 2 (by rfl) ⟨449055, by rfl⟩ : syracuseStep 1197481 = 898111) (by norm_num)
theorem B1197517 : Blo 1060614 1197517 := bbase (se 3 (by rfl) ⟨224534, by rfl⟩ : syracuseStep 1197517 = 449069) (by norm_num)
theorem B2016733 : Blo 1060614 2016733 := bbase (se 3 (by rfl) ⟨378137, by rfl⟩ : syracuseStep 2016733 = 756275) (by norm_num)
theorem B1197553 : Blo 1060614 1197553 := bbase (se 2 (by rfl) ⟨449082, by rfl⟩ : syracuseStep 1197553 = 898165) (by norm_num)
theorem B1164817 : Blo 1060614 1164817 := bbase (se 2 (by rfl) ⟨436806, by rfl⟩ : syracuseStep 1164817 = 873613) (by norm_num)
theorem B1197589 : Blo 1060614 1197589 := bbase (se 6 (by rfl) ⟨28068, by rfl⟩ : syracuseStep 1197589 = 56137) (by norm_num)
theorem B1197625 : Blo 1060614 1197625 := bbase (se 2 (by rfl) ⟨449109, by rfl⟩ : syracuseStep 1197625 = 898219) (by norm_num)
theorem B1197661 : Blo 1060614 1197661 := bbase (se 3 (by rfl) ⟨224561, by rfl⟩ : syracuseStep 1197661 = 449123) (by norm_num)
theorem B2016893 : Blo 1060614 2016893 := bbase (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) (by norm_num)
theorem B1590941 : Blo 1060614 1590941 := bbase (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) (by norm_num)
theorem B1590965 : Blo 1060614 1590965 := bbase (se 5 (by rfl) ⟨74576, by rfl⟩ : syracuseStep 1590965 = 149153) (by norm_num)
theorem B1590989 : Blo 1060614 1590989 := bbase (se 3 (by rfl) ⟨298310, by rfl⟩ : syracuseStep 1590989 = 596621) (by norm_num)
theorem B1591013 : Blo 1060614 1591013 := bbase (se 4 (by rfl) ⟨149157, by rfl⟩ : syracuseStep 1591013 = 298315) (by norm_num)
theorem B1591037 : Blo 1060614 1591037 := bbase (se 3 (by rfl) ⟨298319, by rfl⟩ : syracuseStep 1591037 = 596639) (by norm_num)
theorem B3229445 : Blo 1060614 3229445 := bbase (se 4 (by rfl) ⟨302760, by rfl⟩ : syracuseStep 3229445 = 605521) (by norm_num)
theorem B2017037 : Blo 1060614 2017037 := bbase (se 3 (by rfl) ⟨378194, by rfl⟩ : syracuseStep 2017037 = 756389) (by norm_num)
theorem B1591061 : Blo 1060614 1591061 := bbase (se 6 (by rfl) ⟨37290, by rfl⟩ : syracuseStep 1591061 = 74581) (by norm_num)
theorem B1591085 : Blo 1060614 1591085 := bbase (se 3 (by rfl) ⟨298328, by rfl⟩ : syracuseStep 1591085 = 596657) (by norm_num)
theorem B1591109 : Blo 1060614 1591109 := bbase (se 4 (by rfl) ⟨149166, by rfl⟩ : syracuseStep 1591109 = 298333) (by norm_num)
theorem B3589973 : Blo 1060614 3589973 := bbase (se 9 (by rfl) ⟨10517, by rfl⟩ : syracuseStep 3589973 = 21035) (by norm_num)
theorem B1591133 : Blo 1060614 1591133 := bbase (se 3 (by rfl) ⟨298337, by rfl⟩ : syracuseStep 1591133 = 596675) (by norm_num)
theorem B1591157 : Blo 1060614 1591157 := bbase (se 5 (by rfl) ⟨74585, by rfl⟩ : syracuseStep 1591157 = 149171) (by norm_num)
theorem B1591181 : Blo 1060614 1591181 := bbase (se 3 (by rfl) ⟨298346, by rfl⟩ : syracuseStep 1591181 = 596693) (by norm_num)
theorem B1591205 : Blo 1060614 1591205 := bbase (se 4 (by rfl) ⟨149175, by rfl⟩ : syracuseStep 1591205 = 298351) (by norm_num)
theorem B1361837 : Blo 1060614 1361837 := bbase (se 3 (by rfl) ⟨255344, by rfl⟩ : syracuseStep 1361837 = 510689) (by norm_num)
theorem B1591229 : Blo 1060614 1591229 := bbase (se 3 (by rfl) ⟨298355, by rfl⟩ : syracuseStep 1591229 = 596711) (by norm_num)
theorem B1591253 : Blo 1060614 1591253 := bbase (se 7 (by rfl) ⟨18647, by rfl⟩ : syracuseStep 1591253 = 37295) (by norm_num)
theorem B1591277 : Blo 1060614 1591277 := bbase (se 3 (by rfl) ⟨298364, by rfl⟩ : syracuseStep 1591277 = 596729) (by norm_num)
theorem B1591301 : Blo 1060614 1591301 := bbase (se 4 (by rfl) ⟨149184, by rfl⟩ : syracuseStep 1591301 = 298369) (by norm_num)
theorem B1591325 : Blo 1060614 1591325 := bbase (se 3 (by rfl) ⟨298373, by rfl⟩ : syracuseStep 1591325 = 596747) (by norm_num)
theorem B2017325 : Blo 1060614 2017325 := bbase (se 3 (by rfl) ⟨378248, by rfl⟩ : syracuseStep 2017325 = 756497) (by norm_num)
theorem B1591349 : Blo 1060614 1591349 := bbase (se 5 (by rfl) ⟨74594, by rfl⟩ : syracuseStep 1591349 = 149189) (by norm_num)
theorem B1591373 : Blo 1060614 1591373 := bbase (se 3 (by rfl) ⟨298382, by rfl⟩ : syracuseStep 1591373 = 596765) (by norm_num)
theorem B1591397 : Blo 1060614 1591397 := bbase (se 4 (by rfl) ⟨149193, by rfl⟩ : syracuseStep 1591397 = 298387) (by norm_num)
theorem B1132661 : Blo 1060614 1132661 := bbase (se 5 (by rfl) ⟨53093, by rfl⟩ : syracuseStep 1132661 = 106187) (by norm_num)
theorem B1591421 : Blo 1060614 1591421 := bbase (se 3 (by rfl) ⟨298391, by rfl⟩ : syracuseStep 1591421 = 596783) (by norm_num)
theorem B1591445 : Blo 1060614 1591445 := bbase (se 6 (by rfl) ⟨37299, by rfl⟩ : syracuseStep 1591445 = 74599) (by norm_num)
theorem B1591469 : Blo 1060614 1591469 := bbase (se 3 (by rfl) ⟨298400, by rfl⟩ : syracuseStep 1591469 = 596801) (by norm_num)
theorem B1591493 : Blo 1060614 1591493 := bbase (se 4 (by rfl) ⟨149202, by rfl⟩ : syracuseStep 1591493 = 298405) (by norm_num)
theorem B2017477 : Blo 1060614 2017477 := bbase (se 4 (by rfl) ⟨189138, by rfl⟩ : syracuseStep 2017477 = 378277) (by norm_num)
theorem B1591517 : Blo 1060614 1591517 := bbase (se 3 (by rfl) ⟨298409, by rfl⟩ : syracuseStep 1591517 = 596819) (by norm_num)
theorem B1591541 : Blo 1060614 1591541 := bbase (se 5 (by rfl) ⟨74603, by rfl⟩ : syracuseStep 1591541 = 149207) (by norm_num)
theorem B3590405 : Blo 1060614 3590405 := bbase (se 4 (by rfl) ⟨336600, by rfl⟩ : syracuseStep 3590405 = 673201) (by norm_num)
theorem B1591565 : Blo 1060614 1591565 := bbase (se 3 (by rfl) ⟨298418, by rfl⟩ : syracuseStep 1591565 = 596837) (by norm_num)
theorem B1591589 : Blo 1060614 1591589 := bbase (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) (by norm_num)
theorem B1132849 : Blo 1060614 1132849 := bbase (se 2 (by rfl) ⟨424818, by rfl⟩ : syracuseStep 1132849 = 849637) (by norm_num)
theorem B1591613 : Blo 1060614 1591613 := bbase (se 3 (by rfl) ⟨298427, by rfl⟩ : syracuseStep 1591613 = 596855) (by norm_num)
theorem B1591637 : Blo 1060614 1591637 := bbase (se 10 (by rfl) ⟨2331, by rfl⟩ : syracuseStep 1591637 = 4663) (by norm_num)
theorem B1591661 : Blo 1060614 1591661 := bbase (se 3 (by rfl) ⟨298436, by rfl⟩ : syracuseStep 1591661 = 596873) (by norm_num)
theorem B1591685 : Blo 1060614 1591685 := bbase (se 4 (by rfl) ⟨149220, by rfl⟩ : syracuseStep 1591685 = 298441) (by norm_num)
theorem B1591709 : Blo 1060614 1591709 := bbase (se 3 (by rfl) ⟨298445, by rfl⟩ : syracuseStep 1591709 = 596891) (by norm_num)
theorem B1591733 : Blo 1060614 1591733 := bbase (se 5 (by rfl) ⟨74612, by rfl⟩ : syracuseStep 1591733 = 149225) (by norm_num)
theorem B1591757 : Blo 1060614 1591757 := bbase (se 3 (by rfl) ⟨298454, by rfl⟩ : syracuseStep 1591757 = 596909) (by norm_num)
theorem B1591781 : Blo 1060614 1591781 := bbase (se 4 (by rfl) ⟨149229, by rfl⟩ : syracuseStep 1591781 = 298459) (by norm_num)
theorem B1133033 : Blo 1060614 1133033 := bbase (se 2 (by rfl) ⟨424887, by rfl⟩ : syracuseStep 1133033 = 849775) (by norm_num)
theorem B2017781 : Blo 1060614 2017781 := bbase (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) (by norm_num)
theorem B1591805 : Blo 1060614 1591805 := bbase (se 3 (by rfl) ⟨298463, by rfl⟩ : syracuseStep 1591805 = 596927) (by norm_num)
theorem B1591829 : Blo 1060614 1591829 := bbase (se 6 (by rfl) ⟨37308, by rfl⟩ : syracuseStep 1591829 = 74617) (by norm_num)
theorem B1591853 : Blo 1060614 1591853 := bbase (se 3 (by rfl) ⟨298472, by rfl⟩ : syracuseStep 1591853 = 596945) (by norm_num)
theorem B1591877 : Blo 1060614 1591877 := bbase (se 4 (by rfl) ⟨149238, by rfl⟩ : syracuseStep 1591877 = 298477) (by norm_num)
theorem B1591901 : Blo 1060614 1591901 := bbase (se 3 (by rfl) ⟨298481, by rfl⟩ : syracuseStep 1591901 = 596963) (by norm_num)
theorem B1591925 : Blo 1060614 1591925 := bbase (se 5 (by rfl) ⟨74621, by rfl⟩ : syracuseStep 1591925 = 149243) (by norm_num)
theorem B1591949 : Blo 1060614 1591949 := bbase (se 3 (by rfl) ⟨298490, by rfl⟩ : syracuseStep 1591949 = 596981) (by norm_num)
theorem B1591973 : Blo 1060614 1591973 := bbase (se 4 (by rfl) ⟨149247, by rfl⟩ : syracuseStep 1591973 = 298495) (by norm_num)
theorem B2869925 : Blo 1060614 2869925 := bbase (se 4 (by rfl) ⟨269055, by rfl⟩ : syracuseStep 2869925 = 538111) (by norm_num)
theorem B3590837 : Blo 1060614 3590837 := bbase (se 5 (by rfl) ⟨168320, by rfl⟩ : syracuseStep 3590837 = 336641) (by norm_num)
theorem B1591997 : Blo 1060614 1591997 := bbase (se 3 (by rfl) ⟨298499, by rfl⟩ : syracuseStep 1591997 = 596999) (by norm_num)
theorem B1592021 : Blo 1060614 1592021 := bbase (se 7 (by rfl) ⟨18656, by rfl⟩ : syracuseStep 1592021 = 37313) (by norm_num)
theorem B1592045 : Blo 1060614 1592045 := bbase (se 3 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 1592045 = 597017) (by norm_num)
theorem B1592069 : Blo 1060614 1592069 := bbase (se 4 (by rfl) ⟨149256, by rfl⟩ : syracuseStep 1592069 = 298513) (by norm_num)
theorem B6540053 : Blo 1060614 6540053 := bbase (se 6 (by rfl) ⟨153282, by rfl⟩ : syracuseStep 6540053 = 306565) (by norm_num)
theorem B1592093 : Blo 1060614 1592093 := bbase (se 3 (by rfl) ⟨298517, by rfl⟩ : syracuseStep 1592093 = 597035) (by norm_num)
theorem B1592117 : Blo 1060614 1592117 := bbase (se 5 (by rfl) ⟨74630, by rfl⟩ : syracuseStep 1592117 = 149261) (by norm_num)
theorem B1592141 : Blo 1060614 1592141 := bbase (se 3 (by rfl) ⟨298526, by rfl⟩ : syracuseStep 1592141 = 597053) (by norm_num)
theorem B1592165 : Blo 1060614 1592165 := bbase (se 4 (by rfl) ⟨149265, by rfl⟩ : syracuseStep 1592165 = 298531) (by norm_num)
theorem B1592189 : Blo 1060614 1592189 := bbase (se 3 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 1592189 = 597071) (by norm_num)
theorem B1592213 : Blo 1060614 1592213 := bbase (se 6 (by rfl) ⟨37317, by rfl⟩ : syracuseStep 1592213 = 74635) (by norm_num)
theorem B1592237 : Blo 1060614 1592237 := bbase (se 3 (by rfl) ⟨298544, by rfl⟩ : syracuseStep 1592237 = 597089) (by norm_num)
theorem B1592261 : Blo 1060614 1592261 := bbase (se 4 (by rfl) ⟨149274, by rfl⟩ : syracuseStep 1592261 = 298549) (by norm_num)
theorem B1592285 : Blo 1060614 1592285 := bbase (se 3 (by rfl) ⟨298553, by rfl⟩ : syracuseStep 1592285 = 597107) (by norm_num)
theorem B1592309 : Blo 1060614 1592309 := bbase (se 5 (by rfl) ⟨74639, by rfl⟩ : syracuseStep 1592309 = 149279) (by norm_num)
theorem B1592333 : Blo 1060614 1592333 := bbase (se 3 (by rfl) ⟨298562, by rfl⟩ : syracuseStep 1592333 = 597125) (by norm_num)
theorem B1592357 : Blo 1060614 1592357 := bbase (se 4 (by rfl) ⟨149283, by rfl⟩ : syracuseStep 1592357 = 298567) (by norm_num)
theorem B1592381 : Blo 1060614 1592381 := bbase (se 3 (by rfl) ⟨298571, by rfl⟩ : syracuseStep 1592381 = 597143) (by norm_num)
theorem B1592405 : Blo 1060614 1592405 := bbase (se 8 (by rfl) ⟨9330, by rfl⟩ : syracuseStep 1592405 = 18661) (by norm_num)
theorem B3591269 : Blo 1060614 3591269 := bbase (se 4 (by rfl) ⟨336681, by rfl⟩ : syracuseStep 3591269 = 673363) (by norm_num)
theorem B1592429 : Blo 1060614 1592429 := bbase (se 3 (by rfl) ⟨298580, by rfl⟩ : syracuseStep 1592429 = 597161) (by norm_num)
theorem B1592453 : Blo 1060614 1592453 := bbase (se 4 (by rfl) ⟨149292, by rfl⟩ : syracuseStep 1592453 = 298585) (by norm_num)
theorem B1592477 : Blo 1060614 1592477 := bbase (se 3 (by rfl) ⟨298589, by rfl⟩ : syracuseStep 1592477 = 597179) (by norm_num)
theorem B1592501 : Blo 1060614 1592501 := bbase (se 5 (by rfl) ⟨74648, by rfl⟩ : syracuseStep 1592501 = 149297) (by norm_num)
theorem B1592525 : Blo 1060614 1592525 := bbase (se 3 (by rfl) ⟨298598, by rfl⟩ : syracuseStep 1592525 = 597197) (by norm_num)
theorem B1133785 : Blo 1060614 1133785 := bbase (se 2 (by rfl) ⟨425169, by rfl⟩ : syracuseStep 1133785 = 850339) (by norm_num)
theorem B1592549 : Blo 1060614 1592549 := bbase (se 4 (by rfl) ⟨149301, by rfl⟩ : syracuseStep 1592549 = 298603) (by norm_num)
theorem B2018533 : Blo 1060614 2018533 := bbase (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) (by norm_num)
theorem B1592573 : Blo 1060614 1592573 := bbase (se 3 (by rfl) ⟨298607, by rfl⟩ : syracuseStep 1592573 = 597215) (by norm_num)
theorem B20401429 : Blo 1060614 20401429 := bbase (se 6 (by rfl) ⟨478158, by rfl⟩ : syracuseStep 20401429 = 956317) (by norm_num)
theorem B1592597 : Blo 1060614 1592597 := bbase (se 6 (by rfl) ⟨37326, by rfl⟩ : syracuseStep 1592597 = 74653) (by norm_num)
theorem B5524757 : Blo 1060614 5524757 := bbase (se 6 (by rfl) ⟨129486, by rfl⟩ : syracuseStep 5524757 = 258973) (by norm_num)
theorem B1133857 : Blo 1060614 1133857 := bbase (se 2 (by rfl) ⟨425196, by rfl⟩ : syracuseStep 1133857 = 850393) (by norm_num)
theorem B1592621 : Blo 1060614 1592621 := bbase (se 3 (by rfl) ⟨298616, by rfl⟩ : syracuseStep 1592621 = 597233) (by norm_num)
theorem B1592645 : Blo 1060614 1592645 := bbase (se 4 (by rfl) ⟨149310, by rfl⟩ : syracuseStep 1592645 = 298621) (by norm_num)
theorem B1592669 : Blo 1060614 1592669 := bbase (se 3 (by rfl) ⟨298625, by rfl⟩ : syracuseStep 1592669 = 597251) (by norm_num)
theorem B1592693 : Blo 1060614 1592693 := bbase (se 5 (by rfl) ⟨74657, by rfl⟩ : syracuseStep 1592693 = 149315) (by norm_num)
theorem B2018677 : Blo 1060614 2018677 := bbase (se 5 (by rfl) ⟨94625, by rfl⟩ : syracuseStep 2018677 = 189251) (by norm_num)
theorem B1592717 : Blo 1060614 1592717 := bbase (se 3 (by rfl) ⟨298634, by rfl⟩ : syracuseStep 1592717 = 597269) (by norm_num)
theorem B1592741 : Blo 1060614 1592741 := bbase (se 4 (by rfl) ⟨149319, by rfl⟩ : syracuseStep 1592741 = 298639) (by norm_num)
theorem B1592765 : Blo 1060614 1592765 := bbase (se 3 (by rfl) ⟨298643, by rfl⟩ : syracuseStep 1592765 = 597287) (by norm_num)
theorem B1592789 : Blo 1060614 1592789 := bbase (se 7 (by rfl) ⟨18665, by rfl⟩ : syracuseStep 1592789 = 37331) (by norm_num)
theorem B1134037 : Blo 1060614 1134037 := bbase (se 7 (by rfl) ⟨13289, by rfl⟩ : syracuseStep 1134037 = 26579) (by norm_num)
theorem B1592813 : Blo 1060614 1592813 := bbase (se 3 (by rfl) ⟨298652, by rfl⟩ : syracuseStep 1592813 = 597305) (by norm_num)
theorem B4083205 : Blo 1060614 4083205 := bbase (se 4 (by rfl) ⟨382800, by rfl⟩ : syracuseStep 4083205 = 765601) (by norm_num)
theorem B1592837 : Blo 1060614 1592837 := bbase (se 4 (by rfl) ⟨149328, by rfl⟩ : syracuseStep 1592837 = 298657) (by norm_num)
theorem B2018837 : Blo 1060614 2018837 := bbase (se 6 (by rfl) ⟨47316, by rfl⟩ : syracuseStep 2018837 = 94633) (by norm_num)
theorem B3591701 : Blo 1060614 3591701 := bbase (se 6 (by rfl) ⟨84180, by rfl⟩ : syracuseStep 3591701 = 168361) (by norm_num)
theorem B1592861 : Blo 1060614 1592861 := bbase (se 3 (by rfl) ⟨298661, by rfl⟩ : syracuseStep 1592861 = 597323) (by norm_num)
theorem B4541989 : Blo 1060614 4541989 := bbase (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) (by norm_num)
theorem B1592885 : Blo 1060614 1592885 := bbase (se 5 (by rfl) ⟨74666, by rfl⟩ : syracuseStep 1592885 = 149333) (by norm_num)
theorem B1592909 : Blo 1060614 1592909 := bbase (se 3 (by rfl) ⟨298670, by rfl⟩ : syracuseStep 1592909 = 597341) (by norm_num)
theorem B9064021 : Blo 1060614 9064021 := bbase (se 8 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 9064021 = 106219) (by norm_num)
theorem B1592933 : Blo 1060614 1592933 := bbase (se 4 (by rfl) ⟨149337, by rfl⟩ : syracuseStep 1592933 = 298675) (by norm_num)
theorem B1592957 : Blo 1060614 1592957 := bbase (se 3 (by rfl) ⟨298679, by rfl⟩ : syracuseStep 1592957 = 597359) (by norm_num)
theorem B1592981 : Blo 1060614 1592981 := bbase (se 6 (by rfl) ⟨37335, by rfl⟩ : syracuseStep 1592981 = 74671) (by norm_num)
theorem B2018981 : Blo 1060614 2018981 := bbase (se 4 (by rfl) ⟨189279, by rfl⟩ : syracuseStep 2018981 = 378559) (by norm_num)
theorem B1593005 : Blo 1060614 1593005 := bbase (se 3 (by rfl) ⟨298688, by rfl⟩ : syracuseStep 1593005 = 597377) (by norm_num)
theorem B4312757 : Blo 1060614 4312757 := bbase (se 5 (by rfl) ⟨202160, by rfl⟩ : syracuseStep 4312757 = 404321) (by norm_num)
theorem B1593029 : Blo 1060614 1593029 := bbase (se 4 (by rfl) ⟨149346, by rfl⟩ : syracuseStep 1593029 = 298693) (by norm_num)
theorem B1593053 : Blo 1060614 1593053 := bbase (se 3 (by rfl) ⟨298697, by rfl⟩ : syracuseStep 1593053 = 597395) (by norm_num)
theorem B1593077 : Blo 1060614 1593077 := bbase (se 5 (by rfl) ⟨74675, by rfl⟩ : syracuseStep 1593077 = 149351) (by norm_num)
theorem B1593101 : Blo 1060614 1593101 := bbase (se 3 (by rfl) ⟨298706, by rfl⟩ : syracuseStep 1593101 = 597413) (by norm_num)
theorem B1593125 : Blo 1060614 1593125 := bbase (se 4 (by rfl) ⟨149355, by rfl⟩ : syracuseStep 1593125 = 298711) (by norm_num)
theorem B1593149 : Blo 1060614 1593149 := bbase (se 3 (by rfl) ⟨298715, by rfl⟩ : syracuseStep 1593149 = 597431) (by norm_num)
theorem B4312901 : Blo 1060614 4312901 := bbase (se 4 (by rfl) ⟨404334, by rfl⟩ : syracuseStep 4312901 = 808669) (by norm_num)
theorem B1593173 : Blo 1060614 1593173 := bbase (se 9 (by rfl) ⟨4667, by rfl⟩ : syracuseStep 1593173 = 9335) (by norm_num)
theorem B1789789 : Blo 1060614 1789789 := bbase (se 3 (by rfl) ⟨335585, by rfl⟩ : syracuseStep 1789789 = 671171) (by norm_num)
theorem B1593197 : Blo 1060614 1593197 := bbase (se 3 (by rfl) ⟨298724, by rfl⟩ : syracuseStep 1593197 = 597449) (by norm_num)
theorem B1593221 : Blo 1060614 1593221 := bbase (se 4 (by rfl) ⟨149364, by rfl⟩ : syracuseStep 1593221 = 298729) (by norm_num)
theorem B1134481 : Blo 1060614 1134481 := bbase (se 2 (by rfl) ⟨425430, by rfl⟩ : syracuseStep 1134481 = 850861) (by norm_num)
theorem B1593245 : Blo 1060614 1593245 := bbase (se 3 (by rfl) ⟨298733, by rfl⟩ : syracuseStep 1593245 = 597467) (by norm_num)
theorem B1789877 : Blo 1060614 1789877 := bbase (se 5 (by rfl) ⟨83900, by rfl⟩ : syracuseStep 1789877 = 167801) (by norm_num)
theorem B1593269 : Blo 1060614 1593269 := bbase (se 5 (by rfl) ⟨74684, by rfl⟩ : syracuseStep 1593269 = 149369) (by norm_num)
theorem B2019269 : Blo 1060614 2019269 := bbase (se 4 (by rfl) ⟨189306, by rfl⟩ : syracuseStep 2019269 = 378613) (by norm_num)
theorem B3592133 : Blo 1060614 3592133 := bbase (se 4 (by rfl) ⟨336762, by rfl⟩ : syracuseStep 3592133 = 673525) (by norm_num)
theorem B1593293 : Blo 1060614 1593293 := bbase (se 3 (by rfl) ⟨298742, by rfl⟩ : syracuseStep 1593293 = 597485) (by norm_num)
theorem B7655381 : Blo 1060614 7655381 := bbase (se 7 (by rfl) ⟨89711, by rfl⟩ : syracuseStep 7655381 = 179423) (by norm_num)
theorem B1593317 : Blo 1060614 1593317 := bbase (se 4 (by rfl) ⟨149373, by rfl⟩ : syracuseStep 1593317 = 298747) (by norm_num)
theorem B1593341 : Blo 1060614 1593341 := bbase (se 3 (by rfl) ⟨298751, by rfl⟩ : syracuseStep 1593341 = 597503) (by norm_num)
theorem B1134605 : Blo 1060614 1134605 := bbase (se 3 (by rfl) ⟨212738, by rfl⟩ : syracuseStep 1134605 = 425477) (by norm_num)
theorem B1593365 : Blo 1060614 1593365 := bbase (se 6 (by rfl) ⟨37344, by rfl⟩ : syracuseStep 1593365 = 74689) (by norm_num)
theorem B1593389 : Blo 1060614 1593389 := bbase (se 3 (by rfl) ⟨298760, by rfl⟩ : syracuseStep 1593389 = 597521) (by norm_num)
theorem B1790005 : Blo 1060614 1790005 := bbase (se 5 (by rfl) ⟨83906, by rfl⟩ : syracuseStep 1790005 = 167813) (by norm_num)
theorem B1593413 : Blo 1060614 1593413 := bbase (se 4 (by rfl) ⟨149382, by rfl⟩ : syracuseStep 1593413 = 298765) (by norm_num)
theorem B1593437 : Blo 1060614 1593437 := bbase (se 3 (by rfl) ⟨298769, by rfl⟩ : syracuseStep 1593437 = 597539) (by norm_num)
theorem B2019421 : Blo 1060614 2019421 := bbase (se 3 (by rfl) ⟨378641, by rfl⟩ : syracuseStep 2019421 = 757283) (by norm_num)
theorem B1593461 : Blo 1060614 1593461 := bbase (se 5 (by rfl) ⟨74693, by rfl⟩ : syracuseStep 1593461 = 149387) (by norm_num)
theorem B1790093 : Blo 1060614 1790093 := bbase (se 3 (by rfl) ⟨335642, by rfl⟩ : syracuseStep 1790093 = 671285) (by norm_num)
theorem B1593485 : Blo 1060614 1593485 := bbase (se 3 (by rfl) ⟨298778, by rfl⟩ : syracuseStep 1593485 = 597557) (by norm_num)
theorem B1593509 : Blo 1060614 1593509 := bbase (se 4 (by rfl) ⟨149391, by rfl⟩ : syracuseStep 1593509 = 298783) (by norm_num)
theorem B1593533 : Blo 1060614 1593533 := bbase (se 3 (by rfl) ⟨298787, by rfl⟩ : syracuseStep 1593533 = 597575) (by norm_num)
theorem B1593557 : Blo 1060614 1593557 := bbase (se 7 (by rfl) ⟨18674, by rfl⟩ : syracuseStep 1593557 = 37349) (by norm_num)
theorem B1593581 : Blo 1060614 1593581 := bbase (se 3 (by rfl) ⟨298796, by rfl⟩ : syracuseStep 1593581 = 597593) (by norm_num)
theorem B1593605 : Blo 1060614 1593605 := bbase (se 4 (by rfl) ⟨149400, by rfl⟩ : syracuseStep 1593605 = 298801) (by norm_num)
theorem B1134857 : Blo 1060614 1134857 := bbase (se 2 (by rfl) ⟨425571, by rfl⟩ : syracuseStep 1134857 = 851143) (by norm_num)
theorem B1790221 : Blo 1060614 1790221 := bbase (se 3 (by rfl) ⟨335666, by rfl⟩ : syracuseStep 1790221 = 671333) (by norm_num)
theorem B1593629 : Blo 1060614 1593629 := bbase (se 3 (by rfl) ⟨298805, by rfl⟩ : syracuseStep 1593629 = 597611) (by norm_num)
theorem B1593653 : Blo 1060614 1593653 := bbase (se 5 (by rfl) ⟨74702, by rfl⟩ : syracuseStep 1593653 = 149405) (by norm_num)
theorem B1593677 : Blo 1060614 1593677 := bbase (se 3 (by rfl) ⟨298814, by rfl⟩ : syracuseStep 1593677 = 597629) (by norm_num)
theorem B1790309 : Blo 1060614 1790309 := bbase (se 4 (by rfl) ⟨167841, by rfl⟩ : syracuseStep 1790309 = 335683) (by norm_num)
theorem B1593701 : Blo 1060614 1593701 := bbase (se 4 (by rfl) ⟨149409, by rfl⟩ : syracuseStep 1593701 = 298819) (by norm_num)
theorem B3592565 : Blo 1060614 3592565 := bbase (se 5 (by rfl) ⟨168401, by rfl⟩ : syracuseStep 3592565 = 336803) (by norm_num)
theorem B1593725 : Blo 1060614 1593725 := bbase (se 3 (by rfl) ⟨298823, by rfl⟩ : syracuseStep 1593725 = 597647) (by norm_num)
theorem B2019725 : Blo 1060614 2019725 := bbase (se 3 (by rfl) ⟨378698, by rfl⟩ : syracuseStep 2019725 = 757397) (by norm_num)
theorem B1593749 : Blo 1060614 1593749 := bbase (se 6 (by rfl) ⟨37353, by rfl⟩ : syracuseStep 1593749 = 74707) (by norm_num)
theorem B1593773 : Blo 1060614 1593773 := bbase (se 3 (by rfl) ⟨298832, by rfl⟩ : syracuseStep 1593773 = 597665) (by norm_num)
theorem B1593797 : Blo 1060614 1593797 := bbase (se 4 (by rfl) ⟨149418, by rfl⟩ : syracuseStep 1593797 = 298837) (by norm_num)
theorem B1593821 : Blo 1060614 1593821 := bbase (se 3 (by rfl) ⟨298841, by rfl⟩ : syracuseStep 1593821 = 597683) (by norm_num)
theorem B1790437 : Blo 1060614 1790437 := bbase (se 4 (by rfl) ⟨167853, by rfl⟩ : syracuseStep 1790437 = 335707) (by norm_num)
theorem B2183653 : Blo 1060614 2183653 := bbase (se 4 (by rfl) ⟨204717, by rfl⟩ : syracuseStep 2183653 = 409435) (by norm_num)
theorem B1593845 : Blo 1060614 1593845 := bbase (se 5 (by rfl) ⟨74711, by rfl⟩ : syracuseStep 1593845 = 149423) (by norm_num)
theorem B1593869 : Blo 1060614 1593869 := bbase (se 3 (by rfl) ⟨298850, by rfl⟩ : syracuseStep 1593869 = 597701) (by norm_num)
theorem B1593893 : Blo 1060614 1593893 := bbase (se 4 (by rfl) ⟨149427, by rfl⟩ : syracuseStep 1593893 = 298855) (by norm_num)
theorem B1790525 : Blo 1060614 1790525 := bbase (se 3 (by rfl) ⟨335723, by rfl⟩ : syracuseStep 1790525 = 671447) (by norm_num)
theorem B1593917 : Blo 1060614 1593917 := bbase (se 3 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 1593917 = 597719) (by norm_num)
theorem B1364557 : Blo 1060614 1364557 := bbase (se 3 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 1364557 = 511709) (by norm_num)
theorem B1593941 : Blo 1060614 1593941 := bbase (se 8 (by rfl) ⟨9339, by rfl⟩ : syracuseStep 1593941 = 18679) (by norm_num)
theorem B1593965 : Blo 1060614 1593965 := bbase (se 3 (by rfl) ⟨298868, by rfl⟩ : syracuseStep 1593965 = 597737) (by norm_num)
theorem B1593989 : Blo 1060614 1593989 := bbase (se 4 (by rfl) ⟨149436, by rfl⟩ : syracuseStep 1593989 = 298873) (by norm_num)
theorem B1594013 : Blo 1060614 1594013 := bbase (se 3 (by rfl) ⟨298877, by rfl⟩ : syracuseStep 1594013 = 597755) (by norm_num)
theorem B1594037 : Blo 1060614 1594037 := bbase (se 5 (by rfl) ⟨74720, by rfl⟩ : syracuseStep 1594037 = 149441) (by norm_num)
theorem B1790653 : Blo 1060614 1790653 := bbase (se 3 (by rfl) ⟨335747, by rfl⟩ : syracuseStep 1790653 = 671495) (by norm_num)
theorem B1135301 : Blo 1060614 1135301 := bbase (se 4 (by rfl) ⟨106434, by rfl⟩ : syracuseStep 1135301 = 212869) (by norm_num)
theorem B1594061 : Blo 1060614 1594061 := bbase (se 3 (by rfl) ⟨298886, by rfl⟩ : syracuseStep 1594061 = 597773) (by norm_num)
theorem B5100245 : Blo 1060614 5100245 := bbase (se 7 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 5100245 = 119537) (by norm_num)
theorem B1594085 : Blo 1060614 1594085 := bbase (se 4 (by rfl) ⟨149445, by rfl⟩ : syracuseStep 1594085 = 298891) (by norm_num)
theorem B1594109 : Blo 1060614 1594109 := bbase (se 3 (by rfl) ⟨298895, by rfl⟩ : syracuseStep 1594109 = 597791) (by norm_num)
theorem B1790741 : Blo 1060614 1790741 := bbase (se 6 (by rfl) ⟨41970, by rfl⟩ : syracuseStep 1790741 = 83941) (by norm_num)
theorem B1594133 : Blo 1060614 1594133 := bbase (se 6 (by rfl) ⟨37362, by rfl⟩ : syracuseStep 1594133 = 74725) (by norm_num)
theorem B3592997 : Blo 1060614 3592997 := bbase (se 4 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 3592997 = 673687) (by norm_num)
theorem B1594157 : Blo 1060614 1594157 := bbase (se 3 (by rfl) ⟨298904, by rfl⟩ : syracuseStep 1594157 = 597809) (by norm_num)
theorem B1594181 : Blo 1060614 1594181 := bbase (se 4 (by rfl) ⟨149454, by rfl⟩ : syracuseStep 1594181 = 298909) (by norm_num)
theorem B7656277 : Blo 1060614 7656277 := bbase (se 9 (by rfl) ⟨22430, by rfl⟩ : syracuseStep 7656277 = 44861) (by norm_num)
theorem B1594205 : Blo 1060614 1594205 := bbase (se 3 (by rfl) ⟨298913, by rfl⟩ : syracuseStep 1594205 = 597827) (by norm_num)
theorem B1594229 : Blo 1060614 1594229 := bbase (se 5 (by rfl) ⟨74729, by rfl⟩ : syracuseStep 1594229 = 149459) (by norm_num)
theorem B1594253 : Blo 1060614 1594253 := bbase (se 3 (by rfl) ⟨298922, by rfl⟩ : syracuseStep 1594253 = 597845) (by norm_num)
theorem B1790869 : Blo 1060614 1790869 := bbase (se 6 (by rfl) ⟨41973, by rfl⟩ : syracuseStep 1790869 = 83947) (by norm_num)
theorem B1594277 : Blo 1060614 1594277 := bbase (se 4 (by rfl) ⟨149463, by rfl⟩ : syracuseStep 1594277 = 298927) (by norm_num)
theorem B1594301 : Blo 1060614 1594301 := bbase (se 3 (by rfl) ⟨298931, by rfl⟩ : syracuseStep 1594301 = 597863) (by norm_num)
theorem B1135549 : Blo 1060614 1135549 := bbase (se 3 (by rfl) ⟨212915, by rfl⟩ : syracuseStep 1135549 = 425831) (by norm_num)
theorem B1594325 : Blo 1060614 1594325 := bbase (se 7 (by rfl) ⟨18683, by rfl⟩ : syracuseStep 1594325 = 37367) (by norm_num)
theorem B1790957 : Blo 1060614 1790957 := bbase (se 3 (by rfl) ⟨335804, by rfl⟩ : syracuseStep 1790957 = 671609) (by norm_num)
theorem B1594349 : Blo 1060614 1594349 := bbase (se 3 (by rfl) ⟨298940, by rfl⟩ : syracuseStep 1594349 = 597881) (by norm_num)
theorem B1594373 : Blo 1060614 1594373 := bbase (se 4 (by rfl) ⟨149472, by rfl⟩ : syracuseStep 1594373 = 298945) (by norm_num)
theorem B1594397 : Blo 1060614 1594397 := bbase (se 3 (by rfl) ⟨298949, by rfl⟩ : syracuseStep 1594397 = 597899) (by norm_num)
theorem B1594421 : Blo 1060614 1594421 := bbase (se 5 (by rfl) ⟨74738, by rfl⟩ : syracuseStep 1594421 = 149477) (by norm_num)
theorem B1594445 : Blo 1060614 1594445 := bbase (se 3 (by rfl) ⟨298958, by rfl⟩ : syracuseStep 1594445 = 597917) (by norm_num)
theorem B1594469 : Blo 1060614 1594469 := bbase (se 4 (by rfl) ⟨149481, by rfl⟩ : syracuseStep 1594469 = 298963) (by norm_num)
theorem B1791085 : Blo 1060614 1791085 := bbase (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) (by norm_num)
theorem B1594493 : Blo 1060614 1594493 := bbase (se 3 (by rfl) ⟨298967, by rfl⟩ : syracuseStep 1594493 = 597935) (by norm_num)
theorem B2020477 : Blo 1060614 2020477 := bbase (se 3 (by rfl) ⟨378839, by rfl⟩ : syracuseStep 2020477 = 757679) (by norm_num)
theorem B1594517 : Blo 1060614 1594517 := bbase (se 6 (by rfl) ⟨37371, by rfl⟩ : syracuseStep 1594517 = 74743) (by norm_num)
theorem B1594541 : Blo 1060614 1594541 := bbase (se 3 (by rfl) ⟨298976, by rfl⟩ : syracuseStep 1594541 = 597953) (by norm_num)
theorem B1791173 : Blo 1060614 1791173 := bbase (se 4 (by rfl) ⟨167922, by rfl⟩ : syracuseStep 1791173 = 335845) (by norm_num)
theorem B1594565 : Blo 1060614 1594565 := bbase (se 4 (by rfl) ⟨149490, by rfl⟩ : syracuseStep 1594565 = 298981) (by norm_num)
theorem B1594589 : Blo 1060614 1594589 := bbase (se 3 (by rfl) ⟨298985, by rfl⟩ : syracuseStep 1594589 = 597971) (by norm_num)
theorem B1594613 : Blo 1060614 1594613 := bbase (se 5 (by rfl) ⟨74747, by rfl⟩ : syracuseStep 1594613 = 149495) (by norm_num)
theorem B1365241 : Blo 1060614 1365241 := bbase (se 2 (by rfl) ⟨511965, by rfl⟩ : syracuseStep 1365241 = 1023931) (by norm_num)
theorem B1594637 : Blo 1060614 1594637 := bbase (se 3 (by rfl) ⟨298994, by rfl⟩ : syracuseStep 1594637 = 597989) (by norm_num)
theorem B2020621 : Blo 1060614 2020621 := bbase (se 3 (by rfl) ⟨378866, by rfl⟩ : syracuseStep 2020621 = 757733) (by norm_num)
theorem B1594661 : Blo 1060614 1594661 := bbase (se 4 (by rfl) ⟨149499, by rfl⟩ : syracuseStep 1594661 = 298999) (by norm_num)
theorem B1594685 : Blo 1060614 1594685 := bbase (se 3 (by rfl) ⟨299003, by rfl⟩ : syracuseStep 1594685 = 598007) (by norm_num)
theorem B1791301 : Blo 1060614 1791301 := bbase (se 4 (by rfl) ⟨167934, by rfl⟩ : syracuseStep 1791301 = 335869) (by norm_num)
theorem B1594709 : Blo 1060614 1594709 := bbase (se 16 (by rfl) ⟨36, by rfl⟩ : syracuseStep 1594709 = 73) (by norm_num)
theorem B4150613 : Blo 1060614 4150613 := bbase (se 17 (by rfl) ⟨47, by rfl⟩ : syracuseStep 4150613 = 95) (by norm_num)
theorem B1594733 : Blo 1060614 1594733 := bbase (se 3 (by rfl) ⟨299012, by rfl⟩ : syracuseStep 1594733 = 598025) (by norm_num)
theorem B2872693 : Blo 1060614 2872693 := bbase (se 5 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 2872693 = 269315) (by norm_num)
theorem B1135993 : Blo 1060614 1135993 := bbase (se 2 (by rfl) ⟨425997, by rfl⟩ : syracuseStep 1135993 = 851995) (by norm_num)
theorem B1594757 : Blo 1060614 1594757 := bbase (se 4 (by rfl) ⟨149508, by rfl⟩ : syracuseStep 1594757 = 299017) (by norm_num)
theorem B1791389 : Blo 1060614 1791389 := bbase (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) (by norm_num)
theorem B1594781 : Blo 1060614 1594781 := bbase (se 3 (by rfl) ⟨299021, by rfl⟩ : syracuseStep 1594781 = 598043) (by norm_num)
theorem B2020781 : Blo 1060614 2020781 := bbase (se 3 (by rfl) ⟨378896, by rfl⟩ : syracuseStep 2020781 = 757793) (by norm_num)
theorem B1594805 : Blo 1060614 1594805 := bbase (se 5 (by rfl) ⟨74756, by rfl⟩ : syracuseStep 1594805 = 149513) (by norm_num)
theorem B1136053 : Blo 1060614 1136053 := bbase (se 5 (by rfl) ⟨53252, by rfl⟩ : syracuseStep 1136053 = 106505) (by norm_num)
theorem B1594829 : Blo 1060614 1594829 := bbase (se 3 (by rfl) ⟨299030, by rfl⟩ : syracuseStep 1594829 = 598061) (by norm_num)
theorem B1594853 : Blo 1060614 1594853 := bbase (se 4 (by rfl) ⟨149517, by rfl⟩ : syracuseStep 1594853 = 299035) (by norm_num)
theorem B1594877 : Blo 1060614 1594877 := bbase (se 3 (by rfl) ⟨299039, by rfl⟩ : syracuseStep 1594877 = 598079) (by norm_num)
theorem B3823109 : Blo 1060614 3823109 := bbase (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) (by norm_num)
theorem B9066005 : Blo 1060614 9066005 := bbase (se 6 (by rfl) ⟨212484, by rfl⟩ : syracuseStep 9066005 = 424969) (by norm_num)
theorem B1594901 : Blo 1060614 1594901 := bbase (se 6 (by rfl) ⟨37380, by rfl⟩ : syracuseStep 1594901 = 74761) (by norm_num)
theorem B1791517 : Blo 1060614 1791517 := bbase (se 3 (by rfl) ⟨335909, by rfl⟩ : syracuseStep 1791517 = 671819) (by norm_num)
theorem B2151973 : Blo 1060614 2151973 := bbase (se 4 (by rfl) ⟨201747, by rfl⟩ : syracuseStep 2151973 = 403495) (by norm_num)
theorem B1594925 : Blo 1060614 1594925 := bbase (se 3 (by rfl) ⟨299048, by rfl⟩ : syracuseStep 1594925 = 598097) (by norm_num)
theorem B2020925 : Blo 1060614 2020925 := bbase (se 3 (by rfl) ⟨378923, by rfl⟩ : syracuseStep 2020925 = 757847) (by norm_num)
theorem B1594949 : Blo 1060614 1594949 := bbase (se 4 (by rfl) ⟨149526, by rfl⟩ : syracuseStep 1594949 = 299053) (by norm_num)
theorem B1594973 : Blo 1060614 1594973 := bbase (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) (by norm_num)
theorem B1791605 : Blo 1060614 1791605 := bbase (se 5 (by rfl) ⟨83981, by rfl⟩ : syracuseStep 1791605 = 167963) (by norm_num)
theorem B1594997 : Blo 1060614 1594997 := bbase (se 5 (by rfl) ⟨74765, by rfl⟩ : syracuseStep 1594997 = 149531) (by norm_num)
theorem B1595021 : Blo 1060614 1595021 := bbase (se 3 (by rfl) ⟨299066, by rfl⟩ : syracuseStep 1595021 = 598133) (by norm_num)
theorem B1595045 : Blo 1060614 1595045 := bbase (se 4 (by rfl) ⟨149535, by rfl⟩ : syracuseStep 1595045 = 299071) (by norm_num)
theorem B1595069 : Blo 1060614 1595069 := bbase (se 3 (by rfl) ⟨299075, by rfl⟩ : syracuseStep 1595069 = 598151) (by norm_num)
theorem B1595093 : Blo 1060614 1595093 := bbase (se 7 (by rfl) ⟨18692, by rfl⟩ : syracuseStep 1595093 = 37385) (by norm_num)
theorem B1595117 : Blo 1060614 1595117 := bbase (se 3 (by rfl) ⟨299084, by rfl⟩ : syracuseStep 1595117 = 598169) (by norm_num)
theorem B1136369 : Blo 1060614 1136369 := bbase (se 2 (by rfl) ⟨426138, by rfl⟩ : syracuseStep 1136369 = 852277) (by norm_num)
theorem B1791733 : Blo 1060614 1791733 := bbase (se 5 (by rfl) ⟨83987, by rfl⟩ : syracuseStep 1791733 = 167975) (by norm_num)
theorem B1595141 : Blo 1060614 1595141 := bbase (se 4 (by rfl) ⟨149544, by rfl⟩ : syracuseStep 1595141 = 299089) (by norm_num)
theorem B1595165 : Blo 1060614 1595165 := bbase (se 3 (by rfl) ⟨299093, by rfl⟩ : syracuseStep 1595165 = 598187) (by norm_num)
theorem B1595189 : Blo 1060614 1595189 := bbase (se 5 (by rfl) ⟨74774, by rfl⟩ : syracuseStep 1595189 = 149549) (by norm_num)
theorem B1791821 : Blo 1060614 1791821 := bbase (se 3 (by rfl) ⟨335966, by rfl⟩ : syracuseStep 1791821 = 671933) (by norm_num)
theorem B1595213 : Blo 1060614 1595213 := bbase (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) (by norm_num)
theorem B1595237 : Blo 1060614 1595237 := bbase (se 4 (by rfl) ⟨149553, by rfl⟩ : syracuseStep 1595237 = 299107) (by norm_num)
theorem B1595261 : Blo 1060614 1595261 := bbase (se 3 (by rfl) ⟨299111, by rfl⟩ : syracuseStep 1595261 = 598223) (by norm_num)
theorem B6805397 : Blo 1060614 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B1595285 : Blo 1060614 1595285 := bbase (se 6 (by rfl) ⟨37389, by rfl⟩ : syracuseStep 1595285 = 74779) (by norm_num)
theorem B1595309 : Blo 1060614 1595309 := bbase (se 3 (by rfl) ⟨299120, by rfl⟩ : syracuseStep 1595309 = 598241) (by norm_num)
theorem B1595333 : Blo 1060614 1595333 := bbase (se 4 (by rfl) ⟨149562, by rfl⟩ : syracuseStep 1595333 = 299125) (by norm_num)
theorem B1791949 : Blo 1060614 1791949 := bbase (se 3 (by rfl) ⟨335990, by rfl⟩ : syracuseStep 1791949 = 671981) (by norm_num)
theorem B1595357 : Blo 1060614 1595357 := bbase (se 3 (by rfl) ⟨299129, by rfl⟩ : syracuseStep 1595357 = 598259) (by norm_num)
theorem B1595381 : Blo 1060614 1595381 := bbase (se 5 (by rfl) ⟨74783, by rfl⟩ : syracuseStep 1595381 = 149567) (by norm_num)
theorem B1595405 : Blo 1060614 1595405 := bbase (se 3 (by rfl) ⟨299138, by rfl⟩ : syracuseStep 1595405 = 598277) (by norm_num)
theorem B1792037 : Blo 1060614 1792037 := bbase (se 4 (by rfl) ⟨168003, by rfl⟩ : syracuseStep 1792037 = 336007) (by norm_num)
theorem B1595429 : Blo 1060614 1595429 := bbase (se 4 (by rfl) ⟨149571, by rfl⟩ : syracuseStep 1595429 = 299143) (by norm_num)
theorem B1595453 : Blo 1060614 1595453 := bbase (se 3 (by rfl) ⟨299147, by rfl⟩ : syracuseStep 1595453 = 598295) (by norm_num)
theorem B1595477 : Blo 1060614 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B1595501 : Blo 1060614 1595501 := bbase (se 3 (by rfl) ⟨299156, by rfl⟩ : syracuseStep 1595501 = 598313) (by norm_num)
theorem B1595525 : Blo 1060614 1595525 := bbase (se 4 (by rfl) ⟨149580, by rfl⟩ : syracuseStep 1595525 = 299161) (by norm_num)
theorem B1595549 : Blo 1060614 1595549 := bbase (se 3 (by rfl) ⟨299165, by rfl⟩ : syracuseStep 1595549 = 598331) (by norm_num)
theorem B1792165 : Blo 1060614 1792165 := bbase (se 4 (by rfl) ⟨168015, by rfl⟩ : syracuseStep 1792165 = 336031) (by norm_num)
theorem B1136813 : Blo 1060614 1136813 := bbase (se 3 (by rfl) ⟨213152, by rfl⟩ : syracuseStep 1136813 = 426305) (by norm_num)
theorem B1595573 : Blo 1060614 1595573 := bbase (se 5 (by rfl) ⟨74792, by rfl⟩ : syracuseStep 1595573 = 149585) (by norm_num)
theorem B8083637 : Blo 1060614 8083637 := bbase (se 5 (by rfl) ⟨378920, by rfl⟩ : syracuseStep 8083637 = 757841) (by norm_num)
theorem B1595597 : Blo 1060614 1595597 := bbase (se 3 (by rfl) ⟨299174, by rfl⟩ : syracuseStep 1595597 = 598349) (by norm_num)
theorem B1595621 : Blo 1060614 1595621 := bbase (se 4 (by rfl) ⟨149589, by rfl⟩ : syracuseStep 1595621 = 299179) (by norm_num)
theorem B1792253 : Blo 1060614 1792253 := bbase (se 3 (by rfl) ⟨336047, by rfl⟩ : syracuseStep 1792253 = 672095) (by norm_num)
theorem B1595645 : Blo 1060614 1595645 := bbase (se 3 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 1595645 = 598367) (by norm_num)
theorem B1595669 : Blo 1060614 1595669 := bbase (se 6 (by rfl) ⟨37398, by rfl⟩ : syracuseStep 1595669 = 74797) (by norm_num)
theorem B1595693 : Blo 1060614 1595693 := bbase (se 3 (by rfl) ⟨299192, by rfl⟩ : syracuseStep 1595693 = 598385) (by norm_num)
theorem B1595717 : Blo 1060614 1595717 := bbase (se 4 (by rfl) ⟨149598, by rfl⟩ : syracuseStep 1595717 = 299197) (by norm_num)
theorem B1595741 : Blo 1060614 1595741 := bbase (se 3 (by rfl) ⟨299201, by rfl⟩ : syracuseStep 1595741 = 598403) (by norm_num)
theorem B1595765 : Blo 1060614 1595765 := bbase (se 5 (by rfl) ⟨74801, by rfl⟩ : syracuseStep 1595765 = 149603) (by norm_num)
theorem B1792381 : Blo 1060614 1792381 := bbase (se 3 (by rfl) ⟨336071, by rfl⟩ : syracuseStep 1792381 = 672143) (by norm_num)
theorem B1595789 : Blo 1060614 1595789 := bbase (se 3 (by rfl) ⟨299210, by rfl⟩ : syracuseStep 1595789 = 598421) (by norm_num)
theorem B1595813 : Blo 1060614 1595813 := bbase (se 4 (by rfl) ⟨149607, by rfl⟩ : syracuseStep 1595813 = 299215) (by norm_num)
theorem B1595837 : Blo 1060614 1595837 := bbase (se 3 (by rfl) ⟨299219, by rfl⟩ : syracuseStep 1595837 = 598439) (by norm_num)
theorem B1792469 : Blo 1060614 1792469 := bbase (se 7 (by rfl) ⟨21005, by rfl⟩ : syracuseStep 1792469 = 42011) (by norm_num)
theorem B1595861 : Blo 1060614 1595861 := bbase (se 7 (by rfl) ⟨18701, by rfl⟩ : syracuseStep 1595861 = 37403) (by norm_num)
theorem B4544981 : Blo 1060614 4544981 := bbase (se 7 (by rfl) ⟨53261, by rfl⟩ : syracuseStep 4544981 = 106523) (by norm_num)
theorem B1595885 : Blo 1060614 1595885 := bbase (se 3 (by rfl) ⟨299228, by rfl⟩ : syracuseStep 1595885 = 598457) (by norm_num)
theorem B3824117 : Blo 1060614 3824117 := bbase (se 5 (by rfl) ⟨179255, by rfl⟩ : syracuseStep 3824117 = 358511) (by norm_num)
theorem B1595909 : Blo 1060614 1595909 := bbase (se 4 (by rfl) ⟨149616, by rfl⟩ : syracuseStep 1595909 = 299233) (by norm_num)
theorem B1595933 : Blo 1060614 1595933 := bbase (se 3 (by rfl) ⟨299237, by rfl⟩ : syracuseStep 1595933 = 598475) (by norm_num)
theorem B1595957 : Blo 1060614 1595957 := bbase (se 5 (by rfl) ⟨74810, by rfl⟩ : syracuseStep 1595957 = 149621) (by norm_num)
theorem B1595981 : Blo 1060614 1595981 := bbase (se 3 (by rfl) ⟨299246, by rfl⟩ : syracuseStep 1595981 = 598493) (by norm_num)
theorem B1792597 : Blo 1060614 1792597 := bbase (se 8 (by rfl) ⟨10503, by rfl⟩ : syracuseStep 1792597 = 21007) (by norm_num)
theorem B1596005 : Blo 1060614 1596005 := bbase (se 4 (by rfl) ⟨149625, by rfl⟩ : syracuseStep 1596005 = 299251) (by norm_num)
theorem B1596029 : Blo 1060614 1596029 := bbase (se 3 (by rfl) ⟨299255, by rfl⟩ : syracuseStep 1596029 = 598511) (by norm_num)
theorem B1596053 : Blo 1060614 1596053 := bbase (se 6 (by rfl) ⟨37407, by rfl⟩ : syracuseStep 1596053 = 74815) (by norm_num)
theorem B1792685 : Blo 1060614 1792685 := bbase (se 3 (by rfl) ⟨336128, by rfl⟩ : syracuseStep 1792685 = 672257) (by norm_num)
theorem B1596077 : Blo 1060614 1596077 := bbase (se 3 (by rfl) ⟨299264, by rfl⟩ : syracuseStep 1596077 = 598529) (by norm_num)
theorem B1596101 : Blo 1060614 1596101 := bbase (se 4 (by rfl) ⟨149634, by rfl⟩ : syracuseStep 1596101 = 299269) (by norm_num)
theorem B1596125 : Blo 1060614 1596125 := bbase (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) (by norm_num)
theorem B1596149 : Blo 1060614 1596149 := bbase (se 5 (by rfl) ⟨74819, by rfl⟩ : syracuseStep 1596149 = 149639) (by norm_num)
theorem B1596173 : Blo 1060614 1596173 := bbase (se 3 (by rfl) ⟨299282, by rfl⟩ : syracuseStep 1596173 = 598565) (by norm_num)
theorem B1596197 : Blo 1060614 1596197 := bbase (se 4 (by rfl) ⟨149643, by rfl⟩ : syracuseStep 1596197 = 299287) (by norm_num)
theorem B1792813 : Blo 1060614 1792813 := bbase (se 3 (by rfl) ⟨336152, by rfl⟩ : syracuseStep 1792813 = 672305) (by norm_num)
theorem B1596221 : Blo 1060614 1596221 := bbase (se 3 (by rfl) ⟨299291, by rfl⟩ : syracuseStep 1596221 = 598583) (by norm_num)
theorem B1596245 : Blo 1060614 1596245 := bbase (se 9 (by rfl) ⟨4676, by rfl⟩ : syracuseStep 1596245 = 9353) (by norm_num)
theorem B1596269 : Blo 1060614 1596269 := bbase (se 3 (by rfl) ⟨299300, by rfl⟩ : syracuseStep 1596269 = 598601) (by norm_num)
theorem B1792901 : Blo 1060614 1792901 := bbase (se 4 (by rfl) ⟨168084, by rfl⟩ : syracuseStep 1792901 = 336169) (by norm_num)
theorem B1596293 : Blo 1060614 1596293 := bbase (se 4 (by rfl) ⟨149652, by rfl⟩ : syracuseStep 1596293 = 299305) (by norm_num)
theorem B1596317 : Blo 1060614 1596317 := bbase (se 3 (by rfl) ⟨299309, by rfl⟩ : syracuseStep 1596317 = 598619) (by norm_num)
theorem B1596341 : Blo 1060614 1596341 := bbase (se 5 (by rfl) ⟨74828, by rfl⟩ : syracuseStep 1596341 = 149657) (by norm_num)
theorem B1596365 : Blo 1060614 1596365 := bbase (se 3 (by rfl) ⟨299318, by rfl⟩ : syracuseStep 1596365 = 598637) (by norm_num)
theorem B1596389 : Blo 1060614 1596389 := bbase (se 4 (by rfl) ⟨149661, by rfl⟩ : syracuseStep 1596389 = 299323) (by norm_num)
theorem B1596413 : Blo 1060614 1596413 := bbase (se 3 (by rfl) ⟨299327, by rfl⟩ : syracuseStep 1596413 = 598655) (by norm_num)
theorem B1793029 : Blo 1060614 1793029 := bbase (se 4 (by rfl) ⟨168096, by rfl⟩ : syracuseStep 1793029 = 336193) (by norm_num)
theorem B1596437 : Blo 1060614 1596437 := bbase (se 6 (by rfl) ⟨37416, by rfl⟩ : syracuseStep 1596437 = 74833) (by norm_num)
theorem B1727525 : Blo 1060614 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B1596461 : Blo 1060614 1596461 := bbase (se 3 (by rfl) ⟨299336, by rfl⟩ : syracuseStep 1596461 = 598673) (by norm_num)
theorem B1596485 : Blo 1060614 1596485 := bbase (se 4 (by rfl) ⟨149670, by rfl⟩ : syracuseStep 1596485 = 299341) (by norm_num)
theorem B1793117 : Blo 1060614 1793117 := bbase (se 3 (by rfl) ⟨336209, by rfl⟩ : syracuseStep 1793117 = 672419) (by norm_num)
theorem B1596509 : Blo 1060614 1596509 := bbase (se 3 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 1596509 = 598691) (by norm_num)
theorem B1596533 : Blo 1060614 1596533 := bbase (se 5 (by rfl) ⟨74837, by rfl⟩ : syracuseStep 1596533 = 149675) (by norm_num)
theorem B1596557 : Blo 1060614 1596557 := bbase (se 3 (by rfl) ⟨299354, by rfl⟩ : syracuseStep 1596557 = 598709) (by norm_num)
theorem B1596581 : Blo 1060614 1596581 := bbase (se 4 (by rfl) ⟨149679, by rfl⟩ : syracuseStep 1596581 = 299359) (by norm_num)
theorem B1596605 : Blo 1060614 1596605 := bbase (se 3 (by rfl) ⟨299363, by rfl⟩ : syracuseStep 1596605 = 598727) (by norm_num)
theorem B1596629 : Blo 1060614 1596629 := bbase (se 7 (by rfl) ⟨18710, by rfl⟩ : syracuseStep 1596629 = 37421) (by norm_num)
theorem B1793245 : Blo 1060614 1793245 := bbase (se 3 (by rfl) ⟨336233, by rfl⟩ : syracuseStep 1793245 = 672467) (by norm_num)
theorem B1596653 : Blo 1060614 1596653 := bbase (se 3 (by rfl) ⟨299372, by rfl⟩ : syracuseStep 1596653 = 598745) (by norm_num)
theorem B1596677 : Blo 1060614 1596677 := bbase (se 4 (by rfl) ⟨149688, by rfl⟩ : syracuseStep 1596677 = 299377) (by norm_num)
theorem B1596701 : Blo 1060614 1596701 := bbase (se 3 (by rfl) ⟨299381, by rfl⟩ : syracuseStep 1596701 = 598763) (by norm_num)
theorem B1793333 : Blo 1060614 1793333 := bbase (se 5 (by rfl) ⟨84062, by rfl⟩ : syracuseStep 1793333 = 168125) (by norm_num)
theorem B1596725 : Blo 1060614 1596725 := bbase (se 5 (by rfl) ⟨74846, by rfl⟩ : syracuseStep 1596725 = 149693) (by norm_num)
theorem B1596749 : Blo 1060614 1596749 := bbase (se 3 (by rfl) ⟨299390, by rfl⟩ : syracuseStep 1596749 = 598781) (by norm_num)
theorem B1596773 : Blo 1060614 1596773 := bbase (se 4 (by rfl) ⟨149697, by rfl⟩ : syracuseStep 1596773 = 299395) (by norm_num)
theorem B1596797 : Blo 1060614 1596797 := bbase (se 3 (by rfl) ⟨299399, by rfl⟩ : syracuseStep 1596797 = 598799) (by norm_num)
theorem B1596821 : Blo 1060614 1596821 := bbase (se 6 (by rfl) ⟨37425, by rfl⟩ : syracuseStep 1596821 = 74851) (by norm_num)
theorem B1596845 : Blo 1060614 1596845 := bbase (se 3 (by rfl) ⟨299408, by rfl⟩ : syracuseStep 1596845 = 598817) (by norm_num)
theorem B1793461 : Blo 1060614 1793461 := bbase (se 5 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 1793461 = 168137) (by norm_num)
theorem B4545989 : Blo 1060614 4545989 := bbase (se 4 (by rfl) ⟨426186, by rfl⟩ : syracuseStep 4545989 = 852373) (by norm_num)
theorem B1596869 : Blo 1060614 1596869 := bbase (se 4 (by rfl) ⟨149706, by rfl⟩ : syracuseStep 1596869 = 299413) (by norm_num)
theorem B1596893 : Blo 1060614 1596893 := bbase (se 3 (by rfl) ⟨299417, by rfl⟩ : syracuseStep 1596893 = 598835) (by norm_num)
theorem B1596917 : Blo 1060614 1596917 := bbase (se 5 (by rfl) ⟨74855, by rfl⟩ : syracuseStep 1596917 = 149711) (by norm_num)
theorem B1793549 : Blo 1060614 1793549 := bbase (se 3 (by rfl) ⟨336290, by rfl⟩ : syracuseStep 1793549 = 672581) (by norm_num)
theorem B1793677 : Blo 1060614 1793677 := bbase (se 3 (by rfl) ⟨336314, by rfl⟩ : syracuseStep 1793677 = 672629) (by norm_num)
theorem B3399317 : Blo 1060614 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B6053525 : Blo 1060614 6053525 := bbase (se 6 (by rfl) ⟨141879, by rfl⟩ : syracuseStep 6053525 = 283759) (by norm_num)
theorem B3628709 : Blo 1060614 3628709 := bbase (se 4 (by rfl) ⟨340191, by rfl⟩ : syracuseStep 3628709 = 680383) (by norm_num)
theorem B1793765 : Blo 1060614 1793765 := bbase (se 4 (by rfl) ⟨168165, by rfl⟩ : syracuseStep 1793765 = 336331) (by norm_num)
theorem B3399509 : Blo 1060614 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B1793893 : Blo 1060614 1793893 := bbase (se 4 (by rfl) ⟨168177, by rfl⟩ : syracuseStep 1793893 = 336355) (by norm_num)
theorem B1793981 : Blo 1060614 1793981 := bbase (se 3 (by rfl) ⟨336371, by rfl⟩ : syracuseStep 1793981 = 672743) (by norm_num)
theorem B1794109 : Blo 1060614 1794109 := bbase (se 3 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 1794109 = 672791) (by norm_num)
theorem B1794197 : Blo 1060614 1794197 := bbase (se 6 (by rfl) ⟨42051, by rfl⟩ : syracuseStep 1794197 = 84103) (by norm_num)
theorem B1794325 : Blo 1060614 1794325 := bbase (se 6 (by rfl) ⟨42054, by rfl⟩ : syracuseStep 1794325 = 84109) (by norm_num)
theorem B1433909 : Blo 1060614 1433909 := bbase (se 5 (by rfl) ⟨67214, by rfl⟩ : syracuseStep 1433909 = 134429) (by norm_num)
theorem B1794413 : Blo 1060614 1794413 := bbase (se 3 (by rfl) ⟨336452, by rfl⟩ : syracuseStep 1794413 = 672905) (by norm_num)
theorem B1794541 : Blo 1060614 1794541 := bbase (se 3 (by rfl) ⟨336476, by rfl⟩ : syracuseStep 1794541 = 672953) (by norm_num)
theorem B1794629 : Blo 1060614 1794629 := bbase (se 4 (by rfl) ⟨168246, by rfl⟩ : syracuseStep 1794629 = 336493) (by norm_num)
theorem B1794757 : Blo 1060614 1794757 := bbase (se 4 (by rfl) ⟨168258, by rfl⟩ : syracuseStep 1794757 = 336517) (by norm_num)
theorem B3826453 : Blo 1060614 3826453 := bbase (se 6 (by rfl) ⟨89682, by rfl⟩ : syracuseStep 3826453 = 179365) (by norm_num)
theorem B1794845 : Blo 1060614 1794845 := bbase (se 3 (by rfl) ⟨336533, by rfl⟩ : syracuseStep 1794845 = 673067) (by norm_num)
theorem B6808373 : Blo 1060614 6808373 := bbase (se 5 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 6808373 = 638285) (by norm_num)
theorem B6054709 : Blo 1060614 6054709 := bbase (se 5 (by rfl) ⟨283814, by rfl⟩ : syracuseStep 6054709 = 567629) (by norm_num)
theorem B2155405 : Blo 1060614 2155405 := bbase (se 3 (by rfl) ⟨404138, by rfl⟩ : syracuseStep 2155405 = 808277) (by norm_num)
theorem B1794973 : Blo 1060614 1794973 := bbase (se 3 (by rfl) ⟨336557, by rfl⟩ : syracuseStep 1794973 = 673115) (by norm_num)
theorem B5104549 : Blo 1060614 5104549 := bbase (se 4 (by rfl) ⟨478551, by rfl⟩ : syracuseStep 5104549 = 957103) (by norm_num)
theorem B2155477 : Blo 1060614 2155477 := bbase (se 7 (by rfl) ⟨25259, by rfl⟩ : syracuseStep 2155477 = 50519) (by norm_num)
theorem B1795061 : Blo 1060614 1795061 := bbase (se 5 (by rfl) ⟨84143, by rfl⟩ : syracuseStep 1795061 = 168287) (by norm_num)
theorem B1795189 : Blo 1060614 1795189 := bbase (se 5 (by rfl) ⟨84149, by rfl⟩ : syracuseStep 1795189 = 168299) (by norm_num)
theorem B1795277 : Blo 1060614 1795277 := bbase (se 3 (by rfl) ⟨336614, by rfl⟩ : syracuseStep 1795277 = 673229) (by norm_num)
theorem B1795405 : Blo 1060614 1795405 := bbase (se 3 (by rfl) ⟨336638, by rfl⟩ : syracuseStep 1795405 = 673277) (by norm_num)
theorem B1795493 : Blo 1060614 1795493 := bbase (se 4 (by rfl) ⟨168327, by rfl⟩ : syracuseStep 1795493 = 336655) (by norm_num)
theorem B1795621 : Blo 1060614 1795621 := bbase (se 4 (by rfl) ⟨168339, by rfl⟩ : syracuseStep 1795621 = 336679) (by norm_num)
theorem B1795709 : Blo 1060614 1795709 := bbase (se 3 (by rfl) ⟨336695, by rfl⟩ : syracuseStep 1795709 = 673391) (by norm_num)
theorem B21849749 : Blo 1060614 21849749 := bbase (se 6 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 21849749 = 1024207) (by norm_num)
theorem B1795837 : Blo 1060614 1795837 := bbase (se 3 (by rfl) ⟨336719, by rfl⟩ : syracuseStep 1795837 = 673439) (by norm_num)
theorem B1795925 : Blo 1060614 1795925 := bbase (se 9 (by rfl) ⟨5261, by rfl⟩ : syracuseStep 1795925 = 10523) (by norm_num)
theorem B1796053 : Blo 1060614 1796053 := bbase (se 7 (by rfl) ⟨21047, by rfl⟩ : syracuseStep 1796053 = 42095) (by norm_num)
theorem B1075241 : Blo 1060614 1075241 := bbase (se 2 (by rfl) ⟨403215, by rfl⟩ : syracuseStep 1075241 = 806431) (by norm_num)
theorem B1796141 : Blo 1060614 1796141 := bbase (se 3 (by rfl) ⟨336776, by rfl⟩ : syracuseStep 1796141 = 673553) (by norm_num)
theorem B1796269 : Blo 1060614 1796269 := bbase (se 3 (by rfl) ⟨336800, by rfl⟩ : syracuseStep 1796269 = 673601) (by norm_num)
theorem B1796357 : Blo 1060614 1796357 := bbase (se 4 (by rfl) ⟨168408, by rfl⟩ : syracuseStep 1796357 = 336817) (by norm_num)
theorem B1435925 : Blo 1060614 1435925 := bbase (se 6 (by rfl) ⟨33654, by rfl⟩ : syracuseStep 1435925 = 67309) (by norm_num)
theorem B1796485 : Blo 1060614 1796485 := bbase (se 4 (by rfl) ⟨168420, by rfl⟩ : syracuseStep 1796485 = 336841) (by norm_num)
theorem B2386421 : Blo 1060614 2386421 := bbase (se 5 (by rfl) ⟨111863, by rfl⟩ : syracuseStep 2386421 = 223727) (by norm_num)
theorem B2386493 : Blo 1060614 2386493 := bbase (se 3 (by rfl) ⟨447467, by rfl⟩ : syracuseStep 2386493 = 894935) (by norm_num)
theorem B1534573 : Blo 1060614 1534573 := bbase (se 3 (by rfl) ⟨287732, by rfl⟩ : syracuseStep 1534573 = 575465) (by norm_num)
theorem B1075825 : Blo 1060614 1075825 := bbase (se 2 (by rfl) ⟨403434, by rfl⟩ : syracuseStep 1075825 = 806869) (by norm_num)
theorem B2386565 : Blo 1060614 2386565 := bbase (se 4 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 2386565 = 447481) (by norm_num)
theorem B2386637 : Blo 1060614 2386637 := bbase (se 3 (by rfl) ⟨447494, by rfl⟩ : syracuseStep 2386637 = 894989) (by norm_num)
theorem B6056693 : Blo 1060614 6056693 := bbase (se 5 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 6056693 = 567815) (by norm_num)
theorem B2386709 : Blo 1060614 2386709 := bbase (se 6 (by rfl) ⟨55938, by rfl⟩ : syracuseStep 2386709 = 111877) (by norm_num)
theorem B2386781 : Blo 1060614 2386781 := bbase (se 3 (by rfl) ⟨447521, by rfl⟩ : syracuseStep 2386781 = 895043) (by norm_num)
theorem B14740373 : Blo 1060614 14740373 := bbase (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) (by norm_num)
theorem B2386853 : Blo 1060614 2386853 := bbase (se 4 (by rfl) ⟨223767, by rfl⟩ : syracuseStep 2386853 = 447535) (by norm_num)
theorem B2386925 : Blo 1060614 2386925 := bbase (se 3 (by rfl) ⟨447548, by rfl⟩ : syracuseStep 2386925 = 895097) (by norm_num)
theorem B2386997 : Blo 1060614 2386997 := bbase (se 5 (by rfl) ⟨111890, by rfl⟩ : syracuseStep 2386997 = 223781) (by norm_num)
theorem B1436725 : Blo 1060614 1436725 := bbase (se 5 (by rfl) ⟨67346, by rfl⟩ : syracuseStep 1436725 = 134693) (by norm_num)
theorem B1698941 : Blo 1060614 1698941 := bbase (se 3 (by rfl) ⟨318551, by rfl⟩ : syracuseStep 1698941 = 637103) (by norm_num)
theorem B2387069 : Blo 1060614 2387069 := bbase (se 3 (by rfl) ⟨447575, by rfl⟩ : syracuseStep 2387069 = 895151) (by norm_num)
theorem B2387141 : Blo 1060614 2387141 := bbase (se 4 (by rfl) ⟨223794, by rfl⟩ : syracuseStep 2387141 = 447589) (by norm_num)
theorem B1699069 : Blo 1060614 1699069 := bbase (se 3 (by rfl) ⟨318575, by rfl⟩ : syracuseStep 1699069 = 637151) (by norm_num)
theorem B2387213 : Blo 1060614 2387213 := bbase (se 3 (by rfl) ⟨447602, by rfl⟩ : syracuseStep 2387213 = 895205) (by norm_num)
theorem B1895741 : Blo 1060614 1895741 := bbase (se 3 (by rfl) ⟨355451, by rfl⟩ : syracuseStep 1895741 = 710903) (by norm_num)
theorem B2387285 : Blo 1060614 2387285 := bbase (se 11 (by rfl) ⟨1748, by rfl⟩ : syracuseStep 2387285 = 3497) (by norm_num)
theorem B3403109 : Blo 1060614 3403109 := bbase (se 4 (by rfl) ⟨319041, by rfl⟩ : syracuseStep 3403109 = 638083) (by norm_num)
theorem B2387357 : Blo 1060614 2387357 := bbase (se 3 (by rfl) ⟨447629, by rfl⟩ : syracuseStep 2387357 = 895259) (by norm_num)
theorem B2387429 : Blo 1060614 2387429 := bbase (se 4 (by rfl) ⟨223821, by rfl⟩ : syracuseStep 2387429 = 447643) (by norm_num)
theorem B2551333 : Blo 1060614 2551333 := bbase (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) (by norm_num)
theorem B2387501 : Blo 1060614 2387501 := bbase (se 3 (by rfl) ⟨447656, by rfl⟩ : syracuseStep 2387501 = 895313) (by norm_num)
theorem B2387573 : Blo 1060614 2387573 := bbase (se 5 (by rfl) ⟨111917, by rfl⟩ : syracuseStep 2387573 = 223835) (by norm_num)
theorem B2387645 : Blo 1060614 2387645 := bbase (se 3 (by rfl) ⟨447683, by rfl⟩ : syracuseStep 2387645 = 895367) (by norm_num)
theorem B2387717 : Blo 1060614 2387717 := bbase (se 4 (by rfl) ⟨223848, by rfl⟩ : syracuseStep 2387717 = 447697) (by norm_num)
theorem B2420533 : Blo 1060614 2420533 := bbase (se 5 (by rfl) ⟨113462, by rfl⟩ : syracuseStep 2420533 = 226925) (by norm_num)
theorem B2387789 : Blo 1060614 2387789 := bbase (se 3 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 2387789 = 895421) (by norm_num)
theorem B1699709 : Blo 1060614 1699709 := bbase (se 3 (by rfl) ⟨318695, by rfl⟩ : syracuseStep 1699709 = 637391) (by norm_num)
theorem B2387861 : Blo 1060614 2387861 := bbase (se 6 (by rfl) ⟨55965, by rfl⟩ : syracuseStep 2387861 = 111931) (by norm_num)
theorem B5369813 : Blo 1060614 5369813 := bbase (se 7 (by rfl) ⟨62927, by rfl⟩ : syracuseStep 5369813 = 125855) (by norm_num)
theorem B2387933 : Blo 1060614 2387933 := bbase (se 3 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 2387933 = 895475) (by norm_num)
theorem B2388005 : Blo 1060614 2388005 := bbase (se 4 (by rfl) ⟨223875, by rfl⟩ : syracuseStep 2388005 = 447751) (by norm_num)
theorem B2388077 : Blo 1060614 2388077 := bbase (se 3 (by rfl) ⟨447764, by rfl⟩ : syracuseStep 2388077 = 895529) (by norm_num)
theorem B2551949 : Blo 1060614 2551949 := bbase (se 3 (by rfl) ⟨478490, by rfl⟩ : syracuseStep 2551949 = 956981) (by norm_num)
theorem B2388149 : Blo 1060614 2388149 := bbase (se 5 (by rfl) ⟨111944, by rfl⟩ : syracuseStep 2388149 = 223889) (by norm_num)
theorem B2388221 : Blo 1060614 2388221 := bbase (se 3 (by rfl) ⟨447791, by rfl⟩ : syracuseStep 2388221 = 895583) (by norm_num)
theorem B1700165 : Blo 1060614 1700165 := bbase (se 4 (by rfl) ⟨159390, by rfl⟩ : syracuseStep 1700165 = 318781) (by norm_num)
theorem B2388293 : Blo 1060614 2388293 := bbase (se 4 (by rfl) ⟨223902, by rfl⟩ : syracuseStep 2388293 = 447805) (by norm_num)
theorem B2552141 : Blo 1060614 2552141 := bbase (se 3 (by rfl) ⟨478526, by rfl⟩ : syracuseStep 2552141 = 957053) (by norm_num)
theorem B2388365 : Blo 1060614 2388365 := bbase (se 3 (by rfl) ⟨447818, by rfl⟩ : syracuseStep 2388365 = 895637) (by norm_num)
theorem B2388437 : Blo 1060614 2388437 := bbase (se 7 (by rfl) ⟨27989, by rfl⟩ : syracuseStep 2388437 = 55979) (by norm_num)
theorem B2912741 : Blo 1060614 2912741 := bbase (se 4 (by rfl) ⟨273069, by rfl⟩ : syracuseStep 2912741 = 546139) (by norm_num)
theorem B2388509 : Blo 1060614 2388509 := bbase (se 3 (by rfl) ⟨447845, by rfl⟩ : syracuseStep 2388509 = 895691) (by norm_num)
theorem B1700389 : Blo 1060614 1700389 := bbase (se 4 (by rfl) ⟨159411, by rfl⟩ : syracuseStep 1700389 = 318823) (by norm_num)
theorem B1700453 : Blo 1060614 1700453 := bbase (se 4 (by rfl) ⟨159417, by rfl⟩ : syracuseStep 1700453 = 318835) (by norm_num)
theorem B2388581 : Blo 1060614 2388581 := bbase (se 4 (by rfl) ⟨223929, by rfl⟩ : syracuseStep 2388581 = 447859) (by norm_num)
theorem B1274513 : Blo 1060614 1274513 := bbase (se 2 (by rfl) ⟨477942, by rfl⟩ : syracuseStep 1274513 = 955885) (by norm_num)
theorem B2388653 : Blo 1060614 2388653 := bbase (se 3 (by rfl) ⟨447872, by rfl⟩ : syracuseStep 2388653 = 895745) (by norm_num)
theorem B1700581 : Blo 1060614 1700581 := bbase (se 4 (by rfl) ⟨159429, by rfl⟩ : syracuseStep 1700581 = 318859) (by norm_num)
theorem B1635061 : Blo 1060614 1635061 := bbase (se 5 (by rfl) ⟨76643, by rfl⟩ : syracuseStep 1635061 = 153287) (by norm_num)
theorem B2388725 : Blo 1060614 2388725 := bbase (se 5 (by rfl) ⟨111971, by rfl⟩ : syracuseStep 2388725 = 223943) (by norm_num)
theorem B2388797 : Blo 1060614 2388797 := bbase (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) (by norm_num)
theorem B1438541 : Blo 1060614 1438541 := bbase (se 3 (by rfl) ⟨269726, by rfl⟩ : syracuseStep 1438541 = 539453) (by norm_num)
theorem B1274725 : Blo 1060614 1274725 := bbase (se 4 (by rfl) ⟨119505, by rfl⟩ : syracuseStep 1274725 = 239011) (by norm_num)
theorem B2388869 : Blo 1060614 2388869 := bbase (se 4 (by rfl) ⟨223956, by rfl⟩ : syracuseStep 2388869 = 447913) (by norm_num)
theorem B2552717 : Blo 1060614 2552717 := bbase (se 3 (by rfl) ⟨478634, by rfl⟩ : syracuseStep 2552717 = 957269) (by norm_num)
theorem B6058901 : Blo 1060614 6058901 := bbase (se 6 (by rfl) ⟨142005, by rfl⟩ : syracuseStep 6058901 = 284011) (by norm_num)
theorem B2421701 : Blo 1060614 2421701 := bbase (se 4 (by rfl) ⟨227034, by rfl⟩ : syracuseStep 2421701 = 454069) (by norm_num)
theorem B2388941 : Blo 1060614 2388941 := bbase (se 3 (by rfl) ⟨447926, by rfl⟩ : syracuseStep 2388941 = 895853) (by norm_num)
theorem B12088277 : Blo 1060614 12088277 := bbase (se 7 (by rfl) ⟨141659, by rfl⟩ : syracuseStep 12088277 = 283319) (by norm_num)
theorem B1274869 : Blo 1060614 1274869 := bbase (se 5 (by rfl) ⟨59759, by rfl⟩ : syracuseStep 1274869 = 119519) (by norm_num)
theorem B5108741 : Blo 1060614 5108741 := bbase (se 4 (by rfl) ⟨478944, by rfl⟩ : syracuseStep 5108741 = 957889) (by norm_num)
theorem B2389013 : Blo 1060614 2389013 := bbase (se 6 (by rfl) ⟨55992, by rfl⟩ : syracuseStep 2389013 = 111985) (by norm_num)
theorem B2389085 : Blo 1060614 2389085 := bbase (se 3 (by rfl) ⟨447953, by rfl⟩ : syracuseStep 2389085 = 895907) (by norm_num)
theorem B2389157 : Blo 1060614 2389157 := bbase (se 4 (by rfl) ⟨223983, by rfl⟩ : syracuseStep 2389157 = 447967) (by norm_num)
theorem B1635509 : Blo 1060614 1635509 := bbase (se 5 (by rfl) ⟨76664, by rfl⟩ : syracuseStep 1635509 = 153329) (by norm_num)
theorem B4027589 : Blo 1060614 4027589 := bbase (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) (by norm_num)
theorem B1078481 : Blo 1060614 1078481 := bbase (se 2 (by rfl) ⟨404430, by rfl⟩ : syracuseStep 1078481 = 808861) (by norm_num)
theorem B5371109 : Blo 1060614 5371109 := bbase (se 4 (by rfl) ⟨503541, by rfl⟩ : syracuseStep 5371109 = 1007083) (by norm_num)
theorem B2389229 : Blo 1060614 2389229 := bbase (se 3 (by rfl) ⟨447980, by rfl⟩ : syracuseStep 2389229 = 895961) (by norm_num)
theorem B2553101 : Blo 1060614 2553101 := bbase (se 3 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 2553101 = 957413) (by norm_num)
theorem B2389301 : Blo 1060614 2389301 := bbase (se 5 (by rfl) ⟨111998, by rfl⟩ : syracuseStep 2389301 = 223997) (by norm_num)
theorem B2389373 : Blo 1060614 2389373 := bbase (se 3 (by rfl) ⟨448007, by rfl⟩ : syracuseStep 2389373 = 896015) (by norm_num)
theorem B2389445 : Blo 1060614 2389445 := bbase (se 4 (by rfl) ⟨224010, by rfl⟩ : syracuseStep 2389445 = 448021) (by norm_num)
theorem B4027877 : Blo 1060614 4027877 := bbase (se 4 (by rfl) ⟨377613, by rfl⟩ : syracuseStep 4027877 = 755227) (by norm_num)
theorem B2389517 : Blo 1060614 2389517 := bbase (se 3 (by rfl) ⟨448034, by rfl⟩ : syracuseStep 2389517 = 896069) (by norm_num)
theorem B1078817 : Blo 1060614 1078817 := bbase (se 2 (by rfl) ⟨404556, by rfl⟩ : syracuseStep 1078817 = 809113) (by norm_num)
theorem B3405365 : Blo 1060614 3405365 := bbase (se 5 (by rfl) ⟨159626, by rfl⟩ : syracuseStep 3405365 = 319253) (by norm_num)
theorem B2389589 : Blo 1060614 2389589 := bbase (se 8 (by rfl) ⟨14001, by rfl⟩ : syracuseStep 2389589 = 28003) (by norm_num)
theorem B2586221 : Blo 1060614 2586221 := bbase (se 3 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 2586221 = 969833) (by norm_num)
theorem B2389661 : Blo 1060614 2389661 := bbase (se 3 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 2389661 = 896123) (by norm_num)
theorem B3405493 : Blo 1060614 3405493 := bbase (se 5 (by rfl) ⟨159632, by rfl⟩ : syracuseStep 3405493 = 319265) (by norm_num)
theorem B2389733 : Blo 1060614 2389733 := bbase (se 4 (by rfl) ⟨224037, by rfl⟩ : syracuseStep 2389733 = 448075) (by norm_num)
theorem B1079077 : Blo 1060614 1079077 := bbase (se 4 (by rfl) ⟨101163, by rfl⟩ : syracuseStep 1079077 = 202327) (by norm_num)
theorem B2389805 : Blo 1060614 2389805 := bbase (se 3 (by rfl) ⟨448088, by rfl⟩ : syracuseStep 2389805 = 896177) (by norm_num)
theorem B2684765 : Blo 1060614 2684765 := bbase (se 3 (by rfl) ⟨503393, by rfl⟩ : syracuseStep 2684765 = 1006787) (by norm_num)
theorem B2389877 : Blo 1060614 2389877 := bbase (se 5 (by rfl) ⟨112025, by rfl⟩ : syracuseStep 2389877 = 224051) (by norm_num)
theorem B1701805 : Blo 1060614 1701805 := bbase (se 3 (by rfl) ⟨319088, by rfl⟩ : syracuseStep 1701805 = 638177) (by norm_num)
theorem B2389949 : Blo 1060614 2389949 := bbase (se 3 (by rfl) ⟨448115, by rfl⟩ : syracuseStep 2389949 = 896231) (by norm_num)
theorem B1210321 : Blo 1060614 1210321 := bbase (se 2 (by rfl) ⟨453870, by rfl⟩ : syracuseStep 1210321 = 907741) (by norm_num)
theorem B2390021 : Blo 1060614 2390021 := bbase (se 4 (by rfl) ⟨224064, by rfl⟩ : syracuseStep 2390021 = 448129) (by norm_num)
theorem B2390093 : Blo 1060614 2390093 := bbase (se 3 (by rfl) ⟨448142, by rfl⟩ : syracuseStep 2390093 = 896285) (by norm_num)
theorem B2390165 : Blo 1060614 2390165 := bbase (se 6 (by rfl) ⟨56019, by rfl⟩ : syracuseStep 2390165 = 112039) (by norm_num)
theorem B2685109 : Blo 1060614 2685109 := bbase (se 5 (by rfl) ⟨125864, by rfl⟩ : syracuseStep 2685109 = 251729) (by norm_num)
theorem B2390237 : Blo 1060614 2390237 := bbase (se 3 (by rfl) ⟨448169, by rfl⟩ : syracuseStep 2390237 = 896339) (by norm_num)
theorem B2685221 : Blo 1060614 2685221 := bbase (se 4 (by rfl) ⟨251739, by rfl⟩ : syracuseStep 2685221 = 503479) (by norm_num)
theorem B2390309 : Blo 1060614 2390309 := bbase (se 4 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 2390309 = 448183) (by norm_num)
theorem B2390381 : Blo 1060614 2390381 := bbase (se 3 (by rfl) ⟨448196, by rfl⟩ : syracuseStep 2390381 = 896393) (by norm_num)
theorem B1210777 : Blo 1060614 1210777 := bbase (se 2 (by rfl) ⟨454041, by rfl⟩ : syracuseStep 1210777 = 908083) (by norm_num)
theorem B2390453 : Blo 1060614 2390453 := bbase (se 5 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 2390453 = 224105) (by norm_num)
theorem B2685413 : Blo 1060614 2685413 := bbase (se 4 (by rfl) ⟨251757, by rfl⟩ : syracuseStep 2685413 = 503515) (by norm_num)
theorem B5372405 : Blo 1060614 5372405 := bbase (se 5 (by rfl) ⟨251831, by rfl⟩ : syracuseStep 5372405 = 503663) (by norm_num)
theorem B2390525 : Blo 1060614 2390525 := bbase (se 3 (by rfl) ⟨448223, by rfl⟩ : syracuseStep 2390525 = 896447) (by norm_num)
theorem B1276445 : Blo 1060614 1276445 := bbase (se 3 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 1276445 = 478667) (by norm_num)
theorem B2390597 : Blo 1060614 2390597 := bbase (se 4 (by rfl) ⟨224118, by rfl⟩ : syracuseStep 2390597 = 448237) (by norm_num)
theorem B1702477 : Blo 1060614 1702477 := bbase (se 3 (by rfl) ⟨319214, by rfl⟩ : syracuseStep 1702477 = 638429) (by norm_num)
theorem B4029061 : Blo 1060614 4029061 := bbase (se 4 (by rfl) ⟨377724, by rfl⟩ : syracuseStep 4029061 = 755449) (by norm_num)
theorem B2390669 : Blo 1060614 2390669 := bbase (se 3 (by rfl) ⟨448250, by rfl⟩ : syracuseStep 2390669 = 896501) (by norm_num)
theorem B1211069 : Blo 1060614 1211069 := bbase (se 3 (by rfl) ⟨227075, by rfl⟩ : syracuseStep 1211069 = 454151) (by norm_num)
theorem B2390741 : Blo 1060614 2390741 := bbase (se 7 (by rfl) ⟨28016, by rfl⟩ : syracuseStep 2390741 = 56033) (by norm_num)
theorem B1440509 : Blo 1060614 1440509 := bbase (se 3 (by rfl) ⟨270095, by rfl⟩ : syracuseStep 1440509 = 540191) (by norm_num)
theorem B2390813 : Blo 1060614 2390813 := bbase (se 3 (by rfl) ⟨448277, by rfl⟩ : syracuseStep 2390813 = 896555) (by norm_num)
theorem B2685757 : Blo 1060614 2685757 := bbase (se 3 (by rfl) ⟨503579, by rfl⟩ : syracuseStep 2685757 = 1007159) (by norm_num)
theorem B2390885 : Blo 1060614 2390885 := bbase (se 4 (by rfl) ⟨224145, by rfl⟩ : syracuseStep 2390885 = 448291) (by norm_num)
theorem B1276781 : Blo 1060614 1276781 := bbase (se 3 (by rfl) ⟨239396, by rfl⟩ : syracuseStep 1276781 = 478793) (by norm_num)
theorem B5176181 : Blo 1060614 5176181 := bbase (se 5 (by rfl) ⟨242633, by rfl⟩ : syracuseStep 5176181 = 485267) (by norm_num)
theorem B2685869 : Blo 1060614 2685869 := bbase (se 3 (by rfl) ⟨503600, by rfl⟩ : syracuseStep 2685869 = 1007201) (by norm_num)
theorem B2390957 : Blo 1060614 2390957 := bbase (se 3 (by rfl) ⟨448304, by rfl⟩ : syracuseStep 2390957 = 896609) (by norm_num)
theorem B4029365 : Blo 1060614 4029365 := bbase (se 5 (by rfl) ⟨188876, by rfl⟩ : syracuseStep 4029365 = 377753) (by norm_num)
theorem B1342433 : Blo 1060614 1342433 := bbase (se 2 (by rfl) ⟨503412, by rfl⟩ : syracuseStep 1342433 = 1006825) (by norm_num)
theorem B1276897 : Blo 1060614 1276897 := bbase (se 2 (by rfl) ⟨478836, by rfl⟩ : syracuseStep 1276897 = 957673) (by norm_num)
theorem B2554861 : Blo 1060614 2554861 := bbase (se 3 (by rfl) ⟨479036, by rfl⟩ : syracuseStep 2554861 = 958073) (by norm_num)
theorem B2391029 : Blo 1060614 2391029 := bbase (se 5 (by rfl) ⟨112079, by rfl⟩ : syracuseStep 2391029 = 224159) (by norm_num)
theorem B1342489 : Blo 1060614 1342489 := bbase (se 2 (by rfl) ⟨503433, by rfl⟩ : syracuseStep 1342489 = 1006867) (by norm_num)
theorem B1276969 : Blo 1060614 1276969 := bbase (se 2 (by rfl) ⟨478863, by rfl⟩ : syracuseStep 1276969 = 957727) (by norm_num)
theorem B2391101 : Blo 1060614 2391101 := bbase (se 3 (by rfl) ⟨448331, by rfl⟩ : syracuseStep 2391101 = 896663) (by norm_num)
theorem B1276993 : Blo 1060614 1276993 := bbase (se 2 (by rfl) ⟨478872, by rfl⟩ : syracuseStep 1276993 = 957745) (by norm_num)
theorem B4422725 : Blo 1060614 4422725 := bbase (se 4 (by rfl) ⟨414630, by rfl⟩ : syracuseStep 4422725 = 829261) (by norm_num)
theorem B2686061 : Blo 1060614 2686061 := bbase (se 3 (by rfl) ⟨503636, by rfl⟩ : syracuseStep 2686061 = 1007273) (by norm_num)
theorem B1342585 : Blo 1060614 1342585 := bbase (se 2 (by rfl) ⟨503469, by rfl⟩ : syracuseStep 1342585 = 1006939) (by norm_num)
theorem B2391173 : Blo 1060614 2391173 := bbase (se 4 (by rfl) ⟨224172, by rfl⟩ : syracuseStep 2391173 = 448345) (by norm_num)
theorem B2391245 : Blo 1060614 2391245 := bbase (se 3 (by rfl) ⟨448358, by rfl⟩ : syracuseStep 2391245 = 896717) (by norm_num)
theorem B1277137 : Blo 1060614 1277137 := bbase (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) (by norm_num)
theorem B2391317 : Blo 1060614 2391317 := bbase (se 6 (by rfl) ⟨56046, by rfl⟩ : syracuseStep 2391317 = 112093) (by norm_num)
theorem B1342757 : Blo 1060614 1342757 := bbase (se 4 (by rfl) ⟨125883, by rfl⟩ : syracuseStep 1342757 = 251767) (by norm_num)
theorem B1342813 : Blo 1060614 1342813 := bbase (se 3 (by rfl) ⟨251777, by rfl⟩ : syracuseStep 1342813 = 503555) (by norm_num)
theorem B2391389 : Blo 1060614 2391389 := bbase (se 3 (by rfl) ⟨448385, by rfl⟩ : syracuseStep 2391389 = 896771) (by norm_num)
theorem B8060309 : Blo 1060614 8060309 := bbase (se 6 (by rfl) ⟨188913, by rfl⟩ : syracuseStep 8060309 = 377827) (by norm_num)
theorem B10911125 : Blo 1060614 10911125 := bbase (se 6 (by rfl) ⟨255729, by rfl⟩ : syracuseStep 10911125 = 511459) (by norm_num)
theorem B14548373 : Blo 1060614 14548373 := bbase (se 6 (by rfl) ⟨340977, by rfl⟩ : syracuseStep 14548373 = 681955) (by norm_num)
theorem B2391461 : Blo 1060614 2391461 := bbase (se 4 (by rfl) ⟨224199, by rfl⟩ : syracuseStep 2391461 = 448399) (by norm_num)
theorem B4095397 : Blo 1060614 4095397 := bbase (se 4 (by rfl) ⟨383943, by rfl⟩ : syracuseStep 4095397 = 767887) (by norm_num)
theorem B1342909 : Blo 1060614 1342909 := bbase (se 3 (by rfl) ⟨251795, by rfl⟩ : syracuseStep 1342909 = 503591) (by norm_num)
theorem B2686405 : Blo 1060614 2686405 := bbase (se 4 (by rfl) ⟨251850, by rfl⟩ : syracuseStep 2686405 = 503701) (by norm_num)
theorem B2391533 : Blo 1060614 2391533 := bbase (se 3 (by rfl) ⟨448412, by rfl⟩ : syracuseStep 2391533 = 896825) (by norm_num)
theorem B2686517 : Blo 1060614 2686517 := bbase (se 5 (by rfl) ⟨125930, by rfl⟩ : syracuseStep 2686517 = 251861) (by norm_num)
theorem B2391605 : Blo 1060614 2391605 := bbase (se 5 (by rfl) ⟨112106, by rfl⟩ : syracuseStep 2391605 = 224213) (by norm_num)
theorem B1703477 : Blo 1060614 1703477 := bbase (se 5 (by rfl) ⟨79850, by rfl⟩ : syracuseStep 1703477 = 159701) (by norm_num)
theorem B1343081 : Blo 1060614 1343081 := bbase (se 2 (by rfl) ⟨503655, by rfl⟩ : syracuseStep 1343081 = 1007311) (by norm_num)
theorem B2391677 : Blo 1060614 2391677 := bbase (se 3 (by rfl) ⟨448439, by rfl⟩ : syracuseStep 2391677 = 896879) (by norm_num)
theorem B5111429 : Blo 1060614 5111429 := bbase (se 4 (by rfl) ⟨479196, by rfl⟩ : syracuseStep 5111429 = 958393) (by norm_num)
theorem B1343137 : Blo 1060614 1343137 := bbase (se 2 (by rfl) ⟨503676, by rfl⟩ : syracuseStep 1343137 = 1007353) (by norm_num)
theorem B2391749 : Blo 1060614 2391749 := bbase (se 4 (by rfl) ⟨224226, by rfl⟩ : syracuseStep 2391749 = 448453) (by norm_num)
theorem B2686709 : Blo 1060614 2686709 := bbase (se 5 (by rfl) ⟨125939, by rfl⟩ : syracuseStep 2686709 = 251879) (by norm_num)
theorem B9699061 : Blo 1060614 9699061 := bbase (se 5 (by rfl) ⟨454643, by rfl⟩ : syracuseStep 9699061 = 909287) (by norm_num)
theorem B1343233 : Blo 1060614 1343233 := bbase (se 2 (by rfl) ⟨503712, by rfl⟩ : syracuseStep 1343233 = 1007425) (by norm_num)
theorem B5373701 : Blo 1060614 5373701 := bbase (se 4 (by rfl) ⟨503784, by rfl⟩ : syracuseStep 5373701 = 1007569) (by norm_num)
theorem B2391821 : Blo 1060614 2391821 := bbase (se 3 (by rfl) ⟨448466, by rfl⟩ : syracuseStep 2391821 = 896933) (by norm_num)
theorem B2391893 : Blo 1060614 2391893 := bbase (se 9 (by rfl) ⟨7007, by rfl⟩ : syracuseStep 2391893 = 14015) (by norm_num)
theorem B6225749 : Blo 1060614 6225749 := bbase (se 9 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 6225749 = 36479) (by norm_num)
theorem B2391965 : Blo 1060614 2391965 := bbase (se 3 (by rfl) ⟨448493, by rfl⟩ : syracuseStep 2391965 = 896987) (by norm_num)
theorem B1343405 : Blo 1060614 1343405 := bbase (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) (by norm_num)
theorem B2555869 : Blo 1060614 2555869 := bbase (se 3 (by rfl) ⟨479225, by rfl⟩ : syracuseStep 2555869 = 958451) (by norm_num)
theorem B1343461 : Blo 1060614 1343461 := bbase (se 4 (by rfl) ⟨125949, by rfl⟩ : syracuseStep 1343461 = 251899) (by norm_num)
theorem B2392037 : Blo 1060614 2392037 := bbase (se 4 (by rfl) ⟨224253, by rfl⟩ : syracuseStep 2392037 = 448507) (by norm_num)
theorem B2392145 : Blo 1060614 2392145 := bstep (se 2 (by rfl) ⟨897054, by rfl⟩ : syracuseStep 2392145 = 1794109) B1794109
theorem B2392163 : Blo 1060614 2392163 := bstep (se 1 (by rfl) ⟨1794122, by rfl⟩ : syracuseStep 2392163 = 3588245) B3588245
theorem B2621585 : Blo 1060614 2621585 := bstep (se 2 (by rfl) ⟨983094, by rfl⟩ : syracuseStep 2621585 = 1966189) B1966189
theorem B13631813 : Blo 1060614 13631813 := bstep (se 4 (by rfl) ⟨1277982, by rfl⟩ : syracuseStep 13631813 = 2555965) B2555965
theorem B7668067 : Blo 1060614 7668067 := bstep (se 1 (by rfl) ⟨5751050, by rfl⟩ : syracuseStep 7668067 = 11502101) B11502101
theorem B2392433 : Blo 1060614 2392433 := bstep (se 2 (by rfl) ⟨897162, by rfl⟩ : syracuseStep 2392433 = 1794325) B1794325
theorem B2392451 : Blo 1060614 2392451 := bstep (se 1 (by rfl) ⟨1794338, by rfl⟩ : syracuseStep 2392451 = 3588677) B3588677
theorem B1704323 : Blo 1060614 1704323 := bstep (se 1 (by rfl) ⟨1278242, by rfl⟩ : syracuseStep 1704323 = 2556485) B2556485
theorem B5374349 : Blo 1060614 5374349 := bstep (se 3 (by rfl) ⟨1007690, by rfl⟩ : syracuseStep 5374349 = 2015381) B2015381
theorem B2687377 : Blo 1060614 2687377 := bstep (se 2 (by rfl) ⟨1007766, by rfl⟩ : syracuseStep 2687377 = 2015533) B2015533
theorem B1343891 : Blo 1060614 1343891 := bstep (se 1 (by rfl) ⟨1007918, by rfl⟩ : syracuseStep 1343891 = 2015837) B2015837
theorem B2556323 : Blo 1060614 2556323 := bstep (se 1 (by rfl) ⟨1917242, by rfl⟩ : syracuseStep 2556323 = 3834485) B3834485
theorem B2392721 : Blo 1060614 2392721 := bstep (se 2 (by rfl) ⟨897270, by rfl⟩ : syracuseStep 2392721 = 1794541) B1794541
theorem B2687651 : Blo 1060614 2687651 := bstep (se 1 (by rfl) ⟨2015738, by rfl⟩ : syracuseStep 2687651 = 4031477) B4031477
theorem B2392739 : Blo 1060614 2392739 := bstep (se 1 (by rfl) ⟨1794554, by rfl⟩ : syracuseStep 2392739 = 3589109) B3589109
theorem B1639201 : Blo 1060614 1639201 := bstep (se 2 (by rfl) ⟨614700, by rfl⟩ : syracuseStep 1639201 = 1229401) B1229401
theorem B6128453 : Blo 1060614 6128453 := bstep (se 4 (by rfl) ⟨574542, by rfl⟩ : syracuseStep 6128453 = 1149085) B1149085
theorem B4031309 : Blo 1060614 4031309 := bstep (se 3 (by rfl) ⟨755870, by rfl⟩ : syracuseStep 4031309 = 1511741) B1511741
theorem B2687843 : Blo 1060614 2687843 := bstep (se 1 (by rfl) ⟨2015882, by rfl⟩ : syracuseStep 2687843 = 4031765) B4031765
theorem B1639283 : Blo 1060614 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B1704835 : Blo 1060614 1704835 := bstep (se 1 (by rfl) ⟨1278626, by rfl⟩ : syracuseStep 1704835 = 2557253) B2557253
theorem B2393009 : Blo 1060614 2393009 := bstep (se 2 (by rfl) ⟨897378, by rfl⟩ : syracuseStep 2393009 = 1794757) B1794757
theorem B1704881 : Blo 1060614 1704881 := bstep (se 2 (by rfl) ⟨639330, by rfl⟩ : syracuseStep 1704881 = 1278661) B1278661
theorem B2393027 : Blo 1060614 2393027 := bstep (se 1 (by rfl) ⟨1794770, by rfl⟩ : syracuseStep 2393027 = 3589541) B3589541
theorem B3408941 : Blo 1060614 3408941 := bstep (se 3 (by rfl) ⟨639176, by rfl⟩ : syracuseStep 3408941 = 1278353) B1278353
theorem B1344595 : Blo 1060614 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B1344691 : Blo 1060614 1344691 := bstep (se 1 (by rfl) ⟨1008518, by rfl⟩ : syracuseStep 1344691 = 2017037) B2017037
theorem B2393297 : Blo 1060614 2393297 := bstep (se 2 (by rfl) ⟨897486, by rfl⟩ : syracuseStep 2393297 = 1794973) B1794973
theorem B2393315 : Blo 1060614 2393315 := bstep (se 1 (by rfl) ⟨1794986, by rfl⟩ : syracuseStep 2393315 = 3589973) B3589973
theorem B2393585 : Blo 1060614 2393585 := bstep (se 2 (by rfl) ⟨897594, by rfl⟩ : syracuseStep 2393585 = 1795189) B1795189
theorem B2393603 : Blo 1060614 2393603 := bstep (se 1 (by rfl) ⟨1795202, by rfl⟩ : syracuseStep 2393603 = 3590405) B3590405
theorem B1345187 : Blo 1060614 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B2688785 : Blo 1060614 2688785 := bstep (se 2 (by rfl) ⟨1008294, by rfl⟩ : syracuseStep 2688785 = 2016589) B2016589
theorem B2393873 : Blo 1060614 2393873 := bstep (se 2 (by rfl) ⟨897702, by rfl⟩ : syracuseStep 2393873 = 1795405) B1795405
theorem B2393891 : Blo 1060614 2393891 := bstep (se 1 (by rfl) ⟨1795418, by rfl⟩ : syracuseStep 2393891 = 3590837) B3590837
theorem B2688835 : Blo 1060614 2688835 := bstep (se 1 (by rfl) ⟨2016626, by rfl⟩ : syracuseStep 2688835 = 4033253) B4033253
theorem B3114833 : Blo 1060614 3114833 := bstep (se 2 (by rfl) ⟨1168062, by rfl⟩ : syracuseStep 3114833 = 2336125) B2336125
theorem B2426755 : Blo 1060614 2426755 := bstep (se 1 (by rfl) ⟨1820066, by rfl⟩ : syracuseStep 2426755 = 3640133) B3640133
theorem B6817699 : Blo 1060614 6817699 := bstep (se 1 (by rfl) ⟨5113274, by rfl⟩ : syracuseStep 6817699 = 10226549) B10226549
theorem B2688977 : Blo 1060614 2688977 := bstep (se 2 (by rfl) ⟨1008366, by rfl⟩ : syracuseStep 2688977 = 2016733) B2016733
theorem B5736433 : Blo 1060614 5736433 := bstep (se 2 (by rfl) ⟨2151162, by rfl⟩ : syracuseStep 5736433 = 4302325) B4302325
theorem B2394161 : Blo 1060614 2394161 := bstep (se 2 (by rfl) ⟨897810, by rfl⟩ : syracuseStep 2394161 = 1795621) B1795621
theorem B2394179 : Blo 1060614 2394179 := bstep (se 1 (by rfl) ⟨1795634, by rfl⟩ : syracuseStep 2394179 = 3591269) B3591269
theorem B3410029 : Blo 1060614 3410029 := bstep (se 3 (by rfl) ⟨639380, by rfl⟩ : syracuseStep 3410029 = 1278761) B1278761
theorem B6457477 : Blo 1060614 6457477 := bstep (se 4 (by rfl) ⟨605388, by rfl⟩ : syracuseStep 6457477 = 1210777) B1210777
theorem B14518597 : Blo 1060614 14518597 := bstep (se 4 (by rfl) ⟨1361118, by rfl⟩ : syracuseStep 14518597 = 2722237) B2722237
theorem B2394449 : Blo 1060614 2394449 := bstep (se 2 (by rfl) ⟨897918, by rfl⟩ : syracuseStep 2394449 = 1795837) B1795837
theorem B1345891 : Blo 1060614 1345891 := bstep (se 1 (by rfl) ⟨1009418, by rfl⟩ : syracuseStep 1345891 = 2018837) B2018837
theorem B2394467 : Blo 1060614 2394467 := bstep (se 1 (by rfl) ⟨1795850, by rfl⟩ : syracuseStep 2394467 = 3591701) B3591701
theorem B1345987 : Blo 1060614 1345987 := bstep (se 1 (by rfl) ⟨1009490, by rfl⟩ : syracuseStep 1345987 = 2018981) B2018981
theorem B2394737 : Blo 1060614 2394737 := bstep (se 2 (by rfl) ⟨898026, by rfl⟩ : syracuseStep 2394737 = 1796053) B1796053
theorem B2394755 : Blo 1060614 2394755 := bstep (se 1 (by rfl) ⟨1796066, by rfl⟩ : syracuseStep 2394755 = 3592133) B3592133
theorem B5114659 : Blo 1060614 5114659 := bstep (se 1 (by rfl) ⟨3835994, by rfl⟩ : syracuseStep 5114659 = 7671989) B7671989
theorem B4033421 : Blo 1060614 4033421 := bstep (se 3 (by rfl) ⟨756266, by rfl⟩ : syracuseStep 4033421 = 1512533) B1512533
theorem B6818701 : Blo 1060614 6818701 := bstep (se 3 (by rfl) ⟨1278506, by rfl⟩ : syracuseStep 6818701 = 2557013) B2557013
theorem B2395025 : Blo 1060614 2395025 := bstep (se 2 (by rfl) ⟨898134, by rfl⟩ : syracuseStep 2395025 = 1796269) B1796269
theorem B2395043 : Blo 1060614 2395043 := bstep (se 1 (by rfl) ⟨1796282, by rfl⟩ : syracuseStep 2395043 = 3592565) B3592565
theorem B2689969 : Blo 1060614 2689969 := bstep (se 2 (by rfl) ⟨1008738, by rfl⟩ : syracuseStep 2689969 = 2017477) B2017477
theorem B1346483 : Blo 1060614 1346483 := bstep (se 1 (by rfl) ⟨1009862, by rfl⟩ : syracuseStep 1346483 = 2019725) B2019725
theorem B9079877 : Blo 1060614 9079877 := bstep (se 4 (by rfl) ⟨851238, by rfl⟩ : syracuseStep 9079877 = 1702477) B1702477
theorem B1510483 : Blo 1060614 1510483 := bstep (se 1 (by rfl) ⟨1132862, by rfl⟩ : syracuseStep 1510483 = 2265725) B2265725
theorem B4361357 : Blo 1060614 4361357 := bstep (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) B1635509
theorem B2395313 : Blo 1060614 2395313 := bstep (se 2 (by rfl) ⟨898242, by rfl⟩ : syracuseStep 2395313 = 1796485) B1796485
theorem B1510579 : Blo 1060614 1510579 := bstep (se 1 (by rfl) ⟨1132934, by rfl⟩ : syracuseStep 1510579 = 2265869) B2265869
theorem B2690243 : Blo 1060614 2690243 := bstep (se 1 (by rfl) ⟨2017682, by rfl⟩ : syracuseStep 2690243 = 4035365) B4035365
theorem B2395331 : Blo 1060614 2395331 := bstep (se 1 (by rfl) ⟨1796498, by rfl⟩ : syracuseStep 2395331 = 3592997) B3592997
theorem B8064197 : Blo 1060614 8064197 := bstep (se 4 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 8064197 = 1512037) B1512037
theorem B5377265 : Blo 1060614 5377265 := bstep (se 2 (by rfl) ⟨2016474, by rfl⟩ : syracuseStep 5377265 = 4032949) B4032949
theorem B2690435 : Blo 1060614 2690435 := bstep (se 1 (by rfl) ⟨2017826, by rfl⟩ : syracuseStep 2690435 = 4035653) B4035653
theorem B1347187 : Blo 1060614 1347187 := bstep (se 1 (by rfl) ⟨1010390, by rfl⟩ : syracuseStep 1347187 = 2020781) B2020781
theorem B1511075 : Blo 1060614 1511075 := bstep (se 1 (by rfl) ⟨1133306, by rfl⟩ : syracuseStep 1511075 = 2266613) B2266613
theorem B4034225 : Blo 1060614 4034225 := bstep (se 2 (by rfl) ⟨1512834, by rfl⟩ : syracuseStep 4034225 = 3025669) B3025669
theorem B1347283 : Blo 1060614 1347283 := bstep (se 1 (by rfl) ⟨1010462, by rfl⟩ : syracuseStep 1347283 = 2020925) B2020925
theorem B5115889 : Blo 1060614 5115889 := bstep (se 2 (by rfl) ⟨1918458, by rfl⟩ : syracuseStep 5115889 = 3836917) B3836917
theorem B1511713 : Blo 1060614 1511713 := bstep (se 2 (by rfl) ⟨566892, by rfl⟩ : syracuseStep 1511713 = 1133785) B1133785
theorem B2691377 : Blo 1060614 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B4034893 : Blo 1060614 4034893 := bstep (se 3 (by rfl) ⟨756542, by rfl⟩ : syracuseStep 4034893 = 1513085) B1513085
theorem B2265425 : Blo 1060614 2265425 := bstep (se 2 (by rfl) ⟨849534, by rfl⟩ : syracuseStep 2265425 = 1699069) B1699069
theorem B2691427 : Blo 1060614 2691427 := bstep (se 1 (by rfl) ⟨2018570, by rfl⟩ : syracuseStep 2691427 = 4037141) B4037141
theorem B27201905 : Blo 1060614 27201905 := bstep (se 2 (by rfl) ⟨10200714, by rfl⟩ : syracuseStep 27201905 = 20401429) B20401429
theorem B2691569 : Blo 1060614 2691569 := bstep (se 2 (by rfl) ⟨1009338, by rfl⟩ : syracuseStep 2691569 = 2018677) B2018677
theorem B1512049 : Blo 1060614 1512049 := bstep (se 2 (by rfl) ⟨567018, by rfl⟩ : syracuseStep 1512049 = 1134037) B1134037
theorem B5378723 : Blo 1060614 5378723 := bstep (se 1 (by rfl) ⟨4034042, by rfl⟩ : syracuseStep 5378723 = 8068085) B8068085
theorem B5444273 : Blo 1060614 5444273 := bstep (se 2 (by rfl) ⟨2041602, by rfl⟩ : syracuseStep 5444273 = 4083205) B4083205
theorem B3445517 : Blo 1060614 3445517 := bstep (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) B1292069
theorem B2266211 : Blo 1060614 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B4035683 : Blo 1060614 4035683 := bstep (se 1 (by rfl) ⟨3026762, by rfl⟩ : syracuseStep 4035683 = 6053525) B6053525
theorem B2364547 : Blo 1060614 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B1512641 : Blo 1060614 1512641 := bstep (se 2 (by rfl) ⟨567240, by rfl⟩ : syracuseStep 1512641 = 1134481) B1134481
theorem B13636835 : Blo 1060614 13636835 := bstep (se 1 (by rfl) ⟨10227626, by rfl⟩ : syracuseStep 13636835 = 20455253) B20455253
theorem B20387213 : Blo 1060614 20387213 := bstep (se 3 (by rfl) ⟨3822602, by rfl⟩ : syracuseStep 20387213 = 7645205) B7645205
theorem B5379533 : Blo 1060614 5379533 := bstep (se 3 (by rfl) ⟨1008662, by rfl⟩ : syracuseStep 5379533 = 2017325) B2017325
theorem B2692561 : Blo 1060614 2692561 := bstep (se 2 (by rfl) ⟨1009710, by rfl⟩ : syracuseStep 2692561 = 2019421) B2019421
theorem B3020429 : Blo 1060614 3020429 := bstep (se 3 (by rfl) ⟨566330, by rfl⟩ : syracuseStep 3020429 = 1132661) B1132661
theorem B1513171 : Blo 1060614 1513171 := bstep (se 1 (by rfl) ⟨1134878, by rfl⟩ : syracuseStep 1513171 = 2269757) B2269757
theorem B2692835 : Blo 1060614 2692835 := bstep (se 1 (by rfl) ⟨2019626, by rfl⟩ : syracuseStep 2692835 = 4039253) B4039253
theorem B4036337 : Blo 1060614 4036337 := bstep (se 2 (by rfl) ⟨1513626, by rfl⟩ : syracuseStep 4036337 = 3027253) B3027253
theorem B9836387 : Blo 1060614 9836387 := bstep (se 1 (by rfl) ⟨7377290, by rfl⟩ : syracuseStep 9836387 = 14754581) B14754581
theorem B2693027 : Blo 1060614 2693027 := bstep (se 1 (by rfl) ⟨2019770, by rfl⟩ : syracuseStep 2693027 = 4039541) B4039541
theorem B1513507 : Blo 1060614 1513507 := bstep (se 1 (by rfl) ⟨1135130, by rfl⟩ : syracuseStep 1513507 = 2270261) B2270261
theorem B2267185 : Blo 1060614 2267185 := bstep (se 2 (by rfl) ⟨850194, by rfl⟩ : syracuseStep 2267185 = 1700389) B1700389
theorem B29104181 : Blo 1060614 29104181 := bstep (se 5 (by rfl) ⟨1364258, by rfl⟩ : syracuseStep 29104181 = 2728517) B2728517
theorem B4921613 : Blo 1060614 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B2267441 : Blo 1060614 2267441 := bstep (se 2 (by rfl) ⟨850290, by rfl⟩ : syracuseStep 2267441 = 1700581) B1700581
theorem B1514065 : Blo 1060614 1514065 := bstep (se 2 (by rfl) ⟨567774, by rfl⟩ : syracuseStep 1514065 = 1135549) B1135549
theorem B3021421 : Blo 1060614 3021421 := bstep (se 3 (by rfl) ⟨566516, by rfl⟩ : syracuseStep 3021421 = 1133033) B1133033
theorem B1514099 : Blo 1060614 1514099 := bstep (se 1 (by rfl) ⟨1135574, by rfl⟩ : syracuseStep 1514099 = 2271149) B2271149
theorem B2693969 : Blo 1060614 2693969 := bstep (se 2 (by rfl) ⟨1010238, by rfl⟩ : syracuseStep 2693969 = 2020477) B2020477
theorem B2694019 : Blo 1060614 2694019 := bstep (se 1 (by rfl) ⟨2020514, by rfl⟩ : syracuseStep 2694019 = 4041029) B4041029
theorem B2694161 : Blo 1060614 2694161 := bstep (se 2 (by rfl) ⟨1010310, by rfl⟩ : syracuseStep 2694161 = 2020621) B2020621
theorem B1514657 : Blo 1060614 1514657 := bstep (se 2 (by rfl) ⟨567996, by rfl⟩ : syracuseStep 1514657 = 1135993) B1135993
theorem B4037795 : Blo 1060614 4037795 := bstep (se 1 (by rfl) ⟨3028346, by rfl⟩ : syracuseStep 4037795 = 6056693) B6056693
theorem B4037809 : Blo 1060614 4037809 := bstep (se 2 (by rfl) ⟨1514178, by rfl⟩ : syracuseStep 4037809 = 3028357) B3028357
theorem B1514737 : Blo 1060614 1514737 := bstep (se 2 (by rfl) ⟨568026, by rfl⟩ : syracuseStep 1514737 = 1136053) B1136053
theorem B3546449 : Blo 1060614 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B2268739 : Blo 1060614 2268739 := bstep (se 1 (by rfl) ⟨1701554, by rfl⟩ : syracuseStep 2268739 = 3403109) B3403109
theorem B13803149 : Blo 1060614 13803149 := bstep (se 3 (by rfl) ⟨2588090, by rfl⟩ : syracuseStep 13803149 = 5176181) B5176181
theorem B2269073 : Blo 1060614 2269073 := bstep (se 2 (by rfl) ⟨850902, by rfl⟩ : syracuseStep 2269073 = 1701805) B1701805
theorem B3579821 : Blo 1060614 3579821 := bstep (se 3 (by rfl) ⟨671216, by rfl⟩ : syracuseStep 3579821 = 1342433) B1342433
theorem B3579875 : Blo 1060614 3579875 := bstep (se 1 (by rfl) ⟨2684906, by rfl⟩ : syracuseStep 3579875 = 5369813) B5369813
theorem B1515523 : Blo 1060614 1515523 := bstep (se 1 (by rfl) ⟨1136642, by rfl⟩ : syracuseStep 1515523 = 2273285) B2273285
theorem B34480241 : Blo 1060614 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B11477189 : Blo 1060614 11477189 := bstep (se 4 (by rfl) ⟨1075986, by rfl⟩ : syracuseStep 11477189 = 2151973) B2151973
theorem B3580145 : Blo 1060614 3580145 := bstep (se 2 (by rfl) ⟨1342554, by rfl⟩ : syracuseStep 3580145 = 2685109) B2685109
theorem B3023153 : Blo 1060614 3023153 := bstep (se 2 (by rfl) ⟨1133682, by rfl⟩ : syracuseStep 3023153 = 2267365) B2267365
theorem B5382449 : Blo 1060614 5382449 := bstep (se 2 (by rfl) ⟨2018418, by rfl⟩ : syracuseStep 5382449 = 4036837) B4036837
theorem B1941827 : Blo 1060614 1941827 := bstep (se 1 (by rfl) ⟨1456370, by rfl⟩ : syracuseStep 1941827 = 2912741) B2912741
theorem B29041037 : Blo 1060614 29041037 := bstep (se 3 (by rfl) ⟨5445194, by rfl⟩ : syracuseStep 29041037 = 10890389) B10890389
theorem B3023345 : Blo 1060614 3023345 := bstep (se 2 (by rfl) ⟨1133754, by rfl⟩ : syracuseStep 3023345 = 2267509) B2267509
theorem B4039267 : Blo 1060614 4039267 := bstep (se 1 (by rfl) ⟨3029450, by rfl⟩ : syracuseStep 4039267 = 6058901) B6058901
theorem B1614467 : Blo 1060614 1614467 := bstep (se 1 (by rfl) ⟨1210850, by rfl⟩ : syracuseStep 1614467 = 2421701) B2421701
theorem B3580685 : Blo 1060614 3580685 := bstep (se 3 (by rfl) ⟨671378, by rfl⟩ : syracuseStep 3580685 = 1342757) B1342757
theorem B15344437 : Blo 1060614 15344437 := bstep (se 5 (by rfl) ⟨719270, by rfl⟩ : syracuseStep 15344437 = 1438541) B1438541
theorem B3580739 : Blo 1060614 3580739 := bstep (se 1 (by rfl) ⟨2685554, by rfl⟩ : syracuseStep 3580739 = 5371109) B5371109
theorem B8070029 : Blo 1060614 8070029 := bstep (se 3 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 8070029 = 3026261) B3026261
theorem B2270243 : Blo 1060614 2270243 := bstep (se 1 (by rfl) ⟨1702682, by rfl⟩ : syracuseStep 2270243 = 3405365) B3405365
theorem B3581009 : Blo 1060614 3581009 := bstep (se 2 (by rfl) ⟨1342878, by rfl⟩ : syracuseStep 3581009 = 2685757) B2685757
theorem B18130229 : Blo 1060614 18130229 := bstep (se 5 (by rfl) ⟨849854, by rfl⟩ : syracuseStep 18130229 = 1699709) B1699709
theorem B3024337 : Blo 1060614 3024337 := bstep (se 2 (by rfl) ⟨1134126, by rfl⟩ : syracuseStep 3024337 = 2268253) B2268253
theorem B3581549 : Blo 1060614 3581549 := bstep (se 3 (by rfl) ⟨671540, by rfl⟩ : syracuseStep 3581549 = 1343081) B1343081
theorem B3581603 : Blo 1060614 3581603 := bstep (se 1 (by rfl) ⟨2686202, by rfl⟩ : syracuseStep 3581603 = 5372405) B5372405
theorem B3024611 : Blo 1060614 3024611 := bstep (se 1 (by rfl) ⟨2268458, by rfl⟩ : syracuseStep 3024611 = 4536917) B4536917
theorem B5383907 : Blo 1060614 5383907 := bstep (se 1 (by rfl) ⟨4037930, by rfl⟩ : syracuseStep 5383907 = 8075861) B8075861
theorem B3024803 : Blo 1060614 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B3581873 : Blo 1060614 3581873 := bstep (se 2 (by rfl) ⟨1343202, by rfl⟩ : syracuseStep 3581873 = 2686405) B2686405
theorem B3582413 : Blo 1060614 3582413 := bstep (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) B1343405
theorem B3582467 : Blo 1060614 3582467 := bstep (se 1 (by rfl) ⟨2686850, by rfl⟩ : syracuseStep 3582467 = 5373701) B5373701
theorem B5384717 : Blo 1060614 5384717 := bstep (se 3 (by rfl) ⟨1009634, by rfl⟩ : syracuseStep 5384717 = 2019269) B2019269
theorem B3025613 : Blo 1060614 3025613 := bstep (se 3 (by rfl) ⟨567302, by rfl⟩ : syracuseStep 3025613 = 1134605) B1134605
theorem B4041485 : Blo 1060614 4041485 := bstep (se 3 (by rfl) ⟨757778, by rfl⟩ : syracuseStep 4041485 = 1515557) B1515557
theorem B3582737 : Blo 1060614 3582737 := bstep (se 2 (by rfl) ⟨1343526, by rfl⟩ : syracuseStep 3582737 = 2687053) B2687053
theorem B3025795 : Blo 1060614 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B6466481 : Blo 1060614 6466481 := bstep (se 2 (by rfl) ⟨2424930, by rfl⟩ : syracuseStep 6466481 = 4849861) B4849861
theorem B1616851 : Blo 1060614 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B2272259 : Blo 1060614 2272259 := bstep (se 1 (by rfl) ⟨1704194, by rfl⟩ : syracuseStep 2272259 = 3408389) B3408389
theorem B1617059 : Blo 1060614 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B3583277 : Blo 1060614 3583277 := bstep (se 3 (by rfl) ⟨671864, by rfl⟩ : syracuseStep 3583277 = 1343729) B1343729
theorem B3583331 : Blo 1060614 3583331 := bstep (se 1 (by rfl) ⟨2687498, by rfl⟩ : syracuseStep 3583331 = 5374997) B5374997
theorem B3026285 : Blo 1060614 3026285 := bstep (se 3 (by rfl) ⟨567428, by rfl⟩ : syracuseStep 3026285 = 1134857) B1134857
theorem B8170993 : Blo 1060614 8170993 := bstep (se 2 (by rfl) ⟨3064122, by rfl⟩ : syracuseStep 8170993 = 6128245) B6128245
theorem B3583601 : Blo 1060614 3583601 := bstep (se 2 (by rfl) ⟨1343850, by rfl⟩ : syracuseStep 3583601 = 2687701) B2687701
theorem B9088625 : Blo 1060614 9088625 := bstep (se 2 (by rfl) ⟨3408234, by rfl⟩ : syracuseStep 9088625 = 6816469) B6816469
theorem B8072945 : Blo 1060614 8072945 := bstep (se 2 (by rfl) ⟨3027354, by rfl⟩ : syracuseStep 8072945 = 6054709) B6054709
theorem B1060627 : Blo 1060614 1060627 := bstep (se 1 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 1060627 = 1590941) B1590941
theorem B1060643 : Blo 1060614 1060643 := bstep (se 1 (by rfl) ⟨795482, by rfl⟩ : syracuseStep 1060643 = 1590965) B1590965
theorem B1060659 : Blo 1060614 1060659 := bstep (se 1 (by rfl) ⟨795494, by rfl⟩ : syracuseStep 1060659 = 1590989) B1590989
theorem B1060675 : Blo 1060614 1060675 := bstep (se 1 (by rfl) ⟨795506, by rfl⟩ : syracuseStep 1060675 = 1591013) B1591013
theorem B1060691 : Blo 1060614 1060691 := bstep (se 1 (by rfl) ⟨795518, by rfl⟩ : syracuseStep 1060691 = 1591037) B1591037
theorem B1060707 : Blo 1060614 1060707 := bstep (se 1 (by rfl) ⟨795530, by rfl⟩ : syracuseStep 1060707 = 1591061) B1591061
theorem B4599665 : Blo 1060614 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B1060723 : Blo 1060614 1060723 := bstep (se 1 (by rfl) ⟨795542, by rfl⟩ : syracuseStep 1060723 = 1591085) B1591085
theorem B1060739 : Blo 1060614 1060739 := bstep (se 1 (by rfl) ⟨795554, by rfl⟩ : syracuseStep 1060739 = 1591109) B1591109
theorem B1060755 : Blo 1060614 1060755 := bstep (se 1 (by rfl) ⟨795566, by rfl⟩ : syracuseStep 1060755 = 1591133) B1591133
theorem B1060771 : Blo 1060614 1060771 := bstep (se 1 (by rfl) ⟨795578, by rfl⟩ : syracuseStep 1060771 = 1591157) B1591157
theorem B1060787 : Blo 1060614 1060787 := bstep (se 1 (by rfl) ⟨795590, by rfl⟩ : syracuseStep 1060787 = 1591181) B1591181
theorem B1060803 : Blo 1060614 1060803 := bstep (se 1 (by rfl) ⟨795602, by rfl⟩ : syracuseStep 1060803 = 1591205) B1591205
theorem B1060819 : Blo 1060614 1060819 := bstep (se 1 (by rfl) ⟨795614, by rfl⟩ : syracuseStep 1060819 = 1591229) B1591229
theorem B1060835 : Blo 1060614 1060835 := bstep (se 1 (by rfl) ⟨795626, by rfl⟩ : syracuseStep 1060835 = 1591253) B1591253
theorem B1060851 : Blo 1060614 1060851 := bstep (se 1 (by rfl) ⟨795638, by rfl⟩ : syracuseStep 1060851 = 1591277) B1591277
theorem B1060867 : Blo 1060614 1060867 := bstep (se 1 (by rfl) ⟨795650, by rfl⟩ : syracuseStep 1060867 = 1591301) B1591301
theorem B1060883 : Blo 1060614 1060883 := bstep (se 1 (by rfl) ⟨795662, by rfl⟩ : syracuseStep 1060883 = 1591325) B1591325
theorem B1060899 : Blo 1060614 1060899 := bstep (se 1 (by rfl) ⟨795674, by rfl⟩ : syracuseStep 1060899 = 1591349) B1591349
theorem B1060915 : Blo 1060614 1060915 := bstep (se 1 (by rfl) ⟨795686, by rfl⟩ : syracuseStep 1060915 = 1591373) B1591373
theorem B1060931 : Blo 1060614 1060931 := bstep (se 1 (by rfl) ⟨795698, by rfl⟩ : syracuseStep 1060931 = 1591397) B1591397
theorem B1060947 : Blo 1060614 1060947 := bstep (se 1 (by rfl) ⟨795710, by rfl⟩ : syracuseStep 1060947 = 1591421) B1591421
theorem B1060963 : Blo 1060614 1060963 := bstep (se 1 (by rfl) ⟨795722, by rfl⟩ : syracuseStep 1060963 = 1591445) B1591445
theorem B1060979 : Blo 1060614 1060979 := bstep (se 1 (by rfl) ⟨795734, by rfl⟩ : syracuseStep 1060979 = 1591469) B1591469
theorem B1060995 : Blo 1060614 1060995 := bstep (se 1 (by rfl) ⟨795746, by rfl⟩ : syracuseStep 1060995 = 1591493) B1591493
theorem B3584141 : Blo 1060614 3584141 := bstep (se 3 (by rfl) ⟨672026, by rfl⟩ : syracuseStep 3584141 = 1344053) B1344053
theorem B1061011 : Blo 1060614 1061011 := bstep (se 1 (by rfl) ⟨795758, by rfl⟩ : syracuseStep 1061011 = 1591517) B1591517
theorem B1618067 : Blo 1060614 1618067 := bstep (se 1 (by rfl) ⟨1213550, by rfl⟩ : syracuseStep 1618067 = 2427101) B2427101
theorem B1061027 : Blo 1060614 1061027 := bstep (se 1 (by rfl) ⟨795770, by rfl⟩ : syracuseStep 1061027 = 1591541) B1591541
theorem B1061043 : Blo 1060614 1061043 := bstep (se 1 (by rfl) ⟨795782, by rfl⟩ : syracuseStep 1061043 = 1591565) B1591565
theorem B1061059 : Blo 1060614 1061059 := bstep (se 1 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 1061059 = 1591589) B1591589
theorem B3584195 : Blo 1060614 3584195 := bstep (se 1 (by rfl) ⟨2688146, by rfl⟩ : syracuseStep 3584195 = 5376293) B5376293
theorem B1061075 : Blo 1060614 1061075 := bstep (se 1 (by rfl) ⟨795806, by rfl⟩ : syracuseStep 1061075 = 1591613) B1591613
theorem B1061091 : Blo 1060614 1061091 := bstep (se 1 (by rfl) ⟨795818, by rfl⟩ : syracuseStep 1061091 = 1591637) B1591637
theorem B1061107 : Blo 1060614 1061107 := bstep (se 1 (by rfl) ⟨795830, by rfl⟩ : syracuseStep 1061107 = 1591661) B1591661
theorem B1061123 : Blo 1060614 1061123 := bstep (se 1 (by rfl) ⟨795842, by rfl⟩ : syracuseStep 1061123 = 1591685) B1591685
theorem B6041861 : Blo 1060614 6041861 := bstep (se 4 (by rfl) ⟨566424, by rfl⟩ : syracuseStep 6041861 = 1132849) B1132849
theorem B4534541 : Blo 1060614 4534541 := bstep (se 3 (by rfl) ⟨850226, by rfl⟩ : syracuseStep 4534541 = 1700453) B1700453
theorem B1061139 : Blo 1060614 1061139 := bstep (se 1 (by rfl) ⟨795854, by rfl⟩ : syracuseStep 1061139 = 1591709) B1591709
theorem B1061155 : Blo 1060614 1061155 := bstep (se 1 (by rfl) ⟨795866, by rfl⟩ : syracuseStep 1061155 = 1591733) B1591733
theorem B1061171 : Blo 1060614 1061171 := bstep (se 1 (by rfl) ⟨795878, by rfl⟩ : syracuseStep 1061171 = 1591757) B1591757
theorem B1061187 : Blo 1060614 1061187 := bstep (se 1 (by rfl) ⟨795890, by rfl⟩ : syracuseStep 1061187 = 1591781) B1591781
theorem B1061203 : Blo 1060614 1061203 := bstep (se 1 (by rfl) ⟨795902, by rfl⟩ : syracuseStep 1061203 = 1591805) B1591805
theorem B1061219 : Blo 1060614 1061219 := bstep (se 1 (by rfl) ⟨795914, by rfl⟩ : syracuseStep 1061219 = 1591829) B1591829
theorem B1061235 : Blo 1060614 1061235 := bstep (se 1 (by rfl) ⟨795926, by rfl⟩ : syracuseStep 1061235 = 1591853) B1591853
theorem B1061251 : Blo 1060614 1061251 := bstep (se 1 (by rfl) ⟨795938, by rfl⟩ : syracuseStep 1061251 = 1591877) B1591877
theorem B1061267 : Blo 1060614 1061267 := bstep (se 1 (by rfl) ⟨795950, by rfl⟩ : syracuseStep 1061267 = 1591901) B1591901
theorem B1061283 : Blo 1060614 1061283 := bstep (se 1 (by rfl) ⟨795962, by rfl⟩ : syracuseStep 1061283 = 1591925) B1591925
theorem B1061299 : Blo 1060614 1061299 := bstep (se 1 (by rfl) ⟨795974, by rfl⟩ : syracuseStep 1061299 = 1591949) B1591949
theorem B1061315 : Blo 1060614 1061315 := bstep (se 1 (by rfl) ⟨795986, by rfl⟩ : syracuseStep 1061315 = 1591973) B1591973
theorem B3584465 : Blo 1060614 3584465 := bstep (se 2 (by rfl) ⟨1344174, by rfl⟩ : syracuseStep 3584465 = 2688349) B2688349
theorem B1061331 : Blo 1060614 1061331 := bstep (se 1 (by rfl) ⟨795998, by rfl⟩ : syracuseStep 1061331 = 1591997) B1591997
theorem B1061347 : Blo 1060614 1061347 := bstep (se 1 (by rfl) ⟨796010, by rfl⟩ : syracuseStep 1061347 = 1592021) B1592021
theorem B1061363 : Blo 1060614 1061363 := bstep (se 1 (by rfl) ⟨796022, by rfl⟩ : syracuseStep 1061363 = 1592045) B1592045
theorem B1061379 : Blo 1060614 1061379 := bstep (se 1 (by rfl) ⟨796034, by rfl⟩ : syracuseStep 1061379 = 1592069) B1592069
theorem B3027469 : Blo 1060614 3027469 := bstep (se 3 (by rfl) ⟨567650, by rfl⟩ : syracuseStep 3027469 = 1135301) B1135301
theorem B1061395 : Blo 1060614 1061395 := bstep (se 1 (by rfl) ⟨796046, by rfl⟩ : syracuseStep 1061395 = 1592093) B1592093
theorem B1061411 : Blo 1060614 1061411 := bstep (se 1 (by rfl) ⟨796058, by rfl⟩ : syracuseStep 1061411 = 1592117) B1592117
theorem B1061427 : Blo 1060614 1061427 := bstep (se 1 (by rfl) ⟨796070, by rfl⟩ : syracuseStep 1061427 = 1592141) B1592141
theorem B1061443 : Blo 1060614 1061443 := bstep (se 1 (by rfl) ⟨796082, by rfl⟩ : syracuseStep 1061443 = 1592165) B1592165
theorem B1061459 : Blo 1060614 1061459 := bstep (se 1 (by rfl) ⟨796094, by rfl⟩ : syracuseStep 1061459 = 1592189) B1592189
theorem B1061475 : Blo 1060614 1061475 := bstep (se 1 (by rfl) ⟨796106, by rfl⟩ : syracuseStep 1061475 = 1592213) B1592213
theorem B1061491 : Blo 1060614 1061491 := bstep (se 1 (by rfl) ⟨796118, by rfl⟩ : syracuseStep 1061491 = 1592237) B1592237
theorem B1061507 : Blo 1060614 1061507 := bstep (se 1 (by rfl) ⟨796130, by rfl⟩ : syracuseStep 1061507 = 1592261) B1592261
theorem B1061523 : Blo 1060614 1061523 := bstep (se 1 (by rfl) ⟨796142, by rfl⟩ : syracuseStep 1061523 = 1592285) B1592285
theorem B1061539 : Blo 1060614 1061539 := bstep (se 1 (by rfl) ⟨796154, by rfl⟩ : syracuseStep 1061539 = 1592309) B1592309
theorem B1061555 : Blo 1060614 1061555 := bstep (se 1 (by rfl) ⟨796166, by rfl⟩ : syracuseStep 1061555 = 1592333) B1592333
theorem B1553089 : Blo 1060614 1553089 := bstep (se 2 (by rfl) ⟨582408, by rfl⟩ : syracuseStep 1553089 = 1164817) B1164817
theorem B1061571 : Blo 1060614 1061571 := bstep (se 1 (by rfl) ⟨796178, by rfl⟩ : syracuseStep 1061571 = 1592357) B1592357
theorem B1061587 : Blo 1060614 1061587 := bstep (se 1 (by rfl) ⟨796190, by rfl⟩ : syracuseStep 1061587 = 1592381) B1592381
theorem B1061603 : Blo 1060614 1061603 := bstep (se 1 (by rfl) ⟨796202, by rfl⟩ : syracuseStep 1061603 = 1592405) B1592405
theorem B1061619 : Blo 1060614 1061619 := bstep (se 1 (by rfl) ⟨796214, by rfl⟩ : syracuseStep 1061619 = 1592429) B1592429
theorem B1061635 : Blo 1060614 1061635 := bstep (se 1 (by rfl) ⟨796226, by rfl⟩ : syracuseStep 1061635 = 1592453) B1592453
theorem B1061651 : Blo 1060614 1061651 := bstep (se 1 (by rfl) ⟨796238, by rfl⟩ : syracuseStep 1061651 = 1592477) B1592477
theorem B1061667 : Blo 1060614 1061667 := bstep (se 1 (by rfl) ⟨796250, by rfl⟩ : syracuseStep 1061667 = 1592501) B1592501
theorem B1061683 : Blo 1060614 1061683 := bstep (se 1 (by rfl) ⟨796262, by rfl⟩ : syracuseStep 1061683 = 1592525) B1592525
theorem B1061699 : Blo 1060614 1061699 := bstep (se 1 (by rfl) ⟨796274, by rfl⟩ : syracuseStep 1061699 = 1592549) B1592549
theorem B1061715 : Blo 1060614 1061715 := bstep (se 1 (by rfl) ⟨796286, by rfl⟩ : syracuseStep 1061715 = 1592573) B1592573
theorem B1061731 : Blo 1060614 1061731 := bstep (se 1 (by rfl) ⟨796298, by rfl⟩ : syracuseStep 1061731 = 1592597) B1592597
theorem B3683171 : Blo 1060614 3683171 := bstep (se 1 (by rfl) ⟨2762378, by rfl⟩ : syracuseStep 3683171 = 5524757) B5524757
theorem B1061747 : Blo 1060614 1061747 := bstep (se 1 (by rfl) ⟨796310, by rfl⟩ : syracuseStep 1061747 = 1592621) B1592621
theorem B1061763 : Blo 1060614 1061763 := bstep (se 1 (by rfl) ⟨796322, by rfl⟩ : syracuseStep 1061763 = 1592645) B1592645
theorem B1061779 : Blo 1060614 1061779 := bstep (se 1 (by rfl) ⟨796334, by rfl⟩ : syracuseStep 1061779 = 1592669) B1592669
theorem B1061795 : Blo 1060614 1061795 := bstep (se 1 (by rfl) ⟨796346, by rfl⟩ : syracuseStep 1061795 = 1592693) B1592693
theorem B6042545 : Blo 1060614 6042545 := bstep (se 2 (by rfl) ⟨2265954, by rfl⟩ : syracuseStep 6042545 = 4531909) B4531909
theorem B1061811 : Blo 1060614 1061811 := bstep (se 1 (by rfl) ⟨796358, by rfl⟩ : syracuseStep 1061811 = 1592717) B1592717
theorem B1061827 : Blo 1060614 1061827 := bstep (se 1 (by rfl) ⟨796370, by rfl⟩ : syracuseStep 1061827 = 1592741) B1592741
theorem B1061843 : Blo 1060614 1061843 := bstep (se 1 (by rfl) ⟨796382, by rfl⟩ : syracuseStep 1061843 = 1592765) B1592765
theorem B1061859 : Blo 1060614 1061859 := bstep (se 1 (by rfl) ⟨796394, by rfl⟩ : syracuseStep 1061859 = 1592789) B1592789
theorem B3585005 : Blo 1060614 3585005 := bstep (se 3 (by rfl) ⟨672188, by rfl⟩ : syracuseStep 3585005 = 1344377) B1344377
theorem B1061875 : Blo 1060614 1061875 := bstep (se 1 (by rfl) ⟨796406, by rfl⟩ : syracuseStep 1061875 = 1592813) B1592813
theorem B1061891 : Blo 1060614 1061891 := bstep (se 1 (by rfl) ⟨796418, by rfl⟩ : syracuseStep 1061891 = 1592837) B1592837
theorem B1061907 : Blo 1060614 1061907 := bstep (se 1 (by rfl) ⟨796430, by rfl⟩ : syracuseStep 1061907 = 1592861) B1592861
theorem B1061923 : Blo 1060614 1061923 := bstep (se 1 (by rfl) ⟨796442, by rfl⟩ : syracuseStep 1061923 = 1592885) B1592885
theorem B3585059 : Blo 1060614 3585059 := bstep (se 1 (by rfl) ⟨2688794, by rfl⟩ : syracuseStep 3585059 = 5377589) B5377589
theorem B1061939 : Blo 1060614 1061939 := bstep (se 1 (by rfl) ⟨796454, by rfl⟩ : syracuseStep 1061939 = 1592909) B1592909
theorem B1061955 : Blo 1060614 1061955 := bstep (se 1 (by rfl) ⟨796466, by rfl⟩ : syracuseStep 1061955 = 1592933) B1592933
theorem B1061971 : Blo 1060614 1061971 := bstep (se 1 (by rfl) ⟨796478, by rfl⟩ : syracuseStep 1061971 = 1592957) B1592957
theorem B1061987 : Blo 1060614 1061987 := bstep (se 1 (by rfl) ⟨796490, by rfl⟩ : syracuseStep 1061987 = 1592981) B1592981
theorem B1062003 : Blo 1060614 1062003 := bstep (se 1 (by rfl) ⟨796502, by rfl⟩ : syracuseStep 1062003 = 1593005) B1593005
theorem B1062019 : Blo 1060614 1062019 := bstep (se 1 (by rfl) ⟨796514, by rfl⟩ : syracuseStep 1062019 = 1593029) B1593029
theorem B1062035 : Blo 1060614 1062035 := bstep (se 1 (by rfl) ⟨796526, by rfl⟩ : syracuseStep 1062035 = 1593053) B1593053
theorem B1062051 : Blo 1060614 1062051 := bstep (se 1 (by rfl) ⟨796538, by rfl⟩ : syracuseStep 1062051 = 1593077) B1593077
theorem B1062067 : Blo 1060614 1062067 := bstep (se 1 (by rfl) ⟨796550, by rfl⟩ : syracuseStep 1062067 = 1593101) B1593101
theorem B1062083 : Blo 1060614 1062083 := bstep (se 1 (by rfl) ⟨796562, by rfl⟩ : syracuseStep 1062083 = 1593125) B1593125
theorem B1062099 : Blo 1060614 1062099 := bstep (se 1 (by rfl) ⟨796574, by rfl⟩ : syracuseStep 1062099 = 1593149) B1593149
theorem B1062115 : Blo 1060614 1062115 := bstep (se 1 (by rfl) ⟨796586, by rfl⟩ : syracuseStep 1062115 = 1593173) B1593173
theorem B1062131 : Blo 1060614 1062131 := bstep (se 1 (by rfl) ⟨796598, by rfl⟩ : syracuseStep 1062131 = 1593197) B1593197
theorem B1062147 : Blo 1060614 1062147 := bstep (se 1 (by rfl) ⟨796610, by rfl⟩ : syracuseStep 1062147 = 1593221) B1593221
theorem B1062163 : Blo 1060614 1062163 := bstep (se 1 (by rfl) ⟨796622, by rfl⟩ : syracuseStep 1062163 = 1593245) B1593245
theorem B1193251 : Blo 1060614 1193251 := bstep (se 1 (by rfl) ⟨894938, by rfl⟩ : syracuseStep 1193251 = 1789877) B1789877
theorem B1062179 : Blo 1060614 1062179 := bstep (se 1 (by rfl) ⟨796634, by rfl⟩ : syracuseStep 1062179 = 1593269) B1593269
theorem B3585329 : Blo 1060614 3585329 := bstep (se 2 (by rfl) ⟨1344498, by rfl⟩ : syracuseStep 3585329 = 2688997) B2688997
theorem B1062195 : Blo 1060614 1062195 := bstep (se 1 (by rfl) ⟨796646, by rfl⟩ : syracuseStep 1062195 = 1593293) B1593293
theorem B1062211 : Blo 1060614 1062211 := bstep (se 1 (by rfl) ⟨796658, by rfl⟩ : syracuseStep 1062211 = 1593317) B1593317
theorem B1062227 : Blo 1060614 1062227 := bstep (se 1 (by rfl) ⟨796670, by rfl⟩ : syracuseStep 1062227 = 1593341) B1593341
theorem B1062243 : Blo 1060614 1062243 := bstep (se 1 (by rfl) ⟨796682, by rfl⟩ : syracuseStep 1062243 = 1593365) B1593365
theorem B5387633 : Blo 1060614 5387633 := bstep (se 2 (by rfl) ⟨2020362, by rfl⟩ : syracuseStep 5387633 = 4040725) B4040725
theorem B1062259 : Blo 1060614 1062259 := bstep (se 1 (by rfl) ⟨796694, by rfl⟩ : syracuseStep 1062259 = 1593389) B1593389
theorem B1062275 : Blo 1060614 1062275 := bstep (se 1 (by rfl) ⟨796706, by rfl⟩ : syracuseStep 1062275 = 1593413) B1593413
theorem B1062291 : Blo 1060614 1062291 := bstep (se 1 (by rfl) ⟨796718, by rfl⟩ : syracuseStep 1062291 = 1593437) B1593437
theorem B1062307 : Blo 1060614 1062307 := bstep (se 1 (by rfl) ⟨796730, by rfl⟩ : syracuseStep 1062307 = 1593461) B1593461
theorem B1193395 : Blo 1060614 1193395 := bstep (se 1 (by rfl) ⟨895046, by rfl⟩ : syracuseStep 1193395 = 1790093) B1790093
theorem B1062323 : Blo 1060614 1062323 := bstep (se 1 (by rfl) ⟨796742, by rfl⟩ : syracuseStep 1062323 = 1593485) B1593485
theorem B1062339 : Blo 1060614 1062339 := bstep (se 1 (by rfl) ⟨796754, by rfl⟩ : syracuseStep 1062339 = 1593509) B1593509
theorem B1062355 : Blo 1060614 1062355 := bstep (se 1 (by rfl) ⟨796766, by rfl⟩ : syracuseStep 1062355 = 1593533) B1593533
theorem B1062371 : Blo 1060614 1062371 := bstep (se 1 (by rfl) ⟨796778, by rfl⟩ : syracuseStep 1062371 = 1593557) B1593557
theorem B1062387 : Blo 1060614 1062387 := bstep (se 1 (by rfl) ⟨796790, by rfl⟩ : syracuseStep 1062387 = 1593581) B1593581
theorem B1062403 : Blo 1060614 1062403 := bstep (se 1 (by rfl) ⟨796802, by rfl⟩ : syracuseStep 1062403 = 1593605) B1593605
theorem B1062419 : Blo 1060614 1062419 := bstep (se 1 (by rfl) ⟨796814, by rfl⟩ : syracuseStep 1062419 = 1593629) B1593629
theorem B1062435 : Blo 1060614 1062435 := bstep (se 1 (by rfl) ⟨796826, by rfl⟩ : syracuseStep 1062435 = 1593653) B1593653
theorem B3028529 : Blo 1060614 3028529 := bstep (se 2 (by rfl) ⟨1135698, by rfl⟩ : syracuseStep 3028529 = 2271397) B2271397
theorem B1062451 : Blo 1060614 1062451 := bstep (se 1 (by rfl) ⟨796838, by rfl⟩ : syracuseStep 1062451 = 1593677) B1593677
theorem B1193539 : Blo 1060614 1193539 := bstep (se 1 (by rfl) ⟨895154, by rfl⟩ : syracuseStep 1193539 = 1790309) B1790309
theorem B1062467 : Blo 1060614 1062467 := bstep (se 1 (by rfl) ⟨796850, by rfl⟩ : syracuseStep 1062467 = 1593701) B1593701
theorem B1062483 : Blo 1060614 1062483 := bstep (se 1 (by rfl) ⟨796862, by rfl⟩ : syracuseStep 1062483 = 1593725) B1593725
theorem B1062499 : Blo 1060614 1062499 := bstep (se 1 (by rfl) ⟨796874, by rfl⟩ : syracuseStep 1062499 = 1593749) B1593749
theorem B1062515 : Blo 1060614 1062515 := bstep (se 1 (by rfl) ⟨796886, by rfl⟩ : syracuseStep 1062515 = 1593773) B1593773
theorem B1062531 : Blo 1060614 1062531 := bstep (se 1 (by rfl) ⟨796898, by rfl⟩ : syracuseStep 1062531 = 1593797) B1593797
theorem B1062547 : Blo 1060614 1062547 := bstep (se 1 (by rfl) ⟨796910, by rfl⟩ : syracuseStep 1062547 = 1593821) B1593821
theorem B1062563 : Blo 1060614 1062563 := bstep (se 1 (by rfl) ⟨796922, by rfl⟩ : syracuseStep 1062563 = 1593845) B1593845
theorem B1062579 : Blo 1060614 1062579 := bstep (se 1 (by rfl) ⟨796934, by rfl⟩ : syracuseStep 1062579 = 1593869) B1593869
theorem B1062595 : Blo 1060614 1062595 := bstep (se 1 (by rfl) ⟨796946, by rfl⟩ : syracuseStep 1062595 = 1593893) B1593893
theorem B1193683 : Blo 1060614 1193683 := bstep (se 1 (by rfl) ⟨895262, by rfl⟩ : syracuseStep 1193683 = 1790525) B1790525
theorem B1062611 : Blo 1060614 1062611 := bstep (se 1 (by rfl) ⟨796958, by rfl⟩ : syracuseStep 1062611 = 1593917) B1593917
theorem B1062627 : Blo 1060614 1062627 := bstep (se 1 (by rfl) ⟨796970, by rfl⟩ : syracuseStep 1062627 = 1593941) B1593941
theorem B1062643 : Blo 1060614 1062643 := bstep (se 1 (by rfl) ⟨796982, by rfl⟩ : syracuseStep 1062643 = 1593965) B1593965
theorem B1062659 : Blo 1060614 1062659 := bstep (se 1 (by rfl) ⟨796994, by rfl⟩ : syracuseStep 1062659 = 1593989) B1593989
theorem B1062675 : Blo 1060614 1062675 := bstep (se 1 (by rfl) ⟨797006, by rfl⟩ : syracuseStep 1062675 = 1594013) B1594013
theorem B1062691 : Blo 1060614 1062691 := bstep (se 1 (by rfl) ⟨797018, by rfl⟩ : syracuseStep 1062691 = 1594037) B1594037
theorem B1062707 : Blo 1060614 1062707 := bstep (se 1 (by rfl) ⟨797030, by rfl⟩ : syracuseStep 1062707 = 1594061) B1594061
theorem B1062723 : Blo 1060614 1062723 := bstep (se 1 (by rfl) ⟨797042, by rfl⟩ : syracuseStep 1062723 = 1594085) B1594085
theorem B3585869 : Blo 1060614 3585869 := bstep (se 3 (by rfl) ⟨672350, by rfl⟩ : syracuseStep 3585869 = 1344701) B1344701
theorem B1062739 : Blo 1060614 1062739 := bstep (se 1 (by rfl) ⟨797054, by rfl⟩ : syracuseStep 1062739 = 1594109) B1594109
theorem B1193827 : Blo 1060614 1193827 := bstep (se 1 (by rfl) ⟨895370, by rfl⟩ : syracuseStep 1193827 = 1790741) B1790741
theorem B1062755 : Blo 1060614 1062755 := bstep (se 1 (by rfl) ⟨797066, by rfl⟩ : syracuseStep 1062755 = 1594133) B1594133
theorem B1062771 : Blo 1060614 1062771 := bstep (se 1 (by rfl) ⟨797078, by rfl⟩ : syracuseStep 1062771 = 1594157) B1594157
theorem B3585923 : Blo 1060614 3585923 := bstep (se 1 (by rfl) ⟨2689442, by rfl⟩ : syracuseStep 3585923 = 5378885) B5378885
theorem B1062787 : Blo 1060614 1062787 := bstep (se 1 (by rfl) ⟨797090, by rfl⟩ : syracuseStep 1062787 = 1594181) B1594181
theorem B1062803 : Blo 1060614 1062803 := bstep (se 1 (by rfl) ⟨797102, by rfl⟩ : syracuseStep 1062803 = 1594205) B1594205
theorem B1062819 : Blo 1060614 1062819 := bstep (se 1 (by rfl) ⟨797114, by rfl⟩ : syracuseStep 1062819 = 1594229) B1594229
theorem B1062835 : Blo 1060614 1062835 := bstep (se 1 (by rfl) ⟨797126, by rfl⟩ : syracuseStep 1062835 = 1594253) B1594253
theorem B1062851 : Blo 1060614 1062851 := bstep (se 1 (by rfl) ⟨797138, by rfl⟩ : syracuseStep 1062851 = 1594277) B1594277
theorem B1062867 : Blo 1060614 1062867 := bstep (se 1 (by rfl) ⟨797150, by rfl⟩ : syracuseStep 1062867 = 1594301) B1594301
theorem B1062883 : Blo 1060614 1062883 := bstep (se 1 (by rfl) ⟨797162, by rfl⟩ : syracuseStep 1062883 = 1594325) B1594325
theorem B1193971 : Blo 1060614 1193971 := bstep (se 1 (by rfl) ⟨895478, by rfl⟩ : syracuseStep 1193971 = 1790957) B1790957
theorem B1062899 : Blo 1060614 1062899 := bstep (se 1 (by rfl) ⟨797174, by rfl⟩ : syracuseStep 1062899 = 1594349) B1594349
theorem B1062915 : Blo 1060614 1062915 := bstep (se 1 (by rfl) ⟨797186, by rfl⟩ : syracuseStep 1062915 = 1594373) B1594373
theorem B1062931 : Blo 1060614 1062931 := bstep (se 1 (by rfl) ⟨797198, by rfl⟩ : syracuseStep 1062931 = 1594397) B1594397
theorem B1554467 : Blo 1060614 1554467 := bstep (se 1 (by rfl) ⟨1165850, by rfl⟩ : syracuseStep 1554467 = 2331701) B2331701
theorem B1062947 : Blo 1060614 1062947 := bstep (se 1 (by rfl) ⟨797210, by rfl⟩ : syracuseStep 1062947 = 1594421) B1594421
theorem B1062963 : Blo 1060614 1062963 := bstep (se 1 (by rfl) ⟨797222, by rfl⟩ : syracuseStep 1062963 = 1594445) B1594445
theorem B1062979 : Blo 1060614 1062979 := bstep (se 1 (by rfl) ⟨797234, by rfl⟩ : syracuseStep 1062979 = 1594469) B1594469
theorem B1062995 : Blo 1060614 1062995 := bstep (se 1 (by rfl) ⟨797246, by rfl⟩ : syracuseStep 1062995 = 1594493) B1594493
theorem B1063011 : Blo 1060614 1063011 := bstep (se 1 (by rfl) ⟨797258, by rfl⟩ : syracuseStep 1063011 = 1594517) B1594517
theorem B1063027 : Blo 1060614 1063027 := bstep (se 1 (by rfl) ⟨797270, by rfl⟩ : syracuseStep 1063027 = 1594541) B1594541
theorem B1194115 : Blo 1060614 1194115 := bstep (se 1 (by rfl) ⟨895586, by rfl⟩ : syracuseStep 1194115 = 1791173) B1791173
theorem B1063043 : Blo 1060614 1063043 := bstep (se 1 (by rfl) ⟨797282, by rfl⟩ : syracuseStep 1063043 = 1594565) B1594565
theorem B3586193 : Blo 1060614 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B2046097 : Blo 1060614 2046097 := bstep (se 2 (by rfl) ⟨767286, by rfl⟩ : syracuseStep 2046097 = 1534573) B1534573
theorem B1063059 : Blo 1060614 1063059 := bstep (se 1 (by rfl) ⟨797294, by rfl⟩ : syracuseStep 1063059 = 1594589) B1594589
theorem B1063075 : Blo 1060614 1063075 := bstep (se 1 (by rfl) ⟨797306, by rfl⟩ : syracuseStep 1063075 = 1594613) B1594613
theorem B1063091 : Blo 1060614 1063091 := bstep (se 1 (by rfl) ⟨797318, by rfl⟩ : syracuseStep 1063091 = 1594637) B1594637
theorem B1063107 : Blo 1060614 1063107 := bstep (se 1 (by rfl) ⟨797330, by rfl⟩ : syracuseStep 1063107 = 1594661) B1594661
theorem B3029201 : Blo 1060614 3029201 := bstep (se 2 (by rfl) ⟨1135950, by rfl⟩ : syracuseStep 3029201 = 2271901) B2271901
theorem B1063123 : Blo 1060614 1063123 := bstep (se 1 (by rfl) ⟨797342, by rfl⟩ : syracuseStep 1063123 = 1594685) B1594685
theorem B1063139 : Blo 1060614 1063139 := bstep (se 1 (by rfl) ⟨797354, by rfl⟩ : syracuseStep 1063139 = 1594709) B1594709
theorem B1063155 : Blo 1060614 1063155 := bstep (se 1 (by rfl) ⟨797366, by rfl⟩ : syracuseStep 1063155 = 1594733) B1594733
theorem B1063171 : Blo 1060614 1063171 := bstep (se 1 (by rfl) ⟨797378, by rfl⟩ : syracuseStep 1063171 = 1594757) B1594757
theorem B1194259 : Blo 1060614 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B1063187 : Blo 1060614 1063187 := bstep (se 1 (by rfl) ⟨797390, by rfl⟩ : syracuseStep 1063187 = 1594781) B1594781
theorem B1063203 : Blo 1060614 1063203 := bstep (se 1 (by rfl) ⟨797402, by rfl⟩ : syracuseStep 1063203 = 1594805) B1594805
theorem B1063219 : Blo 1060614 1063219 := bstep (se 1 (by rfl) ⟨797414, by rfl⟩ : syracuseStep 1063219 = 1594829) B1594829
theorem B1063235 : Blo 1060614 1063235 := bstep (se 1 (by rfl) ⟨797426, by rfl⟩ : syracuseStep 1063235 = 1594853) B1594853
theorem B1063251 : Blo 1060614 1063251 := bstep (se 1 (by rfl) ⟨797438, by rfl⟩ : syracuseStep 1063251 = 1594877) B1594877
theorem B6044003 : Blo 1060614 6044003 := bstep (se 1 (by rfl) ⟨4533002, by rfl⟩ : syracuseStep 6044003 = 9066005) B9066005
theorem B1063267 : Blo 1060614 1063267 := bstep (se 1 (by rfl) ⟨797450, by rfl⟩ : syracuseStep 1063267 = 1594901) B1594901
theorem B1063283 : Blo 1060614 1063283 := bstep (se 1 (by rfl) ⟨797462, by rfl⟩ : syracuseStep 1063283 = 1594925) B1594925
theorem B1063299 : Blo 1060614 1063299 := bstep (se 1 (by rfl) ⟨797474, by rfl⟩ : syracuseStep 1063299 = 1594949) B1594949
theorem B1063315 : Blo 1060614 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B1194403 : Blo 1060614 1194403 := bstep (se 1 (by rfl) ⟨895802, by rfl⟩ : syracuseStep 1194403 = 1791605) B1791605
theorem B1063331 : Blo 1060614 1063331 := bstep (se 1 (by rfl) ⟨797498, by rfl⟩ : syracuseStep 1063331 = 1594997) B1594997
theorem B1063347 : Blo 1060614 1063347 := bstep (se 1 (by rfl) ⟨797510, by rfl⟩ : syracuseStep 1063347 = 1595021) B1595021
theorem B2013635 : Blo 1060614 2013635 := bstep (se 1 (by rfl) ⟨1510226, by rfl⟩ : syracuseStep 2013635 = 3020453) B3020453
theorem B1063363 : Blo 1060614 1063363 := bstep (se 1 (by rfl) ⟨797522, by rfl⟩ : syracuseStep 1063363 = 1595045) B1595045
theorem B1063379 : Blo 1060614 1063379 := bstep (se 1 (by rfl) ⟨797534, by rfl⟩ : syracuseStep 1063379 = 1595069) B1595069
theorem B1063395 : Blo 1060614 1063395 := bstep (se 1 (by rfl) ⟨797546, by rfl⟩ : syracuseStep 1063395 = 1595093) B1595093
theorem B1063411 : Blo 1060614 1063411 := bstep (se 1 (by rfl) ⟨797558, by rfl⟩ : syracuseStep 1063411 = 1595117) B1595117
theorem B1063427 : Blo 1060614 1063427 := bstep (se 1 (by rfl) ⟨797570, by rfl⟩ : syracuseStep 1063427 = 1595141) B1595141
theorem B2243089 : Blo 1060614 2243089 := bstep (se 2 (by rfl) ⟨841158, by rfl⟩ : syracuseStep 2243089 = 1682317) B1682317
theorem B1063443 : Blo 1060614 1063443 := bstep (se 1 (by rfl) ⟨797582, by rfl⟩ : syracuseStep 1063443 = 1595165) B1595165
theorem B1063459 : Blo 1060614 1063459 := bstep (se 1 (by rfl) ⟨797594, by rfl⟩ : syracuseStep 1063459 = 1595189) B1595189
theorem B1194547 : Blo 1060614 1194547 := bstep (se 1 (by rfl) ⟨895910, by rfl⟩ : syracuseStep 1194547 = 1791821) B1791821
theorem B1063475 : Blo 1060614 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B1063491 : Blo 1060614 1063491 := bstep (se 1 (by rfl) ⟨797618, by rfl⟩ : syracuseStep 1063491 = 1595237) B1595237
theorem B1063507 : Blo 1060614 1063507 := bstep (se 1 (by rfl) ⟨797630, by rfl⟩ : syracuseStep 1063507 = 1595261) B1595261
theorem B1063523 : Blo 1060614 1063523 := bstep (se 1 (by rfl) ⟨797642, by rfl⟩ : syracuseStep 1063523 = 1595285) B1595285
theorem B1063539 : Blo 1060614 1063539 := bstep (se 1 (by rfl) ⟨797654, by rfl⟩ : syracuseStep 1063539 = 1595309) B1595309
theorem B1063555 : Blo 1060614 1063555 := bstep (se 1 (by rfl) ⟨797666, by rfl⟩ : syracuseStep 1063555 = 1595333) B1595333
theorem B1063571 : Blo 1060614 1063571 := bstep (se 1 (by rfl) ⟨797678, by rfl⟩ : syracuseStep 1063571 = 1595357) B1595357
theorem B1063587 : Blo 1060614 1063587 := bstep (se 1 (by rfl) ⟨797690, by rfl⟩ : syracuseStep 1063587 = 1595381) B1595381
theorem B3586733 : Blo 1060614 3586733 := bstep (se 3 (by rfl) ⟨672512, by rfl⟩ : syracuseStep 3586733 = 1345025) B1345025
theorem B1063603 : Blo 1060614 1063603 := bstep (se 1 (by rfl) ⟨797702, by rfl⟩ : syracuseStep 1063603 = 1595405) B1595405
theorem B1194691 : Blo 1060614 1194691 := bstep (se 1 (by rfl) ⟨896018, by rfl⟩ : syracuseStep 1194691 = 1792037) B1792037
theorem B1063619 : Blo 1060614 1063619 := bstep (se 1 (by rfl) ⟨797714, by rfl⟩ : syracuseStep 1063619 = 1595429) B1595429
theorem B1063635 : Blo 1060614 1063635 := bstep (se 1 (by rfl) ⟨797726, by rfl⟩ : syracuseStep 1063635 = 1595453) B1595453
theorem B2013923 : Blo 1060614 2013923 := bstep (se 1 (by rfl) ⟨1510442, by rfl⟩ : syracuseStep 2013923 = 3020885) B3020885
theorem B3586787 : Blo 1060614 3586787 := bstep (se 1 (by rfl) ⟨2690090, by rfl⟩ : syracuseStep 3586787 = 5380181) B5380181
theorem B1063651 : Blo 1060614 1063651 := bstep (se 1 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 1063651 = 1595477) B1595477
theorem B1915633 : Blo 1060614 1915633 := bstep (se 2 (by rfl) ⟨718362, by rfl⟩ : syracuseStep 1915633 = 1436725) B1436725
theorem B1063667 : Blo 1060614 1063667 := bstep (se 1 (by rfl) ⟨797750, by rfl⟩ : syracuseStep 1063667 = 1595501) B1595501
theorem B1063683 : Blo 1060614 1063683 := bstep (se 1 (by rfl) ⟨797762, by rfl⟩ : syracuseStep 1063683 = 1595525) B1595525
theorem B1063699 : Blo 1060614 1063699 := bstep (se 1 (by rfl) ⟨797774, by rfl⟩ : syracuseStep 1063699 = 1595549) B1595549
theorem B1063715 : Blo 1060614 1063715 := bstep (se 1 (by rfl) ⟨797786, by rfl⟩ : syracuseStep 1063715 = 1595573) B1595573
theorem B5389091 : Blo 1060614 5389091 := bstep (se 1 (by rfl) ⟨4041818, by rfl⟩ : syracuseStep 5389091 = 8083637) B8083637
theorem B1063731 : Blo 1060614 1063731 := bstep (se 1 (by rfl) ⟨797798, by rfl⟩ : syracuseStep 1063731 = 1595597) B1595597
theorem B1063747 : Blo 1060614 1063747 := bstep (se 1 (by rfl) ⟨797810, by rfl⟩ : syracuseStep 1063747 = 1595621) B1595621
theorem B1194835 : Blo 1060614 1194835 := bstep (se 1 (by rfl) ⟨896126, by rfl⟩ : syracuseStep 1194835 = 1792253) B1792253
theorem B1063763 : Blo 1060614 1063763 := bstep (se 1 (by rfl) ⟨797822, by rfl⟩ : syracuseStep 1063763 = 1595645) B1595645
theorem B1063779 : Blo 1060614 1063779 := bstep (se 1 (by rfl) ⟨797834, by rfl⟩ : syracuseStep 1063779 = 1595669) B1595669
theorem B1063795 : Blo 1060614 1063795 := bstep (se 1 (by rfl) ⟨797846, by rfl⟩ : syracuseStep 1063795 = 1595693) B1595693
theorem B1063811 : Blo 1060614 1063811 := bstep (se 1 (by rfl) ⟨797858, by rfl⟩ : syracuseStep 1063811 = 1595717) B1595717
theorem B1063827 : Blo 1060614 1063827 := bstep (se 1 (by rfl) ⟨797870, by rfl⟩ : syracuseStep 1063827 = 1595741) B1595741
theorem B5749667 : Blo 1060614 5749667 := bstep (se 1 (by rfl) ⟨4312250, by rfl⟩ : syracuseStep 5749667 = 8624501) B8624501
theorem B1063843 : Blo 1060614 1063843 := bstep (se 1 (by rfl) ⟨797882, by rfl⟩ : syracuseStep 1063843 = 1595765) B1595765
theorem B1063859 : Blo 1060614 1063859 := bstep (se 1 (by rfl) ⟨797894, by rfl⟩ : syracuseStep 1063859 = 1595789) B1595789
theorem B1063875 : Blo 1060614 1063875 := bstep (se 1 (by rfl) ⟨797906, by rfl⟩ : syracuseStep 1063875 = 1595813) B1595813
theorem B1063891 : Blo 1060614 1063891 := bstep (se 1 (by rfl) ⟨797918, by rfl⟩ : syracuseStep 1063891 = 1595837) B1595837
theorem B1194979 : Blo 1060614 1194979 := bstep (se 1 (by rfl) ⟨896234, by rfl⟩ : syracuseStep 1194979 = 1792469) B1792469
theorem B1063907 : Blo 1060614 1063907 := bstep (se 1 (by rfl) ⟨797930, by rfl⟩ : syracuseStep 1063907 = 1595861) B1595861
theorem B3029987 : Blo 1060614 3029987 := bstep (se 1 (by rfl) ⟨2272490, by rfl⟩ : syracuseStep 3029987 = 4544981) B4544981
theorem B3587057 : Blo 1060614 3587057 := bstep (se 2 (by rfl) ⟨1345146, by rfl⟩ : syracuseStep 3587057 = 2690293) B2690293
theorem B1063923 : Blo 1060614 1063923 := bstep (se 1 (by rfl) ⟨797942, by rfl⟩ : syracuseStep 1063923 = 1595885) B1595885
theorem B1063939 : Blo 1060614 1063939 := bstep (se 1 (by rfl) ⟨797954, by rfl⟩ : syracuseStep 1063939 = 1595909) B1595909
theorem B1063955 : Blo 1060614 1063955 := bstep (se 1 (by rfl) ⟨797966, by rfl⟩ : syracuseStep 1063955 = 1595933) B1595933
theorem B1063971 : Blo 1060614 1063971 := bstep (se 1 (by rfl) ⟨797978, by rfl⟩ : syracuseStep 1063971 = 1595957) B1595957
theorem B1063987 : Blo 1060614 1063987 := bstep (se 1 (by rfl) ⟨797990, by rfl⟩ : syracuseStep 1063987 = 1595981) B1595981
theorem B1064003 : Blo 1060614 1064003 := bstep (se 1 (by rfl) ⟨798002, by rfl⟩ : syracuseStep 1064003 = 1596005) B1596005
theorem B1064019 : Blo 1060614 1064019 := bstep (se 1 (by rfl) ⟨798014, by rfl⟩ : syracuseStep 1064019 = 1596029) B1596029
theorem B1064035 : Blo 1060614 1064035 := bstep (se 1 (by rfl) ⟨798026, by rfl⟩ : syracuseStep 1064035 = 1596053) B1596053
theorem B1195123 : Blo 1060614 1195123 := bstep (se 1 (by rfl) ⟨896342, by rfl⟩ : syracuseStep 1195123 = 1792685) B1792685
theorem B1064051 : Blo 1060614 1064051 := bstep (se 1 (by rfl) ⟨798038, by rfl⟩ : syracuseStep 1064051 = 1596077) B1596077
theorem B1064067 : Blo 1060614 1064067 := bstep (se 1 (by rfl) ⟨798050, by rfl⟩ : syracuseStep 1064067 = 1596101) B1596101
theorem B1064083 : Blo 1060614 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B1064099 : Blo 1060614 1064099 := bstep (se 1 (by rfl) ⟨798074, by rfl⟩ : syracuseStep 1064099 = 1596149) B1596149
theorem B1064115 : Blo 1060614 1064115 := bstep (se 1 (by rfl) ⟨798086, by rfl⟩ : syracuseStep 1064115 = 1596173) B1596173
theorem B1064131 : Blo 1060614 1064131 := bstep (se 1 (by rfl) ⟨798098, by rfl⟩ : syracuseStep 1064131 = 1596197) B1596197
theorem B1064147 : Blo 1060614 1064147 := bstep (se 1 (by rfl) ⟨798110, by rfl⟩ : syracuseStep 1064147 = 1596221) B1596221
theorem B1064163 : Blo 1060614 1064163 := bstep (se 1 (by rfl) ⟨798122, by rfl⟩ : syracuseStep 1064163 = 1596245) B1596245
theorem B1064179 : Blo 1060614 1064179 := bstep (se 1 (by rfl) ⟨798134, by rfl⟩ : syracuseStep 1064179 = 1596269) B1596269
theorem B1195267 : Blo 1060614 1195267 := bstep (se 1 (by rfl) ⟨896450, by rfl⟩ : syracuseStep 1195267 = 1792901) B1792901
theorem B1064195 : Blo 1060614 1064195 := bstep (se 1 (by rfl) ⟨798146, by rfl⟩ : syracuseStep 1064195 = 1596293) B1596293
theorem B1064211 : Blo 1060614 1064211 := bstep (se 1 (by rfl) ⟨798158, by rfl⟩ : syracuseStep 1064211 = 1596317) B1596317
theorem B1817891 : Blo 1060614 1817891 := bstep (se 1 (by rfl) ⟨1363418, by rfl⟩ : syracuseStep 1817891 = 2726837) B2726837
theorem B1064227 : Blo 1060614 1064227 := bstep (se 1 (by rfl) ⟨798170, by rfl⟩ : syracuseStep 1064227 = 1596341) B1596341
theorem B3030317 : Blo 1060614 3030317 := bstep (se 3 (by rfl) ⟨568184, by rfl⟩ : syracuseStep 3030317 = 1136369) B1136369
theorem B1064243 : Blo 1060614 1064243 := bstep (se 1 (by rfl) ⟨798182, by rfl⟩ : syracuseStep 1064243 = 1596365) B1596365
theorem B1064259 : Blo 1060614 1064259 := bstep (se 1 (by rfl) ⟨798194, by rfl⟩ : syracuseStep 1064259 = 1596389) B1596389
theorem B1064275 : Blo 1060614 1064275 := bstep (se 1 (by rfl) ⟨798206, by rfl⟩ : syracuseStep 1064275 = 1596413) B1596413
theorem B1064291 : Blo 1060614 1064291 := bstep (se 1 (by rfl) ⟨798218, by rfl⟩ : syracuseStep 1064291 = 1596437) B1596437
theorem B3030385 : Blo 1060614 3030385 := bstep (se 2 (by rfl) ⟨1136394, by rfl⟩ : syracuseStep 3030385 = 2272789) B2272789
theorem B1064307 : Blo 1060614 1064307 := bstep (se 1 (by rfl) ⟨798230, by rfl⟩ : syracuseStep 1064307 = 1596461) B1596461
theorem B1064323 : Blo 1060614 1064323 := bstep (se 1 (by rfl) ⟨798242, by rfl⟩ : syracuseStep 1064323 = 1596485) B1596485
theorem B1195411 : Blo 1060614 1195411 := bstep (se 1 (by rfl) ⟨896558, by rfl⟩ : syracuseStep 1195411 = 1793117) B1793117
theorem B1064339 : Blo 1060614 1064339 := bstep (se 1 (by rfl) ⟨798254, by rfl⟩ : syracuseStep 1064339 = 1596509) B1596509
theorem B1064355 : Blo 1060614 1064355 := bstep (se 1 (by rfl) ⟨798266, by rfl⟩ : syracuseStep 1064355 = 1596533) B1596533
theorem B1064371 : Blo 1060614 1064371 := bstep (se 1 (by rfl) ⟨798278, by rfl⟩ : syracuseStep 1064371 = 1596557) B1596557
theorem B1064387 : Blo 1060614 1064387 := bstep (se 1 (by rfl) ⟨798290, by rfl⟩ : syracuseStep 1064387 = 1596581) B1596581
theorem B1064403 : Blo 1060614 1064403 := bstep (se 1 (by rfl) ⟨798302, by rfl⟩ : syracuseStep 1064403 = 1596605) B1596605
theorem B1064419 : Blo 1060614 1064419 := bstep (se 1 (by rfl) ⟨798314, by rfl⟩ : syracuseStep 1064419 = 1596629) B1596629
theorem B1064435 : Blo 1060614 1064435 := bstep (se 1 (by rfl) ⟨798326, by rfl⟩ : syracuseStep 1064435 = 1596653) B1596653
theorem B1064451 : Blo 1060614 1064451 := bstep (se 1 (by rfl) ⟨798338, by rfl⟩ : syracuseStep 1064451 = 1596677) B1596677
theorem B3587597 : Blo 1060614 3587597 := bstep (se 3 (by rfl) ⟨672674, by rfl⟩ : syracuseStep 3587597 = 1345349) B1345349
theorem B1064467 : Blo 1060614 1064467 := bstep (se 1 (by rfl) ⟨798350, by rfl⟩ : syracuseStep 1064467 = 1596701) B1596701
theorem B1195555 : Blo 1060614 1195555 := bstep (se 1 (by rfl) ⟨896666, by rfl⟩ : syracuseStep 1195555 = 1793333) B1793333
theorem B1064483 : Blo 1060614 1064483 := bstep (se 1 (by rfl) ⟨798362, by rfl⟩ : syracuseStep 1064483 = 1596725) B1596725
theorem B1064499 : Blo 1060614 1064499 := bstep (se 1 (by rfl) ⟨798374, by rfl⟩ : syracuseStep 1064499 = 1596749) B1596749
theorem B3587651 : Blo 1060614 3587651 := bstep (se 1 (by rfl) ⟨2690738, by rfl⟩ : syracuseStep 3587651 = 5381477) B5381477
theorem B1064515 : Blo 1060614 1064515 := bstep (se 1 (by rfl) ⟨798386, by rfl⟩ : syracuseStep 1064515 = 1596773) B1596773
theorem B1064531 : Blo 1060614 1064531 := bstep (se 1 (by rfl) ⟨798398, by rfl⟩ : syracuseStep 1064531 = 1596797) B1596797
theorem B1064547 : Blo 1060614 1064547 := bstep (se 1 (by rfl) ⟨798410, by rfl⟩ : syracuseStep 1064547 = 1596821) B1596821
theorem B1064563 : Blo 1060614 1064563 := bstep (se 1 (by rfl) ⟨798422, by rfl⟩ : syracuseStep 1064563 = 1596845) B1596845
theorem B3030659 : Blo 1060614 3030659 := bstep (se 1 (by rfl) ⟨2272994, by rfl⟩ : syracuseStep 3030659 = 4545989) B4545989
theorem B1064579 : Blo 1060614 1064579 := bstep (se 1 (by rfl) ⟨798434, by rfl⟩ : syracuseStep 1064579 = 1596869) B1596869
theorem B2014865 : Blo 1060614 2014865 := bstep (se 2 (by rfl) ⟨755574, by rfl⟩ : syracuseStep 2014865 = 1511149) B1511149
theorem B1064595 : Blo 1060614 1064595 := bstep (se 1 (by rfl) ⟨798446, by rfl⟩ : syracuseStep 1064595 = 1596893) B1596893
theorem B1064611 : Blo 1060614 1064611 := bstep (se 1 (by rfl) ⟨798458, by rfl⟩ : syracuseStep 1064611 = 1596917) B1596917
theorem B1195699 : Blo 1060614 1195699 := bstep (se 1 (by rfl) ⟨896774, by rfl⟩ : syracuseStep 1195699 = 1793549) B1793549
theorem B3227377 : Blo 1060614 3227377 := bstep (se 2 (by rfl) ⟨1210266, by rfl⟩ : syracuseStep 3227377 = 2420533) B2420533
theorem B1195843 : Blo 1060614 1195843 := bstep (se 1 (by rfl) ⟨896882, by rfl⟩ : syracuseStep 1195843 = 1793765) B1793765
theorem B3587921 : Blo 1060614 3587921 := bstep (se 2 (by rfl) ⟨1345470, by rfl⟩ : syracuseStep 3587921 = 2690941) B2690941
theorem B6799301 : Blo 1060614 6799301 := bstep (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) B1274869
theorem B1195987 : Blo 1060614 1195987 := bstep (se 1 (by rfl) ⟨896990, by rfl⟩ : syracuseStep 1195987 = 1793981) B1793981
theorem B1196131 : Blo 1060614 1196131 := bstep (se 1 (by rfl) ⟨897098, by rfl⟩ : syracuseStep 1196131 = 1794197) B1794197
theorem B2867309 : Blo 1060614 2867309 := bstep (se 3 (by rfl) ⟨537620, by rfl⟩ : syracuseStep 2867309 = 1075241) B1075241
theorem B2867395 : Blo 1060614 2867395 := bstep (se 1 (by rfl) ⟨2150546, by rfl⟩ : syracuseStep 2867395 = 4301093) B4301093
theorem B1196275 : Blo 1060614 1196275 := bstep (se 1 (by rfl) ⟨897206, by rfl⟩ : syracuseStep 1196275 = 1794413) B1794413
theorem B3588461 : Blo 1060614 3588461 := bstep (se 3 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 3588461 = 1345673) B1345673
theorem B1196419 : Blo 1060614 1196419 := bstep (se 1 (by rfl) ⟨897314, by rfl⟩ : syracuseStep 1196419 = 1794629) B1794629
theorem B3588515 : Blo 1060614 3588515 := bstep (se 1 (by rfl) ⟨2691386, by rfl⟩ : syracuseStep 3588515 = 5382773) B5382773
theorem B3031501 : Blo 1060614 3031501 := bstep (se 3 (by rfl) ⟨568406, by rfl⟩ : syracuseStep 3031501 = 1136813) B1136813
theorem B2015761 : Blo 1060614 2015761 := bstep (se 2 (by rfl) ⟨755910, by rfl⟩ : syracuseStep 2015761 = 1511821) B1511821
theorem B1196563 : Blo 1060614 1196563 := bstep (se 1 (by rfl) ⟨897422, by rfl⟩ : syracuseStep 1196563 = 1794845) B1794845
theorem B4538915 : Blo 1060614 4538915 := bstep (se 1 (by rfl) ⟨3404186, by rfl⟩ : syracuseStep 4538915 = 6808373) B6808373
theorem B13615715 : Blo 1060614 13615715 := bstep (se 1 (by rfl) ⟨10211786, by rfl⟩ : syracuseStep 13615715 = 20423573) B20423573
theorem B1196707 : Blo 1060614 1196707 := bstep (se 1 (by rfl) ⟨897530, by rfl⟩ : syracuseStep 1196707 = 1795061) B1795061
theorem B2015921 : Blo 1060614 2015921 := bstep (se 2 (by rfl) ⟨755970, by rfl⟩ : syracuseStep 2015921 = 1511941) B1511941
theorem B3588785 : Blo 1060614 3588785 := bstep (se 2 (by rfl) ⟨1345794, by rfl⟩ : syracuseStep 3588785 = 2691589) B2691589
theorem B1819409 : Blo 1060614 1819409 := bstep (se 2 (by rfl) ⟨682278, by rfl⟩ : syracuseStep 1819409 = 1364557) B1364557
theorem B1196851 : Blo 1060614 1196851 := bstep (se 1 (by rfl) ⟨897638, by rfl⟩ : syracuseStep 1196851 = 1795277) B1795277
theorem B1196995 : Blo 1060614 1196995 := bstep (se 1 (by rfl) ⟨897746, by rfl⟩ : syracuseStep 1196995 = 1795493) B1795493
theorem B2180081 : Blo 1060614 2180081 := bstep (se 2 (by rfl) ⟨817530, by rfl⟩ : syracuseStep 2180081 = 1635061) B1635061
theorem B2016323 : Blo 1060614 2016323 := bstep (se 1 (by rfl) ⟨1512242, by rfl⟩ : syracuseStep 2016323 = 3024485) B3024485
theorem B1197139 : Blo 1060614 1197139 := bstep (se 1 (by rfl) ⟨897854, by rfl⟩ : syracuseStep 1197139 = 1795709) B1795709
theorem B14566499 : Blo 1060614 14566499 := bstep (se 1 (by rfl) ⟨10924874, by rfl⟩ : syracuseStep 14566499 = 21849749) B21849749
theorem B10208369 : Blo 1060614 10208369 := bstep (se 2 (by rfl) ⟨3828138, by rfl⟩ : syracuseStep 10208369 = 7656277) B7656277
theorem B3589325 : Blo 1060614 3589325 := bstep (se 3 (by rfl) ⟨672998, by rfl⟩ : syracuseStep 3589325 = 1345997) B1345997
theorem B46613717 : Blo 1060614 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B1197283 : Blo 1060614 1197283 := bstep (se 1 (by rfl) ⟨897962, by rfl⟩ : syracuseStep 1197283 = 1795925) B1795925
theorem B3589379 : Blo 1060614 3589379 := bstep (se 1 (by rfl) ⟨2692034, by rfl⟩ : syracuseStep 3589379 = 5384069) B5384069
theorem B1197427 : Blo 1060614 1197427 := bstep (se 1 (by rfl) ⟨898070, by rfl⟩ : syracuseStep 1197427 = 1796141) B1796141
theorem B1197571 : Blo 1060614 1197571 := bstep (se 1 (by rfl) ⟨898178, by rfl⟩ : syracuseStep 1197571 = 1796357) B1796357
theorem B6047237 : Blo 1060614 6047237 := bstep (se 4 (by rfl) ⟨566928, by rfl⟩ : syracuseStep 6047237 = 1133857) B1133857
theorem B3589649 : Blo 1060614 3589649 := bstep (se 2 (by rfl) ⟨1346118, by rfl⟩ : syracuseStep 3589649 = 2692237) B2692237
theorem B1590929 : Blo 1060614 1590929 := bstep (se 2 (by rfl) ⟨596598, by rfl⟩ : syracuseStep 1590929 = 1193197) B1193197
theorem B1820321 : Blo 1060614 1820321 := bstep (se 2 (by rfl) ⟨682620, by rfl⟩ : syracuseStep 1820321 = 1365241) B1365241
theorem B1590947 : Blo 1060614 1590947 := bstep (se 1 (by rfl) ⟨1193210, by rfl⟩ : syracuseStep 1590947 = 2386421) B2386421
theorem B1590977 : Blo 1060614 1590977 := bstep (se 2 (by rfl) ⟨596616, by rfl⟩ : syracuseStep 1590977 = 1193233) B1193233
theorem B5457613 : Blo 1060614 5457613 := bstep (se 3 (by rfl) ⟨1023302, by rfl⟩ : syracuseStep 5457613 = 2046605) B2046605
theorem B1590995 : Blo 1060614 1590995 := bstep (se 1 (by rfl) ⟨1193246, by rfl⟩ : syracuseStep 1590995 = 2386493) B2386493
theorem B1591025 : Blo 1060614 1591025 := bstep (se 2 (by rfl) ⟨596634, by rfl⟩ : syracuseStep 1591025 = 1193269) B1193269
theorem B1591043 : Blo 1060614 1591043 := bstep (se 1 (by rfl) ⟨1193282, by rfl⟩ : syracuseStep 1591043 = 2386565) B2386565
theorem B7653133 : Blo 1060614 7653133 := bstep (se 3 (by rfl) ⟨1434962, by rfl⟩ : syracuseStep 7653133 = 2869925) B2869925
theorem B1591073 : Blo 1060614 1591073 := bstep (se 2 (by rfl) ⟨596652, by rfl⟩ : syracuseStep 1591073 = 1193305) B1193305
theorem B1591091 : Blo 1060614 1591091 := bstep (se 1 (by rfl) ⟨1193318, by rfl⟩ : syracuseStep 1591091 = 2386637) B2386637
theorem B3229517 : Blo 1060614 3229517 := bstep (se 3 (by rfl) ⟨605534, by rfl⟩ : syracuseStep 3229517 = 1211069) B1211069
theorem B1591121 : Blo 1060614 1591121 := bstep (se 2 (by rfl) ⟨596670, by rfl⟩ : syracuseStep 1591121 = 1193341) B1193341
theorem B1591139 : Blo 1060614 1591139 := bstep (se 1 (by rfl) ⟨1193354, by rfl⟩ : syracuseStep 1591139 = 2386709) B2386709
theorem B1591169 : Blo 1060614 1591169 := bstep (se 2 (by rfl) ⟨596688, by rfl⟩ : syracuseStep 1591169 = 1193377) B1193377
theorem B1591187 : Blo 1060614 1591187 := bstep (se 1 (by rfl) ⟨1193390, by rfl⟩ : syracuseStep 1591187 = 2386781) B2386781
theorem B1591217 : Blo 1060614 1591217 := bstep (se 2 (by rfl) ⟨596706, by rfl⟩ : syracuseStep 1591217 = 1193413) B1193413
theorem B1591235 : Blo 1060614 1591235 := bstep (se 1 (by rfl) ⟨1193426, by rfl⟩ : syracuseStep 1591235 = 2386853) B2386853
theorem B2017219 : Blo 1060614 2017219 := bstep (se 1 (by rfl) ⟨1512914, by rfl⟩ : syracuseStep 2017219 = 3025829) B3025829
theorem B6047693 : Blo 1060614 6047693 := bstep (se 3 (by rfl) ⟨1133942, by rfl⟩ : syracuseStep 6047693 = 2267885) B2267885
theorem B1591265 : Blo 1060614 1591265 := bstep (se 2 (by rfl) ⟨596724, by rfl⟩ : syracuseStep 1591265 = 1193449) B1193449
theorem B1591283 : Blo 1060614 1591283 := bstep (se 1 (by rfl) ⟨1193462, by rfl⟩ : syracuseStep 1591283 = 2386925) B2386925
theorem B1591313 : Blo 1060614 1591313 := bstep (se 2 (by rfl) ⟨596742, by rfl⟩ : syracuseStep 1591313 = 1193485) B1193485
theorem B1591331 : Blo 1060614 1591331 := bstep (se 1 (by rfl) ⟨1193498, by rfl⟩ : syracuseStep 1591331 = 2386997) B2386997
theorem B3590189 : Blo 1060614 3590189 := bstep (se 3 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 3590189 = 1346321) B1346321
theorem B1591361 : Blo 1060614 1591361 := bstep (se 2 (by rfl) ⟨596760, by rfl⟩ : syracuseStep 1591361 = 1193521) B1193521
theorem B1132627 : Blo 1060614 1132627 := bstep (se 1 (by rfl) ⟨849470, by rfl⟩ : syracuseStep 1132627 = 1698941) B1698941
theorem B1591379 : Blo 1060614 1591379 := bstep (se 1 (by rfl) ⟨1193534, by rfl⟩ : syracuseStep 1591379 = 2387069) B2387069
theorem B2017379 : Blo 1060614 2017379 := bstep (se 1 (by rfl) ⟨1513034, by rfl⟩ : syracuseStep 2017379 = 3026069) B3026069
theorem B3590243 : Blo 1060614 3590243 := bstep (se 1 (by rfl) ⟨2692682, by rfl⟩ : syracuseStep 3590243 = 5385365) B5385365
theorem B1591409 : Blo 1060614 1591409 := bstep (se 2 (by rfl) ⟨596778, by rfl⟩ : syracuseStep 1591409 = 1193557) B1193557
theorem B1591427 : Blo 1060614 1591427 := bstep (se 1 (by rfl) ⟨1193570, by rfl⟩ : syracuseStep 1591427 = 2387141) B2387141
theorem B1820819 : Blo 1060614 1820819 := bstep (se 1 (by rfl) ⟨1365614, by rfl⟩ : syracuseStep 1820819 = 2731229) B2731229
theorem B1591457 : Blo 1060614 1591457 := bstep (se 2 (by rfl) ⟨596796, by rfl⟩ : syracuseStep 1591457 = 1193593) B1193593
theorem B1591475 : Blo 1060614 1591475 := bstep (se 1 (by rfl) ⟨1193606, by rfl⟩ : syracuseStep 1591475 = 2387213) B2387213
theorem B1591505 : Blo 1060614 1591505 := bstep (se 2 (by rfl) ⟨596814, by rfl⟩ : syracuseStep 1591505 = 1193629) B1193629
theorem B1263827 : Blo 1060614 1263827 := bstep (se 1 (by rfl) ⟨947870, by rfl⟩ : syracuseStep 1263827 = 1895741) B1895741
theorem B1591523 : Blo 1060614 1591523 := bstep (se 1 (by rfl) ⟨1193642, by rfl⟩ : syracuseStep 1591523 = 2387285) B2387285
theorem B4540657 : Blo 1060614 4540657 := bstep (se 2 (by rfl) ⟨1702746, by rfl⟩ : syracuseStep 4540657 = 3405493) B3405493
theorem B1591553 : Blo 1060614 1591553 := bstep (se 2 (by rfl) ⟨596832, by rfl⟩ : syracuseStep 1591553 = 1193665) B1193665
theorem B1591571 : Blo 1060614 1591571 := bstep (se 1 (by rfl) ⟨1193678, by rfl⟩ : syracuseStep 1591571 = 2387357) B2387357
theorem B1591601 : Blo 1060614 1591601 := bstep (se 2 (by rfl) ⟨596850, by rfl⟩ : syracuseStep 1591601 = 1193701) B1193701
theorem B1591619 : Blo 1060614 1591619 := bstep (se 1 (by rfl) ⟨1193714, by rfl⟩ : syracuseStep 1591619 = 2387429) B2387429
theorem B1591649 : Blo 1060614 1591649 := bstep (se 2 (by rfl) ⟨596868, by rfl⟩ : syracuseStep 1591649 = 1193737) B1193737
theorem B10209635 : Blo 1060614 10209635 := bstep (se 1 (by rfl) ⟨7657226, by rfl⟩ : syracuseStep 10209635 = 15314453) B15314453
theorem B3590513 : Blo 1060614 3590513 := bstep (se 2 (by rfl) ⟨1346442, by rfl⟩ : syracuseStep 3590513 = 2692885) B2692885
theorem B1591667 : Blo 1060614 1591667 := bstep (se 1 (by rfl) ⟨1193750, by rfl⟩ : syracuseStep 1591667 = 2387501) B2387501
theorem B1591697 : Blo 1060614 1591697 := bstep (se 2 (by rfl) ⟨596886, by rfl⟩ : syracuseStep 1591697 = 1193773) B1193773
theorem B1591715 : Blo 1060614 1591715 := bstep (se 1 (by rfl) ⟨1193786, by rfl⟩ : syracuseStep 1591715 = 2387573) B2387573
theorem B1591745 : Blo 1060614 1591745 := bstep (se 2 (by rfl) ⟨596904, by rfl⟩ : syracuseStep 1591745 = 1193809) B1193809
theorem B1591763 : Blo 1060614 1591763 := bstep (se 1 (by rfl) ⟨1193822, by rfl⟩ : syracuseStep 1591763 = 2387645) B2387645
theorem B1591793 : Blo 1060614 1591793 := bstep (se 2 (by rfl) ⟨596922, by rfl⟩ : syracuseStep 1591793 = 1193845) B1193845
theorem B1591811 : Blo 1060614 1591811 := bstep (se 1 (by rfl) ⟨1193858, by rfl⟩ : syracuseStep 1591811 = 2387717) B2387717
theorem B1591841 : Blo 1060614 1591841 := bstep (se 2 (by rfl) ⟨596940, by rfl⟩ : syracuseStep 1591841 = 1193881) B1193881
theorem B1591859 : Blo 1060614 1591859 := bstep (se 1 (by rfl) ⟨1193894, by rfl⟩ : syracuseStep 1591859 = 2387789) B2387789
theorem B1591889 : Blo 1060614 1591889 := bstep (se 2 (by rfl) ⟨596958, by rfl⟩ : syracuseStep 1591889 = 1193917) B1193917
theorem B1591907 : Blo 1060614 1591907 := bstep (se 1 (by rfl) ⟨1193930, by rfl⟩ : syracuseStep 1591907 = 2387861) B2387861
theorem B1591937 : Blo 1060614 1591937 := bstep (se 2 (by rfl) ⟨596976, by rfl⟩ : syracuseStep 1591937 = 1193953) B1193953
theorem B1591955 : Blo 1060614 1591955 := bstep (se 1 (by rfl) ⟨1193966, by rfl⟩ : syracuseStep 1591955 = 2387933) B2387933
theorem B1591985 : Blo 1060614 1591985 := bstep (se 2 (by rfl) ⟨596994, by rfl⟩ : syracuseStep 1591985 = 1193989) B1193989
theorem B1592003 : Blo 1060614 1592003 := bstep (se 1 (by rfl) ⟨1194002, by rfl⟩ : syracuseStep 1592003 = 2388005) B2388005
theorem B1592033 : Blo 1060614 1592033 := bstep (se 2 (by rfl) ⟨597012, by rfl⟩ : syracuseStep 1592033 = 1194025) B1194025
theorem B1592051 : Blo 1060614 1592051 := bstep (se 1 (by rfl) ⟨1194038, by rfl⟩ : syracuseStep 1592051 = 2388077) B2388077
theorem B4606733 : Blo 1060614 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B1592081 : Blo 1060614 1592081 := bstep (se 2 (by rfl) ⟨597030, by rfl⟩ : syracuseStep 1592081 = 1194061) B1194061
theorem B1592099 : Blo 1060614 1592099 := bstep (se 1 (by rfl) ⟨1194074, by rfl⟩ : syracuseStep 1592099 = 2388149) B2388149
theorem B1592129 : Blo 1060614 1592129 := bstep (se 2 (by rfl) ⟨597048, by rfl⟩ : syracuseStep 1592129 = 1194097) B1194097
theorem B1592147 : Blo 1060614 1592147 := bstep (se 1 (by rfl) ⟨1194110, by rfl⟩ : syracuseStep 1592147 = 2388221) B2388221
theorem B1592177 : Blo 1060614 1592177 := bstep (se 2 (by rfl) ⟨597066, by rfl⟩ : syracuseStep 1592177 = 1194133) B1194133
theorem B1133443 : Blo 1060614 1133443 := bstep (se 1 (by rfl) ⟨850082, by rfl⟩ : syracuseStep 1133443 = 1700165) B1700165
theorem B1592195 : Blo 1060614 1592195 := bstep (se 1 (by rfl) ⟨1194146, by rfl⟩ : syracuseStep 1592195 = 2388293) B2388293
theorem B3591053 : Blo 1060614 3591053 := bstep (se 3 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 3591053 = 1346645) B1346645
theorem B1592225 : Blo 1060614 1592225 := bstep (se 2 (by rfl) ⟨597084, by rfl⟩ : syracuseStep 1592225 = 1194169) B1194169
theorem B1592243 : Blo 1060614 1592243 := bstep (se 1 (by rfl) ⟨1194182, by rfl⟩ : syracuseStep 1592243 = 2388365) B2388365
theorem B3591107 : Blo 1060614 3591107 := bstep (se 1 (by rfl) ⟨2693330, by rfl⟩ : syracuseStep 3591107 = 5386661) B5386661
theorem B1592273 : Blo 1060614 1592273 := bstep (se 2 (by rfl) ⟨597102, by rfl⟩ : syracuseStep 1592273 = 1194205) B1194205
theorem B1592291 : Blo 1060614 1592291 := bstep (se 1 (by rfl) ⟨1194218, by rfl⟩ : syracuseStep 1592291 = 2388437) B2388437
theorem B1592321 : Blo 1060614 1592321 := bstep (se 2 (by rfl) ⟨597120, by rfl⟩ : syracuseStep 1592321 = 1194241) B1194241
theorem B1592339 : Blo 1060614 1592339 := bstep (se 1 (by rfl) ⟨1194254, by rfl⟩ : syracuseStep 1592339 = 2388509) B2388509
theorem B1592369 : Blo 1060614 1592369 := bstep (se 2 (by rfl) ⟨597138, by rfl⟩ : syracuseStep 1592369 = 1194277) B1194277
theorem B1592387 : Blo 1060614 1592387 := bstep (se 1 (by rfl) ⟨1194290, by rfl⟩ : syracuseStep 1592387 = 2388581) B2388581
theorem B1592417 : Blo 1060614 1592417 := bstep (se 2 (by rfl) ⟨597156, by rfl⟩ : syracuseStep 1592417 = 1194313) B1194313
theorem B1592435 : Blo 1060614 1592435 := bstep (se 1 (by rfl) ⟨1194326, by rfl⟩ : syracuseStep 1592435 = 2388653) B2388653
theorem B1592465 : Blo 1060614 1592465 := bstep (se 2 (by rfl) ⟨597174, by rfl⟩ : syracuseStep 1592465 = 1194349) B1194349
theorem B2018449 : Blo 1060614 2018449 := bstep (se 2 (by rfl) ⟨756918, by rfl⟩ : syracuseStep 2018449 = 1513837) B1513837
theorem B1592483 : Blo 1060614 1592483 := bstep (se 1 (by rfl) ⟨1194362, by rfl⟩ : syracuseStep 1592483 = 2388725) B2388725
theorem B1592513 : Blo 1060614 1592513 := bstep (se 2 (by rfl) ⟨597192, by rfl⟩ : syracuseStep 1592513 = 1194385) B1194385
theorem B3591377 : Blo 1060614 3591377 := bstep (se 2 (by rfl) ⟨1346766, by rfl⟩ : syracuseStep 3591377 = 2693533) B2693533
theorem B1592531 : Blo 1060614 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B1592561 : Blo 1060614 1592561 := bstep (se 2 (by rfl) ⟨597210, by rfl⟩ : syracuseStep 1592561 = 1194421) B1194421
theorem B1592579 : Blo 1060614 1592579 := bstep (se 1 (by rfl) ⟨1194434, by rfl⟩ : syracuseStep 1592579 = 2388869) B2388869
theorem B1592609 : Blo 1060614 1592609 := bstep (se 2 (by rfl) ⟨597228, by rfl⟩ : syracuseStep 1592609 = 1194457) B1194457
theorem B1592627 : Blo 1060614 1592627 := bstep (se 1 (by rfl) ⟨1194470, by rfl⟩ : syracuseStep 1592627 = 2388941) B2388941
theorem B1592657 : Blo 1060614 1592657 := bstep (se 2 (by rfl) ⟨597246, by rfl⟩ : syracuseStep 1592657 = 1194493) B1194493
theorem B1592675 : Blo 1060614 1592675 := bstep (se 1 (by rfl) ⟨1194506, by rfl⟩ : syracuseStep 1592675 = 2389013) B2389013
theorem B1592705 : Blo 1060614 1592705 := bstep (se 2 (by rfl) ⟨597264, by rfl⟩ : syracuseStep 1592705 = 1194529) B1194529
theorem B1592723 : Blo 1060614 1592723 := bstep (se 1 (by rfl) ⟨1194542, by rfl⟩ : syracuseStep 1592723 = 2389085) B2389085
theorem B1592753 : Blo 1060614 1592753 := bstep (se 2 (by rfl) ⟨597282, by rfl⟩ : syracuseStep 1592753 = 1194565) B1194565
theorem B1592771 : Blo 1060614 1592771 := bstep (se 1 (by rfl) ⟨1194578, by rfl⟩ : syracuseStep 1592771 = 2389157) B2389157
theorem B1592801 : Blo 1060614 1592801 := bstep (se 2 (by rfl) ⟨597300, by rfl⟩ : syracuseStep 1592801 = 1194601) B1194601
theorem B1592819 : Blo 1060614 1592819 := bstep (se 1 (by rfl) ⟨1194614, by rfl⟩ : syracuseStep 1592819 = 2389229) B2389229
theorem B1592849 : Blo 1060614 1592849 := bstep (se 2 (by rfl) ⟨597318, by rfl⟩ : syracuseStep 1592849 = 1194637) B1194637
theorem B1592867 : Blo 1060614 1592867 := bstep (se 1 (by rfl) ⟨1194650, by rfl⟩ : syracuseStep 1592867 = 2389301) B2389301
theorem B1592897 : Blo 1060614 1592897 := bstep (se 2 (by rfl) ⟨597336, by rfl⟩ : syracuseStep 1592897 = 1194673) B1194673
theorem B1592915 : Blo 1060614 1592915 := bstep (se 1 (by rfl) ⟨1194686, by rfl⟩ : syracuseStep 1592915 = 2389373) B2389373
theorem B1592945 : Blo 1060614 1592945 := bstep (se 2 (by rfl) ⟨597354, by rfl⟩ : syracuseStep 1592945 = 1194709) B1194709
theorem B1592963 : Blo 1060614 1592963 := bstep (se 1 (by rfl) ⟨1194722, by rfl⟩ : syracuseStep 1592963 = 2389445) B2389445
theorem B1592993 : Blo 1060614 1592993 := bstep (se 2 (by rfl) ⟨597372, by rfl⟩ : syracuseStep 1592993 = 1194745) B1194745
theorem B1593011 : Blo 1060614 1593011 := bstep (se 1 (by rfl) ⟨1194758, by rfl⟩ : syracuseStep 1593011 = 2389517) B2389517
theorem B1593041 : Blo 1060614 1593041 := bstep (se 2 (by rfl) ⟨597390, by rfl⟩ : syracuseStep 1593041 = 1194781) B1194781
theorem B1593059 : Blo 1060614 1593059 := bstep (se 1 (by rfl) ⟨1194794, by rfl⟩ : syracuseStep 1593059 = 2389589) B2389589
theorem B3591917 : Blo 1060614 3591917 := bstep (se 3 (by rfl) ⟨673484, by rfl⟩ : syracuseStep 3591917 = 1346969) B1346969
theorem B1724147 : Blo 1060614 1724147 := bstep (se 1 (by rfl) ⟨1293110, by rfl⟩ : syracuseStep 1724147 = 2586221) B2586221
theorem B1593089 : Blo 1060614 1593089 := bstep (se 2 (by rfl) ⟨597408, by rfl⟩ : syracuseStep 1593089 = 1194817) B1194817
theorem B1593107 : Blo 1060614 1593107 := bstep (se 1 (by rfl) ⟨1194830, by rfl⟩ : syracuseStep 1593107 = 2389661) B2389661
theorem B3591971 : Blo 1060614 3591971 := bstep (se 1 (by rfl) ⟨2693978, by rfl⟩ : syracuseStep 3591971 = 5387957) B5387957
theorem B1593137 : Blo 1060614 1593137 := bstep (se 2 (by rfl) ⟨597426, by rfl⟩ : syracuseStep 1593137 = 1194853) B1194853
theorem B1593155 : Blo 1060614 1593155 := bstep (se 1 (by rfl) ⟨1194866, by rfl⟩ : syracuseStep 1593155 = 2389733) B2389733
theorem B1593185 : Blo 1060614 1593185 := bstep (se 2 (by rfl) ⟨597444, by rfl⟩ : syracuseStep 1593185 = 1194889) B1194889
theorem B1593203 : Blo 1060614 1593203 := bstep (se 1 (by rfl) ⟨1194902, by rfl⟩ : syracuseStep 1593203 = 2389805) B2389805
theorem B1593233 : Blo 1060614 1593233 := bstep (se 2 (by rfl) ⟨597462, by rfl⟩ : syracuseStep 1593233 = 1194925) B1194925
theorem B1789843 : Blo 1060614 1789843 := bstep (se 1 (by rfl) ⟨1342382, by rfl⟩ : syracuseStep 1789843 = 2684765) B2684765
theorem B1593251 : Blo 1060614 1593251 := bstep (se 1 (by rfl) ⟨1194938, by rfl⟩ : syracuseStep 1593251 = 2389877) B2389877
theorem B1593281 : Blo 1060614 1593281 := bstep (se 2 (by rfl) ⟨597480, by rfl⟩ : syracuseStep 1593281 = 1194961) B1194961
theorem B1593299 : Blo 1060614 1593299 := bstep (se 1 (by rfl) ⟨1194974, by rfl⟩ : syracuseStep 1593299 = 2389949) B2389949
theorem B1593329 : Blo 1060614 1593329 := bstep (se 2 (by rfl) ⟨597498, by rfl⟩ : syracuseStep 1593329 = 1194997) B1194997
theorem B1593347 : Blo 1060614 1593347 := bstep (se 1 (by rfl) ⟨1195010, by rfl⟩ : syracuseStep 1593347 = 2390021) B2390021
theorem B1789985 : Blo 1060614 1789985 := bstep (se 2 (by rfl) ⟨671244, by rfl⟩ : syracuseStep 1789985 = 1342489) B1342489
theorem B1593377 : Blo 1060614 1593377 := bstep (se 2 (by rfl) ⟨597516, by rfl⟩ : syracuseStep 1593377 = 1195033) B1195033
theorem B3592241 : Blo 1060614 3592241 := bstep (se 2 (by rfl) ⟨1347090, by rfl⟩ : syracuseStep 3592241 = 2694181) B2694181
theorem B1593395 : Blo 1060614 1593395 := bstep (se 1 (by rfl) ⟨1195046, by rfl⟩ : syracuseStep 1593395 = 2390093) B2390093
theorem B1593425 : Blo 1060614 1593425 := bstep (se 2 (by rfl) ⟨597534, by rfl⟩ : syracuseStep 1593425 = 1195069) B1195069
theorem B1593443 : Blo 1060614 1593443 := bstep (se 1 (by rfl) ⟨1195082, by rfl⟩ : syracuseStep 1593443 = 2390165) B2390165
theorem B1593473 : Blo 1060614 1593473 := bstep (se 2 (by rfl) ⟨597552, by rfl⟩ : syracuseStep 1593473 = 1195105) B1195105
theorem B4542605 : Blo 1060614 4542605 := bstep (se 3 (by rfl) ⟨851738, by rfl⟩ : syracuseStep 4542605 = 1703477) B1703477
theorem B1593491 : Blo 1060614 1593491 := bstep (se 1 (by rfl) ⟨1195118, by rfl⟩ : syracuseStep 1593491 = 2390237) B2390237
theorem B1790113 : Blo 1060614 1790113 := bstep (se 2 (by rfl) ⟨671292, by rfl⟩ : syracuseStep 1790113 = 1342585) B1342585
theorem B1593521 : Blo 1060614 1593521 := bstep (se 2 (by rfl) ⟨597570, by rfl⟩ : syracuseStep 1593521 = 1195141) B1195141
theorem B2019505 : Blo 1060614 2019505 := bstep (se 2 (by rfl) ⟨757314, by rfl⟩ : syracuseStep 2019505 = 1514629) B1514629
theorem B1790147 : Blo 1060614 1790147 := bstep (se 1 (by rfl) ⟨1342610, by rfl⟩ : syracuseStep 1790147 = 2685221) B2685221
theorem B1593539 : Blo 1060614 1593539 := bstep (se 1 (by rfl) ⟨1195154, by rfl⟩ : syracuseStep 1593539 = 2390309) B2390309
theorem B1593569 : Blo 1060614 1593569 := bstep (se 2 (by rfl) ⟨597588, by rfl⟩ : syracuseStep 1593569 = 1195177) B1195177
theorem B1593587 : Blo 1060614 1593587 := bstep (se 1 (by rfl) ⟨1195190, by rfl⟩ : syracuseStep 1593587 = 2390381) B2390381
theorem B1593617 : Blo 1060614 1593617 := bstep (se 2 (by rfl) ⟨597606, by rfl⟩ : syracuseStep 1593617 = 1195213) B1195213
theorem B1593635 : Blo 1060614 1593635 := bstep (se 1 (by rfl) ⟨1195226, by rfl⟩ : syracuseStep 1593635 = 2390453) B2390453
theorem B1593665 : Blo 1060614 1593665 := bstep (se 2 (by rfl) ⟨597624, by rfl⟩ : syracuseStep 1593665 = 1195249) B1195249
theorem B1790275 : Blo 1060614 1790275 := bstep (se 1 (by rfl) ⟨1342706, by rfl⟩ : syracuseStep 1790275 = 2685413) B2685413
theorem B1593683 : Blo 1060614 1593683 := bstep (se 1 (by rfl) ⟨1195262, by rfl⟩ : syracuseStep 1593683 = 2390525) B2390525
theorem B1593713 : Blo 1060614 1593713 := bstep (se 2 (by rfl) ⟨597642, by rfl⟩ : syracuseStep 1593713 = 1195285) B1195285
theorem B1593731 : Blo 1060614 1593731 := bstep (se 1 (by rfl) ⟨1195298, by rfl⟩ : syracuseStep 1593731 = 2390597) B2390597
theorem B1593761 : Blo 1060614 1593761 := bstep (se 2 (by rfl) ⟨597660, by rfl⟩ : syracuseStep 1593761 = 1195321) B1195321
theorem B1593779 : Blo 1060614 1593779 := bstep (se 1 (by rfl) ⟨1195334, by rfl⟩ : syracuseStep 1593779 = 2390669) B2390669
theorem B1790417 : Blo 1060614 1790417 := bstep (se 2 (by rfl) ⟨671406, by rfl⟩ : syracuseStep 1790417 = 1342813) B1342813
theorem B1593809 : Blo 1060614 1593809 := bstep (se 2 (by rfl) ⟨597678, by rfl⟩ : syracuseStep 1593809 = 1195357) B1195357
theorem B6803939 : Blo 1060614 6803939 := bstep (se 1 (by rfl) ⟨5102954, by rfl⟩ : syracuseStep 6803939 = 10205909) B10205909
theorem B1593827 : Blo 1060614 1593827 := bstep (se 1 (by rfl) ⟨1195370, by rfl⟩ : syracuseStep 1593827 = 2390741) B2390741
theorem B1593857 : Blo 1060614 1593857 := bstep (se 2 (by rfl) ⟨597696, by rfl⟩ : syracuseStep 1593857 = 1195393) B1195393
theorem B1593875 : Blo 1060614 1593875 := bstep (se 1 (by rfl) ⟨1195406, by rfl⟩ : syracuseStep 1593875 = 2390813) B2390813
theorem B1593905 : Blo 1060614 1593905 := bstep (se 2 (by rfl) ⟨597714, by rfl⟩ : syracuseStep 1593905 = 1195429) B1195429
theorem B5460529 : Blo 1060614 5460529 := bstep (se 2 (by rfl) ⟨2047698, by rfl⟩ : syracuseStep 5460529 = 4095397) B4095397
theorem B1593923 : Blo 1060614 1593923 := bstep (se 1 (by rfl) ⟨1195442, by rfl⟩ : syracuseStep 1593923 = 2390885) B2390885
theorem B2019907 : Blo 1060614 2019907 := bstep (se 1 (by rfl) ⟨1514930, by rfl⟩ : syracuseStep 2019907 = 3029861) B3029861
theorem B3592781 : Blo 1060614 3592781 := bstep (se 3 (by rfl) ⟨673646, by rfl⟩ : syracuseStep 3592781 = 1347293) B1347293
theorem B1790545 : Blo 1060614 1790545 := bstep (se 2 (by rfl) ⟨671454, by rfl⟩ : syracuseStep 1790545 = 1342909) B1342909
theorem B1593953 : Blo 1060614 1593953 := bstep (se 2 (by rfl) ⟨597732, by rfl⟩ : syracuseStep 1593953 = 1195465) B1195465
theorem B2019953 : Blo 1060614 2019953 := bstep (se 2 (by rfl) ⟨757482, by rfl⟩ : syracuseStep 2019953 = 1514965) B1514965
theorem B1790579 : Blo 1060614 1790579 := bstep (se 1 (by rfl) ⟨1342934, by rfl⟩ : syracuseStep 1790579 = 2685869) B2685869
theorem B1593971 : Blo 1060614 1593971 := bstep (se 1 (by rfl) ⟨1195478, by rfl⟩ : syracuseStep 1593971 = 2390957) B2390957
theorem B3592835 : Blo 1060614 3592835 := bstep (se 1 (by rfl) ⟨2694626, by rfl⟩ : syracuseStep 3592835 = 5389253) B5389253
theorem B1594001 : Blo 1060614 1594001 := bstep (se 2 (by rfl) ⟨597750, by rfl⟩ : syracuseStep 1594001 = 1195501) B1195501
theorem B1594019 : Blo 1060614 1594019 := bstep (se 1 (by rfl) ⟨1195514, by rfl⟩ : syracuseStep 1594019 = 2391029) B2391029
theorem B1594049 : Blo 1060614 1594049 := bstep (se 2 (by rfl) ⟨597768, by rfl⟩ : syracuseStep 1594049 = 1195537) B1195537
theorem B1594067 : Blo 1060614 1594067 := bstep (se 1 (by rfl) ⟨1195550, by rfl⟩ : syracuseStep 1594067 = 2391101) B2391101
theorem B1594097 : Blo 1060614 1594097 := bstep (se 2 (by rfl) ⟨597786, by rfl⟩ : syracuseStep 1594097 = 1195573) B1195573
theorem B1790707 : Blo 1060614 1790707 := bstep (se 1 (by rfl) ⟨1343030, by rfl⟩ : syracuseStep 1790707 = 2686061) B2686061
theorem B1594115 : Blo 1060614 1594115 := bstep (se 1 (by rfl) ⟨1195586, by rfl⟩ : syracuseStep 1594115 = 2391173) B2391173
theorem B1594145 : Blo 1060614 1594145 := bstep (se 2 (by rfl) ⟨597804, by rfl⟩ : syracuseStep 1594145 = 1195609) B1195609
theorem B6050609 : Blo 1060614 6050609 := bstep (se 2 (by rfl) ⟨2268978, by rfl⟩ : syracuseStep 6050609 = 4537957) B4537957
theorem B1594163 : Blo 1060614 1594163 := bstep (se 1 (by rfl) ⟨1195622, by rfl⟩ : syracuseStep 1594163 = 2391245) B2391245
theorem B1594193 : Blo 1060614 1594193 := bstep (se 2 (by rfl) ⟨597822, by rfl⟩ : syracuseStep 1594193 = 1195645) B1195645
theorem B1594211 : Blo 1060614 1594211 := bstep (se 1 (by rfl) ⟨1195658, by rfl⟩ : syracuseStep 1594211 = 2391317) B2391317
theorem B1790849 : Blo 1060614 1790849 := bstep (se 2 (by rfl) ⟨671568, by rfl⟩ : syracuseStep 1790849 = 1343137) B1343137
theorem B1594241 : Blo 1060614 1594241 := bstep (se 2 (by rfl) ⟨597840, by rfl⟩ : syracuseStep 1594241 = 1195681) B1195681
theorem B9065357 : Blo 1060614 9065357 := bstep (se 3 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 9065357 = 3399509) B3399509
theorem B2020241 : Blo 1060614 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B1594259 : Blo 1060614 1594259 := bstep (se 1 (by rfl) ⟨1195694, by rfl⟩ : syracuseStep 1594259 = 2391389) B2391389
theorem B1594289 : Blo 1060614 1594289 := bstep (se 2 (by rfl) ⟨597858, by rfl⟩ : syracuseStep 1594289 = 1195717) B1195717
theorem B1594307 : Blo 1060614 1594307 := bstep (se 1 (by rfl) ⟨1195730, by rfl⟩ : syracuseStep 1594307 = 2391461) B2391461
theorem B1594337 : Blo 1060614 1594337 := bstep (se 2 (by rfl) ⟨597876, by rfl⟩ : syracuseStep 1594337 = 1195753) B1195753
theorem B12932081 : Blo 1060614 12932081 := bstep (se 2 (by rfl) ⟨4849530, by rfl⟩ : syracuseStep 12932081 = 9699061) B9699061
theorem B1594355 : Blo 1060614 1594355 := bstep (se 1 (by rfl) ⟨1195766, by rfl⟩ : syracuseStep 1594355 = 2391533) B2391533
theorem B1790977 : Blo 1060614 1790977 := bstep (se 2 (by rfl) ⟨671616, by rfl⟩ : syracuseStep 1790977 = 1343233) B1343233
theorem B1594385 : Blo 1060614 1594385 := bstep (se 2 (by rfl) ⟨597894, by rfl⟩ : syracuseStep 1594385 = 1195789) B1195789
theorem B1791011 : Blo 1060614 1791011 := bstep (se 1 (by rfl) ⟨1343258, by rfl⟩ : syracuseStep 1791011 = 2686517) B2686517
theorem B1594403 : Blo 1060614 1594403 := bstep (se 1 (by rfl) ⟨1195802, by rfl⟩ : syracuseStep 1594403 = 2391605) B2391605
theorem B1594433 : Blo 1060614 1594433 := bstep (se 2 (by rfl) ⟨597912, by rfl⟩ : syracuseStep 1594433 = 1195825) B1195825
theorem B1594451 : Blo 1060614 1594451 := bstep (se 1 (by rfl) ⟨1195838, by rfl⟩ : syracuseStep 1594451 = 2391677) B2391677
theorem B27939953 : Blo 1060614 27939953 := bstep (se 2 (by rfl) ⟨10477482, by rfl⟩ : syracuseStep 27939953 = 20954965) B20954965
theorem B1594481 : Blo 1060614 1594481 := bstep (se 2 (by rfl) ⟨597930, by rfl⟩ : syracuseStep 1594481 = 1195861) B1195861
theorem B1594499 : Blo 1060614 1594499 := bstep (se 1 (by rfl) ⟨1195874, by rfl⟩ : syracuseStep 1594499 = 2391749) B2391749
theorem B1594529 : Blo 1060614 1594529 := bstep (se 2 (by rfl) ⟨597948, by rfl⟩ : syracuseStep 1594529 = 1195897) B1195897
theorem B1791139 : Blo 1060614 1791139 := bstep (se 1 (by rfl) ⟨1343354, by rfl⟩ : syracuseStep 1791139 = 2686709) B2686709
theorem B1594547 : Blo 1060614 1594547 := bstep (se 1 (by rfl) ⟨1195910, by rfl⟩ : syracuseStep 1594547 = 2391821) B2391821
theorem B1594577 : Blo 1060614 1594577 := bstep (se 2 (by rfl) ⟨597966, by rfl⟩ : syracuseStep 1594577 = 1195933) B1195933
theorem B1594595 : Blo 1060614 1594595 := bstep (se 1 (by rfl) ⟨1195946, by rfl⟩ : syracuseStep 1594595 = 2391893) B2391893
theorem B4150499 : Blo 1060614 4150499 := bstep (se 1 (by rfl) ⟨3112874, by rfl⟩ : syracuseStep 4150499 = 6225749) B6225749
theorem B1594625 : Blo 1060614 1594625 := bstep (se 2 (by rfl) ⟨597984, by rfl⟩ : syracuseStep 1594625 = 1195969) B1195969
theorem B1594643 : Blo 1060614 1594643 := bstep (se 1 (by rfl) ⟨1195982, by rfl⟩ : syracuseStep 1594643 = 2391965) B2391965
theorem B1791281 : Blo 1060614 1791281 := bstep (se 2 (by rfl) ⟨671730, by rfl⟩ : syracuseStep 1791281 = 1343461) B1343461
theorem B1594673 : Blo 1060614 1594673 := bstep (se 2 (by rfl) ⟨598002, by rfl⟩ : syracuseStep 1594673 = 1196005) B1196005
theorem B1594691 : Blo 1060614 1594691 := bstep (se 1 (by rfl) ⟨1196018, by rfl⟩ : syracuseStep 1594691 = 2392037) B2392037
theorem B1594721 : Blo 1060614 1594721 := bstep (se 2 (by rfl) ⟨598020, by rfl⟩ : syracuseStep 1594721 = 1196041) B1196041
theorem B1594739 : Blo 1060614 1594739 := bstep (se 1 (by rfl) ⟨1196054, by rfl⟩ : syracuseStep 1594739 = 2392109) B2392109
theorem B1594769 : Blo 1060614 1594769 := bstep (se 2 (by rfl) ⟨598038, by rfl⟩ : syracuseStep 1594769 = 1196077) B1196077
theorem B1594787 : Blo 1060614 1594787 := bstep (se 1 (by rfl) ⟨1196090, by rfl⟩ : syracuseStep 1594787 = 2392181) B2392181
theorem B1791409 : Blo 1060614 1791409 := bstep (se 2 (by rfl) ⟨671778, by rfl⟩ : syracuseStep 1791409 = 1343557) B1343557
theorem B1594817 : Blo 1060614 1594817 := bstep (se 2 (by rfl) ⟨598056, by rfl⟩ : syracuseStep 1594817 = 1196113) B1196113
theorem B1594835 : Blo 1060614 1594835 := bstep (se 1 (by rfl) ⟨1196126, by rfl⟩ : syracuseStep 1594835 = 2392253) B2392253
theorem B1791443 : Blo 1060614 1791443 := bstep (se 1 (by rfl) ⟨1343582, by rfl⟩ : syracuseStep 1791443 = 2687165) B2687165
theorem B1594865 : Blo 1060614 1594865 := bstep (se 2 (by rfl) ⟨598074, by rfl⟩ : syracuseStep 1594865 = 1196149) B1196149
theorem B1594883 : Blo 1060614 1594883 := bstep (se 1 (by rfl) ⟨1196162, by rfl⟩ : syracuseStep 1594883 = 2392325) B2392325
theorem B1594913 : Blo 1060614 1594913 := bstep (se 2 (by rfl) ⟨598092, by rfl⟩ : syracuseStep 1594913 = 1196185) B1196185
theorem B1594931 : Blo 1060614 1594931 := bstep (se 1 (by rfl) ⟨1196198, by rfl⟩ : syracuseStep 1594931 = 2392397) B2392397
theorem B1594961 : Blo 1060614 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B1791571 : Blo 1060614 1791571 := bstep (se 1 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 1791571 = 2687357) B2687357
theorem B1594979 : Blo 1060614 1594979 := bstep (se 1 (by rfl) ⟨1196234, by rfl⟩ : syracuseStep 1594979 = 2392469) B2392469
theorem B3069539 : Blo 1060614 3069539 := bstep (se 1 (by rfl) ⟨2302154, by rfl⟩ : syracuseStep 3069539 = 4604309) B4604309
theorem B2020963 : Blo 1060614 2020963 := bstep (se 1 (by rfl) ⟨1515722, by rfl⟩ : syracuseStep 2020963 = 3031445) B3031445
theorem B1595009 : Blo 1060614 1595009 := bstep (se 2 (by rfl) ⟨598128, by rfl⟩ : syracuseStep 1595009 = 1196257) B1196257
theorem B1595027 : Blo 1060614 1595027 := bstep (se 1 (by rfl) ⟨1196270, by rfl⟩ : syracuseStep 1595027 = 2392541) B2392541
theorem B1595057 : Blo 1060614 1595057 := bstep (se 2 (by rfl) ⟨598146, by rfl⟩ : syracuseStep 1595057 = 1196293) B1196293
theorem B1595075 : Blo 1060614 1595075 := bstep (se 1 (by rfl) ⟨1196306, by rfl⟩ : syracuseStep 1595075 = 2392613) B2392613
theorem B1791713 : Blo 1060614 1791713 := bstep (se 2 (by rfl) ⟨671892, by rfl⟩ : syracuseStep 1791713 = 1343785) B1343785
theorem B1595105 : Blo 1060614 1595105 := bstep (se 2 (by rfl) ⟨598164, by rfl⟩ : syracuseStep 1595105 = 1196329) B1196329
theorem B1595123 : Blo 1060614 1595123 := bstep (se 1 (by rfl) ⟨1196342, by rfl⟩ : syracuseStep 1595123 = 2392685) B2392685
theorem B1595153 : Blo 1060614 1595153 := bstep (se 2 (by rfl) ⟨598182, by rfl⟩ : syracuseStep 1595153 = 1196365) B1196365
theorem B1595171 : Blo 1060614 1595171 := bstep (se 1 (by rfl) ⟨1196378, by rfl⟩ : syracuseStep 1595171 = 2392757) B2392757
theorem B1595201 : Blo 1060614 1595201 := bstep (se 2 (by rfl) ⟨598200, by rfl⟩ : syracuseStep 1595201 = 1196401) B1196401
theorem B1595219 : Blo 1060614 1595219 := bstep (se 1 (by rfl) ⟨1196414, by rfl⟩ : syracuseStep 1595219 = 2392829) B2392829
theorem B1791841 : Blo 1060614 1791841 := bstep (se 2 (by rfl) ⟨671940, by rfl⟩ : syracuseStep 1791841 = 1343881) B1343881
theorem B2152291 : Blo 1060614 2152291 := bstep (se 1 (by rfl) ⟨1614218, by rfl⟩ : syracuseStep 2152291 = 3228437) B3228437
theorem B1595249 : Blo 1060614 1595249 := bstep (se 2 (by rfl) ⟨598218, by rfl⟩ : syracuseStep 1595249 = 1196437) B1196437
theorem B1791875 : Blo 1060614 1791875 := bstep (se 1 (by rfl) ⟨1343906, by rfl⟩ : syracuseStep 1791875 = 2687813) B2687813
theorem B1595267 : Blo 1060614 1595267 := bstep (se 1 (by rfl) ⟨1196450, by rfl⟩ : syracuseStep 1595267 = 2392901) B2392901
theorem B1595297 : Blo 1060614 1595297 := bstep (se 2 (by rfl) ⟨598236, by rfl⟩ : syracuseStep 1595297 = 1196473) B1196473
theorem B1595315 : Blo 1060614 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B1595345 : Blo 1060614 1595345 := bstep (se 2 (by rfl) ⟨598254, by rfl⟩ : syracuseStep 1595345 = 1196509) B1196509
theorem B1595363 : Blo 1060614 1595363 := bstep (se 1 (by rfl) ⟨1196522, by rfl⟩ : syracuseStep 1595363 = 2393045) B2393045
theorem B1595393 : Blo 1060614 1595393 := bstep (se 2 (by rfl) ⟨598272, by rfl⟩ : syracuseStep 1595393 = 1196545) B1196545
theorem B1792003 : Blo 1060614 1792003 := bstep (se 1 (by rfl) ⟨1344002, by rfl⟩ : syracuseStep 1792003 = 2688005) B2688005
theorem B1595411 : Blo 1060614 1595411 := bstep (se 1 (by rfl) ⟨1196558, by rfl⟩ : syracuseStep 1595411 = 2393117) B2393117
theorem B1595441 : Blo 1060614 1595441 := bstep (se 2 (by rfl) ⟨598290, by rfl⟩ : syracuseStep 1595441 = 1196581) B1196581
theorem B1595459 : Blo 1060614 1595459 := bstep (se 1 (by rfl) ⟨1196594, by rfl⟩ : syracuseStep 1595459 = 2393189) B2393189
theorem B1595489 : Blo 1060614 1595489 := bstep (se 2 (by rfl) ⟨598308, by rfl⟩ : syracuseStep 1595489 = 1196617) B1196617
theorem B1595507 : Blo 1060614 1595507 := bstep (se 1 (by rfl) ⟨1196630, by rfl⟩ : syracuseStep 1595507 = 2393261) B2393261
theorem B3823757 : Blo 1060614 3823757 := bstep (se 3 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 3823757 = 1433909) B1433909
theorem B11491469 : Blo 1060614 11491469 := bstep (se 3 (by rfl) ⟨2154650, by rfl⟩ : syracuseStep 11491469 = 4309301) B4309301
theorem B1792145 : Blo 1060614 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B1595537 : Blo 1060614 1595537 := bstep (se 2 (by rfl) ⟨598326, by rfl⟩ : syracuseStep 1595537 = 1196653) B1196653
theorem B2906275 : Blo 1060614 2906275 := bstep (se 1 (by rfl) ⟨2179706, by rfl⟩ : syracuseStep 2906275 = 4359413) B4359413
theorem B1595555 : Blo 1060614 1595555 := bstep (se 1 (by rfl) ⟨1196666, by rfl⟩ : syracuseStep 1595555 = 2393333) B2393333
theorem B1595585 : Blo 1060614 1595585 := bstep (se 2 (by rfl) ⟨598344, by rfl⟩ : syracuseStep 1595585 = 1196689) B1196689
theorem B1595603 : Blo 1060614 1595603 := bstep (se 1 (by rfl) ⟨1196702, by rfl⟩ : syracuseStep 1595603 = 2393405) B2393405
theorem B6052067 : Blo 1060614 6052067 := bstep (se 1 (by rfl) ⟨4539050, by rfl⟩ : syracuseStep 6052067 = 9078101) B9078101
theorem B1595633 : Blo 1060614 1595633 := bstep (se 2 (by rfl) ⟨598362, by rfl⟩ : syracuseStep 1595633 = 1196725) B1196725
theorem B1595651 : Blo 1060614 1595651 := bstep (se 1 (by rfl) ⟨1196738, by rfl⟩ : syracuseStep 1595651 = 2393477) B2393477
theorem B1792273 : Blo 1060614 1792273 := bstep (se 2 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 1792273 = 1344205) B1344205
theorem B1595681 : Blo 1060614 1595681 := bstep (se 2 (by rfl) ⟨598380, by rfl⟩ : syracuseStep 1595681 = 1196761) B1196761
theorem B1792307 : Blo 1060614 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B1595699 : Blo 1060614 1595699 := bstep (se 1 (by rfl) ⟨1196774, by rfl⟩ : syracuseStep 1595699 = 2393549) B2393549
theorem B1595729 : Blo 1060614 1595729 := bstep (se 2 (by rfl) ⟨598398, by rfl⟩ : syracuseStep 1595729 = 1196797) B1196797
theorem B1595747 : Blo 1060614 1595747 := bstep (se 1 (by rfl) ⟨1196810, by rfl⟩ : syracuseStep 1595747 = 2393621) B2393621
theorem B5101937 : Blo 1060614 5101937 := bstep (se 2 (by rfl) ⟨1913226, by rfl⟩ : syracuseStep 5101937 = 3826453) B3826453
theorem B1595777 : Blo 1060614 1595777 := bstep (se 2 (by rfl) ⟨598416, by rfl⟩ : syracuseStep 1595777 = 1196833) B1196833
theorem B1595795 : Blo 1060614 1595795 := bstep (se 1 (by rfl) ⟨1196846, by rfl⟩ : syracuseStep 1595795 = 2393693) B2393693
theorem B1595825 : Blo 1060614 1595825 := bstep (se 2 (by rfl) ⟨598434, by rfl⟩ : syracuseStep 1595825 = 1196869) B1196869
theorem B1792435 : Blo 1060614 1792435 := bstep (se 1 (by rfl) ⟨1344326, by rfl⟩ : syracuseStep 1792435 = 2688653) B2688653
theorem B1726915 : Blo 1060614 1726915 := bstep (se 1 (by rfl) ⟨1295186, by rfl⟩ : syracuseStep 1726915 = 2590373) B2590373
theorem B1595843 : Blo 1060614 1595843 := bstep (se 1 (by rfl) ⟨1196882, by rfl⟩ : syracuseStep 1595843 = 2393765) B2393765
theorem B1595873 : Blo 1060614 1595873 := bstep (se 2 (by rfl) ⟨598452, by rfl⟩ : syracuseStep 1595873 = 1196905) B1196905
theorem B1595891 : Blo 1060614 1595891 := bstep (se 1 (by rfl) ⟨1196918, by rfl⟩ : syracuseStep 1595891 = 2393837) B2393837
theorem B2152963 : Blo 1060614 2152963 := bstep (se 1 (by rfl) ⟨1614722, by rfl⟩ : syracuseStep 2152963 = 3229445) B3229445
theorem B2873873 : Blo 1060614 2873873 := bstep (se 2 (by rfl) ⟨1077702, by rfl⟩ : syracuseStep 2873873 = 2155405) B2155405
theorem B1595921 : Blo 1060614 1595921 := bstep (se 2 (by rfl) ⟨598470, by rfl⟩ : syracuseStep 1595921 = 1196941) B1196941
theorem B1595939 : Blo 1060614 1595939 := bstep (se 1 (by rfl) ⟨1196954, by rfl⟩ : syracuseStep 1595939 = 2393909) B2393909
theorem B6806065 : Blo 1060614 6806065 := bstep (se 2 (by rfl) ⟨2552274, by rfl⟩ : syracuseStep 6806065 = 5104549) B5104549
theorem B1792577 : Blo 1060614 1792577 := bstep (se 2 (by rfl) ⟨672216, by rfl⟩ : syracuseStep 1792577 = 1344433) B1344433
theorem B1595969 : Blo 1060614 1595969 := bstep (se 2 (by rfl) ⟨598488, by rfl⟩ : syracuseStep 1595969 = 1196977) B1196977
theorem B1595987 : Blo 1060614 1595987 := bstep (se 1 (by rfl) ⟨1196990, by rfl⟩ : syracuseStep 1595987 = 2393981) B2393981
theorem B2873969 : Blo 1060614 2873969 := bstep (se 2 (by rfl) ⟨1077738, by rfl⟩ : syracuseStep 2873969 = 2155477) B2155477
theorem B1596017 : Blo 1060614 1596017 := bstep (se 2 (by rfl) ⟨598506, by rfl⟩ : syracuseStep 1596017 = 1197013) B1197013
theorem B1596035 : Blo 1060614 1596035 := bstep (se 1 (by rfl) ⟨1197026, by rfl⟩ : syracuseStep 1596035 = 2394053) B2394053
theorem B1596065 : Blo 1060614 1596065 := bstep (se 2 (by rfl) ⟨598524, by rfl⟩ : syracuseStep 1596065 = 1197049) B1197049
theorem B1596083 : Blo 1060614 1596083 := bstep (se 1 (by rfl) ⟨1197062, by rfl⟩ : syracuseStep 1596083 = 2394125) B2394125
theorem B1792705 : Blo 1060614 1792705 := bstep (se 2 (by rfl) ⟨672264, by rfl⟩ : syracuseStep 1792705 = 1344529) B1344529
theorem B1596113 : Blo 1060614 1596113 := bstep (se 2 (by rfl) ⟨598542, by rfl⟩ : syracuseStep 1596113 = 1197085) B1197085
theorem B1792739 : Blo 1060614 1792739 := bstep (se 1 (by rfl) ⟨1344554, by rfl⟩ : syracuseStep 1792739 = 2689109) B2689109
theorem B1596131 : Blo 1060614 1596131 := bstep (se 1 (by rfl) ⟨1197098, by rfl⟩ : syracuseStep 1596131 = 2394197) B2394197
theorem B1596161 : Blo 1060614 1596161 := bstep (se 2 (by rfl) ⟨598560, by rfl⟩ : syracuseStep 1596161 = 1197121) B1197121
theorem B1661699 : Blo 1060614 1661699 := bstep (se 1 (by rfl) ⟨1246274, by rfl⟩ : syracuseStep 1661699 = 2492549) B2492549
theorem B1596179 : Blo 1060614 1596179 := bstep (se 1 (by rfl) ⟨1197134, by rfl⟩ : syracuseStep 1596179 = 2394269) B2394269
theorem B1596209 : Blo 1060614 1596209 := bstep (se 2 (by rfl) ⟨598578, by rfl⟩ : syracuseStep 1596209 = 1197157) B1197157
theorem B1596227 : Blo 1060614 1596227 := bstep (se 1 (by rfl) ⟨1197170, by rfl⟩ : syracuseStep 1596227 = 2394341) B2394341
theorem B1596257 : Blo 1060614 1596257 := bstep (se 2 (by rfl) ⟨598596, by rfl⟩ : syracuseStep 1596257 = 1197193) B1197193
theorem B1792867 : Blo 1060614 1792867 := bstep (se 1 (by rfl) ⟨1344650, by rfl⟩ : syracuseStep 1792867 = 2689301) B2689301
theorem B1596275 : Blo 1060614 1596275 := bstep (se 1 (by rfl) ⟨1197206, by rfl⟩ : syracuseStep 1596275 = 2394413) B2394413
theorem B1596305 : Blo 1060614 1596305 := bstep (se 2 (by rfl) ⟨598614, by rfl⟩ : syracuseStep 1596305 = 1197229) B1197229
theorem B1596323 : Blo 1060614 1596323 := bstep (se 1 (by rfl) ⟨1197242, by rfl⟩ : syracuseStep 1596323 = 2394485) B2394485
theorem B1596353 : Blo 1060614 1596353 := bstep (se 2 (by rfl) ⟨598632, by rfl⟩ : syracuseStep 1596353 = 1197265) B1197265
theorem B1596371 : Blo 1060614 1596371 := bstep (se 1 (by rfl) ⟨1197278, by rfl⟩ : syracuseStep 1596371 = 2394557) B2394557
theorem B1793009 : Blo 1060614 1793009 := bstep (se 2 (by rfl) ⟨672378, by rfl⟩ : syracuseStep 1793009 = 1344757) B1344757
theorem B1596401 : Blo 1060614 1596401 := bstep (se 2 (by rfl) ⟨598650, by rfl⟩ : syracuseStep 1596401 = 1197301) B1197301
theorem B1596419 : Blo 1060614 1596419 := bstep (se 1 (by rfl) ⟨1197314, by rfl⟩ : syracuseStep 1596419 = 2394629) B2394629
theorem B1596449 : Blo 1060614 1596449 := bstep (se 2 (by rfl) ⟨598668, by rfl⟩ : syracuseStep 1596449 = 1197337) B1197337
theorem B3398701 : Blo 1060614 3398701 := bstep (se 3 (by rfl) ⟨637256, by rfl⟩ : syracuseStep 3398701 = 1274513) B1274513
theorem B1596467 : Blo 1060614 1596467 := bstep (se 1 (by rfl) ⟨1197350, by rfl⟩ : syracuseStep 1596467 = 2394701) B2394701
theorem B1596497 : Blo 1060614 1596497 := bstep (se 2 (by rfl) ⟨598686, by rfl⟩ : syracuseStep 1596497 = 1197373) B1197373
theorem B1596515 : Blo 1060614 1596515 := bstep (se 1 (by rfl) ⟨1197386, by rfl⟩ : syracuseStep 1596515 = 2394773) B2394773
theorem B1793137 : Blo 1060614 1793137 := bstep (se 2 (by rfl) ⟨672426, by rfl⟩ : syracuseStep 1793137 = 1344853) B1344853
theorem B1596545 : Blo 1060614 1596545 := bstep (se 2 (by rfl) ⟨598704, by rfl⟩ : syracuseStep 1596545 = 1197409) B1197409
theorem B1793171 : Blo 1060614 1793171 := bstep (se 1 (by rfl) ⟨1344878, by rfl⟩ : syracuseStep 1793171 = 2689757) B2689757
theorem B1596563 : Blo 1060614 1596563 := bstep (se 1 (by rfl) ⟨1197422, by rfl⟩ : syracuseStep 1596563 = 2394845) B2394845
theorem B1596593 : Blo 1060614 1596593 := bstep (se 2 (by rfl) ⟨598722, by rfl⟩ : syracuseStep 1596593 = 1197445) B1197445
theorem B1596611 : Blo 1060614 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B6053069 : Blo 1060614 6053069 := bstep (se 3 (by rfl) ⟨1134950, by rfl⟩ : syracuseStep 6053069 = 2269901) B2269901
theorem B1596641 : Blo 1060614 1596641 := bstep (se 2 (by rfl) ⟨598740, by rfl⟩ : syracuseStep 1596641 = 1197481) B1197481
theorem B1596659 : Blo 1060614 1596659 := bstep (se 1 (by rfl) ⟨1197494, by rfl⟩ : syracuseStep 1596659 = 2394989) B2394989
theorem B12082445 : Blo 1060614 12082445 := bstep (se 3 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 12082445 = 4530917) B4530917
theorem B1596689 : Blo 1060614 1596689 := bstep (se 2 (by rfl) ⟨598758, by rfl⟩ : syracuseStep 1596689 = 1197517) B1197517
theorem B1793299 : Blo 1060614 1793299 := bstep (se 1 (by rfl) ⟨1344974, by rfl⟩ : syracuseStep 1793299 = 2689949) B2689949
theorem B1596707 : Blo 1060614 1596707 := bstep (se 1 (by rfl) ⟨1197530, by rfl⟩ : syracuseStep 1596707 = 2395061) B2395061
theorem B1596737 : Blo 1060614 1596737 := bstep (se 2 (by rfl) ⟨598776, by rfl⟩ : syracuseStep 1596737 = 1197553) B1197553
theorem B1596755 : Blo 1060614 1596755 := bstep (se 1 (by rfl) ⟨1197566, by rfl⟩ : syracuseStep 1596755 = 2395133) B2395133
theorem B1596785 : Blo 1060614 1596785 := bstep (se 2 (by rfl) ⟨598794, by rfl⟩ : syracuseStep 1596785 = 1197589) B1197589
theorem B1596803 : Blo 1060614 1596803 := bstep (se 1 (by rfl) ⟨1197602, by rfl⟩ : syracuseStep 1596803 = 2395205) B2395205
theorem B1793441 : Blo 1060614 1793441 := bstep (se 2 (by rfl) ⟨672540, by rfl⟩ : syracuseStep 1793441 = 1345081) B1345081
theorem B1596833 : Blo 1060614 1596833 := bstep (se 2 (by rfl) ⟨598812, by rfl⟩ : syracuseStep 1596833 = 1197625) B1197625
theorem B1596851 : Blo 1060614 1596851 := bstep (se 1 (by rfl) ⟨1197638, by rfl⟩ : syracuseStep 1596851 = 2395277) B2395277
theorem B1596881 : Blo 1060614 1596881 := bstep (se 2 (by rfl) ⟨598830, by rfl⟩ : syracuseStep 1596881 = 1197661) B1197661
theorem B1596899 : Blo 1060614 1596899 := bstep (se 1 (by rfl) ⟨1197674, by rfl⟩ : syracuseStep 1596899 = 2395349) B2395349
theorem B1793569 : Blo 1060614 1793569 := bstep (se 2 (by rfl) ⟨672588, by rfl⟩ : syracuseStep 1793569 = 1345177) B1345177
theorem B1793603 : Blo 1060614 1793603 := bstep (se 1 (by rfl) ⟨1345202, by rfl⟩ : syracuseStep 1793603 = 2690405) B2690405
theorem B1793731 : Blo 1060614 1793731 := bstep (se 1 (by rfl) ⟨1345298, by rfl⟩ : syracuseStep 1793731 = 2690597) B2690597
theorem B3825443 : Blo 1060614 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B2875171 : Blo 1060614 2875171 := bstep (se 1 (by rfl) ⟨2156378, by rfl⟩ : syracuseStep 2875171 = 4312757) B4312757
theorem B1793873 : Blo 1060614 1793873 := bstep (se 2 (by rfl) ⟨672702, by rfl⟩ : syracuseStep 1793873 = 1345405) B1345405
theorem B2875267 : Blo 1060614 2875267 := bstep (se 1 (by rfl) ⟨2156450, by rfl⟩ : syracuseStep 2875267 = 4312901) B4312901
theorem B1794001 : Blo 1060614 1794001 := bstep (se 2 (by rfl) ⟨672750, by rfl⟩ : syracuseStep 1794001 = 1345501) B1345501
theorem B5103587 : Blo 1060614 5103587 := bstep (se 1 (by rfl) ⟨3827690, by rfl⟩ : syracuseStep 5103587 = 7655381) B7655381
theorem B1794035 : Blo 1060614 1794035 := bstep (se 1 (by rfl) ⟨1345526, by rfl⟩ : syracuseStep 1794035 = 2691053) B2691053
theorem B4546637 : Blo 1060614 4546637 := bstep (se 3 (by rfl) ⟨852494, by rfl⟩ : syracuseStep 4546637 = 1704989) B1704989
theorem B1794163 : Blo 1060614 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B1794305 : Blo 1060614 1794305 := bstep (se 2 (by rfl) ⟨672864, by rfl⟩ : syracuseStep 1794305 = 1345729) B1345729
theorem B1794433 : Blo 1060614 1794433 := bstep (se 2 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 1794433 = 1345825) B1345825
theorem B1794467 : Blo 1060614 1794467 := bstep (se 1 (by rfl) ⟨1345850, by rfl⟩ : syracuseStep 1794467 = 2691701) B2691701
theorem B4546979 : Blo 1060614 4546979 := bstep (se 1 (by rfl) ⟨3410234, by rfl⟩ : syracuseStep 4546979 = 6820469) B6820469
theorem B3400163 : Blo 1060614 3400163 := bstep (se 1 (by rfl) ⟨2550122, by rfl⟩ : syracuseStep 3400163 = 5100245) B5100245
theorem B1794595 : Blo 1060614 1794595 := bstep (se 1 (by rfl) ⟨1345946, by rfl⟩ : syracuseStep 1794595 = 2691893) B2691893
theorem B2875949 : Blo 1060614 2875949 := bstep (se 3 (by rfl) ⟨539240, by rfl⟩ : syracuseStep 2875949 = 1078481) B1078481
theorem B1794737 : Blo 1060614 1794737 := bstep (se 2 (by rfl) ⟨673026, by rfl⟩ : syracuseStep 1794737 = 1346053) B1346053
theorem B5104397 : Blo 1060614 5104397 := bstep (se 3 (by rfl) ⟨957074, by rfl⟩ : syracuseStep 5104397 = 1914149) B1914149
theorem B1794865 : Blo 1060614 1794865 := bstep (se 2 (by rfl) ⟨673074, by rfl⟩ : syracuseStep 1794865 = 1346149) B1346149
theorem B1434433 : Blo 1060614 1434433 := bstep (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) B1075825
theorem B1532737 : Blo 1060614 1532737 := bstep (se 2 (by rfl) ⟨574776, by rfl⟩ : syracuseStep 1532737 = 1149553) B1149553
theorem B1794899 : Blo 1060614 1794899 := bstep (se 1 (by rfl) ⟨1346174, by rfl⟩ : syracuseStep 1794899 = 2692349) B2692349
theorem B4547441 : Blo 1060614 4547441 := bstep (se 2 (by rfl) ⟨1705290, by rfl⟩ : syracuseStep 4547441 = 3410581) B3410581
theorem B11068301 : Blo 1060614 11068301 := bstep (se 3 (by rfl) ⟨2075306, by rfl⟩ : syracuseStep 11068301 = 4150613) B4150613
theorem B1795027 : Blo 1060614 1795027 := bstep (se 1 (by rfl) ⟨1346270, by rfl⟩ : syracuseStep 1795027 = 2692541) B2692541
theorem B2548739 : Blo 1060614 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B1795169 : Blo 1060614 1795169 := bstep (se 2 (by rfl) ⟨673188, by rfl⟩ : syracuseStep 1795169 = 1346377) B1346377
theorem B1795297 : Blo 1060614 1795297 := bstep (se 2 (by rfl) ⟨673236, by rfl⟩ : syracuseStep 1795297 = 1346473) B1346473
theorem B1795331 : Blo 1060614 1795331 := bstep (se 1 (by rfl) ⟨1346498, by rfl⟩ : syracuseStep 1795331 = 2692997) B2692997
theorem B1795459 : Blo 1060614 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B2876845 : Blo 1060614 2876845 := bstep (se 3 (by rfl) ⟨539408, by rfl⟩ : syracuseStep 2876845 = 1078817) B1078817
theorem B1795601 : Blo 1060614 1795601 := bstep (se 2 (by rfl) ⟨673350, by rfl⟩ : syracuseStep 1795601 = 1346701) B1346701
theorem B1795729 : Blo 1060614 1795729 := bstep (se 2 (by rfl) ⟨673398, by rfl⟩ : syracuseStep 1795729 = 1346797) B1346797
theorem B2549411 : Blo 1060614 2549411 := bstep (se 1 (by rfl) ⟨1912058, by rfl⟩ : syracuseStep 2549411 = 3824117) B3824117
theorem B1795763 : Blo 1060614 1795763 := bstep (se 1 (by rfl) ⟨1346822, by rfl⟩ : syracuseStep 1795763 = 2693645) B2693645
theorem B1795891 : Blo 1060614 1795891 := bstep (se 1 (by rfl) ⟨1346918, by rfl⟩ : syracuseStep 1795891 = 2693837) B2693837
theorem B2549681 : Blo 1060614 2549681 := bstep (se 2 (by rfl) ⟨956130, by rfl⟩ : syracuseStep 2549681 = 1912261) B1912261
theorem B1796033 : Blo 1060614 1796033 := bstep (se 2 (by rfl) ⟨673512, by rfl⟩ : syracuseStep 1796033 = 1347025) B1347025
theorem B3401777 : Blo 1060614 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B6055985 : Blo 1060614 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B1796161 : Blo 1060614 1796161 := bstep (se 2 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 1796161 = 1347121) B1347121
theorem B1796195 : Blo 1060614 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B12085361 : Blo 1060614 12085361 := bstep (se 2 (by rfl) ⟨4532010, by rfl⟩ : syracuseStep 12085361 = 9064021) B9064021
theorem B7760069 : Blo 1060614 7760069 := bstep (se 4 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 7760069 = 1455013) B1455013
theorem B1796323 : Blo 1060614 1796323 := bstep (se 1 (by rfl) ⟨1347242, by rfl⟩ : syracuseStep 1796323 = 2694485) B2694485
theorem B1796465 : Blo 1060614 1796465 := bstep (se 2 (by rfl) ⟨673674, by rfl⟩ : syracuseStep 1796465 = 1347349) B1347349
theorem B18147725 : Blo 1060614 18147725 := bstep (se 3 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 18147725 = 6805397) B6805397
theorem B2419139 : Blo 1060614 2419139 := bstep (se 1 (by rfl) ⟨1814354, by rfl⟩ : syracuseStep 2419139 = 3628709) B3628709
theorem B3631565 : Blo 1060614 3631565 := bstep (se 3 (by rfl) ⟨680918, by rfl⟩ : syracuseStep 3631565 = 1361837) B1361837
theorem B2386385 : Blo 1060614 2386385 := bstep (se 2 (by rfl) ⟨894894, by rfl⟩ : syracuseStep 2386385 = 1789789) B1789789
theorem B2386403 : Blo 1060614 2386403 := bstep (se 1 (by rfl) ⟨1789802, by rfl⟩ : syracuseStep 2386403 = 3579605) B3579605
theorem B2550257 : Blo 1060614 2550257 := bstep (se 2 (by rfl) ⟨956346, by rfl⟩ : syracuseStep 2550257 = 1912693) B1912693
theorem B2550449 : Blo 1060614 2550449 := bstep (se 2 (by rfl) ⟨956418, by rfl⟩ : syracuseStep 2550449 = 1912837) B1912837
theorem B7269041 : Blo 1060614 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B2386673 : Blo 1060614 2386673 := bstep (se 2 (by rfl) ⟨895002, by rfl⟩ : syracuseStep 2386673 = 1790005) B1790005
theorem B2386691 : Blo 1060614 2386691 := bstep (se 1 (by rfl) ⟨1790018, by rfl⟩ : syracuseStep 2386691 = 3580037) B3580037
theorem B2550737 : Blo 1060614 2550737 := bstep (se 2 (by rfl) ⟨956526, by rfl⟩ : syracuseStep 2550737 = 1913053) B1913053
theorem B2157521 : Blo 1060614 2157521 := bstep (se 2 (by rfl) ⟨809070, by rfl⟩ : syracuseStep 2157521 = 1618141) B1618141
theorem B2157553 : Blo 1060614 2157553 := bstep (se 2 (by rfl) ⟨809082, by rfl⟩ : syracuseStep 2157553 = 1618165) B1618165
theorem B2386961 : Blo 1060614 2386961 := bstep (se 2 (by rfl) ⟨895110, by rfl⟩ : syracuseStep 2386961 = 1790221) B1790221
theorem B2386979 : Blo 1060614 2386979 := bstep (se 1 (by rfl) ⟨1790234, by rfl⟩ : syracuseStep 2386979 = 3580469) B3580469
theorem B44231957 : Blo 1060614 44231957 := bstep (se 6 (by rfl) ⟨1036686, by rfl⟩ : syracuseStep 44231957 = 2073373) B2073373
theorem B2387249 : Blo 1060614 2387249 := bstep (se 2 (by rfl) ⟨895218, by rfl⟩ : syracuseStep 2387249 = 1790437) B1790437
theorem B2911537 : Blo 1060614 2911537 := bstep (se 2 (by rfl) ⟨1091826, by rfl⟩ : syracuseStep 2911537 = 2183653) B2183653
theorem B2387267 : Blo 1060614 2387267 := bstep (se 1 (by rfl) ⟨1790450, by rfl⟩ : syracuseStep 2387267 = 3580901) B3580901
theorem B3829133 : Blo 1060614 3829133 := bstep (se 3 (by rfl) ⟨717962, by rfl⟩ : syracuseStep 3829133 = 1435925) B1435925
theorem B6057443 : Blo 1060614 6057443 := bstep (se 1 (by rfl) ⟨4543082, by rfl⟩ : syracuseStep 6057443 = 9086165) B9086165
theorem B2387537 : Blo 1060614 2387537 := bstep (se 2 (by rfl) ⟨895326, by rfl⟩ : syracuseStep 2387537 = 1790653) B1790653
theorem B2387555 : Blo 1060614 2387555 := bstep (se 1 (by rfl) ⟨1790666, by rfl⟩ : syracuseStep 2387555 = 3581333) B3581333
theorem B6811397 : Blo 1060614 6811397 := bstep (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) B1277137
theorem B1535761 : Blo 1060614 1535761 := bstep (se 2 (by rfl) ⟨575910, by rfl⟩ : syracuseStep 1535761 = 1151821) B1151821
theorem B1699633 : Blo 1060614 1699633 := bstep (se 2 (by rfl) ⟨637362, by rfl⟩ : syracuseStep 1699633 = 1274725) B1274725
theorem B2387825 : Blo 1060614 2387825 := bstep (se 2 (by rfl) ⟨895434, by rfl⟩ : syracuseStep 2387825 = 1790869) B1790869
theorem B2387843 : Blo 1060614 2387843 := bstep (se 1 (by rfl) ⟨1790882, by rfl⟩ : syracuseStep 2387843 = 3581765) B3581765
theorem B3403853 : Blo 1060614 3403853 := bstep (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) B1276445
theorem B2388113 : Blo 1060614 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B2388131 : Blo 1060614 2388131 := bstep (se 1 (by rfl) ⟨1791098, by rfl⟩ : syracuseStep 2388131 = 3582197) B3582197
theorem B2388401 : Blo 1060614 2388401 := bstep (se 2 (by rfl) ⟨895650, by rfl⟩ : syracuseStep 2388401 = 1791301) B1791301
theorem B2388419 : Blo 1060614 2388419 := bstep (se 1 (by rfl) ⟨1791314, by rfl⟩ : syracuseStep 2388419 = 3582629) B3582629
theorem B3830257 : Blo 1060614 3830257 := bstep (se 2 (by rfl) ⟨1436346, by rfl⟩ : syracuseStep 3830257 = 2872693) B2872693
theorem B9826915 : Blo 1060614 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B2585201 : Blo 1060614 2585201 := bstep (se 2 (by rfl) ⟨969450, by rfl⟩ : syracuseStep 2585201 = 1938901) B1938901
theorem B2388689 : Blo 1060614 2388689 := bstep (se 2 (by rfl) ⟨895758, by rfl⟩ : syracuseStep 2388689 = 1791517) B1791517
theorem B2388707 : Blo 1060614 2388707 := bstep (se 1 (by rfl) ⟨1791530, by rfl⟩ : syracuseStep 2388707 = 3583061) B3583061
theorem B24507157 : Blo 1060614 24507157 := bstep (se 6 (by rfl) ⟨574386, by rfl⟩ : syracuseStep 24507157 = 1148773) B1148773
theorem B3404749 : Blo 1060614 3404749 := bstep (se 3 (by rfl) ⟨638390, by rfl⟩ : syracuseStep 3404749 = 1276781) B1276781
theorem B2388977 : Blo 1060614 2388977 := bstep (se 2 (by rfl) ⟨895866, by rfl⟩ : syracuseStep 2388977 = 1791733) B1791733
theorem B2388995 : Blo 1060614 2388995 := bstep (se 1 (by rfl) ⟨1791746, by rfl⟩ : syracuseStep 2388995 = 3583493) B3583493
theorem B1438769 : Blo 1060614 1438769 := bstep (se 2 (by rfl) ⟨539538, by rfl⟩ : syracuseStep 1438769 = 1079077) B1079077
theorem B2389265 : Blo 1060614 2389265 := bstep (se 2 (by rfl) ⟨895974, by rfl⟩ : syracuseStep 2389265 = 1791949) B1791949
theorem B2389283 : Blo 1060614 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B15365429 : Blo 1060614 15365429 := bstep (se 5 (by rfl) ⟨720254, by rfl⟩ : syracuseStep 15365429 = 1440509) B1440509
theorem B5174705 : Blo 1060614 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B1701299 : Blo 1060614 1701299 := bstep (se 1 (by rfl) ⟨1275974, by rfl⟩ : syracuseStep 1701299 = 2551949) B2551949
theorem B1209811 : Blo 1060614 1209811 := bstep (se 1 (by rfl) ⟨907358, by rfl⟩ : syracuseStep 1209811 = 1814717) B1814717
theorem B2389553 : Blo 1060614 2389553 := bstep (se 2 (by rfl) ⟨896082, by rfl⟩ : syracuseStep 2389553 = 1792165) B1792165
theorem B1701427 : Blo 1060614 1701427 := bstep (se 1 (by rfl) ⟨1276070, by rfl⟩ : syracuseStep 1701427 = 2552141) B2552141
theorem B69760565 : Blo 1060614 69760565 := bstep (se 5 (by rfl) ⟨3270026, by rfl⟩ : syracuseStep 69760565 = 6540053) B6540053
theorem B2389571 : Blo 1060614 2389571 := bstep (se 1 (by rfl) ⟨1792178, by rfl⟩ : syracuseStep 2389571 = 3584357) B3584357
theorem B12285539 : Blo 1060614 12285539 := bstep (se 1 (by rfl) ⟨9214154, by rfl⟩ : syracuseStep 12285539 = 18428309) B18428309
theorem B2389841 : Blo 1060614 2389841 := bstep (se 2 (by rfl) ⟨896190, by rfl⟩ : syracuseStep 2389841 = 1792381) B1792381
theorem B2389859 : Blo 1060614 2389859 := bstep (se 1 (by rfl) ⟨1792394, by rfl⟩ : syracuseStep 2389859 = 3584789) B3584789
theorem B2684785 : Blo 1060614 2684785 := bstep (se 2 (by rfl) ⟨1006794, by rfl⟩ : syracuseStep 2684785 = 2013589) B2013589
theorem B1275763 : Blo 1060614 1275763 := bstep (se 1 (by rfl) ⟨956822, by rfl⟩ : syracuseStep 1275763 = 1913645) B1913645
theorem B2455427 : Blo 1060614 2455427 := bstep (se 1 (by rfl) ⟨1841570, by rfl⟩ : syracuseStep 2455427 = 3683141) B3683141
theorem B3831715 : Blo 1060614 3831715 := bstep (se 1 (by rfl) ⟨2873786, by rfl⟩ : syracuseStep 3831715 = 5747573) B5747573
theorem B1701811 : Blo 1060614 1701811 := bstep (se 1 (by rfl) ⟨1276358, by rfl⟩ : syracuseStep 1701811 = 2552717) B2552717
theorem B8058851 : Blo 1060614 8058851 := bstep (se 1 (by rfl) ⟨6044138, by rfl⟩ : syracuseStep 8058851 = 12088277) B12088277
theorem B1275907 : Blo 1060614 1275907 := bstep (se 1 (by rfl) ⟨956930, by rfl⟩ : syracuseStep 1275907 = 1913861) B1913861
theorem B3405827 : Blo 1060614 3405827 := bstep (se 1 (by rfl) ⟨2554370, by rfl⟩ : syracuseStep 3405827 = 5108741) B5108741
theorem B2390129 : Blo 1060614 2390129 := bstep (se 2 (by rfl) ⟨896298, by rfl⟩ : syracuseStep 2390129 = 1792597) B1792597
theorem B2685059 : Blo 1060614 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B2390147 : Blo 1060614 2390147 := bstep (se 1 (by rfl) ⟨1792610, by rfl⟩ : syracuseStep 2390147 = 3585221) B3585221
theorem B5372081 : Blo 1060614 5372081 := bstep (se 2 (by rfl) ⟨2014530, by rfl⟩ : syracuseStep 5372081 = 4029061) B4029061
theorem B1702067 : Blo 1060614 1702067 := bstep (se 1 (by rfl) ⟨1276550, by rfl⟩ : syracuseStep 1702067 = 2553101) B2553101
theorem B2685251 : Blo 1060614 2685251 := bstep (se 1 (by rfl) ⟨2013938, by rfl⟩ : syracuseStep 2685251 = 4027877) B4027877
theorem B3111281 : Blo 1060614 3111281 := bstep (se 2 (by rfl) ⟨1166730, by rfl⟩ : syracuseStep 3111281 = 2333461) B2333461
theorem B2390417 : Blo 1060614 2390417 := bstep (se 2 (by rfl) ⟨896406, by rfl⟩ : syracuseStep 2390417 = 1792813) B1792813
theorem B2390435 : Blo 1060614 2390435 := bstep (se 1 (by rfl) ⟨1792826, by rfl⟩ : syracuseStep 2390435 = 3585653) B3585653
theorem B4028849 : Blo 1060614 4028849 := bstep (se 2 (by rfl) ⟨1510818, by rfl⟩ : syracuseStep 4028849 = 3021637) B3021637
theorem B1702529 : Blo 1060614 1702529 := bstep (se 2 (by rfl) ⟨638448, by rfl⟩ : syracuseStep 1702529 = 1276897) B1276897
theorem B3406481 : Blo 1060614 3406481 := bstep (se 2 (by rfl) ⟨1277430, by rfl⟩ : syracuseStep 3406481 = 2554861) B2554861
theorem B2390705 : Blo 1060614 2390705 := bstep (se 2 (by rfl) ⟨896514, by rfl⟩ : syracuseStep 2390705 = 1793029) B1793029
theorem B2390723 : Blo 1060614 2390723 := bstep (se 1 (by rfl) ⟨1793042, by rfl⟩ : syracuseStep 2390723 = 3586085) B3586085
theorem B1866451 : Blo 1060614 1866451 := bstep (se 1 (by rfl) ⟨1399838, by rfl⟩ : syracuseStep 1866451 = 2799677) B2799677
theorem B1702625 : Blo 1060614 1702625 := bstep (se 2 (by rfl) ⟨638484, by rfl⟩ : syracuseStep 1702625 = 1276969) B1276969
theorem B1702657 : Blo 1060614 1702657 := bstep (se 2 (by rfl) ⟨638496, by rfl⟩ : syracuseStep 1702657 = 1276993) B1276993
theorem B2390993 : Blo 1060614 2390993 := bstep (se 2 (by rfl) ⟨896622, by rfl⟩ : syracuseStep 2390993 = 1793245) B1793245
theorem B2391011 : Blo 1060614 2391011 := bstep (se 1 (by rfl) ⟨1793258, by rfl⟩ : syracuseStep 2391011 = 3586517) B3586517
theorem B1276931 : Blo 1060614 1276931 := bstep (se 1 (by rfl) ⟨957698, by rfl⟩ : syracuseStep 1276931 = 1915397) B1915397
theorem B13630477 : Blo 1060614 13630477 := bstep (se 3 (by rfl) ⟨2555714, by rfl⟩ : syracuseStep 13630477 = 5111429) B5111429
theorem B1342595 : Blo 1060614 1342595 := bstep (se 1 (by rfl) ⟨1006946, by rfl⟩ : syracuseStep 1342595 = 2013893) B2013893
theorem B2686193 : Blo 1060614 2686193 := bstep (se 2 (by rfl) ⟨1007322, by rfl⟩ : syracuseStep 2686193 = 2014645) B2014645
theorem B2391281 : Blo 1060614 2391281 := bstep (se 2 (by rfl) ⟨896730, by rfl⟩ : syracuseStep 2391281 = 1793461) B1793461
theorem B2391299 : Blo 1060614 2391299 := bstep (se 1 (by rfl) ⟨1793474, by rfl⟩ : syracuseStep 2391299 = 3586949) B3586949
theorem B2686243 : Blo 1060614 2686243 := bstep (se 1 (by rfl) ⟨2014682, by rfl⟩ : syracuseStep 2686243 = 4029365) B4029365
theorem B2948483 : Blo 1060614 2948483 := bstep (se 1 (by rfl) ⟨2211362, by rfl⟩ : syracuseStep 2948483 = 4422725) B4422725
theorem B2686385 : Blo 1060614 2686385 := bstep (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) B2014789
theorem B2391569 : Blo 1060614 2391569 := bstep (se 2 (by rfl) ⟨896838, by rfl⟩ : syracuseStep 2391569 = 1793677) B1793677
theorem B2391587 : Blo 1060614 2391587 := bstep (se 1 (by rfl) ⟨1793690, by rfl⟩ : syracuseStep 2391587 = 3587381) B3587381
theorem B5373539 : Blo 1060614 5373539 := bstep (se 1 (by rfl) ⟨4030154, by rfl⟩ : syracuseStep 5373539 = 8060309) B8060309
theorem B7274083 : Blo 1060614 7274083 := bstep (se 1 (by rfl) ⟨5455562, by rfl⟩ : syracuseStep 7274083 = 10911125) B10911125
theorem B9698915 : Blo 1060614 9698915 := bstep (se 1 (by rfl) ⟨7274186, by rfl⟩ : syracuseStep 9698915 = 14548373) B14548373
theorem B6455045 : Blo 1060614 6455045 := bstep (se 4 (by rfl) ⟨605160, by rfl⟩ : syracuseStep 6455045 = 1210321) B1210321
theorem B2391857 : Blo 1060614 2391857 := bstep (se 2 (by rfl) ⟨896946, by rfl⟩ : syracuseStep 2391857 = 1793893) B1793893
theorem B1343299 : Blo 1060614 1343299 := bstep (se 1 (by rfl) ⟨1007474, by rfl⟩ : syracuseStep 1343299 = 2014949) B2014949
theorem B2391875 : Blo 1060614 2391875 := bstep (se 1 (by rfl) ⟨1793906, by rfl⟩ : syracuseStep 2391875 = 3587813) B3587813
theorem B4030307 : Blo 1060614 4030307 := bstep (se 1 (by rfl) ⟨3022730, by rfl⟩ : syracuseStep 4030307 = 6045461) B6045461
theorem B1343395 : Blo 1060614 1343395 := bstep (se 1 (by rfl) ⟨1007546, by rfl⟩ : syracuseStep 1343395 = 2015093) B2015093
theorem B3407825 : Blo 1060614 3407825 := bstep (se 2 (by rfl) ⟨1277934, by rfl⟩ : syracuseStep 3407825 = 2555869) B2555869
theorem B2392217 : Blo 1060614 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B2392307 : Blo 1060614 2392307 := bstep (se 1 (by rfl) ⟨1794230, by rfl⟩ : syracuseStep 2392307 = 3588461) B3588461
theorem B2392343 : Blo 1060614 2392343 := bstep (se 1 (by rfl) ⟨1794257, by rfl⟩ : syracuseStep 2392343 = 3588515) B3588515
theorem B1704215 : Blo 1060614 1704215 := bstep (se 1 (by rfl) ⟨1278161, by rfl⟩ : syracuseStep 1704215 = 2556323) B2556323
theorem B9077143 : Blo 1060614 9077143 := bstep (se 1 (by rfl) ⟨6807857, by rfl⟩ : syracuseStep 9077143 = 13615715) B13615715
theorem B1343947 : Blo 1060614 1343947 := bstep (se 1 (by rfl) ⟨1007960, by rfl⟩ : syracuseStep 1343947 = 2015921) B2015921
theorem B2392523 : Blo 1060614 2392523 := bstep (se 1 (by rfl) ⟨1794392, by rfl⟩ : syracuseStep 2392523 = 3588785) B3588785
theorem B10224089 : Blo 1060614 10224089 := bstep (se 2 (by rfl) ⟨3834033, by rfl⟩ : syracuseStep 10224089 = 7668067) B7668067
theorem B2392577 : Blo 1060614 2392577 := bstep (se 2 (by rfl) ⟨897216, by rfl⟩ : syracuseStep 2392577 = 1794433) B1794433
theorem B2687539 : Blo 1060614 2687539 := bstep (se 1 (by rfl) ⟨2015654, by rfl⟩ : syracuseStep 2687539 = 4031309) B4031309
theorem B2687681 : Blo 1060614 2687681 := bstep (se 2 (by rfl) ⟨1007880, by rfl⟩ : syracuseStep 2687681 = 2015761) B2015761
theorem B1344215 : Blo 1060614 1344215 := bstep (se 1 (by rfl) ⟨1008161, by rfl⟩ : syracuseStep 1344215 = 2016323) B2016323
theorem B2392793 : Blo 1060614 2392793 := bstep (se 2 (by rfl) ⟨897297, by rfl⟩ : syracuseStep 2392793 = 1794595) B1794595
theorem B2392883 : Blo 1060614 2392883 := bstep (se 1 (by rfl) ⟨1794662, by rfl⟩ : syracuseStep 2392883 = 3589325) B3589325
theorem B2392919 : Blo 1060614 2392919 := bstep (se 1 (by rfl) ⟨1794689, by rfl⟩ : syracuseStep 2392919 = 3589379) B3589379
theorem B5178205 : Blo 1060614 5178205 := bstep (se 3 (by rfl) ⟨970913, by rfl⟩ : syracuseStep 5178205 = 1941827) B1941827
theorem B4031491 : Blo 1060614 4031491 := bstep (se 1 (by rfl) ⟨3023618, by rfl⟩ : syracuseStep 4031491 = 6047237) B6047237
theorem B2393099 : Blo 1060614 2393099 := bstep (se 1 (by rfl) ⟨1794824, by rfl⟩ : syracuseStep 2393099 = 3589649) B3589649
theorem B2393153 : Blo 1060614 2393153 := bstep (se 2 (by rfl) ⟨897432, by rfl⟩ : syracuseStep 2393153 = 1794865) B1794865
theorem B1213547 : Blo 1060614 1213547 := bstep (se 1 (by rfl) ⟨910160, by rfl⟩ : syracuseStep 1213547 = 1820321) B1820321
theorem B2393369 : Blo 1060614 2393369 := bstep (se 2 (by rfl) ⟨897513, by rfl⟩ : syracuseStep 2393369 = 1795027) B1795027
theorem B8062253 : Blo 1060614 8062253 := bstep (se 3 (by rfl) ⟨1511672, by rfl⟩ : syracuseStep 8062253 = 3023345) B3023345
theorem B4031795 : Blo 1060614 4031795 := bstep (se 1 (by rfl) ⟨3023846, by rfl⟩ : syracuseStep 4031795 = 6047693) B6047693
theorem B2393459 : Blo 1060614 2393459 := bstep (se 1 (by rfl) ⟨1795094, by rfl⟩ : syracuseStep 2393459 = 3590189) B3590189
theorem B1344919 : Blo 1060614 1344919 := bstep (se 1 (by rfl) ⟨1008689, by rfl⟩ : syracuseStep 1344919 = 2017379) B2017379
theorem B2393495 : Blo 1060614 2393495 := bstep (se 1 (by rfl) ⟨1795121, by rfl⟩ : syracuseStep 2393495 = 3590243) B3590243
theorem B2393675 : Blo 1060614 2393675 := bstep (se 1 (by rfl) ⟨1795256, by rfl⟩ : syracuseStep 2393675 = 3590513) B3590513
theorem B2393729 : Blo 1060614 2393729 := bstep (se 2 (by rfl) ⟨897648, by rfl⟩ : syracuseStep 2393729 = 1795297) B1795297
theorem B2393945 : Blo 1060614 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B3835793 : Blo 1060614 3835793 := bstep (se 2 (by rfl) ⟨1438422, by rfl⟩ : syracuseStep 3835793 = 2876845) B2876845
theorem B2688947 : Blo 1060614 2688947 := bstep (se 1 (by rfl) ⟨2016710, by rfl⟩ : syracuseStep 2688947 = 4033421) B4033421
theorem B2394035 : Blo 1060614 2394035 := bstep (se 1 (by rfl) ⟨1795526, by rfl⟩ : syracuseStep 2394035 = 3591053) B3591053
theorem B4032449 : Blo 1060614 4032449 := bstep (se 2 (by rfl) ⟨1512168, by rfl⟩ : syracuseStep 4032449 = 3024337) B3024337
theorem B2394071 : Blo 1060614 2394071 := bstep (se 1 (by rfl) ⟨1795553, by rfl⟩ : syracuseStep 2394071 = 3591107) B3591107
theorem B4851757 : Blo 1060614 4851757 := bstep (se 3 (by rfl) ⟨909704, by rfl⟩ : syracuseStep 4851757 = 1819409) B1819409
theorem B5376131 : Blo 1060614 5376131 := bstep (se 1 (by rfl) ⟨4032098, by rfl⟩ : syracuseStep 5376131 = 8064197) B8064197
theorem B2394251 : Blo 1060614 2394251 := bstep (se 1 (by rfl) ⟨1795688, by rfl⟩ : syracuseStep 2394251 = 3591377) B3591377
theorem B2394305 : Blo 1060614 2394305 := bstep (se 2 (by rfl) ⟨897864, by rfl⟩ : syracuseStep 2394305 = 1795729) B1795729
theorem B655591637 : Blo 1060614 655591637 := bstep (se 7 (by rfl) ⟨7682714, by rfl⟩ : syracuseStep 655591637 = 15365429) B15365429
theorem B7276817 : Blo 1060614 7276817 := bstep (se 2 (by rfl) ⟨2728806, by rfl⟩ : syracuseStep 7276817 = 5457613) B5457613
theorem B2394521 : Blo 1060614 2394521 := bstep (se 2 (by rfl) ⟨897945, by rfl⟩ : syracuseStep 2394521 = 1795891) B1795891
theorem B2689483 : Blo 1060614 2689483 := bstep (se 1 (by rfl) ⟨2017112, by rfl⟩ : syracuseStep 2689483 = 4034225) B4034225
theorem B2394611 : Blo 1060614 2394611 := bstep (se 1 (by rfl) ⟨1795958, by rfl⟩ : syracuseStep 2394611 = 3591917) B3591917
theorem B1149431 : Blo 1060614 1149431 := bstep (se 1 (by rfl) ⟨862073, by rfl⟩ : syracuseStep 1149431 = 1724147) B1724147
theorem B2394647 : Blo 1060614 2394647 := bstep (se 1 (by rfl) ⟨1795985, by rfl⟩ : syracuseStep 2394647 = 3591971) B3591971
theorem B2689625 : Blo 1060614 2689625 := bstep (se 2 (by rfl) ⟨1008609, by rfl⟩ : syracuseStep 2689625 = 2017219) B2017219
theorem B2394827 : Blo 1060614 2394827 := bstep (se 1 (by rfl) ⟨1796120, by rfl⟩ : syracuseStep 2394827 = 3592241) B3592241
theorem B2394881 : Blo 1060614 2394881 := bstep (se 2 (by rfl) ⟨898080, by rfl⟩ : syracuseStep 2394881 = 1796161) B1796161
theorem B1510169 : Blo 1060614 1510169 := bstep (se 2 (by rfl) ⟨566313, by rfl⟩ : syracuseStep 1510169 = 1132627) B1132627
theorem B3836717 : Blo 1060614 3836717 := bstep (se 3 (by rfl) ⟨719384, by rfl⟩ : syracuseStep 3836717 = 1438769) B1438769
theorem B1510283 : Blo 1060614 1510283 := bstep (se 1 (by rfl) ⟨1132712, by rfl⟩ : syracuseStep 1510283 = 2265425) B2265425
theorem B2395097 : Blo 1060614 2395097 := bstep (se 2 (by rfl) ⟨898161, by rfl⟩ : syracuseStep 2395097 = 1796323) B1796323
theorem B2395187 : Blo 1060614 2395187 := bstep (se 1 (by rfl) ⟨1796390, by rfl⟩ : syracuseStep 2395187 = 3592781) B3592781
theorem B1346635 : Blo 1060614 1346635 := bstep (se 1 (by rfl) ⟨1009976, by rfl⟩ : syracuseStep 1346635 = 2019953) B2019953
theorem B2395223 : Blo 1060614 2395223 := bstep (se 1 (by rfl) ⟨1796417, by rfl⟩ : syracuseStep 2395223 = 3592835) B3592835
theorem B4033709 : Blo 1060614 4033709 := bstep (se 3 (by rfl) ⟨756320, by rfl⟩ : syracuseStep 4033709 = 1512641) B1512641
theorem B2297011 : Blo 1060614 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B4033739 : Blo 1060614 4033739 := bstep (se 1 (by rfl) ⟨3025304, by rfl⟩ : syracuseStep 4033739 = 6050609) B6050609
theorem B8621387 : Blo 1060614 8621387 := bstep (se 1 (by rfl) ⟨6466040, by rfl⟩ : syracuseStep 8621387 = 12932081) B12932081
theorem B1510807 : Blo 1060614 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B2690455 : Blo 1060614 2690455 := bstep (se 1 (by rfl) ⟨2017841, by rfl⟩ : syracuseStep 2690455 = 4035683) B4035683
theorem B6819545 : Blo 1060614 6819545 := bstep (se 2 (by rfl) ⟨2557329, by rfl⟩ : syracuseStep 6819545 = 5114659) B5114659
theorem B2690891 : Blo 1060614 2690891 := bstep (se 1 (by rfl) ⟨2018168, by rfl⟩ : syracuseStep 2690891 = 4036337) B4036337
theorem B4034393 : Blo 1060614 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B6557591 : Blo 1060614 6557591 := bstep (se 1 (by rfl) ⟨4918193, by rfl⟩ : syracuseStep 6557591 = 9836387) B9836387
theorem B19402787 : Blo 1060614 19402787 := bstep (se 1 (by rfl) ⟨14552090, by rfl⟩ : syracuseStep 19402787 = 29104181) B29104181
theorem B4034711 : Blo 1060614 4034711 := bstep (se 1 (by rfl) ⟨3026033, by rfl⟩ : syracuseStep 4034711 = 6052067) B6052067
theorem B3281075 : Blo 1060614 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B2691265 : Blo 1060614 2691265 := bstep (se 2 (by rfl) ⟨1009224, by rfl⟩ : syracuseStep 2691265 = 2018449) B2018449
theorem B1511627 : Blo 1060614 1511627 := bstep (se 1 (by rfl) ⟨1133720, by rfl⟩ : syracuseStep 1511627 = 2267441) B2267441
theorem B2691863 : Blo 1060614 2691863 := bstep (se 1 (by rfl) ⟨2018897, by rfl⟩ : syracuseStep 2691863 = 4037795) B4037795
theorem B4035379 : Blo 1060614 4035379 := bstep (se 1 (by rfl) ⟨3026534, by rfl⟩ : syracuseStep 4035379 = 6053069) B6053069
theorem B2364299 : Blo 1060614 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B2266177 : Blo 1060614 2266177 := bstep (se 2 (by rfl) ⟨849816, by rfl⟩ : syracuseStep 2266177 = 1699633) B1699633
theorem B8066141 : Blo 1060614 8066141 := bstep (se 3 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 8066141 = 3024803) B3024803
theorem B8623205 : Blo 1060614 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B6821185 : Blo 1060614 6821185 := bstep (se 2 (by rfl) ⟨2557944, by rfl⟩ : syracuseStep 6821185 = 5115889) B5115889
theorem B2692673 : Blo 1060614 2692673 := bstep (se 2 (by rfl) ⟨1009752, by rfl⟩ : syracuseStep 2692673 = 2019505) B2019505
theorem B2266775 : Blo 1060614 2266775 := bstep (se 1 (by rfl) ⟨1700081, by rfl⟩ : syracuseStep 2266775 = 3400163) B3400163
theorem B4855517 : Blo 1060614 4855517 := bstep (se 3 (by rfl) ⟨910409, by rfl⟩ : syracuseStep 4855517 = 1820819) B1820819
theorem B5379857 : Blo 1060614 5379857 := bstep (se 2 (by rfl) ⟨2017446, by rfl⟩ : syracuseStep 5379857 = 4034893) B4034893
theorem B5380019 : Blo 1060614 5380019 := bstep (se 1 (by rfl) ⟨4035014, by rfl⟩ : syracuseStep 5380019 = 8070029) B8070029
theorem B7378867 : Blo 1060614 7378867 := bstep (se 1 (by rfl) ⟨5534150, by rfl⟩ : syracuseStep 7378867 = 11068301) B11068301
theorem B4036625 : Blo 1060614 4036625 := bstep (se 2 (by rfl) ⟨1513734, by rfl⟩ : syracuseStep 4036625 = 3027469) B3027469
theorem B1513495 : Blo 1060614 1513495 := bstep (se 1 (by rfl) ⟨1135121, by rfl⟩ : syracuseStep 1513495 = 2270243) B2270243
theorem B7280705 : Blo 1060614 7280705 := bstep (se 2 (by rfl) ⟨2730264, by rfl⟩ : syracuseStep 7280705 = 5460529) B5460529
theorem B2693209 : Blo 1060614 2693209 := bstep (se 2 (by rfl) ⟨1009953, by rfl⟩ : syracuseStep 2693209 = 2019907) B2019907
theorem B2070785 : Blo 1060614 2070785 := bstep (se 2 (by rfl) ⟨776544, by rfl⟩ : syracuseStep 2070785 = 1553089) B1553089
theorem B32676209 : Blo 1060614 32676209 := bstep (se 2 (by rfl) ⟨12253578, by rfl⟩ : syracuseStep 32676209 = 24507157) B24507157
theorem B2267851 : Blo 1060614 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B4037323 : Blo 1060614 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B3152729 : Blo 1060614 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B12098483 : Blo 1060614 12098483 := bstep (se 1 (by rfl) ⟨9073862, by rfl⟩ : syracuseStep 12098483 = 18147725) B18147725
theorem B1612759 : Blo 1060614 1612759 := bstep (se 1 (by rfl) ⟨1209569, by rfl⟩ : syracuseStep 1612759 = 2419139) B2419139
theorem B4037597 : Blo 1060614 4037597 := bstep (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) B1514099
theorem B2694323 : Blo 1060614 2694323 := bstep (se 1 (by rfl) ⟨2020742, by rfl⟩ : syracuseStep 2694323 = 4041485) B4041485
theorem B1613081 : Blo 1060614 1613081 := bstep (se 2 (by rfl) ⟨604905, by rfl⟩ : syracuseStep 1613081 = 1209811) B1209811
theorem B2268569 : Blo 1060614 2268569 := bstep (se 2 (by rfl) ⟨850713, by rfl⟩ : syracuseStep 2268569 = 1701427) B1701427
theorem B2694617 : Blo 1060614 2694617 := bstep (se 2 (by rfl) ⟨1010481, by rfl⟩ : syracuseStep 2694617 = 2020963) B2020963
theorem B4038295 : Blo 1060614 4038295 := bstep (se 1 (by rfl) ⟨3028721, by rfl⟩ : syracuseStep 4038295 = 6057443) B6057443
theorem B3579713 : Blo 1060614 3579713 := bstep (se 2 (by rfl) ⟨1342392, by rfl⟩ : syracuseStep 3579713 = 2684785) B2684785
theorem B5381963 : Blo 1060614 5381963 := bstep (se 1 (by rfl) ⟨4036472, by rfl⟩ : syracuseStep 5381963 = 8072945) B8072945
theorem B2269081 : Blo 1060614 2269081 := bstep (se 2 (by rfl) ⟨850905, by rfl⟩ : syracuseStep 2269081 = 1701811) B1701811
theorem B2269235 : Blo 1060614 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B3022913 : Blo 1060614 3022913 := bstep (se 2 (by rfl) ⟨1133592, by rfl⟩ : syracuseStep 3022913 = 2267185) B2267185
theorem B3023027 : Blo 1060614 3023027 := bstep (se 1 (by rfl) ⟨2267270, by rfl⟩ : syracuseStep 3023027 = 4534541) B4534541
theorem B2728129 : Blo 1060614 2728129 := bstep (se 2 (by rfl) ⟨1023048, by rfl⟩ : syracuseStep 2728129 = 2046097) B2046097
theorem B3875033 : Blo 1060614 3875033 := bstep (se 2 (by rfl) ⟨1453137, by rfl⟩ : syracuseStep 3875033 = 2906275) B2906275
theorem B3580253 : Blo 1060614 3580253 := bstep (se 3 (by rfl) ⟨671297, by rfl⟩ : syracuseStep 3580253 = 1342595) B1342595
theorem B12099941 : Blo 1060614 12099941 := bstep (se 4 (by rfl) ⟨1134369, by rfl⟩ : syracuseStep 12099941 = 2268739) B2268739
theorem B4039085 : Blo 1060614 4039085 := bstep (se 3 (by rfl) ⟨757328, by rfl⟩ : syracuseStep 4039085 = 1514657) B1514657
theorem B2302553 : Blo 1060614 2302553 := bstep (se 2 (by rfl) ⟨863457, by rfl⟩ : syracuseStep 2302553 = 1726915) B1726915
theorem B2990785 : Blo 1060614 2990785 := bstep (se 2 (by rfl) ⟨1121544, by rfl⟩ : syracuseStep 2990785 = 2243089) B2243089
theorem B3449803 : Blo 1060614 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B2270209 : Blo 1060614 2270209 := bstep (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) B1702657
theorem B46507043 : Blo 1060614 46507043 := bstep (se 1 (by rfl) ⟨34880282, by rfl⟩ : syracuseStep 46507043 = 69760565) B69760565
theorem B2270551 : Blo 1060614 2270551 := bstep (se 1 (by rfl) ⟨1702913, by rfl⟩ : syracuseStep 2270551 = 3405827) B3405827
theorem B4531601 : Blo 1060614 4531601 := bstep (se 2 (by rfl) ⟨1699350, by rfl⟩ : syracuseStep 4531601 = 3398701) B3398701
theorem B3581387 : Blo 1060614 3581387 := bstep (se 1 (by rfl) ⟨2686040, by rfl⟩ : syracuseStep 3581387 = 5372081) B5372081
theorem B5383745 : Blo 1060614 5383745 := bstep (se 2 (by rfl) ⟨2018904, by rfl⟩ : syracuseStep 5383745 = 4037809) B4037809
theorem B2074187 : Blo 1060614 2074187 := bstep (se 1 (by rfl) ⟨1555640, by rfl⟩ : syracuseStep 2074187 = 3111281) B3111281
theorem B3581657 : Blo 1060614 3581657 := bstep (se 2 (by rfl) ⟨1343121, by rfl⟩ : syracuseStep 3581657 = 2686243) B2686243
theorem B2270987 : Blo 1060614 2270987 := bstep (se 1 (by rfl) ⟨1703240, by rfl⟩ : syracuseStep 2270987 = 3406481) B3406481
theorem B4040513 : Blo 1060614 4040513 := bstep (se 2 (by rfl) ⟨1515192, by rfl⟩ : syracuseStep 4040513 = 3030385) B3030385
theorem B4303169 : Blo 1060614 4303169 := bstep (se 2 (by rfl) ⟨1613688, by rfl⟩ : syracuseStep 4303169 = 3227377) B3227377
theorem B3582359 : Blo 1060614 3582359 := bstep (se 1 (by rfl) ⟨2686769, by rfl⟩ : syracuseStep 3582359 = 5373539) B5373539
theorem B6465943 : Blo 1060614 6465943 := bstep (se 1 (by rfl) ⟨4849457, by rfl⟩ : syracuseStep 6465943 = 9698915) B9698915
theorem B4303363 : Blo 1060614 4303363 := bstep (se 1 (by rfl) ⟨3227522, by rfl⟩ : syracuseStep 4303363 = 6455045) B6455045
theorem B13609565 : Blo 1060614 13609565 := bstep (se 3 (by rfl) ⟨2551793, by rfl⟩ : syracuseStep 13609565 = 5103587) B5103587
theorem B4532867 : Blo 1060614 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B2271883 : Blo 1060614 2271883 := bstep (se 1 (by rfl) ⟨1703912, by rfl⟩ : syracuseStep 2271883 = 3407825) B3407825
theorem B1911539 : Blo 1060614 1911539 := bstep (se 1 (by rfl) ⟨1433654, by rfl⟩ : syracuseStep 1911539 = 2867309) B2867309
theorem B9087875 : Blo 1060614 9087875 := bstep (se 1 (by rfl) ⟨6815906, by rfl⟩ : syracuseStep 9087875 = 13631813) B13631813
theorem B3582899 : Blo 1060614 3582899 := bstep (se 1 (by rfl) ⟨2687174, by rfl⟩ : syracuseStep 3582899 = 5374349) B5374349
theorem B3025943 : Blo 1060614 3025943 := bstep (se 1 (by rfl) ⟨2269457, by rfl⟩ : syracuseStep 3025943 = 4538915) B4538915
theorem B6990893 : Blo 1060614 6990893 := bstep (se 3 (by rfl) ⟨1310792, by rfl⟩ : syracuseStep 6990893 = 2621585) B2621585
theorem B3583169 : Blo 1060614 3583169 := bstep (se 2 (by rfl) ⟨1343688, by rfl⟩ : syracuseStep 3583169 = 2687377) B2687377
theorem B4042001 : Blo 1060614 4042001 := bstep (se 2 (by rfl) ⟨1515750, by rfl⟩ : syracuseStep 4042001 = 3031501) B3031501
theorem B1453387 : Blo 1060614 1453387 := bstep (se 1 (by rfl) ⟨1090040, by rfl⟩ : syracuseStep 1453387 = 2180081) B2180081
theorem B2272627 : Blo 1060614 2272627 := bstep (se 1 (by rfl) ⟨1704470, by rfl⟩ : syracuseStep 2272627 = 3408941) B3408941
theorem B9710999 : Blo 1060614 9710999 := bstep (se 1 (by rfl) ⟨7283249, by rfl⟩ : syracuseStep 9710999 = 14566499) B14566499
theorem B5385689 : Blo 1060614 5385689 := bstep (se 2 (by rfl) ⟨2019633, by rfl⟩ : syracuseStep 5385689 = 4039267) B4039267
theorem B31075811 : Blo 1060614 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B3583709 : Blo 1060614 3583709 := bstep (se 3 (by rfl) ⟨671945, by rfl⟩ : syracuseStep 3583709 = 1343891) B1343891
theorem B20459249 : Blo 1060614 20459249 := bstep (se 2 (by rfl) ⟨7672218, by rfl⟩ : syracuseStep 20459249 = 15344437) B15344437
theorem B1912577 : Blo 1060614 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B2043649 : Blo 1060614 2043649 := bstep (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) B1532737
theorem B1060619 : Blo 1060614 1060619 := bstep (se 1 (by rfl) ⟨795464, by rfl⟩ : syracuseStep 1060619 = 1590929) B1590929
theorem B1060631 : Blo 1060614 1060631 := bstep (se 1 (by rfl) ⟨795473, by rfl⟩ : syracuseStep 1060631 = 1590947) B1590947
theorem B1060651 : Blo 1060614 1060651 := bstep (se 1 (by rfl) ⟨795488, by rfl⟩ : syracuseStep 1060651 = 1590977) B1590977
theorem B1060663 : Blo 1060614 1060663 := bstep (se 1 (by rfl) ⟨795497, by rfl⟩ : syracuseStep 1060663 = 1590995) B1590995
theorem B1060683 : Blo 1060614 1060683 := bstep (se 1 (by rfl) ⟨795512, by rfl⟩ : syracuseStep 1060683 = 1591025) B1591025
theorem B1060695 : Blo 1060614 1060695 := bstep (se 1 (by rfl) ⟨795521, by rfl⟩ : syracuseStep 1060695 = 1591043) B1591043
theorem B2273113 : Blo 1060614 2273113 := bstep (se 2 (by rfl) ⟨852417, by rfl⟩ : syracuseStep 2273113 = 1704835) B1704835
theorem B1060715 : Blo 1060614 1060715 := bstep (se 1 (by rfl) ⟨795536, by rfl⟩ : syracuseStep 1060715 = 1591073) B1591073
theorem B1060727 : Blo 1060614 1060727 := bstep (se 1 (by rfl) ⟨795545, by rfl⟩ : syracuseStep 1060727 = 1591091) B1591091
theorem B1060747 : Blo 1060614 1060747 := bstep (se 1 (by rfl) ⟨795560, by rfl⟩ : syracuseStep 1060747 = 1591121) B1591121
theorem B1060759 : Blo 1060614 1060759 := bstep (se 1 (by rfl) ⟨795569, by rfl⟩ : syracuseStep 1060759 = 1591139) B1591139
theorem B1060779 : Blo 1060614 1060779 := bstep (se 1 (by rfl) ⟨795584, by rfl⟩ : syracuseStep 1060779 = 1591169) B1591169
theorem B1060791 : Blo 1060614 1060791 := bstep (se 1 (by rfl) ⟨795593, by rfl⟩ : syracuseStep 1060791 = 1591187) B1591187
theorem B1060811 : Blo 1060614 1060811 := bstep (se 1 (by rfl) ⟨795608, by rfl⟩ : syracuseStep 1060811 = 1591217) B1591217
theorem B1060823 : Blo 1060614 1060823 := bstep (se 1 (by rfl) ⟨795617, by rfl⟩ : syracuseStep 1060823 = 1591235) B1591235
theorem B1060843 : Blo 1060614 1060843 := bstep (se 1 (by rfl) ⟨795632, by rfl⟩ : syracuseStep 1060843 = 1591265) B1591265
theorem B1060855 : Blo 1060614 1060855 := bstep (se 1 (by rfl) ⟨795641, by rfl⟩ : syracuseStep 1060855 = 1591283) B1591283
theorem B1060875 : Blo 1060614 1060875 := bstep (se 1 (by rfl) ⟨795656, by rfl⟩ : syracuseStep 1060875 = 1591313) B1591313
theorem B1060887 : Blo 1060614 1060887 := bstep (se 1 (by rfl) ⟨795665, by rfl⟩ : syracuseStep 1060887 = 1591331) B1591331
theorem B1060907 : Blo 1060614 1060907 := bstep (se 1 (by rfl) ⟨795680, by rfl⟩ : syracuseStep 1060907 = 1591361) B1591361
theorem B1060919 : Blo 1060614 1060919 := bstep (se 1 (by rfl) ⟨795689, by rfl⟩ : syracuseStep 1060919 = 1591379) B1591379
theorem B1060939 : Blo 1060614 1060939 := bstep (se 1 (by rfl) ⟨795704, by rfl⟩ : syracuseStep 1060939 = 1591409) B1591409
theorem B1060951 : Blo 1060614 1060951 := bstep (se 1 (by rfl) ⟨795713, by rfl⟩ : syracuseStep 1060951 = 1591427) B1591427
theorem B1060971 : Blo 1060614 1060971 := bstep (se 1 (by rfl) ⟨795728, by rfl⟩ : syracuseStep 1060971 = 1591457) B1591457
theorem B1060983 : Blo 1060614 1060983 := bstep (se 1 (by rfl) ⟨795737, by rfl⟩ : syracuseStep 1060983 = 1591475) B1591475
theorem B1061003 : Blo 1060614 1061003 := bstep (se 1 (by rfl) ⟨795752, by rfl⟩ : syracuseStep 1061003 = 1591505) B1591505
theorem B1061015 : Blo 1060614 1061015 := bstep (se 1 (by rfl) ⟨795761, by rfl⟩ : syracuseStep 1061015 = 1591523) B1591523
theorem B1061035 : Blo 1060614 1061035 := bstep (se 1 (by rfl) ⟨795776, by rfl⟩ : syracuseStep 1061035 = 1591553) B1591553
theorem B1061047 : Blo 1060614 1061047 := bstep (se 1 (by rfl) ⟨795785, by rfl⟩ : syracuseStep 1061047 = 1591571) B1591571
theorem B1061067 : Blo 1060614 1061067 := bstep (se 1 (by rfl) ⟨795800, by rfl⟩ : syracuseStep 1061067 = 1591601) B1591601
theorem B1061079 : Blo 1060614 1061079 := bstep (se 1 (by rfl) ⟨795809, by rfl⟩ : syracuseStep 1061079 = 1591619) B1591619
theorem B1061099 : Blo 1060614 1061099 := bstep (se 1 (by rfl) ⟨795824, by rfl⟩ : syracuseStep 1061099 = 1591649) B1591649
theorem B1061111 : Blo 1060614 1061111 := bstep (se 1 (by rfl) ⟨795833, by rfl⟩ : syracuseStep 1061111 = 1591667) B1591667
theorem B1061131 : Blo 1060614 1061131 := bstep (se 1 (by rfl) ⟨795848, by rfl⟩ : syracuseStep 1061131 = 1591697) B1591697
theorem B1061143 : Blo 1060614 1061143 := bstep (se 1 (by rfl) ⟨795857, by rfl⟩ : syracuseStep 1061143 = 1591715) B1591715
theorem B1061163 : Blo 1060614 1061163 := bstep (se 1 (by rfl) ⟨795872, by rfl⟩ : syracuseStep 1061163 = 1591745) B1591745
theorem B6893869 : Blo 1060614 6893869 := bstep (se 3 (by rfl) ⟨1292600, by rfl⟩ : syracuseStep 6893869 = 2585201) B2585201
theorem B1061175 : Blo 1060614 1061175 := bstep (se 1 (by rfl) ⟨795881, by rfl⟩ : syracuseStep 1061175 = 1591763) B1591763
theorem B1061195 : Blo 1060614 1061195 := bstep (se 1 (by rfl) ⟨795896, by rfl⟩ : syracuseStep 1061195 = 1591793) B1591793
theorem B1061207 : Blo 1060614 1061207 := bstep (se 1 (by rfl) ⟨795905, by rfl⟩ : syracuseStep 1061207 = 1591811) B1591811
theorem B1061227 : Blo 1060614 1061227 := bstep (se 1 (by rfl) ⟨795920, by rfl⟩ : syracuseStep 1061227 = 1591841) B1591841
theorem B1061239 : Blo 1060614 1061239 := bstep (se 1 (by rfl) ⟨795929, by rfl⟩ : syracuseStep 1061239 = 1591859) B1591859
theorem B1061259 : Blo 1060614 1061259 := bstep (se 1 (by rfl) ⟨795944, by rfl⟩ : syracuseStep 1061259 = 1591889) B1591889
theorem B1061271 : Blo 1060614 1061271 := bstep (se 1 (by rfl) ⟨795953, by rfl⟩ : syracuseStep 1061271 = 1591907) B1591907
theorem B1061291 : Blo 1060614 1061291 := bstep (se 1 (by rfl) ⟨795968, by rfl⟩ : syracuseStep 1061291 = 1591937) B1591937
theorem B1061303 : Blo 1060614 1061303 := bstep (se 1 (by rfl) ⟨795977, by rfl⟩ : syracuseStep 1061303 = 1591955) B1591955
theorem B1061323 : Blo 1060614 1061323 := bstep (se 1 (by rfl) ⟨795992, by rfl⟩ : syracuseStep 1061323 = 1591985) B1591985
theorem B1061335 : Blo 1060614 1061335 := bstep (se 1 (by rfl) ⟨796001, by rfl⟩ : syracuseStep 1061335 = 1592003) B1592003
theorem B1061355 : Blo 1060614 1061355 := bstep (se 1 (by rfl) ⟨796016, by rfl⟩ : syracuseStep 1061355 = 1592033) B1592033
theorem B1061367 : Blo 1060614 1061367 := bstep (se 1 (by rfl) ⟨796025, by rfl⟩ : syracuseStep 1061367 = 1592051) B1592051
theorem B1061387 : Blo 1060614 1061387 := bstep (se 1 (by rfl) ⟨796040, by rfl⟩ : syracuseStep 1061387 = 1592081) B1592081
theorem B1061399 : Blo 1060614 1061399 := bstep (se 1 (by rfl) ⟨796049, by rfl⟩ : syracuseStep 1061399 = 1592099) B1592099
theorem B1061419 : Blo 1060614 1061419 := bstep (se 1 (by rfl) ⟨796064, by rfl⟩ : syracuseStep 1061419 = 1592129) B1592129
theorem B1061431 : Blo 1060614 1061431 := bstep (se 1 (by rfl) ⟨796073, by rfl⟩ : syracuseStep 1061431 = 1592147) B1592147
theorem B1061451 : Blo 1060614 1061451 := bstep (se 1 (by rfl) ⟨796088, by rfl⟩ : syracuseStep 1061451 = 1592177) B1592177
theorem B1061463 : Blo 1060614 1061463 := bstep (se 1 (by rfl) ⟨796097, by rfl⟩ : syracuseStep 1061463 = 1592195) B1592195
theorem B1061483 : Blo 1060614 1061483 := bstep (se 1 (by rfl) ⟨796112, by rfl⟩ : syracuseStep 1061483 = 1592225) B1592225
theorem B1061495 : Blo 1060614 1061495 := bstep (se 1 (by rfl) ⟨796121, by rfl⟩ : syracuseStep 1061495 = 1592243) B1592243
theorem B1061515 : Blo 1060614 1061515 := bstep (se 1 (by rfl) ⟨796136, by rfl⟩ : syracuseStep 1061515 = 1592273) B1592273
theorem B1061527 : Blo 1060614 1061527 := bstep (se 1 (by rfl) ⟨796145, by rfl⟩ : syracuseStep 1061527 = 1592291) B1592291
theorem B1061547 : Blo 1060614 1061547 := bstep (se 1 (by rfl) ⟨796160, by rfl⟩ : syracuseStep 1061547 = 1592321) B1592321
theorem B1061559 : Blo 1060614 1061559 := bstep (se 1 (by rfl) ⟨796169, by rfl⟩ : syracuseStep 1061559 = 1592339) B1592339
theorem B1061579 : Blo 1060614 1061579 := bstep (se 1 (by rfl) ⟨796184, by rfl⟩ : syracuseStep 1061579 = 1592369) B1592369
theorem B1061591 : Blo 1060614 1061591 := bstep (se 1 (by rfl) ⟨796193, by rfl⟩ : syracuseStep 1061591 = 1592387) B1592387
theorem B1061611 : Blo 1060614 1061611 := bstep (se 1 (by rfl) ⟨796208, by rfl⟩ : syracuseStep 1061611 = 1592417) B1592417
theorem B1061623 : Blo 1060614 1061623 := bstep (se 1 (by rfl) ⟨796217, by rfl⟩ : syracuseStep 1061623 = 1592435) B1592435
theorem B1061643 : Blo 1060614 1061643 := bstep (se 1 (by rfl) ⟨796232, by rfl⟩ : syracuseStep 1061643 = 1592465) B1592465
theorem B1061655 : Blo 1060614 1061655 := bstep (se 1 (by rfl) ⟨796241, by rfl⟩ : syracuseStep 1061655 = 1592483) B1592483
theorem B1061675 : Blo 1060614 1061675 := bstep (se 1 (by rfl) ⟨796256, by rfl⟩ : syracuseStep 1061675 = 1592513) B1592513
theorem B1061687 : Blo 1060614 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B1061707 : Blo 1060614 1061707 := bstep (se 1 (by rfl) ⟨796280, by rfl⟩ : syracuseStep 1061707 = 1592561) B1592561
theorem B3584843 : Blo 1060614 3584843 := bstep (se 1 (by rfl) ⟨2688632, by rfl⟩ : syracuseStep 3584843 = 5377265) B5377265
theorem B1061719 : Blo 1060614 1061719 := bstep (se 1 (by rfl) ⟨796289, by rfl⟩ : syracuseStep 1061719 = 1592579) B1592579
theorem B1061739 : Blo 1060614 1061739 := bstep (se 1 (by rfl) ⟨796304, by rfl⟩ : syracuseStep 1061739 = 1592609) B1592609
theorem B1061751 : Blo 1060614 1061751 := bstep (se 1 (by rfl) ⟨796313, by rfl⟩ : syracuseStep 1061751 = 1592627) B1592627
theorem B1061771 : Blo 1060614 1061771 := bstep (se 1 (by rfl) ⟨796328, by rfl⟩ : syracuseStep 1061771 = 1592657) B1592657
theorem B1061783 : Blo 1060614 1061783 := bstep (se 1 (by rfl) ⟨796337, by rfl⟩ : syracuseStep 1061783 = 1592675) B1592675
theorem B1061803 : Blo 1060614 1061803 := bstep (se 1 (by rfl) ⟨796352, by rfl⟩ : syracuseStep 1061803 = 1592705) B1592705
theorem B1061815 : Blo 1060614 1061815 := bstep (se 1 (by rfl) ⟨796361, by rfl⟩ : syracuseStep 1061815 = 1592723) B1592723
theorem B1061835 : Blo 1060614 1061835 := bstep (se 1 (by rfl) ⟨796376, by rfl⟩ : syracuseStep 1061835 = 1592753) B1592753
theorem B1061847 : Blo 1060614 1061847 := bstep (se 1 (by rfl) ⟨796385, by rfl⟩ : syracuseStep 1061847 = 1592771) B1592771
theorem B4371421 : Blo 1060614 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B1061867 : Blo 1060614 1061867 := bstep (se 1 (by rfl) ⟨796400, by rfl⟩ : syracuseStep 1061867 = 1592801) B1592801
theorem B1061879 : Blo 1060614 1061879 := bstep (se 1 (by rfl) ⟨796409, by rfl⟩ : syracuseStep 1061879 = 1592819) B1592819
theorem B1061899 : Blo 1060614 1061899 := bstep (se 1 (by rfl) ⟨796424, by rfl⟩ : syracuseStep 1061899 = 1592849) B1592849
theorem B10204177 : Blo 1060614 10204177 := bstep (se 2 (by rfl) ⟨3826566, by rfl⟩ : syracuseStep 10204177 = 7653133) B7653133
theorem B1061911 : Blo 1060614 1061911 := bstep (se 1 (by rfl) ⟨796433, by rfl⟩ : syracuseStep 1061911 = 1592867) B1592867
theorem B1061931 : Blo 1060614 1061931 := bstep (se 1 (by rfl) ⟨796448, by rfl⟩ : syracuseStep 1061931 = 1592897) B1592897
theorem B5387309 : Blo 1060614 5387309 := bstep (se 3 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 5387309 = 2020241) B2020241
theorem B1061943 : Blo 1060614 1061943 := bstep (se 1 (by rfl) ⟨796457, by rfl⟩ : syracuseStep 1061943 = 1592915) B1592915
theorem B1061963 : Blo 1060614 1061963 := bstep (se 1 (by rfl) ⟨796472, by rfl⟩ : syracuseStep 1061963 = 1592945) B1592945
theorem B1061975 : Blo 1060614 1061975 := bstep (se 1 (by rfl) ⟨796481, by rfl⟩ : syracuseStep 1061975 = 1592963) B1592963
theorem B3585113 : Blo 1060614 3585113 := bstep (se 2 (by rfl) ⟨1344417, by rfl⟩ : syracuseStep 3585113 = 2688835) B2688835
theorem B1061995 : Blo 1060614 1061995 := bstep (se 1 (by rfl) ⟨796496, by rfl⟩ : syracuseStep 1061995 = 1592993) B1592993
theorem B1062007 : Blo 1060614 1062007 := bstep (se 1 (by rfl) ⟨796505, by rfl⟩ : syracuseStep 1062007 = 1593011) B1593011
theorem B1062027 : Blo 1060614 1062027 := bstep (se 1 (by rfl) ⟨796520, by rfl⟩ : syracuseStep 1062027 = 1593041) B1593041
theorem B1062039 : Blo 1060614 1062039 := bstep (se 1 (by rfl) ⟨796529, by rfl⟩ : syracuseStep 1062039 = 1593059) B1593059
theorem B1062059 : Blo 1060614 1062059 := bstep (se 1 (by rfl) ⟨796544, by rfl⟩ : syracuseStep 1062059 = 1593089) B1593089
theorem B1062071 : Blo 1060614 1062071 := bstep (se 1 (by rfl) ⟨796553, by rfl⟩ : syracuseStep 1062071 = 1593107) B1593107
theorem B1062091 : Blo 1060614 1062091 := bstep (se 1 (by rfl) ⟨796568, by rfl⟩ : syracuseStep 1062091 = 1593137) B1593137
theorem B1062103 : Blo 1060614 1062103 := bstep (se 1 (by rfl) ⟨796577, by rfl⟩ : syracuseStep 1062103 = 1593155) B1593155
theorem B9090265 : Blo 1060614 9090265 := bstep (se 2 (by rfl) ⟨3408849, by rfl⟩ : syracuseStep 9090265 = 6817699) B6817699
theorem B1062123 : Blo 1060614 1062123 := bstep (se 1 (by rfl) ⟨796592, by rfl⟩ : syracuseStep 1062123 = 1593185) B1593185
theorem B1062135 : Blo 1060614 1062135 := bstep (se 1 (by rfl) ⟨796601, by rfl⟩ : syracuseStep 1062135 = 1593203) B1593203
theorem B20428037 : Blo 1060614 20428037 := bstep (se 4 (by rfl) ⟨1915128, by rfl⟩ : syracuseStep 20428037 = 3830257) B3830257
theorem B1062155 : Blo 1060614 1062155 := bstep (se 1 (by rfl) ⟨796616, by rfl⟩ : syracuseStep 1062155 = 1593233) B1593233
theorem B1062167 : Blo 1060614 1062167 := bstep (se 1 (by rfl) ⟨796625, by rfl⟩ : syracuseStep 1062167 = 1593251) B1593251
theorem B1062187 : Blo 1060614 1062187 := bstep (se 1 (by rfl) ⟨796640, by rfl⟩ : syracuseStep 1062187 = 1593281) B1593281
theorem B1062199 : Blo 1060614 1062199 := bstep (se 1 (by rfl) ⟨796649, by rfl⟩ : syracuseStep 1062199 = 1593299) B1593299
theorem B7648577 : Blo 1060614 7648577 := bstep (se 2 (by rfl) ⟨2868216, by rfl⟩ : syracuseStep 7648577 = 5736433) B5736433
theorem B1062219 : Blo 1060614 1062219 := bstep (se 1 (by rfl) ⟨796664, by rfl⟩ : syracuseStep 1062219 = 1593329) B1593329
theorem B1062231 : Blo 1060614 1062231 := bstep (se 1 (by rfl) ⟨796673, by rfl⟩ : syracuseStep 1062231 = 1593347) B1593347
theorem B11482469 : Blo 1060614 11482469 := bstep (se 4 (by rfl) ⟨1076481, by rfl⟩ : syracuseStep 11482469 = 2152963) B2152963
theorem B1193323 : Blo 1060614 1193323 := bstep (se 1 (by rfl) ⟨894992, by rfl⟩ : syracuseStep 1193323 = 1789985) B1789985
theorem B1062251 : Blo 1060614 1062251 := bstep (se 1 (by rfl) ⟨796688, by rfl⟩ : syracuseStep 1062251 = 1593377) B1593377
theorem B1062263 : Blo 1060614 1062263 := bstep (se 1 (by rfl) ⟨796697, by rfl⟩ : syracuseStep 1062263 = 1593395) B1593395
theorem B1062283 : Blo 1060614 1062283 := bstep (se 1 (by rfl) ⟨796712, by rfl⟩ : syracuseStep 1062283 = 1593425) B1593425
theorem B1062295 : Blo 1060614 1062295 := bstep (se 1 (by rfl) ⟨796721, by rfl⟩ : syracuseStep 1062295 = 1593443) B1593443
theorem B1062315 : Blo 1060614 1062315 := bstep (se 1 (by rfl) ⟨796736, by rfl⟩ : syracuseStep 1062315 = 1593473) B1593473
theorem B3028403 : Blo 1060614 3028403 := bstep (se 1 (by rfl) ⟨2271302, by rfl⟩ : syracuseStep 3028403 = 4542605) B4542605
theorem B1062327 : Blo 1060614 1062327 := bstep (se 1 (by rfl) ⟨796745, by rfl⟩ : syracuseStep 1062327 = 1593491) B1593491
theorem B1062347 : Blo 1060614 1062347 := bstep (se 1 (by rfl) ⟨796760, by rfl⟩ : syracuseStep 1062347 = 1593521) B1593521
theorem B1193431 : Blo 1060614 1193431 := bstep (se 1 (by rfl) ⟨895073, by rfl⟩ : syracuseStep 1193431 = 1790147) B1790147
theorem B1062359 : Blo 1060614 1062359 := bstep (se 1 (by rfl) ⟨796769, by rfl⟩ : syracuseStep 1062359 = 1593539) B1593539
theorem B1062379 : Blo 1060614 1062379 := bstep (se 1 (by rfl) ⟨796784, by rfl⟩ : syracuseStep 1062379 = 1593569) B1593569
theorem B1062391 : Blo 1060614 1062391 := bstep (se 1 (by rfl) ⟨796793, by rfl⟩ : syracuseStep 1062391 = 1593587) B1593587
theorem B1062411 : Blo 1060614 1062411 := bstep (se 1 (by rfl) ⟨796808, by rfl⟩ : syracuseStep 1062411 = 1593617) B1593617
theorem B1062423 : Blo 1060614 1062423 := bstep (se 1 (by rfl) ⟨796817, by rfl⟩ : syracuseStep 1062423 = 1593635) B1593635
theorem B1062443 : Blo 1060614 1062443 := bstep (se 1 (by rfl) ⟨796832, by rfl⟩ : syracuseStep 1062443 = 1593665) B1593665
theorem B1062455 : Blo 1060614 1062455 := bstep (se 1 (by rfl) ⟨796841, by rfl⟩ : syracuseStep 1062455 = 1593683) B1593683
theorem B18134603 : Blo 1060614 18134603 := bstep (se 1 (by rfl) ⟨13600952, by rfl⟩ : syracuseStep 18134603 = 27201905) B27201905
theorem B1062475 : Blo 1060614 1062475 := bstep (se 1 (by rfl) ⟨796856, by rfl⟩ : syracuseStep 1062475 = 1593713) B1593713
theorem B1062487 : Blo 1060614 1062487 := bstep (se 1 (by rfl) ⟨796865, by rfl⟩ : syracuseStep 1062487 = 1593731) B1593731
theorem B1062507 : Blo 1060614 1062507 := bstep (se 1 (by rfl) ⟨796880, by rfl⟩ : syracuseStep 1062507 = 1593761) B1593761
theorem B1062519 : Blo 1060614 1062519 := bstep (se 1 (by rfl) ⟨796889, by rfl⟩ : syracuseStep 1062519 = 1593779) B1593779
theorem B1193611 : Blo 1060614 1193611 := bstep (se 1 (by rfl) ⟨895208, by rfl⟩ : syracuseStep 1193611 = 1790417) B1790417
theorem B1062539 : Blo 1060614 1062539 := bstep (se 1 (by rfl) ⟨796904, by rfl⟩ : syracuseStep 1062539 = 1593809) B1593809
theorem B4535959 : Blo 1060614 4535959 := bstep (se 1 (by rfl) ⟨3401969, by rfl⟩ : syracuseStep 4535959 = 6803939) B6803939
theorem B1062551 : Blo 1060614 1062551 := bstep (se 1 (by rfl) ⟨796913, by rfl⟩ : syracuseStep 1062551 = 1593827) B1593827
theorem B1062571 : Blo 1060614 1062571 := bstep (se 1 (by rfl) ⟨796928, by rfl⟩ : syracuseStep 1062571 = 1593857) B1593857
theorem B1062583 : Blo 1060614 1062583 := bstep (se 1 (by rfl) ⟨796937, by rfl⟩ : syracuseStep 1062583 = 1593875) B1593875
theorem B1062603 : Blo 1060614 1062603 := bstep (se 1 (by rfl) ⟨796952, by rfl⟩ : syracuseStep 1062603 = 1593905) B1593905
theorem B1062615 : Blo 1060614 1062615 := bstep (se 1 (by rfl) ⟨796961, by rfl⟩ : syracuseStep 1062615 = 1593923) B1593923
theorem B1062635 : Blo 1060614 1062635 := bstep (se 1 (by rfl) ⟨796976, by rfl⟩ : syracuseStep 1062635 = 1593953) B1593953
theorem B1193719 : Blo 1060614 1193719 := bstep (se 1 (by rfl) ⟨895289, by rfl⟩ : syracuseStep 1193719 = 1790579) B1790579
theorem B1062647 : Blo 1060614 1062647 := bstep (se 1 (by rfl) ⟨796985, by rfl⟩ : syracuseStep 1062647 = 1593971) B1593971
theorem B1062667 : Blo 1060614 1062667 := bstep (se 1 (by rfl) ⟨797000, by rfl⟩ : syracuseStep 1062667 = 1594001) B1594001
theorem B3585815 : Blo 1060614 3585815 := bstep (se 1 (by rfl) ⟨2689361, by rfl⟩ : syracuseStep 3585815 = 5378723) B5378723
theorem B1062679 : Blo 1060614 1062679 := bstep (se 1 (by rfl) ⟨797009, by rfl⟩ : syracuseStep 1062679 = 1594019) B1594019
theorem B1062699 : Blo 1060614 1062699 := bstep (se 1 (by rfl) ⟨797024, by rfl⟩ : syracuseStep 1062699 = 1594049) B1594049
theorem B1062711 : Blo 1060614 1062711 := bstep (se 1 (by rfl) ⟨797033, by rfl⟩ : syracuseStep 1062711 = 1594067) B1594067
theorem B1062731 : Blo 1060614 1062731 := bstep (se 1 (by rfl) ⟨797048, by rfl⟩ : syracuseStep 1062731 = 1594097) B1594097
theorem B1062743 : Blo 1060614 1062743 := bstep (se 1 (by rfl) ⟨797057, by rfl⟩ : syracuseStep 1062743 = 1594115) B1594115
theorem B1062763 : Blo 1060614 1062763 := bstep (se 1 (by rfl) ⟨797072, by rfl⟩ : syracuseStep 1062763 = 1594145) B1594145
theorem B1062775 : Blo 1060614 1062775 := bstep (se 1 (by rfl) ⟨797081, by rfl⟩ : syracuseStep 1062775 = 1594163) B1594163
theorem B1062795 : Blo 1060614 1062795 := bstep (se 1 (by rfl) ⟨797096, by rfl⟩ : syracuseStep 1062795 = 1594193) B1594193
theorem B1062807 : Blo 1060614 1062807 := bstep (se 1 (by rfl) ⟨797105, by rfl⟩ : syracuseStep 1062807 = 1594211) B1594211
theorem B1193899 : Blo 1060614 1193899 := bstep (se 1 (by rfl) ⟨895424, by rfl⟩ : syracuseStep 1193899 = 1790849) B1790849
theorem B1062827 : Blo 1060614 1062827 := bstep (se 1 (by rfl) ⟨797120, by rfl⟩ : syracuseStep 1062827 = 1594241) B1594241
theorem B6043571 : Blo 1060614 6043571 := bstep (se 1 (by rfl) ⟨4532678, by rfl⟩ : syracuseStep 6043571 = 9065357) B9065357
theorem B1062839 : Blo 1060614 1062839 := bstep (se 1 (by rfl) ⟨797129, by rfl⟩ : syracuseStep 1062839 = 1594259) B1594259
theorem B1062859 : Blo 1060614 1062859 := bstep (se 1 (by rfl) ⟨797144, by rfl⟩ : syracuseStep 1062859 = 1594289) B1594289
theorem B1062871 : Blo 1060614 1062871 := bstep (se 1 (by rfl) ⟨797153, by rfl⟩ : syracuseStep 1062871 = 1594307) B1594307
theorem B1062891 : Blo 1060614 1062891 := bstep (se 1 (by rfl) ⟨797168, by rfl⟩ : syracuseStep 1062891 = 1594337) B1594337
theorem B1062903 : Blo 1060614 1062903 := bstep (se 1 (by rfl) ⟨797177, by rfl⟩ : syracuseStep 1062903 = 1594355) B1594355
theorem B1062923 : Blo 1060614 1062923 := bstep (se 1 (by rfl) ⟨797192, by rfl⟩ : syracuseStep 1062923 = 1594385) B1594385
theorem B1194007 : Blo 1060614 1194007 := bstep (se 1 (by rfl) ⟨895505, by rfl⟩ : syracuseStep 1194007 = 1791011) B1791011
theorem B1062935 : Blo 1060614 1062935 := bstep (se 1 (by rfl) ⟨797201, by rfl⟩ : syracuseStep 1062935 = 1594403) B1594403
theorem B1062955 : Blo 1060614 1062955 := bstep (se 1 (by rfl) ⟨797216, by rfl⟩ : syracuseStep 1062955 = 1594433) B1594433
theorem B1062967 : Blo 1060614 1062967 := bstep (se 1 (by rfl) ⟨797225, by rfl⟩ : syracuseStep 1062967 = 1594451) B1594451
theorem B18626635 : Blo 1060614 18626635 := bstep (se 1 (by rfl) ⟨13969976, by rfl⟩ : syracuseStep 18626635 = 27939953) B27939953
theorem B1062987 : Blo 1060614 1062987 := bstep (se 1 (by rfl) ⟨797240, by rfl⟩ : syracuseStep 1062987 = 1594481) B1594481
theorem B1062999 : Blo 1060614 1062999 := bstep (se 1 (by rfl) ⟨797249, by rfl⟩ : syracuseStep 1062999 = 1594499) B1594499
theorem B1063019 : Blo 1060614 1063019 := bstep (se 1 (by rfl) ⟨797264, by rfl⟩ : syracuseStep 1063019 = 1594529) B1594529
theorem B1063031 : Blo 1060614 1063031 := bstep (se 1 (by rfl) ⟨797273, by rfl⟩ : syracuseStep 1063031 = 1594547) B1594547
theorem B1063051 : Blo 1060614 1063051 := bstep (se 1 (by rfl) ⟨797288, by rfl⟩ : syracuseStep 1063051 = 1594577) B1594577
theorem B1063063 : Blo 1060614 1063063 := bstep (se 1 (by rfl) ⟨797297, by rfl⟩ : syracuseStep 1063063 = 1594595) B1594595
theorem B9091223 : Blo 1060614 9091223 := bstep (se 1 (by rfl) ⟨6818417, by rfl⟩ : syracuseStep 9091223 = 13636835) B13636835
theorem B1063083 : Blo 1060614 1063083 := bstep (se 1 (by rfl) ⟨797312, by rfl⟩ : syracuseStep 1063083 = 1594625) B1594625
theorem B1063095 : Blo 1060614 1063095 := bstep (se 1 (by rfl) ⟨797321, by rfl⟩ : syracuseStep 1063095 = 1594643) B1594643
theorem B1194187 : Blo 1060614 1194187 := bstep (se 1 (by rfl) ⟨895640, by rfl⟩ : syracuseStep 1194187 = 1791281) B1791281
theorem B1063115 : Blo 1060614 1063115 := bstep (se 1 (by rfl) ⟨797336, by rfl⟩ : syracuseStep 1063115 = 1594673) B1594673
theorem B1063127 : Blo 1060614 1063127 := bstep (se 1 (by rfl) ⟨797345, by rfl⟩ : syracuseStep 1063127 = 1594691) B1594691
theorem B1063147 : Blo 1060614 1063147 := bstep (se 1 (by rfl) ⟨797360, by rfl⟩ : syracuseStep 1063147 = 1594721) B1594721
theorem B1063159 : Blo 1060614 1063159 := bstep (se 1 (by rfl) ⟨797369, by rfl⟩ : syracuseStep 1063159 = 1594739) B1594739
theorem B1063179 : Blo 1060614 1063179 := bstep (se 1 (by rfl) ⟨797384, by rfl⟩ : syracuseStep 1063179 = 1594769) B1594769
theorem B1063191 : Blo 1060614 1063191 := bstep (se 1 (by rfl) ⟨797393, by rfl⟩ : syracuseStep 1063191 = 1594787) B1594787
theorem B1063211 : Blo 1060614 1063211 := bstep (se 1 (by rfl) ⟨797408, by rfl⟩ : syracuseStep 1063211 = 1594817) B1594817
theorem B3586355 : Blo 1060614 3586355 := bstep (se 1 (by rfl) ⟨2689766, by rfl⟩ : syracuseStep 3586355 = 5379533) B5379533
theorem B1194295 : Blo 1060614 1194295 := bstep (se 1 (by rfl) ⟨895721, by rfl⟩ : syracuseStep 1194295 = 1791443) B1791443
theorem B1063223 : Blo 1060614 1063223 := bstep (se 1 (by rfl) ⟨797417, by rfl⟩ : syracuseStep 1063223 = 1594835) B1594835
theorem B1063243 : Blo 1060614 1063243 := bstep (se 1 (by rfl) ⟨797432, by rfl⟩ : syracuseStep 1063243 = 1594865) B1594865
theorem B1063255 : Blo 1060614 1063255 := bstep (se 1 (by rfl) ⟨797441, by rfl⟩ : syracuseStep 1063255 = 1594883) B1594883
theorem B1063275 : Blo 1060614 1063275 := bstep (se 1 (by rfl) ⟨797456, by rfl⟩ : syracuseStep 1063275 = 1594913) B1594913
theorem B1063287 : Blo 1060614 1063287 := bstep (se 1 (by rfl) ⟨797465, by rfl⟩ : syracuseStep 1063287 = 1594931) B1594931
theorem B1063307 : Blo 1060614 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B1063319 : Blo 1060614 1063319 := bstep (se 1 (by rfl) ⟨797489, by rfl⟩ : syracuseStep 1063319 = 1594979) B1594979
theorem B2046359 : Blo 1060614 2046359 := bstep (se 1 (by rfl) ⟨1534769, by rfl⟩ : syracuseStep 2046359 = 3069539) B3069539
theorem B1063339 : Blo 1060614 1063339 := bstep (se 1 (by rfl) ⟨797504, by rfl⟩ : syracuseStep 1063339 = 1595009) B1595009
theorem B1063351 : Blo 1060614 1063351 := bstep (se 1 (by rfl) ⟨797513, by rfl⟩ : syracuseStep 1063351 = 1595027) B1595027
theorem B1063371 : Blo 1060614 1063371 := bstep (se 1 (by rfl) ⟨797528, by rfl⟩ : syracuseStep 1063371 = 1595057) B1595057
theorem B1063383 : Blo 1060614 1063383 := bstep (se 1 (by rfl) ⟨797537, by rfl⟩ : syracuseStep 1063383 = 1595075) B1595075
theorem B1194475 : Blo 1060614 1194475 := bstep (se 1 (by rfl) ⟨895856, by rfl⟩ : syracuseStep 1194475 = 1791713) B1791713
theorem B1063403 : Blo 1060614 1063403 := bstep (se 1 (by rfl) ⟨797552, by rfl⟩ : syracuseStep 1063403 = 1595105) B1595105
theorem B1063415 : Blo 1060614 1063415 := bstep (se 1 (by rfl) ⟨797561, by rfl⟩ : syracuseStep 1063415 = 1595123) B1595123
theorem B1063435 : Blo 1060614 1063435 := bstep (se 1 (by rfl) ⟨797576, by rfl⟩ : syracuseStep 1063435 = 1595153) B1595153
theorem B9091601 : Blo 1060614 9091601 := bstep (se 2 (by rfl) ⟨3409350, by rfl⟩ : syracuseStep 9091601 = 6818701) B6818701
theorem B1063447 : Blo 1060614 1063447 := bstep (se 1 (by rfl) ⟨797585, by rfl⟩ : syracuseStep 1063447 = 1595171) B1595171
theorem B1063467 : Blo 1060614 1063467 := bstep (se 1 (by rfl) ⟨797600, by rfl⟩ : syracuseStep 1063467 = 1595201) B1595201
theorem B1063479 : Blo 1060614 1063479 := bstep (se 1 (by rfl) ⟨797609, by rfl⟩ : syracuseStep 1063479 = 1595219) B1595219
theorem B3586625 : Blo 1060614 3586625 := bstep (se 2 (by rfl) ⟨1344984, by rfl⟩ : syracuseStep 3586625 = 2689969) B2689969
theorem B1063499 : Blo 1060614 1063499 := bstep (se 1 (by rfl) ⟨797624, by rfl⟩ : syracuseStep 1063499 = 1595249) B1595249
theorem B1194583 : Blo 1060614 1194583 := bstep (se 1 (by rfl) ⟨895937, by rfl⟩ : syracuseStep 1194583 = 1791875) B1791875
theorem B1063511 : Blo 1060614 1063511 := bstep (se 1 (by rfl) ⟨797633, by rfl⟩ : syracuseStep 1063511 = 1595267) B1595267
theorem B1063531 : Blo 1060614 1063531 := bstep (se 1 (by rfl) ⟨797648, by rfl⟩ : syracuseStep 1063531 = 1595297) B1595297
theorem B1063543 : Blo 1060614 1063543 := bstep (se 1 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 1063543 = 1595315) B1595315
theorem B1063563 : Blo 1060614 1063563 := bstep (se 1 (by rfl) ⟨797672, by rfl⟩ : syracuseStep 1063563 = 1595345) B1595345
theorem B1063575 : Blo 1060614 1063575 := bstep (se 1 (by rfl) ⟨797681, by rfl⟩ : syracuseStep 1063575 = 1595363) B1595363
theorem B1063595 : Blo 1060614 1063595 := bstep (se 1 (by rfl) ⟨797696, by rfl⟩ : syracuseStep 1063595 = 1595393) B1595393
theorem B1063607 : Blo 1060614 1063607 := bstep (se 1 (by rfl) ⟨797705, by rfl⟩ : syracuseStep 1063607 = 1595411) B1595411
theorem B1063627 : Blo 1060614 1063627 := bstep (se 1 (by rfl) ⟨797720, by rfl⟩ : syracuseStep 1063627 = 1595441) B1595441
theorem B1063639 : Blo 1060614 1063639 := bstep (se 1 (by rfl) ⟨797729, by rfl⟩ : syracuseStep 1063639 = 1595459) B1595459
theorem B1063659 : Blo 1060614 1063659 := bstep (se 1 (by rfl) ⟨797744, by rfl⟩ : syracuseStep 1063659 = 1595489) B1595489
theorem B1063671 : Blo 1060614 1063671 := bstep (se 1 (by rfl) ⟨797753, by rfl⟩ : syracuseStep 1063671 = 1595507) B1595507
theorem B1194763 : Blo 1060614 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B1063691 : Blo 1060614 1063691 := bstep (se 1 (by rfl) ⟨797768, by rfl⟩ : syracuseStep 1063691 = 1595537) B1595537
theorem B1063703 : Blo 1060614 1063703 := bstep (se 1 (by rfl) ⟨797777, by rfl⟩ : syracuseStep 1063703 = 1595555) B1595555
theorem B2013977 : Blo 1060614 2013977 := bstep (se 2 (by rfl) ⟨755241, by rfl⟩ : syracuseStep 2013977 = 1510483) B1510483
theorem B1063723 : Blo 1060614 1063723 := bstep (se 1 (by rfl) ⟨797792, by rfl⟩ : syracuseStep 1063723 = 1595585) B1595585
theorem B1063735 : Blo 1060614 1063735 := bstep (se 1 (by rfl) ⟨797801, by rfl⟩ : syracuseStep 1063735 = 1595603) B1595603
theorem B1063755 : Blo 1060614 1063755 := bstep (se 1 (by rfl) ⟨797816, by rfl⟩ : syracuseStep 1063755 = 1595633) B1595633
theorem B1063767 : Blo 1060614 1063767 := bstep (se 1 (by rfl) ⟨797825, by rfl⟩ : syracuseStep 1063767 = 1595651) B1595651
theorem B1063787 : Blo 1060614 1063787 := bstep (se 1 (by rfl) ⟨797840, by rfl⟩ : syracuseStep 1063787 = 1595681) B1595681
theorem B1194871 : Blo 1060614 1194871 := bstep (se 1 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 1194871 = 1792307) B1792307
theorem B1063799 : Blo 1060614 1063799 := bstep (se 1 (by rfl) ⟨797849, by rfl⟩ : syracuseStep 1063799 = 1595699) B1595699
theorem B1063819 : Blo 1060614 1063819 := bstep (se 1 (by rfl) ⟨797864, by rfl⟩ : syracuseStep 1063819 = 1595729) B1595729
theorem B1063831 : Blo 1060614 1063831 := bstep (se 1 (by rfl) ⟨797873, by rfl⟩ : syracuseStep 1063831 = 1595747) B1595747
theorem B1063851 : Blo 1060614 1063851 := bstep (se 1 (by rfl) ⟨797888, by rfl⟩ : syracuseStep 1063851 = 1595777) B1595777
theorem B1063863 : Blo 1060614 1063863 := bstep (se 1 (by rfl) ⟨797897, by rfl⟩ : syracuseStep 1063863 = 1595795) B1595795
theorem B1063883 : Blo 1060614 1063883 := bstep (se 1 (by rfl) ⟨797912, by rfl⟩ : syracuseStep 1063883 = 1595825) B1595825
theorem B1063895 : Blo 1060614 1063895 := bstep (se 1 (by rfl) ⟨797921, by rfl⟩ : syracuseStep 1063895 = 1595843) B1595843
theorem B1063915 : Blo 1060614 1063915 := bstep (se 1 (by rfl) ⟨797936, by rfl⟩ : syracuseStep 1063915 = 1595873) B1595873
theorem B1063927 : Blo 1060614 1063927 := bstep (se 1 (by rfl) ⟨797945, by rfl⟩ : syracuseStep 1063927 = 1595891) B1595891
theorem B1915915 : Blo 1060614 1915915 := bstep (se 1 (by rfl) ⟨1436936, by rfl⟩ : syracuseStep 1915915 = 2873873) B2873873
theorem B1063947 : Blo 1060614 1063947 := bstep (se 1 (by rfl) ⟨797960, by rfl⟩ : syracuseStep 1063947 = 1595921) B1595921
theorem B1063959 : Blo 1060614 1063959 := bstep (se 1 (by rfl) ⟨797969, by rfl⟩ : syracuseStep 1063959 = 1595939) B1595939
theorem B1195051 : Blo 1060614 1195051 := bstep (se 1 (by rfl) ⟨896288, by rfl⟩ : syracuseStep 1195051 = 1792577) B1792577
theorem B1063979 : Blo 1060614 1063979 := bstep (se 1 (by rfl) ⟨797984, by rfl⟩ : syracuseStep 1063979 = 1595969) B1595969
theorem B1063991 : Blo 1060614 1063991 := bstep (se 1 (by rfl) ⟨797993, by rfl⟩ : syracuseStep 1063991 = 1595987) B1595987
theorem B3882049 : Blo 1060614 3882049 := bstep (se 2 (by rfl) ⟨1455768, by rfl⟩ : syracuseStep 3882049 = 2911537) B2911537
theorem B1915979 : Blo 1060614 1915979 := bstep (se 1 (by rfl) ⟨1436984, by rfl⟩ : syracuseStep 1915979 = 2873969) B2873969
theorem B1064011 : Blo 1060614 1064011 := bstep (se 1 (by rfl) ⟨798008, by rfl⟩ : syracuseStep 1064011 = 1596017) B1596017
theorem B1064023 : Blo 1060614 1064023 := bstep (se 1 (by rfl) ⟨798017, by rfl⟩ : syracuseStep 1064023 = 1596035) B1596035
theorem B3587165 : Blo 1060614 3587165 := bstep (se 3 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 3587165 = 1345187) B1345187
theorem B1064043 : Blo 1060614 1064043 := bstep (se 1 (by rfl) ⟨798032, by rfl⟩ : syracuseStep 1064043 = 1596065) B1596065
theorem B1064055 : Blo 1060614 1064055 := bstep (se 1 (by rfl) ⟨798041, by rfl⟩ : syracuseStep 1064055 = 1596083) B1596083
theorem B1064075 : Blo 1060614 1064075 := bstep (se 1 (by rfl) ⟨798056, by rfl⟩ : syracuseStep 1064075 = 1596113) B1596113
theorem B1195159 : Blo 1060614 1195159 := bstep (se 1 (by rfl) ⟨896369, by rfl⟩ : syracuseStep 1195159 = 1792739) B1792739
theorem B1064087 : Blo 1060614 1064087 := bstep (se 1 (by rfl) ⟨798065, by rfl⟩ : syracuseStep 1064087 = 1596131) B1596131
theorem B1064107 : Blo 1060614 1064107 := bstep (se 1 (by rfl) ⟨798080, by rfl⟩ : syracuseStep 1064107 = 1596161) B1596161
theorem B1064119 : Blo 1060614 1064119 := bstep (se 1 (by rfl) ⟨798089, by rfl⟩ : syracuseStep 1064119 = 1596179) B1596179
theorem B1064139 : Blo 1060614 1064139 := bstep (se 1 (by rfl) ⟨798104, by rfl⟩ : syracuseStep 1064139 = 1596209) B1596209
theorem B1064151 : Blo 1060614 1064151 := bstep (se 1 (by rfl) ⟨798113, by rfl⟩ : syracuseStep 1064151 = 1596227) B1596227
theorem B1064171 : Blo 1060614 1064171 := bstep (se 1 (by rfl) ⟨798128, by rfl⟩ : syracuseStep 1064171 = 1596257) B1596257
theorem B1064183 : Blo 1060614 1064183 := bstep (se 1 (by rfl) ⟨798137, by rfl⟩ : syracuseStep 1064183 = 1596275) B1596275
theorem B1064203 : Blo 1060614 1064203 := bstep (se 1 (by rfl) ⟨798152, by rfl⟩ : syracuseStep 1064203 = 1596305) B1596305
theorem B1064215 : Blo 1060614 1064215 := bstep (se 1 (by rfl) ⟨798161, by rfl⟩ : syracuseStep 1064215 = 1596323) B1596323
theorem B1064235 : Blo 1060614 1064235 := bstep (se 1 (by rfl) ⟨798176, by rfl⟩ : syracuseStep 1064235 = 1596353) B1596353
theorem B1064247 : Blo 1060614 1064247 := bstep (se 1 (by rfl) ⟨798185, by rfl⟩ : syracuseStep 1064247 = 1596371) B1596371
theorem B10894657 : Blo 1060614 10894657 := bstep (se 2 (by rfl) ⟨4085496, by rfl⟩ : syracuseStep 10894657 = 8170993) B8170993
theorem B1195339 : Blo 1060614 1195339 := bstep (se 1 (by rfl) ⟨896504, by rfl⟩ : syracuseStep 1195339 = 1793009) B1793009
theorem B1064267 : Blo 1060614 1064267 := bstep (se 1 (by rfl) ⟨798200, by rfl⟩ : syracuseStep 1064267 = 1596401) B1596401
theorem B1064279 : Blo 1060614 1064279 := bstep (se 1 (by rfl) ⟨798209, by rfl⟩ : syracuseStep 1064279 = 1596419) B1596419
theorem B6045029 : Blo 1060614 6045029 := bstep (se 4 (by rfl) ⟨566721, by rfl⟩ : syracuseStep 6045029 = 1133443) B1133443
theorem B1064299 : Blo 1060614 1064299 := bstep (se 1 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 1064299 = 1596449) B1596449
theorem B1064311 : Blo 1060614 1064311 := bstep (se 1 (by rfl) ⟨798233, by rfl⟩ : syracuseStep 1064311 = 1596467) B1596467
theorem B1064331 : Blo 1060614 1064331 := bstep (se 1 (by rfl) ⟨798248, by rfl⟩ : syracuseStep 1064331 = 1596497) B1596497
theorem B1064343 : Blo 1060614 1064343 := bstep (se 1 (by rfl) ⟨798257, by rfl⟩ : syracuseStep 1064343 = 1596515) B1596515
theorem B1064363 : Blo 1060614 1064363 := bstep (se 1 (by rfl) ⟨798272, by rfl⟩ : syracuseStep 1064363 = 1596545) B1596545
theorem B1195447 : Blo 1060614 1195447 := bstep (se 1 (by rfl) ⟨896585, by rfl⟩ : syracuseStep 1195447 = 1793171) B1793171
theorem B1064375 : Blo 1060614 1064375 := bstep (se 1 (by rfl) ⟨798281, by rfl⟩ : syracuseStep 1064375 = 1596563) B1596563
theorem B1064395 : Blo 1060614 1064395 := bstep (se 1 (by rfl) ⟨798296, by rfl⟩ : syracuseStep 1064395 = 1596593) B1596593
theorem B1064407 : Blo 1060614 1064407 := bstep (se 1 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 1064407 = 1596611) B1596611
theorem B1064427 : Blo 1060614 1064427 := bstep (se 1 (by rfl) ⟨798320, by rfl⟩ : syracuseStep 1064427 = 1596641) B1596641
theorem B1064439 : Blo 1060614 1064439 := bstep (se 1 (by rfl) ⟨798329, by rfl⟩ : syracuseStep 1064439 = 1596659) B1596659
theorem B1064459 : Blo 1060614 1064459 := bstep (se 1 (by rfl) ⟨798344, by rfl⟩ : syracuseStep 1064459 = 1596689) B1596689
theorem B1064471 : Blo 1060614 1064471 := bstep (se 1 (by rfl) ⟨798353, by rfl⟩ : syracuseStep 1064471 = 1596707) B1596707
theorem B1064491 : Blo 1060614 1064491 := bstep (se 1 (by rfl) ⟨798368, by rfl⟩ : syracuseStep 1064491 = 1596737) B1596737
theorem B8306221 : Blo 1060614 8306221 := bstep (se 3 (by rfl) ⟨1557416, by rfl⟩ : syracuseStep 8306221 = 3114833) B3114833
theorem B1064503 : Blo 1060614 1064503 := bstep (se 1 (by rfl) ⟨798377, by rfl⟩ : syracuseStep 1064503 = 1596755) B1596755
theorem B1064523 : Blo 1060614 1064523 := bstep (se 1 (by rfl) ⟨798392, by rfl⟩ : syracuseStep 1064523 = 1596785) B1596785
theorem B1064535 : Blo 1060614 1064535 := bstep (se 1 (by rfl) ⟨798401, by rfl⟩ : syracuseStep 1064535 = 1596803) B1596803
theorem B1195627 : Blo 1060614 1195627 := bstep (se 1 (by rfl) ⟨896720, by rfl⟩ : syracuseStep 1195627 = 1793441) B1793441
theorem B1064555 : Blo 1060614 1064555 := bstep (se 1 (by rfl) ⟨798416, by rfl⟩ : syracuseStep 1064555 = 1596833) B1596833
theorem B1064567 : Blo 1060614 1064567 := bstep (se 1 (by rfl) ⟨798425, by rfl⟩ : syracuseStep 1064567 = 1596851) B1596851
theorem B1064587 : Blo 1060614 1064587 := bstep (se 1 (by rfl) ⟨798440, by rfl⟩ : syracuseStep 1064587 = 1596881) B1596881
theorem B1064599 : Blo 1060614 1064599 := bstep (se 1 (by rfl) ⟨798449, by rfl⟩ : syracuseStep 1064599 = 1596899) B1596899
theorem B1195735 : Blo 1060614 1195735 := bstep (se 1 (by rfl) ⟨896801, by rfl⟩ : syracuseStep 1195735 = 1793603) B1793603
theorem B1195915 : Blo 1060614 1195915 := bstep (se 1 (by rfl) ⟨896936, by rfl⟩ : syracuseStep 1195915 = 1793873) B1793873
theorem B1196023 : Blo 1060614 1196023 := bstep (se 1 (by rfl) ⟨897017, by rfl⟩ : syracuseStep 1196023 = 1794035) B1794035
theorem B3031091 : Blo 1060614 3031091 := bstep (se 1 (by rfl) ⟨2273318, by rfl⟩ : syracuseStep 3031091 = 4546637) B4546637
theorem B22986827 : Blo 1060614 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B4145245 : Blo 1060614 4145245 := bstep (se 3 (by rfl) ⟨777233, by rfl⟩ : syracuseStep 4145245 = 1554467) B1554467
theorem B7651459 : Blo 1060614 7651459 := bstep (se 1 (by rfl) ⟨5738594, by rfl⟩ : syracuseStep 7651459 = 11477189) B11477189
theorem B1196203 : Blo 1060614 1196203 := bstep (se 1 (by rfl) ⟨897152, by rfl⟩ : syracuseStep 1196203 = 1794305) B1794305
theorem B2015435 : Blo 1060614 2015435 := bstep (se 1 (by rfl) ⟨1511576, by rfl⟩ : syracuseStep 2015435 = 3023153) B3023153
theorem B3588299 : Blo 1060614 3588299 := bstep (se 1 (by rfl) ⟨2691224, by rfl⟩ : syracuseStep 3588299 = 5382449) B5382449
theorem B1196311 : Blo 1060614 1196311 := bstep (se 1 (by rfl) ⟨897233, by rfl⟩ : syracuseStep 1196311 = 1794467) B1794467
theorem B3031319 : Blo 1060614 3031319 := bstep (se 1 (by rfl) ⟨2273489, by rfl⟩ : syracuseStep 3031319 = 4546979) B4546979
theorem B1917299 : Blo 1060614 1917299 := bstep (se 1 (by rfl) ⟨1437974, by rfl⟩ : syracuseStep 1917299 = 2875949) B2875949
theorem B2015617 : Blo 1060614 2015617 := bstep (se 2 (by rfl) ⟨755856, by rfl⟩ : syracuseStep 2015617 = 1511713) B1511713
theorem B1196491 : Blo 1060614 1196491 := bstep (se 1 (by rfl) ⟨897368, by rfl⟩ : syracuseStep 1196491 = 1794737) B1794737
theorem B3588569 : Blo 1060614 3588569 := bstep (se 2 (by rfl) ⟨1345713, by rfl⟩ : syracuseStep 3588569 = 2691427) B2691427
theorem B4538845 : Blo 1060614 4538845 := bstep (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) B1702067
theorem B1196599 : Blo 1060614 1196599 := bstep (se 1 (by rfl) ⟨897449, by rfl⟩ : syracuseStep 1196599 = 1794899) B1794899
theorem B3031627 : Blo 1060614 3031627 := bstep (se 1 (by rfl) ⟨2273720, by rfl⟩ : syracuseStep 3031627 = 4547441) B4547441
theorem B1196779 : Blo 1060614 1196779 := bstep (se 1 (by rfl) ⟨897584, by rfl⟩ : syracuseStep 1196779 = 1795169) B1795169
theorem B2016065 : Blo 1060614 2016065 := bstep (se 2 (by rfl) ⟨756024, by rfl⟩ : syracuseStep 2016065 = 1512049) B1512049
theorem B1196887 : Blo 1060614 1196887 := bstep (se 1 (by rfl) ⟨897665, by rfl⟩ : syracuseStep 1196887 = 1795331) B1795331
theorem B1197067 : Blo 1060614 1197067 := bstep (se 1 (by rfl) ⟨897800, by rfl⟩ : syracuseStep 1197067 = 1795601) B1795601
theorem B1197175 : Blo 1060614 1197175 := bstep (se 1 (by rfl) ⟨897881, by rfl⟩ : syracuseStep 1197175 = 1795763) B1795763
theorem B2016407 : Blo 1060614 2016407 := bstep (se 1 (by rfl) ⟨1512305, by rfl⟩ : syracuseStep 2016407 = 3024611) B3024611
theorem B3589271 : Blo 1060614 3589271 := bstep (se 1 (by rfl) ⟨2691953, by rfl⟩ : syracuseStep 3589271 = 5383907) B5383907
theorem B9684173 : Blo 1060614 9684173 := bstep (se 3 (by rfl) ⟨1815782, by rfl⟩ : syracuseStep 9684173 = 3631565) B3631565
theorem B4539665 : Blo 1060614 4539665 := bstep (se 2 (by rfl) ⟨1702374, by rfl⟩ : syracuseStep 4539665 = 3404749) B3404749
theorem B1197355 : Blo 1060614 1197355 := bstep (se 1 (by rfl) ⟨898016, by rfl⟩ : syracuseStep 1197355 = 1796033) B1796033
theorem B1197463 : Blo 1060614 1197463 := bstep (se 1 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 1197463 = 1796195) B1796195
theorem B1197643 : Blo 1060614 1197643 := bstep (se 1 (by rfl) ⟨898232, by rfl⟩ : syracuseStep 1197643 = 1796465) B1796465
theorem B1590923 : Blo 1060614 1590923 := bstep (se 1 (by rfl) ⟨1193192, by rfl⟩ : syracuseStep 1590923 = 2386385) B2386385
theorem B1590935 : Blo 1060614 1590935 := bstep (se 1 (by rfl) ⟨1193201, by rfl⟩ : syracuseStep 1590935 = 2386403) B2386403
theorem B3589811 : Blo 1060614 3589811 := bstep (se 1 (by rfl) ⟨2692358, by rfl⟩ : syracuseStep 3589811 = 5384717) B5384717
theorem B1591001 : Blo 1060614 1591001 := bstep (se 2 (by rfl) ⟨596625, by rfl⟩ : syracuseStep 1591001 = 1193251) B1193251
theorem B19384109 : Blo 1060614 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B2017075 : Blo 1060614 2017075 := bstep (se 1 (by rfl) ⟨1512806, by rfl⟩ : syracuseStep 2017075 = 3025613) B3025613
theorem B1591115 : Blo 1060614 1591115 := bstep (se 1 (by rfl) ⟨1193336, by rfl⟩ : syracuseStep 1591115 = 2386673) B2386673
theorem B1591127 : Blo 1060614 1591127 := bstep (se 1 (by rfl) ⟨1193345, by rfl⟩ : syracuseStep 1591127 = 2386691) B2386691
theorem B1591193 : Blo 1060614 1591193 := bstep (se 2 (by rfl) ⟨596697, by rfl⟩ : syracuseStep 1591193 = 1193395) B1193395
theorem B4540333 : Blo 1060614 4540333 := bstep (se 3 (by rfl) ⟨851312, by rfl⟩ : syracuseStep 4540333 = 1702625) B1702625
theorem B3590081 : Blo 1060614 3590081 := bstep (se 2 (by rfl) ⟨1346280, by rfl⟩ : syracuseStep 3590081 = 2692561) B2692561
theorem B4310987 : Blo 1060614 4310987 := bstep (se 1 (by rfl) ⟨3233240, by rfl⟩ : syracuseStep 4310987 = 6466481) B6466481
theorem B1591307 : Blo 1060614 1591307 := bstep (se 1 (by rfl) ⟨1193480, by rfl⟩ : syracuseStep 1591307 = 2386961) B2386961
theorem B1591319 : Blo 1060614 1591319 := bstep (se 1 (by rfl) ⟨1193489, by rfl⟩ : syracuseStep 1591319 = 2386979) B2386979
theorem B1591385 : Blo 1060614 1591385 := bstep (se 2 (by rfl) ⟨596769, by rfl⟩ : syracuseStep 1591385 = 1193539) B1193539
theorem B1591499 : Blo 1060614 1591499 := bstep (se 1 (by rfl) ⟨1193624, by rfl⟩ : syracuseStep 1591499 = 2387249) B2387249
theorem B1591511 : Blo 1060614 1591511 := bstep (se 1 (by rfl) ⟨1193633, by rfl⟩ : syracuseStep 1591511 = 2387267) B2387267
theorem B2017523 : Blo 1060614 2017523 := bstep (se 1 (by rfl) ⟨1513142, by rfl⟩ : syracuseStep 2017523 = 3026285) B3026285
theorem B1591577 : Blo 1060614 1591577 := bstep (se 2 (by rfl) ⟨596841, by rfl⟩ : syracuseStep 1591577 = 1193683) B1193683
theorem B2017561 : Blo 1060614 2017561 := bstep (se 2 (by rfl) ⟨756585, by rfl⟩ : syracuseStep 2017561 = 1513171) B1513171
theorem B1591691 : Blo 1060614 1591691 := bstep (se 1 (by rfl) ⟨1193768, by rfl⟩ : syracuseStep 1591691 = 2387537) B2387537
theorem B1591703 : Blo 1060614 1591703 := bstep (se 1 (by rfl) ⟨1193777, by rfl⟩ : syracuseStep 1591703 = 2387555) B2387555
theorem B1591769 : Blo 1060614 1591769 := bstep (se 2 (by rfl) ⟨596913, by rfl⟩ : syracuseStep 1591769 = 1193827) B1193827
theorem B2869721 : Blo 1060614 2869721 := bstep (se 2 (by rfl) ⟨1076145, by rfl⟩ : syracuseStep 2869721 = 2152291) B2152291
theorem B3590621 : Blo 1060614 3590621 := bstep (se 3 (by rfl) ⟨673241, by rfl⟩ : syracuseStep 3590621 = 1346483) B1346483
theorem B4540931 : Blo 1060614 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B6801965 : Blo 1060614 6801965 := bstep (se 3 (by rfl) ⟨1275368, by rfl⟩ : syracuseStep 6801965 = 2550737) B2550737
theorem B5753389 : Blo 1060614 5753389 := bstep (se 3 (by rfl) ⟨1078760, by rfl⟩ : syracuseStep 5753389 = 2157521) B2157521
theorem B1591883 : Blo 1060614 1591883 := bstep (se 1 (by rfl) ⟨1193912, by rfl⟩ : syracuseStep 1591883 = 2387825) B2387825
theorem B3066443 : Blo 1060614 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B1591895 : Blo 1060614 1591895 := bstep (se 1 (by rfl) ⟨1193921, by rfl⟩ : syracuseStep 1591895 = 2387843) B2387843
theorem B1591961 : Blo 1060614 1591961 := bstep (se 2 (by rfl) ⟨596985, by rfl⟩ : syracuseStep 1591961 = 1193971) B1193971
theorem B2018009 : Blo 1060614 2018009 := bstep (se 2 (by rfl) ⟨756753, by rfl⟩ : syracuseStep 2018009 = 1513507) B1513507
theorem B1592075 : Blo 1060614 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B1592087 : Blo 1060614 1592087 := bstep (se 1 (by rfl) ⟨1194065, by rfl⟩ : syracuseStep 1592087 = 2388131) B2388131
theorem B1592153 : Blo 1060614 1592153 := bstep (se 2 (by rfl) ⟨597057, by rfl⟩ : syracuseStep 1592153 = 1194115) B1194115
theorem B1592267 : Blo 1060614 1592267 := bstep (se 1 (by rfl) ⟨1194200, by rfl⟩ : syracuseStep 1592267 = 2388401) B2388401
theorem B1592279 : Blo 1060614 1592279 := bstep (se 1 (by rfl) ⟨1194209, by rfl⟩ : syracuseStep 1592279 = 2388419) B2388419
theorem B1592345 : Blo 1060614 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B1592459 : Blo 1060614 1592459 := bstep (se 1 (by rfl) ⟨1194344, by rfl⟩ : syracuseStep 1592459 = 2388689) B2388689
theorem B1592471 : Blo 1060614 1592471 := bstep (se 1 (by rfl) ⟨1194353, by rfl⟩ : syracuseStep 1592471 = 2388707) B2388707
theorem B1592537 : Blo 1060614 1592537 := bstep (se 2 (by rfl) ⟨597201, by rfl⟩ : syracuseStep 1592537 = 1194403) B1194403
theorem B1592651 : Blo 1060614 1592651 := bstep (se 1 (by rfl) ⟨1194488, by rfl⟩ : syracuseStep 1592651 = 2388977) B2388977
theorem B1592663 : Blo 1060614 1592663 := bstep (se 1 (by rfl) ⟨1194497, by rfl⟩ : syracuseStep 1592663 = 2388995) B2388995
theorem B1592729 : Blo 1060614 1592729 := bstep (se 2 (by rfl) ⟨597273, by rfl⟩ : syracuseStep 1592729 = 1194547) B1194547
theorem B2018753 : Blo 1060614 2018753 := bstep (se 2 (by rfl) ⟨757032, by rfl⟩ : syracuseStep 2018753 = 1514065) B1514065
theorem B1592843 : Blo 1060614 1592843 := bstep (se 1 (by rfl) ⟨1194632, by rfl⟩ : syracuseStep 1592843 = 2389265) B2389265
theorem B1592855 : Blo 1060614 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B3591755 : Blo 1060614 3591755 := bstep (se 1 (by rfl) ⟨2693816, by rfl⟩ : syracuseStep 3591755 = 5387633) B5387633
theorem B1592921 : Blo 1060614 1592921 := bstep (se 2 (by rfl) ⟨597345, by rfl⟩ : syracuseStep 1592921 = 1194691) B1194691
theorem B1134199 : Blo 1060614 1134199 := bstep (se 1 (by rfl) ⟨850649, by rfl⟩ : syracuseStep 1134199 = 1701299) B1701299
theorem B1593035 : Blo 1060614 1593035 := bstep (se 1 (by rfl) ⟨1194776, by rfl⟩ : syracuseStep 1593035 = 2389553) B2389553
theorem B2019019 : Blo 1060614 2019019 := bstep (se 1 (by rfl) ⟨1514264, by rfl⟩ : syracuseStep 2019019 = 3028529) B3028529
theorem B10211021 : Blo 1060614 10211021 := bstep (se 3 (by rfl) ⟨1914566, by rfl⟩ : syracuseStep 10211021 = 3829133) B3829133
theorem B1593047 : Blo 1060614 1593047 := bstep (se 1 (by rfl) ⟨1194785, by rfl⟩ : syracuseStep 1593047 = 2389571) B2389571
theorem B1593113 : Blo 1060614 1593113 := bstep (se 2 (by rfl) ⟨597417, by rfl⟩ : syracuseStep 1593113 = 1194835) B1194835
theorem B3592025 : Blo 1060614 3592025 := bstep (se 2 (by rfl) ⟨1347009, by rfl⟩ : syracuseStep 3592025 = 2694019) B2694019
theorem B1593227 : Blo 1060614 1593227 := bstep (se 1 (by rfl) ⟨1194920, by rfl⟩ : syracuseStep 1593227 = 2389841) B2389841
theorem B1593239 : Blo 1060614 1593239 := bstep (se 1 (by rfl) ⟨1194929, by rfl⟩ : syracuseStep 1593239 = 2389859) B2389859
theorem B1593305 : Blo 1060614 1593305 := bstep (se 2 (by rfl) ⟨597489, by rfl⟩ : syracuseStep 1593305 = 1194979) B1194979
theorem B18173969 : Blo 1060614 18173969 := bstep (se 2 (by rfl) ⟨6815238, by rfl⟩ : syracuseStep 18173969 = 13630477) B13630477
theorem B1593419 : Blo 1060614 1593419 := bstep (se 1 (by rfl) ⟨1195064, by rfl⟩ : syracuseStep 1593419 = 2390129) B2390129
theorem B1790039 : Blo 1060614 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B1593431 : Blo 1060614 1593431 := bstep (se 1 (by rfl) ⟨1195073, by rfl⟩ : syracuseStep 1593431 = 2390147) B2390147
theorem B2019467 : Blo 1060614 2019467 := bstep (se 1 (by rfl) ⟨1514600, by rfl⟩ : syracuseStep 2019467 = 3029201) B3029201
theorem B1593497 : Blo 1060614 1593497 := bstep (se 2 (by rfl) ⟨597561, by rfl⟩ : syracuseStep 1593497 = 1195123) B1195123
theorem B1790167 : Blo 1060614 1790167 := bstep (se 1 (by rfl) ⟨1342625, by rfl⟩ : syracuseStep 1790167 = 2685251) B2685251
theorem B1593611 : Blo 1060614 1593611 := bstep (se 1 (by rfl) ⟨1195208, by rfl⟩ : syracuseStep 1593611 = 2390417) B2390417
theorem B1593623 : Blo 1060614 1593623 := bstep (se 1 (by rfl) ⟨1195217, by rfl⟩ : syracuseStep 1593623 = 2390435) B2390435
theorem B2019649 : Blo 1060614 2019649 := bstep (se 2 (by rfl) ⟨757368, by rfl⟩ : syracuseStep 2019649 = 1514737) B1514737
theorem B1593689 : Blo 1060614 1593689 := bstep (se 2 (by rfl) ⟨597633, by rfl⟩ : syracuseStep 1593689 = 1195267) B1195267
theorem B1135019 : Blo 1060614 1135019 := bstep (se 1 (by rfl) ⟨851264, by rfl⟩ : syracuseStep 1135019 = 1702529) B1702529
theorem B1593803 : Blo 1060614 1593803 := bstep (se 1 (by rfl) ⟨1195352, by rfl⟩ : syracuseStep 1593803 = 2390705) B2390705
theorem B1593815 : Blo 1060614 1593815 := bstep (se 1 (by rfl) ⟨1195361, by rfl⟩ : syracuseStep 1593815 = 2390723) B2390723
theorem B3592727 : Blo 1060614 3592727 := bstep (se 1 (by rfl) ⟨2694545, by rfl⟩ : syracuseStep 3592727 = 5389091) B5389091
theorem B1593881 : Blo 1060614 1593881 := bstep (se 2 (by rfl) ⟨597705, by rfl⟩ : syracuseStep 1593881 = 1195411) B1195411
theorem B1593995 : Blo 1060614 1593995 := bstep (se 1 (by rfl) ⟨1195496, by rfl⟩ : syracuseStep 1593995 = 2390993) B2390993
theorem B1594007 : Blo 1060614 1594007 := bstep (se 1 (by rfl) ⟨1195505, by rfl⟩ : syracuseStep 1594007 = 2391011) B2391011
theorem B2019991 : Blo 1060614 2019991 := bstep (se 1 (by rfl) ⟨1514993, by rfl⟩ : syracuseStep 2019991 = 3029987) B3029987
theorem B1594073 : Blo 1060614 1594073 := bstep (se 2 (by rfl) ⟨597777, by rfl⟩ : syracuseStep 1594073 = 1195555) B1195555
theorem B1790795 : Blo 1060614 1790795 := bstep (se 1 (by rfl) ⟨1343096, by rfl⟩ : syracuseStep 1790795 = 2686193) B2686193
theorem B1594187 : Blo 1060614 1594187 := bstep (se 1 (by rfl) ⟨1195640, by rfl⟩ : syracuseStep 1594187 = 2391281) B2391281
theorem B1594199 : Blo 1060614 1594199 := bstep (se 1 (by rfl) ⟨1195649, by rfl⟩ : syracuseStep 1594199 = 2391299) B2391299
theorem B2020211 : Blo 1060614 2020211 := bstep (se 1 (by rfl) ⟨1515158, by rfl⟩ : syracuseStep 2020211 = 3030317) B3030317
theorem B1594265 : Blo 1060614 1594265 := bstep (se 2 (by rfl) ⟨597849, by rfl⟩ : syracuseStep 1594265 = 1195699) B1195699
theorem B1790923 : Blo 1060614 1790923 := bstep (se 1 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 1790923 = 2686385) B2686385
theorem B1594379 : Blo 1060614 1594379 := bstep (se 1 (by rfl) ⟨1195784, by rfl⟩ : syracuseStep 1594379 = 2391569) B2391569
theorem B1594391 : Blo 1060614 1594391 := bstep (se 1 (by rfl) ⟨1195793, by rfl⟩ : syracuseStep 1594391 = 2391587) B2391587
theorem B6050861 : Blo 1060614 6050861 := bstep (se 3 (by rfl) ⟨1134536, by rfl⟩ : syracuseStep 6050861 = 2269073) B2269073
theorem B2020439 : Blo 1060614 2020439 := bstep (se 1 (by rfl) ⟨1515329, by rfl⟩ : syracuseStep 2020439 = 3030659) B3030659
theorem B1791065 : Blo 1060614 1791065 := bstep (se 2 (by rfl) ⟨671649, by rfl⟩ : syracuseStep 1791065 = 1343299) B1343299
theorem B1594457 : Blo 1060614 1594457 := bstep (se 2 (by rfl) ⟨597921, by rfl⟩ : syracuseStep 1594457 = 1195843) B1195843
theorem B1594571 : Blo 1060614 1594571 := bstep (se 1 (by rfl) ⟨1195928, by rfl⟩ : syracuseStep 1594571 = 2391857) B2391857
theorem B1594583 : Blo 1060614 1594583 := bstep (se 1 (by rfl) ⟨1195937, by rfl⟩ : syracuseStep 1594583 = 2391875) B2391875
theorem B1791193 : Blo 1060614 1791193 := bstep (se 2 (by rfl) ⟨671697, by rfl⟩ : syracuseStep 1791193 = 1343395) B1343395
theorem B1594649 : Blo 1060614 1594649 := bstep (se 2 (by rfl) ⟨597993, by rfl⟩ : syracuseStep 1594649 = 1195987) B1195987
theorem B2020697 : Blo 1060614 2020697 := bstep (se 2 (by rfl) ⟨757761, by rfl⟩ : syracuseStep 2020697 = 1515523) B1515523
theorem B1594763 : Blo 1060614 1594763 := bstep (se 1 (by rfl) ⟨1196072, by rfl⟩ : syracuseStep 1594763 = 2392145) B2392145
theorem B1594775 : Blo 1060614 1594775 := bstep (se 1 (by rfl) ⟨1196081, by rfl⟩ : syracuseStep 1594775 = 2392163) B2392163
theorem B1594841 : Blo 1060614 1594841 := bstep (se 2 (by rfl) ⟨598065, by rfl⟩ : syracuseStep 1594841 = 1196131) B1196131
theorem B1594955 : Blo 1060614 1594955 := bstep (se 1 (by rfl) ⟨1196216, by rfl⟩ : syracuseStep 1594955 = 2392433) B2392433
theorem B1594967 : Blo 1060614 1594967 := bstep (se 1 (by rfl) ⟨1196225, by rfl⟩ : syracuseStep 1594967 = 2392451) B2392451
theorem B1136215 : Blo 1060614 1136215 := bstep (se 1 (by rfl) ⟨852161, by rfl⟩ : syracuseStep 1136215 = 1704323) B1704323
theorem B3823193 : Blo 1060614 3823193 := bstep (se 2 (by rfl) ⟨1433697, by rfl⟩ : syracuseStep 3823193 = 2867395) B2867395
theorem B1595033 : Blo 1060614 1595033 := bstep (se 2 (by rfl) ⟨598137, by rfl⟩ : syracuseStep 1595033 = 1196275) B1196275
theorem B4314845 : Blo 1060614 4314845 := bstep (se 3 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 4314845 = 1618067) B1618067
theorem B1595147 : Blo 1060614 1595147 := bstep (se 1 (by rfl) ⟨1196360, by rfl⟩ : syracuseStep 1595147 = 2392721) B2392721
theorem B1791767 : Blo 1060614 1791767 := bstep (se 1 (by rfl) ⟨1343825, by rfl⟩ : syracuseStep 1791767 = 2687651) B2687651
theorem B1595159 : Blo 1060614 1595159 := bstep (se 1 (by rfl) ⟨1196369, by rfl⟩ : syracuseStep 1595159 = 2392739) B2392739
theorem B1595225 : Blo 1060614 1595225 := bstep (se 2 (by rfl) ⟨598209, by rfl⟩ : syracuseStep 1595225 = 1196419) B1196419
theorem B4085635 : Blo 1060614 4085635 := bstep (se 1 (by rfl) ⟨3064226, by rfl⟩ : syracuseStep 4085635 = 6128453) B6128453
theorem B1791895 : Blo 1060614 1791895 := bstep (se 1 (by rfl) ⟨1343921, by rfl⟩ : syracuseStep 1791895 = 2687843) B2687843
theorem B1595339 : Blo 1060614 1595339 := bstep (se 1 (by rfl) ⟨1196504, by rfl⟩ : syracuseStep 1595339 = 2393009) B2393009
theorem B1136587 : Blo 1060614 1136587 := bstep (se 1 (by rfl) ⟨852440, by rfl⟩ : syracuseStep 1136587 = 1704881) B1704881
theorem B1595351 : Blo 1060614 1595351 := bstep (se 1 (by rfl) ⟨1196513, by rfl⟩ : syracuseStep 1595351 = 2393027) B2393027
theorem B1595417 : Blo 1060614 1595417 := bstep (se 2 (by rfl) ⟨598281, by rfl⟩ : syracuseStep 1595417 = 1196563) B1196563
theorem B6805579 : Blo 1060614 6805579 := bstep (se 1 (by rfl) ⟨5104184, by rfl⟩ : syracuseStep 6805579 = 10208369) B10208369
theorem B1595531 : Blo 1060614 1595531 := bstep (se 1 (by rfl) ⟨1196648, by rfl⟩ : syracuseStep 1595531 = 2393297) B2393297
theorem B1595543 : Blo 1060614 1595543 := bstep (se 1 (by rfl) ⟨1196657, by rfl⟩ : syracuseStep 1595543 = 2393315) B2393315
theorem B1595609 : Blo 1060614 1595609 := bstep (se 2 (by rfl) ⟨598353, by rfl⟩ : syracuseStep 1595609 = 1196707) B1196707
theorem B1595723 : Blo 1060614 1595723 := bstep (se 1 (by rfl) ⟨1196792, by rfl⟩ : syracuseStep 1595723 = 2393585) B2393585
theorem B1595735 : Blo 1060614 1595735 := bstep (se 1 (by rfl) ⟨1196801, by rfl⟩ : syracuseStep 1595735 = 2393603) B2393603
theorem B2185601 : Blo 1060614 2185601 := bstep (se 2 (by rfl) ⟨819600, by rfl⟩ : syracuseStep 2185601 = 1639201) B1639201
theorem B1595801 : Blo 1060614 1595801 := bstep (se 2 (by rfl) ⟨598425, by rfl⟩ : syracuseStep 1595801 = 1196851) B1196851
theorem B1792523 : Blo 1060614 1792523 := bstep (se 1 (by rfl) ⟨1344392, by rfl⟩ : syracuseStep 1792523 = 2688785) B2688785
theorem B1595915 : Blo 1060614 1595915 := bstep (se 1 (by rfl) ⟨1196936, by rfl⟩ : syracuseStep 1595915 = 2393873) B2393873
theorem B1595927 : Blo 1060614 1595927 := bstep (se 1 (by rfl) ⟨1196945, by rfl⟩ : syracuseStep 1595927 = 2393891) B2393891
theorem B1595993 : Blo 1060614 1595993 := bstep (se 2 (by rfl) ⟨598497, by rfl⟩ : syracuseStep 1595993 = 1196995) B1196995
theorem B1792651 : Blo 1060614 1792651 := bstep (se 1 (by rfl) ⟨1344488, by rfl⟩ : syracuseStep 1792651 = 2688977) B2688977
theorem B1596107 : Blo 1060614 1596107 := bstep (se 1 (by rfl) ⟨1197080, by rfl⟩ : syracuseStep 1596107 = 2394161) B2394161
theorem B1596119 : Blo 1060614 1596119 := bstep (se 1 (by rfl) ⟨1197089, by rfl⟩ : syracuseStep 1596119 = 2394179) B2394179
theorem B1792793 : Blo 1060614 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B1596185 : Blo 1060614 1596185 := bstep (se 2 (by rfl) ⟨598569, by rfl⟩ : syracuseStep 1596185 = 1197139) B1197139
theorem B1596299 : Blo 1060614 1596299 := bstep (se 1 (by rfl) ⟨1197224, by rfl⟩ : syracuseStep 1596299 = 2394449) B2394449
theorem B6806423 : Blo 1060614 6806423 := bstep (se 1 (by rfl) ⟨5104817, by rfl⟩ : syracuseStep 6806423 = 10209635) B10209635
theorem B1596311 : Blo 1060614 1596311 := bstep (se 1 (by rfl) ⟨1197233, by rfl⟩ : syracuseStep 1596311 = 2394467) B2394467
theorem B1792921 : Blo 1060614 1792921 := bstep (se 2 (by rfl) ⟨672345, by rfl⟩ : syracuseStep 1792921 = 1344691) B1344691
theorem B1596377 : Blo 1060614 1596377 := bstep (se 2 (by rfl) ⟨598641, by rfl⟩ : syracuseStep 1596377 = 1197283) B1197283
theorem B1596491 : Blo 1060614 1596491 := bstep (se 1 (by rfl) ⟨1197368, by rfl⟩ : syracuseStep 1596491 = 2394737) B2394737
theorem B1596503 : Blo 1060614 1596503 := bstep (se 1 (by rfl) ⟨1197377, by rfl⟩ : syracuseStep 1596503 = 2394755) B2394755
theorem B1596569 : Blo 1060614 1596569 := bstep (se 2 (by rfl) ⟨598713, by rfl⟩ : syracuseStep 1596569 = 1197427) B1197427
theorem B1596683 : Blo 1060614 1596683 := bstep (se 1 (by rfl) ⟨1197512, by rfl⟩ : syracuseStep 1596683 = 2395025) B2395025
theorem B1596695 : Blo 1060614 1596695 := bstep (se 1 (by rfl) ⟨1197521, by rfl⟩ : syracuseStep 1596695 = 2395043) B2395043
theorem B1596761 : Blo 1060614 1596761 := bstep (se 2 (by rfl) ⟨598785, by rfl⟩ : syracuseStep 1596761 = 1197571) B1197571
theorem B6053251 : Blo 1060614 6053251 := bstep (se 1 (by rfl) ⟨4539938, by rfl⟩ : syracuseStep 6053251 = 9079877) B9079877
theorem B2907571 : Blo 1060614 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B1596875 : Blo 1060614 1596875 := bstep (se 1 (by rfl) ⟨1197656, by rfl⟩ : syracuseStep 1596875 = 2395313) B2395313
theorem B1793495 : Blo 1060614 1793495 := bstep (se 1 (by rfl) ⟨1345121, by rfl⟩ : syracuseStep 1793495 = 2690243) B2690243
theorem B1596887 : Blo 1060614 1596887 := bstep (se 1 (by rfl) ⟨1197665, by rfl⟩ : syracuseStep 1596887 = 2395331) B2395331
theorem B1793623 : Blo 1060614 1793623 := bstep (se 1 (by rfl) ⟨1345217, by rfl⟩ : syracuseStep 1793623 = 2690435) B2690435
theorem B3235673 : Blo 1060614 3235673 := bstep (se 2 (by rfl) ⟨1213377, by rfl⟩ : syracuseStep 3235673 = 2426755) B2426755
theorem B4546705 : Blo 1060614 4546705 := bstep (se 2 (by rfl) ⟨1705014, by rfl⟩ : syracuseStep 4546705 = 3410029) B3410029
theorem B8609969 : Blo 1060614 8609969 := bstep (se 2 (by rfl) ⟨3228738, by rfl⟩ : syracuseStep 8609969 = 6457477) B6457477
theorem B1794251 : Blo 1060614 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B6054209 : Blo 1060614 6054209 := bstep (se 2 (by rfl) ⟨2270328, by rfl⟩ : syracuseStep 6054209 = 4540657) B4540657
theorem B1794379 : Blo 1060614 1794379 := bstep (se 1 (by rfl) ⟨1345784, by rfl⟩ : syracuseStep 1794379 = 2691569) B2691569
theorem B19358129 : Blo 1060614 19358129 := bstep (se 2 (by rfl) ⟨7259298, by rfl⟩ : syracuseStep 19358129 = 14518597) B14518597
theorem B3629515 : Blo 1060614 3629515 := bstep (se 1 (by rfl) ⟨2722136, by rfl⟩ : syracuseStep 3629515 = 5444273) B5444273
theorem B1794521 : Blo 1060614 1794521 := bstep (se 2 (by rfl) ⟨672945, by rfl⟩ : syracuseStep 1794521 = 1345891) B1345891
theorem B1794649 : Blo 1060614 1794649 := bstep (se 2 (by rfl) ⟨672993, by rfl⟩ : syracuseStep 1794649 = 1345987) B1345987
theorem B11067997 : Blo 1060614 11067997 := bstep (se 3 (by rfl) ⟨2075249, by rfl⟩ : syracuseStep 11067997 = 4150499) B4150499
theorem B13591475 : Blo 1060614 13591475 := bstep (se 1 (by rfl) ⟨10193606, by rfl⟩ : syracuseStep 13591475 = 20387213) B20387213
theorem B1795223 : Blo 1060614 1795223 := bstep (se 1 (by rfl) ⟨1346417, by rfl⟩ : syracuseStep 1795223 = 2692835) B2692835
theorem B1795351 : Blo 1060614 1795351 := bstep (se 1 (by rfl) ⟨1346513, by rfl⟩ : syracuseStep 1795351 = 2693027) B2693027
theorem B2876737 : Blo 1060614 2876737 := bstep (se 2 (by rfl) ⟨1078776, by rfl⟩ : syracuseStep 2876737 = 2157553) B2157553
theorem B2549171 : Blo 1060614 2549171 := bstep (se 1 (by rfl) ⟨1911878, by rfl⟩ : syracuseStep 2549171 = 3823757) B3823757
theorem B7660979 : Blo 1060614 7660979 := bstep (se 1 (by rfl) ⟨5745734, by rfl⟩ : syracuseStep 7660979 = 11491469) B11491469
theorem B3401291 : Blo 1060614 3401291 := bstep (se 1 (by rfl) ⟨2550968, by rfl⟩ : syracuseStep 3401291 = 5101937) B5101937
theorem B8054477 : Blo 1060614 8054477 := bstep (se 3 (by rfl) ⟨1510214, by rfl⟩ : syracuseStep 8054477 = 3020429) B3020429
theorem B1107799 : Blo 1060614 1107799 := bstep (se 1 (by rfl) ⟨830849, by rfl⟩ : syracuseStep 1107799 = 1661699) B1661699
theorem B1795979 : Blo 1060614 1795979 := bstep (se 1 (by rfl) ⟨1346984, by rfl⟩ : syracuseStep 1795979 = 2693969) B2693969
theorem B1796107 : Blo 1060614 1796107 := bstep (se 1 (by rfl) ⟨1347080, by rfl⟩ : syracuseStep 1796107 = 2694161) B2694161
theorem B1796249 : Blo 1060614 1796249 := bstep (se 2 (by rfl) ⟨673593, by rfl⟩ : syracuseStep 1796249 = 1347187) B1347187
theorem B8054963 : Blo 1060614 8054963 := bstep (se 1 (by rfl) ⟨6041222, by rfl⟩ : syracuseStep 8054963 = 12082445) B12082445
theorem B8612045 : Blo 1060614 8612045 := bstep (se 3 (by rfl) ⟨1614758, by rfl⟩ : syracuseStep 8612045 = 3229517) B3229517
theorem B1796377 : Blo 1060614 1796377 := bstep (se 2 (by rfl) ⟨673641, by rfl⟩ : syracuseStep 1796377 = 1347283) B1347283
theorem B9202099 : Blo 1060614 9202099 := bstep (se 1 (by rfl) ⟨6901574, by rfl⟩ : syracuseStep 9202099 = 13803149) B13803149
theorem B2550295 : Blo 1060614 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B2386457 : Blo 1060614 2386457 := bstep (se 2 (by rfl) ⟨894921, by rfl⟩ : syracuseStep 2386457 = 1789843) B1789843
theorem B2386547 : Blo 1060614 2386547 := bstep (se 1 (by rfl) ⟨1789910, by rfl⟩ : syracuseStep 2386547 = 3579821) B3579821
theorem B2386583 : Blo 1060614 2386583 := bstep (se 1 (by rfl) ⟨1789937, by rfl⟩ : syracuseStep 2386583 = 3579875) B3579875
theorem B2386763 : Blo 1060614 2386763 := bstep (se 1 (by rfl) ⟨1790072, by rfl⟩ : syracuseStep 2386763 = 3580145) B3580145
theorem B2386817 : Blo 1060614 2386817 := bstep (se 2 (by rfl) ⟨895056, by rfl⟩ : syracuseStep 2386817 = 1790113) B1790113
theorem B19360691 : Blo 1060614 19360691 := bstep (se 1 (by rfl) ⟨14520518, by rfl⟩ : syracuseStep 19360691 = 29041037) B29041037
theorem B1076311 : Blo 1060614 1076311 := bstep (se 1 (by rfl) ⟨807233, by rfl⟩ : syracuseStep 1076311 = 1614467) B1614467
theorem B2387033 : Blo 1060614 2387033 := bstep (se 2 (by rfl) ⟨895137, by rfl⟩ : syracuseStep 2387033 = 1790275) B1790275
theorem B2387123 : Blo 1060614 2387123 := bstep (se 1 (by rfl) ⟨1790342, by rfl⟩ : syracuseStep 2387123 = 3580685) B3580685
theorem B3402931 : Blo 1060614 3402931 := bstep (se 1 (by rfl) ⟨2552198, by rfl⟩ : syracuseStep 3402931 = 5104397) B5104397
theorem B2387159 : Blo 1060614 2387159 := bstep (se 1 (by rfl) ⟨1790369, by rfl⟩ : syracuseStep 2387159 = 3580739) B3580739
theorem B3370205 : Blo 1060614 3370205 := bstep (se 3 (by rfl) ⟨631913, by rfl⟩ : syracuseStep 3370205 = 1263827) B1263827
theorem B1699159 : Blo 1060614 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B2387339 : Blo 1060614 2387339 := bstep (se 1 (by rfl) ⟨1790504, by rfl⟩ : syracuseStep 2387339 = 3581009) B3581009
theorem B2387393 : Blo 1060614 2387393 := bstep (se 2 (by rfl) ⟨895272, by rfl⟩ : syracuseStep 2387393 = 1790545) B1790545
theorem B13102553 : Blo 1060614 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B12086819 : Blo 1060614 12086819 := bstep (se 1 (by rfl) ⟨9065114, by rfl⟩ : syracuseStep 12086819 = 18130229) B18130229
theorem B8056421 : Blo 1060614 8056421 := bstep (se 4 (by rfl) ⟨755289, by rfl⟩ : syracuseStep 8056421 = 1510579) B1510579
theorem B2387609 : Blo 1060614 2387609 := bstep (se 2 (by rfl) ⟨895353, by rfl⟩ : syracuseStep 2387609 = 1790707) B1790707
theorem B2387699 : Blo 1060614 2387699 := bstep (se 1 (by rfl) ⟨1790774, by rfl⟩ : syracuseStep 2387699 = 3581549) B3581549
theorem B1699607 : Blo 1060614 1699607 := bstep (se 1 (by rfl) ⟨1274705, by rfl⟩ : syracuseStep 1699607 = 2549411) B2549411
theorem B2387735 : Blo 1060614 2387735 := bstep (se 1 (by rfl) ⟨1790801, by rfl⟩ : syracuseStep 2387735 = 3581603) B3581603
theorem B1699787 : Blo 1060614 1699787 := bstep (se 1 (by rfl) ⟨1274840, by rfl⟩ : syracuseStep 1699787 = 2549681) B2549681
theorem B2387915 : Blo 1060614 2387915 := bstep (se 1 (by rfl) ⟨1790936, by rfl⟩ : syracuseStep 2387915 = 3581873) B3581873
theorem B2387969 : Blo 1060614 2387969 := bstep (se 2 (by rfl) ⟨895488, by rfl⟩ : syracuseStep 2387969 = 1790977) B1790977
theorem B8056907 : Blo 1060614 8056907 := bstep (se 1 (by rfl) ⟨6042680, by rfl⟩ : syracuseStep 8056907 = 12085361) B12085361
theorem B5173379 : Blo 1060614 5173379 := bstep (se 1 (by rfl) ⟨3880034, by rfl⟩ : syracuseStep 5173379 = 7760069) B7760069
theorem B2388185 : Blo 1060614 2388185 := bstep (se 2 (by rfl) ⟨895569, by rfl⟩ : syracuseStep 2388185 = 1791139) B1791139
theorem B2388275 : Blo 1060614 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B1700171 : Blo 1060614 1700171 := bstep (se 1 (by rfl) ⟨1275128, by rfl⟩ : syracuseStep 1700171 = 2550257) B2550257
theorem B2388311 : Blo 1060614 2388311 := bstep (se 1 (by rfl) ⟨1791233, by rfl⟩ : syracuseStep 2388311 = 3582467) B3582467
theorem B1700299 : Blo 1060614 1700299 := bstep (se 1 (by rfl) ⟨1275224, by rfl⟩ : syracuseStep 1700299 = 2550449) B2550449
theorem B2388491 : Blo 1060614 2388491 := bstep (se 1 (by rfl) ⟨1791368, by rfl⟩ : syracuseStep 2388491 = 3582737) B3582737
theorem B2388545 : Blo 1060614 2388545 := bstep (se 2 (by rfl) ⟨895704, by rfl⟩ : syracuseStep 2388545 = 1791409) B1791409
theorem B5370461 : Blo 1060614 5370461 := bstep (se 3 (by rfl) ⟨1006961, by rfl⟩ : syracuseStep 5370461 = 2013923) B2013923
theorem B12284621 : Blo 1060614 12284621 := bstep (se 3 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 12284621 = 4606733) B4606733
theorem B1078039 : Blo 1060614 1078039 := bstep (se 1 (by rfl) ⟨808529, by rfl⟩ : syracuseStep 1078039 = 1617059) B1617059
theorem B2388761 : Blo 1060614 2388761 := bstep (se 2 (by rfl) ⟨895785, by rfl⟩ : syracuseStep 2388761 = 1791571) B1791571
theorem B29487971 : Blo 1060614 29487971 := bstep (se 1 (by rfl) ⟨22115978, by rfl⟩ : syracuseStep 29487971 = 44231957) B44231957
theorem B2388851 : Blo 1060614 2388851 := bstep (se 1 (by rfl) ⟨1791638, by rfl⟩ : syracuseStep 2388851 = 3583277) B3583277
theorem B2388887 : Blo 1060614 2388887 := bstep (se 1 (by rfl) ⟨1791665, by rfl⟩ : syracuseStep 2388887 = 3583331) B3583331
theorem B2389067 : Blo 1060614 2389067 := bstep (se 1 (by rfl) ⟨1791800, by rfl⟩ : syracuseStep 2389067 = 3583601) B3583601
theorem B6059083 : Blo 1060614 6059083 := bstep (se 1 (by rfl) ⟨4544312, by rfl⟩ : syracuseStep 6059083 = 9088625) B9088625
theorem B2389121 : Blo 1060614 2389121 := bstep (se 2 (by rfl) ⟨895920, by rfl⟩ : syracuseStep 2389121 = 1791841) B1791841
theorem B1701017 : Blo 1060614 1701017 := bstep (se 2 (by rfl) ⟨637881, by rfl⟩ : syracuseStep 1701017 = 1275763) B1275763
theorem B5108953 : Blo 1060614 5108953 := bstep (se 2 (by rfl) ⟨1915857, by rfl⟩ : syracuseStep 5108953 = 3831715) B3831715
theorem B2389337 : Blo 1060614 2389337 := bstep (se 2 (by rfl) ⟨896001, by rfl⟩ : syracuseStep 2389337 = 1792003) B1792003
theorem B1701209 : Blo 1060614 1701209 := bstep (se 2 (by rfl) ⟨637953, by rfl⟩ : syracuseStep 1701209 = 1275907) B1275907
theorem B3405149 : Blo 1060614 3405149 := bstep (se 3 (by rfl) ⟨638465, by rfl⟩ : syracuseStep 3405149 = 1276931) B1276931
theorem B6059357 : Blo 1060614 6059357 := bstep (se 3 (by rfl) ⟨1136129, by rfl⟩ : syracuseStep 6059357 = 2272259) B2272259
theorem B2389427 : Blo 1060614 2389427 := bstep (se 1 (by rfl) ⟨1792070, by rfl⟩ : syracuseStep 2389427 = 3584141) B3584141
theorem B2389463 : Blo 1060614 2389463 := bstep (se 1 (by rfl) ⟨1792097, by rfl⟩ : syracuseStep 2389463 = 3584195) B3584195
theorem B4027907 : Blo 1060614 4027907 := bstep (se 1 (by rfl) ⟨3020930, by rfl⟩ : syracuseStep 4027907 = 6041861) B6041861
theorem B2389643 : Blo 1060614 2389643 := bstep (se 1 (by rfl) ⟨1792232, by rfl⟩ : syracuseStep 2389643 = 3584465) B3584465
theorem B2389697 : Blo 1060614 2389697 := bstep (se 2 (by rfl) ⟨896136, by rfl⟩ : syracuseStep 2389697 = 1792273) B1792273
theorem B2455447 : Blo 1060614 2455447 := bstep (se 1 (by rfl) ⟨1841585, by rfl⟩ : syracuseStep 2455447 = 3683171) B3683171
theorem B2389913 : Blo 1060614 2389913 := bstep (se 2 (by rfl) ⟨896217, by rfl⟩ : syracuseStep 2389913 = 1792435) B1792435
theorem B4028363 : Blo 1060614 4028363 := bstep (se 1 (by rfl) ⟨3021272, by rfl⟩ : syracuseStep 4028363 = 6042545) B6042545
theorem B2390003 : Blo 1060614 2390003 := bstep (se 1 (by rfl) ⟨1792502, by rfl⟩ : syracuseStep 2390003 = 3585005) B3585005
theorem B2390039 : Blo 1060614 2390039 := bstep (se 1 (by rfl) ⟨1792529, by rfl⟩ : syracuseStep 2390039 = 3585059) B3585059
theorem B9074753 : Blo 1060614 9074753 := bstep (se 2 (by rfl) ⟨3403032, by rfl⟩ : syracuseStep 9074753 = 6806065) B6806065
theorem B4028561 : Blo 1060614 4028561 := bstep (se 2 (by rfl) ⟨1510710, by rfl⟩ : syracuseStep 4028561 = 3021421) B3021421
theorem B2390219 : Blo 1060614 2390219 := bstep (se 1 (by rfl) ⟨1792664, by rfl⟩ : syracuseStep 2390219 = 3585329) B3585329
theorem B2390273 : Blo 1060614 2390273 := bstep (se 2 (by rfl) ⟨896352, by rfl⟩ : syracuseStep 2390273 = 1792705) B1792705
theorem B2488601 : Blo 1060614 2488601 := bstep (se 2 (by rfl) ⟨933225, by rfl⟩ : syracuseStep 2488601 = 1866451) B1866451
theorem B2554177 : Blo 1060614 2554177 := bstep (se 2 (by rfl) ⟨957816, by rfl⟩ : syracuseStep 2554177 = 1915633) B1915633
theorem B8190359 : Blo 1060614 8190359 := bstep (se 1 (by rfl) ⟨6142769, by rfl⟩ : syracuseStep 8190359 = 12285539) B12285539
theorem B2390489 : Blo 1060614 2390489 := bstep (se 2 (by rfl) ⟨896433, by rfl⟩ : syracuseStep 2390489 = 1792867) B1792867
theorem B2390579 : Blo 1060614 2390579 := bstep (se 1 (by rfl) ⟨1792934, by rfl⟩ : syracuseStep 2390579 = 3585869) B3585869
theorem B1636951 : Blo 1060614 1636951 := bstep (se 1 (by rfl) ⟨1227713, by rfl⟩ : syracuseStep 1636951 = 2455427) B2455427
theorem B2390615 : Blo 1060614 2390615 := bstep (se 1 (by rfl) ⟨1792961, by rfl⟩ : syracuseStep 2390615 = 3585923) B3585923
theorem B5372567 : Blo 1060614 5372567 := bstep (se 1 (by rfl) ⟨4029425, by rfl⟩ : syracuseStep 5372567 = 8058851) B8058851
theorem B8190725 : Blo 1060614 8190725 := bstep (se 4 (by rfl) ⟨767880, by rfl⟩ : syracuseStep 8190725 = 1535761) B1535761
theorem B2390795 : Blo 1060614 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B2390849 : Blo 1060614 2390849 := bstep (se 2 (by rfl) ⟨896568, by rfl⟩ : syracuseStep 2390849 = 1793137) B1793137
theorem B4029335 : Blo 1060614 4029335 := bstep (se 1 (by rfl) ⟨3022001, by rfl⟩ : syracuseStep 4029335 = 6044003) B6044003
theorem B2685899 : Blo 1060614 2685899 := bstep (se 1 (by rfl) ⟨2014424, by rfl⟩ : syracuseStep 2685899 = 4028849) B4028849
theorem B1342423 : Blo 1060614 1342423 := bstep (se 1 (by rfl) ⟨1006817, by rfl⟩ : syracuseStep 1342423 = 2013635) B2013635
theorem B2391065 : Blo 1060614 2391065 := bstep (se 2 (by rfl) ⟨896649, by rfl⟩ : syracuseStep 2391065 = 1793299) B1793299
theorem B4029533 : Blo 1060614 4029533 := bstep (se 3 (by rfl) ⟨755537, by rfl⟩ : syracuseStep 4029533 = 1511075) B1511075
theorem B2391155 : Blo 1060614 2391155 := bstep (se 1 (by rfl) ⟨1793366, by rfl⟩ : syracuseStep 2391155 = 3586733) B3586733
theorem B2391191 : Blo 1060614 2391191 := bstep (se 1 (by rfl) ⟨1793393, by rfl⟩ : syracuseStep 2391191 = 3586787) B3586787
theorem B3833111 : Blo 1060614 3833111 := bstep (se 1 (by rfl) ⟨2874833, by rfl⟩ : syracuseStep 3833111 = 5749667) B5749667
theorem B2391371 : Blo 1060614 2391371 := bstep (se 1 (by rfl) ⟨1793528, by rfl⟩ : syracuseStep 2391371 = 3587057) B3587057
theorem B2391425 : Blo 1060614 2391425 := bstep (se 2 (by rfl) ⟨896784, by rfl⟩ : syracuseStep 2391425 = 1793569) B1793569
theorem B9698777 : Blo 1060614 9698777 := bstep (se 2 (by rfl) ⟨3637041, by rfl⟩ : syracuseStep 9698777 = 7274083) B7274083
theorem B1211927 : Blo 1060614 1211927 := bstep (se 1 (by rfl) ⟨908945, by rfl⟩ : syracuseStep 1211927 = 1817891) B1817891
theorem B1965655 : Blo 1060614 1965655 := bstep (se 1 (by rfl) ⟨1474241, by rfl⟩ : syracuseStep 1965655 = 2948483) B2948483
theorem B2391641 : Blo 1060614 2391641 := bstep (se 2 (by rfl) ⟨896865, by rfl⟩ : syracuseStep 2391641 = 1793731) B1793731
theorem B2391731 : Blo 1060614 2391731 := bstep (se 1 (by rfl) ⟨1793798, by rfl⟩ : syracuseStep 2391731 = 3587597) B3587597
theorem B2391767 : Blo 1060614 2391767 := bstep (se 1 (by rfl) ⟨1793825, by rfl⟩ : syracuseStep 2391767 = 3587651) B3587651
theorem B3833561 : Blo 1060614 3833561 := bstep (se 2 (by rfl) ⟨1437585, by rfl⟩ : syracuseStep 3833561 = 2875171) B2875171
theorem B1343243 : Blo 1060614 1343243 := bstep (se 1 (by rfl) ⟨1007432, by rfl⟩ : syracuseStep 1343243 = 2014865) B2014865
theorem B3833689 : Blo 1060614 3833689 := bstep (se 2 (by rfl) ⟨1437633, by rfl⟩ : syracuseStep 3833689 = 2875267) B2875267
theorem B2391947 : Blo 1060614 2391947 := bstep (se 1 (by rfl) ⟨1793960, by rfl⟩ : syracuseStep 2391947 = 3587921) B3587921
theorem B2686871 : Blo 1060614 2686871 := bstep (se 1 (by rfl) ⟨2015153, by rfl⟩ : syracuseStep 2686871 = 4030307) B4030307
theorem B2392001 : Blo 1060614 2392001 := bstep (se 2 (by rfl) ⟨897000, by rfl⟩ : syracuseStep 2392001 = 1794001) B1794001
theorem B51740765 : Blo 1060614 51740765 := bstep (se 3 (by rfl) ⟨9701393, by rfl⟩ : syracuseStep 51740765 = 19402787) B19402787
theorem B1343623 : Blo 1060614 1343623 := bstep (se 1 (by rfl) ⟨1007717, by rfl⟩ : syracuseStep 1343623 = 2015435) B2015435
theorem B2392199 : Blo 1060614 2392199 := bstep (se 1 (by rfl) ⟨1794149, by rfl⟩ : syracuseStep 2392199 = 3588299) B3588299
theorem B6062273 : Blo 1060614 6062273 := bstep (se 2 (by rfl) ⟨2273352, by rfl⟩ : syracuseStep 6062273 = 4546705) B4546705
theorem B1278199 : Blo 1060614 1278199 := bstep (se 1 (by rfl) ⟨958649, by rfl⟩ : syracuseStep 1278199 = 1917299) B1917299
theorem B3637505 : Blo 1060614 3637505 := bstep (se 2 (by rfl) ⟨1364064, by rfl⟩ : syracuseStep 3637505 = 2728129) B2728129
theorem B2392379 : Blo 1060614 2392379 := bstep (se 1 (by rfl) ⟨1794284, by rfl⟩ : syracuseStep 2392379 = 3588569) B3588569
theorem B6816059 : Blo 1060614 6816059 := bstep (se 1 (by rfl) ⟨5112044, by rfl⟩ : syracuseStep 6816059 = 10224089) B10224089
theorem B2392505 : Blo 1060614 2392505 := bstep (se 2 (by rfl) ⟨897189, by rfl⟩ : syracuseStep 2392505 = 1794379) B1794379
theorem B2687489 : Blo 1060614 2687489 := bstep (se 2 (by rfl) ⟨1007808, by rfl⟩ : syracuseStep 2687489 = 2015617) B2015617
theorem B4031005 : Blo 1060614 4031005 := bstep (se 3 (by rfl) ⟨755813, by rfl⟩ : syracuseStep 4031005 = 1511627) B1511627
theorem B1344043 : Blo 1060614 1344043 := bstep (se 1 (by rfl) ⟨1008032, by rfl⟩ : syracuseStep 1344043 = 2016065) B2016065
theorem B1344271 : Blo 1060614 1344271 := bstep (se 1 (by rfl) ⟨1008203, by rfl⟩ : syracuseStep 1344271 = 2016407) B2016407
theorem B2392847 : Blo 1060614 2392847 := bstep (se 1 (by rfl) ⟨1794635, by rfl⟩ : syracuseStep 2392847 = 3589271) B3589271
theorem B2392865 : Blo 1060614 2392865 := bstep (se 2 (by rfl) ⟨897324, by rfl⟩ : syracuseStep 2392865 = 1794649) B1794649
theorem B6456115 : Blo 1060614 6456115 := bstep (se 1 (by rfl) ⟨4842086, by rfl⟩ : syracuseStep 6456115 = 9684173) B9684173
theorem B5374835 : Blo 1060614 5374835 := bstep (se 1 (by rfl) ⟨4031126, by rfl⟩ : syracuseStep 5374835 = 8062253) B8062253
theorem B2687863 : Blo 1060614 2687863 := bstep (se 1 (by rfl) ⟨2015897, by rfl⟩ : syracuseStep 2687863 = 4031795) B4031795
theorem B2393207 : Blo 1060614 2393207 := bstep (se 1 (by rfl) ⟨1794905, by rfl⟩ : syracuseStep 2393207 = 3589811) B3589811
theorem B2688299 : Blo 1060614 2688299 := bstep (se 1 (by rfl) ⟨2016224, by rfl⟩ : syracuseStep 2688299 = 4032449) B4032449
theorem B2393387 : Blo 1060614 2393387 := bstep (se 1 (by rfl) ⟨1795040, by rfl⟩ : syracuseStep 2393387 = 3590081) B3590081
theorem B5375321 : Blo 1060614 5375321 := bstep (se 2 (by rfl) ⟨2015745, by rfl⟩ : syracuseStep 5375321 = 4031491) B4031491
theorem B437061091 : Blo 1060614 437061091 := bstep (se 1 (by rfl) ⟨327795818, by rfl⟩ : syracuseStep 437061091 = 655591637) B655591637
theorem B1345015 : Blo 1060614 1345015 := bstep (se 1 (by rfl) ⟨1008761, by rfl⟩ : syracuseStep 1345015 = 2017523) B2017523
theorem B4851211 : Blo 1060614 4851211 := bstep (se 1 (by rfl) ⟨3638408, by rfl⟩ : syracuseStep 4851211 = 7276817) B7276817
theorem B2393747 : Blo 1060614 2393747 := bstep (se 1 (by rfl) ⟨1795310, by rfl⟩ : syracuseStep 2393747 = 3590621) B3590621
theorem B2393801 : Blo 1060614 2393801 := bstep (se 2 (by rfl) ⟨897675, by rfl⟩ : syracuseStep 2393801 = 1795351) B1795351
theorem B3835649 : Blo 1060614 3835649 := bstep (se 2 (by rfl) ⟨1438368, by rfl⟩ : syracuseStep 3835649 = 2876737) B2876737
theorem B1345339 : Blo 1060614 1345339 := bstep (se 1 (by rfl) ⟨1009004, by rfl⟩ : syracuseStep 1345339 = 2018009) B2018009
theorem B2557811 : Blo 1060614 2557811 := bstep (se 1 (by rfl) ⟨1918358, by rfl⟩ : syracuseStep 2557811 = 3836717) B3836717
theorem B2689139 : Blo 1060614 2689139 := bstep (se 1 (by rfl) ⟨2016854, by rfl⟩ : syracuseStep 2689139 = 4033709) B4033709
theorem B2689159 : Blo 1060614 2689159 := bstep (se 1 (by rfl) ⟨2016869, by rfl⟩ : syracuseStep 2689159 = 4033739) B4033739
theorem B1345835 : Blo 1060614 1345835 := bstep (se 1 (by rfl) ⟨1009376, by rfl⟩ : syracuseStep 1345835 = 2018753) B2018753
theorem B2394503 : Blo 1060614 2394503 := bstep (se 1 (by rfl) ⟨1795877, by rfl⟩ : syracuseStep 2394503 = 3591755) B3591755
theorem B2689433 : Blo 1060614 2689433 := bstep (se 2 (by rfl) ⟨1008537, by rfl⟩ : syracuseStep 2689433 = 2017075) B2017075
theorem B2689595 : Blo 1060614 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B2394683 : Blo 1060614 2394683 := bstep (se 1 (by rfl) ⟨1796012, by rfl⟩ : syracuseStep 2394683 = 3592025) B3592025
theorem B2394809 : Blo 1060614 2394809 := bstep (se 2 (by rfl) ⟨898053, by rfl⟩ : syracuseStep 2394809 = 1796107) B1796107
theorem B1346311 : Blo 1060614 1346311 := bstep (se 1 (by rfl) ⟨1009733, by rfl⟩ : syracuseStep 1346311 = 2019467) B2019467
theorem B2689807 : Blo 1060614 2689807 := bstep (se 1 (by rfl) ⟨2017355, by rfl⟩ : syracuseStep 2689807 = 4034711) B4034711
theorem B2395151 : Blo 1060614 2395151 := bstep (se 1 (by rfl) ⟨1796363, by rfl⟩ : syracuseStep 2395151 = 3592727) B3592727
theorem B2690081 : Blo 1060614 2690081 := bstep (se 2 (by rfl) ⟨1008780, by rfl⟩ : syracuseStep 2690081 = 2017561) B2017561
theorem B2395169 : Blo 1060614 2395169 := bstep (se 2 (by rfl) ⟨898188, by rfl⟩ : syracuseStep 2395169 = 1796377) B1796377
theorem B8621257 : Blo 1060614 8621257 := bstep (se 2 (by rfl) ⟨3232971, by rfl⟩ : syracuseStep 8621257 = 6465943) B6465943
theorem B1346807 : Blo 1060614 1346807 := bstep (se 1 (by rfl) ⟨1010105, by rfl⟩ : syracuseStep 1346807 = 2020211) B2020211
theorem B1576199 : Blo 1060614 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B5737817 : Blo 1060614 5737817 := bstep (se 2 (by rfl) ⟨2151681, by rfl⟩ : syracuseStep 5737817 = 4303363) B4303363
theorem B4033907 : Blo 1060614 4033907 := bstep (se 1 (by rfl) ⟨3025430, by rfl⟩ : syracuseStep 4033907 = 6050861) B6050861
theorem B1346959 : Blo 1060614 1346959 := bstep (se 1 (by rfl) ⟨1010219, by rfl⟩ : syracuseStep 1346959 = 2020439) B2020439
theorem B7671185 : Blo 1060614 7671185 := bstep (se 2 (by rfl) ⟨2876694, by rfl⟩ : syracuseStep 7671185 = 5753389) B5753389
theorem B5377427 : Blo 1060614 5377427 := bstep (se 1 (by rfl) ⟨4033070, by rfl⟩ : syracuseStep 5377427 = 8066141) B8066141
theorem B1347131 : Blo 1060614 1347131 := bstep (se 1 (by rfl) ⟨1010348, by rfl⟩ : syracuseStep 1347131 = 2020697) B2020697
theorem B1511183 : Blo 1060614 1511183 := bstep (se 1 (by rfl) ⟨1133387, by rfl⟩ : syracuseStep 1511183 = 2266775) B2266775
theorem B2691083 : Blo 1060614 2691083 := bstep (se 1 (by rfl) ⟨2018312, by rfl⟩ : syracuseStep 2691083 = 4036625) B4036625
theorem B4853803 : Blo 1060614 4853803 := bstep (se 1 (by rfl) ⟨3640352, by rfl⟩ : syracuseStep 4853803 = 7280705) B7280705
theorem B1937849 : Blo 1060614 1937849 := bstep (se 2 (by rfl) ⟨726693, by rfl⟩ : syracuseStep 1937849 = 1453387) B1453387
theorem B2265545 : Blo 1060614 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B8065655 : Blo 1060614 8065655 := bstep (se 1 (by rfl) ⟨6049241, by rfl⟩ : syracuseStep 8065655 = 12098483) B12098483
theorem B2691731 : Blo 1060614 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B1512265 : Blo 1060614 1512265 := bstep (se 2 (by rfl) ⟨567099, by rfl⟩ : syracuseStep 1512265 = 1134199) B1134199
theorem B2692025 : Blo 1060614 2692025 := bstep (se 2 (by rfl) ⟨1009509, by rfl⟩ : syracuseStep 2692025 = 2019019) B2019019
theorem B1512379 : Blo 1060614 1512379 := bstep (se 1 (by rfl) ⟨1134284, by rfl⟩ : syracuseStep 1512379 = 2268569) B2268569
theorem B10228781 : Blo 1060614 10228781 := bstep (se 3 (by rfl) ⟨1917896, by rfl⟩ : syracuseStep 10228781 = 3835793) B3835793
theorem B5739979 : Blo 1060614 5739979 := bstep (se 1 (by rfl) ⟨4304984, by rfl⟩ : syracuseStep 5739979 = 8609969) B8609969
theorem B4036139 : Blo 1060614 4036139 := bstep (se 1 (by rfl) ⟨3027104, by rfl⟩ : syracuseStep 4036139 = 6054209) B6054209
theorem B8066627 : Blo 1060614 8066627 := bstep (se 1 (by rfl) ⟨6049970, by rfl⟩ : syracuseStep 8066627 = 12099941) B12099941
theorem B2692723 : Blo 1060614 2692723 := bstep (se 1 (by rfl) ⟨2019542, by rfl⟩ : syracuseStep 2692723 = 4039085) B4039085
theorem B2692865 : Blo 1060614 2692865 := bstep (se 2 (by rfl) ⟨1009824, by rfl⟩ : syracuseStep 2692865 = 2019649) B2019649
theorem B5740325 : Blo 1060614 5740325 := bstep (se 4 (by rfl) ⟨538155, by rfl⟩ : syracuseStep 5740325 = 1076311) B1076311
theorem B2267065 : Blo 1060614 2267065 := bstep (se 2 (by rfl) ⟨850149, by rfl⟩ : syracuseStep 2267065 = 1700299) B1700299
theorem B31004695 : Blo 1060614 31004695 := bstep (se 1 (by rfl) ⟨23253521, by rfl⟩ : syracuseStep 31004695 = 46507043) B46507043
theorem B2693321 : Blo 1060614 2693321 := bstep (se 2 (by rfl) ⟨1009995, by rfl⟩ : syracuseStep 2693321 = 2019991) B2019991
theorem B3021067 : Blo 1060614 3021067 := bstep (se 1 (by rfl) ⟨2265800, by rfl⟩ : syracuseStep 3021067 = 4531601) B4531601
theorem B2267527 : Blo 1060614 2267527 := bstep (se 1 (by rfl) ⟨1700645, by rfl⟩ : syracuseStep 2267527 = 3401291) B3401291
theorem B5380505 : Blo 1060614 5380505 := bstep (se 2 (by rfl) ⟨2017689, by rfl⟩ : syracuseStep 5380505 = 4035379) B4035379
theorem B1513991 : Blo 1060614 1513991 := bstep (se 1 (by rfl) ⟨1135493, by rfl⟩ : syracuseStep 1513991 = 2270987) B2270987
theorem B2693675 : Blo 1060614 2693675 := bstep (se 1 (by rfl) ⟨2020256, by rfl⟩ : syracuseStep 2693675 = 4040513) B4040513
theorem B13605569 : Blo 1060614 13605569 := bstep (se 2 (by rfl) ⟨5102088, by rfl⟩ : syracuseStep 13605569 = 10204177) B10204177
theorem B3021569 : Blo 1060614 3021569 := bstep (se 2 (by rfl) ⟨1133088, by rfl⟩ : syracuseStep 3021569 = 2266177) B2266177
theorem B5741363 : Blo 1060614 5741363 := bstep (se 1 (by rfl) ⟨4306022, by rfl⟩ : syracuseStep 5741363 = 8612045) B8612045
theorem B3021911 : Blo 1060614 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B4660595 : Blo 1060614 4660595 := bstep (se 1 (by rfl) ⟨3495446, by rfl⟩ : syracuseStep 4660595 = 6990893) B6990893
theorem B1514953 : Blo 1060614 1514953 := bstep (se 2 (by rfl) ⟨568107, by rfl⟩ : syracuseStep 1514953 = 1136215) B1136215
theorem B2694667 : Blo 1060614 2694667 := bstep (se 1 (by rfl) ⟨2021000, by rfl⟩ : syracuseStep 2694667 = 4042001) B4042001
theorem B20717207 : Blo 1060614 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B13639499 : Blo 1060614 13639499 := bstep (se 1 (by rfl) ⟨10229624, by rfl⟩ : syracuseStep 13639499 = 20459249) B20459249
theorem B5447513 : Blo 1060614 5447513 := bstep (se 2 (by rfl) ⟨2042817, by rfl⟩ : syracuseStep 5447513 = 4085635) B4085635
theorem B1515449 : Blo 1060614 1515449 := bstep (se 2 (by rfl) ⟨568293, by rfl⟩ : syracuseStep 1515449 = 1136587) B1136587
theorem B87367733 : Blo 1060614 87367733 := bstep (se 5 (by rfl) ⟨4095362, by rfl⟩ : syracuseStep 87367733 = 8190725) B8190725
theorem B3448919 : Blo 1060614 3448919 := bstep (se 1 (by rfl) ⟨2586689, by rfl⟩ : syracuseStep 3448919 = 5173379) B5173379
theorem B3580307 : Blo 1060614 3580307 := bstep (se 1 (by rfl) ⟨2685230, by rfl⟩ : syracuseStep 3580307 = 5370461) B5370461
theorem B8987213 : Blo 1060614 8987213 := bstep (se 3 (by rfl) ⟨1685102, by rfl⟩ : syracuseStep 8987213 = 3370205) B3370205
theorem B4301549 : Blo 1060614 4301549 := bstep (se 3 (by rfl) ⟨806540, by rfl⟩ : syracuseStep 4301549 = 1613081) B1613081
theorem B2270099 : Blo 1060614 2270099 := bstep (se 1 (by rfl) ⟨1702574, by rfl⟩ : syracuseStep 2270099 = 3405149) B3405149
theorem B4039571 : Blo 1060614 4039571 := bstep (se 1 (by rfl) ⟨3029678, by rfl⟩ : syracuseStep 4039571 = 6059357) B6059357
theorem B3023801 : Blo 1060614 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B5383097 : Blo 1060614 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B14526209 : Blo 1060614 14526209 := bstep (se 2 (by rfl) ⟨5447328, by rfl⟩ : syracuseStep 14526209 = 10894657) B10894657
theorem B3581711 : Blo 1060614 3581711 := bstep (se 1 (by rfl) ⟨2686283, by rfl⟩ : syracuseStep 3581711 = 5372567) B5372567
theorem B5908261 : Blo 1060614 5908261 := bstep (se 4 (by rfl) ⟨553899, by rfl⟩ : syracuseStep 5908261 = 1107799) B1107799
theorem B8071001 : Blo 1060614 8071001 := bstep (se 2 (by rfl) ⟨3026625, by rfl⟩ : syracuseStep 8071001 = 6053251) B6053251
theorem B3876761 : Blo 1060614 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B3581981 : Blo 1060614 3581981 := bstep (se 3 (by rfl) ⟨671621, by rfl⟩ : syracuseStep 3581981 = 1343243) B1343243
theorem B5384393 : Blo 1060614 5384393 := bstep (se 2 (by rfl) ⟨2019147, by rfl⟩ : syracuseStep 5384393 = 4038295) B4038295
theorem B6465851 : Blo 1060614 6465851 := bstep (se 1 (by rfl) ⟨4849388, by rfl⟩ : syracuseStep 6465851 = 9698777) B9698777
theorem B3025441 : Blo 1060614 3025441 := bstep (se 2 (by rfl) ⟨1134540, by rfl⟩ : syracuseStep 3025441 = 2269081) B2269081
theorem B8071973 : Blo 1060614 8071973 := bstep (se 4 (by rfl) ⟨756747, by rfl⟩ : syracuseStep 8071973 = 1513495) B1513495
theorem B10201945 : Blo 1060614 10201945 := bstep (se 2 (by rfl) ⟨3825729, by rfl⟩ : syracuseStep 10201945 = 7651459) B7651459
theorem B12102857 : Blo 1060614 12102857 := bstep (se 2 (by rfl) ⟨4538571, by rfl⟩ : syracuseStep 12102857 = 9077143) B9077143
theorem B10333421 : Blo 1060614 10333421 := bstep (se 3 (by rfl) ⟨1937516, by rfl⟩ : syracuseStep 10333421 = 3875033) B3875033
theorem B3583385 : Blo 1060614 3583385 := bstep (se 2 (by rfl) ⟨1343769, by rfl⟩ : syracuseStep 3583385 = 2687539) B2687539
theorem B4042169 : Blo 1060614 4042169 := bstep (se 2 (by rfl) ⟨1515813, by rfl⟩ : syracuseStep 4042169 = 3031627) B3031627
theorem B14757329 : Blo 1060614 14757329 := bstep (se 2 (by rfl) ⟨5533998, by rfl⟩ : syracuseStep 14757329 = 11067997) B11067997
theorem B1060615 : Blo 1060614 1060615 := bstep (se 1 (by rfl) ⟨795461, by rfl⟩ : syracuseStep 1060615 = 1590923) B1590923
theorem B1060623 : Blo 1060614 1060623 := bstep (se 1 (by rfl) ⟨795467, by rfl⟩ : syracuseStep 1060623 = 1590935) B1590935
theorem B3026717 : Blo 1060614 3026717 := bstep (se 3 (by rfl) ⟨567509, by rfl⟩ : syracuseStep 3026717 = 1135019) B1135019
theorem B1060667 : Blo 1060614 1060667 := bstep (se 1 (by rfl) ⟨795500, by rfl⟩ : syracuseStep 1060667 = 1591001) B1591001
theorem B12922739 : Blo 1060614 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B1060743 : Blo 1060614 1060743 := bstep (se 1 (by rfl) ⟨795557, by rfl⟩ : syracuseStep 1060743 = 1591115) B1591115
theorem B1060751 : Blo 1060614 1060751 := bstep (se 1 (by rfl) ⟨795563, by rfl⟩ : syracuseStep 1060751 = 1591127) B1591127
theorem B4599737 : Blo 1060614 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B1060795 : Blo 1060614 1060795 := bstep (se 1 (by rfl) ⟨795596, by rfl⟩ : syracuseStep 1060795 = 1591193) B1591193
theorem B3026945 : Blo 1060614 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B1060871 : Blo 1060614 1060871 := bstep (se 1 (by rfl) ⟨795653, by rfl⟩ : syracuseStep 1060871 = 1591307) B1591307
theorem B1060879 : Blo 1060614 1060879 := bstep (se 1 (by rfl) ⟨795659, by rfl⟩ : syracuseStep 1060879 = 1591319) B1591319
theorem B1060923 : Blo 1060614 1060923 := bstep (se 1 (by rfl) ⟨795692, by rfl⟩ : syracuseStep 1060923 = 1591385) B1591385
theorem B3584087 : Blo 1060614 3584087 := bstep (se 1 (by rfl) ⟨2688065, by rfl⟩ : syracuseStep 3584087 = 5376131) B5376131
theorem B1060999 : Blo 1060614 1060999 := bstep (se 1 (by rfl) ⟨795749, by rfl⟩ : syracuseStep 1060999 = 1591499) B1591499
theorem B1061007 : Blo 1060614 1061007 := bstep (se 1 (by rfl) ⟨795755, by rfl⟩ : syracuseStep 1061007 = 1591511) B1591511
theorem B1061051 : Blo 1060614 1061051 := bstep (se 1 (by rfl) ⟨795788, by rfl⟩ : syracuseStep 1061051 = 1591577) B1591577
theorem B1061127 : Blo 1060614 1061127 := bstep (se 1 (by rfl) ⟨795845, by rfl⟩ : syracuseStep 1061127 = 1591691) B1591691
theorem B1061135 : Blo 1060614 1061135 := bstep (se 1 (by rfl) ⟨795851, by rfl⟩ : syracuseStep 1061135 = 1591703) B1591703
theorem B1061179 : Blo 1060614 1061179 := bstep (se 1 (by rfl) ⟨795884, by rfl⟩ : syracuseStep 1061179 = 1591769) B1591769
theorem B1913147 : Blo 1060614 1913147 := bstep (se 1 (by rfl) ⟨1434860, by rfl⟩ : syracuseStep 1913147 = 2869721) B2869721
theorem B3027287 : Blo 1060614 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B4534643 : Blo 1060614 4534643 := bstep (se 1 (by rfl) ⟨3400982, by rfl⟩ : syracuseStep 4534643 = 6801965) B6801965
theorem B1061255 : Blo 1060614 1061255 := bstep (se 1 (by rfl) ⟨795941, by rfl⟩ : syracuseStep 1061255 = 1591883) B1591883
theorem B2044295 : Blo 1060614 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B1061263 : Blo 1060614 1061263 := bstep (se 1 (by rfl) ⟨795947, by rfl⟩ : syracuseStep 1061263 = 1591895) B1591895
theorem B1061307 : Blo 1060614 1061307 := bstep (se 1 (by rfl) ⟨795980, by rfl⟩ : syracuseStep 1061307 = 1591961) B1591961
theorem B3027401 : Blo 1060614 3027401 := bstep (se 2 (by rfl) ⟨1135275, by rfl⟩ : syracuseStep 3027401 = 2270551) B2270551
theorem B1061383 : Blo 1060614 1061383 := bstep (se 1 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 1061383 = 1592075) B1592075
theorem B1061391 : Blo 1060614 1061391 := bstep (se 1 (by rfl) ⟨796043, by rfl⟩ : syracuseStep 1061391 = 1592087) B1592087
theorem B1061435 : Blo 1060614 1061435 := bstep (se 1 (by rfl) ⟨796076, by rfl⟩ : syracuseStep 1061435 = 1592153) B1592153
theorem B3584573 : Blo 1060614 3584573 := bstep (se 3 (by rfl) ⟨672107, by rfl⟩ : syracuseStep 3584573 = 1344215) B1344215
theorem B1061511 : Blo 1060614 1061511 := bstep (se 1 (by rfl) ⟨796133, by rfl⟩ : syracuseStep 1061511 = 1592267) B1592267
theorem B1061519 : Blo 1060614 1061519 := bstep (se 1 (by rfl) ⟨796139, by rfl⟩ : syracuseStep 1061519 = 1592279) B1592279
theorem B1061563 : Blo 1060614 1061563 := bstep (se 1 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 1061563 = 1592345) B1592345
theorem B1061639 : Blo 1060614 1061639 := bstep (se 1 (by rfl) ⟨796229, by rfl⟩ : syracuseStep 1061639 = 1592459) B1592459
theorem B1061647 : Blo 1060614 1061647 := bstep (se 1 (by rfl) ⟨796235, by rfl⟩ : syracuseStep 1061647 = 1592471) B1592471
theorem B1061691 : Blo 1060614 1061691 := bstep (se 1 (by rfl) ⟨796268, by rfl⟩ : syracuseStep 1061691 = 1592537) B1592537
theorem B1061767 : Blo 1060614 1061767 := bstep (se 1 (by rfl) ⟨796325, by rfl⟩ : syracuseStep 1061767 = 1592651) B1592651
theorem B5747591 : Blo 1060614 5747591 := bstep (se 1 (by rfl) ⟨4310693, by rfl⟩ : syracuseStep 5747591 = 8621387) B8621387
theorem B1061775 : Blo 1060614 1061775 := bstep (se 1 (by rfl) ⟨796331, by rfl⟩ : syracuseStep 1061775 = 1592663) B1592663
theorem B1061819 : Blo 1060614 1061819 := bstep (se 1 (by rfl) ⟨796364, by rfl⟩ : syracuseStep 1061819 = 1592729) B1592729
theorem B1061895 : Blo 1060614 1061895 := bstep (se 1 (by rfl) ⟨796421, by rfl⟩ : syracuseStep 1061895 = 1592843) B1592843
theorem B1061903 : Blo 1060614 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B1061947 : Blo 1060614 1061947 := bstep (se 1 (by rfl) ⟨796460, by rfl⟩ : syracuseStep 1061947 = 1592921) B1592921
theorem B1062023 : Blo 1060614 1062023 := bstep (se 1 (by rfl) ⟨796517, by rfl⟩ : syracuseStep 1062023 = 1593035) B1593035
theorem B1062031 : Blo 1060614 1062031 := bstep (se 1 (by rfl) ⟨796523, by rfl⟩ : syracuseStep 1062031 = 1593047) B1593047
theorem B1062075 : Blo 1060614 1062075 := bstep (se 1 (by rfl) ⟨796556, by rfl⟩ : syracuseStep 1062075 = 1593113) B1593113
theorem B1062151 : Blo 1060614 1062151 := bstep (se 1 (by rfl) ⟨796613, by rfl⟩ : syracuseStep 1062151 = 1593227) B1593227
theorem B1062159 : Blo 1060614 1062159 := bstep (se 1 (by rfl) ⟨796619, by rfl⟩ : syracuseStep 1062159 = 1593239) B1593239
theorem B4371727 : Blo 1060614 4371727 := bstep (se 1 (by rfl) ⟨3278795, by rfl⟩ : syracuseStep 4371727 = 6557591) B6557591
theorem B1062203 : Blo 1060614 1062203 := bstep (se 1 (by rfl) ⟨796652, by rfl⟩ : syracuseStep 1062203 = 1593305) B1593305
theorem B1062279 : Blo 1060614 1062279 := bstep (se 1 (by rfl) ⟨796709, by rfl⟩ : syracuseStep 1062279 = 1593419) B1593419
theorem B1193359 : Blo 1060614 1193359 := bstep (se 1 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 1193359 = 1790039) B1790039
theorem B1062287 : Blo 1060614 1062287 := bstep (se 1 (by rfl) ⟨796715, by rfl⟩ : syracuseStep 1062287 = 1593431) B1593431
theorem B1062331 : Blo 1060614 1062331 := bstep (se 1 (by rfl) ⟨796748, by rfl⟩ : syracuseStep 1062331 = 1593497) B1593497
theorem B1062407 : Blo 1060614 1062407 := bstep (se 1 (by rfl) ⟨796805, by rfl⟩ : syracuseStep 1062407 = 1593611) B1593611
theorem B1062415 : Blo 1060614 1062415 := bstep (se 1 (by rfl) ⟨796811, by rfl⟩ : syracuseStep 1062415 = 1593623) B1593623
theorem B1062459 : Blo 1060614 1062459 := bstep (se 1 (by rfl) ⟨796844, by rfl⟩ : syracuseStep 1062459 = 1593689) B1593689
theorem B1062535 : Blo 1060614 1062535 := bstep (se 1 (by rfl) ⟨796901, by rfl⟩ : syracuseStep 1062535 = 1593803) B1593803
theorem B1062543 : Blo 1060614 1062543 := bstep (se 1 (by rfl) ⟨796907, by rfl⟩ : syracuseStep 1062543 = 1593815) B1593815
theorem B1062587 : Blo 1060614 1062587 := bstep (se 1 (by rfl) ⟨796940, by rfl⟩ : syracuseStep 1062587 = 1593881) B1593881
theorem B1062663 : Blo 1060614 1062663 := bstep (se 1 (by rfl) ⟨796997, by rfl⟩ : syracuseStep 1062663 = 1593995) B1593995
theorem B1062671 : Blo 1060614 1062671 := bstep (se 1 (by rfl) ⟨797003, by rfl⟩ : syracuseStep 1062671 = 1594007) B1594007
theorem B1062715 : Blo 1060614 1062715 := bstep (se 1 (by rfl) ⟨797036, by rfl⟩ : syracuseStep 1062715 = 1594073) B1594073
theorem B1193863 : Blo 1060614 1193863 := bstep (se 1 (by rfl) ⟨895397, by rfl⟩ : syracuseStep 1193863 = 1790795) B1790795
theorem B1062791 : Blo 1060614 1062791 := bstep (se 1 (by rfl) ⟨797093, by rfl⟩ : syracuseStep 1062791 = 1594187) B1594187
theorem B1062799 : Blo 1060614 1062799 := bstep (se 1 (by rfl) ⟨797099, by rfl⟩ : syracuseStep 1062799 = 1594199) B1594199
theorem B12269465 : Blo 1060614 12269465 := bstep (se 2 (by rfl) ⟨4601049, by rfl⟩ : syracuseStep 12269465 = 9202099) B9202099
theorem B3585977 : Blo 1060614 3585977 := bstep (se 2 (by rfl) ⟨1344741, by rfl⟩ : syracuseStep 3585977 = 2689483) B2689483
theorem B1062843 : Blo 1060614 1062843 := bstep (se 1 (by rfl) ⟨797132, by rfl⟩ : syracuseStep 1062843 = 1594265) B1594265
theorem B1062919 : Blo 1060614 1062919 := bstep (se 1 (by rfl) ⟨797189, by rfl⟩ : syracuseStep 1062919 = 1594379) B1594379
theorem B1062927 : Blo 1060614 1062927 := bstep (se 1 (by rfl) ⟨797195, by rfl⟩ : syracuseStep 1062927 = 1594391) B1594391
theorem B12105773 : Blo 1060614 12105773 := bstep (se 3 (by rfl) ⟨2269832, by rfl⟩ : syracuseStep 12105773 = 4539665) B4539665
theorem B1194043 : Blo 1060614 1194043 := bstep (se 1 (by rfl) ⟨895532, by rfl⟩ : syracuseStep 1194043 = 1791065) B1791065
theorem B1062971 : Blo 1060614 1062971 := bstep (se 1 (by rfl) ⟨797228, by rfl⟩ : syracuseStep 1062971 = 1594457) B1594457
theorem B5748803 : Blo 1060614 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B1063047 : Blo 1060614 1063047 := bstep (se 1 (by rfl) ⟨797285, by rfl⟩ : syracuseStep 1063047 = 1594571) B1594571
theorem B1063055 : Blo 1060614 1063055 := bstep (se 1 (by rfl) ⟨797291, by rfl⟩ : syracuseStep 1063055 = 1594583) B1594583
theorem B3029177 : Blo 1060614 3029177 := bstep (se 2 (by rfl) ⟨1135941, by rfl⟩ : syracuseStep 3029177 = 2271883) B2271883
theorem B1063099 : Blo 1060614 1063099 := bstep (se 1 (by rfl) ⟨797324, by rfl⟩ : syracuseStep 1063099 = 1594649) B1594649
theorem B4536557 : Blo 1060614 4536557 := bstep (se 3 (by rfl) ⟨850604, by rfl⟩ : syracuseStep 4536557 = 1701209) B1701209
theorem B1063175 : Blo 1060614 1063175 := bstep (se 1 (by rfl) ⟨797381, by rfl⟩ : syracuseStep 1063175 = 1594763) B1594763
theorem B1063183 : Blo 1060614 1063183 := bstep (se 1 (by rfl) ⟨797387, by rfl⟩ : syracuseStep 1063183 = 1594775) B1594775
theorem B1063227 : Blo 1060614 1063227 := bstep (se 1 (by rfl) ⟨797420, by rfl⟩ : syracuseStep 1063227 = 1594841) B1594841
theorem B1063303 : Blo 1060614 1063303 := bstep (se 1 (by rfl) ⟨797477, by rfl⟩ : syracuseStep 1063303 = 1594955) B1594955
theorem B1063311 : Blo 1060614 1063311 := bstep (se 1 (by rfl) ⟨797483, by rfl⟩ : syracuseStep 1063311 = 1594967) B1594967
theorem B1063355 : Blo 1060614 1063355 := bstep (se 1 (by rfl) ⟨797516, by rfl⟩ : syracuseStep 1063355 = 1595033) B1595033
theorem B6797789 : Blo 1060614 6797789 := bstep (se 3 (by rfl) ⟨1274585, by rfl⟩ : syracuseStep 6797789 = 2549171) B2549171
theorem B1063431 : Blo 1060614 1063431 := bstep (se 1 (by rfl) ⟨797573, by rfl⟩ : syracuseStep 1063431 = 1595147) B1595147
theorem B3586571 : Blo 1060614 3586571 := bstep (se 1 (by rfl) ⟨2689928, by rfl⟩ : syracuseStep 3586571 = 5379857) B5379857
theorem B1194511 : Blo 1060614 1194511 := bstep (se 1 (by rfl) ⟨895883, by rfl⟩ : syracuseStep 1194511 = 1791767) B1791767
theorem B1063439 : Blo 1060614 1063439 := bstep (se 1 (by rfl) ⟨797579, by rfl⟩ : syracuseStep 1063439 = 1595159) B1595159
theorem B1063483 : Blo 1060614 1063483 := bstep (se 1 (by rfl) ⟨797612, by rfl⟩ : syracuseStep 1063483 = 1595225) B1595225
theorem B3586679 : Blo 1060614 3586679 := bstep (se 1 (by rfl) ⟨2690009, by rfl⟩ : syracuseStep 3586679 = 5380019) B5380019
theorem B1063559 : Blo 1060614 1063559 := bstep (se 1 (by rfl) ⟨797669, by rfl⟩ : syracuseStep 1063559 = 1595339) B1595339
theorem B1063567 : Blo 1060614 1063567 := bstep (se 1 (by rfl) ⟨797675, by rfl⟩ : syracuseStep 1063567 = 1595351) B1595351
theorem B1063611 : Blo 1060614 1063611 := bstep (se 1 (by rfl) ⟨797708, by rfl⟩ : syracuseStep 1063611 = 1595417) B1595417
theorem B1063687 : Blo 1060614 1063687 := bstep (se 1 (by rfl) ⟨797765, by rfl⟩ : syracuseStep 1063687 = 1595531) B1595531
theorem B1063695 : Blo 1060614 1063695 := bstep (se 1 (by rfl) ⟨797771, by rfl⟩ : syracuseStep 1063695 = 1595543) B1595543
theorem B5749541 : Blo 1060614 5749541 := bstep (se 4 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 5749541 = 1078039) B1078039
theorem B1063739 : Blo 1060614 1063739 := bstep (se 1 (by rfl) ⟨797804, by rfl⟩ : syracuseStep 1063739 = 1595609) B1595609
theorem B1063815 : Blo 1060614 1063815 := bstep (se 1 (by rfl) ⟨797861, by rfl⟩ : syracuseStep 1063815 = 1595723) B1595723
theorem B1063823 : Blo 1060614 1063823 := bstep (se 1 (by rfl) ⟨797867, by rfl⟩ : syracuseStep 1063823 = 1595735) B1595735
theorem B3062681 : Blo 1060614 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B4537241 : Blo 1060614 4537241 := bstep (se 2 (by rfl) ⟨1701465, by rfl⟩ : syracuseStep 4537241 = 3402931) B3402931
theorem B1063867 : Blo 1060614 1063867 := bstep (se 1 (by rfl) ⟨797900, by rfl⟩ : syracuseStep 1063867 = 1595801) B1595801
theorem B1195015 : Blo 1060614 1195015 := bstep (se 1 (by rfl) ⟨896261, by rfl⟩ : syracuseStep 1195015 = 1792523) B1792523
theorem B1063943 : Blo 1060614 1063943 := bstep (se 1 (by rfl) ⟨797957, by rfl⟩ : syracuseStep 1063943 = 1595915) B1595915
theorem B1063951 : Blo 1060614 1063951 := bstep (se 1 (by rfl) ⟨797963, by rfl⟩ : syracuseStep 1063951 = 1595927) B1595927
theorem B1063995 : Blo 1060614 1063995 := bstep (se 1 (by rfl) ⟨797996, by rfl⟩ : syracuseStep 1063995 = 1595993) B1595993
theorem B1064071 : Blo 1060614 1064071 := bstep (se 1 (by rfl) ⟨798053, by rfl⟩ : syracuseStep 1064071 = 1596107) B1596107
theorem B1064079 : Blo 1060614 1064079 := bstep (se 1 (by rfl) ⟨798059, by rfl⟩ : syracuseStep 1064079 = 1596119) B1596119
theorem B3030169 : Blo 1060614 3030169 := bstep (se 2 (by rfl) ⟨1136313, by rfl⟩ : syracuseStep 3030169 = 2272627) B2272627
theorem B1195195 : Blo 1060614 1195195 := bstep (se 1 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 1195195 = 1792793) B1792793
theorem B1064123 : Blo 1060614 1064123 := bstep (se 1 (by rfl) ⟨798092, by rfl⟩ : syracuseStep 1064123 = 1596185) B1596185
theorem B2014409 : Blo 1060614 2014409 := bstep (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) B1510807
theorem B3587273 : Blo 1060614 3587273 := bstep (se 2 (by rfl) ⟨1345227, by rfl⟩ : syracuseStep 3587273 = 2690455) B2690455
theorem B1064199 : Blo 1060614 1064199 := bstep (se 1 (by rfl) ⟨798149, by rfl⟩ : syracuseStep 1064199 = 1596299) B1596299
theorem B4537615 : Blo 1060614 4537615 := bstep (se 1 (by rfl) ⟨3403211, by rfl⟩ : syracuseStep 4537615 = 6806423) B6806423
theorem B1064207 : Blo 1060614 1064207 := bstep (se 1 (by rfl) ⟨798155, by rfl⟩ : syracuseStep 1064207 = 1596311) B1596311
theorem B1064251 : Blo 1060614 1064251 := bstep (se 1 (by rfl) ⟨798188, by rfl⟩ : syracuseStep 1064251 = 1596377) B1596377
theorem B1064327 : Blo 1060614 1064327 := bstep (se 1 (by rfl) ⟨798245, by rfl⟩ : syracuseStep 1064327 = 1596491) B1596491
theorem B1064335 : Blo 1060614 1064335 := bstep (se 1 (by rfl) ⟨798251, by rfl⟩ : syracuseStep 1064335 = 1596503) B1596503
theorem B1064379 : Blo 1060614 1064379 := bstep (se 1 (by rfl) ⟨798284, by rfl⟩ : syracuseStep 1064379 = 1596569) B1596569
theorem B1064455 : Blo 1060614 1064455 := bstep (se 1 (by rfl) ⟨798341, by rfl⟩ : syracuseStep 1064455 = 1596683) B1596683
theorem B1064463 : Blo 1060614 1064463 := bstep (se 1 (by rfl) ⟨798347, by rfl⟩ : syracuseStep 1064463 = 1596695) B1596695
theorem B1064507 : Blo 1060614 1064507 := bstep (se 1 (by rfl) ⟨798380, by rfl⟩ : syracuseStep 1064507 = 1596761) B1596761
theorem B1064583 : Blo 1060614 1064583 := bstep (se 1 (by rfl) ⟨798437, by rfl⟩ : syracuseStep 1064583 = 1596875) B1596875
theorem B1195663 : Blo 1060614 1195663 := bstep (se 1 (by rfl) ⟨896747, by rfl⟩ : syracuseStep 1195663 = 1793495) B1793495
theorem B1064591 : Blo 1060614 1064591 := bstep (se 1 (by rfl) ⟨798443, by rfl⟩ : syracuseStep 1064591 = 1596887) B1596887
theorem B3587975 : Blo 1060614 3587975 := bstep (se 1 (by rfl) ⟨2690981, by rfl⟩ : syracuseStep 3587975 = 5381963) B5381963
theorem B2015275 : Blo 1060614 2015275 := bstep (se 1 (by rfl) ⟨1511456, by rfl⟩ : syracuseStep 2015275 = 3022913) B3022913
theorem B2015351 : Blo 1060614 2015351 := bstep (se 1 (by rfl) ⟨1511513, by rfl⟩ : syracuseStep 2015351 = 3023027) B3023027
theorem B1196167 : Blo 1060614 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B12927221 : Blo 1060614 12927221 := bstep (se 5 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 12927221 = 1211927) B1211927
theorem B3588353 : Blo 1060614 3588353 := bstep (se 2 (by rfl) ⟨1345632, by rfl⟩ : syracuseStep 3588353 = 2691265) B2691265
theorem B1196347 : Blo 1060614 1196347 := bstep (se 1 (by rfl) ⟨897260, by rfl⟩ : syracuseStep 1196347 = 1794521) B1794521
theorem B9191825 : Blo 1060614 9191825 := bstep (se 2 (by rfl) ⟨3446934, by rfl⟩ : syracuseStep 9191825 = 6893869) B6893869
theorem B9060983 : Blo 1060614 9060983 := bstep (se 1 (by rfl) ⟨6795737, by rfl⟩ : syracuseStep 9060983 = 13591475) B13591475
theorem B5522093 : Blo 1060614 5522093 := bstep (se 3 (by rfl) ⟨1035392, by rfl⟩ : syracuseStep 5522093 = 2070785) B2070785
theorem B6636269 : Blo 1060614 6636269 := bstep (se 3 (by rfl) ⟨1244300, by rfl⟩ : syracuseStep 6636269 = 2488601) B2488601
theorem B1196815 : Blo 1060614 1196815 := bstep (se 1 (by rfl) ⟨897611, by rfl⟩ : syracuseStep 1196815 = 1795223) B1795223
theorem B3589163 : Blo 1060614 3589163 := bstep (se 1 (by rfl) ⟨2691872, by rfl⟩ : syracuseStep 3589163 = 5383745) B5383745
theorem B1197319 : Blo 1060614 1197319 := bstep (se 1 (by rfl) ⟨897989, by rfl⟩ : syracuseStep 1197319 = 1795979) B1795979
theorem B3065149 : Blo 1060614 3065149 := bstep (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) B1149431
theorem B8078777 : Blo 1060614 8078777 := bstep (se 2 (by rfl) ⟨3029541, by rfl⟩ : syracuseStep 8078777 = 6059083) B6059083
theorem B1197499 : Blo 1060614 1197499 := bstep (se 1 (by rfl) ⟨898124, by rfl⟩ : syracuseStep 1197499 = 1796249) B1796249
theorem B2868779 : Blo 1060614 2868779 := bstep (se 1 (by rfl) ⟨2151584, by rfl⟩ : syracuseStep 2868779 = 4303169) B4303169
theorem B1590971 : Blo 1060614 1590971 := bstep (se 1 (by rfl) ⟨1193228, by rfl⟩ : syracuseStep 1590971 = 2386457) B2386457
theorem B1591031 : Blo 1060614 1591031 := bstep (se 1 (by rfl) ⟨1193273, by rfl⟩ : syracuseStep 1591031 = 2386547) B2386547
theorem B9094913 : Blo 1060614 9094913 := bstep (se 2 (by rfl) ⟨3410592, by rfl⟩ : syracuseStep 9094913 = 6821185) B6821185
theorem B1591055 : Blo 1060614 1591055 := bstep (se 1 (by rfl) ⟨1193291, by rfl⟩ : syracuseStep 1591055 = 2386583) B2386583
theorem B1591097 : Blo 1060614 1591097 := bstep (se 2 (by rfl) ⟨596661, by rfl⟩ : syracuseStep 1591097 = 1193323) B1193323
theorem B1591175 : Blo 1060614 1591175 := bstep (se 1 (by rfl) ⟨1193381, by rfl⟩ : syracuseStep 1591175 = 2386763) B2386763
theorem B1591211 : Blo 1060614 1591211 := bstep (se 1 (by rfl) ⟨1193408, by rfl⟩ : syracuseStep 1591211 = 2386817) B2386817
theorem B1591241 : Blo 1060614 1591241 := bstep (se 2 (by rfl) ⟨596715, by rfl⟩ : syracuseStep 1591241 = 1193431) B1193431
theorem B5097437 : Blo 1060614 5097437 := bstep (se 3 (by rfl) ⟨955769, by rfl⟩ : syracuseStep 5097437 = 1911539) B1911539
theorem B2017295 : Blo 1060614 2017295 := bstep (se 1 (by rfl) ⟨1512971, by rfl⟩ : syracuseStep 2017295 = 3025943) B3025943
theorem B1591355 : Blo 1060614 1591355 := bstep (se 1 (by rfl) ⟨1193516, by rfl⟩ : syracuseStep 1591355 = 2387033) B2387033
theorem B1591415 : Blo 1060614 1591415 := bstep (se 1 (by rfl) ⟨1193561, by rfl⟩ : syracuseStep 1591415 = 2387123) B2387123
theorem B1591439 : Blo 1060614 1591439 := bstep (se 1 (by rfl) ⟨1193579, by rfl⟩ : syracuseStep 1591439 = 2387159) B2387159
theorem B1591481 : Blo 1060614 1591481 := bstep (se 2 (by rfl) ⟨596805, by rfl⟩ : syracuseStep 1591481 = 1193611) B1193611
theorem B6047945 : Blo 1060614 6047945 := bstep (se 2 (by rfl) ⟨2267979, by rfl⟩ : syracuseStep 6047945 = 4535959) B4535959
theorem B8407277 : Blo 1060614 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B1591559 : Blo 1060614 1591559 := bstep (se 1 (by rfl) ⟨1193669, by rfl⟩ : syracuseStep 1591559 = 2387339) B2387339
theorem B6473999 : Blo 1060614 6473999 := bstep (se 1 (by rfl) ⟨4855499, by rfl⟩ : syracuseStep 6473999 = 9710999) B9710999
theorem B1591595 : Blo 1060614 1591595 := bstep (se 1 (by rfl) ⟨1193696, by rfl⟩ : syracuseStep 1591595 = 2387393) B2387393
theorem B8735035 : Blo 1060614 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B3590459 : Blo 1060614 3590459 := bstep (se 1 (by rfl) ⟨2692844, by rfl⟩ : syracuseStep 3590459 = 5385689) B5385689
theorem B1591625 : Blo 1060614 1591625 := bstep (se 2 (by rfl) ⟨596859, by rfl⟩ : syracuseStep 1591625 = 1193719) B1193719
theorem B1591739 : Blo 1060614 1591739 := bstep (se 1 (by rfl) ⟨1193804, by rfl⟩ : syracuseStep 1591739 = 2387609) B2387609
theorem B1591799 : Blo 1060614 1591799 := bstep (se 1 (by rfl) ⟨1193849, by rfl⟩ : syracuseStep 1591799 = 2387699) B2387699
theorem B1133071 : Blo 1060614 1133071 := bstep (se 1 (by rfl) ⟨849803, by rfl⟩ : syracuseStep 1133071 = 1699607) B1699607
theorem B1591823 : Blo 1060614 1591823 := bstep (se 1 (by rfl) ⟨1193867, by rfl⟩ : syracuseStep 1591823 = 2387735) B2387735
theorem B1591865 : Blo 1060614 1591865 := bstep (se 2 (by rfl) ⟨596949, by rfl⟩ : syracuseStep 1591865 = 1193899) B1193899
theorem B1133191 : Blo 1060614 1133191 := bstep (se 1 (by rfl) ⟨849893, by rfl⟩ : syracuseStep 1133191 = 1699787) B1699787
theorem B1591943 : Blo 1060614 1591943 := bstep (se 1 (by rfl) ⟨1193957, by rfl⟩ : syracuseStep 1591943 = 2387915) B2387915
theorem B1591979 : Blo 1060614 1591979 := bstep (se 1 (by rfl) ⟨1193984, by rfl⟩ : syracuseStep 1591979 = 2387969) B2387969
theorem B1592009 : Blo 1060614 1592009 := bstep (se 2 (by rfl) ⟨597003, by rfl⟩ : syracuseStep 1592009 = 1194007) B1194007
theorem B3590945 : Blo 1060614 3590945 := bstep (se 2 (by rfl) ⟨1346604, by rfl⟩ : syracuseStep 3590945 = 2693209) B2693209
theorem B1592123 : Blo 1060614 1592123 := bstep (se 1 (by rfl) ⟨1194092, by rfl⟩ : syracuseStep 1592123 = 2388185) B2388185
theorem B1592183 : Blo 1060614 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B1133447 : Blo 1060614 1133447 := bstep (se 1 (by rfl) ⟨850085, by rfl⟩ : syracuseStep 1133447 = 1700171) B1700171
theorem B1592207 : Blo 1060614 1592207 := bstep (se 1 (by rfl) ⟨1194155, by rfl⟩ : syracuseStep 1592207 = 2388311) B2388311
theorem B1592249 : Blo 1060614 1592249 := bstep (se 2 (by rfl) ⟨597093, by rfl⟩ : syracuseStep 1592249 = 1194187) B1194187
theorem B1592327 : Blo 1060614 1592327 := bstep (se 1 (by rfl) ⟨1194245, by rfl⟩ : syracuseStep 1592327 = 2388491) B2388491
theorem B1592363 : Blo 1060614 1592363 := bstep (se 1 (by rfl) ⟨1194272, by rfl⟩ : syracuseStep 1592363 = 2388545) B2388545
theorem B1592393 : Blo 1060614 1592393 := bstep (se 2 (by rfl) ⟨597147, by rfl⟩ : syracuseStep 1592393 = 1194295) B1194295
theorem B1592507 : Blo 1060614 1592507 := bstep (se 1 (by rfl) ⟨1194380, by rfl⟩ : syracuseStep 1592507 = 2388761) B2388761
theorem B1592567 : Blo 1060614 1592567 := bstep (se 1 (by rfl) ⟨1194425, by rfl⟩ : syracuseStep 1592567 = 2388851) B2388851
theorem B1592591 : Blo 1060614 1592591 := bstep (se 1 (by rfl) ⟨1194443, by rfl⟩ : syracuseStep 1592591 = 2388887) B2388887
theorem B1592633 : Blo 1060614 1592633 := bstep (se 2 (by rfl) ⟨597237, by rfl⟩ : syracuseStep 1592633 = 1194475) B1194475
theorem B3591539 : Blo 1060614 3591539 := bstep (se 1 (by rfl) ⟨2693654, by rfl⟩ : syracuseStep 3591539 = 5387309) B5387309
theorem B1592711 : Blo 1060614 1592711 := bstep (se 1 (by rfl) ⟨1194533, by rfl⟩ : syracuseStep 1592711 = 2389067) B2389067
theorem B1592747 : Blo 1060614 1592747 := bstep (se 1 (by rfl) ⟨1194560, by rfl⟩ : syracuseStep 1592747 = 2389121) B2389121
theorem B1134011 : Blo 1060614 1134011 := bstep (se 1 (by rfl) ⟨850508, by rfl⟩ : syracuseStep 1134011 = 1701017) B1701017
theorem B1592777 : Blo 1060614 1592777 := bstep (se 2 (by rfl) ⟨597291, by rfl⟩ : syracuseStep 1592777 = 1194583) B1194583
theorem B2182601 : Blo 1060614 2182601 := bstep (se 2 (by rfl) ⟨818475, by rfl⟩ : syracuseStep 2182601 = 1636951) B1636951
theorem B13618691 : Blo 1060614 13618691 := bstep (se 1 (by rfl) ⟨10214018, by rfl⟩ : syracuseStep 13618691 = 20428037) B20428037
theorem B5099051 : Blo 1060614 5099051 := bstep (se 1 (by rfl) ⟨3824288, by rfl⟩ : syracuseStep 5099051 = 7648577) B7648577
theorem B1592891 : Blo 1060614 1592891 := bstep (se 1 (by rfl) ⟨1194668, by rfl⟩ : syracuseStep 1592891 = 2389337) B2389337
theorem B7654979 : Blo 1060614 7654979 := bstep (se 1 (by rfl) ⟨5741234, by rfl⟩ : syracuseStep 7654979 = 11482469) B11482469
theorem B1592951 : Blo 1060614 1592951 := bstep (se 1 (by rfl) ⟨1194713, by rfl⟩ : syracuseStep 1592951 = 2389427) B2389427
theorem B2018935 : Blo 1060614 2018935 := bstep (se 1 (by rfl) ⟨1514201, by rfl⟩ : syracuseStep 2018935 = 3028403) B3028403
theorem B1592975 : Blo 1060614 1592975 := bstep (se 1 (by rfl) ⟨1194731, by rfl⟩ : syracuseStep 1592975 = 2389463) B2389463
theorem B1593017 : Blo 1060614 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B1593095 : Blo 1060614 1593095 := bstep (se 1 (by rfl) ⟨1194821, by rfl⟩ : syracuseStep 1593095 = 2389643) B2389643
theorem B1593131 : Blo 1060614 1593131 := bstep (se 1 (by rfl) ⟨1194848, by rfl⟩ : syracuseStep 1593131 = 2389697) B2389697
theorem B1593161 : Blo 1060614 1593161 := bstep (se 2 (by rfl) ⟨597435, by rfl⟩ : syracuseStep 1593161 = 1194871) B1194871
theorem B1593275 : Blo 1060614 1593275 := bstep (se 1 (by rfl) ⟨1194956, by rfl⟩ : syracuseStep 1593275 = 2389913) B2389913
theorem B1789897 : Blo 1060614 1789897 := bstep (se 2 (by rfl) ⟨671211, by rfl⟩ : syracuseStep 1789897 = 1342423) B1342423
theorem B2150345 : Blo 1060614 2150345 := bstep (se 2 (by rfl) ⟨806379, by rfl⟩ : syracuseStep 2150345 = 1612759) B1612759
theorem B1593335 : Blo 1060614 1593335 := bstep (se 1 (by rfl) ⟨1195001, by rfl⟩ : syracuseStep 1593335 = 2390003) B2390003
theorem B10899461 : Blo 1060614 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B1593359 : Blo 1060614 1593359 := bstep (se 1 (by rfl) ⟨1195019, by rfl⟩ : syracuseStep 1593359 = 2390039) B2390039
theorem B6049835 : Blo 1060614 6049835 := bstep (se 1 (by rfl) ⟨4537376, by rfl⟩ : syracuseStep 6049835 = 9074753) B9074753
theorem B1593401 : Blo 1060614 1593401 := bstep (se 2 (by rfl) ⟨597525, by rfl⟩ : syracuseStep 1593401 = 1195051) B1195051
theorem B1593479 : Blo 1060614 1593479 := bstep (se 1 (by rfl) ⟨1195109, by rfl⟩ : syracuseStep 1593479 = 2390219) B2390219
theorem B1593515 : Blo 1060614 1593515 := bstep (se 1 (by rfl) ⟨1195136, by rfl⟩ : syracuseStep 1593515 = 2390273) B2390273
theorem B1593545 : Blo 1060614 1593545 := bstep (se 2 (by rfl) ⟨597579, by rfl⟩ : syracuseStep 1593545 = 1195159) B1195159
theorem B1364239 : Blo 1060614 1364239 := bstep (se 1 (by rfl) ⟨1023179, by rfl⟩ : syracuseStep 1364239 = 2046359) B2046359
theorem B5460239 : Blo 1060614 5460239 := bstep (se 1 (by rfl) ⟨4095179, by rfl⟩ : syracuseStep 5460239 = 8190359) B8190359
theorem B1593659 : Blo 1060614 1593659 := bstep (se 1 (by rfl) ⟨1195244, by rfl⟩ : syracuseStep 1593659 = 2390489) B2390489
theorem B1593719 : Blo 1060614 1593719 := bstep (se 1 (by rfl) ⟨1195289, by rfl⟩ : syracuseStep 1593719 = 2390579) B2390579
theorem B1593743 : Blo 1060614 1593743 := bstep (se 1 (by rfl) ⟨1195307, by rfl⟩ : syracuseStep 1593743 = 2390615) B2390615
theorem B1593785 : Blo 1060614 1593785 := bstep (se 2 (by rfl) ⟨597669, by rfl⟩ : syracuseStep 1593785 = 1195339) B1195339
theorem B1593863 : Blo 1060614 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B1593899 : Blo 1060614 1593899 := bstep (se 1 (by rfl) ⟨1195424, by rfl⟩ : syracuseStep 1593899 = 2390849) B2390849
theorem B1593929 : Blo 1060614 1593929 := bstep (se 2 (by rfl) ⟨597723, by rfl⟩ : syracuseStep 1593929 = 1195447) B1195447
theorem B1790599 : Blo 1060614 1790599 := bstep (se 1 (by rfl) ⟨1342949, by rfl⟩ : syracuseStep 1790599 = 2685899) B2685899
theorem B5100205 : Blo 1060614 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B1594043 : Blo 1060614 1594043 := bstep (se 1 (by rfl) ⟨1195532, by rfl⟩ : syracuseStep 1594043 = 2391065) B2391065
theorem B1594103 : Blo 1060614 1594103 := bstep (se 1 (by rfl) ⟨1195577, by rfl⟩ : syracuseStep 1594103 = 2391155) B2391155
theorem B1594127 : Blo 1060614 1594127 := bstep (se 1 (by rfl) ⟨1195595, by rfl⟩ : syracuseStep 1594127 = 2391191) B2391191
theorem B1594169 : Blo 1060614 1594169 := bstep (se 2 (by rfl) ⟨597813, by rfl⟩ : syracuseStep 1594169 = 1195627) B1195627
theorem B1594247 : Blo 1060614 1594247 := bstep (se 1 (by rfl) ⟨1195685, by rfl⟩ : syracuseStep 1594247 = 2391371) B2391371
theorem B1594283 : Blo 1060614 1594283 := bstep (se 1 (by rfl) ⟨1195712, by rfl⟩ : syracuseStep 1594283 = 2391425) B2391425
theorem B1594313 : Blo 1060614 1594313 := bstep (se 2 (by rfl) ⟨597867, by rfl⟩ : syracuseStep 1594313 = 1195735) B1195735
theorem B1594427 : Blo 1060614 1594427 := bstep (se 1 (by rfl) ⟨1195820, by rfl⟩ : syracuseStep 1594427 = 2391641) B2391641
theorem B1594487 : Blo 1060614 1594487 := bstep (se 1 (by rfl) ⟨1195865, by rfl⟩ : syracuseStep 1594487 = 2391731) B2391731
theorem B1594511 : Blo 1060614 1594511 := bstep (se 1 (by rfl) ⟨1195883, by rfl⟩ : syracuseStep 1594511 = 2391767) B2391767
theorem B1594553 : Blo 1060614 1594553 := bstep (se 2 (by rfl) ⟨597957, by rfl⟩ : syracuseStep 1594553 = 1195915) B1195915
theorem B1594631 : Blo 1060614 1594631 := bstep (se 1 (by rfl) ⟨1195973, by rfl⟩ : syracuseStep 1594631 = 2391947) B2391947
theorem B1791247 : Blo 1060614 1791247 := bstep (se 1 (by rfl) ⟨1343435, by rfl⟩ : syracuseStep 1791247 = 2686871) B2686871
theorem B1594667 : Blo 1060614 1594667 := bstep (se 1 (by rfl) ⟨1196000, by rfl⟩ : syracuseStep 1594667 = 2392001) B2392001
theorem B1594697 : Blo 1060614 1594697 := bstep (se 2 (by rfl) ⟨598011, by rfl⟩ : syracuseStep 1594697 = 1196023) B1196023
theorem B2020727 : Blo 1060614 2020727 := bstep (se 1 (by rfl) ⟨1515545, by rfl⟩ : syracuseStep 2020727 = 3031091) B3031091
theorem B15324551 : Blo 1060614 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B1594811 : Blo 1060614 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B6051293 : Blo 1060614 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B1594871 : Blo 1060614 1594871 := bstep (se 1 (by rfl) ⟨1196153, by rfl⟩ : syracuseStep 1594871 = 2392307) B2392307
theorem B1594895 : Blo 1060614 1594895 := bstep (se 1 (by rfl) ⟨1196171, by rfl⟩ : syracuseStep 1594895 = 2392343) B2392343
theorem B1136143 : Blo 1060614 1136143 := bstep (se 1 (by rfl) ⟨852107, by rfl⟩ : syracuseStep 1136143 = 1704215) B1704215
theorem B2020879 : Blo 1060614 2020879 := bstep (se 1 (by rfl) ⟨1515659, by rfl⟩ : syracuseStep 2020879 = 3031319) B3031319
theorem B1594937 : Blo 1060614 1594937 := bstep (se 2 (by rfl) ⟨598101, by rfl⟩ : syracuseStep 1594937 = 1196203) B1196203
theorem B25876037 : Blo 1060614 25876037 := bstep (se 4 (by rfl) ⟨2425878, by rfl⟩ : syracuseStep 25876037 = 4851757) B4851757
theorem B1595015 : Blo 1060614 1595015 := bstep (se 1 (by rfl) ⟨1196261, by rfl⟩ : syracuseStep 1595015 = 2392523) B2392523
theorem B1595051 : Blo 1060614 1595051 := bstep (se 1 (by rfl) ⟨1196288, by rfl⟩ : syracuseStep 1595051 = 2392577) B2392577
theorem B1595081 : Blo 1060614 1595081 := bstep (se 2 (by rfl) ⟨598155, by rfl⟩ : syracuseStep 1595081 = 1196311) B1196311
theorem B1791787 : Blo 1060614 1791787 := bstep (se 1 (by rfl) ⟨1343840, by rfl⟩ : syracuseStep 1791787 = 2687681) B2687681
theorem B1595195 : Blo 1060614 1595195 := bstep (se 1 (by rfl) ⟨1196396, by rfl⟩ : syracuseStep 1595195 = 2392793) B2392793
theorem B22107973 : Blo 1060614 22107973 := bstep (se 4 (by rfl) ⟨2072622, by rfl⟩ : syracuseStep 22107973 = 4145245) B4145245
theorem B1595255 : Blo 1060614 1595255 := bstep (se 1 (by rfl) ⟨1196441, by rfl⟩ : syracuseStep 1595255 = 2392883) B2392883
theorem B1595279 : Blo 1060614 1595279 := bstep (se 1 (by rfl) ⟨1196459, by rfl⟩ : syracuseStep 1595279 = 2392919) B2392919
theorem B4839353 : Blo 1060614 4839353 := bstep (se 2 (by rfl) ⟨1814757, by rfl⟩ : syracuseStep 4839353 = 3629515) B3629515
theorem B1791929 : Blo 1060614 1791929 := bstep (se 2 (by rfl) ⟨671973, by rfl⟩ : syracuseStep 1791929 = 1343947) B1343947
theorem B1595321 : Blo 1060614 1595321 := bstep (se 2 (by rfl) ⟨598245, by rfl⟩ : syracuseStep 1595321 = 1196491) B1196491
theorem B6051793 : Blo 1060614 6051793 := bstep (se 2 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 6051793 = 4538845) B4538845
theorem B1595399 : Blo 1060614 1595399 := bstep (se 1 (by rfl) ⟨1196549, by rfl⟩ : syracuseStep 1595399 = 2393099) B2393099
theorem B1595435 : Blo 1060614 1595435 := bstep (se 1 (by rfl) ⟨1196576, by rfl⟩ : syracuseStep 1595435 = 2393153) B2393153
theorem B1595465 : Blo 1060614 1595465 := bstep (se 2 (by rfl) ⟨598299, by rfl⟩ : syracuseStep 1595465 = 1196599) B1196599
theorem B1595579 : Blo 1060614 1595579 := bstep (se 1 (by rfl) ⟨1196684, by rfl⟩ : syracuseStep 1595579 = 2393369) B2393369
theorem B1595639 : Blo 1060614 1595639 := bstep (se 1 (by rfl) ⟨1196729, by rfl⟩ : syracuseStep 1595639 = 2393459) B2393459
theorem B3987713 : Blo 1060614 3987713 := bstep (se 2 (by rfl) ⟨1495392, by rfl⟩ : syracuseStep 3987713 = 2990785) B2990785
theorem B1595663 : Blo 1060614 1595663 := bstep (se 1 (by rfl) ⟨1196747, by rfl⟩ : syracuseStep 1595663 = 2393495) B2393495
theorem B1595705 : Blo 1060614 1595705 := bstep (se 2 (by rfl) ⟨598389, by rfl⟩ : syracuseStep 1595705 = 1196779) B1196779
theorem B1595783 : Blo 1060614 1595783 := bstep (se 1 (by rfl) ⟨1196837, by rfl⟩ : syracuseStep 1595783 = 2393675) B2393675
theorem B1595819 : Blo 1060614 1595819 := bstep (se 1 (by rfl) ⟨1196864, by rfl⟩ : syracuseStep 1595819 = 2393729) B2393729
theorem B1595849 : Blo 1060614 1595849 := bstep (se 2 (by rfl) ⟨598443, by rfl⟩ : syracuseStep 1595849 = 1196887) B1196887
theorem B1595963 : Blo 1060614 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B1792631 : Blo 1060614 1792631 := bstep (se 1 (by rfl) ⟨1344473, by rfl⟩ : syracuseStep 1792631 = 2688947) B2688947
theorem B1596023 : Blo 1060614 1596023 := bstep (se 1 (by rfl) ⟨1197017, by rfl⟩ : syracuseStep 1596023 = 2394035) B2394035
theorem B1596047 : Blo 1060614 1596047 := bstep (se 1 (by rfl) ⟨1197035, by rfl⟩ : syracuseStep 1596047 = 2394071) B2394071
theorem B1596089 : Blo 1060614 1596089 := bstep (se 2 (by rfl) ⟨598533, by rfl⟩ : syracuseStep 1596089 = 1197067) B1197067
theorem B1596167 : Blo 1060614 1596167 := bstep (se 1 (by rfl) ⟨1197125, by rfl⟩ : syracuseStep 1596167 = 2394251) B2394251
theorem B1596203 : Blo 1060614 1596203 := bstep (se 1 (by rfl) ⟨1197152, by rfl⟩ : syracuseStep 1596203 = 2394305) B2394305
theorem B1596233 : Blo 1060614 1596233 := bstep (se 2 (by rfl) ⟨598587, by rfl⟩ : syracuseStep 1596233 = 1197175) B1197175
theorem B1596347 : Blo 1060614 1596347 := bstep (se 1 (by rfl) ⟨1197260, by rfl⟩ : syracuseStep 1596347 = 2394521) B2394521
theorem B1596407 : Blo 1060614 1596407 := bstep (se 1 (by rfl) ⟨1197305, by rfl⟩ : syracuseStep 1596407 = 2394611) B2394611
theorem B1596431 : Blo 1060614 1596431 := bstep (se 1 (by rfl) ⟨1197323, by rfl⟩ : syracuseStep 1596431 = 2394647) B2394647
theorem B1596473 : Blo 1060614 1596473 := bstep (se 2 (by rfl) ⟨598677, by rfl⟩ : syracuseStep 1596473 = 1197355) B1197355
theorem B1793083 : Blo 1060614 1793083 := bstep (se 1 (by rfl) ⟨1344812, by rfl⟩ : syracuseStep 1793083 = 2689625) B2689625
theorem B1596551 : Blo 1060614 1596551 := bstep (se 1 (by rfl) ⟨1197413, by rfl⟩ : syracuseStep 1596551 = 2394827) B2394827
theorem B1596587 : Blo 1060614 1596587 := bstep (se 1 (by rfl) ⟨1197440, by rfl⟩ : syracuseStep 1596587 = 2394881) B2394881
theorem B1793225 : Blo 1060614 1793225 := bstep (se 2 (by rfl) ⟨672459, by rfl⟩ : syracuseStep 1793225 = 1344919) B1344919
theorem B1596617 : Blo 1060614 1596617 := bstep (se 2 (by rfl) ⟨598731, by rfl⟩ : syracuseStep 1596617 = 1197463) B1197463
theorem B1596731 : Blo 1060614 1596731 := bstep (se 1 (by rfl) ⟨1197548, by rfl⟩ : syracuseStep 1596731 = 2395097) B2395097
theorem B1596791 : Blo 1060614 1596791 := bstep (se 1 (by rfl) ⟨1197593, by rfl⟩ : syracuseStep 1596791 = 2395187) B2395187
theorem B1596815 : Blo 1060614 1596815 := bstep (se 1 (by rfl) ⟨1197611, by rfl⟩ : syracuseStep 1596815 = 2395223) B2395223
theorem B1596857 : Blo 1060614 1596857 := bstep (se 2 (by rfl) ⟨598821, by rfl⟩ : syracuseStep 1596857 = 1197643) B1197643
theorem B6807347 : Blo 1060614 6807347 := bstep (se 1 (by rfl) ⟨5105510, by rfl⟩ : syracuseStep 6807347 = 10211021) B10211021
theorem B4546363 : Blo 1060614 4546363 := bstep (se 1 (by rfl) ⟨3409772, by rfl⟩ : syracuseStep 4546363 = 6819545) B6819545
theorem B1793927 : Blo 1060614 1793927 := bstep (se 1 (by rfl) ⟨1345445, by rfl⟩ : syracuseStep 1793927 = 2690891) B2690891
theorem B6053777 : Blo 1060614 6053777 := bstep (se 2 (by rfl) ⟨2270166, by rfl⟩ : syracuseStep 6053777 = 4540333) B4540333
theorem B12115979 : Blo 1060614 12115979 := bstep (se 1 (by rfl) ⟨9086984, by rfl⟩ : syracuseStep 12115979 = 18173969) B18173969
theorem B2187383 : Blo 1060614 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B3236125 : Blo 1060614 3236125 := bstep (se 3 (by rfl) ⟨606773, by rfl⟩ : syracuseStep 3236125 = 1213547) B1213547
theorem B1794575 : Blo 1060614 1794575 := bstep (se 1 (by rfl) ⟨1345931, by rfl⟩ : syracuseStep 1794575 = 2691863) B2691863
theorem B3400393 : Blo 1060614 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B1795115 : Blo 1060614 1795115 := bstep (se 1 (by rfl) ⟨1346336, by rfl⟩ : syracuseStep 1795115 = 2692673) B2692673
theorem B2548795 : Blo 1060614 2548795 := bstep (se 1 (by rfl) ⟨1911596, by rfl⟩ : syracuseStep 2548795 = 3823193) B3823193
theorem B2876563 : Blo 1060614 2876563 := bstep (se 1 (by rfl) ⟨2157422, by rfl⟩ : syracuseStep 2876563 = 4314845) B4314845
theorem B3237011 : Blo 1060614 3237011 := bstep (se 1 (by rfl) ⟨2427758, by rfl⟩ : syracuseStep 3237011 = 4855517) B4855517
theorem B1795513 : Blo 1060614 1795513 := bstep (se 2 (by rfl) ⟨673317, by rfl⟩ : syracuseStep 1795513 = 1346635) B1346635
theorem B5531165 : Blo 1060614 5531165 := bstep (se 3 (by rfl) ⟨1037093, by rfl⟩ : syracuseStep 5531165 = 2074187) B2074187
theorem B21784139 : Blo 1060614 21784139 := bstep (se 1 (by rfl) ⟨16338104, by rfl⟩ : syracuseStep 21784139 = 32676209) B32676209
theorem B27617093 : Blo 1060614 27617093 := bstep (se 4 (by rfl) ⟨2589102, by rfl⟩ : syracuseStep 27617093 = 5178205) B5178205
theorem B1796215 : Blo 1060614 1796215 := bstep (se 1 (by rfl) ⟨1347161, by rfl⟩ : syracuseStep 1796215 = 2694323) B2694323
theorem B1796411 : Blo 1060614 1796411 := bstep (se 1 (by rfl) ⟨1347308, by rfl⟩ : syracuseStep 1796411 = 2694617) B2694617
theorem B11495965 : Blo 1060614 11495965 := bstep (se 3 (by rfl) ⟨2155493, by rfl⟩ : syracuseStep 11495965 = 4310987) B4310987
theorem B2386475 : Blo 1060614 2386475 := bstep (se 1 (by rfl) ⟨1789856, by rfl⟩ : syracuseStep 2386475 = 3579713) B3579713
theorem B2157115 : Blo 1060614 2157115 := bstep (se 1 (by rfl) ⟨1617836, by rfl⟩ : syracuseStep 2157115 = 3235673) B3235673
theorem B2386835 : Blo 1060614 2386835 := bstep (se 1 (by rfl) ⟨1790126, by rfl⟩ : syracuseStep 2386835 = 3580253) B3580253
theorem B2386889 : Blo 1060614 2386889 := bstep (se 2 (by rfl) ⟨895083, by rfl⟩ : syracuseStep 2386889 = 1790167) B1790167
theorem B12905419 : Blo 1060614 12905419 := bstep (se 1 (by rfl) ⟨9679064, by rfl⟩ : syracuseStep 12905419 = 19358129) B19358129
theorem B20704261 : Blo 1060614 20704261 := bstep (se 4 (by rfl) ⟨1941024, by rfl⟩ : syracuseStep 20704261 = 3882049) B3882049
theorem B1535035 : Blo 1060614 1535035 := bstep (se 1 (by rfl) ⟨1151276, by rfl⟩ : syracuseStep 1535035 = 2302553) B2302553
theorem B5107319 : Blo 1060614 5107319 := bstep (se 1 (by rfl) ⟨3830489, by rfl⟩ : syracuseStep 5107319 = 7660979) B7660979
theorem B2387591 : Blo 1060614 2387591 := bstep (se 1 (by rfl) ⟨1790693, by rfl⟩ : syracuseStep 2387591 = 3581387) B3581387
theorem B5828269 : Blo 1060614 5828269 := bstep (se 3 (by rfl) ⟨1092800, by rfl⟩ : syracuseStep 5828269 = 2185601) B2185601
theorem B5369651 : Blo 1060614 5369651 := bstep (se 1 (by rfl) ⟨4027238, by rfl⟩ : syracuseStep 5369651 = 8054477) B8054477
theorem B2387771 : Blo 1060614 2387771 := bstep (se 1 (by rfl) ⟨1790828, by rfl⟩ : syracuseStep 2387771 = 3581657) B3581657
theorem B2387897 : Blo 1060614 2387897 := bstep (se 2 (by rfl) ⟨895461, by rfl⟩ : syracuseStep 2387897 = 1790923) B1790923
theorem B5828561 : Blo 1060614 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B5369975 : Blo 1060614 5369975 := bstep (se 1 (by rfl) ⟨4027481, by rfl⟩ : syracuseStep 5369975 = 8054963) B8054963
theorem B2388239 : Blo 1060614 2388239 := bstep (se 1 (by rfl) ⟨1791179, by rfl⟩ : syracuseStep 2388239 = 3582359) B3582359
theorem B2388257 : Blo 1060614 2388257 := bstep (se 2 (by rfl) ⟨895596, by rfl⟩ : syracuseStep 2388257 = 1791193) B1791193
theorem B6811937 : Blo 1060614 6811937 := bstep (se 2 (by rfl) ⟨2554476, by rfl⟩ : syracuseStep 6811937 = 5108953) B5108953
theorem B12120353 : Blo 1060614 12120353 := bstep (se 2 (by rfl) ⟨4545132, by rfl⟩ : syracuseStep 12120353 = 9090265) B9090265
theorem B9073043 : Blo 1060614 9073043 := bstep (se 1 (by rfl) ⟨6804782, by rfl⟩ : syracuseStep 9073043 = 13609565) B13609565
theorem B6058583 : Blo 1060614 6058583 := bstep (se 1 (by rfl) ⟨4543937, by rfl⟩ : syracuseStep 6058583 = 9087875) B9087875
theorem B12907127 : Blo 1060614 12907127 := bstep (se 1 (by rfl) ⟨9680345, by rfl⟩ : syracuseStep 12907127 = 19360691) B19360691
theorem B2388599 : Blo 1060614 2388599 := bstep (se 1 (by rfl) ⟨1791449, by rfl⟩ : syracuseStep 2388599 = 3582899) B3582899
theorem B4027117 : Blo 1060614 4027117 := bstep (se 3 (by rfl) ⟨755084, by rfl⟩ : syracuseStep 4027117 = 1510169) B1510169
theorem B2388779 : Blo 1060614 2388779 := bstep (se 1 (by rfl) ⟨1791584, by rfl⟩ : syracuseStep 2388779 = 3583169) B3583169
theorem B8057879 : Blo 1060614 8057879 := bstep (se 1 (by rfl) ⟨6043409, by rfl⟩ : syracuseStep 8057879 = 12086819) B12086819
theorem B4027421 : Blo 1060614 4027421 := bstep (se 3 (by rfl) ⟨755141, by rfl⟩ : syracuseStep 4027421 = 1510283) B1510283
theorem B5370947 : Blo 1060614 5370947 := bstep (se 1 (by rfl) ⟨4028210, by rfl⟩ : syracuseStep 5370947 = 8056421) B8056421
theorem B2389139 : Blo 1060614 2389139 := bstep (se 1 (by rfl) ⟨1791854, by rfl⟩ : syracuseStep 2389139 = 3583709) B3583709
theorem B2389193 : Blo 1060614 2389193 := bstep (se 2 (by rfl) ⟨895947, by rfl⟩ : syracuseStep 2389193 = 1791895) B1791895
theorem B3273929 : Blo 1060614 3273929 := bstep (se 2 (by rfl) ⟨1227723, by rfl⟩ : syracuseStep 3273929 = 2455447) B2455447
theorem B5371271 : Blo 1060614 5371271 := bstep (se 1 (by rfl) ⟨4028453, by rfl⟩ : syracuseStep 5371271 = 8056907) B8056907
theorem B24835513 : Blo 1060614 24835513 := bstep (se 2 (by rfl) ⟨9313317, by rfl⟩ : syracuseStep 24835513 = 18626635) B18626635
theorem B9074105 : Blo 1060614 9074105 := bstep (se 2 (by rfl) ⟨3402789, by rfl⟩ : syracuseStep 9074105 = 6805579) B6805579
theorem B5109277 : Blo 1060614 5109277 := bstep (se 3 (by rfl) ⟨957989, by rfl⟩ : syracuseStep 5109277 = 1915979) B1915979
theorem B3405569 : Blo 1060614 3405569 := bstep (se 2 (by rfl) ⟨1277088, by rfl⟩ : syracuseStep 3405569 = 2554177) B2554177
theorem B8189747 : Blo 1060614 8189747 := bstep (se 1 (by rfl) ⟨6142310, by rfl⟩ : syracuseStep 8189747 = 12284621) B12284621
theorem B2389895 : Blo 1060614 2389895 := bstep (se 1 (by rfl) ⟨1792421, by rfl⟩ : syracuseStep 2389895 = 3584843) B3584843
theorem B19658647 : Blo 1060614 19658647 := bstep (se 1 (by rfl) ⟨14743985, by rfl⟩ : syracuseStep 19658647 = 29487971) B29487971
theorem B2390075 : Blo 1060614 2390075 := bstep (se 1 (by rfl) ⟨1792556, by rfl⟩ : syracuseStep 2390075 = 3585113) B3585113
theorem B2390201 : Blo 1060614 2390201 := bstep (se 2 (by rfl) ⟨896325, by rfl⟩ : syracuseStep 2390201 = 1792651) B1792651
theorem B2685271 : Blo 1060614 2685271 := bstep (se 1 (by rfl) ⟨2013953, by rfl⟩ : syracuseStep 2685271 = 4027907) B4027907
theorem B12089735 : Blo 1060614 12089735 := bstep (se 1 (by rfl) ⟨9067301, by rfl⟩ : syracuseStep 12089735 = 18134603) B18134603
theorem B2390543 : Blo 1060614 2390543 := bstep (se 1 (by rfl) ⟨1792907, by rfl⟩ : syracuseStep 2390543 = 3585815) B3585815
theorem B2390561 : Blo 1060614 2390561 := bstep (se 2 (by rfl) ⟨896460, by rfl⟩ : syracuseStep 2390561 = 1792921) B1792921
theorem B4029047 : Blo 1060614 4029047 := bstep (se 1 (by rfl) ⟨3021785, by rfl⟩ : syracuseStep 4029047 = 6043571) B6043571
theorem B2685575 : Blo 1060614 2685575 := bstep (se 1 (by rfl) ⟨2014181, by rfl⟩ : syracuseStep 2685575 = 4028363) B4028363
theorem B2554553 : Blo 1060614 2554553 := bstep (se 2 (by rfl) ⟨957957, by rfl⟩ : syracuseStep 2554553 = 1915915) B1915915
theorem B2685707 : Blo 1060614 2685707 := bstep (se 1 (by rfl) ⟨2014280, by rfl⟩ : syracuseStep 2685707 = 4028561) B4028561
theorem B6060815 : Blo 1060614 6060815 := bstep (se 1 (by rfl) ⟨4545611, by rfl⟩ : syracuseStep 6060815 = 9091223) B9091223
theorem B2390903 : Blo 1060614 2390903 := bstep (se 1 (by rfl) ⟨1793177, by rfl⟩ : syracuseStep 2390903 = 3586355) B3586355
theorem B6061067 : Blo 1060614 6061067 := bstep (se 1 (by rfl) ⟨4545800, by rfl⟩ : syracuseStep 6061067 = 9091601) B9091601
theorem B2391083 : Blo 1060614 2391083 := bstep (se 1 (by rfl) ⟨1793312, by rfl⟩ : syracuseStep 2391083 = 3586625) B3586625
theorem B12123269 : Blo 1060614 12123269 := bstep (se 4 (by rfl) ⟨1136556, by rfl⟩ : syracuseStep 12123269 = 2273113) B2273113
theorem B1342651 : Blo 1060614 1342651 := bstep (se 1 (by rfl) ⟨1006988, by rfl⟩ : syracuseStep 1342651 = 2013977) B2013977
theorem B2686223 : Blo 1060614 2686223 := bstep (se 1 (by rfl) ⟨2014667, by rfl⟩ : syracuseStep 2686223 = 4029335) B4029335
theorem B11074961 : Blo 1060614 11074961 := bstep (se 2 (by rfl) ⟨4153110, by rfl⟩ : syracuseStep 11074961 = 8306221) B8306221
theorem B2686355 : Blo 1060614 2686355 := bstep (se 1 (by rfl) ⟨2014766, by rfl⟩ : syracuseStep 2686355 = 4029533) B4029533
theorem B2391443 : Blo 1060614 2391443 := bstep (se 1 (by rfl) ⟨1793582, by rfl⟩ : syracuseStep 2391443 = 3587165) B3587165
theorem B2620873 : Blo 1060614 2620873 := bstep (se 2 (by rfl) ⟨982827, by rfl⟩ : syracuseStep 2620873 = 1965655) B1965655
theorem B2391497 : Blo 1060614 2391497 := bstep (se 2 (by rfl) ⟨896811, by rfl⟩ : syracuseStep 2391497 = 1793623) B1793623
theorem B2555407 : Blo 1060614 2555407 := bstep (se 1 (by rfl) ⟨1916555, by rfl⟩ : syracuseStep 2555407 = 3833111) B3833111
theorem B4030019 : Blo 1060614 4030019 := bstep (se 1 (by rfl) ⟨3022514, by rfl⟩ : syracuseStep 4030019 = 6045029) B6045029
theorem B39353957 : Blo 1060614 39353957 := bstep (se 4 (by rfl) ⟨3689433, by rfl⟩ : syracuseStep 39353957 = 7378867) B7378867
theorem B5111585 : Blo 1060614 5111585 := bstep (se 2 (by rfl) ⟨1916844, by rfl⟩ : syracuseStep 5111585 = 3833689) B3833689
theorem B2555707 : Blo 1060614 2555707 := bstep (se 1 (by rfl) ⟨1916780, by rfl⟩ : syracuseStep 2555707 = 3833561) B3833561
theorem B29065229 : Blo 1060614 29065229 := bstep (se 3 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 29065229 = 10899461) B10899461
theorem B2687033 : Blo 1060614 2687033 := bstep (se 2 (by rfl) ⟨1007637, by rfl⟩ : syracuseStep 2687033 = 2015275) B2015275
theorem B1343567 : Blo 1060614 1343567 := bstep (se 1 (by rfl) ⟨1007675, by rfl⟩ : syracuseStep 1343567 = 2015351) B2015351
theorem B8618147 : Blo 1060614 8618147 := bstep (se 1 (by rfl) ⟨6463610, by rfl⟩ : syracuseStep 8618147 = 12927221) B12927221
theorem B2392235 : Blo 1060614 2392235 := bstep (se 1 (by rfl) ⟨1794176, by rfl⟩ : syracuseStep 2392235 = 3588353) B3588353
theorem B6127883 : Blo 1060614 6127883 := bstep (se 1 (by rfl) ⟨4595912, by rfl⟩ : syracuseStep 6127883 = 9191825) B9191825
theorem B5833021 : Blo 1060614 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B4424179 : Blo 1060614 4424179 := bstep (se 1 (by rfl) ⟨3318134, by rfl⟩ : syracuseStep 4424179 = 6636269) B6636269
theorem B9700013 : Blo 1060614 9700013 := bstep (se 3 (by rfl) ⟨1818752, by rfl⟩ : syracuseStep 9700013 = 3637505) B3637505
theorem B2392775 : Blo 1060614 2392775 := bstep (se 1 (by rfl) ⟨1794581, by rfl⟩ : syracuseStep 2392775 = 3589163) B3589163
theorem B5374673 : Blo 1060614 5374673 := bstep (se 2 (by rfl) ⟨2015502, by rfl⟩ : syracuseStep 5374673 = 4031005) B4031005
theorem B2557099 : Blo 1060614 2557099 := bstep (se 1 (by rfl) ⟨1917824, by rfl⟩ : syracuseStep 2557099 = 3835649) B3835649
theorem B6063275 : Blo 1060614 6063275 := bstep (se 1 (by rfl) ⟨4547456, by rfl⟩ : syracuseStep 6063275 = 9094913) B9094913
theorem B1705207 : Blo 1060614 1705207 := bstep (se 1 (by rfl) ⟨1278905, by rfl⟩ : syracuseStep 1705207 = 2557811) B2557811
theorem B6817061 : Blo 1060614 6817061 := bstep (se 4 (by rfl) ⟨639099, by rfl⟩ : syracuseStep 6817061 = 1278199) B1278199
theorem B1344863 : Blo 1060614 1344863 := bstep (se 1 (by rfl) ⟨1008647, by rfl⟩ : syracuseStep 1344863 = 2017295) B2017295
theorem B4031963 : Blo 1060614 4031963 := bstep (se 1 (by rfl) ⟨3023972, by rfl⟩ : syracuseStep 4031963 = 6047945) B6047945
theorem B5604851 : Blo 1060614 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B2393639 : Blo 1060614 2393639 := bstep (se 1 (by rfl) ⟨1795229, by rfl⟩ : syracuseStep 2393639 = 3590459) B3590459
theorem B2393963 : Blo 1060614 2393963 := bstep (se 1 (by rfl) ⟨1795472, by rfl⟩ : syracuseStep 2393963 = 3590945) B3590945
theorem B2394017 : Blo 1060614 2394017 := bstep (se 2 (by rfl) ⟨897756, by rfl⟩ : syracuseStep 2394017 = 1795513) B1795513
theorem B582748121 : Blo 1060614 582748121 := bstep (se 2 (by rfl) ⟨218530545, by rfl⟩ : syracuseStep 582748121 = 437061091) B437061091
theorem B2689271 : Blo 1060614 2689271 := bstep (se 1 (by rfl) ⟨2016953, by rfl⟩ : syracuseStep 2689271 = 4033907) B4033907
theorem B2394359 : Blo 1060614 2394359 := bstep (se 1 (by rfl) ⟨1795769, by rfl⟩ : syracuseStep 2394359 = 3591539) B3591539
theorem B5114123 : Blo 1060614 5114123 := bstep (se 1 (by rfl) ⟨3835592, by rfl⟩ : syracuseStep 5114123 = 7671185) B7671185
theorem B9079127 : Blo 1060614 9079127 := bstep (se 1 (by rfl) ⟨6809345, by rfl⟩ : syracuseStep 9079127 = 13618691) B13618691
theorem B4033223 : Blo 1060614 4033223 := bstep (se 1 (by rfl) ⟨3024917, by rfl⟩ : syracuseStep 4033223 = 6049835) B6049835
theorem B2394953 : Blo 1060614 2394953 := bstep (se 2 (by rfl) ⟨898107, by rfl⟩ : syracuseStep 2394953 = 1796215) B1796215
theorem B3640159 : Blo 1060614 3640159 := bstep (se 1 (by rfl) ⟨2730119, by rfl⟩ : syracuseStep 3640159 = 5460239) B5460239
theorem B1510363 : Blo 1060614 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B5377103 : Blo 1060614 5377103 := bstep (se 1 (by rfl) ⟨4032827, by rfl⟩ : syracuseStep 5377103 = 8065655) B8065655
theorem B6819187 : Blo 1060614 6819187 := bstep (se 1 (by rfl) ⟨5114390, by rfl⟩ : syracuseStep 6819187 = 10228781) B10228781
theorem B4033921 : Blo 1060614 4033921 := bstep (se 2 (by rfl) ⟨1512720, by rfl⟩ : syracuseStep 4033921 = 3025441) B3025441
theorem B1510921 : Blo 1060614 1510921 := bstep (se 2 (by rfl) ⟨566595, by rfl⟩ : syracuseStep 1510921 = 1133191) B1133191
theorem B4034195 : Blo 1060614 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B2690759 : Blo 1060614 2690759 := bstep (se 1 (by rfl) ⟨2018069, by rfl⟩ : syracuseStep 2690759 = 4036139) B4036139
theorem B5377751 : Blo 1060614 5377751 := bstep (se 1 (by rfl) ⟨4033313, by rfl⟩ : syracuseStep 5377751 = 8066627) B8066627
theorem B13602593 : Blo 1060614 13602593 := bstep (se 2 (by rfl) ⟨5100972, by rfl⟩ : syracuseStep 13602593 = 10201945) B10201945
theorem B17207225 : Blo 1060614 17207225 := bstep (se 2 (by rfl) ⟨6452709, by rfl⟩ : syracuseStep 17207225 = 12905419) B12905419
theorem B2658475 : Blo 1060614 2658475 := bstep (se 1 (by rfl) ⟨1993856, by rfl⟩ : syracuseStep 2658475 = 3987713) B3987713
theorem B9081517 : Blo 1060614 9081517 := bstep (se 3 (by rfl) ⟨1702784, by rfl⟩ : syracuseStep 9081517 = 3405569) B3405569
theorem B2691913 : Blo 1060614 2691913 := bstep (se 2 (by rfl) ⟨1009467, by rfl⟩ : syracuseStep 2691913 = 2018935) B2018935
theorem B7771025 : Blo 1060614 7771025 := bstep (se 2 (by rfl) ⟨2914134, by rfl⟩ : syracuseStep 7771025 = 5828269) B5828269
theorem B4035851 : Blo 1060614 4035851 := bstep (se 1 (by rfl) ⟨3026888, by rfl⟩ : syracuseStep 4035851 = 6053777) B6053777
theorem B2299279 : Blo 1060614 2299279 := bstep (se 1 (by rfl) ⟨1724459, by rfl⟩ : syracuseStep 2299279 = 3448919) B3448919
theorem B1513399 : Blo 1060614 1513399 := bstep (se 1 (by rfl) ⟨1135049, by rfl⟩ : syracuseStep 1513399 = 2270099) B2270099
theorem B2693047 : Blo 1060614 2693047 := bstep (se 1 (by rfl) ⟨2019785, by rfl⟩ : syracuseStep 2693047 = 4039571) B4039571
theorem B15341669 : Blo 1060614 15341669 := bstep (se 4 (by rfl) ⟨1438281, by rfl⟩ : syracuseStep 15341669 = 2876563) B2876563
theorem B14522759 : Blo 1060614 14522759 := bstep (se 1 (by rfl) ⟨10892069, by rfl⟩ : syracuseStep 14522759 = 21784139) B21784139
theorem B5380667 : Blo 1060614 5380667 := bstep (se 1 (by rfl) ⟨4035500, by rfl⟩ : syracuseStep 5380667 = 8071001) B8071001
theorem B4037309 : Blo 1060614 4037309 := bstep (se 3 (by rfl) ⟨756995, by rfl⟩ : syracuseStep 4037309 = 1513991) B1513991
theorem B5381315 : Blo 1060614 5381315 := bstep (se 1 (by rfl) ⟨4035986, by rfl⟩ : syracuseStep 5381315 = 8071973) B8071973
theorem B1514857 : Blo 1060614 1514857 := bstep (se 2 (by rfl) ⟨568071, by rfl⟩ : syracuseStep 1514857 = 1136143) B1136143
theorem B2694505 : Blo 1060614 2694505 := bstep (se 2 (by rfl) ⟨1010439, by rfl⟩ : syracuseStep 2694505 = 2020879) B2020879
theorem B8068571 : Blo 1060614 8068571 := bstep (se 1 (by rfl) ⟨6051428, by rfl⟩ : syracuseStep 8068571 = 12102857) B12102857
theorem B6888947 : Blo 1060614 6888947 := bstep (se 1 (by rfl) ⟨5166710, by rfl⟩ : syracuseStep 6888947 = 10333421) B10333421
theorem B2694779 : Blo 1060614 2694779 := bstep (se 1 (by rfl) ⟨2021084, by rfl⟩ : syracuseStep 2694779 = 4042169) B4042169
theorem B9838219 : Blo 1060614 9838219 := bstep (se 1 (by rfl) ⟨7378664, by rfl⟩ : syracuseStep 9838219 = 14757329) B14757329
theorem B3022525 : Blo 1060614 3022525 := bstep (se 3 (by rfl) ⟨566723, by rfl⟩ : syracuseStep 3022525 = 1133447) B1133447
theorem B3579767 : Blo 1060614 3579767 := bstep (se 1 (by rfl) ⟨2684825, by rfl⟩ : syracuseStep 3579767 = 5369651) B5369651
theorem B3022753 : Blo 1060614 3022753 := bstep (se 2 (by rfl) ⟨1133532, by rfl⟩ : syracuseStep 3022753 = 2267065) B2267065
theorem B8069057 : Blo 1060614 8069057 := bstep (se 2 (by rfl) ⟨3025896, by rfl⟩ : syracuseStep 8069057 = 6051793) B6051793
theorem B3579983 : Blo 1060614 3579983 := bstep (se 1 (by rfl) ⟨2684987, by rfl⟩ : syracuseStep 3579983 = 5369975) B5369975
theorem B3023095 : Blo 1060614 3023095 := bstep (se 1 (by rfl) ⟨2267321, by rfl⟩ : syracuseStep 3023095 = 4534643) B4534643
theorem B4039055 : Blo 1060614 4039055 := bstep (se 1 (by rfl) ⟨3029291, by rfl⟩ : syracuseStep 4039055 = 6058583) B6058583
theorem B3580361 : Blo 1060614 3580361 := bstep (se 2 (by rfl) ⟨1342635, by rfl⟩ : syracuseStep 3580361 = 2685271) B2685271
theorem B3023369 : Blo 1060614 3023369 := bstep (se 2 (by rfl) ⟨1133763, by rfl⟩ : syracuseStep 3023369 = 2267527) B2267527
theorem B4203197 : Blo 1060614 4203197 := bstep (se 3 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 4203197 = 1576199) B1576199
theorem B3580631 : Blo 1060614 3580631 := bstep (se 1 (by rfl) ⟨2685473, by rfl⟩ : syracuseStep 3580631 = 5370947) B5370947
theorem B3580847 : Blo 1060614 3580847 := bstep (se 1 (by rfl) ⟨2685635, by rfl⟩ : syracuseStep 3580847 = 5371271) B5371271
theorem B3024029 : Blo 1060614 3024029 := bstep (se 3 (by rfl) ⟨567005, by rfl⟩ : syracuseStep 3024029 = 1134011) B1134011
theorem B8070515 : Blo 1060614 8070515 := bstep (se 1 (by rfl) ⟨6052886, by rfl⟩ : syracuseStep 8070515 = 12105773) B12105773
theorem B3024371 : Blo 1060614 3024371 := bstep (se 1 (by rfl) ⟨2268278, by rfl⟩ : syracuseStep 3024371 = 4536557) B4536557
theorem B4040225 : Blo 1060614 4040225 := bstep (se 2 (by rfl) ⟨1515084, by rfl⟩ : syracuseStep 4040225 = 3030169) B3030169
theorem B4531859 : Blo 1060614 4531859 := bstep (se 1 (by rfl) ⟨3398894, by rfl⟩ : syracuseStep 4531859 = 6797789) B6797789
theorem B4040543 : Blo 1060614 4040543 := bstep (se 1 (by rfl) ⟨3030407, by rfl⟩ : syracuseStep 4040543 = 6060815) B6060815
theorem B2041787 : Blo 1060614 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B3024827 : Blo 1060614 3024827 := bstep (se 1 (by rfl) ⟨2268620, by rfl⟩ : syracuseStep 3024827 = 4537241) B4537241
theorem B4040711 : Blo 1060614 4040711 := bstep (se 1 (by rfl) ⟨3030533, by rfl⟩ : syracuseStep 4040711 = 6061067) B6061067
theorem B7383307 : Blo 1060614 7383307 := bstep (se 1 (by rfl) ⟨5537480, by rfl⟩ : syracuseStep 7383307 = 11074961) B11074961
theorem B4041197 : Blo 1060614 4041197 := bstep (se 3 (by rfl) ⟨757724, by rfl⟩ : syracuseStep 4041197 = 1515449) B1515449
theorem B4041515 : Blo 1060614 4041515 := bstep (se 1 (by rfl) ⟨3031136, by rfl⟩ : syracuseStep 4041515 = 6062273) B6062273
theorem B6040655 : Blo 1060614 6040655 := bstep (se 1 (by rfl) ⟨4530491, by rfl⟩ : syracuseStep 6040655 = 9060983) B9060983
theorem B3681395 : Blo 1060614 3681395 := bstep (se 1 (by rfl) ⟨2761046, by rfl⟩ : syracuseStep 3681395 = 5522093) B5522093
theorem B3583223 : Blo 1060614 3583223 := bstep (se 1 (by rfl) ⟨2687417, by rfl⟩ : syracuseStep 3583223 = 5374835) B5374835
theorem B3583547 : Blo 1060614 3583547 := bstep (se 1 (by rfl) ⟨2687660, by rfl⟩ : syracuseStep 3583547 = 5375321) B5375321
theorem B4533857 : Blo 1060614 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B5385851 : Blo 1060614 5385851 := bstep (se 1 (by rfl) ⟨4039388, by rfl⟩ : syracuseStep 5385851 = 8078777) B8078777
theorem B1912519 : Blo 1060614 1912519 := bstep (se 1 (by rfl) ⟨1434389, by rfl⟩ : syracuseStep 1912519 = 2868779) B2868779
theorem B1060647 : Blo 1060614 1060647 := bstep (se 1 (by rfl) ⟨795485, by rfl⟩ : syracuseStep 1060647 = 1590971) B1590971
theorem B3583817 : Blo 1060614 3583817 := bstep (se 2 (by rfl) ⟨1343931, by rfl⟩ : syracuseStep 3583817 = 2687863) B2687863
theorem B1060687 : Blo 1060614 1060687 := bstep (se 1 (by rfl) ⟨795515, by rfl⟩ : syracuseStep 1060687 = 1591031) B1591031
theorem B1060703 : Blo 1060614 1060703 := bstep (se 1 (by rfl) ⟨795527, by rfl⟩ : syracuseStep 1060703 = 1591055) B1591055
theorem B1060731 : Blo 1060614 1060731 := bstep (se 1 (by rfl) ⟨795548, by rfl⟩ : syracuseStep 1060731 = 1591097) B1591097
theorem B1060783 : Blo 1060614 1060783 := bstep (se 1 (by rfl) ⟨795587, by rfl⟩ : syracuseStep 1060783 = 1591175) B1591175
theorem B1060807 : Blo 1060614 1060807 := bstep (se 1 (by rfl) ⟨795605, by rfl⟩ : syracuseStep 1060807 = 1591211) B1591211
theorem B1060827 : Blo 1060614 1060827 := bstep (se 1 (by rfl) ⟨795620, by rfl⟩ : syracuseStep 1060827 = 1591241) B1591241
theorem B1060903 : Blo 1060614 1060903 := bstep (se 1 (by rfl) ⟨795677, by rfl⟩ : syracuseStep 1060903 = 1591355) B1591355
theorem B1060943 : Blo 1060614 1060943 := bstep (se 1 (by rfl) ⟨795707, by rfl⟩ : syracuseStep 1060943 = 1591415) B1591415
theorem B1060959 : Blo 1060614 1060959 := bstep (se 1 (by rfl) ⟨795719, by rfl⟩ : syracuseStep 1060959 = 1591439) B1591439
theorem B1060987 : Blo 1060614 1060987 := bstep (se 1 (by rfl) ⟨795740, by rfl⟩ : syracuseStep 1060987 = 1591481) B1591481
theorem B1061039 : Blo 1060614 1061039 := bstep (se 1 (by rfl) ⟨795779, by rfl⟩ : syracuseStep 1061039 = 1591559) B1591559
theorem B1061063 : Blo 1060614 1061063 := bstep (se 1 (by rfl) ⟨795797, by rfl⟩ : syracuseStep 1061063 = 1591595) B1591595
theorem B1061083 : Blo 1060614 1061083 := bstep (se 1 (by rfl) ⟨795812, by rfl⟩ : syracuseStep 1061083 = 1591625) B1591625
theorem B1061159 : Blo 1060614 1061159 := bstep (se 1 (by rfl) ⟨795869, by rfl⟩ : syracuseStep 1061159 = 1591739) B1591739
theorem B34419005 : Blo 1060614 34419005 := bstep (se 3 (by rfl) ⟨6453563, by rfl⟩ : syracuseStep 34419005 = 12907127) B12907127
theorem B1061199 : Blo 1060614 1061199 := bstep (se 1 (by rfl) ⟨795899, by rfl⟩ : syracuseStep 1061199 = 1591799) B1591799
theorem B1061215 : Blo 1060614 1061215 := bstep (se 1 (by rfl) ⟨795911, by rfl⟩ : syracuseStep 1061215 = 1591823) B1591823
theorem B1061243 : Blo 1060614 1061243 := bstep (se 1 (by rfl) ⟨795932, by rfl⟩ : syracuseStep 1061243 = 1591865) B1591865
theorem B1061295 : Blo 1060614 1061295 := bstep (se 1 (by rfl) ⟨795971, by rfl⟩ : syracuseStep 1061295 = 1591943) B1591943
theorem B1061319 : Blo 1060614 1061319 := bstep (se 1 (by rfl) ⟨795989, by rfl⟩ : syracuseStep 1061319 = 1591979) B1591979
theorem B1061339 : Blo 1060614 1061339 := bstep (se 1 (by rfl) ⟨796004, by rfl⟩ : syracuseStep 1061339 = 1592009) B1592009
theorem B1061415 : Blo 1060614 1061415 := bstep (se 1 (by rfl) ⟨796061, by rfl⟩ : syracuseStep 1061415 = 1592123) B1592123
theorem B1061455 : Blo 1060614 1061455 := bstep (se 1 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 1061455 = 1592183) B1592183
theorem B1061471 : Blo 1060614 1061471 := bstep (se 1 (by rfl) ⟨796103, by rfl⟩ : syracuseStep 1061471 = 1592207) B1592207
theorem B1061499 : Blo 1060614 1061499 := bstep (se 1 (by rfl) ⟨796124, by rfl⟩ : syracuseStep 1061499 = 1592249) B1592249
theorem B1061551 : Blo 1060614 1061551 := bstep (se 1 (by rfl) ⟨796163, by rfl⟩ : syracuseStep 1061551 = 1592327) B1592327
theorem B6468281 : Blo 1060614 6468281 := bstep (se 2 (by rfl) ⟨2425605, by rfl⟩ : syracuseStep 6468281 = 4851211) B4851211
theorem B1061575 : Blo 1060614 1061575 := bstep (se 1 (by rfl) ⟨796181, by rfl⟩ : syracuseStep 1061575 = 1592363) B1592363
theorem B1061595 : Blo 1060614 1061595 := bstep (se 1 (by rfl) ⟨796196, by rfl⟩ : syracuseStep 1061595 = 1592393) B1592393
theorem B1061671 : Blo 1060614 1061671 := bstep (se 1 (by rfl) ⟨796253, by rfl⟩ : syracuseStep 1061671 = 1592507) B1592507
theorem B1061711 : Blo 1060614 1061711 := bstep (se 1 (by rfl) ⟨796283, by rfl⟩ : syracuseStep 1061711 = 1592567) B1592567
theorem B1061727 : Blo 1060614 1061727 := bstep (se 1 (by rfl) ⟨796295, by rfl⟩ : syracuseStep 1061727 = 1592591) B1592591
theorem B1061755 : Blo 1060614 1061755 := bstep (se 1 (by rfl) ⟨796316, by rfl⟩ : syracuseStep 1061755 = 1592633) B1592633
theorem B1061807 : Blo 1060614 1061807 := bstep (se 1 (by rfl) ⟨796355, by rfl⟩ : syracuseStep 1061807 = 1592711) B1592711
theorem B3584951 : Blo 1060614 3584951 := bstep (se 1 (by rfl) ⟨2688713, by rfl⟩ : syracuseStep 3584951 = 5377427) B5377427
theorem B1061831 : Blo 1060614 1061831 := bstep (se 1 (by rfl) ⟨796373, by rfl⟩ : syracuseStep 1061831 = 1592747) B1592747
theorem B1061851 : Blo 1060614 1061851 := bstep (se 1 (by rfl) ⟨796388, by rfl⟩ : syracuseStep 1061851 = 1592777) B1592777
theorem B1455067 : Blo 1060614 1455067 := bstep (se 1 (by rfl) ⟨1091300, by rfl⟩ : syracuseStep 1455067 = 2182601) B2182601
theorem B1061927 : Blo 1060614 1061927 := bstep (se 1 (by rfl) ⟨796445, by rfl⟩ : syracuseStep 1061927 = 1592891) B1592891
theorem B7877681 : Blo 1060614 7877681 := bstep (se 2 (by rfl) ⟨2954130, by rfl⟩ : syracuseStep 7877681 = 5908261) B5908261
theorem B1061967 : Blo 1060614 1061967 := bstep (se 1 (by rfl) ⟨796475, by rfl⟩ : syracuseStep 1061967 = 1592951) B1592951
theorem B1061983 : Blo 1060614 1061983 := bstep (se 1 (by rfl) ⟨796487, by rfl⟩ : syracuseStep 1061983 = 1592975) B1592975
theorem B1062011 : Blo 1060614 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B1062063 : Blo 1060614 1062063 := bstep (se 1 (by rfl) ⟨796547, by rfl⟩ : syracuseStep 1062063 = 1593095) B1593095
theorem B1062087 : Blo 1060614 1062087 := bstep (se 1 (by rfl) ⟨796565, by rfl⟩ : syracuseStep 1062087 = 1593131) B1593131
theorem B1062107 : Blo 1060614 1062107 := bstep (se 1 (by rfl) ⟨796580, by rfl⟩ : syracuseStep 1062107 = 1593161) B1593161
theorem B1062183 : Blo 1060614 1062183 := bstep (se 1 (by rfl) ⟨796637, by rfl⟩ : syracuseStep 1062183 = 1593275) B1593275
theorem B1062223 : Blo 1060614 1062223 := bstep (se 1 (by rfl) ⟨796667, by rfl⟩ : syracuseStep 1062223 = 1593335) B1593335
theorem B1062239 : Blo 1060614 1062239 := bstep (se 1 (by rfl) ⟨796679, by rfl⟩ : syracuseStep 1062239 = 1593359) B1593359
theorem B1062267 : Blo 1060614 1062267 := bstep (se 1 (by rfl) ⟨796700, by rfl⟩ : syracuseStep 1062267 = 1593401) B1593401
theorem B6043045 : Blo 1060614 6043045 := bstep (se 4 (by rfl) ⟨566535, by rfl⟩ : syracuseStep 6043045 = 1133071) B1133071
theorem B1062319 : Blo 1060614 1062319 := bstep (se 1 (by rfl) ⟨796739, by rfl⟩ : syracuseStep 1062319 = 1593479) B1593479
theorem B1062343 : Blo 1060614 1062343 := bstep (se 1 (by rfl) ⟨796757, by rfl⟩ : syracuseStep 1062343 = 1593515) B1593515
theorem B1062363 : Blo 1060614 1062363 := bstep (se 1 (by rfl) ⟨796772, by rfl⟩ : syracuseStep 1062363 = 1593545) B1593545
theorem B3585545 : Blo 1060614 3585545 := bstep (se 2 (by rfl) ⟨1344579, by rfl⟩ : syracuseStep 3585545 = 2689159) B2689159
theorem B1062439 : Blo 1060614 1062439 := bstep (se 1 (by rfl) ⟨796829, by rfl⟩ : syracuseStep 1062439 = 1593659) B1593659
theorem B1062479 : Blo 1060614 1062479 := bstep (se 1 (by rfl) ⟨796859, by rfl⟩ : syracuseStep 1062479 = 1593719) B1593719
theorem B1062495 : Blo 1060614 1062495 := bstep (se 1 (by rfl) ⟨796871, by rfl⟩ : syracuseStep 1062495 = 1593743) B1593743
theorem B1062523 : Blo 1060614 1062523 := bstep (se 1 (by rfl) ⟨796892, by rfl⟩ : syracuseStep 1062523 = 1593785) B1593785
theorem B1062575 : Blo 1060614 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B1062599 : Blo 1060614 1062599 := bstep (se 1 (by rfl) ⟨796949, by rfl⟩ : syracuseStep 1062599 = 1593899) B1593899
theorem B1062619 : Blo 1060614 1062619 := bstep (se 1 (by rfl) ⟨796964, by rfl⟩ : syracuseStep 1062619 = 1593929) B1593929
theorem B11646713 : Blo 1060614 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B1062695 : Blo 1060614 1062695 := bstep (se 1 (by rfl) ⟨797021, by rfl⟩ : syracuseStep 1062695 = 1594043) B1594043
theorem B1062735 : Blo 1060614 1062735 := bstep (se 1 (by rfl) ⟨797051, by rfl⟩ : syracuseStep 1062735 = 1594103) B1594103
theorem B1062751 : Blo 1060614 1062751 := bstep (se 1 (by rfl) ⟨797063, by rfl⟩ : syracuseStep 1062751 = 1594127) B1594127
theorem B1062779 : Blo 1060614 1062779 := bstep (se 1 (by rfl) ⟨797084, by rfl⟩ : syracuseStep 1062779 = 1594169) B1594169
theorem B1062831 : Blo 1060614 1062831 := bstep (se 1 (by rfl) ⟨797123, by rfl⟩ : syracuseStep 1062831 = 1594247) B1594247
theorem B1062855 : Blo 1060614 1062855 := bstep (se 1 (by rfl) ⟨797141, by rfl⟩ : syracuseStep 1062855 = 1594283) B1594283
theorem B1062875 : Blo 1060614 1062875 := bstep (se 1 (by rfl) ⟨797156, by rfl⟩ : syracuseStep 1062875 = 1594313) B1594313
theorem B1062951 : Blo 1060614 1062951 := bstep (se 1 (by rfl) ⟨797213, by rfl⟩ : syracuseStep 1062951 = 1594427) B1594427
theorem B1062991 : Blo 1060614 1062991 := bstep (se 1 (by rfl) ⟨797243, by rfl⟩ : syracuseStep 1062991 = 1594487) B1594487
theorem B1063007 : Blo 1060614 1063007 := bstep (se 1 (by rfl) ⟨797255, by rfl⟩ : syracuseStep 1063007 = 1594511) B1594511
theorem B1063035 : Blo 1060614 1063035 := bstep (se 1 (by rfl) ⟨797276, by rfl⟩ : syracuseStep 1063035 = 1594553) B1594553
theorem B1063087 : Blo 1060614 1063087 := bstep (se 1 (by rfl) ⟨797315, by rfl⟩ : syracuseStep 1063087 = 1594631) B1594631
theorem B1063111 : Blo 1060614 1063111 := bstep (se 1 (by rfl) ⟨797333, by rfl⟩ : syracuseStep 1063111 = 1594667) B1594667
theorem B1063131 : Blo 1060614 1063131 := bstep (se 1 (by rfl) ⟨797348, by rfl⟩ : syracuseStep 1063131 = 1594697) B1594697
theorem B1063207 : Blo 1060614 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B5388605 : Blo 1060614 5388605 := bstep (se 3 (by rfl) ⟨1010363, by rfl⟩ : syracuseStep 5388605 = 2020727) B2020727
theorem B1063247 : Blo 1060614 1063247 := bstep (se 1 (by rfl) ⟨797435, by rfl⟩ : syracuseStep 1063247 = 1594871) B1594871
theorem B1063263 : Blo 1060614 1063263 := bstep (se 1 (by rfl) ⟨797447, by rfl⟩ : syracuseStep 1063263 = 1594895) B1594895
theorem B3586409 : Blo 1060614 3586409 := bstep (se 2 (by rfl) ⟨1344903, by rfl⟩ : syracuseStep 3586409 = 2689807) B2689807
theorem B1063291 : Blo 1060614 1063291 := bstep (se 1 (by rfl) ⟨797468, by rfl⟩ : syracuseStep 1063291 = 1594937) B1594937
theorem B17250691 : Blo 1060614 17250691 := bstep (se 1 (by rfl) ⟨12938018, by rfl⟩ : syracuseStep 17250691 = 25876037) B25876037
theorem B1063343 : Blo 1060614 1063343 := bstep (se 1 (by rfl) ⟨797507, by rfl⟩ : syracuseStep 1063343 = 1595015) B1595015
theorem B1063367 : Blo 1060614 1063367 := bstep (se 1 (by rfl) ⟨797525, by rfl⟩ : syracuseStep 1063367 = 1595051) B1595051
theorem B1063387 : Blo 1060614 1063387 := bstep (se 1 (by rfl) ⟨797540, by rfl⟩ : syracuseStep 1063387 = 1595081) B1595081
theorem B1063463 : Blo 1060614 1063463 := bstep (se 1 (by rfl) ⟨797597, by rfl⟩ : syracuseStep 1063463 = 1595195) B1595195
theorem B1063503 : Blo 1060614 1063503 := bstep (se 1 (by rfl) ⟨797627, by rfl⟩ : syracuseStep 1063503 = 1595255) B1595255
theorem B1063519 : Blo 1060614 1063519 := bstep (se 1 (by rfl) ⟨797639, by rfl⟩ : syracuseStep 1063519 = 1595279) B1595279
theorem B3226235 : Blo 1060614 3226235 := bstep (se 1 (by rfl) ⟨2419676, by rfl⟩ : syracuseStep 3226235 = 4839353) B4839353
theorem B1194619 : Blo 1060614 1194619 := bstep (se 1 (by rfl) ⟨895964, by rfl⟩ : syracuseStep 1194619 = 1791929) B1791929
theorem B1063547 : Blo 1060614 1063547 := bstep (se 1 (by rfl) ⟨797660, by rfl⟩ : syracuseStep 1063547 = 1595321) B1595321
theorem B1063599 : Blo 1060614 1063599 := bstep (se 1 (by rfl) ⟨797699, by rfl⟩ : syracuseStep 1063599 = 1595399) B1595399
theorem B27605681 : Blo 1060614 27605681 := bstep (se 2 (by rfl) ⟨10352130, by rfl⟩ : syracuseStep 27605681 = 20704261) B20704261
theorem B1063623 : Blo 1060614 1063623 := bstep (se 1 (by rfl) ⟨797717, by rfl⟩ : syracuseStep 1063623 = 1595435) B1595435
theorem B1063643 : Blo 1060614 1063643 := bstep (se 1 (by rfl) ⟨797732, by rfl⟩ : syracuseStep 1063643 = 1595465) B1595465
theorem B2046713 : Blo 1060614 2046713 := bstep (se 2 (by rfl) ⟨767517, by rfl⟩ : syracuseStep 2046713 = 1535035) B1535035
theorem B1063719 : Blo 1060614 1063719 := bstep (se 1 (by rfl) ⟨797789, by rfl⟩ : syracuseStep 1063719 = 1595579) B1595579
theorem B1063759 : Blo 1060614 1063759 := bstep (se 1 (by rfl) ⟨797819, by rfl⟩ : syracuseStep 1063759 = 1595639) B1595639
theorem B1063775 : Blo 1060614 1063775 := bstep (se 1 (by rfl) ⟨797831, by rfl⟩ : syracuseStep 1063775 = 1595663) B1595663
theorem B1063803 : Blo 1060614 1063803 := bstep (se 1 (by rfl) ⟨797852, by rfl⟩ : syracuseStep 1063803 = 1595705) B1595705
theorem B1063855 : Blo 1060614 1063855 := bstep (se 1 (by rfl) ⟨797891, by rfl⟩ : syracuseStep 1063855 = 1595783) B1595783
theorem B3587003 : Blo 1060614 3587003 := bstep (se 1 (by rfl) ⟨2690252, by rfl⟩ : syracuseStep 3587003 = 5380505) B5380505
theorem B1063879 : Blo 1060614 1063879 := bstep (se 1 (by rfl) ⟨797909, by rfl⟩ : syracuseStep 1063879 = 1595819) B1595819
theorem B1063899 : Blo 1060614 1063899 := bstep (se 1 (by rfl) ⟨797924, by rfl⟩ : syracuseStep 1063899 = 1595849) B1595849
theorem B1063975 : Blo 1060614 1063975 := bstep (se 1 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 1063975 = 1595963) B1595963
theorem B1195087 : Blo 1060614 1195087 := bstep (se 1 (by rfl) ⟨896315, by rfl⟩ : syracuseStep 1195087 = 1792631) B1792631
theorem B1064015 : Blo 1060614 1064015 := bstep (se 1 (by rfl) ⟨798011, by rfl⟩ : syracuseStep 1064015 = 1596023) B1596023
theorem B1064031 : Blo 1060614 1064031 := bstep (se 1 (by rfl) ⟨798023, by rfl⟩ : syracuseStep 1064031 = 1596047) B1596047
theorem B1064059 : Blo 1060614 1064059 := bstep (se 1 (by rfl) ⟨798044, by rfl⟩ : syracuseStep 1064059 = 1596089) B1596089
theorem B2014379 : Blo 1060614 2014379 := bstep (se 1 (by rfl) ⟨1510784, by rfl⟩ : syracuseStep 2014379 = 3021569) B3021569
theorem B1064111 : Blo 1060614 1064111 := bstep (se 1 (by rfl) ⟨798083, by rfl⟩ : syracuseStep 1064111 = 1596167) B1596167
theorem B1064135 : Blo 1060614 1064135 := bstep (se 1 (by rfl) ⟨798101, by rfl⟩ : syracuseStep 1064135 = 1596203) B1596203
theorem B1064155 : Blo 1060614 1064155 := bstep (se 1 (by rfl) ⟨798116, by rfl⟩ : syracuseStep 1064155 = 1596233) B1596233
theorem B1064231 : Blo 1060614 1064231 := bstep (se 1 (by rfl) ⟨798173, by rfl⟩ : syracuseStep 1064231 = 1596347) B1596347
theorem B1064271 : Blo 1060614 1064271 := bstep (se 1 (by rfl) ⟨798203, by rfl⟩ : syracuseStep 1064271 = 1596407) B1596407
theorem B1064287 : Blo 1060614 1064287 := bstep (se 1 (by rfl) ⟨798215, by rfl⟩ : syracuseStep 1064287 = 1596431) B1596431
theorem B1064315 : Blo 1060614 1064315 := bstep (se 1 (by rfl) ⟨798236, by rfl⟩ : syracuseStep 1064315 = 1596473) B1596473
theorem B2014607 : Blo 1060614 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B1064367 : Blo 1060614 1064367 := bstep (se 1 (by rfl) ⟨798275, by rfl⟩ : syracuseStep 1064367 = 1596551) B1596551
theorem B1064391 : Blo 1060614 1064391 := bstep (se 1 (by rfl) ⟨798293, by rfl⟩ : syracuseStep 1064391 = 1596587) B1596587
theorem B1195483 : Blo 1060614 1195483 := bstep (se 1 (by rfl) ⟨896612, by rfl⟩ : syracuseStep 1195483 = 1793225) B1793225
theorem B1064411 : Blo 1060614 1064411 := bstep (se 1 (by rfl) ⟨798308, by rfl⟩ : syracuseStep 1064411 = 1596617) B1596617
theorem B1064487 : Blo 1060614 1064487 := bstep (se 1 (by rfl) ⟨798365, by rfl⟩ : syracuseStep 1064487 = 1596731) B1596731
theorem B1064527 : Blo 1060614 1064527 := bstep (se 1 (by rfl) ⟨798395, by rfl⟩ : syracuseStep 1064527 = 1596791) B1596791
theorem B1064543 : Blo 1060614 1064543 := bstep (se 1 (by rfl) ⟨798407, by rfl⟩ : syracuseStep 1064543 = 1596815) B1596815
theorem B1064571 : Blo 1060614 1064571 := bstep (se 1 (by rfl) ⟨798428, by rfl⟩ : syracuseStep 1064571 = 1596857) B1596857
theorem B13811471 : Blo 1060614 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B4538231 : Blo 1060614 4538231 := bstep (se 1 (by rfl) ⟨3403673, by rfl⟩ : syracuseStep 4538231 = 6807347) B6807347
theorem B9092999 : Blo 1060614 9092999 := bstep (se 1 (by rfl) ⟨6819749, by rfl⟩ : syracuseStep 9092999 = 13639499) B13639499
theorem B1195951 : Blo 1060614 1195951 := bstep (se 1 (by rfl) ⟨896963, by rfl⟩ : syracuseStep 1195951 = 1793927) B1793927
theorem B8077319 : Blo 1060614 8077319 := bstep (se 1 (by rfl) ⟨6057989, by rfl⟩ : syracuseStep 8077319 = 12115979) B12115979
theorem B58245155 : Blo 1060614 58245155 := bstep (se 1 (by rfl) ⟨43683866, by rfl⟩ : syracuseStep 58245155 = 87367733) B87367733
theorem B6471737 : Blo 1060614 6471737 := bstep (se 2 (by rfl) ⟨2426901, by rfl⟩ : syracuseStep 6471737 = 4853803) B4853803
theorem B1196383 : Blo 1060614 1196383 := bstep (se 1 (by rfl) ⟨897287, by rfl⟩ : syracuseStep 1196383 = 1794575) B1794575
theorem B1818985 : Blo 1060614 1818985 := bstep (se 2 (by rfl) ⟨682119, by rfl⟩ : syracuseStep 1818985 = 1364239) B1364239
theorem B8077805 : Blo 1060614 8077805 := bstep (se 3 (by rfl) ⟨1514588, by rfl⟩ : syracuseStep 8077805 = 3029177) B3029177
theorem B2867699 : Blo 1060614 2867699 := bstep (se 1 (by rfl) ⟨2150774, by rfl⟩ : syracuseStep 2867699 = 4301549) B4301549
theorem B2015867 : Blo 1060614 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B3588731 : Blo 1060614 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B1196743 : Blo 1060614 1196743 := bstep (se 1 (by rfl) ⟨897557, by rfl⟩ : syracuseStep 1196743 = 1795115) B1795115
theorem B3588893 : Blo 1060614 3588893 := bstep (se 3 (by rfl) ⟨672917, by rfl⟩ : syracuseStep 3588893 = 1345835) B1345835
theorem B6800273 : Blo 1060614 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B3687443 : Blo 1060614 3687443 := bstep (se 1 (by rfl) ⟨2765582, by rfl⟩ : syracuseStep 3687443 = 5531165) B5531165
theorem B2016353 : Blo 1060614 2016353 := bstep (se 2 (by rfl) ⟨756132, by rfl⟩ : syracuseStep 2016353 = 1512265) B1512265
theorem B9684139 : Blo 1060614 9684139 := bstep (se 1 (by rfl) ⟨7263104, by rfl⟩ : syracuseStep 9684139 = 14526209) B14526209
theorem B2016505 : Blo 1060614 2016505 := bstep (se 2 (by rfl) ⟨756189, by rfl⟩ : syracuseStep 2016505 = 1512379) B1512379
theorem B3589595 : Blo 1060614 3589595 := bstep (se 1 (by rfl) ⟨2692196, by rfl⟩ : syracuseStep 3589595 = 5384393) B5384393
theorem B4310567 : Blo 1060614 4310567 := bstep (se 1 (by rfl) ⟨3232925, by rfl⟩ : syracuseStep 4310567 = 6465851) B6465851
theorem B1197607 : Blo 1060614 1197607 := bstep (se 1 (by rfl) ⟨898205, by rfl⟩ : syracuseStep 1197607 = 1796411) B1796411
theorem B1590983 : Blo 1060614 1590983 := bstep (se 1 (by rfl) ⟨1193237, by rfl⟩ : syracuseStep 1590983 = 2386475) B2386475
theorem B1591145 : Blo 1060614 1591145 := bstep (se 2 (by rfl) ⟨596679, by rfl⟩ : syracuseStep 1591145 = 1193359) B1193359
theorem B33114017 : Blo 1060614 33114017 := bstep (se 2 (by rfl) ⟨12417756, by rfl⟩ : syracuseStep 33114017 = 24835513) B24835513
theorem B1591223 : Blo 1060614 1591223 := bstep (se 1 (by rfl) ⟨1193417, by rfl⟩ : syracuseStep 1591223 = 2386835) B2386835
theorem B7653305 : Blo 1060614 7653305 := bstep (se 2 (by rfl) ⟨2869989, by rfl⟩ : syracuseStep 7653305 = 5739979) B5739979
theorem B1591259 : Blo 1060614 1591259 := bstep (se 1 (by rfl) ⟨1193444, by rfl⟩ : syracuseStep 1591259 = 2386889) B2386889
theorem B3590297 : Blo 1060614 3590297 := bstep (se 2 (by rfl) ⟨1346361, by rfl⟩ : syracuseStep 3590297 = 2692723) B2692723
theorem B8079749 : Blo 1060614 8079749 := bstep (se 4 (by rfl) ⟨757476, by rfl⟩ : syracuseStep 8079749 = 1514953) B1514953
theorem B1591727 : Blo 1060614 1591727 := bstep (se 1 (by rfl) ⟨1193795, by rfl⟩ : syracuseStep 1591727 = 2387591) B2387591
theorem B29477297 : Blo 1060614 29477297 := bstep (se 2 (by rfl) ⟨11053986, by rfl⟩ : syracuseStep 29477297 = 22107973) B22107973
theorem B1591817 : Blo 1060614 1591817 := bstep (se 2 (by rfl) ⟨596931, by rfl⟩ : syracuseStep 1591817 = 1193863) B1193863
theorem B2017811 : Blo 1060614 2017811 := bstep (se 1 (by rfl) ⟨1513358, by rfl⟩ : syracuseStep 2017811 = 3026717) B3026717
theorem B1591847 : Blo 1060614 1591847 := bstep (se 1 (by rfl) ⟨1193885, by rfl⟩ : syracuseStep 1591847 = 2387771) B2387771
theorem B1591931 : Blo 1060614 1591931 := bstep (se 1 (by rfl) ⟨1193948, by rfl⟩ : syracuseStep 1591931 = 2387897) B2387897
theorem B3066491 : Blo 1060614 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B3885707 : Blo 1060614 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B2017963 : Blo 1060614 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B41339593 : Blo 1060614 41339593 := bstep (se 2 (by rfl) ⟨15502347, by rfl⟩ : syracuseStep 41339593 = 31004695) B31004695
theorem B1592057 : Blo 1060614 1592057 := bstep (se 2 (by rfl) ⟨597021, by rfl⟩ : syracuseStep 1592057 = 1194043) B1194043
theorem B1592159 : Blo 1060614 1592159 := bstep (se 1 (by rfl) ⟨1194119, by rfl⟩ : syracuseStep 1592159 = 2388239) B2388239
theorem B1592171 : Blo 1060614 1592171 := bstep (se 1 (by rfl) ⟨1194128, by rfl⟩ : syracuseStep 1592171 = 2388257) B2388257
theorem B4541291 : Blo 1060614 4541291 := bstep (se 1 (by rfl) ⟨3405968, by rfl⟩ : syracuseStep 4541291 = 6811937) B6811937
theorem B8080235 : Blo 1060614 8080235 := bstep (se 1 (by rfl) ⟨6060176, by rfl⟩ : syracuseStep 8080235 = 12120353) B12120353
theorem B2018191 : Blo 1060614 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B1362863 : Blo 1060614 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B6048695 : Blo 1060614 6048695 := bstep (se 1 (by rfl) ⟨4536521, by rfl⟩ : syracuseStep 6048695 = 9073043) B9073043
theorem B2018267 : Blo 1060614 2018267 := bstep (se 1 (by rfl) ⟨1513700, by rfl⟩ : syracuseStep 2018267 = 3027401) B3027401
theorem B1592399 : Blo 1060614 1592399 := bstep (se 1 (by rfl) ⟨1194299, by rfl⟩ : syracuseStep 1592399 = 2388599) B2388599
theorem B1592519 : Blo 1060614 1592519 := bstep (se 1 (by rfl) ⟨1194389, by rfl⟩ : syracuseStep 1592519 = 2388779) B2388779
theorem B3591485 : Blo 1060614 3591485 := bstep (se 3 (by rfl) ⟨673403, by rfl⟩ : syracuseStep 3591485 = 1346807) B1346807
theorem B1592681 : Blo 1060614 1592681 := bstep (se 2 (by rfl) ⟨597255, by rfl⟩ : syracuseStep 1592681 = 1194511) B1194511
theorem B1592759 : Blo 1060614 1592759 := bstep (se 1 (by rfl) ⟨1194569, by rfl⟩ : syracuseStep 1592759 = 2389139) B2389139
theorem B1592795 : Blo 1060614 1592795 := bstep (se 1 (by rfl) ⟨1194596, by rfl⟩ : syracuseStep 1592795 = 2389193) B2389193
theorem B2182619 : Blo 1060614 2182619 := bstep (se 1 (by rfl) ⟨1636964, by rfl⟩ : syracuseStep 2182619 = 3273929) B3273929
theorem B6049403 : Blo 1060614 6049403 := bstep (se 1 (by rfl) ⟨4537052, by rfl⟩ : syracuseStep 6049403 = 9074105) B9074105
theorem B5459831 : Blo 1060614 5459831 := bstep (se 1 (by rfl) ⟨4094873, by rfl⟩ : syracuseStep 5459831 = 8189747) B8189747
theorem B1593263 : Blo 1060614 1593263 := bstep (se 1 (by rfl) ⟨1194947, by rfl⟩ : syracuseStep 1593263 = 2389895) B2389895
theorem B8179643 : Blo 1060614 8179643 := bstep (se 1 (by rfl) ⟨6134732, by rfl⟩ : syracuseStep 8179643 = 12269465) B12269465
theorem B1593353 : Blo 1060614 1593353 := bstep (se 2 (by rfl) ⟨597507, by rfl⟩ : syracuseStep 1593353 = 1195015) B1195015
theorem B1593383 : Blo 1060614 1593383 := bstep (se 1 (by rfl) ⟨1195037, by rfl⟩ : syracuseStep 1593383 = 2390075) B2390075
theorem B1593467 : Blo 1060614 1593467 := bstep (se 1 (by rfl) ⟨1195100, by rfl⟩ : syracuseStep 1593467 = 2390201) B2390201
theorem B3592349 : Blo 1060614 3592349 := bstep (se 3 (by rfl) ⟨673565, by rfl⟩ : syracuseStep 3592349 = 1347131) B1347131
theorem B1790201 : Blo 1060614 1790201 := bstep (se 2 (by rfl) ⟨671325, by rfl⟩ : syracuseStep 1790201 = 1342651) B1342651
theorem B1593593 : Blo 1060614 1593593 := bstep (se 2 (by rfl) ⟨597597, by rfl⟩ : syracuseStep 1593593 = 1195195) B1195195
theorem B1593695 : Blo 1060614 1593695 := bstep (se 1 (by rfl) ⟨1195271, by rfl⟩ : syracuseStep 1593695 = 2390543) B2390543
theorem B6050153 : Blo 1060614 6050153 := bstep (se 2 (by rfl) ⟨2268807, by rfl⟩ : syracuseStep 6050153 = 4537615) B4537615
theorem B1593707 : Blo 1060614 1593707 := bstep (se 1 (by rfl) ⟨1195280, by rfl⟩ : syracuseStep 1593707 = 2390561) B2390561
theorem B1790383 : Blo 1060614 1790383 := bstep (se 1 (by rfl) ⟨1342787, by rfl⟩ : syracuseStep 1790383 = 2685575) B2685575
theorem B1790471 : Blo 1060614 1790471 := bstep (se 1 (by rfl) ⟨1342853, by rfl⟩ : syracuseStep 1790471 = 2685707) B2685707
theorem B1593935 : Blo 1060614 1593935 := bstep (se 1 (by rfl) ⟨1195451, by rfl⟩ : syracuseStep 1593935 = 2390903) B2390903
theorem B3494497 : Blo 1060614 3494497 := bstep (se 2 (by rfl) ⟨1310436, by rfl⟩ : syracuseStep 3494497 = 2620873) B2620873
theorem B3592889 : Blo 1060614 3592889 := bstep (se 2 (by rfl) ⟨1347333, by rfl⟩ : syracuseStep 3592889 = 2694667) B2694667
theorem B1594055 : Blo 1060614 1594055 := bstep (se 1 (by rfl) ⟨1195541, by rfl⟩ : syracuseStep 1594055 = 2391083) B2391083
theorem B8082179 : Blo 1060614 8082179 := bstep (se 1 (by rfl) ⟨6061634, by rfl⟩ : syracuseStep 8082179 = 12123269) B12123269
theorem B1790815 : Blo 1060614 1790815 := bstep (se 1 (by rfl) ⟨1343111, by rfl⟩ : syracuseStep 1790815 = 2686223) B2686223
theorem B1594217 : Blo 1060614 1594217 := bstep (se 2 (by rfl) ⟨597831, by rfl⟩ : syracuseStep 1594217 = 1195663) B1195663
theorem B1790903 : Blo 1060614 1790903 := bstep (se 1 (by rfl) ⟨1343177, by rfl⟩ : syracuseStep 1790903 = 2686355) B2686355
theorem B1594295 : Blo 1060614 1594295 := bstep (se 1 (by rfl) ⟨1195721, by rfl⟩ : syracuseStep 1594295 = 2391443) B2391443
theorem B1594331 : Blo 1060614 1594331 := bstep (se 1 (by rfl) ⟨1195748, by rfl⟩ : syracuseStep 1594331 = 2391497) B2391497
theorem B26235971 : Blo 1060614 26235971 := bstep (se 1 (by rfl) ⟨19676978, by rfl⟩ : syracuseStep 26235971 = 39353957) B39353957
theorem B34493843 : Blo 1060614 34493843 := bstep (se 1 (by rfl) ⟨25870382, by rfl⟩ : syracuseStep 34493843 = 51740765) B51740765
theorem B1594799 : Blo 1060614 1594799 := bstep (se 1 (by rfl) ⟨1196099, by rfl⟩ : syracuseStep 1594799 = 2392199) B2392199
theorem B1791497 : Blo 1060614 1791497 := bstep (se 2 (by rfl) ⟨671811, by rfl⟩ : syracuseStep 1791497 = 1343623) B1343623
theorem B1594889 : Blo 1060614 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B1594919 : Blo 1060614 1594919 := bstep (se 1 (by rfl) ⟨1196189, by rfl⟩ : syracuseStep 1594919 = 2392379) B2392379
theorem B4544039 : Blo 1060614 4544039 := bstep (se 1 (by rfl) ⟨3408029, by rfl⟩ : syracuseStep 4544039 = 6816059) B6816059
theorem B1595003 : Blo 1060614 1595003 := bstep (se 1 (by rfl) ⟨1196252, by rfl⟩ : syracuseStep 1595003 = 2392505) B2392505
theorem B1791659 : Blo 1060614 1791659 := bstep (se 1 (by rfl) ⟨1343744, by rfl⟩ : syracuseStep 1791659 = 2687489) B2687489
theorem B4314833 : Blo 1060614 4314833 := bstep (se 2 (by rfl) ⟨1618062, by rfl⟩ : syracuseStep 4314833 = 3236125) B3236125
theorem B1595129 : Blo 1060614 1595129 := bstep (se 2 (by rfl) ⟨598173, by rfl⟩ : syracuseStep 1595129 = 1196347) B1196347
theorem B1595231 : Blo 1060614 1595231 := bstep (se 1 (by rfl) ⟨1196423, by rfl⟩ : syracuseStep 1595231 = 2392847) B2392847
theorem B1595243 : Blo 1060614 1595243 := bstep (se 1 (by rfl) ⟨1196432, by rfl⟩ : syracuseStep 1595243 = 2392865) B2392865
theorem B1792057 : Blo 1060614 1792057 := bstep (se 2 (by rfl) ⟨672021, by rfl⟩ : syracuseStep 1792057 = 1344043) B1344043
theorem B1595471 : Blo 1060614 1595471 := bstep (se 1 (by rfl) ⟨1196603, by rfl⟩ : syracuseStep 1595471 = 2393207) B2393207
theorem B1792199 : Blo 1060614 1792199 := bstep (se 1 (by rfl) ⟨1344149, by rfl⟩ : syracuseStep 1792199 = 2688299) B2688299
theorem B1595591 : Blo 1060614 1595591 := bstep (se 1 (by rfl) ⟨1196693, by rfl⟩ : syracuseStep 1595591 = 2393387) B2393387
theorem B1595753 : Blo 1060614 1595753 := bstep (se 2 (by rfl) ⟨598407, by rfl⟩ : syracuseStep 1595753 = 1196815) B1196815
theorem B1792361 : Blo 1060614 1792361 := bstep (se 2 (by rfl) ⟨672135, by rfl⟩ : syracuseStep 1792361 = 1344271) B1344271
theorem B8608153 : Blo 1060614 8608153 := bstep (se 2 (by rfl) ⟨3228057, by rfl⟩ : syracuseStep 8608153 = 6456115) B6456115
theorem B1595831 : Blo 1060614 1595831 := bstep (se 1 (by rfl) ⟨1196873, by rfl⟩ : syracuseStep 1595831 = 2393747) B2393747
theorem B1595867 : Blo 1060614 1595867 := bstep (se 1 (by rfl) ⟨1196900, by rfl⟩ : syracuseStep 1595867 = 2393801) B2393801
theorem B5167597 : Blo 1060614 5167597 := bstep (se 3 (by rfl) ⟨968924, by rfl⟩ : syracuseStep 5167597 = 1937849) B1937849
theorem B3398291 : Blo 1060614 3398291 := bstep (se 1 (by rfl) ⟨2548718, by rfl⟩ : syracuseStep 3398291 = 5097437) B5097437
theorem B1792759 : Blo 1060614 1792759 := bstep (se 1 (by rfl) ⟨1344569, by rfl⟩ : syracuseStep 1792759 = 2689139) B2689139
theorem B3398393 : Blo 1060614 3398393 := bstep (se 2 (by rfl) ⟨1274397, by rfl⟩ : syracuseStep 3398393 = 2548795) B2548795
theorem B4315999 : Blo 1060614 4315999 := bstep (se 1 (by rfl) ⟨3236999, by rfl⟩ : syracuseStep 4315999 = 6473999) B6473999
theorem B1596335 : Blo 1060614 1596335 := bstep (se 1 (by rfl) ⟨1197251, by rfl⟩ : syracuseStep 1596335 = 2394503) B2394503
theorem B1792955 : Blo 1060614 1792955 := bstep (se 1 (by rfl) ⟨1344716, by rfl⟩ : syracuseStep 1792955 = 2689433) B2689433
theorem B1596425 : Blo 1060614 1596425 := bstep (se 2 (by rfl) ⟨598659, by rfl⟩ : syracuseStep 1596425 = 1197319) B1197319
theorem B1793063 : Blo 1060614 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B1596455 : Blo 1060614 1596455 := bstep (se 1 (by rfl) ⟨1197341, by rfl⟩ : syracuseStep 1596455 = 2394683) B2394683
theorem B4086865 : Blo 1060614 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B1596539 : Blo 1060614 1596539 := bstep (se 1 (by rfl) ⟨1197404, by rfl⟩ : syracuseStep 1596539 = 2394809) B2394809
theorem B1596665 : Blo 1060614 1596665 := bstep (se 2 (by rfl) ⟨598749, by rfl⟩ : syracuseStep 1596665 = 1197499) B1197499
theorem B1793353 : Blo 1060614 1793353 := bstep (se 2 (by rfl) ⟨672507, by rfl⟩ : syracuseStep 1793353 = 1345015) B1345015
theorem B1596767 : Blo 1060614 1596767 := bstep (se 1 (by rfl) ⟨1197575, by rfl⟩ : syracuseStep 1596767 = 2395151) B2395151
theorem B1793387 : Blo 1060614 1793387 := bstep (se 1 (by rfl) ⟨1345040, by rfl⟩ : syracuseStep 1793387 = 2690081) B2690081
theorem B1596779 : Blo 1060614 1596779 := bstep (se 1 (by rfl) ⟨1197584, by rfl⟩ : syracuseStep 1596779 = 2395169) B2395169
theorem B5103319 : Blo 1060614 5103319 := bstep (se 1 (by rfl) ⟨3827489, by rfl⟩ : syracuseStep 5103319 = 7654979) B7654979
theorem B1793785 : Blo 1060614 1793785 := bstep (se 2 (by rfl) ⟨672669, by rfl⟩ : syracuseStep 1793785 = 1345339) B1345339
theorem B1794055 : Blo 1060614 1794055 := bstep (se 1 (by rfl) ⟨1345541, by rfl⟩ : syracuseStep 1794055 = 2691083) B2691083
theorem B1794487 : Blo 1060614 1794487 := bstep (se 1 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 1794487 = 2691731) B2691731
theorem B1794683 : Blo 1060614 1794683 := bstep (se 1 (by rfl) ⟨1346012, by rfl⟩ : syracuseStep 1794683 = 2692025) B2692025
theorem B15327953 : Blo 1060614 15327953 := bstep (se 2 (by rfl) ⟨5747982, by rfl⟩ : syracuseStep 15327953 = 11495965) B11495965
theorem B2876153 : Blo 1060614 2876153 := bstep (se 2 (by rfl) ⟨1078557, by rfl⟩ : syracuseStep 2876153 = 2157115) B2157115
theorem B10216367 : Blo 1060614 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B1795081 : Blo 1060614 1795081 := bstep (se 2 (by rfl) ⟨673155, by rfl⟩ : syracuseStep 1795081 = 1346311) B1346311
theorem B1795243 : Blo 1060614 1795243 := bstep (se 1 (by rfl) ⟨1346432, by rfl⟩ : syracuseStep 1795243 = 2692865) B2692865
theorem B3826883 : Blo 1060614 3826883 := bstep (se 1 (by rfl) ⟨2870162, by rfl⟩ : syracuseStep 3826883 = 5740325) B5740325
theorem B1795547 : Blo 1060614 1795547 := bstep (se 1 (by rfl) ⟨1346660, by rfl⟩ : syracuseStep 1795547 = 2693321) B2693321
theorem B11495009 : Blo 1060614 11495009 := bstep (se 2 (by rfl) ⟨4310628, by rfl⟩ : syracuseStep 11495009 = 8621257) B8621257
theorem B1795783 : Blo 1060614 1795783 := bstep (se 1 (by rfl) ⟨1346837, by rfl⟩ : syracuseStep 1795783 = 2693675) B2693675
theorem B9070379 : Blo 1060614 9070379 := bstep (se 1 (by rfl) ⟨6802784, by rfl⟩ : syracuseStep 9070379 = 13605569) B13605569
theorem B1795945 : Blo 1060614 1795945 := bstep (se 2 (by rfl) ⟨673479, by rfl⟩ : syracuseStep 1795945 = 1346959) B1346959
theorem B3827575 : Blo 1060614 3827575 := bstep (se 1 (by rfl) ⟨2870681, by rfl⟩ : syracuseStep 3827575 = 5741363) B5741363
theorem B3107063 : Blo 1060614 3107063 := bstep (se 1 (by rfl) ⟨2330297, by rfl⟩ : syracuseStep 3107063 = 4660595) B4660595
theorem B3631675 : Blo 1060614 3631675 := bstep (se 1 (by rfl) ⟨2723756, by rfl⟩ : syracuseStep 3631675 = 5447513) B5447513
theorem B2386529 : Blo 1060614 2386529 := bstep (se 2 (by rfl) ⟨894948, by rfl⟩ : syracuseStep 2386529 = 1789897) B1789897
theorem B2386871 : Blo 1060614 2386871 := bstep (se 1 (by rfl) ⟨1790153, by rfl⟩ : syracuseStep 2386871 = 3580307) B3580307
theorem B5991475 : Blo 1060614 5991475 := bstep (se 1 (by rfl) ⟨4493606, by rfl⟩ : syracuseStep 5991475 = 8987213) B8987213
theorem B2158007 : Blo 1060614 2158007 := bstep (se 1 (by rfl) ⟨1618505, by rfl⟩ : syracuseStep 2158007 = 3237011) B3237011
theorem B2387465 : Blo 1060614 2387465 := bstep (se 2 (by rfl) ⟨895299, by rfl⟩ : syracuseStep 2387465 = 1790599) B1790599
theorem B5369489 : Blo 1060614 5369489 := bstep (se 2 (by rfl) ⟨2013558, by rfl⟩ : syracuseStep 5369489 = 4027117) B4027117
theorem B2387807 : Blo 1060614 2387807 := bstep (se 1 (by rfl) ⟨1790855, by rfl⟩ : syracuseStep 2387807 = 3581711) B3581711
theorem B18411395 : Blo 1060614 18411395 := bstep (se 1 (by rfl) ⟨13808546, by rfl⟩ : syracuseStep 18411395 = 27617093) B27617093
theorem B2584507 : Blo 1060614 2584507 := bstep (se 1 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 2584507 = 3876761) B3876761
theorem B2387987 : Blo 1060614 2387987 := bstep (se 1 (by rfl) ⟨1790990, by rfl⟩ : syracuseStep 2387987 = 3581981) B3581981
theorem B2388329 : Blo 1060614 2388329 := bstep (se 2 (by rfl) ⟨895623, by rfl⟩ : syracuseStep 2388329 = 1791247) B1791247
theorem B5828969 : Blo 1060614 5828969 := bstep (se 2 (by rfl) ⟨2185863, by rfl⟩ : syracuseStep 5828969 = 4371727) B4371727
theorem B6812369 : Blo 1060614 6812369 := bstep (se 2 (by rfl) ⟨2554638, by rfl⟩ : syracuseStep 6812369 = 5109277) B5109277
theorem B2388923 : Blo 1060614 2388923 := bstep (se 1 (by rfl) ⟨1791692, by rfl⟩ : syracuseStep 2388923 = 3583385) B3583385
theorem B2389049 : Blo 1060614 2389049 := bstep (se 2 (by rfl) ⟨895893, by rfl⟩ : syracuseStep 2389049 = 1791787) B1791787
theorem B3404879 : Blo 1060614 3404879 := bstep (se 1 (by rfl) ⟨2553659, by rfl⟩ : syracuseStep 3404879 = 5107319) B5107319
theorem B26211529 : Blo 1060614 26211529 := bstep (se 2 (by rfl) ⟨9829323, by rfl⟩ : syracuseStep 26211529 = 19658647) B19658647
theorem B8615159 : Blo 1060614 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B2389391 : Blo 1060614 2389391 := bstep (se 1 (by rfl) ⟨1792043, by rfl⟩ : syracuseStep 2389391 = 3584087) B3584087
theorem B13628837 : Blo 1060614 13628837 := bstep (se 4 (by rfl) ⟨1277703, by rfl⟩ : syracuseStep 13628837 = 2555407) B2555407
theorem B1275431 : Blo 1060614 1275431 := bstep (se 1 (by rfl) ⟨956573, by rfl⟩ : syracuseStep 1275431 = 1913147) B1913147
theorem B4028089 : Blo 1060614 4028089 := bstep (se 2 (by rfl) ⟨1510533, by rfl⟩ : syracuseStep 4028089 = 3021067) B3021067
theorem B2389715 : Blo 1060614 2389715 := bstep (se 1 (by rfl) ⟨1792286, by rfl⟩ : syracuseStep 2389715 = 3584573) B3584573
theorem B5371757 : Blo 1060614 5371757 := bstep (se 3 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 5371757 = 2014409) B2014409
theorem B3831727 : Blo 1060614 3831727 := bstep (se 1 (by rfl) ⟨2873795, by rfl⟩ : syracuseStep 3831727 = 5747591) B5747591
theorem B5371919 : Blo 1060614 5371919 := bstep (se 1 (by rfl) ⟨4028939, by rfl⟩ : syracuseStep 5371919 = 8057879) B8057879
theorem B2684947 : Blo 1060614 2684947 := bstep (se 1 (by rfl) ⟨2013710, by rfl⟩ : syracuseStep 2684947 = 4027421) B4027421
theorem B15300845 : Blo 1060614 15300845 := bstep (se 3 (by rfl) ⟨2868908, by rfl⟩ : syracuseStep 15300845 = 5737817) B5737817
theorem B2390651 : Blo 1060614 2390651 := bstep (se 1 (by rfl) ⟨1792988, by rfl⟩ : syracuseStep 2390651 = 3585977) B3585977
theorem B3832535 : Blo 1060614 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B2390777 : Blo 1060614 2390777 := bstep (se 2 (by rfl) ⟨896541, by rfl⟩ : syracuseStep 2390777 = 1793083) B1793083
theorem B13597469 : Blo 1060614 13597469 := bstep (se 3 (by rfl) ⟨2549525, by rfl⟩ : syracuseStep 13597469 = 5099051) B5099051
theorem B8059823 : Blo 1060614 8059823 := bstep (se 1 (by rfl) ⟨6044867, by rfl⟩ : syracuseStep 8059823 = 12089735) B12089735
theorem B2391047 : Blo 1060614 2391047 := bstep (se 1 (by rfl) ⟨1793285, by rfl⟩ : syracuseStep 2391047 = 3586571) B3586571
theorem B2686031 : Blo 1060614 2686031 := bstep (se 1 (by rfl) ⟨2014523, by rfl⟩ : syracuseStep 2686031 = 4029047) B4029047
theorem B2391119 : Blo 1060614 2391119 := bstep (se 1 (by rfl) ⟨1793339, by rfl⟩ : syracuseStep 2391119 = 3586679) B3586679
theorem B1703035 : Blo 1060614 1703035 := bstep (se 1 (by rfl) ⟨1277276, by rfl⟩ : syracuseStep 1703035 = 2554553) B2554553
theorem B3833027 : Blo 1060614 3833027 := bstep (se 1 (by rfl) ⟨2874770, by rfl⟩ : syracuseStep 3833027 = 5749541) B5749541
theorem B4029821 : Blo 1060614 4029821 := bstep (se 3 (by rfl) ⟨755591, by rfl⟩ : syracuseStep 4029821 = 1511183) B1511183
theorem B2391515 : Blo 1060614 2391515 := bstep (se 1 (by rfl) ⟨1793636, by rfl⟩ : syracuseStep 2391515 = 3587273) B3587273
theorem B2686679 : Blo 1060614 2686679 := bstep (se 1 (by rfl) ⟨2015009, by rfl⟩ : syracuseStep 2686679 = 4030019) B4030019
theorem B3407609 : Blo 1060614 3407609 := bstep (se 2 (by rfl) ⟨1277853, by rfl⟩ : syracuseStep 3407609 = 2555707) B2555707
theorem B6061817 : Blo 1060614 6061817 := bstep (se 2 (by rfl) ⟨2273181, by rfl⟩ : syracuseStep 6061817 = 4546363) B4546363
theorem B3407723 : Blo 1060614 3407723 := bstep (se 1 (by rfl) ⟨2555792, by rfl⟩ : syracuseStep 3407723 = 5111585) B5111585
theorem B5734253 : Blo 1060614 5734253 := bstep (se 3 (by rfl) ⟨1075172, by rfl⟩ : syracuseStep 5734253 = 2150345) B2150345
theorem B2391983 : Blo 1060614 2391983 := bstep (se 1 (by rfl) ⟨1793987, by rfl⟩ : syracuseStep 2391983 = 3587975) B3587975
theorem B2392073 : Blo 1060614 2392073 := bstep (se 2 (by rfl) ⟨897027, by rfl⟩ : syracuseStep 2392073 = 1794055) B1794055
theorem B38830103 : Blo 1060614 38830103 := bstep (se 1 (by rfl) ⟨29122577, by rfl⟩ : syracuseStep 38830103 = 58245155) B58245155
theorem B4030793 : Blo 1060614 4030793 := bstep (se 2 (by rfl) ⟨1511547, by rfl⟩ : syracuseStep 4030793 = 3023095) B3023095
theorem B2392487 : Blo 1060614 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B2425313 : Blo 1060614 2425313 := bstep (se 2 (by rfl) ⟨909492, by rfl⟩ : syracuseStep 2425313 = 1818985) B1818985
theorem B2392595 : Blo 1060614 2392595 := bstep (se 1 (by rfl) ⟨1794446, by rfl⟩ : syracuseStep 2392595 = 3588893) B3588893
theorem B2392649 : Blo 1060614 2392649 := bstep (se 2 (by rfl) ⟨897243, by rfl⟩ : syracuseStep 2392649 = 1794487) B1794487
theorem B5898905 : Blo 1060614 5898905 := bstep (se 2 (by rfl) ⟨2212089, by rfl⟩ : syracuseStep 5898905 = 4424179) B4424179
theorem B2458295 : Blo 1060614 2458295 := bstep (se 1 (by rfl) ⟨1843721, by rfl⟩ : syracuseStep 2458295 = 3687443) B3687443
theorem B2687975 : Blo 1060614 2687975 := bstep (se 1 (by rfl) ⟨2015981, by rfl⟩ : syracuseStep 2687975 = 4031963) B4031963
theorem B2393063 : Blo 1060614 2393063 := bstep (se 1 (by rfl) ⟨1794797, by rfl⟩ : syracuseStep 2393063 = 3589595) B3589595
theorem B3736567 : Blo 1060614 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B388498747 : Blo 1060614 388498747 := bstep (se 1 (by rfl) ⟨291374060, by rfl⟩ : syracuseStep 388498747 = 582748121) B582748121
theorem B2393441 : Blo 1060614 2393441 := bstep (se 2 (by rfl) ⟨897540, by rfl⟩ : syracuseStep 2393441 = 1795081) B1795081
theorem B2393531 : Blo 1060614 2393531 := bstep (se 1 (by rfl) ⟨1795148, by rfl⟩ : syracuseStep 2393531 = 3590297) B3590297
theorem B3409415 : Blo 1060614 3409415 := bstep (se 1 (by rfl) ⟨2557061, by rfl⟩ : syracuseStep 3409415 = 5114123) B5114123
theorem B12912185 : Blo 1060614 12912185 := bstep (se 2 (by rfl) ⟨4842069, by rfl⟩ : syracuseStep 12912185 = 9684139) B9684139
theorem B2393657 : Blo 1060614 2393657 := bstep (se 2 (by rfl) ⟨897621, by rfl⟩ : syracuseStep 2393657 = 1795243) B1795243
theorem B3409465 : Blo 1060614 3409465 := bstep (se 2 (by rfl) ⟨1278549, by rfl⟩ : syracuseStep 3409465 = 2557099) B2557099
theorem B5375645 : Blo 1060614 5375645 := bstep (se 3 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 5375645 = 2015867) B2015867
theorem B2688673 : Blo 1060614 2688673 := bstep (se 2 (by rfl) ⟨1008252, by rfl⟩ : syracuseStep 2688673 = 2016505) B2016505
theorem B2590471 : Blo 1060614 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B2688815 : Blo 1060614 2688815 := bstep (se 1 (by rfl) ⟨2016611, by rfl⟩ : syracuseStep 2688815 = 4033223) B4033223
theorem B4032463 : Blo 1060614 4032463 := bstep (se 1 (by rfl) ⟨3024347, by rfl⟩ : syracuseStep 4032463 = 6048695) B6048695
theorem B1345511 : Blo 1060614 1345511 := bstep (se 1 (by rfl) ⟨1009133, by rfl⟩ : syracuseStep 1345511 = 2018267) B2018267
theorem B7669741 : Blo 1060614 7669741 := bstep (se 3 (by rfl) ⟨1438076, by rfl⟩ : syracuseStep 7669741 = 2876153) B2876153
theorem B2394323 : Blo 1060614 2394323 := bstep (se 1 (by rfl) ⟨1795742, by rfl⟩ : syracuseStep 2394323 = 3591485) B3591485
theorem B2394377 : Blo 1060614 2394377 := bstep (se 2 (by rfl) ⟨897891, by rfl⟩ : syracuseStep 2394377 = 1795783) B1795783
theorem B4032935 : Blo 1060614 4032935 := bstep (se 1 (by rfl) ⟨3024701, by rfl⟩ : syracuseStep 4032935 = 6049403) B6049403
theorem B2689463 : Blo 1060614 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B2394593 : Blo 1060614 2394593 := bstep (se 2 (by rfl) ⟨897972, by rfl⟩ : syracuseStep 2394593 = 1795945) B1795945
theorem B3639887 : Blo 1060614 3639887 := bstep (se 1 (by rfl) ⟨2729915, by rfl⟩ : syracuseStep 3639887 = 5459831) B5459831
theorem B11471483 : Blo 1060614 11471483 := bstep (se 1 (by rfl) ⟨8603612, by rfl⟩ : syracuseStep 11471483 = 17207225) B17207225
theorem B2394899 : Blo 1060614 2394899 := bstep (se 1 (by rfl) ⟨1796174, by rfl⟩ : syracuseStep 2394899 = 3592349) B3592349
theorem B4033435 : Blo 1060614 4033435 := bstep (se 1 (by rfl) ⟨3025076, by rfl⟩ : syracuseStep 4033435 = 6050153) B6050153
theorem B5376941 : Blo 1060614 5376941 := bstep (se 3 (by rfl) ⟨1008176, by rfl⟩ : syracuseStep 5376941 = 2016353) B2016353
theorem B2395259 : Blo 1060614 2395259 := bstep (se 1 (by rfl) ⟨1796444, by rfl⟩ : syracuseStep 2395259 = 3592889) B3592889
theorem B5180683 : Blo 1060614 5180683 := bstep (se 1 (by rfl) ⟨3885512, by rfl⟩ : syracuseStep 5180683 = 7771025) B7771025
theorem B2690567 : Blo 1060614 2690567 := bstep (se 1 (by rfl) ⟨2017925, by rfl⟩ : syracuseStep 2690567 = 4035851) B4035851
theorem B2690617 : Blo 1060614 2690617 := bstep (se 2 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 2690617 = 2017963) B2017963
theorem B55119457 : Blo 1060614 55119457 := bstep (se 2 (by rfl) ⟨20669796, by rfl⟩ : syracuseStep 55119457 = 41339593) B41339593
theorem B2690921 : Blo 1060614 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B10227779 : Blo 1060614 10227779 := bstep (se 1 (by rfl) ⟨7670834, by rfl⟩ : syracuseStep 10227779 = 15341669) B15341669
theorem B2265527 : Blo 1060614 2265527 := bstep (se 1 (by rfl) ⟨1699145, by rfl⟩ : syracuseStep 2265527 = 3398291) B3398291
theorem B2691539 : Blo 1060614 2691539 := bstep (se 1 (by rfl) ⟨2018654, by rfl⟩ : syracuseStep 2691539 = 4037309) B4037309
theorem B5378561 : Blo 1060614 5378561 := bstep (se 2 (by rfl) ⟨2016960, by rfl⟩ : syracuseStep 5378561 = 4033921) B4033921
theorem B5379047 : Blo 1060614 5379047 := bstep (se 1 (by rfl) ⟨4034285, by rfl⟩ : syracuseStep 5379047 = 8068571) B8068571
theorem B5444765 : Blo 1060614 5444765 := bstep (se 3 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 5444765 = 2041787) B2041787
theorem B3446009 : Blo 1060614 3446009 := bstep (se 2 (by rfl) ⟨1292253, by rfl⟩ : syracuseStep 3446009 = 2584507) B2584507
theorem B5379371 : Blo 1060614 5379371 := bstep (se 1 (by rfl) ⟨4034528, by rfl⟩ : syracuseStep 5379371 = 8069057) B8069057
theorem B3544633 : Blo 1060614 3544633 := bstep (se 2 (by rfl) ⟨1329237, by rfl⟩ : syracuseStep 3544633 = 2658475) B2658475
theorem B2692703 : Blo 1060614 2692703 := bstep (se 1 (by rfl) ⟨2019527, by rfl⟩ : syracuseStep 2692703 = 4039055) B4039055
theorem B13604597 : Blo 1060614 13604597 := bstep (se 5 (by rfl) ⟨637715, by rfl⟩ : syracuseStep 13604597 = 1275431) B1275431
theorem B21796613 : Blo 1060614 21796613 := bstep (se 4 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 21796613 = 4086865) B4086865
theorem B9082853 : Blo 1060614 9082853 := bstep (se 4 (by rfl) ⟨851517, by rfl⟩ : syracuseStep 9082853 = 1703035) B1703035
theorem B4659329 : Blo 1060614 4659329 := bstep (se 2 (by rfl) ⟨1747248, by rfl⟩ : syracuseStep 4659329 = 3494497) B3494497
theorem B5380343 : Blo 1060614 5380343 := bstep (se 1 (by rfl) ⟨4035257, by rfl⟩ : syracuseStep 5380343 = 8070515) B8070515
theorem B2693483 : Blo 1060614 2693483 := bstep (se 1 (by rfl) ⟨2020112, by rfl⟩ : syracuseStep 2693483 = 4040225) B4040225
theorem B3021239 : Blo 1060614 3021239 := bstep (se 1 (by rfl) ⟨2265929, by rfl⟩ : syracuseStep 3021239 = 4531859) B4531859
theorem B2693695 : Blo 1060614 2693695 := bstep (se 1 (by rfl) ⟨2020271, by rfl⟩ : syracuseStep 2693695 = 4040543) B4040543
theorem B1940089 : Blo 1060614 1940089 := bstep (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) B1455067
theorem B2693807 : Blo 1060614 2693807 := bstep (se 1 (by rfl) ⟨2020355, by rfl⟩ : syracuseStep 2693807 = 4040711) B4040711
theorem B5380829 : Blo 1060614 5380829 := bstep (se 3 (by rfl) ⟨1008905, by rfl⟩ : syracuseStep 5380829 = 2017811) B2017811
theorem B2694131 : Blo 1060614 2694131 := bstep (se 1 (by rfl) ⟨2020598, by rfl⟩ : syracuseStep 2694131 = 4041197) B4041197
theorem B2694343 : Blo 1060614 2694343 := bstep (se 1 (by rfl) ⟨2020757, by rfl⟩ : syracuseStep 2694343 = 4041515) B4041515
theorem B3022571 : Blo 1060614 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B3579659 : Blo 1060614 3579659 := bstep (se 1 (by rfl) ⟨2684744, by rfl⟩ : syracuseStep 3579659 = 5369489) B5369489
theorem B21831605 : Blo 1060614 21831605 := bstep (se 5 (by rfl) ⟨1023356, by rfl⟩ : syracuseStep 21831605 = 2046713) B2046713
theorem B3579929 : Blo 1060614 3579929 := bstep (se 2 (by rfl) ⟨1342473, by rfl⟩ : syracuseStep 3579929 = 2684947) B2684947
theorem B22946003 : Blo 1060614 22946003 := bstep (se 1 (by rfl) ⟨17209502, by rfl⟩ : syracuseStep 22946003 = 34419005) B34419005
theorem B11477537 : Blo 1060614 11477537 := bstep (se 2 (by rfl) ⟨4304076, by rfl⟩ : syracuseStep 11477537 = 8608153) B8608153
theorem B6890129 : Blo 1060614 6890129 := bstep (se 2 (by rfl) ⟨2583798, by rfl⟩ : syracuseStep 6890129 = 5167597) B5167597
theorem B5251787 : Blo 1060614 5251787 := bstep (se 1 (by rfl) ⟨3938840, by rfl⟩ : syracuseStep 5251787 = 7877681) B7877681
theorem B2269919 : Blo 1060614 2269919 := bstep (se 1 (by rfl) ⟨1702439, by rfl⟩ : syracuseStep 2269919 = 3404879) B3404879
theorem B5743439 : Blo 1060614 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B9085891 : Blo 1060614 9085891 := bstep (se 1 (by rfl) ⟨6814418, by rfl⟩ : syracuseStep 9085891 = 13628837) B13628837
theorem B3581171 : Blo 1060614 3581171 := bstep (se 1 (by rfl) ⟨2685878, by rfl⟩ : syracuseStep 3581171 = 5371757) B5371757
theorem B3581279 : Blo 1060614 3581279 := bstep (se 1 (by rfl) ⟨2685959, by rfl⟩ : syracuseStep 3581279 = 5371919) B5371919
theorem B10200563 : Blo 1060614 10200563 := bstep (se 1 (by rfl) ⟨7650422, by rfl⟩ : syracuseStep 10200563 = 15300845) B15300845
theorem B13117625 : Blo 1060614 13117625 := bstep (se 2 (by rfl) ⟨4919109, by rfl⟩ : syracuseStep 13117625 = 9838219) B9838219
theorem B49097053 : Blo 1060614 49097053 := bstep (se 3 (by rfl) ⟨9205697, by rfl⟩ : syracuseStep 49097053 = 18411395) B18411395
theorem B2271739 : Blo 1060614 2271739 := bstep (se 1 (by rfl) ⟨1703804, by rfl⟩ : syracuseStep 2271739 = 3407609) B3407609
theorem B4041211 : Blo 1060614 4041211 := bstep (se 1 (by rfl) ⟨3030908, by rfl⟩ : syracuseStep 4041211 = 6061817) B6061817
theorem B2271815 : Blo 1060614 2271815 := bstep (se 1 (by rfl) ⟨1703861, by rfl⟩ : syracuseStep 2271815 = 3407723) B3407723
theorem B3025487 : Blo 1060614 3025487 := bstep (se 1 (by rfl) ⟨2269115, by rfl⟩ : syracuseStep 3025487 = 4538231) B4538231
theorem B5384879 : Blo 1060614 5384879 := bstep (se 1 (by rfl) ⟨4038659, by rfl⟩ : syracuseStep 5384879 = 8077319) B8077319
theorem B19376819 : Blo 1060614 19376819 := bstep (se 1 (by rfl) ⟨14532614, by rfl⟩ : syracuseStep 19376819 = 29065229) B29065229
theorem B5745431 : Blo 1060614 5745431 := bstep (se 1 (by rfl) ⟨4309073, by rfl⟩ : syracuseStep 5745431 = 8618147) B8618147
theorem B3582845 : Blo 1060614 3582845 := bstep (se 3 (by rfl) ⟨671783, by rfl⟩ : syracuseStep 3582845 = 1343567) B1343567
theorem B5385203 : Blo 1060614 5385203 := bstep (se 1 (by rfl) ⟨4038902, by rfl⟩ : syracuseStep 5385203 = 8077805) B8077805
theorem B1911799 : Blo 1060614 1911799 := bstep (se 1 (by rfl) ⟨1433849, by rfl⟩ : syracuseStep 1911799 = 2867699) B2867699
theorem B7777361 : Blo 1060614 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B6466675 : Blo 1060614 6466675 := bstep (se 1 (by rfl) ⟨4850006, by rfl⟩ : syracuseStep 6466675 = 9700013) B9700013
theorem B3583115 : Blo 1060614 3583115 := bstep (se 1 (by rfl) ⟨2687336, by rfl⟩ : syracuseStep 3583115 = 5374673) B5374673
theorem B4533515 : Blo 1060614 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B4042183 : Blo 1060614 4042183 := bstep (se 1 (by rfl) ⟨3031637, by rfl⟩ : syracuseStep 4042183 = 6063275) B6063275
theorem B1060655 : Blo 1060614 1060655 := bstep (se 1 (by rfl) ⟨795491, by rfl⟩ : syracuseStep 1060655 = 1590983) B1590983
theorem B1060763 : Blo 1060614 1060763 := bstep (se 1 (by rfl) ⟨795572, by rfl⟩ : syracuseStep 1060763 = 1591145) B1591145
theorem B1060815 : Blo 1060614 1060815 := bstep (se 1 (by rfl) ⟨795611, by rfl⟩ : syracuseStep 1060815 = 1591223) B1591223
theorem B1060839 : Blo 1060614 1060839 := bstep (se 1 (by rfl) ⟨795629, by rfl⟩ : syracuseStep 1060839 = 1591259) B1591259
theorem B5386499 : Blo 1060614 5386499 := bstep (se 1 (by rfl) ⟨4039874, by rfl⟩ : syracuseStep 5386499 = 8079749) B8079749
theorem B1061151 : Blo 1060614 1061151 := bstep (se 1 (by rfl) ⟨795863, by rfl⟩ : syracuseStep 1061151 = 1591727) B1591727
theorem B2273609 : Blo 1060614 2273609 := bstep (se 2 (by rfl) ⟨852603, by rfl⟩ : syracuseStep 2273609 = 1705207) B1705207
theorem B1061211 : Blo 1060614 1061211 := bstep (se 1 (by rfl) ⟨795908, by rfl⟩ : syracuseStep 1061211 = 1591817) B1591817
theorem B1061231 : Blo 1060614 1061231 := bstep (se 1 (by rfl) ⟨795923, by rfl⟩ : syracuseStep 1061231 = 1591847) B1591847
theorem B1061287 : Blo 1060614 1061287 := bstep (se 1 (by rfl) ⟨795965, by rfl⟩ : syracuseStep 1061287 = 1591931) B1591931
theorem B2044327 : Blo 1060614 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B1061371 : Blo 1060614 1061371 := bstep (se 1 (by rfl) ⟨796028, by rfl⟩ : syracuseStep 1061371 = 1592057) B1592057
theorem B1061439 : Blo 1060614 1061439 := bstep (se 1 (by rfl) ⟨796079, by rfl⟩ : syracuseStep 1061439 = 1592159) B1592159
theorem B1061447 : Blo 1060614 1061447 := bstep (se 1 (by rfl) ⟨796085, by rfl⟩ : syracuseStep 1061447 = 1592171) B1592171
theorem B3027527 : Blo 1060614 3027527 := bstep (se 1 (by rfl) ⟨2270645, by rfl⟩ : syracuseStep 3027527 = 4541291) B4541291
theorem B5386823 : Blo 1060614 5386823 := bstep (se 1 (by rfl) ⟨4040117, by rfl⟩ : syracuseStep 5386823 = 8080235) B8080235
theorem B1061599 : Blo 1060614 1061599 := bstep (se 1 (by rfl) ⟨796199, by rfl⟩ : syracuseStep 1061599 = 1592399) B1592399
theorem B3584735 : Blo 1060614 3584735 := bstep (se 1 (by rfl) ⟨2688551, by rfl⟩ : syracuseStep 3584735 = 5377103) B5377103
theorem B1061679 : Blo 1060614 1061679 := bstep (se 1 (by rfl) ⟨796259, by rfl⟩ : syracuseStep 1061679 = 1592519) B1592519
theorem B1061787 : Blo 1060614 1061787 := bstep (se 1 (by rfl) ⟨796340, by rfl⟩ : syracuseStep 1061787 = 1592681) B1592681
theorem B1061839 : Blo 1060614 1061839 := bstep (se 1 (by rfl) ⟨796379, by rfl⟩ : syracuseStep 1061839 = 1592759) B1592759
theorem B1061863 : Blo 1060614 1061863 := bstep (se 1 (by rfl) ⟨796397, by rfl⟩ : syracuseStep 1061863 = 1592795) B1592795
theorem B1455079 : Blo 1060614 1455079 := bstep (se 1 (by rfl) ⟨1091309, by rfl⟩ : syracuseStep 1455079 = 2182619) B2182619
theorem B3585167 : Blo 1060614 3585167 := bstep (se 1 (by rfl) ⟨2688875, by rfl⟩ : syracuseStep 3585167 = 5377751) B5377751
theorem B1062175 : Blo 1060614 1062175 := bstep (se 1 (by rfl) ⟨796631, by rfl⟩ : syracuseStep 1062175 = 1593263) B1593263
theorem B5453095 : Blo 1060614 5453095 := bstep (se 1 (by rfl) ⟨4089821, by rfl⟩ : syracuseStep 5453095 = 8179643) B8179643
theorem B1062235 : Blo 1060614 1062235 := bstep (se 1 (by rfl) ⟨796676, by rfl⟩ : syracuseStep 1062235 = 1593353) B1593353
theorem B1062255 : Blo 1060614 1062255 := bstep (se 1 (by rfl) ⟨796691, by rfl⟩ : syracuseStep 1062255 = 1593383) B1593383
theorem B1062311 : Blo 1060614 1062311 := bstep (se 1 (by rfl) ⟨796733, by rfl⟩ : syracuseStep 1062311 = 1593467) B1593467
theorem B1193467 : Blo 1060614 1193467 := bstep (se 1 (by rfl) ⟨895100, by rfl⟩ : syracuseStep 1193467 = 1790201) B1790201
theorem B1062395 : Blo 1060614 1062395 := bstep (se 1 (by rfl) ⟨796796, by rfl⟩ : syracuseStep 1062395 = 1593593) B1593593
theorem B1062463 : Blo 1060614 1062463 := bstep (se 1 (by rfl) ⟨796847, by rfl⟩ : syracuseStep 1062463 = 1593695) B1593695
theorem B1062471 : Blo 1060614 1062471 := bstep (se 1 (by rfl) ⟨796853, by rfl⟩ : syracuseStep 1062471 = 1593707) B1593707
theorem B1193647 : Blo 1060614 1193647 := bstep (se 1 (by rfl) ⟨895235, by rfl⟩ : syracuseStep 1193647 = 1790471) B1790471
theorem B9844409 : Blo 1060614 9844409 := bstep (se 2 (by rfl) ⟨3691653, by rfl⟩ : syracuseStep 9844409 = 7383307) B7383307
theorem B1062623 : Blo 1060614 1062623 := bstep (se 1 (by rfl) ⟨796967, by rfl⟩ : syracuseStep 1062623 = 1593935) B1593935
theorem B1062703 : Blo 1060614 1062703 := bstep (se 1 (by rfl) ⟨797027, by rfl⟩ : syracuseStep 1062703 = 1594055) B1594055
theorem B5388119 : Blo 1060614 5388119 := bstep (se 1 (by rfl) ⟨4041089, by rfl⟩ : syracuseStep 5388119 = 8082179) B8082179
theorem B10205021 : Blo 1060614 10205021 := bstep (se 3 (by rfl) ⟨1913441, by rfl⟩ : syracuseStep 10205021 = 3826883) B3826883
theorem B1062811 : Blo 1060614 1062811 := bstep (se 1 (by rfl) ⟨797108, by rfl⟩ : syracuseStep 1062811 = 1594217) B1594217
theorem B1193935 : Blo 1060614 1193935 := bstep (se 1 (by rfl) ⟨895451, by rfl⟩ : syracuseStep 1193935 = 1790903) B1790903
theorem B1062863 : Blo 1060614 1062863 := bstep (se 1 (by rfl) ⟨797147, by rfl⟩ : syracuseStep 1062863 = 1594295) B1594295
theorem B1062887 : Blo 1060614 1062887 := bstep (se 1 (by rfl) ⟨797165, by rfl⟩ : syracuseStep 1062887 = 1594331) B1594331
theorem B3586301 : Blo 1060614 3586301 := bstep (se 3 (by rfl) ⟨672431, by rfl⟩ : syracuseStep 3586301 = 1344863) B1344863
theorem B1063199 : Blo 1060614 1063199 := bstep (se 1 (by rfl) ⟨797399, by rfl⟩ : syracuseStep 1063199 = 1594799) B1594799
theorem B1194331 : Blo 1060614 1194331 := bstep (se 1 (by rfl) ⟨895748, by rfl⟩ : syracuseStep 1194331 = 1791497) B1791497
theorem B1063259 : Blo 1060614 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B1063279 : Blo 1060614 1063279 := bstep (se 1 (by rfl) ⟨797459, by rfl⟩ : syracuseStep 1063279 = 1594919) B1594919
theorem B1063335 : Blo 1060614 1063335 := bstep (se 1 (by rfl) ⟨797501, by rfl⟩ : syracuseStep 1063335 = 1595003) B1595003
theorem B1194439 : Blo 1060614 1194439 := bstep (se 1 (by rfl) ⟨895829, by rfl⟩ : syracuseStep 1194439 = 1791659) B1791659
theorem B1063419 : Blo 1060614 1063419 := bstep (se 1 (by rfl) ⟨797564, by rfl⟩ : syracuseStep 1063419 = 1595129) B1595129
theorem B1063487 : Blo 1060614 1063487 := bstep (se 1 (by rfl) ⟨797615, by rfl⟩ : syracuseStep 1063487 = 1595231) B1595231
theorem B1063495 : Blo 1060614 1063495 := bstep (se 1 (by rfl) ⟨797621, by rfl⟩ : syracuseStep 1063495 = 1595243) B1595243
theorem B2013817 : Blo 1060614 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B1063647 : Blo 1060614 1063647 := bstep (se 1 (by rfl) ⟨797735, by rfl⟩ : syracuseStep 1063647 = 1595471) B1595471
theorem B1194799 : Blo 1060614 1194799 := bstep (se 1 (by rfl) ⟨896099, by rfl⟩ : syracuseStep 1194799 = 1792199) B1792199
theorem B1063727 : Blo 1060614 1063727 := bstep (se 1 (by rfl) ⟨797795, by rfl⟩ : syracuseStep 1063727 = 1595591) B1595591
theorem B1194907 : Blo 1060614 1194907 := bstep (se 1 (by rfl) ⟨896180, by rfl⟩ : syracuseStep 1194907 = 1792361) B1792361
theorem B1063835 : Blo 1060614 1063835 := bstep (se 1 (by rfl) ⟨797876, by rfl⟩ : syracuseStep 1063835 = 1595753) B1595753
theorem B9681839 : Blo 1060614 9681839 := bstep (se 1 (by rfl) ⟨7261379, by rfl⟩ : syracuseStep 9681839 = 14522759) B14522759
theorem B1063887 : Blo 1060614 1063887 := bstep (se 1 (by rfl) ⟨797915, by rfl⟩ : syracuseStep 1063887 = 1595831) B1595831
theorem B1063911 : Blo 1060614 1063911 := bstep (se 1 (by rfl) ⟨797933, by rfl⟩ : syracuseStep 1063911 = 1595867) B1595867
theorem B3587111 : Blo 1060614 3587111 := bstep (se 1 (by rfl) ⟨2690333, by rfl⟩ : syracuseStep 3587111 = 5380667) B5380667
theorem B9092249 : Blo 1060614 9092249 := bstep (se 2 (by rfl) ⟨3409593, by rfl⟩ : syracuseStep 9092249 = 6819187) B6819187
theorem B19414181 : Blo 1060614 19414181 := bstep (se 4 (by rfl) ⟨1820079, by rfl⟩ : syracuseStep 19414181 = 3640159) B3640159
theorem B1064223 : Blo 1060614 1064223 := bstep (se 1 (by rfl) ⟨798167, by rfl⟩ : syracuseStep 1064223 = 1596335) B1596335
theorem B1195303 : Blo 1060614 1195303 := bstep (se 1 (by rfl) ⟨896477, by rfl⟩ : syracuseStep 1195303 = 1792955) B1792955
theorem B1064283 : Blo 1060614 1064283 := bstep (se 1 (by rfl) ⟨798212, by rfl⟩ : syracuseStep 1064283 = 1596425) B1596425
theorem B2014561 : Blo 1060614 2014561 := bstep (se 2 (by rfl) ⟨755460, by rfl⟩ : syracuseStep 2014561 = 1510921) B1510921
theorem B1195375 : Blo 1060614 1195375 := bstep (se 1 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 1195375 = 1793063) B1793063
theorem B1064303 : Blo 1060614 1064303 := bstep (se 1 (by rfl) ⟨798227, by rfl⟩ : syracuseStep 1064303 = 1596455) B1596455
theorem B1064359 : Blo 1060614 1064359 := bstep (se 1 (by rfl) ⟨798269, by rfl⟩ : syracuseStep 1064359 = 1596539) B1596539
theorem B3587543 : Blo 1060614 3587543 := bstep (se 1 (by rfl) ⟨2690657, by rfl⟩ : syracuseStep 3587543 = 5381315) B5381315
theorem B1064443 : Blo 1060614 1064443 := bstep (se 1 (by rfl) ⟨798332, by rfl⟩ : syracuseStep 1064443 = 1596665) B1596665
theorem B1064511 : Blo 1060614 1064511 := bstep (se 1 (by rfl) ⟨798383, by rfl⟩ : syracuseStep 1064511 = 1596767) B1596767
theorem B1195591 : Blo 1060614 1195591 := bstep (se 1 (by rfl) ⟨896693, by rfl⟩ : syracuseStep 1195591 = 1793387) B1793387
theorem B1064519 : Blo 1060614 1064519 := bstep (se 1 (by rfl) ⟨798389, by rfl⟩ : syracuseStep 1064519 = 1596779) B1596779
theorem B2015579 : Blo 1060614 2015579 := bstep (se 1 (by rfl) ⟨1511684, by rfl⟩ : syracuseStep 2015579 = 3023369) B3023369
theorem B1196455 : Blo 1060614 1196455 := bstep (se 1 (by rfl) ⟨897341, by rfl⟩ : syracuseStep 1196455 = 1794683) B1794683
theorem B2802131 : Blo 1060614 2802131 := bstep (se 1 (by rfl) ⟨2101598, by rfl⟩ : syracuseStep 2802131 = 4203197) B4203197
theorem B2016019 : Blo 1060614 2016019 := bstep (se 1 (by rfl) ⟨1512014, by rfl⟩ : syracuseStep 2016019 = 3024029) B3024029
theorem B12108689 : Blo 1060614 12108689 := bstep (se 2 (by rfl) ⟨4540758, by rfl⟩ : syracuseStep 12108689 = 9081517) B9081517
theorem B1197031 : Blo 1060614 1197031 := bstep (se 1 (by rfl) ⟨897773, by rfl⟩ : syracuseStep 1197031 = 1795547) B1795547
theorem B2016247 : Blo 1060614 2016247 := bstep (se 1 (by rfl) ⟨1512185, by rfl⟩ : syracuseStep 2016247 = 3024371) B3024371
theorem B3589217 : Blo 1060614 3589217 := bstep (se 2 (by rfl) ⟨1345956, by rfl⟩ : syracuseStep 3589217 = 2691913) B2691913
theorem B6046919 : Blo 1060614 6046919 := bstep (se 1 (by rfl) ⟨4535189, by rfl⟩ : syracuseStep 6046919 = 9070379) B9070379
theorem B2016551 : Blo 1060614 2016551 := bstep (se 1 (by rfl) ⟨1512413, by rfl⟩ : syracuseStep 2016551 = 3024827) B3024827
theorem B34948705 : Blo 1060614 34948705 := bstep (se 2 (by rfl) ⟨13105764, by rfl⟩ : syracuseStep 34948705 = 26211529) B26211529
theorem B8603293 : Blo 1060614 8603293 := bstep (se 3 (by rfl) ⟨1613117, by rfl⟩ : syracuseStep 8603293 = 3226235) B3226235
theorem B1591019 : Blo 1060614 1591019 := bstep (se 1 (by rfl) ⟨1193264, by rfl⟩ : syracuseStep 1591019 = 2386529) B2386529
theorem B3065705 : Blo 1060614 3065705 := bstep (se 2 (by rfl) ⟨1149639, by rfl⟩ : syracuseStep 3065705 = 2299279) B2299279
theorem B1591247 : Blo 1060614 1591247 := bstep (se 1 (by rfl) ⟨1193435, by rfl⟩ : syracuseStep 1591247 = 2386871) B2386871
theorem B9062381 : Blo 1060614 9062381 := bstep (se 3 (by rfl) ⟨1699196, by rfl⟩ : syracuseStep 9062381 = 3398393) B3398393
theorem B1591643 : Blo 1060614 1591643 := bstep (se 1 (by rfl) ⟨1193732, by rfl⟩ : syracuseStep 1591643 = 2387465) B2387465
theorem B3590567 : Blo 1060614 3590567 := bstep (se 1 (by rfl) ⟨2692925, by rfl⟩ : syracuseStep 3590567 = 5385851) B5385851
theorem B1591871 : Blo 1060614 1591871 := bstep (se 1 (by rfl) ⟨1193903, by rfl⟩ : syracuseStep 1591871 = 2387807) B2387807
theorem B2017865 : Blo 1060614 2017865 := bstep (se 2 (by rfl) ⟨756699, by rfl⟩ : syracuseStep 2017865 = 1513399) B1513399
theorem B3590729 : Blo 1060614 3590729 := bstep (se 2 (by rfl) ⟨1346523, by rfl⟩ : syracuseStep 3590729 = 2693047) B2693047
theorem B1591991 : Blo 1060614 1591991 := bstep (se 1 (by rfl) ⟨1193993, by rfl⟩ : syracuseStep 1591991 = 2387987) B2387987
theorem B1592219 : Blo 1060614 1592219 := bstep (se 1 (by rfl) ⟨1194164, by rfl⟩ : syracuseStep 1592219 = 2388329) B2388329
theorem B3885979 : Blo 1060614 3885979 := bstep (se 1 (by rfl) ⟨2914484, by rfl⟩ : syracuseStep 3885979 = 5828969) B5828969
theorem B4312187 : Blo 1060614 4312187 := bstep (se 1 (by rfl) ⟨3234140, by rfl⟩ : syracuseStep 4312187 = 6468281) B6468281
theorem B4541579 : Blo 1060614 4541579 := bstep (se 1 (by rfl) ⟨3406184, by rfl⟩ : syracuseStep 4541579 = 6812369) B6812369
theorem B1592615 : Blo 1060614 1592615 := bstep (se 1 (by rfl) ⟨1194461, by rfl⟩ : syracuseStep 1592615 = 2388923) B2388923
theorem B1592699 : Blo 1060614 1592699 := bstep (se 1 (by rfl) ⟨1194524, by rfl⟩ : syracuseStep 1592699 = 2389049) B2389049
theorem B1592825 : Blo 1060614 1592825 := bstep (se 2 (by rfl) ⟨597309, by rfl⟩ : syracuseStep 1592825 = 1194619) B1194619
theorem B1592927 : Blo 1060614 1592927 := bstep (se 1 (by rfl) ⟨1194695, by rfl⟩ : syracuseStep 1592927 = 2389391) B2389391
theorem B5754665 : Blo 1060614 5754665 := bstep (se 2 (by rfl) ⟨2157999, by rfl⟩ : syracuseStep 5754665 = 4315999) B4315999
theorem B1593143 : Blo 1060614 1593143 := bstep (se 1 (by rfl) ⟨1194857, by rfl⟩ : syracuseStep 1593143 = 2389715) B2389715
theorem B5754685 : Blo 1060614 5754685 := bstep (se 3 (by rfl) ⟨1079003, by rfl⟩ : syracuseStep 5754685 = 2158007) B2158007
theorem B18370525 : Blo 1060614 18370525 := bstep (se 3 (by rfl) ⟨3444473, by rfl⟩ : syracuseStep 18370525 = 6888947) B6888947
theorem B1593449 : Blo 1060614 1593449 := bstep (se 2 (by rfl) ⟨597543, by rfl⟩ : syracuseStep 1593449 = 1195087) B1195087
theorem B3592403 : Blo 1060614 3592403 := bstep (se 1 (by rfl) ⟨2694302, by rfl⟩ : syracuseStep 3592403 = 5388605) B5388605
theorem B1593767 : Blo 1060614 1593767 := bstep (se 1 (by rfl) ⟨1195325, by rfl⟩ : syracuseStep 1593767 = 2390651) B2390651
theorem B18403787 : Blo 1060614 18403787 := bstep (se 1 (by rfl) ⟨13802840, by rfl⟩ : syracuseStep 18403787 = 27605681) B27605681
theorem B2019809 : Blo 1060614 2019809 := bstep (se 2 (by rfl) ⟨757428, by rfl⟩ : syracuseStep 2019809 = 1514857) B1514857
theorem B3592673 : Blo 1060614 3592673 := bstep (se 2 (by rfl) ⟨1347252, by rfl⟩ : syracuseStep 3592673 = 2694505) B2694505
theorem B1593851 : Blo 1060614 1593851 := bstep (se 1 (by rfl) ⟨1195388, by rfl⟩ : syracuseStep 1593851 = 2390777) B2390777
theorem B9064979 : Blo 1060614 9064979 := bstep (se 1 (by rfl) ⟨6798734, by rfl⟩ : syracuseStep 9064979 = 13597469) B13597469
theorem B1593977 : Blo 1060614 1593977 := bstep (se 2 (by rfl) ⟨597741, by rfl⟩ : syracuseStep 1593977 = 1195483) B1195483
theorem B1594031 : Blo 1060614 1594031 := bstep (se 1 (by rfl) ⟨1195523, by rfl⟩ : syracuseStep 1594031 = 2391047) B2391047
theorem B1790687 : Blo 1060614 1790687 := bstep (se 1 (by rfl) ⟨1343015, by rfl⟩ : syracuseStep 1790687 = 2686031) B2686031
theorem B1594079 : Blo 1060614 1594079 := bstep (se 1 (by rfl) ⟨1195559, by rfl⟩ : syracuseStep 1594079 = 2391119) B2391119
theorem B6804425 : Blo 1060614 6804425 := bstep (se 2 (by rfl) ⟨2551659, by rfl⟩ : syracuseStep 6804425 = 5103319) B5103319
theorem B1594343 : Blo 1060614 1594343 := bstep (se 1 (by rfl) ⟨1195757, by rfl⟩ : syracuseStep 1594343 = 2391515) B2391515
theorem B1791119 : Blo 1060614 1791119 := bstep (se 1 (by rfl) ⟨1343339, by rfl⟩ : syracuseStep 1791119 = 2686679) B2686679
theorem B1594601 : Blo 1060614 1594601 := bstep (se 2 (by rfl) ⟨597975, by rfl⟩ : syracuseStep 1594601 = 1195951) B1195951
theorem B3822835 : Blo 1060614 3822835 := bstep (se 1 (by rfl) ⟨2867126, by rfl⟩ : syracuseStep 3822835 = 5734253) B5734253
theorem B1594655 : Blo 1060614 1594655 := bstep (se 1 (by rfl) ⟨1195991, by rfl⟩ : syracuseStep 1594655 = 2391983) B2391983
theorem B1791355 : Blo 1060614 1791355 := bstep (se 1 (by rfl) ⟨1343516, by rfl⟩ : syracuseStep 1791355 = 2687033) B2687033
theorem B4314491 : Blo 1060614 4314491 := bstep (se 1 (by rfl) ⟨3235868, by rfl⟩ : syracuseStep 4314491 = 6471737) B6471737
theorem B1594823 : Blo 1060614 1594823 := bstep (se 1 (by rfl) ⟨1196117, by rfl⟩ : syracuseStep 1594823 = 2392235) B2392235
theorem B4085255 : Blo 1060614 4085255 := bstep (se 1 (by rfl) ⟨3063941, by rfl⟩ : syracuseStep 4085255 = 6127883) B6127883
theorem B1595177 : Blo 1060614 1595177 := bstep (se 2 (by rfl) ⟨598191, by rfl⟩ : syracuseStep 1595177 = 1196383) B1196383
theorem B1595183 : Blo 1060614 1595183 := bstep (se 1 (by rfl) ⟨1196387, by rfl⟩ : syracuseStep 1595183 = 2392775) B2392775
theorem B4544707 : Blo 1060614 4544707 := bstep (se 1 (by rfl) ⟨3408530, by rfl⟩ : syracuseStep 4544707 = 6817061) B6817061
theorem B1595657 : Blo 1060614 1595657 := bstep (se 2 (by rfl) ⟨598371, by rfl⟩ : syracuseStep 1595657 = 1196743) B1196743
theorem B1595759 : Blo 1060614 1595759 := bstep (se 1 (by rfl) ⟨1196819, by rfl⟩ : syracuseStep 1595759 = 2393639) B2393639
theorem B2873711 : Blo 1060614 2873711 := bstep (se 1 (by rfl) ⟨2155283, by rfl⟩ : syracuseStep 2873711 = 4310567) B4310567
theorem B1595975 : Blo 1060614 1595975 := bstep (se 1 (by rfl) ⟨1196981, by rfl⟩ : syracuseStep 1595975 = 2393963) B2393963
theorem B22076011 : Blo 1060614 22076011 := bstep (se 1 (by rfl) ⟨16557008, by rfl⟩ : syracuseStep 22076011 = 33114017) B33114017
theorem B1596011 : Blo 1060614 1596011 := bstep (se 1 (by rfl) ⟨1197008, by rfl⟩ : syracuseStep 1596011 = 2394017) B2394017
theorem B5102203 : Blo 1060614 5102203 := bstep (se 1 (by rfl) ⟨3826652, by rfl⟩ : syracuseStep 5102203 = 7653305) B7653305
theorem B1792847 : Blo 1060614 1792847 := bstep (se 1 (by rfl) ⟨1344635, by rfl⟩ : syracuseStep 1792847 = 2689271) B2689271
theorem B1596239 : Blo 1060614 1596239 := bstep (se 1 (by rfl) ⟨1197179, by rfl⟩ : syracuseStep 1596239 = 2394359) B2394359
theorem B6052751 : Blo 1060614 6052751 := bstep (se 1 (by rfl) ⟨4539563, by rfl⟩ : syracuseStep 6052751 = 9079127) B9079127
theorem B19651531 : Blo 1060614 19651531 := bstep (se 1 (by rfl) ⟨14738648, by rfl⟩ : syracuseStep 19651531 = 29477297) B29477297
theorem B1596635 : Blo 1060614 1596635 := bstep (se 1 (by rfl) ⟨1197476, by rfl⟩ : syracuseStep 1596635 = 2394953) B2394953
theorem B1596809 : Blo 1060614 1596809 := bstep (se 2 (by rfl) ⟨598803, by rfl⟩ : syracuseStep 1596809 = 1197607) B1197607
theorem B1793839 : Blo 1060614 1793839 := bstep (se 1 (by rfl) ⟨1345379, by rfl⟩ : syracuseStep 1793839 = 2690759) B2690759
theorem B5103433 : Blo 1060614 5103433 := bstep (se 2 (by rfl) ⟨1913787, by rfl⟩ : syracuseStep 5103433 = 3827575) B3827575
theorem B9068395 : Blo 1060614 9068395 := bstep (se 1 (by rfl) ⟨6801296, by rfl⟩ : syracuseStep 9068395 = 13602593) B13602593
theorem B17490647 : Blo 1060614 17490647 := bstep (se 1 (by rfl) ⟨13117985, by rfl⟩ : syracuseStep 17490647 = 26235971) B26235971
theorem B4842233 : Blo 1060614 4842233 := bstep (se 2 (by rfl) ⟨1815837, by rfl⟩ : syracuseStep 4842233 = 3631675) B3631675
theorem B22995895 : Blo 1060614 22995895 := bstep (se 1 (by rfl) ⟨17246921, by rfl⟩ : syracuseStep 22995895 = 34493843) B34493843
theorem B2876555 : Blo 1060614 2876555 := bstep (se 1 (by rfl) ⟨2157416, by rfl⟩ : syracuseStep 2876555 = 4314833) B4314833
theorem B7988633 : Blo 1060614 7988633 := bstep (se 2 (by rfl) ⟨2995737, by rfl⟩ : syracuseStep 7988633 = 5991475) B5991475
theorem B12117437 : Blo 1060614 12117437 := bstep (se 3 (by rfl) ⟨2272019, by rfl⟩ : syracuseStep 12117437 = 4544039) B4544039
theorem B31057901 : Blo 1060614 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B2550025 : Blo 1060614 2550025 := bstep (se 2 (by rfl) ⟨956259, by rfl⟩ : syracuseStep 2550025 = 1912519) B1912519
theorem B1796519 : Blo 1060614 1796519 := bstep (se 1 (by rfl) ⟨1347389, by rfl⟩ : syracuseStep 1796519 = 2694779) B2694779
theorem B2386511 : Blo 1060614 2386511 := bstep (se 1 (by rfl) ⟨1789883, by rfl⟩ : syracuseStep 2386511 = 3579767) B3579767
theorem B2386655 : Blo 1060614 2386655 := bstep (se 1 (by rfl) ⟨1789991, by rfl⟩ : syracuseStep 2386655 = 3579983) B3579983
theorem B2386907 : Blo 1060614 2386907 := bstep (se 1 (by rfl) ⟨1790180, by rfl⟩ : syracuseStep 2386907 = 3580361) B3580361
theorem B10218635 : Blo 1060614 10218635 := bstep (se 1 (by rfl) ⟨7663976, by rfl⟩ : syracuseStep 10218635 = 15327953) B15327953
theorem B2387087 : Blo 1060614 2387087 := bstep (se 1 (by rfl) ⟨1790315, by rfl⟩ : syracuseStep 2387087 = 3580631) B3580631
theorem B2387177 : Blo 1060614 2387177 := bstep (se 2 (by rfl) ⟨895191, by rfl⟩ : syracuseStep 2387177 = 1790383) B1790383
theorem B2387231 : Blo 1060614 2387231 := bstep (se 1 (by rfl) ⟨1790423, by rfl⟩ : syracuseStep 2387231 = 3580847) B3580847
theorem B6810911 : Blo 1060614 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B8285501 : Blo 1060614 8285501 := bstep (se 3 (by rfl) ⟨1553531, by rfl⟩ : syracuseStep 8285501 = 3107063) B3107063
theorem B7663339 : Blo 1060614 7663339 := bstep (se 1 (by rfl) ⟨5747504, by rfl⟩ : syracuseStep 7663339 = 11495009) B11495009
theorem B2387753 : Blo 1060614 2387753 := bstep (se 2 (by rfl) ⟨895407, by rfl⟩ : syracuseStep 2387753 = 1790815) B1790815
theorem B8057393 : Blo 1060614 8057393 := bstep (se 2 (by rfl) ⟨3021522, by rfl⟩ : syracuseStep 8057393 = 6043045) B6043045
theorem B10220093 : Blo 1060614 10220093 := bstep (se 3 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 10220093 = 3832535) B3832535
theorem B4027103 : Blo 1060614 4027103 := bstep (se 1 (by rfl) ⟨3020327, by rfl⟩ : syracuseStep 4027103 = 6040655) B6040655
theorem B2454263 : Blo 1060614 2454263 := bstep (se 1 (by rfl) ⟨1840697, by rfl⟩ : syracuseStep 2454263 = 3681395) B3681395
theorem B2388815 : Blo 1060614 2388815 := bstep (se 1 (by rfl) ⟨1791611, by rfl⟩ : syracuseStep 2388815 = 3583223) B3583223
theorem B5370785 : Blo 1060614 5370785 := bstep (se 2 (by rfl) ⟨2014044, by rfl⟩ : syracuseStep 5370785 = 4028089) B4028089
theorem B2389031 : Blo 1060614 2389031 := bstep (se 1 (by rfl) ⟨1791773, by rfl⟩ : syracuseStep 2389031 = 3583547) B3583547
theorem B3634301 : Blo 1060614 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B2389211 : Blo 1060614 2389211 := bstep (se 1 (by rfl) ⟨1791908, by rfl⟩ : syracuseStep 2389211 = 3583817) B3583817
theorem B5108969 : Blo 1060614 5108969 := bstep (se 2 (by rfl) ⟨1915863, by rfl⟩ : syracuseStep 5108969 = 3831727) B3831727
theorem B2389409 : Blo 1060614 2389409 := bstep (se 2 (by rfl) ⟨896028, by rfl⟩ : syracuseStep 2389409 = 1792057) B1792057
theorem B23000921 : Blo 1060614 23000921 := bstep (se 2 (by rfl) ⟨8625345, by rfl⟩ : syracuseStep 23000921 = 17250691) B17250691
theorem B2389967 : Blo 1060614 2389967 := bstep (se 1 (by rfl) ⟨1792475, by rfl⟩ : syracuseStep 2389967 = 3584951) B3584951
theorem B2390345 : Blo 1060614 2390345 := bstep (se 2 (by rfl) ⟨896379, by rfl⟩ : syracuseStep 2390345 = 1792759) B1792759
theorem B2390363 : Blo 1060614 2390363 := bstep (se 1 (by rfl) ⟨1792772, by rfl⟩ : syracuseStep 2390363 = 3585545) B3585545
theorem B2390939 : Blo 1060614 2390939 := bstep (se 1 (by rfl) ⟨1793204, by rfl⟩ : syracuseStep 2390939 = 3586409) B3586409
theorem B2391137 : Blo 1060614 2391137 := bstep (se 2 (by rfl) ⟨896676, by rfl⟩ : syracuseStep 2391137 = 1793353) B1793353
theorem B5373215 : Blo 1060614 5373215 := bstep (se 1 (by rfl) ⟨4029911, by rfl⟩ : syracuseStep 5373215 = 8059823) B8059823
theorem B2391335 : Blo 1060614 2391335 := bstep (se 1 (by rfl) ⟨1793501, by rfl⟩ : syracuseStep 2391335 = 3587003) B3587003
theorem B1342919 : Blo 1060614 1342919 := bstep (se 1 (by rfl) ⟨1007189, by rfl⟩ : syracuseStep 1342919 = 2014379) B2014379
theorem B2555351 : Blo 1060614 2555351 := bstep (se 1 (by rfl) ⟨1916513, by rfl⟩ : syracuseStep 2555351 = 3833027) B3833027
theorem B4030033 : Blo 1060614 4030033 := bstep (se 2 (by rfl) ⟨1511262, by rfl⟩ : syracuseStep 4030033 = 3022525) B3022525
theorem B2686547 : Blo 1060614 2686547 := bstep (se 1 (by rfl) ⟨2014910, by rfl⟩ : syracuseStep 2686547 = 4029821) B4029821
theorem B1343071 : Blo 1060614 1343071 := bstep (se 1 (by rfl) ⟨1007303, by rfl⟩ : syracuseStep 1343071 = 2014607) B2014607
theorem B2391713 : Blo 1060614 2391713 := bstep (se 2 (by rfl) ⟨896892, by rfl⟩ : syracuseStep 2391713 = 1793785) B1793785
theorem B9207647 : Blo 1060614 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B4030337 : Blo 1060614 4030337 := bstep (se 2 (by rfl) ⟨1511376, by rfl⟩ : syracuseStep 4030337 = 3022753) B3022753
theorem B6061999 : Blo 1060614 6061999 := bstep (se 1 (by rfl) ⟨4546499, by rfl⟩ : syracuseStep 6061999 = 9092999) B9092999
theorem B25886735 : Blo 1060614 25886735 := bstep (se 1 (by rfl) ⟨19415051, by rfl⟩ : syracuseStep 25886735 = 38830103) B38830103
theorem B2687195 : Blo 1060614 2687195 := bstep (se 1 (by rfl) ⟨2015396, by rfl⟩ : syracuseStep 2687195 = 4030793) B4030793
theorem B1343719 : Blo 1060614 1343719 := bstep (se 1 (by rfl) ⟨1007789, by rfl⟩ : syracuseStep 1343719 = 2015579) B2015579
theorem B1868087 : Blo 1060614 1868087 := bstep (se 1 (by rfl) ⟨1401065, by rfl⟩ : syracuseStep 1868087 = 2802131) B2802131
theorem B3932603 : Blo 1060614 3932603 := bstep (se 1 (by rfl) ⟨2949452, by rfl⟩ : syracuseStep 3932603 = 5898905) B5898905
theorem B1638863 : Blo 1060614 1638863 := bstep (se 1 (by rfl) ⟨1229147, by rfl⟩ : syracuseStep 1638863 = 2458295) B2458295
theorem B2392811 : Blo 1060614 2392811 := bstep (se 1 (by rfl) ⟨1794608, by rfl⟩ : syracuseStep 2392811 = 3589217) B3589217
theorem B4031279 : Blo 1060614 4031279 := bstep (se 1 (by rfl) ⟨3023459, by rfl⟩ : syracuseStep 4031279 = 6046919) B6046919
theorem B6062957 : Blo 1060614 6062957 := bstep (se 3 (by rfl) ⟨1136804, by rfl⟩ : syracuseStep 6062957 = 2273609) B2273609
theorem B1344367 : Blo 1060614 1344367 := bstep (se 1 (by rfl) ⟨1008275, by rfl⟩ : syracuseStep 1344367 = 2016551) B2016551
theorem B2688025 : Blo 1060614 2688025 := bstep (se 2 (by rfl) ⟨1008009, by rfl⟩ : syracuseStep 2688025 = 2016019) B2016019
theorem B2688329 : Blo 1060614 2688329 := bstep (se 2 (by rfl) ⟨1008123, by rfl⟩ : syracuseStep 2688329 = 2016247) B2016247
theorem B13600133 : Blo 1060614 13600133 := bstep (se 4 (by rfl) ⟨1275012, by rfl⟩ : syracuseStep 13600133 = 2550025) B2550025
theorem B2688623 : Blo 1060614 2688623 := bstep (se 1 (by rfl) ⟨2016467, by rfl⟩ : syracuseStep 2688623 = 4032935) B4032935
theorem B2393711 : Blo 1060614 2393711 := bstep (se 1 (by rfl) ⟨1795283, by rfl⟩ : syracuseStep 2393711 = 3590567) B3590567
theorem B1345243 : Blo 1060614 1345243 := bstep (se 1 (by rfl) ⟨1008932, by rfl⟩ : syracuseStep 1345243 = 2017865) B2017865
theorem B2393819 : Blo 1060614 2393819 := bstep (se 1 (by rfl) ⟨1795364, by rfl⟩ : syracuseStep 2393819 = 3590729) B3590729
theorem B2426591 : Blo 1060614 2426591 := bstep (se 1 (by rfl) ⟨1819943, by rfl⟩ : syracuseStep 2426591 = 3639887) B3639887
theorem B517998329 : Blo 1060614 517998329 := bstep (se 2 (by rfl) ⟨194249373, by rfl⟩ : syracuseStep 517998329 = 388498747) B388498747
theorem B46598273 : Blo 1060614 46598273 := bstep (se 2 (by rfl) ⟨17474352, by rfl⟩ : syracuseStep 46598273 = 34948705) B34948705
theorem B11471057 : Blo 1060614 11471057 := bstep (se 2 (by rfl) ⟨4301646, by rfl⟩ : syracuseStep 11471057 = 8603293) B8603293
theorem B41388565 : Blo 1060614 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B3836443 : Blo 1060614 3836443 := bstep (se 1 (by rfl) ⟨2877332, by rfl⟩ : syracuseStep 3836443 = 5754665) B5754665
theorem B5376617 : Blo 1060614 5376617 := bstep (se 2 (by rfl) ⟨2016231, by rfl⟩ : syracuseStep 5376617 = 4032463) B4032463
theorem B10226321 : Blo 1060614 10226321 := bstep (se 2 (by rfl) ⟨3834870, by rfl⟩ : syracuseStep 10226321 = 7669741) B7669741
theorem B6818519 : Blo 1060614 6818519 := bstep (se 1 (by rfl) ⟨5113889, by rfl⟩ : syracuseStep 6818519 = 10227779) B10227779
theorem B2394935 : Blo 1060614 2394935 := bstep (se 1 (by rfl) ⟨1796201, by rfl⟩ : syracuseStep 2394935 = 3592403) B3592403
theorem B1346539 : Blo 1060614 1346539 := bstep (se 1 (by rfl) ⟨1009904, by rfl⟩ : syracuseStep 1346539 = 2019809) B2019809
theorem B2395115 : Blo 1060614 2395115 := bstep (se 1 (by rfl) ⟨1796336, by rfl⟩ : syracuseStep 2395115 = 3592673) B3592673
theorem B2297339 : Blo 1060614 2297339 := bstep (se 1 (by rfl) ⟨1723004, by rfl⟩ : syracuseStep 2297339 = 3446009) B3446009
theorem B2723503 : Blo 1060614 2723503 := bstep (se 1 (by rfl) ⟨2042627, by rfl⟩ : syracuseStep 2723503 = 4085255) B4085255
theorem B5181305 : Blo 1060614 5181305 := bstep (se 2 (by rfl) ⟨1942989, by rfl⟩ : syracuseStep 5181305 = 3885979) B3885979
theorem B5377913 : Blo 1060614 5377913 := bstep (se 2 (by rfl) ⟨2016717, by rfl⟩ : syracuseStep 5377913 = 4033435) B4033435
theorem B8622233 : Blo 1060614 8622233 := bstep (se 2 (by rfl) ⟨3233337, by rfl⟩ : syracuseStep 8622233 = 6466675) B6466675
theorem B4035167 : Blo 1060614 4035167 := bstep (se 1 (by rfl) ⟨3026375, by rfl⟩ : syracuseStep 4035167 = 6052751) B6052751
theorem B7672913 : Blo 1060614 7672913 := bstep (se 2 (by rfl) ⟨2877342, by rfl⟩ : syracuseStep 7672913 = 5754685) B5754685
theorem B14554403 : Blo 1060614 14554403 := bstep (se 1 (by rfl) ⟨10915802, by rfl⟩ : syracuseStep 14554403 = 21831605) B21831605
theorem B19928357 : Blo 1060614 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B4593419 : Blo 1060614 4593419 := bstep (se 1 (by rfl) ⟨3445064, by rfl⟩ : syracuseStep 4593419 = 6890129) B6890129
theorem B1513279 : Blo 1060614 1513279 := bstep (se 1 (by rfl) ⟨1134959, by rfl⟩ : syracuseStep 1513279 = 2269919) B2269919
theorem B2725769 : Blo 1060614 2725769 := bstep (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) B2044327
theorem B1940105 : Blo 1060614 1940105 := bstep (se 2 (by rfl) ⟨727539, by rfl⟩ : syracuseStep 1940105 = 1455079) B1455079
theorem B1514543 : Blo 1060614 1514543 := bstep (se 1 (by rfl) ⟨1135907, by rfl⟩ : syracuseStep 1514543 = 2271815) B2271815
theorem B12917879 : Blo 1060614 12917879 := bstep (se 1 (by rfl) ⟨9688409, by rfl⟩ : syracuseStep 12917879 = 19376819) B19376819
theorem B3022343 : Blo 1060614 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B3580523 : Blo 1060614 3580523 := bstep (se 1 (by rfl) ⟨2685392, by rfl⟩ : syracuseStep 3580523 = 5370785) B5370785
theorem B29434681 : Blo 1060614 29434681 := bstep (se 2 (by rfl) ⟨11038005, by rfl⟩ : syracuseStep 29434681 = 22076011) B22076011
theorem B22094669 : Blo 1060614 22094669 := bstep (se 3 (by rfl) ⟨4142750, by rfl⟩ : syracuseStep 22094669 = 8285501) B8285501
theorem B6562939 : Blo 1060614 6562939 := bstep (se 1 (by rfl) ⟨4922204, by rfl⟩ : syracuseStep 6562939 = 9844409) B9844409
theorem B3581117 : Blo 1060614 3581117 := bstep (se 3 (by rfl) ⟨671459, by rfl⟩ : syracuseStep 3581117 = 1342919) B1342919
theorem B3582143 : Blo 1060614 3582143 := bstep (se 1 (by rfl) ⟨2686607, by rfl⟩ : syracuseStep 3582143 = 5373215) B5373215
theorem B6138431 : Blo 1060614 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B8072459 : Blo 1060614 8072459 := bstep (se 1 (by rfl) ⟨6054344, by rfl⟩ : syracuseStep 8072459 = 12108689) B12108689
theorem B2272943 : Blo 1060614 2272943 := bstep (se 1 (by rfl) ⟨1704707, by rfl⟩ : syracuseStep 2272943 = 3409415) B3409415
theorem B3583763 : Blo 1060614 3583763 := bstep (se 1 (by rfl) ⟨2687822, by rfl⟩ : syracuseStep 3583763 = 5375645) B5375645
theorem B6041405 : Blo 1060614 6041405 := bstep (se 3 (by rfl) ⟨1132763, by rfl⟩ : syracuseStep 6041405 = 2265527) B2265527
theorem B1060679 : Blo 1060614 1060679 := bstep (se 1 (by rfl) ⟨795509, by rfl⟩ : syracuseStep 1060679 = 1591019) B1591019
theorem B2043803 : Blo 1060614 2043803 := bstep (se 1 (by rfl) ⟨1532852, by rfl⟩ : syracuseStep 2043803 = 3065705) B3065705
theorem B6467501 : Blo 1060614 6467501 := bstep (se 3 (by rfl) ⟨1212656, by rfl⟩ : syracuseStep 6467501 = 2425313) B2425313
theorem B1060831 : Blo 1060614 1060831 := bstep (se 1 (by rfl) ⟨795623, by rfl⟩ : syracuseStep 1060831 = 1591247) B1591247
theorem B6041587 : Blo 1060614 6041587 := bstep (se 1 (by rfl) ⟨4531190, by rfl⟩ : syracuseStep 6041587 = 9062381) B9062381
theorem B1061095 : Blo 1060614 1061095 := bstep (se 1 (by rfl) ⟨795821, by rfl⟩ : syracuseStep 1061095 = 1591643) B1591643
theorem B1061247 : Blo 1060614 1061247 := bstep (se 1 (by rfl) ⟨795935, by rfl⟩ : syracuseStep 1061247 = 1591871) B1591871
theorem B7647655 : Blo 1060614 7647655 := bstep (se 1 (by rfl) ⟨5735741, by rfl⟩ : syracuseStep 7647655 = 11471483) B11471483
theorem B1061327 : Blo 1060614 1061327 := bstep (se 1 (by rfl) ⟨795995, by rfl⟩ : syracuseStep 1061327 = 1591991) B1591991
theorem B1061479 : Blo 1060614 1061479 := bstep (se 1 (by rfl) ⟨796109, by rfl⟩ : syracuseStep 1061479 = 1592219) B1592219
theorem B3584627 : Blo 1060614 3584627 := bstep (se 1 (by rfl) ⟨2688470, by rfl⟩ : syracuseStep 3584627 = 5376941) B5376941
theorem B3027719 : Blo 1060614 3027719 := bstep (se 1 (by rfl) ⟨2270789, by rfl⟩ : syracuseStep 3027719 = 4541579) B4541579
theorem B1061743 : Blo 1060614 1061743 := bstep (se 1 (by rfl) ⟨796307, by rfl⟩ : syracuseStep 1061743 = 1592615) B1592615
theorem B3584897 : Blo 1060614 3584897 := bstep (se 2 (by rfl) ⟨1344336, by rfl⟩ : syracuseStep 3584897 = 2688673) B2688673
theorem B1061799 : Blo 1060614 1061799 := bstep (se 1 (by rfl) ⟨796349, by rfl⟩ : syracuseStep 1061799 = 1592699) B1592699
theorem B1061883 : Blo 1060614 1061883 := bstep (se 1 (by rfl) ⟨796412, by rfl⟩ : syracuseStep 1061883 = 1592825) B1592825
theorem B3453961 : Blo 1060614 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B1061951 : Blo 1060614 1061951 := bstep (se 1 (by rfl) ⟨796463, by rfl⟩ : syracuseStep 1061951 = 1592927) B1592927
theorem B1062095 : Blo 1060614 1062095 := bstep (se 1 (by rfl) ⟨796571, by rfl⟩ : syracuseStep 1062095 = 1593143) B1593143
theorem B1062299 : Blo 1060614 1062299 := bstep (se 1 (by rfl) ⟨796724, by rfl⟩ : syracuseStep 1062299 = 1593449) B1593449
theorem B1062511 : Blo 1060614 1062511 := bstep (se 1 (by rfl) ⟨796883, by rfl⟩ : syracuseStep 1062511 = 1593767) B1593767
theorem B12269191 : Blo 1060614 12269191 := bstep (se 1 (by rfl) ⟨9201893, by rfl⟩ : syracuseStep 12269191 = 18403787) B18403787
theorem B1062567 : Blo 1060614 1062567 := bstep (se 1 (by rfl) ⟨796925, by rfl⟩ : syracuseStep 1062567 = 1593851) B1593851
theorem B3585707 : Blo 1060614 3585707 := bstep (se 1 (by rfl) ⟨2689280, by rfl⟩ : syracuseStep 3585707 = 5378561) B5378561
theorem B6043319 : Blo 1060614 6043319 := bstep (se 1 (by rfl) ⟨4532489, by rfl⟩ : syracuseStep 6043319 = 9064979) B9064979
theorem B1062651 : Blo 1060614 1062651 := bstep (se 1 (by rfl) ⟨796988, by rfl⟩ : syracuseStep 1062651 = 1593977) B1593977
theorem B1062687 : Blo 1060614 1062687 := bstep (se 1 (by rfl) ⟨797015, by rfl⟩ : syracuseStep 1062687 = 1594031) B1594031
theorem B1193791 : Blo 1060614 1193791 := bstep (se 1 (by rfl) ⟨895343, by rfl⟩ : syracuseStep 1193791 = 1790687) B1790687
theorem B1062719 : Blo 1060614 1062719 := bstep (se 1 (by rfl) ⟨797039, by rfl⟩ : syracuseStep 1062719 = 1594079) B1594079
theorem B4536283 : Blo 1060614 4536283 := bstep (se 1 (by rfl) ⟨3402212, by rfl⟩ : syracuseStep 4536283 = 6804425) B6804425
theorem B3586031 : Blo 1060614 3586031 := bstep (se 1 (by rfl) ⟨2689523, by rfl⟩ : syracuseStep 3586031 = 5379047) B5379047
theorem B1062895 : Blo 1060614 1062895 := bstep (se 1 (by rfl) ⟨797171, by rfl⟩ : syracuseStep 1062895 = 1594343) B1594343
theorem B3028985 : Blo 1060614 3028985 := bstep (se 2 (by rfl) ⟨1135869, by rfl⟩ : syracuseStep 3028985 = 2271739) B2271739
theorem B5388281 : Blo 1060614 5388281 := bstep (se 2 (by rfl) ⟨2020605, by rfl⟩ : syracuseStep 5388281 = 4041211) B4041211
theorem B1194079 : Blo 1060614 1194079 := bstep (se 1 (by rfl) ⟨895559, by rfl⟩ : syracuseStep 1194079 = 1791119) B1791119
theorem B1063067 : Blo 1060614 1063067 := bstep (se 1 (by rfl) ⟨797300, by rfl⟩ : syracuseStep 1063067 = 1594601) B1594601
theorem B1063103 : Blo 1060614 1063103 := bstep (se 1 (by rfl) ⟨797327, by rfl⟩ : syracuseStep 1063103 = 1594655) B1594655
theorem B3586247 : Blo 1060614 3586247 := bstep (se 1 (by rfl) ⟨2689685, by rfl⟩ : syracuseStep 3586247 = 5379371) B5379371
theorem B1063215 : Blo 1060614 1063215 := bstep (se 1 (by rfl) ⟨797411, by rfl⟩ : syracuseStep 1063215 = 1594823) B1594823
theorem B14531075 : Blo 1060614 14531075 := bstep (se 1 (by rfl) ⟨10898306, by rfl⟩ : syracuseStep 14531075 = 21796613) B21796613
theorem B1063451 : Blo 1060614 1063451 := bstep (se 1 (by rfl) ⟨797588, by rfl⟩ : syracuseStep 1063451 = 1595177) B1595177
theorem B1063455 : Blo 1060614 1063455 := bstep (se 1 (by rfl) ⟨797591, by rfl⟩ : syracuseStep 1063455 = 1595183) B1595183
theorem B3586895 : Blo 1060614 3586895 := bstep (se 1 (by rfl) ⟨2690171, by rfl⟩ : syracuseStep 3586895 = 5380343) B5380343
theorem B1063771 : Blo 1060614 1063771 := bstep (se 1 (by rfl) ⟨797828, by rfl⟩ : syracuseStep 1063771 = 1595657) B1595657
theorem B1915807 : Blo 1060614 1915807 := bstep (se 1 (by rfl) ⟨1436855, by rfl⟩ : syracuseStep 1915807 = 2873711) B2873711
theorem B1063839 : Blo 1060614 1063839 := bstep (se 1 (by rfl) ⟨797879, by rfl⟩ : syracuseStep 1063839 = 1595759) B1595759
theorem B2014159 : Blo 1060614 2014159 := bstep (se 1 (by rfl) ⟨1510619, by rfl⟩ : syracuseStep 2014159 = 3021239) B3021239
theorem B1063983 : Blo 1060614 1063983 := bstep (se 1 (by rfl) ⟨797987, by rfl⟩ : syracuseStep 1063983 = 1595975) B1595975
theorem B1064007 : Blo 1060614 1064007 := bstep (se 1 (by rfl) ⟨798005, by rfl⟩ : syracuseStep 1064007 = 1596011) B1596011
theorem B3587219 : Blo 1060614 3587219 := bstep (se 1 (by rfl) ⟨2690414, by rfl⟩ : syracuseStep 3587219 = 5380829) B5380829
theorem B1195231 : Blo 1060614 1195231 := bstep (se 1 (by rfl) ⟨896423, by rfl⟩ : syracuseStep 1195231 = 1792847) B1792847
theorem B1064159 : Blo 1060614 1064159 := bstep (se 1 (by rfl) ⟨798119, by rfl⟩ : syracuseStep 1064159 = 1596239) B1596239
theorem B5389577 : Blo 1060614 5389577 := bstep (se 2 (by rfl) ⟨2021091, by rfl⟩ : syracuseStep 5389577 = 4042183) B4042183
theorem B3587489 : Blo 1060614 3587489 := bstep (se 2 (by rfl) ⟨1345308, by rfl⟩ : syracuseStep 3587489 = 2690617) B2690617
theorem B1064423 : Blo 1060614 1064423 := bstep (se 1 (by rfl) ⟨798317, by rfl⟩ : syracuseStep 1064423 = 1596635) B1596635
theorem B1064539 : Blo 1060614 1064539 := bstep (se 1 (by rfl) ⟨798404, by rfl⟩ : syracuseStep 1064539 = 1596809) B1596809
theorem B2015047 : Blo 1060614 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B3588029 : Blo 1060614 3588029 := bstep (se 3 (by rfl) ⟨672755, by rfl⟩ : syracuseStep 3588029 = 1345511) B1345511
theorem B24494033 : Blo 1060614 24494033 := bstep (se 2 (by rfl) ⟨9185262, by rfl⟩ : syracuseStep 24494033 = 18370525) B18370525
theorem B7651691 : Blo 1060614 7651691 := bstep (se 1 (by rfl) ⟨5738768, by rfl⟩ : syracuseStep 7651691 = 11477537) B11477537
theorem B3228155 : Blo 1060614 3228155 := bstep (se 1 (by rfl) ⟨2421116, by rfl⟩ : syracuseStep 3228155 = 4842233) B4842233
theorem B1917703 : Blo 1060614 1917703 := bstep (se 1 (by rfl) ⟨1438277, by rfl⟩ : syracuseStep 1917703 = 2876555) B2876555
theorem B5325755 : Blo 1060614 5325755 := bstep (se 1 (by rfl) ⟨3994316, by rfl⟩ : syracuseStep 5325755 = 7988633) B7988633
theorem B8078291 : Blo 1060614 8078291 := bstep (se 1 (by rfl) ⟨6058718, by rfl⟩ : syracuseStep 8078291 = 12117437) B12117437
theorem B6800375 : Blo 1060614 6800375 := bstep (se 1 (by rfl) ⟨5100281, by rfl⟩ : syracuseStep 6800375 = 10200563) B10200563
theorem B1197679 : Blo 1060614 1197679 := bstep (se 1 (by rfl) ⟨898259, by rfl⟩ : syracuseStep 1197679 = 1796519) B1796519
theorem B5097113 : Blo 1060614 5097113 := bstep (se 2 (by rfl) ⟨1911417, by rfl⟩ : syracuseStep 5097113 = 3822835) B3822835
theorem B1591007 : Blo 1060614 1591007 := bstep (se 1 (by rfl) ⟨1193255, by rfl⟩ : syracuseStep 1591007 = 2386511) B2386511
theorem B2016991 : Blo 1060614 2016991 := bstep (se 1 (by rfl) ⟨1512743, by rfl⟩ : syracuseStep 2016991 = 3025487) B3025487
theorem B3589919 : Blo 1060614 3589919 := bstep (se 1 (by rfl) ⟨2692439, by rfl⟩ : syracuseStep 3589919 = 5384879) B5384879
theorem B1591103 : Blo 1060614 1591103 := bstep (se 1 (by rfl) ⟨1193327, by rfl⟩ : syracuseStep 1591103 = 2386655) B2386655
theorem B1591271 : Blo 1060614 1591271 := bstep (se 1 (by rfl) ⟨1193453, by rfl⟩ : syracuseStep 1591271 = 2386907) B2386907
theorem B3590135 : Blo 1060614 3590135 := bstep (se 1 (by rfl) ⟨2692601, by rfl⟩ : syracuseStep 3590135 = 5385203) B5385203
theorem B1591289 : Blo 1060614 1591289 := bstep (se 2 (by rfl) ⟨596733, by rfl⟩ : syracuseStep 1591289 = 1193467) B1193467
theorem B1591391 : Blo 1060614 1591391 := bstep (se 1 (by rfl) ⟨1193543, by rfl⟩ : syracuseStep 1591391 = 2387087) B2387087
theorem B1591451 : Blo 1060614 1591451 := bstep (se 1 (by rfl) ⟨1193588, by rfl⟩ : syracuseStep 1591451 = 2387177) B2387177
theorem B1591487 : Blo 1060614 1591487 := bstep (se 1 (by rfl) ⟨1193615, by rfl⟩ : syracuseStep 1591487 = 2387231) B2387231
theorem B4540607 : Blo 1060614 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B1591529 : Blo 1060614 1591529 := bstep (se 2 (by rfl) ⟨596823, by rfl⟩ : syracuseStep 1591529 = 1193647) B1193647
theorem B1591835 : Blo 1060614 1591835 := bstep (se 1 (by rfl) ⟨1193876, by rfl⟩ : syracuseStep 1591835 = 2387753) B2387753
theorem B1591913 : Blo 1060614 1591913 := bstep (se 2 (by rfl) ⟨596967, by rfl⟩ : syracuseStep 1591913 = 1193935) B1193935
theorem B3590999 : Blo 1060614 3590999 := bstep (se 1 (by rfl) ⟨2693249, by rfl⟩ : syracuseStep 3590999 = 5386499) B5386499
theorem B2018351 : Blo 1060614 2018351 := bstep (se 1 (by rfl) ⟨1513763, by rfl⟩ : syracuseStep 2018351 = 3027527) B3027527
theorem B3591215 : Blo 1060614 3591215 := bstep (se 1 (by rfl) ⟨2693411, by rfl⟩ : syracuseStep 3591215 = 5386823) B5386823
theorem B1592441 : Blo 1060614 1592441 := bstep (se 2 (by rfl) ⟨597165, by rfl⟩ : syracuseStep 1592441 = 1194331) B1194331
theorem B1592543 : Blo 1060614 1592543 := bstep (se 1 (by rfl) ⟨1194407, by rfl⟩ : syracuseStep 1592543 = 2388815) B2388815
theorem B1592585 : Blo 1060614 1592585 := bstep (se 2 (by rfl) ⟨597219, by rfl⟩ : syracuseStep 1592585 = 1194439) B1194439
theorem B1592687 : Blo 1060614 1592687 := bstep (se 1 (by rfl) ⟨1194515, by rfl⟩ : syracuseStep 1592687 = 2389031) B2389031
theorem B3591593 : Blo 1060614 3591593 := bstep (se 2 (by rfl) ⟨1346847, by rfl⟩ : syracuseStep 3591593 = 2693695) B2693695
theorem B1592807 : Blo 1060614 1592807 := bstep (se 1 (by rfl) ⟨1194605, by rfl⟩ : syracuseStep 1592807 = 2389211) B2389211
theorem B6802937 : Blo 1060614 6802937 := bstep (se 2 (by rfl) ⟨2551101, by rfl⟩ : syracuseStep 6802937 = 5102203) B5102203
theorem B1592939 : Blo 1060614 1592939 := bstep (se 1 (by rfl) ⟨1194704, by rfl⟩ : syracuseStep 1592939 = 2389409) B2389409
theorem B1593065 : Blo 1060614 1593065 := bstep (se 2 (by rfl) ⟨597399, by rfl⟩ : syracuseStep 1593065 = 1194799) B1194799
theorem B1593209 : Blo 1060614 1593209 := bstep (se 2 (by rfl) ⟨597453, by rfl⟩ : syracuseStep 1593209 = 1194907) B1194907
theorem B3592079 : Blo 1060614 3592079 := bstep (se 1 (by rfl) ⟨2694059, by rfl⟩ : syracuseStep 3592079 = 5388119) B5388119
theorem B6803347 : Blo 1060614 6803347 := bstep (se 1 (by rfl) ⟨5102510, by rfl⟩ : syracuseStep 6803347 = 10205021) B10205021
theorem B26202041 : Blo 1060614 26202041 := bstep (se 2 (by rfl) ⟨9825765, by rfl⟩ : syracuseStep 26202041 = 19651531) B19651531
theorem B1593311 : Blo 1060614 1593311 := bstep (se 1 (by rfl) ⟨1194983, by rfl⟩ : syracuseStep 1593311 = 2389967) B2389967
theorem B1593563 : Blo 1060614 1593563 := bstep (se 1 (by rfl) ⟨1195172, by rfl⟩ : syracuseStep 1593563 = 2390345) B2390345
theorem B1593575 : Blo 1060614 1593575 := bstep (se 1 (by rfl) ⟨1195181, by rfl⟩ : syracuseStep 1593575 = 2390363) B2390363
theorem B3592457 : Blo 1060614 3592457 := bstep (se 2 (by rfl) ⟨1347171, by rfl⟩ : syracuseStep 3592457 = 2694343) B2694343
theorem B1593737 : Blo 1060614 1593737 := bstep (se 2 (by rfl) ⟨597651, by rfl⟩ : syracuseStep 1593737 = 1195303) B1195303
theorem B1593833 : Blo 1060614 1593833 := bstep (se 2 (by rfl) ⟨597687, by rfl⟩ : syracuseStep 1593833 = 1195375) B1195375
theorem B1593959 : Blo 1060614 1593959 := bstep (se 1 (by rfl) ⟨1195469, by rfl⟩ : syracuseStep 1593959 = 2390939) B2390939
theorem B1594091 : Blo 1060614 1594091 := bstep (se 1 (by rfl) ⟨1195568, by rfl⟩ : syracuseStep 1594091 = 2391137) B2391137
theorem B1594121 : Blo 1060614 1594121 := bstep (se 2 (by rfl) ⟨597795, by rfl⟩ : syracuseStep 1594121 = 1195591) B1195591
theorem B1790761 : Blo 1060614 1790761 := bstep (se 2 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 1790761 = 1343071) B1343071
theorem B1594223 : Blo 1060614 1594223 := bstep (se 1 (by rfl) ⟨1195667, by rfl⟩ : syracuseStep 1594223 = 2391335) B2391335
theorem B1791031 : Blo 1060614 1791031 := bstep (se 1 (by rfl) ⟨1343273, by rfl⟩ : syracuseStep 1791031 = 2686547) B2686547
theorem B6804577 : Blo 1060614 6804577 := bstep (se 2 (by rfl) ⟨2551716, by rfl⟩ : syracuseStep 6804577 = 5103433) B5103433
theorem B1594475 : Blo 1060614 1594475 := bstep (se 1 (by rfl) ⟨1195856, by rfl⟩ : syracuseStep 1594475 = 2391713) B2391713
theorem B8082665 : Blo 1060614 8082665 := bstep (se 2 (by rfl) ⟨3030999, by rfl⟩ : syracuseStep 8082665 = 6061999) B6061999
theorem B1594715 : Blo 1060614 1594715 := bstep (se 1 (by rfl) ⟨1196036, by rfl⟩ : syracuseStep 1594715 = 2392073) B2392073
theorem B1594991 : Blo 1060614 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B1595063 : Blo 1060614 1595063 := bstep (se 1 (by rfl) ⟨1196297, by rfl⟩ : syracuseStep 1595063 = 2392595) B2392595
theorem B1595099 : Blo 1060614 1595099 := bstep (se 1 (by rfl) ⟨1196324, by rfl⟩ : syracuseStep 1595099 = 2392649) B2392649
theorem B1595273 : Blo 1060614 1595273 := bstep (se 2 (by rfl) ⟨598227, by rfl⟩ : syracuseStep 1595273 = 1196455) B1196455
theorem B1791983 : Blo 1060614 1791983 := bstep (se 1 (by rfl) ⟨1343987, by rfl⟩ : syracuseStep 1791983 = 2687975) B2687975
theorem B1595375 : Blo 1060614 1595375 := bstep (se 1 (by rfl) ⟨1196531, by rfl⟩ : syracuseStep 1595375 = 2393063) B2393063
theorem B1595627 : Blo 1060614 1595627 := bstep (se 1 (by rfl) ⟨1196720, by rfl⟩ : syracuseStep 1595627 = 2393441) B2393441
theorem B1595687 : Blo 1060614 1595687 := bstep (se 1 (by rfl) ⟨1196765, by rfl⟩ : syracuseStep 1595687 = 2393531) B2393531
theorem B8608123 : Blo 1060614 8608123 := bstep (se 1 (by rfl) ⟨6456092, by rfl⟩ : syracuseStep 8608123 = 12912185) B12912185
theorem B1595771 : Blo 1060614 1595771 := bstep (se 1 (by rfl) ⟨1196828, by rfl⟩ : syracuseStep 1595771 = 2393657) B2393657
theorem B1792543 : Blo 1060614 1792543 := bstep (se 1 (by rfl) ⟨1344407, by rfl⟩ : syracuseStep 1792543 = 2688815) B2688815
theorem B30661193 : Blo 1060614 30661193 := bstep (se 2 (by rfl) ⟨11497947, by rfl⟩ : syracuseStep 30661193 = 22995895) B22995895
theorem B12114521 : Blo 1060614 12114521 := bstep (se 2 (by rfl) ⟨4542945, by rfl⟩ : syracuseStep 12114521 = 9085891) B9085891
theorem B1596041 : Blo 1060614 1596041 := bstep (se 2 (by rfl) ⟨598515, by rfl⟩ : syracuseStep 1596041 = 1197031) B1197031
theorem B1596215 : Blo 1060614 1596215 := bstep (se 1 (by rfl) ⟨1197161, by rfl⟩ : syracuseStep 1596215 = 2394323) B2394323
theorem B1596251 : Blo 1060614 1596251 := bstep (se 1 (by rfl) ⟨1197188, by rfl⟩ : syracuseStep 1596251 = 2394377) B2394377
theorem B1792975 : Blo 1060614 1792975 := bstep (se 1 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 1792975 = 2689463) B2689463
theorem B1596395 : Blo 1060614 1596395 := bstep (se 1 (by rfl) ⟨1197296, by rfl⟩ : syracuseStep 1596395 = 2394593) B2394593
theorem B1596599 : Blo 1060614 1596599 := bstep (se 1 (by rfl) ⟨1197449, by rfl⟩ : syracuseStep 1596599 = 2394899) B2394899
theorem B4545953 : Blo 1060614 4545953 := bstep (se 2 (by rfl) ⟨1704732, by rfl⟩ : syracuseStep 4545953 = 3409465) B3409465
theorem B2874791 : Blo 1060614 2874791 := bstep (se 1 (by rfl) ⟨2156093, by rfl⟩ : syracuseStep 2874791 = 4312187) B4312187
theorem B1596839 : Blo 1060614 1596839 := bstep (se 1 (by rfl) ⟨1197629, by rfl⟩ : syracuseStep 1596839 = 2395259) B2395259
theorem B1793711 : Blo 1060614 1793711 := bstep (se 1 (by rfl) ⟨1345283, by rfl⟩ : syracuseStep 1793711 = 2690567) B2690567
theorem B1793947 : Blo 1060614 1793947 := bstep (se 1 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 1793947 = 2690921) B2690921
theorem B1794359 : Blo 1060614 1794359 := bstep (se 1 (by rfl) ⟨1345769, by rfl⟩ : syracuseStep 1794359 = 2691539) B2691539
theorem B9691469 : Blo 1060614 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B65462737 : Blo 1060614 65462737 := bstep (se 2 (by rfl) ⟨24548526, by rfl⟩ : syracuseStep 65462737 = 49097053) B49097053
theorem B3629843 : Blo 1060614 3629843 := bstep (se 1 (by rfl) ⟨2722382, by rfl⟩ : syracuseStep 3629843 = 5444765) B5444765
theorem B2876327 : Blo 1060614 2876327 := bstep (se 1 (by rfl) ⟨2157245, by rfl⟩ : syracuseStep 2876327 = 4314491) B4314491
theorem B1795135 : Blo 1060614 1795135 := bstep (se 1 (by rfl) ⟨1346351, by rfl⟩ : syracuseStep 1795135 = 2692703) B2692703
theorem B9069731 : Blo 1060614 9069731 := bstep (se 1 (by rfl) ⟨6802298, by rfl⟩ : syracuseStep 9069731 = 13604597) B13604597
theorem B6055235 : Blo 1060614 6055235 := bstep (se 1 (by rfl) ⟨4541426, by rfl⟩ : syracuseStep 6055235 = 9082853) B9082853
theorem B2549065 : Blo 1060614 2549065 := bstep (se 2 (by rfl) ⟨955899, by rfl⟩ : syracuseStep 2549065 = 1911799) B1911799
theorem B3106219 : Blo 1060614 3106219 := bstep (se 1 (by rfl) ⟨2329664, by rfl⟩ : syracuseStep 3106219 = 4659329) B4659329
theorem B1795655 : Blo 1060614 1795655 := bstep (se 1 (by rfl) ⟨1346741, by rfl⟩ : syracuseStep 1795655 = 2693483) B2693483
theorem B6907577 : Blo 1060614 6907577 := bstep (se 2 (by rfl) ⟨2590341, by rfl⟩ : syracuseStep 6907577 = 5180683) B5180683
theorem B1795871 : Blo 1060614 1795871 := bstep (se 1 (by rfl) ⟨1346903, by rfl⟩ : syracuseStep 1795871 = 2693807) B2693807
theorem B1796087 : Blo 1060614 1796087 := bstep (se 1 (by rfl) ⟨1347065, by rfl⟩ : syracuseStep 1796087 = 2694131) B2694131
theorem B73492609 : Blo 1060614 73492609 := bstep (se 2 (by rfl) ⟨27559728, by rfl⟩ : syracuseStep 73492609 = 55119457) B55119457
theorem B10217785 : Blo 1060614 10217785 := bstep (se 2 (by rfl) ⟨3831669, by rfl⟩ : syracuseStep 10217785 = 7663339) B7663339
theorem B2386439 : Blo 1060614 2386439 := bstep (se 1 (by rfl) ⟨1789829, by rfl⟩ : syracuseStep 2386439 = 3579659) B3579659
theorem B2386619 : Blo 1060614 2386619 := bstep (se 1 (by rfl) ⟨1789964, by rfl⟩ : syracuseStep 2386619 = 3579929) B3579929
theorem B15297335 : Blo 1060614 15297335 := bstep (se 1 (by rfl) ⟨11473001, by rfl⟩ : syracuseStep 15297335 = 22946003) B22946003
theorem B3501191 : Blo 1060614 3501191 := bstep (se 1 (by rfl) ⟨2625893, by rfl⟩ : syracuseStep 3501191 = 5251787) B5251787
theorem B11660431 : Blo 1060614 11660431 := bstep (se 1 (by rfl) ⟨8745323, by rfl⟩ : syracuseStep 11660431 = 17490647) B17490647
theorem B3828959 : Blo 1060614 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B2387447 : Blo 1060614 2387447 := bstep (se 1 (by rfl) ⟨1790585, by rfl⟩ : syracuseStep 2387447 = 3581171) B3581171
theorem B2387519 : Blo 1060614 2387519 := bstep (se 1 (by rfl) ⟨1790639, by rfl⟩ : syracuseStep 2387519 = 3581279) B3581279
theorem B20705267 : Blo 1060614 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B8745083 : Blo 1060614 8745083 := bstep (se 1 (by rfl) ⟨6558812, by rfl⟩ : syracuseStep 8745083 = 13117625) B13117625
theorem B7270793 : Blo 1060614 7270793 := bstep (se 2 (by rfl) ⟨2726547, by rfl⟩ : syracuseStep 7270793 = 5453095) B5453095
theorem B2388473 : Blo 1060614 2388473 := bstep (se 2 (by rfl) ⟨895677, by rfl⟩ : syracuseStep 2388473 = 1791355) B1791355
theorem B3830287 : Blo 1060614 3830287 := bstep (se 1 (by rfl) ⟨2872715, by rfl⟩ : syracuseStep 3830287 = 5745431) B5745431
theorem B2388563 : Blo 1060614 2388563 := bstep (se 1 (by rfl) ⟨1791422, by rfl⟩ : syracuseStep 2388563 = 3582845) B3582845
theorem B2388743 : Blo 1060614 2388743 := bstep (se 1 (by rfl) ⟨1791557, by rfl⟩ : syracuseStep 2388743 = 3583115) B3583115
theorem B6812423 : Blo 1060614 6812423 := bstep (se 1 (by rfl) ⟨5109317, by rfl⟩ : syracuseStep 6812423 = 10218635) B10218635
theorem B20739629 : Blo 1060614 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B6059609 : Blo 1060614 6059609 := bstep (se 2 (by rfl) ⟨2272353, by rfl⟩ : syracuseStep 6059609 = 4544707) B4544707
theorem B18904709 : Blo 1060614 18904709 := bstep (se 4 (by rfl) ⟨1772316, by rfl⟩ : syracuseStep 18904709 = 3544633) B3544633
theorem B5371595 : Blo 1060614 5371595 := bstep (se 1 (by rfl) ⟨4028696, by rfl⟩ : syracuseStep 5371595 = 8057393) B8057393
theorem B6813395 : Blo 1060614 6813395 := bstep (se 1 (by rfl) ⟨5110046, by rfl⟩ : syracuseStep 6813395 = 10220093) B10220093
theorem B2684735 : Blo 1060614 2684735 := bstep (se 1 (by rfl) ⟨2013551, by rfl⟩ : syracuseStep 2684735 = 4027103) B4027103
theorem B2389823 : Blo 1060614 2389823 := bstep (se 1 (by rfl) ⟨1792367, by rfl⟩ : syracuseStep 2389823 = 3584735) B3584735
theorem B1636175 : Blo 1060614 1636175 := bstep (se 1 (by rfl) ⟨1227131, by rfl⟩ : syracuseStep 1636175 = 2454263) B2454263
theorem B2390111 : Blo 1060614 2390111 := bstep (se 1 (by rfl) ⟨1792583, by rfl⟩ : syracuseStep 2390111 = 3585167) B3585167
theorem B3405979 : Blo 1060614 3405979 := bstep (se 1 (by rfl) ⟨2554484, by rfl⟩ : syracuseStep 3405979 = 5108969) B5108969
theorem B2685089 : Blo 1060614 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B15333947 : Blo 1060614 15333947 := bstep (se 1 (by rfl) ⟨11500460, by rfl⟩ : syracuseStep 15333947 = 23000921) B23000921
theorem B2390867 : Blo 1060614 2390867 := bstep (se 1 (by rfl) ⟨1793150, by rfl⟩ : syracuseStep 2390867 = 3586301) B3586301
theorem B2686081 : Blo 1060614 2686081 := bstep (se 2 (by rfl) ⟨1007280, by rfl⟩ : syracuseStep 2686081 = 2014561) B2014561
theorem B6454559 : Blo 1060614 6454559 := bstep (se 1 (by rfl) ⟨4840919, by rfl⟩ : syracuseStep 6454559 = 9681839) B9681839
theorem B2391407 : Blo 1060614 2391407 := bstep (se 1 (by rfl) ⟨1793555, by rfl⟩ : syracuseStep 2391407 = 3587111) B3587111
theorem B6061499 : Blo 1060614 6061499 := bstep (se 1 (by rfl) ⟨4546124, by rfl⟩ : syracuseStep 6061499 = 9092249) B9092249
theorem B5373377 : Blo 1060614 5373377 := bstep (se 2 (by rfl) ⟨2015016, by rfl⟩ : syracuseStep 5373377 = 4030033) B4030033
theorem B12942787 : Blo 1060614 12942787 := bstep (se 1 (by rfl) ⟨9707090, by rfl⟩ : syracuseStep 12942787 = 19414181) B19414181
theorem B2391695 : Blo 1060614 2391695 := bstep (se 1 (by rfl) ⟨1793771, by rfl⟩ : syracuseStep 2391695 = 3587543) B3587543
theorem B1703567 : Blo 1060614 1703567 := bstep (se 1 (by rfl) ⟨1277675, by rfl⟩ : syracuseStep 1703567 = 2555351) B2555351
theorem B2391785 : Blo 1060614 2391785 := bstep (se 2 (by rfl) ⟨896919, by rfl⟩ : syracuseStep 2391785 = 1793839) B1793839
theorem B12091193 : Blo 1060614 12091193 := bstep (se 2 (by rfl) ⟨4534197, by rfl⟩ : syracuseStep 12091193 = 9068395) B9068395
theorem B2686891 : Blo 1060614 2686891 := bstep (se 1 (by rfl) ⟨2015168, by rfl⟩ : syracuseStep 2686891 = 4030337) B4030337
theorem B2621735 : Blo 1060614 2621735 := bstep (se 1 (by rfl) ⟨1966301, by rfl⟩ : syracuseStep 2621735 = 3932603) B3932603
theorem B2687519 : Blo 1060614 2687519 := bstep (se 1 (by rfl) ⟨2015639, by rfl⟩ : syracuseStep 2687519 = 4031279) B4031279
theorem B4981565 : Blo 1060614 4981565 := bstep (se 3 (by rfl) ⟨934043, by rfl⟩ : syracuseStep 4981565 = 1868087) B1868087
theorem B2556937 : Blo 1060614 2556937 := bstep (se 2 (by rfl) ⟨958851, by rfl⟩ : syracuseStep 2556937 = 1917703) B1917703
theorem B2393279 : Blo 1060614 2393279 := bstep (se 1 (by rfl) ⟨1794959, by rfl⟩ : syracuseStep 2393279 = 3589919) B3589919
theorem B2393423 : Blo 1060614 2393423 := bstep (se 1 (by rfl) ⟨1795067, by rfl⟩ : syracuseStep 2393423 = 3590135) B3590135
theorem B2393513 : Blo 1060614 2393513 := bstep (se 2 (by rfl) ⟨897567, by rfl⟩ : syracuseStep 2393513 = 1795135) B1795135
theorem B31065515 : Blo 1060614 31065515 := bstep (se 1 (by rfl) ⟨23299136, by rfl⟩ : syracuseStep 31065515 = 46598273) B46598273
theorem B8750585 : Blo 1060614 8750585 := bstep (se 2 (by rfl) ⟨3281469, by rfl⟩ : syracuseStep 8750585 = 6562939) B6562939
theorem B6817547 : Blo 1060614 6817547 := bstep (se 1 (by rfl) ⟨5113160, by rfl⟩ : syracuseStep 6817547 = 10226321) B10226321
theorem B2393999 : Blo 1060614 2393999 := bstep (se 1 (by rfl) ⟨1795499, by rfl⟩ : syracuseStep 2393999 = 3590999) B3590999
theorem B1345567 : Blo 1060614 1345567 := bstep (se 1 (by rfl) ⟨1009175, by rfl⟩ : syracuseStep 1345567 = 2018351) B2018351
theorem B2394143 : Blo 1060614 2394143 := bstep (se 1 (by rfl) ⟨1795607, by rfl⟩ : syracuseStep 2394143 = 3591215) B3591215
theorem B2394395 : Blo 1060614 2394395 := bstep (se 1 (by rfl) ⟨1795796, by rfl⟩ : syracuseStep 2394395 = 3591593) B3591593
theorem B2689321 : Blo 1060614 2689321 := bstep (se 2 (by rfl) ⟨1008495, by rfl⟩ : syracuseStep 2689321 = 2016991) B2016991
theorem B2394719 : Blo 1060614 2394719 := bstep (se 1 (by rfl) ⟨1796039, by rfl⟩ : syracuseStep 2394719 = 3592079) B3592079
theorem B17468027 : Blo 1060614 17468027 := bstep (se 1 (by rfl) ⟨13101020, by rfl⟩ : syracuseStep 17468027 = 26202041) B26202041
theorem B2394971 : Blo 1060614 2394971 := bstep (se 1 (by rfl) ⟨1796228, by rfl⟩ : syracuseStep 2394971 = 3592457) B3592457
theorem B2690111 : Blo 1060614 2690111 := bstep (se 1 (by rfl) ⟨2017583, by rfl⟩ : syracuseStep 2690111 = 4035167) B4035167
theorem B55184753 : Blo 1060614 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B5115257 : Blo 1060614 5115257 := bstep (se 2 (by rfl) ⟨1918221, by rfl⟩ : syracuseStep 5115257 = 3836443) B3836443
theorem B5115275 : Blo 1060614 5115275 := bstep (se 1 (by rfl) ⟨3836456, by rfl⟩ : syracuseStep 5115275 = 7672913) B7672913
theorem B9702935 : Blo 1060614 9702935 := bstep (se 1 (by rfl) ⟨7277201, by rfl⟩ : syracuseStep 9702935 = 14554403) B14554403
theorem B18420205 : Blo 1060614 18420205 := bstep (se 3 (by rfl) ⟨3453788, by rfl⟩ : syracuseStep 18420205 = 6907577) B6907577
theorem B6460979 : Blo 1060614 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B10196873 : Blo 1060614 10196873 := bstep (se 2 (by rfl) ⟨3823827, by rfl⟩ : syracuseStep 10196873 = 7647655) B7647655
theorem B4036823 : Blo 1060614 4036823 := bstep (se 1 (by rfl) ⟨3027617, by rfl⟩ : syracuseStep 4036823 = 6055235) B6055235
theorem B10198223 : Blo 1060614 10198223 := bstep (se 1 (by rfl) ⟨7648667, by rfl⟩ : syracuseStep 10198223 = 15297335) B15297335
theorem B5381639 : Blo 1060614 5381639 := bstep (se 1 (by rfl) ⟨4036229, by rfl⟩ : syracuseStep 5381639 = 8072459) B8072459
theorem B16358921 : Blo 1060614 16358921 := bstep (se 2 (by rfl) ⟨6134595, by rfl⟩ : syracuseStep 16358921 = 12269191) B12269191
theorem B1515295 : Blo 1060614 1515295 := bstep (se 1 (by rfl) ⟨1136471, by rfl⟩ : syracuseStep 1515295 = 2272943) B2272943
theorem B4038781 : Blo 1060614 4038781 := bstep (se 3 (by rfl) ⟨757271, by rfl⟩ : syracuseStep 4038781 = 1514543) B1514543
theorem B11477497 : Blo 1060614 11477497 := bstep (se 2 (by rfl) ⟨4304061, by rfl⟩ : syracuseStep 11477497 = 8608123) B8608123
theorem B4039739 : Blo 1060614 4039739 := bstep (se 1 (by rfl) ⟨3029804, by rfl⟩ : syracuseStep 4039739 = 6059609) B6059609
theorem B3581063 : Blo 1060614 3581063 := bstep (se 1 (by rfl) ⟨2685797, by rfl⟩ : syracuseStep 3581063 = 5371595) B5371595
theorem B1090783 : Blo 1060614 1090783 := bstep (se 1 (by rfl) ⟨818087, by rfl⟩ : syracuseStep 1090783 = 1636175) B1636175
theorem B3581441 : Blo 1060614 3581441 := bstep (se 2 (by rfl) ⟨1343040, by rfl⟩ : syracuseStep 3581441 = 2686081) B2686081
theorem B4303039 : Blo 1060614 4303039 := bstep (se 1 (by rfl) ⟨3227279, by rfl⟩ : syracuseStep 4303039 = 6454559) B6454559
theorem B4040999 : Blo 1060614 4040999 := bstep (se 1 (by rfl) ⟨3030749, by rfl⟩ : syracuseStep 4040999 = 6061499) B6061499
theorem B3582251 : Blo 1060614 3582251 := bstep (se 1 (by rfl) ⟨2686688, by rfl⟩ : syracuseStep 3582251 = 5373377) B5373377
theorem B5450141 : Blo 1060614 5450141 := bstep (se 3 (by rfl) ⟨1021901, by rfl⟩ : syracuseStep 5450141 = 2043803) B2043803
theorem B65317421 : Blo 1060614 65317421 := bstep (se 3 (by rfl) ⟨12247016, by rfl⟩ : syracuseStep 65317421 = 24494033) B24494033
theorem B3582521 : Blo 1060614 3582521 := bstep (se 2 (by rfl) ⟨1343445, by rfl⟩ : syracuseStep 3582521 = 2686891) B2686891
theorem B1092575 : Blo 1060614 1092575 := bstep (se 1 (by rfl) ⟨819431, by rfl⟩ : syracuseStep 1092575 = 1638863) B1638863
theorem B4041971 : Blo 1060614 4041971 := bstep (se 1 (by rfl) ⟨3031478, by rfl⟩ : syracuseStep 4041971 = 6062957) B6062957
theorem B5385527 : Blo 1060614 5385527 := bstep (se 1 (by rfl) ⟨4039145, by rfl⟩ : syracuseStep 5385527 = 8078291) B8078291
theorem B4533583 : Blo 1060614 4533583 := bstep (se 1 (by rfl) ⟨3400187, by rfl⟩ : syracuseStep 4533583 = 6800375) B6800375
theorem B18165221 : Blo 1060614 18165221 := bstep (se 4 (by rfl) ⟨1702989, by rfl⟩ : syracuseStep 18165221 = 3405979) B3405979
theorem B1060671 : Blo 1060614 1060671 := bstep (se 1 (by rfl) ⟨795503, by rfl⟩ : syracuseStep 1060671 = 1591007) B1591007
theorem B1617727 : Blo 1060614 1617727 := bstep (se 1 (by rfl) ⟨1213295, by rfl⟩ : syracuseStep 1617727 = 2426591) B2426591
theorem B1060735 : Blo 1060614 1060735 := bstep (se 1 (by rfl) ⟨795551, by rfl⟩ : syracuseStep 1060735 = 1591103) B1591103
theorem B1060847 : Blo 1060614 1060847 := bstep (se 1 (by rfl) ⟨795635, by rfl⟩ : syracuseStep 1060847 = 1591271) B1591271
theorem B1060859 : Blo 1060614 1060859 := bstep (se 1 (by rfl) ⟨795644, by rfl⟩ : syracuseStep 1060859 = 1591289) B1591289
theorem B3584033 : Blo 1060614 3584033 := bstep (se 2 (by rfl) ⟨1344012, by rfl⟩ : syracuseStep 3584033 = 2688025) B2688025
theorem B1060927 : Blo 1060614 1060927 := bstep (se 1 (by rfl) ⟨795695, by rfl⟩ : syracuseStep 1060927 = 1591391) B1591391
theorem B1060967 : Blo 1060614 1060967 := bstep (se 1 (by rfl) ⟨795725, by rfl⟩ : syracuseStep 1060967 = 1591451) B1591451
theorem B1060991 : Blo 1060614 1060991 := bstep (se 1 (by rfl) ⟨795743, by rfl⟩ : syracuseStep 1060991 = 1591487) B1591487
theorem B3027071 : Blo 1060614 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B7647371 : Blo 1060614 7647371 := bstep (se 1 (by rfl) ⟨5735528, by rfl⟩ : syracuseStep 7647371 = 11471057) B11471057
theorem B1061019 : Blo 1060614 1061019 := bstep (se 1 (by rfl) ⟨795764, by rfl⟩ : syracuseStep 1061019 = 1591529) B1591529
theorem B1061223 : Blo 1060614 1061223 := bstep (se 1 (by rfl) ⟨795917, by rfl⟩ : syracuseStep 1061223 = 1591835) B1591835
theorem B1061275 : Blo 1060614 1061275 := bstep (se 1 (by rfl) ⟨795956, by rfl⟩ : syracuseStep 1061275 = 1591913) B1591913
theorem B3584411 : Blo 1060614 3584411 := bstep (se 1 (by rfl) ⟨2688308, by rfl⟩ : syracuseStep 3584411 = 5376617) B5376617
theorem B4141625 : Blo 1060614 4141625 := bstep (se 2 (by rfl) ⟨1553109, by rfl⟩ : syracuseStep 4141625 = 3106219) B3106219
theorem B8073917 : Blo 1060614 8073917 := bstep (se 3 (by rfl) ⟨1513859, by rfl⟩ : syracuseStep 8073917 = 3027719) B3027719
theorem B1061627 : Blo 1060614 1061627 := bstep (se 1 (by rfl) ⟨796220, by rfl⟩ : syracuseStep 1061627 = 1592441) B1592441
theorem B1061695 : Blo 1060614 1061695 := bstep (se 1 (by rfl) ⟨796271, by rfl⟩ : syracuseStep 1061695 = 1592543) B1592543
theorem B1061723 : Blo 1060614 1061723 := bstep (se 1 (by rfl) ⟨796292, by rfl⟩ : syracuseStep 1061723 = 1592585) B1592585
theorem B1061791 : Blo 1060614 1061791 := bstep (se 1 (by rfl) ⟨796343, by rfl⟩ : syracuseStep 1061791 = 1592687) B1592687
theorem B1061871 : Blo 1060614 1061871 := bstep (se 1 (by rfl) ⟨796403, by rfl⟩ : syracuseStep 1061871 = 1592807) B1592807
theorem B4535291 : Blo 1060614 4535291 := bstep (se 1 (by rfl) ⟨3401468, by rfl⟩ : syracuseStep 4535291 = 6802937) B6802937
theorem B1061959 : Blo 1060614 1061959 := bstep (se 1 (by rfl) ⟨796469, by rfl⟩ : syracuseStep 1061959 = 1592939) B1592939
theorem B1062043 : Blo 1060614 1062043 := bstep (se 1 (by rfl) ⟨796532, by rfl⟩ : syracuseStep 1062043 = 1593065) B1593065
theorem B14202013 : Blo 1060614 14202013 := bstep (se 3 (by rfl) ⟨2662877, by rfl⟩ : syracuseStep 14202013 = 5325755) B5325755
theorem B1062139 : Blo 1060614 1062139 := bstep (se 1 (by rfl) ⟨796604, by rfl⟩ : syracuseStep 1062139 = 1593209) B1593209
theorem B3585275 : Blo 1060614 3585275 := bstep (se 1 (by rfl) ⟨2688956, by rfl⟩ : syracuseStep 3585275 = 5377913) B5377913
theorem B1062207 : Blo 1060614 1062207 := bstep (se 1 (by rfl) ⟨796655, by rfl⟩ : syracuseStep 1062207 = 1593311) B1593311
theorem B5748155 : Blo 1060614 5748155 := bstep (se 1 (by rfl) ⟨4311116, by rfl⟩ : syracuseStep 5748155 = 8622233) B8622233
theorem B1062375 : Blo 1060614 1062375 := bstep (se 1 (by rfl) ⟨796781, by rfl⟩ : syracuseStep 1062375 = 1593563) B1593563
theorem B1062383 : Blo 1060614 1062383 := bstep (se 1 (by rfl) ⟨796787, by rfl⟩ : syracuseStep 1062383 = 1593575) B1593575
theorem B97990145 : Blo 1060614 97990145 := bstep (se 2 (by rfl) ⟨36746304, by rfl⟩ : syracuseStep 97990145 = 73492609) B73492609
theorem B1062491 : Blo 1060614 1062491 := bstep (se 1 (by rfl) ⟨796868, by rfl⟩ : syracuseStep 1062491 = 1593737) B1593737
theorem B1062555 : Blo 1060614 1062555 := bstep (se 1 (by rfl) ⟨796916, by rfl⟩ : syracuseStep 1062555 = 1593833) B1593833
theorem B1062639 : Blo 1060614 1062639 := bstep (se 1 (by rfl) ⟨796979, by rfl⟩ : syracuseStep 1062639 = 1593959) B1593959
theorem B1062727 : Blo 1060614 1062727 := bstep (se 1 (by rfl) ⟨797045, by rfl⟩ : syracuseStep 1062727 = 1594091) B1594091
theorem B1062747 : Blo 1060614 1062747 := bstep (se 1 (by rfl) ⟨797060, by rfl⟩ : syracuseStep 1062747 = 1594121) B1594121
theorem B1062815 : Blo 1060614 1062815 := bstep (se 1 (by rfl) ⟨797111, by rfl⟩ : syracuseStep 1062815 = 1594223) B1594223
theorem B1062983 : Blo 1060614 1062983 := bstep (se 1 (by rfl) ⟨797237, by rfl⟩ : syracuseStep 1062983 = 1594475) B1594475
theorem B5388443 : Blo 1060614 5388443 := bstep (se 1 (by rfl) ⟨4041332, by rfl⟩ : syracuseStep 5388443 = 8082665) B8082665
theorem B13285571 : Blo 1060614 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B1063143 : Blo 1060614 1063143 := bstep (se 1 (by rfl) ⟨797357, by rfl⟩ : syracuseStep 1063143 = 1594715) B1594715
theorem B1063327 : Blo 1060614 1063327 := bstep (se 1 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 1063327 = 1594991) B1594991
theorem B1063375 : Blo 1060614 1063375 := bstep (se 1 (by rfl) ⟨797531, by rfl⟩ : syracuseStep 1063375 = 1595063) B1595063
theorem B1063399 : Blo 1060614 1063399 := bstep (se 1 (by rfl) ⟨797549, by rfl⟩ : syracuseStep 1063399 = 1595099) B1595099
theorem B3062279 : Blo 1060614 3062279 := bstep (se 1 (by rfl) ⟨2296709, by rfl⟩ : syracuseStep 3062279 = 4593419) B4593419
theorem B1063515 : Blo 1060614 1063515 := bstep (se 1 (by rfl) ⟨797636, by rfl⟩ : syracuseStep 1063515 = 1595273) B1595273
theorem B1194655 : Blo 1060614 1194655 := bstep (se 1 (by rfl) ⟨895991, by rfl⟩ : syracuseStep 1194655 = 1791983) B1791983
theorem B1063583 : Blo 1060614 1063583 := bstep (se 1 (by rfl) ⟨797687, by rfl⟩ : syracuseStep 1063583 = 1595375) B1595375
theorem B1063751 : Blo 1060614 1063751 := bstep (se 1 (by rfl) ⟨797813, by rfl⟩ : syracuseStep 1063751 = 1595627) B1595627
theorem B15547241 : Blo 1060614 15547241 := bstep (se 2 (by rfl) ⟨5830215, by rfl⟩ : syracuseStep 15547241 = 11660431) B11660431
theorem B1063791 : Blo 1060614 1063791 := bstep (se 1 (by rfl) ⟨797843, by rfl⟩ : syracuseStep 1063791 = 1595687) B1595687
theorem B1063847 : Blo 1060614 1063847 := bstep (se 1 (by rfl) ⟨797885, by rfl⟩ : syracuseStep 1063847 = 1595771) B1595771
theorem B50412557 : Blo 1060614 50412557 := bstep (se 3 (by rfl) ⟨9452354, by rfl⟩ : syracuseStep 50412557 = 18904709) B18904709
theorem B8076347 : Blo 1060614 8076347 := bstep (se 1 (by rfl) ⟨6057260, by rfl⟩ : syracuseStep 8076347 = 12114521) B12114521
theorem B1293403 : Blo 1060614 1293403 := bstep (se 1 (by rfl) ⟨970052, by rfl⟩ : syracuseStep 1293403 = 1940105) B1940105
theorem B1064027 : Blo 1060614 1064027 := bstep (se 1 (by rfl) ⟨798020, by rfl⟩ : syracuseStep 1064027 = 1596041) B1596041
theorem B1064143 : Blo 1060614 1064143 := bstep (se 1 (by rfl) ⟨798107, by rfl⟩ : syracuseStep 1064143 = 1596215) B1596215
theorem B1064167 : Blo 1060614 1064167 := bstep (se 1 (by rfl) ⟨798125, by rfl⟩ : syracuseStep 1064167 = 1596251) B1596251
theorem B1064263 : Blo 1060614 1064263 := bstep (se 1 (by rfl) ⟨798197, by rfl⟩ : syracuseStep 1064263 = 1596395) B1596395
theorem B1064399 : Blo 1060614 1064399 := bstep (se 1 (by rfl) ⟨798299, by rfl⟩ : syracuseStep 1064399 = 1596599) B1596599
theorem B3030635 : Blo 1060614 3030635 := bstep (se 1 (by rfl) ⟨2272976, by rfl⟩ : syracuseStep 3030635 = 4545953) B4545953
theorem B1064559 : Blo 1060614 1064559 := bstep (se 1 (by rfl) ⟨798419, by rfl⟩ : syracuseStep 1064559 = 1596839) B1596839
theorem B2014895 : Blo 1060614 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B1195807 : Blo 1060614 1195807 := bstep (se 1 (by rfl) ⟨896855, by rfl⟩ : syracuseStep 1195807 = 1793711) B1793711
theorem B1196239 : Blo 1060614 1196239 := bstep (se 1 (by rfl) ⟨897179, by rfl⟩ : syracuseStep 1196239 = 1794359) B1794359
theorem B14729779 : Blo 1060614 14729779 := bstep (se 1 (by rfl) ⟨11047334, by rfl⟩ : syracuseStep 14729779 = 22094669) B22094669
theorem B1917551 : Blo 1060614 1917551 := bstep (se 1 (by rfl) ⟨1438163, by rfl⟩ : syracuseStep 1917551 = 2876327) B2876327
theorem B6046487 : Blo 1060614 6046487 := bstep (se 1 (by rfl) ⟨4534865, by rfl⟩ : syracuseStep 6046487 = 9069731) B9069731
theorem B1197103 : Blo 1060614 1197103 := bstep (se 1 (by rfl) ⟨897827, by rfl⟩ : syracuseStep 1197103 = 1795655) B1795655
theorem B1197247 : Blo 1060614 1197247 := bstep (se 1 (by rfl) ⟨897935, by rfl⟩ : syracuseStep 1197247 = 1795871) B1795871
theorem B1197391 : Blo 1060614 1197391 := bstep (se 1 (by rfl) ⟨898043, by rfl⟩ : syracuseStep 1197391 = 1796087) B1796087
theorem B4605281 : Blo 1060614 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B1590959 : Blo 1060614 1590959 := bstep (se 1 (by rfl) ⟨1193219, by rfl⟩ : syracuseStep 1590959 = 2386439) B2386439
theorem B1591079 : Blo 1060614 1591079 := bstep (se 1 (by rfl) ⟨1193309, by rfl⟩ : syracuseStep 1591079 = 2386619) B2386619
theorem B1591631 : Blo 1060614 1591631 := bstep (se 1 (by rfl) ⟨1193723, by rfl⟩ : syracuseStep 1591631 = 2387447) B2387447
theorem B1591679 : Blo 1060614 1591679 := bstep (se 1 (by rfl) ⟨1193759, by rfl⟩ : syracuseStep 1591679 = 2387519) B2387519
theorem B1591721 : Blo 1060614 1591721 := bstep (se 2 (by rfl) ⟨596895, by rfl⟩ : syracuseStep 1591721 = 1193791) B1193791
theorem B2017705 : Blo 1060614 2017705 := bstep (se 2 (by rfl) ⟨756639, by rfl⟩ : syracuseStep 2017705 = 1513279) B1513279
theorem B4311667 : Blo 1060614 4311667 := bstep (se 1 (by rfl) ⟨3233750, by rfl⟩ : syracuseStep 4311667 = 6467501) B6467501
theorem B6048377 : Blo 1060614 6048377 := bstep (se 2 (by rfl) ⟨2268141, by rfl⟩ : syracuseStep 6048377 = 4536283) B4536283
theorem B1592105 : Blo 1060614 1592105 := bstep (se 2 (by rfl) ⟨597039, by rfl⟩ : syracuseStep 1592105 = 1194079) B1194079
theorem B1592315 : Blo 1060614 1592315 := bstep (se 1 (by rfl) ⟨1194236, by rfl⟩ : syracuseStep 1592315 = 2388473) B2388473
theorem B1592375 : Blo 1060614 1592375 := bstep (se 1 (by rfl) ⟨1194281, by rfl⟩ : syracuseStep 1592375 = 2388563) B2388563
theorem B1592495 : Blo 1060614 1592495 := bstep (se 1 (by rfl) ⟨1194371, by rfl⟩ : syracuseStep 1592495 = 2388743) B2388743
theorem B4541615 : Blo 1060614 4541615 := bstep (se 1 (by rfl) ⟨3406211, by rfl⟩ : syracuseStep 4541615 = 6812423) B6812423
theorem B4542263 : Blo 1060614 4542263 := bstep (se 1 (by rfl) ⟨3406697, by rfl⟩ : syracuseStep 4542263 = 6813395) B6813395
theorem B1789823 : Blo 1060614 1789823 := bstep (se 1 (by rfl) ⟨1342367, by rfl⟩ : syracuseStep 1789823 = 2684735) B2684735
theorem B1593215 : Blo 1060614 1593215 := bstep (se 1 (by rfl) ⟨1194911, by rfl⟩ : syracuseStep 1593215 = 2389823) B2389823
theorem B2019323 : Blo 1060614 2019323 := bstep (se 1 (by rfl) ⟨1514492, by rfl⟩ : syracuseStep 2019323 = 3028985) B3028985
theorem B3592187 : Blo 1060614 3592187 := bstep (se 1 (by rfl) ⟨2694140, by rfl⟩ : syracuseStep 3592187 = 5388281) B5388281
theorem B1593407 : Blo 1060614 1593407 := bstep (se 1 (by rfl) ⟨1195055, by rfl⟩ : syracuseStep 1593407 = 2390111) B2390111
theorem B1790059 : Blo 1060614 1790059 := bstep (se 1 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 1790059 = 2685089) B2685089
theorem B1593641 : Blo 1060614 1593641 := bstep (se 2 (by rfl) ⟨597615, by rfl⟩ : syracuseStep 1593641 = 1195231) B1195231
theorem B9687383 : Blo 1060614 9687383 := bstep (se 1 (by rfl) ⟨7265537, by rfl⟩ : syracuseStep 9687383 = 14531075) B14531075
theorem B1593911 : Blo 1060614 1593911 := bstep (se 1 (by rfl) ⟨1195433, by rfl⟩ : syracuseStep 1593911 = 2390867) B2390867
theorem B17257049 : Blo 1060614 17257049 := bstep (se 2 (by rfl) ⟨6471393, by rfl⟩ : syracuseStep 17257049 = 12942787) B12942787
theorem B3593051 : Blo 1060614 3593051 := bstep (se 1 (by rfl) ⟨2694788, by rfl⟩ : syracuseStep 3593051 = 5389577) B5389577
theorem B1594271 : Blo 1060614 1594271 := bstep (se 1 (by rfl) ⟨1195703, by rfl⟩ : syracuseStep 1594271 = 2391407) B2391407
theorem B13816813 : Blo 1060614 13816813 := bstep (se 3 (by rfl) ⟨2590652, by rfl⟩ : syracuseStep 13816813 = 5181305) B5181305
theorem B1135711 : Blo 1060614 1135711 := bstep (se 1 (by rfl) ⟨851783, by rfl⟩ : syracuseStep 1135711 = 1703567) B1703567
theorem B1594463 : Blo 1060614 1594463 := bstep (se 1 (by rfl) ⟨1195847, by rfl⟩ : syracuseStep 1594463 = 2391695) B2391695
theorem B1594523 : Blo 1060614 1594523 := bstep (se 1 (by rfl) ⟨1195892, by rfl⟩ : syracuseStep 1594523 = 2391785) B2391785
theorem B17257823 : Blo 1060614 17257823 := bstep (se 1 (by rfl) ⟨12943367, by rfl⟩ : syracuseStep 17257823 = 25886735) B25886735
theorem B1791463 : Blo 1060614 1791463 := bstep (se 1 (by rfl) ⟨1343597, by rfl⟩ : syracuseStep 1791463 = 2687195) B2687195
theorem B5101127 : Blo 1060614 5101127 := bstep (se 1 (by rfl) ⟨3825845, by rfl⟩ : syracuseStep 5101127 = 7651691) B7651691
theorem B1791625 : Blo 1060614 1791625 := bstep (se 2 (by rfl) ⟨671859, by rfl⟩ : syracuseStep 1791625 = 1343719) B1343719
theorem B2152103 : Blo 1060614 2152103 := bstep (se 1 (by rfl) ⟨1614077, by rfl⟩ : syracuseStep 2152103 = 3228155) B3228155
theorem B1595207 : Blo 1060614 1595207 := bstep (se 1 (by rfl) ⟨1196405, by rfl⟩ : syracuseStep 1595207 = 2392811) B2392811
theorem B87283649 : Blo 1060614 87283649 := bstep (se 2 (by rfl) ⟨32731368, by rfl⟩ : syracuseStep 87283649 = 65462737) B65462737
theorem B1792219 : Blo 1060614 1792219 := bstep (se 1 (by rfl) ⟨1344164, by rfl⟩ : syracuseStep 1792219 = 2688329) B2688329
theorem B9066755 : Blo 1060614 9066755 := bstep (se 1 (by rfl) ⟨6800066, by rfl⟩ : syracuseStep 9066755 = 13600133) B13600133
theorem B1792415 : Blo 1060614 1792415 := bstep (se 1 (by rfl) ⟨1344311, by rfl⟩ : syracuseStep 1792415 = 2688623) B2688623
theorem B1595807 : Blo 1060614 1595807 := bstep (se 1 (by rfl) ⟨1196855, by rfl⟩ : syracuseStep 1595807 = 2393711) B2393711
theorem B3398075 : Blo 1060614 3398075 := bstep (se 1 (by rfl) ⟨2548556, by rfl⟩ : syracuseStep 3398075 = 5097113) B5097113
theorem B1595879 : Blo 1060614 1595879 := bstep (se 1 (by rfl) ⟨1196909, by rfl⟩ : syracuseStep 1595879 = 2393819) B2393819
theorem B1792489 : Blo 1060614 1792489 := bstep (se 2 (by rfl) ⟨672183, by rfl⟩ : syracuseStep 1792489 = 1344367) B1344367
theorem B345332219 : Blo 1060614 345332219 := bstep (se 1 (by rfl) ⟨258999164, by rfl⟩ : syracuseStep 345332219 = 517998329) B517998329
theorem B3398753 : Blo 1060614 3398753 := bstep (se 2 (by rfl) ⟨1274532, by rfl⟩ : syracuseStep 3398753 = 2549065) B2549065
theorem B1596623 : Blo 1060614 1596623 := bstep (se 1 (by rfl) ⟨1197467, by rfl⟩ : syracuseStep 1596623 = 2394935) B2394935
theorem B1596743 : Blo 1060614 1596743 := bstep (se 1 (by rfl) ⟨1197557, by rfl⟩ : syracuseStep 1596743 = 2395115) B2395115
theorem B1596905 : Blo 1060614 1596905 := bstep (se 2 (by rfl) ⟨598839, by rfl⟩ : syracuseStep 1596905 = 1197679) B1197679
theorem B1793657 : Blo 1060614 1793657 := bstep (se 2 (by rfl) ⟨672621, by rfl⟩ : syracuseStep 1793657 = 1345243) B1345243
theorem B1531559 : Blo 1060614 1531559 := bstep (se 1 (by rfl) ⟨1148669, by rfl⟩ : syracuseStep 1531559 = 2297339) B2297339
theorem B13623713 : Blo 1060614 13623713 := bstep (se 2 (by rfl) ⟨5108892, by rfl⟩ : syracuseStep 13623713 = 10217785) B10217785
theorem B1795385 : Blo 1060614 1795385 := bstep (se 2 (by rfl) ⟨673269, by rfl⟩ : syracuseStep 1795385 = 1346539) B1346539
theorem B156984965 : Blo 1060614 156984965 := bstep (se 4 (by rfl) ⟨14717340, by rfl⟩ : syracuseStep 156984965 = 29434681) B29434681
theorem B20440795 : Blo 1060614 20440795 := bstep (se 1 (by rfl) ⟨15330596, by rfl⟩ : syracuseStep 20440795 = 30661193) B30661193
theorem B8611919 : Blo 1060614 8611919 := bstep (se 1 (by rfl) ⟨6458939, by rfl⟩ : syracuseStep 8611919 = 12917879) B12917879
theorem B3631337 : Blo 1060614 3631337 := bstep (se 2 (by rfl) ⟨1361751, by rfl⟩ : syracuseStep 3631337 = 2723503) B2723503
theorem B7268717 : Blo 1060614 7268717 := bstep (se 3 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 7268717 = 2725769) B2725769
theorem B9071129 : Blo 1060614 9071129 := bstep (se 2 (by rfl) ⟨3401673, by rfl⟩ : syracuseStep 9071129 = 6803347) B6803347
theorem B8055449 : Blo 1060614 8055449 := bstep (se 2 (by rfl) ⟨3020793, by rfl⟩ : syracuseStep 8055449 = 6041587) B6041587
theorem B2387015 : Blo 1060614 2387015 := bstep (se 1 (by rfl) ⟨1790261, by rfl⟩ : syracuseStep 2387015 = 3580523) B3580523
theorem B2419895 : Blo 1060614 2419895 := bstep (se 1 (by rfl) ⟨1814921, by rfl⟩ : syracuseStep 2419895 = 3629843) B3629843
theorem B5107049 : Blo 1060614 5107049 := bstep (se 2 (by rfl) ⟨1915143, by rfl⟩ : syracuseStep 5107049 = 3830287) B3830287
theorem B2387411 : Blo 1060614 2387411 := bstep (se 1 (by rfl) ⟨1790558, by rfl⟩ : syracuseStep 2387411 = 3581117) B3581117
theorem B2387681 : Blo 1060614 2387681 := bstep (se 2 (by rfl) ⟨895380, by rfl⟩ : syracuseStep 2387681 = 1790761) B1790761
theorem B2388041 : Blo 1060614 2388041 := bstep (se 2 (by rfl) ⟨895515, by rfl⟩ : syracuseStep 2388041 = 1791031) B1791031
theorem B2388095 : Blo 1060614 2388095 := bstep (se 1 (by rfl) ⟨1791071, by rfl⟩ : syracuseStep 2388095 = 3582143) B3582143
theorem B9072769 : Blo 1060614 9072769 := bstep (se 2 (by rfl) ⟨3402288, by rfl⟩ : syracuseStep 9072769 = 6804577) B6804577
theorem B4092287 : Blo 1060614 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B18182717 : Blo 1060614 18182717 := bstep (se 3 (by rfl) ⟨3409259, by rfl⟩ : syracuseStep 18182717 = 6818519) B6818519
theorem B2552639 : Blo 1060614 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B2389175 : Blo 1060614 2389175 := bstep (se 1 (by rfl) ⟨1791881, by rfl⟩ : syracuseStep 2389175 = 3583763) B3583763
theorem B4027603 : Blo 1060614 4027603 := bstep (se 1 (by rfl) ⟨3020702, by rfl⟩ : syracuseStep 4027603 = 6041405) B6041405
theorem B5830055 : Blo 1060614 5830055 := bstep (se 1 (by rfl) ⟨4372541, by rfl⟩ : syracuseStep 5830055 = 8745083) B8745083
theorem B4847195 : Blo 1060614 4847195 := bstep (se 1 (by rfl) ⟨3635396, by rfl⟩ : syracuseStep 4847195 = 7270793) B7270793
theorem B9336509 : Blo 1060614 9336509 := bstep (se 3 (by rfl) ⟨1750595, by rfl⟩ : syracuseStep 9336509 = 3501191) B3501191
theorem B2389751 : Blo 1060614 2389751 := bstep (se 1 (by rfl) ⟨1792313, by rfl⟩ : syracuseStep 2389751 = 3584627) B3584627
theorem B2389931 : Blo 1060614 2389931 := bstep (se 1 (by rfl) ⟨1792448, by rfl⟩ : syracuseStep 2389931 = 3584897) B3584897
theorem B2390057 : Blo 1060614 2390057 := bstep (se 2 (by rfl) ⟨896271, by rfl⟩ : syracuseStep 2390057 = 1792543) B1792543
theorem B13826419 : Blo 1060614 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B7666109 : Blo 1060614 7666109 := bstep (se 3 (by rfl) ⟨1437395, by rfl⟩ : syracuseStep 7666109 = 2874791) B2874791
theorem B2390471 : Blo 1060614 2390471 := bstep (se 1 (by rfl) ⟨1792853, by rfl⟩ : syracuseStep 2390471 = 3585707) B3585707
theorem B4028879 : Blo 1060614 4028879 := bstep (se 1 (by rfl) ⟨3021659, by rfl⟩ : syracuseStep 4028879 = 6043319) B6043319
theorem B2554409 : Blo 1060614 2554409 := bstep (se 2 (by rfl) ⟨957903, by rfl⟩ : syracuseStep 2554409 = 1915807) B1915807
theorem B2685545 : Blo 1060614 2685545 := bstep (se 2 (by rfl) ⟨1007079, by rfl⟩ : syracuseStep 2685545 = 2014159) B2014159
theorem B2390633 : Blo 1060614 2390633 := bstep (se 2 (by rfl) ⟨896487, by rfl⟩ : syracuseStep 2390633 = 1792975) B1792975
theorem B2390687 : Blo 1060614 2390687 := bstep (se 1 (by rfl) ⟨1793015, by rfl⟩ : syracuseStep 2390687 = 3586031) B3586031
theorem B2390831 : Blo 1060614 2390831 := bstep (se 1 (by rfl) ⟨1793123, by rfl⟩ : syracuseStep 2390831 = 3586247) B3586247
theorem B10222631 : Blo 1060614 10222631 := bstep (se 1 (by rfl) ⟨7666973, by rfl⟩ : syracuseStep 10222631 = 15333947) B15333947
theorem B2391263 : Blo 1060614 2391263 := bstep (se 1 (by rfl) ⟨1793447, by rfl⟩ : syracuseStep 2391263 = 3586895) B3586895
theorem B2391479 : Blo 1060614 2391479 := bstep (se 1 (by rfl) ⟨1793609, by rfl⟩ : syracuseStep 2391479 = 3587219) B3587219
theorem B2391659 : Blo 1060614 2391659 := bstep (se 1 (by rfl) ⟨1793744, by rfl⟩ : syracuseStep 2391659 = 3587489) B3587489
theorem B2686729 : Blo 1060614 2686729 := bstep (se 2 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 2686729 = 2015047) B2015047
theorem B2391929 : Blo 1060614 2391929 := bstep (se 2 (by rfl) ⟨896973, by rfl⟩ : syracuseStep 2391929 = 1793947) B1793947
theorem B8060795 : Blo 1060614 8060795 := bstep (se 1 (by rfl) ⟨6045596, by rfl⟩ : syracuseStep 8060795 = 12091193) B12091193
theorem B2392019 : Blo 1060614 2392019 := bstep (se 1 (by rfl) ⟨1794014, by rfl⟩ : syracuseStep 2392019 = 3588029) B3588029
theorem B55214045 : Blo 1060614 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B4030991 : Blo 1060614 4030991 := bstep (se 1 (by rfl) ⟨3023243, by rfl⟩ : syracuseStep 4030991 = 6046487) B6046487
theorem B15303329 : Blo 1060614 15303329 := bstep (se 2 (by rfl) ⟨5738748, by rfl⟩ : syracuseStep 15303329 = 11477497) B11477497
theorem B20710343 : Blo 1060614 20710343 := bstep (se 1 (by rfl) ⟨15532757, by rfl⟩ : syracuseStep 20710343 = 31065515) B31065515
theorem B5833723 : Blo 1060614 5833723 := bstep (se 1 (by rfl) ⟨4375292, by rfl⟩ : syracuseStep 5833723 = 8750585) B8750585
theorem B10912765 : Blo 1060614 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B3409249 : Blo 1060614 3409249 := bstep (se 2 (by rfl) ⟨1278468, by rfl⟩ : syracuseStep 3409249 = 2556937) B2556937
theorem B11044333 : Blo 1060614 11044333 := bstep (se 3 (by rfl) ⟨2070812, by rfl⟩ : syracuseStep 11044333 = 4141625) B4141625
theorem B5113469 : Blo 1060614 5113469 := bstep (se 3 (by rfl) ⟨958775, by rfl⟩ : syracuseStep 5113469 = 1917551) B1917551
theorem B4032251 : Blo 1060614 4032251 := bstep (se 1 (by rfl) ⟨3024188, by rfl⟩ : syracuseStep 4032251 = 6048377) B6048377
theorem B3410171 : Blo 1060614 3410171 := bstep (se 1 (by rfl) ⟨2557628, by rfl⟩ : syracuseStep 3410171 = 5115257) B5115257
theorem B3410183 : Blo 1060614 3410183 := bstep (se 1 (by rfl) ⟨2557637, by rfl⟩ : syracuseStep 3410183 = 5115275) B5115275
theorem B12094109 : Blo 1060614 12094109 := bstep (se 3 (by rfl) ⟨2267645, by rfl⟩ : syracuseStep 12094109 = 4535291) B4535291
theorem B1346215 : Blo 1060614 1346215 := bstep (se 1 (by rfl) ⟨1009661, by rfl⟩ : syracuseStep 1346215 = 2019323) B2019323
theorem B2394791 : Blo 1060614 2394791 := bstep (se 1 (by rfl) ⟨1796093, by rfl⟩ : syracuseStep 2394791 = 3592187) B3592187
theorem B6458255 : Blo 1060614 6458255 := bstep (se 1 (by rfl) ⟨4843691, by rfl⟩ : syracuseStep 6458255 = 9687383) B9687383
theorem B5737385 : Blo 1060614 5737385 := bstep (se 2 (by rfl) ⟨2151519, by rfl⟩ : syracuseStep 5737385 = 4303039) B4303039
theorem B11504699 : Blo 1060614 11504699 := bstep (se 1 (by rfl) ⟨8628524, by rfl⟩ : syracuseStep 11504699 = 17257049) B17257049
theorem B2690273 : Blo 1060614 2690273 := bstep (se 2 (by rfl) ⟨1008852, by rfl⟩ : syracuseStep 2690273 = 2017705) B2017705
theorem B2395367 : Blo 1060614 2395367 := bstep (se 1 (by rfl) ⟨1796525, by rfl⟩ : syracuseStep 2395367 = 3593051) B3593051
theorem B11505215 : Blo 1060614 11505215 := bstep (se 1 (by rfl) ⟨8628911, by rfl⟩ : syracuseStep 11505215 = 17257823) B17257823
theorem B2691215 : Blo 1060614 2691215 := bstep (se 1 (by rfl) ⟨2018411, by rfl⟩ : syracuseStep 2691215 = 4036823) B4036823
theorem B2265383 : Blo 1060614 2265383 := bstep (se 1 (by rfl) ⟨1699037, by rfl⟩ : syracuseStep 2265383 = 3398075) B3398075
theorem B5738941 : Blo 1060614 5738941 := bstep (se 3 (by rfl) ⟨1076051, by rfl⟩ : syracuseStep 5738941 = 2152103) B2152103
theorem B2265835 : Blo 1060614 2265835 := bstep (se 1 (by rfl) ⟨1699376, by rfl⟩ : syracuseStep 2265835 = 3398753) B3398753
theorem B12097025 : Blo 1060614 12097025 := bstep (se 2 (by rfl) ⟨4536384, by rfl⟩ : syracuseStep 12097025 = 9072769) B9072769
theorem B9082475 : Blo 1060614 9082475 := bstep (se 1 (by rfl) ⟨6811856, by rfl⟩ : syracuseStep 9082475 = 13623713) B13623713
theorem B2693159 : Blo 1060614 2693159 := bstep (se 1 (by rfl) ⟨2019869, by rfl⟩ : syracuseStep 2693159 = 4039739) B4039739
theorem B18422417 : Blo 1060614 18422417 := bstep (se 2 (by rfl) ⟨6908406, by rfl⟩ : syracuseStep 18422417 = 13816813) B13816813
theorem B920885917 : Blo 1060614 920885917 := bstep (se 3 (by rfl) ⟨172666109, by rfl⟩ : syracuseStep 920885917 = 345332219) B345332219
theorem B5741279 : Blo 1060614 5741279 := bstep (se 1 (by rfl) ⟨4305959, by rfl⟩ : syracuseStep 5741279 = 8611919) B8611919
theorem B2693999 : Blo 1060614 2693999 := bstep (se 1 (by rfl) ⟨2020499, by rfl⟩ : syracuseStep 2693999 = 4040999) B4040999
theorem B2694647 : Blo 1060614 2694647 := bstep (se 1 (by rfl) ⟨2020985, by rfl⟩ : syracuseStep 2694647 = 4041971) B4041971
theorem B41459309 : Blo 1060614 41459309 := bstep (se 3 (by rfl) ⟨7773620, by rfl⟩ : syracuseStep 41459309 = 15547241) B15547241
theorem B5382611 : Blo 1060614 5382611 := bstep (se 1 (by rfl) ⟨4036958, by rfl⟩ : syracuseStep 5382611 = 8073917) B8073917
theorem B2041519 : Blo 1060614 2041519 := bstep (se 1 (by rfl) ⟨1531139, by rfl⟩ : syracuseStep 2041519 = 3062279) B3062279
theorem B5384231 : Blo 1060614 5384231 := bstep (se 1 (by rfl) ⟨4038173, by rfl⟩ : syracuseStep 5384231 = 8076347) B8076347
theorem B3582305 : Blo 1060614 3582305 := bstep (se 2 (by rfl) ⟨1343364, by rfl⟩ : syracuseStep 3582305 = 2686729) B2686729
theorem B36809363 : Blo 1060614 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B5385041 : Blo 1060614 5385041 := bstep (se 2 (by rfl) ⟨2019390, by rfl⟩ : syracuseStep 5385041 = 4038781) B4038781
theorem B1747823 : Blo 1060614 1747823 := bstep (se 1 (by rfl) ⟨1310867, by rfl⟩ : syracuseStep 1747823 = 2621735) B2621735
theorem B3321043 : Blo 1060614 3321043 := bstep (se 1 (by rfl) ⟨2490782, by rfl⟩ : syracuseStep 3321043 = 4981565) B4981565
theorem B19639705 : Blo 1060614 19639705 := bstep (se 2 (by rfl) ⟨7364889, by rfl⟩ : syracuseStep 19639705 = 14729779) B14729779
theorem B1060639 : Blo 1060614 1060639 := bstep (se 1 (by rfl) ⟨795479, by rfl⟩ : syracuseStep 1060639 = 1590959) B1590959
theorem B1060719 : Blo 1060614 1060719 := bstep (se 1 (by rfl) ⟨795539, by rfl⟩ : syracuseStep 1060719 = 1591079) B1591079
theorem B1061087 : Blo 1060614 1061087 := bstep (se 1 (by rfl) ⟨795815, by rfl⟩ : syracuseStep 1061087 = 1591631) B1591631
theorem B1061119 : Blo 1060614 1061119 := bstep (se 1 (by rfl) ⟨795839, by rfl⟩ : syracuseStep 1061119 = 1591679) B1591679
theorem B1061147 : Blo 1060614 1061147 := bstep (se 1 (by rfl) ⟨795860, by rfl⟩ : syracuseStep 1061147 = 1591721) B1591721
theorem B1454377 : Blo 1060614 1454377 := bstep (se 2 (by rfl) ⟨545391, by rfl⟩ : syracuseStep 1454377 = 1090783) B1090783
theorem B11645351 : Blo 1060614 11645351 := bstep (se 1 (by rfl) ⟨8734013, by rfl⟩ : syracuseStep 11645351 = 17468027) B17468027
theorem B1061403 : Blo 1060614 1061403 := bstep (se 1 (by rfl) ⟨796052, by rfl⟩ : syracuseStep 1061403 = 1592105) B1592105
theorem B73740901 : Blo 1060614 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B1061543 : Blo 1060614 1061543 := bstep (se 1 (by rfl) ⟨796157, by rfl⟩ : syracuseStep 1061543 = 1592315) B1592315
theorem B1061583 : Blo 1060614 1061583 := bstep (se 1 (by rfl) ⟨796187, by rfl⟩ : syracuseStep 1061583 = 1592375) B1592375
theorem B1061663 : Blo 1060614 1061663 := bstep (se 1 (by rfl) ⟨796247, by rfl⟩ : syracuseStep 1061663 = 1592495) B1592495
theorem B3027743 : Blo 1060614 3027743 := bstep (se 1 (by rfl) ⟨2270807, by rfl⟩ : syracuseStep 3027743 = 4541615) B4541615
theorem B6468623 : Blo 1060614 6468623 := bstep (se 1 (by rfl) ⟨4851467, by rfl⟩ : syracuseStep 6468623 = 9702935) B9702935
theorem B3028175 : Blo 1060614 3028175 := bstep (se 1 (by rfl) ⟨2271131, by rfl⟩ : syracuseStep 3028175 = 4542263) B4542263
theorem B1193215 : Blo 1060614 1193215 := bstep (se 1 (by rfl) ⟨894911, by rfl⟩ : syracuseStep 1193215 = 1789823) B1789823
theorem B1062143 : Blo 1060614 1062143 := bstep (se 1 (by rfl) ⟨796607, by rfl⟩ : syracuseStep 1062143 = 1593215) B1593215
theorem B1062271 : Blo 1060614 1062271 := bstep (se 1 (by rfl) ⟨796703, by rfl⟩ : syracuseStep 1062271 = 1593407) B1593407
theorem B1062427 : Blo 1060614 1062427 := bstep (se 1 (by rfl) ⟨796820, by rfl⟩ : syracuseStep 1062427 = 1593641) B1593641
theorem B1062607 : Blo 1060614 1062607 := bstep (se 1 (by rfl) ⟨796955, by rfl⟩ : syracuseStep 1062607 = 1593911) B1593911
theorem B3585761 : Blo 1060614 3585761 := bstep (se 2 (by rfl) ⟨1344660, by rfl⟩ : syracuseStep 3585761 = 2689321) B2689321
theorem B1062847 : Blo 1060614 1062847 := bstep (se 1 (by rfl) ⟨797135, by rfl⟩ : syracuseStep 1062847 = 1594271) B1594271
theorem B1062975 : Blo 1060614 1062975 := bstep (se 1 (by rfl) ⟨797231, by rfl⟩ : syracuseStep 1062975 = 1594463) B1594463
theorem B1063015 : Blo 1060614 1063015 := bstep (se 1 (by rfl) ⟨797261, by rfl⟩ : syracuseStep 1063015 = 1594523) B1594523
theorem B5748889 : Blo 1060614 5748889 := bstep (se 2 (by rfl) ⟨2155833, by rfl⟩ : syracuseStep 5748889 = 4311667) B4311667
theorem B1063471 : Blo 1060614 1063471 := bstep (se 1 (by rfl) ⟨797603, by rfl⟩ : syracuseStep 1063471 = 1595207) B1595207
theorem B6797915 : Blo 1060614 6797915 := bstep (se 1 (by rfl) ⟨5098436, by rfl⟩ : syracuseStep 6797915 = 10196873) B10196873
theorem B6044503 : Blo 1060614 6044503 := bstep (se 1 (by rfl) ⟨4533377, by rfl⟩ : syracuseStep 6044503 = 9066755) B9066755
theorem B1194943 : Blo 1060614 1194943 := bstep (se 1 (by rfl) ⟨896207, by rfl⟩ : syracuseStep 1194943 = 1792415) B1792415
theorem B1063871 : Blo 1060614 1063871 := bstep (se 1 (by rfl) ⟨797903, by rfl⟩ : syracuseStep 1063871 = 1595807) B1595807
theorem B1063919 : Blo 1060614 1063919 := bstep (se 1 (by rfl) ⟨797939, by rfl⟩ : syracuseStep 1063919 = 1595879) B1595879
theorem B6044777 : Blo 1060614 6044777 := bstep (se 2 (by rfl) ⟨2266791, by rfl⟩ : syracuseStep 6044777 = 4533583) B4533583
theorem B6798815 : Blo 1060614 6798815 := bstep (se 1 (by rfl) ⟨5099111, by rfl⟩ : syracuseStep 6798815 = 10198223) B10198223
theorem B1064415 : Blo 1060614 1064415 := bstep (se 1 (by rfl) ⟨798311, by rfl⟩ : syracuseStep 1064415 = 1596623) B1596623
theorem B1064495 : Blo 1060614 1064495 := bstep (se 1 (by rfl) ⟨798371, by rfl⟩ : syracuseStep 1064495 = 1596743) B1596743
theorem B1064603 : Blo 1060614 1064603 := bstep (se 1 (by rfl) ⟨798452, by rfl⟩ : syracuseStep 1064603 = 1596905) B1596905
theorem B3587759 : Blo 1060614 3587759 := bstep (se 1 (by rfl) ⟨2690819, by rfl⟩ : syracuseStep 3587759 = 5381639) B5381639
theorem B1195771 : Blo 1060614 1195771 := bstep (se 1 (by rfl) ⟨896828, by rfl⟩ : syracuseStep 1195771 = 1793657) B1793657
theorem B24560273 : Blo 1060614 24560273 := bstep (se 2 (by rfl) ⟨9210102, by rfl⟩ : syracuseStep 24560273 = 18420205) B18420205
theorem B1196923 : Blo 1060614 1196923 := bstep (se 1 (by rfl) ⟨897692, by rfl⟩ : syracuseStep 1196923 = 1795385) B1795385
theorem B19383245 : Blo 1060614 19383245 := bstep (se 3 (by rfl) ⟨3634358, by rfl⟩ : syracuseStep 19383245 = 7268717) B7268717
theorem B6047419 : Blo 1060614 6047419 := bstep (se 1 (by rfl) ⟨4535564, by rfl⟩ : syracuseStep 6047419 = 9071129) B9071129
theorem B1591343 : Blo 1060614 1591343 := bstep (se 1 (by rfl) ⟨1193507, by rfl⟩ : syracuseStep 1591343 = 2387015) B2387015
theorem B3590351 : Blo 1060614 3590351 := bstep (se 1 (by rfl) ⟨2692763, by rfl⟩ : syracuseStep 3590351 = 5385527) B5385527
theorem B1591607 : Blo 1060614 1591607 := bstep (se 1 (by rfl) ⟨1193705, by rfl⟩ : syracuseStep 1591607 = 2387411) B2387411
theorem B12110147 : Blo 1060614 12110147 := bstep (se 1 (by rfl) ⟨9082610, by rfl⟩ : syracuseStep 12110147 = 18165221) B18165221
theorem B1591787 : Blo 1060614 1591787 := bstep (se 1 (by rfl) ⟨1193840, by rfl⟩ : syracuseStep 1591787 = 2387681) B2387681
theorem B1592027 : Blo 1060614 1592027 := bstep (se 1 (by rfl) ⟨1194020, by rfl⟩ : syracuseStep 1592027 = 2388041) B2388041
theorem B1592063 : Blo 1060614 1592063 := bstep (se 1 (by rfl) ⟨1194047, by rfl⟩ : syracuseStep 1592063 = 2388095) B2388095
theorem B2018047 : Blo 1060614 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B5098247 : Blo 1060614 5098247 := bstep (se 1 (by rfl) ⟨3823685, by rfl⟩ : syracuseStep 5098247 = 7647371) B7647371
theorem B1592783 : Blo 1060614 1592783 := bstep (se 1 (by rfl) ⟨1194587, by rfl⟩ : syracuseStep 1592783 = 2389175) B2389175
theorem B1592873 : Blo 1060614 1592873 := bstep (se 2 (by rfl) ⟨597327, by rfl⟩ : syracuseStep 1592873 = 1194655) B1194655
theorem B3886703 : Blo 1060614 3886703 := bstep (se 1 (by rfl) ⟨2915027, by rfl⟩ : syracuseStep 3886703 = 5830055) B5830055
theorem B65326763 : Blo 1060614 65326763 := bstep (se 1 (by rfl) ⟨48995072, by rfl⟩ : syracuseStep 65326763 = 97990145) B97990145
theorem B3231463 : Blo 1060614 3231463 := bstep (se 1 (by rfl) ⟨2423597, by rfl⟩ : syracuseStep 3231463 = 4847195) B4847195
theorem B1593167 : Blo 1060614 1593167 := bstep (se 1 (by rfl) ⟨1194875, by rfl⟩ : syracuseStep 1593167 = 2389751) B2389751
theorem B1593287 : Blo 1060614 1593287 := bstep (se 1 (by rfl) ⟨1194965, by rfl⟩ : syracuseStep 1593287 = 2389931) B2389931
theorem B1593371 : Blo 1060614 1593371 := bstep (se 1 (by rfl) ⟨1195028, by rfl⟩ : syracuseStep 1593371 = 2390057) B2390057
theorem B3592295 : Blo 1060614 3592295 := bstep (se 1 (by rfl) ⟨2694221, by rfl⟩ : syracuseStep 3592295 = 5388443) B5388443
theorem B1724537 : Blo 1060614 1724537 := bstep (se 2 (by rfl) ⟨646701, by rfl⟩ : syracuseStep 1724537 = 1293403) B1293403
theorem B8081693 : Blo 1060614 8081693 := bstep (se 3 (by rfl) ⟨1515317, by rfl⟩ : syracuseStep 8081693 = 3030635) B3030635
theorem B1593647 : Blo 1060614 1593647 := bstep (se 1 (by rfl) ⟨1195235, by rfl⟩ : syracuseStep 1593647 = 2390471) B2390471
theorem B1790363 : Blo 1060614 1790363 := bstep (se 1 (by rfl) ⟨1342772, by rfl⟩ : syracuseStep 1790363 = 2685545) B2685545
theorem B1593755 : Blo 1060614 1593755 := bstep (se 1 (by rfl) ⟨1195316, by rfl⟩ : syracuseStep 1593755 = 2390633) B2390633
theorem B4084157 : Blo 1060614 4084157 := bstep (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) B1531559
theorem B1593791 : Blo 1060614 1593791 := bstep (se 1 (by rfl) ⟨1195343, by rfl⟩ : syracuseStep 1593791 = 2390687) B2390687
theorem B1593887 : Blo 1060614 1593887 := bstep (se 1 (by rfl) ⟨1195415, by rfl⟩ : syracuseStep 1593887 = 2390831) B2390831
theorem B33608371 : Blo 1060614 33608371 := bstep (se 1 (by rfl) ⟨25206278, by rfl⟩ : syracuseStep 33608371 = 50412557) B50412557
theorem B1594175 : Blo 1060614 1594175 := bstep (se 1 (by rfl) ⟨1195631, by rfl⟩ : syracuseStep 1594175 = 2391263) B2391263
theorem B1594319 : Blo 1060614 1594319 := bstep (se 1 (by rfl) ⟨1195739, by rfl⟩ : syracuseStep 1594319 = 2391479) B2391479
theorem B1594409 : Blo 1060614 1594409 := bstep (se 2 (by rfl) ⟨597903, by rfl⟩ : syracuseStep 1594409 = 1195807) B1195807
theorem B2020393 : Blo 1060614 2020393 := bstep (se 2 (by rfl) ⟨757647, by rfl⟩ : syracuseStep 2020393 = 1515295) B1515295
theorem B1594439 : Blo 1060614 1594439 := bstep (se 1 (by rfl) ⟨1195829, by rfl⟩ : syracuseStep 1594439 = 2391659) B2391659
theorem B1594619 : Blo 1060614 1594619 := bstep (se 1 (by rfl) ⟨1195964, by rfl⟩ : syracuseStep 1594619 = 2391929) B2391929
theorem B1594679 : Blo 1060614 1594679 := bstep (se 1 (by rfl) ⟨1196009, by rfl⟩ : syracuseStep 1594679 = 2392019) B2392019
theorem B1594985 : Blo 1060614 1594985 := bstep (se 2 (by rfl) ⟨598119, by rfl⟩ : syracuseStep 1594985 = 1196239) B1196239
theorem B1791679 : Blo 1060614 1791679 := bstep (se 1 (by rfl) ⟨1343759, by rfl⟩ : syracuseStep 1791679 = 2687519) B2687519
theorem B1595519 : Blo 1060614 1595519 := bstep (se 1 (by rfl) ⟨1196639, by rfl⟩ : syracuseStep 1595519 = 2393279) B2393279
theorem B1595615 : Blo 1060614 1595615 := bstep (se 1 (by rfl) ⟨1196711, by rfl⟩ : syracuseStep 1595615 = 2393423) B2393423
theorem B3070187 : Blo 1060614 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B1595675 : Blo 1060614 1595675 := bstep (se 1 (by rfl) ⟨1196756, by rfl⟩ : syracuseStep 1595675 = 2393513) B2393513
theorem B4545031 : Blo 1060614 4545031 := bstep (se 1 (by rfl) ⟨3408773, by rfl⟩ : syracuseStep 4545031 = 6817547) B6817547
theorem B1595999 : Blo 1060614 1595999 := bstep (se 1 (by rfl) ⟨1196999, by rfl⟩ : syracuseStep 1595999 = 2393999) B2393999
theorem B1596095 : Blo 1060614 1596095 := bstep (se 1 (by rfl) ⟨1197071, by rfl⟩ : syracuseStep 1596095 = 2394143) B2394143
theorem B1596137 : Blo 1060614 1596137 := bstep (se 2 (by rfl) ⟨598551, by rfl⟩ : syracuseStep 1596137 = 1197103) B1197103
theorem B1596263 : Blo 1060614 1596263 := bstep (se 1 (by rfl) ⟨1197197, by rfl⟩ : syracuseStep 1596263 = 2394395) B2394395
theorem B1596329 : Blo 1060614 1596329 := bstep (se 2 (by rfl) ⟨598623, by rfl⟩ : syracuseStep 1596329 = 1197247) B1197247
theorem B1596479 : Blo 1060614 1596479 := bstep (se 1 (by rfl) ⟨1197359, by rfl⟩ : syracuseStep 1596479 = 2394719) B2394719
theorem B1596521 : Blo 1060614 1596521 := bstep (se 2 (by rfl) ⟨598695, by rfl⟩ : syracuseStep 1596521 = 1197391) B1197391
theorem B1596647 : Blo 1060614 1596647 := bstep (se 1 (by rfl) ⟨1197485, by rfl⟩ : syracuseStep 1596647 = 2394971) B2394971
theorem B141712757 : Blo 1060614 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B1793407 : Blo 1060614 1793407 := bstep (se 1 (by rfl) ⟨1345055, by rfl⟩ : syracuseStep 1793407 = 2690111) B2690111
theorem B36789835 : Blo 1060614 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B27254393 : Blo 1060614 27254393 := bstep (se 2 (by rfl) ⟨10220397, by rfl⟩ : syracuseStep 27254393 = 20440795) B20440795
theorem B1794089 : Blo 1060614 1794089 := bstep (se 2 (by rfl) ⟨672783, by rfl⟩ : syracuseStep 1794089 = 1345567) B1345567
theorem B3400751 : Blo 1060614 3400751 := bstep (se 1 (by rfl) ⟨2550563, by rfl⟩ : syracuseStep 3400751 = 5101127) B5101127
theorem B58189099 : Blo 1060614 58189099 := bstep (se 1 (by rfl) ⟨43641824, by rfl⟩ : syracuseStep 58189099 = 87283649) B87283649
theorem B17229277 : Blo 1060614 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B10905947 : Blo 1060614 10905947 := bstep (se 1 (by rfl) ⟨8179460, by rfl⟩ : syracuseStep 10905947 = 16358921) B16358921
theorem B2156969 : Blo 1060614 2156969 := bstep (se 2 (by rfl) ⟨808863, by rfl⟩ : syracuseStep 2156969 = 1617727) B1617727
theorem B2386745 : Blo 1060614 2386745 := bstep (se 2 (by rfl) ⟨895029, by rfl⟩ : syracuseStep 2386745 = 1790059) B1790059
theorem B6057125 : Blo 1060614 6057125 := bstep (se 4 (by rfl) ⟨567855, by rfl⟩ : syracuseStep 6057125 = 1135711) B1135711
theorem B2387375 : Blo 1060614 2387375 := bstep (se 1 (by rfl) ⟨1790531, by rfl⟩ : syracuseStep 2387375 = 3581063) B3581063
theorem B2387627 : Blo 1060614 2387627 := bstep (se 1 (by rfl) ⟨1790720, by rfl⟩ : syracuseStep 2387627 = 3581441) B3581441
theorem B104656643 : Blo 1060614 104656643 := bstep (se 1 (by rfl) ⟨78492482, by rfl⟩ : syracuseStep 104656643 = 156984965) B156984965
theorem B2420891 : Blo 1060614 2420891 := bstep (se 1 (by rfl) ⟨1815668, by rfl⟩ : syracuseStep 2420891 = 3631337) B3631337
theorem B2388167 : Blo 1060614 2388167 := bstep (se 1 (by rfl) ⟨1791125, by rfl⟩ : syracuseStep 2388167 = 3582251) B3582251
theorem B18936017 : Blo 1060614 18936017 := bstep (se 2 (by rfl) ⟨7101006, by rfl⟩ : syracuseStep 18936017 = 14202013) B14202013
theorem B3633427 : Blo 1060614 3633427 := bstep (se 1 (by rfl) ⟨2725070, by rfl⟩ : syracuseStep 3633427 = 5450141) B5450141
theorem B5370137 : Blo 1060614 5370137 := bstep (se 2 (by rfl) ⟨2013801, by rfl⟩ : syracuseStep 5370137 = 4027603) B4027603
theorem B43544947 : Blo 1060614 43544947 := bstep (se 1 (by rfl) ⟨32658710, by rfl⟩ : syracuseStep 43544947 = 65317421) B65317421
theorem B2388347 : Blo 1060614 2388347 := bstep (se 1 (by rfl) ⟨1791260, by rfl⟩ : syracuseStep 2388347 = 3582521) B3582521
theorem B5370299 : Blo 1060614 5370299 := bstep (se 1 (by rfl) ⟨4027724, by rfl⟩ : syracuseStep 5370299 = 8055449) B8055449
theorem B2388617 : Blo 1060614 2388617 := bstep (se 2 (by rfl) ⟨895731, by rfl⟩ : syracuseStep 2388617 = 1791463) B1791463
theorem B2388833 : Blo 1060614 2388833 := bstep (se 2 (by rfl) ⟨895812, by rfl⟩ : syracuseStep 2388833 = 1791625) B1791625
theorem B3404699 : Blo 1060614 3404699 := bstep (se 1 (by rfl) ⟨2553524, by rfl⟩ : syracuseStep 3404699 = 5107049) B5107049
theorem B2913533 : Blo 1060614 2913533 := bstep (se 3 (by rfl) ⟨546287, by rfl⟩ : syracuseStep 2913533 = 1092575) B1092575
theorem B2389355 : Blo 1060614 2389355 := bstep (se 1 (by rfl) ⟨1792016, by rfl⟩ : syracuseStep 2389355 = 3584033) B3584033
theorem B2389607 : Blo 1060614 2389607 := bstep (se 1 (by rfl) ⟨1792205, by rfl⟩ : syracuseStep 2389607 = 3584411) B3584411
theorem B2389625 : Blo 1060614 2389625 := bstep (se 2 (by rfl) ⟨896109, by rfl⟩ : syracuseStep 2389625 = 1792219) B1792219
theorem B12121811 : Blo 1060614 12121811 := bstep (se 1 (by rfl) ⟨9091358, by rfl⟩ : syracuseStep 12121811 = 18182717) B18182717
theorem B6453053 : Blo 1060614 6453053 := bstep (se 3 (by rfl) ⟨1209947, by rfl⟩ : syracuseStep 6453053 = 2419895) B2419895
theorem B2389985 : Blo 1060614 2389985 := bstep (se 2 (by rfl) ⟨896244, by rfl⟩ : syracuseStep 2389985 = 1792489) B1792489
theorem B27228149 : Blo 1060614 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B2390183 : Blo 1060614 2390183 := bstep (se 1 (by rfl) ⟨1792637, by rfl⟩ : syracuseStep 2390183 = 3585275) B3585275
theorem B3832103 : Blo 1060614 3832103 := bstep (se 1 (by rfl) ⟨2874077, by rfl⟩ : syracuseStep 3832103 = 5748155) B5748155
theorem B6224339 : Blo 1060614 6224339 := bstep (se 1 (by rfl) ⟨4668254, by rfl⟩ : syracuseStep 6224339 = 9336509) B9336509
theorem B5110739 : Blo 1060614 5110739 := bstep (se 1 (by rfl) ⟨3833054, by rfl⟩ : syracuseStep 5110739 = 7666109) B7666109
theorem B2685919 : Blo 1060614 2685919 := bstep (se 1 (by rfl) ⟨2014439, by rfl⟩ : syracuseStep 2685919 = 4028879) B4028879
theorem B1702939 : Blo 1060614 1702939 := bstep (se 1 (by rfl) ⟨1277204, by rfl⟩ : syracuseStep 1702939 = 2554409) B2554409
theorem B5373053 : Blo 1060614 5373053 := bstep (se 3 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 5373053 = 2014895) B2014895
theorem B6815087 : Blo 1060614 6815087 := bstep (se 1 (by rfl) ⟨5111315, by rfl⟩ : syracuseStep 6815087 = 10222631) B10222631
theorem B5373863 : Blo 1060614 5373863 := bstep (se 1 (by rfl) ⟨4030397, by rfl⟩ : syracuseStep 5373863 = 8060795) B8060795
theorem B2687327 : Blo 1060614 2687327 := bstep (se 1 (by rfl) ⟨2015495, by rfl⟩ : syracuseStep 2687327 = 4030991) B4030991
theorem B3408979 : Blo 1060614 3408979 := bstep (se 1 (by rfl) ⟨2556734, by rfl⟩ : syracuseStep 3408979 = 5113469) B5113469
theorem B2688167 : Blo 1060614 2688167 := bstep (se 1 (by rfl) ⟨2016125, by rfl⟩ : syracuseStep 2688167 = 4032251) B4032251
theorem B14550353 : Blo 1060614 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B2393567 : Blo 1060614 2393567 := bstep (se 1 (by rfl) ⟨1795175, by rfl⟩ : syracuseStep 2393567 = 3590351) B3590351
theorem B8062739 : Blo 1060614 8062739 := bstep (se 1 (by rfl) ⟨6047054, by rfl⟩ : syracuseStep 8062739 = 12094109) B12094109
theorem B22972369 : Blo 1060614 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B7669799 : Blo 1060614 7669799 := bstep (se 1 (by rfl) ⟨5752349, by rfl⟩ : syracuseStep 7669799 = 11504699) B11504699
theorem B2722025 : Blo 1060614 2722025 := bstep (se 2 (by rfl) ⟨1020759, by rfl⟩ : syracuseStep 2722025 = 2041519) B2041519
theorem B8063225 : Blo 1060614 8063225 := bstep (se 2 (by rfl) ⟨3023709, by rfl⟩ : syracuseStep 8063225 = 6047419) B6047419
theorem B7670143 : Blo 1060614 7670143 := bstep (se 1 (by rfl) ⟨5752607, by rfl⟩ : syracuseStep 7670143 = 11505215) B11505215
theorem B2591135 : Blo 1060614 2591135 := bstep (se 1 (by rfl) ⟨1943351, by rfl⟩ : syracuseStep 2591135 = 3886703) B3886703
theorem B2394863 : Blo 1060614 2394863 := bstep (se 1 (by rfl) ⟨1796147, by rfl⟩ : syracuseStep 2394863 = 3592295) B3592295
theorem B1510255 : Blo 1060614 1510255 := bstep (se 1 (by rfl) ⟨1132691, by rfl⟩ : syracuseStep 1510255 = 2265383) B2265383
theorem B2722771 : Blo 1060614 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B2690729 : Blo 1060614 2690729 := bstep (se 2 (by rfl) ⟨1009023, by rfl⟩ : syracuseStep 2690729 = 2018047) B2018047
theorem B8064683 : Blo 1060614 8064683 := bstep (se 1 (by rfl) ⟨6048512, by rfl⟩ : syracuseStep 8064683 = 12097025) B12097025
theorem B26186273 : Blo 1060614 26186273 := bstep (se 2 (by rfl) ⟨9819852, by rfl⟩ : syracuseStep 26186273 = 19639705) B19639705
theorem B94475171 : Blo 1060614 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B1939169 : Blo 1060614 1939169 := bstep (se 2 (by rfl) ⟨727188, by rfl⟩ : syracuseStep 1939169 = 1454377) B1454377
theorem B3021113 : Blo 1060614 3021113 := bstep (se 2 (by rfl) ⟨1132917, by rfl⟩ : syracuseStep 3021113 = 2265835) B2265835
theorem B2693857 : Blo 1060614 2693857 := bstep (se 2 (by rfl) ⟨1010196, by rfl⟩ : syracuseStep 2693857 = 2020393) B2020393
theorem B49126445 : Blo 1060614 49126445 := bstep (se 3 (by rfl) ⟨9211208, by rfl⟩ : syracuseStep 49126445 = 18422417) B18422417
theorem B4038083 : Blo 1060614 4038083 := bstep (se 1 (by rfl) ⟨3028562, by rfl⟩ : syracuseStep 4038083 = 6057125) B6057125
theorem B4660861 : Blo 1060614 4660861 := bstep (se 3 (by rfl) ⟨873911, by rfl⟩ : syracuseStep 4660861 = 1747823) B1747823
theorem B69771095 : Blo 1060614 69771095 := bstep (se 1 (by rfl) ⟨52328321, by rfl⟩ : syracuseStep 69771095 = 104656643) B104656643
theorem B1613927 : Blo 1060614 1613927 := bstep (se 1 (by rfl) ⟨1210445, by rfl⟩ : syracuseStep 1613927 = 2420891) B2420891
theorem B12624011 : Blo 1060614 12624011 := bstep (se 1 (by rfl) ⟨9468008, by rfl⟩ : syracuseStep 12624011 = 18936017) B18936017
theorem B3580091 : Blo 1060614 3580091 := bstep (se 1 (by rfl) ⟨2685068, by rfl⟩ : syracuseStep 3580091 = 5370137) B5370137
theorem B3580199 : Blo 1060614 3580199 := bstep (se 1 (by rfl) ⟨2685149, by rfl⟩ : syracuseStep 3580199 = 5370299) B5370299
theorem B2269799 : Blo 1060614 2269799 := bstep (se 1 (by rfl) ⟨1702349, by rfl⟩ : syracuseStep 2269799 = 3404699) B3404699
theorem B1942355 : Blo 1060614 1942355 := bstep (se 1 (by rfl) ⟨1456766, by rfl⟩ : syracuseStep 1942355 = 2913533) B2913533
theorem B4302035 : Blo 1060614 4302035 := bstep (se 1 (by rfl) ⟨3226526, by rfl⟩ : syracuseStep 4302035 = 6453053) B6453053
theorem B3581225 : Blo 1060614 3581225 := bstep (se 2 (by rfl) ⟨1342959, by rfl⟩ : syracuseStep 3581225 = 2685919) B2685919
theorem B2270585 : Blo 1060614 2270585 := bstep (se 2 (by rfl) ⟨851469, by rfl⟩ : syracuseStep 2270585 = 1702939) B1702939
theorem B4531943 : Blo 1060614 4531943 := bstep (se 1 (by rfl) ⟨3398957, by rfl⟩ : syracuseStep 4531943 = 6797915) B6797915
theorem B174204701 : Blo 1060614 174204701 := bstep (se 3 (by rfl) ⟨32663381, by rfl⟩ : syracuseStep 174204701 = 65326763) B65326763
theorem B3582035 : Blo 1060614 3582035 := bstep (se 1 (by rfl) ⟨2686526, by rfl⟩ : syracuseStep 3582035 = 5373053) B5373053
theorem B4532543 : Blo 1060614 4532543 := bstep (se 1 (by rfl) ⟨3399407, by rfl⟩ : syracuseStep 4532543 = 6798815) B6798815
theorem B3582575 : Blo 1060614 3582575 := bstep (se 1 (by rfl) ⟨2686931, by rfl⟩ : syracuseStep 3582575 = 5373863) B5373863
theorem B4598765 : Blo 1060614 4598765 := bstep (se 3 (by rfl) ⟨862268, by rfl⟩ : syracuseStep 4598765 = 1724537) B1724537
theorem B10202219 : Blo 1060614 10202219 := bstep (se 1 (by rfl) ⟨7651664, by rfl⟩ : syracuseStep 10202219 = 15303329) B15303329
theorem B12922163 : Blo 1060614 12922163 := bstep (se 1 (by rfl) ⟨9691622, by rfl⟩ : syracuseStep 12922163 = 19383245) B19383245
theorem B7778297 : Blo 1060614 7778297 := bstep (se 2 (by rfl) ⟨2916861, by rfl⟩ : syracuseStep 7778297 = 5833723) B5833723
theorem B1060895 : Blo 1060614 1060895 := bstep (se 1 (by rfl) ⟨795671, by rfl⟩ : syracuseStep 1060895 = 1591343) B1591343
theorem B19378277 : Blo 1060614 19378277 := bstep (se 4 (by rfl) ⟨1816713, by rfl⟩ : syracuseStep 19378277 = 3633427) B3633427
theorem B2273447 : Blo 1060614 2273447 := bstep (se 1 (by rfl) ⟨1705085, by rfl⟩ : syracuseStep 2273447 = 3410171) B3410171
theorem B2273455 : Blo 1060614 2273455 := bstep (se 1 (by rfl) ⟨1705091, by rfl⟩ : syracuseStep 2273455 = 3410183) B3410183
theorem B1061071 : Blo 1060614 1061071 := bstep (se 1 (by rfl) ⟨795803, by rfl⟩ : syracuseStep 1061071 = 1591607) B1591607
theorem B8073431 : Blo 1060614 8073431 := bstep (se 1 (by rfl) ⟨6055073, by rfl⟩ : syracuseStep 8073431 = 12110147) B12110147
theorem B1061191 : Blo 1060614 1061191 := bstep (se 1 (by rfl) ⟨795893, by rfl⟩ : syracuseStep 1061191 = 1591787) B1591787
theorem B1061351 : Blo 1060614 1061351 := bstep (se 1 (by rfl) ⟨796013, by rfl⟩ : syracuseStep 1061351 = 1592027) B1592027
theorem B1061375 : Blo 1060614 1061375 := bstep (se 1 (by rfl) ⟨796031, by rfl⟩ : syracuseStep 1061375 = 1592063) B1592063
theorem B4305503 : Blo 1060614 4305503 := bstep (se 1 (by rfl) ⟨3229127, by rfl⟩ : syracuseStep 4305503 = 6458255) B6458255
theorem B1061855 : Blo 1060614 1061855 := bstep (se 1 (by rfl) ⟨796391, by rfl⟩ : syracuseStep 1061855 = 1592783) B1592783
theorem B1061915 : Blo 1060614 1061915 := bstep (se 1 (by rfl) ⟨796436, by rfl⟩ : syracuseStep 1061915 = 1592873) B1592873
theorem B55227581 : Blo 1060614 55227581 := bstep (se 3 (by rfl) ⟨10355171, by rfl⟩ : syracuseStep 55227581 = 20710343) B20710343
theorem B1062111 : Blo 1060614 1062111 := bstep (se 1 (by rfl) ⟨796583, by rfl⟩ : syracuseStep 1062111 = 1593167) B1593167
theorem B1062191 : Blo 1060614 1062191 := bstep (se 1 (by rfl) ⟨796643, by rfl⟩ : syracuseStep 1062191 = 1593287) B1593287
theorem B1062247 : Blo 1060614 1062247 := bstep (se 1 (by rfl) ⟨796685, by rfl⟩ : syracuseStep 1062247 = 1593371) B1593371
theorem B5387795 : Blo 1060614 5387795 := bstep (se 1 (by rfl) ⟨4040846, by rfl⟩ : syracuseStep 5387795 = 8081693) B8081693
theorem B1062431 : Blo 1060614 1062431 := bstep (se 1 (by rfl) ⟨796823, by rfl⟩ : syracuseStep 1062431 = 1593647) B1593647
theorem B1193575 : Blo 1060614 1193575 := bstep (se 1 (by rfl) ⟨895181, by rfl⟩ : syracuseStep 1193575 = 1790363) B1790363
theorem B1062503 : Blo 1060614 1062503 := bstep (se 1 (by rfl) ⟨796877, by rfl⟩ : syracuseStep 1062503 = 1593755) B1593755
theorem B1062527 : Blo 1060614 1062527 := bstep (se 1 (by rfl) ⟨796895, by rfl⟩ : syracuseStep 1062527 = 1593791) B1593791
theorem B1062591 : Blo 1060614 1062591 := bstep (se 1 (by rfl) ⟨796943, by rfl⟩ : syracuseStep 1062591 = 1593887) B1593887
theorem B1062783 : Blo 1060614 1062783 := bstep (se 1 (by rfl) ⟨797087, by rfl⟩ : syracuseStep 1062783 = 1594175) B1594175
theorem B1062879 : Blo 1060614 1062879 := bstep (se 1 (by rfl) ⟨797159, by rfl⟩ : syracuseStep 1062879 = 1594319) B1594319
theorem B1062939 : Blo 1060614 1062939 := bstep (se 1 (by rfl) ⟨797204, by rfl⟩ : syracuseStep 1062939 = 1594409) B1594409
theorem B1062959 : Blo 1060614 1062959 := bstep (se 1 (by rfl) ⟨797219, by rfl⟩ : syracuseStep 1062959 = 1594439) B1594439
theorem B1063079 : Blo 1060614 1063079 := bstep (se 1 (by rfl) ⟨797309, by rfl⟩ : syracuseStep 1063079 = 1594619) B1594619
theorem B1063119 : Blo 1060614 1063119 := bstep (se 1 (by rfl) ⟨797339, by rfl⟩ : syracuseStep 1063119 = 1594679) B1594679
theorem B1063323 : Blo 1060614 1063323 := bstep (se 1 (by rfl) ⟨797492, by rfl⟩ : syracuseStep 1063323 = 1594985) B1594985
theorem B1063679 : Blo 1060614 1063679 := bstep (se 1 (by rfl) ⟨797759, by rfl⟩ : syracuseStep 1063679 = 1595519) B1595519
theorem B1063743 : Blo 1060614 1063743 := bstep (se 1 (by rfl) ⟨797807, by rfl⟩ : syracuseStep 1063743 = 1595615) B1595615
theorem B2046791 : Blo 1060614 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B1063783 : Blo 1060614 1063783 := bstep (se 1 (by rfl) ⟨797837, by rfl⟩ : syracuseStep 1063783 = 1595675) B1595675
theorem B1063999 : Blo 1060614 1063999 := bstep (se 1 (by rfl) ⟨797999, by rfl⟩ : syracuseStep 1063999 = 1595999) B1595999
theorem B1064063 : Blo 1060614 1064063 := bstep (se 1 (by rfl) ⟨798047, by rfl⟩ : syracuseStep 1064063 = 1596095) B1596095
theorem B1064091 : Blo 1060614 1064091 := bstep (se 1 (by rfl) ⟨798068, by rfl⟩ : syracuseStep 1064091 = 1596137) B1596137
theorem B1064175 : Blo 1060614 1064175 := bstep (se 1 (by rfl) ⟨798131, by rfl⟩ : syracuseStep 1064175 = 1596263) B1596263
theorem B1064219 : Blo 1060614 1064219 := bstep (se 1 (by rfl) ⟨798164, by rfl⟩ : syracuseStep 1064219 = 1596329) B1596329
theorem B1064319 : Blo 1060614 1064319 := bstep (se 1 (by rfl) ⟨798239, by rfl⟩ : syracuseStep 1064319 = 1596479) B1596479
theorem B1064347 : Blo 1060614 1064347 := bstep (se 1 (by rfl) ⟨798260, by rfl⟩ : syracuseStep 1064347 = 1596521) B1596521
theorem B1064431 : Blo 1060614 1064431 := bstep (se 1 (by rfl) ⟨798323, by rfl⟩ : syracuseStep 1064431 = 1596647) B1596647
theorem B4308617 : Blo 1060614 4308617 := bstep (se 2 (by rfl) ⟨1615731, by rfl⟩ : syracuseStep 4308617 = 3231463) B3231463
theorem B27639539 : Blo 1060614 27639539 := bstep (se 1 (by rfl) ⟨20729654, by rfl⟩ : syracuseStep 27639539 = 41459309) B41459309
theorem B18169595 : Blo 1060614 18169595 := bstep (se 1 (by rfl) ⟨13627196, by rfl⟩ : syracuseStep 18169595 = 27254393) B27254393
theorem B1196059 : Blo 1060614 1196059 := bstep (se 1 (by rfl) ⟨897044, by rfl⟩ : syracuseStep 1196059 = 1794089) B1794089
theorem B3588407 : Blo 1060614 3588407 := bstep (se 1 (by rfl) ⟨2691305, by rfl⟩ : syracuseStep 3588407 = 5382611) B5382611
theorem B7651921 : Blo 1060614 7651921 := bstep (se 2 (by rfl) ⟨2869470, by rfl⟩ : syracuseStep 7651921 = 5738941) B5738941
theorem B98321201 : Blo 1060614 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B44811161 : Blo 1060614 44811161 := bstep (se 2 (by rfl) ⟨16804185, by rfl⟩ : syracuseStep 44811161 = 33608371) B33608371
theorem B17712229 : Blo 1060614 17712229 := bstep (se 4 (by rfl) ⟨1660521, by rfl⟩ : syracuseStep 17712229 = 3321043) B3321043
theorem B5751917 : Blo 1060614 5751917 := bstep (se 3 (by rfl) ⟨1078484, by rfl⟩ : syracuseStep 5751917 = 2156969) B2156969
theorem B3589487 : Blo 1060614 3589487 := bstep (se 1 (by rfl) ⟨2692115, by rfl⟩ : syracuseStep 3589487 = 5384231) B5384231
theorem B1590953 : Blo 1060614 1590953 := bstep (se 2 (by rfl) ⟨596607, by rfl⟩ : syracuseStep 1590953 = 1193215) B1193215
theorem B98158301 : Blo 1060614 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B1591163 : Blo 1060614 1591163 := bstep (se 1 (by rfl) ⟨1193372, by rfl⟩ : syracuseStep 1591163 = 2386745) B2386745
theorem B3590027 : Blo 1060614 3590027 := bstep (se 1 (by rfl) ⟨2692520, by rfl⟩ : syracuseStep 3590027 = 5385041) B5385041
theorem B1591583 : Blo 1060614 1591583 := bstep (se 1 (by rfl) ⟨1193687, by rfl⟩ : syracuseStep 1591583 = 2387375) B2387375
theorem B1591751 : Blo 1060614 1591751 := bstep (se 1 (by rfl) ⟨1193813, by rfl⟩ : syracuseStep 1591751 = 2387627) B2387627
theorem B58903109 : Blo 1060614 58903109 := bstep (se 4 (by rfl) ⟨5522166, by rfl⟩ : syracuseStep 58903109 = 11044333) B11044333
theorem B1592111 : Blo 1060614 1592111 := bstep (se 1 (by rfl) ⟨1194083, by rfl⟩ : syracuseStep 1592111 = 2388167) B2388167
theorem B1592231 : Blo 1060614 1592231 := bstep (se 1 (by rfl) ⟨1194173, by rfl⟩ : syracuseStep 1592231 = 2388347) B2388347
theorem B1592411 : Blo 1060614 1592411 := bstep (se 1 (by rfl) ⟨1194308, by rfl⟩ : syracuseStep 1592411 = 2388617) B2388617
theorem B2018495 : Blo 1060614 2018495 := bstep (se 1 (by rfl) ⟨1513871, by rfl⟩ : syracuseStep 2018495 = 3027743) B3027743
theorem B1592555 : Blo 1060614 1592555 := bstep (se 1 (by rfl) ⟨1194416, by rfl⟩ : syracuseStep 1592555 = 2388833) B2388833
theorem B4312415 : Blo 1060614 4312415 := bstep (se 1 (by rfl) ⟨3234311, by rfl⟩ : syracuseStep 4312415 = 6468623) B6468623
theorem B2018783 : Blo 1060614 2018783 := bstep (se 1 (by rfl) ⟨1514087, by rfl⟩ : syracuseStep 2018783 = 3028175) B3028175
theorem B1592903 : Blo 1060614 1592903 := bstep (se 1 (by rfl) ⟨1194677, by rfl⟩ : syracuseStep 1592903 = 2389355) B2389355
theorem B1593071 : Blo 1060614 1593071 := bstep (se 1 (by rfl) ⟨1194803, by rfl⟩ : syracuseStep 1593071 = 2389607) B2389607
theorem B1593083 : Blo 1060614 1593083 := bstep (se 1 (by rfl) ⟨1194812, by rfl⟩ : syracuseStep 1593083 = 2389625) B2389625
theorem B8081207 : Blo 1060614 8081207 := bstep (se 1 (by rfl) ⟨6060905, by rfl⟩ : syracuseStep 8081207 = 12121811) B12121811
theorem B1593257 : Blo 1060614 1593257 := bstep (se 2 (by rfl) ⟨597471, by rfl⟩ : syracuseStep 1593257 = 1194943) B1194943
theorem B1593323 : Blo 1060614 1593323 := bstep (se 1 (by rfl) ⟨1194992, by rfl⟩ : syracuseStep 1593323 = 2389985) B2389985
theorem B1593455 : Blo 1060614 1593455 := bstep (se 1 (by rfl) ⟨1195091, by rfl⟩ : syracuseStep 1593455 = 2390183) B2390183
theorem B4149559 : Blo 1060614 4149559 := bstep (se 1 (by rfl) ⟨3112169, by rfl⟩ : syracuseStep 4149559 = 6224339) B6224339
theorem B4543391 : Blo 1060614 4543391 := bstep (se 1 (by rfl) ⟨3407543, by rfl⟩ : syracuseStep 4543391 = 6815087) B6815087
theorem B1594361 : Blo 1060614 1594361 := bstep (se 2 (by rfl) ⟨597885, by rfl⟩ : syracuseStep 1594361 = 1195771) B1195771
theorem B16373515 : Blo 1060614 16373515 := bstep (se 1 (by rfl) ⟨12280136, by rfl⟩ : syracuseStep 16373515 = 24560273) B24560273
theorem B1595897 : Blo 1060614 1595897 := bstep (se 2 (by rfl) ⟨598461, by rfl⟩ : syracuseStep 1595897 = 1196923) B1196923
theorem B77585465 : Blo 1060614 77585465 := bstep (se 2 (by rfl) ⟨29094549, by rfl⟩ : syracuseStep 77585465 = 58189099) B58189099
theorem B1596527 : Blo 1060614 1596527 := bstep (se 1 (by rfl) ⟨1197395, by rfl⟩ : syracuseStep 1596527 = 2394791) B2394791
theorem B4545665 : Blo 1060614 4545665 := bstep (se 2 (by rfl) ⟨1704624, by rfl⟩ : syracuseStep 4545665 = 3409249) B3409249
theorem B3398831 : Blo 1060614 3398831 := bstep (se 1 (by rfl) ⟨2549123, by rfl⟩ : syracuseStep 3398831 = 5098247) B5098247
theorem B3824923 : Blo 1060614 3824923 := bstep (se 1 (by rfl) ⟨2868692, by rfl⟩ : syracuseStep 3824923 = 5737385) B5737385
theorem B1793515 : Blo 1060614 1793515 := bstep (se 1 (by rfl) ⟨1345136, by rfl⟩ : syracuseStep 1793515 = 2690273) B2690273
theorem B1596911 : Blo 1060614 1596911 := bstep (se 1 (by rfl) ⟨1197683, by rfl⟩ : syracuseStep 1596911 = 2395367) B2395367
theorem B1794143 : Blo 1060614 1794143 := bstep (se 1 (by rfl) ⟨1345607, by rfl⟩ : syracuseStep 1794143 = 2691215) B2691215
theorem B9068669 : Blo 1060614 9068669 := bstep (se 3 (by rfl) ⟨1700375, by rfl⟩ : syracuseStep 9068669 = 3400751) B3400751
theorem B1794953 : Blo 1060614 1794953 := bstep (se 2 (by rfl) ⟨673107, by rfl⟩ : syracuseStep 1794953 = 1346215) B1346215
theorem B6054983 : Blo 1060614 6054983 := bstep (se 1 (by rfl) ⟨4541237, by rfl⟩ : syracuseStep 6054983 = 9082475) B9082475
theorem B1795439 : Blo 1060614 1795439 := bstep (se 1 (by rfl) ⟨1346579, by rfl⟩ : syracuseStep 1795439 = 2693159) B2693159
theorem B3827519 : Blo 1060614 3827519 := bstep (se 1 (by rfl) ⟨2870639, by rfl⟩ : syracuseStep 3827519 = 5741279) B5741279
theorem B1795999 : Blo 1060614 1795999 := bstep (se 1 (by rfl) ⟨1346999, by rfl⟩ : syracuseStep 1795999 = 2693999) B2693999
theorem B1796431 : Blo 1060614 1796431 := bstep (se 1 (by rfl) ⟨1347323, by rfl⟩ : syracuseStep 1796431 = 2694647) B2694647
theorem B58059929 : Blo 1060614 58059929 := bstep (se 2 (by rfl) ⟨21772473, by rfl⟩ : syracuseStep 58059929 = 43544947) B43544947
theorem B7270631 : Blo 1060614 7270631 := bstep (se 1 (by rfl) ⟨5452973, by rfl⟩ : syracuseStep 7270631 = 10905947) B10905947
theorem B2388203 : Blo 1060614 2388203 := bstep (se 1 (by rfl) ⟨1791152, by rfl⟩ : syracuseStep 2388203 = 3582305) B3582305
theorem B2388905 : Blo 1060614 2388905 := bstep (se 2 (by rfl) ⟨895839, by rfl⟩ : syracuseStep 2388905 = 1791679) B1791679
theorem B7665185 : Blo 1060614 7665185 := bstep (se 2 (by rfl) ⟨2874444, by rfl⟩ : syracuseStep 7665185 = 5748889) B5748889
theorem B7763567 : Blo 1060614 7763567 := bstep (se 1 (by rfl) ⟨5822675, by rfl⟩ : syracuseStep 7763567 = 11645351) B11645351
theorem B6060041 : Blo 1060614 6060041 := bstep (se 2 (by rfl) ⟨2272515, by rfl⟩ : syracuseStep 6060041 = 4545031) B4545031
theorem B1227847889 : Blo 1060614 1227847889 := bstep (se 2 (by rfl) ⟨460442958, by rfl⟩ : syracuseStep 1227847889 = 920885917) B920885917
theorem B8059337 : Blo 1060614 8059337 := bstep (se 2 (by rfl) ⟨3022251, by rfl⟩ : syracuseStep 8059337 = 6044503) B6044503
theorem B2390507 : Blo 1060614 2390507 := bstep (se 1 (by rfl) ⟨1792880, by rfl⟩ : syracuseStep 2390507 = 3585761) B3585761
theorem B18152099 : Blo 1060614 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B2554735 : Blo 1060614 2554735 := bstep (se 1 (by rfl) ⟨1916051, by rfl⟩ : syracuseStep 2554735 = 3832103) B3832103
theorem B2391209 : Blo 1060614 2391209 := bstep (se 2 (by rfl) ⟨896703, by rfl⟩ : syracuseStep 2391209 = 1793407) B1793407
theorem B3407159 : Blo 1060614 3407159 := bstep (se 1 (by rfl) ⟨2555369, by rfl⟩ : syracuseStep 3407159 = 5110739) B5110739
theorem B4029851 : Blo 1060614 4029851 := bstep (se 1 (by rfl) ⟨3022388, by rfl⟩ : syracuseStep 4029851 = 6044777) B6044777
theorem B49053113 : Blo 1060614 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B2391839 : Blo 1060614 2391839 := bstep (se 1 (by rfl) ⟨1793879, by rfl⟩ : syracuseStep 2391839 = 3587759) B3587759
theorem B2392271 : Blo 1060614 2392271 := bstep (se 1 (by rfl) ⟨1794203, by rfl⟩ : syracuseStep 2392271 = 3588407) B3588407
theorem B6062525 : Blo 1060614 6062525 := bstep (se 3 (by rfl) ⟨1136723, by rfl⟩ : syracuseStep 6062525 = 2273447) B2273447
theorem B3834611 : Blo 1060614 3834611 := bstep (se 1 (by rfl) ⟨2875958, by rfl⟩ : syracuseStep 3834611 = 5751917) B5751917
theorem B9700235 : Blo 1060614 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B2392991 : Blo 1060614 2392991 := bstep (se 1 (by rfl) ⟨1794743, by rfl⟩ : syracuseStep 2392991 = 3589487) B3589487
theorem B65438867 : Blo 1060614 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B5375159 : Blo 1060614 5375159 := bstep (se 1 (by rfl) ⟨4031369, by rfl⟩ : syracuseStep 5375159 = 8062739) B8062739
theorem B2393351 : Blo 1060614 2393351 := bstep (se 1 (by rfl) ⟨1795013, by rfl⟩ : syracuseStep 2393351 = 3590027) B3590027
theorem B5113199 : Blo 1060614 5113199 := bstep (se 1 (by rfl) ⟨3834899, by rfl⟩ : syracuseStep 5113199 = 7669799) B7669799
theorem B5375483 : Blo 1060614 5375483 := bstep (se 1 (by rfl) ⟨4031612, by rfl⟩ : syracuseStep 5375483 = 8063225) B8063225
theorem B1345663 : Blo 1060614 1345663 := bstep (se 1 (by rfl) ⟨1009247, by rfl⟩ : syracuseStep 1345663 = 2018495) B2018495
theorem B5376455 : Blo 1060614 5376455 := bstep (se 1 (by rfl) ⟨4032341, by rfl⟩ : syracuseStep 5376455 = 8064683) B8064683
theorem B2394665 : Blo 1060614 2394665 := bstep (se 2 (by rfl) ⟨897999, by rfl⟩ : syracuseStep 2394665 = 1795999) B1795999
theorem B2395241 : Blo 1060614 2395241 := bstep (se 2 (by rfl) ⟨898215, by rfl⟩ : syracuseStep 2395241 = 1796431) B1796431
theorem B10226857 : Blo 1060614 10226857 := bstep (se 2 (by rfl) ⟨3835071, by rfl⟩ : syracuseStep 10226857 = 7670143) B7670143
theorem B2265887 : Blo 1060614 2265887 := bstep (se 1 (by rfl) ⟨1699415, by rfl⟩ : syracuseStep 2265887 = 3398831) B3398831
theorem B2692055 : Blo 1060614 2692055 := bstep (se 1 (by rfl) ⟨2019041, by rfl⟩ : syracuseStep 2692055 = 4038083) B4038083
theorem B1513199 : Blo 1060614 1513199 := bstep (se 1 (by rfl) ⟨1134899, by rfl⟩ : syracuseStep 1513199 = 2269799) B2269799
theorem B4036655 : Blo 1060614 4036655 := bstep (se 1 (by rfl) ⟨3027491, by rfl⟩ : syracuseStep 4036655 = 6054983) B6054983
theorem B1513723 : Blo 1060614 1513723 := bstep (se 1 (by rfl) ⟨1135292, by rfl⟩ : syracuseStep 1513723 = 2270585) B2270585
theorem B3021295 : Blo 1060614 3021295 := bstep (se 1 (by rfl) ⟨2265971, by rfl⟩ : syracuseStep 3021295 = 4531943) B4531943
theorem B116136467 : Blo 1060614 116136467 := bstep (se 1 (by rfl) ⟨87102350, by rfl⟩ : syracuseStep 116136467 = 174204701) B174204701
theorem B3021695 : Blo 1060614 3021695 := bstep (se 1 (by rfl) ⟨2266271, by rfl⟩ : syracuseStep 3021695 = 4532543) B4532543
theorem B21831353 : Blo 1060614 21831353 := bstep (se 2 (by rfl) ⟨8186757, by rfl⟩ : syracuseStep 21831353 = 16373515) B16373515
theorem B5185531 : Blo 1060614 5185531 := bstep (se 1 (by rfl) ⟨3889148, by rfl⟩ : syracuseStep 5185531 = 7778297) B7778297
theorem B12918851 : Blo 1060614 12918851 := bstep (se 1 (by rfl) ⟨9689138, by rfl⟩ : syracuseStep 12918851 = 19378277) B19378277
theorem B5382287 : Blo 1060614 5382287 := bstep (se 1 (by rfl) ⟨4036715, by rfl⟩ : syracuseStep 5382287 = 8073431) B8073431
theorem B5383421 : Blo 1060614 5383421 := bstep (se 3 (by rfl) ⟨1009391, by rfl⟩ : syracuseStep 5383421 = 2018783) B2018783
theorem B4040027 : Blo 1060614 4040027 := bstep (se 1 (by rfl) ⟨3030020, by rfl⟩ : syracuseStep 4040027 = 6060041) B6060041
theorem B12101399 : Blo 1060614 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B2271439 : Blo 1060614 2271439 := bstep (se 1 (by rfl) ⟨1703579, by rfl⟩ : syracuseStep 2271439 = 3407159) B3407159
theorem B18426359 : Blo 1060614 18426359 := bstep (se 1 (by rfl) ⟨13819769, by rfl⟩ : syracuseStep 18426359 = 27639539) B27639539
theorem B65547467 : Blo 1060614 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B10202561 : Blo 1060614 10202561 := bstep (se 2 (by rfl) ⟨3825960, by rfl⟩ : syracuseStep 10202561 = 7651921) B7651921
theorem B1060635 : Blo 1060614 1060635 := bstep (se 1 (by rfl) ⟨795476, by rfl⟩ : syracuseStep 1060635 = 1590953) B1590953
theorem B1060775 : Blo 1060614 1060775 := bstep (se 1 (by rfl) ⟨795581, by rfl⟩ : syracuseStep 1060775 = 1591163) B1591163
theorem B1814683 : Blo 1060614 1814683 := bstep (se 1 (by rfl) ⟨1361012, by rfl⟩ : syracuseStep 1814683 = 2722025) B2722025
theorem B1061055 : Blo 1060614 1061055 := bstep (se 1 (by rfl) ⟨795791, by rfl⟩ : syracuseStep 1061055 = 1591583) B1591583
theorem B1061167 : Blo 1060614 1061167 := bstep (se 1 (by rfl) ⟨795875, by rfl⟩ : syracuseStep 1061167 = 1591751) B1591751
theorem B39268739 : Blo 1060614 39268739 := bstep (se 1 (by rfl) ⟨29451554, by rfl⟩ : syracuseStep 39268739 = 58903109) B58903109
theorem B1061407 : Blo 1060614 1061407 := bstep (se 1 (by rfl) ⟨796055, by rfl⟩ : syracuseStep 1061407 = 1592111) B1592111
theorem B1061487 : Blo 1060614 1061487 := bstep (se 1 (by rfl) ⟨796115, by rfl⟩ : syracuseStep 1061487 = 1592231) B1592231
theorem B1061607 : Blo 1060614 1061607 := bstep (se 1 (by rfl) ⟨796205, by rfl⟩ : syracuseStep 1061607 = 1592411) B1592411
theorem B1061703 : Blo 1060614 1061703 := bstep (se 1 (by rfl) ⟨796277, by rfl⟩ : syracuseStep 1061703 = 1592555) B1592555
theorem B1061935 : Blo 1060614 1061935 := bstep (se 1 (by rfl) ⟨796451, by rfl⟩ : syracuseStep 1061935 = 1592903) B1592903
theorem B251933789 : Blo 1060614 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B1062047 : Blo 1060614 1062047 := bstep (se 1 (by rfl) ⟨796535, by rfl⟩ : syracuseStep 1062047 = 1593071) B1593071
theorem B1062055 : Blo 1060614 1062055 := bstep (se 1 (by rfl) ⟨796541, by rfl⟩ : syracuseStep 1062055 = 1593083) B1593083
theorem B5387471 : Blo 1060614 5387471 := bstep (se 1 (by rfl) ⟨4040603, by rfl⟩ : syracuseStep 5387471 = 8081207) B8081207
theorem B1062171 : Blo 1060614 1062171 := bstep (se 1 (by rfl) ⟨796628, by rfl⟩ : syracuseStep 1062171 = 1593257) B1593257
theorem B1062215 : Blo 1060614 1062215 := bstep (se 1 (by rfl) ⟨796661, by rfl⟩ : syracuseStep 1062215 = 1593323) B1593323
theorem B1062303 : Blo 1060614 1062303 := bstep (se 1 (by rfl) ⟨796727, by rfl⟩ : syracuseStep 1062303 = 1593455) B1593455
theorem B3028927 : Blo 1060614 3028927 := bstep (se 1 (by rfl) ⟨2271695, by rfl⟩ : syracuseStep 3028927 = 4543391) B4543391
theorem B1062907 : Blo 1060614 1062907 := bstep (se 1 (by rfl) ⟨797180, by rfl⟩ : syracuseStep 1062907 = 1594361) B1594361
theorem B2013673 : Blo 1060614 2013673 := bstep (se 2 (by rfl) ⟨755127, by rfl⟩ : syracuseStep 2013673 = 1510255) B1510255
theorem B1292779 : Blo 1060614 1292779 := bstep (se 1 (by rfl) ⟨969584, by rfl⟩ : syracuseStep 1292779 = 1939169) B1939169
theorem B2014075 : Blo 1060614 2014075 := bstep (se 1 (by rfl) ⟨1510556, by rfl⟩ : syracuseStep 2014075 = 3021113) B3021113
theorem B1063931 : Blo 1060614 1063931 := bstep (se 1 (by rfl) ⟨797948, by rfl⟩ : syracuseStep 1063931 = 1595897) B1595897
theorem B32750963 : Blo 1060614 32750963 := bstep (se 1 (by rfl) ⟨24563222, by rfl⟩ : syracuseStep 32750963 = 49126445) B49126445
theorem B51723643 : Blo 1060614 51723643 := bstep (se 1 (by rfl) ⟨38792732, by rfl⟩ : syracuseStep 51723643 = 77585465) B77585465
theorem B1064351 : Blo 1060614 1064351 := bstep (se 1 (by rfl) ⟨798263, by rfl⟩ : syracuseStep 1064351 = 1596527) B1596527
theorem B3030443 : Blo 1060614 3030443 := bstep (se 1 (by rfl) ⟨2272832, by rfl⟩ : syracuseStep 3030443 = 4545665) B4545665
theorem B1064607 : Blo 1060614 1064607 := bstep (se 1 (by rfl) ⟨798455, by rfl⟩ : syracuseStep 1064607 = 1596911) B1596911
theorem B46514063 : Blo 1060614 46514063 := bstep (se 1 (by rfl) ⟨34885547, by rfl⟩ : syracuseStep 46514063 = 69771095) B69771095
theorem B1196095 : Blo 1060614 1196095 := bstep (se 1 (by rfl) ⟨897071, by rfl⟩ : syracuseStep 1196095 = 1794143) B1794143
theorem B6045779 : Blo 1060614 6045779 := bstep (se 1 (by rfl) ⟨4534334, by rfl⟩ : syracuseStep 6045779 = 9068669) B9068669
theorem B3031273 : Blo 1060614 3031273 := bstep (se 2 (by rfl) ⟨1136727, by rfl⟩ : syracuseStep 3031273 = 2273455) B2273455
theorem B1294903 : Blo 1060614 1294903 := bstep (se 1 (by rfl) ⟨971177, by rfl⟩ : syracuseStep 1294903 = 1942355) B1942355
theorem B1196635 : Blo 1060614 1196635 := bstep (se 1 (by rfl) ⟨897476, by rfl⟩ : syracuseStep 1196635 = 1794953) B1794953
theorem B2868023 : Blo 1060614 2868023 := bstep (se 1 (by rfl) ⟨2151017, by rfl⟩ : syracuseStep 2868023 = 4302035) B4302035
theorem B1196959 : Blo 1060614 1196959 := bstep (se 1 (by rfl) ⟨897719, by rfl⟩ : syracuseStep 1196959 = 1795439) B1795439
theorem B3065843 : Blo 1060614 3065843 := bstep (se 1 (by rfl) ⟨2299382, by rfl⟩ : syracuseStep 3065843 = 4598765) B4598765
theorem B6801479 : Blo 1060614 6801479 := bstep (se 1 (by rfl) ⟨5101109, by rfl⟩ : syracuseStep 6801479 = 10202219) B10202219
theorem B1591433 : Blo 1060614 1591433 := bstep (se 2 (by rfl) ⟨596787, by rfl⟩ : syracuseStep 1591433 = 1193575) B1193575
theorem B1592135 : Blo 1060614 1592135 := bstep (se 1 (by rfl) ⟨1194101, by rfl⟩ : syracuseStep 1592135 = 2388203) B2388203
theorem B2870335 : Blo 1060614 2870335 := bstep (se 1 (by rfl) ⟨2152751, by rfl⟩ : syracuseStep 2870335 = 4305503) B4305503
theorem B1592603 : Blo 1060614 1592603 := bstep (se 1 (by rfl) ⟨1194452, by rfl⟩ : syracuseStep 1592603 = 2388905) B2388905
theorem B36818387 : Blo 1060614 36818387 := bstep (se 1 (by rfl) ⟨27613790, by rfl⟩ : syracuseStep 36818387 = 55227581) B55227581
theorem B3591809 : Blo 1060614 3591809 := bstep (se 2 (by rfl) ⟨1346928, by rfl⟩ : syracuseStep 3591809 = 2693857) B2693857
theorem B3591863 : Blo 1060614 3591863 := bstep (se 1 (by rfl) ⟨2693897, by rfl⟩ : syracuseStep 3591863 = 5387795) B5387795
theorem B818565259 : Blo 1060614 818565259 := bstep (se 1 (by rfl) ⟨613923944, by rfl⟩ : syracuseStep 818565259 = 1227847889) B1227847889
theorem B1593671 : Blo 1060614 1593671 := bstep (se 1 (by rfl) ⟨1195253, by rfl⟩ : syracuseStep 1593671 = 2390507) B2390507
theorem B5099897 : Blo 1060614 5099897 := bstep (se 2 (by rfl) ⟨1912461, by rfl⟩ : syracuseStep 5099897 = 3824923) B3824923
theorem B1364527 : Blo 1060614 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B1594139 : Blo 1060614 1594139 := bstep (se 1 (by rfl) ⟨1195604, by rfl⟩ : syracuseStep 1594139 = 2391209) B2391209
theorem B6214481 : Blo 1060614 6214481 := bstep (se 2 (by rfl) ⟨2330430, by rfl⟩ : syracuseStep 6214481 = 4660861) B4660861
theorem B2872411 : Blo 1060614 2872411 := bstep (se 1 (by rfl) ⟨2154308, by rfl⟩ : syracuseStep 2872411 = 4308617) B4308617
theorem B12113063 : Blo 1060614 12113063 := bstep (se 1 (by rfl) ⟨9084797, by rfl⟩ : syracuseStep 12113063 = 18169595) B18169595
theorem B1594559 : Blo 1060614 1594559 := bstep (se 1 (by rfl) ⟨1195919, by rfl⟩ : syracuseStep 1594559 = 2391839) B2391839
theorem B1594745 : Blo 1060614 1594745 := bstep (se 2 (by rfl) ⟨598029, by rfl⟩ : syracuseStep 1594745 = 1196059) B1196059
theorem B1791551 : Blo 1060614 1791551 := bstep (se 1 (by rfl) ⟨1343663, by rfl⟩ : syracuseStep 1791551 = 2687327) B2687327
theorem B29874107 : Blo 1060614 29874107 := bstep (se 1 (by rfl) ⟨22405580, by rfl⟩ : syracuseStep 29874107 = 44811161) B44811161
theorem B1792111 : Blo 1060614 1792111 := bstep (se 1 (by rfl) ⟨1344083, by rfl⟩ : syracuseStep 1792111 = 2688167) B2688167
theorem B1595711 : Blo 1060614 1595711 := bstep (se 1 (by rfl) ⟨1196783, by rfl⟩ : syracuseStep 1595711 = 2393567) B2393567
theorem B4545305 : Blo 1060614 4545305 := bstep (se 2 (by rfl) ⟨1704489, by rfl⟩ : syracuseStep 4545305 = 3408979) B3408979
theorem B23616305 : Blo 1060614 23616305 := bstep (se 2 (by rfl) ⟨8856114, by rfl⟩ : syracuseStep 23616305 = 17712229) B17712229
theorem B1727423 : Blo 1060614 1727423 := bstep (se 1 (by rfl) ⟨1295567, by rfl⟩ : syracuseStep 1727423 = 2591135) B2591135
theorem B1596575 : Blo 1060614 1596575 := bstep (se 1 (by rfl) ⟨1197431, by rfl⟩ : syracuseStep 1596575 = 2394863) B2394863
theorem B2874943 : Blo 1060614 2874943 := bstep (se 1 (by rfl) ⟨2156207, by rfl⟩ : syracuseStep 2874943 = 4312415) B4312415
theorem B1793819 : Blo 1060614 1793819 := bstep (se 1 (by rfl) ⟨1345364, by rfl⟩ : syracuseStep 1793819 = 2690729) B2690729
theorem B30629825 : Blo 1060614 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B17457515 : Blo 1060614 17457515 := bstep (se 1 (by rfl) ⟨13093136, by rfl⟩ : syracuseStep 17457515 = 26186273) B26186273
theorem B3630361 : Blo 1060614 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B20702845 : Blo 1060614 20702845 := bstep (se 3 (by rfl) ⟨3881783, by rfl⟩ : syracuseStep 20702845 = 7763567) B7763567
theorem B1075951 : Blo 1060614 1075951 := bstep (se 1 (by rfl) ⟨806963, by rfl⟩ : syracuseStep 1075951 = 1613927) B1613927
theorem B8416007 : Blo 1060614 8416007 := bstep (se 1 (by rfl) ⟨6312005, by rfl⟩ : syracuseStep 8416007 = 12624011) B12624011
theorem B2386727 : Blo 1060614 2386727 := bstep (se 1 (by rfl) ⟨1790045, by rfl⟩ : syracuseStep 2386727 = 3580091) B3580091
theorem B2386799 : Blo 1060614 2386799 := bstep (se 1 (by rfl) ⟨1790099, by rfl⟩ : syracuseStep 2386799 = 3580199) B3580199
theorem B5532745 : Blo 1060614 5532745 := bstep (se 2 (by rfl) ⟨2074779, by rfl⟩ : syracuseStep 5532745 = 4149559) B4149559
theorem B2387483 : Blo 1060614 2387483 := bstep (se 1 (by rfl) ⟨1790612, by rfl⟩ : syracuseStep 2387483 = 3581225) B3581225
theorem B2551679 : Blo 1060614 2551679 := bstep (se 1 (by rfl) ⟨1913759, by rfl⟩ : syracuseStep 2551679 = 3827519) B3827519
theorem B2388023 : Blo 1060614 2388023 := bstep (se 1 (by rfl) ⟨1791017, by rfl⟩ : syracuseStep 2388023 = 3582035) B3582035
theorem B2388383 : Blo 1060614 2388383 := bstep (se 1 (by rfl) ⟨1791287, by rfl⟩ : syracuseStep 2388383 = 3582575) B3582575
theorem B8614775 : Blo 1060614 8614775 := bstep (se 1 (by rfl) ⟨6461081, by rfl⟩ : syracuseStep 8614775 = 12922163) B12922163
theorem B4847087 : Blo 1060614 4847087 := bstep (se 1 (by rfl) ⟨3635315, by rfl⟩ : syracuseStep 4847087 = 7270631) B7270631
theorem B154826477 : Blo 1060614 154826477 := bstep (se 3 (by rfl) ⟨29029964, by rfl⟩ : syracuseStep 154826477 = 58059929) B58059929
theorem B5110123 : Blo 1060614 5110123 := bstep (se 1 (by rfl) ⟨3832592, by rfl⟩ : syracuseStep 5110123 = 7665185) B7665185
theorem B3406313 : Blo 1060614 3406313 := bstep (se 2 (by rfl) ⟨1277367, by rfl⟩ : syracuseStep 3406313 = 2554735) B2554735
theorem B5372891 : Blo 1060614 5372891 := bstep (se 1 (by rfl) ⟨4029668, by rfl⟩ : syracuseStep 5372891 = 8059337) B8059337
theorem B2391353 : Blo 1060614 2391353 := bstep (se 2 (by rfl) ⟨896757, by rfl⟩ : syracuseStep 2391353 = 1793515) B1793515
theorem B2686567 : Blo 1060614 2686567 := bstep (se 1 (by rfl) ⟨2014925, by rfl⟩ : syracuseStep 2686567 = 4029851) B4029851
theorem B32702075 : Blo 1060614 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B4030519 : Blo 1060614 4030519 := bstep (se 1 (by rfl) ⟨3022889, by rfl⟩ : syracuseStep 4030519 = 6045779) B6045779
theorem B2556407 : Blo 1060614 2556407 := bstep (se 1 (by rfl) ⟨1917305, by rfl⟩ : syracuseStep 2556407 = 3834611) B3834611
theorem B3408799 : Blo 1060614 3408799 := bstep (se 1 (by rfl) ⟨2556599, by rfl⟩ : syracuseStep 3408799 = 5113199) B5113199
theorem B24545591 : Blo 1060614 24545591 := bstep (se 1 (by rfl) ⟨18409193, by rfl⟩ : syracuseStep 24545591 = 36818387) B36818387
theorem B2394539 : Blo 1060614 2394539 := bstep (se 1 (by rfl) ⟨1795904, by rfl⟩ : syracuseStep 2394539 = 3591809) B3591809
theorem B2394575 : Blo 1060614 2394575 := bstep (se 1 (by rfl) ⟨1795931, by rfl⟩ : syracuseStep 2394575 = 3591863) B3591863
theorem B1510591 : Blo 1060614 1510591 := bstep (se 1 (by rfl) ⟨1132943, by rfl⟩ : syracuseStep 1510591 = 2265887) B2265887
theorem B2691103 : Blo 1060614 2691103 := bstep (se 1 (by rfl) ⟨2018327, by rfl⟩ : syracuseStep 2691103 = 4036655) B4036655
theorem B7376993 : Blo 1060614 7376993 := bstep (se 2 (by rfl) ⟨2766372, by rfl⟩ : syracuseStep 7376993 = 5532745) B5532745
theorem B13635809 : Blo 1060614 13635809 := bstep (se 2 (by rfl) ⟨5113428, by rfl⟩ : syracuseStep 13635809 = 10226857) B10226857
theorem B4035197 : Blo 1060614 4035197 := bstep (se 3 (by rfl) ⟨756599, by rfl⟩ : syracuseStep 4035197 = 1513199) B1513199
theorem B1151615 : Blo 1060614 1151615 := bstep (se 1 (by rfl) ⟨863711, by rfl⟩ : syracuseStep 1151615 = 1727423) B1727423
theorem B14554235 : Blo 1060614 14554235 := bstep (se 1 (by rfl) ⟨10915676, by rfl⟩ : syracuseStep 14554235 = 21831353) B21831353
theorem B79664285 : Blo 1060614 79664285 := bstep (se 3 (by rfl) ⟨14937053, by rfl⟩ : syracuseStep 79664285 = 29874107) B29874107
theorem B20419883 : Blo 1060614 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B11638343 : Blo 1060614 11638343 := bstep (se 1 (by rfl) ⟨8728757, by rfl⟩ : syracuseStep 11638343 = 17457515) B17457515
theorem B15308453 : Blo 1060614 15308453 := bstep (se 4 (by rfl) ⟨1435167, by rfl⟩ : syracuseStep 15308453 = 2870335) B2870335
theorem B2693351 : Blo 1060614 2693351 := bstep (se 1 (by rfl) ⟨2020013, by rfl⟩ : syracuseStep 2693351 = 4040027) B4040027
theorem B8067599 : Blo 1060614 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B9083501 : Blo 1060614 9083501 := bstep (se 3 (by rfl) ⟨1703156, by rfl⟩ : syracuseStep 9083501 = 3406313) B3406313
theorem B5610671 : Blo 1060614 5610671 := bstep (se 1 (by rfl) ⟨4208003, by rfl⟩ : syracuseStep 5610671 = 8416007) B8416007
theorem B4038569 : Blo 1060614 4038569 := bstep (se 2 (by rfl) ⟨1514463, by rfl⟩ : syracuseStep 4038569 = 3028927) B3028927
theorem B5743183 : Blo 1060614 5743183 := bstep (se 1 (by rfl) ⟨4307387, by rfl⟩ : syracuseStep 5743183 = 8614775) B8614775
theorem B3581927 : Blo 1060614 3581927 := bstep (se 1 (by rfl) ⟨2686445, by rfl⟩ : syracuseStep 3581927 = 5372891) B5372891
theorem B3582089 : Blo 1060614 3582089 := bstep (se 2 (by rfl) ⟨1343283, by rfl⟩ : syracuseStep 3582089 = 2686567) B2686567
theorem B21833975 : Blo 1060614 21833975 := bstep (se 1 (by rfl) ⟨16375481, by rfl⟩ : syracuseStep 21833975 = 32750963) B32750963
theorem B21801383 : Blo 1060614 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B31009375 : Blo 1060614 31009375 := bstep (se 1 (by rfl) ⟨23257031, by rfl⟩ : syracuseStep 31009375 = 46514063) B46514063
theorem B4041683 : Blo 1060614 4041683 := bstep (se 1 (by rfl) ⟨3031262, by rfl⟩ : syracuseStep 4041683 = 6062525) B6062525
theorem B4041697 : Blo 1060614 4041697 := bstep (se 2 (by rfl) ⟨1515636, by rfl⟩ : syracuseStep 4041697 = 3031273) B3031273
theorem B1912015 : Blo 1060614 1912015 := bstep (se 1 (by rfl) ⟨1434011, by rfl⟩ : syracuseStep 1912015 = 2868023) B2868023
theorem B6466823 : Blo 1060614 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B43625911 : Blo 1060614 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B3583439 : Blo 1060614 3583439 := bstep (se 1 (by rfl) ⟨2687579, by rfl⟩ : syracuseStep 3583439 = 5375159) B5375159
theorem B3583655 : Blo 1060614 3583655 := bstep (se 1 (by rfl) ⟨2687741, by rfl⟩ : syracuseStep 3583655 = 5375483) B5375483
theorem B2043895 : Blo 1060614 2043895 := bstep (se 1 (by rfl) ⟨1532921, by rfl⟩ : syracuseStep 2043895 = 3065843) B3065843
theorem B4534319 : Blo 1060614 4534319 := bstep (se 1 (by rfl) ⟨3400739, by rfl⟩ : syracuseStep 4534319 = 6801479) B6801479
theorem B1060955 : Blo 1060614 1060955 := bstep (se 1 (by rfl) ⟨795716, by rfl⟩ : syracuseStep 1060955 = 1591433) B1591433
theorem B3584303 : Blo 1060614 3584303 := bstep (se 1 (by rfl) ⟨2688227, by rfl⟩ : syracuseStep 3584303 = 5376455) B5376455
theorem B1061423 : Blo 1060614 1061423 := bstep (se 1 (by rfl) ⟨796067, by rfl⟩ : syracuseStep 1061423 = 1592135) B1592135
theorem B27603793 : Blo 1060614 27603793 := bstep (se 2 (by rfl) ⟨10351422, by rfl⟩ : syracuseStep 27603793 = 20702845) B20702845
theorem B1061735 : Blo 1060614 1061735 := bstep (se 1 (by rfl) ⟨796301, by rfl⟩ : syracuseStep 1061735 = 1592603) B1592603
theorem B6894821 : Blo 1060614 6894821 := bstep (se 4 (by rfl) ⟨646389, by rfl⟩ : syracuseStep 6894821 = 1292779) B1292779
theorem B1062447 : Blo 1060614 1062447 := bstep (se 1 (by rfl) ⟨796835, by rfl⟩ : syracuseStep 1062447 = 1593671) B1593671
theorem B3028585 : Blo 1060614 3028585 := bstep (se 2 (by rfl) ⟨1135719, by rfl⟩ : syracuseStep 3028585 = 2271439) B2271439
theorem B1062759 : Blo 1060614 1062759 := bstep (se 1 (by rfl) ⟨797069, by rfl⟩ : syracuseStep 1062759 = 1594139) B1594139
theorem B4142987 : Blo 1060614 4142987 := bstep (se 1 (by rfl) ⟨3107240, by rfl⟩ : syracuseStep 4142987 = 6214481) B6214481
theorem B8075375 : Blo 1060614 8075375 := bstep (se 1 (by rfl) ⟨6056531, by rfl⟩ : syracuseStep 8075375 = 12113063) B12113063
theorem B1063039 : Blo 1060614 1063039 := bstep (se 1 (by rfl) ⟨797279, by rfl⟩ : syracuseStep 1063039 = 1594559) B1594559
theorem B1063163 : Blo 1060614 1063163 := bstep (se 1 (by rfl) ⟨797372, by rfl⟩ : syracuseStep 1063163 = 1594745) B1594745
theorem B1194367 : Blo 1060614 1194367 := bstep (se 1 (by rfl) ⟨895775, by rfl⟩ : syracuseStep 1194367 = 1791551) B1791551
theorem B12925565 : Blo 1060614 12925565 := bstep (se 3 (by rfl) ⟨2423543, by rfl⟩ : syracuseStep 12925565 = 4847087) B4847087
theorem B1063807 : Blo 1060614 1063807 := bstep (se 1 (by rfl) ⟨797855, by rfl⟩ : syracuseStep 1063807 = 1595711) B1595711
theorem B3030203 : Blo 1060614 3030203 := bstep (se 1 (by rfl) ⟨2272652, by rfl⟩ : syracuseStep 3030203 = 4545305) B4545305
theorem B15744203 : Blo 1060614 15744203 := bstep (se 1 (by rfl) ⟨11808152, by rfl⟩ : syracuseStep 15744203 = 23616305) B23616305
theorem B2014463 : Blo 1060614 2014463 := bstep (se 1 (by rfl) ⟨1510847, by rfl⟩ : syracuseStep 2014463 = 3021695) B3021695
theorem B1064383 : Blo 1060614 1064383 := bstep (se 1 (by rfl) ⟨798287, by rfl⟩ : syracuseStep 1064383 = 1596575) B1596575
theorem B1195879 : Blo 1060614 1195879 := bstep (se 1 (by rfl) ⟨896909, by rfl⟩ : syracuseStep 1195879 = 1793819) B1793819
theorem B3588191 : Blo 1060614 3588191 := bstep (se 1 (by rfl) ⟨2691143, by rfl⟩ : syracuseStep 3588191 = 5382287) B5382287
theorem B1091420345 : Blo 1060614 1091420345 := bstep (se 2 (by rfl) ⟨409282629, by rfl⟩ : syracuseStep 1091420345 = 818565259) B818565259
theorem B15319525 : Blo 1060614 15319525 := bstep (se 4 (by rfl) ⟨1436205, by rfl⟩ : syracuseStep 15319525 = 2872411) B2872411
theorem B1819369 : Blo 1060614 1819369 := bstep (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) B1364527
theorem B3588947 : Blo 1060614 3588947 := bstep (se 1 (by rfl) ⟨2691710, by rfl⟩ : syracuseStep 3588947 = 5383421) B5383421
theorem B1591151 : Blo 1060614 1591151 := bstep (se 1 (by rfl) ⟨1193363, by rfl⟩ : syracuseStep 1591151 = 2386727) B2386727
theorem B1591199 : Blo 1060614 1591199 := bstep (se 1 (by rfl) ⟨1193399, by rfl⟩ : syracuseStep 1591199 = 2386799) B2386799
theorem B43698311 : Blo 1060614 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B6801707 : Blo 1060614 6801707 := bstep (se 1 (by rfl) ⟨5101280, by rfl⟩ : syracuseStep 6801707 = 10202561) B10202561
theorem B1591655 : Blo 1060614 1591655 := bstep (se 1 (by rfl) ⟨1193741, by rfl⟩ : syracuseStep 1591655 = 2387483) B2387483
theorem B1592015 : Blo 1060614 1592015 := bstep (se 1 (by rfl) ⟨1194011, by rfl⟩ : syracuseStep 1592015 = 2388023) B2388023
theorem B1592255 : Blo 1060614 1592255 := bstep (se 1 (by rfl) ⟨1194191, by rfl⟩ : syracuseStep 1592255 = 2388383) B2388383
theorem B2018297 : Blo 1060614 2018297 := bstep (se 2 (by rfl) ⟨756861, by rfl⟩ : syracuseStep 2018297 = 1513723) B1513723
theorem B167955859 : Blo 1060614 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B3591647 : Blo 1060614 3591647 := bstep (se 1 (by rfl) ⟨2693735, by rfl⟩ : syracuseStep 3591647 = 5387471) B5387471
theorem B68964857 : Blo 1060614 68964857 := bstep (se 2 (by rfl) ⟨25861821, by rfl⟩ : syracuseStep 68964857 = 51723643) B51723643
theorem B1594235 : Blo 1060614 1594235 := bstep (se 1 (by rfl) ⟨1195676, by rfl⟩ : syracuseStep 1594235 = 2391353) B2391353
theorem B2020295 : Blo 1060614 2020295 := bstep (se 1 (by rfl) ⟨1515221, by rfl⟩ : syracuseStep 2020295 = 3030443) B3030443
theorem B1594793 : Blo 1060614 1594793 := bstep (se 2 (by rfl) ⟨598047, by rfl⟩ : syracuseStep 1594793 = 1196095) B1196095
theorem B1594847 : Blo 1060614 1594847 := bstep (se 1 (by rfl) ⟨1196135, by rfl⟩ : syracuseStep 1594847 = 2392271) B2392271
theorem B1595327 : Blo 1060614 1595327 := bstep (se 1 (by rfl) ⟨1196495, by rfl⟩ : syracuseStep 1595327 = 2392991) B2392991
theorem B1726537 : Blo 1060614 1726537 := bstep (se 2 (by rfl) ⟨647451, by rfl⟩ : syracuseStep 1726537 = 1294903) B1294903
theorem B1595513 : Blo 1060614 1595513 := bstep (se 2 (by rfl) ⟨598317, by rfl⟩ : syracuseStep 1595513 = 1196635) B1196635
theorem B1595567 : Blo 1060614 1595567 := bstep (se 1 (by rfl) ⟨1196675, by rfl⟩ : syracuseStep 1595567 = 2393351) B2393351
theorem B104716637 : Blo 1060614 104716637 := bstep (se 3 (by rfl) ⟨19634369, by rfl⟩ : syracuseStep 104716637 = 39268739) B39268739
theorem B1595945 : Blo 1060614 1595945 := bstep (se 2 (by rfl) ⟨598479, by rfl⟩ : syracuseStep 1595945 = 1196959) B1196959
theorem B1596443 : Blo 1060614 1596443 := bstep (se 1 (by rfl) ⟨1197332, by rfl⟩ : syracuseStep 1596443 = 2394665) B2394665
theorem B4840481 : Blo 1060614 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B1596827 : Blo 1060614 1596827 := bstep (se 1 (by rfl) ⟨1197620, by rfl⟩ : syracuseStep 1596827 = 2395241) B2395241
theorem B1794217 : Blo 1060614 1794217 := bstep (se 2 (by rfl) ⟨672831, by rfl⟩ : syracuseStep 1794217 = 1345663) B1345663
theorem B3399931 : Blo 1060614 3399931 := bstep (se 1 (by rfl) ⟨2549948, by rfl⟩ : syracuseStep 3399931 = 5099897) B5099897
theorem B1794703 : Blo 1060614 1794703 := bstep (se 1 (by rfl) ⟨1346027, by rfl⟩ : syracuseStep 1794703 = 2692055) B2692055
theorem B1434601 : Blo 1060614 1434601 := bstep (se 2 (by rfl) ⟨537975, by rfl⟩ : syracuseStep 1434601 = 1075951) B1075951
theorem B77424311 : Blo 1060614 77424311 := bstep (se 1 (by rfl) ⟨58068233, by rfl⟩ : syracuseStep 77424311 = 116136467) B116136467
theorem B8612567 : Blo 1060614 8612567 := bstep (se 1 (by rfl) ⟨6459425, by rfl⟩ : syracuseStep 8612567 = 12918851) B12918851
theorem B2419577 : Blo 1060614 2419577 := bstep (se 2 (by rfl) ⟨907341, by rfl⟩ : syracuseStep 2419577 = 1814683) B1814683
theorem B12284239 : Blo 1060614 12284239 := bstep (se 1 (by rfl) ⟨9213179, by rfl⟩ : syracuseStep 12284239 = 18426359) B18426359
theorem B1701119 : Blo 1060614 1701119 := bstep (se 1 (by rfl) ⟨1275839, by rfl⟩ : syracuseStep 1701119 = 2551679) B2551679
theorem B2389481 : Blo 1060614 2389481 := bstep (se 2 (by rfl) ⟨896055, by rfl⟩ : syracuseStep 2389481 = 1792111) B1792111
theorem B6813497 : Blo 1060614 6813497 := bstep (se 2 (by rfl) ⟨2555061, by rfl⟩ : syracuseStep 6813497 = 5110123) B5110123
theorem B2684897 : Blo 1060614 2684897 := bstep (se 2 (by rfl) ⟨1006836, by rfl⟩ : syracuseStep 2684897 = 2013673) B2013673
theorem B4028393 : Blo 1060614 4028393 := bstep (se 2 (by rfl) ⟨1510647, by rfl⟩ : syracuseStep 4028393 = 3021295) B3021295
theorem B103217651 : Blo 1060614 103217651 := bstep (se 1 (by rfl) ⟨77413238, by rfl⟩ : syracuseStep 103217651 = 154826477) B154826477
theorem B2685433 : Blo 1060614 2685433 := bstep (se 2 (by rfl) ⟨1007037, by rfl⟩ : syracuseStep 2685433 = 2014075) B2014075
theorem B3833257 : Blo 1060614 3833257 := bstep (se 2 (by rfl) ⟨1437471, by rfl⟩ : syracuseStep 3833257 = 2874943) B2874943
theorem B6914041 : Blo 1060614 6914041 := bstep (se 2 (by rfl) ⟨2592765, by rfl⟩ : syracuseStep 6914041 = 5185531) B5185531
theorem B2392127 : Blo 1060614 2392127 := bstep (se 1 (by rfl) ⟨1794095, by rfl⟩ : syracuseStep 2392127 = 3588191) B3588191
theorem B5374025 : Blo 1060614 5374025 := bstep (se 2 (by rfl) ⟨2015259, by rfl⟩ : syracuseStep 5374025 = 4030519) B4030519
theorem B727613563 : Blo 1060614 727613563 := bstep (se 1 (by rfl) ⟨545710172, by rfl⟩ : syracuseStep 727613563 = 1091420345) B1091420345
theorem B2392289 : Blo 1060614 2392289 := bstep (se 2 (by rfl) ⟨897108, by rfl⟩ : syracuseStep 2392289 = 1794217) B1794217
theorem B2392631 : Blo 1060614 2392631 := bstep (se 1 (by rfl) ⟨1794473, by rfl⟩ : syracuseStep 2392631 = 3588947) B3588947
theorem B2392937 : Blo 1060614 2392937 := bstep (se 2 (by rfl) ⟨897351, by rfl⟩ : syracuseStep 2392937 = 1794703) B1794703
theorem B2425825 : Blo 1060614 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B6817085 : Blo 1060614 6817085 := bstep (se 3 (by rfl) ⟨1278203, by rfl⟩ : syracuseStep 6817085 = 2556407) B2556407
theorem B29132207 : Blo 1060614 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B2394431 : Blo 1060614 2394431 := bstep (se 1 (by rfl) ⟨1795823, by rfl⟩ : syracuseStep 2394431 = 3591647) B3591647
theorem B4917995 : Blo 1060614 4917995 := bstep (se 1 (by rfl) ⟨3688496, by rfl⟩ : syracuseStep 4917995 = 7376993) B7376993
theorem B45976571 : Blo 1060614 45976571 := bstep (se 1 (by rfl) ⟨34482428, by rfl⟩ : syracuseStep 45976571 = 68964857) B68964857
theorem B2690131 : Blo 1060614 2690131 := bstep (se 1 (by rfl) ⟨2017598, by rfl⟩ : syracuseStep 2690131 = 4035197) B4035197
theorem B165383333 : Blo 1060614 165383333 := bstep (se 4 (by rfl) ⟨15504687, by rfl⟩ : syracuseStep 165383333 = 31009375) B31009375
theorem B1346863 : Blo 1060614 1346863 := bstep (se 1 (by rfl) ⟨1010147, by rfl⟩ : syracuseStep 1346863 = 2020295) B2020295
theorem B9702823 : Blo 1060614 9702823 := bstep (se 1 (by rfl) ⟨7277117, by rfl⟩ : syracuseStep 9702823 = 14554235) B14554235
theorem B31035581 : Blo 1060614 31035581 := bstep (se 3 (by rfl) ⟨5819171, by rfl⟩ : syracuseStep 31035581 = 11638343) B11638343
theorem B5378399 : Blo 1060614 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B223941145 : Blo 1060614 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B58167881 : Blo 1060614 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B3740447 : Blo 1060614 3740447 := bstep (se 1 (by rfl) ⟨2805335, by rfl⟩ : syracuseStep 3740447 = 5610671) B5610671
theorem B2692379 : Blo 1060614 2692379 := bstep (se 1 (by rfl) ⟨2019284, by rfl⟩ : syracuseStep 2692379 = 4038569) B4038569
theorem B2725193 : Blo 1060614 2725193 := bstep (se 2 (by rfl) ⟨1021947, by rfl⟩ : syracuseStep 2725193 = 2043895) B2043895
theorem B10197413 : Blo 1060614 10197413 := bstep (se 4 (by rfl) ⟨956007, by rfl⟩ : syracuseStep 10197413 = 1912015) B1912015
theorem B51616207 : Blo 1060614 51616207 := bstep (se 1 (by rfl) ⟨38712155, by rfl⟩ : syracuseStep 51616207 = 77424311) B77424311
theorem B5741711 : Blo 1060614 5741711 := bstep (se 1 (by rfl) ⟨4306283, by rfl⟩ : syracuseStep 5741711 = 8612567) B8612567
theorem B1613051 : Blo 1060614 1613051 := bstep (se 1 (by rfl) ⟨1209788, by rfl⟩ : syracuseStep 1613051 = 2419577) B2419577
theorem B2694455 : Blo 1060614 2694455 := bstep (se 1 (by rfl) ⟨2020841, by rfl⟩ : syracuseStep 2694455 = 4041683) B4041683
theorem B4038113 : Blo 1060614 4038113 := bstep (se 2 (by rfl) ⟨1514292, by rfl⟩ : syracuseStep 4038113 = 3028585) B3028585
theorem B5382125 : Blo 1060614 5382125 := bstep (se 3 (by rfl) ⟨1009148, by rfl⟩ : syracuseStep 5382125 = 2018297) B2018297
theorem B3022879 : Blo 1060614 3022879 := bstep (se 1 (by rfl) ⟨2267159, by rfl⟩ : syracuseStep 3022879 = 4534319) B4534319
theorem B2302049 : Blo 1060614 2302049 := bstep (se 2 (by rfl) ⟨863268, by rfl⟩ : syracuseStep 2302049 = 1726537) B1726537
theorem B3580577 : Blo 1060614 3580577 := bstep (se 2 (by rfl) ⟨1342716, by rfl⟩ : syracuseStep 3580577 = 2685433) B2685433
theorem B4596547 : Blo 1060614 4596547 := bstep (se 1 (by rfl) ⟨3447410, by rfl⟩ : syracuseStep 4596547 = 6894821) B6894821
theorem B2761991 : Blo 1060614 2761991 := bstep (se 1 (by rfl) ⟨2071493, by rfl⟩ : syracuseStep 2761991 = 4142987) B4142987
theorem B5383583 : Blo 1060614 5383583 := bstep (se 1 (by rfl) ⟨4037687, by rfl⟩ : syracuseStep 5383583 = 8075375) B8075375
theorem B10496135 : Blo 1060614 10496135 := bstep (se 1 (by rfl) ⟨7872101, by rfl⟩ : syracuseStep 10496135 = 15744203) B15744203
theorem B36874885 : Blo 1060614 36874885 := bstep (se 4 (by rfl) ⟨3457020, by rfl⟩ : syracuseStep 36874885 = 6914041) B6914041
theorem B4533241 : Blo 1060614 4533241 := bstep (se 2 (by rfl) ⟨1699965, by rfl⟩ : syracuseStep 4533241 = 3399931) B3399931
theorem B20426033 : Blo 1060614 20426033 := bstep (se 2 (by rfl) ⟨7659762, by rfl⟩ : syracuseStep 20426033 = 15319525) B15319525
theorem B1060767 : Blo 1060614 1060767 := bstep (se 1 (by rfl) ⟨795575, by rfl⟩ : syracuseStep 1060767 = 1591151) B1591151
theorem B1060799 : Blo 1060614 1060799 := bstep (se 1 (by rfl) ⟨795599, by rfl⟩ : syracuseStep 1060799 = 1591199) B1591199
theorem B4534471 : Blo 1060614 4534471 := bstep (se 1 (by rfl) ⟨3400853, by rfl⟩ : syracuseStep 4534471 = 6801707) B6801707
theorem B16363727 : Blo 1060614 16363727 := bstep (se 1 (by rfl) ⟨12272795, by rfl⟩ : syracuseStep 16363727 = 24545591) B24545591
theorem B1061103 : Blo 1060614 1061103 := bstep (se 1 (by rfl) ⟨795827, by rfl⟩ : syracuseStep 1061103 = 1591655) B1591655
theorem B1061343 : Blo 1060614 1061343 := bstep (se 1 (by rfl) ⟨796007, by rfl⟩ : syracuseStep 1061343 = 1592015) B1592015
theorem B1061503 : Blo 1060614 1061503 := bstep (se 1 (by rfl) ⟨796127, by rfl⟩ : syracuseStep 1061503 = 1592255) B1592255
theorem B9090539 : Blo 1060614 9090539 := bstep (se 1 (by rfl) ⟨6817904, by rfl⟩ : syracuseStep 9090539 = 13635809) B13635809
theorem B1062823 : Blo 1060614 1062823 := bstep (se 1 (by rfl) ⟨797117, by rfl⟩ : syracuseStep 1062823 = 1594235) B1594235
theorem B4536317 : Blo 1060614 4536317 := bstep (se 3 (by rfl) ⟨850559, by rfl⟩ : syracuseStep 4536317 = 1701119) B1701119
theorem B13613255 : Blo 1060614 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B1063195 : Blo 1060614 1063195 := bstep (se 1 (by rfl) ⟨797396, by rfl⟩ : syracuseStep 1063195 = 1594793) B1594793
theorem B1063231 : Blo 1060614 1063231 := bstep (se 1 (by rfl) ⟨797423, by rfl⟩ : syracuseStep 1063231 = 1594847) B1594847
theorem B1063551 : Blo 1060614 1063551 := bstep (se 1 (by rfl) ⟨797663, by rfl⟩ : syracuseStep 1063551 = 1595327) B1595327
theorem B5388929 : Blo 1060614 5388929 := bstep (se 2 (by rfl) ⟨2020848, by rfl⟩ : syracuseStep 5388929 = 4041697) B4041697
theorem B1063675 : Blo 1060614 1063675 := bstep (se 1 (by rfl) ⟨797756, by rfl⟩ : syracuseStep 1063675 = 1595513) B1595513
theorem B1063711 : Blo 1060614 1063711 := bstep (se 1 (by rfl) ⟨797783, by rfl⟩ : syracuseStep 1063711 = 1595567) B1595567
theorem B69811091 : Blo 1060614 69811091 := bstep (se 1 (by rfl) ⟨52358318, by rfl⟩ : syracuseStep 69811091 = 104716637) B104716637
theorem B2014121 : Blo 1060614 2014121 := bstep (se 2 (by rfl) ⟨755295, by rfl⟩ : syracuseStep 2014121 = 1510591) B1510591
theorem B1063963 : Blo 1060614 1063963 := bstep (se 1 (by rfl) ⟨797972, by rfl⟩ : syracuseStep 1063963 = 1595945) B1595945
theorem B1064295 : Blo 1060614 1064295 := bstep (se 1 (by rfl) ⟨798221, by rfl⟩ : syracuseStep 1064295 = 1596443) B1596443
theorem B3226987 : Blo 1060614 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B1064551 : Blo 1060614 1064551 := bstep (se 1 (by rfl) ⟨798413, by rfl⟩ : syracuseStep 1064551 = 1596827) B1596827
theorem B7651205 : Blo 1060614 7651205 := bstep (se 4 (by rfl) ⟨717300, by rfl⟩ : syracuseStep 7651205 = 1434601) B1434601
theorem B3588137 : Blo 1060614 3588137 := bstep (se 2 (by rfl) ⟨1345551, by rfl⟩ : syracuseStep 3588137 = 2691103) B2691103
theorem B14534255 : Blo 1060614 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B4311215 : Blo 1060614 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B1592489 : Blo 1060614 1592489 := bstep (se 2 (by rfl) ⟨597183, by rfl⟩ : syracuseStep 1592489 = 1194367) B1194367
theorem B1592987 : Blo 1060614 1592987 := bstep (se 1 (by rfl) ⟨1194740, by rfl⟩ : syracuseStep 1592987 = 2389481) B2389481
theorem B4542331 : Blo 1060614 4542331 := bstep (se 1 (by rfl) ⟨3406748, by rfl⟩ : syracuseStep 4542331 = 6813497) B6813497
theorem B1789931 : Blo 1060614 1789931 := bstep (se 1 (by rfl) ⟨1342448, by rfl⟩ : syracuseStep 1789931 = 2684897) B2684897
theorem B2020135 : Blo 1060614 2020135 := bstep (se 1 (by rfl) ⟨1515101, by rfl⟩ : syracuseStep 2020135 = 3030203) B3030203
theorem B1594505 : Blo 1060614 1594505 := bstep (se 2 (by rfl) ⟨597939, by rfl⟩ : syracuseStep 1594505 = 1195879) B1195879
theorem B7657577 : Blo 1060614 7657577 := bstep (se 2 (by rfl) ⟨2871591, by rfl⟩ : syracuseStep 7657577 = 5743183) B5743183
theorem B4545065 : Blo 1060614 4545065 := bstep (se 2 (by rfl) ⟨1704399, by rfl⟩ : syracuseStep 4545065 = 3408799) B3408799
theorem B1596359 : Blo 1060614 1596359 := bstep (se 1 (by rfl) ⟨1197269, by rfl⟩ : syracuseStep 1596359 = 2394539) B2394539
theorem B1596383 : Blo 1060614 1596383 := bstep (se 1 (by rfl) ⟨1197287, by rfl⟩ : syracuseStep 1596383 = 2394575) B2394575
theorem B3070973 : Blo 1060614 3070973 := bstep (se 3 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 3070973 = 1151615) B1151615
theorem B53109523 : Blo 1060614 53109523 := bstep (se 1 (by rfl) ⟨39832142, by rfl⟩ : syracuseStep 53109523 = 79664285) B79664285
theorem B1795567 : Blo 1060614 1795567 := bstep (se 1 (by rfl) ⟨1346675, by rfl⟩ : syracuseStep 1795567 = 2693351) B2693351
theorem B6055667 : Blo 1060614 6055667 := bstep (se 1 (by rfl) ⟨4541750, by rfl⟩ : syracuseStep 6055667 = 9083501) B9083501
theorem B147220229 : Blo 1060614 147220229 := bstep (se 4 (by rfl) ⟨13801896, by rfl⟩ : syracuseStep 147220229 = 27603793) B27603793
theorem B40822541 : Blo 1060614 40822541 := bstep (se 3 (by rfl) ⟨7654226, by rfl⟩ : syracuseStep 40822541 = 15308453) B15308453
theorem B16378985 : Blo 1060614 16378985 := bstep (se 2 (by rfl) ⟨6142119, by rfl⟩ : syracuseStep 16378985 = 12284239) B12284239
theorem B58223933 : Blo 1060614 58223933 := bstep (se 3 (by rfl) ⟨10916987, by rfl⟩ : syracuseStep 58223933 = 21833975) B21833975
theorem B2387951 : Blo 1060614 2387951 := bstep (se 1 (by rfl) ⟨1790963, by rfl⟩ : syracuseStep 2387951 = 3581927) B3581927
theorem B2388059 : Blo 1060614 2388059 := bstep (se 1 (by rfl) ⟨1791044, by rfl⟩ : syracuseStep 2388059 = 3582089) B3582089
theorem B2388959 : Blo 1060614 2388959 := bstep (se 1 (by rfl) ⟨1791719, by rfl⟩ : syracuseStep 2388959 = 3583439) B3583439
theorem B2389103 : Blo 1060614 2389103 := bstep (se 1 (by rfl) ⟨1791827, by rfl⟩ : syracuseStep 2389103 = 3583655) B3583655
theorem B2389535 : Blo 1060614 2389535 := bstep (se 1 (by rfl) ⟨1792151, by rfl⟩ : syracuseStep 2389535 = 3584303) B3584303
theorem B2685595 : Blo 1060614 2685595 := bstep (se 1 (by rfl) ⟨2014196, by rfl⟩ : syracuseStep 2685595 = 4028393) B4028393
theorem B68811767 : Blo 1060614 68811767 := bstep (se 1 (by rfl) ⟨51608825, by rfl⟩ : syracuseStep 68811767 = 103217651) B103217651
theorem B8617043 : Blo 1060614 8617043 := bstep (se 1 (by rfl) ⟨6462782, by rfl⟩ : syracuseStep 8617043 = 12925565) B12925565
theorem B5111009 : Blo 1060614 5111009 := bstep (se 2 (by rfl) ⟨1916628, by rfl⟩ : syracuseStep 5111009 = 3833257) B3833257
theorem B1342975 : Blo 1060614 1342975 := bstep (se 1 (by rfl) ⟨1007231, by rfl⟩ : syracuseStep 1342975 = 2014463) B2014463
theorem B2392091 : Blo 1060614 2392091 := bstep (se 1 (by rfl) ⟨1794068, by rfl⟩ : syracuseStep 2392091 = 3588137) B3588137
theorem B4030505 : Blo 1060614 4030505 := bstep (se 2 (by rfl) ⟨1511439, by rfl⟩ : syracuseStep 4030505 = 3022879) B3022879
theorem B6128729 : Blo 1060614 6128729 := bstep (se 2 (by rfl) ⟨2298273, by rfl⟩ : syracuseStep 6128729 = 4596547) B4596547
theorem B3278663 : Blo 1060614 3278663 := bstep (se 1 (by rfl) ⟨2458997, by rfl⟩ : syracuseStep 3278663 = 4917995) B4917995
theorem B2394089 : Blo 1060614 2394089 := bstep (se 2 (by rfl) ⟨897783, by rfl⟩ : syracuseStep 2394089 = 1795567) B1795567
theorem B2493631 : Blo 1060614 2493631 := bstep (se 1 (by rfl) ⟨1870223, by rfl⟩ : syracuseStep 2493631 = 3740447) B3740447
theorem B283250789 : Blo 1060614 283250789 := bstep (se 4 (by rfl) ⟨26554761, by rfl⟩ : syracuseStep 283250789 = 53109523) B53109523
theorem B2692075 : Blo 1060614 2692075 := bstep (se 1 (by rfl) ⟨2019056, by rfl⟩ : syracuseStep 2692075 = 4038113) B4038113
theorem B298588193 : Blo 1060614 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B1841327 : Blo 1060614 1841327 := bstep (se 1 (by rfl) ⟨1380995, by rfl⟩ : syracuseStep 1841327 = 2761991) B2761991
theorem B2693513 : Blo 1060614 2693513 := bstep (se 2 (by rfl) ⟨1010067, by rfl⟩ : syracuseStep 2693513 = 2020135) B2020135
theorem B4037111 : Blo 1060614 4037111 := bstep (se 1 (by rfl) ⟨3027833, by rfl⟩ : syracuseStep 4037111 = 6055667) B6055667
theorem B98146819 : Blo 1060614 98146819 := bstep (se 1 (by rfl) ⟨73610114, by rfl⟩ : syracuseStep 98146819 = 147220229) B147220229
theorem B10919323 : Blo 1060614 10919323 := bstep (se 1 (by rfl) ⟨8189492, by rfl⟩ : syracuseStep 10919323 = 16378985) B16378985
theorem B68821609 : Blo 1060614 68821609 := bstep (se 2 (by rfl) ⟨25808103, by rfl⟩ : syracuseStep 68821609 = 51616207) B51616207
theorem B3580793 : Blo 1060614 3580793 := bstep (se 2 (by rfl) ⟨1342797, by rfl⟩ : syracuseStep 3580793 = 2685595) B2685595
theorem B3024211 : Blo 1060614 3024211 := bstep (se 1 (by rfl) ⟨2268158, by rfl⟩ : syracuseStep 3024211 = 4536317) B4536317
theorem B4302649 : Blo 1060614 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B46540727 : Blo 1060614 46540727 := bstep (se 1 (by rfl) ⟨34905545, by rfl⟩ : syracuseStep 46540727 = 69811091) B69811091
theorem B5744695 : Blo 1060614 5744695 := bstep (se 1 (by rfl) ⟨4308521, by rfl⟩ : syracuseStep 5744695 = 8617043) B8617043
theorem B3582683 : Blo 1060614 3582683 := bstep (se 1 (by rfl) ⟨2687012, by rfl⟩ : syracuseStep 3582683 = 5374025) B5374025
theorem B30651047 : Blo 1060614 30651047 := bstep (se 1 (by rfl) ⟨22988285, by rfl⟩ : syracuseStep 30651047 = 45976571) B45976571
theorem B1061659 : Blo 1060614 1061659 := bstep (se 1 (by rfl) ⟨796244, by rfl⟩ : syracuseStep 1061659 = 1592489) B1592489
theorem B1061991 : Blo 1060614 1061991 := bstep (se 1 (by rfl) ⟨796493, by rfl⟩ : syracuseStep 1061991 = 1592987) B1592987
theorem B1193287 : Blo 1060614 1193287 := bstep (se 1 (by rfl) ⟨894965, by rfl⟩ : syracuseStep 1193287 = 1789931) B1789931
theorem B20690387 : Blo 1060614 20690387 := bstep (se 1 (by rfl) ⟨15517790, by rfl⟩ : syracuseStep 20690387 = 31035581) B31035581
theorem B3585599 : Blo 1060614 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B38778587 : Blo 1060614 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B1063003 : Blo 1060614 1063003 := bstep (se 1 (by rfl) ⟨797252, by rfl⟩ : syracuseStep 1063003 = 1594505) B1594505
theorem B49166513 : Blo 1060614 49166513 := bstep (se 2 (by rfl) ⟨18437442, by rfl⟩ : syracuseStep 49166513 = 36874885) B36874885
theorem B1816795 : Blo 1060614 1816795 := bstep (se 1 (by rfl) ⟨1362596, by rfl⟩ : syracuseStep 1816795 = 2725193) B2725193
theorem B6044321 : Blo 1060614 6044321 := bstep (se 2 (by rfl) ⟨2266620, by rfl⟩ : syracuseStep 6044321 = 4533241) B4533241
theorem B3586841 : Blo 1060614 3586841 := bstep (se 2 (by rfl) ⟨1345065, by rfl⟩ : syracuseStep 3586841 = 2690131) B2690131
theorem B6798275 : Blo 1060614 6798275 := bstep (se 1 (by rfl) ⟨5098706, by rfl⟩ : syracuseStep 6798275 = 10197413) B10197413
theorem B3030043 : Blo 1060614 3030043 := bstep (se 1 (by rfl) ⟨2272532, by rfl⟩ : syracuseStep 3030043 = 4545065) B4545065
theorem B1064239 : Blo 1060614 1064239 := bstep (se 1 (by rfl) ⟨798179, by rfl⟩ : syracuseStep 1064239 = 1596359) B1596359
theorem B1064255 : Blo 1060614 1064255 := bstep (se 1 (by rfl) ⟨798191, by rfl⟩ : syracuseStep 1064255 = 1596383) B1596383
theorem B2047315 : Blo 1060614 2047315 := bstep (se 1 (by rfl) ⟨1535486, by rfl⟩ : syracuseStep 2047315 = 3070973) B3070973
theorem B3588083 : Blo 1060614 3588083 := bstep (se 1 (by rfl) ⟨2691062, by rfl⟩ : syracuseStep 3588083 = 5382125) B5382125
theorem B6045961 : Blo 1060614 6045961 := bstep (se 2 (by rfl) ⟨2267235, by rfl⟩ : syracuseStep 6045961 = 4534471) B4534471
theorem B3589055 : Blo 1060614 3589055 := bstep (se 1 (by rfl) ⟨2691791, by rfl⟩ : syracuseStep 3589055 = 5383583) B5383583
theorem B27215027 : Blo 1060614 27215027 := bstep (se 1 (by rfl) ⟨20411270, by rfl⟩ : syracuseStep 27215027 = 40822541) B40822541
theorem B6997423 : Blo 1060614 6997423 := bstep (se 1 (by rfl) ⟨5248067, by rfl⟩ : syracuseStep 6997423 = 10496135) B10496135
theorem B13617355 : Blo 1060614 13617355 := bstep (se 1 (by rfl) ⟨10213016, by rfl⟩ : syracuseStep 13617355 = 20426033) B20426033
theorem B38815955 : Blo 1060614 38815955 := bstep (se 1 (by rfl) ⟨29111966, by rfl⟩ : syracuseStep 38815955 = 58223933) B58223933
theorem B1591967 : Blo 1060614 1591967 := bstep (se 1 (by rfl) ⟨1193975, by rfl⟩ : syracuseStep 1591967 = 2387951) B2387951
theorem B1592039 : Blo 1060614 1592039 := bstep (se 1 (by rfl) ⟨1194029, by rfl⟩ : syracuseStep 1592039 = 2388059) B2388059
theorem B1592639 : Blo 1060614 1592639 := bstep (se 1 (by rfl) ⟨1194479, by rfl⟩ : syracuseStep 1592639 = 2388959) B2388959
theorem B1592735 : Blo 1060614 1592735 := bstep (se 1 (by rfl) ⟨1194551, by rfl⟩ : syracuseStep 1592735 = 2389103) B2389103
theorem B1593023 : Blo 1060614 1593023 := bstep (se 1 (by rfl) ⟨1194767, by rfl⟩ : syracuseStep 1593023 = 2389535) B2389535
theorem B3592619 : Blo 1060614 3592619 := bstep (se 1 (by rfl) ⟨2694464, by rfl⟩ : syracuseStep 3592619 = 5388929) B5388929
theorem B1790633 : Blo 1060614 1790633 := bstep (se 2 (by rfl) ⟨671487, by rfl⟩ : syracuseStep 1790633 = 1342975) B1342975
theorem B5100803 : Blo 1060614 5100803 := bstep (se 1 (by rfl) ⟨3825602, by rfl⟩ : syracuseStep 5100803 = 7651205) B7651205
theorem B1594751 : Blo 1060614 1594751 := bstep (se 1 (by rfl) ⟨1196063, by rfl⟩ : syracuseStep 1594751 = 2392127) B2392127
theorem B1594859 : Blo 1060614 1594859 := bstep (se 1 (by rfl) ⟨1196144, by rfl⟩ : syracuseStep 1594859 = 2392289) B2392289
theorem B970151417 : Blo 1060614 970151417 := bstep (se 2 (by rfl) ⟨363806781, by rfl⟩ : syracuseStep 970151417 = 727613563) B727613563
theorem B1595087 : Blo 1060614 1595087 := bstep (se 1 (by rfl) ⟨1196315, by rfl⟩ : syracuseStep 1595087 = 2392631) B2392631
theorem B1595291 : Blo 1060614 1595291 := bstep (se 1 (by rfl) ⟨1196468, by rfl⟩ : syracuseStep 1595291 = 2392937) B2392937
theorem B4544723 : Blo 1060614 4544723 := bstep (se 1 (by rfl) ⟨3408542, by rfl⟩ : syracuseStep 4544723 = 6817085) B6817085
theorem B19421471 : Blo 1060614 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B3234433 : Blo 1060614 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B2874143 : Blo 1060614 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B1596287 : Blo 1060614 1596287 := bstep (se 1 (by rfl) ⟨1197215, by rfl⟩ : syracuseStep 1596287 = 2394431) B2394431
theorem B110255555 : Blo 1060614 110255555 := bstep (se 1 (by rfl) ⟨82691666, by rfl⟩ : syracuseStep 110255555 = 165383333) B165383333
theorem B1794919 : Blo 1060614 1794919 := bstep (se 1 (by rfl) ⟨1346189, by rfl⟩ : syracuseStep 1794919 = 2692379) B2692379
theorem B5105051 : Blo 1060614 5105051 := bstep (se 1 (by rfl) ⟨3828788, by rfl⟩ : syracuseStep 5105051 = 7657577) B7657577
theorem B38758013 : Blo 1060614 38758013 := bstep (se 3 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 38758013 = 14534255) B14534255
theorem B1795817 : Blo 1060614 1795817 := bstep (se 2 (by rfl) ⟨673431, by rfl⟩ : syracuseStep 1795817 = 1346863) B1346863
theorem B12937097 : Blo 1060614 12937097 := bstep (se 2 (by rfl) ⟨4851411, by rfl⟩ : syracuseStep 12937097 = 9702823) B9702823
theorem B3827807 : Blo 1060614 3827807 := bstep (se 1 (by rfl) ⟨2870855, by rfl⟩ : syracuseStep 3827807 = 5741711) B5741711
theorem B1075367 : Blo 1060614 1075367 := bstep (se 1 (by rfl) ⟨806525, by rfl⟩ : syracuseStep 1075367 = 1613051) B1613051
theorem B1796303 : Blo 1060614 1796303 := bstep (se 1 (by rfl) ⟨1347227, by rfl⟩ : syracuseStep 1796303 = 2694455) B2694455
theorem B6056441 : Blo 1060614 6056441 := bstep (se 2 (by rfl) ⟨2271165, by rfl⟩ : syracuseStep 6056441 = 4542331) B4542331
theorem B1534699 : Blo 1060614 1534699 := bstep (se 1 (by rfl) ⟨1151024, by rfl⟩ : syracuseStep 1534699 = 2302049) B2302049
theorem B2387051 : Blo 1060614 2387051 := bstep (se 1 (by rfl) ⟨1790288, by rfl⟩ : syracuseStep 2387051 = 3580577) B3580577
theorem B10909151 : Blo 1060614 10909151 := bstep (se 1 (by rfl) ⟨8181863, by rfl⟩ : syracuseStep 10909151 = 16363727) B16363727
theorem B6060359 : Blo 1060614 6060359 := bstep (se 1 (by rfl) ⟨4545269, by rfl⟩ : syracuseStep 6060359 = 9090539) B9090539
theorem B9075503 : Blo 1060614 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B1342747 : Blo 1060614 1342747 := bstep (se 1 (by rfl) ⟨1007060, by rfl⟩ : syracuseStep 1342747 = 2014121) B2014121
theorem B45874511 : Blo 1060614 45874511 := bstep (se 1 (by rfl) ⟨34405883, by rfl⟩ : syracuseStep 45874511 = 68811767) B68811767
theorem B3407339 : Blo 1060614 3407339 := bstep (se 1 (by rfl) ⟨2555504, by rfl⟩ : syracuseStep 3407339 = 5111009) B5111009
theorem B2687003 : Blo 1060614 2687003 := bstep (se 1 (by rfl) ⟨2015252, by rfl⟩ : syracuseStep 2687003 = 4030505) B4030505
theorem B8061281 : Blo 1060614 8061281 := bstep (se 2 (by rfl) ⟨3022980, by rfl⟩ : syracuseStep 8061281 = 6045961) B6045961
theorem B2392703 : Blo 1060614 2392703 := bstep (se 1 (by rfl) ⟨1794527, by rfl⟩ : syracuseStep 2392703 = 3589055) B3589055
theorem B2393225 : Blo 1060614 2393225 := bstep (se 2 (by rfl) ⟨897459, by rfl⟩ : syracuseStep 2393225 = 1794919) B1794919
theorem B4032281 : Blo 1060614 4032281 := bstep (se 2 (by rfl) ⟨1512105, by rfl⟩ : syracuseStep 4032281 = 3024211) B3024211
theorem B18156473 : Blo 1060614 18156473 := bstep (se 2 (by rfl) ⟨6808677, by rfl⟩ : syracuseStep 18156473 = 13617355) B13617355
theorem B2395079 : Blo 1060614 2395079 := bstep (se 1 (by rfl) ⟨1796309, by rfl⟩ : syracuseStep 2395079 = 3592619) B3592619
theorem B2691407 : Blo 1060614 2691407 := bstep (se 1 (by rfl) ⟨2018555, by rfl⟩ : syracuseStep 2691407 = 4037111) B4037111
theorem B73503703 : Blo 1060614 73503703 := bstep (se 1 (by rfl) ⟨55127777, by rfl⟩ : syracuseStep 73503703 = 110255555) B110255555
theorem B8624731 : Blo 1060614 8624731 := bstep (se 1 (by rfl) ⟨6468548, by rfl⟩ : syracuseStep 8624731 = 12937097) B12937097
theorem B4037627 : Blo 1060614 4037627 := bstep (se 1 (by rfl) ⟨3028220, by rfl⟩ : syracuseStep 4037627 = 6056441) B6056441
theorem B4040057 : Blo 1060614 4040057 := bstep (se 2 (by rfl) ⟨1515021, by rfl⟩ : syracuseStep 4040057 = 3030043) B3030043
theorem B32777675 : Blo 1060614 32777675 := bstep (se 1 (by rfl) ⟨24583256, by rfl⟩ : syracuseStep 32777675 = 49166513) B49166513
theorem B4040239 : Blo 1060614 4040239 := bstep (se 1 (by rfl) ⟨3030179, by rfl⟩ : syracuseStep 4040239 = 6060359) B6060359
theorem B22947461 : Blo 1060614 22947461 := bstep (se 4 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 22947461 = 4302649) B4302649
theorem B2729753 : Blo 1060614 2729753 := bstep (se 2 (by rfl) ⟨1023657, by rfl⟩ : syracuseStep 2729753 = 2047315) B2047315
theorem B14559097 : Blo 1060614 14559097 := bstep (se 2 (by rfl) ⟨5459661, by rfl⟩ : syracuseStep 14559097 = 10919323) B10919323
theorem B4532183 : Blo 1060614 4532183 := bstep (se 1 (by rfl) ⟨3399137, by rfl⟩ : syracuseStep 4532183 = 6798275) B6798275
theorem B30583007 : Blo 1060614 30583007 := bstep (se 1 (by rfl) ⟨22937255, by rfl⟩ : syracuseStep 30583007 = 45874511) B45874511
theorem B2271559 : Blo 1060614 2271559 := bstep (se 1 (by rfl) ⟨1703669, by rfl⟩ : syracuseStep 2271559 = 3407339) B3407339
theorem B91762145 : Blo 1060614 91762145 := bstep (se 2 (by rfl) ⟨34410804, by rfl⟩ : syracuseStep 91762145 = 68821609) B68821609
theorem B1061311 : Blo 1060614 1061311 := bstep (se 1 (by rfl) ⟨795983, by rfl⟩ : syracuseStep 1061311 = 1591967) B1591967
theorem B1061359 : Blo 1060614 1061359 := bstep (se 1 (by rfl) ⟨796019, by rfl⟩ : syracuseStep 1061359 = 1592039) B1592039
theorem B1061759 : Blo 1060614 1061759 := bstep (se 1 (by rfl) ⟨796319, by rfl⟩ : syracuseStep 1061759 = 1592639) B1592639
theorem B1061823 : Blo 1060614 1061823 := bstep (se 1 (by rfl) ⟨796367, by rfl⟩ : syracuseStep 1061823 = 1592735) B1592735
theorem B1062015 : Blo 1060614 1062015 := bstep (se 1 (by rfl) ⟨796511, by rfl⟩ : syracuseStep 1062015 = 1593023) B1593023
theorem B1193755 : Blo 1060614 1193755 := bstep (se 1 (by rfl) ⟨895316, by rfl⟩ : syracuseStep 1193755 = 1790633) B1790633
theorem B1063167 : Blo 1060614 1063167 := bstep (se 1 (by rfl) ⟨797375, by rfl⟩ : syracuseStep 1063167 = 1594751) B1594751
theorem B2046265 : Blo 1060614 2046265 := bstep (se 2 (by rfl) ⟨767349, by rfl⟩ : syracuseStep 2046265 = 1534699) B1534699
theorem B1063239 : Blo 1060614 1063239 := bstep (se 1 (by rfl) ⟨797429, by rfl⟩ : syracuseStep 1063239 = 1594859) B1594859
theorem B1063391 : Blo 1060614 1063391 := bstep (se 1 (by rfl) ⟨797543, by rfl⟩ : syracuseStep 1063391 = 1595087) B1595087
theorem B1063527 : Blo 1060614 1063527 := bstep (se 1 (by rfl) ⟨797645, by rfl⟩ : syracuseStep 1063527 = 1595291) B1595291
theorem B1227551 : Blo 1060614 1227551 := bstep (se 1 (by rfl) ⟨920663, by rfl⟩ : syracuseStep 1227551 = 1841327) B1841327
theorem B3029815 : Blo 1060614 3029815 := bstep (se 1 (by rfl) ⟨2272361, by rfl⟩ : syracuseStep 3029815 = 4544723) B4544723
theorem B1916095 : Blo 1060614 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B1064191 : Blo 1060614 1064191 := bstep (se 1 (by rfl) ⟨798143, by rfl⟩ : syracuseStep 1064191 = 1596287) B1596287
theorem B2867645 : Blo 1060614 2867645 := bstep (se 3 (by rfl) ⟨537683, by rfl⟩ : syracuseStep 2867645 = 1075367) B1075367
theorem B51790589 : Blo 1060614 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B25838675 : Blo 1060614 25838675 := bstep (se 1 (by rfl) ⟨19379006, by rfl⟩ : syracuseStep 25838675 = 38758013) B38758013
theorem B1197211 : Blo 1060614 1197211 := bstep (se 1 (by rfl) ⟨897908, by rfl⟩ : syracuseStep 1197211 = 1795817) B1795817
theorem B3589433 : Blo 1060614 3589433 := bstep (se 2 (by rfl) ⟨1346037, by rfl⟩ : syracuseStep 3589433 = 2692075) B2692075
theorem B1197535 : Blo 1060614 1197535 := bstep (se 1 (by rfl) ⟨898151, by rfl⟩ : syracuseStep 1197535 = 1796303) B1796303
theorem B1591049 : Blo 1060614 1591049 := bstep (se 2 (by rfl) ⟨596643, by rfl⟩ : syracuseStep 1591049 = 1193287) B1193287
theorem B1591367 : Blo 1060614 1591367 := bstep (se 1 (by rfl) ⟨1193525, by rfl⟩ : syracuseStep 1591367 = 2387051) B2387051
theorem B20434031 : Blo 1060614 20434031 := bstep (se 1 (by rfl) ⟨15325523, by rfl⟩ : syracuseStep 20434031 = 30651047) B30651047
theorem B130862425 : Blo 1060614 130862425 := bstep (se 2 (by rfl) ⟨49073409, by rfl⟩ : syracuseStep 130862425 = 98146819) B98146819
theorem B4312577 : Blo 1060614 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B1790329 : Blo 1060614 1790329 := bstep (se 2 (by rfl) ⟨671373, by rfl⟩ : syracuseStep 1790329 = 1342747) B1342747
theorem B6050335 : Blo 1060614 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B1594727 : Blo 1060614 1594727 := bstep (se 1 (by rfl) ⟨1196045, by rfl⟩ : syracuseStep 1594727 = 2392091) B2392091
theorem B4085819 : Blo 1060614 4085819 := bstep (se 1 (by rfl) ⟨3064364, by rfl⟩ : syracuseStep 4085819 = 6128729) B6128729
theorem B18143351 : Blo 1060614 18143351 := bstep (se 1 (by rfl) ⟨13607513, by rfl⟩ : syracuseStep 18143351 = 27215027) B27215027
theorem B2185775 : Blo 1060614 2185775 := bstep (se 1 (by rfl) ⟨1639331, by rfl⟩ : syracuseStep 2185775 = 3278663) B3278663
theorem B1596059 : Blo 1060614 1596059 := bstep (se 1 (by rfl) ⟨1197044, by rfl⟩ : syracuseStep 1596059 = 2394089) B2394089
theorem B25877303 : Blo 1060614 25877303 := bstep (se 1 (by rfl) ⟨19407977, by rfl⟩ : syracuseStep 25877303 = 38815955) B38815955
theorem B9329897 : Blo 1060614 9329897 := bstep (se 2 (by rfl) ⟨3498711, by rfl⟩ : syracuseStep 9329897 = 6997423) B6997423
theorem B188833859 : Blo 1060614 188833859 := bstep (se 1 (by rfl) ⟨141625394, by rfl⟩ : syracuseStep 188833859 = 283250789) B283250789
theorem B7659593 : Blo 1060614 7659593 := bstep (se 2 (by rfl) ⟨2872347, by rfl⟩ : syracuseStep 7659593 = 5744695) B5744695
theorem B3400535 : Blo 1060614 3400535 := bstep (se 1 (by rfl) ⟨2550401, by rfl⟩ : syracuseStep 3400535 = 5100803) B5100803
theorem B646767611 : Blo 1060614 646767611 := bstep (se 1 (by rfl) ⟨485075708, by rfl⟩ : syracuseStep 646767611 = 970151417) B970151417
theorem B199058795 : Blo 1060614 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B1795675 : Blo 1060614 1795675 := bstep (se 1 (by rfl) ⟨1346756, by rfl⟩ : syracuseStep 1795675 = 2693513) B2693513
theorem B2387195 : Blo 1060614 2387195 := bstep (se 1 (by rfl) ⟨1790396, by rfl⟩ : syracuseStep 2387195 = 3580793) B3580793
theorem B3403367 : Blo 1060614 3403367 := bstep (se 1 (by rfl) ⟨2552525, by rfl⟩ : syracuseStep 3403367 = 5105051) B5105051
theorem B13299365 : Blo 1060614 13299365 := bstep (se 4 (by rfl) ⟨1246815, by rfl⟩ : syracuseStep 13299365 = 2493631) B2493631
theorem B31027151 : Blo 1060614 31027151 := bstep (se 1 (by rfl) ⟨23270363, by rfl⟩ : syracuseStep 31027151 = 46540727) B46540727
theorem B2551871 : Blo 1060614 2551871 := bstep (se 1 (by rfl) ⟨1913903, by rfl⟩ : syracuseStep 2551871 = 3827807) B3827807
theorem B2388455 : Blo 1060614 2388455 := bstep (se 1 (by rfl) ⟨1791341, by rfl⟩ : syracuseStep 2388455 = 3582683) B3582683
theorem B2422393 : Blo 1060614 2422393 := bstep (se 2 (by rfl) ⟨908397, by rfl⟩ : syracuseStep 2422393 = 1816795) B1816795
theorem B13793591 : Blo 1060614 13793591 := bstep (se 1 (by rfl) ⟨10345193, by rfl⟩ : syracuseStep 13793591 = 20690387) B20690387
theorem B7272767 : Blo 1060614 7272767 := bstep (se 1 (by rfl) ⟨5454575, by rfl⟩ : syracuseStep 7272767 = 10909151) B10909151
theorem B2390399 : Blo 1060614 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B25852391 : Blo 1060614 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B4029547 : Blo 1060614 4029547 := bstep (se 1 (by rfl) ⟨3022160, by rfl⟩ : syracuseStep 4029547 = 6044321) B6044321
theorem B2391227 : Blo 1060614 2391227 := bstep (se 1 (by rfl) ⟨1793420, by rfl⟩ : syracuseStep 2391227 = 3586841) B3586841
theorem B2392055 : Blo 1060614 2392055 := bstep (se 1 (by rfl) ⟨1794041, by rfl⟩ : syracuseStep 2392055 = 3588083) B3588083
theorem B5374187 : Blo 1060614 5374187 := bstep (se 1 (by rfl) ⟨4030640, by rfl⟩ : syracuseStep 5374187 = 8061281) B8061281
theorem B2392955 : Blo 1060614 2392955 := bstep (se 1 (by rfl) ⟨1794716, by rfl⟩ : syracuseStep 2392955 = 3589433) B3589433
theorem B2688187 : Blo 1060614 2688187 := bstep (se 1 (by rfl) ⟨2016140, by rfl⟩ : syracuseStep 2688187 = 4032281) B4032281
theorem B10913413 : Blo 1060614 10913413 := bstep (se 4 (by rfl) ⟨1023132, by rfl⟩ : syracuseStep 10913413 = 2046265) B2046265
theorem B2394233 : Blo 1060614 2394233 := bstep (se 2 (by rfl) ⟨897837, by rfl⟩ : syracuseStep 2394233 = 1795675) B1795675
theorem B2723879 : Blo 1060614 2723879 := bstep (se 1 (by rfl) ⟨2042909, by rfl⟩ : syracuseStep 2723879 = 4085819) B4085819
theorem B12095567 : Blo 1060614 12095567 := bstep (se 1 (by rfl) ⟨9071675, by rfl⟩ : syracuseStep 12095567 = 18143351) B18143351
theorem B2691751 : Blo 1060614 2691751 := bstep (se 1 (by rfl) ⟨2018813, by rfl⟩ : syracuseStep 2691751 = 4037627) B4037627
theorem B2267023 : Blo 1060614 2267023 := bstep (se 1 (by rfl) ⟨1700267, by rfl⟩ : syracuseStep 2267023 = 3400535) B3400535
theorem B8067113 : Blo 1060614 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B2693371 : Blo 1060614 2693371 := bstep (se 1 (by rfl) ⟨2020028, by rfl⟩ : syracuseStep 2693371 = 4040057) B4040057
theorem B3021455 : Blo 1060614 3021455 := bstep (se 1 (by rfl) ⟨2266091, by rfl⟩ : syracuseStep 3021455 = 4532183) B4532183
theorem B20388671 : Blo 1060614 20388671 := bstep (se 1 (by rfl) ⟨15291503, by rfl⟩ : syracuseStep 20388671 = 30583007) B30583007
theorem B2268911 : Blo 1060614 2268911 := bstep (se 1 (by rfl) ⟨1701683, by rfl⟩ : syracuseStep 2268911 = 3403367) B3403367
theorem B20684767 : Blo 1060614 20684767 := bstep (se 1 (by rfl) ⟨15513575, by rfl⟩ : syracuseStep 20684767 = 31027151) B31027151
theorem B12919429 : Blo 1060614 12919429 := bstep (se 4 (by rfl) ⟨1211196, by rfl⟩ : syracuseStep 12919429 = 2422393) B2422393
theorem B4039753 : Blo 1060614 4039753 := bstep (se 2 (by rfl) ⟨1514907, by rfl⟩ : syracuseStep 4039753 = 3029815) B3029815
theorem B35464973 : Blo 1060614 35464973 := bstep (se 3 (by rfl) ⟨6649682, by rfl⟩ : syracuseStep 35464973 = 13299365) B13299365
theorem B1911763 : Blo 1060614 1911763 := bstep (se 1 (by rfl) ⟨1433822, by rfl⟩ : syracuseStep 1911763 = 2867645) B2867645
theorem B1060699 : Blo 1060614 1060699 := bstep (se 1 (by rfl) ⟨795524, by rfl⟩ : syracuseStep 1060699 = 1591049) B1591049
theorem B1060911 : Blo 1060614 1060911 := bstep (se 1 (by rfl) ⟨795683, by rfl⟩ : syracuseStep 1060911 = 1591367) B1591367
theorem B12104315 : Blo 1060614 12104315 := bstep (se 1 (by rfl) ⟨9078236, by rfl⟩ : syracuseStep 12104315 = 18156473) B18156473
theorem B5386985 : Blo 1060614 5386985 := bstep (se 2 (by rfl) ⟨2020119, by rfl⟩ : syracuseStep 5386985 = 4040239) B4040239
theorem B19412129 : Blo 1060614 19412129 := bstep (se 2 (by rfl) ⟨7279548, by rfl⟩ : syracuseStep 19412129 = 14559097) B14559097
theorem B3028745 : Blo 1060614 3028745 := bstep (se 2 (by rfl) ⟨1135779, by rfl⟩ : syracuseStep 3028745 = 2271559) B2271559
theorem B1063151 : Blo 1060614 1063151 := bstep (se 1 (by rfl) ⟨797363, by rfl⟩ : syracuseStep 1063151 = 1594727) B1594727
theorem B1457183 : Blo 1060614 1457183 := bstep (se 1 (by rfl) ⟨1092887, by rfl⟩ : syracuseStep 1457183 = 2185775) B2185775
theorem B1064039 : Blo 1060614 1064039 := bstep (se 1 (by rfl) ⟨798029, by rfl⟩ : syracuseStep 1064039 = 1596059) B1596059
theorem B17251535 : Blo 1060614 17251535 := bstep (se 1 (by rfl) ⟨12938651, by rfl⟩ : syracuseStep 17251535 = 25877303) B25877303
theorem B392019749 : Blo 1060614 392019749 := bstep (se 4 (by rfl) ⟨36751851, by rfl⟩ : syracuseStep 392019749 = 73503703) B73503703
theorem B431178407 : Blo 1060614 431178407 := bstep (se 1 (by rfl) ⟨323383805, by rfl⟩ : syracuseStep 431178407 = 646767611) B646767611
theorem B1819835 : Blo 1060614 1819835 := bstep (se 1 (by rfl) ⟨1364876, by rfl⟩ : syracuseStep 1819835 = 2729753) B2729753
theorem B1591463 : Blo 1060614 1591463 := bstep (se 1 (by rfl) ⟨1193597, by rfl⟩ : syracuseStep 1591463 = 2387195) B2387195
theorem B1591673 : Blo 1060614 1591673 := bstep (se 2 (by rfl) ⟨596877, by rfl⟩ : syracuseStep 1591673 = 1193755) B1193755
theorem B1592303 : Blo 1060614 1592303 := bstep (se 1 (by rfl) ⟨1194227, by rfl⟩ : syracuseStep 1592303 = 2388455) B2388455
theorem B13093877 : Blo 1060614 13093877 := bstep (se 5 (by rfl) ⟨613775, by rfl⟩ : syracuseStep 13093877 = 1227551) B1227551
theorem B9195727 : Blo 1060614 9195727 := bstep (se 1 (by rfl) ⟨6896795, by rfl⟩ : syracuseStep 9195727 = 13793591) B13793591
theorem B1593599 : Blo 1060614 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B1594151 : Blo 1060614 1594151 := bstep (se 1 (by rfl) ⟨1195613, by rfl⟩ : syracuseStep 1594151 = 2391227) B2391227
theorem B1594703 : Blo 1060614 1594703 := bstep (se 1 (by rfl) ⟨1196027, by rfl⟩ : syracuseStep 1594703 = 2392055) B2392055
theorem B1791335 : Blo 1060614 1791335 := bstep (se 1 (by rfl) ⟨1343501, by rfl⟩ : syracuseStep 1791335 = 2687003) B2687003
theorem B1595135 : Blo 1060614 1595135 := bstep (se 1 (by rfl) ⟨1196351, by rfl⟩ : syracuseStep 1595135 = 2392703) B2392703
theorem B34527059 : Blo 1060614 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B17225783 : Blo 1060614 17225783 := bstep (se 1 (by rfl) ⟨12919337, by rfl⟩ : syracuseStep 17225783 = 25838675) B25838675
theorem B1595483 : Blo 1060614 1595483 := bstep (se 1 (by rfl) ⟨1196612, by rfl⟩ : syracuseStep 1595483 = 2393225) B2393225
theorem B1596281 : Blo 1060614 1596281 := bstep (se 2 (by rfl) ⟨598605, by rfl⟩ : syracuseStep 1596281 = 1197211) B1197211
theorem B1596713 : Blo 1060614 1596713 := bstep (se 2 (by rfl) ⟨598767, by rfl⟩ : syracuseStep 1596713 = 1197535) B1197535
theorem B1596719 : Blo 1060614 1596719 := bstep (se 1 (by rfl) ⟨1197539, by rfl⟩ : syracuseStep 1596719 = 2395079) B2395079
theorem B13622687 : Blo 1060614 13622687 := bstep (se 1 (by rfl) ⟨10217015, by rfl⟩ : syracuseStep 13622687 = 20434031) B20434031
theorem B2875051 : Blo 1060614 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B1794271 : Blo 1060614 1794271 := bstep (se 1 (by rfl) ⟨1345703, by rfl⟩ : syracuseStep 1794271 = 2691407) B2691407
theorem B174483233 : Blo 1060614 174483233 := bstep (se 2 (by rfl) ⟨65431212, by rfl⟩ : syracuseStep 174483233 = 130862425) B130862425
theorem B6219931 : Blo 1060614 6219931 := bstep (se 1 (by rfl) ⟨4664948, by rfl⟩ : syracuseStep 6219931 = 9329897) B9329897
theorem B125889239 : Blo 1060614 125889239 := bstep (se 1 (by rfl) ⟨94416929, by rfl⟩ : syracuseStep 125889239 = 188833859) B188833859
theorem B5106395 : Blo 1060614 5106395 := bstep (se 1 (by rfl) ⟨3829796, by rfl⟩ : syracuseStep 5106395 = 7659593) B7659593
theorem B2387105 : Blo 1060614 2387105 := bstep (se 2 (by rfl) ⟨895164, by rfl⟩ : syracuseStep 2387105 = 1790329) B1790329
theorem B132705863 : Blo 1060614 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B21851783 : Blo 1060614 21851783 := bstep (se 1 (by rfl) ⟨16388837, by rfl⟩ : syracuseStep 21851783 = 32777675) B32777675
theorem B15298307 : Blo 1060614 15298307 := bstep (se 1 (by rfl) ⟨11473730, by rfl⟩ : syracuseStep 15298307 = 22947461) B22947461
theorem B61174763 : Blo 1060614 61174763 := bstep (se 1 (by rfl) ⟨45881072, by rfl⟩ : syracuseStep 61174763 = 91762145) B91762145
theorem B1701247 : Blo 1060614 1701247 := bstep (se 1 (by rfl) ⟨1275935, by rfl⟩ : syracuseStep 1701247 = 2551871) B2551871
theorem B11499641 : Blo 1060614 11499641 := bstep (se 2 (by rfl) ⟨4312365, by rfl⟩ : syracuseStep 11499641 = 8624731) B8624731
theorem B5372729 : Blo 1060614 5372729 := bstep (se 2 (by rfl) ⟨2014773, by rfl⟩ : syracuseStep 5372729 = 4029547) B4029547
theorem B4848511 : Blo 1060614 4848511 := bstep (se 1 (by rfl) ⟨3636383, by rfl⟩ : syracuseStep 4848511 = 7272767) B7272767
theorem B2554793 : Blo 1060614 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B17234927 : Blo 1060614 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B2392361 : Blo 1060614 2392361 := bstep (se 2 (by rfl) ⟨897135, by rfl⟩ : syracuseStep 2392361 = 1794271) B1794271
theorem B1213223 : Blo 1060614 1213223 := bstep (se 1 (by rfl) ⟨909917, by rfl⟩ : syracuseStep 1213223 = 1819835) B1819835
theorem B14551217 : Blo 1060614 14551217 := bstep (se 2 (by rfl) ⟨5456706, by rfl⟩ : syracuseStep 14551217 = 10913413) B10913413
theorem B8063711 : Blo 1060614 8063711 := bstep (se 1 (by rfl) ⟨6047783, by rfl⟩ : syracuseStep 8063711 = 12095567) B12095567
theorem B8293241 : Blo 1060614 8293241 := bstep (se 2 (by rfl) ⟨3109965, by rfl⟩ : syracuseStep 8293241 = 6219931) B6219931
theorem B5378075 : Blo 1060614 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B94573261 : Blo 1060614 94573261 := bstep (se 3 (by rfl) ⟨17732486, by rfl⟩ : syracuseStep 94573261 = 35464973) B35464973
theorem B9081791 : Blo 1060614 9081791 := bstep (se 1 (by rfl) ⟨6811343, by rfl⟩ : syracuseStep 9081791 = 13622687) B13622687
theorem B1512607 : Blo 1060614 1512607 := bstep (se 1 (by rfl) ⟨1134455, by rfl⟩ : syracuseStep 1512607 = 2268911) B2268911
theorem B12260969 : Blo 1060614 12260969 := bstep (se 2 (by rfl) ⟨4597863, by rfl⟩ : syracuseStep 12260969 = 9195727) B9195727
theorem B2268329 : Blo 1060614 2268329 := bstep (se 2 (by rfl) ⟨850623, by rfl⟩ : syracuseStep 2268329 = 1701247) B1701247
theorem B10198871 : Blo 1060614 10198871 := bstep (se 1 (by rfl) ⟨7649153, by rfl⟩ : syracuseStep 10198871 = 15298307) B15298307
theorem B3022697 : Blo 1060614 3022697 := bstep (se 2 (by rfl) ⟨1133511, by rfl⟩ : syracuseStep 3022697 = 2267023) B2267023
theorem B8069543 : Blo 1060614 8069543 := bstep (se 1 (by rfl) ⟨6052157, by rfl⟩ : syracuseStep 8069543 = 12104315) B12104315
theorem B6464681 : Blo 1060614 6464681 := bstep (se 2 (by rfl) ⟨2424255, by rfl⟩ : syracuseStep 6464681 = 4848511) B4848511
theorem B3581819 : Blo 1060614 3581819 := bstep (se 1 (by rfl) ⟨2686364, by rfl⟩ : syracuseStep 3581819 = 5372729) B5372729
theorem B3582791 : Blo 1060614 3582791 := bstep (se 1 (by rfl) ⟨2687093, by rfl⟩ : syracuseStep 3582791 = 5374187) B5374187
theorem B287452271 : Blo 1060614 287452271 := bstep (se 1 (by rfl) ⟨215589203, by rfl⟩ : syracuseStep 287452271 = 431178407) B431178407
theorem B5386337 : Blo 1060614 5386337 := bstep (se 2 (by rfl) ⟨2019876, by rfl⟩ : syracuseStep 5386337 = 4039753) B4039753
theorem B1060975 : Blo 1060614 1060975 := bstep (se 1 (by rfl) ⟨795731, by rfl⟩ : syracuseStep 1060975 = 1591463) B1591463
theorem B3584249 : Blo 1060614 3584249 := bstep (se 2 (by rfl) ⟨1344093, by rfl⟩ : syracuseStep 3584249 = 2688187) B2688187
theorem B1061115 : Blo 1060614 1061115 := bstep (se 1 (by rfl) ⟨795836, by rfl⟩ : syracuseStep 1061115 = 1591673) B1591673
theorem B1061535 : Blo 1060614 1061535 := bstep (se 1 (by rfl) ⟨796151, by rfl⟩ : syracuseStep 1061535 = 1592303) B1592303
theorem B8729251 : Blo 1060614 8729251 := bstep (se 1 (by rfl) ⟨6546938, by rfl⟩ : syracuseStep 8729251 = 13093877) B13093877
theorem B1062399 : Blo 1060614 1062399 := bstep (se 1 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 1062399 = 1593599) B1593599
theorem B1062767 : Blo 1060614 1062767 := bstep (se 1 (by rfl) ⟨797075, by rfl⟩ : syracuseStep 1062767 = 1594151) B1594151
theorem B1063135 : Blo 1060614 1063135 := bstep (se 1 (by rfl) ⟨797351, by rfl⟩ : syracuseStep 1063135 = 1594703) B1594703
theorem B1194223 : Blo 1060614 1194223 := bstep (se 1 (by rfl) ⟨895667, by rfl⟩ : syracuseStep 1194223 = 1791335) B1791335
theorem B1063423 : Blo 1060614 1063423 := bstep (se 1 (by rfl) ⟨797567, by rfl⟩ : syracuseStep 1063423 = 1595135) B1595135
theorem B23018039 : Blo 1060614 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B11483855 : Blo 1060614 11483855 := bstep (se 1 (by rfl) ⟨8612891, by rfl⟩ : syracuseStep 11483855 = 17225783) B17225783
theorem B1063655 : Blo 1060614 1063655 := bstep (se 1 (by rfl) ⟨797741, by rfl⟩ : syracuseStep 1063655 = 1595483) B1595483
theorem B2014303 : Blo 1060614 2014303 := bstep (se 1 (by rfl) ⟨1510727, by rfl⟩ : syracuseStep 2014303 = 3021455) B3021455
theorem B1064187 : Blo 1060614 1064187 := bstep (se 1 (by rfl) ⟨798140, by rfl⟩ : syracuseStep 1064187 = 1596281) B1596281
theorem B1064475 : Blo 1060614 1064475 := bstep (se 1 (by rfl) ⟨798356, by rfl⟩ : syracuseStep 1064475 = 1596713) B1596713
theorem B1064479 : Blo 1060614 1064479 := bstep (se 1 (by rfl) ⟨798359, by rfl⟩ : syracuseStep 1064479 = 1596719) B1596719
theorem B3589001 : Blo 1060614 3589001 := bstep (se 2 (by rfl) ⟨1345875, by rfl⟩ : syracuseStep 3589001 = 2691751) B2691751
theorem B1591403 : Blo 1060614 1591403 := bstep (se 1 (by rfl) ⟨1193552, by rfl⟩ : syracuseStep 1591403 = 2387105) B2387105
theorem B14567855 : Blo 1060614 14567855 := bstep (se 1 (by rfl) ⟨10925891, by rfl⟩ : syracuseStep 14567855 = 21851783) B21851783
theorem B3885821 : Blo 1060614 3885821 := bstep (se 3 (by rfl) ⟨728591, by rfl⟩ : syracuseStep 3885821 = 1457183) B1457183
theorem B3591161 : Blo 1060614 3591161 := bstep (se 2 (by rfl) ⟨1346685, by rfl⟩ : syracuseStep 3591161 = 2693371) B2693371
theorem B3591323 : Blo 1060614 3591323 := bstep (se 1 (by rfl) ⟨2693492, by rfl⟩ : syracuseStep 3591323 = 5386985) B5386985
theorem B40783175 : Blo 1060614 40783175 := bstep (se 1 (by rfl) ⟨30587381, by rfl⟩ : syracuseStep 40783175 = 61174763) B61174763
theorem B2019163 : Blo 1060614 2019163 := bstep (se 1 (by rfl) ⟨1514372, by rfl⟩ : syracuseStep 2019163 = 3028745) B3028745
theorem B11489951 : Blo 1060614 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B261346499 : Blo 1060614 261346499 := bstep (se 1 (by rfl) ⟨196009874, by rfl⟩ : syracuseStep 261346499 = 392019749) B392019749
theorem B27579689 : Blo 1060614 27579689 := bstep (se 2 (by rfl) ⟨10342383, by rfl⟩ : syracuseStep 27579689 = 20684767) B20684767
theorem B7263677 : Blo 1060614 7263677 := bstep (se 3 (by rfl) ⟨1361939, by rfl⟩ : syracuseStep 7263677 = 2723879) B2723879
theorem B1595303 : Blo 1060614 1595303 := bstep (se 1 (by rfl) ⟨1196477, by rfl⟩ : syracuseStep 1595303 = 2392955) B2392955
theorem B1596155 : Blo 1060614 1596155 := bstep (se 1 (by rfl) ⟨1197116, by rfl⟩ : syracuseStep 1596155 = 2394233) B2394233
theorem B68903621 : Blo 1060614 68903621 := bstep (se 4 (by rfl) ⟨6459714, by rfl⟩ : syracuseStep 68903621 = 12919429) B12919429
theorem B2549017 : Blo 1060614 2549017 := bstep (se 2 (by rfl) ⟨955881, by rfl⟩ : syracuseStep 2549017 = 1911763) B1911763
theorem B13592447 : Blo 1060614 13592447 := bstep (se 1 (by rfl) ⟨10194335, by rfl⟩ : syracuseStep 13592447 = 20388671) B20388671
theorem B116322155 : Blo 1060614 116322155 := bstep (se 1 (by rfl) ⟨87241616, by rfl⟩ : syracuseStep 116322155 = 174483233) B174483233
theorem B3404263 : Blo 1060614 3404263 := bstep (se 1 (by rfl) ⟨2553197, by rfl⟩ : syracuseStep 3404263 = 5106395) B5106395
theorem B335704637 : Blo 1060614 335704637 := bstep (se 3 (by rfl) ⟨62944619, by rfl⟩ : syracuseStep 335704637 = 125889239) B125889239
theorem B88470575 : Blo 1060614 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B12941419 : Blo 1060614 12941419 := bstep (se 1 (by rfl) ⟨9706064, by rfl⟩ : syracuseStep 12941419 = 19412129) B19412129
theorem B7666427 : Blo 1060614 7666427 := bstep (se 1 (by rfl) ⟨5749820, by rfl⟩ : syracuseStep 7666427 = 11499641) B11499641
theorem B1703195 : Blo 1060614 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B11501023 : Blo 1060614 11501023 := bstep (se 1 (by rfl) ⟨8625767, by rfl⟩ : syracuseStep 11501023 = 17251535) B17251535
theorem B3833401 : Blo 1060614 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B2392667 : Blo 1060614 2392667 := bstep (se 1 (by rfl) ⟨1794500, by rfl⟩ : syracuseStep 2392667 = 3589001) B3589001
theorem B9700811 : Blo 1060614 9700811 := bstep (se 1 (by rfl) ⟨7275608, by rfl⟩ : syracuseStep 9700811 = 14551217) B14551217
theorem B30639869 : Blo 1060614 30639869 := bstep (se 3 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 30639869 = 11489951) B11489951
theorem B5375807 : Blo 1060614 5375807 := bstep (se 1 (by rfl) ⟨4031855, by rfl⟩ : syracuseStep 5375807 = 8063711) B8063711
theorem B2590547 : Blo 1060614 2590547 := bstep (se 1 (by rfl) ⟨1942910, by rfl⟩ : syracuseStep 2590547 = 3885821) B3885821
theorem B2394107 : Blo 1060614 2394107 := bstep (se 1 (by rfl) ⟨1795580, by rfl⟩ : syracuseStep 2394107 = 3591161) B3591161
theorem B2394215 : Blo 1060614 2394215 := bstep (se 1 (by rfl) ⟨1795661, by rfl⟩ : syracuseStep 2394215 = 3591323) B3591323
theorem B186224021 : Blo 1060614 186224021 := bstep (se 6 (by rfl) ⟨4364625, by rfl⟩ : syracuseStep 186224021 = 8729251) B8729251
theorem B174230999 : Blo 1060614 174230999 := bstep (se 1 (by rfl) ⟨130673249, by rfl⟩ : syracuseStep 174230999 = 261346499) B261346499
theorem B18386459 : Blo 1060614 18386459 := bstep (se 1 (by rfl) ⟨13789844, by rfl⟩ : syracuseStep 18386459 = 27579689) B27579689
theorem B2692217 : Blo 1060614 2692217 := bstep (se 2 (by rfl) ⟨1009581, by rfl⟩ : syracuseStep 2692217 = 2019163) B2019163
theorem B5379695 : Blo 1060614 5379695 := bstep (se 1 (by rfl) ⟨4034771, by rfl⟩ : syracuseStep 5379695 = 8069543) B8069543
theorem B126097681 : Blo 1060614 126097681 := bstep (se 2 (by rfl) ⟨47286630, by rfl⟩ : syracuseStep 126097681 = 94573261) B94573261
theorem B15345359 : Blo 1060614 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B1060935 : Blo 1060614 1060935 := bstep (se 1 (by rfl) ⟨795701, by rfl⟩ : syracuseStep 1060935 = 1591403) B1591403
theorem B3585383 : Blo 1060614 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B8173979 : Blo 1060614 8173979 := bstep (se 1 (by rfl) ⟨6130484, by rfl⟩ : syracuseStep 8173979 = 12260969) B12260969
theorem B1063535 : Blo 1060614 1063535 := bstep (se 1 (by rfl) ⟨797651, by rfl⟩ : syracuseStep 1063535 = 1595303) B1595303
theorem B1064103 : Blo 1060614 1064103 := bstep (se 1 (by rfl) ⟨798077, by rfl⟩ : syracuseStep 1064103 = 1596155) B1596155
theorem B6799247 : Blo 1060614 6799247 := bstep (se 1 (by rfl) ⟨5099435, by rfl⟩ : syracuseStep 6799247 = 10198871) B10198871
theorem B2015131 : Blo 1060614 2015131 := bstep (se 1 (by rfl) ⟨1511348, by rfl⟩ : syracuseStep 2015131 = 3022697) B3022697
theorem B4539017 : Blo 1060614 4539017 := bstep (se 2 (by rfl) ⟨1702131, by rfl⟩ : syracuseStep 4539017 = 3404263) B3404263
theorem B4309787 : Blo 1060614 4309787 := bstep (se 1 (by rfl) ⟨3232340, by rfl⟩ : syracuseStep 4309787 = 6464681) B6464681
theorem B38847613 : Blo 1060614 38847613 := bstep (se 3 (by rfl) ⟨7283927, by rfl⟩ : syracuseStep 38847613 = 14567855) B14567855
theorem B9061631 : Blo 1060614 9061631 := bstep (se 1 (by rfl) ⟨6796223, by rfl⟩ : syracuseStep 9061631 = 13592447) B13592447
theorem B2016809 : Blo 1060614 2016809 := bstep (se 2 (by rfl) ⟨756303, by rfl⟩ : syracuseStep 2016809 = 1512607) B1512607
theorem B77548103 : Blo 1060614 77548103 := bstep (se 1 (by rfl) ⟨58161077, by rfl⟩ : syracuseStep 77548103 = 116322155) B116322155
theorem B3590891 : Blo 1060614 3590891 := bstep (se 1 (by rfl) ⟨2693168, by rfl⟩ : syracuseStep 3590891 = 5386337) B5386337
theorem B17255225 : Blo 1060614 17255225 := bstep (se 2 (by rfl) ⟨6470709, by rfl⟩ : syracuseStep 17255225 = 12941419) B12941419
theorem B1592297 : Blo 1060614 1592297 := bstep (se 2 (by rfl) ⟨597111, by rfl⟩ : syracuseStep 1592297 = 1194223) B1194223
theorem B6048877 : Blo 1060614 6048877 := bstep (se 3 (by rfl) ⟨1134164, by rfl⟩ : syracuseStep 6048877 = 2268329) B2268329
theorem B7655903 : Blo 1060614 7655903 := bstep (se 1 (by rfl) ⟨5741927, by rfl⟩ : syracuseStep 7655903 = 11483855) B11483855
theorem B1135463 : Blo 1060614 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B1594907 : Blo 1060614 1594907 := bstep (se 1 (by rfl) ⟨1196180, by rfl⟩ : syracuseStep 1594907 = 2392361) B2392361
theorem B3398689 : Blo 1060614 3398689 := bstep (se 2 (by rfl) ⟨1274508, by rfl⟩ : syracuseStep 3398689 = 2549017) B2549017
theorem B5528827 : Blo 1060614 5528827 := bstep (se 1 (by rfl) ⟨4146620, by rfl⟩ : syracuseStep 5528827 = 8293241) B8293241
theorem B3235261 : Blo 1060614 3235261 := bstep (se 3 (by rfl) ⟨606611, by rfl⟩ : syracuseStep 3235261 = 1213223) B1213223
theorem B27188783 : Blo 1060614 27188783 := bstep (se 1 (by rfl) ⟨20391587, by rfl⟩ : syracuseStep 27188783 = 40783175) B40783175
theorem B6054527 : Blo 1060614 6054527 := bstep (se 1 (by rfl) ⟨4540895, by rfl⟩ : syracuseStep 6054527 = 9081791) B9081791
theorem B4842451 : Blo 1060614 4842451 := bstep (se 1 (by rfl) ⟨3631838, by rfl⟩ : syracuseStep 4842451 = 7263677) B7263677
theorem B45935747 : Blo 1060614 45935747 := bstep (se 1 (by rfl) ⟨34451810, by rfl⟩ : syracuseStep 45935747 = 68903621) B68903621
theorem B2387879 : Blo 1060614 2387879 := bstep (se 1 (by rfl) ⟨1790909, by rfl⟩ : syracuseStep 2387879 = 3581819) B3581819
theorem B2388527 : Blo 1060614 2388527 := bstep (se 1 (by rfl) ⟨1791395, by rfl⟩ : syracuseStep 2388527 = 3582791) B3582791
theorem B2389499 : Blo 1060614 2389499 := bstep (se 1 (by rfl) ⟨1792124, by rfl⟩ : syracuseStep 2389499 = 3584249) B3584249
theorem B766539389 : Blo 1060614 766539389 := bstep (se 3 (by rfl) ⟨143726135, by rfl⟩ : syracuseStep 766539389 = 287452271) B287452271
theorem B223803091 : Blo 1060614 223803091 := bstep (se 1 (by rfl) ⟨167852318, by rfl⟩ : syracuseStep 223803091 = 335704637) B335704637
theorem B58980383 : Blo 1060614 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B2685737 : Blo 1060614 2685737 := bstep (se 2 (by rfl) ⟨1007151, by rfl⟩ : syracuseStep 2685737 = 2014303) B2014303
theorem B5110951 : Blo 1060614 5110951 := bstep (se 1 (by rfl) ⟨3833213, by rfl⟩ : syracuseStep 5110951 = 7666427) B7666427
theorem B15334697 : Blo 1060614 15334697 := bstep (se 2 (by rfl) ⟨5750511, by rfl⟩ : syracuseStep 15334697 = 11501023) B11501023
theorem B5111201 : Blo 1060614 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B1344539 : Blo 1060614 1344539 := bstep (se 1 (by rfl) ⟨1008404, by rfl⟩ : syracuseStep 1344539 = 2016809) B2016809
theorem B6456601 : Blo 1060614 6456601 := bstep (se 2 (by rfl) ⟨2421225, by rfl⟩ : syracuseStep 6456601 = 4842451) B4842451
theorem B2393927 : Blo 1060614 2393927 := bstep (se 1 (by rfl) ⟨1795445, by rfl⟩ : syracuseStep 2393927 = 3590891) B3590891
theorem B12257639 : Blo 1060614 12257639 := bstep (se 1 (by rfl) ⟨9193229, by rfl⟩ : syracuseStep 12257639 = 18386459) B18386459
theorem B8065169 : Blo 1060614 8065169 := bstep (se 2 (by rfl) ⟨3024438, by rfl⟩ : syracuseStep 8065169 = 6048877) B6048877
theorem B18125855 : Blo 1060614 18125855 := bstep (se 1 (by rfl) ⟨13594391, by rfl⟩ : syracuseStep 18125855 = 27188783) B27188783
theorem B4036351 : Blo 1060614 4036351 := bstep (se 1 (by rfl) ⟨3027263, by rfl⟩ : syracuseStep 4036351 = 6054527) B6054527
theorem B10230239 : Blo 1060614 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B46013933 : Blo 1060614 46013933 := bstep (se 3 (by rfl) ⟨8627612, by rfl⟩ : syracuseStep 46013933 = 17255225) B17255225
theorem B511026259 : Blo 1060614 511026259 := bstep (se 1 (by rfl) ⟨383269694, by rfl⟩ : syracuseStep 511026259 = 766539389) B766539389
theorem B1193616485 : Blo 1060614 1193616485 := bstep (se 4 (by rfl) ⟨111901545, by rfl⟩ : syracuseStep 1193616485 = 223803091) B223803091
theorem B4531585 : Blo 1060614 4531585 := bstep (se 2 (by rfl) ⟨1699344, by rfl⟩ : syracuseStep 4531585 = 3398689) B3398689
theorem B5449319 : Blo 1060614 5449319 := bstep (se 1 (by rfl) ⟨4086989, by rfl⟩ : syracuseStep 5449319 = 8173979) B8173979
theorem B4532831 : Blo 1060614 4532831 := bstep (se 1 (by rfl) ⟨3399623, by rfl⟩ : syracuseStep 4532831 = 6799247) B6799247
theorem B3026011 : Blo 1060614 3026011 := bstep (se 1 (by rfl) ⟨2269508, by rfl⟩ : syracuseStep 3026011 = 4539017) B4539017
theorem B6041087 : Blo 1060614 6041087 := bstep (se 1 (by rfl) ⟨4530815, by rfl⟩ : syracuseStep 6041087 = 9061631) B9061631
theorem B6467207 : Blo 1060614 6467207 := bstep (se 1 (by rfl) ⟨4850405, by rfl⟩ : syracuseStep 6467207 = 9700811) B9700811
theorem B20426579 : Blo 1060614 20426579 := bstep (se 1 (by rfl) ⟨15319934, by rfl⟩ : syracuseStep 20426579 = 30639869) B30639869
theorem B3583871 : Blo 1060614 3583871 := bstep (se 1 (by rfl) ⟨2687903, by rfl⟩ : syracuseStep 3583871 = 5375807) B5375807
theorem B1061531 : Blo 1060614 1061531 := bstep (se 1 (by rfl) ⟨796148, by rfl⟩ : syracuseStep 1061531 = 1592297) B1592297
theorem B1063271 : Blo 1060614 1063271 := bstep (se 1 (by rfl) ⟨797453, by rfl⟩ : syracuseStep 1063271 = 1594907) B1594907
theorem B3586463 : Blo 1060614 3586463 := bstep (se 1 (by rfl) ⟨2689847, by rfl⟩ : syracuseStep 3586463 = 5379695) B5379695
theorem B30623831 : Blo 1060614 30623831 := bstep (se 1 (by rfl) ⟨22967873, by rfl⟩ : syracuseStep 30623831 = 45935747) B45935747
theorem B1591919 : Blo 1060614 1591919 := bstep (se 1 (by rfl) ⟨1193939, by rfl⟩ : syracuseStep 1591919 = 2387879) B2387879
theorem B1592351 : Blo 1060614 1592351 := bstep (se 1 (by rfl) ⟨1194263, by rfl⟩ : syracuseStep 1592351 = 2388527) B2388527
theorem B1592999 : Blo 1060614 1592999 := bstep (se 1 (by rfl) ⟨1194749, by rfl⟩ : syracuseStep 1592999 = 2389499) B2389499
theorem B12111605 : Blo 1060614 12111605 := bstep (se 5 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 12111605 = 1135463) B1135463
theorem B1790491 : Blo 1060614 1790491 := bstep (se 1 (by rfl) ⟨1342868, by rfl⟩ : syracuseStep 1790491 = 2685737) B2685737
theorem B4313681 : Blo 1060614 4313681 := bstep (se 2 (by rfl) ⟨1617630, by rfl⟩ : syracuseStep 4313681 = 3235261) B3235261
theorem B1595111 : Blo 1060614 1595111 := bstep (se 1 (by rfl) ⟨1196333, by rfl⟩ : syracuseStep 1595111 = 2392667) B2392667
theorem B2873191 : Blo 1060614 2873191 := bstep (se 1 (by rfl) ⟨2154893, by rfl⟩ : syracuseStep 2873191 = 4309787) B4309787
theorem B1596071 : Blo 1060614 1596071 := bstep (se 1 (by rfl) ⟨1197053, by rfl⟩ : syracuseStep 1596071 = 2394107) B2394107
theorem B1596143 : Blo 1060614 1596143 := bstep (se 1 (by rfl) ⟨1197107, by rfl⟩ : syracuseStep 1596143 = 2394215) B2394215
theorem B51796817 : Blo 1060614 51796817 := bstep (se 2 (by rfl) ⟨19423806, by rfl⟩ : syracuseStep 51796817 = 38847613) B38847613
theorem B51698735 : Blo 1060614 51698735 := bstep (se 1 (by rfl) ⟨38774051, by rfl⟩ : syracuseStep 51698735 = 77548103) B77548103
theorem B124149347 : Blo 1060614 124149347 := bstep (se 1 (by rfl) ⟨93112010, by rfl⟩ : syracuseStep 124149347 = 186224021) B186224021
theorem B116153999 : Blo 1060614 116153999 := bstep (se 1 (by rfl) ⟨87115499, by rfl⟩ : syracuseStep 116153999 = 174230999) B174230999
theorem B5103935 : Blo 1060614 5103935 := bstep (se 1 (by rfl) ⟨3827951, by rfl⟩ : syracuseStep 5103935 = 7655903) B7655903
theorem B1794811 : Blo 1060614 1794811 := bstep (se 1 (by rfl) ⟨1346108, by rfl⟩ : syracuseStep 1794811 = 2692217) B2692217
theorem B6908125 : Blo 1060614 6908125 := bstep (se 3 (by rfl) ⟨1295273, by rfl⟩ : syracuseStep 6908125 = 2590547) B2590547
theorem B168130241 : Blo 1060614 168130241 := bstep (se 2 (by rfl) ⟨63048840, by rfl⟩ : syracuseStep 168130241 = 126097681) B126097681
theorem B2390255 : Blo 1060614 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B39320255 : Blo 1060614 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B6814601 : Blo 1060614 6814601 := bstep (se 2 (by rfl) ⟨2555475, by rfl⟩ : syracuseStep 6814601 = 5110951) B5110951
theorem B7371769 : Blo 1060614 7371769 := bstep (se 2 (by rfl) ⟨2764413, by rfl⟩ : syracuseStep 7371769 = 5528827) B5528827
theorem B10223131 : Blo 1060614 10223131 := bstep (se 1 (by rfl) ⟨7667348, by rfl⟩ : syracuseStep 10223131 = 15334697) B15334697
theorem B3407467 : Blo 1060614 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B2686841 : Blo 1060614 2686841 := bstep (se 2 (by rfl) ⟨1007565, by rfl⟩ : syracuseStep 2686841 = 2015131) B2015131
theorem B2393081 : Blo 1060614 2393081 := bstep (se 2 (by rfl) ⟨897405, by rfl⟩ : syracuseStep 2393081 = 1794811) B1794811
theorem B20415887 : Blo 1060614 20415887 := bstep (se 1 (by rfl) ⟨15311915, by rfl⟩ : syracuseStep 20415887 = 30623831) B30623831
theorem B5376779 : Blo 1060614 5376779 := bstep (se 1 (by rfl) ⟨4032584, by rfl⟩ : syracuseStep 5376779 = 8065169) B8065169
theorem B9210833 : Blo 1060614 9210833 := bstep (se 2 (by rfl) ⟨3454062, by rfl⟩ : syracuseStep 9210833 = 6908125) B6908125
theorem B4034681 : Blo 1060614 4034681 := bstep (se 2 (by rfl) ⟨1513005, by rfl⟩ : syracuseStep 4034681 = 3026011) B3026011
theorem B30675955 : Blo 1060614 30675955 := bstep (se 1 (by rfl) ⟨23006966, by rfl⟩ : syracuseStep 30675955 = 46013933) B46013933
theorem B77435999 : Blo 1060614 77435999 := bstep (se 1 (by rfl) ⟨58076999, by rfl⟩ : syracuseStep 77435999 = 116153999) B116153999
theorem B795744323 : Blo 1060614 795744323 := bstep (se 1 (by rfl) ⟨596808242, by rfl⟩ : syracuseStep 795744323 = 1193616485) B1193616485
theorem B3021887 : Blo 1060614 3021887 := bstep (se 1 (by rfl) ⟨2266415, by rfl⟩ : syracuseStep 3021887 = 4532831) B4532831
theorem B5381801 : Blo 1060614 5381801 := bstep (se 2 (by rfl) ⟨2018175, by rfl⟩ : syracuseStep 5381801 = 4036351) B4036351
theorem B17245885 : Blo 1060614 17245885 := bstep (se 3 (by rfl) ⟨3233603, by rfl⟩ : syracuseStep 17245885 = 6467207) B6467207
theorem B8171759 : Blo 1060614 8171759 := bstep (se 1 (by rfl) ⟨6128819, by rfl⟩ : syracuseStep 8171759 = 12257639) B12257639
theorem B1061279 : Blo 1060614 1061279 := bstep (se 1 (by rfl) ⟨795959, by rfl⟩ : syracuseStep 1061279 = 1591919) B1591919
theorem B6042113 : Blo 1060614 6042113 := bstep (se 2 (by rfl) ⟨2265792, by rfl⟩ : syracuseStep 6042113 = 4531585) B4531585
theorem B1061567 : Blo 1060614 1061567 := bstep (se 1 (by rfl) ⟨796175, by rfl⟩ : syracuseStep 1061567 = 1592351) B1592351
theorem B1061999 : Blo 1060614 1061999 := bstep (se 1 (by rfl) ⟨796499, by rfl⟩ : syracuseStep 1061999 = 1592999) B1592999
theorem B8074403 : Blo 1060614 8074403 := bstep (se 1 (by rfl) ⟨6055802, by rfl⟩ : syracuseStep 8074403 = 12111605) B12111605
theorem B3585437 : Blo 1060614 3585437 := bstep (se 3 (by rfl) ⟨672269, by rfl⟩ : syracuseStep 3585437 = 1344539) B1344539
theorem B1063407 : Blo 1060614 1063407 := bstep (se 1 (by rfl) ⟨797555, by rfl⟩ : syracuseStep 1063407 = 1595111) B1595111
theorem B1064047 : Blo 1060614 1064047 := bstep (se 1 (by rfl) ⟨798035, by rfl⟩ : syracuseStep 1064047 = 1596071) B1596071
theorem B1064095 : Blo 1060614 1064095 := bstep (se 1 (by rfl) ⟨798071, by rfl⟩ : syracuseStep 1064095 = 1596143) B1596143
theorem B27280637 : Blo 1060614 27280637 := bstep (se 3 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 27280637 = 10230239) B10230239
theorem B13617719 : Blo 1060614 13617719 := bstep (se 1 (by rfl) ⟨10213289, by rfl⟩ : syracuseStep 13617719 = 20426579) B20426579
theorem B112086827 : Blo 1060614 112086827 := bstep (se 1 (by rfl) ⟨84065120, by rfl⟩ : syracuseStep 112086827 = 168130241) B168130241
theorem B1593503 : Blo 1060614 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B4543067 : Blo 1060614 4543067 := bstep (se 1 (by rfl) ⟨3407300, by rfl⟩ : syracuseStep 4543067 = 6814601) B6814601
theorem B4543289 : Blo 1060614 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B1791227 : Blo 1060614 1791227 := bstep (se 1 (by rfl) ⟨1343420, by rfl⟩ : syracuseStep 1791227 = 2686841) B2686841
theorem B1595951 : Blo 1060614 1595951 := bstep (se 1 (by rfl) ⟨1196963, by rfl⟩ : syracuseStep 1595951 = 2393927) B2393927
theorem B681368345 : Blo 1060614 681368345 := bstep (se 2 (by rfl) ⟨255513129, by rfl⟩ : syracuseStep 681368345 = 511026259) B511026259
theorem B2875787 : Blo 1060614 2875787 := bstep (se 1 (by rfl) ⟨2156840, by rfl⟩ : syracuseStep 2875787 = 4313681) B4313681
theorem B12083903 : Blo 1060614 12083903 := bstep (se 1 (by rfl) ⟨9062927, by rfl⟩ : syracuseStep 12083903 = 18125855) B18125855
theorem B34531211 : Blo 1060614 34531211 := bstep (se 1 (by rfl) ⟨25898408, by rfl⟩ : syracuseStep 34531211 = 51796817) B51796817
theorem B34465823 : Blo 1060614 34465823 := bstep (se 1 (by rfl) ⟨25849367, by rfl⟩ : syracuseStep 34465823 = 51698735) B51698735
theorem B82766231 : Blo 1060614 82766231 := bstep (se 1 (by rfl) ⟨62074673, by rfl⟩ : syracuseStep 82766231 = 124149347) B124149347
theorem B3402623 : Blo 1060614 3402623 := bstep (se 1 (by rfl) ⟨2551967, by rfl⟩ : syracuseStep 3402623 = 5103935) B5103935
theorem B2387321 : Blo 1060614 2387321 := bstep (se 2 (by rfl) ⟨895245, by rfl⟩ : syracuseStep 2387321 = 1790491) B1790491
theorem B3632879 : Blo 1060614 3632879 := bstep (se 1 (by rfl) ⟨2724659, by rfl⟩ : syracuseStep 3632879 = 5449319) B5449319
theorem B34435205 : Blo 1060614 34435205 := bstep (se 4 (by rfl) ⟨3228300, by rfl⟩ : syracuseStep 34435205 = 6456601) B6456601
theorem B4027391 : Blo 1060614 4027391 := bstep (se 1 (by rfl) ⟨3020543, by rfl⟩ : syracuseStep 4027391 = 6041087) B6041087
theorem B3830921 : Blo 1060614 3830921 := bstep (se 2 (by rfl) ⟨1436595, by rfl⟩ : syracuseStep 3830921 = 2873191) B2873191
theorem B2389247 : Blo 1060614 2389247 := bstep (se 1 (by rfl) ⟨1791935, by rfl⟩ : syracuseStep 2389247 = 3583871) B3583871
theorem B9829025 : Blo 1060614 9829025 := bstep (se 2 (by rfl) ⟨3685884, by rfl⟩ : syracuseStep 9829025 = 7371769) B7371769
theorem B2390975 : Blo 1060614 2390975 := bstep (se 1 (by rfl) ⟨1793231, by rfl⟩ : syracuseStep 2390975 = 3586463) B3586463
theorem B26213503 : Blo 1060614 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B13630841 : Blo 1060614 13630841 := bstep (se 2 (by rfl) ⟨5111565, by rfl⟩ : syracuseStep 13630841 = 10223131) B10223131
theorem B18187091 : Blo 1060614 18187091 := bstep (se 1 (by rfl) ⟨13640318, by rfl⟩ : syracuseStep 18187091 = 27280637) B27280637
theorem B9078479 : Blo 1060614 9078479 := bstep (se 1 (by rfl) ⟨6808859, by rfl⟩ : syracuseStep 9078479 = 13617719) B13617719
theorem B2689787 : Blo 1060614 2689787 := bstep (se 1 (by rfl) ⟨2017340, by rfl⟩ : syracuseStep 2689787 = 4034681) B4034681
theorem B40901273 : Blo 1060614 40901273 := bstep (se 2 (by rfl) ⟨15337977, by rfl⟩ : syracuseStep 40901273 = 30675955) B30675955
theorem B22977215 : Blo 1060614 22977215 := bstep (se 1 (by rfl) ⟨17232911, by rfl⟩ : syracuseStep 22977215 = 34465823) B34465823
theorem B2268415 : Blo 1060614 2268415 := bstep (se 1 (by rfl) ⟨1701311, by rfl⟩ : syracuseStep 2268415 = 3402623) B3402623
theorem B5447839 : Blo 1060614 5447839 := bstep (se 1 (by rfl) ⟨4085879, by rfl⟩ : syracuseStep 5447839 = 8171759) B8171759
theorem B5382935 : Blo 1060614 5382935 := bstep (se 1 (by rfl) ⟨4037201, by rfl⟩ : syracuseStep 5382935 = 8074403) B8074403
theorem B9087227 : Blo 1060614 9087227 := bstep (se 1 (by rfl) ⟨6815420, by rfl⟩ : syracuseStep 9087227 = 13630841) B13630841
theorem B13610591 : Blo 1060614 13610591 := bstep (se 1 (by rfl) ⟨10207943, by rfl⟩ : syracuseStep 13610591 = 20415887) B20415887
theorem B3584519 : Blo 1060614 3584519 := bstep (se 1 (by rfl) ⟨2688389, by rfl⟩ : syracuseStep 3584519 = 5376779) B5376779
theorem B6140555 : Blo 1060614 6140555 := bstep (se 1 (by rfl) ⟨4605416, by rfl⟩ : syracuseStep 6140555 = 9210833) B9210833
theorem B74724551 : Blo 1060614 74724551 := bstep (se 1 (by rfl) ⟨56043413, by rfl⟩ : syracuseStep 74724551 = 112086827) B112086827
theorem B1062335 : Blo 1060614 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B3028711 : Blo 1060614 3028711 := bstep (se 1 (by rfl) ⟨2271533, by rfl⟩ : syracuseStep 3028711 = 4543067) B4543067
theorem B3028859 : Blo 1060614 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B51623999 : Blo 1060614 51623999 := bstep (se 1 (by rfl) ⟨38717999, by rfl⟩ : syracuseStep 51623999 = 77435999) B77435999
theorem B1194151 : Blo 1060614 1194151 := bstep (se 1 (by rfl) ⟨895613, by rfl⟩ : syracuseStep 1194151 = 1791227) B1791227
theorem B530496215 : Blo 1060614 530496215 := bstep (se 1 (by rfl) ⟨397872161, by rfl⟩ : syracuseStep 530496215 = 795744323) B795744323
theorem B1063967 : Blo 1060614 1063967 := bstep (se 1 (by rfl) ⟨797975, by rfl⟩ : syracuseStep 1063967 = 1595951) B1595951
theorem B454245563 : Blo 1060614 454245563 := bstep (se 1 (by rfl) ⟨340684172, by rfl⟩ : syracuseStep 454245563 = 681368345) B681368345
theorem B3587867 : Blo 1060614 3587867 := bstep (se 1 (by rfl) ⟨2690900, by rfl⟩ : syracuseStep 3587867 = 5381801) B5381801
theorem B1917191 : Blo 1060614 1917191 := bstep (se 1 (by rfl) ⟨1437893, by rfl⟩ : syracuseStep 1917191 = 2875787) B2875787
theorem B23020807 : Blo 1060614 23020807 := bstep (se 1 (by rfl) ⟨17265605, by rfl⟩ : syracuseStep 23020807 = 34531211) B34531211
theorem B1591547 : Blo 1060614 1591547 := bstep (se 1 (by rfl) ⟨1193660, by rfl⟩ : syracuseStep 1591547 = 2387321) B2387321
theorem B22956803 : Blo 1060614 22956803 := bstep (se 1 (by rfl) ⟨17217602, by rfl⟩ : syracuseStep 22956803 = 34435205) B34435205
theorem B1592831 : Blo 1060614 1592831 := bstep (se 1 (by rfl) ⟨1194623, by rfl⟩ : syracuseStep 1592831 = 2389247) B2389247
theorem B34951337 : Blo 1060614 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B1593983 : Blo 1060614 1593983 := bstep (se 1 (by rfl) ⟨1195487, by rfl⟩ : syracuseStep 1593983 = 2390975) B2390975
theorem B1595387 : Blo 1060614 1595387 := bstep (se 1 (by rfl) ⟨1196540, by rfl⟩ : syracuseStep 1595387 = 2393081) B2393081
theorem B22994513 : Blo 1060614 22994513 := bstep (se 2 (by rfl) ⟨8622942, by rfl⟩ : syracuseStep 22994513 = 17245885) B17245885
theorem B8055935 : Blo 1060614 8055935 := bstep (se 1 (by rfl) ⟨6041951, by rfl⟩ : syracuseStep 8055935 = 12083903) B12083903
theorem B55177487 : Blo 1060614 55177487 := bstep (se 1 (by rfl) ⟨41383115, by rfl⟩ : syracuseStep 55177487 = 82766231) B82766231
theorem B2421919 : Blo 1060614 2421919 := bstep (se 1 (by rfl) ⟨1816439, by rfl⟩ : syracuseStep 2421919 = 3632879) B3632879
theorem B8058365 : Blo 1060614 8058365 := bstep (se 3 (by rfl) ⟨1510943, by rfl⟩ : syracuseStep 8058365 = 3021887) B3021887
theorem B4028075 : Blo 1060614 4028075 := bstep (se 1 (by rfl) ⟨3021056, by rfl⟩ : syracuseStep 4028075 = 6042113) B6042113
theorem B2684927 : Blo 1060614 2684927 := bstep (se 1 (by rfl) ⟨2013695, by rfl⟩ : syracuseStep 2684927 = 4027391) B4027391
theorem B2553947 : Blo 1060614 2553947 := bstep (se 1 (by rfl) ⟨1915460, by rfl⟩ : syracuseStep 2553947 = 3830921) B3830921
theorem B2390291 : Blo 1060614 2390291 := bstep (se 1 (by rfl) ⟨1792718, by rfl⟩ : syracuseStep 2390291 = 3585437) B3585437
theorem B6552683 : Blo 1060614 6552683 := bstep (se 1 (by rfl) ⟨4914512, by rfl⟩ : syracuseStep 6552683 = 9829025) B9829025
theorem B1278127 : Blo 1060614 1278127 := bstep (se 1 (by rfl) ⟨958595, by rfl⟩ : syracuseStep 1278127 = 1917191) B1917191
theorem B12124727 : Blo 1060614 12124727 := bstep (se 1 (by rfl) ⟨9093545, by rfl⟩ : syracuseStep 12124727 = 18187091) B18187091
theorem B15304535 : Blo 1060614 15304535 := bstep (se 1 (by rfl) ⟨11478401, by rfl⟩ : syracuseStep 15304535 = 22956803) B22956803
theorem B23300891 : Blo 1060614 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B27267515 : Blo 1060614 27267515 := bstep (se 1 (by rfl) ⟨20450636, by rfl⟩ : syracuseStep 27267515 = 40901273) B40901273
theorem B12916901 : Blo 1060614 12916901 := bstep (se 4 (by rfl) ⟨1210959, by rfl⟩ : syracuseStep 12916901 = 2421919) B2421919
theorem B4038281 : Blo 1060614 4038281 := bstep (se 2 (by rfl) ⟨1514355, by rfl⟩ : syracuseStep 4038281 = 3028711) B3028711
theorem B49816367 : Blo 1060614 49816367 := bstep (se 1 (by rfl) ⟨37362275, by rfl⟩ : syracuseStep 49816367 = 74724551) B74724551
theorem B34415999 : Blo 1060614 34415999 := bstep (se 1 (by rfl) ⟨25811999, by rfl⟩ : syracuseStep 34415999 = 51623999) B51623999
theorem B3024553 : Blo 1060614 3024553 := bstep (se 2 (by rfl) ⟨1134207, by rfl⟩ : syracuseStep 3024553 = 2268415) B2268415
theorem B4368455 : Blo 1060614 4368455 := bstep (se 1 (by rfl) ⟨3276341, by rfl⟩ : syracuseStep 4368455 = 6552683) B6552683
theorem B1061031 : Blo 1060614 1061031 := bstep (se 1 (by rfl) ⟨795773, by rfl⟩ : syracuseStep 1061031 = 1591547) B1591547
theorem B1061887 : Blo 1060614 1061887 := bstep (se 1 (by rfl) ⟨796415, by rfl⟩ : syracuseStep 1061887 = 1592831) B1592831
theorem B1062655 : Blo 1060614 1062655 := bstep (se 1 (by rfl) ⟨796991, by rfl⟩ : syracuseStep 1062655 = 1593983) B1593983
theorem B1063591 : Blo 1060614 1063591 := bstep (se 1 (by rfl) ⟨797693, by rfl⟩ : syracuseStep 1063591 = 1595387) B1595387
theorem B15318143 : Blo 1060614 15318143 := bstep (se 1 (by rfl) ⟨11488607, by rfl⟩ : syracuseStep 15318143 = 22977215) B22977215
theorem B3588623 : Blo 1060614 3588623 := bstep (se 1 (by rfl) ⟨2691467, by rfl⟩ : syracuseStep 3588623 = 5382935) B5382935
theorem B36784991 : Blo 1060614 36784991 := bstep (se 1 (by rfl) ⟨27588743, by rfl⟩ : syracuseStep 36784991 = 55177487) B55177487
theorem B1592201 : Blo 1060614 1592201 := bstep (se 2 (by rfl) ⟨597075, by rfl⟩ : syracuseStep 1592201 = 1194151) B1194151
theorem B2019239 : Blo 1060614 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B1789951 : Blo 1060614 1789951 := bstep (se 1 (by rfl) ⟨1342463, by rfl⟩ : syracuseStep 1789951 = 2684927) B2684927
theorem B1593527 : Blo 1060614 1593527 := bstep (se 1 (by rfl) ⟨1195145, by rfl⟩ : syracuseStep 1593527 = 2390291) B2390291
theorem B302830375 : Blo 1060614 302830375 := bstep (se 1 (by rfl) ⟨227122781, by rfl⟩ : syracuseStep 302830375 = 454245563) B454245563
theorem B7263785 : Blo 1060614 7263785 := bstep (se 2 (by rfl) ⟨2723919, by rfl⟩ : syracuseStep 7263785 = 5447839) B5447839
theorem B6052319 : Blo 1060614 6052319 := bstep (se 1 (by rfl) ⟨4539239, by rfl⟩ : syracuseStep 6052319 = 9078479) B9078479
theorem B30694409 : Blo 1060614 30694409 := bstep (se 2 (by rfl) ⟨11510403, by rfl⟩ : syracuseStep 30694409 = 23020807) B23020807
theorem B1793191 : Blo 1060614 1793191 := bstep (se 1 (by rfl) ⟨1344893, by rfl⟩ : syracuseStep 1793191 = 2689787) B2689787
theorem B15329675 : Blo 1060614 15329675 := bstep (se 1 (by rfl) ⟨11497256, by rfl⟩ : syracuseStep 15329675 = 22994513) B22994513
theorem B6058151 : Blo 1060614 6058151 := bstep (se 1 (by rfl) ⟨4543613, by rfl⟩ : syracuseStep 6058151 = 9087227) B9087227
theorem B5370623 : Blo 1060614 5370623 := bstep (se 1 (by rfl) ⟨4027967, by rfl⟩ : syracuseStep 5370623 = 8055935) B8055935
theorem B9073727 : Blo 1060614 9073727 := bstep (se 1 (by rfl) ⟨6805295, by rfl⟩ : syracuseStep 9073727 = 13610591) B13610591
theorem B2389679 : Blo 1060614 2389679 := bstep (se 1 (by rfl) ⟨1792259, by rfl⟩ : syracuseStep 2389679 = 3584519) B3584519
theorem B4093703 : Blo 1060614 4093703 := bstep (se 1 (by rfl) ⟨3070277, by rfl⟩ : syracuseStep 4093703 = 6140555) B6140555
theorem B5372243 : Blo 1060614 5372243 := bstep (se 1 (by rfl) ⟨4029182, by rfl⟩ : syracuseStep 5372243 = 8058365) B8058365
theorem B2685383 : Blo 1060614 2685383 := bstep (se 1 (by rfl) ⟨2014037, by rfl⟩ : syracuseStep 2685383 = 4028075) B4028075
theorem B1702631 : Blo 1060614 1702631 := bstep (se 1 (by rfl) ⟨1276973, by rfl⟩ : syracuseStep 1702631 = 2553947) B2553947
theorem B353664143 : Blo 1060614 353664143 := bstep (se 1 (by rfl) ⟨265248107, by rfl⟩ : syracuseStep 353664143 = 530496215) B530496215
theorem B2391911 : Blo 1060614 2391911 := bstep (se 1 (by rfl) ⟨1793933, by rfl⟩ : syracuseStep 2391911 = 3587867) B3587867
theorem B1704169 : Blo 1060614 1704169 := bstep (se 2 (by rfl) ⟨639063, by rfl⟩ : syracuseStep 1704169 = 1278127) B1278127
theorem B2392415 : Blo 1060614 2392415 := bstep (se 1 (by rfl) ⟨1794311, by rfl⟩ : syracuseStep 2392415 = 3588623) B3588623
theorem B15533927 : Blo 1060614 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B4032737 : Blo 1060614 4032737 := bstep (se 2 (by rfl) ⟨1512276, by rfl⟩ : syracuseStep 4032737 = 3024553) B3024553
theorem B1346159 : Blo 1060614 1346159 := bstep (se 1 (by rfl) ⟨1009619, by rfl⟩ : syracuseStep 1346159 = 2019239) B2019239
theorem B4034879 : Blo 1060614 4034879 := bstep (se 1 (by rfl) ⟨3026159, by rfl⟩ : syracuseStep 4034879 = 6052319) B6052319
theorem B2692187 : Blo 1060614 2692187 := bstep (se 1 (by rfl) ⟨2019140, by rfl⟩ : syracuseStep 2692187 = 4038281) B4038281
theorem B22943999 : Blo 1060614 22943999 := bstep (se 1 (by rfl) ⟨17207999, by rfl⟩ : syracuseStep 22943999 = 34415999) B34415999
theorem B403773833 : Blo 1060614 403773833 := bstep (se 2 (by rfl) ⟨151415187, by rfl⟩ : syracuseStep 403773833 = 302830375) B302830375
theorem B4038767 : Blo 1060614 4038767 := bstep (se 1 (by rfl) ⟨3029075, by rfl⟩ : syracuseStep 4038767 = 6058151) B6058151
theorem B3580415 : Blo 1060614 3580415 := bstep (se 1 (by rfl) ⟨2685311, by rfl⟩ : syracuseStep 3580415 = 5370623) B5370623
theorem B2729135 : Blo 1060614 2729135 := bstep (se 1 (by rfl) ⟨2046851, by rfl⟩ : syracuseStep 2729135 = 4093703) B4093703
theorem B3581495 : Blo 1060614 3581495 := bstep (se 1 (by rfl) ⟨2686121, by rfl⟩ : syracuseStep 3581495 = 5372243) B5372243
theorem B235776095 : Blo 1060614 235776095 := bstep (se 1 (by rfl) ⟨176832071, by rfl⟩ : syracuseStep 235776095 = 353664143) B353664143
theorem B10203023 : Blo 1060614 10203023 := bstep (se 1 (by rfl) ⟨7652267, by rfl⟩ : syracuseStep 10203023 = 15304535) B15304535
theorem B24523327 : Blo 1060614 24523327 := bstep (se 1 (by rfl) ⟨18392495, by rfl⟩ : syracuseStep 24523327 = 36784991) B36784991
theorem B1061467 : Blo 1060614 1061467 := bstep (se 1 (by rfl) ⟨796100, by rfl⟩ : syracuseStep 1061467 = 1592201) B1592201
theorem B1062351 : Blo 1060614 1062351 := bstep (se 1 (by rfl) ⟨796763, by rfl⟩ : syracuseStep 1062351 = 1593527) B1593527
theorem B20462939 : Blo 1060614 20462939 := bstep (se 1 (by rfl) ⟨15347204, by rfl⟩ : syracuseStep 20462939 = 30694409) B30694409
theorem B33210911 : Blo 1060614 33210911 := bstep (se 1 (by rfl) ⟨24908183, by rfl⟩ : syracuseStep 33210911 = 49816367) B49816367
theorem B4540349 : Blo 1060614 4540349 := bstep (se 3 (by rfl) ⟨851315, by rfl⟩ : syracuseStep 4540349 = 1702631) B1702631
theorem B6049151 : Blo 1060614 6049151 := bstep (se 1 (by rfl) ⟨4536863, by rfl⟩ : syracuseStep 6049151 = 9073727) B9073727
theorem B1593119 : Blo 1060614 1593119 := bstep (se 1 (by rfl) ⟨1194839, by rfl⟩ : syracuseStep 1593119 = 2389679) B2389679
theorem B1790255 : Blo 1060614 1790255 := bstep (se 1 (by rfl) ⟨1342691, by rfl⟩ : syracuseStep 1790255 = 2685383) B2685383
theorem B10212095 : Blo 1060614 10212095 := bstep (se 1 (by rfl) ⟨7659071, by rfl⟩ : syracuseStep 10212095 = 15318143) B15318143
theorem B1594607 : Blo 1060614 1594607 := bstep (se 1 (by rfl) ⟨1195955, by rfl⟩ : syracuseStep 1594607 = 2391911) B2391911
theorem B8083151 : Blo 1060614 8083151 := bstep (se 1 (by rfl) ⟨6062363, by rfl⟩ : syracuseStep 8083151 = 12124727) B12124727
theorem B18178343 : Blo 1060614 18178343 := bstep (se 1 (by rfl) ⟨13633757, by rfl⟩ : syracuseStep 18178343 = 27267515) B27267515
theorem B4842523 : Blo 1060614 4842523 := bstep (se 1 (by rfl) ⟨3631892, by rfl⟩ : syracuseStep 4842523 = 7263785) B7263785
theorem B8611267 : Blo 1060614 8611267 := bstep (se 1 (by rfl) ⟨6458450, by rfl⟩ : syracuseStep 8611267 = 12916901) B12916901
theorem B2386601 : Blo 1060614 2386601 := bstep (se 2 (by rfl) ⟨894975, by rfl⟩ : syracuseStep 2386601 = 1789951) B1789951
theorem B2912303 : Blo 1060614 2912303 := bstep (se 1 (by rfl) ⟨2184227, by rfl⟩ : syracuseStep 2912303 = 4368455) B4368455
theorem B10219783 : Blo 1060614 10219783 := bstep (se 1 (by rfl) ⟨7664837, by rfl⟩ : syracuseStep 10219783 = 15329675) B15329675
theorem B2390921 : Blo 1060614 2390921 := bstep (se 2 (by rfl) ⟨896595, by rfl⟩ : syracuseStep 2390921 = 1793191) B1793191
theorem B10355951 : Blo 1060614 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B2688491 : Blo 1060614 2688491 := bstep (se 1 (by rfl) ⟨2016368, by rfl⟩ : syracuseStep 2688491 = 4032737) B4032737
theorem B4032767 : Blo 1060614 4032767 := bstep (se 1 (by rfl) ⟨3024575, by rfl⟩ : syracuseStep 4032767 = 6049151) B6049151
theorem B2689919 : Blo 1060614 2689919 := bstep (se 1 (by rfl) ⟨2017439, by rfl⟩ : syracuseStep 2689919 = 4034879) B4034879
theorem B2692511 : Blo 1060614 2692511 := bstep (se 1 (by rfl) ⟨2019383, by rfl⟩ : syracuseStep 2692511 = 4038767) B4038767
theorem B25826789 : Blo 1060614 25826789 := bstep (se 4 (by rfl) ⟨2421261, by rfl⟩ : syracuseStep 25826789 = 4842523) B4842523
theorem B1076730221 : Blo 1060614 1076730221 := bstep (se 3 (by rfl) ⟨201886916, by rfl⟩ : syracuseStep 1076730221 = 403773833) B403773833
theorem B1941535 : Blo 1060614 1941535 := bstep (se 1 (by rfl) ⟨1456151, by rfl⟩ : syracuseStep 1941535 = 2912303) B2912303
theorem B13641959 : Blo 1060614 13641959 := bstep (se 1 (by rfl) ⟨10231469, by rfl⟩ : syracuseStep 13641959 = 20462939) B20462939
theorem B2272225 : Blo 1060614 2272225 := bstep (se 2 (by rfl) ⟨852084, by rfl⟩ : syracuseStep 2272225 = 1704169) B1704169
theorem B3026899 : Blo 1060614 3026899 := bstep (se 1 (by rfl) ⟨2270174, by rfl⟩ : syracuseStep 3026899 = 4540349) B4540349
theorem B11481689 : Blo 1060614 11481689 := bstep (se 2 (by rfl) ⟨4305633, by rfl⟩ : syracuseStep 11481689 = 8611267) B8611267
theorem B1062079 : Blo 1060614 1062079 := bstep (se 1 (by rfl) ⟨796559, by rfl⟩ : syracuseStep 1062079 = 1593119) B1593119
theorem B1193503 : Blo 1060614 1193503 := bstep (se 1 (by rfl) ⟨895127, by rfl⟩ : syracuseStep 1193503 = 1790255) B1790255
theorem B1063071 : Blo 1060614 1063071 := bstep (se 1 (by rfl) ⟨797303, by rfl⟩ : syracuseStep 1063071 = 1594607) B1594607
theorem B5388767 : Blo 1060614 5388767 := bstep (se 1 (by rfl) ⟨4041575, by rfl⟩ : syracuseStep 5388767 = 8083151) B8083151
theorem B1819423 : Blo 1060614 1819423 := bstep (se 1 (by rfl) ⟨1364567, by rfl⟩ : syracuseStep 1819423 = 2729135) B2729135
theorem B3589757 : Blo 1060614 3589757 := bstep (se 3 (by rfl) ⟨673079, by rfl⟩ : syracuseStep 3589757 = 1346159) B1346159
theorem B1591067 : Blo 1060614 1591067 := bstep (se 1 (by rfl) ⟨1193300, by rfl⟩ : syracuseStep 1591067 = 2386601) B2386601
theorem B6802015 : Blo 1060614 6802015 := bstep (se 1 (by rfl) ⟨5101511, by rfl⟩ : syracuseStep 6802015 = 10203023) B10203023
theorem B1593947 : Blo 1060614 1593947 := bstep (se 1 (by rfl) ⟨1195460, by rfl⟩ : syracuseStep 1593947 = 2390921) B2390921
theorem B1594943 : Blo 1060614 1594943 := bstep (se 1 (by rfl) ⟨1196207, by rfl⟩ : syracuseStep 1594943 = 2392415) B2392415
theorem B88562429 : Blo 1060614 88562429 := bstep (se 3 (by rfl) ⟨16605455, by rfl⟩ : syracuseStep 88562429 = 33210911) B33210911
theorem B6808063 : Blo 1060614 6808063 := bstep (se 1 (by rfl) ⟨5106047, by rfl⟩ : syracuseStep 6808063 = 10212095) B10212095
theorem B1794791 : Blo 1060614 1794791 := bstep (se 1 (by rfl) ⟨1346093, by rfl⟩ : syracuseStep 1794791 = 2692187) B2692187
theorem B15295999 : Blo 1060614 15295999 := bstep (se 1 (by rfl) ⟨11471999, by rfl⟩ : syracuseStep 15295999 = 22943999) B22943999
theorem B12118895 : Blo 1060614 12118895 := bstep (se 1 (by rfl) ⟨9089171, by rfl⟩ : syracuseStep 12118895 = 18178343) B18178343
theorem B2386943 : Blo 1060614 2386943 := bstep (se 1 (by rfl) ⟨1790207, by rfl⟩ : syracuseStep 2386943 = 3580415) B3580415
theorem B13626377 : Blo 1060614 13626377 := bstep (se 2 (by rfl) ⟨5109891, by rfl⟩ : syracuseStep 13626377 = 10219783) B10219783
theorem B32697769 : Blo 1060614 32697769 := bstep (se 2 (by rfl) ⟨12261663, by rfl⟩ : syracuseStep 32697769 = 24523327) B24523327
theorem B2387663 : Blo 1060614 2387663 := bstep (se 1 (by rfl) ⟨1790747, by rfl⟩ : syracuseStep 2387663 = 3581495) B3581495
theorem B157184063 : Blo 1060614 157184063 := bstep (se 1 (by rfl) ⟨117888047, by rfl⟩ : syracuseStep 157184063 = 235776095) B235776095
theorem B10354853 : Blo 1060614 10354853 := bstep (se 4 (by rfl) ⟨970767, by rfl⟩ : syracuseStep 10354853 = 1941535) B1941535
theorem B9077417 : Blo 1060614 9077417 := bstep (se 2 (by rfl) ⟨3404031, by rfl⟩ : syracuseStep 9077417 = 6808063) B6808063
theorem B2425897 : Blo 1060614 2425897 := bstep (se 2 (by rfl) ⟨909711, by rfl⟩ : syracuseStep 2425897 = 1819423) B1819423
theorem B2393171 : Blo 1060614 2393171 := bstep (se 1 (by rfl) ⟨1794878, by rfl⟩ : syracuseStep 2393171 = 3589757) B3589757
theorem B2688511 : Blo 1060614 2688511 := bstep (se 1 (by rfl) ⟨2016383, by rfl⟩ : syracuseStep 2688511 = 4032767) B4032767
theorem B717820147 : Blo 1060614 717820147 := bstep (se 1 (by rfl) ⟨538365110, by rfl⟩ : syracuseStep 717820147 = 1076730221) B1076730221
theorem B4035865 : Blo 1060614 4035865 := bstep (se 2 (by rfl) ⟨1513449, by rfl⟩ : syracuseStep 4035865 = 3026899) B3026899
theorem B9084251 : Blo 1060614 9084251 := bstep (se 1 (by rfl) ⟨6813188, by rfl⟩ : syracuseStep 9084251 = 13626377) B13626377
theorem B1060711 : Blo 1060614 1060711 := bstep (se 1 (by rfl) ⟨795533, by rfl⟩ : syracuseStep 1060711 = 1591067) B1591067
theorem B20394665 : Blo 1060614 20394665 := bstep (se 2 (by rfl) ⟨7647999, by rfl⟩ : syracuseStep 20394665 = 15295999) B15295999
theorem B1062631 : Blo 1060614 1062631 := bstep (se 1 (by rfl) ⟨796973, by rfl⟩ : syracuseStep 1062631 = 1593947) B1593947
theorem B17217859 : Blo 1060614 17217859 := bstep (se 1 (by rfl) ⟨12913394, by rfl⟩ : syracuseStep 17217859 = 25826789) B25826789
theorem B1063295 : Blo 1060614 1063295 := bstep (se 1 (by rfl) ⟨797471, by rfl⟩ : syracuseStep 1063295 = 1594943) B1594943
theorem B3029633 : Blo 1060614 3029633 := bstep (se 2 (by rfl) ⟨1136112, by rfl⟩ : syracuseStep 3029633 = 2272225) B2272225
theorem B43597025 : Blo 1060614 43597025 := bstep (se 2 (by rfl) ⟨16348884, by rfl⟩ : syracuseStep 43597025 = 32697769) B32697769
theorem B1196527 : Blo 1060614 1196527 := bstep (se 1 (by rfl) ⟨897395, by rfl⟩ : syracuseStep 1196527 = 1794791) B1794791
theorem B9094639 : Blo 1060614 9094639 := bstep (se 1 (by rfl) ⟨6820979, by rfl⟩ : syracuseStep 9094639 = 13641959) B13641959
theorem B8079263 : Blo 1060614 8079263 := bstep (se 1 (by rfl) ⟨6059447, by rfl⟩ : syracuseStep 8079263 = 12118895) B12118895
theorem B1591295 : Blo 1060614 1591295 := bstep (se 1 (by rfl) ⟨1193471, by rfl⟩ : syracuseStep 1591295 = 2386943) B2386943
theorem B1591337 : Blo 1060614 1591337 := bstep (se 2 (by rfl) ⟨596751, by rfl⟩ : syracuseStep 1591337 = 1193503) B1193503
theorem B1591775 : Blo 1060614 1591775 := bstep (se 1 (by rfl) ⟨1193831, by rfl⟩ : syracuseStep 1591775 = 2387663) B2387663
theorem B7654459 : Blo 1060614 7654459 := bstep (se 1 (by rfl) ⟨5740844, by rfl⟩ : syracuseStep 7654459 = 11481689) B11481689
theorem B3592511 : Blo 1060614 3592511 := bstep (se 1 (by rfl) ⟨2694383, by rfl⟩ : syracuseStep 3592511 = 5388767) B5388767
theorem B6903967 : Blo 1060614 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B1792327 : Blo 1060614 1792327 := bstep (se 1 (by rfl) ⟨1344245, by rfl⟩ : syracuseStep 1792327 = 2688491) B2688491
theorem B1793279 : Blo 1060614 1793279 := bstep (se 1 (by rfl) ⟨1344959, by rfl⟩ : syracuseStep 1793279 = 2689919) B2689919
theorem B9069353 : Blo 1060614 9069353 := bstep (se 2 (by rfl) ⟨3401007, by rfl⟩ : syracuseStep 9069353 = 6802015) B6802015
theorem B1795007 : Blo 1060614 1795007 := bstep (se 1 (by rfl) ⟨1346255, by rfl⟩ : syracuseStep 1795007 = 2692511) B2692511
theorem B59041619 : Blo 1060614 59041619 := bstep (se 1 (by rfl) ⟨44281214, by rfl⟩ : syracuseStep 59041619 = 88562429) B88562429
theorem B104789375 : Blo 1060614 104789375 := bstep (se 1 (by rfl) ⟨78592031, by rfl⟩ : syracuseStep 104789375 = 157184063) B157184063
theorem B12126185 : Blo 1060614 12126185 := bstep (se 2 (by rfl) ⟨4547319, by rfl⟩ : syracuseStep 12126185 = 9094639) B9094639
theorem B2395007 : Blo 1060614 2395007 := bstep (se 1 (by rfl) ⟨1796255, by rfl⟩ : syracuseStep 2395007 = 3592511) B3592511
theorem B957093529 : Blo 1060614 957093529 := bstep (se 2 (by rfl) ⟨358910073, by rfl⟩ : syracuseStep 957093529 = 717820147) B717820147
theorem B39361079 : Blo 1060614 39361079 := bstep (se 1 (by rfl) ⟨29520809, by rfl⟩ : syracuseStep 39361079 = 59041619) B59041619
theorem B5381153 : Blo 1060614 5381153 := bstep (se 2 (by rfl) ⟨2017932, by rfl⟩ : syracuseStep 5381153 = 4035865) B4035865
theorem B5386175 : Blo 1060614 5386175 := bstep (se 1 (by rfl) ⟨4039631, by rfl⟩ : syracuseStep 5386175 = 8079263) B8079263
theorem B1060863 : Blo 1060614 1060863 := bstep (se 1 (by rfl) ⟨795647, by rfl⟩ : syracuseStep 1060863 = 1591295) B1591295
theorem B1060891 : Blo 1060614 1060891 := bstep (se 1 (by rfl) ⟨795668, by rfl⟩ : syracuseStep 1060891 = 1591337) B1591337
theorem B1061183 : Blo 1060614 1061183 := bstep (se 1 (by rfl) ⟨795887, by rfl⟩ : syracuseStep 1061183 = 1591775) B1591775
theorem B3584681 : Blo 1060614 3584681 := bstep (se 2 (by rfl) ⟨1344255, by rfl⟩ : syracuseStep 3584681 = 2688511) B2688511
theorem B10205945 : Blo 1060614 10205945 := bstep (se 2 (by rfl) ⟨3827229, by rfl⟩ : syracuseStep 10205945 = 7654459) B7654459
theorem B1195519 : Blo 1060614 1195519 := bstep (se 1 (by rfl) ⟨896639, by rfl⟩ : syracuseStep 1195519 = 1793279) B1793279
theorem B6046235 : Blo 1060614 6046235 := bstep (se 1 (by rfl) ⟨4534676, by rfl⟩ : syracuseStep 6046235 = 9069353) B9069353
theorem B1196671 : Blo 1060614 1196671 := bstep (se 1 (by rfl) ⟨897503, by rfl⟩ : syracuseStep 1196671 = 1795007) B1795007
theorem B22957145 : Blo 1060614 22957145 := bstep (se 2 (by rfl) ⟨8608929, by rfl⟩ : syracuseStep 22957145 = 17217859) B17217859
theorem B2019755 : Blo 1060614 2019755 := bstep (se 1 (by rfl) ⟨1514816, by rfl⟩ : syracuseStep 2019755 = 3029633) B3029633
theorem B6903235 : Blo 1060614 6903235 := bstep (se 1 (by rfl) ⟨5177426, by rfl⟩ : syracuseStep 6903235 = 10354853) B10354853
theorem B6051611 : Blo 1060614 6051611 := bstep (se 1 (by rfl) ⟨4538708, by rfl⟩ : syracuseStep 6051611 = 9077417) B9077417
theorem B1595369 : Blo 1060614 1595369 := bstep (se 2 (by rfl) ⟨598263, by rfl⟩ : syracuseStep 1595369 = 1196527) B1196527
theorem B1595447 : Blo 1060614 1595447 := bstep (se 1 (by rfl) ⟨1196585, by rfl⟩ : syracuseStep 1595447 = 2393171) B2393171
theorem B3234529 : Blo 1060614 3234529 := bstep (se 2 (by rfl) ⟨1212948, by rfl⟩ : syracuseStep 3234529 = 2425897) B2425897
theorem B6056167 : Blo 1060614 6056167 := bstep (se 1 (by rfl) ⟨4542125, by rfl⟩ : syracuseStep 6056167 = 9084251) B9084251
theorem B9205289 : Blo 1060614 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B2389769 : Blo 1060614 2389769 := bstep (se 2 (by rfl) ⟨896163, by rfl⟩ : syracuseStep 2389769 = 1792327) B1792327
theorem B13596443 : Blo 1060614 13596443 := bstep (se 1 (by rfl) ⟨10197332, by rfl⟩ : syracuseStep 13596443 = 20394665) B20394665
theorem B69859583 : Blo 1060614 69859583 := bstep (se 1 (by rfl) ⟨52394687, by rfl⟩ : syracuseStep 69859583 = 104789375) B104789375
theorem B29064683 : Blo 1060614 29064683 := bstep (se 1 (by rfl) ⟨21798512, by rfl⟩ : syracuseStep 29064683 = 43597025) B43597025
theorem B4030823 : Blo 1060614 4030823 := bstep (se 1 (by rfl) ⟨3023117, by rfl⟩ : syracuseStep 4030823 = 6046235) B6046235
theorem B15304763 : Blo 1060614 15304763 := bstep (se 1 (by rfl) ⟨11478572, by rfl⟩ : syracuseStep 15304763 = 22957145) B22957145
theorem B4034407 : Blo 1060614 4034407 := bstep (se 1 (by rfl) ⟨3025805, by rfl⟩ : syracuseStep 4034407 = 6051611) B6051611
theorem B1276124705 : Blo 1060614 1276124705 := bstep (se 2 (by rfl) ⟨478546764, by rfl⟩ : syracuseStep 1276124705 = 957093529) B957093529
theorem B6136859 : Blo 1060614 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B46573055 : Blo 1060614 46573055 := bstep (se 1 (by rfl) ⟨34929791, by rfl⟩ : syracuseStep 46573055 = 69859583) B69859583
theorem B19376455 : Blo 1060614 19376455 := bstep (se 1 (by rfl) ⟨14532341, by rfl⟩ : syracuseStep 19376455 = 29064683) B29064683
theorem B5386013 : Blo 1060614 5386013 := bstep (se 3 (by rfl) ⟨1009877, by rfl⟩ : syracuseStep 5386013 = 2019755) B2019755
theorem B8074889 : Blo 1060614 8074889 := bstep (se 2 (by rfl) ⟨3028083, by rfl⟩ : syracuseStep 8074889 = 6056167) B6056167
theorem B1063579 : Blo 1060614 1063579 := bstep (se 1 (by rfl) ⟨797684, by rfl⟩ : syracuseStep 1063579 = 1595369) B1595369
theorem B1063631 : Blo 1060614 1063631 := bstep (se 1 (by rfl) ⟨797723, by rfl⟩ : syracuseStep 1063631 = 1595447) B1595447
theorem B3587435 : Blo 1060614 3587435 := bstep (se 1 (by rfl) ⟨2690576, by rfl⟩ : syracuseStep 3587435 = 5381153) B5381153
theorem B3590783 : Blo 1060614 3590783 := bstep (se 1 (by rfl) ⟨2693087, by rfl⟩ : syracuseStep 3590783 = 5386175) B5386175
theorem B4312705 : Blo 1060614 4312705 := bstep (se 2 (by rfl) ⟨1617264, by rfl⟩ : syracuseStep 4312705 = 3234529) B3234529
theorem B1593179 : Blo 1060614 1593179 := bstep (se 1 (by rfl) ⟨1194884, by rfl⟩ : syracuseStep 1593179 = 2389769) B2389769
theorem B9064295 : Blo 1060614 9064295 := bstep (se 1 (by rfl) ⟨6798221, by rfl⟩ : syracuseStep 9064295 = 13596443) B13596443
theorem B6803963 : Blo 1060614 6803963 := bstep (se 1 (by rfl) ⟨5102972, by rfl⟩ : syracuseStep 6803963 = 10205945) B10205945
theorem B1594025 : Blo 1060614 1594025 := bstep (se 2 (by rfl) ⟨597759, by rfl⟩ : syracuseStep 1594025 = 1195519) B1195519
theorem B1595561 : Blo 1060614 1595561 := bstep (se 2 (by rfl) ⟨598335, by rfl⟩ : syracuseStep 1595561 = 1196671) B1196671
theorem B8084123 : Blo 1060614 8084123 := bstep (se 1 (by rfl) ⟨6063092, by rfl⟩ : syracuseStep 8084123 = 12126185) B12126185
theorem B1596671 : Blo 1060614 1596671 := bstep (se 1 (by rfl) ⟨1197503, by rfl⟩ : syracuseStep 1596671 = 2395007) B2395007
theorem B26240719 : Blo 1060614 26240719 := bstep (se 1 (by rfl) ⟨19680539, by rfl⟩ : syracuseStep 26240719 = 39361079) B39361079
theorem B9204313 : Blo 1060614 9204313 := bstep (se 2 (by rfl) ⟨3451617, by rfl⟩ : syracuseStep 9204313 = 6903235) B6903235
theorem B2389787 : Blo 1060614 2389787 := bstep (se 1 (by rfl) ⟨1792340, by rfl⟩ : syracuseStep 2389787 = 3584681) B3584681
theorem B2687215 : Blo 1060614 2687215 := bstep (se 1 (by rfl) ⟨2015411, by rfl⟩ : syracuseStep 2687215 = 4030823) B4030823
theorem B2393855 : Blo 1060614 2393855 := bstep (se 1 (by rfl) ⟨1795391, by rfl⟩ : syracuseStep 2393855 = 3590783) B3590783
theorem B5379209 : Blo 1060614 5379209 := bstep (se 2 (by rfl) ⟨2017203, by rfl⟩ : syracuseStep 5379209 = 4034407) B4034407
theorem B5383259 : Blo 1060614 5383259 := bstep (se 1 (by rfl) ⟨4037444, by rfl⟩ : syracuseStep 5383259 = 8074889) B8074889
theorem B10203175 : Blo 1060614 10203175 := bstep (se 1 (by rfl) ⟨7652381, by rfl⟩ : syracuseStep 10203175 = 15304763) B15304763
theorem B1062119 : Blo 1060614 1062119 := bstep (se 1 (by rfl) ⟨796589, by rfl⟩ : syracuseStep 1062119 = 1593179) B1593179
theorem B6042863 : Blo 1060614 6042863 := bstep (se 1 (by rfl) ⟨4532147, by rfl⟩ : syracuseStep 6042863 = 9064295) B9064295
theorem B4535975 : Blo 1060614 4535975 := bstep (se 1 (by rfl) ⟨3401981, by rfl⟩ : syracuseStep 4535975 = 6803963) B6803963
theorem B25835273 : Blo 1060614 25835273 := bstep (se 2 (by rfl) ⟨9688227, by rfl⟩ : syracuseStep 25835273 = 19376455) B19376455
theorem B1062683 : Blo 1060614 1062683 := bstep (se 1 (by rfl) ⟨797012, by rfl⟩ : syracuseStep 1062683 = 1594025) B1594025
theorem B1063707 : Blo 1060614 1063707 := bstep (se 1 (by rfl) ⟨797780, by rfl⟩ : syracuseStep 1063707 = 1595561) B1595561
theorem B5389415 : Blo 1060614 5389415 := bstep (se 1 (by rfl) ⟨4042061, by rfl⟩ : syracuseStep 5389415 = 8084123) B8084123
theorem B1064447 : Blo 1060614 1064447 := bstep (se 1 (by rfl) ⟨798335, by rfl⟩ : syracuseStep 1064447 = 1596671) B1596671
theorem B5750273 : Blo 1060614 5750273 := bstep (se 2 (by rfl) ⟨2156352, by rfl⟩ : syracuseStep 5750273 = 4312705) B4312705
theorem B12272417 : Blo 1060614 12272417 := bstep (se 2 (by rfl) ⟨4602156, by rfl⟩ : syracuseStep 12272417 = 9204313) B9204313
theorem B31048703 : Blo 1060614 31048703 := bstep (se 1 (by rfl) ⟨23286527, by rfl⟩ : syracuseStep 31048703 = 46573055) B46573055
theorem B3590675 : Blo 1060614 3590675 := bstep (se 1 (by rfl) ⟨2693006, by rfl⟩ : syracuseStep 3590675 = 5386013) B5386013
theorem B1593191 : Blo 1060614 1593191 := bstep (se 1 (by rfl) ⟨1194893, by rfl⟩ : syracuseStep 1593191 = 2389787) B2389787
theorem B34987625 : Blo 1060614 34987625 := bstep (se 2 (by rfl) ⟨13120359, by rfl⟩ : syracuseStep 34987625 = 26240719) B26240719
theorem B850749803 : Blo 1060614 850749803 := bstep (se 1 (by rfl) ⟨638062352, by rfl⟩ : syracuseStep 850749803 = 1276124705) B1276124705
theorem B4091239 : Blo 1060614 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B2391623 : Blo 1060614 2391623 := bstep (se 1 (by rfl) ⟨1793717, by rfl⟩ : syracuseStep 2391623 = 3587435) B3587435
theorem B2393783 : Blo 1060614 2393783 := bstep (se 1 (by rfl) ⟨1795337, by rfl⟩ : syracuseStep 2393783 = 3590675) B3590675
theorem B13604233 : Blo 1060614 13604233 := bstep (se 2 (by rfl) ⟨5101587, by rfl⟩ : syracuseStep 13604233 = 10203175) B10203175
theorem B3023983 : Blo 1060614 3023983 := bstep (se 1 (by rfl) ⟨2267987, by rfl⟩ : syracuseStep 3023983 = 4535975) B4535975
theorem B3582953 : Blo 1060614 3582953 := bstep (se 2 (by rfl) ⟨1343607, by rfl⟩ : syracuseStep 3582953 = 2687215) B2687215
theorem B1062127 : Blo 1060614 1062127 := bstep (se 1 (by rfl) ⟨796595, by rfl⟩ : syracuseStep 1062127 = 1593191) B1593191
theorem B3586139 : Blo 1060614 3586139 := bstep (se 1 (by rfl) ⟨2689604, by rfl⟩ : syracuseStep 3586139 = 5379209) B5379209
theorem B3588839 : Blo 1060614 3588839 := bstep (se 1 (by rfl) ⟨2691629, by rfl⟩ : syracuseStep 3588839 = 5383259) B5383259
theorem B567166535 : Blo 1060614 567166535 := bstep (se 1 (by rfl) ⟨425374901, by rfl⟩ : syracuseStep 567166535 = 850749803) B850749803
theorem B17223515 : Blo 1060614 17223515 := bstep (se 1 (by rfl) ⟨12917636, by rfl⟩ : syracuseStep 17223515 = 25835273) B25835273
theorem B3592943 : Blo 1060614 3592943 := bstep (se 1 (by rfl) ⟨2694707, by rfl⟩ : syracuseStep 3592943 = 5389415) B5389415
theorem B1594415 : Blo 1060614 1594415 := bstep (se 1 (by rfl) ⟨1195811, by rfl⟩ : syracuseStep 1594415 = 2391623) B2391623
theorem B8181611 : Blo 1060614 8181611 := bstep (se 1 (by rfl) ⟨6136208, by rfl⟩ : syracuseStep 8181611 = 12272417) B12272417
theorem B20699135 : Blo 1060614 20699135 := bstep (se 1 (by rfl) ⟨15524351, by rfl⟩ : syracuseStep 20699135 = 31048703) B31048703
theorem B1595903 : Blo 1060614 1595903 := bstep (se 1 (by rfl) ⟨1196927, by rfl⟩ : syracuseStep 1595903 = 2393855) B2393855
theorem B23325083 : Blo 1060614 23325083 := bstep (se 1 (by rfl) ⟨17493812, by rfl⟩ : syracuseStep 23325083 = 34987625) B34987625
theorem B21819941 : Blo 1060614 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B4028575 : Blo 1060614 4028575 := bstep (se 1 (by rfl) ⟨3021431, by rfl⟩ : syracuseStep 4028575 = 6042863) B6042863
theorem B3833515 : Blo 1060614 3833515 := bstep (se 1 (by rfl) ⟨2875136, by rfl⟩ : syracuseStep 3833515 = 5750273) B5750273
theorem B2392559 : Blo 1060614 2392559 := bstep (se 1 (by rfl) ⟨1794419, by rfl⟩ : syracuseStep 2392559 = 3588839) B3588839
theorem B378111023 : Blo 1060614 378111023 := bstep (se 1 (by rfl) ⟨283583267, by rfl⟩ : syracuseStep 378111023 = 567166535) B567166535
theorem B4031977 : Blo 1060614 4031977 := bstep (se 2 (by rfl) ⟨1511991, by rfl⟩ : syracuseStep 4031977 = 3023983) B3023983
theorem B2395295 : Blo 1060614 2395295 := bstep (se 1 (by rfl) ⟨1796471, by rfl⟩ : syracuseStep 2395295 = 3592943) B3592943
theorem B13799423 : Blo 1060614 13799423 := bstep (se 1 (by rfl) ⟨10349567, by rfl⟩ : syracuseStep 13799423 = 20699135) B20699135
theorem B11482343 : Blo 1060614 11482343 := bstep (se 1 (by rfl) ⟨8611757, by rfl⟩ : syracuseStep 11482343 = 17223515) B17223515
theorem B1062943 : Blo 1060614 1062943 := bstep (se 1 (by rfl) ⟨797207, by rfl⟩ : syracuseStep 1062943 = 1594415) B1594415
theorem B5454407 : Blo 1060614 5454407 := bstep (se 1 (by rfl) ⟨4090805, by rfl⟩ : syracuseStep 5454407 = 8181611) B8181611
theorem B1063935 : Blo 1060614 1063935 := bstep (se 1 (by rfl) ⟨797951, by rfl⟩ : syracuseStep 1063935 = 1595903) B1595903
theorem B15550055 : Blo 1060614 15550055 := bstep (se 1 (by rfl) ⟨11662541, by rfl⟩ : syracuseStep 15550055 = 23325083) B23325083
theorem B18138977 : Blo 1060614 18138977 := bstep (se 2 (by rfl) ⟨6802116, by rfl⟩ : syracuseStep 18138977 = 13604233) B13604233
theorem B1595855 : Blo 1060614 1595855 := bstep (se 1 (by rfl) ⟨1196891, by rfl⟩ : syracuseStep 1595855 = 2393783) B2393783
theorem B2388635 : Blo 1060614 2388635 := bstep (se 1 (by rfl) ⟨1791476, by rfl⟩ : syracuseStep 2388635 = 3582953) B3582953
theorem B5371433 : Blo 1060614 5371433 := bstep (se 2 (by rfl) ⟨2014287, by rfl⟩ : syracuseStep 5371433 = 4028575) B4028575
theorem B14546627 : Blo 1060614 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B2390759 : Blo 1060614 2390759 := bstep (se 1 (by rfl) ⟨1793069, by rfl⟩ : syracuseStep 2390759 = 3586139) B3586139
theorem B5111353 : Blo 1060614 5111353 := bstep (se 2 (by rfl) ⟨1916757, by rfl⟩ : syracuseStep 5111353 = 3833515) B3833515
theorem B12092651 : Blo 1060614 12092651 := bstep (se 1 (by rfl) ⟨9069488, by rfl⟩ : syracuseStep 12092651 = 18138977) B18138977
theorem B5375969 : Blo 1060614 5375969 := bstep (se 2 (by rfl) ⟨2015988, by rfl⟩ : syracuseStep 5375969 = 4031977) B4031977
theorem B3580955 : Blo 1060614 3580955 := bstep (se 1 (by rfl) ⟨2685716, by rfl⟩ : syracuseStep 3580955 = 5371433) B5371433
theorem B10366703 : Blo 1060614 10366703 := bstep (se 1 (by rfl) ⟨7775027, by rfl⟩ : syracuseStep 10366703 = 15550055) B15550055
theorem B1063903 : Blo 1060614 1063903 := bstep (se 1 (by rfl) ⟨797927, by rfl⟩ : syracuseStep 1063903 = 1595855) B1595855
theorem B1592423 : Blo 1060614 1592423 := bstep (se 1 (by rfl) ⟨1194317, by rfl⟩ : syracuseStep 1592423 = 2388635) B2388635
theorem B7654895 : Blo 1060614 7654895 := bstep (se 1 (by rfl) ⟨5741171, by rfl⟩ : syracuseStep 7654895 = 11482343) B11482343
theorem B1593839 : Blo 1060614 1593839 := bstep (se 1 (by rfl) ⟨1195379, by rfl⟩ : syracuseStep 1593839 = 2390759) B2390759
theorem B1595039 : Blo 1060614 1595039 := bstep (se 1 (by rfl) ⟨1196279, by rfl⟩ : syracuseStep 1595039 = 2392559) B2392559
theorem B252074015 : Blo 1060614 252074015 := bstep (se 1 (by rfl) ⟨189055511, by rfl⟩ : syracuseStep 252074015 = 378111023) B378111023
theorem B1596863 : Blo 1060614 1596863 := bstep (se 1 (by rfl) ⟨1197647, by rfl⟩ : syracuseStep 1596863 = 2395295) B2395295
theorem B9199615 : Blo 1060614 9199615 := bstep (se 1 (by rfl) ⟨6899711, by rfl⟩ : syracuseStep 9199615 = 13799423) B13799423
theorem B9697751 : Blo 1060614 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B3636271 : Blo 1060614 3636271 := bstep (se 1 (by rfl) ⟨2727203, by rfl⟩ : syracuseStep 3636271 = 5454407) B5454407
theorem B6815137 : Blo 1060614 6815137 := bstep (se 2 (by rfl) ⟨2555676, by rfl⟩ : syracuseStep 6815137 = 5111353) B5111353
theorem B8061767 : Blo 1060614 8061767 := bstep (se 1 (by rfl) ⟨6046325, by rfl⟩ : syracuseStep 8061767 = 12092651) B12092651
theorem B6465167 : Blo 1060614 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B9086849 : Blo 1060614 9086849 := bstep (se 2 (by rfl) ⟨3407568, by rfl⟩ : syracuseStep 9086849 = 6815137) B6815137
theorem B12266153 : Blo 1060614 12266153 := bstep (se 2 (by rfl) ⟨4599807, by rfl⟩ : syracuseStep 12266153 = 9199615) B9199615
theorem B3583979 : Blo 1060614 3583979 := bstep (se 1 (by rfl) ⟨2687984, by rfl⟩ : syracuseStep 3583979 = 5375969) B5375969
theorem B1061615 : Blo 1060614 1061615 := bstep (se 1 (by rfl) ⟨796211, by rfl⟩ : syracuseStep 1061615 = 1592423) B1592423
theorem B1062559 : Blo 1060614 1062559 := bstep (se 1 (by rfl) ⟨796919, by rfl⟩ : syracuseStep 1062559 = 1593839) B1593839
theorem B1063359 : Blo 1060614 1063359 := bstep (se 1 (by rfl) ⟨797519, by rfl⟩ : syracuseStep 1063359 = 1595039) B1595039
theorem B168049343 : Blo 1060614 168049343 := bstep (se 1 (by rfl) ⟨126037007, by rfl⟩ : syracuseStep 168049343 = 252074015) B252074015
theorem B1064575 : Blo 1060614 1064575 := bstep (se 1 (by rfl) ⟨798431, by rfl⟩ : syracuseStep 1064575 = 1596863) B1596863
theorem B5103263 : Blo 1060614 5103263 := bstep (se 1 (by rfl) ⟨3827447, by rfl⟩ : syracuseStep 5103263 = 7654895) B7654895
theorem B19393445 : Blo 1060614 19393445 := bstep (se 4 (by rfl) ⟨1818135, by rfl⟩ : syracuseStep 19393445 = 3636271) B3636271
theorem B2387303 : Blo 1060614 2387303 := bstep (se 1 (by rfl) ⟨1790477, by rfl⟩ : syracuseStep 2387303 = 3580955) B3580955
theorem B6911135 : Blo 1060614 6911135 := bstep (se 1 (by rfl) ⟨5183351, by rfl⟩ : syracuseStep 6911135 = 10366703) B10366703
theorem B5374511 : Blo 1060614 5374511 := bstep (se 1 (by rfl) ⟨4030883, by rfl⟩ : syracuseStep 5374511 = 8061767) B8061767
theorem B51715853 : Blo 1060614 51715853 := bstep (se 3 (by rfl) ⟨9696722, by rfl⟩ : syracuseStep 51715853 = 19393445) B19393445
theorem B4310111 : Blo 1060614 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B8177435 : Blo 1060614 8177435 := bstep (se 1 (by rfl) ⟨6133076, by rfl⟩ : syracuseStep 8177435 = 12266153) B12266153
theorem B1591535 : Blo 1060614 1591535 := bstep (se 1 (by rfl) ⟨1193651, by rfl⟩ : syracuseStep 1591535 = 2387303) B2387303
theorem B4607423 : Blo 1060614 4607423 := bstep (se 1 (by rfl) ⟨3455567, by rfl⟩ : syracuseStep 4607423 = 6911135) B6911135
theorem B3402175 : Blo 1060614 3402175 := bstep (se 1 (by rfl) ⟨2551631, by rfl⟩ : syracuseStep 3402175 = 5103263) B5103263
theorem B6057899 : Blo 1060614 6057899 := bstep (se 1 (by rfl) ⟨4543424, by rfl⟩ : syracuseStep 6057899 = 9086849) B9086849
theorem B2389319 : Blo 1060614 2389319 := bstep (se 1 (by rfl) ⟨1791989, by rfl⟩ : syracuseStep 2389319 = 3583979) B3583979
theorem B112032895 : Blo 1060614 112032895 := bstep (se 1 (by rfl) ⟨84024671, by rfl⟩ : syracuseStep 112032895 = 168049343) B168049343
theorem B34477235 : Blo 1060614 34477235 := bstep (se 1 (by rfl) ⟨25857926, by rfl⟩ : syracuseStep 34477235 = 51715853) B51715853
theorem B4038599 : Blo 1060614 4038599 := bstep (se 1 (by rfl) ⟨3028949, by rfl⟩ : syracuseStep 4038599 = 6057899) B6057899
theorem B3583007 : Blo 1060614 3583007 := bstep (se 1 (by rfl) ⟨2687255, by rfl⟩ : syracuseStep 3583007 = 5374511) B5374511
theorem B5451623 : Blo 1060614 5451623 := bstep (se 1 (by rfl) ⟨4088717, by rfl⟩ : syracuseStep 5451623 = 8177435) B8177435
theorem B1061023 : Blo 1060614 1061023 := bstep (se 1 (by rfl) ⟨795767, by rfl⟩ : syracuseStep 1061023 = 1591535) B1591535
theorem B4536233 : Blo 1060614 4536233 := bstep (se 2 (by rfl) ⟨1701087, by rfl⟩ : syracuseStep 4536233 = 3402175) B3402175
theorem B1592879 : Blo 1060614 1592879 := bstep (se 1 (by rfl) ⟨1194659, by rfl⟩ : syracuseStep 1592879 = 2389319) B2389319
theorem B149377193 : Blo 1060614 149377193 := bstep (se 2 (by rfl) ⟨56016447, by rfl⟩ : syracuseStep 149377193 = 112032895) B112032895
theorem B2873407 : Blo 1060614 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B3071615 : Blo 1060614 3071615 := bstep (se 1 (by rfl) ⟨2303711, by rfl⟩ : syracuseStep 3071615 = 4607423) B4607423
theorem B99584795 : Blo 1060614 99584795 := bstep (se 1 (by rfl) ⟨74688596, by rfl⟩ : syracuseStep 99584795 = 149377193) B149377193
theorem B2692399 : Blo 1060614 2692399 := bstep (se 1 (by rfl) ⟨2019299, by rfl⟩ : syracuseStep 2692399 = 4038599) B4038599
theorem B3024155 : Blo 1060614 3024155 := bstep (se 1 (by rfl) ⟨2268116, by rfl⟩ : syracuseStep 3024155 = 4536233) B4536233
theorem B1061919 : Blo 1060614 1061919 := bstep (se 1 (by rfl) ⟨796439, by rfl⟩ : syracuseStep 1061919 = 1592879) B1592879
theorem B22984823 : Blo 1060614 22984823 := bstep (se 1 (by rfl) ⟨17238617, by rfl⟩ : syracuseStep 22984823 = 34477235) B34477235
theorem B2388671 : Blo 1060614 2388671 := bstep (se 1 (by rfl) ⟨1791503, by rfl⟩ : syracuseStep 2388671 = 3583007) B3583007
theorem B3634415 : Blo 1060614 3634415 := bstep (se 1 (by rfl) ⟨2725811, by rfl⟩ : syracuseStep 3634415 = 5451623) B5451623
theorem B3831209 : Blo 1060614 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B8190973 : Blo 1060614 8190973 := bstep (se 3 (by rfl) ⟨1535807, by rfl⟩ : syracuseStep 8190973 = 3071615) B3071615
theorem B66389863 : Blo 1060614 66389863 := bstep (se 1 (by rfl) ⟨49792397, by rfl⟩ : syracuseStep 66389863 = 99584795) B99584795
theorem B43685189 : Blo 1060614 43685189 := bstep (se 4 (by rfl) ⟨4095486, by rfl⟩ : syracuseStep 43685189 = 8190973) B8190973
theorem B61292861 : Blo 1060614 61292861 := bstep (se 3 (by rfl) ⟨11492411, by rfl⟩ : syracuseStep 61292861 = 22984823) B22984823
theorem B2016103 : Blo 1060614 2016103 := bstep (se 1 (by rfl) ⟨1512077, by rfl⟩ : syracuseStep 2016103 = 3024155) B3024155
theorem B3589865 : Blo 1060614 3589865 := bstep (se 2 (by rfl) ⟨1346199, by rfl⟩ : syracuseStep 3589865 = 2692399) B2692399
theorem B1592447 : Blo 1060614 1592447 := bstep (se 1 (by rfl) ⟨1194335, by rfl⟩ : syracuseStep 1592447 = 2388671) B2388671
theorem B2422943 : Blo 1060614 2422943 := bstep (se 1 (by rfl) ⟨1817207, by rfl⟩ : syracuseStep 2422943 = 3634415) B3634415
theorem B2554139 : Blo 1060614 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B40861907 : Blo 1060614 40861907 := bstep (se 1 (by rfl) ⟨30646430, by rfl⟩ : syracuseStep 40861907 = 61292861) B61292861
theorem B2688137 : Blo 1060614 2688137 := bstep (se 2 (by rfl) ⟨1008051, by rfl⟩ : syracuseStep 2688137 = 2016103) B2016103
theorem B2393243 : Blo 1060614 2393243 := bstep (se 1 (by rfl) ⟨1794932, by rfl⟩ : syracuseStep 2393243 = 3589865) B3589865
theorem B1615295 : Blo 1060614 1615295 := bstep (se 1 (by rfl) ⟨1211471, by rfl⟩ : syracuseStep 1615295 = 2422943) B2422943
theorem B1061631 : Blo 1060614 1061631 := bstep (se 1 (by rfl) ⟨796223, by rfl⟩ : syracuseStep 1061631 = 1592447) B1592447
theorem B88519817 : Blo 1060614 88519817 := bstep (se 2 (by rfl) ⟨33194931, by rfl⟩ : syracuseStep 88519817 = 66389863) B66389863
theorem B29123459 : Blo 1060614 29123459 := bstep (se 1 (by rfl) ⟨21842594, by rfl⟩ : syracuseStep 29123459 = 43685189) B43685189
theorem B6811037 : Blo 1060614 6811037 := bstep (se 3 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 6811037 = 2554139) B2554139
theorem B27241271 : Blo 1060614 27241271 := bstep (se 1 (by rfl) ⟨20430953, by rfl⟩ : syracuseStep 27241271 = 40861907) B40861907
theorem B19415639 : Blo 1060614 19415639 := bstep (se 1 (by rfl) ⟨14561729, by rfl⟩ : syracuseStep 19415639 = 29123459) B29123459
theorem B4540691 : Blo 1060614 4540691 := bstep (se 1 (by rfl) ⟨3405518, by rfl⟩ : syracuseStep 4540691 = 6811037) B6811037
theorem B1792091 : Blo 1060614 1792091 := bstep (se 1 (by rfl) ⟨1344068, by rfl⟩ : syracuseStep 1792091 = 2688137) B2688137
theorem B1595495 : Blo 1060614 1595495 := bstep (se 1 (by rfl) ⟨1196621, by rfl⟩ : syracuseStep 1595495 = 2393243) B2393243
theorem B1076863 : Blo 1060614 1076863 := bstep (se 1 (by rfl) ⟨807647, by rfl⟩ : syracuseStep 1076863 = 1615295) B1615295
theorem B59013211 : Blo 1060614 59013211 := bstep (se 1 (by rfl) ⟨44259908, by rfl⟩ : syracuseStep 59013211 = 88519817) B88519817
theorem B12943759 : Blo 1060614 12943759 := bstep (se 1 (by rfl) ⟨9707819, by rfl⟩ : syracuseStep 12943759 = 19415639) B19415639
theorem B18160847 : Blo 1060614 18160847 := bstep (se 1 (by rfl) ⟨13620635, by rfl⟩ : syracuseStep 18160847 = 27241271) B27241271
theorem B78684281 : Blo 1060614 78684281 := bstep (se 2 (by rfl) ⟨29506605, by rfl⟩ : syracuseStep 78684281 = 59013211) B59013211
theorem B3027127 : Blo 1060614 3027127 := bstep (se 1 (by rfl) ⟨2270345, by rfl⟩ : syracuseStep 3027127 = 4540691) B4540691
theorem B1194727 : Blo 1060614 1194727 := bstep (se 1 (by rfl) ⟨896045, by rfl⟩ : syracuseStep 1194727 = 1792091) B1792091
theorem B1063663 : Blo 1060614 1063663 := bstep (se 1 (by rfl) ⟨797747, by rfl⟩ : syracuseStep 1063663 = 1595495) B1595495
theorem B1435817 : Blo 1060614 1435817 := bstep (se 2 (by rfl) ⟨538431, by rfl⟩ : syracuseStep 1435817 = 1076863) B1076863
theorem B4036169 : Blo 1060614 4036169 := bstep (se 2 (by rfl) ⟨1513563, by rfl⟩ : syracuseStep 4036169 = 3027127) B3027127
theorem B12107231 : Blo 1060614 12107231 := bstep (se 1 (by rfl) ⟨9080423, by rfl⟩ : syracuseStep 12107231 = 18160847) B18160847
theorem B1592969 : Blo 1060614 1592969 := bstep (se 2 (by rfl) ⟨597363, by rfl⟩ : syracuseStep 1592969 = 1194727) B1194727
theorem B17258345 : Blo 1060614 17258345 := bstep (se 2 (by rfl) ⟨6471879, by rfl⟩ : syracuseStep 17258345 = 12943759) B12943759
theorem B52456187 : Blo 1060614 52456187 := bstep (se 1 (by rfl) ⟨39342140, by rfl⟩ : syracuseStep 52456187 = 78684281) B78684281
theorem B3828845 : Blo 1060614 3828845 := bstep (se 3 (by rfl) ⟨717908, by rfl⟩ : syracuseStep 3828845 = 1435817) B1435817
theorem B2690779 : Blo 1060614 2690779 := bstep (se 1 (by rfl) ⟨2018084, by rfl⟩ : syracuseStep 2690779 = 4036169) B4036169
theorem B11505563 : Blo 1060614 11505563 := bstep (se 1 (by rfl) ⟨8629172, by rfl⟩ : syracuseStep 11505563 = 17258345) B17258345
theorem B34970791 : Blo 1060614 34970791 := bstep (se 1 (by rfl) ⟨26228093, by rfl⟩ : syracuseStep 34970791 = 52456187) B52456187
theorem B8071487 : Blo 1060614 8071487 := bstep (se 1 (by rfl) ⟨6053615, by rfl⟩ : syracuseStep 8071487 = 12107231) B12107231
theorem B1061979 : Blo 1060614 1061979 := bstep (se 1 (by rfl) ⟨796484, by rfl⟩ : syracuseStep 1061979 = 1592969) B1592969
theorem B2552563 : Blo 1060614 2552563 := bstep (se 1 (by rfl) ⟨1914422, by rfl⟩ : syracuseStep 2552563 = 3828845) B3828845
theorem B7670375 : Blo 1060614 7670375 := bstep (se 1 (by rfl) ⟨5752781, by rfl⟩ : syracuseStep 7670375 = 11505563) B11505563
theorem B5380991 : Blo 1060614 5380991 := bstep (se 1 (by rfl) ⟨4035743, by rfl⟩ : syracuseStep 5380991 = 8071487) B8071487
theorem B3587705 : Blo 1060614 3587705 := bstep (se 2 (by rfl) ⟨1345389, by rfl⟩ : syracuseStep 3587705 = 2690779) B2690779
theorem B3403417 : Blo 1060614 3403417 := bstep (se 2 (by rfl) ⟨1276281, by rfl⟩ : syracuseStep 3403417 = 2552563) B2552563
theorem B46627721 : Blo 1060614 46627721 := bstep (se 2 (by rfl) ⟨17485395, by rfl⟩ : syracuseStep 46627721 = 34970791) B34970791
theorem B5113583 : Blo 1060614 5113583 := bstep (se 1 (by rfl) ⟨3835187, by rfl⟩ : syracuseStep 5113583 = 7670375) B7670375
theorem B3587327 : Blo 1060614 3587327 := bstep (se 1 (by rfl) ⟨2690495, by rfl⟩ : syracuseStep 3587327 = 5380991) B5380991
theorem B4537889 : Blo 1060614 4537889 := bstep (se 2 (by rfl) ⟨1701708, by rfl⟩ : syracuseStep 4537889 = 3403417) B3403417
theorem B31085147 : Blo 1060614 31085147 := bstep (se 1 (by rfl) ⟨23313860, by rfl⟩ : syracuseStep 31085147 = 46627721) B46627721
theorem B2391803 : Blo 1060614 2391803 := bstep (se 1 (by rfl) ⟨1793852, by rfl⟩ : syracuseStep 2391803 = 3587705) B3587705
theorem B3409055 : Blo 1060614 3409055 := bstep (se 1 (by rfl) ⟨2556791, by rfl⟩ : syracuseStep 3409055 = 5113583) B5113583
theorem B3025259 : Blo 1060614 3025259 := bstep (se 1 (by rfl) ⟨2268944, by rfl⟩ : syracuseStep 3025259 = 4537889) B4537889
theorem B1594535 : Blo 1060614 1594535 := bstep (se 1 (by rfl) ⟨1195901, by rfl⟩ : syracuseStep 1594535 = 2391803) B2391803
theorem B82893725 : Blo 1060614 82893725 := bstep (se 3 (by rfl) ⟨15542573, by rfl⟩ : syracuseStep 82893725 = 31085147) B31085147
theorem B2391551 : Blo 1060614 2391551 := bstep (se 1 (by rfl) ⟨1793663, by rfl⟩ : syracuseStep 2391551 = 3587327) B3587327
theorem B2272703 : Blo 1060614 2272703 := bstep (se 1 (by rfl) ⟨1704527, by rfl⟩ : syracuseStep 2272703 = 3409055) B3409055
theorem B1063023 : Blo 1060614 1063023 := bstep (se 1 (by rfl) ⟨797267, by rfl⟩ : syracuseStep 1063023 = 1594535) B1594535
theorem B55262483 : Blo 1060614 55262483 := bstep (se 1 (by rfl) ⟨41446862, by rfl⟩ : syracuseStep 55262483 = 82893725) B82893725
theorem B2016839 : Blo 1060614 2016839 := bstep (se 1 (by rfl) ⟨1512629, by rfl⟩ : syracuseStep 2016839 = 3025259) B3025259
theorem B1594367 : Blo 1060614 1594367 := bstep (se 1 (by rfl) ⟨1195775, by rfl⟩ : syracuseStep 1594367 = 2391551) B2391551
theorem B5378237 : Blo 1060614 5378237 := bstep (se 3 (by rfl) ⟨1008419, by rfl⟩ : syracuseStep 5378237 = 2016839) B2016839
theorem B36841655 : Blo 1060614 36841655 := bstep (se 1 (by rfl) ⟨27631241, by rfl⟩ : syracuseStep 36841655 = 55262483) B55262483
theorem B1062911 : Blo 1060614 1062911 := bstep (se 1 (by rfl) ⟨797183, by rfl⟩ : syracuseStep 1062911 = 1594367) B1594367
theorem B6060541 : Blo 1060614 6060541 := bstep (se 3 (by rfl) ⟨1136351, by rfl⟩ : syracuseStep 6060541 = 2272703) B2272703
theorem B3585491 : Blo 1060614 3585491 := bstep (se 1 (by rfl) ⟨2689118, by rfl⟩ : syracuseStep 3585491 = 5378237) B5378237
theorem B24561103 : Blo 1060614 24561103 := bstep (se 1 (by rfl) ⟨18420827, by rfl⟩ : syracuseStep 24561103 = 36841655) B36841655
theorem B8080721 : Blo 1060614 8080721 := bstep (se 2 (by rfl) ⟨3030270, by rfl⟩ : syracuseStep 8080721 = 6060541) B6060541
theorem B32748137 : Blo 1060614 32748137 := bstep (se 2 (by rfl) ⟨12280551, by rfl⟩ : syracuseStep 32748137 = 24561103) B24561103
theorem B5387147 : Blo 1060614 5387147 := bstep (se 1 (by rfl) ⟨4040360, by rfl⟩ : syracuseStep 5387147 = 8080721) B8080721
theorem B2390327 : Blo 1060614 2390327 := bstep (se 1 (by rfl) ⟨1792745, by rfl⟩ : syracuseStep 2390327 = 3585491) B3585491
theorem B21832091 : Blo 1060614 21832091 := bstep (se 1 (by rfl) ⟨16374068, by rfl⟩ : syracuseStep 21832091 = 32748137) B32748137
theorem B3591431 : Blo 1060614 3591431 := bstep (se 1 (by rfl) ⟨2693573, by rfl⟩ : syracuseStep 3591431 = 5387147) B5387147
theorem B1593551 : Blo 1060614 1593551 := bstep (se 1 (by rfl) ⟨1195163, by rfl⟩ : syracuseStep 1593551 = 2390327) B2390327
theorem B2394287 : Blo 1060614 2394287 := bstep (se 1 (by rfl) ⟨1795715, by rfl⟩ : syracuseStep 2394287 = 3591431) B3591431
theorem B14554727 : Blo 1060614 14554727 := bstep (se 1 (by rfl) ⟨10916045, by rfl⟩ : syracuseStep 14554727 = 21832091) B21832091
theorem B1062367 : Blo 1060614 1062367 := bstep (se 1 (by rfl) ⟨796775, by rfl⟩ : syracuseStep 1062367 = 1593551) B1593551
theorem B9703151 : Blo 1060614 9703151 := bstep (se 1 (by rfl) ⟨7277363, by rfl⟩ : syracuseStep 9703151 = 14554727) B14554727
theorem B1596191 : Blo 1060614 1596191 := bstep (se 1 (by rfl) ⟨1197143, by rfl⟩ : syracuseStep 1596191 = 2394287) B2394287
theorem B6468767 : Blo 1060614 6468767 := bstep (se 1 (by rfl) ⟨4851575, by rfl⟩ : syracuseStep 6468767 = 9703151) B9703151
theorem B1064127 : Blo 1060614 1064127 := bstep (se 1 (by rfl) ⟨798095, by rfl⟩ : syracuseStep 1064127 = 1596191) B1596191
theorem B4312511 : Blo 1060614 4312511 := bstep (se 1 (by rfl) ⟨3234383, by rfl⟩ : syracuseStep 4312511 = 6468767) B6468767
theorem B2875007 : Blo 1060614 2875007 := bstep (se 1 (by rfl) ⟨2156255, by rfl⟩ : syracuseStep 2875007 = 4312511) B4312511
theorem B1916671 : Blo 1060614 1916671 := bstep (se 1 (by rfl) ⟨1437503, by rfl⟩ : syracuseStep 1916671 = 2875007) B2875007
theorem B2555561 : Blo 1060614 2555561 := bstep (se 2 (by rfl) ⟨958335, by rfl⟩ : syracuseStep 2555561 = 1916671) B1916671
theorem B6814829 : Blo 1060614 6814829 := bstep (se 3 (by rfl) ⟨1277780, by rfl⟩ : syracuseStep 6814829 = 2555561) B2555561
theorem B4543219 : Blo 1060614 4543219 := bstep (se 1 (by rfl) ⟨3407414, by rfl⟩ : syracuseStep 4543219 = 6814829) B6814829
theorem B6057625 : Blo 1060614 6057625 := bstep (se 2 (by rfl) ⟨2271609, by rfl⟩ : syracuseStep 6057625 = 4543219) B4543219
theorem B8076833 : Blo 1060614 8076833 := bstep (se 2 (by rfl) ⟨3028812, by rfl⟩ : syracuseStep 8076833 = 6057625) B6057625
theorem B5384555 : Blo 1060614 5384555 := bstep (se 1 (by rfl) ⟨4038416, by rfl⟩ : syracuseStep 5384555 = 8076833) B8076833
theorem B3589703 : Blo 1060614 3589703 := bstep (se 1 (by rfl) ⟨2692277, by rfl⟩ : syracuseStep 3589703 = 5384555) B5384555
theorem B2393135 : Blo 1060614 2393135 := bstep (se 1 (by rfl) ⟨1794851, by rfl⟩ : syracuseStep 2393135 = 3589703) B3589703
theorem B1595423 : Blo 1060614 1595423 := bstep (se 1 (by rfl) ⟨1196567, by rfl⟩ : syracuseStep 1595423 = 2393135) B2393135
theorem B1063615 : Blo 1060614 1063615 := bstep (se 1 (by rfl) ⟨797711, by rfl⟩ : syracuseStep 1063615 = 1595423) B1595423

theorem C0 (j : ℕ) (h1 : 265153 ≤ j) (h2 : j ≤ 265852) : Blo 1060614 (4 * j + 3) := by
  interval_cases j
  · exact B1060615
  · exact B1060619
  · exact B1060623
  · exact B1060627
  · exact B1060631
  · exact B1060635
  · exact B1060639
  · exact B1060643
  · exact B1060647
  · exact B1060651
  · exact B1060655
  · exact B1060659
  · exact B1060663
  · exact B1060667
  · exact B1060671
  · exact B1060675
  · exact B1060679
  · exact B1060683
  · exact B1060687
  · exact B1060691
  · exact B1060695
  · exact B1060699
  · exact B1060703
  · exact B1060707
  · exact B1060711
  · exact B1060715
  · exact B1060719
  · exact B1060723
  · exact B1060727
  · exact B1060731
  · exact B1060735
  · exact B1060739
  · exact B1060743
  · exact B1060747
  · exact B1060751
  · exact B1060755
  · exact B1060759
  · exact B1060763
  · exact B1060767
  · exact B1060771
  · exact B1060775
  · exact B1060779
  · exact B1060783
  · exact B1060787
  · exact B1060791
  · exact B1060795
  · exact B1060799
  · exact B1060803
  · exact B1060807
  · exact B1060811
  · exact B1060815
  · exact B1060819
  · exact B1060823
  · exact B1060827
  · exact B1060831
  · exact B1060835
  · exact B1060839
  · exact B1060843
  · exact B1060847
  · exact B1060851
  · exact B1060855
  · exact B1060859
  · exact B1060863
  · exact B1060867
  · exact B1060871
  · exact B1060875
  · exact B1060879
  · exact B1060883
  · exact B1060887
  · exact B1060891
  · exact B1060895
  · exact B1060899
  · exact B1060903
  · exact B1060907
  · exact B1060911
  · exact B1060915
  · exact B1060919
  · exact B1060923
  · exact B1060927
  · exact B1060931
  · exact B1060935
  · exact B1060939
  · exact B1060943
  · exact B1060947
  · exact B1060951
  · exact B1060955
  · exact B1060959
  · exact B1060963
  · exact B1060967
  · exact B1060971
  · exact B1060975
  · exact B1060979
  · exact B1060983
  · exact B1060987
  · exact B1060991
  · exact B1060995
  · exact B1060999
  · exact B1061003
  · exact B1061007
  · exact B1061011
  · exact B1061015
  · exact B1061019
  · exact B1061023
  · exact B1061027
  · exact B1061031
  · exact B1061035
  · exact B1061039
  · exact B1061043
  · exact B1061047
  · exact B1061051
  · exact B1061055
  · exact B1061059
  · exact B1061063
  · exact B1061067
  · exact B1061071
  · exact B1061075
  · exact B1061079
  · exact B1061083
  · exact B1061087
  · exact B1061091
  · exact B1061095
  · exact B1061099
  · exact B1061103
  · exact B1061107
  · exact B1061111
  · exact B1061115
  · exact B1061119
  · exact B1061123
  · exact B1061127
  · exact B1061131
  · exact B1061135
  · exact B1061139
  · exact B1061143
  · exact B1061147
  · exact B1061151
  · exact B1061155
  · exact B1061159
  · exact B1061163
  · exact B1061167
  · exact B1061171
  · exact B1061175
  · exact B1061179
  · exact B1061183
  · exact B1061187
  · exact B1061191
  · exact B1061195
  · exact B1061199
  · exact B1061203
  · exact B1061207
  · exact B1061211
  · exact B1061215
  · exact B1061219
  · exact B1061223
  · exact B1061227
  · exact B1061231
  · exact B1061235
  · exact B1061239
  · exact B1061243
  · exact B1061247
  · exact B1061251
  · exact B1061255
  · exact B1061259
  · exact B1061263
  · exact B1061267
  · exact B1061271
  · exact B1061275
  · exact B1061279
  · exact B1061283
  · exact B1061287
  · exact B1061291
  · exact B1061295
  · exact B1061299
  · exact B1061303
  · exact B1061307
  · exact B1061311
  · exact B1061315
  · exact B1061319
  · exact B1061323
  · exact B1061327
  · exact B1061331
  · exact B1061335
  · exact B1061339
  · exact B1061343
  · exact B1061347
  · exact B1061351
  · exact B1061355
  · exact B1061359
  · exact B1061363
  · exact B1061367
  · exact B1061371
  · exact B1061375
  · exact B1061379
  · exact B1061383
  · exact B1061387
  · exact B1061391
  · exact B1061395
  · exact B1061399
  · exact B1061403
  · exact B1061407
  · exact B1061411
  · exact B1061415
  · exact B1061419
  · exact B1061423
  · exact B1061427
  · exact B1061431
  · exact B1061435
  · exact B1061439
  · exact B1061443
  · exact B1061447
  · exact B1061451
  · exact B1061455
  · exact B1061459
  · exact B1061463
  · exact B1061467
  · exact B1061471
  · exact B1061475
  · exact B1061479
  · exact B1061483
  · exact B1061487
  · exact B1061491
  · exact B1061495
  · exact B1061499
  · exact B1061503
  · exact B1061507
  · exact B1061511
  · exact B1061515
  · exact B1061519
  · exact B1061523
  · exact B1061527
  · exact B1061531
  · exact B1061535
  · exact B1061539
  · exact B1061543
  · exact B1061547
  · exact B1061551
  · exact B1061555
  · exact B1061559
  · exact B1061563
  · exact B1061567
  · exact B1061571
  · exact B1061575
  · exact B1061579
  · exact B1061583
  · exact B1061587
  · exact B1061591
  · exact B1061595
  · exact B1061599
  · exact B1061603
  · exact B1061607
  · exact B1061611
  · exact B1061615
  · exact B1061619
  · exact B1061623
  · exact B1061627
  · exact B1061631
  · exact B1061635
  · exact B1061639
  · exact B1061643
  · exact B1061647
  · exact B1061651
  · exact B1061655
  · exact B1061659
  · exact B1061663
  · exact B1061667
  · exact B1061671
  · exact B1061675
  · exact B1061679
  · exact B1061683
  · exact B1061687
  · exact B1061691
  · exact B1061695
  · exact B1061699
  · exact B1061703
  · exact B1061707
  · exact B1061711
  · exact B1061715
  · exact B1061719
  · exact B1061723
  · exact B1061727
  · exact B1061731
  · exact B1061735
  · exact B1061739
  · exact B1061743
  · exact B1061747
  · exact B1061751
  · exact B1061755
  · exact B1061759
  · exact B1061763
  · exact B1061767
  · exact B1061771
  · exact B1061775
  · exact B1061779
  · exact B1061783
  · exact B1061787
  · exact B1061791
  · exact B1061795
  · exact B1061799
  · exact B1061803
  · exact B1061807
  · exact B1061811
  · exact B1061815
  · exact B1061819
  · exact B1061823
  · exact B1061827
  · exact B1061831
  · exact B1061835
  · exact B1061839
  · exact B1061843
  · exact B1061847
  · exact B1061851
  · exact B1061855
  · exact B1061859
  · exact B1061863
  · exact B1061867
  · exact B1061871
  · exact B1061875
  · exact B1061879
  · exact B1061883
  · exact B1061887
  · exact B1061891
  · exact B1061895
  · exact B1061899
  · exact B1061903
  · exact B1061907
  · exact B1061911
  · exact B1061915
  · exact B1061919
  · exact B1061923
  · exact B1061927
  · exact B1061931
  · exact B1061935
  · exact B1061939
  · exact B1061943
  · exact B1061947
  · exact B1061951
  · exact B1061955
  · exact B1061959
  · exact B1061963
  · exact B1061967
  · exact B1061971
  · exact B1061975
  · exact B1061979
  · exact B1061983
  · exact B1061987
  · exact B1061991
  · exact B1061995
  · exact B1061999
  · exact B1062003
  · exact B1062007
  · exact B1062011
  · exact B1062015
  · exact B1062019
  · exact B1062023
  · exact B1062027
  · exact B1062031
  · exact B1062035
  · exact B1062039
  · exact B1062043
  · exact B1062047
  · exact B1062051
  · exact B1062055
  · exact B1062059
  · exact B1062063
  · exact B1062067
  · exact B1062071
  · exact B1062075
  · exact B1062079
  · exact B1062083
  · exact B1062087
  · exact B1062091
  · exact B1062095
  · exact B1062099
  · exact B1062103
  · exact B1062107
  · exact B1062111
  · exact B1062115
  · exact B1062119
  · exact B1062123
  · exact B1062127
  · exact B1062131
  · exact B1062135
  · exact B1062139
  · exact B1062143
  · exact B1062147
  · exact B1062151
  · exact B1062155
  · exact B1062159
  · exact B1062163
  · exact B1062167
  · exact B1062171
  · exact B1062175
  · exact B1062179
  · exact B1062183
  · exact B1062187
  · exact B1062191
  · exact B1062195
  · exact B1062199
  · exact B1062203
  · exact B1062207
  · exact B1062211
  · exact B1062215
  · exact B1062219
  · exact B1062223
  · exact B1062227
  · exact B1062231
  · exact B1062235
  · exact B1062239
  · exact B1062243
  · exact B1062247
  · exact B1062251
  · exact B1062255
  · exact B1062259
  · exact B1062263
  · exact B1062267
  · exact B1062271
  · exact B1062275
  · exact B1062279
  · exact B1062283
  · exact B1062287
  · exact B1062291
  · exact B1062295
  · exact B1062299
  · exact B1062303
  · exact B1062307
  · exact B1062311
  · exact B1062315
  · exact B1062319
  · exact B1062323
  · exact B1062327
  · exact B1062331
  · exact B1062335
  · exact B1062339
  · exact B1062343
  · exact B1062347
  · exact B1062351
  · exact B1062355
  · exact B1062359
  · exact B1062363
  · exact B1062367
  · exact B1062371
  · exact B1062375
  · exact B1062379
  · exact B1062383
  · exact B1062387
  · exact B1062391
  · exact B1062395
  · exact B1062399
  · exact B1062403
  · exact B1062407
  · exact B1062411
  · exact B1062415
  · exact B1062419
  · exact B1062423
  · exact B1062427
  · exact B1062431
  · exact B1062435
  · exact B1062439
  · exact B1062443
  · exact B1062447
  · exact B1062451
  · exact B1062455
  · exact B1062459
  · exact B1062463
  · exact B1062467
  · exact B1062471
  · exact B1062475
  · exact B1062479
  · exact B1062483
  · exact B1062487
  · exact B1062491
  · exact B1062495
  · exact B1062499
  · exact B1062503
  · exact B1062507
  · exact B1062511
  · exact B1062515
  · exact B1062519
  · exact B1062523
  · exact B1062527
  · exact B1062531
  · exact B1062535
  · exact B1062539
  · exact B1062543
  · exact B1062547
  · exact B1062551
  · exact B1062555
  · exact B1062559
  · exact B1062563
  · exact B1062567
  · exact B1062571
  · exact B1062575
  · exact B1062579
  · exact B1062583
  · exact B1062587
  · exact B1062591
  · exact B1062595
  · exact B1062599
  · exact B1062603
  · exact B1062607
  · exact B1062611
  · exact B1062615
  · exact B1062619
  · exact B1062623
  · exact B1062627
  · exact B1062631
  · exact B1062635
  · exact B1062639
  · exact B1062643
  · exact B1062647
  · exact B1062651
  · exact B1062655
  · exact B1062659
  · exact B1062663
  · exact B1062667
  · exact B1062671
  · exact B1062675
  · exact B1062679
  · exact B1062683
  · exact B1062687
  · exact B1062691
  · exact B1062695
  · exact B1062699
  · exact B1062703
  · exact B1062707
  · exact B1062711
  · exact B1062715
  · exact B1062719
  · exact B1062723
  · exact B1062727
  · exact B1062731
  · exact B1062735
  · exact B1062739
  · exact B1062743
  · exact B1062747
  · exact B1062751
  · exact B1062755
  · exact B1062759
  · exact B1062763
  · exact B1062767
  · exact B1062771
  · exact B1062775
  · exact B1062779
  · exact B1062783
  · exact B1062787
  · exact B1062791
  · exact B1062795
  · exact B1062799
  · exact B1062803
  · exact B1062807
  · exact B1062811
  · exact B1062815
  · exact B1062819
  · exact B1062823
  · exact B1062827
  · exact B1062831
  · exact B1062835
  · exact B1062839
  · exact B1062843
  · exact B1062847
  · exact B1062851
  · exact B1062855
  · exact B1062859
  · exact B1062863
  · exact B1062867
  · exact B1062871
  · exact B1062875
  · exact B1062879
  · exact B1062883
  · exact B1062887
  · exact B1062891
  · exact B1062895
  · exact B1062899
  · exact B1062903
  · exact B1062907
  · exact B1062911
  · exact B1062915
  · exact B1062919
  · exact B1062923
  · exact B1062927
  · exact B1062931
  · exact B1062935
  · exact B1062939
  · exact B1062943
  · exact B1062947
  · exact B1062951
  · exact B1062955
  · exact B1062959
  · exact B1062963
  · exact B1062967
  · exact B1062971
  · exact B1062975
  · exact B1062979
  · exact B1062983
  · exact B1062987
  · exact B1062991
  · exact B1062995
  · exact B1062999
  · exact B1063003
  · exact B1063007
  · exact B1063011
  · exact B1063015
  · exact B1063019
  · exact B1063023
  · exact B1063027
  · exact B1063031
  · exact B1063035
  · exact B1063039
  · exact B1063043
  · exact B1063047
  · exact B1063051
  · exact B1063055
  · exact B1063059
  · exact B1063063
  · exact B1063067
  · exact B1063071
  · exact B1063075
  · exact B1063079
  · exact B1063083
  · exact B1063087
  · exact B1063091
  · exact B1063095
  · exact B1063099
  · exact B1063103
  · exact B1063107
  · exact B1063111
  · exact B1063115
  · exact B1063119
  · exact B1063123
  · exact B1063127
  · exact B1063131
  · exact B1063135
  · exact B1063139
  · exact B1063143
  · exact B1063147
  · exact B1063151
  · exact B1063155
  · exact B1063159
  · exact B1063163
  · exact B1063167
  · exact B1063171
  · exact B1063175
  · exact B1063179
  · exact B1063183
  · exact B1063187
  · exact B1063191
  · exact B1063195
  · exact B1063199
  · exact B1063203
  · exact B1063207
  · exact B1063211
  · exact B1063215
  · exact B1063219
  · exact B1063223
  · exact B1063227
  · exact B1063231
  · exact B1063235
  · exact B1063239
  · exact B1063243
  · exact B1063247
  · exact B1063251
  · exact B1063255
  · exact B1063259
  · exact B1063263
  · exact B1063267
  · exact B1063271
  · exact B1063275
  · exact B1063279
  · exact B1063283
  · exact B1063287
  · exact B1063291
  · exact B1063295
  · exact B1063299
  · exact B1063303
  · exact B1063307
  · exact B1063311
  · exact B1063315
  · exact B1063319
  · exact B1063323
  · exact B1063327
  · exact B1063331
  · exact B1063335
  · exact B1063339
  · exact B1063343
  · exact B1063347
  · exact B1063351
  · exact B1063355
  · exact B1063359
  · exact B1063363
  · exact B1063367
  · exact B1063371
  · exact B1063375
  · exact B1063379
  · exact B1063383
  · exact B1063387
  · exact B1063391
  · exact B1063395
  · exact B1063399
  · exact B1063403
  · exact B1063407
  · exact B1063411

theorem C1 (j : ℕ) (h1 : 265853 ≤ j) (h2 : j ≤ 266152) : Blo 1060614 (4 * j + 3) := by
  interval_cases j
  · exact B1063415
  · exact B1063419
  · exact B1063423
  · exact B1063427
  · exact B1063431
  · exact B1063435
  · exact B1063439
  · exact B1063443
  · exact B1063447
  · exact B1063451
  · exact B1063455
  · exact B1063459
  · exact B1063463
  · exact B1063467
  · exact B1063471
  · exact B1063475
  · exact B1063479
  · exact B1063483
  · exact B1063487
  · exact B1063491
  · exact B1063495
  · exact B1063499
  · exact B1063503
  · exact B1063507
  · exact B1063511
  · exact B1063515
  · exact B1063519
  · exact B1063523
  · exact B1063527
  · exact B1063531
  · exact B1063535
  · exact B1063539
  · exact B1063543
  · exact B1063547
  · exact B1063551
  · exact B1063555
  · exact B1063559
  · exact B1063563
  · exact B1063567
  · exact B1063571
  · exact B1063575
  · exact B1063579
  · exact B1063583
  · exact B1063587
  · exact B1063591
  · exact B1063595
  · exact B1063599
  · exact B1063603
  · exact B1063607
  · exact B1063611
  · exact B1063615
  · exact B1063619
  · exact B1063623
  · exact B1063627
  · exact B1063631
  · exact B1063635
  · exact B1063639
  · exact B1063643
  · exact B1063647
  · exact B1063651
  · exact B1063655
  · exact B1063659
  · exact B1063663
  · exact B1063667
  · exact B1063671
  · exact B1063675
  · exact B1063679
  · exact B1063683
  · exact B1063687
  · exact B1063691
  · exact B1063695
  · exact B1063699
  · exact B1063703
  · exact B1063707
  · exact B1063711
  · exact B1063715
  · exact B1063719
  · exact B1063723
  · exact B1063727
  · exact B1063731
  · exact B1063735
  · exact B1063739
  · exact B1063743
  · exact B1063747
  · exact B1063751
  · exact B1063755
  · exact B1063759
  · exact B1063763
  · exact B1063767
  · exact B1063771
  · exact B1063775
  · exact B1063779
  · exact B1063783
  · exact B1063787
  · exact B1063791
  · exact B1063795
  · exact B1063799
  · exact B1063803
  · exact B1063807
  · exact B1063811
  · exact B1063815
  · exact B1063819
  · exact B1063823
  · exact B1063827
  · exact B1063831
  · exact B1063835
  · exact B1063839
  · exact B1063843
  · exact B1063847
  · exact B1063851
  · exact B1063855
  · exact B1063859
  · exact B1063863
  · exact B1063867
  · exact B1063871
  · exact B1063875
  · exact B1063879
  · exact B1063883
  · exact B1063887
  · exact B1063891
  · exact B1063895
  · exact B1063899
  · exact B1063903
  · exact B1063907
  · exact B1063911
  · exact B1063915
  · exact B1063919
  · exact B1063923
  · exact B1063927
  · exact B1063931
  · exact B1063935
  · exact B1063939
  · exact B1063943
  · exact B1063947
  · exact B1063951
  · exact B1063955
  · exact B1063959
  · exact B1063963
  · exact B1063967
  · exact B1063971
  · exact B1063975
  · exact B1063979
  · exact B1063983
  · exact B1063987
  · exact B1063991
  · exact B1063995
  · exact B1063999
  · exact B1064003
  · exact B1064007
  · exact B1064011
  · exact B1064015
  · exact B1064019
  · exact B1064023
  · exact B1064027
  · exact B1064031
  · exact B1064035
  · exact B1064039
  · exact B1064043
  · exact B1064047
  · exact B1064051
  · exact B1064055
  · exact B1064059
  · exact B1064063
  · exact B1064067
  · exact B1064071
  · exact B1064075
  · exact B1064079
  · exact B1064083
  · exact B1064087
  · exact B1064091
  · exact B1064095
  · exact B1064099
  · exact B1064103
  · exact B1064107
  · exact B1064111
  · exact B1064115
  · exact B1064119
  · exact B1064123
  · exact B1064127
  · exact B1064131
  · exact B1064135
  · exact B1064139
  · exact B1064143
  · exact B1064147
  · exact B1064151
  · exact B1064155
  · exact B1064159
  · exact B1064163
  · exact B1064167
  · exact B1064171
  · exact B1064175
  · exact B1064179
  · exact B1064183
  · exact B1064187
  · exact B1064191
  · exact B1064195
  · exact B1064199
  · exact B1064203
  · exact B1064207
  · exact B1064211
  · exact B1064215
  · exact B1064219
  · exact B1064223
  · exact B1064227
  · exact B1064231
  · exact B1064235
  · exact B1064239
  · exact B1064243
  · exact B1064247
  · exact B1064251
  · exact B1064255
  · exact B1064259
  · exact B1064263
  · exact B1064267
  · exact B1064271
  · exact B1064275
  · exact B1064279
  · exact B1064283
  · exact B1064287
  · exact B1064291
  · exact B1064295
  · exact B1064299
  · exact B1064303
  · exact B1064307
  · exact B1064311
  · exact B1064315
  · exact B1064319
  · exact B1064323
  · exact B1064327
  · exact B1064331
  · exact B1064335
  · exact B1064339
  · exact B1064343
  · exact B1064347
  · exact B1064351
  · exact B1064355
  · exact B1064359
  · exact B1064363
  · exact B1064367
  · exact B1064371
  · exact B1064375
  · exact B1064379
  · exact B1064383
  · exact B1064387
  · exact B1064391
  · exact B1064395
  · exact B1064399
  · exact B1064403
  · exact B1064407
  · exact B1064411
  · exact B1064415
  · exact B1064419
  · exact B1064423
  · exact B1064427
  · exact B1064431
  · exact B1064435
  · exact B1064439
  · exact B1064443
  · exact B1064447
  · exact B1064451
  · exact B1064455
  · exact B1064459
  · exact B1064463
  · exact B1064467
  · exact B1064471
  · exact B1064475
  · exact B1064479
  · exact B1064483
  · exact B1064487
  · exact B1064491
  · exact B1064495
  · exact B1064499
  · exact B1064503
  · exact B1064507
  · exact B1064511
  · exact B1064515
  · exact B1064519
  · exact B1064523
  · exact B1064527
  · exact B1064531
  · exact B1064535
  · exact B1064539
  · exact B1064543
  · exact B1064547
  · exact B1064551
  · exact B1064555
  · exact B1064559
  · exact B1064563
  · exact B1064567
  · exact B1064571
  · exact B1064575
  · exact B1064579
  · exact B1064583
  · exact B1064587
  · exact B1064591
  · exact B1064595
  · exact B1064599
  · exact B1064603
  · exact B1064607
  · exact B1064611

theorem solution (m : ℕ) (hlo : 1060614 ≤ m) (hhi : m ≤ 1064614) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 265153 ≤ j := by omega
    have hj2 : j ≤ 266152 := by omega
    have hb : Blo 1060614 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 265853 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
