-- Prove2me | solution 1 for syracuse_descends_range_626299_630299
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:36.468146+00:00
-- url     : https://prove2.me/submissions/2d288855-ba31-44a0-8ca7-4fd53d9a3c49

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


theorem B1146901 : Blo 626299 1146901 := bbase (se 6 (by rfl) ⟨26880, by rfl⟩ : syracuseStep 1146901 = 53761) (by norm_num)
theorem B753769 : Blo 626299 753769 := bbase (se 2 (by rfl) ⟨282663, by rfl⟩ : syracuseStep 753769 = 565327) (by norm_num)
theorem B2392213 : Blo 626299 2392213 := bbase (se 6 (by rfl) ⟨56067, by rfl⟩ : syracuseStep 2392213 = 112135) (by norm_num)
theorem B1409237 : Blo 626299 1409237 := bbase (se 7 (by rfl) ⟨16514, by rfl⟩ : syracuseStep 1409237 = 33029) (by norm_num)
theorem B1409309 : Blo 626299 1409309 := bbase (se 3 (by rfl) ⟨264245, by rfl⟩ : syracuseStep 1409309 = 528491) (by norm_num)
theorem B1409381 : Blo 626299 1409381 := bbase (se 4 (by rfl) ⟨132129, by rfl⟩ : syracuseStep 1409381 = 264259) (by norm_num)
theorem B1343861 : Blo 626299 1343861 := bbase (se 5 (by rfl) ⟨62993, by rfl⟩ : syracuseStep 1343861 = 125987) (by norm_num)
theorem B1409453 : Blo 626299 1409453 := bbase (se 3 (by rfl) ⟨264272, by rfl⟩ : syracuseStep 1409453 = 528545) (by norm_num)
theorem B2687413 : Blo 626299 2687413 := bbase (se 5 (by rfl) ⟨125972, by rfl⟩ : syracuseStep 2687413 = 251945) (by norm_num)
theorem B2392517 : Blo 626299 2392517 := bbase (se 4 (by rfl) ⟨224298, by rfl⟩ : syracuseStep 2392517 = 448597) (by norm_num)
theorem B1409525 : Blo 626299 1409525 := bbase (se 5 (by rfl) ⟨66071, by rfl⟩ : syracuseStep 1409525 = 132143) (by norm_num)
theorem B1409597 : Blo 626299 1409597 := bbase (se 3 (by rfl) ⟨264299, by rfl⟩ : syracuseStep 1409597 = 528599) (by norm_num)
theorem B1344109 : Blo 626299 1344109 := bbase (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) (by norm_num)
theorem B6128245 : Blo 626299 6128245 := bbase (se 5 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 6128245 = 574523) (by norm_num)
theorem B1409669 : Blo 626299 1409669 := bbase (se 4 (by rfl) ⟨132156, by rfl⟩ : syracuseStep 1409669 = 264313) (by norm_num)
theorem B1409741 : Blo 626299 1409741 := bbase (se 3 (by rfl) ⟨264326, by rfl⟩ : syracuseStep 1409741 = 528653) (by norm_num)
theorem B5079829 : Blo 626299 5079829 := bbase (se 6 (by rfl) ⟨119058, by rfl⟩ : syracuseStep 5079829 = 238117) (by norm_num)
theorem B1409813 : Blo 626299 1409813 := bbase (se 6 (by rfl) ⟨33042, by rfl⟩ : syracuseStep 1409813 = 66085) (by norm_num)
theorem B1409885 : Blo 626299 1409885 := bbase (se 3 (by rfl) ⟨264353, by rfl⟩ : syracuseStep 1409885 = 528707) (by norm_num)
theorem B1409957 : Blo 626299 1409957 := bbase (se 4 (by rfl) ⟨132183, by rfl⟩ : syracuseStep 1409957 = 264367) (by norm_num)
theorem B3572693 : Blo 626299 3572693 := bbase (se 7 (by rfl) ⟨41867, by rfl⟩ : syracuseStep 3572693 = 83735) (by norm_num)
theorem B1410029 : Blo 626299 1410029 := bbase (se 3 (by rfl) ⟨264380, by rfl⟩ : syracuseStep 1410029 = 528761) (by norm_num)
theorem B1410101 : Blo 626299 1410101 := bbase (se 5 (by rfl) ⟨66098, by rfl⟩ : syracuseStep 1410101 = 132197) (by norm_num)
theorem B3179573 : Blo 626299 3179573 := bbase (se 5 (by rfl) ⟨149042, by rfl⟩ : syracuseStep 3179573 = 298085) (by norm_num)
theorem B41976917 : Blo 626299 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B1344613 : Blo 626299 1344613 := bbase (se 4 (by rfl) ⟨126057, by rfl⟩ : syracuseStep 1344613 = 252115) (by norm_num)
theorem B1410173 : Blo 626299 1410173 := bbase (se 3 (by rfl) ⟨264407, by rfl⟩ : syracuseStep 1410173 = 528815) (by norm_num)
theorem B1410245 : Blo 626299 1410245 := bbase (se 4 (by rfl) ⟨132210, by rfl⟩ : syracuseStep 1410245 = 264421) (by norm_num)
theorem B1410317 : Blo 626299 1410317 := bbase (se 3 (by rfl) ⟨264434, by rfl⟩ : syracuseStep 1410317 = 528869) (by norm_num)
theorem B1410389 : Blo 626299 1410389 := bbase (se 12 (by rfl) ⟨516, by rfl⟩ : syracuseStep 1410389 = 1033) (by norm_num)
theorem B1410461 : Blo 626299 1410461 := bbase (se 3 (by rfl) ⟨264461, by rfl⟩ : syracuseStep 1410461 = 528923) (by norm_num)
theorem B1410533 : Blo 626299 1410533 := bbase (se 4 (by rfl) ⟨132237, by rfl⟩ : syracuseStep 1410533 = 264475) (by norm_num)
theorem B1410605 : Blo 626299 1410605 := bbase (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) (by norm_num)
theorem B1410677 : Blo 626299 1410677 := bbase (se 5 (by rfl) ⟨66125, by rfl⟩ : syracuseStep 1410677 = 132251) (by norm_num)
theorem B1410749 : Blo 626299 1410749 := bbase (se 3 (by rfl) ⟨264515, by rfl⟩ : syracuseStep 1410749 = 529031) (by norm_num)
theorem B1410821 : Blo 626299 1410821 := bbase (se 4 (by rfl) ⟨132264, by rfl⟩ : syracuseStep 1410821 = 264529) (by norm_num)
theorem B1509133 : Blo 626299 1509133 := bbase (se 3 (by rfl) ⟨282962, by rfl⟩ : syracuseStep 1509133 = 565925) (by norm_num)
theorem B755489 : Blo 626299 755489 := bbase (se 2 (by rfl) ⟨283308, by rfl⟩ : syracuseStep 755489 = 566617) (by norm_num)
theorem B1410893 : Blo 626299 1410893 := bbase (se 3 (by rfl) ⟨264542, by rfl⟩ : syracuseStep 1410893 = 529085) (by norm_num)
theorem B1410965 : Blo 626299 1410965 := bbase (se 6 (by rfl) ⟨33069, by rfl⟩ : syracuseStep 1410965 = 66139) (by norm_num)
theorem B755605 : Blo 626299 755605 := bbase (se 6 (by rfl) ⟨17709, by rfl⟩ : syracuseStep 755605 = 35419) (by norm_num)
theorem B1411037 : Blo 626299 1411037 := bbase (se 3 (by rfl) ⟨264569, by rfl⟩ : syracuseStep 1411037 = 529139) (by norm_num)
theorem B755677 : Blo 626299 755677 := bbase (se 3 (by rfl) ⟨141689, by rfl⟩ : syracuseStep 755677 = 283379) (by norm_num)
theorem B1345501 : Blo 626299 1345501 := bbase (se 3 (by rfl) ⟨252281, by rfl⟩ : syracuseStep 1345501 = 504563) (by norm_num)
theorem B6031381 : Blo 626299 6031381 := bbase (se 6 (by rfl) ⟨141360, by rfl⟩ : syracuseStep 6031381 = 282721) (by norm_num)
theorem B1411109 : Blo 626299 1411109 := bbase (se 4 (by rfl) ⟨132291, by rfl⟩ : syracuseStep 1411109 = 264583) (by norm_num)
theorem B755797 : Blo 626299 755797 := bbase (se 8 (by rfl) ⟨4428, by rfl⟩ : syracuseStep 755797 = 8857) (by norm_num)
theorem B1411181 : Blo 626299 1411181 := bbase (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) (by norm_num)
theorem B952445 : Blo 626299 952445 := bbase (se 3 (by rfl) ⟨178583, by rfl⟩ : syracuseStep 952445 = 357167) (by norm_num)
theorem B1509509 : Blo 626299 1509509 := bbase (se 4 (by rfl) ⟨141516, by rfl⟩ : syracuseStep 1509509 = 283033) (by norm_num)
theorem B1411253 : Blo 626299 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B1411325 : Blo 626299 1411325 := bbase (se 3 (by rfl) ⟨264623, by rfl⟩ : syracuseStep 1411325 = 529247) (by norm_num)
theorem B1411397 : Blo 626299 1411397 := bbase (se 4 (by rfl) ⟨132318, by rfl⟩ : syracuseStep 1411397 = 264637) (by norm_num)
theorem B3180869 : Blo 626299 3180869 := bbase (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) (by norm_num)
theorem B1411469 : Blo 626299 1411469 := bbase (se 3 (by rfl) ⟨264650, by rfl⟩ : syracuseStep 1411469 = 529301) (by norm_num)
theorem B690589 : Blo 626299 690589 := bbase (se 3 (by rfl) ⟨129485, by rfl⟩ : syracuseStep 690589 = 258971) (by norm_num)
theorem B1345997 : Blo 626299 1345997 := bbase (se 3 (by rfl) ⟨252374, by rfl⟩ : syracuseStep 1345997 = 504749) (by norm_num)
theorem B1411541 : Blo 626299 1411541 := bbase (se 7 (by rfl) ⟨16541, by rfl⟩ : syracuseStep 1411541 = 33083) (by norm_num)
theorem B756181 : Blo 626299 756181 := bbase (se 7 (by rfl) ⟨8861, by rfl⟩ : syracuseStep 756181 = 17723) (by norm_num)
theorem B3017189 : Blo 626299 3017189 := bbase (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) (by norm_num)
theorem B1411613 : Blo 626299 1411613 := bbase (se 3 (by rfl) ⟨264677, by rfl⟩ : syracuseStep 1411613 = 529355) (by norm_num)
theorem B1509941 : Blo 626299 1509941 := bbase (se 5 (by rfl) ⟨70778, by rfl⟩ : syracuseStep 1509941 = 141557) (by norm_num)
theorem B1411685 : Blo 626299 1411685 := bbase (se 4 (by rfl) ⟨132345, by rfl⟩ : syracuseStep 1411685 = 264691) (by norm_num)
theorem B2722405 : Blo 626299 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B1411757 : Blo 626299 1411757 := bbase (se 3 (by rfl) ⟨264704, by rfl⟩ : syracuseStep 1411757 = 529409) (by norm_num)
theorem B1411829 : Blo 626299 1411829 := bbase (se 5 (by rfl) ⟨66179, by rfl⟩ : syracuseStep 1411829 = 132359) (by norm_num)
theorem B1018621 : Blo 626299 1018621 := bbase (se 3 (by rfl) ⟨190991, by rfl⟩ : syracuseStep 1018621 = 381983) (by norm_num)
theorem B953101 : Blo 626299 953101 := bbase (se 3 (by rfl) ⟨178706, by rfl⟩ : syracuseStep 953101 = 357413) (by norm_num)
theorem B1411901 : Blo 626299 1411901 := bbase (se 3 (by rfl) ⟨264731, by rfl⟩ : syracuseStep 1411901 = 529463) (by norm_num)
theorem B1411973 : Blo 626299 1411973 := bbase (se 4 (by rfl) ⟨132372, by rfl⟩ : syracuseStep 1411973 = 264745) (by norm_num)
theorem B1412045 : Blo 626299 1412045 := bbase (se 3 (by rfl) ⟨264758, by rfl⟩ : syracuseStep 1412045 = 529517) (by norm_num)
theorem B5377013 : Blo 626299 5377013 := bbase (se 5 (by rfl) ⟨252047, by rfl⟩ : syracuseStep 5377013 = 504095) (by norm_num)
theorem B1412117 : Blo 626299 1412117 := bbase (se 6 (by rfl) ⟨33096, by rfl⟩ : syracuseStep 1412117 = 66193) (by norm_num)
theorem B1412189 : Blo 626299 1412189 := bbase (se 3 (by rfl) ⟨264785, by rfl⟩ : syracuseStep 1412189 = 529571) (by norm_num)
theorem B1510517 : Blo 626299 1510517 := bbase (se 5 (by rfl) ⟨70805, by rfl⟩ : syracuseStep 1510517 = 141611) (by norm_num)
theorem B756869 : Blo 626299 756869 := bbase (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) (by norm_num)
theorem B1412261 : Blo 626299 1412261 := bbase (se 4 (by rfl) ⟨132399, by rfl⟩ : syracuseStep 1412261 = 264799) (by norm_num)
theorem B1412333 : Blo 626299 1412333 := bbase (se 3 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 1412333 = 529625) (by norm_num)
theorem B1412405 : Blo 626299 1412405 := bbase (se 5 (by rfl) ⟨66206, by rfl⟩ : syracuseStep 1412405 = 132413) (by norm_num)
theorem B2690405 : Blo 626299 2690405 := bbase (se 4 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 2690405 = 504451) (by norm_num)
theorem B691573 : Blo 626299 691573 := bbase (se 5 (by rfl) ⟨32417, by rfl⟩ : syracuseStep 691573 = 64835) (by norm_num)
theorem B1412477 : Blo 626299 1412477 := bbase (se 3 (by rfl) ⟨264839, by rfl⟩ : syracuseStep 1412477 = 529679) (by norm_num)
theorem B1412549 : Blo 626299 1412549 := bbase (se 4 (by rfl) ⟨132426, by rfl⟩ : syracuseStep 1412549 = 264853) (by norm_num)
theorem B1412621 : Blo 626299 1412621 := bbase (se 3 (by rfl) ⟨264866, by rfl⟩ : syracuseStep 1412621 = 529733) (by norm_num)
theorem B953893 : Blo 626299 953893 := bbase (se 4 (by rfl) ⟨89427, by rfl⟩ : syracuseStep 953893 = 178855) (by norm_num)
theorem B1412693 : Blo 626299 1412693 := bbase (se 8 (by rfl) ⟨8277, by rfl⟩ : syracuseStep 1412693 = 16555) (by norm_num)
theorem B3182165 : Blo 626299 3182165 := bbase (se 8 (by rfl) ⟨18645, by rfl⟩ : syracuseStep 3182165 = 37291) (by norm_num)
theorem B1412765 : Blo 626299 1412765 := bbase (se 3 (by rfl) ⟨264893, by rfl⟩ : syracuseStep 1412765 = 529787) (by norm_num)
theorem B5738165 : Blo 626299 5738165 := bbase (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) (by norm_num)
theorem B1412837 : Blo 626299 1412837 := bbase (se 4 (by rfl) ⟨132453, by rfl⟩ : syracuseStep 1412837 = 264907) (by norm_num)
theorem B1412909 : Blo 626299 1412909 := bbase (se 3 (by rfl) ⟨264920, by rfl⟩ : syracuseStep 1412909 = 529841) (by norm_num)
theorem B1412981 : Blo 626299 1412981 := bbase (se 5 (by rfl) ⟨66233, by rfl⟩ : syracuseStep 1412981 = 132467) (by norm_num)
theorem B2723701 : Blo 626299 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B4820885 : Blo 626299 4820885 := bbase (se 6 (by rfl) ⟨112989, by rfl⟩ : syracuseStep 4820885 = 225979) (by norm_num)
theorem B1413053 : Blo 626299 1413053 := bbase (se 3 (by rfl) ⟨264947, by rfl⟩ : syracuseStep 1413053 = 529895) (by norm_num)
theorem B1413125 : Blo 626299 1413125 := bbase (se 4 (by rfl) ⟨132480, by rfl⟩ : syracuseStep 1413125 = 264961) (by norm_num)
theorem B1413197 : Blo 626299 1413197 := bbase (se 3 (by rfl) ⟨264974, by rfl⟩ : syracuseStep 1413197 = 529949) (by norm_num)
theorem B8065109 : Blo 626299 8065109 := bbase (se 8 (by rfl) ⟨47256, by rfl⟩ : syracuseStep 8065109 = 94513) (by norm_num)
theorem B1413269 : Blo 626299 1413269 := bbase (se 6 (by rfl) ⟨33123, by rfl⟩ : syracuseStep 1413269 = 66247) (by norm_num)
theorem B1413341 : Blo 626299 1413341 := bbase (se 3 (by rfl) ⟨265001, by rfl⟩ : syracuseStep 1413341 = 530003) (by norm_num)
theorem B1413413 : Blo 626299 1413413 := bbase (se 4 (by rfl) ⟨132507, by rfl⟩ : syracuseStep 1413413 = 265015) (by norm_num)
theorem B2691413 : Blo 626299 2691413 := bbase (se 10 (by rfl) ⟨3942, by rfl⟩ : syracuseStep 2691413 = 7885) (by norm_num)
theorem B1413485 : Blo 626299 1413485 := bbase (se 3 (by rfl) ⟨265028, by rfl⟩ : syracuseStep 1413485 = 530057) (by norm_num)
theorem B954757 : Blo 626299 954757 := bbase (se 4 (by rfl) ⟨89508, by rfl⟩ : syracuseStep 954757 = 179017) (by norm_num)
theorem B1413557 : Blo 626299 1413557 := bbase (se 5 (by rfl) ⟨66260, by rfl⟩ : syracuseStep 1413557 = 132521) (by norm_num)
theorem B1413629 : Blo 626299 1413629 := bbase (se 3 (by rfl) ⟨265055, by rfl⟩ : syracuseStep 1413629 = 530111) (by norm_num)
theorem B1413701 : Blo 626299 1413701 := bbase (se 4 (by rfl) ⟨132534, by rfl⟩ : syracuseStep 1413701 = 265069) (by norm_num)
theorem B1020485 : Blo 626299 1020485 := bbase (se 4 (by rfl) ⟨95670, by rfl⟩ : syracuseStep 1020485 = 191341) (by norm_num)
theorem B1413773 : Blo 626299 1413773 := bbase (se 3 (by rfl) ⟨265082, by rfl⟩ : syracuseStep 1413773 = 530165) (by norm_num)
theorem B4035221 : Blo 626299 4035221 := bbase (se 6 (by rfl) ⟨94575, by rfl⟩ : syracuseStep 4035221 = 189151) (by norm_num)
theorem B1413845 : Blo 626299 1413845 := bbase (se 7 (by rfl) ⟨16568, by rfl⟩ : syracuseStep 1413845 = 33137) (by norm_num)
theorem B1413917 : Blo 626299 1413917 := bbase (se 3 (by rfl) ⟨265109, by rfl⟩ : syracuseStep 1413917 = 530219) (by norm_num)
theorem B2265893 : Blo 626299 2265893 := bbase (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) (by norm_num)
theorem B1413989 : Blo 626299 1413989 := bbase (se 4 (by rfl) ⟨132561, by rfl⟩ : syracuseStep 1413989 = 265123) (by norm_num)
theorem B3183461 : Blo 626299 3183461 := bbase (se 4 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 3183461 = 596899) (by norm_num)
theorem B1414061 : Blo 626299 1414061 := bbase (se 3 (by rfl) ⟨265136, by rfl⟩ : syracuseStep 1414061 = 530273) (by norm_num)
theorem B1414133 : Blo 626299 1414133 := bbase (se 5 (by rfl) ⟨66287, by rfl⟩ : syracuseStep 1414133 = 132575) (by norm_num)
theorem B1610813 : Blo 626299 1610813 := bbase (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) (by norm_num)
theorem B1414205 : Blo 626299 1414205 := bbase (se 3 (by rfl) ⟨265163, by rfl⟩ : syracuseStep 1414205 = 530327) (by norm_num)
theorem B2266181 : Blo 626299 2266181 := bbase (se 4 (by rfl) ⟨212454, by rfl⟩ : syracuseStep 2266181 = 424909) (by norm_num)
theorem B1414277 : Blo 626299 1414277 := bbase (se 4 (by rfl) ⟨132588, by rfl⟩ : syracuseStep 1414277 = 265177) (by norm_num)
theorem B1414349 : Blo 626299 1414349 := bbase (se 3 (by rfl) ⟨265190, by rfl⟩ : syracuseStep 1414349 = 530381) (by norm_num)
theorem B1414421 : Blo 626299 1414421 := bbase (se 6 (by rfl) ⟨33150, by rfl⟩ : syracuseStep 1414421 = 66301) (by norm_num)
theorem B955741 : Blo 626299 955741 := bbase (se 3 (by rfl) ⟨179201, by rfl⟩ : syracuseStep 955741 = 358403) (by norm_num)
theorem B1414493 : Blo 626299 1414493 := bbase (se 3 (by rfl) ⟨265217, by rfl⟩ : syracuseStep 1414493 = 530435) (by norm_num)
theorem B1414565 : Blo 626299 1414565 := bbase (se 4 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 1414565 = 265231) (by norm_num)
theorem B1414637 : Blo 626299 1414637 := bbase (se 3 (by rfl) ⟨265244, by rfl⟩ : syracuseStep 1414637 = 530489) (by norm_num)
theorem B2266613 : Blo 626299 2266613 := bbase (se 5 (by rfl) ⟨106247, by rfl⟩ : syracuseStep 2266613 = 212495) (by norm_num)
theorem B1414709 : Blo 626299 1414709 := bbase (se 5 (by rfl) ⟨66314, by rfl⟩ : syracuseStep 1414709 = 132629) (by norm_num)
theorem B1414781 : Blo 626299 1414781 := bbase (se 3 (by rfl) ⟨265271, by rfl⟩ : syracuseStep 1414781 = 530543) (by norm_num)
theorem B726661 : Blo 626299 726661 := bbase (se 4 (by rfl) ⟨68124, by rfl⟩ : syracuseStep 726661 = 136249) (by norm_num)
theorem B1513093 : Blo 626299 1513093 := bbase (se 4 (by rfl) ⟨141852, by rfl⟩ : syracuseStep 1513093 = 283705) (by norm_num)
theorem B1414853 : Blo 626299 1414853 := bbase (se 4 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 1414853 = 265285) (by norm_num)
theorem B1414925 : Blo 626299 1414925 := bbase (se 3 (by rfl) ⟨265298, by rfl⟩ : syracuseStep 1414925 = 530597) (by norm_num)
theorem B1414997 : Blo 626299 1414997 := bbase (se 9 (by rfl) ⟨4145, by rfl⟩ : syracuseStep 1414997 = 8291) (by norm_num)
theorem B1415069 : Blo 626299 1415069 := bbase (se 3 (by rfl) ⟨265325, by rfl⟩ : syracuseStep 1415069 = 530651) (by norm_num)
theorem B1415141 : Blo 626299 1415141 := bbase (se 4 (by rfl) ⟨132669, by rfl⟩ : syracuseStep 1415141 = 265339) (by norm_num)
theorem B1415213 : Blo 626299 1415213 := bbase (se 3 (by rfl) ⟨265352, by rfl⟩ : syracuseStep 1415213 = 530705) (by norm_num)
theorem B792661 : Blo 626299 792661 := bbase (se 8 (by rfl) ⟨4644, by rfl⟩ : syracuseStep 792661 = 9289) (by norm_num)
theorem B25860181 : Blo 626299 25860181 := bbase (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) (by norm_num)
theorem B6035573 : Blo 626299 6035573 := bbase (se 5 (by rfl) ⟨282917, by rfl⟩ : syracuseStep 6035573 = 565835) (by norm_num)
theorem B1415285 : Blo 626299 1415285 := bbase (se 5 (by rfl) ⟨66341, by rfl⟩ : syracuseStep 1415285 = 132683) (by norm_num)
theorem B3184757 : Blo 626299 3184757 := bbase (se 5 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 3184757 = 298571) (by norm_num)
theorem B792757 : Blo 626299 792757 := bbase (se 5 (by rfl) ⟨37160, by rfl⟩ : syracuseStep 792757 = 74321) (by norm_num)
theorem B1415357 : Blo 626299 1415357 := bbase (se 3 (by rfl) ⟨265379, by rfl⟩ : syracuseStep 1415357 = 530759) (by norm_num)
theorem B1415429 : Blo 626299 1415429 := bbase (se 4 (by rfl) ⟨132696, by rfl⟩ : syracuseStep 1415429 = 265393) (by norm_num)
theorem B1415501 : Blo 626299 1415501 := bbase (se 3 (by rfl) ⟨265406, by rfl⟩ : syracuseStep 1415501 = 530813) (by norm_num)
theorem B2857301 : Blo 626299 2857301 := bbase (se 10 (by rfl) ⟨4185, by rfl⟩ : syracuseStep 2857301 = 8371) (by norm_num)
theorem B792929 : Blo 626299 792929 := bbase (se 2 (by rfl) ⟨297348, by rfl⟩ : syracuseStep 792929 = 594697) (by norm_num)
theorem B1415573 : Blo 626299 1415573 := bbase (se 6 (by rfl) ⟨33177, by rfl⟩ : syracuseStep 1415573 = 66355) (by norm_num)
theorem B792985 : Blo 626299 792985 := bbase (se 2 (by rfl) ⟨297369, by rfl⟩ : syracuseStep 792985 = 594739) (by norm_num)
theorem B1415645 : Blo 626299 1415645 := bbase (se 3 (by rfl) ⟨265433, by rfl⟩ : syracuseStep 1415645 = 530867) (by norm_num)
theorem B793081 : Blo 626299 793081 := bbase (se 2 (by rfl) ⟨297405, by rfl⟩ : syracuseStep 793081 = 594811) (by norm_num)
theorem B1415717 : Blo 626299 1415717 := bbase (se 4 (by rfl) ⟨132723, by rfl⟩ : syracuseStep 1415717 = 265447) (by norm_num)
theorem B1415789 : Blo 626299 1415789 := bbase (se 3 (by rfl) ⟨265460, by rfl⟩ : syracuseStep 1415789 = 530921) (by norm_num)
theorem B793253 : Blo 626299 793253 := bbase (se 4 (by rfl) ⟨74367, by rfl⟩ : syracuseStep 793253 = 148735) (by norm_num)
theorem B1415861 : Blo 626299 1415861 := bbase (se 5 (by rfl) ⟨66368, by rfl⟩ : syracuseStep 1415861 = 132737) (by norm_num)
theorem B793309 : Blo 626299 793309 := bbase (se 3 (by rfl) ⟨148745, by rfl⟩ : syracuseStep 793309 = 297491) (by norm_num)
theorem B1415933 : Blo 626299 1415933 := bbase (se 3 (by rfl) ⟨265487, by rfl⟩ : syracuseStep 1415933 = 530975) (by norm_num)
theorem B1022725 : Blo 626299 1022725 := bbase (se 4 (by rfl) ⟨95880, by rfl⟩ : syracuseStep 1022725 = 191761) (by norm_num)
theorem B1514285 : Blo 626299 1514285 := bbase (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) (by norm_num)
theorem B793405 : Blo 626299 793405 := bbase (se 3 (by rfl) ⟨148763, by rfl⟩ : syracuseStep 793405 = 297527) (by norm_num)
theorem B1416005 : Blo 626299 1416005 := bbase (se 4 (by rfl) ⟨132750, by rfl⟩ : syracuseStep 1416005 = 265501) (by norm_num)
theorem B1416077 : Blo 626299 1416077 := bbase (se 3 (by rfl) ⟨265514, by rfl⟩ : syracuseStep 1416077 = 531029) (by norm_num)
theorem B2726837 : Blo 626299 2726837 := bbase (se 5 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 2726837 = 255641) (by norm_num)
theorem B1416149 : Blo 626299 1416149 := bbase (se 7 (by rfl) ⟨16595, by rfl⟩ : syracuseStep 1416149 = 33191) (by norm_num)
theorem B1022933 : Blo 626299 1022933 := bbase (se 7 (by rfl) ⟨11987, by rfl⟩ : syracuseStep 1022933 = 23975) (by norm_num)
theorem B793577 : Blo 626299 793577 := bbase (se 2 (by rfl) ⟨297591, by rfl⟩ : syracuseStep 793577 = 595183) (by norm_num)
theorem B1416221 : Blo 626299 1416221 := bbase (se 3 (by rfl) ⟨265541, by rfl⟩ : syracuseStep 1416221 = 531083) (by norm_num)
theorem B793633 : Blo 626299 793633 := bbase (se 2 (by rfl) ⟨297612, by rfl⟩ : syracuseStep 793633 = 595225) (by norm_num)
theorem B1416293 : Blo 626299 1416293 := bbase (se 4 (by rfl) ⟨132777, by rfl⟩ : syracuseStep 1416293 = 265555) (by norm_num)
theorem B793729 : Blo 626299 793729 := bbase (se 2 (by rfl) ⟨297648, by rfl⟩ : syracuseStep 793729 = 595297) (by norm_num)
theorem B1416365 : Blo 626299 1416365 := bbase (se 3 (by rfl) ⟨265568, by rfl⟩ : syracuseStep 1416365 = 531137) (by norm_num)
theorem B1416437 : Blo 626299 1416437 := bbase (se 5 (by rfl) ⟨66395, by rfl⟩ : syracuseStep 1416437 = 132791) (by norm_num)
theorem B793901 : Blo 626299 793901 := bbase (se 3 (by rfl) ⟨148856, by rfl⟩ : syracuseStep 793901 = 297713) (by norm_num)
theorem B1416509 : Blo 626299 1416509 := bbase (se 3 (by rfl) ⟨265595, by rfl⟩ : syracuseStep 1416509 = 531191) (by norm_num)
theorem B793957 : Blo 626299 793957 := bbase (se 4 (by rfl) ⟨74433, by rfl⟩ : syracuseStep 793957 = 148867) (by norm_num)
theorem B3186053 : Blo 626299 3186053 := bbase (se 4 (by rfl) ⟨298692, by rfl⟩ : syracuseStep 3186053 = 597385) (by norm_num)
theorem B1416581 : Blo 626299 1416581 := bbase (se 4 (by rfl) ⟨132804, by rfl⟩ : syracuseStep 1416581 = 265609) (by norm_num)
theorem B794053 : Blo 626299 794053 := bbase (se 4 (by rfl) ⟨74442, by rfl⟩ : syracuseStep 794053 = 148885) (by norm_num)
theorem B1416653 : Blo 626299 1416653 := bbase (se 3 (by rfl) ⟨265622, by rfl⟩ : syracuseStep 1416653 = 531245) (by norm_num)
theorem B1416725 : Blo 626299 1416725 := bbase (se 6 (by rfl) ⟨33204, by rfl⟩ : syracuseStep 1416725 = 66409) (by norm_num)
theorem B1416797 : Blo 626299 1416797 := bbase (se 3 (by rfl) ⟨265649, by rfl⟩ : syracuseStep 1416797 = 531299) (by norm_num)
theorem B794225 : Blo 626299 794225 := bbase (se 2 (by rfl) ⟨297834, by rfl⟩ : syracuseStep 794225 = 595669) (by norm_num)
theorem B1416869 : Blo 626299 1416869 := bbase (se 4 (by rfl) ⟨132831, by rfl⟩ : syracuseStep 1416869 = 265663) (by norm_num)
theorem B794281 : Blo 626299 794281 := bbase (se 2 (by rfl) ⟨297855, by rfl⟩ : syracuseStep 794281 = 595711) (by norm_num)
theorem B958157 : Blo 626299 958157 := bbase (se 3 (by rfl) ⟨179654, by rfl⟩ : syracuseStep 958157 = 359309) (by norm_num)
theorem B1416941 : Blo 626299 1416941 := bbase (se 3 (by rfl) ⟨265676, by rfl⟩ : syracuseStep 1416941 = 531353) (by norm_num)
theorem B794377 : Blo 626299 794377 := bbase (se 2 (by rfl) ⟨297891, by rfl⟩ : syracuseStep 794377 = 595783) (by norm_num)
theorem B1417013 : Blo 626299 1417013 := bbase (se 5 (by rfl) ⟨66422, by rfl⟩ : syracuseStep 1417013 = 132845) (by norm_num)
theorem B1417085 : Blo 626299 1417085 := bbase (se 3 (by rfl) ⟨265703, by rfl⟩ : syracuseStep 1417085 = 531407) (by norm_num)
theorem B794549 : Blo 626299 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B1417157 : Blo 626299 1417157 := bbase (se 4 (by rfl) ⟨132858, by rfl⟩ : syracuseStep 1417157 = 265717) (by norm_num)
theorem B16981973 : Blo 626299 16981973 := bbase (se 7 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 16981973 = 398015) (by norm_num)
theorem B794605 : Blo 626299 794605 := bbase (se 3 (by rfl) ⟨148988, by rfl⟩ : syracuseStep 794605 = 297977) (by norm_num)
theorem B1417229 : Blo 626299 1417229 := bbase (se 3 (by rfl) ⟨265730, by rfl⟩ : syracuseStep 1417229 = 531461) (by norm_num)
theorem B892957 : Blo 626299 892957 := bbase (se 3 (by rfl) ⟨167429, by rfl⟩ : syracuseStep 892957 = 334859) (by norm_num)
theorem B794701 : Blo 626299 794701 := bbase (se 3 (by rfl) ⟨149006, by rfl⟩ : syracuseStep 794701 = 298013) (by norm_num)
theorem B39297109 : Blo 626299 39297109 := bbase (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) (by norm_num)
theorem B1417301 : Blo 626299 1417301 := bbase (se 8 (by rfl) ⟨8304, by rfl⟩ : syracuseStep 1417301 = 16609) (by norm_num)
theorem B1548389 : Blo 626299 1548389 := bbase (se 4 (by rfl) ⟨145161, by rfl⟩ : syracuseStep 1548389 = 290323) (by norm_num)
theorem B1056901 : Blo 626299 1056901 := bbase (se 4 (by rfl) ⟨99084, by rfl⟩ : syracuseStep 1056901 = 198169) (by norm_num)
theorem B1417373 : Blo 626299 1417373 := bbase (se 3 (by rfl) ⟨265757, by rfl⟩ : syracuseStep 1417373 = 531515) (by norm_num)
theorem B1056989 : Blo 626299 1056989 := bbase (se 3 (by rfl) ⟨198185, by rfl⟩ : syracuseStep 1056989 = 396371) (by norm_num)
theorem B1417445 : Blo 626299 1417445 := bbase (se 4 (by rfl) ⟨132885, by rfl⟩ : syracuseStep 1417445 = 265771) (by norm_num)
theorem B794873 : Blo 626299 794873 := bbase (se 2 (by rfl) ⟨298077, by rfl⟩ : syracuseStep 794873 = 596155) (by norm_num)
theorem B1417517 : Blo 626299 1417517 := bbase (se 3 (by rfl) ⟨265784, by rfl⟩ : syracuseStep 1417517 = 531569) (by norm_num)
theorem B794929 : Blo 626299 794929 := bbase (se 2 (by rfl) ⟨298098, by rfl⟩ : syracuseStep 794929 = 596197) (by norm_num)
theorem B1057117 : Blo 626299 1057117 := bbase (se 3 (by rfl) ⟨198209, by rfl⟩ : syracuseStep 1057117 = 396419) (by norm_num)
theorem B1417589 : Blo 626299 1417589 := bbase (se 5 (by rfl) ⟨66449, by rfl⟩ : syracuseStep 1417589 = 132899) (by norm_num)
theorem B795025 : Blo 626299 795025 := bbase (se 2 (by rfl) ⟨298134, by rfl⟩ : syracuseStep 795025 = 596269) (by norm_num)
theorem B2007461 : Blo 626299 2007461 := bbase (se 4 (by rfl) ⟨188199, by rfl⟩ : syracuseStep 2007461 = 376399) (by norm_num)
theorem B1057205 : Blo 626299 1057205 := bbase (se 5 (by rfl) ⟨49556, by rfl⟩ : syracuseStep 1057205 = 99113) (by norm_num)
theorem B1417661 : Blo 626299 1417661 := bbase (se 3 (by rfl) ⟨265811, by rfl⟩ : syracuseStep 1417661 = 531623) (by norm_num)
theorem B1417733 : Blo 626299 1417733 := bbase (se 4 (by rfl) ⟨132912, by rfl⟩ : syracuseStep 1417733 = 265825) (by norm_num)
theorem B1057333 : Blo 626299 1057333 := bbase (se 5 (by rfl) ⟨49562, by rfl⟩ : syracuseStep 1057333 = 99125) (by norm_num)
theorem B795197 : Blo 626299 795197 := bbase (se 3 (by rfl) ⟨149099, by rfl⟩ : syracuseStep 795197 = 298199) (by norm_num)
theorem B1450565 : Blo 626299 1450565 := bbase (se 4 (by rfl) ⟨135990, by rfl⟩ : syracuseStep 1450565 = 271981) (by norm_num)
theorem B1417805 : Blo 626299 1417805 := bbase (se 3 (by rfl) ⟨265838, by rfl⟩ : syracuseStep 1417805 = 531677) (by norm_num)
theorem B893549 : Blo 626299 893549 := bbase (se 3 (by rfl) ⟨167540, by rfl⟩ : syracuseStep 893549 = 335081) (by norm_num)
theorem B795253 : Blo 626299 795253 := bbase (se 5 (by rfl) ⟨37277, by rfl⟩ : syracuseStep 795253 = 74555) (by norm_num)
theorem B1057421 : Blo 626299 1057421 := bbase (se 3 (by rfl) ⟨198266, by rfl⟩ : syracuseStep 1057421 = 396533) (by norm_num)
theorem B3187349 : Blo 626299 3187349 := bbase (se 6 (by rfl) ⟨74703, by rfl⟩ : syracuseStep 3187349 = 149407) (by norm_num)
theorem B1417877 : Blo 626299 1417877 := bbase (se 6 (by rfl) ⟨33231, by rfl⟩ : syracuseStep 1417877 = 66463) (by norm_num)
theorem B893629 : Blo 626299 893629 := bbase (se 3 (by rfl) ⟨167555, by rfl⟩ : syracuseStep 893629 = 335111) (by norm_num)
theorem B795349 : Blo 626299 795349 := bbase (se 7 (by rfl) ⟨9320, by rfl⟩ : syracuseStep 795349 = 18641) (by norm_num)
theorem B1417949 : Blo 626299 1417949 := bbase (se 3 (by rfl) ⟨265865, by rfl⟩ : syracuseStep 1417949 = 531731) (by norm_num)
theorem B1057549 : Blo 626299 1057549 := bbase (se 3 (by rfl) ⟨198290, by rfl⟩ : syracuseStep 1057549 = 396581) (by norm_num)
theorem B1418021 : Blo 626299 1418021 := bbase (se 4 (by rfl) ⟨132939, by rfl⟩ : syracuseStep 1418021 = 265879) (by norm_num)
theorem B893749 : Blo 626299 893749 := bbase (se 5 (by rfl) ⟨41894, by rfl⟩ : syracuseStep 893749 = 83789) (by norm_num)
theorem B3580757 : Blo 626299 3580757 := bbase (se 9 (by rfl) ⟨10490, by rfl⟩ : syracuseStep 3580757 = 20981) (by norm_num)
theorem B1057637 : Blo 626299 1057637 := bbase (se 4 (by rfl) ⟨99153, by rfl⟩ : syracuseStep 1057637 = 198307) (by norm_num)
theorem B1418093 : Blo 626299 1418093 := bbase (se 3 (by rfl) ⟨265892, by rfl⟩ : syracuseStep 1418093 = 531785) (by norm_num)
theorem B795521 : Blo 626299 795521 := bbase (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) (by norm_num)
theorem B893845 : Blo 626299 893845 := bbase (se 6 (by rfl) ⟨20949, by rfl⟩ : syracuseStep 893845 = 41899) (by norm_num)
theorem B3449749 : Blo 626299 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B2270101 : Blo 626299 2270101 := bbase (se 6 (by rfl) ⟨53205, by rfl⟩ : syracuseStep 2270101 = 106411) (by norm_num)
theorem B1418165 : Blo 626299 1418165 := bbase (se 5 (by rfl) ⟨66476, by rfl⟩ : syracuseStep 1418165 = 132953) (by norm_num)
theorem B795577 : Blo 626299 795577 := bbase (se 2 (by rfl) ⟨298341, by rfl⟩ : syracuseStep 795577 = 596683) (by norm_num)
theorem B1057765 : Blo 626299 1057765 := bbase (se 4 (by rfl) ⟨99165, by rfl⟩ : syracuseStep 1057765 = 198331) (by norm_num)
theorem B2040805 : Blo 626299 2040805 := bbase (se 4 (by rfl) ⟨191325, by rfl⟩ : syracuseStep 2040805 = 382651) (by norm_num)
theorem B795673 : Blo 626299 795673 := bbase (se 2 (by rfl) ⟨298377, by rfl⟩ : syracuseStep 795673 = 596755) (by norm_num)
theorem B2270261 : Blo 626299 2270261 := bbase (se 5 (by rfl) ⟨106418, by rfl⟩ : syracuseStep 2270261 = 212837) (by norm_num)
theorem B1057853 : Blo 626299 1057853 := bbase (se 3 (by rfl) ⟨198347, by rfl⟩ : syracuseStep 1057853 = 396695) (by norm_num)
theorem B762949 : Blo 626299 762949 := bbase (se 4 (by rfl) ⟨71526, by rfl⟩ : syracuseStep 762949 = 143053) (by norm_num)
theorem B2270389 : Blo 626299 2270389 := bbase (se 5 (by rfl) ⟨106424, by rfl⟩ : syracuseStep 2270389 = 212849) (by norm_num)
theorem B1057981 : Blo 626299 1057981 := bbase (se 3 (by rfl) ⟨198371, by rfl⟩ : syracuseStep 1057981 = 396743) (by norm_num)
theorem B795845 : Blo 626299 795845 := bbase (se 4 (by rfl) ⟨74610, by rfl⟩ : syracuseStep 795845 = 149221) (by norm_num)
theorem B9086165 : Blo 626299 9086165 := bbase (se 7 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 9086165 = 212957) (by norm_num)
theorem B795901 : Blo 626299 795901 := bbase (se 3 (by rfl) ⟨149231, by rfl⟩ : syracuseStep 795901 = 298463) (by norm_num)
theorem B1058069 : Blo 626299 1058069 := bbase (se 6 (by rfl) ⟨24798, by rfl⟩ : syracuseStep 1058069 = 49597) (by norm_num)
theorem B1615133 : Blo 626299 1615133 := bbase (se 3 (by rfl) ⟨302837, by rfl⟩ : syracuseStep 1615133 = 605675) (by norm_num)
theorem B1189181 : Blo 626299 1189181 := bbase (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) (by norm_num)
theorem B795997 : Blo 626299 795997 := bbase (se 3 (by rfl) ⟨149249, by rfl⟩ : syracuseStep 795997 = 298499) (by norm_num)
theorem B894341 : Blo 626299 894341 := bbase (se 4 (by rfl) ⟨83844, by rfl⟩ : syracuseStep 894341 = 167689) (by norm_num)
theorem B1058197 : Blo 626299 1058197 := bbase (se 6 (by rfl) ⟨24801, by rfl⟩ : syracuseStep 1058197 = 49603) (by norm_num)
theorem B1189333 : Blo 626299 1189333 := bbase (se 7 (by rfl) ⟨13937, by rfl⟩ : syracuseStep 1189333 = 27875) (by norm_num)
theorem B3024341 : Blo 626299 3024341 := bbase (se 7 (by rfl) ⟨35441, by rfl⟩ : syracuseStep 3024341 = 70883) (by norm_num)
theorem B1058285 : Blo 626299 1058285 := bbase (se 3 (by rfl) ⟨198428, by rfl⟩ : syracuseStep 1058285 = 396857) (by norm_num)
theorem B796169 : Blo 626299 796169 := bbase (se 2 (by rfl) ⟨298563, by rfl⟩ : syracuseStep 796169 = 597127) (by norm_num)
theorem B796225 : Blo 626299 796225 := bbase (se 2 (by rfl) ⟨298584, by rfl⟩ : syracuseStep 796225 = 597169) (by norm_num)
theorem B1222229 : Blo 626299 1222229 := bbase (se 8 (by rfl) ⟨7161, by rfl⟩ : syracuseStep 1222229 = 14323) (by norm_num)
theorem B1058413 : Blo 626299 1058413 := bbase (se 3 (by rfl) ⟨198452, by rfl⟩ : syracuseStep 1058413 = 396905) (by norm_num)
theorem B763537 : Blo 626299 763537 := bbase (se 2 (by rfl) ⟨286326, by rfl⟩ : syracuseStep 763537 = 572653) (by norm_num)
theorem B796321 : Blo 626299 796321 := bbase (se 2 (by rfl) ⟨298620, by rfl⟩ : syracuseStep 796321 = 597241) (by norm_num)
theorem B1058501 : Blo 626299 1058501 := bbase (se 4 (by rfl) ⟨99234, by rfl⟩ : syracuseStep 1058501 = 198469) (by norm_num)
theorem B1189637 : Blo 626299 1189637 := bbase (se 4 (by rfl) ⟨111528, by rfl⟩ : syracuseStep 1189637 = 223057) (by norm_num)
theorem B1910533 : Blo 626299 1910533 := bbase (se 4 (by rfl) ⟨179112, by rfl⟩ : syracuseStep 1910533 = 358225) (by norm_num)
theorem B4073237 : Blo 626299 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B1058629 : Blo 626299 1058629 := bbase (se 4 (by rfl) ⟨99246, by rfl⟩ : syracuseStep 1058629 = 198493) (by norm_num)
theorem B796493 : Blo 626299 796493 := bbase (se 3 (by rfl) ⟨149342, by rfl⟩ : syracuseStep 796493 = 298685) (by norm_num)
theorem B796549 : Blo 626299 796549 := bbase (se 4 (by rfl) ⟨74676, by rfl⟩ : syracuseStep 796549 = 149353) (by norm_num)
theorem B1058717 : Blo 626299 1058717 := bbase (se 3 (by rfl) ⟨198509, by rfl⟩ : syracuseStep 1058717 = 397019) (by norm_num)
theorem B3188645 : Blo 626299 3188645 := bbase (se 4 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 3188645 = 597871) (by norm_num)
theorem B894893 : Blo 626299 894893 := bbase (se 3 (by rfl) ⟨167792, by rfl⟩ : syracuseStep 894893 = 335585) (by norm_num)
theorem B796645 : Blo 626299 796645 := bbase (se 4 (by rfl) ⟨74685, by rfl⟩ : syracuseStep 796645 = 149371) (by norm_num)
theorem B3581941 : Blo 626299 3581941 := bbase (se 5 (by rfl) ⟨167903, by rfl⟩ : syracuseStep 3581941 = 335807) (by norm_num)
theorem B1058845 : Blo 626299 1058845 := bbase (se 3 (by rfl) ⟨198533, by rfl⟩ : syracuseStep 1058845 = 397067) (by norm_num)
theorem B1058933 : Blo 626299 1058933 := bbase (se 5 (by rfl) ⟨49637, by rfl⟩ : syracuseStep 1058933 = 99275) (by norm_num)
theorem B796817 : Blo 626299 796817 := bbase (se 2 (by rfl) ⟨298806, by rfl⟩ : syracuseStep 796817 = 597613) (by norm_num)
theorem B796873 : Blo 626299 796873 := bbase (se 2 (by rfl) ⟨298827, by rfl⟩ : syracuseStep 796873 = 597655) (by norm_num)
theorem B1059061 : Blo 626299 1059061 := bbase (se 5 (by rfl) ⟨49643, by rfl⟩ : syracuseStep 1059061 = 99287) (by norm_num)
theorem B796969 : Blo 626299 796969 := bbase (se 2 (by rfl) ⟨298863, by rfl⟩ : syracuseStep 796969 = 597727) (by norm_num)
theorem B1059149 : Blo 626299 1059149 := bbase (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) (by norm_num)
theorem B2009461 : Blo 626299 2009461 := bbase (se 5 (by rfl) ⟨94193, by rfl⟩ : syracuseStep 2009461 = 188387) (by norm_num)
theorem B1059277 : Blo 626299 1059277 := bbase (se 3 (by rfl) ⟨198614, by rfl⟩ : syracuseStep 1059277 = 397229) (by norm_num)
theorem B797141 : Blo 626299 797141 := bbase (se 7 (by rfl) ⟨9341, by rfl⟩ : syracuseStep 797141 = 18683) (by norm_num)
theorem B1190389 : Blo 626299 1190389 := bbase (se 5 (by rfl) ⟨55799, by rfl⟩ : syracuseStep 1190389 = 111599) (by norm_num)
theorem B797197 : Blo 626299 797197 := bbase (se 3 (by rfl) ⟨149474, by rfl⟩ : syracuseStep 797197 = 298949) (by norm_num)
theorem B1059365 : Blo 626299 1059365 := bbase (se 4 (by rfl) ⟨99315, by rfl⟩ : syracuseStep 1059365 = 198631) (by norm_num)
theorem B797293 : Blo 626299 797293 := bbase (se 3 (by rfl) ⟨149492, by rfl⟩ : syracuseStep 797293 = 298985) (by norm_num)
theorem B1190533 : Blo 626299 1190533 := bbase (se 4 (by rfl) ⟨111612, by rfl⟩ : syracuseStep 1190533 = 223225) (by norm_num)
theorem B895645 : Blo 626299 895645 := bbase (se 3 (by rfl) ⟨167933, by rfl⟩ : syracuseStep 895645 = 335867) (by norm_num)
theorem B1059493 : Blo 626299 1059493 := bbase (se 4 (by rfl) ⟨99327, by rfl⟩ : syracuseStep 1059493 = 198655) (by norm_num)
theorem B1059581 : Blo 626299 1059581 := bbase (se 3 (by rfl) ⟨198671, by rfl⟩ : syracuseStep 1059581 = 397343) (by norm_num)
theorem B797465 : Blo 626299 797465 := bbase (se 2 (by rfl) ⟨299049, by rfl⟩ : syracuseStep 797465 = 598099) (by norm_num)
theorem B1190693 : Blo 626299 1190693 := bbase (se 4 (by rfl) ⟨111627, by rfl⟩ : syracuseStep 1190693 = 223255) (by norm_num)
theorem B797521 : Blo 626299 797521 := bbase (se 2 (by rfl) ⟨299070, by rfl⟩ : syracuseStep 797521 = 598141) (by norm_num)
theorem B1059709 : Blo 626299 1059709 := bbase (se 3 (by rfl) ⟨198695, by rfl⟩ : syracuseStep 1059709 = 397391) (by norm_num)
theorem B797617 : Blo 626299 797617 := bbase (se 2 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 797617 = 598213) (by norm_num)
theorem B1190837 : Blo 626299 1190837 := bbase (se 5 (by rfl) ⟨55820, by rfl⟩ : syracuseStep 1190837 = 111641) (by norm_num)
theorem B1059797 : Blo 626299 1059797 := bbase (se 7 (by rfl) ⟨12419, by rfl⟩ : syracuseStep 1059797 = 24839) (by norm_num)
theorem B1059925 : Blo 626299 1059925 := bbase (se 8 (by rfl) ⟨6210, by rfl⟩ : syracuseStep 1059925 = 12421) (by norm_num)
theorem B1060013 : Blo 626299 1060013 := bbase (se 3 (by rfl) ⟨198752, by rfl⟩ : syracuseStep 1060013 = 397505) (by norm_num)
theorem B3189941 : Blo 626299 3189941 := bbase (se 5 (by rfl) ⟨149528, by rfl⟩ : syracuseStep 3189941 = 299057) (by norm_num)
theorem B1191125 : Blo 626299 1191125 := bbase (se 7 (by rfl) ⟨13958, by rfl⟩ : syracuseStep 1191125 = 27917) (by norm_num)
theorem B1060141 : Blo 626299 1060141 := bbase (se 3 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 1060141 = 397553) (by norm_num)
theorem B16100693 : Blo 626299 16100693 := bbase (se 11 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 16100693 = 23585) (by norm_num)
theorem B1191277 : Blo 626299 1191277 := bbase (se 3 (by rfl) ⟨223364, by rfl⟩ : syracuseStep 1191277 = 446729) (by norm_num)
theorem B1060229 : Blo 626299 1060229 := bbase (se 4 (by rfl) ⟨99396, by rfl⟩ : syracuseStep 1060229 = 198793) (by norm_num)
theorem B896437 : Blo 626299 896437 := bbase (se 5 (by rfl) ⟨42020, by rfl⟩ : syracuseStep 896437 = 84041) (by norm_num)
theorem B1912261 : Blo 626299 1912261 := bbase (se 4 (by rfl) ⟨179274, by rfl⟩ : syracuseStep 1912261 = 358549) (by norm_num)
theorem B1060357 : Blo 626299 1060357 := bbase (se 4 (by rfl) ⟨99408, by rfl⟩ : syracuseStep 1060357 = 198817) (by norm_num)
theorem B2862661 : Blo 626299 2862661 := bbase (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) (by norm_num)
theorem B1060445 : Blo 626299 1060445 := bbase (se 3 (by rfl) ⟨198833, by rfl⟩ : syracuseStep 1060445 = 397667) (by norm_num)
theorem B3059333 : Blo 626299 3059333 := bbase (se 4 (by rfl) ⟨286812, by rfl⟩ : syracuseStep 3059333 = 573625) (by norm_num)
theorem B4763285 : Blo 626299 4763285 := bbase (se 6 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 4763285 = 223279) (by norm_num)
theorem B1191581 : Blo 626299 1191581 := bbase (se 3 (by rfl) ⟨223421, by rfl⟩ : syracuseStep 1191581 = 446843) (by norm_num)
theorem B1060573 : Blo 626299 1060573 := bbase (se 3 (by rfl) ⟨198857, by rfl⟩ : syracuseStep 1060573 = 397715) (by norm_num)
theorem B1289981 : Blo 626299 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B896773 : Blo 626299 896773 := bbase (se 4 (by rfl) ⟨84072, by rfl⟩ : syracuseStep 896773 = 168145) (by norm_num)
theorem B1060661 : Blo 626299 1060661 := bbase (se 5 (by rfl) ⟨49718, by rfl⟩ : syracuseStep 1060661 = 99437) (by norm_num)
theorem B1060789 : Blo 626299 1060789 := bbase (se 5 (by rfl) ⟨49724, by rfl⟩ : syracuseStep 1060789 = 99449) (by norm_num)
theorem B3583925 : Blo 626299 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B896989 : Blo 626299 896989 := bbase (se 3 (by rfl) ⟨168185, by rfl⟩ : syracuseStep 896989 = 336371) (by norm_num)
theorem B1060877 : Blo 626299 1060877 := bbase (se 3 (by rfl) ⟨198914, by rfl⟩ : syracuseStep 1060877 = 397829) (by norm_num)
theorem B1061005 : Blo 626299 1061005 := bbase (se 3 (by rfl) ⟨198938, by rfl⟩ : syracuseStep 1061005 = 397877) (by norm_num)
theorem B1061093 : Blo 626299 1061093 := bbase (se 4 (by rfl) ⟨99477, by rfl⟩ : syracuseStep 1061093 = 198955) (by norm_num)
theorem B1585453 : Blo 626299 1585453 := bbase (se 3 (by rfl) ⟨297272, by rfl⟩ : syracuseStep 1585453 = 594545) (by norm_num)
theorem B897365 : Blo 626299 897365 := bbase (se 10 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 897365 = 2629) (by norm_num)
theorem B1061221 : Blo 626299 1061221 := bbase (se 4 (by rfl) ⟨99489, by rfl⟩ : syracuseStep 1061221 = 198979) (by norm_num)
theorem B1192333 : Blo 626299 1192333 := bbase (se 3 (by rfl) ⟨223562, by rfl⟩ : syracuseStep 1192333 = 447125) (by norm_num)
theorem B1585565 : Blo 626299 1585565 := bbase (se 3 (by rfl) ⟨297293, by rfl⟩ : syracuseStep 1585565 = 594587) (by norm_num)
theorem B1061309 : Blo 626299 1061309 := bbase (se 3 (by rfl) ⟨198995, by rfl⟩ : syracuseStep 1061309 = 397991) (by norm_num)
theorem B1192477 : Blo 626299 1192477 := bbase (se 3 (by rfl) ⟨223589, by rfl⟩ : syracuseStep 1192477 = 447179) (by norm_num)
theorem B1061437 : Blo 626299 1061437 := bbase (se 3 (by rfl) ⟨199019, by rfl⟩ : syracuseStep 1061437 = 398039) (by norm_num)
theorem B1585757 : Blo 626299 1585757 := bbase (se 3 (by rfl) ⟨297329, by rfl⟩ : syracuseStep 1585757 = 594659) (by norm_num)
theorem B1061525 : Blo 626299 1061525 := bbase (se 6 (by rfl) ⟨24879, by rfl⟩ : syracuseStep 1061525 = 49759) (by norm_num)
theorem B1192637 : Blo 626299 1192637 := bbase (se 3 (by rfl) ⟨223619, by rfl⟩ : syracuseStep 1192637 = 447239) (by norm_num)
theorem B1061653 : Blo 626299 1061653 := bbase (se 6 (by rfl) ⟨24882, by rfl⟩ : syracuseStep 1061653 = 49765) (by norm_num)
theorem B1192781 : Blo 626299 1192781 := bbase (se 3 (by rfl) ⟨223646, by rfl⟩ : syracuseStep 1192781 = 447293) (by norm_num)
theorem B1061741 : Blo 626299 1061741 := bbase (se 3 (by rfl) ⟨199076, by rfl⟩ : syracuseStep 1061741 = 398153) (by norm_num)
theorem B1586101 : Blo 626299 1586101 := bbase (se 5 (by rfl) ⟨74348, by rfl⟩ : syracuseStep 1586101 = 148697) (by norm_num)
theorem B1061869 : Blo 626299 1061869 := bbase (se 3 (by rfl) ⟨199100, by rfl⟩ : syracuseStep 1061869 = 398201) (by norm_num)
theorem B1586213 : Blo 626299 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B635969 : Blo 626299 635969 := bbase (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) (by norm_num)
theorem B1061957 : Blo 626299 1061957 := bbase (se 4 (by rfl) ⟨99558, by rfl⟩ : syracuseStep 1061957 = 199117) (by norm_num)
theorem B1193069 : Blo 626299 1193069 := bbase (se 3 (by rfl) ⟨223700, by rfl⟩ : syracuseStep 1193069 = 447401) (by norm_num)
theorem B1062085 : Blo 626299 1062085 := bbase (se 4 (by rfl) ⟨99570, by rfl⟩ : syracuseStep 1062085 = 199141) (by norm_num)
theorem B1586405 : Blo 626299 1586405 := bbase (se 4 (by rfl) ⟨148725, by rfl⟩ : syracuseStep 1586405 = 297451) (by norm_num)
theorem B1291493 : Blo 626299 1291493 := bbase (se 4 (by rfl) ⟨121077, by rfl⟩ : syracuseStep 1291493 = 242155) (by norm_num)
theorem B1193221 : Blo 626299 1193221 := bbase (se 4 (by rfl) ⟨111864, by rfl⟩ : syracuseStep 1193221 = 223729) (by norm_num)
theorem B668945 : Blo 626299 668945 := bbase (se 2 (by rfl) ⟨250854, by rfl⟩ : syracuseStep 668945 = 501709) (by norm_num)
theorem B1062173 : Blo 626299 1062173 := bbase (se 3 (by rfl) ⟨199157, by rfl⟩ : syracuseStep 1062173 = 398315) (by norm_num)
theorem B3028261 : Blo 626299 3028261 := bbase (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) (by norm_num)
theorem B2012485 : Blo 626299 2012485 := bbase (se 4 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 2012485 = 377341) (by norm_num)
theorem B669017 : Blo 626299 669017 := bbase (se 2 (by rfl) ⟨250881, by rfl⟩ : syracuseStep 669017 = 501763) (by norm_num)
theorem B5354869 : Blo 626299 5354869 := bbase (se 5 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 5354869 = 502019) (by norm_num)
theorem B636305 : Blo 626299 636305 := bbase (se 2 (by rfl) ⟨238614, by rfl⟩ : syracuseStep 636305 = 477229) (by norm_num)
theorem B1062301 : Blo 626299 1062301 := bbase (se 3 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 1062301 = 398363) (by norm_num)
theorem B1062389 : Blo 626299 1062389 := bbase (se 5 (by rfl) ⟨49799, by rfl⟩ : syracuseStep 1062389 = 99599) (by norm_num)
theorem B669205 : Blo 626299 669205 := bbase (se 6 (by rfl) ⟨15684, by rfl⟩ : syracuseStep 669205 = 31369) (by norm_num)
theorem B1193525 : Blo 626299 1193525 := bbase (se 5 (by rfl) ⟨55946, by rfl⟩ : syracuseStep 1193525 = 111893) (by norm_num)
theorem B1586749 : Blo 626299 1586749 := bbase (se 3 (by rfl) ⟨297515, by rfl⟩ : syracuseStep 1586749 = 595031) (by norm_num)
theorem B1062517 : Blo 626299 1062517 := bbase (se 5 (by rfl) ⟨49805, by rfl⟩ : syracuseStep 1062517 = 99611) (by norm_num)
theorem B1586861 : Blo 626299 1586861 := bbase (se 3 (by rfl) ⟨297536, by rfl⟩ : syracuseStep 1586861 = 595073) (by norm_num)
theorem B669389 : Blo 626299 669389 := bbase (se 3 (by rfl) ⟨125510, by rfl⟩ : syracuseStep 669389 = 251021) (by norm_num)
theorem B1062605 : Blo 626299 1062605 := bbase (se 3 (by rfl) ⟨199238, by rfl⟩ : syracuseStep 1062605 = 398477) (by norm_num)
theorem B1062733 : Blo 626299 1062733 := bbase (se 3 (by rfl) ⟨199262, by rfl⟩ : syracuseStep 1062733 = 398525) (by norm_num)
theorem B1587053 : Blo 626299 1587053 := bbase (se 3 (by rfl) ⟨297572, by rfl⟩ : syracuseStep 1587053 = 595145) (by norm_num)
theorem B1062821 : Blo 626299 1062821 := bbase (se 4 (by rfl) ⟨99639, by rfl⟩ : syracuseStep 1062821 = 199279) (by norm_num)
theorem B1062949 : Blo 626299 1062949 := bbase (se 4 (by rfl) ⟨99651, by rfl⟩ : syracuseStep 1062949 = 199303) (by norm_num)
theorem B3586133 : Blo 626299 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B1063037 : Blo 626299 1063037 := bbase (se 3 (by rfl) ⟨199319, by rfl⟩ : syracuseStep 1063037 = 398639) (by norm_num)
theorem B1587397 : Blo 626299 1587397 := bbase (se 4 (by rfl) ⟨148818, by rfl⟩ : syracuseStep 1587397 = 297637) (by norm_num)
theorem B2865365 : Blo 626299 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B1063165 : Blo 626299 1063165 := bbase (se 3 (by rfl) ⟨199343, by rfl⟩ : syracuseStep 1063165 = 398687) (by norm_num)
theorem B1784069 : Blo 626299 1784069 := bbase (se 4 (by rfl) ⟨167256, by rfl⟩ : syracuseStep 1784069 = 334513) (by norm_num)
theorem B1358093 : Blo 626299 1358093 := bbase (se 3 (by rfl) ⟨254642, by rfl⟩ : syracuseStep 1358093 = 509285) (by norm_num)
theorem B1194277 : Blo 626299 1194277 := bbase (se 4 (by rfl) ⟨111963, by rfl⟩ : syracuseStep 1194277 = 223927) (by norm_num)
theorem B1587509 : Blo 626299 1587509 := bbase (se 5 (by rfl) ⟨74414, by rfl⟩ : syracuseStep 1587509 = 148829) (by norm_num)
theorem B36256085 : Blo 626299 36256085 := bbase (se 10 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 36256085 = 106219) (by norm_num)
theorem B1063253 : Blo 626299 1063253 := bbase (se 10 (by rfl) ⟨1557, by rfl⟩ : syracuseStep 1063253 = 3115) (by norm_num)
theorem B1194421 : Blo 626299 1194421 := bbase (se 5 (by rfl) ⟨55988, by rfl⟩ : syracuseStep 1194421 = 111977) (by norm_num)
theorem B670141 : Blo 626299 670141 := bbase (se 3 (by rfl) ⟨125651, by rfl⟩ : syracuseStep 670141 = 251303) (by norm_num)
theorem B1063381 : Blo 626299 1063381 := bbase (se 7 (by rfl) ⟨12461, by rfl⟩ : syracuseStep 1063381 = 24923) (by norm_num)
theorem B1587701 : Blo 626299 1587701 := bbase (se 5 (by rfl) ⟨74423, by rfl⟩ : syracuseStep 1587701 = 148847) (by norm_num)
theorem B670213 : Blo 626299 670213 := bbase (se 4 (by rfl) ⟨62832, by rfl⟩ : syracuseStep 670213 = 125665) (by norm_num)
theorem B1063469 : Blo 626299 1063469 := bbase (se 3 (by rfl) ⟨199400, by rfl⟩ : syracuseStep 1063469 = 398801) (by norm_num)
theorem B4536917 : Blo 626299 4536917 := bbase (se 8 (by rfl) ⟨26583, by rfl⟩ : syracuseStep 4536917 = 53167) (by norm_num)
theorem B1194581 : Blo 626299 1194581 := bbase (se 8 (by rfl) ⟨6999, by rfl⟩ : syracuseStep 1194581 = 13999) (by norm_num)
theorem B1063597 : Blo 626299 1063597 := bbase (se 3 (by rfl) ⟨199424, by rfl⟩ : syracuseStep 1063597 = 398849) (by norm_num)
theorem B1784501 : Blo 626299 1784501 := bbase (se 5 (by rfl) ⟨83648, by rfl⟩ : syracuseStep 1784501 = 167297) (by norm_num)
theorem B670393 : Blo 626299 670393 := bbase (se 2 (by rfl) ⟨251397, by rfl⟩ : syracuseStep 670393 = 502795) (by norm_num)
theorem B1194725 : Blo 626299 1194725 := bbase (se 4 (by rfl) ⟨112005, by rfl⟩ : syracuseStep 1194725 = 224011) (by norm_num)
theorem B637733 : Blo 626299 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B1588045 : Blo 626299 1588045 := bbase (se 3 (by rfl) ⟨297758, by rfl⟩ : syracuseStep 1588045 = 595517) (by norm_num)
theorem B637801 : Blo 626299 637801 := bbase (se 2 (by rfl) ⟨239175, by rfl⟩ : syracuseStep 637801 = 478351) (by norm_num)
theorem B4537205 : Blo 626299 4537205 := bbase (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) (by norm_num)
theorem B1588157 : Blo 626299 1588157 := bbase (se 3 (by rfl) ⟨297779, by rfl⟩ : syracuseStep 1588157 = 595559) (by norm_num)
theorem B1195013 : Blo 626299 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B4013077 : Blo 626299 4013077 := bbase (se 6 (by rfl) ⟨94056, by rfl⟩ : syracuseStep 4013077 = 188113) (by norm_num)
theorem B670837 : Blo 626299 670837 := bbase (se 5 (by rfl) ⟨31445, by rfl⟩ : syracuseStep 670837 = 62891) (by norm_num)
theorem B1588349 : Blo 626299 1588349 := bbase (se 3 (by rfl) ⟨297815, by rfl⟩ : syracuseStep 1588349 = 595631) (by norm_num)
theorem B1195165 : Blo 626299 1195165 := bbase (se 3 (by rfl) ⟨224093, by rfl⟩ : syracuseStep 1195165 = 448187) (by norm_num)
theorem B670961 : Blo 626299 670961 := bbase (se 2 (by rfl) ⟨251610, by rfl⟩ : syracuseStep 670961 = 503221) (by norm_num)
theorem B1129717 : Blo 626299 1129717 := bbase (se 5 (by rfl) ⟨52955, by rfl⟩ : syracuseStep 1129717 = 105911) (by norm_num)
theorem B5356853 : Blo 626299 5356853 := bbase (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) (by norm_num)
theorem B12041621 : Blo 626299 12041621 := bbase (se 6 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 12041621 = 564451) (by norm_num)
theorem B1785253 : Blo 626299 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B4537781 : Blo 626299 4537781 := bbase (se 5 (by rfl) ⟨212708, by rfl⟩ : syracuseStep 4537781 = 425417) (by norm_num)
theorem B1195469 : Blo 626299 1195469 := bbase (se 3 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 1195469 = 448301) (by norm_num)
theorem B1588693 : Blo 626299 1588693 := bbase (se 7 (by rfl) ⟨18617, by rfl⟩ : syracuseStep 1588693 = 37235) (by norm_num)
theorem B671213 : Blo 626299 671213 := bbase (se 3 (by rfl) ⟨125852, by rfl⟩ : syracuseStep 671213 = 251705) (by norm_num)
theorem B2145781 : Blo 626299 2145781 := bbase (se 5 (by rfl) ⟨100583, by rfl⟩ : syracuseStep 2145781 = 201167) (by norm_num)
theorem B1588805 : Blo 626299 1588805 := bbase (se 4 (by rfl) ⟨148950, by rfl⟩ : syracuseStep 1588805 = 297901) (by norm_num)
theorem B638641 : Blo 626299 638641 := bbase (se 2 (by rfl) ⟨239490, by rfl⟩ : syracuseStep 638641 = 478981) (by norm_num)
theorem B1588997 : Blo 626299 1588997 := bbase (se 4 (by rfl) ⟨148968, by rfl⟩ : syracuseStep 1588997 = 297937) (by norm_num)
theorem B671657 : Blo 626299 671657 := bbase (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) (by norm_num)
theorem B1359893 : Blo 626299 1359893 := bbase (se 6 (by rfl) ⟨31872, by rfl⟩ : syracuseStep 1359893 = 63745) (by norm_num)
theorem B1032229 : Blo 626299 1032229 := bbase (se 4 (by rfl) ⟨96771, by rfl⟩ : syracuseStep 1032229 = 193543) (by norm_num)
theorem B3227701 : Blo 626299 3227701 := bbase (se 5 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 3227701 = 302597) (by norm_num)
theorem B1130581 : Blo 626299 1130581 := bbase (se 8 (by rfl) ⟨6624, by rfl⟩ : syracuseStep 1130581 = 13249) (by norm_num)
theorem B704605 : Blo 626299 704605 := bbase (se 3 (by rfl) ⟨132113, by rfl⟩ : syracuseStep 704605 = 264227) (by norm_num)
theorem B1589341 : Blo 626299 1589341 := bbase (se 3 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 1589341 = 596003) (by norm_num)
theorem B704641 : Blo 626299 704641 := bbase (se 2 (by rfl) ⟨264240, by rfl⟩ : syracuseStep 704641 = 528481) (by norm_num)
theorem B2015381 : Blo 626299 2015381 := bbase (se 6 (by rfl) ⟨47235, by rfl⟩ : syracuseStep 2015381 = 94471) (by norm_num)
theorem B671905 : Blo 626299 671905 := bbase (se 2 (by rfl) ⟨251964, by rfl⟩ : syracuseStep 671905 = 503929) (by norm_num)
theorem B704677 : Blo 626299 704677 := bbase (se 4 (by rfl) ⟨66063, by rfl⟩ : syracuseStep 704677 = 132127) (by norm_num)
theorem B1196221 : Blo 626299 1196221 := bbase (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) (by norm_num)
theorem B704713 : Blo 626299 704713 := bbase (se 2 (by rfl) ⟨264267, by rfl⟩ : syracuseStep 704713 = 528535) (by norm_num)
theorem B1589453 : Blo 626299 1589453 := bbase (se 3 (by rfl) ⟨298022, by rfl⟩ : syracuseStep 1589453 = 596045) (by norm_num)
theorem B704749 : Blo 626299 704749 := bbase (se 3 (by rfl) ⟨132140, by rfl⟩ : syracuseStep 704749 = 264281) (by norm_num)
theorem B704785 : Blo 626299 704785 := bbase (se 2 (by rfl) ⟨264294, by rfl⟩ : syracuseStep 704785 = 528589) (by norm_num)
theorem B2113829 : Blo 626299 2113829 := bbase (se 4 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 2113829 = 396343) (by norm_num)
theorem B704821 : Blo 626299 704821 := bbase (se 5 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 704821 = 66077) (by norm_num)
theorem B1196365 : Blo 626299 1196365 := bbase (se 3 (by rfl) ⟨224318, by rfl⟩ : syracuseStep 1196365 = 448637) (by norm_num)
theorem B704857 : Blo 626299 704857 := bbase (se 2 (by rfl) ⟨264321, by rfl⟩ : syracuseStep 704857 = 528643) (by norm_num)
theorem B704893 : Blo 626299 704893 := bbase (se 3 (by rfl) ⟨132167, by rfl⟩ : syracuseStep 704893 = 264335) (by norm_num)
theorem B1589645 : Blo 626299 1589645 := bbase (se 3 (by rfl) ⟨298058, by rfl⟩ : syracuseStep 1589645 = 596117) (by norm_num)
theorem B704929 : Blo 626299 704929 := bbase (se 2 (by rfl) ⟨264348, by rfl⟩ : syracuseStep 704929 = 528697) (by norm_num)
theorem B704965 : Blo 626299 704965 := bbase (se 4 (by rfl) ⟨66090, by rfl⟩ : syracuseStep 704965 = 132181) (by norm_num)
theorem B705001 : Blo 626299 705001 := bbase (se 2 (by rfl) ⟨264375, by rfl⟩ : syracuseStep 705001 = 528751) (by norm_num)
theorem B1196525 : Blo 626299 1196525 := bbase (se 3 (by rfl) ⟨224348, by rfl⟩ : syracuseStep 1196525 = 448697) (by norm_num)
theorem B705037 : Blo 626299 705037 := bbase (se 3 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 705037 = 264389) (by norm_num)
theorem B705073 : Blo 626299 705073 := bbase (se 2 (by rfl) ⟨264402, by rfl⟩ : syracuseStep 705073 = 528805) (by norm_num)
theorem B705109 : Blo 626299 705109 := bbase (se 8 (by rfl) ⟨4131, by rfl⟩ : syracuseStep 705109 = 8263) (by norm_num)
theorem B1131101 : Blo 626299 1131101 := bbase (se 3 (by rfl) ⟨212081, by rfl⟩ : syracuseStep 1131101 = 424163) (by norm_num)
theorem B672349 : Blo 626299 672349 := bbase (se 3 (by rfl) ⟨126065, by rfl⟩ : syracuseStep 672349 = 252131) (by norm_num)
theorem B705145 : Blo 626299 705145 := bbase (se 2 (by rfl) ⟨264429, by rfl⟩ : syracuseStep 705145 = 528859) (by norm_num)
theorem B672409 : Blo 626299 672409 := bbase (se 2 (by rfl) ⟨252153, by rfl⟩ : syracuseStep 672409 = 504307) (by norm_num)
theorem B705181 : Blo 626299 705181 := bbase (se 3 (by rfl) ⟨132221, by rfl⟩ : syracuseStep 705181 = 264443) (by norm_num)
theorem B705217 : Blo 626299 705217 := bbase (se 2 (by rfl) ⟨264456, by rfl⟩ : syracuseStep 705217 = 528913) (by norm_num)
theorem B2114261 : Blo 626299 2114261 := bbase (se 7 (by rfl) ⟨24776, by rfl⟩ : syracuseStep 2114261 = 49553) (by norm_num)
theorem B705253 : Blo 626299 705253 := bbase (se 4 (by rfl) ⟨66117, by rfl⟩ : syracuseStep 705253 = 132235) (by norm_num)
theorem B1589989 : Blo 626299 1589989 := bbase (se 4 (by rfl) ⟨149061, by rfl⟩ : syracuseStep 1589989 = 298123) (by norm_num)
theorem B705289 : Blo 626299 705289 := bbase (se 2 (by rfl) ⟨264483, by rfl⟩ : syracuseStep 705289 = 528967) (by norm_num)
theorem B705325 : Blo 626299 705325 := bbase (se 3 (by rfl) ⟨132248, by rfl⟩ : syracuseStep 705325 = 264497) (by norm_num)
theorem B705361 : Blo 626299 705361 := bbase (se 2 (by rfl) ⟨264510, by rfl⟩ : syracuseStep 705361 = 529021) (by norm_num)
theorem B1590101 : Blo 626299 1590101 := bbase (se 9 (by rfl) ⟨4658, by rfl⟩ : syracuseStep 1590101 = 9317) (by norm_num)
theorem B705397 : Blo 626299 705397 := bbase (se 5 (by rfl) ⟨33065, by rfl⟩ : syracuseStep 705397 = 66131) (by norm_num)
theorem B705433 : Blo 626299 705433 := bbase (se 2 (by rfl) ⟨264537, by rfl⟩ : syracuseStep 705433 = 529075) (by norm_num)
theorem B705469 : Blo 626299 705469 := bbase (se 3 (by rfl) ⟨132275, by rfl⟩ : syracuseStep 705469 = 264551) (by norm_num)
theorem B672725 : Blo 626299 672725 := bbase (se 7 (by rfl) ⟨7883, by rfl⟩ : syracuseStep 672725 = 15767) (by norm_num)
theorem B705505 : Blo 626299 705505 := bbase (se 2 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 705505 = 529129) (by norm_num)
theorem B705541 : Blo 626299 705541 := bbase (se 4 (by rfl) ⟨66144, by rfl⟩ : syracuseStep 705541 = 132289) (by norm_num)
theorem B1590293 : Blo 626299 1590293 := bbase (se 6 (by rfl) ⟨37272, by rfl⟩ : syracuseStep 1590293 = 74545) (by norm_num)
theorem B705577 : Blo 626299 705577 := bbase (se 2 (by rfl) ⟨264591, by rfl⟩ : syracuseStep 705577 = 529183) (by norm_num)
theorem B705613 : Blo 626299 705613 := bbase (se 3 (by rfl) ⟨132302, by rfl⟩ : syracuseStep 705613 = 264605) (by norm_num)
theorem B705649 : Blo 626299 705649 := bbase (se 2 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 705649 = 529237) (by norm_num)
theorem B2114693 : Blo 626299 2114693 := bbase (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) (by norm_num)
theorem B705685 : Blo 626299 705685 := bbase (se 6 (by rfl) ⟨16539, by rfl⟩ : syracuseStep 705685 = 33079) (by norm_num)
theorem B705721 : Blo 626299 705721 := bbase (se 2 (by rfl) ⟨264645, by rfl⟩ : syracuseStep 705721 = 529291) (by norm_num)
theorem B705757 : Blo 626299 705757 := bbase (se 3 (by rfl) ⟨132329, by rfl⟩ : syracuseStep 705757 = 264659) (by norm_num)
theorem B705793 : Blo 626299 705793 := bbase (se 2 (by rfl) ⟨264672, by rfl⟩ : syracuseStep 705793 = 529345) (by norm_num)
theorem B705829 : Blo 626299 705829 := bbase (se 4 (by rfl) ⟨66171, by rfl⟩ : syracuseStep 705829 = 132343) (by norm_num)
theorem B705865 : Blo 626299 705865 := bbase (se 2 (by rfl) ⟨264699, by rfl⟩ : syracuseStep 705865 = 529399) (by norm_num)
theorem B705901 : Blo 626299 705901 := bbase (se 3 (by rfl) ⟨132356, by rfl⟩ : syracuseStep 705901 = 264713) (by norm_num)
theorem B1590637 : Blo 626299 1590637 := bbase (se 3 (by rfl) ⟨298244, by rfl⟩ : syracuseStep 1590637 = 596489) (by norm_num)
theorem B705937 : Blo 626299 705937 := bbase (se 2 (by rfl) ⟨264726, by rfl⟩ : syracuseStep 705937 = 529453) (by norm_num)
theorem B2016677 : Blo 626299 2016677 := bbase (se 4 (by rfl) ⟨189063, by rfl⟩ : syracuseStep 2016677 = 378127) (by norm_num)
theorem B705973 : Blo 626299 705973 := bbase (se 5 (by rfl) ⟨33092, by rfl⟩ : syracuseStep 705973 = 66185) (by norm_num)
theorem B706009 : Blo 626299 706009 := bbase (se 2 (by rfl) ⟨264753, by rfl⟩ : syracuseStep 706009 = 529507) (by norm_num)
theorem B1590749 : Blo 626299 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B3261941 : Blo 626299 3261941 := bbase (se 5 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 3261941 = 305807) (by norm_num)
theorem B706045 : Blo 626299 706045 := bbase (se 3 (by rfl) ⟨132383, by rfl⟩ : syracuseStep 706045 = 264767) (by norm_num)
theorem B706081 : Blo 626299 706081 := bbase (se 2 (by rfl) ⟨264780, by rfl⟩ : syracuseStep 706081 = 529561) (by norm_num)
theorem B2115125 : Blo 626299 2115125 := bbase (se 5 (by rfl) ⟨99146, by rfl⟩ : syracuseStep 2115125 = 198293) (by norm_num)
theorem B706117 : Blo 626299 706117 := bbase (se 4 (by rfl) ⟨66198, by rfl⟩ : syracuseStep 706117 = 132397) (by norm_num)
theorem B706153 : Blo 626299 706153 := bbase (se 2 (by rfl) ⟨264807, by rfl⟩ : syracuseStep 706153 = 529615) (by norm_num)
theorem B706189 : Blo 626299 706189 := bbase (se 3 (by rfl) ⟨132410, by rfl⟩ : syracuseStep 706189 = 264821) (by norm_num)
theorem B1590941 : Blo 626299 1590941 := bbase (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) (by norm_num)
theorem B706225 : Blo 626299 706225 := bbase (se 2 (by rfl) ⟨264834, by rfl⟩ : syracuseStep 706225 = 529669) (by norm_num)
theorem B706261 : Blo 626299 706261 := bbase (se 7 (by rfl) ⟨8276, by rfl⟩ : syracuseStep 706261 = 16553) (by norm_num)
theorem B804601 : Blo 626299 804601 := bbase (se 2 (by rfl) ⟨301725, by rfl⟩ : syracuseStep 804601 = 603451) (by norm_num)
theorem B706297 : Blo 626299 706297 := bbase (se 2 (by rfl) ⟨264861, by rfl⟩ : syracuseStep 706297 = 529723) (by norm_num)
theorem B706333 : Blo 626299 706333 := bbase (se 3 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 706333 = 264875) (by norm_num)
theorem B4015925 : Blo 626299 4015925 := bbase (se 5 (by rfl) ⟨188246, by rfl⟩ : syracuseStep 4015925 = 376493) (by norm_num)
theorem B706369 : Blo 626299 706369 := bbase (se 2 (by rfl) ⟨264888, by rfl⟩ : syracuseStep 706369 = 529777) (by norm_num)
theorem B706405 : Blo 626299 706405 := bbase (se 4 (by rfl) ⟨66225, by rfl⟩ : syracuseStep 706405 = 132451) (by norm_num)
theorem B706441 : Blo 626299 706441 := bbase (se 2 (by rfl) ⟨264915, by rfl⟩ : syracuseStep 706441 = 529831) (by norm_num)
theorem B706477 : Blo 626299 706477 := bbase (se 3 (by rfl) ⟨132464, by rfl⟩ : syracuseStep 706477 = 264929) (by norm_num)
theorem B706513 : Blo 626299 706513 := bbase (se 2 (by rfl) ⟨264942, by rfl⟩ : syracuseStep 706513 = 529885) (by norm_num)
theorem B2115557 : Blo 626299 2115557 := bbase (se 4 (by rfl) ⟨198333, by rfl⟩ : syracuseStep 2115557 = 396667) (by norm_num)
theorem B706549 : Blo 626299 706549 := bbase (se 5 (by rfl) ⟨33119, by rfl⟩ : syracuseStep 706549 = 66239) (by norm_num)
theorem B1591285 : Blo 626299 1591285 := bbase (se 5 (by rfl) ⟨74591, by rfl⟩ : syracuseStep 1591285 = 149183) (by norm_num)
theorem B706585 : Blo 626299 706585 := bbase (se 2 (by rfl) ⟨264969, by rfl⟩ : syracuseStep 706585 = 529939) (by norm_num)
theorem B706621 : Blo 626299 706621 := bbase (se 3 (by rfl) ⟨132491, by rfl⟩ : syracuseStep 706621 = 264983) (by norm_num)
theorem B12863573 : Blo 626299 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B706657 : Blo 626299 706657 := bbase (se 2 (by rfl) ⟨264996, by rfl⟩ : syracuseStep 706657 = 529993) (by norm_num)
theorem B1591397 : Blo 626299 1591397 := bbase (se 4 (by rfl) ⟨149193, by rfl⟩ : syracuseStep 1591397 = 298387) (by norm_num)
theorem B706693 : Blo 626299 706693 := bbase (se 4 (by rfl) ⟨66252, by rfl⟩ : syracuseStep 706693 = 132505) (by norm_num)
theorem B706729 : Blo 626299 706729 := bbase (se 2 (by rfl) ⟨265023, by rfl⟩ : syracuseStep 706729 = 530047) (by norm_num)
theorem B1788101 : Blo 626299 1788101 := bbase (se 4 (by rfl) ⟨167634, by rfl⟩ : syracuseStep 1788101 = 335269) (by norm_num)
theorem B706765 : Blo 626299 706765 := bbase (se 3 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 706765 = 265037) (by norm_num)
theorem B706801 : Blo 626299 706801 := bbase (se 2 (by rfl) ⟨265050, by rfl⟩ : syracuseStep 706801 = 530101) (by norm_num)
theorem B706837 : Blo 626299 706837 := bbase (se 6 (by rfl) ⟨16566, by rfl⟩ : syracuseStep 706837 = 33133) (by norm_num)
theorem B1591589 : Blo 626299 1591589 := bbase (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) (by norm_num)
theorem B706873 : Blo 626299 706873 := bbase (se 2 (by rfl) ⟨265077, by rfl⟩ : syracuseStep 706873 = 530155) (by norm_num)
theorem B706909 : Blo 626299 706909 := bbase (se 3 (by rfl) ⟨132545, by rfl⟩ : syracuseStep 706909 = 265091) (by norm_num)
theorem B706945 : Blo 626299 706945 := bbase (se 2 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 706945 = 530209) (by norm_num)
theorem B2115989 : Blo 626299 2115989 := bbase (se 6 (by rfl) ⟨49593, by rfl⟩ : syracuseStep 2115989 = 99187) (by norm_num)
theorem B706981 : Blo 626299 706981 := bbase (se 4 (by rfl) ⟨66279, by rfl⟩ : syracuseStep 706981 = 132559) (by norm_num)
theorem B707017 : Blo 626299 707017 := bbase (se 2 (by rfl) ⟨265131, by rfl⟩ : syracuseStep 707017 = 530263) (by norm_num)
theorem B707053 : Blo 626299 707053 := bbase (se 3 (by rfl) ⟨132572, by rfl⟩ : syracuseStep 707053 = 265145) (by norm_num)
theorem B3394037 : Blo 626299 3394037 := bbase (se 5 (by rfl) ⟨159095, by rfl⟩ : syracuseStep 3394037 = 318191) (by norm_num)
theorem B707089 : Blo 626299 707089 := bbase (se 2 (by rfl) ⟨265158, by rfl⟩ : syracuseStep 707089 = 530317) (by norm_num)
theorem B707125 : Blo 626299 707125 := bbase (se 5 (by rfl) ⟨33146, by rfl⟩ : syracuseStep 707125 = 66293) (by norm_num)
theorem B707161 : Blo 626299 707161 := bbase (se 2 (by rfl) ⟨265185, by rfl⟩ : syracuseStep 707161 = 530371) (by norm_num)
theorem B3394165 : Blo 626299 3394165 := bbase (se 5 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 3394165 = 318203) (by norm_num)
theorem B707197 : Blo 626299 707197 := bbase (se 3 (by rfl) ⟨132599, by rfl⟩ : syracuseStep 707197 = 265199) (by norm_num)
theorem B1591933 : Blo 626299 1591933 := bbase (se 3 (by rfl) ⟨298487, by rfl⟩ : syracuseStep 1591933 = 596975) (by norm_num)
theorem B707233 : Blo 626299 707233 := bbase (se 2 (by rfl) ⟨265212, by rfl⟩ : syracuseStep 707233 = 530425) (by norm_num)
theorem B707269 : Blo 626299 707269 := bbase (se 4 (by rfl) ⟨66306, by rfl⟩ : syracuseStep 707269 = 132613) (by norm_num)
theorem B707305 : Blo 626299 707305 := bbase (se 2 (by rfl) ⟨265239, by rfl⟩ : syracuseStep 707305 = 530479) (by norm_num)
theorem B1592045 : Blo 626299 1592045 := bbase (se 3 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 1592045 = 597017) (by norm_num)
theorem B707341 : Blo 626299 707341 := bbase (se 3 (by rfl) ⟨132626, by rfl⟩ : syracuseStep 707341 = 265253) (by norm_num)
theorem B707377 : Blo 626299 707377 := bbase (se 2 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 707377 = 530533) (by norm_num)
theorem B2116421 : Blo 626299 2116421 := bbase (se 4 (by rfl) ⟨198414, by rfl⟩ : syracuseStep 2116421 = 396829) (by norm_num)
theorem B707413 : Blo 626299 707413 := bbase (se 9 (by rfl) ⟨2072, by rfl⟩ : syracuseStep 707413 = 4145) (by norm_num)
theorem B707449 : Blo 626299 707449 := bbase (se 2 (by rfl) ⟨265293, by rfl⟩ : syracuseStep 707449 = 530587) (by norm_num)
theorem B707485 : Blo 626299 707485 := bbase (se 3 (by rfl) ⟨132653, by rfl⟩ : syracuseStep 707485 = 265307) (by norm_num)
theorem B1592237 : Blo 626299 1592237 := bbase (se 3 (by rfl) ⟨298544, by rfl⟩ : syracuseStep 1592237 = 597089) (by norm_num)
theorem B707521 : Blo 626299 707521 := bbase (se 2 (by rfl) ⟨265320, by rfl⟩ : syracuseStep 707521 = 530641) (by norm_num)
theorem B8604629 : Blo 626299 8604629 := bbase (se 7 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 8604629 = 201671) (by norm_num)
theorem B707557 : Blo 626299 707557 := bbase (se 4 (by rfl) ⟨66333, by rfl⟩ : syracuseStep 707557 = 132667) (by norm_num)
theorem B707593 : Blo 626299 707593 := bbase (se 2 (by rfl) ⟨265347, by rfl⟩ : syracuseStep 707593 = 530695) (by norm_num)
theorem B707629 : Blo 626299 707629 := bbase (se 3 (by rfl) ⟨132680, by rfl⟩ : syracuseStep 707629 = 265361) (by norm_num)
theorem B707665 : Blo 626299 707665 := bbase (se 2 (by rfl) ⟨265374, by rfl⟩ : syracuseStep 707665 = 530749) (by norm_num)
theorem B707701 : Blo 626299 707701 := bbase (se 5 (by rfl) ⟨33173, by rfl⟩ : syracuseStep 707701 = 66347) (by norm_num)
theorem B707737 : Blo 626299 707737 := bbase (se 2 (by rfl) ⟨265401, by rfl⟩ : syracuseStep 707737 = 530803) (by norm_num)
theorem B707773 : Blo 626299 707773 := bbase (se 3 (by rfl) ⟨132707, by rfl⟩ : syracuseStep 707773 = 265415) (by norm_num)
theorem B4312277 : Blo 626299 4312277 := bbase (se 7 (by rfl) ⟨50534, by rfl⟩ : syracuseStep 4312277 = 101069) (by norm_num)
theorem B707809 : Blo 626299 707809 := bbase (se 2 (by rfl) ⟨265428, by rfl⟩ : syracuseStep 707809 = 530857) (by norm_num)
theorem B2018533 : Blo 626299 2018533 := bbase (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) (by norm_num)
theorem B2116853 : Blo 626299 2116853 := bbase (se 5 (by rfl) ⟨99227, by rfl⟩ : syracuseStep 2116853 = 198455) (by norm_num)
theorem B4771061 : Blo 626299 4771061 := bbase (se 5 (by rfl) ⟨223643, by rfl⟩ : syracuseStep 4771061 = 447287) (by norm_num)
theorem B1592581 : Blo 626299 1592581 := bbase (se 4 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 1592581 = 298609) (by norm_num)
theorem B707845 : Blo 626299 707845 := bbase (se 4 (by rfl) ⟨66360, by rfl⟩ : syracuseStep 707845 = 132721) (by norm_num)
theorem B707881 : Blo 626299 707881 := bbase (se 2 (by rfl) ⟨265455, by rfl⟩ : syracuseStep 707881 = 530911) (by norm_num)
theorem B2379077 : Blo 626299 2379077 := bbase (se 4 (by rfl) ⟨223038, by rfl⟩ : syracuseStep 2379077 = 446077) (by norm_num)
theorem B707917 : Blo 626299 707917 := bbase (se 3 (by rfl) ⟨132734, by rfl⟩ : syracuseStep 707917 = 265469) (by norm_num)
theorem B1789285 : Blo 626299 1789285 := bbase (se 4 (by rfl) ⟨167745, by rfl⟩ : syracuseStep 1789285 = 335491) (by norm_num)
theorem B2149733 : Blo 626299 2149733 := bbase (se 4 (by rfl) ⟨201537, by rfl⟩ : syracuseStep 2149733 = 403075) (by norm_num)
theorem B707953 : Blo 626299 707953 := bbase (se 2 (by rfl) ⟨265482, by rfl⟩ : syracuseStep 707953 = 530965) (by norm_num)
theorem B1592693 : Blo 626299 1592693 := bbase (se 5 (by rfl) ⟨74657, by rfl⟩ : syracuseStep 1592693 = 149315) (by norm_num)
theorem B707989 : Blo 626299 707989 := bbase (se 6 (by rfl) ⟨16593, by rfl⟩ : syracuseStep 707989 = 33187) (by norm_num)
theorem B708025 : Blo 626299 708025 := bbase (se 2 (by rfl) ⟨265509, by rfl⟩ : syracuseStep 708025 = 531019) (by norm_num)
theorem B1134013 : Blo 626299 1134013 := bbase (se 3 (by rfl) ⟨212627, by rfl⟩ : syracuseStep 1134013 = 425255) (by norm_num)
theorem B708061 : Blo 626299 708061 := bbase (se 3 (by rfl) ⟨132761, by rfl⟩ : syracuseStep 708061 = 265523) (by norm_num)
theorem B708097 : Blo 626299 708097 := bbase (se 2 (by rfl) ⟨265536, by rfl⟩ : syracuseStep 708097 = 531073) (by norm_num)
theorem B1789445 : Blo 626299 1789445 := bbase (se 4 (by rfl) ⟨167760, by rfl⟩ : syracuseStep 1789445 = 335521) (by norm_num)
theorem B708133 : Blo 626299 708133 := bbase (se 4 (by rfl) ⟨66387, by rfl⟩ : syracuseStep 708133 = 132775) (by norm_num)
theorem B1592885 : Blo 626299 1592885 := bbase (se 5 (by rfl) ⟨74666, by rfl⟩ : syracuseStep 1592885 = 149333) (by norm_num)
theorem B708169 : Blo 626299 708169 := bbase (se 2 (by rfl) ⟨265563, by rfl⟩ : syracuseStep 708169 = 531127) (by norm_num)
theorem B2379365 : Blo 626299 2379365 := bbase (se 4 (by rfl) ⟨223065, by rfl⟩ : syracuseStep 2379365 = 446131) (by norm_num)
theorem B708205 : Blo 626299 708205 := bbase (se 3 (by rfl) ⟨132788, by rfl⟩ : syracuseStep 708205 = 265577) (by norm_num)
theorem B708241 : Blo 626299 708241 := bbase (se 2 (by rfl) ⟨265590, by rfl⟩ : syracuseStep 708241 = 531181) (by norm_num)
theorem B2117285 : Blo 626299 2117285 := bbase (se 4 (by rfl) ⟨198495, by rfl⟩ : syracuseStep 2117285 = 396991) (by norm_num)
theorem B708277 : Blo 626299 708277 := bbase (se 5 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 708277 = 66401) (by norm_num)
theorem B708313 : Blo 626299 708313 := bbase (se 2 (by rfl) ⟨265617, by rfl⟩ : syracuseStep 708313 = 531235) (by norm_num)
theorem B1789685 : Blo 626299 1789685 := bbase (se 5 (by rfl) ⟨83891, by rfl⟩ : syracuseStep 1789685 = 167783) (by norm_num)
theorem B708349 : Blo 626299 708349 := bbase (se 3 (by rfl) ⟨132815, by rfl⟩ : syracuseStep 708349 = 265631) (by norm_num)
theorem B708385 : Blo 626299 708385 := bbase (se 2 (by rfl) ⟨265644, by rfl⟩ : syracuseStep 708385 = 531289) (by norm_num)
theorem B708421 : Blo 626299 708421 := bbase (se 4 (by rfl) ⟨66414, by rfl⟩ : syracuseStep 708421 = 132829) (by norm_num)
theorem B36622165 : Blo 626299 36622165 := bbase (se 9 (by rfl) ⟨107291, by rfl⟩ : syracuseStep 36622165 = 214583) (by norm_num)
theorem B708457 : Blo 626299 708457 := bbase (se 2 (by rfl) ⟨265671, by rfl⟩ : syracuseStep 708457 = 531343) (by norm_num)
theorem B1593229 : Blo 626299 1593229 := bbase (se 3 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 1593229 = 597461) (by norm_num)
theorem B708493 : Blo 626299 708493 := bbase (se 3 (by rfl) ⟨132842, by rfl⟩ : syracuseStep 708493 = 265685) (by norm_num)
theorem B708529 : Blo 626299 708529 := bbase (se 2 (by rfl) ⟨265698, by rfl⟩ : syracuseStep 708529 = 531397) (by norm_num)
theorem B1789877 : Blo 626299 1789877 := bbase (se 5 (by rfl) ⟨83900, by rfl⟩ : syracuseStep 1789877 = 167801) (by norm_num)
theorem B806869 : Blo 626299 806869 := bbase (se 7 (by rfl) ⟨9455, by rfl⟩ : syracuseStep 806869 = 18911) (by norm_num)
theorem B708565 : Blo 626299 708565 := bbase (se 7 (by rfl) ⟨8303, by rfl⟩ : syracuseStep 708565 = 16607) (by norm_num)
theorem B708601 : Blo 626299 708601 := bbase (se 2 (by rfl) ⟨265725, by rfl⟩ : syracuseStep 708601 = 531451) (by norm_num)
theorem B1593341 : Blo 626299 1593341 := bbase (se 3 (by rfl) ⟨298751, by rfl⟩ : syracuseStep 1593341 = 597503) (by norm_num)
theorem B708637 : Blo 626299 708637 := bbase (se 3 (by rfl) ⟨132869, by rfl⟩ : syracuseStep 708637 = 265739) (by norm_num)
theorem B708673 : Blo 626299 708673 := bbase (se 2 (by rfl) ⟨265752, by rfl⟩ : syracuseStep 708673 = 531505) (by norm_num)
theorem B2117717 : Blo 626299 2117717 := bbase (se 8 (by rfl) ⟨12408, by rfl⟩ : syracuseStep 2117717 = 24817) (by norm_num)
theorem B708709 : Blo 626299 708709 := bbase (se 4 (by rfl) ⟨66441, by rfl⟩ : syracuseStep 708709 = 132883) (by norm_num)
theorem B708745 : Blo 626299 708745 := bbase (se 2 (by rfl) ⟨265779, by rfl⟩ : syracuseStep 708745 = 531559) (by norm_num)
theorem B1134733 : Blo 626299 1134733 := bbase (se 3 (by rfl) ⟨212762, by rfl⟩ : syracuseStep 1134733 = 425525) (by norm_num)
theorem B1003693 : Blo 626299 1003693 := bbase (se 3 (by rfl) ⟨188192, by rfl⟩ : syracuseStep 1003693 = 376385) (by norm_num)
theorem B708781 : Blo 626299 708781 := bbase (se 3 (by rfl) ⟨132896, by rfl⟩ : syracuseStep 708781 = 265793) (by norm_num)
theorem B1593533 : Blo 626299 1593533 := bbase (se 3 (by rfl) ⟨298787, by rfl⟩ : syracuseStep 1593533 = 597575) (by norm_num)
theorem B708817 : Blo 626299 708817 := bbase (se 2 (by rfl) ⟨265806, by rfl⟩ : syracuseStep 708817 = 531613) (by norm_num)
theorem B708853 : Blo 626299 708853 := bbase (se 5 (by rfl) ⟨33227, by rfl⟩ : syracuseStep 708853 = 66455) (by norm_num)
theorem B708889 : Blo 626299 708889 := bbase (se 2 (by rfl) ⟨265833, by rfl⟩ : syracuseStep 708889 = 531667) (by norm_num)
theorem B708925 : Blo 626299 708925 := bbase (se 3 (by rfl) ⟨132923, by rfl⟩ : syracuseStep 708925 = 265847) (by norm_num)
theorem B708961 : Blo 626299 708961 := bbase (se 2 (by rfl) ⟨265860, by rfl⟩ : syracuseStep 708961 = 531721) (by norm_num)
theorem B1134965 : Blo 626299 1134965 := bbase (se 5 (by rfl) ⟨53201, by rfl⟩ : syracuseStep 1134965 = 106403) (by norm_num)
theorem B708997 : Blo 626299 708997 := bbase (se 4 (by rfl) ⟨66468, by rfl⟩ : syracuseStep 708997 = 132937) (by norm_num)
theorem B709033 : Blo 626299 709033 := bbase (se 2 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 709033 = 531775) (by norm_num)
theorem B709069 : Blo 626299 709069 := bbase (se 3 (by rfl) ⟨132950, by rfl⟩ : syracuseStep 709069 = 265901) (by norm_num)
theorem B2118149 : Blo 626299 2118149 := bbase (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) (by norm_num)
theorem B1593877 : Blo 626299 1593877 := bbase (se 6 (by rfl) ⟨37356, by rfl⟩ : syracuseStep 1593877 = 74713) (by norm_num)
theorem B1004141 : Blo 626299 1004141 := bbase (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) (by norm_num)
theorem B1593989 : Blo 626299 1593989 := bbase (se 4 (by rfl) ⟨149436, by rfl⟩ : syracuseStep 1593989 = 298873) (by norm_num)
theorem B2380549 : Blo 626299 2380549 := bbase (se 4 (by rfl) ⟨223176, by rfl⟩ : syracuseStep 2380549 = 446353) (by norm_num)
theorem B1135397 : Blo 626299 1135397 := bbase (se 4 (by rfl) ⟨106443, by rfl⟩ : syracuseStep 1135397 = 212887) (by norm_num)
theorem B3068725 : Blo 626299 3068725 := bbase (se 5 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 3068725 = 287693) (by norm_num)
theorem B1594181 : Blo 626299 1594181 := bbase (se 4 (by rfl) ⟨149454, by rfl⟩ : syracuseStep 1594181 = 298909) (by norm_num)
theorem B1790869 : Blo 626299 1790869 := bbase (se 6 (by rfl) ⟨41973, by rfl⟩ : syracuseStep 1790869 = 83947) (by norm_num)
theorem B2118581 : Blo 626299 2118581 := bbase (se 5 (by rfl) ⟨99308, by rfl⟩ : syracuseStep 2118581 = 198617) (by norm_num)
theorem B1135541 : Blo 626299 1135541 := bbase (se 5 (by rfl) ⟨53228, by rfl⟩ : syracuseStep 1135541 = 106457) (by norm_num)
theorem B2380853 : Blo 626299 2380853 := bbase (se 5 (by rfl) ⟨111602, by rfl⟩ : syracuseStep 2380853 = 223205) (by norm_num)
theorem B1594525 : Blo 626299 1594525 := bbase (se 3 (by rfl) ⟨298973, by rfl⟩ : syracuseStep 1594525 = 597947) (by norm_num)
theorem B1594637 : Blo 626299 1594637 := bbase (se 3 (by rfl) ⟨298994, by rfl⟩ : syracuseStep 1594637 = 597989) (by norm_num)
theorem B2119013 : Blo 626299 2119013 := bbase (se 4 (by rfl) ⟨198657, by rfl⟩ : syracuseStep 2119013 = 397315) (by norm_num)
theorem B939461 : Blo 626299 939461 := bbase (se 4 (by rfl) ⟨88074, by rfl⟩ : syracuseStep 939461 = 176149) (by norm_num)
theorem B1594829 : Blo 626299 1594829 := bbase (se 3 (by rfl) ⟨299030, by rfl⟩ : syracuseStep 1594829 = 598061) (by norm_num)
theorem B939485 : Blo 626299 939485 := bbase (se 3 (by rfl) ⟨176153, by rfl⟩ : syracuseStep 939485 = 352307) (by norm_num)
theorem B939509 : Blo 626299 939509 := bbase (se 5 (by rfl) ⟨44039, by rfl⟩ : syracuseStep 939509 = 88079) (by norm_num)
theorem B939533 : Blo 626299 939533 := bbase (se 3 (by rfl) ⟨176162, by rfl⟩ : syracuseStep 939533 = 352325) (by norm_num)
theorem B939557 : Blo 626299 939557 := bbase (se 4 (by rfl) ⟨88083, by rfl⟩ : syracuseStep 939557 = 176167) (by norm_num)
theorem B939581 : Blo 626299 939581 := bbase (se 3 (by rfl) ⟨176171, by rfl⟩ : syracuseStep 939581 = 352343) (by norm_num)
theorem B939605 : Blo 626299 939605 := bbase (se 8 (by rfl) ⟨5505, by rfl⟩ : syracuseStep 939605 = 11011) (by norm_num)
theorem B18142805 : Blo 626299 18142805 := bbase (se 8 (by rfl) ⟨106305, by rfl⟩ : syracuseStep 18142805 = 212611) (by norm_num)
theorem B939629 : Blo 626299 939629 := bbase (se 3 (by rfl) ⟨176180, by rfl⟩ : syracuseStep 939629 = 352361) (by norm_num)
theorem B2676341 : Blo 626299 2676341 := bbase (se 5 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 2676341 = 250907) (by norm_num)
theorem B939653 : Blo 626299 939653 := bbase (se 4 (by rfl) ⟨88092, by rfl⟩ : syracuseStep 939653 = 176185) (by norm_num)
theorem B939677 : Blo 626299 939677 := bbase (se 3 (by rfl) ⟨176189, by rfl⟩ : syracuseStep 939677 = 352379) (by norm_num)
theorem B939701 : Blo 626299 939701 := bbase (se 5 (by rfl) ⟨44048, by rfl⟩ : syracuseStep 939701 = 88097) (by norm_num)
theorem B1529533 : Blo 626299 1529533 := bbase (se 3 (by rfl) ⟨286787, by rfl⟩ : syracuseStep 1529533 = 573575) (by norm_num)
theorem B939725 : Blo 626299 939725 := bbase (se 3 (by rfl) ⟨176198, by rfl⟩ : syracuseStep 939725 = 352397) (by norm_num)
theorem B939749 : Blo 626299 939749 := bbase (se 4 (by rfl) ⟨88101, by rfl⟩ : syracuseStep 939749 = 176203) (by norm_num)
theorem B939773 : Blo 626299 939773 := bbase (se 3 (by rfl) ⟨176207, by rfl⟩ : syracuseStep 939773 = 352415) (by norm_num)
theorem B939797 : Blo 626299 939797 := bbase (se 6 (by rfl) ⟨22026, by rfl⟩ : syracuseStep 939797 = 44053) (by norm_num)
theorem B2119445 : Blo 626299 2119445 := bbase (se 6 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 2119445 = 99349) (by norm_num)
theorem B1595173 : Blo 626299 1595173 := bbase (se 4 (by rfl) ⟨149547, by rfl⟩ : syracuseStep 1595173 = 299095) (by norm_num)
theorem B939821 : Blo 626299 939821 := bbase (se 3 (by rfl) ⟨176216, by rfl⟩ : syracuseStep 939821 = 352433) (by norm_num)
theorem B939845 : Blo 626299 939845 := bbase (se 4 (by rfl) ⟨88110, by rfl⟩ : syracuseStep 939845 = 176221) (by norm_num)
theorem B939869 : Blo 626299 939869 := bbase (se 3 (by rfl) ⟨176225, by rfl⟩ : syracuseStep 939869 = 352451) (by norm_num)
theorem B939893 : Blo 626299 939893 := bbase (se 5 (by rfl) ⟨44057, by rfl⟩ : syracuseStep 939893 = 88115) (by norm_num)
theorem B939917 : Blo 626299 939917 := bbase (se 3 (by rfl) ⟨176234, by rfl⟩ : syracuseStep 939917 = 352469) (by norm_num)
theorem B1595285 : Blo 626299 1595285 := bbase (se 6 (by rfl) ⟨37389, by rfl⟩ : syracuseStep 1595285 = 74779) (by norm_num)
theorem B939941 : Blo 626299 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B939965 : Blo 626299 939965 := bbase (se 3 (by rfl) ⟨176243, by rfl⟩ : syracuseStep 939965 = 352487) (by norm_num)
theorem B939989 : Blo 626299 939989 := bbase (se 7 (by rfl) ⟨11015, by rfl⟩ : syracuseStep 939989 = 22031) (by norm_num)
theorem B1791973 : Blo 626299 1791973 := bbase (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) (by norm_num)
theorem B940013 : Blo 626299 940013 := bbase (se 3 (by rfl) ⟨176252, by rfl⟩ : syracuseStep 940013 = 352505) (by norm_num)
theorem B940037 : Blo 626299 940037 := bbase (se 4 (by rfl) ⟨88128, by rfl⟩ : syracuseStep 940037 = 176257) (by norm_num)
theorem B2152469 : Blo 626299 2152469 := bbase (se 6 (by rfl) ⟨50448, by rfl⟩ : syracuseStep 2152469 = 100897) (by norm_num)
theorem B940061 : Blo 626299 940061 := bbase (se 3 (by rfl) ⟨176261, by rfl⟩ : syracuseStep 940061 = 352523) (by norm_num)
theorem B940085 : Blo 626299 940085 := bbase (se 5 (by rfl) ⟨44066, by rfl⟩ : syracuseStep 940085 = 88133) (by norm_num)
theorem B940109 : Blo 626299 940109 := bbase (se 3 (by rfl) ⟨176270, by rfl⟩ : syracuseStep 940109 = 352541) (by norm_num)
theorem B1005653 : Blo 626299 1005653 := bbase (se 8 (by rfl) ⟨5892, by rfl⟩ : syracuseStep 1005653 = 11785) (by norm_num)
theorem B940133 : Blo 626299 940133 := bbase (se 4 (by rfl) ⟨88137, by rfl⟩ : syracuseStep 940133 = 176275) (by norm_num)
theorem B940157 : Blo 626299 940157 := bbase (se 3 (by rfl) ⟨176279, by rfl⟩ : syracuseStep 940157 = 352559) (by norm_num)
theorem B940181 : Blo 626299 940181 := bbase (se 6 (by rfl) ⟨22035, by rfl⟩ : syracuseStep 940181 = 44071) (by norm_num)
theorem B940205 : Blo 626299 940205 := bbase (se 3 (by rfl) ⟨176288, by rfl⟩ : syracuseStep 940205 = 352577) (by norm_num)
theorem B940229 : Blo 626299 940229 := bbase (se 4 (by rfl) ⟨88146, by rfl⟩ : syracuseStep 940229 = 176293) (by norm_num)
theorem B2119877 : Blo 626299 2119877 := bbase (se 4 (by rfl) ⟨198738, by rfl⟩ : syracuseStep 2119877 = 397477) (by norm_num)
theorem B1005781 : Blo 626299 1005781 := bbase (se 7 (by rfl) ⟨11786, by rfl⟩ : syracuseStep 1005781 = 23573) (by norm_num)
theorem B940253 : Blo 626299 940253 := bbase (se 3 (by rfl) ⟨176297, by rfl⟩ : syracuseStep 940253 = 352595) (by norm_num)
theorem B940277 : Blo 626299 940277 := bbase (se 5 (by rfl) ⟨44075, by rfl⟩ : syracuseStep 940277 = 88151) (by norm_num)
theorem B645385 : Blo 626299 645385 := bbase (se 2 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 645385 = 484039) (by norm_num)
theorem B940301 : Blo 626299 940301 := bbase (se 3 (by rfl) ⟨176306, by rfl⟩ : syracuseStep 940301 = 352613) (by norm_num)
theorem B940325 : Blo 626299 940325 := bbase (se 4 (by rfl) ⟨88155, by rfl⟩ : syracuseStep 940325 = 176311) (by norm_num)
theorem B940349 : Blo 626299 940349 := bbase (se 3 (by rfl) ⟨176315, by rfl⟩ : syracuseStep 940349 = 352631) (by norm_num)
theorem B940373 : Blo 626299 940373 := bbase (se 10 (by rfl) ⟨1377, by rfl⟩ : syracuseStep 940373 = 2755) (by norm_num)
theorem B940397 : Blo 626299 940397 := bbase (se 3 (by rfl) ⟨176324, by rfl⟩ : syracuseStep 940397 = 352649) (by norm_num)
theorem B940421 : Blo 626299 940421 := bbase (se 4 (by rfl) ⟨88164, by rfl⟩ : syracuseStep 940421 = 176329) (by norm_num)
theorem B940445 : Blo 626299 940445 := bbase (se 3 (by rfl) ⟨176333, by rfl⟩ : syracuseStep 940445 = 352667) (by norm_num)
theorem B940469 : Blo 626299 940469 := bbase (se 5 (by rfl) ⟨44084, by rfl⟩ : syracuseStep 940469 = 88169) (by norm_num)
theorem B940493 : Blo 626299 940493 := bbase (se 3 (by rfl) ⟨176342, by rfl⟩ : syracuseStep 940493 = 352685) (by norm_num)
theorem B940517 : Blo 626299 940517 := bbase (se 4 (by rfl) ⟨88173, by rfl⟩ : syracuseStep 940517 = 176347) (by norm_num)
theorem B940541 : Blo 626299 940541 := bbase (se 3 (by rfl) ⟨176351, by rfl⟩ : syracuseStep 940541 = 352703) (by norm_num)
theorem B940565 : Blo 626299 940565 := bbase (se 6 (by rfl) ⟨22044, by rfl⟩ : syracuseStep 940565 = 44089) (by norm_num)
theorem B940589 : Blo 626299 940589 := bbase (se 3 (by rfl) ⟨176360, by rfl⟩ : syracuseStep 940589 = 352721) (by norm_num)
theorem B940613 : Blo 626299 940613 := bbase (se 4 (by rfl) ⟨88182, by rfl⟩ : syracuseStep 940613 = 176365) (by norm_num)
theorem B2447941 : Blo 626299 2447941 := bbase (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) (by norm_num)
theorem B2677333 : Blo 626299 2677333 := bbase (se 8 (by rfl) ⟨15687, by rfl⟩ : syracuseStep 2677333 = 31375) (by norm_num)
theorem B940637 : Blo 626299 940637 := bbase (se 3 (by rfl) ⟨176369, by rfl⟩ : syracuseStep 940637 = 352739) (by norm_num)
theorem B940661 : Blo 626299 940661 := bbase (se 5 (by rfl) ⟨44093, by rfl⟩ : syracuseStep 940661 = 88187) (by norm_num)
theorem B2120309 : Blo 626299 2120309 := bbase (se 5 (by rfl) ⟨99389, by rfl⟩ : syracuseStep 2120309 = 198779) (by norm_num)
theorem B940685 : Blo 626299 940685 := bbase (se 3 (by rfl) ⟨176378, by rfl⟩ : syracuseStep 940685 = 352757) (by norm_num)
theorem B940709 : Blo 626299 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B940733 : Blo 626299 940733 := bbase (se 3 (by rfl) ⟨176387, by rfl⟩ : syracuseStep 940733 = 352775) (by norm_num)
theorem B940757 : Blo 626299 940757 := bbase (se 7 (by rfl) ⟨11024, by rfl⟩ : syracuseStep 940757 = 22049) (by norm_num)
theorem B940781 : Blo 626299 940781 := bbase (se 3 (by rfl) ⟨176396, by rfl⟩ : syracuseStep 940781 = 352793) (by norm_num)
theorem B940805 : Blo 626299 940805 := bbase (se 4 (by rfl) ⟨88200, by rfl⟩ : syracuseStep 940805 = 176401) (by norm_num)
theorem B940829 : Blo 626299 940829 := bbase (se 3 (by rfl) ⟨176405, by rfl⟩ : syracuseStep 940829 = 352811) (by norm_num)
theorem B940853 : Blo 626299 940853 := bbase (se 5 (by rfl) ⟨44102, by rfl⟩ : syracuseStep 940853 = 88205) (by norm_num)
theorem B1694533 : Blo 626299 1694533 := bbase (se 4 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 1694533 = 317725) (by norm_num)
theorem B940877 : Blo 626299 940877 := bbase (se 3 (by rfl) ⟨176414, by rfl⟩ : syracuseStep 940877 = 352829) (by norm_num)
theorem B940901 : Blo 626299 940901 := bbase (se 4 (by rfl) ⟨88209, by rfl⟩ : syracuseStep 940901 = 176419) (by norm_num)
theorem B940925 : Blo 626299 940925 := bbase (se 3 (by rfl) ⟨176423, by rfl⟩ : syracuseStep 940925 = 352847) (by norm_num)
theorem B940949 : Blo 626299 940949 := bbase (se 6 (by rfl) ⟨22053, by rfl⟩ : syracuseStep 940949 = 44107) (by norm_num)
theorem B940973 : Blo 626299 940973 := bbase (se 3 (by rfl) ⟨176432, by rfl⟩ : syracuseStep 940973 = 352865) (by norm_num)
theorem B940997 : Blo 626299 940997 := bbase (se 4 (by rfl) ⟨88218, by rfl⟩ : syracuseStep 940997 = 176437) (by norm_num)
theorem B941021 : Blo 626299 941021 := bbase (se 3 (by rfl) ⟨176441, by rfl⟩ : syracuseStep 941021 = 352883) (by norm_num)
theorem B941045 : Blo 626299 941045 := bbase (se 5 (by rfl) ⟨44111, by rfl⟩ : syracuseStep 941045 = 88223) (by norm_num)
theorem B941069 : Blo 626299 941069 := bbase (se 3 (by rfl) ⟨176450, by rfl⟩ : syracuseStep 941069 = 352901) (by norm_num)
theorem B941093 : Blo 626299 941093 := bbase (se 4 (by rfl) ⟨88227, by rfl⟩ : syracuseStep 941093 = 176455) (by norm_num)
theorem B2120741 : Blo 626299 2120741 := bbase (se 4 (by rfl) ⟨198819, by rfl⟩ : syracuseStep 2120741 = 397639) (by norm_num)
theorem B941117 : Blo 626299 941117 := bbase (se 3 (by rfl) ⟨176459, by rfl⟩ : syracuseStep 941117 = 352919) (by norm_num)
theorem B941141 : Blo 626299 941141 := bbase (se 8 (by rfl) ⟨5514, by rfl⟩ : syracuseStep 941141 = 11029) (by norm_num)
theorem B941165 : Blo 626299 941165 := bbase (se 3 (by rfl) ⟨176468, by rfl⟩ : syracuseStep 941165 = 352937) (by norm_num)
theorem B2382965 : Blo 626299 2382965 := bbase (se 5 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 2382965 = 223403) (by norm_num)
theorem B941189 : Blo 626299 941189 := bbase (se 4 (by rfl) ⟨88236, by rfl⟩ : syracuseStep 941189 = 176473) (by norm_num)
theorem B941213 : Blo 626299 941213 := bbase (se 3 (by rfl) ⟨176477, by rfl⟩ : syracuseStep 941213 = 352955) (by norm_num)
theorem B941237 : Blo 626299 941237 := bbase (se 5 (by rfl) ⟨44120, by rfl⟩ : syracuseStep 941237 = 88241) (by norm_num)
theorem B941261 : Blo 626299 941261 := bbase (se 3 (by rfl) ⟨176486, by rfl⟩ : syracuseStep 941261 = 352973) (by norm_num)
theorem B908501 : Blo 626299 908501 := bbase (se 7 (by rfl) ⟨10646, by rfl⟩ : syracuseStep 908501 = 21293) (by norm_num)
theorem B941285 : Blo 626299 941285 := bbase (se 4 (by rfl) ⟨88245, by rfl⟩ : syracuseStep 941285 = 176491) (by norm_num)
theorem B941309 : Blo 626299 941309 := bbase (se 3 (by rfl) ⟨176495, by rfl⟩ : syracuseStep 941309 = 352991) (by norm_num)
theorem B1072397 : Blo 626299 1072397 := bbase (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) (by norm_num)
theorem B941333 : Blo 626299 941333 := bbase (se 6 (by rfl) ⟨22062, by rfl⟩ : syracuseStep 941333 = 44125) (by norm_num)
theorem B941357 : Blo 626299 941357 := bbase (se 3 (by rfl) ⟨176504, by rfl⟩ : syracuseStep 941357 = 353009) (by norm_num)
theorem B1072453 : Blo 626299 1072453 := bbase (se 4 (by rfl) ⟨100542, by rfl⟩ : syracuseStep 1072453 = 201085) (by norm_num)
theorem B941381 : Blo 626299 941381 := bbase (se 4 (by rfl) ⟨88254, by rfl⟩ : syracuseStep 941381 = 176509) (by norm_num)
theorem B941405 : Blo 626299 941405 := bbase (se 3 (by rfl) ⟨176513, by rfl⟩ : syracuseStep 941405 = 353027) (by norm_num)
theorem B941429 : Blo 626299 941429 := bbase (se 5 (by rfl) ⟨44129, by rfl⟩ : syracuseStep 941429 = 88259) (by norm_num)
theorem B941453 : Blo 626299 941453 := bbase (se 3 (by rfl) ⟨176522, by rfl⟩ : syracuseStep 941453 = 353045) (by norm_num)
theorem B1531277 : Blo 626299 1531277 := bbase (se 3 (by rfl) ⟨287114, by rfl⟩ : syracuseStep 1531277 = 574229) (by norm_num)
theorem B2383253 : Blo 626299 2383253 := bbase (se 6 (by rfl) ⟨55857, by rfl⟩ : syracuseStep 2383253 = 111715) (by norm_num)
theorem B941477 : Blo 626299 941477 := bbase (se 4 (by rfl) ⟨88263, by rfl⟩ : syracuseStep 941477 = 176527) (by norm_num)
theorem B941501 : Blo 626299 941501 := bbase (se 3 (by rfl) ⟨176531, by rfl⟩ : syracuseStep 941501 = 353063) (by norm_num)
theorem B1793477 : Blo 626299 1793477 := bbase (se 4 (by rfl) ⟨168138, by rfl⟩ : syracuseStep 1793477 = 336277) (by norm_num)
theorem B941525 : Blo 626299 941525 := bbase (se 7 (by rfl) ⟨11033, by rfl⟩ : syracuseStep 941525 = 22067) (by norm_num)
theorem B2121173 : Blo 626299 2121173 := bbase (se 7 (by rfl) ⟨24857, by rfl⟩ : syracuseStep 2121173 = 49715) (by norm_num)
theorem B941549 : Blo 626299 941549 := bbase (se 3 (by rfl) ⟨176540, by rfl⟩ : syracuseStep 941549 = 353081) (by norm_num)
theorem B941573 : Blo 626299 941573 := bbase (se 4 (by rfl) ⟨88272, by rfl⟩ : syracuseStep 941573 = 176545) (by norm_num)
theorem B941597 : Blo 626299 941597 := bbase (se 3 (by rfl) ⟨176549, by rfl⟩ : syracuseStep 941597 = 353099) (by norm_num)
theorem B941621 : Blo 626299 941621 := bbase (se 5 (by rfl) ⟨44138, by rfl⟩ : syracuseStep 941621 = 88277) (by norm_num)
theorem B1007165 : Blo 626299 1007165 := bbase (se 3 (by rfl) ⟨188843, by rfl⟩ : syracuseStep 1007165 = 377687) (by norm_num)
theorem B941645 : Blo 626299 941645 := bbase (se 3 (by rfl) ⟨176558, by rfl⟩ : syracuseStep 941645 = 353117) (by norm_num)
theorem B941669 : Blo 626299 941669 := bbase (se 4 (by rfl) ⟨88281, by rfl⟩ : syracuseStep 941669 = 176563) (by norm_num)
theorem B941693 : Blo 626299 941693 := bbase (se 3 (by rfl) ⟨176567, by rfl⟩ : syracuseStep 941693 = 353135) (by norm_num)
theorem B941717 : Blo 626299 941717 := bbase (se 6 (by rfl) ⟨22071, by rfl⟩ : syracuseStep 941717 = 44143) (by norm_num)
theorem B6053525 : Blo 626299 6053525 := bbase (se 6 (by rfl) ⟨141879, by rfl⟩ : syracuseStep 6053525 = 283759) (by norm_num)
theorem B941741 : Blo 626299 941741 := bbase (se 3 (by rfl) ⟨176576, by rfl⟩ : syracuseStep 941741 = 353153) (by norm_num)
theorem B941765 : Blo 626299 941765 := bbase (se 4 (by rfl) ⟨88290, by rfl⟩ : syracuseStep 941765 = 176581) (by norm_num)
theorem B941789 : Blo 626299 941789 := bbase (se 3 (by rfl) ⟨176585, by rfl⟩ : syracuseStep 941789 = 353171) (by norm_num)
theorem B941813 : Blo 626299 941813 := bbase (se 5 (by rfl) ⟨44147, by rfl⟩ : syracuseStep 941813 = 88295) (by norm_num)
theorem B941837 : Blo 626299 941837 := bbase (se 3 (by rfl) ⟨176594, by rfl⟩ : syracuseStep 941837 = 353189) (by norm_num)
theorem B941861 : Blo 626299 941861 := bbase (se 4 (by rfl) ⟨88299, by rfl⟩ : syracuseStep 941861 = 176599) (by norm_num)
theorem B941885 : Blo 626299 941885 := bbase (se 3 (by rfl) ⟨176603, by rfl⟩ : syracuseStep 941885 = 353207) (by norm_num)
theorem B941909 : Blo 626299 941909 := bbase (se 9 (by rfl) ⟨2759, by rfl⟩ : syracuseStep 941909 = 5519) (by norm_num)
theorem B3399509 : Blo 626299 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B941933 : Blo 626299 941933 := bbase (se 3 (by rfl) ⟨176612, by rfl⟩ : syracuseStep 941933 = 353225) (by norm_num)
theorem B941957 : Blo 626299 941957 := bbase (se 4 (by rfl) ⟨88308, by rfl⟩ : syracuseStep 941957 = 176617) (by norm_num)
theorem B2121605 : Blo 626299 2121605 := bbase (se 4 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 2121605 = 397801) (by norm_num)
theorem B2547605 : Blo 626299 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B941981 : Blo 626299 941981 := bbase (se 3 (by rfl) ⟨176621, by rfl⟩ : syracuseStep 941981 = 353243) (by norm_num)
theorem B942005 : Blo 626299 942005 := bbase (se 5 (by rfl) ⟨44156, by rfl⟩ : syracuseStep 942005 = 88313) (by norm_num)
theorem B942029 : Blo 626299 942029 := bbase (se 3 (by rfl) ⟨176630, by rfl⟩ : syracuseStep 942029 = 353261) (by norm_num)
theorem B942053 : Blo 626299 942053 := bbase (se 4 (by rfl) ⟨88317, by rfl⟩ : syracuseStep 942053 = 176635) (by norm_num)
theorem B942077 : Blo 626299 942077 := bbase (se 3 (by rfl) ⟨176639, by rfl⟩ : syracuseStep 942077 = 353279) (by norm_num)
theorem B942101 : Blo 626299 942101 := bbase (se 6 (by rfl) ⟨22080, by rfl⟩ : syracuseStep 942101 = 44161) (by norm_num)
theorem B942125 : Blo 626299 942125 := bbase (se 3 (by rfl) ⟨176648, by rfl⟩ : syracuseStep 942125 = 353297) (by norm_num)
theorem B942149 : Blo 626299 942149 := bbase (se 4 (by rfl) ⟨88326, by rfl⟩ : syracuseStep 942149 = 176653) (by norm_num)
theorem B942173 : Blo 626299 942173 := bbase (se 3 (by rfl) ⟨176657, by rfl⟩ : syracuseStep 942173 = 353315) (by norm_num)
theorem B942197 : Blo 626299 942197 := bbase (se 5 (by rfl) ⟨44165, by rfl⟩ : syracuseStep 942197 = 88331) (by norm_num)
theorem B942221 : Blo 626299 942221 := bbase (se 3 (by rfl) ⟨176666, by rfl⟩ : syracuseStep 942221 = 353333) (by norm_num)
theorem B942245 : Blo 626299 942245 := bbase (se 4 (by rfl) ⟨88335, by rfl⟩ : syracuseStep 942245 = 176671) (by norm_num)
theorem B942269 : Blo 626299 942269 := bbase (se 3 (by rfl) ⟨176675, by rfl⟩ : syracuseStep 942269 = 353351) (by norm_num)
theorem B942293 : Blo 626299 942293 := bbase (se 7 (by rfl) ⟨11042, by rfl⟩ : syracuseStep 942293 = 22085) (by norm_num)
theorem B942317 : Blo 626299 942317 := bbase (se 3 (by rfl) ⟨176684, by rfl⟩ : syracuseStep 942317 = 353369) (by norm_num)
theorem B942341 : Blo 626299 942341 := bbase (se 4 (by rfl) ⟨88344, by rfl⟩ : syracuseStep 942341 = 176689) (by norm_num)
theorem B5726485 : Blo 626299 5726485 := bbase (se 6 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 5726485 = 268429) (by norm_num)
theorem B942365 : Blo 626299 942365 := bbase (se 3 (by rfl) ⟨176693, by rfl⟩ : syracuseStep 942365 = 353387) (by norm_num)
theorem B942389 : Blo 626299 942389 := bbase (se 5 (by rfl) ⟨44174, by rfl⟩ : syracuseStep 942389 = 88349) (by norm_num)
theorem B2122037 : Blo 626299 2122037 := bbase (se 5 (by rfl) ⟨99470, by rfl⟩ : syracuseStep 2122037 = 198941) (by norm_num)
theorem B942413 : Blo 626299 942413 := bbase (se 3 (by rfl) ⟨176702, by rfl⟩ : syracuseStep 942413 = 353405) (by norm_num)
theorem B2580821 : Blo 626299 2580821 := bbase (se 10 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 2580821 = 7561) (by norm_num)
theorem B942437 : Blo 626299 942437 := bbase (se 4 (by rfl) ⟨88353, by rfl⟩ : syracuseStep 942437 = 176707) (by norm_num)
theorem B942461 : Blo 626299 942461 := bbase (se 3 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 942461 = 353423) (by norm_num)
theorem B1696133 : Blo 626299 1696133 := bbase (se 4 (by rfl) ⟨159012, by rfl⟩ : syracuseStep 1696133 = 318025) (by norm_num)
theorem B942485 : Blo 626299 942485 := bbase (se 6 (by rfl) ⟨22089, by rfl⟩ : syracuseStep 942485 = 44179) (by norm_num)
theorem B942509 : Blo 626299 942509 := bbase (se 3 (by rfl) ⟨176720, by rfl⟩ : syracuseStep 942509 = 353441) (by norm_num)
theorem B942533 : Blo 626299 942533 := bbase (se 4 (by rfl) ⟨88362, by rfl⟩ : syracuseStep 942533 = 176725) (by norm_num)
theorem B942557 : Blo 626299 942557 := bbase (se 3 (by rfl) ⟨176729, by rfl⟩ : syracuseStep 942557 = 353459) (by norm_num)
theorem B1008101 : Blo 626299 1008101 := bbase (se 4 (by rfl) ⟨94509, by rfl⟩ : syracuseStep 1008101 = 189019) (by norm_num)
theorem B942581 : Blo 626299 942581 := bbase (se 5 (by rfl) ⟨44183, by rfl⟩ : syracuseStep 942581 = 88367) (by norm_num)
theorem B942605 : Blo 626299 942605 := bbase (se 3 (by rfl) ⟨176738, by rfl⟩ : syracuseStep 942605 = 353477) (by norm_num)
theorem B942629 : Blo 626299 942629 := bbase (se 4 (by rfl) ⟨88371, by rfl⟩ : syracuseStep 942629 = 176743) (by norm_num)
theorem B2384437 : Blo 626299 2384437 := bbase (se 5 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 2384437 = 223541) (by norm_num)
theorem B942653 : Blo 626299 942653 := bbase (se 3 (by rfl) ⟨176747, by rfl⟩ : syracuseStep 942653 = 353495) (by norm_num)
theorem B942677 : Blo 626299 942677 := bbase (se 8 (by rfl) ⟨5523, by rfl⟩ : syracuseStep 942677 = 11047) (by norm_num)
theorem B942701 : Blo 626299 942701 := bbase (se 3 (by rfl) ⟨176756, by rfl⟩ : syracuseStep 942701 = 353513) (by norm_num)
theorem B942725 : Blo 626299 942725 := bbase (se 4 (by rfl) ⟨88380, by rfl⟩ : syracuseStep 942725 = 176761) (by norm_num)
theorem B942749 : Blo 626299 942749 := bbase (se 3 (by rfl) ⟨176765, by rfl⟩ : syracuseStep 942749 = 353531) (by norm_num)
theorem B942773 : Blo 626299 942773 := bbase (se 5 (by rfl) ⟨44192, by rfl⟩ : syracuseStep 942773 = 88385) (by norm_num)
theorem B942797 : Blo 626299 942797 := bbase (se 3 (by rfl) ⟨176774, by rfl⟩ : syracuseStep 942797 = 353549) (by norm_num)
theorem B5726933 : Blo 626299 5726933 := bbase (se 7 (by rfl) ⟨67112, by rfl⟩ : syracuseStep 5726933 = 134225) (by norm_num)
theorem B942821 : Blo 626299 942821 := bbase (se 4 (by rfl) ⟨88389, by rfl⟩ : syracuseStep 942821 = 176779) (by norm_num)
theorem B2122469 : Blo 626299 2122469 := bbase (se 4 (by rfl) ⟨198981, by rfl⟩ : syracuseStep 2122469 = 397963) (by norm_num)
theorem B942845 : Blo 626299 942845 := bbase (se 3 (by rfl) ⟨176783, by rfl⟩ : syracuseStep 942845 = 353567) (by norm_num)
theorem B942869 : Blo 626299 942869 := bbase (se 6 (by rfl) ⟨22098, by rfl⟩ : syracuseStep 942869 = 44197) (by norm_num)
theorem B942893 : Blo 626299 942893 := bbase (se 3 (by rfl) ⟨176792, by rfl⟩ : syracuseStep 942893 = 353585) (by norm_num)
theorem B942917 : Blo 626299 942917 := bbase (se 4 (by rfl) ⟨88398, by rfl⟩ : syracuseStep 942917 = 176797) (by norm_num)
theorem B942941 : Blo 626299 942941 := bbase (se 3 (by rfl) ⟨176801, by rfl⟩ : syracuseStep 942941 = 353603) (by norm_num)
theorem B2384741 : Blo 626299 2384741 := bbase (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) (by norm_num)
theorem B942965 : Blo 626299 942965 := bbase (se 5 (by rfl) ⟨44201, by rfl⟩ : syracuseStep 942965 = 88403) (by norm_num)
theorem B942989 : Blo 626299 942989 := bbase (se 3 (by rfl) ⟨176810, by rfl⟩ : syracuseStep 942989 = 353621) (by norm_num)
theorem B943013 : Blo 626299 943013 := bbase (se 4 (by rfl) ⟨88407, by rfl⟩ : syracuseStep 943013 = 176815) (by norm_num)
theorem B943037 : Blo 626299 943037 := bbase (se 3 (by rfl) ⟨176819, by rfl⟩ : syracuseStep 943037 = 353639) (by norm_num)
theorem B943061 : Blo 626299 943061 := bbase (se 7 (by rfl) ⟨11051, by rfl⟩ : syracuseStep 943061 = 22103) (by norm_num)
theorem B943085 : Blo 626299 943085 := bbase (se 3 (by rfl) ⟨176828, by rfl⟩ : syracuseStep 943085 = 353657) (by norm_num)
theorem B943109 : Blo 626299 943109 := bbase (se 4 (by rfl) ⟨88416, by rfl⟩ : syracuseStep 943109 = 176833) (by norm_num)
theorem B943133 : Blo 626299 943133 := bbase (se 3 (by rfl) ⟨176837, by rfl⟩ : syracuseStep 943133 = 353675) (by norm_num)
theorem B943157 : Blo 626299 943157 := bbase (se 5 (by rfl) ⟨44210, by rfl⟩ : syracuseStep 943157 = 88421) (by norm_num)
theorem B943181 : Blo 626299 943181 := bbase (se 3 (by rfl) ⟨176846, by rfl⟩ : syracuseStep 943181 = 353693) (by norm_num)
theorem B943205 : Blo 626299 943205 := bbase (se 4 (by rfl) ⟨88425, by rfl⟩ : syracuseStep 943205 = 176851) (by norm_num)
theorem B1008749 : Blo 626299 1008749 := bbase (se 3 (by rfl) ⟨189140, by rfl⟩ : syracuseStep 1008749 = 378281) (by norm_num)
theorem B943229 : Blo 626299 943229 := bbase (se 3 (by rfl) ⟨176855, by rfl⟩ : syracuseStep 943229 = 353711) (by norm_num)
theorem B943253 : Blo 626299 943253 := bbase (se 6 (by rfl) ⟨22107, by rfl⟩ : syracuseStep 943253 = 44215) (by norm_num)
theorem B2122901 : Blo 626299 2122901 := bbase (se 6 (by rfl) ⟨49755, by rfl⟩ : syracuseStep 2122901 = 99511) (by norm_num)
theorem B943277 : Blo 626299 943277 := bbase (se 3 (by rfl) ⟨176864, by rfl⟩ : syracuseStep 943277 = 353729) (by norm_num)
theorem B943301 : Blo 626299 943301 := bbase (se 4 (by rfl) ⟨88434, by rfl⟩ : syracuseStep 943301 = 176869) (by norm_num)
theorem B943325 : Blo 626299 943325 := bbase (se 3 (by rfl) ⟨176873, by rfl⟩ : syracuseStep 943325 = 353747) (by norm_num)
theorem B4515061 : Blo 626299 4515061 := bbase (se 5 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 4515061 = 423287) (by norm_num)
theorem B943349 : Blo 626299 943349 := bbase (se 5 (by rfl) ⟨44219, by rfl⟩ : syracuseStep 943349 = 88439) (by norm_num)
theorem B943373 : Blo 626299 943373 := bbase (se 3 (by rfl) ⟨176882, by rfl⟩ : syracuseStep 943373 = 353765) (by norm_num)
theorem B943397 : Blo 626299 943397 := bbase (se 4 (by rfl) ⟨88443, by rfl⟩ : syracuseStep 943397 = 176887) (by norm_num)
theorem B943421 : Blo 626299 943421 := bbase (se 3 (by rfl) ⟨176891, by rfl⟩ : syracuseStep 943421 = 353783) (by norm_num)
theorem B943445 : Blo 626299 943445 := bbase (se 12 (by rfl) ⟨345, by rfl⟩ : syracuseStep 943445 = 691) (by norm_num)
theorem B943469 : Blo 626299 943469 := bbase (se 3 (by rfl) ⟨176900, by rfl⟩ : syracuseStep 943469 = 353801) (by norm_num)
theorem B943493 : Blo 626299 943493 := bbase (se 4 (by rfl) ⟨88452, by rfl⟩ : syracuseStep 943493 = 176905) (by norm_num)
theorem B943517 : Blo 626299 943517 := bbase (se 3 (by rfl) ⟨176909, by rfl⟩ : syracuseStep 943517 = 353819) (by norm_num)
theorem B943541 : Blo 626299 943541 := bbase (se 5 (by rfl) ⟨44228, by rfl⟩ : syracuseStep 943541 = 88457) (by norm_num)
theorem B943565 : Blo 626299 943565 := bbase (se 3 (by rfl) ⟨176918, by rfl⟩ : syracuseStep 943565 = 353837) (by norm_num)
theorem B3171797 : Blo 626299 3171797 := bbase (se 7 (by rfl) ⟨37169, by rfl⟩ : syracuseStep 3171797 = 74339) (by norm_num)
theorem B943589 : Blo 626299 943589 := bbase (se 4 (by rfl) ⟨88461, by rfl⟩ : syracuseStep 943589 = 176923) (by norm_num)
theorem B943613 : Blo 626299 943613 := bbase (se 3 (by rfl) ⟨176927, by rfl⟩ : syracuseStep 943613 = 353855) (by norm_num)
theorem B943637 : Blo 626299 943637 := bbase (se 6 (by rfl) ⟨22116, by rfl⟩ : syracuseStep 943637 = 44233) (by norm_num)
theorem B943661 : Blo 626299 943661 := bbase (se 3 (by rfl) ⟨176936, by rfl⟩ : syracuseStep 943661 = 353873) (by norm_num)
theorem B943685 : Blo 626299 943685 := bbase (se 4 (by rfl) ⟨88470, by rfl⟩ : syracuseStep 943685 = 176941) (by norm_num)
theorem B2123333 : Blo 626299 2123333 := bbase (se 4 (by rfl) ⟨199062, by rfl⟩ : syracuseStep 2123333 = 398125) (by norm_num)
theorem B1697365 : Blo 626299 1697365 := bbase (se 8 (by rfl) ⟨9945, by rfl⟩ : syracuseStep 1697365 = 19891) (by norm_num)
theorem B943709 : Blo 626299 943709 := bbase (se 3 (by rfl) ⟨176945, by rfl⟩ : syracuseStep 943709 = 353891) (by norm_num)
theorem B943733 : Blo 626299 943733 := bbase (se 5 (by rfl) ⟨44237, by rfl⟩ : syracuseStep 943733 = 88475) (by norm_num)
theorem B943757 : Blo 626299 943757 := bbase (se 3 (by rfl) ⟨176954, by rfl⟩ : syracuseStep 943757 = 353909) (by norm_num)
theorem B1697429 : Blo 626299 1697429 := bbase (se 6 (by rfl) ⟨39783, by rfl⟩ : syracuseStep 1697429 = 79567) (by norm_num)
theorem B943781 : Blo 626299 943781 := bbase (se 4 (by rfl) ⟨88479, by rfl⟩ : syracuseStep 943781 = 176959) (by norm_num)
theorem B943805 : Blo 626299 943805 := bbase (se 3 (by rfl) ⟨176963, by rfl⟩ : syracuseStep 943805 = 353927) (by norm_num)
theorem B943829 : Blo 626299 943829 := bbase (se 7 (by rfl) ⟨11060, by rfl⟩ : syracuseStep 943829 = 22121) (by norm_num)
theorem B943853 : Blo 626299 943853 := bbase (se 3 (by rfl) ⟨176972, by rfl⟩ : syracuseStep 943853 = 353945) (by norm_num)
theorem B943877 : Blo 626299 943877 := bbase (se 4 (by rfl) ⟨88488, by rfl⟩ : syracuseStep 943877 = 176977) (by norm_num)
theorem B943901 : Blo 626299 943901 := bbase (se 3 (by rfl) ⟨176981, by rfl⟩ : syracuseStep 943901 = 353963) (by norm_num)
theorem B943925 : Blo 626299 943925 := bbase (se 5 (by rfl) ⟨44246, by rfl⟩ : syracuseStep 943925 = 88493) (by norm_num)
theorem B943949 : Blo 626299 943949 := bbase (se 3 (by rfl) ⟨176990, by rfl⟩ : syracuseStep 943949 = 353981) (by norm_num)
theorem B1206101 : Blo 626299 1206101 := bbase (se 9 (by rfl) ⟨3533, by rfl⟩ : syracuseStep 1206101 = 7067) (by norm_num)
theorem B943973 : Blo 626299 943973 := bbase (se 4 (by rfl) ⟨88497, by rfl⟩ : syracuseStep 943973 = 176995) (by norm_num)
theorem B943997 : Blo 626299 943997 := bbase (se 3 (by rfl) ⟨176999, by rfl⟩ : syracuseStep 943997 = 353999) (by norm_num)
theorem B944021 : Blo 626299 944021 := bbase (se 6 (by rfl) ⟨22125, by rfl⟩ : syracuseStep 944021 = 44251) (by norm_num)
theorem B944045 : Blo 626299 944045 := bbase (se 3 (by rfl) ⟨177008, by rfl⟩ : syracuseStep 944045 = 354017) (by norm_num)
theorem B944069 : Blo 626299 944069 := bbase (se 4 (by rfl) ⟨88506, by rfl⟩ : syracuseStep 944069 = 177013) (by norm_num)
theorem B944093 : Blo 626299 944093 := bbase (se 3 (by rfl) ⟨177017, by rfl⟩ : syracuseStep 944093 = 354035) (by norm_num)
theorem B2123765 : Blo 626299 2123765 := bbase (se 5 (by rfl) ⟨99551, by rfl⟩ : syracuseStep 2123765 = 199103) (by norm_num)
theorem B944117 : Blo 626299 944117 := bbase (se 5 (by rfl) ⟨44255, by rfl⟩ : syracuseStep 944117 = 88511) (by norm_num)
theorem B944141 : Blo 626299 944141 := bbase (se 3 (by rfl) ⟨177026, by rfl⟩ : syracuseStep 944141 = 354053) (by norm_num)
theorem B944165 : Blo 626299 944165 := bbase (se 4 (by rfl) ⟨88515, by rfl⟩ : syracuseStep 944165 = 177031) (by norm_num)
theorem B944189 : Blo 626299 944189 := bbase (se 3 (by rfl) ⟨177035, by rfl⟩ : syracuseStep 944189 = 354071) (by norm_num)
theorem B1435709 : Blo 626299 1435709 := bbase (se 3 (by rfl) ⟨269195, by rfl⟩ : syracuseStep 1435709 = 538391) (by norm_num)
theorem B944213 : Blo 626299 944213 := bbase (se 8 (by rfl) ⟨5532, by rfl⟩ : syracuseStep 944213 = 11065) (by norm_num)
theorem B682069 : Blo 626299 682069 := bbase (se 8 (by rfl) ⟨3996, by rfl⟩ : syracuseStep 682069 = 7993) (by norm_num)
theorem B944237 : Blo 626299 944237 := bbase (se 3 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 944237 = 354089) (by norm_num)
theorem B944261 : Blo 626299 944261 := bbase (se 4 (by rfl) ⟨88524, by rfl⟩ : syracuseStep 944261 = 177049) (by norm_num)
theorem B944285 : Blo 626299 944285 := bbase (se 3 (by rfl) ⟨177053, by rfl⟩ : syracuseStep 944285 = 354107) (by norm_num)
theorem B944309 : Blo 626299 944309 := bbase (se 5 (by rfl) ⟨44264, by rfl⟩ : syracuseStep 944309 = 88529) (by norm_num)
theorem B944333 : Blo 626299 944333 := bbase (se 3 (by rfl) ⟨177062, by rfl⟩ : syracuseStep 944333 = 354125) (by norm_num)
theorem B944357 : Blo 626299 944357 := bbase (se 4 (by rfl) ⟨88533, by rfl⟩ : syracuseStep 944357 = 177067) (by norm_num)
theorem B944381 : Blo 626299 944381 := bbase (se 3 (by rfl) ⟨177071, by rfl⟩ : syracuseStep 944381 = 354143) (by norm_num)
theorem B944405 : Blo 626299 944405 := bbase (se 6 (by rfl) ⟨22134, by rfl⟩ : syracuseStep 944405 = 44269) (by norm_num)
theorem B944429 : Blo 626299 944429 := bbase (se 3 (by rfl) ⟨177080, by rfl⟩ : syracuseStep 944429 = 354161) (by norm_num)
theorem B944453 : Blo 626299 944453 := bbase (se 4 (by rfl) ⟨88542, by rfl⟩ : syracuseStep 944453 = 177085) (by norm_num)
theorem B944477 : Blo 626299 944477 := bbase (se 3 (by rfl) ⟨177089, by rfl⟩ : syracuseStep 944477 = 354179) (by norm_num)
theorem B1272181 : Blo 626299 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B944501 : Blo 626299 944501 := bbase (se 5 (by rfl) ⟨44273, by rfl⟩ : syracuseStep 944501 = 88547) (by norm_num)
theorem B944525 : Blo 626299 944525 := bbase (se 3 (by rfl) ⟨177098, by rfl⟩ : syracuseStep 944525 = 354197) (by norm_num)
theorem B2124197 : Blo 626299 2124197 := bbase (se 4 (by rfl) ⟨199143, by rfl⟩ : syracuseStep 2124197 = 398287) (by norm_num)
theorem B944549 : Blo 626299 944549 := bbase (se 4 (by rfl) ⟨88551, by rfl⟩ : syracuseStep 944549 = 177103) (by norm_num)
theorem B944573 : Blo 626299 944573 := bbase (se 3 (by rfl) ⟨177107, by rfl⟩ : syracuseStep 944573 = 354215) (by norm_num)
theorem B944597 : Blo 626299 944597 := bbase (se 7 (by rfl) ⟨11069, by rfl⟩ : syracuseStep 944597 = 22139) (by norm_num)
theorem B944621 : Blo 626299 944621 := bbase (se 3 (by rfl) ⟨177116, by rfl⟩ : syracuseStep 944621 = 354233) (by norm_num)
theorem B944645 : Blo 626299 944645 := bbase (se 4 (by rfl) ⟨88560, by rfl⟩ : syracuseStep 944645 = 177121) (by norm_num)
theorem B944669 : Blo 626299 944669 := bbase (se 3 (by rfl) ⟨177125, by rfl⟩ : syracuseStep 944669 = 354251) (by norm_num)
theorem B2419253 : Blo 626299 2419253 := bbase (se 5 (by rfl) ⟨113402, by rfl⟩ : syracuseStep 2419253 = 226805) (by norm_num)
theorem B944693 : Blo 626299 944693 := bbase (se 5 (by rfl) ⟨44282, by rfl⟩ : syracuseStep 944693 = 88565) (by norm_num)
theorem B1436221 : Blo 626299 1436221 := bbase (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) (by norm_num)
theorem B944717 : Blo 626299 944717 := bbase (se 3 (by rfl) ⟨177134, by rfl⟩ : syracuseStep 944717 = 354269) (by norm_num)
theorem B944741 : Blo 626299 944741 := bbase (se 4 (by rfl) ⟨88569, by rfl⟩ : syracuseStep 944741 = 177139) (by norm_num)
theorem B944765 : Blo 626299 944765 := bbase (se 3 (by rfl) ⟨177143, by rfl⟩ : syracuseStep 944765 = 354287) (by norm_num)
theorem B944789 : Blo 626299 944789 := bbase (se 6 (by rfl) ⟨22143, by rfl⟩ : syracuseStep 944789 = 44287) (by norm_num)
theorem B944813 : Blo 626299 944813 := bbase (se 3 (by rfl) ⟨177152, by rfl⟩ : syracuseStep 944813 = 354305) (by norm_num)
theorem B944837 : Blo 626299 944837 := bbase (se 4 (by rfl) ⟨88578, by rfl⟩ : syracuseStep 944837 = 177157) (by norm_num)
theorem B944861 : Blo 626299 944861 := bbase (se 3 (by rfl) ⟨177161, by rfl⟩ : syracuseStep 944861 = 354323) (by norm_num)
theorem B3173093 : Blo 626299 3173093 := bbase (se 4 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 3173093 = 594955) (by norm_num)
theorem B715501 : Blo 626299 715501 := bbase (se 3 (by rfl) ⟨134156, by rfl⟩ : syracuseStep 715501 = 268313) (by norm_num)
theorem B944885 : Blo 626299 944885 := bbase (se 5 (by rfl) ⟨44291, by rfl⟩ : syracuseStep 944885 = 88583) (by norm_num)
theorem B944909 : Blo 626299 944909 := bbase (se 3 (by rfl) ⟨177170, by rfl⟩ : syracuseStep 944909 = 354341) (by norm_num)
theorem B944933 : Blo 626299 944933 := bbase (se 4 (by rfl) ⟨88587, by rfl⟩ : syracuseStep 944933 = 177175) (by norm_num)
theorem B944957 : Blo 626299 944957 := bbase (se 3 (by rfl) ⟨177179, by rfl⟩ : syracuseStep 944957 = 354359) (by norm_num)
theorem B4778837 : Blo 626299 4778837 := bbase (se 9 (by rfl) ⟨14000, by rfl⟩ : syracuseStep 4778837 = 28001) (by norm_num)
theorem B2124629 : Blo 626299 2124629 := bbase (se 9 (by rfl) ⟨6224, by rfl⟩ : syracuseStep 2124629 = 12449) (by norm_num)
theorem B944981 : Blo 626299 944981 := bbase (se 9 (by rfl) ⟨2768, by rfl⟩ : syracuseStep 944981 = 5537) (by norm_num)
theorem B945005 : Blo 626299 945005 := bbase (se 3 (by rfl) ⟨177188, by rfl⟩ : syracuseStep 945005 = 354377) (by norm_num)
theorem B945029 : Blo 626299 945029 := bbase (se 4 (by rfl) ⟨88596, by rfl⟩ : syracuseStep 945029 = 177193) (by norm_num)
theorem B945053 : Blo 626299 945053 := bbase (se 3 (by rfl) ⟨177197, by rfl⟩ : syracuseStep 945053 = 354395) (by norm_num)
theorem B2386853 : Blo 626299 2386853 := bbase (se 4 (by rfl) ⟨223767, by rfl⟩ : syracuseStep 2386853 = 447535) (by norm_num)
theorem B945077 : Blo 626299 945077 := bbase (se 5 (by rfl) ⟨44300, by rfl⟩ : syracuseStep 945077 = 88601) (by norm_num)
theorem B945101 : Blo 626299 945101 := bbase (se 3 (by rfl) ⟨177206, by rfl⟩ : syracuseStep 945101 = 354413) (by norm_num)
theorem B945125 : Blo 626299 945125 := bbase (se 4 (by rfl) ⟨88605, by rfl⟩ : syracuseStep 945125 = 177211) (by norm_num)
theorem B945149 : Blo 626299 945149 := bbase (se 3 (by rfl) ⟨177215, by rfl⟩ : syracuseStep 945149 = 354431) (by norm_num)
theorem B10185749 : Blo 626299 10185749 := bbase (se 6 (by rfl) ⟨238728, by rfl⟩ : syracuseStep 10185749 = 477457) (by norm_num)
theorem B945173 : Blo 626299 945173 := bbase (se 6 (by rfl) ⟨22152, by rfl⟩ : syracuseStep 945173 = 44305) (by norm_num)
theorem B945197 : Blo 626299 945197 := bbase (se 3 (by rfl) ⟨177224, by rfl⟩ : syracuseStep 945197 = 354449) (by norm_num)
theorem B1338437 : Blo 626299 1338437 := bbase (se 4 (by rfl) ⟨125478, by rfl⟩ : syracuseStep 1338437 = 250957) (by norm_num)
theorem B945221 : Blo 626299 945221 := bbase (se 4 (by rfl) ⟨88614, by rfl⟩ : syracuseStep 945221 = 177229) (by norm_num)
theorem B945245 : Blo 626299 945245 := bbase (se 3 (by rfl) ⟨177233, by rfl⟩ : syracuseStep 945245 = 354467) (by norm_num)
theorem B5368949 : Blo 626299 5368949 := bbase (se 5 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 5368949 = 503339) (by norm_num)
theorem B945269 : Blo 626299 945269 := bbase (se 5 (by rfl) ⟨44309, by rfl⟩ : syracuseStep 945269 = 88619) (by norm_num)
theorem B945293 : Blo 626299 945293 := bbase (se 3 (by rfl) ⟨177242, by rfl⟩ : syracuseStep 945293 = 354485) (by norm_num)
theorem B945317 : Blo 626299 945317 := bbase (se 4 (by rfl) ⟨88623, by rfl⟩ : syracuseStep 945317 = 177247) (by norm_num)
theorem B945341 : Blo 626299 945341 := bbase (se 3 (by rfl) ⟨177251, by rfl⟩ : syracuseStep 945341 = 354503) (by norm_num)
theorem B2387141 : Blo 626299 2387141 := bbase (se 4 (by rfl) ⟨223794, by rfl⟩ : syracuseStep 2387141 = 447589) (by norm_num)
theorem B1338581 : Blo 626299 1338581 := bbase (se 7 (by rfl) ⟨15686, by rfl⟩ : syracuseStep 1338581 = 31373) (by norm_num)
theorem B945365 : Blo 626299 945365 := bbase (se 7 (by rfl) ⟨11078, by rfl⟩ : syracuseStep 945365 = 22157) (by norm_num)
theorem B945389 : Blo 626299 945389 := bbase (se 3 (by rfl) ⟨177260, by rfl⟩ : syracuseStep 945389 = 354521) (by norm_num)
theorem B2125061 : Blo 626299 2125061 := bbase (se 4 (by rfl) ⟨199224, by rfl⟩ : syracuseStep 2125061 = 398449) (by norm_num)
theorem B945413 : Blo 626299 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B945437 : Blo 626299 945437 := bbase (se 3 (by rfl) ⟨177269, by rfl⟩ : syracuseStep 945437 = 354539) (by norm_num)
theorem B847309 : Blo 626299 847309 := bbase (se 3 (by rfl) ⟨158870, by rfl⟩ : syracuseStep 847309 = 317741) (by norm_num)
theorem B2682341 : Blo 626299 2682341 := bbase (se 4 (by rfl) ⟨251469, by rfl⟩ : syracuseStep 2682341 = 502939) (by norm_num)
theorem B2125493 : Blo 626299 2125493 := bbase (se 5 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 2125493 = 199265) (by norm_num)
theorem B2682629 : Blo 626299 2682629 := bbase (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) (by norm_num)
theorem B1339325 : Blo 626299 1339325 := bbase (se 3 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 1339325 = 502247) (by norm_num)
theorem B3174389 : Blo 626299 3174389 := bbase (se 5 (by rfl) ⟨148799, by rfl⟩ : syracuseStep 3174389 = 297599) (by norm_num)
theorem B716833 : Blo 626299 716833 := bbase (se 2 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 716833 = 537625) (by norm_num)
theorem B2125925 : Blo 626299 2125925 := bbase (se 4 (by rfl) ⟨199305, by rfl⟩ : syracuseStep 2125925 = 398611) (by norm_num)
theorem B1273981 : Blo 626299 1273981 := bbase (se 3 (by rfl) ⟨238871, by rfl⟩ : syracuseStep 1273981 = 477743) (by norm_num)
theorem B2388325 : Blo 626299 2388325 := bbase (se 4 (by rfl) ⟨223905, by rfl⟩ : syracuseStep 2388325 = 447811) (by norm_num)
theorem B717161 : Blo 626299 717161 := bbase (se 2 (by rfl) ⟨268935, by rfl⟩ : syracuseStep 717161 = 537871) (by norm_num)
theorem B2585029 : Blo 626299 2585029 := bbase (se 4 (by rfl) ⟨242346, by rfl⟩ : syracuseStep 2585029 = 484693) (by norm_num)
theorem B2683381 : Blo 626299 2683381 := bbase (se 5 (by rfl) ⟨125783, by rfl⟩ : syracuseStep 2683381 = 251567) (by norm_num)
theorem B2126357 : Blo 626299 2126357 := bbase (se 6 (by rfl) ⟨49836, by rfl⟩ : syracuseStep 2126357 = 99673) (by norm_num)
theorem B1208981 : Blo 626299 1208981 := bbase (se 6 (by rfl) ⟨28335, by rfl⟩ : syracuseStep 1208981 = 56671) (by norm_num)
theorem B2388629 : Blo 626299 2388629 := bbase (se 6 (by rfl) ⟨55983, by rfl⟩ : syracuseStep 2388629 = 111967) (by norm_num)
theorem B1340077 : Blo 626299 1340077 := bbase (se 3 (by rfl) ⟨251264, by rfl⟩ : syracuseStep 1340077 = 502529) (by norm_num)
theorem B717545 : Blo 626299 717545 := bbase (se 2 (by rfl) ⟨269079, by rfl⟩ : syracuseStep 717545 = 538159) (by norm_num)
theorem B1340221 : Blo 626299 1340221 := bbase (se 3 (by rfl) ⟨251291, by rfl⟩ : syracuseStep 1340221 = 502583) (by norm_num)
theorem B2126789 : Blo 626299 2126789 := bbase (se 4 (by rfl) ⟨199386, by rfl⟩ : syracuseStep 2126789 = 398773) (by norm_num)
theorem B1340597 : Blo 626299 1340597 := bbase (se 5 (by rfl) ⟨62840, by rfl⟩ : syracuseStep 1340597 = 125681) (by norm_num)
theorem B2684117 : Blo 626299 2684117 := bbase (se 7 (by rfl) ⟨31454, by rfl⟩ : syracuseStep 2684117 = 62909) (by norm_num)
theorem B3175685 : Blo 626299 3175685 := bbase (se 4 (by rfl) ⟨297720, by rfl⟩ : syracuseStep 3175685 = 595441) (by norm_num)
theorem B2127221 : Blo 626299 2127221 := bbase (se 5 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 2127221 = 199427) (by norm_num)
theorem B1340965 : Blo 626299 1340965 := bbase (se 4 (by rfl) ⟨125715, by rfl⟩ : syracuseStep 1340965 = 251431) (by norm_num)
theorem B1504925 : Blo 626299 1504925 := bbase (se 3 (by rfl) ⟨282173, by rfl⟩ : syracuseStep 1504925 = 564347) (by norm_num)
theorem B1504981 : Blo 626299 1504981 := bbase (se 7 (by rfl) ⟨17636, by rfl⟩ : syracuseStep 1504981 = 35273) (by norm_num)
theorem B2258741 : Blo 626299 2258741 := bbase (se 5 (by rfl) ⟨105878, by rfl⟩ : syracuseStep 2258741 = 211757) (by norm_num)
theorem B718657 : Blo 626299 718657 := bbase (se 2 (by rfl) ⟨269496, by rfl⟩ : syracuseStep 718657 = 538993) (by norm_num)
theorem B1505213 : Blo 626299 1505213 := bbase (se 3 (by rfl) ⟨282227, by rfl⟩ : syracuseStep 1505213 = 564455) (by norm_num)
theorem B2259029 : Blo 626299 2259029 := bbase (se 8 (by rfl) ⟨13236, by rfl⟩ : syracuseStep 2259029 = 26473) (by norm_num)
theorem B1505405 : Blo 626299 1505405 := bbase (se 3 (by rfl) ⟨282263, by rfl⟩ : syracuseStep 1505405 = 564527) (by norm_num)
theorem B1145029 : Blo 626299 1145029 := bbase (se 4 (by rfl) ⟨107346, by rfl⟩ : syracuseStep 1145029 = 214693) (by norm_num)
theorem B2685349 : Blo 626299 2685349 := bbase (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) (by norm_num)
theorem B3176981 : Blo 626299 3176981 := bbase (se 6 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 3176981 = 148921) (by norm_num)
theorem B1276445 : Blo 626299 1276445 := bbase (se 3 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 1276445 = 478667) (by norm_num)
theorem B2390741 : Blo 626299 2390741 := bbase (se 7 (by rfl) ⟨28016, by rfl⟩ : syracuseStep 2390741 = 56033) (by norm_num)
theorem B4029173 : Blo 626299 4029173 := bbase (se 5 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 4029173 = 377735) (by norm_num)
theorem B4193045 : Blo 626299 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B2391029 : Blo 626299 2391029 := bbase (se 5 (by rfl) ⟨112079, by rfl⟩ : syracuseStep 2391029 = 224159) (by norm_num)
theorem B1342469 : Blo 626299 1342469 := bbase (se 4 (by rfl) ⟨125856, by rfl⟩ : syracuseStep 1342469 = 251713) (by norm_num)
theorem B1506365 : Blo 626299 1506365 := bbase (se 3 (by rfl) ⟨282443, by rfl⟩ : syracuseStep 1506365 = 564887) (by norm_num)
theorem B1277029 : Blo 626299 1277029 := bbase (se 4 (by rfl) ⟨119721, by rfl⟩ : syracuseStep 1277029 = 239443) (by norm_num)
theorem B1342613 : Blo 626299 1342613 := bbase (se 6 (by rfl) ⟨31467, by rfl⟩ : syracuseStep 1342613 = 62935) (by norm_num)
theorem B1211581 : Blo 626299 1211581 := bbase (se 3 (by rfl) ⟨227171, by rfl⟩ : syracuseStep 1211581 = 454343) (by norm_num)
theorem B752909 : Blo 626299 752909 := bbase (se 3 (by rfl) ⟨141170, by rfl⟩ : syracuseStep 752909 = 282341) (by norm_num)
theorem B752933 : Blo 626299 752933 := bbase (se 4 (by rfl) ⟨70587, by rfl⟩ : syracuseStep 752933 = 141175) (by norm_num)
theorem B7142741 : Blo 626299 7142741 := bbase (se 11 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 7142741 = 10463) (by norm_num)
theorem B2751877 : Blo 626299 2751877 := bbase (se 4 (by rfl) ⟨257988, by rfl⟩ : syracuseStep 2751877 = 515977) (by norm_num)
theorem B1342973 : Blo 626299 1342973 := bbase (se 3 (by rfl) ⟨251807, by rfl⟩ : syracuseStep 1342973 = 503615) (by norm_num)
theorem B753241 : Blo 626299 753241 := bbase (se 2 (by rfl) ⟨282465, by rfl⟩ : syracuseStep 753241 = 564931) (by norm_num)
theorem B753413 : Blo 626299 753413 := bbase (se 4 (by rfl) ⟨70632, by rfl⟩ : syracuseStep 753413 = 141265) (by norm_num)
theorem B3014405 : Blo 626299 3014405 := bbase (se 4 (by rfl) ⟨282600, by rfl⟩ : syracuseStep 3014405 = 565201) (by norm_num)
theorem B3178277 : Blo 626299 3178277 := bbase (se 4 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 3178277 = 595927) (by norm_num)
theorem B753529 : Blo 626299 753529 := bbase (se 2 (by rfl) ⟨282573, by rfl⟩ : syracuseStep 753529 = 565147) (by norm_num)
theorem B753625 : Blo 626299 753625 := bbase (se 2 (by rfl) ⟨282609, by rfl⟩ : syracuseStep 753625 = 565219) (by norm_num)
theorem B52396145 : Blo 626299 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B1409201 : Blo 626299 1409201 := bstep (se 2 (by rfl) ⟨528450, by rfl⟩ : syracuseStep 1409201 = 1056901) B1056901
theorem B1409219 : Blo 626299 1409219 := bstep (se 1 (by rfl) ⟨1056914, by rfl⟩ : syracuseStep 1409219 = 2113829) B2113829
theorem B5505221 : Blo 626299 5505221 := bstep (se 4 (by rfl) ⟨516114, by rfl⟩ : syracuseStep 5505221 = 1032229) B1032229
theorem B7635313 : Blo 626299 7635313 := bstep (se 2 (by rfl) ⟨2863242, by rfl⟩ : syracuseStep 7635313 = 5726485) B5726485
theorem B5374349 : Blo 626299 5374349 := bstep (se 3 (by rfl) ⟨1007690, by rfl⟩ : syracuseStep 5374349 = 2015381) B2015381
theorem B754067 : Blo 626299 754067 := bstep (se 1 (by rfl) ⟨565550, by rfl⟩ : syracuseStep 754067 = 1131101) B1131101
theorem B6029765 : Blo 626299 6029765 := bstep (se 4 (by rfl) ⟨565290, by rfl⟩ : syracuseStep 6029765 = 1130581) B1130581
theorem B1409489 : Blo 626299 1409489 := bstep (se 2 (by rfl) ⟨528558, by rfl⟩ : syracuseStep 1409489 = 1057117) B1057117
theorem B1409507 : Blo 626299 1409507 := bstep (se 1 (by rfl) ⟨1057130, by rfl⟩ : syracuseStep 1409507 = 2114261) B2114261
theorem B27984611 : Blo 626299 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B1409777 : Blo 626299 1409777 := bstep (se 2 (by rfl) ⟨528666, by rfl⟩ : syracuseStep 1409777 = 1057333) B1057333
theorem B3179249 : Blo 626299 3179249 := bstep (se 2 (by rfl) ⟨1192218, by rfl⟩ : syracuseStep 3179249 = 2384437) B2384437
theorem B1409795 : Blo 626299 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B2392973 : Blo 626299 2392973 := bstep (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) B897365
theorem B1344451 : Blo 626299 1344451 := bstep (se 1 (by rfl) ⟨1008338, by rfl⟩ : syracuseStep 1344451 = 2016677) B2016677
theorem B1410065 : Blo 626299 1410065 := bstep (se 2 (by rfl) ⟨528774, by rfl⟩ : syracuseStep 1410065 = 1057549) B1057549
theorem B1410083 : Blo 626299 1410083 := bstep (se 1 (by rfl) ⟨1057562, by rfl⟩ : syracuseStep 1410083 = 2115125) B2115125
theorem B1410353 : Blo 626299 1410353 := bstep (se 2 (by rfl) ⟨528882, by rfl⟩ : syracuseStep 1410353 = 1057765) B1057765
theorem B2721073 : Blo 626299 2721073 := bstep (se 2 (by rfl) ⟨1020402, by rfl⟩ : syracuseStep 2721073 = 2040805) B2040805
theorem B1410371 : Blo 626299 1410371 := bstep (se 1 (by rfl) ⟨1057778, by rfl⟩ : syracuseStep 1410371 = 2115557) B2115557
theorem B1017265 : Blo 626299 1017265 := bstep (se 2 (by rfl) ⟨381474, by rfl⟩ : syracuseStep 1017265 = 762949) B762949
theorem B2721293 : Blo 626299 2721293 := bstep (se 3 (by rfl) ⟨510242, by rfl⟩ : syracuseStep 2721293 = 1020485) B1020485
theorem B1410641 : Blo 626299 1410641 := bstep (se 2 (by rfl) ⟨528990, by rfl⟩ : syracuseStep 1410641 = 1057981) B1057981
theorem B1410659 : Blo 626299 1410659 := bstep (se 1 (by rfl) ⟨1057994, by rfl⟩ : syracuseStep 1410659 = 2115989) B2115989
theorem B2262691 : Blo 626299 2262691 := bstep (se 1 (by rfl) ⟨1697018, by rfl⟩ : syracuseStep 2262691 = 3394037) B3394037
theorem B1410929 : Blo 626299 1410929 := bstep (se 2 (by rfl) ⟨529098, by rfl⟩ : syracuseStep 1410929 = 1058197) B1058197
theorem B1410947 : Blo 626299 1410947 := bstep (se 1 (by rfl) ⟨1058210, by rfl⟩ : syracuseStep 1410947 = 2116421) B2116421
theorem B5736419 : Blo 626299 5736419 := bstep (se 1 (by rfl) ⟨4302314, by rfl⟩ : syracuseStep 5736419 = 8604629) B8604629
theorem B2263153 : Blo 626299 2263153 := bstep (se 2 (by rfl) ⟨848682, by rfl⟩ : syracuseStep 2263153 = 1697365) B1697365
theorem B1411217 : Blo 626299 1411217 := bstep (se 2 (by rfl) ⟨529206, by rfl⟩ : syracuseStep 1411217 = 1058413) B1058413
theorem B1411235 : Blo 626299 1411235 := bstep (se 1 (by rfl) ⟨1058426, by rfl⟩ : syracuseStep 1411235 = 2116853) B2116853
theorem B3180707 : Blo 626299 3180707 := bstep (se 1 (by rfl) ⟨2385530, by rfl⟩ : syracuseStep 3180707 = 4771061) B4771061
theorem B1018049 : Blo 626299 1018049 := bstep (se 2 (by rfl) ⟨381768, by rfl⟩ : syracuseStep 1018049 = 763537) B763537
theorem B1411505 : Blo 626299 1411505 := bstep (se 2 (by rfl) ⟨529314, by rfl⟩ : syracuseStep 1411505 = 1058629) B1058629
theorem B1411523 : Blo 626299 1411523 := bstep (se 1 (by rfl) ⟨1058642, by rfl⟩ : syracuseStep 1411523 = 2117285) B2117285
theorem B4032965 : Blo 626299 4032965 := bstep (se 4 (by rfl) ⟨378090, by rfl⟩ : syracuseStep 4032965 = 756181) B756181
theorem B3213923 : Blo 626299 3213923 := bstep (se 1 (by rfl) ⟨2410442, by rfl⟩ : syracuseStep 3213923 = 4820885) B4820885
theorem B3574469 : Blo 626299 3574469 := bstep (se 4 (by rfl) ⟨335106, by rfl⟩ : syracuseStep 3574469 = 670213) B670213
theorem B1411793 : Blo 626299 1411793 := bstep (se 2 (by rfl) ⟨529422, by rfl⟩ : syracuseStep 1411793 = 1058845) B1058845
theorem B1411811 : Blo 626299 1411811 := bstep (se 1 (by rfl) ⟨1058858, by rfl⟩ : syracuseStep 1411811 = 2117717) B2117717
theorem B5376739 : Blo 626299 5376739 := bstep (se 1 (by rfl) ⟨4032554, by rfl⟩ : syracuseStep 5376739 = 8065109) B8065109
theorem B4295501 : Blo 626299 4295501 := bstep (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) B1610813
theorem B756643 : Blo 626299 756643 := bstep (se 1 (by rfl) ⟨567482, by rfl⟩ : syracuseStep 756643 = 1134965) B1134965
theorem B3181517 : Blo 626299 3181517 := bstep (se 3 (by rfl) ⟨596534, by rfl⟩ : syracuseStep 3181517 = 1193069) B1193069
theorem B1412081 : Blo 626299 1412081 := bstep (se 2 (by rfl) ⟨529530, by rfl⟩ : syracuseStep 1412081 = 1059061) B1059061
theorem B1412099 : Blo 626299 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B2690147 : Blo 626299 2690147 := bstep (se 1 (by rfl) ⟨2017610, by rfl⟩ : syracuseStep 2690147 = 4035221) B4035221
theorem B3574925 : Blo 626299 3574925 := bstep (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) B1340597
theorem B1510595 : Blo 626299 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B1412369 : Blo 626299 1412369 := bstep (se 2 (by rfl) ⟨529638, by rfl⟩ : syracuseStep 1412369 = 1059277) B1059277
theorem B1412387 : Blo 626299 1412387 := bstep (se 1 (by rfl) ⟨1059290, by rfl⟩ : syracuseStep 1412387 = 2118581) B2118581
theorem B757027 : Blo 626299 757027 := bstep (se 1 (by rfl) ⟨567770, by rfl⟩ : syracuseStep 757027 = 1135541) B1135541
theorem B1510787 : Blo 626299 1510787 := bstep (se 1 (by rfl) ⟨1133090, by rfl⟩ : syracuseStep 1510787 = 2266181) B2266181
theorem B4525553 : Blo 626299 4525553 := bstep (se 2 (by rfl) ⟨1697082, by rfl⟩ : syracuseStep 4525553 = 3394165) B3394165
theorem B1412657 : Blo 626299 1412657 := bstep (se 2 (by rfl) ⟨529746, by rfl⟩ : syracuseStep 1412657 = 1059493) B1059493
theorem B1412675 : Blo 626299 1412675 := bstep (se 1 (by rfl) ⟨1059506, by rfl⟩ : syracuseStep 1412675 = 2119013) B2119013
theorem B626307 : Blo 626299 626307 := bstep (se 1 (by rfl) ⟨469730, by rfl⟩ : syracuseStep 626307 = 939461) B939461
theorem B954001 : Blo 626299 954001 := bstep (se 2 (by rfl) ⟨357750, by rfl⟩ : syracuseStep 954001 = 715501) B715501
theorem B626323 : Blo 626299 626323 := bstep (se 1 (by rfl) ⟨469742, by rfl⟩ : syracuseStep 626323 = 939485) B939485
theorem B626339 : Blo 626299 626339 := bstep (se 1 (by rfl) ⟨469754, by rfl⟩ : syracuseStep 626339 = 939509) B939509
theorem B1511075 : Blo 626299 1511075 := bstep (se 1 (by rfl) ⟨1133306, by rfl⟩ : syracuseStep 1511075 = 2266613) B2266613
theorem B626355 : Blo 626299 626355 := bstep (se 1 (by rfl) ⟨469766, by rfl⟩ : syracuseStep 626355 = 939533) B939533
theorem B626371 : Blo 626299 626371 := bstep (se 1 (by rfl) ⟨469778, by rfl⟩ : syracuseStep 626371 = 939557) B939557
theorem B626387 : Blo 626299 626387 := bstep (se 1 (by rfl) ⟨469790, by rfl⟩ : syracuseStep 626387 = 939581) B939581
theorem B626403 : Blo 626299 626403 := bstep (se 1 (by rfl) ⟨469802, by rfl⟩ : syracuseStep 626403 = 939605) B939605
theorem B12095203 : Blo 626299 12095203 := bstep (se 1 (by rfl) ⟨9071402, by rfl⟩ : syracuseStep 12095203 = 18142805) B18142805
theorem B626419 : Blo 626299 626419 := bstep (se 1 (by rfl) ⟨469814, by rfl⟩ : syracuseStep 626419 = 939629) B939629
theorem B626435 : Blo 626299 626435 := bstep (se 1 (by rfl) ⟨469826, by rfl⟩ : syracuseStep 626435 = 939653) B939653
theorem B626451 : Blo 626299 626451 := bstep (se 1 (by rfl) ⟨469838, by rfl⟩ : syracuseStep 626451 = 939677) B939677
theorem B626467 : Blo 626299 626467 := bstep (se 1 (by rfl) ⟨469850, by rfl⟩ : syracuseStep 626467 = 939701) B939701
theorem B626483 : Blo 626299 626483 := bstep (se 1 (by rfl) ⟨469862, by rfl⟩ : syracuseStep 626483 = 939725) B939725
theorem B626499 : Blo 626299 626499 := bstep (se 1 (by rfl) ⟨469874, by rfl⟩ : syracuseStep 626499 = 939749) B939749
theorem B1412945 : Blo 626299 1412945 := bstep (se 2 (by rfl) ⟨529854, by rfl⟩ : syracuseStep 1412945 = 1059709) B1059709
theorem B626515 : Blo 626299 626515 := bstep (se 1 (by rfl) ⟨469886, by rfl⟩ : syracuseStep 626515 = 939773) B939773
theorem B626531 : Blo 626299 626531 := bstep (se 1 (by rfl) ⟨469898, by rfl⟩ : syracuseStep 626531 = 939797) B939797
theorem B1412963 : Blo 626299 1412963 := bstep (se 1 (by rfl) ⟨1059722, by rfl⟩ : syracuseStep 1412963 = 2119445) B2119445
theorem B626547 : Blo 626299 626547 := bstep (se 1 (by rfl) ⟨469910, by rfl⟩ : syracuseStep 626547 = 939821) B939821
theorem B626563 : Blo 626299 626563 := bstep (se 1 (by rfl) ⟨469922, by rfl⟩ : syracuseStep 626563 = 939845) B939845
theorem B626579 : Blo 626299 626579 := bstep (se 1 (by rfl) ⟨469934, by rfl⟩ : syracuseStep 626579 = 939869) B939869
theorem B626595 : Blo 626299 626595 := bstep (se 1 (by rfl) ⟨469946, by rfl⟩ : syracuseStep 626595 = 939893) B939893
theorem B626611 : Blo 626299 626611 := bstep (se 1 (by rfl) ⟨469958, by rfl⟩ : syracuseStep 626611 = 939917) B939917
theorem B626627 : Blo 626299 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B626643 : Blo 626299 626643 := bstep (se 1 (by rfl) ⟨469982, by rfl⟩ : syracuseStep 626643 = 939965) B939965
theorem B626659 : Blo 626299 626659 := bstep (se 1 (by rfl) ⟨469994, by rfl⟩ : syracuseStep 626659 = 939989) B939989
theorem B626675 : Blo 626299 626675 := bstep (se 1 (by rfl) ⟨470006, by rfl⟩ : syracuseStep 626675 = 940013) B940013
theorem B626691 : Blo 626299 626691 := bstep (se 1 (by rfl) ⟨470018, by rfl⟩ : syracuseStep 626691 = 940037) B940037
theorem B626707 : Blo 626299 626707 := bstep (se 1 (by rfl) ⟨470030, by rfl⟩ : syracuseStep 626707 = 940061) B940061
theorem B626723 : Blo 626299 626723 := bstep (se 1 (by rfl) ⟨470042, by rfl⟩ : syracuseStep 626723 = 940085) B940085
theorem B626739 : Blo 626299 626739 := bstep (se 1 (by rfl) ⟨470054, by rfl⟩ : syracuseStep 626739 = 940109) B940109
theorem B626755 : Blo 626299 626755 := bstep (se 1 (by rfl) ⟨470066, by rfl⟩ : syracuseStep 626755 = 940133) B940133
theorem B626771 : Blo 626299 626771 := bstep (se 1 (by rfl) ⟨470078, by rfl⟩ : syracuseStep 626771 = 940157) B940157
theorem B626787 : Blo 626299 626787 := bstep (se 1 (by rfl) ⟨470090, by rfl⟩ : syracuseStep 626787 = 940181) B940181
theorem B1413233 : Blo 626299 1413233 := bstep (se 2 (by rfl) ⟨529962, by rfl⟩ : syracuseStep 1413233 = 1059925) B1059925
theorem B626803 : Blo 626299 626803 := bstep (se 1 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 626803 = 940205) B940205
theorem B626819 : Blo 626299 626819 := bstep (se 1 (by rfl) ⟨470114, by rfl⟩ : syracuseStep 626819 = 940229) B940229
theorem B1413251 : Blo 626299 1413251 := bstep (se 1 (by rfl) ⟨1059938, by rfl⟩ : syracuseStep 1413251 = 2119877) B2119877
theorem B626835 : Blo 626299 626835 := bstep (se 1 (by rfl) ⟨470126, by rfl⟩ : syracuseStep 626835 = 940253) B940253
theorem B626851 : Blo 626299 626851 := bstep (se 1 (by rfl) ⟨470138, by rfl⟩ : syracuseStep 626851 = 940277) B940277
theorem B626867 : Blo 626299 626867 := bstep (se 1 (by rfl) ⟨470150, by rfl⟩ : syracuseStep 626867 = 940301) B940301
theorem B6787253 : Blo 626299 6787253 := bstep (se 5 (by rfl) ⟨318152, by rfl⟩ : syracuseStep 6787253 = 636305) B636305
theorem B626883 : Blo 626299 626883 := bstep (se 1 (by rfl) ⟨470162, by rfl⟩ : syracuseStep 626883 = 940325) B940325
theorem B626899 : Blo 626299 626899 := bstep (se 1 (by rfl) ⟨470174, by rfl⟩ : syracuseStep 626899 = 940349) B940349
theorem B1904867 : Blo 626299 1904867 := bstep (se 1 (by rfl) ⟨1428650, by rfl⟩ : syracuseStep 1904867 = 2857301) B2857301
theorem B626915 : Blo 626299 626915 := bstep (se 1 (by rfl) ⟨470186, by rfl⟩ : syracuseStep 626915 = 940373) B940373
theorem B626931 : Blo 626299 626931 := bstep (se 1 (by rfl) ⟨470198, by rfl⟩ : syracuseStep 626931 = 940397) B940397
theorem B626947 : Blo 626299 626947 := bstep (se 1 (by rfl) ⟨470210, by rfl⟩ : syracuseStep 626947 = 940421) B940421
theorem B626963 : Blo 626299 626963 := bstep (se 1 (by rfl) ⟨470222, by rfl⟩ : syracuseStep 626963 = 940445) B940445
theorem B626979 : Blo 626299 626979 := bstep (se 1 (by rfl) ⟨470234, by rfl⟩ : syracuseStep 626979 = 940469) B940469
theorem B2691377 : Blo 626299 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B626995 : Blo 626299 626995 := bstep (se 1 (by rfl) ⟨470246, by rfl⟩ : syracuseStep 626995 = 940493) B940493
theorem B627011 : Blo 626299 627011 := bstep (se 1 (by rfl) ⟨470258, by rfl⟩ : syracuseStep 627011 = 940517) B940517
theorem B627027 : Blo 626299 627027 := bstep (se 1 (by rfl) ⟨470270, by rfl⟩ : syracuseStep 627027 = 940541) B940541
theorem B627043 : Blo 626299 627043 := bstep (se 1 (by rfl) ⟨470282, by rfl⟩ : syracuseStep 627043 = 940565) B940565
theorem B627059 : Blo 626299 627059 := bstep (se 1 (by rfl) ⟨470294, by rfl⟩ : syracuseStep 627059 = 940589) B940589
theorem B627075 : Blo 626299 627075 := bstep (se 1 (by rfl) ⟨470306, by rfl⟩ : syracuseStep 627075 = 940613) B940613
theorem B1413521 : Blo 626299 1413521 := bstep (se 2 (by rfl) ⟨530070, by rfl⟩ : syracuseStep 1413521 = 1060141) B1060141
theorem B627091 : Blo 626299 627091 := bstep (se 1 (by rfl) ⟨470318, by rfl⟩ : syracuseStep 627091 = 940637) B940637
theorem B627107 : Blo 626299 627107 := bstep (se 1 (by rfl) ⟨470330, by rfl⟩ : syracuseStep 627107 = 940661) B940661
theorem B1413539 : Blo 626299 1413539 := bstep (se 1 (by rfl) ⟨1060154, by rfl⟩ : syracuseStep 1413539 = 2120309) B2120309
theorem B627123 : Blo 626299 627123 := bstep (se 1 (by rfl) ⟨470342, by rfl⟩ : syracuseStep 627123 = 940685) B940685
theorem B627139 : Blo 626299 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B627155 : Blo 626299 627155 := bstep (se 1 (by rfl) ⟨470366, by rfl⟩ : syracuseStep 627155 = 940733) B940733
theorem B627171 : Blo 626299 627171 := bstep (se 1 (by rfl) ⟨470378, by rfl⟩ : syracuseStep 627171 = 940757) B940757
theorem B922097 : Blo 626299 922097 := bstep (se 2 (by rfl) ⟨345786, by rfl⟩ : syracuseStep 922097 = 691573) B691573
theorem B627187 : Blo 626299 627187 := bstep (se 1 (by rfl) ⟨470390, by rfl⟩ : syracuseStep 627187 = 940781) B940781
theorem B627203 : Blo 626299 627203 := bstep (se 1 (by rfl) ⟨470402, by rfl⟩ : syracuseStep 627203 = 940805) B940805
theorem B627219 : Blo 626299 627219 := bstep (se 1 (by rfl) ⟨470414, by rfl⟩ : syracuseStep 627219 = 940829) B940829
theorem B627235 : Blo 626299 627235 := bstep (se 1 (by rfl) ⟨470426, by rfl⟩ : syracuseStep 627235 = 940853) B940853
theorem B627251 : Blo 626299 627251 := bstep (se 1 (by rfl) ⟨470438, by rfl⟩ : syracuseStep 627251 = 940877) B940877
theorem B627267 : Blo 626299 627267 := bstep (se 1 (by rfl) ⟨470450, by rfl⟩ : syracuseStep 627267 = 940901) B940901
theorem B1512017 : Blo 626299 1512017 := bstep (se 2 (by rfl) ⟨567006, by rfl⟩ : syracuseStep 1512017 = 1134013) B1134013
theorem B627283 : Blo 626299 627283 := bstep (se 1 (by rfl) ⟨470462, by rfl⟩ : syracuseStep 627283 = 940925) B940925
theorem B627299 : Blo 626299 627299 := bstep (se 1 (by rfl) ⟨470474, by rfl⟩ : syracuseStep 627299 = 940949) B940949
theorem B627315 : Blo 626299 627315 := bstep (se 1 (by rfl) ⟨470486, by rfl⟩ : syracuseStep 627315 = 940973) B940973
theorem B627331 : Blo 626299 627331 := bstep (se 1 (by rfl) ⟨470498, by rfl⟩ : syracuseStep 627331 = 940997) B940997
theorem B627347 : Blo 626299 627347 := bstep (se 1 (by rfl) ⟨470510, by rfl⟩ : syracuseStep 627347 = 941021) B941021
theorem B627363 : Blo 626299 627363 := bstep (se 1 (by rfl) ⟨470522, by rfl⟩ : syracuseStep 627363 = 941045) B941045
theorem B1413809 : Blo 626299 1413809 := bstep (se 2 (by rfl) ⟨530178, by rfl⟩ : syracuseStep 1413809 = 1060357) B1060357
theorem B627379 : Blo 626299 627379 := bstep (se 1 (by rfl) ⟨470534, by rfl⟩ : syracuseStep 627379 = 941069) B941069
theorem B627395 : Blo 626299 627395 := bstep (se 1 (by rfl) ⟨470546, by rfl⟩ : syracuseStep 627395 = 941093) B941093
theorem B1413827 : Blo 626299 1413827 := bstep (se 1 (by rfl) ⟨1060370, by rfl⟩ : syracuseStep 1413827 = 2120741) B2120741
theorem B627411 : Blo 626299 627411 := bstep (se 1 (by rfl) ⟨470558, by rfl⟩ : syracuseStep 627411 = 941117) B941117
theorem B627427 : Blo 626299 627427 := bstep (se 1 (by rfl) ⟨470570, by rfl⟩ : syracuseStep 627427 = 941141) B941141
theorem B627443 : Blo 626299 627443 := bstep (se 1 (by rfl) ⟨470582, by rfl⟩ : syracuseStep 627443 = 941165) B941165
theorem B627459 : Blo 626299 627459 := bstep (se 1 (by rfl) ⟨470594, by rfl⟩ : syracuseStep 627459 = 941189) B941189
theorem B627475 : Blo 626299 627475 := bstep (se 1 (by rfl) ⟨470606, by rfl⟩ : syracuseStep 627475 = 941213) B941213
theorem B627491 : Blo 626299 627491 := bstep (se 1 (by rfl) ⟨470618, by rfl⟩ : syracuseStep 627491 = 941237) B941237
theorem B627507 : Blo 626299 627507 := bstep (se 1 (by rfl) ⟨470630, by rfl⟩ : syracuseStep 627507 = 941261) B941261
theorem B627523 : Blo 626299 627523 := bstep (se 1 (by rfl) ⟨470642, by rfl⟩ : syracuseStep 627523 = 941285) B941285
theorem B627539 : Blo 626299 627539 := bstep (se 1 (by rfl) ⟨470654, by rfl⟩ : syracuseStep 627539 = 941309) B941309
theorem B627555 : Blo 626299 627555 := bstep (se 1 (by rfl) ⟨470666, by rfl⟩ : syracuseStep 627555 = 941333) B941333
theorem B627571 : Blo 626299 627571 := bstep (se 1 (by rfl) ⟨470678, by rfl⟩ : syracuseStep 627571 = 941357) B941357
theorem B627587 : Blo 626299 627587 := bstep (se 1 (by rfl) ⟨470690, by rfl⟩ : syracuseStep 627587 = 941381) B941381
theorem B3216269 : Blo 626299 3216269 := bstep (se 3 (by rfl) ⟨603050, by rfl⟩ : syracuseStep 3216269 = 1206101) B1206101
theorem B627603 : Blo 626299 627603 := bstep (se 1 (by rfl) ⟨470702, by rfl⟩ : syracuseStep 627603 = 941405) B941405
theorem B627619 : Blo 626299 627619 := bstep (se 1 (by rfl) ⟨470714, by rfl⟩ : syracuseStep 627619 = 941429) B941429
theorem B627635 : Blo 626299 627635 := bstep (se 1 (by rfl) ⟨470726, by rfl⟩ : syracuseStep 627635 = 941453) B941453
theorem B1020851 : Blo 626299 1020851 := bstep (se 1 (by rfl) ⟨765638, by rfl⟩ : syracuseStep 1020851 = 1531277) B1531277
theorem B627651 : Blo 626299 627651 := bstep (se 1 (by rfl) ⟨470738, by rfl⟩ : syracuseStep 627651 = 941477) B941477
theorem B1414097 : Blo 626299 1414097 := bstep (se 2 (by rfl) ⟨530286, by rfl⟩ : syracuseStep 1414097 = 1060573) B1060573
theorem B627667 : Blo 626299 627667 := bstep (se 1 (by rfl) ⟨470750, by rfl⟩ : syracuseStep 627667 = 941501) B941501
theorem B627683 : Blo 626299 627683 := bstep (se 1 (by rfl) ⟨470762, by rfl⟩ : syracuseStep 627683 = 941525) B941525
theorem B1414115 : Blo 626299 1414115 := bstep (se 1 (by rfl) ⟨1060586, by rfl⟩ : syracuseStep 1414115 = 2121173) B2121173
theorem B627699 : Blo 626299 627699 := bstep (se 1 (by rfl) ⟨470774, by rfl⟩ : syracuseStep 627699 = 941549) B941549
theorem B627715 : Blo 626299 627715 := bstep (se 1 (by rfl) ⟨470786, by rfl⟩ : syracuseStep 627715 = 941573) B941573
theorem B627731 : Blo 626299 627731 := bstep (se 1 (by rfl) ⟨470798, by rfl⟩ : syracuseStep 627731 = 941597) B941597
theorem B627747 : Blo 626299 627747 := bstep (se 1 (by rfl) ⟨470810, by rfl⟩ : syracuseStep 627747 = 941621) B941621
theorem B627763 : Blo 626299 627763 := bstep (se 1 (by rfl) ⟨470822, by rfl⟩ : syracuseStep 627763 = 941645) B941645
theorem B627779 : Blo 626299 627779 := bstep (se 1 (by rfl) ⟨470834, by rfl⟩ : syracuseStep 627779 = 941669) B941669
theorem B627795 : Blo 626299 627795 := bstep (se 1 (by rfl) ⟨470846, by rfl⟩ : syracuseStep 627795 = 941693) B941693
theorem B627811 : Blo 626299 627811 := bstep (se 1 (by rfl) ⟨470858, by rfl⟩ : syracuseStep 627811 = 941717) B941717
theorem B4035683 : Blo 626299 4035683 := bstep (se 1 (by rfl) ⟨3026762, by rfl⟩ : syracuseStep 4035683 = 6053525) B6053525
theorem B48829553 : Blo 626299 48829553 := bstep (se 2 (by rfl) ⟨18311082, by rfl⟩ : syracuseStep 48829553 = 36622165) B36622165
theorem B627827 : Blo 626299 627827 := bstep (se 1 (by rfl) ⟨470870, by rfl⟩ : syracuseStep 627827 = 941741) B941741
theorem B627843 : Blo 626299 627843 := bstep (se 1 (by rfl) ⟨470882, by rfl⟩ : syracuseStep 627843 = 941765) B941765
theorem B627859 : Blo 626299 627859 := bstep (se 1 (by rfl) ⟨470894, by rfl⟩ : syracuseStep 627859 = 941789) B941789
theorem B627875 : Blo 626299 627875 := bstep (se 1 (by rfl) ⟨470906, by rfl⟩ : syracuseStep 627875 = 941813) B941813
theorem B627891 : Blo 626299 627891 := bstep (se 1 (by rfl) ⟨470918, by rfl⟩ : syracuseStep 627891 = 941837) B941837
theorem B627907 : Blo 626299 627907 := bstep (se 1 (by rfl) ⟨470930, by rfl⟩ : syracuseStep 627907 = 941861) B941861
theorem B627923 : Blo 626299 627923 := bstep (se 1 (by rfl) ⟨470942, by rfl⟩ : syracuseStep 627923 = 941885) B941885
theorem B627939 : Blo 626299 627939 := bstep (se 1 (by rfl) ⟨470954, by rfl⟩ : syracuseStep 627939 = 941909) B941909
theorem B1414385 : Blo 626299 1414385 := bstep (se 2 (by rfl) ⟨530394, by rfl⟩ : syracuseStep 1414385 = 1060789) B1060789
theorem B627955 : Blo 626299 627955 := bstep (se 1 (by rfl) ⟨470966, by rfl⟩ : syracuseStep 627955 = 941933) B941933
theorem B627971 : Blo 626299 627971 := bstep (se 1 (by rfl) ⟨470978, by rfl⟩ : syracuseStep 627971 = 941957) B941957
theorem B1414403 : Blo 626299 1414403 := bstep (se 1 (by rfl) ⟨1060802, by rfl⟩ : syracuseStep 1414403 = 2121605) B2121605
theorem B627987 : Blo 626299 627987 := bstep (se 1 (by rfl) ⟨470990, by rfl⟩ : syracuseStep 627987 = 941981) B941981
theorem B628003 : Blo 626299 628003 := bstep (se 1 (by rfl) ⟨471002, by rfl⟩ : syracuseStep 628003 = 942005) B942005
theorem B628019 : Blo 626299 628019 := bstep (se 1 (by rfl) ⟨471014, by rfl⟩ : syracuseStep 628019 = 942029) B942029
theorem B628035 : Blo 626299 628035 := bstep (se 1 (by rfl) ⟨471026, by rfl⟩ : syracuseStep 628035 = 942053) B942053
theorem B628051 : Blo 626299 628051 := bstep (se 1 (by rfl) ⟨471038, by rfl⟩ : syracuseStep 628051 = 942077) B942077
theorem B628067 : Blo 626299 628067 := bstep (se 1 (by rfl) ⟨471050, by rfl⟩ : syracuseStep 628067 = 942101) B942101
theorem B628083 : Blo 626299 628083 := bstep (se 1 (by rfl) ⟨471062, by rfl⟩ : syracuseStep 628083 = 942125) B942125
theorem B628099 : Blo 626299 628099 := bstep (se 1 (by rfl) ⟨471074, by rfl⟩ : syracuseStep 628099 = 942149) B942149
theorem B628115 : Blo 626299 628115 := bstep (se 1 (by rfl) ⟨471086, by rfl⟩ : syracuseStep 628115 = 942173) B942173
theorem B628131 : Blo 626299 628131 := bstep (se 1 (by rfl) ⟨471098, by rfl⟩ : syracuseStep 628131 = 942197) B942197
theorem B628147 : Blo 626299 628147 := bstep (se 1 (by rfl) ⟨471110, by rfl⟩ : syracuseStep 628147 = 942221) B942221
theorem B628163 : Blo 626299 628163 := bstep (se 1 (by rfl) ⟨471122, by rfl⟩ : syracuseStep 628163 = 942245) B942245
theorem B628179 : Blo 626299 628179 := bstep (se 1 (by rfl) ⟨471134, by rfl⟩ : syracuseStep 628179 = 942269) B942269
theorem B628195 : Blo 626299 628195 := bstep (se 1 (by rfl) ⟨471146, by rfl⟩ : syracuseStep 628195 = 942293) B942293
theorem B628211 : Blo 626299 628211 := bstep (se 1 (by rfl) ⟨471158, by rfl⟩ : syracuseStep 628211 = 942317) B942317
theorem B628227 : Blo 626299 628227 := bstep (se 1 (by rfl) ⟨471170, by rfl⟩ : syracuseStep 628227 = 942341) B942341
theorem B1414673 : Blo 626299 1414673 := bstep (se 2 (by rfl) ⟨530502, by rfl⟩ : syracuseStep 1414673 = 1061005) B1061005
theorem B1512977 : Blo 626299 1512977 := bstep (se 2 (by rfl) ⟨567366, by rfl⟩ : syracuseStep 1512977 = 1134733) B1134733
theorem B628243 : Blo 626299 628243 := bstep (se 1 (by rfl) ⟨471182, by rfl⟩ : syracuseStep 628243 = 942365) B942365
theorem B628259 : Blo 626299 628259 := bstep (se 1 (by rfl) ⟨471194, by rfl⟩ : syracuseStep 628259 = 942389) B942389
theorem B1414691 : Blo 626299 1414691 := bstep (se 1 (by rfl) ⟨1061018, by rfl⟩ : syracuseStep 1414691 = 2122037) B2122037
theorem B628275 : Blo 626299 628275 := bstep (se 1 (by rfl) ⟨471206, by rfl⟩ : syracuseStep 628275 = 942413) B942413
theorem B628291 : Blo 626299 628291 := bstep (se 1 (by rfl) ⟨471218, by rfl⟩ : syracuseStep 628291 = 942437) B942437
theorem B628307 : Blo 626299 628307 := bstep (se 1 (by rfl) ⟨471230, by rfl⟩ : syracuseStep 628307 = 942461) B942461
theorem B628323 : Blo 626299 628323 := bstep (se 1 (by rfl) ⟨471242, by rfl⟩ : syracuseStep 628323 = 942485) B942485
theorem B628339 : Blo 626299 628339 := bstep (se 1 (by rfl) ⟨471254, by rfl⟩ : syracuseStep 628339 = 942509) B942509
theorem B628355 : Blo 626299 628355 := bstep (se 1 (by rfl) ⟨471266, by rfl⟩ : syracuseStep 628355 = 942533) B942533
theorem B628371 : Blo 626299 628371 := bstep (se 1 (by rfl) ⟨471278, by rfl⟩ : syracuseStep 628371 = 942557) B942557
theorem B628387 : Blo 626299 628387 := bstep (se 1 (by rfl) ⟨471290, by rfl⟩ : syracuseStep 628387 = 942581) B942581
theorem B628403 : Blo 626299 628403 := bstep (se 1 (by rfl) ⟨471302, by rfl⟩ : syracuseStep 628403 = 942605) B942605
theorem B628419 : Blo 626299 628419 := bstep (se 1 (by rfl) ⟨471314, by rfl⟩ : syracuseStep 628419 = 942629) B942629
theorem B628435 : Blo 626299 628435 := bstep (se 1 (by rfl) ⟨471326, by rfl⟩ : syracuseStep 628435 = 942653) B942653
theorem B628451 : Blo 626299 628451 := bstep (se 1 (by rfl) ⟨471338, by rfl⟩ : syracuseStep 628451 = 942677) B942677
theorem B628467 : Blo 626299 628467 := bstep (se 1 (by rfl) ⟨471350, by rfl⟩ : syracuseStep 628467 = 942701) B942701
theorem B628483 : Blo 626299 628483 := bstep (se 1 (by rfl) ⟨471362, by rfl⟩ : syracuseStep 628483 = 942725) B942725
theorem B628499 : Blo 626299 628499 := bstep (se 1 (by rfl) ⟨471374, by rfl⟩ : syracuseStep 628499 = 942749) B942749
theorem B628515 : Blo 626299 628515 := bstep (se 1 (by rfl) ⟨471386, by rfl⟩ : syracuseStep 628515 = 942773) B942773
theorem B1414961 : Blo 626299 1414961 := bstep (se 2 (by rfl) ⟨530610, by rfl⟩ : syracuseStep 1414961 = 1061221) B1061221
theorem B3184433 : Blo 626299 3184433 := bstep (se 2 (by rfl) ⟨1194162, by rfl⟩ : syracuseStep 3184433 = 2388325) B2388325
theorem B628531 : Blo 626299 628531 := bstep (se 1 (by rfl) ⟨471398, by rfl⟩ : syracuseStep 628531 = 942797) B942797
theorem B628547 : Blo 626299 628547 := bstep (se 1 (by rfl) ⟨471410, by rfl⟩ : syracuseStep 628547 = 942821) B942821
theorem B1414979 : Blo 626299 1414979 := bstep (se 1 (by rfl) ⟨1061234, by rfl⟩ : syracuseStep 1414979 = 2122469) B2122469
theorem B628563 : Blo 626299 628563 := bstep (se 1 (by rfl) ⟨471422, by rfl⟩ : syracuseStep 628563 = 942845) B942845
theorem B628579 : Blo 626299 628579 := bstep (se 1 (by rfl) ⟨471434, by rfl⟩ : syracuseStep 628579 = 942869) B942869
theorem B628595 : Blo 626299 628595 := bstep (se 1 (by rfl) ⟨471446, by rfl⟩ : syracuseStep 628595 = 942893) B942893
theorem B628611 : Blo 626299 628611 := bstep (se 1 (by rfl) ⟨471458, by rfl⟩ : syracuseStep 628611 = 942917) B942917
theorem B628627 : Blo 626299 628627 := bstep (se 1 (by rfl) ⟨471470, by rfl⟩ : syracuseStep 628627 = 942941) B942941
theorem B628643 : Blo 626299 628643 := bstep (se 1 (by rfl) ⟨471482, by rfl⟩ : syracuseStep 628643 = 942965) B942965
theorem B3446705 : Blo 626299 3446705 := bstep (se 2 (by rfl) ⟨1292514, by rfl⟩ : syracuseStep 3446705 = 2585029) B2585029
theorem B628659 : Blo 626299 628659 := bstep (se 1 (by rfl) ⟨471494, by rfl⟩ : syracuseStep 628659 = 942989) B942989
theorem B628675 : Blo 626299 628675 := bstep (se 1 (by rfl) ⟨471506, by rfl⟩ : syracuseStep 628675 = 943013) B943013
theorem B628691 : Blo 626299 628691 := bstep (se 1 (by rfl) ⟨471518, by rfl⟩ : syracuseStep 628691 = 943037) B943037
theorem B628707 : Blo 626299 628707 := bstep (se 1 (by rfl) ⟨471530, by rfl⟩ : syracuseStep 628707 = 943061) B943061
theorem B3577841 : Blo 626299 3577841 := bstep (se 2 (by rfl) ⟨1341690, by rfl⟩ : syracuseStep 3577841 = 2683381) B2683381
theorem B628723 : Blo 626299 628723 := bstep (se 1 (by rfl) ⟨471542, by rfl⟩ : syracuseStep 628723 = 943085) B943085
theorem B628739 : Blo 626299 628739 := bstep (se 1 (by rfl) ⟨471554, by rfl⟩ : syracuseStep 628739 = 943109) B943109
theorem B628755 : Blo 626299 628755 := bstep (se 1 (by rfl) ⟨471566, by rfl⟩ : syracuseStep 628755 = 943133) B943133
theorem B628771 : Blo 626299 628771 := bstep (se 1 (by rfl) ⟨471578, by rfl⟩ : syracuseStep 628771 = 943157) B943157
theorem B1513507 : Blo 626299 1513507 := bstep (se 1 (by rfl) ⟨1135130, by rfl⟩ : syracuseStep 1513507 = 2270261) B2270261
theorem B628787 : Blo 626299 628787 := bstep (se 1 (by rfl) ⟨471590, by rfl⟩ : syracuseStep 628787 = 943181) B943181
theorem B628803 : Blo 626299 628803 := bstep (se 1 (by rfl) ⟨471602, by rfl⟩ : syracuseStep 628803 = 943205) B943205
theorem B1415249 : Blo 626299 1415249 := bstep (se 2 (by rfl) ⟨530718, by rfl⟩ : syracuseStep 1415249 = 1061437) B1061437
theorem B628819 : Blo 626299 628819 := bstep (se 1 (by rfl) ⟨471614, by rfl⟩ : syracuseStep 628819 = 943229) B943229
theorem B628835 : Blo 626299 628835 := bstep (se 1 (by rfl) ⟨471626, by rfl⟩ : syracuseStep 628835 = 943253) B943253
theorem B1415267 : Blo 626299 1415267 := bstep (se 1 (by rfl) ⟨1061450, by rfl⟩ : syracuseStep 1415267 = 2122901) B2122901
theorem B628851 : Blo 626299 628851 := bstep (se 1 (by rfl) ⟨471638, by rfl⟩ : syracuseStep 628851 = 943277) B943277
theorem B628867 : Blo 626299 628867 := bstep (se 1 (by rfl) ⟨471650, by rfl⟩ : syracuseStep 628867 = 943301) B943301
theorem B628883 : Blo 626299 628883 := bstep (se 1 (by rfl) ⟨471662, by rfl⟩ : syracuseStep 628883 = 943325) B943325
theorem B628899 : Blo 626299 628899 := bstep (se 1 (by rfl) ⟨471674, by rfl⟩ : syracuseStep 628899 = 943349) B943349
theorem B628915 : Blo 626299 628915 := bstep (se 1 (by rfl) ⟨471686, by rfl⟩ : syracuseStep 628915 = 943373) B943373
theorem B628931 : Blo 626299 628931 := bstep (se 1 (by rfl) ⟨471698, by rfl⟩ : syracuseStep 628931 = 943397) B943397
theorem B628947 : Blo 626299 628947 := bstep (se 1 (by rfl) ⟨471710, by rfl⟩ : syracuseStep 628947 = 943421) B943421
theorem B628963 : Blo 626299 628963 := bstep (se 1 (by rfl) ⟨471722, by rfl⟩ : syracuseStep 628963 = 943445) B943445
theorem B628979 : Blo 626299 628979 := bstep (se 1 (by rfl) ⟨471734, by rfl⟩ : syracuseStep 628979 = 943469) B943469
theorem B628995 : Blo 626299 628995 := bstep (se 1 (by rfl) ⟨471746, by rfl⟩ : syracuseStep 628995 = 943493) B943493
theorem B629011 : Blo 626299 629011 := bstep (se 1 (by rfl) ⟨471758, by rfl⟩ : syracuseStep 629011 = 943517) B943517
theorem B629027 : Blo 626299 629027 := bstep (se 1 (by rfl) ⟨471770, by rfl⟩ : syracuseStep 629027 = 943541) B943541
theorem B629043 : Blo 626299 629043 := bstep (se 1 (by rfl) ⟨471782, by rfl⟩ : syracuseStep 629043 = 943565) B943565
theorem B629059 : Blo 626299 629059 := bstep (se 1 (by rfl) ⟨471794, by rfl⟩ : syracuseStep 629059 = 943589) B943589
theorem B6461765 : Blo 626299 6461765 := bstep (se 4 (by rfl) ⟨605790, by rfl⟩ : syracuseStep 6461765 = 1211581) B1211581
theorem B629075 : Blo 626299 629075 := bstep (se 1 (by rfl) ⟨471806, by rfl⟩ : syracuseStep 629075 = 943613) B943613
theorem B629091 : Blo 626299 629091 := bstep (se 1 (by rfl) ⟨471818, by rfl⟩ : syracuseStep 629091 = 943637) B943637
theorem B1415537 : Blo 626299 1415537 := bstep (se 2 (by rfl) ⟨530826, by rfl⟩ : syracuseStep 1415537 = 1061653) B1061653
theorem B629107 : Blo 626299 629107 := bstep (se 1 (by rfl) ⟨471830, by rfl⟩ : syracuseStep 629107 = 943661) B943661
theorem B629123 : Blo 626299 629123 := bstep (se 1 (by rfl) ⟨471842, by rfl⟩ : syracuseStep 629123 = 943685) B943685
theorem B1415555 : Blo 626299 1415555 := bstep (se 1 (by rfl) ⟨1061666, by rfl⟩ : syracuseStep 1415555 = 2123333) B2123333
theorem B629139 : Blo 626299 629139 := bstep (se 1 (by rfl) ⟨471854, by rfl⟩ : syracuseStep 629139 = 943709) B943709
theorem B629155 : Blo 626299 629155 := bstep (se 1 (by rfl) ⟨471866, by rfl⟩ : syracuseStep 629155 = 943733) B943733
theorem B629171 : Blo 626299 629171 := bstep (se 1 (by rfl) ⟨471878, by rfl⟩ : syracuseStep 629171 = 943757) B943757
theorem B629187 : Blo 626299 629187 := bstep (se 1 (by rfl) ⟨471890, by rfl⟩ : syracuseStep 629187 = 943781) B943781
theorem B629203 : Blo 626299 629203 := bstep (se 1 (by rfl) ⟨471902, by rfl⟩ : syracuseStep 629203 = 943805) B943805
theorem B629219 : Blo 626299 629219 := bstep (se 1 (by rfl) ⟨471914, by rfl⟩ : syracuseStep 629219 = 943829) B943829
theorem B629235 : Blo 626299 629235 := bstep (se 1 (by rfl) ⟨471926, by rfl⟩ : syracuseStep 629235 = 943853) B943853
theorem B793091 : Blo 626299 793091 := bstep (se 1 (by rfl) ⟨594818, by rfl⟩ : syracuseStep 793091 = 1189637) B1189637
theorem B629251 : Blo 626299 629251 := bstep (se 1 (by rfl) ⟨471938, by rfl⟩ : syracuseStep 629251 = 943877) B943877
theorem B629267 : Blo 626299 629267 := bstep (se 1 (by rfl) ⟨471950, by rfl⟩ : syracuseStep 629267 = 943901) B943901
theorem B629283 : Blo 626299 629283 := bstep (se 1 (by rfl) ⟨471962, by rfl⟩ : syracuseStep 629283 = 943925) B943925
theorem B629299 : Blo 626299 629299 := bstep (se 1 (by rfl) ⟨471974, by rfl⟩ : syracuseStep 629299 = 943949) B943949
theorem B629315 : Blo 626299 629315 := bstep (se 1 (by rfl) ⟨471986, by rfl⟩ : syracuseStep 629315 = 943973) B943973
theorem B629331 : Blo 626299 629331 := bstep (se 1 (by rfl) ⟨471998, by rfl⟩ : syracuseStep 629331 = 943997) B943997
theorem B629347 : Blo 626299 629347 := bstep (se 1 (by rfl) ⟨472010, by rfl⟩ : syracuseStep 629347 = 944021) B944021
theorem B629363 : Blo 626299 629363 := bstep (se 1 (by rfl) ⟨472022, by rfl⟩ : syracuseStep 629363 = 944045) B944045
theorem B629379 : Blo 626299 629379 := bstep (se 1 (by rfl) ⟨472034, by rfl⟩ : syracuseStep 629379 = 944069) B944069
theorem B1415825 : Blo 626299 1415825 := bstep (se 2 (by rfl) ⟨530934, by rfl⟩ : syracuseStep 1415825 = 1061869) B1061869
theorem B629395 : Blo 626299 629395 := bstep (se 1 (by rfl) ⟨472046, by rfl⟩ : syracuseStep 629395 = 944093) B944093
theorem B1415843 : Blo 626299 1415843 := bstep (se 1 (by rfl) ⟨1061882, by rfl⟩ : syracuseStep 1415843 = 2123765) B2123765
theorem B629411 : Blo 626299 629411 := bstep (se 1 (by rfl) ⟨472058, by rfl⟩ : syracuseStep 629411 = 944117) B944117
theorem B629427 : Blo 626299 629427 := bstep (se 1 (by rfl) ⟨472070, by rfl⟩ : syracuseStep 629427 = 944141) B944141
theorem B629443 : Blo 626299 629443 := bstep (se 1 (by rfl) ⟨472082, by rfl⟩ : syracuseStep 629443 = 944165) B944165
theorem B629459 : Blo 626299 629459 := bstep (se 1 (by rfl) ⟨472094, by rfl⟩ : syracuseStep 629459 = 944189) B944189
theorem B957139 : Blo 626299 957139 := bstep (se 1 (by rfl) ⟨717854, by rfl⟩ : syracuseStep 957139 = 1435709) B1435709
theorem B629475 : Blo 626299 629475 := bstep (se 1 (by rfl) ⟨472106, by rfl⟩ : syracuseStep 629475 = 944213) B944213
theorem B629491 : Blo 626299 629491 := bstep (se 1 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 629491 = 944237) B944237
theorem B629507 : Blo 626299 629507 := bstep (se 1 (by rfl) ⟨472130, by rfl⟩ : syracuseStep 629507 = 944261) B944261
theorem B629523 : Blo 626299 629523 := bstep (se 1 (by rfl) ⟨472142, by rfl⟩ : syracuseStep 629523 = 944285) B944285
theorem B629539 : Blo 626299 629539 := bstep (se 1 (by rfl) ⟨472154, by rfl⟩ : syracuseStep 629539 = 944309) B944309
theorem B629555 : Blo 626299 629555 := bstep (se 1 (by rfl) ⟨472166, by rfl⟩ : syracuseStep 629555 = 944333) B944333
theorem B629571 : Blo 626299 629571 := bstep (se 1 (by rfl) ⟨472178, by rfl⟩ : syracuseStep 629571 = 944357) B944357
theorem B629587 : Blo 626299 629587 := bstep (se 1 (by rfl) ⟨472190, by rfl⟩ : syracuseStep 629587 = 944381) B944381
theorem B629603 : Blo 626299 629603 := bstep (se 1 (by rfl) ⟨472202, by rfl⟩ : syracuseStep 629603 = 944405) B944405
theorem B629619 : Blo 626299 629619 := bstep (se 1 (by rfl) ⟨472214, by rfl⟩ : syracuseStep 629619 = 944429) B944429
theorem B629635 : Blo 626299 629635 := bstep (se 1 (by rfl) ⟨472226, by rfl⟩ : syracuseStep 629635 = 944453) B944453
theorem B629651 : Blo 626299 629651 := bstep (se 1 (by rfl) ⟨472238, by rfl⟩ : syracuseStep 629651 = 944477) B944477
theorem B629667 : Blo 626299 629667 := bstep (se 1 (by rfl) ⟨472250, by rfl⟩ : syracuseStep 629667 = 944501) B944501
theorem B1416113 : Blo 626299 1416113 := bstep (se 2 (by rfl) ⟨531042, by rfl⟩ : syracuseStep 1416113 = 1062085) B1062085
theorem B629683 : Blo 626299 629683 := bstep (se 1 (by rfl) ⟨472262, by rfl⟩ : syracuseStep 629683 = 944525) B944525
theorem B1416131 : Blo 626299 1416131 := bstep (se 1 (by rfl) ⟨1062098, by rfl⟩ : syracuseStep 1416131 = 2124197) B2124197
theorem B629699 : Blo 626299 629699 := bstep (se 1 (by rfl) ⟨472274, by rfl⟩ : syracuseStep 629699 = 944549) B944549
theorem B629715 : Blo 626299 629715 := bstep (se 1 (by rfl) ⟨472286, by rfl⟩ : syracuseStep 629715 = 944573) B944573
theorem B629731 : Blo 626299 629731 := bstep (se 1 (by rfl) ⟨472298, by rfl⟩ : syracuseStep 629731 = 944597) B944597
theorem B629747 : Blo 626299 629747 := bstep (se 1 (by rfl) ⟨472310, by rfl⟩ : syracuseStep 629747 = 944621) B944621
theorem B629763 : Blo 626299 629763 := bstep (se 1 (by rfl) ⟨472322, by rfl⟩ : syracuseStep 629763 = 944645) B944645
theorem B629779 : Blo 626299 629779 := bstep (se 1 (by rfl) ⟨472334, by rfl⟩ : syracuseStep 629779 = 944669) B944669
theorem B1612835 : Blo 626299 1612835 := bstep (se 1 (by rfl) ⟨1209626, by rfl⟩ : syracuseStep 1612835 = 2419253) B2419253
theorem B629795 : Blo 626299 629795 := bstep (se 1 (by rfl) ⟨472346, by rfl⟩ : syracuseStep 629795 = 944693) B944693
theorem B4037681 : Blo 626299 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B629811 : Blo 626299 629811 := bstep (se 1 (by rfl) ⟨472358, by rfl⟩ : syracuseStep 629811 = 944717) B944717
theorem B629827 : Blo 626299 629827 := bstep (se 1 (by rfl) ⟨472370, by rfl⟩ : syracuseStep 629827 = 944741) B944741
theorem B629843 : Blo 626299 629843 := bstep (se 1 (by rfl) ⟨472382, by rfl⟩ : syracuseStep 629843 = 944765) B944765
theorem B629859 : Blo 626299 629859 := bstep (se 1 (by rfl) ⟨472394, by rfl⟩ : syracuseStep 629859 = 944789) B944789
theorem B629875 : Blo 626299 629875 := bstep (se 1 (by rfl) ⟨472406, by rfl⟩ : syracuseStep 629875 = 944813) B944813
theorem B629891 : Blo 626299 629891 := bstep (se 1 (by rfl) ⟨472418, by rfl⟩ : syracuseStep 629891 = 944837) B944837
theorem B629907 : Blo 626299 629907 := bstep (se 1 (by rfl) ⟨472430, by rfl⟩ : syracuseStep 629907 = 944861) B944861
theorem B629923 : Blo 626299 629923 := bstep (se 1 (by rfl) ⟨472442, by rfl⟩ : syracuseStep 629923 = 944885) B944885
theorem B629939 : Blo 626299 629939 := bstep (se 1 (by rfl) ⟨472454, by rfl⟩ : syracuseStep 629939 = 944909) B944909
theorem B793795 : Blo 626299 793795 := bstep (se 1 (by rfl) ⟨595346, by rfl⟩ : syracuseStep 793795 = 1190693) B1190693
theorem B629955 : Blo 626299 629955 := bstep (se 1 (by rfl) ⟨472466, by rfl⟩ : syracuseStep 629955 = 944933) B944933
theorem B1416401 : Blo 626299 1416401 := bstep (se 2 (by rfl) ⟨531150, by rfl⟩ : syracuseStep 1416401 = 1062301) B1062301
theorem B629971 : Blo 626299 629971 := bstep (se 1 (by rfl) ⟨472478, by rfl⟩ : syracuseStep 629971 = 944957) B944957
theorem B3185891 : Blo 626299 3185891 := bstep (se 1 (by rfl) ⟨2389418, by rfl⟩ : syracuseStep 3185891 = 4778837) B4778837
theorem B1416419 : Blo 626299 1416419 := bstep (se 1 (by rfl) ⟨1062314, by rfl⟩ : syracuseStep 1416419 = 2124629) B2124629
theorem B629987 : Blo 626299 629987 := bstep (se 1 (by rfl) ⟨472490, by rfl⟩ : syracuseStep 629987 = 944981) B944981
theorem B630003 : Blo 626299 630003 := bstep (se 1 (by rfl) ⟨472502, by rfl⟩ : syracuseStep 630003 = 945005) B945005
theorem B630019 : Blo 626299 630019 := bstep (se 1 (by rfl) ⟨472514, by rfl⟩ : syracuseStep 630019 = 945029) B945029
theorem B630035 : Blo 626299 630035 := bstep (se 1 (by rfl) ⟨472526, by rfl⟩ : syracuseStep 630035 = 945053) B945053
theorem B793891 : Blo 626299 793891 := bstep (se 1 (by rfl) ⟨595418, by rfl⟩ : syracuseStep 793891 = 1190837) B1190837
theorem B630051 : Blo 626299 630051 := bstep (se 1 (by rfl) ⟨472538, by rfl⟩ : syracuseStep 630051 = 945077) B945077
theorem B630067 : Blo 626299 630067 := bstep (se 1 (by rfl) ⟨472550, by rfl⟩ : syracuseStep 630067 = 945101) B945101
theorem B630083 : Blo 626299 630083 := bstep (se 1 (by rfl) ⟨472562, by rfl⟩ : syracuseStep 630083 = 945125) B945125
theorem B630099 : Blo 626299 630099 := bstep (se 1 (by rfl) ⟨472574, by rfl⟩ : syracuseStep 630099 = 945149) B945149
theorem B6790499 : Blo 626299 6790499 := bstep (se 1 (by rfl) ⟨5092874, by rfl⟩ : syracuseStep 6790499 = 10185749) B10185749
theorem B630115 : Blo 626299 630115 := bstep (se 1 (by rfl) ⟨472586, by rfl⟩ : syracuseStep 630115 = 945173) B945173
theorem B630131 : Blo 626299 630131 := bstep (se 1 (by rfl) ⟨472598, by rfl⟩ : syracuseStep 630131 = 945197) B945197
theorem B892291 : Blo 626299 892291 := bstep (se 1 (by rfl) ⟨669218, by rfl⟩ : syracuseStep 892291 = 1338437) B1338437
theorem B630147 : Blo 626299 630147 := bstep (se 1 (by rfl) ⟨472610, by rfl⟩ : syracuseStep 630147 = 945221) B945221
theorem B630163 : Blo 626299 630163 := bstep (se 1 (by rfl) ⟨472622, by rfl⟩ : syracuseStep 630163 = 945245) B945245
theorem B3579299 : Blo 626299 3579299 := bstep (se 1 (by rfl) ⟨2684474, by rfl⟩ : syracuseStep 3579299 = 5368949) B5368949
theorem B630179 : Blo 626299 630179 := bstep (se 1 (by rfl) ⟨472634, by rfl⟩ : syracuseStep 630179 = 945269) B945269
theorem B630195 : Blo 626299 630195 := bstep (se 1 (by rfl) ⟨472646, by rfl⟩ : syracuseStep 630195 = 945293) B945293
theorem B630211 : Blo 626299 630211 := bstep (se 1 (by rfl) ⟨472658, by rfl⟩ : syracuseStep 630211 = 945317) B945317
theorem B630227 : Blo 626299 630227 := bstep (se 1 (by rfl) ⟨472670, by rfl⟩ : syracuseStep 630227 = 945341) B945341
theorem B892387 : Blo 626299 892387 := bstep (se 1 (by rfl) ⟨669290, by rfl⟩ : syracuseStep 892387 = 1338581) B1338581
theorem B630243 : Blo 626299 630243 := bstep (se 1 (by rfl) ⟨472682, by rfl⟩ : syracuseStep 630243 = 945365) B945365
theorem B1416689 : Blo 626299 1416689 := bstep (se 2 (by rfl) ⟨531258, by rfl⟩ : syracuseStep 1416689 = 1062517) B1062517
theorem B630259 : Blo 626299 630259 := bstep (se 1 (by rfl) ⟨472694, by rfl⟩ : syracuseStep 630259 = 945389) B945389
theorem B1416707 : Blo 626299 1416707 := bstep (se 1 (by rfl) ⟨1062530, by rfl⟩ : syracuseStep 1416707 = 2125061) B2125061
theorem B630275 : Blo 626299 630275 := bstep (se 1 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 630275 = 945413) B945413
theorem B630291 : Blo 626299 630291 := bstep (se 1 (by rfl) ⟨472718, by rfl⟩ : syracuseStep 630291 = 945437) B945437
theorem B2006641 : Blo 626299 2006641 := bstep (se 2 (by rfl) ⟨752490, by rfl⟩ : syracuseStep 2006641 = 1504981) B1504981
theorem B2039555 : Blo 626299 2039555 := bstep (se 1 (by rfl) ⟨1529666, by rfl⟩ : syracuseStep 2039555 = 3059333) B3059333
theorem B1416977 : Blo 626299 1416977 := bstep (se 2 (by rfl) ⟨531366, by rfl⟩ : syracuseStep 1416977 = 1062733) B1062733
theorem B794387 : Blo 626299 794387 := bstep (se 1 (by rfl) ⟨595790, by rfl⟩ : syracuseStep 794387 = 1191581) B1191581
theorem B1416995 : Blo 626299 1416995 := bstep (se 1 (by rfl) ⟨1062746, by rfl⟩ : syracuseStep 1416995 = 2125493) B2125493
theorem B892883 : Blo 626299 892883 := bstep (se 1 (by rfl) ⟨669662, by rfl⟩ : syracuseStep 892883 = 1339325) B1339325
theorem B3186701 : Blo 626299 3186701 := bstep (se 3 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 3186701 = 1195013) B1195013
theorem B1417265 : Blo 626299 1417265 := bstep (se 2 (by rfl) ⟨531474, by rfl⟩ : syracuseStep 1417265 = 1062949) B1062949
theorem B8036405 : Blo 626299 8036405 := bstep (se 5 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 8036405 = 753413) B753413
theorem B1417283 : Blo 626299 1417283 := bstep (se 1 (by rfl) ⟨1062962, by rfl⟩ : syracuseStep 1417283 = 2125925) B2125925
theorem B1056881 : Blo 626299 1056881 := bstep (se 2 (by rfl) ⟨396330, by rfl⟩ : syracuseStep 1056881 = 792661) B792661
theorem B34480241 : Blo 626299 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B1057009 : Blo 626299 1057009 := bstep (se 2 (by rfl) ⟨396378, by rfl⟩ : syracuseStep 1057009 = 792757) B792757
theorem B1057043 : Blo 626299 1057043 := bstep (se 1 (by rfl) ⟨792782, by rfl⟩ : syracuseStep 1057043 = 1585565) B1585565
theorem B1417553 : Blo 626299 1417553 := bstep (se 2 (by rfl) ⟨531582, by rfl⟩ : syracuseStep 1417553 = 1063165) B1063165
theorem B860513 : Blo 626299 860513 := bstep (se 2 (by rfl) ⟨322692, by rfl⟩ : syracuseStep 860513 = 645385) B645385
theorem B1417571 : Blo 626299 1417571 := bstep (se 1 (by rfl) ⟨1063178, by rfl⟩ : syracuseStep 1417571 = 2126357) B2126357
theorem B3580301 : Blo 626299 3580301 := bstep (se 3 (by rfl) ⟨671306, by rfl⟩ : syracuseStep 3580301 = 1342613) B1342613
theorem B1057171 : Blo 626299 1057171 := bstep (se 1 (by rfl) ⟨792878, by rfl⟩ : syracuseStep 1057171 = 1585757) B1585757
theorem B795091 : Blo 626299 795091 := bstep (se 1 (by rfl) ⟨596318, by rfl⟩ : syracuseStep 795091 = 1192637) B1192637
theorem B1057313 : Blo 626299 1057313 := bstep (se 2 (by rfl) ⟨396492, by rfl⟩ : syracuseStep 1057313 = 792985) B792985
theorem B3580465 : Blo 626299 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B795187 : Blo 626299 795187 := bstep (se 1 (by rfl) ⟨596390, by rfl⟩ : syracuseStep 795187 = 1192781) B1192781
theorem B893521 : Blo 626299 893521 := bstep (se 2 (by rfl) ⟨335070, by rfl⟩ : syracuseStep 893521 = 670141) B670141
theorem B1417841 : Blo 626299 1417841 := bstep (se 2 (by rfl) ⟨531690, by rfl⟩ : syracuseStep 1417841 = 1063381) B1063381
theorem B1417859 : Blo 626299 1417859 := bstep (se 1 (by rfl) ⟨1063394, by rfl⟩ : syracuseStep 1417859 = 2126789) B2126789
theorem B1057441 : Blo 626299 1057441 := bstep (se 2 (by rfl) ⟨396540, by rfl⟩ : syracuseStep 1057441 = 793081) B793081
theorem B1057475 : Blo 626299 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B3875525 : Blo 626299 3875525 := bstep (se 4 (by rfl) ⟨363330, by rfl⟩ : syracuseStep 3875525 = 726661) B726661
theorem B2007757 : Blo 626299 2007757 := bstep (se 3 (by rfl) ⟨376454, by rfl⟩ : syracuseStep 2007757 = 752909) B752909
theorem B2859725 : Blo 626299 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B2007821 : Blo 626299 2007821 := bstep (se 3 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 2007821 = 752933) B752933
theorem B1057603 : Blo 626299 1057603 := bstep (se 1 (by rfl) ⟨793202, by rfl⟩ : syracuseStep 1057603 = 1586405) B1586405
theorem B860995 : Blo 626299 860995 := bstep (se 1 (by rfl) ⟨645746, by rfl⟩ : syracuseStep 860995 = 1291493) B1291493
theorem B1418129 : Blo 626299 1418129 := bstep (se 2 (by rfl) ⟨531798, by rfl⟩ : syracuseStep 1418129 = 1063597) B1063597
theorem B893857 : Blo 626299 893857 := bstep (se 2 (by rfl) ⟨335196, by rfl⟩ : syracuseStep 893857 = 670393) B670393
theorem B1418147 : Blo 626299 1418147 := bstep (se 1 (by rfl) ⟨1063610, by rfl⟩ : syracuseStep 1418147 = 2127221) B2127221
theorem B1057745 : Blo 626299 1057745 := bstep (se 2 (by rfl) ⟨396654, by rfl⟩ : syracuseStep 1057745 = 793309) B793309
theorem B795683 : Blo 626299 795683 := bstep (se 1 (by rfl) ⟨596762, by rfl⟩ : syracuseStep 795683 = 1193525) B1193525
theorem B1057873 : Blo 626299 1057873 := bstep (se 2 (by rfl) ⟨396702, by rfl⟩ : syracuseStep 1057873 = 793405) B793405
theorem B1057907 : Blo 626299 1057907 := bstep (se 1 (by rfl) ⟨793430, by rfl⟩ : syracuseStep 1057907 = 1586861) B1586861
theorem B1058035 : Blo 626299 1058035 := bstep (se 1 (by rfl) ⟨793526, by rfl⟩ : syracuseStep 1058035 = 1587053) B1587053
theorem B5350769 : Blo 626299 5350769 := bstep (se 2 (by rfl) ⟨2006538, by rfl⟩ : syracuseStep 5350769 = 4013077) B4013077
theorem B1058177 : Blo 626299 1058177 := bstep (se 2 (by rfl) ⟨396816, by rfl⟩ : syracuseStep 1058177 = 793633) B793633
theorem B1910243 : Blo 626299 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B894449 : Blo 626299 894449 := bstep (se 2 (by rfl) ⟨335418, by rfl⟩ : syracuseStep 894449 = 670837) B670837
theorem B1058305 : Blo 626299 1058305 := bstep (se 2 (by rfl) ⟨396864, by rfl⟩ : syracuseStep 1058305 = 793729) B793729
theorem B1189379 : Blo 626299 1189379 := bstep (se 1 (by rfl) ⟨892034, by rfl⟩ : syracuseStep 1189379 = 1784069) B1784069
theorem B1058339 : Blo 626299 1058339 := bstep (se 1 (by rfl) ⟨793754, by rfl⟩ : syracuseStep 1058339 = 1587509) B1587509
theorem B1058467 : Blo 626299 1058467 := bstep (se 1 (by rfl) ⟨793850, by rfl⟩ : syracuseStep 1058467 = 1587701) B1587701
theorem B796387 : Blo 626299 796387 := bstep (se 1 (by rfl) ⟨597290, by rfl⟩ : syracuseStep 796387 = 1194581) B1194581
theorem B3024611 : Blo 626299 3024611 := bstep (se 1 (by rfl) ⟨2268458, by rfl⟩ : syracuseStep 3024611 = 4536917) B4536917
theorem B1189667 : Blo 626299 1189667 := bstep (se 1 (by rfl) ⟨892250, by rfl⟩ : syracuseStep 1189667 = 1784501) B1784501
theorem B1058609 : Blo 626299 1058609 := bstep (se 2 (by rfl) ⟨396978, by rfl⟩ : syracuseStep 1058609 = 793957) B793957
theorem B796483 : Blo 626299 796483 := bstep (se 1 (by rfl) ⟨597362, by rfl⟩ : syracuseStep 796483 = 1194725) B1194725
theorem B2795363 : Blo 626299 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B3024803 : Blo 626299 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B1058737 : Blo 626299 1058737 := bstep (se 2 (by rfl) ⟨397026, by rfl⟩ : syracuseStep 1058737 = 794053) B794053
theorem B1058771 : Blo 626299 1058771 := bstep (se 1 (by rfl) ⟨794078, by rfl⟩ : syracuseStep 1058771 = 1588157) B1588157
theorem B2861041 : Blo 626299 2861041 := bstep (se 2 (by rfl) ⟨1072890, by rfl⟩ : syracuseStep 2861041 = 2145781) B2145781
theorem B894979 : Blo 626299 894979 := bstep (se 1 (by rfl) ⟨671234, by rfl⟩ : syracuseStep 894979 = 1342469) B1342469
theorem B1058899 : Blo 626299 1058899 := bstep (se 1 (by rfl) ⟨794174, by rfl⟩ : syracuseStep 1058899 = 1588349) B1588349
theorem B1059041 : Blo 626299 1059041 := bstep (se 2 (by rfl) ⟨397140, by rfl⟩ : syracuseStep 1059041 = 794281) B794281
theorem B4761827 : Blo 626299 4761827 := bstep (se 1 (by rfl) ⟨3571370, by rfl⟩ : syracuseStep 4761827 = 7142741) B7142741
theorem B3025187 : Blo 626299 3025187 := bstep (se 1 (by rfl) ⟨2268890, by rfl⟩ : syracuseStep 3025187 = 4537781) B4537781
theorem B796979 : Blo 626299 796979 := bstep (se 1 (by rfl) ⟨597734, by rfl⟩ : syracuseStep 796979 = 1195469) B1195469
theorem B895315 : Blo 626299 895315 := bstep (se 1 (by rfl) ⟨671486, by rfl⟩ : syracuseStep 895315 = 1342973) B1342973
theorem B1059169 : Blo 626299 1059169 := bstep (se 2 (by rfl) ⟨397188, by rfl⟩ : syracuseStep 1059169 = 794377) B794377
theorem B1059203 : Blo 626299 1059203 := bstep (se 1 (by rfl) ⟨794402, by rfl⟩ : syracuseStep 1059203 = 1588805) B1588805
theorem B2009603 : Blo 626299 2009603 := bstep (se 1 (by rfl) ⟨1507202, by rfl⟩ : syracuseStep 2009603 = 3014405) B3014405
theorem B1059331 : Blo 626299 1059331 := bstep (se 1 (by rfl) ⟨794498, by rfl⟩ : syracuseStep 1059331 = 1588997) B1588997
theorem B1059473 : Blo 626299 1059473 := bstep (se 2 (by rfl) ⟨397302, by rfl⟩ : syracuseStep 1059473 = 794605) B794605
theorem B1190609 : Blo 626299 1190609 := bstep (se 2 (by rfl) ⟨446478, by rfl⟩ : syracuseStep 1190609 = 892957) B892957
theorem B4303601 : Blo 626299 4303601 := bstep (se 2 (by rfl) ⟨1613850, by rfl⟩ : syracuseStep 4303601 = 3227701) B3227701
theorem B1059601 : Blo 626299 1059601 := bstep (se 2 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 1059601 = 794701) B794701
theorem B1059635 : Blo 626299 1059635 := bstep (se 1 (by rfl) ⟨794726, by rfl⟩ : syracuseStep 1059635 = 1589453) B1589453
theorem B3189617 : Blo 626299 3189617 := bstep (se 2 (by rfl) ⟨1196106, by rfl⟩ : syracuseStep 3189617 = 2392213) B2392213
theorem B895873 : Blo 626299 895873 := bstep (se 2 (by rfl) ⟨335952, by rfl⟩ : syracuseStep 895873 = 671905) B671905
theorem B895907 : Blo 626299 895907 := bstep (se 1 (by rfl) ⟨671930, by rfl⟩ : syracuseStep 895907 = 1343861) B1343861
theorem B1059763 : Blo 626299 1059763 := bstep (se 1 (by rfl) ⟨794822, by rfl⟩ : syracuseStep 1059763 = 1589645) B1589645
theorem B797683 : Blo 626299 797683 := bstep (se 1 (by rfl) ⟨598262, by rfl⟩ : syracuseStep 797683 = 1196525) B1196525
theorem B1059905 : Blo 626299 1059905 := bstep (se 2 (by rfl) ⟨397464, by rfl⟩ : syracuseStep 1059905 = 794929) B794929
theorem B1060033 : Blo 626299 1060033 := bstep (se 2 (by rfl) ⟨397512, by rfl⟩ : syracuseStep 1060033 = 795025) B795025
theorem B1060067 : Blo 626299 1060067 := bstep (se 1 (by rfl) ⟨795050, by rfl⟩ : syracuseStep 1060067 = 1590101) B1590101
theorem B3583217 : Blo 626299 3583217 := bstep (se 2 (by rfl) ⟨1343706, by rfl⟩ : syracuseStep 3583217 = 2687413) B2687413
theorem B1060195 : Blo 626299 1060195 := bstep (se 1 (by rfl) ⟨795146, by rfl⟩ : syracuseStep 1060195 = 1590293) B1590293
theorem B896465 : Blo 626299 896465 := bstep (se 2 (by rfl) ⟨336174, by rfl⟩ : syracuseStep 896465 = 672349) B672349
theorem B1060337 : Blo 626299 1060337 := bstep (se 2 (by rfl) ⟨397626, by rfl⟩ : syracuseStep 1060337 = 795253) B795253
theorem B8170993 : Blo 626299 8170993 := bstep (se 2 (by rfl) ⟨3064122, by rfl⟩ : syracuseStep 8170993 = 6128245) B6128245
theorem B896545 : Blo 626299 896545 := bstep (se 2 (by rfl) ⟨336204, by rfl⟩ : syracuseStep 896545 = 672409) B672409
theorem B1191505 : Blo 626299 1191505 := bstep (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) B893629
theorem B1912429 : Blo 626299 1912429 := bstep (se 3 (by rfl) ⟨358580, by rfl⟩ : syracuseStep 1912429 = 717161) B717161
theorem B1060465 : Blo 626299 1060465 := bstep (se 2 (by rfl) ⟨397674, by rfl⟩ : syracuseStep 1060465 = 795349) B795349
theorem B1060499 : Blo 626299 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B2174627 : Blo 626299 2174627 := bstep (se 1 (by rfl) ⟨1630970, by rfl⟩ : syracuseStep 2174627 = 3261941) B3261941
theorem B1191665 : Blo 626299 1191665 := bstep (se 2 (by rfl) ⟨446874, by rfl⟩ : syracuseStep 1191665 = 893749) B893749
theorem B5353229 : Blo 626299 5353229 := bstep (se 3 (by rfl) ⟨1003730, by rfl⟩ : syracuseStep 5353229 = 2007461) B2007461
theorem B1060627 : Blo 626299 1060627 := bstep (se 1 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 1060627 = 1590941) B1590941
theorem B4599665 : Blo 626299 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B3026801 : Blo 626299 3026801 := bstep (se 2 (by rfl) ⟨1135050, by rfl⟩ : syracuseStep 3026801 = 2270101) B2270101
theorem B1060769 : Blo 626299 1060769 := bstep (se 2 (by rfl) ⟨397788, by rfl⟩ : syracuseStep 1060769 = 795577) B795577
theorem B1060897 : Blo 626299 1060897 := bstep (se 2 (by rfl) ⟨397836, by rfl⟩ : syracuseStep 1060897 = 795673) B795673
theorem B1060931 : Blo 626299 1060931 := bstep (se 1 (by rfl) ⟨795698, by rfl⟩ : syracuseStep 1060931 = 1591397) B1591397
theorem B634963 : Blo 626299 634963 := bstep (se 1 (by rfl) ⟨476222, by rfl⟩ : syracuseStep 634963 = 952445) B952445
theorem B1192067 : Blo 626299 1192067 := bstep (se 1 (by rfl) ⟨894050, by rfl⟩ : syracuseStep 1192067 = 1788101) B1788101
theorem B1061059 : Blo 626299 1061059 := bstep (se 1 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 1061059 = 1591589) B1591589
theorem B3027185 : Blo 626299 3027185 := bstep (se 2 (by rfl) ⟨1135194, by rfl⟩ : syracuseStep 3027185 = 2270389) B2270389
theorem B897331 : Blo 626299 897331 := bstep (se 1 (by rfl) ⟨672998, by rfl⟩ : syracuseStep 897331 = 1345997) B1345997
theorem B1061201 : Blo 626299 1061201 := bstep (se 2 (by rfl) ⟨397950, by rfl⟩ : syracuseStep 1061201 = 795901) B795901
theorem B1061329 : Blo 626299 1061329 := bstep (se 2 (by rfl) ⟨397998, by rfl⟩ : syracuseStep 1061329 = 795997) B795997
theorem B1061363 : Blo 626299 1061363 := bstep (se 1 (by rfl) ⟨796022, by rfl⟩ : syracuseStep 1061363 = 1592045) B1592045
theorem B1913453 : Blo 626299 1913453 := bstep (se 3 (by rfl) ⟨358772, by rfl⟩ : syracuseStep 1913453 = 717545) B717545
theorem B1585777 : Blo 626299 1585777 := bstep (se 2 (by rfl) ⟨594666, by rfl⟩ : syracuseStep 1585777 = 1189333) B1189333
theorem B1061491 : Blo 626299 1061491 := bstep (se 1 (by rfl) ⟨796118, by rfl⟩ : syracuseStep 1061491 = 1592237) B1592237
theorem B3584675 : Blo 626299 3584675 := bstep (se 1 (by rfl) ⟨2688506, by rfl⟩ : syracuseStep 3584675 = 5377013) B5377013
theorem B1061633 : Blo 626299 1061633 := bstep (se 2 (by rfl) ⟨398112, by rfl⟩ : syracuseStep 1061633 = 796225) B796225
theorem B3027725 : Blo 626299 3027725 := bstep (se 3 (by rfl) ⟨567698, by rfl⟩ : syracuseStep 3027725 = 1135397) B1135397
theorem B3683141 : Blo 626299 3683141 := bstep (se 4 (by rfl) ⟨345294, by rfl⟩ : syracuseStep 3683141 = 690589) B690589
theorem B1061761 : Blo 626299 1061761 := bstep (se 2 (by rfl) ⟨398160, by rfl⟩ : syracuseStep 1061761 = 796321) B796321
theorem B1586051 : Blo 626299 1586051 := bstep (se 1 (by rfl) ⟨1189538, by rfl⟩ : syracuseStep 1586051 = 2379077) B2379077
theorem B1061795 : Blo 626299 1061795 := bstep (se 1 (by rfl) ⟨796346, by rfl⟩ : syracuseStep 1061795 = 1592693) B1592693
theorem B1192963 : Blo 626299 1192963 := bstep (se 1 (by rfl) ⟨894722, by rfl⟩ : syracuseStep 1192963 = 1789445) B1789445
theorem B2012177 : Blo 626299 2012177 := bstep (se 2 (by rfl) ⟨754566, by rfl⟩ : syracuseStep 2012177 = 1509133) B1509133
theorem B1061923 : Blo 626299 1061923 := bstep (se 1 (by rfl) ⟨796442, by rfl⟩ : syracuseStep 1061923 = 1592885) B1592885
theorem B1586243 : Blo 626299 1586243 := bstep (se 1 (by rfl) ⟨1189682, by rfl⟩ : syracuseStep 1586243 = 2379365) B2379365
theorem B1193123 : Blo 626299 1193123 := bstep (se 1 (by rfl) ⟨894842, by rfl⟩ : syracuseStep 1193123 = 1789685) B1789685
theorem B1062065 : Blo 626299 1062065 := bstep (se 2 (by rfl) ⟨398274, by rfl⟩ : syracuseStep 1062065 = 796549) B796549
theorem B1062193 : Blo 626299 1062193 := bstep (se 2 (by rfl) ⟨398322, by rfl⟩ : syracuseStep 1062193 = 796645) B796645
theorem B1062227 : Blo 626299 1062227 := bstep (se 1 (by rfl) ⟨796670, by rfl⟩ : syracuseStep 1062227 = 1593341) B1593341
theorem B8041841 : Blo 626299 8041841 := bstep (se 2 (by rfl) ⟨3015690, by rfl⟩ : syracuseStep 8041841 = 6031381) B6031381
theorem B1062355 : Blo 626299 1062355 := bstep (se 1 (by rfl) ⟨796766, by rfl⟩ : syracuseStep 1062355 = 1593533) B1593533
theorem B1062497 : Blo 626299 1062497 := bstep (se 2 (by rfl) ⟨398436, by rfl⟩ : syracuseStep 1062497 = 796873) B796873
theorem B1062625 : Blo 626299 1062625 := bstep (se 2 (by rfl) ⟨398484, by rfl⟩ : syracuseStep 1062625 = 796969) B796969
theorem B669427 : Blo 626299 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B1062659 : Blo 626299 1062659 := bstep (se 1 (by rfl) ⟨796994, by rfl⟩ : syracuseStep 1062659 = 1593989) B1593989
theorem B1062787 : Blo 626299 1062787 := bstep (se 1 (by rfl) ⟨797090, by rfl⟩ : syracuseStep 1062787 = 1594181) B1594181
theorem B1587185 : Blo 626299 1587185 := bstep (se 2 (by rfl) ⟨595194, by rfl⟩ : syracuseStep 1587185 = 1190389) B1190389
theorem B1062929 : Blo 626299 1062929 := bstep (se 2 (by rfl) ⟨398598, by rfl⟩ : syracuseStep 1062929 = 797197) B797197
theorem B1587235 : Blo 626299 1587235 := bstep (se 1 (by rfl) ⟨1190426, by rfl⟩ : syracuseStep 1587235 = 2380853) B2380853
theorem B1783853 : Blo 626299 1783853 := bstep (se 3 (by rfl) ⟨334472, by rfl⟩ : syracuseStep 1783853 = 668945) B668945
theorem B1063057 : Blo 626299 1063057 := bstep (se 2 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 1063057 = 797293) B797293
theorem B1587377 : Blo 626299 1587377 := bstep (se 2 (by rfl) ⟨595266, by rfl⟩ : syracuseStep 1587377 = 1190533) B1190533
theorem B1063091 : Blo 626299 1063091 := bstep (se 1 (by rfl) ⟨797318, by rfl⟩ : syracuseStep 1063091 = 1594637) B1594637
theorem B1194193 : Blo 626299 1194193 := bstep (se 2 (by rfl) ⟨447822, by rfl⟩ : syracuseStep 1194193 = 895645) B895645
theorem B1784045 : Blo 626299 1784045 := bstep (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) B669017
theorem B1063219 : Blo 626299 1063219 := bstep (se 1 (by rfl) ⟨797414, by rfl⟩ : syracuseStep 1063219 = 1594829) B1594829
theorem B1063361 : Blo 626299 1063361 := bstep (se 2 (by rfl) ⟨398760, by rfl⟩ : syracuseStep 1063361 = 797521) B797521
theorem B1063489 : Blo 626299 1063489 := bstep (se 2 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 1063489 = 797617) B797617
theorem B1063523 : Blo 626299 1063523 := bstep (se 1 (by rfl) ⟨797642, by rfl⟩ : syracuseStep 1063523 = 1595285) B1595285
theorem B5454533 : Blo 626299 5454533 := bstep (se 4 (by rfl) ⟨511362, by rfl⟩ : syracuseStep 5454533 = 1022725) B1022725
theorem B3259277 : Blo 626299 3259277 := bstep (se 3 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 3259277 = 1222229) B1222229
theorem B1588369 : Blo 626299 1588369 := bstep (se 2 (by rfl) ⟨595638, by rfl⟩ : syracuseStep 1588369 = 1191277) B1191277
theorem B1785037 : Blo 626299 1785037 := bstep (se 3 (by rfl) ⟨334694, by rfl⟩ : syracuseStep 1785037 = 669389) B669389
theorem B1195249 : Blo 626299 1195249 := bstep (se 2 (by rfl) ⟨448218, by rfl⟩ : syracuseStep 1195249 = 896437) B896437
theorem B1129745 : Blo 626299 1129745 := bstep (se 2 (by rfl) ⟨423654, by rfl⟩ : syracuseStep 1129745 = 847309) B847309
theorem B1817891 : Blo 626299 1817891 := bstep (se 1 (by rfl) ⟨1363418, by rfl⟩ : syracuseStep 1817891 = 2726837) B2726837
theorem B1588643 : Blo 626299 1588643 := bstep (se 1 (by rfl) ⟨1191482, by rfl⟩ : syracuseStep 1588643 = 2382965) B2382965
theorem B2014637 : Blo 626299 2014637 := bstep (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) B755489
theorem B3816881 : Blo 626299 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B4767173 : Blo 626299 4767173 := bstep (se 4 (by rfl) ⟨446922, by rfl⟩ : syracuseStep 4767173 = 893845) B893845
theorem B1588835 : Blo 626299 1588835 := bstep (se 1 (by rfl) ⟨1191626, by rfl⟩ : syracuseStep 1588835 = 2383253) B2383253
theorem B1195651 : Blo 626299 1195651 := bstep (se 1 (by rfl) ⟨896738, by rfl⟩ : syracuseStep 1195651 = 1793477) B1793477
theorem B1195697 : Blo 626299 1195697 := bstep (se 2 (by rfl) ⟨448386, by rfl⟩ : syracuseStep 1195697 = 896773) B896773
theorem B638771 : Blo 626299 638771 := bstep (se 1 (by rfl) ⟨479078, by rfl⟩ : syracuseStep 638771 = 958157) B958157
theorem B1195985 : Blo 626299 1195985 := bstep (se 2 (by rfl) ⟨448494, by rfl⟩ : syracuseStep 1195985 = 896989) B896989
theorem B11321315 : Blo 626299 11321315 := bstep (se 1 (by rfl) ⟨8490986, by rfl⟩ : syracuseStep 11321315 = 16981973) B16981973
theorem B1032259 : Blo 626299 1032259 := bstep (se 1 (by rfl) ⟨774194, by rfl⟩ : syracuseStep 1032259 = 1548389) B1548389
theorem B704659 : Blo 626299 704659 := bstep (se 1 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 704659 = 1056989) B1056989
theorem B1720547 : Blo 626299 1720547 := bstep (se 1 (by rfl) ⟨1290410, by rfl⟩ : syracuseStep 1720547 = 2580821) B2580821
theorem B1130755 : Blo 626299 1130755 := bstep (se 1 (by rfl) ⟨848066, by rfl⟩ : syracuseStep 1130755 = 1696133) B1696133
theorem B704803 : Blo 626299 704803 := bstep (se 1 (by rfl) ⟨528602, by rfl⟩ : syracuseStep 704803 = 1057205) B1057205
theorem B672067 : Blo 626299 672067 := bstep (se 1 (by rfl) ⟨504050, by rfl⟩ : syracuseStep 672067 = 1008101) B1008101
theorem B967043 : Blo 626299 967043 := bstep (se 1 (by rfl) ⟨725282, by rfl⟩ : syracuseStep 967043 = 1450565) B1450565
theorem B2113937 : Blo 626299 2113937 := bstep (se 2 (by rfl) ⟨792726, by rfl⟩ : syracuseStep 2113937 = 1585453) B1585453
theorem B704947 : Blo 626299 704947 := bstep (se 1 (by rfl) ⟨528710, by rfl⟩ : syracuseStep 704947 = 1057421) B1057421
theorem B3817955 : Blo 626299 3817955 := bstep (se 1 (by rfl) ⟨2863466, by rfl⟩ : syracuseStep 3817955 = 5726933) B5726933
theorem B1589777 : Blo 626299 1589777 := bstep (se 2 (by rfl) ⟨596166, by rfl⟩ : syracuseStep 1589777 = 1192333) B1192333
theorem B705091 : Blo 626299 705091 := bstep (se 1 (by rfl) ⟨528818, by rfl⟩ : syracuseStep 705091 = 1057637) B1057637
theorem B1589827 : Blo 626299 1589827 := bstep (se 1 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 1589827 = 2384741) B2384741
theorem B3621581 : Blo 626299 3621581 := bstep (se 3 (by rfl) ⟨679046, by rfl⟩ : syracuseStep 3621581 = 1358093) B1358093
theorem B1589969 : Blo 626299 1589969 := bstep (se 2 (by rfl) ⟨596238, by rfl⟩ : syracuseStep 1589969 = 1192477) B1192477
theorem B705235 : Blo 626299 705235 := bstep (se 1 (by rfl) ⟨528926, by rfl⟩ : syracuseStep 705235 = 1057853) B1057853
theorem B672499 : Blo 626299 672499 := bstep (se 1 (by rfl) ⟨504374, by rfl⟩ : syracuseStep 672499 = 1008749) B1008749
theorem B705379 : Blo 626299 705379 := bstep (se 1 (by rfl) ⟨529034, by rfl⟩ : syracuseStep 705379 = 1058069) B1058069
theorem B1786769 : Blo 626299 1786769 := bstep (se 2 (by rfl) ⟨670038, by rfl⟩ : syracuseStep 1786769 = 1340077) B1340077
theorem B2114477 : Blo 626299 2114477 := bstep (se 3 (by rfl) ⟨396464, by rfl⟩ : syracuseStep 2114477 = 792929) B792929
theorem B2114531 : Blo 626299 2114531 := bstep (se 1 (by rfl) ⟨1585898, by rfl⟩ : syracuseStep 2114531 = 3171797) B3171797
theorem B2016227 : Blo 626299 2016227 := bstep (se 1 (by rfl) ⟨1512170, by rfl⟩ : syracuseStep 2016227 = 3024341) B3024341
theorem B705523 : Blo 626299 705523 := bstep (se 1 (by rfl) ⟨529142, by rfl⟩ : syracuseStep 705523 = 1058285) B1058285
theorem B1786961 : Blo 626299 1786961 := bstep (se 2 (by rfl) ⟨670110, by rfl⟩ : syracuseStep 1786961 = 1340221) B1340221
theorem B1131619 : Blo 626299 1131619 := bstep (se 1 (by rfl) ⟨848714, by rfl⟩ : syracuseStep 1131619 = 1697429) B1697429
theorem B705667 : Blo 626299 705667 := bstep (se 1 (by rfl) ⟨529250, by rfl⟩ : syracuseStep 705667 = 1058501) B1058501
theorem B2114801 : Blo 626299 2114801 := bstep (se 2 (by rfl) ⟨793050, by rfl⟩ : syracuseStep 2114801 = 1586101) B1586101
theorem B8045837 : Blo 626299 8045837 := bstep (se 3 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 8045837 = 3017189) B3017189
theorem B705811 : Blo 626299 705811 := bstep (se 1 (by rfl) ⟨529358, by rfl⟩ : syracuseStep 705811 = 1058717) B1058717
theorem B705955 : Blo 626299 705955 := bstep (se 1 (by rfl) ⟨529466, by rfl⟩ : syracuseStep 705955 = 1058933) B1058933
theorem B706099 : Blo 626299 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B1590961 : Blo 626299 1590961 := bstep (se 2 (by rfl) ⟨596610, by rfl⟩ : syracuseStep 1590961 = 1193221) B1193221
theorem B706243 : Blo 626299 706243 := bstep (se 1 (by rfl) ⟨529682, by rfl⟩ : syracuseStep 706243 = 1059365) B1059365
theorem B2115341 : Blo 626299 2115341 := bstep (se 3 (by rfl) ⟨396626, by rfl⟩ : syracuseStep 2115341 = 793253) B793253
theorem B2115395 : Blo 626299 2115395 := bstep (se 1 (by rfl) ⟨1586546, by rfl⟩ : syracuseStep 2115395 = 3173093) B3173093
theorem B706387 : Blo 626299 706387 := bstep (se 1 (by rfl) ⟨529790, by rfl⟩ : syracuseStep 706387 = 1059581) B1059581
theorem B1591235 : Blo 626299 1591235 := bstep (se 1 (by rfl) ⟨1193426, by rfl⟩ : syracuseStep 1591235 = 2386853) B2386853
theorem B706531 : Blo 626299 706531 := bstep (se 1 (by rfl) ⟨529898, by rfl⟩ : syracuseStep 706531 = 1059797) B1059797
theorem B1787953 : Blo 626299 1787953 := bstep (se 2 (by rfl) ⟨670482, by rfl⟩ : syracuseStep 1787953 = 1340965) B1340965
theorem B2115665 : Blo 626299 2115665 := bstep (se 2 (by rfl) ⟨793374, by rfl⟩ : syracuseStep 2115665 = 1586749) B1586749
theorem B706675 : Blo 626299 706675 := bstep (se 1 (by rfl) ⟨530006, by rfl⟩ : syracuseStep 706675 = 1060013) B1060013
theorem B1591427 : Blo 626299 1591427 := bstep (se 1 (by rfl) ⟨1193570, by rfl⟩ : syracuseStep 1591427 = 2387141) B2387141
theorem B2017457 : Blo 626299 2017457 := bstep (se 2 (by rfl) ⟨756546, by rfl⟩ : syracuseStep 2017457 = 1513093) B1513093
theorem B10733795 : Blo 626299 10733795 := bstep (se 1 (by rfl) ⟨8050346, by rfl⟩ : syracuseStep 10733795 = 16100693) B16100693
theorem B706819 : Blo 626299 706819 := bstep (se 1 (by rfl) ⟨530114, by rfl⟩ : syracuseStep 706819 = 1060229) B1060229
theorem B1788227 : Blo 626299 1788227 := bstep (se 1 (by rfl) ⟨1341170, by rfl⟩ : syracuseStep 1788227 = 2682341) B2682341
theorem B706963 : Blo 626299 706963 := bstep (se 1 (by rfl) ⟨530222, by rfl⟩ : syracuseStep 706963 = 1060445) B1060445
theorem B1788419 : Blo 626299 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B707107 : Blo 626299 707107 := bstep (se 1 (by rfl) ⟨530330, by rfl⟩ : syracuseStep 707107 = 1060661) B1060661
theorem B2116205 : Blo 626299 2116205 := bstep (se 3 (by rfl) ⟨396788, by rfl⟩ : syracuseStep 2116205 = 793577) B793577
theorem B2116259 : Blo 626299 2116259 := bstep (se 1 (by rfl) ⟨1587194, by rfl⟩ : syracuseStep 2116259 = 3174389) B3174389
theorem B707251 : Blo 626299 707251 := bstep (se 1 (by rfl) ⟨530438, by rfl⟩ : syracuseStep 707251 = 1060877) B1060877
theorem B707395 : Blo 626299 707395 := bstep (se 1 (by rfl) ⟨530546, by rfl⟩ : syracuseStep 707395 = 1061093) B1061093
theorem B1526705 : Blo 626299 1526705 := bstep (se 2 (by rfl) ⟨572514, by rfl⟩ : syracuseStep 1526705 = 1145029) B1145029
theorem B2116529 : Blo 626299 2116529 := bstep (se 2 (by rfl) ⟨793698, by rfl⟩ : syracuseStep 2116529 = 1587397) B1587397
theorem B707539 : Blo 626299 707539 := bstep (se 1 (by rfl) ⟨530654, by rfl⟩ : syracuseStep 707539 = 1061309) B1061309
theorem B2018317 : Blo 626299 2018317 := bstep (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) B756869
theorem B1592369 : Blo 626299 1592369 := bstep (se 2 (by rfl) ⟨597138, by rfl⟩ : syracuseStep 1592369 = 1194277) B1194277
theorem B805987 : Blo 626299 805987 := bstep (se 1 (by rfl) ⟨604490, by rfl⟩ : syracuseStep 805987 = 1208981) B1208981
theorem B707683 : Blo 626299 707683 := bstep (se 1 (by rfl) ⟨530762, by rfl⟩ : syracuseStep 707683 = 1061525) B1061525
theorem B1592419 : Blo 626299 1592419 := bstep (se 1 (by rfl) ⟨1194314, by rfl⟩ : syracuseStep 1592419 = 2388629) B2388629
theorem B1592561 : Blo 626299 1592561 := bstep (se 2 (by rfl) ⟨597210, by rfl⟩ : syracuseStep 1592561 = 1194421) B1194421
theorem B707827 : Blo 626299 707827 := bstep (se 1 (by rfl) ⟨530870, by rfl⟩ : syracuseStep 707827 = 1061741) B1061741
theorem B1789229 : Blo 626299 1789229 := bstep (se 3 (by rfl) ⟨335480, by rfl⟩ : syracuseStep 1789229 = 670961) B670961
theorem B707971 : Blo 626299 707971 := bstep (se 1 (by rfl) ⟨530978, by rfl⟩ : syracuseStep 707971 = 1061957) B1061957
theorem B3263921 : Blo 626299 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B2117069 : Blo 626299 2117069 := bstep (se 3 (by rfl) ⟨396950, by rfl⟩ : syracuseStep 2117069 = 793901) B793901
theorem B1789411 : Blo 626299 1789411 := bstep (se 1 (by rfl) ⟨1342058, by rfl⟩ : syracuseStep 1789411 = 2684117) B2684117
theorem B2117123 : Blo 626299 2117123 := bstep (se 1 (by rfl) ⟨1587842, by rfl⟩ : syracuseStep 2117123 = 3175685) B3175685
theorem B708115 : Blo 626299 708115 := bstep (se 1 (by rfl) ⟨531086, by rfl⟩ : syracuseStep 708115 = 1062173) B1062173
theorem B708259 : Blo 626299 708259 := bstep (se 1 (by rfl) ⟨531194, by rfl⟩ : syracuseStep 708259 = 1062389) B1062389
theorem B2117393 : Blo 626299 2117393 := bstep (se 2 (by rfl) ⟨794022, by rfl⟩ : syracuseStep 2117393 = 1588045) B1588045
theorem B1003283 : Blo 626299 1003283 := bstep (se 1 (by rfl) ⟨752462, by rfl⟩ : syracuseStep 1003283 = 1504925) B1504925
theorem B708403 : Blo 626299 708403 := bstep (se 1 (by rfl) ⟨531302, by rfl⟩ : syracuseStep 708403 = 1062605) B1062605
theorem B708547 : Blo 626299 708547 := bstep (se 1 (by rfl) ⟨531410, by rfl⟩ : syracuseStep 708547 = 1062821) B1062821
theorem B1789901 : Blo 626299 1789901 := bstep (se 3 (by rfl) ⟨335606, by rfl⟩ : syracuseStep 1789901 = 671213) B671213
theorem B1003475 : Blo 626299 1003475 := bstep (se 1 (by rfl) ⟨752606, by rfl⟩ : syracuseStep 1003475 = 1505213) B1505213
theorem B1003603 : Blo 626299 1003603 := bstep (se 1 (by rfl) ⟨752702, by rfl⟩ : syracuseStep 1003603 = 1505405) B1505405
theorem B708691 : Blo 626299 708691 := bstep (se 1 (by rfl) ⟨531518, by rfl⟩ : syracuseStep 708691 = 1063037) B1063037
theorem B1593553 : Blo 626299 1593553 := bstep (se 2 (by rfl) ⟨597582, by rfl⟩ : syracuseStep 1593553 = 1195165) B1195165
theorem B24170723 : Blo 626299 24170723 := bstep (se 1 (by rfl) ⟨18128042, by rfl⟩ : syracuseStep 24170723 = 36256085) B36256085
theorem B708835 : Blo 626299 708835 := bstep (se 1 (by rfl) ⟨531626, by rfl⟩ : syracuseStep 708835 = 1063253) B1063253
theorem B2117933 : Blo 626299 2117933 := bstep (se 3 (by rfl) ⟨397112, by rfl⟩ : syracuseStep 2117933 = 794225) B794225
theorem B2117987 : Blo 626299 2117987 := bstep (se 1 (by rfl) ⟨1588490, by rfl⟩ : syracuseStep 2117987 = 3176981) B3176981
theorem B708979 : Blo 626299 708979 := bstep (se 1 (by rfl) ⟨531734, by rfl⟩ : syracuseStep 708979 = 1063469) B1063469
theorem B1429937 : Blo 626299 1429937 := bstep (se 2 (by rfl) ⟨536226, by rfl⟩ : syracuseStep 1429937 = 1072453) B1072453
theorem B1593827 : Blo 626299 1593827 := bstep (se 1 (by rfl) ⟨1195370, by rfl⟩ : syracuseStep 1593827 = 2390741) B2390741
theorem B2380337 : Blo 626299 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B2118257 : Blo 626299 2118257 := bstep (se 2 (by rfl) ⟨794346, by rfl⟩ : syracuseStep 2118257 = 1588693) B1588693
theorem B1594019 : Blo 626299 1594019 := bstep (se 1 (by rfl) ⟨1195514, by rfl⟩ : syracuseStep 1594019 = 2391029) B2391029
theorem B1004243 : Blo 626299 1004243 := bstep (se 1 (by rfl) ⟨753182, by rfl⟩ : syracuseStep 1004243 = 1506365) B1506365
theorem B1004321 : Blo 626299 1004321 := bstep (se 2 (by rfl) ⟨376620, by rfl⟩ : syracuseStep 1004321 = 753241) B753241
theorem B9065357 : Blo 626299 9065357 := bstep (se 3 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 9065357 = 3399509) B3399509
theorem B1791085 : Blo 626299 1791085 := bstep (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) B671657
theorem B2118797 : Blo 626299 2118797 := bstep (se 3 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 2118797 = 794549) B794549
theorem B4773005 : Blo 626299 4773005 := bstep (se 3 (by rfl) ⟨894938, by rfl⟩ : syracuseStep 4773005 = 1789877) B1789877
theorem B1004705 : Blo 626299 1004705 := bstep (se 2 (by rfl) ⟨376764, by rfl⟩ : syracuseStep 1004705 = 753529) B753529
theorem B2118851 : Blo 626299 2118851 := bstep (se 1 (by rfl) ⟨1589138, by rfl⟩ : syracuseStep 2118851 = 3178277) B3178277
theorem B1004833 : Blo 626299 1004833 := bstep (se 2 (by rfl) ⟨376812, by rfl⟩ : syracuseStep 1004833 = 753625) B753625
theorem B906595 : Blo 626299 906595 := bstep (se 1 (by rfl) ⟨679946, by rfl⟩ : syracuseStep 906595 = 1359893) B1359893
theorem B1529201 : Blo 626299 1529201 := bstep (se 2 (by rfl) ⟨573450, by rfl⟩ : syracuseStep 1529201 = 1146901) B1146901
theorem B939473 : Blo 626299 939473 := bstep (se 2 (by rfl) ⟨352302, by rfl⟩ : syracuseStep 939473 = 704605) B704605
theorem B2119121 : Blo 626299 2119121 := bstep (se 2 (by rfl) ⟨794670, by rfl⟩ : syracuseStep 2119121 = 1589341) B1589341
theorem B939491 : Blo 626299 939491 := bstep (se 1 (by rfl) ⟨704618, by rfl⟩ : syracuseStep 939491 = 1409237) B1409237
theorem B939521 : Blo 626299 939521 := bstep (se 2 (by rfl) ⟨352320, by rfl⟩ : syracuseStep 939521 = 704641) B704641
theorem B3823109 : Blo 626299 3823109 := bstep (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) B716833
theorem B939539 : Blo 626299 939539 := bstep (se 1 (by rfl) ⟨704654, by rfl⟩ : syracuseStep 939539 = 1409309) B1409309
theorem B939569 : Blo 626299 939569 := bstep (se 2 (by rfl) ⟨352338, by rfl⟩ : syracuseStep 939569 = 704677) B704677
theorem B939587 : Blo 626299 939587 := bstep (se 1 (by rfl) ⟨704690, by rfl⟩ : syracuseStep 939587 = 1409381) B1409381
theorem B1594961 : Blo 626299 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B939617 : Blo 626299 939617 := bstep (se 2 (by rfl) ⟨352356, by rfl⟩ : syracuseStep 939617 = 704713) B704713
theorem B939635 : Blo 626299 939635 := bstep (se 1 (by rfl) ⟨704726, by rfl⟩ : syracuseStep 939635 = 1409453) B1409453
theorem B1595011 : Blo 626299 1595011 := bstep (se 1 (by rfl) ⟨1196258, by rfl⟩ : syracuseStep 1595011 = 2392517) B2392517
theorem B939665 : Blo 626299 939665 := bstep (se 2 (by rfl) ⟨352374, by rfl⟩ : syracuseStep 939665 = 704749) B704749
theorem B939683 : Blo 626299 939683 := bstep (se 1 (by rfl) ⟨704762, by rfl⟩ : syracuseStep 939683 = 1409525) B1409525
theorem B939713 : Blo 626299 939713 := bstep (se 2 (by rfl) ⟨352392, by rfl⟩ : syracuseStep 939713 = 704785) B704785
theorem B939731 : Blo 626299 939731 := bstep (se 1 (by rfl) ⟨704798, by rfl⟩ : syracuseStep 939731 = 1409597) B1409597
theorem B939761 : Blo 626299 939761 := bstep (se 2 (by rfl) ⟨352410, by rfl⟩ : syracuseStep 939761 = 704821) B704821
theorem B939779 : Blo 626299 939779 := bstep (se 1 (by rfl) ⟨704834, by rfl⟩ : syracuseStep 939779 = 1409669) B1409669
theorem B1595153 : Blo 626299 1595153 := bstep (se 2 (by rfl) ⟨598182, by rfl⟩ : syracuseStep 1595153 = 1196365) B1196365
theorem B939809 : Blo 626299 939809 := bstep (se 2 (by rfl) ⟨352428, by rfl⟩ : syracuseStep 939809 = 704857) B704857
theorem B939827 : Blo 626299 939827 := bstep (se 1 (by rfl) ⟨704870, by rfl⟩ : syracuseStep 939827 = 1409741) B1409741
theorem B939857 : Blo 626299 939857 := bstep (se 2 (by rfl) ⟨352446, by rfl⟩ : syracuseStep 939857 = 704893) B704893
theorem B939875 : Blo 626299 939875 := bstep (se 1 (by rfl) ⟨704906, by rfl⟩ : syracuseStep 939875 = 1409813) B1409813
theorem B939905 : Blo 626299 939905 := bstep (se 2 (by rfl) ⟨352464, by rfl⟩ : syracuseStep 939905 = 704929) B704929
theorem B4020101 : Blo 626299 4020101 := bstep (se 4 (by rfl) ⟨376884, by rfl⟩ : syracuseStep 4020101 = 753769) B753769
theorem B939923 : Blo 626299 939923 := bstep (se 1 (by rfl) ⟨704942, by rfl⟩ : syracuseStep 939923 = 1409885) B1409885
theorem B939953 : Blo 626299 939953 := bstep (se 2 (by rfl) ⟨352482, by rfl⟩ : syracuseStep 939953 = 704965) B704965
theorem B939971 : Blo 626299 939971 := bstep (se 1 (by rfl) ⟨704978, by rfl⟩ : syracuseStep 939971 = 1409957) B1409957
theorem B940001 : Blo 626299 940001 := bstep (se 2 (by rfl) ⟨352500, by rfl⟩ : syracuseStep 940001 = 705001) B705001
theorem B2381795 : Blo 626299 2381795 := bstep (se 1 (by rfl) ⟨1786346, by rfl⟩ : syracuseStep 2381795 = 3572693) B3572693
theorem B2119661 : Blo 626299 2119661 := bstep (se 3 (by rfl) ⟨397436, by rfl⟩ : syracuseStep 2119661 = 794873) B794873
theorem B940019 : Blo 626299 940019 := bstep (se 1 (by rfl) ⟨705014, by rfl⟩ : syracuseStep 940019 = 1410029) B1410029
theorem B940049 : Blo 626299 940049 := bstep (se 2 (by rfl) ⟨352518, by rfl⟩ : syracuseStep 940049 = 705037) B705037
theorem B940067 : Blo 626299 940067 := bstep (se 1 (by rfl) ⟨705050, by rfl⟩ : syracuseStep 940067 = 1410101) B1410101
theorem B2119715 : Blo 626299 2119715 := bstep (se 1 (by rfl) ⟨1589786, by rfl⟩ : syracuseStep 2119715 = 3179573) B3179573
theorem B940097 : Blo 626299 940097 := bstep (se 2 (by rfl) ⟨352536, by rfl⟩ : syracuseStep 940097 = 705073) B705073
theorem B940115 : Blo 626299 940115 := bstep (se 1 (by rfl) ⟨705086, by rfl⟩ : syracuseStep 940115 = 1410173) B1410173
theorem B940145 : Blo 626299 940145 := bstep (se 2 (by rfl) ⟨352554, by rfl⟩ : syracuseStep 940145 = 705109) B705109
theorem B940163 : Blo 626299 940163 := bstep (se 1 (by rfl) ⟨705122, by rfl⟩ : syracuseStep 940163 = 1410245) B1410245
theorem B1792145 : Blo 626299 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B940193 : Blo 626299 940193 := bstep (se 2 (by rfl) ⟨352572, by rfl⟩ : syracuseStep 940193 = 705145) B705145
theorem B940211 : Blo 626299 940211 := bstep (se 1 (by rfl) ⟨705158, by rfl⟩ : syracuseStep 940211 = 1410317) B1410317
theorem B940241 : Blo 626299 940241 := bstep (se 2 (by rfl) ⟨352590, by rfl⟩ : syracuseStep 940241 = 705181) B705181
theorem B940259 : Blo 626299 940259 := bstep (se 1 (by rfl) ⟨705194, by rfl⟩ : syracuseStep 940259 = 1410389) B1410389
theorem B940289 : Blo 626299 940289 := bstep (se 2 (by rfl) ⟨352608, by rfl⟩ : syracuseStep 940289 = 705217) B705217
theorem B940307 : Blo 626299 940307 := bstep (se 1 (by rfl) ⟨705230, by rfl⟩ : syracuseStep 940307 = 1410461) B1410461
theorem B940337 : Blo 626299 940337 := bstep (se 2 (by rfl) ⟨352626, by rfl⟩ : syracuseStep 940337 = 705253) B705253
theorem B2119985 : Blo 626299 2119985 := bstep (se 2 (by rfl) ⟨794994, by rfl⟩ : syracuseStep 2119985 = 1589989) B1589989
theorem B940355 : Blo 626299 940355 := bstep (se 1 (by rfl) ⟨705266, by rfl⟩ : syracuseStep 940355 = 1410533) B1410533
theorem B940385 : Blo 626299 940385 := bstep (se 2 (by rfl) ⟨352644, by rfl⟩ : syracuseStep 940385 = 705289) B705289
theorem B6773105 : Blo 626299 6773105 := bstep (se 2 (by rfl) ⟨2539914, by rfl⟩ : syracuseStep 6773105 = 5079829) B5079829
theorem B940403 : Blo 626299 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B940433 : Blo 626299 940433 := bstep (se 2 (by rfl) ⟨352662, by rfl⟩ : syracuseStep 940433 = 705325) B705325
theorem B940451 : Blo 626299 940451 := bstep (se 1 (by rfl) ⟨705338, by rfl⟩ : syracuseStep 940451 = 1410677) B1410677
theorem B940481 : Blo 626299 940481 := bstep (se 2 (by rfl) ⟨352680, by rfl⟩ : syracuseStep 940481 = 705361) B705361
theorem B940499 : Blo 626299 940499 := bstep (se 1 (by rfl) ⟨705374, by rfl⟩ : syracuseStep 940499 = 1410749) B1410749
theorem B940529 : Blo 626299 940529 := bstep (se 2 (by rfl) ⟨352698, by rfl⟩ : syracuseStep 940529 = 705397) B705397
theorem B940547 : Blo 626299 940547 := bstep (se 1 (by rfl) ⟨705410, by rfl⟩ : syracuseStep 940547 = 1410821) B1410821
theorem B940577 : Blo 626299 940577 := bstep (se 2 (by rfl) ⟨352716, by rfl⟩ : syracuseStep 940577 = 705433) B705433
theorem B2677283 : Blo 626299 2677283 := bstep (se 1 (by rfl) ⟨2007962, by rfl⟩ : syracuseStep 2677283 = 4015925) B4015925
theorem B940595 : Blo 626299 940595 := bstep (se 1 (by rfl) ⟨705446, by rfl⟩ : syracuseStep 940595 = 1410893) B1410893
theorem B940625 : Blo 626299 940625 := bstep (se 2 (by rfl) ⟨352734, by rfl⟩ : syracuseStep 940625 = 705469) B705469
theorem B940643 : Blo 626299 940643 := bstep (se 1 (by rfl) ⟨705482, by rfl⟩ : syracuseStep 940643 = 1410965) B1410965
theorem B940673 : Blo 626299 940673 := bstep (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) B705505
theorem B940691 : Blo 626299 940691 := bstep (se 1 (by rfl) ⟨705518, by rfl⟩ : syracuseStep 940691 = 1411037) B1411037
theorem B940721 : Blo 626299 940721 := bstep (se 2 (by rfl) ⟨352770, by rfl⟩ : syracuseStep 940721 = 705541) B705541
theorem B940739 : Blo 626299 940739 := bstep (se 1 (by rfl) ⟨705554, by rfl⟩ : syracuseStep 940739 = 1411109) B1411109
theorem B940769 : Blo 626299 940769 := bstep (se 2 (by rfl) ⟨352788, by rfl⟩ : syracuseStep 940769 = 705577) B705577
theorem B8575715 : Blo 626299 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B940787 : Blo 626299 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B1006339 : Blo 626299 1006339 := bstep (se 1 (by rfl) ⟨754754, by rfl⟩ : syracuseStep 1006339 = 1509509) B1509509
theorem B940817 : Blo 626299 940817 := bstep (se 2 (by rfl) ⟨352806, by rfl⟩ : syracuseStep 940817 = 705613) B705613
theorem B940835 : Blo 626299 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B1792817 : Blo 626299 1792817 := bstep (se 2 (by rfl) ⟨672306, by rfl⟩ : syracuseStep 1792817 = 1344613) B1344613
theorem B940865 : Blo 626299 940865 := bstep (se 2 (by rfl) ⟨352824, by rfl⟩ : syracuseStep 940865 = 705649) B705649
theorem B2120525 : Blo 626299 2120525 := bstep (se 3 (by rfl) ⟨397598, by rfl⟩ : syracuseStep 2120525 = 795197) B795197
theorem B940883 : Blo 626299 940883 := bstep (se 1 (by rfl) ⟨705662, by rfl⟩ : syracuseStep 940883 = 1411325) B1411325
theorem B940913 : Blo 626299 940913 := bstep (se 2 (by rfl) ⟨352842, by rfl⟩ : syracuseStep 940913 = 705685) B705685
theorem B940931 : Blo 626299 940931 := bstep (se 1 (by rfl) ⟨705698, by rfl⟩ : syracuseStep 940931 = 1411397) B1411397
theorem B2120579 : Blo 626299 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B940961 : Blo 626299 940961 := bstep (se 2 (by rfl) ⟨352860, by rfl⟩ : syracuseStep 940961 = 705721) B705721
theorem B940979 : Blo 626299 940979 := bstep (se 1 (by rfl) ⟨705734, by rfl⟩ : syracuseStep 940979 = 1411469) B1411469
theorem B2382797 : Blo 626299 2382797 := bstep (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) B893549
theorem B941009 : Blo 626299 941009 := bstep (se 2 (by rfl) ⟨352878, by rfl⟩ : syracuseStep 941009 = 705757) B705757
theorem B941027 : Blo 626299 941027 := bstep (se 1 (by rfl) ⟨705770, by rfl⟩ : syracuseStep 941027 = 1411541) B1411541
theorem B6020081 : Blo 626299 6020081 := bstep (se 2 (by rfl) ⟨2257530, by rfl⟩ : syracuseStep 6020081 = 4515061) B4515061
theorem B941057 : Blo 626299 941057 := bstep (se 2 (by rfl) ⟨352896, by rfl⟩ : syracuseStep 941057 = 705793) B705793
theorem B941075 : Blo 626299 941075 := bstep (se 1 (by rfl) ⟨705806, by rfl⟩ : syracuseStep 941075 = 1411613) B1411613
theorem B941105 : Blo 626299 941105 := bstep (se 2 (by rfl) ⟨352914, by rfl⟩ : syracuseStep 941105 = 705829) B705829
theorem B941123 : Blo 626299 941123 := bstep (se 1 (by rfl) ⟨705842, by rfl⟩ : syracuseStep 941123 = 1411685) B1411685
theorem B941153 : Blo 626299 941153 := bstep (se 2 (by rfl) ⟨352932, by rfl⟩ : syracuseStep 941153 = 705865) B705865
theorem B941171 : Blo 626299 941171 := bstep (se 1 (by rfl) ⟨705878, by rfl⟩ : syracuseStep 941171 = 1411757) B1411757
theorem B941201 : Blo 626299 941201 := bstep (se 2 (by rfl) ⟨352950, by rfl⟩ : syracuseStep 941201 = 705901) B705901
theorem B2120849 : Blo 626299 2120849 := bstep (se 2 (by rfl) ⟨795318, by rfl⟩ : syracuseStep 2120849 = 1590637) B1590637
theorem B941219 : Blo 626299 941219 := bstep (se 1 (by rfl) ⟨705914, by rfl⟩ : syracuseStep 941219 = 1411829) B1411829
theorem B941249 : Blo 626299 941249 := bstep (se 2 (by rfl) ⟨352968, by rfl⟩ : syracuseStep 941249 = 705937) B705937
theorem B941267 : Blo 626299 941267 := bstep (se 1 (by rfl) ⟨705950, by rfl⟩ : syracuseStep 941267 = 1411901) B1411901
theorem B941297 : Blo 626299 941297 := bstep (se 2 (by rfl) ⟨352986, by rfl⟩ : syracuseStep 941297 = 705973) B705973
theorem B941315 : Blo 626299 941315 := bstep (se 1 (by rfl) ⟨705986, by rfl⟩ : syracuseStep 941315 = 1411973) B1411973
theorem B941345 : Blo 626299 941345 := bstep (se 2 (by rfl) ⟨353004, by rfl⟩ : syracuseStep 941345 = 706009) B706009
theorem B941363 : Blo 626299 941363 := bstep (se 1 (by rfl) ⟨706022, by rfl⟩ : syracuseStep 941363 = 1412045) B1412045
theorem B941393 : Blo 626299 941393 := bstep (se 2 (by rfl) ⟨353022, by rfl⟩ : syracuseStep 941393 = 706045) B706045
theorem B941411 : Blo 626299 941411 := bstep (se 1 (by rfl) ⟨706058, by rfl⟩ : syracuseStep 941411 = 1412117) B1412117
theorem B941441 : Blo 626299 941441 := bstep (se 2 (by rfl) ⟨353040, by rfl⟩ : syracuseStep 941441 = 706081) B706081
theorem B941459 : Blo 626299 941459 := bstep (se 1 (by rfl) ⟨706094, by rfl⟩ : syracuseStep 941459 = 1412189) B1412189
theorem B1007011 : Blo 626299 1007011 := bstep (se 1 (by rfl) ⟨755258, by rfl⟩ : syracuseStep 1007011 = 1510517) B1510517
theorem B941489 : Blo 626299 941489 := bstep (se 2 (by rfl) ⟨353058, by rfl⟩ : syracuseStep 941489 = 706117) B706117
theorem B941507 : Blo 626299 941507 := bstep (se 1 (by rfl) ⟨706130, by rfl⟩ : syracuseStep 941507 = 1412261) B1412261
theorem B941537 : Blo 626299 941537 := bstep (se 2 (by rfl) ⟨353076, by rfl⟩ : syracuseStep 941537 = 706153) B706153
theorem B2874851 : Blo 626299 2874851 := bstep (se 1 (by rfl) ⟨2156138, by rfl⟩ : syracuseStep 2874851 = 4312277) B4312277
theorem B941555 : Blo 626299 941555 := bstep (se 1 (by rfl) ⟨706166, by rfl⟩ : syracuseStep 941555 = 1412333) B1412333
theorem B941585 : Blo 626299 941585 := bstep (se 2 (by rfl) ⟨353094, by rfl⟩ : syracuseStep 941585 = 706189) B706189
theorem B941603 : Blo 626299 941603 := bstep (se 1 (by rfl) ⟨706202, by rfl⟩ : syracuseStep 941603 = 1412405) B1412405
theorem B941633 : Blo 626299 941633 := bstep (se 2 (by rfl) ⟨353112, by rfl⟩ : syracuseStep 941633 = 706225) B706225
theorem B1433155 : Blo 626299 1433155 := bstep (se 1 (by rfl) ⟨1074866, by rfl⟩ : syracuseStep 1433155 = 2149733) B2149733
theorem B1793603 : Blo 626299 1793603 := bstep (se 1 (by rfl) ⟨1345202, by rfl⟩ : syracuseStep 1793603 = 2690405) B2690405
theorem B941651 : Blo 626299 941651 := bstep (se 1 (by rfl) ⟨706238, by rfl⟩ : syracuseStep 941651 = 1412477) B1412477
theorem B941681 : Blo 626299 941681 := bstep (se 2 (by rfl) ⟨353130, by rfl⟩ : syracuseStep 941681 = 706261) B706261
theorem B941699 : Blo 626299 941699 := bstep (se 1 (by rfl) ⟨706274, by rfl⟩ : syracuseStep 941699 = 1412549) B1412549
theorem B1072801 : Blo 626299 1072801 := bstep (se 2 (by rfl) ⟨402300, by rfl⟩ : syracuseStep 1072801 = 804601) B804601
theorem B941729 : Blo 626299 941729 := bstep (se 2 (by rfl) ⟨353148, by rfl⟩ : syracuseStep 941729 = 706297) B706297
theorem B2121389 : Blo 626299 2121389 := bstep (se 3 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 2121389 = 795521) B795521
theorem B2547377 : Blo 626299 2547377 := bstep (se 2 (by rfl) ⟨955266, by rfl⟩ : syracuseStep 2547377 = 1910533) B1910533
theorem B941747 : Blo 626299 941747 := bstep (se 1 (by rfl) ⟨706310, by rfl⟩ : syracuseStep 941747 = 1412621) B1412621
theorem B941777 : Blo 626299 941777 := bstep (se 2 (by rfl) ⟨353166, by rfl⟩ : syracuseStep 941777 = 706333) B706333
theorem B941795 : Blo 626299 941795 := bstep (se 1 (by rfl) ⟨706346, by rfl⟩ : syracuseStep 941795 = 1412693) B1412693
theorem B2121443 : Blo 626299 2121443 := bstep (se 1 (by rfl) ⟨1591082, by rfl⟩ : syracuseStep 2121443 = 3182165) B3182165
theorem B941825 : Blo 626299 941825 := bstep (se 2 (by rfl) ⟨353184, by rfl⟩ : syracuseStep 941825 = 706369) B706369
theorem B941843 : Blo 626299 941843 := bstep (se 1 (by rfl) ⟨706382, by rfl⟩ : syracuseStep 941843 = 1412765) B1412765
theorem B3825443 : Blo 626299 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B941873 : Blo 626299 941873 := bstep (se 2 (by rfl) ⟨353202, by rfl⟩ : syracuseStep 941873 = 706405) B706405
theorem B941891 : Blo 626299 941891 := bstep (se 1 (by rfl) ⟨706418, by rfl⟩ : syracuseStep 941891 = 1412837) B1412837
theorem B941921 : Blo 626299 941921 := bstep (se 2 (by rfl) ⟨353220, by rfl⟩ : syracuseStep 941921 = 706441) B706441
theorem B1007473 : Blo 626299 1007473 := bstep (se 2 (by rfl) ⟨377802, by rfl⟩ : syracuseStep 1007473 = 755605) B755605
theorem B941939 : Blo 626299 941939 := bstep (se 1 (by rfl) ⟨706454, by rfl⟩ : syracuseStep 941939 = 1412909) B1412909
theorem B1793933 : Blo 626299 1793933 := bstep (se 3 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 1793933 = 672725) B672725
theorem B941969 : Blo 626299 941969 := bstep (se 2 (by rfl) ⟨353238, by rfl⟩ : syracuseStep 941969 = 706477) B706477
theorem B941987 : Blo 626299 941987 := bstep (se 1 (by rfl) ⟨706490, by rfl⟩ : syracuseStep 941987 = 1412981) B1412981
theorem B942017 : Blo 626299 942017 := bstep (se 2 (by rfl) ⟨353256, by rfl⟩ : syracuseStep 942017 = 706513) B706513
theorem B1007569 : Blo 626299 1007569 := bstep (se 2 (by rfl) ⟨377838, by rfl⟩ : syracuseStep 1007569 = 755677) B755677
theorem B1794001 : Blo 626299 1794001 := bstep (se 2 (by rfl) ⟨672750, by rfl⟩ : syracuseStep 1794001 = 1345501) B1345501
theorem B942035 : Blo 626299 942035 := bstep (se 1 (by rfl) ⟨706526, by rfl⟩ : syracuseStep 942035 = 1413053) B1413053
theorem B942065 : Blo 626299 942065 := bstep (se 2 (by rfl) ⟨353274, by rfl⟩ : syracuseStep 942065 = 706549) B706549
theorem B2121713 : Blo 626299 2121713 := bstep (se 2 (by rfl) ⟨795642, by rfl⟩ : syracuseStep 2121713 = 1591285) B1591285
theorem B4775921 : Blo 626299 4775921 := bstep (se 2 (by rfl) ⟨1790970, by rfl⟩ : syracuseStep 4775921 = 3581941) B3581941
theorem B942083 : Blo 626299 942083 := bstep (se 1 (by rfl) ⟨706562, by rfl⟩ : syracuseStep 942083 = 1413125) B1413125
theorem B942113 : Blo 626299 942113 := bstep (se 2 (by rfl) ⟨353292, by rfl⟩ : syracuseStep 942113 = 706585) B706585
theorem B942131 : Blo 626299 942131 := bstep (se 1 (by rfl) ⟨706598, by rfl⟩ : syracuseStep 942131 = 1413197) B1413197
theorem B942161 : Blo 626299 942161 := bstep (se 2 (by rfl) ⟨353310, by rfl⟩ : syracuseStep 942161 = 706621) B706621
theorem B942179 : Blo 626299 942179 := bstep (se 1 (by rfl) ⟨706634, by rfl⟩ : syracuseStep 942179 = 1413269) B1413269
theorem B1007729 : Blo 626299 1007729 := bstep (se 2 (by rfl) ⟨377898, by rfl⟩ : syracuseStep 1007729 = 755797) B755797
theorem B909425 : Blo 626299 909425 := bstep (se 2 (by rfl) ⟨341034, by rfl⟩ : syracuseStep 909425 = 682069) B682069
theorem B942209 : Blo 626299 942209 := bstep (se 2 (by rfl) ⟨353328, by rfl⟩ : syracuseStep 942209 = 706657) B706657
theorem B942227 : Blo 626299 942227 := bstep (se 1 (by rfl) ⟨706670, by rfl⟩ : syracuseStep 942227 = 1413341) B1413341
theorem B1695917 : Blo 626299 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B942257 : Blo 626299 942257 := bstep (se 2 (by rfl) ⟨353346, by rfl⟩ : syracuseStep 942257 = 706693) B706693
theorem B942275 : Blo 626299 942275 := bstep (se 1 (by rfl) ⟨706706, by rfl⟩ : syracuseStep 942275 = 1413413) B1413413
theorem B942305 : Blo 626299 942305 := bstep (se 2 (by rfl) ⟨353364, by rfl⟩ : syracuseStep 942305 = 706729) B706729
theorem B1794275 : Blo 626299 1794275 := bstep (se 1 (by rfl) ⟨1345706, by rfl⟩ : syracuseStep 1794275 = 2691413) B2691413
theorem B942323 : Blo 626299 942323 := bstep (se 1 (by rfl) ⟨706742, by rfl⟩ : syracuseStep 942323 = 1413485) B1413485
theorem B942353 : Blo 626299 942353 := bstep (se 2 (by rfl) ⟨353382, by rfl⟩ : syracuseStep 942353 = 706765) B706765
theorem B942371 : Blo 626299 942371 := bstep (se 1 (by rfl) ⟨706778, by rfl⟩ : syracuseStep 942371 = 1413557) B1413557
theorem B942401 : Blo 626299 942401 := bstep (se 2 (by rfl) ⟨353400, by rfl⟩ : syracuseStep 942401 = 706801) B706801
theorem B7659845 : Blo 626299 7659845 := bstep (se 4 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 7659845 = 1436221) B1436221
theorem B942419 : Blo 626299 942419 := bstep (se 1 (by rfl) ⟨706814, by rfl⟩ : syracuseStep 942419 = 1413629) B1413629
theorem B942449 : Blo 626299 942449 := bstep (se 2 (by rfl) ⟨353418, by rfl⟩ : syracuseStep 942449 = 706837) B706837
theorem B942467 : Blo 626299 942467 := bstep (se 1 (by rfl) ⟨706850, by rfl⟩ : syracuseStep 942467 = 1413701) B1413701
theorem B942497 : Blo 626299 942497 := bstep (se 2 (by rfl) ⟨353436, by rfl⟩ : syracuseStep 942497 = 706873) B706873
theorem B942515 : Blo 626299 942515 := bstep (se 1 (by rfl) ⟨706886, by rfl⟩ : syracuseStep 942515 = 1413773) B1413773
theorem B942545 : Blo 626299 942545 := bstep (se 2 (by rfl) ⟨353454, by rfl⟩ : syracuseStep 942545 = 706909) B706909
theorem B942563 : Blo 626299 942563 := bstep (se 1 (by rfl) ⟨706922, by rfl⟩ : syracuseStep 942563 = 1413845) B1413845
theorem B2679281 : Blo 626299 2679281 := bstep (se 2 (by rfl) ⟨1004730, by rfl⟩ : syracuseStep 2679281 = 2009461) B2009461
theorem B1696241 : Blo 626299 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B942593 : Blo 626299 942593 := bstep (se 2 (by rfl) ⟨353472, by rfl⟩ : syracuseStep 942593 = 706945) B706945
theorem B2122253 : Blo 626299 2122253 := bstep (se 3 (by rfl) ⟨397922, by rfl⟩ : syracuseStep 2122253 = 795845) B795845
theorem B942611 : Blo 626299 942611 := bstep (se 1 (by rfl) ⟨706958, by rfl⟩ : syracuseStep 942611 = 1413917) B1413917
theorem B942641 : Blo 626299 942641 := bstep (se 2 (by rfl) ⟨353490, by rfl⟩ : syracuseStep 942641 = 706981) B706981
theorem B942659 : Blo 626299 942659 := bstep (se 1 (by rfl) ⟨706994, by rfl⟩ : syracuseStep 942659 = 1413989) B1413989
theorem B2122307 : Blo 626299 2122307 := bstep (se 1 (by rfl) ⟨1591730, by rfl⟩ : syracuseStep 2122307 = 3183461) B3183461
theorem B942689 : Blo 626299 942689 := bstep (se 2 (by rfl) ⟨353508, by rfl⟩ : syracuseStep 942689 = 707017) B707017
theorem B942707 : Blo 626299 942707 := bstep (se 1 (by rfl) ⟨707030, by rfl⟩ : syracuseStep 942707 = 1414061) B1414061
theorem B942737 : Blo 626299 942737 := bstep (se 2 (by rfl) ⟨353526, by rfl⟩ : syracuseStep 942737 = 707053) B707053
theorem B942755 : Blo 626299 942755 := bstep (se 1 (by rfl) ⟨707066, by rfl⟩ : syracuseStep 942755 = 1414133) B1414133
theorem B942785 : Blo 626299 942785 := bstep (se 2 (by rfl) ⟨353544, by rfl⟩ : syracuseStep 942785 = 707089) B707089
theorem B942803 : Blo 626299 942803 := bstep (se 1 (by rfl) ⟨707102, by rfl⟩ : syracuseStep 942803 = 1414205) B1414205
theorem B942833 : Blo 626299 942833 := bstep (se 2 (by rfl) ⟨353562, by rfl⟩ : syracuseStep 942833 = 707125) B707125
theorem B942851 : Blo 626299 942851 := bstep (se 1 (by rfl) ⟨707138, by rfl⟩ : syracuseStep 942851 = 1414277) B1414277
theorem B942881 : Blo 626299 942881 := bstep (se 2 (by rfl) ⟨353580, by rfl⟩ : syracuseStep 942881 = 707161) B707161
theorem B3629873 : Blo 626299 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B942899 : Blo 626299 942899 := bstep (se 1 (by rfl) ⟨707174, by rfl⟩ : syracuseStep 942899 = 1414349) B1414349
theorem B3171149 : Blo 626299 3171149 := bstep (se 3 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 3171149 = 1189181) B1189181
theorem B942929 : Blo 626299 942929 := bstep (se 2 (by rfl) ⟨353598, by rfl⟩ : syracuseStep 942929 = 707197) B707197
theorem B2122577 : Blo 626299 2122577 := bstep (se 2 (by rfl) ⟨795966, by rfl⟩ : syracuseStep 2122577 = 1591933) B1591933
theorem B942947 : Blo 626299 942947 := bstep (se 1 (by rfl) ⟨707210, by rfl⟩ : syracuseStep 942947 = 1414421) B1414421
theorem B942977 : Blo 626299 942977 := bstep (se 2 (by rfl) ⟨353616, by rfl⟩ : syracuseStep 942977 = 707233) B707233
theorem B942995 : Blo 626299 942995 := bstep (se 1 (by rfl) ⟨707246, by rfl⟩ : syracuseStep 942995 = 1414493) B1414493
theorem B943025 : Blo 626299 943025 := bstep (se 2 (by rfl) ⟨353634, by rfl⟩ : syracuseStep 943025 = 707269) B707269
theorem B943043 : Blo 626299 943043 := bstep (se 1 (by rfl) ⟨707282, by rfl⟩ : syracuseStep 943043 = 1414565) B1414565
theorem B943073 : Blo 626299 943073 := bstep (se 2 (by rfl) ⟨353652, by rfl⟩ : syracuseStep 943073 = 707305) B707305
theorem B943091 : Blo 626299 943091 := bstep (se 1 (by rfl) ⟨707318, by rfl⟩ : syracuseStep 943091 = 1414637) B1414637
theorem B2384909 : Blo 626299 2384909 := bstep (se 3 (by rfl) ⟨447170, by rfl⟩ : syracuseStep 2384909 = 894341) B894341
theorem B1270801 : Blo 626299 1270801 := bstep (se 2 (by rfl) ⟨476550, by rfl⟩ : syracuseStep 1270801 = 953101) B953101
theorem B943121 : Blo 626299 943121 := bstep (se 2 (by rfl) ⟨353670, by rfl⟩ : syracuseStep 943121 = 707341) B707341
theorem B943139 : Blo 626299 943139 := bstep (se 1 (by rfl) ⟨707354, by rfl⟩ : syracuseStep 943139 = 1414709) B1414709
theorem B943169 : Blo 626299 943169 := bstep (se 2 (by rfl) ⟨353688, by rfl⟩ : syracuseStep 943169 = 707377) B707377
theorem B943187 : Blo 626299 943187 := bstep (se 1 (by rfl) ⟨707390, by rfl⟩ : syracuseStep 943187 = 1414781) B1414781
theorem B943217 : Blo 626299 943217 := bstep (se 2 (by rfl) ⟨353706, by rfl⟩ : syracuseStep 943217 = 707413) B707413
theorem B943235 : Blo 626299 943235 := bstep (se 1 (by rfl) ⟨707426, by rfl⟩ : syracuseStep 943235 = 1414853) B1414853
theorem B943265 : Blo 626299 943265 := bstep (se 2 (by rfl) ⟨353724, by rfl⟩ : syracuseStep 943265 = 707449) B707449
theorem B943283 : Blo 626299 943283 := bstep (se 1 (by rfl) ⟨707462, by rfl⟩ : syracuseStep 943283 = 1414925) B1414925
theorem B943313 : Blo 626299 943313 := bstep (se 2 (by rfl) ⟨353742, by rfl⟩ : syracuseStep 943313 = 707485) B707485
theorem B943331 : Blo 626299 943331 := bstep (se 1 (by rfl) ⟨707498, by rfl⟩ : syracuseStep 943331 = 1414997) B1414997
theorem B943361 : Blo 626299 943361 := bstep (se 2 (by rfl) ⟨353760, by rfl⟩ : syracuseStep 943361 = 707521) B707521
theorem B943379 : Blo 626299 943379 := bstep (se 1 (by rfl) ⟨707534, by rfl⟩ : syracuseStep 943379 = 1415069) B1415069
theorem B943409 : Blo 626299 943409 := bstep (se 2 (by rfl) ⟨353778, by rfl⟩ : syracuseStep 943409 = 707557) B707557
theorem B943427 : Blo 626299 943427 := bstep (se 1 (by rfl) ⟨707570, by rfl⟩ : syracuseStep 943427 = 1415141) B1415141
theorem B5432645 : Blo 626299 5432645 := bstep (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) B1018621
theorem B943457 : Blo 626299 943457 := bstep (se 2 (by rfl) ⟨353796, by rfl⟩ : syracuseStep 943457 = 707593) B707593
theorem B1434979 : Blo 626299 1434979 := bstep (se 1 (by rfl) ⟨1076234, by rfl⟩ : syracuseStep 1434979 = 2152469) B2152469
theorem B2123117 : Blo 626299 2123117 := bstep (se 3 (by rfl) ⟨398084, by rfl⟩ : syracuseStep 2123117 = 796169) B796169
theorem B943475 : Blo 626299 943475 := bstep (se 1 (by rfl) ⟨707606, by rfl⟩ : syracuseStep 943475 = 1415213) B1415213
theorem B943505 : Blo 626299 943505 := bstep (se 2 (by rfl) ⟨353814, by rfl⟩ : syracuseStep 943505 = 707629) B707629
theorem B4023715 : Blo 626299 4023715 := bstep (se 1 (by rfl) ⟨3017786, by rfl⟩ : syracuseStep 4023715 = 6035573) B6035573
theorem B943523 : Blo 626299 943523 := bstep (se 1 (by rfl) ⟨707642, by rfl⟩ : syracuseStep 943523 = 1415285) B1415285
theorem B2123171 : Blo 626299 2123171 := bstep (se 1 (by rfl) ⟨1592378, by rfl⟩ : syracuseStep 2123171 = 3184757) B3184757
theorem B943553 : Blo 626299 943553 := bstep (se 2 (by rfl) ⟨353832, by rfl⟩ : syracuseStep 943553 = 707665) B707665
theorem B943571 : Blo 626299 943571 := bstep (se 1 (by rfl) ⟨707678, by rfl⟩ : syracuseStep 943571 = 1415357) B1415357
theorem B943601 : Blo 626299 943601 := bstep (se 2 (by rfl) ⟨353850, by rfl⟩ : syracuseStep 943601 = 707701) B707701
theorem B943619 : Blo 626299 943619 := bstep (se 1 (by rfl) ⟨707714, by rfl⟩ : syracuseStep 943619 = 1415429) B1415429
theorem B943649 : Blo 626299 943649 := bstep (se 2 (by rfl) ⟨353868, by rfl⟩ : syracuseStep 943649 = 707737) B707737
theorem B943667 : Blo 626299 943667 := bstep (se 1 (by rfl) ⟨707750, by rfl⟩ : syracuseStep 943667 = 1415501) B1415501
theorem B943697 : Blo 626299 943697 := bstep (se 2 (by rfl) ⟨353886, by rfl⟩ : syracuseStep 943697 = 707773) B707773
theorem B943715 : Blo 626299 943715 := bstep (se 1 (by rfl) ⟨707786, by rfl⟩ : syracuseStep 943715 = 1415573) B1415573
theorem B943745 : Blo 626299 943745 := bstep (se 2 (by rfl) ⟨353904, by rfl⟩ : syracuseStep 943745 = 707809) B707809
theorem B7136909 : Blo 626299 7136909 := bstep (se 3 (by rfl) ⟨1338170, by rfl⟩ : syracuseStep 7136909 = 2676341) B2676341
theorem B943763 : Blo 626299 943763 := bstep (se 1 (by rfl) ⟨707822, by rfl⟩ : syracuseStep 943763 = 1415645) B1415645
theorem B2123441 : Blo 626299 2123441 := bstep (se 2 (by rfl) ⟨796290, by rfl⟩ : syracuseStep 2123441 = 1592581) B1592581
theorem B943793 : Blo 626299 943793 := bstep (se 2 (by rfl) ⟨353922, by rfl⟩ : syracuseStep 943793 = 707845) B707845
theorem B943811 : Blo 626299 943811 := bstep (se 1 (by rfl) ⟨707858, by rfl⟩ : syracuseStep 943811 = 1415717) B1415717
theorem B943841 : Blo 626299 943841 := bstep (se 2 (by rfl) ⟨353940, by rfl⟩ : syracuseStep 943841 = 707881) B707881
theorem B943859 : Blo 626299 943859 := bstep (se 1 (by rfl) ⟨707894, by rfl⟩ : syracuseStep 943859 = 1415789) B1415789
theorem B943889 : Blo 626299 943889 := bstep (se 2 (by rfl) ⟨353958, by rfl⟩ : syracuseStep 943889 = 707917) B707917
theorem B943907 : Blo 626299 943907 := bstep (se 1 (by rfl) ⟨707930, by rfl⟩ : syracuseStep 943907 = 1415861) B1415861
theorem B2385713 : Blo 626299 2385713 := bstep (se 2 (by rfl) ⟨894642, by rfl⟩ : syracuseStep 2385713 = 1789285) B1789285
theorem B943937 : Blo 626299 943937 := bstep (se 2 (by rfl) ⟨353976, by rfl⟩ : syracuseStep 943937 = 707953) B707953
theorem B943955 : Blo 626299 943955 := bstep (se 1 (by rfl) ⟨707966, by rfl⟩ : syracuseStep 943955 = 1415933) B1415933
theorem B943985 : Blo 626299 943985 := bstep (se 2 (by rfl) ⟨353994, by rfl⟩ : syracuseStep 943985 = 707989) B707989
theorem B1009523 : Blo 626299 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B944003 : Blo 626299 944003 := bstep (se 1 (by rfl) ⟨708002, by rfl⟩ : syracuseStep 944003 = 1416005) B1416005
theorem B3401605 : Blo 626299 3401605 := bstep (se 4 (by rfl) ⟨318900, by rfl⟩ : syracuseStep 3401605 = 637801) B637801
theorem B944033 : Blo 626299 944033 := bstep (se 2 (by rfl) ⟨354012, by rfl⟩ : syracuseStep 944033 = 708025) B708025
theorem B2549681 : Blo 626299 2549681 := bstep (se 2 (by rfl) ⟨956130, by rfl⟩ : syracuseStep 2549681 = 1912261) B1912261
theorem B944051 : Blo 626299 944051 := bstep (se 1 (by rfl) ⟨708038, by rfl⟩ : syracuseStep 944051 = 1416077) B1416077
theorem B944081 : Blo 626299 944081 := bstep (se 2 (by rfl) ⟨354030, by rfl⟩ : syracuseStep 944081 = 708061) B708061
theorem B944099 : Blo 626299 944099 := bstep (se 1 (by rfl) ⟨708074, by rfl⟩ : syracuseStep 944099 = 1416149) B1416149
theorem B681955 : Blo 626299 681955 := bstep (se 1 (by rfl) ⟨511466, by rfl⟩ : syracuseStep 681955 = 1022933) B1022933
theorem B944129 : Blo 626299 944129 := bstep (se 2 (by rfl) ⟨354048, by rfl⟩ : syracuseStep 944129 = 708097) B708097
theorem B944147 : Blo 626299 944147 := bstep (se 1 (by rfl) ⟨708110, by rfl⟩ : syracuseStep 944147 = 1416221) B1416221
theorem B1271857 : Blo 626299 1271857 := bstep (se 2 (by rfl) ⟨476946, by rfl⟩ : syracuseStep 1271857 = 953893) B953893
theorem B944177 : Blo 626299 944177 := bstep (se 2 (by rfl) ⟨354066, by rfl⟩ : syracuseStep 944177 = 708133) B708133
theorem B944195 : Blo 626299 944195 := bstep (se 1 (by rfl) ⟨708146, by rfl⟩ : syracuseStep 944195 = 1416293) B1416293
theorem B944225 : Blo 626299 944225 := bstep (se 2 (by rfl) ⟨354084, by rfl⟩ : syracuseStep 944225 = 708169) B708169
theorem B944243 : Blo 626299 944243 := bstep (se 1 (by rfl) ⟨708182, by rfl⟩ : syracuseStep 944243 = 1416365) B1416365
theorem B944273 : Blo 626299 944273 := bstep (se 2 (by rfl) ⟨354102, by rfl⟩ : syracuseStep 944273 = 708205) B708205
theorem B944291 : Blo 626299 944291 := bstep (se 1 (by rfl) ⟨708218, by rfl⟩ : syracuseStep 944291 = 1416437) B1416437
theorem B944321 : Blo 626299 944321 := bstep (se 2 (by rfl) ⟨354120, by rfl⟩ : syracuseStep 944321 = 708241) B708241
theorem B2123981 : Blo 626299 2123981 := bstep (se 3 (by rfl) ⟨398246, by rfl⟩ : syracuseStep 2123981 = 796493) B796493
theorem B944339 : Blo 626299 944339 := bstep (se 1 (by rfl) ⟨708254, by rfl⟩ : syracuseStep 944339 = 1416509) B1416509
theorem B944369 : Blo 626299 944369 := bstep (se 2 (by rfl) ⟨354138, by rfl⟩ : syracuseStep 944369 = 708277) B708277
theorem B2124035 : Blo 626299 2124035 := bstep (se 1 (by rfl) ⟨1593026, by rfl⟩ : syracuseStep 2124035 = 3186053) B3186053
theorem B944387 : Blo 626299 944387 := bstep (se 1 (by rfl) ⟨708290, by rfl⟩ : syracuseStep 944387 = 1416581) B1416581
theorem B944417 : Blo 626299 944417 := bstep (se 2 (by rfl) ⟨354156, by rfl⟩ : syracuseStep 944417 = 708313) B708313
theorem B944435 : Blo 626299 944435 := bstep (se 1 (by rfl) ⟨708326, by rfl⟩ : syracuseStep 944435 = 1416653) B1416653
theorem B944465 : Blo 626299 944465 := bstep (se 2 (by rfl) ⟨354174, by rfl⟩ : syracuseStep 944465 = 708349) B708349
theorem B944483 : Blo 626299 944483 := bstep (se 1 (by rfl) ⟨708362, by rfl⟩ : syracuseStep 944483 = 1416725) B1416725
theorem B944513 : Blo 626299 944513 := bstep (se 2 (by rfl) ⟨354192, by rfl⟩ : syracuseStep 944513 = 708385) B708385
theorem B944531 : Blo 626299 944531 := bstep (se 1 (by rfl) ⟨708398, by rfl⟩ : syracuseStep 944531 = 1416797) B1416797
theorem B944561 : Blo 626299 944561 := bstep (se 2 (by rfl) ⟨354210, by rfl⟩ : syracuseStep 944561 = 708421) B708421
theorem B944579 : Blo 626299 944579 := bstep (se 1 (by rfl) ⟨708434, by rfl⟩ : syracuseStep 944579 = 1416869) B1416869
theorem B2386381 : Blo 626299 2386381 := bstep (se 3 (by rfl) ⟨447446, by rfl⟩ : syracuseStep 2386381 = 894893) B894893
theorem B944609 : Blo 626299 944609 := bstep (se 2 (by rfl) ⟨354228, by rfl⟩ : syracuseStep 944609 = 708457) B708457
theorem B3631601 : Blo 626299 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B944627 : Blo 626299 944627 := bstep (se 1 (by rfl) ⟨708470, by rfl⟩ : syracuseStep 944627 = 1416941) B1416941
theorem B2124305 : Blo 626299 2124305 := bstep (se 2 (by rfl) ⟨796614, by rfl⟩ : syracuseStep 2124305 = 1593229) B1593229
theorem B944657 : Blo 626299 944657 := bstep (se 2 (by rfl) ⟨354246, by rfl⟩ : syracuseStep 944657 = 708493) B708493
theorem B944675 : Blo 626299 944675 := bstep (se 1 (by rfl) ⟨708506, by rfl⟩ : syracuseStep 944675 = 1417013) B1417013
theorem B944705 : Blo 626299 944705 := bstep (se 2 (by rfl) ⟨354264, by rfl⟩ : syracuseStep 944705 = 708529) B708529
theorem B944723 : Blo 626299 944723 := bstep (se 1 (by rfl) ⟨708542, by rfl⟩ : syracuseStep 944723 = 1417085) B1417085
theorem B1698403 : Blo 626299 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B1075825 : Blo 626299 1075825 := bstep (se 2 (by rfl) ⟨403434, by rfl⟩ : syracuseStep 1075825 = 806869) B806869
theorem B944753 : Blo 626299 944753 := bstep (se 2 (by rfl) ⟨354282, by rfl⟩ : syracuseStep 944753 = 708565) B708565
theorem B944771 : Blo 626299 944771 := bstep (se 1 (by rfl) ⟨708578, by rfl⟩ : syracuseStep 944771 = 1417157) B1417157
theorem B944801 : Blo 626299 944801 := bstep (se 2 (by rfl) ⟨354300, by rfl⟩ : syracuseStep 944801 = 708601) B708601
theorem B944819 : Blo 626299 944819 := bstep (se 1 (by rfl) ⟨708614, by rfl⟩ : syracuseStep 944819 = 1417229) B1417229
theorem B944849 : Blo 626299 944849 := bstep (se 2 (by rfl) ⟨354318, by rfl⟩ : syracuseStep 944849 = 708637) B708637
theorem B944867 : Blo 626299 944867 := bstep (se 1 (by rfl) ⟨708650, by rfl⟩ : syracuseStep 944867 = 1417301) B1417301
theorem B944897 : Blo 626299 944897 := bstep (se 2 (by rfl) ⟨354336, by rfl⟩ : syracuseStep 944897 = 708673) B708673
theorem B944915 : Blo 626299 944915 := bstep (se 1 (by rfl) ⟨708686, by rfl⟩ : syracuseStep 944915 = 1417373) B1417373
theorem B944945 : Blo 626299 944945 := bstep (se 2 (by rfl) ⟨354354, by rfl⟩ : syracuseStep 944945 = 708709) B708709
theorem B944963 : Blo 626299 944963 := bstep (se 1 (by rfl) ⟨708722, by rfl⟩ : syracuseStep 944963 = 1417445) B1417445
theorem B1698641 : Blo 626299 1698641 := bstep (se 2 (by rfl) ⟨636990, by rfl⟩ : syracuseStep 1698641 = 1273981) B1273981
theorem B944993 : Blo 626299 944993 := bstep (se 2 (by rfl) ⟨354372, by rfl⟩ : syracuseStep 944993 = 708745) B708745
theorem B945011 : Blo 626299 945011 := bstep (se 1 (by rfl) ⟨708758, by rfl⟩ : syracuseStep 945011 = 1417517) B1417517
theorem B6024077 : Blo 626299 6024077 := bstep (se 3 (by rfl) ⟨1129514, by rfl⟩ : syracuseStep 6024077 = 2259029) B2259029
theorem B2681741 : Blo 626299 2681741 := bstep (se 3 (by rfl) ⟨502826, by rfl⟩ : syracuseStep 2681741 = 1005653) B1005653
theorem B1338257 : Blo 626299 1338257 := bstep (se 2 (by rfl) ⟨501846, by rfl⟩ : syracuseStep 1338257 = 1003693) B1003693
theorem B945041 : Blo 626299 945041 := bstep (se 2 (by rfl) ⟨354390, by rfl⟩ : syracuseStep 945041 = 708781) B708781
theorem B945059 : Blo 626299 945059 := bstep (se 1 (by rfl) ⟨708794, by rfl⟩ : syracuseStep 945059 = 1417589) B1417589
theorem B945089 : Blo 626299 945089 := bstep (se 2 (by rfl) ⟨354408, by rfl⟩ : syracuseStep 945089 = 708817) B708817
theorem B945107 : Blo 626299 945107 := bstep (se 1 (by rfl) ⟨708830, by rfl⟩ : syracuseStep 945107 = 1417661) B1417661
theorem B945137 : Blo 626299 945137 := bstep (se 2 (by rfl) ⟨354426, by rfl⟩ : syracuseStep 945137 = 708853) B708853
theorem B945155 : Blo 626299 945155 := bstep (se 1 (by rfl) ⟨708866, by rfl⟩ : syracuseStep 945155 = 1417733) B1417733
theorem B945185 : Blo 626299 945185 := bstep (se 2 (by rfl) ⟨354444, by rfl⟩ : syracuseStep 945185 = 708889) B708889
theorem B2124845 : Blo 626299 2124845 := bstep (se 3 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 2124845 = 796817) B796817
theorem B945203 : Blo 626299 945203 := bstep (se 1 (by rfl) ⟨708902, by rfl⟩ : syracuseStep 945203 = 1417805) B1417805
theorem B945233 : Blo 626299 945233 := bstep (se 2 (by rfl) ⟨354462, by rfl⟩ : syracuseStep 945233 = 708925) B708925
theorem B2124899 : Blo 626299 2124899 := bstep (se 1 (by rfl) ⟨1593674, by rfl⟩ : syracuseStep 2124899 = 3187349) B3187349
theorem B945251 : Blo 626299 945251 := bstep (se 1 (by rfl) ⟨708938, by rfl⟩ : syracuseStep 945251 = 1417877) B1417877
theorem B945281 : Blo 626299 945281 := bstep (se 2 (by rfl) ⟨354480, by rfl⟩ : syracuseStep 945281 = 708961) B708961
theorem B945299 : Blo 626299 945299 := bstep (se 1 (by rfl) ⟨708974, by rfl⟩ : syracuseStep 945299 = 1417949) B1417949
theorem B1273009 : Blo 626299 1273009 := bstep (se 2 (by rfl) ⟨477378, by rfl⟩ : syracuseStep 1273009 = 954757) B954757
theorem B945329 : Blo 626299 945329 := bstep (se 2 (by rfl) ⟨354498, by rfl⟩ : syracuseStep 945329 = 708997) B708997
theorem B945347 : Blo 626299 945347 := bstep (se 1 (by rfl) ⟨709010, by rfl⟩ : syracuseStep 945347 = 1418021) B1418021
theorem B945377 : Blo 626299 945377 := bstep (se 2 (by rfl) ⟨354516, by rfl⟩ : syracuseStep 945377 = 709033) B709033
theorem B2387171 : Blo 626299 2387171 := bstep (se 1 (by rfl) ⟨1790378, by rfl⟩ : syracuseStep 2387171 = 3580757) B3580757
theorem B945395 : Blo 626299 945395 := bstep (se 1 (by rfl) ⟨709046, by rfl⟩ : syracuseStep 945395 = 1418093) B1418093
theorem B945425 : Blo 626299 945425 := bstep (se 2 (by rfl) ⟨354534, by rfl⟩ : syracuseStep 945425 = 709069) B709069
theorem B945443 : Blo 626299 945443 := bstep (se 1 (by rfl) ⟨709082, by rfl⟩ : syracuseStep 945443 = 1418165) B1418165
theorem B2125169 : Blo 626299 2125169 := bstep (se 2 (by rfl) ⟨796938, by rfl⟩ : syracuseStep 2125169 = 1593877) B1593877
theorem B6057443 : Blo 626299 6057443 := bstep (se 1 (by rfl) ⟨4543082, by rfl⟩ : syracuseStep 6057443 = 9086165) B9086165
theorem B1076755 : Blo 626299 1076755 := bstep (se 1 (by rfl) ⟨807566, by rfl⟩ : syracuseStep 1076755 = 1615133) B1615133
theorem B3174065 : Blo 626299 3174065 := bstep (se 2 (by rfl) ⟨1190274, by rfl⟩ : syracuseStep 3174065 = 2380549) B2380549
theorem B4091633 : Blo 626299 4091633 := bstep (se 2 (by rfl) ⟨1534362, by rfl⟩ : syracuseStep 4091633 = 3068725) B3068725
theorem B2715491 : Blo 626299 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B2387825 : Blo 626299 2387825 := bstep (se 2 (by rfl) ⟨895434, by rfl⟩ : syracuseStep 2387825 = 1790869) B1790869
theorem B2125709 : Blo 626299 2125709 := bstep (se 3 (by rfl) ⟨398570, by rfl⟩ : syracuseStep 2125709 = 797141) B797141
theorem B2125763 : Blo 626299 2125763 := bstep (se 1 (by rfl) ⟨1594322, by rfl⟩ : syracuseStep 2125763 = 3188645) B3188645
theorem B15331349 : Blo 626299 15331349 := bstep (se 6 (by rfl) ⟨359328, by rfl⟩ : syracuseStep 15331349 = 718657) B718657
theorem B3403853 : Blo 626299 3403853 := bstep (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) B1276445
theorem B4026509 : Blo 626299 4026509 := bstep (se 3 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 4026509 = 1509941) B1509941
theorem B2126033 : Blo 626299 2126033 := bstep (se 2 (by rfl) ⟨797262, by rfl⟩ : syracuseStep 2126033 = 1594525) B1594525
theorem B2683313 : Blo 626299 2683313 := bstep (se 2 (by rfl) ⟨1006242, by rfl⟩ : syracuseStep 2683313 = 2012485) B2012485
theorem B1274321 : Blo 626299 1274321 := bstep (se 2 (by rfl) ⟨477870, by rfl⟩ : syracuseStep 1274321 = 955741) B955741
theorem B7139825 : Blo 626299 7139825 := bstep (se 2 (by rfl) ⟨2677434, by rfl⟩ : syracuseStep 7139825 = 5354869) B5354869
theorem B14676677 : Blo 626299 14676677 := bstep (se 4 (by rfl) ⟨1375938, by rfl⟩ : syracuseStep 14676677 = 2751877) B2751877
theorem B2126573 : Blo 626299 2126573 := bstep (se 3 (by rfl) ⟨398732, by rfl⟩ : syracuseStep 2126573 = 797465) B797465
theorem B1700621 : Blo 626299 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B2126627 : Blo 626299 2126627 := bstep (se 1 (by rfl) ⟨1594970, by rfl⟩ : syracuseStep 2126627 = 3189941) B3189941
theorem B2126897 : Blo 626299 2126897 := bstep (se 2 (by rfl) ⟨797586, by rfl⟩ : syracuseStep 2126897 = 1595173) B1595173
theorem B3175523 : Blo 626299 3175523 := bstep (se 1 (by rfl) ⟨2381642, by rfl⟩ : syracuseStep 3175523 = 4763285) B4763285
theorem B2389283 : Blo 626299 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B2389297 : Blo 626299 2389297 := bstep (se 2 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 2389297 = 1791973) B1791973
theorem B3569093 : Blo 626299 3569093 := bstep (se 4 (by rfl) ⟨334602, by rfl⟩ : syracuseStep 3569093 = 669205) B669205
theorem B1341041 : Blo 626299 1341041 := bstep (se 2 (by rfl) ⟨502890, by rfl⟩ : syracuseStep 1341041 = 1005781) B1005781
theorem B3176333 : Blo 626299 3176333 := bstep (se 3 (by rfl) ⟨595562, by rfl⟩ : syracuseStep 3176333 = 1191125) B1191125
theorem B2422669 : Blo 626299 2422669 := bstep (se 3 (by rfl) ⟨454250, by rfl⟩ : syracuseStep 2422669 = 908501) B908501
theorem B3569777 : Blo 626299 3569777 := bstep (se 2 (by rfl) ⟨1338666, by rfl⟩ : syracuseStep 3569777 = 2677333) B2677333
theorem B8157509 : Blo 626299 8157509 := bstep (se 4 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 8157509 = 1529533) B1529533
theorem B2259377 : Blo 626299 2259377 := bstep (se 2 (by rfl) ⟨847266, by rfl⟩ : syracuseStep 2259377 = 1694533) B1694533
theorem B1505827 : Blo 626299 1505827 := bstep (se 1 (by rfl) ⟨1129370, by rfl⟩ : syracuseStep 1505827 = 2258741) B2258741
theorem B2390755 : Blo 626299 2390755 := bstep (se 1 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 2390755 = 3586133) B3586133
theorem B1702705 : Blo 626299 1702705 := bstep (se 2 (by rfl) ⟨638514, by rfl⟩ : syracuseStep 1702705 = 1277029) B1277029
theorem B2685773 : Blo 626299 2685773 := bstep (se 3 (by rfl) ⟨503582, by rfl⟩ : syracuseStep 2685773 = 1007165) B1007165
theorem B1506289 : Blo 626299 1506289 := bstep (se 2 (by rfl) ⟨564858, by rfl⟩ : syracuseStep 1506289 = 1129717) B1129717
theorem B2686115 : Blo 626299 2686115 := bstep (se 1 (by rfl) ⟨2014586, by rfl⟩ : syracuseStep 2686115 = 4029173) B4029173
theorem B3439949 : Blo 626299 3439949 := bstep (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) B1289981
theorem B3571235 : Blo 626299 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B851521 : Blo 626299 851521 := bstep (se 2 (by rfl) ⟨319320, by rfl⟩ : syracuseStep 851521 = 638641) B638641
theorem B8027747 : Blo 626299 8027747 := bstep (se 1 (by rfl) ⟨6020810, by rfl⟩ : syracuseStep 8027747 = 12041621) B12041621
theorem B34930763 : Blo 626299 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B1376345 : Blo 626299 1376345 := bstep (se 2 (by rfl) ⟨516129, by rfl⟩ : syracuseStep 1376345 = 1032259) B1032259
theorem B3670147 : Blo 626299 3670147 := bstep (se 1 (by rfl) ⟨2752610, by rfl⟩ : syracuseStep 3670147 = 5505221) B5505221
theorem B1147031 : Blo 626299 1147031 := bstep (se 1 (by rfl) ⟨860273, by rfl⟩ : syracuseStep 1147031 = 1720547) B1720547
theorem B1409291 : Blo 626299 1409291 := bstep (se 1 (by rfl) ⟨1056968, by rfl⟩ : syracuseStep 1409291 = 2113937) B2113937
theorem B2425133 : Blo 626299 2425133 := bstep (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) B909425
theorem B1409345 : Blo 626299 1409345 := bstep (se 2 (by rfl) ⟨528504, by rfl⟩ : syracuseStep 1409345 = 1057009) B1057009
theorem B1507673 : Blo 626299 1507673 := bstep (se 2 (by rfl) ⟨565377, by rfl⟩ : syracuseStep 1507673 = 1130755) B1130755
theorem B1409561 : Blo 626299 1409561 := bstep (se 2 (by rfl) ⟨528585, by rfl⟩ : syracuseStep 1409561 = 1057171) B1057171
theorem B1409651 : Blo 626299 1409651 := bstep (se 1 (by rfl) ⟨1057238, by rfl⟩ : syracuseStep 1409651 = 2114477) B2114477
theorem B1409687 : Blo 626299 1409687 := bstep (se 1 (by rfl) ⟨1057265, by rfl⟩ : syracuseStep 1409687 = 2114531) B2114531
theorem B1344151 : Blo 626299 1344151 := bstep (se 1 (by rfl) ⟨1008113, by rfl⟩ : syracuseStep 1344151 = 2016227) B2016227
theorem B1409867 : Blo 626299 1409867 := bstep (se 1 (by rfl) ⟨1057400, by rfl⟩ : syracuseStep 1409867 = 2114801) B2114801
theorem B1409921 : Blo 626299 1409921 := bstep (se 2 (by rfl) ⟨528720, by rfl⟩ : syracuseStep 1409921 = 1057441) B1057441
theorem B2294701 : Blo 626299 2294701 := bstep (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) B860513
theorem B1410137 : Blo 626299 1410137 := bstep (se 2 (by rfl) ⟨528801, by rfl⟩ : syracuseStep 1410137 = 1057603) B1057603
theorem B1410227 : Blo 626299 1410227 := bstep (se 1 (by rfl) ⟨1057670, by rfl⟩ : syracuseStep 1410227 = 2115341) B2115341
theorem B1410263 : Blo 626299 1410263 := bstep (se 1 (by rfl) ⟨1057697, by rfl⟩ : syracuseStep 1410263 = 2115395) B2115395
theorem B4523309 : Blo 626299 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B2458925 : Blo 626299 2458925 := bstep (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) B922097
theorem B1410443 : Blo 626299 1410443 := bstep (se 1 (by rfl) ⟨1057832, by rfl⟩ : syracuseStep 1410443 = 2115665) B2115665
theorem B1410497 : Blo 626299 1410497 := bstep (se 2 (by rfl) ⟨528936, by rfl⟩ : syracuseStep 1410497 = 1057873) B1057873
theorem B1344971 : Blo 626299 1344971 := bstep (se 1 (by rfl) ⟨1008728, by rfl⟩ : syracuseStep 1344971 = 2017457) B2017457
theorem B1508825 : Blo 626299 1508825 := bstep (se 2 (by rfl) ⟨565809, by rfl⟩ : syracuseStep 1508825 = 1131619) B1131619
theorem B2688643 : Blo 626299 2688643 := bstep (se 1 (by rfl) ⟨2016482, by rfl⟩ : syracuseStep 2688643 = 4032965) B4032965
theorem B1410713 : Blo 626299 1410713 := bstep (se 2 (by rfl) ⟨529017, by rfl⟩ : syracuseStep 1410713 = 1058035) B1058035
theorem B1410803 : Blo 626299 1410803 := bstep (se 1 (by rfl) ⟨1058102, by rfl⟩ : syracuseStep 1410803 = 2116205) B2116205
theorem B1410839 : Blo 626299 1410839 := bstep (se 1 (by rfl) ⟨1058129, by rfl⟩ : syracuseStep 1410839 = 2116259) B2116259
theorem B1017803 : Blo 626299 1017803 := bstep (se 1 (by rfl) ⟨763352, by rfl⟩ : syracuseStep 1017803 = 1526705) B1526705
theorem B1411019 : Blo 626299 1411019 := bstep (se 1 (by rfl) ⟨1058264, by rfl⟩ : syracuseStep 1411019 = 2116529) B2116529
theorem B1411073 : Blo 626299 1411073 := bstep (se 2 (by rfl) ⟨529152, by rfl⟩ : syracuseStep 1411073 = 1058305) B1058305
theorem B1411289 : Blo 626299 1411289 := bstep (se 2 (by rfl) ⟨529233, by rfl⟩ : syracuseStep 1411289 = 1058467) B1058467
theorem B3016921 : Blo 626299 3016921 := bstep (se 2 (by rfl) ⟨1131345, by rfl⟩ : syracuseStep 3016921 = 2262691) B2262691
theorem B1411379 : Blo 626299 1411379 := bstep (se 1 (by rfl) ⟨1058534, by rfl⟩ : syracuseStep 1411379 = 2117069) B2117069
theorem B3017035 : Blo 626299 3017035 := bstep (se 1 (by rfl) ⟨2262776, by rfl⟩ : syracuseStep 3017035 = 4525553) B4525553
theorem B1411415 : Blo 626299 1411415 := bstep (se 1 (by rfl) ⟨1058561, by rfl⟩ : syracuseStep 1411415 = 2117123) B2117123
theorem B1411595 : Blo 626299 1411595 := bstep (se 1 (by rfl) ⟨1058696, by rfl⟩ : syracuseStep 1411595 = 2117393) B2117393
theorem B1411649 : Blo 626299 1411649 := bstep (se 2 (by rfl) ⟨529368, by rfl⟩ : syracuseStep 1411649 = 1058737) B1058737
theorem B1411865 : Blo 626299 1411865 := bstep (se 2 (by rfl) ⟨529449, by rfl⟩ : syracuseStep 1411865 = 1058899) B1058899
theorem B4524835 : Blo 626299 4524835 := bstep (se 1 (by rfl) ⟨3393626, by rfl⟩ : syracuseStep 4524835 = 6787253) B6787253
theorem B3017537 : Blo 626299 3017537 := bstep (se 2 (by rfl) ⟨1131576, by rfl⟩ : syracuseStep 3017537 = 2263153) B2263153
theorem B1411955 : Blo 626299 1411955 := bstep (se 1 (by rfl) ⟨1058966, by rfl⟩ : syracuseStep 1411955 = 2117933) B2117933
theorem B1411991 : Blo 626299 1411991 := bstep (se 1 (by rfl) ⟨1058993, by rfl⟩ : syracuseStep 1411991 = 2117987) B2117987
theorem B953291 : Blo 626299 953291 := bstep (se 1 (by rfl) ⟨714968, by rfl⟩ : syracuseStep 953291 = 1429937) B1429937
theorem B1412171 : Blo 626299 1412171 := bstep (se 1 (by rfl) ⟨1059128, by rfl⟩ : syracuseStep 1412171 = 2118257) B2118257
theorem B1412225 : Blo 626299 1412225 := bstep (se 2 (by rfl) ⟨529584, by rfl⟩ : syracuseStep 1412225 = 1059169) B1059169
theorem B3181841 : Blo 626299 3181841 := bstep (se 2 (by rfl) ⟨1193190, by rfl⟩ : syracuseStep 3181841 = 2386381) B2386381
theorem B1412441 : Blo 626299 1412441 := bstep (se 2 (by rfl) ⟨529665, by rfl⟩ : syracuseStep 1412441 = 1059331) B1059331
theorem B2690455 : Blo 626299 2690455 := bstep (se 1 (by rfl) ⟨2017841, by rfl⟩ : syracuseStep 2690455 = 4035683) B4035683
theorem B1412531 : Blo 626299 1412531 := bstep (se 1 (by rfl) ⟨1059398, by rfl⟩ : syracuseStep 1412531 = 2118797) B2118797
theorem B3182003 : Blo 626299 3182003 := bstep (se 1 (by rfl) ⟨2386502, by rfl⟩ : syracuseStep 3182003 = 4773005) B4773005
theorem B1412567 : Blo 626299 1412567 := bstep (se 1 (by rfl) ⟨1059425, by rfl⟩ : syracuseStep 1412567 = 2118851) B2118851
theorem B2264537 : Blo 626299 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B1019467 : Blo 626299 1019467 := bstep (se 1 (by rfl) ⟨764600, by rfl⟩ : syracuseStep 1019467 = 1529201) B1529201
theorem B626315 : Blo 626299 626315 := bstep (se 1 (by rfl) ⟨469736, by rfl⟩ : syracuseStep 626315 = 939473) B939473
theorem B1412747 : Blo 626299 1412747 := bstep (se 1 (by rfl) ⟨1059560, by rfl⟩ : syracuseStep 1412747 = 2119121) B2119121
theorem B626327 : Blo 626299 626327 := bstep (se 1 (by rfl) ⟨469745, by rfl⟩ : syracuseStep 626327 = 939491) B939491
theorem B626347 : Blo 626299 626347 := bstep (se 1 (by rfl) ⟨469760, by rfl⟩ : syracuseStep 626347 = 939521) B939521
theorem B626359 : Blo 626299 626359 := bstep (se 1 (by rfl) ⟨469769, by rfl⟩ : syracuseStep 626359 = 939539) B939539
theorem B1412801 : Blo 626299 1412801 := bstep (se 2 (by rfl) ⟨529800, by rfl⟩ : syracuseStep 1412801 = 1059601) B1059601
theorem B626379 : Blo 626299 626379 := bstep (se 1 (by rfl) ⟨469784, by rfl⟩ : syracuseStep 626379 = 939569) B939569
theorem B626391 : Blo 626299 626391 := bstep (se 1 (by rfl) ⟨469793, by rfl⟩ : syracuseStep 626391 = 939587) B939587
theorem B626411 : Blo 626299 626411 := bstep (se 1 (by rfl) ⟨469808, by rfl⟩ : syracuseStep 626411 = 939617) B939617
theorem B626423 : Blo 626299 626423 := bstep (se 1 (by rfl) ⟨469817, by rfl⟩ : syracuseStep 626423 = 939635) B939635
theorem B626443 : Blo 626299 626443 := bstep (se 1 (by rfl) ⟨469832, by rfl⟩ : syracuseStep 626443 = 939665) B939665
theorem B626455 : Blo 626299 626455 := bstep (se 1 (by rfl) ⟨469841, by rfl⟩ : syracuseStep 626455 = 939683) B939683
theorem B626475 : Blo 626299 626475 := bstep (se 1 (by rfl) ⟨469856, by rfl⟩ : syracuseStep 626475 = 939713) B939713
theorem B626487 : Blo 626299 626487 := bstep (se 1 (by rfl) ⟨469865, by rfl⟩ : syracuseStep 626487 = 939731) B939731
theorem B626507 : Blo 626299 626507 := bstep (se 1 (by rfl) ⟨469880, by rfl⟩ : syracuseStep 626507 = 939761) B939761
theorem B626519 : Blo 626299 626519 := bstep (se 1 (by rfl) ⟨469889, by rfl⟩ : syracuseStep 626519 = 939779) B939779
theorem B626539 : Blo 626299 626539 := bstep (se 1 (by rfl) ⟨469904, by rfl⟩ : syracuseStep 626539 = 939809) B939809
theorem B626551 : Blo 626299 626551 := bstep (se 1 (by rfl) ⟨469913, by rfl⟩ : syracuseStep 626551 = 939827) B939827
theorem B626571 : Blo 626299 626571 := bstep (se 1 (by rfl) ⟨469928, by rfl⟩ : syracuseStep 626571 = 939857) B939857
theorem B626583 : Blo 626299 626583 := bstep (se 1 (by rfl) ⟨469937, by rfl⟩ : syracuseStep 626583 = 939875) B939875
theorem B1413017 : Blo 626299 1413017 := bstep (se 2 (by rfl) ⟨529881, by rfl⟩ : syracuseStep 1413017 = 1059763) B1059763
theorem B626603 : Blo 626299 626603 := bstep (se 1 (by rfl) ⟨469952, by rfl⟩ : syracuseStep 626603 = 939905) B939905
theorem B626615 : Blo 626299 626615 := bstep (se 1 (by rfl) ⟨469961, by rfl⟩ : syracuseStep 626615 = 939923) B939923
theorem B626635 : Blo 626299 626635 := bstep (se 1 (by rfl) ⟨469976, by rfl⟩ : syracuseStep 626635 = 939953) B939953
theorem B2297803 : Blo 626299 2297803 := bstep (se 1 (by rfl) ⟨1723352, by rfl⟩ : syracuseStep 2297803 = 3446705) B3446705
theorem B626647 : Blo 626299 626647 := bstep (se 1 (by rfl) ⟨469985, by rfl⟩ : syracuseStep 626647 = 939971) B939971
theorem B626667 : Blo 626299 626667 := bstep (se 1 (by rfl) ⟨470000, by rfl⟩ : syracuseStep 626667 = 940001) B940001
theorem B1413107 : Blo 626299 1413107 := bstep (se 1 (by rfl) ⟨1059830, by rfl⟩ : syracuseStep 1413107 = 2119661) B2119661
theorem B626679 : Blo 626299 626679 := bstep (se 1 (by rfl) ⟨470009, by rfl⟩ : syracuseStep 626679 = 940019) B940019
theorem B626699 : Blo 626299 626699 := bstep (se 1 (by rfl) ⟨470024, by rfl⟩ : syracuseStep 626699 = 940049) B940049
theorem B2691089 : Blo 626299 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B626711 : Blo 626299 626711 := bstep (se 1 (by rfl) ⟨470033, by rfl⟩ : syracuseStep 626711 = 940067) B940067
theorem B1413143 : Blo 626299 1413143 := bstep (se 1 (by rfl) ⟨1059857, by rfl⟩ : syracuseStep 1413143 = 2119715) B2119715
theorem B626731 : Blo 626299 626731 := bstep (se 1 (by rfl) ⟨470048, by rfl⟩ : syracuseStep 626731 = 940097) B940097
theorem B4034605 : Blo 626299 4034605 := bstep (se 3 (by rfl) ⟨756488, by rfl⟩ : syracuseStep 4034605 = 1512977) B1512977
theorem B626743 : Blo 626299 626743 := bstep (se 1 (by rfl) ⟨470057, by rfl⟩ : syracuseStep 626743 = 940115) B940115
theorem B626763 : Blo 626299 626763 := bstep (se 1 (by rfl) ⟨470072, by rfl⟩ : syracuseStep 626763 = 940145) B940145
theorem B626775 : Blo 626299 626775 := bstep (se 1 (by rfl) ⟨470081, by rfl⟩ : syracuseStep 626775 = 940163) B940163
theorem B626795 : Blo 626299 626795 := bstep (se 1 (by rfl) ⟨470096, by rfl⟩ : syracuseStep 626795 = 940193) B940193
theorem B626807 : Blo 626299 626807 := bstep (se 1 (by rfl) ⟨470105, by rfl⟩ : syracuseStep 626807 = 940211) B940211
theorem B626827 : Blo 626299 626827 := bstep (se 1 (by rfl) ⟨470120, by rfl⟩ : syracuseStep 626827 = 940241) B940241
theorem B626839 : Blo 626299 626839 := bstep (se 1 (by rfl) ⟨470129, by rfl⟩ : syracuseStep 626839 = 940259) B940259
theorem B626859 : Blo 626299 626859 := bstep (se 1 (by rfl) ⟨470144, by rfl⟩ : syracuseStep 626859 = 940289) B940289
theorem B626871 : Blo 626299 626871 := bstep (se 1 (by rfl) ⟨470153, by rfl⟩ : syracuseStep 626871 = 940307) B940307
theorem B626891 : Blo 626299 626891 := bstep (se 1 (by rfl) ⟨470168, by rfl⟩ : syracuseStep 626891 = 940337) B940337
theorem B1413323 : Blo 626299 1413323 := bstep (se 1 (by rfl) ⟨1059992, by rfl⟩ : syracuseStep 1413323 = 2119985) B2119985
theorem B626903 : Blo 626299 626903 := bstep (se 1 (by rfl) ⟨470177, by rfl⟩ : syracuseStep 626903 = 940355) B940355
theorem B626923 : Blo 626299 626923 := bstep (se 1 (by rfl) ⟨470192, by rfl⟩ : syracuseStep 626923 = 940385) B940385
theorem B626935 : Blo 626299 626935 := bstep (se 1 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 626935 = 940403) B940403
theorem B1413377 : Blo 626299 1413377 := bstep (se 2 (by rfl) ⟨530016, by rfl⟩ : syracuseStep 1413377 = 1060033) B1060033
theorem B626955 : Blo 626299 626955 := bstep (se 1 (by rfl) ⟨470216, by rfl⟩ : syracuseStep 626955 = 940433) B940433
theorem B626967 : Blo 626299 626967 := bstep (se 1 (by rfl) ⟨470225, by rfl⟩ : syracuseStep 626967 = 940451) B940451
theorem B626987 : Blo 626299 626987 := bstep (se 1 (by rfl) ⟨470240, by rfl⟩ : syracuseStep 626987 = 940481) B940481
theorem B3576109 : Blo 626299 3576109 := bstep (se 3 (by rfl) ⟨670520, by rfl⟩ : syracuseStep 3576109 = 1341041) B1341041
theorem B626999 : Blo 626299 626999 := bstep (se 1 (by rfl) ⟨470249, by rfl⟩ : syracuseStep 626999 = 940499) B940499
theorem B627019 : Blo 626299 627019 := bstep (se 1 (by rfl) ⟨470264, by rfl⟩ : syracuseStep 627019 = 940529) B940529
theorem B627031 : Blo 626299 627031 := bstep (se 1 (by rfl) ⟨470273, by rfl⟩ : syracuseStep 627031 = 940547) B940547
theorem B4591973 : Blo 626299 4591973 := bstep (se 4 (by rfl) ⟨430497, by rfl⟩ : syracuseStep 4591973 = 860995) B860995
theorem B627051 : Blo 626299 627051 := bstep (se 1 (by rfl) ⟨470288, by rfl⟩ : syracuseStep 627051 = 940577) B940577
theorem B627063 : Blo 626299 627063 := bstep (se 1 (by rfl) ⟨470297, by rfl⟩ : syracuseStep 627063 = 940595) B940595
theorem B627083 : Blo 626299 627083 := bstep (se 1 (by rfl) ⟨470312, by rfl⟩ : syracuseStep 627083 = 940625) B940625
theorem B627095 : Blo 626299 627095 := bstep (se 1 (by rfl) ⟨470321, by rfl⟩ : syracuseStep 627095 = 940643) B940643
theorem B627115 : Blo 626299 627115 := bstep (se 1 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 627115 = 940673) B940673
theorem B627127 : Blo 626299 627127 := bstep (se 1 (by rfl) ⟨470345, by rfl⟩ : syracuseStep 627127 = 940691) B940691
theorem B627147 : Blo 626299 627147 := bstep (se 1 (by rfl) ⟨470360, by rfl⟩ : syracuseStep 627147 = 940721) B940721
theorem B627159 : Blo 626299 627159 := bstep (se 1 (by rfl) ⟨470369, by rfl⟩ : syracuseStep 627159 = 940739) B940739
theorem B1413593 : Blo 626299 1413593 := bstep (se 2 (by rfl) ⟨530097, by rfl⟩ : syracuseStep 1413593 = 1060195) B1060195
theorem B627179 : Blo 626299 627179 := bstep (se 1 (by rfl) ⟨470384, by rfl⟩ : syracuseStep 627179 = 940769) B940769
theorem B627191 : Blo 626299 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B627211 : Blo 626299 627211 := bstep (se 1 (by rfl) ⟨470408, by rfl⟩ : syracuseStep 627211 = 940817) B940817
theorem B627223 : Blo 626299 627223 := bstep (se 1 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 627223 = 940835) B940835
theorem B627243 : Blo 626299 627243 := bstep (se 1 (by rfl) ⟨470432, by rfl⟩ : syracuseStep 627243 = 940865) B940865
theorem B1413683 : Blo 626299 1413683 := bstep (se 1 (by rfl) ⟨1060262, by rfl⟩ : syracuseStep 1413683 = 2120525) B2120525
theorem B627255 : Blo 626299 627255 := bstep (se 1 (by rfl) ⟨470441, by rfl⟩ : syracuseStep 627255 = 940883) B940883
theorem B627275 : Blo 626299 627275 := bstep (se 1 (by rfl) ⟨470456, by rfl⟩ : syracuseStep 627275 = 940913) B940913
theorem B627287 : Blo 626299 627287 := bstep (se 1 (by rfl) ⟨470465, by rfl⟩ : syracuseStep 627287 = 940931) B940931
theorem B1413719 : Blo 626299 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B627307 : Blo 626299 627307 := bstep (se 1 (by rfl) ⟨470480, by rfl⟩ : syracuseStep 627307 = 940961) B940961
theorem B627319 : Blo 626299 627319 := bstep (se 1 (by rfl) ⟨470489, by rfl⟩ : syracuseStep 627319 = 940979) B940979
theorem B627339 : Blo 626299 627339 := bstep (se 1 (by rfl) ⟨470504, by rfl⟩ : syracuseStep 627339 = 941009) B941009
theorem B627351 : Blo 626299 627351 := bstep (se 1 (by rfl) ⟨470513, by rfl⟩ : syracuseStep 627351 = 941027) B941027
theorem B627371 : Blo 626299 627371 := bstep (se 1 (by rfl) ⟨470528, by rfl⟩ : syracuseStep 627371 = 941057) B941057
theorem B627383 : Blo 626299 627383 := bstep (se 1 (by rfl) ⟨470537, by rfl⟩ : syracuseStep 627383 = 941075) B941075
theorem B627403 : Blo 626299 627403 := bstep (se 1 (by rfl) ⟨470552, by rfl⟩ : syracuseStep 627403 = 941105) B941105
theorem B2691787 : Blo 626299 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B627415 : Blo 626299 627415 := bstep (se 1 (by rfl) ⟨470561, by rfl⟩ : syracuseStep 627415 = 941123) B941123
theorem B627435 : Blo 626299 627435 := bstep (se 1 (by rfl) ⟨470576, by rfl⟩ : syracuseStep 627435 = 941153) B941153
theorem B627447 : Blo 626299 627447 := bstep (se 1 (by rfl) ⟨470585, by rfl⟩ : syracuseStep 627447 = 941171) B941171
theorem B627467 : Blo 626299 627467 := bstep (se 1 (by rfl) ⟨470600, by rfl⟩ : syracuseStep 627467 = 941201) B941201
theorem B1413899 : Blo 626299 1413899 := bstep (se 1 (by rfl) ⟨1060424, by rfl⟩ : syracuseStep 1413899 = 2120849) B2120849
theorem B627479 : Blo 626299 627479 := bstep (se 1 (by rfl) ⟨470609, by rfl⟩ : syracuseStep 627479 = 941219) B941219
theorem B627499 : Blo 626299 627499 := bstep (se 1 (by rfl) ⟨470624, by rfl⟩ : syracuseStep 627499 = 941249) B941249
theorem B627511 : Blo 626299 627511 := bstep (se 1 (by rfl) ⟨470633, by rfl⟩ : syracuseStep 627511 = 941267) B941267
theorem B1413953 : Blo 626299 1413953 := bstep (se 2 (by rfl) ⟨530232, by rfl⟩ : syracuseStep 1413953 = 1060465) B1060465
theorem B627531 : Blo 626299 627531 := bstep (se 1 (by rfl) ⟨470648, by rfl⟩ : syracuseStep 627531 = 941297) B941297
theorem B627543 : Blo 626299 627543 := bstep (se 1 (by rfl) ⟨470657, by rfl⟩ : syracuseStep 627543 = 941315) B941315
theorem B627563 : Blo 626299 627563 := bstep (se 1 (by rfl) ⟨470672, by rfl⟩ : syracuseStep 627563 = 941345) B941345
theorem B627575 : Blo 626299 627575 := bstep (se 1 (by rfl) ⟨470681, by rfl⟩ : syracuseStep 627575 = 941363) B941363
theorem B627595 : Blo 626299 627595 := bstep (se 1 (by rfl) ⟨470696, by rfl⟩ : syracuseStep 627595 = 941393) B941393
theorem B627607 : Blo 626299 627607 := bstep (se 1 (by rfl) ⟨470705, by rfl⟩ : syracuseStep 627607 = 941411) B941411
theorem B4526999 : Blo 626299 4526999 := bstep (se 1 (by rfl) ⟨3395249, by rfl⟩ : syracuseStep 4526999 = 6790499) B6790499
theorem B627627 : Blo 626299 627627 := bstep (se 1 (by rfl) ⟨470720, by rfl⟩ : syracuseStep 627627 = 941441) B941441
theorem B627639 : Blo 626299 627639 := bstep (se 1 (by rfl) ⟨470729, by rfl⟩ : syracuseStep 627639 = 941459) B941459
theorem B627659 : Blo 626299 627659 := bstep (se 1 (by rfl) ⟨470744, by rfl⟩ : syracuseStep 627659 = 941489) B941489
theorem B627671 : Blo 626299 627671 := bstep (se 1 (by rfl) ⟨470753, by rfl⟩ : syracuseStep 627671 = 941507) B941507
theorem B16126937 : Blo 626299 16126937 := bstep (se 2 (by rfl) ⟨6047601, by rfl⟩ : syracuseStep 16126937 = 12095203) B12095203
theorem B2692061 : Blo 626299 2692061 := bstep (se 3 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 2692061 = 1009523) B1009523
theorem B627691 : Blo 626299 627691 := bstep (se 1 (by rfl) ⟨470768, by rfl⟩ : syracuseStep 627691 = 941537) B941537
theorem B627703 : Blo 626299 627703 := bstep (se 1 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 627703 = 941555) B941555
theorem B627723 : Blo 626299 627723 := bstep (se 1 (by rfl) ⟨470792, by rfl⟩ : syracuseStep 627723 = 941585) B941585
theorem B627735 : Blo 626299 627735 := bstep (se 1 (by rfl) ⟨470801, by rfl⟩ : syracuseStep 627735 = 941603) B941603
theorem B1414169 : Blo 626299 1414169 := bstep (se 2 (by rfl) ⟨530313, by rfl⟩ : syracuseStep 1414169 = 1060627) B1060627
theorem B627755 : Blo 626299 627755 := bstep (se 1 (by rfl) ⟨470816, by rfl⟩ : syracuseStep 627755 = 941633) B941633
theorem B627767 : Blo 626299 627767 := bstep (se 1 (by rfl) ⟨470825, by rfl⟩ : syracuseStep 627767 = 941651) B941651
theorem B627787 : Blo 626299 627787 := bstep (se 1 (by rfl) ⟨470840, by rfl⟩ : syracuseStep 627787 = 941681) B941681
theorem B627799 : Blo 626299 627799 := bstep (se 1 (by rfl) ⟨470849, by rfl⟩ : syracuseStep 627799 = 941699) B941699
theorem B627819 : Blo 626299 627819 := bstep (se 1 (by rfl) ⟨470864, by rfl⟩ : syracuseStep 627819 = 941729) B941729
theorem B1414259 : Blo 626299 1414259 := bstep (se 1 (by rfl) ⟨1060694, by rfl⟩ : syracuseStep 1414259 = 2121389) B2121389
theorem B627831 : Blo 626299 627831 := bstep (se 1 (by rfl) ⟨470873, by rfl⟩ : syracuseStep 627831 = 941747) B941747
theorem B627851 : Blo 626299 627851 := bstep (se 1 (by rfl) ⟨470888, by rfl⟩ : syracuseStep 627851 = 941777) B941777
theorem B627863 : Blo 626299 627863 := bstep (se 1 (by rfl) ⟨470897, by rfl⟩ : syracuseStep 627863 = 941795) B941795
theorem B1414295 : Blo 626299 1414295 := bstep (se 1 (by rfl) ⟨1060721, by rfl⟩ : syracuseStep 1414295 = 2121443) B2121443
theorem B627883 : Blo 626299 627883 := bstep (se 1 (by rfl) ⟨470912, by rfl⟩ : syracuseStep 627883 = 941825) B941825
theorem B627895 : Blo 626299 627895 := bstep (se 1 (by rfl) ⟨470921, by rfl⟩ : syracuseStep 627895 = 941843) B941843
theorem B627915 : Blo 626299 627915 := bstep (se 1 (by rfl) ⟨470936, by rfl⟩ : syracuseStep 627915 = 941873) B941873
theorem B627927 : Blo 626299 627927 := bstep (se 1 (by rfl) ⟨470945, by rfl⟩ : syracuseStep 627927 = 941891) B941891
theorem B627947 : Blo 626299 627947 := bstep (se 1 (by rfl) ⟨470960, by rfl⟩ : syracuseStep 627947 = 941921) B941921
theorem B627959 : Blo 626299 627959 := bstep (se 1 (by rfl) ⟨470969, by rfl⟩ : syracuseStep 627959 = 941939) B941939
theorem B627979 : Blo 626299 627979 := bstep (se 1 (by rfl) ⟨470984, by rfl⟩ : syracuseStep 627979 = 941969) B941969
theorem B627991 : Blo 626299 627991 := bstep (se 1 (by rfl) ⟨470993, by rfl⟩ : syracuseStep 627991 = 941987) B941987
theorem B628011 : Blo 626299 628011 := bstep (se 1 (by rfl) ⟨471008, by rfl⟩ : syracuseStep 628011 = 942017) B942017
theorem B628023 : Blo 626299 628023 := bstep (se 1 (by rfl) ⟨471017, by rfl⟩ : syracuseStep 628023 = 942035) B942035
theorem B628043 : Blo 626299 628043 := bstep (se 1 (by rfl) ⟨471032, by rfl⟩ : syracuseStep 628043 = 942065) B942065
theorem B1414475 : Blo 626299 1414475 := bstep (se 1 (by rfl) ⟨1060856, by rfl⟩ : syracuseStep 1414475 = 2121713) B2121713
theorem B3183947 : Blo 626299 3183947 := bstep (se 1 (by rfl) ⟨2387960, by rfl⟩ : syracuseStep 3183947 = 4775921) B4775921
theorem B628055 : Blo 626299 628055 := bstep (se 1 (by rfl) ⟨471041, by rfl⟩ : syracuseStep 628055 = 942083) B942083
theorem B628075 : Blo 626299 628075 := bstep (se 1 (by rfl) ⟨471056, by rfl⟩ : syracuseStep 628075 = 942113) B942113
theorem B628087 : Blo 626299 628087 := bstep (se 1 (by rfl) ⟨471065, by rfl⟩ : syracuseStep 628087 = 942131) B942131
theorem B1414529 : Blo 626299 1414529 := bstep (se 2 (by rfl) ⟨530448, by rfl⟩ : syracuseStep 1414529 = 1060897) B1060897
theorem B628107 : Blo 626299 628107 := bstep (se 1 (by rfl) ⟨471080, by rfl⟩ : syracuseStep 628107 = 942161) B942161
theorem B628119 : Blo 626299 628119 := bstep (se 1 (by rfl) ⟨471089, by rfl⟩ : syracuseStep 628119 = 942179) B942179
theorem B628139 : Blo 626299 628139 := bstep (se 1 (by rfl) ⟨471104, by rfl⟩ : syracuseStep 628139 = 942209) B942209
theorem B628151 : Blo 626299 628151 := bstep (se 1 (by rfl) ⟨471113, by rfl⟩ : syracuseStep 628151 = 942227) B942227
theorem B628171 : Blo 626299 628171 := bstep (se 1 (by rfl) ⟨471128, by rfl⟩ : syracuseStep 628171 = 942257) B942257
theorem B628183 : Blo 626299 628183 := bstep (se 1 (by rfl) ⟨471137, by rfl⟩ : syracuseStep 628183 = 942275) B942275
theorem B628203 : Blo 626299 628203 := bstep (se 1 (by rfl) ⟨471152, by rfl⟩ : syracuseStep 628203 = 942305) B942305
theorem B628215 : Blo 626299 628215 := bstep (se 1 (by rfl) ⟨471161, by rfl⟩ : syracuseStep 628215 = 942323) B942323
theorem B628235 : Blo 626299 628235 := bstep (se 1 (by rfl) ⟨471176, by rfl⟩ : syracuseStep 628235 = 942353) B942353
theorem B628247 : Blo 626299 628247 := bstep (se 1 (by rfl) ⟨471185, by rfl⟩ : syracuseStep 628247 = 942371) B942371
theorem B628267 : Blo 626299 628267 := bstep (se 1 (by rfl) ⟨471200, by rfl⟩ : syracuseStep 628267 = 942401) B942401
theorem B628279 : Blo 626299 628279 := bstep (se 1 (by rfl) ⟨471209, by rfl⟩ : syracuseStep 628279 = 942419) B942419
theorem B628299 : Blo 626299 628299 := bstep (se 1 (by rfl) ⟨471224, by rfl⟩ : syracuseStep 628299 = 942449) B942449
theorem B628311 : Blo 626299 628311 := bstep (se 1 (by rfl) ⟨471233, by rfl⟩ : syracuseStep 628311 = 942467) B942467
theorem B1414745 : Blo 626299 1414745 := bstep (se 2 (by rfl) ⟨530529, by rfl⟩ : syracuseStep 1414745 = 1061059) B1061059
theorem B628331 : Blo 626299 628331 := bstep (se 1 (by rfl) ⟨471248, by rfl⟩ : syracuseStep 628331 = 942497) B942497
theorem B628343 : Blo 626299 628343 := bstep (se 1 (by rfl) ⟨471257, by rfl⟩ : syracuseStep 628343 = 942515) B942515
theorem B628363 : Blo 626299 628363 := bstep (se 1 (by rfl) ⟨471272, by rfl⟩ : syracuseStep 628363 = 942545) B942545
theorem B628375 : Blo 626299 628375 := bstep (se 1 (by rfl) ⟨471281, by rfl⟩ : syracuseStep 628375 = 942563) B942563
theorem B628395 : Blo 626299 628395 := bstep (se 1 (by rfl) ⟨471296, by rfl⟩ : syracuseStep 628395 = 942593) B942593
theorem B1414835 : Blo 626299 1414835 := bstep (se 1 (by rfl) ⟨1061126, by rfl⟩ : syracuseStep 1414835 = 2122253) B2122253
theorem B628407 : Blo 626299 628407 := bstep (se 1 (by rfl) ⟨471305, by rfl⟩ : syracuseStep 628407 = 942611) B942611
theorem B628427 : Blo 626299 628427 := bstep (se 1 (by rfl) ⟨471320, by rfl⟩ : syracuseStep 628427 = 942641) B942641
theorem B628439 : Blo 626299 628439 := bstep (se 1 (by rfl) ⟨471329, by rfl⟩ : syracuseStep 628439 = 942659) B942659
theorem B1414871 : Blo 626299 1414871 := bstep (se 1 (by rfl) ⟨1061153, by rfl⟩ : syracuseStep 1414871 = 2122307) B2122307
theorem B628459 : Blo 626299 628459 := bstep (se 1 (by rfl) ⟨471344, by rfl⟩ : syracuseStep 628459 = 942689) B942689
theorem B628471 : Blo 626299 628471 := bstep (se 1 (by rfl) ⟨471353, by rfl⟩ : syracuseStep 628471 = 942707) B942707
theorem B628491 : Blo 626299 628491 := bstep (se 1 (by rfl) ⟨471368, by rfl⟩ : syracuseStep 628491 = 942737) B942737
theorem B628503 : Blo 626299 628503 := bstep (se 1 (by rfl) ⟨471377, by rfl⟩ : syracuseStep 628503 = 942755) B942755
theorem B628523 : Blo 626299 628523 := bstep (se 1 (by rfl) ⟨471392, by rfl⟩ : syracuseStep 628523 = 942785) B942785
theorem B628535 : Blo 626299 628535 := bstep (se 1 (by rfl) ⟨471401, by rfl⟩ : syracuseStep 628535 = 942803) B942803
theorem B628555 : Blo 626299 628555 := bstep (se 1 (by rfl) ⟨471416, by rfl⟩ : syracuseStep 628555 = 942833) B942833
theorem B628567 : Blo 626299 628567 := bstep (se 1 (by rfl) ⟨471425, by rfl⟩ : syracuseStep 628567 = 942851) B942851
theorem B628587 : Blo 626299 628587 := bstep (se 1 (by rfl) ⟨471440, by rfl⟩ : syracuseStep 628587 = 942881) B942881
theorem B628599 : Blo 626299 628599 := bstep (se 1 (by rfl) ⟨471449, by rfl⟩ : syracuseStep 628599 = 942899) B942899
theorem B628619 : Blo 626299 628619 := bstep (se 1 (by rfl) ⟨471464, by rfl⟩ : syracuseStep 628619 = 942929) B942929
theorem B1415051 : Blo 626299 1415051 := bstep (se 1 (by rfl) ⟨1061288, by rfl⟩ : syracuseStep 1415051 = 2122577) B2122577
theorem B628631 : Blo 626299 628631 := bstep (se 1 (by rfl) ⟨471473, by rfl⟩ : syracuseStep 628631 = 942947) B942947
theorem B628651 : Blo 626299 628651 := bstep (se 1 (by rfl) ⟨471488, by rfl⟩ : syracuseStep 628651 = 942977) B942977
theorem B628663 : Blo 626299 628663 := bstep (se 1 (by rfl) ⟨471497, by rfl⟩ : syracuseStep 628663 = 942995) B942995
theorem B1415105 : Blo 626299 1415105 := bstep (se 2 (by rfl) ⟨530664, by rfl⟩ : syracuseStep 1415105 = 1061329) B1061329
theorem B628683 : Blo 626299 628683 := bstep (se 1 (by rfl) ⟨471512, by rfl⟩ : syracuseStep 628683 = 943025) B943025
theorem B4757453 : Blo 626299 4757453 := bstep (se 3 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 4757453 = 1784045) B1784045
theorem B628695 : Blo 626299 628695 := bstep (se 1 (by rfl) ⟨471521, by rfl⟩ : syracuseStep 628695 = 943043) B943043
theorem B628715 : Blo 626299 628715 := bstep (se 1 (by rfl) ⟨471536, by rfl⟩ : syracuseStep 628715 = 943073) B943073
theorem B628727 : Blo 626299 628727 := bstep (se 1 (by rfl) ⟨471545, by rfl⟩ : syracuseStep 628727 = 943091) B943091
theorem B628747 : Blo 626299 628747 := bstep (se 1 (by rfl) ⟨471560, by rfl⟩ : syracuseStep 628747 = 943121) B943121
theorem B628759 : Blo 626299 628759 := bstep (se 1 (by rfl) ⟨471569, by rfl⟩ : syracuseStep 628759 = 943139) B943139
theorem B628779 : Blo 626299 628779 := bstep (se 1 (by rfl) ⟨471584, by rfl⟩ : syracuseStep 628779 = 943169) B943169
theorem B628791 : Blo 626299 628791 := bstep (se 1 (by rfl) ⟨471593, by rfl⟩ : syracuseStep 628791 = 943187) B943187
theorem B628811 : Blo 626299 628811 := bstep (se 1 (by rfl) ⟨471608, by rfl⟩ : syracuseStep 628811 = 943217) B943217
theorem B628823 : Blo 626299 628823 := bstep (se 1 (by rfl) ⟨471617, by rfl⟩ : syracuseStep 628823 = 943235) B943235
theorem B628843 : Blo 626299 628843 := bstep (se 1 (by rfl) ⟨471632, by rfl⟩ : syracuseStep 628843 = 943265) B943265
theorem B628855 : Blo 626299 628855 := bstep (se 1 (by rfl) ⟨471641, by rfl⟩ : syracuseStep 628855 = 943283) B943283
theorem B628875 : Blo 626299 628875 := bstep (se 1 (by rfl) ⟨471656, by rfl⟩ : syracuseStep 628875 = 943313) B943313
theorem B628887 : Blo 626299 628887 := bstep (se 1 (by rfl) ⟨471665, by rfl⟩ : syracuseStep 628887 = 943331) B943331
theorem B1415321 : Blo 626299 1415321 := bstep (se 2 (by rfl) ⟨530745, by rfl⟩ : syracuseStep 1415321 = 1061491) B1061491
theorem B628907 : Blo 626299 628907 := bstep (se 1 (by rfl) ⟨471680, by rfl⟩ : syracuseStep 628907 = 943361) B943361
theorem B628919 : Blo 626299 628919 := bstep (se 1 (by rfl) ⟨471689, by rfl⟩ : syracuseStep 628919 = 943379) B943379
theorem B628939 : Blo 626299 628939 := bstep (se 1 (by rfl) ⟨471704, by rfl⟩ : syracuseStep 628939 = 943409) B943409
theorem B628951 : Blo 626299 628951 := bstep (se 1 (by rfl) ⟨471713, by rfl⟩ : syracuseStep 628951 = 943427) B943427
theorem B628971 : Blo 626299 628971 := bstep (se 1 (by rfl) ⟨471728, by rfl⟩ : syracuseStep 628971 = 943457) B943457
theorem B1415411 : Blo 626299 1415411 := bstep (se 1 (by rfl) ⟨1061558, by rfl⟩ : syracuseStep 1415411 = 2123117) B2123117
theorem B628983 : Blo 626299 628983 := bstep (se 1 (by rfl) ⟨471737, by rfl⟩ : syracuseStep 628983 = 943475) B943475
theorem B629003 : Blo 626299 629003 := bstep (se 1 (by rfl) ⟨471752, by rfl⟩ : syracuseStep 629003 = 943505) B943505
theorem B629015 : Blo 626299 629015 := bstep (se 1 (by rfl) ⟨471761, by rfl⟩ : syracuseStep 629015 = 943523) B943523
theorem B1415447 : Blo 626299 1415447 := bstep (se 1 (by rfl) ⟨1061585, by rfl⟩ : syracuseStep 1415447 = 2123171) B2123171
theorem B629035 : Blo 626299 629035 := bstep (se 1 (by rfl) ⟨471776, by rfl⟩ : syracuseStep 629035 = 943553) B943553
theorem B18061613 : Blo 626299 18061613 := bstep (se 3 (by rfl) ⟨3386552, by rfl⟩ : syracuseStep 18061613 = 6773105) B6773105
theorem B629047 : Blo 626299 629047 := bstep (se 1 (by rfl) ⟨471785, by rfl⟩ : syracuseStep 629047 = 943571) B943571
theorem B629067 : Blo 626299 629067 := bstep (se 1 (by rfl) ⟨471800, by rfl⟩ : syracuseStep 629067 = 943601) B943601
theorem B792919 : Blo 626299 792919 := bstep (se 1 (by rfl) ⟨594689, by rfl⟩ : syracuseStep 792919 = 1189379) B1189379
theorem B629079 : Blo 626299 629079 := bstep (se 1 (by rfl) ⟨471809, by rfl⟩ : syracuseStep 629079 = 943619) B943619
theorem B629099 : Blo 626299 629099 := bstep (se 1 (by rfl) ⟨471824, by rfl⟩ : syracuseStep 629099 = 943649) B943649
theorem B629111 : Blo 626299 629111 := bstep (se 1 (by rfl) ⟨471833, by rfl⟩ : syracuseStep 629111 = 943667) B943667
theorem B629131 : Blo 626299 629131 := bstep (se 1 (by rfl) ⟨471848, by rfl⟩ : syracuseStep 629131 = 943697) B943697
theorem B629143 : Blo 626299 629143 := bstep (se 1 (by rfl) ⟨471857, by rfl⟩ : syracuseStep 629143 = 943715) B943715
theorem B629163 : Blo 626299 629163 := bstep (se 1 (by rfl) ⟨471872, by rfl⟩ : syracuseStep 629163 = 943745) B943745
theorem B4757939 : Blo 626299 4757939 := bstep (se 1 (by rfl) ⟨3568454, by rfl⟩ : syracuseStep 4757939 = 7136909) B7136909
theorem B629175 : Blo 626299 629175 := bstep (se 1 (by rfl) ⟨471881, by rfl⟩ : syracuseStep 629175 = 943763) B943763
theorem B1415627 : Blo 626299 1415627 := bstep (se 1 (by rfl) ⟨1061720, by rfl⟩ : syracuseStep 1415627 = 2123441) B2123441
theorem B629195 : Blo 626299 629195 := bstep (se 1 (by rfl) ⟨471896, by rfl⟩ : syracuseStep 629195 = 943793) B943793
theorem B629207 : Blo 626299 629207 := bstep (se 1 (by rfl) ⟨471905, by rfl⟩ : syracuseStep 629207 = 943811) B943811
theorem B629227 : Blo 626299 629227 := bstep (se 1 (by rfl) ⟨471920, by rfl⟩ : syracuseStep 629227 = 943841) B943841
theorem B629239 : Blo 626299 629239 := bstep (se 1 (by rfl) ⟨471929, by rfl⟩ : syracuseStep 629239 = 943859) B943859
theorem B1415681 : Blo 626299 1415681 := bstep (se 2 (by rfl) ⟨530880, by rfl⟩ : syracuseStep 1415681 = 1061761) B1061761
theorem B629259 : Blo 626299 629259 := bstep (se 1 (by rfl) ⟨471944, by rfl⟩ : syracuseStep 629259 = 943889) B943889
theorem B629271 : Blo 626299 629271 := bstep (se 1 (by rfl) ⟨471953, by rfl⟩ : syracuseStep 629271 = 943907) B943907
theorem B629291 : Blo 626299 629291 := bstep (se 1 (by rfl) ⟨471968, by rfl⟩ : syracuseStep 629291 = 943937) B943937
theorem B629303 : Blo 626299 629303 := bstep (se 1 (by rfl) ⟨471977, by rfl⟩ : syracuseStep 629303 = 943955) B943955
theorem B629323 : Blo 626299 629323 := bstep (se 1 (by rfl) ⟨471992, by rfl⟩ : syracuseStep 629323 = 943985) B943985
theorem B629335 : Blo 626299 629335 := bstep (se 1 (by rfl) ⟨472001, by rfl⟩ : syracuseStep 629335 = 944003) B944003
theorem B629355 : Blo 626299 629355 := bstep (se 1 (by rfl) ⟨472016, by rfl⟩ : syracuseStep 629355 = 944033) B944033
theorem B629367 : Blo 626299 629367 := bstep (se 1 (by rfl) ⟨472025, by rfl⟩ : syracuseStep 629367 = 944051) B944051
theorem B629387 : Blo 626299 629387 := bstep (se 1 (by rfl) ⟨472040, by rfl⟩ : syracuseStep 629387 = 944081) B944081
theorem B629399 : Blo 626299 629399 := bstep (se 1 (by rfl) ⟨472049, by rfl⟩ : syracuseStep 629399 = 944099) B944099
theorem B629419 : Blo 626299 629419 := bstep (se 1 (by rfl) ⟨472064, by rfl⟩ : syracuseStep 629419 = 944129) B944129
theorem B629431 : Blo 626299 629431 := bstep (se 1 (by rfl) ⟨472073, by rfl⟩ : syracuseStep 629431 = 944147) B944147
theorem B629451 : Blo 626299 629451 := bstep (se 1 (by rfl) ⟨472088, by rfl⟩ : syracuseStep 629451 = 944177) B944177
theorem B629463 : Blo 626299 629463 := bstep (se 1 (by rfl) ⟨472097, by rfl⟩ : syracuseStep 629463 = 944195) B944195
theorem B1415897 : Blo 626299 1415897 := bstep (se 2 (by rfl) ⟨530961, by rfl⟩ : syracuseStep 1415897 = 1061923) B1061923
theorem B629483 : Blo 626299 629483 := bstep (se 1 (by rfl) ⟨472112, by rfl⟩ : syracuseStep 629483 = 944225) B944225
theorem B629495 : Blo 626299 629495 := bstep (se 1 (by rfl) ⟨472121, by rfl⟩ : syracuseStep 629495 = 944243) B944243
theorem B629515 : Blo 626299 629515 := bstep (se 1 (by rfl) ⟨472136, by rfl⟩ : syracuseStep 629515 = 944273) B944273
theorem B629527 : Blo 626299 629527 := bstep (se 1 (by rfl) ⟨472145, by rfl⟩ : syracuseStep 629527 = 944291) B944291
theorem B629547 : Blo 626299 629547 := bstep (se 1 (by rfl) ⟨472160, by rfl⟩ : syracuseStep 629547 = 944321) B944321
theorem B1415987 : Blo 626299 1415987 := bstep (se 1 (by rfl) ⟨1061990, by rfl⟩ : syracuseStep 1415987 = 2123981) B2123981
theorem B629559 : Blo 626299 629559 := bstep (se 1 (by rfl) ⟨472169, by rfl⟩ : syracuseStep 629559 = 944339) B944339
theorem B629579 : Blo 626299 629579 := bstep (se 1 (by rfl) ⟨472184, by rfl⟩ : syracuseStep 629579 = 944369) B944369
theorem B1416023 : Blo 626299 1416023 := bstep (se 1 (by rfl) ⟨1062017, by rfl⟩ : syracuseStep 1416023 = 2124035) B2124035
theorem B629591 : Blo 626299 629591 := bstep (se 1 (by rfl) ⟨472193, by rfl⟩ : syracuseStep 629591 = 944387) B944387
theorem B629611 : Blo 626299 629611 := bstep (se 1 (by rfl) ⟨472208, by rfl⟩ : syracuseStep 629611 = 944417) B944417
theorem B629623 : Blo 626299 629623 := bstep (se 1 (by rfl) ⟨472217, by rfl⟩ : syracuseStep 629623 = 944435) B944435
theorem B629643 : Blo 626299 629643 := bstep (se 1 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 629643 = 944465) B944465
theorem B629655 : Blo 626299 629655 := bstep (se 1 (by rfl) ⟨472241, by rfl⟩ : syracuseStep 629655 = 944483) B944483
theorem B629675 : Blo 626299 629675 := bstep (se 1 (by rfl) ⟨472256, by rfl⟩ : syracuseStep 629675 = 944513) B944513
theorem B629687 : Blo 626299 629687 := bstep (se 1 (by rfl) ⟨472265, by rfl⟩ : syracuseStep 629687 = 944531) B944531
theorem B629707 : Blo 626299 629707 := bstep (se 1 (by rfl) ⟨472280, by rfl⟩ : syracuseStep 629707 = 944561) B944561
theorem B629719 : Blo 626299 629719 := bstep (se 1 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 629719 = 944579) B944579
theorem B629739 : Blo 626299 629739 := bstep (se 1 (by rfl) ⟨472304, by rfl⟩ : syracuseStep 629739 = 944609) B944609
theorem B629751 : Blo 626299 629751 := bstep (se 1 (by rfl) ⟨472313, by rfl⟩ : syracuseStep 629751 = 944627) B944627
theorem B1416203 : Blo 626299 1416203 := bstep (se 1 (by rfl) ⟨1062152, by rfl⟩ : syracuseStep 1416203 = 2124305) B2124305
theorem B629771 : Blo 626299 629771 := bstep (se 1 (by rfl) ⟨472328, by rfl⟩ : syracuseStep 629771 = 944657) B944657
theorem B629783 : Blo 626299 629783 := bstep (se 1 (by rfl) ⟨472337, by rfl⟩ : syracuseStep 629783 = 944675) B944675
theorem B629803 : Blo 626299 629803 := bstep (se 1 (by rfl) ⟨472352, by rfl⟩ : syracuseStep 629803 = 944705) B944705
theorem B629815 : Blo 626299 629815 := bstep (se 1 (by rfl) ⟨472361, by rfl⟩ : syracuseStep 629815 = 944723) B944723
theorem B3185729 : Blo 626299 3185729 := bstep (se 2 (by rfl) ⟨1194648, by rfl⟩ : syracuseStep 3185729 = 2389297) B2389297
theorem B1416257 : Blo 626299 1416257 := bstep (se 2 (by rfl) ⟨531096, by rfl⟩ : syracuseStep 1416257 = 1062193) B1062193
theorem B629835 : Blo 626299 629835 := bstep (se 1 (by rfl) ⟨472376, by rfl⟩ : syracuseStep 629835 = 944753) B944753
theorem B629847 : Blo 626299 629847 := bstep (se 1 (by rfl) ⟨472385, by rfl⟩ : syracuseStep 629847 = 944771) B944771
theorem B629867 : Blo 626299 629867 := bstep (se 1 (by rfl) ⟨472400, by rfl⟩ : syracuseStep 629867 = 944801) B944801
theorem B629879 : Blo 626299 629879 := bstep (se 1 (by rfl) ⟨472409, by rfl⟩ : syracuseStep 629879 = 944819) B944819
theorem B793739 : Blo 626299 793739 := bstep (se 1 (by rfl) ⟨595304, by rfl⟩ : syracuseStep 793739 = 1190609) B1190609
theorem B629899 : Blo 626299 629899 := bstep (se 1 (by rfl) ⟨472424, by rfl⟩ : syracuseStep 629899 = 944849) B944849
theorem B629911 : Blo 626299 629911 := bstep (se 1 (by rfl) ⟨472433, by rfl⟩ : syracuseStep 629911 = 944867) B944867
theorem B629931 : Blo 626299 629931 := bstep (se 1 (by rfl) ⟨472448, by rfl⟩ : syracuseStep 629931 = 944897) B944897
theorem B629943 : Blo 626299 629943 := bstep (se 1 (by rfl) ⟨472457, by rfl⟩ : syracuseStep 629943 = 944915) B944915
theorem B629963 : Blo 626299 629963 := bstep (se 1 (by rfl) ⟨472472, by rfl⟩ : syracuseStep 629963 = 944945) B944945
theorem B629975 : Blo 626299 629975 := bstep (se 1 (by rfl) ⟨472481, by rfl⟩ : syracuseStep 629975 = 944963) B944963
theorem B629995 : Blo 626299 629995 := bstep (se 1 (by rfl) ⟨472496, by rfl⟩ : syracuseStep 629995 = 944993) B944993
theorem B630007 : Blo 626299 630007 := bstep (se 1 (by rfl) ⟨472505, by rfl⟩ : syracuseStep 630007 = 945011) B945011
theorem B892171 : Blo 626299 892171 := bstep (se 1 (by rfl) ⟨669128, by rfl⟩ : syracuseStep 892171 = 1338257) B1338257
theorem B630027 : Blo 626299 630027 := bstep (se 1 (by rfl) ⟨472520, by rfl⟩ : syracuseStep 630027 = 945041) B945041
theorem B630039 : Blo 626299 630039 := bstep (se 1 (by rfl) ⟨472529, by rfl⟩ : syracuseStep 630039 = 945059) B945059
theorem B1416473 : Blo 626299 1416473 := bstep (se 2 (by rfl) ⟨531177, by rfl⟩ : syracuseStep 1416473 = 1062355) B1062355
theorem B630059 : Blo 626299 630059 := bstep (se 1 (by rfl) ⟨472544, by rfl⟩ : syracuseStep 630059 = 945089) B945089
theorem B630071 : Blo 626299 630071 := bstep (se 1 (by rfl) ⟨472553, by rfl⟩ : syracuseStep 630071 = 945107) B945107
theorem B630091 : Blo 626299 630091 := bstep (se 1 (by rfl) ⟨472568, by rfl⟩ : syracuseStep 630091 = 945137) B945137
theorem B630103 : Blo 626299 630103 := bstep (se 1 (by rfl) ⟨472577, by rfl⟩ : syracuseStep 630103 = 945155) B945155
theorem B630123 : Blo 626299 630123 := bstep (se 1 (by rfl) ⟨472592, by rfl⟩ : syracuseStep 630123 = 945185) B945185
theorem B1416563 : Blo 626299 1416563 := bstep (se 1 (by rfl) ⟨1062422, by rfl⟩ : syracuseStep 1416563 = 2124845) B2124845
theorem B630135 : Blo 626299 630135 := bstep (se 1 (by rfl) ⟨472601, by rfl⟩ : syracuseStep 630135 = 945203) B945203
theorem B630155 : Blo 626299 630155 := bstep (se 1 (by rfl) ⟨472616, by rfl⟩ : syracuseStep 630155 = 945233) B945233
theorem B1416599 : Blo 626299 1416599 := bstep (se 1 (by rfl) ⟨1062449, by rfl⟩ : syracuseStep 1416599 = 2124899) B2124899
theorem B630167 : Blo 626299 630167 := bstep (se 1 (by rfl) ⟨472625, by rfl⟩ : syracuseStep 630167 = 945251) B945251
theorem B630187 : Blo 626299 630187 := bstep (se 1 (by rfl) ⟨472640, by rfl⟩ : syracuseStep 630187 = 945281) B945281
theorem B630199 : Blo 626299 630199 := bstep (se 1 (by rfl) ⟨472649, by rfl⟩ : syracuseStep 630199 = 945299) B945299
theorem B630219 : Blo 626299 630219 := bstep (se 1 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 630219 = 945329) B945329
theorem B630231 : Blo 626299 630231 := bstep (se 1 (by rfl) ⟨472673, by rfl⟩ : syracuseStep 630231 = 945347) B945347
theorem B630251 : Blo 626299 630251 := bstep (se 1 (by rfl) ⟨472688, by rfl⟩ : syracuseStep 630251 = 945377) B945377
theorem B630263 : Blo 626299 630263 := bstep (se 1 (by rfl) ⟨472697, by rfl⟩ : syracuseStep 630263 = 945395) B945395
theorem B630283 : Blo 626299 630283 := bstep (se 1 (by rfl) ⟨472712, by rfl⟩ : syracuseStep 630283 = 945425) B945425
theorem B630295 : Blo 626299 630295 := bstep (se 1 (by rfl) ⟨472721, by rfl⟩ : syracuseStep 630295 = 945443) B945443
theorem B1416779 : Blo 626299 1416779 := bstep (se 1 (by rfl) ⟨1062584, by rfl⟩ : syracuseStep 1416779 = 2125169) B2125169
theorem B1416833 : Blo 626299 1416833 := bstep (se 2 (by rfl) ⟨531312, by rfl⟩ : syracuseStep 1416833 = 1062625) B1062625
theorem B1449751 : Blo 626299 1449751 := bstep (se 1 (by rfl) ⟨1087313, by rfl⟩ : syracuseStep 1449751 = 2174627) B2174627
theorem B794443 : Blo 626299 794443 := bstep (se 1 (by rfl) ⟨595832, by rfl⟩ : syracuseStep 794443 = 1191665) B1191665
theorem B2727755 : Blo 626299 2727755 := bstep (se 1 (by rfl) ⟨2045816, by rfl⟩ : syracuseStep 2727755 = 4091633) B4091633
theorem B1417049 : Blo 626299 1417049 := bstep (se 2 (by rfl) ⟨531393, by rfl⟩ : syracuseStep 1417049 = 1062787) B1062787
theorem B4759397 : Blo 626299 4759397 := bstep (se 4 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 4759397 = 892387) B892387
theorem B1417139 : Blo 626299 1417139 := bstep (se 1 (by rfl) ⟨1062854, by rfl⟩ : syracuseStep 1417139 = 2125709) B2125709
theorem B1417175 : Blo 626299 1417175 := bstep (se 1 (by rfl) ⟨1062881, by rfl⟩ : syracuseStep 1417175 = 2125763) B2125763
theorem B2269235 : Blo 626299 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B794711 : Blo 626299 794711 := bstep (se 1 (by rfl) ⟨596033, by rfl⟩ : syracuseStep 794711 = 1192067) B1192067
theorem B1417355 : Blo 626299 1417355 := bstep (se 1 (by rfl) ⟨1063016, by rfl⟩ : syracuseStep 1417355 = 2126033) B2126033
theorem B1417409 : Blo 626299 1417409 := bstep (se 2 (by rfl) ⟨531528, by rfl⟩ : syracuseStep 1417409 = 1063057) B1063057
theorem B4759883 : Blo 626299 4759883 := bstep (se 1 (by rfl) ⟨3569912, by rfl⟩ : syracuseStep 4759883 = 7139825) B7139825
theorem B1417625 : Blo 626299 1417625 := bstep (se 2 (by rfl) ⟨531609, by rfl⟩ : syracuseStep 1417625 = 1063219) B1063219
theorem B1417715 : Blo 626299 1417715 := bstep (se 1 (by rfl) ⟨1063286, by rfl⟩ : syracuseStep 1417715 = 2126573) B2126573
theorem B1417751 : Blo 626299 1417751 := bstep (se 1 (by rfl) ⟨1063313, by rfl⟩ : syracuseStep 1417751 = 2126627) B2126627
theorem B10199621 : Blo 626299 10199621 := bstep (se 4 (by rfl) ⟨956214, by rfl⟩ : syracuseStep 10199621 = 1912429) B1912429
theorem B1057367 : Blo 626299 1057367 := bstep (se 1 (by rfl) ⟨793025, by rfl⟩ : syracuseStep 1057367 = 1586051) B1586051
theorem B1417931 : Blo 626299 1417931 := bstep (se 1 (by rfl) ⟨1063448, by rfl⟩ : syracuseStep 1417931 = 2126897) B2126897
theorem B1057495 : Blo 626299 1057495 := bstep (se 1 (by rfl) ⟨793121, by rfl⟩ : syracuseStep 1057495 = 1586243) B1586243
theorem B2007769 : Blo 626299 2007769 := bstep (se 2 (by rfl) ⟨752913, by rfl⟩ : syracuseStep 2007769 = 1505827) B1505827
theorem B1417985 : Blo 626299 1417985 := bstep (se 2 (by rfl) ⟨531744, by rfl⟩ : syracuseStep 1417985 = 1063489) B1063489
theorem B5088005 : Blo 626299 5088005 := bstep (se 4 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 5088005 = 954001) B954001
theorem B795415 : Blo 626299 795415 := bstep (se 1 (by rfl) ⟨596561, by rfl⟩ : syracuseStep 795415 = 1193123) B1193123
theorem B3187673 : Blo 626299 3187673 := bstep (se 2 (by rfl) ⟨1195377, by rfl⟩ : syracuseStep 3187673 = 2390755) B2390755
theorem B2270273 : Blo 626299 2270273 := bstep (se 2 (by rfl) ⟨851352, by rfl⟩ : syracuseStep 2270273 = 1702705) B1702705
theorem B2008385 : Blo 626299 2008385 := bstep (se 2 (by rfl) ⟨753144, by rfl⟩ : syracuseStep 2008385 = 1506289) B1506289
theorem B1058123 : Blo 626299 1058123 := bstep (se 1 (by rfl) ⟨793592, by rfl⟩ : syracuseStep 1058123 = 1587185) B1587185
theorem B1189235 : Blo 626299 1189235 := bstep (se 1 (by rfl) ⟨891926, by rfl⟩ : syracuseStep 1189235 = 1783853) B1783853
theorem B1058251 : Blo 626299 1058251 := bstep (se 1 (by rfl) ⟨793688, by rfl⟩ : syracuseStep 1058251 = 1587377) B1587377
theorem B1058393 : Blo 626299 1058393 := bstep (se 2 (by rfl) ⟨396897, by rfl⟩ : syracuseStep 1058393 = 793795) B793795
theorem B1058521 : Blo 626299 1058521 := bstep (se 2 (by rfl) ⟨396945, by rfl⟩ : syracuseStep 1058521 = 793891) B793891
theorem B1189721 : Blo 626299 1189721 := bstep (se 2 (by rfl) ⟨446145, by rfl⟩ : syracuseStep 1189721 = 892291) B892291
theorem B2172851 : Blo 626299 2172851 := bstep (se 1 (by rfl) ⟨1629638, by rfl⟩ : syracuseStep 2172851 = 3259277) B3259277
theorem B1910873 : Blo 626299 1910873 := bstep (se 2 (by rfl) ⟨716577, by rfl⟩ : syracuseStep 1910873 = 1433155) B1433155
theorem B1059095 : Blo 626299 1059095 := bstep (se 1 (by rfl) ⟨794321, by rfl⟩ : syracuseStep 1059095 = 1588643) B1588643
theorem B5351831 : Blo 626299 5351831 := bstep (se 1 (by rfl) ⟨4013873, by rfl⟩ : syracuseStep 5351831 = 8027747) B8027747
theorem B1059223 : Blo 626299 1059223 := bstep (se 1 (by rfl) ⟨794417, by rfl⟩ : syracuseStep 1059223 = 1588835) B1588835
theorem B797131 : Blo 626299 797131 := bstep (se 1 (by rfl) ⟨597848, by rfl⟩ : syracuseStep 797131 = 1195697) B1195697
theorem B3189293 : Blo 626299 3189293 := bstep (se 3 (by rfl) ⟨597992, by rfl⟩ : syracuseStep 3189293 = 1195985) B1195985
theorem B7547543 : Blo 626299 7547543 := bstep (se 1 (by rfl) ⟨5660657, by rfl⟩ : syracuseStep 7547543 = 11321315) B11321315
theorem B3582899 : Blo 626299 3582899 := bstep (se 1 (by rfl) ⟨2687174, by rfl⟩ : syracuseStep 3582899 = 5374349) B5374349
theorem B1059851 : Blo 626299 1059851 := bstep (se 1 (by rfl) ⟨794888, by rfl⟩ : syracuseStep 1059851 = 1589777) B1589777
theorem B1059979 : Blo 626299 1059979 := bstep (se 1 (by rfl) ⟨794984, by rfl⟩ : syracuseStep 1059979 = 1589969) B1589969
theorem B18656407 : Blo 626299 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B1191179 : Blo 626299 1191179 := bstep (se 1 (by rfl) ⟨893384, by rfl⟩ : syracuseStep 1191179 = 1786769) B1786769
theorem B1060121 : Blo 626299 1060121 := bstep (se 2 (by rfl) ⟨397545, by rfl⟩ : syracuseStep 1060121 = 795091) B795091
theorem B1060249 : Blo 626299 1060249 := bstep (se 2 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 1060249 = 795187) B795187
theorem B1191361 : Blo 626299 1191361 := bstep (se 2 (by rfl) ⟨446760, by rfl⟩ : syracuseStep 1191361 = 893521) B893521
theorem B896665 : Blo 626299 896665 := bstep (se 2 (by rfl) ⟨336249, by rfl⟩ : syracuseStep 896665 = 672499) B672499
theorem B1814195 : Blo 626299 1814195 := bstep (se 1 (by rfl) ⟨1360646, by rfl⟩ : syracuseStep 1814195 = 2721293) B2721293
theorem B2010845 : Blo 626299 2010845 := bstep (se 3 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 2010845 = 754067) B754067
theorem B1191809 : Blo 626299 1191809 := bstep (se 2 (by rfl) ⟨446928, by rfl⟩ : syracuseStep 1191809 = 893857) B893857
theorem B1060823 : Blo 626299 1060823 := bstep (se 1 (by rfl) ⟨795617, by rfl⟩ : syracuseStep 1060823 = 1591235) B1591235
theorem B2830301 : Blo 626299 2830301 := bstep (se 3 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 2830301 = 1061363) B1061363
theorem B1060951 : Blo 626299 1060951 := bstep (se 1 (by rfl) ⟨795713, by rfl⟩ : syracuseStep 1060951 = 1591427) B1591427
theorem B7155863 : Blo 626299 7155863 := bstep (se 1 (by rfl) ⟨5366897, by rfl⟩ : syracuseStep 7155863 = 10733795) B10733795
theorem B1192151 : Blo 626299 1192151 := bstep (se 1 (by rfl) ⟨894113, by rfl⟩ : syracuseStep 1192151 = 1788227) B1788227
theorem B3584357 : Blo 626299 3584357 := bstep (se 4 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 3584357 = 672067) B672067
theorem B1913305 : Blo 626299 1913305 := bstep (se 2 (by rfl) ⟨717489, by rfl⟩ : syracuseStep 1913305 = 1434979) B1434979
theorem B2863667 : Blo 626299 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B1356353 : Blo 626299 1356353 := bstep (se 2 (by rfl) ⟨508632, by rfl⟩ : syracuseStep 1356353 = 1017265) B1017265
theorem B1061579 : Blo 626299 1061579 := bstep (se 1 (by rfl) ⟨796184, by rfl⟩ : syracuseStep 1061579 = 1592369) B1592369
theorem B9679661 : Blo 626299 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B1061707 : Blo 626299 1061707 := bstep (se 1 (by rfl) ⟨796280, by rfl⟩ : syracuseStep 1061707 = 1592561) B1592561
theorem B1192819 : Blo 626299 1192819 := bstep (se 1 (by rfl) ⟨894614, by rfl⟩ : syracuseStep 1192819 = 1789229) B1789229
theorem B2175947 : Blo 626299 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B1061849 : Blo 626299 1061849 := bstep (se 2 (by rfl) ⟨398193, by rfl⟩ : syracuseStep 1061849 = 796387) B796387
theorem B1061977 : Blo 626299 1061977 := bstep (se 2 (by rfl) ⟨398241, by rfl⟩ : syracuseStep 1061977 = 796483) B796483
theorem B4535473 : Blo 626299 4535473 := bstep (se 2 (by rfl) ⟨1700802, by rfl⟩ : syracuseStep 4535473 = 3401605) B3401605
theorem B668855 : Blo 626299 668855 := bstep (se 1 (by rfl) ⟨501641, by rfl⟩ : syracuseStep 668855 = 1003283) B1003283
theorem B1193267 : Blo 626299 1193267 := bstep (se 1 (by rfl) ⟨894950, by rfl⟩ : syracuseStep 1193267 = 1789901) B1789901
theorem B668983 : Blo 626299 668983 := bstep (se 1 (by rfl) ⟨501737, by rfl⟩ : syracuseStep 668983 = 1003475) B1003475
theorem B3814721 : Blo 626299 3814721 := bstep (se 2 (by rfl) ⟨1430520, by rfl⟩ : syracuseStep 3814721 = 2861041) B2861041
theorem B1193305 : Blo 626299 1193305 := bstep (se 2 (by rfl) ⟨447489, by rfl⟩ : syracuseStep 1193305 = 894979) B894979
theorem B4765229 : Blo 626299 4765229 := bstep (se 3 (by rfl) ⟨893480, by rfl⟩ : syracuseStep 4765229 = 1786961) B1786961
theorem B1062551 : Blo 626299 1062551 := bstep (se 1 (by rfl) ⟨796913, by rfl⟩ : syracuseStep 1062551 = 1593827) B1593827
theorem B1586891 : Blo 626299 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B1062679 : Blo 626299 1062679 := bstep (se 1 (by rfl) ⟨797009, by rfl⟩ : syracuseStep 1062679 = 1594019) B1594019
theorem B1193753 : Blo 626299 1193753 := bstep (se 2 (by rfl) ⟨447657, by rfl⟩ : syracuseStep 1193753 = 895315) B895315
theorem B669547 : Blo 626299 669547 := bstep (se 1 (by rfl) ⟨502160, by rfl⟩ : syracuseStep 669547 = 1004321) B1004321
theorem B2144179 : Blo 626299 2144179 := bstep (se 1 (by rfl) ⟨1608134, by rfl⟩ : syracuseStep 2144179 = 3216269) B3216269
theorem B6043571 : Blo 626299 6043571 := bstep (se 1 (by rfl) ⟨4532678, by rfl⟩ : syracuseStep 6043571 = 9065357) B9065357
theorem B32553035 : Blo 626299 32553035 := bstep (se 1 (by rfl) ⟨24414776, by rfl⟩ : syracuseStep 32553035 = 48829553) B48829553
theorem B669803 : Blo 626299 669803 := bstep (se 1 (by rfl) ⟨502352, by rfl⟩ : syracuseStep 669803 = 1004705) B1004705
theorem B1063307 : Blo 626299 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B1194497 : Blo 626299 1194497 := bstep (se 2 (by rfl) ⟨447936, by rfl⟩ : syracuseStep 1194497 = 895873) B895873
theorem B1063435 : Blo 626299 1063435 := bstep (se 1 (by rfl) ⟨797576, by rfl⟩ : syracuseStep 1063435 = 1595153) B1595153
theorem B1587863 : Blo 626299 1587863 := bstep (se 1 (by rfl) ⟨1190897, by rfl⟩ : syracuseStep 1587863 = 2381795) B2381795
theorem B1063577 : Blo 626299 1063577 := bstep (se 2 (by rfl) ⟨398841, by rfl⟩ : syracuseStep 1063577 = 797683) B797683
theorem B1194763 : Blo 626299 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B4307843 : Blo 626299 4307843 := bstep (se 1 (by rfl) ⟨3230882, by rfl⟩ : syracuseStep 4307843 = 6461765) B6461765
theorem B1784855 : Blo 626299 1784855 := bstep (se 1 (by rfl) ⟨1338641, by rfl⟩ : syracuseStep 1784855 = 2677283) B2677283
theorem B5717143 : Blo 626299 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B1195211 : Blo 626299 1195211 := bstep (se 1 (by rfl) ⟨896408, by rfl⟩ : syracuseStep 1195211 = 1792817) B1792817
theorem B1588531 : Blo 626299 1588531 := bstep (se 1 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 1588531 = 2382797) B2382797
theorem B10894657 : Blo 626299 10894657 := bstep (se 2 (by rfl) ⟨4085496, by rfl⟩ : syracuseStep 10894657 = 8170993) B8170993
theorem B4013387 : Blo 626299 4013387 := bstep (se 1 (by rfl) ⟨3010040, by rfl⟩ : syracuseStep 4013387 = 6020081) B6020081
theorem B1195393 : Blo 626299 1195393 := bstep (se 2 (by rfl) ⟨448272, by rfl⟩ : syracuseStep 1195393 = 896545) B896545
theorem B1588673 : Blo 626299 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B1916567 : Blo 626299 1916567 := bstep (se 1 (by rfl) ⟨1437425, by rfl⟩ : syracuseStep 1916567 = 2874851) B2874851
theorem B1195735 : Blo 626299 1195735 := bstep (se 1 (by rfl) ⟨896801, by rfl⟩ : syracuseStep 1195735 = 1793603) B1793603
theorem B1359703 : Blo 626299 1359703 := bstep (se 1 (by rfl) ⟨1019777, by rfl⟩ : syracuseStep 1359703 = 2039555) B2039555
theorem B1195955 : Blo 626299 1195955 := bstep (se 1 (by rfl) ⟨896966, by rfl⟩ : syracuseStep 1195955 = 1793933) B1793933
theorem B5357603 : Blo 626299 5357603 := bstep (se 1 (by rfl) ⟨4018202, by rfl⟩ : syracuseStep 5357603 = 8036405) B8036405
theorem B704587 : Blo 626299 704587 := bstep (se 1 (by rfl) ⟨528440, by rfl⟩ : syracuseStep 704587 = 1056881) B1056881
theorem B671819 : Blo 626299 671819 := bstep (se 1 (by rfl) ⟨503864, by rfl⟩ : syracuseStep 671819 = 1007729) B1007729
theorem B22986827 : Blo 626299 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B1130611 : Blo 626299 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B1196183 : Blo 626299 1196183 := bstep (se 1 (by rfl) ⟨897137, by rfl⟩ : syracuseStep 1196183 = 1794275) B1794275
theorem B704695 : Blo 626299 704695 := bstep (se 1 (by rfl) ⟨528521, by rfl⟩ : syracuseStep 704695 = 1057043) B1057043
theorem B1786187 : Blo 626299 1786187 := bstep (se 1 (by rfl) ⟨1339640, by rfl⟩ : syracuseStep 1786187 = 2679281) B2679281
theorem B704875 : Blo 626299 704875 := bstep (se 1 (by rfl) ⟨528656, by rfl⟩ : syracuseStep 704875 = 1057313) B1057313
theorem B1196441 : Blo 626299 1196441 := bstep (se 2 (by rfl) ⟨448665, by rfl⟩ : syracuseStep 1196441 = 897331) B897331
theorem B704983 : Blo 626299 704983 := bstep (se 1 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 704983 = 1057475) B1057475
theorem B2114099 : Blo 626299 2114099 := bstep (se 1 (by rfl) ⟨1585574, by rfl⟩ : syracuseStep 2114099 = 3171149) B3171149
theorem B705163 : Blo 626299 705163 := bstep (se 1 (by rfl) ⟨528872, by rfl⟩ : syracuseStep 705163 = 1057745) B1057745
theorem B1589939 : Blo 626299 1589939 := bstep (se 1 (by rfl) ⟨1192454, by rfl⟩ : syracuseStep 1589939 = 2384909) B2384909
theorem B705271 : Blo 626299 705271 := bstep (se 1 (by rfl) ⟨528953, by rfl⟩ : syracuseStep 705271 = 1057907) B1057907
theorem B2114369 : Blo 626299 2114369 := bstep (se 2 (by rfl) ⟨792888, by rfl⟩ : syracuseStep 2114369 = 1585777) B1585777
theorem B3621763 : Blo 626299 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B705451 : Blo 626299 705451 := bstep (se 1 (by rfl) ⟨529088, by rfl⟩ : syracuseStep 705451 = 1058177) B1058177
theorem B705559 : Blo 626299 705559 := bstep (se 1 (by rfl) ⟨529169, by rfl⟩ : syracuseStep 705559 = 1058339) B1058339
theorem B2016407 : Blo 626299 2016407 := bstep (se 1 (by rfl) ⟨1512305, by rfl⟩ : syracuseStep 2016407 = 3024611) B3024611
theorem B705739 : Blo 626299 705739 := bstep (se 1 (by rfl) ⟨529304, by rfl⟩ : syracuseStep 705739 = 1058609) B1058609
theorem B1590475 : Blo 626299 1590475 := bstep (se 1 (by rfl) ⟨1192856, by rfl⟩ : syracuseStep 1590475 = 2385713) B2385713
theorem B2016535 : Blo 626299 2016535 := bstep (se 1 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 2016535 = 3024803) B3024803
theorem B9684269 : Blo 626299 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B705847 : Blo 626299 705847 := bstep (se 1 (by rfl) ⟨529385, by rfl⟩ : syracuseStep 705847 = 1058771) B1058771
theorem B1590617 : Blo 626299 1590617 := bstep (se 2 (by rfl) ⟨596481, by rfl⟩ : syracuseStep 1590617 = 1192963) B1192963
theorem B2114909 : Blo 626299 2114909 := bstep (se 3 (by rfl) ⟨396545, by rfl⟩ : syracuseStep 2114909 = 793091) B793091
theorem B4769117 : Blo 626299 4769117 := bstep (se 3 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 4769117 = 1788419) B1788419
theorem B706027 : Blo 626299 706027 := bstep (se 1 (by rfl) ⟨529520, by rfl⟩ : syracuseStep 706027 = 1059041) B1059041
theorem B2016791 : Blo 626299 2016791 := bstep (se 1 (by rfl) ⟨1512593, by rfl⟩ : syracuseStep 2016791 = 3025187) B3025187
theorem B706135 : Blo 626299 706135 := bstep (se 1 (by rfl) ⟨529601, by rfl⟩ : syracuseStep 706135 = 1059203) B1059203
theorem B8570461 : Blo 626299 8570461 := bstep (se 3 (by rfl) ⟨1606961, by rfl⟩ : syracuseStep 8570461 = 3213923) B3213923
theorem B706315 : Blo 626299 706315 := bstep (se 1 (by rfl) ⟨529736, by rfl⟩ : syracuseStep 706315 = 1059473) B1059473
theorem B2869067 : Blo 626299 2869067 := bstep (se 1 (by rfl) ⟨2151800, by rfl⟩ : syracuseStep 2869067 = 4303601) B4303601
theorem B4835173 : Blo 626299 4835173 := bstep (se 4 (by rfl) ⟨453297, by rfl⟩ : syracuseStep 4835173 = 906595) B906595
theorem B706423 : Blo 626299 706423 := bstep (se 1 (by rfl) ⟨529817, by rfl⟩ : syracuseStep 706423 = 1059635) B1059635
theorem B1132427 : Blo 626299 1132427 := bstep (se 1 (by rfl) ⟨849320, by rfl⟩ : syracuseStep 1132427 = 1698641) B1698641
theorem B4016051 : Blo 626299 4016051 := bstep (se 1 (by rfl) ⟨3012038, by rfl⟩ : syracuseStep 4016051 = 6024077) B6024077
theorem B1787827 : Blo 626299 1787827 := bstep (se 1 (by rfl) ⟨1340870, by rfl⟩ : syracuseStep 1787827 = 2681741) B2681741
theorem B706603 : Blo 626299 706603 := bstep (se 1 (by rfl) ⟨529952, by rfl⟩ : syracuseStep 706603 = 1059905) B1059905
theorem B706711 : Blo 626299 706711 := bstep (se 1 (by rfl) ⟨530033, by rfl⟩ : syracuseStep 706711 = 1060067) B1060067
theorem B1591447 : Blo 626299 1591447 := bstep (se 1 (by rfl) ⟨1193585, by rfl⟩ : syracuseStep 1591447 = 2387171) B2387171
theorem B706891 : Blo 626299 706891 := bstep (se 1 (by rfl) ⟨530168, by rfl⟩ : syracuseStep 706891 = 1060337) B1060337
theorem B706999 : Blo 626299 706999 := bstep (se 1 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 706999 = 1060499) B1060499
theorem B2116043 : Blo 626299 2116043 := bstep (se 1 (by rfl) ⟨1587032, by rfl⟩ : syracuseStep 2116043 = 3174065) B3174065
theorem B3230225 : Blo 626299 3230225 := bstep (se 2 (by rfl) ⟨1211334, by rfl⟩ : syracuseStep 3230225 = 2422669) B2422669
theorem B1591883 : Blo 626299 1591883 := bstep (se 1 (by rfl) ⟨1193912, by rfl⟩ : syracuseStep 1591883 = 2387825) B2387825
theorem B3066443 : Blo 626299 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B2017867 : Blo 626299 2017867 := bstep (se 1 (by rfl) ⟨1513400, by rfl⟩ : syracuseStep 2017867 = 3026801) B3026801
theorem B707179 : Blo 626299 707179 := bstep (se 1 (by rfl) ⟨530384, by rfl⟩ : syracuseStep 707179 = 1060769) B1060769
theorem B707287 : Blo 626299 707287 := bstep (se 1 (by rfl) ⟨530465, by rfl⟩ : syracuseStep 707287 = 1060931) B1060931
theorem B2116313 : Blo 626299 2116313 := bstep (se 2 (by rfl) ⟨793617, by rfl⟩ : syracuseStep 2116313 = 1587235) B1587235
theorem B2018009 : Blo 626299 2018009 := bstep (se 2 (by rfl) ⟨756753, by rfl⟩ : syracuseStep 2018009 = 1513507) B1513507
theorem B2018123 : Blo 626299 2018123 := bstep (se 1 (by rfl) ⟨1513592, by rfl⟩ : syracuseStep 2018123 = 3027185) B3027185
theorem B707467 : Blo 626299 707467 := bstep (se 1 (by rfl) ⟨530600, by rfl⟩ : syracuseStep 707467 = 1061201) B1061201
theorem B1592257 : Blo 626299 1592257 := bstep (se 2 (by rfl) ⟨597096, by rfl⟩ : syracuseStep 1592257 = 1194193) B1194193
theorem B1788875 : Blo 626299 1788875 := bstep (se 1 (by rfl) ⟨1341656, by rfl⟩ : syracuseStep 1788875 = 2683313) B2683313
theorem B707575 : Blo 626299 707575 := bstep (se 1 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 707575 = 1061363) B1061363
theorem B9784451 : Blo 626299 9784451 := bstep (se 1 (by rfl) ⟨7338338, by rfl⟩ : syracuseStep 9784451 = 14676677) B14676677
theorem B707755 : Blo 626299 707755 := bstep (se 1 (by rfl) ⟨530816, by rfl⟩ : syracuseStep 707755 = 1061633) B1061633
theorem B1133747 : Blo 626299 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B2018483 : Blo 626299 2018483 := bstep (se 1 (by rfl) ⟨1513862, by rfl⟩ : syracuseStep 2018483 = 3027725) B3027725
theorem B707863 : Blo 626299 707863 := bstep (se 1 (by rfl) ⟨530897, by rfl⟩ : syracuseStep 707863 = 1061795) B1061795
theorem B2117015 : Blo 626299 2117015 := bstep (se 1 (by rfl) ⟨1587761, by rfl⟩ : syracuseStep 2117015 = 3175523) B3175523
theorem B708043 : Blo 626299 708043 := bstep (se 1 (by rfl) ⟨531032, by rfl⟩ : syracuseStep 708043 = 1062065) B1062065
theorem B1592855 : Blo 626299 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B708151 : Blo 626299 708151 := bstep (se 1 (by rfl) ⟨531113, by rfl⟩ : syracuseStep 708151 = 1062227) B1062227
theorem B5361227 : Blo 626299 5361227 := bstep (se 1 (by rfl) ⟨4020920, by rfl⟩ : syracuseStep 5361227 = 8041841) B8041841
theorem B2379395 : Blo 626299 2379395 := bstep (se 1 (by rfl) ⟨1784546, by rfl⟩ : syracuseStep 2379395 = 3569093) B3569093
theorem B708331 : Blo 626299 708331 := bstep (se 1 (by rfl) ⟨531248, by rfl⟩ : syracuseStep 708331 = 1062497) B1062497
theorem B708439 : Blo 626299 708439 := bstep (se 1 (by rfl) ⟨531329, by rfl⟩ : syracuseStep 708439 = 1062659) B1062659
theorem B2117555 : Blo 626299 2117555 := bstep (se 1 (by rfl) ⟨1588166, by rfl⟩ : syracuseStep 2117555 = 3176333) B3176333
theorem B708619 : Blo 626299 708619 := bstep (se 1 (by rfl) ⟨531464, by rfl⟩ : syracuseStep 708619 = 1062929) B1062929
theorem B2379851 : Blo 626299 2379851 := bstep (se 1 (by rfl) ⟨1784888, by rfl⟩ : syracuseStep 2379851 = 3569777) B3569777
theorem B708727 : Blo 626299 708727 := bstep (se 1 (by rfl) ⟨531545, by rfl⟩ : syracuseStep 708727 = 1063091) B1063091
theorem B2117825 : Blo 626299 2117825 := bstep (se 2 (by rfl) ⟨794184, by rfl⟩ : syracuseStep 2117825 = 1588369) B1588369
theorem B2380049 : Blo 626299 2380049 := bstep (se 2 (by rfl) ⟨892518, by rfl⟩ : syracuseStep 2380049 = 1785037) B1785037
theorem B708907 : Blo 626299 708907 := bstep (se 1 (by rfl) ⟨531680, by rfl⟩ : syracuseStep 708907 = 1063361) B1063361
theorem B1593665 : Blo 626299 1593665 := bstep (se 2 (by rfl) ⟨597624, by rfl⟩ : syracuseStep 1593665 = 1195249) B1195249
theorem B709015 : Blo 626299 709015 := bstep (se 1 (by rfl) ⟨531761, by rfl⟩ : syracuseStep 709015 = 1063523) B1063523
theorem B1790515 : Blo 626299 1790515 := bstep (se 1 (by rfl) ⟨1342886, by rfl⟩ : syracuseStep 1790515 = 2685773) B2685773
theorem B2118365 : Blo 626299 2118365 := bstep (se 3 (by rfl) ⟨397193, by rfl⟩ : syracuseStep 2118365 = 794387) B794387
theorem B1135361 : Blo 626299 1135361 := bstep (se 2 (by rfl) ⟨425760, by rfl⟩ : syracuseStep 1135361 = 851521) B851521
theorem B1790743 : Blo 626299 1790743 := bstep (se 1 (by rfl) ⟨1343057, by rfl⟩ : syracuseStep 1790743 = 2686115) B2686115
theorem B2675521 : Blo 626299 2675521 := bstep (se 2 (by rfl) ⟨1003320, by rfl⟩ : syracuseStep 2675521 = 2006641) B2006641
theorem B1594201 : Blo 626299 1594201 := bstep (se 2 (by rfl) ⟨597825, by rfl⟩ : syracuseStep 1594201 = 1195651) B1195651
theorem B1430401 : Blo 626299 1430401 := bstep (se 2 (by rfl) ⟨536400, by rfl⟩ : syracuseStep 1430401 = 1072801) B1072801
theorem B2544587 : Blo 626299 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B2380823 : Blo 626299 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B2381021 : Blo 626299 2381021 := bstep (se 3 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 2381021 = 892883) B892883
theorem B939467 : Blo 626299 939467 := bstep (se 1 (by rfl) ⟨704600, by rfl⟩ : syracuseStep 939467 = 1409201) B1409201
theorem B939479 : Blo 626299 939479 := bstep (se 1 (by rfl) ⟨704609, by rfl⟩ : syracuseStep 939479 = 1409219) B1409219
theorem B939545 : Blo 626299 939545 := bstep (se 2 (by rfl) ⟨352329, by rfl⟩ : syracuseStep 939545 = 704659) B704659
theorem B4019843 : Blo 626299 4019843 := bstep (se 1 (by rfl) ⟨3014882, by rfl⟩ : syracuseStep 4019843 = 6029765) B6029765
theorem B939659 : Blo 626299 939659 := bstep (se 1 (by rfl) ⟨704744, by rfl⟩ : syracuseStep 939659 = 1409489) B1409489
theorem B939671 : Blo 626299 939671 := bstep (se 1 (by rfl) ⟨704753, by rfl⟩ : syracuseStep 939671 = 1409507) B1409507
theorem B2545303 : Blo 626299 2545303 := bstep (se 1 (by rfl) ⟨1908977, by rfl⟩ : syracuseStep 2545303 = 3817955) B3817955
theorem B939737 : Blo 626299 939737 := bstep (se 2 (by rfl) ⟨352401, by rfl⟩ : syracuseStep 939737 = 704803) B704803
theorem B2414387 : Blo 626299 2414387 := bstep (se 1 (by rfl) ⟨1810790, by rfl⟩ : syracuseStep 2414387 = 3621581) B3621581
theorem B10180417 : Blo 626299 10180417 := bstep (se 2 (by rfl) ⟨3817656, by rfl⟩ : syracuseStep 10180417 = 7635313) B7635313
theorem B939851 : Blo 626299 939851 := bstep (se 1 (by rfl) ⟨704888, by rfl⟩ : syracuseStep 939851 = 1409777) B1409777
theorem B2119499 : Blo 626299 2119499 := bstep (se 1 (by rfl) ⟨1589624, by rfl⟩ : syracuseStep 2119499 = 3179249) B3179249
theorem B939863 : Blo 626299 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B939929 : Blo 626299 939929 := bstep (se 2 (by rfl) ⟨352473, by rfl⟩ : syracuseStep 939929 = 704947) B704947
theorem B1595315 : Blo 626299 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B940043 : Blo 626299 940043 := bstep (se 1 (by rfl) ⟨705032, by rfl⟩ : syracuseStep 940043 = 1410065) B1410065
theorem B940055 : Blo 626299 940055 := bstep (se 1 (by rfl) ⟨705041, by rfl⟩ : syracuseStep 940055 = 1410083) B1410083
theorem B4773953 : Blo 626299 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B940121 : Blo 626299 940121 := bstep (se 2 (by rfl) ⟨352545, by rfl⟩ : syracuseStep 940121 = 705091) B705091
theorem B2119769 : Blo 626299 2119769 := bstep (se 2 (by rfl) ⟨794913, by rfl⟩ : syracuseStep 2119769 = 1589827) B1589827
theorem B5363891 : Blo 626299 5363891 := bstep (se 1 (by rfl) ⟨4022918, by rfl⟩ : syracuseStep 5363891 = 8045837) B8045837
theorem B940235 : Blo 626299 940235 := bstep (se 1 (by rfl) ⟨705176, by rfl⟩ : syracuseStep 940235 = 1410353) B1410353
theorem B940247 : Blo 626299 940247 := bstep (se 1 (by rfl) ⟨705185, by rfl⟩ : syracuseStep 940247 = 1410371) B1410371
theorem B2677009 : Blo 626299 2677009 := bstep (se 2 (by rfl) ⟨1003878, by rfl⟩ : syracuseStep 2677009 = 2007757) B2007757
theorem B940313 : Blo 626299 940313 := bstep (se 2 (by rfl) ⟨352617, by rfl⟩ : syracuseStep 940313 = 705235) B705235
theorem B2578781 : Blo 626299 2578781 := bstep (se 3 (by rfl) ⟨483521, by rfl⟩ : syracuseStep 2578781 = 967043) B967043
theorem B940427 : Blo 626299 940427 := bstep (se 1 (by rfl) ⟨705320, by rfl⟩ : syracuseStep 940427 = 1410641) B1410641
theorem B940439 : Blo 626299 940439 := bstep (se 1 (by rfl) ⟨705329, by rfl⟩ : syracuseStep 940439 = 1410659) B1410659
theorem B940505 : Blo 626299 940505 := bstep (se 2 (by rfl) ⟨352689, by rfl⟩ : syracuseStep 940505 = 705379) B705379
theorem B940619 : Blo 626299 940619 := bstep (se 1 (by rfl) ⟨705464, by rfl⟩ : syracuseStep 940619 = 1410929) B1410929
theorem B940631 : Blo 626299 940631 := bstep (se 1 (by rfl) ⟨705473, by rfl⟩ : syracuseStep 940631 = 1410947) B1410947
theorem B1792601 : Blo 626299 1792601 := bstep (se 2 (by rfl) ⟨672225, by rfl⟩ : syracuseStep 1792601 = 1344451) B1344451
theorem B3824279 : Blo 626299 3824279 := bstep (se 1 (by rfl) ⟨2868209, by rfl⟩ : syracuseStep 3824279 = 5736419) B5736419
theorem B940697 : Blo 626299 940697 := bstep (se 2 (by rfl) ⟨352761, by rfl⟩ : syracuseStep 940697 = 705523) B705523
theorem B1694401 : Blo 626299 1694401 := bstep (se 2 (by rfl) ⟨635400, by rfl⟩ : syracuseStep 1694401 = 1270801) B1270801
theorem B940811 : Blo 626299 940811 := bstep (se 1 (by rfl) ⟨705608, by rfl⟩ : syracuseStep 940811 = 1411217) B1411217
theorem B940823 : Blo 626299 940823 := bstep (se 1 (by rfl) ⟨705617, by rfl⟩ : syracuseStep 940823 = 1411235) B1411235
theorem B2120471 : Blo 626299 2120471 := bstep (se 1 (by rfl) ⟨1590353, by rfl⟩ : syracuseStep 2120471 = 3180707) B3180707
theorem B940889 : Blo 626299 940889 := bstep (se 2 (by rfl) ⟨352833, by rfl⟩ : syracuseStep 940889 = 705667) B705667
theorem B941003 : Blo 626299 941003 := bstep (se 1 (by rfl) ⟨705752, by rfl⟩ : syracuseStep 941003 = 1411505) B1411505
theorem B941015 : Blo 626299 941015 := bstep (se 1 (by rfl) ⟨705761, by rfl⟩ : syracuseStep 941015 = 1411523) B1411523
theorem B941081 : Blo 626299 941081 := bstep (se 2 (by rfl) ⟨352905, by rfl⟩ : syracuseStep 941081 = 705811) B705811
theorem B3628097 : Blo 626299 3628097 := bstep (se 2 (by rfl) ⟨1360536, by rfl⟩ : syracuseStep 3628097 = 2721073) B2721073
theorem B2382979 : Blo 626299 2382979 := bstep (se 1 (by rfl) ⟨1787234, by rfl⟩ : syracuseStep 2382979 = 3574469) B3574469
theorem B941195 : Blo 626299 941195 := bstep (se 1 (by rfl) ⟨705896, by rfl⟩ : syracuseStep 941195 = 1411793) B1411793
theorem B941207 : Blo 626299 941207 := bstep (se 1 (by rfl) ⟨705905, by rfl⟩ : syracuseStep 941207 = 1411811) B1411811
theorem B7625933 : Blo 626299 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B941273 : Blo 626299 941273 := bstep (se 2 (by rfl) ⟨352977, by rfl⟩ : syracuseStep 941273 = 705955) B705955
theorem B5364953 : Blo 626299 5364953 := bstep (se 2 (by rfl) ⟨2011857, by rfl⟩ : syracuseStep 5364953 = 4023715) B4023715
theorem B2121011 : Blo 626299 2121011 := bstep (se 1 (by rfl) ⟨1590758, by rfl⟩ : syracuseStep 2121011 = 3181517) B3181517
theorem B941387 : Blo 626299 941387 := bstep (se 1 (by rfl) ⟨706040, by rfl⟩ : syracuseStep 941387 = 1412081) B1412081
theorem B941399 : Blo 626299 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B1793431 : Blo 626299 1793431 := bstep (se 1 (by rfl) ⟨1345073, by rfl⟩ : syracuseStep 1793431 = 2690147) B2690147
theorem B941465 : Blo 626299 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B2383283 : Blo 626299 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B1007063 : Blo 626299 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B941579 : Blo 626299 941579 := bstep (se 1 (by rfl) ⟨706184, by rfl⟩ : syracuseStep 941579 = 1412369) B1412369
theorem B941591 : Blo 626299 941591 := bstep (se 1 (by rfl) ⟨706193, by rfl⟩ : syracuseStep 941591 = 1412387) B1412387
theorem B2121281 : Blo 626299 2121281 := bstep (se 2 (by rfl) ⟨795480, by rfl⟩ : syracuseStep 2121281 = 1590961) B1590961
theorem B1007191 : Blo 626299 1007191 := bstep (se 1 (by rfl) ⟨755393, by rfl⟩ : syracuseStep 1007191 = 1510787) B1510787
theorem B941657 : Blo 626299 941657 := bstep (se 2 (by rfl) ⟨353121, by rfl⟩ : syracuseStep 941657 = 706243) B706243
theorem B941771 : Blo 626299 941771 := bstep (se 1 (by rfl) ⟨706328, by rfl⟩ : syracuseStep 941771 = 1412657) B1412657
theorem B941783 : Blo 626299 941783 := bstep (se 1 (by rfl) ⟨706337, by rfl⟩ : syracuseStep 941783 = 1412675) B1412675
theorem B941849 : Blo 626299 941849 := bstep (se 2 (by rfl) ⟨353193, by rfl⟩ : syracuseStep 941849 = 706387) B706387
theorem B941963 : Blo 626299 941963 := bstep (se 1 (by rfl) ⟨706472, by rfl⟩ : syracuseStep 941963 = 1412945) B1412945
theorem B941975 : Blo 626299 941975 := bstep (se 1 (by rfl) ⟨706481, by rfl⟩ : syracuseStep 941975 = 1412963) B1412963
theorem B942041 : Blo 626299 942041 := bstep (se 2 (by rfl) ⟨353265, by rfl⟩ : syracuseStep 942041 = 706531) B706531
theorem B1695809 : Blo 626299 1695809 := bstep (se 2 (by rfl) ⟨635928, by rfl⟩ : syracuseStep 1695809 = 1271857) B1271857
theorem B2383937 : Blo 626299 2383937 := bstep (se 2 (by rfl) ⟨893976, by rfl⟩ : syracuseStep 2383937 = 1787953) B1787953
theorem B942155 : Blo 626299 942155 := bstep (se 1 (by rfl) ⟨706616, by rfl⟩ : syracuseStep 942155 = 1413233) B1413233
theorem B942167 : Blo 626299 942167 := bstep (se 1 (by rfl) ⟨706625, by rfl⟩ : syracuseStep 942167 = 1413251) B1413251
theorem B2121821 : Blo 626299 2121821 := bstep (se 3 (by rfl) ⟨397841, by rfl⟩ : syracuseStep 2121821 = 795683) B795683
theorem B1269911 : Blo 626299 1269911 := bstep (se 1 (by rfl) ⟨952433, by rfl⟩ : syracuseStep 1269911 = 1904867) B1904867
theorem B16113815 : Blo 626299 16113815 := bstep (se 1 (by rfl) ⟨12085361, by rfl⟩ : syracuseStep 16113815 = 24170723) B24170723
theorem B942233 : Blo 626299 942233 := bstep (se 2 (by rfl) ⟨353337, by rfl⟩ : syracuseStep 942233 = 706675) B706675
theorem B1794251 : Blo 626299 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B942347 : Blo 626299 942347 := bstep (se 1 (by rfl) ⟨706760, by rfl⟩ : syracuseStep 942347 = 1413521) B1413521
theorem B942359 : Blo 626299 942359 := bstep (se 1 (by rfl) ⟨706769, by rfl⟩ : syracuseStep 942359 = 1413539) B1413539
theorem B942425 : Blo 626299 942425 := bstep (se 2 (by rfl) ⟨353409, by rfl⟩ : syracuseStep 942425 = 706819) B706819
theorem B1008011 : Blo 626299 1008011 := bstep (se 1 (by rfl) ⟨756008, by rfl⟩ : syracuseStep 1008011 = 1512017) B1512017
theorem B942539 : Blo 626299 942539 := bstep (se 1 (by rfl) ⟨706904, by rfl⟩ : syracuseStep 942539 = 1413809) B1413809
theorem B942551 : Blo 626299 942551 := bstep (se 1 (by rfl) ⟨706913, by rfl⟩ : syracuseStep 942551 = 1413827) B1413827
theorem B942617 : Blo 626299 942617 := bstep (se 2 (by rfl) ⟨353481, by rfl⟩ : syracuseStep 942617 = 706963) B706963
theorem B680567 : Blo 626299 680567 := bstep (se 1 (by rfl) ⟨510425, by rfl⟩ : syracuseStep 680567 = 1020851) B1020851
theorem B942731 : Blo 626299 942731 := bstep (se 1 (by rfl) ⟨707048, by rfl⟩ : syracuseStep 942731 = 1414097) B1414097
theorem B942743 : Blo 626299 942743 := bstep (se 1 (by rfl) ⟨707057, by rfl⟩ : syracuseStep 942743 = 1414115) B1414115
theorem B942809 : Blo 626299 942809 := bstep (se 2 (by rfl) ⟨353553, by rfl⟩ : syracuseStep 942809 = 707107) B707107
theorem B1434433 : Blo 626299 1434433 := bstep (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) B1075825
theorem B942923 : Blo 626299 942923 := bstep (se 1 (by rfl) ⟨707192, by rfl⟩ : syracuseStep 942923 = 1414385) B1414385
theorem B942935 : Blo 626299 942935 := bstep (se 1 (by rfl) ⟨707201, by rfl⟩ : syracuseStep 942935 = 1414403) B1414403
theorem B943001 : Blo 626299 943001 := bstep (se 2 (by rfl) ⟨353625, by rfl⟩ : syracuseStep 943001 = 707251) B707251
theorem B7168985 : Blo 626299 7168985 := bstep (se 2 (by rfl) ⟨2688369, by rfl⟩ : syracuseStep 7168985 = 5376739) B5376739
theorem B2548739 : Blo 626299 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B943115 : Blo 626299 943115 := bstep (se 1 (by rfl) ⟨707336, by rfl⟩ : syracuseStep 943115 = 1414673) B1414673
theorem B943127 : Blo 626299 943127 := bstep (se 1 (by rfl) ⟨707345, by rfl⟩ : syracuseStep 943127 = 1414691) B1414691
theorem B943193 : Blo 626299 943193 := bstep (se 2 (by rfl) ⟨353697, by rfl⟩ : syracuseStep 943193 = 707395) B707395
theorem B5104741 : Blo 626299 5104741 := bstep (se 4 (by rfl) ⟨478569, by rfl⟩ : syracuseStep 5104741 = 957139) B957139
theorem B943307 : Blo 626299 943307 := bstep (se 1 (by rfl) ⟨707480, by rfl⟩ : syracuseStep 943307 = 1414961) B1414961
theorem B2122955 : Blo 626299 2122955 := bstep (se 1 (by rfl) ⟨1592216, by rfl⟩ : syracuseStep 2122955 = 3184433) B3184433
theorem B943319 : Blo 626299 943319 := bstep (se 1 (by rfl) ⟨707489, by rfl⟩ : syracuseStep 943319 = 1414979) B1414979
theorem B1008857 : Blo 626299 1008857 := bstep (se 2 (by rfl) ⟨378321, by rfl⟩ : syracuseStep 1008857 = 756643) B756643
theorem B2680067 : Blo 626299 2680067 := bstep (se 1 (by rfl) ⟨2010050, by rfl⟩ : syracuseStep 2680067 = 4020101) B4020101
theorem B943385 : Blo 626299 943385 := bstep (se 2 (by rfl) ⟨353769, by rfl⟩ : syracuseStep 943385 = 707539) B707539
theorem B2385197 : Blo 626299 2385197 := bstep (se 3 (by rfl) ⟨447224, by rfl⟩ : syracuseStep 2385197 = 894449) B894449
theorem B2385227 : Blo 626299 2385227 := bstep (se 1 (by rfl) ⟨1788920, by rfl⟩ : syracuseStep 2385227 = 3577841) B3577841
theorem B943499 : Blo 626299 943499 := bstep (se 1 (by rfl) ⟨707624, by rfl⟩ : syracuseStep 943499 = 1415249) B1415249
theorem B943511 : Blo 626299 943511 := bstep (se 1 (by rfl) ⟨707633, by rfl⟩ : syracuseStep 943511 = 1415267) B1415267
theorem B1074649 : Blo 626299 1074649 := bstep (se 2 (by rfl) ⟨402993, by rfl⟩ : syracuseStep 1074649 = 805987) B805987
theorem B943577 : Blo 626299 943577 := bstep (se 2 (by rfl) ⟨353841, by rfl⟩ : syracuseStep 943577 = 707683) B707683
theorem B2123225 : Blo 626299 2123225 := bstep (se 2 (by rfl) ⟨796209, by rfl⟩ : syracuseStep 2123225 = 1592419) B1592419
theorem B1697345 : Blo 626299 1697345 := bstep (se 2 (by rfl) ⟨636504, by rfl⟩ : syracuseStep 1697345 = 1273009) B1273009
theorem B943691 : Blo 626299 943691 := bstep (se 1 (by rfl) ⟨707768, by rfl⟩ : syracuseStep 943691 = 1415537) B1415537
theorem B943703 : Blo 626299 943703 := bstep (se 1 (by rfl) ⟨707777, by rfl⟩ : syracuseStep 943703 = 1415555) B1415555
theorem B943769 : Blo 626299 943769 := bstep (se 2 (by rfl) ⟨353913, by rfl⟩ : syracuseStep 943769 = 707827) B707827
theorem B1009369 : Blo 626299 1009369 := bstep (se 2 (by rfl) ⟨378513, by rfl⟩ : syracuseStep 1009369 = 757027) B757027
theorem B943883 : Blo 626299 943883 := bstep (se 1 (by rfl) ⟨707912, by rfl⟩ : syracuseStep 943883 = 1415825) B1415825
theorem B943895 : Blo 626299 943895 := bstep (se 1 (by rfl) ⟨707921, by rfl⟩ : syracuseStep 943895 = 1415843) B1415843
theorem B943961 : Blo 626299 943961 := bstep (se 2 (by rfl) ⟨353985, by rfl⟩ : syracuseStep 943961 = 707971) B707971
theorem B944075 : Blo 626299 944075 := bstep (se 1 (by rfl) ⟨708056, by rfl⟩ : syracuseStep 944075 = 1416113) B1416113
theorem B944087 : Blo 626299 944087 := bstep (se 1 (by rfl) ⟨708065, by rfl⟩ : syracuseStep 944087 = 1416131) B1416131
theorem B2385881 : Blo 626299 2385881 := bstep (se 2 (by rfl) ⟨894705, by rfl⟩ : syracuseStep 2385881 = 1789411) B1789411
theorem B1075223 : Blo 626299 1075223 := bstep (se 1 (by rfl) ⟨806417, by rfl⟩ : syracuseStep 1075223 = 1612835) B1612835
theorem B944153 : Blo 626299 944153 := bstep (se 2 (by rfl) ⟨354057, by rfl⟩ : syracuseStep 944153 = 708115) B708115
theorem B1435673 : Blo 626299 1435673 := bstep (se 2 (by rfl) ⟨538377, by rfl⟩ : syracuseStep 1435673 = 1076755) B1076755
theorem B3172445 : Blo 626299 3172445 := bstep (se 3 (by rfl) ⟨594833, by rfl⟩ : syracuseStep 3172445 = 1189667) B1189667
theorem B944267 : Blo 626299 944267 := bstep (se 1 (by rfl) ⟨708200, by rfl⟩ : syracuseStep 944267 = 1416401) B1416401
theorem B2123927 : Blo 626299 2123927 := bstep (se 1 (by rfl) ⟨1592945, by rfl⟩ : syracuseStep 2123927 = 3185891) B3185891
theorem B944279 : Blo 626299 944279 := bstep (se 1 (by rfl) ⟨708209, by rfl⟩ : syracuseStep 944279 = 1416419) B1416419
theorem B944345 : Blo 626299 944345 := bstep (se 2 (by rfl) ⟨354129, by rfl⟩ : syracuseStep 944345 = 708259) B708259
theorem B2386199 : Blo 626299 2386199 := bstep (se 1 (by rfl) ⟨1789649, by rfl⟩ : syracuseStep 2386199 = 3579299) B3579299
theorem B944459 : Blo 626299 944459 := bstep (se 1 (by rfl) ⟨708344, by rfl⟩ : syracuseStep 944459 = 1416689) B1416689
theorem B944471 : Blo 626299 944471 := bstep (se 1 (by rfl) ⟨708353, by rfl⟩ : syracuseStep 944471 = 1416707) B1416707
theorem B944537 : Blo 626299 944537 := bstep (se 2 (by rfl) ⟨354201, by rfl⟩ : syracuseStep 944537 = 708403) B708403
theorem B1698251 : Blo 626299 1698251 := bstep (se 1 (by rfl) ⟨1273688, by rfl⟩ : syracuseStep 1698251 = 2547377) B2547377
theorem B944651 : Blo 626299 944651 := bstep (se 1 (by rfl) ⟨708488, by rfl⟩ : syracuseStep 944651 = 1416977) B1416977
theorem B2550295 : Blo 626299 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B944663 : Blo 626299 944663 := bstep (se 1 (by rfl) ⟨708497, by rfl⟩ : syracuseStep 944663 = 1416995) B1416995
theorem B944729 : Blo 626299 944729 := bstep (se 2 (by rfl) ⟨354273, by rfl⟩ : syracuseStep 944729 = 708547) B708547
theorem B2124467 : Blo 626299 2124467 := bstep (se 1 (by rfl) ⟨1593350, by rfl⟩ : syracuseStep 2124467 = 3186701) B3186701
theorem B944843 : Blo 626299 944843 := bstep (se 1 (by rfl) ⟨708632, by rfl⟩ : syracuseStep 944843 = 1417265) B1417265
theorem B944855 : Blo 626299 944855 := bstep (se 1 (by rfl) ⟨708641, by rfl⟩ : syracuseStep 944855 = 1417283) B1417283
theorem B846617 : Blo 626299 846617 := bstep (se 2 (by rfl) ⟨317481, by rfl⟩ : syracuseStep 846617 = 634963) B634963
theorem B1338137 : Blo 626299 1338137 := bstep (se 2 (by rfl) ⟨501801, by rfl⟩ : syracuseStep 1338137 = 1003603) B1003603
theorem B944921 : Blo 626299 944921 := bstep (se 2 (by rfl) ⟨354345, by rfl⟩ : syracuseStep 944921 = 708691) B708691
theorem B5106563 : Blo 626299 5106563 := bstep (se 1 (by rfl) ⟨3829922, by rfl⟩ : syracuseStep 5106563 = 7659845) B7659845
theorem B945035 : Blo 626299 945035 := bstep (se 1 (by rfl) ⟨708776, by rfl⟩ : syracuseStep 945035 = 1417553) B1417553
theorem B945047 : Blo 626299 945047 := bstep (se 1 (by rfl) ⟨708785, by rfl⟩ : syracuseStep 945047 = 1417571) B1417571
theorem B2386867 : Blo 626299 2386867 := bstep (se 1 (by rfl) ⟨1790150, by rfl⟩ : syracuseStep 2386867 = 3580301) B3580301
theorem B2124737 : Blo 626299 2124737 := bstep (se 2 (by rfl) ⟨796776, by rfl⟩ : syracuseStep 2124737 = 1593553) B1593553
theorem B945113 : Blo 626299 945113 := bstep (se 2 (by rfl) ⟨354417, by rfl⟩ : syracuseStep 945113 = 708835) B708835
theorem B945227 : Blo 626299 945227 := bstep (se 1 (by rfl) ⟨708920, by rfl⟩ : syracuseStep 945227 = 1417841) B1417841
theorem B945239 : Blo 626299 945239 := bstep (se 1 (by rfl) ⟨708929, by rfl⟩ : syracuseStep 945239 = 1417859) B1417859
theorem B2583683 : Blo 626299 2583683 := bstep (se 1 (by rfl) ⟨1937762, by rfl⟩ : syracuseStep 2583683 = 3875525) B3875525
theorem B945305 : Blo 626299 945305 := bstep (se 2 (by rfl) ⟨354489, by rfl⟩ : syracuseStep 945305 = 708979) B708979
theorem B2714797 : Blo 626299 2714797 := bstep (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) B1018049
theorem B1338547 : Blo 626299 1338547 := bstep (se 1 (by rfl) ⟨1003910, by rfl⟩ : syracuseStep 1338547 = 2007821) B2007821
theorem B945419 : Blo 626299 945419 := bstep (se 1 (by rfl) ⟨709064, by rfl⟩ : syracuseStep 945419 = 1418129) B1418129
theorem B945431 : Blo 626299 945431 := bstep (se 1 (by rfl) ⟨709073, by rfl⟩ : syracuseStep 945431 = 1418147) B1418147
theorem B2125277 : Blo 626299 2125277 := bstep (se 3 (by rfl) ⟨398489, by rfl⟩ : syracuseStep 2125277 = 796979) B796979
theorem B3567179 : Blo 626299 3567179 := bstep (se 1 (by rfl) ⟨2675384, by rfl⟩ : syracuseStep 3567179 = 5350769) B5350769
theorem B1273495 : Blo 626299 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B1863575 : Blo 626299 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B1699787 : Blo 626299 1699787 := bstep (se 1 (by rfl) ⟨1274840, by rfl⟩ : syracuseStep 1699787 = 2549681) B2549681
theorem B2388113 : Blo 626299 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B3174551 : Blo 626299 3174551 := bstep (se 1 (by rfl) ⟨2380913, by rfl⟩ : syracuseStep 3174551 = 4761827) B4761827
theorem B1339735 : Blo 626299 1339735 := bstep (se 1 (by rfl) ⟨1004801, by rfl⟩ : syracuseStep 1339735 = 2009603) B2009603
theorem B1339777 : Blo 626299 1339777 := bstep (se 2 (by rfl) ⟨502416, by rfl⟩ : syracuseStep 1339777 = 1004833) B1004833
theorem B2126411 : Blo 626299 2126411 := bstep (se 1 (by rfl) ⟨1594808, by rfl⟩ : syracuseStep 2126411 = 3189617) B3189617
theorem B2388811 : Blo 626299 2388811 := bstep (se 1 (by rfl) ⟨1791608, by rfl⟩ : syracuseStep 2388811 = 3583217) B3583217
theorem B2126681 : Blo 626299 2126681 := bstep (se 2 (by rfl) ⟨797505, by rfl⟩ : syracuseStep 2126681 = 1595011) B1595011
theorem B5370725 : Blo 626299 5370725 := bstep (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) B1007011
theorem B10711925 : Blo 626299 10711925 := bstep (se 5 (by rfl) ⟨502121, by rfl⟩ : syracuseStep 10711925 = 1004243) B1004243
theorem B2389085 : Blo 626299 2389085 := bstep (se 3 (by rfl) ⟨447953, by rfl⟩ : syracuseStep 2389085 = 895907) B895907
theorem B3568819 : Blo 626299 3568819 := bstep (se 1 (by rfl) ⟨2676614, by rfl⟩ : syracuseStep 3568819 = 5353229) B5353229
theorem B10220899 : Blo 626299 10220899 := bstep (se 1 (by rfl) ⟨7665674, by rfl⟩ : syracuseStep 10220899 = 15331349) B15331349
theorem B2684339 : Blo 626299 2684339 := bstep (se 1 (by rfl) ⟨2013254, by rfl⟩ : syracuseStep 2684339 = 4026509) B4026509
theorem B849547 : Blo 626299 849547 := bstep (se 1 (by rfl) ⟨637160, by rfl⟩ : syracuseStep 849547 = 1274321) B1274321
theorem B1275635 : Blo 626299 1275635 := bstep (se 1 (by rfl) ⟨956726, by rfl⟩ : syracuseStep 1275635 = 1913453) B1913453
theorem B2389783 : Blo 626299 2389783 := bstep (se 1 (by rfl) ⟨1792337, by rfl⟩ : syracuseStep 2389783 = 3584675) B3584675
theorem B2455427 : Blo 626299 2455427 := bstep (se 1 (by rfl) ⟨1841570, by rfl⟩ : syracuseStep 2455427 = 3683141) B3683141
theorem B1341451 : Blo 626299 1341451 := bstep (se 1 (by rfl) ⟨1006088, by rfl⟩ : syracuseStep 1341451 = 2012177) B2012177
theorem B3012653 : Blo 626299 3012653 := bstep (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) B1129745
theorem B9173197 : Blo 626299 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B1341785 : Blo 626299 1341785 := bstep (se 2 (by rfl) ⟨503169, by rfl⟩ : syracuseStep 1341785 = 1006339) B1006339
theorem B5372365 : Blo 626299 5372365 := bstep (se 3 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 5372365 = 2014637) B2014637
theorem B2390573 : Blo 626299 2390573 := bstep (se 3 (by rfl) ⟨448232, by rfl⟩ : syracuseStep 2390573 = 896465) B896465
theorem B16153181 : Blo 626299 16153181 := bstep (se 3 (by rfl) ⟨3028721, by rfl⟩ : syracuseStep 16153181 = 6057443) B6057443
theorem B3570277 : Blo 626299 3570277 := bstep (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) B669427
theorem B5438339 : Blo 626299 5438339 := bstep (se 1 (by rfl) ⟨4078754, by rfl⟩ : syracuseStep 5438339 = 8157509) B8157509
theorem B1506251 : Blo 626299 1506251 := bstep (se 1 (by rfl) ⟨1129688, by rfl⟩ : syracuseStep 1506251 = 2259377) B2259377
theorem B4029533 : Blo 626299 4029533 := bstep (se 3 (by rfl) ⟨755537, by rfl⟩ : syracuseStep 4029533 = 1511075) B1511075
theorem B3636355 : Blo 626299 3636355 := bstep (se 1 (by rfl) ⟨2727266, by rfl⟩ : syracuseStep 3636355 = 5454533) B5454533
theorem B14548373 : Blo 626299 14548373 := bstep (se 6 (by rfl) ⟨340977, by rfl⟩ : syracuseStep 14548373 = 681955) B681955
theorem B1703389 : Blo 626299 1703389 := bstep (se 3 (by rfl) ⟨319385, by rfl⟩ : syracuseStep 1703389 = 638771) B638771
theorem B1211927 : Blo 626299 1211927 := bstep (se 1 (by rfl) ⟨908945, by rfl⟩ : syracuseStep 1211927 = 1817891) B1817891
theorem B7241309 : Blo 626299 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B3178115 : Blo 626299 3178115 := bstep (se 1 (by rfl) ⟨2383586, by rfl⟩ : syracuseStep 3178115 = 4767173) B4767173
theorem B5373701 : Blo 626299 5373701 := bstep (se 4 (by rfl) ⟨503784, by rfl⟩ : syracuseStep 5373701 = 1007569) B1007569
theorem B1343297 : Blo 626299 1343297 := bstep (se 2 (by rfl) ⟨503736, by rfl⟩ : syracuseStep 1343297 = 1007473) B1007473
theorem B2392001 : Blo 626299 2392001 := bstep (se 2 (by rfl) ⟨897000, by rfl⟩ : syracuseStep 2392001 = 1794001) B1794001
theorem B3571735 : Blo 626299 3571735 := bstep (se 1 (by rfl) ⟨2678801, by rfl⟩ : syracuseStep 3571735 = 5357603) B5357603
theorem B917563 : Blo 626299 917563 := bstep (se 1 (by rfl) ⟨688172, by rfl⟩ : syracuseStep 917563 = 1376345) B1376345
theorem B1507481 : Blo 626299 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B1409399 : Blo 626299 1409399 := bstep (se 1 (by rfl) ⟨1057049, by rfl⟩ : syracuseStep 1409399 = 2114099) B2114099
theorem B4784669 : Blo 626299 4784669 := bstep (se 3 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 4784669 = 1794251) B1794251
theorem B1409579 : Blo 626299 1409579 := bstep (se 1 (by rfl) ⟨1057184, by rfl⟩ : syracuseStep 1409579 = 2114369) B2114369
theorem B1344271 : Blo 626299 1344271 := bstep (se 1 (by rfl) ⟨1008203, by rfl⟩ : syracuseStep 1344271 = 2016407) B2016407
theorem B3015539 : Blo 626299 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B6456179 : Blo 626299 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B1639283 : Blo 626299 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B1409939 : Blo 626299 1409939 := bstep (se 1 (by rfl) ⟨1057454, by rfl⟩ : syracuseStep 1409939 = 2114909) B2114909
theorem B3179411 : Blo 626299 3179411 := bstep (se 1 (by rfl) ⟨2384558, by rfl⟩ : syracuseStep 3179411 = 4769117) B4769117
theorem B1409993 : Blo 626299 1409993 := bstep (se 2 (by rfl) ⟨528747, by rfl⟩ : syracuseStep 1409993 = 1057495) B1057495
theorem B1344527 : Blo 626299 1344527 := bstep (se 1 (by rfl) ⟨1008395, by rfl⟩ : syracuseStep 1344527 = 2016791) B2016791
theorem B2688029 : Blo 626299 2688029 := bstep (se 3 (by rfl) ⟨504005, by rfl⟩ : syracuseStep 2688029 = 1008011) B1008011
theorem B754951 : Blo 626299 754951 := bstep (se 1 (by rfl) ⟨566213, by rfl⟩ : syracuseStep 754951 = 1132427) B1132427
theorem B27198989 : Blo 626299 27198989 := bstep (se 3 (by rfl) ⟨5099810, by rfl⟩ : syracuseStep 27198989 = 10199621) B10199621
theorem B1410695 : Blo 626299 1410695 := bstep (se 1 (by rfl) ⟨1058021, by rfl⟩ : syracuseStep 1410695 = 2116043) B2116043
theorem B2688713 : Blo 626299 2688713 := bstep (se 2 (by rfl) ⟨1008267, by rfl⟩ : syracuseStep 2688713 = 2016535) B2016535
theorem B1410875 : Blo 626299 1410875 := bstep (se 1 (by rfl) ⟨1058156, by rfl⟩ : syracuseStep 1410875 = 2116313) B2116313
theorem B1345339 : Blo 626299 1345339 := bstep (se 1 (by rfl) ⟨1009004, by rfl⟩ : syracuseStep 1345339 = 2018009) B2018009
theorem B1345415 : Blo 626299 1345415 := bstep (se 1 (by rfl) ⟨1009061, by rfl⟩ : syracuseStep 1345415 = 2018123) B2018123
theorem B1411001 : Blo 626299 1411001 := bstep (se 2 (by rfl) ⟨529125, by rfl⟩ : syracuseStep 1411001 = 1058251) B1058251
theorem B6522967 : Blo 626299 6522967 := bstep (se 1 (by rfl) ⟨4892225, by rfl⟩ : syracuseStep 6522967 = 9784451) B9784451
theorem B755831 : Blo 626299 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B1345655 : Blo 626299 1345655 := bstep (se 1 (by rfl) ⟨1009241, by rfl⟩ : syracuseStep 1345655 = 2018483) B2018483
theorem B1411343 : Blo 626299 1411343 := bstep (se 1 (by rfl) ⟨1058507, by rfl⟩ : syracuseStep 1411343 = 2117015) B2117015
theorem B1411361 : Blo 626299 1411361 := bstep (se 2 (by rfl) ⟨529260, by rfl⟩ : syracuseStep 1411361 = 1058521) B1058521
theorem B1345825 : Blo 626299 1345825 := bstep (se 2 (by rfl) ⟨504684, by rfl⟩ : syracuseStep 1345825 = 1009369) B1009369
theorem B1509691 : Blo 626299 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B3574151 : Blo 626299 3574151 := bstep (se 1 (by rfl) ⟨2680613, by rfl⟩ : syracuseStep 3574151 = 5361227) B5361227
theorem B1411703 : Blo 626299 1411703 := bstep (se 1 (by rfl) ⟨1058777, by rfl⟩ : syracuseStep 1411703 = 2117555) B2117555
theorem B1411883 : Blo 626299 1411883 := bstep (se 1 (by rfl) ⟨1058912, by rfl⟩ : syracuseStep 1411883 = 2117825) B2117825
theorem B1412243 : Blo 626299 1412243 := bstep (se 1 (by rfl) ⟨1059182, by rfl⟩ : syracuseStep 1412243 = 2118365) B2118365
theorem B756907 : Blo 626299 756907 := bstep (se 1 (by rfl) ⟨567680, by rfl⟩ : syracuseStep 756907 = 1135361) B1135361
theorem B1412297 : Blo 626299 1412297 := bstep (se 2 (by rfl) ⟨529611, by rfl⟩ : syracuseStep 1412297 = 1059223) B1059223
theorem B3017999 : Blo 626299 3017999 := bstep (se 1 (by rfl) ⟨2263499, by rfl⟩ : syracuseStep 3017999 = 4526999) B4526999
theorem B10751291 : Blo 626299 10751291 := bstep (se 1 (by rfl) ⟨8063468, by rfl⟩ : syracuseStep 10751291 = 16126937) B16126937
theorem B2690489 : Blo 626299 2690489 := bstep (se 2 (by rfl) ⟨1008933, by rfl⟩ : syracuseStep 2690489 = 2017867) B2017867
theorem B626311 : Blo 626299 626311 := bstep (se 1 (by rfl) ⟨469733, by rfl⟩ : syracuseStep 626311 = 939467) B939467
theorem B626319 : Blo 626299 626319 := bstep (se 1 (by rfl) ⟨469739, by rfl⟩ : syracuseStep 626319 = 939479) B939479
theorem B626363 : Blo 626299 626363 := bstep (se 1 (by rfl) ⟨469772, by rfl⟩ : syracuseStep 626363 = 939545) B939545
theorem B6033113 : Blo 626299 6033113 := bstep (se 2 (by rfl) ⟨2262417, by rfl⟩ : syracuseStep 6033113 = 4524835) B4524835
theorem B626439 : Blo 626299 626439 := bstep (se 1 (by rfl) ⟨469829, by rfl⟩ : syracuseStep 626439 = 939659) B939659
theorem B626447 : Blo 626299 626447 := bstep (se 1 (by rfl) ⟨469835, by rfl⟩ : syracuseStep 626447 = 939671) B939671
theorem B626491 : Blo 626299 626491 := bstep (se 1 (by rfl) ⟨469868, by rfl⟩ : syracuseStep 626491 = 939737) B939737
theorem B1609591 : Blo 626299 1609591 := bstep (se 1 (by rfl) ⟨1207193, by rfl⟩ : syracuseStep 1609591 = 2414387) B2414387
theorem B626567 : Blo 626299 626567 := bstep (se 1 (by rfl) ⟨469925, by rfl⟩ : syracuseStep 626567 = 939851) B939851
theorem B1412999 : Blo 626299 1412999 := bstep (se 1 (by rfl) ⟨1059749, by rfl⟩ : syracuseStep 1412999 = 2119499) B2119499
theorem B626575 : Blo 626299 626575 := bstep (se 1 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 626575 = 939863) B939863
theorem B3182489 : Blo 626299 3182489 := bstep (se 2 (by rfl) ⟨1193433, by rfl⟩ : syracuseStep 3182489 = 2386867) B2386867
theorem B626619 : Blo 626299 626619 := bstep (se 1 (by rfl) ⟨469964, by rfl⟩ : syracuseStep 626619 = 939929) B939929
theorem B626695 : Blo 626299 626695 := bstep (se 1 (by rfl) ⟨470021, by rfl⟩ : syracuseStep 626695 = 940043) B940043
theorem B626703 : Blo 626299 626703 := bstep (se 1 (by rfl) ⟨470027, by rfl⟩ : syracuseStep 626703 = 940055) B940055
theorem B3182635 : Blo 626299 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B626747 : Blo 626299 626747 := bstep (se 1 (by rfl) ⟨470060, by rfl⟩ : syracuseStep 626747 = 940121) B940121
theorem B1413179 : Blo 626299 1413179 := bstep (se 1 (by rfl) ⟨1059884, by rfl⟩ : syracuseStep 1413179 = 2119769) B2119769
theorem B3575927 : Blo 626299 3575927 := bstep (se 1 (by rfl) ⟨2681945, by rfl⟩ : syracuseStep 3575927 = 5363891) B5363891
theorem B626823 : Blo 626299 626823 := bstep (se 1 (by rfl) ⟨470117, by rfl⟩ : syracuseStep 626823 = 940235) B940235
theorem B626831 : Blo 626299 626831 := bstep (se 1 (by rfl) ⟨470123, by rfl⟩ : syracuseStep 626831 = 940247) B940247
theorem B1413305 : Blo 626299 1413305 := bstep (se 2 (by rfl) ⟨529989, by rfl⟩ : syracuseStep 1413305 = 1059979) B1059979
theorem B626875 : Blo 626299 626875 := bstep (se 1 (by rfl) ⟨470156, by rfl⟩ : syracuseStep 626875 = 940313) B940313
theorem B24875209 : Blo 626299 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B626951 : Blo 626299 626951 := bstep (se 1 (by rfl) ⟨470213, by rfl⟩ : syracuseStep 626951 = 940427) B940427
theorem B626959 : Blo 626299 626959 := bstep (se 1 (by rfl) ⟨470219, by rfl⟩ : syracuseStep 626959 = 940439) B940439
theorem B627003 : Blo 626299 627003 := bstep (se 1 (by rfl) ⟨470252, by rfl⟩ : syracuseStep 627003 = 940505) B940505
theorem B627079 : Blo 626299 627079 := bstep (se 1 (by rfl) ⟨470309, by rfl⟩ : syracuseStep 627079 = 940619) B940619
theorem B627087 : Blo 626299 627087 := bstep (se 1 (by rfl) ⟨470315, by rfl⟩ : syracuseStep 627087 = 940631) B940631
theorem B627131 : Blo 626299 627131 := bstep (se 1 (by rfl) ⟨470348, by rfl⟩ : syracuseStep 627131 = 940697) B940697
theorem B627207 : Blo 626299 627207 := bstep (se 1 (by rfl) ⟨470405, by rfl⟩ : syracuseStep 627207 = 940811) B940811
theorem B627215 : Blo 626299 627215 := bstep (se 1 (by rfl) ⟨470411, by rfl⟩ : syracuseStep 627215 = 940823) B940823
theorem B1413647 : Blo 626299 1413647 := bstep (se 1 (by rfl) ⟨1060235, by rfl⟩ : syracuseStep 1413647 = 2120471) B2120471
theorem B1413665 : Blo 626299 1413665 := bstep (se 2 (by rfl) ⟨530124, by rfl⟩ : syracuseStep 1413665 = 1060249) B1060249
theorem B627259 : Blo 626299 627259 := bstep (se 1 (by rfl) ⟨470444, by rfl⟩ : syracuseStep 627259 = 940889) B940889
theorem B627335 : Blo 626299 627335 := bstep (se 1 (by rfl) ⟨470501, by rfl⟩ : syracuseStep 627335 = 941003) B941003
theorem B627343 : Blo 626299 627343 := bstep (se 1 (by rfl) ⟨470507, by rfl⟩ : syracuseStep 627343 = 941015) B941015
theorem B627387 : Blo 626299 627387 := bstep (se 1 (by rfl) ⟨470540, by rfl⟩ : syracuseStep 627387 = 941081) B941081
theorem B627463 : Blo 626299 627463 := bstep (se 1 (by rfl) ⟨470597, by rfl⟩ : syracuseStep 627463 = 941195) B941195
theorem B627471 : Blo 626299 627471 := bstep (se 1 (by rfl) ⟨470603, by rfl⟩ : syracuseStep 627471 = 941207) B941207
theorem B5083955 : Blo 626299 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B627515 : Blo 626299 627515 := bstep (se 1 (by rfl) ⟨470636, by rfl⟩ : syracuseStep 627515 = 941273) B941273
theorem B3576635 : Blo 626299 3576635 := bstep (se 1 (by rfl) ⟨2682476, by rfl⟩ : syracuseStep 3576635 = 5364953) B5364953
theorem B1414007 : Blo 626299 1414007 := bstep (se 1 (by rfl) ⟨1060505, by rfl⟩ : syracuseStep 1414007 = 2121011) B2121011
theorem B627591 : Blo 626299 627591 := bstep (se 1 (by rfl) ⟨470693, by rfl⟩ : syracuseStep 627591 = 941387) B941387
theorem B627599 : Blo 626299 627599 := bstep (se 1 (by rfl) ⟨470699, by rfl⟩ : syracuseStep 627599 = 941399) B941399
theorem B627643 : Blo 626299 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B627719 : Blo 626299 627719 := bstep (se 1 (by rfl) ⟨470789, by rfl⟩ : syracuseStep 627719 = 941579) B941579
theorem B627727 : Blo 626299 627727 := bstep (se 1 (by rfl) ⟨470795, by rfl⟩ : syracuseStep 627727 = 941591) B941591
theorem B1414187 : Blo 626299 1414187 := bstep (se 1 (by rfl) ⟨1060640, by rfl⟩ : syracuseStep 1414187 = 2121281) B2121281
theorem B627771 : Blo 626299 627771 := bstep (se 1 (by rfl) ⟨470828, by rfl⟩ : syracuseStep 627771 = 941657) B941657
theorem B627847 : Blo 626299 627847 := bstep (se 1 (by rfl) ⟨470885, by rfl⟩ : syracuseStep 627847 = 941771) B941771
theorem B627855 : Blo 626299 627855 := bstep (se 1 (by rfl) ⟨470891, by rfl⟩ : syracuseStep 627855 = 941783) B941783
theorem B627899 : Blo 626299 627899 := bstep (se 1 (by rfl) ⟨470924, by rfl⟩ : syracuseStep 627899 = 941849) B941849
theorem B627975 : Blo 626299 627975 := bstep (se 1 (by rfl) ⟨470981, by rfl⟩ : syracuseStep 627975 = 941963) B941963
theorem B627983 : Blo 626299 627983 := bstep (se 1 (by rfl) ⟨470987, by rfl⟩ : syracuseStep 627983 = 941975) B941975
theorem B628027 : Blo 626299 628027 := bstep (se 1 (by rfl) ⟨471020, by rfl⟩ : syracuseStep 628027 = 942041) B942041
theorem B628103 : Blo 626299 628103 := bstep (se 1 (by rfl) ⟨471077, by rfl⟩ : syracuseStep 628103 = 942155) B942155
theorem B628111 : Blo 626299 628111 := bstep (se 1 (by rfl) ⟨471083, by rfl⟩ : syracuseStep 628111 = 942167) B942167
theorem B5379473 : Blo 626299 5379473 := bstep (se 2 (by rfl) ⟨2017302, by rfl⟩ : syracuseStep 5379473 = 4034605) B4034605
theorem B1414547 : Blo 626299 1414547 := bstep (se 1 (by rfl) ⟨1060910, by rfl⟩ : syracuseStep 1414547 = 2121821) B2121821
theorem B628155 : Blo 626299 628155 := bstep (se 1 (by rfl) ⟨471116, by rfl⟩ : syracuseStep 628155 = 942233) B942233
theorem B1414601 : Blo 626299 1414601 := bstep (se 2 (by rfl) ⟨530475, by rfl⟩ : syracuseStep 1414601 = 1060951) B1060951
theorem B8033741 : Blo 626299 8033741 := bstep (se 3 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 8033741 = 3012653) B3012653
theorem B628231 : Blo 626299 628231 := bstep (se 1 (by rfl) ⟨471173, by rfl⟩ : syracuseStep 628231 = 942347) B942347
theorem B628239 : Blo 626299 628239 := bstep (se 1 (by rfl) ⟨471179, by rfl⟩ : syracuseStep 628239 = 942359) B942359
theorem B628283 : Blo 626299 628283 := bstep (se 1 (by rfl) ⟨471212, by rfl⟩ : syracuseStep 628283 = 942425) B942425
theorem B628359 : Blo 626299 628359 := bstep (se 1 (by rfl) ⟨471269, by rfl⟩ : syracuseStep 628359 = 942539) B942539
theorem B628367 : Blo 626299 628367 := bstep (se 1 (by rfl) ⟨471275, by rfl⟩ : syracuseStep 628367 = 942551) B942551
theorem B628411 : Blo 626299 628411 := bstep (se 1 (by rfl) ⟨471308, by rfl⟩ : syracuseStep 628411 = 942617) B942617
theorem B628487 : Blo 626299 628487 := bstep (se 1 (by rfl) ⟨471365, by rfl⟩ : syracuseStep 628487 = 942731) B942731
theorem B628495 : Blo 626299 628495 := bstep (se 1 (by rfl) ⟨471371, by rfl⟩ : syracuseStep 628495 = 942743) B942743
theorem B628539 : Blo 626299 628539 := bstep (se 1 (by rfl) ⟨471404, by rfl⟩ : syracuseStep 628539 = 942809) B942809
theorem B628615 : Blo 626299 628615 := bstep (se 1 (by rfl) ⟨471461, by rfl⟩ : syracuseStep 628615 = 942923) B942923
theorem B628623 : Blo 626299 628623 := bstep (se 1 (by rfl) ⟨471467, by rfl⟩ : syracuseStep 628623 = 942935) B942935
theorem B628667 : Blo 626299 628667 := bstep (se 1 (by rfl) ⟨471500, by rfl⟩ : syracuseStep 628667 = 943001) B943001
theorem B628743 : Blo 626299 628743 := bstep (se 1 (by rfl) ⟨471557, by rfl⟩ : syracuseStep 628743 = 943115) B943115
theorem B628751 : Blo 626299 628751 := bstep (se 1 (by rfl) ⟨471563, by rfl⟩ : syracuseStep 628751 = 943127) B943127
theorem B628795 : Blo 626299 628795 := bstep (se 1 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 628795 = 943193) B943193
theorem B628871 : Blo 626299 628871 := bstep (se 1 (by rfl) ⟨471653, by rfl⟩ : syracuseStep 628871 = 943307) B943307
theorem B1415303 : Blo 626299 1415303 := bstep (se 1 (by rfl) ⟨1061477, by rfl⟩ : syracuseStep 1415303 = 2122955) B2122955
theorem B628879 : Blo 626299 628879 := bstep (se 1 (by rfl) ⟨471659, by rfl⟩ : syracuseStep 628879 = 943319) B943319
theorem B628923 : Blo 626299 628923 := bstep (se 1 (by rfl) ⟨471692, by rfl⟩ : syracuseStep 628923 = 943385) B943385
theorem B3578093 : Blo 626299 3578093 := bstep (se 3 (by rfl) ⟨670892, by rfl⟩ : syracuseStep 3578093 = 1341785) B1341785
theorem B792823 : Blo 626299 792823 := bstep (se 1 (by rfl) ⟨594617, by rfl⟩ : syracuseStep 792823 = 1189235) B1189235
theorem B628999 : Blo 626299 628999 := bstep (se 1 (by rfl) ⟨471749, by rfl⟩ : syracuseStep 628999 = 943499) B943499
theorem B629007 : Blo 626299 629007 := bstep (se 1 (by rfl) ⟨471755, by rfl⟩ : syracuseStep 629007 = 943511) B943511
theorem B629051 : Blo 626299 629051 := bstep (se 1 (by rfl) ⟨471788, by rfl⟩ : syracuseStep 629051 = 943577) B943577
theorem B1415483 : Blo 626299 1415483 := bstep (se 1 (by rfl) ⟨1061612, by rfl⟩ : syracuseStep 1415483 = 2123225) B2123225
theorem B629127 : Blo 626299 629127 := bstep (se 1 (by rfl) ⟨471845, by rfl⟩ : syracuseStep 629127 = 943691) B943691
theorem B629135 : Blo 626299 629135 := bstep (se 1 (by rfl) ⟨471851, by rfl⟩ : syracuseStep 629135 = 943703) B943703
theorem B3185081 : Blo 626299 3185081 := bstep (se 2 (by rfl) ⟨1194405, by rfl⟩ : syracuseStep 3185081 = 2388811) B2388811
theorem B1415609 : Blo 626299 1415609 := bstep (se 2 (by rfl) ⟨530853, by rfl⟩ : syracuseStep 1415609 = 1061707) B1061707
theorem B629179 : Blo 626299 629179 := bstep (se 1 (by rfl) ⟨471884, by rfl⟩ : syracuseStep 629179 = 943769) B943769
theorem B1907201 : Blo 626299 1907201 := bstep (se 2 (by rfl) ⟨715200, by rfl⟩ : syracuseStep 1907201 = 1430401) B1430401
theorem B629255 : Blo 626299 629255 := bstep (se 1 (by rfl) ⟨471941, by rfl⟩ : syracuseStep 629255 = 943883) B943883
theorem B629263 : Blo 626299 629263 := bstep (se 1 (by rfl) ⟨471947, by rfl⟩ : syracuseStep 629263 = 943895) B943895
theorem B4528669 : Blo 626299 4528669 := bstep (se 3 (by rfl) ⟨849125, by rfl⟩ : syracuseStep 4528669 = 1698251) B1698251
theorem B793147 : Blo 626299 793147 := bstep (se 1 (by rfl) ⟨594860, by rfl⟩ : syracuseStep 793147 = 1189721) B1189721
theorem B629307 : Blo 626299 629307 := bstep (se 1 (by rfl) ⟨471980, by rfl⟩ : syracuseStep 629307 = 943961) B943961
theorem B1448567 : Blo 626299 1448567 := bstep (se 1 (by rfl) ⟨1086425, by rfl⟩ : syracuseStep 1448567 = 2172851) B2172851
theorem B629383 : Blo 626299 629383 := bstep (se 1 (by rfl) ⟨472037, by rfl⟩ : syracuseStep 629383 = 944075) B944075
theorem B629391 : Blo 626299 629391 := bstep (se 1 (by rfl) ⟨472043, by rfl⟩ : syracuseStep 629391 = 944087) B944087
theorem B629435 : Blo 626299 629435 := bstep (se 1 (by rfl) ⟨472076, by rfl⟩ : syracuseStep 629435 = 944153) B944153
theorem B957115 : Blo 626299 957115 := bstep (se 1 (by rfl) ⟨717836, by rfl⟩ : syracuseStep 957115 = 1435673) B1435673
theorem B629511 : Blo 626299 629511 := bstep (se 1 (by rfl) ⟨472133, by rfl⟩ : syracuseStep 629511 = 944267) B944267
theorem B1415951 : Blo 626299 1415951 := bstep (se 1 (by rfl) ⟨1061963, by rfl⟩ : syracuseStep 1415951 = 2123927) B2123927
theorem B629519 : Blo 626299 629519 := bstep (se 1 (by rfl) ⟨472139, by rfl⟩ : syracuseStep 629519 = 944279) B944279
theorem B1415969 : Blo 626299 1415969 := bstep (se 2 (by rfl) ⟨530988, by rfl⟩ : syracuseStep 1415969 = 1061977) B1061977
theorem B629563 : Blo 626299 629563 := bstep (se 1 (by rfl) ⟨472172, by rfl⟩ : syracuseStep 629563 = 944345) B944345
theorem B629639 : Blo 626299 629639 := bstep (se 1 (by rfl) ⟨472229, by rfl⟩ : syracuseStep 629639 = 944459) B944459
theorem B629647 : Blo 626299 629647 := bstep (se 1 (by rfl) ⟨472235, by rfl⟩ : syracuseStep 629647 = 944471) B944471
theorem B4758425 : Blo 626299 4758425 := bstep (se 2 (by rfl) ⟨1784409, by rfl⟩ : syracuseStep 4758425 = 3568819) B3568819
theorem B629691 : Blo 626299 629691 := bstep (se 1 (by rfl) ⟨472268, by rfl⟩ : syracuseStep 629691 = 944537) B944537
theorem B629767 : Blo 626299 629767 := bstep (se 1 (by rfl) ⟨472325, by rfl⟩ : syracuseStep 629767 = 944651) B944651
theorem B629775 : Blo 626299 629775 := bstep (se 1 (by rfl) ⟨472331, by rfl⟩ : syracuseStep 629775 = 944663) B944663
theorem B629819 : Blo 626299 629819 := bstep (se 1 (by rfl) ⟨472364, by rfl⟩ : syracuseStep 629819 = 944729) B944729
theorem B891977 : Blo 626299 891977 := bstep (se 2 (by rfl) ⟨334491, by rfl⟩ : syracuseStep 891977 = 668983) B668983
theorem B1416311 : Blo 626299 1416311 := bstep (se 1 (by rfl) ⟨1062233, by rfl⟩ : syracuseStep 1416311 = 2124467) B2124467
theorem B629895 : Blo 626299 629895 := bstep (se 1 (by rfl) ⟨472421, by rfl⟩ : syracuseStep 629895 = 944843) B944843
theorem B629903 : Blo 626299 629903 := bstep (se 1 (by rfl) ⟨472427, by rfl⟩ : syracuseStep 629903 = 944855) B944855
theorem B892091 : Blo 626299 892091 := bstep (se 1 (by rfl) ⟨669068, by rfl⟩ : syracuseStep 892091 = 1338137) B1338137
theorem B629947 : Blo 626299 629947 := bstep (se 1 (by rfl) ⟨472460, by rfl⟩ : syracuseStep 629947 = 944921) B944921
theorem B630023 : Blo 626299 630023 := bstep (se 1 (by rfl) ⟨472517, by rfl⟩ : syracuseStep 630023 = 945035) B945035
theorem B630031 : Blo 626299 630031 := bstep (se 1 (by rfl) ⟨472523, by rfl⟩ : syracuseStep 630031 = 945047) B945047
theorem B1416491 : Blo 626299 1416491 := bstep (se 1 (by rfl) ⟨1062368, by rfl⟩ : syracuseStep 1416491 = 2124737) B2124737
theorem B630075 : Blo 626299 630075 := bstep (se 1 (by rfl) ⟨472556, by rfl⟩ : syracuseStep 630075 = 945113) B945113
theorem B630151 : Blo 626299 630151 := bstep (se 1 (by rfl) ⟨472613, by rfl⟩ : syracuseStep 630151 = 945227) B945227
theorem B630159 : Blo 626299 630159 := bstep (se 1 (by rfl) ⟨472619, by rfl⟩ : syracuseStep 630159 = 945239) B945239
theorem B630203 : Blo 626299 630203 := bstep (se 1 (by rfl) ⟨472652, by rfl⟩ : syracuseStep 630203 = 945305) B945305
theorem B794119 : Blo 626299 794119 := bstep (se 1 (by rfl) ⟨595589, by rfl⟩ : syracuseStep 794119 = 1191179) B1191179
theorem B630279 : Blo 626299 630279 := bstep (se 1 (by rfl) ⟨472709, by rfl⟩ : syracuseStep 630279 = 945419) B945419
theorem B630287 : Blo 626299 630287 := bstep (se 1 (by rfl) ⟨472715, by rfl⟩ : syracuseStep 630287 = 945431) B945431
theorem B1416851 : Blo 626299 1416851 := bstep (se 1 (by rfl) ⟨1062638, by rfl⟩ : syracuseStep 1416851 = 2125277) B2125277
theorem B3186377 : Blo 626299 3186377 := bstep (se 2 (by rfl) ⟨1194891, by rfl⟩ : syracuseStep 3186377 = 2389783) B2389783
theorem B1416905 : Blo 626299 1416905 := bstep (se 2 (by rfl) ⟨531339, by rfl⟩ : syracuseStep 1416905 = 1062679) B1062679
theorem B13573889 : Blo 626299 13573889 := bstep (se 2 (by rfl) ⟨5090208, by rfl⟩ : syracuseStep 13573889 = 10180417) B10180417
theorem B892729 : Blo 626299 892729 := bstep (se 2 (by rfl) ⟨334773, by rfl⟩ : syracuseStep 892729 = 669547) B669547
theorem B2858905 : Blo 626299 2858905 := bstep (se 2 (by rfl) ⟨1072089, by rfl⟩ : syracuseStep 2858905 = 2144179) B2144179
theorem B794539 : Blo 626299 794539 := bstep (se 1 (by rfl) ⟨595904, by rfl⟩ : syracuseStep 794539 = 1191809) B1191809
theorem B794767 : Blo 626299 794767 := bstep (se 1 (by rfl) ⟨596075, by rfl⟩ : syracuseStep 794767 = 1192151) B1192151
theorem B12230929 : Blo 626299 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B1909111 : Blo 626299 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B1417607 : Blo 626299 1417607 := bstep (se 1 (by rfl) ⟨1063205, by rfl⟩ : syracuseStep 1417607 = 2126411) B2126411
theorem B1057225 : Blo 626299 1057225 := bstep (se 2 (by rfl) ⟨396459, by rfl⟩ : syracuseStep 1057225 = 792919) B792919
theorem B1417787 : Blo 626299 1417787 := bstep (se 1 (by rfl) ⟨1063340, by rfl⟩ : syracuseStep 1417787 = 2126681) B2126681
theorem B3580483 : Blo 626299 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B1450631 : Blo 626299 1450631 := bstep (se 1 (by rfl) ⟨1087973, by rfl⟩ : syracuseStep 1450631 = 2175947) B2175947
theorem B1417913 : Blo 626299 1417913 := bstep (se 2 (by rfl) ⟨531717, by rfl⟩ : syracuseStep 1417913 = 1063435) B1063435
theorem B4530917 : Blo 626299 4530917 := bstep (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) B849547
theorem B4760369 : Blo 626299 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B795511 : Blo 626299 795511 := bstep (se 1 (by rfl) ⟨596633, by rfl⟩ : syracuseStep 795511 = 1193267) B1193267
theorem B1057927 : Blo 626299 1057927 := bstep (se 1 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 1057927 = 1586891) B1586891
theorem B795835 : Blo 626299 795835 := bstep (se 1 (by rfl) ⟨596876, by rfl⟩ : syracuseStep 795835 = 1193753) B1193753
theorem B21702023 : Blo 626299 21702023 := bstep (se 1 (by rfl) ⟨16276517, by rfl⟩ : syracuseStep 21702023 = 32553035) B32553035
theorem B796331 : Blo 626299 796331 := bstep (se 1 (by rfl) ⟨597248, by rfl⟩ : syracuseStep 796331 = 1194497) B1194497
theorem B1189561 : Blo 626299 1189561 := bstep (se 2 (by rfl) ⟨446085, by rfl⟩ : syracuseStep 1189561 = 892171) B892171
theorem B14526209 : Blo 626299 14526209 := bstep (se 2 (by rfl) ⟨5447328, by rfl⟩ : syracuseStep 14526209 = 10894657) B10894657
theorem B1058575 : Blo 626299 1058575 := bstep (se 1 (by rfl) ⟨793931, by rfl⟩ : syracuseStep 1058575 = 1587863) B1587863
theorem B2271185 : Blo 626299 2271185 := bstep (se 2 (by rfl) ⟨851694, by rfl⟩ : syracuseStep 2271185 = 1703389) B1703389
theorem B1189903 : Blo 626299 1189903 := bstep (se 1 (by rfl) ⟨892427, by rfl⟩ : syracuseStep 1189903 = 1784855) B1784855
theorem B796807 : Blo 626299 796807 := bstep (se 1 (by rfl) ⟨597605, by rfl⟩ : syracuseStep 796807 = 1195211) B1195211
theorem B1059115 : Blo 626299 1059115 := bstep (se 1 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 1059115 = 1588673) B1588673
theorem B4827539 : Blo 626299 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B1059257 : Blo 626299 1059257 := bstep (se 2 (by rfl) ⟨397221, by rfl⟩ : syracuseStep 1059257 = 794443) B794443
theorem B1812937 : Blo 626299 1812937 := bstep (se 2 (by rfl) ⟨679851, by rfl⟩ : syracuseStep 1812937 = 1359703) B1359703
theorem B3582467 : Blo 626299 3582467 := bstep (se 1 (by rfl) ⟨2686850, by rfl⟩ : syracuseStep 3582467 = 5373701) B5373701
theorem B895531 : Blo 626299 895531 := bstep (se 1 (by rfl) ⟨671648, by rfl⟩ : syracuseStep 895531 = 1343297) B1343297
theorem B797303 : Blo 626299 797303 := bstep (se 1 (by rfl) ⟨597977, by rfl⟩ : syracuseStep 797303 = 1195955) B1195955
theorem B7154405 : Blo 626299 7154405 := bstep (se 4 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 7154405 = 1341451) B1341451
theorem B764687 : Blo 626299 764687 := bstep (se 1 (by rfl) ⟨573515, by rfl⟩ : syracuseStep 764687 = 1147031) B1147031
theorem B797455 : Blo 626299 797455 := bstep (se 1 (by rfl) ⟨598091, by rfl⟩ : syracuseStep 797455 = 1196183) B1196183
theorem B4893529 : Blo 626299 4893529 := bstep (se 2 (by rfl) ⟨1835073, by rfl⟩ : syracuseStep 4893529 = 3670147) B3670147
theorem B1616755 : Blo 626299 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B1190791 : Blo 626299 1190791 := bstep (se 1 (by rfl) ⟨893093, by rfl⟩ : syracuseStep 1190791 = 1786187) B1786187
theorem B797627 : Blo 626299 797627 := bstep (se 1 (by rfl) ⟨598220, by rfl⟩ : syracuseStep 797627 = 1196441) B1196441
theorem B1059959 : Blo 626299 1059959 := bstep (se 1 (by rfl) ⟨794969, by rfl⟩ : syracuseStep 1059959 = 1589939) B1589939
theorem B1060411 : Blo 626299 1060411 := bstep (se 1 (by rfl) ⟨795308, by rfl⟩ : syracuseStep 1060411 = 1590617) B1590617
theorem B1060553 : Blo 626299 1060553 := bstep (se 2 (by rfl) ⟨397707, by rfl⟩ : syracuseStep 1060553 = 795415) B795415
theorem B1912577 : Blo 626299 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B4829017 : Blo 626299 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B1061255 : Blo 626299 1061255 := bstep (se 1 (by rfl) ⟨795941, by rfl⟩ : syracuseStep 1061255 = 1591883) B1591883
theorem B2044295 : Blo 626299 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B2011691 : Blo 626299 2011691 := bstep (se 1 (by rfl) ⟨1508768, by rfl⟩ : syracuseStep 2011691 = 3017537) B3017537
theorem B635527 : Blo 626299 635527 := bstep (se 1 (by rfl) ⟨476645, by rfl⟩ : syracuseStep 635527 = 953291) B953291
theorem B1192583 : Blo 626299 1192583 := bstep (se 1 (by rfl) ⟨894437, by rfl⟩ : syracuseStep 1192583 = 1788875) B1788875
theorem B3584857 : Blo 626299 3584857 := bstep (se 2 (by rfl) ⟨1344321, by rfl⟩ : syracuseStep 3584857 = 2688643) B2688643
theorem B1061903 : Blo 626299 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B1586263 : Blo 626299 1586263 := bstep (se 1 (by rfl) ⟨1189697, by rfl⟩ : syracuseStep 1586263 = 2379395) B2379395
theorem B1586567 : Blo 626299 1586567 := bstep (se 1 (by rfl) ⟨1189925, by rfl⟩ : syracuseStep 1586567 = 2379851) B2379851
theorem B1586699 : Blo 626299 1586699 := bstep (se 1 (by rfl) ⟨1190024, by rfl⟩ : syracuseStep 1586699 = 2380049) B2380049
theorem B1062443 : Blo 626299 1062443 := bstep (se 1 (by rfl) ⟨796832, by rfl⟩ : syracuseStep 1062443 = 1593665) B1593665
theorem B1783613 : Blo 626299 1783613 := bstep (se 3 (by rfl) ⟨334427, by rfl⟩ : syracuseStep 1783613 = 668855) B668855
theorem B1062841 : Blo 626299 1062841 := bstep (se 2 (by rfl) ⟨398565, by rfl⟩ : syracuseStep 1062841 = 797131) B797131
theorem B1587215 : Blo 626299 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B1587347 : Blo 626299 1587347 := bstep (se 1 (by rfl) ⟨1190510, by rfl⟩ : syracuseStep 1587347 = 2381021) B2381021
theorem B3586589 : Blo 626299 3586589 := bstep (se 3 (by rfl) ⟨672485, by rfl⟩ : syracuseStep 3586589 = 1344971) B1344971
theorem B1063543 : Blo 626299 1063543 := bstep (se 1 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 1063543 = 1595315) B1595315
theorem B12041075 : Blo 626299 12041075 := bstep (se 1 (by rfl) ⟨9030806, by rfl⟩ : syracuseStep 12041075 = 18061613) B18061613
theorem B3619729 : Blo 626299 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B1719187 : Blo 626299 1719187 := bstep (se 1 (by rfl) ⟨1289390, by rfl⟩ : syracuseStep 1719187 = 2578781) B2578781
theorem B1784729 : Blo 626299 1784729 := bstep (se 2 (by rfl) ⟨669273, by rfl⟩ : syracuseStep 1784729 = 1338547) B1338547
theorem B1195067 : Blo 626299 1195067 := bstep (se 1 (by rfl) ⟨896300, by rfl⟩ : syracuseStep 1195067 = 1792601) B1792601
theorem B3587273 : Blo 626299 3587273 := bstep (se 2 (by rfl) ⟨1345227, by rfl⟩ : syracuseStep 3587273 = 2690455) B2690455
theorem B1588481 : Blo 626299 1588481 := bstep (se 2 (by rfl) ⟨595680, by rfl⟩ : syracuseStep 1588481 = 1191361) B1191361
theorem B1359289 : Blo 626299 1359289 := bstep (se 2 (by rfl) ⟨509733, by rfl⟩ : syracuseStep 1359289 = 1019467) B1019467
theorem B7650845 : Blo 626299 7650845 := bstep (se 3 (by rfl) ⟨1434533, by rfl⟩ : syracuseStep 7650845 = 2869067) B2869067
theorem B1195553 : Blo 626299 1195553 := bstep (se 2 (by rfl) ⟨448332, by rfl⟩ : syracuseStep 1195553 = 896665) B896665
theorem B1588855 : Blo 626299 1588855 := bstep (se 1 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 1588855 = 2383283) B2383283
theorem B671375 : Blo 626299 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B1818503 : Blo 626299 1818503 := bstep (se 1 (by rfl) ⟨1363877, by rfl⟩ : syracuseStep 1818503 = 2727755) B2727755
theorem B3063737 : Blo 626299 3063737 := bstep (se 2 (by rfl) ⟨1148901, by rfl⟩ : syracuseStep 3063737 = 2297803) B2297803
theorem B1130539 : Blo 626299 1130539 := bstep (se 1 (by rfl) ⟨847904, by rfl⟩ : syracuseStep 1130539 = 1695809) B1695809
theorem B1589291 : Blo 626299 1589291 := bstep (se 1 (by rfl) ⟨1191968, by rfl⟩ : syracuseStep 1589291 = 2383937) B2383937
theorem B12927221 : Blo 626299 12927221 := bstep (se 5 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 12927221 = 1211927) B1211927
theorem B1786141 : Blo 626299 1786141 := bstep (se 3 (by rfl) ⟨334901, by rfl⟩ : syracuseStep 1786141 = 669803) B669803
theorem B704911 : Blo 626299 704911 := bstep (se 1 (by rfl) ⟨528683, by rfl⟩ : syracuseStep 704911 = 1057367) B1057367
theorem B4768145 : Blo 626299 4768145 := bstep (se 2 (by rfl) ⟨1788054, by rfl⟩ : syracuseStep 4768145 = 3576109) B3576109
theorem B1786313 : Blo 626299 1786313 := bstep (se 2 (by rfl) ⟨669867, by rfl⟩ : syracuseStep 1786313 = 1339735) B1339735
theorem B1786369 : Blo 626299 1786369 := bstep (se 2 (by rfl) ⟨669888, by rfl⟩ : syracuseStep 1786369 = 1339777) B1339777
theorem B3392003 : Blo 626299 3392003 := bstep (se 1 (by rfl) ⟨2544002, by rfl⟩ : syracuseStep 3392003 = 5088005) B5088005
theorem B672571 : Blo 626299 672571 := bstep (se 1 (by rfl) ⟨504428, by rfl⟩ : syracuseStep 672571 = 1008857) B1008857
theorem B1786711 : Blo 626299 1786711 := bstep (se 1 (by rfl) ⟨1340033, by rfl⟩ : syracuseStep 1786711 = 2680067) B2680067
theorem B1590131 : Blo 626299 1590131 := bstep (se 1 (by rfl) ⟨1192598, by rfl⟩ : syracuseStep 1590131 = 2385197) B2385197
theorem B705415 : Blo 626299 705415 := bstep (se 1 (by rfl) ⟨529061, by rfl⟩ : syracuseStep 705415 = 1058123) B1058123
theorem B1590151 : Blo 626299 1590151 := bstep (se 1 (by rfl) ⟨1192613, by rfl⟩ : syracuseStep 1590151 = 2385227) B2385227
theorem B3589049 : Blo 626299 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B1131563 : Blo 626299 1131563 := bstep (se 1 (by rfl) ⟨848672, by rfl⟩ : syracuseStep 1131563 = 1697345) B1697345
theorem B705595 : Blo 626299 705595 := bstep (se 1 (by rfl) ⟨529196, by rfl⟩ : syracuseStep 705595 = 1058393) B1058393
theorem B1590425 : Blo 626299 1590425 := bstep (se 2 (by rfl) ⟨596409, by rfl⟩ : syracuseStep 1590425 = 1192819) B1192819
theorem B7259381 : Blo 626299 7259381 := bstep (se 5 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 7259381 = 680567) B680567
theorem B1590587 : Blo 626299 1590587 := bstep (se 1 (by rfl) ⟨1192940, by rfl⟩ : syracuseStep 1590587 = 2385881) B2385881
theorem B2114963 : Blo 626299 2114963 := bstep (se 1 (by rfl) ⟨1586222, by rfl⟩ : syracuseStep 2114963 = 3172445) B3172445
theorem B706063 : Blo 626299 706063 := bstep (se 1 (by rfl) ⟨529547, by rfl⟩ : syracuseStep 706063 = 1059095) B1059095
theorem B1590799 : Blo 626299 1590799 := bstep (se 1 (by rfl) ⟨1193099, by rfl⟩ : syracuseStep 1590799 = 2386199) B2386199
theorem B6047297 : Blo 626299 6047297 := bstep (se 2 (by rfl) ⟨2267736, by rfl⟩ : syracuseStep 6047297 = 4535473) B4535473
theorem B5031695 : Blo 626299 5031695 := bstep (se 1 (by rfl) ⟨3773771, by rfl⟩ : syracuseStep 5031695 = 7547543) B7547543
theorem B1591073 : Blo 626299 1591073 := bstep (se 2 (by rfl) ⟨596652, by rfl⟩ : syracuseStep 1591073 = 1193305) B1193305
theorem B706567 : Blo 626299 706567 := bstep (se 1 (by rfl) ⟨529925, by rfl⟩ : syracuseStep 706567 = 1059851) B1059851
theorem B1722455 : Blo 626299 1722455 := bstep (se 1 (by rfl) ⟨1291841, by rfl⟩ : syracuseStep 1722455 = 2583683) B2583683
theorem B706747 : Blo 626299 706747 := bstep (se 1 (by rfl) ⟨530060, by rfl⟩ : syracuseStep 706747 = 1060121) B1060121
theorem B3393737 : Blo 626299 3393737 := bstep (se 2 (by rfl) ⟨1272651, by rfl⟩ : syracuseStep 3393737 = 2545303) B2545303
theorem B2378119 : Blo 626299 2378119 := bstep (se 1 (by rfl) ⟨1783589, by rfl⟩ : syracuseStep 2378119 = 3567179) B3567179
theorem B1133191 : Blo 626299 1133191 := bstep (se 1 (by rfl) ⟨849893, by rfl⟩ : syracuseStep 1133191 = 1699787) B1699787
theorem B707215 : Blo 626299 707215 := bstep (se 1 (by rfl) ⟨530411, by rfl⟩ : syracuseStep 707215 = 1060823) B1060823
theorem B1886867 : Blo 626299 1886867 := bstep (se 1 (by rfl) ⟨1415150, by rfl⟩ : syracuseStep 1886867 = 2830301) B2830301
theorem B1592075 : Blo 626299 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B2116367 : Blo 626299 2116367 := bstep (se 1 (by rfl) ⟨1587275, by rfl⟩ : syracuseStep 2116367 = 3174551) B3174551
theorem B4770575 : Blo 626299 4770575 := bstep (se 1 (by rfl) ⟨3577931, by rfl⟩ : syracuseStep 4770575 = 7155863) B7155863
theorem B2116637 : Blo 626299 2116637 := bstep (se 3 (by rfl) ⟨396869, by rfl⟩ : syracuseStep 2116637 = 793739) B793739
theorem B904235 : Blo 626299 904235 := bstep (se 1 (by rfl) ⟨678176, by rfl⟩ : syracuseStep 904235 = 1356353) B1356353
theorem B707719 : Blo 626299 707719 := bstep (se 1 (by rfl) ⟨530789, by rfl⟩ : syracuseStep 707719 = 1061579) B1061579
theorem B7163153 : Blo 626299 7163153 := bstep (se 2 (by rfl) ⟨2686182, by rfl⟩ : syracuseStep 7163153 = 5372365) B5372365
theorem B707899 : Blo 626299 707899 := bstep (se 1 (by rfl) ⟨530924, by rfl⟩ : syracuseStep 707899 = 1061849) B1061849
theorem B1592723 : Blo 626299 1592723 := bstep (se 1 (by rfl) ⟨1194542, by rfl⟩ : syracuseStep 1592723 = 2389085) B2389085
theorem B2543147 : Blo 626299 2543147 := bstep (se 1 (by rfl) ⟨1907360, by rfl⟩ : syracuseStep 2543147 = 3814721) B3814721
theorem B1789559 : Blo 626299 1789559 := bstep (se 1 (by rfl) ⟨1342169, by rfl⟩ : syracuseStep 1789559 = 2684339) B2684339
theorem B1593017 : Blo 626299 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B708367 : Blo 626299 708367 := bstep (se 1 (by rfl) ⟨531275, by rfl⟩ : syracuseStep 708367 = 1062551) B1062551
theorem B7622857 : Blo 626299 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B708871 : Blo 626299 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B1593715 : Blo 626299 1593715 := bstep (se 1 (by rfl) ⟨1195286, by rfl⟩ : syracuseStep 1593715 = 2390573) B2390573
theorem B10768787 : Blo 626299 10768787 := bstep (se 1 (by rfl) ⟨8076590, by rfl⟩ : syracuseStep 10768787 = 16153181) B16153181
theorem B2118041 : Blo 626299 2118041 := bstep (se 2 (by rfl) ⟨794265, by rfl⟩ : syracuseStep 2118041 = 1588531) B1588531
theorem B709051 : Blo 626299 709051 := bstep (se 1 (by rfl) ⟨531788, by rfl⟩ : syracuseStep 709051 = 1063577) B1063577
theorem B1593857 : Blo 626299 1593857 := bstep (se 2 (by rfl) ⟨597696, by rfl⟩ : syracuseStep 1593857 = 1195393) B1195393
theorem B3625559 : Blo 626299 3625559 := bstep (se 1 (by rfl) ⟨2719169, by rfl⟩ : syracuseStep 3625559 = 5438339) B5438339
theorem B2871895 : Blo 626299 2871895 := bstep (se 1 (by rfl) ⟨2153921, by rfl⟩ : syracuseStep 2871895 = 4307843) B4307843
theorem B1004167 : Blo 626299 1004167 := bstep (se 1 (by rfl) ⟨753125, by rfl⟩ : syracuseStep 1004167 = 1506251) B1506251
theorem B2675591 : Blo 626299 2675591 := bstep (se 1 (by rfl) ⟨2006693, by rfl⟩ : syracuseStep 2675591 = 4013387) B4013387
theorem B1594313 : Blo 626299 1594313 := bstep (se 2 (by rfl) ⟨597867, by rfl⟩ : syracuseStep 1594313 = 1195735) B1195735
theorem B2118743 : Blo 626299 2118743 := bstep (se 1 (by rfl) ⟨1589057, by rfl⟩ : syracuseStep 2118743 = 3178115) B3178115
theorem B1594667 : Blo 626299 1594667 := bstep (se 1 (by rfl) ⟨1196000, by rfl⟩ : syracuseStep 1594667 = 2392001) B2392001
theorem B23287175 : Blo 626299 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B15324551 : Blo 626299 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B939449 : Blo 626299 939449 := bstep (se 2 (by rfl) ⟨352293, by rfl⟩ : syracuseStep 939449 = 704587) B704587
theorem B6051293 : Blo 626299 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B939527 : Blo 626299 939527 := bstep (se 1 (by rfl) ⟨704645, by rfl⟩ : syracuseStep 939527 = 1409291) B1409291
theorem B939563 : Blo 626299 939563 := bstep (se 1 (by rfl) ⟨704672, by rfl⟩ : syracuseStep 939563 = 1409345) B1409345
theorem B1005115 : Blo 626299 1005115 := bstep (se 1 (by rfl) ⟨753836, by rfl⟩ : syracuseStep 1005115 = 1507673) B1507673
theorem B2119229 : Blo 626299 2119229 := bstep (se 3 (by rfl) ⟨397355, by rfl⟩ : syracuseStep 2119229 = 794711) B794711
theorem B939593 : Blo 626299 939593 := bstep (se 2 (by rfl) ⟨352347, by rfl⟩ : syracuseStep 939593 = 704695) B704695
theorem B939707 : Blo 626299 939707 := bstep (se 1 (by rfl) ⟨704780, by rfl⟩ : syracuseStep 939707 = 1409561) B1409561
theorem B939767 : Blo 626299 939767 := bstep (se 1 (by rfl) ⟨704825, by rfl⟩ : syracuseStep 939767 = 1409651) B1409651
theorem B939791 : Blo 626299 939791 := bstep (se 1 (by rfl) ⟨704843, by rfl⟩ : syracuseStep 939791 = 1409687) B1409687
theorem B939833 : Blo 626299 939833 := bstep (se 2 (by rfl) ⟨352437, by rfl⟩ : syracuseStep 939833 = 704875) B704875
theorem B939911 : Blo 626299 939911 := bstep (se 1 (by rfl) ⟨704933, by rfl⟩ : syracuseStep 939911 = 1409867) B1409867
theorem B939947 : Blo 626299 939947 := bstep (se 1 (by rfl) ⟨704960, by rfl⟩ : syracuseStep 939947 = 1409921) B1409921
theorem B939977 : Blo 626299 939977 := bstep (se 2 (by rfl) ⟨352491, by rfl⟩ : syracuseStep 939977 = 704983) B704983
theorem B940091 : Blo 626299 940091 := bstep (se 1 (by rfl) ⟨705068, by rfl⟩ : syracuseStep 940091 = 1410137) B1410137
theorem B7166069 : Blo 626299 7166069 := bstep (se 5 (by rfl) ⟨335909, by rfl⟩ : syracuseStep 7166069 = 671819) B671819
theorem B940151 : Blo 626299 940151 := bstep (se 1 (by rfl) ⟨705113, by rfl⟩ : syracuseStep 940151 = 1410227) B1410227
theorem B940175 : Blo 626299 940175 := bstep (se 1 (by rfl) ⟨705131, by rfl⟩ : syracuseStep 940175 = 1410263) B1410263
theorem B940217 : Blo 626299 940217 := bstep (se 2 (by rfl) ⟨352581, by rfl⟩ : syracuseStep 940217 = 705163) B705163
theorem B1792201 : Blo 626299 1792201 := bstep (se 2 (by rfl) ⟨672075, by rfl⟩ : syracuseStep 1792201 = 1344151) B1344151
theorem B940295 : Blo 626299 940295 := bstep (se 1 (by rfl) ⟨705221, by rfl⟩ : syracuseStep 940295 = 1410443) B1410443
theorem B12245261 : Blo 626299 12245261 := bstep (se 3 (by rfl) ⟨2295986, by rfl⟩ : syracuseStep 12245261 = 4591973) B4591973
theorem B2677025 : Blo 626299 2677025 := bstep (se 2 (by rfl) ⟨1003884, by rfl⟩ : syracuseStep 2677025 = 2007769) B2007769
theorem B940331 : Blo 626299 940331 := bstep (se 1 (by rfl) ⟨705248, by rfl⟩ : syracuseStep 940331 = 1410497) B1410497
theorem B940361 : Blo 626299 940361 := bstep (se 2 (by rfl) ⟨352635, by rfl⟩ : syracuseStep 940361 = 705271) B705271
theorem B940475 : Blo 626299 940475 := bstep (se 1 (by rfl) ⟨705356, by rfl⟩ : syracuseStep 940475 = 1410713) B1410713
theorem B940535 : Blo 626299 940535 := bstep (se 1 (by rfl) ⟨705401, by rfl⟩ : syracuseStep 940535 = 1410803) B1410803
theorem B940559 : Blo 626299 940559 := bstep (se 1 (by rfl) ⟨705419, by rfl⟩ : syracuseStep 940559 = 1410839) B1410839
theorem B940601 : Blo 626299 940601 := bstep (se 2 (by rfl) ⟨352725, by rfl⟩ : syracuseStep 940601 = 705451) B705451
theorem B2677367 : Blo 626299 2677367 := bstep (se 1 (by rfl) ⟨2008025, by rfl⟩ : syracuseStep 2677367 = 4016051) B4016051
theorem B940679 : Blo 626299 940679 := bstep (se 1 (by rfl) ⟨705509, by rfl⟩ : syracuseStep 940679 = 1411019) B1411019
theorem B940715 : Blo 626299 940715 := bstep (se 1 (by rfl) ⟨705536, by rfl⟩ : syracuseStep 940715 = 1411073) B1411073
theorem B940745 : Blo 626299 940745 := bstep (se 2 (by rfl) ⟨352779, by rfl⟩ : syracuseStep 940745 = 705559) B705559
theorem B6806321 : Blo 626299 6806321 := bstep (se 2 (by rfl) ⟨2552370, by rfl⟩ : syracuseStep 6806321 = 5104741) B5104741
theorem B940859 : Blo 626299 940859 := bstep (se 1 (by rfl) ⟨705644, by rfl⟩ : syracuseStep 940859 = 1411289) B1411289
theorem B940919 : Blo 626299 940919 := bstep (se 1 (by rfl) ⟨705689, by rfl⟩ : syracuseStep 940919 = 1411379) B1411379
theorem B940943 : Blo 626299 940943 := bstep (se 1 (by rfl) ⟨705707, by rfl⟩ : syracuseStep 940943 = 1411415) B1411415
theorem B940985 : Blo 626299 940985 := bstep (se 2 (by rfl) ⟨352869, by rfl⟩ : syracuseStep 940985 = 705739) B705739
theorem B2120633 : Blo 626299 2120633 := bstep (se 2 (by rfl) ⟨795237, by rfl⟩ : syracuseStep 2120633 = 1590475) B1590475
theorem B941063 : Blo 626299 941063 := bstep (se 1 (by rfl) ⟨705797, by rfl⟩ : syracuseStep 941063 = 1411595) B1411595
theorem B2153483 : Blo 626299 2153483 := bstep (se 1 (by rfl) ⟨1615112, by rfl⟩ : syracuseStep 2153483 = 3230225) B3230225
theorem B941099 : Blo 626299 941099 := bstep (se 1 (by rfl) ⟨705824, by rfl⟩ : syracuseStep 941099 = 1411649) B1411649
theorem B941129 : Blo 626299 941129 := bstep (se 2 (by rfl) ⟨352923, by rfl⟩ : syracuseStep 941129 = 705847) B705847
theorem B941243 : Blo 626299 941243 := bstep (se 1 (by rfl) ⟨705932, by rfl⟩ : syracuseStep 941243 = 1411865) B1411865
theorem B941303 : Blo 626299 941303 := bstep (se 1 (by rfl) ⟨705977, by rfl⟩ : syracuseStep 941303 = 1411955) B1411955
theorem B941327 : Blo 626299 941327 := bstep (se 1 (by rfl) ⟨705995, by rfl⟩ : syracuseStep 941327 = 1411991) B1411991
theorem B1432865 : Blo 626299 1432865 := bstep (se 2 (by rfl) ⟨537324, by rfl⟩ : syracuseStep 1432865 = 1074649) B1074649
theorem B941369 : Blo 626299 941369 := bstep (se 2 (by rfl) ⟨353013, by rfl⟩ : syracuseStep 941369 = 706027) B706027
theorem B941447 : Blo 626299 941447 := bstep (se 1 (by rfl) ⟨706085, by rfl⟩ : syracuseStep 941447 = 1412171) B1412171
theorem B941483 : Blo 626299 941483 := bstep (se 1 (by rfl) ⟨706112, by rfl⟩ : syracuseStep 941483 = 1412225) B1412225
theorem B941513 : Blo 626299 941513 := bstep (se 2 (by rfl) ⟨353067, by rfl⟩ : syracuseStep 941513 = 706135) B706135
theorem B11427281 : Blo 626299 11427281 := bstep (se 2 (by rfl) ⟨4285230, by rfl⟩ : syracuseStep 11427281 = 8570461) B8570461
theorem B2121227 : Blo 626299 2121227 := bstep (se 1 (by rfl) ⟨1590920, by rfl⟩ : syracuseStep 2121227 = 3181841) B3181841
theorem B941627 : Blo 626299 941627 := bstep (se 1 (by rfl) ⟨706220, by rfl⟩ : syracuseStep 941627 = 1412441) B1412441
theorem B941687 : Blo 626299 941687 := bstep (se 1 (by rfl) ⟨706265, by rfl⟩ : syracuseStep 941687 = 1412531) B1412531
theorem B2121335 : Blo 626299 2121335 := bstep (se 1 (by rfl) ⟨1591001, by rfl⟩ : syracuseStep 2121335 = 3182003) B3182003
theorem B941711 : Blo 626299 941711 := bstep (se 1 (by rfl) ⟨706283, by rfl⟩ : syracuseStep 941711 = 1412567) B1412567
theorem B941753 : Blo 626299 941753 := bstep (se 2 (by rfl) ⟨353157, by rfl⟩ : syracuseStep 941753 = 706315) B706315
theorem B941831 : Blo 626299 941831 := bstep (se 1 (by rfl) ⟨706373, by rfl⟩ : syracuseStep 941831 = 1412747) B1412747
theorem B941867 : Blo 626299 941867 := bstep (se 1 (by rfl) ⟨706400, by rfl⟩ : syracuseStep 941867 = 1412801) B1412801
theorem B6446897 : Blo 626299 6446897 := bstep (se 2 (by rfl) ⟨2417586, by rfl⟩ : syracuseStep 6446897 = 4835173) B4835173
theorem B941897 : Blo 626299 941897 := bstep (se 2 (by rfl) ⟨353211, by rfl⟩ : syracuseStep 941897 = 706423) B706423
theorem B2383769 : Blo 626299 2383769 := bstep (se 2 (by rfl) ⟨893913, by rfl⟩ : syracuseStep 2383769 = 1787827) B1787827
theorem B942011 : Blo 626299 942011 := bstep (se 1 (by rfl) ⟨706508, by rfl⟩ : syracuseStep 942011 = 1413017) B1413017
theorem B942071 : Blo 626299 942071 := bstep (se 1 (by rfl) ⟨706553, by rfl⟩ : syracuseStep 942071 = 1413107) B1413107
theorem B1794059 : Blo 626299 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B942095 : Blo 626299 942095 := bstep (se 1 (by rfl) ⟨706571, by rfl⟩ : syracuseStep 942095 = 1413143) B1413143
theorem B942137 : Blo 626299 942137 := bstep (se 2 (by rfl) ⟨353301, by rfl⟩ : syracuseStep 942137 = 706603) B706603
theorem B942215 : Blo 626299 942215 := bstep (se 1 (by rfl) ⟨706661, by rfl⟩ : syracuseStep 942215 = 1413323) B1413323
theorem B942251 : Blo 626299 942251 := bstep (se 1 (by rfl) ⟨706688, by rfl⟩ : syracuseStep 942251 = 1413377) B1413377
theorem B6054061 : Blo 626299 6054061 := bstep (se 3 (by rfl) ⟨1135136, by rfl⟩ : syracuseStep 6054061 = 2270273) B2270273
theorem B942281 : Blo 626299 942281 := bstep (se 2 (by rfl) ⟨353355, by rfl⟩ : syracuseStep 942281 = 706711) B706711
theorem B2121929 : Blo 626299 2121929 := bstep (se 2 (by rfl) ⟨795723, by rfl⟩ : syracuseStep 2121929 = 1591447) B1591447
theorem B4022561 : Blo 626299 4022561 := bstep (se 2 (by rfl) ⟨1508460, by rfl⟩ : syracuseStep 4022561 = 3016921) B3016921
theorem B942395 : Blo 626299 942395 := bstep (se 1 (by rfl) ⟨706796, by rfl⟩ : syracuseStep 942395 = 1413593) B1413593
theorem B942455 : Blo 626299 942455 := bstep (se 1 (by rfl) ⟨706841, by rfl⟩ : syracuseStep 942455 = 1413683) B1413683
theorem B942479 : Blo 626299 942479 := bstep (se 1 (by rfl) ⟨706859, by rfl⟩ : syracuseStep 942479 = 1413719) B1413719
theorem B4022713 : Blo 626299 4022713 := bstep (se 2 (by rfl) ⟨1508517, by rfl⟩ : syracuseStep 4022713 = 3017035) B3017035
theorem B942521 : Blo 626299 942521 := bstep (se 2 (by rfl) ⟨353445, by rfl⟩ : syracuseStep 942521 = 706891) B706891
theorem B942599 : Blo 626299 942599 := bstep (se 1 (by rfl) ⟨706949, by rfl⟩ : syracuseStep 942599 = 1413899) B1413899
theorem B942635 : Blo 626299 942635 := bstep (se 1 (by rfl) ⟨706976, by rfl⟩ : syracuseStep 942635 = 1413953) B1413953
theorem B942665 : Blo 626299 942665 := bstep (se 2 (by rfl) ⟨353499, by rfl⟩ : syracuseStep 942665 = 706999) B706999
theorem B1696391 : Blo 626299 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B1794707 : Blo 626299 1794707 := bstep (se 1 (by rfl) ⟨1346030, by rfl⟩ : syracuseStep 1794707 = 2692061) B2692061
theorem B942779 : Blo 626299 942779 := bstep (se 1 (by rfl) ⟨707084, by rfl⟩ : syracuseStep 942779 = 1414169) B1414169
theorem B3400393 : Blo 626299 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B942839 : Blo 626299 942839 := bstep (se 1 (by rfl) ⟨707129, by rfl⟩ : syracuseStep 942839 = 1414259) B1414259
theorem B942863 : Blo 626299 942863 := bstep (se 1 (by rfl) ⟨707147, by rfl⟩ : syracuseStep 942863 = 1414295) B1414295
theorem B942905 : Blo 626299 942905 := bstep (se 2 (by rfl) ⟨353589, by rfl⟩ : syracuseStep 942905 = 707179) B707179
theorem B942983 : Blo 626299 942983 := bstep (se 1 (by rfl) ⟨707237, by rfl⟩ : syracuseStep 942983 = 1414475) B1414475
theorem B2122631 : Blo 626299 2122631 := bstep (se 1 (by rfl) ⟨1591973, by rfl⟩ : syracuseStep 2122631 = 3183947) B3183947
theorem B943019 : Blo 626299 943019 := bstep (se 1 (by rfl) ⟨707264, by rfl⟩ : syracuseStep 943019 = 1414529) B1414529
theorem B943049 : Blo 626299 943049 := bstep (se 2 (by rfl) ⟨353643, by rfl⟩ : syracuseStep 943049 = 707287) B707287
theorem B9036805 : Blo 626299 9036805 := bstep (se 4 (by rfl) ⟨847200, by rfl⟩ : syracuseStep 9036805 = 1694401) B1694401
theorem B943163 : Blo 626299 943163 := bstep (se 1 (by rfl) ⟨707372, by rfl⟩ : syracuseStep 943163 = 1414745) B1414745
theorem B2679895 : Blo 626299 2679895 := bstep (se 1 (by rfl) ⟨2009921, by rfl⟩ : syracuseStep 2679895 = 4019843) B4019843
theorem B943223 : Blo 626299 943223 := bstep (se 1 (by rfl) ⟨707417, by rfl⟩ : syracuseStep 943223 = 1414835) B1414835
theorem B943247 : Blo 626299 943247 := bstep (se 1 (by rfl) ⟨707435, by rfl⟩ : syracuseStep 943247 = 1414871) B1414871
theorem B943289 : Blo 626299 943289 := bstep (se 2 (by rfl) ⟨353733, by rfl⟩ : syracuseStep 943289 = 707467) B707467
theorem B4023533 : Blo 626299 4023533 := bstep (se 3 (by rfl) ⟨754412, by rfl⟩ : syracuseStep 4023533 = 1508825) B1508825
theorem B2123009 : Blo 626299 2123009 := bstep (se 2 (by rfl) ⟨796128, by rfl⟩ : syracuseStep 2123009 = 1592257) B1592257
theorem B943367 : Blo 626299 943367 := bstep (se 1 (by rfl) ⟨707525, by rfl⟩ : syracuseStep 943367 = 1415051) B1415051
theorem B943403 : Blo 626299 943403 := bstep (se 1 (by rfl) ⟨707552, by rfl⟩ : syracuseStep 943403 = 1415105) B1415105
theorem B3171635 : Blo 626299 3171635 := bstep (se 1 (by rfl) ⟨2378726, by rfl⟩ : syracuseStep 3171635 = 4757453) B4757453
theorem B943433 : Blo 626299 943433 := bstep (se 2 (by rfl) ⟨353787, by rfl⟩ : syracuseStep 943433 = 707575) B707575
theorem B943547 : Blo 626299 943547 := bstep (se 1 (by rfl) ⟨707660, by rfl⟩ : syracuseStep 943547 = 1415321) B1415321
theorem B943607 : Blo 626299 943607 := bstep (se 1 (by rfl) ⟨707705, by rfl⟩ : syracuseStep 943607 = 1415411) B1415411
theorem B943631 : Blo 626299 943631 := bstep (se 1 (by rfl) ⟨707723, by rfl⟩ : syracuseStep 943631 = 1415447) B1415447
theorem B943673 : Blo 626299 943673 := bstep (se 2 (by rfl) ⟨353877, by rfl⟩ : syracuseStep 943673 = 707755) B707755
theorem B3171959 : Blo 626299 3171959 := bstep (se 1 (by rfl) ⟨2378969, by rfl⟩ : syracuseStep 3171959 = 4757939) B4757939
theorem B943751 : Blo 626299 943751 := bstep (se 1 (by rfl) ⟨707813, by rfl⟩ : syracuseStep 943751 = 1415627) B1415627
theorem B943787 : Blo 626299 943787 := bstep (se 1 (by rfl) ⟨707840, by rfl⟩ : syracuseStep 943787 = 1415681) B1415681
theorem B943817 : Blo 626299 943817 := bstep (se 2 (by rfl) ⟨353931, by rfl⟩ : syracuseStep 943817 = 707863) B707863
theorem B2549519 : Blo 626299 2549519 := bstep (se 1 (by rfl) ⟨1912139, by rfl⟩ : syracuseStep 2549519 = 3824279) B3824279
theorem B943931 : Blo 626299 943931 := bstep (se 1 (by rfl) ⟨707948, by rfl⟩ : syracuseStep 943931 = 1415897) B1415897
theorem B943991 : Blo 626299 943991 := bstep (se 1 (by rfl) ⟨707993, by rfl⟩ : syracuseStep 943991 = 1415987) B1415987
theorem B944015 : Blo 626299 944015 := bstep (se 1 (by rfl) ⟨708011, by rfl⟩ : syracuseStep 944015 = 1416023) B1416023
theorem B944057 : Blo 626299 944057 := bstep (se 2 (by rfl) ⟨354021, by rfl⟩ : syracuseStep 944057 = 708043) B708043
theorem B944135 : Blo 626299 944135 := bstep (se 1 (by rfl) ⟨708101, by rfl⟩ : syracuseStep 944135 = 1416203) B1416203
theorem B2418731 : Blo 626299 2418731 := bstep (se 1 (by rfl) ⟨1814048, by rfl⟩ : syracuseStep 2418731 = 3628097) B3628097
theorem B2123819 : Blo 626299 2123819 := bstep (se 1 (by rfl) ⟨1592864, by rfl⟩ : syracuseStep 2123819 = 3185729) B3185729
theorem B944171 : Blo 626299 944171 := bstep (se 1 (by rfl) ⟨708128, by rfl⟩ : syracuseStep 944171 = 1416257) B1416257
theorem B944201 : Blo 626299 944201 := bstep (se 2 (by rfl) ⟨354075, by rfl⟩ : syracuseStep 944201 = 708151) B708151
theorem B944315 : Blo 626299 944315 := bstep (se 1 (by rfl) ⟨708236, by rfl⟩ : syracuseStep 944315 = 1416473) B1416473
theorem B1697993 : Blo 626299 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B944375 : Blo 626299 944375 := bstep (se 1 (by rfl) ⟨708281, by rfl⟩ : syracuseStep 944375 = 1416563) B1416563
theorem B944399 : Blo 626299 944399 := bstep (se 1 (by rfl) ⟨708299, by rfl⟩ : syracuseStep 944399 = 1416599) B1416599
theorem B944441 : Blo 626299 944441 := bstep (se 2 (by rfl) ⟨354165, by rfl⟩ : syracuseStep 944441 = 708331) B708331
theorem B944519 : Blo 626299 944519 := bstep (se 1 (by rfl) ⟨708389, by rfl⟩ : syracuseStep 944519 = 1416779) B1416779
theorem B944555 : Blo 626299 944555 := bstep (se 1 (by rfl) ⟨708416, by rfl⟩ : syracuseStep 944555 = 1416833) B1416833
theorem B944585 : Blo 626299 944585 := bstep (se 2 (by rfl) ⟨354219, by rfl⟩ : syracuseStep 944585 = 708439) B708439
theorem B2714141 : Blo 626299 2714141 := bstep (se 3 (by rfl) ⟨508901, by rfl⟩ : syracuseStep 2714141 = 1017803) B1017803
theorem B944699 : Blo 626299 944699 := bstep (se 1 (by rfl) ⟨708524, by rfl⟩ : syracuseStep 944699 = 1417049) B1417049
theorem B3172931 : Blo 626299 3172931 := bstep (se 1 (by rfl) ⟨2379698, by rfl⟩ : syracuseStep 3172931 = 4759397) B4759397
theorem B944759 : Blo 626299 944759 := bstep (se 1 (by rfl) ⟨708569, by rfl⟩ : syracuseStep 944759 = 1417139) B1417139
theorem B944783 : Blo 626299 944783 := bstep (se 1 (by rfl) ⟨708587, by rfl⟩ : syracuseStep 944783 = 1417175) B1417175
theorem B944825 : Blo 626299 944825 := bstep (se 2 (by rfl) ⟨354309, by rfl⟩ : syracuseStep 944825 = 708619) B708619
theorem B944903 : Blo 626299 944903 := bstep (se 1 (by rfl) ⟨708677, by rfl⟩ : syracuseStep 944903 = 1417355) B1417355
theorem B846607 : Blo 626299 846607 := bstep (se 1 (by rfl) ⟨634955, by rfl⟩ : syracuseStep 846607 = 1269911) B1269911
theorem B10742543 : Blo 626299 10742543 := bstep (se 1 (by rfl) ⟨8056907, by rfl⟩ : syracuseStep 10742543 = 16113815) B16113815
theorem B944939 : Blo 626299 944939 := bstep (se 1 (by rfl) ⟨708704, by rfl⟩ : syracuseStep 944939 = 1417409) B1417409
theorem B944969 : Blo 626299 944969 := bstep (se 2 (by rfl) ⟨354363, by rfl⟩ : syracuseStep 944969 = 708727) B708727
theorem B3173255 : Blo 626299 3173255 := bstep (se 1 (by rfl) ⟨2379941, by rfl⟩ : syracuseStep 3173255 = 4759883) B4759883
theorem B945083 : Blo 626299 945083 := bstep (se 1 (by rfl) ⟨708812, by rfl⟩ : syracuseStep 945083 = 1417625) B1417625
theorem B945143 : Blo 626299 945143 := bstep (se 1 (by rfl) ⟨708857, by rfl⟩ : syracuseStep 945143 = 1417715) B1417715
theorem B945167 : Blo 626299 945167 := bstep (se 1 (by rfl) ⟨708875, by rfl⟩ : syracuseStep 945167 = 1417751) B1417751
theorem B945209 : Blo 626299 945209 := bstep (se 2 (by rfl) ⟨354453, by rfl⟩ : syracuseStep 945209 = 708907) B708907
theorem B945287 : Blo 626299 945287 := bstep (se 1 (by rfl) ⟨708965, by rfl⟩ : syracuseStep 945287 = 1417931) B1417931
theorem B945323 : Blo 626299 945323 := bstep (se 1 (by rfl) ⟨708992, by rfl⟩ : syracuseStep 945323 = 1417985) B1417985
theorem B945353 : Blo 626299 945353 := bstep (se 2 (by rfl) ⟨354507, by rfl⟩ : syracuseStep 945353 = 709015) B709015
theorem B2551073 : Blo 626299 2551073 := bstep (se 2 (by rfl) ⟨956652, by rfl⟩ : syracuseStep 2551073 = 1913305) B1913305
theorem B4779323 : Blo 626299 4779323 := bstep (se 1 (by rfl) ⟨3584492, by rfl⟩ : syracuseStep 4779323 = 7168985) B7168985
theorem B2125115 : Blo 626299 2125115 := bstep (se 1 (by rfl) ⟨1593836, by rfl⟩ : syracuseStep 2125115 = 3187673) B3187673
theorem B1699159 : Blo 626299 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B2387353 : Blo 626299 2387353 := bstep (se 2 (by rfl) ⟨895257, by rfl⟩ : syracuseStep 2387353 = 1790515) B1790515
theorem B1338923 : Blo 626299 1338923 := bstep (se 1 (by rfl) ⟨1004192, by rfl⟩ : syracuseStep 1338923 = 2008385) B2008385
theorem B2387657 : Blo 626299 2387657 := bstep (se 2 (by rfl) ⟨895371, by rfl⟩ : syracuseStep 2387657 = 1790743) B1790743
theorem B3567361 : Blo 626299 3567361 := bstep (se 2 (by rfl) ⟨1337760, by rfl⟩ : syracuseStep 3567361 = 2675521) B2675521
theorem B2125601 : Blo 626299 2125601 := bstep (se 2 (by rfl) ⟨797100, by rfl⟩ : syracuseStep 2125601 = 1594201) B1594201
theorem B716815 : Blo 626299 716815 := bstep (se 1 (by rfl) ⟨537611, by rfl⟩ : syracuseStep 716815 = 1075223) B1075223
theorem B1273915 : Blo 626299 1273915 := bstep (se 1 (by rfl) ⟨955436, by rfl⟩ : syracuseStep 1273915 = 1910873) B1910873
theorem B3567887 : Blo 626299 3567887 := bstep (se 1 (by rfl) ⟨2675915, by rfl⟩ : syracuseStep 3567887 = 5351831) B5351831
theorem B2126195 : Blo 626299 2126195 := bstep (se 1 (by rfl) ⟨1594646, by rfl⟩ : syracuseStep 2126195 = 3189293) B3189293
theorem B13627865 : Blo 626299 13627865 := bstep (se 2 (by rfl) ⟨5110449, by rfl⟩ : syracuseStep 13627865 = 10220899) B10220899
theorem B3404375 : Blo 626299 3404375 := bstep (se 1 (by rfl) ⟨2553281, by rfl⟩ : syracuseStep 3404375 = 5106563) B5106563
theorem B2388599 : Blo 626299 2388599 := bstep (se 1 (by rfl) ⟨1791449, by rfl⟩ : syracuseStep 2388599 = 3582899) B3582899
theorem B2257645 : Blo 626299 2257645 := bstep (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) B846617
theorem B1209463 : Blo 626299 1209463 := bstep (se 1 (by rfl) ⟨907097, by rfl⟩ : syracuseStep 1209463 = 1814195) B1814195
theorem B1340563 : Blo 626299 1340563 := bstep (se 1 (by rfl) ⟨1005422, by rfl⟩ : syracuseStep 1340563 = 2010845) B2010845
theorem B1242383 : Blo 626299 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B2389571 : Blo 626299 2389571 := bstep (se 1 (by rfl) ⟨1792178, by rfl⟩ : syracuseStep 2389571 = 3584357) B3584357
theorem B3569345 : Blo 626299 3569345 := bstep (se 2 (by rfl) ⟨1338504, by rfl⟩ : syracuseStep 3569345 = 2677009) B2677009
theorem B6453107 : Blo 626299 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B7141283 : Blo 626299 7141283 := bstep (se 1 (by rfl) ⟨5355962, by rfl⟩ : syracuseStep 7141283 = 10711925) B10711925
theorem B48953621 : Blo 626299 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B3176819 : Blo 626299 3176819 := bstep (se 1 (by rfl) ⟨2382614, by rfl⟩ : syracuseStep 3176819 = 4765229) B4765229
theorem B850423 : Blo 626299 850423 := bstep (se 1 (by rfl) ⟨637817, by rfl⟩ : syracuseStep 850423 = 1275635) B1275635
theorem B1636951 : Blo 626299 1636951 := bstep (se 1 (by rfl) ⟨1227713, by rfl⟩ : syracuseStep 1636951 = 2455427) B2455427
theorem B4029047 : Blo 626299 4029047 := bstep (se 1 (by rfl) ⟨3021785, by rfl⟩ : syracuseStep 4029047 = 6043571) B6043571
theorem B3177305 : Blo 626299 3177305 := bstep (se 2 (by rfl) ⟨1191489, by rfl⟩ : syracuseStep 3177305 = 2382979) B2382979
theorem B4848473 : Blo 626299 4848473 := bstep (se 2 (by rfl) ⟨1818177, by rfl⟩ : syracuseStep 4848473 = 3636355) B3636355
theorem B2391241 : Blo 626299 2391241 := bstep (se 2 (by rfl) ⟨896715, by rfl⟩ : syracuseStep 2391241 = 1793431) B1793431
theorem B2686355 : Blo 626299 2686355 := bstep (se 1 (by rfl) ⟨2014766, by rfl⟩ : syracuseStep 2686355 = 4029533) B4029533
theorem B1342921 : Blo 626299 1342921 := bstep (se 2 (by rfl) ⟨503595, by rfl⟩ : syracuseStep 1342921 = 1007191) B1007191
theorem B9698915 : Blo 626299 9698915 := bstep (se 1 (by rfl) ⟨7274186, by rfl⟩ : syracuseStep 9698915 = 14548373) B14548373
theorem B1933001 : Blo 626299 1933001 := bstep (se 2 (by rfl) ⟨724875, by rfl⟩ : syracuseStep 1933001 = 1449751) B1449751
theorem B1277711 : Blo 626299 1277711 := bstep (se 1 (by rfl) ⟨958283, by rfl⟩ : syracuseStep 1277711 = 1916567) B1916567
theorem B1507385 : Blo 626299 1507385 := bstep (se 2 (by rfl) ⟨565269, by rfl⟩ : syracuseStep 1507385 = 1130539) B1130539
theorem B8618147 : Blo 626299 8618147 := bstep (se 1 (by rfl) ⟨6463610, by rfl⟩ : syracuseStep 8618147 = 12927221) B12927221
theorem B3178763 : Blo 626299 3178763 := bstep (se 1 (by rfl) ⟨2384072, by rfl⟩ : syracuseStep 3178763 = 4768145) B4768145
theorem B1409633 : Blo 626299 1409633 := bstep (se 2 (by rfl) ⟨528612, by rfl⟩ : syracuseStep 1409633 = 1057225) B1057225
theorem B2392699 : Blo 626299 2392699 := bstep (se 1 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 2392699 = 3589049) B3589049
theorem B754375 : Blo 626299 754375 := bstep (se 1 (by rfl) ⟨565781, by rfl⟩ : syracuseStep 754375 = 1131563) B1131563
theorem B1409975 : Blo 626299 1409975 := bstep (se 1 (by rfl) ⟨1057481, by rfl⟩ : syracuseStep 1409975 = 2114963) B2114963
theorem B4031531 : Blo 626299 4031531 := bstep (se 1 (by rfl) ⟨3023648, by rfl⟩ : syracuseStep 4031531 = 6047297) B6047297
theorem B9045341 : Blo 626299 9045341 := bstep (se 3 (by rfl) ⟨1696001, by rfl⟩ : syracuseStep 9045341 = 3392003) B3392003
theorem B1148303 : Blo 626299 1148303 := bstep (se 1 (by rfl) ⟨861227, by rfl⟩ : syracuseStep 1148303 = 1722455) B1722455
theorem B3573193 : Blo 626299 3573193 := bstep (se 2 (by rfl) ⟨1339947, by rfl⟩ : syracuseStep 3573193 = 2679895) B2679895
theorem B2262491 : Blo 626299 2262491 := bstep (se 1 (by rfl) ⟨1696868, by rfl⟩ : syracuseStep 2262491 = 3393737) B3393737
theorem B7177733 : Blo 626299 7177733 := bstep (se 4 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 7177733 = 1345825) B1345825
theorem B1410569 : Blo 626299 1410569 := bstep (se 2 (by rfl) ⟨528963, by rfl⟩ : syracuseStep 1410569 = 1057927) B1057927
theorem B3180221 : Blo 626299 3180221 := bstep (se 3 (by rfl) ⟨596291, by rfl⟩ : syracuseStep 3180221 = 1192583) B1192583
theorem B1410911 : Blo 626299 1410911 := bstep (se 1 (by rfl) ⟨1058183, by rfl⟩ : syracuseStep 1410911 = 2116367) B2116367
theorem B3180383 : Blo 626299 3180383 := bstep (se 1 (by rfl) ⟨2385287, by rfl⟩ : syracuseStep 3180383 = 4770575) B4770575
theorem B1411091 : Blo 626299 1411091 := bstep (se 1 (by rfl) ⟨1058318, by rfl⟩ : syracuseStep 1411091 = 2116637) B2116637
theorem B1411433 : Blo 626299 1411433 := bstep (se 2 (by rfl) ⟨529287, by rfl⟩ : syracuseStep 1411433 = 1058575) B1058575
theorem B7179191 : Blo 626299 7179191 := bstep (se 1 (by rfl) ⟨5384393, by rfl⟩ : syracuseStep 7179191 = 10768787) B10768787
theorem B1412027 : Blo 626299 1412027 := bstep (se 1 (by rfl) ⟨1059020, by rfl⟩ : syracuseStep 1412027 = 2118041) B2118041
theorem B1412153 : Blo 626299 1412153 := bstep (se 2 (by rfl) ⟨529557, by rfl⟩ : syracuseStep 1412153 = 1059115) B1059115
theorem B3313021 : Blo 626299 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B1412495 : Blo 626299 1412495 := bstep (se 1 (by rfl) ⟨1059371, by rfl⟩ : syracuseStep 1412495 = 2118743) B2118743
theorem B1510921 : Blo 626299 1510921 := bstep (se 2 (by rfl) ⟨566595, by rfl⟩ : syracuseStep 1510921 = 1133191) B1133191
theorem B626299 : Blo 626299 626299 := bstep (se 1 (by rfl) ⟨469724, by rfl⟩ : syracuseStep 626299 = 939449) B939449
theorem B4034195 : Blo 626299 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B626351 : Blo 626299 626351 := bstep (se 1 (by rfl) ⟨469763, by rfl⟩ : syracuseStep 626351 = 939527) B939527
theorem B626375 : Blo 626299 626375 := bstep (se 1 (by rfl) ⟨469781, by rfl⟩ : syracuseStep 626375 = 939563) B939563
theorem B1412819 : Blo 626299 1412819 := bstep (se 1 (by rfl) ⟨1059614, by rfl⟩ : syracuseStep 1412819 = 2119229) B2119229
theorem B626395 : Blo 626299 626395 := bstep (se 1 (by rfl) ⟨469796, by rfl⟩ : syracuseStep 626395 = 939593) B939593
theorem B6524705 : Blo 626299 6524705 := bstep (se 2 (by rfl) ⟨2446764, by rfl⟩ : syracuseStep 6524705 = 4893529) B4893529
theorem B626471 : Blo 626299 626471 := bstep (se 1 (by rfl) ⟨469853, by rfl⟩ : syracuseStep 626471 = 939707) B939707
theorem B626511 : Blo 626299 626511 := bstep (se 1 (by rfl) ⟨469883, by rfl⟩ : syracuseStep 626511 = 939767) B939767
theorem B626527 : Blo 626299 626527 := bstep (se 1 (by rfl) ⟨469895, by rfl⟩ : syracuseStep 626527 = 939791) B939791
theorem B626555 : Blo 626299 626555 := bstep (se 1 (by rfl) ⟨469916, by rfl⟩ : syracuseStep 626555 = 939833) B939833
theorem B626607 : Blo 626299 626607 := bstep (se 1 (by rfl) ⟨469955, by rfl⟩ : syracuseStep 626607 = 939911) B939911
theorem B626631 : Blo 626299 626631 := bstep (se 1 (by rfl) ⟨469973, by rfl⟩ : syracuseStep 626631 = 939947) B939947
theorem B626651 : Blo 626299 626651 := bstep (se 1 (by rfl) ⟨469988, by rfl⟩ : syracuseStep 626651 = 939977) B939977
theorem B626727 : Blo 626299 626727 := bstep (se 1 (by rfl) ⟨470045, by rfl⟩ : syracuseStep 626727 = 940091) B940091
theorem B626767 : Blo 626299 626767 := bstep (se 1 (by rfl) ⟨470075, by rfl⟩ : syracuseStep 626767 = 940151) B940151
theorem B626783 : Blo 626299 626783 := bstep (se 1 (by rfl) ⟨470087, by rfl⟩ : syracuseStep 626783 = 940175) B940175
theorem B626811 : Blo 626299 626811 := bstep (se 1 (by rfl) ⟨470108, by rfl⟩ : syracuseStep 626811 = 940217) B940217
theorem B626863 : Blo 626299 626863 := bstep (se 1 (by rfl) ⟨470147, by rfl⟩ : syracuseStep 626863 = 940295) B940295
theorem B626887 : Blo 626299 626887 := bstep (se 1 (by rfl) ⟨470165, by rfl⟩ : syracuseStep 626887 = 940331) B940331
theorem B626907 : Blo 626299 626907 := bstep (se 1 (by rfl) ⟨470180, by rfl⟩ : syracuseStep 626907 = 940361) B940361
theorem B626983 : Blo 626299 626983 := bstep (se 1 (by rfl) ⟨470237, by rfl⟩ : syracuseStep 626983 = 940475) B940475
theorem B627023 : Blo 626299 627023 := bstep (se 1 (by rfl) ⟨470267, by rfl⟩ : syracuseStep 627023 = 940535) B940535
theorem B627039 : Blo 626299 627039 := bstep (se 1 (by rfl) ⟨470279, by rfl⟩ : syracuseStep 627039 = 940559) B940559
theorem B627067 : Blo 626299 627067 := bstep (se 1 (by rfl) ⟨470300, by rfl⟩ : syracuseStep 627067 = 940601) B940601
theorem B627119 : Blo 626299 627119 := bstep (se 1 (by rfl) ⟨470339, by rfl⟩ : syracuseStep 627119 = 940679) B940679
theorem B627143 : Blo 626299 627143 := bstep (se 1 (by rfl) ⟨470357, by rfl⟩ : syracuseStep 627143 = 940715) B940715
theorem B2265545 : Blo 626299 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B627163 : Blo 626299 627163 := bstep (se 1 (by rfl) ⟨470372, by rfl⟩ : syracuseStep 627163 = 940745) B940745
theorem B3183137 : Blo 626299 3183137 := bstep (se 2 (by rfl) ⟨1193676, by rfl⟩ : syracuseStep 3183137 = 2387353) B2387353
theorem B627239 : Blo 626299 627239 := bstep (se 1 (by rfl) ⟨470429, by rfl⟩ : syracuseStep 627239 = 940859) B940859
theorem B627279 : Blo 626299 627279 := bstep (se 1 (by rfl) ⟨470459, by rfl⟩ : syracuseStep 627279 = 940919) B940919
theorem B627295 : Blo 626299 627295 := bstep (se 1 (by rfl) ⟨470471, by rfl⟩ : syracuseStep 627295 = 940943) B940943
theorem B627323 : Blo 626299 627323 := bstep (se 1 (by rfl) ⟨470492, by rfl⟩ : syracuseStep 627323 = 940985) B940985
theorem B1413755 : Blo 626299 1413755 := bstep (se 1 (by rfl) ⟨1060316, by rfl⟩ : syracuseStep 1413755 = 2120633) B2120633
theorem B627375 : Blo 626299 627375 := bstep (se 1 (by rfl) ⟨470531, by rfl⟩ : syracuseStep 627375 = 941063) B941063
theorem B627399 : Blo 626299 627399 := bstep (se 1 (by rfl) ⟨470549, by rfl⟩ : syracuseStep 627399 = 941099) B941099
theorem B627419 : Blo 626299 627419 := bstep (se 1 (by rfl) ⟨470564, by rfl⟩ : syracuseStep 627419 = 941129) B941129
theorem B1413881 : Blo 626299 1413881 := bstep (se 2 (by rfl) ⟨530205, by rfl⟩ : syracuseStep 1413881 = 1060411) B1060411
theorem B627495 : Blo 626299 627495 := bstep (se 1 (by rfl) ⟨470621, by rfl⟩ : syracuseStep 627495 = 941243) B941243
theorem B627535 : Blo 626299 627535 := bstep (se 1 (by rfl) ⟨470651, by rfl⟩ : syracuseStep 627535 = 941303) B941303
theorem B627551 : Blo 626299 627551 := bstep (se 1 (by rfl) ⟨470663, by rfl⟩ : syracuseStep 627551 = 941327) B941327
theorem B955243 : Blo 626299 955243 := bstep (se 1 (by rfl) ⟨716432, by rfl⟩ : syracuseStep 955243 = 1432865) B1432865
theorem B627579 : Blo 626299 627579 := bstep (se 1 (by rfl) ⟨470684, by rfl⟩ : syracuseStep 627579 = 941369) B941369
theorem B627631 : Blo 626299 627631 := bstep (se 1 (by rfl) ⟨470723, by rfl⟩ : syracuseStep 627631 = 941447) B941447
theorem B627655 : Blo 626299 627655 := bstep (se 1 (by rfl) ⟨470741, by rfl⟩ : syracuseStep 627655 = 941483) B941483
theorem B627675 : Blo 626299 627675 := bstep (se 1 (by rfl) ⟨470756, by rfl⟩ : syracuseStep 627675 = 941513) B941513
theorem B4756481 : Blo 626299 4756481 := bstep (se 2 (by rfl) ⟨1783680, by rfl⟩ : syracuseStep 4756481 = 3567361) B3567361
theorem B1414151 : Blo 626299 1414151 := bstep (se 1 (by rfl) ⟨1060613, by rfl⟩ : syracuseStep 1414151 = 2121227) B2121227
theorem B627751 : Blo 626299 627751 := bstep (se 1 (by rfl) ⟨470813, by rfl⟩ : syracuseStep 627751 = 941627) B941627
theorem B627791 : Blo 626299 627791 := bstep (se 1 (by rfl) ⟨470843, by rfl⟩ : syracuseStep 627791 = 941687) B941687
theorem B1414223 : Blo 626299 1414223 := bstep (se 1 (by rfl) ⟨1060667, by rfl⟩ : syracuseStep 1414223 = 2121335) B2121335
theorem B627807 : Blo 626299 627807 := bstep (se 1 (by rfl) ⟨470855, by rfl⟩ : syracuseStep 627807 = 941711) B941711
theorem B627835 : Blo 626299 627835 := bstep (se 1 (by rfl) ⟨470876, by rfl⟩ : syracuseStep 627835 = 941753) B941753
theorem B9049259 : Blo 626299 9049259 := bstep (se 1 (by rfl) ⟨6786944, by rfl⟩ : syracuseStep 9049259 = 13573889) B13573889
theorem B627887 : Blo 626299 627887 := bstep (se 1 (by rfl) ⟨470915, by rfl⟩ : syracuseStep 627887 = 941831) B941831
theorem B627911 : Blo 626299 627911 := bstep (se 1 (by rfl) ⟨470933, by rfl⟩ : syracuseStep 627911 = 941867) B941867
theorem B4297931 : Blo 626299 4297931 := bstep (se 1 (by rfl) ⟨3223448, by rfl⟩ : syracuseStep 4297931 = 6446897) B6446897
theorem B627931 : Blo 626299 627931 := bstep (se 1 (by rfl) ⟨470948, by rfl⟩ : syracuseStep 627931 = 941897) B941897
theorem B628007 : Blo 626299 628007 := bstep (se 1 (by rfl) ⟨471005, by rfl⟩ : syracuseStep 628007 = 942011) B942011
theorem B628047 : Blo 626299 628047 := bstep (se 1 (by rfl) ⟨471035, by rfl⟩ : syracuseStep 628047 = 942071) B942071
theorem B628063 : Blo 626299 628063 := bstep (se 1 (by rfl) ⟨471047, by rfl⟩ : syracuseStep 628063 = 942095) B942095
theorem B628091 : Blo 626299 628091 := bstep (se 1 (by rfl) ⟨471068, by rfl⟩ : syracuseStep 628091 = 942137) B942137
theorem B628143 : Blo 626299 628143 := bstep (se 1 (by rfl) ⟨471107, by rfl⟩ : syracuseStep 628143 = 942215) B942215
theorem B628167 : Blo 626299 628167 := bstep (se 1 (by rfl) ⟨471125, by rfl⟩ : syracuseStep 628167 = 942251) B942251
theorem B628187 : Blo 626299 628187 := bstep (se 1 (by rfl) ⟨471140, by rfl⟩ : syracuseStep 628187 = 942281) B942281
theorem B1414619 : Blo 626299 1414619 := bstep (se 1 (by rfl) ⟨1060964, by rfl⟩ : syracuseStep 1414619 = 2121929) B2121929
theorem B628263 : Blo 626299 628263 := bstep (se 1 (by rfl) ⟨471197, by rfl⟩ : syracuseStep 628263 = 942395) B942395
theorem B628303 : Blo 626299 628303 := bstep (se 1 (by rfl) ⟨471227, by rfl⟩ : syracuseStep 628303 = 942455) B942455
theorem B628319 : Blo 626299 628319 := bstep (se 1 (by rfl) ⟨471239, by rfl⟩ : syracuseStep 628319 = 942479) B942479
theorem B10163809 : Blo 626299 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B33166945 : Blo 626299 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B628347 : Blo 626299 628347 := bstep (se 1 (by rfl) ⟨471260, by rfl⟩ : syracuseStep 628347 = 942521) B942521
theorem B628399 : Blo 626299 628399 := bstep (se 1 (by rfl) ⟨471299, by rfl⟩ : syracuseStep 628399 = 942599) B942599
theorem B628423 : Blo 626299 628423 := bstep (se 1 (by rfl) ⟨471317, by rfl⟩ : syracuseStep 628423 = 942635) B942635
theorem B628443 : Blo 626299 628443 := bstep (se 1 (by rfl) ⟨471332, by rfl⟩ : syracuseStep 628443 = 942665) B942665
theorem B628519 : Blo 626299 628519 := bstep (se 1 (by rfl) ⟨471389, by rfl⟩ : syracuseStep 628519 = 942779) B942779
theorem B628559 : Blo 626299 628559 := bstep (se 1 (by rfl) ⟨471419, by rfl⟩ : syracuseStep 628559 = 942839) B942839
theorem B628575 : Blo 626299 628575 := bstep (se 1 (by rfl) ⟨471431, by rfl⟩ : syracuseStep 628575 = 942863) B942863
theorem B628603 : Blo 626299 628603 := bstep (se 1 (by rfl) ⟨471452, by rfl⟩ : syracuseStep 628603 = 942905) B942905
theorem B628655 : Blo 626299 628655 := bstep (se 1 (by rfl) ⟨471491, by rfl⟩ : syracuseStep 628655 = 942983) B942983
theorem B1415087 : Blo 626299 1415087 := bstep (se 1 (by rfl) ⟨1061315, by rfl⟩ : syracuseStep 1415087 = 2122631) B2122631
theorem B628679 : Blo 626299 628679 := bstep (se 1 (by rfl) ⟨471509, by rfl⟩ : syracuseStep 628679 = 943019) B943019
theorem B628699 : Blo 626299 628699 := bstep (se 1 (by rfl) ⟨471524, by rfl⟩ : syracuseStep 628699 = 943049) B943049
theorem B628775 : Blo 626299 628775 := bstep (se 1 (by rfl) ⟨471581, by rfl⟩ : syracuseStep 628775 = 943163) B943163
theorem B628815 : Blo 626299 628815 := bstep (se 1 (by rfl) ⟨471611, by rfl⟩ : syracuseStep 628815 = 943223) B943223
theorem B628831 : Blo 626299 628831 := bstep (se 1 (by rfl) ⟨471623, by rfl⟩ : syracuseStep 628831 = 943247) B943247
theorem B628859 : Blo 626299 628859 := bstep (se 1 (by rfl) ⟨471644, by rfl⟩ : syracuseStep 628859 = 943289) B943289
theorem B1415339 : Blo 626299 1415339 := bstep (se 1 (by rfl) ⟨1061504, by rfl⟩ : syracuseStep 1415339 = 2123009) B2123009
theorem B628911 : Blo 626299 628911 := bstep (se 1 (by rfl) ⟨471683, by rfl⟩ : syracuseStep 628911 = 943367) B943367
theorem B628935 : Blo 626299 628935 := bstep (se 1 (by rfl) ⟨471701, by rfl⟩ : syracuseStep 628935 = 943403) B943403
theorem B628955 : Blo 626299 628955 := bstep (se 1 (by rfl) ⟨471716, by rfl⟩ : syracuseStep 628955 = 943433) B943433
theorem B4036837 : Blo 626299 4036837 := bstep (se 4 (by rfl) ⟨378453, by rfl⟩ : syracuseStep 4036837 = 756907) B756907
theorem B629031 : Blo 626299 629031 := bstep (se 1 (by rfl) ⟨471773, by rfl⟩ : syracuseStep 629031 = 943547) B943547
theorem B629071 : Blo 626299 629071 := bstep (se 1 (by rfl) ⟨471803, by rfl⟩ : syracuseStep 629071 = 943607) B943607
theorem B629087 : Blo 626299 629087 := bstep (se 1 (by rfl) ⟨471815, by rfl⟩ : syracuseStep 629087 = 943631) B943631
theorem B629115 : Blo 626299 629115 := bstep (se 1 (by rfl) ⟨471836, by rfl⟩ : syracuseStep 629115 = 943673) B943673
theorem B629167 : Blo 626299 629167 := bstep (se 1 (by rfl) ⟨471875, by rfl⟩ : syracuseStep 629167 = 943751) B943751
theorem B629191 : Blo 626299 629191 := bstep (se 1 (by rfl) ⟨471893, by rfl⟩ : syracuseStep 629191 = 943787) B943787
theorem B629211 : Blo 626299 629211 := bstep (se 1 (by rfl) ⟨471908, by rfl⟩ : syracuseStep 629211 = 943817) B943817
theorem B629287 : Blo 626299 629287 := bstep (se 1 (by rfl) ⟨471965, by rfl⟩ : syracuseStep 629287 = 943931) B943931
theorem B629327 : Blo 626299 629327 := bstep (se 1 (by rfl) ⟨471995, by rfl⟩ : syracuseStep 629327 = 943991) B943991
theorem B629343 : Blo 626299 629343 := bstep (se 1 (by rfl) ⟨472007, by rfl⟩ : syracuseStep 629343 = 944015) B944015
theorem B629371 : Blo 626299 629371 := bstep (se 1 (by rfl) ⟨472028, by rfl⟩ : syracuseStep 629371 = 944057) B944057
theorem B1514123 : Blo 626299 1514123 := bstep (se 1 (by rfl) ⟨1135592, by rfl⟩ : syracuseStep 1514123 = 2271185) B2271185
theorem B629423 : Blo 626299 629423 := bstep (se 1 (by rfl) ⟨472067, by rfl⟩ : syracuseStep 629423 = 944135) B944135
theorem B1612487 : Blo 626299 1612487 := bstep (se 1 (by rfl) ⟨1209365, by rfl⟩ : syracuseStep 1612487 = 2418731) B2418731
theorem B1415879 : Blo 626299 1415879 := bstep (se 1 (by rfl) ⟨1061909, by rfl⟩ : syracuseStep 1415879 = 2123819) B2123819
theorem B629447 : Blo 626299 629447 := bstep (se 1 (by rfl) ⟨472085, by rfl⟩ : syracuseStep 629447 = 944171) B944171
theorem B629467 : Blo 626299 629467 := bstep (se 1 (by rfl) ⟨472100, by rfl⟩ : syracuseStep 629467 = 944201) B944201
theorem B629543 : Blo 626299 629543 := bstep (se 1 (by rfl) ⟨472157, by rfl⟩ : syracuseStep 629543 = 944315) B944315
theorem B629583 : Blo 626299 629583 := bstep (se 1 (by rfl) ⟨472187, by rfl⟩ : syracuseStep 629583 = 944375) B944375
theorem B629599 : Blo 626299 629599 := bstep (se 1 (by rfl) ⟨472199, by rfl⟩ : syracuseStep 629599 = 944399) B944399
theorem B629627 : Blo 626299 629627 := bstep (se 1 (by rfl) ⟨472220, by rfl⟩ : syracuseStep 629627 = 944441) B944441
theorem B629679 : Blo 626299 629679 := bstep (se 1 (by rfl) ⟨472259, by rfl⟩ : syracuseStep 629679 = 944519) B944519
theorem B3218359 : Blo 626299 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B629703 : Blo 626299 629703 := bstep (se 1 (by rfl) ⟨472277, by rfl⟩ : syracuseStep 629703 = 944555) B944555
theorem B629723 : Blo 626299 629723 := bstep (se 1 (by rfl) ⟨472292, by rfl⟩ : syracuseStep 629723 = 944585) B944585
theorem B1809427 : Blo 626299 1809427 := bstep (se 1 (by rfl) ⟨1357070, by rfl⟩ : syracuseStep 1809427 = 2714141) B2714141
theorem B629799 : Blo 626299 629799 := bstep (se 1 (by rfl) ⟨472349, by rfl⟩ : syracuseStep 629799 = 944699) B944699
theorem B629839 : Blo 626299 629839 := bstep (se 1 (by rfl) ⟨472379, by rfl⟩ : syracuseStep 629839 = 944759) B944759
theorem B629855 : Blo 626299 629855 := bstep (se 1 (by rfl) ⟨472391, by rfl⟩ : syracuseStep 629855 = 944783) B944783
theorem B629883 : Blo 626299 629883 := bstep (se 1 (by rfl) ⟨472412, by rfl⟩ : syracuseStep 629883 = 944825) B944825
theorem B629935 : Blo 626299 629935 := bstep (se 1 (by rfl) ⟨472451, by rfl⟩ : syracuseStep 629935 = 944903) B944903
theorem B629959 : Blo 626299 629959 := bstep (se 1 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 629959 = 944939) B944939
theorem B629979 : Blo 626299 629979 := bstep (se 1 (by rfl) ⟨472484, by rfl⟩ : syracuseStep 629979 = 944969) B944969
theorem B630055 : Blo 626299 630055 := bstep (se 1 (by rfl) ⟨472541, by rfl⟩ : syracuseStep 630055 = 945083) B945083
theorem B630095 : Blo 626299 630095 := bstep (se 1 (by rfl) ⟨472571, by rfl⟩ : syracuseStep 630095 = 945143) B945143
theorem B630111 : Blo 626299 630111 := bstep (se 1 (by rfl) ⟨472583, by rfl⟩ : syracuseStep 630111 = 945167) B945167
theorem B630139 : Blo 626299 630139 := bstep (se 1 (by rfl) ⟨472604, by rfl⟩ : syracuseStep 630139 = 945209) B945209
theorem B2039165 : Blo 626299 2039165 := bstep (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) B764687
theorem B630191 : Blo 626299 630191 := bstep (se 1 (by rfl) ⟨472643, by rfl⟩ : syracuseStep 630191 = 945287) B945287
theorem B630215 : Blo 626299 630215 := bstep (se 1 (by rfl) ⟨472661, by rfl⟩ : syracuseStep 630215 = 945323) B945323
theorem B630235 : Blo 626299 630235 := bstep (se 1 (by rfl) ⟨472676, by rfl⟩ : syracuseStep 630235 = 945353) B945353
theorem B3186215 : Blo 626299 3186215 := bstep (se 1 (by rfl) ⟨2389661, by rfl⟩ : syracuseStep 3186215 = 4779323) B4779323
theorem B1416743 : Blo 626299 1416743 := bstep (se 1 (by rfl) ⟨1062557, by rfl⟩ : syracuseStep 1416743 = 2125115) B2125115
theorem B892615 : Blo 626299 892615 := bstep (se 1 (by rfl) ⟨669461, by rfl⟩ : syracuseStep 892615 = 1338923) B1338923
theorem B1417067 : Blo 626299 1417067 := bstep (se 1 (by rfl) ⟨1062800, by rfl⟩ : syracuseStep 1417067 = 2125601) B2125601
theorem B1417121 : Blo 626299 1417121 := bstep (se 2 (by rfl) ⟨531420, by rfl⟩ : syracuseStep 1417121 = 1062841) B1062841
theorem B1417463 : Blo 626299 1417463 := bstep (se 1 (by rfl) ⟨1063097, by rfl⟩ : syracuseStep 1417463 = 2126195) B2126195
theorem B9085243 : Blo 626299 9085243 := bstep (se 1 (by rfl) ⟨6813932, by rfl⟩ : syracuseStep 9085243 = 13627865) B13627865
theorem B1057097 : Blo 626299 1057097 := bstep (se 2 (by rfl) ⟨396411, by rfl⟩ : syracuseStep 1057097 = 792823) B792823
theorem B2269583 : Blo 626299 2269583 := bstep (se 1 (by rfl) ⟨1702187, by rfl⟩ : syracuseStep 2269583 = 3404375) B3404375
theorem B6038225 : Blo 626299 6038225 := bstep (se 2 (by rfl) ⟨2264334, by rfl⟩ : syracuseStep 6038225 = 4528669) B4528669
theorem B1057529 : Blo 626299 1057529 := bstep (se 2 (by rfl) ⟨396573, by rfl⟩ : syracuseStep 1057529 = 793147) B793147
theorem B1418057 : Blo 626299 1418057 := bstep (se 2 (by rfl) ⟨531771, by rfl⟩ : syracuseStep 1418057 = 1063543) B1063543
theorem B1057711 : Blo 626299 1057711 := bstep (se 1 (by rfl) ⟨793283, by rfl⟩ : syracuseStep 1057711 = 1586567) B1586567
theorem B1057799 : Blo 626299 1057799 := bstep (se 1 (by rfl) ⟨793349, by rfl⟩ : syracuseStep 1057799 = 1586699) B1586699
theorem B4826305 : Blo 626299 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B1189075 : Blo 626299 1189075 := bstep (se 1 (by rfl) ⟨891806, by rfl⟩ : syracuseStep 1189075 = 1783613) B1783613
theorem B4302071 : Blo 626299 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B4760855 : Blo 626299 4760855 := bstep (se 1 (by rfl) ⟨3570641, by rfl⟩ : syracuseStep 4760855 = 7141283) B7141283
theorem B1058143 : Blo 626299 1058143 := bstep (se 1 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 1058143 = 1587215) B1587215
theorem B1058231 : Blo 626299 1058231 := bstep (se 1 (by rfl) ⟨793673, by rfl⟩ : syracuseStep 1058231 = 1587347) B1587347
theorem B3188321 : Blo 626299 3188321 := bstep (se 2 (by rfl) ⟨1195620, by rfl⟩ : syracuseStep 3188321 = 2391241) B2391241
theorem B1812385 : Blo 626299 1812385 := bstep (se 2 (by rfl) ⟨679644, by rfl⟩ : syracuseStep 1812385 = 1359289) B1359289
theorem B1189819 : Blo 626299 1189819 := bstep (se 1 (by rfl) ⟨892364, by rfl⟩ : syracuseStep 1189819 = 1784729) B1784729
theorem B1058825 : Blo 626299 1058825 := bstep (se 2 (by rfl) ⟨397059, by rfl⟩ : syracuseStep 1058825 = 794119) B794119
theorem B796711 : Blo 626299 796711 := bstep (se 1 (by rfl) ⟨597533, by rfl⟩ : syracuseStep 796711 = 1195067) B1195067
theorem B1058987 : Blo 626299 1058987 := bstep (se 1 (by rfl) ⟨794240, by rfl⟩ : syracuseStep 1058987 = 1588481) B1588481
theorem B797035 : Blo 626299 797035 := bstep (se 1 (by rfl) ⟨597776, by rfl⟩ : syracuseStep 797035 = 1195553) B1195553
theorem B6465943 : Blo 626299 6465943 := bstep (se 1 (by rfl) ⟨4849457, by rfl⟩ : syracuseStep 6465943 = 9698915) B9698915
theorem B1190305 : Blo 626299 1190305 := bstep (se 2 (by rfl) ⟨446364, by rfl⟩ : syracuseStep 1190305 = 892729) B892729
theorem B1288667 : Blo 626299 1288667 := bstep (se 1 (by rfl) ⟨966500, by rfl⟩ : syracuseStep 1288667 = 1933001) B1933001
theorem B3811873 : Blo 626299 3811873 := bstep (se 2 (by rfl) ⟨1429452, by rfl⟩ : syracuseStep 3811873 = 2858905) B2858905
theorem B1059385 : Blo 626299 1059385 := bstep (se 2 (by rfl) ⟨397269, by rfl⟩ : syracuseStep 1059385 = 794539) B794539
theorem B2042491 : Blo 626299 2042491 := bstep (se 1 (by rfl) ⟨1531868, by rfl⟩ : syracuseStep 2042491 = 3063737) B3063737
theorem B1059527 : Blo 626299 1059527 := bstep (se 1 (by rfl) ⟨794645, by rfl⟩ : syracuseStep 1059527 = 1589291) B1589291
theorem B4762313 : Blo 626299 4762313 := bstep (se 2 (by rfl) ⟨1785867, by rfl⟩ : syracuseStep 4762313 = 3571735) B3571735
theorem B1223417 : Blo 626299 1223417 := bstep (se 2 (by rfl) ⟨458781, by rfl⟩ : syracuseStep 1223417 = 917563) B917563
theorem B1059689 : Blo 626299 1059689 := bstep (se 2 (by rfl) ⟨397383, by rfl⟩ : syracuseStep 1059689 = 794767) B794767
theorem B8072081 : Blo 626299 8072081 := bstep (se 2 (by rfl) ⟨3027030, by rfl⟩ : syracuseStep 8072081 = 6054061) B6054061
theorem B1190875 : Blo 626299 1190875 := bstep (se 1 (by rfl) ⟨893156, by rfl⟩ : syracuseStep 1190875 = 1786313) B1786313
theorem B3189779 : Blo 626299 3189779 := bstep (se 1 (by rfl) ⟨2392334, by rfl⟩ : syracuseStep 3189779 = 4784669) B4784669
theorem B2010359 : Blo 626299 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B1060087 : Blo 626299 1060087 := bstep (se 1 (by rfl) ⟨795065, by rfl⟩ : syracuseStep 1060087 = 1590131) B1590131
theorem B4304119 : Blo 626299 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B896351 : Blo 626299 896351 := bstep (se 1 (by rfl) ⟨672263, by rfl⟩ : syracuseStep 896351 = 1344527) B1344527
theorem B1060283 : Blo 626299 1060283 := bstep (se 1 (by rfl) ⟨795212, by rfl⟩ : syracuseStep 1060283 = 1590425) B1590425
theorem B1060391 : Blo 626299 1060391 := bstep (se 1 (by rfl) ⟨795293, by rfl⟩ : syracuseStep 1060391 = 1590587) B1590587
theorem B4533857 : Blo 626299 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B18132659 : Blo 626299 18132659 := bstep (se 1 (by rfl) ⟨13599494, by rfl⟩ : syracuseStep 18132659 = 27198989) B27198989
theorem B896761 : Blo 626299 896761 := bstep (se 2 (by rfl) ⟨336285, by rfl⟩ : syracuseStep 896761 = 672571) B672571
theorem B1060681 : Blo 626299 1060681 := bstep (se 2 (by rfl) ⟨397755, by rfl⟩ : syracuseStep 1060681 = 795511) B795511
theorem B3354463 : Blo 626299 3354463 := bstep (se 1 (by rfl) ⟨2515847, by rfl⟩ : syracuseStep 3354463 = 5031695) B5031695
theorem B1060715 : Blo 626299 1060715 := bstep (se 1 (by rfl) ⟨795536, by rfl⟩ : syracuseStep 1060715 = 1591073) B1591073
theorem B897103 : Blo 626299 897103 := bstep (se 1 (by rfl) ⟨672827, by rfl⟩ : syracuseStep 897103 = 1345655) B1345655
theorem B1061113 : Blo 626299 1061113 := bstep (se 2 (by rfl) ⟨397917, by rfl⟩ : syracuseStep 1061113 = 795835) B795835
theorem B1257911 : Blo 626299 1257911 := bstep (se 1 (by rfl) ⟨943433, by rfl⟩ : syracuseStep 1257911 = 1886867) B1886867
theorem B1061383 : Blo 626299 1061383 := bstep (se 1 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 1061383 = 1592075) B1592075
theorem B2011999 : Blo 626299 2011999 := bstep (se 1 (by rfl) ⟨1508999, by rfl⟩ : syracuseStep 2011999 = 3017999) B3017999
theorem B1586081 : Blo 626299 1586081 := bstep (se 2 (by rfl) ⟨594780, by rfl⟩ : syracuseStep 1586081 = 1189561) B1189561
theorem B1061815 : Blo 626299 1061815 := bstep (se 1 (by rfl) ⟨796361, by rfl⟩ : syracuseStep 1061815 = 1592723) B1592723
theorem B4371421 : Blo 626299 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B1193039 : Blo 626299 1193039 := bstep (se 1 (by rfl) ⟨894779, by rfl⟩ : syracuseStep 1193039 = 1789559) B1789559
theorem B1062011 : Blo 626299 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B25801877 : Blo 626299 25801877 := bstep (se 6 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 25801877 = 1209463) B1209463
theorem B1586537 : Blo 626299 1586537 := bstep (se 2 (by rfl) ⟨594951, by rfl⟩ : syracuseStep 1586537 = 1189903) B1189903
theorem B8697289 : Blo 626299 8697289 := bstep (se 2 (by rfl) ⟨3261483, by rfl⟩ : syracuseStep 8697289 = 6522967) B6522967
theorem B1062409 : Blo 626299 1062409 := bstep (se 2 (by rfl) ⟨398403, by rfl⟩ : syracuseStep 1062409 = 796807) B796807
theorem B1062571 : Blo 626299 1062571 := bstep (se 1 (by rfl) ⟨796928, by rfl⟩ : syracuseStep 1062571 = 1593857) B1593857
theorem B2012921 : Blo 626299 2012921 := bstep (se 2 (by rfl) ⟨754845, by rfl⟩ : syracuseStep 2012921 = 1509691) B1509691
theorem B3389303 : Blo 626299 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B1783727 : Blo 626299 1783727 := bstep (se 1 (by rfl) ⟨1337795, by rfl⟩ : syracuseStep 1783727 = 2675591) B2675591
theorem B10729421 : Blo 626299 10729421 := bstep (se 3 (by rfl) ⟨2011766, by rfl⟩ : syracuseStep 10729421 = 4023533) B4023533
theorem B1062875 : Blo 626299 1062875 := bstep (se 1 (by rfl) ⟨797156, by rfl⟩ : syracuseStep 1062875 = 1594313) B1594313
theorem B1194041 : Blo 626299 1194041 := bstep (se 2 (by rfl) ⟨447765, by rfl⟩ : syracuseStep 1194041 = 895531) B895531
theorem B1063111 : Blo 626299 1063111 := bstep (se 1 (by rfl) ⟨797333, by rfl⟩ : syracuseStep 1063111 = 1594667) B1594667
theorem B3586315 : Blo 626299 3586315 := bstep (se 1 (by rfl) ⟨2689736, by rfl⟩ : syracuseStep 3586315 = 5379473) B5379473
theorem B5355827 : Blo 626299 5355827 := bstep (se 1 (by rfl) ⟨4016870, by rfl⟩ : syracuseStep 5355827 = 8033741) B8033741
theorem B1128809 : Blo 626299 1128809 := bstep (se 2 (by rfl) ⟨423303, by rfl⟩ : syracuseStep 1128809 = 846607) B846607
theorem B1063273 : Blo 626299 1063273 := bstep (se 2 (by rfl) ⟨398727, by rfl⟩ : syracuseStep 1063273 = 797455) B797455
theorem B1587721 : Blo 626299 1587721 := bstep (se 2 (by rfl) ⟨595395, by rfl⟩ : syracuseStep 1587721 = 1190791) B1190791
theorem B1784683 : Blo 626299 1784683 := bstep (se 1 (by rfl) ⟨1338512, by rfl⟩ : syracuseStep 1784683 = 2677025) B2677025
theorem B965711 : Blo 626299 965711 := bstep (se 1 (by rfl) ⟨724283, by rfl⟩ : syracuseStep 965711 = 1448567) B1448567
theorem B1784911 : Blo 626299 1784911 := bstep (se 1 (by rfl) ⟨1338683, by rfl⟩ : syracuseStep 1784911 = 2677367) B2677367
theorem B4537547 : Blo 626299 4537547 := bstep (se 1 (by rfl) ⟨3403160, by rfl⟩ : syracuseStep 4537547 = 6806321) B6806321
theorem B7618187 : Blo 626299 7618187 := bstep (se 1 (by rfl) ⟨5713640, by rfl⟩ : syracuseStep 7618187 = 11427281) B11427281
theorem B3587773 : Blo 626299 3587773 := bstep (se 3 (by rfl) ⟨672707, by rfl⟩ : syracuseStep 3587773 = 1345415) B1345415
theorem B6438689 : Blo 626299 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B2146121 : Blo 626299 2146121 := bstep (se 2 (by rfl) ⟨804795, by rfl⟩ : syracuseStep 2146121 = 1609591) B1609591
theorem B1589179 : Blo 626299 1589179 := bstep (se 1 (by rfl) ⟨1191884, by rfl⟩ : syracuseStep 1589179 = 2383769) B2383769
theorem B1196039 : Blo 626299 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B4243513 : Blo 626299 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B2015549 : Blo 626299 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B967087 : Blo 626299 967087 := bstep (se 1 (by rfl) ⟨725315, by rfl⟩ : syracuseStep 967087 = 1450631) B1450631
theorem B1130927 : Blo 626299 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B1196471 : Blo 626299 1196471 := bstep (se 1 (by rfl) ⟨897353, by rfl⟩ : syracuseStep 1196471 = 1794707) B1794707
theorem B32654029 : Blo 626299 32654029 := bstep (se 3 (by rfl) ⟨6122630, by rfl⟩ : syracuseStep 32654029 = 12245261) B12245261
theorem B2114423 : Blo 626299 2114423 := bstep (se 1 (by rfl) ⟨1585817, by rfl⟩ : syracuseStep 2114423 = 3171635) B3171635
theorem B14468015 : Blo 626299 14468015 := bstep (se 1 (by rfl) ⟨10851011, by rfl⟩ : syracuseStep 14468015 = 21702023) B21702023
theorem B2114639 : Blo 626299 2114639 := bstep (se 1 (by rfl) ⟨1585979, by rfl⟩ : syracuseStep 2114639 = 3171959) B3171959
theorem B9684139 : Blo 626299 9684139 := bstep (se 1 (by rfl) ⟨7263104, by rfl⟩ : syracuseStep 9684139 = 14526209) B14526209
theorem B2115017 : Blo 626299 2115017 := bstep (se 2 (by rfl) ⟨793131, by rfl⟩ : syracuseStep 2115017 = 1586263) B1586263
theorem B1131995 : Blo 626299 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B1787417 : Blo 626299 1787417 := bstep (se 2 (by rfl) ⟨670281, by rfl⟩ : syracuseStep 1787417 = 1340563) B1340563
theorem B706171 : Blo 626299 706171 := bstep (se 1 (by rfl) ⟨529628, by rfl⟩ : syracuseStep 706171 = 1059257) B1059257
theorem B2115287 : Blo 626299 2115287 := bstep (se 1 (by rfl) ⟨1586465, by rfl⟩ : syracuseStep 2115287 = 3172931) B3172931
theorem B4769603 : Blo 626299 4769603 := bstep (se 1 (by rfl) ⟨3577202, by rfl⟩ : syracuseStep 4769603 = 7154405) B7154405
theorem B7161695 : Blo 626299 7161695 := bstep (se 1 (by rfl) ⟨5371271, by rfl⟩ : syracuseStep 7161695 = 10742543) B10742543
theorem B2115503 : Blo 626299 2115503 := bstep (se 1 (by rfl) ⟨1586627, by rfl⟩ : syracuseStep 2115503 = 3173255) B3173255
theorem B706639 : Blo 626299 706639 := bstep (se 1 (by rfl) ⟨529979, by rfl⟩ : syracuseStep 706639 = 1059959) B1059959
theorem B707035 : Blo 626299 707035 := bstep (se 1 (by rfl) ⟨530276, by rfl⟩ : syracuseStep 707035 = 1060553) B1060553
theorem B1591771 : Blo 626299 1591771 := bstep (se 1 (by rfl) ⟨1193828, by rfl⟩ : syracuseStep 1591771 = 2387657) B2387657
theorem B2411293 : Blo 626299 2411293 := bstep (se 3 (by rfl) ⟨452117, by rfl⟩ : syracuseStep 2411293 = 904235) B904235
theorem B2378591 : Blo 626299 2378591 := bstep (se 1 (by rfl) ⟨1783943, by rfl⟩ : syracuseStep 2378591 = 3567887) B3567887
theorem B2378605 : Blo 626299 2378605 := bstep (se 3 (by rfl) ⟨445988, by rfl⟩ : syracuseStep 2378605 = 891977) B891977
theorem B707503 : Blo 626299 707503 := bstep (se 1 (by rfl) ⟨530627, by rfl⟩ : syracuseStep 707503 = 1061255) B1061255
theorem B1362863 : Blo 626299 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B1592399 : Blo 626299 1592399 := bstep (se 1 (by rfl) ⟨1194299, by rfl⟩ : syracuseStep 1592399 = 2388599) B2388599
theorem B2378909 : Blo 626299 2378909 := bstep (se 3 (by rfl) ⟨446045, by rfl⟩ : syracuseStep 2378909 = 892091) B892091
theorem B1133897 : Blo 626299 1133897 := bstep (se 2 (by rfl) ⟨425211, by rfl⟩ : syracuseStep 1133897 = 850423) B850423
theorem B707935 : Blo 626299 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B6802861 : Blo 626299 6802861 := bstep (se 3 (by rfl) ⟨1275536, by rfl⟩ : syracuseStep 6802861 = 2551073) B2551073
theorem B2182601 : Blo 626299 2182601 := bstep (se 2 (by rfl) ⟨818475, by rfl⟩ : syracuseStep 2182601 = 1636951) B1636951
theorem B708295 : Blo 626299 708295 := bstep (se 1 (by rfl) ⟨531221, by rfl⟩ : syracuseStep 708295 = 1062443) B1062443
theorem B1593047 : Blo 626299 1593047 := bstep (se 1 (by rfl) ⟨1194785, by rfl⟩ : syracuseStep 1593047 = 2389571) B2389571
theorem B2379563 : Blo 626299 2379563 := bstep (se 1 (by rfl) ⟨1784672, by rfl⟩ : syracuseStep 2379563 = 3569345) B3569345
theorem B2117879 : Blo 626299 2117879 := bstep (se 1 (by rfl) ⟨1588409, by rfl⟩ : syracuseStep 2117879 = 3176819) B3176819
theorem B1790333 : Blo 626299 1790333 := bstep (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) B671375
theorem B2118203 : Blo 626299 2118203 := bstep (se 1 (by rfl) ⟨1588652, by rfl⟩ : syracuseStep 2118203 = 3177305) B3177305
theorem B3232315 : Blo 626299 3232315 := bstep (se 1 (by rfl) ⟨2424236, by rfl⟩ : syracuseStep 3232315 = 4848473) B4848473
theorem B1790561 : Blo 626299 1790561 := bstep (se 2 (by rfl) ⟨671460, by rfl⟩ : syracuseStep 1790561 = 1342921) B1342921
theorem B5100205 : Blo 626299 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B2118473 : Blo 626299 2118473 := bstep (se 2 (by rfl) ⟨794427, by rfl⟩ : syracuseStep 2118473 = 1588855) B1588855
theorem B1790903 : Blo 626299 1790903 := bstep (se 1 (by rfl) ⟨1343177, by rfl⟩ : syracuseStep 1790903 = 2686355) B2686355
theorem B5100563 : Blo 626299 5100563 := bstep (se 1 (by rfl) ⟨3825422, by rfl⟩ : syracuseStep 5100563 = 7650845) B7650845
theorem B3823013 : Blo 626299 3823013 := bstep (se 4 (by rfl) ⟨358407, by rfl⟩ : syracuseStep 3823013 = 716815) B716815
theorem B1004987 : Blo 626299 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B939599 : Blo 626299 939599 := bstep (se 1 (by rfl) ⟨704699, by rfl⟩ : syracuseStep 939599 = 1409399) B1409399
theorem B16307905 : Blo 626299 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B939719 : Blo 626299 939719 := bstep (se 1 (by rfl) ⟨704789, by rfl⟩ : syracuseStep 939719 = 1409579) B1409579
theorem B2381521 : Blo 626299 2381521 := bstep (se 2 (by rfl) ⟨893070, by rfl⟩ : syracuseStep 2381521 = 1786141) B1786141
theorem B2545481 : Blo 626299 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B939881 : Blo 626299 939881 := bstep (se 2 (by rfl) ⟨352455, by rfl⟩ : syracuseStep 939881 = 704911) B704911
theorem B5363617 : Blo 626299 5363617 := bstep (se 2 (by rfl) ⟨2011356, by rfl⟩ : syracuseStep 5363617 = 4022713) B4022713
theorem B939959 : Blo 626299 939959 := bstep (se 1 (by rfl) ⟨704969, by rfl⟩ : syracuseStep 939959 = 1409939) B1409939
theorem B2119607 : Blo 626299 2119607 := bstep (se 1 (by rfl) ⟨1589705, by rfl⟩ : syracuseStep 2119607 = 3179411) B3179411
theorem B939995 : Blo 626299 939995 := bstep (se 1 (by rfl) ⟨704996, by rfl⟩ : syracuseStep 939995 = 1409993) B1409993
theorem B2381825 : Blo 626299 2381825 := bstep (se 2 (by rfl) ⟨893184, by rfl⟩ : syracuseStep 2381825 = 1786369) B1786369
theorem B1792019 : Blo 626299 1792019 := bstep (se 1 (by rfl) ⟨1344014, by rfl⟩ : syracuseStep 1792019 = 2688029) B2688029
theorem B4773977 : Blo 626299 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B4839587 : Blo 626299 4839587 := bstep (se 1 (by rfl) ⟨3629690, by rfl⟩ : syracuseStep 4839587 = 7259381) B7259381
theorem B1792361 : Blo 626299 1792361 := bstep (se 2 (by rfl) ⟨672135, by rfl⟩ : syracuseStep 1792361 = 1344271) B1344271
theorem B940463 : Blo 626299 940463 := bstep (se 1 (by rfl) ⟨705347, by rfl⟩ : syracuseStep 940463 = 1410695) B1410695
theorem B2382281 : Blo 626299 2382281 := bstep (se 2 (by rfl) ⟨893355, by rfl⟩ : syracuseStep 2382281 = 1786711) B1786711
theorem B1792475 : Blo 626299 1792475 := bstep (se 1 (by rfl) ⟨1344356, by rfl⟩ : syracuseStep 1792475 = 2688713) B2688713
theorem B940553 : Blo 626299 940553 := bstep (se 2 (by rfl) ⟨352707, by rfl⟩ : syracuseStep 940553 = 705415) B705415
theorem B2120201 : Blo 626299 2120201 := bstep (se 2 (by rfl) ⟨795075, by rfl⟩ : syracuseStep 2120201 = 1590151) B1590151
theorem B940583 : Blo 626299 940583 := bstep (se 1 (by rfl) ⟨705437, by rfl⟩ : syracuseStep 940583 = 1410875) B1410875
theorem B940667 : Blo 626299 940667 := bstep (se 1 (by rfl) ⟨705500, by rfl⟩ : syracuseStep 940667 = 1411001) B1411001
theorem B12049073 : Blo 626299 12049073 := bstep (se 2 (by rfl) ⟨4518402, by rfl⟩ : syracuseStep 12049073 = 9036805) B9036805
theorem B940793 : Blo 626299 940793 := bstep (se 2 (by rfl) ⟨352797, by rfl⟩ : syracuseStep 940793 = 705595) B705595
theorem B940895 : Blo 626299 940895 := bstep (se 1 (by rfl) ⟨705671, by rfl⟩ : syracuseStep 940895 = 1411343) B1411343
theorem B940907 : Blo 626299 940907 := bstep (se 1 (by rfl) ⟨705680, by rfl⟩ : syracuseStep 940907 = 1411361) B1411361
theorem B2382767 : Blo 626299 2382767 := bstep (se 1 (by rfl) ⟨1787075, by rfl⟩ : syracuseStep 2382767 = 3574151) B3574151
theorem B1006601 : Blo 626299 1006601 := bstep (se 2 (by rfl) ⟨377475, by rfl⟩ : syracuseStep 1006601 = 754951) B754951
theorem B941135 : Blo 626299 941135 := bstep (se 1 (by rfl) ⟨705851, by rfl⟩ : syracuseStep 941135 = 1411703) B1411703
theorem B941255 : Blo 626299 941255 := bstep (se 1 (by rfl) ⟨705941, by rfl⟩ : syracuseStep 941255 = 1411883) B1411883
theorem B12082445 : Blo 626299 12082445 := bstep (se 3 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 12082445 = 4530917) B4530917
theorem B941417 : Blo 626299 941417 := bstep (se 2 (by rfl) ⟨353031, by rfl⟩ : syracuseStep 941417 = 706063) B706063
theorem B2121065 : Blo 626299 2121065 := bstep (se 2 (by rfl) ⟨795399, by rfl⟩ : syracuseStep 2121065 = 1590799) B1590799
theorem B941495 : Blo 626299 941495 := bstep (se 1 (by rfl) ⟨706121, by rfl⟩ : syracuseStep 941495 = 1412243) B1412243
theorem B941531 : Blo 626299 941531 := bstep (se 1 (by rfl) ⟨706148, by rfl⟩ : syracuseStep 941531 = 1412297) B1412297
theorem B4775435 : Blo 626299 4775435 := bstep (se 1 (by rfl) ⟨3581576, by rfl⟩ : syracuseStep 4775435 = 7163153) B7163153
theorem B7167527 : Blo 626299 7167527 := bstep (se 1 (by rfl) ⟨5375645, by rfl⟩ : syracuseStep 7167527 = 10751291) B10751291
theorem B1793659 : Blo 626299 1793659 := bstep (se 1 (by rfl) ⟨1345244, by rfl⟩ : syracuseStep 1793659 = 2690489) B2690489
theorem B1695431 : Blo 626299 1695431 := bstep (se 1 (by rfl) ⟨1271573, by rfl⟩ : syracuseStep 1695431 = 2543147) B2543147
theorem B1793785 : Blo 626299 1793785 := bstep (se 2 (by rfl) ⟨672669, by rfl⟩ : syracuseStep 1793785 = 1345339) B1345339
theorem B4022075 : Blo 626299 4022075 := bstep (se 1 (by rfl) ⟨3016556, by rfl⟩ : syracuseStep 4022075 = 6033113) B6033113
theorem B941999 : Blo 626299 941999 := bstep (se 1 (by rfl) ⟨706499, by rfl⟩ : syracuseStep 941999 = 1412999) B1412999
theorem B2121659 : Blo 626299 2121659 := bstep (se 1 (by rfl) ⟨1591244, by rfl⟩ : syracuseStep 2121659 = 3182489) B3182489
theorem B942089 : Blo 626299 942089 := bstep (se 2 (by rfl) ⟨353283, by rfl⟩ : syracuseStep 942089 = 706567) B706567
theorem B942119 : Blo 626299 942119 := bstep (se 1 (by rfl) ⟨706589, by rfl⟩ : syracuseStep 942119 = 1413179) B1413179
theorem B2383951 : Blo 626299 2383951 := bstep (se 1 (by rfl) ⟨1787963, by rfl⟩ : syracuseStep 2383951 = 3575927) B3575927
theorem B942203 : Blo 626299 942203 := bstep (se 1 (by rfl) ⟨706652, by rfl⟩ : syracuseStep 942203 = 1413305) B1413305
theorem B942329 : Blo 626299 942329 := bstep (se 2 (by rfl) ⟨353373, by rfl⟩ : syracuseStep 942329 = 706747) B706747
theorem B942431 : Blo 626299 942431 := bstep (se 1 (by rfl) ⟨706823, by rfl⟩ : syracuseStep 942431 = 1413647) B1413647
theorem B942443 : Blo 626299 942443 := bstep (se 1 (by rfl) ⟨706832, by rfl⟩ : syracuseStep 942443 = 1413665) B1413665
theorem B2417039 : Blo 626299 2417039 := bstep (se 1 (by rfl) ⟨1812779, by rfl⟩ : syracuseStep 2417039 = 3625559) B3625559
theorem B3170825 : Blo 626299 3170825 := bstep (se 2 (by rfl) ⟨1189059, by rfl⟩ : syracuseStep 3170825 = 2378119) B2378119
theorem B2384423 : Blo 626299 2384423 := bstep (se 1 (by rfl) ⟨1788317, by rfl⟩ : syracuseStep 2384423 = 3576635) B3576635
theorem B942671 : Blo 626299 942671 := bstep (se 1 (by rfl) ⟨707003, by rfl⟩ : syracuseStep 942671 = 1414007) B1414007
theorem B2417249 : Blo 626299 2417249 := bstep (se 2 (by rfl) ⟨906468, by rfl⟩ : syracuseStep 2417249 = 1812937) B1812937
theorem B942791 : Blo 626299 942791 := bstep (se 1 (by rfl) ⟨707093, by rfl⟩ : syracuseStep 942791 = 1414187) B1414187
theorem B942953 : Blo 626299 942953 := bstep (se 2 (by rfl) ⟨353607, by rfl⟩ : syracuseStep 942953 = 707215) B707215
theorem B15524783 : Blo 626299 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B10216367 : Blo 626299 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B943031 : Blo 626299 943031 := bstep (se 1 (by rfl) ⟨707273, by rfl⟩ : syracuseStep 943031 = 1414547) B1414547
theorem B943067 : Blo 626299 943067 := bstep (se 1 (by rfl) ⟨707300, by rfl⟩ : syracuseStep 943067 = 1414601) B1414601
theorem B5104613 : Blo 626299 5104613 := bstep (se 4 (by rfl) ⟨478557, by rfl⟩ : syracuseStep 5104613 = 957115) B957115
theorem B2155673 : Blo 626299 2155673 := bstep (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) B1616755
theorem B4777379 : Blo 626299 4777379 := bstep (se 1 (by rfl) ⟨3583034, by rfl⟩ : syracuseStep 4777379 = 7166069) B7166069
theorem B943535 : Blo 626299 943535 := bstep (se 1 (by rfl) ⟨707651, by rfl⟩ : syracuseStep 943535 = 1415303) B1415303
theorem B2385395 : Blo 626299 2385395 := bstep (se 1 (by rfl) ⟨1789046, by rfl⟩ : syracuseStep 2385395 = 3578093) B3578093
theorem B943625 : Blo 626299 943625 := bstep (se 2 (by rfl) ⟨353859, by rfl⟩ : syracuseStep 943625 = 707719) B707719
theorem B943655 : Blo 626299 943655 := bstep (se 1 (by rfl) ⟨707741, by rfl⟩ : syracuseStep 943655 = 1415483) B1415483
theorem B2123387 : Blo 626299 2123387 := bstep (se 1 (by rfl) ⟨1592540, by rfl⟩ : syracuseStep 2123387 = 3185081) B3185081
theorem B943739 : Blo 626299 943739 := bstep (se 1 (by rfl) ⟨707804, by rfl⟩ : syracuseStep 943739 = 1415609) B1415609
theorem B1271467 : Blo 626299 1271467 := bstep (se 1 (by rfl) ⟨953600, by rfl⟩ : syracuseStep 1271467 = 1907201) B1907201
theorem B943865 : Blo 626299 943865 := bstep (se 2 (by rfl) ⟨353949, by rfl⟩ : syracuseStep 943865 = 707899) B707899
theorem B2123549 : Blo 626299 2123549 := bstep (se 3 (by rfl) ⟨398165, by rfl⟩ : syracuseStep 2123549 = 796331) B796331
theorem B943967 : Blo 626299 943967 := bstep (se 1 (by rfl) ⟨707975, by rfl⟩ : syracuseStep 943967 = 1415951) B1415951
theorem B943979 : Blo 626299 943979 := bstep (se 1 (by rfl) ⟨707984, by rfl⟩ : syracuseStep 943979 = 1415969) B1415969
theorem B3172283 : Blo 626299 3172283 := bstep (se 1 (by rfl) ⟨2379212, by rfl⟩ : syracuseStep 3172283 = 4758425) B4758425
theorem B1435655 : Blo 626299 1435655 := bstep (se 1 (by rfl) ⟨1076741, by rfl⟩ : syracuseStep 1435655 = 2153483) B2153483
theorem B944207 : Blo 626299 944207 := bstep (se 1 (by rfl) ⟨708155, by rfl⟩ : syracuseStep 944207 = 1416311) B1416311
theorem B9168997 : Blo 626299 9168997 := bstep (se 4 (by rfl) ⟨859593, by rfl⟩ : syracuseStep 9168997 = 1719187) B1719187
theorem B944327 : Blo 626299 944327 := bstep (se 1 (by rfl) ⟨708245, by rfl⟩ : syracuseStep 944327 = 1416491) B1416491
theorem B944489 : Blo 626299 944489 := bstep (se 2 (by rfl) ⟨354183, by rfl⟩ : syracuseStep 944489 = 708367) B708367
theorem B944567 : Blo 626299 944567 := bstep (se 1 (by rfl) ⟨708425, by rfl⟩ : syracuseStep 944567 = 1416851) B1416851
theorem B2124251 : Blo 626299 2124251 := bstep (se 1 (by rfl) ⟨1593188, by rfl⟩ : syracuseStep 2124251 = 3186377) B3186377
theorem B944603 : Blo 626299 944603 := bstep (se 1 (by rfl) ⟨708452, by rfl⟩ : syracuseStep 944603 = 1416905) B1416905
theorem B1698553 : Blo 626299 1698553 := bstep (se 2 (by rfl) ⟨636957, by rfl⟩ : syracuseStep 1698553 = 1273915) B1273915
theorem B2681707 : Blo 626299 2681707 := bstep (se 1 (by rfl) ⟨2011280, by rfl⟩ : syracuseStep 2681707 = 4022561) B4022561
theorem B945071 : Blo 626299 945071 := bstep (se 1 (by rfl) ⟨708803, by rfl⟩ : syracuseStep 945071 = 1417607) B1417607
theorem B945161 : Blo 626299 945161 := bstep (se 2 (by rfl) ⟨354435, by rfl⟩ : syracuseStep 945161 = 708871) B708871
theorem B945191 : Blo 626299 945191 := bstep (se 1 (by rfl) ⟨708893, by rfl⟩ : syracuseStep 945191 = 1417787) B1417787
theorem B945275 : Blo 626299 945275 := bstep (se 1 (by rfl) ⟨708956, by rfl⟩ : syracuseStep 945275 = 1417913) B1417913
theorem B2124953 : Blo 626299 2124953 := bstep (se 2 (by rfl) ⟨796857, by rfl⟩ : syracuseStep 2124953 = 1593715) B1593715
theorem B3173579 : Blo 626299 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B945401 : Blo 626299 945401 := bstep (se 2 (by rfl) ⟨354525, by rfl⟩ : syracuseStep 945401 = 709051) B709051
theorem B3829193 : Blo 626299 3829193 := bstep (se 2 (by rfl) ⟨1435947, by rfl⟩ : syracuseStep 3829193 = 2871895) B2871895
theorem B1338889 : Blo 626299 1338889 := bstep (se 2 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 1338889 = 1004167) B1004167
theorem B847369 : Blo 626299 847369 := bstep (se 2 (by rfl) ⟨317763, by rfl⟩ : syracuseStep 847369 = 635527) B635527
theorem B3010193 : Blo 626299 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B4779809 : Blo 626299 4779809 := bstep (se 2 (by rfl) ⟨1792428, by rfl⟩ : syracuseStep 4779809 = 3584857) B3584857
theorem B1699679 : Blo 626299 1699679 := bstep (se 1 (by rfl) ⟨1274759, by rfl⟩ : syracuseStep 1699679 = 2549519) B2549519
theorem B2126141 : Blo 626299 2126141 := bstep (se 3 (by rfl) ⟨398651, by rfl⟩ : syracuseStep 2126141 = 797303) B797303
theorem B2388311 : Blo 626299 2388311 := bstep (se 1 (by rfl) ⟨1791233, by rfl⟩ : syracuseStep 2388311 = 3582467) B3582467
theorem B1340153 : Blo 626299 1340153 := bstep (se 2 (by rfl) ⟨502557, by rfl⟩ : syracuseStep 1340153 = 1005115) B1005115
theorem B2127005 : Blo 626299 2127005 := bstep (se 3 (by rfl) ⟨398813, by rfl⟩ : syracuseStep 2127005 = 797627) B797627
theorem B2389601 : Blo 626299 2389601 := bstep (se 2 (by rfl) ⟨896100, by rfl⟩ : syracuseStep 2389601 = 1792201) B1792201
theorem B1341127 : Blo 626299 1341127 := bstep (se 1 (by rfl) ⟨1005845, by rfl⟩ : syracuseStep 1341127 = 2011691) B2011691
theorem B32635747 : Blo 626299 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B2391059 : Blo 626299 2391059 := bstep (se 1 (by rfl) ⟨1793294, by rfl⟩ : syracuseStep 2391059 = 3586589) B3586589
theorem B2686031 : Blo 626299 2686031 := bstep (se 1 (by rfl) ⟨2014523, by rfl⟩ : syracuseStep 2686031 = 4029047) B4029047
theorem B8027383 : Blo 626299 8027383 := bstep (se 1 (by rfl) ⟨6020537, by rfl⟩ : syracuseStep 8027383 = 12041075) B12041075
theorem B2391515 : Blo 626299 2391515 := bstep (se 1 (by rfl) ⟨1793636, by rfl⟩ : syracuseStep 2391515 = 3587273) B3587273
theorem B851807 : Blo 626299 851807 := bstep (se 1 (by rfl) ⟨638855, by rfl⟩ : syracuseStep 851807 = 1277711) B1277711
theorem B1212335 : Blo 626299 1212335 := bstep (se 1 (by rfl) ⟨909251, by rfl⟩ : syracuseStep 1212335 = 1818503) B1818503
theorem B3178601 : Blo 626299 3178601 := bstep (se 2 (by rfl) ⟨1191975, by rfl⟩ : syracuseStep 3178601 = 2383951) B2383951
theorem B1343699 : Blo 626299 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B1409615 : Blo 626299 1409615 := bstep (se 1 (by rfl) ⟨1057211, by rfl⟩ : syracuseStep 1409615 = 2114423) B2114423
theorem B2687687 : Blo 626299 2687687 := bstep (se 1 (by rfl) ⟨2015765, by rfl⟩ : syracuseStep 2687687 = 4031531) B4031531
theorem B1409759 : Blo 626299 1409759 := bstep (se 1 (by rfl) ⟨1057319, by rfl⟩ : syracuseStep 1409759 = 2114639) B2114639
theorem B6030227 : Blo 626299 6030227 := bstep (se 1 (by rfl) ⟨4522670, by rfl⟩ : syracuseStep 6030227 = 9045341) B9045341
theorem B1410011 : Blo 626299 1410011 := bstep (se 1 (by rfl) ⟨1057508, by rfl⟩ : syracuseStep 1410011 = 2115017) B2115017
theorem B1508327 : Blo 626299 1508327 := bstep (se 1 (by rfl) ⟨1131245, by rfl⟩ : syracuseStep 1508327 = 2262491) B2262491
theorem B4785155 : Blo 626299 4785155 := bstep (se 1 (by rfl) ⟨3588866, by rfl⟩ : syracuseStep 4785155 = 7177733) B7177733
theorem B3015805 : Blo 626299 3015805 := bstep (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) B1130927
theorem B1410191 : Blo 626299 1410191 := bstep (se 1 (by rfl) ⟨1057643, by rfl⟩ : syracuseStep 1410191 = 2115287) B2115287
theorem B3179735 : Blo 626299 3179735 := bstep (se 1 (by rfl) ⟨2384801, by rfl⟩ : syracuseStep 3179735 = 4769603) B4769603
theorem B1410281 : Blo 626299 1410281 := bstep (se 2 (by rfl) ⟨528855, by rfl⟩ : syracuseStep 1410281 = 1057711) B1057711
theorem B1410335 : Blo 626299 1410335 := bstep (se 1 (by rfl) ⟨1057751, by rfl⟩ : syracuseStep 1410335 = 2115503) B2115503
theorem B12912185 : Blo 626299 12912185 := bstep (se 2 (by rfl) ⟨4842069, by rfl⟩ : syracuseStep 12912185 = 9684139) B9684139
theorem B1410857 : Blo 626299 1410857 := bstep (se 2 (by rfl) ⟨529071, by rfl⟩ : syracuseStep 1410857 = 1058143) B1058143
theorem B4786127 : Blo 626299 4786127 := bstep (se 1 (by rfl) ⟨3589595, by rfl⟩ : syracuseStep 4786127 = 7179191) B7179191
theorem B2689463 : Blo 626299 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B12225329 : Blo 626299 12225329 := bstep (se 2 (by rfl) ⟨4584498, by rfl⟩ : syracuseStep 12225329 = 9168997) B9168997
theorem B1411919 : Blo 626299 1411919 := bstep (se 1 (by rfl) ⟨1058939, by rfl⟩ : syracuseStep 1411919 = 2117879) B2117879
theorem B1510363 : Blo 626299 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B17239013 : Blo 626299 17239013 := bstep (se 4 (by rfl) ⟨1616157, by rfl⟩ : syracuseStep 17239013 = 3232315) B3232315
theorem B1412135 : Blo 626299 1412135 := bstep (se 1 (by rfl) ⟨1059101, by rfl⟩ : syracuseStep 1412135 = 2118203) B2118203
theorem B8621257 : Blo 626299 8621257 := bstep (se 2 (by rfl) ⟨3232971, by rfl⟩ : syracuseStep 8621257 = 6465943) B6465943
theorem B1412315 : Blo 626299 1412315 := bstep (se 1 (by rfl) ⟨1059236, by rfl⟩ : syracuseStep 1412315 = 2118473) B2118473
theorem B5082497 : Blo 626299 5082497 := bstep (se 2 (by rfl) ⟨1905936, by rfl⟩ : syracuseStep 5082497 = 3811873) B3811873
theorem B1412513 : Blo 626299 1412513 := bstep (se 2 (by rfl) ⟨529692, by rfl⟩ : syracuseStep 1412513 = 1059385) B1059385
theorem B2723321 : Blo 626299 2723321 := bstep (se 2 (by rfl) ⟨1021245, by rfl⟩ : syracuseStep 2723321 = 2042491) B2042491
theorem B3215057 : Blo 626299 3215057 := bstep (se 2 (by rfl) ⟨1205646, by rfl⟩ : syracuseStep 3215057 = 2411293) B2411293
theorem B626399 : Blo 626299 626399 := bstep (se 1 (by rfl) ⟨469799, by rfl⟩ : syracuseStep 626399 = 939599) B939599
theorem B626479 : Blo 626299 626479 := bstep (se 1 (by rfl) ⟨469859, by rfl⟩ : syracuseStep 626479 = 939719) B939719
theorem B3575609 : Blo 626299 3575609 := bstep (se 2 (by rfl) ⟨1340853, by rfl⟩ : syracuseStep 3575609 = 2681707) B2681707
theorem B626587 : Blo 626299 626587 := bstep (se 1 (by rfl) ⟨469940, by rfl⟩ : syracuseStep 626587 = 939881) B939881
theorem B3018653 : Blo 626299 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B626639 : Blo 626299 626639 := bstep (se 1 (by rfl) ⟨469979, by rfl⟩ : syracuseStep 626639 = 939959) B939959
theorem B1413071 : Blo 626299 1413071 := bstep (se 1 (by rfl) ⟨1059803, by rfl⟩ : syracuseStep 1413071 = 2119607) B2119607
theorem B626663 : Blo 626299 626663 := bstep (se 1 (by rfl) ⟨469997, by rfl⟩ : syracuseStep 626663 = 939995) B939995
theorem B3182651 : Blo 626299 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B626975 : Blo 626299 626975 := bstep (se 1 (by rfl) ⟨470231, by rfl⟩ : syracuseStep 626975 = 940463) B940463
theorem B1413449 : Blo 626299 1413449 := bstep (se 2 (by rfl) ⟨530043, by rfl⟩ : syracuseStep 1413449 = 1060087) B1060087
theorem B5738825 : Blo 626299 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B627035 : Blo 626299 627035 := bstep (se 1 (by rfl) ⟨470276, by rfl⟩ : syracuseStep 627035 = 940553) B940553
theorem B1413467 : Blo 626299 1413467 := bstep (se 1 (by rfl) ⟨1060100, by rfl⟩ : syracuseStep 1413467 = 2120201) B2120201
theorem B627055 : Blo 626299 627055 := bstep (se 1 (by rfl) ⟨470291, by rfl⟩ : syracuseStep 627055 = 940583) B940583
theorem B627111 : Blo 626299 627111 := bstep (se 1 (by rfl) ⟨470333, by rfl⟩ : syracuseStep 627111 = 940667) B940667
theorem B8032715 : Blo 626299 8032715 := bstep (se 1 (by rfl) ⟨6024536, by rfl⟩ : syracuseStep 8032715 = 12049073) B12049073
theorem B627195 : Blo 626299 627195 := bstep (se 1 (by rfl) ⟨470396, by rfl⟩ : syracuseStep 627195 = 940793) B940793
theorem B627263 : Blo 626299 627263 := bstep (se 1 (by rfl) ⟨470447, by rfl⟩ : syracuseStep 627263 = 940895) B940895
theorem B627271 : Blo 626299 627271 := bstep (se 1 (by rfl) ⟨470453, by rfl⟩ : syracuseStep 627271 = 940907) B940907
theorem B627423 : Blo 626299 627423 := bstep (se 1 (by rfl) ⟨470567, by rfl⟩ : syracuseStep 627423 = 941135) B941135
theorem B627503 : Blo 626299 627503 := bstep (se 1 (by rfl) ⟨470627, by rfl⟩ : syracuseStep 627503 = 941255) B941255
theorem B627611 : Blo 626299 627611 := bstep (se 1 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 627611 = 941417) B941417
theorem B1414043 : Blo 626299 1414043 := bstep (se 1 (by rfl) ⟨1060532, by rfl⟩ : syracuseStep 1414043 = 2121065) B2121065
theorem B627663 : Blo 626299 627663 := bstep (se 1 (by rfl) ⟨470747, by rfl⟩ : syracuseStep 627663 = 941495) B941495
theorem B627687 : Blo 626299 627687 := bstep (se 1 (by rfl) ⟨470765, by rfl⟩ : syracuseStep 627687 = 941531) B941531
theorem B3183623 : Blo 626299 3183623 := bstep (se 1 (by rfl) ⟨2387717, by rfl⟩ : syracuseStep 3183623 = 4775435) B4775435
theorem B1414241 : Blo 626299 1414241 := bstep (se 2 (by rfl) ⟨530340, by rfl⟩ : syracuseStep 1414241 = 1060681) B1060681
theorem B627999 : Blo 626299 627999 := bstep (se 1 (by rfl) ⟨470999, by rfl⟩ : syracuseStep 627999 = 941999) B941999
theorem B1414439 : Blo 626299 1414439 := bstep (se 1 (by rfl) ⟨1060829, by rfl⟩ : syracuseStep 1414439 = 2121659) B2121659
theorem B628059 : Blo 626299 628059 := bstep (se 1 (by rfl) ⟨471044, by rfl⟩ : syracuseStep 628059 = 942089) B942089
theorem B628079 : Blo 626299 628079 := bstep (se 1 (by rfl) ⟨471059, by rfl⟩ : syracuseStep 628079 = 942119) B942119
theorem B628135 : Blo 626299 628135 := bstep (se 1 (by rfl) ⟨471101, by rfl⟩ : syracuseStep 628135 = 942203) B942203
theorem B3184109 : Blo 626299 3184109 := bstep (se 3 (by rfl) ⟨597020, by rfl⟩ : syracuseStep 3184109 = 1194041) B1194041
theorem B628219 : Blo 626299 628219 := bstep (se 1 (by rfl) ⟨471164, by rfl⟩ : syracuseStep 628219 = 942329) B942329
theorem B628287 : Blo 626299 628287 := bstep (se 1 (by rfl) ⟨471215, by rfl⟩ : syracuseStep 628287 = 942431) B942431
theorem B628295 : Blo 626299 628295 := bstep (se 1 (by rfl) ⟨471221, by rfl⟩ : syracuseStep 628295 = 942443) B942443
theorem B1611359 : Blo 626299 1611359 := bstep (se 1 (by rfl) ⟨1208519, by rfl⟩ : syracuseStep 1611359 = 2417039) B2417039
theorem B1513055 : Blo 626299 1513055 := bstep (se 1 (by rfl) ⟨1134791, by rfl⟩ : syracuseStep 1513055 = 2269583) B2269583
theorem B1414817 : Blo 626299 1414817 := bstep (se 2 (by rfl) ⟨530556, by rfl⟩ : syracuseStep 1414817 = 1061113) B1061113
theorem B628447 : Blo 626299 628447 := bstep (se 1 (by rfl) ⟨471335, by rfl⟩ : syracuseStep 628447 = 942671) B942671
theorem B1611499 : Blo 626299 1611499 := bstep (se 1 (by rfl) ⟨1208624, by rfl⟩ : syracuseStep 1611499 = 2417249) B2417249
theorem B628527 : Blo 626299 628527 := bstep (se 1 (by rfl) ⟨471395, by rfl⟩ : syracuseStep 628527 = 942791) B942791
theorem B628635 : Blo 626299 628635 := bstep (se 1 (by rfl) ⟨471476, by rfl⟩ : syracuseStep 628635 = 942953) B942953
theorem B628687 : Blo 626299 628687 := bstep (se 1 (by rfl) ⟨471515, by rfl⟩ : syracuseStep 628687 = 943031) B943031
theorem B628711 : Blo 626299 628711 := bstep (se 1 (by rfl) ⟨471533, by rfl⟩ : syracuseStep 628711 = 943067) B943067
theorem B1415177 : Blo 626299 1415177 := bstep (se 2 (by rfl) ⟨530691, by rfl⟩ : syracuseStep 1415177 = 1061383) B1061383
theorem B3184919 : Blo 626299 3184919 := bstep (se 1 (by rfl) ⟨2388689, by rfl⟩ : syracuseStep 3184919 = 4777379) B4777379
theorem B629023 : Blo 626299 629023 := bstep (se 1 (by rfl) ⟨471767, by rfl⟩ : syracuseStep 629023 = 943535) B943535
theorem B629083 : Blo 626299 629083 := bstep (se 1 (by rfl) ⟨471812, by rfl⟩ : syracuseStep 629083 = 943625) B943625
theorem B629103 : Blo 626299 629103 := bstep (se 1 (by rfl) ⟨471827, by rfl⟩ : syracuseStep 629103 = 943655) B943655
theorem B1415591 : Blo 626299 1415591 := bstep (se 1 (by rfl) ⟨1061693, by rfl⟩ : syracuseStep 1415591 = 2123387) B2123387
theorem B629159 : Blo 626299 629159 := bstep (se 1 (by rfl) ⟨471869, by rfl⟩ : syracuseStep 629159 = 943739) B943739
theorem B629243 : Blo 626299 629243 := bstep (se 1 (by rfl) ⟨471932, by rfl⟩ : syracuseStep 629243 = 943865) B943865
theorem B1415699 : Blo 626299 1415699 := bstep (se 1 (by rfl) ⟨1061774, by rfl⟩ : syracuseStep 1415699 = 2123549) B2123549
theorem B629311 : Blo 626299 629311 := bstep (se 1 (by rfl) ⟨471983, by rfl⟩ : syracuseStep 629311 = 943967) B943967
theorem B629319 : Blo 626299 629319 := bstep (se 1 (by rfl) ⟨471989, by rfl⟩ : syracuseStep 629319 = 943979) B943979
theorem B1415753 : Blo 626299 1415753 := bstep (se 2 (by rfl) ⟨530907, by rfl⟩ : syracuseStep 1415753 = 1061815) B1061815
theorem B957103 : Blo 626299 957103 := bstep (se 1 (by rfl) ⟨717827, by rfl⟩ : syracuseStep 957103 = 1435655) B1435655
theorem B629471 : Blo 626299 629471 := bstep (se 1 (by rfl) ⟨472103, by rfl⟩ : syracuseStep 629471 = 944207) B944207
theorem B629551 : Blo 626299 629551 := bstep (se 1 (by rfl) ⟨472163, by rfl⟩ : syracuseStep 629551 = 944327) B944327
theorem B629659 : Blo 626299 629659 := bstep (se 1 (by rfl) ⟨472244, by rfl⟩ : syracuseStep 629659 = 944489) B944489
theorem B629711 : Blo 626299 629711 := bstep (se 1 (by rfl) ⟨472283, by rfl⟩ : syracuseStep 629711 = 944567) B944567
theorem B1416167 : Blo 626299 1416167 := bstep (se 1 (by rfl) ⟨1062125, by rfl⟩ : syracuseStep 1416167 = 2124251) B2124251
theorem B629735 : Blo 626299 629735 := bstep (se 1 (by rfl) ⟨472301, by rfl⟩ : syracuseStep 629735 = 944603) B944603
theorem B5381387 : Blo 626299 5381387 := bstep (se 1 (by rfl) ⟨4036040, by rfl⟩ : syracuseStep 5381387 = 8072081) B8072081
theorem B630047 : Blo 626299 630047 := bstep (se 1 (by rfl) ⟨472535, by rfl⟩ : syracuseStep 630047 = 945071) B945071
theorem B630107 : Blo 626299 630107 := bstep (se 1 (by rfl) ⟨472580, by rfl⟩ : syracuseStep 630107 = 945161) B945161
theorem B1416545 : Blo 626299 1416545 := bstep (se 2 (by rfl) ⟨531204, by rfl⟩ : syracuseStep 1416545 = 1062409) B1062409
theorem B630127 : Blo 626299 630127 := bstep (se 1 (by rfl) ⟨472595, by rfl⟩ : syracuseStep 630127 = 945191) B945191
theorem B630183 : Blo 626299 630183 := bstep (se 1 (by rfl) ⟨472637, by rfl⟩ : syracuseStep 630183 = 945275) B945275
theorem B1416635 : Blo 626299 1416635 := bstep (se 1 (by rfl) ⟨1062476, by rfl⟩ : syracuseStep 1416635 = 2124953) B2124953
theorem B630267 : Blo 626299 630267 := bstep (se 1 (by rfl) ⟨472700, by rfl⟩ : syracuseStep 630267 = 945401) B945401
theorem B1416761 : Blo 626299 1416761 := bstep (se 2 (by rfl) ⟨531285, by rfl⟩ : syracuseStep 1416761 = 1062571) B1062571
theorem B3022571 : Blo 626299 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B2006795 : Blo 626299 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B3186539 : Blo 626299 3186539 := bstep (se 1 (by rfl) ⟨2389904, by rfl⟩ : syracuseStep 3186539 = 4779809) B4779809
theorem B7151489 : Blo 626299 7151489 := bstep (se 2 (by rfl) ⟨2681808, by rfl⟩ : syracuseStep 7151489 = 5363617) B5363617
theorem B1417427 : Blo 626299 1417427 := bstep (se 1 (by rfl) ⟨1063070, by rfl⟩ : syracuseStep 1417427 = 2126141) B2126141
theorem B1417481 : Blo 626299 1417481 := bstep (se 2 (by rfl) ⟨531555, by rfl⟩ : syracuseStep 1417481 = 1063111) B1063111
theorem B5382449 : Blo 626299 5382449 := bstep (se 2 (by rfl) ⟨2018418, by rfl⟩ : syracuseStep 5382449 = 4036837) B4036837
theorem B1417697 : Blo 626299 1417697 := bstep (se 2 (by rfl) ⟨531636, by rfl⟩ : syracuseStep 1417697 = 1063273) B1063273
theorem B893435 : Blo 626299 893435 := bstep (se 1 (by rfl) ⟨670076, by rfl⟩ : syracuseStep 893435 = 1340153) B1340153
theorem B54206981 : Blo 626299 54206981 := bstep (se 4 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 54206981 = 10163809) B10163809
theorem B1057387 : Blo 626299 1057387 := bstep (se 1 (by rfl) ⟨793040, by rfl⟩ : syracuseStep 1057387 = 1586081) B1586081
theorem B795359 : Blo 626299 795359 := bstep (se 1 (by rfl) ⟨596519, by rfl⟩ : syracuseStep 795359 = 1193039) B1193039
theorem B1418003 : Blo 626299 1418003 := bstep (se 1 (by rfl) ⟨1063502, by rfl⟩ : syracuseStep 1418003 = 2127005) B2127005
theorem B3023725 : Blo 626299 3023725 := bstep (se 3 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 3023725 = 1133897) B1133897
theorem B1057691 : Blo 626299 1057691 := bstep (se 1 (by rfl) ⟨793268, by rfl⟩ : syracuseStep 1057691 = 1586537) B1586537
theorem B1189151 : Blo 626299 1189151 := bstep (se 1 (by rfl) ⟨891863, by rfl⟩ : syracuseStep 1189151 = 1783727) B1783727
theorem B7152947 : Blo 626299 7152947 := bstep (se 1 (by rfl) ⟨5364710, by rfl⟩ : syracuseStep 7152947 = 10729421) B10729421
theorem B3025031 : Blo 626299 3025031 := bstep (se 1 (by rfl) ⟨2268773, by rfl⟩ : syracuseStep 3025031 = 4537547) B4537547
theorem B2271485 : Blo 626299 2271485 := bstep (se 3 (by rfl) ⟨425903, by rfl⟩ : syracuseStep 2271485 = 851807) B851807
theorem B1190153 : Blo 626299 1190153 := bstep (se 2 (by rfl) ⟨446307, by rfl⟩ : syracuseStep 1190153 = 892615) B892615
theorem B797359 : Blo 626299 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B5745431 : Blo 626299 5745431 := bstep (se 1 (by rfl) ⟨4309073, by rfl⟩ : syracuseStep 5745431 = 8618147) B8618147
theorem B1289449 : Blo 626299 1289449 := bstep (se 2 (by rfl) ⟨483543, by rfl⟩ : syracuseStep 1289449 = 967087) B967087
theorem B3190265 : Blo 626299 3190265 := bstep (se 2 (by rfl) ⟨1196349, by rfl⟩ : syracuseStep 3190265 = 2392699) B2392699
theorem B765535 : Blo 626299 765535 := bstep (se 1 (by rfl) ⟨574151, by rfl⟩ : syracuseStep 765535 = 1148303) B1148303
theorem B1191611 : Blo 626299 1191611 := bstep (se 1 (by rfl) ⟨893708, by rfl⟩ : syracuseStep 1191611 = 1787417) B1787417
theorem B3190589 : Blo 626299 3190589 := bstep (se 3 (by rfl) ⟨598235, by rfl⟩ : syracuseStep 3190589 = 1196471) B1196471
theorem B6435073 : Blo 626299 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B1585433 : Blo 626299 1585433 := bstep (se 2 (by rfl) ⟨594537, by rfl⟩ : syracuseStep 1585433 = 1189075) B1189075
theorem B1585727 : Blo 626299 1585727 := bstep (se 1 (by rfl) ⟨1189295, by rfl⟩ : syracuseStep 1585727 = 2378591) B2378591
theorem B4764257 : Blo 626299 4764257 := bstep (se 2 (by rfl) ⟨1786596, by rfl⟩ : syracuseStep 4764257 = 3573193) B3573193
theorem B1061599 : Blo 626299 1061599 := bstep (se 1 (by rfl) ⟨796199, by rfl⟩ : syracuseStep 1061599 = 1592399) B1592399
theorem B1585939 : Blo 626299 1585939 := bstep (se 1 (by rfl) ⟨1189454, by rfl⟩ : syracuseStep 1585939 = 2378909) B2378909
theorem B1455067 : Blo 626299 1455067 := bstep (se 1 (by rfl) ⟨1091300, by rfl⟩ : syracuseStep 1455067 = 2182601) B2182601
theorem B38581373 : Blo 626299 38581373 := bstep (se 3 (by rfl) ⟨7234007, by rfl⟩ : syracuseStep 38581373 = 14468015) B14468015
theorem B1062031 : Blo 626299 1062031 := bstep (se 1 (by rfl) ⟨796523, by rfl⟩ : syracuseStep 1062031 = 1593047) B1593047
theorem B1586375 : Blo 626299 1586375 := bstep (se 1 (by rfl) ⟨1189781, by rfl⟩ : syracuseStep 1586375 = 2379563) B2379563
theorem B1586425 : Blo 626299 1586425 := bstep (se 2 (by rfl) ⟨594909, by rfl⟩ : syracuseStep 1586425 = 1189819) B1189819
theorem B1062281 : Blo 626299 1062281 := bstep (se 2 (by rfl) ⟨398355, by rfl⟩ : syracuseStep 1062281 = 796711) B796711
theorem B1193555 : Blo 626299 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B1193707 : Blo 626299 1193707 := bstep (se 1 (by rfl) ⟨895280, by rfl⟩ : syracuseStep 1193707 = 1790561) B1790561
theorem B24131357 : Blo 626299 24131357 := bstep (se 3 (by rfl) ⟨4524629, by rfl⟩ : syracuseStep 24131357 = 9049259) B9049259
theorem B1062713 : Blo 626299 1062713 := bstep (se 2 (by rfl) ⟨398517, by rfl⟩ : syracuseStep 1062713 = 797035) B797035
theorem B1587073 : Blo 626299 1587073 := bstep (se 2 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 1587073 = 1190305) B1190305
theorem B1193935 : Blo 626299 1193935 := bstep (se 1 (by rfl) ⟨895451, by rfl⟩ : syracuseStep 1193935 = 1790903) B1790903
theorem B2865287 : Blo 626299 2865287 := bstep (se 1 (by rfl) ⟨2148965, by rfl⟩ : syracuseStep 2865287 = 4297931) B4297931
theorem B1587833 : Blo 626299 1587833 := bstep (se 2 (by rfl) ⟨595437, by rfl⟩ : syracuseStep 1587833 = 1190875) B1190875
theorem B9058949 : Blo 626299 9058949 := bstep (se 4 (by rfl) ⟨849276, by rfl⟩ : syracuseStep 9058949 = 1698553) B1698553
theorem B1587883 : Blo 626299 1587883 := bstep (se 1 (by rfl) ⟨1190912, by rfl⟩ : syracuseStep 1587883 = 2381825) B2381825
theorem B1194679 : Blo 626299 1194679 := bstep (se 1 (by rfl) ⟨896009, by rfl⟩ : syracuseStep 1194679 = 1792019) B1792019
theorem B3226391 : Blo 626299 3226391 := bstep (se 1 (by rfl) ⟨2419793, by rfl⟩ : syracuseStep 3226391 = 4839587) B4839587
theorem B1194907 : Blo 626299 1194907 := bstep (se 1 (by rfl) ⟨896180, by rfl⟩ : syracuseStep 1194907 = 1792361) B1792361
theorem B1588187 : Blo 626299 1588187 := bstep (se 1 (by rfl) ⟨1191140, by rfl⟩ : syracuseStep 1588187 = 2382281) B2382281
theorem B1194983 : Blo 626299 1194983 := bstep (se 1 (by rfl) ⟨896237, by rfl⟩ : syracuseStep 1194983 = 1792475) B1792475
theorem B1588511 : Blo 626299 1588511 := bstep (se 1 (by rfl) ⟨1191383, by rfl⟩ : syracuseStep 1588511 = 2382767) B2382767
theorem B1785185 : Blo 626299 1785185 := bstep (se 2 (by rfl) ⟨669444, by rfl⟩ : syracuseStep 1785185 = 1338889) B1338889
theorem B1129825 : Blo 626299 1129825 := bstep (se 2 (by rfl) ⟨423684, by rfl⟩ : syracuseStep 1129825 = 847369) B847369
theorem B2014561 : Blo 626299 2014561 := bstep (se 2 (by rfl) ⟨755460, by rfl⟩ : syracuseStep 2014561 = 1510921) B1510921
theorem B1359443 : Blo 626299 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B4472617 : Blo 626299 4472617 := bstep (se 2 (by rfl) ⟨1677231, by rfl⟩ : syracuseStep 4472617 = 3354463) B3354463
theorem B1130287 : Blo 626299 1130287 := bstep (se 1 (by rfl) ⟨847715, by rfl⟩ : syracuseStep 1130287 = 1695431) B1695431
theorem B1196137 : Blo 626299 1196137 := bstep (se 2 (by rfl) ⟨448551, by rfl⟩ : syracuseStep 1196137 = 897103) B897103
theorem B704731 : Blo 626299 704731 := bstep (se 1 (by rfl) ⟨528548, by rfl⟩ : syracuseStep 704731 = 1057097) B1057097
theorem B2113883 : Blo 626299 2113883 := bstep (se 1 (by rfl) ⟨1585412, by rfl⟩ : syracuseStep 2113883 = 3170825) B3170825
theorem B1589615 : Blo 626299 1589615 := bstep (se 1 (by rfl) ⟨1192211, by rfl⟩ : syracuseStep 1589615 = 2384423) B2384423
theorem B705019 : Blo 626299 705019 := bstep (se 1 (by rfl) ⟨528764, by rfl⟩ : syracuseStep 705019 = 1057529) B1057529
theorem B705199 : Blo 626299 705199 := bstep (se 1 (by rfl) ⟨528899, by rfl⟩ : syracuseStep 705199 = 1057799) B1057799
theorem B2868047 : Blo 626299 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B6800273 : Blo 626299 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B705487 : Blo 626299 705487 := bstep (se 1 (by rfl) ⟨529115, by rfl⟩ : syracuseStep 705487 = 1058231) B1058231
theorem B1590263 : Blo 626299 1590263 := bstep (se 1 (by rfl) ⟨1192697, by rfl⟩ : syracuseStep 1590263 = 2385395) B2385395
theorem B2114855 : Blo 626299 2114855 := bstep (se 1 (by rfl) ⟨1586141, by rfl⟩ : syracuseStep 2114855 = 3172283) B3172283
theorem B705883 : Blo 626299 705883 := bstep (se 1 (by rfl) ⟨529412, by rfl⟩ : syracuseStep 705883 = 1058825) B1058825
theorem B705991 : Blo 626299 705991 := bstep (se 1 (by rfl) ⟨529493, by rfl⟩ : syracuseStep 705991 = 1058987) B1058987
theorem B706351 : Blo 626299 706351 := bstep (se 1 (by rfl) ⟨529763, by rfl⟩ : syracuseStep 706351 = 1059527) B1059527
theorem B706459 : Blo 626299 706459 := bstep (se 1 (by rfl) ⟨529844, by rfl⟩ : syracuseStep 706459 = 1059689) B1059689
theorem B44222593 : Blo 626299 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B2115719 : Blo 626299 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B21743873 : Blo 626299 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B1788169 : Blo 626299 1788169 := bstep (se 2 (by rfl) ⟨670563, by rfl⟩ : syracuseStep 1788169 = 1341127) B1341127
theorem B706855 : Blo 626299 706855 := bstep (se 1 (by rfl) ⟨530141, by rfl⟩ : syracuseStep 706855 = 1060283) B1060283
theorem B706927 : Blo 626299 706927 := bstep (se 1 (by rfl) ⟨530195, by rfl⟩ : syracuseStep 706927 = 1060391) B1060391
theorem B1133119 : Blo 626299 1133119 := bstep (se 1 (by rfl) ⟨849839, by rfl⟩ : syracuseStep 1133119 = 1699679) B1699679
theorem B707143 : Blo 626299 707143 := bstep (se 1 (by rfl) ⟨530357, by rfl⟩ : syracuseStep 707143 = 1060715) B1060715
theorem B1592207 : Blo 626299 1592207 := bstep (se 1 (by rfl) ⟨1194155, by rfl⟩ : syracuseStep 1592207 = 2388311) B2388311
theorem B838607 : Blo 626299 838607 := bstep (se 1 (by rfl) ⟨628955, by rfl⟩ : syracuseStep 838607 = 1257911) B1257911
theorem B2116961 : Blo 626299 2116961 := bstep (se 2 (by rfl) ⟨793860, by rfl⟩ : syracuseStep 2116961 = 1587721) B1587721
theorem B708007 : Blo 626299 708007 := bstep (se 1 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 708007 = 1062011) B1062011
theorem B1593067 : Blo 626299 1593067 := bstep (se 1 (by rfl) ⟨1194800, by rfl⟩ : syracuseStep 1593067 = 2389601) B2389601
theorem B2379577 : Blo 626299 2379577 := bstep (se 2 (by rfl) ⟨892341, by rfl⟩ : syracuseStep 2379577 = 1784683) B1784683
theorem B708583 : Blo 626299 708583 := bstep (se 1 (by rfl) ⟨531437, by rfl⟩ : syracuseStep 708583 = 1062875) B1062875
theorem B2412569 : Blo 626299 2412569 := bstep (se 2 (by rfl) ⟨904713, by rfl⟩ : syracuseStep 2412569 = 1809427) B1809427
theorem B2379881 : Blo 626299 2379881 := bstep (se 2 (by rfl) ⟨892455, by rfl⟩ : syracuseStep 2379881 = 1784911) B1784911
theorem B10703177 : Blo 626299 10703177 := bstep (se 2 (by rfl) ⟨4013691, by rfl⟩ : syracuseStep 10703177 = 8027383) B8027383
theorem B1594039 : Blo 626299 1594039 := bstep (se 1 (by rfl) ⟨1195529, by rfl⟩ : syracuseStep 1594039 = 2391059) B2391059
theorem B643807 : Blo 626299 643807 := bstep (se 1 (by rfl) ⟨482855, by rfl⟩ : syracuseStep 643807 = 965711) B965711
theorem B1790687 : Blo 626299 1790687 := bstep (se 1 (by rfl) ⟨1343015, by rfl⟩ : syracuseStep 1790687 = 2686031) B2686031
theorem B1594343 : Blo 626299 1594343 := bstep (se 1 (by rfl) ⟨1195757, by rfl⟩ : syracuseStep 1594343 = 2391515) B2391515
theorem B1430747 : Blo 626299 1430747 := bstep (se 1 (by rfl) ⟨1073060, by rfl⟩ : syracuseStep 1430747 = 2146121) B2146121
theorem B2118905 : Blo 626299 2118905 := bstep (se 2 (by rfl) ⟨794589, by rfl⟩ : syracuseStep 2118905 = 1589179) B1589179
theorem B808223 : Blo 626299 808223 := bstep (se 1 (by rfl) ⟨606167, by rfl⟩ : syracuseStep 808223 = 1212335) B1212335
theorem B1004923 : Blo 626299 1004923 := bstep (se 1 (by rfl) ⟨753692, by rfl⟩ : syracuseStep 1004923 = 1507385) B1507385
theorem B5658017 : Blo 626299 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B2119175 : Blo 626299 2119175 := bstep (se 1 (by rfl) ⟨1589381, by rfl⟩ : syracuseStep 2119175 = 3178763) B3178763
theorem B939755 : Blo 626299 939755 := bstep (se 1 (by rfl) ⟨704816, by rfl⟩ : syracuseStep 939755 = 1409633) B1409633
theorem B12113657 : Blo 626299 12113657 := bstep (se 2 (by rfl) ⟨4542621, by rfl⟩ : syracuseStep 12113657 = 9085243) B9085243
theorem B939983 : Blo 626299 939983 := bstep (se 1 (by rfl) ⟨704987, by rfl⟩ : syracuseStep 939983 = 1409975) B1409975
theorem B1005833 : Blo 626299 1005833 := bstep (se 2 (by rfl) ⟨377187, by rfl⟩ : syracuseStep 1005833 = 754375) B754375
theorem B43538705 : Blo 626299 43538705 := bstep (se 2 (by rfl) ⟨16327014, by rfl⟩ : syracuseStep 43538705 = 32654029) B32654029
theorem B940379 : Blo 626299 940379 := bstep (se 1 (by rfl) ⟨705284, by rfl⟩ : syracuseStep 940379 = 1410569) B1410569
theorem B2120147 : Blo 626299 2120147 := bstep (se 1 (by rfl) ⟨1590110, by rfl⟩ : syracuseStep 2120147 = 3180221) B3180221
theorem B940607 : Blo 626299 940607 := bstep (se 1 (by rfl) ⟨705455, by rfl⟩ : syracuseStep 940607 = 1410911) B1410911
theorem B2120255 : Blo 626299 2120255 := bstep (se 1 (by rfl) ⟨1590191, by rfl⟩ : syracuseStep 2120255 = 3180383) B3180383
theorem B4774463 : Blo 626299 4774463 := bstep (se 1 (by rfl) ⟨3580847, by rfl⟩ : syracuseStep 4774463 = 7161695) B7161695
theorem B940727 : Blo 626299 940727 := bstep (se 1 (by rfl) ⟨705545, by rfl⟩ : syracuseStep 940727 = 1411091) B1411091
theorem B940955 : Blo 626299 940955 := bstep (se 1 (by rfl) ⟨705716, by rfl⟩ : syracuseStep 940955 = 1411433) B1411433
theorem B941351 : Blo 626299 941351 := bstep (se 1 (by rfl) ⟨706013, by rfl⟩ : syracuseStep 941351 = 1412027) B1412027
theorem B941435 : Blo 626299 941435 := bstep (se 1 (by rfl) ⟨706076, by rfl⟩ : syracuseStep 941435 = 1412153) B1412153
theorem B941561 : Blo 626299 941561 := bstep (se 2 (by rfl) ⟨353085, by rfl⟩ : syracuseStep 941561 = 706171) B706171
theorem B941663 : Blo 626299 941663 := bstep (se 1 (by rfl) ⟨706247, by rfl⟩ : syracuseStep 941663 = 1412495) B1412495
theorem B941879 : Blo 626299 941879 := bstep (se 1 (by rfl) ⟨706409, by rfl⟩ : syracuseStep 941879 = 1412819) B1412819
theorem B4349803 : Blo 626299 4349803 := bstep (se 1 (by rfl) ⟨3262352, by rfl⟩ : syracuseStep 4349803 = 6524705) B6524705
theorem B2416513 : Blo 626299 2416513 := bstep (se 2 (by rfl) ⟨906192, by rfl⟩ : syracuseStep 2416513 = 1812385) B1812385
theorem B942185 : Blo 626299 942185 := bstep (se 2 (by rfl) ⟨353319, by rfl⟩ : syracuseStep 942185 = 706639) B706639
theorem B2122091 : Blo 626299 2122091 := bstep (se 1 (by rfl) ⟨1591568, by rfl⟩ : syracuseStep 2122091 = 3183137) B3183137
theorem B942503 : Blo 626299 942503 := bstep (se 1 (by rfl) ⟨706877, by rfl⟩ : syracuseStep 942503 = 1413755) B1413755
theorem B942587 : Blo 626299 942587 := bstep (se 1 (by rfl) ⟨706940, by rfl⟩ : syracuseStep 942587 = 1413881) B1413881
theorem B942713 : Blo 626299 942713 := bstep (se 2 (by rfl) ⟨353517, by rfl⟩ : syracuseStep 942713 = 707035) B707035
theorem B2122361 : Blo 626299 2122361 := bstep (se 2 (by rfl) ⟨795885, by rfl⟩ : syracuseStep 2122361 = 1591771) B1591771
theorem B3170987 : Blo 626299 3170987 := bstep (se 1 (by rfl) ⟨2378240, by rfl⟩ : syracuseStep 3170987 = 4756481) B4756481
theorem B942767 : Blo 626299 942767 := bstep (se 1 (by rfl) ⟨707075, by rfl⟩ : syracuseStep 942767 = 1414151) B1414151
theorem B3400375 : Blo 626299 3400375 := bstep (se 1 (by rfl) ⟨2550281, by rfl⟩ : syracuseStep 3400375 = 5100563) B5100563
theorem B942815 : Blo 626299 942815 := bstep (se 1 (by rfl) ⟨707111, by rfl⟩ : syracuseStep 942815 = 1414223) B1414223
theorem B2548675 : Blo 626299 2548675 := bstep (se 1 (by rfl) ⟨1911506, by rfl⟩ : syracuseStep 2548675 = 3823013) B3823013
theorem B943079 : Blo 626299 943079 := bstep (se 1 (by rfl) ⟨707309, by rfl⟩ : syracuseStep 943079 = 1414619) B1414619
theorem B3171473 : Blo 626299 3171473 := bstep (se 2 (by rfl) ⟨1189302, by rfl⟩ : syracuseStep 3171473 = 2378605) B2378605
theorem B2679965 : Blo 626299 2679965 := bstep (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) B1004987
theorem B1696987 : Blo 626299 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B943337 : Blo 626299 943337 := bstep (se 2 (by rfl) ⟨353751, by rfl⟩ : syracuseStep 943337 = 707503) B707503
theorem B943391 : Blo 626299 943391 := bstep (se 1 (by rfl) ⟨707543, by rfl⟩ : syracuseStep 943391 = 1415087) B1415087
theorem B943559 : Blo 626299 943559 := bstep (se 1 (by rfl) ⟨707669, by rfl⟩ : syracuseStep 943559 = 1415339) B1415339
theorem B1009415 : Blo 626299 1009415 := bstep (se 1 (by rfl) ⟨757061, by rfl⟩ : syracuseStep 1009415 = 1514123) B1514123
theorem B943913 : Blo 626299 943913 := bstep (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) B707935
theorem B1074991 : Blo 626299 1074991 := bstep (se 1 (by rfl) ⟨806243, by rfl⟩ : syracuseStep 1074991 = 1612487) B1612487
theorem B943919 : Blo 626299 943919 := bstep (se 1 (by rfl) ⟨707939, by rfl⟩ : syracuseStep 943919 = 1415879) B1415879
theorem B4417361 : Blo 626299 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B9070481 : Blo 626299 9070481 := bstep (se 2 (by rfl) ⟨3401430, by rfl⟩ : syracuseStep 9070481 = 6802861) B6802861
theorem B8054963 : Blo 626299 8054963 := bstep (se 1 (by rfl) ⟨6041222, by rfl⟩ : syracuseStep 8054963 = 12082445) B12082445
theorem B944393 : Blo 626299 944393 := bstep (se 2 (by rfl) ⟨354147, by rfl⟩ : syracuseStep 944393 = 708295) B708295
theorem B9038141 : Blo 626299 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B4778351 : Blo 626299 4778351 := bstep (se 1 (by rfl) ⟨3583763, by rfl⟩ : syracuseStep 4778351 = 7167527) B7167527
theorem B2124143 : Blo 626299 2124143 := bstep (se 1 (by rfl) ⟨1593107, by rfl⟩ : syracuseStep 2124143 = 3186215) B3186215
theorem B944495 : Blo 626299 944495 := bstep (se 1 (by rfl) ⟨708371, by rfl⟩ : syracuseStep 944495 = 1416743) B1416743
theorem B2681383 : Blo 626299 2681383 := bstep (se 1 (by rfl) ⟨2011037, by rfl⟩ : syracuseStep 2681383 = 4022075) B4022075
theorem B944711 : Blo 626299 944711 := bstep (se 1 (by rfl) ⟨708533, by rfl⟩ : syracuseStep 944711 = 1417067) B1417067
theorem B944747 : Blo 626299 944747 := bstep (se 1 (by rfl) ⟨708560, by rfl⟩ : syracuseStep 944747 = 1417121) B1417121
theorem B944975 : Blo 626299 944975 := bstep (se 1 (by rfl) ⟨708731, by rfl⟩ : syracuseStep 944975 = 1417463) B1417463
theorem B4025483 : Blo 626299 4025483 := bstep (se 1 (by rfl) ⟨3019112, by rfl⟩ : syracuseStep 4025483 = 6038225) B6038225
theorem B945371 : Blo 626299 945371 := bstep (se 1 (by rfl) ⟨709028, by rfl⟩ : syracuseStep 945371 = 1418057) B1418057
theorem B10349855 : Blo 626299 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B6810911 : Blo 626299 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B3403075 : Blo 626299 3403075 := bstep (se 1 (by rfl) ⟨2552306, by rfl⟩ : syracuseStep 3403075 = 5104613) B5104613
theorem B1437115 : Blo 626299 1437115 := bstep (se 1 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 1437115 = 2155673) B2155673
theorem B3173903 : Blo 626299 3173903 := bstep (se 1 (by rfl) ⟨2380427, by rfl⟩ : syracuseStep 3173903 = 4760855) B4760855
theorem B2125547 : Blo 626299 2125547 := bstep (se 1 (by rfl) ⟨1594160, by rfl⟩ : syracuseStep 2125547 = 3188321) B3188321
theorem B2682665 : Blo 626299 2682665 := bstep (se 2 (by rfl) ⟨1005999, by rfl⟩ : syracuseStep 2682665 = 2011999) B2011999
theorem B1273657 : Blo 626299 1273657 := bstep (se 2 (by rfl) ⟨477621, by rfl⟩ : syracuseStep 1273657 = 955243) B955243
theorem B3436445 : Blo 626299 3436445 := bstep (se 3 (by rfl) ⟨644333, by rfl⟩ : syracuseStep 3436445 = 1288667) B1288667
theorem B5828561 : Blo 626299 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B3174875 : Blo 626299 3174875 := bstep (se 1 (by rfl) ⟨2381156, by rfl⟩ : syracuseStep 3174875 = 4762313) B4762313
theorem B815611 : Blo 626299 815611 := bstep (se 1 (by rfl) ⟨611708, by rfl⟩ : syracuseStep 815611 = 1223417) B1223417
theorem B11596385 : Blo 626299 11596385 := bstep (se 2 (by rfl) ⟨4348644, by rfl⟩ : syracuseStep 11596385 = 8697289) B8697289
theorem B2126519 : Blo 626299 2126519 := bstep (se 1 (by rfl) ⟨1594889, by rfl⟩ : syracuseStep 2126519 = 3189779) B3189779
theorem B1340239 : Blo 626299 1340239 := bstep (se 1 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 1340239 = 2010359) B2010359
theorem B3175361 : Blo 626299 3175361 := bstep (se 2 (by rfl) ⟨1190760, by rfl⟩ : syracuseStep 3175361 = 2381521) B2381521
theorem B2552795 : Blo 626299 2552795 := bstep (se 1 (by rfl) ⟨1914596, by rfl⟩ : syracuseStep 2552795 = 3829193) B3829193
theorem B12088439 : Blo 626299 12088439 := bstep (se 1 (by rfl) ⟨9066329, by rfl⟩ : syracuseStep 12088439 = 18132659) B18132659
theorem B3634301 : Blo 626299 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B2684269 : Blo 626299 2684269 := bstep (se 3 (by rfl) ⟨503300, by rfl⟩ : syracuseStep 2684269 = 1006601) B1006601
theorem B4781753 : Blo 626299 4781753 := bstep (se 2 (by rfl) ⟨1793157, by rfl⟩ : syracuseStep 4781753 = 3586315) B3586315
theorem B17201251 : Blo 626299 17201251 := bstep (se 1 (by rfl) ⟨12900938, by rfl⟩ : syracuseStep 17201251 = 25801877) B25801877
theorem B6781157 : Blo 626299 6781157 := bstep (se 4 (by rfl) ⟨635733, by rfl⟩ : syracuseStep 6781157 = 1271467) B1271467
theorem B2390269 : Blo 626299 2390269 := bstep (se 3 (by rfl) ⟨448175, by rfl⟩ : syracuseStep 2390269 = 896351) B896351
theorem B43514329 : Blo 626299 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B1341947 : Blo 626299 1341947 := bstep (se 1 (by rfl) ⟨1006460, by rfl⟩ : syracuseStep 1341947 = 2012921) B2012921
theorem B4291145 : Blo 626299 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B4782725 : Blo 626299 4782725 := bstep (se 4 (by rfl) ⟨448380, by rfl⟩ : syracuseStep 4782725 = 896761) B896761
theorem B3570551 : Blo 626299 3570551 := bstep (se 1 (by rfl) ⟨2677913, by rfl⟩ : syracuseStep 3570551 = 5355827) B5355827
theorem B752539 : Blo 626299 752539 := bstep (se 1 (by rfl) ⟨564404, by rfl⟩ : syracuseStep 752539 = 1128809) B1128809
theorem B2391545 : Blo 626299 2391545 := bstep (se 2 (by rfl) ⟨896829, by rfl⟩ : syracuseStep 2391545 = 1793659) B1793659
theorem B4783697 : Blo 626299 4783697 := bstep (se 2 (by rfl) ⟨1793886, by rfl⟩ : syracuseStep 4783697 = 3587773) B3587773
theorem B2391713 : Blo 626299 2391713 := bstep (se 2 (by rfl) ⟨896892, by rfl⟩ : syracuseStep 2391713 = 1793785) B1793785
theorem B5078791 : Blo 626299 5078791 := bstep (se 1 (by rfl) ⟨3809093, by rfl⟩ : syracuseStep 5078791 = 7618187) B7618187
theorem B4292459 : Blo 626299 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B1409255 : Blo 626299 1409255 := bstep (se 1 (by rfl) ⟨1056941, by rfl⟩ : syracuseStep 1409255 = 2113883) B2113883
theorem B1409849 : Blo 626299 1409849 := bstep (se 2 (by rfl) ⟨528693, by rfl⟩ : syracuseStep 1409849 = 1057387) B1057387
theorem B1409903 : Blo 626299 1409903 := bstep (se 1 (by rfl) ⟨1057427, by rfl⟩ : syracuseStep 1409903 = 2114855) B2114855
theorem B4031633 : Blo 626299 4031633 := bstep (se 2 (by rfl) ⟨1511862, by rfl⟩ : syracuseStep 4031633 = 3023725) B3023725
theorem B1410479 : Blo 626299 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B2262649 : Blo 626299 2262649 := bstep (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) B1696987
theorem B1411307 : Blo 626299 1411307 := bstep (se 1 (by rfl) ⟨1058480, by rfl⟩ : syracuseStep 1411307 = 2116961) B2116961
theorem B1608379 : Blo 626299 1608379 := bstep (se 1 (by rfl) ⟨1206284, by rfl⟩ : syracuseStep 1608379 = 2412569) B2412569
theorem B3575177 : Blo 626299 3575177 := bstep (se 2 (by rfl) ⟨1340691, by rfl⟩ : syracuseStep 3575177 = 2681383) B2681383
theorem B1510825 : Blo 626299 1510825 := bstep (se 2 (by rfl) ⟨566559, by rfl⟩ : syracuseStep 1510825 = 1133119) B1133119
theorem B953831 : Blo 626299 953831 := bstep (se 1 (by rfl) ⟨715373, by rfl⟩ : syracuseStep 953831 = 1430747) B1430747
theorem B1412603 : Blo 626299 1412603 := bstep (se 1 (by rfl) ⟨1059452, by rfl⟩ : syracuseStep 1412603 = 2118905) B2118905
theorem B1412783 : Blo 626299 1412783 := bstep (se 1 (by rfl) ⟨1059587, by rfl⟩ : syracuseStep 1412783 = 2119175) B2119175
theorem B626503 : Blo 626299 626503 := bstep (se 1 (by rfl) ⟨469877, by rfl⟩ : syracuseStep 626503 = 939755) B939755
theorem B626655 : Blo 626299 626655 := bstep (se 1 (by rfl) ⟨469991, by rfl⟩ : syracuseStep 626655 = 939983) B939983
theorem B3182813 : Blo 626299 3182813 := bstep (se 3 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 3182813 = 1193555) B1193555
theorem B626919 : Blo 626299 626919 := bstep (se 1 (by rfl) ⟨470189, by rfl⟩ : syracuseStep 626919 = 940379) B940379
theorem B1413431 : Blo 626299 1413431 := bstep (se 1 (by rfl) ⟨1060073, by rfl⟩ : syracuseStep 1413431 = 2120147) B2120147
theorem B627071 : Blo 626299 627071 := bstep (se 1 (by rfl) ⟨470303, by rfl⟩ : syracuseStep 627071 = 940607) B940607
theorem B1413503 : Blo 626299 1413503 := bstep (se 1 (by rfl) ⟨1060127, by rfl⟩ : syracuseStep 1413503 = 2120255) B2120255
theorem B3182975 : Blo 626299 3182975 := bstep (se 1 (by rfl) ⟨2387231, by rfl⟩ : syracuseStep 3182975 = 4774463) B4774463
theorem B627151 : Blo 626299 627151 := bstep (se 1 (by rfl) ⟨470363, by rfl⟩ : syracuseStep 627151 = 940727) B940727
theorem B627303 : Blo 626299 627303 := bstep (se 1 (by rfl) ⟨470477, by rfl⟩ : syracuseStep 627303 = 940955) B940955
theorem B1020713 : Blo 626299 1020713 := bstep (se 2 (by rfl) ⟨382767, by rfl⟩ : syracuseStep 1020713 = 765535) B765535
theorem B627567 : Blo 626299 627567 := bstep (se 1 (by rfl) ⟨470675, by rfl⟩ : syracuseStep 627567 = 941351) B941351
theorem B627623 : Blo 626299 627623 := bstep (se 1 (by rfl) ⟨470717, by rfl⟩ : syracuseStep 627623 = 941435) B941435
theorem B627707 : Blo 626299 627707 := bstep (se 1 (by rfl) ⟨470780, by rfl⟩ : syracuseStep 627707 = 941561) B941561
theorem B627775 : Blo 626299 627775 := bstep (se 1 (by rfl) ⟨470831, by rfl⟩ : syracuseStep 627775 = 941663) B941663
theorem B627919 : Blo 626299 627919 := bstep (se 1 (by rfl) ⟨470939, by rfl⟩ : syracuseStep 627919 = 941879) B941879
theorem B628123 : Blo 626299 628123 := bstep (se 1 (by rfl) ⟨471092, by rfl⟩ : syracuseStep 628123 = 942185) B942185
theorem B1414727 : Blo 626299 1414727 := bstep (se 1 (by rfl) ⟨1061045, by rfl⟩ : syracuseStep 1414727 = 2122091) B2122091
theorem B628335 : Blo 626299 628335 := bstep (se 1 (by rfl) ⟨471251, by rfl⟩ : syracuseStep 628335 = 942503) B942503
theorem B628391 : Blo 626299 628391 := bstep (se 1 (by rfl) ⟨471293, by rfl⟩ : syracuseStep 628391 = 942587) B942587
theorem B8066749 : Blo 626299 8066749 := bstep (se 3 (by rfl) ⟨1512515, by rfl⟩ : syracuseStep 8066749 = 3025031) B3025031
theorem B628475 : Blo 626299 628475 := bstep (se 1 (by rfl) ⟨471356, by rfl⟩ : syracuseStep 628475 = 942713) B942713
theorem B1414907 : Blo 626299 1414907 := bstep (se 1 (by rfl) ⟨1061180, by rfl⟩ : syracuseStep 1414907 = 2122361) B2122361
theorem B628511 : Blo 626299 628511 := bstep (se 1 (by rfl) ⟨471383, by rfl⟩ : syracuseStep 628511 = 942767) B942767
theorem B628543 : Blo 626299 628543 := bstep (se 1 (by rfl) ⟨471407, by rfl⟩ : syracuseStep 628543 = 942815) B942815
theorem B628719 : Blo 626299 628719 := bstep (se 1 (by rfl) ⟨471539, by rfl⟩ : syracuseStep 628719 = 943079) B943079
theorem B1087481 : Blo 626299 1087481 := bstep (se 2 (by rfl) ⟨407805, by rfl⟩ : syracuseStep 1087481 = 815611) B815611
theorem B628891 : Blo 626299 628891 := bstep (se 1 (by rfl) ⟨471668, by rfl⟩ : syracuseStep 628891 = 943337) B943337
theorem B792767 : Blo 626299 792767 := bstep (se 1 (by rfl) ⟨594575, by rfl⟩ : syracuseStep 792767 = 1189151) B1189151
theorem B628927 : Blo 626299 628927 := bstep (se 1 (by rfl) ⟨471695, by rfl⟩ : syracuseStep 628927 = 943391) B943391
theorem B1415465 : Blo 626299 1415465 := bstep (se 2 (by rfl) ⟨530799, by rfl⟩ : syracuseStep 1415465 = 1061599) B1061599
theorem B629039 : Blo 626299 629039 := bstep (se 1 (by rfl) ⟨471779, by rfl⟩ : syracuseStep 629039 = 943559) B943559
theorem B629275 : Blo 626299 629275 := bstep (se 1 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 629275 = 943913) B943913
theorem B629279 : Blo 626299 629279 := bstep (se 1 (by rfl) ⟨471959, by rfl⟩ : syracuseStep 629279 = 943919) B943919
theorem B1940089 : Blo 626299 1940089 := bstep (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) B1455067
theorem B3578525 : Blo 626299 3578525 := bstep (se 3 (by rfl) ⟨670973, by rfl⟩ : syracuseStep 3578525 = 1341947) B1341947
theorem B1514323 : Blo 626299 1514323 := bstep (se 1 (by rfl) ⟨1135742, by rfl⟩ : syracuseStep 1514323 = 2271485) B2271485
theorem B629595 : Blo 626299 629595 := bstep (se 1 (by rfl) ⟨472196, by rfl⟩ : syracuseStep 629595 = 944393) B944393
theorem B1416041 : Blo 626299 1416041 := bstep (se 2 (by rfl) ⟨531015, by rfl⟩ : syracuseStep 1416041 = 1062031) B1062031
theorem B3185567 : Blo 626299 3185567 := bstep (se 1 (by rfl) ⟨2389175, by rfl⟩ : syracuseStep 3185567 = 4778351) B4778351
theorem B1416095 : Blo 626299 1416095 := bstep (se 1 (by rfl) ⟨1062071, by rfl⟩ : syracuseStep 1416095 = 2124143) B2124143
theorem B629663 : Blo 626299 629663 := bstep (se 1 (by rfl) ⟨472247, by rfl⟩ : syracuseStep 629663 = 944495) B944495
theorem B629807 : Blo 626299 629807 := bstep (se 1 (by rfl) ⟨472355, by rfl⟩ : syracuseStep 629807 = 944711) B944711
theorem B629831 : Blo 626299 629831 := bstep (se 1 (by rfl) ⟨472373, by rfl⟩ : syracuseStep 629831 = 944747) B944747
theorem B3579025 : Blo 626299 3579025 := bstep (se 2 (by rfl) ⟨1342134, by rfl⟩ : syracuseStep 3579025 = 2684269) B2684269
theorem B629983 : Blo 626299 629983 := bstep (se 1 (by rfl) ⟨472487, by rfl⟩ : syracuseStep 629983 = 944975) B944975
theorem B630247 : Blo 626299 630247 := bstep (se 1 (by rfl) ⟨472685, by rfl⟩ : syracuseStep 630247 = 945371) B945371
theorem B1417031 : Blo 626299 1417031 := bstep (se 1 (by rfl) ⟨1062773, by rfl⟩ : syracuseStep 1417031 = 2125547) B2125547
theorem B2236285 : Blo 626299 2236285 := bstep (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) B838607
theorem B1056955 : Blo 626299 1056955 := bstep (se 1 (by rfl) ⟨792716, by rfl⟩ : syracuseStep 1056955 = 1585433) B1585433
theorem B3187025 : Blo 626299 3187025 := bstep (se 2 (by rfl) ⟨1195134, by rfl⟩ : syracuseStep 3187025 = 2390269) B2390269
theorem B1057151 : Blo 626299 1057151 := bstep (se 1 (by rfl) ⟨792863, by rfl⟩ : syracuseStep 1057151 = 1585727) B1585727
theorem B1417679 : Blo 626299 1417679 := bstep (se 1 (by rfl) ⟨1063259, by rfl⟩ : syracuseStep 1417679 = 2126519) B2126519
theorem B1057583 : Blo 626299 1057583 := bstep (se 1 (by rfl) ⟨793187, by rfl⟩ : syracuseStep 1057583 = 1586375) B1586375
theorem B3187835 : Blo 626299 3187835 := bstep (se 1 (by rfl) ⟨2390876, by rfl⟩ : syracuseStep 3187835 = 4781753) B4781753
theorem B1910191 : Blo 626299 1910191 := bstep (se 1 (by rfl) ⟨1432643, by rfl⟩ : syracuseStep 1910191 = 2865287) B2865287
theorem B2860763 : Blo 626299 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B1058555 : Blo 626299 1058555 := bstep (se 1 (by rfl) ⟨793916, by rfl⟩ : syracuseStep 1058555 = 1587833) B1587833
theorem B6039299 : Blo 626299 6039299 := bstep (se 1 (by rfl) ⟨4529474, by rfl⟩ : syracuseStep 6039299 = 9058949) B9058949
theorem B3188483 : Blo 626299 3188483 := bstep (se 1 (by rfl) ⟨2391362, by rfl⟩ : syracuseStep 3188483 = 4782725) B4782725
theorem B1058791 : Blo 626299 1058791 := bstep (se 1 (by rfl) ⟨794093, by rfl⟩ : syracuseStep 1058791 = 1588187) B1588187
theorem B796655 : Blo 626299 796655 := bstep (se 1 (by rfl) ⟨597491, by rfl⟩ : syracuseStep 796655 = 1194983) B1194983
theorem B5351453 : Blo 626299 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B1059007 : Blo 626299 1059007 := bstep (se 1 (by rfl) ⟨794255, by rfl⟩ : syracuseStep 1059007 = 1588511) B1588511
theorem B1190123 : Blo 626299 1190123 := bstep (se 1 (by rfl) ⟨892592, by rfl⟩ : syracuseStep 1190123 = 1785185) B1785185
theorem B3189131 : Blo 626299 3189131 := bstep (se 1 (by rfl) ⟨2391848, by rfl⟩ : syracuseStep 3189131 = 4783697) B4783697
theorem B3222017 : Blo 626299 3222017 := bstep (se 2 (by rfl) ⟨1208256, by rfl⟩ : syracuseStep 3222017 = 2416513) B2416513
theorem B2861639 : Blo 626299 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B895799 : Blo 626299 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B1059743 : Blo 626299 1059743 := bstep (se 1 (by rfl) ⟨794807, by rfl⟩ : syracuseStep 1059743 = 1589615) B1589615
theorem B1912031 : Blo 626299 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B4533515 : Blo 626299 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B1060175 : Blo 626299 1060175 := bstep (se 1 (by rfl) ⟨795131, by rfl⟩ : syracuseStep 1060175 = 1590263) B1590263
theorem B3190103 : Blo 626299 3190103 := bstep (se 1 (by rfl) ⟨2392577, by rfl⟩ : syracuseStep 3190103 = 4785155) B4785155
theorem B4533833 : Blo 626299 4533833 := bstep (se 2 (by rfl) ⟨1700187, by rfl⟩ : syracuseStep 4533833 = 3400375) B3400375
theorem B3190751 : Blo 626299 3190751 := bstep (se 1 (by rfl) ⟨2393063, by rfl⟩ : syracuseStep 3190751 = 4786127) B4786127
theorem B14495915 : Blo 626299 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B1061471 : Blo 626299 1061471 := bstep (se 1 (by rfl) ⟨796103, by rfl⟩ : syracuseStep 1061471 = 1592207) B1592207
theorem B3388331 : Blo 626299 3388331 := bstep (se 1 (by rfl) ⟨2541248, by rfl⟩ : syracuseStep 3388331 = 5082497) B5082497
theorem B1815547 : Blo 626299 1815547 := bstep (se 1 (by rfl) ⟨1361660, by rfl⟩ : syracuseStep 1815547 = 2723321) B2723321
theorem B2012435 : Blo 626299 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B1586587 : Blo 626299 1586587 := bstep (se 1 (by rfl) ⟨1189940, by rfl⟩ : syracuseStep 1586587 = 2379881) B2379881
theorem B58963457 : Blo 626299 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B5355143 : Blo 626299 5355143 := bstep (se 1 (by rfl) ⟨4016357, by rfl⟩ : syracuseStep 5355143 = 8032715) B8032715
theorem B1193791 : Blo 626299 1193791 := bstep (se 1 (by rfl) ⟨895343, by rfl⟩ : syracuseStep 1193791 = 1790687) B1790687
theorem B1062895 : Blo 626299 1062895 := bstep (se 1 (by rfl) ⟨797171, by rfl⟩ : syracuseStep 1062895 = 1594343) B1594343
theorem B1063145 : Blo 626299 1063145 := bstep (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) B797359
theorem B15088045 : Blo 626299 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B8075771 : Blo 626299 8075771 := bstep (se 1 (by rfl) ⟨6056828, by rfl⟩ : syracuseStep 8075771 = 12113657) B12113657
theorem B2013817 : Blo 626299 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B670555 : Blo 626299 670555 := bstep (se 1 (by rfl) ⟨502916, by rfl⟩ : syracuseStep 670555 = 1005833) B1005833
theorem B1719265 : Blo 626299 1719265 := bstep (se 2 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 1719265 = 1289449) B1289449
theorem B4537433 : Blo 626299 4537433 := bstep (se 2 (by rfl) ⟨1701537, by rfl⟩ : syracuseStep 4537433 = 3403075) B3403075
theorem B1916153 : Blo 626299 1916153 := bstep (se 2 (by rfl) ⟨718557, by rfl⟩ : syracuseStep 1916153 = 1437115) B1437115
theorem B3587591 : Blo 626299 3587591 := bstep (se 1 (by rfl) ⟨2690693, by rfl⟩ : syracuseStep 3587591 = 5381387) B5381387
theorem B2015047 : Blo 626299 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B4767659 : Blo 626299 4767659 := bstep (se 1 (by rfl) ⟨3575744, by rfl⟩ : syracuseStep 4767659 = 7151489) B7151489
theorem B3588299 : Blo 626299 3588299 := bstep (se 1 (by rfl) ⟨2691224, by rfl⟩ : syracuseStep 3588299 = 5382449) B5382449
theorem B2113991 : Blo 626299 2113991 := bstep (se 1 (by rfl) ⟨1585493, by rfl⟩ : syracuseStep 2113991 = 3170987) B3170987
theorem B705127 : Blo 626299 705127 := bstep (se 1 (by rfl) ⟨528845, by rfl⟩ : syracuseStep 705127 = 1057691) B1057691
theorem B2114315 : Blo 626299 2114315 := bstep (se 1 (by rfl) ⟨1585736, by rfl⟩ : syracuseStep 2114315 = 3171473) B3171473
theorem B1786643 : Blo 626299 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B4768631 : Blo 626299 4768631 := bstep (se 1 (by rfl) ⟨3576473, by rfl⟩ : syracuseStep 4768631 = 7152947) B7152947
theorem B2114585 : Blo 626299 2114585 := bstep (se 2 (by rfl) ⟨792969, by rfl⟩ : syracuseStep 2114585 = 1585939) B1585939
theorem B1786985 : Blo 626299 1786985 := bstep (se 2 (by rfl) ⟨670119, by rfl⟩ : syracuseStep 1786985 = 1340239) B1340239
theorem B672943 : Blo 626299 672943 := bstep (se 1 (by rfl) ⟨504707, by rfl⟩ : syracuseStep 672943 = 1009415) B1009415
theorem B6046987 : Blo 626299 6046987 := bstep (se 1 (by rfl) ⟨4535240, by rfl⟩ : syracuseStep 6046987 = 9070481) B9070481
theorem B2115233 : Blo 626299 2115233 := bstep (se 2 (by rfl) ⟨793212, by rfl⟩ : syracuseStep 2115233 = 1586425) B1586425
theorem B6899903 : Blo 626299 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B4540607 : Blo 626299 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B2148665 : Blo 626299 2148665 := bstep (se 2 (by rfl) ⟨805749, by rfl⟩ : syracuseStep 2148665 = 1611499) B1611499
theorem B1591609 : Blo 626299 1591609 := bstep (se 2 (by rfl) ⟨596853, by rfl⟩ : syracuseStep 1591609 = 1193707) B1193707
theorem B2115935 : Blo 626299 2115935 := bstep (se 1 (by rfl) ⟨1586951, by rfl⟩ : syracuseStep 2115935 = 3173903) B3173903
theorem B2116097 : Blo 626299 2116097 := bstep (se 2 (by rfl) ⟨793536, by rfl⟩ : syracuseStep 2116097 = 1587073) B1587073
theorem B1788443 : Blo 626299 1788443 := bstep (se 1 (by rfl) ⟨1341332, by rfl⟩ : syracuseStep 1788443 = 2682665) B2682665
theorem B1591913 : Blo 626299 1591913 := bstep (se 2 (by rfl) ⟨596967, by rfl⟩ : syracuseStep 1591913 = 1193935) B1193935
theorem B3885707 : Blo 626299 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B2116583 : Blo 626299 2116583 := bstep (se 1 (by rfl) ⟨1587437, by rfl⟩ : syracuseStep 2116583 = 3174875) B3174875
theorem B58019105 : Blo 626299 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B2116907 : Blo 626299 2116907 := bstep (se 1 (by rfl) ⟨1587680, by rfl⟩ : syracuseStep 2116907 = 3175361) B3175361
theorem B2117177 : Blo 626299 2117177 := bstep (se 2 (by rfl) ⟨793941, by rfl⟩ : syracuseStep 2117177 = 1587883) B1587883
theorem B1592905 : Blo 626299 1592905 := bstep (se 2 (by rfl) ⟨597339, by rfl⟩ : syracuseStep 1592905 = 1194679) B1194679
theorem B708187 : Blo 626299 708187 := bstep (se 1 (by rfl) ⟨531140, by rfl⟩ : syracuseStep 708187 = 1062281) B1062281
theorem B1003385 : Blo 626299 1003385 := bstep (se 2 (by rfl) ⟨376269, by rfl⟩ : syracuseStep 1003385 = 752539) B752539
theorem B1593209 : Blo 626299 1593209 := bstep (se 2 (by rfl) ⟨597453, by rfl⟩ : syracuseStep 1593209 = 1194907) B1194907
theorem B708475 : Blo 626299 708475 := bstep (se 1 (by rfl) ⟨531356, by rfl⟩ : syracuseStep 708475 = 1062713) B1062713
theorem B27086885 : Blo 626299 27086885 := bstep (se 4 (by rfl) ⟨2539395, by rfl⟩ : syracuseStep 27086885 = 5078791) B5078791
theorem B3625181 : Blo 626299 3625181 := bstep (se 3 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 3625181 = 1359443) B1359443
theorem B2150927 : Blo 626299 2150927 := bstep (se 1 (by rfl) ⟨1613195, by rfl⟩ : syracuseStep 2150927 = 3226391) B3226391
theorem B8573485 : Blo 626299 8573485 := bstep (se 3 (by rfl) ⟨1607528, by rfl⟩ : syracuseStep 8573485 = 3215057) B3215057
theorem B2380367 : Blo 626299 2380367 := bstep (se 1 (by rfl) ⟨1785275, by rfl⟩ : syracuseStep 2380367 = 3570551) B3570551
theorem B1594363 : Blo 626299 1594363 := bstep (se 1 (by rfl) ⟨1195772, by rfl⟩ : syracuseStep 1594363 = 2391545) B2391545
theorem B1594475 : Blo 626299 1594475 := bstep (se 1 (by rfl) ⟨1195856, by rfl⟩ : syracuseStep 1594475 = 2391713) B2391713
theorem B2119067 : Blo 626299 2119067 := bstep (se 1 (by rfl) ⟨1589300, by rfl⟩ : syracuseStep 2119067 = 3178601) B3178601
theorem B1594849 : Blo 626299 1594849 := bstep (se 2 (by rfl) ⟨598068, by rfl⟩ : syracuseStep 1594849 = 1196137) B1196137
theorem B939641 : Blo 626299 939641 := bstep (se 2 (by rfl) ⟨352365, by rfl⟩ : syracuseStep 939641 = 704731) B704731
theorem B939743 : Blo 626299 939743 := bstep (se 1 (by rfl) ⟨704807, by rfl⟩ : syracuseStep 939743 = 1409615) B1409615
theorem B1791791 : Blo 626299 1791791 := bstep (se 1 (by rfl) ⟨1343843, by rfl⟩ : syracuseStep 1791791 = 2687687) B2687687
theorem B939839 : Blo 626299 939839 := bstep (se 1 (by rfl) ⟨704879, by rfl⟩ : syracuseStep 939839 = 1409759) B1409759
theorem B4020151 : Blo 626299 4020151 := bstep (se 1 (by rfl) ⟨3015113, by rfl⟩ : syracuseStep 4020151 = 6030227) B6030227
theorem B940007 : Blo 626299 940007 := bstep (se 1 (by rfl) ⟨705005, by rfl⟩ : syracuseStep 940007 = 1410011) B1410011
theorem B1005551 : Blo 626299 1005551 := bstep (se 1 (by rfl) ⟨754163, by rfl⟩ : syracuseStep 1005551 = 1508327) B1508327
theorem B940025 : Blo 626299 940025 := bstep (se 2 (by rfl) ⟨352509, by rfl⟩ : syracuseStep 940025 = 705019) B705019
theorem B940127 : Blo 626299 940127 := bstep (se 1 (by rfl) ⟨705095, by rfl⟩ : syracuseStep 940127 = 1410191) B1410191
theorem B2119823 : Blo 626299 2119823 := bstep (se 1 (by rfl) ⟨1589867, by rfl⟩ : syracuseStep 2119823 = 3179735) B3179735
theorem B940187 : Blo 626299 940187 := bstep (se 1 (by rfl) ⟨705140, by rfl⟩ : syracuseStep 940187 = 1410281) B1410281
theorem B940223 : Blo 626299 940223 := bstep (se 1 (by rfl) ⟨705167, by rfl⟩ : syracuseStep 940223 = 1410335) B1410335
theorem B940265 : Blo 626299 940265 := bstep (se 2 (by rfl) ⟨352599, by rfl⟩ : syracuseStep 940265 = 705199) B705199
theorem B8608123 : Blo 626299 8608123 := bstep (se 1 (by rfl) ⟨6456092, by rfl⟩ : syracuseStep 8608123 = 12912185) B12912185
theorem B940571 : Blo 626299 940571 := bstep (se 1 (by rfl) ⟨705428, by rfl⟩ : syracuseStep 940571 = 1410857) B1410857
theorem B3398233 : Blo 626299 3398233 := bstep (se 2 (by rfl) ⟨1274337, by rfl⟩ : syracuseStep 3398233 = 2548675) B2548675
theorem B940649 : Blo 626299 940649 := bstep (se 2 (by rfl) ⟨352743, by rfl⟩ : syracuseStep 940649 = 705487) B705487
theorem B2382493 : Blo 626299 2382493 := bstep (se 3 (by rfl) ⟨446717, by rfl⟩ : syracuseStep 2382493 = 893435) B893435
theorem B4021073 : Blo 626299 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B941177 : Blo 626299 941177 := bstep (se 2 (by rfl) ⟨352941, by rfl⟩ : syracuseStep 941177 = 705883) B705883
theorem B8150219 : Blo 626299 8150219 := bstep (se 1 (by rfl) ⟨6112664, by rfl⟩ : syracuseStep 8150219 = 12225329) B12225329
theorem B941279 : Blo 626299 941279 := bstep (se 1 (by rfl) ⟨705959, by rfl⟩ : syracuseStep 941279 = 1411919) B1411919
theorem B2120957 : Blo 626299 2120957 := bstep (se 3 (by rfl) ⟨397679, by rfl⟩ : syracuseStep 2120957 = 795359) B795359
theorem B941321 : Blo 626299 941321 := bstep (se 2 (by rfl) ⟨352995, by rfl⟩ : syracuseStep 941321 = 705991) B705991
theorem B11492675 : Blo 626299 11492675 := bstep (se 1 (by rfl) ⟨8619506, by rfl⟩ : syracuseStep 11492675 = 17239013) B17239013
theorem B941423 : Blo 626299 941423 := bstep (se 1 (by rfl) ⟨706067, by rfl⟩ : syracuseStep 941423 = 1412135) B1412135
theorem B941543 : Blo 626299 941543 := bstep (se 1 (by rfl) ⟨706157, by rfl⟩ : syracuseStep 941543 = 1412315) B1412315
theorem B941675 : Blo 626299 941675 := bstep (se 1 (by rfl) ⟨706256, by rfl⟩ : syracuseStep 941675 = 1412513) B1412513
theorem B941801 : Blo 626299 941801 := bstep (se 2 (by rfl) ⟨353175, by rfl⟩ : syracuseStep 941801 = 706351) B706351
theorem B1433321 : Blo 626299 1433321 := bstep (se 2 (by rfl) ⟨537495, by rfl⟩ : syracuseStep 1433321 = 1074991) B1074991
theorem B941945 : Blo 626299 941945 := bstep (se 2 (by rfl) ⟨353229, by rfl⟩ : syracuseStep 941945 = 706459) B706459
theorem B2383739 : Blo 626299 2383739 := bstep (se 1 (by rfl) ⟨1787804, by rfl⟩ : syracuseStep 2383739 = 3575609) B3575609
theorem B942047 : Blo 626299 942047 := bstep (se 1 (by rfl) ⟨706535, by rfl⟩ : syracuseStep 942047 = 1413071) B1413071
theorem B2121767 : Blo 626299 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B7135451 : Blo 626299 7135451 := bstep (se 1 (by rfl) ⟨5351588, by rfl⟩ : syracuseStep 7135451 = 10703177) B10703177
theorem B942299 : Blo 626299 942299 := bstep (se 1 (by rfl) ⟨706724, by rfl⟩ : syracuseStep 942299 = 1413449) B1413449
theorem B3825883 : Blo 626299 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B942311 : Blo 626299 942311 := bstep (se 1 (by rfl) ⟨706733, by rfl⟩ : syracuseStep 942311 = 1413467) B1413467
theorem B9691469 : Blo 626299 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B2384225 : Blo 626299 2384225 := bstep (se 2 (by rfl) ⟨894084, by rfl⟩ : syracuseStep 2384225 = 1788169) B1788169
theorem B942473 : Blo 626299 942473 := bstep (se 2 (by rfl) ⟨353427, by rfl⟩ : syracuseStep 942473 = 706855) B706855
theorem B942569 : Blo 626299 942569 := bstep (se 2 (by rfl) ⟨353463, by rfl⟩ : syracuseStep 942569 = 706927) B706927
theorem B942695 : Blo 626299 942695 := bstep (se 1 (by rfl) ⟨707021, by rfl⟩ : syracuseStep 942695 = 1414043) B1414043
theorem B2122415 : Blo 626299 2122415 := bstep (se 1 (by rfl) ⟨1591811, by rfl⟩ : syracuseStep 2122415 = 3183623) B3183623
theorem B942827 : Blo 626299 942827 := bstep (se 1 (by rfl) ⟨707120, by rfl⟩ : syracuseStep 942827 = 1414241) B1414241
theorem B2155261 : Blo 626299 2155261 := bstep (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) B808223
theorem B942857 : Blo 626299 942857 := bstep (se 2 (by rfl) ⟨353571, by rfl⟩ : syracuseStep 942857 = 707143) B707143
theorem B942959 : Blo 626299 942959 := bstep (se 1 (by rfl) ⟨707219, by rfl⟩ : syracuseStep 942959 = 1414439) B1414439
theorem B5104549 : Blo 626299 5104549 := bstep (se 4 (by rfl) ⟨478551, by rfl⟩ : syracuseStep 5104549 = 957103) B957103
theorem B2122739 : Blo 626299 2122739 := bstep (se 1 (by rfl) ⟨1592054, by rfl⟩ : syracuseStep 2122739 = 3184109) B3184109
theorem B1074239 : Blo 626299 1074239 := bstep (se 1 (by rfl) ⟨805679, by rfl⟩ : syracuseStep 1074239 = 1611359) B1611359
theorem B1008703 : Blo 626299 1008703 := bstep (se 1 (by rfl) ⟨756527, by rfl⟩ : syracuseStep 1008703 = 1513055) B1513055
theorem B943211 : Blo 626299 943211 := bstep (se 1 (by rfl) ⟨707408, by rfl⟩ : syracuseStep 943211 = 1414817) B1414817
theorem B3433637 : Blo 626299 3433637 := bstep (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) B643807
theorem B943451 : Blo 626299 943451 := bstep (se 1 (by rfl) ⟨707588, by rfl⟩ : syracuseStep 943451 = 1415177) B1415177
theorem B29025803 : Blo 626299 29025803 := bstep (se 1 (by rfl) ⟨21769352, by rfl⟩ : syracuseStep 29025803 = 43538705) B43538705
theorem B2123279 : Blo 626299 2123279 := bstep (se 1 (by rfl) ⟨1592459, by rfl⟩ : syracuseStep 2123279 = 3184919) B3184919
theorem B11495009 : Blo 626299 11495009 := bstep (se 2 (by rfl) ⟨4310628, by rfl⟩ : syracuseStep 11495009 = 8621257) B8621257
theorem B943727 : Blo 626299 943727 := bstep (se 1 (by rfl) ⟨707795, by rfl⟩ : syracuseStep 943727 = 1415591) B1415591
theorem B943799 : Blo 626299 943799 := bstep (se 1 (by rfl) ⟨707849, by rfl⟩ : syracuseStep 943799 = 1415699) B1415699
theorem B943835 : Blo 626299 943835 := bstep (se 1 (by rfl) ⟨707876, by rfl⟩ : syracuseStep 943835 = 1415753) B1415753
theorem B944009 : Blo 626299 944009 := bstep (se 2 (by rfl) ⟨354003, by rfl⟩ : syracuseStep 944009 = 708007) B708007
theorem B944111 : Blo 626299 944111 := bstep (se 1 (by rfl) ⟨708083, by rfl⟩ : syracuseStep 944111 = 1416167) B1416167
theorem B944363 : Blo 626299 944363 := bstep (se 1 (by rfl) ⟨708272, by rfl⟩ : syracuseStep 944363 = 1416545) B1416545
theorem B944423 : Blo 626299 944423 := bstep (se 1 (by rfl) ⟨708317, by rfl⟩ : syracuseStep 944423 = 1416635) B1416635
theorem B2124089 : Blo 626299 2124089 := bstep (se 2 (by rfl) ⟨796533, by rfl⟩ : syracuseStep 2124089 = 1593067) B1593067
theorem B944507 : Blo 626299 944507 := bstep (se 1 (by rfl) ⟨708380, by rfl⟩ : syracuseStep 944507 = 1416761) B1416761
theorem B3172769 : Blo 626299 3172769 := bstep (se 2 (by rfl) ⟨1189788, by rfl⟩ : syracuseStep 3172769 = 2379577) B2379577
theorem B1698209 : Blo 626299 1698209 := bstep (se 2 (by rfl) ⟨636828, by rfl⟩ : syracuseStep 1698209 = 1273657) B1273657
theorem B2124359 : Blo 626299 2124359 := bstep (se 1 (by rfl) ⟨1593269, by rfl⟩ : syracuseStep 2124359 = 3186539) B3186539
theorem B944777 : Blo 626299 944777 := bstep (se 2 (by rfl) ⟨354291, by rfl⟩ : syracuseStep 944777 = 708583) B708583
theorem B944951 : Blo 626299 944951 := bstep (se 1 (by rfl) ⟨708713, by rfl⟩ : syracuseStep 944951 = 1417427) B1417427
theorem B944987 : Blo 626299 944987 := bstep (se 1 (by rfl) ⟨708740, by rfl⟩ : syracuseStep 944987 = 1417481) B1417481
theorem B945131 : Blo 626299 945131 := bstep (se 1 (by rfl) ⟨708848, by rfl⟩ : syracuseStep 945131 = 1417697) B1417697
theorem B8580097 : Blo 626299 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B36137987 : Blo 626299 36137987 := bstep (se 1 (by rfl) ⟨27103490, by rfl⟩ : syracuseStep 36137987 = 54206981) B54206981
theorem B945335 : Blo 626299 945335 := bstep (se 1 (by rfl) ⟨709001, by rfl⟩ : syracuseStep 945335 = 1418003) B1418003
theorem B3173741 : Blo 626299 3173741 := bstep (se 3 (by rfl) ⟨595076, by rfl⟩ : syracuseStep 3173741 = 1190153) B1190153
theorem B2125385 : Blo 626299 2125385 := bstep (se 2 (by rfl) ⟨797019, by rfl⟩ : syracuseStep 2125385 = 1594039) B1594039
theorem B7171901 : Blo 626299 7171901 := bstep (se 3 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 7171901 = 2689463) B2689463
theorem B2944907 : Blo 626299 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B5369975 : Blo 626299 5369975 := bstep (se 1 (by rfl) ⟨4027481, by rfl⟩ : syracuseStep 5369975 = 8054963) B8054963
theorem B6025427 : Blo 626299 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B1339897 : Blo 626299 1339897 := bstep (se 2 (by rfl) ⟨502461, by rfl⟩ : syracuseStep 1339897 = 1004923) B1004923
theorem B3830287 : Blo 626299 3830287 := bstep (se 1 (by rfl) ⟨2872715, by rfl⟩ : syracuseStep 3830287 = 5745431) B5745431
theorem B2683655 : Blo 626299 2683655 := bstep (se 1 (by rfl) ⟨2012741, by rfl⟩ : syracuseStep 2683655 = 4025483) B4025483
theorem B2126843 : Blo 626299 2126843 := bstep (se 1 (by rfl) ⟨1595132, by rfl⟩ : syracuseStep 2126843 = 3190265) B3190265
theorem B2127059 : Blo 626299 2127059 := bstep (se 1 (by rfl) ⟨1595294, by rfl⟩ : syracuseStep 2127059 = 3190589) B3190589
theorem B2290963 : Blo 626299 2290963 := bstep (se 1 (by rfl) ⟨1718222, by rfl⟩ : syracuseStep 2290963 = 3436445) B3436445
theorem B22935001 : Blo 626299 22935001 := bstep (se 2 (by rfl) ⟨8600625, by rfl⟩ : syracuseStep 22935001 = 17201251) B17201251
theorem B7730923 : Blo 626299 7730923 := bstep (se 1 (by rfl) ⟨5798192, by rfl⟩ : syracuseStep 7730923 = 11596385) B11596385
theorem B3176171 : Blo 626299 3176171 := bstep (se 1 (by rfl) ⟨2382128, by rfl⟩ : syracuseStep 3176171 = 4764257) B4764257
theorem B1701863 : Blo 626299 1701863 := bstep (se 1 (by rfl) ⟨1276397, by rfl⟩ : syracuseStep 1701863 = 2552795) B2552795
theorem B8058959 : Blo 626299 8058959 := bstep (se 1 (by rfl) ⟨6044219, by rfl⟩ : syracuseStep 8058959 = 12088439) B12088439
theorem B25720915 : Blo 626299 25720915 := bstep (se 1 (by rfl) ⟨19290686, by rfl⟩ : syracuseStep 25720915 = 38581373) B38581373
theorem B16087571 : Blo 626299 16087571 := bstep (se 1 (by rfl) ⟨12065678, by rfl⟩ : syracuseStep 16087571 = 24131357) B24131357
theorem B4520771 : Blo 626299 4520771 := bstep (se 1 (by rfl) ⟨3390578, by rfl⟩ : syracuseStep 4520771 = 6781157) B6781157
theorem B1506433 : Blo 626299 1506433 := bstep (se 2 (by rfl) ⟨564912, by rfl⟩ : syracuseStep 1506433 = 1129825) B1129825
theorem B2686081 : Blo 626299 2686081 := bstep (se 2 (by rfl) ⟨1007280, by rfl⟩ : syracuseStep 2686081 = 2014561) B2014561
theorem B3177629 : Blo 626299 3177629 := bstep (se 3 (by rfl) ⟨595805, by rfl⟩ : syracuseStep 3177629 = 1191611) B1191611
theorem B5963489 : Blo 626299 5963489 := bstep (se 2 (by rfl) ⟨2236308, by rfl⟩ : syracuseStep 5963489 = 4472617) B4472617
theorem B1507049 : Blo 626299 1507049 := bstep (se 2 (by rfl) ⟨565143, by rfl⟩ : syracuseStep 1507049 = 1130287) B1130287
theorem B5799737 : Blo 626299 5799737 := bstep (se 2 (by rfl) ⟨2174901, by rfl⟩ : syracuseStep 5799737 = 4349803) B4349803
theorem B2392199 : Blo 626299 2392199 := bstep (se 1 (by rfl) ⟨1794149, by rfl⟩ : syracuseStep 2392199 = 3588299) B3588299
theorem B1409273 : Blo 626299 1409273 := bstep (se 2 (by rfl) ⟨528477, by rfl⟩ : syracuseStep 1409273 = 1056955) B1056955
theorem B1409327 : Blo 626299 1409327 := bstep (se 1 (by rfl) ⟨1056995, by rfl⟩ : syracuseStep 1409327 = 2113991) B2113991
theorem B1409543 : Blo 626299 1409543 := bstep (se 1 (by rfl) ⟨1057157, by rfl⟩ : syracuseStep 1409543 = 2114315) B2114315
theorem B3179087 : Blo 626299 3179087 := bstep (se 1 (by rfl) ⟨2384315, by rfl⟩ : syracuseStep 3179087 = 4768631) B4768631
theorem B1409723 : Blo 626299 1409723 := bstep (se 1 (by rfl) ⟨1057292, by rfl⟩ : syracuseStep 1409723 = 2114585) B2114585
theorem B2687755 : Blo 626299 2687755 := bstep (se 1 (by rfl) ⟨2015816, by rfl⟩ : syracuseStep 2687755 = 4031633) B4031633
theorem B1410155 : Blo 626299 1410155 := bstep (se 1 (by rfl) ⟨1057616, by rfl⟩ : syracuseStep 1410155 = 2115233) B2115233
theorem B1344937 : Blo 626299 1344937 := bstep (se 2 (by rfl) ⟨504351, by rfl⟩ : syracuseStep 1344937 = 1008703) B1008703
theorem B1410623 : Blo 626299 1410623 := bstep (se 1 (by rfl) ⟨1057967, by rfl⟩ : syracuseStep 1410623 = 2115935) B2115935
theorem B1410731 : Blo 626299 1410731 := bstep (se 1 (by rfl) ⟨1058048, by rfl⟩ : syracuseStep 1410731 = 2116097) B2116097
theorem B8062649 : Blo 626299 8062649 := bstep (se 2 (by rfl) ⟨3023493, by rfl⟩ : syracuseStep 8062649 = 6046987) B6046987
theorem B2590471 : Blo 626299 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B1411055 : Blo 626299 1411055 := bstep (se 1 (by rfl) ⟨1058291, by rfl⟩ : syracuseStep 1411055 = 2116583) B2116583
theorem B3016865 : Blo 626299 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B1411271 : Blo 626299 1411271 := bstep (se 1 (by rfl) ⟨1058453, by rfl⟩ : syracuseStep 1411271 = 2116907) B2116907
theorem B1411451 : Blo 626299 1411451 := bstep (se 1 (by rfl) ⟨1058588, by rfl⟩ : syracuseStep 1411451 = 2117177) B2117177
theorem B41388565 : Blo 626299 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B1411721 : Blo 626299 1411721 := bstep (se 2 (by rfl) ⟨529395, by rfl⟩ : syracuseStep 1411721 = 1058791) B1058791
theorem B18057923 : Blo 626299 18057923 := bstep (se 1 (by rfl) ⟨13543442, by rfl⟩ : syracuseStep 18057923 = 27086885) B27086885
theorem B1412009 : Blo 626299 1412009 := bstep (se 2 (by rfl) ⟨529503, by rfl⟩ : syracuseStep 1412009 = 1059007) B1059007
theorem B1412711 : Blo 626299 1412711 := bstep (se 1 (by rfl) ⟨1059533, by rfl⟩ : syracuseStep 1412711 = 2119067) B2119067
theorem B626427 : Blo 626299 626427 := bstep (se 1 (by rfl) ⟨469820, by rfl⟩ : syracuseStep 626427 = 939641) B939641
theorem B626495 : Blo 626299 626495 := bstep (se 1 (by rfl) ⟨469871, by rfl⟩ : syracuseStep 626495 = 939743) B939743
theorem B626559 : Blo 626299 626559 := bstep (se 1 (by rfl) ⟨469919, by rfl⟩ : syracuseStep 626559 = 939839) B939839
theorem B34312085 : Blo 626299 34312085 := bstep (se 6 (by rfl) ⟨804189, by rfl⟩ : syracuseStep 34312085 = 1608379) B1608379
theorem B626671 : Blo 626299 626671 := bstep (se 1 (by rfl) ⟨470003, by rfl⟩ : syracuseStep 626671 = 940007) B940007
theorem B626683 : Blo 626299 626683 := bstep (se 1 (by rfl) ⟨470012, by rfl⟩ : syracuseStep 626683 = 940025) B940025
theorem B724987 : Blo 626299 724987 := bstep (se 1 (by rfl) ⟨543740, by rfl⟩ : syracuseStep 724987 = 1087481) B1087481
theorem B11440129 : Blo 626299 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B626751 : Blo 626299 626751 := bstep (se 1 (by rfl) ⟨470063, by rfl⟩ : syracuseStep 626751 = 940127) B940127
theorem B1413215 : Blo 626299 1413215 := bstep (se 1 (by rfl) ⟨1059911, by rfl⟩ : syracuseStep 1413215 = 2119823) B2119823
theorem B626791 : Blo 626299 626791 := bstep (se 1 (by rfl) ⟨470093, by rfl⟩ : syracuseStep 626791 = 940187) B940187
theorem B626815 : Blo 626299 626815 := bstep (se 1 (by rfl) ⟨470111, by rfl⟩ : syracuseStep 626815 = 940223) B940223
theorem B626843 : Blo 626299 626843 := bstep (se 1 (by rfl) ⟨470132, by rfl⟩ : syracuseStep 626843 = 940265) B940265
theorem B627047 : Blo 626299 627047 := bstep (se 1 (by rfl) ⟨470285, by rfl⟩ : syracuseStep 627047 = 940571) B940571
theorem B627099 : Blo 626299 627099 := bstep (se 1 (by rfl) ⟨470324, by rfl⟩ : syracuseStep 627099 = 940649) B940649
theorem B627451 : Blo 626299 627451 := bstep (se 1 (by rfl) ⟨470588, by rfl⟩ : syracuseStep 627451 = 941177) B941177
theorem B627519 : Blo 626299 627519 := bstep (se 1 (by rfl) ⟨470639, by rfl⟩ : syracuseStep 627519 = 941279) B941279
theorem B1413971 : Blo 626299 1413971 := bstep (se 1 (by rfl) ⟨1060478, by rfl⟩ : syracuseStep 1413971 = 2120957) B2120957
theorem B627547 : Blo 626299 627547 := bstep (se 1 (by rfl) ⟨470660, by rfl⟩ : syracuseStep 627547 = 941321) B941321
theorem B627615 : Blo 626299 627615 := bstep (se 1 (by rfl) ⟨470711, by rfl⟩ : syracuseStep 627615 = 941423) B941423
theorem B627695 : Blo 626299 627695 := bstep (se 1 (by rfl) ⟨470771, by rfl⟩ : syracuseStep 627695 = 941543) B941543
theorem B627783 : Blo 626299 627783 := bstep (se 1 (by rfl) ⟨470837, by rfl⟩ : syracuseStep 627783 = 941675) B941675
theorem B627867 : Blo 626299 627867 := bstep (se 1 (by rfl) ⟨470900, by rfl⟩ : syracuseStep 627867 = 941801) B941801
theorem B955547 : Blo 626299 955547 := bstep (se 1 (by rfl) ⟨716660, by rfl⟩ : syracuseStep 955547 = 1433321) B1433321
theorem B627963 : Blo 626299 627963 := bstep (se 1 (by rfl) ⟨470972, by rfl⟩ : syracuseStep 627963 = 941945) B941945
theorem B628031 : Blo 626299 628031 := bstep (se 1 (by rfl) ⟨471023, by rfl⟩ : syracuseStep 628031 = 942047) B942047
theorem B1414511 : Blo 626299 1414511 := bstep (se 1 (by rfl) ⟨1060883, by rfl⟩ : syracuseStep 1414511 = 2121767) B2121767
theorem B4756967 : Blo 626299 4756967 := bstep (se 1 (by rfl) ⟨3567725, by rfl⟩ : syracuseStep 4756967 = 7135451) B7135451
theorem B628199 : Blo 626299 628199 := bstep (se 1 (by rfl) ⟨471149, by rfl⟩ : syracuseStep 628199 = 942299) B942299
theorem B628207 : Blo 626299 628207 := bstep (se 1 (by rfl) ⟨471155, by rfl⟩ : syracuseStep 628207 = 942311) B942311
theorem B6460979 : Blo 626299 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B628315 : Blo 626299 628315 := bstep (se 1 (by rfl) ⟨471236, by rfl⟩ : syracuseStep 628315 = 942473) B942473
theorem B628379 : Blo 626299 628379 := bstep (se 1 (by rfl) ⟨471284, by rfl⟩ : syracuseStep 628379 = 942569) B942569
theorem B628463 : Blo 626299 628463 := bstep (se 1 (by rfl) ⟨471347, by rfl⟩ : syracuseStep 628463 = 942695) B942695
theorem B1414943 : Blo 626299 1414943 := bstep (se 1 (by rfl) ⟨1061207, by rfl⟩ : syracuseStep 1414943 = 2122415) B2122415
theorem B628551 : Blo 626299 628551 := bstep (se 1 (by rfl) ⟨471413, by rfl⟩ : syracuseStep 628551 = 942827) B942827
theorem B628571 : Blo 626299 628571 := bstep (se 1 (by rfl) ⟨471428, by rfl⟩ : syracuseStep 628571 = 942857) B942857
theorem B628639 : Blo 626299 628639 := bstep (se 1 (by rfl) ⟨471479, by rfl⟩ : syracuseStep 628639 = 942959) B942959
theorem B1415159 : Blo 626299 1415159 := bstep (se 1 (by rfl) ⟨1061369, by rfl⟩ : syracuseStep 1415159 = 2122739) B2122739
theorem B628807 : Blo 626299 628807 := bstep (se 1 (by rfl) ⟨471605, by rfl⟩ : syracuseStep 628807 = 943211) B943211
theorem B628967 : Blo 626299 628967 := bstep (se 1 (by rfl) ⟨471725, by rfl⟩ : syracuseStep 628967 = 943451) B943451
theorem B1415519 : Blo 626299 1415519 := bstep (se 1 (by rfl) ⟨1061639, by rfl⟩ : syracuseStep 1415519 = 2123279) B2123279
theorem B629151 : Blo 626299 629151 := bstep (se 1 (by rfl) ⟨471863, by rfl⟩ : syracuseStep 629151 = 943727) B943727
theorem B629199 : Blo 626299 629199 := bstep (se 1 (by rfl) ⟨471899, by rfl⟩ : syracuseStep 629199 = 943799) B943799
theorem B629223 : Blo 626299 629223 := bstep (se 1 (by rfl) ⟨471917, by rfl⟩ : syracuseStep 629223 = 943835) B943835
theorem B629339 : Blo 626299 629339 := bstep (se 1 (by rfl) ⟨472004, by rfl⟩ : syracuseStep 629339 = 944009) B944009
theorem B629407 : Blo 626299 629407 := bstep (se 1 (by rfl) ⟨472055, by rfl⟩ : syracuseStep 629407 = 944111) B944111
theorem B793415 : Blo 626299 793415 := bstep (se 1 (by rfl) ⟨595061, by rfl⟩ : syracuseStep 793415 = 1190123) B1190123
theorem B629575 : Blo 626299 629575 := bstep (se 1 (by rfl) ⟨472181, by rfl⟩ : syracuseStep 629575 = 944363) B944363
theorem B629615 : Blo 626299 629615 := bstep (se 1 (by rfl) ⟨472211, by rfl⟩ : syracuseStep 629615 = 944423) B944423
theorem B1416059 : Blo 626299 1416059 := bstep (se 1 (by rfl) ⟨1062044, by rfl⟩ : syracuseStep 1416059 = 2124089) B2124089
theorem B629671 : Blo 626299 629671 := bstep (se 1 (by rfl) ⟨472253, by rfl⟩ : syracuseStep 629671 = 944507) B944507
theorem B3054617 : Blo 626299 3054617 := bstep (se 2 (by rfl) ⟨1145481, by rfl⟩ : syracuseStep 3054617 = 2290963) B2290963
theorem B1907759 : Blo 626299 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B1416239 : Blo 626299 1416239 := bstep (se 1 (by rfl) ⟨1062179, by rfl⟩ : syracuseStep 1416239 = 2124359) B2124359
theorem B629851 : Blo 626299 629851 := bstep (se 1 (by rfl) ⟨472388, by rfl⟩ : syracuseStep 629851 = 944777) B944777
theorem B629967 : Blo 626299 629967 := bstep (se 1 (by rfl) ⟨472475, by rfl⟩ : syracuseStep 629967 = 944951) B944951
theorem B629991 : Blo 626299 629991 := bstep (se 1 (by rfl) ⟨472493, by rfl⟩ : syracuseStep 629991 = 944987) B944987
theorem B30580001 : Blo 626299 30580001 := bstep (se 2 (by rfl) ⟨11467500, by rfl⟩ : syracuseStep 30580001 = 22935001) B22935001
theorem B630087 : Blo 626299 630087 := bstep (se 1 (by rfl) ⟨472565, by rfl⟩ : syracuseStep 630087 = 945131) B945131
theorem B24091991 : Blo 626299 24091991 := bstep (se 1 (by rfl) ⟨18068993, by rfl⟩ : syracuseStep 24091991 = 36137987) B36137987
theorem B630223 : Blo 626299 630223 := bstep (se 1 (by rfl) ⟨472667, by rfl⟩ : syracuseStep 630223 = 945335) B945335
theorem B3022343 : Blo 626299 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B10755665 : Blo 626299 10755665 := bstep (se 2 (by rfl) ⟨4033374, by rfl⟩ : syracuseStep 10755665 = 8066749) B8066749
theorem B3022555 : Blo 626299 3022555 := bstep (se 1 (by rfl) ⟨2266916, by rfl⟩ : syracuseStep 3022555 = 4533833) B4533833
theorem B1416923 : Blo 626299 1416923 := bstep (se 1 (by rfl) ⟨1062692, by rfl⟩ : syracuseStep 1416923 = 2125385) B2125385
theorem B1417193 : Blo 626299 1417193 := bstep (se 2 (by rfl) ⟨531447, by rfl⟩ : syracuseStep 1417193 = 1062895) B1062895
theorem B3579983 : Blo 626299 3579983 := bstep (se 1 (by rfl) ⟨2684987, by rfl⟩ : syracuseStep 3579983 = 5369975) B5369975
theorem B10887605 : Blo 626299 10887605 := bstep (se 5 (by rfl) ⟨510356, by rfl⟩ : syracuseStep 10887605 = 1020713) B1020713
theorem B11477497 : Blo 626299 11477497 := bstep (se 2 (by rfl) ⟨4304061, by rfl⟩ : syracuseStep 11477497 = 8608123) B8608123
theorem B1417895 : Blo 626299 1417895 := bstep (se 1 (by rfl) ⟨1063421, by rfl⟩ : syracuseStep 1417895 = 2126843) B2126843
theorem B4530977 : Blo 626299 4530977 := bstep (se 2 (by rfl) ⟨1699116, by rfl⟩ : syracuseStep 4530977 = 3398233) B3398233
theorem B1418039 : Blo 626299 1418039 := bstep (se 1 (by rfl) ⟨1063529, by rfl⟩ : syracuseStep 1418039 = 2127059) B2127059
theorem B894073 : Blo 626299 894073 := bstep (se 2 (by rfl) ⟨335277, by rfl⟩ : syracuseStep 894073 = 670555) B670555
theorem B2008577 : Blo 626299 2008577 := bstep (se 2 (by rfl) ⟨753216, by rfl⟩ : syracuseStep 2008577 = 1506433) B1506433
theorem B3581441 : Blo 626299 3581441 := bstep (se 2 (by rfl) ⟨1343040, by rfl⟩ : syracuseStep 3581441 = 2686081) B2686081
theorem B5383847 : Blo 626299 5383847 := bstep (se 1 (by rfl) ⟨4037885, by rfl⟩ : syracuseStep 5383847 = 8075771) B8075771
theorem B10725047 : Blo 626299 10725047 := bstep (se 1 (by rfl) ⟨8043785, by rfl⟩ : syracuseStep 10725047 = 16087571) B16087571
theorem B3024955 : Blo 626299 3024955 := bstep (se 1 (by rfl) ⟨2268716, by rfl⟩ : syracuseStep 3024955 = 4537433) B4537433
theorem B3975659 : Blo 626299 3975659 := bstep (se 1 (by rfl) ⟨2981744, by rfl⟩ : syracuseStep 3975659 = 5963489) B5963489
theorem B1191095 : Blo 626299 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B1191323 : Blo 626299 1191323 := bstep (se 1 (by rfl) ⟨893492, by rfl⟩ : syracuseStep 1191323 = 1786985) B1786985
theorem B4599935 : Blo 626299 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B3027071 : Blo 626299 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B897257 : Blo 626299 897257 := bstep (se 2 (by rfl) ⟨336471, by rfl⟩ : syracuseStep 897257 = 672943) B672943
theorem B1192295 : Blo 626299 1192295 := bstep (se 1 (by rfl) ⟨894221, by rfl⟩ : syracuseStep 1192295 = 1788443) B1788443
theorem B1061275 : Blo 626299 1061275 := bstep (se 1 (by rfl) ⟨795956, by rfl⟩ : syracuseStep 1061275 = 1591913) B1591913
theorem B38679403 : Blo 626299 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B635887 : Blo 626299 635887 := bstep (se 1 (by rfl) ⟨476915, by rfl⟩ : syracuseStep 635887 = 953831) B953831
theorem B1062139 : Blo 626299 1062139 := bstep (se 1 (by rfl) ⟨796604, by rfl⟩ : syracuseStep 1062139 = 1593209) B1593209
theorem B1586911 : Blo 626299 1586911 := bstep (se 1 (by rfl) ⟨1190183, by rfl⟩ : syracuseStep 1586911 = 2380367) B2380367
theorem B1062983 : Blo 626299 1062983 := bstep (se 1 (by rfl) ⟨797237, by rfl⟩ : syracuseStep 1062983 = 1594475) B1594475
theorem B1194527 : Blo 626299 1194527 := bstep (se 1 (by rfl) ⟨895895, by rfl⟩ : syracuseStep 1194527 = 1791791) B1791791
theorem B670367 : Blo 626299 670367 := bstep (se 1 (by rfl) ⟨502775, by rfl⟩ : syracuseStep 670367 = 1005551) B1005551
theorem B2014433 : Blo 626299 2014433 := bstep (se 2 (by rfl) ⟨755412, by rfl⟩ : syracuseStep 2014433 = 1510825) B1510825
theorem B1589159 : Blo 626299 1589159 := bstep (se 1 (by rfl) ⟨1191869, by rfl⟩ : syracuseStep 1589159 = 2383739) B2383739
theorem B1589483 : Blo 626299 1589483 := bstep (se 1 (by rfl) ⟨1192112, by rfl⟩ : syracuseStep 1589483 = 2384225) B2384225
theorem B704767 : Blo 626299 704767 := bstep (se 1 (by rfl) ⟨528575, by rfl⟩ : syracuseStep 704767 = 1057151) B1057151
theorem B2114045 : Blo 626299 2114045 := bstep (se 3 (by rfl) ⟨396383, by rfl⟩ : syracuseStep 2114045 = 792767) B792767
theorem B705055 : Blo 626299 705055 := bstep (se 1 (by rfl) ⟨528791, by rfl⟩ : syracuseStep 705055 = 1057583) B1057583
theorem B1786529 : Blo 626299 1786529 := bstep (se 2 (by rfl) ⟨669948, by rfl⟩ : syracuseStep 1786529 = 1339897) B1339897
theorem B19350535 : Blo 626299 19350535 := bstep (se 1 (by rfl) ⟨14512901, by rfl⟩ : syracuseStep 19350535 = 29025803) B29025803
theorem B705703 : Blo 626299 705703 := bstep (se 1 (by rfl) ⟨529277, by rfl⟩ : syracuseStep 705703 = 1058555) B1058555
theorem B2115179 : Blo 626299 2115179 := bstep (se 1 (by rfl) ⟨1586384, by rfl⟩ : syracuseStep 2115179 = 3172769) B3172769
theorem B1132139 : Blo 626299 1132139 := bstep (se 1 (by rfl) ⟨849104, by rfl⟩ : syracuseStep 1132139 = 1698209) B1698209
theorem B2148011 : Blo 626299 2148011 := bstep (se 1 (by rfl) ⟨1611008, by rfl⟩ : syracuseStep 2148011 = 3222017) B3222017
theorem B2115449 : Blo 626299 2115449 := bstep (se 2 (by rfl) ⟨793293, by rfl⟩ : syracuseStep 2115449 = 1586587) B1586587
theorem B706495 : Blo 626299 706495 := bstep (se 1 (by rfl) ⟨529871, by rfl⟩ : syracuseStep 706495 = 1059743) B1059743
theorem B706783 : Blo 626299 706783 := bstep (se 1 (by rfl) ⟨530087, by rfl⟩ : syracuseStep 706783 = 1060175) B1060175
theorem B2115827 : Blo 626299 2115827 := bstep (se 1 (by rfl) ⟨1586870, by rfl⟩ : syracuseStep 2115827 = 3173741) B3173741
theorem B10307897 : Blo 626299 10307897 := bstep (se 2 (by rfl) ⟨3865461, by rfl⟩ : syracuseStep 10307897 = 7730923) B7730923
theorem B1591721 : Blo 626299 1591721 := bstep (se 2 (by rfl) ⟨596895, by rfl⟩ : syracuseStep 1591721 = 1193791) B1193791
theorem B5360201 : Blo 626299 5360201 := bstep (se 2 (by rfl) ⟨2010075, by rfl⟩ : syracuseStep 5360201 = 4020151) B4020151
theorem B34294553 : Blo 626299 34294553 := bstep (se 2 (by rfl) ⟨12860457, by rfl⟩ : syracuseStep 34294553 = 25720915) B25720915
theorem B4016951 : Blo 626299 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B707647 : Blo 626299 707647 := bstep (se 1 (by rfl) ⟨530735, by rfl⟩ : syracuseStep 707647 = 1061471) B1061471
theorem B1789103 : Blo 626299 1789103 := bstep (se 1 (by rfl) ⟨1341827, by rfl⟩ : syracuseStep 1789103 = 2683655) B2683655
theorem B39308971 : Blo 626299 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B2019097 : Blo 626299 2019097 := bstep (se 2 (by rfl) ⟨757161, by rfl⟩ : syracuseStep 2019097 = 1514323) B1514323
theorem B2117447 : Blo 626299 2117447 := bstep (se 1 (by rfl) ⟨1588085, by rfl⟩ : syracuseStep 2117447 = 3176171) B3176171
theorem B1134575 : Blo 626299 1134575 := bstep (se 1 (by rfl) ⟨850931, by rfl⟩ : syracuseStep 1134575 = 1701863) B1701863
theorem B708763 : Blo 626299 708763 := bstep (se 1 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 708763 = 1063145) B1063145
theorem B4772033 : Blo 626299 4772033 := bstep (se 2 (by rfl) ⟨1789512, by rfl⟩ : syracuseStep 4772033 = 3579025) B3579025
theorem B2118419 : Blo 626299 2118419 := bstep (se 1 (by rfl) ⟨1588814, by rfl⟩ : syracuseStep 2118419 = 3177629) B3177629
theorem B2675693 : Blo 626299 2675693 := bstep (se 3 (by rfl) ⟨501692, by rfl⟩ : syracuseStep 2675693 = 1003385) B1003385
theorem B1004699 : Blo 626299 1004699 := bstep (se 1 (by rfl) ⟨753524, by rfl⟩ : syracuseStep 1004699 = 1507049) B1507049
theorem B939503 : Blo 626299 939503 := bstep (se 1 (by rfl) ⟨704627, by rfl⟩ : syracuseStep 939503 = 1409255) B1409255
theorem B939899 : Blo 626299 939899 := bstep (se 1 (by rfl) ⟨704924, by rfl⟩ : syracuseStep 939899 = 1409849) B1409849
theorem B939935 : Blo 626299 939935 := bstep (se 1 (by rfl) ⟨704951, by rfl⟩ : syracuseStep 939935 = 1409903) B1409903
theorem B940169 : Blo 626299 940169 := bstep (se 2 (by rfl) ⟨352563, by rfl⟩ : syracuseStep 940169 = 705127) B705127
theorem B940319 : Blo 626299 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B2873681 : Blo 626299 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B20404709 : Blo 626299 20404709 := bstep (se 4 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 20404709 = 3825883) B3825883
theorem B6806065 : Blo 626299 6806065 := bstep (se 2 (by rfl) ⟨2552274, by rfl⟩ : syracuseStep 6806065 = 5104549) B5104549
theorem B940871 : Blo 626299 940871 := bstep (se 1 (by rfl) ⟨705653, by rfl⟩ : syracuseStep 940871 = 1411307) B1411307
theorem B2546921 : Blo 626299 2546921 := bstep (se 2 (by rfl) ⟨955095, by rfl⟩ : syracuseStep 2546921 = 1910191) B1910191
theorem B2383451 : Blo 626299 2383451 := bstep (se 1 (by rfl) ⟨1787588, by rfl⟩ : syracuseStep 2383451 = 3575177) B3575177
theorem B941735 : Blo 626299 941735 := bstep (se 1 (by rfl) ⟨706301, by rfl⟩ : syracuseStep 941735 = 1412603) B1412603
theorem B941855 : Blo 626299 941855 := bstep (se 1 (by rfl) ⟨706391, by rfl⟩ : syracuseStep 941855 = 1412783) B1412783
theorem B2416787 : Blo 626299 2416787 := bstep (se 1 (by rfl) ⟨1812590, by rfl⟩ : syracuseStep 2416787 = 3625181) B3625181
theorem B2121875 : Blo 626299 2121875 := bstep (se 1 (by rfl) ⟨1591406, by rfl⟩ : syracuseStep 2121875 = 3182813) B3182813
theorem B942287 : Blo 626299 942287 := bstep (se 1 (by rfl) ⟨706715, by rfl⟩ : syracuseStep 942287 = 1413431) B1413431
theorem B942335 : Blo 626299 942335 := bstep (se 1 (by rfl) ⟨706751, by rfl⟩ : syracuseStep 942335 = 1413503) B1413503
theorem B2121983 : Blo 626299 2121983 := bstep (se 1 (by rfl) ⟨1591487, by rfl⟩ : syracuseStep 2121983 = 3182975) B3182975
theorem B1433951 : Blo 626299 1433951 := bstep (se 1 (by rfl) ⟨1075463, by rfl⟩ : syracuseStep 1433951 = 2150927) B2150927
theorem B2122145 : Blo 626299 2122145 := bstep (se 2 (by rfl) ⟨795804, by rfl⟩ : syracuseStep 2122145 = 1591609) B1591609
theorem B943151 : Blo 626299 943151 := bstep (se 1 (by rfl) ⟨707363, by rfl⟩ : syracuseStep 943151 = 1414727) B1414727
theorem B943271 : Blo 626299 943271 := bstep (se 1 (by rfl) ⟨707453, by rfl⟩ : syracuseStep 943271 = 1414907) B1414907
theorem B943643 : Blo 626299 943643 := bstep (se 1 (by rfl) ⟨707732, by rfl⟩ : syracuseStep 943643 = 1415465) B1415465
theorem B2385683 : Blo 626299 2385683 := bstep (se 1 (by rfl) ⟨1789262, by rfl⟩ : syracuseStep 2385683 = 3578525) B3578525
theorem B2680715 : Blo 626299 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B944027 : Blo 626299 944027 := bstep (se 1 (by rfl) ⟨708020, by rfl⟩ : syracuseStep 944027 = 1416041) B1416041
theorem B7628701 : Blo 626299 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B2123711 : Blo 626299 2123711 := bstep (se 1 (by rfl) ⟨1592783, by rfl⟩ : syracuseStep 2123711 = 3185567) B3185567
theorem B944063 : Blo 626299 944063 := bstep (se 1 (by rfl) ⟨708047, by rfl⟩ : syracuseStep 944063 = 1416095) B1416095
theorem B2123873 : Blo 626299 2123873 := bstep (se 2 (by rfl) ⟨796452, by rfl⟩ : syracuseStep 2123873 = 1592905) B1592905
theorem B944249 : Blo 626299 944249 := bstep (se 2 (by rfl) ⟨354093, by rfl⟩ : syracuseStep 944249 = 708187) B708187
theorem B5433479 : Blo 626299 5433479 := bstep (se 1 (by rfl) ⟨4075109, by rfl⟩ : syracuseStep 5433479 = 8150219) B8150219
theorem B7661783 : Blo 626299 7661783 := bstep (se 1 (by rfl) ⟨5746337, by rfl⟩ : syracuseStep 7661783 = 11492675) B11492675
theorem B944633 : Blo 626299 944633 := bstep (se 2 (by rfl) ⟨354237, by rfl⟩ : syracuseStep 944633 = 708475) B708475
theorem B944687 : Blo 626299 944687 := bstep (se 1 (by rfl) ⟨708515, by rfl⟩ : syracuseStep 944687 = 1417031) B1417031
theorem B2124413 : Blo 626299 2124413 := bstep (se 3 (by rfl) ⟨398327, by rfl⟩ : syracuseStep 2124413 = 796655) B796655
theorem B2124683 : Blo 626299 2124683 := bstep (se 1 (by rfl) ⟨1593512, by rfl⟩ : syracuseStep 2124683 = 3187025) B3187025
theorem B945119 : Blo 626299 945119 := bstep (se 1 (by rfl) ⟨708839, by rfl⟩ : syracuseStep 945119 = 1417679) B1417679
theorem B5107049 : Blo 626299 5107049 := bstep (se 2 (by rfl) ⟨1915143, by rfl⟩ : syracuseStep 5107049 = 3830287) B3830287
theorem B716159 : Blo 626299 716159 := bstep (se 1 (by rfl) ⟨537119, by rfl⟩ : syracuseStep 716159 = 1074239) B1074239
theorem B11431313 : Blo 626299 11431313 := bstep (se 2 (by rfl) ⟨4286742, by rfl⟩ : syracuseStep 11431313 = 8573485) B8573485
theorem B2125223 : Blo 626299 2125223 := bstep (se 1 (by rfl) ⟨1593917, by rfl⟩ : syracuseStep 2125223 = 3187835) B3187835
theorem B2289091 : Blo 626299 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B5729773 : Blo 626299 5729773 := bstep (se 3 (by rfl) ⟨1074332, by rfl⟩ : syracuseStep 5729773 = 2148665) B2148665
theorem B7663339 : Blo 626299 7663339 := bstep (se 1 (by rfl) ⟨5747504, by rfl⟩ : syracuseStep 7663339 = 11495009) B11495009
theorem B4026199 : Blo 626299 4026199 := bstep (se 1 (by rfl) ⟨3019649, by rfl⟩ : syracuseStep 4026199 = 6039299) B6039299
theorem B2125655 : Blo 626299 2125655 := bstep (se 1 (by rfl) ⟨1594241, by rfl⟩ : syracuseStep 2125655 = 3188483) B3188483
theorem B2420729 : Blo 626299 2420729 := bstep (se 2 (by rfl) ⟨907773, by rfl⟩ : syracuseStep 2420729 = 1815547) B1815547
theorem B2125817 : Blo 626299 2125817 := bstep (se 2 (by rfl) ⟨797181, by rfl⟩ : syracuseStep 2125817 = 1594363) B1594363
theorem B3567635 : Blo 626299 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B2126087 : Blo 626299 2126087 := bstep (se 1 (by rfl) ⟨1594565, by rfl⟩ : syracuseStep 2126087 = 3189131) B3189131
theorem B2126465 : Blo 626299 2126465 := bstep (se 2 (by rfl) ⟨797424, by rfl⟩ : syracuseStep 2126465 = 1594849) B1594849
theorem B2388797 : Blo 626299 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B1274687 : Blo 626299 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B2126735 : Blo 626299 2126735 := bstep (se 1 (by rfl) ⟨1595051, by rfl⟩ : syracuseStep 2126735 = 3190103) B3190103
theorem B4781267 : Blo 626299 4781267 := bstep (se 1 (by rfl) ⟨3585950, by rfl⟩ : syracuseStep 4781267 = 7171901) B7171901
theorem B1963271 : Blo 626299 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B2127167 : Blo 626299 2127167 := bstep (se 1 (by rfl) ⟨1595375, by rfl⟩ : syracuseStep 2127167 = 3190751) B3190751
theorem B9663943 : Blo 626299 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B20117393 : Blo 626299 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B2258887 : Blo 626299 2258887 := bstep (se 1 (by rfl) ⟨1694165, by rfl⟩ : syracuseStep 2258887 = 3388331) B3388331
theorem B2685089 : Blo 626299 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B1341623 : Blo 626299 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B3176657 : Blo 626299 3176657 := bstep (se 2 (by rfl) ⟨1191246, by rfl⟩ : syracuseStep 3176657 = 2382493) B2382493
theorem B3570095 : Blo 626299 3570095 := bstep (se 1 (by rfl) ⟨2677571, by rfl⟩ : syracuseStep 3570095 = 5355143) B5355143
theorem B2292353 : Blo 626299 2292353 := bstep (se 2 (by rfl) ⟨859632, by rfl⟩ : syracuseStep 2292353 = 1719265) B1719265
theorem B5372639 : Blo 626299 5372639 := bstep (se 1 (by rfl) ⟨4029479, by rfl⟩ : syracuseStep 5372639 = 8058959) B8058959
theorem B10746917 : Blo 626299 10746917 := bstep (se 4 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 10746917 = 2015047) B2015047
theorem B3013847 : Blo 626299 3013847 := bstep (se 1 (by rfl) ⟨2260385, by rfl⟩ : syracuseStep 3013847 = 4520771) B4520771
theorem B1277435 : Blo 626299 1277435 := bstep (se 1 (by rfl) ⟨958076, by rfl⟩ : syracuseStep 1277435 = 1916153) B1916153
theorem B2391727 : Blo 626299 2391727 := bstep (se 1 (by rfl) ⟨1793795, by rfl⟩ : syracuseStep 2391727 = 3587591) B3587591
theorem B2981713 : Blo 626299 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B3866491 : Blo 626299 3866491 := bstep (se 1 (by rfl) ⟨2899868, by rfl⟩ : syracuseStep 3866491 = 5799737) B5799737
theorem B3178439 : Blo 626299 3178439 := bstep (se 1 (by rfl) ⟨2383829, by rfl⟩ : syracuseStep 3178439 = 4767659) B4767659
theorem B1409363 : Blo 626299 1409363 := bstep (se 1 (by rfl) ⟨1057022, by rfl⟩ : syracuseStep 1409363 = 2114045) B2114045
theorem B2392685 : Blo 626299 2392685 := bstep (se 3 (by rfl) ⟨448628, by rfl⟩ : syracuseStep 2392685 = 897257) B897257
theorem B15303329 : Blo 626299 15303329 := bstep (se 2 (by rfl) ⟨5738748, by rfl⟩ : syracuseStep 15303329 = 11477497) B11477497
theorem B1410119 : Blo 626299 1410119 := bstep (se 1 (by rfl) ⟨1057589, by rfl⟩ : syracuseStep 1410119 = 2115179) B2115179
theorem B754759 : Blo 626299 754759 := bstep (se 1 (by rfl) ⟨566069, by rfl⟩ : syracuseStep 754759 = 1132139) B1132139
theorem B5375099 : Blo 626299 5375099 := bstep (se 1 (by rfl) ⟨4031324, by rfl⟩ : syracuseStep 5375099 = 8062649) B8062649
theorem B1410299 : Blo 626299 1410299 := bstep (se 1 (by rfl) ⟨1057724, by rfl⟩ : syracuseStep 1410299 = 2115449) B2115449
theorem B1410551 : Blo 626299 1410551 := bstep (se 1 (by rfl) ⟨1057913, by rfl⟩ : syracuseStep 1410551 = 2115827) B2115827
theorem B3573467 : Blo 626299 3573467 := bstep (se 1 (by rfl) ⟨2680100, by rfl⟩ : syracuseStep 3573467 = 5360201) B5360201
theorem B1411631 : Blo 626299 1411631 := bstep (se 1 (by rfl) ⟨1058723, by rfl⟩ : syracuseStep 1411631 = 2117447) B2117447
theorem B22874723 : Blo 626299 22874723 := bstep (se 1 (by rfl) ⟨17156042, by rfl⟩ : syracuseStep 22874723 = 34312085) B34312085
theorem B756383 : Blo 626299 756383 := bstep (se 1 (by rfl) ⟨567287, by rfl⟩ : syracuseStep 756383 = 1134575) B1134575
theorem B4033273 : Blo 626299 4033273 := bstep (se 2 (by rfl) ⟨1512477, by rfl⟩ : syracuseStep 4033273 = 3024955) B3024955
theorem B3181355 : Blo 626299 3181355 := bstep (se 1 (by rfl) ⟨2386016, by rfl⟩ : syracuseStep 3181355 = 4772033) B4772033
theorem B1412279 : Blo 626299 1412279 := bstep (se 1 (by rfl) ⟨1059209, by rfl⟩ : syracuseStep 1412279 = 2118419) B2118419
theorem B55184753 : Blo 626299 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B626335 : Blo 626299 626335 := bstep (se 1 (by rfl) ⟨469751, by rfl⟩ : syracuseStep 626335 = 939503) B939503
theorem B626599 : Blo 626299 626599 := bstep (se 1 (by rfl) ⟨469949, by rfl⟩ : syracuseStep 626599 = 939899) B939899
theorem B626623 : Blo 626299 626623 := bstep (se 1 (by rfl) ⟨469967, by rfl⟩ : syracuseStep 626623 = 939935) B939935
theorem B626779 : Blo 626299 626779 := bstep (se 1 (by rfl) ⟨470084, by rfl⟩ : syracuseStep 626779 = 940169) B940169
theorem B626879 : Blo 626299 626879 := bstep (se 1 (by rfl) ⟨470159, by rfl⟩ : syracuseStep 626879 = 940319) B940319
theorem B13603139 : Blo 626299 13603139 := bstep (se 1 (by rfl) ⟨10202354, by rfl⟩ : syracuseStep 13603139 = 20404709) B20404709
theorem B627247 : Blo 626299 627247 := bstep (se 1 (by rfl) ⟨470435, by rfl⟩ : syracuseStep 627247 = 940871) B940871
theorem B3052121 : Blo 626299 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B7639697 : Blo 626299 7639697 := bstep (se 2 (by rfl) ⟨2864886, by rfl⟩ : syracuseStep 7639697 = 5729773) B5729773
theorem B2036411 : Blo 626299 2036411 := bstep (se 1 (by rfl) ⟨1527308, by rfl⟩ : syracuseStep 2036411 = 3054617) B3054617
theorem B20386667 : Blo 626299 20386667 := bstep (se 1 (by rfl) ⟨15290000, by rfl⟩ : syracuseStep 20386667 = 30580001) B30580001
theorem B16061327 : Blo 626299 16061327 := bstep (se 1 (by rfl) ⟨12045995, by rfl⟩ : syracuseStep 16061327 = 24091991) B24091991
theorem B7148573 : Blo 626299 7148573 := bstep (se 3 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 7148573 = 2680715) B2680715
theorem B2692129 : Blo 626299 2692129 := bstep (se 2 (by rfl) ⟨1009548, by rfl⟩ : syracuseStep 2692129 = 2019097) B2019097
theorem B627823 : Blo 626299 627823 := bstep (se 1 (by rfl) ⟨470867, by rfl⟩ : syracuseStep 627823 = 941735) B941735
theorem B627903 : Blo 626299 627903 := bstep (se 1 (by rfl) ⟨470927, by rfl⟩ : syracuseStep 627903 = 941855) B941855
theorem B1611191 : Blo 626299 1611191 := bstep (se 1 (by rfl) ⟨1208393, by rfl⟩ : syracuseStep 1611191 = 2416787) B2416787
theorem B1414583 : Blo 626299 1414583 := bstep (se 1 (by rfl) ⟨1060937, by rfl⟩ : syracuseStep 1414583 = 2121875) B2121875
theorem B628191 : Blo 626299 628191 := bstep (se 1 (by rfl) ⟨471143, by rfl⟩ : syracuseStep 628191 = 942287) B942287
theorem B628223 : Blo 626299 628223 := bstep (se 1 (by rfl) ⟨471167, by rfl⟩ : syracuseStep 628223 = 942335) B942335
theorem B1414655 : Blo 626299 1414655 := bstep (se 1 (by rfl) ⟨1060991, by rfl⟩ : syracuseStep 1414655 = 2121983) B2121983
theorem B955967 : Blo 626299 955967 := bstep (se 1 (by rfl) ⟨716975, by rfl⟩ : syracuseStep 955967 = 1433951) B1433951
theorem B1414763 : Blo 626299 1414763 := bstep (se 1 (by rfl) ⟨1061072, by rfl⟩ : syracuseStep 1414763 = 2122145) B2122145
theorem B3020651 : Blo 626299 3020651 := bstep (se 1 (by rfl) ⟨2265488, by rfl⟩ : syracuseStep 3020651 = 4530977) B4530977
theorem B1415033 : Blo 626299 1415033 := bstep (se 2 (by rfl) ⟨530637, by rfl⟩ : syracuseStep 1415033 = 1061275) B1061275
theorem B628767 : Blo 626299 628767 := bstep (se 1 (by rfl) ⟨471575, by rfl⟩ : syracuseStep 628767 = 943151) B943151
theorem B628847 : Blo 626299 628847 := bstep (se 1 (by rfl) ⟨471635, by rfl⟩ : syracuseStep 628847 = 943271) B943271
theorem B629095 : Blo 626299 629095 := bstep (se 1 (by rfl) ⟨471821, by rfl⟩ : syracuseStep 629095 = 943643) B943643
theorem B7150031 : Blo 626299 7150031 := bstep (se 1 (by rfl) ⟨5362523, by rfl⟩ : syracuseStep 7150031 = 10725047) B10725047
theorem B629351 : Blo 626299 629351 := bstep (se 1 (by rfl) ⟨472013, by rfl⟩ : syracuseStep 629351 = 944027) B944027
theorem B1415807 : Blo 626299 1415807 := bstep (se 1 (by rfl) ⟨1061855, by rfl⟩ : syracuseStep 1415807 = 2123711) B2123711
theorem B629375 : Blo 626299 629375 := bstep (se 1 (by rfl) ⟨472031, by rfl⟩ : syracuseStep 629375 = 944063) B944063
theorem B1415915 : Blo 626299 1415915 := bstep (se 1 (by rfl) ⟨1061936, by rfl⟩ : syracuseStep 1415915 = 2123873) B2123873
theorem B629499 : Blo 626299 629499 := bstep (se 1 (by rfl) ⟨472124, by rfl⟩ : syracuseStep 629499 = 944249) B944249
theorem B3185405 : Blo 626299 3185405 := bstep (se 3 (by rfl) ⟨597263, by rfl⟩ : syracuseStep 3185405 = 1194527) B1194527
theorem B1416185 : Blo 626299 1416185 := bstep (se 2 (by rfl) ⟨531069, by rfl⟩ : syracuseStep 1416185 = 1062139) B1062139
theorem B629755 : Blo 626299 629755 := bstep (se 1 (by rfl) ⟨472316, by rfl⟩ : syracuseStep 629755 = 944633) B944633
theorem B629791 : Blo 626299 629791 := bstep (se 1 (by rfl) ⟨472343, by rfl⟩ : syracuseStep 629791 = 944687) B944687
theorem B1416275 : Blo 626299 1416275 := bstep (se 1 (by rfl) ⟨1062206, by rfl⟩ : syracuseStep 1416275 = 2124413) B2124413
theorem B1416455 : Blo 626299 1416455 := bstep (se 1 (by rfl) ⟨1062341, by rfl⟩ : syracuseStep 1416455 = 2124683) B2124683
theorem B12885257 : Blo 626299 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B630079 : Blo 626299 630079 := bstep (se 1 (by rfl) ⟨472559, by rfl⟩ : syracuseStep 630079 = 945119) B945119
theorem B794063 : Blo 626299 794063 := bstep (se 1 (by rfl) ⟨595547, by rfl⟩ : syracuseStep 794063 = 1191095) B1191095
theorem B794215 : Blo 626299 794215 := bstep (se 1 (by rfl) ⟨595661, by rfl⟩ : syracuseStep 794215 = 1191323) B1191323
theorem B1416815 : Blo 626299 1416815 := bstep (se 1 (by rfl) ⟨1062611, by rfl⟩ : syracuseStep 1416815 = 2125223) B2125223
theorem B1417103 : Blo 626299 1417103 := bstep (se 1 (by rfl) ⟨1062827, by rfl⟩ : syracuseStep 1417103 = 2125655) B2125655
theorem B1613819 : Blo 626299 1613819 := bstep (se 1 (by rfl) ⟨1210364, by rfl⟩ : syracuseStep 1613819 = 2420729) B2420729
theorem B1417211 : Blo 626299 1417211 := bstep (se 1 (by rfl) ⟨1062908, by rfl⟩ : syracuseStep 1417211 = 2125817) B2125817
theorem B5087357 : Blo 626299 5087357 := bstep (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) B1907759
theorem B1417391 : Blo 626299 1417391 := bstep (se 1 (by rfl) ⟨1063043, by rfl⟩ : syracuseStep 1417391 = 2126087) B2126087
theorem B794863 : Blo 626299 794863 := bstep (se 1 (by rfl) ⟨596147, by rfl⟩ : syracuseStep 794863 = 1192295) B1192295
theorem B1417643 : Blo 626299 1417643 := bstep (se 1 (by rfl) ⟨1063232, by rfl⟩ : syracuseStep 1417643 = 2126465) B2126465
theorem B1417823 : Blo 626299 1417823 := bstep (se 1 (by rfl) ⟨1063367, by rfl⟩ : syracuseStep 1417823 = 2126735) B2126735
theorem B6791789 : Blo 626299 6791789 := bstep (se 3 (by rfl) ⟨1273460, by rfl⟩ : syracuseStep 6791789 = 2546921) B2546921
theorem B3187511 : Blo 626299 3187511 := bstep (se 1 (by rfl) ⟨2390633, by rfl⟩ : syracuseStep 3187511 = 4781267) B4781267
theorem B1418111 : Blo 626299 1418111 := bstep (se 1 (by rfl) ⟨1063583, by rfl⟩ : syracuseStep 1418111 = 2127167) B2127167
theorem B1909757 : Blo 626299 1909757 := bstep (se 3 (by rfl) ⟨358079, by rfl⟩ : syracuseStep 1909757 = 716159) B716159
theorem B13411595 : Blo 626299 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B894415 : Blo 626299 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B3581759 : Blo 626299 3581759 := bstep (se 1 (by rfl) ⟨2686319, by rfl⟩ : syracuseStep 3581759 = 5372639) B5372639
theorem B2009231 : Blo 626299 2009231 := bstep (se 1 (by rfl) ⟨1506923, by rfl⟩ : syracuseStep 2009231 = 3013847) B3013847
theorem B3188969 : Blo 626299 3188969 := bstep (se 2 (by rfl) ⟨1195863, by rfl⟩ : syracuseStep 3188969 = 2391727) B2391727
theorem B3975617 : Blo 626299 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B5155321 : Blo 626299 5155321 := bstep (se 2 (by rfl) ⟨1933245, by rfl⟩ : syracuseStep 5155321 = 3866491) B3866491
theorem B1059439 : Blo 626299 1059439 := bstep (se 1 (by rfl) ⟨794579, by rfl⟩ : syracuseStep 1059439 = 1589159) B1589159
theorem B1059655 : Blo 626299 1059655 := bstep (se 1 (by rfl) ⟨794741, by rfl⟩ : syracuseStep 1059655 = 1589483) B1589483
theorem B1191019 : Blo 626299 1191019 := bstep (se 1 (by rfl) ⟨893264, by rfl⟩ : syracuseStep 1191019 = 1786529) B1786529
theorem B3583673 : Blo 626299 3583673 := bstep (se 2 (by rfl) ⟨1343877, by rfl⟩ : syracuseStep 3583673 = 2687755) B2687755
theorem B25800713 : Blo 626299 25800713 := bstep (se 2 (by rfl) ⟨9675267, by rfl⟩ : syracuseStep 25800713 = 19350535) B19350535
theorem B2011243 : Blo 626299 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B1192097 : Blo 626299 1192097 := bstep (se 2 (by rfl) ⟨447036, by rfl⟩ : syracuseStep 1192097 = 894073) B894073
theorem B1061147 : Blo 626299 1061147 := bstep (se 1 (by rfl) ⟨795860, by rfl⟩ : syracuseStep 1061147 = 1591721) B1591721
theorem B12038615 : Blo 626299 12038615 := bstep (se 1 (by rfl) ⟨9028961, by rfl⟩ : syracuseStep 12038615 = 18057923) B18057923
theorem B1192735 : Blo 626299 1192735 := bstep (se 1 (by rfl) ⟨894551, by rfl⟩ : syracuseStep 1192735 = 1789103) B1789103
theorem B3453961 : Blo 626299 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B10171601 : Blo 626299 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B1783795 : Blo 626299 1783795 := bstep (se 1 (by rfl) ⟨1337846, by rfl⟩ : syracuseStep 1783795 = 2675693) B2675693
theorem B669799 : Blo 626299 669799 := bstep (se 1 (by rfl) ⟨502349, by rfl⟩ : syracuseStep 669799 = 1004699) B1004699
theorem B637031 : Blo 626299 637031 := bstep (se 1 (by rfl) ⟨477773, by rfl⟩ : syracuseStep 637031 = 955547) B955547
theorem B5356205 : Blo 626299 5356205 := bstep (se 3 (by rfl) ⟨1004288, by rfl⟩ : syracuseStep 5356205 = 2008577) B2008577
theorem B1915787 : Blo 626299 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B52411961 : Blo 626299 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B2014895 : Blo 626299 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B1588967 : Blo 626299 1588967 := bstep (se 1 (by rfl) ⟨1191725, by rfl⟩ : syracuseStep 1588967 = 2383451) B2383451
theorem B3391397 : Blo 626299 3391397 := bstep (se 4 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 3391397 = 635887) B635887
theorem B966649 : Blo 626299 966649 := bstep (se 2 (by rfl) ⟨362493, by rfl⟩ : syracuseStep 966649 = 724987) B724987
theorem B15253505 : Blo 626299 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B7258403 : Blo 626299 7258403 := bstep (se 1 (by rfl) ⟨5443802, by rfl⟩ : syracuseStep 7258403 = 10887605) B10887605
theorem B7160237 : Blo 626299 7160237 := bstep (se 3 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 7160237 = 2685089) B2685089
theorem B3589231 : Blo 626299 3589231 := bstep (se 1 (by rfl) ⟨2691923, by rfl⟩ : syracuseStep 3589231 = 5383847) B5383847
theorem B1590455 : Blo 626299 1590455 := bstep (se 1 (by rfl) ⟨1192841, by rfl⟩ : syracuseStep 1590455 = 2385683) B2385683
theorem B3622319 : Blo 626299 3622319 := bstep (se 1 (by rfl) ⟨2716739, by rfl⟩ : syracuseStep 3622319 = 5433479) B5433479
theorem B1787645 : Blo 626299 1787645 := bstep (se 3 (by rfl) ⟨335183, by rfl⟩ : syracuseStep 1787645 = 670367) B670367
theorem B2115773 : Blo 626299 2115773 := bstep (se 3 (by rfl) ⟨396707, by rfl⟩ : syracuseStep 2115773 = 793415) B793415
theorem B7620875 : Blo 626299 7620875 := bstep (se 1 (by rfl) ⟨5715656, by rfl⟩ : syracuseStep 7620875 = 11431313) B11431313
theorem B2115881 : Blo 626299 2115881 := bstep (se 2 (by rfl) ⟨793455, by rfl⟩ : syracuseStep 2115881 = 1586911) B1586911
theorem B2378423 : Blo 626299 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B3066623 : Blo 626299 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B2018047 : Blo 626299 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B1592531 : Blo 626299 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B708655 : Blo 626299 708655 := bstep (se 1 (by rfl) ⟨531491, by rfl⟩ : syracuseStep 708655 = 1062983) B1062983
theorem B2117771 : Blo 626299 2117771 := bstep (se 1 (by rfl) ⟨1588328, by rfl⟩ : syracuseStep 2117771 = 3176657) B3176657
theorem B2380063 : Blo 626299 2380063 := bstep (se 1 (by rfl) ⟨1785047, by rfl⟩ : syracuseStep 2380063 = 3570095) B3570095
theorem B1528235 : Blo 626299 1528235 := bstep (se 1 (by rfl) ⟨1146176, by rfl⟩ : syracuseStep 1528235 = 2292353) B2292353
theorem B7164611 : Blo 626299 7164611 := bstep (se 1 (by rfl) ⟨5373458, by rfl⟩ : syracuseStep 7164611 = 10746917) B10746917
theorem B2118959 : Blo 626299 2118959 := bstep (se 1 (by rfl) ⟨1589219, by rfl⟩ : syracuseStep 2118959 = 3178439) B3178439
theorem B1594799 : Blo 626299 1594799 := bstep (se 1 (by rfl) ⟨1196099, by rfl⟩ : syracuseStep 1594799 = 2392199) B2392199
theorem B939515 : Blo 626299 939515 := bstep (se 1 (by rfl) ⟨704636, by rfl⟩ : syracuseStep 939515 = 1409273) B1409273
theorem B939551 : Blo 626299 939551 := bstep (se 1 (by rfl) ⟨704663, by rfl⟩ : syracuseStep 939551 = 1409327) B1409327
theorem B939689 : Blo 626299 939689 := bstep (se 2 (by rfl) ⟨352383, by rfl⟩ : syracuseStep 939689 = 704767) B704767
theorem B939695 : Blo 626299 939695 := bstep (se 1 (by rfl) ⟨704771, by rfl⟩ : syracuseStep 939695 = 1409543) B1409543
theorem B2119391 : Blo 626299 2119391 := bstep (se 1 (by rfl) ⟨1589543, by rfl⟩ : syracuseStep 2119391 = 3179087) B3179087
theorem B939815 : Blo 626299 939815 := bstep (se 1 (by rfl) ⟨704861, by rfl⟩ : syracuseStep 939815 = 1409723) B1409723
theorem B940073 : Blo 626299 940073 := bstep (se 2 (by rfl) ⟨352527, by rfl⟩ : syracuseStep 940073 = 705055) B705055
theorem B940103 : Blo 626299 940103 := bstep (se 1 (by rfl) ⟨705077, by rfl⟩ : syracuseStep 940103 = 1410155) B1410155
theorem B940415 : Blo 626299 940415 := bstep (se 1 (by rfl) ⟨705311, by rfl⟩ : syracuseStep 940415 = 1410623) B1410623
theorem B940487 : Blo 626299 940487 := bstep (se 1 (by rfl) ⟨705365, by rfl⟩ : syracuseStep 940487 = 1410731) B1410731
theorem B1432007 : Blo 626299 1432007 := bstep (se 1 (by rfl) ⟨1074005, by rfl⟩ : syracuseStep 1432007 = 2148011) B2148011
theorem B940703 : Blo 626299 940703 := bstep (se 1 (by rfl) ⟨705527, by rfl⟩ : syracuseStep 940703 = 1411055) B1411055
theorem B940847 : Blo 626299 940847 := bstep (se 1 (by rfl) ⟨705635, by rfl⟩ : syracuseStep 940847 = 1411271) B1411271
theorem B6871931 : Blo 626299 6871931 := bstep (se 1 (by rfl) ⟨5153948, by rfl⟩ : syracuseStep 6871931 = 10307897) B10307897
theorem B940937 : Blo 626299 940937 := bstep (se 2 (by rfl) ⟨352851, by rfl⟩ : syracuseStep 940937 = 705703) B705703
theorem B940967 : Blo 626299 940967 := bstep (se 1 (by rfl) ⟨705725, by rfl⟩ : syracuseStep 940967 = 1411451) B1411451
theorem B941147 : Blo 626299 941147 := bstep (se 1 (by rfl) ⟨705860, by rfl⟩ : syracuseStep 941147 = 1411721) B1411721
theorem B22863035 : Blo 626299 22863035 := bstep (se 1 (by rfl) ⟨17147276, by rfl⟩ : syracuseStep 22863035 = 34294553) B34294553
theorem B2677967 : Blo 626299 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B1793249 : Blo 626299 1793249 := bstep (se 2 (by rfl) ⟨672468, by rfl⟩ : syracuseStep 1793249 = 1344937) B1344937
theorem B941339 : Blo 626299 941339 := bstep (se 1 (by rfl) ⟨706004, by rfl⟩ : syracuseStep 941339 = 1412009) B1412009
theorem B941807 : Blo 626299 941807 := bstep (se 1 (by rfl) ⟨706355, by rfl⟩ : syracuseStep 941807 = 1412711) B1412711
theorem B941993 : Blo 626299 941993 := bstep (se 2 (by rfl) ⟨353247, by rfl⟩ : syracuseStep 941993 = 706495) B706495
theorem B942143 : Blo 626299 942143 := bstep (se 1 (by rfl) ⟨706607, by rfl⟩ : syracuseStep 942143 = 1413215) B1413215
theorem B942377 : Blo 626299 942377 := bstep (se 2 (by rfl) ⟨353391, by rfl⟩ : syracuseStep 942377 = 706783) B706783
theorem B942647 : Blo 626299 942647 := bstep (se 1 (by rfl) ⟨706985, by rfl⟩ : syracuseStep 942647 = 1413971) B1413971
theorem B943007 : Blo 626299 943007 := bstep (se 1 (by rfl) ⟨707255, by rfl⟩ : syracuseStep 943007 = 1414511) B1414511
theorem B3171311 : Blo 626299 3171311 := bstep (se 1 (by rfl) ⟨2378483, by rfl⟩ : syracuseStep 3171311 = 4756967) B4756967
theorem B943295 : Blo 626299 943295 := bstep (se 1 (by rfl) ⟨707471, by rfl⟩ : syracuseStep 943295 = 1414943) B1414943
theorem B943439 : Blo 626299 943439 := bstep (se 1 (by rfl) ⟨707579, by rfl⟩ : syracuseStep 943439 = 1415159) B1415159
theorem B943529 : Blo 626299 943529 := bstep (se 2 (by rfl) ⟨353823, by rfl⟩ : syracuseStep 943529 = 707647) B707647
theorem B17229277 : Blo 626299 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B943679 : Blo 626299 943679 := bstep (se 1 (by rfl) ⟨707759, by rfl⟩ : syracuseStep 943679 = 1415519) B1415519
theorem B944039 : Blo 626299 944039 := bstep (se 1 (by rfl) ⟨708029, by rfl⟩ : syracuseStep 944039 = 1416059) B1416059
theorem B944159 : Blo 626299 944159 := bstep (se 1 (by rfl) ⟨708119, by rfl⟩ : syracuseStep 944159 = 1416239) B1416239
theorem B10217785 : Blo 626299 10217785 := bstep (se 2 (by rfl) ⟨3831669, by rfl⟩ : syracuseStep 10217785 = 7663339) B7663339
theorem B7170443 : Blo 626299 7170443 := bstep (se 1 (by rfl) ⟨5377832, by rfl⟩ : syracuseStep 7170443 = 10755665) B10755665
theorem B5368265 : Blo 626299 5368265 := bstep (se 2 (by rfl) ⟨2013099, by rfl⟩ : syracuseStep 5368265 = 4026199) B4026199
theorem B944615 : Blo 626299 944615 := bstep (se 1 (by rfl) ⟨708461, by rfl⟩ : syracuseStep 944615 = 1416923) B1416923
theorem B944795 : Blo 626299 944795 := bstep (se 1 (by rfl) ⟨708596, by rfl⟩ : syracuseStep 944795 = 1417193) B1417193
theorem B2386655 : Blo 626299 2386655 := bstep (se 1 (by rfl) ⟨1789991, by rfl⟩ : syracuseStep 2386655 = 3579983) B3579983
theorem B945017 : Blo 626299 945017 := bstep (se 2 (by rfl) ⟨354381, by rfl⟩ : syracuseStep 945017 = 708763) B708763
theorem B945263 : Blo 626299 945263 := bstep (se 1 (by rfl) ⟨708947, by rfl⟩ : syracuseStep 945263 = 1417895) B1417895
theorem B945359 : Blo 626299 945359 := bstep (se 1 (by rfl) ⟨709019, by rfl⟩ : syracuseStep 945359 = 1418039) B1418039
theorem B2387627 : Blo 626299 2387627 := bstep (se 1 (by rfl) ⟨1790720, by rfl⟩ : syracuseStep 2387627 = 3581441) B3581441
theorem B51572537 : Blo 626299 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B5107855 : Blo 626299 5107855 := bstep (se 1 (by rfl) ⟨3830891, by rfl⟩ : syracuseStep 5107855 = 7661783) B7661783
theorem B2650439 : Blo 626299 2650439 := bstep (se 1 (by rfl) ⟨1987829, by rfl⟩ : syracuseStep 2650439 = 3975659) B3975659
theorem B3404699 : Blo 626299 3404699 := bstep (se 1 (by rfl) ⟨2553524, by rfl⟩ : syracuseStep 3404699 = 5107049) B5107049
theorem B3011849 : Blo 626299 3011849 := bstep (se 2 (by rfl) ⟨1129443, by rfl⟩ : syracuseStep 3011849 = 2258887) B2258887
theorem B849791 : Blo 626299 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B9074753 : Blo 626299 9074753 := bstep (se 2 (by rfl) ⟨3403032, by rfl⟩ : syracuseStep 9074753 = 6806065) B6806065
theorem B1308847 : Blo 626299 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B1342955 : Blo 626299 1342955 := bstep (se 1 (by rfl) ⟨1007216, by rfl⟩ : syracuseStep 1342955 = 2014433) B2014433
theorem B4030073 : Blo 626299 4030073 := bstep (se 2 (by rfl) ⟨1511277, by rfl⟩ : syracuseStep 4030073 = 3022555) B3022555
theorem B851623 : Blo 626299 851623 := bstep (se 1 (by rfl) ⟨638717, by rfl⟩ : syracuseStep 851623 = 1277435) B1277435
theorem B3178925 : Blo 626299 3178925 := bstep (se 3 (by rfl) ⟨596048, by rfl⟩ : syracuseStep 3178925 = 1192097) B1192097
theorem B3572261 : Blo 626299 3572261 := bstep (se 4 (by rfl) ⟨334899, by rfl⟩ : syracuseStep 3572261 = 669799) B669799
theorem B1410515 : Blo 626299 1410515 := bstep (se 1 (by rfl) ⟨1057886, by rfl⟩ : syracuseStep 1410515 = 2115773) B2115773
theorem B4785641 : Blo 626299 4785641 := bstep (se 2 (by rfl) ⟨1794615, by rfl⟩ : syracuseStep 4785641 = 3589231) B3589231
theorem B5080583 : Blo 626299 5080583 := bstep (se 1 (by rfl) ⟨3810437, by rfl⟩ : syracuseStep 5080583 = 7620875) B7620875
theorem B1410587 : Blo 626299 1410587 := bstep (se 1 (by rfl) ⟨1057940, by rfl⟩ : syracuseStep 1410587 = 2115881) B2115881
theorem B22972369 : Blo 626299 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B1411847 : Blo 626299 1411847 := bstep (se 1 (by rfl) ⟨1058885, by rfl⟩ : syracuseStep 1411847 = 2117771) B2117771
theorem B1018823 : Blo 626299 1018823 := bstep (se 1 (by rfl) ⟨764117, by rfl⟩ : syracuseStep 1018823 = 1528235) B1528235
theorem B1412585 : Blo 626299 1412585 := bstep (se 2 (by rfl) ⟨529719, by rfl⟩ : syracuseStep 1412585 = 1059439) B1059439
theorem B1412639 : Blo 626299 1412639 := bstep (se 1 (by rfl) ⟨1059479, by rfl⟩ : syracuseStep 1412639 = 2118959) B2118959
theorem B5377697 : Blo 626299 5377697 := bstep (se 2 (by rfl) ⟨2016636, by rfl⟩ : syracuseStep 5377697 = 4033273) B4033273
theorem B626343 : Blo 626299 626343 := bstep (se 1 (by rfl) ⟨469757, by rfl⟩ : syracuseStep 626343 = 939515) B939515
theorem B2690729 : Blo 626299 2690729 := bstep (se 2 (by rfl) ⟨1009023, by rfl⟩ : syracuseStep 2690729 = 2018047) B2018047
theorem B626367 : Blo 626299 626367 := bstep (se 1 (by rfl) ⟨469775, by rfl⟩ : syracuseStep 626367 = 939551) B939551
theorem B1412873 : Blo 626299 1412873 := bstep (se 2 (by rfl) ⟨529827, by rfl⟩ : syracuseStep 1412873 = 1059655) B1059655
theorem B626459 : Blo 626299 626459 := bstep (se 1 (by rfl) ⟨469844, by rfl⟩ : syracuseStep 626459 = 939689) B939689
theorem B626463 : Blo 626299 626463 := bstep (se 1 (by rfl) ⟨469847, by rfl⟩ : syracuseStep 626463 = 939695) B939695
theorem B4296509 : Blo 626299 4296509 := bstep (se 3 (by rfl) ⟨805595, by rfl⟩ : syracuseStep 4296509 = 1611191) B1611191
theorem B1412927 : Blo 626299 1412927 := bstep (se 1 (by rfl) ⟨1059695, by rfl⟩ : syracuseStep 1412927 = 2119391) B2119391
theorem B626543 : Blo 626299 626543 := bstep (se 1 (by rfl) ⟨469907, by rfl⟩ : syracuseStep 626543 = 939815) B939815
theorem B626715 : Blo 626299 626715 := bstep (se 1 (by rfl) ⟨470036, by rfl⟩ : syracuseStep 626715 = 940073) B940073
theorem B626735 : Blo 626299 626735 := bstep (se 1 (by rfl) ⟨470051, by rfl⟩ : syracuseStep 626735 = 940103) B940103
theorem B626943 : Blo 626299 626943 := bstep (se 1 (by rfl) ⟨470207, by rfl⟩ : syracuseStep 626943 = 940415) B940415
theorem B626991 : Blo 626299 626991 := bstep (se 1 (by rfl) ⟨470243, by rfl⟩ : syracuseStep 626991 = 940487) B940487
theorem B954671 : Blo 626299 954671 := bstep (se 1 (by rfl) ⟨716003, by rfl⟩ : syracuseStep 954671 = 1432007) B1432007
theorem B627135 : Blo 626299 627135 := bstep (se 1 (by rfl) ⟨470351, by rfl⟩ : syracuseStep 627135 = 940703) B940703
theorem B627231 : Blo 626299 627231 := bstep (se 1 (by rfl) ⟨470423, by rfl⟩ : syracuseStep 627231 = 940847) B940847
theorem B627291 : Blo 626299 627291 := bstep (se 1 (by rfl) ⟨470468, by rfl⟩ : syracuseStep 627291 = 940937) B940937
theorem B627311 : Blo 626299 627311 := bstep (se 1 (by rfl) ⟨470483, by rfl⟩ : syracuseStep 627311 = 940967) B940967
theorem B627431 : Blo 626299 627431 := bstep (se 1 (by rfl) ⟨470573, by rfl⟩ : syracuseStep 627431 = 941147) B941147
theorem B15242023 : Blo 626299 15242023 := bstep (se 1 (by rfl) ⟨11431517, by rfl⟩ : syracuseStep 15242023 = 22863035) B22863035
theorem B8590171 : Blo 626299 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B627559 : Blo 626299 627559 := bstep (se 1 (by rfl) ⟨470669, by rfl⟩ : syracuseStep 627559 = 941339) B941339
theorem B2266109 : Blo 626299 2266109 := bstep (se 3 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 2266109 = 849791) B849791
theorem B627871 : Blo 626299 627871 := bstep (se 1 (by rfl) ⟨470903, by rfl⟩ : syracuseStep 627871 = 941807) B941807
theorem B627995 : Blo 626299 627995 := bstep (se 1 (by rfl) ⟨470996, by rfl⟩ : syracuseStep 627995 = 941993) B941993
theorem B628095 : Blo 626299 628095 := bstep (se 1 (by rfl) ⟨471071, by rfl⟩ : syracuseStep 628095 = 942143) B942143
theorem B628251 : Blo 626299 628251 := bstep (se 1 (by rfl) ⟨471188, by rfl⟩ : syracuseStep 628251 = 942377) B942377
theorem B628431 : Blo 626299 628431 := bstep (se 1 (by rfl) ⟨471323, by rfl⟩ : syracuseStep 628431 = 942647) B942647
theorem B628671 : Blo 626299 628671 := bstep (se 1 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 628671 = 943007) B943007
theorem B628863 : Blo 626299 628863 := bstep (se 1 (by rfl) ⟨471647, by rfl⟩ : syracuseStep 628863 = 943295) B943295
theorem B628959 : Blo 626299 628959 := bstep (se 1 (by rfl) ⟨471719, by rfl⟩ : syracuseStep 628959 = 943439) B943439
theorem B629019 : Blo 626299 629019 := bstep (se 1 (by rfl) ⟨471764, by rfl⟩ : syracuseStep 629019 = 943529) B943529
theorem B629119 : Blo 626299 629119 := bstep (se 1 (by rfl) ⟨471839, by rfl⟩ : syracuseStep 629119 = 943679) B943679
theorem B629359 : Blo 626299 629359 := bstep (se 1 (by rfl) ⟨472019, by rfl⟩ : syracuseStep 629359 = 944039) B944039
theorem B629439 : Blo 626299 629439 := bstep (se 1 (by rfl) ⟨472079, by rfl⟩ : syracuseStep 629439 = 944159) B944159
theorem B3578843 : Blo 626299 3578843 := bstep (se 1 (by rfl) ⟨2684132, by rfl⟩ : syracuseStep 3578843 = 5368265) B5368265
theorem B629743 : Blo 626299 629743 := bstep (se 1 (by rfl) ⟨472307, by rfl⟩ : syracuseStep 629743 = 944615) B944615
theorem B8068085 : Blo 626299 8068085 := bstep (se 5 (by rfl) ⟨378191, by rfl⟩ : syracuseStep 8068085 = 756383) B756383
theorem B629863 : Blo 626299 629863 := bstep (se 1 (by rfl) ⟨472397, by rfl⟩ : syracuseStep 629863 = 944795) B944795
theorem B630011 : Blo 626299 630011 := bstep (se 1 (by rfl) ⟨472508, by rfl⟩ : syracuseStep 630011 = 945017) B945017
theorem B630175 : Blo 626299 630175 := bstep (se 1 (by rfl) ⟨472631, by rfl⟩ : syracuseStep 630175 = 945263) B945263
theorem B630239 : Blo 626299 630239 := bstep (se 1 (by rfl) ⟨472679, by rfl⟩ : syracuseStep 630239 = 945359) B945359
theorem B34381691 : Blo 626299 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B1745129 : Blo 626299 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B2269799 : Blo 626299 2269799 := bstep (se 1 (by rfl) ⟨1702349, by rfl⟩ : syracuseStep 2269799 = 3404699) B3404699
theorem B2007899 : Blo 626299 2007899 := bstep (se 1 (by rfl) ⟨1505924, by rfl⟩ : syracuseStep 2007899 = 3011849) B3011849
theorem B1058953 : Blo 626299 1058953 := bstep (se 2 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 1058953 = 794215) B794215
theorem B895303 : Blo 626299 895303 := bstep (se 1 (by rfl) ⟨671477, by rfl⟩ : syracuseStep 895303 = 1342955) B1342955
theorem B34941307 : Blo 626299 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B1059311 : Blo 626299 1059311 := bstep (se 1 (by rfl) ⟨794483, by rfl⟩ : syracuseStep 1059311 = 1588967) B1588967
theorem B1288865 : Blo 626299 1288865 := bstep (se 2 (by rfl) ⟨483324, by rfl⟩ : syracuseStep 1288865 = 966649) B966649
theorem B10169003 : Blo 626299 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B1059817 : Blo 626299 1059817 := bstep (se 2 (by rfl) ⟨397431, by rfl⟩ : syracuseStep 1059817 = 794863) B794863
theorem B10202219 : Blo 626299 10202219 := bstep (se 1 (by rfl) ⟨7651664, by rfl⟩ : syracuseStep 10202219 = 15303329) B15303329
theorem B3583399 : Blo 626299 3583399 := bstep (se 1 (by rfl) ⟨2687549, by rfl⟩ : syracuseStep 3583399 = 5375099) B5375099
theorem B1060303 : Blo 626299 1060303 := bstep (se 1 (by rfl) ⟨795227, by rfl⟩ : syracuseStep 1060303 = 1590455) B1590455
theorem B1191763 : Blo 626299 1191763 := bstep (se 1 (by rfl) ⟨893822, by rfl⟩ : syracuseStep 1191763 = 1787645) B1787645
theorem B8138989 : Blo 626299 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B15249815 : Blo 626299 15249815 := bstep (se 1 (by rfl) ⟨11437361, by rfl⟩ : syracuseStep 15249815 = 22874723) B22874723
theorem B1585615 : Blo 626299 1585615 := bstep (se 1 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 1585615 = 2378423) B2378423
theorem B2044415 : Blo 626299 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B1192553 : Blo 626299 1192553 := bstep (se 2 (by rfl) ⟨447207, by rfl⟩ : syracuseStep 1192553 = 894415) B894415
theorem B1061687 : Blo 626299 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B5093131 : Blo 626299 5093131 := bstep (se 1 (by rfl) ⟨3819848, by rfl⟩ : syracuseStep 5093131 = 7639697) B7639697
theorem B1357607 : Blo 626299 1357607 := bstep (se 1 (by rfl) ⟨1018205, by rfl⟩ : syracuseStep 1357607 = 2036411) B2036411
theorem B4765715 : Blo 626299 4765715 := bstep (se 1 (by rfl) ⟨3574286, by rfl⟩ : syracuseStep 4765715 = 7148573) B7148573
theorem B35764253 : Blo 626299 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B1063199 : Blo 626299 1063199 := bstep (se 1 (by rfl) ⟨797399, by rfl⟩ : syracuseStep 1063199 = 1594799) B1594799
theorem B2013767 : Blo 626299 2013767 := bstep (se 1 (by rfl) ⟨1510325, by rfl⟩ : syracuseStep 2013767 = 3020651) B3020651
theorem B1588025 : Blo 626299 1588025 := bstep (se 2 (by rfl) ⟨595509, by rfl⟩ : syracuseStep 1588025 = 1191019) B1191019
theorem B4766687 : Blo 626299 4766687 := bstep (se 1 (by rfl) ⟨3575015, by rfl⟩ : syracuseStep 4766687 = 7150031) B7150031
theorem B1785311 : Blo 626299 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B1195499 : Blo 626299 1195499 := bstep (se 1 (by rfl) ⟨896624, by rfl⟩ : syracuseStep 1195499 = 1793249) B1793249
theorem B3391571 : Blo 626299 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B2114207 : Blo 626299 2114207 := bstep (se 1 (by rfl) ⟨1585655, by rfl⟩ : syracuseStep 2114207 = 3171311) B3171311
theorem B1590313 : Blo 626299 1590313 := bstep (se 2 (by rfl) ⟨596367, by rfl⟩ : syracuseStep 1590313 = 1192735) B1192735
theorem B4605281 : Blo 626299 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B3589505 : Blo 626299 3589505 := bstep (se 2 (by rfl) ⟨1346064, by rfl⟩ : syracuseStep 3589505 = 2692129) B2692129
theorem B1591103 : Blo 626299 1591103 := bstep (se 1 (by rfl) ⟨1193327, by rfl⟩ : syracuseStep 1591103 = 2386655) B2386655
theorem B1591751 : Blo 626299 1591751 := bstep (se 1 (by rfl) ⟨1193813, by rfl⟩ : syracuseStep 1591751 = 2387627) B2387627
theorem B2378393 : Blo 626299 2378393 := bstep (se 2 (by rfl) ⟨891897, by rfl⟩ : syracuseStep 2378393 = 1783795) B1783795
theorem B707431 : Blo 626299 707431 := bstep (se 1 (by rfl) ⟨530573, by rfl⟩ : syracuseStep 707431 = 1061147) B1061147
theorem B4541989 : Blo 626299 4541989 := bstep (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) B851623
theorem B2117501 : Blo 626299 2117501 := bstep (se 3 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 2117501 = 794063) B794063
theorem B6049835 : Blo 626299 6049835 := bstep (se 1 (by rfl) ⟨4537376, by rfl⟩ : syracuseStep 6049835 = 9074753) B9074753
theorem B4838935 : Blo 626299 4838935 := bstep (se 1 (by rfl) ⟨3629201, by rfl⟩ : syracuseStep 4838935 = 7258403) B7258403
theorem B939575 : Blo 626299 939575 := bstep (se 1 (by rfl) ⟨704681, by rfl⟩ : syracuseStep 939575 = 1409363) B1409363
theorem B4773491 : Blo 626299 4773491 := bstep (se 1 (by rfl) ⟨3580118, by rfl⟩ : syracuseStep 4773491 = 7160237) B7160237
theorem B1595123 : Blo 626299 1595123 := bstep (se 1 (by rfl) ⟨1196342, by rfl⟩ : syracuseStep 1595123 = 2392685) B2392685
theorem B940079 : Blo 626299 940079 := bstep (se 1 (by rfl) ⟨705059, by rfl⟩ : syracuseStep 940079 = 1410119) B1410119
theorem B940199 : Blo 626299 940199 := bstep (se 1 (by rfl) ⟨705149, by rfl⟩ : syracuseStep 940199 = 1410299) B1410299
theorem B7067837 : Blo 626299 7067837 := bstep (se 3 (by rfl) ⟨1325219, by rfl⟩ : syracuseStep 7067837 = 2650439) B2650439
theorem B2414879 : Blo 626299 2414879 := bstep (se 1 (by rfl) ⟨1811159, by rfl⟩ : syracuseStep 2414879 = 3622319) B3622319
theorem B940367 : Blo 626299 940367 := bstep (se 1 (by rfl) ⟨705275, by rfl⟩ : syracuseStep 940367 = 1410551) B1410551
theorem B2382311 : Blo 626299 2382311 := bstep (se 1 (by rfl) ⟨1786733, by rfl⟩ : syracuseStep 2382311 = 3573467) B3573467
theorem B1006345 : Blo 626299 1006345 := bstep (se 2 (by rfl) ⟨377379, by rfl⟩ : syracuseStep 1006345 = 754759) B754759
theorem B18111437 : Blo 626299 18111437 := bstep (se 3 (by rfl) ⟨3395894, by rfl⟩ : syracuseStep 18111437 = 6791789) B6791789
theorem B941087 : Blo 626299 941087 := bstep (se 1 (by rfl) ⟨705815, by rfl⟩ : syracuseStep 941087 = 1411631) B1411631
theorem B2120903 : Blo 626299 2120903 := bstep (se 1 (by rfl) ⟨1590677, by rfl⟩ : syracuseStep 2120903 = 3181355) B3181355
theorem B941519 : Blo 626299 941519 := bstep (se 1 (by rfl) ⟨706139, by rfl⟩ : syracuseStep 941519 = 1412279) B1412279
theorem B36789835 : Blo 626299 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B9068759 : Blo 626299 9068759 := bstep (se 1 (by rfl) ⟨6801569, by rfl⟩ : syracuseStep 9068759 = 13603139) B13603139
theorem B13623713 : Blo 626299 13623713 := bstep (se 2 (by rfl) ⟨5108892, by rfl⟩ : syracuseStep 13623713 = 10217785) B10217785
theorem B4776407 : Blo 626299 4776407 := bstep (se 1 (by rfl) ⟨3582305, by rfl⟩ : syracuseStep 4776407 = 7164611) B7164611
theorem B13591111 : Blo 626299 13591111 := bstep (se 1 (by rfl) ⟨10193333, by rfl⟩ : syracuseStep 13591111 = 20386667) B20386667
theorem B10707551 : Blo 626299 10707551 := bstep (se 1 (by rfl) ⟨8030663, by rfl⟩ : syracuseStep 10707551 = 16061327) B16061327
theorem B6873761 : Blo 626299 6873761 := bstep (se 2 (by rfl) ⟨2577660, by rfl⟩ : syracuseStep 6873761 = 5155321) B5155321
theorem B943055 : Blo 626299 943055 := bstep (se 1 (by rfl) ⟨707291, by rfl⟩ : syracuseStep 943055 = 1414583) B1414583
theorem B943103 : Blo 626299 943103 := bstep (se 1 (by rfl) ⟨707327, by rfl⟩ : syracuseStep 943103 = 1414655) B1414655
theorem B943175 : Blo 626299 943175 := bstep (se 1 (by rfl) ⟨707381, by rfl⟩ : syracuseStep 943175 = 1414763) B1414763
theorem B943355 : Blo 626299 943355 := bstep (se 1 (by rfl) ⟨707516, by rfl⟩ : syracuseStep 943355 = 1415033) B1415033
theorem B2549245 : Blo 626299 2549245 := bstep (se 3 (by rfl) ⟨477983, by rfl⟩ : syracuseStep 2549245 = 955967) B955967
theorem B943871 : Blo 626299 943871 := bstep (se 1 (by rfl) ⟨707903, by rfl⟩ : syracuseStep 943871 = 1415807) B1415807
theorem B943943 : Blo 626299 943943 := bstep (se 1 (by rfl) ⟨707957, by rfl⟩ : syracuseStep 943943 = 1415915) B1415915
theorem B2123603 : Blo 626299 2123603 := bstep (se 1 (by rfl) ⟨1592702, by rfl⟩ : syracuseStep 2123603 = 3185405) B3185405
theorem B4581287 : Blo 626299 4581287 := bstep (se 1 (by rfl) ⟨3435965, by rfl⟩ : syracuseStep 4581287 = 6871931) B6871931
theorem B944123 : Blo 626299 944123 := bstep (se 1 (by rfl) ⟨708092, by rfl⟩ : syracuseStep 944123 = 1416185) B1416185
theorem B944183 : Blo 626299 944183 := bstep (se 1 (by rfl) ⟨708137, by rfl⟩ : syracuseStep 944183 = 1416275) B1416275
theorem B944303 : Blo 626299 944303 := bstep (se 1 (by rfl) ⟨708227, by rfl⟩ : syracuseStep 944303 = 1416455) B1416455
theorem B944543 : Blo 626299 944543 := bstep (se 1 (by rfl) ⟨708407, by rfl⟩ : syracuseStep 944543 = 1416815) B1416815
theorem B944735 : Blo 626299 944735 := bstep (se 1 (by rfl) ⟨708551, by rfl⟩ : syracuseStep 944735 = 1417103) B1417103
theorem B1075879 : Blo 626299 1075879 := bstep (se 1 (by rfl) ⟨806909, by rfl⟩ : syracuseStep 1075879 = 1613819) B1613819
theorem B944807 : Blo 626299 944807 := bstep (se 1 (by rfl) ⟨708605, by rfl⟩ : syracuseStep 944807 = 1417211) B1417211
theorem B944873 : Blo 626299 944873 := bstep (se 2 (by rfl) ⟨354327, by rfl⟩ : syracuseStep 944873 = 708655) B708655
theorem B944927 : Blo 626299 944927 := bstep (se 1 (by rfl) ⟨708695, by rfl⟩ : syracuseStep 944927 = 1417391) B1417391
theorem B2681657 : Blo 626299 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B6810473 : Blo 626299 6810473 := bstep (se 2 (by rfl) ⟨2553927, by rfl⟩ : syracuseStep 6810473 = 5107855) B5107855
theorem B1698749 : Blo 626299 1698749 := bstep (se 3 (by rfl) ⟨318515, by rfl⟩ : syracuseStep 1698749 = 637031) B637031
theorem B945095 : Blo 626299 945095 := bstep (se 1 (by rfl) ⟨708821, by rfl⟩ : syracuseStep 945095 = 1417643) B1417643
theorem B3173417 : Blo 626299 3173417 := bstep (se 2 (by rfl) ⟨1190031, by rfl⟩ : syracuseStep 3173417 = 2380063) B2380063
theorem B945215 : Blo 626299 945215 := bstep (se 1 (by rfl) ⟨708911, by rfl⟩ : syracuseStep 945215 = 1417823) B1417823
theorem B2125007 : Blo 626299 2125007 := bstep (se 1 (by rfl) ⟨1593755, by rfl⟩ : syracuseStep 2125007 = 3187511) B3187511
theorem B945407 : Blo 626299 945407 := bstep (se 1 (by rfl) ⟨709055, by rfl⟩ : syracuseStep 945407 = 1418111) B1418111
theorem B1273171 : Blo 626299 1273171 := bstep (se 1 (by rfl) ⟨954878, by rfl⟩ : syracuseStep 1273171 = 1909757) B1909757
theorem B2387839 : Blo 626299 2387839 := bstep (se 1 (by rfl) ⟨1790879, by rfl⟩ : syracuseStep 2387839 = 3581759) B3581759
theorem B1339487 : Blo 626299 1339487 := bstep (se 1 (by rfl) ⟨1004615, by rfl⟩ : syracuseStep 1339487 = 2009231) B2009231
theorem B2125979 : Blo 626299 2125979 := bstep (se 1 (by rfl) ⟨1594484, by rfl⟩ : syracuseStep 2125979 = 3188969) B3188969
theorem B4780295 : Blo 626299 4780295 := bstep (se 1 (by rfl) ⟨3585221, by rfl⟩ : syracuseStep 4780295 = 7170443) B7170443
theorem B2650411 : Blo 626299 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B2389115 : Blo 626299 2389115 := bstep (se 1 (by rfl) ⟨1791836, by rfl⟩ : syracuseStep 2389115 = 3583673) B3583673
theorem B17200475 : Blo 626299 17200475 := bstep (se 1 (by rfl) ⟨12900356, by rfl⟩ : syracuseStep 17200475 = 25800713) B25800713
theorem B8025743 : Blo 626299 8025743 := bstep (se 1 (by rfl) ⟨6019307, by rfl⟩ : syracuseStep 8025743 = 12038615) B12038615
theorem B6781067 : Blo 626299 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B3570803 : Blo 626299 3570803 := bstep (se 1 (by rfl) ⟨2678102, by rfl⟩ : syracuseStep 3570803 = 5356205) B5356205
theorem B1277191 : Blo 626299 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B2686715 : Blo 626299 2686715 := bstep (se 1 (by rfl) ⟨2015036, by rfl⟩ : syracuseStep 2686715 = 4030073) B4030073
theorem B1343263 : Blo 626299 1343263 := bstep (se 1 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 1343263 = 2014895) B2014895
theorem B2260931 : Blo 626299 2260931 := bstep (se 1 (by rfl) ⟨1695698, by rfl⟩ : syracuseStep 2260931 = 3391397) B3391397
theorem B2261047 : Blo 626299 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B1409471 : Blo 626299 1409471 := bstep (se 1 (by rfl) ⟨1057103, by rfl⟩ : syracuseStep 1409471 = 2114207) B2114207
theorem B4653677 : Blo 626299 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B18121481 : Blo 626299 18121481 := bstep (se 2 (by rfl) ⟨6795555, by rfl⟩ : syracuseStep 18121481 = 13591111) B13591111
theorem B2393003 : Blo 626299 2393003 := bstep (se 1 (by rfl) ⟨1794752, by rfl⟩ : syracuseStep 2393003 = 3589505) B3589505
theorem B1411667 : Blo 626299 1411667 := bstep (se 1 (by rfl) ⟨1058750, by rfl⟩ : syracuseStep 1411667 = 2117501) B2117501
theorem B4033223 : Blo 626299 4033223 := bstep (se 1 (by rfl) ⟨3024917, by rfl⟩ : syracuseStep 4033223 = 6049835) B6049835
theorem B1411937 : Blo 626299 1411937 := bstep (se 2 (by rfl) ⟨529476, by rfl⟩ : syracuseStep 1411937 = 1058953) B1058953
theorem B1510739 : Blo 626299 1510739 := bstep (se 1 (by rfl) ⟨1133054, by rfl⟩ : syracuseStep 1510739 = 2266109) B2266109
theorem B626383 : Blo 626299 626383 := bstep (se 1 (by rfl) ⟨469787, by rfl⟩ : syracuseStep 626383 = 939575) B939575
theorem B3182327 : Blo 626299 3182327 := bstep (se 1 (by rfl) ⟨2386745, by rfl⟩ : syracuseStep 3182327 = 4773491) B4773491
theorem B1413089 : Blo 626299 1413089 := bstep (se 2 (by rfl) ⟨529908, by rfl⟩ : syracuseStep 1413089 = 1059817) B1059817
theorem B626719 : Blo 626299 626719 := bstep (se 1 (by rfl) ⟨470039, by rfl⟩ : syracuseStep 626719 = 940079) B940079
theorem B626799 : Blo 626299 626799 := bstep (se 1 (by rfl) ⟨470099, by rfl⟩ : syracuseStep 626799 = 940199) B940199
theorem B1609919 : Blo 626299 1609919 := bstep (se 1 (by rfl) ⟨1207439, by rfl⟩ : syracuseStep 1609919 = 2414879) B2414879
theorem B626911 : Blo 626299 626911 := bstep (se 1 (by rfl) ⟨470183, by rfl⟩ : syracuseStep 626911 = 940367) B940367
theorem B1413737 : Blo 626299 1413737 := bstep (se 2 (by rfl) ⟨530151, by rfl⟩ : syracuseStep 1413737 = 1060303) B1060303
theorem B5378723 : Blo 626299 5378723 := bstep (se 1 (by rfl) ⟨4034042, by rfl⟩ : syracuseStep 5378723 = 8068085) B8068085
theorem B627391 : Blo 626299 627391 := bstep (se 1 (by rfl) ⟨470543, by rfl⟩ : syracuseStep 627391 = 941087) B941087
theorem B1413935 : Blo 626299 1413935 := bstep (se 1 (by rfl) ⟨1060451, by rfl⟩ : syracuseStep 1413935 = 2120903) B2120903
theorem B627679 : Blo 626299 627679 := bstep (se 1 (by rfl) ⟨470759, by rfl⟩ : syracuseStep 627679 = 941519) B941519
theorem B3183785 : Blo 626299 3183785 := bstep (se 2 (by rfl) ⟨1193919, by rfl⟩ : syracuseStep 3183785 = 2387839) B2387839
theorem B9082475 : Blo 626299 9082475 := bstep (se 1 (by rfl) ⟨6811856, by rfl⟩ : syracuseStep 9082475 = 13623713) B13623713
theorem B10851985 : Blo 626299 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B3184271 : Blo 626299 3184271 := bstep (se 1 (by rfl) ⟨2388203, by rfl⟩ : syracuseStep 3184271 = 4776407) B4776407
theorem B1513199 : Blo 626299 1513199 := bstep (se 1 (by rfl) ⟨1134899, by rfl⟩ : syracuseStep 1513199 = 2269799) B2269799
theorem B628703 : Blo 626299 628703 := bstep (se 1 (by rfl) ⟨471527, by rfl⟩ : syracuseStep 628703 = 943055) B943055
theorem B628735 : Blo 626299 628735 := bstep (se 1 (by rfl) ⟨471551, by rfl⟩ : syracuseStep 628735 = 943103) B943103
theorem B628783 : Blo 626299 628783 := bstep (se 1 (by rfl) ⟨471587, by rfl⟩ : syracuseStep 628783 = 943175) B943175
theorem B628903 : Blo 626299 628903 := bstep (se 1 (by rfl) ⟨471677, by rfl⟩ : syracuseStep 628903 = 943355) B943355
theorem B20322697 : Blo 626299 20322697 := bstep (se 2 (by rfl) ⟨7621011, by rfl⟩ : syracuseStep 20322697 = 15242023) B15242023
theorem B629247 : Blo 626299 629247 := bstep (se 1 (by rfl) ⟨471935, by rfl⟩ : syracuseStep 629247 = 943871) B943871
theorem B629295 : Blo 626299 629295 := bstep (se 1 (by rfl) ⟨471971, by rfl⟩ : syracuseStep 629295 = 943943) B943943
theorem B1415735 : Blo 626299 1415735 := bstep (se 1 (by rfl) ⟨1061801, by rfl⟩ : syracuseStep 1415735 = 2123603) B2123603
theorem B3054191 : Blo 626299 3054191 := bstep (se 1 (by rfl) ⟨2290643, by rfl⟩ : syracuseStep 3054191 = 4581287) B4581287
theorem B629415 : Blo 626299 629415 := bstep (se 1 (by rfl) ⟨472061, by rfl⟩ : syracuseStep 629415 = 944123) B944123
theorem B629455 : Blo 626299 629455 := bstep (se 1 (by rfl) ⟨472091, by rfl⟩ : syracuseStep 629455 = 944183) B944183
theorem B629535 : Blo 626299 629535 := bstep (se 1 (by rfl) ⟨472151, by rfl⟩ : syracuseStep 629535 = 944303) B944303
theorem B629695 : Blo 626299 629695 := bstep (se 1 (by rfl) ⟨472271, by rfl⟩ : syracuseStep 629695 = 944543) B944543
theorem B629823 : Blo 626299 629823 := bstep (se 1 (by rfl) ⟨472367, by rfl⟩ : syracuseStep 629823 = 944735) B944735
theorem B859243 : Blo 626299 859243 := bstep (se 1 (by rfl) ⟨644432, by rfl⟩ : syracuseStep 859243 = 1288865) B1288865
theorem B629871 : Blo 626299 629871 := bstep (se 1 (by rfl) ⟨472403, by rfl⟩ : syracuseStep 629871 = 944807) B944807
theorem B629915 : Blo 626299 629915 := bstep (se 1 (by rfl) ⟨472436, by rfl⟩ : syracuseStep 629915 = 944873) B944873
theorem B629951 : Blo 626299 629951 := bstep (se 1 (by rfl) ⟨472463, by rfl⟩ : syracuseStep 629951 = 944927) B944927
theorem B630063 : Blo 626299 630063 := bstep (se 1 (by rfl) ⟨472547, by rfl⟩ : syracuseStep 630063 = 945095) B945095
theorem B630143 : Blo 626299 630143 := bstep (se 1 (by rfl) ⟨472607, by rfl⟩ : syracuseStep 630143 = 945215) B945215
theorem B1416671 : Blo 626299 1416671 := bstep (se 1 (by rfl) ⟨1062503, by rfl⟩ : syracuseStep 1416671 = 2125007) B2125007
theorem B630271 : Blo 626299 630271 := bstep (se 1 (by rfl) ⟨472703, by rfl⟩ : syracuseStep 630271 = 945407) B945407
theorem B6790841 : Blo 626299 6790841 := bstep (se 2 (by rfl) ⟨2546565, by rfl⟩ : syracuseStep 6790841 = 5093131) B5093131
theorem B892991 : Blo 626299 892991 := bstep (se 1 (by rfl) ⟨669743, by rfl⟩ : syracuseStep 892991 = 1339487) B1339487
theorem B1417319 : Blo 626299 1417319 := bstep (se 1 (by rfl) ⟨1062989, by rfl⟩ : syracuseStep 1417319 = 2125979) B2125979
theorem B3186863 : Blo 626299 3186863 := bstep (se 1 (by rfl) ⟨2390147, by rfl⟩ : syracuseStep 3186863 = 4780295) B4780295
theorem B10166543 : Blo 626299 10166543 := bstep (se 1 (by rfl) ⟨7624907, by rfl⟩ : syracuseStep 10166543 = 15249815) B15249815
theorem B795035 : Blo 626299 795035 := bstep (se 1 (by rfl) ⟨596276, by rfl⟩ : syracuseStep 795035 = 1192553) B1192553
theorem B5350495 : Blo 626299 5350495 := bstep (se 1 (by rfl) ⟨4012871, by rfl⟩ : syracuseStep 5350495 = 8025743) B8025743
theorem B3187997 : Blo 626299 3187997 := bstep (se 3 (by rfl) ⟨597749, by rfl⟩ : syracuseStep 3187997 = 1195499) B1195499
theorem B1058683 : Blo 626299 1058683 := bstep (se 1 (by rfl) ⟨794012, by rfl⟩ : syracuseStep 1058683 = 1588025) B1588025
theorem B1190207 : Blo 626299 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B3190427 : Blo 626299 3190427 := bstep (se 1 (by rfl) ⟨2392820, by rfl⟩ : syracuseStep 3190427 = 4785641) B4785641
theorem B3387055 : Blo 626299 3387055 := bstep (se 1 (by rfl) ⟨2540291, by rfl⟩ : syracuseStep 3387055 = 5080583) B5080583
theorem B1060735 : Blo 626299 1060735 := bstep (se 1 (by rfl) ⟨795551, by rfl⟩ : syracuseStep 1060735 = 1591103) B1591103
theorem B1061167 : Blo 626299 1061167 := bstep (se 1 (by rfl) ⟨795875, by rfl⟩ : syracuseStep 1061167 = 1591751) B1591751
theorem B1585595 : Blo 626299 1585595 := bstep (se 1 (by rfl) ⟨1189196, by rfl⟩ : syracuseStep 1585595 = 2378393) B2378393
theorem B3585131 : Blo 626299 3585131 := bstep (se 1 (by rfl) ⟨2688848, by rfl⟩ : syracuseStep 3585131 = 5377697) B5377697
theorem B2864339 : Blo 626299 2864339 := bstep (se 1 (by rfl) ⟨2148254, by rfl⟩ : syracuseStep 2864339 = 4296509) B4296509
theorem B1063415 : Blo 626299 1063415 := bstep (se 1 (by rfl) ⟨797561, by rfl⟩ : syracuseStep 1063415 = 1595123) B1595123
theorem B1588207 : Blo 626299 1588207 := bstep (se 1 (by rfl) ⟨1191155, by rfl⟩ : syracuseStep 1588207 = 2382311) B2382311
theorem B12074291 : Blo 626299 12074291 := bstep (se 1 (by rfl) ⟨9055718, by rfl⟩ : syracuseStep 12074291 = 18111437) B18111437
theorem B3620285 : Blo 626299 3620285 := bstep (se 3 (by rfl) ⟨678803, by rfl⟩ : syracuseStep 3620285 = 1357607) B1357607
theorem B1589017 : Blo 626299 1589017 := bstep (se 2 (by rfl) ⟨595881, by rfl⟩ : syracuseStep 1589017 = 1191763) B1191763
theorem B22921127 : Blo 626299 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B6045839 : Blo 626299 6045839 := bstep (se 1 (by rfl) ⟨4534379, by rfl⟩ : syracuseStep 6045839 = 9068759) B9068759
theorem B2114153 : Blo 626299 2114153 := bstep (se 2 (by rfl) ⟨792807, by rfl⟩ : syracuseStep 2114153 = 1585615) B1585615
theorem B11453561 : Blo 626299 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B706207 : Blo 626299 706207 := bstep (se 1 (by rfl) ⟨529655, by rfl⟩ : syracuseStep 706207 = 1059311) B1059311
theorem B1787771 : Blo 626299 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B4540315 : Blo 626299 4540315 := bstep (se 1 (by rfl) ⟨3405236, by rfl⟩ : syracuseStep 4540315 = 6810473) B6810473
theorem B1132499 : Blo 626299 1132499 := bstep (se 1 (by rfl) ⟨849374, by rfl⟩ : syracuseStep 1132499 = 1698749) B1698749
theorem B2115611 : Blo 626299 2115611 := bstep (se 1 (by rfl) ⟨1586708, by rfl⟩ : syracuseStep 2115611 = 3173417) B3173417
theorem B6801479 : Blo 626299 6801479 := bstep (se 1 (by rfl) ⟨5101109, by rfl⟩ : syracuseStep 6801479 = 10202219) B10202219
theorem B1362943 : Blo 626299 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B707791 : Blo 626299 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B1592743 : Blo 626299 1592743 := bstep (se 1 (by rfl) ⟨1194557, by rfl⟩ : syracuseStep 1592743 = 2389115) B2389115
theorem B23842835 : Blo 626299 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B708799 : Blo 626299 708799 := bstep (se 1 (by rfl) ⟨531599, by rfl⟩ : syracuseStep 708799 = 1063199) B1063199
theorem B10867445 : Blo 626299 10867445 := bstep (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) B1018823
theorem B2380535 : Blo 626299 2380535 := bstep (se 1 (by rfl) ⟨1785401, by rfl⟩ : syracuseStep 2380535 = 3570803) B3570803
theorem B1791017 : Blo 626299 1791017 := bstep (se 2 (by rfl) ⟨671631, by rfl⟩ : syracuseStep 1791017 = 1343263) B1343263
theorem B1791143 : Blo 626299 1791143 := bstep (se 1 (by rfl) ⟨1343357, by rfl⟩ : syracuseStep 1791143 = 2686715) B2686715
theorem B2119283 : Blo 626299 2119283 := bstep (se 1 (by rfl) ⟨1589462, by rfl⟩ : syracuseStep 2119283 = 3178925) B3178925
theorem B2381507 : Blo 626299 2381507 := bstep (se 1 (by rfl) ⟨1786130, by rfl⟩ : syracuseStep 2381507 = 3572261) B3572261
theorem B2545789 : Blo 626299 2545789 := bstep (se 3 (by rfl) ⟨477335, by rfl⟩ : syracuseStep 2545789 = 954671) B954671
theorem B3070187 : Blo 626299 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B940343 : Blo 626299 940343 := bstep (se 1 (by rfl) ⟨705257, by rfl⟩ : syracuseStep 940343 = 1410515) B1410515
theorem B940391 : Blo 626299 940391 := bstep (se 1 (by rfl) ⟨705293, by rfl⟩ : syracuseStep 940391 = 1410587) B1410587
theorem B2120417 : Blo 626299 2120417 := bstep (se 2 (by rfl) ⟨795156, by rfl⟩ : syracuseStep 2120417 = 1590313) B1590313
theorem B4774949 : Blo 626299 4774949 := bstep (se 4 (by rfl) ⟨447651, by rfl⟩ : syracuseStep 4774949 = 895303) B895303
theorem B941231 : Blo 626299 941231 := bstep (se 1 (by rfl) ⟨705923, by rfl⟩ : syracuseStep 941231 = 1411847) B1411847
theorem B3398993 : Blo 626299 3398993 := bstep (se 2 (by rfl) ⟨1274622, by rfl⟩ : syracuseStep 3398993 = 2549245) B2549245
theorem B941723 : Blo 626299 941723 := bstep (se 1 (by rfl) ⟨706292, by rfl⟩ : syracuseStep 941723 = 1412585) B1412585
theorem B941759 : Blo 626299 941759 := bstep (se 1 (by rfl) ⟨706319, by rfl⟩ : syracuseStep 941759 = 1412639) B1412639
theorem B1793819 : Blo 626299 1793819 := bstep (se 1 (by rfl) ⟨1345364, by rfl⟩ : syracuseStep 1793819 = 2690729) B2690729
theorem B941915 : Blo 626299 941915 := bstep (se 1 (by rfl) ⟨706436, by rfl⟩ : syracuseStep 941915 = 1412873) B1412873
theorem B941951 : Blo 626299 941951 := bstep (se 1 (by rfl) ⟨706463, by rfl⟩ : syracuseStep 941951 = 1412927) B1412927
theorem B30629825 : Blo 626299 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B46588409 : Blo 626299 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B1434505 : Blo 626299 1434505 := bstep (se 2 (by rfl) ⟨537939, by rfl⟩ : syracuseStep 1434505 = 1075879) B1075879
theorem B943241 : Blo 626299 943241 := bstep (se 2 (by rfl) ⟨353715, by rfl⟩ : syracuseStep 943241 = 707431) B707431
theorem B4711891 : Blo 626299 4711891 := bstep (se 1 (by rfl) ⟨3533918, by rfl⟩ : syracuseStep 4711891 = 7067837) B7067837
theorem B1697561 : Blo 626299 1697561 := bstep (se 2 (by rfl) ⟨636585, by rfl⟩ : syracuseStep 1697561 = 1273171) B1273171
theorem B4777865 : Blo 626299 4777865 := bstep (se 2 (by rfl) ⟨1791699, by rfl⟩ : syracuseStep 4777865 = 3583399) B3583399
theorem B2385895 : Blo 626299 2385895 := bstep (se 1 (by rfl) ⟨1789421, by rfl⟩ : syracuseStep 2385895 = 3578843) B3578843
theorem B6055985 : Blo 626299 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B3533881 : Blo 626299 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B7138367 : Blo 626299 7138367 := bstep (se 1 (by rfl) ⟨5353775, by rfl⟩ : syracuseStep 7138367 = 10707551) B10707551
theorem B4582507 : Blo 626299 4582507 := bstep (se 1 (by rfl) ⟨3436880, by rfl⟩ : syracuseStep 4582507 = 6873761) B6873761
theorem B1338599 : Blo 626299 1338599 := bstep (se 1 (by rfl) ⟨1003949, by rfl⟩ : syracuseStep 1338599 = 2007899) B2007899
theorem B6811685 : Blo 626299 6811685 := bstep (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) B1277191
theorem B6779335 : Blo 626299 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B6451913 : Blo 626299 6451913 := bstep (se 2 (by rfl) ⟨2419467, by rfl⟩ : syracuseStep 6451913 = 4838935) B4838935
theorem B11466983 : Blo 626299 11466983 := bstep (se 1 (by rfl) ⟨8600237, by rfl⟩ : syracuseStep 11466983 = 17200475) B17200475
theorem B1341793 : Blo 626299 1341793 := bstep (se 2 (by rfl) ⟨503172, by rfl⟩ : syracuseStep 1341793 = 1006345) B1006345
theorem B3177143 : Blo 626299 3177143 := bstep (se 1 (by rfl) ⟨2382857, by rfl⟩ : syracuseStep 3177143 = 4765715) B4765715
theorem B4520711 : Blo 626299 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B1342511 : Blo 626299 1342511 := bstep (se 1 (by rfl) ⟨1006883, by rfl⟩ : syracuseStep 1342511 = 2013767) B2013767
theorem B3177791 : Blo 626299 3177791 := bstep (se 1 (by rfl) ⟨2383343, by rfl⟩ : syracuseStep 3177791 = 4766687) B4766687
theorem B49053113 : Blo 626299 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B6029149 : Blo 626299 6029149 := bstep (se 3 (by rfl) ⟨1130465, by rfl⟩ : syracuseStep 6029149 = 2260931) B2260931
theorem B3014729 : Blo 626299 3014729 := bstep (se 2 (by rfl) ⟨1130523, by rfl⟩ : syracuseStep 3014729 = 2261047) B2261047
theorem B4030559 : Blo 626299 4030559 := bstep (se 1 (by rfl) ⟨3022919, by rfl⟩ : syracuseStep 4030559 = 6045839) B6045839
theorem B1409435 : Blo 626299 1409435 := bstep (se 1 (by rfl) ⟨1057076, by rfl⟩ : syracuseStep 1409435 = 2114153) B2114153
theorem B7635707 : Blo 626299 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B1410407 : Blo 626299 1410407 := bstep (se 1 (by rfl) ⟨1057805, by rfl⟩ : syracuseStep 1410407 = 2115611) B2115611
theorem B2688815 : Blo 626299 2688815 := bstep (se 1 (by rfl) ⟨2016611, by rfl⟩ : syracuseStep 2688815 = 4033223) B4033223
theorem B1411577 : Blo 626299 1411577 := bstep (se 2 (by rfl) ⟨529341, by rfl⟩ : syracuseStep 1411577 = 1058683) B1058683
theorem B3181193 : Blo 626299 3181193 := bstep (se 2 (by rfl) ⟨1192947, by rfl⟩ : syracuseStep 3181193 = 2385895) B2385895
theorem B15895223 : Blo 626299 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B7244963 : Blo 626299 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B1412855 : Blo 626299 1412855 := bstep (se 1 (by rfl) ⟨1059641, by rfl⟩ : syracuseStep 1412855 = 2119283) B2119283
theorem B626895 : Blo 626299 626895 := bstep (se 1 (by rfl) ⟨470171, by rfl⟩ : syracuseStep 626895 = 940343) B940343
theorem B626927 : Blo 626299 626927 := bstep (se 1 (by rfl) ⟨470195, by rfl⟩ : syracuseStep 626927 = 940391) B940391
theorem B1413611 : Blo 626299 1413611 := bstep (se 1 (by rfl) ⟨1060208, by rfl⟩ : syracuseStep 1413611 = 2120417) B2120417
theorem B4035197 : Blo 626299 4035197 := bstep (se 3 (by rfl) ⟨756599, by rfl⟩ : syracuseStep 4035197 = 1513199) B1513199
theorem B3183299 : Blo 626299 3183299 := bstep (se 1 (by rfl) ⟨2387474, by rfl⟩ : syracuseStep 3183299 = 4774949) B4774949
theorem B627487 : Blo 626299 627487 := bstep (se 1 (by rfl) ⟨470615, by rfl⟩ : syracuseStep 627487 = 941231) B941231
theorem B2265995 : Blo 626299 2265995 := bstep (se 1 (by rfl) ⟨1699496, by rfl⟩ : syracuseStep 2265995 = 3398993) B3398993
theorem B627815 : Blo 626299 627815 := bstep (se 1 (by rfl) ⟨470861, by rfl⟩ : syracuseStep 627815 = 941723) B941723
theorem B4527227 : Blo 626299 4527227 := bstep (se 1 (by rfl) ⟨3395420, by rfl⟩ : syracuseStep 4527227 = 6790841) B6790841
theorem B627839 : Blo 626299 627839 := bstep (se 1 (by rfl) ⟨470879, by rfl⟩ : syracuseStep 627839 = 941759) B941759
theorem B1414313 : Blo 626299 1414313 := bstep (se 2 (by rfl) ⟨530367, by rfl⟩ : syracuseStep 1414313 = 1060735) B1060735
theorem B3019997 : Blo 626299 3019997 := bstep (se 3 (by rfl) ⟨566249, by rfl⟩ : syracuseStep 3019997 = 1132499) B1132499
theorem B627943 : Blo 626299 627943 := bstep (se 1 (by rfl) ⟨470957, by rfl⟩ : syracuseStep 627943 = 941915) B941915
theorem B627967 : Blo 626299 627967 := bstep (se 1 (by rfl) ⟨470975, by rfl⟩ : syracuseStep 627967 = 941951) B941951
theorem B20419883 : Blo 626299 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B1414889 : Blo 626299 1414889 := bstep (se 2 (by rfl) ⟨530583, by rfl⟩ : syracuseStep 1414889 = 1061167) B1061167
theorem B628827 : Blo 626299 628827 := bstep (se 1 (by rfl) ⟨471620, by rfl⟩ : syracuseStep 628827 = 943241) B943241
theorem B3185243 : Blo 626299 3185243 := bstep (se 1 (by rfl) ⟨2388932, by rfl⟩ : syracuseStep 3185243 = 4777865) B4777865
theorem B4037323 : Blo 626299 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B793471 : Blo 626299 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B4758911 : Blo 626299 4758911 := bstep (se 1 (by rfl) ⟨3569183, by rfl⟩ : syracuseStep 4758911 = 7138367) B7138367
theorem B892399 : Blo 626299 892399 := bstep (se 1 (by rfl) ⟨669299, by rfl⟩ : syracuseStep 892399 = 1338599) B1338599
theorem B1057063 : Blo 626299 1057063 := bstep (se 1 (by rfl) ⟨792797, by rfl⟩ : syracuseStep 1057063 = 1585595) B1585595
theorem B4301275 : Blo 626299 4301275 := bstep (se 1 (by rfl) ⟨3225956, by rfl⟩ : syracuseStep 4301275 = 6451913) B6451913
theorem B1909559 : Blo 626299 1909559 := bstep (se 1 (by rfl) ⟨1432169, by rfl⟩ : syracuseStep 1909559 = 2864339) B2864339
theorem B7644655 : Blo 626299 7644655 := bstep (se 1 (by rfl) ⟨5733491, by rfl⟩ : syracuseStep 7644655 = 11466983) B11466983
theorem B895007 : Blo 626299 895007 := bstep (se 1 (by rfl) ⟨671255, by rfl⟩ : syracuseStep 895007 = 1342511) B1342511
theorem B8038865 : Blo 626299 8038865 := bstep (se 2 (by rfl) ⟨3014574, by rfl⟩ : syracuseStep 8038865 = 6029149) B6029149
theorem B15280751 : Blo 626299 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B1912673 : Blo 626299 1912673 := bstep (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) B1434505
theorem B1191847 : Blo 626299 1191847 := bstep (se 1 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 1191847 = 1787771) B1787771
theorem B4534319 : Blo 626299 4534319 := bstep (se 1 (by rfl) ⟨3400739, by rfl⟩ : syracuseStep 4534319 = 6801479) B6801479
theorem B3585815 : Blo 626299 3585815 := bstep (se 1 (by rfl) ⟨2689361, by rfl⟩ : syracuseStep 3585815 = 5378723) B5378723
theorem B1587023 : Blo 626299 1587023 := bstep (se 1 (by rfl) ⟨1190267, by rfl⟩ : syracuseStep 1587023 = 2380535) B2380535
theorem B1194011 : Blo 626299 1194011 := bstep (se 1 (by rfl) ⟨895508, by rfl⟩ : syracuseStep 1194011 = 1791017) B1791017
theorem B1194095 : Blo 626299 1194095 := bstep (se 1 (by rfl) ⟨895571, by rfl⟩ : syracuseStep 1194095 = 1791143) B1791143
theorem B1587671 : Blo 626299 1587671 := bstep (se 1 (by rfl) ⟨1190753, by rfl⟩ : syracuseStep 1587671 = 2381507) B2381507
theorem B1817257 : Blo 626299 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B6110009 : Blo 626299 6110009 := bstep (se 2 (by rfl) ⟨2291253, by rfl⟩ : syracuseStep 6110009 = 4582507) B4582507
theorem B2046791 : Blo 626299 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B1195879 : Blo 626299 1195879 := bstep (se 1 (by rfl) ⟨896909, by rfl⟩ : syracuseStep 1195879 = 1793819) B1793819
theorem B1131707 : Blo 626299 1131707 := bstep (se 1 (by rfl) ⟨848780, by rfl⟩ : syracuseStep 1131707 = 1697561) B1697561
theorem B8144509 : Blo 626299 8144509 := bstep (se 3 (by rfl) ⟨1527095, by rfl⟩ : syracuseStep 8144509 = 3054191) B3054191
theorem B14469313 : Blo 626299 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B4541123 : Blo 626299 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B3394385 : Blo 626299 3394385 := bstep (se 2 (by rfl) ⟨1272894, by rfl⟩ : syracuseStep 3394385 = 2545789) B2545789
theorem B1789057 : Blo 626299 1789057 := bstep (se 2 (by rfl) ⟨670896, by rfl⟩ : syracuseStep 1789057 = 1341793) B1341793
theorem B2117609 : Blo 626299 2117609 := bstep (se 2 (by rfl) ⟨794103, by rfl⟩ : syracuseStep 2117609 = 1588207) B1588207
theorem B708943 : Blo 626299 708943 := bstep (se 1 (by rfl) ⟨531707, by rfl⟩ : syracuseStep 708943 = 1063415) B1063415
theorem B2118095 : Blo 626299 2118095 := bstep (se 1 (by rfl) ⟨1588571, by rfl⟩ : syracuseStep 2118095 = 3177143) B3177143
theorem B8049527 : Blo 626299 8049527 := bstep (se 1 (by rfl) ⟨6037145, by rfl⟩ : syracuseStep 8049527 = 12074291) B12074291
theorem B2118527 : Blo 626299 2118527 := bstep (se 1 (by rfl) ⟨1588895, by rfl⟩ : syracuseStep 2118527 = 3177791) B3177791
theorem B2413523 : Blo 626299 2413523 := bstep (se 1 (by rfl) ⟨1810142, by rfl⟩ : syracuseStep 2413523 = 3620285) B3620285
theorem B2118689 : Blo 626299 2118689 := bstep (se 2 (by rfl) ⟨794508, by rfl⟩ : syracuseStep 2118689 = 1589017) B1589017
theorem B2381309 : Blo 626299 2381309 := bstep (se 3 (by rfl) ⟨446495, by rfl⟩ : syracuseStep 2381309 = 892991) B892991
theorem B939647 : Blo 626299 939647 := bstep (se 1 (by rfl) ⟨704735, by rfl⟩ : syracuseStep 939647 = 1409471) B1409471
theorem B12080987 : Blo 626299 12080987 := bstep (se 1 (by rfl) ⟨9060740, by rfl⟩ : syracuseStep 12080987 = 18121481) B18121481
theorem B1595335 : Blo 626299 1595335 := bstep (se 1 (by rfl) ⟨1196501, by rfl⟩ : syracuseStep 1595335 = 2393003) B2393003
theorem B2120093 : Blo 626299 2120093 := bstep (se 3 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 2120093 = 795035) B795035
theorem B7133993 : Blo 626299 7133993 := bstep (se 2 (by rfl) ⟨2675247, by rfl⟩ : syracuseStep 7133993 = 5350495) B5350495
theorem B12409805 : Blo 626299 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B941111 : Blo 626299 941111 := bstep (se 1 (by rfl) ⟨705833, by rfl⟩ : syracuseStep 941111 = 1411667) B1411667
theorem B941291 : Blo 626299 941291 := bstep (se 1 (by rfl) ⟨705968, by rfl⟩ : syracuseStep 941291 = 1411937) B1411937
theorem B6282521 : Blo 626299 6282521 := bstep (se 2 (by rfl) ⟨2355945, by rfl⟩ : syracuseStep 6282521 = 4711891) B4711891
theorem B941609 : Blo 626299 941609 := bstep (se 2 (by rfl) ⟨353103, by rfl⟩ : syracuseStep 941609 = 706207) B706207
theorem B1007159 : Blo 626299 1007159 := bstep (se 1 (by rfl) ⟨755369, by rfl⟩ : syracuseStep 1007159 = 1510739) B1510739
theorem B2121551 : Blo 626299 2121551 := bstep (se 1 (by rfl) ⟨1591163, by rfl⟩ : syracuseStep 2121551 = 3182327) B3182327
theorem B6053753 : Blo 626299 6053753 := bstep (se 2 (by rfl) ⟨2270157, by rfl⟩ : syracuseStep 6053753 = 4540315) B4540315
theorem B942059 : Blo 626299 942059 := bstep (se 1 (by rfl) ⟨706544, by rfl⟩ : syracuseStep 942059 = 1413089) B1413089
theorem B1073279 : Blo 626299 1073279 := bstep (se 1 (by rfl) ⟨804959, by rfl⟩ : syracuseStep 1073279 = 1609919) B1609919
theorem B942491 : Blo 626299 942491 := bstep (se 1 (by rfl) ⟨706868, by rfl⟩ : syracuseStep 942491 = 1413737) B1413737
theorem B942623 : Blo 626299 942623 := bstep (se 1 (by rfl) ⟨706967, by rfl⟩ : syracuseStep 942623 = 1413935) B1413935
theorem B2122523 : Blo 626299 2122523 := bstep (se 1 (by rfl) ⟨1591892, by rfl⟩ : syracuseStep 2122523 = 3183785) B3183785
theorem B6054983 : Blo 626299 6054983 := bstep (se 1 (by rfl) ⟨4541237, by rfl⟩ : syracuseStep 6054983 = 9082475) B9082475
theorem B2122847 : Blo 626299 2122847 := bstep (se 1 (by rfl) ⟨1592135, by rfl⟩ : syracuseStep 2122847 = 3184271) B3184271
theorem B4711841 : Blo 626299 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B943721 : Blo 626299 943721 := bstep (se 2 (by rfl) ⟨353895, by rfl⟩ : syracuseStep 943721 = 707791) B707791
theorem B943823 : Blo 626299 943823 := bstep (se 1 (by rfl) ⟨707867, by rfl⟩ : syracuseStep 943823 = 1415735) B1415735
theorem B2123657 : Blo 626299 2123657 := bstep (se 2 (by rfl) ⟨796371, by rfl⟩ : syracuseStep 2123657 = 1592743) B1592743
theorem B4516073 : Blo 626299 4516073 := bstep (se 2 (by rfl) ⟨1693527, by rfl⟩ : syracuseStep 4516073 = 3387055) B3387055
theorem B944447 : Blo 626299 944447 := bstep (se 1 (by rfl) ⟨708335, by rfl⟩ : syracuseStep 944447 = 1416671) B1416671
theorem B944879 : Blo 626299 944879 := bstep (se 1 (by rfl) ⟨708659, by rfl⟩ : syracuseStep 944879 = 1417319) B1417319
theorem B2124575 : Blo 626299 2124575 := bstep (se 1 (by rfl) ⟨1593431, by rfl⟩ : syracuseStep 2124575 = 3186863) B3186863
theorem B6777695 : Blo 626299 6777695 := bstep (se 1 (by rfl) ⟨5083271, by rfl⟩ : syracuseStep 6777695 = 10166543) B10166543
theorem B945065 : Blo 626299 945065 := bstep (se 2 (by rfl) ⟨354399, by rfl⟩ : syracuseStep 945065 = 708799) B708799
theorem B31058939 : Blo 626299 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B9039113 : Blo 626299 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B2125331 : Blo 626299 2125331 := bstep (se 1 (by rfl) ⟨1593998, by rfl⟩ : syracuseStep 2125331 = 3187997) B3187997
theorem B2126951 : Blo 626299 2126951 := bstep (se 1 (by rfl) ⟨1595213, by rfl⟩ : syracuseStep 2126951 = 3190427) B3190427
theorem B27096929 : Blo 626299 27096929 := bstep (se 2 (by rfl) ⟨10161348, by rfl⟩ : syracuseStep 27096929 = 20322697) B20322697
theorem B2390087 : Blo 626299 2390087 := bstep (se 1 (by rfl) ⟨1792565, by rfl⟩ : syracuseStep 2390087 = 3585131) B3585131
theorem B1145657 : Blo 626299 1145657 := bstep (se 2 (by rfl) ⟨429621, by rfl⟩ : syracuseStep 1145657 = 859243) B859243
theorem B3013807 : Blo 626299 3013807 := bstep (se 1 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 3013807 = 4520711) B4520711
theorem B32702075 : Blo 626299 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B2687039 : Blo 626299 2687039 := bstep (se 1 (by rfl) ⟨2015279, by rfl⟩ : syracuseStep 2687039 = 4030559) B4030559
theorem B1409417 : Blo 626299 1409417 := bstep (se 2 (by rfl) ⟨528531, by rfl⟩ : syracuseStep 1409417 = 1057063) B1057063
theorem B5735033 : Blo 626299 5735033 := bstep (se 2 (by rfl) ⟨2150637, by rfl⟩ : syracuseStep 5735033 = 4301275) B4301275
theorem B754471 : Blo 626299 754471 := bstep (se 1 (by rfl) ⟨565853, by rfl⟩ : syracuseStep 754471 = 1131707) B1131707
theorem B2262923 : Blo 626299 2262923 := bstep (se 1 (by rfl) ⟨1697192, by rfl⟩ : syracuseStep 2262923 = 3394385) B3394385
theorem B10192873 : Blo 626299 10192873 := bstep (se 2 (by rfl) ⟨3822327, by rfl⟩ : syracuseStep 10192873 = 7644655) B7644655
theorem B1411739 : Blo 626299 1411739 := bstep (se 1 (by rfl) ⟨1058804, by rfl⟩ : syracuseStep 1411739 = 2117609) B2117609
theorem B1412063 : Blo 626299 1412063 := bstep (se 1 (by rfl) ⟨1059047, by rfl⟩ : syracuseStep 1412063 = 2118095) B2118095
theorem B2690131 : Blo 626299 2690131 := bstep (se 1 (by rfl) ⟨2017598, by rfl⟩ : syracuseStep 2690131 = 4035197) B4035197
theorem B1412351 : Blo 626299 1412351 := bstep (se 1 (by rfl) ⟨1059263, by rfl⟩ : syracuseStep 1412351 = 2118527) B2118527
theorem B1510663 : Blo 626299 1510663 := bstep (se 1 (by rfl) ⟨1132997, by rfl⟩ : syracuseStep 1510663 = 2265995) B2265995
theorem B1412459 : Blo 626299 1412459 := bstep (se 1 (by rfl) ⟨1059344, by rfl⟩ : syracuseStep 1412459 = 2118689) B2118689
theorem B3018151 : Blo 626299 3018151 := bstep (se 1 (by rfl) ⟨2263613, by rfl⟩ : syracuseStep 3018151 = 4527227) B4527227
theorem B626431 : Blo 626299 626431 := bstep (se 1 (by rfl) ⟨469823, by rfl⟩ : syracuseStep 626431 = 939647) B939647
theorem B1413395 : Blo 626299 1413395 := bstep (se 1 (by rfl) ⟨1060046, by rfl⟩ : syracuseStep 1413395 = 2120093) B2120093
theorem B4755995 : Blo 626299 4755995 := bstep (se 1 (by rfl) ⟨3566996, by rfl⟩ : syracuseStep 4755995 = 7133993) B7133993
theorem B627407 : Blo 626299 627407 := bstep (se 1 (by rfl) ⟨470555, by rfl⟩ : syracuseStep 627407 = 941111) B941111
theorem B627527 : Blo 626299 627527 := bstep (se 1 (by rfl) ⟨470645, by rfl⟩ : syracuseStep 627527 = 941291) B941291
theorem B627739 : Blo 626299 627739 := bstep (se 1 (by rfl) ⟨470804, by rfl⟩ : syracuseStep 627739 = 941609) B941609
theorem B1414367 : Blo 626299 1414367 := bstep (se 1 (by rfl) ⟨1060775, by rfl⟩ : syracuseStep 1414367 = 2121551) B2121551
theorem B4035835 : Blo 626299 4035835 := bstep (se 1 (by rfl) ⟨3026876, by rfl⟩ : syracuseStep 4035835 = 6053753) B6053753
theorem B628039 : Blo 626299 628039 := bstep (se 1 (by rfl) ⟨471029, by rfl⟩ : syracuseStep 628039 = 942059) B942059
theorem B628327 : Blo 626299 628327 := bstep (se 1 (by rfl) ⟨471245, by rfl⟩ : syracuseStep 628327 = 942491) B942491
theorem B628415 : Blo 626299 628415 := bstep (se 1 (by rfl) ⟨471311, by rfl⟩ : syracuseStep 628415 = 942623) B942623
theorem B1415015 : Blo 626299 1415015 := bstep (se 1 (by rfl) ⟨1061261, by rfl⟩ : syracuseStep 1415015 = 2122523) B2122523
theorem B4036655 : Blo 626299 4036655 := bstep (se 1 (by rfl) ⟨3027491, by rfl⟩ : syracuseStep 4036655 = 6054983) B6054983
theorem B1415231 : Blo 626299 1415231 := bstep (se 1 (by rfl) ⟨1061423, by rfl⟩ : syracuseStep 1415231 = 2122847) B2122847
theorem B629147 : Blo 626299 629147 := bstep (se 1 (by rfl) ⟨471860, by rfl⟩ : syracuseStep 629147 = 943721) B943721
theorem B629215 : Blo 626299 629215 := bstep (se 1 (by rfl) ⟨471911, by rfl⟩ : syracuseStep 629215 = 943823) B943823
theorem B1415771 : Blo 626299 1415771 := bstep (se 1 (by rfl) ⟨1061828, by rfl⟩ : syracuseStep 1415771 = 2123657) B2123657
theorem B629631 : Blo 626299 629631 := bstep (se 1 (by rfl) ⟨472223, by rfl⟩ : syracuseStep 629631 = 944447) B944447
theorem B629919 : Blo 626299 629919 := bstep (se 1 (by rfl) ⟨472439, by rfl⟩ : syracuseStep 629919 = 944879) B944879
theorem B1416383 : Blo 626299 1416383 := bstep (se 1 (by rfl) ⟨1062287, by rfl⟩ : syracuseStep 1416383 = 2124575) B2124575
theorem B630043 : Blo 626299 630043 := bstep (se 1 (by rfl) ⟨472532, by rfl⟩ : syracuseStep 630043 = 945065) B945065
theorem B1416887 : Blo 626299 1416887 := bstep (se 1 (by rfl) ⟨1062665, by rfl⟩ : syracuseStep 1416887 = 2125331) B2125331
theorem B3022879 : Blo 626299 3022879 := bstep (se 1 (by rfl) ⟨2267159, by rfl⟩ : syracuseStep 3022879 = 4534319) B4534319
theorem B1417967 : Blo 626299 1417967 := bstep (se 1 (by rfl) ⟨1063475, by rfl⟩ : syracuseStep 1417967 = 2126951) B2126951
theorem B5383097 : Blo 626299 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B1057961 : Blo 626299 1057961 := bstep (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) B793471
theorem B1058015 : Blo 626299 1058015 := bstep (se 1 (by rfl) ⟨793511, by rfl⟩ : syracuseStep 1058015 = 1587023) B1587023
theorem B18064619 : Blo 626299 18064619 := bstep (se 1 (by rfl) ⟨13548464, by rfl⟩ : syracuseStep 18064619 = 27096929) B27096929
theorem B796007 : Blo 626299 796007 := bstep (se 1 (by rfl) ⟨597005, by rfl⟩ : syracuseStep 796007 = 1194011) B1194011
theorem B796063 : Blo 626299 796063 := bstep (se 1 (by rfl) ⟨597047, by rfl⟩ : syracuseStep 796063 = 1194095) B1194095
theorem B1058447 : Blo 626299 1058447 := bstep (se 1 (by rfl) ⟨793835, by rfl⟩ : syracuseStep 1058447 = 1587671) B1587671
theorem B4073339 : Blo 626299 4073339 := bstep (se 1 (by rfl) ⟨3055004, by rfl⟩ : syracuseStep 4073339 = 6110009) B6110009
theorem B763771 : Blo 626299 763771 := bstep (se 1 (by rfl) ⟨572828, by rfl⟩ : syracuseStep 763771 = 1145657) B1145657
theorem B1189865 : Blo 626299 1189865 := bstep (se 2 (by rfl) ⟨446199, by rfl⟩ : syracuseStep 1189865 = 892399) B892399
theorem B21801383 : Blo 626299 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B2009819 : Blo 626299 2009819 := bstep (se 1 (by rfl) ⟨1507364, by rfl⟩ : syracuseStep 2009819 = 3014729) B3014729
theorem B5090471 : Blo 626299 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B10596815 : Blo 626299 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B4829975 : Blo 626299 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B10859345 : Blo 626299 10859345 := bstep (se 2 (by rfl) ⟨4072254, by rfl⟩ : syracuseStep 10859345 = 8144509) B8144509
theorem B6436061 : Blo 626299 6436061 := bstep (se 3 (by rfl) ⟨1206761, by rfl⟩ : syracuseStep 6436061 = 2413523) B2413523
theorem B2013331 : Blo 626299 2013331 := bstep (se 1 (by rfl) ⟨1509998, by rfl⟩ : syracuseStep 2013331 = 3019997) B3019997
theorem B13613255 : Blo 626299 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B1587539 : Blo 626299 1587539 := bstep (se 1 (by rfl) ⟨1190654, by rfl⟩ : syracuseStep 1587539 = 2381309) B2381309
theorem B1589129 : Blo 626299 1589129 := bstep (se 2 (by rfl) ⟨595923, by rfl⟩ : syracuseStep 1589129 = 1191847) B1191847
theorem B5359243 : Blo 626299 5359243 := bstep (se 1 (by rfl) ⟨4019432, by rfl⟩ : syracuseStep 5359243 = 8038865) B8038865
theorem B12109661 : Blo 626299 12109661 := bstep (se 3 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 12109661 = 4541123) B4541123
theorem B1593391 : Blo 626299 1593391 := bstep (se 1 (by rfl) ⟨1195043, by rfl⟩ : syracuseStep 1593391 = 2390087) B2390087
theorem B4018409 : Blo 626299 4018409 := bstep (se 2 (by rfl) ⟨1506903, by rfl⟩ : syracuseStep 4018409 = 3013807) B3013807
theorem B1364527 : Blo 626299 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B5100461 : Blo 626299 5100461 := bstep (se 3 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 5100461 = 1912673) B1912673
theorem B1594505 : Blo 626299 1594505 := bstep (se 2 (by rfl) ⟨597939, by rfl⟩ : syracuseStep 1594505 = 1195879) B1195879
theorem B939623 : Blo 626299 939623 := bstep (se 1 (by rfl) ⟨704717, by rfl⟩ : syracuseStep 939623 = 1409435) B1409435
theorem B940271 : Blo 626299 940271 := bstep (se 1 (by rfl) ⟨705203, by rfl⟩ : syracuseStep 940271 = 1410407) B1410407
theorem B1792543 : Blo 626299 1792543 := bstep (se 1 (by rfl) ⟨1344407, by rfl⟩ : syracuseStep 1792543 = 2688815) B2688815
theorem B941051 : Blo 626299 941051 := bstep (se 1 (by rfl) ⟨705788, by rfl⟩ : syracuseStep 941051 = 1411577) B1411577
theorem B2120795 : Blo 626299 2120795 := bstep (se 1 (by rfl) ⟨1590596, by rfl⟩ : syracuseStep 2120795 = 3181193) B3181193
theorem B941903 : Blo 626299 941903 := bstep (se 1 (by rfl) ⟨706427, by rfl⟩ : syracuseStep 941903 = 1412855) B1412855
theorem B19292417 : Blo 626299 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B942407 : Blo 626299 942407 := bstep (se 1 (by rfl) ⟨706805, by rfl⟩ : syracuseStep 942407 = 1413611) B1413611
theorem B2122199 : Blo 626299 2122199 := bstep (se 1 (by rfl) ⟨1591649, by rfl⟩ : syracuseStep 2122199 = 3183299) B3183299
theorem B5366351 : Blo 626299 5366351 := bstep (se 1 (by rfl) ⟨4024763, by rfl⟩ : syracuseStep 5366351 = 8049527) B8049527
theorem B942875 : Blo 626299 942875 := bstep (se 1 (by rfl) ⟨707156, by rfl⟩ : syracuseStep 942875 = 1414313) B1414313
theorem B943259 : Blo 626299 943259 := bstep (se 1 (by rfl) ⟨707444, by rfl⟩ : syracuseStep 943259 = 1414889) B1414889
theorem B8053991 : Blo 626299 8053991 := bstep (se 1 (by rfl) ⟨6040493, by rfl⟩ : syracuseStep 8053991 = 12080987) B12080987
theorem B2385409 : Blo 626299 2385409 := bstep (se 2 (by rfl) ⟨894528, by rfl⟩ : syracuseStep 2385409 = 1789057) B1789057
theorem B2123495 : Blo 626299 2123495 := bstep (se 1 (by rfl) ⟨1592621, by rfl⟩ : syracuseStep 2123495 = 3185243) B3185243
theorem B4188347 : Blo 626299 4188347 := bstep (se 1 (by rfl) ⟨3141260, by rfl⟩ : syracuseStep 4188347 = 6282521) B6282521
theorem B3172607 : Blo 626299 3172607 := bstep (se 1 (by rfl) ⟨2379455, by rfl⟩ : syracuseStep 3172607 = 4758911) B4758911
theorem B2386685 : Blo 626299 2386685 := bstep (se 3 (by rfl) ⟨447503, by rfl⟩ : syracuseStep 2386685 = 895007) B895007
theorem B715519 : Blo 626299 715519 := bstep (se 1 (by rfl) ⟨536639, by rfl⟩ : syracuseStep 715519 = 1073279) B1073279
theorem B945257 : Blo 626299 945257 := bstep (se 2 (by rfl) ⟨354471, by rfl⟩ : syracuseStep 945257 = 708943) B708943
theorem B1273039 : Blo 626299 1273039 := bstep (se 1 (by rfl) ⟨954779, by rfl⟩ : syracuseStep 1273039 = 1909559) B1909559
theorem B3141227 : Blo 626299 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B3010715 : Blo 626299 3010715 := bstep (se 1 (by rfl) ⟨2258036, by rfl⟩ : syracuseStep 3010715 = 4516073) B4516073
theorem B10187167 : Blo 626299 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B4518463 : Blo 626299 4518463 := bstep (se 1 (by rfl) ⟨3388847, by rfl⟩ : syracuseStep 4518463 = 6777695) B6777695
theorem B20705959 : Blo 626299 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B6026075 : Blo 626299 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B33092813 : Blo 626299 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B2127113 : Blo 626299 2127113 := bstep (se 2 (by rfl) ⟨797667, by rfl⟩ : syracuseStep 2127113 = 1595335) B1595335
theorem B2423009 : Blo 626299 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B2390543 : Blo 626299 2390543 := bstep (se 1 (by rfl) ⟨1792907, by rfl⟩ : syracuseStep 2390543 = 3585815) B3585815
theorem B2685757 : Blo 626299 2685757 := bstep (se 3 (by rfl) ⟨503579, by rfl⟩ : syracuseStep 2685757 = 1007159) B1007159
theorem B4030505 : Blo 626299 4030505 := bstep (se 2 (by rfl) ⟨1511439, by rfl⟩ : syracuseStep 4030505 = 3022879) B3022879
theorem B1508615 : Blo 626299 1508615 := bstep (se 1 (by rfl) ⟨1131461, by rfl⟩ : syracuseStep 1508615 = 2262923) B2262923
theorem B3180545 : Blo 626299 3180545 := bstep (se 2 (by rfl) ⟨1192704, by rfl⟩ : syracuseStep 3180545 = 2385409) B2385409
theorem B7145657 : Blo 626299 7145657 := bstep (se 2 (by rfl) ⟨2679621, by rfl⟩ : syracuseStep 7145657 = 5359243) B5359243
theorem B1018361 : Blo 626299 1018361 := bstep (se 2 (by rfl) ⟨381885, by rfl⟩ : syracuseStep 1018361 = 763771) B763771
theorem B88247501 : Blo 626299 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B954025 : Blo 626299 954025 := bstep (se 2 (by rfl) ⟨357759, by rfl⟩ : syracuseStep 954025 = 715519) B715519
theorem B626415 : Blo 626299 626415 := bstep (se 1 (by rfl) ⟨469811, by rfl⟩ : syracuseStep 626415 = 939623) B939623
theorem B626847 : Blo 626299 626847 := bstep (se 1 (by rfl) ⟨470135, by rfl⟩ : syracuseStep 626847 = 940271) B940271
theorem B627367 : Blo 626299 627367 := bstep (se 1 (by rfl) ⟨470525, by rfl⟩ : syracuseStep 627367 = 941051) B941051
theorem B1413863 : Blo 626299 1413863 := bstep (se 1 (by rfl) ⟨1060397, by rfl⟩ : syracuseStep 1413863 = 2120795) B2120795
theorem B627935 : Blo 626299 627935 := bstep (se 1 (by rfl) ⟨470951, by rfl⟩ : syracuseStep 627935 = 941903) B941903
theorem B628271 : Blo 626299 628271 := bstep (se 1 (by rfl) ⟨471203, by rfl⟩ : syracuseStep 628271 = 942407) B942407
theorem B1414799 : Blo 626299 1414799 := bstep (se 1 (by rfl) ⟨1061099, by rfl⟩ : syracuseStep 1414799 = 2122199) B2122199
theorem B3577567 : Blo 626299 3577567 := bstep (se 1 (by rfl) ⟨2683175, by rfl⟩ : syracuseStep 3577567 = 5366351) B5366351
theorem B628583 : Blo 626299 628583 := bstep (se 1 (by rfl) ⟨471437, by rfl⟩ : syracuseStep 628583 = 942875) B942875
theorem B628839 : Blo 626299 628839 := bstep (se 1 (by rfl) ⟨471629, by rfl⟩ : syracuseStep 628839 = 943259) B943259
theorem B1415663 : Blo 626299 1415663 := bstep (se 1 (by rfl) ⟨1061747, by rfl⟩ : syracuseStep 1415663 = 2123495) B2123495
theorem B793243 : Blo 626299 793243 := bstep (se 1 (by rfl) ⟨594932, by rfl⟩ : syracuseStep 793243 = 1189865) B1189865
theorem B2792231 : Blo 626299 2792231 := bstep (se 1 (by rfl) ⟨2094173, by rfl⟩ : syracuseStep 2792231 = 4188347) B4188347
theorem B5381113 : Blo 626299 5381113 := bstep (se 2 (by rfl) ⟨2017917, by rfl⟩ : syracuseStep 5381113 = 4035835) B4035835
theorem B630171 : Blo 626299 630171 := bstep (se 1 (by rfl) ⟨472628, by rfl⟩ : syracuseStep 630171 = 945257) B945257
theorem B2007143 : Blo 626299 2007143 := bstep (se 1 (by rfl) ⟨1505357, by rfl⟩ : syracuseStep 2007143 = 3010715) B3010715
theorem B3219983 : Blo 626299 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B1418075 : Blo 626299 1418075 := bstep (se 1 (by rfl) ⟨1063556, by rfl⟩ : syracuseStep 1418075 = 2127113) B2127113
theorem B3581009 : Blo 626299 3581009 := bstep (se 2 (by rfl) ⟨1342878, by rfl⟩ : syracuseStep 3581009 = 2685757) B2685757
theorem B1615339 : Blo 626299 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B1058359 : Blo 626299 1058359 := bstep (se 1 (by rfl) ⟨793769, by rfl⟩ : syracuseStep 1058359 = 1587539) B1587539
theorem B1059419 : Blo 626299 1059419 := bstep (se 1 (by rfl) ⟨794564, by rfl⟩ : syracuseStep 1059419 = 1589129) B1589129
theorem B8073107 : Blo 626299 8073107 := bstep (se 1 (by rfl) ⟨6054830, by rfl⟩ : syracuseStep 8073107 = 12109661) B12109661
theorem B1061417 : Blo 626299 1061417 := bstep (se 2 (by rfl) ⟨398031, by rfl⟩ : syracuseStep 1061417 = 796063) B796063
theorem B1063003 : Blo 626299 1063003 := bstep (se 1 (by rfl) ⟨797252, by rfl⟩ : syracuseStep 1063003 = 1594505) B1594505
theorem B3586841 : Blo 626299 3586841 := bstep (se 2 (by rfl) ⟨1345065, by rfl⟩ : syracuseStep 3586841 = 2690131) B2690131
theorem B2014217 : Blo 626299 2014217 := bstep (se 2 (by rfl) ⟨755331, by rfl⟩ : syracuseStep 2014217 = 1510663) B1510663
theorem B10862237 : Blo 626299 10862237 := bstep (se 3 (by rfl) ⟨2036669, by rfl⟩ : syracuseStep 10862237 = 4073339) B4073339
theorem B10764413 : Blo 626299 10764413 := bstep (se 3 (by rfl) ⟨2018327, by rfl⟩ : syracuseStep 10764413 = 4036655) B4036655
theorem B12861611 : Blo 626299 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B13582889 : Blo 626299 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B3588731 : Blo 626299 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B1819369 : Blo 626299 1819369 := bstep (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) B1364527
theorem B705307 : Blo 626299 705307 := bstep (se 1 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 705307 = 1057961) B1057961
theorem B705343 : Blo 626299 705343 := bstep (se 1 (by rfl) ⟨529007, by rfl⟩ : syracuseStep 705343 = 1058015) B1058015
theorem B12043079 : Blo 626299 12043079 := bstep (se 1 (by rfl) ⟨9032309, by rfl⟩ : syracuseStep 12043079 = 18064619) B18064619
theorem B27607945 : Blo 626299 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B705631 : Blo 626299 705631 := bstep (se 1 (by rfl) ⟨529223, by rfl⟩ : syracuseStep 705631 = 1058447) B1058447
theorem B2115071 : Blo 626299 2115071 := bstep (se 1 (by rfl) ⟨1586303, by rfl⟩ : syracuseStep 2115071 = 3172607) B3172607
theorem B14534255 : Blo 626299 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B1591123 : Blo 626299 1591123 := bstep (se 1 (by rfl) ⟨1193342, by rfl⟩ : syracuseStep 1591123 = 2386685) B2386685
theorem B5359517 : Blo 626299 5359517 := bstep (se 3 (by rfl) ⟨1004909, by rfl⟩ : syracuseStep 5359517 = 2009819) B2009819
theorem B3393647 : Blo 626299 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B7064543 : Blo 626299 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B4017383 : Blo 626299 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B8376605 : Blo 626299 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B1593695 : Blo 626299 1593695 := bstep (se 1 (by rfl) ⟨1195271, by rfl⟩ : syracuseStep 1593695 = 2390543) B2390543
theorem B1791359 : Blo 626299 1791359 := bstep (se 1 (by rfl) ⟨1343519, by rfl⟩ : syracuseStep 1791359 = 2687039) B2687039
theorem B939611 : Blo 626299 939611 := bstep (se 1 (by rfl) ⟨704708, by rfl⟩ : syracuseStep 939611 = 1409417) B1409417
theorem B3823355 : Blo 626299 3823355 := bstep (se 1 (by rfl) ⟨2867516, by rfl⟩ : syracuseStep 3823355 = 5735033) B5735033
theorem B1005961 : Blo 626299 1005961 := bstep (se 2 (by rfl) ⟨377235, by rfl⟩ : syracuseStep 1005961 = 754471) B754471
theorem B941159 : Blo 626299 941159 := bstep (se 1 (by rfl) ⟨705869, by rfl⟩ : syracuseStep 941159 = 1411739) B1411739
theorem B941375 : Blo 626299 941375 := bstep (se 1 (by rfl) ⟨706031, by rfl⟩ : syracuseStep 941375 = 1412063) B1412063
theorem B941567 : Blo 626299 941567 := bstep (se 1 (by rfl) ⟨706175, by rfl⟩ : syracuseStep 941567 = 1412351) B1412351
theorem B941639 : Blo 626299 941639 := bstep (se 1 (by rfl) ⟨706229, by rfl⟩ : syracuseStep 941639 = 1412459) B1412459
theorem B13590497 : Blo 626299 13590497 := bstep (se 2 (by rfl) ⟨5096436, by rfl⟩ : syracuseStep 13590497 = 10192873) B10192873
theorem B2678939 : Blo 626299 2678939 := bstep (se 1 (by rfl) ⟨2009204, by rfl⟩ : syracuseStep 2678939 = 4018409) B4018409
theorem B942263 : Blo 626299 942263 := bstep (se 1 (by rfl) ⟨706697, by rfl⟩ : syracuseStep 942263 = 1413395) B1413395
theorem B3170663 : Blo 626299 3170663 := bstep (se 1 (by rfl) ⟨2377997, by rfl⟩ : syracuseStep 3170663 = 4755995) B4755995
theorem B3400307 : Blo 626299 3400307 := bstep (se 1 (by rfl) ⟨2550230, by rfl⟩ : syracuseStep 3400307 = 5100461) B5100461
theorem B942911 : Blo 626299 942911 := bstep (se 1 (by rfl) ⟨707183, by rfl⟩ : syracuseStep 942911 = 1414367) B1414367
theorem B2122685 : Blo 626299 2122685 := bstep (se 3 (by rfl) ⟨398003, by rfl⟩ : syracuseStep 2122685 = 796007) B796007
theorem B943343 : Blo 626299 943343 := bstep (se 1 (by rfl) ⟨707507, by rfl⟩ : syracuseStep 943343 = 1415015) B1415015
theorem B943487 : Blo 626299 943487 := bstep (se 1 (by rfl) ⟨707615, by rfl⟩ : syracuseStep 943487 = 1415231) B1415231
theorem B27158165 : Blo 626299 27158165 := bstep (se 6 (by rfl) ⟨636519, by rfl⟩ : syracuseStep 27158165 = 1273039) B1273039
theorem B943847 : Blo 626299 943847 := bstep (se 1 (by rfl) ⟨707885, by rfl⟩ : syracuseStep 943847 = 1415771) B1415771
theorem B4024201 : Blo 626299 4024201 := bstep (se 2 (by rfl) ⟨1509075, by rfl⟩ : syracuseStep 4024201 = 3018151) B3018151
theorem B944255 : Blo 626299 944255 := bstep (se 1 (by rfl) ⟨708191, by rfl⟩ : syracuseStep 944255 = 1416383) B1416383
theorem B944591 : Blo 626299 944591 := bstep (se 1 (by rfl) ⟨708443, by rfl⟩ : syracuseStep 944591 = 1416887) B1416887
theorem B2124521 : Blo 626299 2124521 := bstep (se 2 (by rfl) ⟨796695, by rfl⟩ : syracuseStep 2124521 = 1593391) B1593391
theorem B945311 : Blo 626299 945311 := bstep (se 1 (by rfl) ⟨708983, by rfl⟩ : syracuseStep 945311 = 1417967) B1417967
theorem B6024617 : Blo 626299 6024617 := bstep (se 2 (by rfl) ⟨2259231, by rfl⟩ : syracuseStep 6024617 = 4518463) B4518463
theorem B5369327 : Blo 626299 5369327 := bstep (se 1 (by rfl) ⟨4026995, by rfl⟩ : syracuseStep 5369327 = 8053991) B8053991
theorem B2684441 : Blo 626299 2684441 := bstep (se 2 (by rfl) ⟨1006665, by rfl⟩ : syracuseStep 2684441 = 2013331) B2013331
theorem B7239563 : Blo 626299 7239563 := bstep (se 1 (by rfl) ⟨5429672, by rfl⟩ : syracuseStep 7239563 = 10859345) B10859345
theorem B2390057 : Blo 626299 2390057 := bstep (se 2 (by rfl) ⟨896271, by rfl⟩ : syracuseStep 2390057 = 1792543) B1792543
theorem B4290707 : Blo 626299 4290707 := bstep (se 1 (by rfl) ⟨3218030, by rfl⟩ : syracuseStep 4290707 = 6436061) B6436061
theorem B9075503 : Blo 626299 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B2687003 : Blo 626299 2687003 := bstep (se 1 (by rfl) ⟨2015252, by rfl⟩ : syracuseStep 2687003 = 4030505) B4030505
theorem B7176275 : Blo 626299 7176275 := bstep (se 1 (by rfl) ⟨5382206, by rfl⟩ : syracuseStep 7176275 = 10764413) B10764413
theorem B2392487 : Blo 626299 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B8028719 : Blo 626299 8028719 := bstep (se 1 (by rfl) ⟨6021539, by rfl⟩ : syracuseStep 8028719 = 12043079) B12043079
theorem B2425825 : Blo 626299 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B1410047 : Blo 626299 1410047 := bstep (se 1 (by rfl) ⟨1057535, by rfl⟩ : syracuseStep 1410047 = 2115071) B2115071
theorem B3573011 : Blo 626299 3573011 := bstep (se 1 (by rfl) ⟨2679758, by rfl⟩ : syracuseStep 3573011 = 5359517) B5359517
theorem B2262431 : Blo 626299 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B1411145 : Blo 626299 1411145 := bstep (se 2 (by rfl) ⟨529179, by rfl⟩ : syracuseStep 1411145 = 1058359) B1058359
theorem B626407 : Blo 626299 626407 := bstep (se 1 (by rfl) ⟨469805, by rfl⟩ : syracuseStep 626407 = 939611) B939611
theorem B627439 : Blo 626299 627439 := bstep (se 1 (by rfl) ⟨470579, by rfl⟩ : syracuseStep 627439 = 941159) B941159
theorem B627583 : Blo 626299 627583 := bstep (se 1 (by rfl) ⟨470687, by rfl⟩ : syracuseStep 627583 = 941375) B941375
theorem B627711 : Blo 626299 627711 := bstep (se 1 (by rfl) ⟨470783, by rfl⟩ : syracuseStep 627711 = 941567) B941567
theorem B627759 : Blo 626299 627759 := bstep (se 1 (by rfl) ⟨470819, by rfl⟩ : syracuseStep 627759 = 941639) B941639
theorem B628175 : Blo 626299 628175 := bstep (se 1 (by rfl) ⟨471131, by rfl⟩ : syracuseStep 628175 = 942263) B942263
theorem B2266871 : Blo 626299 2266871 := bstep (se 1 (by rfl) ⟨1700153, by rfl⟩ : syracuseStep 2266871 = 3400307) B3400307
theorem B628607 : Blo 626299 628607 := bstep (se 1 (by rfl) ⟨471455, by rfl⟩ : syracuseStep 628607 = 942911) B942911
theorem B1415123 : Blo 626299 1415123 := bstep (se 1 (by rfl) ⟨1061342, by rfl⟩ : syracuseStep 1415123 = 2122685) B2122685
theorem B628895 : Blo 626299 628895 := bstep (se 1 (by rfl) ⟨471671, by rfl⟩ : syracuseStep 628895 = 943343) B943343
theorem B628991 : Blo 626299 628991 := bstep (se 1 (by rfl) ⟨471743, by rfl⟩ : syracuseStep 628991 = 943487) B943487
theorem B629231 : Blo 626299 629231 := bstep (se 1 (by rfl) ⟨471923, by rfl⟩ : syracuseStep 629231 = 943847) B943847
theorem B629503 : Blo 626299 629503 := bstep (se 1 (by rfl) ⟨472127, by rfl⟩ : syracuseStep 629503 = 944255) B944255
theorem B629727 : Blo 626299 629727 := bstep (se 1 (by rfl) ⟨472295, by rfl⟩ : syracuseStep 629727 = 944591) B944591
theorem B1416347 : Blo 626299 1416347 := bstep (se 1 (by rfl) ⟨1062260, by rfl⟩ : syracuseStep 1416347 = 2124521) B2124521
theorem B630207 : Blo 626299 630207 := bstep (se 1 (by rfl) ⟨472655, by rfl⟩ : syracuseStep 630207 = 945311) B945311
theorem B3579551 : Blo 626299 3579551 := bstep (se 1 (by rfl) ⟨2684663, by rfl⟩ : syracuseStep 3579551 = 5369327) B5369327
theorem B5382071 : Blo 626299 5382071 := bstep (se 1 (by rfl) ⟨4036553, by rfl⟩ : syracuseStep 5382071 = 8073107) B8073107
theorem B1417337 : Blo 626299 1417337 := bstep (se 2 (by rfl) ⟨531501, by rfl⟩ : syracuseStep 1417337 = 1063003) B1063003
theorem B1057657 : Blo 626299 1057657 := bstep (se 2 (by rfl) ⟨396621, by rfl⟩ : syracuseStep 1057657 = 793243) B793243
theorem B5088133 : Blo 626299 5088133 := bstep (se 4 (by rfl) ⟨477012, by rfl⟩ : syracuseStep 5088133 = 954025) B954025
theorem B4826375 : Blo 626299 4826375 := bstep (se 1 (by rfl) ⟨3619781, by rfl⟩ : syracuseStep 4826375 = 7239563) B7239563
theorem B2860471 : Blo 626299 2860471 := bstep (se 1 (by rfl) ⟨2145353, by rfl⟩ : syracuseStep 2860471 = 4290707) B4290707
theorem B9055259 : Blo 626299 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B36810593 : Blo 626299 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B4763771 : Blo 626299 4763771 := bstep (se 1 (by rfl) ⟨3572828, by rfl⟩ : syracuseStep 4763771 = 7145657) B7145657
theorem B58831667 : Blo 626299 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B5584403 : Blo 626299 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B1062463 : Blo 626299 1062463 := bstep (se 1 (by rfl) ⟨796847, by rfl⟩ : syracuseStep 1062463 = 1593695) B1593695
theorem B1194239 : Blo 626299 1194239 := bstep (se 1 (by rfl) ⟨895679, by rfl⟩ : syracuseStep 1194239 = 1791359) B1791359
theorem B9060331 : Blo 626299 9060331 := bstep (se 1 (by rfl) ⟨6795248, by rfl⟩ : syracuseStep 9060331 = 13590497) B13590497
theorem B1785959 : Blo 626299 1785959 := bstep (se 1 (by rfl) ⟨1339469, by rfl⟩ : syracuseStep 1785959 = 2678939) B2678939
theorem B2113775 : Blo 626299 2113775 := bstep (se 1 (by rfl) ⟨1585331, by rfl⟩ : syracuseStep 2113775 = 3170663) B3170663
theorem B2146655 : Blo 626299 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B18105443 : Blo 626299 18105443 := bstep (se 1 (by rfl) ⟨13579082, by rfl⟩ : syracuseStep 18105443 = 27158165) B27158165
theorem B706279 : Blo 626299 706279 := bstep (se 1 (by rfl) ⟨529709, by rfl⟩ : syracuseStep 706279 = 1059419) B1059419
theorem B4016411 : Blo 626299 4016411 := bstep (se 1 (by rfl) ⟨3012308, by rfl⟩ : syracuseStep 4016411 = 6024617) B6024617
theorem B4770089 : Blo 626299 4770089 := bstep (se 2 (by rfl) ⟨1788783, by rfl⟩ : syracuseStep 4770089 = 3577567) B3577567
theorem B707611 : Blo 626299 707611 := bstep (se 1 (by rfl) ⟨530708, by rfl⟩ : syracuseStep 707611 = 1061417) B1061417
theorem B1789627 : Blo 626299 1789627 := bstep (se 1 (by rfl) ⟨1342220, by rfl⟩ : syracuseStep 1789627 = 2684441) B2684441
theorem B1593371 : Blo 626299 1593371 := bstep (se 1 (by rfl) ⟨1195028, by rfl⟩ : syracuseStep 1593371 = 2390057) B2390057
theorem B6050335 : Blo 626299 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B8574407 : Blo 626299 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B1005743 : Blo 626299 1005743 := bstep (se 1 (by rfl) ⟨754307, by rfl⟩ : syracuseStep 1005743 = 1508615) B1508615
theorem B940409 : Blo 626299 940409 := bstep (se 2 (by rfl) ⟨352653, by rfl⟩ : syracuseStep 940409 = 705307) B705307
theorem B940457 : Blo 626299 940457 := bstep (se 2 (by rfl) ⟨352671, by rfl⟩ : syracuseStep 940457 = 705343) B705343
theorem B2120363 : Blo 626299 2120363 := bstep (se 1 (by rfl) ⟨1590272, by rfl⟩ : syracuseStep 2120363 = 3180545) B3180545
theorem B940841 : Blo 626299 940841 := bstep (se 2 (by rfl) ⟨352815, by rfl⟩ : syracuseStep 940841 = 705631) B705631
theorem B678907 : Blo 626299 678907 := bstep (se 1 (by rfl) ⟨509180, by rfl⟩ : syracuseStep 678907 = 1018361) B1018361
theorem B2153785 : Blo 626299 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B2678255 : Blo 626299 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B2121497 : Blo 626299 2121497 := bstep (se 2 (by rfl) ⟨795561, by rfl⟩ : syracuseStep 2121497 = 1591123) B1591123
theorem B5365601 : Blo 626299 5365601 := bstep (se 2 (by rfl) ⟨2012100, by rfl⟩ : syracuseStep 5365601 = 4024201) B4024201
theorem B942575 : Blo 626299 942575 := bstep (se 1 (by rfl) ⟨706931, by rfl⟩ : syracuseStep 942575 = 1413863) B1413863
theorem B943199 : Blo 626299 943199 := bstep (se 1 (by rfl) ⟨707399, by rfl⟩ : syracuseStep 943199 = 1414799) B1414799
theorem B2548903 : Blo 626299 2548903 := bstep (se 1 (by rfl) ⟨1911677, by rfl⟩ : syracuseStep 2548903 = 3823355) B3823355
theorem B38758013 : Blo 626299 38758013 := bstep (se 3 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 38758013 = 14534255) B14534255
theorem B943775 : Blo 626299 943775 := bstep (se 1 (by rfl) ⟨707831, by rfl⟩ : syracuseStep 943775 = 1415663) B1415663
theorem B1861487 : Blo 626299 1861487 := bstep (se 1 (by rfl) ⟨1396115, by rfl⟩ : syracuseStep 1861487 = 2792231) B2792231
theorem B1338095 : Blo 626299 1338095 := bstep (se 1 (by rfl) ⟨1003571, by rfl⟩ : syracuseStep 1338095 = 2007143) B2007143
theorem B945383 : Blo 626299 945383 := bstep (se 1 (by rfl) ⟨709037, by rfl⟩ : syracuseStep 945383 = 1418075) B1418075
theorem B2387339 : Blo 626299 2387339 := bstep (se 1 (by rfl) ⟨1790504, by rfl⟩ : syracuseStep 2387339 = 3581009) B3581009
theorem B18838781 : Blo 626299 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B1341281 : Blo 626299 1341281 := bstep (se 2 (by rfl) ⟨502980, by rfl⟩ : syracuseStep 1341281 = 1005961) B1005961
theorem B7174817 : Blo 626299 7174817 := bstep (se 2 (by rfl) ⟨2690556, by rfl⟩ : syracuseStep 7174817 = 5381113) B5381113
theorem B2391227 : Blo 626299 2391227 := bstep (se 1 (by rfl) ⟨1793420, by rfl⟩ : syracuseStep 2391227 = 3586841) B3586841
theorem B1342811 : Blo 626299 1342811 := bstep (se 1 (by rfl) ⟨1007108, by rfl⟩ : syracuseStep 1342811 = 2014217) B2014217
theorem B7241491 : Blo 626299 7241491 := bstep (se 1 (by rfl) ⟨5431118, by rfl⟩ : syracuseStep 7241491 = 10862237) B10862237
theorem B4784183 : Blo 626299 4784183 := bstep (se 1 (by rfl) ⟨3588137, by rfl⟩ : syracuseStep 4784183 = 7176275) B7176275
theorem B1409183 : Blo 626299 1409183 := bstep (se 1 (by rfl) ⟨1056887, by rfl⟩ : syracuseStep 1409183 = 2113775) B2113775
theorem B1410209 : Blo 626299 1410209 := bstep (se 2 (by rfl) ⟨528828, by rfl⟩ : syracuseStep 1410209 = 1057657) B1057657
theorem B6784177 : Blo 626299 6784177 := bstep (se 2 (by rfl) ⟨2544066, by rfl⟩ : syracuseStep 6784177 = 5088133) B5088133
theorem B3180059 : Blo 626299 3180059 := bstep (se 1 (by rfl) ⟨2385044, by rfl⟩ : syracuseStep 3180059 = 4770089) B4770089
theorem B6033149 : Blo 626299 6033149 := bstep (se 3 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 6033149 = 2262431) B2262431
theorem B626939 : Blo 626299 626939 := bstep (se 1 (by rfl) ⟨470204, by rfl⟩ : syracuseStep 626939 = 940409) B940409
theorem B626971 : Blo 626299 626971 := bstep (se 1 (by rfl) ⟨470228, by rfl⟩ : syracuseStep 626971 = 940457) B940457
theorem B1413575 : Blo 626299 1413575 := bstep (se 1 (by rfl) ⟨1060181, by rfl⟩ : syracuseStep 1413575 = 2120363) B2120363
theorem B627227 : Blo 626299 627227 := bstep (se 1 (by rfl) ⟨470420, by rfl⟩ : syracuseStep 627227 = 940841) B940841
theorem B1414331 : Blo 626299 1414331 := bstep (se 1 (by rfl) ⟨1060748, by rfl⟩ : syracuseStep 1414331 = 2121497) B2121497
theorem B3577067 : Blo 626299 3577067 := bstep (se 1 (by rfl) ⟨2682800, by rfl⟩ : syracuseStep 3577067 = 5365601) B5365601
theorem B628383 : Blo 626299 628383 := bstep (se 1 (by rfl) ⟨471287, by rfl⟩ : syracuseStep 628383 = 942575) B942575
theorem B8067113 : Blo 626299 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B628799 : Blo 626299 628799 := bstep (se 1 (by rfl) ⟨471599, by rfl⟩ : syracuseStep 628799 = 943199) B943199
theorem B3217583 : Blo 626299 3217583 := bstep (se 1 (by rfl) ⟨2413187, by rfl⟩ : syracuseStep 3217583 = 4826375) B4826375
theorem B629183 : Blo 626299 629183 := bstep (se 1 (by rfl) ⟨471887, by rfl⟩ : syracuseStep 629183 = 943775) B943775
theorem B892063 : Blo 626299 892063 := bstep (se 1 (by rfl) ⟨669047, by rfl⟩ : syracuseStep 892063 = 1338095) B1338095
theorem B6036839 : Blo 626299 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B1416617 : Blo 626299 1416617 := bstep (se 2 (by rfl) ⟨531231, by rfl⟩ : syracuseStep 1416617 = 1062463) B1062463
theorem B630255 : Blo 626299 630255 := bstep (se 1 (by rfl) ⟨472691, by rfl⟩ : syracuseStep 630255 = 945383) B945383
theorem B12559187 : Blo 626299 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B894187 : Blo 626299 894187 := bstep (se 1 (by rfl) ⟨670640, by rfl⟩ : syracuseStep 894187 = 1341281) B1341281
theorem B796159 : Blo 626299 796159 := bstep (se 1 (by rfl) ⟨597119, by rfl⟩ : syracuseStep 796159 = 1194239) B1194239
theorem B895207 : Blo 626299 895207 := bstep (se 1 (by rfl) ⟨671405, by rfl⟩ : syracuseStep 895207 = 1342811) B1342811
theorem B1190639 : Blo 626299 1190639 := bstep (se 1 (by rfl) ⟨892979, by rfl⟩ : syracuseStep 1190639 = 1785959) B1785959
theorem B5352479 : Blo 626299 5352479 := bstep (se 1 (by rfl) ⟨4014359, by rfl⟩ : syracuseStep 5352479 = 8028719) B8028719
theorem B12070295 : Blo 626299 12070295 := bstep (se 1 (by rfl) ⟨9052721, by rfl⟩ : syracuseStep 12070295 = 18105443) B18105443
theorem B3813961 : Blo 626299 3813961 := bstep (se 2 (by rfl) ⟨1430235, by rfl⟩ : syracuseStep 3813961 = 2860471) B2860471
theorem B1062247 : Blo 626299 1062247 := bstep (se 1 (by rfl) ⟨796685, by rfl⟩ : syracuseStep 1062247 = 1593371) B1593371
theorem B5716271 : Blo 626299 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B1570585301 : Blo 626299 1570585301 := bstep (se 7 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 1570585301 = 36810593) B36810593
theorem B6044989 : Blo 626299 6044989 := bstep (se 3 (by rfl) ⟨1133435, by rfl⟩ : syracuseStep 6044989 = 2266871) B2266871
theorem B1785503 : Blo 626299 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B3588047 : Blo 626299 3588047 := bstep (se 1 (by rfl) ⟨2691035, by rfl⟩ : syracuseStep 3588047 = 5382071) B5382071
theorem B3620837 : Blo 626299 3620837 := bstep (se 4 (by rfl) ⟨339453, by rfl⟩ : syracuseStep 3620837 = 678907) B678907
theorem B25838675 : Blo 626299 25838675 := bstep (se 1 (by rfl) ⟨19379006, by rfl⟩ : syracuseStep 25838675 = 38758013) B38758013
theorem B1591559 : Blo 626299 1591559 := bstep (se 1 (by rfl) ⟨1193669, by rfl⟩ : syracuseStep 1591559 = 2387339) B2387339
theorem B3722935 : Blo 626299 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B2871713 : Blo 626299 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B1594151 : Blo 626299 1594151 := bstep (se 1 (by rfl) ⟨1195613, by rfl⟩ : syracuseStep 1594151 = 2391227) B2391227
theorem B9655321 : Blo 626299 9655321 := bstep (se 2 (by rfl) ⟨3620745, by rfl⟩ : syracuseStep 9655321 = 7241491) B7241491
theorem B12080441 : Blo 626299 12080441 := bstep (se 2 (by rfl) ⟨4530165, by rfl⟩ : syracuseStep 12080441 = 9060331) B9060331
theorem B1791335 : Blo 626299 1791335 := bstep (se 1 (by rfl) ⟨1343501, by rfl⟩ : syracuseStep 1791335 = 2687003) B2687003
theorem B1431103 : Blo 626299 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B1594991 : Blo 626299 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B940031 : Blo 626299 940031 := bstep (se 1 (by rfl) ⟨705023, by rfl⟩ : syracuseStep 940031 = 1410047) B1410047
theorem B2382007 : Blo 626299 2382007 := bstep (se 1 (by rfl) ⟨1786505, by rfl⟩ : syracuseStep 2382007 = 3573011) B3573011
theorem B3234433 : Blo 626299 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B940763 : Blo 626299 940763 := bstep (se 1 (by rfl) ⟨705572, by rfl⟩ : syracuseStep 940763 = 1411145) B1411145
theorem B2677607 : Blo 626299 2677607 := bstep (se 1 (by rfl) ⟨2008205, by rfl⟩ : syracuseStep 2677607 = 4016411) B4016411
theorem B3398537 : Blo 626299 3398537 := bstep (se 2 (by rfl) ⟨1274451, by rfl⟩ : syracuseStep 3398537 = 2548903) B2548903
theorem B941705 : Blo 626299 941705 := bstep (se 2 (by rfl) ⟨353139, by rfl⟩ : syracuseStep 941705 = 706279) B706279
theorem B943415 : Blo 626299 943415 := bstep (se 1 (by rfl) ⟨707561, by rfl⟩ : syracuseStep 943415 = 1415123) B1415123
theorem B943481 : Blo 626299 943481 := bstep (se 2 (by rfl) ⟨353805, by rfl⟩ : syracuseStep 943481 = 707611) B707611
theorem B944231 : Blo 626299 944231 := bstep (se 1 (by rfl) ⟨708173, by rfl⟩ : syracuseStep 944231 = 1416347) B1416347
theorem B2386169 : Blo 626299 2386169 := bstep (se 2 (by rfl) ⟨894813, by rfl⟩ : syracuseStep 2386169 = 1789627) B1789627
theorem B2386367 : Blo 626299 2386367 := bstep (se 1 (by rfl) ⟨1789775, by rfl⟩ : syracuseStep 2386367 = 3579551) B3579551
theorem B944891 : Blo 626299 944891 := bstep (se 1 (by rfl) ⟨708668, by rfl⟩ : syracuseStep 944891 = 1417337) B1417337
theorem B2681981 : Blo 626299 2681981 := bstep (se 3 (by rfl) ⟨502871, by rfl⟩ : syracuseStep 2681981 = 1005743) B1005743
theorem B1240991 : Blo 626299 1240991 := bstep (se 1 (by rfl) ⟨930743, by rfl⟩ : syracuseStep 1240991 = 1861487) B1861487
theorem B3175847 : Blo 626299 3175847 := bstep (se 1 (by rfl) ⟨2381885, by rfl⟩ : syracuseStep 3175847 = 4763771) B4763771
theorem B39221111 : Blo 626299 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B4783211 : Blo 626299 4783211 := bstep (se 1 (by rfl) ⟨3587408, by rfl⟩ : syracuseStep 4783211 = 7174817) B7174817
theorem B9045569 : Blo 626299 9045569 := bstep (se 2 (by rfl) ⟨3392088, by rfl⟩ : syracuseStep 9045569 = 6784177) B6784177
theorem B626687 : Blo 626299 626687 := bstep (se 1 (by rfl) ⟨470015, by rfl⟩ : syracuseStep 626687 = 940031) B940031
theorem B5378075 : Blo 626299 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B627175 : Blo 626299 627175 := bstep (se 1 (by rfl) ⟨470381, by rfl⟩ : syracuseStep 627175 = 940763) B940763
theorem B2265691 : Blo 626299 2265691 := bstep (se 1 (by rfl) ⟨1699268, by rfl⟩ : syracuseStep 2265691 = 3398537) B3398537
theorem B627803 : Blo 626299 627803 := bstep (se 1 (by rfl) ⟨470852, by rfl⟩ : syracuseStep 627803 = 941705) B941705
theorem B5085281 : Blo 626299 5085281 := bstep (se 2 (by rfl) ⟨1906980, by rfl⟩ : syracuseStep 5085281 = 3813961) B3813961
theorem B15243389 : Blo 626299 15243389 := bstep (se 3 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 15243389 = 5716271) B5716271
theorem B628943 : Blo 626299 628943 := bstep (se 1 (by rfl) ⟨471707, by rfl⟩ : syracuseStep 628943 = 943415) B943415
theorem B628987 : Blo 626299 628987 := bstep (se 1 (by rfl) ⟨471740, by rfl⟩ : syracuseStep 628987 = 943481) B943481
theorem B629487 : Blo 626299 629487 := bstep (se 1 (by rfl) ⟨472115, by rfl⟩ : syracuseStep 629487 = 944231) B944231
theorem B1416329 : Blo 626299 1416329 := bstep (se 2 (by rfl) ⟨531123, by rfl⟩ : syracuseStep 1416329 = 1062247) B1062247
theorem B629927 : Blo 626299 629927 := bstep (se 1 (by rfl) ⟨472445, by rfl⟩ : syracuseStep 629927 = 944891) B944891
theorem B1908137 : Blo 626299 1908137 := bstep (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) B1431103
theorem B827327 : Blo 626299 827327 := bstep (se 1 (by rfl) ⟨620495, by rfl⟩ : syracuseStep 827327 = 1240991) B1240991
theorem B1189417 : Blo 626299 1189417 := bstep (se 2 (by rfl) ⟨446031, by rfl⟩ : syracuseStep 1189417 = 892063) B892063
theorem B4761341 : Blo 626299 4761341 := bstep (se 3 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 4761341 = 1785503) B1785503
theorem B3188807 : Blo 626299 3188807 := bstep (se 1 (by rfl) ⟨2391605, by rfl⟩ : syracuseStep 3188807 = 4783211) B4783211
theorem B3189455 : Blo 626299 3189455 := bstep (se 1 (by rfl) ⟨2392091, by rfl⟩ : syracuseStep 3189455 = 4784183) B4784183
theorem B1061039 : Blo 626299 1061039 := bstep (se 1 (by rfl) ⟨795779, by rfl⟩ : syracuseStep 1061039 = 1591559) B1591559
theorem B1192249 : Blo 626299 1192249 := bstep (se 2 (by rfl) ⟨447093, by rfl⟩ : syracuseStep 1192249 = 894187) B894187
theorem B1061545 : Blo 626299 1061545 := bstep (se 2 (by rfl) ⟨398079, by rfl⟩ : syracuseStep 1061545 = 796159) B796159
theorem B1914475 : Blo 626299 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B1193609 : Blo 626299 1193609 := bstep (se 2 (by rfl) ⟨447603, by rfl⟩ : syracuseStep 1193609 = 895207) B895207
theorem B1062767 : Blo 626299 1062767 := bstep (se 1 (by rfl) ⟨797075, by rfl⟩ : syracuseStep 1062767 = 1594151) B1594151
theorem B1063327 : Blo 626299 1063327 := bstep (se 1 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 1063327 = 1594991) B1594991
theorem B2145055 : Blo 626299 2145055 := bstep (se 1 (by rfl) ⟨1608791, by rfl⟩ : syracuseStep 2145055 = 3217583) B3217583
theorem B1785071 : Blo 626299 1785071 := bstep (se 1 (by rfl) ⟨1338803, by rfl⟩ : syracuseStep 1785071 = 2677607) B2677607
theorem B4963913 : Blo 626299 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B8372791 : Blo 626299 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B1590779 : Blo 626299 1590779 := bstep (se 1 (by rfl) ⟨1193084, by rfl⟩ : syracuseStep 1590779 = 2386169) B2386169
theorem B1590911 : Blo 626299 1590911 := bstep (se 1 (by rfl) ⟨1193183, by rfl⟩ : syracuseStep 1590911 = 2386367) B2386367
theorem B1787987 : Blo 626299 1787987 := bstep (se 1 (by rfl) ⟨1340990, by rfl⟩ : syracuseStep 1787987 = 2681981) B2681981
theorem B8046863 : Blo 626299 8046863 := bstep (se 1 (by rfl) ⟨6035147, by rfl⟩ : syracuseStep 8046863 = 12070295) B12070295
theorem B4312577 : Blo 626299 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B2117231 : Blo 626299 2117231 := bstep (se 1 (by rfl) ⟨1587923, by rfl⟩ : syracuseStep 2117231 = 3175847) B3175847
theorem B1047056867 : Blo 626299 1047056867 := bstep (se 1 (by rfl) ⟨785292650, by rfl⟩ : syracuseStep 1047056867 = 1570585301) B1570585301
theorem B2413891 : Blo 626299 2413891 := bstep (se 1 (by rfl) ⟨1810418, by rfl⟩ : syracuseStep 2413891 = 3620837) B3620837
theorem B939455 : Blo 626299 939455 := bstep (se 1 (by rfl) ⟨704591, by rfl⟩ : syracuseStep 939455 = 1409183) B1409183
theorem B17225783 : Blo 626299 17225783 := bstep (se 1 (by rfl) ⟨12919337, by rfl⟩ : syracuseStep 17225783 = 25838675) B25838675
theorem B940139 : Blo 626299 940139 := bstep (se 1 (by rfl) ⟨705104, by rfl⟩ : syracuseStep 940139 = 1410209) B1410209
theorem B2120039 : Blo 626299 2120039 := bstep (se 1 (by rfl) ⟨1590029, by rfl⟩ : syracuseStep 2120039 = 3180059) B3180059
theorem B4022099 : Blo 626299 4022099 := bstep (se 1 (by rfl) ⟨3016574, by rfl⟩ : syracuseStep 4022099 = 6033149) B6033149
theorem B942383 : Blo 626299 942383 := bstep (se 1 (by rfl) ⟨706787, by rfl⟩ : syracuseStep 942383 = 1413575) B1413575
theorem B942887 : Blo 626299 942887 := bstep (se 1 (by rfl) ⟨707165, by rfl⟩ : syracuseStep 942887 = 1414331) B1414331
theorem B2384711 : Blo 626299 2384711 := bstep (se 1 (by rfl) ⟨1788533, by rfl⟩ : syracuseStep 2384711 = 3577067) B3577067
theorem B8053627 : Blo 626299 8053627 := bstep (se 1 (by rfl) ⟨6040220, by rfl⟩ : syracuseStep 8053627 = 12080441) B12080441
theorem B4776893 : Blo 626299 4776893 := bstep (se 3 (by rfl) ⟨895667, by rfl⟩ : syracuseStep 4776893 = 1791335) B1791335
theorem B4024559 : Blo 626299 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B944411 : Blo 626299 944411 := bstep (se 1 (by rfl) ⟨708308, by rfl⟩ : syracuseStep 944411 = 1416617) B1416617
theorem B12873761 : Blo 626299 12873761 := bstep (se 2 (by rfl) ⟨4827660, by rfl⟩ : syracuseStep 12873761 = 9655321) B9655321
theorem B3175037 : Blo 626299 3175037 := bstep (se 3 (by rfl) ⟨595319, by rfl⟩ : syracuseStep 3175037 = 1190639) B1190639
theorem B3568319 : Blo 626299 3568319 := bstep (se 1 (by rfl) ⟨2676239, by rfl⟩ : syracuseStep 3568319 = 5352479) B5352479
theorem B3176009 : Blo 626299 3176009 := bstep (se 2 (by rfl) ⟨1191003, by rfl⟩ : syracuseStep 3176009 = 2382007) B2382007
theorem B26147407 : Blo 626299 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B8059985 : Blo 626299 8059985 := bstep (se 2 (by rfl) ⟨3022494, by rfl⟩ : syracuseStep 8059985 = 6044989) B6044989
theorem B2392031 : Blo 626299 2392031 := bstep (se 1 (by rfl) ⟨1794023, by rfl⟩ : syracuseStep 2392031 = 3588047) B3588047
theorem B6030379 : Blo 626299 6030379 := bstep (se 1 (by rfl) ⟨4522784, by rfl⟩ : syracuseStep 6030379 = 9045569) B9045569
theorem B1411487 : Blo 626299 1411487 := bstep (se 1 (by rfl) ⟨1058615, by rfl⟩ : syracuseStep 1411487 = 2117231) B2117231
theorem B626303 : Blo 626299 626303 := bstep (se 1 (by rfl) ⟨469727, by rfl⟩ : syracuseStep 626303 = 939455) B939455
theorem B626759 : Blo 626299 626759 := bstep (se 1 (by rfl) ⟨470069, by rfl⟩ : syracuseStep 626759 = 940139) B940139
theorem B10162259 : Blo 626299 10162259 := bstep (se 1 (by rfl) ⟨7621694, by rfl⟩ : syracuseStep 10162259 = 15243389) B15243389
theorem B1413359 : Blo 626299 1413359 := bstep (se 1 (by rfl) ⟨1060019, by rfl⟩ : syracuseStep 1413359 = 2120039) B2120039
theorem B628255 : Blo 626299 628255 := bstep (se 1 (by rfl) ⟨471191, by rfl⟩ : syracuseStep 628255 = 942383) B942383
theorem B628591 : Blo 626299 628591 := bstep (se 1 (by rfl) ⟨471443, by rfl⟩ : syracuseStep 628591 = 942887) B942887
theorem B3184595 : Blo 626299 3184595 := bstep (se 1 (by rfl) ⟨2388446, by rfl⟩ : syracuseStep 3184595 = 4776893) B4776893
theorem B3020921 : Blo 626299 3020921 := bstep (se 2 (by rfl) ⟨1132845, by rfl⟩ : syracuseStep 3020921 = 2265691) B2265691
theorem B1415393 : Blo 626299 1415393 := bstep (se 2 (by rfl) ⟨530772, by rfl⟩ : syracuseStep 1415393 = 1061545) B1061545
theorem B629607 : Blo 626299 629607 := bstep (se 1 (by rfl) ⟨472205, by rfl⟩ : syracuseStep 629607 = 944411) B944411
theorem B1417769 : Blo 626299 1417769 := bstep (se 2 (by rfl) ⟨531663, by rfl⟩ : syracuseStep 1417769 = 1063327) B1063327
theorem B2860073 : Blo 626299 2860073 := bstep (se 2 (by rfl) ⟨1072527, by rfl⟩ : syracuseStep 2860073 = 2145055) B2145055
theorem B795739 : Blo 626299 795739 := bstep (se 1 (by rfl) ⟨596804, by rfl⟩ : syracuseStep 795739 = 1193609) B1193609
theorem B5088365 : Blo 626299 5088365 := bstep (se 3 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 5088365 = 1908137) B1908137
theorem B1190047 : Blo 626299 1190047 := bstep (se 1 (by rfl) ⟨892535, by rfl⟩ : syracuseStep 1190047 = 1785071) B1785071
theorem B2206205 : Blo 626299 2206205 := bstep (se 3 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 2206205 = 827327) B827327
theorem B1060519 : Blo 626299 1060519 := bstep (se 1 (by rfl) ⟨795389, by rfl⟩ : syracuseStep 1060519 = 1590779) B1590779
theorem B1060607 : Blo 626299 1060607 := bstep (se 1 (by rfl) ⟨795455, by rfl⟩ : syracuseStep 1060607 = 1590911) B1590911
theorem B1191991 : Blo 626299 1191991 := bstep (se 1 (by rfl) ⟨893993, by rfl⟩ : syracuseStep 1191991 = 1787987) B1787987
theorem B1585889 : Blo 626299 1585889 := bstep (se 2 (by rfl) ⟨594708, by rfl⟩ : syracuseStep 1585889 = 1189417) B1189417
theorem B3585383 : Blo 626299 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B698037911 : Blo 626299 698037911 := bstep (se 1 (by rfl) ⟨523528433, by rfl⟩ : syracuseStep 698037911 = 1047056867) B1047056867
theorem B11483855 : Blo 626299 11483855 := bstep (se 1 (by rfl) ⟨8612891, by rfl⟩ : syracuseStep 11483855 = 17225783) B17225783
theorem B3390187 : Blo 626299 3390187 := bstep (se 1 (by rfl) ⟨2542640, by rfl⟩ : syracuseStep 3390187 = 5085281) B5085281
theorem B1589665 : Blo 626299 1589665 := bstep (se 2 (by rfl) ⟨596124, by rfl⟩ : syracuseStep 1589665 = 1192249) B1192249
theorem B1589807 : Blo 626299 1589807 := bstep (se 1 (by rfl) ⟨1192355, by rfl⟩ : syracuseStep 1589807 = 2384711) B2384711
theorem B707359 : Blo 626299 707359 := bstep (se 1 (by rfl) ⟨530519, by rfl⟩ : syracuseStep 707359 = 1061039) B1061039
theorem B2116691 : Blo 626299 2116691 := bstep (se 1 (by rfl) ⟨1587518, by rfl⟩ : syracuseStep 2116691 = 3175037) B3175037
theorem B2378879 : Blo 626299 2378879 := bstep (se 1 (by rfl) ⟨1784159, by rfl⟩ : syracuseStep 2378879 = 3568319) B3568319
theorem B2117339 : Blo 626299 2117339 := bstep (se 1 (by rfl) ⟨1588004, by rfl⟩ : syracuseStep 2117339 = 3176009) B3176009
theorem B708511 : Blo 626299 708511 := bstep (se 1 (by rfl) ⟨531383, by rfl⟩ : syracuseStep 708511 = 1062767) B1062767
theorem B1594687 : Blo 626299 1594687 := bstep (se 1 (by rfl) ⟨1196015, by rfl⟩ : syracuseStep 1594687 = 2392031) B2392031
theorem B10738169 : Blo 626299 10738169 := bstep (se 2 (by rfl) ⟨4026813, by rfl⟩ : syracuseStep 10738169 = 8053627) B8053627
theorem B5364575 : Blo 626299 5364575 := bstep (se 1 (by rfl) ⟨4023431, by rfl⟩ : syracuseStep 5364575 = 8046863) B8046863
theorem B2875051 : Blo 626299 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B44654885 : Blo 626299 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B944219 : Blo 626299 944219 := bstep (se 1 (by rfl) ⟨708164, by rfl⟩ : syracuseStep 944219 = 1416329) B1416329
theorem B2681399 : Blo 626299 2681399 := bstep (se 1 (by rfl) ⟨2011049, by rfl⟩ : syracuseStep 2681399 = 4022099) B4022099
theorem B3174227 : Blo 626299 3174227 := bstep (se 1 (by rfl) ⟨2380670, by rfl⟩ : syracuseStep 3174227 = 4761341) B4761341
theorem B2125871 : Blo 626299 2125871 := bstep (se 1 (by rfl) ⟨1594403, by rfl⟩ : syracuseStep 2125871 = 3188807) B3188807
theorem B2683039 : Blo 626299 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B12874085 : Blo 626299 12874085 := bstep (se 4 (by rfl) ⟨1206945, by rfl⟩ : syracuseStep 12874085 = 2413891) B2413891
theorem B2126303 : Blo 626299 2126303 := bstep (se 1 (by rfl) ⟨1594727, by rfl⟩ : syracuseStep 2126303 = 3189455) B3189455
theorem B2552633 : Blo 626299 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B8582507 : Blo 626299 8582507 := bstep (se 1 (by rfl) ⟨6436880, by rfl⟩ : syracuseStep 8582507 = 12873761) B12873761
theorem B34863209 : Blo 626299 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B5373323 : Blo 626299 5373323 := bstep (se 1 (by rfl) ⟨4029992, by rfl⟩ : syracuseStep 5373323 = 8059985) B8059985
theorem B3309275 : Blo 626299 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B1411127 : Blo 626299 1411127 := bstep (se 1 (by rfl) ⟨1058345, by rfl⟩ : syracuseStep 1411127 = 2116691) B2116691
theorem B1411559 : Blo 626299 1411559 := bstep (se 1 (by rfl) ⟨1058669, by rfl⟩ : syracuseStep 1411559 = 2117339) B2117339
theorem B3576383 : Blo 626299 3576383 := bstep (se 1 (by rfl) ⟨2682287, by rfl⟩ : syracuseStep 3576383 = 5364575) B5364575
theorem B1414025 : Blo 626299 1414025 := bstep (se 2 (by rfl) ⟨530259, by rfl⟩ : syracuseStep 1414025 = 1060519) B1060519
theorem B3577385 : Blo 626299 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B1906715 : Blo 626299 1906715 := bstep (se 1 (by rfl) ⟨1430036, by rfl⟩ : syracuseStep 1906715 = 2860073) B2860073
theorem B629479 : Blo 626299 629479 := bstep (se 1 (by rfl) ⟨472109, by rfl⟩ : syracuseStep 629479 = 944219) B944219
theorem B1417247 : Blo 626299 1417247 := bstep (se 1 (by rfl) ⟨1062935, by rfl⟩ : syracuseStep 1417247 = 2125871) B2125871
theorem B1417535 : Blo 626299 1417535 := bstep (se 1 (by rfl) ⟨1063151, by rfl⟩ : syracuseStep 1417535 = 2126303) B2126303
theorem B1057259 : Blo 626299 1057259 := bstep (se 1 (by rfl) ⟨792944, by rfl⟩ : syracuseStep 1057259 = 1585889) B1585889
theorem B23242139 : Blo 626299 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B8824733 : Blo 626299 8824733 := bstep (se 3 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 8824733 = 3309275) B3309275
theorem B3582215 : Blo 626299 3582215 := bstep (se 1 (by rfl) ⟨2686661, by rfl⟩ : syracuseStep 3582215 = 5373323) B5373323
theorem B1059871 : Blo 626299 1059871 := bstep (se 1 (by rfl) ⟨794903, by rfl⟩ : syracuseStep 1059871 = 1589807) B1589807
theorem B8040505 : Blo 626299 8040505 := bstep (se 2 (by rfl) ⟨3015189, by rfl⟩ : syracuseStep 8040505 = 6030379) B6030379
theorem B1060985 : Blo 626299 1060985 := bstep (se 2 (by rfl) ⟨397869, by rfl⟩ : syracuseStep 1060985 = 795739) B795739
theorem B1585919 : Blo 626299 1585919 := bstep (se 1 (by rfl) ⟨1189439, by rfl⟩ : syracuseStep 1585919 = 2378879) B2378879
theorem B1586729 : Blo 626299 1586729 := bstep (se 2 (by rfl) ⟨595023, by rfl⟩ : syracuseStep 1586729 = 1190047) B1190047
theorem B2013947 : Blo 626299 2013947 := bstep (se 1 (by rfl) ⟨1510460, by rfl⟩ : syracuseStep 2013947 = 3020921) B3020921
theorem B7158779 : Blo 626299 7158779 := bstep (se 1 (by rfl) ⟨5369084, by rfl⟩ : syracuseStep 7158779 = 10738169) B10738169
theorem B1589321 : Blo 626299 1589321 := bstep (se 2 (by rfl) ⟨595995, by rfl⟩ : syracuseStep 1589321 = 1191991) B1191991
theorem B29769923 : Blo 626299 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B3392243 : Blo 626299 3392243 := bstep (se 1 (by rfl) ⟨2544182, by rfl⟩ : syracuseStep 3392243 = 5088365) B5088365
theorem B1787599 : Blo 626299 1787599 := bstep (se 1 (by rfl) ⟨1340699, by rfl⟩ : syracuseStep 1787599 = 2681399) B2681399
theorem B707071 : Blo 626299 707071 := bstep (se 1 (by rfl) ⟨530303, by rfl⟩ : syracuseStep 707071 = 1060607) B1060607
theorem B2116151 : Blo 626299 2116151 := bstep (se 1 (by rfl) ⟨1587113, by rfl⟩ : syracuseStep 2116151 = 3174227) B3174227
theorem B5721671 : Blo 626299 5721671 := bstep (se 1 (by rfl) ⟨4291253, by rfl⟩ : syracuseStep 5721671 = 8582507) B8582507
theorem B465358607 : Blo 626299 465358607 := bstep (se 1 (by rfl) ⟨349018955, by rfl⟩ : syracuseStep 465358607 = 698037911) B698037911
theorem B7655903 : Blo 626299 7655903 := bstep (se 1 (by rfl) ⟨5741927, by rfl⟩ : syracuseStep 7655903 = 11483855) B11483855
theorem B2119553 : Blo 626299 2119553 := bstep (se 2 (by rfl) ⟨794832, by rfl⟩ : syracuseStep 2119553 = 1589665) B1589665
theorem B940991 : Blo 626299 940991 := bstep (se 1 (by rfl) ⟨705743, by rfl⟩ : syracuseStep 940991 = 1411487) B1411487
theorem B6774839 : Blo 626299 6774839 := bstep (se 1 (by rfl) ⟨5081129, by rfl⟩ : syracuseStep 6774839 = 10162259) B10162259
theorem B942239 : Blo 626299 942239 := bstep (se 1 (by rfl) ⟨706679, by rfl⟩ : syracuseStep 942239 = 1413359) B1413359
theorem B943145 : Blo 626299 943145 := bstep (se 2 (by rfl) ⟨353679, by rfl⟩ : syracuseStep 943145 = 707359) B707359
theorem B2123063 : Blo 626299 2123063 := bstep (se 1 (by rfl) ⟨1592297, by rfl⟩ : syracuseStep 2123063 = 3184595) B3184595
theorem B943595 : Blo 626299 943595 := bstep (se 1 (by rfl) ⟨707696, by rfl⟩ : syracuseStep 943595 = 1415393) B1415393
theorem B944681 : Blo 626299 944681 := bstep (se 2 (by rfl) ⟨354255, by rfl⟩ : syracuseStep 944681 = 708511) B708511
theorem B945179 : Blo 626299 945179 := bstep (se 1 (by rfl) ⟨708884, by rfl⟩ : syracuseStep 945179 = 1417769) B1417769
theorem B1470803 : Blo 626299 1470803 := bstep (se 1 (by rfl) ⟨1103102, by rfl⟩ : syracuseStep 1470803 = 2206205) B2206205
theorem B2126249 : Blo 626299 2126249 := bstep (se 2 (by rfl) ⟨797343, by rfl⟩ : syracuseStep 2126249 = 1594687) B1594687
theorem B8582723 : Blo 626299 8582723 := bstep (se 1 (by rfl) ⟨6437042, by rfl⟩ : syracuseStep 8582723 = 12874085) B12874085
theorem B1701755 : Blo 626299 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B2390255 : Blo 626299 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B4520249 : Blo 626299 4520249 := bstep (se 2 (by rfl) ⟨1695093, by rfl⟩ : syracuseStep 4520249 = 3390187) B3390187
theorem B3833401 : Blo 626299 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B2261495 : Blo 626299 2261495 := bstep (se 1 (by rfl) ⟨1696121, by rfl⟩ : syracuseStep 2261495 = 3392243) B3392243
theorem B1410767 : Blo 626299 1410767 := bstep (se 1 (by rfl) ⟨1058075, by rfl⟩ : syracuseStep 1410767 = 2116151) B2116151
theorem B1413035 : Blo 626299 1413035 := bstep (se 1 (by rfl) ⟨1059776, by rfl⟩ : syracuseStep 1413035 = 2119553) B2119553
theorem B1413161 : Blo 626299 1413161 := bstep (se 2 (by rfl) ⟨529935, by rfl⟩ : syracuseStep 1413161 = 1059871) B1059871
theorem B627327 : Blo 626299 627327 := bstep (se 1 (by rfl) ⟨470495, by rfl⟩ : syracuseStep 627327 = 940991) B940991
theorem B10720673 : Blo 626299 10720673 := bstep (se 2 (by rfl) ⟨4020252, by rfl⟩ : syracuseStep 10720673 = 8040505) B8040505
theorem B628159 : Blo 626299 628159 := bstep (se 1 (by rfl) ⟨471119, by rfl⟩ : syracuseStep 628159 = 942239) B942239
theorem B628763 : Blo 626299 628763 := bstep (se 1 (by rfl) ⟨471572, by rfl⟩ : syracuseStep 628763 = 943145) B943145
theorem B1415375 : Blo 626299 1415375 := bstep (se 1 (by rfl) ⟨1061531, by rfl⟩ : syracuseStep 1415375 = 2123063) B2123063
theorem B629063 : Blo 626299 629063 := bstep (se 1 (by rfl) ⟨471797, by rfl⟩ : syracuseStep 629063 = 943595) B943595
theorem B629787 : Blo 626299 629787 := bstep (se 1 (by rfl) ⟨472340, by rfl⟩ : syracuseStep 629787 = 944681) B944681
theorem B630119 : Blo 626299 630119 := bstep (se 1 (by rfl) ⟨472589, by rfl⟩ : syracuseStep 630119 = 945179) B945179
theorem B1417499 : Blo 626299 1417499 := bstep (se 1 (by rfl) ⟨1063124, by rfl⟩ : syracuseStep 1417499 = 2126249) B2126249
theorem B1057279 : Blo 626299 1057279 := bstep (se 1 (by rfl) ⟨792959, by rfl⟩ : syracuseStep 1057279 = 1585919) B1585919
theorem B1057819 : Blo 626299 1057819 := bstep (se 1 (by rfl) ⟨793364, by rfl⟩ : syracuseStep 1057819 = 1586729) B1586729
theorem B1059547 : Blo 626299 1059547 := bstep (se 1 (by rfl) ⟨794660, by rfl⟩ : syracuseStep 1059547 = 1589321) B1589321
theorem B3814447 : Blo 626299 3814447 := bstep (se 1 (by rfl) ⟨2860835, by rfl⟩ : syracuseStep 3814447 = 5721671) B5721671
theorem B704839 : Blo 626299 704839 := bstep (se 1 (by rfl) ⟨528629, by rfl⟩ : syracuseStep 704839 = 1057259) B1057259
theorem B5883155 : Blo 626299 5883155 := bstep (se 1 (by rfl) ⟨4412366, by rfl⟩ : syracuseStep 5883155 = 8824733) B8824733
theorem B707323 : Blo 626299 707323 := bstep (se 1 (by rfl) ⟨530492, by rfl⟩ : syracuseStep 707323 = 1060985) B1060985
theorem B5721815 : Blo 626299 5721815 := bstep (se 1 (by rfl) ⟨4291361, by rfl⟩ : syracuseStep 5721815 = 8582723) B8582723
theorem B1134503 : Blo 626299 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B1593503 : Blo 626299 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B4772519 : Blo 626299 4772519 := bstep (se 1 (by rfl) ⟨3579389, by rfl⟩ : syracuseStep 4772519 = 7158779) B7158779
theorem B19846615 : Blo 626299 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B3922141 : Blo 626299 3922141 := bstep (se 3 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 3922141 = 1470803) B1470803
theorem B940751 : Blo 626299 940751 := bstep (se 1 (by rfl) ⟨705563, by rfl⟩ : syracuseStep 940751 = 1411127) B1411127
theorem B941039 : Blo 626299 941039 := bstep (se 1 (by rfl) ⟨705779, by rfl⟩ : syracuseStep 941039 = 1411559) B1411559
theorem B2383465 : Blo 626299 2383465 := bstep (se 2 (by rfl) ⟨893799, by rfl⟩ : syracuseStep 2383465 = 1787599) B1787599
theorem B310239071 : Blo 626299 310239071 := bstep (se 1 (by rfl) ⟨232679303, by rfl⟩ : syracuseStep 310239071 = 465358607) B465358607
theorem B5103935 : Blo 626299 5103935 := bstep (se 1 (by rfl) ⟨3827951, by rfl⟩ : syracuseStep 5103935 = 7655903) B7655903
theorem B2384255 : Blo 626299 2384255 := bstep (se 1 (by rfl) ⟨1788191, by rfl⟩ : syracuseStep 2384255 = 3576383) B3576383
theorem B942683 : Blo 626299 942683 := bstep (se 1 (by rfl) ⟨707012, by rfl⟩ : syracuseStep 942683 = 1414025) B1414025
theorem B942761 : Blo 626299 942761 := bstep (se 2 (by rfl) ⟨353535, by rfl⟩ : syracuseStep 942761 = 707071) B707071
theorem B2384923 : Blo 626299 2384923 := bstep (se 1 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 2384923 = 3577385) B3577385
theorem B1271143 : Blo 626299 1271143 := bstep (se 1 (by rfl) ⟨953357, by rfl⟩ : syracuseStep 1271143 = 1906715) B1906715
theorem B944831 : Blo 626299 944831 := bstep (se 1 (by rfl) ⟨708623, by rfl⟩ : syracuseStep 944831 = 1417247) B1417247
theorem B4516559 : Blo 626299 4516559 := bstep (se 1 (by rfl) ⟨3387419, by rfl⟩ : syracuseStep 4516559 = 6774839) B6774839
theorem B945023 : Blo 626299 945023 := bstep (se 1 (by rfl) ⟨708767, by rfl⟩ : syracuseStep 945023 = 1417535) B1417535
theorem B15494759 : Blo 626299 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B2388143 : Blo 626299 2388143 := bstep (se 1 (by rfl) ⟨1791107, by rfl⟩ : syracuseStep 2388143 = 3582215) B3582215
theorem B3013499 : Blo 626299 3013499 := bstep (se 1 (by rfl) ⟨2260124, by rfl⟩ : syracuseStep 3013499 = 4520249) B4520249
theorem B1342631 : Blo 626299 1342631 := bstep (se 1 (by rfl) ⟨1006973, by rfl⟩ : syracuseStep 1342631 = 2013947) B2013947
theorem B5111201 : Blo 626299 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B1507663 : Blo 626299 1507663 := bstep (se 1 (by rfl) ⟨1130747, by rfl⟩ : syracuseStep 1507663 = 2261495) B2261495
theorem B1409705 : Blo 626299 1409705 := bstep (se 2 (by rfl) ⟨528639, by rfl⟩ : syracuseStep 1409705 = 1057279) B1057279
theorem B1410425 : Blo 626299 1410425 := bstep (se 2 (by rfl) ⟨528909, by rfl⟩ : syracuseStep 1410425 = 1057819) B1057819
theorem B3179897 : Blo 626299 3179897 := bstep (se 2 (by rfl) ⟨1192461, by rfl⟩ : syracuseStep 3179897 = 2384923) B2384923
theorem B756335 : Blo 626299 756335 := bstep (se 1 (by rfl) ⟨567251, by rfl⟩ : syracuseStep 756335 = 1134503) B1134503
theorem B3181679 : Blo 626299 3181679 := bstep (se 1 (by rfl) ⟨2386259, by rfl⟩ : syracuseStep 3181679 = 4772519) B4772519
theorem B7147115 : Blo 626299 7147115 := bstep (se 1 (by rfl) ⟨5360336, by rfl⟩ : syracuseStep 7147115 = 10720673) B10720673
theorem B1412729 : Blo 626299 1412729 := bstep (se 2 (by rfl) ⟨529773, by rfl⟩ : syracuseStep 1412729 = 1059547) B1059547
theorem B627167 : Blo 626299 627167 := bstep (se 1 (by rfl) ⟨470375, by rfl⟩ : syracuseStep 627167 = 940751) B940751
theorem B627359 : Blo 626299 627359 := bstep (se 1 (by rfl) ⟨470519, by rfl⟩ : syracuseStep 627359 = 941039) B941039
theorem B628455 : Blo 626299 628455 := bstep (se 1 (by rfl) ⟨471341, by rfl⟩ : syracuseStep 628455 = 942683) B942683
theorem B628507 : Blo 626299 628507 := bstep (se 1 (by rfl) ⟨471380, by rfl⟩ : syracuseStep 628507 = 942761) B942761
theorem B5085929 : Blo 626299 5085929 := bstep (se 2 (by rfl) ⟨1907223, by rfl⟩ : syracuseStep 5085929 = 3814447) B3814447
theorem B629887 : Blo 626299 629887 := bstep (se 1 (by rfl) ⟨472415, by rfl⟩ : syracuseStep 629887 = 944831) B944831
theorem B630015 : Blo 626299 630015 := bstep (se 1 (by rfl) ⟨472511, by rfl⟩ : syracuseStep 630015 = 945023) B945023
theorem B10329839 : Blo 626299 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B2008999 : Blo 626299 2008999 := bstep (se 1 (by rfl) ⟨1506749, by rfl⟩ : syracuseStep 2008999 = 3013499) B3013499
theorem B895087 : Blo 626299 895087 := bstep (se 1 (by rfl) ⟨671315, by rfl⟩ : syracuseStep 895087 = 1342631) B1342631
theorem B3814543 : Blo 626299 3814543 := bstep (se 1 (by rfl) ⟨2860907, by rfl⟩ : syracuseStep 3814543 = 5721815) B5721815
theorem B1062335 : Blo 626299 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B1589503 : Blo 626299 1589503 := bstep (se 1 (by rfl) ⟨1192127, by rfl⟩ : syracuseStep 1589503 = 2384255) B2384255
theorem B26462153 : Blo 626299 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B1592095 : Blo 626299 1592095 := bstep (se 1 (by rfl) ⟨1194071, by rfl⟩ : syracuseStep 1592095 = 2388143) B2388143
theorem B5229521 : Blo 626299 5229521 := bstep (se 2 (by rfl) ⟨1961070, by rfl⟩ : syracuseStep 5229521 = 3922141) B3922141
theorem B939785 : Blo 626299 939785 := bstep (se 2 (by rfl) ⟨352419, by rfl⟩ : syracuseStep 939785 = 704839) B704839
theorem B3922103 : Blo 626299 3922103 := bstep (se 1 (by rfl) ⟨2941577, by rfl⟩ : syracuseStep 3922103 = 5883155) B5883155
theorem B940511 : Blo 626299 940511 := bstep (se 1 (by rfl) ⟨705383, by rfl⟩ : syracuseStep 940511 = 1410767) B1410767
theorem B1694857 : Blo 626299 1694857 := bstep (se 2 (by rfl) ⟨635571, by rfl⟩ : syracuseStep 1694857 = 1271143) B1271143
theorem B942023 : Blo 626299 942023 := bstep (se 1 (by rfl) ⟨706517, by rfl⟩ : syracuseStep 942023 = 1413035) B1413035
theorem B942107 : Blo 626299 942107 := bstep (se 1 (by rfl) ⟨706580, by rfl⟩ : syracuseStep 942107 = 1413161) B1413161
theorem B943097 : Blo 626299 943097 := bstep (se 2 (by rfl) ⟨353661, by rfl⟩ : syracuseStep 943097 = 707323) B707323
theorem B943583 : Blo 626299 943583 := bstep (se 1 (by rfl) ⟨707687, by rfl⟩ : syracuseStep 943583 = 1415375) B1415375
theorem B206826047 : Blo 626299 206826047 := bstep (se 1 (by rfl) ⟨155119535, by rfl⟩ : syracuseStep 206826047 = 310239071) B310239071
theorem B944999 : Blo 626299 944999 := bstep (se 1 (by rfl) ⟨708749, by rfl⟩ : syracuseStep 944999 = 1417499) B1417499
theorem B3402623 : Blo 626299 3402623 := bstep (se 1 (by rfl) ⟨2551967, by rfl⟩ : syracuseStep 3402623 = 5103935) B5103935
theorem B3011039 : Blo 626299 3011039 := bstep (se 1 (by rfl) ⟨2258279, by rfl⟩ : syracuseStep 3011039 = 4516559) B4516559
theorem B3177953 : Blo 626299 3177953 := bstep (se 2 (by rfl) ⟨1191732, by rfl⟩ : syracuseStep 3177953 = 2383465) B2383465
theorem B3407467 : Blo 626299 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B626523 : Blo 626299 626523 := bstep (se 1 (by rfl) ⟨469892, by rfl⟩ : syracuseStep 626523 = 939785) B939785
theorem B627007 : Blo 626299 627007 := bstep (se 1 (by rfl) ⟨470255, by rfl⟩ : syracuseStep 627007 = 940511) B940511
theorem B6886559 : Blo 626299 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B628015 : Blo 626299 628015 := bstep (se 1 (by rfl) ⟨471011, by rfl⟩ : syracuseStep 628015 = 942023) B942023
theorem B628071 : Blo 626299 628071 := bstep (se 1 (by rfl) ⟨471053, by rfl⟩ : syracuseStep 628071 = 942107) B942107
theorem B628731 : Blo 626299 628731 := bstep (se 1 (by rfl) ⟨471548, by rfl⟩ : syracuseStep 628731 = 943097) B943097
theorem B629055 : Blo 626299 629055 := bstep (se 1 (by rfl) ⟨471791, by rfl⟩ : syracuseStep 629055 = 943583) B943583
theorem B5086057 : Blo 626299 5086057 := bstep (se 2 (by rfl) ⟨1907271, by rfl⟩ : syracuseStep 5086057 = 3814543) B3814543
theorem B629999 : Blo 626299 629999 := bstep (se 1 (by rfl) ⟨472499, by rfl⟩ : syracuseStep 629999 = 944999) B944999
theorem B2268415 : Blo 626299 2268415 := bstep (se 1 (by rfl) ⟨1701311, by rfl⟩ : syracuseStep 2268415 = 3402623) B3402623
theorem B2007359 : Blo 626299 2007359 := bstep (se 1 (by rfl) ⟨1505519, by rfl⟩ : syracuseStep 2007359 = 3011039) B3011039
theorem B8040869 : Blo 626299 8040869 := bstep (se 4 (by rfl) ⟨753831, by rfl⟩ : syracuseStep 8040869 = 1507663) B1507663
theorem B3486347 : Blo 626299 3486347 := bstep (se 1 (by rfl) ⟨2614760, by rfl⟩ : syracuseStep 3486347 = 5229521) B5229521
theorem B4764743 : Blo 626299 4764743 := bstep (se 1 (by rfl) ⟨3573557, by rfl⟩ : syracuseStep 4764743 = 7147115) B7147115
theorem B1193449 : Blo 626299 1193449 := bstep (se 2 (by rfl) ⟨447543, by rfl⟩ : syracuseStep 1193449 = 895087) B895087
theorem B70565741 : Blo 626299 70565741 := bstep (se 3 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 70565741 = 26462153) B26462153
theorem B2016893 : Blo 626299 2016893 := bstep (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) B756335
theorem B708223 : Blo 626299 708223 := bstep (se 1 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 708223 = 1062335) B1062335
theorem B4543289 : Blo 626299 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B2118635 : Blo 626299 2118635 := bstep (se 1 (by rfl) ⟨1588976, by rfl⟩ : syracuseStep 2118635 = 3177953) B3177953
theorem B2119337 : Blo 626299 2119337 := bstep (se 2 (by rfl) ⟨794751, by rfl⟩ : syracuseStep 2119337 = 1589503) B1589503
theorem B939803 : Blo 626299 939803 := bstep (se 1 (by rfl) ⟨704852, by rfl⟩ : syracuseStep 939803 = 1409705) B1409705
theorem B940283 : Blo 626299 940283 := bstep (se 1 (by rfl) ⟨705212, by rfl⟩ : syracuseStep 940283 = 1410425) B1410425
theorem B2119931 : Blo 626299 2119931 := bstep (se 1 (by rfl) ⟨1589948, by rfl⟩ : syracuseStep 2119931 = 3179897) B3179897
theorem B2121119 : Blo 626299 2121119 := bstep (se 1 (by rfl) ⟨1590839, by rfl⟩ : syracuseStep 2121119 = 3181679) B3181679
theorem B941819 : Blo 626299 941819 := bstep (se 1 (by rfl) ⟨706364, by rfl⟩ : syracuseStep 941819 = 1412729) B1412729
theorem B2678665 : Blo 626299 2678665 := bstep (se 2 (by rfl) ⟨1004499, by rfl⟩ : syracuseStep 2678665 = 2008999) B2008999
theorem B2122793 : Blo 626299 2122793 := bstep (se 2 (by rfl) ⟨796047, by rfl⟩ : syracuseStep 2122793 = 1592095) B1592095
theorem B2614735 : Blo 626299 2614735 := bstep (se 1 (by rfl) ⟨1961051, by rfl⟩ : syracuseStep 2614735 = 3922103) B3922103
theorem B137884031 : Blo 626299 137884031 := bstep (se 1 (by rfl) ⟨103413023, by rfl⟩ : syracuseStep 137884031 = 206826047) B206826047
theorem B13562477 : Blo 626299 13562477 := bstep (se 3 (by rfl) ⟨2542964, by rfl⟩ : syracuseStep 13562477 = 5085929) B5085929
theorem B2259809 : Blo 626299 2259809 := bstep (se 2 (by rfl) ⟨847428, by rfl⟩ : syracuseStep 2259809 = 1694857) B1694857
theorem B1344595 : Blo 626299 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B1412423 : Blo 626299 1412423 := bstep (se 1 (by rfl) ⟨1059317, by rfl⟩ : syracuseStep 1412423 = 2118635) B2118635
theorem B1412891 : Blo 626299 1412891 := bstep (se 1 (by rfl) ⟨1059668, by rfl⟩ : syracuseStep 1412891 = 2119337) B2119337
theorem B626535 : Blo 626299 626535 := bstep (se 1 (by rfl) ⟨469901, by rfl⟩ : syracuseStep 626535 = 939803) B939803
theorem B626855 : Blo 626299 626855 := bstep (se 1 (by rfl) ⟨470141, by rfl⟩ : syracuseStep 626855 = 940283) B940283
theorem B1413287 : Blo 626299 1413287 := bstep (se 1 (by rfl) ⟨1059965, by rfl⟩ : syracuseStep 1413287 = 2119931) B2119931
theorem B1414079 : Blo 626299 1414079 := bstep (se 1 (by rfl) ⟨1060559, by rfl⟩ : syracuseStep 1414079 = 2121119) B2121119
theorem B627879 : Blo 626299 627879 := bstep (se 1 (by rfl) ⟨470909, by rfl⟩ : syracuseStep 627879 = 941819) B941819
theorem B1415195 : Blo 626299 1415195 := bstep (se 1 (by rfl) ⟨1061396, by rfl⟩ : syracuseStep 1415195 = 2122793) B2122793
theorem B91922687 : Blo 626299 91922687 := bstep (se 1 (by rfl) ⟨68942015, by rfl⟩ : syracuseStep 91922687 = 137884031) B137884031
theorem B3024553 : Blo 626299 3024553 := bstep (se 2 (by rfl) ⟨1134207, by rfl⟩ : syracuseStep 3024553 = 2268415) B2268415
theorem B3486313 : Blo 626299 3486313 := bstep (se 2 (by rfl) ⟨1307367, by rfl⟩ : syracuseStep 3486313 = 2614735) B2614735
theorem B18364157 : Blo 626299 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B3028859 : Blo 626299 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B148750805 : Blo 626299 148750805 := bstep (se 7 (by rfl) ⟨1743173, by rfl⟩ : syracuseStep 148750805 = 3486347) B3486347
theorem B1591265 : Blo 626299 1591265 := bstep (se 2 (by rfl) ⟨596724, by rfl⟩ : syracuseStep 1591265 = 1193449) B1193449
theorem B5360579 : Blo 626299 5360579 := bstep (se 1 (by rfl) ⟨4020434, by rfl⟩ : syracuseStep 5360579 = 8040869) B8040869
theorem B47043827 : Blo 626299 47043827 := bstep (se 1 (by rfl) ⟨35282870, by rfl⟩ : syracuseStep 47043827 = 70565741) B70565741
theorem B944297 : Blo 626299 944297 := bstep (se 2 (by rfl) ⟨354111, by rfl⟩ : syracuseStep 944297 = 708223) B708223
theorem B1338239 : Blo 626299 1338239 := bstep (se 1 (by rfl) ⟨1003679, by rfl⟩ : syracuseStep 1338239 = 2007359) B2007359
theorem B9041651 : Blo 626299 9041651 := bstep (se 1 (by rfl) ⟨6781238, by rfl⟩ : syracuseStep 9041651 = 13562477) B13562477
theorem B3176495 : Blo 626299 3176495 := bstep (se 1 (by rfl) ⟨2382371, by rfl⟩ : syracuseStep 3176495 = 4764743) B4764743
theorem B6781409 : Blo 626299 6781409 := bstep (se 2 (by rfl) ⟨2543028, by rfl⟩ : syracuseStep 6781409 = 5086057) B5086057
theorem B1506539 : Blo 626299 1506539 := bstep (se 1 (by rfl) ⟨1129904, by rfl⟩ : syracuseStep 1506539 = 2259809) B2259809
theorem B3571553 : Blo 626299 3571553 := bstep (se 2 (by rfl) ⟨1339332, by rfl⟩ : syracuseStep 3571553 = 2678665) B2678665
theorem B3573719 : Blo 626299 3573719 := bstep (se 1 (by rfl) ⟨2680289, by rfl⟩ : syracuseStep 3573719 = 5360579) B5360579
theorem B4032737 : Blo 626299 4032737 := bstep (se 2 (by rfl) ⟨1512276, by rfl⟩ : syracuseStep 4032737 = 3024553) B3024553
theorem B31362551 : Blo 626299 31362551 := bstep (se 1 (by rfl) ⟨23521913, by rfl⟩ : syracuseStep 31362551 = 47043827) B47043827
theorem B61281791 : Blo 626299 61281791 := bstep (se 1 (by rfl) ⟨45961343, by rfl⟩ : syracuseStep 61281791 = 91922687) B91922687
theorem B629531 : Blo 626299 629531 := bstep (se 1 (by rfl) ⟨472148, by rfl⟩ : syracuseStep 629531 = 944297) B944297
theorem B99167203 : Blo 626299 99167203 := bstep (se 1 (by rfl) ⟨74375402, by rfl⟩ : syracuseStep 99167203 = 148750805) B148750805
theorem B1060843 : Blo 626299 1060843 := bstep (se 1 (by rfl) ⟨795632, by rfl⟩ : syracuseStep 1060843 = 1591265) B1591265
theorem B4017437 : Blo 626299 4017437 := bstep (se 3 (by rfl) ⟨753269, by rfl⟩ : syracuseStep 4017437 = 1506539) B1506539
theorem B12242771 : Blo 626299 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B2019239 : Blo 626299 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B2117663 : Blo 626299 2117663 := bstep (se 1 (by rfl) ⟨1588247, by rfl⟩ : syracuseStep 2117663 = 3176495) B3176495
theorem B2381035 : Blo 626299 2381035 := bstep (se 1 (by rfl) ⟨1785776, by rfl⟩ : syracuseStep 2381035 = 3571553) B3571553
theorem B1792793 : Blo 626299 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B941615 : Blo 626299 941615 := bstep (se 1 (by rfl) ⟨706211, by rfl⟩ : syracuseStep 941615 = 1412423) B1412423
theorem B941927 : Blo 626299 941927 := bstep (se 1 (by rfl) ⟨706445, by rfl⟩ : syracuseStep 941927 = 1412891) B1412891
theorem B942191 : Blo 626299 942191 := bstep (se 1 (by rfl) ⟨706643, by rfl⟩ : syracuseStep 942191 = 1413287) B1413287
theorem B942719 : Blo 626299 942719 := bstep (se 1 (by rfl) ⟨707039, by rfl⟩ : syracuseStep 942719 = 1414079) B1414079
theorem B943463 : Blo 626299 943463 := bstep (se 1 (by rfl) ⟨707597, by rfl⟩ : syracuseStep 943463 = 1415195) B1415195
theorem B4648417 : Blo 626299 4648417 := bstep (se 2 (by rfl) ⟨1743156, by rfl⟩ : syracuseStep 4648417 = 3486313) B3486313
theorem B3568637 : Blo 626299 3568637 := bstep (se 3 (by rfl) ⟨669119, by rfl⟩ : syracuseStep 3568637 = 1338239) B1338239
theorem B6027767 : Blo 626299 6027767 := bstep (se 1 (by rfl) ⟨4520825, by rfl⟩ : syracuseStep 6027767 = 9041651) B9041651
theorem B4520939 : Blo 626299 4520939 := bstep (se 1 (by rfl) ⟨3390704, by rfl⟩ : syracuseStep 4520939 = 6781409) B6781409
theorem B2688491 : Blo 626299 2688491 := bstep (se 1 (by rfl) ⟨2016368, by rfl⟩ : syracuseStep 2688491 = 4032737) B4032737
theorem B20908367 : Blo 626299 20908367 := bstep (se 1 (by rfl) ⟨15681275, by rfl⟩ : syracuseStep 20908367 = 31362551) B31362551
theorem B8161847 : Blo 626299 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B1346159 : Blo 626299 1346159 := bstep (se 1 (by rfl) ⟨1009619, by rfl⟩ : syracuseStep 1346159 = 2019239) B2019239
theorem B1411775 : Blo 626299 1411775 := bstep (se 1 (by rfl) ⟨1058831, by rfl⟩ : syracuseStep 1411775 = 2117663) B2117663
theorem B132222937 : Blo 626299 132222937 := bstep (se 2 (by rfl) ⟨49583601, by rfl⟩ : syracuseStep 132222937 = 99167203) B99167203
theorem B627743 : Blo 626299 627743 := bstep (se 1 (by rfl) ⟨470807, by rfl⟩ : syracuseStep 627743 = 941615) B941615
theorem B627951 : Blo 626299 627951 := bstep (se 1 (by rfl) ⟨470963, by rfl⟩ : syracuseStep 627951 = 941927) B941927
theorem B1414457 : Blo 626299 1414457 := bstep (se 2 (by rfl) ⟨530421, by rfl⟩ : syracuseStep 1414457 = 1060843) B1060843
theorem B628127 : Blo 626299 628127 := bstep (se 1 (by rfl) ⟨471095, by rfl⟩ : syracuseStep 628127 = 942191) B942191
theorem B628479 : Blo 626299 628479 := bstep (se 1 (by rfl) ⟨471359, by rfl⟩ : syracuseStep 628479 = 942719) B942719
theorem B628975 : Blo 626299 628975 := bstep (se 1 (by rfl) ⟨471731, by rfl⟩ : syracuseStep 628975 = 943463) B943463
theorem B24791557 : Blo 626299 24791557 := bstep (se 4 (by rfl) ⟨2324208, by rfl⟩ : syracuseStep 24791557 = 4648417) B4648417
theorem B2379091 : Blo 626299 2379091 := bstep (se 1 (by rfl) ⟨1784318, by rfl⟩ : syracuseStep 2379091 = 3568637) B3568637
theorem B4018511 : Blo 626299 4018511 := bstep (se 1 (by rfl) ⟨3013883, by rfl⟩ : syracuseStep 4018511 = 6027767) B6027767
theorem B2382479 : Blo 626299 2382479 := bstep (se 1 (by rfl) ⟨1786859, by rfl⟩ : syracuseStep 2382479 = 3573719) B3573719
theorem B2678291 : Blo 626299 2678291 := bstep (se 1 (by rfl) ⟨2008718, by rfl⟩ : syracuseStep 2678291 = 4017437) B4017437
theorem B40854527 : Blo 626299 40854527 := bstep (se 1 (by rfl) ⟨30640895, by rfl⟩ : syracuseStep 40854527 = 61281791) B61281791
theorem B3174713 : Blo 626299 3174713 := bstep (se 2 (by rfl) ⟨1190517, by rfl⟩ : syracuseStep 3174713 = 2381035) B2381035
theorem B4780781 : Blo 626299 4780781 := bstep (se 3 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 4780781 = 1792793) B1792793
theorem B12055837 : Blo 626299 12055837 := bstep (se 3 (by rfl) ⟨2260469, by rfl⟩ : syracuseStep 12055837 = 4520939) B4520939
theorem B5441231 : Blo 626299 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B176297249 : Blo 626299 176297249 := bstep (se 2 (by rfl) ⟨66111468, by rfl⟩ : syracuseStep 176297249 = 132222937) B132222937
theorem B27236351 : Blo 626299 27236351 := bstep (se 1 (by rfl) ⟨20427263, by rfl⟩ : syracuseStep 27236351 = 40854527) B40854527
theorem B3187187 : Blo 626299 3187187 := bstep (se 1 (by rfl) ⟨2390390, by rfl⟩ : syracuseStep 3187187 = 4780781) B4780781
theorem B13938911 : Blo 626299 13938911 := bstep (se 1 (by rfl) ⟨10454183, by rfl⟩ : syracuseStep 13938911 = 20908367) B20908367
theorem B1588319 : Blo 626299 1588319 := bstep (se 1 (by rfl) ⟨1191239, by rfl⟩ : syracuseStep 1588319 = 2382479) B2382479
theorem B1785527 : Blo 626299 1785527 := bstep (se 1 (by rfl) ⟨1339145, by rfl⟩ : syracuseStep 1785527 = 2678291) B2678291
theorem B3589757 : Blo 626299 3589757 := bstep (se 3 (by rfl) ⟨673079, by rfl⟩ : syracuseStep 3589757 = 1346159) B1346159
theorem B16074449 : Blo 626299 16074449 := bstep (se 2 (by rfl) ⟨6027918, by rfl⟩ : syracuseStep 16074449 = 12055837) B12055837
theorem B2116475 : Blo 626299 2116475 := bstep (se 1 (by rfl) ⟨1587356, by rfl⟩ : syracuseStep 2116475 = 3174713) B3174713
theorem B1792327 : Blo 626299 1792327 := bstep (se 1 (by rfl) ⟨1344245, by rfl⟩ : syracuseStep 1792327 = 2688491) B2688491
theorem B941183 : Blo 626299 941183 := bstep (se 1 (by rfl) ⟨705887, by rfl⟩ : syracuseStep 941183 = 1411775) B1411775
theorem B2679007 : Blo 626299 2679007 := bstep (se 1 (by rfl) ⟨2009255, by rfl⟩ : syracuseStep 2679007 = 4018511) B4018511
theorem B33055409 : Blo 626299 33055409 := bstep (se 2 (by rfl) ⟨12395778, by rfl⟩ : syracuseStep 33055409 = 24791557) B24791557
theorem B942971 : Blo 626299 942971 := bstep (se 1 (by rfl) ⟨707228, by rfl⟩ : syracuseStep 942971 = 1414457) B1414457
theorem B3172121 : Blo 626299 3172121 := bstep (se 2 (by rfl) ⟨1189545, by rfl⟩ : syracuseStep 3172121 = 2379091) B2379091
theorem B3572009 : Blo 626299 3572009 := bstep (se 2 (by rfl) ⟨1339503, by rfl⟩ : syracuseStep 3572009 = 2679007) B2679007
theorem B2393171 : Blo 626299 2393171 := bstep (se 1 (by rfl) ⟨1794878, by rfl⟩ : syracuseStep 2393171 = 3589757) B3589757
theorem B10716299 : Blo 626299 10716299 := bstep (se 1 (by rfl) ⟨8037224, by rfl⟩ : syracuseStep 10716299 = 16074449) B16074449
theorem B88147757 : Blo 626299 88147757 := bstep (se 3 (by rfl) ⟨16527704, by rfl⟩ : syracuseStep 88147757 = 33055409) B33055409
theorem B1410983 : Blo 626299 1410983 := bstep (se 1 (by rfl) ⟨1058237, by rfl⟩ : syracuseStep 1410983 = 2116475) B2116475
theorem B18157567 : Blo 626299 18157567 := bstep (se 1 (by rfl) ⟨13618175, by rfl⟩ : syracuseStep 18157567 = 27236351) B27236351
theorem B627455 : Blo 626299 627455 := bstep (se 1 (by rfl) ⟨470591, by rfl⟩ : syracuseStep 627455 = 941183) B941183
theorem B628647 : Blo 626299 628647 := bstep (se 1 (by rfl) ⟨471485, by rfl⟩ : syracuseStep 628647 = 942971) B942971
theorem B1058879 : Blo 626299 1058879 := bstep (se 1 (by rfl) ⟨794159, by rfl⟩ : syracuseStep 1058879 = 1588319) B1588319
theorem B1190351 : Blo 626299 1190351 := bstep (se 1 (by rfl) ⟨892763, by rfl⟩ : syracuseStep 1190351 = 1785527) B1785527
theorem B2114747 : Blo 626299 2114747 := bstep (se 1 (by rfl) ⟨1586060, by rfl⟩ : syracuseStep 2114747 = 3172121) B3172121
theorem B9292607 : Blo 626299 9292607 := bstep (se 1 (by rfl) ⟨6969455, by rfl⟩ : syracuseStep 9292607 = 13938911) B13938911
theorem B3627487 : Blo 626299 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B117531499 : Blo 626299 117531499 := bstep (se 1 (by rfl) ⟨88148624, by rfl⟩ : syracuseStep 117531499 = 176297249) B176297249
theorem B2124791 : Blo 626299 2124791 := bstep (se 1 (by rfl) ⟨1593593, by rfl⟩ : syracuseStep 2124791 = 3187187) B3187187
theorem B2389769 : Blo 626299 2389769 := bstep (se 2 (by rfl) ⟨896163, by rfl⟩ : syracuseStep 2389769 = 1792327) B1792327
theorem B7144199 : Blo 626299 7144199 := bstep (se 1 (by rfl) ⟨5358149, by rfl⟩ : syracuseStep 7144199 = 10716299) B10716299
theorem B1409831 : Blo 626299 1409831 := bstep (se 1 (by rfl) ⟨1057373, by rfl⟩ : syracuseStep 1409831 = 2114747) B2114747
theorem B6195071 : Blo 626299 6195071 := bstep (se 1 (by rfl) ⟨4646303, by rfl⟩ : syracuseStep 6195071 = 9292607) B9292607
theorem B793567 : Blo 626299 793567 := bstep (se 1 (by rfl) ⟨595175, by rfl⟩ : syracuseStep 793567 = 1190351) B1190351
theorem B1416527 : Blo 626299 1416527 := bstep (se 1 (by rfl) ⟨1062395, by rfl⟩ : syracuseStep 1416527 = 2124791) B2124791
theorem B156708665 : Blo 626299 156708665 := bstep (se 2 (by rfl) ⟨58765749, by rfl⟩ : syracuseStep 156708665 = 117531499) B117531499
theorem B58765171 : Blo 626299 58765171 := bstep (se 1 (by rfl) ⟨44073878, by rfl⟩ : syracuseStep 58765171 = 88147757) B88147757
theorem B19346597 : Blo 626299 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B705919 : Blo 626299 705919 := bstep (se 1 (by rfl) ⟨529439, by rfl⟩ : syracuseStep 705919 = 1058879) B1058879
theorem B1593179 : Blo 626299 1593179 := bstep (se 1 (by rfl) ⟨1194884, by rfl⟩ : syracuseStep 1593179 = 2389769) B2389769
theorem B2381339 : Blo 626299 2381339 := bstep (se 1 (by rfl) ⟨1786004, by rfl⟩ : syracuseStep 2381339 = 3572009) B3572009
theorem B1595447 : Blo 626299 1595447 := bstep (se 1 (by rfl) ⟨1196585, by rfl⟩ : syracuseStep 1595447 = 2393171) B2393171
theorem B940655 : Blo 626299 940655 := bstep (se 1 (by rfl) ⟨705491, by rfl⟩ : syracuseStep 940655 = 1410983) B1410983
theorem B24210089 : Blo 626299 24210089 := bstep (se 2 (by rfl) ⟨9078783, by rfl⟩ : syracuseStep 24210089 = 18157567) B18157567
theorem B4130047 : Blo 626299 4130047 := bstep (se 1 (by rfl) ⟨3097535, by rfl⟩ : syracuseStep 4130047 = 6195071) B6195071
theorem B627103 : Blo 626299 627103 := bstep (se 1 (by rfl) ⟨470327, by rfl⟩ : syracuseStep 627103 = 940655) B940655
theorem B78353561 : Blo 626299 78353561 := bstep (se 2 (by rfl) ⟨29382585, by rfl⟩ : syracuseStep 78353561 = 58765171) B58765171
theorem B104472443 : Blo 626299 104472443 := bstep (se 1 (by rfl) ⟨78354332, by rfl⟩ : syracuseStep 104472443 = 156708665) B156708665
theorem B1058089 : Blo 626299 1058089 := bstep (se 2 (by rfl) ⟨396783, by rfl⟩ : syracuseStep 1058089 = 793567) B793567
theorem B4762799 : Blo 626299 4762799 := bstep (se 1 (by rfl) ⟨3572099, by rfl⟩ : syracuseStep 4762799 = 7144199) B7144199
theorem B1062119 : Blo 626299 1062119 := bstep (se 1 (by rfl) ⟨796589, by rfl⟩ : syracuseStep 1062119 = 1593179) B1593179
theorem B1587559 : Blo 626299 1587559 := bstep (se 1 (by rfl) ⟨1190669, by rfl⟩ : syracuseStep 1587559 = 2381339) B2381339
theorem B1063631 : Blo 626299 1063631 := bstep (se 1 (by rfl) ⟨797723, by rfl⟩ : syracuseStep 1063631 = 1595447) B1595447
theorem B16140059 : Blo 626299 16140059 := bstep (se 1 (by rfl) ⟨12105044, by rfl⟩ : syracuseStep 16140059 = 24210089) B24210089
theorem B12897731 : Blo 626299 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B939887 : Blo 626299 939887 := bstep (se 1 (by rfl) ⟨704915, by rfl⟩ : syracuseStep 939887 = 1409831) B1409831
theorem B941225 : Blo 626299 941225 := bstep (se 2 (by rfl) ⟨352959, by rfl⟩ : syracuseStep 941225 = 705919) B705919
theorem B944351 : Blo 626299 944351 := bstep (se 1 (by rfl) ⟨708263, by rfl⟩ : syracuseStep 944351 = 1416527) B1416527
theorem B1410785 : Blo 626299 1410785 := bstep (se 2 (by rfl) ⟨529044, by rfl⟩ : syracuseStep 1410785 = 1058089) B1058089
theorem B52235707 : Blo 626299 52235707 := bstep (se 1 (by rfl) ⟨39176780, by rfl⟩ : syracuseStep 52235707 = 78353561) B78353561
theorem B626591 : Blo 626299 626591 := bstep (se 1 (by rfl) ⟨469943, by rfl⟩ : syracuseStep 626591 = 939887) B939887
theorem B627483 : Blo 626299 627483 := bstep (se 1 (by rfl) ⟨470612, by rfl⟩ : syracuseStep 627483 = 941225) B941225
theorem B22026917 : Blo 626299 22026917 := bstep (se 4 (by rfl) ⟨2065023, by rfl⟩ : syracuseStep 22026917 = 4130047) B4130047
theorem B629567 : Blo 626299 629567 := bstep (se 1 (by rfl) ⟨472175, by rfl⟩ : syracuseStep 629567 = 944351) B944351
theorem B10760039 : Blo 626299 10760039 := bstep (se 1 (by rfl) ⟨8070029, by rfl⟩ : syracuseStep 10760039 = 16140059) B16140059
theorem B8598487 : Blo 626299 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B2116745 : Blo 626299 2116745 := bstep (se 2 (by rfl) ⟨793779, by rfl⟩ : syracuseStep 2116745 = 1587559) B1587559
theorem B708079 : Blo 626299 708079 := bstep (se 1 (by rfl) ⟨531059, by rfl⟩ : syracuseStep 708079 = 1062119) B1062119
theorem B709087 : Blo 626299 709087 := bstep (se 1 (by rfl) ⟨531815, by rfl⟩ : syracuseStep 709087 = 1063631) B1063631
theorem B3175199 : Blo 626299 3175199 := bstep (se 1 (by rfl) ⟨2381399, by rfl⟩ : syracuseStep 3175199 = 4762799) B4762799
theorem B278593181 : Blo 626299 278593181 := bstep (se 3 (by rfl) ⟨52236221, by rfl⟩ : syracuseStep 278593181 = 104472443) B104472443
theorem B1411163 : Blo 626299 1411163 := bstep (se 1 (by rfl) ⟨1058372, by rfl⟩ : syracuseStep 1411163 = 2116745) B2116745
theorem B14684611 : Blo 626299 14684611 := bstep (se 1 (by rfl) ⟨11013458, by rfl⟩ : syracuseStep 14684611 = 22026917) B22026917
theorem B69647609 : Blo 626299 69647609 := bstep (se 2 (by rfl) ⟨26117853, by rfl⟩ : syracuseStep 69647609 = 52235707) B52235707
theorem B2116799 : Blo 626299 2116799 := bstep (se 1 (by rfl) ⟨1587599, by rfl⟩ : syracuseStep 2116799 = 3175199) B3175199
theorem B940523 : Blo 626299 940523 := bstep (se 1 (by rfl) ⟨705392, by rfl⟩ : syracuseStep 940523 = 1410785) B1410785
theorem B944105 : Blo 626299 944105 := bstep (se 2 (by rfl) ⟨354039, by rfl⟩ : syracuseStep 944105 = 708079) B708079
theorem B945449 : Blo 626299 945449 := bstep (se 2 (by rfl) ⟨354543, by rfl⟩ : syracuseStep 945449 = 709087) B709087
theorem B11464649 : Blo 626299 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B7173359 : Blo 626299 7173359 := bstep (se 1 (by rfl) ⟨5380019, by rfl⟩ : syracuseStep 7173359 = 10760039) B10760039
theorem B185728787 : Blo 626299 185728787 := bstep (se 1 (by rfl) ⟨139296590, by rfl⟩ : syracuseStep 185728787 = 278593181) B278593181
theorem B1411199 : Blo 626299 1411199 := bstep (se 1 (by rfl) ⟨1058399, by rfl⟩ : syracuseStep 1411199 = 2116799) B2116799
theorem B627015 : Blo 626299 627015 := bstep (se 1 (by rfl) ⟨470261, by rfl⟩ : syracuseStep 627015 = 940523) B940523
theorem B629403 : Blo 626299 629403 := bstep (se 1 (by rfl) ⟨472052, by rfl⟩ : syracuseStep 629403 = 944105) B944105
theorem B630299 : Blo 626299 630299 := bstep (se 1 (by rfl) ⟨472724, by rfl⟩ : syracuseStep 630299 = 945449) B945449
theorem B7643099 : Blo 626299 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B19579481 : Blo 626299 19579481 := bstep (se 2 (by rfl) ⟨7342305, by rfl⟩ : syracuseStep 19579481 = 14684611) B14684611
theorem B123819191 : Blo 626299 123819191 := bstep (se 1 (by rfl) ⟨92864393, by rfl⟩ : syracuseStep 123819191 = 185728787) B185728787
theorem B940775 : Blo 626299 940775 := bstep (se 1 (by rfl) ⟨705581, by rfl⟩ : syracuseStep 940775 = 1411163) B1411163
theorem B4782239 : Blo 626299 4782239 := bstep (se 1 (by rfl) ⟨3586679, by rfl⟩ : syracuseStep 4782239 = 7173359) B7173359
theorem B46431739 : Blo 626299 46431739 := bstep (se 1 (by rfl) ⟨34823804, by rfl⟩ : syracuseStep 46431739 = 69647609) B69647609
theorem B82546127 : Blo 626299 82546127 := bstep (se 1 (by rfl) ⟨61909595, by rfl⟩ : syracuseStep 82546127 = 123819191) B123819191
theorem B627183 : Blo 626299 627183 := bstep (se 1 (by rfl) ⟨470387, by rfl⟩ : syracuseStep 627183 = 940775) B940775
theorem B3188159 : Blo 626299 3188159 := bstep (se 1 (by rfl) ⟨2391119, by rfl⟩ : syracuseStep 3188159 = 4782239) B4782239
theorem B61908985 : Blo 626299 61908985 := bstep (se 2 (by rfl) ⟨23215869, by rfl⟩ : syracuseStep 61908985 = 46431739) B46431739
theorem B13052987 : Blo 626299 13052987 := bstep (se 1 (by rfl) ⟨9789740, by rfl⟩ : syracuseStep 13052987 = 19579481) B19579481
theorem B5095399 : Blo 626299 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B940799 : Blo 626299 940799 := bstep (se 1 (by rfl) ⟨705599, by rfl⟩ : syracuseStep 940799 = 1411199) B1411199
theorem B82545313 : Blo 626299 82545313 := bstep (se 2 (by rfl) ⟨30954492, by rfl⟩ : syracuseStep 82545313 = 61908985) B61908985
theorem B627199 : Blo 626299 627199 := bstep (se 1 (by rfl) ⟨470399, by rfl⟩ : syracuseStep 627199 = 940799) B940799
theorem B6793865 : Blo 626299 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B55030751 : Blo 626299 55030751 := bstep (se 1 (by rfl) ⟨41273063, by rfl⟩ : syracuseStep 55030751 = 82546127) B82546127
theorem B8701991 : Blo 626299 8701991 := bstep (se 1 (by rfl) ⟨6526493, by rfl⟩ : syracuseStep 8701991 = 13052987) B13052987
theorem B2125439 : Blo 626299 2125439 := bstep (se 1 (by rfl) ⟨1594079, by rfl⟩ : syracuseStep 2125439 = 3188159) B3188159
theorem B5801327 : Blo 626299 5801327 := bstep (se 1 (by rfl) ⟨4350995, by rfl⟩ : syracuseStep 5801327 = 8701991) B8701991
theorem B4529243 : Blo 626299 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B1416959 : Blo 626299 1416959 := bstep (se 1 (by rfl) ⟨1062719, by rfl⟩ : syracuseStep 1416959 = 2125439) B2125439
theorem B36687167 : Blo 626299 36687167 := bstep (se 1 (by rfl) ⟨27515375, by rfl⟩ : syracuseStep 36687167 = 55030751) B55030751
theorem B110060417 : Blo 626299 110060417 := bstep (se 2 (by rfl) ⟨41272656, by rfl⟩ : syracuseStep 110060417 = 82545313) B82545313
theorem B3867551 : Blo 626299 3867551 := bstep (se 1 (by rfl) ⟨2900663, by rfl⟩ : syracuseStep 3867551 = 5801327) B5801327
theorem B73373611 : Blo 626299 73373611 := bstep (se 1 (by rfl) ⟨55030208, by rfl⟩ : syracuseStep 73373611 = 110060417) B110060417
theorem B24458111 : Blo 626299 24458111 := bstep (se 1 (by rfl) ⟨18343583, by rfl⟩ : syracuseStep 24458111 = 36687167) B36687167
theorem B12077981 : Blo 626299 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B944639 : Blo 626299 944639 := bstep (se 1 (by rfl) ⟨708479, by rfl⟩ : syracuseStep 944639 = 1416959) B1416959
theorem B629759 : Blo 626299 629759 := bstep (se 1 (by rfl) ⟨472319, by rfl⟩ : syracuseStep 629759 = 944639) B944639
theorem B97831481 : Blo 626299 97831481 := bstep (se 2 (by rfl) ⟨36686805, by rfl⟩ : syracuseStep 97831481 = 73373611) B73373611
theorem B16305407 : Blo 626299 16305407 := bstep (se 1 (by rfl) ⟨12229055, by rfl⟩ : syracuseStep 16305407 = 24458111) B24458111
theorem B8051987 : Blo 626299 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B41253877 : Blo 626299 41253877 := bstep (se 5 (by rfl) ⟨1933775, by rfl⟩ : syracuseStep 41253877 = 3867551) B3867551
theorem B1043535797 : Blo 626299 1043535797 := bstep (se 5 (by rfl) ⟨48915740, by rfl⟩ : syracuseStep 1043535797 = 97831481) B97831481
theorem B55005169 : Blo 626299 55005169 := bstep (se 2 (by rfl) ⟨20626938, by rfl⟩ : syracuseStep 55005169 = 41253877) B41253877
theorem B10870271 : Blo 626299 10870271 := bstep (se 1 (by rfl) ⟨8152703, by rfl⟩ : syracuseStep 10870271 = 16305407) B16305407
theorem B5367991 : Blo 626299 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B7246847 : Blo 626299 7246847 := bstep (se 1 (by rfl) ⟨5435135, by rfl⟩ : syracuseStep 7246847 = 10870271) B10870271
theorem B73340225 : Blo 626299 73340225 := bstep (se 2 (by rfl) ⟨27502584, by rfl⟩ : syracuseStep 73340225 = 55005169) B55005169
theorem B7157321 : Blo 626299 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B695690531 : Blo 626299 695690531 := bstep (se 1 (by rfl) ⟨521767898, by rfl⟩ : syracuseStep 695690531 = 1043535797) B1043535797
theorem B48893483 : Blo 626299 48893483 := bstep (se 1 (by rfl) ⟨36670112, by rfl⟩ : syracuseStep 48893483 = 73340225) B73340225
theorem B4771547 : Blo 626299 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B19324925 : Blo 626299 19324925 := bstep (se 3 (by rfl) ⟨3623423, by rfl⟩ : syracuseStep 19324925 = 7246847) B7246847
theorem B463793687 : Blo 626299 463793687 := bstep (se 1 (by rfl) ⟨347845265, by rfl⟩ : syracuseStep 463793687 = 695690531) B695690531
theorem B3181031 : Blo 626299 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B12883283 : Blo 626299 12883283 := bstep (se 1 (by rfl) ⟨9662462, by rfl⟩ : syracuseStep 12883283 = 19324925) B19324925
theorem B309195791 : Blo 626299 309195791 := bstep (se 1 (by rfl) ⟨231896843, by rfl⟩ : syracuseStep 309195791 = 463793687) B463793687
theorem B130382621 : Blo 626299 130382621 := bstep (se 3 (by rfl) ⟨24446741, by rfl⟩ : syracuseStep 130382621 = 48893483) B48893483
theorem B8588855 : Blo 626299 8588855 := bstep (se 1 (by rfl) ⟨6441641, by rfl⟩ : syracuseStep 8588855 = 12883283) B12883283
theorem B206130527 : Blo 626299 206130527 := bstep (se 1 (by rfl) ⟨154597895, by rfl⟩ : syracuseStep 206130527 = 309195791) B309195791
theorem B86921747 : Blo 626299 86921747 := bstep (se 1 (by rfl) ⟨65191310, by rfl⟩ : syracuseStep 86921747 = 130382621) B130382621
theorem B2120687 : Blo 626299 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B1413791 : Blo 626299 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B57947831 : Blo 626299 57947831 := bstep (se 1 (by rfl) ⟨43460873, by rfl⟩ : syracuseStep 57947831 = 86921747) B86921747
theorem B137420351 : Blo 626299 137420351 := bstep (se 1 (by rfl) ⟨103065263, by rfl⟩ : syracuseStep 137420351 = 206130527) B206130527
theorem B5725903 : Blo 626299 5725903 := bstep (se 1 (by rfl) ⟨4294427, by rfl⟩ : syracuseStep 5725903 = 8588855) B8588855
theorem B942527 : Blo 626299 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B91613567 : Blo 626299 91613567 := bstep (se 1 (by rfl) ⟨68710175, by rfl⟩ : syracuseStep 91613567 = 137420351) B137420351
theorem B38631887 : Blo 626299 38631887 := bstep (se 1 (by rfl) ⟨28973915, by rfl⟩ : syracuseStep 38631887 = 57947831) B57947831
theorem B7634537 : Blo 626299 7634537 := bstep (se 2 (by rfl) ⟨2862951, by rfl⟩ : syracuseStep 7634537 = 5725903) B5725903
theorem B628351 : Blo 626299 628351 := bstep (se 1 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 628351 = 942527) B942527
theorem B5089691 : Blo 626299 5089691 := bstep (se 1 (by rfl) ⟨3817268, by rfl⟩ : syracuseStep 5089691 = 7634537) B7634537
theorem B61075711 : Blo 626299 61075711 := bstep (se 1 (by rfl) ⟨45806783, by rfl⟩ : syracuseStep 61075711 = 91613567) B91613567
theorem B25754591 : Blo 626299 25754591 := bstep (se 1 (by rfl) ⟨19315943, by rfl⟩ : syracuseStep 25754591 = 38631887) B38631887
theorem B81434281 : Blo 626299 81434281 := bstep (se 2 (by rfl) ⟨30537855, by rfl⟩ : syracuseStep 81434281 = 61075711) B61075711
theorem B3393127 : Blo 626299 3393127 := bstep (se 1 (by rfl) ⟨2544845, by rfl⟩ : syracuseStep 3393127 = 5089691) B5089691
theorem B17169727 : Blo 626299 17169727 := bstep (se 1 (by rfl) ⟨12877295, by rfl⟩ : syracuseStep 17169727 = 25754591) B25754591
theorem B4524169 : Blo 626299 4524169 := bstep (se 2 (by rfl) ⟨1696563, by rfl⟩ : syracuseStep 4524169 = 3393127) B3393127
theorem B108579041 : Blo 626299 108579041 := bstep (se 2 (by rfl) ⟨40717140, by rfl⟩ : syracuseStep 108579041 = 81434281) B81434281
theorem B22892969 : Blo 626299 22892969 := bstep (se 2 (by rfl) ⟨8584863, by rfl⟩ : syracuseStep 22892969 = 17169727) B17169727
theorem B72386027 : Blo 626299 72386027 := bstep (se 1 (by rfl) ⟨54289520, by rfl⟩ : syracuseStep 72386027 = 108579041) B108579041
theorem B6032225 : Blo 626299 6032225 := bstep (se 2 (by rfl) ⟨2262084, by rfl⟩ : syracuseStep 6032225 = 4524169) B4524169
theorem B15261979 : Blo 626299 15261979 := bstep (se 1 (by rfl) ⟨11446484, by rfl⟩ : syracuseStep 15261979 = 22892969) B22892969
theorem B20349305 : Blo 626299 20349305 := bstep (se 2 (by rfl) ⟨7630989, by rfl⟩ : syracuseStep 20349305 = 15261979) B15261979
theorem B48257351 : Blo 626299 48257351 := bstep (se 1 (by rfl) ⟨36193013, by rfl⟩ : syracuseStep 48257351 = 72386027) B72386027
theorem B4021483 : Blo 626299 4021483 := bstep (se 1 (by rfl) ⟨3016112, by rfl⟩ : syracuseStep 4021483 = 6032225) B6032225
theorem B13566203 : Blo 626299 13566203 := bstep (se 1 (by rfl) ⟨10174652, by rfl⟩ : syracuseStep 13566203 = 20349305) B20349305
theorem B5361977 : Blo 626299 5361977 := bstep (se 2 (by rfl) ⟨2010741, by rfl⟩ : syracuseStep 5361977 = 4021483) B4021483
theorem B32171567 : Blo 626299 32171567 := bstep (se 1 (by rfl) ⟨24128675, by rfl⟩ : syracuseStep 32171567 = 48257351) B48257351
theorem B9044135 : Blo 626299 9044135 := bstep (se 1 (by rfl) ⟨6783101, by rfl⟩ : syracuseStep 9044135 = 13566203) B13566203
theorem B3574651 : Blo 626299 3574651 := bstep (se 1 (by rfl) ⟨2680988, by rfl⟩ : syracuseStep 3574651 = 5361977) B5361977
theorem B85790845 : Blo 626299 85790845 := bstep (se 3 (by rfl) ⟨16085783, by rfl⟩ : syracuseStep 85790845 = 32171567) B32171567
theorem B6029423 : Blo 626299 6029423 := bstep (se 1 (by rfl) ⟨4522067, by rfl⟩ : syracuseStep 6029423 = 9044135) B9044135
theorem B457551173 : Blo 626299 457551173 := bstep (se 4 (by rfl) ⟨42895422, by rfl⟩ : syracuseStep 457551173 = 85790845) B85790845
theorem B4766201 : Blo 626299 4766201 := bstep (se 2 (by rfl) ⟨1787325, by rfl⟩ : syracuseStep 4766201 = 3574651) B3574651
theorem B4019615 : Blo 626299 4019615 := bstep (se 1 (by rfl) ⟨3014711, by rfl⟩ : syracuseStep 4019615 = 6029423) B6029423
theorem B305034115 : Blo 626299 305034115 := bstep (se 1 (by rfl) ⟨228775586, by rfl⟩ : syracuseStep 305034115 = 457551173) B457551173
theorem B3177467 : Blo 626299 3177467 := bstep (se 1 (by rfl) ⟨2383100, by rfl⟩ : syracuseStep 3177467 = 4766201) B4766201
theorem B2118311 : Blo 626299 2118311 := bstep (se 1 (by rfl) ⟨1588733, by rfl⟩ : syracuseStep 2118311 = 3177467) B3177467
theorem B2679743 : Blo 626299 2679743 := bstep (se 1 (by rfl) ⟨2009807, by rfl⟩ : syracuseStep 2679743 = 4019615) B4019615
theorem B406712153 : Blo 626299 406712153 := bstep (se 2 (by rfl) ⟨152517057, by rfl⟩ : syracuseStep 406712153 = 305034115) B305034115
theorem B1412207 : Blo 626299 1412207 := bstep (se 1 (by rfl) ⟨1059155, by rfl⟩ : syracuseStep 1412207 = 2118311) B2118311
theorem B1786495 : Blo 626299 1786495 := bstep (se 1 (by rfl) ⟨1339871, by rfl⟩ : syracuseStep 1786495 = 2679743) B2679743
theorem B271141435 : Blo 626299 271141435 := bstep (se 1 (by rfl) ⟨203356076, by rfl⟩ : syracuseStep 271141435 = 406712153) B406712153
theorem B1446087653 : Blo 626299 1446087653 := bstep (se 4 (by rfl) ⟨135570717, by rfl⟩ : syracuseStep 1446087653 = 271141435) B271141435
theorem B2381993 : Blo 626299 2381993 := bstep (se 2 (by rfl) ⟨893247, by rfl⟩ : syracuseStep 2381993 = 1786495) B1786495
theorem B941471 : Blo 626299 941471 := bstep (se 1 (by rfl) ⟨706103, by rfl⟩ : syracuseStep 941471 = 1412207) B1412207
theorem B627647 : Blo 626299 627647 := bstep (se 1 (by rfl) ⟨470735, by rfl⟩ : syracuseStep 627647 = 941471) B941471
theorem B1587995 : Blo 626299 1587995 := bstep (se 1 (by rfl) ⟨1190996, by rfl⟩ : syracuseStep 1587995 = 2381993) B2381993
theorem B964058435 : Blo 626299 964058435 := bstep (se 1 (by rfl) ⟨723043826, by rfl⟩ : syracuseStep 964058435 = 1446087653) B1446087653
theorem B1058663 : Blo 626299 1058663 := bstep (se 1 (by rfl) ⟨793997, by rfl⟩ : syracuseStep 1058663 = 1587995) B1587995
theorem B642705623 : Blo 626299 642705623 := bstep (se 1 (by rfl) ⟨482029217, by rfl⟩ : syracuseStep 642705623 = 964058435) B964058435
theorem B705775 : Blo 626299 705775 := bstep (se 1 (by rfl) ⟨529331, by rfl⟩ : syracuseStep 705775 = 1058663) B1058663
theorem B428470415 : Blo 626299 428470415 := bstep (se 1 (by rfl) ⟨321352811, by rfl⟩ : syracuseStep 428470415 = 642705623) B642705623
theorem B285646943 : Blo 626299 285646943 := bstep (se 1 (by rfl) ⟨214235207, by rfl⟩ : syracuseStep 285646943 = 428470415) B428470415
theorem B941033 : Blo 626299 941033 := bstep (se 2 (by rfl) ⟨352887, by rfl⟩ : syracuseStep 941033 = 705775) B705775
theorem B761725181 : Blo 626299 761725181 := bstep (se 3 (by rfl) ⟨142823471, by rfl⟩ : syracuseStep 761725181 = 285646943) B285646943
theorem B627355 : Blo 626299 627355 := bstep (se 1 (by rfl) ⟨470516, by rfl⟩ : syracuseStep 627355 = 941033) B941033
theorem B507816787 : Blo 626299 507816787 := bstep (se 1 (by rfl) ⟨380862590, by rfl⟩ : syracuseStep 507816787 = 761725181) B761725181
theorem B677089049 : Blo 626299 677089049 := bstep (se 2 (by rfl) ⟨253908393, by rfl⟩ : syracuseStep 677089049 = 507816787) B507816787
theorem B1805570797 : Blo 626299 1805570797 := bstep (se 3 (by rfl) ⟨338544524, by rfl⟩ : syracuseStep 1805570797 = 677089049) B677089049
theorem B2407427729 : Blo 626299 2407427729 := bstep (se 2 (by rfl) ⟨902785398, by rfl⟩ : syracuseStep 2407427729 = 1805570797) B1805570797
theorem B1604951819 : Blo 626299 1604951819 := bstep (se 1 (by rfl) ⟨1203713864, by rfl⟩ : syracuseStep 1604951819 = 2407427729) B2407427729
theorem B1069967879 : Blo 626299 1069967879 := bstep (se 1 (by rfl) ⟨802475909, by rfl⟩ : syracuseStep 1069967879 = 1604951819) B1604951819
theorem B713311919 : Blo 626299 713311919 := bstep (se 1 (by rfl) ⟨534983939, by rfl⟩ : syracuseStep 713311919 = 1069967879) B1069967879
theorem B475541279 : Blo 626299 475541279 := bstep (se 1 (by rfl) ⟨356655959, by rfl⟩ : syracuseStep 475541279 = 713311919) B713311919
theorem B317027519 : Blo 626299 317027519 := bstep (se 1 (by rfl) ⟨237770639, by rfl⟩ : syracuseStep 317027519 = 475541279) B475541279
theorem B211351679 : Blo 626299 211351679 := bstep (se 1 (by rfl) ⟨158513759, by rfl⟩ : syracuseStep 211351679 = 317027519) B317027519
theorem B140901119 : Blo 626299 140901119 := bstep (se 1 (by rfl) ⟨105675839, by rfl⟩ : syracuseStep 140901119 = 211351679) B211351679
theorem B93934079 : Blo 626299 93934079 := bstep (se 1 (by rfl) ⟨70450559, by rfl⟩ : syracuseStep 93934079 = 140901119) B140901119
theorem B62622719 : Blo 626299 62622719 := bstep (se 1 (by rfl) ⟨46967039, by rfl⟩ : syracuseStep 62622719 = 93934079) B93934079
theorem B41748479 : Blo 626299 41748479 := bstep (se 1 (by rfl) ⟨31311359, by rfl⟩ : syracuseStep 41748479 = 62622719) B62622719
theorem B27832319 : Blo 626299 27832319 := bstep (se 1 (by rfl) ⟨20874239, by rfl⟩ : syracuseStep 27832319 = 41748479) B41748479
theorem B18554879 : Blo 626299 18554879 := bstep (se 1 (by rfl) ⟨13916159, by rfl⟩ : syracuseStep 18554879 = 27832319) B27832319
theorem B12369919 : Blo 626299 12369919 := bstep (se 1 (by rfl) ⟨9277439, by rfl⟩ : syracuseStep 12369919 = 18554879) B18554879
theorem B16493225 : Blo 626299 16493225 := bstep (se 2 (by rfl) ⟨6184959, by rfl⟩ : syracuseStep 16493225 = 12369919) B12369919
theorem B175927733 : Blo 626299 175927733 := bstep (se 5 (by rfl) ⟨8246612, by rfl⟩ : syracuseStep 175927733 = 16493225) B16493225
theorem B117285155 : Blo 626299 117285155 := bstep (se 1 (by rfl) ⟨87963866, by rfl⟩ : syracuseStep 117285155 = 175927733) B175927733
theorem B78190103 : Blo 626299 78190103 := bstep (se 1 (by rfl) ⟨58642577, by rfl⟩ : syracuseStep 78190103 = 117285155) B117285155
theorem B52126735 : Blo 626299 52126735 := bstep (se 1 (by rfl) ⟨39095051, by rfl⟩ : syracuseStep 52126735 = 78190103) B78190103
theorem B69502313 : Blo 626299 69502313 := bstep (se 2 (by rfl) ⟨26063367, by rfl⟩ : syracuseStep 69502313 = 52126735) B52126735
theorem B46334875 : Blo 626299 46334875 := bstep (se 1 (by rfl) ⟨34751156, by rfl⟩ : syracuseStep 46334875 = 69502313) B69502313
theorem B61779833 : Blo 626299 61779833 := bstep (se 2 (by rfl) ⟨23167437, by rfl⟩ : syracuseStep 61779833 = 46334875) B46334875
theorem B41186555 : Blo 626299 41186555 := bstep (se 1 (by rfl) ⟨30889916, by rfl⟩ : syracuseStep 41186555 = 61779833) B61779833
theorem B27457703 : Blo 626299 27457703 := bstep (se 1 (by rfl) ⟨20593277, by rfl⟩ : syracuseStep 27457703 = 41186555) B41186555
theorem B18305135 : Blo 626299 18305135 := bstep (se 1 (by rfl) ⟨13728851, by rfl⟩ : syracuseStep 18305135 = 27457703) B27457703
theorem B12203423 : Blo 626299 12203423 := bstep (se 1 (by rfl) ⟨9152567, by rfl⟩ : syracuseStep 12203423 = 18305135) B18305135
theorem B8135615 : Blo 626299 8135615 := bstep (se 1 (by rfl) ⟨6101711, by rfl⟩ : syracuseStep 8135615 = 12203423) B12203423
theorem B5423743 : Blo 626299 5423743 := bstep (se 1 (by rfl) ⟨4067807, by rfl⟩ : syracuseStep 5423743 = 8135615) B8135615
theorem B28926629 : Blo 626299 28926629 := bstep (se 4 (by rfl) ⟨2711871, by rfl⟩ : syracuseStep 28926629 = 5423743) B5423743
theorem B19284419 : Blo 626299 19284419 := bstep (se 1 (by rfl) ⟨14463314, by rfl⟩ : syracuseStep 19284419 = 28926629) B28926629
theorem B51425117 : Blo 626299 51425117 := bstep (se 3 (by rfl) ⟨9642209, by rfl⟩ : syracuseStep 51425117 = 19284419) B19284419
theorem B34283411 : Blo 626299 34283411 := bstep (se 1 (by rfl) ⟨25712558, by rfl⟩ : syracuseStep 34283411 = 51425117) B51425117
theorem B22855607 : Blo 626299 22855607 := bstep (se 1 (by rfl) ⟨17141705, by rfl⟩ : syracuseStep 22855607 = 34283411) B34283411
theorem B15237071 : Blo 626299 15237071 := bstep (se 1 (by rfl) ⟨11427803, by rfl⟩ : syracuseStep 15237071 = 22855607) B22855607
theorem B10158047 : Blo 626299 10158047 := bstep (se 1 (by rfl) ⟨7618535, by rfl⟩ : syracuseStep 10158047 = 15237071) B15237071
theorem B6772031 : Blo 626299 6772031 := bstep (se 1 (by rfl) ⟨5079023, by rfl⟩ : syracuseStep 6772031 = 10158047) B10158047
theorem B4514687 : Blo 626299 4514687 := bstep (se 1 (by rfl) ⟨3386015, by rfl⟩ : syracuseStep 4514687 = 6772031) B6772031
theorem B3009791 : Blo 626299 3009791 := bstep (se 1 (by rfl) ⟨2257343, by rfl⟩ : syracuseStep 3009791 = 4514687) B4514687
theorem B2006527 : Blo 626299 2006527 := bstep (se 1 (by rfl) ⟨1504895, by rfl⟩ : syracuseStep 2006527 = 3009791) B3009791
theorem B2675369 : Blo 626299 2675369 := bstep (se 2 (by rfl) ⟨1003263, by rfl⟩ : syracuseStep 2675369 = 2006527) B2006527
theorem B1783579 : Blo 626299 1783579 := bstep (se 1 (by rfl) ⟨1337684, by rfl⟩ : syracuseStep 1783579 = 2675369) B2675369
theorem B2378105 : Blo 626299 2378105 := bstep (se 2 (by rfl) ⟨891789, by rfl⟩ : syracuseStep 2378105 = 1783579) B1783579
theorem B1585403 : Blo 626299 1585403 := bstep (se 1 (by rfl) ⟨1189052, by rfl⟩ : syracuseStep 1585403 = 2378105) B2378105
theorem B1056935 : Blo 626299 1056935 := bstep (se 1 (by rfl) ⟨792701, by rfl⟩ : syracuseStep 1056935 = 1585403) B1585403
theorem B704623 : Blo 626299 704623 := bstep (se 1 (by rfl) ⟨528467, by rfl⟩ : syracuseStep 704623 = 1056935) B1056935
theorem B939497 : Blo 626299 939497 := bstep (se 2 (by rfl) ⟨352311, by rfl⟩ : syracuseStep 939497 = 704623) B704623
theorem B626331 : Blo 626299 626331 := bstep (se 1 (by rfl) ⟨469748, by rfl⟩ : syracuseStep 626331 = 939497) B939497

theorem C0 (j : ℕ) (h1 : 156574 ≤ j) (h2 : j ≤ 157273) : Blo 626299 (4 * j + 3) := by
  interval_cases j
  · exact B626299
  · exact B626303
  · exact B626307
  · exact B626311
  · exact B626315
  · exact B626319
  · exact B626323
  · exact B626327
  · exact B626331
  · exact B626335
  · exact B626339
  · exact B626343
  · exact B626347
  · exact B626351
  · exact B626355
  · exact B626359
  · exact B626363
  · exact B626367
  · exact B626371
  · exact B626375
  · exact B626379
  · exact B626383
  · exact B626387
  · exact B626391
  · exact B626395
  · exact B626399
  · exact B626403
  · exact B626407
  · exact B626411
  · exact B626415
  · exact B626419
  · exact B626423
  · exact B626427
  · exact B626431
  · exact B626435
  · exact B626439
  · exact B626443
  · exact B626447
  · exact B626451
  · exact B626455
  · exact B626459
  · exact B626463
  · exact B626467
  · exact B626471
  · exact B626475
  · exact B626479
  · exact B626483
  · exact B626487
  · exact B626491
  · exact B626495
  · exact B626499
  · exact B626503
  · exact B626507
  · exact B626511
  · exact B626515
  · exact B626519
  · exact B626523
  · exact B626527
  · exact B626531
  · exact B626535
  · exact B626539
  · exact B626543
  · exact B626547
  · exact B626551
  · exact B626555
  · exact B626559
  · exact B626563
  · exact B626567
  · exact B626571
  · exact B626575
  · exact B626579
  · exact B626583
  · exact B626587
  · exact B626591
  · exact B626595
  · exact B626599
  · exact B626603
  · exact B626607
  · exact B626611
  · exact B626615
  · exact B626619
  · exact B626623
  · exact B626627
  · exact B626631
  · exact B626635
  · exact B626639
  · exact B626643
  · exact B626647
  · exact B626651
  · exact B626655
  · exact B626659
  · exact B626663
  · exact B626667
  · exact B626671
  · exact B626675
  · exact B626679
  · exact B626683
  · exact B626687
  · exact B626691
  · exact B626695
  · exact B626699
  · exact B626703
  · exact B626707
  · exact B626711
  · exact B626715
  · exact B626719
  · exact B626723
  · exact B626727
  · exact B626731
  · exact B626735
  · exact B626739
  · exact B626743
  · exact B626747
  · exact B626751
  · exact B626755
  · exact B626759
  · exact B626763
  · exact B626767
  · exact B626771
  · exact B626775
  · exact B626779
  · exact B626783
  · exact B626787
  · exact B626791
  · exact B626795
  · exact B626799
  · exact B626803
  · exact B626807
  · exact B626811
  · exact B626815
  · exact B626819
  · exact B626823
  · exact B626827
  · exact B626831
  · exact B626835
  · exact B626839
  · exact B626843
  · exact B626847
  · exact B626851
  · exact B626855
  · exact B626859
  · exact B626863
  · exact B626867
  · exact B626871
  · exact B626875
  · exact B626879
  · exact B626883
  · exact B626887
  · exact B626891
  · exact B626895
  · exact B626899
  · exact B626903
  · exact B626907
  · exact B626911
  · exact B626915
  · exact B626919
  · exact B626923
  · exact B626927
  · exact B626931
  · exact B626935
  · exact B626939
  · exact B626943
  · exact B626947
  · exact B626951
  · exact B626955
  · exact B626959
  · exact B626963
  · exact B626967
  · exact B626971
  · exact B626975
  · exact B626979
  · exact B626983
  · exact B626987
  · exact B626991
  · exact B626995
  · exact B626999
  · exact B627003
  · exact B627007
  · exact B627011
  · exact B627015
  · exact B627019
  · exact B627023
  · exact B627027
  · exact B627031
  · exact B627035
  · exact B627039
  · exact B627043
  · exact B627047
  · exact B627051
  · exact B627055
  · exact B627059
  · exact B627063
  · exact B627067
  · exact B627071
  · exact B627075
  · exact B627079
  · exact B627083
  · exact B627087
  · exact B627091
  · exact B627095
  · exact B627099
  · exact B627103
  · exact B627107
  · exact B627111
  · exact B627115
  · exact B627119
  · exact B627123
  · exact B627127
  · exact B627131
  · exact B627135
  · exact B627139
  · exact B627143
  · exact B627147
  · exact B627151
  · exact B627155
  · exact B627159
  · exact B627163
  · exact B627167
  · exact B627171
  · exact B627175
  · exact B627179
  · exact B627183
  · exact B627187
  · exact B627191
  · exact B627195
  · exact B627199
  · exact B627203
  · exact B627207
  · exact B627211
  · exact B627215
  · exact B627219
  · exact B627223
  · exact B627227
  · exact B627231
  · exact B627235
  · exact B627239
  · exact B627243
  · exact B627247
  · exact B627251
  · exact B627255
  · exact B627259
  · exact B627263
  · exact B627267
  · exact B627271
  · exact B627275
  · exact B627279
  · exact B627283
  · exact B627287
  · exact B627291
  · exact B627295
  · exact B627299
  · exact B627303
  · exact B627307
  · exact B627311
  · exact B627315
  · exact B627319
  · exact B627323
  · exact B627327
  · exact B627331
  · exact B627335
  · exact B627339
  · exact B627343
  · exact B627347
  · exact B627351
  · exact B627355
  · exact B627359
  · exact B627363
  · exact B627367
  · exact B627371
  · exact B627375
  · exact B627379
  · exact B627383
  · exact B627387
  · exact B627391
  · exact B627395
  · exact B627399
  · exact B627403
  · exact B627407
  · exact B627411
  · exact B627415
  · exact B627419
  · exact B627423
  · exact B627427
  · exact B627431
  · exact B627435
  · exact B627439
  · exact B627443
  · exact B627447
  · exact B627451
  · exact B627455
  · exact B627459
  · exact B627463
  · exact B627467
  · exact B627471
  · exact B627475
  · exact B627479
  · exact B627483
  · exact B627487
  · exact B627491
  · exact B627495
  · exact B627499
  · exact B627503
  · exact B627507
  · exact B627511
  · exact B627515
  · exact B627519
  · exact B627523
  · exact B627527
  · exact B627531
  · exact B627535
  · exact B627539
  · exact B627543
  · exact B627547
  · exact B627551
  · exact B627555
  · exact B627559
  · exact B627563
  · exact B627567
  · exact B627571
  · exact B627575
  · exact B627579
  · exact B627583
  · exact B627587
  · exact B627591
  · exact B627595
  · exact B627599
  · exact B627603
  · exact B627607
  · exact B627611
  · exact B627615
  · exact B627619
  · exact B627623
  · exact B627627
  · exact B627631
  · exact B627635
  · exact B627639
  · exact B627643
  · exact B627647
  · exact B627651
  · exact B627655
  · exact B627659
  · exact B627663
  · exact B627667
  · exact B627671
  · exact B627675
  · exact B627679
  · exact B627683
  · exact B627687
  · exact B627691
  · exact B627695
  · exact B627699
  · exact B627703
  · exact B627707
  · exact B627711
  · exact B627715
  · exact B627719
  · exact B627723
  · exact B627727
  · exact B627731
  · exact B627735
  · exact B627739
  · exact B627743
  · exact B627747
  · exact B627751
  · exact B627755
  · exact B627759
  · exact B627763
  · exact B627767
  · exact B627771
  · exact B627775
  · exact B627779
  · exact B627783
  · exact B627787
  · exact B627791
  · exact B627795
  · exact B627799
  · exact B627803
  · exact B627807
  · exact B627811
  · exact B627815
  · exact B627819
  · exact B627823
  · exact B627827
  · exact B627831
  · exact B627835
  · exact B627839
  · exact B627843
  · exact B627847
  · exact B627851
  · exact B627855
  · exact B627859
  · exact B627863
  · exact B627867
  · exact B627871
  · exact B627875
  · exact B627879
  · exact B627883
  · exact B627887
  · exact B627891
  · exact B627895
  · exact B627899
  · exact B627903
  · exact B627907
  · exact B627911
  · exact B627915
  · exact B627919
  · exact B627923
  · exact B627927
  · exact B627931
  · exact B627935
  · exact B627939
  · exact B627943
  · exact B627947
  · exact B627951
  · exact B627955
  · exact B627959
  · exact B627963
  · exact B627967
  · exact B627971
  · exact B627975
  · exact B627979
  · exact B627983
  · exact B627987
  · exact B627991
  · exact B627995
  · exact B627999
  · exact B628003
  · exact B628007
  · exact B628011
  · exact B628015
  · exact B628019
  · exact B628023
  · exact B628027
  · exact B628031
  · exact B628035
  · exact B628039
  · exact B628043
  · exact B628047
  · exact B628051
  · exact B628055
  · exact B628059
  · exact B628063
  · exact B628067
  · exact B628071
  · exact B628075
  · exact B628079
  · exact B628083
  · exact B628087
  · exact B628091
  · exact B628095
  · exact B628099
  · exact B628103
  · exact B628107
  · exact B628111
  · exact B628115
  · exact B628119
  · exact B628123
  · exact B628127
  · exact B628131
  · exact B628135
  · exact B628139
  · exact B628143
  · exact B628147
  · exact B628151
  · exact B628155
  · exact B628159
  · exact B628163
  · exact B628167
  · exact B628171
  · exact B628175
  · exact B628179
  · exact B628183
  · exact B628187
  · exact B628191
  · exact B628195
  · exact B628199
  · exact B628203
  · exact B628207
  · exact B628211
  · exact B628215
  · exact B628219
  · exact B628223
  · exact B628227
  · exact B628231
  · exact B628235
  · exact B628239
  · exact B628243
  · exact B628247
  · exact B628251
  · exact B628255
  · exact B628259
  · exact B628263
  · exact B628267
  · exact B628271
  · exact B628275
  · exact B628279
  · exact B628283
  · exact B628287
  · exact B628291
  · exact B628295
  · exact B628299
  · exact B628303
  · exact B628307
  · exact B628311
  · exact B628315
  · exact B628319
  · exact B628323
  · exact B628327
  · exact B628331
  · exact B628335
  · exact B628339
  · exact B628343
  · exact B628347
  · exact B628351
  · exact B628355
  · exact B628359
  · exact B628363
  · exact B628367
  · exact B628371
  · exact B628375
  · exact B628379
  · exact B628383
  · exact B628387
  · exact B628391
  · exact B628395
  · exact B628399
  · exact B628403
  · exact B628407
  · exact B628411
  · exact B628415
  · exact B628419
  · exact B628423
  · exact B628427
  · exact B628431
  · exact B628435
  · exact B628439
  · exact B628443
  · exact B628447
  · exact B628451
  · exact B628455
  · exact B628459
  · exact B628463
  · exact B628467
  · exact B628471
  · exact B628475
  · exact B628479
  · exact B628483
  · exact B628487
  · exact B628491
  · exact B628495
  · exact B628499
  · exact B628503
  · exact B628507
  · exact B628511
  · exact B628515
  · exact B628519
  · exact B628523
  · exact B628527
  · exact B628531
  · exact B628535
  · exact B628539
  · exact B628543
  · exact B628547
  · exact B628551
  · exact B628555
  · exact B628559
  · exact B628563
  · exact B628567
  · exact B628571
  · exact B628575
  · exact B628579
  · exact B628583
  · exact B628587
  · exact B628591
  · exact B628595
  · exact B628599
  · exact B628603
  · exact B628607
  · exact B628611
  · exact B628615
  · exact B628619
  · exact B628623
  · exact B628627
  · exact B628631
  · exact B628635
  · exact B628639
  · exact B628643
  · exact B628647
  · exact B628651
  · exact B628655
  · exact B628659
  · exact B628663
  · exact B628667
  · exact B628671
  · exact B628675
  · exact B628679
  · exact B628683
  · exact B628687
  · exact B628691
  · exact B628695
  · exact B628699
  · exact B628703
  · exact B628707
  · exact B628711
  · exact B628715
  · exact B628719
  · exact B628723
  · exact B628727
  · exact B628731
  · exact B628735
  · exact B628739
  · exact B628743
  · exact B628747
  · exact B628751
  · exact B628755
  · exact B628759
  · exact B628763
  · exact B628767
  · exact B628771
  · exact B628775
  · exact B628779
  · exact B628783
  · exact B628787
  · exact B628791
  · exact B628795
  · exact B628799
  · exact B628803
  · exact B628807
  · exact B628811
  · exact B628815
  · exact B628819
  · exact B628823
  · exact B628827
  · exact B628831
  · exact B628835
  · exact B628839
  · exact B628843
  · exact B628847
  · exact B628851
  · exact B628855
  · exact B628859
  · exact B628863
  · exact B628867
  · exact B628871
  · exact B628875
  · exact B628879
  · exact B628883
  · exact B628887
  · exact B628891
  · exact B628895
  · exact B628899
  · exact B628903
  · exact B628907
  · exact B628911
  · exact B628915
  · exact B628919
  · exact B628923
  · exact B628927
  · exact B628931
  · exact B628935
  · exact B628939
  · exact B628943
  · exact B628947
  · exact B628951
  · exact B628955
  · exact B628959
  · exact B628963
  · exact B628967
  · exact B628971
  · exact B628975
  · exact B628979
  · exact B628983
  · exact B628987
  · exact B628991
  · exact B628995
  · exact B628999
  · exact B629003
  · exact B629007
  · exact B629011
  · exact B629015
  · exact B629019
  · exact B629023
  · exact B629027
  · exact B629031
  · exact B629035
  · exact B629039
  · exact B629043
  · exact B629047
  · exact B629051
  · exact B629055
  · exact B629059
  · exact B629063
  · exact B629067
  · exact B629071
  · exact B629075
  · exact B629079
  · exact B629083
  · exact B629087
  · exact B629091
  · exact B629095

theorem C1 (j : ℕ) (h1 : 157274 ≤ j) (h2 : j ≤ 157574) : Blo 626299 (4 * j + 3) := by
  interval_cases j
  · exact B629099
  · exact B629103
  · exact B629107
  · exact B629111
  · exact B629115
  · exact B629119
  · exact B629123
  · exact B629127
  · exact B629131
  · exact B629135
  · exact B629139
  · exact B629143
  · exact B629147
  · exact B629151
  · exact B629155
  · exact B629159
  · exact B629163
  · exact B629167
  · exact B629171
  · exact B629175
  · exact B629179
  · exact B629183
  · exact B629187
  · exact B629191
  · exact B629195
  · exact B629199
  · exact B629203
  · exact B629207
  · exact B629211
  · exact B629215
  · exact B629219
  · exact B629223
  · exact B629227
  · exact B629231
  · exact B629235
  · exact B629239
  · exact B629243
  · exact B629247
  · exact B629251
  · exact B629255
  · exact B629259
  · exact B629263
  · exact B629267
  · exact B629271
  · exact B629275
  · exact B629279
  · exact B629283
  · exact B629287
  · exact B629291
  · exact B629295
  · exact B629299
  · exact B629303
  · exact B629307
  · exact B629311
  · exact B629315
  · exact B629319
  · exact B629323
  · exact B629327
  · exact B629331
  · exact B629335
  · exact B629339
  · exact B629343
  · exact B629347
  · exact B629351
  · exact B629355
  · exact B629359
  · exact B629363
  · exact B629367
  · exact B629371
  · exact B629375
  · exact B629379
  · exact B629383
  · exact B629387
  · exact B629391
  · exact B629395
  · exact B629399
  · exact B629403
  · exact B629407
  · exact B629411
  · exact B629415
  · exact B629419
  · exact B629423
  · exact B629427
  · exact B629431
  · exact B629435
  · exact B629439
  · exact B629443
  · exact B629447
  · exact B629451
  · exact B629455
  · exact B629459
  · exact B629463
  · exact B629467
  · exact B629471
  · exact B629475
  · exact B629479
  · exact B629483
  · exact B629487
  · exact B629491
  · exact B629495
  · exact B629499
  · exact B629503
  · exact B629507
  · exact B629511
  · exact B629515
  · exact B629519
  · exact B629523
  · exact B629527
  · exact B629531
  · exact B629535
  · exact B629539
  · exact B629543
  · exact B629547
  · exact B629551
  · exact B629555
  · exact B629559
  · exact B629563
  · exact B629567
  · exact B629571
  · exact B629575
  · exact B629579
  · exact B629583
  · exact B629587
  · exact B629591
  · exact B629595
  · exact B629599
  · exact B629603
  · exact B629607
  · exact B629611
  · exact B629615
  · exact B629619
  · exact B629623
  · exact B629627
  · exact B629631
  · exact B629635
  · exact B629639
  · exact B629643
  · exact B629647
  · exact B629651
  · exact B629655
  · exact B629659
  · exact B629663
  · exact B629667
  · exact B629671
  · exact B629675
  · exact B629679
  · exact B629683
  · exact B629687
  · exact B629691
  · exact B629695
  · exact B629699
  · exact B629703
  · exact B629707
  · exact B629711
  · exact B629715
  · exact B629719
  · exact B629723
  · exact B629727
  · exact B629731
  · exact B629735
  · exact B629739
  · exact B629743
  · exact B629747
  · exact B629751
  · exact B629755
  · exact B629759
  · exact B629763
  · exact B629767
  · exact B629771
  · exact B629775
  · exact B629779
  · exact B629783
  · exact B629787
  · exact B629791
  · exact B629795
  · exact B629799
  · exact B629803
  · exact B629807
  · exact B629811
  · exact B629815
  · exact B629819
  · exact B629823
  · exact B629827
  · exact B629831
  · exact B629835
  · exact B629839
  · exact B629843
  · exact B629847
  · exact B629851
  · exact B629855
  · exact B629859
  · exact B629863
  · exact B629867
  · exact B629871
  · exact B629875
  · exact B629879
  · exact B629883
  · exact B629887
  · exact B629891
  · exact B629895
  · exact B629899
  · exact B629903
  · exact B629907
  · exact B629911
  · exact B629915
  · exact B629919
  · exact B629923
  · exact B629927
  · exact B629931
  · exact B629935
  · exact B629939
  · exact B629943
  · exact B629947
  · exact B629951
  · exact B629955
  · exact B629959
  · exact B629963
  · exact B629967
  · exact B629971
  · exact B629975
  · exact B629979
  · exact B629983
  · exact B629987
  · exact B629991
  · exact B629995
  · exact B629999
  · exact B630003
  · exact B630007
  · exact B630011
  · exact B630015
  · exact B630019
  · exact B630023
  · exact B630027
  · exact B630031
  · exact B630035
  · exact B630039
  · exact B630043
  · exact B630047
  · exact B630051
  · exact B630055
  · exact B630059
  · exact B630063
  · exact B630067
  · exact B630071
  · exact B630075
  · exact B630079
  · exact B630083
  · exact B630087
  · exact B630091
  · exact B630095
  · exact B630099
  · exact B630103
  · exact B630107
  · exact B630111
  · exact B630115
  · exact B630119
  · exact B630123
  · exact B630127
  · exact B630131
  · exact B630135
  · exact B630139
  · exact B630143
  · exact B630147
  · exact B630151
  · exact B630155
  · exact B630159
  · exact B630163
  · exact B630167
  · exact B630171
  · exact B630175
  · exact B630179
  · exact B630183
  · exact B630187
  · exact B630191
  · exact B630195
  · exact B630199
  · exact B630203
  · exact B630207
  · exact B630211
  · exact B630215
  · exact B630219
  · exact B630223
  · exact B630227
  · exact B630231
  · exact B630235
  · exact B630239
  · exact B630243
  · exact B630247
  · exact B630251
  · exact B630255
  · exact B630259
  · exact B630263
  · exact B630267
  · exact B630271
  · exact B630275
  · exact B630279
  · exact B630283
  · exact B630287
  · exact B630291
  · exact B630295
  · exact B630299

theorem solution (m : ℕ) (hlo : 626299 ≤ m) (hhi : m ≤ 630299) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 156574 ≤ j := by omega
    have hj2 : j ≤ 157574 := by omega
    have hb : Blo 626299 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 157274 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
