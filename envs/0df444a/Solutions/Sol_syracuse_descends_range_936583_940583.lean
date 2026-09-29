-- Prove2me | solution 1 for syracuse_descends_range_936583_940583
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:56.686325+00:00
-- url     : https://prove2.me/submissions/514fa5c7-0258-416b-9321-d2e15c830103

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


theorem B1409045 : Blo 936583 1409045 := bbase (se 6 (by rfl) ⟨33024, by rfl⟩ : syracuseStep 1409045 = 66049) (by norm_num)
theorem B1409069 : Blo 936583 1409069 := bbase (se 3 (by rfl) ⟨264200, by rfl⟩ : syracuseStep 1409069 = 528401) (by norm_num)
theorem B1409093 : Blo 936583 1409093 := bbase (se 4 (by rfl) ⟨132102, by rfl⟩ : syracuseStep 1409093 = 264205) (by norm_num)
theorem B1409117 : Blo 936583 1409117 := bbase (se 3 (by rfl) ⟨264209, by rfl⟩ : syracuseStep 1409117 = 528419) (by norm_num)
theorem B1409141 : Blo 936583 1409141 := bbase (se 5 (by rfl) ⟨66053, by rfl⟩ : syracuseStep 1409141 = 132107) (by norm_num)
theorem B1409165 : Blo 936583 1409165 := bbase (se 3 (by rfl) ⟨264218, by rfl⟩ : syracuseStep 1409165 = 528437) (by norm_num)
theorem B1409189 : Blo 936583 1409189 := bbase (se 4 (by rfl) ⟨132111, by rfl⟩ : syracuseStep 1409189 = 264223) (by norm_num)
theorem B2031797 : Blo 936583 2031797 := bbase (se 5 (by rfl) ⟨95240, by rfl⟩ : syracuseStep 2031797 = 190481) (by norm_num)
theorem B8028341 : Blo 936583 8028341 := bbase (se 5 (by rfl) ⟨376328, by rfl⟩ : syracuseStep 8028341 = 752657) (by norm_num)
theorem B1409213 : Blo 936583 1409213 := bbase (se 3 (by rfl) ⟨264227, by rfl⟩ : syracuseStep 1409213 = 528455) (by norm_num)
theorem B1409237 : Blo 936583 1409237 := bbase (se 7 (by rfl) ⟨16514, by rfl⟩ : syracuseStep 1409237 = 33029) (by norm_num)
theorem B1409261 : Blo 936583 1409261 := bbase (se 3 (by rfl) ⟨264236, by rfl⟩ : syracuseStep 1409261 = 528473) (by norm_num)
theorem B4751621 : Blo 936583 4751621 := bbase (se 4 (by rfl) ⟨445464, by rfl⟩ : syracuseStep 4751621 = 890929) (by norm_num)
theorem B1409285 : Blo 936583 1409285 := bbase (se 4 (by rfl) ⟨132120, by rfl⟩ : syracuseStep 1409285 = 264241) (by norm_num)
theorem B1409309 : Blo 936583 1409309 := bbase (se 3 (by rfl) ⟨264245, by rfl⟩ : syracuseStep 1409309 = 528491) (by norm_num)
theorem B1409333 : Blo 936583 1409333 := bbase (se 5 (by rfl) ⟨66062, by rfl⟩ : syracuseStep 1409333 = 132125) (by norm_num)
theorem B1409357 : Blo 936583 1409357 := bbase (se 3 (by rfl) ⟨264254, by rfl⟩ : syracuseStep 1409357 = 528509) (by norm_num)
theorem B1409381 : Blo 936583 1409381 := bbase (se 4 (by rfl) ⟨132129, by rfl⟩ : syracuseStep 1409381 = 264259) (by norm_num)
theorem B1409405 : Blo 936583 1409405 := bbase (se 3 (by rfl) ⟨264263, by rfl⟩ : syracuseStep 1409405 = 528527) (by norm_num)
theorem B1409429 : Blo 936583 1409429 := bbase (se 6 (by rfl) ⟨33033, by rfl⟩ : syracuseStep 1409429 = 66067) (by norm_num)
theorem B1409453 : Blo 936583 1409453 := bbase (se 3 (by rfl) ⟨264272, by rfl⟩ : syracuseStep 1409453 = 528545) (by norm_num)
theorem B950717 : Blo 936583 950717 := bbase (se 3 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 950717 = 356519) (by norm_num)
theorem B1409477 : Blo 936583 1409477 := bbase (se 4 (by rfl) ⟨132138, by rfl⟩ : syracuseStep 1409477 = 264277) (by norm_num)
theorem B1409501 : Blo 936583 1409501 := bbase (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) (by norm_num)
theorem B2851301 : Blo 936583 2851301 := bbase (se 4 (by rfl) ⟨267309, by rfl⟩ : syracuseStep 2851301 = 534619) (by norm_num)
theorem B1409525 : Blo 936583 1409525 := bbase (se 5 (by rfl) ⟨66071, by rfl⟩ : syracuseStep 1409525 = 132143) (by norm_num)
theorem B1409549 : Blo 936583 1409549 := bbase (se 3 (by rfl) ⟨264290, by rfl⟩ : syracuseStep 1409549 = 528581) (by norm_num)
theorem B1409573 : Blo 936583 1409573 := bbase (se 4 (by rfl) ⟨132147, by rfl⟩ : syracuseStep 1409573 = 264295) (by norm_num)
theorem B1409597 : Blo 936583 1409597 := bbase (se 3 (by rfl) ⟨264299, by rfl⟩ : syracuseStep 1409597 = 528599) (by norm_num)
theorem B1409621 : Blo 936583 1409621 := bbase (se 8 (by rfl) ⟨8259, by rfl⟩ : syracuseStep 1409621 = 16519) (by norm_num)
theorem B1409645 : Blo 936583 1409645 := bbase (se 3 (by rfl) ⟨264308, by rfl⟩ : syracuseStep 1409645 = 528617) (by norm_num)
theorem B1409669 : Blo 936583 1409669 := bbase (se 4 (by rfl) ⟨132156, by rfl⟩ : syracuseStep 1409669 = 264313) (by norm_num)
theorem B1409693 : Blo 936583 1409693 := bbase (se 3 (by rfl) ⟨264317, by rfl⟩ : syracuseStep 1409693 = 528635) (by norm_num)
theorem B1409717 : Blo 936583 1409717 := bbase (se 5 (by rfl) ⟨66080, by rfl⟩ : syracuseStep 1409717 = 132161) (by norm_num)
theorem B950977 : Blo 936583 950977 := bbase (se 2 (by rfl) ⟨356616, by rfl⟩ : syracuseStep 950977 = 713233) (by norm_num)
theorem B1409741 : Blo 936583 1409741 := bbase (se 3 (by rfl) ⟨264326, by rfl⟩ : syracuseStep 1409741 = 528653) (by norm_num)
theorem B3801829 : Blo 936583 3801829 := bbase (se 4 (by rfl) ⟨356421, by rfl⟩ : syracuseStep 3801829 = 712843) (by norm_num)
theorem B1409765 : Blo 936583 1409765 := bbase (se 4 (by rfl) ⟨132165, by rfl⟩ : syracuseStep 1409765 = 264331) (by norm_num)
theorem B951025 : Blo 936583 951025 := bbase (se 2 (by rfl) ⟨356634, by rfl⟩ : syracuseStep 951025 = 713269) (by norm_num)
theorem B1409789 : Blo 936583 1409789 := bbase (se 3 (by rfl) ⟨264335, by rfl⟩ : syracuseStep 1409789 = 528671) (by norm_num)
theorem B5079829 : Blo 936583 5079829 := bbase (se 6 (by rfl) ⟨119058, by rfl⟩ : syracuseStep 5079829 = 238117) (by norm_num)
theorem B1409813 : Blo 936583 1409813 := bbase (se 6 (by rfl) ⟨33042, by rfl⟩ : syracuseStep 1409813 = 66085) (by norm_num)
theorem B1409837 : Blo 936583 1409837 := bbase (se 3 (by rfl) ⟨264344, by rfl⟩ : syracuseStep 1409837 = 528689) (by norm_num)
theorem B1409861 : Blo 936583 1409861 := bbase (se 4 (by rfl) ⟨132174, by rfl⟩ : syracuseStep 1409861 = 264349) (by norm_num)
theorem B1409885 : Blo 936583 1409885 := bbase (se 3 (by rfl) ⟨264353, by rfl⟩ : syracuseStep 1409885 = 528707) (by norm_num)
theorem B1409909 : Blo 936583 1409909 := bbase (se 5 (by rfl) ⟨66089, by rfl⟩ : syracuseStep 1409909 = 132179) (by norm_num)
theorem B1409933 : Blo 936583 1409933 := bbase (se 3 (by rfl) ⟨264362, by rfl⟩ : syracuseStep 1409933 = 528725) (by norm_num)
theorem B4064165 : Blo 936583 4064165 := bbase (se 4 (by rfl) ⟨381015, by rfl⟩ : syracuseStep 4064165 = 762031) (by norm_num)
theorem B1409957 : Blo 936583 1409957 := bbase (se 4 (by rfl) ⟨132183, by rfl⟩ : syracuseStep 1409957 = 264367) (by norm_num)
theorem B1409981 : Blo 936583 1409981 := bbase (se 3 (by rfl) ⟨264371, by rfl⟩ : syracuseStep 1409981 = 528743) (by norm_num)
theorem B1410005 : Blo 936583 1410005 := bbase (se 7 (by rfl) ⟨16523, by rfl⟩ : syracuseStep 1410005 = 33047) (by norm_num)
theorem B1410029 : Blo 936583 1410029 := bbase (se 3 (by rfl) ⟨264380, by rfl⟩ : syracuseStep 1410029 = 528761) (by norm_num)
theorem B1410053 : Blo 936583 1410053 := bbase (se 4 (by rfl) ⟨132192, by rfl⟩ : syracuseStep 1410053 = 264385) (by norm_num)
theorem B1410077 : Blo 936583 1410077 := bbase (se 3 (by rfl) ⟨264389, by rfl⟩ : syracuseStep 1410077 = 528779) (by norm_num)
theorem B1410101 : Blo 936583 1410101 := bbase (se 5 (by rfl) ⟨66098, by rfl⟩ : syracuseStep 1410101 = 132197) (by norm_num)
theorem B1410125 : Blo 936583 1410125 := bbase (se 3 (by rfl) ⟨264398, by rfl⟩ : syracuseStep 1410125 = 528797) (by norm_num)
theorem B1410149 : Blo 936583 1410149 := bbase (se 4 (by rfl) ⟨132201, by rfl⟩ : syracuseStep 1410149 = 264403) (by norm_num)
theorem B1410173 : Blo 936583 1410173 := bbase (se 3 (by rfl) ⟨264407, by rfl⟩ : syracuseStep 1410173 = 528815) (by norm_num)
theorem B1410197 : Blo 936583 1410197 := bbase (se 6 (by rfl) ⟨33051, by rfl⟩ : syracuseStep 1410197 = 66103) (by norm_num)
theorem B1410221 : Blo 936583 1410221 := bbase (se 3 (by rfl) ⟨264416, by rfl⟩ : syracuseStep 1410221 = 528833) (by norm_num)
theorem B1410245 : Blo 936583 1410245 := bbase (se 4 (by rfl) ⟨132210, by rfl⟩ : syracuseStep 1410245 = 264421) (by norm_num)
theorem B1410269 : Blo 936583 1410269 := bbase (se 3 (by rfl) ⟨264425, by rfl⟩ : syracuseStep 1410269 = 528851) (by norm_num)
theorem B1410293 : Blo 936583 1410293 := bbase (se 5 (by rfl) ⟨66107, by rfl⟩ : syracuseStep 1410293 = 132215) (by norm_num)
theorem B1410317 : Blo 936583 1410317 := bbase (se 3 (by rfl) ⟨264434, by rfl⟩ : syracuseStep 1410317 = 528869) (by norm_num)
theorem B951589 : Blo 936583 951589 := bbase (se 4 (by rfl) ⟨89211, by rfl⟩ : syracuseStep 951589 = 178423) (by norm_num)
theorem B1410341 : Blo 936583 1410341 := bbase (se 4 (by rfl) ⟨132219, by rfl⟩ : syracuseStep 1410341 = 264439) (by norm_num)
theorem B951593 : Blo 936583 951593 := bbase (se 2 (by rfl) ⟨356847, by rfl⟩ : syracuseStep 951593 = 713695) (by norm_num)
theorem B1410365 : Blo 936583 1410365 := bbase (se 3 (by rfl) ⟨264443, by rfl⟩ : syracuseStep 1410365 = 528887) (by norm_num)
theorem B1410389 : Blo 936583 1410389 := bbase (se 12 (by rfl) ⟨516, by rfl⟩ : syracuseStep 1410389 = 1033) (by norm_num)
theorem B1410413 : Blo 936583 1410413 := bbase (se 3 (by rfl) ⟨264452, by rfl⟩ : syracuseStep 1410413 = 528905) (by norm_num)
theorem B1410437 : Blo 936583 1410437 := bbase (se 4 (by rfl) ⟨132228, by rfl⟩ : syracuseStep 1410437 = 264457) (by norm_num)
theorem B1410461 : Blo 936583 1410461 := bbase (se 3 (by rfl) ⟨264461, by rfl⟩ : syracuseStep 1410461 = 528923) (by norm_num)
theorem B1410485 : Blo 936583 1410485 := bbase (se 5 (by rfl) ⟨66116, by rfl⟩ : syracuseStep 1410485 = 132233) (by norm_num)
theorem B1410509 : Blo 936583 1410509 := bbase (se 3 (by rfl) ⟨264470, by rfl⟩ : syracuseStep 1410509 = 528941) (by norm_num)
theorem B1410533 : Blo 936583 1410533 := bbase (se 4 (by rfl) ⟨132237, by rfl⟩ : syracuseStep 1410533 = 264475) (by norm_num)
theorem B1410557 : Blo 936583 1410557 := bbase (se 3 (by rfl) ⟨264479, by rfl⟩ : syracuseStep 1410557 = 528959) (by norm_num)
theorem B4752917 : Blo 936583 4752917 := bbase (se 6 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 4752917 = 222793) (by norm_num)
theorem B1410581 : Blo 936583 1410581 := bbase (se 6 (by rfl) ⟨33060, by rfl⟩ : syracuseStep 1410581 = 66121) (by norm_num)
theorem B2033189 : Blo 936583 2033189 := bbase (se 4 (by rfl) ⟨190611, by rfl⟩ : syracuseStep 2033189 = 381223) (by norm_num)
theorem B1410605 : Blo 936583 1410605 := bbase (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) (by norm_num)
theorem B951869 : Blo 936583 951869 := bbase (se 3 (by rfl) ⟨178475, by rfl⟩ : syracuseStep 951869 = 356951) (by norm_num)
theorem B1410629 : Blo 936583 1410629 := bbase (se 4 (by rfl) ⟨132246, by rfl⟩ : syracuseStep 1410629 = 264493) (by norm_num)
theorem B1410653 : Blo 936583 1410653 := bbase (se 3 (by rfl) ⟨264497, by rfl⟩ : syracuseStep 1410653 = 528995) (by norm_num)
theorem B1410677 : Blo 936583 1410677 := bbase (se 5 (by rfl) ⟨66125, by rfl⟩ : syracuseStep 1410677 = 132251) (by norm_num)
theorem B1410701 : Blo 936583 1410701 := bbase (se 3 (by rfl) ⟨264506, by rfl⟩ : syracuseStep 1410701 = 529013) (by norm_num)
theorem B1410725 : Blo 936583 1410725 := bbase (se 4 (by rfl) ⟨132255, by rfl⟩ : syracuseStep 1410725 = 264511) (by norm_num)
theorem B1410749 : Blo 936583 1410749 := bbase (se 3 (by rfl) ⟨264515, by rfl⟩ : syracuseStep 1410749 = 529031) (by norm_num)
theorem B1410773 : Blo 936583 1410773 := bbase (se 7 (by rfl) ⟨16532, by rfl⟩ : syracuseStep 1410773 = 33065) (by norm_num)
theorem B1410797 : Blo 936583 1410797 := bbase (se 3 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 1410797 = 529049) (by norm_num)
theorem B1410821 : Blo 936583 1410821 := bbase (se 4 (by rfl) ⟨132264, by rfl⟩ : syracuseStep 1410821 = 264529) (by norm_num)
theorem B1410845 : Blo 936583 1410845 := bbase (se 3 (by rfl) ⟨264533, by rfl⟩ : syracuseStep 1410845 = 529067) (by norm_num)
theorem B1410869 : Blo 936583 1410869 := bbase (se 5 (by rfl) ⟨66134, by rfl⟩ : syracuseStep 1410869 = 132269) (by norm_num)
theorem B3376981 : Blo 936583 3376981 := bbase (se 9 (by rfl) ⟨9893, by rfl⟩ : syracuseStep 3376981 = 19787) (by norm_num)
theorem B1607509 : Blo 936583 1607509 := bbase (se 9 (by rfl) ⟨4709, by rfl⟩ : syracuseStep 1607509 = 9419) (by norm_num)
theorem B6096757 : Blo 936583 6096757 := bbase (se 5 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 6096757 = 571571) (by norm_num)
theorem B3213269 : Blo 936583 3213269 := bbase (se 7 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 3213269 = 75311) (by norm_num)
theorem B9635861 : Blo 936583 9635861 := bbase (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) (by norm_num)
theorem B2001037 : Blo 936583 2001037 := bbase (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) (by norm_num)
theorem B7604405 : Blo 936583 7604405 := bbase (se 5 (by rfl) ⟨356456, by rfl⟩ : syracuseStep 7604405 = 712913) (by norm_num)
theorem B1018049 : Blo 936583 1018049 := bbase (se 2 (by rfl) ⟨381768, by rfl⟩ : syracuseStep 1018049 = 763537) (by norm_num)
theorem B2034013 : Blo 936583 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B952769 : Blo 936583 952769 := bbase (se 2 (by rfl) ⟨357288, by rfl⟩ : syracuseStep 952769 = 714577) (by norm_num)
theorem B8554997 : Blo 936583 8554997 := bbase (se 5 (by rfl) ⟨401015, by rfl⟩ : syracuseStep 8554997 = 802031) (by norm_num)
theorem B953101 : Blo 936583 953101 := bbase (se 3 (by rfl) ⟨178706, by rfl⟩ : syracuseStep 953101 = 357413) (by norm_num)
theorem B4754213 : Blo 936583 4754213 := bbase (se 4 (by rfl) ⟨445707, by rfl⟩ : syracuseStep 4754213 = 891415) (by norm_num)
theorem B1608509 : Blo 936583 1608509 := bbase (se 3 (by rfl) ⟨301595, by rfl⟩ : syracuseStep 1608509 = 603191) (by norm_num)
theorem B1805141 : Blo 936583 1805141 := bbase (se 9 (by rfl) ⟨5288, by rfl⟩ : syracuseStep 1805141 = 10577) (by norm_num)
theorem B6753269 : Blo 936583 6753269 := bbase (se 5 (by rfl) ⟨316559, by rfl⟩ : syracuseStep 6753269 = 633119) (by norm_num)
theorem B2001925 : Blo 936583 2001925 := bbase (se 4 (by rfl) ⟨187680, by rfl⟩ : syracuseStep 2001925 = 375361) (by norm_num)
theorem B9767989 : Blo 936583 9767989 := bbase (se 5 (by rfl) ⟨457874, by rfl⟩ : syracuseStep 9767989 = 915749) (by norm_num)
theorem B1608797 : Blo 936583 1608797 := bbase (se 3 (by rfl) ⟨301649, by rfl⟩ : syracuseStep 1608797 = 603299) (by norm_num)
theorem B1903981 : Blo 936583 1903981 := bbase (se 3 (by rfl) ⟨356996, by rfl⟩ : syracuseStep 1903981 = 713993) (by norm_num)
theorem B2002421 : Blo 936583 2002421 := bbase (se 5 (by rfl) ⟨93863, by rfl⟩ : syracuseStep 2002421 = 187727) (by norm_num)
theorem B1740629 : Blo 936583 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B4820885 : Blo 936583 4820885 := bbase (se 6 (by rfl) ⟨112989, by rfl⟩ : syracuseStep 4820885 = 225979) (by norm_num)
theorem B1904581 : Blo 936583 1904581 := bbase (se 4 (by rfl) ⟨178554, by rfl⟩ : syracuseStep 1904581 = 357109) (by norm_num)
theorem B2854901 : Blo 936583 2854901 := bbase (se 5 (by rfl) ⟨133823, by rfl⟩ : syracuseStep 2854901 = 267647) (by norm_num)
theorem B4755509 : Blo 936583 4755509 := bbase (se 5 (by rfl) ⟨222914, by rfl⟩ : syracuseStep 4755509 = 445829) (by norm_num)
theorem B2854997 : Blo 936583 2854997 := bbase (se 8 (by rfl) ⟨16728, by rfl⟩ : syracuseStep 2854997 = 33457) (by norm_num)
theorem B2003285 : Blo 936583 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B5345621 : Blo 936583 5345621 := bbase (se 10 (by rfl) ⟨7830, by rfl⟩ : syracuseStep 5345621 = 15661) (by norm_num)
theorem B6951349 : Blo 936583 6951349 := bbase (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) (by norm_num)
theorem B2003429 : Blo 936583 2003429 := bbase (se 4 (by rfl) ⟨187821, by rfl⟩ : syracuseStep 2003429 = 375643) (by norm_num)
theorem B9015893 : Blo 936583 9015893 := bbase (se 8 (by rfl) ⟨52827, by rfl⟩ : syracuseStep 9015893 = 105655) (by norm_num)
theorem B1053661 : Blo 936583 1053661 := bbase (se 3 (by rfl) ⟨197561, by rfl⟩ : syracuseStep 1053661 = 395123) (by norm_num)
theorem B1053697 : Blo 936583 1053697 := bbase (se 2 (by rfl) ⟨395136, by rfl⟩ : syracuseStep 1053697 = 790273) (by norm_num)
theorem B4822037 : Blo 936583 4822037 := bbase (se 6 (by rfl) ⟨113016, by rfl⟩ : syracuseStep 4822037 = 226033) (by norm_num)
theorem B1053733 : Blo 936583 1053733 := bbase (se 4 (by rfl) ⟨98787, by rfl⟩ : syracuseStep 1053733 = 197575) (by norm_num)
theorem B1905709 : Blo 936583 1905709 := bbase (se 3 (by rfl) ⟨357320, by rfl⟩ : syracuseStep 1905709 = 714641) (by norm_num)
theorem B1053769 : Blo 936583 1053769 := bbase (se 2 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 1053769 = 790327) (by norm_num)
theorem B1053805 : Blo 936583 1053805 := bbase (se 3 (by rfl) ⟨197588, by rfl⟩ : syracuseStep 1053805 = 395177) (by norm_num)
theorem B1905781 : Blo 936583 1905781 := bbase (se 5 (by rfl) ⟨89333, by rfl⟩ : syracuseStep 1905781 = 178667) (by norm_num)
theorem B1053841 : Blo 936583 1053841 := bbase (se 2 (by rfl) ⟨395190, by rfl⟩ : syracuseStep 1053841 = 790381) (by norm_num)
theorem B1053877 : Blo 936583 1053877 := bbase (se 5 (by rfl) ⟨49400, by rfl⟩ : syracuseStep 1053877 = 98801) (by norm_num)
theorem B2004173 : Blo 936583 2004173 := bbase (se 3 (by rfl) ⟨375782, by rfl⟩ : syracuseStep 2004173 = 751565) (by norm_num)
theorem B1053913 : Blo 936583 1053913 := bbase (se 2 (by rfl) ⟨395217, by rfl⟩ : syracuseStep 1053913 = 790435) (by norm_num)
theorem B1053949 : Blo 936583 1053949 := bbase (se 3 (by rfl) ⟨197615, by rfl⟩ : syracuseStep 1053949 = 395231) (by norm_num)
theorem B1053985 : Blo 936583 1053985 := bbase (se 2 (by rfl) ⟨395244, by rfl⟩ : syracuseStep 1053985 = 790489) (by norm_num)
theorem B1054021 : Blo 936583 1054021 := bbase (se 4 (by rfl) ⟨98814, by rfl⟩ : syracuseStep 1054021 = 197629) (by norm_num)
theorem B4756805 : Blo 936583 4756805 := bbase (se 4 (by rfl) ⟨445950, by rfl⟩ : syracuseStep 4756805 = 891901) (by norm_num)
theorem B1054057 : Blo 936583 1054057 := bbase (se 2 (by rfl) ⟨395271, by rfl⟩ : syracuseStep 1054057 = 790543) (by norm_num)
theorem B1054093 : Blo 936583 1054093 := bbase (se 3 (by rfl) ⟨197642, by rfl⟩ : syracuseStep 1054093 = 395285) (by norm_num)
theorem B1054129 : Blo 936583 1054129 := bbase (se 2 (by rfl) ⟨395298, by rfl⟩ : syracuseStep 1054129 = 790597) (by norm_num)
theorem B1054165 : Blo 936583 1054165 := bbase (se 7 (by rfl) ⟨12353, by rfl⟩ : syracuseStep 1054165 = 24707) (by norm_num)
theorem B1054201 : Blo 936583 1054201 := bbase (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) (by norm_num)
theorem B1283581 : Blo 936583 1283581 := bbase (se 3 (by rfl) ⟨240671, by rfl⟩ : syracuseStep 1283581 = 481343) (by norm_num)
theorem B1054237 : Blo 936583 1054237 := bbase (se 3 (by rfl) ⟨197669, by rfl⟩ : syracuseStep 1054237 = 395339) (by norm_num)
theorem B1054273 : Blo 936583 1054273 := bbase (se 2 (by rfl) ⟨395352, by rfl⟩ : syracuseStep 1054273 = 790705) (by norm_num)
theorem B1054309 : Blo 936583 1054309 := bbase (se 4 (by rfl) ⟨98841, by rfl⟩ : syracuseStep 1054309 = 197683) (by norm_num)
theorem B1054345 : Blo 936583 1054345 := bbase (se 2 (by rfl) ⟨395379, by rfl⟩ : syracuseStep 1054345 = 790759) (by norm_num)
theorem B1185445 : Blo 936583 1185445 := bbase (se 4 (by rfl) ⟨111135, by rfl⟩ : syracuseStep 1185445 = 222271) (by norm_num)
theorem B1054381 : Blo 936583 1054381 := bbase (se 3 (by rfl) ⟨197696, by rfl⟩ : syracuseStep 1054381 = 395393) (by norm_num)
theorem B1054417 : Blo 936583 1054417 := bbase (se 2 (by rfl) ⟨395406, by rfl⟩ : syracuseStep 1054417 = 790813) (by norm_num)
theorem B1054453 : Blo 936583 1054453 := bbase (se 5 (by rfl) ⟨49427, by rfl⟩ : syracuseStep 1054453 = 98855) (by norm_num)
theorem B1054489 : Blo 936583 1054489 := bbase (se 2 (by rfl) ⟨395433, by rfl⟩ : syracuseStep 1054489 = 790867) (by norm_num)
theorem B1054525 : Blo 936583 1054525 := bbase (se 3 (by rfl) ⟨197723, by rfl⟩ : syracuseStep 1054525 = 395447) (by norm_num)
theorem B1185617 : Blo 936583 1185617 := bbase (se 2 (by rfl) ⟨444606, by rfl⟩ : syracuseStep 1185617 = 889213) (by norm_num)
theorem B1054561 : Blo 936583 1054561 := bbase (se 2 (by rfl) ⟨395460, by rfl⟩ : syracuseStep 1054561 = 790921) (by norm_num)
theorem B1054597 : Blo 936583 1054597 := bbase (se 4 (by rfl) ⟨98868, by rfl⟩ : syracuseStep 1054597 = 197737) (by norm_num)
theorem B1185673 : Blo 936583 1185673 := bbase (se 2 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 1185673 = 889255) (by norm_num)
theorem B1054633 : Blo 936583 1054633 := bbase (se 2 (by rfl) ⟨395487, by rfl⟩ : syracuseStep 1054633 = 790975) (by norm_num)
theorem B2004925 : Blo 936583 2004925 := bbase (se 3 (by rfl) ⟨375923, by rfl⟩ : syracuseStep 2004925 = 751847) (by norm_num)
theorem B1054669 : Blo 936583 1054669 := bbase (se 3 (by rfl) ⟨197750, by rfl⟩ : syracuseStep 1054669 = 395501) (by norm_num)
theorem B1185769 : Blo 936583 1185769 := bbase (se 2 (by rfl) ⟨444663, by rfl⟩ : syracuseStep 1185769 = 889327) (by norm_num)
theorem B1054705 : Blo 936583 1054705 := bbase (se 2 (by rfl) ⟨395514, by rfl⟩ : syracuseStep 1054705 = 791029) (by norm_num)
theorem B1054741 : Blo 936583 1054741 := bbase (se 6 (by rfl) ⟨24720, by rfl⟩ : syracuseStep 1054741 = 49441) (by norm_num)
theorem B1054777 : Blo 936583 1054777 := bbase (se 2 (by rfl) ⟨395541, by rfl⟩ : syracuseStep 1054777 = 791083) (by norm_num)
theorem B2005069 : Blo 936583 2005069 := bbase (se 3 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 2005069 = 751901) (by norm_num)
theorem B10688597 : Blo 936583 10688597 := bbase (se 8 (by rfl) ⟨62628, by rfl⟩ : syracuseStep 10688597 = 125257) (by norm_num)
theorem B1054813 : Blo 936583 1054813 := bbase (se 3 (by rfl) ⟨197777, by rfl⟩ : syracuseStep 1054813 = 395555) (by norm_num)
theorem B3381365 : Blo 936583 3381365 := bbase (se 5 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 3381365 = 317003) (by norm_num)
theorem B1054849 : Blo 936583 1054849 := bbase (se 2 (by rfl) ⟨395568, by rfl⟩ : syracuseStep 1054849 = 791137) (by norm_num)
theorem B1185941 : Blo 936583 1185941 := bbase (se 6 (by rfl) ⟨27795, by rfl⟩ : syracuseStep 1185941 = 55591) (by norm_num)
theorem B1054885 : Blo 936583 1054885 := bbase (se 4 (by rfl) ⟨98895, by rfl⟩ : syracuseStep 1054885 = 197791) (by norm_num)
theorem B1054921 : Blo 936583 1054921 := bbase (se 2 (by rfl) ⟨395595, by rfl⟩ : syracuseStep 1054921 = 791191) (by norm_num)
theorem B1185997 : Blo 936583 1185997 := bbase (se 3 (by rfl) ⟨222374, by rfl⟩ : syracuseStep 1185997 = 444749) (by norm_num)
theorem B1054957 : Blo 936583 1054957 := bbase (se 3 (by rfl) ⟨197804, by rfl⟩ : syracuseStep 1054957 = 395609) (by norm_num)
theorem B1054993 : Blo 936583 1054993 := bbase (se 2 (by rfl) ⟨395622, by rfl⟩ : syracuseStep 1054993 = 791245) (by norm_num)
theorem B1186093 : Blo 936583 1186093 := bbase (se 3 (by rfl) ⟨222392, by rfl⟩ : syracuseStep 1186093 = 444785) (by norm_num)
theorem B1055029 : Blo 936583 1055029 := bbase (se 5 (by rfl) ⟨49454, by rfl⟩ : syracuseStep 1055029 = 98909) (by norm_num)
theorem B1055065 : Blo 936583 1055065 := bbase (se 2 (by rfl) ⟨395649, by rfl⟩ : syracuseStep 1055065 = 791299) (by norm_num)
theorem B1055101 : Blo 936583 1055101 := bbase (se 3 (by rfl) ⟨197831, by rfl⟩ : syracuseStep 1055101 = 395663) (by norm_num)
theorem B1055137 : Blo 936583 1055137 := bbase (se 2 (by rfl) ⟨395676, by rfl⟩ : syracuseStep 1055137 = 791353) (by norm_num)
theorem B4004261 : Blo 936583 4004261 := bbase (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) (by norm_num)
theorem B1055173 : Blo 936583 1055173 := bbase (se 4 (by rfl) ⟨98922, by rfl⟩ : syracuseStep 1055173 = 197845) (by norm_num)
theorem B2005445 : Blo 936583 2005445 := bbase (se 4 (by rfl) ⟨188010, by rfl⟩ : syracuseStep 2005445 = 376021) (by norm_num)
theorem B3807701 : Blo 936583 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B1186265 : Blo 936583 1186265 := bbase (se 2 (by rfl) ⟨444849, by rfl⟩ : syracuseStep 1186265 = 889699) (by norm_num)
theorem B1055209 : Blo 936583 1055209 := bbase (se 2 (by rfl) ⟨395703, by rfl⟩ : syracuseStep 1055209 = 791407) (by norm_num)
theorem B1055245 : Blo 936583 1055245 := bbase (se 3 (by rfl) ⟨197858, by rfl⟩ : syracuseStep 1055245 = 395717) (by norm_num)
theorem B1186321 : Blo 936583 1186321 := bbase (se 2 (by rfl) ⟨444870, by rfl⟩ : syracuseStep 1186321 = 889741) (by norm_num)
theorem B1055281 : Blo 936583 1055281 := bbase (se 2 (by rfl) ⟨395730, by rfl⟩ : syracuseStep 1055281 = 791461) (by norm_num)
theorem B1055317 : Blo 936583 1055317 := bbase (se 8 (by rfl) ⟨6183, by rfl⟩ : syracuseStep 1055317 = 12367) (by norm_num)
theorem B4758101 : Blo 936583 4758101 := bbase (se 8 (by rfl) ⟨27879, by rfl⟩ : syracuseStep 4758101 = 55759) (by norm_num)
theorem B1186417 : Blo 936583 1186417 := bbase (se 2 (by rfl) ⟨444906, by rfl⟩ : syracuseStep 1186417 = 889813) (by norm_num)
theorem B1055353 : Blo 936583 1055353 := bbase (se 2 (by rfl) ⟨395757, by rfl⟩ : syracuseStep 1055353 = 791515) (by norm_num)
theorem B1055389 : Blo 936583 1055389 := bbase (se 3 (by rfl) ⟨197885, by rfl⟩ : syracuseStep 1055389 = 395771) (by norm_num)
theorem B1055425 : Blo 936583 1055425 := bbase (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) (by norm_num)
theorem B1055461 : Blo 936583 1055461 := bbase (se 4 (by rfl) ⟨98949, by rfl⟩ : syracuseStep 1055461 = 197899) (by norm_num)
theorem B1055497 : Blo 936583 1055497 := bbase (se 2 (by rfl) ⟨395811, by rfl⟩ : syracuseStep 1055497 = 791623) (by norm_num)
theorem B1186589 : Blo 936583 1186589 := bbase (se 3 (by rfl) ⟨222485, by rfl⟩ : syracuseStep 1186589 = 444971) (by norm_num)
theorem B1055533 : Blo 936583 1055533 := bbase (se 3 (by rfl) ⟨197912, by rfl⟩ : syracuseStep 1055533 = 395825) (by norm_num)
theorem B2005813 : Blo 936583 2005813 := bbase (se 5 (by rfl) ⟨94022, by rfl⟩ : syracuseStep 2005813 = 188045) (by norm_num)
theorem B1055569 : Blo 936583 1055569 := bbase (se 2 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 1055569 = 791677) (by norm_num)
theorem B1186645 : Blo 936583 1186645 := bbase (se 9 (by rfl) ⟨3476, by rfl⟩ : syracuseStep 1186645 = 6953) (by norm_num)
theorem B1055605 : Blo 936583 1055605 := bbase (se 5 (by rfl) ⟨49481, by rfl⟩ : syracuseStep 1055605 = 98963) (by norm_num)
theorem B1055641 : Blo 936583 1055641 := bbase (se 2 (by rfl) ⟨395865, by rfl⟩ : syracuseStep 1055641 = 791731) (by norm_num)
theorem B1186741 : Blo 936583 1186741 := bbase (se 5 (by rfl) ⟨55628, by rfl⟩ : syracuseStep 1186741 = 111257) (by norm_num)
theorem B1055677 : Blo 936583 1055677 := bbase (se 3 (by rfl) ⟨197939, by rfl⟩ : syracuseStep 1055677 = 395879) (by norm_num)
theorem B1055713 : Blo 936583 1055713 := bbase (se 2 (by rfl) ⟨395892, by rfl⟩ : syracuseStep 1055713 = 791785) (by norm_num)
theorem B1055749 : Blo 936583 1055749 := bbase (se 4 (by rfl) ⟨98976, by rfl⟩ : syracuseStep 1055749 = 197953) (by norm_num)
theorem B1055785 : Blo 936583 1055785 := bbase (se 2 (by rfl) ⟨395919, by rfl⟩ : syracuseStep 1055785 = 791839) (by norm_num)
theorem B1055821 : Blo 936583 1055821 := bbase (se 3 (by rfl) ⟨197966, by rfl⟩ : syracuseStep 1055821 = 395933) (by norm_num)
theorem B1186913 : Blo 936583 1186913 := bbase (se 2 (by rfl) ⟨445092, by rfl⟩ : syracuseStep 1186913 = 890185) (by norm_num)
theorem B1055857 : Blo 936583 1055857 := bbase (se 2 (by rfl) ⟨395946, by rfl⟩ : syracuseStep 1055857 = 791893) (by norm_num)
theorem B1055893 : Blo 936583 1055893 := bbase (se 6 (by rfl) ⟨24747, by rfl⟩ : syracuseStep 1055893 = 49495) (by norm_num)
theorem B1186969 : Blo 936583 1186969 := bbase (se 2 (by rfl) ⟨445113, by rfl⟩ : syracuseStep 1186969 = 890227) (by norm_num)
theorem B1055929 : Blo 936583 1055929 := bbase (se 2 (by rfl) ⟨395973, by rfl⟩ : syracuseStep 1055929 = 791947) (by norm_num)
theorem B1055965 : Blo 936583 1055965 := bbase (se 3 (by rfl) ⟨197993, by rfl⟩ : syracuseStep 1055965 = 395987) (by norm_num)
theorem B1187065 : Blo 936583 1187065 := bbase (se 2 (by rfl) ⟨445149, by rfl⟩ : syracuseStep 1187065 = 890299) (by norm_num)
theorem B1056001 : Blo 936583 1056001 := bbase (se 2 (by rfl) ⟨396000, by rfl⟩ : syracuseStep 1056001 = 792001) (by norm_num)
theorem B1056037 : Blo 936583 1056037 := bbase (se 4 (by rfl) ⟨99003, by rfl⟩ : syracuseStep 1056037 = 198007) (by norm_num)
theorem B1056073 : Blo 936583 1056073 := bbase (se 2 (by rfl) ⟨396027, by rfl⟩ : syracuseStep 1056073 = 792055) (by norm_num)
theorem B1056109 : Blo 936583 1056109 := bbase (se 3 (by rfl) ⟨198020, by rfl⟩ : syracuseStep 1056109 = 396041) (by norm_num)
theorem B1056145 : Blo 936583 1056145 := bbase (se 2 (by rfl) ⟨396054, by rfl⟩ : syracuseStep 1056145 = 792109) (by norm_num)
theorem B1187237 : Blo 936583 1187237 := bbase (se 4 (by rfl) ⟨111303, by rfl⟩ : syracuseStep 1187237 = 222607) (by norm_num)
theorem B1056181 : Blo 936583 1056181 := bbase (se 5 (by rfl) ⟨49508, by rfl⟩ : syracuseStep 1056181 = 99017) (by norm_num)
theorem B1580485 : Blo 936583 1580485 := bbase (se 4 (by rfl) ⟨148170, by rfl⟩ : syracuseStep 1580485 = 296341) (by norm_num)
theorem B1056217 : Blo 936583 1056217 := bbase (se 2 (by rfl) ⟨396081, by rfl⟩ : syracuseStep 1056217 = 792163) (by norm_num)
theorem B1187293 : Blo 936583 1187293 := bbase (se 3 (by rfl) ⟨222617, by rfl⟩ : syracuseStep 1187293 = 445235) (by norm_num)
theorem B1056253 : Blo 936583 1056253 := bbase (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) (by norm_num)
theorem B1580573 : Blo 936583 1580573 := bbase (se 3 (by rfl) ⟨296357, by rfl⟩ : syracuseStep 1580573 = 592715) (by norm_num)
theorem B1056289 : Blo 936583 1056289 := bbase (se 2 (by rfl) ⟨396108, by rfl⟩ : syracuseStep 1056289 = 792217) (by norm_num)
theorem B1187389 : Blo 936583 1187389 := bbase (se 3 (by rfl) ⟨222635, by rfl⟩ : syracuseStep 1187389 = 445271) (by norm_num)
theorem B1056325 : Blo 936583 1056325 := bbase (se 4 (by rfl) ⟨99030, by rfl⟩ : syracuseStep 1056325 = 198061) (by norm_num)
theorem B1056361 : Blo 936583 1056361 := bbase (se 2 (by rfl) ⟨396135, by rfl⟩ : syracuseStep 1056361 = 792271) (by norm_num)
theorem B1056397 : Blo 936583 1056397 := bbase (se 3 (by rfl) ⟨198074, by rfl⟩ : syracuseStep 1056397 = 396149) (by norm_num)
theorem B1580701 : Blo 936583 1580701 := bbase (se 3 (by rfl) ⟨296381, by rfl⟩ : syracuseStep 1580701 = 592763) (by norm_num)
theorem B1056433 : Blo 936583 1056433 := bbase (se 2 (by rfl) ⟨396162, by rfl⟩ : syracuseStep 1056433 = 792325) (by norm_num)
theorem B1056469 : Blo 936583 1056469 := bbase (se 7 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 1056469 = 24761) (by norm_num)
theorem B1187561 : Blo 936583 1187561 := bbase (se 2 (by rfl) ⟨445335, by rfl⟩ : syracuseStep 1187561 = 890671) (by norm_num)
theorem B1580789 : Blo 936583 1580789 := bbase (se 5 (by rfl) ⟨74099, by rfl⟩ : syracuseStep 1580789 = 148199) (by norm_num)
theorem B1056505 : Blo 936583 1056505 := bbase (se 2 (by rfl) ⟨396189, by rfl⟩ : syracuseStep 1056505 = 792379) (by norm_num)
theorem B1056541 : Blo 936583 1056541 := bbase (se 3 (by rfl) ⟨198101, by rfl⟩ : syracuseStep 1056541 = 396203) (by norm_num)
theorem B1187617 : Blo 936583 1187617 := bbase (se 2 (by rfl) ⟨445356, by rfl⟩ : syracuseStep 1187617 = 890713) (by norm_num)
theorem B3383093 : Blo 936583 3383093 := bbase (se 5 (by rfl) ⟨158582, by rfl⟩ : syracuseStep 3383093 = 317165) (by norm_num)
theorem B1056577 : Blo 936583 1056577 := bbase (se 2 (by rfl) ⟨396216, by rfl⟩ : syracuseStep 1056577 = 792433) (by norm_num)
theorem B1056613 : Blo 936583 1056613 := bbase (se 4 (by rfl) ⟨99057, by rfl⟩ : syracuseStep 1056613 = 198115) (by norm_num)
theorem B4759397 : Blo 936583 4759397 := bbase (se 4 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 4759397 = 892387) (by norm_num)
theorem B1580917 : Blo 936583 1580917 := bbase (se 5 (by rfl) ⟨74105, by rfl⟩ : syracuseStep 1580917 = 148211) (by norm_num)
theorem B1187713 : Blo 936583 1187713 := bbase (se 2 (by rfl) ⟨445392, by rfl⟩ : syracuseStep 1187713 = 890785) (by norm_num)
theorem B1056649 : Blo 936583 1056649 := bbase (se 2 (by rfl) ⟨396243, by rfl⟩ : syracuseStep 1056649 = 792487) (by norm_num)
theorem B1056685 : Blo 936583 1056685 := bbase (se 3 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 1056685 = 396257) (by norm_num)
theorem B1581005 : Blo 936583 1581005 := bbase (se 3 (by rfl) ⟨296438, by rfl⟩ : syracuseStep 1581005 = 592877) (by norm_num)
theorem B1056721 : Blo 936583 1056721 := bbase (se 2 (by rfl) ⟨396270, by rfl⟩ : syracuseStep 1056721 = 792541) (by norm_num)
theorem B1056757 : Blo 936583 1056757 := bbase (se 5 (by rfl) ⟨49535, by rfl⟩ : syracuseStep 1056757 = 99071) (by norm_num)
theorem B1056793 : Blo 936583 1056793 := bbase (se 2 (by rfl) ⟨396297, by rfl⟩ : syracuseStep 1056793 = 792595) (by norm_num)
theorem B1187885 : Blo 936583 1187885 := bbase (se 3 (by rfl) ⟨222728, by rfl⟩ : syracuseStep 1187885 = 445457) (by norm_num)
theorem B2138165 : Blo 936583 2138165 := bbase (se 5 (by rfl) ⟨100226, by rfl⟩ : syracuseStep 2138165 = 200453) (by norm_num)
theorem B1056829 : Blo 936583 1056829 := bbase (se 3 (by rfl) ⟨198155, by rfl⟩ : syracuseStep 1056829 = 396311) (by norm_num)
theorem B1581133 : Blo 936583 1581133 := bbase (se 3 (by rfl) ⟨296462, by rfl⟩ : syracuseStep 1581133 = 592925) (by norm_num)
theorem B1056865 : Blo 936583 1056865 := bbase (se 2 (by rfl) ⟨396324, by rfl⟩ : syracuseStep 1056865 = 792649) (by norm_num)
theorem B1187941 : Blo 936583 1187941 := bbase (se 4 (by rfl) ⟨111369, by rfl⟩ : syracuseStep 1187941 = 222739) (by norm_num)
theorem B1056901 : Blo 936583 1056901 := bbase (se 4 (by rfl) ⟨99084, by rfl⟩ : syracuseStep 1056901 = 198169) (by norm_num)
theorem B6758549 : Blo 936583 6758549 := bbase (se 6 (by rfl) ⟨158403, by rfl⟩ : syracuseStep 6758549 = 316807) (by norm_num)
theorem B4006037 : Blo 936583 4006037 := bbase (se 6 (by rfl) ⟨93891, by rfl⟩ : syracuseStep 4006037 = 187783) (by norm_num)
theorem B1581221 : Blo 936583 1581221 := bbase (se 4 (by rfl) ⟨148239, by rfl⟩ : syracuseStep 1581221 = 296479) (by norm_num)
theorem B1056937 : Blo 936583 1056937 := bbase (se 2 (by rfl) ⟨396351, by rfl⟩ : syracuseStep 1056937 = 792703) (by norm_num)
theorem B1188037 : Blo 936583 1188037 := bbase (se 4 (by rfl) ⟨111378, by rfl⟩ : syracuseStep 1188037 = 222757) (by norm_num)
theorem B1056973 : Blo 936583 1056973 := bbase (se 3 (by rfl) ⟨198182, by rfl⟩ : syracuseStep 1056973 = 396365) (by norm_num)
theorem B1057009 : Blo 936583 1057009 := bbase (se 2 (by rfl) ⟨396378, by rfl⟩ : syracuseStep 1057009 = 792757) (by norm_num)
theorem B1057045 : Blo 936583 1057045 := bbase (se 6 (by rfl) ⟨24774, by rfl⟩ : syracuseStep 1057045 = 49549) (by norm_num)
theorem B2007317 : Blo 936583 2007317 := bbase (se 6 (by rfl) ⟨47046, by rfl⟩ : syracuseStep 2007317 = 94093) (by norm_num)
theorem B1581349 : Blo 936583 1581349 := bbase (se 4 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 1581349 = 296503) (by norm_num)
theorem B1057081 : Blo 936583 1057081 := bbase (se 2 (by rfl) ⟨396405, by rfl⟩ : syracuseStep 1057081 = 792811) (by norm_num)
theorem B1057117 : Blo 936583 1057117 := bbase (se 3 (by rfl) ⟨198209, by rfl⟩ : syracuseStep 1057117 = 396419) (by norm_num)
theorem B1188209 : Blo 936583 1188209 := bbase (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) (by norm_num)
theorem B1581437 : Blo 936583 1581437 := bbase (se 3 (by rfl) ⟨296519, by rfl⟩ : syracuseStep 1581437 = 593039) (by norm_num)
theorem B1057153 : Blo 936583 1057153 := bbase (se 2 (by rfl) ⟨396432, by rfl⟩ : syracuseStep 1057153 = 792865) (by norm_num)
theorem B1057189 : Blo 936583 1057189 := bbase (se 4 (by rfl) ⟨99111, by rfl⟩ : syracuseStep 1057189 = 198223) (by norm_num)
theorem B2007461 : Blo 936583 2007461 := bbase (se 4 (by rfl) ⟨188199, by rfl⟩ : syracuseStep 2007461 = 376399) (by norm_num)
theorem B1188265 : Blo 936583 1188265 := bbase (se 2 (by rfl) ⟨445599, by rfl⟩ : syracuseStep 1188265 = 891199) (by norm_num)
theorem B1057225 : Blo 936583 1057225 := bbase (se 2 (by rfl) ⟨396459, by rfl⟩ : syracuseStep 1057225 = 792919) (by norm_num)
theorem B1057261 : Blo 936583 1057261 := bbase (se 3 (by rfl) ⟨198236, by rfl⟩ : syracuseStep 1057261 = 396473) (by norm_num)
theorem B1581565 : Blo 936583 1581565 := bbase (se 3 (by rfl) ⟨296543, by rfl⟩ : syracuseStep 1581565 = 593087) (by norm_num)
theorem B1188361 : Blo 936583 1188361 := bbase (se 2 (by rfl) ⟨445635, by rfl⟩ : syracuseStep 1188361 = 891271) (by norm_num)
theorem B1057297 : Blo 936583 1057297 := bbase (se 2 (by rfl) ⟨396486, by rfl⟩ : syracuseStep 1057297 = 792973) (by norm_num)
theorem B1778213 : Blo 936583 1778213 := bbase (se 4 (by rfl) ⟨166707, by rfl⟩ : syracuseStep 1778213 = 333415) (by norm_num)
theorem B2531893 : Blo 936583 2531893 := bbase (se 5 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 2531893 = 237365) (by norm_num)
theorem B7119413 : Blo 936583 7119413 := bbase (se 5 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 7119413 = 667445) (by norm_num)
theorem B1057333 : Blo 936583 1057333 := bbase (se 5 (by rfl) ⟨49562, by rfl⟩ : syracuseStep 1057333 = 99125) (by norm_num)
theorem B1581653 : Blo 936583 1581653 := bbase (se 8 (by rfl) ⟨9267, by rfl⟩ : syracuseStep 1581653 = 18535) (by norm_num)
theorem B1057369 : Blo 936583 1057369 := bbase (se 2 (by rfl) ⟨396513, by rfl⟩ : syracuseStep 1057369 = 793027) (by norm_num)
theorem B1057405 : Blo 936583 1057405 := bbase (se 3 (by rfl) ⟨198263, by rfl⟩ : syracuseStep 1057405 = 396527) (by norm_num)
theorem B1057441 : Blo 936583 1057441 := bbase (se 2 (by rfl) ⟨396540, by rfl⟩ : syracuseStep 1057441 = 793081) (by norm_num)
theorem B1188533 : Blo 936583 1188533 := bbase (se 5 (by rfl) ⟨55712, by rfl⟩ : syracuseStep 1188533 = 111425) (by norm_num)
theorem B1778365 : Blo 936583 1778365 := bbase (se 3 (by rfl) ⟨333443, by rfl⟩ : syracuseStep 1778365 = 666887) (by norm_num)
theorem B1057477 : Blo 936583 1057477 := bbase (se 4 (by rfl) ⟨99138, by rfl⟩ : syracuseStep 1057477 = 198277) (by norm_num)
theorem B1581781 : Blo 936583 1581781 := bbase (se 7 (by rfl) ⟨18536, by rfl⟩ : syracuseStep 1581781 = 37073) (by norm_num)
theorem B1057513 : Blo 936583 1057513 := bbase (se 2 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 1057513 = 793135) (by norm_num)
theorem B1188589 : Blo 936583 1188589 := bbase (se 3 (by rfl) ⟨222860, by rfl⟩ : syracuseStep 1188589 = 445721) (by norm_num)
theorem B1057549 : Blo 936583 1057549 := bbase (se 3 (by rfl) ⟨198290, by rfl⟩ : syracuseStep 1057549 = 396581) (by norm_num)
theorem B2007821 : Blo 936583 2007821 := bbase (se 3 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 2007821 = 752933) (by norm_num)
theorem B1581869 : Blo 936583 1581869 := bbase (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) (by norm_num)
theorem B1057585 : Blo 936583 1057585 := bbase (se 2 (by rfl) ⟨396594, by rfl⟩ : syracuseStep 1057585 = 793189) (by norm_num)
theorem B1188685 : Blo 936583 1188685 := bbase (se 3 (by rfl) ⟨222878, by rfl⟩ : syracuseStep 1188685 = 445757) (by norm_num)
theorem B1057621 : Blo 936583 1057621 := bbase (se 9 (by rfl) ⟨3098, by rfl⟩ : syracuseStep 1057621 = 6197) (by norm_num)
theorem B1057657 : Blo 936583 1057657 := bbase (se 2 (by rfl) ⟨396621, by rfl⟩ : syracuseStep 1057657 = 793243) (by norm_num)
theorem B1057693 : Blo 936583 1057693 := bbase (se 3 (by rfl) ⟨198317, by rfl⟩ : syracuseStep 1057693 = 396635) (by norm_num)
theorem B1581997 : Blo 936583 1581997 := bbase (se 3 (by rfl) ⟨296624, by rfl⟩ : syracuseStep 1581997 = 593249) (by norm_num)
theorem B2139061 : Blo 936583 2139061 := bbase (se 5 (by rfl) ⟨100268, by rfl⟩ : syracuseStep 2139061 = 200537) (by norm_num)
theorem B1057729 : Blo 936583 1057729 := bbase (se 2 (by rfl) ⟨396648, by rfl⟩ : syracuseStep 1057729 = 793297) (by norm_num)
theorem B1057765 : Blo 936583 1057765 := bbase (se 4 (by rfl) ⟨99165, by rfl⟩ : syracuseStep 1057765 = 198331) (by norm_num)
theorem B1778669 : Blo 936583 1778669 := bbase (se 3 (by rfl) ⟨333500, by rfl⟩ : syracuseStep 1778669 = 667001) (by norm_num)
theorem B1188857 : Blo 936583 1188857 := bbase (se 2 (by rfl) ⟨445821, by rfl⟩ : syracuseStep 1188857 = 891643) (by norm_num)
theorem B1582085 : Blo 936583 1582085 := bbase (se 4 (by rfl) ⟨148320, by rfl⟩ : syracuseStep 1582085 = 296641) (by norm_num)
theorem B1057801 : Blo 936583 1057801 := bbase (se 2 (by rfl) ⟨396675, by rfl⟩ : syracuseStep 1057801 = 793351) (by norm_num)
theorem B1057837 : Blo 936583 1057837 := bbase (se 3 (by rfl) ⟨198344, by rfl⟩ : syracuseStep 1057837 = 396689) (by norm_num)
theorem B1188913 : Blo 936583 1188913 := bbase (se 2 (by rfl) ⟨445842, by rfl⟩ : syracuseStep 1188913 = 891685) (by norm_num)
theorem B1057873 : Blo 936583 1057873 := bbase (se 2 (by rfl) ⟨396702, by rfl⟩ : syracuseStep 1057873 = 793405) (by norm_num)
theorem B4007029 : Blo 936583 4007029 := bbase (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) (by norm_num)
theorem B1057909 : Blo 936583 1057909 := bbase (se 5 (by rfl) ⟨49589, by rfl⟩ : syracuseStep 1057909 = 99179) (by norm_num)
theorem B4760693 : Blo 936583 4760693 := bbase (se 5 (by rfl) ⟨223157, by rfl⟩ : syracuseStep 4760693 = 446315) (by norm_num)
theorem B1582213 : Blo 936583 1582213 := bbase (se 4 (by rfl) ⟨148332, by rfl⟩ : syracuseStep 1582213 = 296665) (by norm_num)
theorem B1189009 : Blo 936583 1189009 := bbase (se 2 (by rfl) ⟨445878, by rfl⟩ : syracuseStep 1189009 = 891757) (by norm_num)
theorem B1057945 : Blo 936583 1057945 := bbase (se 2 (by rfl) ⟨396729, by rfl⟩ : syracuseStep 1057945 = 793459) (by norm_num)
theorem B1057981 : Blo 936583 1057981 := bbase (se 3 (by rfl) ⟨198371, by rfl⟩ : syracuseStep 1057981 = 396743) (by norm_num)
theorem B1582301 : Blo 936583 1582301 := bbase (se 3 (by rfl) ⟨296681, by rfl⟩ : syracuseStep 1582301 = 593363) (by norm_num)
theorem B1058017 : Blo 936583 1058017 := bbase (se 2 (by rfl) ⟨396756, by rfl⟩ : syracuseStep 1058017 = 793513) (by norm_num)
theorem B1058053 : Blo 936583 1058053 := bbase (se 4 (by rfl) ⟨99192, by rfl⟩ : syracuseStep 1058053 = 198385) (by norm_num)
theorem B1058089 : Blo 936583 1058089 := bbase (se 2 (by rfl) ⟨396783, by rfl⟩ : syracuseStep 1058089 = 793567) (by norm_num)
theorem B1189181 : Blo 936583 1189181 := bbase (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) (by norm_num)
theorem B1058125 : Blo 936583 1058125 := bbase (se 3 (by rfl) ⟨198398, by rfl⟩ : syracuseStep 1058125 = 396797) (by norm_num)
theorem B1582429 : Blo 936583 1582429 := bbase (se 3 (by rfl) ⟨296705, by rfl⟩ : syracuseStep 1582429 = 593411) (by norm_num)
theorem B1189237 : Blo 936583 1189237 := bbase (se 5 (by rfl) ⟨55745, by rfl⟩ : syracuseStep 1189237 = 111491) (by norm_num)
theorem B1582517 : Blo 936583 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B1189333 : Blo 936583 1189333 := bbase (se 7 (by rfl) ⟨13937, by rfl⟩ : syracuseStep 1189333 = 27875) (by norm_num)
theorem B1582645 : Blo 936583 1582645 := bbase (se 5 (by rfl) ⟨74186, by rfl⟩ : syracuseStep 1582645 = 148373) (by norm_num)
theorem B1189505 : Blo 936583 1189505 := bbase (se 2 (by rfl) ⟨446064, by rfl⟩ : syracuseStep 1189505 = 892129) (by norm_num)
theorem B2008709 : Blo 936583 2008709 := bbase (se 4 (by rfl) ⟨188316, by rfl⟩ : syracuseStep 2008709 = 376633) (by norm_num)
theorem B1582733 : Blo 936583 1582733 := bbase (se 3 (by rfl) ⟨296762, by rfl⟩ : syracuseStep 1582733 = 593525) (by norm_num)
theorem B1189561 : Blo 936583 1189561 := bbase (se 2 (by rfl) ⟨446085, by rfl⟩ : syracuseStep 1189561 = 892171) (by norm_num)
theorem B1779421 : Blo 936583 1779421 := bbase (se 3 (by rfl) ⟨333641, by rfl⟩ : syracuseStep 1779421 = 667283) (by norm_num)
theorem B1582861 : Blo 936583 1582861 := bbase (se 3 (by rfl) ⟨296786, by rfl⟩ : syracuseStep 1582861 = 593573) (by norm_num)
theorem B1189657 : Blo 936583 1189657 := bbase (se 2 (by rfl) ⟨446121, by rfl⟩ : syracuseStep 1189657 = 892243) (by norm_num)
theorem B1582949 : Blo 936583 1582949 := bbase (se 4 (by rfl) ⟨148401, by rfl⟩ : syracuseStep 1582949 = 296803) (by norm_num)
theorem B1779565 : Blo 936583 1779565 := bbase (se 3 (by rfl) ⟨333668, by rfl⟩ : syracuseStep 1779565 = 667337) (by norm_num)
theorem B1353613 : Blo 936583 1353613 := bbase (se 3 (by rfl) ⟨253802, by rfl⟩ : syracuseStep 1353613 = 507605) (by norm_num)
theorem B1189829 : Blo 936583 1189829 := bbase (se 4 (by rfl) ⟨111546, by rfl⟩ : syracuseStep 1189829 = 223093) (by norm_num)
theorem B2107349 : Blo 936583 2107349 := bbase (se 7 (by rfl) ⟨24695, by rfl⟩ : syracuseStep 2107349 = 49391) (by norm_num)
theorem B1583077 : Blo 936583 1583077 := bbase (se 4 (by rfl) ⟨148413, by rfl⟩ : syracuseStep 1583077 = 296827) (by norm_num)
theorem B1189885 : Blo 936583 1189885 := bbase (se 3 (by rfl) ⟨223103, by rfl⟩ : syracuseStep 1189885 = 446207) (by norm_num)
theorem B1779725 : Blo 936583 1779725 := bbase (se 3 (by rfl) ⟨333698, by rfl⟩ : syracuseStep 1779725 = 667397) (by norm_num)
theorem B12003349 : Blo 936583 12003349 := bbase (se 6 (by rfl) ⟨281328, by rfl⟩ : syracuseStep 12003349 = 562657) (by norm_num)
theorem B2107421 : Blo 936583 2107421 := bbase (se 3 (by rfl) ⟨395141, by rfl⟩ : syracuseStep 2107421 = 790283) (by norm_num)
theorem B1583165 : Blo 936583 1583165 := bbase (se 3 (by rfl) ⟨296843, by rfl⟩ : syracuseStep 1583165 = 593687) (by norm_num)
theorem B1189981 : Blo 936583 1189981 := bbase (se 3 (by rfl) ⟨223121, by rfl⟩ : syracuseStep 1189981 = 446243) (by norm_num)
theorem B2107493 : Blo 936583 2107493 := bbase (se 4 (by rfl) ⟨197577, by rfl⟩ : syracuseStep 2107493 = 395155) (by norm_num)
theorem B1779869 : Blo 936583 1779869 := bbase (se 3 (by rfl) ⟨333725, by rfl⟩ : syracuseStep 1779869 = 667451) (by norm_num)
theorem B2107565 : Blo 936583 2107565 := bbase (se 3 (by rfl) ⟨395168, by rfl⟩ : syracuseStep 2107565 = 790337) (by norm_num)
theorem B1583293 : Blo 936583 1583293 := bbase (se 3 (by rfl) ⟨296867, by rfl⟩ : syracuseStep 1583293 = 593735) (by norm_num)
theorem B2140373 : Blo 936583 2140373 := bbase (se 7 (by rfl) ⟨25082, by rfl⟩ : syracuseStep 2140373 = 50165) (by norm_num)
theorem B2107637 : Blo 936583 2107637 := bbase (se 5 (by rfl) ⟨98795, by rfl⟩ : syracuseStep 2107637 = 197591) (by norm_num)
theorem B1190153 : Blo 936583 1190153 := bbase (se 2 (by rfl) ⟨446307, by rfl⟩ : syracuseStep 1190153 = 892615) (by norm_num)
theorem B1583381 : Blo 936583 1583381 := bbase (se 6 (by rfl) ⟨37110, by rfl⟩ : syracuseStep 1583381 = 74221) (by norm_num)
theorem B2107709 : Blo 936583 2107709 := bbase (se 3 (by rfl) ⟨395195, by rfl⟩ : syracuseStep 2107709 = 790391) (by norm_num)
theorem B1190209 : Blo 936583 1190209 := bbase (se 2 (by rfl) ⟨446328, by rfl⟩ : syracuseStep 1190209 = 892657) (by norm_num)
theorem B2107781 : Blo 936583 2107781 := bbase (se 4 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 2107781 = 395209) (by norm_num)
theorem B1583509 : Blo 936583 1583509 := bbase (se 6 (by rfl) ⟨37113, by rfl⟩ : syracuseStep 1583509 = 74227) (by norm_num)
theorem B1190305 : Blo 936583 1190305 := bbase (se 2 (by rfl) ⟨446364, by rfl⟩ : syracuseStep 1190305 = 892729) (by norm_num)
theorem B1780157 : Blo 936583 1780157 := bbase (se 3 (by rfl) ⟨333779, by rfl⟩ : syracuseStep 1780157 = 667559) (by norm_num)
theorem B2107853 : Blo 936583 2107853 := bbase (se 3 (by rfl) ⟨395222, by rfl⟩ : syracuseStep 2107853 = 790445) (by norm_num)
theorem B1157609 : Blo 936583 1157609 := bbase (se 2 (by rfl) ⟨434103, by rfl⟩ : syracuseStep 1157609 = 868207) (by norm_num)
theorem B1583597 : Blo 936583 1583597 := bbase (se 3 (by rfl) ⟨296924, by rfl⟩ : syracuseStep 1583597 = 593849) (by norm_num)
theorem B2107925 : Blo 936583 2107925 := bbase (se 6 (by rfl) ⟨49404, by rfl⟩ : syracuseStep 2107925 = 98809) (by norm_num)
theorem B1780309 : Blo 936583 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B2107997 : Blo 936583 2107997 := bbase (se 3 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 2107997 = 790499) (by norm_num)
theorem B1583725 : Blo 936583 1583725 := bbase (se 3 (by rfl) ⟨296948, by rfl⟩ : syracuseStep 1583725 = 593897) (by norm_num)
theorem B2108069 : Blo 936583 2108069 := bbase (se 4 (by rfl) ⟨197631, by rfl⟩ : syracuseStep 2108069 = 395263) (by norm_num)
theorem B1583813 : Blo 936583 1583813 := bbase (se 4 (by rfl) ⟨148482, by rfl⟩ : syracuseStep 1583813 = 296965) (by norm_num)
theorem B2108141 : Blo 936583 2108141 := bbase (se 3 (by rfl) ⟨395276, by rfl⟩ : syracuseStep 2108141 = 790553) (by norm_num)
theorem B2108213 : Blo 936583 2108213 := bbase (se 5 (by rfl) ⟨98822, by rfl⟩ : syracuseStep 2108213 = 197645) (by norm_num)
theorem B1583941 : Blo 936583 1583941 := bbase (se 4 (by rfl) ⟨148494, by rfl⟩ : syracuseStep 1583941 = 296989) (by norm_num)
theorem B1125209 : Blo 936583 1125209 := bbase (se 2 (by rfl) ⟨421953, by rfl⟩ : syracuseStep 1125209 = 843907) (by norm_num)
theorem B2108285 : Blo 936583 2108285 := bbase (se 3 (by rfl) ⟨395303, by rfl⟩ : syracuseStep 2108285 = 790607) (by norm_num)
theorem B1780613 : Blo 936583 1780613 := bbase (se 4 (by rfl) ⟨166932, by rfl⟩ : syracuseStep 1780613 = 333865) (by norm_num)
theorem B1125257 : Blo 936583 1125257 := bbase (se 2 (by rfl) ⟨421971, by rfl⟩ : syracuseStep 1125257 = 843943) (by norm_num)
theorem B1584029 : Blo 936583 1584029 := bbase (se 3 (by rfl) ⟨297005, by rfl⟩ : syracuseStep 1584029 = 594011) (by norm_num)
theorem B2108357 : Blo 936583 2108357 := bbase (se 4 (by rfl) ⟨197658, by rfl⟩ : syracuseStep 2108357 = 395317) (by norm_num)
theorem B1125353 : Blo 936583 1125353 := bbase (se 2 (by rfl) ⟨422007, by rfl⟩ : syracuseStep 1125353 = 844015) (by norm_num)
theorem B2108429 : Blo 936583 2108429 := bbase (se 3 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 2108429 = 790661) (by norm_num)
theorem B1584157 : Blo 936583 1584157 := bbase (se 3 (by rfl) ⟨297029, by rfl⟩ : syracuseStep 1584157 = 594059) (by norm_num)
theorem B2108501 : Blo 936583 2108501 := bbase (se 8 (by rfl) ⟨12354, by rfl⟩ : syracuseStep 2108501 = 24709) (by norm_num)
theorem B1584245 : Blo 936583 1584245 := bbase (se 5 (by rfl) ⟨74261, by rfl⟩ : syracuseStep 1584245 = 148523) (by norm_num)
theorem B1125517 : Blo 936583 1125517 := bbase (se 3 (by rfl) ⟨211034, by rfl⟩ : syracuseStep 1125517 = 422069) (by norm_num)
theorem B2108573 : Blo 936583 2108573 := bbase (se 3 (by rfl) ⟨395357, by rfl⟩ : syracuseStep 2108573 = 790715) (by norm_num)
theorem B2108645 : Blo 936583 2108645 := bbase (se 4 (by rfl) ⟨197685, by rfl⟩ : syracuseStep 2108645 = 395371) (by norm_num)
theorem B1584373 : Blo 936583 1584373 := bbase (se 5 (by rfl) ⟨74267, by rfl⟩ : syracuseStep 1584373 = 148535) (by norm_num)
theorem B2370829 : Blo 936583 2370829 := bbase (se 3 (by rfl) ⟨444530, by rfl⟩ : syracuseStep 2370829 = 889061) (by norm_num)
theorem B2108717 : Blo 936583 2108717 := bbase (se 3 (by rfl) ⟨395384, by rfl⟩ : syracuseStep 2108717 = 790769) (by norm_num)
theorem B1584461 : Blo 936583 1584461 := bbase (se 3 (by rfl) ⟨297086, by rfl⟩ : syracuseStep 1584461 = 594173) (by norm_num)
theorem B1125733 : Blo 936583 1125733 := bbase (se 4 (by rfl) ⟨105537, by rfl⟩ : syracuseStep 1125733 = 211075) (by norm_num)
theorem B2108789 : Blo 936583 2108789 := bbase (se 5 (by rfl) ⟨98849, by rfl⟩ : syracuseStep 2108789 = 197699) (by norm_num)
theorem B2370941 : Blo 936583 2370941 := bbase (se 3 (by rfl) ⟨444551, by rfl⟩ : syracuseStep 2370941 = 889103) (by norm_num)
theorem B2108861 : Blo 936583 2108861 := bbase (se 3 (by rfl) ⟨395411, by rfl⟩ : syracuseStep 2108861 = 790823) (by norm_num)
theorem B1584589 : Blo 936583 1584589 := bbase (se 3 (by rfl) ⟨297110, by rfl⟩ : syracuseStep 1584589 = 594221) (by norm_num)
theorem B4500949 : Blo 936583 4500949 := bbase (se 7 (by rfl) ⟨52745, by rfl⟩ : syracuseStep 4500949 = 105491) (by norm_num)
theorem B2108933 : Blo 936583 2108933 := bbase (se 4 (by rfl) ⟨197712, by rfl⟩ : syracuseStep 2108933 = 395425) (by norm_num)
theorem B1125901 : Blo 936583 1125901 := bbase (se 3 (by rfl) ⟨211106, by rfl⟩ : syracuseStep 1125901 = 422213) (by norm_num)
theorem B1584677 : Blo 936583 1584677 := bbase (se 4 (by rfl) ⟨148563, by rfl⟩ : syracuseStep 1584677 = 297127) (by norm_num)
theorem B2371133 : Blo 936583 2371133 := bbase (se 3 (by rfl) ⟨444587, by rfl⟩ : syracuseStep 2371133 = 889175) (by norm_num)
theorem B2109005 : Blo 936583 2109005 := bbase (se 3 (by rfl) ⟨395438, by rfl⟩ : syracuseStep 2109005 = 790877) (by norm_num)
theorem B1781365 : Blo 936583 1781365 := bbase (se 5 (by rfl) ⟨83501, by rfl⟩ : syracuseStep 1781365 = 167003) (by norm_num)
theorem B2109077 : Blo 936583 2109077 := bbase (se 6 (by rfl) ⟨49431, by rfl⟩ : syracuseStep 2109077 = 98863) (by norm_num)
theorem B1584805 : Blo 936583 1584805 := bbase (se 4 (by rfl) ⟨148575, by rfl⟩ : syracuseStep 1584805 = 297151) (by norm_num)
theorem B2109149 : Blo 936583 2109149 := bbase (se 3 (by rfl) ⟨395465, by rfl⟩ : syracuseStep 2109149 = 790931) (by norm_num)
theorem B1584893 : Blo 936583 1584893 := bbase (se 3 (by rfl) ⟨297167, by rfl⟩ : syracuseStep 1584893 = 594335) (by norm_num)
theorem B1781509 : Blo 936583 1781509 := bbase (se 4 (by rfl) ⟨167016, by rfl⟩ : syracuseStep 1781509 = 334033) (by norm_num)
theorem B2109221 : Blo 936583 2109221 := bbase (se 4 (by rfl) ⟨197739, by rfl⟩ : syracuseStep 2109221 = 395479) (by norm_num)
theorem B6762325 : Blo 936583 6762325 := bbase (se 9 (by rfl) ⟨19811, by rfl⟩ : syracuseStep 6762325 = 39623) (by norm_num)
theorem B2109293 : Blo 936583 2109293 := bbase (se 3 (by rfl) ⟨395492, by rfl⟩ : syracuseStep 2109293 = 790985) (by norm_num)
theorem B1585021 : Blo 936583 1585021 := bbase (se 3 (by rfl) ⟨297191, by rfl⟩ : syracuseStep 1585021 = 594383) (by norm_num)
theorem B2371477 : Blo 936583 2371477 := bbase (se 6 (by rfl) ⟨55581, by rfl⟩ : syracuseStep 2371477 = 111163) (by norm_num)
theorem B1781669 : Blo 936583 1781669 := bbase (se 4 (by rfl) ⟨167031, by rfl⟩ : syracuseStep 1781669 = 334063) (by norm_num)
theorem B2109365 : Blo 936583 2109365 := bbase (se 5 (by rfl) ⟨98876, by rfl⟩ : syracuseStep 2109365 = 197753) (by norm_num)
theorem B1585109 : Blo 936583 1585109 := bbase (se 7 (by rfl) ⟨18575, by rfl⟩ : syracuseStep 1585109 = 37151) (by norm_num)
theorem B2109437 : Blo 936583 2109437 := bbase (se 3 (by rfl) ⟨395519, by rfl⟩ : syracuseStep 2109437 = 791039) (by norm_num)
theorem B2371589 : Blo 936583 2371589 := bbase (se 4 (by rfl) ⟨222336, by rfl⟩ : syracuseStep 2371589 = 444673) (by norm_num)
theorem B1126429 : Blo 936583 1126429 := bbase (se 3 (by rfl) ⟨211205, by rfl⟩ : syracuseStep 1126429 = 422411) (by norm_num)
theorem B1781813 : Blo 936583 1781813 := bbase (se 5 (by rfl) ⟨83522, by rfl⟩ : syracuseStep 1781813 = 167045) (by norm_num)
theorem B2109509 : Blo 936583 2109509 := bbase (se 4 (by rfl) ⟨197766, by rfl⟩ : syracuseStep 2109509 = 395533) (by norm_num)
theorem B1585237 : Blo 936583 1585237 := bbase (se 8 (by rfl) ⟨9288, by rfl⟩ : syracuseStep 1585237 = 18577) (by norm_num)
theorem B2109581 : Blo 936583 2109581 := bbase (se 3 (by rfl) ⟨395546, by rfl⟩ : syracuseStep 2109581 = 791093) (by norm_num)
theorem B1585325 : Blo 936583 1585325 := bbase (se 3 (by rfl) ⟨297248, by rfl⟩ : syracuseStep 1585325 = 594497) (by norm_num)
theorem B2371781 : Blo 936583 2371781 := bbase (se 4 (by rfl) ⟨222354, by rfl⟩ : syracuseStep 2371781 = 444709) (by norm_num)
theorem B2109653 : Blo 936583 2109653 := bbase (se 7 (by rfl) ⟨24722, by rfl⟩ : syracuseStep 2109653 = 49445) (by norm_num)
theorem B5353685 : Blo 936583 5353685 := bbase (se 7 (by rfl) ⟨62738, by rfl⟩ : syracuseStep 5353685 = 125477) (by norm_num)
theorem B2109725 : Blo 936583 2109725 := bbase (se 3 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 2109725 = 791147) (by norm_num)
theorem B1585453 : Blo 936583 1585453 := bbase (se 3 (by rfl) ⟨297272, by rfl⟩ : syracuseStep 1585453 = 594545) (by norm_num)
theorem B1782101 : Blo 936583 1782101 := bbase (se 10 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 1782101 = 5221) (by norm_num)
theorem B2109797 : Blo 936583 2109797 := bbase (se 4 (by rfl) ⟨197793, by rfl⟩ : syracuseStep 2109797 = 395587) (by norm_num)
theorem B1585541 : Blo 936583 1585541 := bbase (se 4 (by rfl) ⟨148644, by rfl⟩ : syracuseStep 1585541 = 297289) (by norm_num)
theorem B2109869 : Blo 936583 2109869 := bbase (se 3 (by rfl) ⟨395600, by rfl⟩ : syracuseStep 2109869 = 791201) (by norm_num)
theorem B1782253 : Blo 936583 1782253 := bbase (se 3 (by rfl) ⟨334172, by rfl⟩ : syracuseStep 1782253 = 668345) (by norm_num)
theorem B2109941 : Blo 936583 2109941 := bbase (se 5 (by rfl) ⟨98903, by rfl⟩ : syracuseStep 2109941 = 197807) (by norm_num)
theorem B1585669 : Blo 936583 1585669 := bbase (se 4 (by rfl) ⟨148656, by rfl⟩ : syracuseStep 1585669 = 297313) (by norm_num)
theorem B2372125 : Blo 936583 2372125 := bbase (se 3 (by rfl) ⟨444773, by rfl⟩ : syracuseStep 2372125 = 889547) (by norm_num)
theorem B2110013 : Blo 936583 2110013 := bbase (se 3 (by rfl) ⟨395627, by rfl⟩ : syracuseStep 2110013 = 791255) (by norm_num)
theorem B1585757 : Blo 936583 1585757 := bbase (se 3 (by rfl) ⟨297329, by rfl⟩ : syracuseStep 1585757 = 594659) (by norm_num)
theorem B2110085 : Blo 936583 2110085 := bbase (se 4 (by rfl) ⟨197820, by rfl⟩ : syracuseStep 2110085 = 395641) (by norm_num)
theorem B2372237 : Blo 936583 2372237 := bbase (se 3 (by rfl) ⟨444794, by rfl⟩ : syracuseStep 2372237 = 889589) (by norm_num)
theorem B2110157 : Blo 936583 2110157 := bbase (se 3 (by rfl) ⟨395654, by rfl⟩ : syracuseStep 2110157 = 791309) (by norm_num)
theorem B1585885 : Blo 936583 1585885 := bbase (se 3 (by rfl) ⟨297353, by rfl⟩ : syracuseStep 1585885 = 594707) (by norm_num)
theorem B2110229 : Blo 936583 2110229 := bbase (se 6 (by rfl) ⟨49458, by rfl⟩ : syracuseStep 2110229 = 98917) (by norm_num)
theorem B1782557 : Blo 936583 1782557 := bbase (se 3 (by rfl) ⟨334229, by rfl⟩ : syracuseStep 1782557 = 668459) (by norm_num)
theorem B1585973 : Blo 936583 1585973 := bbase (se 5 (by rfl) ⟨74342, by rfl⟩ : syracuseStep 1585973 = 148685) (by norm_num)
theorem B2372429 : Blo 936583 2372429 := bbase (se 3 (by rfl) ⟨444830, by rfl⟩ : syracuseStep 2372429 = 889661) (by norm_num)
theorem B2110301 : Blo 936583 2110301 := bbase (se 3 (by rfl) ⟨395681, by rfl⟩ : syracuseStep 2110301 = 791363) (by norm_num)
theorem B2110373 : Blo 936583 2110373 := bbase (se 4 (by rfl) ⟨197847, by rfl⟩ : syracuseStep 2110373 = 395695) (by norm_num)
theorem B1586101 : Blo 936583 1586101 := bbase (se 5 (by rfl) ⟨74348, by rfl⟩ : syracuseStep 1586101 = 148697) (by norm_num)
theorem B2110445 : Blo 936583 2110445 := bbase (se 3 (by rfl) ⟨395708, by rfl⟩ : syracuseStep 2110445 = 791417) (by norm_num)
theorem B1586189 : Blo 936583 1586189 := bbase (se 3 (by rfl) ⟨297410, by rfl⟩ : syracuseStep 1586189 = 594821) (by norm_num)
theorem B2110517 : Blo 936583 2110517 := bbase (se 5 (by rfl) ⟨98930, by rfl⟩ : syracuseStep 2110517 = 197861) (by norm_num)
theorem B1127525 : Blo 936583 1127525 := bbase (se 4 (by rfl) ⟨105705, by rfl⟩ : syracuseStep 1127525 = 211411) (by norm_num)
theorem B2110589 : Blo 936583 2110589 := bbase (se 3 (by rfl) ⟨395735, by rfl⟩ : syracuseStep 2110589 = 791471) (by norm_num)
theorem B1586317 : Blo 936583 1586317 := bbase (se 3 (by rfl) ⟨297434, by rfl⟩ : syracuseStep 1586317 = 594869) (by norm_num)
theorem B2372773 : Blo 936583 2372773 := bbase (se 4 (by rfl) ⟨222447, by rfl⟩ : syracuseStep 2372773 = 444895) (by norm_num)
theorem B2110661 : Blo 936583 2110661 := bbase (se 4 (by rfl) ⟨197874, by rfl⟩ : syracuseStep 2110661 = 395749) (by norm_num)
theorem B1586405 : Blo 936583 1586405 := bbase (se 4 (by rfl) ⟨148725, by rfl⟩ : syracuseStep 1586405 = 297451) (by norm_num)
theorem B2110733 : Blo 936583 2110733 := bbase (se 3 (by rfl) ⟨395762, by rfl⟩ : syracuseStep 2110733 = 791525) (by norm_num)
theorem B2372885 : Blo 936583 2372885 := bbase (se 6 (by rfl) ⟨55614, by rfl⟩ : syracuseStep 2372885 = 111229) (by norm_num)
theorem B2110805 : Blo 936583 2110805 := bbase (se 13 (by rfl) ⟨386, by rfl⟩ : syracuseStep 2110805 = 773) (by norm_num)
theorem B1586533 : Blo 936583 1586533 := bbase (se 4 (by rfl) ⟨148737, by rfl⟩ : syracuseStep 1586533 = 297475) (by norm_num)
theorem B5354869 : Blo 936583 5354869 := bbase (se 5 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 5354869 = 502019) (by norm_num)
theorem B2110877 : Blo 936583 2110877 := bbase (se 3 (by rfl) ⟨395789, by rfl⟩ : syracuseStep 2110877 = 791579) (by norm_num)
theorem B964013 : Blo 936583 964013 := bbase (se 3 (by rfl) ⟨180752, by rfl⟩ : syracuseStep 964013 = 361505) (by norm_num)
theorem B1586621 : Blo 936583 1586621 := bbase (se 3 (by rfl) ⟨297491, by rfl⟩ : syracuseStep 1586621 = 594983) (by norm_num)
theorem B2373077 : Blo 936583 2373077 := bbase (se 7 (by rfl) ⟨27809, by rfl⟩ : syracuseStep 2373077 = 55619) (by norm_num)
theorem B2110949 : Blo 936583 2110949 := bbase (se 4 (by rfl) ⟨197901, by rfl⟩ : syracuseStep 2110949 = 395803) (by norm_num)
theorem B1783309 : Blo 936583 1783309 := bbase (se 3 (by rfl) ⟨334370, by rfl⟩ : syracuseStep 1783309 = 668741) (by norm_num)
theorem B2111021 : Blo 936583 2111021 := bbase (se 3 (by rfl) ⟨395816, by rfl⟩ : syracuseStep 2111021 = 791633) (by norm_num)
theorem B1586749 : Blo 936583 1586749 := bbase (se 3 (by rfl) ⟨297515, by rfl⟩ : syracuseStep 1586749 = 595031) (by norm_num)
theorem B2111093 : Blo 936583 2111093 := bbase (se 5 (by rfl) ⟨98957, by rfl⟩ : syracuseStep 2111093 = 197915) (by norm_num)
theorem B1586837 : Blo 936583 1586837 := bbase (se 6 (by rfl) ⟨37191, by rfl⟩ : syracuseStep 1586837 = 74383) (by norm_num)
theorem B1783453 : Blo 936583 1783453 := bbase (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) (by norm_num)
theorem B2111165 : Blo 936583 2111165 := bbase (se 3 (by rfl) ⟨395843, by rfl⟩ : syracuseStep 2111165 = 791687) (by norm_num)
theorem B2668277 : Blo 936583 2668277 := bbase (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) (by norm_num)
theorem B2111237 : Blo 936583 2111237 := bbase (se 4 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 2111237 = 395857) (by norm_num)
theorem B1586965 : Blo 936583 1586965 := bbase (se 6 (by rfl) ⟨37194, by rfl⟩ : syracuseStep 1586965 = 74389) (by norm_num)
theorem B1128217 : Blo 936583 1128217 := bbase (se 2 (by rfl) ⟨423081, by rfl⟩ : syracuseStep 1128217 = 846163) (by norm_num)
theorem B2373421 : Blo 936583 2373421 := bbase (se 3 (by rfl) ⟨445016, by rfl⟩ : syracuseStep 2373421 = 890033) (by norm_num)
theorem B1783613 : Blo 936583 1783613 := bbase (se 3 (by rfl) ⟨334427, by rfl⟩ : syracuseStep 1783613 = 668855) (by norm_num)
theorem B2111309 : Blo 936583 2111309 := bbase (se 3 (by rfl) ⟨395870, by rfl⟩ : syracuseStep 2111309 = 791741) (by norm_num)
theorem B1587053 : Blo 936583 1587053 := bbase (se 3 (by rfl) ⟨297572, by rfl⟩ : syracuseStep 1587053 = 595145) (by norm_num)
theorem B1128313 : Blo 936583 1128313 := bbase (se 2 (by rfl) ⟨423117, by rfl⟩ : syracuseStep 1128313 = 846235) (by norm_num)
theorem B2111381 : Blo 936583 2111381 := bbase (se 6 (by rfl) ⟨49485, by rfl⟩ : syracuseStep 2111381 = 98971) (by norm_num)
theorem B2537365 : Blo 936583 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B2373533 : Blo 936583 2373533 := bbase (se 3 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 2373533 = 890075) (by norm_num)
theorem B1783757 : Blo 936583 1783757 := bbase (se 3 (by rfl) ⟨334454, by rfl⟩ : syracuseStep 1783757 = 668909) (by norm_num)
theorem B2111453 : Blo 936583 2111453 := bbase (se 3 (by rfl) ⟨395897, by rfl⟩ : syracuseStep 2111453 = 791795) (by norm_num)
theorem B1587181 : Blo 936583 1587181 := bbase (se 3 (by rfl) ⟨297596, by rfl⟩ : syracuseStep 1587181 = 595193) (by norm_num)
theorem B4012037 : Blo 936583 4012037 := bbase (se 4 (by rfl) ⟨376128, by rfl⟩ : syracuseStep 4012037 = 752257) (by norm_num)
theorem B2111525 : Blo 936583 2111525 := bbase (se 4 (by rfl) ⟨197955, by rfl⟩ : syracuseStep 2111525 = 395911) (by norm_num)
theorem B2373725 : Blo 936583 2373725 := bbase (se 3 (by rfl) ⟨445073, by rfl⟩ : syracuseStep 2373725 = 890147) (by norm_num)
theorem B2111597 : Blo 936583 2111597 := bbase (se 3 (by rfl) ⟨395924, by rfl⟩ : syracuseStep 2111597 = 791849) (by norm_num)
theorem B4503701 : Blo 936583 4503701 := bbase (se 6 (by rfl) ⟨105555, by rfl⟩ : syracuseStep 4503701 = 211111) (by norm_num)
theorem B2144405 : Blo 936583 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B2111669 : Blo 936583 2111669 := bbase (se 5 (by rfl) ⟨98984, by rfl⟩ : syracuseStep 2111669 = 197969) (by norm_num)
theorem B1784045 : Blo 936583 1784045 := bbase (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) (by norm_num)
theorem B1128697 : Blo 936583 1128697 := bbase (se 2 (by rfl) ⟨423261, by rfl⟩ : syracuseStep 1128697 = 846523) (by norm_num)
theorem B2111741 : Blo 936583 2111741 := bbase (se 3 (by rfl) ⟨395951, by rfl⟩ : syracuseStep 2111741 = 791903) (by norm_num)
theorem B4012325 : Blo 936583 4012325 := bbase (se 4 (by rfl) ⟨376155, by rfl⟩ : syracuseStep 4012325 = 752311) (by norm_num)
theorem B2111813 : Blo 936583 2111813 := bbase (se 4 (by rfl) ⟨197982, by rfl⟩ : syracuseStep 2111813 = 395965) (by norm_num)
theorem B1784197 : Blo 936583 1784197 := bbase (se 4 (by rfl) ⟨167268, by rfl⟩ : syracuseStep 1784197 = 334537) (by norm_num)
theorem B2111885 : Blo 936583 2111885 := bbase (se 3 (by rfl) ⟨395978, by rfl⟩ : syracuseStep 2111885 = 791957) (by norm_num)
theorem B2374069 : Blo 936583 2374069 := bbase (se 5 (by rfl) ⟨111284, by rfl⟩ : syracuseStep 2374069 = 222569) (by norm_num)
theorem B2111957 : Blo 936583 2111957 := bbase (se 7 (by rfl) ⟨24749, by rfl⟩ : syracuseStep 2111957 = 49499) (by norm_num)
theorem B2112029 : Blo 936583 2112029 := bbase (se 3 (by rfl) ⟨396005, by rfl⟩ : syracuseStep 2112029 = 792011) (by norm_num)
theorem B2374181 : Blo 936583 2374181 := bbase (se 4 (by rfl) ⟨222579, by rfl⟩ : syracuseStep 2374181 = 445159) (by norm_num)
theorem B965201 : Blo 936583 965201 := bbase (se 2 (by rfl) ⟨361950, by rfl⟩ : syracuseStep 965201 = 723901) (by norm_num)
theorem B2112101 : Blo 936583 2112101 := bbase (se 4 (by rfl) ⟨198009, by rfl⟩ : syracuseStep 2112101 = 396019) (by norm_num)
theorem B2112173 : Blo 936583 2112173 := bbase (se 3 (by rfl) ⟨396032, by rfl⟩ : syracuseStep 2112173 = 792065) (by norm_num)
theorem B1784501 : Blo 936583 1784501 := bbase (se 5 (by rfl) ⟨83648, by rfl⟩ : syracuseStep 1784501 = 167297) (by norm_num)
theorem B2374373 : Blo 936583 2374373 := bbase (se 4 (by rfl) ⟨222597, by rfl⟩ : syracuseStep 2374373 = 445195) (by norm_num)
theorem B2112245 : Blo 936583 2112245 := bbase (se 5 (by rfl) ⟨99011, by rfl⟩ : syracuseStep 2112245 = 198023) (by norm_num)
theorem B5716757 : Blo 936583 5716757 := bbase (se 6 (by rfl) ⟨133986, by rfl⟩ : syracuseStep 5716757 = 267973) (by norm_num)
theorem B2112317 : Blo 936583 2112317 := bbase (se 3 (by rfl) ⟨396059, by rfl⟩ : syracuseStep 2112317 = 792119) (by norm_num)
theorem B4275013 : Blo 936583 4275013 := bbase (se 4 (by rfl) ⟨400782, by rfl⟩ : syracuseStep 4275013 = 801565) (by norm_num)
theorem B2112389 : Blo 936583 2112389 := bbase (se 4 (by rfl) ⟨198036, by rfl⟩ : syracuseStep 2112389 = 396073) (by norm_num)
theorem B1424269 : Blo 936583 1424269 := bbase (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) (by norm_num)
theorem B3160997 : Blo 936583 3160997 := bbase (se 4 (by rfl) ⟨296343, by rfl⟩ : syracuseStep 3160997 = 592687) (by norm_num)
theorem B2112461 : Blo 936583 2112461 := bbase (se 3 (by rfl) ⟨396086, by rfl⟩ : syracuseStep 2112461 = 792173) (by norm_num)
theorem B2112533 : Blo 936583 2112533 := bbase (se 6 (by rfl) ⟨49512, by rfl⟩ : syracuseStep 2112533 = 99025) (by norm_num)
theorem B4013077 : Blo 936583 4013077 := bbase (se 6 (by rfl) ⟨94056, by rfl⟩ : syracuseStep 4013077 = 188113) (by norm_num)
theorem B2374717 : Blo 936583 2374717 := bbase (se 3 (by rfl) ⟨445259, by rfl⟩ : syracuseStep 2374717 = 890519) (by norm_num)
theorem B2112605 : Blo 936583 2112605 := bbase (se 3 (by rfl) ⟨396113, by rfl⟩ : syracuseStep 2112605 = 792227) (by norm_num)
theorem B2112677 : Blo 936583 2112677 := bbase (se 4 (by rfl) ⟨198063, by rfl⟩ : syracuseStep 2112677 = 396127) (by norm_num)
theorem B2374829 : Blo 936583 2374829 := bbase (se 3 (by rfl) ⟨445280, by rfl⟩ : syracuseStep 2374829 = 890561) (by norm_num)
theorem B2112749 : Blo 936583 2112749 := bbase (se 3 (by rfl) ⟨396140, by rfl⟩ : syracuseStep 2112749 = 792281) (by norm_num)
theorem B1129745 : Blo 936583 1129745 := bbase (se 2 (by rfl) ⟨423654, by rfl⟩ : syracuseStep 1129745 = 847309) (by norm_num)
theorem B2669861 : Blo 936583 2669861 := bbase (se 4 (by rfl) ⟨250299, by rfl⟩ : syracuseStep 2669861 = 500599) (by norm_num)
theorem B2112821 : Blo 936583 2112821 := bbase (se 5 (by rfl) ⟨99038, by rfl⟩ : syracuseStep 2112821 = 198077) (by norm_num)
theorem B5356853 : Blo 936583 5356853 := bbase (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) (by norm_num)
theorem B3161429 : Blo 936583 3161429 := bbase (se 11 (by rfl) ⟨2315, by rfl⟩ : syracuseStep 3161429 = 4631) (by norm_num)
theorem B2375021 : Blo 936583 2375021 := bbase (se 3 (by rfl) ⟨445316, by rfl⟩ : syracuseStep 2375021 = 890633) (by norm_num)
theorem B2112893 : Blo 936583 2112893 := bbase (se 3 (by rfl) ⟨396167, by rfl⟩ : syracuseStep 2112893 = 792335) (by norm_num)
theorem B1785253 : Blo 936583 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B2112965 : Blo 936583 2112965 := bbase (se 4 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 2112965 = 396181) (by norm_num)
theorem B2113037 : Blo 936583 2113037 := bbase (se 3 (by rfl) ⟨396194, by rfl⟩ : syracuseStep 2113037 = 792389) (by norm_num)
theorem B1785397 : Blo 936583 1785397 := bbase (se 5 (by rfl) ⟨83690, by rfl⟩ : syracuseStep 1785397 = 167381) (by norm_num)
theorem B2113109 : Blo 936583 2113109 := bbase (se 8 (by rfl) ⟨12381, by rfl⟩ : syracuseStep 2113109 = 24763) (by norm_num)
theorem B2113181 : Blo 936583 2113181 := bbase (se 3 (by rfl) ⟨396221, by rfl⟩ : syracuseStep 2113181 = 792443) (by norm_num)
theorem B2375365 : Blo 936583 2375365 := bbase (se 4 (by rfl) ⟨222690, by rfl⟩ : syracuseStep 2375365 = 445381) (by norm_num)
theorem B1785557 : Blo 936583 1785557 := bbase (se 7 (by rfl) ⟨20924, by rfl⟩ : syracuseStep 1785557 = 41849) (by norm_num)
theorem B2113253 : Blo 936583 2113253 := bbase (se 4 (by rfl) ⟨198117, by rfl⟩ : syracuseStep 2113253 = 396235) (by norm_num)
theorem B4013813 : Blo 936583 4013813 := bbase (se 5 (by rfl) ⟨188147, by rfl⟩ : syracuseStep 4013813 = 376295) (by norm_num)
theorem B3161861 : Blo 936583 3161861 := bbase (se 4 (by rfl) ⟨296424, by rfl⟩ : syracuseStep 3161861 = 592849) (by norm_num)
theorem B2113325 : Blo 936583 2113325 := bbase (se 3 (by rfl) ⟨396248, by rfl⟩ : syracuseStep 2113325 = 792497) (by norm_num)
theorem B4570933 : Blo 936583 4570933 := bbase (se 5 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 4570933 = 428525) (by norm_num)
theorem B2375477 : Blo 936583 2375477 := bbase (se 5 (by rfl) ⟨111350, by rfl⟩ : syracuseStep 2375477 = 222701) (by norm_num)
theorem B2408309 : Blo 936583 2408309 := bbase (se 5 (by rfl) ⟨112889, by rfl⟩ : syracuseStep 2408309 = 225779) (by norm_num)
theorem B2113397 : Blo 936583 2113397 := bbase (se 5 (by rfl) ⟨99065, by rfl⟩ : syracuseStep 2113397 = 198131) (by norm_num)
theorem B2408381 : Blo 936583 2408381 := bbase (se 3 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 2408381 = 903143) (by norm_num)
theorem B2113469 : Blo 936583 2113469 := bbase (se 3 (by rfl) ⟨396275, by rfl⟩ : syracuseStep 2113469 = 792551) (by norm_num)
theorem B2670533 : Blo 936583 2670533 := bbase (se 4 (by rfl) ⟨250362, by rfl⟩ : syracuseStep 2670533 = 500725) (by norm_num)
theorem B2375669 : Blo 936583 2375669 := bbase (se 5 (by rfl) ⟨111359, by rfl⟩ : syracuseStep 2375669 = 222719) (by norm_num)
theorem B2113541 : Blo 936583 2113541 := bbase (se 4 (by rfl) ⟨198144, by rfl⟩ : syracuseStep 2113541 = 396289) (by norm_num)
theorem B2113613 : Blo 936583 2113613 := bbase (se 3 (by rfl) ⟨396302, by rfl⟩ : syracuseStep 2113613 = 792605) (by norm_num)
theorem B7127189 : Blo 936583 7127189 := bbase (se 6 (by rfl) ⟨167043, by rfl⟩ : syracuseStep 7127189 = 334087) (by norm_num)
theorem B2113685 : Blo 936583 2113685 := bbase (se 6 (by rfl) ⟨49539, by rfl⟩ : syracuseStep 2113685 = 99079) (by norm_num)
theorem B3162293 : Blo 936583 3162293 := bbase (se 5 (by rfl) ⟨148232, by rfl⟩ : syracuseStep 3162293 = 296465) (by norm_num)
theorem B2113757 : Blo 936583 2113757 := bbase (se 3 (by rfl) ⟨396329, by rfl⟩ : syracuseStep 2113757 = 792659) (by norm_num)
theorem B2113829 : Blo 936583 2113829 := bbase (se 4 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 2113829 = 396343) (by norm_num)
theorem B2376013 : Blo 936583 2376013 := bbase (se 3 (by rfl) ⟨445502, by rfl⟩ : syracuseStep 2376013 = 891005) (by norm_num)
theorem B2113901 : Blo 936583 2113901 := bbase (se 3 (by rfl) ⟨396356, by rfl⟩ : syracuseStep 2113901 = 792713) (by norm_num)
theorem B2670965 : Blo 936583 2670965 := bbase (se 5 (by rfl) ⟨125201, by rfl⟩ : syracuseStep 2670965 = 250403) (by norm_num)
theorem B2113973 : Blo 936583 2113973 := bbase (se 5 (by rfl) ⟨99092, by rfl⟩ : syracuseStep 2113973 = 198185) (by norm_num)
theorem B2376125 : Blo 936583 2376125 := bbase (se 3 (by rfl) ⟨445523, by rfl⟩ : syracuseStep 2376125 = 891047) (by norm_num)
theorem B4506101 : Blo 936583 4506101 := bbase (se 5 (by rfl) ⟨211223, by rfl⟩ : syracuseStep 4506101 = 422447) (by norm_num)
theorem B2114045 : Blo 936583 2114045 := bbase (se 3 (by rfl) ⟨396383, by rfl⟩ : syracuseStep 2114045 = 792767) (by norm_num)
theorem B12829205 : Blo 936583 12829205 := bbase (se 6 (by rfl) ⟨300684, by rfl⟩ : syracuseStep 12829205 = 601369) (by norm_num)
theorem B2114117 : Blo 936583 2114117 := bbase (se 4 (by rfl) ⟨198198, by rfl⟩ : syracuseStep 2114117 = 396397) (by norm_num)
theorem B3162725 : Blo 936583 3162725 := bbase (se 4 (by rfl) ⟨296505, by rfl⟩ : syracuseStep 3162725 = 593011) (by norm_num)
theorem B2376317 : Blo 936583 2376317 := bbase (se 3 (by rfl) ⟨445559, by rfl⟩ : syracuseStep 2376317 = 891119) (by norm_num)
theorem B2114189 : Blo 936583 2114189 := bbase (se 3 (by rfl) ⟨396410, by rfl⟩ : syracuseStep 2114189 = 792821) (by norm_num)
theorem B2540197 : Blo 936583 2540197 := bbase (se 4 (by rfl) ⟨238143, by rfl⟩ : syracuseStep 2540197 = 476287) (by norm_num)
theorem B2114261 : Blo 936583 2114261 := bbase (se 7 (by rfl) ⟨24776, by rfl⟩ : syracuseStep 2114261 = 49553) (by norm_num)
theorem B2114333 : Blo 936583 2114333 := bbase (se 3 (by rfl) ⟨396437, by rfl⟩ : syracuseStep 2114333 = 792875) (by norm_num)
theorem B6275893 : Blo 936583 6275893 := bbase (se 5 (by rfl) ⟨294182, by rfl⟩ : syracuseStep 6275893 = 588365) (by norm_num)
theorem B2409293 : Blo 936583 2409293 := bbase (se 3 (by rfl) ⟨451742, by rfl⟩ : syracuseStep 2409293 = 903485) (by norm_num)
theorem B2114405 : Blo 936583 2114405 := bbase (se 4 (by rfl) ⟨198225, by rfl⟩ : syracuseStep 2114405 = 396451) (by norm_num)
theorem B2114477 : Blo 936583 2114477 := bbase (se 3 (by rfl) ⟨396464, by rfl⟩ : syracuseStep 2114477 = 792929) (by norm_num)
theorem B2376661 : Blo 936583 2376661 := bbase (se 7 (by rfl) ⟨27851, by rfl⟩ : syracuseStep 2376661 = 55703) (by norm_num)
theorem B2114549 : Blo 936583 2114549 := bbase (se 5 (by rfl) ⟨99119, by rfl⟩ : syracuseStep 2114549 = 198239) (by norm_num)
theorem B3163157 : Blo 936583 3163157 := bbase (se 6 (by rfl) ⟨74136, by rfl⟩ : syracuseStep 3163157 = 148273) (by norm_num)
theorem B2114621 : Blo 936583 2114621 := bbase (se 3 (by rfl) ⟨396491, by rfl⟩ : syracuseStep 2114621 = 792983) (by norm_num)
theorem B2376773 : Blo 936583 2376773 := bbase (se 4 (by rfl) ⟨222822, by rfl⟩ : syracuseStep 2376773 = 445645) (by norm_num)
theorem B1000549 : Blo 936583 1000549 := bbase (se 4 (by rfl) ⟨93801, by rfl⟩ : syracuseStep 1000549 = 187603) (by norm_num)
theorem B2671717 : Blo 936583 2671717 := bbase (se 4 (by rfl) ⟨250473, by rfl⟩ : syracuseStep 2671717 = 500947) (by norm_num)
theorem B2114693 : Blo 936583 2114693 := bbase (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) (by norm_num)
theorem B1000621 : Blo 936583 1000621 := bbase (se 3 (by rfl) ⟨187616, by rfl⟩ : syracuseStep 1000621 = 375233) (by norm_num)
theorem B2114765 : Blo 936583 2114765 := bbase (se 3 (by rfl) ⟨396518, by rfl⟩ : syracuseStep 2114765 = 793037) (by norm_num)
theorem B2376965 : Blo 936583 2376965 := bbase (se 4 (by rfl) ⟨222840, by rfl⟩ : syracuseStep 2376965 = 445681) (by norm_num)
theorem B2114837 : Blo 936583 2114837 := bbase (se 6 (by rfl) ⟨49566, by rfl⟩ : syracuseStep 2114837 = 99133) (by norm_num)
theorem B2114909 : Blo 936583 2114909 := bbase (se 3 (by rfl) ⟨396545, by rfl⟩ : syracuseStep 2114909 = 793091) (by norm_num)
theorem B2114981 : Blo 936583 2114981 := bbase (se 4 (by rfl) ⟨198279, by rfl⟩ : syracuseStep 2114981 = 396559) (by norm_num)
theorem B3163589 : Blo 936583 3163589 := bbase (se 4 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 3163589 = 593173) (by norm_num)
theorem B2115053 : Blo 936583 2115053 := bbase (se 3 (by rfl) ⟨396572, by rfl⟩ : syracuseStep 2115053 = 793145) (by norm_num)
theorem B1000993 : Blo 936583 1000993 := bbase (se 2 (by rfl) ⟨375372, by rfl⟩ : syracuseStep 1000993 = 750745) (by norm_num)
theorem B2115125 : Blo 936583 2115125 := bbase (se 5 (by rfl) ⟨99146, by rfl⟩ : syracuseStep 2115125 = 198293) (by norm_num)
theorem B2377309 : Blo 936583 2377309 := bbase (se 3 (by rfl) ⟨445745, by rfl⟩ : syracuseStep 2377309 = 891491) (by norm_num)
theorem B2115197 : Blo 936583 2115197 := bbase (se 3 (by rfl) ⟨396599, by rfl⟩ : syracuseStep 2115197 = 793199) (by norm_num)
theorem B6014645 : Blo 936583 6014645 := bbase (se 5 (by rfl) ⟨281936, by rfl⟩ : syracuseStep 6014645 = 563873) (by norm_num)
theorem B2115269 : Blo 936583 2115269 := bbase (se 4 (by rfl) ⟨198306, by rfl⟩ : syracuseStep 2115269 = 396613) (by norm_num)
theorem B2377421 : Blo 936583 2377421 := bbase (se 3 (by rfl) ⟨445766, by rfl⟩ : syracuseStep 2377421 = 891533) (by norm_num)
theorem B14436053 : Blo 936583 14436053 := bbase (se 7 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 14436053 = 338345) (by norm_num)
theorem B2115341 : Blo 936583 2115341 := bbase (se 3 (by rfl) ⟨396626, by rfl⟩ : syracuseStep 2115341 = 793253) (by norm_num)
theorem B3557141 : Blo 936583 3557141 := bbase (se 6 (by rfl) ⟨83370, by rfl⟩ : syracuseStep 3557141 = 166741) (by norm_num)
theorem B2705237 : Blo 936583 2705237 := bbase (se 9 (by rfl) ⟨7925, by rfl⟩ : syracuseStep 2705237 = 15851) (by norm_num)
theorem B2115413 : Blo 936583 2115413 := bbase (se 9 (by rfl) ⟨6197, by rfl⟩ : syracuseStep 2115413 = 12395) (by norm_num)
theorem B3164021 : Blo 936583 3164021 := bbase (se 5 (by rfl) ⟨148313, by rfl⟩ : syracuseStep 3164021 = 296627) (by norm_num)
theorem B2377613 : Blo 936583 2377613 := bbase (se 3 (by rfl) ⟨445802, by rfl⟩ : syracuseStep 2377613 = 891605) (by norm_num)
theorem B1001369 : Blo 936583 1001369 := bbase (se 2 (by rfl) ⟨375513, by rfl⟩ : syracuseStep 1001369 = 751027) (by norm_num)
theorem B2115485 : Blo 936583 2115485 := bbase (se 3 (by rfl) ⟨396653, by rfl⟩ : syracuseStep 2115485 = 793307) (by norm_num)
theorem B1001441 : Blo 936583 1001441 := bbase (se 2 (by rfl) ⟨375540, by rfl⟩ : syracuseStep 1001441 = 751081) (by norm_num)
theorem B2115557 : Blo 936583 2115557 := bbase (se 4 (by rfl) ⟨198333, by rfl⟩ : syracuseStep 2115557 = 396667) (by norm_num)
theorem B2115629 : Blo 936583 2115629 := bbase (se 3 (by rfl) ⟨396680, by rfl⟩ : syracuseStep 2115629 = 793361) (by norm_num)
theorem B3557429 : Blo 936583 3557429 := bbase (se 5 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 3557429 = 333509) (by norm_num)
theorem B12863573 : Blo 936583 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B2115701 : Blo 936583 2115701 := bbase (se 5 (by rfl) ⟨99173, by rfl⟩ : syracuseStep 2115701 = 198347) (by norm_num)
theorem B1001629 : Blo 936583 1001629 := bbase (se 3 (by rfl) ⟨187805, by rfl⟩ : syracuseStep 1001629 = 375611) (by norm_num)
theorem B2115773 : Blo 936583 2115773 := bbase (se 3 (by rfl) ⟨396707, by rfl⟩ : syracuseStep 2115773 = 793415) (by norm_num)
theorem B2377957 : Blo 936583 2377957 := bbase (se 4 (by rfl) ⟨222933, by rfl⟩ : syracuseStep 2377957 = 445867) (by norm_num)
theorem B2115845 : Blo 936583 2115845 := bbase (se 4 (by rfl) ⟨198360, by rfl⟩ : syracuseStep 2115845 = 396721) (by norm_num)
theorem B3164453 : Blo 936583 3164453 := bbase (se 4 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 3164453 = 593335) (by norm_num)
theorem B2115917 : Blo 936583 2115917 := bbase (se 3 (by rfl) ⟨396734, by rfl⟩ : syracuseStep 2115917 = 793469) (by norm_num)
theorem B1001813 : Blo 936583 1001813 := bbase (se 10 (by rfl) ⟨1467, by rfl⟩ : syracuseStep 1001813 = 2935) (by norm_num)
theorem B2378069 : Blo 936583 2378069 := bbase (se 10 (by rfl) ⟨3483, by rfl⟩ : syracuseStep 2378069 = 6967) (by norm_num)
theorem B2115989 : Blo 936583 2115989 := bbase (se 6 (by rfl) ⟨49593, by rfl⟩ : syracuseStep 2115989 = 99187) (by norm_num)
theorem B8014261 : Blo 936583 8014261 := bbase (se 5 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 8014261 = 751337) (by norm_num)
theorem B21121493 : Blo 936583 21121493 := bbase (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) (by norm_num)
theorem B2116061 : Blo 936583 2116061 := bbase (se 3 (by rfl) ⟨396761, by rfl⟩ : syracuseStep 2116061 = 793523) (by norm_num)
theorem B2378261 : Blo 936583 2378261 := bbase (se 6 (by rfl) ⟨55740, by rfl⟩ : syracuseStep 2378261 = 111481) (by norm_num)
theorem B2116133 : Blo 936583 2116133 := bbase (se 4 (by rfl) ⟨198387, by rfl⟩ : syracuseStep 2116133 = 396775) (by norm_num)
theorem B2116205 : Blo 936583 2116205 := bbase (se 3 (by rfl) ⟨396788, by rfl⟩ : syracuseStep 2116205 = 793577) (by norm_num)
theorem B2116277 : Blo 936583 2116277 := bbase (se 5 (by rfl) ⟨99200, by rfl⟩ : syracuseStep 2116277 = 198401) (by norm_num)
theorem B3164885 : Blo 936583 3164885 := bbase (se 7 (by rfl) ⟨37088, by rfl⟩ : syracuseStep 3164885 = 74177) (by norm_num)
theorem B1428229 : Blo 936583 1428229 := bbase (se 4 (by rfl) ⟨133896, by rfl⟩ : syracuseStep 1428229 = 267793) (by norm_num)
theorem B1428277 : Blo 936583 1428277 := bbase (se 5 (by rfl) ⟨66950, by rfl⟩ : syracuseStep 1428277 = 133901) (by norm_num)
theorem B1690445 : Blo 936583 1690445 := bbase (se 3 (by rfl) ⟨316958, by rfl⟩ : syracuseStep 1690445 = 633917) (by norm_num)
theorem B2378605 : Blo 936583 2378605 := bbase (se 3 (by rfl) ⟨445988, by rfl⟩ : syracuseStep 2378605 = 891977) (by norm_num)
theorem B4017109 : Blo 936583 4017109 := bbase (se 7 (by rfl) ⟨47075, by rfl⟩ : syracuseStep 4017109 = 94151) (by norm_num)
theorem B2378717 : Blo 936583 2378717 := bbase (se 3 (by rfl) ⟨446009, by rfl⟩ : syracuseStep 2378717 = 892019) (by norm_num)
theorem B1068061 : Blo 936583 1068061 := bbase (se 3 (by rfl) ⟨200261, by rfl⟩ : syracuseStep 1068061 = 400523) (by norm_num)
theorem B1002565 : Blo 936583 1002565 := bbase (se 4 (by rfl) ⟨93990, by rfl⟩ : syracuseStep 1002565 = 187981) (by norm_num)
theorem B1428581 : Blo 936583 1428581 := bbase (se 4 (by rfl) ⟨133929, by rfl⟩ : syracuseStep 1428581 = 267859) (by norm_num)
theorem B3165317 : Blo 936583 3165317 := bbase (se 4 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 3165317 = 593497) (by norm_num)
theorem B1002637 : Blo 936583 1002637 := bbase (se 3 (by rfl) ⟨187994, by rfl⟩ : syracuseStep 1002637 = 375989) (by norm_num)
theorem B2378909 : Blo 936583 2378909 := bbase (se 3 (by rfl) ⟨446045, by rfl⟩ : syracuseStep 2378909 = 892091) (by norm_num)
theorem B3558613 : Blo 936583 3558613 := bbase (se 7 (by rfl) ⟨41702, by rfl⟩ : syracuseStep 3558613 = 83405) (by norm_num)
theorem B1002817 : Blo 936583 1002817 := bbase (se 2 (by rfl) ⟨376056, by rfl⟩ : syracuseStep 1002817 = 752113) (by norm_num)
theorem B2379253 : Blo 936583 2379253 := bbase (se 5 (by rfl) ⟨111527, by rfl⟩ : syracuseStep 2379253 = 223055) (by norm_num)
theorem B3558917 : Blo 936583 3558917 := bbase (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) (by norm_num)
theorem B3165749 : Blo 936583 3165749 := bbase (se 5 (by rfl) ⟨148394, by rfl⟩ : syracuseStep 3165749 = 296789) (by norm_num)
theorem B2379365 : Blo 936583 2379365 := bbase (se 4 (by rfl) ⟨223065, by rfl⟩ : syracuseStep 2379365 = 446131) (by norm_num)
theorem B8113877 : Blo 936583 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B1003261 : Blo 936583 1003261 := bbase (se 3 (by rfl) ⟨188111, by rfl⟩ : syracuseStep 1003261 = 376223) (by norm_num)
theorem B1068809 : Blo 936583 1068809 := bbase (se 2 (by rfl) ⟨400803, by rfl⟩ : syracuseStep 1068809 = 801607) (by norm_num)
theorem B14634773 : Blo 936583 14634773 := bbase (se 6 (by rfl) ⟨343002, by rfl⟩ : syracuseStep 14634773 = 686005) (by norm_num)
theorem B2379557 : Blo 936583 2379557 := bbase (se 4 (by rfl) ⟨223083, by rfl⟩ : syracuseStep 2379557 = 446167) (by norm_num)
theorem B3002197 : Blo 936583 3002197 := bbase (se 9 (by rfl) ⟨8795, by rfl⟩ : syracuseStep 3002197 = 17591) (by norm_num)
theorem B4575061 : Blo 936583 4575061 := bbase (se 9 (by rfl) ⟨13403, by rfl⟩ : syracuseStep 4575061 = 26807) (by norm_num)
theorem B36622165 : Blo 936583 36622165 := bbase (se 9 (by rfl) ⟨107291, by rfl⟩ : syracuseStep 36622165 = 214583) (by norm_num)
theorem B1003385 : Blo 936583 1003385 := bbase (se 2 (by rfl) ⟨376269, by rfl⟩ : syracuseStep 1003385 = 752539) (by norm_num)
theorem B2674565 : Blo 936583 2674565 := bbase (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) (by norm_num)
theorem B1429445 : Blo 936583 1429445 := bbase (se 4 (by rfl) ⟨134010, by rfl⟩ : syracuseStep 1429445 = 268021) (by norm_num)
theorem B3166181 : Blo 936583 3166181 := bbase (se 4 (by rfl) ⟨296829, by rfl⟩ : syracuseStep 3166181 = 593659) (by norm_num)
theorem B8572949 : Blo 936583 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B1003637 : Blo 936583 1003637 := bbase (se 5 (by rfl) ⟨47045, by rfl⟩ : syracuseStep 1003637 = 94091) (by norm_num)
theorem B2379901 : Blo 936583 2379901 := bbase (se 3 (by rfl) ⟨446231, by rfl⟩ : syracuseStep 2379901 = 892463) (by norm_num)
theorem B2380013 : Blo 936583 2380013 := bbase (se 3 (by rfl) ⟨446252, by rfl⟩ : syracuseStep 2380013 = 892505) (by norm_num)
theorem B5067029 : Blo 936583 5067029 := bbase (se 6 (by rfl) ⟨118758, by rfl⟩ : syracuseStep 5067029 = 237517) (by norm_num)
theorem B8016245 : Blo 936583 8016245 := bbase (se 5 (by rfl) ⟨375761, by rfl⟩ : syracuseStep 8016245 = 751523) (by norm_num)
theorem B3166613 : Blo 936583 3166613 := bbase (se 6 (by rfl) ⟨74217, by rfl⟩ : syracuseStep 3166613 = 148435) (by norm_num)
theorem B1266077 : Blo 936583 1266077 := bbase (se 3 (by rfl) ⟨237389, by rfl⟩ : syracuseStep 1266077 = 474779) (by norm_num)
theorem B2380205 : Blo 936583 2380205 := bbase (se 3 (by rfl) ⟨446288, by rfl⟩ : syracuseStep 2380205 = 892577) (by norm_num)
theorem B1692181 : Blo 936583 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B1004081 : Blo 936583 1004081 := bbase (se 2 (by rfl) ⟨376530, by rfl⟩ : syracuseStep 1004081 = 753061) (by norm_num)
theorem B8114741 : Blo 936583 8114741 := bbase (se 5 (by rfl) ⟨380378, by rfl⟩ : syracuseStep 8114741 = 760757) (by norm_num)
theorem B2380549 : Blo 936583 2380549 := bbase (se 4 (by rfl) ⟨223176, by rfl⟩ : syracuseStep 2380549 = 446353) (by norm_num)
theorem B1004329 : Blo 936583 1004329 := bbase (se 2 (by rfl) ⟨376623, by rfl⟩ : syracuseStep 1004329 = 753247) (by norm_num)
theorem B3167045 : Blo 936583 3167045 := bbase (se 4 (by rfl) ⟨296910, by rfl⟩ : syracuseStep 3167045 = 593821) (by norm_num)
theorem B2380661 : Blo 936583 2380661 := bbase (se 5 (by rfl) ⟨111593, by rfl⟩ : syracuseStep 2380661 = 223187) (by norm_num)
theorem B1266709 : Blo 936583 1266709 := bbase (se 6 (by rfl) ⟨29688, by rfl⟩ : syracuseStep 1266709 = 59377) (by norm_num)
theorem B2675749 : Blo 936583 2675749 := bbase (se 4 (by rfl) ⟨250851, by rfl⟩ : syracuseStep 2675749 = 501703) (by norm_num)
theorem B2380853 : Blo 936583 2380853 := bbase (se 5 (by rfl) ⟨111602, by rfl⟩ : syracuseStep 2380853 = 223205) (by norm_num)
theorem B1070177 : Blo 936583 1070177 := bbase (se 2 (by rfl) ⟨401316, by rfl⟩ : syracuseStep 1070177 = 802633) (by norm_num)
theorem B1070213 : Blo 936583 1070213 := bbase (se 4 (by rfl) ⟨100332, by rfl⟩ : syracuseStep 1070213 = 200665) (by norm_num)
theorem B2675909 : Blo 936583 2675909 := bbase (se 4 (by rfl) ⟨250866, by rfl⟩ : syracuseStep 2675909 = 501733) (by norm_num)
theorem B3167477 : Blo 936583 3167477 := bbase (se 5 (by rfl) ⟨148475, by rfl⟩ : syracuseStep 3167477 = 296951) (by norm_num)
theorem B1692989 : Blo 936583 1692989 := bbase (se 3 (by rfl) ⟨317435, by rfl⟩ : syracuseStep 1692989 = 634871) (by norm_num)
theorem B2315621 : Blo 936583 2315621 := bbase (se 4 (by rfl) ⟨217089, by rfl⟩ : syracuseStep 2315621 = 434179) (by norm_num)
theorem B2676149 : Blo 936583 2676149 := bbase (se 5 (by rfl) ⟨125444, by rfl⟩ : syracuseStep 2676149 = 250889) (by norm_num)
theorem B3561029 : Blo 936583 3561029 := bbase (se 4 (by rfl) ⟨333846, by rfl⟩ : syracuseStep 3561029 = 667693) (by norm_num)
theorem B2676341 : Blo 936583 2676341 := bbase (se 5 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 2676341 = 250907) (by norm_num)
theorem B2250389 : Blo 936583 2250389 := bbase (se 6 (by rfl) ⟨52743, by rfl⟩ : syracuseStep 2250389 = 105487) (by norm_num)
theorem B1201825 : Blo 936583 1201825 := bbase (se 2 (by rfl) ⟨450684, by rfl⟩ : syracuseStep 1201825 = 901369) (by norm_num)
theorem B3167909 : Blo 936583 3167909 := bbase (se 4 (by rfl) ⟨296991, by rfl⟩ : syracuseStep 3167909 = 593983) (by norm_num)
theorem B3561317 : Blo 936583 3561317 := bbase (se 4 (by rfl) ⟨333873, by rfl⟩ : syracuseStep 3561317 = 667747) (by norm_num)
theorem B3168341 : Blo 936583 3168341 := bbase (se 8 (by rfl) ⟨18564, by rfl⟩ : syracuseStep 3168341 = 37129) (by norm_num)
theorem B1268093 : Blo 936583 1268093 := bbase (se 3 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 1268093 = 475535) (by norm_num)
theorem B1268141 : Blo 936583 1268141 := bbase (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) (by norm_num)
theorem B3168773 : Blo 936583 3168773 := bbase (se 4 (by rfl) ⟨297072, by rfl⟩ : syracuseStep 3168773 = 594145) (by norm_num)
theorem B1333837 : Blo 936583 1333837 := bbase (se 3 (by rfl) ⟨250094, by rfl⟩ : syracuseStep 1333837 = 500189) (by norm_num)
theorem B2677333 : Blo 936583 2677333 := bbase (se 8 (by rfl) ⟨15687, by rfl⟩ : syracuseStep 2677333 = 31375) (by norm_num)
theorem B3005029 : Blo 936583 3005029 := bbase (se 4 (by rfl) ⟨281721, by rfl⟩ : syracuseStep 3005029 = 563443) (by norm_num)
theorem B3005093 : Blo 936583 3005093 := bbase (se 4 (by rfl) ⟨281727, by rfl⟩ : syracuseStep 3005093 = 563455) (by norm_num)
theorem B1334173 : Blo 936583 1334173 := bbase (se 3 (by rfl) ⟨250157, by rfl⟩ : syracuseStep 1334173 = 500315) (by norm_num)
theorem B3169205 : Blo 936583 3169205 := bbase (se 5 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 3169205 = 297113) (by norm_num)
theorem B4283317 : Blo 936583 4283317 := bbase (se 5 (by rfl) ⟨200780, by rfl⟩ : syracuseStep 4283317 = 401561) (by norm_num)
theorem B3562501 : Blo 936583 3562501 := bbase (se 4 (by rfl) ⟨333984, by rfl⟩ : syracuseStep 3562501 = 667969) (by norm_num)
theorem B4512773 : Blo 936583 4512773 := bbase (se 4 (by rfl) ⟨423072, by rfl⟩ : syracuseStep 4512773 = 846145) (by norm_num)
theorem B1334389 : Blo 936583 1334389 := bbase (se 5 (by rfl) ⟨62549, by rfl⟩ : syracuseStep 1334389 = 125099) (by norm_num)
theorem B3562805 : Blo 936583 3562805 := bbase (se 5 (by rfl) ⟨167006, by rfl⟩ : syracuseStep 3562805 = 334013) (by norm_num)
theorem B3169637 : Blo 936583 3169637 := bbase (se 4 (by rfl) ⟨297153, by rfl⟩ : syracuseStep 3169637 = 594307) (by norm_num)
theorem B4742549 : Blo 936583 4742549 := bbase (se 6 (by rfl) ⟨111153, by rfl⟩ : syracuseStep 4742549 = 222307) (by norm_num)
theorem B1334765 : Blo 936583 1334765 := bbase (se 3 (by rfl) ⟨250268, by rfl⟩ : syracuseStep 1334765 = 500537) (by norm_num)
theorem B4513445 : Blo 936583 4513445 := bbase (se 4 (by rfl) ⟨423135, by rfl⟩ : syracuseStep 4513445 = 846271) (by norm_num)
theorem B2678437 : Blo 936583 2678437 := bbase (se 4 (by rfl) ⟨251103, by rfl⟩ : syracuseStep 2678437 = 502207) (by norm_num)
theorem B7134965 : Blo 936583 7134965 := bbase (se 5 (by rfl) ⟨334451, by rfl⟩ : syracuseStep 7134965 = 668903) (by norm_num)
theorem B3170069 : Blo 936583 3170069 := bbase (se 6 (by rfl) ⟨74298, by rfl⟩ : syracuseStep 3170069 = 148597) (by norm_num)
theorem B1925141 : Blo 936583 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B4284485 : Blo 936583 4284485 := bbase (se 4 (by rfl) ⟨401670, by rfl⟩ : syracuseStep 4284485 = 803341) (by norm_num)
theorem B3170501 : Blo 936583 3170501 := bbase (se 4 (by rfl) ⟨297234, by rfl⟩ : syracuseStep 3170501 = 594469) (by norm_num)
theorem B3170933 : Blo 936583 3170933 := bbase (se 5 (by rfl) ⟨148637, by rfl⟩ : syracuseStep 3170933 = 297275) (by norm_num)
theorem B4743845 : Blo 936583 4743845 := bbase (se 4 (by rfl) ⟨444735, by rfl⟩ : syracuseStep 4743845 = 889471) (by norm_num)
theorem B1336189 : Blo 936583 1336189 := bbase (se 3 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 1336189 = 501071) (by norm_num)
theorem B2253781 : Blo 936583 2253781 := bbase (se 7 (by rfl) ⟨26411, by rfl⟩ : syracuseStep 2253781 = 52823) (by norm_num)
theorem B3171365 : Blo 936583 3171365 := bbase (se 4 (by rfl) ⟨297315, by rfl⟩ : syracuseStep 3171365 = 594631) (by norm_num)
theorem B1270909 : Blo 936583 1270909 := bbase (se 3 (by rfl) ⟨238295, by rfl⟩ : syracuseStep 1270909 = 476591) (by norm_num)
theorem B3433637 : Blo 936583 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B1467605 : Blo 936583 1467605 := bbase (se 7 (by rfl) ⟨17198, by rfl⟩ : syracuseStep 1467605 = 34397) (by norm_num)
theorem B3564917 : Blo 936583 3564917 := bbase (se 5 (by rfl) ⟨167105, by rfl⟩ : syracuseStep 3564917 = 334211) (by norm_num)
theorem B2254205 : Blo 936583 2254205 := bbase (se 3 (by rfl) ⟨422663, by rfl⟩ : syracuseStep 2254205 = 845327) (by norm_num)
theorem B1336781 : Blo 936583 1336781 := bbase (se 3 (by rfl) ⟨250646, by rfl⟩ : syracuseStep 1336781 = 501293) (by norm_num)
theorem B3171797 : Blo 936583 3171797 := bbase (se 7 (by rfl) ⟨37169, by rfl⟩ : syracuseStep 3171797 = 74339) (by norm_num)
theorem B1336861 : Blo 936583 1336861 := bbase (se 3 (by rfl) ⟨250661, by rfl⟩ : syracuseStep 1336861 = 501323) (by norm_num)
theorem B2745893 : Blo 936583 2745893 := bbase (se 4 (by rfl) ⟨257427, by rfl⟩ : syracuseStep 2745893 = 514855) (by norm_num)
theorem B3008117 : Blo 936583 3008117 := bbase (se 5 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 3008117 = 282011) (by norm_num)
theorem B3565205 : Blo 936583 3565205 := bbase (se 6 (by rfl) ⟨83559, by rfl⟩ : syracuseStep 3565205 = 167119) (by norm_num)
theorem B1336981 : Blo 936583 1336981 := bbase (se 6 (by rfl) ⟨31335, by rfl⟩ : syracuseStep 1336981 = 62671) (by norm_num)
theorem B2254493 : Blo 936583 2254493 := bbase (se 3 (by rfl) ⟨422717, by rfl⟩ : syracuseStep 2254493 = 845435) (by norm_num)
theorem B1337077 : Blo 936583 1337077 := bbase (se 5 (by rfl) ⟨62675, by rfl⟩ : syracuseStep 1337077 = 125351) (by norm_num)
theorem B3663749 : Blo 936583 3663749 := bbase (se 4 (by rfl) ⟨343476, by rfl⟩ : syracuseStep 3663749 = 686953) (by norm_num)
theorem B3172229 : Blo 936583 3172229 := bbase (se 4 (by rfl) ⟨297396, by rfl⟩ : syracuseStep 3172229 = 594793) (by norm_num)
theorem B4745141 : Blo 936583 4745141 := bbase (se 5 (by rfl) ⟨222428, by rfl⟩ : syracuseStep 4745141 = 444857) (by norm_num)
theorem B1206289 : Blo 936583 1206289 := bbase (se 2 (by rfl) ⟨452358, by rfl⟩ : syracuseStep 1206289 = 904717) (by norm_num)
theorem B4810853 : Blo 936583 4810853 := bbase (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) (by norm_num)
theorem B1337573 : Blo 936583 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B3172661 : Blo 936583 3172661 := bbase (se 5 (by rfl) ⟨148718, by rfl⟩ : syracuseStep 3172661 = 297437) (by norm_num)
theorem B1206617 : Blo 936583 1206617 := bbase (se 2 (by rfl) ⟨452481, by rfl⟩ : syracuseStep 1206617 = 904963) (by norm_num)
theorem B1501573 : Blo 936583 1501573 := bbase (se 4 (by rfl) ⟨140772, by rfl⟩ : syracuseStep 1501573 = 281545) (by norm_num)
theorem B1501829 : Blo 936583 1501829 := bbase (se 4 (by rfl) ⟨140796, by rfl⟩ : syracuseStep 1501829 = 281593) (by norm_num)
theorem B1927837 : Blo 936583 1927837 := bbase (se 3 (by rfl) ⟨361469, by rfl⟩ : syracuseStep 1927837 = 722939) (by norm_num)
theorem B5335733 : Blo 936583 5335733 := bbase (se 5 (by rfl) ⟨250112, by rfl⟩ : syracuseStep 5335733 = 500225) (by norm_num)
theorem B3173093 : Blo 936583 3173093 := bbase (se 4 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 3173093 = 594955) (by norm_num)
theorem B1338125 : Blo 936583 1338125 := bbase (se 3 (by rfl) ⟨250898, by rfl⟩ : syracuseStep 1338125 = 501797) (by norm_num)
theorem B1141525 : Blo 936583 1141525 := bbase (se 6 (by rfl) ⟨26754, by rfl⟩ : syracuseStep 1141525 = 53509) (by norm_num)
theorem B3566389 : Blo 936583 3566389 := bbase (se 5 (by rfl) ⟨167174, by rfl⟩ : syracuseStep 3566389 = 334349) (by norm_num)
theorem B1502021 : Blo 936583 1502021 := bbase (se 4 (by rfl) ⟨140814, by rfl⟩ : syracuseStep 1502021 = 281629) (by norm_num)
theorem B3206101 : Blo 936583 3206101 := bbase (se 7 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 3206101 = 75143) (by norm_num)
theorem B3566693 : Blo 936583 3566693 := bbase (se 4 (by rfl) ⟨334377, by rfl⟩ : syracuseStep 3566693 = 668755) (by norm_num)
theorem B3173525 : Blo 936583 3173525 := bbase (se 6 (by rfl) ⟨74379, by rfl⟩ : syracuseStep 3173525 = 148759) (by norm_num)
theorem B4746437 : Blo 936583 4746437 := bbase (se 4 (by rfl) ⟨444978, by rfl⟩ : syracuseStep 4746437 = 889957) (by norm_num)
theorem B3042613 : Blo 936583 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B5696885 : Blo 936583 5696885 := bbase (se 5 (by rfl) ⟨267041, by rfl⟩ : syracuseStep 5696885 = 534083) (by norm_num)
theorem B1338877 : Blo 936583 1338877 := bbase (se 3 (by rfl) ⟨251039, by rfl⟩ : syracuseStep 1338877 = 502079) (by norm_num)
theorem B3173957 : Blo 936583 3173957 := bbase (se 4 (by rfl) ⟨297558, by rfl⟩ : syracuseStep 3173957 = 595117) (by norm_num)
theorem B1502957 : Blo 936583 1502957 := bbase (se 3 (by rfl) ⟨281804, by rfl⟩ : syracuseStep 1502957 = 563609) (by norm_num)
theorem B4288373 : Blo 936583 4288373 := bbase (se 5 (by rfl) ⟨201017, by rfl⟩ : syracuseStep 4288373 = 402035) (by norm_num)
theorem B1929085 : Blo 936583 1929085 := bbase (se 3 (by rfl) ⟨361703, by rfl⟩ : syracuseStep 1929085 = 723407) (by norm_num)
theorem B1404893 : Blo 936583 1404893 := bbase (se 3 (by rfl) ⟨263417, by rfl⟩ : syracuseStep 1404893 = 526835) (by norm_num)
theorem B1404917 : Blo 936583 1404917 := bbase (se 5 (by rfl) ⟨65855, by rfl⟩ : syracuseStep 1404917 = 131711) (by norm_num)
theorem B3174389 : Blo 936583 3174389 := bbase (se 5 (by rfl) ⟨148799, by rfl⟩ : syracuseStep 3174389 = 297599) (by norm_num)
theorem B1404941 : Blo 936583 1404941 := bbase (se 3 (by rfl) ⟨263426, by rfl⟩ : syracuseStep 1404941 = 526853) (by norm_num)
theorem B1404965 : Blo 936583 1404965 := bbase (se 4 (by rfl) ⟨131715, by rfl⟩ : syracuseStep 1404965 = 263431) (by norm_num)
theorem B1404989 : Blo 936583 1404989 := bbase (se 3 (by rfl) ⟨263435, by rfl⟩ : syracuseStep 1404989 = 526871) (by norm_num)
theorem B1405013 : Blo 936583 1405013 := bbase (se 8 (by rfl) ⟨8232, by rfl⟩ : syracuseStep 1405013 = 16465) (by norm_num)
theorem B1405037 : Blo 936583 1405037 := bbase (se 3 (by rfl) ⟨263444, by rfl⟩ : syracuseStep 1405037 = 526889) (by norm_num)
theorem B1503341 : Blo 936583 1503341 := bbase (se 3 (by rfl) ⟨281876, by rfl⟩ : syracuseStep 1503341 = 563753) (by norm_num)
theorem B1405061 : Blo 936583 1405061 := bbase (se 4 (by rfl) ⟨131724, by rfl⟩ : syracuseStep 1405061 = 263449) (by norm_num)
theorem B1405085 : Blo 936583 1405085 := bbase (se 3 (by rfl) ⟨263453, by rfl⟩ : syracuseStep 1405085 = 526907) (by norm_num)
theorem B1405109 : Blo 936583 1405109 := bbase (se 5 (by rfl) ⟨65864, by rfl⟩ : syracuseStep 1405109 = 131729) (by norm_num)
theorem B1405133 : Blo 936583 1405133 := bbase (se 3 (by rfl) ⟨263462, by rfl⟩ : syracuseStep 1405133 = 526925) (by norm_num)
theorem B1405157 : Blo 936583 1405157 := bbase (se 4 (by rfl) ⟨131733, by rfl⟩ : syracuseStep 1405157 = 263467) (by norm_num)
theorem B1503469 : Blo 936583 1503469 := bbase (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) (by norm_num)
theorem B1405181 : Blo 936583 1405181 := bbase (se 3 (by rfl) ⟨263471, by rfl⟩ : syracuseStep 1405181 = 526943) (by norm_num)
theorem B1405205 : Blo 936583 1405205 := bbase (se 6 (by rfl) ⟨32934, by rfl⟩ : syracuseStep 1405205 = 65869) (by norm_num)
theorem B1405229 : Blo 936583 1405229 := bbase (se 3 (by rfl) ⟨263480, by rfl⟩ : syracuseStep 1405229 = 526961) (by norm_num)
theorem B1405253 : Blo 936583 1405253 := bbase (se 4 (by rfl) ⟨131742, by rfl⟩ : syracuseStep 1405253 = 263485) (by norm_num)
theorem B1405277 : Blo 936583 1405277 := bbase (se 3 (by rfl) ⟨263489, by rfl⟩ : syracuseStep 1405277 = 526979) (by norm_num)
theorem B1405301 : Blo 936583 1405301 := bbase (se 5 (by rfl) ⟨65873, by rfl⟩ : syracuseStep 1405301 = 131747) (by norm_num)
theorem B1405325 : Blo 936583 1405325 := bbase (se 3 (by rfl) ⟨263498, by rfl⟩ : syracuseStep 1405325 = 526997) (by norm_num)
theorem B1405349 : Blo 936583 1405349 := bbase (se 4 (by rfl) ⟨131751, by rfl⟩ : syracuseStep 1405349 = 263503) (by norm_num)
theorem B1405373 : Blo 936583 1405373 := bbase (se 3 (by rfl) ⟨263507, by rfl⟩ : syracuseStep 1405373 = 527015) (by norm_num)
theorem B1405397 : Blo 936583 1405397 := bbase (se 7 (by rfl) ⟨16469, by rfl⟩ : syracuseStep 1405397 = 32939) (by norm_num)
theorem B4747733 : Blo 936583 4747733 := bbase (se 7 (by rfl) ⟨55637, by rfl⟩ : syracuseStep 4747733 = 111275) (by norm_num)
theorem B1405421 : Blo 936583 1405421 := bbase (se 3 (by rfl) ⟨263516, by rfl⟩ : syracuseStep 1405421 = 527033) (by norm_num)
theorem B1405445 : Blo 936583 1405445 := bbase (se 4 (by rfl) ⟨131760, by rfl⟩ : syracuseStep 1405445 = 263521) (by norm_num)
theorem B1405469 : Blo 936583 1405469 := bbase (se 3 (by rfl) ⟨263525, by rfl⟩ : syracuseStep 1405469 = 527051) (by norm_num)
theorem B1405493 : Blo 936583 1405493 := bbase (se 5 (by rfl) ⟨65882, by rfl⟩ : syracuseStep 1405493 = 131765) (by norm_num)
theorem B1405517 : Blo 936583 1405517 := bbase (se 3 (by rfl) ⟨263534, by rfl⟩ : syracuseStep 1405517 = 527069) (by norm_num)
theorem B1405541 : Blo 936583 1405541 := bbase (se 4 (by rfl) ⟨131769, by rfl⟩ : syracuseStep 1405541 = 263539) (by norm_num)
theorem B1405565 : Blo 936583 1405565 := bbase (se 3 (by rfl) ⟨263543, by rfl⟩ : syracuseStep 1405565 = 527087) (by norm_num)
theorem B1405589 : Blo 936583 1405589 := bbase (se 6 (by rfl) ⟨32943, by rfl⟩ : syracuseStep 1405589 = 65887) (by norm_num)
theorem B1405613 : Blo 936583 1405613 := bbase (se 3 (by rfl) ⟨263552, by rfl⟩ : syracuseStep 1405613 = 527105) (by norm_num)
theorem B1405637 : Blo 936583 1405637 := bbase (se 4 (by rfl) ⟨131778, by rfl⟩ : syracuseStep 1405637 = 263557) (by norm_num)
theorem B1405661 : Blo 936583 1405661 := bbase (se 3 (by rfl) ⟨263561, by rfl⟩ : syracuseStep 1405661 = 527123) (by norm_num)
theorem B2257645 : Blo 936583 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B1405685 : Blo 936583 1405685 := bbase (se 5 (by rfl) ⟨65891, by rfl⟩ : syracuseStep 1405685 = 131783) (by norm_num)
theorem B1405709 : Blo 936583 1405709 := bbase (se 3 (by rfl) ⟨263570, by rfl⟩ : syracuseStep 1405709 = 527141) (by norm_num)
theorem B1405733 : Blo 936583 1405733 := bbase (se 4 (by rfl) ⟨131787, by rfl⟩ : syracuseStep 1405733 = 263575) (by norm_num)
theorem B1405757 : Blo 936583 1405757 := bbase (se 3 (by rfl) ⟨263579, by rfl⟩ : syracuseStep 1405757 = 527159) (by norm_num)
theorem B1405781 : Blo 936583 1405781 := bbase (se 9 (by rfl) ⟨4118, by rfl⟩ : syracuseStep 1405781 = 8237) (by norm_num)
theorem B1405805 : Blo 936583 1405805 := bbase (se 3 (by rfl) ⟨263588, by rfl⟩ : syracuseStep 1405805 = 527177) (by norm_num)
theorem B1405829 : Blo 936583 1405829 := bbase (se 4 (by rfl) ⟨131796, by rfl⟩ : syracuseStep 1405829 = 263593) (by norm_num)
theorem B1405853 : Blo 936583 1405853 := bbase (se 3 (by rfl) ⟨263597, by rfl⟩ : syracuseStep 1405853 = 527195) (by norm_num)
theorem B1405877 : Blo 936583 1405877 := bbase (se 5 (by rfl) ⟨65900, by rfl⟩ : syracuseStep 1405877 = 131801) (by norm_num)
theorem B1405901 : Blo 936583 1405901 := bbase (se 3 (by rfl) ⟨263606, by rfl⟩ : syracuseStep 1405901 = 527213) (by norm_num)
theorem B1405925 : Blo 936583 1405925 := bbase (se 4 (by rfl) ⟨131805, by rfl⟩ : syracuseStep 1405925 = 263611) (by norm_num)
theorem B1405949 : Blo 936583 1405949 := bbase (se 3 (by rfl) ⟨263615, by rfl⟩ : syracuseStep 1405949 = 527231) (by norm_num)
theorem B1405973 : Blo 936583 1405973 := bbase (se 6 (by rfl) ⟨32952, by rfl⟩ : syracuseStep 1405973 = 65905) (by norm_num)
theorem B1405997 : Blo 936583 1405997 := bbase (se 3 (by rfl) ⟨263624, by rfl⟩ : syracuseStep 1405997 = 527249) (by norm_num)
theorem B1406021 : Blo 936583 1406021 := bbase (se 4 (by rfl) ⟨131814, by rfl⟩ : syracuseStep 1406021 = 263629) (by norm_num)
theorem B1406045 : Blo 936583 1406045 := bbase (se 3 (by rfl) ⟨263633, by rfl⟩ : syracuseStep 1406045 = 527267) (by norm_num)
theorem B1406069 : Blo 936583 1406069 := bbase (se 5 (by rfl) ⟨65909, by rfl⟩ : syracuseStep 1406069 = 131819) (by norm_num)
theorem B1406093 : Blo 936583 1406093 := bbase (se 3 (by rfl) ⟨263642, by rfl⟩ : syracuseStep 1406093 = 527285) (by norm_num)
theorem B1406117 : Blo 936583 1406117 := bbase (se 4 (by rfl) ⟨131823, by rfl⟩ : syracuseStep 1406117 = 263647) (by norm_num)
theorem B3568805 : Blo 936583 3568805 := bbase (se 4 (by rfl) ⟨334575, by rfl⟩ : syracuseStep 3568805 = 669151) (by norm_num)
theorem B3798197 : Blo 936583 3798197 := bbase (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) (by norm_num)
theorem B1406141 : Blo 936583 1406141 := bbase (se 3 (by rfl) ⟨263651, by rfl⟩ : syracuseStep 1406141 = 527303) (by norm_num)
theorem B1406165 : Blo 936583 1406165 := bbase (se 7 (by rfl) ⟨16478, by rfl⟩ : syracuseStep 1406165 = 32957) (by norm_num)
theorem B1504469 : Blo 936583 1504469 := bbase (se 7 (by rfl) ⟨17630, by rfl⟩ : syracuseStep 1504469 = 35261) (by norm_num)
theorem B1406189 : Blo 936583 1406189 := bbase (se 3 (by rfl) ⟨263660, by rfl⟩ : syracuseStep 1406189 = 527321) (by norm_num)
theorem B1406213 : Blo 936583 1406213 := bbase (se 4 (by rfl) ⟨131832, by rfl⟩ : syracuseStep 1406213 = 263665) (by norm_num)
theorem B1406237 : Blo 936583 1406237 := bbase (se 3 (by rfl) ⟨263669, by rfl⟩ : syracuseStep 1406237 = 527339) (by norm_num)
theorem B1406261 : Blo 936583 1406261 := bbase (se 5 (by rfl) ⟨65918, by rfl⟩ : syracuseStep 1406261 = 131837) (by norm_num)
theorem B3011909 : Blo 936583 3011909 := bbase (se 4 (by rfl) ⟨282366, by rfl⟩ : syracuseStep 3011909 = 564733) (by norm_num)
theorem B1406285 : Blo 936583 1406285 := bbase (se 3 (by rfl) ⟨263678, by rfl⟩ : syracuseStep 1406285 = 527357) (by norm_num)
theorem B1504597 : Blo 936583 1504597 := bbase (se 13 (by rfl) ⟨275, by rfl⟩ : syracuseStep 1504597 = 551) (by norm_num)
theorem B1406309 : Blo 936583 1406309 := bbase (se 4 (by rfl) ⟨131841, by rfl⟩ : syracuseStep 1406309 = 263683) (by norm_num)
theorem B1406333 : Blo 936583 1406333 := bbase (se 3 (by rfl) ⟨263687, by rfl⟩ : syracuseStep 1406333 = 527375) (by norm_num)
theorem B2258317 : Blo 936583 2258317 := bbase (se 3 (by rfl) ⟨423434, by rfl⟩ : syracuseStep 2258317 = 846869) (by norm_num)
theorem B1406357 : Blo 936583 1406357 := bbase (se 6 (by rfl) ⟨32961, by rfl⟩ : syracuseStep 1406357 = 65923) (by norm_num)
theorem B1406381 : Blo 936583 1406381 := bbase (se 3 (by rfl) ⟨263696, by rfl⟩ : syracuseStep 1406381 = 527393) (by norm_num)
theorem B1406405 : Blo 936583 1406405 := bbase (se 4 (by rfl) ⟨131850, by rfl⟩ : syracuseStep 1406405 = 263701) (by norm_num)
theorem B3569093 : Blo 936583 3569093 := bbase (se 4 (by rfl) ⟨334602, by rfl⟩ : syracuseStep 3569093 = 669205) (by norm_num)
theorem B1406429 : Blo 936583 1406429 := bbase (se 3 (by rfl) ⟨263705, by rfl⟩ : syracuseStep 1406429 = 527411) (by norm_num)
theorem B1406453 : Blo 936583 1406453 := bbase (se 5 (by rfl) ⟨65927, by rfl⟩ : syracuseStep 1406453 = 131855) (by norm_num)
theorem B1406477 : Blo 936583 1406477 := bbase (se 3 (by rfl) ⟨263714, by rfl⟩ : syracuseStep 1406477 = 527429) (by norm_num)
theorem B1406501 : Blo 936583 1406501 := bbase (se 4 (by rfl) ⟨131859, by rfl⟩ : syracuseStep 1406501 = 263719) (by norm_num)
theorem B1406525 : Blo 936583 1406525 := bbase (se 3 (by rfl) ⟨263723, by rfl⟩ : syracuseStep 1406525 = 527447) (by norm_num)
theorem B1406549 : Blo 936583 1406549 := bbase (se 8 (by rfl) ⟨8241, by rfl⟩ : syracuseStep 1406549 = 16483) (by norm_num)
theorem B1406573 : Blo 936583 1406573 := bbase (se 3 (by rfl) ⟨263732, by rfl⟩ : syracuseStep 1406573 = 527465) (by norm_num)
theorem B2258549 : Blo 936583 2258549 := bbase (se 5 (by rfl) ⟨105869, by rfl⟩ : syracuseStep 2258549 = 211739) (by norm_num)
theorem B1406597 : Blo 936583 1406597 := bbase (se 4 (by rfl) ⟨131868, by rfl⟩ : syracuseStep 1406597 = 263737) (by norm_num)
theorem B2848405 : Blo 936583 2848405 := bbase (se 6 (by rfl) ⟨66759, by rfl⟩ : syracuseStep 2848405 = 133519) (by norm_num)
theorem B1406621 : Blo 936583 1406621 := bbase (se 3 (by rfl) ⟨263741, by rfl⟩ : syracuseStep 1406621 = 527483) (by norm_num)
theorem B1406645 : Blo 936583 1406645 := bbase (se 5 (by rfl) ⟨65936, by rfl⟩ : syracuseStep 1406645 = 131873) (by norm_num)
theorem B1406669 : Blo 936583 1406669 := bbase (se 3 (by rfl) ⟨263750, by rfl⟩ : syracuseStep 1406669 = 527501) (by norm_num)
theorem B1504981 : Blo 936583 1504981 := bbase (se 7 (by rfl) ⟨17636, by rfl⟩ : syracuseStep 1504981 = 35273) (by norm_num)
theorem B1406693 : Blo 936583 1406693 := bbase (se 4 (by rfl) ⟨131877, by rfl⟩ : syracuseStep 1406693 = 263755) (by norm_num)
theorem B4749029 : Blo 936583 4749029 := bbase (se 4 (by rfl) ⟨445221, by rfl⟩ : syracuseStep 4749029 = 890443) (by norm_num)
theorem B1603309 : Blo 936583 1603309 := bbase (se 3 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 1603309 = 601241) (by norm_num)
theorem B1406717 : Blo 936583 1406717 := bbase (se 3 (by rfl) ⟨263759, by rfl⟩ : syracuseStep 1406717 = 527519) (by norm_num)
theorem B2258693 : Blo 936583 2258693 := bbase (se 4 (by rfl) ⟨211752, by rfl⟩ : syracuseStep 2258693 = 423505) (by norm_num)
theorem B1406741 : Blo 936583 1406741 := bbase (se 6 (by rfl) ⟨32970, by rfl⟩ : syracuseStep 1406741 = 65941) (by norm_num)
theorem B1406765 : Blo 936583 1406765 := bbase (se 3 (by rfl) ⟨263768, by rfl⟩ : syracuseStep 1406765 = 527537) (by norm_num)
theorem B2258741 : Blo 936583 2258741 := bbase (se 5 (by rfl) ⟨105878, by rfl⟩ : syracuseStep 2258741 = 211757) (by norm_num)
theorem B1406789 : Blo 936583 1406789 := bbase (se 4 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 1406789 = 263773) (by norm_num)
theorem B1603405 : Blo 936583 1603405 := bbase (se 3 (by rfl) ⟨300638, by rfl⟩ : syracuseStep 1603405 = 601277) (by norm_num)
theorem B5699413 : Blo 936583 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B1406813 : Blo 936583 1406813 := bbase (se 3 (by rfl) ⟨263777, by rfl⟩ : syracuseStep 1406813 = 527555) (by norm_num)
theorem B1406837 : Blo 936583 1406837 := bbase (se 5 (by rfl) ⟨65945, by rfl⟩ : syracuseStep 1406837 = 131891) (by norm_num)
theorem B1406861 : Blo 936583 1406861 := bbase (se 3 (by rfl) ⟨263786, by rfl⟩ : syracuseStep 1406861 = 527573) (by norm_num)
theorem B1406885 : Blo 936583 1406885 := bbase (se 4 (by rfl) ⟨131895, by rfl⟩ : syracuseStep 1406885 = 263791) (by norm_num)
theorem B1406909 : Blo 936583 1406909 := bbase (se 3 (by rfl) ⟨263795, by rfl⟩ : syracuseStep 1406909 = 527591) (by norm_num)
theorem B1603541 : Blo 936583 1603541 := bbase (se 7 (by rfl) ⟨18791, by rfl⟩ : syracuseStep 1603541 = 37583) (by norm_num)
theorem B1406933 : Blo 936583 1406933 := bbase (se 7 (by rfl) ⟨16487, by rfl⟩ : syracuseStep 1406933 = 32975) (by norm_num)
theorem B1505237 : Blo 936583 1505237 := bbase (se 7 (by rfl) ⟨17639, by rfl⟩ : syracuseStep 1505237 = 35279) (by norm_num)
theorem B1406957 : Blo 936583 1406957 := bbase (se 3 (by rfl) ⟨263804, by rfl⟩ : syracuseStep 1406957 = 527609) (by norm_num)
theorem B1406981 : Blo 936583 1406981 := bbase (se 4 (by rfl) ⟨131904, by rfl⟩ : syracuseStep 1406981 = 263809) (by norm_num)
theorem B1407005 : Blo 936583 1407005 := bbase (se 3 (by rfl) ⟨263813, by rfl⟩ : syracuseStep 1407005 = 527627) (by norm_num)
theorem B1407029 : Blo 936583 1407029 := bbase (se 5 (by rfl) ⟨65954, by rfl⟩ : syracuseStep 1407029 = 131909) (by norm_num)
theorem B1407053 : Blo 936583 1407053 := bbase (se 3 (by rfl) ⟨263822, by rfl⟩ : syracuseStep 1407053 = 527645) (by norm_num)
theorem B9140309 : Blo 936583 9140309 := bbase (se 8 (by rfl) ⟨53556, by rfl⟩ : syracuseStep 9140309 = 107113) (by norm_num)
theorem B2259029 : Blo 936583 2259029 := bbase (se 8 (by rfl) ⟨13236, by rfl⟩ : syracuseStep 2259029 = 26473) (by norm_num)
theorem B1407077 : Blo 936583 1407077 := bbase (se 4 (by rfl) ⟨131913, by rfl⟩ : syracuseStep 1407077 = 263827) (by norm_num)
theorem B1407101 : Blo 936583 1407101 := bbase (se 3 (by rfl) ⟨263831, by rfl⟩ : syracuseStep 1407101 = 527663) (by norm_num)
theorem B1407125 : Blo 936583 1407125 := bbase (se 6 (by rfl) ⟨32979, by rfl⟩ : syracuseStep 1407125 = 65959) (by norm_num)
theorem B2062493 : Blo 936583 2062493 := bbase (se 3 (by rfl) ⟨386717, by rfl⟩ : syracuseStep 2062493 = 773435) (by norm_num)
theorem B1407149 : Blo 936583 1407149 := bbase (se 3 (by rfl) ⟨263840, by rfl⟩ : syracuseStep 1407149 = 527681) (by norm_num)
theorem B1407173 : Blo 936583 1407173 := bbase (se 4 (by rfl) ⟨131922, by rfl⟩ : syracuseStep 1407173 = 263845) (by norm_num)
theorem B1145029 : Blo 936583 1145029 := bbase (se 4 (by rfl) ⟨107346, by rfl⟩ : syracuseStep 1145029 = 214693) (by norm_num)
theorem B3012821 : Blo 936583 3012821 := bbase (se 7 (by rfl) ⟨35306, by rfl⟩ : syracuseStep 3012821 = 70613) (by norm_num)
theorem B1407197 : Blo 936583 1407197 := bbase (se 3 (by rfl) ⟨263849, by rfl⟩ : syracuseStep 1407197 = 527699) (by norm_num)
theorem B1407221 : Blo 936583 1407221 := bbase (se 5 (by rfl) ⟨65963, by rfl⟩ : syracuseStep 1407221 = 131927) (by norm_num)
theorem B1407245 : Blo 936583 1407245 := bbase (se 3 (by rfl) ⟨263858, by rfl⟩ : syracuseStep 1407245 = 527717) (by norm_num)
theorem B1407269 : Blo 936583 1407269 := bbase (se 4 (by rfl) ⟨131931, by rfl⟩ : syracuseStep 1407269 = 263863) (by norm_num)
theorem B1407293 : Blo 936583 1407293 := bbase (se 3 (by rfl) ⟨263867, by rfl⟩ : syracuseStep 1407293 = 527735) (by norm_num)
theorem B1603925 : Blo 936583 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B1407317 : Blo 936583 1407317 := bbase (se 10 (by rfl) ⟨2061, by rfl⟩ : syracuseStep 1407317 = 4123) (by norm_num)
theorem B19298645 : Blo 936583 19298645 := bbase (se 10 (by rfl) ⟨28269, by rfl⟩ : syracuseStep 19298645 = 56539) (by norm_num)
theorem B1407341 : Blo 936583 1407341 := bbase (se 3 (by rfl) ⟨263876, by rfl⟩ : syracuseStep 1407341 = 527753) (by norm_num)
theorem B1407365 : Blo 936583 1407365 := bbase (se 4 (by rfl) ⟨131940, by rfl⟩ : syracuseStep 1407365 = 263881) (by norm_num)
theorem B1407389 : Blo 936583 1407389 := bbase (se 3 (by rfl) ⟨263885, by rfl⟩ : syracuseStep 1407389 = 527771) (by norm_num)
theorem B1407413 : Blo 936583 1407413 := bbase (se 5 (by rfl) ⟨65972, by rfl⟩ : syracuseStep 1407413 = 131945) (by norm_num)
theorem B1407437 : Blo 936583 1407437 := bbase (se 3 (by rfl) ⟨263894, by rfl⟩ : syracuseStep 1407437 = 527789) (by norm_num)
theorem B1407461 : Blo 936583 1407461 := bbase (se 4 (by rfl) ⟨131949, by rfl⟩ : syracuseStep 1407461 = 263899) (by norm_num)
theorem B1407485 : Blo 936583 1407485 := bbase (se 3 (by rfl) ⟨263903, by rfl⟩ : syracuseStep 1407485 = 527807) (by norm_num)
theorem B1407509 : Blo 936583 1407509 := bbase (se 6 (by rfl) ⟨32988, by rfl⟩ : syracuseStep 1407509 = 65977) (by norm_num)
theorem B1407533 : Blo 936583 1407533 := bbase (se 3 (by rfl) ⟨263912, by rfl⟩ : syracuseStep 1407533 = 527825) (by norm_num)
theorem B1407557 : Blo 936583 1407557 := bbase (se 4 (by rfl) ⟨131958, by rfl⟩ : syracuseStep 1407557 = 263917) (by norm_num)
theorem B1407581 : Blo 936583 1407581 := bbase (se 3 (by rfl) ⟨263921, by rfl⟩ : syracuseStep 1407581 = 527843) (by norm_num)
theorem B3570277 : Blo 936583 3570277 := bbase (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) (by norm_num)
theorem B1014377 : Blo 936583 1014377 := bbase (se 2 (by rfl) ⟨380391, by rfl⟩ : syracuseStep 1014377 = 760783) (by norm_num)
theorem B1407605 : Blo 936583 1407605 := bbase (se 5 (by rfl) ⟨65981, by rfl⟩ : syracuseStep 1407605 = 131963) (by norm_num)
theorem B1407629 : Blo 936583 1407629 := bbase (se 3 (by rfl) ⟨263930, by rfl⟩ : syracuseStep 1407629 = 527861) (by norm_num)
theorem B1407653 : Blo 936583 1407653 := bbase (se 4 (by rfl) ⟨131967, by rfl⟩ : syracuseStep 1407653 = 263935) (by norm_num)
theorem B1899197 : Blo 936583 1899197 := bbase (se 3 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 1899197 = 712199) (by norm_num)
theorem B1407677 : Blo 936583 1407677 := bbase (se 3 (by rfl) ⟨263939, by rfl⟩ : syracuseStep 1407677 = 527879) (by norm_num)
theorem B1407701 : Blo 936583 1407701 := bbase (se 7 (by rfl) ⟨16496, by rfl⟩ : syracuseStep 1407701 = 32993) (by norm_num)
theorem B1407725 : Blo 936583 1407725 := bbase (se 3 (by rfl) ⟨263948, by rfl⟩ : syracuseStep 1407725 = 527897) (by norm_num)
theorem B1407749 : Blo 936583 1407749 := bbase (se 4 (by rfl) ⟨131976, by rfl⟩ : syracuseStep 1407749 = 263953) (by norm_num)
theorem B1407773 : Blo 936583 1407773 := bbase (se 3 (by rfl) ⟨263957, by rfl⟩ : syracuseStep 1407773 = 527915) (by norm_num)
theorem B2849573 : Blo 936583 2849573 := bbase (se 4 (by rfl) ⟨267147, by rfl⟩ : syracuseStep 2849573 = 534295) (by norm_num)
theorem B1407797 : Blo 936583 1407797 := bbase (se 5 (by rfl) ⟨65990, by rfl⟩ : syracuseStep 1407797 = 131981) (by norm_num)
theorem B1506109 : Blo 936583 1506109 := bbase (se 3 (by rfl) ⟨282395, by rfl⟩ : syracuseStep 1506109 = 564791) (by norm_num)
theorem B1407821 : Blo 936583 1407821 := bbase (se 3 (by rfl) ⟨263966, by rfl⟩ : syracuseStep 1407821 = 527933) (by norm_num)
theorem B1407845 : Blo 936583 1407845 := bbase (se 4 (by rfl) ⟨131985, by rfl⟩ : syracuseStep 1407845 = 263971) (by norm_num)
theorem B1407869 : Blo 936583 1407869 := bbase (se 3 (by rfl) ⟨263975, by rfl⟩ : syracuseStep 1407869 = 527951) (by norm_num)
theorem B1407893 : Blo 936583 1407893 := bbase (se 6 (by rfl) ⟨32997, by rfl⟩ : syracuseStep 1407893 = 65995) (by norm_num)
theorem B3570581 : Blo 936583 3570581 := bbase (se 6 (by rfl) ⟨83685, by rfl⟩ : syracuseStep 3570581 = 167371) (by norm_num)
theorem B1506205 : Blo 936583 1506205 := bbase (se 3 (by rfl) ⟨282413, by rfl⟩ : syracuseStep 1506205 = 564827) (by norm_num)
theorem B1407917 : Blo 936583 1407917 := bbase (se 3 (by rfl) ⟨263984, by rfl⟩ : syracuseStep 1407917 = 527969) (by norm_num)
theorem B1407941 : Blo 936583 1407941 := bbase (se 4 (by rfl) ⟨131994, by rfl⟩ : syracuseStep 1407941 = 263989) (by norm_num)
theorem B1407965 : Blo 936583 1407965 := bbase (se 3 (by rfl) ⟨263993, by rfl⟩ : syracuseStep 1407965 = 527987) (by norm_num)
theorem B4750325 : Blo 936583 4750325 := bbase (se 5 (by rfl) ⟨222671, by rfl⟩ : syracuseStep 4750325 = 445343) (by norm_num)
theorem B1407989 : Blo 936583 1407989 := bbase (se 5 (by rfl) ⟨65999, by rfl⟩ : syracuseStep 1407989 = 131999) (by norm_num)
theorem B1408013 : Blo 936583 1408013 := bbase (se 3 (by rfl) ⟨264002, by rfl⟩ : syracuseStep 1408013 = 528005) (by norm_num)
theorem B1408037 : Blo 936583 1408037 := bbase (se 4 (by rfl) ⟨132003, by rfl⟩ : syracuseStep 1408037 = 264007) (by norm_num)
theorem B1408061 : Blo 936583 1408061 := bbase (se 3 (by rfl) ⟨264011, by rfl⟩ : syracuseStep 1408061 = 528023) (by norm_num)
theorem B1506365 : Blo 936583 1506365 := bbase (se 3 (by rfl) ⟨282443, by rfl⟩ : syracuseStep 1506365 = 564887) (by norm_num)
theorem B1408085 : Blo 936583 1408085 := bbase (se 8 (by rfl) ⟨8250, by rfl⟩ : syracuseStep 1408085 = 16501) (by norm_num)
theorem B1408109 : Blo 936583 1408109 := bbase (se 3 (by rfl) ⟨264020, by rfl⟩ : syracuseStep 1408109 = 528041) (by norm_num)
theorem B1408133 : Blo 936583 1408133 := bbase (se 4 (by rfl) ⟨132012, by rfl⟩ : syracuseStep 1408133 = 264025) (by norm_num)
theorem B1408157 : Blo 936583 1408157 := bbase (se 3 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 1408157 = 528059) (by norm_num)
theorem B1408181 : Blo 936583 1408181 := bbase (se 5 (by rfl) ⟨66008, by rfl⟩ : syracuseStep 1408181 = 132017) (by norm_num)
theorem B1408205 : Blo 936583 1408205 := bbase (se 3 (by rfl) ⟨264038, by rfl⟩ : syracuseStep 1408205 = 528077) (by norm_num)
theorem B1408229 : Blo 936583 1408229 := bbase (se 4 (by rfl) ⟨132021, by rfl⟩ : syracuseStep 1408229 = 264043) (by norm_num)
theorem B1408253 : Blo 936583 1408253 := bbase (se 3 (by rfl) ⟨264047, by rfl⟩ : syracuseStep 1408253 = 528095) (by norm_num)
theorem B1408277 : Blo 936583 1408277 := bbase (se 6 (by rfl) ⟨33006, by rfl⟩ : syracuseStep 1408277 = 66013) (by norm_num)
theorem B1408301 : Blo 936583 1408301 := bbase (se 3 (by rfl) ⟨264056, by rfl⟩ : syracuseStep 1408301 = 528113) (by norm_num)
theorem B1408325 : Blo 936583 1408325 := bbase (se 4 (by rfl) ⟨132030, by rfl⟩ : syracuseStep 1408325 = 264061) (by norm_num)
theorem B1408349 : Blo 936583 1408349 := bbase (se 3 (by rfl) ⟨264065, by rfl⟩ : syracuseStep 1408349 = 528131) (by norm_num)
theorem B1899877 : Blo 936583 1899877 := bbase (se 4 (by rfl) ⟨178113, by rfl⟩ : syracuseStep 1899877 = 356227) (by norm_num)
theorem B1408373 : Blo 936583 1408373 := bbase (se 5 (by rfl) ⟨66017, by rfl⟩ : syracuseStep 1408373 = 132035) (by norm_num)
theorem B1408397 : Blo 936583 1408397 := bbase (se 3 (by rfl) ⟨264074, by rfl⟩ : syracuseStep 1408397 = 528149) (by norm_num)
theorem B11435413 : Blo 936583 11435413 := bbase (se 6 (by rfl) ⟨268017, by rfl⟩ : syracuseStep 11435413 = 536035) (by norm_num)
theorem B1408421 : Blo 936583 1408421 := bbase (se 4 (by rfl) ⟨132039, by rfl⟩ : syracuseStep 1408421 = 264079) (by norm_num)
theorem B1408445 : Blo 936583 1408445 := bbase (se 3 (by rfl) ⟨264083, by rfl⟩ : syracuseStep 1408445 = 528167) (by norm_num)
theorem B1113553 : Blo 936583 1113553 := bbase (se 2 (by rfl) ⟨417582, by rfl⟩ : syracuseStep 1113553 = 835165) (by norm_num)
theorem B1408469 : Blo 936583 1408469 := bbase (se 7 (by rfl) ⟨16505, by rfl⟩ : syracuseStep 1408469 = 33011) (by norm_num)
theorem B1408493 : Blo 936583 1408493 := bbase (se 3 (by rfl) ⟨264092, by rfl⟩ : syracuseStep 1408493 = 528185) (by norm_num)
theorem B1408517 : Blo 936583 1408517 := bbase (se 4 (by rfl) ⟨132048, by rfl⟩ : syracuseStep 1408517 = 264097) (by norm_num)
theorem B1408541 : Blo 936583 1408541 := bbase (se 3 (by rfl) ⟨264101, by rfl⟩ : syracuseStep 1408541 = 528203) (by norm_num)
theorem B1408565 : Blo 936583 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B1408589 : Blo 936583 1408589 := bbase (se 3 (by rfl) ⟨264110, by rfl⟩ : syracuseStep 1408589 = 528221) (by norm_num)
theorem B949849 : Blo 936583 949849 := bbase (se 2 (by rfl) ⟨356193, by rfl⟩ : syracuseStep 949849 = 712387) (by norm_num)
theorem B1408613 : Blo 936583 1408613 := bbase (se 4 (by rfl) ⟨132057, by rfl⟩ : syracuseStep 1408613 = 264115) (by norm_num)
theorem B1408637 : Blo 936583 1408637 := bbase (se 3 (by rfl) ⟨264119, by rfl⟩ : syracuseStep 1408637 = 528239) (by norm_num)
theorem B12025493 : Blo 936583 12025493 := bbase (se 6 (by rfl) ⟨281847, by rfl⟩ : syracuseStep 12025493 = 563695) (by norm_num)
theorem B1408661 : Blo 936583 1408661 := bbase (se 6 (by rfl) ⟨33015, by rfl⟩ : syracuseStep 1408661 = 66031) (by norm_num)
theorem B1408685 : Blo 936583 1408685 := bbase (se 3 (by rfl) ⟨264128, by rfl⟩ : syracuseStep 1408685 = 528257) (by norm_num)
theorem B1408709 : Blo 936583 1408709 := bbase (se 4 (by rfl) ⟨132066, by rfl⟩ : syracuseStep 1408709 = 264133) (by norm_num)
theorem B1408733 : Blo 936583 1408733 := bbase (se 3 (by rfl) ⟨264137, by rfl⟩ : syracuseStep 1408733 = 528275) (by norm_num)
theorem B1408757 : Blo 936583 1408757 := bbase (se 5 (by rfl) ⟨66035, by rfl⟩ : syracuseStep 1408757 = 132071) (by norm_num)
theorem B1408781 : Blo 936583 1408781 := bbase (se 3 (by rfl) ⟨264146, by rfl⟩ : syracuseStep 1408781 = 528293) (by norm_num)
theorem B1408805 : Blo 936583 1408805 := bbase (se 4 (by rfl) ⟨132075, by rfl⟩ : syracuseStep 1408805 = 264151) (by norm_num)
theorem B950077 : Blo 936583 950077 := bbase (se 3 (by rfl) ⟨178139, by rfl⟩ : syracuseStep 950077 = 356279) (by norm_num)
theorem B1408829 : Blo 936583 1408829 := bbase (se 3 (by rfl) ⟨264155, by rfl⟩ : syracuseStep 1408829 = 528311) (by norm_num)
theorem B1408853 : Blo 936583 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B1408877 : Blo 936583 1408877 := bbase (se 3 (by rfl) ⟨264164, by rfl⟩ : syracuseStep 1408877 = 528329) (by norm_num)
theorem B9633653 : Blo 936583 9633653 := bbase (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) (by norm_num)
theorem B1408901 : Blo 936583 1408901 := bbase (se 4 (by rfl) ⟨132084, by rfl⟩ : syracuseStep 1408901 = 264169) (by norm_num)
theorem B1408925 : Blo 936583 1408925 := bbase (se 3 (by rfl) ⟨264173, by rfl⟩ : syracuseStep 1408925 = 528347) (by norm_num)
theorem B1408949 : Blo 936583 1408949 := bbase (se 5 (by rfl) ⟨66044, by rfl⟩ : syracuseStep 1408949 = 132089) (by norm_num)
theorem B1408973 : Blo 936583 1408973 := bbase (se 3 (by rfl) ⟨264182, by rfl⟩ : syracuseStep 1408973 = 528365) (by norm_num)
theorem B1408997 : Blo 936583 1408997 := bbase (se 4 (by rfl) ⟨132093, by rfl⟩ : syracuseStep 1408997 = 264187) (by norm_num)
theorem B1900525 : Blo 936583 1900525 := bbase (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) (by norm_num)
theorem B1409021 : Blo 936583 1409021 := bbase (se 3 (by rfl) ⟨264191, by rfl⟩ : syracuseStep 1409021 = 528383) (by norm_num)
theorem B1409027 : Blo 936583 1409027 := bstep (se 1 (by rfl) ⟨1056770, by rfl⟩ : syracuseStep 1409027 = 2113541) B2113541
theorem B1409057 : Blo 936583 1409057 := bstep (se 2 (by rfl) ⟨528396, by rfl⟩ : syracuseStep 1409057 = 1056793) B1056793
theorem B1409075 : Blo 936583 1409075 := bstep (se 1 (by rfl) ⟨1056806, by rfl⟩ : syracuseStep 1409075 = 2113613) B2113613
theorem B1409105 : Blo 936583 1409105 := bstep (se 2 (by rfl) ⟨528414, by rfl⟩ : syracuseStep 1409105 = 1056829) B1056829
theorem B4751459 : Blo 936583 4751459 := bstep (se 1 (by rfl) ⟨3563594, by rfl⟩ : syracuseStep 4751459 = 7127189) B7127189
theorem B1409123 : Blo 936583 1409123 := bstep (se 1 (by rfl) ⟨1056842, by rfl⟩ : syracuseStep 1409123 = 2113685) B2113685
theorem B1409153 : Blo 936583 1409153 := bstep (se 2 (by rfl) ⟨528432, by rfl⟩ : syracuseStep 1409153 = 1056865) B1056865
theorem B1409171 : Blo 936583 1409171 := bstep (se 1 (by rfl) ⟨1056878, by rfl⟩ : syracuseStep 1409171 = 2113757) B2113757
theorem B1409201 : Blo 936583 1409201 := bstep (se 2 (by rfl) ⟨528450, by rfl⟩ : syracuseStep 1409201 = 1056901) B1056901
theorem B1409219 : Blo 936583 1409219 := bstep (se 1 (by rfl) ⟨1056914, by rfl⟩ : syracuseStep 1409219 = 2113829) B2113829
theorem B1409249 : Blo 936583 1409249 := bstep (se 2 (by rfl) ⟨528468, by rfl⟩ : syracuseStep 1409249 = 1056937) B1056937
theorem B1409267 : Blo 936583 1409267 := bstep (se 1 (by rfl) ⟨1056950, by rfl⟩ : syracuseStep 1409267 = 2113901) B2113901
theorem B1409297 : Blo 936583 1409297 := bstep (se 2 (by rfl) ⟨528486, by rfl⟩ : syracuseStep 1409297 = 1056973) B1056973
theorem B1409315 : Blo 936583 1409315 := bstep (se 1 (by rfl) ⟨1056986, by rfl⟩ : syracuseStep 1409315 = 2113973) B2113973
theorem B1409345 : Blo 936583 1409345 := bstep (se 2 (by rfl) ⟨528504, by rfl⟩ : syracuseStep 1409345 = 1057009) B1057009
theorem B1409363 : Blo 936583 1409363 := bstep (se 1 (by rfl) ⟨1057022, by rfl⟩ : syracuseStep 1409363 = 2114045) B2114045
theorem B8552803 : Blo 936583 8552803 := bstep (se 1 (by rfl) ⟨6414602, by rfl⟩ : syracuseStep 8552803 = 12829205) B12829205
theorem B1409393 : Blo 936583 1409393 := bstep (se 2 (by rfl) ⟨528522, by rfl⟩ : syracuseStep 1409393 = 1057045) B1057045
theorem B1409411 : Blo 936583 1409411 := bstep (se 1 (by rfl) ⟨1057058, by rfl⟩ : syracuseStep 1409411 = 2114117) B2114117
theorem B10682765 : Blo 936583 10682765 := bstep (se 3 (by rfl) ⟨2003018, by rfl⟩ : syracuseStep 10682765 = 4006037) B4006037
theorem B1409441 : Blo 936583 1409441 := bstep (se 2 (by rfl) ⟨528540, by rfl⟩ : syracuseStep 1409441 = 1057081) B1057081
theorem B1409459 : Blo 936583 1409459 := bstep (se 1 (by rfl) ⟨1057094, by rfl⟩ : syracuseStep 1409459 = 2114189) B2114189
theorem B1409489 : Blo 936583 1409489 := bstep (se 2 (by rfl) ⟨528558, by rfl⟩ : syracuseStep 1409489 = 1057117) B1057117
theorem B1409507 : Blo 936583 1409507 := bstep (se 1 (by rfl) ⟨1057130, by rfl⟩ : syracuseStep 1409507 = 2114261) B2114261
theorem B1409537 : Blo 936583 1409537 := bstep (se 2 (by rfl) ⟨528576, by rfl⟩ : syracuseStep 1409537 = 1057153) B1057153
theorem B1409555 : Blo 936583 1409555 := bstep (se 1 (by rfl) ⟨1057166, by rfl⟩ : syracuseStep 1409555 = 2114333) B2114333
theorem B1409585 : Blo 936583 1409585 := bstep (se 2 (by rfl) ⟨528594, by rfl⟩ : syracuseStep 1409585 = 1057189) B1057189
theorem B1606195 : Blo 936583 1606195 := bstep (se 1 (by rfl) ⟨1204646, by rfl⟩ : syracuseStep 1606195 = 2409293) B2409293
theorem B1409603 : Blo 936583 1409603 := bstep (se 1 (by rfl) ⟨1057202, by rfl⟩ : syracuseStep 1409603 = 2114405) B2114405
theorem B1409633 : Blo 936583 1409633 := bstep (se 2 (by rfl) ⟨528612, by rfl⟩ : syracuseStep 1409633 = 1057225) B1057225
theorem B1409651 : Blo 936583 1409651 := bstep (se 1 (by rfl) ⟨1057238, by rfl⟩ : syracuseStep 1409651 = 2114477) B2114477
theorem B1409681 : Blo 936583 1409681 := bstep (se 2 (by rfl) ⟨528630, by rfl⟩ : syracuseStep 1409681 = 1057261) B1057261
theorem B1409699 : Blo 936583 1409699 := bstep (se 1 (by rfl) ⟨1057274, by rfl⟩ : syracuseStep 1409699 = 2114549) B2114549
theorem B1409729 : Blo 936583 1409729 := bstep (se 2 (by rfl) ⟨528648, by rfl⟩ : syracuseStep 1409729 = 1057297) B1057297
theorem B1409747 : Blo 936583 1409747 := bstep (se 1 (by rfl) ⟨1057310, by rfl⟩ : syracuseStep 1409747 = 2114621) B2114621
theorem B3375857 : Blo 936583 3375857 := bstep (se 2 (by rfl) ⟨1265946, by rfl⟩ : syracuseStep 3375857 = 2531893) B2531893
theorem B1409777 : Blo 936583 1409777 := bstep (se 2 (by rfl) ⟨528666, by rfl⟩ : syracuseStep 1409777 = 1057333) B1057333
theorem B1409795 : Blo 936583 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B1409825 : Blo 936583 1409825 := bstep (se 2 (by rfl) ⟨528684, by rfl⟩ : syracuseStep 1409825 = 1057369) B1057369
theorem B1409843 : Blo 936583 1409843 := bstep (se 1 (by rfl) ⟨1057382, by rfl⟩ : syracuseStep 1409843 = 2114765) B2114765
theorem B5342021 : Blo 936583 5342021 := bstep (se 4 (by rfl) ⟨500814, by rfl⟩ : syracuseStep 5342021 = 1001629) B1001629
theorem B1409873 : Blo 936583 1409873 := bstep (se 2 (by rfl) ⟨528702, by rfl⟩ : syracuseStep 1409873 = 1057405) B1057405
theorem B1409891 : Blo 936583 1409891 := bstep (se 1 (by rfl) ⟨1057418, by rfl⟩ : syracuseStep 1409891 = 2114837) B2114837
theorem B1409921 : Blo 936583 1409921 := bstep (se 2 (by rfl) ⟨528720, by rfl⟩ : syracuseStep 1409921 = 1057441) B1057441
theorem B4752269 : Blo 936583 4752269 := bstep (se 3 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 4752269 = 1782101) B1782101
theorem B1409939 : Blo 936583 1409939 := bstep (se 1 (by rfl) ⟨1057454, by rfl⟩ : syracuseStep 1409939 = 2114909) B2114909
theorem B1409969 : Blo 936583 1409969 := bstep (se 2 (by rfl) ⟨528738, by rfl⟩ : syracuseStep 1409969 = 1057477) B1057477
theorem B1409987 : Blo 936583 1409987 := bstep (se 1 (by rfl) ⟨1057490, by rfl⟩ : syracuseStep 1409987 = 2114981) B2114981
theorem B1410017 : Blo 936583 1410017 := bstep (se 2 (by rfl) ⟨528756, by rfl⟩ : syracuseStep 1410017 = 1057513) B1057513
theorem B1410035 : Blo 936583 1410035 := bstep (se 1 (by rfl) ⟨1057526, by rfl⟩ : syracuseStep 1410035 = 2115053) B2115053
theorem B1410065 : Blo 936583 1410065 := bstep (se 2 (by rfl) ⟨528774, by rfl⟩ : syracuseStep 1410065 = 1057549) B1057549
theorem B1410083 : Blo 936583 1410083 := bstep (se 1 (by rfl) ⟨1057562, by rfl⟩ : syracuseStep 1410083 = 2115125) B2115125
theorem B1410113 : Blo 936583 1410113 := bstep (se 2 (by rfl) ⟨528792, by rfl⟩ : syracuseStep 1410113 = 1057585) B1057585
theorem B3376205 : Blo 936583 3376205 := bstep (se 3 (by rfl) ⟨633038, by rfl⟩ : syracuseStep 3376205 = 1266077) B1266077
theorem B1410131 : Blo 936583 1410131 := bstep (se 1 (by rfl) ⟨1057598, by rfl⟩ : syracuseStep 1410131 = 2115197) B2115197
theorem B1410161 : Blo 936583 1410161 := bstep (se 2 (by rfl) ⟨528810, by rfl⟩ : syracuseStep 1410161 = 1057621) B1057621
theorem B1410179 : Blo 936583 1410179 := bstep (se 1 (by rfl) ⟨1057634, by rfl⟩ : syracuseStep 1410179 = 2115269) B2115269
theorem B1410209 : Blo 936583 1410209 := bstep (se 2 (by rfl) ⟨528828, by rfl⟩ : syracuseStep 1410209 = 1057657) B1057657
theorem B1410227 : Blo 936583 1410227 := bstep (se 1 (by rfl) ⟨1057670, by rfl⟩ : syracuseStep 1410227 = 2115341) B2115341
theorem B1410257 : Blo 936583 1410257 := bstep (se 2 (by rfl) ⟨528846, by rfl⟩ : syracuseStep 1410257 = 1057693) B1057693
theorem B1803491 : Blo 936583 1803491 := bstep (se 1 (by rfl) ⟨1352618, by rfl⟩ : syracuseStep 1803491 = 2705237) B2705237
theorem B1410275 : Blo 936583 1410275 := bstep (se 1 (by rfl) ⟨1057706, by rfl⟩ : syracuseStep 1410275 = 2115413) B2115413
theorem B2852081 : Blo 936583 2852081 := bstep (se 2 (by rfl) ⟨1069530, by rfl⟩ : syracuseStep 2852081 = 2139061) B2139061
theorem B1410305 : Blo 936583 1410305 := bstep (se 2 (by rfl) ⟨528864, by rfl⟩ : syracuseStep 1410305 = 1057729) B1057729
theorem B7603469 : Blo 936583 7603469 := bstep (se 3 (by rfl) ⟨1425650, by rfl⟩ : syracuseStep 7603469 = 2851301) B2851301
theorem B1410323 : Blo 936583 1410323 := bstep (se 1 (by rfl) ⟨1057742, by rfl⟩ : syracuseStep 1410323 = 2115485) B2115485
theorem B1410353 : Blo 936583 1410353 := bstep (se 2 (by rfl) ⟨528882, by rfl⟩ : syracuseStep 1410353 = 1057765) B1057765
theorem B1410371 : Blo 936583 1410371 := bstep (se 1 (by rfl) ⟨1057778, by rfl⟩ : syracuseStep 1410371 = 2115557) B2115557
theorem B1410401 : Blo 936583 1410401 := bstep (se 2 (by rfl) ⟨528900, by rfl⟩ : syracuseStep 1410401 = 1057801) B1057801
theorem B6423907 : Blo 936583 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B1410419 : Blo 936583 1410419 := bstep (se 1 (by rfl) ⟨1057814, by rfl⟩ : syracuseStep 1410419 = 2115629) B2115629
theorem B1410449 : Blo 936583 1410449 := bstep (se 2 (by rfl) ⟨528918, by rfl⟩ : syracuseStep 1410449 = 1057837) B1057837
theorem B1410467 : Blo 936583 1410467 := bstep (se 1 (by rfl) ⟨1057850, by rfl⟩ : syracuseStep 1410467 = 2115701) B2115701
theorem B1410497 : Blo 936583 1410497 := bstep (se 2 (by rfl) ⟨528936, by rfl⟩ : syracuseStep 1410497 = 1057873) B1057873
theorem B1410515 : Blo 936583 1410515 := bstep (se 1 (by rfl) ⟨1057886, by rfl⟩ : syracuseStep 1410515 = 2115773) B2115773
theorem B5342705 : Blo 936583 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B1410545 : Blo 936583 1410545 := bstep (se 2 (by rfl) ⟨528954, by rfl⟩ : syracuseStep 1410545 = 1057909) B1057909
theorem B1410563 : Blo 936583 1410563 := bstep (se 1 (by rfl) ⟨1057922, by rfl⟩ : syracuseStep 1410563 = 2115845) B2115845
theorem B1410593 : Blo 936583 1410593 := bstep (se 2 (by rfl) ⟨528972, by rfl⟩ : syracuseStep 1410593 = 1057945) B1057945
theorem B1410611 : Blo 936583 1410611 := bstep (se 1 (by rfl) ⟨1057958, by rfl⟩ : syracuseStep 1410611 = 2115917) B2115917
theorem B1410641 : Blo 936583 1410641 := bstep (se 2 (by rfl) ⟨528990, by rfl⟩ : syracuseStep 1410641 = 1057981) B1057981
theorem B1410659 : Blo 936583 1410659 := bstep (se 1 (by rfl) ⟨1057994, by rfl⟩ : syracuseStep 1410659 = 2115989) B2115989
theorem B1410689 : Blo 936583 1410689 := bstep (se 2 (by rfl) ⟨529008, by rfl⟩ : syracuseStep 1410689 = 1058017) B1058017
theorem B1410707 : Blo 936583 1410707 := bstep (se 1 (by rfl) ⟨1058030, by rfl⟩ : syracuseStep 1410707 = 2116061) B2116061
theorem B5703331 : Blo 936583 5703331 := bstep (se 1 (by rfl) ⟨4277498, by rfl⟩ : syracuseStep 5703331 = 8554997) B8554997
theorem B1410737 : Blo 936583 1410737 := bstep (se 2 (by rfl) ⟨529026, by rfl⟩ : syracuseStep 1410737 = 1058053) B1058053
theorem B1410755 : Blo 936583 1410755 := bstep (se 1 (by rfl) ⟨1058066, by rfl⟩ : syracuseStep 1410755 = 2116133) B2116133
theorem B1410785 : Blo 936583 1410785 := bstep (se 2 (by rfl) ⟨529044, by rfl⟩ : syracuseStep 1410785 = 1058089) B1058089
theorem B1410803 : Blo 936583 1410803 := bstep (se 1 (by rfl) ⟨1058102, by rfl⟩ : syracuseStep 1410803 = 2116205) B2116205
theorem B1410833 : Blo 936583 1410833 := bstep (se 2 (by rfl) ⟨529062, by rfl⟩ : syracuseStep 1410833 = 1058125) B1058125
theorem B1410851 : Blo 936583 1410851 := bstep (se 1 (by rfl) ⟨1058138, by rfl⟩ : syracuseStep 1410851 = 2116277) B2116277
theorem B5409251 : Blo 936583 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B8129009 : Blo 936583 8129009 := bstep (se 2 (by rfl) ⟨3048378, by rfl⟩ : syracuseStep 8129009 = 6096757) B6096757
theorem B1804817 : Blo 936583 1804817 := bstep (se 2 (by rfl) ⟨676806, by rfl⟩ : syracuseStep 1804817 = 1353613) B1353613
theorem B3213923 : Blo 936583 3213923 := bstep (se 1 (by rfl) ⟨2410442, by rfl⟩ : syracuseStep 3213923 = 4820885) B4820885
theorem B1903267 : Blo 936583 1903267 := bstep (se 1 (by rfl) ⟨1427450, by rfl⟩ : syracuseStep 1903267 = 2854901) B2854901
theorem B1608385 : Blo 936583 1608385 := bstep (se 2 (by rfl) ⟨603144, by rfl⟩ : syracuseStep 1608385 = 1206289) B1206289
theorem B1903331 : Blo 936583 1903331 := bstep (se 1 (by rfl) ⟨1427498, by rfl⟩ : syracuseStep 1903331 = 2854997) B2854997
theorem B3378019 : Blo 936583 3378019 := bstep (se 1 (by rfl) ⟨2533514, by rfl⟩ : syracuseStep 3378019 = 5067029) B5067029
theorem B5344163 : Blo 936583 5344163 := bstep (se 1 (by rfl) ⟨4008122, by rfl⟩ : syracuseStep 5344163 = 8016245) B8016245
theorem B2853805 : Blo 936583 2853805 := bstep (se 3 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 2853805 = 1070177) B1070177
theorem B2853901 : Blo 936583 2853901 := bstep (se 3 (by rfl) ⟨535106, by rfl⟩ : syracuseStep 2853901 = 1070213) B1070213
theorem B5409827 : Blo 936583 5409827 := bstep (se 1 (by rfl) ⟨4057370, by rfl⟩ : syracuseStep 5409827 = 8114741) B8114741
theorem B2002097 : Blo 936583 2002097 := bstep (se 2 (by rfl) ⟨750786, by rfl⟩ : syracuseStep 2002097 = 1501573) B1501573
theorem B10685681 : Blo 936583 10685681 := bstep (se 2 (by rfl) ⟨4007130, by rfl⟩ : syracuseStep 10685681 = 8014261) B8014261
theorem B3214691 : Blo 936583 3214691 := bstep (se 1 (by rfl) ⟨2411018, by rfl⟩ : syracuseStep 3214691 = 4822037) B4822037
theorem B8031757 : Blo 936583 8031757 := bstep (se 3 (by rfl) ⟨1505954, by rfl⟩ : syracuseStep 8031757 = 3011909) B3011909
theorem B1543747 : Blo 936583 1543747 := bstep (se 1 (by rfl) ⟨1157810, by rfl⟩ : syracuseStep 1543747 = 2315621) B2315621
theorem B1904305 : Blo 936583 1904305 := bstep (se 2 (by rfl) ⟨714114, by rfl⟩ : syracuseStep 1904305 = 1428229) B1428229
theorem B4755185 : Blo 936583 4755185 := bstep (se 2 (by rfl) ⟨1783194, by rfl⟩ : syracuseStep 4755185 = 3566389) B3566389
theorem B1904369 : Blo 936583 1904369 := bstep (se 2 (by rfl) ⟨714138, by rfl⟩ : syracuseStep 1904369 = 1428277) B1428277
theorem B6001037 : Blo 936583 6001037 := bstep (se 3 (by rfl) ⟨1125194, by rfl⟩ : syracuseStep 6001037 = 2250389) B2250389
theorem B2003395 : Blo 936583 2003395 := bstep (se 1 (by rfl) ⟨1502546, by rfl⟩ : syracuseStep 2003395 = 3005093) B3005093
theorem B6001265 : Blo 936583 6001265 := bstep (se 2 (by rfl) ⟨2250474, by rfl⟩ : syracuseStep 6001265 = 4500949) B4500949
theorem B8033093 : Blo 936583 8033093 := bstep (se 4 (by rfl) ⟨753102, by rfl⟩ : syracuseStep 8033093 = 1506205) B1506205
theorem B9769997 : Blo 936583 9769997 := bstep (se 3 (by rfl) ⟨1831874, by rfl⟩ : syracuseStep 9769997 = 3663749) B3663749
theorem B1053715 : Blo 936583 1053715 := bstep (se 1 (by rfl) ⟨790286, by rfl⟩ : syracuseStep 1053715 = 1580573) B1580573
theorem B4002929 : Blo 936583 4002929 := bstep (se 2 (by rfl) ⟨1501098, by rfl⟩ : syracuseStep 4002929 = 3002197) B3002197
theorem B9016433 : Blo 936583 9016433 := bstep (se 2 (by rfl) ⟨3381162, by rfl⟩ : syracuseStep 9016433 = 6762325) B6762325
theorem B48829553 : Blo 936583 48829553 := bstep (se 2 (by rfl) ⟨18311082, by rfl⟩ : syracuseStep 48829553 = 36622165) B36622165
theorem B1053859 : Blo 936583 1053859 := bstep (se 1 (by rfl) ⟨790394, by rfl⟩ : syracuseStep 1053859 = 1580789) B1580789
theorem B4756643 : Blo 936583 4756643 := bstep (se 1 (by rfl) ⟨3567482, by rfl⟩ : syracuseStep 4756643 = 7134965) B7134965
theorem B1054003 : Blo 936583 1054003 := bstep (se 1 (by rfl) ⟨790502, by rfl⟩ : syracuseStep 1054003 = 1581005) B1581005
theorem B2856323 : Blo 936583 2856323 := bstep (se 1 (by rfl) ⟨2142242, by rfl⟩ : syracuseStep 2856323 = 4284485) B4284485
theorem B1054147 : Blo 936583 1054147 := bstep (se 1 (by rfl) ⟨790610, by rfl⟩ : syracuseStep 1054147 = 1581221) B1581221
theorem B1054291 : Blo 936583 1054291 := bstep (se 1 (by rfl) ⟨790718, by rfl⟩ : syracuseStep 1054291 = 1581437) B1581437
theorem B2004625 : Blo 936583 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B1054435 : Blo 936583 1054435 := bstep (se 1 (by rfl) ⟨790826, by rfl⟩ : syracuseStep 1054435 = 1581653) B1581653
theorem B1054579 : Blo 936583 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B4757453 : Blo 936583 4757453 := bstep (se 3 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 4757453 = 1784045) B1784045
theorem B1185779 : Blo 936583 1185779 := bstep (se 1 (by rfl) ⟨889334, by rfl⟩ : syracuseStep 1185779 = 1778669) B1778669
theorem B1054723 : Blo 936583 1054723 := bstep (se 1 (by rfl) ⟨791042, by rfl⟩ : syracuseStep 1054723 = 1582085) B1582085
theorem B5347397 : Blo 936583 5347397 := bstep (se 4 (by rfl) ⟨501318, by rfl⟩ : syracuseStep 5347397 = 1002637) B1002637
theorem B1054867 : Blo 936583 1054867 := bstep (se 1 (by rfl) ⟨791150, by rfl⟩ : syracuseStep 1054867 = 1582301) B1582301
theorem B3217645 : Blo 936583 3217645 := bstep (se 3 (by rfl) ⟨603308, by rfl⟩ : syracuseStep 3217645 = 1206617) B1206617
theorem B1055011 : Blo 936583 1055011 := bstep (se 1 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 1055011 = 1582517) B1582517
theorem B3381581 : Blo 936583 3381581 := bstep (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) B1268093
theorem B2005411 : Blo 936583 2005411 := bstep (se 1 (by rfl) ⟨1504058, by rfl⟩ : syracuseStep 2005411 = 3008117) B3008117
theorem B1055155 : Blo 936583 1055155 := bstep (se 1 (by rfl) ⟨791366, by rfl⟩ : syracuseStep 1055155 = 1582733) B1582733
theorem B5347853 : Blo 936583 5347853 := bstep (se 3 (by rfl) ⟨1002722, by rfl⟩ : syracuseStep 5347853 = 2005445) B2005445
theorem B1055299 : Blo 936583 1055299 := bstep (se 1 (by rfl) ⟨791474, by rfl⟩ : syracuseStep 1055299 = 1582949) B1582949
theorem B3086957 : Blo 936583 3086957 := bstep (se 3 (by rfl) ⟨578804, by rfl⟩ : syracuseStep 3086957 = 1157609) B1157609
theorem B1186483 : Blo 936583 1186483 := bstep (se 1 (by rfl) ⟨889862, by rfl⟩ : syracuseStep 1186483 = 1779725) B1779725
theorem B1055443 : Blo 936583 1055443 := bstep (se 1 (by rfl) ⟨791582, by rfl⟩ : syracuseStep 1055443 = 1583165) B1583165
theorem B1186579 : Blo 936583 1186579 := bstep (se 1 (by rfl) ⟨889934, by rfl⟩ : syracuseStep 1186579 = 1779869) B1779869
theorem B1055587 : Blo 936583 1055587 := bstep (se 1 (by rfl) ⟨791690, by rfl⟩ : syracuseStep 1055587 = 1583381) B1583381
theorem B1055731 : Blo 936583 1055731 := bstep (se 1 (by rfl) ⟨791798, by rfl⟩ : syracuseStep 1055731 = 1583597) B1583597
theorem B2006129 : Blo 936583 2006129 := bstep (se 2 (by rfl) ⟨752298, by rfl⟩ : syracuseStep 2006129 = 1504597) B1504597
theorem B1055875 : Blo 936583 1055875 := bstep (se 1 (by rfl) ⟨791906, by rfl⟩ : syracuseStep 1055875 = 1583813) B1583813
theorem B1187075 : Blo 936583 1187075 := bstep (se 1 (by rfl) ⟨890306, by rfl⟩ : syracuseStep 1187075 = 1780613) B1780613
theorem B1056019 : Blo 936583 1056019 := bstep (se 1 (by rfl) ⟨792014, by rfl⟩ : syracuseStep 1056019 = 1584029) B1584029
theorem B1711441 : Blo 936583 1711441 := bstep (se 2 (by rfl) ⟨641790, by rfl⟩ : syracuseStep 1711441 = 1283581) B1283581
theorem B1056163 : Blo 936583 1056163 := bstep (se 1 (by rfl) ⟨792122, by rfl⟩ : syracuseStep 1056163 = 1584245) B1584245
theorem B4005389 : Blo 936583 4005389 := bstep (se 3 (by rfl) ⟨751010, by rfl⟩ : syracuseStep 4005389 = 1502021) B1502021
theorem B1580593 : Blo 936583 1580593 := bstep (se 2 (by rfl) ⟨592722, by rfl⟩ : syracuseStep 1580593 = 1185445) B1185445
theorem B1056307 : Blo 936583 1056307 := bstep (se 1 (by rfl) ⟨792230, by rfl⟩ : syracuseStep 1056307 = 1584461) B1584461
theorem B1580627 : Blo 936583 1580627 := bstep (se 1 (by rfl) ⟨1185470, by rfl⟩ : syracuseStep 1580627 = 2370941) B2370941
theorem B2006641 : Blo 936583 2006641 := bstep (se 2 (by rfl) ⟨752490, by rfl⟩ : syracuseStep 2006641 = 1504981) B1504981
theorem B2137745 : Blo 936583 2137745 := bstep (se 2 (by rfl) ⟨801654, by rfl⟩ : syracuseStep 2137745 = 1603309) B1603309
theorem B1056451 : Blo 936583 1056451 := bstep (se 1 (by rfl) ⟨792338, by rfl⟩ : syracuseStep 1056451 = 1584677) B1584677
theorem B1580755 : Blo 936583 1580755 := bstep (se 1 (by rfl) ⟨1185566, by rfl⟩ : syracuseStep 1580755 = 2371133) B2371133
theorem B2137873 : Blo 936583 2137873 := bstep (se 2 (by rfl) ⟨801702, by rfl⟩ : syracuseStep 2137873 = 1603405) B1603405
theorem B1056595 : Blo 936583 1056595 := bstep (se 1 (by rfl) ⟨792446, by rfl⟩ : syracuseStep 1056595 = 1584893) B1584893
theorem B1580897 : Blo 936583 1580897 := bstep (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) B1185673
theorem B3383153 : Blo 936583 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B2858915 : Blo 936583 2858915 := bstep (se 1 (by rfl) ⟨2144186, by rfl⟩ : syracuseStep 2858915 = 4288373) B4288373
theorem B1187779 : Blo 936583 1187779 := bstep (se 1 (by rfl) ⟨890834, by rfl⟩ : syracuseStep 1187779 = 1781669) B1781669
theorem B1581025 : Blo 936583 1581025 := bstep (se 2 (by rfl) ⟨592884, by rfl⟩ : syracuseStep 1581025 = 1185769) B1185769
theorem B1056739 : Blo 936583 1056739 := bstep (se 1 (by rfl) ⟨792554, by rfl⟩ : syracuseStep 1056739 = 1585109) B1585109
theorem B1581059 : Blo 936583 1581059 := bstep (se 1 (by rfl) ⟨1185794, by rfl⟩ : syracuseStep 1581059 = 2371589) B2371589
theorem B1187875 : Blo 936583 1187875 := bstep (se 1 (by rfl) ⟨890906, by rfl⟩ : syracuseStep 1187875 = 1781813) B1781813
theorem B1056883 : Blo 936583 1056883 := bstep (se 1 (by rfl) ⟨792662, by rfl⟩ : syracuseStep 1056883 = 1585325) B1585325
theorem B1581187 : Blo 936583 1581187 := bstep (se 1 (by rfl) ⟨1185890, by rfl⟩ : syracuseStep 1581187 = 2371781) B2371781
theorem B1057027 : Blo 936583 1057027 := bstep (se 1 (by rfl) ⟨792770, by rfl⟩ : syracuseStep 1057027 = 1585541) B1585541
theorem B3809549 : Blo 936583 3809549 := bstep (se 3 (by rfl) ⟨714290, by rfl⟩ : syracuseStep 3809549 = 1428581) B1428581
theorem B1581329 : Blo 936583 1581329 := bstep (se 2 (by rfl) ⟨592998, by rfl⟩ : syracuseStep 1581329 = 1185997) B1185997
theorem B1581457 : Blo 936583 1581457 := bstep (se 2 (by rfl) ⟨593046, by rfl⟩ : syracuseStep 1581457 = 1186093) B1186093
theorem B1057171 : Blo 936583 1057171 := bstep (se 1 (by rfl) ⟨792878, by rfl⟩ : syracuseStep 1057171 = 1585757) B1585757
theorem B1581491 : Blo 936583 1581491 := bstep (se 1 (by rfl) ⟨1186118, by rfl⟩ : syracuseStep 1581491 = 2372237) B2372237
theorem B1188371 : Blo 936583 1188371 := bstep (se 1 (by rfl) ⟨891278, by rfl⟩ : syracuseStep 1188371 = 1782557) B1782557
theorem B1057315 : Blo 936583 1057315 := bstep (se 1 (by rfl) ⟨792986, by rfl⟩ : syracuseStep 1057315 = 1585973) B1585973
theorem B1581619 : Blo 936583 1581619 := bstep (se 1 (by rfl) ⟨1186214, by rfl⟩ : syracuseStep 1581619 = 2372429) B2372429
theorem B1057459 : Blo 936583 1057459 := bstep (se 1 (by rfl) ⟨793094, by rfl⟩ : syracuseStep 1057459 = 1586189) B1586189
theorem B1581761 : Blo 936583 1581761 := bstep (se 2 (by rfl) ⟨593160, by rfl⟩ : syracuseStep 1581761 = 1186321) B1186321
theorem B1778449 : Blo 936583 1778449 := bstep (se 2 (by rfl) ⟨666918, by rfl⟩ : syracuseStep 1778449 = 1333837) B1333837
theorem B2532131 : Blo 936583 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B4006705 : Blo 936583 4006705 := bstep (se 2 (by rfl) ⟨1502514, by rfl⟩ : syracuseStep 4006705 = 3005029) B3005029
theorem B4760369 : Blo 936583 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B1581889 : Blo 936583 1581889 := bstep (se 2 (by rfl) ⟨593208, by rfl⟩ : syracuseStep 1581889 = 1186417) B1186417
theorem B1057603 : Blo 936583 1057603 := bstep (se 1 (by rfl) ⟨793202, by rfl⟩ : syracuseStep 1057603 = 1586405) B1586405
theorem B1581923 : Blo 936583 1581923 := bstep (se 1 (by rfl) ⟨1186442, by rfl⟩ : syracuseStep 1581923 = 2372885) B2372885
theorem B1057747 : Blo 936583 1057747 := bstep (se 1 (by rfl) ⟨793310, by rfl⟩ : syracuseStep 1057747 = 1586621) B1586621
theorem B1582051 : Blo 936583 1582051 := bstep (se 1 (by rfl) ⟨1186538, by rfl⟩ : syracuseStep 1582051 = 2373077) B2373077
theorem B2008145 : Blo 936583 2008145 := bstep (se 2 (by rfl) ⟨753054, by rfl⟩ : syracuseStep 2008145 = 1506109) B1506109
theorem B1057891 : Blo 936583 1057891 := bstep (se 1 (by rfl) ⟨793418, by rfl⟩ : syracuseStep 1057891 = 1586837) B1586837
theorem B1582193 : Blo 936583 1582193 := bstep (se 2 (by rfl) ⟨593322, by rfl⟩ : syracuseStep 1582193 = 1186645) B1186645
theorem B1778851 : Blo 936583 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B1778897 : Blo 936583 1778897 := bstep (se 2 (by rfl) ⟨667086, by rfl⟩ : syracuseStep 1778897 = 1334173) B1334173
theorem B1189075 : Blo 936583 1189075 := bstep (se 1 (by rfl) ⟨891806, by rfl⟩ : syracuseStep 1189075 = 1783613) B1783613
theorem B1582321 : Blo 936583 1582321 := bstep (se 2 (by rfl) ⟨593370, by rfl⟩ : syracuseStep 1582321 = 1186741) B1186741
theorem B5711089 : Blo 936583 5711089 := bstep (se 2 (by rfl) ⟨2141658, by rfl⟩ : syracuseStep 5711089 = 4283317) B4283317
theorem B1058035 : Blo 936583 1058035 := bstep (se 1 (by rfl) ⟨793526, by rfl⟩ : syracuseStep 1058035 = 1587053) B1587053
theorem B1582355 : Blo 936583 1582355 := bstep (se 1 (by rfl) ⟨1186766, by rfl⟩ : syracuseStep 1582355 = 2373533) B2373533
theorem B1189171 : Blo 936583 1189171 := bstep (se 1 (by rfl) ⟨891878, by rfl⟩ : syracuseStep 1189171 = 1783757) B1783757
theorem B5350769 : Blo 936583 5350769 := bstep (se 2 (by rfl) ⟨2006538, by rfl⟩ : syracuseStep 5350769 = 4013077) B4013077
theorem B1582483 : Blo 936583 1582483 := bstep (se 1 (by rfl) ⟨1186862, by rfl⟩ : syracuseStep 1582483 = 2373725) B2373725
theorem B2008547 : Blo 936583 2008547 := bstep (se 1 (by rfl) ⟨1506410, by rfl⟩ : syracuseStep 2008547 = 3012821) B3012821
theorem B1779185 : Blo 936583 1779185 := bstep (se 2 (by rfl) ⟨667194, by rfl⟩ : syracuseStep 1779185 = 1334389) B1334389
theorem B1582625 : Blo 936583 1582625 := bstep (se 2 (by rfl) ⟨593484, by rfl⟩ : syracuseStep 1582625 = 1186969) B1186969
theorem B1582753 : Blo 936583 1582753 := bstep (se 2 (by rfl) ⟨593532, by rfl⟩ : syracuseStep 1582753 = 1187065) B1187065
theorem B1582787 : Blo 936583 1582787 := bstep (se 1 (by rfl) ⟨1187090, by rfl⟩ : syracuseStep 1582787 = 2374181) B2374181
theorem B1189667 : Blo 936583 1189667 := bstep (se 1 (by rfl) ⟨892250, by rfl⟩ : syracuseStep 1189667 = 1784501) B1784501
theorem B2533169 : Blo 936583 2533169 := bstep (se 2 (by rfl) ⟨949938, by rfl⟩ : syracuseStep 2533169 = 1899877) B1899877
theorem B1582915 : Blo 936583 1582915 := bstep (se 1 (by rfl) ⟨1187186, by rfl⟩ : syracuseStep 1582915 = 2374373) B2374373
theorem B3811171 : Blo 936583 3811171 := bstep (se 1 (by rfl) ⟨2858378, by rfl⟩ : syracuseStep 3811171 = 5716757) B5716757
theorem B15247217 : Blo 936583 15247217 := bstep (se 2 (by rfl) ⟨5717706, by rfl⟩ : syracuseStep 15247217 = 11435413) B11435413
theorem B2107313 : Blo 936583 2107313 := bstep (se 2 (by rfl) ⟨790242, by rfl⟩ : syracuseStep 2107313 = 1580485) B1580485
theorem B1484737 : Blo 936583 1484737 := bstep (se 2 (by rfl) ⟨556776, by rfl⟩ : syracuseStep 1484737 = 1113553) B1113553
theorem B2107331 : Blo 936583 2107331 := bstep (se 1 (by rfl) ⟨1580498, by rfl⟩ : syracuseStep 2107331 = 3160997) B3160997
theorem B1583057 : Blo 936583 1583057 := bstep (se 2 (by rfl) ⟨593646, by rfl⟩ : syracuseStep 1583057 = 1187293) B1187293
theorem B1583185 : Blo 936583 1583185 := bstep (se 2 (by rfl) ⟨593694, by rfl⟩ : syracuseStep 1583185 = 1187389) B1187389
theorem B1583219 : Blo 936583 1583219 := bstep (se 1 (by rfl) ⟨1187414, by rfl⟩ : syracuseStep 1583219 = 2374829) B2374829
theorem B9021581 : Blo 936583 9021581 := bstep (se 3 (by rfl) ⟨1691546, by rfl⟩ : syracuseStep 9021581 = 3383093) B3383093
theorem B1779907 : Blo 936583 1779907 := bstep (se 1 (by rfl) ⟨1334930, by rfl⟩ : syracuseStep 1779907 = 2669861) B2669861
theorem B2107601 : Blo 936583 2107601 := bstep (se 2 (by rfl) ⟨790350, by rfl⟩ : syracuseStep 2107601 = 1580701) B1580701
theorem B2107619 : Blo 936583 2107619 := bstep (se 1 (by rfl) ⟨1580714, by rfl⟩ : syracuseStep 2107619 = 3161429) B3161429
theorem B1583347 : Blo 936583 1583347 := bstep (se 1 (by rfl) ⟨1187510, by rfl⟩ : syracuseStep 1583347 = 2375021) B2375021
theorem B1583489 : Blo 936583 1583489 := bstep (se 2 (by rfl) ⟨593808, by rfl⟩ : syracuseStep 1583489 = 1187617) B1187617
theorem B1190371 : Blo 936583 1190371 := bstep (se 1 (by rfl) ⟨892778, by rfl⟩ : syracuseStep 1190371 = 1785557) B1785557
theorem B2107889 : Blo 936583 2107889 := bstep (se 2 (by rfl) ⟨790458, by rfl⟩ : syracuseStep 2107889 = 1580917) B1580917
theorem B1583617 : Blo 936583 1583617 := bstep (se 2 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 1583617 = 1187713) B1187713
theorem B2107907 : Blo 936583 2107907 := bstep (se 1 (by rfl) ⟨1580930, by rfl⟩ : syracuseStep 2107907 = 3161861) B3161861
theorem B3811853 : Blo 936583 3811853 := bstep (se 3 (by rfl) ⟨714722, by rfl⟩ : syracuseStep 3811853 = 1429445) B1429445
theorem B1583651 : Blo 936583 1583651 := bstep (se 1 (by rfl) ⟨1187738, by rfl⟩ : syracuseStep 1583651 = 2375477) B2375477
theorem B1780355 : Blo 936583 1780355 := bstep (se 1 (by rfl) ⟨1335266, by rfl⟩ : syracuseStep 1780355 = 2670533) B2670533
theorem B2534033 : Blo 936583 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B1583779 : Blo 936583 1583779 := bstep (se 1 (by rfl) ⟨1187834, by rfl⟩ : syracuseStep 1583779 = 2375669) B2375669
theorem B2108177 : Blo 936583 2108177 := bstep (se 2 (by rfl) ⟨790566, by rfl⟩ : syracuseStep 2108177 = 1581133) B1581133
theorem B5352227 : Blo 936583 5352227 := bstep (se 1 (by rfl) ⟨4014170, by rfl⟩ : syracuseStep 5352227 = 8028341) B8028341
theorem B2108195 : Blo 936583 2108195 := bstep (se 1 (by rfl) ⟨1581146, by rfl⟩ : syracuseStep 2108195 = 3162293) B3162293
theorem B1354531 : Blo 936583 1354531 := bstep (se 1 (by rfl) ⟨1015898, by rfl⟩ : syracuseStep 1354531 = 2031797) B2031797
theorem B1583921 : Blo 936583 1583921 := bstep (se 2 (by rfl) ⟨593970, by rfl⟩ : syracuseStep 1583921 = 1187941) B1187941
theorem B6007621 : Blo 936583 6007621 := bstep (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) B1126429
theorem B1780643 : Blo 936583 1780643 := bstep (se 1 (by rfl) ⟨1335482, by rfl⟩ : syracuseStep 1780643 = 2670965) B2670965
theorem B1584049 : Blo 936583 1584049 := bstep (se 2 (by rfl) ⟨594018, by rfl⟩ : syracuseStep 1584049 = 1188037) B1188037
theorem B1584083 : Blo 936583 1584083 := bstep (se 1 (by rfl) ⟨1188062, by rfl⟩ : syracuseStep 1584083 = 2376125) B2376125
theorem B2108465 : Blo 936583 2108465 := bstep (se 2 (by rfl) ⟨790674, by rfl⟩ : syracuseStep 2108465 = 1581349) B1581349
theorem B2108483 : Blo 936583 2108483 := bstep (se 1 (by rfl) ⟨1581362, by rfl⟩ : syracuseStep 2108483 = 3162725) B3162725
theorem B1584211 : Blo 936583 1584211 := bstep (se 1 (by rfl) ⟨1188158, by rfl⟩ : syracuseStep 1584211 = 2376317) B2376317
theorem B1584353 : Blo 936583 1584353 := bstep (se 2 (by rfl) ⟨594132, by rfl⟩ : syracuseStep 1584353 = 1188265) B1188265
theorem B2108753 : Blo 936583 2108753 := bstep (se 2 (by rfl) ⟨790782, by rfl⟩ : syracuseStep 2108753 = 1581565) B1581565
theorem B1584481 : Blo 936583 1584481 := bstep (se 2 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 1584481 = 1188361) B1188361
theorem B2108771 : Blo 936583 2108771 := bstep (se 1 (by rfl) ⟨1581578, by rfl⟩ : syracuseStep 2108771 = 3163157) B3163157
theorem B1584515 : Blo 936583 1584515 := bstep (se 1 (by rfl) ⟨1188386, by rfl⟩ : syracuseStep 1584515 = 2376773) B2376773
theorem B1584643 : Blo 936583 1584643 := bstep (se 1 (by rfl) ⟨1188482, by rfl⟩ : syracuseStep 1584643 = 2376965) B2376965
theorem B3386929 : Blo 936583 3386929 := bstep (se 2 (by rfl) ⟨1270098, by rfl⟩ : syracuseStep 3386929 = 2540197) B2540197
theorem B2371153 : Blo 936583 2371153 := bstep (se 2 (by rfl) ⟨889182, by rfl⟩ : syracuseStep 2371153 = 1778365) B1778365
theorem B2109041 : Blo 936583 2109041 := bstep (se 2 (by rfl) ⟨790890, by rfl⟩ : syracuseStep 2109041 = 1581781) B1581781
theorem B2109059 : Blo 936583 2109059 := bstep (se 1 (by rfl) ⟨1581794, by rfl⟩ : syracuseStep 2109059 = 3163589) B3163589
theorem B1584785 : Blo 936583 1584785 := bstep (se 2 (by rfl) ⟨594294, by rfl⟩ : syracuseStep 1584785 = 1188589) B1188589
theorem B1355459 : Blo 936583 1355459 := bstep (se 1 (by rfl) ⟨1016594, by rfl⟩ : syracuseStep 1355459 = 2033189) B2033189
theorem B8367857 : Blo 936583 8367857 := bstep (se 2 (by rfl) ⟨3137946, by rfl⟩ : syracuseStep 8367857 = 6275893) B6275893
theorem B5353229 : Blo 936583 5353229 := bstep (se 3 (by rfl) ⟨1003730, by rfl⟩ : syracuseStep 5353229 = 2007461) B2007461
theorem B1584913 : Blo 936583 1584913 := bstep (se 2 (by rfl) ⟨594342, by rfl⟩ : syracuseStep 1584913 = 1188685) B1188685
theorem B4009763 : Blo 936583 4009763 := bstep (se 1 (by rfl) ⟨3007322, by rfl⟩ : syracuseStep 4009763 = 6014645) B6014645
theorem B1584947 : Blo 936583 1584947 := bstep (se 1 (by rfl) ⟨1188710, by rfl⟩ : syracuseStep 1584947 = 2377421) B2377421
theorem B2535245 : Blo 936583 2535245 := bstep (se 3 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 2535245 = 950717) B950717
theorem B1781585 : Blo 936583 1781585 := bstep (se 2 (by rfl) ⟨668094, by rfl⟩ : syracuseStep 1781585 = 1336189) B1336189
theorem B2371427 : Blo 936583 2371427 := bstep (se 1 (by rfl) ⟨1778570, by rfl⟩ : syracuseStep 2371427 = 3557141) B3557141
theorem B2109329 : Blo 936583 2109329 := bstep (se 2 (by rfl) ⟨790998, by rfl⟩ : syracuseStep 2109329 = 1581997) B1581997
theorem B2109347 : Blo 936583 2109347 := bstep (se 1 (by rfl) ⟨1582010, by rfl⟩ : syracuseStep 2109347 = 3164021) B3164021
theorem B1585075 : Blo 936583 1585075 := bstep (se 1 (by rfl) ⟨1188806, by rfl⟩ : syracuseStep 1585075 = 2377613) B2377613
theorem B2142179 : Blo 936583 2142179 := bstep (se 1 (by rfl) ⟨1606634, by rfl⟩ : syracuseStep 2142179 = 3213269) B3213269
theorem B2371619 : Blo 936583 2371619 := bstep (se 1 (by rfl) ⟨1778714, by rfl⟩ : syracuseStep 2371619 = 3557429) B3557429
theorem B1585217 : Blo 936583 1585217 := bstep (se 2 (by rfl) ⟨594456, by rfl⟩ : syracuseStep 1585217 = 1188913) B1188913
theorem B2109617 : Blo 936583 2109617 := bstep (se 2 (by rfl) ⟨791106, by rfl⟩ : syracuseStep 2109617 = 1582213) B1582213
theorem B1585345 : Blo 936583 1585345 := bstep (se 2 (by rfl) ⟨594504, by rfl⟩ : syracuseStep 1585345 = 1189009) B1189009
theorem B2109635 : Blo 936583 2109635 := bstep (se 1 (by rfl) ⟨1582226, by rfl⟩ : syracuseStep 2109635 = 3164453) B3164453
theorem B1585379 : Blo 936583 1585379 := bstep (se 1 (by rfl) ⟨1189034, by rfl⟩ : syracuseStep 1585379 = 2378069) B2378069
theorem B1585507 : Blo 936583 1585507 := bstep (se 1 (by rfl) ⟨1189130, by rfl⟩ : syracuseStep 1585507 = 2378261) B2378261
theorem B2109905 : Blo 936583 2109905 := bstep (se 2 (by rfl) ⟨791214, by rfl⟩ : syracuseStep 2109905 = 1582429) B1582429
theorem B2109923 : Blo 936583 2109923 := bstep (se 1 (by rfl) ⟨1582442, by rfl⟩ : syracuseStep 2109923 = 3164885) B3164885
theorem B1585649 : Blo 936583 1585649 := bstep (se 2 (by rfl) ⟨594618, by rfl⟩ : syracuseStep 1585649 = 1189237) B1189237
theorem B20263445 : Blo 936583 20263445 := bstep (se 6 (by rfl) ⟨474924, by rfl⟩ : syracuseStep 20263445 = 949849) B949849
theorem B1126963 : Blo 936583 1126963 := bstep (se 1 (by rfl) ⟨845222, by rfl⟩ : syracuseStep 1126963 = 1690445) B1690445
theorem B1585777 : Blo 936583 1585777 := bstep (se 2 (by rfl) ⟨594666, by rfl⟩ : syracuseStep 1585777 = 1189333) B1189333
theorem B1585811 : Blo 936583 1585811 := bstep (se 1 (by rfl) ⟨1189358, by rfl⟩ : syracuseStep 1585811 = 2378717) B2378717
theorem B4502179 : Blo 936583 4502179 := bstep (se 1 (by rfl) ⟨3376634, by rfl⟩ : syracuseStep 4502179 = 6753269) B6753269
theorem B1782481 : Blo 936583 1782481 := bstep (se 2 (by rfl) ⟨668430, by rfl⟩ : syracuseStep 1782481 = 1336861) B1336861
theorem B2110193 : Blo 936583 2110193 := bstep (se 2 (by rfl) ⟨791322, by rfl⟩ : syracuseStep 2110193 = 1582645) B1582645
theorem B2110211 : Blo 936583 2110211 := bstep (se 1 (by rfl) ⟨1582658, by rfl⟩ : syracuseStep 2110211 = 3165317) B3165317
theorem B1585939 : Blo 936583 1585939 := bstep (se 1 (by rfl) ⟨1189454, by rfl⟩ : syracuseStep 1585939 = 2378909) B2378909
theorem B1782641 : Blo 936583 1782641 := bstep (se 2 (by rfl) ⟨668490, by rfl⟩ : syracuseStep 1782641 = 1336981) B1336981
theorem B1586081 : Blo 936583 1586081 := bstep (se 2 (by rfl) ⟨594780, by rfl⟩ : syracuseStep 1586081 = 1189561) B1189561
theorem B2372561 : Blo 936583 2372561 := bstep (se 2 (by rfl) ⟨889710, by rfl⟩ : syracuseStep 2372561 = 1779421) B1779421
theorem B2372611 : Blo 936583 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B2110481 : Blo 936583 2110481 := bstep (se 2 (by rfl) ⟨791430, by rfl⟩ : syracuseStep 2110481 = 1582861) B1582861
theorem B1586209 : Blo 936583 1586209 := bstep (se 2 (by rfl) ⟨594828, by rfl⟩ : syracuseStep 1586209 = 1189657) B1189657
theorem B2110499 : Blo 936583 2110499 := bstep (se 1 (by rfl) ⟨1582874, by rfl⟩ : syracuseStep 2110499 = 3165749) B3165749
theorem B1586243 : Blo 936583 1586243 := bstep (se 1 (by rfl) ⟨1189682, by rfl⟩ : syracuseStep 1586243 = 2379365) B2379365
theorem B4502641 : Blo 936583 4502641 := bstep (se 2 (by rfl) ⟨1688490, by rfl⟩ : syracuseStep 4502641 = 3376981) B3376981
theorem B2143345 : Blo 936583 2143345 := bstep (se 2 (by rfl) ⟨803754, by rfl⟩ : syracuseStep 2143345 = 1607509) B1607509
theorem B2372753 : Blo 936583 2372753 := bstep (se 2 (by rfl) ⟨889782, by rfl⟩ : syracuseStep 2372753 = 1779565) B1779565
theorem B1586371 : Blo 936583 1586371 := bstep (se 1 (by rfl) ⟨1189778, by rfl⟩ : syracuseStep 1586371 = 2379557) B2379557
theorem B1783043 : Blo 936583 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B2110769 : Blo 936583 2110769 := bstep (se 2 (by rfl) ⟨791538, by rfl⟩ : syracuseStep 2110769 = 1583077) B1583077
theorem B2110787 : Blo 936583 2110787 := bstep (se 1 (by rfl) ⟨1583090, by rfl⟩ : syracuseStep 2110787 = 3166181) B3166181
theorem B1586513 : Blo 936583 1586513 := bstep (se 2 (by rfl) ⟨594942, by rfl⟩ : syracuseStep 1586513 = 1189885) B1189885
theorem B5715299 : Blo 936583 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B16004465 : Blo 936583 16004465 := bstep (se 2 (by rfl) ⟨6001674, by rfl⟩ : syracuseStep 16004465 = 12003349) B12003349
theorem B9024965 : Blo 936583 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B1586641 : Blo 936583 1586641 := bstep (se 2 (by rfl) ⟨594990, by rfl⟩ : syracuseStep 1586641 = 1189981) B1189981
theorem B1586675 : Blo 936583 1586675 := bstep (se 1 (by rfl) ⟨1190006, by rfl⟩ : syracuseStep 1586675 = 2380013) B2380013
theorem B2668049 : Blo 936583 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B2111057 : Blo 936583 2111057 := bstep (se 2 (by rfl) ⟨791646, by rfl⟩ : syracuseStep 2111057 = 1583293) B1583293
theorem B2111075 : Blo 936583 2111075 := bstep (se 1 (by rfl) ⟨1583306, by rfl⟩ : syracuseStep 2111075 = 3166613) B3166613
theorem B1586803 : Blo 936583 1586803 := bstep (se 1 (by rfl) ⟨1190102, by rfl⟩ : syracuseStep 1586803 = 2380205) B2380205
theorem B6010595 : Blo 936583 6010595 := bstep (se 1 (by rfl) ⟨4507946, by rfl⟩ : syracuseStep 6010595 = 9015893) B9015893
theorem B1586945 : Blo 936583 1586945 := bstep (se 2 (by rfl) ⟨595104, by rfl⟩ : syracuseStep 1586945 = 1190209) B1190209
theorem B2111345 : Blo 936583 2111345 := bstep (se 2 (by rfl) ⟨791754, by rfl⟩ : syracuseStep 2111345 = 1583509) B1583509
theorem B1587073 : Blo 936583 1587073 := bstep (se 2 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 1587073 = 1190305) B1190305
theorem B2111363 : Blo 936583 2111363 := bstep (se 1 (by rfl) ⟨1583522, by rfl⟩ : syracuseStep 2111363 = 3167045) B3167045
theorem B1587107 : Blo 936583 1587107 := bstep (se 1 (by rfl) ⟨1190330, by rfl⟩ : syracuseStep 1587107 = 2380661) B2380661
theorem B1587235 : Blo 936583 1587235 := bstep (se 1 (by rfl) ⟨1190426, by rfl⟩ : syracuseStep 1587235 = 2380853) B2380853
theorem B2537581 : Blo 936583 2537581 := bstep (se 3 (by rfl) ⟨475796, by rfl⟩ : syracuseStep 2537581 = 951593) B951593
theorem B2373745 : Blo 936583 2373745 := bstep (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) B1780309
theorem B1783939 : Blo 936583 1783939 := bstep (se 1 (by rfl) ⟨1337954, by rfl⟩ : syracuseStep 1783939 = 2675909) B2675909
theorem B2111633 : Blo 936583 2111633 := bstep (se 2 (by rfl) ⟨791862, by rfl⟩ : syracuseStep 2111633 = 1583725) B1583725
theorem B2111651 : Blo 936583 2111651 := bstep (se 1 (by rfl) ⟨1583738, by rfl⟩ : syracuseStep 2111651 = 3167477) B3167477
theorem B2570449 : Blo 936583 2570449 := bstep (se 2 (by rfl) ⟨963918, by rfl⟩ : syracuseStep 2570449 = 1927837) B1927837
theorem B1128659 : Blo 936583 1128659 := bstep (se 1 (by rfl) ⟨846494, by rfl⟩ : syracuseStep 1128659 = 1692989) B1692989
theorem B1784099 : Blo 936583 1784099 := bstep (se 1 (by rfl) ⟨1338074, by rfl⟩ : syracuseStep 1784099 = 2676149) B2676149
theorem B1522033 : Blo 936583 1522033 := bstep (se 2 (by rfl) ⟨570762, by rfl⟩ : syracuseStep 1522033 = 1141525) B1141525
theorem B2374019 : Blo 936583 2374019 := bstep (se 1 (by rfl) ⟨1780514, by rfl⟩ : syracuseStep 2374019 = 3561029) B3561029
theorem B2111921 : Blo 936583 2111921 := bstep (se 2 (by rfl) ⟨791970, by rfl⟩ : syracuseStep 2111921 = 1583941) B1583941
theorem B2111939 : Blo 936583 2111939 := bstep (se 1 (by rfl) ⟨1583954, by rfl⟩ : syracuseStep 2111939 = 3167909) B3167909
theorem B2374211 : Blo 936583 2374211 := bstep (se 1 (by rfl) ⟨1780658, by rfl⟩ : syracuseStep 2374211 = 3561317) B3561317
theorem B4274801 : Blo 936583 4274801 := bstep (se 2 (by rfl) ⟨1603050, by rfl⟩ : syracuseStep 4274801 = 3206101) B3206101
theorem B5356145 : Blo 936583 5356145 := bstep (se 2 (by rfl) ⟨2008554, by rfl⟩ : syracuseStep 5356145 = 4017109) B4017109
theorem B1424081 : Blo 936583 1424081 := bstep (se 2 (by rfl) ⟨534030, by rfl⟩ : syracuseStep 1424081 = 1068061) B1068061
theorem B2112209 : Blo 936583 2112209 := bstep (se 2 (by rfl) ⟨792078, by rfl⟩ : syracuseStep 2112209 = 1584157) B1584157
theorem B7125731 : Blo 936583 7125731 := bstep (se 1 (by rfl) ⟨5344298, by rfl⟩ : syracuseStep 7125731 = 10688597) B10688597
theorem B2112227 : Blo 936583 2112227 := bstep (se 1 (by rfl) ⟨1584170, by rfl⟩ : syracuseStep 2112227 = 3168341) B3168341
theorem B13023985 : Blo 936583 13023985 := bstep (se 2 (by rfl) ⟨4883994, by rfl⟩ : syracuseStep 13023985 = 9767989) B9767989
theorem B2538317 : Blo 936583 2538317 := bstep (se 3 (by rfl) ⟨475934, by rfl⟩ : syracuseStep 2538317 = 951869) B951869
theorem B2669507 : Blo 936583 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B2538467 : Blo 936583 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B2112497 : Blo 936583 2112497 := bstep (se 2 (by rfl) ⟨792186, by rfl⟩ : syracuseStep 2112497 = 1584373) B1584373
theorem B2112515 : Blo 936583 2112515 := bstep (se 1 (by rfl) ⟨1584386, by rfl⟩ : syracuseStep 2112515 = 3168773) B3168773
theorem B3161105 : Blo 936583 3161105 := bstep (se 2 (by rfl) ⟨1185414, by rfl⟩ : syracuseStep 3161105 = 2370829) B2370829
theorem B6011981 : Blo 936583 6011981 := bstep (se 3 (by rfl) ⟨1127246, by rfl⟩ : syracuseStep 6011981 = 2254493) B2254493
theorem B2538641 : Blo 936583 2538641 := bstep (se 2 (by rfl) ⟨951990, by rfl⟩ : syracuseStep 2538641 = 1903981) B1903981
theorem B2112785 : Blo 936583 2112785 := bstep (se 2 (by rfl) ⟨792294, by rfl⟩ : syracuseStep 2112785 = 1584589) B1584589
theorem B2112803 : Blo 936583 2112803 := bstep (se 1 (by rfl) ⟨1584602, by rfl⟩ : syracuseStep 2112803 = 3169205) B3169205
theorem B1785169 : Blo 936583 1785169 := bstep (se 2 (by rfl) ⟨669438, by rfl⟩ : syracuseStep 1785169 = 1338877) B1338877
theorem B2375153 : Blo 936583 2375153 := bstep (se 2 (by rfl) ⟨890682, by rfl⟩ : syracuseStep 2375153 = 1781365) B1781365
theorem B2375203 : Blo 936583 2375203 := bstep (se 1 (by rfl) ⟨1781402, by rfl⟩ : syracuseStep 2375203 = 3562805) B3562805
theorem B3161645 : Blo 936583 3161645 := bstep (se 3 (by rfl) ⟨592808, by rfl⟩ : syracuseStep 3161645 = 1185617) B1185617
theorem B2113073 : Blo 936583 2113073 := bstep (se 2 (by rfl) ⟨792402, by rfl⟩ : syracuseStep 2113073 = 1584805) B1584805
theorem B2113091 : Blo 936583 2113091 := bstep (se 1 (by rfl) ⟨1584818, by rfl⟩ : syracuseStep 2113091 = 3169637) B3169637
theorem B3161699 : Blo 936583 3161699 := bstep (se 1 (by rfl) ⟨2371274, by rfl⟩ : syracuseStep 3161699 = 4742549) B4742549
theorem B2375345 : Blo 936583 2375345 := bstep (se 2 (by rfl) ⟨890754, by rfl⟩ : syracuseStep 2375345 = 1781509) B1781509
theorem B2670317 : Blo 936583 2670317 := bstep (se 3 (by rfl) ⟨500684, by rfl⟩ : syracuseStep 2670317 = 1001369) B1001369
theorem B2113361 : Blo 936583 2113361 := bstep (se 2 (by rfl) ⟨792510, by rfl⟩ : syracuseStep 2113361 = 1585021) B1585021
theorem B2113379 : Blo 936583 2113379 := bstep (se 1 (by rfl) ⟨1585034, by rfl⟩ : syracuseStep 2113379 = 3170069) B3170069
theorem B3161969 : Blo 936583 3161969 := bstep (se 2 (by rfl) ⟨1185738, by rfl⟩ : syracuseStep 3161969 = 2371477) B2371477
theorem B4276109 : Blo 936583 4276109 := bstep (se 3 (by rfl) ⟨801770, by rfl⟩ : syracuseStep 4276109 = 1603541) B1603541
theorem B4013965 : Blo 936583 4013965 := bstep (se 3 (by rfl) ⟨752618, by rfl⟩ : syracuseStep 4013965 = 1505237) B1505237
theorem B2670509 : Blo 936583 2670509 := bstep (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) B1001441
theorem B2539441 : Blo 936583 2539441 := bstep (se 2 (by rfl) ⟨952290, by rfl⟩ : syracuseStep 2539441 = 1904581) B1904581
theorem B1425443 : Blo 936583 1425443 := bstep (se 1 (by rfl) ⟨1069082, by rfl⟩ : syracuseStep 1425443 = 2138165) B2138165
theorem B4505699 : Blo 936583 4505699 := bstep (se 1 (by rfl) ⟨3379274, by rfl⟩ : syracuseStep 4505699 = 6758549) B6758549
theorem B2113649 : Blo 936583 2113649 := bstep (se 2 (by rfl) ⟨792618, by rfl⟩ : syracuseStep 2113649 = 1585237) B1585237
theorem B2113667 : Blo 936583 2113667 := bstep (se 1 (by rfl) ⟨1585250, by rfl⟩ : syracuseStep 2113667 = 3170501) B3170501
theorem B12828941 : Blo 936583 12828941 := bstep (se 3 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 12828941 = 4810853) B4810853
theorem B3162509 : Blo 936583 3162509 := bstep (se 3 (by rfl) ⟨592970, by rfl⟩ : syracuseStep 3162509 = 1185941) B1185941
theorem B5718413 : Blo 936583 5718413 := bstep (se 3 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 5718413 = 2144405) B2144405
theorem B2113937 : Blo 936583 2113937 := bstep (se 2 (by rfl) ⟨792726, by rfl⟩ : syracuseStep 2113937 = 1585453) B1585453
theorem B2113955 : Blo 936583 2113955 := bstep (se 1 (by rfl) ⟨1585466, by rfl⟩ : syracuseStep 2113955 = 3170933) B3170933
theorem B3162563 : Blo 936583 3162563 := bstep (se 1 (by rfl) ⟨2371922, by rfl⟩ : syracuseStep 3162563 = 4743845) B4743845
theorem B2376337 : Blo 936583 2376337 := bstep (se 2 (by rfl) ⟨891126, by rfl⟩ : syracuseStep 2376337 = 1782253) B1782253
theorem B2114225 : Blo 936583 2114225 := bstep (se 2 (by rfl) ⟨792834, by rfl⟩ : syracuseStep 2114225 = 1585669) B1585669
theorem B2114243 : Blo 936583 2114243 := bstep (se 1 (by rfl) ⟨1585682, by rfl⟩ : syracuseStep 2114243 = 3171365) B3171365
theorem B3162833 : Blo 936583 3162833 := bstep (se 2 (by rfl) ⟨1186062, by rfl⟩ : syracuseStep 3162833 = 2372125) B2372125
theorem B2671501 : Blo 936583 2671501 := bstep (se 3 (by rfl) ⟨500906, by rfl⟩ : syracuseStep 2671501 = 1001813) B1001813
theorem B2376611 : Blo 936583 2376611 := bstep (se 1 (by rfl) ⟨1782458, by rfl⟩ : syracuseStep 2376611 = 3564917) B3564917
theorem B2114513 : Blo 936583 2114513 := bstep (se 2 (by rfl) ⟨792942, by rfl⟩ : syracuseStep 2114513 = 1585885) B1585885
theorem B2114531 : Blo 936583 2114531 := bstep (se 1 (by rfl) ⟨1585898, by rfl⟩ : syracuseStep 2114531 = 3171797) B3171797
theorem B2376803 : Blo 936583 2376803 := bstep (se 1 (by rfl) ⟨1782602, by rfl⟩ : syracuseStep 2376803 = 3565205) B3565205
theorem B2540717 : Blo 936583 2540717 := bstep (se 3 (by rfl) ⟨476384, by rfl⟩ : syracuseStep 2540717 = 952769) B952769
theorem B3163373 : Blo 936583 3163373 := bstep (se 3 (by rfl) ⟨593132, by rfl⟩ : syracuseStep 3163373 = 1186265) B1186265
theorem B2114801 : Blo 936583 2114801 := bstep (se 2 (by rfl) ⟨793050, by rfl⟩ : syracuseStep 2114801 = 1586101) B1586101
theorem B2114819 : Blo 936583 2114819 := bstep (se 1 (by rfl) ⟨1586114, by rfl⟩ : syracuseStep 2114819 = 3172229) B3172229
theorem B3163427 : Blo 936583 3163427 := bstep (se 1 (by rfl) ⟨2372570, by rfl⟩ : syracuseStep 3163427 = 4745141) B4745141
theorem B1688945 : Blo 936583 1688945 := bstep (se 2 (by rfl) ⟨633354, by rfl⟩ : syracuseStep 1688945 = 1266709) B1266709
theorem B2540945 : Blo 936583 2540945 := bstep (se 2 (by rfl) ⟨952854, by rfl⟩ : syracuseStep 2540945 = 1905709) B1905709
theorem B1426915 : Blo 936583 1426915 := bstep (se 1 (by rfl) ⟨1070186, by rfl⟩ : syracuseStep 1426915 = 2140373) B2140373
theorem B2541041 : Blo 936583 2541041 := bstep (se 2 (by rfl) ⟨952890, by rfl⟩ : syracuseStep 2541041 = 1905781) B1905781
theorem B2115089 : Blo 936583 2115089 := bstep (se 2 (by rfl) ⟨793158, by rfl⟩ : syracuseStep 2115089 = 1586317) B1586317
theorem B2115107 : Blo 936583 2115107 := bstep (se 1 (by rfl) ⟨1586330, by rfl⟩ : syracuseStep 2115107 = 3172661) B3172661
theorem B2573869 : Blo 936583 2573869 := bstep (se 3 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 2573869 = 965201) B965201
theorem B3163697 : Blo 936583 3163697 := bstep (se 2 (by rfl) ⟨1186386, by rfl⟩ : syracuseStep 3163697 = 2372773) B2372773
theorem B2705005 : Blo 936583 2705005 := bstep (se 3 (by rfl) ⟨507188, by rfl⟩ : syracuseStep 2705005 = 1014377) B1014377
theorem B1001219 : Blo 936583 1001219 := bstep (se 1 (by rfl) ⟨750914, by rfl⟩ : syracuseStep 1001219 = 1501829) B1501829
theorem B3557155 : Blo 936583 3557155 := bstep (se 1 (by rfl) ⟨2667866, by rfl⟩ : syracuseStep 3557155 = 5335733) B5335733
theorem B2115377 : Blo 936583 2115377 := bstep (se 2 (by rfl) ⟨793266, by rfl⟩ : syracuseStep 2115377 = 1586533) B1586533
theorem B2115395 : Blo 936583 2115395 := bstep (se 1 (by rfl) ⟨1586546, by rfl⟩ : syracuseStep 2115395 = 3173093) B3173093
theorem B2377745 : Blo 936583 2377745 := bstep (se 2 (by rfl) ⟨891654, by rfl⟩ : syracuseStep 2377745 = 1783309) B1783309
theorem B2377795 : Blo 936583 2377795 := bstep (se 1 (by rfl) ⟨1783346, by rfl⟩ : syracuseStep 2377795 = 3566693) B3566693
theorem B3164237 : Blo 936583 3164237 := bstep (se 3 (by rfl) ⟨593294, by rfl⟩ : syracuseStep 3164237 = 1186589) B1186589
theorem B2115665 : Blo 936583 2115665 := bstep (se 2 (by rfl) ⟨793374, by rfl⟩ : syracuseStep 2115665 = 1586749) B1586749
theorem B2115683 : Blo 936583 2115683 := bstep (se 1 (by rfl) ⟨1586762, by rfl⟩ : syracuseStep 2115683 = 3173525) B3173525
theorem B3164291 : Blo 936583 3164291 := bstep (se 1 (by rfl) ⟨2373218, by rfl⟩ : syracuseStep 3164291 = 4746437) B4746437
theorem B2377937 : Blo 936583 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B3000557 : Blo 936583 3000557 := bstep (se 3 (by rfl) ⟨562604, by rfl⟩ : syracuseStep 3000557 = 1125209) B1125209
theorem B3000685 : Blo 936583 3000685 := bstep (se 3 (by rfl) ⟨562628, by rfl⟩ : syracuseStep 3000685 = 1125257) B1125257
theorem B2115953 : Blo 936583 2115953 := bstep (se 2 (by rfl) ⟨793482, by rfl⟩ : syracuseStep 2115953 = 1586965) B1586965
theorem B2115971 : Blo 936583 2115971 := bstep (se 1 (by rfl) ⟨1586978, by rfl⟩ : syracuseStep 2115971 = 3173957) B3173957
theorem B3164561 : Blo 936583 3164561 := bstep (se 2 (by rfl) ⟨1186710, by rfl⟩ : syracuseStep 3164561 = 2373421) B2373421
theorem B1001971 : Blo 936583 1001971 := bstep (se 1 (by rfl) ⟨751478, by rfl⟩ : syracuseStep 1001971 = 1502957) B1502957
theorem B2673233 : Blo 936583 2673233 := bstep (se 2 (by rfl) ⟨1002462, by rfl⟩ : syracuseStep 2673233 = 2004925) B2004925
theorem B3000941 : Blo 936583 3000941 := bstep (se 3 (by rfl) ⟨562676, by rfl⟩ : syracuseStep 3000941 = 1125353) B1125353
theorem B2116241 : Blo 936583 2116241 := bstep (se 2 (by rfl) ⟨793590, by rfl⟩ : syracuseStep 2116241 = 1587181) B1587181
theorem B936595 : Blo 936583 936595 := bstep (se 1 (by rfl) ⟨702446, by rfl⟩ : syracuseStep 936595 = 1404893) B1404893
theorem B936611 : Blo 936583 936611 := bstep (se 1 (by rfl) ⟨702458, by rfl⟩ : syracuseStep 936611 = 1404917) B1404917
theorem B2116259 : Blo 936583 2116259 := bstep (se 1 (by rfl) ⟨1587194, by rfl⟩ : syracuseStep 2116259 = 3174389) B3174389
theorem B936627 : Blo 936583 936627 := bstep (se 1 (by rfl) ⟨702470, by rfl⟩ : syracuseStep 936627 = 1404941) B1404941
theorem B936643 : Blo 936583 936643 := bstep (se 1 (by rfl) ⟨702482, by rfl⟩ : syracuseStep 936643 = 1404965) B1404965
theorem B936659 : Blo 936583 936659 := bstep (se 1 (by rfl) ⟨702494, by rfl⟩ : syracuseStep 936659 = 1404989) B1404989
theorem B936675 : Blo 936583 936675 := bstep (se 1 (by rfl) ⟨702506, by rfl⟩ : syracuseStep 936675 = 1405013) B1405013
theorem B936691 : Blo 936583 936691 := bstep (se 1 (by rfl) ⟨702518, by rfl⟩ : syracuseStep 936691 = 1405037) B1405037
theorem B1002227 : Blo 936583 1002227 := bstep (se 1 (by rfl) ⟨751670, by rfl⟩ : syracuseStep 1002227 = 1503341) B1503341
theorem B936707 : Blo 936583 936707 := bstep (se 1 (by rfl) ⟨702530, by rfl⟩ : syracuseStep 936707 = 1405061) B1405061
theorem B2673425 : Blo 936583 2673425 := bstep (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) B2005069
theorem B936723 : Blo 936583 936723 := bstep (se 1 (by rfl) ⟨702542, by rfl⟩ : syracuseStep 936723 = 1405085) B1405085
theorem B936739 : Blo 936583 936739 := bstep (se 1 (by rfl) ⟨702554, by rfl⟩ : syracuseStep 936739 = 1405109) B1405109
theorem B936755 : Blo 936583 936755 := bstep (se 1 (by rfl) ⟨702566, by rfl⟩ : syracuseStep 936755 = 1405133) B1405133
theorem B936771 : Blo 936583 936771 := bstep (se 1 (by rfl) ⟨702578, by rfl⟩ : syracuseStep 936771 = 1405157) B1405157
theorem B936787 : Blo 936583 936787 := bstep (se 1 (by rfl) ⟨702590, by rfl⟩ : syracuseStep 936787 = 1405181) B1405181
theorem B936803 : Blo 936583 936803 := bstep (se 1 (by rfl) ⟨702602, by rfl⟩ : syracuseStep 936803 = 1405205) B1405205
theorem B936819 : Blo 936583 936819 := bstep (se 1 (by rfl) ⟨702614, by rfl⟩ : syracuseStep 936819 = 1405229) B1405229
theorem B936835 : Blo 936583 936835 := bstep (se 1 (by rfl) ⟨702626, by rfl⟩ : syracuseStep 936835 = 1405253) B1405253
theorem B936851 : Blo 936583 936851 := bstep (se 1 (by rfl) ⟨702638, by rfl⟩ : syracuseStep 936851 = 1405277) B1405277
theorem B936867 : Blo 936583 936867 := bstep (se 1 (by rfl) ⟨702650, by rfl⟩ : syracuseStep 936867 = 1405301) B1405301
theorem B3165101 : Blo 936583 3165101 := bstep (se 3 (by rfl) ⟨593456, by rfl⟩ : syracuseStep 3165101 = 1186913) B1186913
theorem B1526705 : Blo 936583 1526705 := bstep (se 2 (by rfl) ⟨572514, by rfl⟩ : syracuseStep 1526705 = 1145029) B1145029
theorem B936883 : Blo 936583 936883 := bstep (se 1 (by rfl) ⟨702662, by rfl⟩ : syracuseStep 936883 = 1405325) B1405325
theorem B936899 : Blo 936583 936899 := bstep (se 1 (by rfl) ⟨702674, by rfl⟩ : syracuseStep 936899 = 1405349) B1405349
theorem B936915 : Blo 936583 936915 := bstep (se 1 (by rfl) ⟨702686, by rfl⟩ : syracuseStep 936915 = 1405373) B1405373
theorem B936931 : Blo 936583 936931 := bstep (se 1 (by rfl) ⟨702698, by rfl⟩ : syracuseStep 936931 = 1405397) B1405397
theorem B3165155 : Blo 936583 3165155 := bstep (se 1 (by rfl) ⟨2373866, by rfl⟩ : syracuseStep 3165155 = 4747733) B4747733
theorem B936947 : Blo 936583 936947 := bstep (se 1 (by rfl) ⟨702710, by rfl⟩ : syracuseStep 936947 = 1405421) B1405421
theorem B936963 : Blo 936583 936963 := bstep (se 1 (by rfl) ⟨702722, by rfl⟩ : syracuseStep 936963 = 1405445) B1405445
theorem B936979 : Blo 936583 936979 := bstep (se 1 (by rfl) ⟨702734, by rfl⟩ : syracuseStep 936979 = 1405469) B1405469
theorem B936995 : Blo 936583 936995 := bstep (se 1 (by rfl) ⟨702746, by rfl⟩ : syracuseStep 936995 = 1405493) B1405493
theorem B937011 : Blo 936583 937011 := bstep (se 1 (by rfl) ⟨702758, by rfl⟩ : syracuseStep 937011 = 1405517) B1405517
theorem B937027 : Blo 936583 937027 := bstep (se 1 (by rfl) ⟨702770, by rfl⟩ : syracuseStep 937027 = 1405541) B1405541
theorem B937043 : Blo 936583 937043 := bstep (se 1 (by rfl) ⟨702782, by rfl⟩ : syracuseStep 937043 = 1405565) B1405565
theorem B937059 : Blo 936583 937059 := bstep (se 1 (by rfl) ⟨702794, by rfl⟩ : syracuseStep 937059 = 1405589) B1405589
theorem B937075 : Blo 936583 937075 := bstep (se 1 (by rfl) ⟨702806, by rfl⟩ : syracuseStep 937075 = 1405613) B1405613
theorem B937091 : Blo 936583 937091 := bstep (se 1 (by rfl) ⟨702818, by rfl⟩ : syracuseStep 937091 = 1405637) B1405637
theorem B937107 : Blo 936583 937107 := bstep (se 1 (by rfl) ⟨702830, by rfl⟩ : syracuseStep 937107 = 1405661) B1405661
theorem B937123 : Blo 936583 937123 := bstep (se 1 (by rfl) ⟨702842, by rfl⟩ : syracuseStep 937123 = 1405685) B1405685
theorem B2378929 : Blo 936583 2378929 := bstep (se 2 (by rfl) ⟨892098, by rfl⟩ : syracuseStep 2378929 = 1784197) B1784197
theorem B937139 : Blo 936583 937139 := bstep (se 1 (by rfl) ⟨702854, by rfl⟩ : syracuseStep 937139 = 1405709) B1405709
theorem B937155 : Blo 936583 937155 := bstep (se 1 (by rfl) ⟨702866, by rfl⟩ : syracuseStep 937155 = 1405733) B1405733
theorem B937171 : Blo 936583 937171 := bstep (se 1 (by rfl) ⟨702878, by rfl⟩ : syracuseStep 937171 = 1405757) B1405757
theorem B937187 : Blo 936583 937187 := bstep (se 1 (by rfl) ⟨702890, by rfl⟩ : syracuseStep 937187 = 1405781) B1405781
theorem B3165425 : Blo 936583 3165425 := bstep (se 2 (by rfl) ⟨1187034, by rfl⟩ : syracuseStep 3165425 = 2374069) B2374069
theorem B937203 : Blo 936583 937203 := bstep (se 1 (by rfl) ⟨702902, by rfl⟩ : syracuseStep 937203 = 1405805) B1405805
theorem B937219 : Blo 936583 937219 := bstep (se 1 (by rfl) ⟨702914, by rfl⟩ : syracuseStep 937219 = 1405829) B1405829
theorem B937235 : Blo 936583 937235 := bstep (se 1 (by rfl) ⟨702926, by rfl⟩ : syracuseStep 937235 = 1405853) B1405853
theorem B937251 : Blo 936583 937251 := bstep (se 1 (by rfl) ⟨702938, by rfl⟩ : syracuseStep 937251 = 1405877) B1405877
theorem B937267 : Blo 936583 937267 := bstep (se 1 (by rfl) ⟨702950, by rfl⟩ : syracuseStep 937267 = 1405901) B1405901
theorem B937283 : Blo 936583 937283 := bstep (se 1 (by rfl) ⟨702962, by rfl⟩ : syracuseStep 937283 = 1405925) B1405925
theorem B937299 : Blo 936583 937299 := bstep (se 1 (by rfl) ⟨702974, by rfl⟩ : syracuseStep 937299 = 1405949) B1405949
theorem B937315 : Blo 936583 937315 := bstep (se 1 (by rfl) ⟨702986, by rfl⟩ : syracuseStep 937315 = 1405973) B1405973
theorem B937331 : Blo 936583 937331 := bstep (se 1 (by rfl) ⟨702998, by rfl⟩ : syracuseStep 937331 = 1405997) B1405997
theorem B937347 : Blo 936583 937347 := bstep (se 1 (by rfl) ⟨703010, by rfl⟩ : syracuseStep 937347 = 1406021) B1406021
theorem B937363 : Blo 936583 937363 := bstep (se 1 (by rfl) ⟨703022, by rfl⟩ : syracuseStep 937363 = 1406045) B1406045
theorem B937379 : Blo 936583 937379 := bstep (se 1 (by rfl) ⟨703034, by rfl⟩ : syracuseStep 937379 = 1406069) B1406069
theorem B937395 : Blo 936583 937395 := bstep (se 1 (by rfl) ⟨703046, by rfl⟩ : syracuseStep 937395 = 1406093) B1406093
theorem B937411 : Blo 936583 937411 := bstep (se 1 (by rfl) ⟨703058, by rfl⟩ : syracuseStep 937411 = 1406117) B1406117
theorem B2379203 : Blo 936583 2379203 := bstep (se 1 (by rfl) ⟨1784402, by rfl⟩ : syracuseStep 2379203 = 3568805) B3568805
theorem B937427 : Blo 936583 937427 := bstep (se 1 (by rfl) ⟨703070, by rfl⟩ : syracuseStep 937427 = 1406141) B1406141
theorem B937443 : Blo 936583 937443 := bstep (se 1 (by rfl) ⟨703082, by rfl⟩ : syracuseStep 937443 = 1406165) B1406165
theorem B1002979 : Blo 936583 1002979 := bstep (se 1 (by rfl) ⟨752234, by rfl⟩ : syracuseStep 1002979 = 1504469) B1504469
theorem B937459 : Blo 936583 937459 := bstep (se 1 (by rfl) ⟨703094, by rfl⟩ : syracuseStep 937459 = 1406189) B1406189
theorem B937475 : Blo 936583 937475 := bstep (se 1 (by rfl) ⟨703106, by rfl⟩ : syracuseStep 937475 = 1406213) B1406213
theorem B937491 : Blo 936583 937491 := bstep (se 1 (by rfl) ⟨703118, by rfl⟩ : syracuseStep 937491 = 1406237) B1406237
theorem B937507 : Blo 936583 937507 := bstep (se 1 (by rfl) ⟨703130, by rfl⟩ : syracuseStep 937507 = 1406261) B1406261
theorem B937523 : Blo 936583 937523 := bstep (se 1 (by rfl) ⟨703142, by rfl⟩ : syracuseStep 937523 = 1406285) B1406285
theorem B937539 : Blo 936583 937539 := bstep (se 1 (by rfl) ⟨703154, by rfl⟩ : syracuseStep 937539 = 1406309) B1406309
theorem B937555 : Blo 936583 937555 := bstep (se 1 (by rfl) ⟨703166, by rfl⟩ : syracuseStep 937555 = 1406333) B1406333
theorem B937571 : Blo 936583 937571 := bstep (se 1 (by rfl) ⟨703178, by rfl⟩ : syracuseStep 937571 = 1406357) B1406357
theorem B937587 : Blo 936583 937587 := bstep (se 1 (by rfl) ⟨703190, by rfl⟩ : syracuseStep 937587 = 1406381) B1406381
theorem B937603 : Blo 936583 937603 := bstep (se 1 (by rfl) ⟨703202, by rfl⟩ : syracuseStep 937603 = 1406405) B1406405
theorem B2379395 : Blo 936583 2379395 := bstep (se 1 (by rfl) ⟨1784546, by rfl⟩ : syracuseStep 2379395 = 3569093) B3569093
theorem B937619 : Blo 936583 937619 := bstep (se 1 (by rfl) ⟨703214, by rfl⟩ : syracuseStep 937619 = 1406429) B1406429
theorem B937635 : Blo 936583 937635 := bstep (se 1 (by rfl) ⟨703226, by rfl⟩ : syracuseStep 937635 = 1406453) B1406453
theorem B937651 : Blo 936583 937651 := bstep (se 1 (by rfl) ⟨703238, by rfl⟩ : syracuseStep 937651 = 1406477) B1406477
theorem B937667 : Blo 936583 937667 := bstep (se 1 (by rfl) ⟨703250, by rfl⟩ : syracuseStep 937667 = 1406501) B1406501
theorem B937683 : Blo 936583 937683 := bstep (se 1 (by rfl) ⟨703262, by rfl⟩ : syracuseStep 937683 = 1406525) B1406525
theorem B937699 : Blo 936583 937699 := bstep (se 1 (by rfl) ⟨703274, by rfl⟩ : syracuseStep 937699 = 1406549) B1406549
theorem B2674417 : Blo 936583 2674417 := bstep (se 2 (by rfl) ⟨1002906, by rfl⟩ : syracuseStep 2674417 = 2005813) B2005813
theorem B937715 : Blo 936583 937715 := bstep (se 1 (by rfl) ⟨703286, by rfl⟩ : syracuseStep 937715 = 1406573) B1406573
theorem B937731 : Blo 936583 937731 := bstep (se 1 (by rfl) ⟨703298, by rfl⟩ : syracuseStep 937731 = 1406597) B1406597
theorem B3165965 : Blo 936583 3165965 := bstep (se 3 (by rfl) ⟨593618, by rfl⟩ : syracuseStep 3165965 = 1187237) B1187237
theorem B937747 : Blo 936583 937747 := bstep (se 1 (by rfl) ⟨703310, by rfl⟩ : syracuseStep 937747 = 1406621) B1406621
theorem B937763 : Blo 936583 937763 := bstep (se 1 (by rfl) ⟨703322, by rfl⟩ : syracuseStep 937763 = 1406645) B1406645
theorem B937779 : Blo 936583 937779 := bstep (se 1 (by rfl) ⟨703334, by rfl⟩ : syracuseStep 937779 = 1406669) B1406669
theorem B937795 : Blo 936583 937795 := bstep (se 1 (by rfl) ⟨703346, by rfl⟩ : syracuseStep 937795 = 1406693) B1406693
theorem B3166019 : Blo 936583 3166019 := bstep (se 1 (by rfl) ⟨2374514, by rfl⟩ : syracuseStep 3166019 = 4749029) B4749029
theorem B937811 : Blo 936583 937811 := bstep (se 1 (by rfl) ⟨703358, by rfl⟩ : syracuseStep 937811 = 1406717) B1406717
theorem B937827 : Blo 936583 937827 := bstep (se 1 (by rfl) ⟨703370, by rfl⟩ : syracuseStep 937827 = 1406741) B1406741
theorem B937843 : Blo 936583 937843 := bstep (se 1 (by rfl) ⟨703382, by rfl⟩ : syracuseStep 937843 = 1406765) B1406765
theorem B937859 : Blo 936583 937859 := bstep (se 1 (by rfl) ⟨703394, by rfl⟩ : syracuseStep 937859 = 1406789) B1406789
theorem B937875 : Blo 936583 937875 := bstep (se 1 (by rfl) ⟨703406, by rfl⟩ : syracuseStep 937875 = 1406813) B1406813
theorem B937891 : Blo 936583 937891 := bstep (se 1 (by rfl) ⟨703418, by rfl⟩ : syracuseStep 937891 = 1406837) B1406837
theorem B937907 : Blo 936583 937907 := bstep (se 1 (by rfl) ⟨703430, by rfl⟩ : syracuseStep 937907 = 1406861) B1406861
theorem B937923 : Blo 936583 937923 := bstep (se 1 (by rfl) ⟨703442, by rfl⟩ : syracuseStep 937923 = 1406885) B1406885
theorem B7131077 : Blo 936583 7131077 := bstep (se 4 (by rfl) ⟨668538, by rfl⟩ : syracuseStep 7131077 = 1337077) B1337077
theorem B3559373 : Blo 936583 3559373 := bstep (se 3 (by rfl) ⟨667382, by rfl⟩ : syracuseStep 3559373 = 1334765) B1334765
theorem B937939 : Blo 936583 937939 := bstep (se 1 (by rfl) ⟨703454, by rfl⟩ : syracuseStep 937939 = 1406909) B1406909
theorem B937955 : Blo 936583 937955 := bstep (se 1 (by rfl) ⟨703466, by rfl⟩ : syracuseStep 937955 = 1406933) B1406933
theorem B937971 : Blo 936583 937971 := bstep (se 1 (by rfl) ⟨703478, by rfl⟩ : syracuseStep 937971 = 1406957) B1406957
theorem B937987 : Blo 936583 937987 := bstep (se 1 (by rfl) ⟨703490, by rfl⟩ : syracuseStep 937987 = 1406981) B1406981
theorem B2674691 : Blo 936583 2674691 := bstep (se 1 (by rfl) ⟨2006018, by rfl⟩ : syracuseStep 2674691 = 4012037) B4012037
theorem B938003 : Blo 936583 938003 := bstep (se 1 (by rfl) ⟨703502, by rfl⟩ : syracuseStep 938003 = 1407005) B1407005
theorem B938019 : Blo 936583 938019 := bstep (se 1 (by rfl) ⟨703514, by rfl⟩ : syracuseStep 938019 = 1407029) B1407029
theorem B938035 : Blo 936583 938035 := bstep (se 1 (by rfl) ⟨703526, by rfl⟩ : syracuseStep 938035 = 1407053) B1407053
theorem B938051 : Blo 936583 938051 := bstep (se 1 (by rfl) ⟨703538, by rfl⟩ : syracuseStep 938051 = 1407077) B1407077
theorem B3166289 : Blo 936583 3166289 := bstep (se 2 (by rfl) ⟨1187358, by rfl⟩ : syracuseStep 3166289 = 2374717) B2374717
theorem B938067 : Blo 936583 938067 := bstep (se 1 (by rfl) ⟨703550, by rfl⟩ : syracuseStep 938067 = 1407101) B1407101
theorem B3002467 : Blo 936583 3002467 := bstep (se 1 (by rfl) ⟨2251850, by rfl⟩ : syracuseStep 3002467 = 4503701) B4503701
theorem B938083 : Blo 936583 938083 := bstep (se 1 (by rfl) ⟨703562, by rfl⟩ : syracuseStep 938083 = 1407125) B1407125
theorem B938099 : Blo 936583 938099 := bstep (se 1 (by rfl) ⟨703574, by rfl⟩ : syracuseStep 938099 = 1407149) B1407149
theorem B938115 : Blo 936583 938115 := bstep (se 1 (by rfl) ⟨703586, by rfl⟩ : syracuseStep 938115 = 1407173) B1407173
theorem B938131 : Blo 936583 938131 := bstep (se 1 (by rfl) ⟨703598, by rfl⟩ : syracuseStep 938131 = 1407197) B1407197
theorem B938147 : Blo 936583 938147 := bstep (se 1 (by rfl) ⟨703610, by rfl⟩ : syracuseStep 938147 = 1407221) B1407221
theorem B938163 : Blo 936583 938163 := bstep (se 1 (by rfl) ⟨703622, by rfl⟩ : syracuseStep 938163 = 1407245) B1407245
theorem B938179 : Blo 936583 938179 := bstep (se 1 (by rfl) ⟨703634, by rfl⟩ : syracuseStep 938179 = 1407269) B1407269
theorem B2674883 : Blo 936583 2674883 := bstep (se 1 (by rfl) ⟨2006162, by rfl⟩ : syracuseStep 2674883 = 4012325) B4012325
theorem B938195 : Blo 936583 938195 := bstep (se 1 (by rfl) ⟨703646, by rfl⟩ : syracuseStep 938195 = 1407293) B1407293
theorem B1069283 : Blo 936583 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B938211 : Blo 936583 938211 := bstep (se 1 (by rfl) ⟨703658, by rfl⟩ : syracuseStep 938211 = 1407317) B1407317
theorem B12865763 : Blo 936583 12865763 := bstep (se 1 (by rfl) ⟨9649322, by rfl⟩ : syracuseStep 12865763 = 19298645) B19298645
theorem B938227 : Blo 936583 938227 := bstep (se 1 (by rfl) ⟨703670, by rfl⟩ : syracuseStep 938227 = 1407341) B1407341
theorem B938243 : Blo 936583 938243 := bstep (se 1 (by rfl) ⟨703682, by rfl⟩ : syracuseStep 938243 = 1407365) B1407365
theorem B938259 : Blo 936583 938259 := bstep (se 1 (by rfl) ⟨703694, by rfl⟩ : syracuseStep 938259 = 1407389) B1407389
theorem B938275 : Blo 936583 938275 := bstep (se 1 (by rfl) ⟨703706, by rfl⟩ : syracuseStep 938275 = 1407413) B1407413
theorem B938291 : Blo 936583 938291 := bstep (se 1 (by rfl) ⟨703718, by rfl⟩ : syracuseStep 938291 = 1407437) B1407437
theorem B938307 : Blo 936583 938307 := bstep (se 1 (by rfl) ⟨703730, by rfl⟩ : syracuseStep 938307 = 1407461) B1407461
theorem B938323 : Blo 936583 938323 := bstep (se 1 (by rfl) ⟨703742, by rfl⟩ : syracuseStep 938323 = 1407485) B1407485
theorem B938339 : Blo 936583 938339 := bstep (se 1 (by rfl) ⟨703754, by rfl⟩ : syracuseStep 938339 = 1407509) B1407509
theorem B938355 : Blo 936583 938355 := bstep (se 1 (by rfl) ⟨703766, by rfl⟩ : syracuseStep 938355 = 1407533) B1407533
theorem B938371 : Blo 936583 938371 := bstep (se 1 (by rfl) ⟨703778, by rfl⟩ : syracuseStep 938371 = 1407557) B1407557
theorem B938387 : Blo 936583 938387 := bstep (se 1 (by rfl) ⟨703790, by rfl⟩ : syracuseStep 938387 = 1407581) B1407581
theorem B938403 : Blo 936583 938403 := bstep (se 1 (by rfl) ⟨703802, by rfl⟩ : syracuseStep 938403 = 1407605) B1407605
theorem B938419 : Blo 936583 938419 := bstep (se 1 (by rfl) ⟨703814, by rfl⟩ : syracuseStep 938419 = 1407629) B1407629
theorem B938435 : Blo 936583 938435 := bstep (se 1 (by rfl) ⟨703826, by rfl⟩ : syracuseStep 938435 = 1407653) B1407653
theorem B24400325 : Blo 936583 24400325 := bstep (se 4 (by rfl) ⟨2287530, by rfl⟩ : syracuseStep 24400325 = 4575061) B4575061
theorem B1266131 : Blo 936583 1266131 := bstep (se 1 (by rfl) ⟨949598, by rfl⟩ : syracuseStep 1266131 = 1899197) B1899197
theorem B938451 : Blo 936583 938451 := bstep (se 1 (by rfl) ⟨703838, by rfl⟩ : syracuseStep 938451 = 1407677) B1407677
theorem B938467 : Blo 936583 938467 := bstep (se 1 (by rfl) ⟨703850, by rfl⟩ : syracuseStep 938467 = 1407701) B1407701
theorem B938483 : Blo 936583 938483 := bstep (se 1 (by rfl) ⟨703862, by rfl⟩ : syracuseStep 938483 = 1407725) B1407725
theorem B938499 : Blo 936583 938499 := bstep (se 1 (by rfl) ⟨703874, by rfl⟩ : syracuseStep 938499 = 1407749) B1407749
theorem B938515 : Blo 936583 938515 := bstep (se 1 (by rfl) ⟨703886, by rfl⟩ : syracuseStep 938515 = 1407773) B1407773
theorem B938531 : Blo 936583 938531 := bstep (se 1 (by rfl) ⟨703898, by rfl⟩ : syracuseStep 938531 = 1407797) B1407797
theorem B938547 : Blo 936583 938547 := bstep (se 1 (by rfl) ⟨703910, by rfl⟩ : syracuseStep 938547 = 1407821) B1407821
theorem B2380337 : Blo 936583 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B938563 : Blo 936583 938563 := bstep (se 1 (by rfl) ⟨703922, by rfl⟩ : syracuseStep 938563 = 1407845) B1407845
theorem B938579 : Blo 936583 938579 := bstep (se 1 (by rfl) ⟨703934, by rfl⟩ : syracuseStep 938579 = 1407869) B1407869
theorem B938595 : Blo 936583 938595 := bstep (se 1 (by rfl) ⟨703946, by rfl⟩ : syracuseStep 938595 = 1407893) B1407893
theorem B2380387 : Blo 936583 2380387 := bstep (se 1 (by rfl) ⟨1785290, by rfl⟩ : syracuseStep 2380387 = 3570581) B3570581
theorem B3166829 : Blo 936583 3166829 := bstep (se 3 (by rfl) ⟨593780, by rfl⟩ : syracuseStep 3166829 = 1187561) B1187561
theorem B938611 : Blo 936583 938611 := bstep (se 1 (by rfl) ⟨703958, by rfl⟩ : syracuseStep 938611 = 1407917) B1407917
theorem B938627 : Blo 936583 938627 := bstep (se 1 (by rfl) ⟨703970, by rfl⟩ : syracuseStep 938627 = 1407941) B1407941
theorem B938643 : Blo 936583 938643 := bstep (se 1 (by rfl) ⟨703982, by rfl⟩ : syracuseStep 938643 = 1407965) B1407965
theorem B3166883 : Blo 936583 3166883 := bstep (se 1 (by rfl) ⟨2375162, by rfl⟩ : syracuseStep 3166883 = 4750325) B4750325
theorem B938659 : Blo 936583 938659 := bstep (se 1 (by rfl) ⟨703994, by rfl⟩ : syracuseStep 938659 = 1407989) B1407989
theorem B938675 : Blo 936583 938675 := bstep (se 1 (by rfl) ⟨704006, by rfl⟩ : syracuseStep 938675 = 1408013) B1408013
theorem B938691 : Blo 936583 938691 := bstep (se 1 (by rfl) ⟨704018, by rfl⟩ : syracuseStep 938691 = 1408037) B1408037
theorem B938707 : Blo 936583 938707 := bstep (se 1 (by rfl) ⟨704030, by rfl⟩ : syracuseStep 938707 = 1408061) B1408061
theorem B1004243 : Blo 936583 1004243 := bstep (se 1 (by rfl) ⟨753182, by rfl⟩ : syracuseStep 1004243 = 1506365) B1506365
theorem B938723 : Blo 936583 938723 := bstep (se 1 (by rfl) ⟨704042, by rfl⟩ : syracuseStep 938723 = 1408085) B1408085
theorem B2380529 : Blo 936583 2380529 := bstep (se 2 (by rfl) ⟨892698, by rfl⟩ : syracuseStep 2380529 = 1785397) B1785397
theorem B938739 : Blo 936583 938739 := bstep (se 1 (by rfl) ⟨704054, by rfl⟩ : syracuseStep 938739 = 1408109) B1408109
theorem B938755 : Blo 936583 938755 := bstep (se 1 (by rfl) ⟨704066, by rfl⟩ : syracuseStep 938755 = 1408133) B1408133
theorem B938771 : Blo 936583 938771 := bstep (se 1 (by rfl) ⟨704078, by rfl⟩ : syracuseStep 938771 = 1408157) B1408157
theorem B938787 : Blo 936583 938787 := bstep (se 1 (by rfl) ⟨704090, by rfl⟩ : syracuseStep 938787 = 1408181) B1408181
theorem B938803 : Blo 936583 938803 := bstep (se 1 (by rfl) ⟨704102, by rfl⟩ : syracuseStep 938803 = 1408205) B1408205
theorem B938819 : Blo 936583 938819 := bstep (se 1 (by rfl) ⟨704114, by rfl⟩ : syracuseStep 938819 = 1408229) B1408229
theorem B938835 : Blo 936583 938835 := bstep (se 1 (by rfl) ⟨704126, by rfl⟩ : syracuseStep 938835 = 1408253) B1408253
theorem B938851 : Blo 936583 938851 := bstep (se 1 (by rfl) ⟨704138, by rfl⟩ : syracuseStep 938851 = 1408277) B1408277
theorem B938867 : Blo 936583 938867 := bstep (se 1 (by rfl) ⟨704150, by rfl⟩ : syracuseStep 938867 = 1408301) B1408301
theorem B938883 : Blo 936583 938883 := bstep (se 1 (by rfl) ⟨704162, by rfl⟩ : syracuseStep 938883 = 1408325) B1408325
theorem B4641677 : Blo 936583 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B938899 : Blo 936583 938899 := bstep (se 1 (by rfl) ⟨704174, by rfl⟩ : syracuseStep 938899 = 1408349) B1408349
theorem B938915 : Blo 936583 938915 := bstep (se 1 (by rfl) ⟨704186, by rfl⟩ : syracuseStep 938915 = 1408373) B1408373
theorem B3167153 : Blo 936583 3167153 := bstep (se 2 (by rfl) ⟨1187682, by rfl⟩ : syracuseStep 3167153 = 2375365) B2375365
theorem B938931 : Blo 936583 938931 := bstep (se 1 (by rfl) ⟨704198, by rfl⟩ : syracuseStep 938931 = 1408397) B1408397
theorem B938947 : Blo 936583 938947 := bstep (se 1 (by rfl) ⟨704210, by rfl⟩ : syracuseStep 938947 = 1408421) B1408421
theorem B938963 : Blo 936583 938963 := bstep (se 1 (by rfl) ⟨704222, by rfl⟩ : syracuseStep 938963 = 1408445) B1408445
theorem B938979 : Blo 936583 938979 := bstep (se 1 (by rfl) ⟨704234, by rfl⟩ : syracuseStep 938979 = 1408469) B1408469
theorem B2675693 : Blo 936583 2675693 := bstep (se 3 (by rfl) ⟨501692, by rfl⟩ : syracuseStep 2675693 = 1003385) B1003385
theorem B938995 : Blo 936583 938995 := bstep (se 1 (by rfl) ⟨704246, by rfl⟩ : syracuseStep 938995 = 1408493) B1408493
theorem B939011 : Blo 936583 939011 := bstep (se 1 (by rfl) ⟨704258, by rfl⟩ : syracuseStep 939011 = 1408517) B1408517
theorem B939027 : Blo 936583 939027 := bstep (se 1 (by rfl) ⟨704270, by rfl⟩ : syracuseStep 939027 = 1408541) B1408541
theorem B939043 : Blo 936583 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B939059 : Blo 936583 939059 := bstep (se 1 (by rfl) ⟨704294, by rfl⟩ : syracuseStep 939059 = 1408589) B1408589
theorem B939075 : Blo 936583 939075 := bstep (se 1 (by rfl) ⟨704306, by rfl⟩ : syracuseStep 939075 = 1408613) B1408613
theorem B1266769 : Blo 936583 1266769 := bstep (se 2 (by rfl) ⟨475038, by rfl⟩ : syracuseStep 1266769 = 950077) B950077
theorem B939091 : Blo 936583 939091 := bstep (se 1 (by rfl) ⟨704318, by rfl⟩ : syracuseStep 939091 = 1408637) B1408637
theorem B8016995 : Blo 936583 8016995 := bstep (se 1 (by rfl) ⟨6012746, by rfl⟩ : syracuseStep 8016995 = 12025493) B12025493
theorem B939107 : Blo 936583 939107 := bstep (se 1 (by rfl) ⟨704330, by rfl⟩ : syracuseStep 939107 = 1408661) B1408661
theorem B939123 : Blo 936583 939123 := bstep (se 1 (by rfl) ⟨704342, by rfl⟩ : syracuseStep 939123 = 1408685) B1408685
theorem B939139 : Blo 936583 939139 := bstep (se 1 (by rfl) ⟨704354, by rfl⟩ : syracuseStep 939139 = 1408709) B1408709
theorem B939155 : Blo 936583 939155 := bstep (se 1 (by rfl) ⟨704366, by rfl⟩ : syracuseStep 939155 = 1408733) B1408733
theorem B939171 : Blo 936583 939171 := bstep (se 1 (by rfl) ⟨704378, by rfl⟩ : syracuseStep 939171 = 1408757) B1408757
theorem B2675875 : Blo 936583 2675875 := bstep (se 1 (by rfl) ⟨2006906, by rfl⟩ : syracuseStep 2675875 = 4013813) B4013813
theorem B939187 : Blo 936583 939187 := bstep (se 1 (by rfl) ⟨704390, by rfl⟩ : syracuseStep 939187 = 1408781) B1408781
theorem B939203 : Blo 936583 939203 := bstep (se 1 (by rfl) ⟨704402, by rfl⟩ : syracuseStep 939203 = 1408805) B1408805
theorem B939219 : Blo 936583 939219 := bstep (se 1 (by rfl) ⟨704414, by rfl⟩ : syracuseStep 939219 = 1408829) B1408829
theorem B939235 : Blo 936583 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B939251 : Blo 936583 939251 := bstep (se 1 (by rfl) ⟨704438, by rfl⟩ : syracuseStep 939251 = 1408877) B1408877
theorem B939267 : Blo 936583 939267 := bstep (se 1 (by rfl) ⟨704450, by rfl⟩ : syracuseStep 939267 = 1408901) B1408901
theorem B939283 : Blo 936583 939283 := bstep (se 1 (by rfl) ⟨704462, by rfl⟩ : syracuseStep 939283 = 1408925) B1408925
theorem B939299 : Blo 936583 939299 := bstep (se 1 (by rfl) ⟨704474, by rfl⟩ : syracuseStep 939299 = 1408949) B1408949
theorem B939315 : Blo 936583 939315 := bstep (se 1 (by rfl) ⟨704486, by rfl⟩ : syracuseStep 939315 = 1408973) B1408973
theorem B939331 : Blo 936583 939331 := bstep (se 1 (by rfl) ⟨704498, by rfl⟩ : syracuseStep 939331 = 1408997) B1408997
theorem B939347 : Blo 936583 939347 := bstep (se 1 (by rfl) ⟨704510, by rfl⟩ : syracuseStep 939347 = 1409021) B1409021
theorem B939363 : Blo 936583 939363 := bstep (se 1 (by rfl) ⟨704522, by rfl⟩ : syracuseStep 939363 = 1409045) B1409045
theorem B939379 : Blo 936583 939379 := bstep (se 1 (by rfl) ⟨704534, by rfl⟩ : syracuseStep 939379 = 1409069) B1409069
theorem B939395 : Blo 936583 939395 := bstep (se 1 (by rfl) ⟨704546, by rfl⟩ : syracuseStep 939395 = 1409093) B1409093
theorem B5133709 : Blo 936583 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B939411 : Blo 936583 939411 := bstep (se 1 (by rfl) ⟨704558, by rfl⟩ : syracuseStep 939411 = 1409117) B1409117
theorem B939427 : Blo 936583 939427 := bstep (se 1 (by rfl) ⟨704570, by rfl⟩ : syracuseStep 939427 = 1409141) B1409141
theorem B939443 : Blo 936583 939443 := bstep (se 1 (by rfl) ⟨704582, by rfl⟩ : syracuseStep 939443 = 1409165) B1409165
theorem B939459 : Blo 936583 939459 := bstep (se 1 (by rfl) ⟨704594, by rfl⟩ : syracuseStep 939459 = 1409189) B1409189
theorem B3167693 : Blo 936583 3167693 := bstep (se 3 (by rfl) ⟨593942, by rfl⟩ : syracuseStep 3167693 = 1187885) B1187885
theorem B939475 : Blo 936583 939475 := bstep (se 1 (by rfl) ⟨704606, by rfl⟩ : syracuseStep 939475 = 1409213) B1409213
theorem B939491 : Blo 936583 939491 := bstep (se 1 (by rfl) ⟨704618, by rfl⟩ : syracuseStep 939491 = 1409237) B1409237
theorem B939507 : Blo 936583 939507 := bstep (se 1 (by rfl) ⟨704630, by rfl⟩ : syracuseStep 939507 = 1409261) B1409261
theorem B3167747 : Blo 936583 3167747 := bstep (se 1 (by rfl) ⟨2375810, by rfl⟩ : syracuseStep 3167747 = 4751621) B4751621
theorem B939523 : Blo 936583 939523 := bstep (se 1 (by rfl) ⟨704642, by rfl⟩ : syracuseStep 939523 = 1409285) B1409285
theorem B939539 : Blo 936583 939539 := bstep (se 1 (by rfl) ⟨704654, by rfl⟩ : syracuseStep 939539 = 1409309) B1409309
theorem B939555 : Blo 936583 939555 := bstep (se 1 (by rfl) ⟨704666, by rfl⟩ : syracuseStep 939555 = 1409333) B1409333
theorem B939571 : Blo 936583 939571 := bstep (se 1 (by rfl) ⟨704678, by rfl⟩ : syracuseStep 939571 = 1409357) B1409357
theorem B939587 : Blo 936583 939587 := bstep (se 1 (by rfl) ⟨704690, by rfl⟩ : syracuseStep 939587 = 1409381) B1409381
theorem B939603 : Blo 936583 939603 := bstep (se 1 (by rfl) ⟨704702, by rfl⟩ : syracuseStep 939603 = 1409405) B1409405
theorem B939619 : Blo 936583 939619 := bstep (se 1 (by rfl) ⟨704714, by rfl⟩ : syracuseStep 939619 = 1409429) B1409429
theorem B939635 : Blo 936583 939635 := bstep (se 1 (by rfl) ⟨704726, by rfl⟩ : syracuseStep 939635 = 1409453) B1409453
theorem B939651 : Blo 936583 939651 := bstep (se 1 (by rfl) ⟨704738, by rfl⟩ : syracuseStep 939651 = 1409477) B1409477
theorem B2676365 : Blo 936583 2676365 := bstep (se 3 (by rfl) ⟨501818, by rfl⟩ : syracuseStep 2676365 = 1003637) B1003637
theorem B939667 : Blo 936583 939667 := bstep (se 1 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 939667 = 1409501) B1409501
theorem B3004067 : Blo 936583 3004067 := bstep (se 1 (by rfl) ⟨2253050, by rfl⟩ : syracuseStep 3004067 = 4506101) B4506101
theorem B939683 : Blo 936583 939683 := bstep (se 1 (by rfl) ⟨704762, by rfl⟩ : syracuseStep 939683 = 1409525) B1409525
theorem B939699 : Blo 936583 939699 := bstep (se 1 (by rfl) ⟨704774, by rfl⟩ : syracuseStep 939699 = 1409549) B1409549
theorem B939715 : Blo 936583 939715 := bstep (se 1 (by rfl) ⟨704786, by rfl⟩ : syracuseStep 939715 = 1409573) B1409573
theorem B939731 : Blo 936583 939731 := bstep (se 1 (by rfl) ⟨704798, by rfl⟩ : syracuseStep 939731 = 1409597) B1409597
theorem B939747 : Blo 936583 939747 := bstep (se 1 (by rfl) ⟨704810, by rfl⟩ : syracuseStep 939747 = 1409621) B1409621
theorem B939763 : Blo 936583 939763 := bstep (se 1 (by rfl) ⟨704822, by rfl⟩ : syracuseStep 939763 = 1409645) B1409645
theorem B939779 : Blo 936583 939779 := bstep (se 1 (by rfl) ⟨704834, by rfl⟩ : syracuseStep 939779 = 1409669) B1409669
theorem B3168017 : Blo 936583 3168017 := bstep (se 2 (by rfl) ⟨1188006, by rfl⟩ : syracuseStep 3168017 = 2376013) B2376013
theorem B939795 : Blo 936583 939795 := bstep (se 1 (by rfl) ⟨704846, by rfl⟩ : syracuseStep 939795 = 1409693) B1409693
theorem B939811 : Blo 936583 939811 := bstep (se 1 (by rfl) ⟨704858, by rfl⟩ : syracuseStep 939811 = 1409717) B1409717
theorem B939827 : Blo 936583 939827 := bstep (se 1 (by rfl) ⟨704870, by rfl⟩ : syracuseStep 939827 = 1409741) B1409741
theorem B939843 : Blo 936583 939843 := bstep (se 1 (by rfl) ⟨704882, by rfl⟩ : syracuseStep 939843 = 1409765) B1409765
theorem B939859 : Blo 936583 939859 := bstep (se 1 (by rfl) ⟨704894, by rfl⟩ : syracuseStep 939859 = 1409789) B1409789
theorem B939875 : Blo 936583 939875 := bstep (se 1 (by rfl) ⟨704906, by rfl⟩ : syracuseStep 939875 = 1409813) B1409813
theorem B939891 : Blo 936583 939891 := bstep (se 1 (by rfl) ⟨704918, by rfl⟩ : syracuseStep 939891 = 1409837) B1409837
theorem B939907 : Blo 936583 939907 := bstep (se 1 (by rfl) ⟨704930, by rfl⟩ : syracuseStep 939907 = 1409861) B1409861
theorem B939923 : Blo 936583 939923 := bstep (se 1 (by rfl) ⟨704942, by rfl⟩ : syracuseStep 939923 = 1409885) B1409885
theorem B939939 : Blo 936583 939939 := bstep (se 1 (by rfl) ⟨704954, by rfl⟩ : syracuseStep 939939 = 1409909) B1409909
theorem B939955 : Blo 936583 939955 := bstep (se 1 (by rfl) ⟨704966, by rfl⟩ : syracuseStep 939955 = 1409933) B1409933
theorem B2709443 : Blo 936583 2709443 := bstep (se 1 (by rfl) ⟨2032082, by rfl⟩ : syracuseStep 2709443 = 4064165) B4064165
theorem B939971 : Blo 936583 939971 := bstep (se 1 (by rfl) ⟨704978, by rfl⟩ : syracuseStep 939971 = 1409957) B1409957
theorem B939987 : Blo 936583 939987 := bstep (se 1 (by rfl) ⟨704990, by rfl⟩ : syracuseStep 939987 = 1409981) B1409981
theorem B940003 : Blo 936583 940003 := bstep (se 1 (by rfl) ⟨705002, by rfl⟩ : syracuseStep 940003 = 1410005) B1410005
theorem B940019 : Blo 936583 940019 := bstep (se 1 (by rfl) ⟨705014, by rfl⟩ : syracuseStep 940019 = 1410029) B1410029
theorem B940035 : Blo 936583 940035 := bstep (se 1 (by rfl) ⟨705026, by rfl⟩ : syracuseStep 940035 = 1410053) B1410053
theorem B940051 : Blo 936583 940051 := bstep (se 1 (by rfl) ⟨705038, by rfl⟩ : syracuseStep 940051 = 1410077) B1410077
theorem B940067 : Blo 936583 940067 := bstep (se 1 (by rfl) ⟨705050, by rfl⟩ : syracuseStep 940067 = 1410101) B1410101
theorem B940083 : Blo 936583 940083 := bstep (se 1 (by rfl) ⟨705062, by rfl⟩ : syracuseStep 940083 = 1410125) B1410125
theorem B940099 : Blo 936583 940099 := bstep (se 1 (by rfl) ⟨705074, by rfl⟩ : syracuseStep 940099 = 1410149) B1410149
theorem B940115 : Blo 936583 940115 := bstep (se 1 (by rfl) ⟨705086, by rfl⟩ : syracuseStep 940115 = 1410173) B1410173
theorem B940131 : Blo 936583 940131 := bstep (se 1 (by rfl) ⟨705098, by rfl⟩ : syracuseStep 940131 = 1410197) B1410197
theorem B940147 : Blo 936583 940147 := bstep (se 1 (by rfl) ⟨705110, by rfl⟩ : syracuseStep 940147 = 1410221) B1410221
theorem B940163 : Blo 936583 940163 := bstep (se 1 (by rfl) ⟨705122, by rfl⟩ : syracuseStep 940163 = 1410245) B1410245
theorem B940179 : Blo 936583 940179 := bstep (se 1 (by rfl) ⟨705134, by rfl⟩ : syracuseStep 940179 = 1410269) B1410269
theorem B940195 : Blo 936583 940195 := bstep (se 1 (by rfl) ⟨705146, by rfl⟩ : syracuseStep 940195 = 1410293) B1410293
theorem B940211 : Blo 936583 940211 := bstep (se 1 (by rfl) ⟨705158, by rfl⟩ : syracuseStep 940211 = 1410317) B1410317
theorem B940227 : Blo 936583 940227 := bstep (se 1 (by rfl) ⟨705170, by rfl⟩ : syracuseStep 940227 = 1410341) B1410341
theorem B940243 : Blo 936583 940243 := bstep (se 1 (by rfl) ⟨705182, by rfl⟩ : syracuseStep 940243 = 1410365) B1410365
theorem B940259 : Blo 936583 940259 := bstep (se 1 (by rfl) ⟨705194, by rfl⟩ : syracuseStep 940259 = 1410389) B1410389
theorem B940275 : Blo 936583 940275 := bstep (se 1 (by rfl) ⟨705206, by rfl⟩ : syracuseStep 940275 = 1410413) B1410413
theorem B1267969 : Blo 936583 1267969 := bstep (se 2 (by rfl) ⟨475488, by rfl⟩ : syracuseStep 1267969 = 950977) B950977
theorem B940291 : Blo 936583 940291 := bstep (se 1 (by rfl) ⟨705218, by rfl⟩ : syracuseStep 940291 = 1410437) B1410437
theorem B940307 : Blo 936583 940307 := bstep (se 1 (by rfl) ⟨705230, by rfl⟩ : syracuseStep 940307 = 1410461) B1410461
theorem B940323 : Blo 936583 940323 := bstep (se 1 (by rfl) ⟨705242, by rfl⟩ : syracuseStep 940323 = 1410485) B1410485
theorem B3168557 : Blo 936583 3168557 := bstep (se 3 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 3168557 = 1188209) B1188209
theorem B5069105 : Blo 936583 5069105 := bstep (se 2 (by rfl) ⟨1900914, by rfl⟩ : syracuseStep 5069105 = 3801829) B3801829
theorem B940339 : Blo 936583 940339 := bstep (se 1 (by rfl) ⟨705254, by rfl⟩ : syracuseStep 940339 = 1410509) B1410509
theorem B1268033 : Blo 936583 1268033 := bstep (se 2 (by rfl) ⟨475512, by rfl⟩ : syracuseStep 1268033 = 951025) B951025
theorem B940355 : Blo 936583 940355 := bstep (se 1 (by rfl) ⟨705266, by rfl⟩ : syracuseStep 940355 = 1410533) B1410533
theorem B940371 : Blo 936583 940371 := bstep (se 1 (by rfl) ⟨705278, by rfl⟩ : syracuseStep 940371 = 1410557) B1410557
theorem B3168611 : Blo 936583 3168611 := bstep (se 1 (by rfl) ⟨2376458, by rfl⟩ : syracuseStep 3168611 = 4752917) B4752917
theorem B940387 : Blo 936583 940387 := bstep (se 1 (by rfl) ⟨705290, by rfl⟩ : syracuseStep 940387 = 1410581) B1410581
theorem B6773105 : Blo 936583 6773105 := bstep (se 2 (by rfl) ⟨2539914, by rfl⟩ : syracuseStep 6773105 = 5079829) B5079829
theorem B940403 : Blo 936583 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B940419 : Blo 936583 940419 := bstep (se 1 (by rfl) ⟨705314, by rfl⟩ : syracuseStep 940419 = 1410629) B1410629
theorem B940435 : Blo 936583 940435 := bstep (se 1 (by rfl) ⟨705326, by rfl⟩ : syracuseStep 940435 = 1410653) B1410653
theorem B940451 : Blo 936583 940451 := bstep (se 1 (by rfl) ⟨705338, by rfl⟩ : syracuseStep 940451 = 1410677) B1410677
theorem B940467 : Blo 936583 940467 := bstep (se 1 (by rfl) ⟨705350, by rfl⟩ : syracuseStep 940467 = 1410701) B1410701
theorem B940483 : Blo 936583 940483 := bstep (se 1 (by rfl) ⟨705362, by rfl⟩ : syracuseStep 940483 = 1410725) B1410725
theorem B940499 : Blo 936583 940499 := bstep (se 1 (by rfl) ⟨705374, by rfl⟩ : syracuseStep 940499 = 1410749) B1410749
theorem B9624035 : Blo 936583 9624035 := bstep (se 1 (by rfl) ⟨7218026, by rfl⟩ : syracuseStep 9624035 = 14436053) B14436053
theorem B940515 : Blo 936583 940515 := bstep (se 1 (by rfl) ⟨705386, by rfl⟩ : syracuseStep 940515 = 1410773) B1410773
theorem B940531 : Blo 936583 940531 := bstep (se 1 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 940531 = 1410797) B1410797
theorem B940547 : Blo 936583 940547 := bstep (se 1 (by rfl) ⟨705410, by rfl⟩ : syracuseStep 940547 = 1410821) B1410821
theorem B940563 : Blo 936583 940563 := bstep (se 1 (by rfl) ⟨705422, by rfl⟩ : syracuseStep 940563 = 1410845) B1410845
theorem B940579 : Blo 936583 940579 := bstep (se 1 (by rfl) ⟨705434, by rfl⟩ : syracuseStep 940579 = 1410869) B1410869
theorem B3005041 : Blo 936583 3005041 := bstep (se 2 (by rfl) ⟨1126890, by rfl⟩ : syracuseStep 3005041 = 2253781) B2253781
theorem B3168881 : Blo 936583 3168881 := bstep (se 2 (by rfl) ⟨1188330, by rfl⟩ : syracuseStep 3168881 = 2376661) B2376661
theorem B8575715 : Blo 936583 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B4741901 : Blo 936583 4741901 := bstep (se 3 (by rfl) ⟨889106, by rfl⟩ : syracuseStep 4741901 = 1778213) B1778213
theorem B5069603 : Blo 936583 5069603 := bstep (se 1 (by rfl) ⟨3802202, by rfl⟩ : syracuseStep 5069603 = 7604405) B7604405
theorem B2677549 : Blo 936583 2677549 := bstep (se 3 (by rfl) ⟨502040, by rfl⟩ : syracuseStep 2677549 = 1004081) B1004081
theorem B1334065 : Blo 936583 1334065 := bstep (se 2 (by rfl) ⟨500274, by rfl⟩ : syracuseStep 1334065 = 1000549) B1000549
theorem B3562289 : Blo 936583 3562289 := bstep (se 2 (by rfl) ⟨1335858, by rfl⟩ : syracuseStep 3562289 = 2671717) B2671717
theorem B1334161 : Blo 936583 1334161 := bstep (se 2 (by rfl) ⟨500310, by rfl⟩ : syracuseStep 1334161 = 1000621) B1000621
theorem B1268785 : Blo 936583 1268785 := bstep (se 2 (by rfl) ⟨475794, by rfl⟩ : syracuseStep 1268785 = 951589) B951589
theorem B3169421 : Blo 936583 3169421 := bstep (se 3 (by rfl) ⟨594266, by rfl⟩ : syracuseStep 3169421 = 1188533) B1188533
theorem B3169475 : Blo 936583 3169475 := bstep (se 1 (by rfl) ⟨2377106, by rfl⟩ : syracuseStep 3169475 = 4754213) B4754213
theorem B1203427 : Blo 936583 1203427 := bstep (se 1 (by rfl) ⟨902570, by rfl⟩ : syracuseStep 1203427 = 1805141) B1805141
theorem B1334657 : Blo 936583 1334657 := bstep (se 2 (by rfl) ⟨500496, by rfl⟩ : syracuseStep 1334657 = 1000993) B1000993
theorem B1072531 : Blo 936583 1072531 := bstep (se 1 (by rfl) ⟨804398, by rfl⟩ : syracuseStep 1072531 = 1608797) B1608797
theorem B3169745 : Blo 936583 3169745 := bstep (se 2 (by rfl) ⟨1188654, by rfl⟩ : syracuseStep 3169745 = 2377309) B2377309
theorem B9756515 : Blo 936583 9756515 := bstep (se 1 (by rfl) ⟨7317386, by rfl⟩ : syracuseStep 9756515 = 14634773) B14634773
theorem B3170285 : Blo 936583 3170285 := bstep (se 3 (by rfl) ⟨594428, by rfl⟩ : syracuseStep 3170285 = 1188857) B1188857
theorem B3170339 : Blo 936583 3170339 := bstep (se 1 (by rfl) ⟨2377754, by rfl⟩ : syracuseStep 3170339 = 4755509) B4755509
theorem B1335523 : Blo 936583 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B3563747 : Blo 936583 3563747 := bstep (se 1 (by rfl) ⟨2672810, by rfl⟩ : syracuseStep 3563747 = 5345621) B5345621
theorem B3006733 : Blo 936583 3006733 := bstep (se 3 (by rfl) ⟨563762, by rfl⟩ : syracuseStep 3006733 = 1127525) B1127525
theorem B3170609 : Blo 936583 3170609 := bstep (se 2 (by rfl) ⟨1188978, by rfl⟩ : syracuseStep 3170609 = 2377957) B2377957
theorem B1335619 : Blo 936583 1335619 := bstep (se 1 (by rfl) ⟨1001714, by rfl⟩ : syracuseStep 1335619 = 2003429) B2003429
theorem B2712017 : Blo 936583 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B1336115 : Blo 936583 1336115 := bstep (se 1 (by rfl) ⟨1002086, by rfl⟩ : syracuseStep 1336115 = 2004173) B2004173
theorem B3171149 : Blo 936583 3171149 := bstep (se 3 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 3171149 = 1189181) B1189181
theorem B3171203 : Blo 936583 3171203 := bstep (se 1 (by rfl) ⟨2378402, by rfl⟩ : syracuseStep 3171203 = 4756805) B4756805
theorem B1270801 : Blo 936583 1270801 := bstep (se 2 (by rfl) ⟨476550, by rfl⟩ : syracuseStep 1270801 = 953101) B953101
theorem B3171473 : Blo 936583 3171473 := bstep (se 2 (by rfl) ⟨1189302, by rfl⟩ : syracuseStep 3171473 = 2378605) B2378605
theorem B3564749 : Blo 936583 3564749 := bstep (se 3 (by rfl) ⟨668390, by rfl⟩ : syracuseStep 3564749 = 1336781) B1336781
theorem B2254243 : Blo 936583 2254243 := bstep (se 1 (by rfl) ⟨1690682, by rfl⟩ : syracuseStep 2254243 = 3381365) B3381365
theorem B1336753 : Blo 936583 1336753 := bstep (se 2 (by rfl) ⟨501282, by rfl⟩ : syracuseStep 1336753 = 1002565) B1002565
theorem B1500689 : Blo 936583 1500689 := bstep (se 2 (by rfl) ⟨562758, by rfl⟩ : syracuseStep 1500689 = 1125517) B1125517
theorem B4744817 : Blo 936583 4744817 := bstep (se 2 (by rfl) ⟨1779306, by rfl⟩ : syracuseStep 4744817 = 3558613) B3558613
theorem B7136909 : Blo 936583 7136909 := bstep (se 3 (by rfl) ⟨1338170, by rfl⟩ : syracuseStep 7136909 = 2676341) B2676341
theorem B3172013 : Blo 936583 3172013 := bstep (se 3 (by rfl) ⟨594752, by rfl⟩ : syracuseStep 3172013 = 1189505) B1189505
theorem B3172067 : Blo 936583 3172067 := bstep (se 1 (by rfl) ⟨2379050, by rfl⟩ : syracuseStep 3172067 = 4758101) B4758101
theorem B4056817 : Blo 936583 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B1337089 : Blo 936583 1337089 := bstep (se 2 (by rfl) ⟨501408, by rfl⟩ : syracuseStep 1337089 = 1002817) B1002817
theorem B1500977 : Blo 936583 1500977 := bstep (se 2 (by rfl) ⟨562866, by rfl⟩ : syracuseStep 1500977 = 1125733) B1125733
theorem B10282805 : Blo 936583 10282805 := bstep (se 5 (by rfl) ⟨482006, by rfl⟩ : syracuseStep 10282805 = 964013) B964013
theorem B13526837 : Blo 936583 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B3172337 : Blo 936583 3172337 := bstep (se 2 (by rfl) ⟨1189626, by rfl⟩ : syracuseStep 3172337 = 2379253) B2379253
theorem B3008515 : Blo 936583 3008515 := bstep (se 1 (by rfl) ⟨2256386, by rfl⟩ : syracuseStep 3008515 = 4512773) B4512773
theorem B1501201 : Blo 936583 1501201 := bstep (se 2 (by rfl) ⟨562950, by rfl⟩ : syracuseStep 1501201 = 1125901) B1125901
theorem B7596101 : Blo 936583 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B1337681 : Blo 936583 1337681 := bstep (se 2 (by rfl) ⟨501630, by rfl⟩ : syracuseStep 1337681 = 1003261) B1003261
theorem B3008963 : Blo 936583 3008963 := bstep (se 1 (by rfl) ⟨2256722, by rfl⟩ : syracuseStep 3008963 = 4513445) B4513445
theorem B3172877 : Blo 936583 3172877 := bstep (se 3 (by rfl) ⟨594914, by rfl⟩ : syracuseStep 3172877 = 1189829) B1189829
theorem B24078869 : Blo 936583 24078869 := bstep (se 6 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 24078869 = 1128697) B1128697
theorem B3172931 : Blo 936583 3172931 := bstep (se 1 (by rfl) ⟨2379698, by rfl⟩ : syracuseStep 3172931 = 4759397) B4759397
theorem B10676933 : Blo 936583 10676933 := bstep (se 4 (by rfl) ⟨1000962, by rfl⟩ : syracuseStep 10676933 = 2001925) B2001925
theorem B3173201 : Blo 936583 3173201 := bstep (se 2 (by rfl) ⟨1189950, by rfl⟩ : syracuseStep 3173201 = 2379901) B2379901
theorem B1338211 : Blo 936583 1338211 := bstep (se 1 (by rfl) ⟨1003658, by rfl⟩ : syracuseStep 1338211 = 2007317) B2007317
theorem B6024077 : Blo 936583 6024077 := bstep (se 3 (by rfl) ⟨1129514, by rfl⟩ : syracuseStep 6024077 = 2259029) B2259029
theorem B4746275 : Blo 936583 4746275 := bstep (se 1 (by rfl) ⟨3559706, by rfl⟩ : syracuseStep 4746275 = 7119413) B7119413
theorem B2714797 : Blo 936583 2714797 := bstep (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) B1018049
theorem B1338547 : Blo 936583 1338547 := bstep (se 1 (by rfl) ⟨1003910, by rfl⟩ : syracuseStep 1338547 = 2007821) B2007821
theorem B9268465 : Blo 936583 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B3566861 : Blo 936583 3566861 := bstep (se 3 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 3566861 = 1337573) B1337573
theorem B6778181 : Blo 936583 6778181 := bstep (se 4 (by rfl) ⟨635454, by rfl⟩ : syracuseStep 6778181 = 1270909) B1270909
theorem B3173741 : Blo 936583 3173741 := bstep (se 3 (by rfl) ⟨595076, by rfl⟩ : syracuseStep 3173741 = 1190153) B1190153
theorem B3173795 : Blo 936583 3173795 := bstep (se 1 (by rfl) ⟨2380346, by rfl⟩ : syracuseStep 3173795 = 4760693) B4760693
theorem B2289091 : Blo 936583 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B978403 : Blo 936583 978403 := bstep (se 1 (by rfl) ⟨733802, by rfl⟩ : syracuseStep 978403 = 1467605) B1467605
theorem B1502803 : Blo 936583 1502803 := bstep (se 1 (by rfl) ⟨1127102, by rfl⟩ : syracuseStep 1502803 = 2254205) B2254205
theorem B3010193 : Blo 936583 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B3174065 : Blo 936583 3174065 := bstep (se 2 (by rfl) ⟨1190274, by rfl⟩ : syracuseStep 3174065 = 2380549) B2380549
theorem B1830595 : Blo 936583 1830595 := bstep (se 1 (by rfl) ⟨1372946, by rfl⟩ : syracuseStep 1830595 = 2745893) B2745893
theorem B1339105 : Blo 936583 1339105 := bstep (se 2 (by rfl) ⟨502164, by rfl⟩ : syracuseStep 1339105 = 1004329) B1004329
theorem B1339139 : Blo 936583 1339139 := bstep (se 1 (by rfl) ⟨1004354, by rfl⟩ : syracuseStep 1339139 = 2008709) B2008709
theorem B4747085 : Blo 936583 4747085 := bstep (se 3 (by rfl) ⟨890078, by rfl⟩ : syracuseStep 4747085 = 1780157) B1780157
theorem B56323981 : Blo 936583 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B1404881 : Blo 936583 1404881 := bstep (se 2 (by rfl) ⟨526830, by rfl⟩ : syracuseStep 1404881 = 1053661) B1053661
theorem B1404899 : Blo 936583 1404899 := bstep (se 1 (by rfl) ⟨1053674, by rfl⟩ : syracuseStep 1404899 = 2107349) B2107349
theorem B1404929 : Blo 936583 1404929 := bstep (se 2 (by rfl) ⟨526848, by rfl⟩ : syracuseStep 1404929 = 1053697) B1053697
theorem B1404947 : Blo 936583 1404947 := bstep (se 1 (by rfl) ⟨1053710, by rfl⟩ : syracuseStep 1404947 = 2107421) B2107421
theorem B1404977 : Blo 936583 1404977 := bstep (se 2 (by rfl) ⟨526866, by rfl⟩ : syracuseStep 1404977 = 1053733) B1053733
theorem B3567665 : Blo 936583 3567665 := bstep (se 2 (by rfl) ⟨1337874, by rfl⟩ : syracuseStep 3567665 = 2675749) B2675749
theorem B1404995 : Blo 936583 1404995 := bstep (se 1 (by rfl) ⟨1053746, by rfl⟩ : syracuseStep 1404995 = 2107493) B2107493
theorem B1405025 : Blo 936583 1405025 := bstep (se 2 (by rfl) ⟨526884, by rfl⟩ : syracuseStep 1405025 = 1053769) B1053769
theorem B1405043 : Blo 936583 1405043 := bstep (se 1 (by rfl) ⟨1053782, by rfl⟩ : syracuseStep 1405043 = 2107565) B2107565
theorem B1405073 : Blo 936583 1405073 := bstep (se 2 (by rfl) ⟨526902, by rfl⟩ : syracuseStep 1405073 = 1053805) B1053805
theorem B1405091 : Blo 936583 1405091 := bstep (se 1 (by rfl) ⟨1053818, by rfl⟩ : syracuseStep 1405091 = 2107637) B2107637
theorem B1405121 : Blo 936583 1405121 := bstep (se 2 (by rfl) ⟨526920, by rfl⟩ : syracuseStep 1405121 = 1053841) B1053841
theorem B1405139 : Blo 936583 1405139 := bstep (se 1 (by rfl) ⟨1053854, by rfl⟩ : syracuseStep 1405139 = 2107709) B2107709
theorem B1405169 : Blo 936583 1405169 := bstep (se 2 (by rfl) ⟨526938, by rfl⟩ : syracuseStep 1405169 = 1053877) B1053877
theorem B1405187 : Blo 936583 1405187 := bstep (se 1 (by rfl) ⟨1053890, by rfl⟩ : syracuseStep 1405187 = 2107781) B2107781
theorem B1405217 : Blo 936583 1405217 := bstep (se 2 (by rfl) ⟨526956, by rfl⟩ : syracuseStep 1405217 = 1053913) B1053913
theorem B1405235 : Blo 936583 1405235 := bstep (se 1 (by rfl) ⟨1053926, by rfl⟩ : syracuseStep 1405235 = 2107853) B2107853
theorem B1405265 : Blo 936583 1405265 := bstep (se 2 (by rfl) ⟨526974, by rfl⟩ : syracuseStep 1405265 = 1053949) B1053949
theorem B1405283 : Blo 936583 1405283 := bstep (se 1 (by rfl) ⟨1053962, by rfl⟩ : syracuseStep 1405283 = 2107925) B2107925
theorem B1405313 : Blo 936583 1405313 := bstep (se 2 (by rfl) ⟨526992, by rfl⟩ : syracuseStep 1405313 = 1053985) B1053985
theorem B1405331 : Blo 936583 1405331 := bstep (se 1 (by rfl) ⟨1053998, by rfl⟩ : syracuseStep 1405331 = 2107997) B2107997
theorem B1405361 : Blo 936583 1405361 := bstep (se 2 (by rfl) ⟨527010, by rfl⟩ : syracuseStep 1405361 = 1054021) B1054021
theorem B1405379 : Blo 936583 1405379 := bstep (se 1 (by rfl) ⟨1054034, by rfl⟩ : syracuseStep 1405379 = 2108069) B2108069
theorem B1405409 : Blo 936583 1405409 := bstep (se 2 (by rfl) ⟨527028, by rfl⟩ : syracuseStep 1405409 = 1054057) B1054057
theorem B7139825 : Blo 936583 7139825 := bstep (se 2 (by rfl) ⟨2677434, by rfl⟩ : syracuseStep 7139825 = 5354869) B5354869
theorem B1405427 : Blo 936583 1405427 := bstep (se 1 (by rfl) ⟨1054070, by rfl⟩ : syracuseStep 1405427 = 2108141) B2108141
theorem B1405457 : Blo 936583 1405457 := bstep (se 2 (by rfl) ⟨527046, by rfl⟩ : syracuseStep 1405457 = 1054093) B1054093
theorem B3011089 : Blo 936583 3011089 := bstep (se 2 (by rfl) ⟨1129158, by rfl⟩ : syracuseStep 3011089 = 2258317) B2258317
theorem B1405475 : Blo 936583 1405475 := bstep (se 1 (by rfl) ⟨1054106, by rfl⟩ : syracuseStep 1405475 = 2108213) B2108213
theorem B1405505 : Blo 936583 1405505 := bstep (se 2 (by rfl) ⟨527064, by rfl⟩ : syracuseStep 1405505 = 1054129) B1054129
theorem B1405523 : Blo 936583 1405523 := bstep (se 1 (by rfl) ⟨1054142, by rfl⟩ : syracuseStep 1405523 = 2108285) B2108285
theorem B1405553 : Blo 936583 1405553 := bstep (se 2 (by rfl) ⟨527082, by rfl⟩ : syracuseStep 1405553 = 1054165) B1054165
theorem B1405571 : Blo 936583 1405571 := bstep (se 1 (by rfl) ⟨1054178, by rfl⟩ : syracuseStep 1405571 = 2108357) B2108357
theorem B1405601 : Blo 936583 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B1405619 : Blo 936583 1405619 := bstep (se 1 (by rfl) ⟨1054214, by rfl⟩ : syracuseStep 1405619 = 2108429) B2108429
theorem B3568333 : Blo 936583 3568333 := bstep (se 3 (by rfl) ⟨669062, by rfl⟩ : syracuseStep 3568333 = 1338125) B1338125
theorem B1405649 : Blo 936583 1405649 := bstep (se 2 (by rfl) ⟨527118, by rfl⟩ : syracuseStep 1405649 = 1054237) B1054237
theorem B1405667 : Blo 936583 1405667 := bstep (se 1 (by rfl) ⟨1054250, by rfl⟩ : syracuseStep 1405667 = 2108501) B2108501
theorem B1405697 : Blo 936583 1405697 := bstep (se 2 (by rfl) ⟨527136, by rfl⟩ : syracuseStep 1405697 = 1054273) B1054273
theorem B1405715 : Blo 936583 1405715 := bstep (se 1 (by rfl) ⟨1054286, by rfl⟩ : syracuseStep 1405715 = 2108573) B2108573
theorem B1405745 : Blo 936583 1405745 := bstep (se 2 (by rfl) ⟨527154, by rfl⟩ : syracuseStep 1405745 = 1054309) B1054309
theorem B1405763 : Blo 936583 1405763 := bstep (se 1 (by rfl) ⟨1054322, by rfl⟩ : syracuseStep 1405763 = 2108645) B2108645
theorem B4289357 : Blo 936583 4289357 := bstep (se 3 (by rfl) ⟨804254, by rfl⟩ : syracuseStep 4289357 = 1608509) B1608509
theorem B1405793 : Blo 936583 1405793 := bstep (se 2 (by rfl) ⟨527172, by rfl⟩ : syracuseStep 1405793 = 1054345) B1054345
theorem B3797873 : Blo 936583 3797873 := bstep (se 2 (by rfl) ⟨1424202, by rfl⟩ : syracuseStep 3797873 = 2848405) B2848405
theorem B1405811 : Blo 936583 1405811 := bstep (se 1 (by rfl) ⟨1054358, by rfl⟩ : syracuseStep 1405811 = 2108717) B2108717
theorem B1602433 : Blo 936583 1602433 := bstep (se 2 (by rfl) ⟨600912, by rfl⟩ : syracuseStep 1602433 = 1201825) B1201825
theorem B1405841 : Blo 936583 1405841 := bstep (se 2 (by rfl) ⟨527190, by rfl⟩ : syracuseStep 1405841 = 1054381) B1054381
theorem B3797923 : Blo 936583 3797923 := bstep (se 1 (by rfl) ⟨2848442, by rfl⟩ : syracuseStep 3797923 = 5696885) B5696885
theorem B1405859 : Blo 936583 1405859 := bstep (se 1 (by rfl) ⟨1054394, by rfl⟩ : syracuseStep 1405859 = 2108789) B2108789
theorem B1405889 : Blo 936583 1405889 := bstep (se 2 (by rfl) ⟨527208, by rfl⟩ : syracuseStep 1405889 = 1054417) B1054417
theorem B1405907 : Blo 936583 1405907 := bstep (se 1 (by rfl) ⟨1054430, by rfl⟩ : syracuseStep 1405907 = 2108861) B2108861
theorem B1405937 : Blo 936583 1405937 := bstep (se 2 (by rfl) ⟨527226, by rfl⟩ : syracuseStep 1405937 = 1054453) B1054453
theorem B1405955 : Blo 936583 1405955 := bstep (se 1 (by rfl) ⟨1054466, by rfl⟩ : syracuseStep 1405955 = 2108933) B2108933
theorem B1405985 : Blo 936583 1405985 := bstep (se 2 (by rfl) ⟨527244, by rfl⟩ : syracuseStep 1405985 = 1054489) B1054489
theorem B1504289 : Blo 936583 1504289 := bstep (se 2 (by rfl) ⟨564108, by rfl⟩ : syracuseStep 1504289 = 1128217) B1128217
theorem B1406003 : Blo 936583 1406003 := bstep (se 1 (by rfl) ⟨1054502, by rfl⟩ : syracuseStep 1406003 = 2109005) B2109005
theorem B1406033 : Blo 936583 1406033 := bstep (se 2 (by rfl) ⟨527262, by rfl⟩ : syracuseStep 1406033 = 1054525) B1054525
theorem B1406051 : Blo 936583 1406051 := bstep (se 1 (by rfl) ⟨1054538, by rfl⟩ : syracuseStep 1406051 = 2109077) B2109077
theorem B7599217 : Blo 936583 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B1406081 : Blo 936583 1406081 := bstep (se 2 (by rfl) ⟨527280, by rfl⟩ : syracuseStep 1406081 = 1054561) B1054561
theorem B1406099 : Blo 936583 1406099 := bstep (se 1 (by rfl) ⟨1054574, by rfl⟩ : syracuseStep 1406099 = 2109149) B2109149
theorem B1504417 : Blo 936583 1504417 := bstep (se 2 (by rfl) ⟨564156, by rfl⟩ : syracuseStep 1504417 = 1128313) B1128313
theorem B1406129 : Blo 936583 1406129 := bstep (se 2 (by rfl) ⟨527298, by rfl⟩ : syracuseStep 1406129 = 1054597) B1054597
theorem B1406147 : Blo 936583 1406147 := bstep (se 1 (by rfl) ⟨1054610, by rfl⟩ : syracuseStep 1406147 = 2109221) B2109221
theorem B1406177 : Blo 936583 1406177 := bstep (se 2 (by rfl) ⟨527316, by rfl⟩ : syracuseStep 1406177 = 1054633) B1054633
theorem B1406195 : Blo 936583 1406195 := bstep (se 1 (by rfl) ⟨1054646, by rfl⟩ : syracuseStep 1406195 = 2109293) B2109293
theorem B1406225 : Blo 936583 1406225 := bstep (se 2 (by rfl) ⟨527334, by rfl⟩ : syracuseStep 1406225 = 1054669) B1054669
theorem B1406243 : Blo 936583 1406243 := bstep (se 1 (by rfl) ⟨1054682, by rfl⟩ : syracuseStep 1406243 = 2109365) B2109365
theorem B1406273 : Blo 936583 1406273 := bstep (se 2 (by rfl) ⟨527352, by rfl⟩ : syracuseStep 1406273 = 1054705) B1054705
theorem B1406291 : Blo 936583 1406291 := bstep (se 1 (by rfl) ⟨1054718, by rfl⟩ : syracuseStep 1406291 = 2109437) B2109437
theorem B1406321 : Blo 936583 1406321 := bstep (se 2 (by rfl) ⟨527370, by rfl⟩ : syracuseStep 1406321 = 1054741) B1054741
theorem B1406339 : Blo 936583 1406339 := bstep (se 1 (by rfl) ⟨1054754, by rfl⟩ : syracuseStep 1406339 = 2109509) B2109509
theorem B1406369 : Blo 936583 1406369 := bstep (se 2 (by rfl) ⟨527388, by rfl⟩ : syracuseStep 1406369 = 1054777) B1054777
theorem B1406387 : Blo 936583 1406387 := bstep (se 1 (by rfl) ⟨1054790, by rfl⟩ : syracuseStep 1406387 = 2109581) B2109581
theorem B1406417 : Blo 936583 1406417 := bstep (se 2 (by rfl) ⟨527406, by rfl⟩ : syracuseStep 1406417 = 1054813) B1054813
theorem B1406435 : Blo 936583 1406435 := bstep (se 1 (by rfl) ⟨1054826, by rfl⟩ : syracuseStep 1406435 = 2109653) B2109653
theorem B3569123 : Blo 936583 3569123 := bstep (se 1 (by rfl) ⟨2676842, by rfl⟩ : syracuseStep 3569123 = 5353685) B5353685
theorem B1406465 : Blo 936583 1406465 := bstep (se 2 (by rfl) ⟨527424, by rfl⟩ : syracuseStep 1406465 = 1054849) B1054849
theorem B1406483 : Blo 936583 1406483 := bstep (se 1 (by rfl) ⟨1054862, by rfl⟩ : syracuseStep 1406483 = 2109725) B2109725
theorem B1406513 : Blo 936583 1406513 := bstep (se 2 (by rfl) ⟨527442, by rfl⟩ : syracuseStep 1406513 = 1054885) B1054885
theorem B1406531 : Blo 936583 1406531 := bstep (se 1 (by rfl) ⟨1054898, by rfl⟩ : syracuseStep 1406531 = 2109797) B2109797
theorem B1406561 : Blo 936583 1406561 := bstep (se 2 (by rfl) ⟨527460, by rfl⟩ : syracuseStep 1406561 = 1054921) B1054921
theorem B1406579 : Blo 936583 1406579 := bstep (se 1 (by rfl) ⟨1054934, by rfl⟩ : syracuseStep 1406579 = 2109869) B2109869
theorem B1406609 : Blo 936583 1406609 := bstep (se 2 (by rfl) ⟨527478, by rfl⟩ : syracuseStep 1406609 = 1054957) B1054957
theorem B1406627 : Blo 936583 1406627 := bstep (se 1 (by rfl) ⟨1054970, by rfl⟩ : syracuseStep 1406627 = 2109941) B2109941
theorem B1406657 : Blo 936583 1406657 := bstep (se 2 (by rfl) ⟨527496, by rfl⟩ : syracuseStep 1406657 = 1054993) B1054993
theorem B1406675 : Blo 936583 1406675 := bstep (se 1 (by rfl) ⟨1055006, by rfl⟩ : syracuseStep 1406675 = 2110013) B2110013
theorem B1406705 : Blo 936583 1406705 := bstep (se 2 (by rfl) ⟨527514, by rfl⟩ : syracuseStep 1406705 = 1055029) B1055029
theorem B1406723 : Blo 936583 1406723 := bstep (se 1 (by rfl) ⟨1055042, by rfl⟩ : syracuseStep 1406723 = 2110085) B2110085
theorem B1406753 : Blo 936583 1406753 := bstep (se 2 (by rfl) ⟨527532, by rfl⟩ : syracuseStep 1406753 = 1055065) B1055065
theorem B1406771 : Blo 936583 1406771 := bstep (se 1 (by rfl) ⟨1055078, by rfl⟩ : syracuseStep 1406771 = 2110157) B2110157
theorem B1406801 : Blo 936583 1406801 := bstep (se 2 (by rfl) ⟨527550, by rfl⟩ : syracuseStep 1406801 = 1055101) B1055101
theorem B1406819 : Blo 936583 1406819 := bstep (se 1 (by rfl) ⟨1055114, by rfl⟩ : syracuseStep 1406819 = 2110229) B2110229
theorem B1406849 : Blo 936583 1406849 := bstep (se 2 (by rfl) ⟨527568, by rfl⟩ : syracuseStep 1406849 = 1055137) B1055137
theorem B1406867 : Blo 936583 1406867 := bstep (se 1 (by rfl) ⟨1055150, by rfl⟩ : syracuseStep 1406867 = 2110301) B2110301
theorem B1406897 : Blo 936583 1406897 := bstep (se 2 (by rfl) ⟨527586, by rfl⟩ : syracuseStep 1406897 = 1055173) B1055173
theorem B1406915 : Blo 936583 1406915 := bstep (se 1 (by rfl) ⟨1055186, by rfl⟩ : syracuseStep 1406915 = 2110373) B2110373
theorem B1406945 : Blo 936583 1406945 := bstep (se 2 (by rfl) ⟨527604, by rfl⟩ : syracuseStep 1406945 = 1055209) B1055209
theorem B1406963 : Blo 936583 1406963 := bstep (se 1 (by rfl) ⟨1055222, by rfl⟩ : syracuseStep 1406963 = 2110445) B2110445
theorem B1406993 : Blo 936583 1406993 := bstep (se 2 (by rfl) ⟨527622, by rfl⟩ : syracuseStep 1406993 = 1055245) B1055245
theorem B1407011 : Blo 936583 1407011 := bstep (se 1 (by rfl) ⟨1055258, by rfl⟩ : syracuseStep 1407011 = 2110517) B2110517
theorem B3012653 : Blo 936583 3012653 := bstep (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) B1129745
theorem B1407041 : Blo 936583 1407041 := bstep (se 2 (by rfl) ⟨527640, by rfl⟩ : syracuseStep 1407041 = 1055281) B1055281
theorem B1407059 : Blo 936583 1407059 := bstep (se 1 (by rfl) ⟨1055294, by rfl⟩ : syracuseStep 1407059 = 2110589) B2110589
theorem B1407089 : Blo 936583 1407089 := bstep (se 2 (by rfl) ⟨527658, by rfl⟩ : syracuseStep 1407089 = 1055317) B1055317
theorem B3569777 : Blo 936583 3569777 := bstep (se 2 (by rfl) ⟨1338666, by rfl⟩ : syracuseStep 3569777 = 2677333) B2677333
theorem B1407107 : Blo 936583 1407107 := bstep (se 1 (by rfl) ⟨1055330, by rfl⟩ : syracuseStep 1407107 = 2110661) B2110661
theorem B1407137 : Blo 936583 1407137 := bstep (se 2 (by rfl) ⟨527676, by rfl⟩ : syracuseStep 1407137 = 1055353) B1055353
theorem B1407155 : Blo 936583 1407155 := bstep (se 1 (by rfl) ⟨1055366, by rfl⟩ : syracuseStep 1407155 = 2110733) B2110733
theorem B1407185 : Blo 936583 1407185 := bstep (se 2 (by rfl) ⟨527694, by rfl⟩ : syracuseStep 1407185 = 1055389) B1055389
theorem B1407203 : Blo 936583 1407203 := bstep (se 1 (by rfl) ⟨1055402, by rfl⟩ : syracuseStep 1407203 = 2110805) B2110805
theorem B1407233 : Blo 936583 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B1407251 : Blo 936583 1407251 := bstep (se 1 (by rfl) ⟨1055438, by rfl⟩ : syracuseStep 1407251 = 2110877) B2110877
theorem B1407281 : Blo 936583 1407281 := bstep (se 2 (by rfl) ⟨527730, by rfl⟩ : syracuseStep 1407281 = 1055461) B1055461
theorem B1407299 : Blo 936583 1407299 := bstep (se 1 (by rfl) ⟨1055474, by rfl⟩ : syracuseStep 1407299 = 2110949) B2110949
theorem B1407329 : Blo 936583 1407329 := bstep (se 2 (by rfl) ⟨527748, by rfl⟩ : syracuseStep 1407329 = 1055497) B1055497
theorem B1407347 : Blo 936583 1407347 := bstep (se 1 (by rfl) ⟨1055510, by rfl⟩ : syracuseStep 1407347 = 2111021) B2111021
theorem B1407377 : Blo 936583 1407377 := bstep (se 2 (by rfl) ⟨527766, by rfl⟩ : syracuseStep 1407377 = 1055533) B1055533
theorem B1407395 : Blo 936583 1407395 := bstep (se 1 (by rfl) ⟨1055546, by rfl⟩ : syracuseStep 1407395 = 2111093) B2111093
theorem B1505699 : Blo 936583 1505699 := bstep (se 1 (by rfl) ⟨1129274, by rfl⟩ : syracuseStep 1505699 = 2258549) B2258549
theorem B5700017 : Blo 936583 5700017 := bstep (se 2 (by rfl) ⟨2137506, by rfl⟩ : syracuseStep 5700017 = 4275013) B4275013
theorem B1407425 : Blo 936583 1407425 := bstep (se 2 (by rfl) ⟨527784, by rfl⟩ : syracuseStep 1407425 = 1055569) B1055569
theorem B1407443 : Blo 936583 1407443 := bstep (se 1 (by rfl) ⟨1055582, by rfl⟩ : syracuseStep 1407443 = 2111165) B2111165
theorem B1407473 : Blo 936583 1407473 := bstep (se 2 (by rfl) ⟨527802, by rfl⟩ : syracuseStep 1407473 = 1055605) B1055605
theorem B1407491 : Blo 936583 1407491 := bstep (se 1 (by rfl) ⟨1055618, by rfl⟩ : syracuseStep 1407491 = 2111237) B2111237
theorem B1505795 : Blo 936583 1505795 := bstep (se 1 (by rfl) ⟨1129346, by rfl⟩ : syracuseStep 1505795 = 2258693) B2258693
theorem B1407521 : Blo 936583 1407521 := bstep (se 2 (by rfl) ⟨527820, by rfl⟩ : syracuseStep 1407521 = 1055641) B1055641
theorem B1505827 : Blo 936583 1505827 := bstep (se 1 (by rfl) ⟨1129370, by rfl⟩ : syracuseStep 1505827 = 2258741) B2258741
theorem B1407539 : Blo 936583 1407539 := bstep (se 1 (by rfl) ⟨1055654, by rfl⟩ : syracuseStep 1407539 = 2111309) B2111309
theorem B1407569 : Blo 936583 1407569 := bstep (se 2 (by rfl) ⟨527838, by rfl⟩ : syracuseStep 1407569 = 1055677) B1055677
theorem B1407587 : Blo 936583 1407587 := bstep (se 1 (by rfl) ⟨1055690, by rfl⟩ : syracuseStep 1407587 = 2111381) B2111381
theorem B1407617 : Blo 936583 1407617 := bstep (se 2 (by rfl) ⟨527856, by rfl⟩ : syracuseStep 1407617 = 1055713) B1055713
theorem B5339789 : Blo 936583 5339789 := bstep (se 3 (by rfl) ⟨1001210, by rfl⟩ : syracuseStep 5339789 = 2002421) B2002421
theorem B1407635 : Blo 936583 1407635 := bstep (se 1 (by rfl) ⟨1055726, by rfl⟩ : syracuseStep 1407635 = 2111453) B2111453
theorem B4750001 : Blo 936583 4750001 := bstep (se 2 (by rfl) ⟨1781250, by rfl⟩ : syracuseStep 4750001 = 3562501) B3562501
theorem B1407665 : Blo 936583 1407665 := bstep (se 2 (by rfl) ⟨527874, by rfl⟩ : syracuseStep 1407665 = 1055749) B1055749
theorem B1407683 : Blo 936583 1407683 := bstep (se 1 (by rfl) ⟨1055762, by rfl⟩ : syracuseStep 1407683 = 2111525) B2111525
theorem B1407713 : Blo 936583 1407713 := bstep (se 2 (by rfl) ⟨527892, by rfl⟩ : syracuseStep 1407713 = 1055785) B1055785
theorem B6093539 : Blo 936583 6093539 := bstep (se 1 (by rfl) ⟨4570154, by rfl⟩ : syracuseStep 6093539 = 9140309) B9140309
theorem B1407731 : Blo 936583 1407731 := bstep (se 1 (by rfl) ⟨1055798, by rfl⟩ : syracuseStep 1407731 = 2111597) B2111597
theorem B1407761 : Blo 936583 1407761 := bstep (se 2 (by rfl) ⟨527910, by rfl⟩ : syracuseStep 1407761 = 1055821) B1055821
theorem B1374995 : Blo 936583 1374995 := bstep (se 1 (by rfl) ⟨1031246, by rfl⟩ : syracuseStep 1374995 = 2062493) B2062493
theorem B1407779 : Blo 936583 1407779 := bstep (se 1 (by rfl) ⟨1055834, by rfl⟩ : syracuseStep 1407779 = 2111669) B2111669
theorem B1407809 : Blo 936583 1407809 := bstep (se 2 (by rfl) ⟨527928, by rfl⟩ : syracuseStep 1407809 = 1055857) B1055857
theorem B1407827 : Blo 936583 1407827 := bstep (se 1 (by rfl) ⟨1055870, by rfl⟩ : syracuseStep 1407827 = 2111741) B2111741
theorem B1407857 : Blo 936583 1407857 := bstep (se 2 (by rfl) ⟨527946, by rfl⟩ : syracuseStep 1407857 = 1055893) B1055893
theorem B1407875 : Blo 936583 1407875 := bstep (se 1 (by rfl) ⟨1055906, by rfl⟩ : syracuseStep 1407875 = 2111813) B2111813
theorem B1407905 : Blo 936583 1407905 := bstep (se 2 (by rfl) ⟨527964, by rfl⟩ : syracuseStep 1407905 = 1055929) B1055929
theorem B1407923 : Blo 936583 1407923 := bstep (se 1 (by rfl) ⟨1055942, by rfl⟩ : syracuseStep 1407923 = 2111885) B2111885
theorem B1407953 : Blo 936583 1407953 := bstep (se 2 (by rfl) ⟨527982, by rfl⟩ : syracuseStep 1407953 = 1055965) B1055965
theorem B1407971 : Blo 936583 1407971 := bstep (se 1 (by rfl) ⟨1055978, by rfl⟩ : syracuseStep 1407971 = 2111957) B2111957
theorem B1408001 : Blo 936583 1408001 := bstep (se 2 (by rfl) ⟨528000, by rfl⟩ : syracuseStep 1408001 = 1056001) B1056001
theorem B1408019 : Blo 936583 1408019 := bstep (se 1 (by rfl) ⟨1056014, by rfl⟩ : syracuseStep 1408019 = 2112029) B2112029
theorem B1408049 : Blo 936583 1408049 := bstep (se 2 (by rfl) ⟨528018, by rfl⟩ : syracuseStep 1408049 = 1056037) B1056037
theorem B1408067 : Blo 936583 1408067 := bstep (se 1 (by rfl) ⟨1056050, by rfl⟩ : syracuseStep 1408067 = 2112101) B2112101
theorem B1408097 : Blo 936583 1408097 := bstep (se 2 (by rfl) ⟨528036, by rfl⟩ : syracuseStep 1408097 = 1056073) B1056073
theorem B1408115 : Blo 936583 1408115 := bstep (se 1 (by rfl) ⟨1056086, by rfl⟩ : syracuseStep 1408115 = 2112173) B2112173
theorem B1408145 : Blo 936583 1408145 := bstep (se 2 (by rfl) ⟨528054, by rfl⟩ : syracuseStep 1408145 = 1056109) B1056109
theorem B1408163 : Blo 936583 1408163 := bstep (se 1 (by rfl) ⟨1056122, by rfl⟩ : syracuseStep 1408163 = 2112245) B2112245
theorem B1408193 : Blo 936583 1408193 := bstep (se 2 (by rfl) ⟨528072, by rfl⟩ : syracuseStep 1408193 = 1056145) B1056145
theorem B1899715 : Blo 936583 1899715 := bstep (se 1 (by rfl) ⟨1424786, by rfl⟩ : syracuseStep 1899715 = 2849573) B2849573
theorem B1408211 : Blo 936583 1408211 := bstep (se 1 (by rfl) ⟨1056158, by rfl⟩ : syracuseStep 1408211 = 2112317) B2112317
theorem B1408241 : Blo 936583 1408241 := bstep (se 2 (by rfl) ⟨528090, by rfl⟩ : syracuseStep 1408241 = 1056181) B1056181
theorem B1408259 : Blo 936583 1408259 := bstep (se 1 (by rfl) ⟨1056194, by rfl⟩ : syracuseStep 1408259 = 2112389) B2112389
theorem B1408289 : Blo 936583 1408289 := bstep (se 2 (by rfl) ⟨528108, by rfl⟩ : syracuseStep 1408289 = 1056217) B1056217
theorem B1408307 : Blo 936583 1408307 := bstep (se 1 (by rfl) ⟨1056230, by rfl⟩ : syracuseStep 1408307 = 2112461) B2112461
theorem B10288453 : Blo 936583 10288453 := bstep (se 4 (by rfl) ⟨964542, by rfl⟩ : syracuseStep 10288453 = 1929085) B1929085
theorem B1408337 : Blo 936583 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B1408355 : Blo 936583 1408355 := bstep (se 1 (by rfl) ⟨1056266, by rfl⟩ : syracuseStep 1408355 = 2112533) B2112533
theorem B2850157 : Blo 936583 2850157 := bstep (se 3 (by rfl) ⟨534404, by rfl⟩ : syracuseStep 2850157 = 1068809) B1068809
theorem B1408385 : Blo 936583 1408385 := bstep (se 2 (by rfl) ⟨528144, by rfl⟩ : syracuseStep 1408385 = 1056289) B1056289
theorem B1408403 : Blo 936583 1408403 := bstep (se 1 (by rfl) ⟨1056302, by rfl⟩ : syracuseStep 1408403 = 2112605) B2112605
theorem B1408433 : Blo 936583 1408433 := bstep (se 2 (by rfl) ⟨528162, by rfl⟩ : syracuseStep 1408433 = 1056325) B1056325
theorem B1408451 : Blo 936583 1408451 := bstep (se 1 (by rfl) ⟨1056338, by rfl⟩ : syracuseStep 1408451 = 2112677) B2112677
theorem B1408481 : Blo 936583 1408481 := bstep (se 2 (by rfl) ⟨528180, by rfl⟩ : syracuseStep 1408481 = 1056361) B1056361
theorem B1408499 : Blo 936583 1408499 := bstep (se 1 (by rfl) ⟨1056374, by rfl⟩ : syracuseStep 1408499 = 2112749) B2112749
theorem B1408529 : Blo 936583 1408529 := bstep (se 2 (by rfl) ⟨528198, by rfl⟩ : syracuseStep 1408529 = 1056397) B1056397
theorem B1408547 : Blo 936583 1408547 := bstep (se 1 (by rfl) ⟨1056410, by rfl⟩ : syracuseStep 1408547 = 2112821) B2112821
theorem B3571235 : Blo 936583 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B3571249 : Blo 936583 3571249 := bstep (se 2 (by rfl) ⟨1339218, by rfl⟩ : syracuseStep 3571249 = 2678437) B2678437
theorem B1408577 : Blo 936583 1408577 := bstep (se 2 (by rfl) ⟨528216, by rfl⟩ : syracuseStep 1408577 = 1056433) B1056433
theorem B1408595 : Blo 936583 1408595 := bstep (se 1 (by rfl) ⟨1056446, by rfl⟩ : syracuseStep 1408595 = 2112893) B2112893
theorem B1408625 : Blo 936583 1408625 := bstep (se 2 (by rfl) ⟨528234, by rfl⟩ : syracuseStep 1408625 = 1056469) B1056469
theorem B1408643 : Blo 936583 1408643 := bstep (se 1 (by rfl) ⟨1056482, by rfl⟩ : syracuseStep 1408643 = 2112965) B2112965
theorem B1408673 : Blo 936583 1408673 := bstep (se 2 (by rfl) ⟨528252, by rfl⟩ : syracuseStep 1408673 = 1056505) B1056505
theorem B1408691 : Blo 936583 1408691 := bstep (se 1 (by rfl) ⟨1056518, by rfl⟩ : syracuseStep 1408691 = 2113037) B2113037
theorem B1408721 : Blo 936583 1408721 := bstep (se 2 (by rfl) ⟨528270, by rfl⟩ : syracuseStep 1408721 = 1056541) B1056541
theorem B1408739 : Blo 936583 1408739 := bstep (se 1 (by rfl) ⟨1056554, by rfl⟩ : syracuseStep 1408739 = 2113109) B2113109
theorem B6094577 : Blo 936583 6094577 := bstep (se 2 (by rfl) ⟨2285466, by rfl⟩ : syracuseStep 6094577 = 4570933) B4570933
theorem B1408769 : Blo 936583 1408769 := bstep (se 2 (by rfl) ⟨528288, by rfl⟩ : syracuseStep 1408769 = 1056577) B1056577
theorem B1408787 : Blo 936583 1408787 := bstep (se 1 (by rfl) ⟨1056590, by rfl⟩ : syracuseStep 1408787 = 2113181) B2113181
theorem B1408817 : Blo 936583 1408817 := bstep (se 2 (by rfl) ⟨528306, by rfl⟩ : syracuseStep 1408817 = 1056613) B1056613
theorem B1408835 : Blo 936583 1408835 := bstep (se 1 (by rfl) ⟨1056626, by rfl⟩ : syracuseStep 1408835 = 2113253) B2113253
theorem B1408865 : Blo 936583 1408865 := bstep (se 2 (by rfl) ⟨528324, by rfl⟩ : syracuseStep 1408865 = 1056649) B1056649
theorem B1408883 : Blo 936583 1408883 := bstep (se 1 (by rfl) ⟨1056662, by rfl⟩ : syracuseStep 1408883 = 2113325) B2113325
theorem B1408913 : Blo 936583 1408913 := bstep (se 2 (by rfl) ⟨528342, by rfl⟩ : syracuseStep 1408913 = 1056685) B1056685
theorem B1605539 : Blo 936583 1605539 := bstep (se 1 (by rfl) ⟨1204154, by rfl⟩ : syracuseStep 1605539 = 2408309) B2408309
theorem B6422435 : Blo 936583 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B1408931 : Blo 936583 1408931 := bstep (se 1 (by rfl) ⟨1056698, by rfl⟩ : syracuseStep 1408931 = 2113397) B2113397
theorem B1408961 : Blo 936583 1408961 := bstep (se 2 (by rfl) ⟨528360, by rfl⟩ : syracuseStep 1408961 = 1056721) B1056721
theorem B1605587 : Blo 936583 1605587 := bstep (se 1 (by rfl) ⟨1204190, by rfl⟩ : syracuseStep 1605587 = 2408381) B2408381
theorem B1408979 : Blo 936583 1408979 := bstep (se 1 (by rfl) ⟨1056734, by rfl⟩ : syracuseStep 1408979 = 2113469) B2113469
theorem B1409009 : Blo 936583 1409009 := bstep (se 2 (by rfl) ⟨528378, by rfl⟩ : syracuseStep 1409009 = 1056757) B1056757
theorem B1409099 : Blo 936583 1409099 := bstep (se 1 (by rfl) ⟨1056824, by rfl⟩ : syracuseStep 1409099 = 2113649) B2113649
theorem B1409111 : Blo 936583 1409111 := bstep (se 1 (by rfl) ⟨1056833, by rfl⟩ : syracuseStep 1409111 = 2113667) B2113667
theorem B3801181 : Blo 936583 3801181 := bstep (se 3 (by rfl) ⟨712721, by rfl⟩ : syracuseStep 3801181 = 1425443) B1425443
theorem B1409177 : Blo 936583 1409177 := bstep (se 2 (by rfl) ⟨528441, by rfl⟩ : syracuseStep 1409177 = 1056883) B1056883
theorem B8552627 : Blo 936583 8552627 := bstep (se 1 (by rfl) ⟨6414470, by rfl⟩ : syracuseStep 8552627 = 12828941) B12828941
theorem B1409291 : Blo 936583 1409291 := bstep (se 1 (by rfl) ⟨1056968, by rfl⟩ : syracuseStep 1409291 = 2113937) B2113937
theorem B1409303 : Blo 936583 1409303 := bstep (se 1 (by rfl) ⟨1056977, by rfl⟩ : syracuseStep 1409303 = 2113955) B2113955
theorem B1409369 : Blo 936583 1409369 := bstep (se 2 (by rfl) ⟨528513, by rfl⟩ : syracuseStep 1409369 = 1057027) B1057027
theorem B1409483 : Blo 936583 1409483 := bstep (se 1 (by rfl) ⟨1057112, by rfl⟩ : syracuseStep 1409483 = 2114225) B2114225
theorem B1409495 : Blo 936583 1409495 := bstep (se 1 (by rfl) ⟨1057121, by rfl⟩ : syracuseStep 1409495 = 2114243) B2114243
theorem B11403737 : Blo 936583 11403737 := bstep (se 2 (by rfl) ⟨4276401, by rfl⟩ : syracuseStep 11403737 = 8552803) B8552803
theorem B1409561 : Blo 936583 1409561 := bstep (se 2 (by rfl) ⟨528585, by rfl⟩ : syracuseStep 1409561 = 1057171) B1057171
theorem B2851421 : Blo 936583 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B1409675 : Blo 936583 1409675 := bstep (se 1 (by rfl) ⟨1057256, by rfl⟩ : syracuseStep 1409675 = 2114513) B2114513
theorem B1409687 : Blo 936583 1409687 := bstep (se 1 (by rfl) ⟨1057265, by rfl⟩ : syracuseStep 1409687 = 2114531) B2114531
theorem B10158797 : Blo 936583 10158797 := bstep (se 3 (by rfl) ⟨1904774, by rfl⟩ : syracuseStep 10158797 = 3809549) B3809549
theorem B1409753 : Blo 936583 1409753 := bstep (se 2 (by rfl) ⟨528657, by rfl⟩ : syracuseStep 1409753 = 1057315) B1057315
theorem B1901387 : Blo 936583 1901387 := bstep (se 1 (by rfl) ⟨1426040, by rfl⟩ : syracuseStep 1901387 = 2852081) B2852081
theorem B1409867 : Blo 936583 1409867 := bstep (se 1 (by rfl) ⟨1057400, by rfl⟩ : syracuseStep 1409867 = 2114801) B2114801
theorem B1409879 : Blo 936583 1409879 := bstep (se 1 (by rfl) ⟨1057409, by rfl⟩ : syracuseStep 1409879 = 2114819) B2114819
theorem B1409945 : Blo 936583 1409945 := bstep (se 2 (by rfl) ⟨528729, by rfl⟩ : syracuseStep 1409945 = 1057459) B1057459
theorem B1410059 : Blo 936583 1410059 := bstep (se 1 (by rfl) ⟨1057544, by rfl⟩ : syracuseStep 1410059 = 2115089) B2115089
theorem B1410071 : Blo 936583 1410071 := bstep (se 1 (by rfl) ⟨1057553, by rfl⟩ : syracuseStep 1410071 = 2115107) B2115107
theorem B5342273 : Blo 936583 5342273 := bstep (se 2 (by rfl) ⟨2003352, by rfl⟩ : syracuseStep 5342273 = 4006705) B4006705
theorem B1410137 : Blo 936583 1410137 := bstep (se 2 (by rfl) ⟨528801, by rfl⟩ : syracuseStep 1410137 = 1057603) B1057603
theorem B1410251 : Blo 936583 1410251 := bstep (se 1 (by rfl) ⟨1057688, by rfl⟩ : syracuseStep 1410251 = 2115377) B2115377
theorem B1410263 : Blo 936583 1410263 := bstep (se 1 (by rfl) ⟨1057697, by rfl⟩ : syracuseStep 1410263 = 2115395) B2115395
theorem B3376349 : Blo 936583 3376349 := bstep (se 3 (by rfl) ⟨633065, by rfl⟩ : syracuseStep 3376349 = 1266131) B1266131
theorem B1410329 : Blo 936583 1410329 := bstep (se 2 (by rfl) ⟨528873, by rfl⟩ : syracuseStep 1410329 = 1057747) B1057747
theorem B1410443 : Blo 936583 1410443 := bstep (se 1 (by rfl) ⟨1057832, by rfl⟩ : syracuseStep 1410443 = 2115665) B2115665
theorem B1410455 : Blo 936583 1410455 := bstep (se 1 (by rfl) ⟨1057841, by rfl⟩ : syracuseStep 1410455 = 2115683) B2115683
theorem B1410521 : Blo 936583 1410521 := bstep (se 2 (by rfl) ⟨528945, by rfl⟩ : syracuseStep 1410521 = 1057891) B1057891
theorem B2000371 : Blo 936583 2000371 := bstep (se 1 (by rfl) ⟨1500278, by rfl⟩ : syracuseStep 2000371 = 3000557) B3000557
theorem B1410635 : Blo 936583 1410635 := bstep (se 1 (by rfl) ⟨1057976, by rfl⟩ : syracuseStep 1410635 = 2115953) B2115953
theorem B1410647 : Blo 936583 1410647 := bstep (se 1 (by rfl) ⟨1057985, by rfl⟩ : syracuseStep 1410647 = 2115971) B2115971
theorem B3606167 : Blo 936583 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B1410713 : Blo 936583 1410713 := bstep (se 2 (by rfl) ⟨529017, by rfl⟩ : syracuseStep 1410713 = 1058035) B1058035
theorem B2000627 : Blo 936583 2000627 := bstep (se 1 (by rfl) ⟨1500470, by rfl⟩ : syracuseStep 2000627 = 3000941) B3000941
theorem B1410827 : Blo 936583 1410827 := bstep (se 1 (by rfl) ⟨1058120, by rfl⟩ : syracuseStep 1410827 = 2116241) B2116241
theorem B1410839 : Blo 936583 1410839 := bstep (se 1 (by rfl) ⟨1058129, by rfl⟩ : syracuseStep 1410839 = 2116259) B2116259
theorem B1017803 : Blo 936583 1017803 := bstep (se 1 (by rfl) ⟨763352, by rfl⟩ : syracuseStep 1017803 = 1526705) B1526705
theorem B3606551 : Blo 936583 3606551 := bstep (se 1 (by rfl) ⟨2704913, by rfl⟩ : syracuseStep 3606551 = 5409827) B5409827
theorem B7604441 : Blo 936583 7604441 := bstep (se 2 (by rfl) ⟨2851665, by rfl⟩ : syracuseStep 7604441 = 5703331) B5703331
theorem B5409089 : Blo 936583 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B5081561 : Blo 936583 5081561 := bstep (se 2 (by rfl) ⟨1905585, by rfl⟩ : syracuseStep 5081561 = 3811171) B3811171
theorem B4754051 : Blo 936583 4754051 := bstep (se 1 (by rfl) ⟨3565538, by rfl⟩ : syracuseStep 4754051 = 7131077) B7131077
theorem B2001601 : Blo 936583 2001601 := bstep (se 2 (by rfl) ⟨750600, by rfl⟩ : syracuseStep 2001601 = 1501201) B1501201
theorem B4000691 : Blo 936583 4000691 := bstep (se 1 (by rfl) ⟨3000518, by rfl⟩ : syracuseStep 4000691 = 6001037) B6001037
theorem B4000843 : Blo 936583 4000843 := bstep (se 1 (by rfl) ⟨3000632, by rfl⟩ : syracuseStep 4000843 = 6001265) B6001265
theorem B4000913 : Blo 936583 4000913 := bstep (se 2 (by rfl) ⟨1500342, by rfl⟩ : syracuseStep 4000913 = 3000685) B3000685
theorem B5344663 : Blo 936583 5344663 := bstep (se 1 (by rfl) ⟨4008497, by rfl⟩ : syracuseStep 5344663 = 8016995) B8016995
theorem B1806041 : Blo 936583 1806041 := bstep (se 2 (by rfl) ⟨677265, by rfl⟩ : syracuseStep 1806041 = 1354531) B1354531
theorem B3805073 : Blo 936583 3805073 := bstep (se 2 (by rfl) ⟨1426902, by rfl⟩ : syracuseStep 3805073 = 2853805) B2853805
theorem B1806295 : Blo 936583 1806295 := bstep (se 1 (by rfl) ⟨1354721, by rfl⟩ : syracuseStep 1806295 = 2709443) B2709443
theorem B3805201 : Blo 936583 3805201 := bstep (se 2 (by rfl) ⟨1426950, by rfl⟩ : syracuseStep 3805201 = 2853901) B2853901
theorem B3379403 : Blo 936583 3379403 := bstep (se 1 (by rfl) ⟨2534552, by rfl⟩ : syracuseStep 3379403 = 5069105) B5069105
theorem B12357953 : Blo 936583 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B3379735 : Blo 936583 3379735 := bstep (se 1 (by rfl) ⟨2534801, by rfl⟩ : syracuseStep 3379735 = 5069603) B5069603
theorem B3052121 : Blo 936583 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B7115525 : Blo 936583 7115525 := bstep (se 4 (by rfl) ⟨667080, by rfl⟩ : syracuseStep 7115525 = 1334161) B1334161
theorem B2003737 : Blo 936583 2003737 := bstep (se 2 (by rfl) ⟨751401, by rfl⟩ : syracuseStep 2003737 = 1502803) B1502803
theorem B4002605 : Blo 936583 4002605 := bstep (se 3 (by rfl) ⟨750488, by rfl⟩ : syracuseStep 4002605 = 1500977) B1500977
theorem B1053751 : Blo 936583 1053751 := bstep (se 1 (by rfl) ⟨790313, by rfl⟩ : syracuseStep 1053751 = 1580627) B1580627
theorem B1053931 : Blo 936583 1053931 := bstep (se 1 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 1053931 = 1580897) B1580897
theorem B1905943 : Blo 936583 1905943 := bstep (se 1 (by rfl) ⟨1429457, by rfl⟩ : syracuseStep 1905943 = 2858915) B2858915
theorem B1054039 : Blo 936583 1054039 := bstep (se 1 (by rfl) ⟨790529, by rfl⟩ : syracuseStep 1054039 = 1581059) B1581059
theorem B8033741 : Blo 936583 8033741 := bstep (se 3 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 8033741 = 3012653) B3012653
theorem B4003289 : Blo 936583 4003289 := bstep (se 2 (by rfl) ⟨1501233, by rfl⟩ : syracuseStep 4003289 = 3002467) B3002467
theorem B1054219 : Blo 936583 1054219 := bstep (se 1 (by rfl) ⟨790664, by rfl⟩ : syracuseStep 1054219 = 1581329) B1581329
theorem B1054327 : Blo 936583 1054327 := bstep (se 1 (by rfl) ⟨790745, by rfl⟩ : syracuseStep 1054327 = 1581491) B1581491
theorem B1808011 : Blo 936583 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B1054507 : Blo 936583 1054507 := bstep (se 1 (by rfl) ⟨790880, by rfl⟩ : syracuseStep 1054507 = 1581761) B1581761
theorem B1054615 : Blo 936583 1054615 := bstep (se 1 (by rfl) ⟨790961, by rfl⟩ : syracuseStep 1054615 = 1581923) B1581923
theorem B1054795 : Blo 936583 1054795 := bstep (se 1 (by rfl) ⟨791096, by rfl⟩ : syracuseStep 1054795 = 1582193) B1582193
theorem B1185931 : Blo 936583 1185931 := bstep (se 1 (by rfl) ⟨889448, by rfl⟩ : syracuseStep 1185931 = 1778897) B1778897
theorem B3381421 : Blo 936583 3381421 := bstep (se 3 (by rfl) ⟨634016, by rfl⟩ : syracuseStep 3381421 = 1268033) B1268033
theorem B1054903 : Blo 936583 1054903 := bstep (se 1 (by rfl) ⟨791177, by rfl⟩ : syracuseStep 1054903 = 1582355) B1582355
theorem B6002905 : Blo 936583 6002905 := bstep (se 2 (by rfl) ⟨2251089, by rfl⟩ : syracuseStep 6002905 = 4502179) B4502179
theorem B4757777 : Blo 936583 4757777 := bstep (se 2 (by rfl) ⟨1784166, by rfl⟩ : syracuseStep 4757777 = 3568333) B3568333
theorem B18061613 : Blo 936583 18061613 := bstep (se 3 (by rfl) ⟨3386552, by rfl⟩ : syracuseStep 18061613 = 6773105) B6773105
theorem B1055083 : Blo 936583 1055083 := bstep (se 1 (by rfl) ⟨791312, by rfl⟩ : syracuseStep 1055083 = 1582625) B1582625
theorem B4757939 : Blo 936583 4757939 := bstep (se 1 (by rfl) ⟨3568454, by rfl⟩ : syracuseStep 4757939 = 7136909) B7136909
theorem B1055191 : Blo 936583 1055191 := bstep (se 1 (by rfl) ⟨791393, by rfl⟩ : syracuseStep 1055191 = 1582787) B1582787
theorem B6855203 : Blo 936583 6855203 := bstep (se 1 (by rfl) ⟨5141402, by rfl⟩ : syracuseStep 6855203 = 10282805) B10282805
theorem B9017891 : Blo 936583 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B10164811 : Blo 936583 10164811 := bstep (se 1 (by rfl) ⟨7623608, by rfl⟩ : syracuseStep 10164811 = 15247217) B15247217
theorem B1055371 : Blo 936583 1055371 := bstep (se 1 (by rfl) ⟨791528, by rfl⟩ : syracuseStep 1055371 = 1583057) B1583057
theorem B1055479 : Blo 936583 1055479 := bstep (se 1 (by rfl) ⟨791609, by rfl⟩ : syracuseStep 1055479 = 1583219) B1583219
theorem B6003521 : Blo 936583 6003521 := bstep (se 2 (by rfl) ⟨2251320, by rfl⟩ : syracuseStep 6003521 = 4502641) B4502641
theorem B10132289 : Blo 936583 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B2857793 : Blo 936583 2857793 := bstep (se 2 (by rfl) ⟨1071672, by rfl⟩ : syracuseStep 2857793 = 2143345) B2143345
theorem B2005889 : Blo 936583 2005889 := bstep (se 2 (by rfl) ⟨752208, by rfl⟩ : syracuseStep 2005889 = 1504417) B1504417
theorem B1055659 : Blo 936583 1055659 := bstep (se 1 (by rfl) ⟨791744, by rfl⟩ : syracuseStep 1055659 = 1583489) B1583489
theorem B2005975 : Blo 936583 2005975 := bstep (se 1 (by rfl) ⟨1504481, by rfl⟩ : syracuseStep 2005975 = 3008963) B3008963
theorem B1055767 : Blo 936583 1055767 := bstep (se 1 (by rfl) ⟨791825, by rfl⟩ : syracuseStep 1055767 = 1583651) B1583651
theorem B1186903 : Blo 936583 1186903 := bstep (se 1 (by rfl) ⟨890177, by rfl⟩ : syracuseStep 1186903 = 1780355) B1780355
theorem B7117955 : Blo 936583 7117955 := bstep (se 1 (by rfl) ⟨5338466, by rfl⟩ : syracuseStep 7117955 = 10676933) B10676933
theorem B1055947 : Blo 936583 1055947 := bstep (se 1 (by rfl) ⟨791960, by rfl⟩ : syracuseStep 1055947 = 1583921) B1583921
theorem B1056055 : Blo 936583 1056055 := bstep (se 1 (by rfl) ⟨792041, by rfl⟩ : syracuseStep 1056055 = 1584083) B1584083
theorem B1056235 : Blo 936583 1056235 := bstep (se 1 (by rfl) ⟨792176, by rfl⟩ : syracuseStep 1056235 = 1584353) B1584353
theorem B1056343 : Blo 936583 1056343 := bstep (se 1 (by rfl) ⟨792257, by rfl⟩ : syracuseStep 1056343 = 1584515) B1584515
theorem B1056523 : Blo 936583 1056523 := bstep (se 1 (by rfl) ⟨792392, by rfl⟩ : syracuseStep 1056523 = 1584785) B1584785
theorem B2006795 : Blo 936583 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B5578571 : Blo 936583 5578571 := bstep (se 1 (by rfl) ⟨4183928, by rfl⟩ : syracuseStep 5578571 = 8367857) B8367857
theorem B7610213 : Blo 936583 7610213 := bstep (se 4 (by rfl) ⟨713457, by rfl⟩ : syracuseStep 7610213 = 1426915) B1426915
theorem B1056631 : Blo 936583 1056631 := bstep (se 1 (by rfl) ⟨792473, by rfl⟩ : syracuseStep 1056631 = 1584947) B1584947
theorem B1187723 : Blo 936583 1187723 := bstep (se 1 (by rfl) ⟨890792, by rfl⟩ : syracuseStep 1187723 = 1781585) B1781585
theorem B1580951 : Blo 936583 1580951 := bstep (se 1 (by rfl) ⟨1185713, by rfl⟩ : syracuseStep 1580951 = 2371427) B2371427
theorem B1581079 : Blo 936583 1581079 := bstep (se 1 (by rfl) ⟨1185809, by rfl⟩ : syracuseStep 1581079 = 2371619) B2371619
theorem B1056811 : Blo 936583 1056811 := bstep (se 1 (by rfl) ⟨792608, by rfl⟩ : syracuseStep 1056811 = 1585217) B1585217
theorem B3383441 : Blo 936583 3383441 := bstep (se 2 (by rfl) ⟨1268790, by rfl⟩ : syracuseStep 3383441 = 2537581) B2537581
theorem B1056919 : Blo 936583 1056919 := bstep (se 1 (by rfl) ⟨792689, by rfl⟩ : syracuseStep 1056919 = 1585379) B1585379
theorem B1057099 : Blo 936583 1057099 := bstep (se 1 (by rfl) ⟨792824, by rfl⟩ : syracuseStep 1057099 = 1585649) B1585649
theorem B4759883 : Blo 936583 4759883 := bstep (se 1 (by rfl) ⟨3569912, by rfl⟩ : syracuseStep 4759883 = 7139825) B7139825
theorem B13508963 : Blo 936583 13508963 := bstep (se 1 (by rfl) ⟨10131722, by rfl⟩ : syracuseStep 13508963 = 20263445) B20263445
theorem B1057207 : Blo 936583 1057207 := bstep (se 1 (by rfl) ⟨792905, by rfl⟩ : syracuseStep 1057207 = 1585811) B1585811
theorem B2859571 : Blo 936583 2859571 := bstep (se 1 (by rfl) ⟨2144678, by rfl⟩ : syracuseStep 2859571 = 4289357) B4289357
theorem B14426693 : Blo 936583 14426693 := bstep (se 4 (by rfl) ⟨1352502, by rfl⟩ : syracuseStep 14426693 = 2705005) B2705005
theorem B2531915 : Blo 936583 2531915 := bstep (se 1 (by rfl) ⟨1898936, by rfl⟩ : syracuseStep 2531915 = 3797873) B3797873
theorem B1188427 : Blo 936583 1188427 := bstep (se 1 (by rfl) ⟨891320, by rfl⟩ : syracuseStep 1188427 = 1782641) B1782641
theorem B1057387 : Blo 936583 1057387 := bstep (se 1 (by rfl) ⟨793040, by rfl⟩ : syracuseStep 1057387 = 1586081) B1586081
theorem B1581707 : Blo 936583 1581707 := bstep (se 1 (by rfl) ⟨1186280, by rfl⟩ : syracuseStep 1581707 = 2372561) B2372561
theorem B1057495 : Blo 936583 1057495 := bstep (se 1 (by rfl) ⟨793121, by rfl⟩ : syracuseStep 1057495 = 1586243) B1586243
theorem B2007769 : Blo 936583 2007769 := bstep (se 2 (by rfl) ⟨752913, by rfl⟩ : syracuseStep 2007769 = 1505827) B1505827
theorem B1581835 : Blo 936583 1581835 := bstep (se 1 (by rfl) ⟨1186376, by rfl⟩ : syracuseStep 1581835 = 2372753) B2372753
theorem B4006721 : Blo 936583 4006721 := bstep (se 2 (by rfl) ⟨1502520, by rfl⟩ : syracuseStep 4006721 = 3005041) B3005041
theorem B1188695 : Blo 936583 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B1057675 : Blo 936583 1057675 := bstep (se 1 (by rfl) ⟨793256, by rfl⟩ : syracuseStep 1057675 = 1586513) B1586513
theorem B3810199 : Blo 936583 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B1581977 : Blo 936583 1581977 := bstep (se 2 (by rfl) ⟨593241, by rfl⟩ : syracuseStep 1581977 = 1186483) B1186483
theorem B1057783 : Blo 936583 1057783 := bstep (se 1 (by rfl) ⟨793337, by rfl⟩ : syracuseStep 1057783 = 1586675) B1586675
theorem B1778699 : Blo 936583 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B1582105 : Blo 936583 1582105 := bstep (se 2 (by rfl) ⟨593289, by rfl⟩ : syracuseStep 1582105 = 1186579) B1186579
theorem B1778753 : Blo 936583 1778753 := bstep (se 2 (by rfl) ⟨667032, by rfl⟩ : syracuseStep 1778753 = 1334065) B1334065
theorem B4007063 : Blo 936583 4007063 := bstep (se 1 (by rfl) ⟨3005297, by rfl⟩ : syracuseStep 4007063 = 6010595) B6010595
theorem B1057963 : Blo 936583 1057963 := bstep (se 1 (by rfl) ⟨793472, by rfl⟩ : syracuseStep 1057963 = 1586945) B1586945
theorem B1058071 : Blo 936583 1058071 := bstep (se 1 (by rfl) ⟨793553, by rfl⟩ : syracuseStep 1058071 = 1587107) B1587107
theorem B1189399 : Blo 936583 1189399 := bstep (se 1 (by rfl) ⟨892049, by rfl⟩ : syracuseStep 1189399 = 1784099) B1784099
theorem B1582679 : Blo 936583 1582679 := bstep (se 1 (by rfl) ⟨1187009, by rfl⟩ : syracuseStep 1582679 = 2374019) B2374019
theorem B2532953 : Blo 936583 2532953 := bstep (se 2 (by rfl) ⟨949857, by rfl⟩ : syracuseStep 2532953 = 1899715) B1899715
theorem B1582807 : Blo 936583 1582807 := bstep (se 1 (by rfl) ⟨1187105, by rfl⟩ : syracuseStep 1582807 = 2374211) B2374211
theorem B3614557 : Blo 936583 3614557 := bstep (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) B1355459
theorem B1779671 : Blo 936583 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B2107403 : Blo 936583 2107403 := bstep (se 1 (by rfl) ⟨1580552, by rfl⟩ : syracuseStep 2107403 = 3161105) B3161105
theorem B4007987 : Blo 936583 4007987 := bstep (se 1 (by rfl) ⟨3005990, by rfl⟩ : syracuseStep 4007987 = 6011981) B6011981
theorem B2107457 : Blo 936583 2107457 := bstep (se 2 (by rfl) ⟨790296, by rfl⟩ : syracuseStep 2107457 = 1580593) B1580593
theorem B4761665 : Blo 936583 4761665 := bstep (se 2 (by rfl) ⟨1785624, by rfl⟩ : syracuseStep 4761665 = 3571249) B3571249
theorem B300394565 : Blo 936583 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B2107673 : Blo 936583 2107673 := bstep (se 2 (by rfl) ⟨790377, by rfl⟩ : syracuseStep 2107673 = 1580755) B1580755
theorem B1583435 : Blo 936583 1583435 := bstep (se 1 (by rfl) ⟨1187576, by rfl⟩ : syracuseStep 1583435 = 2375153) B2375153
theorem B2107763 : Blo 936583 2107763 := bstep (se 1 (by rfl) ⟨1580822, by rfl⟩ : syracuseStep 2107763 = 3161645) B3161645
theorem B2107799 : Blo 936583 2107799 := bstep (se 1 (by rfl) ⟨1580849, by rfl⟩ : syracuseStep 2107799 = 3161699) B3161699
theorem B1583563 : Blo 936583 1583563 := bstep (se 1 (by rfl) ⟨1187672, by rfl⟩ : syracuseStep 1583563 = 2375345) B2375345
theorem B7121357 : Blo 936583 7121357 := bstep (se 3 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 7121357 = 2670509) B2670509
theorem B1780211 : Blo 936583 1780211 := bstep (se 1 (by rfl) ⟨1335158, by rfl⟩ : syracuseStep 1780211 = 2670317) B2670317
theorem B5351953 : Blo 936583 5351953 := bstep (se 2 (by rfl) ⟨2006982, by rfl⟩ : syracuseStep 5351953 = 4013965) B4013965
theorem B3385921 : Blo 936583 3385921 := bstep (se 2 (by rfl) ⟨1269720, by rfl⟩ : syracuseStep 3385921 = 2539441) B2539441
theorem B2107979 : Blo 936583 2107979 := bstep (se 1 (by rfl) ⟨1580984, by rfl⟩ : syracuseStep 2107979 = 3161969) B3161969
theorem B1583705 : Blo 936583 1583705 := bstep (se 2 (by rfl) ⟨593889, by rfl⟩ : syracuseStep 1583705 = 1187779) B1187779
theorem B2108033 : Blo 936583 2108033 := bstep (se 2 (by rfl) ⟨790512, by rfl⟩ : syracuseStep 2108033 = 1581025) B1581025
theorem B1583833 : Blo 936583 1583833 := bstep (se 2 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 1583833 = 1187875) B1187875
theorem B2108249 : Blo 936583 2108249 := bstep (se 2 (by rfl) ⟨790593, by rfl⟩ : syracuseStep 2108249 = 1581187) B1581187
theorem B2108339 : Blo 936583 2108339 := bstep (se 1 (by rfl) ⟨1581254, by rfl⟩ : syracuseStep 2108339 = 3162509) B3162509
theorem B7121843 : Blo 936583 7121843 := bstep (se 1 (by rfl) ⟨5341382, by rfl⟩ : syracuseStep 7121843 = 10682765) B10682765
theorem B3812275 : Blo 936583 3812275 := bstep (se 1 (by rfl) ⟨2859206, by rfl⟩ : syracuseStep 3812275 = 5718413) B5718413
theorem B2108375 : Blo 936583 2108375 := bstep (se 1 (by rfl) ⟨1581281, by rfl⟩ : syracuseStep 2108375 = 3162563) B3162563
theorem B1780697 : Blo 936583 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B4008977 : Blo 936583 4008977 := bstep (se 2 (by rfl) ⟨1503366, by rfl⟩ : syracuseStep 4008977 = 3006733) B3006733
theorem B2108555 : Blo 936583 2108555 := bstep (se 1 (by rfl) ⟨1581416, by rfl⟩ : syracuseStep 2108555 = 3162833) B3162833
theorem B2108609 : Blo 936583 2108609 := bstep (se 2 (by rfl) ⟨790728, by rfl⟩ : syracuseStep 2108609 = 1581457) B1581457
theorem B1584407 : Blo 936583 1584407 := bstep (se 1 (by rfl) ⟨1188305, by rfl⟩ : syracuseStep 1584407 = 2376611) B2376611
theorem B1584535 : Blo 936583 1584535 := bstep (se 1 (by rfl) ⟨1188401, by rfl⟩ : syracuseStep 1584535 = 2376803) B2376803
theorem B2108825 : Blo 936583 2108825 := bstep (se 2 (by rfl) ⟨790809, by rfl⟩ : syracuseStep 2108825 = 1581619) B1581619
theorem B2108915 : Blo 936583 2108915 := bstep (se 1 (by rfl) ⟨1581686, by rfl⟩ : syracuseStep 2108915 = 3163373) B3163373
theorem B2108951 : Blo 936583 2108951 := bstep (se 1 (by rfl) ⟨1581713, by rfl⟩ : syracuseStep 2108951 = 3163427) B3163427
theorem B2371265 : Blo 936583 2371265 := bstep (se 2 (by rfl) ⟨889224, by rfl⟩ : syracuseStep 2371265 = 1778449) B1778449
theorem B2109131 : Blo 936583 2109131 := bstep (se 1 (by rfl) ⟨1581848, by rfl⟩ : syracuseStep 2109131 = 3163697) B3163697
theorem B2109185 : Blo 936583 2109185 := bstep (se 2 (by rfl) ⟨790944, by rfl⟩ : syracuseStep 2109185 = 1581889) B1581889
theorem B2109401 : Blo 936583 2109401 := bstep (se 2 (by rfl) ⟨791025, by rfl⟩ : syracuseStep 2109401 = 1582051) B1582051
theorem B1585163 : Blo 936583 1585163 := bstep (se 1 (by rfl) ⟨1188872, by rfl⟩ : syracuseStep 1585163 = 2377745) B2377745
theorem B2109491 : Blo 936583 2109491 := bstep (se 1 (by rfl) ⟨1582118, by rfl⟩ : syracuseStep 2109491 = 3164237) B3164237
theorem B2109527 : Blo 936583 2109527 := bstep (se 1 (by rfl) ⟨1582145, by rfl⟩ : syracuseStep 2109527 = 3164291) B3164291
theorem B1585291 : Blo 936583 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B2371801 : Blo 936583 2371801 := bstep (se 2 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 2371801 = 1778851) B1778851
theorem B2109707 : Blo 936583 2109707 := bstep (se 1 (by rfl) ⟨1582280, by rfl⟩ : syracuseStep 2109707 = 3164561) B3164561
theorem B1585433 : Blo 936583 1585433 := bstep (se 2 (by rfl) ⟨594537, by rfl⟩ : syracuseStep 1585433 = 1189075) B1189075
theorem B2109761 : Blo 936583 2109761 := bstep (se 2 (by rfl) ⟨791160, by rfl⟩ : syracuseStep 2109761 = 1582321) B1582321
theorem B7614785 : Blo 936583 7614785 := bstep (se 2 (by rfl) ⟨2855544, by rfl⟩ : syracuseStep 7614785 = 5711089) B5711089
theorem B7123301 : Blo 936583 7123301 := bstep (se 4 (by rfl) ⟨667809, by rfl⟩ : syracuseStep 7123301 = 1335619) B1335619
theorem B1782155 : Blo 936583 1782155 := bstep (se 1 (by rfl) ⟨1336616, by rfl⟩ : syracuseStep 1782155 = 2673233) B2673233
theorem B1585561 : Blo 936583 1585561 := bstep (se 2 (by rfl) ⟨594585, by rfl⟩ : syracuseStep 1585561 = 1189171) B1189171
theorem B8565209 : Blo 936583 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B2109977 : Blo 936583 2109977 := bstep (se 2 (by rfl) ⟨791241, by rfl⟩ : syracuseStep 2109977 = 1582483) B1582483
theorem B1782337 : Blo 936583 1782337 := bstep (se 2 (by rfl) ⟨668376, by rfl⟩ : syracuseStep 1782337 = 1336753) B1336753
theorem B2110067 : Blo 936583 2110067 := bstep (se 1 (by rfl) ⟨1582550, by rfl⟩ : syracuseStep 2110067 = 3165101) B3165101
theorem B2110103 : Blo 936583 2110103 := bstep (se 1 (by rfl) ⟨1582577, by rfl⟩ : syracuseStep 2110103 = 3165155) B3165155
theorem B2110283 : Blo 936583 2110283 := bstep (se 1 (by rfl) ⟨1582712, by rfl⟩ : syracuseStep 2110283 = 3165425) B3165425
theorem B7123787 : Blo 936583 7123787 := bstep (se 1 (by rfl) ⟨5342840, by rfl⟩ : syracuseStep 7123787 = 10685681) B10685681
theorem B2110337 : Blo 936583 2110337 := bstep (se 2 (by rfl) ⟨791376, by rfl⟩ : syracuseStep 2110337 = 1582753) B1582753
theorem B2143127 : Blo 936583 2143127 := bstep (se 1 (by rfl) ⟨1607345, by rfl⟩ : syracuseStep 2143127 = 3214691) B3214691
theorem B1586135 : Blo 936583 1586135 := bstep (se 1 (by rfl) ⟨1189601, by rfl⟩ : syracuseStep 1586135 = 2379203) B2379203
theorem B1782785 : Blo 936583 1782785 := bstep (se 2 (by rfl) ⟨668544, by rfl⟩ : syracuseStep 1782785 = 1337089) B1337089
theorem B1586263 : Blo 936583 1586263 := bstep (se 1 (by rfl) ⟨1189697, by rfl⟩ : syracuseStep 1586263 = 2379395) B2379395
theorem B2110553 : Blo 936583 2110553 := bstep (se 2 (by rfl) ⟨791457, by rfl⟩ : syracuseStep 2110553 = 1582915) B1582915
theorem B2110643 : Blo 936583 2110643 := bstep (se 1 (by rfl) ⟨1582982, by rfl⟩ : syracuseStep 2110643 = 3165965) B3165965
theorem B2110679 : Blo 936583 2110679 := bstep (se 1 (by rfl) ⟨1583009, by rfl⟩ : syracuseStep 2110679 = 3166019) B3166019
theorem B2372915 : Blo 936583 2372915 := bstep (se 1 (by rfl) ⟨1779686, by rfl⟩ : syracuseStep 2372915 = 3559373) B3559373
theorem B1783127 : Blo 936583 1783127 := bstep (se 1 (by rfl) ⟨1337345, by rfl⟩ : syracuseStep 1783127 = 2674691) B2674691
theorem B4011353 : Blo 936583 4011353 := bstep (se 2 (by rfl) ⟨1504257, by rfl⟩ : syracuseStep 4011353 = 3008515) B3008515
theorem B2110859 : Blo 936583 2110859 := bstep (se 1 (by rfl) ⟨1583144, by rfl⟩ : syracuseStep 2110859 = 3166289) B3166289
theorem B4011437 : Blo 936583 4011437 := bstep (se 3 (by rfl) ⟨752144, by rfl⟩ : syracuseStep 4011437 = 1504289) B1504289
theorem B2110913 : Blo 936583 2110913 := bstep (se 2 (by rfl) ⟨791592, by rfl⟩ : syracuseStep 2110913 = 1583185) B1583185
theorem B2373209 : Blo 936583 2373209 := bstep (se 2 (by rfl) ⟨889953, by rfl⟩ : syracuseStep 2373209 = 1779907) B1779907
theorem B6010469 : Blo 936583 6010469 := bstep (se 4 (by rfl) ⟨563481, by rfl⟩ : syracuseStep 6010469 = 1126963) B1126963
theorem B8566373 : Blo 936583 8566373 := bstep (se 4 (by rfl) ⟨803097, by rfl⟩ : syracuseStep 8566373 = 1606195) B1606195
theorem B2111129 : Blo 936583 2111129 := bstep (se 2 (by rfl) ⟨791673, by rfl⟩ : syracuseStep 2111129 = 1583347) B1583347
theorem B1586891 : Blo 936583 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B2111219 : Blo 936583 2111219 := bstep (se 1 (by rfl) ⟨1583414, by rfl⟩ : syracuseStep 2111219 = 3166829) B3166829
theorem B2111255 : Blo 936583 2111255 := bstep (se 1 (by rfl) ⟨1583441, by rfl⟩ : syracuseStep 2111255 = 3166883) B3166883
theorem B1587019 : Blo 936583 1587019 := bstep (se 1 (by rfl) ⟨1190264, by rfl⟩ : syracuseStep 1587019 = 2380529) B2380529
theorem B5355395 : Blo 936583 5355395 := bstep (se 1 (by rfl) ⟨4016546, by rfl⟩ : syracuseStep 5355395 = 8033093) B8033093
theorem B3094451 : Blo 936583 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B2111435 : Blo 936583 2111435 := bstep (se 1 (by rfl) ⟨1583576, by rfl⟩ : syracuseStep 2111435 = 3167153) B3167153
theorem B1587161 : Blo 936583 1587161 := bstep (se 2 (by rfl) ⟨595185, by rfl⟩ : syracuseStep 1587161 = 1190371) B1190371
theorem B1783795 : Blo 936583 1783795 := bstep (se 1 (by rfl) ⟨1337846, by rfl⟩ : syracuseStep 1783795 = 2675693) B2675693
theorem B2111489 : Blo 936583 2111489 := bstep (se 2 (by rfl) ⟨791808, by rfl⟩ : syracuseStep 2111489 = 1583617) B1583617
theorem B2668619 : Blo 936583 2668619 := bstep (se 1 (by rfl) ⟨2001464, by rfl⟩ : syracuseStep 2668619 = 4002929) B4002929
theorem B6010955 : Blo 936583 6010955 := bstep (se 1 (by rfl) ⟨4508216, by rfl⟩ : syracuseStep 6010955 = 9016433) B9016433
theorem B32553035 : Blo 936583 32553035 := bstep (se 1 (by rfl) ⟨24414776, by rfl⟩ : syracuseStep 32553035 = 48829553) B48829553
theorem B2111705 : Blo 936583 2111705 := bstep (se 2 (by rfl) ⟨791889, by rfl⟩ : syracuseStep 2111705 = 1583779) B1583779
theorem B2144513 : Blo 936583 2144513 := bstep (se 2 (by rfl) ⟨804192, by rfl⟩ : syracuseStep 2144513 = 1608385) B1608385
theorem B4503853 : Blo 936583 4503853 := bstep (se 3 (by rfl) ⟨844472, by rfl⟩ : syracuseStep 4503853 = 1688945) B1688945
theorem B2111795 : Blo 936583 2111795 := bstep (se 1 (by rfl) ⟨1583846, by rfl⟩ : syracuseStep 2111795 = 3167693) B3167693
theorem B2111831 : Blo 936583 2111831 := bstep (se 1 (by rfl) ⟨1583873, by rfl⟩ : syracuseStep 2111831 = 3167747) B3167747
theorem B7616861 : Blo 936583 7616861 := bstep (se 3 (by rfl) ⟨1428161, by rfl⟩ : syracuseStep 7616861 = 2856323) B2856323
theorem B8010161 : Blo 936583 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B1784243 : Blo 936583 1784243 := bstep (se 1 (by rfl) ⟨1338182, by rfl⟩ : syracuseStep 1784243 = 2676365) B2676365
theorem B4504025 : Blo 936583 4504025 := bstep (se 2 (by rfl) ⟨1689009, by rfl⟩ : syracuseStep 4504025 = 3378019) B3378019
theorem B1784281 : Blo 936583 1784281 := bstep (se 2 (by rfl) ⟨669105, by rfl⟩ : syracuseStep 1784281 = 1338211) B1338211
theorem B2112011 : Blo 936583 2112011 := bstep (se 1 (by rfl) ⟨1584008, by rfl⟩ : syracuseStep 2112011 = 3168017) B3168017
theorem B2112065 : Blo 936583 2112065 := bstep (se 2 (by rfl) ⟨792024, by rfl⟩ : syracuseStep 2112065 = 1584049) B1584049
theorem B2112281 : Blo 936583 2112281 := bstep (se 2 (by rfl) ⟨792105, by rfl⟩ : syracuseStep 2112281 = 1584211) B1584211
theorem B2112371 : Blo 936583 2112371 := bstep (se 1 (by rfl) ⟨1584278, by rfl⟩ : syracuseStep 2112371 = 3168557) B3168557
theorem B3619729 : Blo 936583 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B2112407 : Blo 936583 2112407 := bstep (se 1 (by rfl) ⟨1584305, by rfl⟩ : syracuseStep 2112407 = 3168611) B3168611
theorem B1784729 : Blo 936583 1784729 := bstep (se 2 (by rfl) ⟨669273, by rfl⟩ : syracuseStep 1784729 = 1338547) B1338547
theorem B2112587 : Blo 936583 2112587 := bstep (se 1 (by rfl) ⟨1584440, by rfl⟩ : syracuseStep 2112587 = 3168881) B3168881
theorem B8010845 : Blo 936583 8010845 := bstep (se 3 (by rfl) ⟨1502033, by rfl⟩ : syracuseStep 8010845 = 3004067) B3004067
theorem B2112641 : Blo 936583 2112641 := bstep (se 2 (by rfl) ⟨792240, by rfl⟩ : syracuseStep 2112641 = 1584481) B1584481
theorem B5717143 : Blo 936583 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B3161267 : Blo 936583 3161267 := bstep (se 1 (by rfl) ⟨2370950, by rfl⟩ : syracuseStep 3161267 = 4741901) B4741901
theorem B2374859 : Blo 936583 2374859 := bstep (se 1 (by rfl) ⟨1781144, by rfl⟩ : syracuseStep 2374859 = 3562289) B3562289
theorem B2112857 : Blo 936583 2112857 := bstep (se 2 (by rfl) ⟨792321, by rfl⟩ : syracuseStep 2112857 = 1584643) B1584643
theorem B2669917 : Blo 936583 2669917 := bstep (se 3 (by rfl) ⟨500609, by rfl⟩ : syracuseStep 2669917 = 1001219) B1001219
theorem B2112947 : Blo 936583 2112947 := bstep (se 1 (by rfl) ⟨1584710, by rfl⟩ : syracuseStep 2112947 = 3169421) B3169421
theorem B3161537 : Blo 936583 3161537 := bstep (se 2 (by rfl) ⟨1185576, by rfl⟩ : syracuseStep 3161537 = 2371153) B2371153
theorem B2112983 : Blo 936583 2112983 := bstep (se 1 (by rfl) ⟨1584737, by rfl⟩ : syracuseStep 2112983 = 3169475) B3169475
theorem B2539073 : Blo 936583 2539073 := bstep (se 2 (by rfl) ⟨952152, by rfl⟩ : syracuseStep 2539073 = 1904305) B1904305
theorem B2440793 : Blo 936583 2440793 := bstep (se 2 (by rfl) ⟨915297, by rfl⟩ : syracuseStep 2440793 = 1830595) B1830595
theorem B1785473 : Blo 936583 1785473 := bstep (se 2 (by rfl) ⟨669552, by rfl⟩ : syracuseStep 1785473 = 1339105) B1339105
theorem B2113163 : Blo 936583 2113163 := bstep (se 1 (by rfl) ⟨1584872, by rfl⟩ : syracuseStep 2113163 = 3169745) B3169745
theorem B2670259 : Blo 936583 2670259 := bstep (se 1 (by rfl) ⟨2002694, by rfl⟩ : syracuseStep 2670259 = 4005389) B4005389
theorem B2113217 : Blo 936583 2113217 := bstep (se 2 (by rfl) ⟨792456, by rfl⟩ : syracuseStep 2113217 = 1584913) B1584913
theorem B1425163 : Blo 936583 1425163 := bstep (se 1 (by rfl) ⟨1068872, by rfl⟩ : syracuseStep 1425163 = 2137745) B2137745
theorem B6504343 : Blo 936583 6504343 := bstep (se 1 (by rfl) ⟨4878257, by rfl⟩ : syracuseStep 6504343 = 9756515) B9756515
theorem B2113433 : Blo 936583 2113433 := bstep (se 2 (by rfl) ⟨792537, by rfl⟩ : syracuseStep 2113433 = 1585075) B1585075
theorem B3162077 : Blo 936583 3162077 := bstep (se 3 (by rfl) ⟨592889, by rfl⟩ : syracuseStep 3162077 = 1185779) B1185779
theorem B2113523 : Blo 936583 2113523 := bstep (se 1 (by rfl) ⟨1585142, by rfl⟩ : syracuseStep 2113523 = 3170285) B3170285
theorem B2113559 : Blo 936583 2113559 := bstep (se 1 (by rfl) ⟨1585169, by rfl⟩ : syracuseStep 2113559 = 3170339) B3170339
theorem B2375831 : Blo 936583 2375831 := bstep (se 1 (by rfl) ⟨1781873, by rfl⟩ : syracuseStep 2375831 = 3563747) B3563747
theorem B2113739 : Blo 936583 2113739 := bstep (se 1 (by rfl) ⟨1585304, by rfl⟩ : syracuseStep 2113739 = 3170609) B3170609
theorem B2113793 : Blo 936583 2113793 := bstep (se 2 (by rfl) ⟨792672, by rfl⟩ : syracuseStep 2113793 = 1585345) B1585345
theorem B2114009 : Blo 936583 2114009 := bstep (se 2 (by rfl) ⟨792753, by rfl⟩ : syracuseStep 2114009 = 1585507) B1585507
theorem B1688087 : Blo 936583 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B2114099 : Blo 936583 2114099 := bstep (se 1 (by rfl) ⟨1585574, by rfl⟩ : syracuseStep 2114099 = 3171149) B3171149
theorem B2114135 : Blo 936583 2114135 := bstep (se 1 (by rfl) ⟨1585601, by rfl⟩ : syracuseStep 2114135 = 3171203) B3171203
theorem B2671193 : Blo 936583 2671193 := bstep (se 2 (by rfl) ⟨1001697, by rfl⟩ : syracuseStep 2671193 = 2003395) B2003395
theorem B4014785 : Blo 936583 4014785 := bstep (se 2 (by rfl) ⟨1505544, by rfl⟩ : syracuseStep 4014785 = 3011089) B3011089
theorem B2114315 : Blo 936583 2114315 := bstep (se 1 (by rfl) ⟨1585736, by rfl⟩ : syracuseStep 2114315 = 3171473) B3171473
theorem B2376499 : Blo 936583 2376499 := bstep (se 1 (by rfl) ⟨1782374, by rfl⟩ : syracuseStep 2376499 = 3564749) B3564749
theorem B2114369 : Blo 936583 2114369 := bstep (se 2 (by rfl) ⟨792888, by rfl⟩ : syracuseStep 2114369 = 1585777) B1585777
theorem B2376641 : Blo 936583 2376641 := bstep (se 2 (by rfl) ⟨891240, by rfl⟩ : syracuseStep 2376641 = 1782481) B1782481
theorem B1000459 : Blo 936583 1000459 := bstep (se 1 (by rfl) ⟨750344, by rfl⟩ : syracuseStep 1000459 = 1500689) B1500689
theorem B2114585 : Blo 936583 2114585 := bstep (se 2 (by rfl) ⟨792969, by rfl⟩ : syracuseStep 2114585 = 1585939) B1585939
theorem B3163211 : Blo 936583 3163211 := bstep (se 1 (by rfl) ⟨2372408, by rfl⟩ : syracuseStep 3163211 = 4744817) B4744817
theorem B2114675 : Blo 936583 2114675 := bstep (se 1 (by rfl) ⟨1586006, by rfl⟩ : syracuseStep 2114675 = 3172013) B3172013
theorem B2114711 : Blo 936583 2114711 := bstep (se 1 (by rfl) ⟨1586033, by rfl⟩ : syracuseStep 2114711 = 3172067) B3172067
theorem B1688779 : Blo 936583 1688779 := bstep (se 1 (by rfl) ⟨1266584, by rfl⟩ : syracuseStep 1688779 = 2533169) B2533169
theorem B5063897 : Blo 936583 5063897 := bstep (se 2 (by rfl) ⟨1898961, by rfl⟩ : syracuseStep 5063897 = 3797923) B3797923
theorem B21677357 : Blo 936583 21677357 := bstep (se 3 (by rfl) ⟨4064504, by rfl⟩ : syracuseStep 21677357 = 8129009) B8129009
theorem B2114891 : Blo 936583 2114891 := bstep (se 1 (by rfl) ⟨1586168, by rfl⟩ : syracuseStep 2114891 = 3172337) B3172337
theorem B3163481 : Blo 936583 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B4015453 : Blo 936583 4015453 := bstep (se 3 (by rfl) ⟨752897, by rfl⟩ : syracuseStep 4015453 = 1505795) B1505795
theorem B2114945 : Blo 936583 2114945 := bstep (se 2 (by rfl) ⟨793104, by rfl⟩ : syracuseStep 2114945 = 1586209) B1586209
theorem B5064067 : Blo 936583 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B6014387 : Blo 936583 6014387 := bstep (se 1 (by rfl) ⟨4510790, by rfl⟩ : syracuseStep 6014387 = 9021581) B9021581
theorem B1689025 : Blo 936583 1689025 := bstep (se 2 (by rfl) ⟨633384, by rfl⟩ : syracuseStep 1689025 = 1266769) B1266769
theorem B2115161 : Blo 936583 2115161 := bstep (se 2 (by rfl) ⟨793185, by rfl⟩ : syracuseStep 2115161 = 1586371) B1586371
theorem B8570461 : Blo 936583 8570461 := bstep (se 3 (by rfl) ⟨1606961, by rfl⟩ : syracuseStep 8570461 = 3213923) B3213923
theorem B2115251 : Blo 936583 2115251 := bstep (se 1 (by rfl) ⟨1586438, by rfl⟩ : syracuseStep 2115251 = 3172877) B3172877
theorem B2541235 : Blo 936583 2541235 := bstep (se 1 (by rfl) ⟨1905926, by rfl⟩ : syracuseStep 2541235 = 3811853) B3811853
theorem B2115287 : Blo 936583 2115287 := bstep (se 1 (by rfl) ⟨1586465, by rfl⟩ : syracuseStep 2115287 = 3172931) B3172931
theorem B1689355 : Blo 936583 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B2115467 : Blo 936583 2115467 := bstep (se 1 (by rfl) ⟨1586600, by rfl⟩ : syracuseStep 2115467 = 3173201) B3173201
theorem B4016051 : Blo 936583 4016051 := bstep (se 1 (by rfl) ⟨3012038, by rfl⟩ : syracuseStep 4016051 = 6024077) B6024077
theorem B2115521 : Blo 936583 2115521 := bstep (se 2 (by rfl) ⟨793320, by rfl⟩ : syracuseStep 2115521 = 1586641) B1586641
theorem B2672605 : Blo 936583 2672605 := bstep (se 3 (by rfl) ⟨501113, by rfl⟩ : syracuseStep 2672605 = 1002227) B1002227
theorem B3164183 : Blo 936583 3164183 := bstep (se 1 (by rfl) ⟨2373137, by rfl⟩ : syracuseStep 3164183 = 4746275) B4746275
theorem B7129133 : Blo 936583 7129133 := bstep (se 3 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 7129133 = 2673425) B2673425
theorem B2115737 : Blo 936583 2115737 := bstep (se 2 (by rfl) ⟨793401, by rfl⟩ : syracuseStep 2115737 = 1586803) B1586803
theorem B2377907 : Blo 936583 2377907 := bstep (se 1 (by rfl) ⟨1783430, by rfl⟩ : syracuseStep 2377907 = 3566861) B3566861
theorem B2672833 : Blo 936583 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B2115827 : Blo 936583 2115827 := bstep (se 1 (by rfl) ⟨1586870, by rfl⟩ : syracuseStep 2115827 = 3173741) B3173741
theorem B2115863 : Blo 936583 2115863 := bstep (se 1 (by rfl) ⟨1586897, by rfl⟩ : syracuseStep 2115863 = 3173795) B3173795
theorem B2116043 : Blo 936583 2116043 := bstep (se 1 (by rfl) ⟨1587032, by rfl⟩ : syracuseStep 2116043 = 3174065) B3174065
theorem B2116097 : Blo 936583 2116097 := bstep (se 2 (by rfl) ⟨793536, by rfl⟩ : syracuseStep 2116097 = 1587073) B1587073
theorem B2673175 : Blo 936583 2673175 := bstep (se 1 (by rfl) ⟨2004881, by rfl⟩ : syracuseStep 2673175 = 4009763) B4009763
theorem B3164723 : Blo 936583 3164723 := bstep (se 1 (by rfl) ⟨2373542, by rfl⟩ : syracuseStep 3164723 = 4747085) B4747085
theorem B1690163 : Blo 936583 1690163 := bstep (se 1 (by rfl) ⟨1267622, by rfl⟩ : syracuseStep 1690163 = 2535245) B2535245
theorem B936587 : Blo 936583 936587 := bstep (se 1 (by rfl) ⟨702440, by rfl⟩ : syracuseStep 936587 = 1404881) B1404881
theorem B936599 : Blo 936583 936599 := bstep (se 1 (by rfl) ⟨702449, by rfl⟩ : syracuseStep 936599 = 1404899) B1404899
theorem B1428119 : Blo 936583 1428119 := bstep (se 1 (by rfl) ⟨1071089, by rfl⟩ : syracuseStep 1428119 = 2142179) B2142179
theorem B936619 : Blo 936583 936619 := bstep (se 1 (by rfl) ⟨702464, by rfl⟩ : syracuseStep 936619 = 1404929) B1404929
theorem B936631 : Blo 936583 936631 := bstep (se 1 (by rfl) ⟨702473, by rfl⟩ : syracuseStep 936631 = 1404947) B1404947
theorem B936651 : Blo 936583 936651 := bstep (se 1 (by rfl) ⟨702488, by rfl⟩ : syracuseStep 936651 = 1404977) B1404977
theorem B2378443 : Blo 936583 2378443 := bstep (se 1 (by rfl) ⟨1783832, by rfl⟩ : syracuseStep 2378443 = 3567665) B3567665
theorem B936663 : Blo 936583 936663 := bstep (se 1 (by rfl) ⟨702497, by rfl⟩ : syracuseStep 936663 = 1404995) B1404995
theorem B2116313 : Blo 936583 2116313 := bstep (se 2 (by rfl) ⟨793617, by rfl⟩ : syracuseStep 2116313 = 1587235) B1587235
theorem B936683 : Blo 936583 936683 := bstep (se 1 (by rfl) ⟨702512, by rfl⟩ : syracuseStep 936683 = 1405025) B1405025
theorem B936695 : Blo 936583 936695 := bstep (se 1 (by rfl) ⟨702521, by rfl⟩ : syracuseStep 936695 = 1405043) B1405043
theorem B936715 : Blo 936583 936715 := bstep (se 1 (by rfl) ⟨702536, by rfl⟩ : syracuseStep 936715 = 1405073) B1405073
theorem B936727 : Blo 936583 936727 := bstep (se 1 (by rfl) ⟨702545, by rfl⟩ : syracuseStep 936727 = 1405091) B1405091
theorem B936747 : Blo 936583 936747 := bstep (se 1 (by rfl) ⟨702560, by rfl⟩ : syracuseStep 936747 = 1405121) B1405121
theorem B936759 : Blo 936583 936759 := bstep (se 1 (by rfl) ⟨702569, by rfl⟩ : syracuseStep 936759 = 1405139) B1405139
theorem B3164993 : Blo 936583 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B936779 : Blo 936583 936779 := bstep (se 1 (by rfl) ⟨702584, by rfl⟩ : syracuseStep 936779 = 1405169) B1405169
theorem B936791 : Blo 936583 936791 := bstep (se 1 (by rfl) ⟨702593, by rfl⟩ : syracuseStep 936791 = 1405187) B1405187
theorem B2378585 : Blo 936583 2378585 := bstep (se 2 (by rfl) ⟨891969, by rfl⟩ : syracuseStep 2378585 = 1783939) B1783939
theorem B936811 : Blo 936583 936811 := bstep (se 1 (by rfl) ⟨702608, by rfl⟩ : syracuseStep 936811 = 1405217) B1405217
theorem B936823 : Blo 936583 936823 := bstep (se 1 (by rfl) ⟨702617, by rfl⟩ : syracuseStep 936823 = 1405235) B1405235
theorem B936843 : Blo 936583 936843 := bstep (se 1 (by rfl) ⟨702632, by rfl⟩ : syracuseStep 936843 = 1405265) B1405265
theorem B936855 : Blo 936583 936855 := bstep (se 1 (by rfl) ⟨702641, by rfl⟩ : syracuseStep 936855 = 1405283) B1405283
theorem B936875 : Blo 936583 936875 := bstep (se 1 (by rfl) ⟨702656, by rfl⟩ : syracuseStep 936875 = 1405313) B1405313
theorem B936887 : Blo 936583 936887 := bstep (se 1 (by rfl) ⟨702665, by rfl⟩ : syracuseStep 936887 = 1405331) B1405331
theorem B3427265 : Blo 936583 3427265 := bstep (se 2 (by rfl) ⟨1285224, by rfl⟩ : syracuseStep 3427265 = 2570449) B2570449
theorem B936907 : Blo 936583 936907 := bstep (se 1 (by rfl) ⟨702680, by rfl⟩ : syracuseStep 936907 = 1405361) B1405361
theorem B936919 : Blo 936583 936919 := bstep (se 1 (by rfl) ⟨702689, by rfl⟩ : syracuseStep 936919 = 1405379) B1405379
theorem B936939 : Blo 936583 936939 := bstep (se 1 (by rfl) ⟨702704, by rfl⟩ : syracuseStep 936939 = 1405409) B1405409
theorem B936951 : Blo 936583 936951 := bstep (se 1 (by rfl) ⟨702713, by rfl⟩ : syracuseStep 936951 = 1405427) B1405427
theorem B1690625 : Blo 936583 1690625 := bstep (se 2 (by rfl) ⟨633984, by rfl⟩ : syracuseStep 1690625 = 1267969) B1267969
theorem B936971 : Blo 936583 936971 := bstep (se 1 (by rfl) ⟨702728, by rfl⟩ : syracuseStep 936971 = 1405457) B1405457
theorem B936983 : Blo 936583 936983 := bstep (se 1 (by rfl) ⟨702737, by rfl⟩ : syracuseStep 936983 = 1405475) B1405475
theorem B937003 : Blo 936583 937003 := bstep (se 1 (by rfl) ⟨702752, by rfl⟩ : syracuseStep 937003 = 1405505) B1405505
theorem B937015 : Blo 936583 937015 := bstep (se 1 (by rfl) ⟨702761, by rfl⟩ : syracuseStep 937015 = 1405523) B1405523
theorem B937035 : Blo 936583 937035 := bstep (se 1 (by rfl) ⟨702776, by rfl⟩ : syracuseStep 937035 = 1405553) B1405553
theorem B937047 : Blo 936583 937047 := bstep (se 1 (by rfl) ⟨702785, by rfl⟩ : syracuseStep 937047 = 1405571) B1405571
theorem B937067 : Blo 936583 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B937079 : Blo 936583 937079 := bstep (se 1 (by rfl) ⟨702809, by rfl⟩ : syracuseStep 937079 = 1405619) B1405619
theorem B937099 : Blo 936583 937099 := bstep (se 1 (by rfl) ⟨702824, by rfl⟩ : syracuseStep 937099 = 1405649) B1405649
theorem B937111 : Blo 936583 937111 := bstep (se 1 (by rfl) ⟨702833, by rfl⟩ : syracuseStep 937111 = 1405667) B1405667
theorem B937131 : Blo 936583 937131 := bstep (se 1 (by rfl) ⟨702848, by rfl⟩ : syracuseStep 937131 = 1405697) B1405697
theorem B937143 : Blo 936583 937143 := bstep (se 1 (by rfl) ⟨702857, by rfl⟩ : syracuseStep 937143 = 1405715) B1405715
theorem B937163 : Blo 936583 937163 := bstep (se 1 (by rfl) ⟨702872, by rfl⟩ : syracuseStep 937163 = 1405745) B1405745
theorem B937175 : Blo 936583 937175 := bstep (se 1 (by rfl) ⟨702881, by rfl⟩ : syracuseStep 937175 = 1405763) B1405763
theorem B2673881 : Blo 936583 2673881 := bstep (se 2 (by rfl) ⟨1002705, by rfl⟩ : syracuseStep 2673881 = 2005411) B2005411
theorem B937195 : Blo 936583 937195 := bstep (se 1 (by rfl) ⟨702896, by rfl⟩ : syracuseStep 937195 = 1405793) B1405793
theorem B937207 : Blo 936583 937207 := bstep (se 1 (by rfl) ⟨702905, by rfl⟩ : syracuseStep 937207 = 1405811) B1405811
theorem B937227 : Blo 936583 937227 := bstep (se 1 (by rfl) ⟨702920, by rfl⟩ : syracuseStep 937227 = 1405841) B1405841
theorem B937239 : Blo 936583 937239 := bstep (se 1 (by rfl) ⟨702929, by rfl⟩ : syracuseStep 937239 = 1405859) B1405859
theorem B937259 : Blo 936583 937259 := bstep (se 1 (by rfl) ⟨702944, by rfl⟩ : syracuseStep 937259 = 1405889) B1405889
theorem B937271 : Blo 936583 937271 := bstep (se 1 (by rfl) ⟨702953, by rfl⟩ : syracuseStep 937271 = 1405907) B1405907
theorem B937291 : Blo 936583 937291 := bstep (se 1 (by rfl) ⟨702968, by rfl⟩ : syracuseStep 937291 = 1405937) B1405937
theorem B937303 : Blo 936583 937303 := bstep (se 1 (by rfl) ⟨702977, by rfl⟩ : syracuseStep 937303 = 1405955) B1405955
theorem B3165533 : Blo 936583 3165533 := bstep (se 3 (by rfl) ⟨593537, by rfl⟩ : syracuseStep 3165533 = 1187075) B1187075
theorem B937323 : Blo 936583 937323 := bstep (se 1 (by rfl) ⟨702992, by rfl⟩ : syracuseStep 937323 = 1405985) B1405985
theorem B937335 : Blo 936583 937335 := bstep (se 1 (by rfl) ⟨703001, by rfl⟩ : syracuseStep 937335 = 1406003) B1406003
theorem B937355 : Blo 936583 937355 := bstep (se 1 (by rfl) ⟨703016, by rfl⟩ : syracuseStep 937355 = 1406033) B1406033
theorem B937367 : Blo 936583 937367 := bstep (se 1 (by rfl) ⟨703025, by rfl⟩ : syracuseStep 937367 = 1406051) B1406051
theorem B937387 : Blo 936583 937387 := bstep (se 1 (by rfl) ⟨703040, by rfl⟩ : syracuseStep 937387 = 1406081) B1406081
theorem B937399 : Blo 936583 937399 := bstep (se 1 (by rfl) ⟨703049, by rfl⟩ : syracuseStep 937399 = 1406099) B1406099
theorem B937419 : Blo 936583 937419 := bstep (se 1 (by rfl) ⟨703064, by rfl⟩ : syracuseStep 937419 = 1406129) B1406129
theorem B937431 : Blo 936583 937431 := bstep (se 1 (by rfl) ⟨703073, by rfl⟩ : syracuseStep 937431 = 1406147) B1406147
theorem B937451 : Blo 936583 937451 := bstep (se 1 (by rfl) ⟨703088, by rfl⟩ : syracuseStep 937451 = 1406177) B1406177
theorem B937463 : Blo 936583 937463 := bstep (se 1 (by rfl) ⟨703097, by rfl⟩ : syracuseStep 937463 = 1406195) B1406195
theorem B937483 : Blo 936583 937483 := bstep (se 1 (by rfl) ⟨703112, by rfl⟩ : syracuseStep 937483 = 1406225) B1406225
theorem B937495 : Blo 936583 937495 := bstep (se 1 (by rfl) ⟨703121, by rfl⟩ : syracuseStep 937495 = 1406243) B1406243
theorem B937515 : Blo 936583 937515 := bstep (se 1 (by rfl) ⟨703136, by rfl⟩ : syracuseStep 937515 = 1406273) B1406273
theorem B937527 : Blo 936583 937527 := bstep (se 1 (by rfl) ⟨703145, by rfl⟩ : syracuseStep 937527 = 1406291) B1406291
theorem B10669643 : Blo 936583 10669643 := bstep (se 1 (by rfl) ⟨8002232, by rfl⟩ : syracuseStep 10669643 = 16004465) B16004465
theorem B937547 : Blo 936583 937547 := bstep (se 1 (by rfl) ⟨703160, by rfl⟩ : syracuseStep 937547 = 1406321) B1406321
theorem B937559 : Blo 936583 937559 := bstep (se 1 (by rfl) ⟨703169, by rfl⟩ : syracuseStep 937559 = 1406339) B1406339
theorem B937579 : Blo 936583 937579 := bstep (se 1 (by rfl) ⟨703184, by rfl⟩ : syracuseStep 937579 = 1406369) B1406369
theorem B937591 : Blo 936583 937591 := bstep (se 1 (by rfl) ⟨703193, by rfl⟩ : syracuseStep 937591 = 1406387) B1406387
theorem B6016643 : Blo 936583 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B937611 : Blo 936583 937611 := bstep (se 1 (by rfl) ⟨703208, by rfl⟩ : syracuseStep 937611 = 1406417) B1406417
theorem B937623 : Blo 936583 937623 := bstep (se 1 (by rfl) ⟨703217, by rfl⟩ : syracuseStep 937623 = 1406435) B1406435
theorem B2379415 : Blo 936583 2379415 := bstep (se 1 (by rfl) ⟨1784561, by rfl⟩ : syracuseStep 2379415 = 3569123) B3569123
theorem B937643 : Blo 936583 937643 := bstep (se 1 (by rfl) ⟨703232, by rfl⟩ : syracuseStep 937643 = 1406465) B1406465
theorem B3559085 : Blo 936583 3559085 := bstep (se 3 (by rfl) ⟨667328, by rfl⟩ : syracuseStep 3559085 = 1334657) B1334657
theorem B937655 : Blo 936583 937655 := bstep (se 1 (by rfl) ⟨703241, by rfl⟩ : syracuseStep 937655 = 1406483) B1406483
theorem B937675 : Blo 936583 937675 := bstep (se 1 (by rfl) ⟨703256, by rfl⟩ : syracuseStep 937675 = 1406513) B1406513
theorem B937687 : Blo 936583 937687 := bstep (se 1 (by rfl) ⟨703265, by rfl⟩ : syracuseStep 937687 = 1406531) B1406531
theorem B937707 : Blo 936583 937707 := bstep (se 1 (by rfl) ⟨703280, by rfl⟩ : syracuseStep 937707 = 1406561) B1406561
theorem B937719 : Blo 936583 937719 := bstep (se 1 (by rfl) ⟨703289, by rfl⟩ : syracuseStep 937719 = 1406579) B1406579
theorem B937739 : Blo 936583 937739 := bstep (se 1 (by rfl) ⟨703304, by rfl⟩ : syracuseStep 937739 = 1406609) B1406609
theorem B937751 : Blo 936583 937751 := bstep (se 1 (by rfl) ⟨703313, by rfl⟩ : syracuseStep 937751 = 1406627) B1406627
theorem B937771 : Blo 936583 937771 := bstep (se 1 (by rfl) ⟨703328, by rfl⟩ : syracuseStep 937771 = 1406657) B1406657
theorem B937783 : Blo 936583 937783 := bstep (se 1 (by rfl) ⟨703337, by rfl⟩ : syracuseStep 937783 = 1406675) B1406675
theorem B937803 : Blo 936583 937803 := bstep (se 1 (by rfl) ⟨703352, by rfl⟩ : syracuseStep 937803 = 1406705) B1406705
theorem B937815 : Blo 936583 937815 := bstep (se 1 (by rfl) ⟨703361, by rfl⟩ : syracuseStep 937815 = 1406723) B1406723
theorem B937835 : Blo 936583 937835 := bstep (se 1 (by rfl) ⟨703376, by rfl⟩ : syracuseStep 937835 = 1406753) B1406753
theorem B937847 : Blo 936583 937847 := bstep (se 1 (by rfl) ⟨703385, by rfl⟩ : syracuseStep 937847 = 1406771) B1406771
theorem B937867 : Blo 936583 937867 := bstep (se 1 (by rfl) ⟨703400, by rfl⟩ : syracuseStep 937867 = 1406801) B1406801
theorem B937879 : Blo 936583 937879 := bstep (se 1 (by rfl) ⟨703409, by rfl⟩ : syracuseStep 937879 = 1406819) B1406819
theorem B937899 : Blo 936583 937899 := bstep (se 1 (by rfl) ⟨703424, by rfl⟩ : syracuseStep 937899 = 1406849) B1406849
theorem B937911 : Blo 936583 937911 := bstep (se 1 (by rfl) ⟨703433, by rfl⟩ : syracuseStep 937911 = 1406867) B1406867
theorem B937931 : Blo 936583 937931 := bstep (se 1 (by rfl) ⟨703448, by rfl⟩ : syracuseStep 937931 = 1406897) B1406897
theorem B937943 : Blo 936583 937943 := bstep (se 1 (by rfl) ⟨703457, by rfl⟩ : syracuseStep 937943 = 1406915) B1406915
theorem B937963 : Blo 936583 937963 := bstep (se 1 (by rfl) ⟨703472, by rfl⟩ : syracuseStep 937963 = 1406945) B1406945
theorem B937975 : Blo 936583 937975 := bstep (se 1 (by rfl) ⟨703481, by rfl⟩ : syracuseStep 937975 = 1406963) B1406963
theorem B937995 : Blo 936583 937995 := bstep (se 1 (by rfl) ⟨703496, by rfl⟩ : syracuseStep 937995 = 1406993) B1406993
theorem B938007 : Blo 936583 938007 := bstep (se 1 (by rfl) ⟨703505, by rfl⟩ : syracuseStep 938007 = 1407011) B1407011
theorem B938027 : Blo 936583 938027 := bstep (se 1 (by rfl) ⟨703520, by rfl⟩ : syracuseStep 938027 = 1407041) B1407041
theorem B938039 : Blo 936583 938039 := bstep (se 1 (by rfl) ⟨703529, by rfl⟩ : syracuseStep 938039 = 1407059) B1407059
theorem B1691713 : Blo 936583 1691713 := bstep (se 2 (by rfl) ⟨634392, by rfl⟩ : syracuseStep 1691713 = 1268785) B1268785
theorem B938059 : Blo 936583 938059 := bstep (se 1 (by rfl) ⟨703544, by rfl⟩ : syracuseStep 938059 = 1407089) B1407089
theorem B2379851 : Blo 936583 2379851 := bstep (se 1 (by rfl) ⟨1784888, by rfl⟩ : syracuseStep 2379851 = 3569777) B3569777
theorem B938071 : Blo 936583 938071 := bstep (se 1 (by rfl) ⟨703553, by rfl⟩ : syracuseStep 938071 = 1407107) B1407107
theorem B938091 : Blo 936583 938091 := bstep (se 1 (by rfl) ⟨703568, by rfl⟩ : syracuseStep 938091 = 1407137) B1407137
theorem B938103 : Blo 936583 938103 := bstep (se 1 (by rfl) ⟨703577, by rfl⟩ : syracuseStep 938103 = 1407155) B1407155
theorem B938123 : Blo 936583 938123 := bstep (se 1 (by rfl) ⟨703592, by rfl⟩ : syracuseStep 938123 = 1407185) B1407185
theorem B938135 : Blo 936583 938135 := bstep (se 1 (by rfl) ⟨703601, by rfl⟩ : syracuseStep 938135 = 1407203) B1407203
theorem B938155 : Blo 936583 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B938167 : Blo 936583 938167 := bstep (se 1 (by rfl) ⟨703625, by rfl⟩ : syracuseStep 938167 = 1407251) B1407251
theorem B938187 : Blo 936583 938187 := bstep (se 1 (by rfl) ⟨703640, by rfl⟩ : syracuseStep 938187 = 1407281) B1407281
theorem B938199 : Blo 936583 938199 := bstep (se 1 (by rfl) ⟨703649, by rfl⟩ : syracuseStep 938199 = 1407299) B1407299
theorem B938219 : Blo 936583 938219 := bstep (se 1 (by rfl) ⟨703664, by rfl⟩ : syracuseStep 938219 = 1407329) B1407329
theorem B938231 : Blo 936583 938231 := bstep (se 1 (by rfl) ⟨703673, by rfl⟩ : syracuseStep 938231 = 1407347) B1407347
theorem B938251 : Blo 936583 938251 := bstep (se 1 (by rfl) ⟨703688, by rfl⟩ : syracuseStep 938251 = 1407377) B1407377
theorem B938263 : Blo 936583 938263 := bstep (se 1 (by rfl) ⟨703697, by rfl⟩ : syracuseStep 938263 = 1407395) B1407395
theorem B1003799 : Blo 936583 1003799 := bstep (se 1 (by rfl) ⟨752849, by rfl⟩ : syracuseStep 1003799 = 1505699) B1505699
theorem B938283 : Blo 936583 938283 := bstep (se 1 (by rfl) ⟨703712, by rfl⟩ : syracuseStep 938283 = 1407425) B1407425
theorem B938295 : Blo 936583 938295 := bstep (se 1 (by rfl) ⟨703721, by rfl⟩ : syracuseStep 938295 = 1407443) B1407443
theorem B938315 : Blo 936583 938315 := bstep (se 1 (by rfl) ⟨703736, by rfl⟩ : syracuseStep 938315 = 1407473) B1407473
theorem B938327 : Blo 936583 938327 := bstep (se 1 (by rfl) ⟨703745, by rfl⟩ : syracuseStep 938327 = 1407491) B1407491
theorem B938347 : Blo 936583 938347 := bstep (se 1 (by rfl) ⟨703760, by rfl⟩ : syracuseStep 938347 = 1407521) B1407521
theorem B938359 : Blo 936583 938359 := bstep (se 1 (by rfl) ⟨703769, by rfl⟩ : syracuseStep 938359 = 1407539) B1407539
theorem B938379 : Blo 936583 938379 := bstep (se 1 (by rfl) ⟨703784, by rfl⟩ : syracuseStep 938379 = 1407569) B1407569
theorem B938391 : Blo 936583 938391 := bstep (se 1 (by rfl) ⟨703793, by rfl⟩ : syracuseStep 938391 = 1407587) B1407587
theorem B938411 : Blo 936583 938411 := bstep (se 1 (by rfl) ⟨703808, by rfl⟩ : syracuseStep 938411 = 1407617) B1407617
theorem B13717937 : Blo 936583 13717937 := bstep (se 2 (by rfl) ⟨5144226, by rfl⟩ : syracuseStep 13717937 = 10288453) B10288453
theorem B3559859 : Blo 936583 3559859 := bstep (se 1 (by rfl) ⟨2669894, by rfl⟩ : syracuseStep 3559859 = 5339789) B5339789
theorem B938423 : Blo 936583 938423 := bstep (se 1 (by rfl) ⟨703817, by rfl⟩ : syracuseStep 938423 = 1407635) B1407635
theorem B2281921 : Blo 936583 2281921 := bstep (se 2 (by rfl) ⟨855720, by rfl⟩ : syracuseStep 2281921 = 1711441) B1711441
theorem B2380225 : Blo 936583 2380225 := bstep (se 2 (by rfl) ⟨892584, by rfl⟩ : syracuseStep 2380225 = 1785169) B1785169
theorem B3166667 : Blo 936583 3166667 := bstep (se 1 (by rfl) ⟨2375000, by rfl⟩ : syracuseStep 3166667 = 4750001) B4750001
theorem B938443 : Blo 936583 938443 := bstep (se 1 (by rfl) ⟨703832, by rfl⟩ : syracuseStep 938443 = 1407665) B1407665
theorem B938455 : Blo 936583 938455 := bstep (se 1 (by rfl) ⟨703841, by rfl⟩ : syracuseStep 938455 = 1407683) B1407683
theorem B938475 : Blo 936583 938475 := bstep (se 1 (by rfl) ⟨703856, by rfl⟩ : syracuseStep 938475 = 1407713) B1407713
theorem B938487 : Blo 936583 938487 := bstep (se 1 (by rfl) ⟨703865, by rfl⟩ : syracuseStep 938487 = 1407731) B1407731
theorem B938507 : Blo 936583 938507 := bstep (se 1 (by rfl) ⟨703880, by rfl⟩ : syracuseStep 938507 = 1407761) B1407761
theorem B938519 : Blo 936583 938519 := bstep (se 1 (by rfl) ⟨703889, by rfl⟩ : syracuseStep 938519 = 1407779) B1407779
theorem B1430041 : Blo 936583 1430041 := bstep (se 2 (by rfl) ⟨536265, by rfl⟩ : syracuseStep 1430041 = 1072531) B1072531
theorem B938539 : Blo 936583 938539 := bstep (se 1 (by rfl) ⟨703904, by rfl⟩ : syracuseStep 938539 = 1407809) B1407809
theorem B1692211 : Blo 936583 1692211 := bstep (se 1 (by rfl) ⟨1269158, by rfl⟩ : syracuseStep 1692211 = 2538317) B2538317
theorem B938551 : Blo 936583 938551 := bstep (se 1 (by rfl) ⟨703913, by rfl⟩ : syracuseStep 938551 = 1407827) B1407827
theorem B938571 : Blo 936583 938571 := bstep (se 1 (by rfl) ⟨703928, by rfl⟩ : syracuseStep 938571 = 1407857) B1407857
theorem B938583 : Blo 936583 938583 := bstep (se 1 (by rfl) ⟨703937, by rfl⟩ : syracuseStep 938583 = 1407875) B1407875
theorem B938603 : Blo 936583 938603 := bstep (se 1 (by rfl) ⟨703952, by rfl⟩ : syracuseStep 938603 = 1407905) B1407905
theorem B938615 : Blo 936583 938615 := bstep (se 1 (by rfl) ⟨703961, by rfl⟩ : syracuseStep 938615 = 1407923) B1407923
theorem B938635 : Blo 936583 938635 := bstep (se 1 (by rfl) ⟨703976, by rfl⟩ : syracuseStep 938635 = 1407953) B1407953
theorem B938647 : Blo 936583 938647 := bstep (se 1 (by rfl) ⟨703985, by rfl⟩ : syracuseStep 938647 = 1407971) B1407971
theorem B1692311 : Blo 936583 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B938667 : Blo 936583 938667 := bstep (se 1 (by rfl) ⟨704000, by rfl⟩ : syracuseStep 938667 = 1408001) B1408001
theorem B938679 : Blo 936583 938679 := bstep (se 1 (by rfl) ⟨704009, by rfl⟩ : syracuseStep 938679 = 1408019) B1408019
theorem B938699 : Blo 936583 938699 := bstep (se 1 (by rfl) ⟨704024, by rfl⟩ : syracuseStep 938699 = 1408049) B1408049
theorem B938711 : Blo 936583 938711 := bstep (se 1 (by rfl) ⟨704033, by rfl⟩ : syracuseStep 938711 = 1408067) B1408067
theorem B3166937 : Blo 936583 3166937 := bstep (se 2 (by rfl) ⟨1187601, by rfl⟩ : syracuseStep 3166937 = 2375203) B2375203
theorem B938731 : Blo 936583 938731 := bstep (se 1 (by rfl) ⟨704048, by rfl⟩ : syracuseStep 938731 = 1408097) B1408097
theorem B938743 : Blo 936583 938743 := bstep (se 1 (by rfl) ⟨704057, by rfl⟩ : syracuseStep 938743 = 1408115) B1408115
theorem B938763 : Blo 936583 938763 := bstep (se 1 (by rfl) ⟨704072, by rfl⟩ : syracuseStep 938763 = 1408145) B1408145
theorem B1692427 : Blo 936583 1692427 := bstep (se 1 (by rfl) ⟨1269320, by rfl⟩ : syracuseStep 1692427 = 2538641) B2538641
theorem B938775 : Blo 936583 938775 := bstep (se 1 (by rfl) ⟨704081, by rfl⟩ : syracuseStep 938775 = 1408163) B1408163
theorem B938795 : Blo 936583 938795 := bstep (se 1 (by rfl) ⟨704096, by rfl⟩ : syracuseStep 938795 = 1408193) B1408193
theorem B938807 : Blo 936583 938807 := bstep (se 1 (by rfl) ⟨704105, by rfl⟩ : syracuseStep 938807 = 1408211) B1408211
theorem B2675521 : Blo 936583 2675521 := bstep (se 2 (by rfl) ⟨1003320, by rfl⟩ : syracuseStep 2675521 = 2006641) B2006641
theorem B938827 : Blo 936583 938827 := bstep (se 1 (by rfl) ⟨704120, by rfl⟩ : syracuseStep 938827 = 1408241) B1408241
theorem B938839 : Blo 936583 938839 := bstep (se 1 (by rfl) ⟨704129, by rfl⟩ : syracuseStep 938839 = 1408259) B1408259
theorem B938859 : Blo 936583 938859 := bstep (se 1 (by rfl) ⟨704144, by rfl⟩ : syracuseStep 938859 = 1408289) B1408289
theorem B17126261 : Blo 936583 17126261 := bstep (se 5 (by rfl) ⟨802793, by rfl⟩ : syracuseStep 17126261 = 1605587) B1605587
theorem B938871 : Blo 936583 938871 := bstep (se 1 (by rfl) ⟨704153, by rfl⟩ : syracuseStep 938871 = 1408307) B1408307
theorem B938891 : Blo 936583 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B938903 : Blo 936583 938903 := bstep (se 1 (by rfl) ⟨704177, by rfl⟩ : syracuseStep 938903 = 1408355) B1408355
theorem B938923 : Blo 936583 938923 := bstep (se 1 (by rfl) ⟨704192, by rfl⟩ : syracuseStep 938923 = 1408385) B1408385
theorem B938935 : Blo 936583 938935 := bstep (se 1 (by rfl) ⟨704201, by rfl⟩ : syracuseStep 938935 = 1408403) B1408403
theorem B938955 : Blo 936583 938955 := bstep (se 1 (by rfl) ⟨704216, by rfl⟩ : syracuseStep 938955 = 1408433) B1408433
theorem B938967 : Blo 936583 938967 := bstep (se 1 (by rfl) ⟨704225, by rfl⟩ : syracuseStep 938967 = 1408451) B1408451
theorem B938987 : Blo 936583 938987 := bstep (se 1 (by rfl) ⟨704240, by rfl⟩ : syracuseStep 938987 = 1408481) B1408481
theorem B938999 : Blo 936583 938999 := bstep (se 1 (by rfl) ⟨704249, by rfl⟩ : syracuseStep 938999 = 1408499) B1408499
theorem B7918597 : Blo 936583 7918597 := bstep (se 4 (by rfl) ⟨742368, by rfl⟩ : syracuseStep 7918597 = 1484737) B1484737
theorem B939019 : Blo 936583 939019 := bstep (se 1 (by rfl) ⟨704264, by rfl⟩ : syracuseStep 939019 = 1408529) B1408529
theorem B939031 : Blo 936583 939031 := bstep (se 1 (by rfl) ⟨704273, by rfl⟩ : syracuseStep 939031 = 1408547) B1408547
theorem B2380823 : Blo 936583 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B939051 : Blo 936583 939051 := bstep (se 1 (by rfl) ⟨704288, by rfl⟩ : syracuseStep 939051 = 1408577) B1408577
theorem B939063 : Blo 936583 939063 := bstep (se 1 (by rfl) ⟨704297, by rfl⟩ : syracuseStep 939063 = 1408595) B1408595
theorem B939083 : Blo 936583 939083 := bstep (se 1 (by rfl) ⟨704312, by rfl⟩ : syracuseStep 939083 = 1408625) B1408625
theorem B939095 : Blo 936583 939095 := bstep (se 1 (by rfl) ⟨704321, by rfl⟩ : syracuseStep 939095 = 1408643) B1408643
theorem B4281437 : Blo 936583 4281437 := bstep (se 3 (by rfl) ⟨802769, by rfl⟩ : syracuseStep 4281437 = 1605539) B1605539
theorem B939115 : Blo 936583 939115 := bstep (se 1 (by rfl) ⟨704336, by rfl⟩ : syracuseStep 939115 = 1408673) B1408673
theorem B939127 : Blo 936583 939127 := bstep (se 1 (by rfl) ⟨704345, by rfl⟩ : syracuseStep 939127 = 1408691) B1408691
theorem B939147 : Blo 936583 939147 := bstep (se 1 (by rfl) ⟨704360, by rfl⟩ : syracuseStep 939147 = 1408721) B1408721
theorem B939159 : Blo 936583 939159 := bstep (se 1 (by rfl) ⟨704369, by rfl⟩ : syracuseStep 939159 = 1408739) B1408739
theorem B939179 : Blo 936583 939179 := bstep (se 1 (by rfl) ⟨704384, by rfl⟩ : syracuseStep 939179 = 1408769) B1408769
theorem B939191 : Blo 936583 939191 := bstep (se 1 (by rfl) ⟨704393, by rfl⟩ : syracuseStep 939191 = 1408787) B1408787
theorem B939211 : Blo 936583 939211 := bstep (se 1 (by rfl) ⟨704408, by rfl⟩ : syracuseStep 939211 = 1408817) B1408817
theorem B939223 : Blo 936583 939223 := bstep (se 1 (by rfl) ⟨704417, by rfl⟩ : syracuseStep 939223 = 1408835) B1408835
theorem B939243 : Blo 936583 939243 := bstep (se 1 (by rfl) ⟨704432, by rfl⟩ : syracuseStep 939243 = 1408865) B1408865
theorem B939255 : Blo 936583 939255 := bstep (se 1 (by rfl) ⟨704441, by rfl⟩ : syracuseStep 939255 = 1408883) B1408883
theorem B939275 : Blo 936583 939275 := bstep (se 1 (by rfl) ⟨704456, by rfl⟩ : syracuseStep 939275 = 1408913) B1408913
theorem B4281623 : Blo 936583 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B939287 : Blo 936583 939287 := bstep (se 1 (by rfl) ⟨704465, by rfl⟩ : syracuseStep 939287 = 1408931) B1408931
theorem B939307 : Blo 936583 939307 := bstep (se 1 (by rfl) ⟨704480, by rfl⟩ : syracuseStep 939307 = 1408961) B1408961
theorem B939319 : Blo 936583 939319 := bstep (se 1 (by rfl) ⟨704489, by rfl⟩ : syracuseStep 939319 = 1408979) B1408979
theorem B939339 : Blo 936583 939339 := bstep (se 1 (by rfl) ⟨704504, by rfl⟩ : syracuseStep 939339 = 1409009) B1409009
theorem B939351 : Blo 936583 939351 := bstep (se 1 (by rfl) ⟨704513, by rfl⟩ : syracuseStep 939351 = 1409027) B1409027
theorem B939371 : Blo 936583 939371 := bstep (se 1 (by rfl) ⟨704528, by rfl⟩ : syracuseStep 939371 = 1409057) B1409057
theorem B939383 : Blo 936583 939383 := bstep (se 1 (by rfl) ⟨704537, by rfl⟩ : syracuseStep 939383 = 1409075) B1409075
theorem B939403 : Blo 936583 939403 := bstep (se 1 (by rfl) ⟨704552, by rfl⟩ : syracuseStep 939403 = 1409105) B1409105
theorem B3003799 : Blo 936583 3003799 := bstep (se 1 (by rfl) ⟨2252849, by rfl⟩ : syracuseStep 3003799 = 4505699) B4505699
theorem B3167639 : Blo 936583 3167639 := bstep (se 1 (by rfl) ⟨2375729, by rfl⟩ : syracuseStep 3167639 = 4751459) B4751459
theorem B939415 : Blo 936583 939415 := bstep (se 1 (by rfl) ⟨704561, by rfl⟩ : syracuseStep 939415 = 1409123) B1409123
theorem B939435 : Blo 936583 939435 := bstep (se 1 (by rfl) ⟨704576, by rfl⟩ : syracuseStep 939435 = 1409153) B1409153
theorem B939447 : Blo 936583 939447 := bstep (se 1 (by rfl) ⟨704585, by rfl⟩ : syracuseStep 939447 = 1409171) B1409171
theorem B939467 : Blo 936583 939467 := bstep (se 1 (by rfl) ⟨704600, by rfl⟩ : syracuseStep 939467 = 1409201) B1409201
theorem B939479 : Blo 936583 939479 := bstep (se 1 (by rfl) ⟨704609, by rfl⟩ : syracuseStep 939479 = 1409219) B1409219
theorem B939499 : Blo 936583 939499 := bstep (se 1 (by rfl) ⟨704624, by rfl⟩ : syracuseStep 939499 = 1409249) B1409249
theorem B939511 : Blo 936583 939511 := bstep (se 1 (by rfl) ⟨704633, by rfl⟩ : syracuseStep 939511 = 1409267) B1409267
theorem B939531 : Blo 936583 939531 := bstep (se 1 (by rfl) ⟨704648, by rfl⟩ : syracuseStep 939531 = 1409297) B1409297
theorem B939543 : Blo 936583 939543 := bstep (se 1 (by rfl) ⟨704657, by rfl⟩ : syracuseStep 939543 = 1409315) B1409315
theorem B939563 : Blo 936583 939563 := bstep (se 1 (by rfl) ⟨704672, by rfl⟩ : syracuseStep 939563 = 1409345) B1409345
theorem B939575 : Blo 936583 939575 := bstep (se 1 (by rfl) ⟨704681, by rfl⟩ : syracuseStep 939575 = 1409363) B1409363
theorem B939595 : Blo 936583 939595 := bstep (se 1 (by rfl) ⟨704696, by rfl⟩ : syracuseStep 939595 = 1409393) B1409393
theorem B939607 : Blo 936583 939607 := bstep (se 1 (by rfl) ⟨704705, by rfl⟩ : syracuseStep 939607 = 1409411) B1409411
theorem B939627 : Blo 936583 939627 := bstep (se 1 (by rfl) ⟨704720, by rfl⟩ : syracuseStep 939627 = 1409441) B1409441
theorem B939639 : Blo 936583 939639 := bstep (se 1 (by rfl) ⟨704729, by rfl⟩ : syracuseStep 939639 = 1409459) B1409459
theorem B939659 : Blo 936583 939659 := bstep (se 1 (by rfl) ⟨704744, by rfl⟩ : syracuseStep 939659 = 1409489) B1409489
theorem B939671 : Blo 936583 939671 := bstep (se 1 (by rfl) ⟨704753, by rfl⟩ : syracuseStep 939671 = 1409507) B1409507
theorem B939691 : Blo 936583 939691 := bstep (se 1 (by rfl) ⟨704768, by rfl⟩ : syracuseStep 939691 = 1409537) B1409537
theorem B939703 : Blo 936583 939703 := bstep (se 1 (by rfl) ⟨704777, by rfl⟩ : syracuseStep 939703 = 1409555) B1409555
theorem B939723 : Blo 936583 939723 := bstep (se 1 (by rfl) ⟨704792, by rfl⟩ : syracuseStep 939723 = 1409585) B1409585
theorem B939735 : Blo 936583 939735 := bstep (se 1 (by rfl) ⟨704801, by rfl⟩ : syracuseStep 939735 = 1409603) B1409603
theorem B939755 : Blo 936583 939755 := bstep (se 1 (by rfl) ⟨704816, by rfl⟩ : syracuseStep 939755 = 1409633) B1409633
theorem B939767 : Blo 936583 939767 := bstep (se 1 (by rfl) ⟨704825, by rfl⟩ : syracuseStep 939767 = 1409651) B1409651
theorem B939787 : Blo 936583 939787 := bstep (se 1 (by rfl) ⟨704840, by rfl⟩ : syracuseStep 939787 = 1409681) B1409681
theorem B939799 : Blo 936583 939799 := bstep (se 1 (by rfl) ⟨704849, by rfl⟩ : syracuseStep 939799 = 1409699) B1409699
theorem B939819 : Blo 936583 939819 := bstep (se 1 (by rfl) ⟨704864, by rfl⟩ : syracuseStep 939819 = 1409729) B1409729
theorem B939831 : Blo 936583 939831 := bstep (se 1 (by rfl) ⟨704873, by rfl⟩ : syracuseStep 939831 = 1409747) B1409747
theorem B939851 : Blo 936583 939851 := bstep (se 1 (by rfl) ⟨704888, by rfl⟩ : syracuseStep 939851 = 1409777) B1409777
theorem B939863 : Blo 936583 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B7133021 : Blo 936583 7133021 := bstep (se 3 (by rfl) ⟨1337441, by rfl⟩ : syracuseStep 7133021 = 2674883) B2674883
theorem B939883 : Blo 936583 939883 := bstep (se 1 (by rfl) ⟨704912, by rfl⟩ : syracuseStep 939883 = 1409825) B1409825
theorem B939895 : Blo 936583 939895 := bstep (se 1 (by rfl) ⟨704921, by rfl⟩ : syracuseStep 939895 = 1409843) B1409843
theorem B3561347 : Blo 936583 3561347 := bstep (se 1 (by rfl) ⟨2671010, by rfl⟩ : syracuseStep 3561347 = 5342021) B5342021
theorem B939915 : Blo 936583 939915 := bstep (se 1 (by rfl) ⟨704936, by rfl⟩ : syracuseStep 939915 = 1409873) B1409873
theorem B939927 : Blo 936583 939927 := bstep (se 1 (by rfl) ⟨704945, by rfl⟩ : syracuseStep 939927 = 1409891) B1409891
theorem B939947 : Blo 936583 939947 := bstep (se 1 (by rfl) ⟨704960, by rfl⟩ : syracuseStep 939947 = 1409921) B1409921
theorem B3168179 : Blo 936583 3168179 := bstep (se 1 (by rfl) ⟨2376134, by rfl⟩ : syracuseStep 3168179 = 4752269) B4752269
theorem B939959 : Blo 936583 939959 := bstep (se 1 (by rfl) ⟨704969, by rfl⟩ : syracuseStep 939959 = 1409939) B1409939
theorem B939979 : Blo 936583 939979 := bstep (se 1 (by rfl) ⟨704984, by rfl⟩ : syracuseStep 939979 = 1409969) B1409969
theorem B939991 : Blo 936583 939991 := bstep (se 1 (by rfl) ⟨704993, by rfl⟩ : syracuseStep 939991 = 1409987) B1409987
theorem B940011 : Blo 936583 940011 := bstep (se 1 (by rfl) ⟨705008, by rfl⟩ : syracuseStep 940011 = 1410017) B1410017
theorem B940023 : Blo 936583 940023 := bstep (se 1 (by rfl) ⟨705017, by rfl⟩ : syracuseStep 940023 = 1410035) B1410035
theorem B940043 : Blo 936583 940043 := bstep (se 1 (by rfl) ⟨705032, by rfl⟩ : syracuseStep 940043 = 1410065) B1410065
theorem B940055 : Blo 936583 940055 := bstep (se 1 (by rfl) ⟨705041, by rfl⟩ : syracuseStep 940055 = 1410083) B1410083
theorem B940075 : Blo 936583 940075 := bstep (se 1 (by rfl) ⟨705056, by rfl⟩ : syracuseStep 940075 = 1410113) B1410113
theorem B2250803 : Blo 936583 2250803 := bstep (se 1 (by rfl) ⟨1688102, by rfl⟩ : syracuseStep 2250803 = 3376205) B3376205
theorem B940087 : Blo 936583 940087 := bstep (se 1 (by rfl) ⟨705065, by rfl⟩ : syracuseStep 940087 = 1410131) B1410131
theorem B940107 : Blo 936583 940107 := bstep (se 1 (by rfl) ⟨705080, by rfl⟩ : syracuseStep 940107 = 1410161) B1410161
theorem B940119 : Blo 936583 940119 := bstep (se 1 (by rfl) ⟨705089, by rfl⟩ : syracuseStep 940119 = 1410179) B1410179
theorem B940139 : Blo 936583 940139 := bstep (se 1 (by rfl) ⟨705104, by rfl⟩ : syracuseStep 940139 = 1410209) B1410209
theorem B1693811 : Blo 936583 1693811 := bstep (se 1 (by rfl) ⟨1270358, by rfl⟩ : syracuseStep 1693811 = 2540717) B2540717
theorem B940151 : Blo 936583 940151 := bstep (se 1 (by rfl) ⟨705113, by rfl⟩ : syracuseStep 940151 = 1410227) B1410227
theorem B940171 : Blo 936583 940171 := bstep (se 1 (by rfl) ⟨705128, by rfl⟩ : syracuseStep 940171 = 1410257) B1410257
theorem B1202327 : Blo 936583 1202327 := bstep (se 1 (by rfl) ⟨901745, by rfl⟩ : syracuseStep 1202327 = 1803491) B1803491
theorem B940183 : Blo 936583 940183 := bstep (se 1 (by rfl) ⟨705137, by rfl⟩ : syracuseStep 940183 = 1410275) B1410275
theorem B940203 : Blo 936583 940203 := bstep (se 1 (by rfl) ⟨705152, by rfl⟩ : syracuseStep 940203 = 1410305) B1410305
theorem B5068979 : Blo 936583 5068979 := bstep (se 1 (by rfl) ⟨3801734, by rfl⟩ : syracuseStep 5068979 = 7603469) B7603469
theorem B940215 : Blo 936583 940215 := bstep (se 1 (by rfl) ⟨705161, by rfl⟩ : syracuseStep 940215 = 1410323) B1410323
theorem B3168449 : Blo 936583 3168449 := bstep (se 2 (by rfl) ⟨1188168, by rfl⟩ : syracuseStep 3168449 = 2376337) B2376337
theorem B940235 : Blo 936583 940235 := bstep (se 1 (by rfl) ⟨705176, by rfl⟩ : syracuseStep 940235 = 1410353) B1410353
theorem B940247 : Blo 936583 940247 := bstep (se 1 (by rfl) ⟨705185, by rfl⟩ : syracuseStep 940247 = 1410371) B1410371
theorem B940267 : Blo 936583 940267 := bstep (se 1 (by rfl) ⟨705200, by rfl⟩ : syracuseStep 940267 = 1410401) B1410401
theorem B940279 : Blo 936583 940279 := bstep (se 1 (by rfl) ⟨705209, by rfl⟩ : syracuseStep 940279 = 1410419) B1410419
theorem B1693963 : Blo 936583 1693963 := bstep (se 1 (by rfl) ⟨1270472, by rfl⟩ : syracuseStep 1693963 = 2540945) B2540945
theorem B940299 : Blo 936583 940299 := bstep (se 1 (by rfl) ⟨705224, by rfl⟩ : syracuseStep 940299 = 1410449) B1410449
theorem B940311 : Blo 936583 940311 := bstep (se 1 (by rfl) ⟨705233, by rfl⟩ : syracuseStep 940311 = 1410467) B1410467
theorem B940331 : Blo 936583 940331 := bstep (se 1 (by rfl) ⟨705248, by rfl⟩ : syracuseStep 940331 = 1410497) B1410497
theorem B940343 : Blo 936583 940343 := bstep (se 1 (by rfl) ⟨705257, by rfl⟩ : syracuseStep 940343 = 1410515) B1410515
theorem B3561803 : Blo 936583 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B1694027 : Blo 936583 1694027 := bstep (se 1 (by rfl) ⟨1270520, by rfl⟩ : syracuseStep 1694027 = 2541041) B2541041
theorem B940363 : Blo 936583 940363 := bstep (se 1 (by rfl) ⟨705272, by rfl⟩ : syracuseStep 940363 = 1410545) B1410545
theorem B940375 : Blo 936583 940375 := bstep (se 1 (by rfl) ⟨705281, by rfl⟩ : syracuseStep 940375 = 1410563) B1410563
theorem B940395 : Blo 936583 940395 := bstep (se 1 (by rfl) ⟨705296, by rfl⟩ : syracuseStep 940395 = 1410593) B1410593
theorem B940407 : Blo 936583 940407 := bstep (se 1 (by rfl) ⟨705305, by rfl⟩ : syracuseStep 940407 = 1410611) B1410611
theorem B940427 : Blo 936583 940427 := bstep (se 1 (by rfl) ⟨705320, by rfl⟩ : syracuseStep 940427 = 1410641) B1410641
theorem B940439 : Blo 936583 940439 := bstep (se 1 (by rfl) ⟨705329, by rfl⟩ : syracuseStep 940439 = 1410659) B1410659
theorem B940459 : Blo 936583 940459 := bstep (se 1 (by rfl) ⟨705344, by rfl⟩ : syracuseStep 940459 = 1410689) B1410689
theorem B940471 : Blo 936583 940471 := bstep (se 1 (by rfl) ⟨705353, by rfl⟩ : syracuseStep 940471 = 1410707) B1410707
theorem B940491 : Blo 936583 940491 := bstep (se 1 (by rfl) ⟨705368, by rfl⟩ : syracuseStep 940491 = 1410737) B1410737
theorem B940503 : Blo 936583 940503 := bstep (se 1 (by rfl) ⟨705377, by rfl⟩ : syracuseStep 940503 = 1410755) B1410755
theorem B940523 : Blo 936583 940523 := bstep (se 1 (by rfl) ⟨705392, by rfl⟩ : syracuseStep 940523 = 1410785) B1410785
theorem B940535 : Blo 936583 940535 := bstep (se 1 (by rfl) ⟨705401, by rfl⟩ : syracuseStep 940535 = 1410803) B1410803
theorem B940555 : Blo 936583 940555 := bstep (se 1 (by rfl) ⟨705416, by rfl⟩ : syracuseStep 940555 = 1410833) B1410833
theorem B65067533 : Blo 936583 65067533 := bstep (se 3 (by rfl) ⟨12200162, by rfl⟩ : syracuseStep 65067533 = 24400325) B24400325
theorem B3562001 : Blo 936583 3562001 := bstep (se 2 (by rfl) ⟨1335750, by rfl⟩ : syracuseStep 3562001 = 2671501) B2671501
theorem B940567 : Blo 936583 940567 := bstep (se 1 (by rfl) ⟨705425, by rfl⟩ : syracuseStep 940567 = 1410851) B1410851
theorem B1694401 : Blo 936583 1694401 := bstep (se 2 (by rfl) ⟨635400, by rfl⟩ : syracuseStep 1694401 = 1270801) B1270801
theorem B3168989 : Blo 936583 3168989 := bstep (se 3 (by rfl) ⟨594185, by rfl⟩ : syracuseStep 3168989 = 1188371) B1188371
theorem B1203211 : Blo 936583 1203211 := bstep (se 1 (by rfl) ⟨902408, by rfl⟩ : syracuseStep 1203211 = 1804817) B1804817
theorem B3005657 : Blo 936583 3005657 := bstep (se 2 (by rfl) ⟨1127121, by rfl⟩ : syracuseStep 3005657 = 2254243) B2254243
theorem B8117509 : Blo 936583 8117509 := bstep (se 4 (by rfl) ⟨761016, by rfl⟩ : syracuseStep 8117509 = 1522033) B1522033
theorem B3562775 : Blo 936583 3562775 := bstep (se 1 (by rfl) ⟨2672081, by rfl⟩ : syracuseStep 3562775 = 5344163) B5344163
theorem B9002285 : Blo 936583 9002285 := bstep (se 3 (by rfl) ⟨1687928, by rfl⟩ : syracuseStep 9002285 = 3375857) B3375857
theorem B3431825 : Blo 936583 3431825 := bstep (se 2 (by rfl) ⟨1286934, by rfl⟩ : syracuseStep 3431825 = 2573869) B2573869
theorem B1334731 : Blo 936583 1334731 := bstep (se 1 (by rfl) ⟨1001048, by rfl⟩ : syracuseStep 1334731 = 2002097) B2002097
theorem B3562973 : Blo 936583 3562973 := bstep (se 3 (by rfl) ⟨668057, by rfl⟩ : syracuseStep 3562973 = 1336115) B1336115
theorem B4742873 : Blo 936583 4742873 := bstep (se 2 (by rfl) ⟨1778577, by rfl⟩ : syracuseStep 4742873 = 3557155) B3557155
theorem B3170123 : Blo 936583 3170123 := bstep (se 1 (by rfl) ⟨2377592, by rfl⟩ : syracuseStep 3170123 = 4755185) B4755185
theorem B3170393 : Blo 936583 3170393 := bstep (se 2 (by rfl) ⟨1188897, by rfl⟩ : syracuseStep 3170393 = 2377795) B2377795
theorem B8577175 : Blo 936583 8577175 := bstep (se 1 (by rfl) ⟨6432881, by rfl⟩ : syracuseStep 8577175 = 12865763) B12865763
theorem B1335961 : Blo 936583 1335961 := bstep (se 2 (by rfl) ⟨500985, by rfl⟩ : syracuseStep 1335961 = 1001971) B1001971
theorem B6513331 : Blo 936583 6513331 := bstep (se 1 (by rfl) ⟨4884998, by rfl⟩ : syracuseStep 6513331 = 9769997) B9769997
theorem B3171095 : Blo 936583 3171095 := bstep (se 1 (by rfl) ⟨2378321, by rfl⟩ : syracuseStep 3171095 = 4756643) B4756643
theorem B10150757 : Blo 936583 10150757 := bstep (se 4 (by rfl) ⟨951633, by rfl⟩ : syracuseStep 10150757 = 1903267) B1903267
theorem B4744493 : Blo 936583 4744493 := bstep (se 3 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 4744493 = 1779185) B1779185
theorem B3171635 : Blo 936583 3171635 := bstep (se 1 (by rfl) ⟨2378726, by rfl⟩ : syracuseStep 3171635 = 4757453) B4757453
theorem B3564931 : Blo 936583 3564931 := bstep (se 1 (by rfl) ⟨2673698, by rfl⟩ : syracuseStep 3564931 = 5347397) B5347397
theorem B2254387 : Blo 936583 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B3171905 : Blo 936583 3171905 := bstep (se 2 (by rfl) ⟨1189464, by rfl⟩ : syracuseStep 3171905 = 2378929) B2378929
theorem B6416023 : Blo 936583 6416023 := bstep (se 1 (by rfl) ⟨4812017, by rfl⟩ : syracuseStep 6416023 = 9624035) B9624035
theorem B3565235 : Blo 936583 3565235 := bstep (se 1 (by rfl) ⟨2673926, by rfl⟩ : syracuseStep 3565235 = 5347853) B5347853
theorem B2057971 : Blo 936583 2057971 := bstep (se 1 (by rfl) ⟨1543478, by rfl⟩ : syracuseStep 2057971 = 3086957) B3086957
theorem B1337305 : Blo 936583 1337305 := bstep (se 2 (by rfl) ⟨501489, by rfl⟩ : syracuseStep 1337305 = 1002979) B1002979
theorem B1304537 : Blo 936583 1304537 := bstep (se 2 (by rfl) ⟨489201, by rfl⟩ : syracuseStep 1304537 = 978403) B978403
theorem B8546309 : Blo 936583 8546309 := bstep (se 4 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 8546309 = 1602433) B1602433
theorem B10709009 : Blo 936583 10709009 := bstep (se 2 (by rfl) ⟨4015878, by rfl⟩ : syracuseStep 10709009 = 8031757) B8031757
theorem B4515905 : Blo 936583 4515905 := bstep (se 2 (by rfl) ⟨1693464, by rfl⟩ : syracuseStep 4515905 = 3386929) B3386929
theorem B1337419 : Blo 936583 1337419 := bstep (se 1 (by rfl) ⟨1003064, by rfl⟩ : syracuseStep 1337419 = 2006129) B2006129
theorem B2058329 : Blo 936583 2058329 := bstep (se 2 (by rfl) ⟨771873, by rfl⟩ : syracuseStep 2058329 = 1543747) B1543747
theorem B3172445 : Blo 936583 3172445 := bstep (se 3 (by rfl) ⟨594833, by rfl⟩ : syracuseStep 3172445 = 1189667) B1189667
theorem B3565889 : Blo 936583 3565889 := bstep (se 2 (by rfl) ⟨1337208, by rfl⟩ : syracuseStep 3565889 = 2674417) B2674417
theorem B2255435 : Blo 936583 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B3173579 : Blo 936583 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B3009757 : Blo 936583 3009757 := bstep (se 3 (by rfl) ⟨564329, by rfl⟩ : syracuseStep 3009757 = 1128659) B1128659
theorem B1338763 : Blo 936583 1338763 := bstep (se 1 (by rfl) ⟨1004072, by rfl⟩ : syracuseStep 1338763 = 2008145) B2008145
theorem B3173849 : Blo 936583 3173849 := bstep (se 2 (by rfl) ⟨1190193, by rfl⟩ : syracuseStep 3173849 = 2380387) B2380387
theorem B3567149 : Blo 936583 3567149 := bstep (se 3 (by rfl) ⟨668840, by rfl⟩ : syracuseStep 3567149 = 1337681) B1337681
theorem B3567179 : Blo 936583 3567179 := bstep (se 1 (by rfl) ⟨2675384, by rfl⟩ : syracuseStep 3567179 = 5350769) B5350769
theorem B1339031 : Blo 936583 1339031 := bstep (se 1 (by rfl) ⟨1004273, by rfl⟩ : syracuseStep 1339031 = 2008547) B2008547
theorem B15200045 : Blo 936583 15200045 := bstep (se 3 (by rfl) ⟨2850008, by rfl⟩ : syracuseStep 15200045 = 5700017) B5700017
theorem B6418277 : Blo 936583 6418277 := bstep (se 4 (by rfl) ⟨601713, by rfl⟩ : syracuseStep 6418277 = 1203427) B1203427
theorem B1404875 : Blo 936583 1404875 := bstep (se 1 (by rfl) ⟨1053656, by rfl⟩ : syracuseStep 1404875 = 2107313) B2107313
theorem B1404887 : Blo 936583 1404887 := bstep (se 1 (by rfl) ⟨1053665, by rfl⟩ : syracuseStep 1404887 = 2107331) B2107331
theorem B1404953 : Blo 936583 1404953 := bstep (se 2 (by rfl) ⟨526857, by rfl⟩ : syracuseStep 1404953 = 1053715) B1053715
theorem B1405067 : Blo 936583 1405067 := bstep (se 1 (by rfl) ⟨1053800, by rfl⟩ : syracuseStep 1405067 = 2107601) B2107601
theorem B1405079 : Blo 936583 1405079 := bstep (se 1 (by rfl) ⟨1053809, by rfl⟩ : syracuseStep 1405079 = 2107619) B2107619
theorem B1405145 : Blo 936583 1405145 := bstep (se 2 (by rfl) ⟨526929, by rfl⟩ : syracuseStep 1405145 = 1053859) B1053859
theorem B3567833 : Blo 936583 3567833 := bstep (se 2 (by rfl) ⟨1337937, by rfl⟩ : syracuseStep 3567833 = 2675875) B2675875
theorem B1405259 : Blo 936583 1405259 := bstep (se 1 (by rfl) ⟨1053944, by rfl⟩ : syracuseStep 1405259 = 2107889) B2107889
theorem B1405271 : Blo 936583 1405271 := bstep (se 1 (by rfl) ⟨1053953, by rfl⟩ : syracuseStep 1405271 = 2107907) B2107907
theorem B16052579 : Blo 936583 16052579 := bstep (se 1 (by rfl) ⟨12039434, by rfl⟩ : syracuseStep 16052579 = 24078869) B24078869
theorem B1405337 : Blo 936583 1405337 := bstep (se 2 (by rfl) ⟨527001, by rfl⟩ : syracuseStep 1405337 = 1054003) B1054003
theorem B1405451 : Blo 936583 1405451 := bstep (se 1 (by rfl) ⟨1054088, by rfl⟩ : syracuseStep 1405451 = 2108177) B2108177
theorem B6844945 : Blo 936583 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B3568151 : Blo 936583 3568151 := bstep (se 1 (by rfl) ⟨2676113, by rfl⟩ : syracuseStep 3568151 = 5352227) B5352227
theorem B1405463 : Blo 936583 1405463 := bstep (se 1 (by rfl) ⟨1054097, by rfl⟩ : syracuseStep 1405463 = 2108195) B2108195
theorem B3797549 : Blo 936583 3797549 := bstep (se 3 (by rfl) ⟨712040, by rfl⟩ : syracuseStep 3797549 = 1424081) B1424081
theorem B1405529 : Blo 936583 1405529 := bstep (se 2 (by rfl) ⟨527073, by rfl⟩ : syracuseStep 1405529 = 1054147) B1054147
theorem B5075549 : Blo 936583 5075549 := bstep (se 3 (by rfl) ⟨951665, by rfl⟩ : syracuseStep 5075549 = 1903331) B1903331
theorem B1405643 : Blo 936583 1405643 := bstep (se 1 (by rfl) ⟨1054232, by rfl⟩ : syracuseStep 1405643 = 2108465) B2108465
theorem B1405655 : Blo 936583 1405655 := bstep (se 1 (by rfl) ⟨1054241, by rfl⟩ : syracuseStep 1405655 = 2108483) B2108483
theorem B3666653 : Blo 936583 3666653 := bstep (se 3 (by rfl) ⟨687497, by rfl⟩ : syracuseStep 3666653 = 1374995) B1374995
theorem B1405721 : Blo 936583 1405721 := bstep (se 2 (by rfl) ⟨527145, by rfl⟩ : syracuseStep 1405721 = 1054291) B1054291
theorem B10711925 : Blo 936583 10711925 := bstep (se 5 (by rfl) ⟨502121, by rfl⟩ : syracuseStep 10711925 = 1004243) B1004243
theorem B4518787 : Blo 936583 4518787 := bstep (se 1 (by rfl) ⟨3389090, by rfl⟩ : syracuseStep 4518787 = 6778181) B6778181
theorem B1405835 : Blo 936583 1405835 := bstep (se 1 (by rfl) ⟨1054376, by rfl⟩ : syracuseStep 1405835 = 2108753) B2108753
theorem B1405847 : Blo 936583 1405847 := bstep (se 1 (by rfl) ⟨1054385, by rfl⟩ : syracuseStep 1405847 = 2108771) B2108771
theorem B1405913 : Blo 936583 1405913 := bstep (se 2 (by rfl) ⟨527217, by rfl⟩ : syracuseStep 1405913 = 1054435) B1054435
theorem B1406027 : Blo 936583 1406027 := bstep (se 1 (by rfl) ⟨1054520, by rfl⟩ : syracuseStep 1406027 = 2109041) B2109041
theorem B1406039 : Blo 936583 1406039 := bstep (se 1 (by rfl) ⟨1054529, by rfl⟩ : syracuseStep 1406039 = 2109059) B2109059
theorem B4748381 : Blo 936583 4748381 := bstep (se 3 (by rfl) ⟨890321, by rfl⟩ : syracuseStep 4748381 = 1780643) B1780643
theorem B1406105 : Blo 936583 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B3568819 : Blo 936583 3568819 := bstep (se 1 (by rfl) ⟨2676614, by rfl⟩ : syracuseStep 3568819 = 5353229) B5353229
theorem B1406219 : Blo 936583 1406219 := bstep (se 1 (by rfl) ⟨1054664, by rfl⟩ : syracuseStep 1406219 = 2109329) B2109329
theorem B1406231 : Blo 936583 1406231 := bstep (se 1 (by rfl) ⟨1054673, by rfl⟩ : syracuseStep 1406231 = 2109347) B2109347
theorem B1406297 : Blo 936583 1406297 := bstep (se 2 (by rfl) ⟨527361, by rfl⟩ : syracuseStep 1406297 = 1054723) B1054723
theorem B1406411 : Blo 936583 1406411 := bstep (se 1 (by rfl) ⟨1054808, by rfl⟩ : syracuseStep 1406411 = 2109617) B2109617
theorem B1406423 : Blo 936583 1406423 := bstep (se 1 (by rfl) ⟨1054817, by rfl⟩ : syracuseStep 1406423 = 2109635) B2109635
theorem B1406489 : Blo 936583 1406489 := bstep (se 2 (by rfl) ⟨527433, by rfl⟩ : syracuseStep 1406489 = 1054867) B1054867
theorem B1406603 : Blo 936583 1406603 := bstep (se 1 (by rfl) ⟨1054952, by rfl⟩ : syracuseStep 1406603 = 2109905) B2109905
theorem B4290193 : Blo 936583 4290193 := bstep (se 2 (by rfl) ⟨1608822, by rfl⟩ : syracuseStep 4290193 = 3217645) B3217645
theorem B1406615 : Blo 936583 1406615 := bstep (se 1 (by rfl) ⟨1054961, by rfl⟩ : syracuseStep 1406615 = 2109923) B2109923
theorem B1406681 : Blo 936583 1406681 := bstep (se 2 (by rfl) ⟨527505, by rfl⟩ : syracuseStep 1406681 = 1055011) B1055011
theorem B1406795 : Blo 936583 1406795 := bstep (se 1 (by rfl) ⟨1055096, by rfl⟩ : syracuseStep 1406795 = 2110193) B2110193
theorem B1406807 : Blo 936583 1406807 := bstep (se 1 (by rfl) ⟨1055105, by rfl⟩ : syracuseStep 1406807 = 2110211) B2110211
theorem B1406873 : Blo 936583 1406873 := bstep (se 2 (by rfl) ⟨527577, by rfl⟩ : syracuseStep 1406873 = 1055155) B1055155
theorem B1406987 : Blo 936583 1406987 := bstep (se 1 (by rfl) ⟨1055240, by rfl⟩ : syracuseStep 1406987 = 2110481) B2110481
theorem B1406999 : Blo 936583 1406999 := bstep (se 1 (by rfl) ⟨1055249, by rfl⟩ : syracuseStep 1406999 = 2110499) B2110499
theorem B1407065 : Blo 936583 1407065 := bstep (se 2 (by rfl) ⟨527649, by rfl⟩ : syracuseStep 1407065 = 1055299) B1055299
theorem B1407179 : Blo 936583 1407179 := bstep (se 1 (by rfl) ⟨1055384, by rfl⟩ : syracuseStep 1407179 = 2110769) B2110769
theorem B1407191 : Blo 936583 1407191 := bstep (se 1 (by rfl) ⟨1055393, by rfl⟩ : syracuseStep 1407191 = 2110787) B2110787
theorem B1407257 : Blo 936583 1407257 := bstep (se 2 (by rfl) ⟨527721, by rfl⟩ : syracuseStep 1407257 = 1055443) B1055443
theorem B17365313 : Blo 936583 17365313 := bstep (se 2 (by rfl) ⟨6511992, by rfl⟩ : syracuseStep 17365313 = 13023985) B13023985
theorem B1407371 : Blo 936583 1407371 := bstep (se 1 (by rfl) ⟨1055528, by rfl⟩ : syracuseStep 1407371 = 2111057) B2111057
theorem B3570065 : Blo 936583 3570065 := bstep (se 2 (by rfl) ⟨1338774, by rfl⟩ : syracuseStep 3570065 = 2677549) B2677549
theorem B1407383 : Blo 936583 1407383 := bstep (se 1 (by rfl) ⟨1055537, by rfl⟩ : syracuseStep 1407383 = 2111075) B2111075
theorem B1407449 : Blo 936583 1407449 := bstep (se 2 (by rfl) ⟨527793, by rfl⟩ : syracuseStep 1407449 = 1055587) B1055587
theorem B1407563 : Blo 936583 1407563 := bstep (se 1 (by rfl) ⟨1055672, by rfl⟩ : syracuseStep 1407563 = 2111345) B2111345
theorem B1407575 : Blo 936583 1407575 := bstep (se 1 (by rfl) ⟨1055681, by rfl⟩ : syracuseStep 1407575 = 2111363) B2111363
theorem B1407641 : Blo 936583 1407641 := bstep (se 2 (by rfl) ⟨527865, by rfl⟩ : syracuseStep 1407641 = 1055731) B1055731
theorem B1407755 : Blo 936583 1407755 := bstep (se 1 (by rfl) ⟨1055816, by rfl⟩ : syracuseStep 1407755 = 2111633) B2111633
theorem B1407767 : Blo 936583 1407767 := bstep (se 1 (by rfl) ⟨1055825, by rfl⟩ : syracuseStep 1407767 = 2111651) B2111651
theorem B1407833 : Blo 936583 1407833 := bstep (se 2 (by rfl) ⟨527937, by rfl⟩ : syracuseStep 1407833 = 1055875) B1055875
theorem B1407947 : Blo 936583 1407947 := bstep (se 1 (by rfl) ⟨1055960, by rfl⟩ : syracuseStep 1407947 = 2111921) B2111921
theorem B1407959 : Blo 936583 1407959 := bstep (se 1 (by rfl) ⟨1055969, by rfl⟩ : syracuseStep 1407959 = 2111939) B2111939
theorem B1408025 : Blo 936583 1408025 := bstep (se 2 (by rfl) ⟨528009, by rfl⟩ : syracuseStep 1408025 = 1056019) B1056019
theorem B2849867 : Blo 936583 2849867 := bstep (se 1 (by rfl) ⟨2137400, by rfl⟩ : syracuseStep 2849867 = 4274801) B4274801
theorem B3570763 : Blo 936583 3570763 := bstep (se 1 (by rfl) ⟨2678072, by rfl⟩ : syracuseStep 3570763 = 5356145) B5356145
theorem B1408139 : Blo 936583 1408139 := bstep (se 1 (by rfl) ⟨1056104, by rfl⟩ : syracuseStep 1408139 = 2112209) B2112209
theorem B3800209 : Blo 936583 3800209 := bstep (se 2 (by rfl) ⟨1425078, by rfl⟩ : syracuseStep 3800209 = 2850157) B2850157
theorem B4062359 : Blo 936583 4062359 := bstep (se 1 (by rfl) ⟨3046769, by rfl⟩ : syracuseStep 4062359 = 6093539) B6093539
theorem B4750487 : Blo 936583 4750487 := bstep (se 1 (by rfl) ⟨3562865, by rfl⟩ : syracuseStep 4750487 = 7125731) B7125731
theorem B1408151 : Blo 936583 1408151 := bstep (se 1 (by rfl) ⟨1056113, by rfl⟩ : syracuseStep 1408151 = 2112227) B2112227
theorem B1408217 : Blo 936583 1408217 := bstep (se 2 (by rfl) ⟨528081, by rfl⟩ : syracuseStep 1408217 = 1056163) B1056163
theorem B5078317 : Blo 936583 5078317 := bstep (se 3 (by rfl) ⟨952184, by rfl⟩ : syracuseStep 5078317 = 1904369) B1904369
theorem B1408331 : Blo 936583 1408331 := bstep (se 1 (by rfl) ⟨1056248, by rfl⟩ : syracuseStep 1408331 = 2112497) B2112497
theorem B1408343 : Blo 936583 1408343 := bstep (se 1 (by rfl) ⟨1056257, by rfl⟩ : syracuseStep 1408343 = 2112515) B2112515
theorem B3571037 : Blo 936583 3571037 := bstep (se 3 (by rfl) ⟨669569, by rfl⟩ : syracuseStep 3571037 = 1339139) B1339139
theorem B1408409 : Blo 936583 1408409 := bstep (se 2 (by rfl) ⟨528153, by rfl⟩ : syracuseStep 1408409 = 1056307) B1056307
theorem B1408523 : Blo 936583 1408523 := bstep (se 1 (by rfl) ⟨1056392, by rfl⟩ : syracuseStep 1408523 = 2112785) B2112785
theorem B1408535 : Blo 936583 1408535 := bstep (se 1 (by rfl) ⟨1056401, by rfl⟩ : syracuseStep 1408535 = 2112803) B2112803
theorem B1408601 : Blo 936583 1408601 := bstep (se 2 (by rfl) ⟨528225, by rfl⟩ : syracuseStep 1408601 = 1056451) B1056451
theorem B2850497 : Blo 936583 2850497 := bstep (se 2 (by rfl) ⟨1068936, by rfl⟩ : syracuseStep 2850497 = 2137873) B2137873
theorem B1408715 : Blo 936583 1408715 := bstep (se 1 (by rfl) ⟨1056536, by rfl⟩ : syracuseStep 1408715 = 2113073) B2113073
theorem B11402957 : Blo 936583 11402957 := bstep (se 3 (by rfl) ⟨2138054, by rfl⟩ : syracuseStep 11402957 = 4276109) B4276109
theorem B1408727 : Blo 936583 1408727 := bstep (se 1 (by rfl) ⟨1056545, by rfl⟩ : syracuseStep 1408727 = 2113091) B2113091
theorem B1408793 : Blo 936583 1408793 := bstep (se 2 (by rfl) ⟨528297, by rfl⟩ : syracuseStep 1408793 = 1056595) B1056595
theorem B4063051 : Blo 936583 4063051 := bstep (se 1 (by rfl) ⟨3047288, by rfl⟩ : syracuseStep 4063051 = 6094577) B6094577
theorem B1408907 : Blo 936583 1408907 := bstep (se 1 (by rfl) ⟨1056680, by rfl⟩ : syracuseStep 1408907 = 2113361) B2113361
theorem B1408919 : Blo 936583 1408919 := bstep (se 1 (by rfl) ⟨1056689, by rfl⟩ : syracuseStep 1408919 = 2113379) B2113379
theorem B1408985 : Blo 936583 1408985 := bstep (se 2 (by rfl) ⟨528369, by rfl⟩ : syracuseStep 1408985 = 1056739) B1056739
theorem B1409039 : Blo 936583 1409039 := bstep (se 1 (by rfl) ⟨1056779, by rfl⟩ : syracuseStep 1409039 = 2113559) B2113559
theorem B1409081 : Blo 936583 1409081 := bstep (se 2 (by rfl) ⟨528405, by rfl⟩ : syracuseStep 1409081 = 1056811) B1056811
theorem B5701751 : Blo 936583 5701751 := bstep (se 1 (by rfl) ⟨4276313, by rfl⟩ : syracuseStep 5701751 = 8552627) B8552627
theorem B1409159 : Blo 936583 1409159 := bstep (se 1 (by rfl) ⟨1056869, by rfl⟩ : syracuseStep 1409159 = 2113739) B2113739
theorem B1409195 : Blo 936583 1409195 := bstep (se 1 (by rfl) ⟨1056896, by rfl⟩ : syracuseStep 1409195 = 2113793) B2113793
theorem B1409225 : Blo 936583 1409225 := bstep (se 2 (by rfl) ⟨528459, by rfl⟩ : syracuseStep 1409225 = 1056919) B1056919
theorem B11436233 : Blo 936583 11436233 := bstep (se 2 (by rfl) ⟨4288587, by rfl⟩ : syracuseStep 11436233 = 8577175) B8577175
theorem B7602491 : Blo 936583 7602491 := bstep (se 1 (by rfl) ⟨5701868, by rfl⟩ : syracuseStep 7602491 = 11403737) B11403737
theorem B1409339 : Blo 936583 1409339 := bstep (se 1 (by rfl) ⟨1057004, by rfl⟩ : syracuseStep 1409339 = 2114009) B2114009
theorem B1409399 : Blo 936583 1409399 := bstep (se 1 (by rfl) ⟨1057049, by rfl⟩ : syracuseStep 1409399 = 2114099) B2114099
theorem B1409423 : Blo 936583 1409423 := bstep (se 1 (by rfl) ⟨1057067, by rfl⟩ : syracuseStep 1409423 = 2114135) B2114135
theorem B1409465 : Blo 936583 1409465 := bstep (se 2 (by rfl) ⟨528549, by rfl⟩ : syracuseStep 1409465 = 1057099) B1057099
theorem B1409543 : Blo 936583 1409543 := bstep (se 1 (by rfl) ⟨1057157, by rfl⟩ : syracuseStep 1409543 = 2114315) B2114315
theorem B1409579 : Blo 936583 1409579 := bstep (se 1 (by rfl) ⟨1057184, by rfl⟩ : syracuseStep 1409579 = 2114369) B2114369
theorem B1409609 : Blo 936583 1409609 := bstep (se 2 (by rfl) ⟨528603, by rfl⟩ : syracuseStep 1409609 = 1057207) B1057207
theorem B1409723 : Blo 936583 1409723 := bstep (se 1 (by rfl) ⟨1057292, by rfl⟩ : syracuseStep 1409723 = 2114585) B2114585
theorem B1409783 : Blo 936583 1409783 := bstep (se 1 (by rfl) ⟨1057337, by rfl⟩ : syracuseStep 1409783 = 2114675) B2114675
theorem B1409807 : Blo 936583 1409807 := bstep (se 1 (by rfl) ⟨1057355, by rfl⟩ : syracuseStep 1409807 = 2114711) B2114711
theorem B1409849 : Blo 936583 1409849 := bstep (se 2 (by rfl) ⟨528693, by rfl⟩ : syracuseStep 1409849 = 1057387) B1057387
theorem B3375931 : Blo 936583 3375931 := bstep (se 1 (by rfl) ⟨2531948, by rfl⟩ : syracuseStep 3375931 = 5063897) B5063897
theorem B14451571 : Blo 936583 14451571 := bstep (se 1 (by rfl) ⟨10838678, by rfl⟩ : syracuseStep 14451571 = 21677357) B21677357
theorem B1409927 : Blo 936583 1409927 := bstep (se 1 (by rfl) ⟨1057445, by rfl⟩ : syracuseStep 1409927 = 2114891) B2114891
theorem B8684441 : Blo 936583 8684441 := bstep (se 2 (by rfl) ⟨3256665, by rfl⟩ : syracuseStep 8684441 = 6513331) B6513331
theorem B1409963 : Blo 936583 1409963 := bstep (se 1 (by rfl) ⟨1057472, by rfl⟩ : syracuseStep 1409963 = 2114945) B2114945
theorem B1409993 : Blo 936583 1409993 := bstep (se 2 (by rfl) ⟨528747, by rfl⟩ : syracuseStep 1409993 = 1057495) B1057495
theorem B1410107 : Blo 936583 1410107 := bstep (se 1 (by rfl) ⟨1057580, by rfl⟩ : syracuseStep 1410107 = 2115161) B2115161
theorem B1410167 : Blo 936583 1410167 := bstep (se 1 (by rfl) ⟨1057625, by rfl⟩ : syracuseStep 1410167 = 2115251) B2115251
theorem B1410191 : Blo 936583 1410191 := bstep (se 1 (by rfl) ⟨1057643, by rfl⟩ : syracuseStep 1410191 = 2115287) B2115287
theorem B1410233 : Blo 936583 1410233 := bstep (se 2 (by rfl) ⟨528837, by rfl⟩ : syracuseStep 1410233 = 1057675) B1057675
theorem B5080265 : Blo 936583 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B1410311 : Blo 936583 1410311 := bstep (se 1 (by rfl) ⟨1057733, by rfl⟩ : syracuseStep 1410311 = 2115467) B2115467
theorem B1410347 : Blo 936583 1410347 := bstep (se 1 (by rfl) ⟨1057760, by rfl⟩ : syracuseStep 1410347 = 2115521) B2115521
theorem B1410377 : Blo 936583 1410377 := bstep (se 2 (by rfl) ⟨528891, by rfl⟩ : syracuseStep 1410377 = 1057783) B1057783
theorem B4752755 : Blo 936583 4752755 := bstep (se 1 (by rfl) ⟨3564566, by rfl⟩ : syracuseStep 4752755 = 7129133) B7129133
theorem B1410491 : Blo 936583 1410491 := bstep (se 1 (by rfl) ⟨1057868, by rfl⟩ : syracuseStep 1410491 = 2115737) B2115737
theorem B1410551 : Blo 936583 1410551 := bstep (se 1 (by rfl) ⟨1057913, by rfl⟩ : syracuseStep 1410551 = 2115827) B2115827
theorem B1410575 : Blo 936583 1410575 := bstep (se 1 (by rfl) ⟨1057931, by rfl⟩ : syracuseStep 1410575 = 2115863) B2115863
theorem B3606059 : Blo 936583 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B1410617 : Blo 936583 1410617 := bstep (se 2 (by rfl) ⟨528981, by rfl⟩ : syracuseStep 1410617 = 1057963) B1057963
theorem B7603789 : Blo 936583 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B1410695 : Blo 936583 1410695 := bstep (se 1 (by rfl) ⟨1058021, by rfl⟩ : syracuseStep 1410695 = 2116043) B2116043
theorem B1410731 : Blo 936583 1410731 := bstep (se 1 (by rfl) ⟨1058048, by rfl⟩ : syracuseStep 1410731 = 2116097) B2116097
theorem B1410761 : Blo 936583 1410761 := bstep (se 2 (by rfl) ⟨529035, by rfl⟩ : syracuseStep 1410761 = 1058071) B1058071
theorem B952079 : Blo 936583 952079 := bstep (se 1 (by rfl) ⟨714059, by rfl⟩ : syracuseStep 952079 = 1428119) B1428119
theorem B1410875 : Blo 936583 1410875 := bstep (se 1 (by rfl) ⟨1058156, by rfl⟩ : syracuseStep 1410875 = 2116313) B2116313
theorem B6752089 : Blo 936583 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B4753241 : Blo 936583 4753241 := bstep (se 2 (by rfl) ⟨1782465, by rfl⟩ : syracuseStep 4753241 = 3564931) B3564931
theorem B8554697 : Blo 936583 8554697 := bstep (se 2 (by rfl) ⟨3208011, by rfl⟩ : syracuseStep 8554697 = 6416023) B6416023
theorem B7113095 : Blo 936583 7113095 := bstep (se 1 (by rfl) ⟨5334821, by rfl⟩ : syracuseStep 7113095 = 10669643) B10669643
theorem B4819409 : Blo 936583 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B18025253 : Blo 936583 18025253 := bstep (se 4 (by rfl) ⟨1689867, by rfl⟩ : syracuseStep 18025253 = 3379735) B3379735
theorem B2854291 : Blo 936583 2854291 := bstep (se 1 (by rfl) ⟨2140718, by rfl⟩ : syracuseStep 2854291 = 4281437) B4281437
theorem B2854415 : Blo 936583 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B4755347 : Blo 936583 4755347 := bstep (se 1 (by rfl) ⟨3566510, by rfl⟩ : syracuseStep 4755347 = 7133021) B7133021
theorem B5083033 : Blo 936583 5083033 := bstep (se 2 (by rfl) ⟨1906137, by rfl⟩ : syracuseStep 5083033 = 3812275) B3812275
theorem B3379319 : Blo 936583 3379319 := bstep (se 1 (by rfl) ⟨2534489, by rfl⟩ : syracuseStep 3379319 = 5068979) B5068979
theorem B4002347 : Blo 936583 4002347 := bstep (se 1 (by rfl) ⟨3001760, by rfl⟩ : syracuseStep 4002347 = 6003521) B6003521
theorem B6754859 : Blo 936583 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B2003771 : Blo 936583 2003771 := bstep (se 1 (by rfl) ⟨1502828, by rfl⟩ : syracuseStep 2003771 = 3005657) B3005657
theorem B6001523 : Blo 936583 6001523 := bstep (se 1 (by rfl) ⟨4501142, by rfl⟩ : syracuseStep 6001523 = 9002285) B9002285
theorem B1053967 : Blo 936583 1053967 := bstep (se 1 (by rfl) ⟨790475, by rfl⟩ : syracuseStep 1053967 = 1580951) B1580951
theorem B1054471 : Blo 936583 1054471 := bstep (se 1 (by rfl) ⟨790853, by rfl⟩ : syracuseStep 1054471 = 1581707) B1581707
theorem B1054651 : Blo 936583 1054651 := bstep (se 1 (by rfl) ⟨790988, by rfl⟩ : syracuseStep 1054651 = 1581977) B1581977
theorem B1906721 : Blo 936583 1906721 := bstep (se 2 (by rfl) ⟨715020, by rfl⟩ : syracuseStep 1906721 = 1430041) B1430041
theorem B1185835 : Blo 936583 1185835 := bstep (se 1 (by rfl) ⟨889376, by rfl⟩ : syracuseStep 1185835 = 1778753) B1778753
theorem B46307501 : Blo 936583 46307501 := bstep (se 3 (by rfl) ⟨8682656, by rfl⟩ : syracuseStep 46307501 = 17365313) B17365313
theorem B1055119 : Blo 936583 1055119 := bstep (se 1 (by rfl) ⟨791339, by rfl⟩ : syracuseStep 1055119 = 1582679) B1582679
theorem B10558129 : Blo 936583 10558129 := bstep (se 2 (by rfl) ⟨3959298, by rfl⟩ : syracuseStep 10558129 = 7918597) B7918597
theorem B1055623 : Blo 936583 1055623 := bstep (se 1 (by rfl) ⟨791717, by rfl⟩ : syracuseStep 1055623 = 1583435) B1583435
theorem B4758425 : Blo 936583 4758425 := bstep (se 2 (by rfl) ⟨1784409, by rfl⟩ : syracuseStep 4758425 = 3568819) B3568819
theorem B1186807 : Blo 936583 1186807 := bstep (se 1 (by rfl) ⟨890105, by rfl⟩ : syracuseStep 1186807 = 1780211) B1780211
theorem B1055803 : Blo 936583 1055803 := bstep (se 1 (by rfl) ⟨791852, by rfl⟩ : syracuseStep 1055803 = 1583705) B1583705
theorem B4005065 : Blo 936583 4005065 := bstep (se 2 (by rfl) ⟨1501899, by rfl⟩ : syracuseStep 4005065 = 3003799) B3003799
theorem B1187131 : Blo 936583 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B1056271 : Blo 936583 1056271 := bstep (se 1 (by rfl) ⟨792203, by rfl⟩ : syracuseStep 1056271 = 1584407) B1584407
theorem B5349037 : Blo 936583 5349037 := bstep (se 3 (by rfl) ⟨1002944, by rfl⟩ : syracuseStep 5349037 = 2005889) B2005889
theorem B1580843 : Blo 936583 1580843 := bstep (se 1 (by rfl) ⟨1185632, by rfl⟩ : syracuseStep 1580843 = 2371265) B2371265
theorem B10133363 : Blo 936583 10133363 := bstep (se 1 (by rfl) ⟨7600022, by rfl⟩ : syracuseStep 10133363 = 15200045) B15200045
theorem B1056775 : Blo 936583 1056775 := bstep (se 1 (by rfl) ⟨792581, by rfl⟩ : syracuseStep 1056775 = 1585163) B1585163
theorem B1581241 : Blo 936583 1581241 := bstep (se 2 (by rfl) ⟨592965, by rfl⟩ : syracuseStep 1581241 = 1185931) B1185931
theorem B1056955 : Blo 936583 1056955 := bstep (se 1 (by rfl) ⟨792716, by rfl⟩ : syracuseStep 1056955 = 1585433) B1585433
theorem B1188103 : Blo 936583 1188103 := bstep (se 1 (by rfl) ⟨891077, by rfl⟩ : syracuseStep 1188103 = 1782155) B1782155
theorem B8003873 : Blo 936583 8003873 := bstep (se 2 (by rfl) ⟨3001452, by rfl⟩ : syracuseStep 8003873 = 6002905) B6002905
theorem B5710139 : Blo 936583 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B2531699 : Blo 936583 2531699 := bstep (se 1 (by rfl) ⟨1898774, by rfl⟩ : syracuseStep 2531699 = 3797549) B3797549
theorem B6005137 : Blo 936583 6005137 := bstep (se 2 (by rfl) ⟨2251926, by rfl⟩ : syracuseStep 6005137 = 4503853) B4503853
theorem B3383699 : Blo 936583 3383699 := bstep (se 1 (by rfl) ⟨2537774, by rfl⟩ : syracuseStep 3383699 = 5075549) B5075549
theorem B1057423 : Blo 936583 1057423 := bstep (se 1 (by rfl) ⟨793067, by rfl⟩ : syracuseStep 1057423 = 1586135) B1586135
theorem B1188523 : Blo 936583 1188523 := bstep (se 1 (by rfl) ⟨891392, by rfl⟩ : syracuseStep 1188523 = 1782785) B1782785
theorem B30483125 : Blo 936583 30483125 := bstep (se 5 (by rfl) ⟨1428896, by rfl⟩ : syracuseStep 30483125 = 2857793) B2857793
theorem B9642725 : Blo 936583 9642725 := bstep (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) B1808011
theorem B1581943 : Blo 936583 1581943 := bstep (se 1 (by rfl) ⟨1186457, by rfl⟩ : syracuseStep 1581943 = 2372915) B2372915
theorem B1188751 : Blo 936583 1188751 := bstep (se 1 (by rfl) ⟨891563, by rfl⟩ : syracuseStep 1188751 = 1783127) B1783127
theorem B1582139 : Blo 936583 1582139 := bstep (se 1 (by rfl) ⟨1186604, by rfl⟩ : syracuseStep 1582139 = 2373209) B2373209
theorem B4006979 : Blo 936583 4006979 := bstep (se 1 (by rfl) ⟨3005234, by rfl⟩ : syracuseStep 4006979 = 6010469) B6010469
theorem B5710915 : Blo 936583 5710915 := bstep (se 1 (by rfl) ⟨4283186, by rfl⟩ : syracuseStep 5710915 = 8566373) B8566373
theorem B1057927 : Blo 936583 1057927 := bstep (se 1 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 1057927 = 1586891) B1586891
theorem B4826305 : Blo 936583 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B1058107 : Blo 936583 1058107 := bstep (se 1 (by rfl) ⟨793580, by rfl⟩ : syracuseStep 1058107 = 1587161) B1587161
theorem B1779079 : Blo 936583 1779079 := bstep (se 1 (by rfl) ⟨1334309, by rfl⟩ : syracuseStep 1779079 = 2668619) B2668619
theorem B4007303 : Blo 936583 4007303 := bstep (se 1 (by rfl) ⟨3005477, by rfl⟩ : syracuseStep 4007303 = 6010955) B6010955
theorem B21702023 : Blo 936583 21702023 := bstep (se 1 (by rfl) ⟨16276517, by rfl⟩ : syracuseStep 21702023 = 32553035) B32553035
theorem B4761017 : Blo 936583 4761017 := bstep (se 2 (by rfl) ⟨1785381, by rfl⟩ : syracuseStep 4761017 = 3570763) B3570763
theorem B1582537 : Blo 936583 1582537 := bstep (se 2 (by rfl) ⟨593451, by rfl⟩ : syracuseStep 1582537 = 1186903) B1186903
theorem B1189495 : Blo 936583 1189495 := bstep (se 1 (by rfl) ⟨892121, by rfl⟩ : syracuseStep 1189495 = 1784243) B1784243
theorem B10823345 : Blo 936583 10823345 := bstep (se 2 (by rfl) ⟨4058754, by rfl⟩ : syracuseStep 10823345 = 8117509) B8117509
theorem B1779641 : Blo 936583 1779641 := bstep (se 2 (by rfl) ⟨667365, by rfl⟩ : syracuseStep 1779641 = 1334731) B1334731
theorem B1189819 : Blo 936583 1189819 := bstep (se 1 (by rfl) ⟨892364, by rfl⟩ : syracuseStep 1189819 = 1784729) B1784729
theorem B5351453 : Blo 936583 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B2107511 : Blo 936583 2107511 := bstep (se 1 (by rfl) ⟨1580633, by rfl⟩ : syracuseStep 2107511 = 3161267) B3161267
theorem B1583239 : Blo 936583 1583239 := bstep (se 1 (by rfl) ⟨1187429, by rfl⟩ : syracuseStep 1583239 = 2374859) B2374859
theorem B2107691 : Blo 936583 2107691 := bstep (se 1 (by rfl) ⟨1580768, by rfl⟩ : syracuseStep 2107691 = 3161537) B3161537
theorem B1190315 : Blo 936583 1190315 := bstep (se 1 (by rfl) ⟨892736, by rfl⟩ : syracuseStep 1190315 = 1785473) B1785473
theorem B5417401 : Blo 936583 5417401 := bstep (se 2 (by rfl) ⟨2031525, by rfl⟩ : syracuseStep 5417401 = 4063051) B4063051
theorem B2108051 : Blo 936583 2108051 := bstep (se 1 (by rfl) ⟨1581038, by rfl⟩ : syracuseStep 2108051 = 3162077) B3162077
theorem B2108105 : Blo 936583 2108105 := bstep (se 2 (by rfl) ⟨790539, by rfl⟩ : syracuseStep 2108105 = 1581079) B1581079
theorem B1583887 : Blo 936583 1583887 := bstep (se 1 (by rfl) ⟨1187915, by rfl⟩ : syracuseStep 1583887 = 2375831) B2375831
theorem B1780795 : Blo 936583 1780795 := bstep (se 1 (by rfl) ⟨1335596, by rfl⟩ : syracuseStep 1780795 = 2671193) B2671193
theorem B1584427 : Blo 936583 1584427 := bstep (se 1 (by rfl) ⟨1188320, by rfl⟩ : syracuseStep 1584427 = 2376641) B2376641
theorem B2108807 : Blo 936583 2108807 := bstep (se 1 (by rfl) ⟨1581605, by rfl⟩ : syracuseStep 2108807 = 3163211) B3163211
theorem B3812761 : Blo 936583 3812761 := bstep (se 2 (by rfl) ⟨1429785, by rfl⟩ : syracuseStep 3812761 = 2859571) B2859571
theorem B1584569 : Blo 936583 1584569 := bstep (se 2 (by rfl) ⟨594213, by rfl⟩ : syracuseStep 1584569 = 1188427) B1188427
theorem B1781281 : Blo 936583 1781281 := bstep (se 2 (by rfl) ⟨667980, by rfl⟩ : syracuseStep 1781281 = 1335961) B1335961
theorem B2108987 : Blo 936583 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B4009591 : Blo 936583 4009591 := bstep (se 1 (by rfl) ⟨3007193, by rfl⟩ : syracuseStep 4009591 = 6014387) B6014387
theorem B2109113 : Blo 936583 2109113 := bstep (se 2 (by rfl) ⟨790917, by rfl⟩ : syracuseStep 2109113 = 1581835) B1581835
theorem B36581165 : Blo 936583 36581165 := bstep (se 3 (by rfl) ⟨6858968, by rfl⟩ : syracuseStep 36581165 = 13717937) B13717937
theorem B2404367 : Blo 936583 2404367 := bstep (se 1 (by rfl) ⟨1803275, by rfl⟩ : syracuseStep 2404367 = 3606551) B3606551
theorem B2109455 : Blo 936583 2109455 := bstep (se 1 (by rfl) ⟨1582091, by rfl⟩ : syracuseStep 2109455 = 3164183) B3164183
theorem B2109473 : Blo 936583 2109473 := bstep (se 2 (by rfl) ⟨791052, by rfl⟩ : syracuseStep 2109473 = 1582105) B1582105
theorem B4501565 : Blo 936583 4501565 := bstep (se 3 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 4501565 = 1688087) B1688087
theorem B1585271 : Blo 936583 1585271 := bstep (se 1 (by rfl) ⟨1188953, by rfl⟩ : syracuseStep 1585271 = 2377907) B2377907
theorem B8138989 : Blo 936583 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B12824821 : Blo 936583 12824821 := bstep (se 5 (by rfl) ⟨601163, by rfl⟩ : syracuseStep 12824821 = 1202327) B1202327
theorem B3387707 : Blo 936583 3387707 := bstep (se 1 (by rfl) ⟨2540780, by rfl⟩ : syracuseStep 3387707 = 5081561) B5081561
theorem B2109815 : Blo 936583 2109815 := bstep (se 1 (by rfl) ⟨1582361, by rfl⟩ : syracuseStep 2109815 = 3164723) B3164723
theorem B1126775 : Blo 936583 1126775 := bstep (se 1 (by rfl) ⟨845081, by rfl⟩ : syracuseStep 1126775 = 1690163) B1690163
theorem B5353937 : Blo 936583 5353937 := bstep (se 2 (by rfl) ⟨2007726, by rfl⟩ : syracuseStep 5353937 = 4015453) B4015453
theorem B2109995 : Blo 936583 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B1585723 : Blo 936583 1585723 := bstep (se 1 (by rfl) ⟨1189292, by rfl⟩ : syracuseStep 1585723 = 2378585) B2378585
theorem B2667127 : Blo 936583 2667127 := bstep (se 1 (by rfl) ⟨2000345, by rfl⟩ : syracuseStep 2667127 = 4000691) B4000691
theorem B2667161 : Blo 936583 2667161 := bstep (se 2 (by rfl) ⟨1000185, by rfl⟩ : syracuseStep 2667161 = 2000371) B2000371
theorem B1127083 : Blo 936583 1127083 := bstep (se 1 (by rfl) ⟨845312, by rfl⟩ : syracuseStep 1127083 = 1690625) B1690625
theorem B1585865 : Blo 936583 1585865 := bstep (se 2 (by rfl) ⟨594699, by rfl⟩ : syracuseStep 1585865 = 1189399) B1189399
theorem B2667275 : Blo 936583 2667275 := bstep (se 1 (by rfl) ⟨2000456, by rfl⟩ : syracuseStep 2667275 = 4000913) B4000913
theorem B1782587 : Blo 936583 1782587 := bstep (se 1 (by rfl) ⟨1336940, by rfl⟩ : syracuseStep 1782587 = 2673881) B2673881
theorem B2110355 : Blo 936583 2110355 := bstep (se 1 (by rfl) ⟨1582766, by rfl⟩ : syracuseStep 2110355 = 3165533) B3165533
theorem B3388313 : Blo 936583 3388313 := bstep (se 2 (by rfl) ⟨1270617, by rfl⟩ : syracuseStep 3388313 = 2541235) B2541235
theorem B2110409 : Blo 936583 2110409 := bstep (se 2 (by rfl) ⟨791403, by rfl⟩ : syracuseStep 2110409 = 1582807) B1582807
theorem B12170245 : Blo 936583 12170245 := bstep (se 4 (by rfl) ⟨1140960, by rfl⟩ : syracuseStep 12170245 = 2281921) B2281921
theorem B4011095 : Blo 936583 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B2372723 : Blo 936583 2372723 := bstep (se 1 (by rfl) ⟨1779542, by rfl⟩ : syracuseStep 2372723 = 3559085) B3559085
theorem B2536715 : Blo 936583 2536715 := bstep (se 1 (by rfl) ⟨1902536, by rfl⟩ : syracuseStep 2536715 = 3805073) B3805073
theorem B1783073 : Blo 936583 1783073 := bstep (se 2 (by rfl) ⟨668652, by rfl⟩ : syracuseStep 1783073 = 1337305) B1337305
theorem B1586567 : Blo 936583 1586567 := bstep (se 1 (by rfl) ⟨1189925, by rfl⟩ : syracuseStep 1586567 = 2379851) B2379851
theorem B1783225 : Blo 936583 1783225 := bstep (se 2 (by rfl) ⟨668709, by rfl⟩ : syracuseStep 1783225 = 1337419) B1337419
theorem B8238635 : Blo 936583 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B2373239 : Blo 936583 2373239 := bstep (se 1 (by rfl) ⟨1779929, by rfl⟩ : syracuseStep 2373239 = 3559859) B3559859
theorem B2111111 : Blo 936583 2111111 := bstep (se 1 (by rfl) ⟨1583333, by rfl⟩ : syracuseStep 2111111 = 3166667) B3166667
theorem B2111291 : Blo 936583 2111291 := bstep (se 1 (by rfl) ⟨1583468, by rfl⟩ : syracuseStep 2111291 = 3166937) B3166937
theorem B2668403 : Blo 936583 2668403 := bstep (se 1 (by rfl) ⟨2001302, by rfl⟩ : syracuseStep 2668403 = 4002605) B4002605
theorem B11417507 : Blo 936583 11417507 := bstep (se 1 (by rfl) ⟨8563130, by rfl⟩ : syracuseStep 11417507 = 17126261) B17126261
theorem B2111417 : Blo 936583 2111417 := bstep (se 2 (by rfl) ⟨791781, by rfl⟩ : syracuseStep 2111417 = 1583563) B1583563
theorem B1587215 : Blo 936583 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B2668801 : Blo 936583 2668801 := bstep (se 2 (by rfl) ⟨1000800, by rfl⟩ : syracuseStep 2668801 = 2001601) B2001601
theorem B2111759 : Blo 936583 2111759 := bstep (se 1 (by rfl) ⟨1583819, by rfl⟩ : syracuseStep 2111759 = 3167639) B3167639
theorem B2111777 : Blo 936583 2111777 := bstep (se 2 (by rfl) ⟨791916, by rfl⟩ : syracuseStep 2111777 = 1583833) B1583833
theorem B5355827 : Blo 936583 5355827 := bstep (se 1 (by rfl) ⟨4016870, by rfl⟩ : syracuseStep 5355827 = 8033741) B8033741
theorem B2668859 : Blo 936583 2668859 := bstep (se 1 (by rfl) ⟨2001644, by rfl⟩ : syracuseStep 2668859 = 4003289) B4003289
theorem B2374231 : Blo 936583 2374231 := bstep (se 1 (by rfl) ⟨1780673, by rfl⟩ : syracuseStep 2374231 = 3561347) B3561347
theorem B2112119 : Blo 936583 2112119 := bstep (se 1 (by rfl) ⟨1584089, by rfl⟩ : syracuseStep 2112119 = 3168179) B3168179
theorem B2112299 : Blo 936583 2112299 := bstep (se 1 (by rfl) ⟨1584224, by rfl⟩ : syracuseStep 2112299 = 3168449) B3168449
theorem B12041075 : Blo 936583 12041075 := bstep (se 1 (by rfl) ⟨9030806, by rfl⟩ : syracuseStep 12041075 = 18061613) B18061613
theorem B2374535 : Blo 936583 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B1129351 : Blo 936583 1129351 := bstep (se 1 (by rfl) ⟨847013, by rfl⟩ : syracuseStep 1129351 = 1694027) B1694027
theorem B4013009 : Blo 936583 4013009 := bstep (se 2 (by rfl) ⟨1504878, by rfl⟩ : syracuseStep 4013009 = 3009757) B3009757
theorem B2374667 : Blo 936583 2374667 := bstep (se 1 (by rfl) ⟨1781000, by rfl⟩ : syracuseStep 2374667 = 3562001) B3562001
theorem B6011927 : Blo 936583 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B9616445 : Blo 936583 9616445 := bstep (se 3 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 9616445 = 3606167) B3606167
theorem B2112659 : Blo 936583 2112659 := bstep (se 1 (by rfl) ⟨1584494, by rfl⟩ : syracuseStep 2112659 = 3168989) B3168989
theorem B1785017 : Blo 936583 1785017 := bstep (se 2 (by rfl) ⟨669381, by rfl⟩ : syracuseStep 1785017 = 1338763) B1338763
theorem B7126217 : Blo 936583 7126217 := bstep (se 2 (by rfl) ⟨2672331, by rfl⟩ : syracuseStep 7126217 = 5344663) B5344663
theorem B2112713 : Blo 936583 2112713 := bstep (se 2 (by rfl) ⟨792267, by rfl⟩ : syracuseStep 2112713 = 1584535) B1584535
theorem B2375183 : Blo 936583 2375183 := bstep (se 1 (by rfl) ⟨1781387, by rfl⟩ : syracuseStep 2375183 = 3562775) B3562775
theorem B2375315 : Blo 936583 2375315 := bstep (se 1 (by rfl) ⟨1781486, by rfl⟩ : syracuseStep 2375315 = 3562973) B3562973
theorem B3161915 : Blo 936583 3161915 := bstep (se 1 (by rfl) ⟨2371436, by rfl⟩ : syracuseStep 3161915 = 4742873) B4742873
theorem B2113415 : Blo 936583 2113415 := bstep (se 1 (by rfl) ⟨1585061, by rfl⟩ : syracuseStep 2113415 = 3170123) B3170123
theorem B3719047 : Blo 936583 3719047 := bstep (se 1 (by rfl) ⟨2789285, by rfl⟩ : syracuseStep 3719047 = 5578571) B5578571
theorem B2408393 : Blo 936583 2408393 := bstep (se 2 (by rfl) ⟨903147, by rfl⟩ : syracuseStep 2408393 = 1806295) B1806295
theorem B2113595 : Blo 936583 2113595 := bstep (se 1 (by rfl) ⟨1585196, by rfl⟩ : syracuseStep 2113595 = 3170393) B3170393
theorem B2113721 : Blo 936583 2113721 := bstep (se 2 (by rfl) ⟨792645, by rfl⟩ : syracuseStep 2113721 = 1585291) B1585291
theorem B5488877 : Blo 936583 5488877 := bstep (se 3 (by rfl) ⟨1029164, by rfl⟩ : syracuseStep 5488877 = 2058329) B2058329
theorem B3162401 : Blo 936583 3162401 := bstep (se 2 (by rfl) ⟨1185900, by rfl⟩ : syracuseStep 3162401 = 2371801) B2371801
theorem B9617795 : Blo 936583 9617795 := bstep (se 1 (by rfl) ⟨7213346, by rfl⟩ : syracuseStep 9617795 = 14426693) B14426693
theorem B1687943 : Blo 936583 1687943 := bstep (se 1 (by rfl) ⟨1265957, by rfl⟩ : syracuseStep 1687943 = 2531915) B2531915
theorem B2114063 : Blo 936583 2114063 := bstep (se 1 (by rfl) ⟨1585547, by rfl⟩ : syracuseStep 2114063 = 3171095) B3171095
theorem B2114081 : Blo 936583 2114081 := bstep (se 2 (by rfl) ⟨792780, by rfl⟩ : syracuseStep 2114081 = 1585561) B1585561
theorem B2671147 : Blo 936583 2671147 := bstep (se 1 (by rfl) ⟨2003360, by rfl⟩ : syracuseStep 2671147 = 4006721) B4006721
theorem B6767171 : Blo 936583 6767171 := bstep (se 1 (by rfl) ⟨5075378, by rfl⟩ : syracuseStep 6767171 = 10150757) B10150757
theorem B5718701 : Blo 936583 5718701 := bstep (se 3 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 5718701 = 2144513) B2144513
theorem B9126593 : Blo 936583 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B2376449 : Blo 936583 2376449 := bstep (se 2 (by rfl) ⟨891168, by rfl⟩ : syracuseStep 2376449 = 1782337) B1782337
theorem B2671375 : Blo 936583 2671375 := bstep (se 1 (by rfl) ⟨2003531, by rfl⟩ : syracuseStep 2671375 = 4007063) B4007063
theorem B3162995 : Blo 936583 3162995 := bstep (se 1 (by rfl) ⟨2372246, by rfl⟩ : syracuseStep 3162995 = 4744493) B4744493
theorem B2114423 : Blo 936583 2114423 := bstep (se 1 (by rfl) ⟨1585817, by rfl⟩ : syracuseStep 2114423 = 3171635) B3171635
theorem B2671649 : Blo 936583 2671649 := bstep (se 2 (by rfl) ⟨1001868, by rfl⟩ : syracuseStep 2671649 = 2003737) B2003737
theorem B2114603 : Blo 936583 2114603 := bstep (se 1 (by rfl) ⟨1585952, by rfl⟩ : syracuseStep 2114603 = 3171905) B3171905
theorem B1688635 : Blo 936583 1688635 := bstep (se 1 (by rfl) ⟨1266476, by rfl⟩ : syracuseStep 1688635 = 2532953) B2532953
theorem B2376823 : Blo 936583 2376823 := bstep (se 1 (by rfl) ⟨1782617, by rfl⟩ : syracuseStep 2376823 = 3565235) B3565235
theorem B2671991 : Blo 936583 2671991 := bstep (se 1 (by rfl) ⟨2003993, by rfl⟩ : syracuseStep 2671991 = 4007987) B4007987
theorem B200263043 : Blo 936583 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B2114963 : Blo 936583 2114963 := bstep (se 1 (by rfl) ⟨1586222, by rfl⟩ : syracuseStep 2114963 = 3172445) B3172445
theorem B2115017 : Blo 936583 2115017 := bstep (se 2 (by rfl) ⟨793131, by rfl⟩ : syracuseStep 2115017 = 1586263) B1586263
theorem B2377259 : Blo 936583 2377259 := bstep (se 1 (by rfl) ⟨1782944, by rfl⟩ : syracuseStep 2377259 = 3565889) B3565889
theorem B2541257 : Blo 936583 2541257 := bstep (se 2 (by rfl) ⟨952971, by rfl⟩ : syracuseStep 2541257 = 1905943) B1905943
theorem B2672651 : Blo 936583 2672651 := bstep (se 1 (by rfl) ⟨2004488, by rfl⟩ : syracuseStep 2672651 = 4008977) B4008977
theorem B2115719 : Blo 936583 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B5720257 : Blo 936583 5720257 := bstep (se 2 (by rfl) ⟨2145096, by rfl⟩ : syracuseStep 5720257 = 4290193) B4290193
theorem B2115899 : Blo 936583 2115899 := bstep (se 1 (by rfl) ⟨1586924, by rfl⟩ : syracuseStep 2115899 = 3173849) B3173849
theorem B2378099 : Blo 936583 2378099 := bstep (se 1 (by rfl) ⟨1783574, by rfl⟩ : syracuseStep 2378099 = 3567149) B3567149
theorem B2378119 : Blo 936583 2378119 := bstep (se 1 (by rfl) ⟨1783589, by rfl⟩ : syracuseStep 2378119 = 3567179) B3567179
theorem B2116025 : Blo 936583 2116025 := bstep (se 2 (by rfl) ⟨793509, by rfl⟩ : syracuseStep 2116025 = 1587019) B1587019
theorem B4278851 : Blo 936583 4278851 := bstep (se 1 (by rfl) ⟨3209138, by rfl⟩ : syracuseStep 4278851 = 6418277) B6418277
theorem B936583 : Blo 936583 936583 := bstep (se 1 (by rfl) ⟨702437, by rfl⟩ : syracuseStep 936583 = 1404875) B1404875
theorem B936591 : Blo 936583 936591 := bstep (se 1 (by rfl) ⟨702443, by rfl⟩ : syracuseStep 936591 = 1404887) B1404887
theorem B2378393 : Blo 936583 2378393 := bstep (se 2 (by rfl) ⟨891897, by rfl⟩ : syracuseStep 2378393 = 1783795) B1783795
theorem B936635 : Blo 936583 936635 := bstep (se 1 (by rfl) ⟨702476, by rfl⟩ : syracuseStep 936635 = 1404953) B1404953
theorem B936711 : Blo 936583 936711 := bstep (se 1 (by rfl) ⟨702533, by rfl⟩ : syracuseStep 936711 = 1405067) B1405067
theorem B936719 : Blo 936583 936719 := bstep (se 1 (by rfl) ⟨702539, by rfl⟩ : syracuseStep 936719 = 1405079) B1405079
theorem B936763 : Blo 936583 936763 := bstep (se 1 (by rfl) ⟨702572, by rfl⟩ : syracuseStep 936763 = 1405145) B1405145
theorem B2378555 : Blo 936583 2378555 := bstep (se 1 (by rfl) ⟨1783916, by rfl⟩ : syracuseStep 2378555 = 3567833) B3567833
theorem B936839 : Blo 936583 936839 := bstep (se 1 (by rfl) ⟨702629, by rfl⟩ : syracuseStep 936839 = 1405259) B1405259
theorem B936847 : Blo 936583 936847 := bstep (se 1 (by rfl) ⟨702635, by rfl⟩ : syracuseStep 936847 = 1405271) B1405271
theorem B4508561 : Blo 936583 4508561 := bstep (se 2 (by rfl) ⟨1690710, by rfl⟩ : syracuseStep 4508561 = 3381421) B3381421
theorem B10701719 : Blo 936583 10701719 := bstep (se 1 (by rfl) ⟨8026289, by rfl⟩ : syracuseStep 10701719 = 16052579) B16052579
theorem B936891 : Blo 936583 936891 := bstep (se 1 (by rfl) ⟨702668, by rfl⟩ : syracuseStep 936891 = 1405337) B1405337
theorem B936967 : Blo 936583 936967 := bstep (se 1 (by rfl) ⟨702725, by rfl⟩ : syracuseStep 936967 = 1405451) B1405451
theorem B936975 : Blo 936583 936975 := bstep (se 1 (by rfl) ⟨702731, by rfl⟩ : syracuseStep 936975 = 1405463) B1405463
theorem B2378767 : Blo 936583 2378767 := bstep (se 1 (by rfl) ⟨1784075, by rfl⟩ : syracuseStep 2378767 = 3568151) B3568151
theorem B937019 : Blo 936583 937019 := bstep (se 1 (by rfl) ⟨702764, by rfl⟩ : syracuseStep 937019 = 1405529) B1405529
theorem B937095 : Blo 936583 937095 := bstep (se 1 (by rfl) ⟨702821, by rfl⟩ : syracuseStep 937095 = 1405643) B1405643
theorem B937103 : Blo 936583 937103 := bstep (se 1 (by rfl) ⟨702827, by rfl⟩ : syracuseStep 937103 = 1405655) B1405655
theorem B2444435 : Blo 936583 2444435 := bstep (se 1 (by rfl) ⟨1833326, by rfl⟩ : syracuseStep 2444435 = 3666653) B3666653
theorem B937147 : Blo 936583 937147 := bstep (se 1 (by rfl) ⟨702860, by rfl⟩ : syracuseStep 937147 = 1405721) B1405721
theorem B937223 : Blo 936583 937223 := bstep (se 1 (by rfl) ⟨702917, by rfl⟩ : syracuseStep 937223 = 1405835) B1405835
theorem B937231 : Blo 936583 937231 := bstep (se 1 (by rfl) ⟨702923, by rfl⟩ : syracuseStep 937231 = 1405847) B1405847
theorem B1428751 : Blo 936583 1428751 := bstep (se 1 (by rfl) ⟨1071563, by rfl⟩ : syracuseStep 1428751 = 2143127) B2143127
theorem B2379041 : Blo 936583 2379041 := bstep (se 2 (by rfl) ⟨892140, by rfl⟩ : syracuseStep 2379041 = 1784281) B1784281
theorem B937275 : Blo 936583 937275 := bstep (se 1 (by rfl) ⟨702956, by rfl⟩ : syracuseStep 937275 = 1405913) B1405913
theorem B937351 : Blo 936583 937351 := bstep (se 1 (by rfl) ⟨703013, by rfl⟩ : syracuseStep 937351 = 1406027) B1406027
theorem B937359 : Blo 936583 937359 := bstep (se 1 (by rfl) ⟨703019, by rfl⟩ : syracuseStep 937359 = 1406039) B1406039
theorem B3165587 : Blo 936583 3165587 := bstep (se 1 (by rfl) ⟨2374190, by rfl⟩ : syracuseStep 3165587 = 4748381) B4748381
theorem B13553081 : Blo 936583 13553081 := bstep (se 2 (by rfl) ⟨5082405, by rfl⟩ : syracuseStep 13553081 = 10164811) B10164811
theorem B937403 : Blo 936583 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B937479 : Blo 936583 937479 := bstep (se 1 (by rfl) ⟨703109, by rfl⟩ : syracuseStep 937479 = 1406219) B1406219
theorem B937487 : Blo 936583 937487 := bstep (se 1 (by rfl) ⟨703115, by rfl⟩ : syracuseStep 937487 = 1406231) B1406231
theorem B937531 : Blo 936583 937531 := bstep (se 1 (by rfl) ⟨703148, by rfl⟩ : syracuseStep 937531 = 1406297) B1406297
theorem B2674235 : Blo 936583 2674235 := bstep (se 1 (by rfl) ⟨2005676, by rfl⟩ : syracuseStep 2674235 = 4011353) B4011353
theorem B2674291 : Blo 936583 2674291 := bstep (se 1 (by rfl) ⟨2005718, by rfl⟩ : syracuseStep 2674291 = 4011437) B4011437
theorem B937607 : Blo 936583 937607 := bstep (se 1 (by rfl) ⟨703205, by rfl⟩ : syracuseStep 937607 = 1406411) B1406411
theorem B937615 : Blo 936583 937615 := bstep (se 1 (by rfl) ⟨703211, by rfl⟩ : syracuseStep 937615 = 1406423) B1406423
theorem B937659 : Blo 936583 937659 := bstep (se 1 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 937659 = 1406489) B1406489
theorem B937735 : Blo 936583 937735 := bstep (se 1 (by rfl) ⟨703301, by rfl⟩ : syracuseStep 937735 = 1406603) B1406603
theorem B937743 : Blo 936583 937743 := bstep (se 1 (by rfl) ⟨703307, by rfl⟩ : syracuseStep 937743 = 1406615) B1406615
theorem B937787 : Blo 936583 937787 := bstep (se 1 (by rfl) ⟨703340, by rfl⟩ : syracuseStep 937787 = 1406681) B1406681
theorem B937863 : Blo 936583 937863 := bstep (se 1 (by rfl) ⟨703397, by rfl⟩ : syracuseStep 937863 = 1406795) B1406795
theorem B937871 : Blo 936583 937871 := bstep (se 1 (by rfl) ⟨703403, by rfl⟩ : syracuseStep 937871 = 1406807) B1406807
theorem B937915 : Blo 936583 937915 := bstep (se 1 (by rfl) ⟨703436, by rfl⟩ : syracuseStep 937915 = 1406873) B1406873
theorem B2674633 : Blo 936583 2674633 := bstep (se 2 (by rfl) ⟨1002987, by rfl⟩ : syracuseStep 2674633 = 2005975) B2005975
theorem B937991 : Blo 936583 937991 := bstep (se 1 (by rfl) ⟨703493, by rfl⟩ : syracuseStep 937991 = 1406987) B1406987
theorem B937999 : Blo 936583 937999 := bstep (se 1 (by rfl) ⟨703499, by rfl⟩ : syracuseStep 937999 = 1406999) B1406999
theorem B938043 : Blo 936583 938043 := bstep (se 1 (by rfl) ⟨703532, by rfl⟩ : syracuseStep 938043 = 1407065) B1407065
theorem B938119 : Blo 936583 938119 := bstep (se 1 (by rfl) ⟨703589, by rfl⟩ : syracuseStep 938119 = 1407179) B1407179
theorem B938127 : Blo 936583 938127 := bstep (se 1 (by rfl) ⟨703595, by rfl⟩ : syracuseStep 938127 = 1407191) B1407191
theorem B6770861 : Blo 936583 6770861 := bstep (se 3 (by rfl) ⟨1269536, by rfl⟩ : syracuseStep 6770861 = 2539073) B2539073
theorem B938171 : Blo 936583 938171 := bstep (se 1 (by rfl) ⟨703628, by rfl⟩ : syracuseStep 938171 = 1407257) B1407257
theorem B5066945 : Blo 936583 5066945 := bstep (se 2 (by rfl) ⟨1900104, by rfl⟩ : syracuseStep 5066945 = 3800209) B3800209
theorem B7622857 : Blo 936583 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B938247 : Blo 936583 938247 := bstep (se 1 (by rfl) ⟨703685, by rfl⟩ : syracuseStep 938247 = 1407371) B1407371
theorem B2380043 : Blo 936583 2380043 := bstep (se 1 (by rfl) ⟨1785032, by rfl⟩ : syracuseStep 2380043 = 3570065) B3570065
theorem B938255 : Blo 936583 938255 := bstep (se 1 (by rfl) ⟨703691, by rfl⟩ : syracuseStep 938255 = 1407383) B1407383
theorem B3002683 : Blo 936583 3002683 := bstep (se 1 (by rfl) ⟨2252012, by rfl⟩ : syracuseStep 3002683 = 4504025) B4504025
theorem B938299 : Blo 936583 938299 := bstep (se 1 (by rfl) ⟨703724, by rfl⟩ : syracuseStep 938299 = 1407449) B1407449
theorem B938375 : Blo 936583 938375 := bstep (se 1 (by rfl) ⟨703781, by rfl⟩ : syracuseStep 938375 = 1407563) B1407563
theorem B938383 : Blo 936583 938383 := bstep (se 1 (by rfl) ⟨703787, by rfl⟩ : syracuseStep 938383 = 1407575) B1407575
theorem B6771089 : Blo 936583 6771089 := bstep (se 2 (by rfl) ⟨2539158, by rfl⟩ : syracuseStep 6771089 = 5078317) B5078317
theorem B938427 : Blo 936583 938427 := bstep (se 1 (by rfl) ⟨703820, by rfl⟩ : syracuseStep 938427 = 1407641) B1407641
theorem B3559889 : Blo 936583 3559889 := bstep (se 2 (by rfl) ⟨1334958, by rfl⟩ : syracuseStep 3559889 = 2669917) B2669917
theorem B938503 : Blo 936583 938503 := bstep (se 1 (by rfl) ⟨703877, by rfl⟩ : syracuseStep 938503 = 1407755) B1407755
theorem B938511 : Blo 936583 938511 := bstep (se 1 (by rfl) ⟨703883, by rfl⟩ : syracuseStep 938511 = 1407767) B1407767
theorem B938555 : Blo 936583 938555 := bstep (se 1 (by rfl) ⟨703916, by rfl⟩ : syracuseStep 938555 = 1407833) B1407833
theorem B938631 : Blo 936583 938631 := bstep (se 1 (by rfl) ⟨703973, by rfl⟩ : syracuseStep 938631 = 1407947) B1407947
theorem B938639 : Blo 936583 938639 := bstep (se 1 (by rfl) ⟨703979, by rfl⟩ : syracuseStep 938639 = 1407959) B1407959
theorem B938683 : Blo 936583 938683 := bstep (se 1 (by rfl) ⟨704012, by rfl⟩ : syracuseStep 938683 = 1408025) B1408025
theorem B938759 : Blo 936583 938759 := bstep (se 1 (by rfl) ⟨704069, by rfl⟩ : syracuseStep 938759 = 1408139) B1408139
theorem B2708239 : Blo 936583 2708239 := bstep (se 1 (by rfl) ⟨2031179, by rfl⟩ : syracuseStep 2708239 = 4062359) B4062359
theorem B3166991 : Blo 936583 3166991 := bstep (se 1 (by rfl) ⟨2375243, by rfl⟩ : syracuseStep 3166991 = 4750487) B4750487
theorem B938767 : Blo 936583 938767 := bstep (se 1 (by rfl) ⟨704075, by rfl⟩ : syracuseStep 938767 = 1408151) B1408151
theorem B34689829 : Blo 936583 34689829 := bstep (se 4 (by rfl) ⟨3252171, by rfl⟩ : syracuseStep 34689829 = 6504343) B6504343
theorem B938811 : Blo 936583 938811 := bstep (se 1 (by rfl) ⟨704108, by rfl⟩ : syracuseStep 938811 = 1408217) B1408217
theorem B938887 : Blo 936583 938887 := bstep (se 1 (by rfl) ⟨704165, by rfl⟩ : syracuseStep 938887 = 1408331) B1408331
theorem B938895 : Blo 936583 938895 := bstep (se 1 (by rfl) ⟨704171, by rfl⟩ : syracuseStep 938895 = 1408343) B1408343
theorem B2380691 : Blo 936583 2380691 := bstep (se 1 (by rfl) ⟨1785518, by rfl⟩ : syracuseStep 2380691 = 3571037) B3571037
theorem B3560345 : Blo 936583 3560345 := bstep (se 2 (by rfl) ⟨1335129, by rfl⟩ : syracuseStep 3560345 = 2670259) B2670259
theorem B13915061 : Blo 936583 13915061 := bstep (se 5 (by rfl) ⟨652268, by rfl⟩ : syracuseStep 13915061 = 1304537) B1304537
theorem B938939 : Blo 936583 938939 := bstep (se 1 (by rfl) ⟨704204, by rfl⟩ : syracuseStep 938939 = 1408409) B1408409
theorem B939015 : Blo 936583 939015 := bstep (se 1 (by rfl) ⟨704261, by rfl⟩ : syracuseStep 939015 = 1408523) B1408523
theorem B939023 : Blo 936583 939023 := bstep (se 1 (by rfl) ⟨704267, by rfl⟩ : syracuseStep 939023 = 1408535) B1408535
theorem B3167261 : Blo 936583 3167261 := bstep (se 3 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 3167261 = 1187723) B1187723
theorem B1627195 : Blo 936583 1627195 := bstep (se 1 (by rfl) ⟨1220396, by rfl⟩ : syracuseStep 1627195 = 2440793) B2440793
theorem B939067 : Blo 936583 939067 := bstep (se 1 (by rfl) ⟨704300, by rfl⟩ : syracuseStep 939067 = 1408601) B1408601
theorem B939143 : Blo 936583 939143 := bstep (se 1 (by rfl) ⟨704357, by rfl⟩ : syracuseStep 939143 = 1408715) B1408715
theorem B939151 : Blo 936583 939151 := bstep (se 1 (by rfl) ⟨704363, by rfl⟩ : syracuseStep 939151 = 1408727) B1408727
theorem B939195 : Blo 936583 939195 := bstep (se 1 (by rfl) ⟨704396, by rfl⟩ : syracuseStep 939195 = 1408793) B1408793
theorem B939271 : Blo 936583 939271 := bstep (se 1 (by rfl) ⟨704453, by rfl⟩ : syracuseStep 939271 = 1408907) B1408907
theorem B939279 : Blo 936583 939279 := bstep (se 1 (by rfl) ⟨704459, by rfl⟩ : syracuseStep 939279 = 1408919) B1408919
theorem B939323 : Blo 936583 939323 := bstep (se 1 (by rfl) ⟨704492, by rfl⟩ : syracuseStep 939323 = 1408985) B1408985
theorem B939399 : Blo 936583 939399 := bstep (se 1 (by rfl) ⟨704549, by rfl⟩ : syracuseStep 939399 = 1409099) B1409099
theorem B939407 : Blo 936583 939407 := bstep (se 1 (by rfl) ⟨704555, by rfl⟩ : syracuseStep 939407 = 1409111) B1409111
theorem B939451 : Blo 936583 939451 := bstep (se 1 (by rfl) ⟨704588, by rfl⟩ : syracuseStep 939451 = 1409177) B1409177
theorem B5068241 : Blo 936583 5068241 := bstep (se 2 (by rfl) ⟨1900590, by rfl⟩ : syracuseStep 5068241 = 3801181) B3801181
theorem B939527 : Blo 936583 939527 := bstep (se 1 (by rfl) ⟨704645, by rfl⟩ : syracuseStep 939527 = 1409291) B1409291
theorem B939535 : Blo 936583 939535 := bstep (se 1 (by rfl) ⟨704651, by rfl⟩ : syracuseStep 939535 = 1409303) B1409303
theorem B939579 : Blo 936583 939579 := bstep (se 1 (by rfl) ⟨704684, by rfl⟩ : syracuseStep 939579 = 1409369) B1409369
theorem B939655 : Blo 936583 939655 := bstep (se 1 (by rfl) ⟨704741, by rfl⟩ : syracuseStep 939655 = 1409483) B1409483
theorem B939663 : Blo 936583 939663 := bstep (se 1 (by rfl) ⟨704747, by rfl⟩ : syracuseStep 939663 = 1409495) B1409495
theorem B939707 : Blo 936583 939707 := bstep (se 1 (by rfl) ⟨704780, by rfl⟩ : syracuseStep 939707 = 1409561) B1409561
theorem B939783 : Blo 936583 939783 := bstep (se 1 (by rfl) ⟨704837, by rfl⟩ : syracuseStep 939783 = 1409675) B1409675
theorem B939791 : Blo 936583 939791 := bstep (se 1 (by rfl) ⟨704843, by rfl⟩ : syracuseStep 939791 = 1409687) B1409687
theorem B6772531 : Blo 936583 6772531 := bstep (se 1 (by rfl) ⟨5079398, by rfl⟩ : syracuseStep 6772531 = 10158797) B10158797
theorem B939835 : Blo 936583 939835 := bstep (se 1 (by rfl) ⟨704876, by rfl⟩ : syracuseStep 939835 = 1409753) B1409753
theorem B1267591 : Blo 936583 1267591 := bstep (se 1 (by rfl) ⟨950693, by rfl⟩ : syracuseStep 1267591 = 1901387) B1901387
theorem B939911 : Blo 936583 939911 := bstep (se 1 (by rfl) ⟨704933, by rfl⟩ : syracuseStep 939911 = 1409867) B1409867
theorem B939919 : Blo 936583 939919 := bstep (se 1 (by rfl) ⟨704939, by rfl⟩ : syracuseStep 939919 = 1409879) B1409879
theorem B939963 : Blo 936583 939963 := bstep (se 1 (by rfl) ⟨704972, by rfl⟩ : syracuseStep 939963 = 1409945) B1409945
theorem B940039 : Blo 936583 940039 := bstep (se 1 (by rfl) ⟨705029, by rfl⟩ : syracuseStep 940039 = 1410059) B1410059
theorem B940047 : Blo 936583 940047 := bstep (se 1 (by rfl) ⟨705035, by rfl⟩ : syracuseStep 940047 = 1410071) B1410071
theorem B3561515 : Blo 936583 3561515 := bstep (se 1 (by rfl) ⟨2671136, by rfl⟩ : syracuseStep 3561515 = 5342273) B5342273
theorem B940091 : Blo 936583 940091 := bstep (se 1 (by rfl) ⟨705068, by rfl⟩ : syracuseStep 940091 = 1410137) B1410137
theorem B2676797 : Blo 936583 2676797 := bstep (se 3 (by rfl) ⟨501899, by rfl⟩ : syracuseStep 2676797 = 1003799) B1003799
theorem B940167 : Blo 936583 940167 := bstep (se 1 (by rfl) ⟨705125, by rfl⟩ : syracuseStep 940167 = 1410251) B1410251
theorem B940175 : Blo 936583 940175 := bstep (se 1 (by rfl) ⟨705131, by rfl⟩ : syracuseStep 940175 = 1410263) B1410263
theorem B2250899 : Blo 936583 2250899 := bstep (se 1 (by rfl) ⟨1688174, by rfl⟩ : syracuseStep 2250899 = 3376349) B3376349
theorem B940219 : Blo 936583 940219 := bstep (se 1 (by rfl) ⟨705164, by rfl⟩ : syracuseStep 940219 = 1410329) B1410329
theorem B940295 : Blo 936583 940295 := bstep (se 1 (by rfl) ⟨705221, by rfl⟩ : syracuseStep 940295 = 1410443) B1410443
theorem B940303 : Blo 936583 940303 := bstep (se 1 (by rfl) ⟨705227, by rfl⟩ : syracuseStep 940303 = 1410455) B1410455
theorem B2677025 : Blo 936583 2677025 := bstep (se 2 (by rfl) ⟨1003884, by rfl⟩ : syracuseStep 2677025 = 2007769) B2007769
theorem B940347 : Blo 936583 940347 := bstep (se 1 (by rfl) ⟨705260, by rfl⟩ : syracuseStep 940347 = 1410521) B1410521
theorem B940423 : Blo 936583 940423 := bstep (se 1 (by rfl) ⟨705317, by rfl⟩ : syracuseStep 940423 = 1410635) B1410635
theorem B940431 : Blo 936583 940431 := bstep (se 1 (by rfl) ⟨705323, by rfl⟩ : syracuseStep 940431 = 1410647) B1410647
theorem B3168665 : Blo 936583 3168665 := bstep (se 2 (by rfl) ⟨1188249, by rfl⟩ : syracuseStep 3168665 = 2376499) B2376499
theorem B940475 : Blo 936583 940475 := bstep (se 1 (by rfl) ⟨705356, by rfl⟩ : syracuseStep 940475 = 1410713) B1410713
theorem B1333751 : Blo 936583 1333751 := bstep (se 1 (by rfl) ⟨1000313, by rfl⟩ : syracuseStep 1333751 = 2000627) B2000627
theorem B940551 : Blo 936583 940551 := bstep (se 1 (by rfl) ⟨705413, by rfl⟩ : syracuseStep 940551 = 1410827) B1410827
theorem B940559 : Blo 936583 940559 := bstep (se 1 (by rfl) ⟨705419, by rfl⟩ : syracuseStep 940559 = 1410839) B1410839
theorem B2677367 : Blo 936583 2677367 := bstep (se 1 (by rfl) ⟨2008025, by rfl⟩ : syracuseStep 2677367 = 4016051) B4016051
theorem B1333945 : Blo 936583 1333945 := bstep (se 2 (by rfl) ⟨500229, by rfl⟩ : syracuseStep 1333945 = 1000459) B1000459
theorem B5069627 : Blo 936583 5069627 := bstep (se 1 (by rfl) ⟨3802220, by rfl⟩ : syracuseStep 5069627 = 7604441) B7604441
theorem B2251705 : Blo 936583 2251705 := bstep (se 2 (by rfl) ⟨844389, by rfl⟩ : syracuseStep 2251705 = 1688779) B1688779
theorem B4512829 : Blo 936583 4512829 := bstep (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) B1692311
theorem B3169367 : Blo 936583 3169367 := bstep (se 1 (by rfl) ⟨2377025, by rfl⟩ : syracuseStep 3169367 = 4754051) B4754051
theorem B10706093 : Blo 936583 10706093 := bstep (se 3 (by rfl) ⟨2007392, by rfl⟩ : syracuseStep 10706093 = 4014785) B4014785
theorem B2252033 : Blo 936583 2252033 := bstep (se 2 (by rfl) ⟨844512, by rfl⟩ : syracuseStep 2252033 = 1689025) B1689025
theorem B2284843 : Blo 936583 2284843 := bstep (se 1 (by rfl) ⟨1713632, by rfl⟩ : syracuseStep 2284843 = 3427265) B3427265
theorem B3005849 : Blo 936583 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B11427281 : Blo 936583 11427281 := bstep (se 2 (by rfl) ⟨4285230, by rfl⟩ : syracuseStep 11427281 = 8570461) B8570461
theorem B3169853 : Blo 936583 3169853 := bstep (se 3 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 3169853 = 1188695) B1188695
theorem B2743961 : Blo 936583 2743961 := bstep (se 2 (by rfl) ⟨1028985, by rfl⟩ : syracuseStep 2743961 = 2057971) B2057971
theorem B1204027 : Blo 936583 1204027 := bstep (se 1 (by rfl) ⟨903020, by rfl⟩ : syracuseStep 1204027 = 1806041) B1806041
theorem B3563473 : Blo 936583 3563473 := bstep (se 2 (by rfl) ⟨1336302, by rfl⟩ : syracuseStep 3563473 = 2672605) B2672605
theorem B4743197 : Blo 936583 4743197 := bstep (se 3 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 4743197 = 1778699) B1778699
theorem B2252935 : Blo 936583 2252935 := bstep (se 1 (by rfl) ⟨1689701, by rfl⟩ : syracuseStep 2252935 = 3379403) B3379403
theorem B3563777 : Blo 936583 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B4743683 : Blo 936583 4743683 := bstep (se 1 (by rfl) ⟨3557762, by rfl⟩ : syracuseStep 4743683 = 7115525) B7115525
theorem B7135937 : Blo 936583 7135937 := bstep (se 2 (by rfl) ⟨2675976, by rfl⟩ : syracuseStep 7135937 = 5351953) B5351953
theorem B3564233 : Blo 936583 3564233 := bstep (se 2 (by rfl) ⟨1336587, by rfl⟩ : syracuseStep 3564233 = 2673175) B2673175
theorem B4514561 : Blo 936583 4514561 := bstep (se 2 (by rfl) ⟨1692960, by rfl⟩ : syracuseStep 4514561 = 3385921) B3385921
theorem B3171257 : Blo 936583 3171257 := bstep (se 2 (by rfl) ⟨1189221, by rfl⟩ : syracuseStep 3171257 = 2378443) B2378443
theorem B9036805 : Blo 936583 9036805 := bstep (se 4 (by rfl) ⟨847200, by rfl⟩ : syracuseStep 9036805 = 1694401) B1694401
theorem B1500535 : Blo 936583 1500535 := bstep (se 1 (by rfl) ⟨1125401, by rfl⟩ : syracuseStep 1500535 = 2250803) B2250803
theorem B5334457 : Blo 936583 5334457 := bstep (se 2 (by rfl) ⟨2000421, by rfl⟩ : syracuseStep 5334457 = 4000843) B4000843
theorem B3171851 : Blo 936583 3171851 := bstep (se 1 (by rfl) ⟨2378888, by rfl⟩ : syracuseStep 3171851 = 4757777) B4757777
theorem B3171959 : Blo 936583 3171959 := bstep (se 1 (by rfl) ⟨2378969, by rfl⟩ : syracuseStep 3171959 = 4757939) B4757939
theorem B43378355 : Blo 936583 43378355 := bstep (se 1 (by rfl) ⟨32533766, by rfl⟩ : syracuseStep 43378355 = 65067533) B65067533
theorem B4745303 : Blo 936583 4745303 := bstep (se 1 (by rfl) ⟨3558977, by rfl⟩ : syracuseStep 4745303 = 7117955) B7117955
theorem B3172553 : Blo 936583 3172553 := bstep (se 2 (by rfl) ⟨1189707, by rfl⟩ : syracuseStep 3172553 = 2379415) B2379415
theorem B2287883 : Blo 936583 2287883 := bstep (se 1 (by rfl) ⟨1715912, by rfl⟩ : syracuseStep 2287883 = 3431825) B3431825
theorem B2714141 : Blo 936583 2714141 := bstep (se 3 (by rfl) ⟨508901, by rfl⟩ : syracuseStep 2714141 = 1017803) B1017803
theorem B4745789 : Blo 936583 4745789 := bstep (se 3 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 4745789 = 1779671) B1779671
theorem B5073475 : Blo 936583 5073475 := bstep (se 1 (by rfl) ⟨3805106, by rfl⟩ : syracuseStep 5073475 = 7610213) B7610213
theorem B5073601 : Blo 936583 5073601 := bstep (se 2 (by rfl) ⟨1902600, by rfl⟩ : syracuseStep 5073601 = 3805201) B3805201
theorem B2255617 : Blo 936583 2255617 := bstep (se 2 (by rfl) ⟨845856, by rfl⟩ : syracuseStep 2255617 = 1691713) B1691713
theorem B2255627 : Blo 936583 2255627 := bstep (se 1 (by rfl) ⟨1691720, by rfl⟩ : syracuseStep 2255627 = 3383441) B3383441
theorem B3173255 : Blo 936583 3173255 := bstep (se 1 (by rfl) ⟨2379941, by rfl⟩ : syracuseStep 3173255 = 4759883) B4759883
theorem B9005975 : Blo 936583 9005975 := bstep (se 1 (by rfl) ⟨6754481, by rfl⟩ : syracuseStep 9005975 = 13508963) B13508963
theorem B4516829 : Blo 936583 4516829 := bstep (se 3 (by rfl) ⟨846905, by rfl⟩ : syracuseStep 4516829 = 1693811) B1693811
theorem B3173633 : Blo 936583 3173633 := bstep (se 2 (by rfl) ⟨1190112, by rfl⟩ : syracuseStep 3173633 = 2380225) B2380225
theorem B2256281 : Blo 936583 2256281 := bstep (se 2 (by rfl) ⟨846105, by rfl⟩ : syracuseStep 2256281 = 1692211) B1692211
theorem B2256569 : Blo 936583 2256569 := bstep (se 2 (by rfl) ⟨846213, by rfl⟩ : syracuseStep 2256569 = 1692427) B1692427
theorem B3567361 : Blo 936583 3567361 := bstep (se 2 (by rfl) ⟨1337760, by rfl⟩ : syracuseStep 3567361 = 2675521) B2675521
theorem B6025049 : Blo 936583 6025049 := bstep (se 2 (by rfl) ⟨2259393, by rfl⟩ : syracuseStep 6025049 = 4518787) B4518787
theorem B5697539 : Blo 936583 5697539 := bstep (se 1 (by rfl) ⟨4273154, by rfl⟩ : syracuseStep 5697539 = 8546309) B8546309
theorem B1404935 : Blo 936583 1404935 := bstep (se 1 (by rfl) ⟨1053701, by rfl⟩ : syracuseStep 1404935 = 2107403) B2107403
theorem B7139339 : Blo 936583 7139339 := bstep (se 1 (by rfl) ⟨5354504, by rfl⟩ : syracuseStep 7139339 = 10709009) B10709009
theorem B1404971 : Blo 936583 1404971 := bstep (se 1 (by rfl) ⟨1053728, by rfl⟩ : syracuseStep 1404971 = 2107457) B2107457
theorem B3010603 : Blo 936583 3010603 := bstep (se 1 (by rfl) ⟨2257952, by rfl⟩ : syracuseStep 3010603 = 4515905) B4515905
theorem B3174443 : Blo 936583 3174443 := bstep (se 1 (by rfl) ⟨2380832, by rfl⟩ : syracuseStep 3174443 = 4761665) B4761665
theorem B1405001 : Blo 936583 1405001 := bstep (se 2 (by rfl) ⟨526875, by rfl⟩ : syracuseStep 1405001 = 1053751) B1053751
theorem B18280541 : Blo 936583 18280541 := bstep (se 3 (by rfl) ⟨3427601, by rfl⟩ : syracuseStep 18280541 = 6855203) B6855203
theorem B1405115 : Blo 936583 1405115 := bstep (se 1 (by rfl) ⟨1053836, by rfl⟩ : syracuseStep 1405115 = 2107673) B2107673
theorem B1405175 : Blo 936583 1405175 := bstep (se 1 (by rfl) ⟨1053881, by rfl⟩ : syracuseStep 1405175 = 2107763) B2107763
theorem B1405199 : Blo 936583 1405199 := bstep (se 1 (by rfl) ⟨1053899, by rfl⟩ : syracuseStep 1405199 = 2107799) B2107799
theorem B4747571 : Blo 936583 4747571 := bstep (se 1 (by rfl) ⟨3560678, by rfl⟩ : syracuseStep 4747571 = 7121357) B7121357
theorem B1405241 : Blo 936583 1405241 := bstep (se 2 (by rfl) ⟨526965, by rfl⟩ : syracuseStep 1405241 = 1053931) B1053931
theorem B1405319 : Blo 936583 1405319 := bstep (se 1 (by rfl) ⟨1053989, by rfl⟩ : syracuseStep 1405319 = 2107979) B2107979
theorem B1503623 : Blo 936583 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B1405355 : Blo 936583 1405355 := bstep (se 1 (by rfl) ⟨1054016, by rfl⟩ : syracuseStep 1405355 = 2108033) B2108033
theorem B1405385 : Blo 936583 1405385 := bstep (se 2 (by rfl) ⟨527019, by rfl⟩ : syracuseStep 1405385 = 1054039) B1054039
theorem B1405499 : Blo 936583 1405499 := bstep (se 1 (by rfl) ⟨1054124, by rfl⟩ : syracuseStep 1405499 = 2108249) B2108249
theorem B1405559 : Blo 936583 1405559 := bstep (se 1 (by rfl) ⟨1054169, by rfl⟩ : syracuseStep 1405559 = 2108339) B2108339
theorem B4747895 : Blo 936583 4747895 := bstep (se 1 (by rfl) ⟨3560921, by rfl⟩ : syracuseStep 4747895 = 7121843) B7121843
theorem B1405583 : Blo 936583 1405583 := bstep (se 1 (by rfl) ⟨1054187, by rfl⟩ : syracuseStep 1405583 = 2108375) B2108375
theorem B1405625 : Blo 936583 1405625 := bstep (se 2 (by rfl) ⟨527109, by rfl⟩ : syracuseStep 1405625 = 1054219) B1054219
theorem B1405703 : Blo 936583 1405703 := bstep (se 1 (by rfl) ⟨1054277, by rfl⟩ : syracuseStep 1405703 = 2108555) B2108555
theorem B1405739 : Blo 936583 1405739 := bstep (se 1 (by rfl) ⟨1054304, by rfl⟩ : syracuseStep 1405739 = 2108609) B2108609
theorem B1405769 : Blo 936583 1405769 := bstep (se 2 (by rfl) ⟨527163, by rfl⟩ : syracuseStep 1405769 = 1054327) B1054327
theorem B1405883 : Blo 936583 1405883 := bstep (se 1 (by rfl) ⟨1054412, by rfl⟩ : syracuseStep 1405883 = 2108825) B2108825
theorem B1405943 : Blo 936583 1405943 := bstep (se 1 (by rfl) ⟨1054457, by rfl⟩ : syracuseStep 1405943 = 2108915) B2108915
theorem B1405967 : Blo 936583 1405967 := bstep (se 1 (by rfl) ⟨1054475, by rfl⟩ : syracuseStep 1405967 = 2108951) B2108951
theorem B1406009 : Blo 936583 1406009 := bstep (se 2 (by rfl) ⟨527253, by rfl⟩ : syracuseStep 1406009 = 1054507) B1054507
theorem B1406087 : Blo 936583 1406087 := bstep (se 1 (by rfl) ⟨1054565, by rfl⟩ : syracuseStep 1406087 = 2109131) B2109131
theorem B1406123 : Blo 936583 1406123 := bstep (se 1 (by rfl) ⟨1054592, by rfl⟩ : syracuseStep 1406123 = 2109185) B2109185
theorem B1406153 : Blo 936583 1406153 := bstep (se 2 (by rfl) ⟨527307, by rfl⟩ : syracuseStep 1406153 = 1054615) B1054615
theorem B1406267 : Blo 936583 1406267 := bstep (se 1 (by rfl) ⟨1054700, by rfl⟩ : syracuseStep 1406267 = 2109401) B2109401
theorem B1406327 : Blo 936583 1406327 := bstep (se 1 (by rfl) ⟨1054745, by rfl⟩ : syracuseStep 1406327 = 2109491) B2109491
theorem B1406351 : Blo 936583 1406351 := bstep (se 1 (by rfl) ⟨1054763, by rfl⟩ : syracuseStep 1406351 = 2109527) B2109527
theorem B1406393 : Blo 936583 1406393 := bstep (se 2 (by rfl) ⟨527397, by rfl⟩ : syracuseStep 1406393 = 1054795) B1054795
theorem B1406471 : Blo 936583 1406471 := bstep (se 1 (by rfl) ⟨1054853, by rfl⟩ : syracuseStep 1406471 = 2109707) B2109707
theorem B1406507 : Blo 936583 1406507 := bstep (se 1 (by rfl) ⟨1054880, by rfl⟩ : syracuseStep 1406507 = 2109761) B2109761
theorem B5076523 : Blo 936583 5076523 := bstep (se 1 (by rfl) ⟨3807392, by rfl⟩ : syracuseStep 5076523 = 7614785) B7614785
theorem B4748867 : Blo 936583 4748867 := bstep (se 1 (by rfl) ⟨3561650, by rfl⟩ : syracuseStep 4748867 = 7123301) B7123301
theorem B1406537 : Blo 936583 1406537 := bstep (se 2 (by rfl) ⟨527451, by rfl⟩ : syracuseStep 1406537 = 1054903) B1054903
theorem B2258617 : Blo 936583 2258617 := bstep (se 2 (by rfl) ⟨846981, by rfl⟩ : syracuseStep 2258617 = 1693963) B1693963
theorem B1406651 : Blo 936583 1406651 := bstep (se 1 (by rfl) ⟨1054988, by rfl⟩ : syracuseStep 1406651 = 2109977) B2109977
theorem B1406711 : Blo 936583 1406711 := bstep (se 1 (by rfl) ⟨1055033, by rfl⟩ : syracuseStep 1406711 = 2110067) B2110067
theorem B1406735 : Blo 936583 1406735 := bstep (se 1 (by rfl) ⟨1055051, by rfl⟩ : syracuseStep 1406735 = 2110103) B2110103
theorem B1406777 : Blo 936583 1406777 := bstep (se 2 (by rfl) ⟨527541, by rfl⟩ : syracuseStep 1406777 = 1055083) B1055083
theorem B1406855 : Blo 936583 1406855 := bstep (se 1 (by rfl) ⟨1055141, by rfl⟩ : syracuseStep 1406855 = 2110283) B2110283
theorem B4749191 : Blo 936583 4749191 := bstep (se 1 (by rfl) ⟨3561893, by rfl⟩ : syracuseStep 4749191 = 7123787) B7123787
theorem B7141283 : Blo 936583 7141283 := bstep (se 1 (by rfl) ⟨5355962, by rfl⟩ : syracuseStep 7141283 = 10711925) B10711925
theorem B1406891 : Blo 936583 1406891 := bstep (se 1 (by rfl) ⟨1055168, by rfl⟩ : syracuseStep 1406891 = 2110337) B2110337
theorem B1406921 : Blo 936583 1406921 := bstep (se 2 (by rfl) ⟨527595, by rfl⟩ : syracuseStep 1406921 = 1055191) B1055191
theorem B1407035 : Blo 936583 1407035 := bstep (se 1 (by rfl) ⟨1055276, by rfl⟩ : syracuseStep 1407035 = 2110553) B2110553
theorem B1407095 : Blo 936583 1407095 := bstep (se 1 (by rfl) ⟨1055321, by rfl⟩ : syracuseStep 1407095 = 2110643) B2110643
theorem B1407119 : Blo 936583 1407119 := bstep (se 1 (by rfl) ⟨1055339, by rfl⟩ : syracuseStep 1407119 = 2110679) B2110679
theorem B1407161 : Blo 936583 1407161 := bstep (se 2 (by rfl) ⟨527685, by rfl⟩ : syracuseStep 1407161 = 1055371) B1055371
theorem B1407239 : Blo 936583 1407239 := bstep (se 1 (by rfl) ⟨1055429, by rfl⟩ : syracuseStep 1407239 = 2110859) B2110859
theorem B1407275 : Blo 936583 1407275 := bstep (se 1 (by rfl) ⟨1055456, by rfl⟩ : syracuseStep 1407275 = 2110913) B2110913
theorem B1407305 : Blo 936583 1407305 := bstep (se 2 (by rfl) ⟨527739, by rfl⟩ : syracuseStep 1407305 = 1055479) B1055479
theorem B1407419 : Blo 936583 1407419 := bstep (se 1 (by rfl) ⟨1055564, by rfl⟩ : syracuseStep 1407419 = 2111129) B2111129
theorem B1407479 : Blo 936583 1407479 := bstep (se 1 (by rfl) ⟨1055609, by rfl⟩ : syracuseStep 1407479 = 2111219) B2111219
theorem B1407503 : Blo 936583 1407503 := bstep (se 1 (by rfl) ⟨1055627, by rfl⟩ : syracuseStep 1407503 = 2111255) B2111255
theorem B1407545 : Blo 936583 1407545 := bstep (se 2 (by rfl) ⟨527829, by rfl⟩ : syracuseStep 1407545 = 1055659) B1055659
theorem B3570263 : Blo 936583 3570263 := bstep (se 1 (by rfl) ⟨2677697, by rfl⟩ : syracuseStep 3570263 = 5355395) B5355395
theorem B2062967 : Blo 936583 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B1407623 : Blo 936583 1407623 := bstep (se 1 (by rfl) ⟨1055717, by rfl⟩ : syracuseStep 1407623 = 2111435) B2111435
theorem B1407659 : Blo 936583 1407659 := bstep (se 1 (by rfl) ⟨1055744, by rfl⟩ : syracuseStep 1407659 = 2111489) B2111489
theorem B1604281 : Blo 936583 1604281 := bstep (se 2 (by rfl) ⟨601605, by rfl⟩ : syracuseStep 1604281 = 1203211) B1203211
theorem B1407689 : Blo 936583 1407689 := bstep (se 2 (by rfl) ⟨527883, by rfl⟩ : syracuseStep 1407689 = 1055767) B1055767
theorem B9009893 : Blo 936583 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B1407803 : Blo 936583 1407803 := bstep (se 1 (by rfl) ⟨1055852, by rfl⟩ : syracuseStep 1407803 = 2111705) B2111705
theorem B1407863 : Blo 936583 1407863 := bstep (se 1 (by rfl) ⟨1055897, by rfl⟩ : syracuseStep 1407863 = 2111795) B2111795
theorem B1407887 : Blo 936583 1407887 := bstep (se 1 (by rfl) ⟨1055915, by rfl⟩ : syracuseStep 1407887 = 2111831) B2111831
theorem B5077907 : Blo 936583 5077907 := bstep (se 1 (by rfl) ⟨3808430, by rfl⟩ : syracuseStep 5077907 = 7616861) B7616861
theorem B1407929 : Blo 936583 1407929 := bstep (se 2 (by rfl) ⟨527973, by rfl⟩ : syracuseStep 1407929 = 1055947) B1055947
theorem B5340107 : Blo 936583 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B1408007 : Blo 936583 1408007 := bstep (se 1 (by rfl) ⟨1056005, by rfl⟩ : syracuseStep 1408007 = 2112011) B2112011
theorem B1408043 : Blo 936583 1408043 := bstep (se 1 (by rfl) ⟨1056032, by rfl⟩ : syracuseStep 1408043 = 2112065) B2112065
theorem B3570749 : Blo 936583 3570749 := bstep (se 3 (by rfl) ⟨669515, by rfl⟩ : syracuseStep 3570749 = 1339031) B1339031
theorem B1408073 : Blo 936583 1408073 := bstep (se 2 (by rfl) ⟨528027, by rfl⟩ : syracuseStep 1408073 = 1056055) B1056055
theorem B1408187 : Blo 936583 1408187 := bstep (se 1 (by rfl) ⟨1056140, by rfl⟩ : syracuseStep 1408187 = 2112281) B2112281
theorem B1408247 : Blo 936583 1408247 := bstep (se 1 (by rfl) ⟨1056185, by rfl⟩ : syracuseStep 1408247 = 2112371) B2112371
theorem B1408271 : Blo 936583 1408271 := bstep (se 1 (by rfl) ⟨1056203, by rfl⟩ : syracuseStep 1408271 = 2112407) B2112407
theorem B1408313 : Blo 936583 1408313 := bstep (se 2 (by rfl) ⟨528117, by rfl⟩ : syracuseStep 1408313 = 1056235) B1056235
theorem B1899911 : Blo 936583 1899911 := bstep (se 1 (by rfl) ⟨1424933, by rfl⟩ : syracuseStep 1899911 = 2849867) B2849867
theorem B1408391 : Blo 936583 1408391 := bstep (se 1 (by rfl) ⟨1056293, by rfl⟩ : syracuseStep 1408391 = 2112587) B2112587
theorem B5340563 : Blo 936583 5340563 := bstep (se 1 (by rfl) ⟨4005422, by rfl⟩ : syracuseStep 5340563 = 8010845) B8010845
theorem B1408427 : Blo 936583 1408427 := bstep (se 1 (by rfl) ⟨1056320, by rfl⟩ : syracuseStep 1408427 = 2112641) B2112641
theorem B1408457 : Blo 936583 1408457 := bstep (se 2 (by rfl) ⟨528171, by rfl⟩ : syracuseStep 1408457 = 1056343) B1056343
theorem B1408571 : Blo 936583 1408571 := bstep (se 1 (by rfl) ⟨1056428, by rfl⟩ : syracuseStep 1408571 = 2112857) B2112857
theorem B1408631 : Blo 936583 1408631 := bstep (se 1 (by rfl) ⟨1056473, by rfl⟩ : syracuseStep 1408631 = 2112947) B2112947
theorem B1408655 : Blo 936583 1408655 := bstep (se 1 (by rfl) ⟨1056491, by rfl⟩ : syracuseStep 1408655 = 2112983) B2112983
theorem B1900217 : Blo 936583 1900217 := bstep (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) B1425163
theorem B1408697 : Blo 936583 1408697 := bstep (se 2 (by rfl) ⟨528261, by rfl⟩ : syracuseStep 1408697 = 1056523) B1056523
theorem B1408775 : Blo 936583 1408775 := bstep (se 1 (by rfl) ⟨1056581, by rfl⟩ : syracuseStep 1408775 = 2113163) B2113163
theorem B1900331 : Blo 936583 1900331 := bstep (se 1 (by rfl) ⟨1425248, by rfl⟩ : syracuseStep 1900331 = 2850497) B2850497
theorem B1408811 : Blo 936583 1408811 := bstep (se 1 (by rfl) ⟨1056608, by rfl⟩ : syracuseStep 1408811 = 2113217) B2113217
theorem B7601971 : Blo 936583 7601971 := bstep (se 1 (by rfl) ⟨5701478, by rfl⟩ : syracuseStep 7601971 = 11402957) B11402957
theorem B1408841 : Blo 936583 1408841 := bstep (se 2 (by rfl) ⟨528315, by rfl⟩ : syracuseStep 1408841 = 1056631) B1056631
theorem B1408955 : Blo 936583 1408955 := bstep (se 1 (by rfl) ⟨1056716, by rfl⟩ : syracuseStep 1408955 = 2113433) B2113433
theorem B1409015 : Blo 936583 1409015 := bstep (se 1 (by rfl) ⟨1056761, by rfl⟩ : syracuseStep 1409015 = 2113523) B2113523
theorem B1409033 : Blo 936583 1409033 := bstep (se 2 (by rfl) ⟨528387, by rfl⟩ : syracuseStep 1409033 = 1056775) B1056775
theorem B1409063 : Blo 936583 1409063 := bstep (se 1 (by rfl) ⟨1056797, by rfl⟩ : syracuseStep 1409063 = 2113595) B2113595
theorem B3801167 : Blo 936583 3801167 := bstep (se 1 (by rfl) ⟨2850875, by rfl⟩ : syracuseStep 3801167 = 5701751) B5701751
theorem B1409147 : Blo 936583 1409147 := bstep (se 1 (by rfl) ⟨1056860, by rfl⟩ : syracuseStep 1409147 = 2113721) B2113721
theorem B1409273 : Blo 936583 1409273 := bstep (se 2 (by rfl) ⟨528477, by rfl⟩ : syracuseStep 1409273 = 1056955) B1056955
theorem B1409375 : Blo 936583 1409375 := bstep (se 1 (by rfl) ⟨1057031, by rfl⟩ : syracuseStep 1409375 = 2114063) B2114063
theorem B1409387 : Blo 936583 1409387 := bstep (se 1 (by rfl) ⟨1057040, by rfl⟩ : syracuseStep 1409387 = 2114081) B2114081
theorem B1409615 : Blo 936583 1409615 := bstep (se 1 (by rfl) ⟨1057211, by rfl⟩ : syracuseStep 1409615 = 2114423) B2114423
theorem B1409735 : Blo 936583 1409735 := bstep (se 1 (by rfl) ⟨1057301, by rfl⟩ : syracuseStep 1409735 = 2114603) B2114603
theorem B1409897 : Blo 936583 1409897 := bstep (se 2 (by rfl) ⟨528711, by rfl⟩ : syracuseStep 1409897 = 1057423) B1057423
theorem B1409975 : Blo 936583 1409975 := bstep (se 1 (by rfl) ⟨1057481, by rfl⟩ : syracuseStep 1409975 = 2114963) B2114963
theorem B1410011 : Blo 936583 1410011 := bstep (se 1 (by rfl) ⟨1057508, by rfl⟩ : syracuseStep 1410011 = 2115017) B2115017
theorem B19268761 : Blo 936583 19268761 := bstep (se 2 (by rfl) ⟨7225785, by rfl⟩ : syracuseStep 19268761 = 14451571) B14451571
theorem B1410479 : Blo 936583 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B5703131 : Blo 936583 5703131 := bstep (se 1 (by rfl) ⟨4277348, by rfl⟩ : syracuseStep 5703131 = 8554697) B8554697
theorem B1410569 : Blo 936583 1410569 := bstep (se 2 (by rfl) ⟨528963, by rfl⟩ : syracuseStep 1410569 = 1057927) B1057927
theorem B1410599 : Blo 936583 1410599 := bstep (se 1 (by rfl) ⟨1057949, by rfl⟩ : syracuseStep 1410599 = 2115899) B2115899
theorem B1410683 : Blo 936583 1410683 := bstep (se 1 (by rfl) ⟨1058012, by rfl⟩ : syracuseStep 1410683 = 2116025) B2116025
theorem B3212939 : Blo 936583 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B2852567 : Blo 936583 2852567 := bstep (se 1 (by rfl) ⟨2139425, by rfl⟩ : syracuseStep 2852567 = 4278851) B4278851
theorem B1410809 : Blo 936583 1410809 := bstep (se 2 (by rfl) ⟨529053, by rfl⟩ : syracuseStep 1410809 = 1058107) B1058107
theorem B2000713 : Blo 936583 2000713 := bstep (se 2 (by rfl) ⟨750267, by rfl⟩ : syracuseStep 2000713 = 1500535) B1500535
theorem B7112609 : Blo 936583 7112609 := bstep (se 2 (by rfl) ⟨2667228, by rfl⟩ : syracuseStep 7112609 = 5334457) B5334457
theorem B4753565 : Blo 936583 4753565 := bstep (se 3 (by rfl) ⟨891293, by rfl⟩ : syracuseStep 4753565 = 1782587) B1782587
theorem B1902943 : Blo 936583 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B3377963 : Blo 936583 3377963 := bstep (se 1 (by rfl) ⟨2533472, by rfl⟩ : syracuseStep 3377963 = 5066945) B5066945
theorem B4001015 : Blo 936583 4001015 := bstep (se 1 (by rfl) ⟨3000761, by rfl⟩ : syracuseStep 4001015 = 6001523) B6001523
theorem B9276707 : Blo 936583 9276707 := bstep (se 1 (by rfl) ⟨6957530, by rfl⟩ : syracuseStep 9276707 = 13915061) B13915061
theorem B4754861 : Blo 936583 4754861 := bstep (se 3 (by rfl) ⟨891536, by rfl⟩ : syracuseStep 4754861 = 1783073) B1783073
theorem B3378827 : Blo 936583 3378827 := bstep (se 1 (by rfl) ⟨2534120, by rfl⟩ : syracuseStep 3378827 = 5068241) B5068241
theorem B12029957 : Blo 936583 12029957 := bstep (se 4 (by rfl) ⟨1127808, by rfl⟩ : syracuseStep 12029957 = 2255617) B2255617
theorem B30871667 : Blo 936583 30871667 := bstep (se 1 (by rfl) ⟨23153750, by rfl⟩ : syracuseStep 30871667 = 46307501) B46307501
theorem B1905001 : Blo 936583 1905001 := bstep (se 2 (by rfl) ⟨714375, by rfl⟩ : syracuseStep 1905001 = 1428751) B1428751
theorem B3805721 : Blo 936583 3805721 := bstep (se 2 (by rfl) ⟨1427145, by rfl⟩ : syracuseStep 3805721 = 2854291) B2854291
theorem B3379751 : Blo 936583 3379751 := bstep (se 1 (by rfl) ⟨2534813, by rfl⟩ : syracuseStep 3379751 = 5069627) B5069627
theorem B5346121 : Blo 936583 5346121 := bstep (se 2 (by rfl) ⟨2004795, by rfl⟩ : syracuseStep 5346121 = 4009591) B4009591
theorem B4756481 : Blo 936583 4756481 := bstep (se 2 (by rfl) ⟨1783680, by rfl⟩ : syracuseStep 4756481 = 3567361) B3567361
theorem B1053895 : Blo 936583 1053895 := bstep (se 1 (by rfl) ⟨790421, by rfl⟩ : syracuseStep 1053895 = 1580843) B1580843
theorem B6755575 : Blo 936583 6755575 := bstep (se 1 (by rfl) ⟨5066681, by rfl⟩ : syracuseStep 6755575 = 10133363) B10133363
theorem B3806759 : Blo 936583 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B10163809 : Blo 936583 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B10851985 : Blo 936583 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B4003577 : Blo 936583 4003577 := bstep (se 2 (by rfl) ⟨1501341, by rfl⟩ : syracuseStep 4003577 = 3002683) B3002683
theorem B20322083 : Blo 936583 20322083 := bstep (se 1 (by rfl) ⟨15241562, by rfl⟩ : syracuseStep 20322083 = 30483125) B30483125
theorem B4757291 : Blo 936583 4757291 := bstep (se 1 (by rfl) ⟨3567968, by rfl⟩ : syracuseStep 4757291 = 7135937) B7135937
theorem B6428483 : Blo 936583 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B6101021 : Blo 936583 6101021 := bstep (se 3 (by rfl) ⟨1143941, by rfl⟩ : syracuseStep 6101021 = 2287883) B2287883
theorem B1054759 : Blo 936583 1054759 := bstep (se 1 (by rfl) ⟨791069, by rfl⟩ : syracuseStep 1054759 = 1582139) B1582139
theorem B3610985 : Blo 936583 3610985 := bstep (se 2 (by rfl) ⟨1354119, by rfl⟩ : syracuseStep 3610985 = 2708239) B2708239
theorem B7215563 : Blo 936583 7215563 := bstep (se 1 (by rfl) ⟨5411672, by rfl⟩ : syracuseStep 7215563 = 10823345) B10823345
theorem B1186427 : Blo 936583 1186427 := bstep (se 1 (by rfl) ⟨889820, by rfl⟩ : syracuseStep 1186427 = 1779641) B1779641
theorem B16226993 : Blo 936583 16226993 := bstep (se 2 (by rfl) ⟨6085122, by rfl⟩ : syracuseStep 16226993 = 12170245) B12170245
theorem B2169593 : Blo 936583 2169593 := bstep (se 2 (by rfl) ⟨813597, by rfl⟩ : syracuseStep 2169593 = 1627195) B1627195
theorem B1809427 : Blo 936583 1809427 := bstep (se 1 (by rfl) ⟨1357070, by rfl⟩ : syracuseStep 1809427 = 2714141) B2714141
theorem B24026381 : Blo 936583 24026381 := bstep (se 3 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 24026381 = 9009893) B9009893
theorem B6003983 : Blo 936583 6003983 := bstep (se 1 (by rfl) ⟨4502987, by rfl⟩ : syracuseStep 6003983 = 9005975) B9005975
theorem B1056379 : Blo 936583 1056379 := bstep (se 1 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 1056379 = 1584569) B1584569
theorem B24387443 : Blo 936583 24387443 := bstep (se 1 (by rfl) ⟨18290582, by rfl⟩ : syracuseStep 24387443 = 36581165) B36581165
theorem B4759559 : Blo 936583 4759559 := bstep (se 1 (by rfl) ⟨3569669, by rfl⟩ : syracuseStep 4759559 = 7139339) B7139339
theorem B1581113 : Blo 936583 1581113 := bstep (se 2 (by rfl) ⟨592917, by rfl⟩ : syracuseStep 1581113 = 1185835) B1185835
theorem B1056847 : Blo 936583 1056847 := bstep (se 1 (by rfl) ⟨792635, by rfl⟩ : syracuseStep 1056847 = 1585271) B1585271
theorem B1778107 : Blo 936583 1778107 := bstep (se 1 (by rfl) ⟨1333580, by rfl⟩ : syracuseStep 1778107 = 2667161) B2667161
theorem B1057243 : Blo 936583 1057243 := bstep (se 1 (by rfl) ⟨792932, by rfl⟩ : syracuseStep 1057243 = 1585865) B1585865
theorem B4760045 : Blo 936583 4760045 := bstep (se 3 (by rfl) ⟨892508, by rfl⟩ : syracuseStep 4760045 = 1785017) B1785017
theorem B1778183 : Blo 936583 1778183 := bstep (se 1 (by rfl) ⟨1333637, by rfl⟩ : syracuseStep 1778183 = 2667275) B2667275
theorem B1581815 : Blo 936583 1581815 := bstep (se 1 (by rfl) ⟨1186361, by rfl⟩ : syracuseStep 1581815 = 2372723) B2372723
theorem B1778593 : Blo 936583 1778593 := bstep (se 2 (by rfl) ⟨666972, by rfl⟩ : syracuseStep 1778593 = 1333945) B1333945
theorem B2139041 : Blo 936583 2139041 := bstep (se 2 (by rfl) ⟨802140, by rfl⟩ : syracuseStep 2139041 = 1604281) B1604281
theorem B1057711 : Blo 936583 1057711 := bstep (se 1 (by rfl) ⟨793283, by rfl⟩ : syracuseStep 1057711 = 1586567) B1586567
theorem B1582159 : Blo 936583 1582159 := bstep (se 1 (by rfl) ⟨1186619, by rfl⟩ : syracuseStep 1582159 = 2373239) B2373239
theorem B1778935 : Blo 936583 1778935 := bstep (se 1 (by rfl) ⟨1334201, by rfl⟩ : syracuseStep 1778935 = 2668403) B2668403
theorem B7611671 : Blo 936583 7611671 := bstep (se 1 (by rfl) ⟨5708753, by rfl⟩ : syracuseStep 7611671 = 11417507) B11417507
theorem B4760855 : Blo 936583 4760855 := bstep (se 1 (by rfl) ⟨3570641, by rfl⟩ : syracuseStep 4760855 = 7141283) B7141283
theorem B1582409 : Blo 936583 1582409 := bstep (se 2 (by rfl) ⟨593403, by rfl⟩ : syracuseStep 1582409 = 1186807) B1186807
theorem B1058143 : Blo 936583 1058143 := bstep (se 1 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 1058143 = 1587215) B1587215
theorem B1779239 : Blo 936583 1779239 := bstep (se 1 (by rfl) ⟨1334429, by rfl⟩ : syracuseStep 1779239 = 2668859) B2668859
theorem B7317229 : Blo 936583 7317229 := bstep (se 3 (by rfl) ⟨1371980, by rfl⟩ : syracuseStep 7317229 = 2743961) B2743961
theorem B1582841 : Blo 936583 1582841 := bstep (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) B1187131
theorem B1583023 : Blo 936583 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B3385271 : Blo 936583 3385271 := bstep (se 1 (by rfl) ⟨2538953, by rfl⟩ : syracuseStep 3385271 = 5077907) B5077907
theorem B1583111 : Blo 936583 1583111 := bstep (se 1 (by rfl) ⟨1187333, by rfl⟩ : syracuseStep 1583111 = 2374667) B2374667
theorem B4007951 : Blo 936583 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B1583455 : Blo 936583 1583455 := bstep (se 1 (by rfl) ⟨1187591, by rfl⟩ : syracuseStep 1583455 = 2375183) B2375183
theorem B10135961 : Blo 936583 10135961 := bstep (se 2 (by rfl) ⟨3800985, by rfl⟩ : syracuseStep 10135961 = 7601971) B7601971
theorem B1583543 : Blo 936583 1583543 := bstep (se 1 (by rfl) ⟨1187657, by rfl⟩ : syracuseStep 1583543 = 2375315) B2375315
theorem B4958729 : Blo 936583 4958729 := bstep (se 2 (by rfl) ⟨1859523, by rfl⟩ : syracuseStep 4958729 = 3719047) B3719047
theorem B2107943 : Blo 936583 2107943 := bstep (se 1 (by rfl) ⟨1580957, by rfl⟩ : syracuseStep 2107943 = 3161915) B3161915
theorem B2108267 : Blo 936583 2108267 := bstep (se 1 (by rfl) ⟨1581200, by rfl⟩ : syracuseStep 2108267 = 3162401) B3162401
theorem B2108321 : Blo 936583 2108321 := bstep (se 2 (by rfl) ⟨790620, by rfl⟩ : syracuseStep 2108321 = 1581241) B1581241
theorem B1125295 : Blo 936583 1125295 := bstep (se 1 (by rfl) ⟨843971, by rfl⟩ : syracuseStep 1125295 = 1687943) B1687943
theorem B1584137 : Blo 936583 1584137 := bstep (se 2 (by rfl) ⟨594051, by rfl⟩ : syracuseStep 1584137 = 1188103) B1188103
theorem B1584299 : Blo 936583 1584299 := bstep (se 1 (by rfl) ⟨1188224, by rfl⟩ : syracuseStep 1584299 = 2376449) B2376449
theorem B8006849 : Blo 936583 8006849 := bstep (se 2 (by rfl) ⟨3002568, by rfl⟩ : syracuseStep 8006849 = 6005137) B6005137
theorem B2108663 : Blo 936583 2108663 := bstep (se 1 (by rfl) ⟨1581497, by rfl⟩ : syracuseStep 2108663 = 3162995) B3162995
theorem B1781099 : Blo 936583 1781099 := bstep (se 1 (by rfl) ⟨1335824, by rfl⟩ : syracuseStep 1781099 = 2671649) B2671649
theorem B3386843 : Blo 936583 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B1584697 : Blo 936583 1584697 := bstep (se 2 (by rfl) ⟨594261, by rfl⟩ : syracuseStep 1584697 = 1188523) B1188523
theorem B1781327 : Blo 936583 1781327 := bstep (se 1 (by rfl) ⟨1335995, by rfl⟩ : syracuseStep 1781327 = 2671991) B2671991
theorem B4009661 : Blo 936583 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B2404039 : Blo 936583 2404039 := bstep (se 1 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 2404039 = 3606059) B3606059
theorem B1584839 : Blo 936583 1584839 := bstep (se 1 (by rfl) ⟨1188629, by rfl⟩ : syracuseStep 1584839 = 2377259) B2377259
theorem B9023197 : Blo 936583 9023197 := bstep (se 3 (by rfl) ⟨1691849, by rfl⟩ : syracuseStep 9023197 = 3383699) B3383699
theorem B4501241 : Blo 936583 4501241 := bstep (se 2 (by rfl) ⟨1687965, by rfl⟩ : syracuseStep 4501241 = 3375931) B3375931
theorem B2109257 : Blo 936583 2109257 := bstep (se 2 (by rfl) ⟨790971, by rfl⟩ : syracuseStep 2109257 = 1581943) B1581943
theorem B1585001 : Blo 936583 1585001 := bstep (se 2 (by rfl) ⟨594375, by rfl⟩ : syracuseStep 1585001 = 1188751) B1188751
theorem B1781767 : Blo 936583 1781767 := bstep (se 1 (by rfl) ⟨1336325, by rfl⟩ : syracuseStep 1781767 = 2672651) B2672651
theorem B1585399 : Blo 936583 1585399 := bstep (se 1 (by rfl) ⟨1189049, by rfl⟩ : syracuseStep 1585399 = 2378099) B2378099
theorem B6435073 : Blo 936583 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B1585595 : Blo 936583 1585595 := bstep (se 1 (by rfl) ⟨1189196, by rfl⟩ : syracuseStep 1585595 = 2378393) B2378393
theorem B15249869 : Blo 936583 15249869 := bstep (se 3 (by rfl) ⟨2859350, by rfl⟩ : syracuseStep 15249869 = 5718701) B5718701
theorem B2372105 : Blo 936583 2372105 := bstep (se 2 (by rfl) ⟨889539, by rfl⟩ : syracuseStep 2372105 = 1779079) B1779079
theorem B1585703 : Blo 936583 1585703 := bstep (se 1 (by rfl) ⟨1189277, by rfl⟩ : syracuseStep 1585703 = 2378555) B2378555
theorem B2110049 : Blo 936583 2110049 := bstep (se 2 (by rfl) ⟨791268, by rfl⟩ : syracuseStep 2110049 = 1582537) B1582537
theorem B10138385 : Blo 936583 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B1585993 : Blo 936583 1585993 := bstep (se 2 (by rfl) ⟨594747, by rfl⟩ : syracuseStep 1585993 = 1189495) B1189495
theorem B1586027 : Blo 936583 1586027 := bstep (se 1 (by rfl) ⟨1189520, by rfl⟩ : syracuseStep 1586027 = 2379041) B2379041
theorem B2110391 : Blo 936583 2110391 := bstep (se 1 (by rfl) ⟨1582793, by rfl⟩ : syracuseStep 2110391 = 3165587) B3165587
theorem B1782823 : Blo 936583 1782823 := bstep (se 1 (by rfl) ⟨1337117, by rfl⟩ : syracuseStep 1782823 = 2674235) B2674235
theorem B1586425 : Blo 936583 1586425 := bstep (se 2 (by rfl) ⟨594909, by rfl⟩ : syracuseStep 1586425 = 1189819) B1189819
theorem B1586695 : Blo 936583 1586695 := bstep (se 1 (by rfl) ⟨1190021, by rfl⟩ : syracuseStep 1586695 = 2380043) B2380043
theorem B2110985 : Blo 936583 2110985 := bstep (se 2 (by rfl) ⟨791619, by rfl⟩ : syracuseStep 2110985 = 1583239) B1583239
theorem B2373259 : Blo 936583 2373259 := bstep (se 1 (by rfl) ⟨1779944, by rfl⟩ : syracuseStep 2373259 = 3559889) B3559889
theorem B2668231 : Blo 936583 2668231 := bstep (se 1 (by rfl) ⟨2001173, by rfl⟩ : syracuseStep 2668231 = 4002347) B4002347
theorem B4503239 : Blo 936583 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B2111327 : Blo 936583 2111327 := bstep (se 1 (by rfl) ⟨1583495, by rfl⟩ : syracuseStep 2111327 = 3166991) B3166991
theorem B7223201 : Blo 936583 7223201 := bstep (se 2 (by rfl) ⟨2708700, by rfl⟩ : syracuseStep 7223201 = 5417401) B5417401
theorem B1587127 : Blo 936583 1587127 := bstep (se 1 (by rfl) ⟨1190345, by rfl⟩ : syracuseStep 1587127 = 2380691) B2380691
theorem B2373563 : Blo 936583 2373563 := bstep (se 1 (by rfl) ⟨1780172, by rfl⟩ : syracuseStep 2373563 = 3560345) B3560345
theorem B2111507 : Blo 936583 2111507 := bstep (se 1 (by rfl) ⟨1583630, by rfl⟩ : syracuseStep 2111507 = 3167261) B3167261
theorem B6764573 : Blo 936583 6764573 := bstep (se 3 (by rfl) ⟨1268357, by rfl⟩ : syracuseStep 6764573 = 2536715) B2536715
theorem B6764633 : Blo 936583 6764633 := bstep (se 2 (by rfl) ⟨2536737, by rfl⟩ : syracuseStep 6764633 = 5073475) B5073475
theorem B6764801 : Blo 936583 6764801 := bstep (se 2 (by rfl) ⟨2536800, by rfl⟩ : syracuseStep 6764801 = 5073601) B5073601
theorem B534034781 : Blo 936583 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B2111849 : Blo 936583 2111849 := bstep (se 2 (by rfl) ⟨791943, by rfl⟩ : syracuseStep 2111849 = 1583887) B1583887
theorem B2374343 : Blo 936583 2374343 := bstep (se 1 (by rfl) ⟨1780757, by rfl⟩ : syracuseStep 2374343 = 3561515) B3561515
theorem B1784531 : Blo 936583 1784531 := bstep (se 1 (by rfl) ⟨1338398, by rfl⟩ : syracuseStep 1784531 = 2676797) B2676797
theorem B2374393 : Blo 936583 2374393 := bstep (se 2 (by rfl) ⟨890397, by rfl⟩ : syracuseStep 2374393 = 1780795) B1780795
theorem B1784683 : Blo 936583 1784683 := bstep (se 1 (by rfl) ⟨1338512, by rfl⟩ : syracuseStep 1784683 = 2677025) B2677025
theorem B2112443 : Blo 936583 2112443 := bstep (se 1 (by rfl) ⟨1584332, by rfl⟩ : syracuseStep 2112443 = 3168665) B3168665
theorem B2112569 : Blo 936583 2112569 := bstep (se 2 (by rfl) ⟨792213, by rfl⟩ : syracuseStep 2112569 = 1584427) B1584427
theorem B1784911 : Blo 936583 1784911 := bstep (se 1 (by rfl) ⟨1338683, by rfl⟩ : syracuseStep 1784911 = 2677367) B2677367
theorem B2538877 : Blo 936583 2538877 := bstep (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) B952079
theorem B2375041 : Blo 936583 2375041 := bstep (se 2 (by rfl) ⟨890640, by rfl⟩ : syracuseStep 2375041 = 1781281) B1781281
theorem B2112911 : Blo 936583 2112911 := bstep (se 1 (by rfl) ⟨1584683, by rfl⟩ : syracuseStep 2112911 = 3169367) B3169367
theorem B2670043 : Blo 936583 2670043 := bstep (se 1 (by rfl) ⟨2002532, by rfl⟩ : syracuseStep 2670043 = 4005065) B4005065
theorem B7618187 : Blo 936583 7618187 := bstep (se 1 (by rfl) ⟨5713640, by rfl⟩ : syracuseStep 7618187 = 11427281) B11427281
theorem B2113235 : Blo 936583 2113235 := bstep (se 1 (by rfl) ⟨1584926, by rfl⟩ : syracuseStep 2113235 = 3169853) B3169853
theorem B3162131 : Blo 936583 3162131 := bstep (se 1 (by rfl) ⟨2371598, by rfl⟩ : syracuseStep 3162131 = 4743197) B4743197
theorem B4014137 : Blo 936583 4014137 := bstep (se 2 (by rfl) ⟨1505301, by rfl⟩ : syracuseStep 4014137 = 3010603) B3010603
theorem B2375851 : Blo 936583 2375851 := bstep (se 1 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 2375851 = 3563777) B3563777
theorem B1687799 : Blo 936583 1687799 := bstep (se 1 (by rfl) ⟨1265849, by rfl⟩ : syracuseStep 1687799 = 2531699) B2531699
theorem B3162455 : Blo 936583 3162455 := bstep (se 1 (by rfl) ⟨2371841, by rfl⟩ : syracuseStep 3162455 = 4743683) B4743683
theorem B30458213 : Blo 936583 30458213 := bstep (se 4 (by rfl) ⟨2855457, by rfl⟩ : syracuseStep 30458213 = 5710915) B5710915
theorem B2376155 : Blo 936583 2376155 := bstep (se 1 (by rfl) ⟨1782116, by rfl⟩ : syracuseStep 2376155 = 3564233) B3564233
theorem B2114171 : Blo 936583 2114171 := bstep (se 1 (by rfl) ⟨1585628, by rfl⟩ : syracuseStep 2114171 = 3171257) B3171257
theorem B2671319 : Blo 936583 2671319 := bstep (se 1 (by rfl) ⟨2003489, by rfl⟩ : syracuseStep 2671319 = 4006979) B4006979
theorem B2114297 : Blo 936583 2114297 := bstep (se 2 (by rfl) ⟨792861, by rfl⟩ : syracuseStep 2114297 = 1585723) B1585723
theorem B3556169 : Blo 936583 3556169 := bstep (se 2 (by rfl) ⟨1333563, by rfl⟩ : syracuseStep 3556169 = 2667127) B2667127
theorem B2671535 : Blo 936583 2671535 := bstep (se 1 (by rfl) ⟨2003651, by rfl⟩ : syracuseStep 2671535 = 4007303) B4007303
theorem B14468015 : Blo 936583 14468015 := bstep (se 1 (by rfl) ⟨10851011, by rfl⟩ : syracuseStep 14468015 = 21702023) B21702023
theorem B2114567 : Blo 936583 2114567 := bstep (se 1 (by rfl) ⟨1585925, by rfl⟩ : syracuseStep 2114567 = 3171851) B3171851
theorem B46253105 : Blo 936583 46253105 := bstep (se 2 (by rfl) ⟨17344914, by rfl⟩ : syracuseStep 46253105 = 34689829) B34689829
theorem B2114639 : Blo 936583 2114639 := bstep (se 1 (by rfl) ⟨1585979, by rfl⟩ : syracuseStep 2114639 = 3171959) B3171959
theorem B28918903 : Blo 936583 28918903 := bstep (se 1 (by rfl) ⟨21689177, by rfl⟩ : syracuseStep 28918903 = 43378355) B43378355
theorem B3556669 : Blo 936583 3556669 := bstep (se 3 (by rfl) ⟨666875, by rfl⟩ : syracuseStep 3556669 = 1333751) B1333751
theorem B3163535 : Blo 936583 3163535 := bstep (se 1 (by rfl) ⟨2372651, by rfl⟩ : syracuseStep 3163535 = 4745303) B4745303
theorem B2115035 : Blo 936583 2115035 := bstep (se 1 (by rfl) ⟨1586276, by rfl⟩ : syracuseStep 2115035 = 3172553) B3172553
theorem B3163859 : Blo 936583 3163859 := bstep (se 1 (by rfl) ⟨2372894, by rfl⟩ : syracuseStep 3163859 = 4745789) B4745789
theorem B2377633 : Blo 936583 2377633 := bstep (se 2 (by rfl) ⟨891612, by rfl⟩ : syracuseStep 2377633 = 1783225) B1783225
theorem B2115503 : Blo 936583 2115503 := bstep (se 1 (by rfl) ⟨1586627, by rfl⟩ : syracuseStep 2115503 = 3173255) B3173255
theorem B6768697 : Blo 936583 6768697 := bstep (se 2 (by rfl) ⟨2538261, by rfl⟩ : syracuseStep 6768697 = 5076523) B5076523
theorem B20334725 : Blo 936583 20334725 := bstep (se 4 (by rfl) ⟨1906380, by rfl⟩ : syracuseStep 20334725 = 3812761) B3812761
theorem B2115755 : Blo 936583 2115755 := bstep (se 1 (by rfl) ⟨1586816, by rfl⟩ : syracuseStep 2115755 = 3173633) B3173633
theorem B9030041 : Blo 936583 9030041 := bstep (se 2 (by rfl) ⟨3386265, by rfl⟩ : syracuseStep 9030041 = 6772531) B6772531
theorem B1690121 : Blo 936583 1690121 := bstep (se 2 (by rfl) ⟨633795, by rfl⟩ : syracuseStep 1690121 = 1267591) B1267591
theorem B4016699 : Blo 936583 4016699 := bstep (se 1 (by rfl) ⟨3012524, by rfl⟩ : syracuseStep 4016699 = 6025049) B6025049
theorem B936623 : Blo 936583 936623 := bstep (se 1 (by rfl) ⟨702467, by rfl⟩ : syracuseStep 936623 = 1404935) B1404935
theorem B936647 : Blo 936583 936647 := bstep (se 1 (by rfl) ⟨702485, by rfl⟩ : syracuseStep 936647 = 1404971) B1404971
theorem B2116295 : Blo 936583 2116295 := bstep (se 1 (by rfl) ⟨1587221, by rfl⟩ : syracuseStep 2116295 = 3174443) B3174443
theorem B3001043 : Blo 936583 3001043 := bstep (se 1 (by rfl) ⟨2250782, by rfl⟩ : syracuseStep 3001043 = 4501565) B4501565
theorem B936667 : Blo 936583 936667 := bstep (se 1 (by rfl) ⟨702500, by rfl⟩ : syracuseStep 936667 = 1405001) B1405001
theorem B936743 : Blo 936583 936743 := bstep (se 1 (by rfl) ⟨702557, by rfl⟩ : syracuseStep 936743 = 1405115) B1405115
theorem B936783 : Blo 936583 936783 := bstep (se 1 (by rfl) ⟨702587, by rfl⟩ : syracuseStep 936783 = 1405175) B1405175
theorem B936799 : Blo 936583 936799 := bstep (se 1 (by rfl) ⟨702599, by rfl⟩ : syracuseStep 936799 = 1405199) B1405199
theorem B3165047 : Blo 936583 3165047 := bstep (se 1 (by rfl) ⟨2373785, by rfl⟩ : syracuseStep 3165047 = 4747571) B4747571
theorem B936827 : Blo 936583 936827 := bstep (se 1 (by rfl) ⟨702620, by rfl⟩ : syracuseStep 936827 = 1405241) B1405241
theorem B936879 : Blo 936583 936879 := bstep (se 1 (by rfl) ⟨702659, by rfl⟩ : syracuseStep 936879 = 1405319) B1405319
theorem B936903 : Blo 936583 936903 := bstep (se 1 (by rfl) ⟨702677, by rfl⟩ : syracuseStep 936903 = 1405355) B1405355
theorem B936923 : Blo 936583 936923 := bstep (se 1 (by rfl) ⟨702692, by rfl⟩ : syracuseStep 936923 = 1405385) B1405385
theorem B3558401 : Blo 936583 3558401 := bstep (se 2 (by rfl) ⟨1334400, by rfl⟩ : syracuseStep 3558401 = 2668801) B2668801
theorem B936999 : Blo 936583 936999 := bstep (se 1 (by rfl) ⟨702749, by rfl⟩ : syracuseStep 936999 = 1405499) B1405499
theorem B937039 : Blo 936583 937039 := bstep (se 1 (by rfl) ⟨702779, by rfl⟩ : syracuseStep 937039 = 1405559) B1405559
theorem B3165263 : Blo 936583 3165263 := bstep (se 1 (by rfl) ⟨2373947, by rfl⟩ : syracuseStep 3165263 = 4747895) B4747895
theorem B937055 : Blo 936583 937055 := bstep (se 1 (by rfl) ⟨702791, by rfl⟩ : syracuseStep 937055 = 1405583) B1405583
theorem B937083 : Blo 936583 937083 := bstep (se 1 (by rfl) ⟨702812, by rfl⟩ : syracuseStep 937083 = 1405625) B1405625
theorem B937135 : Blo 936583 937135 := bstep (se 1 (by rfl) ⟨702851, by rfl⟩ : syracuseStep 937135 = 1405703) B1405703
theorem B937159 : Blo 936583 937159 := bstep (se 1 (by rfl) ⟨702869, by rfl⟩ : syracuseStep 937159 = 1405739) B1405739
theorem B937179 : Blo 936583 937179 := bstep (se 1 (by rfl) ⟨702884, by rfl⟩ : syracuseStep 937179 = 1405769) B1405769
theorem B937255 : Blo 936583 937255 := bstep (se 1 (by rfl) ⟨702941, by rfl⟩ : syracuseStep 937255 = 1405883) B1405883
theorem B937295 : Blo 936583 937295 := bstep (se 1 (by rfl) ⟨702971, by rfl⟩ : syracuseStep 937295 = 1405943) B1405943
theorem B937311 : Blo 936583 937311 := bstep (se 1 (by rfl) ⟨702983, by rfl⟩ : syracuseStep 937311 = 1405967) B1405967
theorem B937339 : Blo 936583 937339 := bstep (se 1 (by rfl) ⟨703004, by rfl⟩ : syracuseStep 937339 = 1406009) B1406009
theorem B2674063 : Blo 936583 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B937391 : Blo 936583 937391 := bstep (se 1 (by rfl) ⟨703043, by rfl⟩ : syracuseStep 937391 = 1406087) B1406087
theorem B937415 : Blo 936583 937415 := bstep (se 1 (by rfl) ⟨703061, by rfl⟩ : syracuseStep 937415 = 1406123) B1406123
theorem B3165641 : Blo 936583 3165641 := bstep (se 2 (by rfl) ⟨1187115, by rfl⟩ : syracuseStep 3165641 = 2374231) B2374231
theorem B937435 : Blo 936583 937435 := bstep (se 1 (by rfl) ⟨703076, by rfl⟩ : syracuseStep 937435 = 1406153) B1406153
theorem B937511 : Blo 936583 937511 := bstep (se 1 (by rfl) ⟨703133, by rfl⟩ : syracuseStep 937511 = 1406267) B1406267
theorem B14077505 : Blo 936583 14077505 := bstep (se 2 (by rfl) ⟨5279064, by rfl⟩ : syracuseStep 14077505 = 10558129) B10558129
theorem B937551 : Blo 936583 937551 := bstep (se 1 (by rfl) ⟨703163, by rfl⟩ : syracuseStep 937551 = 1406327) B1406327
theorem B937567 : Blo 936583 937567 := bstep (se 1 (by rfl) ⟨703175, by rfl⟩ : syracuseStep 937567 = 1406351) B1406351
theorem B937595 : Blo 936583 937595 := bstep (se 1 (by rfl) ⟨703196, by rfl⟩ : syracuseStep 937595 = 1406393) B1406393
theorem B937647 : Blo 936583 937647 := bstep (se 1 (by rfl) ⟨703235, by rfl⟩ : syracuseStep 937647 = 1406471) B1406471
theorem B937671 : Blo 936583 937671 := bstep (se 1 (by rfl) ⟨703253, by rfl⟩ : syracuseStep 937671 = 1406507) B1406507
theorem B5492423 : Blo 936583 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B3165911 : Blo 936583 3165911 := bstep (se 1 (by rfl) ⟨2374433, by rfl⟩ : syracuseStep 3165911 = 4748867) B4748867
theorem B937691 : Blo 936583 937691 := bstep (se 1 (by rfl) ⟨703268, by rfl⟩ : syracuseStep 937691 = 1406537) B1406537
theorem B8015597 : Blo 936583 8015597 := bstep (se 3 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 8015597 = 3005849) B3005849
theorem B937767 : Blo 936583 937767 := bstep (se 1 (by rfl) ⟨703325, by rfl⟩ : syracuseStep 937767 = 1406651) B1406651
theorem B937807 : Blo 936583 937807 := bstep (se 1 (by rfl) ⟨703355, by rfl⟩ : syracuseStep 937807 = 1406711) B1406711
theorem B937823 : Blo 936583 937823 := bstep (se 1 (by rfl) ⟨703367, by rfl⟩ : syracuseStep 937823 = 1406735) B1406735
theorem B937851 : Blo 936583 937851 := bstep (se 1 (by rfl) ⟨703388, by rfl⟩ : syracuseStep 937851 = 1406777) B1406777
theorem B3002273 : Blo 936583 3002273 := bstep (se 2 (by rfl) ⟨1125852, by rfl⟩ : syracuseStep 3002273 = 2251705) B2251705
theorem B937903 : Blo 936583 937903 := bstep (se 1 (by rfl) ⟨703427, by rfl⟩ : syracuseStep 937903 = 1406855) B1406855
theorem B3166127 : Blo 936583 3166127 := bstep (se 1 (by rfl) ⟨2374595, by rfl⟩ : syracuseStep 3166127 = 4749191) B4749191
theorem B937927 : Blo 936583 937927 := bstep (se 1 (by rfl) ⟨703445, by rfl⟩ : syracuseStep 937927 = 1406891) B1406891
theorem B937947 : Blo 936583 937947 := bstep (se 1 (by rfl) ⟨703460, by rfl⟩ : syracuseStep 937947 = 1406921) B1406921
theorem B938023 : Blo 936583 938023 := bstep (se 1 (by rfl) ⟨703517, by rfl⟩ : syracuseStep 938023 = 1407035) B1407035
theorem B938063 : Blo 936583 938063 := bstep (se 1 (by rfl) ⟨703547, by rfl⟩ : syracuseStep 938063 = 1407095) B1407095
theorem B6017105 : Blo 936583 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B938079 : Blo 936583 938079 := bstep (se 1 (by rfl) ⟨703559, by rfl⟩ : syracuseStep 938079 = 1407119) B1407119
theorem B938107 : Blo 936583 938107 := bstep (se 1 (by rfl) ⟨703580, by rfl⟩ : syracuseStep 938107 = 1407161) B1407161
theorem B938159 : Blo 936583 938159 := bstep (se 1 (by rfl) ⟨703619, by rfl⟩ : syracuseStep 938159 = 1407239) B1407239
theorem B938183 : Blo 936583 938183 := bstep (se 1 (by rfl) ⟨703637, by rfl⟩ : syracuseStep 938183 = 1407275) B1407275
theorem B938203 : Blo 936583 938203 := bstep (se 1 (by rfl) ⟨703652, by rfl⟩ : syracuseStep 938203 = 1407305) B1407305
theorem B938279 : Blo 936583 938279 := bstep (se 1 (by rfl) ⟨703709, by rfl⟩ : syracuseStep 938279 = 1407419) B1407419
theorem B938319 : Blo 936583 938319 := bstep (se 1 (by rfl) ⟨703739, by rfl⟩ : syracuseStep 938319 = 1407479) B1407479
theorem B938335 : Blo 936583 938335 := bstep (se 1 (by rfl) ⟨703751, by rfl⟩ : syracuseStep 938335 = 1407503) B1407503
theorem B938363 : Blo 936583 938363 := bstep (se 1 (by rfl) ⟨703772, by rfl⟩ : syracuseStep 938363 = 1407545) B1407545
theorem B2380175 : Blo 936583 2380175 := bstep (se 1 (by rfl) ⟨1785131, by rfl⟩ : syracuseStep 2380175 = 3570263) B3570263
theorem B938415 : Blo 936583 938415 := bstep (se 1 (by rfl) ⟨703811, by rfl⟩ : syracuseStep 938415 = 1407623) B1407623
theorem B938439 : Blo 936583 938439 := bstep (se 1 (by rfl) ⟨703829, by rfl⟩ : syracuseStep 938439 = 1407659) B1407659
theorem B938459 : Blo 936583 938459 := bstep (se 1 (by rfl) ⟨703844, by rfl⟩ : syracuseStep 938459 = 1407689) B1407689
theorem B5067245 : Blo 936583 5067245 := bstep (se 3 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 5067245 = 1900217) B1900217
theorem B938535 : Blo 936583 938535 := bstep (se 1 (by rfl) ⟨703901, by rfl⟩ : syracuseStep 938535 = 1407803) B1407803
theorem B938575 : Blo 936583 938575 := bstep (se 1 (by rfl) ⟨703931, by rfl⟩ : syracuseStep 938575 = 1407863) B1407863
theorem B938591 : Blo 936583 938591 := bstep (se 1 (by rfl) ⟨703943, by rfl⟩ : syracuseStep 938591 = 1407887) B1407887
theorem B938619 : Blo 936583 938619 := bstep (se 1 (by rfl) ⟨703964, by rfl⟩ : syracuseStep 938619 = 1407929) B1407929
theorem B3560071 : Blo 936583 3560071 := bstep (se 1 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 3560071 = 5340107) B5340107
theorem B2675339 : Blo 936583 2675339 := bstep (se 1 (by rfl) ⟨2006504, by rfl⟩ : syracuseStep 2675339 = 4013009) B4013009
theorem B938671 : Blo 936583 938671 := bstep (se 1 (by rfl) ⟨704003, by rfl⟩ : syracuseStep 938671 = 1408007) B1408007
theorem B938695 : Blo 936583 938695 := bstep (se 1 (by rfl) ⟨704021, by rfl⟩ : syracuseStep 938695 = 1408043) B1408043
theorem B6410963 : Blo 936583 6410963 := bstep (se 1 (by rfl) ⟨4808222, by rfl⟩ : syracuseStep 6410963 = 9616445) B9616445
theorem B2380499 : Blo 936583 2380499 := bstep (se 1 (by rfl) ⟨1785374, by rfl⟩ : syracuseStep 2380499 = 3570749) B3570749
theorem B938715 : Blo 936583 938715 := bstep (se 1 (by rfl) ⟨704036, by rfl⟩ : syracuseStep 938715 = 1408073) B1408073
theorem B938791 : Blo 936583 938791 := bstep (se 1 (by rfl) ⟨704093, by rfl⟩ : syracuseStep 938791 = 1408187) B1408187
theorem B938831 : Blo 936583 938831 := bstep (se 1 (by rfl) ⟨704123, by rfl⟩ : syracuseStep 938831 = 1408247) B1408247
theorem B938847 : Blo 936583 938847 := bstep (se 1 (by rfl) ⟨704135, by rfl⟩ : syracuseStep 938847 = 1408271) B1408271
theorem B938875 : Blo 936583 938875 := bstep (se 1 (by rfl) ⟨704156, by rfl⟩ : syracuseStep 938875 = 1408313) B1408313
theorem B7132049 : Blo 936583 7132049 := bstep (se 2 (by rfl) ⟨2674518, by rfl⟩ : syracuseStep 7132049 = 5349037) B5349037
theorem B1266607 : Blo 936583 1266607 := bstep (se 1 (by rfl) ⟨949955, by rfl⟩ : syracuseStep 1266607 = 1899911) B1899911
theorem B938927 : Blo 936583 938927 := bstep (se 1 (by rfl) ⟨704195, by rfl⟩ : syracuseStep 938927 = 1408391) B1408391
theorem B3560375 : Blo 936583 3560375 := bstep (se 1 (by rfl) ⟨2670281, by rfl⟩ : syracuseStep 3560375 = 5340563) B5340563
theorem B938951 : Blo 936583 938951 := bstep (se 1 (by rfl) ⟨704213, by rfl⟩ : syracuseStep 938951 = 1408427) B1408427
theorem B938971 : Blo 936583 938971 := bstep (se 1 (by rfl) ⟨704228, by rfl⟩ : syracuseStep 938971 = 1408457) B1408457
theorem B939047 : Blo 936583 939047 := bstep (se 1 (by rfl) ⟨704285, by rfl⟩ : syracuseStep 939047 = 1408571) B1408571
theorem B939087 : Blo 936583 939087 := bstep (se 1 (by rfl) ⟨704315, by rfl⟩ : syracuseStep 939087 = 1408631) B1408631
theorem B939103 : Blo 936583 939103 := bstep (se 1 (by rfl) ⟨704327, by rfl⟩ : syracuseStep 939103 = 1408655) B1408655
theorem B939131 : Blo 936583 939131 := bstep (se 1 (by rfl) ⟨704348, by rfl⟩ : syracuseStep 939131 = 1408697) B1408697
theorem B939183 : Blo 936583 939183 := bstep (se 1 (by rfl) ⟨704387, by rfl⟩ : syracuseStep 939183 = 1408775) B1408775
theorem B1266887 : Blo 936583 1266887 := bstep (se 1 (by rfl) ⟨950165, by rfl⟩ : syracuseStep 1266887 = 1900331) B1900331
theorem B939207 : Blo 936583 939207 := bstep (se 1 (by rfl) ⟨704405, by rfl⟩ : syracuseStep 939207 = 1408811) B1408811
theorem B939227 : Blo 936583 939227 := bstep (se 1 (by rfl) ⟨704420, by rfl⟩ : syracuseStep 939227 = 1408841) B1408841
theorem B939303 : Blo 936583 939303 := bstep (se 1 (by rfl) ⟨704477, by rfl⟩ : syracuseStep 939303 = 1408955) B1408955
theorem B939343 : Blo 936583 939343 := bstep (se 1 (by rfl) ⟨704507, by rfl⟩ : syracuseStep 939343 = 1409015) B1409015
theorem B939359 : Blo 936583 939359 := bstep (se 1 (by rfl) ⟨704519, by rfl⟩ : syracuseStep 939359 = 1409039) B1409039
theorem B939387 : Blo 936583 939387 := bstep (se 1 (by rfl) ⟨704540, by rfl⟩ : syracuseStep 939387 = 1409081) B1409081
theorem B939439 : Blo 936583 939439 := bstep (se 1 (by rfl) ⟨704579, by rfl⟩ : syracuseStep 939439 = 1409159) B1409159
theorem B939463 : Blo 936583 939463 := bstep (se 1 (by rfl) ⟨704597, by rfl⟩ : syracuseStep 939463 = 1409195) B1409195
theorem B939483 : Blo 936583 939483 := bstep (se 1 (by rfl) ⟨704612, by rfl⟩ : syracuseStep 939483 = 1409225) B1409225
theorem B3659251 : Blo 936583 3659251 := bstep (se 1 (by rfl) ⟨2744438, by rfl⟩ : syracuseStep 3659251 = 5488877) B5488877
theorem B3003913 : Blo 936583 3003913 := bstep (se 2 (by rfl) ⟨1126467, by rfl⟩ : syracuseStep 3003913 = 2252935) B2252935
theorem B5068327 : Blo 936583 5068327 := bstep (se 1 (by rfl) ⟨3801245, by rfl⟩ : syracuseStep 5068327 = 7602491) B7602491
theorem B939559 : Blo 936583 939559 := bstep (se 1 (by rfl) ⟨704669, by rfl⟩ : syracuseStep 939559 = 1409339) B1409339
theorem B939599 : Blo 936583 939599 := bstep (se 1 (by rfl) ⟨704699, by rfl⟩ : syracuseStep 939599 = 1409399) B1409399
theorem B6411863 : Blo 936583 6411863 := bstep (se 1 (by rfl) ⟨4808897, by rfl⟩ : syracuseStep 6411863 = 9617795) B9617795
theorem B939615 : Blo 936583 939615 := bstep (se 1 (by rfl) ⟨704711, by rfl⟩ : syracuseStep 939615 = 1409423) B1409423
theorem B939643 : Blo 936583 939643 := bstep (se 1 (by rfl) ⟨704732, by rfl⟩ : syracuseStep 939643 = 1409465) B1409465
theorem B939695 : Blo 936583 939695 := bstep (se 1 (by rfl) ⟨704771, by rfl⟩ : syracuseStep 939695 = 1409543) B1409543
theorem B939719 : Blo 936583 939719 := bstep (se 1 (by rfl) ⟨704789, by rfl⟩ : syracuseStep 939719 = 1409579) B1409579
theorem B4511447 : Blo 936583 4511447 := bstep (se 1 (by rfl) ⟨3383585, by rfl⟩ : syracuseStep 4511447 = 6767171) B6767171
theorem B939739 : Blo 936583 939739 := bstep (se 1 (by rfl) ⟨704804, by rfl⟩ : syracuseStep 939739 = 1409609) B1409609
theorem B939815 : Blo 936583 939815 := bstep (se 1 (by rfl) ⟨704861, by rfl⟩ : syracuseStep 939815 = 1409723) B1409723
theorem B6084395 : Blo 936583 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B939855 : Blo 936583 939855 := bstep (se 1 (by rfl) ⟨704891, by rfl⟩ : syracuseStep 939855 = 1409783) B1409783
theorem B939871 : Blo 936583 939871 := bstep (se 1 (by rfl) ⟨704903, by rfl⟩ : syracuseStep 939871 = 1409807) B1409807
theorem B30496621 : Blo 936583 30496621 := bstep (se 3 (by rfl) ⟨5718116, by rfl⟩ : syracuseStep 30496621 = 11436233) B11436233
theorem B939899 : Blo 936583 939899 := bstep (se 1 (by rfl) ⟨704924, by rfl⟩ : syracuseStep 939899 = 1409849) B1409849
theorem B939951 : Blo 936583 939951 := bstep (se 1 (by rfl) ⟨704963, by rfl⟩ : syracuseStep 939951 = 1409927) B1409927
theorem B5789627 : Blo 936583 5789627 := bstep (se 1 (by rfl) ⟨4342220, by rfl⟩ : syracuseStep 5789627 = 8684441) B8684441
theorem B939975 : Blo 936583 939975 := bstep (se 1 (by rfl) ⟨704981, by rfl⟩ : syracuseStep 939975 = 1409963) B1409963
theorem B939995 : Blo 936583 939995 := bstep (se 1 (by rfl) ⟨704996, by rfl⟩ : syracuseStep 939995 = 1409993) B1409993
theorem B940071 : Blo 936583 940071 := bstep (se 1 (by rfl) ⟨705053, by rfl⟩ : syracuseStep 940071 = 1410107) B1410107
theorem B3561529 : Blo 936583 3561529 := bstep (se 2 (by rfl) ⟨1335573, by rfl⟩ : syracuseStep 3561529 = 2671147) B2671147
theorem B940111 : Blo 936583 940111 := bstep (se 1 (by rfl) ⟨705083, by rfl⟩ : syracuseStep 940111 = 1410167) B1410167
theorem B940127 : Blo 936583 940127 := bstep (se 1 (by rfl) ⟨705095, by rfl⟩ : syracuseStep 940127 = 1410191) B1410191
theorem B940155 : Blo 936583 940155 := bstep (se 1 (by rfl) ⟨705116, by rfl⟩ : syracuseStep 940155 = 1410233) B1410233
theorem B940207 : Blo 936583 940207 := bstep (se 1 (by rfl) ⟨705155, by rfl⟩ : syracuseStep 940207 = 1410311) B1410311
theorem B940231 : Blo 936583 940231 := bstep (se 1 (by rfl) ⟨705173, by rfl⟩ : syracuseStep 940231 = 1410347) B1410347
theorem B940251 : Blo 936583 940251 := bstep (se 1 (by rfl) ⟨705188, by rfl⟩ : syracuseStep 940251 = 1410377) B1410377
theorem B3168503 : Blo 936583 3168503 := bstep (se 1 (by rfl) ⟨2376377, by rfl⟩ : syracuseStep 3168503 = 4752755) B4752755
theorem B940327 : Blo 936583 940327 := bstep (se 1 (by rfl) ⟨705245, by rfl⟩ : syracuseStep 940327 = 1410491) B1410491
theorem B3004733 : Blo 936583 3004733 := bstep (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) B1126775
theorem B940367 : Blo 936583 940367 := bstep (se 1 (by rfl) ⟨705275, by rfl⟩ : syracuseStep 940367 = 1410551) B1410551
theorem B940383 : Blo 936583 940383 := bstep (se 1 (by rfl) ⟨705287, by rfl⟩ : syracuseStep 940383 = 1410575) B1410575
theorem B3561833 : Blo 936583 3561833 := bstep (se 2 (by rfl) ⟨1335687, by rfl⟩ : syracuseStep 3561833 = 2671375) B2671375
theorem B940411 : Blo 936583 940411 := bstep (se 1 (by rfl) ⟨705308, by rfl⟩ : syracuseStep 940411 = 1410617) B1410617
theorem B940463 : Blo 936583 940463 := bstep (se 1 (by rfl) ⟨705347, by rfl⟩ : syracuseStep 940463 = 1410695) B1410695
theorem B940487 : Blo 936583 940487 := bstep (se 1 (by rfl) ⟨705365, by rfl⟩ : syracuseStep 940487 = 1410731) B1410731
theorem B1694171 : Blo 936583 1694171 := bstep (se 1 (by rfl) ⟨1270628, by rfl⟩ : syracuseStep 1694171 = 2541257) B2541257
theorem B940507 : Blo 936583 940507 := bstep (se 1 (by rfl) ⟨705380, by rfl⟩ : syracuseStep 940507 = 1410761) B1410761
theorem B940583 : Blo 936583 940583 := bstep (se 1 (by rfl) ⟨705437, by rfl⟩ : syracuseStep 940583 = 1410875) B1410875
theorem B3168827 : Blo 936583 3168827 := bstep (se 1 (by rfl) ⟨2376620, by rfl⟩ : syracuseStep 3168827 = 4753241) B4753241
theorem B12049073 : Blo 936583 12049073 := bstep (se 2 (by rfl) ⟨4518402, by rfl⟩ : syracuseStep 12049073 = 9036805) B9036805
theorem B2251513 : Blo 936583 2251513 := bstep (se 2 (by rfl) ⟨844317, by rfl⟩ : syracuseStep 2251513 = 1688635) B1688635
theorem B3169097 : Blo 936583 3169097 := bstep (se 2 (by rfl) ⟨1188411, by rfl⟩ : syracuseStep 3169097 = 2376823) B2376823
theorem B4742063 : Blo 936583 4742063 := bstep (se 1 (by rfl) ⟨3556547, by rfl⟩ : syracuseStep 4742063 = 7113095) B7113095
theorem B12016835 : Blo 936583 12016835 := bstep (se 1 (by rfl) ⟨9012626, by rfl⟩ : syracuseStep 12016835 = 18025253) B18025253
theorem B7134479 : Blo 936583 7134479 := bstep (se 1 (by rfl) ⟨5350859, by rfl⟩ : syracuseStep 7134479 = 10701719) B10701719
theorem B1629623 : Blo 936583 1629623 := bstep (se 1 (by rfl) ⟨1222217, by rfl⟩ : syracuseStep 1629623 = 2444435) B2444435
theorem B9035387 : Blo 936583 9035387 := bstep (se 1 (by rfl) ⟨6776540, by rfl⟩ : syracuseStep 9035387 = 13553081) B13553081
theorem B9002785 : Blo 936583 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B3170231 : Blo 936583 3170231 := bstep (se 1 (by rfl) ⟨2377673, by rfl⟩ : syracuseStep 3170231 = 4755347) B4755347
theorem B2252879 : Blo 936583 2252879 := bstep (se 1 (by rfl) ⟨1689659, by rfl⟩ : syracuseStep 2252879 = 3379319) B3379319
theorem B4513907 : Blo 936583 4513907 := bstep (se 1 (by rfl) ⟨3385430, by rfl⟩ : syracuseStep 4513907 = 6770861) B6770861
theorem B7627009 : Blo 936583 7627009 := bstep (se 2 (by rfl) ⟨2860128, by rfl⟩ : syracuseStep 7627009 = 5720257) B5720257
theorem B4514059 : Blo 936583 4514059 := bstep (se 1 (by rfl) ⟨3385544, by rfl⟩ : syracuseStep 4514059 = 6771089) B6771089
theorem B3170825 : Blo 936583 3170825 := bstep (se 2 (by rfl) ⟨1189059, by rfl⟩ : syracuseStep 3170825 = 2378119) B2378119
theorem B1335847 : Blo 936583 1335847 := bstep (se 1 (by rfl) ⟨1001885, by rfl⟩ : syracuseStep 1335847 = 2003771) B2003771
theorem B3171689 : Blo 936583 3171689 := bstep (se 2 (by rfl) ⟨1189383, by rfl⟩ : syracuseStep 3171689 = 2378767) B2378767
theorem B1271147 : Blo 936583 1271147 := bstep (se 1 (by rfl) ⟨953360, by rfl⟩ : syracuseStep 1271147 = 1906721) B1906721
theorem B1500599 : Blo 936583 1500599 := bstep (se 1 (by rfl) ⟨1125449, by rfl⟩ : syracuseStep 1500599 = 2250899) B2250899
theorem B3172283 : Blo 936583 3172283 := bstep (se 1 (by rfl) ⟨2379212, by rfl⟩ : syracuseStep 3172283 = 4758425) B4758425
theorem B7137395 : Blo 936583 7137395 := bstep (se 1 (by rfl) ⟨5353046, by rfl⟩ : syracuseStep 7137395 = 10706093) B10706093
theorem B3565721 : Blo 936583 3565721 := bstep (se 2 (by rfl) ⟨1337145, by rfl⟩ : syracuseStep 3565721 = 2674291) B2674291
theorem B1501355 : Blo 936583 1501355 := bstep (se 1 (by rfl) ⟨1126016, by rfl⟩ : syracuseStep 1501355 = 2252033) B2252033
theorem B6777377 : Blo 936583 6777377 := bstep (se 2 (by rfl) ⟨2541516, by rfl⟩ : syracuseStep 6777377 = 5083033) B5083033
theorem B3566177 : Blo 936583 3566177 := bstep (se 2 (by rfl) ⟨1337316, by rfl⟩ : syracuseStep 3566177 = 2674633) B2674633
theorem B5335915 : Blo 936583 5335915 := bstep (se 1 (by rfl) ⟨4001936, by rfl⟩ : syracuseStep 5335915 = 8003873) B8003873
theorem B17099761 : Blo 936583 17099761 := bstep (se 2 (by rfl) ⟨6412410, by rfl⟩ : syracuseStep 17099761 = 12824821) B12824821
theorem B3009707 : Blo 936583 3009707 := bstep (se 1 (by rfl) ⟨2257280, by rfl⟩ : syracuseStep 3009707 = 4514561) B4514561
theorem B1502777 : Blo 936583 1502777 := bstep (se 2 (by rfl) ⟨563541, by rfl⟩ : syracuseStep 1502777 = 1127083) B1127083
theorem B3174011 : Blo 936583 3174011 := bstep (se 1 (by rfl) ⟨2380508, by rfl⟩ : syracuseStep 3174011 = 4761017) B4761017
theorem B3174173 : Blo 936583 3174173 := bstep (se 3 (by rfl) ⟨595157, by rfl⟩ : syracuseStep 3174173 = 1190315) B1190315
theorem B3567635 : Blo 936583 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B1405007 : Blo 936583 1405007 := bstep (se 1 (by rfl) ⟨1053755, by rfl⟩ : syracuseStep 1405007 = 2107511) B2107511
theorem B1405127 : Blo 936583 1405127 := bstep (se 1 (by rfl) ⟨1053845, by rfl⟩ : syracuseStep 1405127 = 2107691) B2107691
theorem B5501245 : Blo 936583 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B1405289 : Blo 936583 1405289 := bstep (se 2 (by rfl) ⟨526983, by rfl⟩ : syracuseStep 1405289 = 1053967) B1053967
theorem B1405367 : Blo 936583 1405367 := bstep (se 1 (by rfl) ⟨1054025, by rfl⟩ : syracuseStep 1405367 = 2108051) B2108051
theorem B1405403 : Blo 936583 1405403 := bstep (se 1 (by rfl) ⟨1054052, by rfl⟩ : syracuseStep 1405403 = 2108105) B2108105
theorem B1503751 : Blo 936583 1503751 := bstep (se 1 (by rfl) ⟨1127813, by rfl⟩ : syracuseStep 1503751 = 2255627) B2255627
theorem B3011219 : Blo 936583 3011219 := bstep (se 1 (by rfl) ⟨2258414, by rfl⟩ : syracuseStep 3011219 = 4516829) B4516829
theorem B3011489 : Blo 936583 3011489 := bstep (se 2 (by rfl) ⟨1129308, by rfl⟩ : syracuseStep 3011489 = 2258617) B2258617
theorem B1405871 : Blo 936583 1405871 := bstep (se 1 (by rfl) ⟨1054403, by rfl⟩ : syracuseStep 1405871 = 2108807) B2108807
theorem B1504187 : Blo 936583 1504187 := bstep (se 1 (by rfl) ⟨1128140, by rfl⟩ : syracuseStep 1504187 = 2256281) B2256281
theorem B1405961 : Blo 936583 1405961 := bstep (se 2 (by rfl) ⟨527235, by rfl⟩ : syracuseStep 1405961 = 1054471) B1054471
theorem B1405991 : Blo 936583 1405991 := bstep (se 1 (by rfl) ⟨1054493, by rfl⟩ : syracuseStep 1405991 = 2108987) B2108987
theorem B12022829 : Blo 936583 12022829 := bstep (se 3 (by rfl) ⟨2254280, by rfl⟩ : syracuseStep 12022829 = 4508561) B4508561
theorem B1406075 : Blo 936583 1406075 := bstep (se 1 (by rfl) ⟨1054556, by rfl⟩ : syracuseStep 1406075 = 2109113) B2109113
theorem B1504379 : Blo 936583 1504379 := bstep (se 1 (by rfl) ⟨1128284, by rfl⟩ : syracuseStep 1504379 = 2256569) B2256569
theorem B1406201 : Blo 936583 1406201 := bstep (se 2 (by rfl) ⟨527325, by rfl⟩ : syracuseStep 1406201 = 1054651) B1054651
theorem B3798359 : Blo 936583 3798359 := bstep (se 1 (by rfl) ⟨2848769, by rfl⟩ : syracuseStep 3798359 = 5697539) B5697539
theorem B1602911 : Blo 936583 1602911 := bstep (se 1 (by rfl) ⟨1202183, by rfl⟩ : syracuseStep 1602911 = 2404367) B2404367
theorem B1406303 : Blo 936583 1406303 := bstep (se 1 (by rfl) ⟨1054727, by rfl⟩ : syracuseStep 1406303 = 2109455) B2109455
theorem B1406315 : Blo 936583 1406315 := bstep (se 1 (by rfl) ⟨1054736, by rfl⟩ : syracuseStep 1406315 = 2109473) B2109473
theorem B12187027 : Blo 936583 12187027 := bstep (se 1 (by rfl) ⟨9140270, by rfl⟩ : syracuseStep 12187027 = 18280541) B18280541
theorem B2258471 : Blo 936583 2258471 := bstep (se 1 (by rfl) ⟨1693853, by rfl⟩ : syracuseStep 2258471 = 3387707) B3387707
theorem B1406543 : Blo 936583 1406543 := bstep (se 1 (by rfl) ⟨1054907, by rfl⟩ : syracuseStep 1406543 = 2109815) B2109815
theorem B3569291 : Blo 936583 3569291 := bstep (se 1 (by rfl) ⟨2676968, by rfl⟩ : syracuseStep 3569291 = 5353937) B5353937
theorem B1406663 : Blo 936583 1406663 := bstep (se 1 (by rfl) ⟨1054997, by rfl⟩ : syracuseStep 1406663 = 2109995) B2109995
theorem B1406825 : Blo 936583 1406825 := bstep (se 2 (by rfl) ⟨527559, by rfl⟩ : syracuseStep 1406825 = 1055119) B1055119
theorem B1406903 : Blo 936583 1406903 := bstep (se 1 (by rfl) ⟨1055177, by rfl⟩ : syracuseStep 1406903 = 2110355) B2110355
theorem B2258875 : Blo 936583 2258875 := bstep (se 1 (by rfl) ⟨1694156, by rfl⟩ : syracuseStep 2258875 = 3388313) B3388313
theorem B1406939 : Blo 936583 1406939 := bstep (se 1 (by rfl) ⟨1055204, by rfl⟩ : syracuseStep 1406939 = 2110409) B2110409
theorem B1407407 : Blo 936583 1407407 := bstep (se 1 (by rfl) ⟨1055555, by rfl⟩ : syracuseStep 1407407 = 2111111) B2111111
theorem B1407497 : Blo 936583 1407497 := bstep (se 2 (by rfl) ⟨527811, by rfl⟩ : syracuseStep 1407497 = 1055623) B1055623
theorem B1505801 : Blo 936583 1505801 := bstep (se 2 (by rfl) ⟨564675, by rfl⟩ : syracuseStep 1505801 = 1129351) B1129351
theorem B1407527 : Blo 936583 1407527 := bstep (se 1 (by rfl) ⟨1055645, by rfl⟩ : syracuseStep 1407527 = 2111291) B2111291
theorem B1407611 : Blo 936583 1407611 := bstep (se 1 (by rfl) ⟨1055708, by rfl⟩ : syracuseStep 1407611 = 2111417) B2111417
theorem B1407737 : Blo 936583 1407737 := bstep (se 2 (by rfl) ⟨527901, by rfl⟩ : syracuseStep 1407737 = 1055803) B1055803
theorem B1407839 : Blo 936583 1407839 := bstep (se 1 (by rfl) ⟨1055879, by rfl⟩ : syracuseStep 1407839 = 2111759) B2111759
theorem B1407851 : Blo 936583 1407851 := bstep (se 1 (by rfl) ⟨1055888, by rfl⟩ : syracuseStep 1407851 = 2111777) B2111777
theorem B3570551 : Blo 936583 3570551 := bstep (se 1 (by rfl) ⟨2677913, by rfl⟩ : syracuseStep 3570551 = 5355827) B5355827
theorem B6421477 : Blo 936583 6421477 := bstep (se 4 (by rfl) ⟨602013, by rfl⟩ : syracuseStep 6421477 = 1204027) B1204027
theorem B3046457 : Blo 936583 3046457 := bstep (se 2 (by rfl) ⟨1142421, by rfl⟩ : syracuseStep 3046457 = 2284843) B2284843
theorem B1408079 : Blo 936583 1408079 := bstep (se 1 (by rfl) ⟨1056059, by rfl⟩ : syracuseStep 1408079 = 2112119) B2112119
theorem B1408199 : Blo 936583 1408199 := bstep (se 1 (by rfl) ⟨1056149, by rfl⟩ : syracuseStep 1408199 = 2112299) B2112299
theorem B8027383 : Blo 936583 8027383 := bstep (se 1 (by rfl) ⟨6020537, by rfl⟩ : syracuseStep 8027383 = 12041075) B12041075
theorem B1408361 : Blo 936583 1408361 := bstep (se 2 (by rfl) ⟨528135, by rfl⟩ : syracuseStep 1408361 = 1056271) B1056271
theorem B1408439 : Blo 936583 1408439 := bstep (se 1 (by rfl) ⟨1056329, by rfl⟩ : syracuseStep 1408439 = 2112659) B2112659
theorem B4750811 : Blo 936583 4750811 := bstep (se 1 (by rfl) ⟨3563108, by rfl⟩ : syracuseStep 4750811 = 7126217) B7126217
theorem B1408475 : Blo 936583 1408475 := bstep (se 1 (by rfl) ⟨1056356, by rfl⟩ : syracuseStep 1408475 = 2112713) B2112713
theorem B1408943 : Blo 936583 1408943 := bstep (se 1 (by rfl) ⟨1056707, by rfl⟩ : syracuseStep 1408943 = 2113415) B2113415
theorem B4751297 : Blo 936583 4751297 := bstep (se 2 (by rfl) ⟨1781736, by rfl⟩ : syracuseStep 4751297 = 3563473) B3563473
theorem B1605595 : Blo 936583 1605595 := bstep (se 1 (by rfl) ⟨1204196, by rfl⟩ : syracuseStep 1605595 = 2408393) B2408393
theorem B1409129 : Blo 936583 1409129 := bstep (se 2 (by rfl) ⟨528423, by rfl⟩ : syracuseStep 1409129 = 1056847) B1056847
theorem B1409447 : Blo 936583 1409447 := bstep (se 1 (by rfl) ⟨1057085, by rfl⟩ : syracuseStep 1409447 = 2114171) B2114171
theorem B1409531 : Blo 936583 1409531 := bstep (se 1 (by rfl) ⟨1057148, by rfl⟩ : syracuseStep 1409531 = 2114297) B2114297
theorem B1409657 : Blo 936583 1409657 := bstep (se 2 (by rfl) ⟨528621, by rfl⟩ : syracuseStep 1409657 = 1057243) B1057243
theorem B1409711 : Blo 936583 1409711 := bstep (se 1 (by rfl) ⟨1057283, by rfl⟩ : syracuseStep 1409711 = 2114567) B2114567
theorem B30835403 : Blo 936583 30835403 := bstep (se 1 (by rfl) ⟨23126552, by rfl⟩ : syracuseStep 30835403 = 46253105) B46253105
theorem B1409759 : Blo 936583 1409759 := bstep (se 1 (by rfl) ⟨1057319, by rfl⟩ : syracuseStep 1409759 = 2114639) B2114639
theorem B3802087 : Blo 936583 3802087 := bstep (se 1 (by rfl) ⟨2851565, by rfl⟩ : syracuseStep 3802087 = 5703131) B5703131
theorem B1410023 : Blo 936583 1410023 := bstep (se 1 (by rfl) ⟨1057517, by rfl⟩ : syracuseStep 1410023 = 2115035) B2115035
theorem B1901711 : Blo 936583 1901711 := bstep (se 1 (by rfl) ⟨1426283, by rfl⟩ : syracuseStep 1901711 = 2852567) B2852567
theorem B1410281 : Blo 936583 1410281 := bstep (se 2 (by rfl) ⟨528855, by rfl⟩ : syracuseStep 1410281 = 1057711) B1057711
theorem B1410335 : Blo 936583 1410335 := bstep (se 1 (by rfl) ⟨1057751, by rfl⟩ : syracuseStep 1410335 = 2115503) B2115503
theorem B1410503 : Blo 936583 1410503 := bstep (se 1 (by rfl) ⟨1057877, by rfl⟩ : syracuseStep 1410503 = 2115755) B2115755
theorem B25691681 : Blo 936583 25691681 := bstep (se 2 (by rfl) ⟨9634380, by rfl⟩ : syracuseStep 25691681 = 19268761) B19268761
theorem B1410857 : Blo 936583 1410857 := bstep (se 2 (by rfl) ⟨529071, by rfl⟩ : syracuseStep 1410857 = 1058143) B1058143
theorem B1410863 : Blo 936583 1410863 := bstep (se 1 (by rfl) ⟨1058147, by rfl⟩ : syracuseStep 1410863 = 2116295) B2116295
theorem B2000695 : Blo 936583 2000695 := bstep (se 1 (by rfl) ⟨1500521, by rfl⟩ : syracuseStep 2000695 = 3001043) B3001043
theorem B10160005 : Blo 936583 10160005 := bstep (se 4 (by rfl) ⟨952500, by rfl⟩ : syracuseStep 10160005 = 1905001) B1905001
theorem B5343731 : Blo 936583 5343731 := bstep (se 1 (by rfl) ⟨4007798, by rfl⟩ : syracuseStep 5343731 = 8015597) B8015597
theorem B2001515 : Blo 936583 2001515 := bstep (se 1 (by rfl) ⟨1501136, by rfl⟩ : syracuseStep 2001515 = 3002273) B3002273
theorem B20581111 : Blo 936583 20581111 := bstep (se 1 (by rfl) ⟨15435833, by rfl⟩ : syracuseStep 20581111 = 30871667) B30871667
theorem B3378365 : Blo 936583 3378365 := bstep (se 3 (by rfl) ⟨633443, by rfl⟩ : syracuseStep 3378365 = 1266887) B1266887
theorem B4754699 : Blo 936583 4754699 := bstep (se 1 (by rfl) ⟨3566024, by rfl⟩ : syracuseStep 4754699 = 7132049) B7132049
theorem B7114553 : Blo 936583 7114553 := bstep (se 2 (by rfl) ⟨2667957, by rfl⟩ : syracuseStep 7114553 = 5335915) B5335915
theorem B4067347 : Blo 936583 4067347 := bstep (se 1 (by rfl) ⟨3050510, by rfl⟩ : syracuseStep 4067347 = 6101021) B6101021
theorem B10817995 : Blo 936583 10817995 := bstep (se 1 (by rfl) ⟨8113496, by rfl⟩ : syracuseStep 10817995 = 16226993) B16226993
theorem B8032715 : Blo 936583 8032715 := bstep (se 1 (by rfl) ⟨6024536, by rfl⟩ : syracuseStep 8032715 = 12049073) B12049073
theorem B1446395 : Blo 936583 1446395 := bstep (se 1 (by rfl) ⟨1084796, by rfl⟩ : syracuseStep 1446395 = 2169593) B2169593
theorem B4002655 : Blo 936583 4002655 := bstep (se 1 (by rfl) ⟨3001991, by rfl⟩ : syracuseStep 4002655 = 6003983) B6003983
theorem B4756319 : Blo 936583 4756319 := bstep (se 1 (by rfl) ⟨3567239, by rfl⟩ : syracuseStep 4756319 = 7134479) B7134479
theorem B6001573 : Blo 936583 6001573 := bstep (se 4 (by rfl) ⟨562647, by rfl⟩ : syracuseStep 6001573 = 1125295) B1125295
theorem B1086415 : Blo 936583 1086415 := bstep (se 1 (by rfl) ⟨814811, by rfl⟩ : syracuseStep 1086415 = 1629623) B1629623
theorem B12030929 : Blo 936583 12030929 := bstep (se 2 (by rfl) ⟨4511598, by rfl⟩ : syracuseStep 12030929 = 9023197) B9023197
theorem B16258295 : Blo 936583 16258295 := bstep (se 1 (by rfl) ⟨12193721, by rfl⟩ : syracuseStep 16258295 = 24387443) B24387443
theorem B1054075 : Blo 936583 1054075 := bstep (se 1 (by rfl) ⟨790556, by rfl⟩ : syracuseStep 1054075 = 1581113) B1581113
theorem B1185455 : Blo 936583 1185455 := bstep (se 1 (by rfl) ⟨889091, by rfl⟩ : syracuseStep 1185455 = 1778183) B1778183
theorem B4003613 : Blo 936583 4003613 := bstep (se 3 (by rfl) ⟨750677, by rfl⟩ : syracuseStep 4003613 = 1501355) B1501355
theorem B1054543 : Blo 936583 1054543 := bstep (se 1 (by rfl) ⟨790907, by rfl⟩ : syracuseStep 1054543 = 1581815) B1581815
theorem B2005001 : Blo 936583 2005001 := bstep (se 2 (by rfl) ⟨751875, by rfl⟩ : syracuseStep 2005001 = 1503751) B1503751
theorem B1054939 : Blo 936583 1054939 := bstep (se 1 (by rfl) ⟨791204, by rfl⟩ : syracuseStep 1054939 = 1582409) B1582409
theorem B1186159 : Blo 936583 1186159 := bstep (se 1 (by rfl) ⟨889619, by rfl⟩ : syracuseStep 1186159 = 1779239) B1779239
theorem B1055227 : Blo 936583 1055227 := bstep (se 1 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 1055227 = 1582841) B1582841
theorem B1055407 : Blo 936583 1055407 := bstep (se 1 (by rfl) ⟨791555, by rfl⟩ : syracuseStep 1055407 = 1583111) B1583111
theorem B4758263 : Blo 936583 4758263 := bstep (se 1 (by rfl) ⟨3568697, by rfl⟩ : syracuseStep 4758263 = 7137395) B7137395
theorem B6757307 : Blo 936583 6757307 := bstep (se 1 (by rfl) ⟨5067980, by rfl⟩ : syracuseStep 6757307 = 10135961) B10135961
theorem B1055695 : Blo 936583 1055695 := bstep (se 1 (by rfl) ⟨791771, by rfl⟩ : syracuseStep 1055695 = 1583543) B1583543
theorem B4758749 : Blo 936583 4758749 := bstep (se 3 (by rfl) ⟨892265, by rfl⟩ : syracuseStep 4758749 = 1784531) B1784531
theorem B1056091 : Blo 936583 1056091 := bstep (se 1 (by rfl) ⟨792068, by rfl⟩ : syracuseStep 1056091 = 1584137) B1584137
theorem B4005217 : Blo 936583 4005217 := bstep (se 2 (by rfl) ⟨1501956, by rfl⟩ : syracuseStep 4005217 = 3003913) B3003913
theorem B6757769 : Blo 936583 6757769 := bstep (se 2 (by rfl) ⟨2534163, by rfl⟩ : syracuseStep 6757769 = 5068327) B5068327
theorem B1056199 : Blo 936583 1056199 := bstep (se 1 (by rfl) ⟨792149, by rfl⟩ : syracuseStep 1056199 = 1584299) B1584299
theorem B2006471 : Blo 936583 2006471 := bstep (se 1 (by rfl) ⟨1504853, by rfl⟩ : syracuseStep 2006471 = 3009707) B3009707
theorem B1187399 : Blo 936583 1187399 := bstep (se 1 (by rfl) ⟨890549, by rfl⟩ : syracuseStep 1187399 = 1781099) B1781099
theorem B1187551 : Blo 936583 1187551 := bstep (se 1 (by rfl) ⟨890663, by rfl⟩ : syracuseStep 1187551 = 1781327) B1781327
theorem B1056559 : Blo 936583 1056559 := bstep (se 1 (by rfl) ⟨792419, by rfl⟩ : syracuseStep 1056559 = 1584839) B1584839
theorem B1056667 : Blo 936583 1056667 := bstep (se 1 (by rfl) ⟨792500, by rfl⟩ : syracuseStep 1056667 = 1585001) B1585001
theorem B1057063 : Blo 936583 1057063 := bstep (se 1 (by rfl) ⟨792797, by rfl⟩ : syracuseStep 1057063 = 1585595) B1585595
theorem B10166579 : Blo 936583 10166579 := bstep (se 1 (by rfl) ⟨7624934, by rfl⟩ : syracuseStep 10166579 = 15249869) B15249869
theorem B1581403 : Blo 936583 1581403 := bstep (se 1 (by rfl) ⟨1186052, by rfl⟩ : syracuseStep 1581403 = 2372105) B2372105
theorem B1057135 : Blo 936583 1057135 := bstep (se 1 (by rfl) ⟨792851, by rfl⟩ : syracuseStep 1057135 = 1585703) B1585703
theorem B2007479 : Blo 936583 2007479 := bstep (se 1 (by rfl) ⟨1505609, by rfl⟩ : syracuseStep 2007479 = 3011219) B3011219
theorem B54206981 : Blo 936583 54206981 := bstep (se 4 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 54206981 = 10163809) B10163809
theorem B6758923 : Blo 936583 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B1057351 : Blo 936583 1057351 := bstep (se 1 (by rfl) ⟨793013, by rfl⟩ : syracuseStep 1057351 = 1586027) B1586027
theorem B2007659 : Blo 936583 2007659 := bstep (se 1 (by rfl) ⟨1505744, by rfl⟩ : syracuseStep 2007659 = 3011489) B3011489
theorem B2532239 : Blo 936583 2532239 := bstep (se 1 (by rfl) ⟨1899179, by rfl⟩ : syracuseStep 2532239 = 3798359) B3798359
theorem B1582375 : Blo 936583 1582375 := bstep (se 1 (by rfl) ⟨1186781, by rfl⟩ : syracuseStep 1582375 = 2373563) B2373563
theorem B8561969 : Blo 936583 8561969 := bstep (se 2 (by rfl) ⟨3210738, by rfl⟩ : syracuseStep 8561969 = 6421477) B6421477
theorem B1582895 : Blo 936583 1582895 := bstep (se 1 (by rfl) ⟨1187171, by rfl⟩ : syracuseStep 1582895 = 2374343) B2374343
theorem B3385169 : Blo 936583 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B12003713 : Blo 936583 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B2140793 : Blo 936583 2140793 := bstep (se 2 (by rfl) ⟨802797, by rfl⟩ : syracuseStep 2140793 = 1605595) B1605595
theorem B2108087 : Blo 936583 2108087 := bstep (se 1 (by rfl) ⟨1581065, by rfl⟩ : syracuseStep 2108087 = 3162131) B3162131
theorem B2534111 : Blo 936583 2534111 := bstep (se 1 (by rfl) ⟨1900583, by rfl⟩ : syracuseStep 2534111 = 3801167) B3801167
theorem B1125199 : Blo 936583 1125199 := bstep (se 1 (by rfl) ⟨843899, by rfl⟩ : syracuseStep 1125199 = 1687799) B1687799
theorem B2108303 : Blo 936583 2108303 := bstep (se 1 (by rfl) ⟨1581227, by rfl⟩ : syracuseStep 2108303 = 3162455) B3162455
theorem B1584103 : Blo 936583 1584103 := bstep (se 1 (by rfl) ⟨1188077, by rfl⟩ : syracuseStep 1584103 = 2376155) B2376155
theorem B10169345 : Blo 936583 10169345 := bstep (se 2 (by rfl) ⟨3813504, by rfl⟩ : syracuseStep 10169345 = 7627009) B7627009
theorem B1780879 : Blo 936583 1780879 := bstep (se 1 (by rfl) ⟨1335659, by rfl⟩ : syracuseStep 1780879 = 2671319) B2671319
theorem B2370779 : Blo 936583 2370779 := bstep (se 1 (by rfl) ⟨1778084, by rfl⟩ : syracuseStep 2370779 = 3556169) B3556169
theorem B2370809 : Blo 936583 2370809 := bstep (se 2 (by rfl) ⟨889053, by rfl⟩ : syracuseStep 2370809 = 1778107) B1778107
theorem B1781023 : Blo 936583 1781023 := bstep (se 1 (by rfl) ⟨1335767, by rfl⟩ : syracuseStep 1781023 = 2671535) B2671535
theorem B1781129 : Blo 936583 1781129 := bstep (se 2 (by rfl) ⟨667923, by rfl⟩ : syracuseStep 1781129 = 1335847) B1335847
theorem B2109023 : Blo 936583 2109023 := bstep (se 1 (by rfl) ⟨1581767, by rfl⟩ : syracuseStep 2109023 = 3163535) B3163535
theorem B2141959 : Blo 936583 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B2109239 : Blo 936583 2109239 := bstep (se 1 (by rfl) ⟨1581929, by rfl⟩ : syracuseStep 2109239 = 3163859) B3163859
theorem B2371457 : Blo 936583 2371457 := bstep (se 2 (by rfl) ⟨889296, by rfl⟩ : syracuseStep 2371457 = 1778593) B1778593
theorem B13512653 : Blo 936583 13512653 := bstep (se 3 (by rfl) ⟨2533622, by rfl⟩ : syracuseStep 13512653 = 5067245) B5067245
theorem B2109545 : Blo 936583 2109545 := bstep (se 2 (by rfl) ⟨791079, by rfl⟩ : syracuseStep 2109545 = 1582159) B1582159
theorem B2371913 : Blo 936583 2371913 := bstep (se 2 (by rfl) ⟨889467, by rfl⟩ : syracuseStep 2371913 = 1778935) B1778935
theorem B1126747 : Blo 936583 1126747 := bstep (se 1 (by rfl) ⟨845060, by rfl⟩ : syracuseStep 1126747 = 1690121) B1690121
theorem B2110031 : Blo 936583 2110031 := bstep (se 1 (by rfl) ⟨1582523, by rfl⟩ : syracuseStep 2110031 = 3165047) B3165047
theorem B2372267 : Blo 936583 2372267 := bstep (se 1 (by rfl) ⟨1779200, by rfl⟩ : syracuseStep 2372267 = 3558401) B3558401
theorem B2110175 : Blo 936583 2110175 := bstep (se 1 (by rfl) ⟨1582631, by rfl⟩ : syracuseStep 2110175 = 3165263) B3165263
theorem B2667343 : Blo 936583 2667343 := bstep (se 1 (by rfl) ⟨2000507, by rfl⟩ : syracuseStep 2667343 = 4001015) B4001015
theorem B2110427 : Blo 936583 2110427 := bstep (se 1 (by rfl) ⟨1582820, by rfl⟩ : syracuseStep 2110427 = 3165641) B3165641
theorem B9385003 : Blo 936583 9385003 := bstep (se 1 (by rfl) ⟨7038752, by rfl⟩ : syracuseStep 9385003 = 14077505) B14077505
theorem B2667617 : Blo 936583 2667617 := bstep (se 2 (by rfl) ⟨1000356, by rfl⟩ : syracuseStep 2667617 = 2000713) B2000713
theorem B38581373 : Blo 936583 38581373 := bstep (se 3 (by rfl) ⟨7234007, by rfl⟩ : syracuseStep 38581373 = 14468015) B14468015
theorem B2110607 : Blo 936583 2110607 := bstep (se 1 (by rfl) ⟨1582955, by rfl⟩ : syracuseStep 2110607 = 3165911) B3165911
theorem B2110697 : Blo 936583 2110697 := bstep (se 2 (by rfl) ⟨791511, by rfl⟩ : syracuseStep 2110697 = 1583023) B1583023
theorem B2110751 : Blo 936583 2110751 := bstep (se 1 (by rfl) ⟨1583063, by rfl⟩ : syracuseStep 2110751 = 3166127) B3166127
theorem B4011403 : Blo 936583 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B9024929 : Blo 936583 9024929 := bstep (se 2 (by rfl) ⟨3384348, by rfl⟩ : syracuseStep 9024929 = 6768697) B6768697
theorem B1586783 : Blo 936583 1586783 := bstep (se 1 (by rfl) ⟨1190087, by rfl⟩ : syracuseStep 1586783 = 2380175) B2380175
theorem B4011677 : Blo 936583 4011677 := bstep (se 3 (by rfl) ⟨752189, by rfl⟩ : syracuseStep 4011677 = 1504379) B1504379
theorem B2537147 : Blo 936583 2537147 := bstep (se 1 (by rfl) ⟨1902860, by rfl⟩ : syracuseStep 2537147 = 3805721) B3805721
theorem B1783559 : Blo 936583 1783559 := bstep (se 1 (by rfl) ⟨1337669, by rfl⟩ : syracuseStep 1783559 = 2675339) B2675339
theorem B2111273 : Blo 936583 2111273 := bstep (se 2 (by rfl) ⟨791727, by rfl⟩ : syracuseStep 2111273 = 1583455) B1583455
theorem B2537257 : Blo 936583 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B4273975 : Blo 936583 4273975 := bstep (se 1 (by rfl) ⟨3205481, by rfl⟩ : syracuseStep 4273975 = 6410963) B6410963
theorem B1586999 : Blo 936583 1586999 := bstep (se 1 (by rfl) ⟨1190249, by rfl⟩ : syracuseStep 1586999 = 2380499) B2380499
theorem B2373583 : Blo 936583 2373583 := bstep (se 1 (by rfl) ⟨1780187, by rfl⟩ : syracuseStep 2373583 = 3560375) B3560375
theorem B20297789 : Blo 936583 20297789 := bstep (se 3 (by rfl) ⟨3805835, by rfl⟩ : syracuseStep 20297789 = 7611671) B7611671
theorem B4274429 : Blo 936583 4274429 := bstep (se 3 (by rfl) ⟨801455, by rfl⟩ : syracuseStep 4274429 = 1602911) B1602911
theorem B3389725 : Blo 936583 3389725 := bstep (se 3 (by rfl) ⟨635573, by rfl⟩ : syracuseStep 3389725 = 1271147) B1271147
theorem B2537839 : Blo 936583 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B4274575 : Blo 936583 4274575 := bstep (se 1 (by rfl) ⟨3205931, by rfl⟩ : syracuseStep 4274575 = 6411863) B6411863
theorem B2669051 : Blo 936583 2669051 := bstep (se 1 (by rfl) ⟨2001788, by rfl⟩ : syracuseStep 2669051 = 4003577) B4003577
theorem B13548055 : Blo 936583 13548055 := bstep (se 1 (by rfl) ⟨10161041, by rfl⟩ : syracuseStep 13548055 = 20322083) B20322083
theorem B2112335 : Blo 936583 2112335 := bstep (se 1 (by rfl) ⟨1584251, by rfl⟩ : syracuseStep 2112335 = 3168503) B3168503
theorem B2374555 : Blo 936583 2374555 := bstep (se 1 (by rfl) ⟨1780916, by rfl⟩ : syracuseStep 2374555 = 3561833) B3561833
theorem B1129447 : Blo 936583 1129447 := bstep (se 1 (by rfl) ⟨847085, by rfl⟩ : syracuseStep 1129447 = 1694171) B1694171
theorem B2112551 : Blo 936583 2112551 := bstep (se 1 (by rfl) ⟨1584413, by rfl⟩ : syracuseStep 2112551 = 3168827) B3168827
theorem B2112731 : Blo 936583 2112731 := bstep (se 1 (by rfl) ⟨1584548, by rfl⟩ : syracuseStep 2112731 = 3169097) B3169097
theorem B3161375 : Blo 936583 3161375 := bstep (se 1 (by rfl) ⟨2371031, by rfl⟩ : syracuseStep 3161375 = 4742063) B4742063
theorem B2112929 : Blo 936583 2112929 := bstep (se 2 (by rfl) ⟨792348, by rfl⟩ : syracuseStep 2112929 = 1584697) B1584697
theorem B8011223 : Blo 936583 8011223 := bstep (se 1 (by rfl) ⟨6008417, by rfl⟩ : syracuseStep 8011223 = 12016835) B12016835
theorem B9027389 : Blo 936583 9027389 := bstep (se 3 (by rfl) ⟨1692635, by rfl⟩ : syracuseStep 9027389 = 3385271) B3385271
theorem B2113487 : Blo 936583 2113487 := bstep (se 1 (by rfl) ⟨1585115, by rfl⟩ : syracuseStep 2113487 = 3170231) B3170231
theorem B2375689 : Blo 936583 2375689 := bstep (se 2 (by rfl) ⟨890883, by rfl⟩ : syracuseStep 2375689 = 1781767) B1781767
theorem B2113865 : Blo 936583 2113865 := bstep (se 2 (by rfl) ⟨792699, by rfl⟩ : syracuseStep 2113865 = 1585399) B1585399
theorem B2113883 : Blo 936583 2113883 := bstep (se 1 (by rfl) ⟨1585412, by rfl⟩ : syracuseStep 2113883 = 3170825) B3170825
theorem B1426027 : Blo 936583 1426027 := bstep (se 1 (by rfl) ⟨1069520, by rfl⟩ : syracuseStep 1426027 = 2139041) B2139041
theorem B18039469 : Blo 936583 18039469 := bstep (se 3 (by rfl) ⟨3382400, by rfl⟩ : syracuseStep 18039469 = 6764801) B6764801
theorem B8012621 : Blo 936583 8012621 := bstep (se 3 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 8012621 = 3004733) B3004733
theorem B2114459 : Blo 936583 2114459 := bstep (se 1 (by rfl) ⟨1585844, by rfl⟩ : syracuseStep 2114459 = 3171689) B3171689
theorem B1000399 : Blo 936583 1000399 := bstep (se 1 (by rfl) ⟨750299, by rfl⟩ : syracuseStep 1000399 = 1500599) B1500599
theorem B7128161 : Blo 936583 7128161 := bstep (se 2 (by rfl) ⟨2673060, by rfl⟩ : syracuseStep 7128161 = 5346121) B5346121
theorem B2114657 : Blo 936583 2114657 := bstep (se 2 (by rfl) ⟨792996, by rfl⟩ : syracuseStep 2114657 = 1585993) B1585993
theorem B1688809 : Blo 936583 1688809 := bstep (se 2 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 1688809 = 1266607) B1266607
theorem B2114855 : Blo 936583 2114855 := bstep (se 1 (by rfl) ⟨1586141, by rfl⟩ : syracuseStep 2114855 = 3172283) B3172283
theorem B2671967 : Blo 936583 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B4015469 : Blo 936583 4015469 := bstep (se 3 (by rfl) ⟨752900, by rfl⟩ : syracuseStep 4015469 = 1505801) B1505801
theorem B2377097 : Blo 936583 2377097 := bstep (se 2 (by rfl) ⟨891411, by rfl⟩ : syracuseStep 2377097 = 1782823) B1782823
theorem B2377147 : Blo 936583 2377147 := bstep (se 1 (by rfl) ⟨1782860, by rfl⟩ : syracuseStep 2377147 = 3565721) B3565721
theorem B3163805 : Blo 936583 3163805 := bstep (se 3 (by rfl) ⟨593213, by rfl⟩ : syracuseStep 3163805 = 1186427) B1186427
theorem B2115233 : Blo 936583 2115233 := bstep (se 2 (by rfl) ⟨793212, by rfl⟩ : syracuseStep 2115233 = 1586425) B1586425
theorem B2377451 : Blo 936583 2377451 := bstep (se 1 (by rfl) ⟨1783088, by rfl⟩ : syracuseStep 2377451 = 3566177) B3566177
theorem B2115593 : Blo 936583 2115593 := bstep (se 2 (by rfl) ⟨793347, by rfl⟩ : syracuseStep 2115593 = 1586695) B1586695
theorem B3164345 : Blo 936583 3164345 := bstep (se 2 (by rfl) ⟨1186629, by rfl⟩ : syracuseStep 3164345 = 2373259) B2373259
theorem B14469313 : Blo 936583 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B3557641 : Blo 936583 3557641 := bstep (se 2 (by rfl) ⟨1334115, by rfl⟩ : syracuseStep 3557641 = 2668231) B2668231
theorem B1001851 : Blo 936583 1001851 := bstep (se 1 (by rfl) ⟨751388, by rfl⟩ : syracuseStep 1001851 = 1502777) B1502777
theorem B2116007 : Blo 936583 2116007 := bstep (se 1 (by rfl) ⟨1587005, by rfl⟩ : syracuseStep 2116007 = 3174011) B3174011
theorem B2673107 : Blo 936583 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B3000827 : Blo 936583 3000827 := bstep (se 1 (by rfl) ⟨2250620, by rfl⟩ : syracuseStep 3000827 = 4501241) B4501241
theorem B2116115 : Blo 936583 2116115 := bstep (se 1 (by rfl) ⟨1587086, by rfl⟩ : syracuseStep 2116115 = 3174173) B3174173
theorem B2116169 : Blo 936583 2116169 := bstep (se 2 (by rfl) ⟨793563, by rfl⟩ : syracuseStep 2116169 = 1587127) B1587127
theorem B2378423 : Blo 936583 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B936671 : Blo 936583 936671 := bstep (se 1 (by rfl) ⟨702503, by rfl⟩ : syracuseStep 936671 = 1405007) B1405007
theorem B936751 : Blo 936583 936751 := bstep (se 1 (by rfl) ⟨702563, by rfl⟩ : syracuseStep 936751 = 1405127) B1405127
theorem B936859 : Blo 936583 936859 := bstep (se 1 (by rfl) ⟨702644, by rfl⟩ : syracuseStep 936859 = 1405289) B1405289
theorem B936911 : Blo 936583 936911 := bstep (se 1 (by rfl) ⟨702683, by rfl⟩ : syracuseStep 936911 = 1405367) B1405367
theorem B936935 : Blo 936583 936935 := bstep (se 1 (by rfl) ⟨702701, by rfl⟩ : syracuseStep 936935 = 1405403) B1405403
theorem B937247 : Blo 936583 937247 := bstep (se 1 (by rfl) ⟨702935, by rfl⟩ : syracuseStep 937247 = 1405871) B1405871
theorem B1002791 : Blo 936583 1002791 := bstep (se 1 (by rfl) ⟨752093, by rfl⟩ : syracuseStep 1002791 = 1504187) B1504187
theorem B937307 : Blo 936583 937307 := bstep (se 1 (by rfl) ⟨702980, by rfl⟩ : syracuseStep 937307 = 1405961) B1405961
theorem B937327 : Blo 936583 937327 := bstep (se 1 (by rfl) ⟨702995, by rfl⟩ : syracuseStep 937327 = 1405991) B1405991
theorem B8015219 : Blo 936583 8015219 := bstep (se 1 (by rfl) ⟨6011414, by rfl⟩ : syracuseStep 8015219 = 12022829) B12022829
theorem B937383 : Blo 936583 937383 := bstep (se 1 (by rfl) ⟨703037, by rfl⟩ : syracuseStep 937383 = 1406075) B1406075
theorem B937467 : Blo 936583 937467 := bstep (se 1 (by rfl) ⟨703100, by rfl⟩ : syracuseStep 937467 = 1406201) B1406201
theorem B937535 : Blo 936583 937535 := bstep (se 1 (by rfl) ⟨703151, by rfl⟩ : syracuseStep 937535 = 1406303) B1406303
theorem B937543 : Blo 936583 937543 := bstep (se 1 (by rfl) ⟨703157, by rfl⟩ : syracuseStep 937543 = 1406315) B1406315
theorem B3002017 : Blo 936583 3002017 := bstep (se 2 (by rfl) ⟨1125756, by rfl⟩ : syracuseStep 3002017 = 2251513) B2251513
theorem B3165857 : Blo 936583 3165857 := bstep (se 2 (by rfl) ⟨1187196, by rfl⟩ : syracuseStep 3165857 = 2374393) B2374393
theorem B937695 : Blo 936583 937695 := bstep (se 1 (by rfl) ⟨703271, by rfl⟩ : syracuseStep 937695 = 1406543) B1406543
theorem B2379527 : Blo 936583 2379527 := bstep (se 1 (by rfl) ⟨1784645, by rfl⟩ : syracuseStep 2379527 = 3569291) B3569291
theorem B3002159 : Blo 936583 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B937775 : Blo 936583 937775 := bstep (se 1 (by rfl) ⟨703331, by rfl⟩ : syracuseStep 937775 = 1406663) B1406663
theorem B2379577 : Blo 936583 2379577 := bstep (se 2 (by rfl) ⟨892341, by rfl⟩ : syracuseStep 2379577 = 1784683) B1784683
theorem B937883 : Blo 936583 937883 := bstep (se 1 (by rfl) ⟨703412, by rfl⟩ : syracuseStep 937883 = 1406825) B1406825
theorem B937935 : Blo 936583 937935 := bstep (se 1 (by rfl) ⟨703451, by rfl⟩ : syracuseStep 937935 = 1406903) B1406903
theorem B937959 : Blo 936583 937959 := bstep (se 1 (by rfl) ⟨703469, by rfl⟩ : syracuseStep 937959 = 1406939) B1406939
theorem B4509715 : Blo 936583 4509715 := bstep (se 1 (by rfl) ⟨3382286, by rfl⟩ : syracuseStep 4509715 = 6764573) B6764573
theorem B2412569 : Blo 936583 2412569 := bstep (se 2 (by rfl) ⟨904713, by rfl⟩ : syracuseStep 2412569 = 1809427) B1809427
theorem B4509755 : Blo 936583 4509755 := bstep (se 1 (by rfl) ⟨3382316, by rfl⟩ : syracuseStep 4509755 = 6764633) B6764633
theorem B2379881 : Blo 936583 2379881 := bstep (se 2 (by rfl) ⟨892455, by rfl⟩ : syracuseStep 2379881 = 1784911) B1784911
theorem B938271 : Blo 936583 938271 := bstep (se 1 (by rfl) ⟨703703, by rfl⟩ : syracuseStep 938271 = 1407407) B1407407
theorem B10703177 : Blo 936583 10703177 := bstep (se 2 (by rfl) ⟨4013691, by rfl⟩ : syracuseStep 10703177 = 8027383) B8027383
theorem B938331 : Blo 936583 938331 := bstep (se 1 (by rfl) ⟨703748, by rfl⟩ : syracuseStep 938331 = 1407497) B1407497
theorem B938351 : Blo 936583 938351 := bstep (se 1 (by rfl) ⟨703763, by rfl⟩ : syracuseStep 938351 = 1407527) B1407527
theorem B938407 : Blo 936583 938407 := bstep (se 1 (by rfl) ⟨703805, by rfl⟩ : syracuseStep 938407 = 1407611) B1407611
theorem B938491 : Blo 936583 938491 := bstep (se 1 (by rfl) ⟨703868, by rfl⟩ : syracuseStep 938491 = 1407737) B1407737
theorem B3166721 : Blo 936583 3166721 := bstep (se 2 (by rfl) ⟨1187520, by rfl⟩ : syracuseStep 3166721 = 2375041) B2375041
theorem B938559 : Blo 936583 938559 := bstep (se 1 (by rfl) ⟨703919, by rfl⟩ : syracuseStep 938559 = 1407839) B1407839
theorem B938567 : Blo 936583 938567 := bstep (se 1 (by rfl) ⟨703925, by rfl⟩ : syracuseStep 938567 = 1407851) B1407851
theorem B2380367 : Blo 936583 2380367 := bstep (se 1 (by rfl) ⟨1785275, by rfl⟩ : syracuseStep 2380367 = 3570551) B3570551
theorem B3560057 : Blo 936583 3560057 := bstep (se 2 (by rfl) ⟨1335021, by rfl⟩ : syracuseStep 3560057 = 2670043) B2670043
theorem B938719 : Blo 936583 938719 := bstep (se 1 (by rfl) ⟨704039, by rfl⟩ : syracuseStep 938719 = 1408079) B1408079
theorem B938799 : Blo 936583 938799 := bstep (se 1 (by rfl) ⟨704099, by rfl⟩ : syracuseStep 938799 = 1408199) B1408199
theorem B938907 : Blo 936583 938907 := bstep (se 1 (by rfl) ⟨704180, by rfl⟩ : syracuseStep 938907 = 1408361) B1408361
theorem B938959 : Blo 936583 938959 := bstep (se 1 (by rfl) ⟨704219, by rfl⟩ : syracuseStep 938959 = 1408439) B1408439
theorem B3167207 : Blo 936583 3167207 := bstep (se 1 (by rfl) ⟨2375405, by rfl⟩ : syracuseStep 3167207 = 4750811) B4750811
theorem B938983 : Blo 936583 938983 := bstep (se 1 (by rfl) ⟨704237, by rfl⟩ : syracuseStep 938983 = 1408475) B1408475
theorem B939295 : Blo 936583 939295 := bstep (se 1 (by rfl) ⟨704471, by rfl⟩ : syracuseStep 939295 = 1408943) B1408943
theorem B3167531 : Blo 936583 3167531 := bstep (se 1 (by rfl) ⟨2375648, by rfl⟩ : syracuseStep 3167531 = 4751297) B4751297
theorem B939355 : Blo 936583 939355 := bstep (se 1 (by rfl) ⟨704516, by rfl⟩ : syracuseStep 939355 = 1409033) B1409033
theorem B939375 : Blo 936583 939375 := bstep (se 1 (by rfl) ⟨704531, by rfl⟩ : syracuseStep 939375 = 1409063) B1409063
theorem B2676091 : Blo 936583 2676091 := bstep (se 1 (by rfl) ⟨2007068, by rfl⟩ : syracuseStep 2676091 = 4014137) B4014137
theorem B939431 : Blo 936583 939431 := bstep (se 1 (by rfl) ⟨704573, by rfl⟩ : syracuseStep 939431 = 1409147) B1409147
theorem B939515 : Blo 936583 939515 := bstep (se 1 (by rfl) ⟨704636, by rfl⟩ : syracuseStep 939515 = 1409273) B1409273
theorem B3167801 : Blo 936583 3167801 := bstep (se 2 (by rfl) ⟨1187925, by rfl⟩ : syracuseStep 3167801 = 2375851) B2375851
theorem B939583 : Blo 936583 939583 := bstep (se 1 (by rfl) ⟨704687, by rfl⟩ : syracuseStep 939583 = 1409375) B1409375
theorem B20305475 : Blo 936583 20305475 := bstep (se 1 (by rfl) ⟨15229106, by rfl⟩ : syracuseStep 20305475 = 30458213) B30458213
theorem B939591 : Blo 936583 939591 := bstep (se 1 (by rfl) ⟨704693, by rfl⟩ : syracuseStep 939591 = 1409387) B1409387
theorem B6018745 : Blo 936583 6018745 := bstep (se 2 (by rfl) ⟨2257029, by rfl⟩ : syracuseStep 6018745 = 4514059) B4514059
theorem B939743 : Blo 936583 939743 := bstep (se 1 (by rfl) ⟨704807, by rfl⟩ : syracuseStep 939743 = 1409615) B1409615
theorem B939823 : Blo 936583 939823 := bstep (se 1 (by rfl) ⟨704867, by rfl⟩ : syracuseStep 939823 = 1409735) B1409735
theorem B939931 : Blo 936583 939931 := bstep (se 1 (by rfl) ⟨704948, by rfl⟩ : syracuseStep 939931 = 1409897) B1409897
theorem B939983 : Blo 936583 939983 := bstep (se 1 (by rfl) ⟨704987, by rfl⟩ : syracuseStep 939983 = 1409975) B1409975
theorem B940007 : Blo 936583 940007 := bstep (se 1 (by rfl) ⟨705005, by rfl⟩ : syracuseStep 940007 = 1410011) B1410011
theorem B940319 : Blo 936583 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B940379 : Blo 936583 940379 := bstep (se 1 (by rfl) ⟨705284, by rfl⟩ : syracuseStep 940379 = 1410569) B1410569
theorem B940399 : Blo 936583 940399 := bstep (se 1 (by rfl) ⟨705299, by rfl⟩ : syracuseStep 940399 = 1410599) B1410599
theorem B940455 : Blo 936583 940455 := bstep (se 1 (by rfl) ⟨705341, by rfl⟩ : syracuseStep 940455 = 1410683) B1410683
theorem B940539 : Blo 936583 940539 := bstep (se 1 (by rfl) ⟨705404, by rfl⟩ : syracuseStep 940539 = 1410809) B1410809
theorem B4741739 : Blo 936583 4741739 := bstep (se 1 (by rfl) ⟨3556304, by rfl⟩ : syracuseStep 4741739 = 7112609) B7112609
theorem B13556483 : Blo 936583 13556483 := bstep (se 1 (by rfl) ⟨10167362, by rfl⟩ : syracuseStep 13556483 = 20334725) B20334725
theorem B3169043 : Blo 936583 3169043 := bstep (se 1 (by rfl) ⟨2376782, by rfl⟩ : syracuseStep 3169043 = 4753565) B4753565
theorem B38558537 : Blo 936583 38558537 := bstep (se 2 (by rfl) ⟨14459451, by rfl⟩ : syracuseStep 38558537 = 28918903) B28918903
theorem B6020027 : Blo 936583 6020027 := bstep (se 1 (by rfl) ⟨4515020, by rfl⟩ : syracuseStep 6020027 = 9030041) B9030041
theorem B2677799 : Blo 936583 2677799 := bstep (se 1 (by rfl) ⟨2008349, by rfl⟩ : syracuseStep 2677799 = 4016699) B4016699
theorem B4742225 : Blo 936583 4742225 := bstep (se 2 (by rfl) ⟨1778334, by rfl⟩ : syracuseStep 4742225 = 3556669) B3556669
theorem B2251975 : Blo 936583 2251975 := bstep (se 1 (by rfl) ⟨1688981, by rfl⟩ : syracuseStep 2251975 = 3377963) B3377963
theorem B6184471 : Blo 936583 6184471 := bstep (se 1 (by rfl) ⟨4638353, by rfl⟩ : syracuseStep 6184471 = 9276707) B9276707
theorem B3169907 : Blo 936583 3169907 := bstep (se 1 (by rfl) ⟨2377430, by rfl⟩ : syracuseStep 3169907 = 4754861) B4754861
theorem B9756305 : Blo 936583 9756305 := bstep (se 2 (by rfl) ⟨3658614, by rfl⟩ : syracuseStep 9756305 = 7317229) B7317229
theorem B2252551 : Blo 936583 2252551 := bstep (se 1 (by rfl) ⟨1689413, by rfl⟩ : syracuseStep 2252551 = 3378827) B3378827
theorem B3661615 : Blo 936583 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B3170177 : Blo 936583 3170177 := bstep (se 2 (by rfl) ⟨1188816, by rfl⟩ : syracuseStep 3170177 = 2377633) B2377633
theorem B8019971 : Blo 936583 8019971 := bstep (se 1 (by rfl) ⟨6014978, by rfl⟩ : syracuseStep 8019971 = 12029957) B12029957
theorem B2253167 : Blo 936583 2253167 := bstep (se 1 (by rfl) ⟨1689875, by rfl⟩ : syracuseStep 2253167 = 3379751) B3379751
theorem B3170987 : Blo 936583 3170987 := bstep (se 1 (by rfl) ⟨2378240, by rfl⟩ : syracuseStep 3170987 = 4756481) B4756481
theorem B3007631 : Blo 936583 3007631 := bstep (se 1 (by rfl) ⟨2255723, by rfl⟩ : syracuseStep 3007631 = 4511447) B4511447
theorem B4056263 : Blo 936583 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B3171527 : Blo 936583 3171527 := bstep (se 1 (by rfl) ⟨2378645, by rfl⟩ : syracuseStep 3171527 = 4757291) B4757291
theorem B4285655 : Blo 936583 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B3859751 : Blo 936583 3859751 := bstep (se 1 (by rfl) ⟨2894813, by rfl⟩ : syracuseStep 3859751 = 5789627) B5789627
theorem B22799681 : Blo 936583 22799681 := bstep (se 2 (by rfl) ⟨8549880, by rfl⟩ : syracuseStep 22799681 = 17099761) B17099761
theorem B4810375 : Blo 936583 4810375 := bstep (se 1 (by rfl) ⟨3607781, by rfl⟩ : syracuseStep 4810375 = 7215563) B7215563
theorem B3565417 : Blo 936583 3565417 := bstep (se 2 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 3565417 = 2674063) B2674063
theorem B16017587 : Blo 936583 16017587 := bstep (se 1 (by rfl) ⟨12013190, by rfl⟩ : syracuseStep 16017587 = 24026381) B24026381
theorem B3205385 : Blo 936583 3205385 := bstep (se 2 (by rfl) ⟨1202019, by rfl⟩ : syracuseStep 3205385 = 2404039) B2404039
theorem B6023591 : Blo 936583 6023591 := bstep (se 1 (by rfl) ⟨4517693, by rfl⟩ : syracuseStep 6023591 = 9035387) B9035387
theorem B3173039 : Blo 936583 3173039 := bstep (se 1 (by rfl) ⟨2379779, by rfl⟩ : syracuseStep 3173039 = 4759559) B4759559
theorem B1501919 : Blo 936583 1501919 := bstep (se 1 (by rfl) ⟨1126439, by rfl⟩ : syracuseStep 1501919 = 2252879) B2252879
theorem B3009271 : Blo 936583 3009271 := bstep (se 1 (by rfl) ⟨2256953, by rfl⟩ : syracuseStep 3009271 = 4513907) B4513907
theorem B3173363 : Blo 936583 3173363 := bstep (se 1 (by rfl) ⟨2380022, by rfl⟩ : syracuseStep 3173363 = 4760045) B4760045
theorem B8580097 : Blo 936583 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B7334993 : Blo 936583 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B4746761 : Blo 936583 4746761 := bstep (se 2 (by rfl) ⟨1780035, by rfl⟩ : syracuseStep 4746761 = 3560071) B3560071
theorem B3173903 : Blo 936583 3173903 := bstep (se 1 (by rfl) ⟨2380427, by rfl⟩ : syracuseStep 3173903 = 4760855) B4760855
theorem B9629293 : Blo 936583 9629293 := bstep (se 3 (by rfl) ⟨1805492, by rfl⟩ : syracuseStep 9629293 = 3610985) B3610985
theorem B1405193 : Blo 936583 1405193 := bstep (se 2 (by rfl) ⟨526947, by rfl⟩ : syracuseStep 1405193 = 1053895) B1053895
theorem B9007433 : Blo 936583 9007433 := bstep (se 2 (by rfl) ⟨3377787, by rfl⟩ : syracuseStep 9007433 = 6755575) B6755575
theorem B3305819 : Blo 936583 3305819 := bstep (se 1 (by rfl) ⟨2479364, by rfl⟩ : syracuseStep 3305819 = 4958729) B4958729
theorem B4518251 : Blo 936583 4518251 := bstep (se 1 (by rfl) ⟨3388688, by rfl⟩ : syracuseStep 4518251 = 6777377) B6777377
theorem B1405295 : Blo 936583 1405295 := bstep (se 1 (by rfl) ⟨1053971, by rfl⟩ : syracuseStep 1405295 = 2107943) B2107943
theorem B16249369 : Blo 936583 16249369 := bstep (se 2 (by rfl) ⟨6093513, by rfl⟩ : syracuseStep 16249369 = 12187027) B12187027
theorem B1405511 : Blo 936583 1405511 := bstep (se 1 (by rfl) ⟨1054133, by rfl⟩ : syracuseStep 1405511 = 2108267) B2108267
theorem B1405547 : Blo 936583 1405547 := bstep (se 1 (by rfl) ⟨1054160, by rfl⟩ : syracuseStep 1405547 = 2108321) B2108321
theorem B4879001 : Blo 936583 4879001 := bstep (se 2 (by rfl) ⟨1829625, by rfl⟩ : syracuseStep 4879001 = 3659251) B3659251
theorem B5337899 : Blo 936583 5337899 := bstep (se 1 (by rfl) ⟨4003424, by rfl⟩ : syracuseStep 5337899 = 8006849) B8006849
theorem B1405775 : Blo 936583 1405775 := bstep (se 1 (by rfl) ⟨1054331, by rfl⟩ : syracuseStep 1405775 = 2108663) B2108663
theorem B2257895 : Blo 936583 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B40662161 : Blo 936583 40662161 := bstep (se 2 (by rfl) ⟨15248310, by rfl⟩ : syracuseStep 40662161 = 30496621) B30496621
theorem B1406171 : Blo 936583 1406171 := bstep (se 1 (by rfl) ⟨1054628, by rfl⟩ : syracuseStep 1406171 = 2109257) B2109257
theorem B3011833 : Blo 936583 3011833 := bstep (se 2 (by rfl) ⟨1129437, by rfl⟩ : syracuseStep 3011833 = 2258875) B2258875
theorem B1406345 : Blo 936583 1406345 := bstep (se 2 (by rfl) ⟨527379, by rfl⟩ : syracuseStep 1406345 = 1054759) B1054759
theorem B4748705 : Blo 936583 4748705 := bstep (se 2 (by rfl) ⟨1780764, by rfl⟩ : syracuseStep 4748705 = 3561529) B3561529
theorem B8123885 : Blo 936583 8123885 := bstep (se 3 (by rfl) ⟨1523228, by rfl⟩ : syracuseStep 8123885 = 3046457) B3046457
theorem B1406699 : Blo 936583 1406699 := bstep (se 1 (by rfl) ⟨1055024, by rfl⟩ : syracuseStep 1406699 = 2110049) B2110049
theorem B1406927 : Blo 936583 1406927 := bstep (se 1 (by rfl) ⟨1055195, by rfl⟩ : syracuseStep 1406927 = 2110391) B2110391
theorem B1407323 : Blo 936583 1407323 := bstep (se 1 (by rfl) ⟨1055492, by rfl⟩ : syracuseStep 1407323 = 2110985) B2110985
theorem B1505647 : Blo 936583 1505647 := bstep (se 1 (by rfl) ⟨1129235, by rfl⟩ : syracuseStep 1505647 = 2258471) B2258471
theorem B1407551 : Blo 936583 1407551 := bstep (se 1 (by rfl) ⟨1055663, by rfl⟩ : syracuseStep 1407551 = 2111327) B2111327
theorem B4815467 : Blo 936583 4815467 := bstep (se 1 (by rfl) ⟨3611600, by rfl⟩ : syracuseStep 4815467 = 7223201) B7223201
theorem B1407671 : Blo 936583 1407671 := bstep (se 1 (by rfl) ⟨1055753, by rfl⟩ : syracuseStep 1407671 = 2111507) B2111507
theorem B356023187 : Blo 936583 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B1407899 : Blo 936583 1407899 := bstep (se 1 (by rfl) ⟨1055924, by rfl⟩ : syracuseStep 1407899 = 2111849) B2111849
theorem B1408295 : Blo 936583 1408295 := bstep (se 1 (by rfl) ⟨1056221, by rfl⟩ : syracuseStep 1408295 = 2112443) B2112443
theorem B1408379 : Blo 936583 1408379 := bstep (se 1 (by rfl) ⟨1056284, by rfl⟩ : syracuseStep 1408379 = 2112569) B2112569
theorem B1408505 : Blo 936583 1408505 := bstep (se 2 (by rfl) ⟨528189, by rfl⟩ : syracuseStep 1408505 = 1056379) B1056379
theorem B1408607 : Blo 936583 1408607 := bstep (se 1 (by rfl) ⟨1056455, by rfl⟩ : syracuseStep 1408607 = 2112911) B2112911
theorem B5078791 : Blo 936583 5078791 := bstep (se 1 (by rfl) ⟨3809093, by rfl⟩ : syracuseStep 5078791 = 7618187) B7618187
theorem B1408823 : Blo 936583 1408823 := bstep (se 1 (by rfl) ⟨1056617, by rfl⟩ : syracuseStep 1408823 = 2113235) B2113235
theorem B1409243 : Blo 936583 1409243 := bstep (se 1 (by rfl) ⟨1056932, by rfl⟩ : syracuseStep 1409243 = 2113865) B2113865
theorem B1409255 : Blo 936583 1409255 := bstep (se 1 (by rfl) ⟨1056941, by rfl⟩ : syracuseStep 1409255 = 2113883) B2113883
theorem B1409417 : Blo 936583 1409417 := bstep (se 2 (by rfl) ⟨528531, by rfl⟩ : syracuseStep 1409417 = 1057063) B1057063
theorem B1409513 : Blo 936583 1409513 := bstep (se 2 (by rfl) ⟨528567, by rfl⟩ : syracuseStep 1409513 = 1057135) B1057135
theorem B5341747 : Blo 936583 5341747 := bstep (se 1 (by rfl) ⟨4006310, by rfl⟩ : syracuseStep 5341747 = 8012621) B8012621
theorem B1409639 : Blo 936583 1409639 := bstep (se 1 (by rfl) ⟨1057229, by rfl⟩ : syracuseStep 1409639 = 2114459) B2114459
theorem B9011897 : Blo 936583 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B4752107 : Blo 936583 4752107 := bstep (se 1 (by rfl) ⟨3564080, by rfl⟩ : syracuseStep 4752107 = 7128161) B7128161
theorem B1409771 : Blo 936583 1409771 := bstep (se 1 (by rfl) ⟨1057328, by rfl⟩ : syracuseStep 1409771 = 2114657) B2114657
theorem B1409801 : Blo 936583 1409801 := bstep (se 2 (by rfl) ⟨528675, by rfl⟩ : syracuseStep 1409801 = 1057351) B1057351
theorem B1901369 : Blo 936583 1901369 := bstep (se 2 (by rfl) ⟨713013, by rfl⟩ : syracuseStep 1901369 = 1426027) B1426027
theorem B1409903 : Blo 936583 1409903 := bstep (se 1 (by rfl) ⟨1057427, by rfl⟩ : syracuseStep 1409903 = 2114855) B2114855
theorem B24052625 : Blo 936583 24052625 := bstep (se 2 (by rfl) ⟨9019734, by rfl⟩ : syracuseStep 24052625 = 18039469) B18039469
theorem B8815517 : Blo 936583 8815517 := bstep (se 3 (by rfl) ⟨1652909, by rfl⟩ : syracuseStep 8815517 = 3305819) B3305819
theorem B1410155 : Blo 936583 1410155 := bstep (se 1 (by rfl) ⟨1057616, by rfl⟩ : syracuseStep 1410155 = 2115233) B2115233
theorem B1410395 : Blo 936583 1410395 := bstep (se 1 (by rfl) ⟨1057796, by rfl⟩ : syracuseStep 1410395 = 2115593) B2115593
theorem B1410671 : Blo 936583 1410671 := bstep (se 1 (by rfl) ⟨1058003, by rfl⟩ : syracuseStep 1410671 = 2116007) B2116007
theorem B2000551 : Blo 936583 2000551 := bstep (se 1 (by rfl) ⟨1500413, by rfl⟩ : syracuseStep 2000551 = 3000827) B3000827
theorem B1410743 : Blo 936583 1410743 := bstep (se 1 (by rfl) ⟨1058057, by rfl⟩ : syracuseStep 1410743 = 2116115) B2116115
theorem B1410779 : Blo 936583 1410779 := bstep (se 1 (by rfl) ⟨1058084, by rfl⟩ : syracuseStep 1410779 = 2116169) B2116169
theorem B8030117 : Blo 936583 8030117 := bstep (se 4 (by rfl) ⟨752823, by rfl⟩ : syracuseStep 8030117 = 1505647) B1505647
theorem B5343205 : Blo 936583 5343205 := bstep (se 4 (by rfl) ⟨500925, by rfl⟩ : syracuseStep 5343205 = 1001851) B1001851
theorem B5343479 : Blo 936583 5343479 := bstep (se 1 (by rfl) ⟨4007609, by rfl⟩ : syracuseStep 5343479 = 8015219) B8015219
theorem B4753889 : Blo 936583 4753889 := bstep (se 2 (by rfl) ⟨1782708, by rfl⟩ : syracuseStep 4753889 = 3565417) B3565417
theorem B2001439 : Blo 936583 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B1608379 : Blo 936583 1608379 := bstep (se 1 (by rfl) ⟨1206284, by rfl⟩ : syracuseStep 1608379 = 2412569) B2412569
theorem B13536983 : Blo 936583 13536983 := bstep (se 1 (by rfl) ⟨10152737, by rfl⟩ : syracuseStep 13536983 = 20305475) B20305475
theorem B11440129 : Blo 936583 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B4756157 : Blo 936583 4756157 := bstep (se 3 (by rfl) ⟨891779, by rfl⟩ : syracuseStep 4756157 = 1783559) B1783559
theorem B4002689 : Blo 936583 4002689 := bstep (se 2 (by rfl) ⟨1501008, by rfl⟩ : syracuseStep 4002689 = 3002017) B3002017
theorem B2855945 : Blo 936583 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B5346647 : Blo 936583 5346647 := bstep (se 1 (by rfl) ⟨4009985, by rfl⟩ : syracuseStep 5346647 = 8019971) B8019971
theorem B14423993 : Blo 936583 14423993 := bstep (se 2 (by rfl) ⟨5408997, by rfl⟩ : syracuseStep 14423993 = 10817995) B10817995
theorem B21665825 : Blo 936583 21665825 := bstep (se 2 (by rfl) ⟨8124684, by rfl⟩ : syracuseStep 21665825 = 16249369) B16249369
theorem B2005087 : Blo 936583 2005087 := bstep (se 1 (by rfl) ⟨1503815, by rfl⟩ : syracuseStep 2005087 = 3007631) B3007631
theorem B2857103 : Blo 936583 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B5707979 : Blo 936583 5707979 := bstep (se 1 (by rfl) ⟨4280984, by rfl⟩ : syracuseStep 5707979 = 8561969) B8561969
theorem B1055263 : Blo 936583 1055263 := bstep (se 1 (by rfl) ⟨791447, by rfl⟩ : syracuseStep 1055263 = 1582895) B1582895
theorem B8002097 : Blo 936583 8002097 := bstep (se 2 (by rfl) ⟨3000786, by rfl⟩ : syracuseStep 8002097 = 6001573) B6001573
theorem B7117469 : Blo 936583 7117469 := bstep (se 3 (by rfl) ⟨1334525, by rfl⟩ : syracuseStep 7117469 = 2669051) B2669051
theorem B2136923 : Blo 936583 2136923 := bstep (se 1 (by rfl) ⟨1602692, by rfl⟩ : syracuseStep 2136923 = 3205385) B3205385
theorem B8002475 : Blo 936583 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B5348537 : Blo 936583 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B1580519 : Blo 936583 1580519 := bstep (se 1 (by rfl) ⟨1185389, by rfl⟩ : syracuseStep 1580519 = 2370779) B2370779
theorem B1580539 : Blo 936583 1580539 := bstep (se 1 (by rfl) ⟨1185404, by rfl⟩ : syracuseStep 1580539 = 2370809) B2370809
theorem B3383009 : Blo 936583 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B1580971 : Blo 936583 1580971 := bstep (se 1 (by rfl) ⟨1185728, by rfl⟩ : syracuseStep 1580971 = 2371457) B2371457
theorem B1581275 : Blo 936583 1581275 := bstep (se 1 (by rfl) ⟨1185956, by rfl⟩ : syracuseStep 1581275 = 2371913) B2371913
theorem B6004955 : Blo 936583 6004955 := bstep (se 1 (by rfl) ⟨4503716, by rfl⟩ : syracuseStep 6004955 = 9007433) B9007433
theorem B3252667 : Blo 936583 3252667 := bstep (se 1 (by rfl) ⟨2439500, by rfl⟩ : syracuseStep 3252667 = 4879001) B4879001
theorem B1581511 : Blo 936583 1581511 := bstep (se 1 (by rfl) ⟨1186133, by rfl⟩ : syracuseStep 1581511 = 2372267) B2372267
theorem B1581545 : Blo 936583 1581545 := bstep (se 2 (by rfl) ⟨593079, by rfl⟩ : syracuseStep 1581545 = 1186159) B1186159
theorem B3383785 : Blo 936583 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B18064073 : Blo 936583 18064073 := bstep (se 2 (by rfl) ⟨6774027, by rfl⟩ : syracuseStep 18064073 = 13548055) B13548055
theorem B1778411 : Blo 936583 1778411 := bstep (se 1 (by rfl) ⟨1333808, by rfl⟩ : syracuseStep 1778411 = 2667617) B2667617
theorem B27108107 : Blo 936583 27108107 := bstep (se 1 (by rfl) ⟨20331080, by rfl⟩ : syracuseStep 27108107 = 40662161) B40662161
theorem B5415923 : Blo 936583 5415923 := bstep (se 1 (by rfl) ⟨4061942, by rfl⟩ : syracuseStep 5415923 = 8123885) B8123885
theorem B1057855 : Blo 936583 1057855 := bstep (se 1 (by rfl) ⟨793391, by rfl⟩ : syracuseStep 1057855 = 1586783) B1586783
theorem B1057999 : Blo 936583 1057999 := bstep (se 1 (by rfl) ⟨793499, by rfl⟩ : syracuseStep 1057999 = 1586999) B1586999
theorem B237348791 : Blo 936583 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B2107583 : Blo 936583 2107583 := bstep (se 1 (by rfl) ⟨1580687, by rfl⟩ : syracuseStep 2107583 = 3161375) B3161375
theorem B1583401 : Blo 936583 1583401 := bstep (se 2 (by rfl) ⟨593775, by rfl⟩ : syracuseStep 1583401 = 1187551) B1187551
theorem B2108537 : Blo 936583 2108537 := bstep (se 2 (by rfl) ⟨790701, by rfl⟩ : syracuseStep 2108537 = 1581403) B1581403
theorem B20556935 : Blo 936583 20556935 := bstep (se 1 (by rfl) ⟨15417701, by rfl⟩ : syracuseStep 20556935 = 30835403) B30835403
theorem B1584731 : Blo 936583 1584731 := bstep (se 1 (by rfl) ⟨1188548, by rfl⟩ : syracuseStep 1584731 = 2377097) B2377097
theorem B2109203 : Blo 936583 2109203 := bstep (se 1 (by rfl) ⟨1581902, by rfl⟩ : syracuseStep 2109203 = 3163805) B3163805
theorem B1584967 : Blo 936583 1584967 := bstep (se 1 (by rfl) ⟨1188725, by rfl⟩ : syracuseStep 1584967 = 2377451) B2377451
theorem B2109563 : Blo 936583 2109563 := bstep (se 1 (by rfl) ⟨1582172, by rfl⟩ : syracuseStep 2109563 = 3164345) B3164345
theorem B1782071 : Blo 936583 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B2109833 : Blo 936583 2109833 := bstep (se 2 (by rfl) ⟨791187, by rfl⟩ : syracuseStep 2109833 = 1582375) B1582375
theorem B1585615 : Blo 936583 1585615 := bstep (se 1 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 1585615 = 2378423) B2378423
theorem B2667593 : Blo 936583 2667593 := bstep (se 2 (by rfl) ⟨1000347, by rfl⟩ : syracuseStep 2667593 = 2000695) B2000695
theorem B2110571 : Blo 936583 2110571 := bstep (se 1 (by rfl) ⟨1582928, by rfl⟩ : syracuseStep 2110571 = 3165857) B3165857
theorem B1586351 : Blo 936583 1586351 := bstep (se 1 (by rfl) ⟨1189763, by rfl⟩ : syracuseStep 1586351 = 2379527) B2379527
theorem B13546673 : Blo 936583 13546673 := bstep (se 2 (by rfl) ⟨5080002, by rfl⟩ : syracuseStep 13546673 = 10160005) B10160005
theorem B1586587 : Blo 936583 1586587 := bstep (se 1 (by rfl) ⟨1189940, by rfl⟩ : syracuseStep 1586587 = 2379881) B2379881
theorem B5355143 : Blo 936583 5355143 := bstep (se 1 (by rfl) ⟨4016357, by rfl⟩ : syracuseStep 5355143 = 8032715) B8032715
theorem B2111147 : Blo 936583 2111147 := bstep (se 1 (by rfl) ⟨1583360, by rfl⟩ : syracuseStep 2111147 = 3166721) B3166721
theorem B1586911 : Blo 936583 1586911 := bstep (se 1 (by rfl) ⟨1190183, by rfl⟩ : syracuseStep 1586911 = 2380367) B2380367
theorem B2373371 : Blo 936583 2373371 := bstep (se 1 (by rfl) ⟨1780028, by rfl⟩ : syracuseStep 2373371 = 3560057) B3560057
theorem B2111471 : Blo 936583 2111471 := bstep (se 1 (by rfl) ⟨1583603, by rfl⟩ : syracuseStep 2111471 = 3167207) B3167207
theorem B2111687 : Blo 936583 2111687 := bstep (se 1 (by rfl) ⟨1583765, by rfl⟩ : syracuseStep 2111687 = 3167531) B3167531
theorem B7125245 : Blo 936583 7125245 := bstep (se 3 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 7125245 = 2671967) B2671967
theorem B4012361 : Blo 936583 4012361 := bstep (se 2 (by rfl) ⟨1504635, by rfl⟩ : syracuseStep 4012361 = 3009271) B3009271
theorem B2111867 : Blo 936583 2111867 := bstep (se 1 (by rfl) ⟨1583900, by rfl⟩ : syracuseStep 2111867 = 3167801) B3167801
theorem B2669075 : Blo 936583 2669075 := bstep (se 1 (by rfl) ⟨2001806, by rfl⟩ : syracuseStep 2669075 = 4003613) B4003613
theorem B2112137 : Blo 936583 2112137 := bstep (se 2 (by rfl) ⟨792051, by rfl⟩ : syracuseStep 2112137 = 1584103) B1584103
theorem B2374505 : Blo 936583 2374505 := bstep (se 2 (by rfl) ⟨890439, by rfl⟩ : syracuseStep 2374505 = 1780879) B1780879
theorem B2374697 : Blo 936583 2374697 := bstep (se 2 (by rfl) ⟨890511, by rfl⟩ : syracuseStep 2374697 = 1781023) B1781023
theorem B3161159 : Blo 936583 3161159 := bstep (se 1 (by rfl) ⟨2370869, by rfl⟩ : syracuseStep 3161159 = 4741739) B4741739
theorem B3161213 : Blo 936583 3161213 := bstep (se 3 (by rfl) ⟨592727, by rfl⟩ : syracuseStep 3161213 = 1185455) B1185455
theorem B2112695 : Blo 936583 2112695 := bstep (se 1 (by rfl) ⟨1584521, by rfl⟩ : syracuseStep 2112695 = 3169043) B3169043
theorem B25705691 : Blo 936583 25705691 := bstep (se 1 (by rfl) ⟨19279268, by rfl⟩ : syracuseStep 25705691 = 38558537) B38558537
theorem B4504871 : Blo 936583 4504871 := bstep (se 1 (by rfl) ⟨3378653, by rfl⟩ : syracuseStep 4504871 = 6757307) B6757307
theorem B4013351 : Blo 936583 4013351 := bstep (se 1 (by rfl) ⟨3010013, by rfl⟩ : syracuseStep 4013351 = 6020027) B6020027
theorem B3161483 : Blo 936583 3161483 := bstep (se 1 (by rfl) ⟨2371112, by rfl⟩ : syracuseStep 3161483 = 4742225) B4742225
theorem B4505179 : Blo 936583 4505179 := bstep (se 1 (by rfl) ⟨3378884, by rfl⟩ : syracuseStep 4505179 = 6757769) B6757769
theorem B2113271 : Blo 936583 2113271 := bstep (se 1 (by rfl) ⟨1584953, by rfl⟩ : syracuseStep 2113271 = 3169907) B3169907
theorem B6504203 : Blo 936583 6504203 := bstep (se 1 (by rfl) ⟨4878152, by rfl⟩ : syracuseStep 6504203 = 9756305) B9756305
theorem B2113451 : Blo 936583 2113451 := bstep (se 1 (by rfl) ⟨1585088, by rfl⟩ : syracuseStep 2113451 = 3170177) B3170177
theorem B6012953 : Blo 936583 6012953 := bstep (se 2 (by rfl) ⟨2254857, by rfl⟩ : syracuseStep 6012953 = 4509715) B4509715
theorem B5423129 : Blo 936583 5423129 := bstep (se 2 (by rfl) ⟨2033673, by rfl⟩ : syracuseStep 5423129 = 4067347) B4067347
theorem B2113991 : Blo 936583 2113991 := bstep (se 1 (by rfl) ⟨1585493, by rfl⟩ : syracuseStep 2113991 = 3170987) B3170987
theorem B1688159 : Blo 936583 1688159 := bstep (se 1 (by rfl) ⟨1266119, by rfl⟩ : syracuseStep 1688159 = 2532239) B2532239
theorem B2704175 : Blo 936583 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B2114351 : Blo 936583 2114351 := bstep (se 1 (by rfl) ⟨1585763, by rfl⟩ : syracuseStep 2114351 = 3171527) B3171527
theorem B2573167 : Blo 936583 2573167 := bstep (se 1 (by rfl) ⟨1929875, by rfl⟩ : syracuseStep 2573167 = 3859751) B3859751
theorem B3556457 : Blo 936583 3556457 := bstep (se 2 (by rfl) ⟨1333671, by rfl⟩ : syracuseStep 3556457 = 2667343) B2667343
theorem B4015727 : Blo 936583 4015727 := bstep (se 1 (by rfl) ⟨3011795, by rfl⟩ : syracuseStep 4015727 = 6023591) B6023591
theorem B4015777 : Blo 936583 4015777 := bstep (se 2 (by rfl) ⟨1505916, by rfl⟩ : syracuseStep 4015777 = 3011833) B3011833
theorem B1427195 : Blo 936583 1427195 := bstep (se 1 (by rfl) ⟨1070396, by rfl⟩ : syracuseStep 1427195 = 2140793) B2140793
theorem B2115359 : Blo 936583 2115359 := bstep (se 1 (by rfl) ⟨1586519, by rfl⟩ : syracuseStep 2115359 = 3173039) B3173039
theorem B1689407 : Blo 936583 1689407 := bstep (se 1 (by rfl) ⟨1267055, by rfl⟩ : syracuseStep 1689407 = 2534111) B2534111
theorem B1001279 : Blo 936583 1001279 := bstep (se 1 (by rfl) ⟨750959, by rfl⟩ : syracuseStep 1001279 = 1501919) B1501919
theorem B2115575 : Blo 936583 2115575 := bstep (se 1 (by rfl) ⟨1586681, by rfl⟩ : syracuseStep 2115575 = 3173363) B3173363
theorem B3164507 : Blo 936583 3164507 := bstep (se 1 (by rfl) ⟨2373380, by rfl⟩ : syracuseStep 3164507 = 4746761) B4746761
theorem B2115935 : Blo 936583 2115935 := bstep (se 1 (by rfl) ⟨1586951, by rfl⟩ : syracuseStep 2115935 = 3173903) B3173903
theorem B3164777 : Blo 936583 3164777 := bstep (se 2 (by rfl) ⟨1186791, by rfl⟩ : syracuseStep 3164777 = 2373583) B2373583
theorem B27118253 : Blo 936583 27118253 := bstep (se 3 (by rfl) ⟨5084672, by rfl⟩ : syracuseStep 27118253 = 10169345) B10169345
theorem B936795 : Blo 936583 936795 := bstep (se 1 (by rfl) ⟨702596, by rfl⟩ : syracuseStep 936795 = 1405193) B1405193
theorem B936863 : Blo 936583 936863 := bstep (se 1 (by rfl) ⟨702647, by rfl⟩ : syracuseStep 936863 = 1405295) B1405295
theorem B937007 : Blo 936583 937007 := bstep (se 1 (by rfl) ⟨702755, by rfl⟩ : syracuseStep 937007 = 1405511) B1405511
theorem B937031 : Blo 936583 937031 := bstep (se 1 (by rfl) ⟨702773, by rfl⟩ : syracuseStep 937031 = 1405547) B1405547
theorem B3558599 : Blo 936583 3558599 := bstep (se 1 (by rfl) ⟨2668949, by rfl⟩ : syracuseStep 3558599 = 5337899) B5337899
theorem B937183 : Blo 936583 937183 := bstep (se 1 (by rfl) ⟨702887, by rfl⟩ : syracuseStep 937183 = 1405775) B1405775
theorem B2674109 : Blo 936583 2674109 := bstep (se 3 (by rfl) ⟨501395, by rfl⟩ : syracuseStep 2674109 = 1002791) B1002791
theorem B937447 : Blo 936583 937447 := bstep (se 1 (by rfl) ⟨703085, by rfl⟩ : syracuseStep 937447 = 1406171) B1406171
theorem B937563 : Blo 936583 937563 := bstep (se 1 (by rfl) ⟨703172, by rfl⟩ : syracuseStep 937563 = 1406345) B1406345
theorem B3165803 : Blo 936583 3165803 := bstep (se 1 (by rfl) ⟨2374352, by rfl⟩ : syracuseStep 3165803 = 4748705) B4748705
theorem B6016619 : Blo 936583 6016619 := bstep (se 1 (by rfl) ⟨4512464, by rfl⟩ : syracuseStep 6016619 = 9024929) B9024929
theorem B2674451 : Blo 936583 2674451 := bstep (se 1 (by rfl) ⟨2005838, by rfl⟩ : syracuseStep 2674451 = 4011677) B4011677
theorem B1691431 : Blo 936583 1691431 := bstep (se 1 (by rfl) ⟨1268573, by rfl⟩ : syracuseStep 1691431 = 2537147) B2537147
theorem B937799 : Blo 936583 937799 := bstep (se 1 (by rfl) ⟨703349, by rfl⟩ : syracuseStep 937799 = 1406699) B1406699
theorem B3166073 : Blo 936583 3166073 := bstep (se 2 (by rfl) ⟨1187277, by rfl⟩ : syracuseStep 3166073 = 2374555) B2374555
theorem B937951 : Blo 936583 937951 := bstep (se 1 (by rfl) ⟨703463, by rfl⟩ : syracuseStep 937951 = 1406927) B1406927
theorem B27086885 : Blo 936583 27086885 := bstep (se 4 (by rfl) ⟨2539395, by rfl⟩ : syracuseStep 27086885 = 5078791) B5078791
theorem B3166397 : Blo 936583 3166397 := bstep (se 3 (by rfl) ⟨593699, by rfl⟩ : syracuseStep 3166397 = 1187399) B1187399
theorem B938215 : Blo 936583 938215 := bstep (se 1 (by rfl) ⟨703661, by rfl⟩ : syracuseStep 938215 = 1407323) B1407323
theorem B3002633 : Blo 936583 3002633 := bstep (se 2 (by rfl) ⟨1125987, by rfl⟩ : syracuseStep 3002633 = 2251975) B2251975
theorem B22794533 : Blo 936583 22794533 := bstep (se 4 (by rfl) ⟨2136987, by rfl⟩ : syracuseStep 22794533 = 4273975) B4273975
theorem B938367 : Blo 936583 938367 := bstep (se 1 (by rfl) ⟨703775, by rfl⟩ : syracuseStep 938367 = 1407551) B1407551
theorem B938447 : Blo 936583 938447 := bstep (se 1 (by rfl) ⟨703835, by rfl⟩ : syracuseStep 938447 = 1407671) B1407671
theorem B938599 : Blo 936583 938599 := bstep (se 1 (by rfl) ⟨703949, by rfl⟩ : syracuseStep 938599 = 1407899) B1407899
theorem B8245961 : Blo 936583 8245961 := bstep (se 2 (by rfl) ⟨3092235, by rfl⟩ : syracuseStep 8245961 = 6184471) B6184471
theorem B938863 : Blo 936583 938863 := bstep (se 1 (by rfl) ⟨704147, by rfl⟩ : syracuseStep 938863 = 1408295) B1408295
theorem B938919 : Blo 936583 938919 := bstep (se 1 (by rfl) ⟨704189, by rfl⟩ : syracuseStep 938919 = 1408379) B1408379
theorem B939003 : Blo 936583 939003 := bstep (se 1 (by rfl) ⟨704252, by rfl⟩ : syracuseStep 939003 = 1408505) B1408505
theorem B3003401 : Blo 936583 3003401 := bstep (se 2 (by rfl) ⟨1126275, by rfl⟩ : syracuseStep 3003401 = 2252551) B2252551
theorem B939071 : Blo 936583 939071 := bstep (se 1 (by rfl) ⟨704303, by rfl⟩ : syracuseStep 939071 = 1408607) B1408607
theorem B939215 : Blo 936583 939215 := bstep (se 1 (by rfl) ⟨704411, by rfl⟩ : syracuseStep 939215 = 1408823) B1408823
theorem B6018259 : Blo 936583 6018259 := bstep (se 1 (by rfl) ⟨4513694, by rfl⟩ : syracuseStep 6018259 = 9027389) B9027389
theorem B3167585 : Blo 936583 3167585 := bstep (se 2 (by rfl) ⟨1187844, by rfl⟩ : syracuseStep 3167585 = 2375689) B2375689
theorem B939419 : Blo 936583 939419 := bstep (se 1 (by rfl) ⟨704564, by rfl⟩ : syracuseStep 939419 = 1409129) B1409129
theorem B939631 : Blo 936583 939631 := bstep (se 1 (by rfl) ⟨704723, by rfl⟩ : syracuseStep 939631 = 1409447) B1409447
theorem B939687 : Blo 936583 939687 := bstep (se 1 (by rfl) ⟨704765, by rfl⟩ : syracuseStep 939687 = 1409531) B1409531
theorem B939771 : Blo 936583 939771 := bstep (se 1 (by rfl) ⟨704828, by rfl⟩ : syracuseStep 939771 = 1409657) B1409657
theorem B939807 : Blo 936583 939807 := bstep (se 1 (by rfl) ⟨704855, by rfl⟩ : syracuseStep 939807 = 1409711) B1409711
theorem B939839 : Blo 936583 939839 := bstep (se 1 (by rfl) ⟨704879, by rfl⟩ : syracuseStep 939839 = 1409759) B1409759
theorem B940015 : Blo 936583 940015 := bstep (se 1 (by rfl) ⟨705011, by rfl⟩ : syracuseStep 940015 = 1410023) B1410023
theorem B1267807 : Blo 936583 1267807 := bstep (se 1 (by rfl) ⟨950855, by rfl⟩ : syracuseStep 1267807 = 1901711) B1901711
theorem B940187 : Blo 936583 940187 := bstep (se 1 (by rfl) ⟨705140, by rfl⟩ : syracuseStep 940187 = 1410281) B1410281
theorem B940223 : Blo 936583 940223 := bstep (se 1 (by rfl) ⟨705167, by rfl⟩ : syracuseStep 940223 = 1410335) B1410335
theorem B2676979 : Blo 936583 2676979 := bstep (se 1 (by rfl) ⟨2007734, by rfl⟩ : syracuseStep 2676979 = 4015469) B4015469
theorem B940335 : Blo 936583 940335 := bstep (se 1 (by rfl) ⟨705251, by rfl⟩ : syracuseStep 940335 = 1410503) B1410503
theorem B17127787 : Blo 936583 17127787 := bstep (se 1 (by rfl) ⟨12845840, by rfl⟩ : syracuseStep 17127787 = 25691681) B25691681
theorem B940571 : Blo 936583 940571 := bstep (se 1 (by rfl) ⟨705428, by rfl⟩ : syracuseStep 940571 = 1410857) B1410857
theorem B940575 : Blo 936583 940575 := bstep (se 1 (by rfl) ⟨705431, by rfl⟩ : syracuseStep 940575 = 1410863) B1410863
theorem B1333865 : Blo 936583 1333865 := bstep (se 2 (by rfl) ⟨500199, by rfl⟩ : syracuseStep 1333865 = 1000399) B1000399
theorem B5069449 : Blo 936583 5069449 := bstep (se 2 (by rfl) ⟨1901043, by rfl⟩ : syracuseStep 5069449 = 3802087) B3802087
theorem B3857053 : Blo 936583 3857053 := bstep (se 3 (by rfl) ⟨723197, by rfl⟩ : syracuseStep 3857053 = 1446395) B1446395
theorem B2251745 : Blo 936583 2251745 := bstep (se 2 (by rfl) ⟨844404, by rfl⟩ : syracuseStep 2251745 = 1688809) B1688809
theorem B3562487 : Blo 936583 3562487 := bstep (se 1 (by rfl) ⟨2671865, by rfl⟩ : syracuseStep 3562487 = 5343731) B5343731
theorem B3169529 : Blo 936583 3169529 := bstep (se 2 (by rfl) ⟨1188573, by rfl⟩ : syracuseStep 3169529 = 2377147) B2377147
theorem B22797733 : Blo 936583 22797733 := bstep (se 4 (by rfl) ⟨2137287, by rfl⟩ : syracuseStep 22797733 = 4274575) B4274575
theorem B2252243 : Blo 936583 2252243 := bstep (se 1 (by rfl) ⟨1689182, by rfl⟩ : syracuseStep 2252243 = 3378365) B3378365
theorem B3169799 : Blo 936583 3169799 := bstep (se 1 (by rfl) ⟨2377349, by rfl⟩ : syracuseStep 3169799 = 4754699) B4754699
theorem B6413833 : Blo 936583 6413833 := bstep (se 2 (by rfl) ⟨2405187, by rfl⟩ : syracuseStep 6413833 = 4810375) B4810375
theorem B4743035 : Blo 936583 4743035 := bstep (se 1 (by rfl) ⟨3557276, by rfl⟩ : syracuseStep 4743035 = 7114553) B7114553
theorem B6021053 : Blo 936583 6021053 := bstep (se 3 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 6021053 = 2257895) B2257895
theorem B3006503 : Blo 936583 3006503 := bstep (se 1 (by rfl) ⟨2254877, by rfl⟩ : syracuseStep 3006503 = 4509755) B4509755
theorem B7135451 : Blo 936583 7135451 := bstep (se 1 (by rfl) ⟨5351588, by rfl⟩ : syracuseStep 7135451 = 10703177) B10703177
theorem B19292417 : Blo 936583 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B4743521 : Blo 936583 4743521 := bstep (se 2 (by rfl) ⟨1778820, by rfl⟩ : syracuseStep 4743521 = 3557641) B3557641
theorem B3170879 : Blo 936583 3170879 := bstep (se 1 (by rfl) ⟨2378159, by rfl⟩ : syracuseStep 3170879 = 4756319) B4756319
theorem B8020619 : Blo 936583 8020619 := bstep (se 1 (by rfl) ⟨6015464, by rfl⟩ : syracuseStep 8020619 = 12030929) B12030929
theorem B10838863 : Blo 936583 10838863 := bstep (se 1 (by rfl) ⟨8129147, by rfl⟩ : syracuseStep 10838863 = 16258295) B16258295
theorem B1500265 : Blo 936583 1500265 := bstep (se 2 (by rfl) ⟨562599, by rfl⟩ : syracuseStep 1500265 = 1125199) B1125199
theorem B109765925 : Blo 936583 109765925 := bstep (se 4 (by rfl) ⟨10290555, by rfl⟩ : syracuseStep 109765925 = 20581111) B20581111
theorem B1336667 : Blo 936583 1336667 := bstep (se 1 (by rfl) ⟨1002500, by rfl⟩ : syracuseStep 1336667 = 2005001) B2005001
theorem B3172175 : Blo 936583 3172175 := bstep (se 1 (by rfl) ⟨2379131, by rfl⟩ : syracuseStep 3172175 = 4758263) B4758263
theorem B9037655 : Blo 936583 9037655 := bstep (se 1 (by rfl) ⟨6778241, by rfl⟩ : syracuseStep 9037655 = 13556483) B13556483
theorem B12839057 : Blo 936583 12839057 := bstep (se 2 (by rfl) ⟨4814646, by rfl⟩ : syracuseStep 12839057 = 9629293) B9629293
theorem B3172499 : Blo 936583 3172499 := bstep (se 1 (by rfl) ⟨2379374, by rfl⟩ : syracuseStep 3172499 = 4758749) B4758749
theorem B1337647 : Blo 936583 1337647 := bstep (se 1 (by rfl) ⟨1003235, by rfl⟩ : syracuseStep 1337647 = 2006471) B2006471
theorem B3172769 : Blo 936583 3172769 := bstep (se 2 (by rfl) ⟨1189788, by rfl⟩ : syracuseStep 3172769 = 2379577) B2379577
theorem B5794213 : Blo 936583 5794213 := bstep (se 4 (by rfl) ⟨543207, by rfl⟩ : syracuseStep 5794213 = 1086415) B1086415
theorem B6023717 : Blo 936583 6023717 := bstep (se 4 (by rfl) ⟨564723, by rfl⟩ : syracuseStep 6023717 = 1129447) B1129447
theorem B6777719 : Blo 936583 6777719 := bstep (se 1 (by rfl) ⟨5083289, by rfl⟩ : syracuseStep 6777719 = 10166579) B10166579
theorem B1502111 : Blo 936583 1502111 := bstep (se 1 (by rfl) ⟨1126583, by rfl⟩ : syracuseStep 1502111 = 2253167) B2253167
theorem B1338319 : Blo 936583 1338319 := bstep (se 1 (by rfl) ⟨1003739, by rfl⟩ : syracuseStep 1338319 = 2007479) B2007479
theorem B36137987 : Blo 936583 36137987 := bstep (se 1 (by rfl) ⟨27103490, by rfl⟩ : syracuseStep 36137987 = 54206981) B54206981
theorem B1338439 : Blo 936583 1338439 := bstep (se 1 (by rfl) ⟨1003829, by rfl⟩ : syracuseStep 1338439 = 2007659) B2007659
theorem B1502329 : Blo 936583 1502329 := bstep (se 2 (by rfl) ⟨563373, by rfl⟩ : syracuseStep 1502329 = 1126747) B1126747
theorem B11398477 : Blo 936583 11398477 := bstep (se 3 (by rfl) ⟨2137214, by rfl⟩ : syracuseStep 11398477 = 4274429) B4274429
theorem B15199787 : Blo 936583 15199787 := bstep (se 1 (by rfl) ⟨11399840, by rfl⟩ : syracuseStep 15199787 = 22799681) B22799681
theorem B5336873 : Blo 936583 5336873 := bstep (se 2 (by rfl) ⟨2001327, by rfl⟩ : syracuseStep 5336873 = 4002655) B4002655
theorem B2256779 : Blo 936583 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B12513337 : Blo 936583 12513337 := bstep (se 2 (by rfl) ⟨4692501, by rfl⟩ : syracuseStep 12513337 = 9385003) B9385003
theorem B10678391 : Blo 936583 10678391 := bstep (se 1 (by rfl) ⟨8008793, by rfl⟩ : syracuseStep 10678391 = 16017587) B16017587
theorem B5337373 : Blo 936583 5337373 := bstep (se 3 (by rfl) ⟨1000757, by rfl⟩ : syracuseStep 5337373 = 2001515) B2001515
theorem B1405391 : Blo 936583 1405391 := bstep (se 1 (by rfl) ⟨1054043, by rfl⟩ : syracuseStep 1405391 = 2108087) B2108087
theorem B1405433 : Blo 936583 1405433 := bstep (se 2 (by rfl) ⟨527037, by rfl⟩ : syracuseStep 1405433 = 1054075) B1054075
theorem B3568121 : Blo 936583 3568121 := bstep (se 2 (by rfl) ⟨1338045, by rfl⟩ : syracuseStep 3568121 = 2676091) B2676091
theorem B1405535 : Blo 936583 1405535 := bstep (se 1 (by rfl) ⟨1054151, by rfl⟩ : syracuseStep 1405535 = 2108303) B2108303
theorem B8024993 : Blo 936583 8024993 := bstep (se 2 (by rfl) ⟨3009372, by rfl⟩ : syracuseStep 8024993 = 6018745) B6018745
theorem B1406015 : Blo 936583 1406015 := bstep (se 1 (by rfl) ⟨1054511, by rfl⟩ : syracuseStep 1406015 = 2109023) B2109023
theorem B1406057 : Blo 936583 1406057 := bstep (se 2 (by rfl) ⟨527271, by rfl⟩ : syracuseStep 1406057 = 1054543) B1054543
theorem B1406159 : Blo 936583 1406159 := bstep (se 1 (by rfl) ⟨1054619, by rfl⟩ : syracuseStep 1406159 = 2109239) B2109239
theorem B9008435 : Blo 936583 9008435 := bstep (se 1 (by rfl) ⟨6756326, by rfl⟩ : syracuseStep 9008435 = 13512653) B13512653
theorem B1406363 : Blo 936583 1406363 := bstep (se 1 (by rfl) ⟨1054772, by rfl⟩ : syracuseStep 1406363 = 2109545) B2109545
theorem B7140797 : Blo 936583 7140797 := bstep (se 3 (by rfl) ⟨1338899, by rfl⟩ : syracuseStep 7140797 = 2677799) B2677799
theorem B19559981 : Blo 936583 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B3012167 : Blo 936583 3012167 := bstep (se 1 (by rfl) ⟨2259125, by rfl⟩ : syracuseStep 3012167 = 4518251) B4518251
theorem B1406585 : Blo 936583 1406585 := bstep (se 2 (by rfl) ⟨527469, by rfl⟩ : syracuseStep 1406585 = 1054939) B1054939
theorem B4519633 : Blo 936583 4519633 := bstep (se 2 (by rfl) ⟨1694862, by rfl⟩ : syracuseStep 4519633 = 3389725) B3389725
theorem B1406687 : Blo 936583 1406687 := bstep (se 1 (by rfl) ⟨1055015, by rfl⟩ : syracuseStep 1406687 = 2110031) B2110031
theorem B1406783 : Blo 936583 1406783 := bstep (se 1 (by rfl) ⟨1055087, by rfl⟩ : syracuseStep 1406783 = 2110175) B2110175
theorem B1406951 : Blo 936583 1406951 := bstep (se 1 (by rfl) ⟨1055213, by rfl⟩ : syracuseStep 1406951 = 2110427) B2110427
theorem B1406969 : Blo 936583 1406969 := bstep (se 2 (by rfl) ⟨527613, by rfl⟩ : syracuseStep 1406969 = 1055227) B1055227
theorem B25720915 : Blo 936583 25720915 := bstep (se 1 (by rfl) ⟨19290686, by rfl⟩ : syracuseStep 25720915 = 38581373) B38581373
theorem B1407071 : Blo 936583 1407071 := bstep (se 1 (by rfl) ⟨1055303, by rfl⟩ : syracuseStep 1407071 = 2110607) B2110607
theorem B1407131 : Blo 936583 1407131 := bstep (se 1 (by rfl) ⟨1055348, by rfl⟩ : syracuseStep 1407131 = 2110697) B2110697
theorem B1407167 : Blo 936583 1407167 := bstep (se 1 (by rfl) ⟨1055375, by rfl⟩ : syracuseStep 1407167 = 2110751) B2110751
theorem B1407209 : Blo 936583 1407209 := bstep (se 2 (by rfl) ⟨527703, by rfl⟩ : syracuseStep 1407209 = 1055407) B1055407
theorem B4749677 : Blo 936583 4749677 := bstep (se 3 (by rfl) ⟨890564, by rfl⟩ : syracuseStep 4749677 = 1781129) B1781129
theorem B1407515 : Blo 936583 1407515 := bstep (se 1 (by rfl) ⟨1055636, by rfl⟩ : syracuseStep 1407515 = 2111273) B2111273
theorem B1407593 : Blo 936583 1407593 := bstep (se 2 (by rfl) ⟨527847, by rfl⟩ : syracuseStep 1407593 = 1055695) B1055695
theorem B13531859 : Blo 936583 13531859 := bstep (se 1 (by rfl) ⟨10148894, by rfl⟩ : syracuseStep 13531859 = 20297789) B20297789
theorem B19528613 : Blo 936583 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B3210311 : Blo 936583 3210311 := bstep (se 1 (by rfl) ⟨2407733, by rfl⟩ : syracuseStep 3210311 = 4815467) B4815467
theorem B1408121 : Blo 936583 1408121 := bstep (se 2 (by rfl) ⟨528045, by rfl⟩ : syracuseStep 1408121 = 1056091) B1056091
theorem B5340289 : Blo 936583 5340289 := bstep (se 2 (by rfl) ⟨2002608, by rfl⟩ : syracuseStep 5340289 = 4005217) B4005217
theorem B1408223 : Blo 936583 1408223 := bstep (se 1 (by rfl) ⟨1056167, by rfl⟩ : syracuseStep 1408223 = 2112335) B2112335
theorem B1408265 : Blo 936583 1408265 := bstep (se 2 (by rfl) ⟨528099, by rfl⟩ : syracuseStep 1408265 = 1056199) B1056199
theorem B1408367 : Blo 936583 1408367 := bstep (se 1 (by rfl) ⟨1056275, by rfl⟩ : syracuseStep 1408367 = 2112551) B2112551
theorem B1408487 : Blo 936583 1408487 := bstep (se 1 (by rfl) ⟨1056365, by rfl⟩ : syracuseStep 1408487 = 2112731) B2112731
theorem B1408619 : Blo 936583 1408619 := bstep (se 1 (by rfl) ⟨1056464, by rfl⟩ : syracuseStep 1408619 = 2112929) B2112929
theorem B5340815 : Blo 936583 5340815 := bstep (se 1 (by rfl) ⟨4005611, by rfl⟩ : syracuseStep 5340815 = 8011223) B8011223
theorem B1408745 : Blo 936583 1408745 := bstep (se 2 (by rfl) ⟨528279, by rfl⟩ : syracuseStep 1408745 = 1056559) B1056559
theorem B1408889 : Blo 936583 1408889 := bstep (se 2 (by rfl) ⟨528333, by rfl⟩ : syracuseStep 1408889 = 1056667) B1056667
theorem B1408991 : Blo 936583 1408991 := bstep (se 1 (by rfl) ⟨1056743, by rfl⟩ : syracuseStep 1408991 = 2113487) B2113487
theorem B1409327 : Blo 936583 1409327 := bstep (se 1 (by rfl) ⟨1056995, by rfl⟩ : syracuseStep 1409327 = 2113991) B2113991
theorem B1802783 : Blo 936583 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B1409567 : Blo 936583 1409567 := bstep (se 1 (by rfl) ⟨1057175, by rfl⟩ : syracuseStep 1409567 = 2114351) B2114351
theorem B14451817 : Blo 936583 14451817 := bstep (se 2 (by rfl) ⟨5419431, by rfl⟩ : syracuseStep 14451817 = 10838863) B10838863
theorem B951463 : Blo 936583 951463 := bstep (se 1 (by rfl) ⟨713597, by rfl⟩ : syracuseStep 951463 = 1427195) B1427195
theorem B1410239 : Blo 936583 1410239 := bstep (se 1 (by rfl) ⟨1057679, by rfl⟩ : syracuseStep 1410239 = 2115359) B2115359
theorem B1410383 : Blo 936583 1410383 := bstep (se 1 (by rfl) ⟨1057787, by rfl⟩ : syracuseStep 1410383 = 2115575) B2115575
theorem B1410473 : Blo 936583 1410473 := bstep (se 2 (by rfl) ⟨528927, by rfl⟩ : syracuseStep 1410473 = 1057855) B1057855
theorem B1410623 : Blo 936583 1410623 := bstep (se 1 (by rfl) ⟨1057967, by rfl⟩ : syracuseStep 1410623 = 2115935) B2115935
theorem B1410665 : Blo 936583 1410665 := bstep (se 2 (by rfl) ⟨528999, by rfl⟩ : syracuseStep 1410665 = 1057999) B1057999
theorem B18057923 : Blo 936583 18057923 := bstep (se 1 (by rfl) ⟨13543442, by rfl⟩ : syracuseStep 18057923 = 27086885) B27086885
theorem B2001755 : Blo 936583 2001755 := bstep (se 1 (by rfl) ⟨1501316, by rfl⟩ : syracuseStep 2001755 = 3002633) B3002633
theorem B7113581 : Blo 936583 7113581 := bstep (se 3 (by rfl) ⟨1333796, by rfl⟩ : syracuseStep 7113581 = 2667593) B2667593
theorem B2002267 : Blo 936583 2002267 := bstep (se 1 (by rfl) ⟨1501700, by rfl⟩ : syracuseStep 2002267 = 3003401) B3003401
theorem B27037061 : Blo 936583 27037061 := bstep (se 4 (by rfl) ⟨2534724, by rfl⟩ : syracuseStep 27037061 = 5069449) B5069449
theorem B34312085 : Blo 936583 34312085 := bstep (se 6 (by rfl) ⟨804189, by rfl⟩ : syracuseStep 34312085 = 1608379) B1608379
theorem B1904735 : Blo 936583 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B3805319 : Blo 936583 3805319 := bstep (se 1 (by rfl) ⟨2853989, by rfl⟩ : syracuseStep 3805319 = 5707979) B5707979
theorem B2003105 : Blo 936583 2003105 := bstep (se 2 (by rfl) ⟨751164, by rfl⟩ : syracuseStep 2003105 = 1502329) B1502329
theorem B1053679 : Blo 936583 1053679 := bstep (se 1 (by rfl) ⟨790259, by rfl⟩ : syracuseStep 1053679 = 1580519) B1580519
theorem B2004335 : Blo 936583 2004335 := bstep (se 1 (by rfl) ⟨1503251, by rfl⟩ : syracuseStep 2004335 = 3006503) B3006503
theorem B1054183 : Blo 936583 1054183 := bstep (se 1 (by rfl) ⟨790637, by rfl⟩ : syracuseStep 1054183 = 1581275) B1581275
theorem B4756967 : Blo 936583 4756967 := bstep (se 1 (by rfl) ⟨3567725, by rfl⟩ : syracuseStep 4756967 = 7135451) B7135451
theorem B1054363 : Blo 936583 1054363 := bstep (se 1 (by rfl) ⟨790772, by rfl⟩ : syracuseStep 1054363 = 1581545) B1581545
theorem B7116497 : Blo 936583 7116497 := bstep (se 2 (by rfl) ⟨2668686, by rfl⟩ : syracuseStep 7116497 = 5337373) B5337373
theorem B5347079 : Blo 936583 5347079 := bstep (se 1 (by rfl) ⟨4010309, by rfl⟩ : syracuseStep 5347079 = 8020619) B8020619
theorem B1185607 : Blo 936583 1185607 := bstep (se 1 (by rfl) ⟨889205, by rfl⟩ : syracuseStep 1185607 = 1778411) B1778411
theorem B8001413 : Blo 936583 8001413 := bstep (se 4 (by rfl) ⟨750132, by rfl⟩ : syracuseStep 8001413 = 1500265) B1500265
theorem B73177283 : Blo 936583 73177283 := bstep (se 1 (by rfl) ⟨54882962, by rfl⟩ : syracuseStep 73177283 = 109765925) B109765925
theorem B8559371 : Blo 936583 8559371 := bstep (se 1 (by rfl) ⟨6419528, by rfl⟩ : syracuseStep 8559371 = 12839057) B12839057
theorem B24091991 : Blo 936583 24091991 := bstep (se 1 (by rfl) ⟨18068993, by rfl⟩ : syracuseStep 24091991 = 36137987) B36137987
theorem B13704623 : Blo 936583 13704623 := bstep (se 1 (by rfl) ⟨10278467, by rfl⟩ : syracuseStep 13704623 = 20556935) B20556935
theorem B10133191 : Blo 936583 10133191 := bstep (se 1 (by rfl) ⟨7599893, by rfl⟩ : syracuseStep 10133191 = 15199787) B15199787
theorem B1056487 : Blo 936583 1056487 := bstep (se 1 (by rfl) ⟨792365, by rfl⟩ : syracuseStep 1056487 = 1584731) B1584731
theorem B7118927 : Blo 936583 7118927 := bstep (se 1 (by rfl) ⟨5339195, by rfl⟩ : syracuseStep 7118927 = 10678391) B10678391
theorem B8560829 : Blo 936583 8560829 := bstep (se 3 (by rfl) ⟨1605155, by rfl⟩ : syracuseStep 8560829 = 3210311) B3210311
theorem B1188047 : Blo 936583 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B5349995 : Blo 936583 5349995 := bstep (se 1 (by rfl) ⟨4012496, by rfl⟩ : syracuseStep 5349995 = 8024993) B8024993
theorem B1057567 : Blo 936583 1057567 := bstep (se 1 (by rfl) ⟨793175, by rfl⟩ : syracuseStep 1057567 = 1586351) B1586351
theorem B6005623 : Blo 936583 6005623 := bstep (se 1 (by rfl) ⟨4504217, by rfl⟩ : syracuseStep 6005623 = 9008435) B9008435
theorem B4760531 : Blo 936583 4760531 := bstep (se 1 (by rfl) ⟨3570398, by rfl⟩ : syracuseStep 4760531 = 7140797) B7140797
theorem B2008111 : Blo 936583 2008111 := bstep (se 1 (by rfl) ⟨1506083, by rfl⟩ : syracuseStep 2008111 = 3012167) B3012167
theorem B1582247 : Blo 936583 1582247 := bstep (se 1 (by rfl) ⟨1186685, by rfl⟩ : syracuseStep 1582247 = 2373371) B2373371
theorem B6005981 : Blo 936583 6005981 := bstep (se 3 (by rfl) ⟨1126121, by rfl⟩ : syracuseStep 6005981 = 2252243) B2252243
theorem B7120385 : Blo 936583 7120385 := bstep (se 2 (by rfl) ⟨2670144, by rfl⟩ : syracuseStep 7120385 = 5340289) B5340289
theorem B9020965 : Blo 936583 9020965 := bstep (se 4 (by rfl) ⟨845715, by rfl⟩ : syracuseStep 9020965 = 1691431) B1691431
theorem B1779383 : Blo 936583 1779383 := bstep (se 1 (by rfl) ⟨1334537, by rfl⟩ : syracuseStep 1779383 = 2669075) B2669075
theorem B9021239 : Blo 936583 9021239 := bstep (se 1 (by rfl) ⟨6765929, by rfl⟩ : syracuseStep 9021239 = 13531859) B13531859
theorem B1583003 : Blo 936583 1583003 := bstep (se 1 (by rfl) ⟨1187252, by rfl⟩ : syracuseStep 1583003 = 2374505) B2374505
theorem B13019075 : Blo 936583 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B2107385 : Blo 936583 2107385 := bstep (se 2 (by rfl) ⟨790269, by rfl⟩ : syracuseStep 2107385 = 1580539) B1580539
theorem B1583131 : Blo 936583 1583131 := bstep (se 1 (by rfl) ⟨1187348, by rfl⟩ : syracuseStep 1583131 = 2374697) B2374697
theorem B2107439 : Blo 936583 2107439 := bstep (se 1 (by rfl) ⟨1580579, by rfl⟩ : syracuseStep 2107439 = 3161159) B3161159
theorem B2107475 : Blo 936583 2107475 := bstep (se 1 (by rfl) ⟨1580606, by rfl⟩ : syracuseStep 2107475 = 3161213) B3161213
theorem B6006905 : Blo 936583 6006905 := bstep (se 2 (by rfl) ⟨2252589, by rfl⟩ : syracuseStep 6006905 = 4505179) B4505179
theorem B2107655 : Blo 936583 2107655 := bstep (se 1 (by rfl) ⟨1580741, by rfl⟩ : syracuseStep 2107655 = 3161483) B3161483
theorem B4336135 : Blo 936583 4336135 := bstep (se 1 (by rfl) ⟨3252101, by rfl⟩ : syracuseStep 4336135 = 6504203) B6504203
theorem B2107961 : Blo 936583 2107961 := bstep (se 2 (by rfl) ⟨790485, by rfl⟩ : syracuseStep 2107961 = 1580971) B1580971
theorem B4008635 : Blo 936583 4008635 := bstep (se 1 (by rfl) ⟨3006476, by rfl⟩ : syracuseStep 4008635 = 6012953) B6012953
theorem B3615419 : Blo 936583 3615419 := bstep (se 1 (by rfl) ⟨2711564, by rfl⟩ : syracuseStep 3615419 = 5423129) B5423129
theorem B6007931 : Blo 936583 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B2108681 : Blo 936583 2108681 := bstep (se 2 (by rfl) ⟨790755, by rfl⟩ : syracuseStep 2108681 = 1581511) B1581511
theorem B16035083 : Blo 936583 16035083 := bstep (se 1 (by rfl) ⟨12026312, by rfl⟩ : syracuseStep 16035083 = 24052625) B24052625
theorem B5877011 : Blo 936583 5877011 := bstep (se 1 (by rfl) ⟨4407758, by rfl⟩ : syracuseStep 5877011 = 8815517) B8815517
theorem B7122329 : Blo 936583 7122329 := bstep (se 2 (by rfl) ⟨2670873, by rfl⟩ : syracuseStep 7122329 = 5341747) B5341747
theorem B2370971 : Blo 936583 2370971 := bstep (se 1 (by rfl) ⟨1778228, by rfl⟩ : syracuseStep 2370971 = 3556457) B3556457
theorem B1126271 : Blo 936583 1126271 := bstep (se 1 (by rfl) ⟨844703, by rfl⟩ : syracuseStep 1126271 = 1689407) B1689407
theorem B5353411 : Blo 936583 5353411 := bstep (se 1 (by rfl) ⟨4015058, by rfl⟩ : syracuseStep 5353411 = 8030117) B8030117
theorem B2109671 : Blo 936583 2109671 := bstep (se 1 (by rfl) ⟨1582253, by rfl⟩ : syracuseStep 2109671 = 3164507) B3164507
theorem B4501757 : Blo 936583 4501757 := bstep (se 3 (by rfl) ⟨844079, by rfl⟩ : syracuseStep 4501757 = 1688159) B1688159
theorem B2109851 : Blo 936583 2109851 := bstep (se 1 (by rfl) ⟨1582388, by rfl⟩ : syracuseStep 2109851 = 3164777) B3164777
theorem B2372399 : Blo 936583 2372399 := bstep (se 1 (by rfl) ⟨1779299, by rfl⟩ : syracuseStep 2372399 = 3558599) B3558599
theorem B5354369 : Blo 936583 5354369 := bstep (se 2 (by rfl) ⟨2007888, by rfl⟩ : syracuseStep 5354369 = 4015777) B4015777
theorem B2667401 : Blo 936583 2667401 := bstep (se 2 (by rfl) ⟨1000275, by rfl⟩ : syracuseStep 2667401 = 2000551) B2000551
theorem B1782739 : Blo 936583 1782739 := bstep (se 1 (by rfl) ⟨1337054, by rfl⟩ : syracuseStep 1782739 = 2674109) B2674109
theorem B2110535 : Blo 936583 2110535 := bstep (se 1 (by rfl) ⟨1582901, by rfl⟩ : syracuseStep 2110535 = 3165803) B3165803
theorem B4011079 : Blo 936583 4011079 := bstep (se 1 (by rfl) ⟨3008309, by rfl⟩ : syracuseStep 4011079 = 6016619) B6016619
theorem B1782967 : Blo 936583 1782967 := bstep (se 1 (by rfl) ⟨1337225, by rfl⟩ : syracuseStep 1782967 = 2674451) B2674451
theorem B2110715 : Blo 936583 2110715 := bstep (se 1 (by rfl) ⟨1583036, by rfl⟩ : syracuseStep 2110715 = 3166073) B3166073
theorem B7124273 : Blo 936583 7124273 := bstep (se 2 (by rfl) ⟨2671602, by rfl⟩ : syracuseStep 7124273 = 5343205) B5343205
theorem B7615853 : Blo 936583 7615853 := bstep (se 3 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 7615853 = 2855945) B2855945
theorem B2110931 : Blo 936583 2110931 := bstep (se 1 (by rfl) ⟨1583198, by rfl⟩ : syracuseStep 2110931 = 3166397) B3166397
theorem B2111201 : Blo 936583 2111201 := bstep (se 2 (by rfl) ⟨791700, by rfl⟩ : syracuseStep 2111201 = 1583401) B1583401
theorem B1783529 : Blo 936583 1783529 := bstep (se 2 (by rfl) ⟨668823, by rfl⟩ : syracuseStep 1783529 = 1337647) B1337647
theorem B2668459 : Blo 936583 2668459 := bstep (se 1 (by rfl) ⟨2001344, by rfl⟩ : syracuseStep 2668459 = 4002689) B4002689
theorem B2668585 : Blo 936583 2668585 := bstep (se 2 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 2668585 = 2001439) B2001439
theorem B2111723 : Blo 936583 2111723 := bstep (se 1 (by rfl) ⟨1583792, by rfl⟩ : syracuseStep 2111723 = 3167585) B3167585
theorem B1784425 : Blo 936583 1784425 := bstep (se 2 (by rfl) ⟨669159, by rfl⟩ : syracuseStep 1784425 = 1338319) B1338319
theorem B9615995 : Blo 936583 9615995 := bstep (se 1 (by rfl) ⟨7211996, by rfl⟩ : syracuseStep 9615995 = 14423993) B14423993
theorem B1784585 : Blo 936583 1784585 := bstep (se 2 (by rfl) ⟨669219, by rfl⟩ : syracuseStep 1784585 = 1338439) B1338439
theorem B1424615 : Blo 936583 1424615 := bstep (se 1 (by rfl) ⟨1068461, by rfl⟩ : syracuseStep 1424615 = 2136923) B2136923
theorem B2374991 : Blo 936583 2374991 := bstep (se 1 (by rfl) ⟨1781243, by rfl⟩ : syracuseStep 2374991 = 3562487) B3562487
theorem B2113019 : Blo 936583 2113019 := bstep (se 1 (by rfl) ⟨1584764, by rfl⟩ : syracuseStep 2113019 = 3169529) B3169529
theorem B2670077 : Blo 936583 2670077 := bstep (se 3 (by rfl) ⟨500639, by rfl⟩ : syracuseStep 2670077 = 1001279) B1001279
theorem B2113199 : Blo 936583 2113199 := bstep (se 1 (by rfl) ⟨1584899, by rfl⟩ : syracuseStep 2113199 = 3169799) B3169799
theorem B2113289 : Blo 936583 2113289 := bstep (se 2 (by rfl) ⟨792483, by rfl⟩ : syracuseStep 2113289 = 1584967) B1584967
theorem B3162023 : Blo 936583 3162023 := bstep (se 1 (by rfl) ⟨2371517, by rfl⟩ : syracuseStep 3162023 = 4743035) B4743035
theorem B4014035 : Blo 936583 4014035 := bstep (se 1 (by rfl) ⟨3010526, by rfl⟩ : syracuseStep 4014035 = 6021053) B6021053
theorem B15253505 : Blo 936583 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B12861611 : Blo 936583 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B3162347 : Blo 936583 3162347 := bstep (se 1 (by rfl) ⟨2371760, by rfl⟩ : syracuseStep 3162347 = 4743521) B4743521
theorem B2113919 : Blo 936583 2113919 := bstep (se 1 (by rfl) ⟨1585439, by rfl⟩ : syracuseStep 2113919 = 3170879) B3170879
theorem B12042715 : Blo 936583 12042715 := bstep (se 1 (by rfl) ⟨9032036, by rfl⟩ : syracuseStep 12042715 = 18064073) B18064073
theorem B18072071 : Blo 936583 18072071 := bstep (se 1 (by rfl) ⟨13554053, by rfl⟩ : syracuseStep 18072071 = 27108107) B27108107
theorem B2114153 : Blo 936583 2114153 := bstep (se 2 (by rfl) ⟨792807, by rfl⟩ : syracuseStep 2114153 = 1585615) B1585615
theorem B2114783 : Blo 936583 2114783 := bstep (se 1 (by rfl) ⟨1586087, by rfl⟩ : syracuseStep 2114783 = 3172175) B3172175
theorem B2114999 : Blo 936583 2114999 := bstep (se 1 (by rfl) ⟨1586249, by rfl⟩ : syracuseStep 2114999 = 3172499) B3172499
theorem B2115179 : Blo 936583 2115179 := bstep (se 1 (by rfl) ⟨1586384, by rfl⟩ : syracuseStep 2115179 = 3172769) B3172769
theorem B3556973 : Blo 936583 3556973 := bstep (se 3 (by rfl) ⟨666932, by rfl⟩ : syracuseStep 3556973 = 1333865) B1333865
theorem B4015811 : Blo 936583 4015811 := bstep (se 1 (by rfl) ⟨3011858, by rfl⟩ : syracuseStep 4015811 = 6023717) B6023717
theorem B2115449 : Blo 936583 2115449 := bstep (se 2 (by rfl) ⟨793293, by rfl⟩ : syracuseStep 2115449 = 1586587) B1586587
theorem B1001407 : Blo 936583 1001407 := bstep (se 1 (by rfl) ⟨751055, by rfl⟩ : syracuseStep 1001407 = 1502111) B1502111
theorem B2115881 : Blo 936583 2115881 := bstep (se 2 (by rfl) ⟨793455, by rfl⟩ : syracuseStep 2115881 = 1586911) B1586911
theorem B3557915 : Blo 936583 3557915 := bstep (se 1 (by rfl) ⟨2668436, by rfl⟩ : syracuseStep 3557915 = 5336873) B5336873
theorem B34294553 : Blo 936583 34294553 := bstep (se 2 (by rfl) ⟨12860457, by rfl⟩ : syracuseStep 34294553 = 25720915) B25720915
theorem B1690409 : Blo 936583 1690409 := bstep (se 2 (by rfl) ⟨633903, by rfl⟩ : syracuseStep 1690409 = 1267807) B1267807
theorem B2673449 : Blo 936583 2673449 := bstep (se 2 (by rfl) ⟨1002543, by rfl⟩ : syracuseStep 2673449 = 2005087) B2005087
theorem B936927 : Blo 936583 936927 := bstep (se 1 (by rfl) ⟨702695, by rfl⟩ : syracuseStep 936927 = 1405391) B1405391
theorem B936955 : Blo 936583 936955 := bstep (se 1 (by rfl) ⟨702716, by rfl⟩ : syracuseStep 936955 = 1405433) B1405433
theorem B2378747 : Blo 936583 2378747 := bstep (se 1 (by rfl) ⟨1784060, by rfl⟩ : syracuseStep 2378747 = 3568121) B3568121
theorem B937023 : Blo 936583 937023 := bstep (se 1 (by rfl) ⟨702767, by rfl⟩ : syracuseStep 937023 = 1405535) B1405535
theorem B937343 : Blo 936583 937343 := bstep (se 1 (by rfl) ⟨703007, by rfl⟩ : syracuseStep 937343 = 1406015) B1406015
theorem B937371 : Blo 936583 937371 := bstep (se 1 (by rfl) ⟨703028, by rfl⟩ : syracuseStep 937371 = 1406057) B1406057
theorem B9031115 : Blo 936583 9031115 := bstep (se 1 (by rfl) ⟨6773336, by rfl⟩ : syracuseStep 9031115 = 13546673) B13546673
theorem B937439 : Blo 936583 937439 := bstep (se 1 (by rfl) ⟨703079, by rfl⟩ : syracuseStep 937439 = 1406159) B1406159
theorem B937575 : Blo 936583 937575 := bstep (se 1 (by rfl) ⟨703181, by rfl⟩ : syracuseStep 937575 = 1406363) B1406363
theorem B937723 : Blo 936583 937723 := bstep (se 1 (by rfl) ⟨703292, by rfl⟩ : syracuseStep 937723 = 1406585) B1406585
theorem B937791 : Blo 936583 937791 := bstep (se 1 (by rfl) ⟨703343, by rfl⟩ : syracuseStep 937791 = 1406687) B1406687
theorem B937855 : Blo 936583 937855 := bstep (se 1 (by rfl) ⟨703391, by rfl⟩ : syracuseStep 937855 = 1406783) B1406783
theorem B69390229 : Blo 936583 69390229 := bstep (se 6 (by rfl) ⟨1626333, by rfl⟩ : syracuseStep 69390229 = 3252667) B3252667
theorem B937967 : Blo 936583 937967 := bstep (se 1 (by rfl) ⟨703475, by rfl⟩ : syracuseStep 937967 = 1406951) B1406951
theorem B937979 : Blo 936583 937979 := bstep (se 1 (by rfl) ⟨703484, by rfl⟩ : syracuseStep 937979 = 1406969) B1406969
theorem B938047 : Blo 936583 938047 := bstep (se 1 (by rfl) ⟨703535, by rfl⟩ : syracuseStep 938047 = 1407071) B1407071
theorem B938087 : Blo 936583 938087 := bstep (se 1 (by rfl) ⟨703565, by rfl⟩ : syracuseStep 938087 = 1407131) B1407131
theorem B938111 : Blo 936583 938111 := bstep (se 1 (by rfl) ⟨703583, by rfl⟩ : syracuseStep 938111 = 1407167) B1407167
theorem B938139 : Blo 936583 938139 := bstep (se 1 (by rfl) ⟨703604, by rfl⟩ : syracuseStep 938139 = 1407209) B1407209
theorem B2674907 : Blo 936583 2674907 := bstep (se 1 (by rfl) ⟨2006180, by rfl⟩ : syracuseStep 2674907 = 4012361) B4012361
theorem B3166451 : Blo 936583 3166451 := bstep (se 1 (by rfl) ⟨2374838, by rfl⟩ : syracuseStep 3166451 = 4749677) B4749677
theorem B938343 : Blo 936583 938343 := bstep (se 1 (by rfl) ⟨703757, by rfl⟩ : syracuseStep 938343 = 1407515) B1407515
theorem B938395 : Blo 936583 938395 := bstep (se 1 (by rfl) ⟨703796, by rfl⟩ : syracuseStep 938395 = 1407593) B1407593
theorem B30396977 : Blo 936583 30396977 := bstep (se 2 (by rfl) ⟨11398866, by rfl⟩ : syracuseStep 30396977 = 22797733) B22797733
theorem B36098621 : Blo 936583 36098621 := bstep (se 3 (by rfl) ⟨6768491, by rfl⟩ : syracuseStep 36098621 = 13536983) B13536983
theorem B938747 : Blo 936583 938747 := bstep (se 1 (by rfl) ⟨704060, by rfl⟩ : syracuseStep 938747 = 1408121) B1408121
theorem B938815 : Blo 936583 938815 := bstep (se 1 (by rfl) ⟨704111, by rfl⟩ : syracuseStep 938815 = 1408223) B1408223
theorem B938843 : Blo 936583 938843 := bstep (se 1 (by rfl) ⟨704132, by rfl⟩ : syracuseStep 938843 = 1408265) B1408265
theorem B2675567 : Blo 936583 2675567 := bstep (se 1 (by rfl) ⟨2006675, by rfl⟩ : syracuseStep 2675567 = 4013351) B4013351
theorem B3003247 : Blo 936583 3003247 := bstep (se 1 (by rfl) ⟨2252435, by rfl⟩ : syracuseStep 3003247 = 4504871) B4504871
theorem B938911 : Blo 936583 938911 := bstep (se 1 (by rfl) ⟨704183, by rfl⟩ : syracuseStep 938911 = 1408367) B1408367
theorem B938991 : Blo 936583 938991 := bstep (se 1 (by rfl) ⟨704243, by rfl⟩ : syracuseStep 938991 = 1408487) B1408487
theorem B6018077 : Blo 936583 6018077 := bstep (se 3 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 6018077 = 2256779) B2256779
theorem B939079 : Blo 936583 939079 := bstep (se 1 (by rfl) ⟨704309, by rfl⟩ : syracuseStep 939079 = 1408619) B1408619
theorem B3560543 : Blo 936583 3560543 := bstep (se 1 (by rfl) ⟨2670407, by rfl⟩ : syracuseStep 3560543 = 5340815) B5340815
theorem B939163 : Blo 936583 939163 := bstep (se 1 (by rfl) ⟨704372, by rfl⟩ : syracuseStep 939163 = 1408745) B1408745
theorem B939259 : Blo 936583 939259 := bstep (se 1 (by rfl) ⟨704444, by rfl⟩ : syracuseStep 939259 = 1408889) B1408889
theorem B939327 : Blo 936583 939327 := bstep (se 1 (by rfl) ⟨704495, by rfl⟩ : syracuseStep 939327 = 1408991) B1408991
theorem B939495 : Blo 936583 939495 := bstep (se 1 (by rfl) ⟨704621, by rfl⟩ : syracuseStep 939495 = 1409243) B1409243
theorem B939503 : Blo 936583 939503 := bstep (se 1 (by rfl) ⟨704627, by rfl⟩ : syracuseStep 939503 = 1409255) B1409255
theorem B939611 : Blo 936583 939611 := bstep (se 1 (by rfl) ⟨704708, by rfl⟩ : syracuseStep 939611 = 1409417) B1409417
theorem B939675 : Blo 936583 939675 := bstep (se 1 (by rfl) ⟨704756, by rfl⟩ : syracuseStep 939675 = 1409513) B1409513
theorem B939759 : Blo 936583 939759 := bstep (se 1 (by rfl) ⟨704819, by rfl⟩ : syracuseStep 939759 = 1409639) B1409639
theorem B3168071 : Blo 936583 3168071 := bstep (se 1 (by rfl) ⟨2376053, by rfl⟩ : syracuseStep 3168071 = 4752107) B4752107
theorem B939847 : Blo 936583 939847 := bstep (se 1 (by rfl) ⟨704885, by rfl⟩ : syracuseStep 939847 = 1409771) B1409771
theorem B939867 : Blo 936583 939867 := bstep (se 1 (by rfl) ⟨704900, by rfl⟩ : syracuseStep 939867 = 1409801) B1409801
theorem B1267579 : Blo 936583 1267579 := bstep (se 1 (by rfl) ⟨950684, by rfl⟩ : syracuseStep 1267579 = 1901369) B1901369
theorem B16013213 : Blo 936583 16013213 := bstep (se 3 (by rfl) ⟨3002477, by rfl⟩ : syracuseStep 16013213 = 6004955) B6004955
theorem B939935 : Blo 936583 939935 := bstep (se 1 (by rfl) ⟨704951, by rfl⟩ : syracuseStep 939935 = 1409903) B1409903
theorem B4511713 : Blo 936583 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B940103 : Blo 936583 940103 := bstep (se 1 (by rfl) ⟨705077, by rfl⟩ : syracuseStep 940103 = 1410155) B1410155
theorem B940263 : Blo 936583 940263 := bstep (se 1 (by rfl) ⟨705197, by rfl⟩ : syracuseStep 940263 = 1410395) B1410395
theorem B2677151 : Blo 936583 2677151 := bstep (se 1 (by rfl) ⟨2007863, by rfl⟩ : syracuseStep 2677151 = 4015727) B4015727
theorem B940447 : Blo 936583 940447 := bstep (se 1 (by rfl) ⟨705335, by rfl⟩ : syracuseStep 940447 = 1410671) B1410671
theorem B940495 : Blo 936583 940495 := bstep (se 1 (by rfl) ⟨705371, by rfl⟩ : syracuseStep 940495 = 1410743) B1410743
theorem B940519 : Blo 936583 940519 := bstep (se 1 (by rfl) ⟨705389, by rfl⟩ : syracuseStep 940519 = 1410779) B1410779
theorem B3430889 : Blo 936583 3430889 := bstep (se 2 (by rfl) ⟨1286583, by rfl⟩ : syracuseStep 3430889 = 2573167) B2573167
theorem B266951189 : Blo 936583 266951189 := bstep (se 6 (by rfl) ⟨6256668, by rfl⟩ : syracuseStep 266951189 = 12513337) B12513337
theorem B3562319 : Blo 936583 3562319 := bstep (se 1 (by rfl) ⟨2671739, by rfl⟩ : syracuseStep 3562319 = 5343479) B5343479
theorem B3169259 : Blo 936583 3169259 := bstep (se 1 (by rfl) ⟨2376944, by rfl⟩ : syracuseStep 3169259 = 4753889) B4753889
theorem B18078835 : Blo 936583 18078835 := bstep (se 1 (by rfl) ⟨13559126, by rfl⟩ : syracuseStep 18078835 = 27118253) B27118253
theorem B14442461 : Blo 936583 14442461 := bstep (se 3 (by rfl) ⟨2707961, by rfl⟩ : syracuseStep 14442461 = 5415923) B5415923
theorem B15196355 : Blo 936583 15196355 := bstep (se 1 (by rfl) ⟨11397266, by rfl⟩ : syracuseStep 15196355 = 22794533) B22794533
theorem B3170771 : Blo 936583 3170771 := bstep (se 1 (by rfl) ⟨2378078, by rfl⟩ : syracuseStep 3170771 = 4756157) B4756157
theorem B5497307 : Blo 936583 5497307 := bstep (se 1 (by rfl) ⟨4122980, by rfl⟩ : syracuseStep 5497307 = 8245961) B8245961
theorem B7725617 : Blo 936583 7725617 := bstep (se 2 (by rfl) ⟨2897106, by rfl⟩ : syracuseStep 7725617 = 5794213) B5794213
theorem B3564431 : Blo 936583 3564431 := bstep (se 1 (by rfl) ⟨2673323, by rfl⟩ : syracuseStep 3564431 = 5346647) B5346647
theorem B3564445 : Blo 936583 3564445 := bstep (se 3 (by rfl) ⟨668333, by rfl⟩ : syracuseStep 3564445 = 1336667) B1336667
theorem B14443883 : Blo 936583 14443883 := bstep (se 1 (by rfl) ⟨10832912, by rfl⟩ : syracuseStep 14443883 = 21665825) B21665825
theorem B52159949 : Blo 936583 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B5334731 : Blo 936583 5334731 := bstep (se 1 (by rfl) ⟨4001048, by rfl⟩ : syracuseStep 5334731 = 8002097) B8002097
theorem B15197969 : Blo 936583 15197969 := bstep (se 2 (by rfl) ⟨5699238, by rfl⟩ : syracuseStep 15197969 = 11398477) B11398477
theorem B4744979 : Blo 936583 4744979 := bstep (se 1 (by rfl) ⟨3558734, by rfl⟩ : syracuseStep 4744979 = 7117469) B7117469
theorem B5334983 : Blo 936583 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B1501163 : Blo 936583 1501163 := bstep (se 1 (by rfl) ⟨1125872, by rfl⟩ : syracuseStep 1501163 = 2251745) B2251745
theorem B3565691 : Blo 936583 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B2255339 : Blo 936583 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B6025103 : Blo 936583 6025103 := bstep (se 1 (by rfl) ⟨4518827, by rfl⟩ : syracuseStep 6025103 = 9037655) B9037655
theorem B158232527 : Blo 936583 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B1405055 : Blo 936583 1405055 := bstep (se 1 (by rfl) ⟨1053791, by rfl⟩ : syracuseStep 1405055 = 2107583) B2107583
theorem B8024345 : Blo 936583 8024345 := bstep (se 2 (by rfl) ⟨3009129, by rfl⟩ : syracuseStep 8024345 = 6018259) B6018259
theorem B4518479 : Blo 936583 4518479 := bstep (se 1 (by rfl) ⟨3388859, by rfl⟩ : syracuseStep 4518479 = 6777719) B6777719
theorem B1405691 : Blo 936583 1405691 := bstep (se 1 (by rfl) ⟨1054268, by rfl⟩ : syracuseStep 1405691 = 2108537) B2108537
theorem B6026177 : Blo 936583 6026177 := bstep (se 2 (by rfl) ⟨2259816, by rfl⟩ : syracuseStep 6026177 = 4519633) B4519633
theorem B1406135 : Blo 936583 1406135 := bstep (se 1 (by rfl) ⟨1054601, by rfl⟩ : syracuseStep 1406135 = 2109203) B2109203
theorem B34207109 : Blo 936583 34207109 := bstep (se 4 (by rfl) ⟨3206916, by rfl⟩ : syracuseStep 34207109 = 6413833) B6413833
theorem B1406375 : Blo 936583 1406375 := bstep (se 1 (by rfl) ⟨1054781, by rfl⟩ : syracuseStep 1406375 = 2109563) B2109563
theorem B1406555 : Blo 936583 1406555 := bstep (se 1 (by rfl) ⟨1054916, by rfl⟩ : syracuseStep 1406555 = 2109833) B2109833
theorem B3569305 : Blo 936583 3569305 := bstep (se 2 (by rfl) ⟨1338489, by rfl⟩ : syracuseStep 3569305 = 2676979) B2676979
theorem B22837049 : Blo 936583 22837049 := bstep (se 2 (by rfl) ⟨8563893, by rfl⟩ : syracuseStep 22837049 = 17127787) B17127787
theorem B1407017 : Blo 936583 1407017 := bstep (se 2 (by rfl) ⟨527631, by rfl⟩ : syracuseStep 1407017 = 1055263) B1055263
theorem B1407047 : Blo 936583 1407047 := bstep (se 1 (by rfl) ⟨1055285, by rfl⟩ : syracuseStep 1407047 = 2110571) B2110571
theorem B5142737 : Blo 936583 5142737 := bstep (se 2 (by rfl) ⟨1928526, by rfl⟩ : syracuseStep 5142737 = 3857053) B3857053
theorem B3570095 : Blo 936583 3570095 := bstep (se 1 (by rfl) ⟨2677571, by rfl⟩ : syracuseStep 3570095 = 5355143) B5355143
theorem B1407431 : Blo 936583 1407431 := bstep (se 1 (by rfl) ⟨1055573, by rfl⟩ : syracuseStep 1407431 = 2111147) B2111147
theorem B1407647 : Blo 936583 1407647 := bstep (se 1 (by rfl) ⟨1055735, by rfl⟩ : syracuseStep 1407647 = 2111471) B2111471
theorem B1407791 : Blo 936583 1407791 := bstep (se 1 (by rfl) ⟨1055843, by rfl⟩ : syracuseStep 1407791 = 2111687) B2111687
theorem B4750163 : Blo 936583 4750163 := bstep (se 1 (by rfl) ⟨3562622, by rfl⟩ : syracuseStep 4750163 = 7125245) B7125245
theorem B1407911 : Blo 936583 1407911 := bstep (se 1 (by rfl) ⟨1055933, by rfl⟩ : syracuseStep 1407911 = 2111867) B2111867
theorem B1408091 : Blo 936583 1408091 := bstep (se 1 (by rfl) ⟨1056068, by rfl⟩ : syracuseStep 1408091 = 2112137) B2112137
theorem B1408463 : Blo 936583 1408463 := bstep (se 1 (by rfl) ⟨1056347, by rfl⟩ : syracuseStep 1408463 = 2112695) B2112695
theorem B17137127 : Blo 936583 17137127 := bstep (se 1 (by rfl) ⟨12852845, by rfl⟩ : syracuseStep 17137127 = 25705691) B25705691
theorem B1408847 : Blo 936583 1408847 := bstep (se 1 (by rfl) ⟨1056635, by rfl⟩ : syracuseStep 1408847 = 2113271) B2113271
theorem B1408967 : Blo 936583 1408967 := bstep (se 1 (by rfl) ⟨1056725, by rfl⟩ : syracuseStep 1408967 = 2113451) B2113451
theorem B92504213 : Blo 936583 92504213 := bstep (se 6 (by rfl) ⟨2168067, by rfl⟩ : syracuseStep 92504213 = 4336135) B4336135
theorem B5079293 : Blo 936583 5079293 := bstep (se 3 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 5079293 = 1904735) B1904735
theorem B1409279 : Blo 936583 1409279 := bstep (se 1 (by rfl) ⟨1056959, by rfl⟩ : syracuseStep 1409279 = 2113919) B2113919
theorem B1409435 : Blo 936583 1409435 := bstep (se 1 (by rfl) ⟨1057076, by rfl⟩ : syracuseStep 1409435 = 2114153) B2114153
theorem B16056953 : Blo 936583 16056953 := bstep (se 2 (by rfl) ⟨6021357, by rfl⟩ : syracuseStep 16056953 = 12042715) B12042715
theorem B1409855 : Blo 936583 1409855 := bstep (se 1 (by rfl) ⟨1057391, by rfl⟩ : syracuseStep 1409855 = 2114783) B2114783
theorem B1409999 : Blo 936583 1409999 := bstep (se 1 (by rfl) ⟨1057499, by rfl⟩ : syracuseStep 1409999 = 2114999) B2114999
theorem B1410089 : Blo 936583 1410089 := bstep (se 2 (by rfl) ⟨528783, by rfl⟩ : syracuseStep 1410089 = 1057567) B1057567
theorem B1410119 : Blo 936583 1410119 := bstep (se 1 (by rfl) ⟨1057589, by rfl⟩ : syracuseStep 1410119 = 2115179) B2115179
theorem B4752593 : Blo 936583 4752593 := bstep (se 2 (by rfl) ⟨1782222, by rfl⟩ : syracuseStep 4752593 = 3564445) B3564445
theorem B1410299 : Blo 936583 1410299 := bstep (se 1 (by rfl) ⟨1057724, by rfl⟩ : syracuseStep 1410299 = 2115449) B2115449
theorem B19269089 : Blo 936583 19269089 := bstep (se 2 (by rfl) ⟨7225908, by rfl⟩ : syracuseStep 19269089 = 14451817) B14451817
theorem B1410587 : Blo 936583 1410587 := bstep (se 1 (by rfl) ⟨1057940, by rfl⟩ : syracuseStep 1410587 = 2115881) B2115881
theorem B12027953 : Blo 936583 12027953 := bstep (se 2 (by rfl) ⟨4510482, by rfl⟩ : syracuseStep 12027953 = 9020965) B9020965
theorem B18024707 : Blo 936583 18024707 := bstep (se 1 (by rfl) ⟨13518530, by rfl⟩ : syracuseStep 18024707 = 27037061) B27037061
theorem B22874723 : Blo 936583 22874723 := bstep (se 1 (by rfl) ⟨17156042, by rfl⟩ : syracuseStep 22874723 = 34312085) B34312085
theorem B177967459 : Blo 936583 177967459 := bstep (se 1 (by rfl) ⟨133475594, by rfl⟩ : syracuseStep 177967459 = 266951189) B266951189
theorem B5706247 : Blo 936583 5706247 := bstep (se 1 (by rfl) ⟨4279685, by rfl⟩ : syracuseStep 5706247 = 8559371) B8559371
theorem B16061327 : Blo 936583 16061327 := bstep (se 1 (by rfl) ⟨12045995, by rfl⟩ : syracuseStep 16061327 = 24091991) B24091991
theorem B10130903 : Blo 936583 10130903 := bstep (se 1 (by rfl) ⟨7598177, by rfl⟩ : syracuseStep 10130903 = 15196355) B15196355
theorem B5150411 : Blo 936583 5150411 := bstep (se 1 (by rfl) ⟨3862808, by rfl⟩ : syracuseStep 5150411 = 7725617) B7725617
theorem B1054831 : Blo 936583 1054831 := bstep (se 1 (by rfl) ⟨791123, by rfl⟩ : syracuseStep 1054831 = 1582247) B1582247
theorem B4003987 : Blo 936583 4003987 := bstep (se 1 (by rfl) ⟨3002990, by rfl⟩ : syracuseStep 4003987 = 6005981) B6005981
theorem B34773299 : Blo 936583 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B1186255 : Blo 936583 1186255 := bstep (se 1 (by rfl) ⟨889691, by rfl⟩ : syracuseStep 1186255 = 1779383) B1779383
theorem B4004329 : Blo 936583 4004329 := bstep (se 2 (by rfl) ⟨1501623, by rfl⟩ : syracuseStep 4004329 = 3003247) B3003247
theorem B10131979 : Blo 936583 10131979 := bstep (se 1 (by rfl) ⟨7598984, by rfl⟩ : syracuseStep 10131979 = 15197969) B15197969
theorem B1055335 : Blo 936583 1055335 := bstep (se 1 (by rfl) ⟨791501, by rfl⟩ : syracuseStep 1055335 = 1583003) B1583003
theorem B4004603 : Blo 936583 4004603 := bstep (se 1 (by rfl) ⟨3003452, by rfl⟩ : syracuseStep 4004603 = 6006905) B6006905
theorem B5348105 : Blo 936583 5348105 := bstep (se 2 (by rfl) ⟨2005539, by rfl⟩ : syracuseStep 5348105 = 4011079) B4011079
theorem B4005287 : Blo 936583 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B10690055 : Blo 936583 10690055 := bstep (se 1 (by rfl) ⟨8017541, by rfl⟩ : syracuseStep 10690055 = 16035083) B16035083
theorem B4759073 : Blo 936583 4759073 := bstep (se 2 (by rfl) ⟨1784652, by rfl⟩ : syracuseStep 4759073 = 3569305) B3569305
theorem B1580647 : Blo 936583 1580647 := bstep (se 1 (by rfl) ⟨1185485, by rfl⟩ : syracuseStep 1580647 = 2370971) B2370971
theorem B1580809 : Blo 936583 1580809 := bstep (se 2 (by rfl) ⟨592803, by rfl⟩ : syracuseStep 1580809 = 1185607) B1185607
theorem B105488351 : Blo 936583 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B5349563 : Blo 936583 5349563 := bstep (se 1 (by rfl) ⟨4012172, by rfl⟩ : syracuseStep 5349563 = 8024345) B8024345
theorem B1581599 : Blo 936583 1581599 := bstep (se 1 (by rfl) ⟨1186199, by rfl⟩ : syracuseStep 1581599 = 2372399) B2372399
theorem B1778267 : Blo 936583 1778267 := bstep (se 1 (by rfl) ⟨1333700, by rfl⟩ : syracuseStep 1778267 = 2667401) B2667401
theorem B1189019 : Blo 936583 1189019 := bstep (se 1 (by rfl) ⟨891764, by rfl⟩ : syracuseStep 1189019 = 1783529) B1783529
theorem B1189723 : Blo 936583 1189723 := bstep (se 1 (by rfl) ⟨892292, by rfl⟩ : syracuseStep 1189723 = 1784585) B1784585
theorem B6760421 : Blo 936583 6760421 := bstep (se 4 (by rfl) ⟨633789, by rfl⟩ : syracuseStep 6760421 = 1267579) B1267579
theorem B1583327 : Blo 936583 1583327 := bstep (se 1 (by rfl) ⟨1187495, by rfl⟩ : syracuseStep 1583327 = 2374991) B2374991
theorem B13510921 : Blo 936583 13510921 := bstep (se 2 (by rfl) ⟨5066595, by rfl⟩ : syracuseStep 13510921 = 10133191) B10133191
theorem B1780051 : Blo 936583 1780051 := bstep (se 1 (by rfl) ⟨1335038, by rfl⟩ : syracuseStep 1780051 = 2670077) B2670077
theorem B2108015 : Blo 936583 2108015 := bstep (se 1 (by rfl) ⟨1581011, by rfl⟩ : syracuseStep 2108015 = 3162023) B3162023
theorem B10169003 : Blo 936583 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B2108231 : Blo 936583 2108231 := bstep (se 1 (by rfl) ⟨1581173, by rfl⟩ : syracuseStep 2108231 = 3162347) B3162347
theorem B12004685 : Blo 936583 12004685 := bstep (se 3 (by rfl) ⟨2250878, by rfl⟩ : syracuseStep 12004685 = 4501757) B4501757
theorem B2371315 : Blo 936583 2371315 := bstep (se 1 (by rfl) ⟨1778486, by rfl⟩ : syracuseStep 2371315 = 3556973) B3556973
theorem B8007497 : Blo 936583 8007497 := bstep (se 2 (by rfl) ⟨3002811, by rfl⟩ : syracuseStep 8007497 = 6005623) B6005623
theorem B2371943 : Blo 936583 2371943 := bstep (se 1 (by rfl) ⟨1778957, by rfl⟩ : syracuseStep 2371943 = 3557915) B3557915
theorem B12038615 : Blo 936583 12038615 := bstep (se 1 (by rfl) ⟨9028961, by rfl⟩ : syracuseStep 12038615 = 18057923) B18057923
theorem B1782299 : Blo 936583 1782299 := bstep (se 1 (by rfl) ⟨1336724, by rfl⟩ : syracuseStep 1782299 = 2673449) B2673449
theorem B1585831 : Blo 936583 1585831 := bstep (se 1 (by rfl) ⟨1189373, by rfl⟩ : syracuseStep 1585831 = 2378747) B2378747
theorem B2110841 : Blo 936583 2110841 := bstep (se 2 (by rfl) ⟨791565, by rfl⟩ : syracuseStep 2110841 = 1583131) B1583131
theorem B2536879 : Blo 936583 2536879 := bstep (se 1 (by rfl) ⟨1902659, by rfl⟩ : syracuseStep 2536879 = 3805319) B3805319
theorem B1783271 : Blo 936583 1783271 := bstep (se 1 (by rfl) ⟨1337453, by rfl⟩ : syracuseStep 1783271 = 2674907) B2674907
theorem B2110967 : Blo 936583 2110967 := bstep (se 1 (by rfl) ⟨1583225, by rfl⟩ : syracuseStep 2110967 = 3166451) B3166451
theorem B20264651 : Blo 936583 20264651 := bstep (se 1 (by rfl) ⟨15198488, by rfl⟩ : syracuseStep 20264651 = 30396977) B30396977
theorem B24065747 : Blo 936583 24065747 := bstep (se 1 (by rfl) ⟨18049310, by rfl⟩ : syracuseStep 24065747 = 36098621) B36098621
theorem B1783711 : Blo 936583 1783711 := bstep (se 1 (by rfl) ⟨1337783, by rfl⟩ : syracuseStep 1783711 = 2675567) B2675567
theorem B2373695 : Blo 936583 2373695 := bstep (se 1 (by rfl) ⟨1780271, by rfl⟩ : syracuseStep 2373695 = 3560543) B3560543
theorem B2112047 : Blo 936583 2112047 := bstep (se 1 (by rfl) ⟨1584035, by rfl⟩ : syracuseStep 2112047 = 3168071) B3168071
theorem B1784767 : Blo 936583 1784767 := bstep (se 1 (by rfl) ⟨1338575, by rfl⟩ : syracuseStep 1784767 = 2677151) B2677151
theorem B2669689 : Blo 936583 2669689 := bstep (se 2 (by rfl) ⟨1001133, by rfl⟩ : syracuseStep 2669689 = 2002267) B2002267
theorem B2374879 : Blo 936583 2374879 := bstep (se 1 (by rfl) ⟨1781159, by rfl⟩ : syracuseStep 2374879 = 3562319) B3562319
theorem B2112839 : Blo 936583 2112839 := bstep (se 1 (by rfl) ⟨1584629, by rfl⟩ : syracuseStep 2112839 = 3169259) B3169259
theorem B92520305 : Blo 936583 92520305 := bstep (se 2 (by rfl) ⟨34695114, by rfl⟩ : syracuseStep 92520305 = 69390229) B69390229
theorem B2113847 : Blo 936583 2113847 := bstep (se 1 (by rfl) ⟨1585385, by rfl⟩ : syracuseStep 2113847 = 3170771) B3170771
theorem B2376287 : Blo 936583 2376287 := bstep (se 1 (by rfl) ⟨1782215, by rfl⟩ : syracuseStep 2376287 = 3564431) B3564431
theorem B3556487 : Blo 936583 3556487 := bstep (se 1 (by rfl) ⟨2667365, by rfl⟩ : syracuseStep 3556487 = 5334731) B5334731
theorem B3163319 : Blo 936583 3163319 := bstep (se 1 (by rfl) ⟨2372489, by rfl⟩ : syracuseStep 3163319 = 4744979) B4744979
theorem B6014159 : Blo 936583 6014159 := bstep (se 1 (by rfl) ⟨4510619, by rfl⟩ : syracuseStep 6014159 = 9021239) B9021239
theorem B2376985 : Blo 936583 2376985 := bstep (se 2 (by rfl) ⟨891369, by rfl⟩ : syracuseStep 2376985 = 1782739) B1782739
theorem B3556655 : Blo 936583 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B1000775 : Blo 936583 1000775 := bstep (se 1 (by rfl) ⟨750581, by rfl⟩ : syracuseStep 1000775 = 1501163) B1501163
theorem B2377127 : Blo 936583 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B2377289 : Blo 936583 2377289 := bstep (se 2 (by rfl) ⟨891483, by rfl⟩ : syracuseStep 2377289 = 1782967) B1782967
theorem B2672423 : Blo 936583 2672423 := bstep (se 1 (by rfl) ⟨2004317, by rfl⟩ : syracuseStep 2672423 = 4008635) B4008635
theorem B2410279 : Blo 936583 2410279 := bstep (se 1 (by rfl) ⟨1807709, by rfl⟩ : syracuseStep 2410279 = 3615419) B3615419
theorem B4507757 : Blo 936583 4507757 := bstep (se 3 (by rfl) ⟨845204, by rfl⟩ : syracuseStep 4507757 = 1690409) B1690409
theorem B3918007 : Blo 936583 3918007 := bstep (se 1 (by rfl) ⟨2938505, by rfl⟩ : syracuseStep 3918007 = 5877011) B5877011
theorem B3557945 : Blo 936583 3557945 := bstep (se 2 (by rfl) ⟨1334229, by rfl⟩ : syracuseStep 3557945 = 2668459) B2668459
theorem B4016735 : Blo 936583 4016735 := bstep (se 1 (by rfl) ⟨3012551, by rfl⟩ : syracuseStep 4016735 = 6025103) B6025103
theorem B6015617 : Blo 936583 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B3558113 : Blo 936583 3558113 := bstep (se 2 (by rfl) ⟨1334292, by rfl⟩ : syracuseStep 3558113 = 2668585) B2668585
theorem B936703 : Blo 936583 936703 := bstep (se 1 (by rfl) ⟨702527, by rfl⟩ : syracuseStep 936703 = 1405055) B1405055
theorem B937127 : Blo 936583 937127 := bstep (se 1 (by rfl) ⟨702845, by rfl⟩ : syracuseStep 937127 = 1405691) B1405691
theorem B4017451 : Blo 936583 4017451 := bstep (se 1 (by rfl) ⟨3013088, by rfl⟩ : syracuseStep 4017451 = 6026177) B6026177
theorem B937423 : Blo 936583 937423 := bstep (se 1 (by rfl) ⟨703067, by rfl⟩ : syracuseStep 937423 = 1406135) B1406135
theorem B2379233 : Blo 936583 2379233 := bstep (se 2 (by rfl) ⟨892212, by rfl⟩ : syracuseStep 2379233 = 1784425) B1784425
theorem B937583 : Blo 936583 937583 := bstep (se 1 (by rfl) ⟨703187, by rfl⟩ : syracuseStep 937583 = 1406375) B1406375
theorem B937703 : Blo 936583 937703 := bstep (se 1 (by rfl) ⟨703277, by rfl⟩ : syracuseStep 937703 = 1406555) B1406555
theorem B15224699 : Blo 936583 15224699 := bstep (se 1 (by rfl) ⟨11418524, by rfl⟩ : syracuseStep 15224699 = 22837049) B22837049
theorem B45699005 : Blo 936583 45699005 := bstep (se 3 (by rfl) ⟨8568563, by rfl⟩ : syracuseStep 45699005 = 17137127) B17137127
theorem B938011 : Blo 936583 938011 := bstep (se 1 (by rfl) ⟨703508, by rfl⟩ : syracuseStep 938011 = 1407017) B1407017
theorem B938031 : Blo 936583 938031 := bstep (se 1 (by rfl) ⟨703523, by rfl⟩ : syracuseStep 938031 = 1407047) B1407047
theorem B3428491 : Blo 936583 3428491 := bstep (se 1 (by rfl) ⟨2571368, by rfl⟩ : syracuseStep 3428491 = 5142737) B5142737
theorem B24105113 : Blo 936583 24105113 := bstep (se 2 (by rfl) ⟨9039417, by rfl⟩ : syracuseStep 24105113 = 18078835) B18078835
theorem B2380063 : Blo 936583 2380063 := bstep (se 1 (by rfl) ⟨1785047, by rfl⟩ : syracuseStep 2380063 = 3570095) B3570095
theorem B938287 : Blo 936583 938287 := bstep (se 1 (by rfl) ⟨703715, by rfl⟩ : syracuseStep 938287 = 1407431) B1407431
theorem B6410663 : Blo 936583 6410663 := bstep (se 1 (by rfl) ⟨4807997, by rfl⟩ : syracuseStep 6410663 = 9615995) B9615995
theorem B938431 : Blo 936583 938431 := bstep (se 1 (by rfl) ⟨703823, by rfl⟩ : syracuseStep 938431 = 1407647) B1407647
theorem B938527 : Blo 936583 938527 := bstep (se 1 (by rfl) ⟨703895, by rfl⟩ : syracuseStep 938527 = 1407791) B1407791
theorem B3166775 : Blo 936583 3166775 := bstep (se 1 (by rfl) ⟨2375081, by rfl⟩ : syracuseStep 3166775 = 4750163) B4750163
theorem B938607 : Blo 936583 938607 := bstep (se 1 (by rfl) ⟨703955, by rfl⟩ : syracuseStep 938607 = 1407911) B1407911
theorem B938727 : Blo 936583 938727 := bstep (se 1 (by rfl) ⟨704045, by rfl⟩ : syracuseStep 938727 = 1408091) B1408091
theorem B938975 : Blo 936583 938975 := bstep (se 1 (by rfl) ⟨704231, by rfl⟩ : syracuseStep 938975 = 1408463) B1408463
theorem B3003389 : Blo 936583 3003389 := bstep (se 3 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 3003389 = 1126271) B1126271
theorem B939231 : Blo 936583 939231 := bstep (se 1 (by rfl) ⟨704423, by rfl⟩ : syracuseStep 939231 = 1408847) B1408847
theorem B939311 : Blo 936583 939311 := bstep (se 1 (by rfl) ⟨704483, by rfl⟩ : syracuseStep 939311 = 1408967) B1408967
theorem B2676023 : Blo 936583 2676023 := bstep (se 1 (by rfl) ⟨2007017, by rfl⟩ : syracuseStep 2676023 = 4014035) B4014035
theorem B8574407 : Blo 936583 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B939551 : Blo 936583 939551 := bstep (se 1 (by rfl) ⟨704663, by rfl⟩ : syracuseStep 939551 = 1409327) B1409327
theorem B12048047 : Blo 936583 12048047 := bstep (se 1 (by rfl) ⟨9036035, by rfl⟩ : syracuseStep 12048047 = 18072071) B18072071
theorem B1201855 : Blo 936583 1201855 := bstep (se 1 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 1201855 = 1802783) B1802783
theorem B939711 : Blo 936583 939711 := bstep (se 1 (by rfl) ⟨704783, by rfl⟩ : syracuseStep 939711 = 1409567) B1409567
theorem B22828877 : Blo 936583 22828877 := bstep (se 3 (by rfl) ⟨4280414, by rfl⟩ : syracuseStep 22828877 = 8560829) B8560829
theorem B3168125 : Blo 936583 3168125 := bstep (se 3 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 3168125 = 1188047) B1188047
theorem B940159 : Blo 936583 940159 := bstep (se 1 (by rfl) ⟨705119, by rfl⟩ : syracuseStep 940159 = 1410239) B1410239
theorem B940255 : Blo 936583 940255 := bstep (se 1 (by rfl) ⟨705191, by rfl⟩ : syracuseStep 940255 = 1410383) B1410383
theorem B940315 : Blo 936583 940315 := bstep (se 1 (by rfl) ⟨705236, by rfl⟩ : syracuseStep 940315 = 1410473) B1410473
theorem B940415 : Blo 936583 940415 := bstep (se 1 (by rfl) ⟨705311, by rfl⟩ : syracuseStep 940415 = 1410623) B1410623
theorem B940443 : Blo 936583 940443 := bstep (se 1 (by rfl) ⟨705332, by rfl⟩ : syracuseStep 940443 = 1410665) B1410665
theorem B2677207 : Blo 936583 2677207 := bstep (se 1 (by rfl) ⟨2007905, by rfl⟩ : syracuseStep 2677207 = 4015811) B4015811
theorem B2677481 : Blo 936583 2677481 := bstep (se 2 (by rfl) ⟨1004055, by rfl⟩ : syracuseStep 2677481 = 2008111) B2008111
theorem B1268617 : Blo 936583 1268617 := bstep (se 2 (by rfl) ⟨475731, by rfl⟩ : syracuseStep 1268617 = 951463) B951463
theorem B22863035 : Blo 936583 22863035 := bstep (se 1 (by rfl) ⟨17147276, by rfl⟩ : syracuseStep 22863035 = 34294553) B34294553
theorem B1334503 : Blo 936583 1334503 := bstep (se 1 (by rfl) ⟨1000877, by rfl⟩ : syracuseStep 1334503 = 2001755) B2001755
theorem B4742387 : Blo 936583 4742387 := bstep (se 1 (by rfl) ⟨3556790, by rfl⟩ : syracuseStep 4742387 = 7113581) B7113581
theorem B6020743 : Blo 936583 6020743 := bstep (se 1 (by rfl) ⟨4515557, by rfl⟩ : syracuseStep 6020743 = 9031115) B9031115
theorem B1335209 : Blo 936583 1335209 := bstep (se 2 (by rfl) ⟨500703, by rfl⟩ : syracuseStep 1335209 = 1001407) B1001407
theorem B16048205 : Blo 936583 16048205 := bstep (se 3 (by rfl) ⟨3009038, by rfl⟩ : syracuseStep 16048205 = 6018077) B6018077
theorem B1335403 : Blo 936583 1335403 := bstep (se 1 (by rfl) ⟨1001552, by rfl⟩ : syracuseStep 1335403 = 2003105) B2003105
theorem B1336223 : Blo 936583 1336223 := bstep (se 1 (by rfl) ⟨1002167, by rfl⟩ : syracuseStep 1336223 = 2004335) B2004335
theorem B3171311 : Blo 936583 3171311 := bstep (se 1 (by rfl) ⟨2378483, by rfl⟩ : syracuseStep 3171311 = 4756967) B4756967
theorem B4744331 : Blo 936583 4744331 := bstep (se 1 (by rfl) ⟨3558248, by rfl⟩ : syracuseStep 4744331 = 7116497) B7116497
theorem B3564719 : Blo 936583 3564719 := bstep (se 1 (by rfl) ⟨2673539, by rfl⟩ : syracuseStep 3564719 = 5347079) B5347079
theorem B5334275 : Blo 936583 5334275 := bstep (se 1 (by rfl) ⟨4000706, by rfl⟩ : syracuseStep 5334275 = 8001413) B8001413
theorem B10675475 : Blo 936583 10675475 := bstep (se 1 (by rfl) ⟨8006606, by rfl⟩ : syracuseStep 10675475 = 16013213) B16013213
theorem B48784855 : Blo 936583 48784855 := bstep (se 1 (by rfl) ⟨36588641, by rfl⟩ : syracuseStep 48784855 = 73177283) B73177283
theorem B2287259 : Blo 936583 2287259 := bstep (se 1 (by rfl) ⟨1715444, by rfl⟩ : syracuseStep 2287259 = 3430889) B3430889
theorem B9136415 : Blo 936583 9136415 := bstep (se 1 (by rfl) ⟨6852311, by rfl⟩ : syracuseStep 9136415 = 13704623) B13704623
theorem B7137881 : Blo 936583 7137881 := bstep (se 2 (by rfl) ⟨2676705, by rfl⟩ : syracuseStep 7137881 = 5353411) B5353411
theorem B9628307 : Blo 936583 9628307 := bstep (se 1 (by rfl) ⟨7221230, by rfl⟩ : syracuseStep 9628307 = 14442461) B14442461
theorem B4745951 : Blo 936583 4745951 := bstep (se 1 (by rfl) ⟨3559463, by rfl⟩ : syracuseStep 4745951 = 7118927) B7118927
theorem B3664871 : Blo 936583 3664871 := bstep (se 1 (by rfl) ⟨2748653, by rfl⟩ : syracuseStep 3664871 = 5497307) B5497307
theorem B3566663 : Blo 936583 3566663 := bstep (se 1 (by rfl) ⟨2674997, by rfl⟩ : syracuseStep 3566663 = 5349995) B5349995
theorem B3173687 : Blo 936583 3173687 := bstep (se 1 (by rfl) ⟨2380265, by rfl⟩ : syracuseStep 3173687 = 4760531) B4760531
theorem B9629255 : Blo 936583 9629255 := bstep (se 1 (by rfl) ⟨7221941, by rfl⟩ : syracuseStep 9629255 = 14443883) B14443883
theorem B4746923 : Blo 936583 4746923 := bstep (se 1 (by rfl) ⟨3560192, by rfl⟩ : syracuseStep 4746923 = 7120385) B7120385
theorem B8679383 : Blo 936583 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B1404905 : Blo 936583 1404905 := bstep (se 2 (by rfl) ⟨526839, by rfl⟩ : syracuseStep 1404905 = 1053679) B1053679
theorem B1404923 : Blo 936583 1404923 := bstep (se 1 (by rfl) ⟨1053692, by rfl⟩ : syracuseStep 1404923 = 2107385) B2107385
theorem B1404959 : Blo 936583 1404959 := bstep (se 1 (by rfl) ⟨1053719, by rfl⟩ : syracuseStep 1404959 = 2107439) B2107439
theorem B1404983 : Blo 936583 1404983 := bstep (se 1 (by rfl) ⟨1053737, by rfl⟩ : syracuseStep 1404983 = 2107475) B2107475
theorem B1405103 : Blo 936583 1405103 := bstep (se 1 (by rfl) ⟨1053827, by rfl⟩ : syracuseStep 1405103 = 2107655) B2107655
theorem B1503559 : Blo 936583 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B1405307 : Blo 936583 1405307 := bstep (se 1 (by rfl) ⟨1053980, by rfl⟩ : syracuseStep 1405307 = 2107961) B2107961
theorem B1405577 : Blo 936583 1405577 := bstep (se 2 (by rfl) ⟨527091, by rfl⟩ : syracuseStep 1405577 = 1054183) B1054183
theorem B1405787 : Blo 936583 1405787 := bstep (se 1 (by rfl) ⟨1054340, by rfl⟩ : syracuseStep 1405787 = 2108681) B2108681
theorem B1405817 : Blo 936583 1405817 := bstep (se 2 (by rfl) ⟨527181, by rfl⟩ : syracuseStep 1405817 = 1054363) B1054363
theorem B4748219 : Blo 936583 4748219 := bstep (se 1 (by rfl) ⟨3561164, by rfl⟩ : syracuseStep 4748219 = 7122329) B7122329
theorem B1406447 : Blo 936583 1406447 := bstep (se 1 (by rfl) ⟨1054835, by rfl⟩ : syracuseStep 1406447 = 2109671) B2109671
theorem B1406567 : Blo 936583 1406567 := bstep (se 1 (by rfl) ⟨1054925, by rfl⟩ : syracuseStep 1406567 = 2109851) B2109851
theorem B3012319 : Blo 936583 3012319 := bstep (se 1 (by rfl) ⟨2259239, by rfl⟩ : syracuseStep 3012319 = 4518479) B4518479
theorem B3569579 : Blo 936583 3569579 := bstep (se 1 (by rfl) ⟨2677184, by rfl⟩ : syracuseStep 3569579 = 5354369) B5354369
theorem B3798973 : Blo 936583 3798973 := bstep (se 3 (by rfl) ⟨712307, by rfl⟩ : syracuseStep 3798973 = 1424615) B1424615
theorem B1407023 : Blo 936583 1407023 := bstep (se 1 (by rfl) ⟨1055267, by rfl⟩ : syracuseStep 1407023 = 2110535) B2110535
theorem B1407143 : Blo 936583 1407143 := bstep (se 1 (by rfl) ⟨1055357, by rfl⟩ : syracuseStep 1407143 = 2110715) B2110715
theorem B4749515 : Blo 936583 4749515 := bstep (se 1 (by rfl) ⟨3562136, by rfl⟩ : syracuseStep 4749515 = 7124273) B7124273
theorem B5077235 : Blo 936583 5077235 := bstep (se 1 (by rfl) ⟨3807926, by rfl⟩ : syracuseStep 5077235 = 7615853) B7615853
theorem B22804739 : Blo 936583 22804739 := bstep (se 1 (by rfl) ⟨17103554, by rfl⟩ : syracuseStep 22804739 = 34207109) B34207109
theorem B1407287 : Blo 936583 1407287 := bstep (se 1 (by rfl) ⟨1055465, by rfl⟩ : syracuseStep 1407287 = 2110931) B2110931
theorem B1407467 : Blo 936583 1407467 := bstep (se 1 (by rfl) ⟨1055600, by rfl⟩ : syracuseStep 1407467 = 2111201) B2111201
theorem B1407815 : Blo 936583 1407815 := bstep (se 1 (by rfl) ⟨1055861, by rfl⟩ : syracuseStep 1407815 = 2111723) B2111723
theorem B1408649 : Blo 936583 1408649 := bstep (se 2 (by rfl) ⟨528243, by rfl⟩ : syracuseStep 1408649 = 1056487) B1056487
theorem B1408679 : Blo 936583 1408679 := bstep (se 1 (by rfl) ⟨1056509, by rfl⟩ : syracuseStep 1408679 = 2113019) B2113019
theorem B1408799 : Blo 936583 1408799 := bstep (se 1 (by rfl) ⟨1056599, by rfl⟩ : syracuseStep 1408799 = 2113199) B2113199
theorem B1408859 : Blo 936583 1408859 := bstep (se 1 (by rfl) ⟨1056644, by rfl⟩ : syracuseStep 1408859 = 2113289) B2113289
theorem B61669475 : Blo 936583 61669475 := bstep (se 1 (by rfl) ⟨46252106, by rfl⟩ : syracuseStep 61669475 = 92504213) B92504213
theorem B1409231 : Blo 936583 1409231 := bstep (se 1 (by rfl) ⟨1056923, by rfl⟩ : syracuseStep 1409231 = 2113847) B2113847
theorem B12846059 : Blo 936583 12846059 := bstep (se 1 (by rfl) ⟨9634544, by rfl⟩ : syracuseStep 12846059 = 19269089) B19269089
theorem B65046473 : Blo 936583 65046473 := bstep (se 2 (by rfl) ⟨24392427, by rfl⟩ : syracuseStep 65046473 = 48784855) B48784855
theorem B2002259 : Blo 936583 2002259 := bstep (se 1 (by rfl) ⟨1501694, by rfl⟩ : syracuseStep 2002259 = 3003389) B3003389
theorem B6753935 : Blo 936583 6753935 := bstep (se 1 (by rfl) ⟨5065451, by rfl⟩ : syracuseStep 6753935 = 10130903) B10130903
theorem B8032031 : Blo 936583 8032031 := bstep (se 1 (by rfl) ⟨6024023, by rfl⟩ : syracuseStep 8032031 = 12048047) B12048047
theorem B15242023 : Blo 936583 15242023 := bstep (se 1 (by rfl) ⟨11431517, by rfl⟩ : syracuseStep 15242023 = 22863035) B22863035
theorem B70325567 : Blo 936583 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B1054399 : Blo 936583 1054399 := bstep (se 1 (by rfl) ⟨790799, by rfl⟩ : syracuseStep 1054399 = 1581599) B1581599
theorem B1185511 : Blo 936583 1185511 := bstep (se 1 (by rfl) ⟨889133, by rfl⟩ : syracuseStep 1185511 = 1778267) B1778267
theorem B2004745 : Blo 936583 2004745 := bstep (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) B1503559
theorem B7608329 : Blo 936583 7608329 := bstep (se 2 (by rfl) ⟨2853123, by rfl⟩ : syracuseStep 7608329 = 5706247) B5706247
theorem B7116983 : Blo 936583 7116983 := bstep (se 1 (by rfl) ⟨5337737, by rfl⟩ : syracuseStep 7116983 = 10675475) B10675475
theorem B1055551 : Blo 936583 1055551 := bstep (se 1 (by rfl) ⟨791663, by rfl⟩ : syracuseStep 1055551 = 1583327) B1583327
theorem B4758587 : Blo 936583 4758587 := bstep (se 1 (by rfl) ⟨3568940, by rfl⟩ : syracuseStep 4758587 = 7137881) B7137881
theorem B3382505 : Blo 936583 3382505 := bstep (se 2 (by rfl) ⟨1268439, by rfl⟩ : syracuseStep 3382505 = 2536879) B2536879
theorem B8003123 : Blo 936583 8003123 := bstep (se 1 (by rfl) ⟨6002342, by rfl⟩ : syracuseStep 8003123 = 12004685) B12004685
theorem B1581295 : Blo 936583 1581295 := bstep (se 1 (by rfl) ⟨1185971, by rfl⟩ : syracuseStep 1581295 = 2371943) B2371943
theorem B1188199 : Blo 936583 1188199 := bstep (se 1 (by rfl) ⟨891149, by rfl⟩ : syracuseStep 1188199 = 1782299) B1782299
theorem B1581673 : Blo 936583 1581673 := bstep (se 2 (by rfl) ⟨593127, by rfl⟩ : syracuseStep 1581673 = 1186255) B1186255
theorem B13509305 : Blo 936583 13509305 := bstep (se 2 (by rfl) ⟨5065989, by rfl⟩ : syracuseStep 13509305 = 10131979) B10131979
theorem B1188847 : Blo 936583 1188847 := bstep (se 1 (by rfl) ⟨891635, by rfl⟩ : syracuseStep 1188847 = 1783271) B1783271
theorem B13509767 : Blo 936583 13509767 := bstep (se 1 (by rfl) ⟨10132325, by rfl⟩ : syracuseStep 13509767 = 20264651) B20264651
theorem B16065701 : Blo 936583 16065701 := bstep (se 4 (by rfl) ⟨1506159, by rfl⟩ : syracuseStep 16065701 = 3012319) B3012319
theorem B1582463 : Blo 936583 1582463 := bstep (se 1 (by rfl) ⟨1186847, by rfl⟩ : syracuseStep 1582463 = 2373695) B2373695
theorem B3384823 : Blo 936583 3384823 := bstep (se 1 (by rfl) ⟨2538617, by rfl⟩ : syracuseStep 3384823 = 5077235) B5077235
theorem B12854821 : Blo 936583 12854821 := bstep (se 4 (by rfl) ⟨1205139, by rfl⟩ : syracuseStep 12854821 = 2410279) B2410279
theorem B1779337 : Blo 936583 1779337 := bstep (se 2 (by rfl) ⟨667251, by rfl⟩ : syracuseStep 1779337 = 1334503) B1334503
theorem B2107529 : Blo 936583 2107529 := bstep (se 2 (by rfl) ⟨790323, by rfl⟩ : syracuseStep 2107529 = 1580647) B1580647
theorem B2107745 : Blo 936583 2107745 := bstep (se 2 (by rfl) ⟨790404, by rfl⟩ : syracuseStep 2107745 = 1580809) B1580809
theorem B61680203 : Blo 936583 61680203 := bstep (se 1 (by rfl) ⟨46260152, by rfl⟩ : syracuseStep 61680203 = 92520305) B92520305
theorem B1780537 : Blo 936583 1780537 := bstep (se 2 (by rfl) ⟨667701, by rfl⟩ : syracuseStep 1780537 = 1335403) B1335403
theorem B3386195 : Blo 936583 3386195 := bstep (se 1 (by rfl) ⟨2539646, by rfl⟩ : syracuseStep 3386195 = 5079293) B5079293
theorem B1584191 : Blo 936583 1584191 := bstep (se 1 (by rfl) ⟨1188143, by rfl⟩ : syracuseStep 1584191 = 2376287) B2376287
theorem B2370991 : Blo 936583 2370991 := bstep (se 1 (by rfl) ⟨1778243, by rfl⟩ : syracuseStep 2370991 = 3556487) B3556487
theorem B2108879 : Blo 936583 2108879 := bstep (se 1 (by rfl) ⟨1581659, by rfl⟩ : syracuseStep 2108879 = 3163319) B3163319
theorem B4009439 : Blo 936583 4009439 := bstep (se 1 (by rfl) ⟨3007079, by rfl⟩ : syracuseStep 4009439 = 6014159) B6014159
theorem B2371103 : Blo 936583 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B1584751 : Blo 936583 1584751 := bstep (se 1 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 1584751 = 2377127) B2377127
theorem B1584859 : Blo 936583 1584859 := bstep (se 1 (by rfl) ⟨1188644, by rfl⟩ : syracuseStep 1584859 = 2377289) B2377289
theorem B1781615 : Blo 936583 1781615 := bstep (se 1 (by rfl) ⟨1336211, by rfl⟩ : syracuseStep 1781615 = 2672423) B2672423
theorem B2371963 : Blo 936583 2371963 := bstep (se 1 (by rfl) ⟨1778972, by rfl⟩ : syracuseStep 2371963 = 3557945) B3557945
theorem B15249815 : Blo 936583 15249815 := bstep (se 1 (by rfl) ⟨11437361, by rfl⟩ : syracuseStep 15249815 = 22874723) B22874723
theorem B4010411 : Blo 936583 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B2372075 : Blo 936583 2372075 := bstep (se 1 (by rfl) ⟨1779056, by rfl⟩ : syracuseStep 2372075 = 3558113) B3558113
theorem B1586155 : Blo 936583 1586155 := bstep (se 1 (by rfl) ⟨1189616, by rfl⟩ : syracuseStep 1586155 = 2379233) B2379233
theorem B1586297 : Blo 936583 1586297 := bstep (se 2 (by rfl) ⟨594861, by rfl⟩ : syracuseStep 1586297 = 1189723) B1189723
theorem B16070075 : Blo 936583 16070075 := bstep (se 1 (by rfl) ⟨12052556, by rfl⟩ : syracuseStep 16070075 = 24105113) B24105113
theorem B4273775 : Blo 936583 4273775 := bstep (se 1 (by rfl) ⟨3205331, by rfl⟩ : syracuseStep 4273775 = 6410663) B6410663
theorem B2111183 : Blo 936583 2111183 := bstep (se 1 (by rfl) ⟨1583387, by rfl⟩ : syracuseStep 2111183 = 3166775) B3166775
theorem B2373401 : Blo 936583 2373401 := bstep (se 2 (by rfl) ⟨890025, by rfl⟩ : syracuseStep 2373401 = 1780051) B1780051
theorem B2668733 : Blo 936583 2668733 := bstep (se 3 (by rfl) ⟨500387, by rfl⟩ : syracuseStep 2668733 = 1000775) B1000775
theorem B1784015 : Blo 936583 1784015 := bstep (se 1 (by rfl) ⟨1338011, by rfl⟩ : syracuseStep 1784015 = 2676023) B2676023
theorem B5716271 : Blo 936583 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B15219251 : Blo 936583 15219251 := bstep (se 1 (by rfl) ⟨11414438, by rfl⟩ : syracuseStep 15219251 = 22828877) B22828877
theorem B2112083 : Blo 936583 2112083 := bstep (se 1 (by rfl) ⟨1584062, by rfl⟩ : syracuseStep 2112083 = 3168125) B3168125
theorem B23182199 : Blo 936583 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B5356601 : Blo 936583 5356601 := bstep (se 2 (by rfl) ⟨2008725, by rfl⟩ : syracuseStep 5356601 = 4017451) B4017451
theorem B1784987 : Blo 936583 1784987 := bstep (se 1 (by rfl) ⟨1338740, by rfl⟩ : syracuseStep 1784987 = 2677481) B2677481
theorem B2669735 : Blo 936583 2669735 := bstep (se 1 (by rfl) ⟨2002301, by rfl⟩ : syracuseStep 2669735 = 4004603) B4004603
theorem B3161591 : Blo 936583 3161591 := bstep (se 1 (by rfl) ⟨2371193, by rfl⟩ : syracuseStep 3161591 = 4742387) B4742387
theorem B2670191 : Blo 936583 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B3161753 : Blo 936583 3161753 := bstep (se 2 (by rfl) ⟨1185657, by rfl⟩ : syracuseStep 3161753 = 2371315) B2371315
theorem B7126703 : Blo 936583 7126703 := bstep (se 1 (by rfl) ⟨5345027, by rfl⟩ : syracuseStep 7126703 = 10690055) B10690055
theorem B10698803 : Blo 936583 10698803 := bstep (se 1 (by rfl) ⟨8024102, by rfl⟩ : syracuseStep 10698803 = 16048205) B16048205
theorem B4571321 : Blo 936583 4571321 := bstep (se 2 (by rfl) ⟨1714245, by rfl⟩ : syracuseStep 4571321 = 3428491) B3428491
theorem B237289945 : Blo 936583 237289945 := bstep (se 2 (by rfl) ⟨88983729, by rfl⟩ : syracuseStep 237289945 = 177967459) B177967459
theorem B2114207 : Blo 936583 2114207 := bstep (se 1 (by rfl) ⟨1585655, by rfl⟩ : syracuseStep 2114207 = 3171311) B3171311
theorem B24363773 : Blo 936583 24363773 := bstep (se 3 (by rfl) ⟨4568207, by rfl⟩ : syracuseStep 24363773 = 9136415) B9136415
theorem B3162887 : Blo 936583 3162887 := bstep (se 1 (by rfl) ⟨2372165, by rfl⟩ : syracuseStep 3162887 = 4744331) B4744331
theorem B2376479 : Blo 936583 2376479 := bstep (se 1 (by rfl) ⟨1782359, by rfl⟩ : syracuseStep 2376479 = 3564719) B3564719
theorem B3556183 : Blo 936583 3556183 := bstep (se 1 (by rfl) ⟨2667137, by rfl⟩ : syracuseStep 3556183 = 5334275) B5334275
theorem B2114441 : Blo 936583 2114441 := bstep (se 2 (by rfl) ⟨792915, by rfl⟩ : syracuseStep 2114441 = 1585831) B1585831
theorem B1524839 : Blo 936583 1524839 := bstep (se 1 (by rfl) ⟨1143629, by rfl⟩ : syracuseStep 1524839 = 2287259) B2287259
theorem B4506947 : Blo 936583 4506947 := bstep (se 1 (by rfl) ⟨3380210, by rfl⟩ : syracuseStep 4506947 = 6760421) B6760421
theorem B3163967 : Blo 936583 3163967 := bstep (se 1 (by rfl) ⟨2372975, by rfl⟩ : syracuseStep 3163967 = 4745951) B4745951
theorem B2443247 : Blo 936583 2443247 := bstep (se 1 (by rfl) ⟨1832435, by rfl⟩ : syracuseStep 2443247 = 3664871) B3664871
theorem B2377775 : Blo 936583 2377775 := bstep (se 1 (by rfl) ⟨1783331, by rfl⟩ : syracuseStep 2377775 = 3566663) B3566663
theorem B2115791 : Blo 936583 2115791 := bstep (se 1 (by rfl) ⟨1586843, by rfl⟩ : syracuseStep 2115791 = 3173687) B3173687
theorem B3164615 : Blo 936583 3164615 := bstep (se 1 (by rfl) ⟨2373461, by rfl⟩ : syracuseStep 3164615 = 4746923) B4746923
theorem B2378281 : Blo 936583 2378281 := bstep (se 2 (by rfl) ⟨891855, by rfl⟩ : syracuseStep 2378281 = 1783711) B1783711
theorem B5065297 : Blo 936583 5065297 := bstep (se 2 (by rfl) ⟨1899486, by rfl⟩ : syracuseStep 5065297 = 3798973) B3798973
theorem B5786255 : Blo 936583 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B936603 : Blo 936583 936603 := bstep (se 1 (by rfl) ⟨702452, by rfl⟩ : syracuseStep 936603 = 1404905) B1404905
theorem B936615 : Blo 936583 936615 := bstep (se 1 (by rfl) ⟨702461, by rfl⟩ : syracuseStep 936615 = 1404923) B1404923
theorem B936639 : Blo 936583 936639 := bstep (se 1 (by rfl) ⟨702479, by rfl⟩ : syracuseStep 936639 = 1404959) B1404959
theorem B936655 : Blo 936583 936655 := bstep (se 1 (by rfl) ⟨702491, by rfl⟩ : syracuseStep 936655 = 1404983) B1404983
theorem B936735 : Blo 936583 936735 := bstep (se 1 (by rfl) ⟨702551, by rfl⟩ : syracuseStep 936735 = 1405103) B1405103
theorem B936871 : Blo 936583 936871 := bstep (se 1 (by rfl) ⟨702653, by rfl⟩ : syracuseStep 936871 = 1405307) B1405307
theorem B937051 : Blo 936583 937051 := bstep (se 1 (by rfl) ⟨702788, by rfl⟩ : syracuseStep 937051 = 1405577) B1405577
theorem B937191 : Blo 936583 937191 := bstep (se 1 (by rfl) ⟨702893, by rfl⟩ : syracuseStep 937191 = 1405787) B1405787
theorem B937211 : Blo 936583 937211 := bstep (se 1 (by rfl) ⟨702908, by rfl⟩ : syracuseStep 937211 = 1405817) B1405817
theorem B3165479 : Blo 936583 3165479 := bstep (se 1 (by rfl) ⟨2374109, by rfl⟩ : syracuseStep 3165479 = 4748219) B4748219
theorem B937631 : Blo 936583 937631 := bstep (se 1 (by rfl) ⟨703223, by rfl⟩ : syracuseStep 937631 = 1406447) B1406447
theorem B937711 : Blo 936583 937711 := bstep (se 1 (by rfl) ⟨703283, by rfl⟩ : syracuseStep 937711 = 1406567) B1406567
theorem B16043831 : Blo 936583 16043831 := bstep (se 1 (by rfl) ⟨12032873, by rfl⟩ : syracuseStep 16043831 = 24065747) B24065747
theorem B1691489 : Blo 936583 1691489 := bstep (se 2 (by rfl) ⟨634308, by rfl⟩ : syracuseStep 1691489 = 1268617) B1268617
theorem B2379689 : Blo 936583 2379689 := bstep (se 2 (by rfl) ⟨892383, by rfl⟩ : syracuseStep 2379689 = 1784767) B1784767
theorem B2379719 : Blo 936583 2379719 := bstep (se 1 (by rfl) ⟨1784789, by rfl⟩ : syracuseStep 2379719 = 3569579) B3569579
theorem B938015 : Blo 936583 938015 := bstep (se 1 (by rfl) ⟨703511, by rfl⟩ : syracuseStep 938015 = 1407023) B1407023
theorem B938095 : Blo 936583 938095 := bstep (se 1 (by rfl) ⟨703571, by rfl⟩ : syracuseStep 938095 = 1407143) B1407143
theorem B3166343 : Blo 936583 3166343 := bstep (se 1 (by rfl) ⟨2374757, by rfl⟩ : syracuseStep 3166343 = 4749515) B4749515
theorem B3559585 : Blo 936583 3559585 := bstep (se 2 (by rfl) ⟨1334844, by rfl⟩ : syracuseStep 3559585 = 2669689) B2669689
theorem B938191 : Blo 936583 938191 := bstep (se 1 (by rfl) ⟨703643, by rfl⟩ : syracuseStep 938191 = 1407287) B1407287
theorem B3166505 : Blo 936583 3166505 := bstep (se 2 (by rfl) ⟨1187439, by rfl⟩ : syracuseStep 3166505 = 2374879) B2374879
theorem B938311 : Blo 936583 938311 := bstep (se 1 (by rfl) ⟨703733, by rfl⟩ : syracuseStep 938311 = 1407467) B1407467
theorem B938543 : Blo 936583 938543 := bstep (se 1 (by rfl) ⟨703907, by rfl⟩ : syracuseStep 938543 = 1407815) B1407815
theorem B939099 : Blo 936583 939099 := bstep (se 1 (by rfl) ⟨704324, by rfl⟩ : syracuseStep 939099 = 1408649) B1408649
theorem B3560557 : Blo 936583 3560557 := bstep (se 3 (by rfl) ⟨667604, by rfl⟩ : syracuseStep 3560557 = 1335209) B1335209
theorem B939119 : Blo 936583 939119 := bstep (se 1 (by rfl) ⟨704339, by rfl⟩ : syracuseStep 939119 = 1408679) B1408679
theorem B939199 : Blo 936583 939199 := bstep (se 1 (by rfl) ⟨704399, by rfl⟩ : syracuseStep 939199 = 1408799) B1408799
theorem B939239 : Blo 936583 939239 := bstep (se 1 (by rfl) ⟨704429, by rfl⟩ : syracuseStep 939239 = 1408859) B1408859
theorem B939519 : Blo 936583 939519 := bstep (se 1 (by rfl) ⟨704639, by rfl⟩ : syracuseStep 939519 = 1409279) B1409279
theorem B939623 : Blo 936583 939623 := bstep (se 1 (by rfl) ⟨704717, by rfl⟩ : syracuseStep 939623 = 1409435) B1409435
theorem B10704635 : Blo 936583 10704635 := bstep (se 1 (by rfl) ⟨8028476, by rfl⟩ : syracuseStep 10704635 = 16056953) B16056953
theorem B939903 : Blo 936583 939903 := bstep (se 1 (by rfl) ⟨704927, by rfl⟩ : syracuseStep 939903 = 1409855) B1409855
theorem B939999 : Blo 936583 939999 := bstep (se 1 (by rfl) ⟨704999, by rfl⟩ : syracuseStep 939999 = 1409999) B1409999
theorem B940059 : Blo 936583 940059 := bstep (se 1 (by rfl) ⟨705044, by rfl⟩ : syracuseStep 940059 = 1410089) B1410089
theorem B940079 : Blo 936583 940079 := bstep (se 1 (by rfl) ⟨705059, by rfl⟩ : syracuseStep 940079 = 1410119) B1410119
theorem B3168395 : Blo 936583 3168395 := bstep (se 1 (by rfl) ⟨2376296, by rfl⟩ : syracuseStep 3168395 = 4752593) B4752593
theorem B940199 : Blo 936583 940199 := bstep (se 1 (by rfl) ⟨705149, by rfl⟩ : syracuseStep 940199 = 1410299) B1410299
theorem B20896037 : Blo 936583 20896037 := bstep (se 4 (by rfl) ⟨1959003, by rfl⟩ : syracuseStep 20896037 = 3918007) B3918007
theorem B940391 : Blo 936583 940391 := bstep (se 1 (by rfl) ⟨705293, by rfl⟩ : syracuseStep 940391 = 1410587) B1410587
theorem B8018635 : Blo 936583 8018635 := bstep (se 1 (by rfl) ⟨6013976, by rfl⟩ : syracuseStep 8018635 = 12027953) B12027953
theorem B3005171 : Blo 936583 3005171 := bstep (se 1 (by rfl) ⟨2253878, by rfl⟩ : syracuseStep 3005171 = 4507757) B4507757
theorem B12016471 : Blo 936583 12016471 := bstep (se 1 (by rfl) ⟨9012353, by rfl⟩ : syracuseStep 12016471 = 18024707) B18024707
theorem B3169313 : Blo 936583 3169313 := bstep (se 2 (by rfl) ⟨1188492, by rfl⟩ : syracuseStep 3169313 = 2376985) B2376985
theorem B2677823 : Blo 936583 2677823 := bstep (se 1 (by rfl) ⟨2008367, by rfl⟩ : syracuseStep 2677823 = 4016735) B4016735
theorem B3563261 : Blo 936583 3563261 := bstep (se 3 (by rfl) ⟨668111, by rfl⟩ : syracuseStep 3563261 = 1336223) B1336223
theorem B10149799 : Blo 936583 10149799 := bstep (se 1 (by rfl) ⟨7612349, by rfl⟩ : syracuseStep 10149799 = 15224699) B15224699
theorem B30466003 : Blo 936583 30466003 := bstep (se 1 (by rfl) ⟨22849502, by rfl⟩ : syracuseStep 30466003 = 45699005) B45699005
theorem B18014561 : Blo 936583 18014561 := bstep (se 2 (by rfl) ⟨6755460, by rfl⟩ : syracuseStep 18014561 = 13510921) B13510921
theorem B3170717 : Blo 936583 3170717 := bstep (se 3 (by rfl) ⟨594509, by rfl⟩ : syracuseStep 3170717 = 1189019) B1189019
theorem B10707551 : Blo 936583 10707551 := bstep (se 1 (by rfl) ⟨8030663, by rfl⟩ : syracuseStep 10707551 = 16061327) B16061327
theorem B3433607 : Blo 936583 3433607 := bstep (se 1 (by rfl) ⟨2575205, by rfl⟩ : syracuseStep 3433607 = 5150411) B5150411
theorem B3565403 : Blo 936583 3565403 := bstep (se 1 (by rfl) ⟨2674052, by rfl⟩ : syracuseStep 3565403 = 5348105) B5348105
theorem B3172715 : Blo 936583 3172715 := bstep (se 1 (by rfl) ⟨2379536, by rfl⟩ : syracuseStep 3172715 = 4759073) B4759073
theorem B3566375 : Blo 936583 3566375 := bstep (se 1 (by rfl) ⟨2674781, by rfl⟩ : syracuseStep 3566375 = 5349563) B5349563
theorem B3173417 : Blo 936583 3173417 := bstep (se 2 (by rfl) ⟨1190031, by rfl⟩ : syracuseStep 3173417 = 2380063) B2380063
theorem B1405343 : Blo 936583 1405343 := bstep (se 1 (by rfl) ⟨1054007, by rfl⟩ : syracuseStep 1405343 = 2108015) B2108015
theorem B6418871 : Blo 936583 6418871 := bstep (se 1 (by rfl) ⟨4814153, by rfl⟩ : syracuseStep 6418871 = 9628307) B9628307
theorem B6779335 : Blo 936583 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B1405487 : Blo 936583 1405487 := bstep (se 1 (by rfl) ⟨1054115, by rfl⟩ : syracuseStep 1405487 = 2108231) B2108231
theorem B1602473 : Blo 936583 1602473 := bstep (se 2 (by rfl) ⟨600927, by rfl⟩ : syracuseStep 1602473 = 1201855) B1201855
theorem B6419503 : Blo 936583 6419503 := bstep (se 1 (by rfl) ⟨4814627, by rfl⟩ : syracuseStep 6419503 = 9629255) B9629255
theorem B5338331 : Blo 936583 5338331 := bstep (se 1 (by rfl) ⟨4003748, by rfl⟩ : syracuseStep 5338331 = 8007497) B8007497
theorem B1406441 : Blo 936583 1406441 := bstep (se 2 (by rfl) ⟨527415, by rfl⟩ : syracuseStep 1406441 = 1054831) B1054831
theorem B5338649 : Blo 936583 5338649 := bstep (se 2 (by rfl) ⟨2001993, by rfl⟩ : syracuseStep 5338649 = 4003987) B4003987
theorem B8025743 : Blo 936583 8025743 := bstep (se 1 (by rfl) ⟨6019307, by rfl⟩ : syracuseStep 8025743 = 12038615) B12038615
theorem B3569609 : Blo 936583 3569609 := bstep (se 2 (by rfl) ⟨1338603, by rfl⟩ : syracuseStep 3569609 = 2677207) B2677207
theorem B5339105 : Blo 936583 5339105 := bstep (se 2 (by rfl) ⟨2002164, by rfl⟩ : syracuseStep 5339105 = 4004329) B4004329
theorem B1407113 : Blo 936583 1407113 := bstep (se 2 (by rfl) ⟨527667, by rfl⟩ : syracuseStep 1407113 = 1055335) B1055335
theorem B1407227 : Blo 936583 1407227 := bstep (se 1 (by rfl) ⟨1055420, by rfl⟩ : syracuseStep 1407227 = 2110841) B2110841
theorem B1407311 : Blo 936583 1407311 := bstep (se 1 (by rfl) ⟨1055483, by rfl⟩ : syracuseStep 1407311 = 2110967) B2110967
theorem B15203159 : Blo 936583 15203159 := bstep (se 1 (by rfl) ⟨11402369, by rfl⟩ : syracuseStep 15203159 = 22804739) B22804739
theorem B1408031 : Blo 936583 1408031 := bstep (se 1 (by rfl) ⟨1056023, by rfl⟩ : syracuseStep 1408031 = 2112047) B2112047
theorem B8027657 : Blo 936583 8027657 := bstep (se 2 (by rfl) ⟨3010371, by rfl⟩ : syracuseStep 8027657 = 6020743) B6020743
theorem B1408559 : Blo 936583 1408559 := bstep (se 1 (by rfl) ⟨1056419, by rfl⟩ : syracuseStep 1408559 = 2112839) B2112839
theorem B1409471 : Blo 936583 1409471 := bstep (se 1 (by rfl) ⟨1057103, by rfl⟩ : syracuseStep 1409471 = 2114207) B2114207
theorem B12190189 : Blo 936583 12190189 := bstep (se 3 (by rfl) ⟨2285660, by rfl⟩ : syracuseStep 12190189 = 4571321) B4571321
theorem B1409627 : Blo 936583 1409627 := bstep (se 1 (by rfl) ⟨1057220, by rfl⟩ : syracuseStep 1409627 = 2114441) B2114441
theorem B1410527 : Blo 936583 1410527 := bstep (se 1 (by rfl) ⟨1057895, by rfl⟩ : syracuseStep 1410527 = 2115791) B2115791
theorem B17139761 : Blo 936583 17139761 := bstep (se 2 (by rfl) ⟨6427410, by rfl⟩ : syracuseStep 17139761 = 12854821) B12854821
theorem B4066237 : Blo 936583 4066237 := bstep (se 3 (by rfl) ⟨762419, by rfl⟩ : syracuseStep 4066237 = 1524839) B1524839
theorem B2003447 : Blo 936583 2003447 := bstep (se 1 (by rfl) ⟨1502585, by rfl⟩ : syracuseStep 2003447 = 3005171) B3005171
theorem B15243389 : Blo 936583 15243389 := bstep (se 3 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 15243389 = 5716271) B5716271
theorem B1054975 : Blo 936583 1054975 := bstep (se 1 (by rfl) ⟨791231, by rfl⟩ : syracuseStep 1054975 = 1582463) B1582463
theorem B20322697 : Blo 936583 20322697 := bstep (se 2 (by rfl) ⟨7621011, by rfl⟩ : syracuseStep 20322697 = 15242023) B15242023
theorem B1056127 : Blo 936583 1056127 := bstep (se 1 (by rfl) ⟨792095, by rfl⟩ : syracuseStep 1056127 = 1584191) B1584191
theorem B1580681 : Blo 936583 1580681 := bstep (se 2 (by rfl) ⟨592755, by rfl⟩ : syracuseStep 1580681 = 1185511) B1185511
theorem B1580735 : Blo 936583 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B10166543 : Blo 936583 10166543 := bstep (se 1 (by rfl) ⟨7624907, by rfl⟩ : syracuseStep 10166543 = 15249815) B15249815
theorem B1581383 : Blo 936583 1581383 := bstep (se 1 (by rfl) ⟨1186037, by rfl⟩ : syracuseStep 1581383 = 2372075) B2372075
theorem B1057531 : Blo 936583 1057531 := bstep (se 1 (by rfl) ⟨793148, by rfl⟩ : syracuseStep 1057531 = 1586297) B1586297
theorem B10691513 : Blo 936583 10691513 := bstep (se 2 (by rfl) ⟨4009317, by rfl⟩ : syracuseStep 10691513 = 8018635) B8018635
theorem B5350495 : Blo 936583 5350495 := bstep (se 1 (by rfl) ⟨4012871, by rfl⟩ : syracuseStep 5350495 = 8025743) B8025743
theorem B1582267 : Blo 936583 1582267 := bstep (se 1 (by rfl) ⟨1186700, by rfl⟩ : syracuseStep 1582267 = 2373401) B2373401
theorem B1779155 : Blo 936583 1779155 := bstep (se 1 (by rfl) ⟨1334366, by rfl⟩ : syracuseStep 1779155 = 2668733) B2668733
theorem B1189343 : Blo 936583 1189343 := bstep (se 1 (by rfl) ⟨892007, by rfl⟩ : syracuseStep 1189343 = 1784015) B1784015
theorem B10135439 : Blo 936583 10135439 := bstep (se 1 (by rfl) ⟨7601579, by rfl⟩ : syracuseStep 10135439 = 15203159) B15203159
theorem B1189991 : Blo 936583 1189991 := bstep (se 1 (by rfl) ⟨892493, by rfl⟩ : syracuseStep 1189991 = 1784987) B1784987
theorem B1779823 : Blo 936583 1779823 := bstep (se 1 (by rfl) ⟨1334867, by rfl⟩ : syracuseStep 1779823 = 2669735) B2669735
theorem B2107727 : Blo 936583 2107727 := bstep (se 1 (by rfl) ⟨1580795, by rfl⟩ : syracuseStep 2107727 = 3161591) B3161591
theorem B5351771 : Blo 936583 5351771 := bstep (se 1 (by rfl) ⟨4013828, by rfl⟩ : syracuseStep 5351771 = 8027657) B8027657
theorem B1780127 : Blo 936583 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B2107835 : Blo 936583 2107835 := bstep (se 1 (by rfl) ⟨1580876, by rfl⟩ : syracuseStep 2107835 = 3161753) B3161753
theorem B2108393 : Blo 936583 2108393 := bstep (se 2 (by rfl) ⟨790647, by rfl⟩ : syracuseStep 2108393 = 1581295) B1581295
theorem B1584265 : Blo 936583 1584265 := bstep (se 2 (by rfl) ⟨594099, by rfl⟩ : syracuseStep 1584265 = 1188199) B1188199
theorem B2108591 : Blo 936583 2108591 := bstep (se 1 (by rfl) ⟨1581443, by rfl⟩ : syracuseStep 2108591 = 3162887) B3162887
theorem B1584319 : Blo 936583 1584319 := bstep (se 1 (by rfl) ⟨1188239, by rfl⟩ : syracuseStep 1584319 = 2376479) B2376479
theorem B316386593 : Blo 936583 316386593 := bstep (se 2 (by rfl) ⟨118644972, by rfl⟩ : syracuseStep 316386593 = 237289945) B237289945
theorem B8564039 : Blo 936583 8564039 := bstep (se 1 (by rfl) ⟨6423029, by rfl⟩ : syracuseStep 8564039 = 12846059) B12846059
theorem B2108897 : Blo 936583 2108897 := bstep (se 2 (by rfl) ⟨790836, by rfl⟩ : syracuseStep 2108897 = 1581673) B1581673
theorem B10694429 : Blo 936583 10694429 := bstep (se 3 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 10694429 = 4010411) B4010411
theorem B2109311 : Blo 936583 2109311 := bstep (se 1 (by rfl) ⟨1581983, by rfl⟩ : syracuseStep 2109311 = 3163967) B3163967
theorem B43364315 : Blo 936583 43364315 := bstep (se 1 (by rfl) ⟨32523236, by rfl⟩ : syracuseStep 43364315 = 65046473) B65046473
theorem B1585129 : Blo 936583 1585129 := bstep (se 2 (by rfl) ⟨594423, by rfl⟩ : syracuseStep 1585129 = 1188847) B1188847
theorem B1585183 : Blo 936583 1585183 := bstep (se 1 (by rfl) ⟨1188887, by rfl⟩ : syracuseStep 1585183 = 2377775) B2377775
theorem B891564245 : Blo 936583 891564245 := bstep (se 7 (by rfl) ⟨10448018, by rfl⟩ : syracuseStep 891564245 = 20896037) B20896037
theorem B2109743 : Blo 936583 2109743 := bstep (se 1 (by rfl) ⟨1582307, by rfl⟩ : syracuseStep 2109743 = 3164615) B3164615
theorem B2372449 : Blo 936583 2372449 := bstep (se 2 (by rfl) ⟨889668, by rfl⟩ : syracuseStep 2372449 = 1779337) B1779337
theorem B2110319 : Blo 936583 2110319 := bstep (se 1 (by rfl) ⟨1582739, by rfl⟩ : syracuseStep 2110319 = 3165479) B3165479
theorem B4502623 : Blo 936583 4502623 := bstep (se 1 (by rfl) ⟨3376967, by rfl⟩ : syracuseStep 4502623 = 6753935) B6753935
theorem B5354687 : Blo 936583 5354687 := bstep (se 1 (by rfl) ⟨4016015, by rfl⟩ : syracuseStep 5354687 = 8032031) B8032031
theorem B10695887 : Blo 936583 10695887 := bstep (se 1 (by rfl) ⟨8021915, by rfl⟩ : syracuseStep 10695887 = 16043831) B16043831
theorem B1586459 : Blo 936583 1586459 := bstep (se 1 (by rfl) ⟨1189844, by rfl⟩ : syracuseStep 1586459 = 2379689) B2379689
theorem B1586479 : Blo 936583 1586479 := bstep (se 1 (by rfl) ⟨1189859, by rfl⟩ : syracuseStep 1586479 = 2379719) B2379719
theorem B2110895 : Blo 936583 2110895 := bstep (se 1 (by rfl) ⟨1583171, by rfl⟩ : syracuseStep 2110895 = 3166343) B3166343
theorem B2111003 : Blo 936583 2111003 := bstep (se 1 (by rfl) ⟨1583252, by rfl⟩ : syracuseStep 2111003 = 3166505) B3166505
theorem B27014917 : Blo 936583 27014917 := bstep (se 4 (by rfl) ⟨2532648, by rfl⟩ : syracuseStep 27014917 = 5065297) B5065297
theorem B2374049 : Blo 936583 2374049 := bstep (se 2 (by rfl) ⟨890268, by rfl⟩ : syracuseStep 2374049 = 1780537) B1780537
theorem B2112263 : Blo 936583 2112263 := bstep (se 1 (by rfl) ⟨1584197, by rfl⟩ : syracuseStep 2112263 = 3168395) B3168395
theorem B3161321 : Blo 936583 3161321 := bstep (se 2 (by rfl) ⟨1185495, by rfl⟩ : syracuseStep 3161321 = 2370991) B2370991
theorem B2112875 : Blo 936583 2112875 := bstep (se 1 (by rfl) ⟨1584656, by rfl⟩ : syracuseStep 2112875 = 3169313) B3169313
theorem B1785215 : Blo 936583 1785215 := bstep (se 1 (by rfl) ⟨1338911, by rfl⟩ : syracuseStep 1785215 = 2677823) B2677823
theorem B2113001 : Blo 936583 2113001 := bstep (se 2 (by rfl) ⟨792375, by rfl⟩ : syracuseStep 2113001 = 1584751) B1584751
theorem B2113145 : Blo 936583 2113145 := bstep (se 2 (by rfl) ⟨792429, by rfl⟩ : syracuseStep 2113145 = 1584859) B1584859
theorem B2375507 : Blo 936583 2375507 := bstep (se 1 (by rfl) ⟨1781630, by rfl⟩ : syracuseStep 2375507 = 3563261) B3563261
theorem B12009707 : Blo 936583 12009707 := bstep (se 1 (by rfl) ⟨9007280, by rfl⟩ : syracuseStep 12009707 = 18014561) B18014561
theorem B2113811 : Blo 936583 2113811 := bstep (se 1 (by rfl) ⟨1585358, by rfl⟩ : syracuseStep 2113811 = 3170717) B3170717
theorem B3162617 : Blo 936583 3162617 := bstep (se 2 (by rfl) ⟨1185981, by rfl⟩ : syracuseStep 3162617 = 2371963) B2371963
theorem B2376935 : Blo 936583 2376935 := bstep (se 1 (by rfl) ⟨1782701, by rfl⟩ : syracuseStep 2376935 = 3565403) B3565403
theorem B2114873 : Blo 936583 2114873 := bstep (se 2 (by rfl) ⟨793077, by rfl⟩ : syracuseStep 2114873 = 1586155) B1586155
theorem B2115143 : Blo 936583 2115143 := bstep (se 1 (by rfl) ⟨1586357, by rfl⟩ : syracuseStep 2115143 = 3172715) B3172715
theorem B2377583 : Blo 936583 2377583 := bstep (se 1 (by rfl) ⟨1783187, by rfl⟩ : syracuseStep 2377583 = 3566375) B3566375
theorem B2115611 : Blo 936583 2115611 := bstep (se 1 (by rfl) ⟨1586708, by rfl⟩ : syracuseStep 2115611 = 3173417) B3173417
theorem B2672959 : Blo 936583 2672959 := bstep (se 1 (by rfl) ⟨2004719, by rfl⟩ : syracuseStep 2672959 = 4009439) B4009439
theorem B2672993 : Blo 936583 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B936895 : Blo 936583 936895 := bstep (se 1 (by rfl) ⟨702671, by rfl⟩ : syracuseStep 936895 = 1405343) B1405343
theorem B4279247 : Blo 936583 4279247 := bstep (se 1 (by rfl) ⟨3209435, by rfl⟩ : syracuseStep 4279247 = 6418871) B6418871
theorem B936991 : Blo 936583 936991 := bstep (se 1 (by rfl) ⟨702743, by rfl⟩ : syracuseStep 936991 = 1405487) B1405487
theorem B3558887 : Blo 936583 3558887 := bstep (se 1 (by rfl) ⟨2669165, by rfl⟩ : syracuseStep 3558887 = 5338331) B5338331
theorem B937627 : Blo 936583 937627 := bstep (se 1 (by rfl) ⟨703220, by rfl⟩ : syracuseStep 937627 = 1406441) B1406441
theorem B3559099 : Blo 936583 3559099 := bstep (se 1 (by rfl) ⟨2669324, by rfl⟩ : syracuseStep 3559099 = 5338649) B5338649
theorem B2379739 : Blo 936583 2379739 := bstep (se 1 (by rfl) ⟨1784804, by rfl⟩ : syracuseStep 2379739 = 3569609) B3569609
theorem B3559403 : Blo 936583 3559403 := bstep (se 1 (by rfl) ⟨2669552, by rfl⟩ : syracuseStep 3559403 = 5339105) B5339105
theorem B938075 : Blo 936583 938075 := bstep (se 1 (by rfl) ⟨703556, by rfl⟩ : syracuseStep 938075 = 1407113) B1407113
theorem B938151 : Blo 936583 938151 := bstep (se 1 (by rfl) ⟨703613, by rfl⟩ : syracuseStep 938151 = 1407227) B1407227
theorem B938207 : Blo 936583 938207 := bstep (se 1 (by rfl) ⟨703655, by rfl⟩ : syracuseStep 938207 = 1407311) B1407311
theorem B10146167 : Blo 936583 10146167 := bstep (se 1 (by rfl) ⟨7609625, by rfl⟩ : syracuseStep 10146167 = 15219251) B15219251
theorem B17093045 : Blo 936583 17093045 := bstep (se 5 (by rfl) ⟨801236, by rfl⟩ : syracuseStep 17093045 = 1602473) B1602473
theorem B15454799 : Blo 936583 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B938687 : Blo 936583 938687 := bstep (se 1 (by rfl) ⟨704015, by rfl⟩ : syracuseStep 938687 = 1408031) B1408031
theorem B4510637 : Blo 936583 4510637 := bstep (se 3 (by rfl) ⟨845744, by rfl⟩ : syracuseStep 4510637 = 1691489) B1691489
theorem B939039 : Blo 936583 939039 := bstep (se 1 (by rfl) ⟨704279, by rfl⟩ : syracuseStep 939039 = 1408559) B1408559
theorem B40621337 : Blo 936583 40621337 := bstep (se 2 (by rfl) ⟨15233001, by rfl⟩ : syracuseStep 40621337 = 30466003) B30466003
theorem B7132535 : Blo 936583 7132535 := bstep (se 1 (by rfl) ⟨5349401, by rfl⟩ : syracuseStep 7132535 = 10698803) B10698803
theorem B41112983 : Blo 936583 41112983 := bstep (se 1 (by rfl) ⟨30834737, by rfl⟩ : syracuseStep 41112983 = 61669475) B61669475
theorem B939487 : Blo 936583 939487 := bstep (se 1 (by rfl) ⟨704615, by rfl⟩ : syracuseStep 939487 = 1409231) B1409231
theorem B16242515 : Blo 936583 16242515 := bstep (se 1 (by rfl) ⟨12181886, by rfl⟩ : syracuseStep 16242515 = 24363773) B24363773
theorem B3004631 : Blo 936583 3004631 := bstep (se 1 (by rfl) ⟨2253473, by rfl⟩ : syracuseStep 3004631 = 4506947) B4506947
theorem B4741577 : Blo 936583 4741577 := bstep (se 2 (by rfl) ⟨1778091, by rfl⟩ : syracuseStep 4741577 = 3556183) B3556183
theorem B1628831 : Blo 936583 1628831 := bstep (se 1 (by rfl) ⟨1221623, by rfl⟩ : syracuseStep 1628831 = 2443247) B2443247
theorem B3857503 : Blo 936583 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B4513097 : Blo 936583 4513097 := bstep (se 2 (by rfl) ⟨1692411, by rfl⟩ : syracuseStep 4513097 = 3384823) B3384823
theorem B3171041 : Blo 936583 3171041 := bstep (se 2 (by rfl) ⟨1189140, by rfl⟩ : syracuseStep 3171041 = 2378281) B2378281
theorem B46883711 : Blo 936583 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B7136423 : Blo 936583 7136423 := bstep (se 1 (by rfl) ⟨5352317, by rfl⟩ : syracuseStep 7136423 = 10704635) B10704635
theorem B5072219 : Blo 936583 5072219 := bstep (se 1 (by rfl) ⟨3804164, by rfl⟩ : syracuseStep 5072219 = 7608329) B7608329
theorem B4744655 : Blo 936583 4744655 := bstep (se 1 (by rfl) ⟨3558491, by rfl⟩ : syracuseStep 4744655 = 7116983) B7116983
theorem B3172391 : Blo 936583 3172391 := bstep (se 1 (by rfl) ⟨2379293, by rfl⟩ : syracuseStep 3172391 = 4758587) B4758587
theorem B2255003 : Blo 936583 2255003 := bstep (se 1 (by rfl) ⟨1691252, by rfl⟩ : syracuseStep 2255003 = 3382505) B3382505
theorem B5335415 : Blo 936583 5335415 := bstep (se 1 (by rfl) ⟨4001561, by rfl⟩ : syracuseStep 5335415 = 8003123) B8003123
theorem B4746113 : Blo 936583 4746113 := bstep (se 2 (by rfl) ⟨1779792, by rfl⟩ : syracuseStep 4746113 = 3559585) B3559585
theorem B34237349 : Blo 936583 34237349 := bstep (se 4 (by rfl) ⟨3209751, by rfl⟩ : syracuseStep 34237349 = 6419503) B6419503
theorem B7138367 : Blo 936583 7138367 := bstep (se 1 (by rfl) ⟨5353775, by rfl⟩ : syracuseStep 7138367 = 10707551) B10707551
theorem B9006203 : Blo 936583 9006203 := bstep (se 1 (by rfl) ⟨6754652, by rfl⟩ : syracuseStep 9006203 = 13509305) B13509305
theorem B9039113 : Blo 936583 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B9006511 : Blo 936583 9006511 := bstep (se 1 (by rfl) ⟨6754883, by rfl⟩ : syracuseStep 9006511 = 13509767) B13509767
theorem B2289071 : Blo 936583 2289071 := bstep (se 1 (by rfl) ⟨1716803, by rfl⟩ : syracuseStep 2289071 = 3433607) B3433607
theorem B10710467 : Blo 936583 10710467 := bstep (se 1 (by rfl) ⟨8032850, by rfl⟩ : syracuseStep 10710467 = 16065701) B16065701
theorem B1405019 : Blo 936583 1405019 := bstep (se 1 (by rfl) ⟨1053764, by rfl⟩ : syracuseStep 1405019 = 2107529) B2107529
theorem B4747409 : Blo 936583 4747409 := bstep (se 2 (by rfl) ⟨1780278, by rfl⟩ : syracuseStep 4747409 = 3560557) B3560557
theorem B1405163 : Blo 936583 1405163 := bstep (se 1 (by rfl) ⟨1053872, by rfl⟩ : syracuseStep 1405163 = 2107745) B2107745
theorem B41120135 : Blo 936583 41120135 := bstep (se 1 (by rfl) ⟨30840101, by rfl⟩ : syracuseStep 41120135 = 61680203) B61680203
theorem B2257463 : Blo 936583 2257463 := bstep (se 1 (by rfl) ⟨1693097, by rfl⟩ : syracuseStep 2257463 = 3386195) B3386195
theorem B1405865 : Blo 936583 1405865 := bstep (se 2 (by rfl) ⟨527199, by rfl⟩ : syracuseStep 1405865 = 1054399) B1054399
theorem B1405919 : Blo 936583 1405919 := bstep (se 1 (by rfl) ⟨1054439, by rfl⟩ : syracuseStep 1405919 = 2108879) B2108879
theorem B5339357 : Blo 936583 5339357 := bstep (se 3 (by rfl) ⟨1001129, by rfl⟩ : syracuseStep 5339357 = 2002259) B2002259
theorem B10713383 : Blo 936583 10713383 := bstep (se 1 (by rfl) ⟨8035037, by rfl⟩ : syracuseStep 10713383 = 16070075) B16070075
theorem B2849183 : Blo 936583 2849183 := bstep (se 1 (by rfl) ⟨2136887, by rfl⟩ : syracuseStep 2849183 = 4273775) B4273775
theorem B1407401 : Blo 936583 1407401 := bstep (se 2 (by rfl) ⟨527775, by rfl⟩ : syracuseStep 1407401 = 1055551) B1055551
theorem B16021961 : Blo 936583 16021961 := bstep (se 2 (by rfl) ⟨6008235, by rfl⟩ : syracuseStep 16021961 = 12016471) B12016471
theorem B1407455 : Blo 936583 1407455 := bstep (se 1 (by rfl) ⟨1055591, by rfl⟩ : syracuseStep 1407455 = 2111183) B2111183
theorem B1408055 : Blo 936583 1408055 := bstep (se 1 (by rfl) ⟨1056041, by rfl⟩ : syracuseStep 1408055 = 2112083) B2112083
theorem B3571067 : Blo 936583 3571067 := bstep (se 1 (by rfl) ⟨2678300, by rfl⟩ : syracuseStep 3571067 = 5356601) B5356601
theorem B4750973 : Blo 936583 4750973 := bstep (se 3 (by rfl) ⟨890807, by rfl⟩ : syracuseStep 4750973 = 1781615) B1781615
theorem B4751135 : Blo 936583 4751135 := bstep (se 1 (by rfl) ⟨3563351, by rfl⟩ : syracuseStep 4751135 = 7126703) B7126703
theorem B13533065 : Blo 936583 13533065 := bstep (se 2 (by rfl) ⟨5074899, by rfl⟩ : syracuseStep 13533065 = 10149799) B10149799
theorem B1409207 : Blo 936583 1409207 := bstep (se 1 (by rfl) ⟨1056905, by rfl⟩ : syracuseStep 1409207 = 2113811) B2113811
theorem B16253585 : Blo 936583 16253585 := bstep (se 2 (by rfl) ⟨6095094, by rfl⟩ : syracuseStep 16253585 = 12190189) B12190189
theorem B1409915 : Blo 936583 1409915 := bstep (se 1 (by rfl) ⟨1057436, by rfl⟩ : syracuseStep 1409915 = 2114873) B2114873
theorem B1410041 : Blo 936583 1410041 := bstep (se 2 (by rfl) ⟨528765, by rfl⟩ : syracuseStep 1410041 = 1057531) B1057531
theorem B1410095 : Blo 936583 1410095 := bstep (se 1 (by rfl) ⟨1057571, by rfl⟩ : syracuseStep 1410095 = 2115143) B2115143
theorem B45581453 : Blo 936583 45581453 := bstep (se 3 (by rfl) ⟨8546522, by rfl⟩ : syracuseStep 45581453 = 17093045) B17093045
theorem B1410407 : Blo 936583 1410407 := bstep (se 1 (by rfl) ⟨1057805, by rfl⟩ : syracuseStep 1410407 = 2115611) B2115611
theorem B2852831 : Blo 936583 2852831 := bstep (se 1 (by rfl) ⟨2139623, by rfl⟩ : syracuseStep 2852831 = 4279247) B4279247
theorem B4755023 : Blo 936583 4755023 := bstep (se 1 (by rfl) ⟨3566267, by rfl⟩ : syracuseStep 4755023 = 7132535) B7132535
theorem B10162259 : Blo 936583 10162259 := bstep (se 1 (by rfl) ⟨7621694, by rfl⟩ : syracuseStep 10162259 = 15243389) B15243389
theorem B2003087 : Blo 936583 2003087 := bstep (se 1 (by rfl) ⟨1502315, by rfl⟩ : syracuseStep 2003087 = 3004631) B3004631
theorem B1053787 : Blo 936583 1053787 := bstep (se 1 (by rfl) ⟨790340, by rfl⟩ : syracuseStep 1053787 = 1580681) B1580681
theorem B1053823 : Blo 936583 1053823 := bstep (se 1 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 1053823 = 1580735) B1580735
theorem B1054255 : Blo 936583 1054255 := bstep (se 1 (by rfl) ⟨790691, by rfl⟩ : syracuseStep 1054255 = 1581383) B1581383
theorem B4757615 : Blo 936583 4757615 := bstep (se 1 (by rfl) ⟨3568211, by rfl⟩ : syracuseStep 4757615 = 7136423) B7136423
theorem B3381479 : Blo 936583 3381479 := bstep (se 1 (by rfl) ⟨2536109, by rfl⟩ : syracuseStep 3381479 = 5072219) B5072219
theorem B1186103 : Blo 936583 1186103 := bstep (se 1 (by rfl) ⟨889577, by rfl⟩ : syracuseStep 1186103 = 1779155) B1779155
theorem B6756959 : Blo 936583 6756959 := bstep (se 1 (by rfl) ⟨5067719, by rfl⟩ : syracuseStep 6756959 = 10135439) B10135439
theorem B6003497 : Blo 936583 6003497 := bstep (se 2 (by rfl) ⟨2251311, by rfl⟩ : syracuseStep 6003497 = 4502623) B4502623
theorem B1186751 : Blo 936583 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B4758911 : Blo 936583 4758911 := bstep (se 1 (by rfl) ⟨3569183, by rfl⟩ : syracuseStep 4758911 = 7138367) B7138367
theorem B6004135 : Blo 936583 6004135 := bstep (se 1 (by rfl) ⟨4503101, by rfl⟩ : syracuseStep 6004135 = 9006203) B9006203
theorem B5709359 : Blo 936583 5709359 := bstep (se 1 (by rfl) ⟨4282019, by rfl⟩ : syracuseStep 5709359 = 8564039) B8564039
theorem B36019889 : Blo 936583 36019889 := bstep (se 2 (by rfl) ⟨13507458, by rfl⟩ : syracuseStep 36019889 = 27014917) B27014917
theorem B28909543 : Blo 936583 28909543 := bstep (se 1 (by rfl) ⟨21682157, by rfl⟩ : syracuseStep 28909543 = 43364315) B43364315
theorem B1057639 : Blo 936583 1057639 := bstep (se 1 (by rfl) ⟨793229, by rfl⟩ : syracuseStep 1057639 = 1586459) B1586459
theorem B12034925 : Blo 936583 12034925 := bstep (se 3 (by rfl) ⟨2256548, by rfl⟩ : syracuseStep 12034925 = 4513097) B4513097
theorem B1582699 : Blo 936583 1582699 := bstep (se 1 (by rfl) ⟨1187024, by rfl⟩ : syracuseStep 1582699 = 2374049) B2374049
theorem B2107547 : Blo 936583 2107547 := bstep (se 1 (by rfl) ⟨1580660, by rfl⟩ : syracuseStep 2107547 = 3161321) B3161321
theorem B1190143 : Blo 936583 1190143 := bstep (se 1 (by rfl) ⟨892607, by rfl⟩ : syracuseStep 1190143 = 1785215) B1785215
theorem B1583671 : Blo 936583 1583671 := bstep (se 1 (by rfl) ⟨1187753, by rfl⟩ : syracuseStep 1583671 = 2375507) B2375507
theorem B9022043 : Blo 936583 9022043 := bstep (se 1 (by rfl) ⟨6766532, by rfl⟩ : syracuseStep 9022043 = 13533065) B13533065
theorem B8006471 : Blo 936583 8006471 := bstep (se 1 (by rfl) ⟨6004853, by rfl⟩ : syracuseStep 8006471 = 12009707) B12009707
theorem B2108411 : Blo 936583 2108411 := bstep (se 1 (by rfl) ⟨1581308, by rfl⟩ : syracuseStep 2108411 = 3162617) B3162617
theorem B1584623 : Blo 936583 1584623 := bstep (se 1 (by rfl) ⟨1188467, by rfl⟩ : syracuseStep 1584623 = 2376935) B2376935
theorem B1585055 : Blo 936583 1585055 := bstep (se 1 (by rfl) ⟨1188791, by rfl⟩ : syracuseStep 1585055 = 2377583) B2377583
theorem B1781995 : Blo 936583 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B2109689 : Blo 936583 2109689 := bstep (se 2 (by rfl) ⟨791133, by rfl⟩ : syracuseStep 2109689 = 1582267) B1582267
theorem B2372591 : Blo 936583 2372591 := bstep (se 1 (by rfl) ⟨1779443, by rfl⟩ : syracuseStep 2372591 = 3558887) B3558887
theorem B2372935 : Blo 936583 2372935 := bstep (se 1 (by rfl) ⟨1779701, by rfl⟩ : syracuseStep 2372935 = 3559403) B3559403
theorem B2373097 : Blo 936583 2373097 := bstep (se 2 (by rfl) ⟨889911, by rfl⟩ : syracuseStep 2373097 = 1779823) B1779823
theorem B6764111 : Blo 936583 6764111 := bstep (se 1 (by rfl) ⟨5073083, by rfl⟩ : syracuseStep 6764111 = 10146167) B10146167
theorem B10303199 : Blo 936583 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B27080891 : Blo 936583 27080891 := bstep (se 1 (by rfl) ⟨20310668, by rfl⟩ : syracuseStep 27080891 = 40621337) B40621337
theorem B27408655 : Blo 936583 27408655 := bstep (se 1 (by rfl) ⟨20556491, by rfl⟩ : syracuseStep 27408655 = 41112983) B41112983
theorem B10828343 : Blo 936583 10828343 := bstep (se 1 (by rfl) ⟨8121257, by rfl⟩ : syracuseStep 10828343 = 16242515) B16242515
theorem B5421649 : Blo 936583 5421649 := bstep (se 2 (by rfl) ⟨2033118, by rfl⟩ : syracuseStep 5421649 = 4066237) B4066237
theorem B2112353 : Blo 936583 2112353 := bstep (se 2 (by rfl) ⟨792132, by rfl⟩ : syracuseStep 2112353 = 1584265) B1584265
theorem B2112425 : Blo 936583 2112425 := bstep (se 2 (by rfl) ⟨792159, by rfl⟩ : syracuseStep 2112425 = 1584319) B1584319
theorem B3161051 : Blo 936583 3161051 := bstep (se 1 (by rfl) ⟨2370788, by rfl⟩ : syracuseStep 3161051 = 4741577) B4741577
theorem B12008681 : Blo 936583 12008681 := bstep (se 2 (by rfl) ⟨4503255, by rfl⟩ : syracuseStep 12008681 = 9006511) B9006511
theorem B2113505 : Blo 936583 2113505 := bstep (se 2 (by rfl) ⟨792564, by rfl⟩ : syracuseStep 2113505 = 1585129) B1585129
theorem B2113577 : Blo 936583 2113577 := bstep (se 2 (by rfl) ⟨792591, by rfl⟩ : syracuseStep 2113577 = 1585183) B1585183
theorem B2114027 : Blo 936583 2114027 := bstep (se 1 (by rfl) ⟨1585520, by rfl⟩ : syracuseStep 2114027 = 3171041) B3171041
theorem B7127675 : Blo 936583 7127675 := bstep (se 1 (by rfl) ⟨5345756, by rfl⟩ : syracuseStep 7127675 = 10691513) B10691513
theorem B3163103 : Blo 936583 3163103 := bstep (se 1 (by rfl) ⟨2372327, by rfl⟩ : syracuseStep 3163103 = 4744655) B4744655
theorem B3163265 : Blo 936583 3163265 := bstep (se 2 (by rfl) ⟨1186224, by rfl⟩ : syracuseStep 3163265 = 2372449) B2372449
theorem B2114927 : Blo 936583 2114927 := bstep (se 1 (by rfl) ⟨1586195, by rfl⟩ : syracuseStep 2114927 = 3172391) B3172391
theorem B3556943 : Blo 936583 3556943 := bstep (se 1 (by rfl) ⟨2667707, by rfl⟩ : syracuseStep 3556943 = 5335415) B5335415
theorem B2115305 : Blo 936583 2115305 := bstep (se 2 (by rfl) ⟨793239, by rfl⟩ : syracuseStep 2115305 = 1586479) B1586479
theorem B4343549 : Blo 936583 4343549 := bstep (se 3 (by rfl) ⟨814415, by rfl⟩ : syracuseStep 4343549 = 1628831) B1628831
theorem B3164075 : Blo 936583 3164075 := bstep (se 1 (by rfl) ⟨2373056, by rfl⟩ : syracuseStep 3164075 = 4746113) B4746113
theorem B22824899 : Blo 936583 22824899 := bstep (se 1 (by rfl) ⟨17118674, by rfl⟩ : syracuseStep 22824899 = 34237349) B34237349
theorem B1526047 : Blo 936583 1526047 := bstep (se 1 (by rfl) ⟨1144535, by rfl⟩ : syracuseStep 1526047 = 2289071) B2289071
theorem B7129619 : Blo 936583 7129619 := bstep (se 1 (by rfl) ⟨5347214, by rfl⟩ : syracuseStep 7129619 = 10694429) B10694429
theorem B936679 : Blo 936583 936679 := bstep (se 1 (by rfl) ⟨702509, by rfl⟩ : syracuseStep 936679 = 1405019) B1405019
theorem B3164939 : Blo 936583 3164939 := bstep (se 1 (by rfl) ⟨2373704, by rfl⟩ : syracuseStep 3164939 = 4747409) B4747409
theorem B936775 : Blo 936583 936775 := bstep (se 1 (by rfl) ⟨702581, by rfl⟩ : syracuseStep 936775 = 1405163) B1405163
theorem B27413423 : Blo 936583 27413423 := bstep (se 1 (by rfl) ⟨20560067, by rfl⟩ : syracuseStep 27413423 = 41120135) B41120135
theorem B937243 : Blo 936583 937243 := bstep (se 1 (by rfl) ⟨702932, by rfl⟩ : syracuseStep 937243 = 1405865) B1405865
theorem B937279 : Blo 936583 937279 := bstep (se 1 (by rfl) ⟨702959, by rfl⟩ : syracuseStep 937279 = 1405919) B1405919
theorem B7130591 : Blo 936583 7130591 := bstep (se 1 (by rfl) ⟨5347943, by rfl⟩ : syracuseStep 7130591 = 10695887) B10695887
theorem B3559571 : Blo 936583 3559571 := bstep (se 1 (by rfl) ⟨2669678, by rfl⟩ : syracuseStep 3559571 = 5339357) B5339357
theorem B938267 : Blo 936583 938267 := bstep (se 1 (by rfl) ⟨703700, by rfl⟩ : syracuseStep 938267 = 1407401) B1407401
theorem B938303 : Blo 936583 938303 := bstep (se 1 (by rfl) ⟨703727, by rfl⟩ : syracuseStep 938303 = 1407455) B1407455
theorem B938703 : Blo 936583 938703 := bstep (se 1 (by rfl) ⟨704027, by rfl⟩ : syracuseStep 938703 = 1408055) B1408055
theorem B2380711 : Blo 936583 2380711 := bstep (se 1 (by rfl) ⟨1785533, by rfl⟩ : syracuseStep 2380711 = 3571067) B3571067
theorem B3167315 : Blo 936583 3167315 := bstep (se 1 (by rfl) ⟨2375486, by rfl⟩ : syracuseStep 3167315 = 4750973) B4750973
theorem B3167423 : Blo 936583 3167423 := bstep (se 1 (by rfl) ⟨2375567, by rfl⟩ : syracuseStep 3167423 = 4751135) B4751135
theorem B939647 : Blo 936583 939647 := bstep (se 1 (by rfl) ⟨704735, by rfl⟩ : syracuseStep 939647 = 1409471) B1409471
theorem B939751 : Blo 936583 939751 := bstep (se 1 (by rfl) ⟨704813, by rfl⟩ : syracuseStep 939751 = 1409627) B1409627
theorem B940351 : Blo 936583 940351 := bstep (se 1 (by rfl) ⟨705263, by rfl⟩ : syracuseStep 940351 = 1410527) B1410527
theorem B11426507 : Blo 936583 11426507 := bstep (se 1 (by rfl) ⟨8569880, by rfl⟩ : syracuseStep 11426507 = 17139761) B17139761
theorem B7133993 : Blo 936583 7133993 := bstep (se 2 (by rfl) ⟨2675247, by rfl⟩ : syracuseStep 7133993 = 5350495) B5350495
theorem B1335631 : Blo 936583 1335631 := bstep (se 1 (by rfl) ⟨1001723, by rfl⟩ : syracuseStep 1335631 = 2003447) B2003447
theorem B3563945 : Blo 936583 3563945 := bstep (se 2 (by rfl) ⟨1336479, by rfl⟩ : syracuseStep 3563945 = 2672959) B2672959
theorem B3007091 : Blo 936583 3007091 := bstep (se 1 (by rfl) ⟨2255318, by rfl⟩ : syracuseStep 3007091 = 4510637) B4510637
theorem B3171581 : Blo 936583 3171581 := bstep (se 3 (by rfl) ⟨594671, by rfl⟩ : syracuseStep 3171581 = 1189343) B1189343
theorem B4745465 : Blo 936583 4745465 := bstep (se 2 (by rfl) ⟨1779549, by rfl⟩ : syracuseStep 4745465 = 3559099) B3559099
theorem B3172985 : Blo 936583 3172985 := bstep (se 2 (by rfl) ⟨1189869, by rfl⟩ : syracuseStep 3172985 = 2379739) B2379739
theorem B6777695 : Blo 936583 6777695 := bstep (se 1 (by rfl) ⟨5083271, by rfl⟩ : syracuseStep 6777695 = 10166543) B10166543
theorem B3173309 : Blo 936583 3173309 := bstep (se 3 (by rfl) ⟨594995, by rfl⟩ : syracuseStep 3173309 = 1189991) B1189991
theorem B31255807 : Blo 936583 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B1503335 : Blo 936583 1503335 := bstep (se 1 (by rfl) ⟨1127501, by rfl⟩ : syracuseStep 1503335 = 2255003) B2255003
theorem B1405151 : Blo 936583 1405151 := bstep (se 1 (by rfl) ⟨1053863, by rfl⟩ : syracuseStep 1405151 = 2107727) B2107727
theorem B3567847 : Blo 936583 3567847 := bstep (se 1 (by rfl) ⟨2675885, by rfl⟩ : syracuseStep 3567847 = 5351771) B5351771
theorem B1405223 : Blo 936583 1405223 := bstep (se 1 (by rfl) ⟨1053917, by rfl⟩ : syracuseStep 1405223 = 2107835) B2107835
theorem B1405595 : Blo 936583 1405595 := bstep (se 1 (by rfl) ⟨1054196, by rfl⟩ : syracuseStep 1405595 = 2108393) B2108393
theorem B1405727 : Blo 936583 1405727 := bstep (se 1 (by rfl) ⟨1054295, by rfl⟩ : syracuseStep 1405727 = 2108591) B2108591
theorem B6026075 : Blo 936583 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B210924395 : Blo 936583 210924395 := bstep (se 1 (by rfl) ⟨158193296, by rfl⟩ : syracuseStep 210924395 = 316386593) B316386593
theorem B7140311 : Blo 936583 7140311 := bstep (se 1 (by rfl) ⟨5355233, by rfl⟩ : syracuseStep 7140311 = 10710467) B10710467
theorem B1405931 : Blo 936583 1405931 := bstep (se 1 (by rfl) ⟨1054448, by rfl⟩ : syracuseStep 1405931 = 2108897) B2108897
theorem B1406207 : Blo 936583 1406207 := bstep (se 1 (by rfl) ⟨1054655, by rfl⟩ : syracuseStep 1406207 = 2109311) B2109311
theorem B594376163 : Blo 936583 594376163 := bstep (se 1 (by rfl) ⟨445782122, by rfl⟩ : syracuseStep 594376163 = 891564245) B891564245
theorem B1406495 : Blo 936583 1406495 := bstep (se 1 (by rfl) ⟨1054871, by rfl⟩ : syracuseStep 1406495 = 2109743) B2109743
theorem B1406633 : Blo 936583 1406633 := bstep (se 2 (by rfl) ⟨527487, by rfl⟩ : syracuseStep 1406633 = 1054975) B1054975
theorem B1504975 : Blo 936583 1504975 := bstep (se 1 (by rfl) ⟨1128731, by rfl⟩ : syracuseStep 1504975 = 2257463) B2257463
theorem B27096929 : Blo 936583 27096929 := bstep (se 2 (by rfl) ⟨10161348, by rfl⟩ : syracuseStep 27096929 = 20322697) B20322697
theorem B1406879 : Blo 936583 1406879 := bstep (se 1 (by rfl) ⟨1055159, by rfl⟩ : syracuseStep 1406879 = 2110319) B2110319
theorem B3569791 : Blo 936583 3569791 := bstep (se 1 (by rfl) ⟨2677343, by rfl⟩ : syracuseStep 3569791 = 5354687) B5354687
theorem B1407263 : Blo 936583 1407263 := bstep (se 1 (by rfl) ⟨1055447, by rfl⟩ : syracuseStep 1407263 = 2110895) B2110895
theorem B1407335 : Blo 936583 1407335 := bstep (se 1 (by rfl) ⟨1055501, by rfl⟩ : syracuseStep 1407335 = 2111003) B2111003
theorem B5143337 : Blo 936583 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B7142255 : Blo 936583 7142255 := bstep (se 1 (by rfl) ⟨5356691, by rfl⟩ : syracuseStep 7142255 = 10713383) B10713383
theorem B1899455 : Blo 936583 1899455 := bstep (se 1 (by rfl) ⟨1424591, by rfl⟩ : syracuseStep 1899455 = 2849183) B2849183
theorem B10681307 : Blo 936583 10681307 := bstep (se 1 (by rfl) ⟨8010980, by rfl⟩ : syracuseStep 10681307 = 16021961) B16021961
theorem B1408169 : Blo 936583 1408169 := bstep (se 2 (by rfl) ⟨528063, by rfl⟩ : syracuseStep 1408169 = 1056127) B1056127
theorem B1408175 : Blo 936583 1408175 := bstep (se 1 (by rfl) ⟨1056131, by rfl⟩ : syracuseStep 1408175 = 2112263) B2112263
theorem B1408583 : Blo 936583 1408583 := bstep (se 1 (by rfl) ⟨1056437, by rfl⟩ : syracuseStep 1408583 = 2112875) B2112875
theorem B1408667 : Blo 936583 1408667 := bstep (se 1 (by rfl) ⟨1056500, by rfl⟩ : syracuseStep 1408667 = 2113001) B2113001
theorem B1408763 : Blo 936583 1408763 := bstep (se 1 (by rfl) ⟨1056572, by rfl⟩ : syracuseStep 1408763 = 2113145) B2113145
theorem B1409051 : Blo 936583 1409051 := bstep (se 1 (by rfl) ⟨1056788, by rfl⟩ : syracuseStep 1409051 = 2113577) B2113577
theorem B1409351 : Blo 936583 1409351 := bstep (se 1 (by rfl) ⟨1057013, by rfl⟩ : syracuseStep 1409351 = 2114027) B2114027
theorem B5341565 : Blo 936583 5341565 := bstep (se 3 (by rfl) ⟨1001543, by rfl⟩ : syracuseStep 5341565 = 2003087) B2003087
theorem B4751783 : Blo 936583 4751783 := bstep (se 1 (by rfl) ⟨3563837, by rfl⟩ : syracuseStep 4751783 = 7127675) B7127675
theorem B1409951 : Blo 936583 1409951 := bstep (se 1 (by rfl) ⟨1057463, by rfl⟩ : syracuseStep 1409951 = 2114927) B2114927
theorem B1410185 : Blo 936583 1410185 := bstep (se 2 (by rfl) ⟨528819, by rfl⟩ : syracuseStep 1410185 = 1057639) B1057639
theorem B1410203 : Blo 936583 1410203 := bstep (se 1 (by rfl) ⟨1057652, by rfl⟩ : syracuseStep 1410203 = 2115305) B2115305
theorem B1901887 : Blo 936583 1901887 := bstep (se 1 (by rfl) ⟨1426415, by rfl⟩ : syracuseStep 1901887 = 2852831) B2852831
theorem B4753079 : Blo 936583 4753079 := bstep (se 1 (by rfl) ⟨3564809, by rfl⟩ : syracuseStep 4753079 = 7129619) B7129619
theorem B4753727 : Blo 936583 4753727 := bstep (se 1 (by rfl) ⟨3565295, by rfl⟩ : syracuseStep 4753727 = 7130591) B7130591
theorem B4002331 : Blo 936583 4002331 := bstep (se 1 (by rfl) ⟨3001748, by rfl⟩ : syracuseStep 4002331 = 6003497) B6003497
theorem B4755995 : Blo 936583 4755995 := bstep (se 1 (by rfl) ⟨3566996, by rfl⟩ : syracuseStep 4755995 = 7133993) B7133993
theorem B3806239 : Blo 936583 3806239 := bstep (se 1 (by rfl) ⟨2854679, by rfl⟩ : syracuseStep 3806239 = 5709359) B5709359
theorem B4757129 : Blo 936583 4757129 := bstep (se 2 (by rfl) ⟨1783923, by rfl⟩ : syracuseStep 4757129 = 3567847) B3567847
theorem B2006633 : Blo 936583 2006633 := bstep (se 2 (by rfl) ⟨752487, by rfl⟩ : syracuseStep 2006633 = 1504975) B1504975
theorem B1056415 : Blo 936583 1056415 := bstep (se 1 (by rfl) ⟨792311, by rfl⟩ : syracuseStep 1056415 = 1584623) B1584623
theorem B1056703 : Blo 936583 1056703 := bstep (se 1 (by rfl) ⟨792527, by rfl⟩ : syracuseStep 1056703 = 1585055) B1585055
theorem B4759721 : Blo 936583 4759721 := bstep (se 2 (by rfl) ⟨1784895, by rfl⟩ : syracuseStep 4759721 = 3569791) B3569791
theorem B36544873 : Blo 936583 36544873 := bstep (se 2 (by rfl) ⟨13704327, by rfl⟩ : syracuseStep 36544873 = 27408655) B27408655
theorem B140616263 : Blo 936583 140616263 := bstep (se 1 (by rfl) ⟨105462197, by rfl⟩ : syracuseStep 140616263 = 210924395) B210924395
theorem B4760207 : Blo 936583 4760207 := bstep (se 1 (by rfl) ⟨3570155, by rfl⟩ : syracuseStep 4760207 = 7140311) B7140311
theorem B1581727 : Blo 936583 1581727 := bstep (se 1 (by rfl) ⟨1186295, by rfl⟩ : syracuseStep 1581727 = 2372591) B2372591
theorem B18064619 : Blo 936583 18064619 := bstep (se 1 (by rfl) ⟨13548464, by rfl⟩ : syracuseStep 18064619 = 27096929) B27096929
theorem B7218895 : Blo 936583 7218895 := bstep (se 1 (by rfl) ⟨5414171, by rfl⟩ : syracuseStep 7218895 = 10828343) B10828343
theorem B8005513 : Blo 936583 8005513 := bstep (se 2 (by rfl) ⟨3002067, by rfl⟩ : syracuseStep 8005513 = 6004135) B6004135
theorem B4761503 : Blo 936583 4761503 := bstep (se 1 (by rfl) ⟨3571127, by rfl⟩ : syracuseStep 4761503 = 7142255) B7142255
theorem B2107367 : Blo 936583 2107367 := bstep (se 1 (by rfl) ⟨1580525, by rfl⟩ : syracuseStep 2107367 = 3161051) B3161051
theorem B7120871 : Blo 936583 7120871 := bstep (se 1 (by rfl) ⟨5340653, by rfl⟩ : syracuseStep 7120871 = 10681307) B10681307
theorem B8005787 : Blo 936583 8005787 := bstep (se 1 (by rfl) ⟨6004340, by rfl⟩ : syracuseStep 8005787 = 12008681) B12008681
theorem B38546057 : Blo 936583 38546057 := bstep (se 2 (by rfl) ⟨14454771, by rfl⟩ : syracuseStep 38546057 = 28909543) B28909543
theorem B1780841 : Blo 936583 1780841 := bstep (se 2 (by rfl) ⟨667815, by rfl⟩ : syracuseStep 1780841 = 1335631) B1335631
theorem B2108735 : Blo 936583 2108735 := bstep (se 1 (by rfl) ⟨1581551, by rfl⟩ : syracuseStep 2108735 = 3163103) B3163103
theorem B2108843 : Blo 936583 2108843 := bstep (se 1 (by rfl) ⟨1581632, by rfl⟩ : syracuseStep 2108843 = 3163265) B3163265
theorem B30387635 : Blo 936583 30387635 := bstep (se 1 (by rfl) ⟨22790726, by rfl⟩ : syracuseStep 30387635 = 45581453) B45581453
theorem B2371295 : Blo 936583 2371295 := bstep (se 1 (by rfl) ⟨1778471, by rfl⟩ : syracuseStep 2371295 = 3556943) B3556943
theorem B2109383 : Blo 936583 2109383 := bstep (se 1 (by rfl) ⟨1582037, by rfl⟩ : syracuseStep 2109383 = 3164075) B3164075
theorem B15216599 : Blo 936583 15216599 := bstep (se 1 (by rfl) ⟨11412449, by rfl⟩ : syracuseStep 15216599 = 22824899) B22824899
theorem B8138917 : Blo 936583 8138917 := bstep (se 4 (by rfl) ⟨763023, by rfl⟩ : syracuseStep 8138917 = 1526047) B1526047
theorem B2109959 : Blo 936583 2109959 := bstep (se 1 (by rfl) ⟨1582469, by rfl⟩ : syracuseStep 2109959 = 3164939) B3164939
theorem B2110265 : Blo 936583 2110265 := bstep (se 2 (by rfl) ⟨791349, by rfl⟩ : syracuseStep 2110265 = 1582699) B1582699
theorem B2373047 : Blo 936583 2373047 := bstep (se 1 (by rfl) ⟨1779785, by rfl⟩ : syracuseStep 2373047 = 3559571) B3559571
theorem B1586857 : Blo 936583 1586857 := bstep (se 2 (by rfl) ⟨595071, by rfl⟩ : syracuseStep 1586857 = 1190143) B1190143
theorem B2111543 : Blo 936583 2111543 := bstep (se 1 (by rfl) ⟨1583657, by rfl⟩ : syracuseStep 2111543 = 3167315) B3167315
theorem B2111561 : Blo 936583 2111561 := bstep (se 2 (by rfl) ⟨791835, by rfl⟩ : syracuseStep 2111561 = 1583671) B1583671
theorem B2111615 : Blo 936583 2111615 := bstep (se 1 (by rfl) ⟨1583711, by rfl⟩ : syracuseStep 2111615 = 3167423) B3167423
theorem B7617671 : Blo 936583 7617671 := bstep (se 1 (by rfl) ⟨5713253, by rfl⟩ : syracuseStep 7617671 = 11426507) B11426507
theorem B11582797 : Blo 936583 11582797 := bstep (se 3 (by rfl) ⟨2171774, by rfl⟩ : syracuseStep 11582797 = 4343549) B4343549
theorem B2375963 : Blo 936583 2375963 := bstep (se 1 (by rfl) ⟨1781972, by rfl⟩ : syracuseStep 2375963 = 3563945) B3563945
theorem B2375993 : Blo 936583 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B3162941 : Blo 936583 3162941 := bstep (se 3 (by rfl) ⟨593051, by rfl⟩ : syracuseStep 3162941 = 1186103) B1186103
theorem B2114387 : Blo 936583 2114387 := bstep (se 1 (by rfl) ⟨1585790, by rfl⟩ : syracuseStep 2114387 = 3171581) B3171581
theorem B3163643 : Blo 936583 3163643 := bstep (se 1 (by rfl) ⟨2372732, by rfl⟩ : syracuseStep 3163643 = 4745465) B4745465
theorem B6014695 : Blo 936583 6014695 := bstep (se 1 (by rfl) ⟨4511021, by rfl⟩ : syracuseStep 6014695 = 9022043) B9022043
theorem B2115323 : Blo 936583 2115323 := bstep (se 1 (by rfl) ⟨1586492, by rfl⟩ : syracuseStep 2115323 = 3172985) B3172985
theorem B3163913 : Blo 936583 3163913 := bstep (se 2 (by rfl) ⟨1186467, by rfl⟩ : syracuseStep 3163913 = 2372935) B2372935
theorem B2115539 : Blo 936583 2115539 := bstep (se 1 (by rfl) ⟨1586654, by rfl⟩ : syracuseStep 2115539 = 3173309) B3173309
theorem B3164129 : Blo 936583 3164129 := bstep (se 2 (by rfl) ⟨1186548, by rfl⟩ : syracuseStep 3164129 = 2373097) B2373097
theorem B5065213 : Blo 936583 5065213 := bstep (se 3 (by rfl) ⟨949727, by rfl⟩ : syracuseStep 5065213 = 1899455) B1899455
theorem B3164669 : Blo 936583 3164669 := bstep (se 3 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 3164669 = 1186751) B1186751
theorem B1002223 : Blo 936583 1002223 := bstep (se 1 (by rfl) ⟨751667, by rfl⟩ : syracuseStep 1002223 = 1503335) B1503335
theorem B936767 : Blo 936583 936767 := bstep (se 1 (by rfl) ⟨702575, by rfl⟩ : syracuseStep 936767 = 1405151) B1405151
theorem B936815 : Blo 936583 936815 := bstep (se 1 (by rfl) ⟨702611, by rfl⟩ : syracuseStep 936815 = 1405223) B1405223
theorem B937063 : Blo 936583 937063 := bstep (se 1 (by rfl) ⟨702797, by rfl⟩ : syracuseStep 937063 = 1405595) B1405595
theorem B937151 : Blo 936583 937151 := bstep (se 1 (by rfl) ⟨702863, by rfl⟩ : syracuseStep 937151 = 1405727) B1405727
theorem B4017383 : Blo 936583 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B937287 : Blo 936583 937287 := bstep (se 1 (by rfl) ⟨702965, by rfl⟩ : syracuseStep 937287 = 1405931) B1405931
theorem B7228865 : Blo 936583 7228865 := bstep (se 2 (by rfl) ⟨2710824, by rfl⟩ : syracuseStep 7228865 = 5421649) B5421649
theorem B937471 : Blo 936583 937471 := bstep (se 1 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 937471 = 1406207) B1406207
theorem B396250775 : Blo 936583 396250775 := bstep (se 1 (by rfl) ⟨297188081, by rfl⟩ : syracuseStep 396250775 = 594376163) B594376163
theorem B937663 : Blo 936583 937663 := bstep (se 1 (by rfl) ⟨703247, by rfl⟩ : syracuseStep 937663 = 1406495) B1406495
theorem B4509407 : Blo 936583 4509407 := bstep (se 1 (by rfl) ⟨3382055, by rfl⟩ : syracuseStep 4509407 = 6764111) B6764111
theorem B937755 : Blo 936583 937755 := bstep (se 1 (by rfl) ⟨703316, by rfl⟩ : syracuseStep 937755 = 1406633) B1406633
theorem B6868799 : Blo 936583 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B937919 : Blo 936583 937919 := bstep (se 1 (by rfl) ⟨703439, by rfl⟩ : syracuseStep 937919 = 1406879) B1406879
theorem B938175 : Blo 936583 938175 := bstep (se 1 (by rfl) ⟨703631, by rfl⟩ : syracuseStep 938175 = 1407263) B1407263
theorem B938223 : Blo 936583 938223 := bstep (se 1 (by rfl) ⟨703667, by rfl⟩ : syracuseStep 938223 = 1407335) B1407335
theorem B3428891 : Blo 936583 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B938779 : Blo 936583 938779 := bstep (se 1 (by rfl) ⟨704084, by rfl⟩ : syracuseStep 938779 = 1408169) B1408169
theorem B938783 : Blo 936583 938783 := bstep (se 1 (by rfl) ⟨704087, by rfl⟩ : syracuseStep 938783 = 1408175) B1408175
theorem B939055 : Blo 936583 939055 := bstep (se 1 (by rfl) ⟨704291, by rfl⟩ : syracuseStep 939055 = 1408583) B1408583
theorem B939111 : Blo 936583 939111 := bstep (se 1 (by rfl) ⟨704333, by rfl⟩ : syracuseStep 939111 = 1408667) B1408667
theorem B939175 : Blo 936583 939175 := bstep (se 1 (by rfl) ⟨704381, by rfl⟩ : syracuseStep 939175 = 1408763) B1408763
theorem B939471 : Blo 936583 939471 := bstep (se 1 (by rfl) ⟨704603, by rfl⟩ : syracuseStep 939471 = 1409207) B1409207
theorem B10835723 : Blo 936583 10835723 := bstep (se 1 (by rfl) ⟨8126792, by rfl⟩ : syracuseStep 10835723 = 16253585) B16253585
theorem B939943 : Blo 936583 939943 := bstep (se 1 (by rfl) ⟨704957, by rfl⟩ : syracuseStep 939943 = 1409915) B1409915
theorem B940027 : Blo 936583 940027 := bstep (se 1 (by rfl) ⟨705020, by rfl⟩ : syracuseStep 940027 = 1410041) B1410041
theorem B940063 : Blo 936583 940063 := bstep (se 1 (by rfl) ⟨705047, by rfl⟩ : syracuseStep 940063 = 1410095) B1410095
theorem B940271 : Blo 936583 940271 := bstep (se 1 (by rfl) ⟨705203, by rfl⟩ : syracuseStep 940271 = 1410407) B1410407
theorem B8018909 : Blo 936583 8018909 := bstep (se 3 (by rfl) ⟨1503545, by rfl⟩ : syracuseStep 8018909 = 3007091) B3007091
theorem B18275615 : Blo 936583 18275615 := bstep (se 1 (by rfl) ⟨13706711, by rfl⟩ : syracuseStep 18275615 = 27413423) B27413423
theorem B3170015 : Blo 936583 3170015 := bstep (se 1 (by rfl) ⟨2377511, by rfl⟩ : syracuseStep 3170015 = 4755023) B4755023
theorem B6774839 : Blo 936583 6774839 := bstep (se 1 (by rfl) ⟨5081129, by rfl⟩ : syracuseStep 6774839 = 10162259) B10162259
theorem B3171743 : Blo 936583 3171743 := bstep (se 1 (by rfl) ⟨2378807, by rfl⟩ : syracuseStep 3171743 = 4757615) B4757615
theorem B2254319 : Blo 936583 2254319 := bstep (se 1 (by rfl) ⟨1690739, by rfl⟩ : syracuseStep 2254319 = 3381479) B3381479
theorem B41674409 : Blo 936583 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B3172607 : Blo 936583 3172607 := bstep (se 1 (by rfl) ⟨2379455, by rfl⟩ : syracuseStep 3172607 = 4758911) B4758911
theorem B24013259 : Blo 936583 24013259 := bstep (se 1 (by rfl) ⟨18009944, by rfl⟩ : syracuseStep 24013259 = 36019889) B36019889
theorem B8023283 : Blo 936583 8023283 := bstep (se 1 (by rfl) ⟨6017462, by rfl⟩ : syracuseStep 8023283 = 12034925) B12034925
theorem B3174281 : Blo 936583 3174281 := bstep (se 2 (by rfl) ⟨1190355, by rfl⟩ : syracuseStep 3174281 = 2380711) B2380711
theorem B1405031 : Blo 936583 1405031 := bstep (se 1 (by rfl) ⟨1053773, by rfl⟩ : syracuseStep 1405031 = 2107547) B2107547
theorem B1405049 : Blo 936583 1405049 := bstep (se 2 (by rfl) ⟨526893, by rfl⟩ : syracuseStep 1405049 = 1053787) B1053787
theorem B1405097 : Blo 936583 1405097 := bstep (se 2 (by rfl) ⟨526911, by rfl⟩ : syracuseStep 1405097 = 1053823) B1053823
theorem B18018557 : Blo 936583 18018557 := bstep (se 3 (by rfl) ⟨3378479, by rfl⟩ : syracuseStep 18018557 = 6756959) B6756959
theorem B5337647 : Blo 936583 5337647 := bstep (se 1 (by rfl) ⟨4003235, by rfl⟩ : syracuseStep 5337647 = 8006471) B8006471
theorem B4518463 : Blo 936583 4518463 := bstep (se 1 (by rfl) ⟨3388847, by rfl⟩ : syracuseStep 4518463 = 6777695) B6777695
theorem B1405607 : Blo 936583 1405607 := bstep (se 1 (by rfl) ⟨1054205, by rfl⟩ : syracuseStep 1405607 = 2108411) B2108411
theorem B1405673 : Blo 936583 1405673 := bstep (se 2 (by rfl) ⟨527127, by rfl⟩ : syracuseStep 1405673 = 1054255) B1054255
theorem B1406459 : Blo 936583 1406459 := bstep (se 1 (by rfl) ⟨1054844, by rfl⟩ : syracuseStep 1406459 = 2109689) B2109689
theorem B18053927 : Blo 936583 18053927 := bstep (se 1 (by rfl) ⟨13540445, by rfl⟩ : syracuseStep 18053927 = 27080891) B27080891
theorem B1408235 : Blo 936583 1408235 := bstep (se 1 (by rfl) ⟨1056176, by rfl⟩ : syracuseStep 1408235 = 2112353) B2112353
theorem B1408283 : Blo 936583 1408283 := bstep (se 1 (by rfl) ⟨1056212, by rfl⟩ : syracuseStep 1408283 = 2112425) B2112425
theorem B1409003 : Blo 936583 1409003 := bstep (se 1 (by rfl) ⟨1056752, by rfl⟩ : syracuseStep 1409003 = 2113505) B2113505
theorem B48726497 : Blo 936583 48726497 := bstep (se 2 (by rfl) ⟨18272436, by rfl⟩ : syracuseStep 48726497 = 36544873) B36544873
theorem B1409591 : Blo 936583 1409591 := bstep (se 1 (by rfl) ⟨1057193, by rfl⟩ : syracuseStep 1409591 = 2114387) B2114387
theorem B1410215 : Blo 936583 1410215 := bstep (se 1 (by rfl) ⟨1057661, by rfl⟩ : syracuseStep 1410215 = 2115323) B2115323
theorem B1410359 : Blo 936583 1410359 := bstep (se 1 (by rfl) ⟨1057769, by rfl⟩ : syracuseStep 1410359 = 2115539) B2115539
theorem B4819243 : Blo 936583 4819243 := bstep (se 1 (by rfl) ⟨3614432, by rfl⟩ : syracuseStep 4819243 = 7228865) B7228865
theorem B6753617 : Blo 936583 6753617 := bstep (se 2 (by rfl) ⟨2532606, by rfl⟩ : syracuseStep 6753617 = 5065213) B5065213
theorem B5345189 : Blo 936583 5345189 := bstep (se 4 (by rfl) ⟨501111, by rfl⟩ : syracuseStep 5345189 = 1002223) B1002223
theorem B5345939 : Blo 936583 5345939 := bstep (se 1 (by rfl) ⟨4009454, by rfl⟩ : syracuseStep 5345939 = 8018909) B8018909
theorem B10851889 : Blo 936583 10851889 := bstep (se 2 (by rfl) ⟨4069458, by rfl⟩ : syracuseStep 10851889 = 8138917) B8138917
theorem B25697371 : Blo 936583 25697371 := bstep (se 1 (by rfl) ⟨19273028, by rfl⟩ : syracuseStep 25697371 = 38546057) B38546057
theorem B1187227 : Blo 936583 1187227 := bstep (se 1 (by rfl) ⟨890420, by rfl⟩ : syracuseStep 1187227 = 1780841) B1780841
theorem B5348855 : Blo 936583 5348855 := bstep (se 1 (by rfl) ⟨4011641, by rfl⟩ : syracuseStep 5348855 = 8023283) B8023283
theorem B20258423 : Blo 936583 20258423 := bstep (se 1 (by rfl) ⟨15193817, by rfl⟩ : syracuseStep 20258423 = 30387635) B30387635
theorem B1580863 : Blo 936583 1580863 := bstep (se 1 (by rfl) ⟨1185647, by rfl⟩ : syracuseStep 1580863 = 2371295) B2371295
theorem B1582031 : Blo 936583 1582031 := bstep (se 1 (by rfl) ⟨1186523, by rfl⟩ : syracuseStep 1582031 = 2373047) B2373047
theorem B5351021 : Blo 936583 5351021 := bstep (se 3 (by rfl) ⟨1003316, by rfl⟩ : syracuseStep 5351021 = 2006633) B2006633
theorem B15443729 : Blo 936583 15443729 := bstep (se 2 (by rfl) ⟨5791398, by rfl⟩ : syracuseStep 15443729 = 11582797) B11582797
theorem B12035951 : Blo 936583 12035951 := bstep (se 1 (by rfl) ⟨9026963, by rfl⟩ : syracuseStep 12035951 = 18053927) B18053927
theorem B1583975 : Blo 936583 1583975 := bstep (se 1 (by rfl) ⟨1187981, by rfl⟩ : syracuseStep 1583975 = 2375963) B2375963
theorem B1583995 : Blo 936583 1583995 := bstep (se 1 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 1583995 = 2375993) B2375993
theorem B2108627 : Blo 936583 2108627 := bstep (se 1 (by rfl) ⟨1581470, by rfl⟩ : syracuseStep 2108627 = 3162941) B3162941
theorem B2108969 : Blo 936583 2108969 := bstep (se 2 (by rfl) ⟨790863, by rfl⟩ : syracuseStep 2108969 = 1581727) B1581727
theorem B2109095 : Blo 936583 2109095 := bstep (se 1 (by rfl) ⟨1581821, by rfl⟩ : syracuseStep 2109095 = 3163643) B3163643
theorem B2109275 : Blo 936583 2109275 := bstep (se 1 (by rfl) ⟨1581956, by rfl⟩ : syracuseStep 2109275 = 3163913) B3163913
theorem B2109419 : Blo 936583 2109419 := bstep (se 1 (by rfl) ⟨1582064, by rfl⟩ : syracuseStep 2109419 = 3164129) B3164129
theorem B374976701 : Blo 936583 374976701 := bstep (se 3 (by rfl) ⟨70308131, by rfl⟩ : syracuseStep 374976701 = 140616263) B140616263
theorem B2109779 : Blo 936583 2109779 := bstep (se 1 (by rfl) ⟨1582334, by rfl⟩ : syracuseStep 2109779 = 3164669) B3164669
theorem B7223815 : Blo 936583 7223815 := bstep (se 1 (by rfl) ⟨5417861, by rfl⟩ : syracuseStep 7223815 = 10835723) B10835723
theorem B2113343 : Blo 936583 2113343 := bstep (se 1 (by rfl) ⟨1585007, by rfl⟩ : syracuseStep 2113343 = 3170015) B3170015
theorem B12043079 : Blo 936583 12043079 := bstep (se 1 (by rfl) ⟨9032309, by rfl⟩ : syracuseStep 12043079 = 18064619) B18064619
theorem B2114495 : Blo 936583 2114495 := bstep (se 1 (by rfl) ⟨1585871, by rfl⟩ : syracuseStep 2114495 = 3171743) B3171743
theorem B2115071 : Blo 936583 2115071 := bstep (se 1 (by rfl) ⟨1586303, by rfl⟩ : syracuseStep 2115071 = 3172607) B3172607
theorem B16008839 : Blo 936583 16008839 := bstep (se 1 (by rfl) ⟨12006629, by rfl⟩ : syracuseStep 16008839 = 24013259) B24013259
theorem B10143397 : Blo 936583 10143397 := bstep (se 4 (by rfl) ⟨950943, by rfl⟩ : syracuseStep 10143397 = 1901887) B1901887
theorem B2115809 : Blo 936583 2115809 := bstep (se 2 (by rfl) ⟨793428, by rfl⟩ : syracuseStep 2115809 = 1586857) B1586857
theorem B2116187 : Blo 936583 2116187 := bstep (se 1 (by rfl) ⟨1587140, by rfl⟩ : syracuseStep 2116187 = 3174281) B3174281
theorem B10144399 : Blo 936583 10144399 := bstep (se 1 (by rfl) ⟨7608299, by rfl⟩ : syracuseStep 10144399 = 15216599) B15216599
theorem B936687 : Blo 936583 936687 := bstep (se 1 (by rfl) ⟨702515, by rfl⟩ : syracuseStep 936687 = 1405031) B1405031
theorem B936699 : Blo 936583 936699 := bstep (se 1 (by rfl) ⟨702524, by rfl⟩ : syracuseStep 936699 = 1405049) B1405049
theorem B936731 : Blo 936583 936731 := bstep (se 1 (by rfl) ⟨702548, by rfl⟩ : syracuseStep 936731 = 1405097) B1405097
theorem B12012371 : Blo 936583 12012371 := bstep (se 1 (by rfl) ⟨9009278, by rfl⟩ : syracuseStep 12012371 = 18018557) B18018557
theorem B3558431 : Blo 936583 3558431 := bstep (se 1 (by rfl) ⟨2668823, by rfl⟩ : syracuseStep 3558431 = 5337647) B5337647
theorem B937071 : Blo 936583 937071 := bstep (se 1 (by rfl) ⟨702803, by rfl⟩ : syracuseStep 937071 = 1405607) B1405607
theorem B937115 : Blo 936583 937115 := bstep (se 1 (by rfl) ⟨702836, by rfl⟩ : syracuseStep 937115 = 1405673) B1405673
theorem B937639 : Blo 936583 937639 := bstep (se 1 (by rfl) ⟨703229, by rfl⟩ : syracuseStep 937639 = 1406459) B1406459
theorem B938823 : Blo 936583 938823 := bstep (se 1 (by rfl) ⟨704117, by rfl⟩ : syracuseStep 938823 = 1408235) B1408235
theorem B938855 : Blo 936583 938855 := bstep (se 1 (by rfl) ⟨704141, by rfl⟩ : syracuseStep 938855 = 1408283) B1408283
theorem B939335 : Blo 936583 939335 := bstep (se 1 (by rfl) ⟨704501, by rfl⟩ : syracuseStep 939335 = 1409003) B1409003
theorem B939367 : Blo 936583 939367 := bstep (se 1 (by rfl) ⟨704525, by rfl⟩ : syracuseStep 939367 = 1409051) B1409051
theorem B939567 : Blo 936583 939567 := bstep (se 1 (by rfl) ⟨704675, by rfl⟩ : syracuseStep 939567 = 1409351) B1409351
theorem B3561043 : Blo 936583 3561043 := bstep (se 1 (by rfl) ⟨2670782, by rfl⟩ : syracuseStep 3561043 = 5341565) B5341565
theorem B3167855 : Blo 936583 3167855 := bstep (se 1 (by rfl) ⟨2375891, by rfl⟩ : syracuseStep 3167855 = 4751783) B4751783
theorem B939967 : Blo 936583 939967 := bstep (se 1 (by rfl) ⟨704975, by rfl⟩ : syracuseStep 939967 = 1409951) B1409951
theorem B940123 : Blo 936583 940123 := bstep (se 1 (by rfl) ⟨705092, by rfl⟩ : syracuseStep 940123 = 1410185) B1410185
theorem B940135 : Blo 936583 940135 := bstep (se 1 (by rfl) ⟨705101, by rfl⟩ : syracuseStep 940135 = 1410203) B1410203
theorem B3168719 : Blo 936583 3168719 := bstep (se 1 (by rfl) ⟨2376539, by rfl⟩ : syracuseStep 3168719 = 4753079) B4753079
theorem B3169151 : Blo 936583 3169151 := bstep (se 1 (by rfl) ⟨2376863, by rfl⟩ : syracuseStep 3169151 = 4753727) B4753727
theorem B2678255 : Blo 936583 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B9625193 : Blo 936583 9625193 := bstep (se 2 (by rfl) ⟨3609447, by rfl⟩ : syracuseStep 9625193 = 7218895) B7218895
theorem B8019593 : Blo 936583 8019593 := bstep (se 2 (by rfl) ⟨3007347, by rfl⟩ : syracuseStep 8019593 = 6014695) B6014695
theorem B264167183 : Blo 936583 264167183 := bstep (se 1 (by rfl) ⟨198125387, by rfl⟩ : syracuseStep 264167183 = 396250775) B396250775
theorem B3006271 : Blo 936583 3006271 := bstep (se 1 (by rfl) ⟨2254703, by rfl⟩ : syracuseStep 3006271 = 4509407) B4509407
theorem B10674017 : Blo 936583 10674017 := bstep (se 2 (by rfl) ⟨4002756, by rfl⟩ : syracuseStep 10674017 = 8005513) B8005513
theorem B4579199 : Blo 936583 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B2285927 : Blo 936583 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B3170663 : Blo 936583 3170663 := bstep (se 1 (by rfl) ⟨2377997, by rfl⟩ : syracuseStep 3170663 = 4755995) B4755995
theorem B3171419 : Blo 936583 3171419 := bstep (se 1 (by rfl) ⟨2378564, by rfl⟩ : syracuseStep 3171419 = 4757129) B4757129
theorem B12183743 : Blo 936583 12183743 := bstep (se 1 (by rfl) ⟨9137807, by rfl⟩ : syracuseStep 12183743 = 18275615) B18275615
theorem B4516559 : Blo 936583 4516559 := bstep (se 1 (by rfl) ⟨3387419, by rfl⟩ : syracuseStep 4516559 = 6774839) B6774839
theorem B3173147 : Blo 936583 3173147 := bstep (se 1 (by rfl) ⟨2379860, by rfl⟩ : syracuseStep 3173147 = 4759721) B4759721
theorem B3173471 : Blo 936583 3173471 := bstep (se 1 (by rfl) ⟨2380103, by rfl⟩ : syracuseStep 3173471 = 4760207) B4760207
theorem B5336441 : Blo 936583 5336441 := bstep (se 2 (by rfl) ⟨2001165, by rfl⟩ : syracuseStep 5336441 = 4002331) B4002331
theorem B6024617 : Blo 936583 6024617 := bstep (se 2 (by rfl) ⟨2259231, by rfl⟩ : syracuseStep 6024617 = 4518463) B4518463
theorem B1502879 : Blo 936583 1502879 := bstep (se 1 (by rfl) ⟨1127159, by rfl⟩ : syracuseStep 1502879 = 2254319) B2254319
theorem B27782939 : Blo 936583 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B3174335 : Blo 936583 3174335 := bstep (se 1 (by rfl) ⟨2380751, by rfl⟩ : syracuseStep 3174335 = 4761503) B4761503
theorem B1404911 : Blo 936583 1404911 := bstep (se 1 (by rfl) ⟨1053683, by rfl⟩ : syracuseStep 1404911 = 2107367) B2107367
theorem B4747247 : Blo 936583 4747247 := bstep (se 1 (by rfl) ⟨3560435, by rfl⟩ : syracuseStep 4747247 = 7120871) B7120871
theorem B5074985 : Blo 936583 5074985 := bstep (se 2 (by rfl) ⟨1903119, by rfl⟩ : syracuseStep 5074985 = 3806239) B3806239
theorem B5337191 : Blo 936583 5337191 := bstep (se 1 (by rfl) ⟨4002893, by rfl⟩ : syracuseStep 5337191 = 8005787) B8005787
theorem B1405823 : Blo 936583 1405823 := bstep (se 1 (by rfl) ⟨1054367, by rfl⟩ : syracuseStep 1405823 = 2108735) B2108735
theorem B1405895 : Blo 936583 1405895 := bstep (se 1 (by rfl) ⟨1054421, by rfl⟩ : syracuseStep 1405895 = 2108843) B2108843
theorem B1406255 : Blo 936583 1406255 := bstep (se 1 (by rfl) ⟨1054691, by rfl⟩ : syracuseStep 1406255 = 2109383) B2109383
theorem B1406639 : Blo 936583 1406639 := bstep (se 1 (by rfl) ⟨1054979, by rfl⟩ : syracuseStep 1406639 = 2109959) B2109959
theorem B1406843 : Blo 936583 1406843 := bstep (se 1 (by rfl) ⟨1055132, by rfl⟩ : syracuseStep 1406843 = 2110265) B2110265
theorem B1407695 : Blo 936583 1407695 := bstep (se 1 (by rfl) ⟨1055771, by rfl⟩ : syracuseStep 1407695 = 2111543) B2111543
theorem B1407707 : Blo 936583 1407707 := bstep (se 1 (by rfl) ⟨1055780, by rfl⟩ : syracuseStep 1407707 = 2111561) B2111561
theorem B1407743 : Blo 936583 1407743 := bstep (se 1 (by rfl) ⟨1055807, by rfl⟩ : syracuseStep 1407743 = 2111615) B2111615
theorem B5078447 : Blo 936583 5078447 := bstep (se 1 (by rfl) ⟨3808835, by rfl⟩ : syracuseStep 5078447 = 7617671) B7617671
theorem B1408553 : Blo 936583 1408553 := bstep (se 2 (by rfl) ⟨528207, by rfl⟩ : syracuseStep 1408553 = 1056415) B1056415
theorem B1408937 : Blo 936583 1408937 := bstep (se 2 (by rfl) ⟨528351, by rfl⟩ : syracuseStep 1408937 = 1056703) B1056703
theorem B13533293 : Blo 936583 13533293 := bstep (se 3 (by rfl) ⟨2537492, by rfl⟩ : syracuseStep 13533293 = 5074985) B5074985
theorem B8028719 : Blo 936583 8028719 := bstep (se 1 (by rfl) ⟨6021539, by rfl⟩ : syracuseStep 8028719 = 12043079) B12043079
theorem B1409663 : Blo 936583 1409663 := bstep (se 1 (by rfl) ⟨1057247, by rfl⟩ : syracuseStep 1409663 = 2114495) B2114495
theorem B1410047 : Blo 936583 1410047 := bstep (se 1 (by rfl) ⟨1057535, by rfl⟩ : syracuseStep 1410047 = 2115071) B2115071
theorem B1410539 : Blo 936583 1410539 := bstep (se 1 (by rfl) ⟨1057904, by rfl⟩ : syracuseStep 1410539 = 2115809) B2115809
theorem B1410791 : Blo 936583 1410791 := bstep (se 1 (by rfl) ⟨1058093, by rfl⟩ : syracuseStep 1410791 = 2116187) B2116187
theorem B6425657 : Blo 936583 6425657 := bstep (se 2 (by rfl) ⟨2409621, by rfl⟩ : syracuseStep 6425657 = 4819243) B4819243
theorem B13505615 : Blo 936583 13505615 := bstep (se 1 (by rfl) ⟨10129211, by rfl⟩ : syracuseStep 13505615 = 20258423) B20258423
theorem B5346395 : Blo 936583 5346395 := bstep (se 1 (by rfl) ⟨4009796, by rfl⟩ : syracuseStep 5346395 = 8019593) B8019593
theorem B7116011 : Blo 936583 7116011 := bstep (se 1 (by rfl) ⟨5337008, by rfl⟩ : syracuseStep 7116011 = 10674017) B10674017
theorem B3052799 : Blo 936583 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B1054687 : Blo 936583 1054687 := bstep (se 1 (by rfl) ⟨791015, by rfl⟩ : syracuseStep 1054687 = 1582031) B1582031
theorem B10295819 : Blo 936583 10295819 := bstep (se 1 (by rfl) ⟨7721864, by rfl⟩ : syracuseStep 10295819 = 15443729) B15443729
theorem B16030709 : Blo 936583 16030709 := bstep (se 5 (by rfl) ⟨751439, by rfl⟩ : syracuseStep 16030709 = 1502879) B1502879
theorem B1055983 : Blo 936583 1055983 := bstep (se 1 (by rfl) ⟨791987, by rfl⟩ : syracuseStep 1055983 = 1583975) B1583975
theorem B18521959 : Blo 936583 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B1582969 : Blo 936583 1582969 := bstep (se 2 (by rfl) ⟨593613, by rfl⟩ : syracuseStep 1582969 = 1187227) B1187227
theorem B3385631 : Blo 936583 3385631 := bstep (se 1 (by rfl) ⟨2539223, by rfl⟩ : syracuseStep 3385631 = 5078447) B5078447
theorem B2107817 : Blo 936583 2107817 := bstep (se 2 (by rfl) ⟨790431, by rfl⟩ : syracuseStep 2107817 = 1580863) B1580863
theorem B4008361 : Blo 936583 4008361 := bstep (se 2 (by rfl) ⟨1503135, by rfl⟩ : syracuseStep 4008361 = 3006271) B3006271
theorem B32484331 : Blo 936583 32484331 := bstep (se 1 (by rfl) ⟨24363248, by rfl⟩ : syracuseStep 32484331 = 48726497) B48726497
theorem B8008247 : Blo 936583 8008247 := bstep (se 1 (by rfl) ⟨6006185, by rfl⟩ : syracuseStep 8008247 = 12012371) B12012371
theorem B2372287 : Blo 936583 2372287 := bstep (se 1 (by rfl) ⟨1779215, by rfl⟩ : syracuseStep 2372287 = 3558431) B3558431
theorem B4502411 : Blo 936583 4502411 := bstep (se 1 (by rfl) ⟨3376808, by rfl⟩ : syracuseStep 4502411 = 6753617) B6753617
theorem B2111903 : Blo 936583 2111903 := bstep (se 1 (by rfl) ⟨1583927, by rfl⟩ : syracuseStep 2111903 = 3167855) B3167855
theorem B2111993 : Blo 936583 2111993 := bstep (se 2 (by rfl) ⟨791997, by rfl⟩ : syracuseStep 2111993 = 1583995) B1583995
theorem B2112479 : Blo 936583 2112479 := bstep (se 1 (by rfl) ⟨1584359, by rfl⟩ : syracuseStep 2112479 = 3168719) B3168719
theorem B2112767 : Blo 936583 2112767 := bstep (se 1 (by rfl) ⟨1584575, by rfl⟩ : syracuseStep 2112767 = 3169151) B3169151
theorem B1785503 : Blo 936583 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B176111455 : Blo 936583 176111455 := bstep (se 1 (by rfl) ⟨132083591, by rfl⟩ : syracuseStep 176111455 = 264167183) B264167183
theorem B1523951 : Blo 936583 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B2113775 : Blo 936583 2113775 := bstep (se 1 (by rfl) ⟨1585331, by rfl⟩ : syracuseStep 2113775 = 3170663) B3170663
theorem B32489981 : Blo 936583 32489981 := bstep (se 3 (by rfl) ⟨6091871, by rfl⟩ : syracuseStep 32489981 = 12183743) B12183743
theorem B2114279 : Blo 936583 2114279 := bstep (se 1 (by rfl) ⟨1585709, by rfl⟩ : syracuseStep 2114279 = 3171419) B3171419
theorem B2115431 : Blo 936583 2115431 := bstep (se 1 (by rfl) ⟨1586573, by rfl⟩ : syracuseStep 2115431 = 3173147) B3173147
theorem B2115647 : Blo 936583 2115647 := bstep (se 1 (by rfl) ⟨1586735, by rfl⟩ : syracuseStep 2115647 = 3173471) B3173471
theorem B14469185 : Blo 936583 14469185 := bstep (se 2 (by rfl) ⟨5425944, by rfl⟩ : syracuseStep 14469185 = 10851889) B10851889
theorem B3557627 : Blo 936583 3557627 := bstep (se 1 (by rfl) ⟨2668220, by rfl⟩ : syracuseStep 3557627 = 5336441) B5336441
theorem B4016411 : Blo 936583 4016411 := bstep (se 1 (by rfl) ⟨3012308, by rfl⟩ : syracuseStep 4016411 = 6024617) B6024617
theorem B2116223 : Blo 936583 2116223 := bstep (se 1 (by rfl) ⟨1587167, by rfl⟩ : syracuseStep 2116223 = 3174335) B3174335
theorem B936607 : Blo 936583 936607 := bstep (se 1 (by rfl) ⟨702455, by rfl⟩ : syracuseStep 936607 = 1404911) B1404911
theorem B3164831 : Blo 936583 3164831 := bstep (se 1 (by rfl) ⟨2373623, by rfl⟩ : syracuseStep 3164831 = 4747247) B4747247
theorem B3558127 : Blo 936583 3558127 := bstep (se 1 (by rfl) ⟨2668595, by rfl⟩ : syracuseStep 3558127 = 5337191) B5337191
theorem B937215 : Blo 936583 937215 := bstep (se 1 (by rfl) ⟨702911, by rfl⟩ : syracuseStep 937215 = 1405823) B1405823
theorem B937263 : Blo 936583 937263 := bstep (se 1 (by rfl) ⟨702947, by rfl⟩ : syracuseStep 937263 = 1405895) B1405895
theorem B937503 : Blo 936583 937503 := bstep (se 1 (by rfl) ⟨703127, by rfl⟩ : syracuseStep 937503 = 1406255) B1406255
theorem B937759 : Blo 936583 937759 := bstep (se 1 (by rfl) ⟨703319, by rfl⟩ : syracuseStep 937759 = 1406639) B1406639
theorem B937895 : Blo 936583 937895 := bstep (se 1 (by rfl) ⟨703421, by rfl⟩ : syracuseStep 937895 = 1406843) B1406843
theorem B34263161 : Blo 936583 34263161 := bstep (se 2 (by rfl) ⟨12848685, by rfl⟩ : syracuseStep 34263161 = 25697371) B25697371
theorem B938463 : Blo 936583 938463 := bstep (se 1 (by rfl) ⟨703847, by rfl⟩ : syracuseStep 938463 = 1407695) B1407695
theorem B938471 : Blo 936583 938471 := bstep (se 1 (by rfl) ⟨703853, by rfl⟩ : syracuseStep 938471 = 1407707) B1407707
theorem B938495 : Blo 936583 938495 := bstep (se 1 (by rfl) ⟨703871, by rfl⟩ : syracuseStep 938495 = 1407743) B1407743
theorem B939035 : Blo 936583 939035 := bstep (se 1 (by rfl) ⟨704276, by rfl⟩ : syracuseStep 939035 = 1408553) B1408553
theorem B939291 : Blo 936583 939291 := bstep (se 1 (by rfl) ⟨704468, by rfl⟩ : syracuseStep 939291 = 1408937) B1408937
theorem B939727 : Blo 936583 939727 := bstep (se 1 (by rfl) ⟨704795, by rfl⟩ : syracuseStep 939727 = 1409591) B1409591
theorem B940143 : Blo 936583 940143 := bstep (se 1 (by rfl) ⟨705107, by rfl⟩ : syracuseStep 940143 = 1410215) B1410215
theorem B940239 : Blo 936583 940239 := bstep (se 1 (by rfl) ⟨705179, by rfl⟩ : syracuseStep 940239 = 1410359) B1410359
theorem B10672559 : Blo 936583 10672559 := bstep (se 1 (by rfl) ⟨8004419, by rfl⟩ : syracuseStep 10672559 = 16008839) B16008839
theorem B13524529 : Blo 936583 13524529 := bstep (se 2 (by rfl) ⟨5071698, by rfl⟩ : syracuseStep 13524529 = 10143397) B10143397
theorem B3563459 : Blo 936583 3563459 := bstep (se 1 (by rfl) ⟨2672594, by rfl⟩ : syracuseStep 3563459 = 5345189) B5345189
theorem B3563959 : Blo 936583 3563959 := bstep (se 1 (by rfl) ⟨2672969, by rfl⟩ : syracuseStep 3563959 = 5345939) B5345939
theorem B13525865 : Blo 936583 13525865 := bstep (se 2 (by rfl) ⟨5072199, by rfl⟩ : syracuseStep 13525865 = 10144399) B10144399
theorem B3565903 : Blo 936583 3565903 := bstep (se 1 (by rfl) ⟨2674427, by rfl⟩ : syracuseStep 3565903 = 5348855) B5348855
theorem B6416795 : Blo 936583 6416795 := bstep (se 1 (by rfl) ⟨4812596, by rfl⟩ : syracuseStep 6416795 = 9625193) B9625193
theorem B3567347 : Blo 936583 3567347 := bstep (se 1 (by rfl) ⟨2675510, by rfl⟩ : syracuseStep 3567347 = 5351021) B5351021
theorem B8023967 : Blo 936583 8023967 := bstep (se 1 (by rfl) ⟨6017975, by rfl⟩ : syracuseStep 8023967 = 12035951) B12035951
theorem B3011039 : Blo 936583 3011039 := bstep (se 1 (by rfl) ⟨2258279, by rfl⟩ : syracuseStep 3011039 = 4516559) B4516559
theorem B4748057 : Blo 936583 4748057 := bstep (se 2 (by rfl) ⟨1780521, by rfl⟩ : syracuseStep 4748057 = 3561043) B3561043
theorem B1405751 : Blo 936583 1405751 := bstep (se 1 (by rfl) ⟨1054313, by rfl⟩ : syracuseStep 1405751 = 2108627) B2108627
theorem B1405979 : Blo 936583 1405979 := bstep (se 1 (by rfl) ⟨1054484, by rfl⟩ : syracuseStep 1405979 = 2108969) B2108969
theorem B1406063 : Blo 936583 1406063 := bstep (se 1 (by rfl) ⟨1054547, by rfl⟩ : syracuseStep 1406063 = 2109095) B2109095
theorem B1406183 : Blo 936583 1406183 := bstep (se 1 (by rfl) ⟨1054637, by rfl⟩ : syracuseStep 1406183 = 2109275) B2109275
theorem B1406279 : Blo 936583 1406279 := bstep (se 1 (by rfl) ⟨1054709, by rfl⟩ : syracuseStep 1406279 = 2109419) B2109419
theorem B249984467 : Blo 936583 249984467 := bstep (se 1 (by rfl) ⟨187488350, by rfl⟩ : syracuseStep 249984467 = 374976701) B374976701
theorem B1406519 : Blo 936583 1406519 := bstep (se 1 (by rfl) ⟨1054889, by rfl⟩ : syracuseStep 1406519 = 2109779) B2109779
theorem B9631753 : Blo 936583 9631753 := bstep (se 2 (by rfl) ⟨3611907, by rfl⟩ : syracuseStep 9631753 = 7223815) B7223815
theorem B1408895 : Blo 936583 1408895 := bstep (se 1 (by rfl) ⟨1056671, by rfl⟩ : syracuseStep 1408895 = 2113343) B2113343
theorem B1015967 : Blo 936583 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B1409183 : Blo 936583 1409183 := bstep (se 1 (by rfl) ⟨1056887, by rfl⟩ : syracuseStep 1409183 = 2113775) B2113775
theorem B21659987 : Blo 936583 21659987 := bstep (se 1 (by rfl) ⟨16244990, by rfl⟩ : syracuseStep 21659987 = 32489981) B32489981
theorem B1409519 : Blo 936583 1409519 := bstep (se 1 (by rfl) ⟨1057139, by rfl⟩ : syracuseStep 1409519 = 2114279) B2114279
theorem B4751945 : Blo 936583 4751945 := bstep (se 2 (by rfl) ⟨1781979, by rfl⟩ : syracuseStep 4751945 = 3563959) B3563959
theorem B1410287 : Blo 936583 1410287 := bstep (se 1 (by rfl) ⟨1057715, by rfl⟩ : syracuseStep 1410287 = 2115431) B2115431
theorem B1410431 : Blo 936583 1410431 := bstep (se 1 (by rfl) ⟨1057823, by rfl⟩ : syracuseStep 1410431 = 2115647) B2115647
theorem B1410815 : Blo 936583 1410815 := bstep (se 1 (by rfl) ⟨1058111, by rfl⟩ : syracuseStep 1410815 = 2116223) B2116223
theorem B22842107 : Blo 936583 22842107 := bstep (se 1 (by rfl) ⟨17131580, by rfl⟩ : syracuseStep 22842107 = 34263161) B34263161
theorem B4754537 : Blo 936583 4754537 := bstep (se 2 (by rfl) ⟨1782951, by rfl⟩ : syracuseStep 4754537 = 3565903) B3565903
theorem B5344481 : Blo 936583 5344481 := bstep (se 2 (by rfl) ⟨2004180, by rfl⟩ : syracuseStep 5344481 = 4008361) B4008361
theorem B2035199 : Blo 936583 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B7115039 : Blo 936583 7115039 := bstep (se 1 (by rfl) ⟨5336279, by rfl⟩ : syracuseStep 7115039 = 10672559) B10672559
theorem B10687139 : Blo 936583 10687139 := bstep (se 1 (by rfl) ⟨8015354, by rfl⟩ : syracuseStep 10687139 = 16030709) B16030709
theorem B173249765 : Blo 936583 173249765 := bstep (se 4 (by rfl) ⟨16242165, by rfl⟩ : syracuseStep 173249765 = 32484331) B32484331
theorem B9017243 : Blo 936583 9017243 := bstep (se 1 (by rfl) ⟨6762932, by rfl⟩ : syracuseStep 9017243 = 13525865) B13525865
theorem B5349311 : Blo 936583 5349311 := bstep (se 1 (by rfl) ⟨4011983, by rfl⟩ : syracuseStep 5349311 = 8023967) B8023967
theorem B2007359 : Blo 936583 2007359 := bstep (se 1 (by rfl) ⟨1505519, by rfl⟩ : syracuseStep 2007359 = 3011039) B3011039
theorem B4761341 : Blo 936583 4761341 := bstep (se 3 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 4761341 = 1785503) B1785503
theorem B18032705 : Blo 936583 18032705 := bstep (se 2 (by rfl) ⟨6762264, by rfl⟩ : syracuseStep 18032705 = 13524529) B13524529
theorem B9022195 : Blo 936583 9022195 := bstep (se 1 (by rfl) ⟨6766646, by rfl⟩ : syracuseStep 9022195 = 13533293) B13533293
theorem B5352479 : Blo 936583 5352479 := bstep (se 1 (by rfl) ⟨4014359, by rfl⟩ : syracuseStep 5352479 = 8028719) B8028719
theorem B9646123 : Blo 936583 9646123 := bstep (se 1 (by rfl) ⟨7234592, by rfl⟩ : syracuseStep 9646123 = 14469185) B14469185
theorem B2371751 : Blo 936583 2371751 := bstep (se 1 (by rfl) ⟨1778813, by rfl⟩ : syracuseStep 2371751 = 3557627) B3557627
theorem B2109887 : Blo 936583 2109887 := bstep (se 1 (by rfl) ⟨1582415, by rfl⟩ : syracuseStep 2109887 = 3164831) B3164831
theorem B2110625 : Blo 936583 2110625 := bstep (se 2 (by rfl) ⟨791484, by rfl⟩ : syracuseStep 2110625 = 1582969) B1582969
theorem B6863879 : Blo 936583 6863879 := bstep (se 1 (by rfl) ⟨5147909, by rfl⟩ : syracuseStep 6863879 = 10295819) B10295819
theorem B2375639 : Blo 936583 2375639 := bstep (se 1 (by rfl) ⟨1781729, by rfl⟩ : syracuseStep 2375639 = 3563459) B3563459
theorem B3163049 : Blo 936583 3163049 := bstep (se 2 (by rfl) ⟨1186143, by rfl⟩ : syracuseStep 3163049 = 2372287) B2372287
theorem B4277863 : Blo 936583 4277863 := bstep (se 1 (by rfl) ⟨3208397, by rfl⟩ : syracuseStep 4277863 = 6416795) B6416795
theorem B2378231 : Blo 936583 2378231 := bstep (se 1 (by rfl) ⟨1783673, by rfl⟩ : syracuseStep 2378231 = 3567347) B3567347
theorem B3165371 : Blo 936583 3165371 := bstep (se 1 (by rfl) ⟨2374028, by rfl⟩ : syracuseStep 3165371 = 4748057) B4748057
theorem B937167 : Blo 936583 937167 := bstep (se 1 (by rfl) ⟨702875, by rfl⟩ : syracuseStep 937167 = 1405751) B1405751
theorem B3001607 : Blo 936583 3001607 := bstep (se 1 (by rfl) ⟨2251205, by rfl⟩ : syracuseStep 3001607 = 4502411) B4502411
theorem B937319 : Blo 936583 937319 := bstep (se 1 (by rfl) ⟨702989, by rfl⟩ : syracuseStep 937319 = 1405979) B1405979
theorem B937375 : Blo 936583 937375 := bstep (se 1 (by rfl) ⟨703031, by rfl⟩ : syracuseStep 937375 = 1406063) B1406063
theorem B937455 : Blo 936583 937455 := bstep (se 1 (by rfl) ⟨703091, by rfl⟩ : syracuseStep 937455 = 1406183) B1406183
theorem B937519 : Blo 936583 937519 := bstep (se 1 (by rfl) ⟨703139, by rfl⟩ : syracuseStep 937519 = 1406279) B1406279
theorem B937679 : Blo 936583 937679 := bstep (se 1 (by rfl) ⟨703259, by rfl⟩ : syracuseStep 937679 = 1406519) B1406519
theorem B24695945 : Blo 936583 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B939263 : Blo 936583 939263 := bstep (se 1 (by rfl) ⟨704447, by rfl⟩ : syracuseStep 939263 = 1408895) B1408895
theorem B51369349 : Blo 936583 51369349 := bstep (se 4 (by rfl) ⟨4815876, by rfl⟩ : syracuseStep 51369349 = 9631753) B9631753
theorem B939775 : Blo 936583 939775 := bstep (se 1 (by rfl) ⟨704831, by rfl⟩ : syracuseStep 939775 = 1409663) B1409663
theorem B940031 : Blo 936583 940031 := bstep (se 1 (by rfl) ⟨705023, by rfl⟩ : syracuseStep 940031 = 1410047) B1410047
theorem B940359 : Blo 936583 940359 := bstep (se 1 (by rfl) ⟨705269, by rfl⟩ : syracuseStep 940359 = 1410539) B1410539
theorem B940527 : Blo 936583 940527 := bstep (se 1 (by rfl) ⟨705395, by rfl⟩ : syracuseStep 940527 = 1410791) B1410791
theorem B2677607 : Blo 936583 2677607 := bstep (se 1 (by rfl) ⟨2008205, by rfl⟩ : syracuseStep 2677607 = 4016411) B4016411
theorem B4283771 : Blo 936583 4283771 := bstep (se 1 (by rfl) ⟨3212828, by rfl⟩ : syracuseStep 4283771 = 6425657) B6425657
theorem B9003743 : Blo 936583 9003743 := bstep (se 1 (by rfl) ⟨6752807, by rfl⟩ : syracuseStep 9003743 = 13505615) B13505615
theorem B3564263 : Blo 936583 3564263 := bstep (se 1 (by rfl) ⟨2673197, by rfl⟩ : syracuseStep 3564263 = 5346395) B5346395
theorem B4744007 : Blo 936583 4744007 := bstep (se 1 (by rfl) ⟨3558005, by rfl⟩ : syracuseStep 4744007 = 7116011) B7116011
theorem B4744169 : Blo 936583 4744169 := bstep (se 2 (by rfl) ⟨1779063, by rfl⟩ : syracuseStep 4744169 = 3558127) B3558127
theorem B2257087 : Blo 936583 2257087 := bstep (se 1 (by rfl) ⟨1692815, by rfl⟩ : syracuseStep 2257087 = 3385631) B3385631
theorem B1405211 : Blo 936583 1405211 := bstep (se 1 (by rfl) ⟨1053908, by rfl⟩ : syracuseStep 1405211 = 2107817) B2107817
theorem B1406249 : Blo 936583 1406249 := bstep (se 2 (by rfl) ⟨527343, by rfl⟩ : syracuseStep 1406249 = 1054687) B1054687
theorem B5338831 : Blo 936583 5338831 := bstep (se 1 (by rfl) ⟨4004123, by rfl⟩ : syracuseStep 5338831 = 8008247) B8008247
theorem B166656311 : Blo 936583 166656311 := bstep (se 1 (by rfl) ⟨124992233, by rfl⟩ : syracuseStep 166656311 = 249984467) B249984467
theorem B1407935 : Blo 936583 1407935 := bstep (se 1 (by rfl) ⟨1055951, by rfl⟩ : syracuseStep 1407935 = 2111903) B2111903
theorem B1407977 : Blo 936583 1407977 := bstep (se 2 (by rfl) ⟨527991, by rfl⟩ : syracuseStep 1407977 = 1055983) B1055983
theorem B1407995 : Blo 936583 1407995 := bstep (se 1 (by rfl) ⟨1055996, by rfl⟩ : syracuseStep 1407995 = 2111993) B2111993
theorem B1408319 : Blo 936583 1408319 := bstep (se 1 (by rfl) ⟨1056239, by rfl⟩ : syracuseStep 1408319 = 2112479) B2112479
theorem B1408511 : Blo 936583 1408511 := bstep (se 1 (by rfl) ⟨1056383, by rfl⟩ : syracuseStep 1408511 = 2112767) B2112767
theorem B234815273 : Blo 936583 234815273 := bstep (se 2 (by rfl) ⟨88055727, by rfl⟩ : syracuseStep 234815273 = 176111455) B176111455
theorem B5703817 : Blo 936583 5703817 := bstep (se 2 (by rfl) ⟨2138931, by rfl⟩ : syracuseStep 5703817 = 4277863) B4277863
theorem B2001071 : Blo 936583 2001071 := bstep (se 1 (by rfl) ⟨1500803, by rfl⟩ : syracuseStep 2001071 = 3001607) B3001607
theorem B12029593 : Blo 936583 12029593 := bstep (se 2 (by rfl) ⟨4511097, by rfl⟩ : syracuseStep 12029593 = 9022195) B9022195
theorem B6002495 : Blo 936583 6002495 := bstep (se 1 (by rfl) ⟨4501871, by rfl⟩ : syracuseStep 6002495 = 9003743) B9003743
theorem B68492465 : Blo 936583 68492465 := bstep (se 2 (by rfl) ⟨25684674, by rfl⟩ : syracuseStep 68492465 = 51369349) B51369349
theorem B7118441 : Blo 936583 7118441 := bstep (se 2 (by rfl) ⟨2669415, by rfl⟩ : syracuseStep 7118441 = 5338831) B5338831
theorem B1581167 : Blo 936583 1581167 := bstep (se 1 (by rfl) ⟨1185875, by rfl⟩ : syracuseStep 1581167 = 2371751) B2371751
theorem B156543515 : Blo 936583 156543515 := bstep (se 1 (by rfl) ⟨117407636, by rfl⟩ : syracuseStep 156543515 = 234815273) B234815273
theorem B1583759 : Blo 936583 1583759 := bstep (se 1 (by rfl) ⟨1187819, by rfl⟩ : syracuseStep 1583759 = 2375639) B2375639
theorem B2108699 : Blo 936583 2108699 := bstep (se 1 (by rfl) ⟨1581524, by rfl⟩ : syracuseStep 2108699 = 3163049) B3163049
theorem B1585487 : Blo 936583 1585487 := bstep (se 1 (by rfl) ⟨1189115, by rfl⟩ : syracuseStep 1585487 = 2378231) B2378231
theorem B2110247 : Blo 936583 2110247 := bstep (se 1 (by rfl) ⟨1582685, by rfl⟩ : syracuseStep 2110247 = 3165371) B3165371
theorem B1356799 : Blo 936583 1356799 := bstep (se 1 (by rfl) ⟨1017599, by rfl⟩ : syracuseStep 1356799 = 2035199) B2035199
theorem B7124759 : Blo 936583 7124759 := bstep (se 1 (by rfl) ⟨5343569, by rfl⟩ : syracuseStep 7124759 = 10687139) B10687139
theorem B16463963 : Blo 936583 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B6011495 : Blo 936583 6011495 := bstep (se 1 (by rfl) ⟨4508621, by rfl⟩ : syracuseStep 6011495 = 9017243) B9017243
theorem B1785071 : Blo 936583 1785071 := bstep (se 1 (by rfl) ⟨1338803, by rfl⟩ : syracuseStep 1785071 = 2677607) B2677607
theorem B12861497 : Blo 936583 12861497 := bstep (se 2 (by rfl) ⟨4823061, by rfl⟩ : syracuseStep 12861497 = 9646123) B9646123
theorem B2376175 : Blo 936583 2376175 := bstep (se 1 (by rfl) ⟨1782131, by rfl⟩ : syracuseStep 2376175 = 3564263) B3564263
theorem B3162671 : Blo 936583 3162671 := bstep (se 1 (by rfl) ⟨2372003, by rfl⟩ : syracuseStep 3162671 = 4744007) B4744007
theorem B3162779 : Blo 936583 3162779 := bstep (se 1 (by rfl) ⟨2372084, by rfl⟩ : syracuseStep 3162779 = 4744169) B4744169
theorem B18303677 : Blo 936583 18303677 := bstep (se 3 (by rfl) ⟨3431939, by rfl⟩ : syracuseStep 18303677 = 6863879) B6863879
theorem B936807 : Blo 936583 936807 := bstep (se 1 (by rfl) ⟨702605, by rfl⟩ : syracuseStep 936807 = 1405211) B1405211
theorem B937499 : Blo 936583 937499 := bstep (se 1 (by rfl) ⟨703124, by rfl⟩ : syracuseStep 937499 = 1406249) B1406249
theorem B11423389 : Blo 936583 11423389 := bstep (se 3 (by rfl) ⟨2141885, by rfl⟩ : syracuseStep 11423389 = 4283771) B4283771
theorem B111104207 : Blo 936583 111104207 := bstep (se 1 (by rfl) ⟨83328155, by rfl⟩ : syracuseStep 111104207 = 166656311) B166656311
theorem B938623 : Blo 936583 938623 := bstep (se 1 (by rfl) ⟨703967, by rfl⟩ : syracuseStep 938623 = 1407935) B1407935
theorem B938651 : Blo 936583 938651 := bstep (se 1 (by rfl) ⟨703988, by rfl⟩ : syracuseStep 938651 = 1407977) B1407977
theorem B938663 : Blo 936583 938663 := bstep (se 1 (by rfl) ⟨703997, by rfl⟩ : syracuseStep 938663 = 1407995) B1407995
theorem B938879 : Blo 936583 938879 := bstep (se 1 (by rfl) ⟨704159, by rfl⟩ : syracuseStep 938879 = 1408319) B1408319
theorem B939007 : Blo 936583 939007 := bstep (se 1 (by rfl) ⟨704255, by rfl⟩ : syracuseStep 939007 = 1408511) B1408511
theorem B939455 : Blo 936583 939455 := bstep (se 1 (by rfl) ⟨704591, by rfl⟩ : syracuseStep 939455 = 1409183) B1409183
theorem B14439991 : Blo 936583 14439991 := bstep (se 1 (by rfl) ⟨10829993, by rfl⟩ : syracuseStep 14439991 = 21659987) B21659987
theorem B939679 : Blo 936583 939679 := bstep (se 1 (by rfl) ⟨704759, by rfl⟩ : syracuseStep 939679 = 1409519) B1409519
theorem B3167963 : Blo 936583 3167963 := bstep (se 1 (by rfl) ⟨2375972, by rfl⟩ : syracuseStep 3167963 = 4751945) B4751945
theorem B2709245 : Blo 936583 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B940191 : Blo 936583 940191 := bstep (se 1 (by rfl) ⟨705143, by rfl⟩ : syracuseStep 940191 = 1410287) B1410287
theorem B940287 : Blo 936583 940287 := bstep (se 1 (by rfl) ⟨705215, by rfl⟩ : syracuseStep 940287 = 1410431) B1410431
theorem B940543 : Blo 936583 940543 := bstep (se 1 (by rfl) ⟨705407, by rfl⟩ : syracuseStep 940543 = 1410815) B1410815
theorem B15228071 : Blo 936583 15228071 := bstep (se 1 (by rfl) ⟨11421053, by rfl⟩ : syracuseStep 15228071 = 22842107) B22842107
theorem B3169691 : Blo 936583 3169691 := bstep (se 1 (by rfl) ⟨2377268, by rfl⟩ : syracuseStep 3169691 = 4754537) B4754537
theorem B3562987 : Blo 936583 3562987 := bstep (se 1 (by rfl) ⟨2672240, by rfl⟩ : syracuseStep 3562987 = 5344481) B5344481
theorem B4743359 : Blo 936583 4743359 := bstep (se 1 (by rfl) ⟨3557519, by rfl⟩ : syracuseStep 4743359 = 7115039) B7115039
theorem B115499843 : Blo 936583 115499843 := bstep (se 1 (by rfl) ⟨86624882, by rfl⟩ : syracuseStep 115499843 = 173249765) B173249765
theorem B3566207 : Blo 936583 3566207 := bstep (se 1 (by rfl) ⟨2674655, by rfl⟩ : syracuseStep 3566207 = 5349311) B5349311
theorem B1338239 : Blo 936583 1338239 := bstep (se 1 (by rfl) ⟨1003679, by rfl⟩ : syracuseStep 1338239 = 2007359) B2007359
theorem B3009449 : Blo 936583 3009449 := bstep (se 2 (by rfl) ⟨1128543, by rfl⟩ : syracuseStep 3009449 = 2257087) B2257087
theorem B3174227 : Blo 936583 3174227 := bstep (se 1 (by rfl) ⟨2380670, by rfl⟩ : syracuseStep 3174227 = 4761341) B4761341
theorem B12021803 : Blo 936583 12021803 := bstep (se 1 (by rfl) ⟨9016352, by rfl⟩ : syracuseStep 12021803 = 18032705) B18032705
theorem B3568319 : Blo 936583 3568319 := bstep (se 1 (by rfl) ⟨2676239, by rfl⟩ : syracuseStep 3568319 = 5352479) B5352479
theorem B1406591 : Blo 936583 1406591 := bstep (se 1 (by rfl) ⟨1054943, by rfl⟩ : syracuseStep 1406591 = 2109887) B2109887
theorem B1407083 : Blo 936583 1407083 := bstep (se 1 (by rfl) ⟨1055312, by rfl⟩ : syracuseStep 1407083 = 2110625) B2110625
theorem B7605089 : Blo 936583 7605089 := bstep (se 2 (by rfl) ⟨2851908, by rfl⟩ : syracuseStep 7605089 = 5703817) B5703817
theorem B4001663 : Blo 936583 4001663 := bstep (se 1 (by rfl) ⟨3001247, by rfl⟩ : syracuseStep 4001663 = 6002495) B6002495
theorem B1054111 : Blo 936583 1054111 := bstep (se 1 (by rfl) ⟨790583, by rfl⟩ : syracuseStep 1054111 = 1581167) B1581167
theorem B1809065 : Blo 936583 1809065 := bstep (se 2 (by rfl) ⟨678399, by rfl⟩ : syracuseStep 1809065 = 1356799) B1356799
theorem B1055839 : Blo 936583 1055839 := bstep (se 1 (by rfl) ⟨791879, by rfl⟩ : syracuseStep 1055839 = 1583759) B1583759
theorem B2006299 : Blo 936583 2006299 := bstep (se 1 (by rfl) ⟨1504724, by rfl⟩ : syracuseStep 2006299 = 3009449) B3009449
theorem B1056991 : Blo 936583 1056991 := bstep (se 1 (by rfl) ⟨792743, by rfl⟩ : syracuseStep 1056991 = 1585487) B1585487
theorem B4007663 : Blo 936583 4007663 := bstep (se 1 (by rfl) ⟨3005747, by rfl⟩ : syracuseStep 4007663 = 6011495) B6011495
theorem B1190047 : Blo 936583 1190047 := bstep (se 1 (by rfl) ⟨892535, by rfl⟩ : syracuseStep 1190047 = 1785071) B1785071
theorem B2108447 : Blo 936583 2108447 := bstep (se 1 (by rfl) ⟨1581335, by rfl⟩ : syracuseStep 2108447 = 3162671) B3162671
theorem B2108519 : Blo 936583 2108519 := bstep (se 1 (by rfl) ⟨1581389, by rfl⟩ : syracuseStep 2108519 = 3162779) B3162779
theorem B12202451 : Blo 936583 12202451 := bstep (se 1 (by rfl) ⟨9151838, by rfl⟩ : syracuseStep 12202451 = 18303677) B18303677
theorem B74069471 : Blo 936583 74069471 := bstep (se 1 (by rfl) ⟨55552103, by rfl⟩ : syracuseStep 74069471 = 111104207) B111104207
theorem B2111975 : Blo 936583 2111975 := bstep (se 1 (by rfl) ⟨1583981, by rfl⟩ : syracuseStep 2111975 = 3167963) B3167963
theorem B7224653 : Blo 936583 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B45661643 : Blo 936583 45661643 := bstep (se 1 (by rfl) ⟨34246232, by rfl⟩ : syracuseStep 45661643 = 68492465) B68492465
theorem B16039457 : Blo 936583 16039457 := bstep (se 2 (by rfl) ⟨6014796, by rfl⟩ : syracuseStep 16039457 = 12029593) B12029593
theorem B2113127 : Blo 936583 2113127 := bstep (se 1 (by rfl) ⟨1584845, by rfl⟩ : syracuseStep 2113127 = 3169691) B3169691
theorem B3162239 : Blo 936583 3162239 := bstep (se 1 (by rfl) ⟨2371679, by rfl⟩ : syracuseStep 3162239 = 4743359) B4743359
theorem B2377471 : Blo 936583 2377471 := bstep (se 1 (by rfl) ⟨1783103, by rfl⟩ : syracuseStep 2377471 = 3566207) B3566207
theorem B19253321 : Blo 936583 19253321 := bstep (se 2 (by rfl) ⟨7219995, by rfl⟩ : syracuseStep 19253321 = 14439991) B14439991
theorem B2116151 : Blo 936583 2116151 := bstep (se 1 (by rfl) ⟨1587113, by rfl⟩ : syracuseStep 2116151 = 3174227) B3174227
theorem B8014535 : Blo 936583 8014535 := bstep (se 1 (by rfl) ⟨6010901, by rfl⟩ : syracuseStep 8014535 = 12021803) B12021803
theorem B2378879 : Blo 936583 2378879 := bstep (se 1 (by rfl) ⟨1784159, by rfl⟩ : syracuseStep 2378879 = 3568319) B3568319
theorem B937727 : Blo 936583 937727 := bstep (se 1 (by rfl) ⟨703295, by rfl⟩ : syracuseStep 937727 = 1406591) B1406591
theorem B938055 : Blo 936583 938055 := bstep (se 1 (by rfl) ⟨703541, by rfl⟩ : syracuseStep 938055 = 1407083) B1407083
theorem B8574331 : Blo 936583 8574331 := bstep (se 1 (by rfl) ⟨6430748, by rfl⟩ : syracuseStep 8574331 = 12861497) B12861497
theorem B3168233 : Blo 936583 3168233 := bstep (se 2 (by rfl) ⟨1188087, by rfl⟩ : syracuseStep 3168233 = 2376175) B2376175
theorem B10152047 : Blo 936583 10152047 := bstep (se 1 (by rfl) ⟨7614035, by rfl⟩ : syracuseStep 10152047 = 15228071) B15228071
theorem B15231185 : Blo 936583 15231185 := bstep (se 2 (by rfl) ⟨5711694, by rfl⟩ : syracuseStep 15231185 = 11423389) B11423389
theorem B4745627 : Blo 936583 4745627 := bstep (se 1 (by rfl) ⟨3559220, by rfl⟩ : syracuseStep 4745627 = 7118441) B7118441
theorem B5336189 : Blo 936583 5336189 := bstep (se 3 (by rfl) ⟨1000535, by rfl⟩ : syracuseStep 5336189 = 2001071) B2001071
theorem B76999895 : Blo 936583 76999895 := bstep (se 1 (by rfl) ⟨57749921, by rfl⟩ : syracuseStep 76999895 = 115499843) B115499843
theorem B104362343 : Blo 936583 104362343 := bstep (se 1 (by rfl) ⟨78271757, by rfl⟩ : syracuseStep 104362343 = 156543515) B156543515
theorem B1405799 : Blo 936583 1405799 := bstep (se 1 (by rfl) ⟨1054349, by rfl⟩ : syracuseStep 1405799 = 2108699) B2108699
theorem B3568637 : Blo 936583 3568637 := bstep (se 3 (by rfl) ⟨669119, by rfl⟩ : syracuseStep 3568637 = 1338239) B1338239
theorem B1406831 : Blo 936583 1406831 := bstep (se 1 (by rfl) ⟨1055123, by rfl⟩ : syracuseStep 1406831 = 2110247) B2110247
theorem B4749839 : Blo 936583 4749839 := bstep (se 1 (by rfl) ⟨3562379, by rfl⟩ : syracuseStep 4749839 = 7124759) B7124759
theorem B10975975 : Blo 936583 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B4750649 : Blo 936583 4750649 := bstep (se 2 (by rfl) ⟨1781493, by rfl⟩ : syracuseStep 4750649 = 3562987) B3562987
theorem B1409321 : Blo 936583 1409321 := bstep (se 2 (by rfl) ⟨528495, by rfl⟩ : syracuseStep 1409321 = 1056991) B1056991
theorem B1410767 : Blo 936583 1410767 := bstep (se 1 (by rfl) ⟨1058075, by rfl⟩ : syracuseStep 1410767 = 2116151) B2116151
theorem B5343023 : Blo 936583 5343023 := bstep (se 1 (by rfl) ⟨4007267, by rfl⟩ : syracuseStep 5343023 = 8014535) B8014535
theorem B4824173 : Blo 936583 4824173 := bstep (se 3 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 4824173 = 1809065) B1809065
theorem B69574895 : Blo 936583 69574895 := bstep (se 1 (by rfl) ⟨52181171, by rfl⟩ : syracuseStep 69574895 = 104362343) B104362343
theorem B8134967 : Blo 936583 8134967 := bstep (se 1 (by rfl) ⟨6101225, by rfl⟩ : syracuseStep 8134967 = 12202451) B12202451
theorem B10692971 : Blo 936583 10692971 := bstep (se 1 (by rfl) ⟨8019728, by rfl⟩ : syracuseStep 10692971 = 16039457) B16039457
theorem B2108159 : Blo 936583 2108159 := bstep (se 1 (by rfl) ⟨1581119, by rfl⟩ : syracuseStep 2108159 = 3162239) B3162239
theorem B1585919 : Blo 936583 1585919 := bstep (se 1 (by rfl) ⟨1189439, by rfl⟩ : syracuseStep 1585919 = 2378879) B2378879
theorem B1586729 : Blo 936583 1586729 := bstep (se 2 (by rfl) ⟨595023, by rfl⟩ : syracuseStep 1586729 = 1190047) B1190047
theorem B58538533 : Blo 936583 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B2112155 : Blo 936583 2112155 := bstep (se 1 (by rfl) ⟨1584116, by rfl⟩ : syracuseStep 2112155 = 3168233) B3168233
theorem B2671775 : Blo 936583 2671775 := bstep (se 1 (by rfl) ⟨2003831, by rfl⟩ : syracuseStep 2671775 = 4007663) B4007663
theorem B6768031 : Blo 936583 6768031 := bstep (se 1 (by rfl) ⟨5076023, by rfl⟩ : syracuseStep 6768031 = 10152047) B10152047
theorem B10700261 : Blo 936583 10700261 := bstep (se 4 (by rfl) ⟨1003149, by rfl⟩ : syracuseStep 10700261 = 2006299) B2006299
theorem B3163751 : Blo 936583 3163751 := bstep (se 1 (by rfl) ⟨2372813, by rfl⟩ : syracuseStep 3163751 = 4745627) B4745627
theorem B3557459 : Blo 936583 3557459 := bstep (se 1 (by rfl) ⟨2668094, by rfl⟩ : syracuseStep 3557459 = 5336189) B5336189
theorem B51333263 : Blo 936583 51333263 := bstep (se 1 (by rfl) ⟨38499947, by rfl⟩ : syracuseStep 51333263 = 76999895) B76999895
theorem B937199 : Blo 936583 937199 := bstep (se 1 (by rfl) ⟨702899, by rfl⟩ : syracuseStep 937199 = 1405799) B1405799
theorem B2379091 : Blo 936583 2379091 := bstep (se 1 (by rfl) ⟨1784318, by rfl⟩ : syracuseStep 2379091 = 3568637) B3568637
theorem B937887 : Blo 936583 937887 := bstep (se 1 (by rfl) ⟨703415, by rfl⟩ : syracuseStep 937887 = 1406831) B1406831
theorem B3166559 : Blo 936583 3166559 := bstep (se 1 (by rfl) ⟨2374919, by rfl⟩ : syracuseStep 3166559 = 4749839) B4749839
theorem B3167099 : Blo 936583 3167099 := bstep (se 1 (by rfl) ⟨2375324, by rfl⟩ : syracuseStep 3167099 = 4750649) B4750649
theorem B10671101 : Blo 936583 10671101 := bstep (se 3 (by rfl) ⟨2000831, by rfl⟩ : syracuseStep 10671101 = 4001663) B4001663
theorem B12835547 : Blo 936583 12835547 := bstep (se 1 (by rfl) ⟨9626660, by rfl⟩ : syracuseStep 12835547 = 19253321) B19253321
theorem B5070059 : Blo 936583 5070059 := bstep (se 1 (by rfl) ⟨3802544, by rfl⟩ : syracuseStep 5070059 = 7605089) B7605089
theorem B3169961 : Blo 936583 3169961 := bstep (se 2 (by rfl) ⟨1188735, by rfl⟩ : syracuseStep 3169961 = 2377471) B2377471
theorem B10154123 : Blo 936583 10154123 := bstep (se 1 (by rfl) ⟨7615592, by rfl⟩ : syracuseStep 10154123 = 15231185) B15231185
theorem B11432441 : Blo 936583 11432441 := bstep (se 2 (by rfl) ⟨4287165, by rfl⟩ : syracuseStep 11432441 = 8574331) B8574331
theorem B1405481 : Blo 936583 1405481 := bstep (se 2 (by rfl) ⟨527055, by rfl⟩ : syracuseStep 1405481 = 1054111) B1054111
theorem B1405631 : Blo 936583 1405631 := bstep (se 1 (by rfl) ⟨1054223, by rfl⟩ : syracuseStep 1405631 = 2108447) B2108447
theorem B1405679 : Blo 936583 1405679 := bstep (se 1 (by rfl) ⟨1054259, by rfl⟩ : syracuseStep 1405679 = 2108519) B2108519
theorem B49379647 : Blo 936583 49379647 := bstep (se 1 (by rfl) ⟨37034735, by rfl⟩ : syracuseStep 49379647 = 74069471) B74069471
theorem B1407785 : Blo 936583 1407785 := bstep (se 2 (by rfl) ⟨527919, by rfl⟩ : syracuseStep 1407785 = 1055839) B1055839
theorem B1407983 : Blo 936583 1407983 := bstep (se 1 (by rfl) ⟨1055987, by rfl⟩ : syracuseStep 1407983 = 2111975) B2111975
theorem B4816435 : Blo 936583 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B30441095 : Blo 936583 30441095 := bstep (se 1 (by rfl) ⟨22830821, by rfl⟩ : syracuseStep 30441095 = 45661643) B45661643
theorem B1408751 : Blo 936583 1408751 := bstep (se 1 (by rfl) ⟨1056563, by rfl⟩ : syracuseStep 1408751 = 2113127) B2113127
theorem B7114067 : Blo 936583 7114067 := bstep (se 1 (by rfl) ⟨5335550, by rfl⟩ : syracuseStep 7114067 = 10671101) B10671101
theorem B8557031 : Blo 936583 8557031 := bstep (se 1 (by rfl) ⟨6417773, by rfl⟩ : syracuseStep 8557031 = 12835547) B12835547
theorem B3216115 : Blo 936583 3216115 := bstep (se 1 (by rfl) ⟨2412086, by rfl⟩ : syracuseStep 3216115 = 4824173) B4824173
theorem B3380039 : Blo 936583 3380039 := bstep (se 1 (by rfl) ⟨2535029, by rfl⟩ : syracuseStep 3380039 = 5070059) B5070059
theorem B1053432469 : Blo 936583 1053432469 := bstep (se 6 (by rfl) ⟨24689823, by rfl⟩ : syracuseStep 1053432469 = 49379647) B49379647
theorem B1057279 : Blo 936583 1057279 := bstep (se 1 (by rfl) ⟨792959, by rfl⟩ : syracuseStep 1057279 = 1585919) B1585919
theorem B1057819 : Blo 936583 1057819 := bstep (se 1 (by rfl) ⟨793364, by rfl⟩ : syracuseStep 1057819 = 1586729) B1586729
theorem B20294063 : Blo 936583 20294063 := bstep (se 1 (by rfl) ⟨15220547, by rfl⟩ : syracuseStep 20294063 = 30441095) B30441095
theorem B1781183 : Blo 936583 1781183 := bstep (se 1 (by rfl) ⟨1335887, by rfl⟩ : syracuseStep 1781183 = 2671775) B2671775
theorem B2109167 : Blo 936583 2109167 := bstep (se 1 (by rfl) ⟨1581875, by rfl⟩ : syracuseStep 2109167 = 3163751) B3163751
theorem B2371639 : Blo 936583 2371639 := bstep (se 1 (by rfl) ⟨1778729, by rfl⟩ : syracuseStep 2371639 = 3557459) B3557459
theorem B34222175 : Blo 936583 34222175 := bstep (se 1 (by rfl) ⟨25666631, by rfl⟩ : syracuseStep 34222175 = 51333263) B51333263
theorem B9024041 : Blo 936583 9024041 := bstep (se 2 (by rfl) ⟨3384015, by rfl⟩ : syracuseStep 9024041 = 6768031) B6768031
theorem B2111039 : Blo 936583 2111039 := bstep (se 1 (by rfl) ⟨1583279, by rfl⟩ : syracuseStep 2111039 = 3166559) B3166559
theorem B2111399 : Blo 936583 2111399 := bstep (se 1 (by rfl) ⟨1583549, by rfl⟩ : syracuseStep 2111399 = 3167099) B3167099
theorem B2113307 : Blo 936583 2113307 := bstep (se 1 (by rfl) ⟨1584980, by rfl⟩ : syracuseStep 2113307 = 3169961) B3169961
theorem B46383263 : Blo 936583 46383263 := bstep (se 1 (by rfl) ⟨34787447, by rfl⟩ : syracuseStep 46383263 = 69574895) B69574895
theorem B5423311 : Blo 936583 5423311 := bstep (se 1 (by rfl) ⟨4067483, by rfl⟩ : syracuseStep 5423311 = 8134967) B8134967
theorem B7128647 : Blo 936583 7128647 := bstep (se 1 (by rfl) ⟨5346485, by rfl⟩ : syracuseStep 7128647 = 10692971) B10692971
theorem B6769415 : Blo 936583 6769415 := bstep (se 1 (by rfl) ⟨5077061, by rfl⟩ : syracuseStep 6769415 = 10154123) B10154123
theorem B7621627 : Blo 936583 7621627 := bstep (se 1 (by rfl) ⟨5716220, by rfl⟩ : syracuseStep 7621627 = 11432441) B11432441
theorem B936987 : Blo 936583 936987 := bstep (se 1 (by rfl) ⟨702740, by rfl⟩ : syracuseStep 936987 = 1405481) B1405481
theorem B937087 : Blo 936583 937087 := bstep (se 1 (by rfl) ⟨702815, by rfl⟩ : syracuseStep 937087 = 1405631) B1405631
theorem B937119 : Blo 936583 937119 := bstep (se 1 (by rfl) ⟨702839, by rfl⟩ : syracuseStep 937119 = 1405679) B1405679
theorem B938523 : Blo 936583 938523 := bstep (se 1 (by rfl) ⟨703892, by rfl⟩ : syracuseStep 938523 = 1407785) B1407785
theorem B938655 : Blo 936583 938655 := bstep (se 1 (by rfl) ⟨703991, by rfl⟩ : syracuseStep 938655 = 1407983) B1407983
theorem B939167 : Blo 936583 939167 := bstep (se 1 (by rfl) ⟨704375, by rfl⟩ : syracuseStep 939167 = 1408751) B1408751
theorem B939547 : Blo 936583 939547 := bstep (se 1 (by rfl) ⟨704660, by rfl⟩ : syracuseStep 939547 = 1409321) B1409321
theorem B7133507 : Blo 936583 7133507 := bstep (se 1 (by rfl) ⟨5350130, by rfl⟩ : syracuseStep 7133507 = 10700261) B10700261
theorem B940511 : Blo 936583 940511 := bstep (se 1 (by rfl) ⟨705383, by rfl⟩ : syracuseStep 940511 = 1410767) B1410767
theorem B3562015 : Blo 936583 3562015 := bstep (se 1 (by rfl) ⟨2671511, by rfl⟩ : syracuseStep 3562015 = 5343023) B5343023
theorem B3172121 : Blo 936583 3172121 := bstep (se 2 (by rfl) ⟨1189545, by rfl⟩ : syracuseStep 3172121 = 2379091) B2379091
theorem B1405439 : Blo 936583 1405439 := bstep (se 1 (by rfl) ⟨1054079, by rfl⟩ : syracuseStep 1405439 = 2108159) B2108159
theorem B78051377 : Blo 936583 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B1408103 : Blo 936583 1408103 := bstep (se 1 (by rfl) ⟨1056077, by rfl⟩ : syracuseStep 1408103 = 2112155) B2112155
theorem B6421913 : Blo 936583 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B1409705 : Blo 936583 1409705 := bstep (se 2 (by rfl) ⟨528639, by rfl⟩ : syracuseStep 1409705 = 1057279) B1057279
theorem B4752431 : Blo 936583 4752431 := bstep (se 1 (by rfl) ⟨3564323, by rfl⟩ : syracuseStep 4752431 = 7128647) B7128647
theorem B1410425 : Blo 936583 1410425 := bstep (se 2 (by rfl) ⟨528909, by rfl⟩ : syracuseStep 1410425 = 1057819) B1057819
theorem B5704687 : Blo 936583 5704687 := bstep (se 1 (by rfl) ⟨4278515, by rfl⟩ : syracuseStep 5704687 = 8557031) B8557031
theorem B10162169 : Blo 936583 10162169 := bstep (se 2 (by rfl) ⟨3810813, by rfl⟩ : syracuseStep 10162169 = 7621627) B7621627
theorem B4755671 : Blo 936583 4755671 := bstep (se 1 (by rfl) ⟨3566753, by rfl⟩ : syracuseStep 4755671 = 7133507) B7133507
theorem B1187455 : Blo 936583 1187455 := bstep (se 1 (by rfl) ⟨890591, by rfl⟩ : syracuseStep 1187455 = 1781183) B1781183
theorem B22814783 : Blo 936583 22814783 := bstep (se 1 (by rfl) ⟨17111087, by rfl⟩ : syracuseStep 22814783 = 34222175) B34222175
theorem B1404576625 : Blo 936583 1404576625 := bstep (se 2 (by rfl) ⟨526716234, by rfl⟩ : syracuseStep 1404576625 = 1053432469) B1053432469
theorem B3162185 : Blo 936583 3162185 := bstep (se 2 (by rfl) ⟨1185819, by rfl⟩ : syracuseStep 3162185 = 2371639) B2371639
theorem B2114747 : Blo 936583 2114747 := bstep (se 1 (by rfl) ⟨1586060, by rfl⟩ : syracuseStep 2114747 = 3172121) B3172121
theorem B936959 : Blo 936583 936959 := bstep (se 1 (by rfl) ⟨702719, by rfl⟩ : syracuseStep 936959 = 1405439) B1405439
theorem B6016027 : Blo 936583 6016027 := bstep (se 1 (by rfl) ⟨4512020, by rfl⟩ : syracuseStep 6016027 = 9024041) B9024041
theorem B938735 : Blo 936583 938735 := bstep (se 1 (by rfl) ⟨704051, by rfl⟩ : syracuseStep 938735 = 1408103) B1408103
theorem B4281275 : Blo 936583 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B30922175 : Blo 936583 30922175 := bstep (se 1 (by rfl) ⟨23191631, by rfl⟩ : syracuseStep 30922175 = 46383263) B46383263
theorem B7231081 : Blo 936583 7231081 := bstep (se 2 (by rfl) ⟨2711655, by rfl⟩ : syracuseStep 7231081 = 5423311) B5423311
theorem B4512943 : Blo 936583 4512943 := bstep (se 1 (by rfl) ⟨3384707, by rfl⟩ : syracuseStep 4512943 = 6769415) B6769415
theorem B4742711 : Blo 936583 4742711 := bstep (se 1 (by rfl) ⟨3557033, by rfl⟩ : syracuseStep 4742711 = 7114067) B7114067
theorem B2253359 : Blo 936583 2253359 := bstep (se 1 (by rfl) ⟨1690019, by rfl⟩ : syracuseStep 2253359 = 3380039) B3380039
theorem B4288153 : Blo 936583 4288153 := bstep (se 2 (by rfl) ⟨1608057, by rfl⟩ : syracuseStep 4288153 = 3216115) B3216115
theorem B13529375 : Blo 936583 13529375 := bstep (se 1 (by rfl) ⟨10147031, by rfl⟩ : syracuseStep 13529375 = 20294063) B20294063
theorem B1406111 : Blo 936583 1406111 := bstep (se 1 (by rfl) ⟨1054583, by rfl⟩ : syracuseStep 1406111 = 2109167) B2109167
theorem B4749353 : Blo 936583 4749353 := bstep (se 2 (by rfl) ⟨1781007, by rfl⟩ : syracuseStep 4749353 = 3562015) B3562015
theorem B1407359 : Blo 936583 1407359 := bstep (se 1 (by rfl) ⟨1055519, by rfl⟩ : syracuseStep 1407359 = 2111039) B2111039
theorem B1407599 : Blo 936583 1407599 := bstep (se 1 (by rfl) ⟨1055699, by rfl⟩ : syracuseStep 1407599 = 2111399) B2111399
theorem B52034251 : Blo 936583 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B1408871 : Blo 936583 1408871 := bstep (se 1 (by rfl) ⟨1056653, by rfl⟩ : syracuseStep 1408871 = 2113307) B2113307
theorem B1409831 : Blo 936583 1409831 := bstep (se 1 (by rfl) ⟨1057373, by rfl⟩ : syracuseStep 1409831 = 2114747) B2114747
theorem B20614783 : Blo 936583 20614783 := bstep (se 1 (by rfl) ⟨15461087, by rfl⟩ : syracuseStep 20614783 = 30922175) B30922175
theorem B15209855 : Blo 936583 15209855 := bstep (se 1 (by rfl) ⟨11407391, by rfl⟩ : syracuseStep 15209855 = 22814783) B22814783
theorem B9641441 : Blo 936583 9641441 := bstep (se 2 (by rfl) ⟨3615540, by rfl⟩ : syracuseStep 9641441 = 7231081) B7231081
theorem B9019583 : Blo 936583 9019583 := bstep (se 1 (by rfl) ⟨6764687, by rfl⟩ : syracuseStep 9019583 = 13529375) B13529375
theorem B69379001 : Blo 936583 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B1583273 : Blo 936583 1583273 := bstep (se 2 (by rfl) ⟨593727, by rfl⟩ : syracuseStep 1583273 = 1187455) B1187455
theorem B2108123 : Blo 936583 2108123 := bstep (se 1 (by rfl) ⟨1581092, by rfl⟩ : syracuseStep 2108123 = 3162185) B3162185
theorem B1872768833 : Blo 936583 1872768833 := bstep (se 2 (by rfl) ⟨702288312, by rfl⟩ : syracuseStep 1872768833 = 1404576625) B1404576625
theorem B11416733 : Blo 936583 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B5717537 : Blo 936583 5717537 := bstep (se 2 (by rfl) ⟨2144076, by rfl⟩ : syracuseStep 5717537 = 4288153) B4288153
theorem B3161807 : Blo 936583 3161807 := bstep (se 1 (by rfl) ⟨2371355, by rfl⟩ : syracuseStep 3161807 = 4742711) B4742711
theorem B30424997 : Blo 936583 30424997 := bstep (se 4 (by rfl) ⟨2852343, by rfl⟩ : syracuseStep 30424997 = 5704687) B5704687
theorem B937407 : Blo 936583 937407 := bstep (se 1 (by rfl) ⟨703055, by rfl⟩ : syracuseStep 937407 = 1406111) B1406111
theorem B3166235 : Blo 936583 3166235 := bstep (se 1 (by rfl) ⟨2374676, by rfl⟩ : syracuseStep 3166235 = 4749353) B4749353
theorem B6017257 : Blo 936583 6017257 := bstep (se 2 (by rfl) ⟨2256471, by rfl⟩ : syracuseStep 6017257 = 4512943) B4512943
theorem B938239 : Blo 936583 938239 := bstep (se 1 (by rfl) ⟨703679, by rfl⟩ : syracuseStep 938239 = 1407359) B1407359
theorem B938399 : Blo 936583 938399 := bstep (se 1 (by rfl) ⟨703799, by rfl⟩ : syracuseStep 938399 = 1407599) B1407599
theorem B939247 : Blo 936583 939247 := bstep (se 1 (by rfl) ⟨704435, by rfl⟩ : syracuseStep 939247 = 1408871) B1408871
theorem B939803 : Blo 936583 939803 := bstep (se 1 (by rfl) ⟨704852, by rfl⟩ : syracuseStep 939803 = 1409705) B1409705
theorem B3168287 : Blo 936583 3168287 := bstep (se 1 (by rfl) ⟨2376215, by rfl⟩ : syracuseStep 3168287 = 4752431) B4752431
theorem B940283 : Blo 936583 940283 := bstep (se 1 (by rfl) ⟨705212, by rfl⟩ : syracuseStep 940283 = 1410425) B1410425
theorem B6774779 : Blo 936583 6774779 := bstep (se 1 (by rfl) ⟨5081084, by rfl⟩ : syracuseStep 6774779 = 10162169) B10162169
theorem B3170447 : Blo 936583 3170447 := bstep (se 1 (by rfl) ⟨2377835, by rfl⟩ : syracuseStep 3170447 = 4755671) B4755671
theorem B8021369 : Blo 936583 8021369 := bstep (se 2 (by rfl) ⟨3008013, by rfl⟩ : syracuseStep 8021369 = 6016027) B6016027
theorem B1502239 : Blo 936583 1502239 := bstep (se 1 (by rfl) ⟨1126679, by rfl⟩ : syracuseStep 1502239 = 2253359) B2253359
theorem B2002985 : Blo 936583 2002985 := bstep (se 2 (by rfl) ⟨751119, by rfl⟩ : syracuseStep 2002985 = 1502239) B1502239
theorem B5347579 : Blo 936583 5347579 := bstep (se 1 (by rfl) ⟨4010684, by rfl⟩ : syracuseStep 5347579 = 8021369) B8021369
theorem B1055515 : Blo 936583 1055515 := bstep (se 1 (by rfl) ⟨791636, by rfl⟩ : syracuseStep 1055515 = 1583273) B1583273
theorem B7611155 : Blo 936583 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B3811691 : Blo 936583 3811691 := bstep (se 1 (by rfl) ⟨2858768, by rfl⟩ : syracuseStep 3811691 = 5717537) B5717537
theorem B2107871 : Blo 936583 2107871 := bstep (se 1 (by rfl) ⟨1580903, by rfl⟩ : syracuseStep 2107871 = 3161807) B3161807
theorem B18066077 : Blo 936583 18066077 := bstep (se 3 (by rfl) ⟨3387389, by rfl⟩ : syracuseStep 18066077 = 6774779) B6774779
theorem B2110823 : Blo 936583 2110823 := bstep (se 1 (by rfl) ⟨1583117, by rfl⟩ : syracuseStep 2110823 = 3166235) B3166235
theorem B10139903 : Blo 936583 10139903 := bstep (se 1 (by rfl) ⟨7604927, by rfl⟩ : syracuseStep 10139903 = 15209855) B15209855
theorem B2112191 : Blo 936583 2112191 := bstep (se 1 (by rfl) ⟨1584143, by rfl⟩ : syracuseStep 2112191 = 3168287) B3168287
theorem B2113631 : Blo 936583 2113631 := bstep (se 1 (by rfl) ⟨1585223, by rfl⟩ : syracuseStep 2113631 = 3170447) B3170447
theorem B6013055 : Blo 936583 6013055 := bstep (se 1 (by rfl) ⟨4509791, by rfl⟩ : syracuseStep 6013055 = 9019583) B9019583
theorem B46252667 : Blo 936583 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B1248512555 : Blo 936583 1248512555 := bstep (se 1 (by rfl) ⟨936384416, by rfl⟩ : syracuseStep 1248512555 = 1872768833) B1872768833
theorem B25710509 : Blo 936583 25710509 := bstep (se 3 (by rfl) ⟨4820720, by rfl⟩ : syracuseStep 25710509 = 9641441) B9641441
theorem B939887 : Blo 936583 939887 := bstep (se 1 (by rfl) ⟨704915, by rfl⟩ : syracuseStep 939887 = 1409831) B1409831
theorem B27486377 : Blo 936583 27486377 := bstep (se 2 (by rfl) ⟨10307391, by rfl⟩ : syracuseStep 27486377 = 20614783) B20614783
theorem B8023009 : Blo 936583 8023009 := bstep (se 2 (by rfl) ⟨3008628, by rfl⟩ : syracuseStep 8023009 = 6017257) B6017257
theorem B1405415 : Blo 936583 1405415 := bstep (se 1 (by rfl) ⟨1054061, by rfl⟩ : syracuseStep 1405415 = 2108123) B2108123
theorem B81133325 : Blo 936583 81133325 := bstep (se 3 (by rfl) ⟨15212498, by rfl⟩ : syracuseStep 81133325 = 30424997) B30424997
theorem B1409087 : Blo 936583 1409087 := bstep (se 1 (by rfl) ⟨1056815, by rfl⟩ : syracuseStep 1409087 = 2113631) B2113631
theorem B123340445 : Blo 936583 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B832341703 : Blo 936583 832341703 := bstep (se 1 (by rfl) ⟨624256277, by rfl⟩ : syracuseStep 832341703 = 1248512555) B1248512555
theorem B17140339 : Blo 936583 17140339 := bstep (se 1 (by rfl) ⟨12855254, by rfl⟩ : syracuseStep 17140339 = 25710509) B25710509
theorem B18324251 : Blo 936583 18324251 := bstep (se 1 (by rfl) ⟨13743188, by rfl⟩ : syracuseStep 18324251 = 27486377) B27486377
theorem B6759935 : Blo 936583 6759935 := bstep (se 1 (by rfl) ⟨5069951, by rfl⟩ : syracuseStep 6759935 = 10139903) B10139903
theorem B4008703 : Blo 936583 4008703 := bstep (se 1 (by rfl) ⟨3006527, by rfl⟩ : syracuseStep 4008703 = 6013055) B6013055
theorem B10697345 : Blo 936583 10697345 := bstep (se 2 (by rfl) ⟨4011504, by rfl⟩ : syracuseStep 10697345 = 8023009) B8023009
theorem B2541127 : Blo 936583 2541127 := bstep (se 1 (by rfl) ⟨1905845, by rfl⟩ : syracuseStep 2541127 = 3811691) B3811691
theorem B12044051 : Blo 936583 12044051 := bstep (se 1 (by rfl) ⟨9033038, by rfl⟩ : syracuseStep 12044051 = 18066077) B18066077
theorem B936943 : Blo 936583 936943 := bstep (se 1 (by rfl) ⟨702707, by rfl⟩ : syracuseStep 936943 = 1405415) B1405415
theorem B7130105 : Blo 936583 7130105 := bstep (se 2 (by rfl) ⟨2673789, by rfl⟩ : syracuseStep 7130105 = 5347579) B5347579
theorem B54088883 : Blo 936583 54088883 := bstep (se 1 (by rfl) ⟨40566662, by rfl⟩ : syracuseStep 54088883 = 81133325) B81133325
theorem B1335323 : Blo 936583 1335323 := bstep (se 1 (by rfl) ⟨1001492, by rfl⟩ : syracuseStep 1335323 = 2002985) B2002985
theorem B5074103 : Blo 936583 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B1405247 : Blo 936583 1405247 := bstep (se 1 (by rfl) ⟨1053935, by rfl⟩ : syracuseStep 1405247 = 2107871) B2107871
theorem B1407215 : Blo 936583 1407215 := bstep (se 1 (by rfl) ⟨1055411, by rfl⟩ : syracuseStep 1407215 = 2110823) B2110823
theorem B1407353 : Blo 936583 1407353 := bstep (se 2 (by rfl) ⟨527757, by rfl⟩ : syracuseStep 1407353 = 1055515) B1055515
theorem B1408127 : Blo 936583 1408127 := bstep (se 1 (by rfl) ⟨1056095, by rfl⟩ : syracuseStep 1408127 = 2112191) B2112191
theorem B8029367 : Blo 936583 8029367 := bstep (se 1 (by rfl) ⟨6022025, by rfl⟩ : syracuseStep 8029367 = 12044051) B12044051
theorem B4753403 : Blo 936583 4753403 := bstep (se 1 (by rfl) ⟨3565052, by rfl⟩ : syracuseStep 4753403 = 7130105) B7130105
theorem B1109788937 : Blo 936583 1109788937 := bstep (se 2 (by rfl) ⟨416170851, by rfl⟩ : syracuseStep 1109788937 = 832341703) B832341703
theorem B5344937 : Blo 936583 5344937 := bstep (se 2 (by rfl) ⟨2004351, by rfl⟩ : syracuseStep 5344937 = 4008703) B4008703
theorem B3382735 : Blo 936583 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B82226963 : Blo 936583 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B3388169 : Blo 936583 3388169 := bstep (se 2 (by rfl) ⟨1270563, by rfl⟩ : syracuseStep 3388169 = 2541127) B2541127
theorem B36059255 : Blo 936583 36059255 := bstep (se 1 (by rfl) ⟨27044441, by rfl⟩ : syracuseStep 36059255 = 54088883) B54088883
theorem B22853785 : Blo 936583 22853785 := bstep (se 2 (by rfl) ⟨8570169, by rfl⟩ : syracuseStep 22853785 = 17140339) B17140339
theorem B4506623 : Blo 936583 4506623 := bstep (se 1 (by rfl) ⟨3379967, by rfl⟩ : syracuseStep 4506623 = 6759935) B6759935
theorem B936831 : Blo 936583 936831 := bstep (se 1 (by rfl) ⟨702623, by rfl⟩ : syracuseStep 936831 = 1405247) B1405247
theorem B938143 : Blo 936583 938143 := bstep (se 1 (by rfl) ⟨703607, by rfl⟩ : syracuseStep 938143 = 1407215) B1407215
theorem B938235 : Blo 936583 938235 := bstep (se 1 (by rfl) ⟨703676, by rfl⟩ : syracuseStep 938235 = 1407353) B1407353
theorem B7131563 : Blo 936583 7131563 := bstep (se 1 (by rfl) ⟨5348672, by rfl⟩ : syracuseStep 7131563 = 10697345) B10697345
theorem B938751 : Blo 936583 938751 := bstep (se 1 (by rfl) ⟨704063, by rfl⟩ : syracuseStep 938751 = 1408127) B1408127
theorem B939391 : Blo 936583 939391 := bstep (se 1 (by rfl) ⟨704543, by rfl⟩ : syracuseStep 939391 = 1409087) B1409087
theorem B3560861 : Blo 936583 3560861 := bstep (se 3 (by rfl) ⟨667661, by rfl⟩ : syracuseStep 3560861 = 1335323) B1335323
theorem B12216167 : Blo 936583 12216167 := bstep (se 1 (by rfl) ⟨9162125, by rfl⟩ : syracuseStep 12216167 = 18324251) B18324251
theorem B4754375 : Blo 936583 4754375 := bstep (se 1 (by rfl) ⟨3565781, by rfl⟩ : syracuseStep 4754375 = 7131563) B7131563
theorem B5352911 : Blo 936583 5352911 := bstep (se 1 (by rfl) ⟨4014683, by rfl⟩ : syracuseStep 5352911 = 8029367) B8029367
theorem B2373907 : Blo 936583 2373907 := bstep (se 1 (by rfl) ⟨1780430, by rfl⟩ : syracuseStep 2373907 = 3560861) B3560861
theorem B8144111 : Blo 936583 8144111 := bstep (se 1 (by rfl) ⟨6108083, by rfl⟩ : syracuseStep 8144111 = 12216167) B12216167
theorem B24039503 : Blo 936583 24039503 := bstep (se 1 (by rfl) ⟨18029627, by rfl⟩ : syracuseStep 24039503 = 36059255) B36059255
theorem B4510313 : Blo 936583 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B3004415 : Blo 936583 3004415 := bstep (se 1 (by rfl) ⟨2253311, by rfl⟩ : syracuseStep 3004415 = 4506623) B4506623
theorem B3168935 : Blo 936583 3168935 := bstep (se 1 (by rfl) ⟨2376701, by rfl⟩ : syracuseStep 3168935 = 4753403) B4753403
theorem B739859291 : Blo 936583 739859291 := bstep (se 1 (by rfl) ⟨554894468, by rfl⟩ : syracuseStep 739859291 = 1109788937) B1109788937
theorem B3563291 : Blo 936583 3563291 := bstep (se 1 (by rfl) ⟨2672468, by rfl⟩ : syracuseStep 3563291 = 5344937) B5344937
theorem B54817975 : Blo 936583 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B30471713 : Blo 936583 30471713 := bstep (se 2 (by rfl) ⟨11426892, by rfl⟩ : syracuseStep 30471713 = 22853785) B22853785
theorem B2258779 : Blo 936583 2258779 := bstep (se 1 (by rfl) ⟨1694084, by rfl⟩ : syracuseStep 2258779 = 3388169) B3388169
theorem B16026335 : Blo 936583 16026335 := bstep (se 1 (by rfl) ⟨12019751, by rfl⟩ : syracuseStep 16026335 = 24039503) B24039503
theorem B2002943 : Blo 936583 2002943 := bstep (se 1 (by rfl) ⟨1502207, by rfl⟩ : syracuseStep 2002943 = 3004415) B3004415
theorem B2112623 : Blo 936583 2112623 := bstep (se 1 (by rfl) ⟨1584467, by rfl⟩ : syracuseStep 2112623 = 3168935) B3168935
theorem B493239527 : Blo 936583 493239527 := bstep (se 1 (by rfl) ⟨369929645, by rfl⟩ : syracuseStep 493239527 = 739859291) B739859291
theorem B2375527 : Blo 936583 2375527 := bstep (se 1 (by rfl) ⟨1781645, by rfl⟩ : syracuseStep 2375527 = 3563291) B3563291
theorem B73090633 : Blo 936583 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B3165209 : Blo 936583 3165209 := bstep (se 2 (by rfl) ⟨1186953, by rfl⟩ : syracuseStep 3165209 = 2373907) B2373907
theorem B3169583 : Blo 936583 3169583 := bstep (se 1 (by rfl) ⟨2377187, by rfl⟩ : syracuseStep 3169583 = 4754375) B4754375
theorem B3006875 : Blo 936583 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B21717629 : Blo 936583 21717629 := bstep (se 3 (by rfl) ⟨4072055, by rfl⟩ : syracuseStep 21717629 = 8144111) B8144111
theorem B3568607 : Blo 936583 3568607 := bstep (se 1 (by rfl) ⟨2676455, by rfl⟩ : syracuseStep 3568607 = 5352911) B5352911
theorem B3011705 : Blo 936583 3011705 := bstep (se 2 (by rfl) ⟨1129389, by rfl⟩ : syracuseStep 3011705 = 2258779) B2258779
theorem B20314475 : Blo 936583 20314475 := bstep (se 1 (by rfl) ⟨15235856, by rfl⟩ : syracuseStep 20314475 = 30471713) B30471713
theorem B10684223 : Blo 936583 10684223 := bstep (se 1 (by rfl) ⟨8013167, by rfl⟩ : syracuseStep 10684223 = 16026335) B16026335
theorem B97454177 : Blo 936583 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B2004583 : Blo 936583 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B2007803 : Blo 936583 2007803 := bstep (se 1 (by rfl) ⟨1505852, by rfl⟩ : syracuseStep 2007803 = 3011705) B3011705
theorem B13542983 : Blo 936583 13542983 := bstep (se 1 (by rfl) ⟨10157237, by rfl⟩ : syracuseStep 13542983 = 20314475) B20314475
theorem B2110139 : Blo 936583 2110139 := bstep (se 1 (by rfl) ⟨1582604, by rfl⟩ : syracuseStep 2110139 = 3165209) B3165209
theorem B2113055 : Blo 936583 2113055 := bstep (se 1 (by rfl) ⟨1584791, by rfl⟩ : syracuseStep 2113055 = 3169583) B3169583
theorem B2379071 : Blo 936583 2379071 := bstep (se 1 (by rfl) ⟨1784303, by rfl⟩ : syracuseStep 2379071 = 3568607) B3568607
theorem B3167369 : Blo 936583 3167369 := bstep (se 2 (by rfl) ⟨1187763, by rfl⟩ : syracuseStep 3167369 = 2375527) B2375527
theorem B1335295 : Blo 936583 1335295 := bstep (se 1 (by rfl) ⟨1001471, by rfl⟩ : syracuseStep 1335295 = 2002943) B2002943
theorem B14478419 : Blo 936583 14478419 := bstep (se 1 (by rfl) ⟨10858814, by rfl⟩ : syracuseStep 14478419 = 21717629) B21717629
theorem B1408415 : Blo 936583 1408415 := bstep (se 1 (by rfl) ⟨1056311, by rfl⟩ : syracuseStep 1408415 = 2112623) B2112623
theorem B328826351 : Blo 936583 328826351 := bstep (se 1 (by rfl) ⟨246619763, by rfl⟩ : syracuseStep 328826351 = 493239527) B493239527
theorem B1780393 : Blo 936583 1780393 := bstep (se 2 (by rfl) ⟨667647, by rfl⟩ : syracuseStep 1780393 = 1335295) B1335295
theorem B7122815 : Blo 936583 7122815 := bstep (se 1 (by rfl) ⟨5342111, by rfl⟩ : syracuseStep 7122815 = 10684223) B10684223
theorem B1586047 : Blo 936583 1586047 := bstep (se 1 (by rfl) ⟨1189535, by rfl⟩ : syracuseStep 1586047 = 2379071) B2379071
theorem B2111579 : Blo 936583 2111579 := bstep (se 1 (by rfl) ⟨1583684, by rfl⟩ : syracuseStep 2111579 = 3167369) B3167369
theorem B9028655 : Blo 936583 9028655 := bstep (se 1 (by rfl) ⟨6771491, by rfl⟩ : syracuseStep 9028655 = 13542983) B13542983
theorem B9652279 : Blo 936583 9652279 := bstep (se 1 (by rfl) ⟨7239209, by rfl⟩ : syracuseStep 9652279 = 14478419) B14478419
theorem B2672777 : Blo 936583 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B938943 : Blo 936583 938943 := bstep (se 1 (by rfl) ⟨704207, by rfl⟩ : syracuseStep 938943 = 1408415) B1408415
theorem B64969451 : Blo 936583 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B1338535 : Blo 936583 1338535 := bstep (se 1 (by rfl) ⟨1003901, by rfl⟩ : syracuseStep 1338535 = 2007803) B2007803
theorem B1406759 : Blo 936583 1406759 := bstep (se 1 (by rfl) ⟨1055069, by rfl⟩ : syracuseStep 1406759 = 2110139) B2110139
theorem B876870269 : Blo 936583 876870269 := bstep (se 3 (by rfl) ⟨164413175, by rfl⟩ : syracuseStep 876870269 = 328826351) B328826351
theorem B1408703 : Blo 936583 1408703 := bstep (se 1 (by rfl) ⟨1056527, by rfl⟩ : syracuseStep 1408703 = 2113055) B2113055
theorem B1781851 : Blo 936583 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B2373857 : Blo 936583 2373857 := bstep (se 2 (by rfl) ⟨890196, by rfl⟩ : syracuseStep 2373857 = 1780393) B1780393
theorem B2114729 : Blo 936583 2114729 := bstep (se 2 (by rfl) ⟨793023, by rfl⟩ : syracuseStep 2114729 = 1586047) B1586047
theorem B937839 : Blo 936583 937839 := bstep (se 1 (by rfl) ⟨703379, by rfl⟩ : syracuseStep 937839 = 1406759) B1406759
theorem B939135 : Blo 936583 939135 := bstep (se 1 (by rfl) ⟨704351, by rfl⟩ : syracuseStep 939135 = 1408703) B1408703
theorem B6019103 : Blo 936583 6019103 := bstep (se 1 (by rfl) ⟨4514327, by rfl⟩ : syracuseStep 6019103 = 9028655) B9028655
theorem B12869705 : Blo 936583 12869705 := bstep (se 2 (by rfl) ⟨4826139, by rfl⟩ : syracuseStep 12869705 = 9652279) B9652279
theorem B43312967 : Blo 936583 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B7138853 : Blo 936583 7138853 := bstep (se 4 (by rfl) ⟨669267, by rfl⟩ : syracuseStep 7138853 = 1338535) B1338535
theorem B4748543 : Blo 936583 4748543 := bstep (se 1 (by rfl) ⟨3561407, by rfl⟩ : syracuseStep 4748543 = 7122815) B7122815
theorem B1407719 : Blo 936583 1407719 := bstep (se 1 (by rfl) ⟨1055789, by rfl⟩ : syracuseStep 1407719 = 2111579) B2111579
theorem B584580179 : Blo 936583 584580179 := bstep (se 1 (by rfl) ⟨438435134, by rfl⟩ : syracuseStep 584580179 = 876870269) B876870269
theorem B1409819 : Blo 936583 1409819 := bstep (se 1 (by rfl) ⟨1057364, by rfl⟩ : syracuseStep 1409819 = 2114729) B2114729
theorem B28875311 : Blo 936583 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B4759235 : Blo 936583 4759235 := bstep (se 1 (by rfl) ⟨3569426, by rfl⟩ : syracuseStep 4759235 = 7138853) B7138853
theorem B1582571 : Blo 936583 1582571 := bstep (se 1 (by rfl) ⟨1186928, by rfl⟩ : syracuseStep 1582571 = 2373857) B2373857
theorem B389720119 : Blo 936583 389720119 := bstep (se 1 (by rfl) ⟨292290089, by rfl⟩ : syracuseStep 389720119 = 584580179) B584580179
theorem B4012735 : Blo 936583 4012735 := bstep (se 1 (by rfl) ⟨3009551, by rfl⟩ : syracuseStep 4012735 = 6019103) B6019103
theorem B2375801 : Blo 936583 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B3165695 : Blo 936583 3165695 := bstep (se 1 (by rfl) ⟨2374271, by rfl⟩ : syracuseStep 3165695 = 4748543) B4748543
theorem B938479 : Blo 936583 938479 := bstep (se 1 (by rfl) ⟨703859, by rfl⟩ : syracuseStep 938479 = 1407719) B1407719
theorem B8579803 : Blo 936583 8579803 := bstep (se 1 (by rfl) ⟨6434852, by rfl⟩ : syracuseStep 8579803 = 12869705) B12869705
theorem B11439737 : Blo 936583 11439737 := bstep (se 2 (by rfl) ⟨4289901, by rfl⟩ : syracuseStep 11439737 = 8579803) B8579803
theorem B1055047 : Blo 936583 1055047 := bstep (se 1 (by rfl) ⟨791285, by rfl⟩ : syracuseStep 1055047 = 1582571) B1582571
theorem B5350313 : Blo 936583 5350313 := bstep (se 2 (by rfl) ⟨2006367, by rfl⟩ : syracuseStep 5350313 = 4012735) B4012735
theorem B1583867 : Blo 936583 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B2110463 : Blo 936583 2110463 := bstep (se 1 (by rfl) ⟨1582847, by rfl⟩ : syracuseStep 2110463 = 3165695) B3165695
theorem B19250207 : Blo 936583 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B939879 : Blo 936583 939879 := bstep (se 1 (by rfl) ⟨704909, by rfl⟩ : syracuseStep 939879 = 1409819) B1409819
theorem B519626825 : Blo 936583 519626825 := bstep (se 2 (by rfl) ⟨194860059, by rfl⟩ : syracuseStep 519626825 = 389720119) B389720119
theorem B3172823 : Blo 936583 3172823 := bstep (se 1 (by rfl) ⟨2379617, by rfl⟩ : syracuseStep 3172823 = 4759235) B4759235
theorem B1055911 : Blo 936583 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B2115215 : Blo 936583 2115215 := bstep (se 1 (by rfl) ⟨1586411, by rfl⟩ : syracuseStep 2115215 = 3172823) B3172823
theorem B12833471 : Blo 936583 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B7626491 : Blo 936583 7626491 := bstep (se 1 (by rfl) ⟨5719868, by rfl⟩ : syracuseStep 7626491 = 11439737) B11439737
theorem B346417883 : Blo 936583 346417883 := bstep (se 1 (by rfl) ⟨259813412, by rfl⟩ : syracuseStep 346417883 = 519626825) B519626825
theorem B3566875 : Blo 936583 3566875 := bstep (se 1 (by rfl) ⟨2675156, by rfl⟩ : syracuseStep 3566875 = 5350313) B5350313
theorem B1406729 : Blo 936583 1406729 := bstep (se 2 (by rfl) ⟨527523, by rfl⟩ : syracuseStep 1406729 = 1055047) B1055047
theorem B1406975 : Blo 936583 1406975 := bstep (se 1 (by rfl) ⟨1055231, by rfl⟩ : syracuseStep 1406975 = 2110463) B2110463
theorem B1410143 : Blo 936583 1410143 := bstep (se 1 (by rfl) ⟨1057607, by rfl⟩ : syracuseStep 1410143 = 2115215) B2115215
theorem B8555647 : Blo 936583 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B4755833 : Blo 936583 4755833 := bstep (se 2 (by rfl) ⟨1783437, by rfl⟩ : syracuseStep 4755833 = 3566875) B3566875
theorem B5084327 : Blo 936583 5084327 := bstep (se 1 (by rfl) ⟨3813245, by rfl⟩ : syracuseStep 5084327 = 7626491) B7626491
theorem B937819 : Blo 936583 937819 := bstep (se 1 (by rfl) ⟨703364, by rfl⟩ : syracuseStep 937819 = 1406729) B1406729
theorem B937983 : Blo 936583 937983 := bstep (se 1 (by rfl) ⟨703487, by rfl⟩ : syracuseStep 937983 = 1406975) B1406975
theorem B230945255 : Blo 936583 230945255 := bstep (se 1 (by rfl) ⟨173208941, by rfl⟩ : syracuseStep 230945255 = 346417883) B346417883
theorem B1407881 : Blo 936583 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B11407529 : Blo 936583 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B153963503 : Blo 936583 153963503 := bstep (se 1 (by rfl) ⟨115472627, by rfl⟩ : syracuseStep 153963503 = 230945255) B230945255
theorem B938587 : Blo 936583 938587 := bstep (se 1 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 938587 = 1407881) B1407881
theorem B940095 : Blo 936583 940095 := bstep (se 1 (by rfl) ⟨705071, by rfl⟩ : syracuseStep 940095 = 1410143) B1410143
theorem B3170555 : Blo 936583 3170555 := bstep (se 1 (by rfl) ⟨2377916, by rfl⟩ : syracuseStep 3170555 = 4755833) B4755833
theorem B13558205 : Blo 936583 13558205 := bstep (se 3 (by rfl) ⟨2542163, by rfl⟩ : syracuseStep 13558205 = 5084327) B5084327
theorem B7605019 : Blo 936583 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B102642335 : Blo 936583 102642335 := bstep (se 1 (by rfl) ⟨76981751, by rfl⟩ : syracuseStep 102642335 = 153963503) B153963503
theorem B2113703 : Blo 936583 2113703 := bstep (se 1 (by rfl) ⟨1585277, by rfl⟩ : syracuseStep 2113703 = 3170555) B3170555
theorem B9038803 : Blo 936583 9038803 := bstep (se 1 (by rfl) ⟨6779102, by rfl⟩ : syracuseStep 9038803 = 13558205) B13558205
theorem B1409135 : Blo 936583 1409135 := bstep (se 1 (by rfl) ⟨1056851, by rfl⟩ : syracuseStep 1409135 = 2113703) B2113703
theorem B68428223 : Blo 936583 68428223 := bstep (se 1 (by rfl) ⟨51321167, by rfl⟩ : syracuseStep 68428223 = 102642335) B102642335
theorem B12051737 : Blo 936583 12051737 := bstep (se 2 (by rfl) ⟨4519401, by rfl⟩ : syracuseStep 12051737 = 9038803) B9038803
theorem B40560101 : Blo 936583 40560101 := bstep (se 4 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 40560101 = 7605019) B7605019
theorem B45618815 : Blo 936583 45618815 := bstep (se 1 (by rfl) ⟨34214111, by rfl⟩ : syracuseStep 45618815 = 68428223) B68428223
theorem B8034491 : Blo 936583 8034491 := bstep (se 1 (by rfl) ⟨6025868, by rfl⟩ : syracuseStep 8034491 = 12051737) B12051737
theorem B27040067 : Blo 936583 27040067 := bstep (se 1 (by rfl) ⟨20280050, by rfl⟩ : syracuseStep 27040067 = 40560101) B40560101
theorem B939423 : Blo 936583 939423 := bstep (se 1 (by rfl) ⟨704567, by rfl⟩ : syracuseStep 939423 = 1409135) B1409135
theorem B30412543 : Blo 936583 30412543 := bstep (se 1 (by rfl) ⟨22809407, by rfl⟩ : syracuseStep 30412543 = 45618815) B45618815
theorem B18026711 : Blo 936583 18026711 := bstep (se 1 (by rfl) ⟨13520033, by rfl⟩ : syracuseStep 18026711 = 27040067) B27040067
theorem B5356327 : Blo 936583 5356327 := bstep (se 1 (by rfl) ⟨4017245, by rfl⟩ : syracuseStep 5356327 = 8034491) B8034491
theorem B40550057 : Blo 936583 40550057 := bstep (se 2 (by rfl) ⟨15206271, by rfl⟩ : syracuseStep 40550057 = 30412543) B30412543
theorem B12017807 : Blo 936583 12017807 := bstep (se 1 (by rfl) ⟨9013355, by rfl⟩ : syracuseStep 12017807 = 18026711) B18026711
theorem B7141769 : Blo 936583 7141769 := bstep (se 2 (by rfl) ⟨2678163, by rfl⟩ : syracuseStep 7141769 = 5356327) B5356327
theorem B4761179 : Blo 936583 4761179 := bstep (se 1 (by rfl) ⟨3570884, by rfl⟩ : syracuseStep 4761179 = 7141769) B7141769
theorem B8011871 : Blo 936583 8011871 := bstep (se 1 (by rfl) ⟨6008903, by rfl⟩ : syracuseStep 8011871 = 12017807) B12017807
theorem B27033371 : Blo 936583 27033371 := bstep (se 1 (by rfl) ⟨20275028, by rfl⟩ : syracuseStep 27033371 = 40550057) B40550057
theorem B5341247 : Blo 936583 5341247 := bstep (se 1 (by rfl) ⟨4005935, by rfl⟩ : syracuseStep 5341247 = 8011871) B8011871
theorem B3174119 : Blo 936583 3174119 := bstep (se 1 (by rfl) ⟨2380589, by rfl⟩ : syracuseStep 3174119 = 4761179) B4761179
theorem B18022247 : Blo 936583 18022247 := bstep (se 1 (by rfl) ⟨13516685, by rfl⟩ : syracuseStep 18022247 = 27033371) B27033371
theorem B2116079 : Blo 936583 2116079 := bstep (se 1 (by rfl) ⟨1587059, by rfl⟩ : syracuseStep 2116079 = 3174119) B3174119
theorem B12014831 : Blo 936583 12014831 := bstep (se 1 (by rfl) ⟨9011123, by rfl⟩ : syracuseStep 12014831 = 18022247) B18022247
theorem B3560831 : Blo 936583 3560831 := bstep (se 1 (by rfl) ⟨2670623, by rfl⟩ : syracuseStep 3560831 = 5341247) B5341247
theorem B1410719 : Blo 936583 1410719 := bstep (se 1 (by rfl) ⟨1058039, by rfl⟩ : syracuseStep 1410719 = 2116079) B2116079
theorem B8009887 : Blo 936583 8009887 := bstep (se 1 (by rfl) ⟨6007415, by rfl⟩ : syracuseStep 8009887 = 12014831) B12014831
theorem B2373887 : Blo 936583 2373887 := bstep (se 1 (by rfl) ⟨1780415, by rfl⟩ : syracuseStep 2373887 = 3560831) B3560831
theorem B1582591 : Blo 936583 1582591 := bstep (se 1 (by rfl) ⟨1186943, by rfl⟩ : syracuseStep 1582591 = 2373887) B2373887
theorem B940479 : Blo 936583 940479 := bstep (se 1 (by rfl) ⟨705359, by rfl⟩ : syracuseStep 940479 = 1410719) B1410719
theorem B10679849 : Blo 936583 10679849 := bstep (se 2 (by rfl) ⟨4004943, by rfl⟩ : syracuseStep 10679849 = 8009887) B8009887
theorem B7119899 : Blo 936583 7119899 := bstep (se 1 (by rfl) ⟨5339924, by rfl⟩ : syracuseStep 7119899 = 10679849) B10679849
theorem B2110121 : Blo 936583 2110121 := bstep (se 2 (by rfl) ⟨791295, by rfl⟩ : syracuseStep 2110121 = 1582591) B1582591
theorem B4746599 : Blo 936583 4746599 := bstep (se 1 (by rfl) ⟨3559949, by rfl⟩ : syracuseStep 4746599 = 7119899) B7119899
theorem B1406747 : Blo 936583 1406747 := bstep (se 1 (by rfl) ⟨1055060, by rfl⟩ : syracuseStep 1406747 = 2110121) B2110121
theorem B3164399 : Blo 936583 3164399 := bstep (se 1 (by rfl) ⟨2373299, by rfl⟩ : syracuseStep 3164399 = 4746599) B4746599
theorem B937831 : Blo 936583 937831 := bstep (se 1 (by rfl) ⟨703373, by rfl⟩ : syracuseStep 937831 = 1406747) B1406747
theorem B2109599 : Blo 936583 2109599 := bstep (se 1 (by rfl) ⟨1582199, by rfl⟩ : syracuseStep 2109599 = 3164399) B3164399
theorem B1406399 : Blo 936583 1406399 := bstep (se 1 (by rfl) ⟨1054799, by rfl⟩ : syracuseStep 1406399 = 2109599) B2109599
theorem B937599 : Blo 936583 937599 := bstep (se 1 (by rfl) ⟨703199, by rfl⟩ : syracuseStep 937599 = 1406399) B1406399

theorem C0 (j : ℕ) (h1 : 234145 ≤ j) (h2 : j ≤ 234844) : Blo 936583 (4 * j + 3) := by
  interval_cases j
  · exact B936583
  · exact B936587
  · exact B936591
  · exact B936595
  · exact B936599
  · exact B936603
  · exact B936607
  · exact B936611
  · exact B936615
  · exact B936619
  · exact B936623
  · exact B936627
  · exact B936631
  · exact B936635
  · exact B936639
  · exact B936643
  · exact B936647
  · exact B936651
  · exact B936655
  · exact B936659
  · exact B936663
  · exact B936667
  · exact B936671
  · exact B936675
  · exact B936679
  · exact B936683
  · exact B936687
  · exact B936691
  · exact B936695
  · exact B936699
  · exact B936703
  · exact B936707
  · exact B936711
  · exact B936715
  · exact B936719
  · exact B936723
  · exact B936727
  · exact B936731
  · exact B936735
  · exact B936739
  · exact B936743
  · exact B936747
  · exact B936751
  · exact B936755
  · exact B936759
  · exact B936763
  · exact B936767
  · exact B936771
  · exact B936775
  · exact B936779
  · exact B936783
  · exact B936787
  · exact B936791
  · exact B936795
  · exact B936799
  · exact B936803
  · exact B936807
  · exact B936811
  · exact B936815
  · exact B936819
  · exact B936823
  · exact B936827
  · exact B936831
  · exact B936835
  · exact B936839
  · exact B936843
  · exact B936847
  · exact B936851
  · exact B936855
  · exact B936859
  · exact B936863
  · exact B936867
  · exact B936871
  · exact B936875
  · exact B936879
  · exact B936883
  · exact B936887
  · exact B936891
  · exact B936895
  · exact B936899
  · exact B936903
  · exact B936907
  · exact B936911
  · exact B936915
  · exact B936919
  · exact B936923
  · exact B936927
  · exact B936931
  · exact B936935
  · exact B936939
  · exact B936943
  · exact B936947
  · exact B936951
  · exact B936955
  · exact B936959
  · exact B936963
  · exact B936967
  · exact B936971
  · exact B936975
  · exact B936979
  · exact B936983
  · exact B936987
  · exact B936991
  · exact B936995
  · exact B936999
  · exact B937003
  · exact B937007
  · exact B937011
  · exact B937015
  · exact B937019
  · exact B937023
  · exact B937027
  · exact B937031
  · exact B937035
  · exact B937039
  · exact B937043
  · exact B937047
  · exact B937051
  · exact B937055
  · exact B937059
  · exact B937063
  · exact B937067
  · exact B937071
  · exact B937075
  · exact B937079
  · exact B937083
  · exact B937087
  · exact B937091
  · exact B937095
  · exact B937099
  · exact B937103
  · exact B937107
  · exact B937111
  · exact B937115
  · exact B937119
  · exact B937123
  · exact B937127
  · exact B937131
  · exact B937135
  · exact B937139
  · exact B937143
  · exact B937147
  · exact B937151
  · exact B937155
  · exact B937159
  · exact B937163
  · exact B937167
  · exact B937171
  · exact B937175
  · exact B937179
  · exact B937183
  · exact B937187
  · exact B937191
  · exact B937195
  · exact B937199
  · exact B937203
  · exact B937207
  · exact B937211
  · exact B937215
  · exact B937219
  · exact B937223
  · exact B937227
  · exact B937231
  · exact B937235
  · exact B937239
  · exact B937243
  · exact B937247
  · exact B937251
  · exact B937255
  · exact B937259
  · exact B937263
  · exact B937267
  · exact B937271
  · exact B937275
  · exact B937279
  · exact B937283
  · exact B937287
  · exact B937291
  · exact B937295
  · exact B937299
  · exact B937303
  · exact B937307
  · exact B937311
  · exact B937315
  · exact B937319
  · exact B937323
  · exact B937327
  · exact B937331
  · exact B937335
  · exact B937339
  · exact B937343
  · exact B937347
  · exact B937351
  · exact B937355
  · exact B937359
  · exact B937363
  · exact B937367
  · exact B937371
  · exact B937375
  · exact B937379
  · exact B937383
  · exact B937387
  · exact B937391
  · exact B937395
  · exact B937399
  · exact B937403
  · exact B937407
  · exact B937411
  · exact B937415
  · exact B937419
  · exact B937423
  · exact B937427
  · exact B937431
  · exact B937435
  · exact B937439
  · exact B937443
  · exact B937447
  · exact B937451
  · exact B937455
  · exact B937459
  · exact B937463
  · exact B937467
  · exact B937471
  · exact B937475
  · exact B937479
  · exact B937483
  · exact B937487
  · exact B937491
  · exact B937495
  · exact B937499
  · exact B937503
  · exact B937507
  · exact B937511
  · exact B937515
  · exact B937519
  · exact B937523
  · exact B937527
  · exact B937531
  · exact B937535
  · exact B937539
  · exact B937543
  · exact B937547
  · exact B937551
  · exact B937555
  · exact B937559
  · exact B937563
  · exact B937567
  · exact B937571
  · exact B937575
  · exact B937579
  · exact B937583
  · exact B937587
  · exact B937591
  · exact B937595
  · exact B937599
  · exact B937603
  · exact B937607
  · exact B937611
  · exact B937615
  · exact B937619
  · exact B937623
  · exact B937627
  · exact B937631
  · exact B937635
  · exact B937639
  · exact B937643
  · exact B937647
  · exact B937651
  · exact B937655
  · exact B937659
  · exact B937663
  · exact B937667
  · exact B937671
  · exact B937675
  · exact B937679
  · exact B937683
  · exact B937687
  · exact B937691
  · exact B937695
  · exact B937699
  · exact B937703
  · exact B937707
  · exact B937711
  · exact B937715
  · exact B937719
  · exact B937723
  · exact B937727
  · exact B937731
  · exact B937735
  · exact B937739
  · exact B937743
  · exact B937747
  · exact B937751
  · exact B937755
  · exact B937759
  · exact B937763
  · exact B937767
  · exact B937771
  · exact B937775
  · exact B937779
  · exact B937783
  · exact B937787
  · exact B937791
  · exact B937795
  · exact B937799
  · exact B937803
  · exact B937807
  · exact B937811
  · exact B937815
  · exact B937819
  · exact B937823
  · exact B937827
  · exact B937831
  · exact B937835
  · exact B937839
  · exact B937843
  · exact B937847
  · exact B937851
  · exact B937855
  · exact B937859
  · exact B937863
  · exact B937867
  · exact B937871
  · exact B937875
  · exact B937879
  · exact B937883
  · exact B937887
  · exact B937891
  · exact B937895
  · exact B937899
  · exact B937903
  · exact B937907
  · exact B937911
  · exact B937915
  · exact B937919
  · exact B937923
  · exact B937927
  · exact B937931
  · exact B937935
  · exact B937939
  · exact B937943
  · exact B937947
  · exact B937951
  · exact B937955
  · exact B937959
  · exact B937963
  · exact B937967
  · exact B937971
  · exact B937975
  · exact B937979
  · exact B937983
  · exact B937987
  · exact B937991
  · exact B937995
  · exact B937999
  · exact B938003
  · exact B938007
  · exact B938011
  · exact B938015
  · exact B938019
  · exact B938023
  · exact B938027
  · exact B938031
  · exact B938035
  · exact B938039
  · exact B938043
  · exact B938047
  · exact B938051
  · exact B938055
  · exact B938059
  · exact B938063
  · exact B938067
  · exact B938071
  · exact B938075
  · exact B938079
  · exact B938083
  · exact B938087
  · exact B938091
  · exact B938095
  · exact B938099
  · exact B938103
  · exact B938107
  · exact B938111
  · exact B938115
  · exact B938119
  · exact B938123
  · exact B938127
  · exact B938131
  · exact B938135
  · exact B938139
  · exact B938143
  · exact B938147
  · exact B938151
  · exact B938155
  · exact B938159
  · exact B938163
  · exact B938167
  · exact B938171
  · exact B938175
  · exact B938179
  · exact B938183
  · exact B938187
  · exact B938191
  · exact B938195
  · exact B938199
  · exact B938203
  · exact B938207
  · exact B938211
  · exact B938215
  · exact B938219
  · exact B938223
  · exact B938227
  · exact B938231
  · exact B938235
  · exact B938239
  · exact B938243
  · exact B938247
  · exact B938251
  · exact B938255
  · exact B938259
  · exact B938263
  · exact B938267
  · exact B938271
  · exact B938275
  · exact B938279
  · exact B938283
  · exact B938287
  · exact B938291
  · exact B938295
  · exact B938299
  · exact B938303
  · exact B938307
  · exact B938311
  · exact B938315
  · exact B938319
  · exact B938323
  · exact B938327
  · exact B938331
  · exact B938335
  · exact B938339
  · exact B938343
  · exact B938347
  · exact B938351
  · exact B938355
  · exact B938359
  · exact B938363
  · exact B938367
  · exact B938371
  · exact B938375
  · exact B938379
  · exact B938383
  · exact B938387
  · exact B938391
  · exact B938395
  · exact B938399
  · exact B938403
  · exact B938407
  · exact B938411
  · exact B938415
  · exact B938419
  · exact B938423
  · exact B938427
  · exact B938431
  · exact B938435
  · exact B938439
  · exact B938443
  · exact B938447
  · exact B938451
  · exact B938455
  · exact B938459
  · exact B938463
  · exact B938467
  · exact B938471
  · exact B938475
  · exact B938479
  · exact B938483
  · exact B938487
  · exact B938491
  · exact B938495
  · exact B938499
  · exact B938503
  · exact B938507
  · exact B938511
  · exact B938515
  · exact B938519
  · exact B938523
  · exact B938527
  · exact B938531
  · exact B938535
  · exact B938539
  · exact B938543
  · exact B938547
  · exact B938551
  · exact B938555
  · exact B938559
  · exact B938563
  · exact B938567
  · exact B938571
  · exact B938575
  · exact B938579
  · exact B938583
  · exact B938587
  · exact B938591
  · exact B938595
  · exact B938599
  · exact B938603
  · exact B938607
  · exact B938611
  · exact B938615
  · exact B938619
  · exact B938623
  · exact B938627
  · exact B938631
  · exact B938635
  · exact B938639
  · exact B938643
  · exact B938647
  · exact B938651
  · exact B938655
  · exact B938659
  · exact B938663
  · exact B938667
  · exact B938671
  · exact B938675
  · exact B938679
  · exact B938683
  · exact B938687
  · exact B938691
  · exact B938695
  · exact B938699
  · exact B938703
  · exact B938707
  · exact B938711
  · exact B938715
  · exact B938719
  · exact B938723
  · exact B938727
  · exact B938731
  · exact B938735
  · exact B938739
  · exact B938743
  · exact B938747
  · exact B938751
  · exact B938755
  · exact B938759
  · exact B938763
  · exact B938767
  · exact B938771
  · exact B938775
  · exact B938779
  · exact B938783
  · exact B938787
  · exact B938791
  · exact B938795
  · exact B938799
  · exact B938803
  · exact B938807
  · exact B938811
  · exact B938815
  · exact B938819
  · exact B938823
  · exact B938827
  · exact B938831
  · exact B938835
  · exact B938839
  · exact B938843
  · exact B938847
  · exact B938851
  · exact B938855
  · exact B938859
  · exact B938863
  · exact B938867
  · exact B938871
  · exact B938875
  · exact B938879
  · exact B938883
  · exact B938887
  · exact B938891
  · exact B938895
  · exact B938899
  · exact B938903
  · exact B938907
  · exact B938911
  · exact B938915
  · exact B938919
  · exact B938923
  · exact B938927
  · exact B938931
  · exact B938935
  · exact B938939
  · exact B938943
  · exact B938947
  · exact B938951
  · exact B938955
  · exact B938959
  · exact B938963
  · exact B938967
  · exact B938971
  · exact B938975
  · exact B938979
  · exact B938983
  · exact B938987
  · exact B938991
  · exact B938995
  · exact B938999
  · exact B939003
  · exact B939007
  · exact B939011
  · exact B939015
  · exact B939019
  · exact B939023
  · exact B939027
  · exact B939031
  · exact B939035
  · exact B939039
  · exact B939043
  · exact B939047
  · exact B939051
  · exact B939055
  · exact B939059
  · exact B939063
  · exact B939067
  · exact B939071
  · exact B939075
  · exact B939079
  · exact B939083
  · exact B939087
  · exact B939091
  · exact B939095
  · exact B939099
  · exact B939103
  · exact B939107
  · exact B939111
  · exact B939115
  · exact B939119
  · exact B939123
  · exact B939127
  · exact B939131
  · exact B939135
  · exact B939139
  · exact B939143
  · exact B939147
  · exact B939151
  · exact B939155
  · exact B939159
  · exact B939163
  · exact B939167
  · exact B939171
  · exact B939175
  · exact B939179
  · exact B939183
  · exact B939187
  · exact B939191
  · exact B939195
  · exact B939199
  · exact B939203
  · exact B939207
  · exact B939211
  · exact B939215
  · exact B939219
  · exact B939223
  · exact B939227
  · exact B939231
  · exact B939235
  · exact B939239
  · exact B939243
  · exact B939247
  · exact B939251
  · exact B939255
  · exact B939259
  · exact B939263
  · exact B939267
  · exact B939271
  · exact B939275
  · exact B939279
  · exact B939283
  · exact B939287
  · exact B939291
  · exact B939295
  · exact B939299
  · exact B939303
  · exact B939307
  · exact B939311
  · exact B939315
  · exact B939319
  · exact B939323
  · exact B939327
  · exact B939331
  · exact B939335
  · exact B939339
  · exact B939343
  · exact B939347
  · exact B939351
  · exact B939355
  · exact B939359
  · exact B939363
  · exact B939367
  · exact B939371
  · exact B939375
  · exact B939379

theorem C1 (j : ℕ) (h1 : 234845 ≤ j) (h2 : j ≤ 235145) : Blo 936583 (4 * j + 3) := by
  interval_cases j
  · exact B939383
  · exact B939387
  · exact B939391
  · exact B939395
  · exact B939399
  · exact B939403
  · exact B939407
  · exact B939411
  · exact B939415
  · exact B939419
  · exact B939423
  · exact B939427
  · exact B939431
  · exact B939435
  · exact B939439
  · exact B939443
  · exact B939447
  · exact B939451
  · exact B939455
  · exact B939459
  · exact B939463
  · exact B939467
  · exact B939471
  · exact B939475
  · exact B939479
  · exact B939483
  · exact B939487
  · exact B939491
  · exact B939495
  · exact B939499
  · exact B939503
  · exact B939507
  · exact B939511
  · exact B939515
  · exact B939519
  · exact B939523
  · exact B939527
  · exact B939531
  · exact B939535
  · exact B939539
  · exact B939543
  · exact B939547
  · exact B939551
  · exact B939555
  · exact B939559
  · exact B939563
  · exact B939567
  · exact B939571
  · exact B939575
  · exact B939579
  · exact B939583
  · exact B939587
  · exact B939591
  · exact B939595
  · exact B939599
  · exact B939603
  · exact B939607
  · exact B939611
  · exact B939615
  · exact B939619
  · exact B939623
  · exact B939627
  · exact B939631
  · exact B939635
  · exact B939639
  · exact B939643
  · exact B939647
  · exact B939651
  · exact B939655
  · exact B939659
  · exact B939663
  · exact B939667
  · exact B939671
  · exact B939675
  · exact B939679
  · exact B939683
  · exact B939687
  · exact B939691
  · exact B939695
  · exact B939699
  · exact B939703
  · exact B939707
  · exact B939711
  · exact B939715
  · exact B939719
  · exact B939723
  · exact B939727
  · exact B939731
  · exact B939735
  · exact B939739
  · exact B939743
  · exact B939747
  · exact B939751
  · exact B939755
  · exact B939759
  · exact B939763
  · exact B939767
  · exact B939771
  · exact B939775
  · exact B939779
  · exact B939783
  · exact B939787
  · exact B939791
  · exact B939795
  · exact B939799
  · exact B939803
  · exact B939807
  · exact B939811
  · exact B939815
  · exact B939819
  · exact B939823
  · exact B939827
  · exact B939831
  · exact B939835
  · exact B939839
  · exact B939843
  · exact B939847
  · exact B939851
  · exact B939855
  · exact B939859
  · exact B939863
  · exact B939867
  · exact B939871
  · exact B939875
  · exact B939879
  · exact B939883
  · exact B939887
  · exact B939891
  · exact B939895
  · exact B939899
  · exact B939903
  · exact B939907
  · exact B939911
  · exact B939915
  · exact B939919
  · exact B939923
  · exact B939927
  · exact B939931
  · exact B939935
  · exact B939939
  · exact B939943
  · exact B939947
  · exact B939951
  · exact B939955
  · exact B939959
  · exact B939963
  · exact B939967
  · exact B939971
  · exact B939975
  · exact B939979
  · exact B939983
  · exact B939987
  · exact B939991
  · exact B939995
  · exact B939999
  · exact B940003
  · exact B940007
  · exact B940011
  · exact B940015
  · exact B940019
  · exact B940023
  · exact B940027
  · exact B940031
  · exact B940035
  · exact B940039
  · exact B940043
  · exact B940047
  · exact B940051
  · exact B940055
  · exact B940059
  · exact B940063
  · exact B940067
  · exact B940071
  · exact B940075
  · exact B940079
  · exact B940083
  · exact B940087
  · exact B940091
  · exact B940095
  · exact B940099
  · exact B940103
  · exact B940107
  · exact B940111
  · exact B940115
  · exact B940119
  · exact B940123
  · exact B940127
  · exact B940131
  · exact B940135
  · exact B940139
  · exact B940143
  · exact B940147
  · exact B940151
  · exact B940155
  · exact B940159
  · exact B940163
  · exact B940167
  · exact B940171
  · exact B940175
  · exact B940179
  · exact B940183
  · exact B940187
  · exact B940191
  · exact B940195
  · exact B940199
  · exact B940203
  · exact B940207
  · exact B940211
  · exact B940215
  · exact B940219
  · exact B940223
  · exact B940227
  · exact B940231
  · exact B940235
  · exact B940239
  · exact B940243
  · exact B940247
  · exact B940251
  · exact B940255
  · exact B940259
  · exact B940263
  · exact B940267
  · exact B940271
  · exact B940275
  · exact B940279
  · exact B940283
  · exact B940287
  · exact B940291
  · exact B940295
  · exact B940299
  · exact B940303
  · exact B940307
  · exact B940311
  · exact B940315
  · exact B940319
  · exact B940323
  · exact B940327
  · exact B940331
  · exact B940335
  · exact B940339
  · exact B940343
  · exact B940347
  · exact B940351
  · exact B940355
  · exact B940359
  · exact B940363
  · exact B940367
  · exact B940371
  · exact B940375
  · exact B940379
  · exact B940383
  · exact B940387
  · exact B940391
  · exact B940395
  · exact B940399
  · exact B940403
  · exact B940407
  · exact B940411
  · exact B940415
  · exact B940419
  · exact B940423
  · exact B940427
  · exact B940431
  · exact B940435
  · exact B940439
  · exact B940443
  · exact B940447
  · exact B940451
  · exact B940455
  · exact B940459
  · exact B940463
  · exact B940467
  · exact B940471
  · exact B940475
  · exact B940479
  · exact B940483
  · exact B940487
  · exact B940491
  · exact B940495
  · exact B940499
  · exact B940503
  · exact B940507
  · exact B940511
  · exact B940515
  · exact B940519
  · exact B940523
  · exact B940527
  · exact B940531
  · exact B940535
  · exact B940539
  · exact B940543
  · exact B940547
  · exact B940551
  · exact B940555
  · exact B940559
  · exact B940563
  · exact B940567
  · exact B940571
  · exact B940575
  · exact B940579
  · exact B940583

theorem solution (m : ℕ) (hlo : 936583 ≤ m) (hhi : m ≤ 940583) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 234145 ≤ j := by omega
    have hj2 : j ≤ 235145 := by omega
    have hb : Blo 936583 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 234845 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
