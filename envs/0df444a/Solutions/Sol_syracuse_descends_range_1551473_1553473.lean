-- Prove2me | solution 1 for syracuse_descends_range_1551473_1553473
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:05:44.175541+00:00
-- url     : https://prove2.me/submissions/2c5b0dfb-b067-46d4-a954-cc932b6a301e

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


theorem B3932165 : Blo 1551473 3932165 := bbase (se 4 (by rfl) ⟨368640, by rfl⟩ : syracuseStep 3932165 = 737281) (by norm_num)
theorem B2621477 : Blo 1551473 2621477 := bbase (se 4 (by rfl) ⟨245763, by rfl⟩ : syracuseStep 2621477 = 491527) (by norm_num)
theorem B2211877 : Blo 1551473 2211877 := bbase (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) (by norm_num)
theorem B8396885 : Blo 1551473 8396885 := bbase (se 8 (by rfl) ⟨49200, by rfl⟩ : syracuseStep 8396885 = 98401) (by norm_num)
theorem B13263061 : Blo 1551473 13263061 := bbase (se 7 (by rfl) ⟨155426, by rfl⟩ : syracuseStep 13263061 = 310853) (by norm_num)
theorem B1990885 : Blo 1551473 1990885 := bbase (se 4 (by rfl) ⟨186645, by rfl⟩ : syracuseStep 1990885 = 373291) (by norm_num)
theorem B4194613 : Blo 1551473 4194613 := bbase (se 5 (by rfl) ⟨196622, by rfl⟩ : syracuseStep 4194613 = 393245) (by norm_num)
theorem B2302277 : Blo 1551473 2302277 := bbase (se 4 (by rfl) ⟨215838, by rfl⟩ : syracuseStep 2302277 = 431677) (by norm_num)
theorem B3408229 : Blo 1551473 3408229 := bbase (se 4 (by rfl) ⟨319521, by rfl⟩ : syracuseStep 3408229 = 639043) (by norm_num)
theorem B7561637 : Blo 1551473 7561637 := bbase (se 4 (by rfl) ⟨708903, by rfl⟩ : syracuseStep 7561637 = 1417807) (by norm_num)
theorem B1769941 : Blo 1551473 1769941 := bbase (se 7 (by rfl) ⟨20741, by rfl⟩ : syracuseStep 1769941 = 41483) (by norm_num)
theorem B1573333 : Blo 1551473 1573333 := bbase (se 7 (by rfl) ⟨18437, by rfl⟩ : syracuseStep 1573333 = 36875) (by norm_num)
theorem B17686997 : Blo 1551473 17686997 := bbase (se 7 (by rfl) ⟨207269, by rfl⟩ : syracuseStep 17686997 = 414539) (by norm_num)
theorem B6644213 : Blo 1551473 6644213 := bbase (se 5 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 6644213 = 622895) (by norm_num)
theorem B6291989 : Blo 1551473 6291989 := bbase (se 6 (by rfl) ⟨147468, by rfl⟩ : syracuseStep 6291989 = 294937) (by norm_num)
theorem B1745437 : Blo 1551473 1745437 := bbase (se 3 (by rfl) ⟨327269, by rfl⟩ : syracuseStep 1745437 = 654539) (by norm_num)
theorem B4481573 : Blo 1551473 4481573 := bbase (se 4 (by rfl) ⟨420147, by rfl⟩ : syracuseStep 4481573 = 840295) (by norm_num)
theorem B1745473 : Blo 1551473 1745473 := bbase (se 2 (by rfl) ⟨654552, by rfl⟩ : syracuseStep 1745473 = 1309105) (by norm_num)
theorem B1745509 : Blo 1551473 1745509 := bbase (se 4 (by rfl) ⟨163641, by rfl⟩ : syracuseStep 1745509 = 327283) (by norm_num)
theorem B4194917 : Blo 1551473 4194917 := bbase (se 4 (by rfl) ⟨393273, by rfl⟩ : syracuseStep 4194917 = 786547) (by norm_num)
theorem B1745545 : Blo 1551473 1745545 := bbase (se 2 (by rfl) ⟨654579, by rfl⟩ : syracuseStep 1745545 = 1309159) (by norm_num)
theorem B2327213 : Blo 1551473 2327213 := bbase (se 3 (by rfl) ⟨436352, by rfl⟩ : syracuseStep 2327213 = 872705) (by norm_num)
theorem B1745581 : Blo 1551473 1745581 := bbase (se 3 (by rfl) ⟨327296, by rfl⟩ : syracuseStep 1745581 = 654593) (by norm_num)
theorem B2327237 : Blo 1551473 2327237 := bbase (se 4 (by rfl) ⟨218178, by rfl⟩ : syracuseStep 2327237 = 436357) (by norm_num)
theorem B7856837 : Blo 1551473 7856837 := bbase (se 4 (by rfl) ⟨736578, by rfl⟩ : syracuseStep 7856837 = 1473157) (by norm_num)
theorem B1745617 : Blo 1551473 1745617 := bbase (se 2 (by rfl) ⟨654606, by rfl⟩ : syracuseStep 1745617 = 1309213) (by norm_num)
theorem B2327261 : Blo 1551473 2327261 := bbase (se 3 (by rfl) ⟨436361, by rfl⟩ : syracuseStep 2327261 = 872723) (by norm_num)
theorem B1573597 : Blo 1551473 1573597 := bbase (se 3 (by rfl) ⟨295049, by rfl⟩ : syracuseStep 1573597 = 590099) (by norm_num)
theorem B3982061 : Blo 1551473 3982061 := bbase (se 3 (by rfl) ⟨746636, by rfl⟩ : syracuseStep 3982061 = 1493273) (by norm_num)
theorem B2327285 : Blo 1551473 2327285 := bbase (se 5 (by rfl) ⟨109091, by rfl⟩ : syracuseStep 2327285 = 218183) (by norm_num)
theorem B1745653 : Blo 1551473 1745653 := bbase (se 5 (by rfl) ⟨81827, by rfl⟩ : syracuseStep 1745653 = 163655) (by norm_num)
theorem B3539717 : Blo 1551473 3539717 := bbase (se 4 (by rfl) ⟨331848, by rfl⟩ : syracuseStep 3539717 = 663697) (by norm_num)
theorem B2327309 : Blo 1551473 2327309 := bbase (se 3 (by rfl) ⟨436370, by rfl⟩ : syracuseStep 2327309 = 872741) (by norm_num)
theorem B1745689 : Blo 1551473 1745689 := bbase (se 2 (by rfl) ⟨654633, by rfl⟩ : syracuseStep 1745689 = 1309267) (by norm_num)
theorem B2327333 : Blo 1551473 2327333 := bbase (se 4 (by rfl) ⟨218187, by rfl⟩ : syracuseStep 2327333 = 436375) (by norm_num)
theorem B2327357 : Blo 1551473 2327357 := bbase (se 3 (by rfl) ⟨436379, by rfl⟩ : syracuseStep 2327357 = 872759) (by norm_num)
theorem B1745725 : Blo 1551473 1745725 := bbase (se 3 (by rfl) ⟨327323, by rfl⟩ : syracuseStep 1745725 = 654647) (by norm_num)
theorem B2327381 : Blo 1551473 2327381 := bbase (se 9 (by rfl) ⟨6818, by rfl⟩ : syracuseStep 2327381 = 13637) (by norm_num)
theorem B1745761 : Blo 1551473 1745761 := bbase (se 2 (by rfl) ⟨654660, by rfl⟩ : syracuseStep 1745761 = 1309321) (by norm_num)
theorem B2327405 : Blo 1551473 2327405 := bbase (se 3 (by rfl) ⟨436388, by rfl⟩ : syracuseStep 2327405 = 872777) (by norm_num)
theorem B2327429 : Blo 1551473 2327429 := bbase (se 4 (by rfl) ⟨218196, by rfl⟩ : syracuseStep 2327429 = 436393) (by norm_num)
theorem B1745797 : Blo 1551473 1745797 := bbase (se 4 (by rfl) ⟨163668, by rfl⟩ : syracuseStep 1745797 = 327337) (by norm_num)
theorem B2327453 : Blo 1551473 2327453 := bbase (se 3 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 2327453 = 872795) (by norm_num)
theorem B1745833 : Blo 1551473 1745833 := bbase (se 2 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 1745833 = 1309375) (by norm_num)
theorem B2327477 : Blo 1551473 2327477 := bbase (se 5 (by rfl) ⟨109100, by rfl⟩ : syracuseStep 2327477 = 218201) (by norm_num)
theorem B2327501 : Blo 1551473 2327501 := bbase (se 3 (by rfl) ⟨436406, by rfl⟩ : syracuseStep 2327501 = 872813) (by norm_num)
theorem B1745869 : Blo 1551473 1745869 := bbase (se 3 (by rfl) ⟨327350, by rfl⟩ : syracuseStep 1745869 = 654701) (by norm_num)
theorem B2327525 : Blo 1551473 2327525 := bbase (se 4 (by rfl) ⟨218205, by rfl⟩ : syracuseStep 2327525 = 436411) (by norm_num)
theorem B1745905 : Blo 1551473 1745905 := bbase (se 2 (by rfl) ⟨654714, by rfl⟩ : syracuseStep 1745905 = 1309429) (by norm_num)
theorem B2327549 : Blo 1551473 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B3490829 : Blo 1551473 3490829 := bbase (se 3 (by rfl) ⟨654530, by rfl⟩ : syracuseStep 3490829 = 1309061) (by norm_num)
theorem B2327573 : Blo 1551473 2327573 := bbase (se 6 (by rfl) ⟨54552, by rfl⟩ : syracuseStep 2327573 = 109105) (by norm_num)
theorem B1745941 : Blo 1551473 1745941 := bbase (se 6 (by rfl) ⟨40920, by rfl⟩ : syracuseStep 1745941 = 81841) (by norm_num)
theorem B2327597 : Blo 1551473 2327597 := bbase (se 3 (by rfl) ⟨436424, by rfl⟩ : syracuseStep 2327597 = 872849) (by norm_num)
theorem B3146797 : Blo 1551473 3146797 := bbase (se 3 (by rfl) ⟨590024, by rfl⟩ : syracuseStep 3146797 = 1180049) (by norm_num)
theorem B1745977 : Blo 1551473 1745977 := bbase (se 2 (by rfl) ⟨654741, by rfl⟩ : syracuseStep 1745977 = 1309483) (by norm_num)
theorem B2327621 : Blo 1551473 2327621 := bbase (se 4 (by rfl) ⟨218214, by rfl⟩ : syracuseStep 2327621 = 436429) (by norm_num)
theorem B3490901 : Blo 1551473 3490901 := bbase (se 8 (by rfl) ⟨20454, by rfl⟩ : syracuseStep 3490901 = 40909) (by norm_num)
theorem B2327645 : Blo 1551473 2327645 := bbase (se 3 (by rfl) ⟨436433, by rfl⟩ : syracuseStep 2327645 = 872867) (by norm_num)
theorem B1746013 : Blo 1551473 1746013 := bbase (se 3 (by rfl) ⟨327377, by rfl⟩ : syracuseStep 1746013 = 654755) (by norm_num)
theorem B2327669 : Blo 1551473 2327669 := bbase (se 5 (by rfl) ⟨109109, by rfl⟩ : syracuseStep 2327669 = 218219) (by norm_num)
theorem B1746049 : Blo 1551473 1746049 := bbase (se 2 (by rfl) ⟨654768, by rfl⟩ : syracuseStep 1746049 = 1309537) (by norm_num)
theorem B2327693 : Blo 1551473 2327693 := bbase (se 3 (by rfl) ⟨436442, by rfl⟩ : syracuseStep 2327693 = 872885) (by norm_num)
theorem B3490973 : Blo 1551473 3490973 := bbase (se 3 (by rfl) ⟨654557, by rfl⟩ : syracuseStep 3490973 = 1309115) (by norm_num)
theorem B2327717 : Blo 1551473 2327717 := bbase (se 4 (by rfl) ⟨218223, by rfl⟩ : syracuseStep 2327717 = 436447) (by norm_num)
theorem B1746085 : Blo 1551473 1746085 := bbase (se 4 (by rfl) ⟨163695, by rfl⟩ : syracuseStep 1746085 = 327391) (by norm_num)
theorem B2327741 : Blo 1551473 2327741 := bbase (se 3 (by rfl) ⟨436451, by rfl⟩ : syracuseStep 2327741 = 872903) (by norm_num)
theorem B1746121 : Blo 1551473 1746121 := bbase (se 2 (by rfl) ⟨654795, by rfl⟩ : syracuseStep 1746121 = 1309591) (by norm_num)
theorem B2327765 : Blo 1551473 2327765 := bbase (se 7 (by rfl) ⟨27278, by rfl⟩ : syracuseStep 2327765 = 54557) (by norm_num)
theorem B3491045 : Blo 1551473 3491045 := bbase (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) (by norm_num)
theorem B2327789 : Blo 1551473 2327789 := bbase (se 3 (by rfl) ⟨436460, by rfl⟩ : syracuseStep 2327789 = 872921) (by norm_num)
theorem B1746157 : Blo 1551473 1746157 := bbase (se 3 (by rfl) ⟨327404, by rfl⟩ : syracuseStep 1746157 = 654809) (by norm_num)
theorem B2327813 : Blo 1551473 2327813 := bbase (se 4 (by rfl) ⟨218232, by rfl⟩ : syracuseStep 2327813 = 436465) (by norm_num)
theorem B1746193 : Blo 1551473 1746193 := bbase (se 2 (by rfl) ⟨654822, by rfl⟩ : syracuseStep 1746193 = 1309645) (by norm_num)
theorem B2327837 : Blo 1551473 2327837 := bbase (se 3 (by rfl) ⟨436469, by rfl⟩ : syracuseStep 2327837 = 872939) (by norm_num)
theorem B3491117 : Blo 1551473 3491117 := bbase (se 3 (by rfl) ⟨654584, by rfl⟩ : syracuseStep 3491117 = 1309169) (by norm_num)
theorem B6628661 : Blo 1551473 6628661 := bbase (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) (by norm_num)
theorem B2327861 : Blo 1551473 2327861 := bbase (se 5 (by rfl) ⟨109118, by rfl⟩ : syracuseStep 2327861 = 218237) (by norm_num)
theorem B1746229 : Blo 1551473 1746229 := bbase (se 5 (by rfl) ⟨81854, by rfl⟩ : syracuseStep 1746229 = 163709) (by norm_num)
theorem B1770817 : Blo 1551473 1770817 := bbase (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) (by norm_num)
theorem B2327885 : Blo 1551473 2327885 := bbase (se 3 (by rfl) ⟨436478, by rfl⟩ : syracuseStep 2327885 = 872957) (by norm_num)
theorem B5891413 : Blo 1551473 5891413 := bbase (se 12 (by rfl) ⟨2157, by rfl⟩ : syracuseStep 5891413 = 4315) (by norm_num)
theorem B1746265 : Blo 1551473 1746265 := bbase (se 2 (by rfl) ⟨654849, by rfl⟩ : syracuseStep 1746265 = 1309699) (by norm_num)
theorem B2327909 : Blo 1551473 2327909 := bbase (se 4 (by rfl) ⟨218241, by rfl⟩ : syracuseStep 2327909 = 436483) (by norm_num)
theorem B3491189 : Blo 1551473 3491189 := bbase (se 5 (by rfl) ⟨163649, by rfl⟩ : syracuseStep 3491189 = 327299) (by norm_num)
theorem B2327933 : Blo 1551473 2327933 := bbase (se 3 (by rfl) ⟨436487, by rfl⟩ : syracuseStep 2327933 = 872975) (by norm_num)
theorem B1746301 : Blo 1551473 1746301 := bbase (se 3 (by rfl) ⟨327431, by rfl⟩ : syracuseStep 1746301 = 654863) (by norm_num)
theorem B4973957 : Blo 1551473 4973957 := bbase (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) (by norm_num)
theorem B2327957 : Blo 1551473 2327957 := bbase (se 6 (by rfl) ⟨54561, by rfl⟩ : syracuseStep 2327957 = 109123) (by norm_num)
theorem B1746337 : Blo 1551473 1746337 := bbase (se 2 (by rfl) ⟨654876, by rfl⟩ : syracuseStep 1746337 = 1309753) (by norm_num)
theorem B2327981 : Blo 1551473 2327981 := bbase (se 3 (by rfl) ⟨436496, by rfl⟩ : syracuseStep 2327981 = 872993) (by norm_num)
theorem B3491261 : Blo 1551473 3491261 := bbase (se 3 (by rfl) ⟨654611, by rfl⟩ : syracuseStep 3491261 = 1309223) (by norm_num)
theorem B2328005 : Blo 1551473 2328005 := bbase (se 4 (by rfl) ⟨218250, by rfl⟩ : syracuseStep 2328005 = 436501) (by norm_num)
theorem B1746373 : Blo 1551473 1746373 := bbase (se 4 (by rfl) ⟨163722, by rfl⟩ : syracuseStep 1746373 = 327445) (by norm_num)
theorem B1770949 : Blo 1551473 1770949 := bbase (se 4 (by rfl) ⟨166026, by rfl⟩ : syracuseStep 1770949 = 332053) (by norm_num)
theorem B2328029 : Blo 1551473 2328029 := bbase (se 3 (by rfl) ⟨436505, by rfl⟩ : syracuseStep 2328029 = 873011) (by norm_num)
theorem B1746409 : Blo 1551473 1746409 := bbase (se 2 (by rfl) ⟨654903, by rfl⟩ : syracuseStep 1746409 = 1309807) (by norm_num)
theorem B2328053 : Blo 1551473 2328053 := bbase (se 5 (by rfl) ⟨109127, by rfl⟩ : syracuseStep 2328053 = 218255) (by norm_num)
theorem B3491333 : Blo 1551473 3491333 := bbase (se 4 (by rfl) ⟨327312, by rfl⟩ : syracuseStep 3491333 = 654625) (by norm_num)
theorem B2328077 : Blo 1551473 2328077 := bbase (se 3 (by rfl) ⟨436514, by rfl⟩ : syracuseStep 2328077 = 873029) (by norm_num)
theorem B3982861 : Blo 1551473 3982861 := bbase (se 3 (by rfl) ⟨746786, by rfl⟩ : syracuseStep 3982861 = 1493573) (by norm_num)
theorem B1746445 : Blo 1551473 1746445 := bbase (se 3 (by rfl) ⟨327458, by rfl⟩ : syracuseStep 1746445 = 654917) (by norm_num)
theorem B2328101 : Blo 1551473 2328101 := bbase (se 4 (by rfl) ⟨218259, by rfl⟩ : syracuseStep 2328101 = 436519) (by norm_num)
theorem B1746481 : Blo 1551473 1746481 := bbase (se 2 (by rfl) ⟨654930, by rfl⟩ : syracuseStep 1746481 = 1309861) (by norm_num)
theorem B2328125 : Blo 1551473 2328125 := bbase (se 3 (by rfl) ⟨436523, by rfl⟩ : syracuseStep 2328125 = 873047) (by norm_num)
theorem B4974149 : Blo 1551473 4974149 := bbase (se 4 (by rfl) ⟨466326, by rfl⟩ : syracuseStep 4974149 = 932653) (by norm_num)
theorem B3491405 : Blo 1551473 3491405 := bbase (se 3 (by rfl) ⟨654638, by rfl⟩ : syracuseStep 3491405 = 1309277) (by norm_num)
theorem B2328149 : Blo 1551473 2328149 := bbase (se 8 (by rfl) ⟨13641, by rfl⟩ : syracuseStep 2328149 = 27283) (by norm_num)
theorem B1746517 : Blo 1551473 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B5236325 : Blo 1551473 5236325 := bbase (se 4 (by rfl) ⟨490905, by rfl⟩ : syracuseStep 5236325 = 981811) (by norm_num)
theorem B2328173 : Blo 1551473 2328173 := bbase (se 3 (by rfl) ⟨436532, by rfl⟩ : syracuseStep 2328173 = 873065) (by norm_num)
theorem B1746553 : Blo 1551473 1746553 := bbase (se 2 (by rfl) ⟨654957, by rfl⟩ : syracuseStep 1746553 = 1309915) (by norm_num)
theorem B2328197 : Blo 1551473 2328197 := bbase (se 4 (by rfl) ⟨218268, by rfl⟩ : syracuseStep 2328197 = 436537) (by norm_num)
theorem B5891717 : Blo 1551473 5891717 := bbase (se 4 (by rfl) ⟨552348, by rfl⟩ : syracuseStep 5891717 = 1104697) (by norm_num)
theorem B1574537 : Blo 1551473 1574537 := bbase (se 2 (by rfl) ⟨590451, by rfl⟩ : syracuseStep 1574537 = 1180903) (by norm_num)
theorem B3491477 : Blo 1551473 3491477 := bbase (se 6 (by rfl) ⟨81831, by rfl⟩ : syracuseStep 3491477 = 163663) (by norm_num)
theorem B2328221 : Blo 1551473 2328221 := bbase (se 3 (by rfl) ⟨436541, by rfl⟩ : syracuseStep 2328221 = 873083) (by norm_num)
theorem B1746589 : Blo 1551473 1746589 := bbase (se 3 (by rfl) ⟨327485, by rfl⟩ : syracuseStep 1746589 = 654971) (by norm_num)
theorem B2328245 : Blo 1551473 2328245 := bbase (se 5 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 2328245 = 218273) (by norm_num)
theorem B1746625 : Blo 1551473 1746625 := bbase (se 2 (by rfl) ⟨654984, by rfl⟩ : syracuseStep 1746625 = 1309969) (by norm_num)
theorem B2328269 : Blo 1551473 2328269 := bbase (se 3 (by rfl) ⟨436550, by rfl⟩ : syracuseStep 2328269 = 873101) (by norm_num)
theorem B3491549 : Blo 1551473 3491549 := bbase (se 3 (by rfl) ⟨654665, by rfl⟩ : syracuseStep 3491549 = 1309331) (by norm_num)
theorem B7079653 : Blo 1551473 7079653 := bbase (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) (by norm_num)
theorem B2328293 : Blo 1551473 2328293 := bbase (se 4 (by rfl) ⟨218277, by rfl⟩ : syracuseStep 2328293 = 436555) (by norm_num)
theorem B1746661 : Blo 1551473 1746661 := bbase (se 4 (by rfl) ⟨163749, by rfl⟩ : syracuseStep 1746661 = 327499) (by norm_num)
theorem B2328317 : Blo 1551473 2328317 := bbase (se 3 (by rfl) ⟨436559, by rfl⟩ : syracuseStep 2328317 = 873119) (by norm_num)
theorem B1746697 : Blo 1551473 1746697 := bbase (se 2 (by rfl) ⟨655011, by rfl⟩ : syracuseStep 1746697 = 1310023) (by norm_num)
theorem B2328341 : Blo 1551473 2328341 := bbase (se 6 (by rfl) ⟨54570, by rfl⟩ : syracuseStep 2328341 = 109141) (by norm_num)
theorem B3491621 : Blo 1551473 3491621 := bbase (se 4 (by rfl) ⟨327339, by rfl⟩ : syracuseStep 3491621 = 654679) (by norm_num)
theorem B2361125 : Blo 1551473 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B2328365 : Blo 1551473 2328365 := bbase (se 3 (by rfl) ⟨436568, by rfl⟩ : syracuseStep 2328365 = 873137) (by norm_num)
theorem B1746733 : Blo 1551473 1746733 := bbase (se 3 (by rfl) ⟨327512, by rfl⟩ : syracuseStep 1746733 = 655025) (by norm_num)
theorem B2328389 : Blo 1551473 2328389 := bbase (se 4 (by rfl) ⟨218286, by rfl⟩ : syracuseStep 2328389 = 436573) (by norm_num)
theorem B1746769 : Blo 1551473 1746769 := bbase (se 2 (by rfl) ⟨655038, by rfl⟩ : syracuseStep 1746769 = 1310077) (by norm_num)
theorem B2328413 : Blo 1551473 2328413 := bbase (se 3 (by rfl) ⟨436577, by rfl⟩ : syracuseStep 2328413 = 873155) (by norm_num)
theorem B3491693 : Blo 1551473 3491693 := bbase (se 3 (by rfl) ⟨654692, by rfl⟩ : syracuseStep 3491693 = 1309385) (by norm_num)
theorem B2328437 : Blo 1551473 2328437 := bbase (se 5 (by rfl) ⟨109145, by rfl⟩ : syracuseStep 2328437 = 218291) (by norm_num)
theorem B1746805 : Blo 1551473 1746805 := bbase (se 5 (by rfl) ⟨81881, by rfl⟩ : syracuseStep 1746805 = 163763) (by norm_num)
theorem B3188621 : Blo 1551473 3188621 := bbase (se 3 (by rfl) ⟨597866, by rfl⟩ : syracuseStep 3188621 = 1195733) (by norm_num)
theorem B2328461 : Blo 1551473 2328461 := bbase (se 3 (by rfl) ⟨436586, by rfl⟩ : syracuseStep 2328461 = 873173) (by norm_num)
theorem B11495317 : Blo 1551473 11495317 := bbase (se 6 (by rfl) ⟨269421, by rfl⟩ : syracuseStep 11495317 = 538843) (by norm_num)
theorem B1746841 : Blo 1551473 1746841 := bbase (se 2 (by rfl) ⟨655065, by rfl⟩ : syracuseStep 1746841 = 1310131) (by norm_num)
theorem B2328485 : Blo 1551473 2328485 := bbase (se 4 (by rfl) ⟨218295, by rfl⟩ : syracuseStep 2328485 = 436591) (by norm_num)
theorem B3491765 : Blo 1551473 3491765 := bbase (se 5 (by rfl) ⟨163676, by rfl⟩ : syracuseStep 3491765 = 327353) (by norm_num)
theorem B2328509 : Blo 1551473 2328509 := bbase (se 3 (by rfl) ⟨436595, by rfl⟩ : syracuseStep 2328509 = 873191) (by norm_num)
theorem B1746877 : Blo 1551473 1746877 := bbase (se 3 (by rfl) ⟨327539, by rfl⟩ : syracuseStep 1746877 = 655079) (by norm_num)
theorem B7858133 : Blo 1551473 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B2328533 : Blo 1551473 2328533 := bbase (se 7 (by rfl) ⟨27287, by rfl⟩ : syracuseStep 2328533 = 54575) (by norm_num)
theorem B1746913 : Blo 1551473 1746913 := bbase (se 2 (by rfl) ⟨655092, by rfl⟩ : syracuseStep 1746913 = 1310185) (by norm_num)
theorem B2328557 : Blo 1551473 2328557 := bbase (se 3 (by rfl) ⟨436604, by rfl⟩ : syracuseStep 2328557 = 873209) (by norm_num)
theorem B3491837 : Blo 1551473 3491837 := bbase (se 3 (by rfl) ⟨654719, by rfl⟩ : syracuseStep 3491837 = 1309439) (by norm_num)
theorem B2328581 : Blo 1551473 2328581 := bbase (se 4 (by rfl) ⟨218304, by rfl⟩ : syracuseStep 2328581 = 436609) (by norm_num)
theorem B1746949 : Blo 1551473 1746949 := bbase (se 4 (by rfl) ⟨163776, by rfl⟩ : syracuseStep 1746949 = 327553) (by norm_num)
theorem B5236757 : Blo 1551473 5236757 := bbase (se 6 (by rfl) ⟨122736, by rfl⟩ : syracuseStep 5236757 = 245473) (by norm_num)
theorem B2328605 : Blo 1551473 2328605 := bbase (se 3 (by rfl) ⟨436613, by rfl⟩ : syracuseStep 2328605 = 873227) (by norm_num)
theorem B1746985 : Blo 1551473 1746985 := bbase (se 2 (by rfl) ⟨655119, by rfl⟩ : syracuseStep 1746985 = 1310239) (by norm_num)
theorem B2328629 : Blo 1551473 2328629 := bbase (se 5 (by rfl) ⟨109154, by rfl⟩ : syracuseStep 2328629 = 218309) (by norm_num)
theorem B3491909 : Blo 1551473 3491909 := bbase (se 4 (by rfl) ⟨327366, by rfl⟩ : syracuseStep 3491909 = 654733) (by norm_num)
theorem B2328653 : Blo 1551473 2328653 := bbase (se 3 (by rfl) ⟨436622, by rfl⟩ : syracuseStep 2328653 = 873245) (by norm_num)
theorem B1747021 : Blo 1551473 1747021 := bbase (se 3 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 1747021 = 655133) (by norm_num)
theorem B2328677 : Blo 1551473 2328677 := bbase (se 4 (by rfl) ⟨218313, by rfl⟩ : syracuseStep 2328677 = 436627) (by norm_num)
theorem B6383717 : Blo 1551473 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B1747057 : Blo 1551473 1747057 := bbase (se 2 (by rfl) ⟨655146, by rfl⟩ : syracuseStep 1747057 = 1310293) (by norm_num)
theorem B2328701 : Blo 1551473 2328701 := bbase (se 3 (by rfl) ⟨436631, by rfl⟩ : syracuseStep 2328701 = 873263) (by norm_num)
theorem B3491981 : Blo 1551473 3491981 := bbase (se 3 (by rfl) ⟨654746, by rfl⟩ : syracuseStep 3491981 = 1309493) (by norm_num)
theorem B2328725 : Blo 1551473 2328725 := bbase (se 6 (by rfl) ⟨54579, by rfl⟩ : syracuseStep 2328725 = 109159) (by norm_num)
theorem B13265045 : Blo 1551473 13265045 := bbase (se 6 (by rfl) ⟨310899, by rfl⟩ : syracuseStep 13265045 = 621799) (by norm_num)
theorem B1747093 : Blo 1551473 1747093 := bbase (se 6 (by rfl) ⟨40947, by rfl⟩ : syracuseStep 1747093 = 81895) (by norm_num)
theorem B2328749 : Blo 1551473 2328749 := bbase (se 3 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 2328749 = 873281) (by norm_num)
theorem B1747129 : Blo 1551473 1747129 := bbase (se 2 (by rfl) ⟨655173, by rfl⟩ : syracuseStep 1747129 = 1310347) (by norm_num)
theorem B2328773 : Blo 1551473 2328773 := bbase (se 4 (by rfl) ⟨218322, by rfl⟩ : syracuseStep 2328773 = 436645) (by norm_num)
theorem B3492053 : Blo 1551473 3492053 := bbase (se 7 (by rfl) ⟨40922, by rfl⟩ : syracuseStep 3492053 = 81845) (by norm_num)
theorem B23914709 : Blo 1551473 23914709 := bbase (se 7 (by rfl) ⟨280250, by rfl⟩ : syracuseStep 23914709 = 560501) (by norm_num)
theorem B2328797 : Blo 1551473 2328797 := bbase (se 3 (by rfl) ⟨436649, by rfl⟩ : syracuseStep 2328797 = 873299) (by norm_num)
theorem B1747165 : Blo 1551473 1747165 := bbase (se 3 (by rfl) ⟨327593, by rfl⟩ : syracuseStep 1747165 = 655187) (by norm_num)
theorem B2328821 : Blo 1551473 2328821 := bbase (se 5 (by rfl) ⟨109163, by rfl⟩ : syracuseStep 2328821 = 218327) (by norm_num)
theorem B1747201 : Blo 1551473 1747201 := bbase (se 2 (by rfl) ⟨655200, by rfl⟩ : syracuseStep 1747201 = 1310401) (by norm_num)
theorem B1657093 : Blo 1551473 1657093 := bbase (se 4 (by rfl) ⟨155352, by rfl⟩ : syracuseStep 1657093 = 310705) (by norm_num)
theorem B2328845 : Blo 1551473 2328845 := bbase (se 3 (by rfl) ⟨436658, by rfl⟩ : syracuseStep 2328845 = 873317) (by norm_num)
theorem B3492125 : Blo 1551473 3492125 := bbase (se 3 (by rfl) ⟨654773, by rfl⟩ : syracuseStep 3492125 = 1309547) (by norm_num)
theorem B2328869 : Blo 1551473 2328869 := bbase (se 4 (by rfl) ⟨218331, by rfl⟩ : syracuseStep 2328869 = 436663) (by norm_num)
theorem B1747237 : Blo 1551473 1747237 := bbase (se 4 (by rfl) ⟨163803, by rfl⟩ : syracuseStep 1747237 = 327607) (by norm_num)
theorem B2328893 : Blo 1551473 2328893 := bbase (se 3 (by rfl) ⟨436667, by rfl⟩ : syracuseStep 2328893 = 873335) (by norm_num)
theorem B1747273 : Blo 1551473 1747273 := bbase (se 2 (by rfl) ⟨655227, by rfl⟩ : syracuseStep 1747273 = 1310455) (by norm_num)
theorem B2328917 : Blo 1551473 2328917 := bbase (se 10 (by rfl) ⟨3411, by rfl⟩ : syracuseStep 2328917 = 6823) (by norm_num)
theorem B3983701 : Blo 1551473 3983701 := bbase (se 10 (by rfl) ⟨5835, by rfl⟩ : syracuseStep 3983701 = 11671) (by norm_num)
theorem B3492197 : Blo 1551473 3492197 := bbase (se 4 (by rfl) ⟨327393, by rfl⟩ : syracuseStep 3492197 = 654787) (by norm_num)
theorem B2328941 : Blo 1551473 2328941 := bbase (se 3 (by rfl) ⟨436676, by rfl⟩ : syracuseStep 2328941 = 873353) (by norm_num)
theorem B1747309 : Blo 1551473 1747309 := bbase (se 3 (by rfl) ⟨327620, by rfl⟩ : syracuseStep 1747309 = 655241) (by norm_num)
theorem B2328965 : Blo 1551473 2328965 := bbase (se 4 (by rfl) ⟨218340, by rfl⟩ : syracuseStep 2328965 = 436681) (by norm_num)
theorem B1747345 : Blo 1551473 1747345 := bbase (se 2 (by rfl) ⟨655254, by rfl⟩ : syracuseStep 1747345 = 1310509) (by norm_num)
theorem B2328989 : Blo 1551473 2328989 := bbase (se 3 (by rfl) ⟨436685, by rfl⟩ : syracuseStep 2328989 = 873371) (by norm_num)
theorem B3492269 : Blo 1551473 3492269 := bbase (se 3 (by rfl) ⟨654800, by rfl⟩ : syracuseStep 3492269 = 1309601) (by norm_num)
theorem B2329013 : Blo 1551473 2329013 := bbase (se 5 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 2329013 = 218345) (by norm_num)
theorem B1747381 : Blo 1551473 1747381 := bbase (se 5 (by rfl) ⟨81908, by rfl⟩ : syracuseStep 1747381 = 163817) (by norm_num)
theorem B5237189 : Blo 1551473 5237189 := bbase (se 4 (by rfl) ⟨490986, by rfl⟩ : syracuseStep 5237189 = 981973) (by norm_num)
theorem B2329037 : Blo 1551473 2329037 := bbase (se 3 (by rfl) ⟨436694, by rfl⟩ : syracuseStep 2329037 = 873389) (by norm_num)
theorem B1747417 : Blo 1551473 1747417 := bbase (se 2 (by rfl) ⟨655281, by rfl⟩ : syracuseStep 1747417 = 1310563) (by norm_num)
theorem B2329061 : Blo 1551473 2329061 := bbase (se 4 (by rfl) ⟨218349, by rfl⟩ : syracuseStep 2329061 = 436699) (by norm_num)
theorem B3492341 : Blo 1551473 3492341 := bbase (se 5 (by rfl) ⟨163703, by rfl⟩ : syracuseStep 3492341 = 327407) (by norm_num)
theorem B2329085 : Blo 1551473 2329085 := bbase (se 3 (by rfl) ⟨436703, by rfl⟩ : syracuseStep 2329085 = 873407) (by norm_num)
theorem B1747453 : Blo 1551473 1747453 := bbase (se 3 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 1747453 = 655295) (by norm_num)
theorem B2329109 : Blo 1551473 2329109 := bbase (se 6 (by rfl) ⟨54588, by rfl⟩ : syracuseStep 2329109 = 109177) (by norm_num)
theorem B1747489 : Blo 1551473 1747489 := bbase (se 2 (by rfl) ⟨655308, by rfl⟩ : syracuseStep 1747489 = 1310617) (by norm_num)
theorem B2329133 : Blo 1551473 2329133 := bbase (se 3 (by rfl) ⟨436712, by rfl⟩ : syracuseStep 2329133 = 873425) (by norm_num)
theorem B3492413 : Blo 1551473 3492413 := bbase (se 3 (by rfl) ⟨654827, by rfl⟩ : syracuseStep 3492413 = 1309655) (by norm_num)
theorem B2329157 : Blo 1551473 2329157 := bbase (se 4 (by rfl) ⟨218358, by rfl⟩ : syracuseStep 2329157 = 436717) (by norm_num)
theorem B1747525 : Blo 1551473 1747525 := bbase (se 4 (by rfl) ⟨163830, by rfl⟩ : syracuseStep 1747525 = 327661) (by norm_num)
theorem B3729997 : Blo 1551473 3729997 := bbase (se 3 (by rfl) ⟨699374, by rfl⟩ : syracuseStep 3729997 = 1398749) (by norm_num)
theorem B2329181 : Blo 1551473 2329181 := bbase (se 3 (by rfl) ⟨436721, by rfl⟩ : syracuseStep 2329181 = 873443) (by norm_num)
theorem B1747561 : Blo 1551473 1747561 := bbase (se 2 (by rfl) ⟨655335, by rfl⟩ : syracuseStep 1747561 = 1310671) (by norm_num)
theorem B2329205 : Blo 1551473 2329205 := bbase (se 5 (by rfl) ⟨109181, by rfl⟩ : syracuseStep 2329205 = 218363) (by norm_num)
theorem B1657469 : Blo 1551473 1657469 := bbase (se 3 (by rfl) ⟨310775, by rfl⟩ : syracuseStep 1657469 = 621551) (by norm_num)
theorem B3730045 : Blo 1551473 3730045 := bbase (se 3 (by rfl) ⟨699383, by rfl⟩ : syracuseStep 3730045 = 1398767) (by norm_num)
theorem B3492485 : Blo 1551473 3492485 := bbase (se 4 (by rfl) ⟨327420, by rfl⟩ : syracuseStep 3492485 = 654841) (by norm_num)
theorem B3361421 : Blo 1551473 3361421 := bbase (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) (by norm_num)
theorem B2329229 : Blo 1551473 2329229 := bbase (se 3 (by rfl) ⟨436730, by rfl⟩ : syracuseStep 2329229 = 873461) (by norm_num)
theorem B1747597 : Blo 1551473 1747597 := bbase (se 3 (by rfl) ⟨327674, by rfl⟩ : syracuseStep 1747597 = 655349) (by norm_num)
theorem B2329253 : Blo 1551473 2329253 := bbase (se 4 (by rfl) ⟨218367, by rfl⟩ : syracuseStep 2329253 = 436735) (by norm_num)
theorem B1747633 : Blo 1551473 1747633 := bbase (se 2 (by rfl) ⟨655362, by rfl⟩ : syracuseStep 1747633 = 1310725) (by norm_num)
theorem B2329277 : Blo 1551473 2329277 := bbase (se 3 (by rfl) ⟨436739, by rfl⟩ : syracuseStep 2329277 = 873479) (by norm_num)
theorem B1657541 : Blo 1551473 1657541 := bbase (se 4 (by rfl) ⟨155394, by rfl⟩ : syracuseStep 1657541 = 310789) (by norm_num)
theorem B3492557 : Blo 1551473 3492557 := bbase (se 3 (by rfl) ⟨654854, by rfl⟩ : syracuseStep 3492557 = 1309709) (by norm_num)
theorem B2329301 : Blo 1551473 2329301 := bbase (se 7 (by rfl) ⟨27296, by rfl⟩ : syracuseStep 2329301 = 54593) (by norm_num)
theorem B2018029 : Blo 1551473 2018029 := bbase (se 3 (by rfl) ⟨378380, by rfl⟩ : syracuseStep 2018029 = 756761) (by norm_num)
theorem B2329325 : Blo 1551473 2329325 := bbase (se 3 (by rfl) ⟨436748, by rfl⟩ : syracuseStep 2329325 = 873497) (by norm_num)
theorem B2329349 : Blo 1551473 2329349 := bbase (se 4 (by rfl) ⟨218376, by rfl⟩ : syracuseStep 2329349 = 436753) (by norm_num)
theorem B3492629 : Blo 1551473 3492629 := bbase (se 6 (by rfl) ⟨81858, by rfl⟩ : syracuseStep 3492629 = 163717) (by norm_num)
theorem B2329373 : Blo 1551473 2329373 := bbase (se 3 (by rfl) ⟨436757, by rfl⟩ : syracuseStep 2329373 = 873515) (by norm_num)
theorem B2329397 : Blo 1551473 2329397 := bbase (se 5 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 2329397 = 218381) (by norm_num)
theorem B2329421 : Blo 1551473 2329421 := bbase (se 3 (by rfl) ⟨436766, by rfl⟩ : syracuseStep 2329421 = 873533) (by norm_num)
theorem B3492701 : Blo 1551473 3492701 := bbase (se 3 (by rfl) ⟨654881, by rfl⟩ : syracuseStep 3492701 = 1309763) (by norm_num)
theorem B2329445 : Blo 1551473 2329445 := bbase (se 4 (by rfl) ⟨218385, by rfl⟩ : syracuseStep 2329445 = 436771) (by norm_num)
theorem B5237621 : Blo 1551473 5237621 := bbase (se 5 (by rfl) ⟨245513, by rfl⟩ : syracuseStep 5237621 = 491027) (by norm_num)
theorem B2657141 : Blo 1551473 2657141 := bbase (se 5 (by rfl) ⟨124553, by rfl⟩ : syracuseStep 2657141 = 249107) (by norm_num)
theorem B2329469 : Blo 1551473 2329469 := bbase (se 3 (by rfl) ⟨436775, by rfl⟩ : syracuseStep 2329469 = 873551) (by norm_num)
theorem B1657729 : Blo 1551473 1657729 := bbase (se 2 (by rfl) ⟨621648, by rfl⟩ : syracuseStep 1657729 = 1243297) (by norm_num)
theorem B2329493 : Blo 1551473 2329493 := bbase (se 6 (by rfl) ⟨54597, by rfl⟩ : syracuseStep 2329493 = 109195) (by norm_num)
theorem B3492773 : Blo 1551473 3492773 := bbase (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) (by norm_num)
theorem B2329517 : Blo 1551473 2329517 := bbase (se 3 (by rfl) ⟨436784, by rfl⟩ : syracuseStep 2329517 = 873569) (by norm_num)
theorem B2329541 : Blo 1551473 2329541 := bbase (se 4 (by rfl) ⟨218394, by rfl⟩ : syracuseStep 2329541 = 436789) (by norm_num)
theorem B2329565 : Blo 1551473 2329565 := bbase (se 3 (by rfl) ⟨436793, by rfl⟩ : syracuseStep 2329565 = 873587) (by norm_num)
theorem B3492845 : Blo 1551473 3492845 := bbase (se 3 (by rfl) ⟨654908, by rfl⟩ : syracuseStep 3492845 = 1309817) (by norm_num)
theorem B2329589 : Blo 1551473 2329589 := bbase (se 5 (by rfl) ⟨109199, by rfl⟩ : syracuseStep 2329589 = 218399) (by norm_num)
theorem B2329613 : Blo 1551473 2329613 := bbase (se 3 (by rfl) ⟨436802, by rfl⟩ : syracuseStep 2329613 = 873605) (by norm_num)
theorem B6630437 : Blo 1551473 6630437 := bbase (se 4 (by rfl) ⟨621603, by rfl⟩ : syracuseStep 6630437 = 1243207) (by norm_num)
theorem B2329637 : Blo 1551473 2329637 := bbase (se 4 (by rfl) ⟨218403, by rfl⟩ : syracuseStep 2329637 = 436807) (by norm_num)
theorem B3492917 : Blo 1551473 3492917 := bbase (se 5 (by rfl) ⟨163730, by rfl⟩ : syracuseStep 3492917 = 327461) (by norm_num)
theorem B1657913 : Blo 1551473 1657913 := bbase (se 2 (by rfl) ⟨621717, by rfl⟩ : syracuseStep 1657913 = 1243435) (by norm_num)
theorem B2329661 : Blo 1551473 2329661 := bbase (se 3 (by rfl) ⟨436811, by rfl⟩ : syracuseStep 2329661 = 873623) (by norm_num)
theorem B2329685 : Blo 1551473 2329685 := bbase (se 8 (by rfl) ⟨13650, by rfl⟩ : syracuseStep 2329685 = 27301) (by norm_num)
theorem B3542125 : Blo 1551473 3542125 := bbase (se 3 (by rfl) ⟨664148, by rfl⟩ : syracuseStep 3542125 = 1328297) (by norm_num)
theorem B2329709 : Blo 1551473 2329709 := bbase (se 3 (by rfl) ⟨436820, by rfl⟩ : syracuseStep 2329709 = 873641) (by norm_num)
theorem B3492989 : Blo 1551473 3492989 := bbase (se 3 (by rfl) ⟨654935, by rfl⟩ : syracuseStep 3492989 = 1309871) (by norm_num)
theorem B2329733 : Blo 1551473 2329733 := bbase (se 4 (by rfl) ⟨218412, by rfl⟩ : syracuseStep 2329733 = 436825) (by norm_num)
theorem B2329757 : Blo 1551473 2329757 := bbase (se 3 (by rfl) ⟨436829, by rfl⟩ : syracuseStep 2329757 = 873659) (by norm_num)
theorem B2329781 : Blo 1551473 2329781 := bbase (se 5 (by rfl) ⟨109208, by rfl⟩ : syracuseStep 2329781 = 218417) (by norm_num)
theorem B3493061 : Blo 1551473 3493061 := bbase (se 4 (by rfl) ⟨327474, by rfl⟩ : syracuseStep 3493061 = 654949) (by norm_num)
theorem B2329805 : Blo 1551473 2329805 := bbase (se 3 (by rfl) ⟨436838, by rfl⟩ : syracuseStep 2329805 = 873677) (by norm_num)
theorem B7859429 : Blo 1551473 7859429 := bbase (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) (by norm_num)
theorem B3730661 : Blo 1551473 3730661 := bbase (se 4 (by rfl) ⟨349749, by rfl⟩ : syracuseStep 3730661 = 699499) (by norm_num)
theorem B2329829 : Blo 1551473 2329829 := bbase (se 4 (by rfl) ⟨218421, by rfl⟩ : syracuseStep 2329829 = 436843) (by norm_num)
theorem B2329853 : Blo 1551473 2329853 := bbase (se 3 (by rfl) ⟨436847, by rfl⟩ : syracuseStep 2329853 = 873695) (by norm_num)
theorem B3493133 : Blo 1551473 3493133 := bbase (se 3 (by rfl) ⟨654962, by rfl⟩ : syracuseStep 3493133 = 1309925) (by norm_num)
theorem B2329877 : Blo 1551473 2329877 := bbase (se 6 (by rfl) ⟨54606, by rfl⟩ : syracuseStep 2329877 = 109213) (by norm_num)
theorem B3927325 : Blo 1551473 3927325 := bbase (se 3 (by rfl) ⟨736373, by rfl⟩ : syracuseStep 3927325 = 1472747) (by norm_num)
theorem B5238053 : Blo 1551473 5238053 := bbase (se 4 (by rfl) ⟨491067, by rfl⟩ : syracuseStep 5238053 = 982135) (by norm_num)
theorem B2329901 : Blo 1551473 2329901 := bbase (se 3 (by rfl) ⟨436856, by rfl⟩ : syracuseStep 2329901 = 873713) (by norm_num)
theorem B4197685 : Blo 1551473 4197685 := bbase (se 5 (by rfl) ⟨196766, by rfl⟩ : syracuseStep 4197685 = 393533) (by norm_num)
theorem B2329925 : Blo 1551473 2329925 := bbase (se 4 (by rfl) ⟨218430, by rfl⟩ : syracuseStep 2329925 = 436861) (by norm_num)
theorem B3493205 : Blo 1551473 3493205 := bbase (se 11 (by rfl) ⟨2558, by rfl⟩ : syracuseStep 3493205 = 5117) (by norm_num)
theorem B2329949 : Blo 1551473 2329949 := bbase (se 3 (by rfl) ⟨436865, by rfl⟩ : syracuseStep 2329949 = 873731) (by norm_num)
theorem B7458149 : Blo 1551473 7458149 := bbase (se 4 (by rfl) ⟨699201, by rfl⟩ : syracuseStep 7458149 = 1398403) (by norm_num)
theorem B4148597 : Blo 1551473 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B2329973 : Blo 1551473 2329973 := bbase (se 5 (by rfl) ⟨109217, by rfl⟩ : syracuseStep 2329973 = 218435) (by norm_num)
theorem B3927437 : Blo 1551473 3927437 := bbase (se 3 (by rfl) ⟨736394, by rfl⟩ : syracuseStep 3927437 = 1472789) (by norm_num)
theorem B2329997 : Blo 1551473 2329997 := bbase (se 3 (by rfl) ⟨436874, by rfl⟩ : syracuseStep 2329997 = 873749) (by norm_num)
theorem B3493277 : Blo 1551473 3493277 := bbase (se 3 (by rfl) ⟨654989, by rfl⟩ : syracuseStep 3493277 = 1309979) (by norm_num)
theorem B2330021 : Blo 1551473 2330021 := bbase (se 4 (by rfl) ⟨218439, by rfl⟩ : syracuseStep 2330021 = 436879) (by norm_num)
theorem B2330045 : Blo 1551473 2330045 := bbase (se 3 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 2330045 = 873767) (by norm_num)
theorem B2330069 : Blo 1551473 2330069 := bbase (se 7 (by rfl) ⟨27305, by rfl⟩ : syracuseStep 2330069 = 54611) (by norm_num)
theorem B3493349 : Blo 1551473 3493349 := bbase (se 4 (by rfl) ⟨327501, by rfl⟩ : syracuseStep 3493349 = 655003) (by norm_num)
theorem B2330093 : Blo 1551473 2330093 := bbase (se 3 (by rfl) ⟨436892, by rfl⟩ : syracuseStep 2330093 = 873785) (by norm_num)
theorem B2330117 : Blo 1551473 2330117 := bbase (se 4 (by rfl) ⟨218448, by rfl⟩ : syracuseStep 2330117 = 436897) (by norm_num)
theorem B2330141 : Blo 1551473 2330141 := bbase (se 3 (by rfl) ⟨436901, by rfl⟩ : syracuseStep 2330141 = 873803) (by norm_num)
theorem B3493421 : Blo 1551473 3493421 := bbase (se 3 (by rfl) ⟨655016, by rfl⟩ : syracuseStep 3493421 = 1310033) (by norm_num)
theorem B2330165 : Blo 1551473 2330165 := bbase (se 5 (by rfl) ⟨109226, by rfl⟩ : syracuseStep 2330165 = 218453) (by norm_num)
theorem B3731005 : Blo 1551473 3731005 := bbase (se 3 (by rfl) ⟨699563, by rfl⟩ : syracuseStep 3731005 = 1399127) (by norm_num)
theorem B3927629 : Blo 1551473 3927629 := bbase (se 3 (by rfl) ⟨736430, by rfl⟩ : syracuseStep 3927629 = 1472861) (by norm_num)
theorem B2330189 : Blo 1551473 2330189 := bbase (se 3 (by rfl) ⟨436910, by rfl⟩ : syracuseStep 2330189 = 873821) (by norm_num)
theorem B2240093 : Blo 1551473 2240093 := bbase (se 3 (by rfl) ⟨420017, by rfl⟩ : syracuseStep 2240093 = 840035) (by norm_num)
theorem B14921333 : Blo 1551473 14921333 := bbase (se 5 (by rfl) ⟨699437, by rfl⟩ : syracuseStep 14921333 = 1398875) (by norm_num)
theorem B3493493 : Blo 1551473 3493493 := bbase (se 5 (by rfl) ⟨163757, by rfl⟩ : syracuseStep 3493493 = 327515) (by norm_num)
theorem B3493565 : Blo 1551473 3493565 := bbase (se 3 (by rfl) ⟨655043, by rfl⟩ : syracuseStep 3493565 = 1310087) (by norm_num)
theorem B5893829 : Blo 1551473 5893829 := bbase (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) (by norm_num)
theorem B5238485 : Blo 1551473 5238485 := bbase (se 7 (by rfl) ⟨61388, by rfl⟩ : syracuseStep 5238485 = 122777) (by norm_num)
theorem B3493637 : Blo 1551473 3493637 := bbase (se 4 (by rfl) ⟨327528, by rfl⟩ : syracuseStep 3493637 = 655057) (by norm_num)
theorem B3731237 : Blo 1551473 3731237 := bbase (se 4 (by rfl) ⟨349803, by rfl⟩ : syracuseStep 3731237 = 699607) (by norm_num)
theorem B1658665 : Blo 1551473 1658665 := bbase (se 2 (by rfl) ⟨621999, by rfl⟩ : syracuseStep 1658665 = 1243999) (by norm_num)
theorem B2486069 : Blo 1551473 2486069 := bbase (se 5 (by rfl) ⟨116534, by rfl⟩ : syracuseStep 2486069 = 233069) (by norm_num)
theorem B3493709 : Blo 1551473 3493709 := bbase (se 3 (by rfl) ⟨655070, by rfl⟩ : syracuseStep 3493709 = 1310141) (by norm_num)
theorem B1658737 : Blo 1551473 1658737 := bbase (se 2 (by rfl) ⟨622026, by rfl⟩ : syracuseStep 1658737 = 1244053) (by norm_num)
theorem B4419461 : Blo 1551473 4419461 := bbase (se 4 (by rfl) ⟨414324, by rfl⟩ : syracuseStep 4419461 = 828649) (by norm_num)
theorem B3493781 : Blo 1551473 3493781 := bbase (se 6 (by rfl) ⟨81885, by rfl⟩ : syracuseStep 3493781 = 163771) (by norm_num)
theorem B3927973 : Blo 1551473 3927973 := bbase (se 4 (by rfl) ⟨368247, by rfl⟩ : syracuseStep 3927973 = 736495) (by norm_num)
theorem B3493853 : Blo 1551473 3493853 := bbase (se 3 (by rfl) ⟨655097, by rfl⟩ : syracuseStep 3493853 = 1310195) (by norm_num)
theorem B5894117 : Blo 1551473 5894117 := bbase (se 4 (by rfl) ⟨552573, by rfl⟩ : syracuseStep 5894117 = 1105147) (by norm_num)
theorem B3731429 : Blo 1551473 3731429 := bbase (se 4 (by rfl) ⟨349821, by rfl⟩ : syracuseStep 3731429 = 699643) (by norm_num)
theorem B2486261 : Blo 1551473 2486261 := bbase (se 5 (by rfl) ⟨116543, by rfl⟩ : syracuseStep 2486261 = 233087) (by norm_num)
theorem B6631429 : Blo 1551473 6631429 := bbase (se 4 (by rfl) ⟨621696, by rfl⟩ : syracuseStep 6631429 = 1243393) (by norm_num)
theorem B3928085 : Blo 1551473 3928085 := bbase (se 6 (by rfl) ⟨92064, by rfl⟩ : syracuseStep 3928085 = 184129) (by norm_num)
theorem B6295589 : Blo 1551473 6295589 := bbase (se 4 (by rfl) ⟨590211, by rfl⟩ : syracuseStep 6295589 = 1180423) (by norm_num)
theorem B3493925 : Blo 1551473 3493925 := bbase (se 4 (by rfl) ⟨327555, by rfl⟩ : syracuseStep 3493925 = 655111) (by norm_num)
theorem B3493997 : Blo 1551473 3493997 := bbase (se 3 (by rfl) ⟨655124, by rfl⟩ : syracuseStep 3493997 = 1310249) (by norm_num)
theorem B2486389 : Blo 1551473 2486389 := bbase (se 5 (by rfl) ⟨116549, by rfl⟩ : syracuseStep 2486389 = 233099) (by norm_num)
theorem B5238917 : Blo 1551473 5238917 := bbase (se 4 (by rfl) ⟨491148, by rfl⟩ : syracuseStep 5238917 = 982297) (by norm_num)
theorem B3494069 : Blo 1551473 3494069 := bbase (se 5 (by rfl) ⟨163784, by rfl⟩ : syracuseStep 3494069 = 327569) (by norm_num)
theorem B3928277 : Blo 1551473 3928277 := bbase (se 7 (by rfl) ⟨46034, by rfl⟩ : syracuseStep 3928277 = 92069) (by norm_num)
theorem B3494141 : Blo 1551473 3494141 := bbase (se 3 (by rfl) ⟨655151, by rfl⟩ : syracuseStep 3494141 = 1310303) (by norm_num)
theorem B3731717 : Blo 1551473 3731717 := bbase (se 4 (by rfl) ⟨349848, by rfl⟩ : syracuseStep 3731717 = 699697) (by norm_num)
theorem B1863965 : Blo 1551473 1863965 := bbase (se 3 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 1863965 = 698987) (by norm_num)
theorem B1863985 : Blo 1551473 1863985 := bbase (se 2 (by rfl) ⟨698994, by rfl⟩ : syracuseStep 1863985 = 1397989) (by norm_num)
theorem B3494213 : Blo 1551473 3494213 := bbase (se 4 (by rfl) ⟨327582, by rfl⟩ : syracuseStep 3494213 = 655165) (by norm_num)
theorem B2019713 : Blo 1551473 2019713 := bbase (se 2 (by rfl) ⟨757392, by rfl⟩ : syracuseStep 2019713 = 1514785) (by norm_num)
theorem B3494285 : Blo 1551473 3494285 := bbase (se 3 (by rfl) ⟨655178, by rfl⟩ : syracuseStep 3494285 = 1310357) (by norm_num)
theorem B11792789 : Blo 1551473 11792789 := bbase (se 6 (by rfl) ⟨276393, by rfl⟩ : syracuseStep 11792789 = 552787) (by norm_num)
theorem B1864129 : Blo 1551473 1864129 := bbase (se 2 (by rfl) ⟨699048, by rfl⟩ : syracuseStep 1864129 = 1398097) (by norm_num)
theorem B4198853 : Blo 1551473 4198853 := bbase (se 4 (by rfl) ⟨393642, by rfl⟩ : syracuseStep 4198853 = 787285) (by norm_num)
theorem B3314125 : Blo 1551473 3314125 := bbase (se 3 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 3314125 = 1242797) (by norm_num)
theorem B3494357 : Blo 1551473 3494357 := bbase (se 7 (by rfl) ⟨40949, by rfl⟩ : syracuseStep 3494357 = 81899) (by norm_num)
theorem B7180757 : Blo 1551473 7180757 := bbase (se 7 (by rfl) ⟨84149, by rfl⟩ : syracuseStep 7180757 = 168299) (by norm_num)
theorem B3781093 : Blo 1551473 3781093 := bbase (se 4 (by rfl) ⟨354477, by rfl⟩ : syracuseStep 3781093 = 708955) (by norm_num)
theorem B7860725 : Blo 1551473 7860725 := bbase (se 5 (by rfl) ⟨368471, by rfl⟩ : syracuseStep 7860725 = 736943) (by norm_num)
theorem B3494429 : Blo 1551473 3494429 := bbase (se 3 (by rfl) ⟨655205, by rfl⟩ : syracuseStep 3494429 = 1310411) (by norm_num)
theorem B4420133 : Blo 1551473 4420133 := bbase (se 4 (by rfl) ⟨414387, by rfl⟩ : syracuseStep 4420133 = 828775) (by norm_num)
theorem B3928621 : Blo 1551473 3928621 := bbase (se 3 (by rfl) ⟨736616, by rfl⟩ : syracuseStep 3928621 = 1473233) (by norm_num)
theorem B5239349 : Blo 1551473 5239349 := bbase (se 5 (by rfl) ⟨245594, by rfl⟩ : syracuseStep 5239349 = 491189) (by norm_num)
theorem B7459397 : Blo 1551473 7459397 := bbase (se 4 (by rfl) ⟨699318, by rfl⟩ : syracuseStep 7459397 = 1398637) (by norm_num)
theorem B3494501 : Blo 1551473 3494501 := bbase (se 4 (by rfl) ⟨327609, by rfl⟩ : syracuseStep 3494501 = 655219) (by norm_num)
theorem B3928733 : Blo 1551473 3928733 := bbase (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) (by norm_num)
theorem B3494573 : Blo 1551473 3494573 := bbase (se 3 (by rfl) ⟨655232, by rfl⟩ : syracuseStep 3494573 = 1310465) (by norm_num)
theorem B2487029 : Blo 1551473 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B3494645 : Blo 1551473 3494645 := bbase (se 5 (by rfl) ⟨163811, by rfl⟩ : syracuseStep 3494645 = 327623) (by norm_num)
theorem B2945821 : Blo 1551473 2945821 := bbase (se 3 (by rfl) ⟨552341, by rfl⟩ : syracuseStep 2945821 = 1104683) (by norm_num)
theorem B2618149 : Blo 1551473 2618149 := bbase (se 4 (by rfl) ⟨245451, by rfl⟩ : syracuseStep 2618149 = 490903) (by norm_num)
theorem B11785013 : Blo 1551473 11785013 := bbase (se 5 (by rfl) ⟨552422, by rfl⟩ : syracuseStep 11785013 = 1104845) (by norm_num)
theorem B3494717 : Blo 1551473 3494717 := bbase (se 3 (by rfl) ⟨655259, by rfl⟩ : syracuseStep 3494717 = 1310519) (by norm_num)
theorem B22688597 : Blo 1551473 22688597 := bbase (se 9 (by rfl) ⟨66470, by rfl⟩ : syracuseStep 22688597 = 132941) (by norm_num)
theorem B3928925 : Blo 1551473 3928925 := bbase (se 3 (by rfl) ⟨736673, by rfl⟩ : syracuseStep 3928925 = 1473347) (by norm_num)
theorem B2618237 : Blo 1551473 2618237 := bbase (se 3 (by rfl) ⟨490919, by rfl⟩ : syracuseStep 2618237 = 981839) (by norm_num)
theorem B3494789 : Blo 1551473 3494789 := bbase (se 4 (by rfl) ⟨327636, by rfl⟩ : syracuseStep 3494789 = 655273) (by norm_num)
theorem B1594273 : Blo 1551473 1594273 := bbase (se 2 (by rfl) ⟨597852, by rfl⟩ : syracuseStep 1594273 = 1195705) (by norm_num)
theorem B2945965 : Blo 1551473 2945965 := bbase (se 3 (by rfl) ⟨552368, by rfl⟩ : syracuseStep 2945965 = 1104737) (by norm_num)
theorem B3314621 : Blo 1551473 3314621 := bbase (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) (by norm_num)
theorem B3494861 : Blo 1551473 3494861 := bbase (se 3 (by rfl) ⟨655286, by rfl⟩ : syracuseStep 3494861 = 1310573) (by norm_num)
theorem B4420565 : Blo 1551473 4420565 := bbase (se 7 (by rfl) ⟨51803, by rfl⟩ : syracuseStep 4420565 = 103607) (by norm_num)
theorem B5239781 : Blo 1551473 5239781 := bbase (se 4 (by rfl) ⟨491229, by rfl⟩ : syracuseStep 5239781 = 982459) (by norm_num)
theorem B2618365 : Blo 1551473 2618365 := bbase (se 3 (by rfl) ⟨490943, by rfl⟩ : syracuseStep 2618365 = 981887) (by norm_num)
theorem B3494933 : Blo 1551473 3494933 := bbase (se 6 (by rfl) ⟨81912, by rfl⟩ : syracuseStep 3494933 = 163825) (by norm_num)
theorem B2946125 : Blo 1551473 2946125 := bbase (se 3 (by rfl) ⟨552398, by rfl⟩ : syracuseStep 2946125 = 1104797) (by norm_num)
theorem B2618453 : Blo 1551473 2618453 := bbase (se 8 (by rfl) ⟨15342, by rfl⟩ : syracuseStep 2618453 = 30685) (by norm_num)
theorem B3495005 : Blo 1551473 3495005 := bbase (se 3 (by rfl) ⟨655313, by rfl⟩ : syracuseStep 3495005 = 1310627) (by norm_num)
theorem B4035701 : Blo 1551473 4035701 := bbase (se 5 (by rfl) ⟨189173, by rfl⟩ : syracuseStep 4035701 = 378347) (by norm_num)
theorem B5895301 : Blo 1551473 5895301 := bbase (se 4 (by rfl) ⟨552684, by rfl⟩ : syracuseStep 5895301 = 1105369) (by norm_num)
theorem B3495077 : Blo 1551473 3495077 := bbase (se 4 (by rfl) ⟨327663, by rfl⟩ : syracuseStep 3495077 = 655327) (by norm_num)
theorem B3929269 : Blo 1551473 3929269 := bbase (se 5 (by rfl) ⟨184184, by rfl⟩ : syracuseStep 3929269 = 368369) (by norm_num)
theorem B2487485 : Blo 1551473 2487485 := bbase (se 3 (by rfl) ⟨466403, by rfl⟩ : syracuseStep 2487485 = 932807) (by norm_num)
theorem B2618581 : Blo 1551473 2618581 := bbase (se 7 (by rfl) ⟨30686, by rfl⟩ : syracuseStep 2618581 = 61373) (by norm_num)
theorem B2946269 : Blo 1551473 2946269 := bbase (se 3 (by rfl) ⟨552425, by rfl⟩ : syracuseStep 2946269 = 1104851) (by norm_num)
theorem B3495149 : Blo 1551473 3495149 := bbase (se 3 (by rfl) ⟨655340, by rfl⟩ : syracuseStep 3495149 = 1310681) (by norm_num)
theorem B3929381 : Blo 1551473 3929381 := bbase (se 4 (by rfl) ⟨368379, by rfl⟩ : syracuseStep 3929381 = 736759) (by norm_num)
theorem B7083301 : Blo 1551473 7083301 := bbase (se 4 (by rfl) ⟨664059, by rfl⟩ : syracuseStep 7083301 = 1328119) (by norm_num)
theorem B2618669 : Blo 1551473 2618669 := bbase (se 3 (by rfl) ⟨491000, by rfl⟩ : syracuseStep 2618669 = 982001) (by norm_num)
theorem B3495221 : Blo 1551473 3495221 := bbase (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) (by norm_num)
theorem B3495293 : Blo 1551473 3495293 := bbase (se 3 (by rfl) ⟨655367, by rfl⟩ : syracuseStep 3495293 = 1310735) (by norm_num)
theorem B5240213 : Blo 1551473 5240213 := bbase (se 6 (by rfl) ⟨122817, by rfl⟩ : syracuseStep 5240213 = 245635) (by norm_num)
theorem B2487709 : Blo 1551473 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B2209189 : Blo 1551473 2209189 := bbase (se 4 (by rfl) ⟨207111, by rfl⟩ : syracuseStep 2209189 = 414223) (by norm_num)
theorem B2618797 : Blo 1551473 2618797 := bbase (se 3 (by rfl) ⟨491024, by rfl⟩ : syracuseStep 2618797 = 982049) (by norm_num)
theorem B5895605 : Blo 1551473 5895605 := bbase (se 5 (by rfl) ⟨276356, by rfl⟩ : syracuseStep 5895605 = 552713) (by norm_num)
theorem B2987453 : Blo 1551473 2987453 := bbase (se 3 (by rfl) ⟨560147, by rfl⟩ : syracuseStep 2987453 = 1120295) (by norm_num)
theorem B10221013 : Blo 1551473 10221013 := bbase (se 7 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 10221013 = 239555) (by norm_num)
theorem B2487773 : Blo 1551473 2487773 := bbase (se 3 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 2487773 = 932915) (by norm_num)
theorem B3929573 : Blo 1551473 3929573 := bbase (se 4 (by rfl) ⟨368397, by rfl⟩ : syracuseStep 3929573 = 736795) (by norm_num)
theorem B2946557 : Blo 1551473 2946557 := bbase (se 3 (by rfl) ⟨552479, by rfl⟩ : syracuseStep 2946557 = 1104959) (by norm_num)
theorem B2618885 : Blo 1551473 2618885 := bbase (se 4 (by rfl) ⟨245520, by rfl⟩ : syracuseStep 2618885 = 491041) (by norm_num)
theorem B8844821 : Blo 1551473 8844821 := bbase (se 6 (by rfl) ⟨207300, by rfl⟩ : syracuseStep 8844821 = 414601) (by norm_num)
theorem B25187861 : Blo 1551473 25187861 := bbase (se 6 (by rfl) ⟨590340, by rfl⟩ : syracuseStep 25187861 = 1180681) (by norm_num)
theorem B9942581 : Blo 1551473 9942581 := bbase (se 5 (by rfl) ⟨466058, by rfl⟩ : syracuseStep 9942581 = 932117) (by norm_num)
theorem B1963597 : Blo 1551473 1963597 := bbase (se 3 (by rfl) ⟨368174, by rfl⟩ : syracuseStep 1963597 = 736349) (by norm_num)
theorem B14161493 : Blo 1551473 14161493 := bbase (se 8 (by rfl) ⟨82977, by rfl⟩ : syracuseStep 14161493 = 165955) (by norm_num)
theorem B2487901 : Blo 1551473 2487901 := bbase (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) (by norm_num)
theorem B2619013 : Blo 1551473 2619013 := bbase (se 4 (by rfl) ⟨245532, by rfl⟩ : syracuseStep 2619013 = 491065) (by norm_num)
theorem B2946709 : Blo 1551473 2946709 := bbase (se 6 (by rfl) ⟨69063, by rfl⟩ : syracuseStep 2946709 = 138127) (by norm_num)
theorem B1963693 : Blo 1551473 1963693 := bbase (se 3 (by rfl) ⟨368192, by rfl⟩ : syracuseStep 1963693 = 736385) (by norm_num)
theorem B4421317 : Blo 1551473 4421317 := bbase (se 4 (by rfl) ⟨414498, by rfl⟩ : syracuseStep 4421317 = 828997) (by norm_num)
theorem B2619101 : Blo 1551473 2619101 := bbase (se 3 (by rfl) ⟨491081, by rfl⟩ : syracuseStep 2619101 = 982163) (by norm_num)
theorem B7862021 : Blo 1551473 7862021 := bbase (se 4 (by rfl) ⟨737064, by rfl⟩ : syracuseStep 7862021 = 1474129) (by norm_num)
theorem B2209565 : Blo 1551473 2209565 := bbase (se 3 (by rfl) ⟨414293, by rfl⟩ : syracuseStep 2209565 = 828587) (by norm_num)
theorem B3315485 : Blo 1551473 3315485 := bbase (se 3 (by rfl) ⟨621653, by rfl⟩ : syracuseStep 3315485 = 1243307) (by norm_num)
theorem B3929917 : Blo 1551473 3929917 := bbase (se 3 (by rfl) ⟨736859, by rfl⟩ : syracuseStep 3929917 = 1473719) (by norm_num)
theorem B5240645 : Blo 1551473 5240645 := bbase (se 4 (by rfl) ⟨491310, by rfl⟩ : syracuseStep 5240645 = 982621) (by norm_num)
theorem B11196245 : Blo 1551473 11196245 := bbase (se 9 (by rfl) ⟨32801, by rfl⟩ : syracuseStep 11196245 = 65603) (by norm_num)
theorem B1963865 : Blo 1551473 1963865 := bbase (se 2 (by rfl) ⟨736449, by rfl⟩ : syracuseStep 1963865 = 1472899) (by norm_num)
theorem B2619229 : Blo 1551473 2619229 := bbase (se 3 (by rfl) ⟨491105, by rfl⟩ : syracuseStep 2619229 = 982211) (by norm_num)
theorem B1963921 : Blo 1551473 1963921 := bbase (se 2 (by rfl) ⟨736470, by rfl⟩ : syracuseStep 1963921 = 1472941) (by norm_num)
theorem B3315629 : Blo 1551473 3315629 := bbase (se 3 (by rfl) ⟨621680, by rfl⟩ : syracuseStep 3315629 = 1243361) (by norm_num)
theorem B3930029 : Blo 1551473 3930029 := bbase (se 3 (by rfl) ⟨736880, by rfl⟩ : syracuseStep 3930029 = 1473761) (by norm_num)
theorem B2619317 : Blo 1551473 2619317 := bbase (se 5 (by rfl) ⟨122780, by rfl⟩ : syracuseStep 2619317 = 245561) (by norm_num)
theorem B2947013 : Blo 1551473 2947013 := bbase (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) (by norm_num)
theorem B1964017 : Blo 1551473 1964017 := bbase (se 2 (by rfl) ⟨736506, by rfl⟩ : syracuseStep 1964017 = 1473013) (by norm_num)
theorem B2619445 : Blo 1551473 2619445 := bbase (se 5 (by rfl) ⟨122786, by rfl⟩ : syracuseStep 2619445 = 245573) (by norm_num)
theorem B3930221 : Blo 1551473 3930221 := bbase (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) (by norm_num)
theorem B2619533 : Blo 1551473 2619533 := bbase (se 3 (by rfl) ⟨491162, by rfl⟩ : syracuseStep 2619533 = 982325) (by norm_num)
theorem B1964189 : Blo 1551473 1964189 := bbase (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) (by norm_num)
theorem B1865921 : Blo 1551473 1865921 := bbase (se 2 (by rfl) ⟨699720, by rfl⟩ : syracuseStep 1865921 = 1399441) (by norm_num)
theorem B7182533 : Blo 1551473 7182533 := bbase (se 4 (by rfl) ⟨673362, by rfl⟩ : syracuseStep 7182533 = 1346725) (by norm_num)
theorem B1964245 : Blo 1551473 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B5241077 : Blo 1551473 5241077 := bbase (se 5 (by rfl) ⟨245675, by rfl⟩ : syracuseStep 5241077 = 491351) (by norm_num)
theorem B2619661 : Blo 1551473 2619661 := bbase (se 3 (by rfl) ⟨491186, by rfl⟩ : syracuseStep 2619661 = 982373) (by norm_num)
theorem B1554733 : Blo 1551473 1554733 := bbase (se 3 (by rfl) ⟨291512, by rfl⟩ : syracuseStep 1554733 = 583025) (by norm_num)
theorem B1964341 : Blo 1551473 1964341 := bbase (se 5 (by rfl) ⟨92078, by rfl⟩ : syracuseStep 1964341 = 184157) (by norm_num)
theorem B2619749 : Blo 1551473 2619749 := bbase (se 4 (by rfl) ⟨245601, by rfl⟩ : syracuseStep 2619749 = 491203) (by norm_num)
theorem B4970933 : Blo 1551473 4970933 := bbase (se 5 (by rfl) ⟨233012, by rfl⟩ : syracuseStep 4970933 = 466025) (by norm_num)
theorem B3930565 : Blo 1551473 3930565 := bbase (se 4 (by rfl) ⟨368490, by rfl⟩ : syracuseStep 3930565 = 736981) (by norm_num)
theorem B1964513 : Blo 1551473 1964513 := bbase (se 2 (by rfl) ⟨736692, by rfl⟩ : syracuseStep 1964513 = 1473385) (by norm_num)
theorem B2619877 : Blo 1551473 2619877 := bbase (se 4 (by rfl) ⟨245613, by rfl⟩ : syracuseStep 2619877 = 491227) (by norm_num)
theorem B1866253 : Blo 1551473 1866253 := bbase (se 3 (by rfl) ⟨349922, by rfl⟩ : syracuseStep 1866253 = 699845) (by norm_num)
theorem B1964569 : Blo 1551473 1964569 := bbase (se 2 (by rfl) ⟨736713, by rfl⟩ : syracuseStep 1964569 = 1473427) (by norm_num)
theorem B3930677 : Blo 1551473 3930677 := bbase (se 5 (by rfl) ⟨184250, by rfl⟩ : syracuseStep 3930677 = 368501) (by norm_num)
theorem B2619965 : Blo 1551473 2619965 := bbase (se 3 (by rfl) ⟨491243, by rfl⟩ : syracuseStep 2619965 = 982487) (by norm_num)
theorem B9837173 : Blo 1551473 9837173 := bbase (se 5 (by rfl) ⟨461117, by rfl⟩ : syracuseStep 9837173 = 922235) (by norm_num)
theorem B1964665 : Blo 1551473 1964665 := bbase (se 2 (by rfl) ⟨736749, by rfl⟩ : syracuseStep 1964665 = 1473499) (by norm_num)
theorem B3316373 : Blo 1551473 3316373 := bbase (se 6 (by rfl) ⟨77727, by rfl⟩ : syracuseStep 3316373 = 155455) (by norm_num)
theorem B5241509 : Blo 1551473 5241509 := bbase (se 4 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 5241509 = 982783) (by norm_num)
theorem B2947765 : Blo 1551473 2947765 := bbase (se 5 (by rfl) ⟨138176, by rfl⟩ : syracuseStep 2947765 = 276353) (by norm_num)
theorem B2620093 : Blo 1551473 2620093 := bbase (se 3 (by rfl) ⟨491267, by rfl⟩ : syracuseStep 2620093 = 982535) (by norm_num)
theorem B3930869 : Blo 1551473 3930869 := bbase (se 5 (by rfl) ⟨184259, by rfl⟩ : syracuseStep 3930869 = 368519) (by norm_num)
theorem B2620181 : Blo 1551473 2620181 := bbase (se 6 (by rfl) ⟨61410, by rfl⟩ : syracuseStep 2620181 = 122821) (by norm_num)
theorem B1964837 : Blo 1551473 1964837 := bbase (se 4 (by rfl) ⟨184203, by rfl⟩ : syracuseStep 1964837 = 368407) (by norm_num)
theorem B2947909 : Blo 1551473 2947909 := bbase (se 4 (by rfl) ⟨276366, by rfl⟩ : syracuseStep 2947909 = 552733) (by norm_num)
theorem B1964893 : Blo 1551473 1964893 := bbase (se 3 (by rfl) ⟨368417, by rfl⟩ : syracuseStep 1964893 = 736835) (by norm_num)
theorem B2620309 : Blo 1551473 2620309 := bbase (se 6 (by rfl) ⟨61413, by rfl⟩ : syracuseStep 2620309 = 122827) (by norm_num)
theorem B1964989 : Blo 1551473 1964989 := bbase (se 3 (by rfl) ⟨368435, by rfl⟩ : syracuseStep 1964989 = 736871) (by norm_num)
theorem B2948069 : Blo 1551473 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B2620397 : Blo 1551473 2620397 := bbase (se 3 (by rfl) ⟨491324, by rfl⟩ : syracuseStep 2620397 = 982649) (by norm_num)
theorem B7863317 : Blo 1551473 7863317 := bbase (se 6 (by rfl) ⟨184296, by rfl⟩ : syracuseStep 7863317 = 368593) (by norm_num)
theorem B3931213 : Blo 1551473 3931213 := bbase (se 3 (by rfl) ⟨737102, by rfl⟩ : syracuseStep 3931213 = 1474205) (by norm_num)
theorem B8387669 : Blo 1551473 8387669 := bbase (se 8 (by rfl) ⟨49146, by rfl⟩ : syracuseStep 8387669 = 98293) (by norm_num)
theorem B5241941 : Blo 1551473 5241941 := bbase (se 8 (by rfl) ⟨30714, by rfl⟩ : syracuseStep 5241941 = 61429) (by norm_num)
theorem B1965161 : Blo 1551473 1965161 := bbase (se 2 (by rfl) ⟨736935, by rfl⟩ : syracuseStep 1965161 = 1473871) (by norm_num)
theorem B2620525 : Blo 1551473 2620525 := bbase (se 3 (by rfl) ⟨491348, by rfl⟩ : syracuseStep 2620525 = 982697) (by norm_num)
theorem B2948213 : Blo 1551473 2948213 := bbase (se 5 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 2948213 = 276395) (by norm_num)
theorem B16776341 : Blo 1551473 16776341 := bbase (se 6 (by rfl) ⟨393195, by rfl⟩ : syracuseStep 16776341 = 786391) (by norm_num)
theorem B1965217 : Blo 1551473 1965217 := bbase (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) (by norm_num)
theorem B2210989 : Blo 1551473 2210989 := bbase (se 3 (by rfl) ⟨414560, by rfl⟩ : syracuseStep 2210989 = 829121) (by norm_num)
theorem B4971701 : Blo 1551473 4971701 := bbase (se 5 (by rfl) ⟨233048, by rfl⟩ : syracuseStep 4971701 = 466097) (by norm_num)
theorem B3931325 : Blo 1551473 3931325 := bbase (se 3 (by rfl) ⟨737123, by rfl⟩ : syracuseStep 3931325 = 1474247) (by norm_num)
theorem B2620613 : Blo 1551473 2620613 := bbase (se 4 (by rfl) ⟨245682, by rfl⟩ : syracuseStep 2620613 = 491365) (by norm_num)
theorem B8182997 : Blo 1551473 8182997 := bbase (se 7 (by rfl) ⟨95894, by rfl⟩ : syracuseStep 8182997 = 191789) (by norm_num)
theorem B1965313 : Blo 1551473 1965313 := bbase (se 2 (by rfl) ⟨736992, by rfl⟩ : syracuseStep 1965313 = 1473985) (by norm_num)
theorem B7462165 : Blo 1551473 7462165 := bbase (se 6 (by rfl) ⟨174894, by rfl⟩ : syracuseStep 7462165 = 349789) (by norm_num)
theorem B2620741 : Blo 1551473 2620741 := bbase (se 4 (by rfl) ⟨245694, by rfl⟩ : syracuseStep 2620741 = 491389) (by norm_num)
theorem B3931517 : Blo 1551473 3931517 := bbase (se 3 (by rfl) ⟨737159, by rfl⟩ : syracuseStep 3931517 = 1474319) (by norm_num)
theorem B3317125 : Blo 1551473 3317125 := bbase (se 4 (by rfl) ⟨310980, by rfl⟩ : syracuseStep 3317125 = 621961) (by norm_num)
theorem B10624405 : Blo 1551473 10624405 := bbase (se 6 (by rfl) ⟨249009, by rfl⟩ : syracuseStep 10624405 = 498019) (by norm_num)
theorem B2948501 : Blo 1551473 2948501 := bbase (se 6 (by rfl) ⟨69105, by rfl⟩ : syracuseStep 2948501 = 138211) (by norm_num)
theorem B2620829 : Blo 1551473 2620829 := bbase (se 3 (by rfl) ⟨491405, by rfl⟩ : syracuseStep 2620829 = 982811) (by norm_num)
theorem B1965485 : Blo 1551473 1965485 := bbase (se 3 (by rfl) ⟨368528, by rfl⟩ : syracuseStep 1965485 = 737057) (by norm_num)
theorem B7855541 : Blo 1551473 7855541 := bbase (se 5 (by rfl) ⟨368228, by rfl⟩ : syracuseStep 7855541 = 736457) (by norm_num)
theorem B1965541 : Blo 1551473 1965541 := bbase (se 4 (by rfl) ⟨184269, by rfl⟩ : syracuseStep 1965541 = 368539) (by norm_num)
theorem B5897717 : Blo 1551473 5897717 := bbase (se 5 (by rfl) ⟨276455, by rfl⟩ : syracuseStep 5897717 = 552911) (by norm_num)
theorem B5242373 : Blo 1551473 5242373 := bbase (se 4 (by rfl) ⟨491472, by rfl⟩ : syracuseStep 5242373 = 982945) (by norm_num)
theorem B3317269 : Blo 1551473 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B2620957 : Blo 1551473 2620957 := bbase (se 3 (by rfl) ⟨491429, by rfl⟩ : syracuseStep 2620957 = 982859) (by norm_num)
theorem B2948653 : Blo 1551473 2948653 := bbase (se 3 (by rfl) ⟨552872, by rfl⟩ : syracuseStep 2948653 = 1105745) (by norm_num)
theorem B1965637 : Blo 1551473 1965637 := bbase (se 4 (by rfl) ⟨184278, by rfl⟩ : syracuseStep 1965637 = 368557) (by norm_num)
theorem B7077461 : Blo 1551473 7077461 := bbase (se 8 (by rfl) ⟨41469, by rfl⟩ : syracuseStep 7077461 = 82939) (by norm_num)
theorem B3538541 : Blo 1551473 3538541 := bbase (se 3 (by rfl) ⟨663476, by rfl⟩ : syracuseStep 3538541 = 1326953) (by norm_num)
theorem B4251253 : Blo 1551473 4251253 := bbase (se 5 (by rfl) ⟨199277, by rfl⟩ : syracuseStep 4251253 = 398555) (by norm_num)
theorem B2621045 : Blo 1551473 2621045 := bbase (se 5 (by rfl) ⟨122861, by rfl⟩ : syracuseStep 2621045 = 245723) (by norm_num)
theorem B4972213 : Blo 1551473 4972213 := bbase (se 5 (by rfl) ⟨233072, by rfl⟩ : syracuseStep 4972213 = 466145) (by norm_num)
theorem B3931861 : Blo 1551473 3931861 := bbase (se 7 (by rfl) ⟨46076, by rfl⟩ : syracuseStep 3931861 = 92153) (by norm_num)
theorem B1965809 : Blo 1551473 1965809 := bbase (se 2 (by rfl) ⟨737178, by rfl⟩ : syracuseStep 1965809 = 1474357) (by norm_num)
theorem B2621173 : Blo 1551473 2621173 := bbase (se 5 (by rfl) ⟨122867, by rfl⟩ : syracuseStep 2621173 = 245735) (by norm_num)
theorem B2391805 : Blo 1551473 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B2211581 : Blo 1551473 2211581 := bbase (se 3 (by rfl) ⟨414671, by rfl⟩ : syracuseStep 2211581 = 829343) (by norm_num)
theorem B4718357 : Blo 1551473 4718357 := bbase (se 6 (by rfl) ⟨110586, by rfl⟩ : syracuseStep 4718357 = 221173) (by norm_num)
theorem B5898005 : Blo 1551473 5898005 := bbase (se 6 (by rfl) ⟨138234, by rfl⟩ : syracuseStep 5898005 = 276469) (by norm_num)
theorem B1965865 : Blo 1551473 1965865 := bbase (se 2 (by rfl) ⟨737199, by rfl⟩ : syracuseStep 1965865 = 1474399) (by norm_num)
theorem B3931973 : Blo 1551473 3931973 := bbase (se 4 (by rfl) ⟨368622, by rfl⟩ : syracuseStep 3931973 = 737245) (by norm_num)
theorem B2211661 : Blo 1551473 2211661 := bbase (se 3 (by rfl) ⟨414686, by rfl⟩ : syracuseStep 2211661 = 829373) (by norm_num)
theorem B2621261 : Blo 1551473 2621261 := bbase (se 3 (by rfl) ⟨491486, by rfl⟩ : syracuseStep 2621261 = 982973) (by norm_num)
theorem B1572697 : Blo 1551473 1572697 := bbase (se 2 (by rfl) ⟨589761, by rfl⟩ : syracuseStep 1572697 = 1179523) (by norm_num)
theorem B2948957 : Blo 1551473 2948957 := bbase (se 3 (by rfl) ⟨552929, by rfl⟩ : syracuseStep 2948957 = 1105859) (by norm_num)
theorem B1965961 : Blo 1551473 1965961 := bbase (se 2 (by rfl) ⟨737235, by rfl⟩ : syracuseStep 1965961 = 1474471) (by norm_num)
theorem B3317645 : Blo 1551473 3317645 := bbase (se 3 (by rfl) ⟨622058, by rfl⟩ : syracuseStep 3317645 = 1244117) (by norm_num)
theorem B5242805 : Blo 1551473 5242805 := bbase (se 5 (by rfl) ⟨245756, by rfl⟩ : syracuseStep 5242805 = 491513) (by norm_num)
theorem B2211781 : Blo 1551473 2211781 := bbase (se 4 (by rfl) ⟨207354, by rfl⟩ : syracuseStep 2211781 = 414709) (by norm_num)
theorem B2621389 : Blo 1551473 2621389 := bbase (se 3 (by rfl) ⟨491510, by rfl⟩ : syracuseStep 2621389 = 983021) (by norm_num)
theorem B2621443 : Blo 1551473 2621443 := bstep (se 1 (by rfl) ⟨1966082, by rfl⟩ : syracuseStep 2621443 = 3932165) B3932165
theorem B11796677 : Blo 1551473 11796677 := bstep (se 4 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 11796677 = 2211877) B2211877
theorem B2654513 : Blo 1551473 2654513 := bstep (se 2 (by rfl) ⟨995442, by rfl⟩ : syracuseStep 2654513 = 1990885) B1990885
theorem B19898693 : Blo 1551473 19898693 := bstep (se 4 (by rfl) ⟨1865502, by rfl⟩ : syracuseStep 19898693 = 3731005) B3731005
theorem B4194659 : Blo 1551473 4194659 := bstep (se 1 (by rfl) ⟨3145994, by rfl⟩ : syracuseStep 4194659 = 6291989) B6291989
theorem B4972931 : Blo 1551473 4972931 := bstep (se 1 (by rfl) ⟨3729698, by rfl⟩ : syracuseStep 4972931 = 7459397) B7459397
theorem B2654707 : Blo 1551473 2654707 := bstep (se 1 (by rfl) ⟨1991030, by rfl⟩ : syracuseStep 2654707 = 3982061) B3982061
theorem B2359811 : Blo 1551473 2359811 := bstep (se 1 (by rfl) ⟨1769858, by rfl⟩ : syracuseStep 2359811 = 3539717) B3539717
theorem B7856675 : Blo 1551473 7856675 := bstep (se 1 (by rfl) ⟨5892506, by rfl⟩ : syracuseStep 7856675 = 11785013) B11785013
theorem B1745491 : Blo 1551473 1745491 := bstep (se 1 (by rfl) ⟨1309118, by rfl⟩ : syracuseStep 1745491 = 2618237) B2618237
theorem B2327219 : Blo 1551473 2327219 := bstep (se 1 (by rfl) ⟨1745414, by rfl⟩ : syracuseStep 2327219 = 3490829) B3490829
theorem B2327249 : Blo 1551473 2327249 := bstep (se 2 (by rfl) ⟨872718, by rfl⟩ : syracuseStep 2327249 = 1745437) B1745437
theorem B2327267 : Blo 1551473 2327267 := bstep (se 1 (by rfl) ⟨1745450, by rfl⟩ : syracuseStep 2327267 = 3490901) B3490901
theorem B1745635 : Blo 1551473 1745635 := bstep (se 1 (by rfl) ⟨1309226, by rfl⟩ : syracuseStep 1745635 = 2618453) B2618453
theorem B2327297 : Blo 1551473 2327297 := bstep (se 2 (by rfl) ⟨872736, by rfl⟩ : syracuseStep 2327297 = 1745473) B1745473
theorem B4973329 : Blo 1551473 4973329 := bstep (se 2 (by rfl) ⟨1864998, by rfl⟩ : syracuseStep 4973329 = 3729997) B3729997
theorem B2327315 : Blo 1551473 2327315 := bstep (se 1 (by rfl) ⟨1745486, by rfl⟩ : syracuseStep 2327315 = 3490973) B3490973
theorem B2327345 : Blo 1551473 2327345 := bstep (se 2 (by rfl) ⟨872754, by rfl⟩ : syracuseStep 2327345 = 1745509) B1745509
theorem B2327363 : Blo 1551473 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B4973393 : Blo 1551473 4973393 := bstep (se 2 (by rfl) ⟨1865022, by rfl⟩ : syracuseStep 4973393 = 3730045) B3730045
theorem B2327393 : Blo 1551473 2327393 := bstep (se 2 (by rfl) ⟨872772, by rfl⟩ : syracuseStep 2327393 = 1745545) B1745545
theorem B2327411 : Blo 1551473 2327411 := bstep (se 1 (by rfl) ⟨1745558, by rfl⟩ : syracuseStep 2327411 = 3491117) B3491117
theorem B1745779 : Blo 1551473 1745779 := bstep (se 1 (by rfl) ⟨1309334, by rfl⟩ : syracuseStep 1745779 = 2618669) B2618669
theorem B2327441 : Blo 1551473 2327441 := bstep (se 2 (by rfl) ⟨872790, by rfl⟩ : syracuseStep 2327441 = 1745581) B1745581
theorem B2327459 : Blo 1551473 2327459 := bstep (se 1 (by rfl) ⟨1745594, by rfl⟩ : syracuseStep 2327459 = 3491189) B3491189
theorem B2327489 : Blo 1551473 2327489 := bstep (se 2 (by rfl) ⟨872808, by rfl⟩ : syracuseStep 2327489 = 1745617) B1745617
theorem B2098129 : Blo 1551473 2098129 := bstep (se 2 (by rfl) ⟨786798, by rfl⟩ : syracuseStep 2098129 = 1573597) B1573597
theorem B2327507 : Blo 1551473 2327507 := bstep (se 1 (by rfl) ⟨1745630, by rfl⟩ : syracuseStep 2327507 = 3491261) B3491261
theorem B2327537 : Blo 1551473 2327537 := bstep (se 2 (by rfl) ⟨872826, by rfl⟩ : syracuseStep 2327537 = 1745653) B1745653
theorem B2327555 : Blo 1551473 2327555 := bstep (se 1 (by rfl) ⟨1745666, by rfl⟩ : syracuseStep 2327555 = 3491333) B3491333
theorem B1745923 : Blo 1551473 1745923 := bstep (se 1 (by rfl) ⟨1309442, by rfl⟩ : syracuseStep 1745923 = 2618885) B2618885
theorem B2327585 : Blo 1551473 2327585 := bstep (se 2 (by rfl) ⟨872844, by rfl⟩ : syracuseStep 2327585 = 1745689) B1745689
theorem B6628387 : Blo 1551473 6628387 := bstep (se 1 (by rfl) ⟨4971290, by rfl⟩ : syracuseStep 6628387 = 9942581) B9942581
theorem B3490865 : Blo 1551473 3490865 := bstep (se 2 (by rfl) ⟨1309074, by rfl⟩ : syracuseStep 3490865 = 2618149) B2618149
theorem B2327603 : Blo 1551473 2327603 := bstep (se 1 (by rfl) ⟨1745702, by rfl⟩ : syracuseStep 2327603 = 3491405) B3491405
theorem B3490883 : Blo 1551473 3490883 := bstep (se 1 (by rfl) ⟨2618162, by rfl⟩ : syracuseStep 3490883 = 5236325) B5236325
theorem B2327633 : Blo 1551473 2327633 := bstep (se 2 (by rfl) ⟨872862, by rfl⟩ : syracuseStep 2327633 = 1745725) B1745725
theorem B2327651 : Blo 1551473 2327651 := bstep (se 1 (by rfl) ⟨1745738, by rfl⟩ : syracuseStep 2327651 = 3491477) B3491477
theorem B2327681 : Blo 1551473 2327681 := bstep (se 2 (by rfl) ⟨872880, by rfl⟩ : syracuseStep 2327681 = 1745761) B1745761
theorem B2327699 : Blo 1551473 2327699 := bstep (se 1 (by rfl) ⟨1745774, by rfl⟩ : syracuseStep 2327699 = 3491549) B3491549
theorem B1746067 : Blo 1551473 1746067 := bstep (se 1 (by rfl) ⟨1309550, by rfl⟩ : syracuseStep 1746067 = 2619101) B2619101
theorem B2327729 : Blo 1551473 2327729 := bstep (se 2 (by rfl) ⟨872898, by rfl⟩ : syracuseStep 2327729 = 1745797) B1745797
theorem B2327747 : Blo 1551473 2327747 := bstep (se 1 (by rfl) ⟨1745810, by rfl⟩ : syracuseStep 2327747 = 3491621) B3491621
theorem B1574083 : Blo 1551473 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B2327777 : Blo 1551473 2327777 := bstep (se 2 (by rfl) ⟨872916, by rfl⟩ : syracuseStep 2327777 = 1745833) B1745833
theorem B7464163 : Blo 1551473 7464163 := bstep (se 1 (by rfl) ⟨5598122, by rfl⟩ : syracuseStep 7464163 = 11196245) B11196245
theorem B2327795 : Blo 1551473 2327795 := bstep (se 1 (by rfl) ⟨1745846, by rfl⟩ : syracuseStep 2327795 = 3491693) B3491693
theorem B2327825 : Blo 1551473 2327825 := bstep (se 2 (by rfl) ⟨872934, by rfl⟩ : syracuseStep 2327825 = 1745869) B1745869
theorem B2327843 : Blo 1551473 2327843 := bstep (se 1 (by rfl) ⟨1745882, by rfl⟩ : syracuseStep 2327843 = 3491765) B3491765
theorem B1746211 : Blo 1551473 1746211 := bstep (se 1 (by rfl) ⟨1309658, by rfl⟩ : syracuseStep 1746211 = 2619317) B2619317
theorem B2327873 : Blo 1551473 2327873 := bstep (se 2 (by rfl) ⟨872952, by rfl⟩ : syracuseStep 2327873 = 1745905) B1745905
theorem B7857485 : Blo 1551473 7857485 := bstep (se 3 (by rfl) ⟨1473278, by rfl⟩ : syracuseStep 7857485 = 2946557) B2946557
theorem B3491153 : Blo 1551473 3491153 := bstep (se 2 (by rfl) ⟨1309182, by rfl⟩ : syracuseStep 3491153 = 2618365) B2618365
theorem B2327891 : Blo 1551473 2327891 := bstep (se 1 (by rfl) ⟨1745918, by rfl⟩ : syracuseStep 2327891 = 3491837) B3491837
theorem B3491171 : Blo 1551473 3491171 := bstep (se 1 (by rfl) ⟨2618378, by rfl⟩ : syracuseStep 3491171 = 5236757) B5236757
theorem B2327921 : Blo 1551473 2327921 := bstep (se 2 (by rfl) ⟨872970, by rfl⟩ : syracuseStep 2327921 = 1745941) B1745941
theorem B2327939 : Blo 1551473 2327939 := bstep (se 1 (by rfl) ⟨1745954, by rfl⟩ : syracuseStep 2327939 = 3491909) B3491909
theorem B4195729 : Blo 1551473 4195729 := bstep (se 2 (by rfl) ⟨1573398, by rfl⟩ : syracuseStep 4195729 = 3146797) B3146797
theorem B2327969 : Blo 1551473 2327969 := bstep (se 2 (by rfl) ⟨872988, by rfl⟩ : syracuseStep 2327969 = 1745977) B1745977
theorem B2327987 : Blo 1551473 2327987 := bstep (se 1 (by rfl) ⟨1745990, by rfl⟩ : syracuseStep 2327987 = 3491981) B3491981
theorem B1746355 : Blo 1551473 1746355 := bstep (se 1 (by rfl) ⟨1309766, by rfl⟩ : syracuseStep 1746355 = 2619533) B2619533
theorem B2328017 : Blo 1551473 2328017 := bstep (se 2 (by rfl) ⟨873006, by rfl⟩ : syracuseStep 2328017 = 1746013) B1746013
theorem B2328035 : Blo 1551473 2328035 := bstep (se 1 (by rfl) ⟨1746026, by rfl⟩ : syracuseStep 2328035 = 3492053) B3492053
theorem B15943139 : Blo 1551473 15943139 := bstep (se 1 (by rfl) ⟨11957354, by rfl⟩ : syracuseStep 15943139 = 23914709) B23914709
theorem B2328065 : Blo 1551473 2328065 := bstep (se 2 (by rfl) ⟨873024, by rfl⟩ : syracuseStep 2328065 = 1746049) B1746049
theorem B13264397 : Blo 1551473 13264397 := bstep (se 3 (by rfl) ⟨2487074, by rfl⟩ : syracuseStep 13264397 = 4974149) B4974149
theorem B2328083 : Blo 1551473 2328083 := bstep (se 1 (by rfl) ⟨1746062, by rfl⟩ : syracuseStep 2328083 = 3492125) B3492125
theorem B2328113 : Blo 1551473 2328113 := bstep (se 2 (by rfl) ⟨873042, by rfl⟩ : syracuseStep 2328113 = 1746085) B1746085
theorem B2328131 : Blo 1551473 2328131 := bstep (se 1 (by rfl) ⟨1746098, by rfl⟩ : syracuseStep 2328131 = 3492197) B3492197
theorem B1746499 : Blo 1551473 1746499 := bstep (se 1 (by rfl) ⟨1309874, by rfl⟩ : syracuseStep 1746499 = 2619749) B2619749
theorem B8291909 : Blo 1551473 8291909 := bstep (se 4 (by rfl) ⟨777366, by rfl⟩ : syracuseStep 8291909 = 1554733) B1554733
theorem B5973581 : Blo 1551473 5973581 := bstep (se 3 (by rfl) ⟨1120046, by rfl⟩ : syracuseStep 5973581 = 2240093) B2240093
theorem B2328161 : Blo 1551473 2328161 := bstep (se 2 (by rfl) ⟨873060, by rfl⟩ : syracuseStep 2328161 = 1746121) B1746121
theorem B3491441 : Blo 1551473 3491441 := bstep (se 2 (by rfl) ⟨1309290, by rfl⟩ : syracuseStep 3491441 = 2618581) B2618581
theorem B2328179 : Blo 1551473 2328179 := bstep (se 1 (by rfl) ⟨1746134, by rfl⟩ : syracuseStep 2328179 = 3492269) B3492269
theorem B3491459 : Blo 1551473 3491459 := bstep (se 1 (by rfl) ⟨2618594, by rfl⟩ : syracuseStep 3491459 = 5237189) B5237189
theorem B2328209 : Blo 1551473 2328209 := bstep (se 2 (by rfl) ⟨873078, by rfl⟩ : syracuseStep 2328209 = 1746157) B1746157
theorem B2328227 : Blo 1551473 2328227 := bstep (se 1 (by rfl) ⟨1746170, by rfl⟩ : syracuseStep 2328227 = 3492341) B3492341
theorem B2328257 : Blo 1551473 2328257 := bstep (se 2 (by rfl) ⟨873096, by rfl⟩ : syracuseStep 2328257 = 1746193) B1746193
theorem B5236433 : Blo 1551473 5236433 := bstep (se 2 (by rfl) ⟨1963662, by rfl⟩ : syracuseStep 5236433 = 3927325) B3927325
theorem B2328275 : Blo 1551473 2328275 := bstep (se 1 (by rfl) ⟨1746206, by rfl⟩ : syracuseStep 2328275 = 3492413) B3492413
theorem B1746643 : Blo 1551473 1746643 := bstep (se 1 (by rfl) ⟨1309982, by rfl⟩ : syracuseStep 1746643 = 2619965) B2619965
theorem B2328305 : Blo 1551473 2328305 := bstep (se 2 (by rfl) ⟨873114, by rfl⟩ : syracuseStep 2328305 = 1746229) B1746229
theorem B5596913 : Blo 1551473 5596913 := bstep (se 2 (by rfl) ⟨2098842, by rfl⟩ : syracuseStep 5596913 = 4197685) B4197685
theorem B2361089 : Blo 1551473 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B2328323 : Blo 1551473 2328323 := bstep (se 1 (by rfl) ⟨1746242, by rfl⟩ : syracuseStep 2328323 = 3492485) B3492485
theorem B2328353 : Blo 1551473 2328353 := bstep (se 2 (by rfl) ⟨873132, by rfl⟩ : syracuseStep 2328353 = 1746265) B1746265
theorem B2328371 : Blo 1551473 2328371 := bstep (se 1 (by rfl) ⟨1746278, by rfl⟩ : syracuseStep 2328371 = 3492557) B3492557
theorem B2328401 : Blo 1551473 2328401 := bstep (se 2 (by rfl) ⟨873150, by rfl⟩ : syracuseStep 2328401 = 1746301) B1746301
theorem B2328419 : Blo 1551473 2328419 := bstep (se 1 (by rfl) ⟨1746314, by rfl⟩ : syracuseStep 2328419 = 3492629) B3492629
theorem B1746787 : Blo 1551473 1746787 := bstep (se 1 (by rfl) ⟨1310090, by rfl⟩ : syracuseStep 1746787 = 2620181) B2620181
theorem B14165873 : Blo 1551473 14165873 := bstep (se 2 (by rfl) ⟨5312202, by rfl⟩ : syracuseStep 14165873 = 10624405) B10624405
theorem B2328449 : Blo 1551473 2328449 := bstep (se 2 (by rfl) ⟨873168, by rfl⟩ : syracuseStep 2328449 = 1746337) B1746337
theorem B3491729 : Blo 1551473 3491729 := bstep (se 2 (by rfl) ⟨1309398, by rfl⟩ : syracuseStep 3491729 = 2618797) B2618797
theorem B2328467 : Blo 1551473 2328467 := bstep (se 1 (by rfl) ⟨1746350, by rfl⟩ : syracuseStep 2328467 = 3492701) B3492701
theorem B3491747 : Blo 1551473 3491747 := bstep (se 1 (by rfl) ⟨2618810, by rfl⟩ : syracuseStep 3491747 = 5237621) B5237621
theorem B1771427 : Blo 1551473 1771427 := bstep (se 1 (by rfl) ⟨1328570, by rfl⟩ : syracuseStep 1771427 = 2657141) B2657141
theorem B2328497 : Blo 1551473 2328497 := bstep (se 2 (by rfl) ⟨873186, by rfl⟩ : syracuseStep 2328497 = 1746373) B1746373
theorem B2328515 : Blo 1551473 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B2328545 : Blo 1551473 2328545 := bstep (se 2 (by rfl) ⟨873204, by rfl⟩ : syracuseStep 2328545 = 1746409) B1746409
theorem B2328563 : Blo 1551473 2328563 := bstep (se 1 (by rfl) ⟨1746422, by rfl⟩ : syracuseStep 2328563 = 3492845) B3492845
theorem B1746931 : Blo 1551473 1746931 := bstep (se 1 (by rfl) ⟨1310198, by rfl⟩ : syracuseStep 1746931 = 2620397) B2620397
theorem B8841221 : Blo 1551473 8841221 := bstep (se 4 (by rfl) ⟨828864, by rfl⟩ : syracuseStep 8841221 = 1657729) B1657729
theorem B5310481 : Blo 1551473 5310481 := bstep (se 2 (by rfl) ⟨1991430, by rfl⟩ : syracuseStep 5310481 = 3982861) B3982861
theorem B2328593 : Blo 1551473 2328593 := bstep (se 2 (by rfl) ⟨873222, by rfl⟩ : syracuseStep 2328593 = 1746445) B1746445
theorem B2328611 : Blo 1551473 2328611 := bstep (se 1 (by rfl) ⟨1746458, by rfl⟩ : syracuseStep 2328611 = 3492917) B3492917
theorem B2328641 : Blo 1551473 2328641 := bstep (se 2 (by rfl) ⟨873240, by rfl⟩ : syracuseStep 2328641 = 1746481) B1746481
theorem B5892173 : Blo 1551473 5892173 := bstep (se 3 (by rfl) ⟨1104782, by rfl⟩ : syracuseStep 5892173 = 2209565) B2209565
theorem B2328659 : Blo 1551473 2328659 := bstep (se 1 (by rfl) ⟨1746494, by rfl⟩ : syracuseStep 2328659 = 3492989) B3492989
theorem B11184227 : Blo 1551473 11184227 := bstep (se 1 (by rfl) ⟨8388170, by rfl⟩ : syracuseStep 11184227 = 16776341) B16776341
theorem B2328689 : Blo 1551473 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B2328707 : Blo 1551473 2328707 := bstep (se 1 (by rfl) ⟨1746530, by rfl⟩ : syracuseStep 2328707 = 3493061) B3493061
theorem B1747075 : Blo 1551473 1747075 := bstep (se 1 (by rfl) ⟨1310306, by rfl⟩ : syracuseStep 1747075 = 2620613) B2620613
theorem B2328737 : Blo 1551473 2328737 := bstep (se 2 (by rfl) ⟨873276, by rfl⟩ : syracuseStep 2328737 = 1746553) B1746553
theorem B3492017 : Blo 1551473 3492017 := bstep (se 2 (by rfl) ⟨1309506, by rfl⟩ : syracuseStep 3492017 = 2619013) B2619013
theorem B2328755 : Blo 1551473 2328755 := bstep (se 1 (by rfl) ⟨1746566, by rfl⟩ : syracuseStep 2328755 = 3493133) B3493133
theorem B3492035 : Blo 1551473 3492035 := bstep (se 1 (by rfl) ⟨2619026, by rfl⟩ : syracuseStep 3492035 = 5238053) B5238053
theorem B2328785 : Blo 1551473 2328785 := bstep (se 2 (by rfl) ⟨873294, by rfl⟩ : syracuseStep 2328785 = 1746589) B1746589
theorem B2328803 : Blo 1551473 2328803 := bstep (se 1 (by rfl) ⟨1746602, by rfl⟩ : syracuseStep 2328803 = 3493205) B3493205
theorem B5236973 : Blo 1551473 5236973 := bstep (se 3 (by rfl) ⟨981932, by rfl⟩ : syracuseStep 5236973 = 1963865) B1963865
theorem B6629617 : Blo 1551473 6629617 := bstep (se 2 (by rfl) ⟨2486106, by rfl⟩ : syracuseStep 6629617 = 4972213) B4972213
theorem B2328833 : Blo 1551473 2328833 := bstep (se 2 (by rfl) ⟨873312, by rfl⟩ : syracuseStep 2328833 = 1746625) B1746625
theorem B2328851 : Blo 1551473 2328851 := bstep (se 1 (by rfl) ⟨1746638, by rfl⟩ : syracuseStep 2328851 = 3493277) B3493277
theorem B1747219 : Blo 1551473 1747219 := bstep (se 1 (by rfl) ⟨1310414, by rfl⟩ : syracuseStep 1747219 = 2620829) B2620829
theorem B5237027 : Blo 1551473 5237027 := bstep (se 1 (by rfl) ⟨3927770, by rfl⟩ : syracuseStep 5237027 = 7855541) B7855541
theorem B9439537 : Blo 1551473 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B2328881 : Blo 1551473 2328881 := bstep (se 2 (by rfl) ⟨873330, by rfl⟩ : syracuseStep 2328881 = 1746661) B1746661
theorem B2328899 : Blo 1551473 2328899 := bstep (se 1 (by rfl) ⟨1746674, by rfl⟩ : syracuseStep 2328899 = 3493349) B3493349
theorem B3189073 : Blo 1551473 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B2328929 : Blo 1551473 2328929 := bstep (se 2 (by rfl) ⟨873348, by rfl⟩ : syracuseStep 2328929 = 1746697) B1746697
theorem B2328947 : Blo 1551473 2328947 := bstep (se 1 (by rfl) ⟨1746710, by rfl⟩ : syracuseStep 2328947 = 3493421) B3493421
theorem B2328977 : Blo 1551473 2328977 := bstep (se 2 (by rfl) ⟨873366, by rfl⟩ : syracuseStep 2328977 = 1746733) B1746733
theorem B9947555 : Blo 1551473 9947555 := bstep (se 1 (by rfl) ⟨7460666, by rfl⟩ : syracuseStep 9947555 = 14921333) B14921333
theorem B2328995 : Blo 1551473 2328995 := bstep (se 1 (by rfl) ⟨1746746, by rfl⟩ : syracuseStep 2328995 = 3493493) B3493493
theorem B1747363 : Blo 1551473 1747363 := bstep (se 1 (by rfl) ⟨1310522, by rfl⟩ : syracuseStep 1747363 = 2621045) B2621045
theorem B2329025 : Blo 1551473 2329025 := bstep (se 2 (by rfl) ⟨873384, by rfl⟩ : syracuseStep 2329025 = 1746769) B1746769
theorem B9439685 : Blo 1551473 9439685 := bstep (se 4 (by rfl) ⟨884970, by rfl⟩ : syracuseStep 9439685 = 1769941) B1769941
theorem B8391109 : Blo 1551473 8391109 := bstep (se 4 (by rfl) ⟨786666, by rfl⟩ : syracuseStep 8391109 = 1573333) B1573333
theorem B3492305 : Blo 1551473 3492305 := bstep (se 2 (by rfl) ⟨1309614, by rfl⟩ : syracuseStep 3492305 = 2619229) B2619229
theorem B2329043 : Blo 1551473 2329043 := bstep (se 1 (by rfl) ⟨1746782, by rfl⟩ : syracuseStep 2329043 = 3493565) B3493565
theorem B3492323 : Blo 1551473 3492323 := bstep (se 1 (by rfl) ⟨2619242, by rfl⟩ : syracuseStep 3492323 = 5238485) B5238485
theorem B2329073 : Blo 1551473 2329073 := bstep (se 2 (by rfl) ⟨873402, by rfl⟩ : syracuseStep 2329073 = 1746805) B1746805
theorem B2329091 : Blo 1551473 2329091 := bstep (se 1 (by rfl) ⟨1746818, by rfl⟩ : syracuseStep 2329091 = 3493637) B3493637
theorem B1657379 : Blo 1551473 1657379 := bstep (se 1 (by rfl) ⟨1243034, by rfl⟩ : syracuseStep 1657379 = 2486069) B2486069
theorem B2329121 : Blo 1551473 2329121 := bstep (se 2 (by rfl) ⟨873420, by rfl⟩ : syracuseStep 2329121 = 1746841) B1746841
theorem B5237297 : Blo 1551473 5237297 := bstep (se 2 (by rfl) ⟨1963986, by rfl⟩ : syracuseStep 5237297 = 3927973) B3927973
theorem B26528309 : Blo 1551473 26528309 := bstep (se 5 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 26528309 = 2487029) B2487029
theorem B2329139 : Blo 1551473 2329139 := bstep (se 1 (by rfl) ⟨1746854, by rfl⟩ : syracuseStep 2329139 = 3493709) B3493709
theorem B1747507 : Blo 1551473 1747507 := bstep (se 1 (by rfl) ⟨1310630, by rfl⟩ : syracuseStep 1747507 = 2621261) B2621261
theorem B2329169 : Blo 1551473 2329169 := bstep (se 2 (by rfl) ⟨873438, by rfl⟩ : syracuseStep 2329169 = 1746877) B1746877
theorem B2329187 : Blo 1551473 2329187 := bstep (se 1 (by rfl) ⟨1746890, by rfl⟩ : syracuseStep 2329187 = 3493781) B3493781
theorem B2329217 : Blo 1551473 2329217 := bstep (se 2 (by rfl) ⟨873456, by rfl⟩ : syracuseStep 2329217 = 1746913) B1746913
theorem B2329235 : Blo 1551473 2329235 := bstep (se 1 (by rfl) ⟨1746926, by rfl⟩ : syracuseStep 2329235 = 3493853) B3493853
theorem B1657507 : Blo 1551473 1657507 := bstep (se 1 (by rfl) ⟨1243130, by rfl⟩ : syracuseStep 1657507 = 2486261) B2486261
theorem B8841905 : Blo 1551473 8841905 := bstep (se 2 (by rfl) ⟨3315714, by rfl⟩ : syracuseStep 8841905 = 6631429) B6631429
theorem B2329265 : Blo 1551473 2329265 := bstep (se 2 (by rfl) ⟨873474, by rfl⟩ : syracuseStep 2329265 = 1746949) B1746949
theorem B4197059 : Blo 1551473 4197059 := bstep (se 1 (by rfl) ⟨3147794, by rfl⟩ : syracuseStep 4197059 = 6295589) B6295589
theorem B2329283 : Blo 1551473 2329283 := bstep (se 1 (by rfl) ⟨1746962, by rfl⟩ : syracuseStep 2329283 = 3493925) B3493925
theorem B1747651 : Blo 1551473 1747651 := bstep (se 1 (by rfl) ⟨1310738, by rfl⟩ : syracuseStep 1747651 = 2621477) B2621477
theorem B2329313 : Blo 1551473 2329313 := bstep (se 2 (by rfl) ⟨873492, by rfl⟩ : syracuseStep 2329313 = 1746985) B1746985
theorem B5597923 : Blo 1551473 5597923 := bstep (se 1 (by rfl) ⟨4198442, by rfl⟩ : syracuseStep 5597923 = 8396885) B8396885
theorem B3492593 : Blo 1551473 3492593 := bstep (se 2 (by rfl) ⟨1309722, by rfl⟩ : syracuseStep 3492593 = 2619445) B2619445
theorem B2329331 : Blo 1551473 2329331 := bstep (se 1 (by rfl) ⟨1746998, by rfl⟩ : syracuseStep 2329331 = 3493997) B3493997
theorem B3492611 : Blo 1551473 3492611 := bstep (se 1 (by rfl) ⟨2619458, by rfl⟩ : syracuseStep 3492611 = 5238917) B5238917
theorem B17681165 : Blo 1551473 17681165 := bstep (se 3 (by rfl) ⟨3315218, by rfl⟩ : syracuseStep 17681165 = 6630437) B6630437
theorem B2329361 : Blo 1551473 2329361 := bstep (se 2 (by rfl) ⟨873510, by rfl⟩ : syracuseStep 2329361 = 1747021) B1747021
theorem B2329379 : Blo 1551473 2329379 := bstep (se 1 (by rfl) ⟨1747034, by rfl⟩ : syracuseStep 2329379 = 3494069) B3494069
theorem B2329409 : Blo 1551473 2329409 := bstep (se 2 (by rfl) ⟨873528, by rfl⟩ : syracuseStep 2329409 = 1747057) B1747057
theorem B2329427 : Blo 1551473 2329427 := bstep (se 1 (by rfl) ⟨1747070, by rfl⟩ : syracuseStep 2329427 = 3494141) B3494141
theorem B2329457 : Blo 1551473 2329457 := bstep (se 2 (by rfl) ⟨873546, by rfl⟩ : syracuseStep 2329457 = 1747093) B1747093
theorem B2329475 : Blo 1551473 2329475 := bstep (se 1 (by rfl) ⟨1747106, by rfl⟩ : syracuseStep 2329475 = 3494213) B3494213
theorem B22367117 : Blo 1551473 22367117 := bstep (se 3 (by rfl) ⟨4193834, by rfl⟩ : syracuseStep 22367117 = 8387669) B8387669
theorem B2329505 : Blo 1551473 2329505 := bstep (se 2 (by rfl) ⟨873564, by rfl⟩ : syracuseStep 2329505 = 1747129) B1747129
theorem B2329523 : Blo 1551473 2329523 := bstep (se 1 (by rfl) ⟨1747142, by rfl⟩ : syracuseStep 2329523 = 3494285) B3494285
theorem B5041091 : Blo 1551473 5041091 := bstep (se 1 (by rfl) ⟨3780818, by rfl⟩ : syracuseStep 5041091 = 7561637) B7561637
theorem B2329553 : Blo 1551473 2329553 := bstep (se 2 (by rfl) ⟨873582, by rfl⟩ : syracuseStep 2329553 = 1747165) B1747165
theorem B11791331 : Blo 1551473 11791331 := bstep (se 1 (by rfl) ⟨8843498, by rfl⟩ : syracuseStep 11791331 = 17686997) B17686997
theorem B2329571 : Blo 1551473 2329571 := bstep (se 1 (by rfl) ⟨1747178, by rfl⟩ : syracuseStep 2329571 = 3494357) B3494357
theorem B4787171 : Blo 1551473 4787171 := bstep (se 1 (by rfl) ⟨3590378, by rfl⟩ : syracuseStep 4787171 = 7180757) B7180757
theorem B2329601 : Blo 1551473 2329601 := bstep (se 2 (by rfl) ⟨873600, by rfl⟩ : syracuseStep 2329601 = 1747201) B1747201
theorem B3492881 : Blo 1551473 3492881 := bstep (se 2 (by rfl) ⟨1309830, by rfl⟩ : syracuseStep 3492881 = 2619661) B2619661
theorem B2329619 : Blo 1551473 2329619 := bstep (se 1 (by rfl) ⟨1747214, by rfl⟩ : syracuseStep 2329619 = 3494429) B3494429
theorem B3492899 : Blo 1551473 3492899 := bstep (se 1 (by rfl) ⟨2619674, by rfl⟩ : syracuseStep 3492899 = 5239349) B5239349
theorem B2329649 : Blo 1551473 2329649 := bstep (se 2 (by rfl) ⟨873618, by rfl⟩ : syracuseStep 2329649 = 1747237) B1747237
theorem B47803445 : Blo 1551473 47803445 := bstep (se 5 (by rfl) ⟨2240786, by rfl⟩ : syracuseStep 47803445 = 4481573) B4481573
theorem B2485313 : Blo 1551473 2485313 := bstep (se 2 (by rfl) ⟨931992, by rfl⟩ : syracuseStep 2485313 = 1863985) B1863985
theorem B2796611 : Blo 1551473 2796611 := bstep (se 1 (by rfl) ⟨2097458, by rfl⟩ : syracuseStep 2796611 = 4194917) B4194917
theorem B2329667 : Blo 1551473 2329667 := bstep (se 1 (by rfl) ⟨1747250, by rfl⟩ : syracuseStep 2329667 = 3494501) B3494501
theorem B5237837 : Blo 1551473 5237837 := bstep (se 3 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 5237837 = 1964189) B1964189
theorem B2329697 : Blo 1551473 2329697 := bstep (se 2 (by rfl) ⟨873636, by rfl⟩ : syracuseStep 2329697 = 1747273) B1747273
theorem B5311601 : Blo 1551473 5311601 := bstep (se 2 (by rfl) ⟨1991850, by rfl⟩ : syracuseStep 5311601 = 3983701) B3983701
theorem B1551475 : Blo 1551473 1551475 := bstep (se 1 (by rfl) ⟨1163606, by rfl⟩ : syracuseStep 1551475 = 2327213) B2327213
theorem B2329715 : Blo 1551473 2329715 := bstep (se 1 (by rfl) ⟨1747286, by rfl⟩ : syracuseStep 2329715 = 3494573) B3494573
theorem B1551491 : Blo 1551473 1551491 := bstep (se 1 (by rfl) ⟨1163618, by rfl⟩ : syracuseStep 1551491 = 2327237) B2327237
theorem B5237891 : Blo 1551473 5237891 := bstep (se 1 (by rfl) ⟨3928418, by rfl⟩ : syracuseStep 5237891 = 7856837) B7856837
theorem B2329745 : Blo 1551473 2329745 := bstep (se 2 (by rfl) ⟨873654, by rfl⟩ : syracuseStep 2329745 = 1747309) B1747309
theorem B1551507 : Blo 1551473 1551507 := bstep (se 1 (by rfl) ⟨1163630, by rfl⟩ : syracuseStep 1551507 = 2327261) B2327261
theorem B1551523 : Blo 1551473 1551523 := bstep (se 1 (by rfl) ⟨1163642, by rfl⟩ : syracuseStep 1551523 = 2327285) B2327285
theorem B2329763 : Blo 1551473 2329763 := bstep (se 1 (by rfl) ⟨1747322, by rfl⟩ : syracuseStep 2329763 = 3494645) B3494645
theorem B1551539 : Blo 1551473 1551539 := bstep (se 1 (by rfl) ⟨1163654, by rfl⟩ : syracuseStep 1551539 = 2327309) B2327309
theorem B2329793 : Blo 1551473 2329793 := bstep (se 2 (by rfl) ⟨873672, by rfl⟩ : syracuseStep 2329793 = 1747345) B1747345
theorem B1551555 : Blo 1551473 1551555 := bstep (se 1 (by rfl) ⟨1163666, by rfl⟩ : syracuseStep 1551555 = 2327333) B2327333
theorem B1551571 : Blo 1551473 1551571 := bstep (se 1 (by rfl) ⟨1163678, by rfl⟩ : syracuseStep 1551571 = 2327357) B2327357
theorem B2329811 : Blo 1551473 2329811 := bstep (se 1 (by rfl) ⟨1747358, by rfl⟩ : syracuseStep 2329811 = 3494717) B3494717
theorem B1551587 : Blo 1551473 1551587 := bstep (se 1 (by rfl) ⟨1163690, by rfl⟩ : syracuseStep 1551587 = 2327381) B2327381
theorem B1551603 : Blo 1551473 1551603 := bstep (se 1 (by rfl) ⟨1163702, by rfl⟩ : syracuseStep 1551603 = 2327405) B2327405
theorem B2329841 : Blo 1551473 2329841 := bstep (se 2 (by rfl) ⟨873690, by rfl⟩ : syracuseStep 2329841 = 1747381) B1747381
theorem B2485505 : Blo 1551473 2485505 := bstep (se 2 (by rfl) ⟨932064, by rfl⟩ : syracuseStep 2485505 = 1864129) B1864129
theorem B1551619 : Blo 1551473 1551619 := bstep (se 1 (by rfl) ⟨1163714, by rfl⟩ : syracuseStep 1551619 = 2327429) B2327429
theorem B2329859 : Blo 1551473 2329859 := bstep (se 1 (by rfl) ⟨1747394, by rfl⟩ : syracuseStep 2329859 = 3494789) B3494789
theorem B1551635 : Blo 1551473 1551635 := bstep (se 1 (by rfl) ⟨1163726, by rfl⟩ : syracuseStep 1551635 = 2327453) B2327453
theorem B2329889 : Blo 1551473 2329889 := bstep (se 2 (by rfl) ⟨873708, by rfl⟩ : syracuseStep 2329889 = 1747417) B1747417
theorem B1551651 : Blo 1551473 1551651 := bstep (se 1 (by rfl) ⟨1163738, by rfl⟩ : syracuseStep 1551651 = 2327477) B2327477
theorem B5041457 : Blo 1551473 5041457 := bstep (se 2 (by rfl) ⟨1890546, by rfl⟩ : syracuseStep 5041457 = 3781093) B3781093
theorem B3493169 : Blo 1551473 3493169 := bstep (se 2 (by rfl) ⟨1309938, by rfl⟩ : syracuseStep 3493169 = 2619877) B2619877
theorem B1551667 : Blo 1551473 1551667 := bstep (se 1 (by rfl) ⟨1163750, by rfl⟩ : syracuseStep 1551667 = 2327501) B2327501
theorem B2329907 : Blo 1551473 2329907 := bstep (se 1 (by rfl) ⟨1747430, by rfl⟩ : syracuseStep 2329907 = 3494861) B3494861
theorem B1551683 : Blo 1551473 1551683 := bstep (se 1 (by rfl) ⟨1163762, by rfl⟩ : syracuseStep 1551683 = 2327525) B2327525
theorem B3493187 : Blo 1551473 3493187 := bstep (se 1 (by rfl) ⟨2619890, by rfl⟩ : syracuseStep 3493187 = 5239781) B5239781
theorem B2329937 : Blo 1551473 2329937 := bstep (se 2 (by rfl) ⟨873726, by rfl⟩ : syracuseStep 2329937 = 1747453) B1747453
theorem B1551699 : Blo 1551473 1551699 := bstep (se 1 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 1551699 = 2327549) B2327549
theorem B1551715 : Blo 1551473 1551715 := bstep (se 1 (by rfl) ⟨1163786, by rfl⟩ : syracuseStep 1551715 = 2327573) B2327573
theorem B2329955 : Blo 1551473 2329955 := bstep (se 1 (by rfl) ⟨1747466, by rfl⟩ : syracuseStep 2329955 = 3494933) B3494933
theorem B1551731 : Blo 1551473 1551731 := bstep (se 1 (by rfl) ⟨1163798, by rfl⟩ : syracuseStep 1551731 = 2327597) B2327597
theorem B2329985 : Blo 1551473 2329985 := bstep (se 2 (by rfl) ⟨873744, by rfl⟩ : syracuseStep 2329985 = 1747489) B1747489
theorem B1551747 : Blo 1551473 1551747 := bstep (se 1 (by rfl) ⟨1163810, by rfl⟩ : syracuseStep 1551747 = 2327621) B2327621
theorem B5238161 : Blo 1551473 5238161 := bstep (se 2 (by rfl) ⟨1964310, by rfl⟩ : syracuseStep 5238161 = 3928621) B3928621
theorem B1551763 : Blo 1551473 1551763 := bstep (se 1 (by rfl) ⟨1163822, by rfl⟩ : syracuseStep 1551763 = 2327645) B2327645
theorem B2330003 : Blo 1551473 2330003 := bstep (se 1 (by rfl) ⟨1747502, by rfl⟩ : syracuseStep 2330003 = 3495005) B3495005
theorem B1551779 : Blo 1551473 1551779 := bstep (se 1 (by rfl) ⟨1163834, by rfl⟩ : syracuseStep 1551779 = 2327669) B2327669
theorem B2330033 : Blo 1551473 2330033 := bstep (se 2 (by rfl) ⟨873762, by rfl⟩ : syracuseStep 2330033 = 1747525) B1747525
theorem B1551795 : Blo 1551473 1551795 := bstep (se 1 (by rfl) ⟨1163846, by rfl⟩ : syracuseStep 1551795 = 2327693) B2327693
theorem B1551811 : Blo 1551473 1551811 := bstep (se 1 (by rfl) ⟨1163858, by rfl⟩ : syracuseStep 1551811 = 2327717) B2327717
theorem B2330051 : Blo 1551473 2330051 := bstep (se 1 (by rfl) ⟨1747538, by rfl⟩ : syracuseStep 2330051 = 3495077) B3495077
theorem B1551827 : Blo 1551473 1551827 := bstep (se 1 (by rfl) ⟨1163870, by rfl⟩ : syracuseStep 1551827 = 2327741) B2327741
theorem B1658323 : Blo 1551473 1658323 := bstep (se 1 (by rfl) ⟨1243742, by rfl⟩ : syracuseStep 1658323 = 2487485) B2487485
theorem B2330081 : Blo 1551473 2330081 := bstep (se 2 (by rfl) ⟨873780, by rfl⟩ : syracuseStep 2330081 = 1747561) B1747561
theorem B1551843 : Blo 1551473 1551843 := bstep (se 1 (by rfl) ⟨1163882, by rfl⟩ : syracuseStep 1551843 = 2327765) B2327765
theorem B1551859 : Blo 1551473 1551859 := bstep (se 1 (by rfl) ⟨1163894, by rfl⟩ : syracuseStep 1551859 = 2327789) B2327789
theorem B2330099 : Blo 1551473 2330099 := bstep (se 1 (by rfl) ⟨1747574, by rfl⟩ : syracuseStep 2330099 = 3495149) B3495149
theorem B1551875 : Blo 1551473 1551875 := bstep (se 1 (by rfl) ⟨1163906, by rfl⟩ : syracuseStep 1551875 = 2327813) B2327813
theorem B6139405 : Blo 1551473 6139405 := bstep (se 3 (by rfl) ⟨1151138, by rfl⟩ : syracuseStep 6139405 = 2302277) B2302277
theorem B2330129 : Blo 1551473 2330129 := bstep (se 2 (by rfl) ⟨873798, by rfl⟩ : syracuseStep 2330129 = 1747597) B1747597
theorem B1551891 : Blo 1551473 1551891 := bstep (se 1 (by rfl) ⟨1163918, by rfl⟩ : syracuseStep 1551891 = 2327837) B2327837
theorem B4419107 : Blo 1551473 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B1551907 : Blo 1551473 1551907 := bstep (se 1 (by rfl) ⟨1163930, by rfl⟩ : syracuseStep 1551907 = 2327861) B2327861
theorem B2330147 : Blo 1551473 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B1551923 : Blo 1551473 1551923 := bstep (se 1 (by rfl) ⟨1163942, by rfl⟩ : syracuseStep 1551923 = 2327885) B2327885
theorem B75492917 : Blo 1551473 75492917 := bstep (se 5 (by rfl) ⟨3538730, by rfl⟩ : syracuseStep 75492917 = 7077461) B7077461
theorem B2330177 : Blo 1551473 2330177 := bstep (se 2 (by rfl) ⟨873816, by rfl⟩ : syracuseStep 2330177 = 1747633) B1747633
theorem B1551939 : Blo 1551473 1551939 := bstep (se 1 (by rfl) ⟨1163954, by rfl⟩ : syracuseStep 1551939 = 2327909) B2327909
theorem B3493457 : Blo 1551473 3493457 := bstep (se 2 (by rfl) ⟨1310046, by rfl⟩ : syracuseStep 3493457 = 2620093) B2620093
theorem B1551955 : Blo 1551473 1551955 := bstep (se 1 (by rfl) ⟨1163966, by rfl⟩ : syracuseStep 1551955 = 2327933) B2327933
theorem B2330195 : Blo 1551473 2330195 := bstep (se 1 (by rfl) ⟨1747646, by rfl⟩ : syracuseStep 2330195 = 3495293) B3495293
theorem B1551971 : Blo 1551473 1551971 := bstep (se 1 (by rfl) ⟨1163978, by rfl⟩ : syracuseStep 1551971 = 2327957) B2327957
theorem B3493475 : Blo 1551473 3493475 := bstep (se 1 (by rfl) ⟨2620106, by rfl⟩ : syracuseStep 3493475 = 5240213) B5240213
theorem B1551987 : Blo 1551473 1551987 := bstep (se 1 (by rfl) ⟨1163990, by rfl⟩ : syracuseStep 1551987 = 2327981) B2327981
theorem B1552003 : Blo 1551473 1552003 := bstep (se 1 (by rfl) ⟨1164002, by rfl⟩ : syracuseStep 1552003 = 2328005) B2328005
theorem B11062925 : Blo 1551473 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B2690705 : Blo 1551473 2690705 := bstep (se 2 (by rfl) ⟨1009014, by rfl⟩ : syracuseStep 2690705 = 2018029) B2018029
theorem B1552019 : Blo 1551473 1552019 := bstep (se 1 (by rfl) ⟨1164014, by rfl⟩ : syracuseStep 1552019 = 2328029) B2328029
theorem B1552035 : Blo 1551473 1552035 := bstep (se 1 (by rfl) ⟨1164026, by rfl⟩ : syracuseStep 1552035 = 2328053) B2328053
theorem B5385901 : Blo 1551473 5385901 := bstep (se 3 (by rfl) ⟨1009856, by rfl⟩ : syracuseStep 5385901 = 2019713) B2019713
theorem B1552051 : Blo 1551473 1552051 := bstep (se 1 (by rfl) ⟨1164038, by rfl⟩ : syracuseStep 1552051 = 2328077) B2328077
theorem B1552067 : Blo 1551473 1552067 := bstep (se 1 (by rfl) ⟨1164050, by rfl⟩ : syracuseStep 1552067 = 2328101) B2328101
theorem B3927761 : Blo 1551473 3927761 := bstep (se 2 (by rfl) ⟨1472910, by rfl⟩ : syracuseStep 3927761 = 2945821) B2945821
theorem B1552083 : Blo 1551473 1552083 := bstep (se 1 (by rfl) ⟨1164062, by rfl⟩ : syracuseStep 1552083 = 2328125) B2328125
theorem B1552099 : Blo 1551473 1552099 := bstep (se 1 (by rfl) ⟨1164074, by rfl⟩ : syracuseStep 1552099 = 2328149) B2328149
theorem B9440995 : Blo 1551473 9440995 := bstep (se 1 (by rfl) ⟨7080746, by rfl⟩ : syracuseStep 9440995 = 14161493) B14161493
theorem B1552115 : Blo 1551473 1552115 := bstep (se 1 (by rfl) ⟨1164086, by rfl⟩ : syracuseStep 1552115 = 2328173) B2328173
theorem B3927811 : Blo 1551473 3927811 := bstep (se 1 (by rfl) ⟨2945858, by rfl⟩ : syracuseStep 3927811 = 5891717) B5891717
theorem B1552131 : Blo 1551473 1552131 := bstep (se 1 (by rfl) ⟨1164098, by rfl⟩ : syracuseStep 1552131 = 2328197) B2328197
theorem B1552147 : Blo 1551473 1552147 := bstep (se 1 (by rfl) ⟨1164110, by rfl⟩ : syracuseStep 1552147 = 2328221) B2328221
theorem B1552163 : Blo 1551473 1552163 := bstep (se 1 (by rfl) ⟨1164122, by rfl⟩ : syracuseStep 1552163 = 2328245) B2328245
theorem B1552179 : Blo 1551473 1552179 := bstep (se 1 (by rfl) ⟨1164134, by rfl⟩ : syracuseStep 1552179 = 2328269) B2328269
theorem B1552195 : Blo 1551473 1552195 := bstep (se 1 (by rfl) ⟨1164146, by rfl⟩ : syracuseStep 1552195 = 2328293) B2328293
theorem B7966541 : Blo 1551473 7966541 := bstep (se 3 (by rfl) ⟨1493726, by rfl⟩ : syracuseStep 7966541 = 2987453) B2987453
theorem B1552211 : Blo 1551473 1552211 := bstep (se 1 (by rfl) ⟨1164158, by rfl⟩ : syracuseStep 1552211 = 2328317) B2328317
theorem B1552227 : Blo 1551473 1552227 := bstep (se 1 (by rfl) ⟨1164170, by rfl⟩ : syracuseStep 1552227 = 2328341) B2328341
theorem B3493745 : Blo 1551473 3493745 := bstep (se 2 (by rfl) ⟨1310154, by rfl⟩ : syracuseStep 3493745 = 2620309) B2620309
theorem B1552243 : Blo 1551473 1552243 := bstep (se 1 (by rfl) ⟨1164182, by rfl⟩ : syracuseStep 1552243 = 2328365) B2328365
theorem B2125697 : Blo 1551473 2125697 := bstep (se 2 (by rfl) ⟨797136, by rfl⟩ : syracuseStep 2125697 = 1594273) B1594273
theorem B1552259 : Blo 1551473 1552259 := bstep (se 1 (by rfl) ⟨1164194, by rfl⟩ : syracuseStep 1552259 = 2328389) B2328389
theorem B3493763 : Blo 1551473 3493763 := bstep (se 1 (by rfl) ⟨2620322, by rfl⟩ : syracuseStep 3493763 = 5240645) B5240645
theorem B3927953 : Blo 1551473 3927953 := bstep (se 2 (by rfl) ⟨1472982, by rfl⟩ : syracuseStep 3927953 = 2945965) B2945965
theorem B1552275 : Blo 1551473 1552275 := bstep (se 1 (by rfl) ⟨1164206, by rfl⟩ : syracuseStep 1552275 = 2328413) B2328413
theorem B1552291 : Blo 1551473 1552291 := bstep (se 1 (by rfl) ⟨1164218, by rfl⟩ : syracuseStep 1552291 = 2328437) B2328437
theorem B5238701 : Blo 1551473 5238701 := bstep (se 3 (by rfl) ⟨982256, by rfl⟩ : syracuseStep 5238701 = 1964513) B1964513
theorem B2125747 : Blo 1551473 2125747 := bstep (se 1 (by rfl) ⟨1594310, by rfl⟩ : syracuseStep 2125747 = 3188621) B3188621
theorem B1552307 : Blo 1551473 1552307 := bstep (se 1 (by rfl) ⟨1164230, by rfl⟩ : syracuseStep 1552307 = 2328461) B2328461
theorem B1552323 : Blo 1551473 1552323 := bstep (se 1 (by rfl) ⟨1164242, by rfl⟩ : syracuseStep 1552323 = 2328485) B2328485
theorem B1552339 : Blo 1551473 1552339 := bstep (se 1 (by rfl) ⟨1164254, by rfl⟩ : syracuseStep 1552339 = 2328509) B2328509
theorem B5238755 : Blo 1551473 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B1552355 : Blo 1551473 1552355 := bstep (se 1 (by rfl) ⟨1164266, by rfl⟩ : syracuseStep 1552355 = 2328533) B2328533
theorem B1552371 : Blo 1551473 1552371 := bstep (se 1 (by rfl) ⟨1164278, by rfl⟩ : syracuseStep 1552371 = 2328557) B2328557
theorem B1552387 : Blo 1551473 1552387 := bstep (se 1 (by rfl) ⟨1164290, by rfl⟩ : syracuseStep 1552387 = 2328581) B2328581
theorem B1552403 : Blo 1551473 1552403 := bstep (se 1 (by rfl) ⟨1164302, by rfl⟩ : syracuseStep 1552403 = 2328605) B2328605
theorem B1552419 : Blo 1551473 1552419 := bstep (se 1 (by rfl) ⟨1164314, by rfl⟩ : syracuseStep 1552419 = 2328629) B2328629
theorem B1552435 : Blo 1551473 1552435 := bstep (se 1 (by rfl) ⟨1164326, by rfl⟩ : syracuseStep 1552435 = 2328653) B2328653
theorem B1552451 : Blo 1551473 1552451 := bstep (se 1 (by rfl) ⟨1164338, by rfl⟩ : syracuseStep 1552451 = 2328677) B2328677
theorem B4255811 : Blo 1551473 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B1552467 : Blo 1551473 1552467 := bstep (se 1 (by rfl) ⟨1164350, by rfl⟩ : syracuseStep 1552467 = 2328701) B2328701
theorem B1552483 : Blo 1551473 1552483 := bstep (se 1 (by rfl) ⟨1164362, by rfl⟩ : syracuseStep 1552483 = 2328725) B2328725
theorem B8843363 : Blo 1551473 8843363 := bstep (se 1 (by rfl) ⟨6632522, by rfl⟩ : syracuseStep 8843363 = 13265045) B13265045
theorem B1552499 : Blo 1551473 1552499 := bstep (se 1 (by rfl) ⟨1164374, by rfl⟩ : syracuseStep 1552499 = 2328749) B2328749
theorem B1552515 : Blo 1551473 1552515 := bstep (se 1 (by rfl) ⟨1164386, by rfl⟩ : syracuseStep 1552515 = 2328773) B2328773
theorem B4788355 : Blo 1551473 4788355 := bstep (se 1 (by rfl) ⟨3591266, by rfl⟩ : syracuseStep 4788355 = 7182533) B7182533
theorem B3494033 : Blo 1551473 3494033 := bstep (se 2 (by rfl) ⟨1310262, by rfl⟩ : syracuseStep 3494033 = 2620525) B2620525
theorem B4722833 : Blo 1551473 4722833 := bstep (se 2 (by rfl) ⟨1771062, by rfl⟩ : syracuseStep 4722833 = 3542125) B3542125
theorem B1552531 : Blo 1551473 1552531 := bstep (se 1 (by rfl) ⟨1164398, by rfl⟩ : syracuseStep 1552531 = 2328797) B2328797
theorem B1552547 : Blo 1551473 1552547 := bstep (se 1 (by rfl) ⟨1164410, by rfl⟩ : syracuseStep 1552547 = 2328821) B2328821
theorem B3494051 : Blo 1551473 3494051 := bstep (se 1 (by rfl) ⟨2620538, by rfl⟩ : syracuseStep 3494051 = 5241077) B5241077
theorem B7860401 : Blo 1551473 7860401 := bstep (se 2 (by rfl) ⟨2947650, by rfl⟩ : syracuseStep 7860401 = 5895301) B5895301
theorem B1552563 : Blo 1551473 1552563 := bstep (se 1 (by rfl) ⟨1164422, by rfl⟩ : syracuseStep 1552563 = 2328845) B2328845
theorem B1552579 : Blo 1551473 1552579 := bstep (se 1 (by rfl) ⟨1164434, by rfl⟩ : syracuseStep 1552579 = 2328869) B2328869
theorem B1552595 : Blo 1551473 1552595 := bstep (se 1 (by rfl) ⟨1164446, by rfl⟩ : syracuseStep 1552595 = 2328893) B2328893
theorem B1552611 : Blo 1551473 1552611 := bstep (se 1 (by rfl) ⟨1164458, by rfl⟩ : syracuseStep 1552611 = 2328917) B2328917
theorem B5239025 : Blo 1551473 5239025 := bstep (se 2 (by rfl) ⟨1964634, by rfl⟩ : syracuseStep 5239025 = 3929269) B3929269
theorem B1552627 : Blo 1551473 1552627 := bstep (se 1 (by rfl) ⟨1164470, by rfl⟩ : syracuseStep 1552627 = 2328941) B2328941
theorem B1552643 : Blo 1551473 1552643 := bstep (se 1 (by rfl) ⟨1164482, by rfl⟩ : syracuseStep 1552643 = 2328965) B2328965
theorem B1552659 : Blo 1551473 1552659 := bstep (se 1 (by rfl) ⟨1164494, by rfl⟩ : syracuseStep 1552659 = 2328989) B2328989
theorem B3313955 : Blo 1551473 3313955 := bstep (se 1 (by rfl) ⟨2485466, by rfl⟩ : syracuseStep 3313955 = 4970933) B4970933
theorem B1552675 : Blo 1551473 1552675 := bstep (se 1 (by rfl) ⟨1164506, by rfl⟩ : syracuseStep 1552675 = 2329013) B2329013
theorem B1552691 : Blo 1551473 1552691 := bstep (se 1 (by rfl) ⟨1164518, by rfl⟩ : syracuseStep 1552691 = 2329037) B2329037
theorem B1552707 : Blo 1551473 1552707 := bstep (se 1 (by rfl) ⟨1164530, by rfl⟩ : syracuseStep 1552707 = 2329061) B2329061
theorem B4419917 : Blo 1551473 4419917 := bstep (se 3 (by rfl) ⟨828734, by rfl⟩ : syracuseStep 4419917 = 1657469) B1657469
theorem B1552723 : Blo 1551473 1552723 := bstep (se 1 (by rfl) ⟨1164542, by rfl⟩ : syracuseStep 1552723 = 2329085) B2329085
theorem B1552739 : Blo 1551473 1552739 := bstep (se 1 (by rfl) ⟨1164554, by rfl⟩ : syracuseStep 1552739 = 2329109) B2329109
theorem B4198765 : Blo 1551473 4198765 := bstep (se 3 (by rfl) ⟨787268, by rfl⟩ : syracuseStep 4198765 = 1574537) B1574537
theorem B9949553 : Blo 1551473 9949553 := bstep (se 2 (by rfl) ⟨3731082, by rfl⟩ : syracuseStep 9949553 = 7462165) B7462165
theorem B1552755 : Blo 1551473 1552755 := bstep (se 1 (by rfl) ⟨1164566, by rfl⟩ : syracuseStep 1552755 = 2329133) B2329133
theorem B1552771 : Blo 1551473 1552771 := bstep (se 1 (by rfl) ⟨1164578, by rfl⟩ : syracuseStep 1552771 = 2329157) B2329157
theorem B1552787 : Blo 1551473 1552787 := bstep (se 1 (by rfl) ⟨1164590, by rfl⟩ : syracuseStep 1552787 = 2329181) B2329181
theorem B1552803 : Blo 1551473 1552803 := bstep (se 1 (by rfl) ⟨1164602, by rfl⟩ : syracuseStep 1552803 = 2329205) B2329205
theorem B6558115 : Blo 1551473 6558115 := bstep (se 1 (by rfl) ⟨4918586, by rfl⟩ : syracuseStep 6558115 = 9837173) B9837173
theorem B3494321 : Blo 1551473 3494321 := bstep (se 2 (by rfl) ⟨1310370, by rfl⟩ : syracuseStep 3494321 = 2620741) B2620741
theorem B2240947 : Blo 1551473 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B1552819 : Blo 1551473 1552819 := bstep (se 1 (by rfl) ⟨1164614, by rfl⟩ : syracuseStep 1552819 = 2329229) B2329229
theorem B1552835 : Blo 1551473 1552835 := bstep (se 1 (by rfl) ⟨1164626, by rfl⟩ : syracuseStep 1552835 = 2329253) B2329253
theorem B3494339 : Blo 1551473 3494339 := bstep (se 1 (by rfl) ⟨2620754, by rfl⟩ : syracuseStep 3494339 = 5241509) B5241509
theorem B1552851 : Blo 1551473 1552851 := bstep (se 1 (by rfl) ⟨1164638, by rfl⟩ : syracuseStep 1552851 = 2329277) B2329277
theorem B1552867 : Blo 1551473 1552867 := bstep (se 1 (by rfl) ⟨1164650, by rfl⟩ : syracuseStep 1552867 = 2329301) B2329301
theorem B1552883 : Blo 1551473 1552883 := bstep (se 1 (by rfl) ⟨1164662, by rfl⟩ : syracuseStep 1552883 = 2329325) B2329325
theorem B1552899 : Blo 1551473 1552899 := bstep (se 1 (by rfl) ⟨1164674, by rfl⟩ : syracuseStep 1552899 = 2329349) B2329349
theorem B4420109 : Blo 1551473 4420109 := bstep (se 3 (by rfl) ⟨828770, by rfl⟩ : syracuseStep 4420109 = 1657541) B1657541
theorem B1552915 : Blo 1551473 1552915 := bstep (se 1 (by rfl) ⟨1164686, by rfl⟩ : syracuseStep 1552915 = 2329373) B2329373
theorem B1552931 : Blo 1551473 1552931 := bstep (se 1 (by rfl) ⟨1164698, by rfl⟩ : syracuseStep 1552931 = 2329397) B2329397
theorem B2945585 : Blo 1551473 2945585 := bstep (se 2 (by rfl) ⟨1104594, by rfl⟩ : syracuseStep 2945585 = 2209189) B2209189
theorem B1552947 : Blo 1551473 1552947 := bstep (se 1 (by rfl) ⟨1164710, by rfl⟩ : syracuseStep 1552947 = 2329421) B2329421
theorem B1552963 : Blo 1551473 1552963 := bstep (se 1 (by rfl) ⟨1164722, by rfl⟩ : syracuseStep 1552963 = 2329445) B2329445
theorem B1552979 : Blo 1551473 1552979 := bstep (se 1 (by rfl) ⟨1164734, by rfl⟩ : syracuseStep 1552979 = 2329469) B2329469
theorem B1552995 : Blo 1551473 1552995 := bstep (se 1 (by rfl) ⟨1164746, by rfl⟩ : syracuseStep 1552995 = 2329493) B2329493
theorem B13628017 : Blo 1551473 13628017 := bstep (se 2 (by rfl) ⟨5110506, by rfl⟩ : syracuseStep 13628017 = 10221013) B10221013
theorem B1553011 : Blo 1551473 1553011 := bstep (se 1 (by rfl) ⟨1164758, by rfl⟩ : syracuseStep 1553011 = 2329517) B2329517
theorem B1553027 : Blo 1551473 1553027 := bstep (se 1 (by rfl) ⟨1164770, by rfl⟩ : syracuseStep 1553027 = 2329541) B2329541
theorem B1553043 : Blo 1551473 1553043 := bstep (se 1 (by rfl) ⟨1164782, by rfl⟩ : syracuseStep 1553043 = 2329565) B2329565
theorem B1553059 : Blo 1551473 1553059 := bstep (se 1 (by rfl) ⟨1164794, by rfl⟩ : syracuseStep 1553059 = 2329589) B2329589
theorem B1553075 : Blo 1551473 1553075 := bstep (se 1 (by rfl) ⟨1164806, by rfl⟩ : syracuseStep 1553075 = 2329613) B2329613
theorem B19903157 : Blo 1551473 19903157 := bstep (se 5 (by rfl) ⟨932960, by rfl⟩ : syracuseStep 19903157 = 1865921) B1865921
theorem B1553091 : Blo 1551473 1553091 := bstep (se 1 (by rfl) ⟨1164818, by rfl⟩ : syracuseStep 1553091 = 2329637) B2329637
theorem B3494609 : Blo 1551473 3494609 := bstep (se 2 (by rfl) ⟨1310478, by rfl⟩ : syracuseStep 3494609 = 2620957) B2620957
theorem B1553107 : Blo 1551473 1553107 := bstep (se 1 (by rfl) ⟨1164830, by rfl⟩ : syracuseStep 1553107 = 2329661) B2329661
theorem B1553123 : Blo 1551473 1553123 := bstep (se 1 (by rfl) ⟨1164842, by rfl⟩ : syracuseStep 1553123 = 2329685) B2329685
theorem B3494627 : Blo 1551473 3494627 := bstep (se 1 (by rfl) ⟨2620970, by rfl⟩ : syracuseStep 3494627 = 5241941) B5241941
theorem B1553139 : Blo 1551473 1553139 := bstep (se 1 (by rfl) ⟨1164854, by rfl⟩ : syracuseStep 1553139 = 2329709) B2329709
theorem B1553155 : Blo 1551473 1553155 := bstep (se 1 (by rfl) ⟨1164866, by rfl⟩ : syracuseStep 1553155 = 2329733) B2329733
theorem B5239565 : Blo 1551473 5239565 := bstep (se 3 (by rfl) ⟨982418, by rfl⟩ : syracuseStep 5239565 = 1964837) B1964837
theorem B2618129 : Blo 1551473 2618129 := bstep (se 2 (by rfl) ⟨981798, by rfl⟩ : syracuseStep 2618129 = 1963597) B1963597
theorem B1553171 : Blo 1551473 1553171 := bstep (se 1 (by rfl) ⟨1164878, by rfl⟩ : syracuseStep 1553171 = 2329757) B2329757
theorem B3314467 : Blo 1551473 3314467 := bstep (se 1 (by rfl) ⟨2485850, by rfl⟩ : syracuseStep 3314467 = 4971701) B4971701
theorem B1553187 : Blo 1551473 1553187 := bstep (se 1 (by rfl) ⟨1164890, by rfl⟩ : syracuseStep 1553187 = 2329781) B2329781
theorem B1553203 : Blo 1551473 1553203 := bstep (se 1 (by rfl) ⟨1164902, by rfl⟩ : syracuseStep 1553203 = 2329805) B2329805
theorem B5239619 : Blo 1551473 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B2487107 : Blo 1551473 2487107 := bstep (se 1 (by rfl) ⟨1865330, by rfl⟩ : syracuseStep 2487107 = 3730661) B3730661
theorem B1553219 : Blo 1551473 1553219 := bstep (se 1 (by rfl) ⟨1164914, by rfl⟩ : syracuseStep 1553219 = 2329829) B2329829
theorem B1553235 : Blo 1551473 1553235 := bstep (se 1 (by rfl) ⟨1164926, by rfl⟩ : syracuseStep 1553235 = 2329853) B2329853
theorem B1553251 : Blo 1551473 1553251 := bstep (se 1 (by rfl) ⟨1164938, by rfl⟩ : syracuseStep 1553251 = 2329877) B2329877
theorem B3928945 : Blo 1551473 3928945 := bstep (se 2 (by rfl) ⟨1473354, by rfl⟩ : syracuseStep 3928945 = 2946709) B2946709
theorem B1553267 : Blo 1551473 1553267 := bstep (se 1 (by rfl) ⟨1164950, by rfl⟩ : syracuseStep 1553267 = 2329901) B2329901
theorem B1553283 : Blo 1551473 1553283 := bstep (se 1 (by rfl) ⟨1164962, by rfl⟩ : syracuseStep 1553283 = 2329925) B2329925
theorem B60502925 : Blo 1551473 60502925 := bstep (se 3 (by rfl) ⟨11344298, by rfl⟩ : syracuseStep 60502925 = 22688597) B22688597
theorem B2618257 : Blo 1551473 2618257 := bstep (se 2 (by rfl) ⟨981846, by rfl⟩ : syracuseStep 2618257 = 1963693) B1963693
theorem B1553299 : Blo 1551473 1553299 := bstep (se 1 (by rfl) ⟨1164974, by rfl⟩ : syracuseStep 1553299 = 2329949) B2329949
theorem B1553315 : Blo 1551473 1553315 := bstep (se 1 (by rfl) ⟨1164986, by rfl⟩ : syracuseStep 1553315 = 2329973) B2329973
theorem B5895089 : Blo 1551473 5895089 := bstep (se 2 (by rfl) ⟨2210658, by rfl⟩ : syracuseStep 5895089 = 4421317) B4421317
theorem B2618291 : Blo 1551473 2618291 := bstep (se 1 (by rfl) ⟨1963718, by rfl⟩ : syracuseStep 2618291 = 3927437) B3927437
theorem B1553331 : Blo 1551473 1553331 := bstep (se 1 (by rfl) ⟨1164998, by rfl⟩ : syracuseStep 1553331 = 2329997) B2329997
theorem B1553347 : Blo 1551473 1553347 := bstep (se 1 (by rfl) ⟨1165010, by rfl⟩ : syracuseStep 1553347 = 2330021) B2330021
theorem B1553363 : Blo 1551473 1553363 := bstep (se 1 (by rfl) ⟨1165022, by rfl⟩ : syracuseStep 1553363 = 2330045) B2330045
theorem B1553379 : Blo 1551473 1553379 := bstep (se 1 (by rfl) ⟨1165034, by rfl⟩ : syracuseStep 1553379 = 2330069) B2330069
theorem B3494897 : Blo 1551473 3494897 := bstep (se 2 (by rfl) ⟨1310586, by rfl⟩ : syracuseStep 3494897 = 2621173) B2621173
theorem B1553395 : Blo 1551473 1553395 := bstep (se 1 (by rfl) ⟨1165046, by rfl⟩ : syracuseStep 1553395 = 2330093) B2330093
theorem B3494915 : Blo 1551473 3494915 := bstep (se 1 (by rfl) ⟨2621186, by rfl⟩ : syracuseStep 3494915 = 5242373) B5242373
theorem B1553411 : Blo 1551473 1553411 := bstep (se 1 (by rfl) ⟨1165058, by rfl⟩ : syracuseStep 1553411 = 2330117) B2330117
theorem B1553427 : Blo 1551473 1553427 := bstep (se 1 (by rfl) ⟨1165070, by rfl⟩ : syracuseStep 1553427 = 2330141) B2330141
theorem B1553443 : Blo 1551473 1553443 := bstep (se 1 (by rfl) ⟨1165082, by rfl⟩ : syracuseStep 1553443 = 2330165) B2330165
theorem B2618419 : Blo 1551473 2618419 := bstep (se 1 (by rfl) ⟨1963814, by rfl⟩ : syracuseStep 2618419 = 3927629) B3927629
theorem B1553459 : Blo 1551473 1553459 := bstep (se 1 (by rfl) ⟨1165094, by rfl⟩ : syracuseStep 1553459 = 2330189) B2330189
theorem B17675333 : Blo 1551473 17675333 := bstep (se 4 (by rfl) ⟨1657062, by rfl⟩ : syracuseStep 17675333 = 3314125) B3314125
theorem B5239889 : Blo 1551473 5239889 := bstep (se 2 (by rfl) ⟨1964958, by rfl⟩ : syracuseStep 5239889 = 3929917) B3929917
theorem B3929219 : Blo 1551473 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B2618561 : Blo 1551473 2618561 := bstep (se 2 (by rfl) ⟨981960, by rfl⟩ : syracuseStep 2618561 = 1963921) B1963921
theorem B2487491 : Blo 1551473 2487491 := bstep (se 1 (by rfl) ⟨1865618, by rfl⟩ : syracuseStep 2487491 = 3731237) B3731237
theorem B2946307 : Blo 1551473 2946307 := bstep (se 1 (by rfl) ⟨2209730, by rfl⟩ : syracuseStep 2946307 = 4419461) B4419461
theorem B3495185 : Blo 1551473 3495185 := bstep (se 2 (by rfl) ⟨1310694, by rfl⟩ : syracuseStep 3495185 = 2621389) B2621389
theorem B3495203 : Blo 1551473 3495203 := bstep (se 1 (by rfl) ⟨2621402, by rfl⟩ : syracuseStep 3495203 = 5242805) B5242805
theorem B2618689 : Blo 1551473 2618689 := bstep (se 2 (by rfl) ⟨982008, by rfl⟩ : syracuseStep 2618689 = 1964017) B1964017
theorem B3929411 : Blo 1551473 3929411 := bstep (se 1 (by rfl) ⟨2947058, by rfl⟩ : syracuseStep 3929411 = 5894117) B5894117
theorem B2487619 : Blo 1551473 2487619 := bstep (se 1 (by rfl) ⟨1865714, by rfl⟩ : syracuseStep 2487619 = 3731429) B3731429
theorem B2618723 : Blo 1551473 2618723 := bstep (se 1 (by rfl) ⟨1964042, by rfl⟩ : syracuseStep 2618723 = 3928085) B3928085
theorem B2618851 : Blo 1551473 2618851 := bstep (se 1 (by rfl) ⟨1964138, by rfl⟩ : syracuseStep 2618851 = 3928277) B3928277
theorem B4421101 : Blo 1551473 4421101 := bstep (se 3 (by rfl) ⟨828956, by rfl⟩ : syracuseStep 4421101 = 1657913) B1657913
theorem B3315185 : Blo 1551473 3315185 := bstep (se 2 (by rfl) ⟨1243194, by rfl⟩ : syracuseStep 3315185 = 2486389) B2486389
theorem B7861859 : Blo 1551473 7861859 := bstep (se 1 (by rfl) ⟨5896394, by rfl⟩ : syracuseStep 7861859 = 11792789) B11792789
theorem B5240429 : Blo 1551473 5240429 := bstep (se 3 (by rfl) ⟨982580, by rfl⟩ : syracuseStep 5240429 = 1965161) B1965161
theorem B2618993 : Blo 1551473 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B17684081 : Blo 1551473 17684081 := bstep (se 2 (by rfl) ⟨6631530, by rfl⟩ : syracuseStep 17684081 = 13263061) B13263061
theorem B2799235 : Blo 1551473 2799235 := bstep (se 1 (by rfl) ⟨2099426, by rfl⟩ : syracuseStep 2799235 = 4198853) B4198853
theorem B10761869 : Blo 1551473 10761869 := bstep (se 3 (by rfl) ⟨2017850, by rfl⟩ : syracuseStep 10761869 = 4035701) B4035701
theorem B4429475 : Blo 1551473 4429475 := bstep (se 1 (by rfl) ⟨3322106, by rfl⟩ : syracuseStep 4429475 = 6644213) B6644213
theorem B5240483 : Blo 1551473 5240483 := bstep (se 1 (by rfl) ⟨3930362, by rfl⟩ : syracuseStep 5240483 = 7860725) B7860725
theorem B2209457 : Blo 1551473 2209457 := bstep (se 2 (by rfl) ⟨828546, by rfl⟩ : syracuseStep 2209457 = 1657093) B1657093
theorem B2946755 : Blo 1551473 2946755 := bstep (se 1 (by rfl) ⟨2210066, by rfl⟩ : syracuseStep 2946755 = 4420133) B4420133
theorem B5592817 : Blo 1551473 5592817 := bstep (se 2 (by rfl) ⟨2097306, by rfl⟩ : syracuseStep 5592817 = 4194613) B4194613
theorem B2619121 : Blo 1551473 2619121 := bstep (se 2 (by rfl) ⟨982170, by rfl⟩ : syracuseStep 2619121 = 1964341) B1964341
theorem B2619155 : Blo 1551473 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B4544305 : Blo 1551473 4544305 := bstep (se 2 (by rfl) ⟨1704114, by rfl⟩ : syracuseStep 4544305 = 3408229) B3408229
theorem B2619283 : Blo 1551473 2619283 := bstep (se 1 (by rfl) ⟨1964462, by rfl⟩ : syracuseStep 2619283 = 3928925) B3928925
theorem B5240753 : Blo 1551473 5240753 := bstep (se 2 (by rfl) ⟨1965282, by rfl⟩ : syracuseStep 5240753 = 3930565) B3930565
theorem B2947043 : Blo 1551473 2947043 := bstep (se 1 (by rfl) ⟨2210282, by rfl⟩ : syracuseStep 2947043 = 4420565) B4420565
theorem B9951245 : Blo 1551473 9951245 := bstep (se 3 (by rfl) ⟨1865858, by rfl⟩ : syracuseStep 9951245 = 3731717) B3731717
theorem B2488337 : Blo 1551473 2488337 := bstep (se 2 (by rfl) ⟨933126, by rfl⟩ : syracuseStep 2488337 = 1866253) B1866253
theorem B2619425 : Blo 1551473 2619425 := bstep (se 2 (by rfl) ⟨982284, by rfl⟩ : syracuseStep 2619425 = 1964569) B1964569
theorem B1964083 : Blo 1551473 1964083 := bstep (se 1 (by rfl) ⟨1473062, by rfl⟩ : syracuseStep 1964083 = 2946125) B2946125
theorem B4970573 : Blo 1551473 4970573 := bstep (se 3 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 4970573 = 1863965) B1863965
theorem B1964179 : Blo 1551473 1964179 := bstep (se 1 (by rfl) ⟨1473134, by rfl⟩ : syracuseStep 1964179 = 2946269) B2946269
theorem B2619553 : Blo 1551473 2619553 := bstep (se 2 (by rfl) ⟨982332, by rfl⟩ : syracuseStep 2619553 = 1964665) B1964665
theorem B2619587 : Blo 1551473 2619587 := bstep (se 1 (by rfl) ⟨1964690, by rfl⟩ : syracuseStep 2619587 = 3929381) B3929381
theorem B3930353 : Blo 1551473 3930353 := bstep (se 2 (by rfl) ⟨1473882, by rfl⟩ : syracuseStep 3930353 = 2947765) B2947765
theorem B3315971 : Blo 1551473 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B3930403 : Blo 1551473 3930403 := bstep (se 1 (by rfl) ⟨2947802, by rfl⟩ : syracuseStep 3930403 = 5895605) B5895605
theorem B2619715 : Blo 1551473 2619715 := bstep (se 1 (by rfl) ⟨1964786, by rfl⟩ : syracuseStep 2619715 = 3929573) B3929573
theorem B5896547 : Blo 1551473 5896547 := bstep (se 1 (by rfl) ⟨4422410, by rfl⟩ : syracuseStep 5896547 = 8844821) B8844821
theorem B16791907 : Blo 1551473 16791907 := bstep (se 1 (by rfl) ⟨12593930, by rfl⟩ : syracuseStep 16791907 = 25187861) B25187861
theorem B7862669 : Blo 1551473 7862669 := bstep (se 3 (by rfl) ⟨1474250, by rfl⟩ : syracuseStep 7862669 = 2948501) B2948501
theorem B3930545 : Blo 1551473 3930545 := bstep (se 2 (by rfl) ⟨1473954, by rfl⟩ : syracuseStep 3930545 = 2947909) B2947909
theorem B5241293 : Blo 1551473 5241293 := bstep (se 3 (by rfl) ⟨982742, by rfl⟩ : syracuseStep 5241293 = 1965485) B1965485
theorem B2619857 : Blo 1551473 2619857 := bstep (se 2 (by rfl) ⟨982446, by rfl⟩ : syracuseStep 2619857 = 1964893) B1964893
theorem B5241347 : Blo 1551473 5241347 := bstep (se 1 (by rfl) ⟨3931010, by rfl⟩ : syracuseStep 5241347 = 7862021) B7862021
theorem B2210323 : Blo 1551473 2210323 := bstep (se 1 (by rfl) ⟨1657742, by rfl⟩ : syracuseStep 2210323 = 3315485) B3315485
theorem B6634061 : Blo 1551473 6634061 := bstep (se 3 (by rfl) ⟨1243886, by rfl⟩ : syracuseStep 6634061 = 2487773) B2487773
theorem B2619985 : Blo 1551473 2619985 := bstep (se 2 (by rfl) ⟨982494, by rfl⟩ : syracuseStep 2619985 = 1964989) B1964989
theorem B2210419 : Blo 1551473 2210419 := bstep (se 1 (by rfl) ⟨1657814, by rfl⟩ : syracuseStep 2210419 = 3315629) B3315629
theorem B2620019 : Blo 1551473 2620019 := bstep (se 1 (by rfl) ⟨1965014, by rfl⟩ : syracuseStep 2620019 = 3930029) B3930029
theorem B1964675 : Blo 1551473 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B2620147 : Blo 1551473 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B5241617 : Blo 1551473 5241617 := bstep (se 2 (by rfl) ⟨1965606, by rfl⟩ : syracuseStep 5241617 = 3931213) B3931213
theorem B2620289 : Blo 1551473 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B2947985 : Blo 1551473 2947985 := bstep (se 2 (by rfl) ⟨1105494, by rfl⟩ : syracuseStep 2947985 = 2210989) B2210989
theorem B2620417 : Blo 1551473 2620417 := bstep (se 2 (by rfl) ⟨982656, by rfl⟩ : syracuseStep 2620417 = 1965313) B1965313
theorem B2620451 : Blo 1551473 2620451 := bstep (se 1 (by rfl) ⟨1965338, by rfl⟩ : syracuseStep 2620451 = 3930677) B3930677
theorem B9444401 : Blo 1551473 9444401 := bstep (se 2 (by rfl) ⟨3541650, by rfl⟩ : syracuseStep 9444401 = 7083301) B7083301
theorem B2210915 : Blo 1551473 2210915 := bstep (se 1 (by rfl) ⟨1658186, by rfl⟩ : syracuseStep 2210915 = 3316373) B3316373
theorem B7855217 : Blo 1551473 7855217 := bstep (se 2 (by rfl) ⟨2945706, by rfl⟩ : syracuseStep 7855217 = 5891413) B5891413
theorem B2620579 : Blo 1551473 2620579 := bstep (se 1 (by rfl) ⟨1965434, by rfl⟩ : syracuseStep 2620579 = 3930869) B3930869
theorem B4422833 : Blo 1551473 4422833 := bstep (se 2 (by rfl) ⟨1658562, by rfl⟩ : syracuseStep 4422833 = 3317125) B3317125
theorem B3316945 : Blo 1551473 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B8846597 : Blo 1551473 8846597 := bstep (se 4 (by rfl) ⟨829368, by rfl⟩ : syracuseStep 8846597 = 1658737) B1658737
theorem B5242157 : Blo 1551473 5242157 := bstep (se 3 (by rfl) ⟨982904, by rfl⟩ : syracuseStep 5242157 = 1965809) B1965809
theorem B2620721 : Blo 1551473 2620721 := bstep (se 2 (by rfl) ⟨982770, by rfl⟩ : syracuseStep 2620721 = 1965541) B1965541
theorem B1965379 : Blo 1551473 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B5897549 : Blo 1551473 5897549 := bstep (se 3 (by rfl) ⟨1105790, by rfl⟩ : syracuseStep 5897549 = 2211581) B2211581
theorem B5242211 : Blo 1551473 5242211 := bstep (se 1 (by rfl) ⟨3931658, by rfl⟩ : syracuseStep 5242211 = 7863317) B7863317
theorem B4423025 : Blo 1551473 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B3931537 : Blo 1551473 3931537 := bstep (se 2 (by rfl) ⟨1474326, by rfl⟩ : syracuseStep 3931537 = 2948653) B2948653
theorem B1965475 : Blo 1551473 1965475 := bstep (se 1 (by rfl) ⟨1474106, by rfl⟩ : syracuseStep 1965475 = 2948213) B2948213
theorem B2620849 : Blo 1551473 2620849 := bstep (se 2 (by rfl) ⟨982818, by rfl⟩ : syracuseStep 2620849 = 1965637) B1965637
theorem B3317201 : Blo 1551473 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B2620883 : Blo 1551473 2620883 := bstep (se 1 (by rfl) ⟨1965662, by rfl⟩ : syracuseStep 2620883 = 3931325) B3931325
theorem B5455331 : Blo 1551473 5455331 := bstep (se 1 (by rfl) ⟨4091498, by rfl⟩ : syracuseStep 5455331 = 8182997) B8182997
theorem B5668337 : Blo 1551473 5668337 := bstep (se 2 (by rfl) ⟨2125626, by rfl⟩ : syracuseStep 5668337 = 4251253) B4251253
theorem B4972099 : Blo 1551473 4972099 := bstep (se 1 (by rfl) ⟨3729074, by rfl⟩ : syracuseStep 4972099 = 7458149) B7458149
theorem B2621011 : Blo 1551473 2621011 := bstep (se 1 (by rfl) ⟨1965758, by rfl⟩ : syracuseStep 2621011 = 3931517) B3931517
theorem B5242481 : Blo 1551473 5242481 := bstep (se 2 (by rfl) ⟨1965930, by rfl⟩ : syracuseStep 5242481 = 3931861) B3931861
theorem B3931811 : Blo 1551473 3931811 := bstep (se 1 (by rfl) ⟨2948858, by rfl⟩ : syracuseStep 3931811 = 5897717) B5897717
theorem B9445061 : Blo 1551473 9445061 := bstep (se 4 (by rfl) ⟨885474, by rfl⟩ : syracuseStep 9445061 = 1770949) B1770949
theorem B8847053 : Blo 1551473 8847053 := bstep (se 3 (by rfl) ⟨1658822, by rfl⟩ : syracuseStep 8847053 = 3317645) B3317645
theorem B2211553 : Blo 1551473 2211553 := bstep (se 2 (by rfl) ⟨829332, by rfl⟩ : syracuseStep 2211553 = 1658665) B1658665
theorem B2621153 : Blo 1551473 2621153 := bstep (se 2 (by rfl) ⟨982932, by rfl⟩ : syracuseStep 2621153 = 1965865) B1965865
theorem B2359027 : Blo 1551473 2359027 := bstep (se 1 (by rfl) ⟨1769270, by rfl⟩ : syracuseStep 2359027 = 3538541) B3538541
theorem B2948881 : Blo 1551473 2948881 := bstep (se 2 (by rfl) ⟨1105830, by rfl⟩ : syracuseStep 2948881 = 2211661) B2211661
theorem B2096929 : Blo 1551473 2096929 := bstep (se 2 (by rfl) ⟨786348, by rfl⟩ : syracuseStep 2096929 = 1572697) B1572697
theorem B8838989 : Blo 1551473 8838989 := bstep (se 3 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 8838989 = 3314621) B3314621
theorem B2621281 : Blo 1551473 2621281 := bstep (se 2 (by rfl) ⟨982980, by rfl⟩ : syracuseStep 2621281 = 1965961) B1965961
theorem B3145571 : Blo 1551473 3145571 := bstep (se 1 (by rfl) ⟨2359178, by rfl⟩ : syracuseStep 3145571 = 4718357) B4718357
theorem B3932003 : Blo 1551473 3932003 := bstep (se 1 (by rfl) ⟨2949002, by rfl⟩ : syracuseStep 3932003 = 5898005) B5898005
theorem B15327089 : Blo 1551473 15327089 := bstep (se 2 (by rfl) ⟨5747658, by rfl⟩ : syracuseStep 15327089 = 11495317) B11495317
theorem B2621315 : Blo 1551473 2621315 := bstep (se 1 (by rfl) ⟨1965986, by rfl⟩ : syracuseStep 2621315 = 3931973) B3931973
theorem B1965971 : Blo 1551473 1965971 := bstep (se 1 (by rfl) ⟨1474478, by rfl⟩ : syracuseStep 1965971 = 2948957) B2948957
theorem B2949041 : Blo 1551473 2949041 := bstep (se 2 (by rfl) ⟨1105890, by rfl⟩ : syracuseStep 2949041 = 2211781) B2211781
theorem B7864451 : Blo 1551473 7864451 := bstep (se 1 (by rfl) ⟨5898338, by rfl⟩ : syracuseStep 7864451 = 11796677) B11796677
theorem B8839489 : Blo 1551473 8839489 := bstep (se 2 (by rfl) ⟨3314808, by rfl⟩ : syracuseStep 8839489 = 6629617) B6629617
theorem B4252097 : Blo 1551473 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B22389209 : Blo 1551473 22389209 := bstep (se 2 (by rfl) ⟨8395953, by rfl⟩ : syracuseStep 22389209 = 16791907) B16791907
theorem B1745419 : Blo 1551473 1745419 := bstep (se 1 (by rfl) ⟨1309064, by rfl⟩ : syracuseStep 1745419 = 2618129) B2618129
theorem B11788901 : Blo 1551473 11788901 := bstep (se 4 (by rfl) ⟨1105209, by rfl⟩ : syracuseStep 11788901 = 2210419) B2210419
theorem B1745527 : Blo 1551473 1745527 := bstep (se 1 (by rfl) ⟨1309145, by rfl⟩ : syracuseStep 1745527 = 2618291) B2618291
theorem B3539609 : Blo 1551473 3539609 := bstep (se 2 (by rfl) ⟨1327353, by rfl⟩ : syracuseStep 3539609 = 2654707) B2654707
theorem B6628013 : Blo 1551473 6628013 := bstep (se 3 (by rfl) ⟨1242752, by rfl⟩ : syracuseStep 6628013 = 2485505) B2485505
theorem B2327243 : Blo 1551473 2327243 := bstep (se 1 (by rfl) ⟨1745432, by rfl⟩ : syracuseStep 2327243 = 3490865) B3490865
theorem B2327255 : Blo 1551473 2327255 := bstep (se 1 (by rfl) ⟨1745441, by rfl⟩ : syracuseStep 2327255 = 3490883) B3490883
theorem B2327321 : Blo 1551473 2327321 := bstep (se 2 (by rfl) ⟨872745, by rfl⟩ : syracuseStep 2327321 = 1745491) B1745491
theorem B1745707 : Blo 1551473 1745707 := bstep (se 1 (by rfl) ⟨1309280, by rfl⟩ : syracuseStep 1745707 = 2618561) B2618561
theorem B2327435 : Blo 1551473 2327435 := bstep (se 1 (by rfl) ⟨1745576, by rfl⟩ : syracuseStep 2327435 = 3491153) B3491153
theorem B2327447 : Blo 1551473 2327447 := bstep (se 1 (by rfl) ⟨1745585, by rfl⟩ : syracuseStep 2327447 = 3491171) B3491171
theorem B1745815 : Blo 1551473 1745815 := bstep (se 1 (by rfl) ⟨1309361, by rfl⟩ : syracuseStep 1745815 = 2618723) B2618723
theorem B2327513 : Blo 1551473 2327513 := bstep (se 2 (by rfl) ⟨872817, by rfl⟩ : syracuseStep 2327513 = 1745635) B1745635
theorem B7463897 : Blo 1551473 7463897 := bstep (se 2 (by rfl) ⟨2798961, by rfl⟩ : syracuseStep 7463897 = 5597923) B5597923
theorem B3982387 : Blo 1551473 3982387 := bstep (se 1 (by rfl) ⟨2986790, by rfl⟩ : syracuseStep 3982387 = 5973581) B5973581
theorem B2327627 : Blo 1551473 2327627 := bstep (se 1 (by rfl) ⟨1745720, by rfl⟩ : syracuseStep 2327627 = 3491441) B3491441
theorem B1745995 : Blo 1551473 1745995 := bstep (se 1 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 1745995 = 2618993) B2618993
theorem B11789387 : Blo 1551473 11789387 := bstep (se 1 (by rfl) ⟨8842040, by rfl⟩ : syracuseStep 11789387 = 17684081) B17684081
theorem B2327639 : Blo 1551473 2327639 := bstep (se 1 (by rfl) ⟨1745729, by rfl⟩ : syracuseStep 2327639 = 3491459) B3491459
theorem B3490955 : Blo 1551473 3490955 := bstep (se 1 (by rfl) ⟨2618216, by rfl⟩ : syracuseStep 3490955 = 5236433) B5236433
theorem B2327705 : Blo 1551473 2327705 := bstep (se 2 (by rfl) ⟨872889, by rfl⟩ : syracuseStep 2327705 = 1745779) B1745779
theorem B1746103 : Blo 1551473 1746103 := bstep (se 1 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 1746103 = 2619155) B2619155
theorem B3491009 : Blo 1551473 3491009 := bstep (se 2 (by rfl) ⟨1309128, by rfl⟩ : syracuseStep 3491009 = 2618257) B2618257
theorem B29828357 : Blo 1551473 29828357 := bstep (se 4 (by rfl) ⟨2796408, by rfl⟩ : syracuseStep 29828357 = 5592817) B5592817
theorem B2327819 : Blo 1551473 2327819 := bstep (se 1 (by rfl) ⟨1745864, by rfl⟩ : syracuseStep 2327819 = 3491729) B3491729
theorem B2327831 : Blo 1551473 2327831 := bstep (se 1 (by rfl) ⟨1745873, by rfl⟩ : syracuseStep 2327831 = 3491747) B3491747
theorem B15115565 : Blo 1551473 15115565 := bstep (se 3 (by rfl) ⟨2834168, by rfl⟩ : syracuseStep 15115565 = 5668337) B5668337
theorem B2327897 : Blo 1551473 2327897 := bstep (se 2 (by rfl) ⟨872961, by rfl⟩ : syracuseStep 2327897 = 1745923) B1745923
theorem B6292829 : Blo 1551473 6292829 := bstep (se 3 (by rfl) ⟨1179905, by rfl⟩ : syracuseStep 6292829 = 2359811) B2359811
theorem B1746283 : Blo 1551473 1746283 := bstep (se 1 (by rfl) ⟨1309712, by rfl⟩ : syracuseStep 1746283 = 2619425) B2619425
theorem B7456151 : Blo 1551473 7456151 := bstep (se 1 (by rfl) ⟨5592113, by rfl⟩ : syracuseStep 7456151 = 11184227) B11184227
theorem B3491225 : Blo 1551473 3491225 := bstep (se 2 (by rfl) ⟨1309209, by rfl⟩ : syracuseStep 3491225 = 2618419) B2618419
theorem B2328011 : Blo 1551473 2328011 := bstep (se 1 (by rfl) ⟨1746008, by rfl⟩ : syracuseStep 2328011 = 3492017) B3492017
theorem B2328023 : Blo 1551473 2328023 := bstep (se 1 (by rfl) ⟨1746017, by rfl⟩ : syracuseStep 2328023 = 3492035) B3492035
theorem B1746391 : Blo 1551473 1746391 := bstep (se 1 (by rfl) ⟨1309793, by rfl⟩ : syracuseStep 1746391 = 2619587) B2619587
theorem B3491315 : Blo 1551473 3491315 := bstep (se 1 (by rfl) ⟨2618486, by rfl⟩ : syracuseStep 3491315 = 5236973) B5236973
theorem B3491351 : Blo 1551473 3491351 := bstep (se 1 (by rfl) ⟨2618513, by rfl⟩ : syracuseStep 3491351 = 5237027) B5237027
theorem B2328089 : Blo 1551473 2328089 := bstep (se 2 (by rfl) ⟨873033, by rfl⟩ : syracuseStep 2328089 = 1746067) B1746067
theorem B2098777 : Blo 1551473 2098777 := bstep (se 2 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 2098777 = 1574083) B1574083
theorem B6293123 : Blo 1551473 6293123 := bstep (se 1 (by rfl) ⟨4719842, by rfl⟩ : syracuseStep 6293123 = 9439685) B9439685
theorem B2328203 : Blo 1551473 2328203 := bstep (se 1 (by rfl) ⟨1746152, by rfl⟩ : syracuseStep 2328203 = 3492305) B3492305
theorem B1746571 : Blo 1551473 1746571 := bstep (se 1 (by rfl) ⟨1309928, by rfl⟩ : syracuseStep 1746571 = 2619857) B2619857
theorem B2328215 : Blo 1551473 2328215 := bstep (se 1 (by rfl) ⟨1746161, by rfl⟩ : syracuseStep 2328215 = 3492323) B3492323
theorem B3491531 : Blo 1551473 3491531 := bstep (se 1 (by rfl) ⟨2618648, by rfl⟩ : syracuseStep 3491531 = 5237297) B5237297
theorem B2328281 : Blo 1551473 2328281 := bstep (se 2 (by rfl) ⟨873105, by rfl⟩ : syracuseStep 2328281 = 1746211) B1746211
theorem B1746679 : Blo 1551473 1746679 := bstep (se 1 (by rfl) ⟨1310009, by rfl⟩ : syracuseStep 1746679 = 2620019) B2620019
theorem B3491585 : Blo 1551473 3491585 := bstep (se 2 (by rfl) ⟨1309344, by rfl⟩ : syracuseStep 3491585 = 2618689) B2618689
theorem B5891885 : Blo 1551473 5891885 := bstep (se 3 (by rfl) ⟨1104728, by rfl⟩ : syracuseStep 5891885 = 2209457) B2209457
theorem B2328395 : Blo 1551473 2328395 := bstep (se 1 (by rfl) ⟨1746296, by rfl⟩ : syracuseStep 2328395 = 3492593) B3492593
theorem B2328407 : Blo 1551473 2328407 := bstep (se 1 (by rfl) ⟨1746305, by rfl⟩ : syracuseStep 2328407 = 3492611) B3492611
theorem B2328473 : Blo 1551473 2328473 := bstep (se 2 (by rfl) ⟨873177, by rfl⟩ : syracuseStep 2328473 = 1746355) B1746355
theorem B1746859 : Blo 1551473 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B14911411 : Blo 1551473 14911411 := bstep (se 1 (by rfl) ⟨11183558, by rfl⟩ : syracuseStep 14911411 = 22367117) B22367117
theorem B3360727 : Blo 1551473 3360727 := bstep (se 1 (by rfl) ⟨2520545, by rfl⟩ : syracuseStep 3360727 = 5041091) B5041091
theorem B3491801 : Blo 1551473 3491801 := bstep (se 2 (by rfl) ⟨1309425, by rfl⟩ : syracuseStep 3491801 = 2618851) B2618851
theorem B2328587 : Blo 1551473 2328587 := bstep (se 1 (by rfl) ⟨1746440, by rfl⟩ : syracuseStep 2328587 = 3492881) B3492881
theorem B8185873 : Blo 1551473 8185873 := bstep (se 2 (by rfl) ⟨3069702, by rfl⟩ : syracuseStep 8185873 = 6139405) B6139405
theorem B2328599 : Blo 1551473 2328599 := bstep (se 1 (by rfl) ⟨1746449, by rfl⟩ : syracuseStep 2328599 = 3492899) B3492899
theorem B1746967 : Blo 1551473 1746967 := bstep (se 1 (by rfl) ⟨1310225, by rfl⟩ : syracuseStep 1746967 = 2620451) B2620451
theorem B31868963 : Blo 1551473 31868963 := bstep (se 1 (by rfl) ⟨23901722, by rfl⟩ : syracuseStep 31868963 = 47803445) B47803445
theorem B1656875 : Blo 1551473 1656875 := bstep (se 1 (by rfl) ⟨1242656, by rfl⟩ : syracuseStep 1656875 = 2485313) B2485313
theorem B3491891 : Blo 1551473 3491891 := bstep (se 1 (by rfl) ⟨2618918, by rfl⟩ : syracuseStep 3491891 = 5237837) B5237837
theorem B5236811 : Blo 1551473 5236811 := bstep (se 1 (by rfl) ⟨3927608, by rfl⟩ : syracuseStep 5236811 = 7855217) B7855217
theorem B3541067 : Blo 1551473 3541067 := bstep (se 1 (by rfl) ⟨2655800, by rfl⟩ : syracuseStep 3541067 = 5311601) B5311601
theorem B3491927 : Blo 1551473 3491927 := bstep (se 1 (by rfl) ⟨2618945, by rfl⟩ : syracuseStep 3491927 = 5237891) B5237891
theorem B6629465 : Blo 1551473 6629465 := bstep (se 2 (by rfl) ⟨2486049, by rfl⟩ : syracuseStep 6629465 = 4972099) B4972099
theorem B2328665 : Blo 1551473 2328665 := bstep (se 2 (by rfl) ⟨873249, by rfl⟩ : syracuseStep 2328665 = 1746499) B1746499
theorem B3360971 : Blo 1551473 3360971 := bstep (se 1 (by rfl) ⟨2520728, by rfl⟩ : syracuseStep 3360971 = 5041457) B5041457
theorem B2328779 : Blo 1551473 2328779 := bstep (se 1 (by rfl) ⟨1746584, by rfl⟩ : syracuseStep 2328779 = 3493169) B3493169
theorem B1747147 : Blo 1551473 1747147 := bstep (se 1 (by rfl) ⟨1310360, by rfl⟩ : syracuseStep 1747147 = 2620721) B2620721
theorem B2328791 : Blo 1551473 2328791 := bstep (se 1 (by rfl) ⟨1746593, by rfl⟩ : syracuseStep 2328791 = 3493187) B3493187
theorem B3492107 : Blo 1551473 3492107 := bstep (se 1 (by rfl) ⟨2619080, by rfl⟩ : syracuseStep 3492107 = 5238161) B5238161
theorem B2328857 : Blo 1551473 2328857 := bstep (se 2 (by rfl) ⟨873321, by rfl⟩ : syracuseStep 2328857 = 1746643) B1746643
theorem B1747255 : Blo 1551473 1747255 := bstep (se 1 (by rfl) ⟨1310441, by rfl⟩ : syracuseStep 1747255 = 2620883) B2620883
theorem B3492161 : Blo 1551473 3492161 := bstep (se 2 (by rfl) ⟨1309560, by rfl⟩ : syracuseStep 3492161 = 2619121) B2619121
theorem B5237081 : Blo 1551473 5237081 := bstep (se 2 (by rfl) ⟨1963905, by rfl⟩ : syracuseStep 5237081 = 3927811) B3927811
theorem B2795905 : Blo 1551473 2795905 := bstep (se 2 (by rfl) ⟨1048464, by rfl⟩ : syracuseStep 2795905 = 2096929) B2096929
theorem B2328971 : Blo 1551473 2328971 := bstep (se 1 (by rfl) ⟨1746728, by rfl⟩ : syracuseStep 2328971 = 3493457) B3493457
theorem B2328983 : Blo 1551473 2328983 := bstep (se 1 (by rfl) ⟨1746737, by rfl⟩ : syracuseStep 2328983 = 3493475) B3493475
theorem B7375283 : Blo 1551473 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B2329049 : Blo 1551473 2329049 := bstep (se 2 (by rfl) ⟨873393, by rfl⟩ : syracuseStep 2329049 = 1746787) B1746787
theorem B1747435 : Blo 1551473 1747435 := bstep (se 1 (by rfl) ⟨1310576, by rfl⟩ : syracuseStep 1747435 = 2621153) B2621153
theorem B3492377 : Blo 1551473 3492377 := bstep (se 2 (by rfl) ⟨1309641, by rfl⟩ : syracuseStep 3492377 = 2619283) B2619283
theorem B5892659 : Blo 1551473 5892659 := bstep (se 1 (by rfl) ⟨4419494, by rfl⟩ : syracuseStep 5892659 = 8838989) B8838989
theorem B5311027 : Blo 1551473 5311027 := bstep (se 1 (by rfl) ⟨3983270, by rfl⟩ : syracuseStep 5311027 = 7966541) B7966541
theorem B10218059 : Blo 1551473 10218059 := bstep (se 1 (by rfl) ⟨7663544, by rfl⟩ : syracuseStep 10218059 = 15327089) B15327089
theorem B2329163 : Blo 1551473 2329163 := bstep (se 1 (by rfl) ⟨1746872, by rfl⟩ : syracuseStep 2329163 = 3493745) B3493745
theorem B2329175 : Blo 1551473 2329175 := bstep (se 1 (by rfl) ⟨1746881, by rfl⟩ : syracuseStep 2329175 = 3493763) B3493763
theorem B1747543 : Blo 1551473 1747543 := bstep (se 1 (by rfl) ⟨1310657, by rfl⟩ : syracuseStep 1747543 = 2621315) B2621315
theorem B7858781 : Blo 1551473 7858781 := bstep (se 3 (by rfl) ⟨1473521, by rfl⟩ : syracuseStep 7858781 = 2947043) B2947043
theorem B3492467 : Blo 1551473 3492467 := bstep (se 1 (by rfl) ⟨2619350, by rfl⟩ : syracuseStep 3492467 = 5238701) B5238701
theorem B3492503 : Blo 1551473 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B2329241 : Blo 1551473 2329241 := bstep (se 2 (by rfl) ⟨873465, by rfl⟩ : syracuseStep 2329241 = 1746931) B1746931
theorem B7080641 : Blo 1551473 7080641 := bstep (se 2 (by rfl) ⟨2655240, by rfl⟩ : syracuseStep 7080641 = 5310481) B5310481
theorem B2837207 : Blo 1551473 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B2329355 : Blo 1551473 2329355 := bstep (se 1 (by rfl) ⟨1747016, by rfl⟩ : syracuseStep 2329355 = 3494033) B3494033
theorem B3148555 : Blo 1551473 3148555 := bstep (se 1 (by rfl) ⟨2361416, by rfl⟩ : syracuseStep 3148555 = 4722833) B4722833
theorem B2329367 : Blo 1551473 2329367 := bstep (se 1 (by rfl) ⟨1747025, by rfl⟩ : syracuseStep 2329367 = 3494051) B3494051
theorem B3492683 : Blo 1551473 3492683 := bstep (se 1 (by rfl) ⟨2619512, by rfl⟩ : syracuseStep 3492683 = 5239025) B5239025
theorem B2329433 : Blo 1551473 2329433 := bstep (se 2 (by rfl) ⟨873537, by rfl⟩ : syracuseStep 2329433 = 1747075) B1747075
theorem B6384473 : Blo 1551473 6384473 := bstep (se 2 (by rfl) ⟨2394177, by rfl⟩ : syracuseStep 6384473 = 4788355) B4788355
theorem B7457629 : Blo 1551473 7457629 := bstep (se 3 (by rfl) ⟨1398305, by rfl⟩ : syracuseStep 7457629 = 2796611) B2796611
theorem B3492737 : Blo 1551473 3492737 := bstep (se 2 (by rfl) ⟨1309776, by rfl⟩ : syracuseStep 3492737 = 2619553) B2619553
theorem B13265795 : Blo 1551473 13265795 := bstep (se 1 (by rfl) ⟨9949346, by rfl⟩ : syracuseStep 13265795 = 19898693) B19898693
theorem B2796439 : Blo 1551473 2796439 := bstep (se 1 (by rfl) ⟨2097329, by rfl⟩ : syracuseStep 2796439 = 4194659) B4194659
theorem B2329547 : Blo 1551473 2329547 := bstep (se 1 (by rfl) ⟨1747160, by rfl⟩ : syracuseStep 2329547 = 3494321) B3494321
theorem B2329559 : Blo 1551473 2329559 := bstep (se 1 (by rfl) ⟨1747169, by rfl⟩ : syracuseStep 2329559 = 3494339) B3494339
theorem B5237783 : Blo 1551473 5237783 := bstep (se 1 (by rfl) ⟨3928337, by rfl⟩ : syracuseStep 5237783 = 7856675) B7856675
theorem B2329625 : Blo 1551473 2329625 := bstep (se 2 (by rfl) ⟨873609, by rfl⟩ : syracuseStep 2329625 = 1747219) B1747219
theorem B12586049 : Blo 1551473 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B3492953 : Blo 1551473 3492953 := bstep (se 2 (by rfl) ⟨1309857, by rfl⟩ : syracuseStep 3492953 = 2619715) B2619715
theorem B1551479 : Blo 1551473 1551479 := bstep (se 1 (by rfl) ⟨1163609, by rfl⟩ : syracuseStep 1551479 = 2327219) B2327219
theorem B1551499 : Blo 1551473 1551499 := bstep (se 1 (by rfl) ⟨1163624, by rfl⟩ : syracuseStep 1551499 = 2327249) B2327249
theorem B2329739 : Blo 1551473 2329739 := bstep (se 1 (by rfl) ⟨1747304, by rfl⟩ : syracuseStep 2329739 = 3494609) B3494609
theorem B5598353 : Blo 1551473 5598353 := bstep (se 2 (by rfl) ⟨2099382, by rfl⟩ : syracuseStep 5598353 = 4198765) B4198765
theorem B1551511 : Blo 1551473 1551511 := bstep (se 1 (by rfl) ⟨1163633, by rfl⟩ : syracuseStep 1551511 = 2327267) B2327267
theorem B2329751 : Blo 1551473 2329751 := bstep (se 1 (by rfl) ⟨1747313, by rfl⟩ : syracuseStep 2329751 = 3494627) B3494627
theorem B1551531 : Blo 1551473 1551531 := bstep (se 1 (by rfl) ⟨1163648, by rfl⟩ : syracuseStep 1551531 = 2327297) B2327297
theorem B3493043 : Blo 1551473 3493043 := bstep (se 1 (by rfl) ⟨2619782, by rfl⟩ : syracuseStep 3493043 = 5239565) B5239565
theorem B28314805 : Blo 1551473 28314805 := bstep (se 5 (by rfl) ⟨1327256, by rfl⟩ : syracuseStep 28314805 = 2654513) B2654513
theorem B1551543 : Blo 1551473 1551543 := bstep (se 1 (by rfl) ⟨1163657, by rfl⟩ : syracuseStep 1551543 = 2327315) B2327315
theorem B1551563 : Blo 1551473 1551563 := bstep (se 1 (by rfl) ⟨1163672, by rfl⟩ : syracuseStep 1551563 = 2327345) B2327345
theorem B1551575 : Blo 1551473 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B3493079 : Blo 1551473 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B1658071 : Blo 1551473 1658071 := bstep (se 1 (by rfl) ⟨1243553, by rfl⟩ : syracuseStep 1658071 = 2487107) B2487107
theorem B8744153 : Blo 1551473 8744153 := bstep (se 2 (by rfl) ⟨3279057, by rfl⟩ : syracuseStep 8744153 = 6558115) B6558115
theorem B2329817 : Blo 1551473 2329817 := bstep (se 2 (by rfl) ⟨873681, by rfl⟩ : syracuseStep 2329817 = 1747363) B1747363
theorem B1551595 : Blo 1551473 1551595 := bstep (se 1 (by rfl) ⟨1163696, by rfl⟩ : syracuseStep 1551595 = 2327393) B2327393
theorem B1551607 : Blo 1551473 1551607 := bstep (se 1 (by rfl) ⟨1163705, by rfl⟩ : syracuseStep 1551607 = 2327411) B2327411
theorem B72682757 : Blo 1551473 72682757 := bstep (se 4 (by rfl) ⟨6814008, by rfl⟩ : syracuseStep 72682757 = 13628017) B13628017
theorem B1551627 : Blo 1551473 1551627 := bstep (se 1 (by rfl) ⟨1163720, by rfl⟩ : syracuseStep 1551627 = 2327441) B2327441
theorem B1551639 : Blo 1551473 1551639 := bstep (se 1 (by rfl) ⟨1163729, by rfl⟩ : syracuseStep 1551639 = 2327459) B2327459
theorem B1551659 : Blo 1551473 1551659 := bstep (se 1 (by rfl) ⟨1163744, by rfl⟩ : syracuseStep 1551659 = 2327489) B2327489
theorem B1551671 : Blo 1551473 1551671 := bstep (se 1 (by rfl) ⟨1163753, by rfl⟩ : syracuseStep 1551671 = 2327507) B2327507
theorem B1551691 : Blo 1551473 1551691 := bstep (se 1 (by rfl) ⟨1163768, by rfl⟩ : syracuseStep 1551691 = 2327537) B2327537
theorem B2329931 : Blo 1551473 2329931 := bstep (se 1 (by rfl) ⟨1747448, by rfl⟩ : syracuseStep 2329931 = 3494897) B3494897
theorem B1551703 : Blo 1551473 1551703 := bstep (se 1 (by rfl) ⟨1163777, by rfl⟩ : syracuseStep 1551703 = 2327555) B2327555
theorem B2329943 : Blo 1551473 2329943 := bstep (se 1 (by rfl) ⟨1747457, by rfl⟩ : syracuseStep 2329943 = 3494915) B3494915
theorem B1551723 : Blo 1551473 1551723 := bstep (se 1 (by rfl) ⟨1163792, by rfl⟩ : syracuseStep 1551723 = 2327585) B2327585
theorem B1551735 : Blo 1551473 1551735 := bstep (se 1 (by rfl) ⟨1163801, by rfl⟩ : syracuseStep 1551735 = 2327603) B2327603
theorem B11783555 : Blo 1551473 11783555 := bstep (se 1 (by rfl) ⟨8837666, by rfl⟩ : syracuseStep 11783555 = 17675333) B17675333
theorem B1551755 : Blo 1551473 1551755 := bstep (se 1 (by rfl) ⟨1163816, by rfl⟩ : syracuseStep 1551755 = 2327633) B2327633
theorem B3493259 : Blo 1551473 3493259 := bstep (se 1 (by rfl) ⟨2619944, by rfl⟩ : syracuseStep 3493259 = 5239889) B5239889
theorem B1551767 : Blo 1551473 1551767 := bstep (se 1 (by rfl) ⟨1163825, by rfl⟩ : syracuseStep 1551767 = 2327651) B2327651
theorem B2330009 : Blo 1551473 2330009 := bstep (se 2 (by rfl) ⟨873753, by rfl⟩ : syracuseStep 2330009 = 1747507) B1747507
theorem B1551787 : Blo 1551473 1551787 := bstep (se 1 (by rfl) ⟨1163840, by rfl⟩ : syracuseStep 1551787 = 2327681) B2327681
theorem B1551799 : Blo 1551473 1551799 := bstep (se 1 (by rfl) ⟨1163849, by rfl⟩ : syracuseStep 1551799 = 2327699) B2327699
theorem B3493313 : Blo 1551473 3493313 := bstep (se 2 (by rfl) ⟨1309992, by rfl⟩ : syracuseStep 3493313 = 2619985) B2619985
theorem B1551819 : Blo 1551473 1551819 := bstep (se 1 (by rfl) ⟨1163864, by rfl⟩ : syracuseStep 1551819 = 2327729) B2327729
theorem B1551831 : Blo 1551473 1551831 := bstep (se 1 (by rfl) ⟨1163873, by rfl⟩ : syracuseStep 1551831 = 2327747) B2327747
theorem B1658327 : Blo 1551473 1658327 := bstep (se 1 (by rfl) ⟨1243745, by rfl⟩ : syracuseStep 1658327 = 2487491) B2487491
theorem B1551851 : Blo 1551473 1551851 := bstep (se 1 (by rfl) ⟨1163888, by rfl⟩ : syracuseStep 1551851 = 2327777) B2327777
theorem B1551863 : Blo 1551473 1551863 := bstep (se 1 (by rfl) ⟨1163897, by rfl⟩ : syracuseStep 1551863 = 2327795) B2327795
theorem B1551883 : Blo 1551473 1551883 := bstep (se 1 (by rfl) ⟨1163912, by rfl⟩ : syracuseStep 1551883 = 2327825) B2327825
theorem B2330123 : Blo 1551473 2330123 := bstep (se 1 (by rfl) ⟨1747592, by rfl⟩ : syracuseStep 2330123 = 3495185) B3495185
theorem B1551895 : Blo 1551473 1551895 := bstep (se 1 (by rfl) ⟨1163921, by rfl⟩ : syracuseStep 1551895 = 2327843) B2327843
theorem B2330135 : Blo 1551473 2330135 := bstep (se 1 (by rfl) ⟨1747601, by rfl⟩ : syracuseStep 2330135 = 3495203) B3495203
theorem B1551915 : Blo 1551473 1551915 := bstep (se 1 (by rfl) ⟨1163936, by rfl⟩ : syracuseStep 1551915 = 2327873) B2327873
theorem B5238323 : Blo 1551473 5238323 := bstep (se 1 (by rfl) ⟨3928742, by rfl⟩ : syracuseStep 5238323 = 7857485) B7857485
theorem B1551927 : Blo 1551473 1551927 := bstep (se 1 (by rfl) ⟨1163945, by rfl⟩ : syracuseStep 1551927 = 2327891) B2327891
theorem B1551947 : Blo 1551473 1551947 := bstep (se 1 (by rfl) ⟨1163960, by rfl⟩ : syracuseStep 1551947 = 2327921) B2327921
theorem B1551959 : Blo 1551473 1551959 := bstep (se 1 (by rfl) ⟨1163969, by rfl⟩ : syracuseStep 1551959 = 2327939) B2327939
theorem B2330201 : Blo 1551473 2330201 := bstep (se 2 (by rfl) ⟨873825, by rfl⟩ : syracuseStep 2330201 = 1747651) B1747651
theorem B1551979 : Blo 1551473 1551979 := bstep (se 1 (by rfl) ⟨1163984, by rfl⟩ : syracuseStep 1551979 = 2327969) B2327969
theorem B1551991 : Blo 1551473 1551991 := bstep (se 1 (by rfl) ⟨1163993, by rfl⟩ : syracuseStep 1551991 = 2327987) B2327987
theorem B1552011 : Blo 1551473 1552011 := bstep (se 1 (by rfl) ⟨1164008, by rfl⟩ : syracuseStep 1552011 = 2328017) B2328017
theorem B1552023 : Blo 1551473 1552023 := bstep (se 1 (by rfl) ⟨1164017, by rfl⟩ : syracuseStep 1552023 = 2328035) B2328035
theorem B10628759 : Blo 1551473 10628759 := bstep (se 1 (by rfl) ⟨7971569, by rfl⟩ : syracuseStep 10628759 = 15943139) B15943139
theorem B3493529 : Blo 1551473 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B1552043 : Blo 1551473 1552043 := bstep (se 1 (by rfl) ⟨1164032, by rfl⟩ : syracuseStep 1552043 = 2328065) B2328065
theorem B8842931 : Blo 1551473 8842931 := bstep (se 1 (by rfl) ⟨6632198, by rfl⟩ : syracuseStep 8842931 = 13264397) B13264397
theorem B1552055 : Blo 1551473 1552055 := bstep (se 1 (by rfl) ⟨1164041, by rfl⟩ : syracuseStep 1552055 = 2328083) B2328083
theorem B6631105 : Blo 1551473 6631105 := bstep (se 2 (by rfl) ⟨2486664, by rfl⟩ : syracuseStep 6631105 = 4973329) B4973329
theorem B1552075 : Blo 1551473 1552075 := bstep (se 1 (by rfl) ⟨1164056, by rfl⟩ : syracuseStep 1552075 = 2328113) B2328113
theorem B1552087 : Blo 1551473 1552087 := bstep (se 1 (by rfl) ⟨1164065, by rfl⟩ : syracuseStep 1552087 = 2328131) B2328131
theorem B4419289 : Blo 1551473 4419289 := bstep (se 2 (by rfl) ⟨1657233, by rfl⟩ : syracuseStep 4419289 = 3314467) B3314467
theorem B1552107 : Blo 1551473 1552107 := bstep (se 1 (by rfl) ⟨1164080, by rfl⟩ : syracuseStep 1552107 = 2328161) B2328161
theorem B3493619 : Blo 1551473 3493619 := bstep (se 1 (by rfl) ⟨2620214, by rfl⟩ : syracuseStep 3493619 = 5240429) B5240429
theorem B1552119 : Blo 1551473 1552119 := bstep (se 1 (by rfl) ⟨1164089, by rfl⟩ : syracuseStep 1552119 = 2328179) B2328179
theorem B1552139 : Blo 1551473 1552139 := bstep (se 1 (by rfl) ⟨1164104, by rfl⟩ : syracuseStep 1552139 = 2328209) B2328209
theorem B1552151 : Blo 1551473 1552151 := bstep (se 1 (by rfl) ⟨1164113, by rfl⟩ : syracuseStep 1552151 = 2328227) B2328227
theorem B2952983 : Blo 1551473 2952983 := bstep (se 1 (by rfl) ⟨2214737, by rfl⟩ : syracuseStep 2952983 = 4429475) B4429475
theorem B3493655 : Blo 1551473 3493655 := bstep (se 1 (by rfl) ⟨2620241, by rfl⟩ : syracuseStep 3493655 = 5240483) B5240483
theorem B1552171 : Blo 1551473 1552171 := bstep (se 1 (by rfl) ⟨1164128, by rfl⟩ : syracuseStep 1552171 = 2328257) B2328257
theorem B1552183 : Blo 1551473 1552183 := bstep (se 1 (by rfl) ⟨1164137, by rfl⟩ : syracuseStep 1552183 = 2328275) B2328275
theorem B5238593 : Blo 1551473 5238593 := bstep (se 2 (by rfl) ⟨1964472, by rfl⟩ : syracuseStep 5238593 = 3928945) B3928945
theorem B1552203 : Blo 1551473 1552203 := bstep (se 1 (by rfl) ⟨1164152, by rfl⟩ : syracuseStep 1552203 = 2328305) B2328305
theorem B3731275 : Blo 1551473 3731275 := bstep (se 1 (by rfl) ⟨2798456, by rfl⟩ : syracuseStep 3731275 = 5596913) B5596913
theorem B1552215 : Blo 1551473 1552215 := bstep (se 1 (by rfl) ⟨1164161, by rfl⟩ : syracuseStep 1552215 = 2328323) B2328323
theorem B1552235 : Blo 1551473 1552235 := bstep (se 1 (by rfl) ⟨1164176, by rfl⟩ : syracuseStep 1552235 = 2328353) B2328353
theorem B1552247 : Blo 1551473 1552247 := bstep (se 1 (by rfl) ⟨1164185, by rfl⟩ : syracuseStep 1552247 = 2328371) B2328371
theorem B1552267 : Blo 1551473 1552267 := bstep (se 1 (by rfl) ⟨1164200, by rfl⟩ : syracuseStep 1552267 = 2328401) B2328401
theorem B1552279 : Blo 1551473 1552279 := bstep (se 1 (by rfl) ⟨1164209, by rfl⟩ : syracuseStep 1552279 = 2328419) B2328419
theorem B1552299 : Blo 1551473 1552299 := bstep (se 1 (by rfl) ⟨1164224, by rfl⟩ : syracuseStep 1552299 = 2328449) B2328449
theorem B1552311 : Blo 1551473 1552311 := bstep (se 1 (by rfl) ⟨1164233, by rfl⟩ : syracuseStep 1552311 = 2328467) B2328467
theorem B2797505 : Blo 1551473 2797505 := bstep (se 2 (by rfl) ⟨1049064, by rfl⟩ : syracuseStep 2797505 = 2098129) B2098129
theorem B1552331 : Blo 1551473 1552331 := bstep (se 1 (by rfl) ⟨1164248, by rfl⟩ : syracuseStep 1552331 = 2328497) B2328497
theorem B3493835 : Blo 1551473 3493835 := bstep (se 1 (by rfl) ⟨2620376, by rfl⟩ : syracuseStep 3493835 = 5240753) B5240753
theorem B1552343 : Blo 1551473 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B1552363 : Blo 1551473 1552363 := bstep (se 1 (by rfl) ⟨1164272, by rfl⟩ : syracuseStep 1552363 = 2328545) B2328545
theorem B1552375 : Blo 1551473 1552375 := bstep (se 1 (by rfl) ⟨1164281, by rfl⟩ : syracuseStep 1552375 = 2328563) B2328563
theorem B3493889 : Blo 1551473 3493889 := bstep (se 2 (by rfl) ⟨1310208, by rfl⟩ : syracuseStep 3493889 = 2620417) B2620417
theorem B5894147 : Blo 1551473 5894147 := bstep (se 1 (by rfl) ⟨4420610, by rfl⟩ : syracuseStep 5894147 = 8841221) B8841221
theorem B1552395 : Blo 1551473 1552395 := bstep (se 1 (by rfl) ⟨1164296, by rfl⟩ : syracuseStep 1552395 = 2328593) B2328593
theorem B1658891 : Blo 1551473 1658891 := bstep (se 1 (by rfl) ⟨1244168, by rfl⟩ : syracuseStep 1658891 = 2488337) B2488337
theorem B1552407 : Blo 1551473 1552407 := bstep (se 1 (by rfl) ⟨1164305, by rfl⟩ : syracuseStep 1552407 = 2328611) B2328611
theorem B1552427 : Blo 1551473 1552427 := bstep (se 1 (by rfl) ⟨1164320, by rfl⟩ : syracuseStep 1552427 = 2328641) B2328641
theorem B3313715 : Blo 1551473 3313715 := bstep (se 1 (by rfl) ⟨2485286, by rfl⟩ : syracuseStep 3313715 = 4970573) B4970573
theorem B3928115 : Blo 1551473 3928115 := bstep (se 1 (by rfl) ⟨2946086, by rfl⟩ : syracuseStep 3928115 = 5892173) B5892173
theorem B1552439 : Blo 1551473 1552439 := bstep (se 1 (by rfl) ⟨1164329, by rfl⟩ : syracuseStep 1552439 = 2328659) B2328659
theorem B1552459 : Blo 1551473 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B1552471 : Blo 1551473 1552471 := bstep (se 1 (by rfl) ⟨1164353, by rfl⟩ : syracuseStep 1552471 = 2328707) B2328707
theorem B4419677 : Blo 1551473 4419677 := bstep (se 3 (by rfl) ⟨828689, by rfl⟩ : syracuseStep 4419677 = 1657379) B1657379
theorem B1552491 : Blo 1551473 1552491 := bstep (se 1 (by rfl) ⟨1164368, by rfl⟩ : syracuseStep 1552491 = 2328737) B2328737
theorem B1552503 : Blo 1551473 1552503 := bstep (se 1 (by rfl) ⟨1164377, by rfl⟩ : syracuseStep 1552503 = 2328755) B2328755
theorem B1552523 : Blo 1551473 1552523 := bstep (se 1 (by rfl) ⟨1164392, by rfl⟩ : syracuseStep 1552523 = 2328785) B2328785
theorem B1552535 : Blo 1551473 1552535 := bstep (se 1 (by rfl) ⟨1164401, by rfl⟩ : syracuseStep 1552535 = 2328803) B2328803
theorem B1552555 : Blo 1551473 1552555 := bstep (se 1 (by rfl) ⟨1164416, by rfl⟩ : syracuseStep 1552555 = 2328833) B2328833
theorem B1552567 : Blo 1551473 1552567 := bstep (se 1 (by rfl) ⟨1164425, by rfl⟩ : syracuseStep 1552567 = 2328851) B2328851
theorem B1552587 : Blo 1551473 1552587 := bstep (se 1 (by rfl) ⟨1164440, by rfl⟩ : syracuseStep 1552587 = 2328881) B2328881
theorem B1552599 : Blo 1551473 1552599 := bstep (se 1 (by rfl) ⟨1164449, by rfl⟩ : syracuseStep 1552599 = 2328899) B2328899
theorem B3494105 : Blo 1551473 3494105 := bstep (se 2 (by rfl) ⟨1310289, by rfl⟩ : syracuseStep 3494105 = 2620579) B2620579
theorem B1552619 : Blo 1551473 1552619 := bstep (se 1 (by rfl) ⟨1164464, by rfl⟩ : syracuseStep 1552619 = 2328929) B2328929
theorem B1552631 : Blo 1551473 1552631 := bstep (se 1 (by rfl) ⟨1164473, by rfl⟩ : syracuseStep 1552631 = 2328947) B2328947
theorem B24236293 : Blo 1551473 24236293 := bstep (se 4 (by rfl) ⟨2272152, by rfl⟩ : syracuseStep 24236293 = 4544305) B4544305
theorem B1552651 : Blo 1551473 1552651 := bstep (se 1 (by rfl) ⟨1164488, by rfl⟩ : syracuseStep 1552651 = 2328977) B2328977
theorem B6631703 : Blo 1551473 6631703 := bstep (se 1 (by rfl) ⟨4973777, by rfl⟩ : syracuseStep 6631703 = 9947555) B9947555
theorem B1552663 : Blo 1551473 1552663 := bstep (se 1 (by rfl) ⟨1164497, by rfl⟩ : syracuseStep 1552663 = 2328995) B2328995
theorem B1552683 : Blo 1551473 1552683 := bstep (se 1 (by rfl) ⟨1164512, by rfl⟩ : syracuseStep 1552683 = 2329025) B2329025
theorem B3494195 : Blo 1551473 3494195 := bstep (se 1 (by rfl) ⟨2620646, by rfl⟩ : syracuseStep 3494195 = 5241293) B5241293
theorem B1552695 : Blo 1551473 1552695 := bstep (se 1 (by rfl) ⟨1164521, by rfl⟩ : syracuseStep 1552695 = 2329043) B2329043
theorem B1552715 : Blo 1551473 1552715 := bstep (se 1 (by rfl) ⟨1164536, by rfl⟩ : syracuseStep 1552715 = 2329073) B2329073
theorem B1552727 : Blo 1551473 1552727 := bstep (se 1 (by rfl) ⟨1164545, by rfl⟩ : syracuseStep 1552727 = 2329091) B2329091
theorem B3494231 : Blo 1551473 3494231 := bstep (se 1 (by rfl) ⟨2620673, by rfl⟩ : syracuseStep 3494231 = 5241347) B5241347
theorem B3928409 : Blo 1551473 3928409 := bstep (se 2 (by rfl) ⟨1473153, by rfl⟩ : syracuseStep 3928409 = 2946307) B2946307
theorem B5239133 : Blo 1551473 5239133 := bstep (se 3 (by rfl) ⟨982337, by rfl⟩ : syracuseStep 5239133 = 1964675) B1964675
theorem B1552747 : Blo 1551473 1552747 := bstep (se 1 (by rfl) ⟨1164560, by rfl⟩ : syracuseStep 1552747 = 2329121) B2329121
theorem B1552759 : Blo 1551473 1552759 := bstep (se 1 (by rfl) ⟨1164569, by rfl⟩ : syracuseStep 1552759 = 2329139) B2329139
theorem B1552779 : Blo 1551473 1552779 := bstep (se 1 (by rfl) ⟨1164584, by rfl⟩ : syracuseStep 1552779 = 2329169) B2329169
theorem B1552791 : Blo 1551473 1552791 := bstep (se 1 (by rfl) ⟨1164593, by rfl⟩ : syracuseStep 1552791 = 2329187) B2329187
theorem B1552811 : Blo 1551473 1552811 := bstep (se 1 (by rfl) ⟨1164608, by rfl⟩ : syracuseStep 1552811 = 2329217) B2329217
theorem B1552823 : Blo 1551473 1552823 := bstep (se 1 (by rfl) ⟨1164617, by rfl⟩ : syracuseStep 1552823 = 2329235) B2329235
theorem B5894603 : Blo 1551473 5894603 := bstep (se 1 (by rfl) ⟨4420952, by rfl⟩ : syracuseStep 5894603 = 8841905) B8841905
theorem B1552843 : Blo 1551473 1552843 := bstep (se 1 (by rfl) ⟨1164632, by rfl⟩ : syracuseStep 1552843 = 2329265) B2329265
theorem B2798039 : Blo 1551473 2798039 := bstep (se 1 (by rfl) ⟨2098529, by rfl⟩ : syracuseStep 2798039 = 4197059) B4197059
theorem B1552855 : Blo 1551473 1552855 := bstep (se 1 (by rfl) ⟨1164641, by rfl⟩ : syracuseStep 1552855 = 2329283) B2329283
theorem B1552875 : Blo 1551473 1552875 := bstep (se 1 (by rfl) ⟨1164656, by rfl⟩ : syracuseStep 1552875 = 2329313) B2329313
theorem B1552887 : Blo 1551473 1552887 := bstep (se 1 (by rfl) ⟨1164665, by rfl⟩ : syracuseStep 1552887 = 2329331) B2329331
theorem B1552907 : Blo 1551473 1552907 := bstep (se 1 (by rfl) ⟨1164680, by rfl⟩ : syracuseStep 1552907 = 2329361) B2329361
theorem B3494411 : Blo 1551473 3494411 := bstep (se 1 (by rfl) ⟨2620808, by rfl⟩ : syracuseStep 3494411 = 5241617) B5241617
theorem B1552919 : Blo 1551473 1552919 := bstep (se 1 (by rfl) ⟨1164689, by rfl⟩ : syracuseStep 1552919 = 2329379) B2329379
theorem B1552939 : Blo 1551473 1552939 := bstep (se 1 (by rfl) ⟨1164704, by rfl⟩ : syracuseStep 1552939 = 2329409) B2329409
theorem B1552951 : Blo 1551473 1552951 := bstep (se 1 (by rfl) ⟨1164713, by rfl⟩ : syracuseStep 1552951 = 2329427) B2329427
theorem B3494465 : Blo 1551473 3494465 := bstep (se 2 (by rfl) ⟨1310424, by rfl⟩ : syracuseStep 3494465 = 2620849) B2620849
theorem B1552971 : Blo 1551473 1552971 := bstep (se 1 (by rfl) ⟨1164728, by rfl⟩ : syracuseStep 1552971 = 2329457) B2329457
theorem B1552983 : Blo 1551473 1552983 := bstep (se 1 (by rfl) ⟨1164737, by rfl⟩ : syracuseStep 1552983 = 2329475) B2329475
theorem B1553003 : Blo 1551473 1553003 := bstep (se 1 (by rfl) ⟨1164752, by rfl⟩ : syracuseStep 1553003 = 2329505) B2329505
theorem B1553015 : Blo 1551473 1553015 := bstep (se 1 (by rfl) ⟨1164761, by rfl⟩ : syracuseStep 1553015 = 2329523) B2329523
theorem B1553035 : Blo 1551473 1553035 := bstep (se 1 (by rfl) ⟨1164776, by rfl⟩ : syracuseStep 1553035 = 2329553) B2329553
theorem B5894801 : Blo 1551473 5894801 := bstep (se 2 (by rfl) ⟨2210550, by rfl⟩ : syracuseStep 5894801 = 4421101) B4421101
theorem B7860887 : Blo 1551473 7860887 := bstep (se 1 (by rfl) ⟨5895665, by rfl⟩ : syracuseStep 7860887 = 11791331) B11791331
theorem B1553047 : Blo 1551473 1553047 := bstep (se 1 (by rfl) ⟨1164785, by rfl⟩ : syracuseStep 1553047 = 2329571) B2329571
theorem B3191447 : Blo 1551473 3191447 := bstep (se 1 (by rfl) ⟨2393585, by rfl⟩ : syracuseStep 3191447 = 4787171) B4787171
theorem B1553067 : Blo 1551473 1553067 := bstep (se 1 (by rfl) ⟨1164800, by rfl⟩ : syracuseStep 1553067 = 2329601) B2329601
theorem B6296237 : Blo 1551473 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B1553079 : Blo 1551473 1553079 := bstep (se 1 (by rfl) ⟨1164809, by rfl⟩ : syracuseStep 1553079 = 2329619) B2329619
theorem B6296267 : Blo 1551473 6296267 := bstep (se 1 (by rfl) ⟨4722200, by rfl⟩ : syracuseStep 6296267 = 9444401) B9444401
theorem B1553099 : Blo 1551473 1553099 := bstep (se 1 (by rfl) ⟨1164824, by rfl⟩ : syracuseStep 1553099 = 2329649) B2329649
theorem B1553111 : Blo 1551473 1553111 := bstep (se 1 (by rfl) ⟨1164833, by rfl⟩ : syracuseStep 1553111 = 2329667) B2329667
theorem B1553131 : Blo 1551473 1553131 := bstep (se 1 (by rfl) ⟨1164848, by rfl⟩ : syracuseStep 1553131 = 2329697) B2329697
theorem B1553143 : Blo 1551473 1553143 := bstep (se 1 (by rfl) ⟨1164857, by rfl⟩ : syracuseStep 1553143 = 2329715) B2329715
theorem B1553163 : Blo 1551473 1553163 := bstep (se 1 (by rfl) ⟨1164872, by rfl⟩ : syracuseStep 1553163 = 2329745) B2329745
theorem B1553175 : Blo 1551473 1553175 := bstep (se 1 (by rfl) ⟨1164881, by rfl⟩ : syracuseStep 1553175 = 2329763) B2329763
theorem B3494681 : Blo 1551473 3494681 := bstep (se 2 (by rfl) ⟨1310505, by rfl⟩ : syracuseStep 3494681 = 2621011) B2621011
theorem B1553195 : Blo 1551473 1553195 := bstep (se 1 (by rfl) ⟨1164896, by rfl⟩ : syracuseStep 1553195 = 2329793) B2329793
theorem B1553207 : Blo 1551473 1553207 := bstep (se 1 (by rfl) ⟨1164905, by rfl⟩ : syracuseStep 1553207 = 2329811) B2329811
theorem B1553227 : Blo 1551473 1553227 := bstep (se 1 (by rfl) ⟨1164920, by rfl⟩ : syracuseStep 1553227 = 2329841) B2329841
theorem B1553239 : Blo 1551473 1553239 := bstep (se 1 (by rfl) ⟨1164929, by rfl⟩ : syracuseStep 1553239 = 2329859) B2329859
theorem B3732313 : Blo 1551473 3732313 := bstep (se 2 (by rfl) ⟨1399617, by rfl⟩ : syracuseStep 3732313 = 2799235) B2799235
theorem B1553259 : Blo 1551473 1553259 := bstep (se 1 (by rfl) ⟨1164944, by rfl⟩ : syracuseStep 1553259 = 2329889) B2329889
theorem B3494771 : Blo 1551473 3494771 := bstep (se 1 (by rfl) ⟨2621078, by rfl⟩ : syracuseStep 3494771 = 5242157) B5242157
theorem B1553271 : Blo 1551473 1553271 := bstep (se 1 (by rfl) ⟨1164953, by rfl⟩ : syracuseStep 1553271 = 2329907) B2329907
theorem B1553291 : Blo 1551473 1553291 := bstep (se 1 (by rfl) ⟨1164968, by rfl⟩ : syracuseStep 1553291 = 2329937) B2329937
theorem B7181201 : Blo 1551473 7181201 := bstep (se 2 (by rfl) ⟨2692950, by rfl⟩ : syracuseStep 7181201 = 5385901) B5385901
theorem B3494807 : Blo 1551473 3494807 := bstep (se 1 (by rfl) ⟨2621105, by rfl⟩ : syracuseStep 3494807 = 5242211) B5242211
theorem B1553303 : Blo 1551473 1553303 := bstep (se 1 (by rfl) ⟨1164977, by rfl⟩ : syracuseStep 1553303 = 2329955) B2329955
theorem B1553323 : Blo 1551473 1553323 := bstep (se 1 (by rfl) ⟨1164992, by rfl⟩ : syracuseStep 1553323 = 2329985) B2329985
theorem B1553335 : Blo 1551473 1553335 := bstep (se 1 (by rfl) ⟨1165001, by rfl⟩ : syracuseStep 1553335 = 2330003) B2330003
theorem B1553355 : Blo 1551473 1553355 := bstep (se 1 (by rfl) ⟨1165016, by rfl⟩ : syracuseStep 1553355 = 2330033) B2330033
theorem B1553367 : Blo 1551473 1553367 := bstep (se 1 (by rfl) ⟨1165025, by rfl⟩ : syracuseStep 1553367 = 2330051) B2330051
theorem B12587993 : Blo 1551473 12587993 := bstep (se 2 (by rfl) ⟨4720497, by rfl⟩ : syracuseStep 12587993 = 9440995) B9440995
theorem B1553387 : Blo 1551473 1553387 := bstep (se 1 (by rfl) ⟨1165040, by rfl⟩ : syracuseStep 1553387 = 2330081) B2330081
theorem B1553399 : Blo 1551473 1553399 := bstep (se 1 (by rfl) ⟨1165049, by rfl⟩ : syracuseStep 1553399 = 2330099) B2330099
theorem B1553419 : Blo 1551473 1553419 := bstep (se 1 (by rfl) ⟨1165064, by rfl⟩ : syracuseStep 1553419 = 2330129) B2330129
theorem B2946071 : Blo 1551473 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B1553431 : Blo 1551473 1553431 := bstep (se 1 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 1553431 = 2330147) B2330147
theorem B50328611 : Blo 1551473 50328611 := bstep (se 1 (by rfl) ⟨37746458, by rfl⟩ : syracuseStep 50328611 = 75492917) B75492917
theorem B1553451 : Blo 1551473 1553451 := bstep (se 1 (by rfl) ⟨1165088, by rfl⟩ : syracuseStep 1553451 = 2330177) B2330177
theorem B1553463 : Blo 1551473 1553463 := bstep (se 1 (by rfl) ⟨1165097, by rfl⟩ : syracuseStep 1553463 = 2330195) B2330195
theorem B3494987 : Blo 1551473 3494987 := bstep (se 1 (by rfl) ⟨2621240, by rfl⟩ : syracuseStep 3494987 = 5242481) B5242481
theorem B4723805 : Blo 1551473 4723805 := bstep (se 3 (by rfl) ⟨885713, by rfl⟩ : syracuseStep 4723805 = 1771427) B1771427
theorem B8844389 : Blo 1551473 8844389 := bstep (se 4 (by rfl) ⟨829161, by rfl⟩ : syracuseStep 8844389 = 1658323) B1658323
theorem B3495041 : Blo 1551473 3495041 := bstep (se 2 (by rfl) ⟨1310640, by rfl⟩ : syracuseStep 3495041 = 2621281) B2621281
theorem B6296707 : Blo 1551473 6296707 := bstep (se 1 (by rfl) ⟨4722530, by rfl⟩ : syracuseStep 6296707 = 9445061) B9445061
theorem B2618507 : Blo 1551473 2618507 := bstep (se 1 (by rfl) ⟨1963880, by rfl⟩ : syracuseStep 2618507 = 3927761) B3927761
theorem B2618635 : Blo 1551473 2618635 := bstep (se 1 (by rfl) ⟨1963976, by rfl⟩ : syracuseStep 2618635 = 3927953) B3927953
theorem B3495257 : Blo 1551473 3495257 := bstep (se 2 (by rfl) ⟨1310721, by rfl⟩ : syracuseStep 3495257 = 2621443) B2621443
theorem B5895575 : Blo 1551473 5895575 := bstep (se 1 (by rfl) ⟨4421681, by rfl⟩ : syracuseStep 5895575 = 8843363) B8843363
theorem B2618777 : Blo 1551473 2618777 := bstep (se 2 (by rfl) ⟨982041, by rfl⟩ : syracuseStep 2618777 = 1964083) B1964083
theorem B5240267 : Blo 1551473 5240267 := bstep (se 1 (by rfl) ⟨3930200, by rfl⟩ : syracuseStep 5240267 = 7860401) B7860401
theorem B2209303 : Blo 1551473 2209303 := bstep (se 1 (by rfl) ⟨1656977, by rfl⟩ : syracuseStep 2209303 = 3313955) B3313955
theorem B2618905 : Blo 1551473 2618905 := bstep (se 2 (by rfl) ⟨982089, by rfl⟩ : syracuseStep 2618905 = 1964179) B1964179
theorem B2946611 : Blo 1551473 2946611 := bstep (se 1 (by rfl) ⟨2209958, by rfl⟩ : syracuseStep 2946611 = 4419917) B4419917
theorem B6633035 : Blo 1551473 6633035 := bstep (se 1 (by rfl) ⟨4974776, by rfl⟩ : syracuseStep 6633035 = 9949553) B9949553
theorem B3315287 : Blo 1551473 3315287 := bstep (se 1 (by rfl) ⟨2486465, by rfl⟩ : syracuseStep 3315287 = 4972931) B4972931
theorem B5895773 : Blo 1551473 5895773 := bstep (se 3 (by rfl) ⟨1105457, by rfl⟩ : syracuseStep 5895773 = 2210915) B2210915
theorem B5240537 : Blo 1551473 5240537 := bstep (se 2 (by rfl) ⟨1965201, by rfl⟩ : syracuseStep 5240537 = 3930403) B3930403
theorem B13268771 : Blo 1551473 13268771 := bstep (se 1 (by rfl) ⟨9951578, by rfl⟩ : syracuseStep 13268771 = 19903157) B19903157
theorem B3315595 : Blo 1551473 3315595 := bstep (se 1 (by rfl) ⟨2486696, by rfl⟩ : syracuseStep 3315595 = 4973393) B4973393
theorem B2987929 : Blo 1551473 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B11188145 : Blo 1551473 11188145 := bstep (se 2 (by rfl) ⟨4195554, by rfl⟩ : syracuseStep 11188145 = 8391109) B8391109
theorem B40335283 : Blo 1551473 40335283 := bstep (se 1 (by rfl) ⟨30251462, by rfl⟩ : syracuseStep 40335283 = 60502925) B60502925
theorem B3930059 : Blo 1551473 3930059 := bstep (se 1 (by rfl) ⟨2947544, by rfl⟩ : syracuseStep 3930059 = 5895089) B5895089
theorem B2947097 : Blo 1551473 2947097 := bstep (se 2 (by rfl) ⟨1105161, by rfl⟩ : syracuseStep 2947097 = 2210323) B2210323
theorem B2619479 : Blo 1551473 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B2619607 : Blo 1551473 2619607 := bstep (se 1 (by rfl) ⟨1964705, by rfl⟩ : syracuseStep 2619607 = 3929411) B3929411
theorem B2210009 : Blo 1551473 2210009 := bstep (se 2 (by rfl) ⟨828753, by rfl⟩ : syracuseStep 2210009 = 1657507) B1657507
theorem B11794733 : Blo 1551473 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B2210123 : Blo 1551473 2210123 := bstep (se 1 (by rfl) ⟨1657592, by rfl⟩ : syracuseStep 2210123 = 3315185) B3315185
theorem B5527939 : Blo 1551473 5527939 := bstep (se 1 (by rfl) ⟨4145954, by rfl⟩ : syracuseStep 5527939 = 8291909) B8291909
theorem B5241239 : Blo 1551473 5241239 := bstep (se 1 (by rfl) ⟨3930929, by rfl⟩ : syracuseStep 5241239 = 7861859) B7861859
theorem B7174579 : Blo 1551473 7174579 := bstep (se 1 (by rfl) ⟨5380934, by rfl⟩ : syracuseStep 7174579 = 10761869) B10761869
theorem B1964503 : Blo 1551473 1964503 := bstep (se 1 (by rfl) ⟨1473377, by rfl⟩ : syracuseStep 1964503 = 2946755) B2946755
theorem B9443915 : Blo 1551473 9443915 := bstep (se 1 (by rfl) ⟨7082936, by rfl⟩ : syracuseStep 9443915 = 14165873) B14165873
theorem B12581477 : Blo 1551473 12581477 := bstep (se 4 (by rfl) ⟨1179513, by rfl⟩ : syracuseStep 12581477 = 2359027) B2359027
theorem B6634163 : Blo 1551473 6634163 := bstep (se 1 (by rfl) ⟨4975622, by rfl⟩ : syracuseStep 6634163 = 9951245) B9951245
theorem B11786957 : Blo 1551473 11786957 := bstep (se 3 (by rfl) ⟨2210054, by rfl⟩ : syracuseStep 11786957 = 4420109) B4420109
theorem B8837849 : Blo 1551473 8837849 := bstep (se 2 (by rfl) ⟨3314193, by rfl⟩ : syracuseStep 8837849 = 6628387) B6628387
theorem B7854893 : Blo 1551473 7854893 := bstep (se 3 (by rfl) ⟨1472792, by rfl⟩ : syracuseStep 7854893 = 2945585) B2945585
theorem B2620235 : Blo 1551473 2620235 := bstep (se 1 (by rfl) ⟨1965176, by rfl⟩ : syracuseStep 2620235 = 3930353) B3930353
theorem B2210647 : Blo 1551473 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B3931031 : Blo 1551473 3931031 := bstep (se 1 (by rfl) ⟨2948273, by rfl⟩ : syracuseStep 3931031 = 5896547) B5896547
theorem B5241779 : Blo 1551473 5241779 := bstep (se 1 (by rfl) ⟨3931334, by rfl⟩ : syracuseStep 5241779 = 7862669) B7862669
theorem B4422593 : Blo 1551473 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2620363 : Blo 1551473 2620363 := bstep (se 1 (by rfl) ⟨1965272, by rfl⟩ : syracuseStep 2620363 = 3930545) B3930545
theorem B9952217 : Blo 1551473 9952217 := bstep (se 2 (by rfl) ⟨3732081, by rfl⟩ : syracuseStep 9952217 = 7464163) B7464163
theorem B17685539 : Blo 1551473 17685539 := bstep (se 1 (by rfl) ⟨13264154, by rfl⟩ : syracuseStep 17685539 = 26528309) B26528309
theorem B7175213 : Blo 1551473 7175213 := bstep (se 3 (by rfl) ⟨1345352, by rfl⟩ : syracuseStep 7175213 = 2690705) B2690705
theorem B4422707 : Blo 1551473 4422707 := bstep (se 1 (by rfl) ⟨3317030, by rfl⟩ : syracuseStep 4422707 = 6634061) B6634061
theorem B2620505 : Blo 1551473 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B3316825 : Blo 1551473 3316825 := bstep (se 2 (by rfl) ⟨1243809, by rfl⟩ : syracuseStep 3316825 = 2487619) B2487619
theorem B11787443 : Blo 1551473 11787443 := bstep (se 1 (by rfl) ⟨8840582, by rfl⟩ : syracuseStep 11787443 = 17681165) B17681165
theorem B5594305 : Blo 1551473 5594305 := bstep (se 2 (by rfl) ⟨2097864, by rfl⟩ : syracuseStep 5594305 = 4195729) B4195729
theorem B5242049 : Blo 1551473 5242049 := bstep (se 2 (by rfl) ⟨1965768, by rfl⟩ : syracuseStep 5242049 = 3931537) B3931537
theorem B2620633 : Blo 1551473 2620633 := bstep (se 2 (by rfl) ⟨982737, by rfl⟩ : syracuseStep 2620633 = 1965475) B1965475
theorem B1965323 : Blo 1551473 1965323 := bstep (se 1 (by rfl) ⟨1473992, by rfl⟩ : syracuseStep 1965323 = 2947985) B2947985
theorem B2948555 : Blo 1551473 2948555 := bstep (se 1 (by rfl) ⟨2211416, by rfl⟩ : syracuseStep 2948555 = 4422833) B4422833
theorem B5897731 : Blo 1551473 5897731 := bstep (se 1 (by rfl) ⟨4423298, by rfl⟩ : syracuseStep 5897731 = 8846597) B8846597
theorem B3931699 : Blo 1551473 3931699 := bstep (se 1 (by rfl) ⟨2948774, by rfl⟩ : syracuseStep 3931699 = 5897549) B5897549
theorem B11337317 : Blo 1551473 11337317 := bstep (se 4 (by rfl) ⟨1062873, by rfl⟩ : syracuseStep 11337317 = 2125747) B2125747
theorem B2948737 : Blo 1551473 2948737 := bstep (se 2 (by rfl) ⟨1105776, by rfl⟩ : syracuseStep 2948737 = 2211553) B2211553
theorem B2211467 : Blo 1551473 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B3636887 : Blo 1551473 3636887 := bstep (se 1 (by rfl) ⟨2727665, by rfl⟩ : syracuseStep 3636887 = 5455331) B5455331
theorem B5668525 : Blo 1551473 5668525 := bstep (se 3 (by rfl) ⟨1062848, by rfl⟩ : syracuseStep 5668525 = 2125697) B2125697
theorem B3931841 : Blo 1551473 3931841 := bstep (se 2 (by rfl) ⟨1474440, by rfl⟩ : syracuseStep 3931841 = 2948881) B2948881
theorem B5242589 : Blo 1551473 5242589 := bstep (se 3 (by rfl) ⟨982985, by rfl⟩ : syracuseStep 5242589 = 1965971) B1965971
theorem B2621207 : Blo 1551473 2621207 := bstep (se 1 (by rfl) ⟨1965905, by rfl⟩ : syracuseStep 2621207 = 3931811) B3931811
theorem B5898035 : Blo 1551473 5898035 := bstep (se 1 (by rfl) ⟨4423526, by rfl⟩ : syracuseStep 5898035 = 8847053) B8847053
theorem B2097047 : Blo 1551473 2097047 := bstep (se 1 (by rfl) ⟨1572785, by rfl⟩ : syracuseStep 2097047 = 3145571) B3145571
theorem B2621335 : Blo 1551473 2621335 := bstep (se 1 (by rfl) ⟨1966001, by rfl⟩ : syracuseStep 2621335 = 3932003) B3932003
theorem B1966027 : Blo 1551473 1966027 := bstep (se 1 (by rfl) ⟨1474520, by rfl⟩ : syracuseStep 1966027 = 2949041) B2949041
theorem B4423709 : Blo 1551473 4423709 := bstep (se 3 (by rfl) ⟨829445, by rfl⟩ : syracuseStep 4423709 = 1658891) B1658891
theorem B7856189 : Blo 1551473 7856189 := bstep (se 3 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 7856189 = 2946071) B2946071
theorem B5242967 : Blo 1551473 5242967 := bstep (se 1 (by rfl) ⟨3932225, by rfl⟩ : syracuseStep 5242967 = 7864451) B7864451
theorem B2834731 : Blo 1551473 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B14926139 : Blo 1551473 14926139 := bstep (se 1 (by rfl) ⟨11194604, by rfl⟩ : syracuseStep 14926139 = 22389209) B22389209
theorem B2359739 : Blo 1551473 2359739 := bstep (se 1 (by rfl) ⟨1769804, by rfl⟩ : syracuseStep 2359739 = 3539609) B3539609
theorem B3727873 : Blo 1551473 3727873 := bstep (se 2 (by rfl) ⟨1397952, by rfl⟩ : syracuseStep 3727873 = 2795905) B2795905
theorem B8962589 : Blo 1551473 8962589 := bstep (se 3 (by rfl) ⟨1680485, by rfl⟩ : syracuseStep 8962589 = 3360971) B3360971
theorem B2327225 : Blo 1551473 2327225 := bstep (se 2 (by rfl) ⟨872709, by rfl⟩ : syracuseStep 2327225 = 1745419) B1745419
theorem B2327303 : Blo 1551473 2327303 := bstep (se 1 (by rfl) ⟨1745477, by rfl⟩ : syracuseStep 2327303 = 3490955) B3490955
theorem B1745671 : Blo 1551473 1745671 := bstep (se 1 (by rfl) ⟨1309253, by rfl⟩ : syracuseStep 1745671 = 2618507) B2618507
theorem B2327339 : Blo 1551473 2327339 := bstep (se 1 (by rfl) ⟨1745504, by rfl⟩ : syracuseStep 2327339 = 3491009) B3491009
theorem B2327369 : Blo 1551473 2327369 := bstep (se 2 (by rfl) ⟨872763, by rfl⟩ : syracuseStep 2327369 = 1745527) B1745527
theorem B10077043 : Blo 1551473 10077043 := bstep (se 1 (by rfl) ⟨7557782, by rfl⟩ : syracuseStep 10077043 = 15115565) B15115565
theorem B4195219 : Blo 1551473 4195219 := bstep (se 1 (by rfl) ⟨3146414, by rfl⟩ : syracuseStep 4195219 = 6292829) B6292829
theorem B2327483 : Blo 1551473 2327483 := bstep (se 1 (by rfl) ⟨1745612, by rfl⟩ : syracuseStep 2327483 = 3491225) B3491225
theorem B1745851 : Blo 1551473 1745851 := bstep (se 1 (by rfl) ⟨1309388, by rfl⟩ : syracuseStep 1745851 = 2618777) B2618777
theorem B2327543 : Blo 1551473 2327543 := bstep (se 1 (by rfl) ⟨1745657, by rfl⟩ : syracuseStep 2327543 = 3491315) B3491315
theorem B2327567 : Blo 1551473 2327567 := bstep (se 1 (by rfl) ⟨1745675, by rfl⟩ : syracuseStep 2327567 = 3491351) B3491351
theorem B2327609 : Blo 1551473 2327609 := bstep (se 2 (by rfl) ⟨872853, by rfl⟩ : syracuseStep 2327609 = 1745707) B1745707
theorem B4195415 : Blo 1551473 4195415 := bstep (se 1 (by rfl) ⟨3146561, by rfl⟩ : syracuseStep 4195415 = 6293123) B6293123
theorem B2327687 : Blo 1551473 2327687 := bstep (se 1 (by rfl) ⟨1745765, by rfl⟩ : syracuseStep 2327687 = 3491531) B3491531
theorem B2327723 : Blo 1551473 2327723 := bstep (se 1 (by rfl) ⟨1745792, by rfl⟩ : syracuseStep 2327723 = 3491585) B3491585
theorem B3728585 : Blo 1551473 3728585 := bstep (se 2 (by rfl) ⟨1398219, by rfl⟩ : syracuseStep 3728585 = 2796439) B2796439
theorem B2327753 : Blo 1551473 2327753 := bstep (se 2 (by rfl) ⟨872907, by rfl⟩ : syracuseStep 2327753 = 1745815) B1745815
theorem B2327867 : Blo 1551473 2327867 := bstep (se 1 (by rfl) ⟨1745900, by rfl⟩ : syracuseStep 2327867 = 3491801) B3491801
theorem B2327927 : Blo 1551473 2327927 := bstep (se 1 (by rfl) ⟨1745945, by rfl⟩ : syracuseStep 2327927 = 3491891) B3491891
theorem B3491207 : Blo 1551473 3491207 := bstep (se 1 (by rfl) ⟨2618405, by rfl⟩ : syracuseStep 3491207 = 5236811) B5236811
theorem B2360711 : Blo 1551473 2360711 := bstep (se 1 (by rfl) ⟨1770533, by rfl⟩ : syracuseStep 2360711 = 3541067) B3541067
theorem B2327951 : Blo 1551473 2327951 := bstep (se 1 (by rfl) ⟨1745963, by rfl⟩ : syracuseStep 2327951 = 3491927) B3491927
theorem B1746319 : Blo 1551473 1746319 := bstep (se 1 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 1746319 = 2619479) B2619479
theorem B5309849 : Blo 1551473 5309849 := bstep (se 2 (by rfl) ⟨1991193, by rfl⟩ : syracuseStep 5309849 = 3982387) B3982387
theorem B2327993 : Blo 1551473 2327993 := bstep (se 2 (by rfl) ⟨872997, by rfl⟩ : syracuseStep 2327993 = 1745995) B1745995
theorem B2328071 : Blo 1551473 2328071 := bstep (se 1 (by rfl) ⟨1746053, by rfl⟩ : syracuseStep 2328071 = 3492107) B3492107
theorem B2328107 : Blo 1551473 2328107 := bstep (se 1 (by rfl) ⟨1746080, by rfl⟩ : syracuseStep 2328107 = 3492161) B3492161
theorem B3491387 : Blo 1551473 3491387 := bstep (se 1 (by rfl) ⟨2618540, by rfl⟩ : syracuseStep 3491387 = 5237081) B5237081
theorem B8840765 : Blo 1551473 8840765 := bstep (se 3 (by rfl) ⟨1657643, by rfl⟩ : syracuseStep 8840765 = 3315287) B3315287
theorem B2328137 : Blo 1551473 2328137 := bstep (se 2 (by rfl) ⟨873051, by rfl⟩ : syracuseStep 2328137 = 1746103) B1746103
theorem B4916855 : Blo 1551473 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B3491513 : Blo 1551473 3491513 := bstep (se 2 (by rfl) ⟨1309317, by rfl⟩ : syracuseStep 3491513 = 2618635) B2618635
theorem B2328251 : Blo 1551473 2328251 := bstep (se 1 (by rfl) ⟨1746188, by rfl⟩ : syracuseStep 2328251 = 3492377) B3492377
theorem B2328311 : Blo 1551473 2328311 := bstep (se 1 (by rfl) ⟨1746233, by rfl⟩ : syracuseStep 2328311 = 3492467) B3492467
theorem B2328335 : Blo 1551473 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B4720427 : Blo 1551473 4720427 := bstep (se 1 (by rfl) ⟨3540320, by rfl⟩ : syracuseStep 4720427 = 7080641) B7080641
theorem B7857971 : Blo 1551473 7857971 := bstep (se 1 (by rfl) ⟨5893478, by rfl⟩ : syracuseStep 7857971 = 11786957) B11786957
theorem B2328377 : Blo 1551473 2328377 := bstep (se 2 (by rfl) ⟨873141, by rfl⟩ : syracuseStep 2328377 = 1746283) B1746283
theorem B5891899 : Blo 1551473 5891899 := bstep (se 1 (by rfl) ⟨4418924, by rfl⟩ : syracuseStep 5891899 = 8837849) B8837849
theorem B5236595 : Blo 1551473 5236595 := bstep (se 1 (by rfl) ⟨3927446, by rfl⟩ : syracuseStep 5236595 = 7854893) B7854893
theorem B2328455 : Blo 1551473 2328455 := bstep (se 1 (by rfl) ⟨1746341, by rfl⟩ : syracuseStep 2328455 = 3492683) B3492683
theorem B1746823 : Blo 1551473 1746823 := bstep (se 1 (by rfl) ⟨1310117, by rfl⟩ : syracuseStep 1746823 = 2620235) B2620235
theorem B2328491 : Blo 1551473 2328491 := bstep (se 1 (by rfl) ⟨1746368, by rfl⟩ : syracuseStep 2328491 = 3492737) B3492737
theorem B2328521 : Blo 1551473 2328521 := bstep (se 2 (by rfl) ⟨873195, by rfl⟩ : syracuseStep 2328521 = 1746391) B1746391
theorem B3491855 : Blo 1551473 3491855 := bstep (se 1 (by rfl) ⟨2618891, by rfl⟩ : syracuseStep 3491855 = 5237783) B5237783
theorem B11790359 : Blo 1551473 11790359 := bstep (se 1 (by rfl) ⟨8842769, by rfl⟩ : syracuseStep 11790359 = 17685539) B17685539
theorem B3491873 : Blo 1551473 3491873 := bstep (se 2 (by rfl) ⟨1309452, by rfl⟩ : syracuseStep 3491873 = 2618905) B2618905
theorem B8390699 : Blo 1551473 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B2328635 : Blo 1551473 2328635 := bstep (se 1 (by rfl) ⟨1746476, by rfl⟩ : syracuseStep 2328635 = 3492953) B3492953
theorem B7874621 : Blo 1551473 7874621 := bstep (se 3 (by rfl) ⟨1476491, by rfl⟩ : syracuseStep 7874621 = 2952983) B2952983
theorem B1747003 : Blo 1551473 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B7858295 : Blo 1551473 7858295 := bstep (se 1 (by rfl) ⟨5893721, by rfl⟩ : syracuseStep 7858295 = 11787443) B11787443
theorem B2328695 : Blo 1551473 2328695 := bstep (se 1 (by rfl) ⟨1746521, by rfl⟩ : syracuseStep 2328695 = 3493043) B3493043
theorem B2328719 : Blo 1551473 2328719 := bstep (se 1 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 2328719 = 3493079) B3493079
theorem B2328761 : Blo 1551473 2328761 := bstep (se 2 (by rfl) ⟨873285, by rfl⟩ : syracuseStep 2328761 = 1746571) B1746571
theorem B8841473 : Blo 1551473 8841473 := bstep (se 2 (by rfl) ⟨3315552, by rfl⟩ : syracuseStep 8841473 = 6631105) B6631105
theorem B2328839 : Blo 1551473 2328839 := bstep (se 1 (by rfl) ⟨1746629, by rfl⟩ : syracuseStep 2328839 = 3493259) B3493259
theorem B5892385 : Blo 1551473 5892385 := bstep (se 2 (by rfl) ⟨2209644, by rfl⟩ : syracuseStep 5892385 = 4419289) B4419289
theorem B2328875 : Blo 1551473 2328875 := bstep (se 1 (by rfl) ⟨1746656, by rfl⟩ : syracuseStep 2328875 = 3493313) B3493313
theorem B2328905 : Blo 1551473 2328905 := bstep (se 2 (by rfl) ⟨873339, by rfl⟩ : syracuseStep 2328905 = 1746679) B1746679
theorem B3492215 : Blo 1551473 3492215 := bstep (se 1 (by rfl) ⟨2619161, by rfl⟩ : syracuseStep 3492215 = 5238323) B5238323
theorem B4975033 : Blo 1551473 4975033 := bstep (se 2 (by rfl) ⟨1865637, by rfl⟩ : syracuseStep 4975033 = 3731275) B3731275
theorem B2329019 : Blo 1551473 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B2329079 : Blo 1551473 2329079 := bstep (se 1 (by rfl) ⟨1746809, by rfl⟩ : syracuseStep 2329079 = 3493619) B3493619
theorem B2329103 : Blo 1551473 2329103 := bstep (se 1 (by rfl) ⟨1746827, by rfl⟩ : syracuseStep 2329103 = 3493655) B3493655
theorem B1747471 : Blo 1551473 1747471 := bstep (se 1 (by rfl) ⟨1310603, by rfl⟩ : syracuseStep 1747471 = 2621207) B2621207
theorem B3983905 : Blo 1551473 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B3492395 : Blo 1551473 3492395 := bstep (se 1 (by rfl) ⟨2619296, by rfl⟩ : syracuseStep 3492395 = 5238593) B5238593
theorem B2329145 : Blo 1551473 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B2329223 : Blo 1551473 2329223 := bstep (se 1 (by rfl) ⟨1746917, by rfl⟩ : syracuseStep 2329223 = 3493835) B3493835
theorem B2329259 : Blo 1551473 2329259 := bstep (se 1 (by rfl) ⟨1746944, by rfl⟩ : syracuseStep 2329259 = 3493889) B3493889
theorem B10914497 : Blo 1551473 10914497 := bstep (se 2 (by rfl) ⟨4092936, by rfl⟩ : syracuseStep 10914497 = 8185873) B8185873
theorem B2329289 : Blo 1551473 2329289 := bstep (se 2 (by rfl) ⟨873483, by rfl⟩ : syracuseStep 2329289 = 1746967) B1746967
theorem B4418333 : Blo 1551473 4418333 := bstep (se 3 (by rfl) ⟨828437, by rfl⟩ : syracuseStep 4418333 = 1656875) B1656875
theorem B2329403 : Blo 1551473 2329403 := bstep (se 1 (by rfl) ⟨1747052, by rfl⟩ : syracuseStep 2329403 = 3494105) B3494105
theorem B2329463 : Blo 1551473 2329463 := bstep (se 1 (by rfl) ⟨1747097, by rfl⟩ : syracuseStep 2329463 = 3494195) B3494195
theorem B2329487 : Blo 1551473 2329487 := bstep (se 1 (by rfl) ⟨1747115, by rfl⟩ : syracuseStep 2329487 = 3494231) B3494231
theorem B3492755 : Blo 1551473 3492755 := bstep (se 1 (by rfl) ⟨2619566, by rfl⟩ : syracuseStep 3492755 = 5239133) B5239133
theorem B2329529 : Blo 1551473 2329529 := bstep (se 2 (by rfl) ⟨873573, by rfl⟩ : syracuseStep 2329529 = 1747147) B1747147
theorem B3492809 : Blo 1551473 3492809 := bstep (se 2 (by rfl) ⟨1309803, by rfl⟩ : syracuseStep 3492809 = 2619607) B2619607
theorem B2329607 : Blo 1551473 2329607 := bstep (se 1 (by rfl) ⟨1747205, by rfl⟩ : syracuseStep 2329607 = 3494411) B3494411
theorem B2329643 : Blo 1551473 2329643 := bstep (se 1 (by rfl) ⟨1747232, by rfl⟩ : syracuseStep 2329643 = 3494465) B3494465
theorem B14928941 : Blo 1551473 14928941 := bstep (se 3 (by rfl) ⟨2799176, by rfl⟩ : syracuseStep 14928941 = 5598353) B5598353
theorem B7859267 : Blo 1551473 7859267 := bstep (se 1 (by rfl) ⟨5894450, by rfl⟩ : syracuseStep 7859267 = 11788901) B11788901
theorem B2329673 : Blo 1551473 2329673 := bstep (se 2 (by rfl) ⟨873627, by rfl⟩ : syracuseStep 2329673 = 1747255) B1747255
theorem B4418675 : Blo 1551473 4418675 := bstep (se 1 (by rfl) ⟨3314006, by rfl⟩ : syracuseStep 4418675 = 6628013) B6628013
theorem B4197491 : Blo 1551473 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B1551495 : Blo 1551473 1551495 := bstep (se 1 (by rfl) ⟨1163621, by rfl⟩ : syracuseStep 1551495 = 2327243) B2327243
theorem B4197511 : Blo 1551473 4197511 := bstep (se 1 (by rfl) ⟨3148133, by rfl⟩ : syracuseStep 4197511 = 6296267) B6296267
theorem B1551503 : Blo 1551473 1551503 := bstep (se 1 (by rfl) ⟨1163627, by rfl⟩ : syracuseStep 1551503 = 2327255) B2327255
theorem B1551547 : Blo 1551473 1551547 := bstep (se 1 (by rfl) ⟨1163660, by rfl⟩ : syracuseStep 1551547 = 2327321) B2327321
theorem B2329787 : Blo 1551473 2329787 := bstep (se 1 (by rfl) ⟨1747340, by rfl⟩ : syracuseStep 2329787 = 3494681) B3494681
theorem B5893357 : Blo 1551473 5893357 := bstep (se 3 (by rfl) ⟨1105004, by rfl⟩ : syracuseStep 5893357 = 2210009) B2210009
theorem B23317741 : Blo 1551473 23317741 := bstep (se 3 (by rfl) ⟨4372076, by rfl⟩ : syracuseStep 23317741 = 8744153) B8744153
theorem B2329847 : Blo 1551473 2329847 := bstep (se 1 (by rfl) ⟨1747385, by rfl⟩ : syracuseStep 2329847 = 3494771) B3494771
theorem B1551623 : Blo 1551473 1551623 := bstep (se 1 (by rfl) ⟨1163717, by rfl⟩ : syracuseStep 1551623 = 2327435) B2327435
theorem B4787467 : Blo 1551473 4787467 := bstep (se 1 (by rfl) ⟨3590600, by rfl⟩ : syracuseStep 4787467 = 7181201) B7181201
theorem B1551631 : Blo 1551473 1551631 := bstep (se 1 (by rfl) ⟨1163723, by rfl⟩ : syracuseStep 1551631 = 2327447) B2327447
theorem B2329871 : Blo 1551473 2329871 := bstep (se 1 (by rfl) ⟨1747403, by rfl⟩ : syracuseStep 2329871 = 3494807) B3494807
theorem B2329913 : Blo 1551473 2329913 := bstep (se 2 (by rfl) ⟨873717, by rfl⟩ : syracuseStep 2329913 = 1747435) B1747435
theorem B1551675 : Blo 1551473 1551675 := bstep (se 1 (by rfl) ⟨1163756, by rfl⟩ : syracuseStep 1551675 = 2327513) B2327513
theorem B8391995 : Blo 1551473 8391995 := bstep (se 1 (by rfl) ⟨6293996, by rfl⟩ : syracuseStep 8391995 = 12587993) B12587993
theorem B4975931 : Blo 1551473 4975931 := bstep (se 1 (by rfl) ⟨3731948, by rfl⟩ : syracuseStep 4975931 = 7463897) B7463897
theorem B1551751 : Blo 1551473 1551751 := bstep (se 1 (by rfl) ⟨1163813, by rfl⟩ : syracuseStep 1551751 = 2327627) B2327627
theorem B7859591 : Blo 1551473 7859591 := bstep (se 1 (by rfl) ⟨5894693, by rfl⟩ : syracuseStep 7859591 = 11789387) B11789387
theorem B2329991 : Blo 1551473 2329991 := bstep (se 1 (by rfl) ⟨1747493, by rfl⟩ : syracuseStep 2329991 = 3494987) B3494987
theorem B1551759 : Blo 1551473 1551759 := bstep (se 1 (by rfl) ⟨1163819, by rfl⟩ : syracuseStep 1551759 = 2327639) B2327639
theorem B2330027 : Blo 1551473 2330027 := bstep (se 1 (by rfl) ⟨1747520, by rfl⟩ : syracuseStep 2330027 = 3495041) B3495041
theorem B1551803 : Blo 1551473 1551803 := bstep (se 1 (by rfl) ⟨1163852, by rfl⟩ : syracuseStep 1551803 = 2327705) B2327705
theorem B2330057 : Blo 1551473 2330057 := bstep (se 2 (by rfl) ⟨873771, by rfl⟩ : syracuseStep 2330057 = 1747543) B1747543
theorem B19885571 : Blo 1551473 19885571 := bstep (se 1 (by rfl) ⟨14914178, by rfl⟩ : syracuseStep 19885571 = 29828357) B29828357
theorem B1551879 : Blo 1551473 1551879 := bstep (se 1 (by rfl) ⟨1163909, by rfl⟩ : syracuseStep 1551879 = 2327819) B2327819
theorem B1551887 : Blo 1551473 1551887 := bstep (se 1 (by rfl) ⟨1163915, by rfl⟩ : syracuseStep 1551887 = 2327831) B2327831
theorem B5893661 : Blo 1551473 5893661 := bstep (se 3 (by rfl) ⟨1105061, by rfl⟩ : syracuseStep 5893661 = 2210123) B2210123
theorem B1551931 : Blo 1551473 1551931 := bstep (se 1 (by rfl) ⟨1163948, by rfl⟩ : syracuseStep 1551931 = 2327897) B2327897
theorem B2330171 : Blo 1551473 2330171 := bstep (se 1 (by rfl) ⟨1747628, by rfl⟩ : syracuseStep 2330171 = 3495257) B3495257
theorem B1552007 : Blo 1551473 1552007 := bstep (se 1 (by rfl) ⟨1164005, by rfl⟩ : syracuseStep 1552007 = 2328011) B2328011
theorem B3493511 : Blo 1551473 3493511 := bstep (se 1 (by rfl) ⟨2620133, by rfl⟩ : syracuseStep 3493511 = 5240267) B5240267
theorem B1552015 : Blo 1551473 1552015 := bstep (se 1 (by rfl) ⟨1164011, by rfl⟩ : syracuseStep 1552015 = 2328023) B2328023
theorem B4198073 : Blo 1551473 4198073 := bstep (se 2 (by rfl) ⟨1574277, by rfl⟩ : syracuseStep 4198073 = 3148555) B3148555
theorem B1552059 : Blo 1551473 1552059 := bstep (se 1 (by rfl) ⟨1164044, by rfl⟩ : syracuseStep 1552059 = 2328089) B2328089
theorem B1552135 : Blo 1551473 1552135 := bstep (se 1 (by rfl) ⟨1164101, by rfl⟩ : syracuseStep 1552135 = 2328203) B2328203
theorem B1552143 : Blo 1551473 1552143 := bstep (se 1 (by rfl) ⟨1164107, by rfl⟩ : syracuseStep 1552143 = 2328215) B2328215
theorem B4976417 : Blo 1551473 4976417 := bstep (se 2 (by rfl) ⟨1866156, by rfl⟩ : syracuseStep 4976417 = 3732313) B3732313
theorem B1552187 : Blo 1551473 1552187 := bstep (se 1 (by rfl) ⟨1164140, by rfl⟩ : syracuseStep 1552187 = 2328281) B2328281
theorem B3493691 : Blo 1551473 3493691 := bstep (se 1 (by rfl) ⟨2620268, by rfl⟩ : syracuseStep 3493691 = 5240537) B5240537
theorem B3927923 : Blo 1551473 3927923 := bstep (se 1 (by rfl) ⟨2945942, by rfl⟩ : syracuseStep 3927923 = 5891885) B5891885
theorem B1552263 : Blo 1551473 1552263 := bstep (se 1 (by rfl) ⟨1164197, by rfl⟩ : syracuseStep 1552263 = 2328395) B2328395
theorem B1552271 : Blo 1551473 1552271 := bstep (se 1 (by rfl) ⟨1164203, by rfl⟩ : syracuseStep 1552271 = 2328407) B2328407
theorem B3493817 : Blo 1551473 3493817 := bstep (se 2 (by rfl) ⟨1310181, by rfl⟩ : syracuseStep 3493817 = 2620363) B2620363
theorem B1552315 : Blo 1551473 1552315 := bstep (se 1 (by rfl) ⟨1164236, by rfl⟩ : syracuseStep 1552315 = 2328473) B2328473
theorem B1552391 : Blo 1551473 1552391 := bstep (se 1 (by rfl) ⟨1164293, by rfl⟩ : syracuseStep 1552391 = 2328587) B2328587
theorem B1552399 : Blo 1551473 1552399 := bstep (se 1 (by rfl) ⟨1164299, by rfl⟩ : syracuseStep 1552399 = 2328599) B2328599
theorem B21245975 : Blo 1551473 21245975 := bstep (se 1 (by rfl) ⟨15934481, by rfl⟩ : syracuseStep 21245975 = 31868963) B31868963
theorem B4419643 : Blo 1551473 4419643 := bstep (se 1 (by rfl) ⟨3314732, by rfl⟩ : syracuseStep 4419643 = 6629465) B6629465
theorem B1552443 : Blo 1551473 1552443 := bstep (se 1 (by rfl) ⟨1164332, by rfl⟩ : syracuseStep 1552443 = 2328665) B2328665
theorem B1552519 : Blo 1551473 1552519 := bstep (se 1 (by rfl) ⟨1164389, by rfl⟩ : syracuseStep 1552519 = 2328779) B2328779
theorem B1552527 : Blo 1551473 1552527 := bstep (se 1 (by rfl) ⟨1164395, by rfl⟩ : syracuseStep 1552527 = 2328791) B2328791
theorem B1552571 : Blo 1551473 1552571 := bstep (se 1 (by rfl) ⟨1164428, by rfl⟩ : syracuseStep 1552571 = 2328857) B2328857
theorem B37753073 : Blo 1551473 37753073 := bstep (se 2 (by rfl) ⟨14157402, by rfl⟩ : syracuseStep 37753073 = 28314805) B28314805
theorem B7459073 : Blo 1551473 7459073 := bstep (se 2 (by rfl) ⟨2797152, by rfl⟩ : syracuseStep 7459073 = 5594305) B5594305
theorem B1552647 : Blo 1551473 1552647 := bstep (se 1 (by rfl) ⟨1164485, by rfl⟩ : syracuseStep 1552647 = 2328971) B2328971
theorem B1552655 : Blo 1551473 1552655 := bstep (se 1 (by rfl) ⟨1164491, by rfl⟩ : syracuseStep 1552655 = 2328983) B2328983
theorem B3494159 : Blo 1551473 3494159 := bstep (se 1 (by rfl) ⟨2620619, by rfl⟩ : syracuseStep 3494159 = 5241239) B5241239
theorem B3494177 : Blo 1551473 3494177 := bstep (se 2 (by rfl) ⟨1310316, by rfl⟩ : syracuseStep 3494177 = 2620633) B2620633
theorem B1552699 : Blo 1551473 1552699 := bstep (se 1 (by rfl) ⟨1164524, by rfl⟩ : syracuseStep 1552699 = 2329049) B2329049
theorem B3928439 : Blo 1551473 3928439 := bstep (se 1 (by rfl) ⟨2946329, by rfl⟩ : syracuseStep 3928439 = 5892659) B5892659
theorem B6812039 : Blo 1551473 6812039 := bstep (se 1 (by rfl) ⟨5109029, by rfl⟩ : syracuseStep 6812039 = 10218059) B10218059
theorem B1552775 : Blo 1551473 1552775 := bstep (se 1 (by rfl) ⟨1164581, by rfl⟩ : syracuseStep 1552775 = 2329163) B2329163
theorem B6295943 : Blo 1551473 6295943 := bstep (se 1 (by rfl) ⟨4721957, by rfl⟩ : syracuseStep 6295943 = 9443915) B9443915
theorem B1552783 : Blo 1551473 1552783 := bstep (se 1 (by rfl) ⟨1164587, by rfl⟩ : syracuseStep 1552783 = 2329175) B2329175
theorem B5239187 : Blo 1551473 5239187 := bstep (se 1 (by rfl) ⟨3929390, by rfl⟩ : syracuseStep 5239187 = 7858781) B7858781
theorem B1552827 : Blo 1551473 1552827 := bstep (se 1 (by rfl) ⟨1164620, by rfl⟩ : syracuseStep 1552827 = 2329241) B2329241
theorem B1552903 : Blo 1551473 1552903 := bstep (se 1 (by rfl) ⟨1164677, by rfl⟩ : syracuseStep 1552903 = 2329355) B2329355
theorem B1552911 : Blo 1551473 1552911 := bstep (se 1 (by rfl) ⟨1164683, by rfl⟩ : syracuseStep 1552911 = 2329367) B2329367
theorem B1552955 : Blo 1551473 1552955 := bstep (se 1 (by rfl) ⟨1164716, by rfl⟩ : syracuseStep 1552955 = 2329433) B2329433
theorem B4256315 : Blo 1551473 4256315 := bstep (se 1 (by rfl) ⟨3192236, by rfl⟩ : syracuseStep 4256315 = 6384473) B6384473
theorem B7565885 : Blo 1551473 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B8843863 : Blo 1551473 8843863 := bstep (se 1 (by rfl) ⟨6632897, by rfl⟩ : syracuseStep 8843863 = 13265795) B13265795
theorem B3494519 : Blo 1551473 3494519 := bstep (se 1 (by rfl) ⟨2620889, by rfl⟩ : syracuseStep 3494519 = 5241779) B5241779
theorem B1553031 : Blo 1551473 1553031 := bstep (se 1 (by rfl) ⟨1164773, by rfl⟩ : syracuseStep 1553031 = 2329547) B2329547
theorem B1553039 : Blo 1551473 1553039 := bstep (se 1 (by rfl) ⟨1164779, by rfl⟩ : syracuseStep 1553039 = 2329559) B2329559
theorem B1553083 : Blo 1551473 1553083 := bstep (se 1 (by rfl) ⟨1164812, by rfl⟩ : syracuseStep 1553083 = 2329625) B2329625
theorem B2945737 : Blo 1551473 2945737 := bstep (se 2 (by rfl) ⟨1104651, by rfl⟩ : syracuseStep 2945737 = 2209303) B2209303
theorem B1553159 : Blo 1551473 1553159 := bstep (se 1 (by rfl) ⟨1164869, by rfl⟩ : syracuseStep 1553159 = 2329739) B2329739
theorem B1553167 : Blo 1551473 1553167 := bstep (se 1 (by rfl) ⟨1164875, by rfl⟩ : syracuseStep 1553167 = 2329751) B2329751
theorem B2798369 : Blo 1551473 2798369 := bstep (se 2 (by rfl) ⟨1049388, by rfl⟩ : syracuseStep 2798369 = 2098777) B2098777
theorem B3494699 : Blo 1551473 3494699 := bstep (se 1 (by rfl) ⟨2621024, by rfl⟩ : syracuseStep 3494699 = 5242049) B5242049
theorem B1553211 : Blo 1551473 1553211 := bstep (se 1 (by rfl) ⟨1164908, by rfl⟩ : syracuseStep 1553211 = 2329817) B2329817
theorem B1553287 : Blo 1551473 1553287 := bstep (se 1 (by rfl) ⟨1164965, by rfl⟩ : syracuseStep 1553287 = 2329931) B2329931
theorem B1553295 : Blo 1551473 1553295 := bstep (se 1 (by rfl) ⟨1164971, by rfl⟩ : syracuseStep 1553295 = 2329943) B2329943
theorem B7558033 : Blo 1551473 7558033 := bstep (se 2 (by rfl) ⟨2834262, by rfl⟩ : syracuseStep 7558033 = 5668525) B5668525
theorem B1553339 : Blo 1551473 1553339 := bstep (se 1 (by rfl) ⟨1165004, by rfl⟩ : syracuseStep 1553339 = 2330009) B2330009
theorem B1553415 : Blo 1551473 1553415 := bstep (se 1 (by rfl) ⟨1165061, by rfl⟩ : syracuseStep 1553415 = 2330123) B2330123
theorem B1553423 : Blo 1551473 1553423 := bstep (se 1 (by rfl) ⟨1165067, by rfl⟩ : syracuseStep 1553423 = 2330135) B2330135
theorem B1553467 : Blo 1551473 1553467 := bstep (se 1 (by rfl) ⟨1165100, by rfl⟩ : syracuseStep 1553467 = 2330201) B2330201
theorem B5592125 : Blo 1551473 5592125 := bstep (se 3 (by rfl) ⟨1048523, by rfl⟩ : syracuseStep 5592125 = 2097047) B2097047
theorem B7558211 : Blo 1551473 7558211 := bstep (se 1 (by rfl) ⟨5668658, by rfl⟩ : syracuseStep 7558211 = 11337317) B11337317
theorem B5895287 : Blo 1551473 5895287 := bstep (se 1 (by rfl) ⟨4421465, by rfl⟩ : syracuseStep 5895287 = 8842931) B8842931
theorem B3495059 : Blo 1551473 3495059 := bstep (se 1 (by rfl) ⟨2621294, by rfl⟩ : syracuseStep 3495059 = 5242589) B5242589
theorem B4420793 : Blo 1551473 4420793 := bstep (se 2 (by rfl) ⟨1657797, by rfl⟩ : syracuseStep 4420793 = 3315595) B3315595
theorem B3495113 : Blo 1551473 3495113 := bstep (se 2 (by rfl) ⟨1310667, by rfl⟩ : syracuseStep 3495113 = 2621335) B2621335
theorem B1865003 : Blo 1551473 1865003 := bstep (se 1 (by rfl) ⟨1398752, by rfl⟩ : syracuseStep 1865003 = 2797505) B2797505
theorem B3929431 : Blo 1551473 3929431 := bstep (se 1 (by rfl) ⟨2947073, by rfl⟩ : syracuseStep 3929431 = 5894147) B5894147
theorem B2618743 : Blo 1551473 2618743 := bstep (se 1 (by rfl) ⟨1964057, by rfl⟩ : syracuseStep 2618743 = 3928115) B3928115
theorem B2946451 : Blo 1551473 2946451 := bstep (se 1 (by rfl) ⟨2209838, by rfl⟩ : syracuseStep 2946451 = 4419677) B4419677
theorem B8836573 : Blo 1551473 8836573 := bstep (se 3 (by rfl) ⟨1656857, by rfl⟩ : syracuseStep 8836573 = 3313715) B3313715
theorem B4421135 : Blo 1551473 4421135 := bstep (se 1 (by rfl) ⟨3315851, by rfl⟩ : syracuseStep 4421135 = 6631703) B6631703
theorem B2618939 : Blo 1551473 2618939 := bstep (se 1 (by rfl) ⟨1964204, by rfl⟩ : syracuseStep 2618939 = 3928409) B3928409
theorem B12596813 : Blo 1551473 12596813 := bstep (se 3 (by rfl) ⟨2361902, by rfl⟩ : syracuseStep 12596813 = 4723805) B4723805
theorem B28325477 : Blo 1551473 28325477 := bstep (se 4 (by rfl) ⟨2655513, by rfl⟩ : syracuseStep 28325477 = 5311027) B5311027
theorem B3929735 : Blo 1551473 3929735 := bstep (se 1 (by rfl) ⟨2947301, by rfl⟩ : syracuseStep 3929735 = 5894603) B5894603
theorem B1865359 : Blo 1551473 1865359 := bstep (se 1 (by rfl) ⟨1399019, by rfl⟩ : syracuseStep 1865359 = 2798039) B2798039
theorem B32315057 : Blo 1551473 32315057 := bstep (se 2 (by rfl) ⟨12118146, by rfl⟩ : syracuseStep 32315057 = 24236293) B24236293
theorem B11785985 : Blo 1551473 11785985 := bstep (se 2 (by rfl) ⟨4419744, by rfl⟩ : syracuseStep 11785985 = 8839489) B8839489
theorem B3929867 : Blo 1551473 3929867 := bstep (se 1 (by rfl) ⟨2947400, by rfl⟩ : syracuseStep 3929867 = 5894801) B5894801
theorem B5240591 : Blo 1551473 5240591 := bstep (se 1 (by rfl) ⟨3930443, by rfl⟩ : syracuseStep 5240591 = 7860887) B7860887
theorem B7370585 : Blo 1551473 7370585 := bstep (se 2 (by rfl) ⟨2763969, by rfl⟩ : syracuseStep 7370585 = 5527939) B5527939
theorem B9566105 : Blo 1551473 9566105 := bstep (se 2 (by rfl) ⟨3587289, by rfl⟩ : syracuseStep 9566105 = 7174579) B7174579
theorem B2619337 : Blo 1551473 2619337 := bstep (se 2 (by rfl) ⟨982251, by rfl⟩ : syracuseStep 2619337 = 1964503) B1964503
theorem B33552407 : Blo 1551473 33552407 := bstep (se 1 (by rfl) ⟨25164305, by rfl⟩ : syracuseStep 33552407 = 50328611) B50328611
theorem B5240861 : Blo 1551473 5240861 := bstep (se 3 (by rfl) ⟨982661, by rfl⟩ : syracuseStep 5240861 = 1965323) B1965323
theorem B5896259 : Blo 1551473 5896259 := bstep (se 1 (by rfl) ⟨4422194, by rfl⟩ : syracuseStep 5896259 = 8844389) B8844389
theorem B4970767 : Blo 1551473 4970767 := bstep (se 1 (by rfl) ⟨3728075, by rfl⟩ : syracuseStep 4970767 = 7456151) B7456151
theorem B3930383 : Blo 1551473 3930383 := bstep (se 1 (by rfl) ⟨2947787, by rfl⟩ : syracuseStep 3930383 = 5895575) B5895575
theorem B1964407 : Blo 1551473 1964407 := bstep (se 1 (by rfl) ⟨1473305, by rfl⟩ : syracuseStep 1964407 = 2946611) B2946611
theorem B4422023 : Blo 1551473 4422023 := bstep (se 1 (by rfl) ⟨3316517, by rfl⟩ : syracuseStep 4422023 = 6633035) B6633035
theorem B3930515 : Blo 1551473 3930515 := bstep (se 1 (by rfl) ⟨2947886, by rfl⟩ : syracuseStep 3930515 = 5895773) B5895773
theorem B2947529 : Blo 1551473 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B9943505 : Blo 1551473 9943505 := bstep (se 2 (by rfl) ⟨3728814, by rfl⟩ : syracuseStep 9943505 = 7457629) B7457629
theorem B8845847 : Blo 1551473 8845847 := bstep (se 1 (by rfl) ⟨6634385, by rfl⟩ : syracuseStep 8845847 = 13268771) B13268771
theorem B4422205 : Blo 1551473 4422205 := bstep (se 3 (by rfl) ⟨829163, by rfl⟩ : syracuseStep 4422205 = 1658327) B1658327
theorem B2620039 : Blo 1551473 2620039 := bstep (se 1 (by rfl) ⟨1965029, by rfl⟩ : syracuseStep 2620039 = 3930059) B3930059
theorem B1964731 : Blo 1551473 1964731 := bstep (se 1 (by rfl) ⟨1473548, by rfl⟩ : syracuseStep 1964731 = 2947097) B2947097
theorem B4422433 : Blo 1551473 4422433 := bstep (se 2 (by rfl) ⟨1658412, by rfl⟩ : syracuseStep 4422433 = 3316825) B3316825
theorem B8395609 : Blo 1551473 8395609 := bstep (se 2 (by rfl) ⟨3148353, by rfl⟩ : syracuseStep 8395609 = 6296707) B6296707
theorem B7863155 : Blo 1551473 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B2210761 : Blo 1551473 2210761 := bstep (se 2 (by rfl) ⟨829035, by rfl⟩ : syracuseStep 2210761 = 1658071) B1658071
theorem B5897245 : Blo 1551473 5897245 := bstep (se 3 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 5897245 = 2211467) B2211467
theorem B9698365 : Blo 1551473 9698365 := bstep (se 3 (by rfl) ⟨1818443, by rfl⟩ : syracuseStep 9698365 = 3636887) B3636887
theorem B8510525 : Blo 1551473 8510525 := bstep (se 3 (by rfl) ⟨1595723, by rfl⟩ : syracuseStep 8510525 = 3191447) B3191447
theorem B8387651 : Blo 1551473 8387651 := bstep (se 1 (by rfl) ⟨6290738, by rfl⟩ : syracuseStep 8387651 = 12581477) B12581477
theorem B4422775 : Blo 1551473 4422775 := bstep (se 1 (by rfl) ⟨3317081, by rfl⟩ : syracuseStep 4422775 = 6634163) B6634163
theorem B2620687 : Blo 1551473 2620687 := bstep (se 1 (by rfl) ⟨1965515, by rfl⟩ : syracuseStep 2620687 = 3931031) B3931031
theorem B2948395 : Blo 1551473 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B6634811 : Blo 1551473 6634811 := bstep (se 1 (by rfl) ⟨4976108, by rfl⟩ : syracuseStep 6634811 = 9952217) B9952217
theorem B7863641 : Blo 1551473 7863641 := bstep (se 2 (by rfl) ⟨2948865, by rfl⟩ : syracuseStep 7863641 = 5897731) B5897731
theorem B4783475 : Blo 1551473 4783475 := bstep (se 1 (by rfl) ⟨3587606, by rfl⟩ : syracuseStep 4783475 = 7175213) B7175213
theorem B2948471 : Blo 1551473 2948471 := bstep (se 1 (by rfl) ⟨2211353, by rfl⟩ : syracuseStep 2948471 = 4422707) B4422707
theorem B5242265 : Blo 1551473 5242265 := bstep (se 2 (by rfl) ⟨1965849, by rfl⟩ : syracuseStep 5242265 = 3931699) B3931699
theorem B3931649 : Blo 1551473 3931649 := bstep (se 2 (by rfl) ⟨1474368, by rfl⟩ : syracuseStep 3931649 = 2948737) B2948737
theorem B48455171 : Blo 1551473 48455171 := bstep (se 1 (by rfl) ⟨36341378, by rfl⟩ : syracuseStep 48455171 = 72682757) B72682757
theorem B7855703 : Blo 1551473 7855703 := bstep (se 1 (by rfl) ⟨5891777, by rfl⟩ : syracuseStep 7855703 = 11783555) B11783555
theorem B1965703 : Blo 1551473 1965703 := bstep (se 1 (by rfl) ⟨1474277, by rfl⟩ : syracuseStep 1965703 = 2948555) B2948555
theorem B7085839 : Blo 1551473 7085839 := bstep (se 1 (by rfl) ⟨5314379, by rfl⟩ : syracuseStep 7085839 = 10628759) B10628759
theorem B2621227 : Blo 1551473 2621227 := bstep (se 1 (by rfl) ⟨1965920, by rfl⟩ : syracuseStep 2621227 = 3931841) B3931841
theorem B29835053 : Blo 1551473 29835053 := bstep (se 3 (by rfl) ⟨5594072, by rfl⟩ : syracuseStep 29835053 = 11188145) B11188145
theorem B3932023 : Blo 1551473 3932023 := bstep (se 1 (by rfl) ⟨2949017, by rfl⟩ : syracuseStep 3932023 = 5898035) B5898035
theorem B19881881 : Blo 1551473 19881881 := bstep (se 2 (by rfl) ⟨7455705, by rfl⟩ : syracuseStep 19881881 = 14911411) B14911411
theorem B53780377 : Blo 1551473 53780377 := bstep (se 2 (by rfl) ⟨20167641, by rfl⟩ : syracuseStep 53780377 = 40335283) B40335283
theorem B2621369 : Blo 1551473 2621369 := bstep (se 2 (by rfl) ⟨983013, by rfl⟩ : syracuseStep 2621369 = 1966027) B1966027
theorem B4480969 : Blo 1551473 4480969 := bstep (se 2 (by rfl) ⟨1680363, by rfl⟩ : syracuseStep 4480969 = 3360727) B3360727
theorem B14163983 : Blo 1551473 14163983 := bstep (se 1 (by rfl) ⟨10622987, by rfl⟩ : syracuseStep 14163983 = 21245975) B21245975
theorem B2949139 : Blo 1551473 2949139 := bstep (se 1 (by rfl) ⟨2211854, by rfl⟩ : syracuseStep 2949139 = 4423709) B4423709
theorem B4972715 : Blo 1551473 4972715 := bstep (se 1 (by rfl) ⟨3729536, by rfl⟩ : syracuseStep 4972715 = 7459073) B7459073
theorem B6627689 : Blo 1551473 6627689 := bstep (se 2 (by rfl) ⟨2485383, by rfl⟩ : syracuseStep 6627689 = 4970767) B4970767
theorem B7856513 : Blo 1551473 7856513 := bstep (se 2 (by rfl) ⟨2946192, by rfl⟩ : syracuseStep 7856513 = 5892385) B5892385
theorem B5038807 : Blo 1551473 5038807 := bstep (se 1 (by rfl) ⟨3779105, by rfl⟩ : syracuseStep 5038807 = 7558211) B7558211
theorem B4973341 : Blo 1551473 4973341 := bstep (se 3 (by rfl) ⟨932501, by rfl⟩ : syracuseStep 4973341 = 1865003) B1865003
theorem B2327471 : Blo 1551473 2327471 := bstep (se 1 (by rfl) ⟨1745603, by rfl⟩ : syracuseStep 2327471 = 3491207) B3491207
theorem B3539899 : Blo 1551473 3539899 := bstep (se 1 (by rfl) ⟨2654924, by rfl⟩ : syracuseStep 3539899 = 5309849) B5309849
theorem B2327561 : Blo 1551473 2327561 := bstep (se 2 (by rfl) ⟨872835, by rfl⟩ : syracuseStep 2327561 = 1745671) B1745671
theorem B2327591 : Blo 1551473 2327591 := bstep (se 1 (by rfl) ⟨1745693, by rfl⟩ : syracuseStep 2327591 = 3491387) B3491387
theorem B1745959 : Blo 1551473 1745959 := bstep (se 1 (by rfl) ⟨1309469, by rfl⟩ : syracuseStep 1745959 = 2618939) B2618939
theorem B8397875 : Blo 1551473 8397875 := bstep (se 1 (by rfl) ⟨6298406, by rfl⟩ : syracuseStep 8397875 = 12596813) B12596813
theorem B18883651 : Blo 1551473 18883651 := bstep (se 1 (by rfl) ⟨14162738, by rfl⟩ : syracuseStep 18883651 = 28325477) B28325477
theorem B3277903 : Blo 1551473 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B2327675 : Blo 1551473 2327675 := bstep (se 1 (by rfl) ⟨1745756, by rfl⟩ : syracuseStep 2327675 = 3491513) B3491513
theorem B13436057 : Blo 1551473 13436057 := bstep (se 2 (by rfl) ⟨5038521, by rfl⟩ : syracuseStep 13436057 = 10077043) B10077043
theorem B6292637 : Blo 1551473 6292637 := bstep (se 3 (by rfl) ⟨1179869, by rfl⟩ : syracuseStep 6292637 = 2359739) B2359739
theorem B7857323 : Blo 1551473 7857323 := bstep (se 1 (by rfl) ⟨5892992, by rfl⟩ : syracuseStep 7857323 = 11785985) B11785985
theorem B10077377 : Blo 1551473 10077377 := bstep (se 2 (by rfl) ⟨3779016, by rfl⟩ : syracuseStep 10077377 = 7558033) B7558033
theorem B3146951 : Blo 1551473 3146951 := bstep (se 1 (by rfl) ⟨2360213, by rfl⟩ : syracuseStep 3146951 = 4720427) B4720427
theorem B3491063 : Blo 1551473 3491063 := bstep (se 1 (by rfl) ⟨2618297, by rfl⟩ : syracuseStep 3491063 = 5236595) B5236595
theorem B2327801 : Blo 1551473 2327801 := bstep (se 2 (by rfl) ⟨872925, by rfl⟩ : syracuseStep 2327801 = 1745851) B1745851
theorem B2327903 : Blo 1551473 2327903 := bstep (se 1 (by rfl) ⟨1745927, by rfl⟩ : syracuseStep 2327903 = 3491855) B3491855
theorem B2327915 : Blo 1551473 2327915 := bstep (se 1 (by rfl) ⟨1745936, by rfl⟩ : syracuseStep 2327915 = 3491873) B3491873
theorem B2328143 : Blo 1551473 2328143 := bstep (se 1 (by rfl) ⟨1746107, by rfl⟩ : syracuseStep 2328143 = 3492215) B3492215
theorem B6629003 : Blo 1551473 6629003 := bstep (se 1 (by rfl) ⟨4971752, by rfl⟩ : syracuseStep 6629003 = 9943505) B9943505
theorem B7857809 : Blo 1551473 7857809 := bstep (se 2 (by rfl) ⟨2946678, by rfl⟩ : syracuseStep 7857809 = 5893357) B5893357
theorem B31090321 : Blo 1551473 31090321 := bstep (se 2 (by rfl) ⟨11658870, by rfl⟩ : syracuseStep 31090321 = 23317741) B23317741
theorem B2328263 : Blo 1551473 2328263 := bstep (se 1 (by rfl) ⟨1746197, by rfl⟩ : syracuseStep 2328263 = 3492395) B3492395
theorem B7276331 : Blo 1551473 7276331 := bstep (se 1 (by rfl) ⟨5457248, by rfl⟩ : syracuseStep 7276331 = 10914497) B10914497
theorem B3491657 : Blo 1551473 3491657 := bstep (se 2 (by rfl) ⟨1309371, by rfl⟩ : syracuseStep 3491657 = 2618743) B2618743
theorem B2328425 : Blo 1551473 2328425 := bstep (se 2 (by rfl) ⟨873159, by rfl⟩ : syracuseStep 2328425 = 1746319) B1746319
theorem B2328503 : Blo 1551473 2328503 := bstep (se 1 (by rfl) ⟨1746377, by rfl⟩ : syracuseStep 2328503 = 3492755) B3492755
theorem B11782097 : Blo 1551473 11782097 := bstep (se 2 (by rfl) ⟨4418286, by rfl⟩ : syracuseStep 11782097 = 8836573) B8836573
theorem B2328539 : Blo 1551473 2328539 := bstep (se 1 (by rfl) ⟨1746404, by rfl⟩ : syracuseStep 2328539 = 3492809) B3492809
theorem B3188983 : Blo 1551473 3188983 := bstep (se 1 (by rfl) ⟨2391737, by rfl⟩ : syracuseStep 3188983 = 4783475) B4783475
theorem B13257047 : Blo 1551473 13257047 := bstep (se 1 (by rfl) ⟨9942785, by rfl⟩ : syracuseStep 13257047 = 19885571) B19885571
theorem B32303447 : Blo 1551473 32303447 := bstep (se 1 (by rfl) ⟨24227585, by rfl⟩ : syracuseStep 32303447 = 48455171) B48455171
theorem B9447785 : Blo 1551473 9447785 := bstep (se 2 (by rfl) ⟨3542919, by rfl⟩ : syracuseStep 9447785 = 7085839) B7085839
theorem B5237135 : Blo 1551473 5237135 := bstep (se 1 (by rfl) ⟨3927851, by rfl⟩ : syracuseStep 5237135 = 7855703) B7855703
theorem B2329007 : Blo 1551473 2329007 := bstep (se 1 (by rfl) ⟨1746755, by rfl⟩ : syracuseStep 2329007 = 3493511) B3493511
theorem B2329097 : Blo 1551473 2329097 := bstep (se 2 (by rfl) ⟨873411, by rfl⟩ : syracuseStep 2329097 = 1746823) B1746823
theorem B71707169 : Blo 1551473 71707169 := bstep (se 2 (by rfl) ⟨26890188, by rfl⟩ : syracuseStep 71707169 = 53780377) B53780377
theorem B2329127 : Blo 1551473 2329127 := bstep (se 1 (by rfl) ⟨1746845, by rfl⟩ : syracuseStep 2329127 = 3493691) B3493691
theorem B3492449 : Blo 1551473 3492449 := bstep (se 2 (by rfl) ⟨1309668, by rfl⟩ : syracuseStep 3492449 = 2619337) B2619337
theorem B5974625 : Blo 1551473 5974625 := bstep (se 2 (by rfl) ⟨2240484, by rfl⟩ : syracuseStep 5974625 = 4480969) B4480969
theorem B2329211 : Blo 1551473 2329211 := bstep (se 1 (by rfl) ⟨1746908, by rfl⟩ : syracuseStep 2329211 = 3493817) B3493817
theorem B1747579 : Blo 1551473 1747579 := bstep (se 1 (by rfl) ⟨1310684, by rfl⟩ : syracuseStep 1747579 = 2621369) B2621369
theorem B5237459 : Blo 1551473 5237459 := bstep (se 1 (by rfl) ⟨3928094, by rfl⟩ : syracuseStep 5237459 = 7856189) B7856189
theorem B5892857 : Blo 1551473 5892857 := bstep (se 2 (by rfl) ⟨2209821, by rfl⟩ : syracuseStep 5892857 = 4419643) B4419643
theorem B2329337 : Blo 1551473 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B25168715 : Blo 1551473 25168715 := bstep (se 1 (by rfl) ⟨18876536, by rfl⟩ : syracuseStep 25168715 = 37753073) B37753073
theorem B14912333 : Blo 1551473 14912333 := bstep (se 3 (by rfl) ⟨2796062, by rfl⟩ : syracuseStep 14912333 = 5592125) B5592125
theorem B2329439 : Blo 1551473 2329439 := bstep (se 1 (by rfl) ⟨1747079, by rfl⟩ : syracuseStep 2329439 = 3494159) B3494159
theorem B2329451 : Blo 1551473 2329451 := bstep (se 1 (by rfl) ⟨1747088, by rfl⟩ : syracuseStep 2329451 = 3494177) B3494177
theorem B4541359 : Blo 1551473 4541359 := bstep (se 1 (by rfl) ⟨3406019, by rfl⟩ : syracuseStep 4541359 = 6812039) B6812039
theorem B4197295 : Blo 1551473 4197295 := bstep (se 1 (by rfl) ⟨3147971, by rfl⟩ : syracuseStep 4197295 = 6295943) B6295943
theorem B3492791 : Blo 1551473 3492791 := bstep (se 1 (by rfl) ⟨2619593, by rfl⟩ : syracuseStep 3492791 = 5239187) B5239187
theorem B5975059 : Blo 1551473 5975059 := bstep (se 1 (by rfl) ⟨4481294, by rfl⟩ : syracuseStep 5975059 = 8962589) B8962589
theorem B2837543 : Blo 1551473 2837543 := bstep (se 1 (by rfl) ⟨2128157, by rfl⟩ : syracuseStep 2837543 = 4256315) B4256315
theorem B3779641 : Blo 1551473 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B2329679 : Blo 1551473 2329679 := bstep (se 1 (by rfl) ⟨1747259, by rfl⟩ : syracuseStep 2329679 = 3494519) B3494519
theorem B1551483 : Blo 1551473 1551483 := bstep (se 1 (by rfl) ⟨1163612, by rfl⟩ : syracuseStep 1551483 = 2327225) B2327225
theorem B1551535 : Blo 1551473 1551535 := bstep (se 1 (by rfl) ⟨1163651, by rfl⟩ : syracuseStep 1551535 = 2327303) B2327303
theorem B1551559 : Blo 1551473 1551559 := bstep (se 1 (by rfl) ⟨1163669, by rfl⟩ : syracuseStep 1551559 = 2327339) B2327339
theorem B2329799 : Blo 1551473 2329799 := bstep (se 1 (by rfl) ⟨1747349, by rfl⟩ : syracuseStep 2329799 = 3494699) B3494699
theorem B1551579 : Blo 1551473 1551579 := bstep (se 1 (by rfl) ⟨1163684, by rfl⟩ : syracuseStep 1551579 = 2327369) B2327369
theorem B1551655 : Blo 1551473 1551655 := bstep (se 1 (by rfl) ⟨1163741, by rfl⟩ : syracuseStep 1551655 = 2327483) B2327483
theorem B1551695 : Blo 1551473 1551695 := bstep (se 1 (by rfl) ⟨1163771, by rfl⟩ : syracuseStep 1551695 = 2327543) B2327543
theorem B1551711 : Blo 1551473 1551711 := bstep (se 1 (by rfl) ⟨1163783, by rfl⟩ : syracuseStep 1551711 = 2327567) B2327567
theorem B2329961 : Blo 1551473 2329961 := bstep (se 2 (by rfl) ⟨873735, by rfl⟩ : syracuseStep 2329961 = 1747471) B1747471
theorem B1551739 : Blo 1551473 1551739 := bstep (se 1 (by rfl) ⟨1163804, by rfl⟩ : syracuseStep 1551739 = 2327609) B2327609
theorem B5311873 : Blo 1551473 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B2796943 : Blo 1551473 2796943 := bstep (se 1 (by rfl) ⟨2097707, by rfl⟩ : syracuseStep 2796943 = 4195415) B4195415
theorem B9948581 : Blo 1551473 9948581 := bstep (se 4 (by rfl) ⟨932679, by rfl⟩ : syracuseStep 9948581 = 1865359) B1865359
theorem B1551791 : Blo 1551473 1551791 := bstep (se 1 (by rfl) ⟨1163843, by rfl⟩ : syracuseStep 1551791 = 2327687) B2327687
theorem B2330039 : Blo 1551473 2330039 := bstep (se 1 (by rfl) ⟨1747529, by rfl⟩ : syracuseStep 2330039 = 3495059) B3495059
theorem B1551815 : Blo 1551473 1551815 := bstep (se 1 (by rfl) ⟨1163861, by rfl⟩ : syracuseStep 1551815 = 2327723) B2327723
theorem B11791817 : Blo 1551473 11791817 := bstep (se 2 (by rfl) ⟨4421931, by rfl⟩ : syracuseStep 11791817 = 8843863) B8843863
theorem B2485723 : Blo 1551473 2485723 := bstep (se 1 (by rfl) ⟨1864292, by rfl⟩ : syracuseStep 2485723 = 3728585) B3728585
theorem B1551835 : Blo 1551473 1551835 := bstep (se 1 (by rfl) ⟨1163876, by rfl⟩ : syracuseStep 1551835 = 2327753) B2327753
theorem B2330075 : Blo 1551473 2330075 := bstep (se 1 (by rfl) ⟨1747556, by rfl⟩ : syracuseStep 2330075 = 3495113) B3495113
theorem B3493385 : Blo 1551473 3493385 := bstep (se 2 (by rfl) ⟨1310019, by rfl⟩ : syracuseStep 3493385 = 2620039) B2620039
theorem B1551911 : Blo 1551473 1551911 := bstep (se 1 (by rfl) ⟨1163933, by rfl⟩ : syracuseStep 1551911 = 2327867) B2327867
theorem B1551951 : Blo 1551473 1551951 := bstep (se 1 (by rfl) ⟨1163963, by rfl⟩ : syracuseStep 1551951 = 2327927) B2327927
theorem B1551967 : Blo 1551473 1551967 := bstep (se 1 (by rfl) ⟨1163975, by rfl⟩ : syracuseStep 1551967 = 2327951) B2327951
theorem B3927649 : Blo 1551473 3927649 := bstep (se 2 (by rfl) ⟨1472868, by rfl⟩ : syracuseStep 3927649 = 2945737) B2945737
theorem B1551995 : Blo 1551473 1551995 := bstep (se 1 (by rfl) ⟨1163996, by rfl⟩ : syracuseStep 1551995 = 2327993) B2327993
theorem B1552047 : Blo 1551473 1552047 := bstep (se 1 (by rfl) ⟨1164035, by rfl⟩ : syracuseStep 1552047 = 2328071) B2328071
theorem B6295229 : Blo 1551473 6295229 := bstep (se 3 (by rfl) ⟨1180355, by rfl⟩ : syracuseStep 6295229 = 2360711) B2360711
theorem B1552071 : Blo 1551473 1552071 := bstep (se 1 (by rfl) ⟨1164053, by rfl⟩ : syracuseStep 1552071 = 2328107) B2328107
theorem B5893843 : Blo 1551473 5893843 := bstep (se 1 (by rfl) ⟨4420382, by rfl⟩ : syracuseStep 5893843 = 8840765) B8840765
theorem B1552091 : Blo 1551473 1552091 := bstep (se 1 (by rfl) ⟨1164068, by rfl⟩ : syracuseStep 1552091 = 2328137) B2328137
theorem B11194145 : Blo 1551473 11194145 := bstep (se 2 (by rfl) ⟨4197804, by rfl⟩ : syracuseStep 11194145 = 8395609) B8395609
theorem B1552167 : Blo 1551473 1552167 := bstep (se 1 (by rfl) ⟨1164125, by rfl⟩ : syracuseStep 1552167 = 2328251) B2328251
theorem B1552207 : Blo 1551473 1552207 := bstep (se 1 (by rfl) ⟨1164155, by rfl⟩ : syracuseStep 1552207 = 2328311) B2328311
theorem B1552223 : Blo 1551473 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B3493727 : Blo 1551473 3493727 := bstep (se 1 (by rfl) ⟨2620295, by rfl⟩ : syracuseStep 3493727 = 5240591) B5240591
theorem B7860077 : Blo 1551473 7860077 := bstep (se 3 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 7860077 = 2947529) B2947529
theorem B5238647 : Blo 1551473 5238647 := bstep (se 1 (by rfl) ⟨3928985, by rfl⟩ : syracuseStep 5238647 = 7857971) B7857971
theorem B1552251 : Blo 1551473 1552251 := bstep (se 1 (by rfl) ⟨1164188, by rfl⟩ : syracuseStep 1552251 = 2328377) B2328377
theorem B1552303 : Blo 1551473 1552303 := bstep (se 1 (by rfl) ⟨1164227, by rfl⟩ : syracuseStep 1552303 = 2328455) B2328455
theorem B1552327 : Blo 1551473 1552327 := bstep (se 1 (by rfl) ⟨1164245, by rfl⟩ : syracuseStep 1552327 = 2328491) B2328491
theorem B1552347 : Blo 1551473 1552347 := bstep (se 1 (by rfl) ⟨1164260, by rfl⟩ : syracuseStep 1552347 = 2328521) B2328521
theorem B22368271 : Blo 1551473 22368271 := bstep (se 1 (by rfl) ⟨16776203, by rfl⟩ : syracuseStep 22368271 = 33552407) B33552407
theorem B7860239 : Blo 1551473 7860239 := bstep (se 1 (by rfl) ⟨5895179, by rfl⟩ : syracuseStep 7860239 = 11790359) B11790359
theorem B3493907 : Blo 1551473 3493907 := bstep (se 1 (by rfl) ⟨2620430, by rfl⟩ : syracuseStep 3493907 = 5240861) B5240861
theorem B1552423 : Blo 1551473 1552423 := bstep (se 1 (by rfl) ⟨1164317, by rfl⟩ : syracuseStep 1552423 = 2328635) B2328635
theorem B5238863 : Blo 1551473 5238863 := bstep (se 1 (by rfl) ⟨3929147, by rfl⟩ : syracuseStep 5238863 = 7858295) B7858295
theorem B1552463 : Blo 1551473 1552463 := bstep (se 1 (by rfl) ⟨1164347, by rfl⟩ : syracuseStep 1552463 = 2328695) B2328695
theorem B12931153 : Blo 1551473 12931153 := bstep (se 2 (by rfl) ⟨4849182, by rfl⟩ : syracuseStep 12931153 = 9698365) B9698365
theorem B1552479 : Blo 1551473 1552479 := bstep (se 1 (by rfl) ⟨1164359, by rfl⟩ : syracuseStep 1552479 = 2328719) B2328719
theorem B1552507 : Blo 1551473 1552507 := bstep (se 1 (by rfl) ⟨1164380, by rfl⟩ : syracuseStep 1552507 = 2328761) B2328761
theorem B5894315 : Blo 1551473 5894315 := bstep (se 1 (by rfl) ⟨4420736, by rfl⟩ : syracuseStep 5894315 = 8841473) B8841473
theorem B1552559 : Blo 1551473 1552559 := bstep (se 1 (by rfl) ⟨1164419, by rfl⟩ : syracuseStep 1552559 = 2328839) B2328839
theorem B1552583 : Blo 1551473 1552583 := bstep (se 1 (by rfl) ⟨1164437, by rfl⟩ : syracuseStep 1552583 = 2328875) B2328875
theorem B1552603 : Blo 1551473 1552603 := bstep (se 1 (by rfl) ⟨1164452, by rfl⟩ : syracuseStep 1552603 = 2328905) B2328905
theorem B1552679 : Blo 1551473 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B1552719 : Blo 1551473 1552719 := bstep (se 1 (by rfl) ⟨1164539, by rfl⟩ : syracuseStep 1552719 = 2329079) B2329079
theorem B1552735 : Blo 1551473 1552735 := bstep (se 1 (by rfl) ⟨1164551, by rfl⟩ : syracuseStep 1552735 = 2329103) B2329103
theorem B3494249 : Blo 1551473 3494249 := bstep (se 2 (by rfl) ⟨1310343, by rfl⟩ : syracuseStep 3494249 = 2620687) B2620687
theorem B1552763 : Blo 1551473 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B1552815 : Blo 1551473 1552815 := bstep (se 1 (by rfl) ⟨1164611, by rfl⟩ : syracuseStep 1552815 = 2329223) B2329223
theorem B1552839 : Blo 1551473 1552839 := bstep (se 1 (by rfl) ⟨1164629, by rfl⟩ : syracuseStep 1552839 = 2329259) B2329259
theorem B5239241 : Blo 1551473 5239241 := bstep (se 2 (by rfl) ⟨1964715, by rfl⟩ : syracuseStep 5239241 = 3929431) B3929431
theorem B1552859 : Blo 1551473 1552859 := bstep (se 1 (by rfl) ⟨1164644, by rfl⟩ : syracuseStep 1552859 = 2329289) B2329289
theorem B11194861 : Blo 1551473 11194861 := bstep (se 3 (by rfl) ⟨2099036, by rfl⟩ : syracuseStep 11194861 = 4198073) B4198073
theorem B2945555 : Blo 1551473 2945555 := bstep (se 1 (by rfl) ⟨2209166, by rfl⟩ : syracuseStep 2945555 = 4418333) B4418333
theorem B3928601 : Blo 1551473 3928601 := bstep (se 2 (by rfl) ⟨1473225, by rfl⟩ : syracuseStep 3928601 = 2946451) B2946451
theorem B1552935 : Blo 1551473 1552935 := bstep (se 1 (by rfl) ⟨1164701, by rfl⟩ : syracuseStep 1552935 = 2329403) B2329403
theorem B1552975 : Blo 1551473 1552975 := bstep (se 1 (by rfl) ⟨1164731, by rfl⟩ : syracuseStep 1552975 = 2329463) B2329463
theorem B1552991 : Blo 1551473 1552991 := bstep (se 1 (by rfl) ⟨1164743, by rfl⟩ : syracuseStep 1552991 = 2329487) B2329487
theorem B1553019 : Blo 1551473 1553019 := bstep (se 1 (by rfl) ⟨1164764, by rfl⟩ : syracuseStep 1553019 = 2329529) B2329529
theorem B1553071 : Blo 1551473 1553071 := bstep (se 1 (by rfl) ⟨1164803, by rfl⟩ : syracuseStep 1553071 = 2329607) B2329607
theorem B1553095 : Blo 1551473 1553095 := bstep (se 1 (by rfl) ⟨1164821, by rfl⟩ : syracuseStep 1553095 = 2329643) B2329643
theorem B5673683 : Blo 1551473 5673683 := bstep (se 1 (by rfl) ⟨4255262, by rfl⟩ : syracuseStep 5673683 = 8510525) B8510525
theorem B5591767 : Blo 1551473 5591767 := bstep (se 1 (by rfl) ⟨4193825, by rfl⟩ : syracuseStep 5591767 = 8387651) B8387651
theorem B5239511 : Blo 1551473 5239511 := bstep (se 1 (by rfl) ⟨3929633, by rfl⟩ : syracuseStep 5239511 = 7859267) B7859267
theorem B1553115 : Blo 1551473 1553115 := bstep (se 1 (by rfl) ⟨1164836, by rfl⟩ : syracuseStep 1553115 = 2329673) B2329673
theorem B2945783 : Blo 1551473 2945783 := bstep (se 1 (by rfl) ⟨2209337, by rfl⟩ : syracuseStep 2945783 = 4418675) B4418675
theorem B2798327 : Blo 1551473 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B1553191 : Blo 1551473 1553191 := bstep (se 1 (by rfl) ⟨1164893, by rfl⟩ : syracuseStep 1553191 = 2329787) B2329787
theorem B1553231 : Blo 1551473 1553231 := bstep (se 1 (by rfl) ⟨1164923, by rfl⟩ : syracuseStep 1553231 = 2329847) B2329847
theorem B1553247 : Blo 1551473 1553247 := bstep (se 1 (by rfl) ⟨1164935, by rfl⟩ : syracuseStep 1553247 = 2329871) B2329871
theorem B1553275 : Blo 1551473 1553275 := bstep (se 1 (by rfl) ⟨1164956, by rfl⟩ : syracuseStep 1553275 = 2329913) B2329913
theorem B5239727 : Blo 1551473 5239727 := bstep (se 1 (by rfl) ⟨3929795, by rfl⟩ : syracuseStep 5239727 = 7859591) B7859591
theorem B1553327 : Blo 1551473 1553327 := bstep (se 1 (by rfl) ⟨1164995, by rfl⟩ : syracuseStep 1553327 = 2329991) B2329991
theorem B3494843 : Blo 1551473 3494843 := bstep (se 1 (by rfl) ⟨2621132, by rfl⟩ : syracuseStep 3494843 = 5242265) B5242265
theorem B1553351 : Blo 1551473 1553351 := bstep (se 1 (by rfl) ⟨1165013, by rfl⟩ : syracuseStep 1553351 = 2330027) B2330027
theorem B1553371 : Blo 1551473 1553371 := bstep (se 1 (by rfl) ⟨1165028, by rfl⟩ : syracuseStep 1553371 = 2330057) B2330057
theorem B3929107 : Blo 1551473 3929107 := bstep (se 1 (by rfl) ⟨2946830, by rfl⟩ : syracuseStep 3929107 = 5893661) B5893661
theorem B1553447 : Blo 1551473 1553447 := bstep (se 1 (by rfl) ⟨1165085, by rfl⟩ : syracuseStep 1553447 = 2330171) B2330171
theorem B3494969 : Blo 1551473 3494969 := bstep (se 2 (by rfl) ⟨1310613, by rfl⟩ : syracuseStep 3494969 = 2621227) B2621227
theorem B2618615 : Blo 1551473 2618615 := bstep (se 1 (by rfl) ⟨1963961, by rfl⟩ : syracuseStep 2618615 = 3927923) B3927923
theorem B3495311 : Blo 1551473 3495311 := bstep (se 1 (by rfl) ⟨2621483, by rfl⟩ : syracuseStep 3495311 = 5242967) B5242967
theorem B9950759 : Blo 1551473 9950759 := bstep (se 1 (by rfl) ⟨7463069, by rfl⟩ : syracuseStep 9950759 = 14926139) B14926139
theorem B2618959 : Blo 1551473 2618959 := bstep (se 1 (by rfl) ⟨1964219, by rfl⟩ : syracuseStep 2618959 = 3928439) B3928439
theorem B29849269 : Blo 1551473 29849269 := bstep (se 5 (by rfl) ⟨1399184, by rfl⟩ : syracuseStep 29849269 = 2798369) B2798369
theorem B5043923 : Blo 1551473 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B2619209 : Blo 1551473 2619209 := bstep (se 2 (by rfl) ⟨982203, by rfl⟩ : syracuseStep 2619209 = 1964407) B1964407
theorem B6633377 : Blo 1551473 6633377 := bstep (se 2 (by rfl) ⟨2487516, by rfl⟩ : syracuseStep 6633377 = 4975033) B4975033
theorem B4970497 : Blo 1551473 4970497 := bstep (se 2 (by rfl) ⟨1863936, by rfl⟩ : syracuseStep 4970497 = 3727873) B3727873
theorem B22386725 : Blo 1551473 22386725 := bstep (se 4 (by rfl) ⟨2098755, by rfl⟩ : syracuseStep 22386725 = 4197511) B4197511
theorem B3930191 : Blo 1551473 3930191 := bstep (se 1 (by rfl) ⟨2947643, by rfl⟩ : syracuseStep 3930191 = 5895287) B5895287
theorem B5896273 : Blo 1551473 5896273 := bstep (se 2 (by rfl) ⟨2211102, by rfl⟩ : syracuseStep 5896273 = 4422205) B4422205
theorem B2947195 : Blo 1551473 2947195 := bstep (se 1 (by rfl) ⟨2210396, by rfl⟩ : syracuseStep 2947195 = 4420793) B4420793
theorem B17692829 : Blo 1551473 17692829 := bstep (se 3 (by rfl) ⟨3317405, by rfl⟩ : syracuseStep 17692829 = 6634811) B6634811
theorem B2619641 : Blo 1551473 2619641 := bstep (se 2 (by rfl) ⟨982365, by rfl⟩ : syracuseStep 2619641 = 1964731) B1964731
theorem B2947423 : Blo 1551473 2947423 := bstep (se 1 (by rfl) ⟨2210567, by rfl⟩ : syracuseStep 2947423 = 4421135) B4421135
theorem B5896577 : Blo 1551473 5896577 := bstep (se 2 (by rfl) ⟨2211216, by rfl⟩ : syracuseStep 5896577 = 4422433) B4422433
theorem B2619823 : Blo 1551473 2619823 := bstep (se 1 (by rfl) ⟨1964867, by rfl⟩ : syracuseStep 2619823 = 3929735) B3929735
theorem B21543371 : Blo 1551473 21543371 := bstep (se 1 (by rfl) ⟨16157528, by rfl⟩ : syracuseStep 21543371 = 32315057) B32315057
theorem B2619911 : Blo 1551473 2619911 := bstep (se 1 (by rfl) ⟨1964933, by rfl⟩ : syracuseStep 2619911 = 3929867) B3929867
theorem B5593625 : Blo 1551473 5593625 := bstep (se 2 (by rfl) ⟨2097609, by rfl⟩ : syracuseStep 5593625 = 4195219) B4195219
theorem B4913723 : Blo 1551473 4913723 := bstep (se 1 (by rfl) ⟨3685292, by rfl⟩ : syracuseStep 4913723 = 7370585) B7370585
theorem B2947681 : Blo 1551473 2947681 := bstep (se 2 (by rfl) ⟨1105380, by rfl⟩ : syracuseStep 2947681 = 2210761) B2210761
theorem B5593799 : Blo 1551473 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B7862993 : Blo 1551473 7862993 := bstep (se 2 (by rfl) ⟨2948622, by rfl⟩ : syracuseStep 7862993 = 5897245) B5897245
theorem B5249747 : Blo 1551473 5249747 := bstep (se 1 (by rfl) ⟨3937310, by rfl⟩ : syracuseStep 5249747 = 7874621) B7874621
theorem B3930839 : Blo 1551473 3930839 := bstep (se 1 (by rfl) ⟨2948129, by rfl⟩ : syracuseStep 3930839 = 5896259) B5896259
theorem B25533157 : Blo 1551473 25533157 := bstep (se 4 (by rfl) ⟨2393733, by rfl⟩ : syracuseStep 25533157 = 4787467) B4787467
theorem B5897033 : Blo 1551473 5897033 := bstep (se 2 (by rfl) ⟨2211387, by rfl⟩ : syracuseStep 5897033 = 4422775) B4422775
theorem B2620255 : Blo 1551473 2620255 := bstep (se 1 (by rfl) ⟨1965191, by rfl⟩ : syracuseStep 2620255 = 3930383) B3930383
theorem B2948015 : Blo 1551473 2948015 := bstep (se 1 (by rfl) ⟨2211011, by rfl⟩ : syracuseStep 2948015 = 4422023) B4422023
theorem B2620343 : Blo 1551473 2620343 := bstep (se 1 (by rfl) ⟨1965257, by rfl⟩ : syracuseStep 2620343 = 3930515) B3930515
theorem B5897231 : Blo 1551473 5897231 := bstep (se 1 (by rfl) ⟨4422923, by rfl⟩ : syracuseStep 5897231 = 8845847) B8845847
theorem B3931193 : Blo 1551473 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B5242103 : Blo 1551473 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B9952627 : Blo 1551473 9952627 := bstep (se 1 (by rfl) ⟨7464470, by rfl⟩ : syracuseStep 9952627 = 14928941) B14928941
theorem B2620937 : Blo 1551473 2620937 := bstep (se 2 (by rfl) ⟨982851, by rfl⟩ : syracuseStep 2620937 = 1965703) B1965703
theorem B5594663 : Blo 1551473 5594663 := bstep (se 1 (by rfl) ⟨4195997, by rfl⟩ : syracuseStep 5594663 = 8391995) B8391995
theorem B3317287 : Blo 1551473 3317287 := bstep (se 1 (by rfl) ⟨2487965, by rfl⟩ : syracuseStep 3317287 = 4975931) B4975931
theorem B5242427 : Blo 1551473 5242427 := bstep (se 1 (by rfl) ⟨3931820, by rfl⟩ : syracuseStep 5242427 = 7863641) B7863641
theorem B1965647 : Blo 1551473 1965647 := bstep (se 1 (by rfl) ⟨1474235, by rfl⟩ : syracuseStep 1965647 = 2948471) B2948471
theorem B2621099 : Blo 1551473 2621099 := bstep (se 1 (by rfl) ⟨1965824, by rfl⟩ : syracuseStep 2621099 = 3931649) B3931649
theorem B25509613 : Blo 1551473 25509613 := bstep (se 3 (by rfl) ⟨4783052, by rfl⟩ : syracuseStep 25509613 = 9566105) B9566105
theorem B7855865 : Blo 1551473 7855865 := bstep (se 2 (by rfl) ⟨2945949, by rfl⟩ : syracuseStep 7855865 = 5891899) B5891899
theorem B5242697 : Blo 1551473 5242697 := bstep (se 2 (by rfl) ⟨1966011, by rfl⟩ : syracuseStep 5242697 = 3932023) B3932023
theorem B3317611 : Blo 1551473 3317611 := bstep (se 1 (by rfl) ⟨2488208, by rfl⟩ : syracuseStep 3317611 = 4976417) B4976417
theorem B19890035 : Blo 1551473 19890035 := bstep (se 1 (by rfl) ⟨14917526, by rfl⟩ : syracuseStep 19890035 = 29835053) B29835053
theorem B13254587 : Blo 1551473 13254587 := bstep (se 1 (by rfl) ⟨9940940, by rfl⟩ : syracuseStep 13254587 = 19881881) B19881881
theorem B6627329 : Blo 1551473 6627329 := bstep (se 2 (by rfl) ⟨2485248, by rfl⟩ : syracuseStep 6627329 = 4970497) B4970497
theorem B3932185 : Blo 1551473 3932185 := bstep (se 2 (by rfl) ⟨1474569, by rfl⟩ : syracuseStep 3932185 = 2949139) B2949139
theorem B4251977 : Blo 1551473 4251977 := bstep (se 2 (by rfl) ⟨1594491, by rfl⟩ : syracuseStep 4251977 = 3188983) B3188983
theorem B14926481 : Blo 1551473 14926481 := bstep (se 2 (by rfl) ⟨5597430, by rfl⟩ : syracuseStep 14926481 = 11194861) B11194861
theorem B165815045 : Blo 1551473 165815045 := bstep (se 4 (by rfl) ⟨15545160, by rfl⟩ : syracuseStep 165815045 = 31090321) B31090321
theorem B4195091 : Blo 1551473 4195091 := bstep (se 1 (by rfl) ⟨3146318, by rfl⟩ : syracuseStep 4195091 = 6292637) B6292637
theorem B2327375 : Blo 1551473 2327375 := bstep (se 1 (by rfl) ⟨1745531, by rfl⟩ : syracuseStep 2327375 = 3491063) B3491063
theorem B1745743 : Blo 1551473 1745743 := bstep (se 1 (by rfl) ⟨1309307, by rfl⟩ : syracuseStep 1745743 = 2618615) B2618615
theorem B7455689 : Blo 1551473 7455689 := bstep (se 2 (by rfl) ⟨2795883, by rfl⟩ : syracuseStep 7455689 = 5591767) B5591767
theorem B6718409 : Blo 1551473 6718409 := bstep (se 2 (by rfl) ⟨2519403, by rfl⟩ : syracuseStep 6718409 = 5038807) B5038807
theorem B4850887 : Blo 1551473 4850887 := bstep (se 1 (by rfl) ⟨3638165, by rfl⟩ : syracuseStep 4850887 = 7276331) B7276331
theorem B2327771 : Blo 1551473 2327771 := bstep (se 1 (by rfl) ⟨1745828, by rfl⟩ : syracuseStep 2327771 = 3491657) B3491657
theorem B1746139 : Blo 1551473 1746139 := bstep (se 1 (by rfl) ⟨1309604, by rfl⟩ : syracuseStep 1746139 = 2619209) B2619209
theorem B6055145 : Blo 1551473 6055145 := bstep (se 2 (by rfl) ⟨2270679, by rfl⟩ : syracuseStep 6055145 = 4541359) B4541359
theorem B5596393 : Blo 1551473 5596393 := bstep (se 2 (by rfl) ⟨2098647, by rfl⟩ : syracuseStep 5596393 = 4197295) B4197295
theorem B4719865 : Blo 1551473 4719865 := bstep (se 2 (by rfl) ⟨1769949, by rfl⟩ : syracuseStep 4719865 = 3539899) B3539899
theorem B2327945 : Blo 1551473 2327945 := bstep (se 2 (by rfl) ⟨872979, by rfl⟩ : syracuseStep 2327945 = 1745959) B1745959
theorem B1746427 : Blo 1551473 1746427 := bstep (se 1 (by rfl) ⟨1309820, by rfl⟩ : syracuseStep 1746427 = 2619641) B2619641
theorem B3491423 : Blo 1551473 3491423 := bstep (se 1 (by rfl) ⟨2618567, by rfl⟩ : syracuseStep 3491423 = 5237135) B5237135
theorem B14362247 : Blo 1551473 14362247 := bstep (se 1 (by rfl) ⟨10771685, by rfl⟩ : syracuseStep 14362247 = 21543371) B21543371
theorem B1746607 : Blo 1551473 1746607 := bstep (se 1 (by rfl) ⟨1309955, by rfl⟩ : syracuseStep 1746607 = 2619911) B2619911
theorem B3729083 : Blo 1551473 3729083 := bstep (se 1 (by rfl) ⟨2796812, by rfl⟩ : syracuseStep 3729083 = 5593625) B5593625
theorem B2328299 : Blo 1551473 2328299 := bstep (se 1 (by rfl) ⟨1746224, by rfl⟩ : syracuseStep 2328299 = 3492449) B3492449
theorem B3983083 : Blo 1551473 3983083 := bstep (se 1 (by rfl) ⟨2987312, by rfl⟩ : syracuseStep 3983083 = 5974625) B5974625
theorem B3491639 : Blo 1551473 3491639 := bstep (se 1 (by rfl) ⟨2618729, by rfl⟩ : syracuseStep 3491639 = 5237459) B5237459
theorem B3499831 : Blo 1551473 3499831 := bstep (se 1 (by rfl) ⟨2624873, by rfl⟩ : syracuseStep 3499831 = 5249747) B5249747
theorem B3729257 : Blo 1551473 3729257 := bstep (se 2 (by rfl) ⟨1398471, by rfl⟩ : syracuseStep 3729257 = 2796943) B2796943
theorem B16779143 : Blo 1551473 16779143 := bstep (se 1 (by rfl) ⟨12584357, by rfl⟩ : syracuseStep 16779143 = 25168715) B25168715
theorem B2328527 : Blo 1551473 2328527 := bstep (se 1 (by rfl) ⟨1746395, by rfl⟩ : syracuseStep 2328527 = 3492791) B3492791
theorem B1746895 : Blo 1551473 1746895 := bstep (se 1 (by rfl) ⟨1310171, by rfl⟩ : syracuseStep 1746895 = 2620343) B2620343
theorem B3491945 : Blo 1551473 3491945 := bstep (se 2 (by rfl) ⟨1309479, by rfl⟩ : syracuseStep 3491945 = 2618959) B2618959
theorem B5236865 : Blo 1551473 5236865 := bstep (se 2 (by rfl) ⟨1963824, by rfl⟩ : syracuseStep 5236865 = 3927649) B3927649
theorem B39799025 : Blo 1551473 39799025 := bstep (se 2 (by rfl) ⟨14924634, by rfl⟩ : syracuseStep 39799025 = 29849269) B29849269
theorem B7858457 : Blo 1551473 7858457 := bstep (se 2 (by rfl) ⟨2946921, by rfl⟩ : syracuseStep 7858457 = 5893843) B5893843
theorem B2328923 : Blo 1551473 2328923 := bstep (se 1 (by rfl) ⟨1746692, by rfl⟩ : syracuseStep 2328923 = 3493385) B3493385
theorem B1747291 : Blo 1551473 1747291 := bstep (se 1 (by rfl) ⟨1310468, by rfl⟩ : syracuseStep 1747291 = 2620937) B2620937
theorem B3729775 : Blo 1551473 3729775 := bstep (se 1 (by rfl) ⟨2797331, by rfl⟩ : syracuseStep 3729775 = 5594663) B5594663
theorem B1747399 : Blo 1551473 1747399 := bstep (se 1 (by rfl) ⟨1310549, by rfl⟩ : syracuseStep 1747399 = 2621099) B2621099
theorem B4196819 : Blo 1551473 4196819 := bstep (se 1 (by rfl) ⟨3147614, by rfl⟩ : syracuseStep 4196819 = 6295229) B6295229
theorem B5237243 : Blo 1551473 5237243 := bstep (se 1 (by rfl) ⟨3927932, by rfl⟩ : syracuseStep 5237243 = 7855865) B7855865
theorem B2329151 : Blo 1551473 2329151 := bstep (se 1 (by rfl) ⟨1746863, by rfl⟩ : syracuseStep 2329151 = 3493727) B3493727
theorem B3492431 : Blo 1551473 3492431 := bstep (se 1 (by rfl) ⟨2619323, by rfl⟩ : syracuseStep 3492431 = 5238647) B5238647
theorem B2329271 : Blo 1551473 2329271 := bstep (se 1 (by rfl) ⟨1746953, by rfl⟩ : syracuseStep 2329271 = 3493907) B3493907
theorem B3492575 : Blo 1551473 3492575 := bstep (se 1 (by rfl) ⟨2619431, by rfl⟩ : syracuseStep 3492575 = 5238863) B5238863
theorem B4418459 : Blo 1551473 4418459 := bstep (se 1 (by rfl) ⟨3313844, by rfl⟩ : syracuseStep 4418459 = 6627689) B6627689
theorem B2329499 : Blo 1551473 2329499 := bstep (se 1 (by rfl) ⟨1747124, by rfl⟩ : syracuseStep 2329499 = 3494249) B3494249
theorem B5237675 : Blo 1551473 5237675 := bstep (se 1 (by rfl) ⟨3928256, by rfl⟩ : syracuseStep 5237675 = 7856513) B7856513
theorem B3492827 : Blo 1551473 3492827 := bstep (se 1 (by rfl) ⟨2619620, by rfl⟩ : syracuseStep 3492827 = 5239241) B5239241
theorem B3493007 : Blo 1551473 3493007 := bstep (se 1 (by rfl) ⟨2619755, by rfl⟩ : syracuseStep 3493007 = 5239511) B5239511
theorem B8391869 : Blo 1551473 8391869 := bstep (se 3 (by rfl) ⟨1573475, by rfl⟩ : syracuseStep 8391869 = 3146951) B3146951
theorem B3493097 : Blo 1551473 3493097 := bstep (se 2 (by rfl) ⟨1309911, by rfl⟩ : syracuseStep 3493097 = 2619823) B2619823
theorem B1551647 : Blo 1551473 1551647 := bstep (se 1 (by rfl) ⟨1163735, by rfl⟩ : syracuseStep 1551647 = 2327471) B2327471
theorem B3493151 : Blo 1551473 3493151 := bstep (se 1 (by rfl) ⟨2619863, by rfl⟩ : syracuseStep 3493151 = 5239727) B5239727
theorem B2329895 : Blo 1551473 2329895 := bstep (se 1 (by rfl) ⟨1747421, by rfl⟩ : syracuseStep 2329895 = 3494843) B3494843
theorem B1551707 : Blo 1551473 1551707 := bstep (se 1 (by rfl) ⟨1163780, by rfl⟩ : syracuseStep 1551707 = 2327561) B2327561
theorem B1551727 : Blo 1551473 1551727 := bstep (se 1 (by rfl) ⟨1163795, by rfl⟩ : syracuseStep 1551727 = 2327591) B2327591
theorem B2329979 : Blo 1551473 2329979 := bstep (se 1 (by rfl) ⟨1747484, by rfl⟩ : syracuseStep 2329979 = 3494969) B3494969
theorem B1551783 : Blo 1551473 1551783 := bstep (se 1 (by rfl) ⟨1163837, by rfl⟩ : syracuseStep 1551783 = 2327675) B2327675
theorem B5238215 : Blo 1551473 5238215 := bstep (se 1 (by rfl) ⟨3928661, by rfl⟩ : syracuseStep 5238215 = 7857323) B7857323
theorem B2330105 : Blo 1551473 2330105 := bstep (se 2 (by rfl) ⟨873789, by rfl⟩ : syracuseStep 2330105 = 1747579) B1747579
theorem B1551867 : Blo 1551473 1551867 := bstep (se 1 (by rfl) ⟨1163900, by rfl⟩ : syracuseStep 1551867 = 2327801) B2327801
theorem B1551935 : Blo 1551473 1551935 := bstep (se 1 (by rfl) ⟨1163951, by rfl⟩ : syracuseStep 1551935 = 2327903) B2327903
theorem B1551943 : Blo 1551473 1551943 := bstep (se 1 (by rfl) ⟨1163957, by rfl⟩ : syracuseStep 1551943 = 2327915) B2327915
theorem B2330207 : Blo 1551473 2330207 := bstep (se 1 (by rfl) ⟨1747655, by rfl⟩ : syracuseStep 2330207 = 3495311) B3495311
theorem B6631121 : Blo 1551473 6631121 := bstep (se 2 (by rfl) ⟨2486670, by rfl⟩ : syracuseStep 6631121 = 4973341) B4973341
theorem B1552095 : Blo 1551473 1552095 := bstep (se 1 (by rfl) ⟨1164071, by rfl⟩ : syracuseStep 1552095 = 2328143) B2328143
theorem B4419335 : Blo 1551473 4419335 := bstep (se 1 (by rfl) ⟨3314501, by rfl⟩ : syracuseStep 4419335 = 6629003) B6629003
theorem B5238539 : Blo 1551473 5238539 := bstep (se 1 (by rfl) ⟨3928904, by rfl⟩ : syracuseStep 5238539 = 7857809) B7857809
theorem B3493673 : Blo 1551473 3493673 := bstep (se 2 (by rfl) ⟨1310127, by rfl⟩ : syracuseStep 3493673 = 2620255) B2620255
theorem B1552175 : Blo 1551473 1552175 := bstep (se 1 (by rfl) ⟨1164131, by rfl⟩ : syracuseStep 1552175 = 2328263) B2328263
theorem B3362615 : Blo 1551473 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B1552283 : Blo 1551473 1552283 := bstep (se 1 (by rfl) ⟨1164212, by rfl⟩ : syracuseStep 1552283 = 2328425) B2328425
theorem B1552335 : Blo 1551473 1552335 := bstep (se 1 (by rfl) ⟨1164251, by rfl⟩ : syracuseStep 1552335 = 2328503) B2328503
theorem B1552359 : Blo 1551473 1552359 := bstep (se 1 (by rfl) ⟨1164269, by rfl⟩ : syracuseStep 1552359 = 2328539) B2328539
theorem B5238809 : Blo 1551473 5238809 := bstep (se 2 (by rfl) ⟨1964553, by rfl⟩ : syracuseStep 5238809 = 3929107) B3929107
theorem B7966745 : Blo 1551473 7966745 := bstep (se 2 (by rfl) ⟨2987529, by rfl⟩ : syracuseStep 7966745 = 5975059) B5975059
theorem B25178201 : Blo 1551473 25178201 := bstep (se 2 (by rfl) ⟨9441825, by rfl⟩ : syracuseStep 25178201 = 18883651) B18883651
theorem B4370537 : Blo 1551473 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B1552671 : Blo 1551473 1552671 := bstep (se 1 (by rfl) ⟨1164503, by rfl⟩ : syracuseStep 1552671 = 2329007) B2329007
theorem B1552731 : Blo 1551473 1552731 := bstep (se 1 (by rfl) ⟨1164548, by rfl⟩ : syracuseStep 1552731 = 2329097) B2329097
theorem B47804779 : Blo 1551473 47804779 := bstep (se 1 (by rfl) ⟨35853584, by rfl⟩ : syracuseStep 47804779 = 71707169) B71707169
theorem B1552751 : Blo 1551473 1552751 := bstep (se 1 (by rfl) ⟨1164563, by rfl⟩ : syracuseStep 1552751 = 2329127) B2329127
theorem B1552807 : Blo 1551473 1552807 := bstep (se 1 (by rfl) ⟨1164605, by rfl⟩ : syracuseStep 1552807 = 2329211) B2329211
theorem B3928571 : Blo 1551473 3928571 := bstep (se 1 (by rfl) ⟨2946428, by rfl⟩ : syracuseStep 3928571 = 5892857) B5892857
theorem B1552891 : Blo 1551473 1552891 := bstep (se 1 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 1552891 = 2329337) B2329337
theorem B7082497 : Blo 1551473 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B9941555 : Blo 1551473 9941555 := bstep (se 1 (by rfl) ⟨7456166, by rfl⟩ : syracuseStep 9941555 = 14912333) B14912333
theorem B1552959 : Blo 1551473 1552959 := bstep (se 1 (by rfl) ⟨1164719, by rfl⟩ : syracuseStep 1552959 = 2329439) B2329439
theorem B1552967 : Blo 1551473 1552967 := bstep (se 1 (by rfl) ⟨1164725, by rfl⟩ : syracuseStep 1552967 = 2329451) B2329451
theorem B3314297 : Blo 1551473 3314297 := bstep (se 2 (by rfl) ⟨1242861, by rfl⟩ : syracuseStep 3314297 = 2485723) B2485723
theorem B107492021 : Blo 1551473 107492021 := bstep (se 5 (by rfl) ⟨5038688, by rfl⟩ : syracuseStep 107492021 = 10077377) B10077377
theorem B1553119 : Blo 1551473 1553119 := bstep (se 1 (by rfl) ⟨1164839, by rfl⟩ : syracuseStep 1553119 = 2329679) B2329679
theorem B1553199 : Blo 1551473 1553199 := bstep (se 1 (by rfl) ⟨1164899, by rfl⟩ : syracuseStep 1553199 = 2329799) B2329799
theorem B3494735 : Blo 1551473 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B1553307 : Blo 1551473 1553307 := bstep (se 1 (by rfl) ⟨1164980, by rfl⟩ : syracuseStep 1553307 = 2329961) B2329961
theorem B6632387 : Blo 1551473 6632387 := bstep (se 1 (by rfl) ⟨4974290, by rfl⟩ : syracuseStep 6632387 = 9948581) B9948581
theorem B1553359 : Blo 1551473 1553359 := bstep (se 1 (by rfl) ⟨1165019, by rfl⟩ : syracuseStep 1553359 = 2330039) B2330039
theorem B7861211 : Blo 1551473 7861211 := bstep (se 1 (by rfl) ⟨5895908, by rfl⟩ : syracuseStep 7861211 = 11791817) B11791817
theorem B1553383 : Blo 1551473 1553383 := bstep (se 1 (by rfl) ⟨1165037, by rfl⟩ : syracuseStep 1553383 = 2330075) B2330075
theorem B3494951 : Blo 1551473 3494951 := bstep (se 1 (by rfl) ⟨2621213, by rfl⟩ : syracuseStep 3494951 = 5242427) B5242427
theorem B7861373 : Blo 1551473 7861373 := bstep (se 3 (by rfl) ⟨1474007, by rfl⟩ : syracuseStep 7861373 = 2948015) B2948015
theorem B3495131 : Blo 1551473 3495131 := bstep (se 1 (by rfl) ⟨2621348, by rfl⟩ : syracuseStep 3495131 = 5242697) B5242697
theorem B5240051 : Blo 1551473 5240051 := bstep (se 1 (by rfl) ⟨3930038, by rfl⟩ : syracuseStep 5240051 = 7860077) B7860077
theorem B13260023 : Blo 1551473 13260023 := bstep (se 1 (by rfl) ⟨9945017, by rfl⟩ : syracuseStep 13260023 = 19890035) B19890035
theorem B8836391 : Blo 1551473 8836391 := bstep (se 1 (by rfl) ⟨6627293, by rfl⟩ : syracuseStep 8836391 = 13254587) B13254587
theorem B9442655 : Blo 1551473 9442655 := bstep (se 1 (by rfl) ⟨7081991, by rfl⟩ : syracuseStep 9442655 = 14163983) B14163983
theorem B5240159 : Blo 1551473 5240159 := bstep (se 1 (by rfl) ⟨3930119, by rfl⟩ : syracuseStep 5240159 = 7860239) B7860239
theorem B29824361 : Blo 1551473 29824361 := bstep (se 2 (by rfl) ⟨11184135, by rfl⟩ : syracuseStep 29824361 = 22368271) B22368271
theorem B7566781 : Blo 1551473 7566781 := bstep (se 3 (by rfl) ⟨1418771, by rfl⟩ : syracuseStep 7566781 = 2837543) B2837543
theorem B7861697 : Blo 1551473 7861697 := bstep (se 2 (by rfl) ⟨2948136, by rfl⟩ : syracuseStep 7861697 = 5896273) B5896273
theorem B3315143 : Blo 1551473 3315143 := bstep (se 1 (by rfl) ⟨2486357, by rfl⟩ : syracuseStep 3315143 = 4972715) B4972715
theorem B3929543 : Blo 1551473 3929543 := bstep (se 1 (by rfl) ⟨2947157, by rfl⟩ : syracuseStep 3929543 = 5894315) B5894315
theorem B22394333 : Blo 1551473 22394333 := bstep (se 3 (by rfl) ⟨4198937, by rfl⟩ : syracuseStep 22394333 = 8397875) B8397875
theorem B3929593 : Blo 1551473 3929593 := bstep (se 2 (by rfl) ⟨1473597, by rfl⟩ : syracuseStep 3929593 = 2947195) B2947195
theorem B20158085 : Blo 1551473 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B1963703 : Blo 1551473 1963703 := bstep (se 1 (by rfl) ⟨1472777, by rfl⟩ : syracuseStep 1963703 = 2945555) B2945555
theorem B2619067 : Blo 1551473 2619067 := bstep (se 1 (by rfl) ⟨1964300, by rfl⟩ : syracuseStep 2619067 = 3928601) B3928601
theorem B35829485 : Blo 1551473 35829485 := bstep (se 3 (by rfl) ⟨6718028, by rfl⟩ : syracuseStep 35829485 = 13436057) B13436057
theorem B68966149 : Blo 1551473 68966149 := bstep (se 4 (by rfl) ⟨6465576, by rfl⟩ : syracuseStep 68966149 = 12931153) B12931153
theorem B3929897 : Blo 1551473 3929897 := bstep (se 2 (by rfl) ⟨1473711, by rfl⟩ : syracuseStep 3929897 = 2947423) B2947423
theorem B1963855 : Blo 1551473 1963855 := bstep (se 1 (by rfl) ⟨1472891, by rfl⟩ : syracuseStep 1963855 = 2945783) B2945783
theorem B3930241 : Blo 1551473 3930241 := bstep (se 2 (by rfl) ⟨1473840, by rfl⟩ : syracuseStep 3930241 = 2947681) B2947681
theorem B34044209 : Blo 1551473 34044209 := bstep (se 2 (by rfl) ⟨12766578, by rfl⟩ : syracuseStep 34044209 = 25533157) B25533157
theorem B6633839 : Blo 1551473 6633839 := bstep (se 1 (by rfl) ⟨4975379, by rfl⟩ : syracuseStep 6633839 = 9950759) B9950759
theorem B4422251 : Blo 1551473 4422251 := bstep (se 1 (by rfl) ⟨3316688, by rfl⟩ : syracuseStep 4422251 = 6633377) B6633377
theorem B7854731 : Blo 1551473 7854731 := bstep (se 1 (by rfl) ⟨5891048, by rfl⟩ : syracuseStep 7854731 = 11782097) B11782097
theorem B14924483 : Blo 1551473 14924483 := bstep (se 1 (by rfl) ⟨11193362, by rfl⟩ : syracuseStep 14924483 = 22386725) B22386725
theorem B2620127 : Blo 1551473 2620127 := bstep (se 1 (by rfl) ⟨1965095, by rfl⟩ : syracuseStep 2620127 = 3930191) B3930191
theorem B11795219 : Blo 1551473 11795219 := bstep (se 1 (by rfl) ⟨8846414, by rfl⟩ : syracuseStep 11795219 = 17692829) B17692829
theorem B5241725 : Blo 1551473 5241725 := bstep (se 3 (by rfl) ⟨982823, by rfl⟩ : syracuseStep 5241725 = 1965647) B1965647
theorem B8838031 : Blo 1551473 8838031 := bstep (se 1 (by rfl) ⟨6628523, by rfl⟩ : syracuseStep 8838031 = 13257047) B13257047
theorem B21535631 : Blo 1551473 21535631 := bstep (se 1 (by rfl) ⟨16151723, by rfl⟩ : syracuseStep 21535631 = 32303447) B32303447
theorem B6298523 : Blo 1551473 6298523 := bstep (se 1 (by rfl) ⟨4723892, by rfl⟩ : syracuseStep 6298523 = 9447785) B9447785
theorem B3931051 : Blo 1551473 3931051 := bstep (se 1 (by rfl) ⟨2948288, by rfl⟩ : syracuseStep 3931051 = 5896577) B5896577
theorem B3275815 : Blo 1551473 3275815 := bstep (se 1 (by rfl) ⟨2456861, by rfl⟩ : syracuseStep 3275815 = 4913723) B4913723
theorem B5241995 : Blo 1551473 5241995 := bstep (se 1 (by rfl) ⟨3931496, by rfl⟩ : syracuseStep 5241995 = 7862993) B7862993
theorem B2620559 : Blo 1551473 2620559 := bstep (se 1 (by rfl) ⟨1965419, by rfl⟩ : syracuseStep 2620559 = 3930839) B3930839
theorem B13270169 : Blo 1551473 13270169 := bstep (se 2 (by rfl) ⟨4976313, by rfl⟩ : syracuseStep 13270169 = 9952627) B9952627
theorem B14916797 : Blo 1551473 14916797 := bstep (se 3 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 14916797 = 5593799) B5593799
theorem B3931355 : Blo 1551473 3931355 := bstep (se 1 (by rfl) ⟨2948516, by rfl⟩ : syracuseStep 3931355 = 5897033) B5897033
theorem B15129821 : Blo 1551473 15129821 := bstep (se 3 (by rfl) ⟨2836841, by rfl⟩ : syracuseStep 15129821 = 5673683) B5673683
theorem B7462205 : Blo 1551473 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B3931487 : Blo 1551473 3931487 := bstep (se 1 (by rfl) ⟨2948615, by rfl⟩ : syracuseStep 3931487 = 5897231) B5897231
theorem B2620795 : Blo 1551473 2620795 := bstep (se 1 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 2620795 = 3931193) B3931193
theorem B4423049 : Blo 1551473 4423049 := bstep (se 2 (by rfl) ⟨1658643, by rfl⟩ : syracuseStep 4423049 = 3317287) B3317287
theorem B34012817 : Blo 1551473 34012817 := bstep (se 2 (by rfl) ⟨12754806, by rfl⟩ : syracuseStep 34012817 = 25509613) B25509613
theorem B4423481 : Blo 1551473 4423481 := bstep (se 2 (by rfl) ⟨1658805, by rfl⟩ : syracuseStep 4423481 = 3317611) B3317611
theorem B7462763 : Blo 1551473 7462763 := bstep (se 1 (by rfl) ⟨5597072, by rfl⟩ : syracuseStep 7462763 = 11194145) B11194145
theorem B37773317 : Blo 1551473 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B5242913 : Blo 1551473 5242913 := bstep (se 2 (by rfl) ⟨1966092, by rfl⟩ : syracuseStep 5242913 = 3932185) B3932185
theorem B16785467 : Blo 1551473 16785467 := bstep (se 1 (by rfl) ⟨12589100, by rfl⟩ : syracuseStep 16785467 = 25178201) B25178201
theorem B2834651 : Blo 1551473 2834651 := bstep (se 1 (by rfl) ⟨2125988, by rfl⟩ : syracuseStep 2834651 = 4251977) B4251977
theorem B4973033 : Blo 1551473 4973033 := bstep (se 2 (by rfl) ⟨1864887, by rfl⟩ : syracuseStep 4973033 = 3729775) B3729775
theorem B110543363 : Blo 1551473 110543363 := bstep (se 1 (by rfl) ⟨82907522, by rfl⟩ : syracuseStep 110543363 = 165815045) B165815045
theorem B8840015 : Blo 1551473 8840015 := bstep (se 1 (by rfl) ⟨6630011, by rfl⟩ : syracuseStep 8840015 = 13260023) B13260023
theorem B5890927 : Blo 1551473 5890927 := bstep (se 1 (by rfl) ⟨4418195, by rfl⟩ : syracuseStep 5890927 = 8836391) B8836391
theorem B19882907 : Blo 1551473 19882907 := bstep (se 1 (by rfl) ⟨14912180, by rfl⟩ : syracuseStep 19882907 = 29824361) B29824361
theorem B2327615 : Blo 1551473 2327615 := bstep (se 1 (by rfl) ⟨1745711, by rfl⟩ : syracuseStep 2327615 = 3491423) B3491423
theorem B2327657 : Blo 1551473 2327657 := bstep (se 2 (by rfl) ⟨872871, by rfl⟩ : syracuseStep 2327657 = 1745743) B1745743
theorem B2327759 : Blo 1551473 2327759 := bstep (se 1 (by rfl) ⟨1745819, by rfl⟩ : syracuseStep 2327759 = 3491639) B3491639
theorem B11191517 : Blo 1551473 11191517 := bstep (se 3 (by rfl) ⟨2098409, by rfl⟩ : syracuseStep 11191517 = 4196819) B4196819
theorem B21243109 : Blo 1551473 21243109 := bstep (se 4 (by rfl) ⟨1991541, by rfl⟩ : syracuseStep 21243109 = 3983083) B3983083
theorem B4367753 : Blo 1551473 4367753 := bstep (se 2 (by rfl) ⟨1637907, by rfl⟩ : syracuseStep 4367753 = 3275815) B3275815
theorem B2327963 : Blo 1551473 2327963 := bstep (se 1 (by rfl) ⟨1745972, by rfl⟩ : syracuseStep 2327963 = 3491945) B3491945
theorem B3491243 : Blo 1551473 3491243 := bstep (se 1 (by rfl) ⟨2618432, by rfl⟩ : syracuseStep 3491243 = 5236865) B5236865
theorem B26510813 : Blo 1551473 26510813 := bstep (se 3 (by rfl) ⟨4970777, by rfl⟩ : syracuseStep 26510813 = 9941555) B9941555
theorem B2328185 : Blo 1551473 2328185 := bstep (se 2 (by rfl) ⟨873069, by rfl⟩ : syracuseStep 2328185 = 1746139) B1746139
theorem B6293153 : Blo 1551473 6293153 := bstep (se 2 (by rfl) ⟨2359932, by rfl⟩ : syracuseStep 6293153 = 4719865) B4719865
theorem B3491495 : Blo 1551473 3491495 := bstep (se 1 (by rfl) ⟨2618621, by rfl⟩ : syracuseStep 3491495 = 5237243) B5237243
theorem B38299325 : Blo 1551473 38299325 := bstep (se 3 (by rfl) ⟨7181123, by rfl⟩ : syracuseStep 38299325 = 14362247) B14362247
theorem B2328287 : Blo 1551473 2328287 := bstep (se 1 (by rfl) ⟨1746215, by rfl⟩ : syracuseStep 2328287 = 3492431) B3492431
theorem B5236487 : Blo 1551473 5236487 := bstep (se 1 (by rfl) ⟨3927365, by rfl⟩ : syracuseStep 5236487 = 7854731) B7854731
theorem B5236541 : Blo 1551473 5236541 := bstep (se 3 (by rfl) ⟨981851, by rfl⟩ : syracuseStep 5236541 = 1963703) B1963703
theorem B2328383 : Blo 1551473 2328383 := bstep (se 1 (by rfl) ⟨1746287, by rfl⟩ : syracuseStep 2328383 = 3492575) B3492575
theorem B1746751 : Blo 1551473 1746751 := bstep (se 1 (by rfl) ⟨1310063, by rfl⟩ : syracuseStep 1746751 = 2620127) B2620127
theorem B3491783 : Blo 1551473 3491783 := bstep (se 1 (by rfl) ⟨2618837, by rfl⟩ : syracuseStep 3491783 = 5237675) B5237675
theorem B2328551 : Blo 1551473 2328551 := bstep (se 1 (by rfl) ⟨1746413, by rfl⟩ : syracuseStep 2328551 = 3492827) B3492827
theorem B2328569 : Blo 1551473 2328569 := bstep (se 2 (by rfl) ⟨873213, by rfl⟩ : syracuseStep 2328569 = 1746427) B1746427
theorem B2328671 : Blo 1551473 2328671 := bstep (se 1 (by rfl) ⟨1746503, by rfl⟩ : syracuseStep 2328671 = 3493007) B3493007
theorem B1747039 : Blo 1551473 1747039 := bstep (se 1 (by rfl) ⟨1310279, by rfl⟩ : syracuseStep 1747039 = 2620559) B2620559
theorem B10086547 : Blo 1551473 10086547 := bstep (se 1 (by rfl) ⟨7564910, by rfl⟩ : syracuseStep 10086547 = 15129821) B15129821
theorem B2328731 : Blo 1551473 2328731 := bstep (se 1 (by rfl) ⟨1746548, by rfl⟩ : syracuseStep 2328731 = 3493097) B3493097
theorem B2328767 : Blo 1551473 2328767 := bstep (se 1 (by rfl) ⟨1746575, by rfl⟩ : syracuseStep 2328767 = 3493151) B3493151
theorem B4974803 : Blo 1551473 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B2328809 : Blo 1551473 2328809 := bstep (se 2 (by rfl) ⟨873303, by rfl⟩ : syracuseStep 2328809 = 1746607) B1746607
theorem B3492089 : Blo 1551473 3492089 := bstep (se 2 (by rfl) ⟨1309533, by rfl⟩ : syracuseStep 3492089 = 2619067) B2619067
theorem B3492143 : Blo 1551473 3492143 := bstep (se 1 (by rfl) ⟨2619107, by rfl⟩ : syracuseStep 3492143 = 5238215) B5238215
theorem B3492359 : Blo 1551473 3492359 := bstep (se 1 (by rfl) ⟨2619269, by rfl⟩ : syracuseStep 3492359 = 5238539) B5238539
theorem B2329115 : Blo 1551473 2329115 := bstep (se 1 (by rfl) ⟨1746836, by rfl⟩ : syracuseStep 2329115 = 3493673) B3493673
theorem B4975175 : Blo 1551473 4975175 := bstep (se 1 (by rfl) ⟨3731381, by rfl⟩ : syracuseStep 4975175 = 7462763) B7462763
theorem B2329193 : Blo 1551473 2329193 := bstep (se 2 (by rfl) ⟨873447, by rfl⟩ : syracuseStep 2329193 = 1746895) B1746895
theorem B4418219 : Blo 1551473 4418219 := bstep (se 1 (by rfl) ⟨3313664, by rfl⟩ : syracuseStep 4418219 = 6627329) B6627329
theorem B3492539 : Blo 1551473 3492539 := bstep (se 1 (by rfl) ⟨2619404, by rfl⟩ : syracuseStep 3492539 = 5238809) B5238809
theorem B5311163 : Blo 1551473 5311163 := bstep (se 1 (by rfl) ⟨3983372, by rfl⟩ : syracuseStep 5311163 = 7966745) B7966745
theorem B2329721 : Blo 1551473 2329721 := bstep (se 2 (by rfl) ⟨873645, by rfl⟩ : syracuseStep 2329721 = 1747291) B1747291
theorem B2796727 : Blo 1551473 2796727 := bstep (se 1 (by rfl) ⟨2097545, by rfl⟩ : syracuseStep 2796727 = 4195091) B4195091
theorem B1551583 : Blo 1551473 1551583 := bstep (se 1 (by rfl) ⟨1163687, by rfl⟩ : syracuseStep 1551583 = 2327375) B2327375
theorem B2329823 : Blo 1551473 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B2329865 : Blo 1551473 2329865 := bstep (se 2 (by rfl) ⟨873699, by rfl⟩ : syracuseStep 2329865 = 1747399) B1747399
theorem B2329967 : Blo 1551473 2329967 := bstep (se 1 (by rfl) ⟨1747475, by rfl⟩ : syracuseStep 2329967 = 3494951) B3494951
theorem B1551847 : Blo 1551473 1551847 := bstep (se 1 (by rfl) ⟨1163885, by rfl⟩ : syracuseStep 1551847 = 2327771) B2327771
theorem B2330087 : Blo 1551473 2330087 := bstep (se 1 (by rfl) ⟨1747565, by rfl⟩ : syracuseStep 2330087 = 3495131) B3495131
theorem B3493367 : Blo 1551473 3493367 := bstep (se 1 (by rfl) ⟨2620025, by rfl⟩ : syracuseStep 3493367 = 5240051) B5240051
theorem B6295103 : Blo 1551473 6295103 := bstep (se 1 (by rfl) ⟨4721327, by rfl⟩ : syracuseStep 6295103 = 9442655) B9442655
theorem B3493439 : Blo 1551473 3493439 := bstep (se 1 (by rfl) ⟨2620079, by rfl⟩ : syracuseStep 3493439 = 5240159) B5240159
theorem B1551963 : Blo 1551473 1551963 := bstep (se 1 (by rfl) ⟨1163972, by rfl⟩ : syracuseStep 1551963 = 2327945) B2327945
theorem B13438723 : Blo 1551473 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B1552199 : Blo 1551473 1552199 := bstep (se 1 (by rfl) ⟨1164149, by rfl⟩ : syracuseStep 1552199 = 2328299) B2328299
theorem B11784041 : Blo 1551473 11784041 := bstep (se 2 (by rfl) ⟨4419015, by rfl⟩ : syracuseStep 11784041 = 8838031) B8838031
theorem B2486171 : Blo 1551473 2486171 := bstep (se 1 (by rfl) ⟨1864628, by rfl⟩ : syracuseStep 2486171 = 3729257) B3729257
theorem B11186095 : Blo 1551473 11186095 := bstep (se 1 (by rfl) ⟨8389571, by rfl⟩ : syracuseStep 11186095 = 16779143) B16779143
theorem B1552351 : Blo 1551473 1552351 := bstep (se 1 (by rfl) ⟨1164263, by rfl⟩ : syracuseStep 1552351 = 2328527) B2328527
theorem B5238971 : Blo 1551473 5238971 := bstep (se 1 (by rfl) ⟨3929228, by rfl⟩ : syracuseStep 5238971 = 7858457) B7858457
theorem B22696139 : Blo 1551473 22696139 := bstep (se 1 (by rfl) ⟨17022104, by rfl⟩ : syracuseStep 22696139 = 34044209) B34044209
theorem B1552615 : Blo 1551473 1552615 := bstep (se 1 (by rfl) ⟨1164461, by rfl⟩ : syracuseStep 1552615 = 2328923) B2328923
theorem B6467849 : Blo 1551473 6467849 := bstep (se 2 (by rfl) ⟨2425443, by rfl⟩ : syracuseStep 6467849 = 4850887) B4850887
theorem B18665765 : Blo 1551473 18665765 := bstep (se 4 (by rfl) ⟨1749915, by rfl⟩ : syracuseStep 18665765 = 3499831) B3499831
theorem B1552767 : Blo 1551473 1552767 := bstep (se 1 (by rfl) ⟨1164575, by rfl⟩ : syracuseStep 1552767 = 2329151) B2329151
theorem B1552847 : Blo 1551473 1552847 := bstep (se 1 (by rfl) ⟨1164635, by rfl⟩ : syracuseStep 1552847 = 2329271) B2329271
theorem B9949655 : Blo 1551473 9949655 := bstep (se 1 (by rfl) ⟨7462241, by rfl⟩ : syracuseStep 9949655 = 14924483) B14924483
theorem B3494393 : Blo 1551473 3494393 := bstep (se 2 (by rfl) ⟨1310397, by rfl⟩ : syracuseStep 3494393 = 2620795) B2620795
theorem B10089041 : Blo 1551473 10089041 := bstep (se 2 (by rfl) ⟨3783390, by rfl⟩ : syracuseStep 10089041 = 7566781) B7566781
theorem B3494483 : Blo 1551473 3494483 := bstep (se 1 (by rfl) ⟨2620862, by rfl⟩ : syracuseStep 3494483 = 5241725) B5241725
theorem B14357087 : Blo 1551473 14357087 := bstep (se 1 (by rfl) ⟨10767815, by rfl⟩ : syracuseStep 14357087 = 21535631) B21535631
theorem B2945639 : Blo 1551473 2945639 := bstep (se 1 (by rfl) ⟨2209229, by rfl⟩ : syracuseStep 2945639 = 4418459) B4418459
theorem B1552999 : Blo 1551473 1552999 := bstep (se 1 (by rfl) ⟨1164749, by rfl⟩ : syracuseStep 1552999 = 2329499) B2329499
theorem B4199015 : Blo 1551473 4199015 := bstep (se 1 (by rfl) ⟨3149261, by rfl⟩ : syracuseStep 4199015 = 6298523) B6298523
theorem B5239457 : Blo 1551473 5239457 := bstep (se 2 (by rfl) ⟨1964796, by rfl⟩ : syracuseStep 5239457 = 3929593) B3929593
theorem B3494663 : Blo 1551473 3494663 := bstep (se 1 (by rfl) ⟨2620997, by rfl⟩ : syracuseStep 3494663 = 5241995) B5241995
theorem B1553263 : Blo 1551473 1553263 := bstep (se 1 (by rfl) ⟨1164947, by rfl⟩ : syracuseStep 1553263 = 2329895) B2329895
theorem B1553319 : Blo 1551473 1553319 := bstep (se 1 (by rfl) ⟨1164989, by rfl⟩ : syracuseStep 1553319 = 2329979) B2329979
theorem B143471573 : Blo 1551473 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B1553403 : Blo 1551473 1553403 := bstep (se 1 (by rfl) ⟨1165052, by rfl⟩ : syracuseStep 1553403 = 2330105) B2330105
theorem B1553471 : Blo 1551473 1553471 := bstep (se 1 (by rfl) ⟨1165103, by rfl⟩ : syracuseStep 1553471 = 2330207) B2330207
theorem B2618473 : Blo 1551473 2618473 := bstep (se 2 (by rfl) ⟨981927, by rfl⟩ : syracuseStep 2618473 = 1963855) B1963855
theorem B4420747 : Blo 1551473 4420747 := bstep (se 1 (by rfl) ⟨3315560, by rfl⟩ : syracuseStep 4420747 = 6631121) B6631121
theorem B2946223 : Blo 1551473 2946223 := bstep (se 1 (by rfl) ⟨2209667, by rfl⟩ : syracuseStep 2946223 = 4419335) B4419335
theorem B5240321 : Blo 1551473 5240321 := bstep (se 2 (by rfl) ⟨1965120, by rfl⟩ : syracuseStep 5240321 = 3930241) B3930241
theorem B11654765 : Blo 1551473 11654765 := bstep (se 3 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 11654765 = 4370537) B4370537
theorem B2619047 : Blo 1551473 2619047 := bstep (se 1 (by rfl) ⟨1964285, by rfl⟩ : syracuseStep 2619047 = 3928571) B3928571
theorem B2209531 : Blo 1551473 2209531 := bstep (se 1 (by rfl) ⟨1657148, by rfl⟩ : syracuseStep 2209531 = 3314297) B3314297
theorem B9950987 : Blo 1551473 9950987 := bstep (se 1 (by rfl) ⟨7463240, by rfl⟩ : syracuseStep 9950987 = 14926481) B14926481
theorem B71661347 : Blo 1551473 71661347 := bstep (se 1 (by rfl) ⟨53746010, by rfl⟩ : syracuseStep 71661347 = 107492021) B107492021
theorem B63739705 : Blo 1551473 63739705 := bstep (se 2 (by rfl) ⟨23902389, by rfl⟩ : syracuseStep 63739705 = 47804779) B47804779
theorem B4421591 : Blo 1551473 4421591 := bstep (se 1 (by rfl) ⟨3316193, by rfl⟩ : syracuseStep 4421591 = 6632387) B6632387
theorem B4970459 : Blo 1551473 4970459 := bstep (se 1 (by rfl) ⟨3727844, by rfl⟩ : syracuseStep 4970459 = 7455689) B7455689
theorem B4478939 : Blo 1551473 4478939 := bstep (se 1 (by rfl) ⟨3359204, by rfl⟩ : syracuseStep 4478939 = 6718409) B6718409
theorem B5240807 : Blo 1551473 5240807 := bstep (se 1 (by rfl) ⟨3930605, by rfl⟩ : syracuseStep 5240807 = 7861211) B7861211
theorem B5240915 : Blo 1551473 5240915 := bstep (se 1 (by rfl) ⟨3930686, by rfl⟩ : syracuseStep 5240915 = 7861373) B7861373
theorem B4036763 : Blo 1551473 4036763 := bstep (se 1 (by rfl) ⟨3027572, by rfl⟩ : syracuseStep 4036763 = 6055145) B6055145
theorem B5241131 : Blo 1551473 5241131 := bstep (se 1 (by rfl) ⟨3930848, by rfl⟩ : syracuseStep 5241131 = 7861697) B7861697
theorem B2210095 : Blo 1551473 2210095 := bstep (se 1 (by rfl) ⟨1657571, by rfl⟩ : syracuseStep 2210095 = 3315143) B3315143
theorem B2619695 : Blo 1551473 2619695 := bstep (se 1 (by rfl) ⟨1964771, by rfl⟩ : syracuseStep 2619695 = 3929543) B3929543
theorem B23886323 : Blo 1551473 23886323 := bstep (se 1 (by rfl) ⟨17914742, by rfl⟩ : syracuseStep 23886323 = 35829485) B35829485
theorem B2619931 : Blo 1551473 2619931 := bstep (se 1 (by rfl) ⟨1964948, by rfl⟩ : syracuseStep 2619931 = 3929897) B3929897
theorem B5241401 : Blo 1551473 5241401 := bstep (se 2 (by rfl) ⟨1965525, by rfl⟩ : syracuseStep 5241401 = 3931051) B3931051
theorem B59718221 : Blo 1551473 59718221 := bstep (se 3 (by rfl) ⟨11197166, by rfl⟩ : syracuseStep 59718221 = 22394333) B22394333
theorem B26532683 : Blo 1551473 26532683 := bstep (se 1 (by rfl) ⟨19899512, by rfl⟩ : syracuseStep 26532683 = 39799025) B39799025
theorem B4422559 : Blo 1551473 4422559 := bstep (se 1 (by rfl) ⟨3316919, by rfl⟩ : syracuseStep 4422559 = 6633839) B6633839
theorem B7461857 : Blo 1551473 7461857 := bstep (se 2 (by rfl) ⟨2798196, by rfl⟩ : syracuseStep 7461857 = 5596393) B5596393
theorem B2948167 : Blo 1551473 2948167 := bstep (se 1 (by rfl) ⟨2211125, by rfl⟩ : syracuseStep 2948167 = 4422251) B4422251
theorem B9944221 : Blo 1551473 9944221 := bstep (se 3 (by rfl) ⟨1864541, by rfl⟩ : syracuseStep 9944221 = 3729083) B3729083
theorem B7863479 : Blo 1551473 7863479 := bstep (se 1 (by rfl) ⟨5897609, by rfl⟩ : syracuseStep 7863479 = 11795219) B11795219
theorem B8846779 : Blo 1551473 8846779 := bstep (se 1 (by rfl) ⟨6635084, by rfl⟩ : syracuseStep 8846779 = 13270169) B13270169
theorem B9944531 : Blo 1551473 9944531 := bstep (se 1 (by rfl) ⟨7458398, by rfl⟩ : syracuseStep 9944531 = 14916797) B14916797
theorem B5594579 : Blo 1551473 5594579 := bstep (se 1 (by rfl) ⟨4195934, by rfl⟩ : syracuseStep 5594579 = 8391869) B8391869
theorem B2620903 : Blo 1551473 2620903 := bstep (se 1 (by rfl) ⟨1965677, by rfl⟩ : syracuseStep 2620903 = 3931355) B3931355
theorem B2620991 : Blo 1551473 2620991 := bstep (se 1 (by rfl) ⟨1965743, by rfl⟩ : syracuseStep 2620991 = 3931487) B3931487
theorem B2948699 : Blo 1551473 2948699 := bstep (se 1 (by rfl) ⟨2211524, by rfl⟩ : syracuseStep 2948699 = 4423049) B4423049
theorem B91954865 : Blo 1551473 91954865 := bstep (se 2 (by rfl) ⟨34483074, by rfl⟩ : syracuseStep 91954865 = 68966149) B68966149
theorem B22675211 : Blo 1551473 22675211 := bstep (se 1 (by rfl) ⟨17006408, by rfl⟩ : syracuseStep 22675211 = 34012817) B34012817
theorem B2948987 : Blo 1551473 2948987 := bstep (se 1 (by rfl) ⟨2211740, by rfl⟩ : syracuseStep 2948987 = 4423481) B4423481
theorem B25182211 : Blo 1551473 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B11190311 : Blo 1551473 11190311 := bstep (se 1 (by rfl) ⟨8392733, by rfl⟩ : syracuseStep 11190311 = 16785467) B16785467
theorem B15130759 : Blo 1551473 15130759 := bstep (se 1 (by rfl) ⟨11348069, by rfl⟩ : syracuseStep 15130759 = 22696139) B22696139
theorem B12443843 : Blo 1551473 12443843 := bstep (se 1 (by rfl) ⟨9332882, by rfl⟩ : syracuseStep 12443843 = 18665765) B18665765
theorem B73695575 : Blo 1551473 73695575 := bstep (se 1 (by rfl) ⟨55271681, by rfl⟩ : syracuseStep 73695575 = 110543363) B110543363
theorem B13255271 : Blo 1551473 13255271 := bstep (se 1 (by rfl) ⟨9941453, by rfl⟩ : syracuseStep 13255271 = 19882907) B19882907
theorem B2327495 : Blo 1551473 2327495 := bstep (se 1 (by rfl) ⟨1745621, by rfl⟩ : syracuseStep 2327495 = 3491243) B3491243
theorem B2327663 : Blo 1551473 2327663 := bstep (se 1 (by rfl) ⟨1745747, by rfl⟩ : syracuseStep 2327663 = 3491495) B3491495
theorem B1746031 : Blo 1551473 1746031 := bstep (se 1 (by rfl) ⟨1309523, by rfl⟩ : syracuseStep 1746031 = 2619047) B2619047
theorem B3490991 : Blo 1551473 3490991 := bstep (se 1 (by rfl) ⟨2618243, by rfl⟩ : syracuseStep 3490991 = 5236487) B5236487
theorem B3491027 : Blo 1551473 3491027 := bstep (se 1 (by rfl) ⟨2618270, by rfl⟩ : syracuseStep 3491027 = 5236541) B5236541
theorem B2327855 : Blo 1551473 2327855 := bstep (se 1 (by rfl) ⟨1745891, by rfl⟩ : syracuseStep 2327855 = 3491783) B3491783
theorem B3491297 : Blo 1551473 3491297 := bstep (se 2 (by rfl) ⟨1309236, by rfl⟩ : syracuseStep 3491297 = 2618473) B2618473
theorem B2328059 : Blo 1551473 2328059 := bstep (se 1 (by rfl) ⟨1746044, by rfl⟩ : syracuseStep 2328059 = 3492089) B3492089
theorem B2328095 : Blo 1551473 2328095 := bstep (se 1 (by rfl) ⟨1746071, by rfl⟩ : syracuseStep 2328095 = 3492143) B3492143
theorem B1746463 : Blo 1551473 1746463 := bstep (se 1 (by rfl) ⟨1309847, by rfl⟩ : syracuseStep 1746463 = 2619695) B2619695
theorem B26904109 : Blo 1551473 26904109 := bstep (se 3 (by rfl) ⟨5044520, by rfl⟩ : syracuseStep 26904109 = 10089041) B10089041
theorem B3728969 : Blo 1551473 3728969 := bstep (se 2 (by rfl) ⟨1398363, by rfl⟩ : syracuseStep 3728969 = 2796727) B2796727
theorem B2328239 : Blo 1551473 2328239 := bstep (se 1 (by rfl) ⟨1746179, by rfl⟩ : syracuseStep 2328239 = 3492359) B3492359
theorem B2328359 : Blo 1551473 2328359 := bstep (se 1 (by rfl) ⟨1746269, by rfl⟩ : syracuseStep 2328359 = 3492539) B3492539
theorem B3540775 : Blo 1551473 3540775 := bstep (se 1 (by rfl) ⟨2655581, by rfl⟩ : syracuseStep 3540775 = 5311163) B5311163
theorem B102131533 : Blo 1551473 102131533 := bstep (se 3 (by rfl) ⟨19149662, by rfl⟩ : syracuseStep 102131533 = 38299325) B38299325
theorem B17688455 : Blo 1551473 17688455 := bstep (se 1 (by rfl) ⟨13266341, by rfl⟩ : syracuseStep 17688455 = 26532683) B26532683
theorem B4974571 : Blo 1551473 4974571 := bstep (se 1 (by rfl) ⟨3730928, by rfl⟩ : syracuseStep 4974571 = 7461857) B7461857
theorem B6629687 : Blo 1551473 6629687 := bstep (se 1 (by rfl) ⟨4972265, by rfl⟩ : syracuseStep 6629687 = 9944531) B9944531
theorem B3729719 : Blo 1551473 3729719 := bstep (se 1 (by rfl) ⟨2797289, by rfl⟩ : syracuseStep 3729719 = 5594579) B5594579
theorem B2328911 : Blo 1551473 2328911 := bstep (se 1 (by rfl) ⟨1746683, by rfl⟩ : syracuseStep 2328911 = 3493367) B3493367
theorem B17918297 : Blo 1551473 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B4196735 : Blo 1551473 4196735 := bstep (se 1 (by rfl) ⟨3147551, by rfl⟩ : syracuseStep 4196735 = 6295103) B6295103
theorem B2328959 : Blo 1551473 2328959 := bstep (se 1 (by rfl) ⟨1746719, by rfl⟩ : syracuseStep 2328959 = 3493439) B3493439
theorem B1747327 : Blo 1551473 1747327 := bstep (se 1 (by rfl) ⟨1310495, by rfl⟩ : syracuseStep 1747327 = 2620991) B2620991
theorem B6629789 : Blo 1551473 6629789 := bstep (se 3 (by rfl) ⟨1243085, by rfl⟩ : syracuseStep 6629789 = 2486171) B2486171
theorem B84986273 : Blo 1551473 84986273 := bstep (se 2 (by rfl) ⟨31869852, by rfl⟩ : syracuseStep 84986273 = 63739705) B63739705
theorem B2329001 : Blo 1551473 2329001 := bstep (se 2 (by rfl) ⟨873375, by rfl⟩ : syracuseStep 2329001 = 1746751) B1746751
theorem B61303243 : Blo 1551473 61303243 := bstep (se 1 (by rfl) ⟨45977432, by rfl⟩ : syracuseStep 61303243 = 91954865) B91954865
theorem B15116807 : Blo 1551473 15116807 := bstep (se 1 (by rfl) ⟨11337605, by rfl⟩ : syracuseStep 15116807 = 22675211) B22675211
theorem B3492647 : Blo 1551473 3492647 := bstep (se 1 (by rfl) ⟨2619485, by rfl⟩ : syracuseStep 3492647 = 5238971) B5238971
theorem B2329385 : Blo 1551473 2329385 := bstep (se 2 (by rfl) ⟨873519, by rfl⟩ : syracuseStep 2329385 = 1747039) B1747039
theorem B4311899 : Blo 1551473 4311899 := bstep (se 1 (by rfl) ⟨3233924, by rfl⟩ : syracuseStep 4311899 = 6467849) B6467849
theorem B2329595 : Blo 1551473 2329595 := bstep (se 1 (by rfl) ⟨1747196, by rfl⟩ : syracuseStep 2329595 = 3494393) B3494393
theorem B2329655 : Blo 1551473 2329655 := bstep (se 1 (by rfl) ⟨1747241, by rfl⟩ : syracuseStep 2329655 = 3494483) B3494483
theorem B9571391 : Blo 1551473 9571391 := bstep (se 1 (by rfl) ⟨7178543, by rfl⟩ : syracuseStep 9571391 = 14357087) B14357087
theorem B3492971 : Blo 1551473 3492971 := bstep (se 1 (by rfl) ⟨2619728, by rfl⟩ : syracuseStep 3492971 = 5239457) B5239457
theorem B2329775 : Blo 1551473 2329775 := bstep (se 1 (by rfl) ⟨1747331, by rfl⟩ : syracuseStep 2329775 = 3494663) B3494663
theorem B5893343 : Blo 1551473 5893343 := bstep (se 1 (by rfl) ⟨4420007, by rfl⟩ : syracuseStep 5893343 = 8840015) B8840015
theorem B3493241 : Blo 1551473 3493241 := bstep (se 2 (by rfl) ⟨1309965, by rfl⟩ : syracuseStep 3493241 = 2619931) B2619931
theorem B1551743 : Blo 1551473 1551743 := bstep (se 1 (by rfl) ⟨1163807, by rfl⟩ : syracuseStep 1551743 = 2327615) B2327615
theorem B1551771 : Blo 1551473 1551771 := bstep (se 1 (by rfl) ⟨1163828, by rfl⟩ : syracuseStep 1551771 = 2327657) B2327657
theorem B1551839 : Blo 1551473 1551839 := bstep (se 1 (by rfl) ⟨1163879, by rfl⟩ : syracuseStep 1551839 = 2327759) B2327759
theorem B2911835 : Blo 1551473 2911835 := bstep (se 1 (by rfl) ⟨2183876, by rfl⟩ : syracuseStep 2911835 = 4367753) B4367753
theorem B1551975 : Blo 1551473 1551975 := bstep (se 1 (by rfl) ⟨1163981, by rfl⟩ : syracuseStep 1551975 = 2327963) B2327963
theorem B17673875 : Blo 1551473 17673875 := bstep (se 1 (by rfl) ⟨13255406, by rfl⟩ : syracuseStep 17673875 = 26510813) B26510813
theorem B3493547 : Blo 1551473 3493547 := bstep (se 1 (by rfl) ⟨2620160, by rfl⟩ : syracuseStep 3493547 = 5240321) B5240321
theorem B7769843 : Blo 1551473 7769843 := bstep (se 1 (by rfl) ⟨5827382, by rfl⟩ : syracuseStep 7769843 = 11654765) B11654765
theorem B1552123 : Blo 1551473 1552123 := bstep (se 1 (by rfl) ⟨1164092, by rfl⟩ : syracuseStep 1552123 = 2328185) B2328185
theorem B1552191 : Blo 1551473 1552191 := bstep (se 1 (by rfl) ⟨1164143, by rfl⟩ : syracuseStep 1552191 = 2328287) B2328287
theorem B1552255 : Blo 1551473 1552255 := bstep (se 1 (by rfl) ⟨1164191, by rfl⟩ : syracuseStep 1552255 = 2328383) B2328383
theorem B3313639 : Blo 1551473 3313639 := bstep (se 1 (by rfl) ⟨2485229, by rfl⟩ : syracuseStep 3313639 = 4970459) B4970459
theorem B2985959 : Blo 1551473 2985959 := bstep (se 1 (by rfl) ⟨2239469, by rfl⟩ : syracuseStep 2985959 = 4478939) B4478939
theorem B1552367 : Blo 1551473 1552367 := bstep (se 1 (by rfl) ⟨1164275, by rfl⟩ : syracuseStep 1552367 = 2328551) B2328551
theorem B3493871 : Blo 1551473 3493871 := bstep (se 1 (by rfl) ⟨2620403, by rfl⟩ : syracuseStep 3493871 = 5240807) B5240807
theorem B1552379 : Blo 1551473 1552379 := bstep (se 1 (by rfl) ⟨1164284, by rfl⟩ : syracuseStep 1552379 = 2328569) B2328569
theorem B3493943 : Blo 1551473 3493943 := bstep (se 1 (by rfl) ⟨2620457, by rfl⟩ : syracuseStep 3493943 = 5240915) B5240915
theorem B1552447 : Blo 1551473 1552447 := bstep (se 1 (by rfl) ⟨1164335, by rfl⟩ : syracuseStep 1552447 = 2328671) B2328671
theorem B2691175 : Blo 1551473 2691175 := bstep (se 1 (by rfl) ⟨2018381, by rfl⟩ : syracuseStep 2691175 = 4036763) B4036763
theorem B1552487 : Blo 1551473 1552487 := bstep (se 1 (by rfl) ⟨1164365, by rfl⟩ : syracuseStep 1552487 = 2328731) B2328731
theorem B1552511 : Blo 1551473 1552511 := bstep (se 1 (by rfl) ⟨1164383, by rfl⟩ : syracuseStep 1552511 = 2328767) B2328767
theorem B1552539 : Blo 1551473 1552539 := bstep (se 1 (by rfl) ⟨1164404, by rfl⟩ : syracuseStep 1552539 = 2328809) B2328809
theorem B5894329 : Blo 1551473 5894329 := bstep (se 2 (by rfl) ⟨2210373, by rfl⟩ : syracuseStep 5894329 = 4420747) B4420747
theorem B3494087 : Blo 1551473 3494087 := bstep (se 1 (by rfl) ⟨2620565, by rfl⟩ : syracuseStep 3494087 = 5241131) B5241131
theorem B13258961 : Blo 1551473 13258961 := bstep (se 2 (by rfl) ⟨4972110, by rfl⟩ : syracuseStep 13258961 = 9944221) B9944221
theorem B3928297 : Blo 1551473 3928297 := bstep (se 2 (by rfl) ⟨1473111, by rfl⟩ : syracuseStep 3928297 = 2946223) B2946223
theorem B28324145 : Blo 1551473 28324145 := bstep (se 2 (by rfl) ⟨10621554, by rfl⟩ : syracuseStep 28324145 = 21243109) B21243109
theorem B1552743 : Blo 1551473 1552743 := bstep (se 1 (by rfl) ⟨1164557, by rfl⟩ : syracuseStep 1552743 = 2329115) B2329115
theorem B3494267 : Blo 1551473 3494267 := bstep (se 1 (by rfl) ⟨2620700, by rfl⟩ : syracuseStep 3494267 = 5241401) B5241401
theorem B1552795 : Blo 1551473 1552795 := bstep (se 1 (by rfl) ⟨1164596, by rfl⟩ : syracuseStep 1552795 = 2329193) B2329193
theorem B16781741 : Blo 1551473 16781741 := bstep (se 3 (by rfl) ⟨3146576, by rfl⟩ : syracuseStep 16781741 = 6293153) B6293153
theorem B2945479 : Blo 1551473 2945479 := bstep (se 1 (by rfl) ⟨2209109, by rfl⟩ : syracuseStep 2945479 = 4418219) B4418219
theorem B3494537 : Blo 1551473 3494537 := bstep (se 2 (by rfl) ⟨1310451, by rfl⟩ : syracuseStep 3494537 = 2620903) B2620903
theorem B1553147 : Blo 1551473 1553147 := bstep (se 1 (by rfl) ⟨1164860, by rfl⟩ : syracuseStep 1553147 = 2329721) B2329721
theorem B1553215 : Blo 1551473 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B1553243 : Blo 1551473 1553243 := bstep (se 1 (by rfl) ⟨1164932, by rfl⟩ : syracuseStep 1553243 = 2329865) B2329865
theorem B1553311 : Blo 1551473 1553311 := bstep (se 1 (by rfl) ⟨1164983, by rfl⟩ : syracuseStep 1553311 = 2329967) B2329967
theorem B1553391 : Blo 1551473 1553391 := bstep (se 1 (by rfl) ⟨1165043, by rfl⟩ : syracuseStep 1553391 = 2330087) B2330087
theorem B2946041 : Blo 1551473 2946041 := bstep (se 2 (by rfl) ⟨1104765, by rfl⟩ : syracuseStep 2946041 = 2209531) B2209531
theorem B14914793 : Blo 1551473 14914793 := bstep (se 2 (by rfl) ⟨5593047, by rfl⟩ : syracuseStep 14914793 = 11186095) B11186095
theorem B3495275 : Blo 1551473 3495275 := bstep (se 1 (by rfl) ⟨2621456, by rfl⟩ : syracuseStep 3495275 = 5242913) B5242913
theorem B1889767 : Blo 1551473 1889767 := bstep (se 1 (by rfl) ⟨1417325, by rfl⟩ : syracuseStep 1889767 = 2834651) B2834651
theorem B13448729 : Blo 1551473 13448729 := bstep (se 2 (by rfl) ⟨5043273, by rfl⟩ : syracuseStep 13448729 = 10086547) B10086547
theorem B6633103 : Blo 1551473 6633103 := bstep (se 1 (by rfl) ⟨4974827, by rfl⟩ : syracuseStep 6633103 = 9949655) B9949655
theorem B2946793 : Blo 1551473 2946793 := bstep (se 2 (by rfl) ⟨1105047, by rfl⟩ : syracuseStep 2946793 = 2210095) B2210095
theorem B1963759 : Blo 1551473 1963759 := bstep (se 1 (by rfl) ⟨1472819, by rfl⟩ : syracuseStep 1963759 = 2945639) B2945639
theorem B2799343 : Blo 1551473 2799343 := bstep (se 1 (by rfl) ⟨2099507, by rfl⟩ : syracuseStep 2799343 = 4199015) B4199015
theorem B95647715 : Blo 1551473 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B7461011 : Blo 1551473 7461011 := bstep (se 1 (by rfl) ⟨5595758, by rfl⟩ : syracuseStep 7461011 = 11191517) B11191517
theorem B7854569 : Blo 1551473 7854569 := bstep (se 2 (by rfl) ⟨2945463, by rfl⟩ : syracuseStep 7854569 = 5890927) B5890927
theorem B6633991 : Blo 1551473 6633991 := bstep (se 1 (by rfl) ⟨4975493, by rfl⟩ : syracuseStep 6633991 = 9950987) B9950987
theorem B47774231 : Blo 1551473 47774231 := bstep (se 1 (by rfl) ⟨35830673, by rfl⟩ : syracuseStep 47774231 = 71661347) B71661347
theorem B5896745 : Blo 1551473 5896745 := bstep (se 2 (by rfl) ⟨2211279, by rfl⟩ : syracuseStep 5896745 = 4422559) B4422559
theorem B13261421 : Blo 1551473 13261421 := bstep (se 3 (by rfl) ⟨2486516, by rfl⟩ : syracuseStep 13261421 = 4973033) B4973033
theorem B2947727 : Blo 1551473 2947727 := bstep (se 1 (by rfl) ⟨2210795, by rfl⟩ : syracuseStep 2947727 = 4421591) B4421591
theorem B3930889 : Blo 1551473 3930889 := bstep (se 2 (by rfl) ⟨1474083, by rfl⟩ : syracuseStep 3930889 = 2948167) B2948167
theorem B3316535 : Blo 1551473 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B15924215 : Blo 1551473 15924215 := bstep (se 1 (by rfl) ⟨11943161, by rfl⟩ : syracuseStep 15924215 = 23886323) B23886323
theorem B3316783 : Blo 1551473 3316783 := bstep (se 1 (by rfl) ⟨2487587, by rfl⟩ : syracuseStep 3316783 = 4975175) B4975175
theorem B39812147 : Blo 1551473 39812147 := bstep (se 1 (by rfl) ⟨29859110, by rfl⟩ : syracuseStep 39812147 = 59718221) B59718221
theorem B11795705 : Blo 1551473 11795705 := bstep (se 2 (by rfl) ⟨4423389, by rfl⟩ : syracuseStep 11795705 = 8846779) B8846779
theorem B5242319 : Blo 1551473 5242319 := bstep (se 1 (by rfl) ⟨3931739, by rfl⟩ : syracuseStep 5242319 = 7863479) B7863479
theorem B7863965 : Blo 1551473 7863965 := bstep (se 3 (by rfl) ⟨1474493, by rfl⟩ : syracuseStep 7863965 = 2948987) B2948987
theorem B1965799 : Blo 1551473 1965799 := bstep (se 1 (by rfl) ⟨1474349, by rfl⟩ : syracuseStep 1965799 = 2948699) B2948699
theorem B7856027 : Blo 1551473 7856027 := bstep (se 1 (by rfl) ⟨5892020, by rfl⟩ : syracuseStep 7856027 = 11784041) B11784041
theorem B3588233 : Blo 1551473 3588233 := bstep (se 2 (by rfl) ⟨1345587, by rfl⟩ : syracuseStep 3588233 = 2691175) B2691175
theorem B8839307 : Blo 1551473 8839307 := bstep (se 1 (by rfl) ⟨6629480, by rfl⟩ : syracuseStep 8839307 = 13258961) B13258961
theorem B18882763 : Blo 1551473 18882763 := bstep (se 1 (by rfl) ⟨14162072, by rfl⟩ : syracuseStep 18882763 = 28324145) B28324145
theorem B39772781 : Blo 1551473 39772781 := bstep (se 3 (by rfl) ⟨7457396, by rfl⟩ : syracuseStep 39772781 = 14914793) B14914793
theorem B2327327 : Blo 1551473 2327327 := bstep (se 1 (by rfl) ⟨1745495, by rfl⟩ : syracuseStep 2327327 = 3490991) B3490991
theorem B2327351 : Blo 1551473 2327351 := bstep (se 1 (by rfl) ⟨1745513, by rfl⟩ : syracuseStep 2327351 = 3491027) B3491027
theorem B2327531 : Blo 1551473 2327531 := bstep (se 1 (by rfl) ⟨1745648, by rfl⟩ : syracuseStep 2327531 = 3491297) B3491297
theorem B2328041 : Blo 1551473 2328041 := bstep (se 2 (by rfl) ⟨873015, by rfl⟩ : syracuseStep 2328041 = 1746031) B1746031
theorem B11945531 : Blo 1551473 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B56657515 : Blo 1551473 56657515 := bstep (se 1 (by rfl) ⟨42493136, by rfl⟩ : syracuseStep 56657515 = 84986273) B84986273
theorem B5236379 : Blo 1551473 5236379 := bstep (se 1 (by rfl) ⟨3927284, by rfl⟩ : syracuseStep 5236379 = 7854569) B7854569
theorem B10077871 : Blo 1551473 10077871 := bstep (se 1 (by rfl) ⟨7558403, by rfl⟩ : syracuseStep 10077871 = 15116807) B15116807
theorem B8840947 : Blo 1551473 8840947 := bstep (se 1 (by rfl) ⟨6630710, by rfl⟩ : syracuseStep 8840947 = 13261421) B13261421
theorem B2328431 : Blo 1551473 2328431 := bstep (se 1 (by rfl) ⟨1746323, by rfl⟩ : syracuseStep 2328431 = 3492647) B3492647
theorem B2328617 : Blo 1551473 2328617 := bstep (se 2 (by rfl) ⟨873231, by rfl⟩ : syracuseStep 2328617 = 1746463) B1746463
theorem B2328647 : Blo 1551473 2328647 := bstep (se 1 (by rfl) ⟨1746485, by rfl⟩ : syracuseStep 2328647 = 3492971) B3492971
theorem B2328827 : Blo 1551473 2328827 := bstep (se 1 (by rfl) ⟨1746620, by rfl⟩ : syracuseStep 2328827 = 3493241) B3493241
theorem B4721033 : Blo 1551473 4721033 := bstep (se 2 (by rfl) ⟨1770387, by rfl⟩ : syracuseStep 4721033 = 3540775) B3540775
theorem B11782583 : Blo 1551473 11782583 := bstep (se 1 (by rfl) ⟨8836937, by rfl⟩ : syracuseStep 11782583 = 17673875) B17673875
theorem B2329031 : Blo 1551473 2329031 := bstep (se 1 (by rfl) ⟨1746773, by rfl⟩ : syracuseStep 2329031 = 3493547) B3493547
theorem B5179895 : Blo 1551473 5179895 := bstep (se 1 (by rfl) ⟨3884921, by rfl⟩ : syracuseStep 5179895 = 7769843) B7769843
theorem B5237351 : Blo 1551473 5237351 := bstep (se 1 (by rfl) ⟨3928013, by rfl⟩ : syracuseStep 5237351 = 7856027) B7856027
theorem B4418185 : Blo 1551473 4418185 := bstep (se 2 (by rfl) ⟨1656819, by rfl⟩ : syracuseStep 4418185 = 3313639) B3313639
theorem B2329247 : Blo 1551473 2329247 := bstep (se 1 (by rfl) ⟨1746935, by rfl⟩ : syracuseStep 2329247 = 3493871) B3493871
theorem B2329295 : Blo 1551473 2329295 := bstep (se 1 (by rfl) ⟨1746971, by rfl⟩ : syracuseStep 2329295 = 3493943) B3493943
theorem B2329391 : Blo 1551473 2329391 := bstep (se 1 (by rfl) ⟨1747043, by rfl⟩ : syracuseStep 2329391 = 3494087) B3494087
theorem B49130383 : Blo 1551473 49130383 := bstep (se 1 (by rfl) ⟨36847787, by rfl⟩ : syracuseStep 49130383 = 73695575) B73695575
theorem B7859105 : Blo 1551473 7859105 := bstep (se 2 (by rfl) ⟨2947164, by rfl⟩ : syracuseStep 7859105 = 5894329) B5894329
theorem B2329511 : Blo 1551473 2329511 := bstep (se 1 (by rfl) ⟨1747133, by rfl⟩ : syracuseStep 2329511 = 3494267) B3494267
theorem B5237729 : Blo 1551473 5237729 := bstep (se 2 (by rfl) ⟨1964148, by rfl⟩ : syracuseStep 5237729 = 3928297) B3928297
theorem B2329691 : Blo 1551473 2329691 := bstep (se 1 (by rfl) ⟨1747268, by rfl⟩ : syracuseStep 2329691 = 3494537) B3494537
theorem B2329769 : Blo 1551473 2329769 := bstep (se 2 (by rfl) ⟨873663, by rfl⟩ : syracuseStep 2329769 = 1747327) B1747327
theorem B3927305 : Blo 1551473 3927305 := bstep (se 2 (by rfl) ⟨1472739, by rfl⟩ : syracuseStep 3927305 = 2945479) B2945479
theorem B1551663 : Blo 1551473 1551663 := bstep (se 1 (by rfl) ⟨1163747, by rfl⟩ : syracuseStep 1551663 = 2327495) B2327495
theorem B1551775 : Blo 1551473 1551775 := bstep (se 1 (by rfl) ⟨1163831, by rfl⟩ : syracuseStep 1551775 = 2327663) B2327663
theorem B1551903 : Blo 1551473 1551903 := bstep (se 1 (by rfl) ⟨1163927, by rfl⟩ : syracuseStep 1551903 = 2327855) B2327855
theorem B2330183 : Blo 1551473 2330183 := bstep (se 1 (by rfl) ⟨1747637, by rfl⟩ : syracuseStep 2330183 = 3495275) B3495275
theorem B1552039 : Blo 1551473 1552039 := bstep (se 1 (by rfl) ⟨1164029, by rfl⟩ : syracuseStep 1552039 = 2328059) B2328059
theorem B8965819 : Blo 1551473 8965819 := bstep (se 1 (by rfl) ⟨6724364, by rfl⟩ : syracuseStep 8965819 = 13448729) B13448729
theorem B1552063 : Blo 1551473 1552063 := bstep (se 1 (by rfl) ⟨1164047, by rfl⟩ : syracuseStep 1552063 = 2328095) B2328095
theorem B2485979 : Blo 1551473 2485979 := bstep (se 1 (by rfl) ⟨1864484, by rfl⟩ : syracuseStep 2485979 = 3728969) B3728969
theorem B1552159 : Blo 1551473 1552159 := bstep (se 1 (by rfl) ⟨1164119, by rfl⟩ : syracuseStep 1552159 = 2328239) B2328239
theorem B1552239 : Blo 1551473 1552239 := bstep (se 1 (by rfl) ⟨1164179, by rfl⟩ : syracuseStep 1552239 = 2328359) B2328359
theorem B14929829 : Blo 1551473 14929829 := bstep (se 4 (by rfl) ⟨1399671, by rfl⟩ : syracuseStep 14929829 = 2799343) B2799343
theorem B11792303 : Blo 1551473 11792303 := bstep (se 1 (by rfl) ⟨8844227, by rfl⟩ : syracuseStep 11792303 = 17688455) B17688455
theorem B4419791 : Blo 1551473 4419791 := bstep (se 1 (by rfl) ⟨3314843, by rfl⟩ : syracuseStep 4419791 = 6629687) B6629687
theorem B2486479 : Blo 1551473 2486479 := bstep (se 1 (by rfl) ⟨1864859, by rfl⟩ : syracuseStep 2486479 = 3729719) B3729719
theorem B1552607 : Blo 1551473 1552607 := bstep (se 1 (by rfl) ⟨1164455, by rfl⟩ : syracuseStep 1552607 = 2328911) B2328911
theorem B2797823 : Blo 1551473 2797823 := bstep (se 1 (by rfl) ⟨2098367, by rfl⟩ : syracuseStep 2797823 = 4196735) B4196735
theorem B1552639 : Blo 1551473 1552639 := bstep (se 1 (by rfl) ⟨1164479, by rfl⟩ : syracuseStep 1552639 = 2328959) B2328959
theorem B4419859 : Blo 1551473 4419859 := bstep (se 1 (by rfl) ⟨3314894, by rfl⟩ : syracuseStep 4419859 = 6629789) B6629789
theorem B1552667 : Blo 1551473 1552667 := bstep (se 1 (by rfl) ⟨1164500, by rfl⟩ : syracuseStep 1552667 = 2329001) B2329001
theorem B1552923 : Blo 1551473 1552923 := bstep (se 1 (by rfl) ⟨1164692, by rfl⟩ : syracuseStep 1552923 = 2329385) B2329385
theorem B2519689 : Blo 1551473 2519689 := bstep (se 2 (by rfl) ⟨944883, by rfl⟩ : syracuseStep 2519689 = 1889767) B1889767
theorem B1553063 : Blo 1551473 1553063 := bstep (se 1 (by rfl) ⟨1164797, by rfl⟩ : syracuseStep 1553063 = 2329595) B2329595
theorem B1553103 : Blo 1551473 1553103 := bstep (se 1 (by rfl) ⟨1164827, by rfl⟩ : syracuseStep 1553103 = 2329655) B2329655
theorem B1553183 : Blo 1551473 1553183 := bstep (se 1 (by rfl) ⟨1164887, by rfl⟩ : syracuseStep 1553183 = 2329775) B2329775
theorem B3928895 : Blo 1551473 3928895 := bstep (se 1 (by rfl) ⟨2946671, by rfl⟩ : syracuseStep 3928895 = 5893343) B5893343
theorem B8844137 : Blo 1551473 8844137 := bstep (se 2 (by rfl) ⟨3316551, by rfl⟩ : syracuseStep 8844137 = 6633103) B6633103
theorem B3494879 : Blo 1551473 3494879 := bstep (se 1 (by rfl) ⟨2621159, by rfl⟩ : syracuseStep 3494879 = 5242319) B5242319
theorem B3929057 : Blo 1551473 3929057 := bstep (se 2 (by rfl) ⟨1473396, by rfl⟩ : syracuseStep 3929057 = 2946793) B2946793
theorem B2618345 : Blo 1551473 2618345 := bstep (se 2 (by rfl) ⟨981879, by rfl⟩ : syracuseStep 2618345 = 1963759) B1963759
theorem B6632761 : Blo 1551473 6632761 := bstep (se 2 (by rfl) ⟨2487285, by rfl⟩ : syracuseStep 6632761 = 4974571) B4974571
theorem B33576281 : Blo 1551473 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B7460207 : Blo 1551473 7460207 := bstep (se 1 (by rfl) ⟨5595155, by rfl⟩ : syracuseStep 7460207 = 11190311) B11190311
theorem B8295895 : Blo 1551473 8295895 := bstep (se 1 (by rfl) ⟨6221921, by rfl⟩ : syracuseStep 8295895 = 12443843) B12443843
theorem B20174345 : Blo 1551473 20174345 := bstep (se 2 (by rfl) ⟨7565379, by rfl⟩ : syracuseStep 20174345 = 15130759) B15130759
theorem B11187827 : Blo 1551473 11187827 := bstep (se 1 (by rfl) ⟨8390870, by rfl⟩ : syracuseStep 11187827 = 16781741) B16781741
theorem B19896029 : Blo 1551473 19896029 := bstep (se 3 (by rfl) ⟨3730505, by rfl⟩ : syracuseStep 19896029 = 7461011) B7461011
theorem B8836847 : Blo 1551473 8836847 := bstep (se 1 (by rfl) ⟨6627635, by rfl⟩ : syracuseStep 8836847 = 13255271) B13255271
theorem B81737657 : Blo 1551473 81737657 := bstep (se 2 (by rfl) ⟨30651621, by rfl⟩ : syracuseStep 81737657 = 61303243) B61303243
theorem B1964027 : Blo 1551473 1964027 := bstep (se 1 (by rfl) ⟨1473020, by rfl⟩ : syracuseStep 1964027 = 2946041) B2946041
theorem B8845321 : Blo 1551473 8845321 := bstep (se 2 (by rfl) ⟨3316995, by rfl⟩ : syracuseStep 8845321 = 6633991) B6633991
theorem B5241185 : Blo 1551473 5241185 := bstep (se 2 (by rfl) ⟨1965444, by rfl⟩ : syracuseStep 5241185 = 3930889) B3930889
theorem B63765143 : Blo 1551473 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B4422377 : Blo 1551473 4422377 := bstep (se 2 (by rfl) ⟨1658391, by rfl⟩ : syracuseStep 4422377 = 3316783) B3316783
theorem B31849487 : Blo 1551473 31849487 := bstep (se 1 (by rfl) ⟨23887115, by rfl⟩ : syracuseStep 31849487 = 47774231) B47774231
theorem B3931163 : Blo 1551473 3931163 := bstep (se 1 (by rfl) ⟨2948372, by rfl⟩ : syracuseStep 3931163 = 5896745) B5896745
theorem B1965151 : Blo 1551473 1965151 := bstep (se 1 (by rfl) ⟨1473863, by rfl⟩ : syracuseStep 1965151 = 2947727) B2947727
theorem B2211023 : Blo 1551473 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B2874599 : Blo 1551473 2874599 := bstep (se 1 (by rfl) ⟨2155949, by rfl⟩ : syracuseStep 2874599 = 4311899) B4311899
theorem B10616143 : Blo 1551473 10616143 := bstep (se 1 (by rfl) ⟨7962107, by rfl⟩ : syracuseStep 10616143 = 15924215) B15924215
theorem B26541431 : Blo 1551473 26541431 := bstep (se 1 (by rfl) ⟨19906073, by rfl⟩ : syracuseStep 26541431 = 39812147) B39812147
theorem B6380927 : Blo 1551473 6380927 := bstep (se 1 (by rfl) ⟨4785695, by rfl⟩ : syracuseStep 6380927 = 9571391) B9571391
theorem B35872145 : Blo 1551473 35872145 := bstep (se 2 (by rfl) ⟨13452054, by rfl⟩ : syracuseStep 35872145 = 26904109) B26904109
theorem B7863803 : Blo 1551473 7863803 := bstep (se 1 (by rfl) ⟨5897852, by rfl⟩ : syracuseStep 7863803 = 11795705) B11795705
theorem B2621065 : Blo 1551473 2621065 := bstep (se 2 (by rfl) ⟨982899, by rfl⟩ : syracuseStep 2621065 = 1965799) B1965799
theorem B1941223 : Blo 1551473 1941223 := bstep (se 1 (by rfl) ⟨1455917, by rfl⟩ : syracuseStep 1941223 = 2911835) B2911835
theorem B136175377 : Blo 1551473 136175377 := bstep (se 2 (by rfl) ⟨51065766, by rfl⟩ : syracuseStep 136175377 = 102131533) B102131533
theorem B5242643 : Blo 1551473 5242643 := bstep (se 1 (by rfl) ⟨3931982, by rfl⟩ : syracuseStep 5242643 = 7863965) B7863965
theorem B1990639 : Blo 1551473 1990639 := bstep (se 1 (by rfl) ⟨1492979, by rfl⟩ : syracuseStep 1990639 = 2985959) B2985959
theorem B9568621 : Blo 1551473 9568621 := bstep (se 3 (by rfl) ⟨1794116, by rfl⟩ : syracuseStep 9568621 = 3588233) B3588233
theorem B1745563 : Blo 1551473 1745563 := bstep (se 1 (by rfl) ⟨1309172, by rfl⟩ : syracuseStep 1745563 = 2618345) B2618345
theorem B5890913 : Blo 1551473 5890913 := bstep (se 2 (by rfl) ⟨2209092, by rfl⟩ : syracuseStep 5890913 = 4418185) B4418185
theorem B3359585 : Blo 1551473 3359585 := bstep (se 2 (by rfl) ⟨1259844, by rfl⟩ : syracuseStep 3359585 = 2519689) B2519689
theorem B4973471 : Blo 1551473 4973471 := bstep (se 1 (by rfl) ⟨3730103, by rfl⟩ : syracuseStep 4973471 = 7460207) B7460207
theorem B7963687 : Blo 1551473 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B3490919 : Blo 1551473 3490919 := bstep (se 1 (by rfl) ⟨2618189, by rfl⟩ : syracuseStep 3490919 = 5236379) B5236379
theorem B13264019 : Blo 1551473 13264019 := bstep (se 1 (by rfl) ⟨9948014, by rfl⟩ : syracuseStep 13264019 = 19896029) B19896029
theorem B5891231 : Blo 1551473 5891231 := bstep (se 1 (by rfl) ⟨4418423, by rfl⟩ : syracuseStep 5891231 = 8836847) B8836847
theorem B3147355 : Blo 1551473 3147355 := bstep (se 1 (by rfl) ⟨2360516, by rfl⟩ : syracuseStep 3147355 = 4721033) B4721033
theorem B3491567 : Blo 1551473 3491567 := bstep (se 1 (by rfl) ⟨2618675, by rfl⟩ : syracuseStep 3491567 = 5237351) B5237351
theorem B42510095 : Blo 1551473 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B11061193 : Blo 1551473 11061193 := bstep (se 2 (by rfl) ⟨4147947, by rfl⟩ : syracuseStep 11061193 = 8295895) B8295895
theorem B3491819 : Blo 1551473 3491819 := bstep (se 1 (by rfl) ⟨2618864, by rfl⟩ : syracuseStep 3491819 = 5237729) B5237729
theorem B13437161 : Blo 1551473 13437161 := bstep (se 2 (by rfl) ⟨5038935, by rfl⟩ : syracuseStep 13437161 = 10077871) B10077871
theorem B11954425 : Blo 1551473 11954425 := bstep (se 2 (by rfl) ⟨4482909, by rfl⟩ : syracuseStep 11954425 = 8965819) B8965819
theorem B4253951 : Blo 1551473 4253951 := bstep (se 1 (by rfl) ⟨3190463, by rfl⟩ : syracuseStep 4253951 = 6380927) B6380927
theorem B23914763 : Blo 1551473 23914763 := bstep (se 1 (by rfl) ⟨17936072, by rfl⟩ : syracuseStep 23914763 = 35872145) B35872145
theorem B1657319 : Blo 1551473 1657319 := bstep (se 1 (by rfl) ⟨1242989, by rfl⟩ : syracuseStep 1657319 = 2485979) B2485979
theorem B5237405 : Blo 1551473 5237405 := bstep (se 3 (by rfl) ⟨982013, by rfl⟩ : syracuseStep 5237405 = 1964027) B1964027
theorem B5892871 : Blo 1551473 5892871 := bstep (se 1 (by rfl) ⟨4419653, by rfl⟩ : syracuseStep 5892871 = 8839307) B8839307
theorem B5893145 : Blo 1551473 5893145 := bstep (se 2 (by rfl) ⟨2209929, by rfl⟩ : syracuseStep 5893145 = 4419859) B4419859
theorem B1551551 : Blo 1551473 1551551 := bstep (se 1 (by rfl) ⟨1163663, by rfl⟩ : syracuseStep 1551551 = 2327327) B2327327
theorem B1551567 : Blo 1551473 1551567 := bstep (se 1 (by rfl) ⟨1163675, by rfl⟩ : syracuseStep 1551567 = 2327351) B2327351
theorem B2329919 : Blo 1551473 2329919 := bstep (se 1 (by rfl) ⟨1747439, by rfl⟩ : syracuseStep 2329919 = 3494879) B3494879
theorem B1551687 : Blo 1551473 1551687 := bstep (se 1 (by rfl) ⟨1163765, by rfl⟩ : syracuseStep 1551687 = 2327531) B2327531
theorem B22384187 : Blo 1551473 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B1552027 : Blo 1551473 1552027 := bstep (se 1 (by rfl) ⟨1164020, by rfl⟩ : syracuseStep 1552027 = 2328041) B2328041
theorem B100708069 : Blo 1551473 100708069 := bstep (se 4 (by rfl) ⟨9441381, by rfl⟩ : syracuseStep 100708069 = 18882763) B18882763
theorem B7458551 : Blo 1551473 7458551 := bstep (se 1 (by rfl) ⟨5593913, by rfl⟩ : syracuseStep 7458551 = 11187827) B11187827
theorem B65507177 : Blo 1551473 65507177 := bstep (se 2 (by rfl) ⟨24565191, by rfl⟩ : syracuseStep 65507177 = 49130383) B49130383
theorem B1552287 : Blo 1551473 1552287 := bstep (se 1 (by rfl) ⟨1164215, by rfl⟩ : syracuseStep 1552287 = 2328431) B2328431
theorem B1552411 : Blo 1551473 1552411 := bstep (se 1 (by rfl) ⟨1164308, by rfl⟩ : syracuseStep 1552411 = 2328617) B2328617
theorem B1552431 : Blo 1551473 1552431 := bstep (se 1 (by rfl) ⟨1164323, by rfl⟩ : syracuseStep 1552431 = 2328647) B2328647
theorem B1552551 : Blo 1551473 1552551 := bstep (se 1 (by rfl) ⟨1164413, by rfl⟩ : syracuseStep 1552551 = 2328827) B2328827
theorem B3494123 : Blo 1551473 3494123 := bstep (se 1 (by rfl) ⟨2620592, by rfl⟩ : syracuseStep 3494123 = 5241185) B5241185
theorem B1552687 : Blo 1551473 1552687 := bstep (se 1 (by rfl) ⟨1164515, by rfl⟩ : syracuseStep 1552687 = 2329031) B2329031
theorem B3453263 : Blo 1551473 3453263 := bstep (se 1 (by rfl) ⟨2589947, by rfl⟩ : syracuseStep 3453263 = 5179895) B5179895
theorem B8843681 : Blo 1551473 8843681 := bstep (se 2 (by rfl) ⟨3316380, by rfl⟩ : syracuseStep 8843681 = 6632761) B6632761
theorem B1552831 : Blo 1551473 1552831 := bstep (se 1 (by rfl) ⟨1164623, by rfl⟩ : syracuseStep 1552831 = 2329247) B2329247
theorem B1552863 : Blo 1551473 1552863 := bstep (se 1 (by rfl) ⟨1164647, by rfl⟩ : syracuseStep 1552863 = 2329295) B2329295
theorem B1552927 : Blo 1551473 1552927 := bstep (se 1 (by rfl) ⟨1164695, by rfl⟩ : syracuseStep 1552927 = 2329391) B2329391
theorem B5239403 : Blo 1551473 5239403 := bstep (se 1 (by rfl) ⟨3929552, by rfl⟩ : syracuseStep 5239403 = 7859105) B7859105
theorem B1553007 : Blo 1551473 1553007 := bstep (se 1 (by rfl) ⟨1164755, by rfl⟩ : syracuseStep 1553007 = 2329511) B2329511
theorem B1553127 : Blo 1551473 1553127 := bstep (se 1 (by rfl) ⟨1164845, by rfl⟩ : syracuseStep 1553127 = 2329691) B2329691
theorem B1553179 : Blo 1551473 1553179 := bstep (se 1 (by rfl) ⟨1164884, by rfl⟩ : syracuseStep 1553179 = 2329769) B2329769
theorem B75543353 : Blo 1551473 75543353 := bstep (se 2 (by rfl) ⟨28328757, by rfl⟩ : syracuseStep 75543353 = 56657515) B56657515
theorem B2618203 : Blo 1551473 2618203 := bstep (se 1 (by rfl) ⟨1963652, by rfl⟩ : syracuseStep 2618203 = 3927305) B3927305
theorem B3494753 : Blo 1551473 3494753 := bstep (se 2 (by rfl) ⟨1310532, by rfl⟩ : syracuseStep 3494753 = 2621065) B2621065
theorem B1553455 : Blo 1551473 1553455 := bstep (se 1 (by rfl) ⟨1165091, by rfl⟩ : syracuseStep 1553455 = 2330183) B2330183
theorem B3495095 : Blo 1551473 3495095 := bstep (se 1 (by rfl) ⟨2621321, by rfl⟩ : syracuseStep 3495095 = 5242643) B5242643
theorem B7861535 : Blo 1551473 7861535 := bstep (se 1 (by rfl) ⟨5896151, by rfl⟩ : syracuseStep 7861535 = 11792303) B11792303
theorem B11793761 : Blo 1551473 11793761 := bstep (se 2 (by rfl) ⟨4422660, by rfl⟩ : syracuseStep 11793761 = 8845321) B8845321
theorem B2946527 : Blo 1551473 2946527 := bstep (se 1 (by rfl) ⟨2209895, by rfl⟩ : syracuseStep 2946527 = 4419791) B4419791
theorem B1865215 : Blo 1551473 1865215 := bstep (se 1 (by rfl) ⟨1398911, by rfl⟩ : syracuseStep 1865215 = 2797823) B2797823
theorem B3315305 : Blo 1551473 3315305 := bstep (se 2 (by rfl) ⟨1243239, by rfl⟩ : syracuseStep 3315305 = 2486479) B2486479
theorem B26515187 : Blo 1551473 26515187 := bstep (se 1 (by rfl) ⟨19886390, by rfl⟩ : syracuseStep 26515187 = 39772781) B39772781
theorem B5896061 : Blo 1551473 5896061 := bstep (se 3 (by rfl) ⟨1105511, by rfl⟩ : syracuseStep 5896061 = 2211023) B2211023
theorem B2619263 : Blo 1551473 2619263 := bstep (se 1 (by rfl) ⟨1964447, by rfl⟩ : syracuseStep 2619263 = 3928895) B3928895
theorem B5896091 : Blo 1551473 5896091 := bstep (se 1 (by rfl) ⟨4422068, by rfl⟩ : syracuseStep 5896091 = 8844137) B8844137
theorem B2619371 : Blo 1551473 2619371 := bstep (se 1 (by rfl) ⟨1964528, by rfl⟩ : syracuseStep 2619371 = 3929057) B3929057
theorem B13449563 : Blo 1551473 13449563 := bstep (se 1 (by rfl) ⟨10087172, by rfl⟩ : syracuseStep 13449563 = 20174345) B20174345
theorem B54491771 : Blo 1551473 54491771 := bstep (se 1 (by rfl) ⟨40868828, by rfl⟩ : syracuseStep 54491771 = 81737657) B81737657
theorem B2620201 : Blo 1551473 2620201 := bstep (se 2 (by rfl) ⟨982575, by rfl⟩ : syracuseStep 2620201 = 1965151) B1965151
theorem B7855055 : Blo 1551473 7855055 := bstep (se 1 (by rfl) ⟨5891291, by rfl⟩ : syracuseStep 7855055 = 11782583) B11782583
theorem B14154857 : Blo 1551473 14154857 := bstep (se 2 (by rfl) ⟨5308071, by rfl⟩ : syracuseStep 14154857 = 10616143) B10616143
theorem B2948251 : Blo 1551473 2948251 := bstep (se 1 (by rfl) ⟨2211188, by rfl⟩ : syracuseStep 2948251 = 4422377) B4422377
theorem B21232991 : Blo 1551473 21232991 := bstep (se 1 (by rfl) ⟨15924743, by rfl⟩ : syracuseStep 21232991 = 31849487) B31849487
theorem B2620775 : Blo 1551473 2620775 := bstep (se 1 (by rfl) ⟨1965581, by rfl⟩ : syracuseStep 2620775 = 3931163) B3931163
theorem B1916399 : Blo 1551473 1916399 := bstep (se 1 (by rfl) ⟨1437299, by rfl⟩ : syracuseStep 1916399 = 2874599) B2874599
theorem B17694287 : Blo 1551473 17694287 := bstep (se 1 (by rfl) ⟨13270715, by rfl⟩ : syracuseStep 17694287 = 26541431) B26541431
theorem B2588297 : Blo 1551473 2588297 := bstep (se 2 (by rfl) ⟨970611, by rfl⟩ : syracuseStep 2588297 = 1941223) B1941223
theorem B11787929 : Blo 1551473 11787929 := bstep (se 2 (by rfl) ⟨4420473, by rfl⟩ : syracuseStep 11787929 = 8840947) B8840947
theorem B5242535 : Blo 1551473 5242535 := bstep (se 1 (by rfl) ⟨3931901, by rfl⟩ : syracuseStep 5242535 = 7863803) B7863803
theorem B181567169 : Blo 1551473 181567169 := bstep (se 2 (by rfl) ⟨68087688, by rfl⟩ : syracuseStep 181567169 = 136175377) B136175377
theorem B10616741 : Blo 1551473 10616741 := bstep (se 4 (by rfl) ⟨995319, by rfl⟩ : syracuseStep 10616741 = 1990639) B1990639
theorem B9953219 : Blo 1551473 9953219 := bstep (se 1 (by rfl) ⟨7464914, by rfl⟩ : syracuseStep 9953219 = 14929829) B14929829
theorem B2302175 : Blo 1551473 2302175 := bstep (se 1 (by rfl) ⟨1726631, by rfl⟩ : syracuseStep 2302175 = 3453263) B3453263
theorem B16785893 : Blo 1551473 16785893 := bstep (se 4 (by rfl) ⟨1573677, by rfl⟩ : syracuseStep 16785893 = 3147355) B3147355
theorem B2327279 : Blo 1551473 2327279 := bstep (se 1 (by rfl) ⟨1745459, by rfl⟩ : syracuseStep 2327279 = 3490919) B3490919
theorem B2327417 : Blo 1551473 2327417 := bstep (se 2 (by rfl) ⟨872781, by rfl⟩ : syracuseStep 2327417 = 1745563) B1745563
theorem B7857161 : Blo 1551473 7857161 := bstep (se 2 (by rfl) ⟨2946435, by rfl⟩ : syracuseStep 7857161 = 5892871) B5892871
theorem B3490937 : Blo 1551473 3490937 := bstep (se 2 (by rfl) ⟨1309101, by rfl⟩ : syracuseStep 3490937 = 2618203) B2618203
theorem B2327711 : Blo 1551473 2327711 := bstep (se 1 (by rfl) ⟨1745783, by rfl⟩ : syracuseStep 2327711 = 3491567) B3491567
theorem B1746175 : Blo 1551473 1746175 := bstep (se 1 (by rfl) ⟨1309631, by rfl⟩ : syracuseStep 1746175 = 2619263) B2619263
theorem B2327879 : Blo 1551473 2327879 := bstep (se 1 (by rfl) ⟨1745909, by rfl⟩ : syracuseStep 2327879 = 3491819) B3491819
theorem B1746247 : Blo 1551473 1746247 := bstep (se 1 (by rfl) ⟨1309685, by rfl⟩ : syracuseStep 1746247 = 2619371) B2619371
theorem B27608501 : Blo 1551473 27608501 := bstep (se 5 (by rfl) ⟨1294148, by rfl⟩ : syracuseStep 27608501 = 2588297) B2588297
theorem B2835967 : Blo 1551473 2835967 := bstep (se 1 (by rfl) ⟨2126975, by rfl⟩ : syracuseStep 2835967 = 4253951) B4253951
theorem B15943175 : Blo 1551473 15943175 := bstep (se 1 (by rfl) ⟨11957381, by rfl⟩ : syracuseStep 15943175 = 23914763) B23914763
theorem B3491603 : Blo 1551473 3491603 := bstep (se 1 (by rfl) ⟨2618702, by rfl⟩ : syracuseStep 3491603 = 5237405) B5237405
theorem B5236703 : Blo 1551473 5236703 := bstep (se 1 (by rfl) ⟨3927527, by rfl⟩ : syracuseStep 5236703 = 7855055) B7855055
theorem B1747183 : Blo 1551473 1747183 := bstep (se 1 (by rfl) ⟨1310387, by rfl⟩ : syracuseStep 1747183 = 2620775) B2620775
theorem B134277425 : Blo 1551473 134277425 := bstep (se 2 (by rfl) ⟨50354034, by rfl⟩ : syracuseStep 134277425 = 100708069) B100708069
theorem B7858619 : Blo 1551473 7858619 := bstep (se 1 (by rfl) ⟨5893964, by rfl⟩ : syracuseStep 7858619 = 11787929) B11787929
theorem B14748257 : Blo 1551473 14748257 := bstep (se 2 (by rfl) ⟨5530596, by rfl⟩ : syracuseStep 14748257 = 11061193) B11061193
theorem B2329415 : Blo 1551473 2329415 := bstep (se 1 (by rfl) ⟨1747061, by rfl⟩ : syracuseStep 2329415 = 3494123) B3494123
theorem B3492935 : Blo 1551473 3492935 := bstep (se 1 (by rfl) ⟨2619701, by rfl⟩ : syracuseStep 3492935 = 5239403) B5239403
theorem B12758161 : Blo 1551473 12758161 := bstep (se 2 (by rfl) ⟨4784310, by rfl⟩ : syracuseStep 12758161 = 9568621) B9568621
theorem B3927275 : Blo 1551473 3927275 := bstep (se 1 (by rfl) ⟨2945456, by rfl⟩ : syracuseStep 3927275 = 5890913) B5890913
theorem B2239723 : Blo 1551473 2239723 := bstep (se 1 (by rfl) ⟨1679792, by rfl⟩ : syracuseStep 2239723 = 3359585) B3359585
theorem B2329835 : Blo 1551473 2329835 := bstep (se 1 (by rfl) ⟨1747376, by rfl⟩ : syracuseStep 2329835 = 3494753) B3494753
theorem B8842679 : Blo 1551473 8842679 := bstep (se 1 (by rfl) ⟨6632009, by rfl⟩ : syracuseStep 8842679 = 13264019) B13264019
theorem B3927487 : Blo 1551473 3927487 := bstep (se 1 (by rfl) ⟨2945615, by rfl⟩ : syracuseStep 3927487 = 5891231) B5891231
theorem B2330063 : Blo 1551473 2330063 := bstep (se 1 (by rfl) ⟨1747547, by rfl⟩ : syracuseStep 2330063 = 3495095) B3495095
theorem B3493601 : Blo 1551473 3493601 := bstep (se 2 (by rfl) ⟨1310100, by rfl⟩ : syracuseStep 3493601 = 2620201) B2620201
theorem B28340063 : Blo 1551473 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B4419517 : Blo 1551473 4419517 := bstep (se 3 (by rfl) ⟨828659, by rfl⟩ : syracuseStep 4419517 = 1657319) B1657319
theorem B8958107 : Blo 1551473 8958107 := bstep (se 1 (by rfl) ⟨6718580, by rfl⟩ : syracuseStep 8958107 = 13437161) B13437161
theorem B8966375 : Blo 1551473 8966375 := bstep (se 1 (by rfl) ⟨6724781, by rfl⟩ : syracuseStep 8966375 = 13449563) B13449563
theorem B36327847 : Blo 1551473 36327847 := bstep (se 1 (by rfl) ⟨27245885, by rfl⟩ : syracuseStep 36327847 = 54491771) B54491771
theorem B2486953 : Blo 1551473 2486953 := bstep (se 2 (by rfl) ⟨932607, by rfl⟩ : syracuseStep 2486953 = 1865215) B1865215
theorem B3928763 : Blo 1551473 3928763 := bstep (se 1 (by rfl) ⟨2946572, by rfl⟩ : syracuseStep 3928763 = 5893145) B5893145
theorem B1553279 : Blo 1551473 1553279 := bstep (se 1 (by rfl) ⟨1164959, by rfl⟩ : syracuseStep 1553279 = 2329919) B2329919
theorem B14922791 : Blo 1551473 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B3495023 : Blo 1551473 3495023 := bstep (se 1 (by rfl) ⟨2621267, by rfl⟩ : syracuseStep 3495023 = 5242535) B5242535
theorem B42472997 : Blo 1551473 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B5895787 : Blo 1551473 5895787 := bstep (se 1 (by rfl) ⟨4421840, by rfl⟩ : syracuseStep 5895787 = 8843681) B8843681
theorem B15939233 : Blo 1551473 15939233 := bstep (se 2 (by rfl) ⟨5977212, by rfl⟩ : syracuseStep 15939233 = 11954425) B11954425
theorem B50362235 : Blo 1551473 50362235 := bstep (se 1 (by rfl) ⟨37771676, by rfl⟩ : syracuseStep 50362235 = 75543353) B75543353
theorem B3315647 : Blo 1551473 3315647 := bstep (se 1 (by rfl) ⟨2486735, by rfl⟩ : syracuseStep 3315647 = 4973471) B4973471
theorem B5241023 : Blo 1551473 5241023 := bstep (se 1 (by rfl) ⟨3930767, by rfl⟩ : syracuseStep 5241023 = 7861535) B7861535
theorem B7862507 : Blo 1551473 7862507 := bstep (se 1 (by rfl) ⟨5896880, by rfl⟩ : syracuseStep 7862507 = 11793761) B11793761
theorem B1964351 : Blo 1551473 1964351 := bstep (se 1 (by rfl) ⟨1473263, by rfl⟩ : syracuseStep 1964351 = 2946527) B2946527
theorem B2210203 : Blo 1551473 2210203 := bstep (se 1 (by rfl) ⟨1657652, by rfl⟩ : syracuseStep 2210203 = 3315305) B3315305
theorem B17676791 : Blo 1551473 17676791 := bstep (se 1 (by rfl) ⟨13257593, by rfl⟩ : syracuseStep 17676791 = 26515187) B26515187
theorem B3930707 : Blo 1551473 3930707 := bstep (se 1 (by rfl) ⟨2948030, by rfl⟩ : syracuseStep 3930707 = 5896061) B5896061
theorem B3930727 : Blo 1551473 3930727 := bstep (se 1 (by rfl) ⟨2948045, by rfl⟩ : syracuseStep 3930727 = 5896091) B5896091
theorem B5110397 : Blo 1551473 5110397 := bstep (se 3 (by rfl) ⟨958199, by rfl⟩ : syracuseStep 5110397 = 1916399) B1916399
theorem B3931001 : Blo 1551473 3931001 := bstep (se 2 (by rfl) ⟨1474125, by rfl⟩ : syracuseStep 3931001 = 2948251) B2948251
theorem B9436571 : Blo 1551473 9436571 := bstep (se 1 (by rfl) ⟨7077428, by rfl⟩ : syracuseStep 9436571 = 14154857) B14154857
theorem B14155327 : Blo 1551473 14155327 := bstep (se 1 (by rfl) ⟨10616495, by rfl⟩ : syracuseStep 14155327 = 21232991) B21232991
theorem B174685805 : Blo 1551473 174685805 := bstep (se 3 (by rfl) ⟨32753588, by rfl⟩ : syracuseStep 174685805 = 65507177) B65507177
theorem B11796191 : Blo 1551473 11796191 := bstep (se 1 (by rfl) ⟨8847143, by rfl⟩ : syracuseStep 11796191 = 17694287) B17694287
theorem B121044779 : Blo 1551473 121044779 := bstep (se 1 (by rfl) ⟨90783584, by rfl⟩ : syracuseStep 121044779 = 181567169) B181567169
theorem B4972367 : Blo 1551473 4972367 := bstep (se 1 (by rfl) ⟨3729275, by rfl⟩ : syracuseStep 4972367 = 7458551) B7458551
theorem B7077827 : Blo 1551473 7077827 := bstep (se 1 (by rfl) ⟨5308370, by rfl⟩ : syracuseStep 7077827 = 10616741) B10616741
theorem B6635479 : Blo 1551473 6635479 := bstep (se 1 (by rfl) ⟨4976609, by rfl⟩ : syracuseStep 6635479 = 9953219) B9953219
theorem B5972071 : Blo 1551473 5972071 := bstep (se 1 (by rfl) ⟨4479053, by rfl⟩ : syracuseStep 5972071 = 8958107) B8958107
theorem B11190595 : Blo 1551473 11190595 := bstep (se 1 (by rfl) ⟨8392946, by rfl⟩ : syracuseStep 11190595 = 16785893) B16785893
theorem B2327291 : Blo 1551473 2327291 := bstep (se 1 (by rfl) ⟨1745468, by rfl⟩ : syracuseStep 2327291 = 3490937) B3490937
theorem B10626155 : Blo 1551473 10626155 := bstep (se 1 (by rfl) ⟨7969616, by rfl⟩ : syracuseStep 10626155 = 15939233) B15939233
theorem B2327735 : Blo 1551473 2327735 := bstep (se 1 (by rfl) ⟨1745801, by rfl⟩ : syracuseStep 2327735 = 3491603) B3491603
theorem B11945189 : Blo 1551473 11945189 := bstep (se 4 (by rfl) ⟨1119861, by rfl⟩ : syracuseStep 11945189 = 2239723) B2239723
theorem B3491135 : Blo 1551473 3491135 := bstep (se 1 (by rfl) ⟨2618351, by rfl⟩ : syracuseStep 3491135 = 5236703) B5236703
theorem B2328233 : Blo 1551473 2328233 := bstep (se 2 (by rfl) ⟨873087, by rfl⟩ : syracuseStep 2328233 = 1746175) B1746175
theorem B2328329 : Blo 1551473 2328329 := bstep (se 2 (by rfl) ⟨873123, by rfl⟩ : syracuseStep 2328329 = 1746247) B1746247
theorem B5236649 : Blo 1551473 5236649 := bstep (se 2 (by rfl) ⟨1963743, by rfl⟩ : syracuseStep 5236649 = 3927487) B3927487
theorem B2328623 : Blo 1551473 2328623 := bstep (se 1 (by rfl) ⟨1746467, by rfl⟩ : syracuseStep 2328623 = 3492935) B3492935
theorem B2329067 : Blo 1551473 2329067 := bstep (se 1 (by rfl) ⟨1746800, by rfl⟩ : syracuseStep 2329067 = 3493601) B3493601
theorem B18893375 : Blo 1551473 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B5892689 : Blo 1551473 5892689 := bstep (se 2 (by rfl) ⟨2209758, by rfl⟩ : syracuseStep 5892689 = 4419517) B4419517
theorem B2329577 : Blo 1551473 2329577 := bstep (se 2 (by rfl) ⟨873591, by rfl⟩ : syracuseStep 2329577 = 1747183) B1747183
theorem B1551519 : Blo 1551473 1551519 := bstep (se 1 (by rfl) ⟨1163639, by rfl⟩ : syracuseStep 1551519 = 2327279) B2327279
theorem B1551611 : Blo 1551473 1551611 := bstep (se 1 (by rfl) ⟨1163708, by rfl⟩ : syracuseStep 1551611 = 2327417) B2327417
theorem B6139133 : Blo 1551473 6139133 := bstep (se 3 (by rfl) ⟨1151087, by rfl⟩ : syracuseStep 6139133 = 2302175) B2302175
theorem B5238107 : Blo 1551473 5238107 := bstep (se 1 (by rfl) ⟨3928580, by rfl⟩ : syracuseStep 5238107 = 7857161) B7857161
theorem B9948527 : Blo 1551473 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B2330015 : Blo 1551473 2330015 := bstep (se 1 (by rfl) ⟨1747511, by rfl⟩ : syracuseStep 2330015 = 3495023) B3495023
theorem B1551807 : Blo 1551473 1551807 := bstep (se 1 (by rfl) ⟨1163855, by rfl⟩ : syracuseStep 1551807 = 2327711) B2327711
theorem B5238269 : Blo 1551473 5238269 := bstep (se 3 (by rfl) ⟨982175, by rfl⟩ : syracuseStep 5238269 = 1964351) B1964351
theorem B1551919 : Blo 1551473 1551919 := bstep (se 1 (by rfl) ⟨1163939, by rfl⟩ : syracuseStep 1551919 = 2327879) B2327879
theorem B10628783 : Blo 1551473 10628783 := bstep (se 1 (by rfl) ⟨7971587, by rfl⟩ : syracuseStep 10628783 = 15943175) B15943175
theorem B28315331 : Blo 1551473 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B33574823 : Blo 1551473 33574823 := bstep (se 1 (by rfl) ⟨25181117, by rfl⟩ : syracuseStep 33574823 = 50362235) B50362235
theorem B3494015 : Blo 1551473 3494015 := bstep (se 1 (by rfl) ⟨2620511, by rfl⟩ : syracuseStep 3494015 = 5241023) B5241023
theorem B17010881 : Blo 1551473 17010881 := bstep (se 2 (by rfl) ⟨6379080, by rfl⟩ : syracuseStep 17010881 = 12758161) B12758161
theorem B89518283 : Blo 1551473 89518283 := bstep (se 1 (by rfl) ⟨67138712, by rfl⟩ : syracuseStep 89518283 = 134277425) B134277425
theorem B5239079 : Blo 1551473 5239079 := bstep (se 1 (by rfl) ⟨3929309, by rfl⟩ : syracuseStep 5239079 = 7858619) B7858619
theorem B11784527 : Blo 1551473 11784527 := bstep (se 1 (by rfl) ⟨8838395, by rfl⟩ : syracuseStep 11784527 = 17676791) B17676791
theorem B1552943 : Blo 1551473 1552943 := bstep (se 1 (by rfl) ⟨1164707, by rfl⟩ : syracuseStep 1552943 = 2329415) B2329415
theorem B3781289 : Blo 1551473 3781289 := bstep (se 2 (by rfl) ⟨1417983, by rfl⟩ : syracuseStep 3781289 = 2835967) B2835967
theorem B7861049 : Blo 1551473 7861049 := bstep (se 2 (by rfl) ⟨2947893, by rfl⟩ : syracuseStep 7861049 = 5895787) B5895787
theorem B2618183 : Blo 1551473 2618183 := bstep (se 1 (by rfl) ⟨1963637, by rfl⟩ : syracuseStep 2618183 = 3927275) B3927275
theorem B1553223 : Blo 1551473 1553223 := bstep (se 1 (by rfl) ⟨1164917, by rfl⟩ : syracuseStep 1553223 = 2329835) B2329835
theorem B13259645 : Blo 1551473 13259645 := bstep (se 3 (by rfl) ⟨2486183, by rfl⟩ : syracuseStep 13259645 = 4972367) B4972367
theorem B5895119 : Blo 1551473 5895119 := bstep (se 1 (by rfl) ⟨4421339, by rfl⟩ : syracuseStep 5895119 = 8842679) B8842679
theorem B1553375 : Blo 1551473 1553375 := bstep (se 1 (by rfl) ⟨1165031, by rfl⟩ : syracuseStep 1553375 = 2330063) B2330063
theorem B80696519 : Blo 1551473 80696519 := bstep (se 1 (by rfl) ⟨60522389, by rfl⟩ : syracuseStep 80696519 = 121044779) B121044779
theorem B5977583 : Blo 1551473 5977583 := bstep (se 1 (by rfl) ⟨4483187, by rfl⟩ : syracuseStep 5977583 = 8966375) B8966375
theorem B2619175 : Blo 1551473 2619175 := bstep (se 1 (by rfl) ⟨1964381, by rfl⟩ : syracuseStep 2619175 = 3928763) B3928763
theorem B2946937 : Blo 1551473 2946937 := bstep (se 2 (by rfl) ⟨1105101, by rfl⟩ : syracuseStep 2946937 = 2210203) B2210203
theorem B48437129 : Blo 1551473 48437129 := bstep (se 2 (by rfl) ⟨18163923, by rfl⟩ : syracuseStep 48437129 = 36327847) B36327847
theorem B5240969 : Blo 1551473 5240969 := bstep (se 2 (by rfl) ⟨1965363, by rfl⟩ : syracuseStep 5240969 = 3930727) B3930727
theorem B3315937 : Blo 1551473 3315937 := bstep (se 2 (by rfl) ⟨1243476, by rfl⟩ : syracuseStep 3315937 = 2486953) B2486953
theorem B18405667 : Blo 1551473 18405667 := bstep (se 1 (by rfl) ⟨13804250, by rfl⟩ : syracuseStep 18405667 = 27608501) B27608501
theorem B2210431 : Blo 1551473 2210431 := bstep (se 1 (by rfl) ⟨1657823, by rfl⟩ : syracuseStep 2210431 = 3315647) B3315647
theorem B5241671 : Blo 1551473 5241671 := bstep (se 1 (by rfl) ⟨3931253, by rfl⟩ : syracuseStep 5241671 = 7862507) B7862507
theorem B39328685 : Blo 1551473 39328685 := bstep (se 3 (by rfl) ⟨7374128, by rfl⟩ : syracuseStep 39328685 = 14748257) B14748257
theorem B2620471 : Blo 1551473 2620471 := bstep (se 1 (by rfl) ⟨1965353, by rfl⟩ : syracuseStep 2620471 = 3930707) B3930707
theorem B3406931 : Blo 1551473 3406931 := bstep (se 1 (by rfl) ⟨2555198, by rfl⟩ : syracuseStep 3406931 = 5110397) B5110397
theorem B2620667 : Blo 1551473 2620667 := bstep (se 1 (by rfl) ⟨1965500, by rfl⟩ : syracuseStep 2620667 = 3931001) B3931001
theorem B18873769 : Blo 1551473 18873769 := bstep (se 2 (by rfl) ⟨7077663, by rfl⟩ : syracuseStep 18873769 = 14155327) B14155327
theorem B6291047 : Blo 1551473 6291047 := bstep (se 1 (by rfl) ⟨4718285, by rfl⟩ : syracuseStep 6291047 = 9436571) B9436571
theorem B116457203 : Blo 1551473 116457203 := bstep (se 1 (by rfl) ⟨87342902, by rfl⟩ : syracuseStep 116457203 = 174685805) B174685805
theorem B7864127 : Blo 1551473 7864127 := bstep (se 1 (by rfl) ⟨5898095, by rfl⟩ : syracuseStep 7864127 = 11796191) B11796191
theorem B18874205 : Blo 1551473 18874205 := bstep (se 3 (by rfl) ⟨3538913, by rfl⟩ : syracuseStep 18874205 = 7077827) B7077827
theorem B8847305 : Blo 1551473 8847305 := bstep (se 2 (by rfl) ⟨3317739, by rfl⟩ : syracuseStep 8847305 = 6635479) B6635479
theorem B59678855 : Blo 1551473 59678855 := bstep (se 1 (by rfl) ⟨44759141, by rfl⟩ : syracuseStep 59678855 = 89518283) B89518283
theorem B7962761 : Blo 1551473 7962761 := bstep (se 2 (by rfl) ⟨2986035, by rfl⟩ : syracuseStep 7962761 = 5972071) B5972071
theorem B7856351 : Blo 1551473 7856351 := bstep (se 1 (by rfl) ⟨5892263, by rfl⟩ : syracuseStep 7856351 = 11784527) B11784527
theorem B1745455 : Blo 1551473 1745455 := bstep (se 1 (by rfl) ⟨1309091, by rfl⟩ : syracuseStep 1745455 = 2618183) B2618183
theorem B8839763 : Blo 1551473 8839763 := bstep (se 1 (by rfl) ⟨6629822, by rfl⟩ : syracuseStep 8839763 = 13259645) B13259645
theorem B53797679 : Blo 1551473 53797679 := bstep (se 1 (by rfl) ⟨40348259, by rfl⟩ : syracuseStep 53797679 = 80696519) B80696519
theorem B2327423 : Blo 1551473 2327423 := bstep (se 1 (by rfl) ⟨1745567, by rfl⟩ : syracuseStep 2327423 = 3491135) B3491135
theorem B3491099 : Blo 1551473 3491099 := bstep (se 1 (by rfl) ⟨2618324, by rfl⟩ : syracuseStep 3491099 = 5236649) B5236649
theorem B2271287 : Blo 1551473 2271287 := bstep (se 1 (by rfl) ⟨1703465, by rfl⟩ : syracuseStep 2271287 = 3406931) B3406931
theorem B1747111 : Blo 1551473 1747111 := bstep (se 1 (by rfl) ⟨1310333, by rfl⟩ : syracuseStep 1747111 = 2620667) B2620667
theorem B3492071 : Blo 1551473 3492071 := bstep (se 1 (by rfl) ⟨2619053, by rfl⟩ : syracuseStep 3492071 = 5238107) B5238107
theorem B3492179 : Blo 1551473 3492179 := bstep (se 1 (by rfl) ⟨2619134, by rfl⟩ : syracuseStep 3492179 = 5238269) B5238269
theorem B3492233 : Blo 1551473 3492233 := bstep (se 2 (by rfl) ⟨1309587, by rfl⟩ : syracuseStep 3492233 = 2619175) B2619175
theorem B18876887 : Blo 1551473 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B77638135 : Blo 1551473 77638135 := bstep (se 1 (by rfl) ⟨58228601, by rfl⟩ : syracuseStep 77638135 = 116457203) B116457203
theorem B22383215 : Blo 1551473 22383215 := bstep (se 1 (by rfl) ⟨16787411, by rfl⟩ : syracuseStep 22383215 = 33574823) B33574823
theorem B2329343 : Blo 1551473 2329343 := bstep (se 1 (by rfl) ⟨1747007, by rfl⟩ : syracuseStep 2329343 = 3494015) B3494015
theorem B11340587 : Blo 1551473 11340587 := bstep (se 1 (by rfl) ⟨8505440, by rfl⟩ : syracuseStep 11340587 = 17010881) B17010881
theorem B3492719 : Blo 1551473 3492719 := bstep (se 1 (by rfl) ⟨2619539, by rfl⟩ : syracuseStep 3492719 = 5239079) B5239079
theorem B14920793 : Blo 1551473 14920793 := bstep (se 2 (by rfl) ⟨5595297, by rfl⟩ : syracuseStep 14920793 = 11190595) B11190595
theorem B1551527 : Blo 1551473 1551527 := bstep (se 1 (by rfl) ⟨1163645, by rfl⟩ : syracuseStep 1551527 = 2327291) B2327291
theorem B31853837 : Blo 1551473 31853837 := bstep (se 3 (by rfl) ⟨5972594, by rfl⟩ : syracuseStep 31853837 = 11945189) B11945189
theorem B1551823 : Blo 1551473 1551823 := bstep (se 1 (by rfl) ⟨1163867, by rfl⟩ : syracuseStep 1551823 = 2327735) B2327735
theorem B3985055 : Blo 1551473 3985055 := bstep (se 1 (by rfl) ⟨2988791, by rfl⟩ : syracuseStep 3985055 = 5977583) B5977583
theorem B1552155 : Blo 1551473 1552155 := bstep (se 1 (by rfl) ⟨1164116, by rfl⟩ : syracuseStep 1552155 = 2328233) B2328233
theorem B1552219 : Blo 1551473 1552219 := bstep (se 1 (by rfl) ⟨1164164, by rfl⟩ : syracuseStep 1552219 = 2328329) B2328329
theorem B1552415 : Blo 1551473 1552415 := bstep (se 1 (by rfl) ⟨1164311, by rfl⟩ : syracuseStep 1552415 = 2328623) B2328623
theorem B3493961 : Blo 1551473 3493961 := bstep (se 2 (by rfl) ⟨1310235, by rfl⟩ : syracuseStep 3493961 = 2620471) B2620471
theorem B3493979 : Blo 1551473 3493979 := bstep (se 1 (by rfl) ⟨2620484, by rfl⟩ : syracuseStep 3493979 = 5240969) B5240969
theorem B1552711 : Blo 1551473 1552711 := bstep (se 1 (by rfl) ⟨1164533, by rfl⟩ : syracuseStep 1552711 = 2329067) B2329067
theorem B12595583 : Blo 1551473 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B3928459 : Blo 1551473 3928459 := bstep (se 1 (by rfl) ⟨2946344, by rfl⟩ : syracuseStep 3928459 = 5892689) B5892689
theorem B3494447 : Blo 1551473 3494447 := bstep (se 1 (by rfl) ⟨2620835, by rfl⟩ : syracuseStep 3494447 = 5241671) B5241671
theorem B26219123 : Blo 1551473 26219123 := bstep (se 1 (by rfl) ⟨19664342, by rfl⟩ : syracuseStep 26219123 = 39328685) B39328685
theorem B1553051 : Blo 1551473 1553051 := bstep (se 1 (by rfl) ⟨1164788, by rfl⟩ : syracuseStep 1553051 = 2329577) B2329577
theorem B4092755 : Blo 1551473 4092755 := bstep (se 1 (by rfl) ⟨3069566, by rfl⟩ : syracuseStep 4092755 = 6139133) B6139133
theorem B6632351 : Blo 1551473 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B1553343 : Blo 1551473 1553343 := bstep (se 1 (by rfl) ⟨1165007, by rfl⟩ : syracuseStep 1553343 = 2330015) B2330015
theorem B3929249 : Blo 1551473 3929249 := bstep (se 2 (by rfl) ⟨1473468, by rfl⟩ : syracuseStep 3929249 = 2946937) B2946937
theorem B4421249 : Blo 1551473 4421249 := bstep (se 2 (by rfl) ⟨1657968, by rfl⟩ : syracuseStep 4421249 = 3315937) B3315937
theorem B24540889 : Blo 1551473 24540889 := bstep (se 2 (by rfl) ⟨9202833, by rfl⟩ : syracuseStep 24540889 = 18405667) B18405667
theorem B5240699 : Blo 1551473 5240699 := bstep (se 1 (by rfl) ⟨3930524, by rfl⟩ : syracuseStep 5240699 = 7861049) B7861049
theorem B3930079 : Blo 1551473 3930079 := bstep (se 1 (by rfl) ⟨2947559, by rfl⟩ : syracuseStep 3930079 = 5895119) B5895119
theorem B7084103 : Blo 1551473 7084103 := bstep (se 1 (by rfl) ⟨5313077, by rfl⟩ : syracuseStep 7084103 = 10626155) B10626155
theorem B2947241 : Blo 1551473 2947241 := bstep (se 2 (by rfl) ⟨1105215, by rfl⟩ : syracuseStep 2947241 = 2210431) B2210431
theorem B32291419 : Blo 1551473 32291419 := bstep (se 1 (by rfl) ⟨24218564, by rfl⟩ : syracuseStep 32291419 = 48437129) B48437129
theorem B10083437 : Blo 1551473 10083437 := bstep (se 3 (by rfl) ⟨1890644, by rfl⟩ : syracuseStep 10083437 = 3781289) B3781289
theorem B25165025 : Blo 1551473 25165025 := bstep (se 2 (by rfl) ⟨9436884, by rfl⟩ : syracuseStep 25165025 = 18873769) B18873769
theorem B4194031 : Blo 1551473 4194031 := bstep (se 1 (by rfl) ⟨3145523, by rfl⟩ : syracuseStep 4194031 = 6291047) B6291047
theorem B7085855 : Blo 1551473 7085855 := bstep (se 1 (by rfl) ⟨5314391, by rfl⟩ : syracuseStep 7085855 = 10628783) B10628783
theorem B5242751 : Blo 1551473 5242751 := bstep (se 1 (by rfl) ⟨3932063, by rfl⟩ : syracuseStep 5242751 = 7864127) B7864127
theorem B12582803 : Blo 1551473 12582803 := bstep (se 1 (by rfl) ⟨9437102, by rfl⟩ : syracuseStep 12582803 = 18874205) B18874205
theorem B5898203 : Blo 1551473 5898203 := bstep (se 1 (by rfl) ⟨4423652, by rfl⟩ : syracuseStep 5898203 = 8847305) B8847305
theorem B5308507 : Blo 1551473 5308507 := bstep (se 1 (by rfl) ⟨3981380, by rfl⟩ : syracuseStep 5308507 = 7962761) B7962761
theorem B18890941 : Blo 1551473 18890941 := bstep (se 3 (by rfl) ⟨3542051, by rfl⟩ : syracuseStep 18890941 = 7084103) B7084103
theorem B8397055 : Blo 1551473 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B35865119 : Blo 1551473 35865119 := bstep (se 1 (by rfl) ⟨26898839, by rfl⟩ : syracuseStep 35865119 = 53797679) B53797679
theorem B2327273 : Blo 1551473 2327273 := bstep (se 2 (by rfl) ⟨872727, by rfl⟩ : syracuseStep 2327273 = 1745455) B1745455
theorem B2327399 : Blo 1551473 2327399 := bstep (se 1 (by rfl) ⟨1745549, by rfl⟩ : syracuseStep 2327399 = 3491099) B3491099
theorem B2328047 : Blo 1551473 2328047 := bstep (se 1 (by rfl) ⟨1746035, by rfl⟩ : syracuseStep 2328047 = 3492071) B3492071
theorem B2328119 : Blo 1551473 2328119 := bstep (se 1 (by rfl) ⟨1746089, by rfl⟩ : syracuseStep 2328119 = 3492179) B3492179
theorem B2328155 : Blo 1551473 2328155 := bstep (se 1 (by rfl) ⟨1746116, by rfl⟩ : syracuseStep 2328155 = 3492233) B3492233
theorem B12584591 : Blo 1551473 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B2328479 : Blo 1551473 2328479 := bstep (se 1 (by rfl) ⟨1746359, by rfl⟩ : syracuseStep 2328479 = 3492719) B3492719
theorem B9947195 : Blo 1551473 9947195 := bstep (se 1 (by rfl) ⟨7460396, by rfl⟩ : syracuseStep 9947195 = 14920793) B14920793
theorem B21235891 : Blo 1551473 21235891 := bstep (se 1 (by rfl) ⟨15926918, by rfl⟩ : syracuseStep 21235891 = 31853837) B31853837
theorem B10914013 : Blo 1551473 10914013 := bstep (se 3 (by rfl) ⟨2046377, by rfl⟩ : syracuseStep 10914013 = 4092755) B4092755
theorem B32721185 : Blo 1551473 32721185 := bstep (se 2 (by rfl) ⟨12270444, by rfl⟩ : syracuseStep 32721185 = 24540889) B24540889
theorem B2656703 : Blo 1551473 2656703 := bstep (se 1 (by rfl) ⟨1992527, by rfl⟩ : syracuseStep 2656703 = 3985055) B3985055
theorem B2329307 : Blo 1551473 2329307 := bstep (se 1 (by rfl) ⟨1746980, by rfl⟩ : syracuseStep 2329307 = 3493961) B3493961
theorem B2329319 : Blo 1551473 2329319 := bstep (se 1 (by rfl) ⟨1746989, by rfl⟩ : syracuseStep 2329319 = 3493979) B3493979
theorem B6056765 : Blo 1551473 6056765 := bstep (se 3 (by rfl) ⟨1135643, by rfl⟩ : syracuseStep 6056765 = 2271287) B2271287
theorem B5237567 : Blo 1551473 5237567 := bstep (se 1 (by rfl) ⟨3928175, by rfl⟩ : syracuseStep 5237567 = 7856351) B7856351
theorem B2329481 : Blo 1551473 2329481 := bstep (se 2 (by rfl) ⟨873555, by rfl⟩ : syracuseStep 2329481 = 1747111) B1747111
theorem B2329631 : Blo 1551473 2329631 := bstep (se 1 (by rfl) ⟨1747223, by rfl⟩ : syracuseStep 2329631 = 3494447) B3494447
theorem B5893175 : Blo 1551473 5893175 := bstep (se 1 (by rfl) ⟨4419881, by rfl⟩ : syracuseStep 5893175 = 8839763) B8839763
theorem B5237945 : Blo 1551473 5237945 := bstep (se 2 (by rfl) ⟨1964229, by rfl⟩ : syracuseStep 5237945 = 3928459) B3928459
theorem B1551615 : Blo 1551473 1551615 := bstep (se 1 (by rfl) ⟨1163711, by rfl⟩ : syracuseStep 1551615 = 2327423) B2327423
theorem B103517513 : Blo 1551473 103517513 := bstep (se 2 (by rfl) ⟨38819067, by rfl⟩ : syracuseStep 103517513 = 77638135) B77638135
theorem B3493799 : Blo 1551473 3493799 := bstep (se 1 (by rfl) ⟨2620349, by rfl⟩ : syracuseStep 3493799 = 5240699) B5240699
theorem B14922143 : Blo 1551473 14922143 := bstep (se 1 (by rfl) ⟨11191607, by rfl⟩ : syracuseStep 14922143 = 22383215) B22383215
theorem B1552895 : Blo 1551473 1552895 := bstep (se 1 (by rfl) ⟨1164671, by rfl⟩ : syracuseStep 1552895 = 2329343) B2329343
theorem B6722291 : Blo 1551473 6722291 := bstep (se 1 (by rfl) ⟨5041718, by rfl⟩ : syracuseStep 6722291 = 10083437) B10083437
theorem B5592041 : Blo 1551473 5592041 := bstep (se 2 (by rfl) ⟨2097015, by rfl⟩ : syracuseStep 5592041 = 4194031) B4194031
theorem B4723903 : Blo 1551473 4723903 := bstep (se 1 (by rfl) ⟨3542927, by rfl⟩ : syracuseStep 4723903 = 7085855) B7085855
theorem B3495167 : Blo 1551473 3495167 := bstep (se 1 (by rfl) ⟨2621375, by rfl⟩ : syracuseStep 3495167 = 5242751) B5242751
theorem B5240105 : Blo 1551473 5240105 := bstep (se 2 (by rfl) ⟨1965039, by rfl⟩ : syracuseStep 5240105 = 3930079) B3930079
theorem B39785903 : Blo 1551473 39785903 := bstep (se 1 (by rfl) ⟨29839427, by rfl⟩ : syracuseStep 39785903 = 59678855) B59678855
theorem B17479415 : Blo 1551473 17479415 := bstep (se 1 (by rfl) ⟨13109561, by rfl⟩ : syracuseStep 17479415 = 26219123) B26219123
theorem B4421567 : Blo 1551473 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B2619499 : Blo 1551473 2619499 := bstep (se 1 (by rfl) ⟨1964624, by rfl⟩ : syracuseStep 2619499 = 3929249) B3929249
theorem B43055225 : Blo 1551473 43055225 := bstep (se 2 (by rfl) ⟨16145709, by rfl⟩ : syracuseStep 43055225 = 32291419) B32291419
theorem B2947499 : Blo 1551473 2947499 := bstep (se 1 (by rfl) ⟨2210624, by rfl⟩ : syracuseStep 2947499 = 4421249) B4421249
theorem B1964827 : Blo 1551473 1964827 := bstep (se 1 (by rfl) ⟨1473620, by rfl⟩ : syracuseStep 1964827 = 2947241) B2947241
theorem B7560391 : Blo 1551473 7560391 := bstep (se 1 (by rfl) ⟨5670293, by rfl⟩ : syracuseStep 7560391 = 11340587) B11340587
theorem B16776683 : Blo 1551473 16776683 := bstep (se 1 (by rfl) ⟨12582512, by rfl⟩ : syracuseStep 16776683 = 25165025) B25165025
theorem B8388535 : Blo 1551473 8388535 := bstep (se 1 (by rfl) ⟨6291401, by rfl⟩ : syracuseStep 8388535 = 12582803) B12582803
theorem B3932135 : Blo 1551473 3932135 := bstep (se 1 (by rfl) ⟨2949101, by rfl⟩ : syracuseStep 3932135 = 5898203) B5898203
theorem B28312037 : Blo 1551473 28312037 := bstep (se 4 (by rfl) ⟨2654253, by rfl⟩ : syracuseStep 28312037 = 5308507) B5308507
theorem B3728027 : Blo 1551473 3728027 := bstep (se 1 (by rfl) ⟨2796020, by rfl⟩ : syracuseStep 3728027 = 5592041) B5592041
theorem B8389727 : Blo 1551473 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B1771135 : Blo 1551473 1771135 := bstep (se 1 (by rfl) ⟨1328351, by rfl⟩ : syracuseStep 1771135 = 2656703) B2656703
theorem B3491711 : Blo 1551473 3491711 := bstep (se 1 (by rfl) ⟨2618783, by rfl⟩ : syracuseStep 3491711 = 5237567) B5237567
theorem B17926109 : Blo 1551473 17926109 := bstep (se 3 (by rfl) ⟨3361145, by rfl⟩ : syracuseStep 17926109 = 6722291) B6722291
theorem B3491963 : Blo 1551473 3491963 := bstep (se 1 (by rfl) ⟨2618972, by rfl⟩ : syracuseStep 3491963 = 5237945) B5237945
theorem B69011675 : Blo 1551473 69011675 := bstep (se 1 (by rfl) ⟨51758756, by rfl⟩ : syracuseStep 69011675 = 103517513) B103517513
theorem B11184455 : Blo 1551473 11184455 := bstep (se 1 (by rfl) ⟨8388341, by rfl⟩ : syracuseStep 11184455 = 16776683) B16776683
theorem B11790845 : Blo 1551473 11790845 := bstep (se 3 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 11790845 = 4421567) B4421567
theorem B11184713 : Blo 1551473 11184713 := bstep (se 2 (by rfl) ⟨4194267, by rfl⟩ : syracuseStep 11184713 = 8388535) B8388535
theorem B2329199 : Blo 1551473 2329199 := bstep (se 1 (by rfl) ⟨1746899, by rfl⟩ : syracuseStep 2329199 = 3493799) B3493799
theorem B3492665 : Blo 1551473 3492665 := bstep (se 2 (by rfl) ⟨1309749, by rfl⟩ : syracuseStep 3492665 = 2619499) B2619499
theorem B28314521 : Blo 1551473 28314521 := bstep (se 2 (by rfl) ⟨10617945, by rfl⟩ : syracuseStep 28314521 = 21235891) B21235891
theorem B9948095 : Blo 1551473 9948095 := bstep (se 1 (by rfl) ⟨7461071, by rfl⟩ : syracuseStep 9948095 = 14922143) B14922143
theorem B14552017 : Blo 1551473 14552017 := bstep (se 2 (by rfl) ⟨5457006, by rfl⟩ : syracuseStep 14552017 = 10914013) B10914013
theorem B1551515 : Blo 1551473 1551515 := bstep (se 1 (by rfl) ⟨1163636, by rfl⟩ : syracuseStep 1551515 = 2327273) B2327273
theorem B1551599 : Blo 1551473 1551599 := bstep (se 1 (by rfl) ⟨1163699, by rfl⟩ : syracuseStep 1551599 = 2327399) B2327399
theorem B2330111 : Blo 1551473 2330111 := bstep (se 1 (by rfl) ⟨1747583, by rfl⟩ : syracuseStep 2330111 = 3495167) B3495167
theorem B3493403 : Blo 1551473 3493403 := bstep (se 1 (by rfl) ⟨2620052, by rfl⟩ : syracuseStep 3493403 = 5240105) B5240105
theorem B1552031 : Blo 1551473 1552031 := bstep (se 1 (by rfl) ⟨1164023, by rfl⟩ : syracuseStep 1552031 = 2328047) B2328047
theorem B25194149 : Blo 1551473 25194149 := bstep (se 4 (by rfl) ⟨2361951, by rfl⟩ : syracuseStep 25194149 = 4723903) B4723903
theorem B1552079 : Blo 1551473 1552079 := bstep (se 1 (by rfl) ⟨1164059, by rfl⟩ : syracuseStep 1552079 = 2328119) B2328119
theorem B1552103 : Blo 1551473 1552103 := bstep (se 1 (by rfl) ⟨1164077, by rfl⟩ : syracuseStep 1552103 = 2328155) B2328155
theorem B1552319 : Blo 1551473 1552319 := bstep (se 1 (by rfl) ⟨1164239, by rfl⟩ : syracuseStep 1552319 = 2328479) B2328479
theorem B6631463 : Blo 1551473 6631463 := bstep (se 1 (by rfl) ⟨4973597, by rfl⟩ : syracuseStep 6631463 = 9947195) B9947195
theorem B10080521 : Blo 1551473 10080521 := bstep (se 2 (by rfl) ⟨3780195, by rfl⟩ : syracuseStep 10080521 = 7560391) B7560391
theorem B1552871 : Blo 1551473 1552871 := bstep (se 1 (by rfl) ⟨1164653, by rfl⟩ : syracuseStep 1552871 = 2329307) B2329307
theorem B1552879 : Blo 1551473 1552879 := bstep (se 1 (by rfl) ⟨1164659, by rfl⟩ : syracuseStep 1552879 = 2329319) B2329319
theorem B1552987 : Blo 1551473 1552987 := bstep (se 1 (by rfl) ⟨1164740, by rfl⟩ : syracuseStep 1552987 = 2329481) B2329481
theorem B1553087 : Blo 1551473 1553087 := bstep (se 1 (by rfl) ⟨1164815, by rfl⟩ : syracuseStep 1553087 = 2329631) B2329631
theorem B3928783 : Blo 1551473 3928783 := bstep (se 1 (by rfl) ⟨2946587, by rfl⟩ : syracuseStep 3928783 = 5893175) B5893175
theorem B25187921 : Blo 1551473 25187921 := bstep (se 2 (by rfl) ⟨9445470, by rfl⟩ : syracuseStep 25187921 = 18890941) B18890941
theorem B11196073 : Blo 1551473 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B23910079 : Blo 1551473 23910079 := bstep (se 1 (by rfl) ⟨17932559, by rfl⟩ : syracuseStep 23910079 = 35865119) B35865119
theorem B26523935 : Blo 1551473 26523935 := bstep (se 1 (by rfl) ⟨19892951, by rfl⟩ : syracuseStep 26523935 = 39785903) B39785903
theorem B2619769 : Blo 1551473 2619769 := bstep (se 2 (by rfl) ⟨982413, by rfl⟩ : syracuseStep 2619769 = 1964827) B1964827
theorem B28703483 : Blo 1551473 28703483 := bstep (se 1 (by rfl) ⟨21527612, by rfl⟩ : syracuseStep 28703483 = 43055225) B43055225
theorem B21814123 : Blo 1551473 21814123 := bstep (se 1 (by rfl) ⟨16360592, by rfl⟩ : syracuseStep 21814123 = 32721185) B32721185
theorem B1964999 : Blo 1551473 1964999 := bstep (se 1 (by rfl) ⟨1473749, by rfl⟩ : syracuseStep 1964999 = 2947499) B2947499
theorem B4037843 : Blo 1551473 4037843 := bstep (se 1 (by rfl) ⟨3028382, by rfl⟩ : syracuseStep 4037843 = 6056765) B6056765
theorem B46611773 : Blo 1551473 46611773 := bstep (se 3 (by rfl) ⟨8739707, by rfl⟩ : syracuseStep 46611773 = 17479415) B17479415
theorem B2621423 : Blo 1551473 2621423 := bstep (se 1 (by rfl) ⟨1966067, by rfl⟩ : syracuseStep 2621423 = 3932135) B3932135
theorem B18874691 : Blo 1551473 18874691 := bstep (se 1 (by rfl) ⟨14156018, by rfl⟩ : syracuseStep 18874691 = 28312037) B28312037
theorem B9446053 : Blo 1551473 9446053 := bstep (se 4 (by rfl) ⟨885567, by rfl⟩ : syracuseStep 9446053 = 1771135) B1771135
theorem B2327807 : Blo 1551473 2327807 := bstep (se 1 (by rfl) ⟨1745855, by rfl⟩ : syracuseStep 2327807 = 3491711) B3491711
theorem B2327975 : Blo 1551473 2327975 := bstep (se 1 (by rfl) ⟨1745981, by rfl⟩ : syracuseStep 2327975 = 3491963) B3491963
theorem B46007783 : Blo 1551473 46007783 := bstep (se 1 (by rfl) ⟨34505837, by rfl⟩ : syracuseStep 46007783 = 69011675) B69011675
theorem B7456303 : Blo 1551473 7456303 := bstep (se 1 (by rfl) ⟨5592227, by rfl⟩ : syracuseStep 7456303 = 11184455) B11184455
theorem B7456475 : Blo 1551473 7456475 := bstep (se 1 (by rfl) ⟨5592356, by rfl⟩ : syracuseStep 7456475 = 11184713) B11184713
theorem B2328443 : Blo 1551473 2328443 := bstep (se 1 (by rfl) ⟨1746332, by rfl⟩ : syracuseStep 2328443 = 3492665) B3492665
theorem B18876347 : Blo 1551473 18876347 := bstep (se 1 (by rfl) ⟨14157260, by rfl⟩ : syracuseStep 18876347 = 28314521) B28314521
theorem B31074515 : Blo 1551473 31074515 := bstep (se 1 (by rfl) ⟨23305886, by rfl⟩ : syracuseStep 31074515 = 46611773) B46611773
theorem B14928097 : Blo 1551473 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B2328935 : Blo 1551473 2328935 := bstep (se 1 (by rfl) ⟨1746701, by rfl⟩ : syracuseStep 2328935 = 3493403) B3493403
theorem B16796099 : Blo 1551473 16796099 := bstep (se 1 (by rfl) ⟨12597074, by rfl⟩ : syracuseStep 16796099 = 25194149) B25194149
theorem B1747615 : Blo 1551473 1747615 := bstep (se 1 (by rfl) ⟨1310711, by rfl⟩ : syracuseStep 1747615 = 2621423) B2621423
theorem B6720347 : Blo 1551473 6720347 := bstep (se 1 (by rfl) ⟨5040260, by rfl⟩ : syracuseStep 6720347 = 10080521) B10080521
theorem B2485351 : Blo 1551473 2485351 := bstep (se 1 (by rfl) ⟨1864013, by rfl⟩ : syracuseStep 2485351 = 3728027) B3728027
theorem B3493025 : Blo 1551473 3493025 := bstep (se 2 (by rfl) ⟨1309884, by rfl⟩ : syracuseStep 3493025 = 2619769) B2619769
theorem B5238377 : Blo 1551473 5238377 := bstep (se 2 (by rfl) ⟨1964391, by rfl⟩ : syracuseStep 5238377 = 3928783) B3928783
theorem B29085497 : Blo 1551473 29085497 := bstep (se 2 (by rfl) ⟨10907061, by rfl⟩ : syracuseStep 29085497 = 21814123) B21814123
theorem B17682623 : Blo 1551473 17682623 := bstep (se 1 (by rfl) ⟨13261967, by rfl⟩ : syracuseStep 17682623 = 26523935) B26523935
theorem B7860563 : Blo 1551473 7860563 := bstep (se 1 (by rfl) ⟨5895422, by rfl⟩ : syracuseStep 7860563 = 11790845) B11790845
theorem B1552799 : Blo 1551473 1552799 := bstep (se 1 (by rfl) ⟨1164599, by rfl⟩ : syracuseStep 1552799 = 2329199) B2329199
theorem B6632063 : Blo 1551473 6632063 := bstep (se 1 (by rfl) ⟨4974047, by rfl⟩ : syracuseStep 6632063 = 9948095) B9948095
theorem B2691895 : Blo 1551473 2691895 := bstep (se 1 (by rfl) ⟨2018921, by rfl⟩ : syracuseStep 2691895 = 4037843) B4037843
theorem B31880105 : Blo 1551473 31880105 := bstep (se 2 (by rfl) ⟨11955039, by rfl⟩ : syracuseStep 31880105 = 23910079) B23910079
theorem B1553407 : Blo 1551473 1553407 := bstep (se 1 (by rfl) ⟨1165055, by rfl⟩ : syracuseStep 1553407 = 2330111) B2330111
theorem B5239997 : Blo 1551473 5239997 := bstep (se 3 (by rfl) ⟨982499, by rfl⟩ : syracuseStep 5239997 = 1964999) B1964999
theorem B4420975 : Blo 1551473 4420975 := bstep (se 1 (by rfl) ⟨3315731, by rfl⟩ : syracuseStep 4420975 = 6631463) B6631463
theorem B5593151 : Blo 1551473 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B16791947 : Blo 1551473 16791947 := bstep (se 1 (by rfl) ⟨12593960, by rfl⟩ : syracuseStep 16791947 = 25187921) B25187921
theorem B11950739 : Blo 1551473 11950739 := bstep (se 1 (by rfl) ⟨8963054, by rfl⟩ : syracuseStep 11950739 = 17926109) B17926109
theorem B19135655 : Blo 1551473 19135655 := bstep (se 1 (by rfl) ⟨14351741, by rfl⟩ : syracuseStep 19135655 = 28703483) B28703483
theorem B77610757 : Blo 1551473 77610757 := bstep (se 4 (by rfl) ⟨7276008, by rfl⟩ : syracuseStep 77610757 = 14552017) B14552017
theorem B11788415 : Blo 1551473 11788415 := bstep (se 1 (by rfl) ⟨8841311, by rfl⟩ : syracuseStep 11788415 = 17682623) B17682623
theorem B12583127 : Blo 1551473 12583127 := bstep (se 1 (by rfl) ⟨9437345, by rfl⟩ : syracuseStep 12583127 = 18874691) B18874691
theorem B30671855 : Blo 1551473 30671855 := bstep (se 1 (by rfl) ⟨23003891, by rfl⟩ : syracuseStep 30671855 = 46007783) B46007783
theorem B3589193 : Blo 1551473 3589193 := bstep (se 2 (by rfl) ⟨1345947, by rfl⟩ : syracuseStep 3589193 = 2691895) B2691895
theorem B12584231 : Blo 1551473 12584231 := bstep (se 1 (by rfl) ⟨9438173, by rfl⟩ : syracuseStep 12584231 = 18876347) B18876347
theorem B3728767 : Blo 1551473 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B2328683 : Blo 1551473 2328683 := bstep (se 1 (by rfl) ⟨1746512, by rfl⟩ : syracuseStep 2328683 = 3493025) B3493025
theorem B12757103 : Blo 1551473 12757103 := bstep (se 1 (by rfl) ⟨9567827, by rfl⟩ : syracuseStep 12757103 = 19135655) B19135655
theorem B3492251 : Blo 1551473 3492251 := bstep (se 1 (by rfl) ⟨2619188, by rfl⟩ : syracuseStep 3492251 = 5238377) B5238377
theorem B21253403 : Blo 1551473 21253403 := bstep (se 1 (by rfl) ⟨15940052, by rfl⟩ : syracuseStep 21253403 = 31880105) B31880105
theorem B3493331 : Blo 1551473 3493331 := bstep (se 1 (by rfl) ⟨2619998, by rfl⟩ : syracuseStep 3493331 = 5239997) B5239997
theorem B1551871 : Blo 1551473 1551871 := bstep (se 1 (by rfl) ⟨1163903, by rfl⟩ : syracuseStep 1551871 = 2327807) B2327807
theorem B2330153 : Blo 1551473 2330153 := bstep (se 2 (by rfl) ⟨873807, by rfl⟩ : syracuseStep 2330153 = 1747615) B1747615
theorem B12594737 : Blo 1551473 12594737 := bstep (se 2 (by rfl) ⟨4723026, by rfl⟩ : syracuseStep 12594737 = 9446053) B9446053
theorem B1551983 : Blo 1551473 1551983 := bstep (se 1 (by rfl) ⟨1163987, by rfl⟩ : syracuseStep 1551983 = 2327975) B2327975
theorem B1552295 : Blo 1551473 1552295 := bstep (se 1 (by rfl) ⟨1164221, by rfl⟩ : syracuseStep 1552295 = 2328443) B2328443
theorem B3313801 : Blo 1551473 3313801 := bstep (se 2 (by rfl) ⟨1242675, by rfl⟩ : syracuseStep 3313801 = 2485351) B2485351
theorem B1552623 : Blo 1551473 1552623 := bstep (se 1 (by rfl) ⟨1164467, by rfl⟩ : syracuseStep 1552623 = 2328935) B2328935
theorem B11194631 : Blo 1551473 11194631 := bstep (se 1 (by rfl) ⟨8395973, by rfl⟩ : syracuseStep 11194631 = 16791947) B16791947
theorem B7967159 : Blo 1551473 7967159 := bstep (se 1 (by rfl) ⟨5975369, by rfl⟩ : syracuseStep 7967159 = 11950739) B11950739
theorem B5894633 : Blo 1551473 5894633 := bstep (se 2 (by rfl) ⟨2210487, by rfl⟩ : syracuseStep 5894633 = 4420975) B4420975
theorem B9941737 : Blo 1551473 9941737 := bstep (se 2 (by rfl) ⟨3728151, by rfl⟩ : syracuseStep 9941737 = 7456303) B7456303
theorem B5240375 : Blo 1551473 5240375 := bstep (se 1 (by rfl) ⟨3930281, by rfl⟩ : syracuseStep 5240375 = 7860563) B7860563
theorem B19904129 : Blo 1551473 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B4421375 : Blo 1551473 4421375 := bstep (se 1 (by rfl) ⟨3316031, by rfl⟩ : syracuseStep 4421375 = 6632063) B6632063
theorem B4970983 : Blo 1551473 4970983 := bstep (se 1 (by rfl) ⟨3728237, by rfl⟩ : syracuseStep 4970983 = 7456475) B7456475
theorem B20716343 : Blo 1551473 20716343 := bstep (se 1 (by rfl) ⟨15537257, by rfl⟩ : syracuseStep 20716343 = 31074515) B31074515
theorem B11197399 : Blo 1551473 11197399 := bstep (se 1 (by rfl) ⟨8398049, by rfl⟩ : syracuseStep 11197399 = 16796099) B16796099
theorem B4480231 : Blo 1551473 4480231 := bstep (se 1 (by rfl) ⟨3360173, by rfl⟩ : syracuseStep 4480231 = 6720347) B6720347
theorem B103481009 : Blo 1551473 103481009 := bstep (se 2 (by rfl) ⟨38805378, by rfl⟩ : syracuseStep 103481009 = 77610757) B77610757
theorem B19390331 : Blo 1551473 19390331 := bstep (se 1 (by rfl) ⟨14542748, by rfl⟩ : syracuseStep 19390331 = 29085497) B29085497
theorem B7463087 : Blo 1551473 7463087 := bstep (se 1 (by rfl) ⟨5597315, by rfl⟩ : syracuseStep 7463087 = 11194631) B11194631
theorem B33555005 : Blo 1551473 33555005 := bstep (se 3 (by rfl) ⟨6291563, by rfl⟩ : syracuseStep 33555005 = 12583127) B12583127
theorem B6627977 : Blo 1551473 6627977 := bstep (se 2 (by rfl) ⟨2485491, by rfl⟩ : syracuseStep 6627977 = 4970983) B4970983
theorem B20447903 : Blo 1551473 20447903 := bstep (se 1 (by rfl) ⟨15335927, by rfl⟩ : syracuseStep 20447903 = 30671855) B30671855
theorem B8389487 : Blo 1551473 8389487 := bstep (se 1 (by rfl) ⟨6292115, by rfl⟩ : syracuseStep 8389487 = 12584231) B12584231
theorem B13255649 : Blo 1551473 13255649 := bstep (se 2 (by rfl) ⟨4970868, by rfl⟩ : syracuseStep 13255649 = 9941737) B9941737
theorem B8504735 : Blo 1551473 8504735 := bstep (se 1 (by rfl) ⟨6378551, by rfl⟩ : syracuseStep 8504735 = 12757103) B12757103
theorem B2328167 : Blo 1551473 2328167 := bstep (se 1 (by rfl) ⟨1746125, by rfl⟩ : syracuseStep 2328167 = 3492251) B3492251
theorem B5973641 : Blo 1551473 5973641 := bstep (se 2 (by rfl) ⟨2240115, by rfl⟩ : syracuseStep 5973641 = 4480231) B4480231
theorem B2328887 : Blo 1551473 2328887 := bstep (se 1 (by rfl) ⟨1746665, by rfl⟩ : syracuseStep 2328887 = 3493331) B3493331
theorem B68987339 : Blo 1551473 68987339 := bstep (se 1 (by rfl) ⟨51740504, by rfl⟩ : syracuseStep 68987339 = 103481009) B103481009
theorem B7858943 : Blo 1551473 7858943 := bstep (se 1 (by rfl) ⟨5894207, by rfl⟩ : syracuseStep 7858943 = 11788415) B11788415
theorem B4418401 : Blo 1551473 4418401 := bstep (se 2 (by rfl) ⟨1656900, by rfl⟩ : syracuseStep 4418401 = 3313801) B3313801
theorem B9571181 : Blo 1551473 9571181 := bstep (se 3 (by rfl) ⟨1794596, by rfl⟩ : syracuseStep 9571181 = 3589193) B3589193
theorem B5311439 : Blo 1551473 5311439 := bstep (se 1 (by rfl) ⟨3983579, by rfl⟩ : syracuseStep 5311439 = 7967159) B7967159
theorem B3493583 : Blo 1551473 3493583 := bstep (se 1 (by rfl) ⟨2620187, by rfl⟩ : syracuseStep 3493583 = 5240375) B5240375
theorem B14929865 : Blo 1551473 14929865 := bstep (se 2 (by rfl) ⟨5598699, by rfl⟩ : syracuseStep 14929865 = 11197399) B11197399
theorem B1552455 : Blo 1551473 1552455 := bstep (se 1 (by rfl) ⟨1164341, by rfl⟩ : syracuseStep 1552455 = 2328683) B2328683
theorem B14168935 : Blo 1551473 14168935 := bstep (se 1 (by rfl) ⟨10626701, by rfl⟩ : syracuseStep 14168935 = 21253403) B21253403
theorem B1553435 : Blo 1551473 1553435 := bstep (se 1 (by rfl) ⟨1165076, by rfl⟩ : syracuseStep 1553435 = 2330153) B2330153
theorem B3929755 : Blo 1551473 3929755 := bstep (se 1 (by rfl) ⟨2947316, by rfl⟩ : syracuseStep 3929755 = 5894633) B5894633
theorem B13269419 : Blo 1551473 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B2947583 : Blo 1551473 2947583 := bstep (se 1 (by rfl) ⟨2210687, by rfl⟩ : syracuseStep 2947583 = 4421375) B4421375
theorem B33585965 : Blo 1551473 33585965 := bstep (se 3 (by rfl) ⟨6297368, by rfl⟩ : syracuseStep 33585965 = 12594737) B12594737
theorem B4971689 : Blo 1551473 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B13810895 : Blo 1551473 13810895 := bstep (se 1 (by rfl) ⟨10358171, by rfl⟩ : syracuseStep 13810895 = 20716343) B20716343
theorem B51707549 : Blo 1551473 51707549 := bstep (se 3 (by rfl) ⟨9695165, by rfl⟩ : syracuseStep 51707549 = 19390331) B19390331
theorem B13631935 : Blo 1551473 13631935 := bstep (se 1 (by rfl) ⟨10223951, by rfl⟩ : syracuseStep 13631935 = 20447903) B20447903
theorem B3982427 : Blo 1551473 3982427 := bstep (se 1 (by rfl) ⟨2986820, by rfl⟩ : syracuseStep 3982427 = 5973641) B5973641
theorem B5891201 : Blo 1551473 5891201 := bstep (se 2 (by rfl) ⟨2209200, by rfl⟩ : syracuseStep 5891201 = 4418401) B4418401
theorem B45991559 : Blo 1551473 45991559 := bstep (se 1 (by rfl) ⟨34493669, by rfl⟩ : syracuseStep 45991559 = 68987339) B68987339
theorem B22390643 : Blo 1551473 22390643 := bstep (se 1 (by rfl) ⟨16792982, by rfl⟩ : syracuseStep 22390643 = 33585965) B33585965
theorem B3540959 : Blo 1551473 3540959 := bstep (se 1 (by rfl) ⟨2655719, by rfl⟩ : syracuseStep 3540959 = 5311439) B5311439
theorem B2329055 : Blo 1551473 2329055 := bstep (se 1 (by rfl) ⟨1746791, by rfl⟩ : syracuseStep 2329055 = 3493583) B3493583
theorem B4975391 : Blo 1551473 4975391 := bstep (se 1 (by rfl) ⟨3731543, by rfl⟩ : syracuseStep 4975391 = 7463087) B7463087
theorem B4418651 : Blo 1551473 4418651 := bstep (se 1 (by rfl) ⟨3313988, by rfl⟩ : syracuseStep 4418651 = 6627977) B6627977
theorem B1552111 : Blo 1551473 1552111 := bstep (se 1 (by rfl) ⟨1164083, by rfl⟩ : syracuseStep 1552111 = 2328167) B2328167
theorem B22679293 : Blo 1551473 22679293 := bstep (se 3 (by rfl) ⟨4252367, by rfl⟩ : syracuseStep 22679293 = 8504735) B8504735
theorem B1552591 : Blo 1551473 1552591 := bstep (se 1 (by rfl) ⟨1164443, by rfl⟩ : syracuseStep 1552591 = 2328887) B2328887
theorem B5239295 : Blo 1551473 5239295 := bstep (se 1 (by rfl) ⟨3929471, by rfl⟩ : syracuseStep 5239295 = 7858943) B7858943
theorem B75567653 : Blo 1551473 75567653 := bstep (se 4 (by rfl) ⟨7084467, by rfl⟩ : syracuseStep 75567653 = 14168935) B14168935
theorem B3314459 : Blo 1551473 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B5239673 : Blo 1551473 5239673 := bstep (se 2 (by rfl) ⟨1964877, by rfl⟩ : syracuseStep 5239673 = 3929755) B3929755
theorem B25523149 : Blo 1551473 25523149 := bstep (se 3 (by rfl) ⟨4785590, by rfl⟩ : syracuseStep 25523149 = 9571181) B9571181
theorem B22370003 : Blo 1551473 22370003 := bstep (se 1 (by rfl) ⟨16777502, by rfl⟩ : syracuseStep 22370003 = 33555005) B33555005
theorem B5592991 : Blo 1551473 5592991 := bstep (se 1 (by rfl) ⟨4194743, by rfl⟩ : syracuseStep 5592991 = 8389487) B8389487
theorem B8837099 : Blo 1551473 8837099 := bstep (se 1 (by rfl) ⟨6627824, by rfl⟩ : syracuseStep 8837099 = 13255649) B13255649
theorem B8846279 : Blo 1551473 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B1965055 : Blo 1551473 1965055 := bstep (se 1 (by rfl) ⟨1473791, by rfl⟩ : syracuseStep 1965055 = 2947583) B2947583
theorem B9207263 : Blo 1551473 9207263 := bstep (se 1 (by rfl) ⟨6905447, by rfl⟩ : syracuseStep 9207263 = 13810895) B13810895
theorem B34471699 : Blo 1551473 34471699 := bstep (se 1 (by rfl) ⟨25853774, by rfl⟩ : syracuseStep 34471699 = 51707549) B51707549
theorem B9953243 : Blo 1551473 9953243 := bstep (se 1 (by rfl) ⟨7464932, by rfl⟩ : syracuseStep 9953243 = 14929865) B14929865
theorem B2654951 : Blo 1551473 2654951 := bstep (se 1 (by rfl) ⟨1991213, by rfl⟩ : syracuseStep 2654951 = 3982427) B3982427
theorem B14927095 : Blo 1551473 14927095 := bstep (se 1 (by rfl) ⟨11195321, by rfl⟩ : syracuseStep 14927095 = 22390643) B22390643
theorem B34030865 : Blo 1551473 34030865 := bstep (se 2 (by rfl) ⟨12761574, by rfl⟩ : syracuseStep 34030865 = 25523149) B25523149
theorem B2360639 : Blo 1551473 2360639 := bstep (se 1 (by rfl) ⟨1770479, by rfl⟩ : syracuseStep 2360639 = 3540959) B3540959
theorem B5891399 : Blo 1551473 5891399 := bstep (se 1 (by rfl) ⟨4418549, by rfl⟩ : syracuseStep 5891399 = 8837099) B8837099
theorem B6138175 : Blo 1551473 6138175 := bstep (se 1 (by rfl) ⟨4603631, by rfl⟩ : syracuseStep 6138175 = 9207263) B9207263
theorem B30239057 : Blo 1551473 30239057 := bstep (se 2 (by rfl) ⟨11339646, by rfl⟩ : syracuseStep 30239057 = 22679293) B22679293
theorem B7457321 : Blo 1551473 7457321 := bstep (se 2 (by rfl) ⟨2796495, by rfl⟩ : syracuseStep 7457321 = 5592991) B5592991
theorem B11783069 : Blo 1551473 11783069 := bstep (se 3 (by rfl) ⟨2209325, by rfl⟩ : syracuseStep 11783069 = 4418651) B4418651
theorem B3492863 : Blo 1551473 3492863 := bstep (se 1 (by rfl) ⟨2619647, by rfl⟩ : syracuseStep 3492863 = 5239295) B5239295
theorem B3493115 : Blo 1551473 3493115 := bstep (se 1 (by rfl) ⟨2619836, by rfl⟩ : syracuseStep 3493115 = 5239673) B5239673
theorem B3927467 : Blo 1551473 3927467 := bstep (se 1 (by rfl) ⟨2945600, by rfl⟩ : syracuseStep 3927467 = 5891201) B5891201
theorem B14913335 : Blo 1551473 14913335 := bstep (se 1 (by rfl) ⟨11185001, by rfl⟩ : syracuseStep 14913335 = 22370003) B22370003
theorem B183849061 : Blo 1551473 183849061 := bstep (se 4 (by rfl) ⟨17235849, by rfl⟩ : syracuseStep 183849061 = 34471699) B34471699
theorem B1552703 : Blo 1551473 1552703 := bstep (se 1 (by rfl) ⟨1164527, by rfl⟩ : syracuseStep 1552703 = 2329055) B2329055
theorem B13267709 : Blo 1551473 13267709 := bstep (se 3 (by rfl) ⟨2487695, by rfl⟩ : syracuseStep 13267709 = 4975391) B4975391
theorem B50378435 : Blo 1551473 50378435 := bstep (se 1 (by rfl) ⟨37783826, by rfl⟩ : syracuseStep 50378435 = 75567653) B75567653
theorem B18175913 : Blo 1551473 18175913 := bstep (se 2 (by rfl) ⟨6815967, by rfl⟩ : syracuseStep 18175913 = 13631935) B13631935
theorem B30661039 : Blo 1551473 30661039 := bstep (se 1 (by rfl) ⟨22995779, by rfl⟩ : syracuseStep 30661039 = 45991559) B45991559
theorem B2620073 : Blo 1551473 2620073 := bstep (se 2 (by rfl) ⟨982527, by rfl⟩ : syracuseStep 2620073 = 1965055) B1965055
theorem B5897519 : Blo 1551473 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B8838557 : Blo 1551473 8838557 := bstep (se 3 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 8838557 = 3314459) B3314459
theorem B6635495 : Blo 1551473 6635495 := bstep (se 1 (by rfl) ⟨4976621, by rfl⟩ : syracuseStep 6635495 = 9953243) B9953243
theorem B8184233 : Blo 1551473 8184233 := bstep (se 2 (by rfl) ⟨3069087, by rfl⟩ : syracuseStep 8184233 = 6138175) B6138175
theorem B1573759 : Blo 1551473 1573759 := bstep (se 1 (by rfl) ⟨1180319, by rfl⟩ : syracuseStep 1573759 = 2360639) B2360639
theorem B12117275 : Blo 1551473 12117275 := bstep (se 1 (by rfl) ⟨9087956, by rfl⟩ : syracuseStep 12117275 = 18175913) B18175913
theorem B1746715 : Blo 1551473 1746715 := bstep (se 1 (by rfl) ⟨1310036, by rfl⟩ : syracuseStep 1746715 = 2620073) B2620073
theorem B7079869 : Blo 1551473 7079869 := bstep (se 3 (by rfl) ⟨1327475, by rfl⟩ : syracuseStep 7079869 = 2654951) B2654951
theorem B2328575 : Blo 1551473 2328575 := bstep (se 1 (by rfl) ⟨1746431, by rfl⟩ : syracuseStep 2328575 = 3492863) B3492863
theorem B2328743 : Blo 1551473 2328743 := bstep (se 1 (by rfl) ⟨1746557, by rfl⟩ : syracuseStep 2328743 = 3493115) B3493115
theorem B5892371 : Blo 1551473 5892371 := bstep (se 1 (by rfl) ⟨4419278, by rfl⟩ : syracuseStep 5892371 = 8838557) B8838557
theorem B245132081 : Blo 1551473 245132081 := bstep (se 2 (by rfl) ⟨91924530, by rfl⟩ : syracuseStep 245132081 = 183849061) B183849061
theorem B40881385 : Blo 1551473 40881385 := bstep (se 2 (by rfl) ⟨15330519, by rfl⟩ : syracuseStep 40881385 = 30661039) B30661039
theorem B3927599 : Blo 1551473 3927599 := bstep (se 1 (by rfl) ⟨2945699, by rfl⟩ : syracuseStep 3927599 = 5891399) B5891399
theorem B19902793 : Blo 1551473 19902793 := bstep (se 2 (by rfl) ⟨7463547, by rfl⟩ : syracuseStep 19902793 = 14927095) B14927095
theorem B2618311 : Blo 1551473 2618311 := bstep (se 1 (by rfl) ⟨1963733, by rfl⟩ : syracuseStep 2618311 = 3927467) B3927467
theorem B9942223 : Blo 1551473 9942223 := bstep (se 1 (by rfl) ⟨7456667, by rfl⟩ : syracuseStep 9942223 = 14913335) B14913335
theorem B8845139 : Blo 1551473 8845139 := bstep (se 1 (by rfl) ⟨6633854, by rfl⟩ : syracuseStep 8845139 = 13267709) B13267709
theorem B90748973 : Blo 1551473 90748973 := bstep (se 3 (by rfl) ⟨17015432, by rfl⟩ : syracuseStep 90748973 = 34030865) B34030865
theorem B33585623 : Blo 1551473 33585623 := bstep (se 1 (by rfl) ⟨25189217, by rfl⟩ : syracuseStep 33585623 = 50378435) B50378435
theorem B20159371 : Blo 1551473 20159371 := bstep (se 1 (by rfl) ⟨15119528, by rfl⟩ : syracuseStep 20159371 = 30239057) B30239057
theorem B4971547 : Blo 1551473 4971547 := bstep (se 1 (by rfl) ⟨3728660, by rfl⟩ : syracuseStep 4971547 = 7457321) B7457321
theorem B7855379 : Blo 1551473 7855379 := bstep (se 1 (by rfl) ⟨5891534, by rfl⟩ : syracuseStep 7855379 = 11783069) B11783069
theorem B3931679 : Blo 1551473 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B4423663 : Blo 1551473 4423663 := bstep (se 1 (by rfl) ⟨3317747, by rfl⟩ : syracuseStep 4423663 = 6635495) B6635495
theorem B5456155 : Blo 1551473 5456155 := bstep (se 1 (by rfl) ⟨4092116, by rfl⟩ : syracuseStep 5456155 = 8184233) B8184233
theorem B8078183 : Blo 1551473 8078183 := bstep (se 1 (by rfl) ⟨6058637, by rfl⟩ : syracuseStep 8078183 = 12117275) B12117275
theorem B26879161 : Blo 1551473 26879161 := bstep (se 2 (by rfl) ⟨10079685, by rfl⟩ : syracuseStep 26879161 = 20159371) B20159371
theorem B3491081 : Blo 1551473 3491081 := bstep (se 2 (by rfl) ⟨1309155, by rfl⟩ : syracuseStep 3491081 = 2618311) B2618311
theorem B60499315 : Blo 1551473 60499315 := bstep (se 1 (by rfl) ⟨45374486, by rfl⟩ : syracuseStep 60499315 = 90748973) B90748973
theorem B6628729 : Blo 1551473 6628729 := bstep (se 2 (by rfl) ⟨2485773, by rfl⟩ : syracuseStep 6628729 = 4971547) B4971547
theorem B13256297 : Blo 1551473 13256297 := bstep (se 2 (by rfl) ⟨4971111, by rfl⟩ : syracuseStep 13256297 = 9942223) B9942223
theorem B22390415 : Blo 1551473 22390415 := bstep (se 1 (by rfl) ⟨16792811, by rfl⟩ : syracuseStep 22390415 = 33585623) B33585623
theorem B5236919 : Blo 1551473 5236919 := bstep (se 1 (by rfl) ⟨3927689, by rfl⟩ : syracuseStep 5236919 = 7855379) B7855379
theorem B2328953 : Blo 1551473 2328953 := bstep (se 2 (by rfl) ⟨873357, by rfl⟩ : syracuseStep 2328953 = 1746715) B1746715
theorem B9439825 : Blo 1551473 9439825 := bstep (se 2 (by rfl) ⟨3539934, by rfl⟩ : syracuseStep 9439825 = 7079869) B7079869
theorem B26537057 : Blo 1551473 26537057 := bstep (se 2 (by rfl) ⟨9951396, by rfl⟩ : syracuseStep 26537057 = 19902793) B19902793
theorem B1552383 : Blo 1551473 1552383 := bstep (se 1 (by rfl) ⟨1164287, by rfl⟩ : syracuseStep 1552383 = 2328575) B2328575
theorem B1552495 : Blo 1551473 1552495 := bstep (se 1 (by rfl) ⟨1164371, by rfl⟩ : syracuseStep 1552495 = 2328743) B2328743
theorem B3928247 : Blo 1551473 3928247 := bstep (se 1 (by rfl) ⟨2946185, by rfl⟩ : syracuseStep 3928247 = 5892371) B5892371
theorem B8393381 : Blo 1551473 8393381 := bstep (se 4 (by rfl) ⟨786879, by rfl⟩ : syracuseStep 8393381 = 1573759) B1573759
theorem B2618399 : Blo 1551473 2618399 := bstep (se 1 (by rfl) ⟨1963799, by rfl⟩ : syracuseStep 2618399 = 3927599) B3927599
theorem B5896759 : Blo 1551473 5896759 := bstep (se 1 (by rfl) ⟨4422569, by rfl⟩ : syracuseStep 5896759 = 8845139) B8845139
theorem B54508513 : Blo 1551473 54508513 := bstep (se 2 (by rfl) ⟨20440692, by rfl⟩ : syracuseStep 54508513 = 40881385) B40881385
theorem B163421387 : Blo 1551473 163421387 := bstep (se 1 (by rfl) ⟨122566040, by rfl⟩ : syracuseStep 163421387 = 245132081) B245132081
theorem B2621119 : Blo 1551473 2621119 := bstep (se 1 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 2621119 = 3931679) B3931679
theorem B5898217 : Blo 1551473 5898217 := bstep (se 2 (by rfl) ⟨2211831, by rfl⟩ : syracuseStep 5898217 = 4423663) B4423663
theorem B7274873 : Blo 1551473 7274873 := bstep (se 2 (by rfl) ⟨2728077, by rfl⟩ : syracuseStep 7274873 = 5456155) B5456155
theorem B5595587 : Blo 1551473 5595587 := bstep (se 1 (by rfl) ⟨4196690, by rfl⟩ : syracuseStep 5595587 = 8393381) B8393381
theorem B1745599 : Blo 1551473 1745599 := bstep (se 1 (by rfl) ⟨1309199, by rfl⟩ : syracuseStep 1745599 = 2618399) B2618399
theorem B2327387 : Blo 1551473 2327387 := bstep (se 1 (by rfl) ⟨1745540, by rfl⟩ : syracuseStep 2327387 = 3491081) B3491081
theorem B14926943 : Blo 1551473 14926943 := bstep (se 1 (by rfl) ⟨11195207, by rfl⟩ : syracuseStep 14926943 = 22390415) B22390415
theorem B3491279 : Blo 1551473 3491279 := bstep (se 1 (by rfl) ⟨2618459, by rfl⟩ : syracuseStep 3491279 = 5236919) B5236919
theorem B108947591 : Blo 1551473 108947591 := bstep (se 1 (by rfl) ⟨81710693, by rfl⟩ : syracuseStep 108947591 = 163421387) B163421387
theorem B5385455 : Blo 1551473 5385455 := bstep (se 1 (by rfl) ⟨4039091, by rfl⟩ : syracuseStep 5385455 = 8078183) B8078183
theorem B12586433 : Blo 1551473 12586433 := bstep (se 2 (by rfl) ⟨4719912, by rfl⟩ : syracuseStep 12586433 = 9439825) B9439825
theorem B1552635 : Blo 1551473 1552635 := bstep (se 1 (by rfl) ⟨1164476, by rfl⟩ : syracuseStep 1552635 = 2328953) B2328953
theorem B17691371 : Blo 1551473 17691371 := bstep (se 1 (by rfl) ⟨13268528, by rfl⟩ : syracuseStep 17691371 = 26537057) B26537057
theorem B3494825 : Blo 1551473 3494825 := bstep (se 2 (by rfl) ⟨1310559, by rfl⟩ : syracuseStep 3494825 = 2621119) B2621119
theorem B2618831 : Blo 1551473 2618831 := bstep (se 1 (by rfl) ⟨1964123, by rfl⟩ : syracuseStep 2618831 = 3928247) B3928247
theorem B7862345 : Blo 1551473 7862345 := bstep (se 2 (by rfl) ⟨2948379, by rfl⟩ : syracuseStep 7862345 = 5896759) B5896759
theorem B8837531 : Blo 1551473 8837531 := bstep (se 1 (by rfl) ⟨6628148, by rfl⟩ : syracuseStep 8837531 = 13256297) B13256297
theorem B72678017 : Blo 1551473 72678017 := bstep (se 2 (by rfl) ⟨27254256, by rfl⟩ : syracuseStep 72678017 = 54508513) B54508513
theorem B35838881 : Blo 1551473 35838881 := bstep (se 2 (by rfl) ⟨13439580, by rfl⟩ : syracuseStep 35838881 = 26879161) B26879161
theorem B80665753 : Blo 1551473 80665753 := bstep (se 2 (by rfl) ⟨30249657, by rfl⟩ : syracuseStep 80665753 = 60499315) B60499315
theorem B8838305 : Blo 1551473 8838305 := bstep (se 2 (by rfl) ⟨3314364, by rfl⟩ : syracuseStep 8838305 = 6628729) B6628729
theorem B7864289 : Blo 1551473 7864289 := bstep (se 2 (by rfl) ⟨2949108, by rfl⟩ : syracuseStep 7864289 = 5898217) B5898217
theorem B2327465 : Blo 1551473 2327465 := bstep (se 2 (by rfl) ⟨872799, by rfl⟩ : syracuseStep 2327465 = 1745599) B1745599
theorem B2327519 : Blo 1551473 2327519 := bstep (se 1 (by rfl) ⟨1745639, by rfl⟩ : syracuseStep 2327519 = 3491279) B3491279
theorem B1745887 : Blo 1551473 1745887 := bstep (se 1 (by rfl) ⟨1309415, by rfl⟩ : syracuseStep 1745887 = 2618831) B2618831
theorem B19399661 : Blo 1551473 19399661 := bstep (se 3 (by rfl) ⟨3637436, by rfl⟩ : syracuseStep 19399661 = 7274873) B7274873
theorem B33563821 : Blo 1551473 33563821 := bstep (se 3 (by rfl) ⟨6293216, by rfl⟩ : syracuseStep 33563821 = 12586433) B12586433
theorem B72631727 : Blo 1551473 72631727 := bstep (se 1 (by rfl) ⟨54473795, by rfl⟩ : syracuseStep 72631727 = 108947591) B108947591
theorem B107554337 : Blo 1551473 107554337 := bstep (se 2 (by rfl) ⟨40332876, by rfl⟩ : syracuseStep 107554337 = 80665753) B80665753
theorem B5891687 : Blo 1551473 5891687 := bstep (se 1 (by rfl) ⟨4418765, by rfl⟩ : syracuseStep 5891687 = 8837531) B8837531
theorem B193808045 : Blo 1551473 193808045 := bstep (se 3 (by rfl) ⟨36339008, by rfl⟩ : syracuseStep 193808045 = 72678017) B72678017
theorem B5892203 : Blo 1551473 5892203 := bstep (se 1 (by rfl) ⟨4419152, by rfl⟩ : syracuseStep 5892203 = 8838305) B8838305
theorem B3590303 : Blo 1551473 3590303 := bstep (se 1 (by rfl) ⟨2692727, by rfl⟩ : syracuseStep 3590303 = 5385455) B5385455
theorem B3730391 : Blo 1551473 3730391 := bstep (se 1 (by rfl) ⟨2797793, by rfl⟩ : syracuseStep 3730391 = 5595587) B5595587
theorem B1551591 : Blo 1551473 1551591 := bstep (se 1 (by rfl) ⟨1163693, by rfl⟩ : syracuseStep 1551591 = 2327387) B2327387
theorem B2329883 : Blo 1551473 2329883 := bstep (se 1 (by rfl) ⟨1747412, by rfl⟩ : syracuseStep 2329883 = 3494825) B3494825
theorem B23892587 : Blo 1551473 23892587 := bstep (se 1 (by rfl) ⟨17919440, by rfl⟩ : syracuseStep 23892587 = 35838881) B35838881
theorem B11794247 : Blo 1551473 11794247 := bstep (se 1 (by rfl) ⟨8845685, by rfl⟩ : syracuseStep 11794247 = 17691371) B17691371
theorem B9951295 : Blo 1551473 9951295 := bstep (se 1 (by rfl) ⟨7463471, by rfl⟩ : syracuseStep 9951295 = 14926943) B14926943
theorem B5241563 : Blo 1551473 5241563 := bstep (se 1 (by rfl) ⟨3931172, by rfl⟩ : syracuseStep 5241563 = 7862345) B7862345
theorem B5242859 : Blo 1551473 5242859 := bstep (se 1 (by rfl) ⟨3932144, by rfl⟩ : syracuseStep 5242859 = 7864289) B7864289
theorem B129205363 : Blo 1551473 129205363 := bstep (se 1 (by rfl) ⟨96904022, by rfl⟩ : syracuseStep 129205363 = 193808045) B193808045
theorem B2327849 : Blo 1551473 2327849 := bstep (se 2 (by rfl) ⟨872943, by rfl⟩ : syracuseStep 2327849 = 1745887) B1745887
theorem B15928391 : Blo 1551473 15928391 := bstep (se 1 (by rfl) ⟨11946293, by rfl⟩ : syracuseStep 15928391 = 23892587) B23892587
theorem B1551643 : Blo 1551473 1551643 := bstep (se 1 (by rfl) ⟨1163732, by rfl⟩ : syracuseStep 1551643 = 2327465) B2327465
theorem B1551679 : Blo 1551473 1551679 := bstep (se 1 (by rfl) ⟨1163759, by rfl⟩ : syracuseStep 1551679 = 2327519) B2327519
theorem B3927791 : Blo 1551473 3927791 := bstep (se 1 (by rfl) ⟨2945843, by rfl⟩ : syracuseStep 3927791 = 5891687) B5891687
theorem B3928135 : Blo 1551473 3928135 := bstep (se 1 (by rfl) ⟨2946101, by rfl⟩ : syracuseStep 3928135 = 5892203) B5892203
theorem B3494375 : Blo 1551473 3494375 := bstep (se 1 (by rfl) ⟨2620781, by rfl⟩ : syracuseStep 3494375 = 5241563) B5241563
theorem B2486927 : Blo 1551473 2486927 := bstep (se 1 (by rfl) ⟨1865195, by rfl⟩ : syracuseStep 2486927 = 3730391) B3730391
theorem B1553255 : Blo 1551473 1553255 := bstep (se 1 (by rfl) ⟨1164941, by rfl⟩ : syracuseStep 1553255 = 2329883) B2329883
theorem B3495239 : Blo 1551473 3495239 := bstep (se 1 (by rfl) ⟨2621429, by rfl⟩ : syracuseStep 3495239 = 5242859) B5242859
theorem B13268393 : Blo 1551473 13268393 := bstep (se 2 (by rfl) ⟨4975647, by rfl⟩ : syracuseStep 13268393 = 9951295) B9951295
theorem B9574141 : Blo 1551473 9574141 := bstep (se 3 (by rfl) ⟨1795151, by rfl⟩ : syracuseStep 9574141 = 3590303) B3590303
theorem B12933107 : Blo 1551473 12933107 := bstep (se 1 (by rfl) ⟨9699830, by rfl⟩ : syracuseStep 12933107 = 19399661) B19399661
theorem B48421151 : Blo 1551473 48421151 := bstep (se 1 (by rfl) ⟨36315863, by rfl⟩ : syracuseStep 48421151 = 72631727) B72631727
theorem B71702891 : Blo 1551473 71702891 := bstep (se 1 (by rfl) ⟨53777168, by rfl⟩ : syracuseStep 71702891 = 107554337) B107554337
theorem B7862831 : Blo 1551473 7862831 := bstep (se 1 (by rfl) ⟨5897123, by rfl⟩ : syracuseStep 7862831 = 11794247) B11794247
theorem B44751761 : Blo 1551473 44751761 := bstep (se 2 (by rfl) ⟨16781910, by rfl⟩ : syracuseStep 44751761 = 33563821) B33563821
theorem B42475709 : Blo 1551473 42475709 := bstep (se 3 (by rfl) ⟨7964195, by rfl⟩ : syracuseStep 42475709 = 15928391) B15928391
theorem B47801927 : Blo 1551473 47801927 := bstep (se 1 (by rfl) ⟨35851445, by rfl⟩ : syracuseStep 47801927 = 71702891) B71702891
theorem B12765521 : Blo 1551473 12765521 := bstep (se 2 (by rfl) ⟨4787070, by rfl⟩ : syracuseStep 12765521 = 9574141) B9574141
theorem B5237513 : Blo 1551473 5237513 := bstep (se 2 (by rfl) ⟨1964067, by rfl⟩ : syracuseStep 5237513 = 3928135) B3928135
theorem B2329583 : Blo 1551473 2329583 := bstep (se 1 (by rfl) ⟨1747187, by rfl⟩ : syracuseStep 2329583 = 3494375) B3494375
theorem B1657951 : Blo 1551473 1657951 := bstep (se 1 (by rfl) ⟨1243463, by rfl⟩ : syracuseStep 1657951 = 2486927) B2486927
theorem B1551899 : Blo 1551473 1551899 := bstep (se 1 (by rfl) ⟨1163924, by rfl⟩ : syracuseStep 1551899 = 2327849) B2327849
theorem B2330159 : Blo 1551473 2330159 := bstep (se 1 (by rfl) ⟨1747619, by rfl⟩ : syracuseStep 2330159 = 3495239) B3495239
theorem B8622071 : Blo 1551473 8622071 := bstep (se 1 (by rfl) ⟨6466553, by rfl⟩ : syracuseStep 8622071 = 12933107) B12933107
theorem B172273817 : Blo 1551473 172273817 := bstep (se 2 (by rfl) ⟨64602681, by rfl⟩ : syracuseStep 172273817 = 129205363) B129205363
theorem B32280767 : Blo 1551473 32280767 := bstep (se 1 (by rfl) ⟨24210575, by rfl⟩ : syracuseStep 32280767 = 48421151) B48421151
theorem B2618527 : Blo 1551473 2618527 := bstep (se 1 (by rfl) ⟨1963895, by rfl⟩ : syracuseStep 2618527 = 3927791) B3927791
theorem B8845595 : Blo 1551473 8845595 := bstep (se 1 (by rfl) ⟨6634196, by rfl⟩ : syracuseStep 8845595 = 13268393) B13268393
theorem B5241887 : Blo 1551473 5241887 := bstep (se 1 (by rfl) ⟨3931415, by rfl⟩ : syracuseStep 5241887 = 7862831) B7862831
theorem B29834507 : Blo 1551473 29834507 := bstep (se 1 (by rfl) ⟨22375880, by rfl⟩ : syracuseStep 29834507 = 44751761) B44751761
theorem B21520511 : Blo 1551473 21520511 := bstep (se 1 (by rfl) ⟨16140383, by rfl⟩ : syracuseStep 21520511 = 32280767) B32280767
theorem B31867951 : Blo 1551473 31867951 := bstep (se 1 (by rfl) ⟨23900963, by rfl⟩ : syracuseStep 31867951 = 47801927) B47801927
theorem B3491369 : Blo 1551473 3491369 := bstep (se 2 (by rfl) ⟨1309263, by rfl⟩ : syracuseStep 3491369 = 2618527) B2618527
theorem B3491675 : Blo 1551473 3491675 := bstep (se 1 (by rfl) ⟨2618756, by rfl⟩ : syracuseStep 3491675 = 5237513) B5237513
theorem B8842405 : Blo 1551473 8842405 := bstep (se 4 (by rfl) ⟨828975, by rfl⟩ : syracuseStep 8842405 = 1657951) B1657951
theorem B1553055 : Blo 1551473 1553055 := bstep (se 1 (by rfl) ⟨1164791, by rfl⟩ : syracuseStep 1553055 = 2329583) B2329583
theorem B3494591 : Blo 1551473 3494591 := bstep (se 1 (by rfl) ⟨2620943, by rfl⟩ : syracuseStep 3494591 = 5241887) B5241887
theorem B1553439 : Blo 1551473 1553439 := bstep (se 1 (by rfl) ⟨1165079, by rfl⟩ : syracuseStep 1553439 = 2330159) B2330159
theorem B5748047 : Blo 1551473 5748047 := bstep (se 1 (by rfl) ⟨4311035, by rfl⟩ : syracuseStep 5748047 = 8622071) B8622071
theorem B459396845 : Blo 1551473 459396845 := bstep (se 3 (by rfl) ⟨86136908, by rfl⟩ : syracuseStep 459396845 = 172273817) B172273817
theorem B113268557 : Blo 1551473 113268557 := bstep (se 3 (by rfl) ⟨21237854, by rfl⟩ : syracuseStep 113268557 = 42475709) B42475709
theorem B5897063 : Blo 1551473 5897063 := bstep (se 1 (by rfl) ⟨4422797, by rfl⟩ : syracuseStep 5897063 = 8845595) B8845595
theorem B8510347 : Blo 1551473 8510347 := bstep (se 1 (by rfl) ⟨6382760, by rfl⟩ : syracuseStep 8510347 = 12765521) B12765521
theorem B19889671 : Blo 1551473 19889671 := bstep (se 1 (by rfl) ⟨14917253, by rfl⟩ : syracuseStep 19889671 = 29834507) B29834507
theorem B2327579 : Blo 1551473 2327579 := bstep (se 1 (by rfl) ⟨1745684, by rfl⟩ : syracuseStep 2327579 = 3491369) B3491369
theorem B11347129 : Blo 1551473 11347129 := bstep (se 2 (by rfl) ⟨4255173, by rfl⟩ : syracuseStep 11347129 = 8510347) B8510347
theorem B2327783 : Blo 1551473 2327783 := bstep (se 1 (by rfl) ⟨1745837, by rfl⟩ : syracuseStep 2327783 = 3491675) B3491675
theorem B11789873 : Blo 1551473 11789873 := bstep (se 2 (by rfl) ⟨4421202, by rfl⟩ : syracuseStep 11789873 = 8842405) B8842405
theorem B26519561 : Blo 1551473 26519561 := bstep (se 2 (by rfl) ⟨9944835, by rfl⟩ : syracuseStep 26519561 = 19889671) B19889671
theorem B14347007 : Blo 1551473 14347007 := bstep (se 1 (by rfl) ⟨10760255, by rfl⟩ : syracuseStep 14347007 = 21520511) B21520511
theorem B2329727 : Blo 1551473 2329727 := bstep (se 1 (by rfl) ⟨1747295, by rfl⟩ : syracuseStep 2329727 = 3494591) B3494591
theorem B3832031 : Blo 1551473 3832031 := bstep (se 1 (by rfl) ⟨2874023, by rfl⟩ : syracuseStep 3832031 = 5748047) B5748047
theorem B306264563 : Blo 1551473 306264563 := bstep (se 1 (by rfl) ⟨229698422, by rfl⟩ : syracuseStep 306264563 = 459396845) B459396845
theorem B75512371 : Blo 1551473 75512371 := bstep (se 1 (by rfl) ⟨56634278, by rfl⟩ : syracuseStep 75512371 = 113268557) B113268557
theorem B42490601 : Blo 1551473 42490601 := bstep (se 2 (by rfl) ⟨15933975, by rfl⟩ : syracuseStep 42490601 = 31867951) B31867951
theorem B3931375 : Blo 1551473 3931375 := bstep (se 1 (by rfl) ⟨2948531, by rfl⟩ : syracuseStep 3931375 = 5897063) B5897063
theorem B17679707 : Blo 1551473 17679707 := bstep (se 1 (by rfl) ⟨13259780, by rfl⟩ : syracuseStep 17679707 = 26519561) B26519561
theorem B1551719 : Blo 1551473 1551719 := bstep (se 1 (by rfl) ⟨1163789, by rfl⟩ : syracuseStep 1551719 = 2327579) B2327579
theorem B100683161 : Blo 1551473 100683161 := bstep (se 2 (by rfl) ⟨37756185, by rfl⟩ : syracuseStep 100683161 = 75512371) B75512371
theorem B1551855 : Blo 1551473 1551855 := bstep (se 1 (by rfl) ⟨1163891, by rfl⟩ : syracuseStep 1551855 = 2327783) B2327783
theorem B7859915 : Blo 1551473 7859915 := bstep (se 1 (by rfl) ⟨5894936, by rfl⟩ : syracuseStep 7859915 = 11789873) B11789873
theorem B9564671 : Blo 1551473 9564671 := bstep (se 1 (by rfl) ⟨7173503, by rfl⟩ : syracuseStep 9564671 = 14347007) B14347007
theorem B1553151 : Blo 1551473 1553151 := bstep (se 1 (by rfl) ⟨1164863, by rfl⟩ : syracuseStep 1553151 = 2329727) B2329727
theorem B2554687 : Blo 1551473 2554687 := bstep (se 1 (by rfl) ⟨1916015, by rfl⟩ : syracuseStep 2554687 = 3832031) B3832031
theorem B15129505 : Blo 1551473 15129505 := bstep (se 2 (by rfl) ⟨5673564, by rfl⟩ : syracuseStep 15129505 = 11347129) B11347129
theorem B5241833 : Blo 1551473 5241833 := bstep (se 2 (by rfl) ⟨1965687, by rfl⟩ : syracuseStep 5241833 = 3931375) B3931375
theorem B204176375 : Blo 1551473 204176375 := bstep (se 1 (by rfl) ⟨153132281, by rfl⟩ : syracuseStep 204176375 = 306264563) B306264563
theorem B28327067 : Blo 1551473 28327067 := bstep (se 1 (by rfl) ⟨21245300, by rfl⟩ : syracuseStep 28327067 = 42490601) B42490601
theorem B18884711 : Blo 1551473 18884711 := bstep (se 1 (by rfl) ⟨14163533, by rfl⟩ : syracuseStep 18884711 = 28327067) B28327067
theorem B6376447 : Blo 1551473 6376447 := bstep (se 1 (by rfl) ⟨4782335, by rfl⟩ : syracuseStep 6376447 = 9564671) B9564671
theorem B20172673 : Blo 1551473 20172673 := bstep (se 2 (by rfl) ⟨7564752, by rfl⟩ : syracuseStep 20172673 = 15129505) B15129505
theorem B3494555 : Blo 1551473 3494555 := bstep (se 1 (by rfl) ⟨2620916, by rfl⟩ : syracuseStep 3494555 = 5241833) B5241833
theorem B67122107 : Blo 1551473 67122107 := bstep (se 1 (by rfl) ⟨50341580, by rfl⟩ : syracuseStep 67122107 = 100683161) B100683161
theorem B5239943 : Blo 1551473 5239943 := bstep (se 1 (by rfl) ⟨3929957, by rfl⟩ : syracuseStep 5239943 = 7859915) B7859915
theorem B11786471 : Blo 1551473 11786471 := bstep (se 1 (by rfl) ⟨8839853, by rfl⟩ : syracuseStep 11786471 = 17679707) B17679707
theorem B3406249 : Blo 1551473 3406249 := bstep (se 2 (by rfl) ⟨1277343, by rfl⟩ : syracuseStep 3406249 = 2554687) B2554687
theorem B136117583 : Blo 1551473 136117583 := bstep (se 1 (by rfl) ⟨102088187, by rfl⟩ : syracuseStep 136117583 = 204176375) B204176375
theorem B7857647 : Blo 1551473 7857647 := bstep (se 1 (by rfl) ⟨5893235, by rfl⟩ : syracuseStep 7857647 = 11786471) B11786471
theorem B90745055 : Blo 1551473 90745055 := bstep (se 1 (by rfl) ⟨68058791, by rfl⟩ : syracuseStep 90745055 = 136117583) B136117583
theorem B26896897 : Blo 1551473 26896897 := bstep (se 2 (by rfl) ⟨10086336, by rfl⟩ : syracuseStep 26896897 = 20172673) B20172673
theorem B50359229 : Blo 1551473 50359229 := bstep (se 3 (by rfl) ⟨9442355, by rfl⟩ : syracuseStep 50359229 = 18884711) B18884711
theorem B2329703 : Blo 1551473 2329703 := bstep (se 1 (by rfl) ⟨1747277, by rfl⟩ : syracuseStep 2329703 = 3494555) B3494555
theorem B4541665 : Blo 1551473 4541665 := bstep (se 2 (by rfl) ⟨1703124, by rfl⟩ : syracuseStep 4541665 = 3406249) B3406249
theorem B44748071 : Blo 1551473 44748071 := bstep (se 1 (by rfl) ⟨33561053, by rfl⟩ : syracuseStep 44748071 = 67122107) B67122107
theorem B3493295 : Blo 1551473 3493295 := bstep (se 1 (by rfl) ⟨2619971, by rfl⟩ : syracuseStep 3493295 = 5239943) B5239943
theorem B8501929 : Blo 1551473 8501929 := bstep (se 2 (by rfl) ⟨3188223, by rfl⟩ : syracuseStep 8501929 = 6376447) B6376447
theorem B45343621 : Blo 1551473 45343621 := bstep (se 4 (by rfl) ⟨4250964, by rfl⟩ : syracuseStep 45343621 = 8501929) B8501929
theorem B6055553 : Blo 1551473 6055553 := bstep (se 2 (by rfl) ⟨2270832, by rfl⟩ : syracuseStep 6055553 = 4541665) B4541665
theorem B33572819 : Blo 1551473 33572819 := bstep (se 1 (by rfl) ⟨25179614, by rfl⟩ : syracuseStep 33572819 = 50359229) B50359229
theorem B2328863 : Blo 1551473 2328863 := bstep (se 1 (by rfl) ⟨1746647, by rfl⟩ : syracuseStep 2328863 = 3493295) B3493295
theorem B5238431 : Blo 1551473 5238431 := bstep (se 1 (by rfl) ⟨3928823, by rfl⟩ : syracuseStep 5238431 = 7857647) B7857647
theorem B1553135 : Blo 1551473 1553135 := bstep (se 1 (by rfl) ⟨1164851, by rfl⟩ : syracuseStep 1553135 = 2329703) B2329703
theorem B29832047 : Blo 1551473 29832047 := bstep (se 1 (by rfl) ⟨22374035, by rfl⟩ : syracuseStep 29832047 = 44748071) B44748071
theorem B35862529 : Blo 1551473 35862529 := bstep (se 2 (by rfl) ⟨13448448, by rfl⟩ : syracuseStep 35862529 = 26896897) B26896897
theorem B60496703 : Blo 1551473 60496703 := bstep (se 1 (by rfl) ⟨45372527, by rfl⟩ : syracuseStep 60496703 = 90745055) B90745055
theorem B47816705 : Blo 1551473 47816705 := bstep (se 2 (by rfl) ⟨17931264, by rfl⟩ : syracuseStep 47816705 = 35862529) B35862529
theorem B60458161 : Blo 1551473 60458161 := bstep (se 2 (by rfl) ⟨22671810, by rfl⟩ : syracuseStep 60458161 = 45343621) B45343621
theorem B22381879 : Blo 1551473 22381879 := bstep (se 1 (by rfl) ⟨16786409, by rfl⟩ : syracuseStep 22381879 = 33572819) B33572819
theorem B40331135 : Blo 1551473 40331135 := bstep (se 1 (by rfl) ⟨30248351, by rfl⟩ : syracuseStep 40331135 = 60496703) B60496703
theorem B3492287 : Blo 1551473 3492287 := bstep (se 1 (by rfl) ⟨2619215, by rfl⟩ : syracuseStep 3492287 = 5238431) B5238431
theorem B1552575 : Blo 1551473 1552575 := bstep (se 1 (by rfl) ⟨1164431, by rfl⟩ : syracuseStep 1552575 = 2328863) B2328863
theorem B19888031 : Blo 1551473 19888031 := bstep (se 1 (by rfl) ⟨14916023, by rfl⟩ : syracuseStep 19888031 = 29832047) B29832047
theorem B4037035 : Blo 1551473 4037035 := bstep (se 1 (by rfl) ⟨3027776, by rfl⟩ : syracuseStep 4037035 = 6055553) B6055553
theorem B5382713 : Blo 1551473 5382713 := bstep (se 2 (by rfl) ⟨2018517, by rfl⟩ : syracuseStep 5382713 = 4037035) B4037035
theorem B26887423 : Blo 1551473 26887423 := bstep (se 1 (by rfl) ⟨20165567, by rfl⟩ : syracuseStep 26887423 = 40331135) B40331135
theorem B80610881 : Blo 1551473 80610881 := bstep (se 2 (by rfl) ⟨30229080, by rfl⟩ : syracuseStep 80610881 = 60458161) B60458161
theorem B2328191 : Blo 1551473 2328191 := bstep (se 1 (by rfl) ⟨1746143, by rfl⟩ : syracuseStep 2328191 = 3492287) B3492287
theorem B31877803 : Blo 1551473 31877803 := bstep (se 1 (by rfl) ⟨23908352, by rfl⟩ : syracuseStep 31877803 = 47816705) B47816705
theorem B13258687 : Blo 1551473 13258687 := bstep (se 1 (by rfl) ⟨9944015, by rfl⟩ : syracuseStep 13258687 = 19888031) B19888031
theorem B29842505 : Blo 1551473 29842505 := bstep (se 2 (by rfl) ⟨11190939, by rfl⟩ : syracuseStep 29842505 = 22381879) B22381879
theorem B3588475 : Blo 1551473 3588475 := bstep (se 1 (by rfl) ⟨2691356, by rfl⟩ : syracuseStep 3588475 = 5382713) B5382713
theorem B35849897 : Blo 1551473 35849897 := bstep (se 2 (by rfl) ⟨13443711, by rfl⟩ : syracuseStep 35849897 = 26887423) B26887423
theorem B42503737 : Blo 1551473 42503737 := bstep (se 2 (by rfl) ⟨15938901, by rfl⟩ : syracuseStep 42503737 = 31877803) B31877803
theorem B1552127 : Blo 1551473 1552127 := bstep (se 1 (by rfl) ⟨1164095, by rfl⟩ : syracuseStep 1552127 = 2328191) B2328191
theorem B214962349 : Blo 1551473 214962349 := bstep (se 3 (by rfl) ⟨40305440, by rfl⟩ : syracuseStep 214962349 = 80610881) B80610881
theorem B19895003 : Blo 1551473 19895003 := bstep (se 1 (by rfl) ⟨14921252, by rfl⟩ : syracuseStep 19895003 = 29842505) B29842505
theorem B17678249 : Blo 1551473 17678249 := bstep (se 2 (by rfl) ⟨6629343, by rfl⟩ : syracuseStep 17678249 = 13258687) B13258687
theorem B13263335 : Blo 1551473 13263335 := bstep (se 1 (by rfl) ⟨9947501, by rfl⟩ : syracuseStep 13263335 = 19895003) B19895003
theorem B4784633 : Blo 1551473 4784633 := bstep (se 2 (by rfl) ⟨1794237, by rfl⟩ : syracuseStep 4784633 = 3588475) B3588475
theorem B286616465 : Blo 1551473 286616465 := bstep (se 2 (by rfl) ⟨107481174, by rfl⟩ : syracuseStep 286616465 = 214962349) B214962349
theorem B23899931 : Blo 1551473 23899931 := bstep (se 1 (by rfl) ⟨17924948, by rfl⟩ : syracuseStep 23899931 = 35849897) B35849897
theorem B11785499 : Blo 1551473 11785499 := bstep (se 1 (by rfl) ⟨8839124, by rfl⟩ : syracuseStep 11785499 = 17678249) B17678249
theorem B56671649 : Blo 1551473 56671649 := bstep (se 2 (by rfl) ⟨21251868, by rfl⟩ : syracuseStep 56671649 = 42503737) B42503737
theorem B7856999 : Blo 1551473 7856999 := bstep (se 1 (by rfl) ⟨5892749, by rfl⟩ : syracuseStep 7856999 = 11785499) B11785499
theorem B8842223 : Blo 1551473 8842223 := bstep (se 1 (by rfl) ⟨6631667, by rfl⟩ : syracuseStep 8842223 = 13263335) B13263335
theorem B3189755 : Blo 1551473 3189755 := bstep (se 1 (by rfl) ⟨2392316, by rfl⟩ : syracuseStep 3189755 = 4784633) B4784633
theorem B191077643 : Blo 1551473 191077643 := bstep (se 1 (by rfl) ⟨143308232, by rfl⟩ : syracuseStep 191077643 = 286616465) B286616465
theorem B37781099 : Blo 1551473 37781099 := bstep (se 1 (by rfl) ⟨28335824, by rfl⟩ : syracuseStep 37781099 = 56671649) B56671649
theorem B15933287 : Blo 1551473 15933287 := bstep (se 1 (by rfl) ⟨11949965, by rfl⟩ : syracuseStep 15933287 = 23899931) B23899931
theorem B5237999 : Blo 1551473 5237999 := bstep (se 1 (by rfl) ⟨3928499, by rfl⟩ : syracuseStep 5237999 = 7856999) B7856999
theorem B5894815 : Blo 1551473 5894815 := bstep (se 1 (by rfl) ⟨4421111, by rfl⟩ : syracuseStep 5894815 = 8842223) B8842223
theorem B2126503 : Blo 1551473 2126503 := bstep (se 1 (by rfl) ⟨1594877, by rfl⟩ : syracuseStep 2126503 = 3189755) B3189755
theorem B25187399 : Blo 1551473 25187399 := bstep (se 1 (by rfl) ⟨18890549, by rfl⟩ : syracuseStep 25187399 = 37781099) B37781099
theorem B10622191 : Blo 1551473 10622191 := bstep (se 1 (by rfl) ⟨7966643, by rfl⟩ : syracuseStep 10622191 = 15933287) B15933287
theorem B127385095 : Blo 1551473 127385095 := bstep (se 1 (by rfl) ⟨95538821, by rfl⟩ : syracuseStep 127385095 = 191077643) B191077643
theorem B2835337 : Blo 1551473 2835337 := bstep (se 2 (by rfl) ⟨1063251, by rfl⟩ : syracuseStep 2835337 = 2126503) B2126503
theorem B169846793 : Blo 1551473 169846793 := bstep (se 2 (by rfl) ⟨63692547, by rfl⟩ : syracuseStep 169846793 = 127385095) B127385095
theorem B3491999 : Blo 1551473 3491999 := bstep (se 1 (by rfl) ⟨2618999, by rfl⟩ : syracuseStep 3491999 = 5237999) B5237999
theorem B7859753 : Blo 1551473 7859753 := bstep (se 2 (by rfl) ⟨2947407, by rfl⟩ : syracuseStep 7859753 = 5894815) B5894815
theorem B16791599 : Blo 1551473 16791599 := bstep (se 1 (by rfl) ⟨12593699, by rfl⟩ : syracuseStep 16791599 = 25187399) B25187399
theorem B14162921 : Blo 1551473 14162921 := bstep (se 2 (by rfl) ⟨5311095, by rfl⟩ : syracuseStep 14162921 = 10622191) B10622191
theorem B113231195 : Blo 1551473 113231195 := bstep (se 1 (by rfl) ⟨84923396, by rfl⟩ : syracuseStep 113231195 = 169846793) B169846793
theorem B2327999 : Blo 1551473 2327999 := bstep (se 1 (by rfl) ⟨1745999, by rfl⟩ : syracuseStep 2327999 = 3491999) B3491999
theorem B3780449 : Blo 1551473 3780449 := bstep (se 2 (by rfl) ⟨1417668, by rfl⟩ : syracuseStep 3780449 = 2835337) B2835337
theorem B11194399 : Blo 1551473 11194399 := bstep (se 1 (by rfl) ⟨8395799, by rfl⟩ : syracuseStep 11194399 = 16791599) B16791599
theorem B9441947 : Blo 1551473 9441947 := bstep (se 1 (by rfl) ⟨7081460, by rfl⟩ : syracuseStep 9441947 = 14162921) B14162921
theorem B5239835 : Blo 1551473 5239835 := bstep (se 1 (by rfl) ⟨3929876, by rfl⟩ : syracuseStep 5239835 = 7859753) B7859753
theorem B14925865 : Blo 1551473 14925865 := bstep (se 2 (by rfl) ⟨5597199, by rfl⟩ : syracuseStep 14925865 = 11194399) B11194399
theorem B6294631 : Blo 1551473 6294631 := bstep (se 1 (by rfl) ⟨4720973, by rfl⟩ : syracuseStep 6294631 = 9441947) B9441947
theorem B3493223 : Blo 1551473 3493223 := bstep (se 1 (by rfl) ⟨2619917, by rfl⟩ : syracuseStep 3493223 = 5239835) B5239835
theorem B1551999 : Blo 1551473 1551999 := bstep (se 1 (by rfl) ⟨1163999, by rfl⟩ : syracuseStep 1551999 = 2327999) B2327999
theorem B2520299 : Blo 1551473 2520299 := bstep (se 1 (by rfl) ⟨1890224, by rfl⟩ : syracuseStep 2520299 = 3780449) B3780449
theorem B75487463 : Blo 1551473 75487463 := bstep (se 1 (by rfl) ⟨56615597, by rfl⟩ : syracuseStep 75487463 = 113231195) B113231195
theorem B1680199 : Blo 1551473 1680199 := bstep (se 1 (by rfl) ⟨1260149, by rfl⟩ : syracuseStep 1680199 = 2520299) B2520299
theorem B50324975 : Blo 1551473 50324975 := bstep (se 1 (by rfl) ⟨37743731, by rfl⟩ : syracuseStep 50324975 = 75487463) B75487463
theorem B2328815 : Blo 1551473 2328815 := bstep (se 1 (by rfl) ⟨1746611, by rfl⟩ : syracuseStep 2328815 = 3493223) B3493223
theorem B19901153 : Blo 1551473 19901153 := bstep (se 2 (by rfl) ⟨7462932, by rfl⟩ : syracuseStep 19901153 = 14925865) B14925865
theorem B8392841 : Blo 1551473 8392841 := bstep (se 2 (by rfl) ⟨3147315, by rfl⟩ : syracuseStep 8392841 = 6294631) B6294631
theorem B5595227 : Blo 1551473 5595227 := bstep (se 1 (by rfl) ⟨4196420, by rfl⟩ : syracuseStep 5595227 = 8392841) B8392841
theorem B33549983 : Blo 1551473 33549983 := bstep (se 1 (by rfl) ⟨25162487, by rfl⟩ : syracuseStep 33549983 = 50324975) B50324975
theorem B1552543 : Blo 1551473 1552543 := bstep (se 1 (by rfl) ⟨1164407, by rfl⟩ : syracuseStep 1552543 = 2328815) B2328815
theorem B13267435 : Blo 1551473 13267435 := bstep (se 1 (by rfl) ⟨9950576, by rfl⟩ : syracuseStep 13267435 = 19901153) B19901153
theorem B8961061 : Blo 1551473 8961061 := bstep (se 4 (by rfl) ⟨840099, by rfl⟩ : syracuseStep 8961061 = 1680199) B1680199
theorem B22366655 : Blo 1551473 22366655 := bstep (se 1 (by rfl) ⟨16774991, by rfl⟩ : syracuseStep 22366655 = 33549983) B33549983
theorem B3730151 : Blo 1551473 3730151 := bstep (se 1 (by rfl) ⟨2797613, by rfl⟩ : syracuseStep 3730151 = 5595227) B5595227
theorem B17689913 : Blo 1551473 17689913 := bstep (se 2 (by rfl) ⟨6633717, by rfl⟩ : syracuseStep 17689913 = 13267435) B13267435
theorem B11948081 : Blo 1551473 11948081 := bstep (se 2 (by rfl) ⟨4480530, by rfl⟩ : syracuseStep 11948081 = 8961061) B8961061
theorem B14911103 : Blo 1551473 14911103 := bstep (se 1 (by rfl) ⟨11183327, by rfl⟩ : syracuseStep 14911103 = 22366655) B22366655
theorem B9947069 : Blo 1551473 9947069 := bstep (se 3 (by rfl) ⟨1865075, by rfl⟩ : syracuseStep 9947069 = 3730151) B3730151
theorem B31861549 : Blo 1551473 31861549 := bstep (se 3 (by rfl) ⟨5974040, by rfl⟩ : syracuseStep 31861549 = 11948081) B11948081
theorem B11793275 : Blo 1551473 11793275 := bstep (se 1 (by rfl) ⟨8844956, by rfl⟩ : syracuseStep 11793275 = 17689913) B17689913
theorem B9940735 : Blo 1551473 9940735 := bstep (se 1 (by rfl) ⟨7455551, by rfl⟩ : syracuseStep 9940735 = 14911103) B14911103
theorem B6631379 : Blo 1551473 6631379 := bstep (se 1 (by rfl) ⟨4973534, by rfl⟩ : syracuseStep 6631379 = 9947069) B9947069
theorem B7862183 : Blo 1551473 7862183 := bstep (se 1 (by rfl) ⟨5896637, by rfl⟩ : syracuseStep 7862183 = 11793275) B11793275
theorem B42482065 : Blo 1551473 42482065 := bstep (se 2 (by rfl) ⟨15930774, by rfl⟩ : syracuseStep 42482065 = 31861549) B31861549
theorem B56642753 : Blo 1551473 56642753 := bstep (se 2 (by rfl) ⟨21241032, by rfl⟩ : syracuseStep 56642753 = 42482065) B42482065
theorem B4420919 : Blo 1551473 4420919 := bstep (se 1 (by rfl) ⟨3315689, by rfl⟩ : syracuseStep 4420919 = 6631379) B6631379
theorem B5241455 : Blo 1551473 5241455 := bstep (se 1 (by rfl) ⟨3931091, by rfl⟩ : syracuseStep 5241455 = 7862183) B7862183
theorem B13254313 : Blo 1551473 13254313 := bstep (se 2 (by rfl) ⟨4970367, by rfl⟩ : syracuseStep 13254313 = 9940735) B9940735
theorem B17672417 : Blo 1551473 17672417 := bstep (se 2 (by rfl) ⟨6627156, by rfl⟩ : syracuseStep 17672417 = 13254313) B13254313
theorem B151047341 : Blo 1551473 151047341 := bstep (se 3 (by rfl) ⟨28321376, by rfl⟩ : syracuseStep 151047341 = 56642753) B56642753
theorem B3494303 : Blo 1551473 3494303 := bstep (se 1 (by rfl) ⟨2620727, by rfl⟩ : syracuseStep 3494303 = 5241455) B5241455
theorem B2947279 : Blo 1551473 2947279 := bstep (se 1 (by rfl) ⟨2210459, by rfl⟩ : syracuseStep 2947279 = 4420919) B4420919
theorem B11781611 : Blo 1551473 11781611 := bstep (se 1 (by rfl) ⟨8836208, by rfl⟩ : syracuseStep 11781611 = 17672417) B17672417
theorem B100698227 : Blo 1551473 100698227 := bstep (se 1 (by rfl) ⟨75523670, by rfl⟩ : syracuseStep 100698227 = 151047341) B151047341
theorem B2329535 : Blo 1551473 2329535 := bstep (se 1 (by rfl) ⟨1747151, by rfl⟩ : syracuseStep 2329535 = 3494303) B3494303
theorem B3929705 : Blo 1551473 3929705 := bstep (se 2 (by rfl) ⟨1473639, by rfl⟩ : syracuseStep 3929705 = 2947279) B2947279
theorem B1553023 : Blo 1551473 1553023 := bstep (se 1 (by rfl) ⟨1164767, by rfl⟩ : syracuseStep 1553023 = 2329535) B2329535
theorem B7854407 : Blo 1551473 7854407 := bstep (se 1 (by rfl) ⟨5890805, by rfl⟩ : syracuseStep 7854407 = 11781611) B11781611
theorem B2619803 : Blo 1551473 2619803 := bstep (se 1 (by rfl) ⟨1964852, by rfl⟩ : syracuseStep 2619803 = 3929705) B3929705
theorem B67132151 : Blo 1551473 67132151 := bstep (se 1 (by rfl) ⟨50349113, by rfl⟩ : syracuseStep 67132151 = 100698227) B100698227
theorem B5236271 : Blo 1551473 5236271 := bstep (se 1 (by rfl) ⟨3927203, by rfl⟩ : syracuseStep 5236271 = 7854407) B7854407
theorem B1746535 : Blo 1551473 1746535 := bstep (se 1 (by rfl) ⟨1309901, by rfl⟩ : syracuseStep 1746535 = 2619803) B2619803
theorem B44754767 : Blo 1551473 44754767 := bstep (se 1 (by rfl) ⟨33566075, by rfl⟩ : syracuseStep 44754767 = 67132151) B67132151
theorem B3490847 : Blo 1551473 3490847 := bstep (se 1 (by rfl) ⟨2618135, by rfl⟩ : syracuseStep 3490847 = 5236271) B5236271
theorem B29836511 : Blo 1551473 29836511 := bstep (se 1 (by rfl) ⟨22377383, by rfl⟩ : syracuseStep 29836511 = 44754767) B44754767
theorem B2328713 : Blo 1551473 2328713 := bstep (se 2 (by rfl) ⟨873267, by rfl⟩ : syracuseStep 2328713 = 1746535) B1746535
theorem B2327231 : Blo 1551473 2327231 := bstep (se 1 (by rfl) ⟨1745423, by rfl⟩ : syracuseStep 2327231 = 3490847) B3490847
theorem B19891007 : Blo 1551473 19891007 := bstep (se 1 (by rfl) ⟨14918255, by rfl⟩ : syracuseStep 19891007 = 29836511) B29836511
theorem B1552475 : Blo 1551473 1552475 := bstep (se 1 (by rfl) ⟨1164356, by rfl⟩ : syracuseStep 1552475 = 2328713) B2328713
theorem B1551487 : Blo 1551473 1551487 := bstep (se 1 (by rfl) ⟨1163615, by rfl⟩ : syracuseStep 1551487 = 2327231) B2327231
theorem B13260671 : Blo 1551473 13260671 := bstep (se 1 (by rfl) ⟨9945503, by rfl⟩ : syracuseStep 13260671 = 19891007) B19891007
theorem B8840447 : Blo 1551473 8840447 := bstep (se 1 (by rfl) ⟨6630335, by rfl⟩ : syracuseStep 8840447 = 13260671) B13260671
theorem B5893631 : Blo 1551473 5893631 := bstep (se 1 (by rfl) ⟨4420223, by rfl⟩ : syracuseStep 5893631 = 8840447) B8840447
theorem B3929087 : Blo 1551473 3929087 := bstep (se 1 (by rfl) ⟨2946815, by rfl⟩ : syracuseStep 3929087 = 5893631) B5893631
theorem B2619391 : Blo 1551473 2619391 := bstep (se 1 (by rfl) ⟨1964543, by rfl⟩ : syracuseStep 2619391 = 3929087) B3929087
theorem B3492521 : Blo 1551473 3492521 := bstep (se 2 (by rfl) ⟨1309695, by rfl⟩ : syracuseStep 3492521 = 2619391) B2619391
theorem B2328347 : Blo 1551473 2328347 := bstep (se 1 (by rfl) ⟨1746260, by rfl⟩ : syracuseStep 2328347 = 3492521) B3492521
theorem B1552231 : Blo 1551473 1552231 := bstep (se 1 (by rfl) ⟨1164173, by rfl⟩ : syracuseStep 1552231 = 2328347) B2328347

theorem C0 (j : ℕ) (h1 : 387868 ≤ j) (h2 : j ≤ 388367) : Blo 1551473 (4 * j + 3) := by
  interval_cases j
  · exact B1551475
  · exact B1551479
  · exact B1551483
  · exact B1551487
  · exact B1551491
  · exact B1551495
  · exact B1551499
  · exact B1551503
  · exact B1551507
  · exact B1551511
  · exact B1551515
  · exact B1551519
  · exact B1551523
  · exact B1551527
  · exact B1551531
  · exact B1551535
  · exact B1551539
  · exact B1551543
  · exact B1551547
  · exact B1551551
  · exact B1551555
  · exact B1551559
  · exact B1551563
  · exact B1551567
  · exact B1551571
  · exact B1551575
  · exact B1551579
  · exact B1551583
  · exact B1551587
  · exact B1551591
  · exact B1551595
  · exact B1551599
  · exact B1551603
  · exact B1551607
  · exact B1551611
  · exact B1551615
  · exact B1551619
  · exact B1551623
  · exact B1551627
  · exact B1551631
  · exact B1551635
  · exact B1551639
  · exact B1551643
  · exact B1551647
  · exact B1551651
  · exact B1551655
  · exact B1551659
  · exact B1551663
  · exact B1551667
  · exact B1551671
  · exact B1551675
  · exact B1551679
  · exact B1551683
  · exact B1551687
  · exact B1551691
  · exact B1551695
  · exact B1551699
  · exact B1551703
  · exact B1551707
  · exact B1551711
  · exact B1551715
  · exact B1551719
  · exact B1551723
  · exact B1551727
  · exact B1551731
  · exact B1551735
  · exact B1551739
  · exact B1551743
  · exact B1551747
  · exact B1551751
  · exact B1551755
  · exact B1551759
  · exact B1551763
  · exact B1551767
  · exact B1551771
  · exact B1551775
  · exact B1551779
  · exact B1551783
  · exact B1551787
  · exact B1551791
  · exact B1551795
  · exact B1551799
  · exact B1551803
  · exact B1551807
  · exact B1551811
  · exact B1551815
  · exact B1551819
  · exact B1551823
  · exact B1551827
  · exact B1551831
  · exact B1551835
  · exact B1551839
  · exact B1551843
  · exact B1551847
  · exact B1551851
  · exact B1551855
  · exact B1551859
  · exact B1551863
  · exact B1551867
  · exact B1551871
  · exact B1551875
  · exact B1551879
  · exact B1551883
  · exact B1551887
  · exact B1551891
  · exact B1551895
  · exact B1551899
  · exact B1551903
  · exact B1551907
  · exact B1551911
  · exact B1551915
  · exact B1551919
  · exact B1551923
  · exact B1551927
  · exact B1551931
  · exact B1551935
  · exact B1551939
  · exact B1551943
  · exact B1551947
  · exact B1551951
  · exact B1551955
  · exact B1551959
  · exact B1551963
  · exact B1551967
  · exact B1551971
  · exact B1551975
  · exact B1551979
  · exact B1551983
  · exact B1551987
  · exact B1551991
  · exact B1551995
  · exact B1551999
  · exact B1552003
  · exact B1552007
  · exact B1552011
  · exact B1552015
  · exact B1552019
  · exact B1552023
  · exact B1552027
  · exact B1552031
  · exact B1552035
  · exact B1552039
  · exact B1552043
  · exact B1552047
  · exact B1552051
  · exact B1552055
  · exact B1552059
  · exact B1552063
  · exact B1552067
  · exact B1552071
  · exact B1552075
  · exact B1552079
  · exact B1552083
  · exact B1552087
  · exact B1552091
  · exact B1552095
  · exact B1552099
  · exact B1552103
  · exact B1552107
  · exact B1552111
  · exact B1552115
  · exact B1552119
  · exact B1552123
  · exact B1552127
  · exact B1552131
  · exact B1552135
  · exact B1552139
  · exact B1552143
  · exact B1552147
  · exact B1552151
  · exact B1552155
  · exact B1552159
  · exact B1552163
  · exact B1552167
  · exact B1552171
  · exact B1552175
  · exact B1552179
  · exact B1552183
  · exact B1552187
  · exact B1552191
  · exact B1552195
  · exact B1552199
  · exact B1552203
  · exact B1552207
  · exact B1552211
  · exact B1552215
  · exact B1552219
  · exact B1552223
  · exact B1552227
  · exact B1552231
  · exact B1552235
  · exact B1552239
  · exact B1552243
  · exact B1552247
  · exact B1552251
  · exact B1552255
  · exact B1552259
  · exact B1552263
  · exact B1552267
  · exact B1552271
  · exact B1552275
  · exact B1552279
  · exact B1552283
  · exact B1552287
  · exact B1552291
  · exact B1552295
  · exact B1552299
  · exact B1552303
  · exact B1552307
  · exact B1552311
  · exact B1552315
  · exact B1552319
  · exact B1552323
  · exact B1552327
  · exact B1552331
  · exact B1552335
  · exact B1552339
  · exact B1552343
  · exact B1552347
  · exact B1552351
  · exact B1552355
  · exact B1552359
  · exact B1552363
  · exact B1552367
  · exact B1552371
  · exact B1552375
  · exact B1552379
  · exact B1552383
  · exact B1552387
  · exact B1552391
  · exact B1552395
  · exact B1552399
  · exact B1552403
  · exact B1552407
  · exact B1552411
  · exact B1552415
  · exact B1552419
  · exact B1552423
  · exact B1552427
  · exact B1552431
  · exact B1552435
  · exact B1552439
  · exact B1552443
  · exact B1552447
  · exact B1552451
  · exact B1552455
  · exact B1552459
  · exact B1552463
  · exact B1552467
  · exact B1552471
  · exact B1552475
  · exact B1552479
  · exact B1552483
  · exact B1552487
  · exact B1552491
  · exact B1552495
  · exact B1552499
  · exact B1552503
  · exact B1552507
  · exact B1552511
  · exact B1552515
  · exact B1552519
  · exact B1552523
  · exact B1552527
  · exact B1552531
  · exact B1552535
  · exact B1552539
  · exact B1552543
  · exact B1552547
  · exact B1552551
  · exact B1552555
  · exact B1552559
  · exact B1552563
  · exact B1552567
  · exact B1552571
  · exact B1552575
  · exact B1552579
  · exact B1552583
  · exact B1552587
  · exact B1552591
  · exact B1552595
  · exact B1552599
  · exact B1552603
  · exact B1552607
  · exact B1552611
  · exact B1552615
  · exact B1552619
  · exact B1552623
  · exact B1552627
  · exact B1552631
  · exact B1552635
  · exact B1552639
  · exact B1552643
  · exact B1552647
  · exact B1552651
  · exact B1552655
  · exact B1552659
  · exact B1552663
  · exact B1552667
  · exact B1552671
  · exact B1552675
  · exact B1552679
  · exact B1552683
  · exact B1552687
  · exact B1552691
  · exact B1552695
  · exact B1552699
  · exact B1552703
  · exact B1552707
  · exact B1552711
  · exact B1552715
  · exact B1552719
  · exact B1552723
  · exact B1552727
  · exact B1552731
  · exact B1552735
  · exact B1552739
  · exact B1552743
  · exact B1552747
  · exact B1552751
  · exact B1552755
  · exact B1552759
  · exact B1552763
  · exact B1552767
  · exact B1552771
  · exact B1552775
  · exact B1552779
  · exact B1552783
  · exact B1552787
  · exact B1552791
  · exact B1552795
  · exact B1552799
  · exact B1552803
  · exact B1552807
  · exact B1552811
  · exact B1552815
  · exact B1552819
  · exact B1552823
  · exact B1552827
  · exact B1552831
  · exact B1552835
  · exact B1552839
  · exact B1552843
  · exact B1552847
  · exact B1552851
  · exact B1552855
  · exact B1552859
  · exact B1552863
  · exact B1552867
  · exact B1552871
  · exact B1552875
  · exact B1552879
  · exact B1552883
  · exact B1552887
  · exact B1552891
  · exact B1552895
  · exact B1552899
  · exact B1552903
  · exact B1552907
  · exact B1552911
  · exact B1552915
  · exact B1552919
  · exact B1552923
  · exact B1552927
  · exact B1552931
  · exact B1552935
  · exact B1552939
  · exact B1552943
  · exact B1552947
  · exact B1552951
  · exact B1552955
  · exact B1552959
  · exact B1552963
  · exact B1552967
  · exact B1552971
  · exact B1552975
  · exact B1552979
  · exact B1552983
  · exact B1552987
  · exact B1552991
  · exact B1552995
  · exact B1552999
  · exact B1553003
  · exact B1553007
  · exact B1553011
  · exact B1553015
  · exact B1553019
  · exact B1553023
  · exact B1553027
  · exact B1553031
  · exact B1553035
  · exact B1553039
  · exact B1553043
  · exact B1553047
  · exact B1553051
  · exact B1553055
  · exact B1553059
  · exact B1553063
  · exact B1553067
  · exact B1553071
  · exact B1553075
  · exact B1553079
  · exact B1553083
  · exact B1553087
  · exact B1553091
  · exact B1553095
  · exact B1553099
  · exact B1553103
  · exact B1553107
  · exact B1553111
  · exact B1553115
  · exact B1553119
  · exact B1553123
  · exact B1553127
  · exact B1553131
  · exact B1553135
  · exact B1553139
  · exact B1553143
  · exact B1553147
  · exact B1553151
  · exact B1553155
  · exact B1553159
  · exact B1553163
  · exact B1553167
  · exact B1553171
  · exact B1553175
  · exact B1553179
  · exact B1553183
  · exact B1553187
  · exact B1553191
  · exact B1553195
  · exact B1553199
  · exact B1553203
  · exact B1553207
  · exact B1553211
  · exact B1553215
  · exact B1553219
  · exact B1553223
  · exact B1553227
  · exact B1553231
  · exact B1553235
  · exact B1553239
  · exact B1553243
  · exact B1553247
  · exact B1553251
  · exact B1553255
  · exact B1553259
  · exact B1553263
  · exact B1553267
  · exact B1553271
  · exact B1553275
  · exact B1553279
  · exact B1553283
  · exact B1553287
  · exact B1553291
  · exact B1553295
  · exact B1553299
  · exact B1553303
  · exact B1553307
  · exact B1553311
  · exact B1553315
  · exact B1553319
  · exact B1553323
  · exact B1553327
  · exact B1553331
  · exact B1553335
  · exact B1553339
  · exact B1553343
  · exact B1553347
  · exact B1553351
  · exact B1553355
  · exact B1553359
  · exact B1553363
  · exact B1553367
  · exact B1553371
  · exact B1553375
  · exact B1553379
  · exact B1553383
  · exact B1553387
  · exact B1553391
  · exact B1553395
  · exact B1553399
  · exact B1553403
  · exact B1553407
  · exact B1553411
  · exact B1553415
  · exact B1553419
  · exact B1553423
  · exact B1553427
  · exact B1553431
  · exact B1553435
  · exact B1553439
  · exact B1553443
  · exact B1553447
  · exact B1553451
  · exact B1553455
  · exact B1553459
  · exact B1553463
  · exact B1553467
  · exact B1553471

theorem solution (m : ℕ) (hlo : 1551473 ≤ m) (hhi : m ≤ 1553473) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 387868 ≤ j := by omega
    have hj2 : j ≤ 388367 := by omega
    have hb : Blo 1551473 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
