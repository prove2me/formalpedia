-- Prove2me | solution 1 for syracuse_descends_range_1148636_1152636
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:47.753644+00:00
-- url     : https://prove2.me/submissions/a421a0ab-3e33-4ab7-bcf7-3bfb19dc76e2

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


theorem B1310737 : Blo 1148636 1310737 := bbase (se 2 (by rfl) ⟨491526, by rfl⟩ : syracuseStep 1310737 = 983053) (by norm_num)
theorem B2588741 : Blo 1148636 2588741 := bbase (se 4 (by rfl) ⟨242694, by rfl⟩ : syracuseStep 2588741 = 485389) (by norm_num)
theorem B2621525 : Blo 1148636 2621525 := bbase (se 8 (by rfl) ⟨15360, by rfl⟩ : syracuseStep 2621525 = 30721) (by norm_num)
theorem B2916445 : Blo 1148636 2916445 := bbase (se 3 (by rfl) ⟨546833, by rfl⟩ : syracuseStep 2916445 = 1093667) (by norm_num)
theorem B3113093 : Blo 1148636 3113093 := bbase (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) (by norm_num)
theorem B2588813 : Blo 1148636 2588813 := bbase (se 3 (by rfl) ⟨485402, by rfl⟩ : syracuseStep 2588813 = 970805) (by norm_num)
theorem B1310909 : Blo 1148636 1310909 := bbase (se 3 (by rfl) ⟨245795, by rfl⟩ : syracuseStep 1310909 = 491591) (by norm_num)
theorem B2916557 : Blo 1148636 2916557 := bbase (se 3 (by rfl) ⟨546854, by rfl⟩ : syracuseStep 2916557 = 1093709) (by norm_num)
theorem B2588885 : Blo 1148636 2588885 := bbase (se 7 (by rfl) ⟨30338, by rfl⟩ : syracuseStep 2588885 = 60677) (by norm_num)
theorem B3277061 : Blo 1148636 3277061 := bbase (se 4 (by rfl) ⟨307224, by rfl⟩ : syracuseStep 3277061 = 614449) (by norm_num)
theorem B2588957 : Blo 1148636 2588957 := bbase (se 3 (by rfl) ⟨485429, by rfl⟩ : syracuseStep 2588957 = 970859) (by norm_num)
theorem B2589029 : Blo 1148636 2589029 := bbase (se 4 (by rfl) ⟨242721, by rfl⟩ : syracuseStep 2589029 = 485443) (by norm_num)
theorem B2916749 : Blo 1148636 2916749 := bbase (se 3 (by rfl) ⟨546890, by rfl⟩ : syracuseStep 2916749 = 1093781) (by norm_num)
theorem B2589101 : Blo 1148636 2589101 := bbase (se 3 (by rfl) ⟨485456, by rfl⟩ : syracuseStep 2589101 = 970913) (by norm_num)
theorem B2589173 : Blo 1148636 2589173 := bbase (se 5 (by rfl) ⟨121367, by rfl⟩ : syracuseStep 2589173 = 242735) (by norm_num)
theorem B1475101 : Blo 1148636 1475101 := bbase (se 3 (by rfl) ⟨276581, by rfl⟩ : syracuseStep 1475101 = 553163) (by norm_num)
theorem B2589245 : Blo 1148636 2589245 := bbase (se 3 (by rfl) ⟨485483, by rfl⟩ : syracuseStep 2589245 = 970967) (by norm_num)
theorem B2458181 : Blo 1148636 2458181 := bbase (se 4 (by rfl) ⟨230454, by rfl⟩ : syracuseStep 2458181 = 460909) (by norm_num)
theorem B1966693 : Blo 1148636 1966693 := bbase (se 4 (by rfl) ⟨184377, by rfl⟩ : syracuseStep 1966693 = 368755) (by norm_num)
theorem B4915829 : Blo 1148636 4915829 := bbase (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) (by norm_num)
theorem B2589317 : Blo 1148636 2589317 := bbase (se 4 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 2589317 = 485497) (by norm_num)
theorem B1475245 : Blo 1148636 1475245 := bbase (se 3 (by rfl) ⟨276608, by rfl⟩ : syracuseStep 1475245 = 553217) (by norm_num)
theorem B3277493 : Blo 1148636 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B2589389 : Blo 1148636 2589389 := bbase (se 3 (by rfl) ⟨485510, by rfl⟩ : syracuseStep 2589389 = 971021) (by norm_num)
theorem B2458325 : Blo 1148636 2458325 := bbase (se 7 (by rfl) ⟨28808, by rfl⟩ : syracuseStep 2458325 = 57617) (by norm_num)
theorem B2917093 : Blo 1148636 2917093 := bbase (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) (by norm_num)
theorem B5899013 : Blo 1148636 5899013 := bbase (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) (by norm_num)
theorem B1311493 : Blo 1148636 1311493 := bbase (se 4 (by rfl) ⟨122952, by rfl⟩ : syracuseStep 1311493 = 245905) (by norm_num)
theorem B2589461 : Blo 1148636 2589461 := bbase (se 6 (by rfl) ⟨60690, by rfl⟩ : syracuseStep 2589461 = 121381) (by norm_num)
theorem B2917205 : Blo 1148636 2917205 := bbase (se 9 (by rfl) ⟨8546, by rfl⟩ : syracuseStep 2917205 = 17093) (by norm_num)
theorem B2589533 : Blo 1148636 2589533 := bbase (se 3 (by rfl) ⟨485537, by rfl⟩ : syracuseStep 2589533 = 971075) (by norm_num)
theorem B22119317 : Blo 1148636 22119317 := bbase (se 6 (by rfl) ⟨518421, by rfl⟩ : syracuseStep 22119317 = 1036843) (by norm_num)
theorem B2589605 : Blo 1148636 2589605 := bbase (se 4 (by rfl) ⟨242775, by rfl⟩ : syracuseStep 2589605 = 485551) (by norm_num)
theorem B1967069 : Blo 1148636 1967069 := bbase (se 3 (by rfl) ⟨368825, by rfl⟩ : syracuseStep 1967069 = 737651) (by norm_num)
theorem B2589677 : Blo 1148636 2589677 := bbase (se 3 (by rfl) ⟨485564, by rfl⟩ : syracuseStep 2589677 = 971129) (by norm_num)
theorem B9339893 : Blo 1148636 9339893 := bbase (se 5 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 9339893 = 875615) (by norm_num)
theorem B2917397 : Blo 1148636 2917397 := bbase (se 6 (by rfl) ⟨68376, by rfl⟩ : syracuseStep 2917397 = 136753) (by norm_num)
theorem B1639453 : Blo 1148636 1639453 := bbase (se 3 (by rfl) ⟨307397, by rfl⟩ : syracuseStep 1639453 = 614795) (by norm_num)
theorem B2589749 : Blo 1148636 2589749 := bbase (se 5 (by rfl) ⟨121394, by rfl⟩ : syracuseStep 2589749 = 242789) (by norm_num)
theorem B5833781 : Blo 1148636 5833781 := bbase (se 5 (by rfl) ⟨273458, by rfl⟩ : syracuseStep 5833781 = 546917) (by norm_num)
theorem B1967213 : Blo 1148636 1967213 := bbase (se 3 (by rfl) ⟨368852, by rfl⟩ : syracuseStep 1967213 = 737705) (by norm_num)
theorem B2589821 : Blo 1148636 2589821 := bbase (se 3 (by rfl) ⟨485591, by rfl⟩ : syracuseStep 2589821 = 971183) (by norm_num)
theorem B1311913 : Blo 1148636 1311913 := bbase (se 2 (by rfl) ⟨491967, by rfl⟩ : syracuseStep 1311913 = 983935) (by norm_num)
theorem B2589893 : Blo 1148636 2589893 := bbase (se 4 (by rfl) ⟨242802, by rfl⟩ : syracuseStep 2589893 = 485605) (by norm_num)
theorem B2589965 : Blo 1148636 2589965 := bbase (se 3 (by rfl) ⟨485618, by rfl⟩ : syracuseStep 2589965 = 971237) (by norm_num)
theorem B2590037 : Blo 1148636 2590037 := bbase (se 12 (by rfl) ⟨948, by rfl⟩ : syracuseStep 2590037 = 1897) (by norm_num)
theorem B2590109 : Blo 1148636 2590109 := bbase (se 3 (by rfl) ⟨485645, by rfl⟩ : syracuseStep 2590109 = 971291) (by norm_num)
theorem B3278245 : Blo 1148636 3278245 := bbase (se 4 (by rfl) ⟨307335, by rfl⟩ : syracuseStep 3278245 = 614671) (by norm_num)
theorem B2459069 : Blo 1148636 2459069 := bbase (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) (by norm_num)
theorem B2590181 : Blo 1148636 2590181 := bbase (se 4 (by rfl) ⟨242829, by rfl⟩ : syracuseStep 2590181 = 485659) (by norm_num)
theorem B2590253 : Blo 1148636 2590253 := bbase (se 3 (by rfl) ⟨485672, by rfl⟩ : syracuseStep 2590253 = 971345) (by norm_num)
theorem B4916821 : Blo 1148636 4916821 := bbase (se 8 (by rfl) ⟨28809, by rfl⟩ : syracuseStep 4916821 = 57619) (by norm_num)
theorem B1640045 : Blo 1148636 1640045 := bbase (se 3 (by rfl) ⟨307508, by rfl⟩ : syracuseStep 1640045 = 615017) (by norm_num)
theorem B2590325 : Blo 1148636 2590325 := bbase (se 5 (by rfl) ⟨121421, by rfl⟩ : syracuseStep 2590325 = 242843) (by norm_num)
theorem B1312405 : Blo 1148636 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B2590397 : Blo 1148636 2590397 := bbase (se 3 (by rfl) ⟨485699, by rfl⟩ : syracuseStep 2590397 = 971399) (by norm_num)
theorem B1640125 : Blo 1148636 1640125 := bbase (se 3 (by rfl) ⟨307523, by rfl⟩ : syracuseStep 1640125 = 615047) (by norm_num)
theorem B2590469 : Blo 1148636 2590469 := bbase (se 4 (by rfl) ⟨242856, by rfl⟩ : syracuseStep 2590469 = 485713) (by norm_num)
theorem B2623277 : Blo 1148636 2623277 := bbase (se 3 (by rfl) ⟨491864, by rfl⟩ : syracuseStep 2623277 = 983729) (by norm_num)
theorem B1640245 : Blo 1148636 1640245 := bbase (se 5 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 1640245 = 153773) (by norm_num)
theorem B2590541 : Blo 1148636 2590541 := bbase (se 3 (by rfl) ⟨485726, by rfl⟩ : syracuseStep 2590541 = 971453) (by norm_num)
theorem B2590613 : Blo 1148636 2590613 := bbase (se 6 (by rfl) ⟨60717, by rfl⟩ : syracuseStep 2590613 = 121435) (by norm_num)
theorem B1640341 : Blo 1148636 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B1312697 : Blo 1148636 1312697 := bbase (se 2 (by rfl) ⟨492261, by rfl⟩ : syracuseStep 1312697 = 984523) (by norm_num)
theorem B8521685 : Blo 1148636 8521685 := bbase (se 7 (by rfl) ⟨99863, by rfl⟩ : syracuseStep 8521685 = 199727) (by norm_num)
theorem B2590685 : Blo 1148636 2590685 := bbase (se 3 (by rfl) ⟨485753, by rfl⟩ : syracuseStep 2590685 = 971507) (by norm_num)
theorem B1312753 : Blo 1148636 1312753 := bbase (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) (by norm_num)
theorem B1312789 : Blo 1148636 1312789 := bbase (se 6 (by rfl) ⟨30768, by rfl⟩ : syracuseStep 1312789 = 61537) (by norm_num)
theorem B2590757 : Blo 1148636 2590757 := bbase (se 4 (by rfl) ⟨242883, by rfl⟩ : syracuseStep 2590757 = 485767) (by norm_num)
theorem B2951261 : Blo 1148636 2951261 := bbase (se 3 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 2951261 = 1106723) (by norm_num)
theorem B2590829 : Blo 1148636 2590829 := bbase (se 3 (by rfl) ⟨485780, by rfl⟩ : syracuseStep 2590829 = 971561) (by norm_num)
theorem B2459821 : Blo 1148636 2459821 := bbase (se 3 (by rfl) ⟨461216, by rfl⟩ : syracuseStep 2459821 = 922433) (by norm_num)
theorem B2590901 : Blo 1148636 2590901 := bbase (se 5 (by rfl) ⟨121448, by rfl⟩ : syracuseStep 2590901 = 242897) (by norm_num)
theorem B3147973 : Blo 1148636 3147973 := bbase (se 4 (by rfl) ⟨295122, by rfl⟩ : syracuseStep 3147973 = 590245) (by norm_num)
theorem B2590973 : Blo 1148636 2590973 := bbase (se 3 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 2590973 = 971615) (by norm_num)
theorem B7375157 : Blo 1148636 7375157 := bbase (se 5 (by rfl) ⟨345710, by rfl⟩ : syracuseStep 7375157 = 691421) (by norm_num)
theorem B2459965 : Blo 1148636 2459965 := bbase (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) (by norm_num)
theorem B2591045 : Blo 1148636 2591045 := bbase (se 4 (by rfl) ⟨242910, by rfl⟩ : syracuseStep 2591045 = 485821) (by norm_num)
theorem B5835077 : Blo 1148636 5835077 := bbase (se 4 (by rfl) ⟨547038, by rfl⟩ : syracuseStep 5835077 = 1094077) (by norm_num)
theorem B2623861 : Blo 1148636 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B1640837 : Blo 1148636 1640837 := bbase (se 4 (by rfl) ⟨153828, by rfl⟩ : syracuseStep 1640837 = 307657) (by norm_num)
theorem B1477001 : Blo 1148636 1477001 := bbase (se 2 (by rfl) ⟨553875, by rfl⟩ : syracuseStep 1477001 = 1107751) (by norm_num)
theorem B2591117 : Blo 1148636 2591117 := bbase (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) (by norm_num)
theorem B2329013 : Blo 1148636 2329013 := bbase (se 5 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 2329013 = 218345) (by norm_num)
theorem B2591189 : Blo 1148636 2591189 := bbase (se 7 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 2591189 = 60731) (by norm_num)
theorem B1313281 : Blo 1148636 1313281 := bbase (se 2 (by rfl) ⟨492480, by rfl⟩ : syracuseStep 1313281 = 984961) (by norm_num)
theorem B2591261 : Blo 1148636 2591261 := bbase (se 3 (by rfl) ⟨485861, by rfl⟩ : syracuseStep 2591261 = 971723) (by norm_num)
theorem B2591333 : Blo 1148636 2591333 := bbase (se 4 (by rfl) ⟨242937, by rfl⟩ : syracuseStep 2591333 = 485875) (by norm_num)
theorem B2591405 : Blo 1148636 2591405 := bbase (se 3 (by rfl) ⟨485888, by rfl⟩ : syracuseStep 2591405 = 971777) (by norm_num)
theorem B2460341 : Blo 1148636 2460341 := bbase (se 5 (by rfl) ⟨115328, by rfl⟩ : syracuseStep 2460341 = 230657) (by norm_num)
theorem B2591477 : Blo 1148636 2591477 := bbase (se 5 (by rfl) ⟨121475, by rfl⟩ : syracuseStep 2591477 = 242951) (by norm_num)
theorem B2591549 : Blo 1148636 2591549 := bbase (se 3 (by rfl) ⟨485915, by rfl⟩ : syracuseStep 2591549 = 971831) (by norm_num)
theorem B1313609 : Blo 1148636 1313609 := bbase (se 2 (by rfl) ⟨492603, by rfl⟩ : syracuseStep 1313609 = 985207) (by norm_num)
theorem B1477453 : Blo 1148636 1477453 := bbase (se 3 (by rfl) ⟨277022, by rfl⟩ : syracuseStep 1477453 = 554045) (by norm_num)
theorem B2591621 : Blo 1148636 2591621 := bbase (se 4 (by rfl) ⟨242964, by rfl⟩ : syracuseStep 2591621 = 485929) (by norm_num)
theorem B2591693 : Blo 1148636 2591693 := bbase (se 3 (by rfl) ⟨485942, by rfl⟩ : syracuseStep 2591693 = 971885) (by norm_num)
theorem B2591765 : Blo 1148636 2591765 := bbase (se 6 (by rfl) ⟨60744, by rfl⟩ : syracuseStep 2591765 = 121489) (by norm_num)
theorem B2460709 : Blo 1148636 2460709 := bbase (se 4 (by rfl) ⟨230691, by rfl⟩ : syracuseStep 2460709 = 461383) (by norm_num)
theorem B2591837 : Blo 1148636 2591837 := bbase (se 3 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 2591837 = 971939) (by norm_num)
theorem B2591909 : Blo 1148636 2591909 := bbase (se 4 (by rfl) ⟨242991, by rfl⟩ : syracuseStep 2591909 = 485983) (by norm_num)
theorem B2591981 : Blo 1148636 2591981 := bbase (se 3 (by rfl) ⟨485996, by rfl⟩ : syracuseStep 2591981 = 971993) (by norm_num)
theorem B8752373 : Blo 1148636 8752373 := bbase (se 5 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 8752373 = 820535) (by norm_num)
theorem B2592053 : Blo 1148636 2592053 := bbase (se 5 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 2592053 = 243005) (by norm_num)
theorem B5606741 : Blo 1148636 5606741 := bbase (se 11 (by rfl) ⟨4106, by rfl⟩ : syracuseStep 5606741 = 8213) (by norm_num)
theorem B9833845 : Blo 1148636 9833845 := bbase (se 5 (by rfl) ⟨460961, by rfl⟩ : syracuseStep 9833845 = 921923) (by norm_num)
theorem B2592125 : Blo 1148636 2592125 := bbase (se 3 (by rfl) ⟨486023, by rfl⟩ : syracuseStep 2592125 = 972047) (by norm_num)
theorem B1314193 : Blo 1148636 1314193 := bbase (se 2 (by rfl) ⟨492822, by rfl⟩ : syracuseStep 1314193 = 985645) (by norm_num)
theorem B2592197 : Blo 1148636 2592197 := bbase (se 4 (by rfl) ⟨243018, by rfl⟩ : syracuseStep 2592197 = 486037) (by norm_num)
theorem B2592269 : Blo 1148636 2592269 := bbase (se 3 (by rfl) ⟨486050, by rfl⟩ : syracuseStep 2592269 = 972101) (by norm_num)
theorem B2428453 : Blo 1148636 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B2494013 : Blo 1148636 2494013 := bbase (se 3 (by rfl) ⟨467627, by rfl⟩ : syracuseStep 2494013 = 935255) (by norm_num)
theorem B2592341 : Blo 1148636 2592341 := bbase (se 8 (by rfl) ⟨15189, by rfl⟩ : syracuseStep 2592341 = 30379) (by norm_num)
theorem B2592413 : Blo 1148636 2592413 := bbase (se 3 (by rfl) ⟨486077, by rfl⟩ : syracuseStep 2592413 = 972155) (by norm_num)
theorem B4361957 : Blo 1148636 4361957 := bbase (se 4 (by rfl) ⟨408933, by rfl⟩ : syracuseStep 4361957 = 817867) (by norm_num)
theorem B2592485 : Blo 1148636 2592485 := bbase (se 4 (by rfl) ⟨243045, by rfl⟩ : syracuseStep 2592485 = 486091) (by norm_num)
theorem B2592557 : Blo 1148636 2592557 := bbase (se 3 (by rfl) ⟨486104, by rfl⟩ : syracuseStep 2592557 = 972209) (by norm_num)
theorem B8294197 : Blo 1148636 8294197 := bbase (se 5 (by rfl) ⟨388790, by rfl⟩ : syracuseStep 8294197 = 777581) (by norm_num)
theorem B2592629 : Blo 1148636 2592629 := bbase (se 5 (by rfl) ⟨121529, by rfl⟩ : syracuseStep 2592629 = 243059) (by norm_num)
theorem B2592701 : Blo 1148636 2592701 := bbase (se 3 (by rfl) ⟨486131, by rfl⟩ : syracuseStep 2592701 = 972263) (by norm_num)
theorem B5050325 : Blo 1148636 5050325 := bbase (se 7 (by rfl) ⟨59183, by rfl⟩ : syracuseStep 5050325 = 118367) (by norm_num)
theorem B11800565 : Blo 1148636 11800565 := bbase (se 5 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 11800565 = 1106303) (by norm_num)
theorem B4362245 : Blo 1148636 4362245 := bbase (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) (by norm_num)
theorem B2592773 : Blo 1148636 2592773 := bbase (se 4 (by rfl) ⟨243072, by rfl⟩ : syracuseStep 2592773 = 486145) (by norm_num)
theorem B12455957 : Blo 1148636 12455957 := bbase (se 6 (by rfl) ⟨291936, by rfl⟩ : syracuseStep 12455957 = 583873) (by norm_num)
theorem B5247029 : Blo 1148636 5247029 := bbase (se 5 (by rfl) ⟨245954, by rfl⟩ : syracuseStep 5247029 = 491909) (by norm_num)
theorem B2592845 : Blo 1148636 2592845 := bbase (se 3 (by rfl) ⟨486158, by rfl⟩ : syracuseStep 2592845 = 972317) (by norm_num)
theorem B2592917 : Blo 1148636 2592917 := bbase (se 6 (by rfl) ⟨60771, by rfl⟩ : syracuseStep 2592917 = 121543) (by norm_num)
theorem B1380521 : Blo 1148636 1380521 := bbase (se 2 (by rfl) ⟨517695, by rfl⟩ : syracuseStep 1380521 = 1035391) (by norm_num)
theorem B2330821 : Blo 1148636 2330821 := bbase (se 4 (by rfl) ⟨218514, by rfl⟩ : syracuseStep 2330821 = 437029) (by norm_num)
theorem B3281093 : Blo 1148636 3281093 := bbase (se 4 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 3281093 = 615205) (by norm_num)
theorem B2592989 : Blo 1148636 2592989 := bbase (se 3 (by rfl) ⟨486185, by rfl⟩ : syracuseStep 2592989 = 972371) (by norm_num)
theorem B8392949 : Blo 1148636 8392949 := bbase (se 5 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 8392949 = 786839) (by norm_num)
theorem B2593061 : Blo 1148636 2593061 := bbase (se 4 (by rfl) ⟨243099, by rfl⟩ : syracuseStep 2593061 = 486199) (by norm_num)
theorem B2593133 : Blo 1148636 2593133 := bbase (se 3 (by rfl) ⟨486212, by rfl⟩ : syracuseStep 2593133 = 972425) (by norm_num)
theorem B2593205 : Blo 1148636 2593205 := bbase (se 5 (by rfl) ⟨121556, by rfl⟩ : syracuseStep 2593205 = 243113) (by norm_num)
theorem B1380829 : Blo 1148636 1380829 := bbase (se 3 (by rfl) ⟨258905, by rfl⟩ : syracuseStep 1380829 = 517811) (by norm_num)
theorem B2593277 : Blo 1148636 2593277 := bbase (se 3 (by rfl) ⟨486239, by rfl⟩ : syracuseStep 2593277 = 972479) (by norm_num)
theorem B2593349 : Blo 1148636 2593349 := bbase (se 4 (by rfl) ⟨243126, by rfl⟩ : syracuseStep 2593349 = 486253) (by norm_num)
theorem B1380997 : Blo 1148636 1380997 := bbase (se 4 (by rfl) ⟨129468, by rfl⟩ : syracuseStep 1380997 = 258937) (by norm_num)
theorem B2593421 : Blo 1148636 2593421 := bbase (se 3 (by rfl) ⟨486266, by rfl⟩ : syracuseStep 2593421 = 972533) (by norm_num)
theorem B1774285 : Blo 1148636 1774285 := bbase (se 3 (by rfl) ⟨332678, by rfl⟩ : syracuseStep 1774285 = 665357) (by norm_num)
theorem B1970909 : Blo 1148636 1970909 := bbase (se 3 (by rfl) ⟨369545, by rfl⟩ : syracuseStep 1970909 = 739091) (by norm_num)
theorem B1839925 : Blo 1148636 1839925 := bbase (se 5 (by rfl) ⟨86246, by rfl⟩ : syracuseStep 1839925 = 172493) (by norm_num)
theorem B1381193 : Blo 1148636 1381193 := bbase (se 2 (by rfl) ⟨517947, by rfl⟩ : syracuseStep 1381193 = 1035895) (by norm_num)
theorem B6558677 : Blo 1148636 6558677 := bbase (se 7 (by rfl) ⟨76859, by rfl⟩ : syracuseStep 6558677 = 153719) (by norm_num)
theorem B1938397 : Blo 1148636 1938397 := bbase (se 3 (by rfl) ⟨363449, by rfl⟩ : syracuseStep 1938397 = 726899) (by norm_num)
theorem B1938485 : Blo 1148636 1938485 := bbase (se 5 (by rfl) ⟨90866, by rfl⟩ : syracuseStep 1938485 = 181733) (by norm_num)
theorem B3413125 : Blo 1148636 3413125 := bbase (se 4 (by rfl) ⟨319980, by rfl⟩ : syracuseStep 3413125 = 639961) (by norm_num)
theorem B4363429 : Blo 1148636 4363429 := bbase (se 4 (by rfl) ⟨409071, by rfl⟩ : syracuseStep 4363429 = 818143) (by norm_num)
theorem B1938613 : Blo 1148636 1938613 := bbase (se 5 (by rfl) ⟨90872, by rfl⟩ : syracuseStep 1938613 = 181745) (by norm_num)
theorem B1938701 : Blo 1148636 1938701 := bbase (se 3 (by rfl) ⟨363506, by rfl⟩ : syracuseStep 1938701 = 727013) (by norm_num)
theorem B9835829 : Blo 1148636 9835829 := bbase (se 5 (by rfl) ⟨461054, by rfl⟩ : syracuseStep 9835829 = 922109) (by norm_num)
theorem B1552389461 : Blo 1148636 1552389461 := bbase (se 14 (by rfl) ⟨142125, by rfl⟩ : syracuseStep 1552389461 = 284251) (by norm_num)
theorem B1840477 : Blo 1148636 1840477 := bbase (se 3 (by rfl) ⟨345089, by rfl⟩ : syracuseStep 1840477 = 690179) (by norm_num)
theorem B3282277 : Blo 1148636 3282277 := bbase (se 4 (by rfl) ⟨307713, by rfl⟩ : syracuseStep 3282277 = 615427) (by norm_num)
theorem B1938829 : Blo 1148636 1938829 := bbase (se 3 (by rfl) ⟨363530, by rfl⟩ : syracuseStep 1938829 = 727061) (by norm_num)
theorem B4363733 : Blo 1148636 4363733 := bbase (se 7 (by rfl) ⟨51137, by rfl⟩ : syracuseStep 4363733 = 102275) (by norm_num)
theorem B1938917 : Blo 1148636 1938917 := bbase (se 4 (by rfl) ⟨181773, by rfl⟩ : syracuseStep 1938917 = 363547) (by norm_num)
theorem B1840733 : Blo 1148636 1840733 := bbase (se 3 (by rfl) ⟨345137, by rfl⟩ : syracuseStep 1840733 = 690275) (by norm_num)
theorem B4658789 : Blo 1148636 4658789 := bbase (se 4 (by rfl) ⟨436761, by rfl⟩ : syracuseStep 4658789 = 873523) (by norm_num)
theorem B1939045 : Blo 1148636 1939045 := bbase (se 4 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 1939045 = 363571) (by norm_num)
theorem B1939133 : Blo 1148636 1939133 := bbase (se 3 (by rfl) ⟨363587, by rfl⟩ : syracuseStep 1939133 = 727175) (by norm_num)
theorem B4658933 : Blo 1148636 4658933 := bbase (se 5 (by rfl) ⟨218387, by rfl⟩ : syracuseStep 4658933 = 436775) (by norm_num)
theorem B1939261 : Blo 1148636 1939261 := bbase (se 3 (by rfl) ⟨363611, by rfl⟩ : syracuseStep 1939261 = 727223) (by norm_num)
theorem B1939349 : Blo 1148636 1939349 := bbase (se 6 (by rfl) ⟨45453, by rfl⟩ : syracuseStep 1939349 = 90907) (by norm_num)
theorem B1939477 : Blo 1148636 1939477 := bbase (se 6 (by rfl) ⟨45456, by rfl⟩ : syracuseStep 1939477 = 90913) (by norm_num)
theorem B1939565 : Blo 1148636 1939565 := bbase (se 3 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 1939565 = 727337) (by norm_num)
theorem B2627749 : Blo 1148636 2627749 := bbase (se 4 (by rfl) ⟨246351, by rfl⟩ : syracuseStep 2627749 = 492703) (by norm_num)
theorem B1939693 : Blo 1148636 1939693 := bbase (se 3 (by rfl) ⟨363692, by rfl⟩ : syracuseStep 1939693 = 727385) (by norm_num)
theorem B1841437 : Blo 1148636 1841437 := bbase (se 3 (by rfl) ⟨345269, by rfl⟩ : syracuseStep 1841437 = 690539) (by norm_num)
theorem B1939781 : Blo 1148636 1939781 := bbase (se 4 (by rfl) ⟨181854, by rfl⟩ : syracuseStep 1939781 = 363709) (by norm_num)
theorem B1382765 : Blo 1148636 1382765 := bbase (se 3 (by rfl) ⟨259268, by rfl⟩ : syracuseStep 1382765 = 518537) (by norm_num)
theorem B1382789 : Blo 1148636 1382789 := bbase (se 4 (by rfl) ⟨129636, by rfl⟩ : syracuseStep 1382789 = 259273) (by norm_num)
theorem B1939909 : Blo 1148636 1939909 := bbase (se 4 (by rfl) ⟨181866, by rfl⟩ : syracuseStep 1939909 = 363733) (by norm_num)
theorem B4921829 : Blo 1148636 4921829 := bbase (se 4 (by rfl) ⟨461421, by rfl⟩ : syracuseStep 4921829 = 922843) (by norm_num)
theorem B1939997 : Blo 1148636 1939997 := bbase (se 3 (by rfl) ⟨363749, by rfl⟩ : syracuseStep 1939997 = 727499) (by norm_num)
theorem B1940125 : Blo 1148636 1940125 := bbase (se 3 (by rfl) ⟨363773, by rfl⟩ : syracuseStep 1940125 = 727547) (by norm_num)
theorem B2071213 : Blo 1148636 2071213 := bbase (se 3 (by rfl) ⟨388352, by rfl⟩ : syracuseStep 2071213 = 776705) (by norm_num)
theorem B1383097 : Blo 1148636 1383097 := bbase (se 2 (by rfl) ⟨518661, by rfl⟩ : syracuseStep 1383097 = 1037323) (by norm_num)
theorem B1841861 : Blo 1148636 1841861 := bbase (se 4 (by rfl) ⟨172674, by rfl⟩ : syracuseStep 1841861 = 345349) (by norm_num)
theorem B1940213 : Blo 1148636 1940213 := bbase (se 5 (by rfl) ⟨90947, by rfl⟩ : syracuseStep 1940213 = 181895) (by norm_num)
theorem B4922117 : Blo 1148636 4922117 := bbase (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) (by norm_num)
theorem B1383269 : Blo 1148636 1383269 := bbase (se 4 (by rfl) ⟨129681, by rfl⟩ : syracuseStep 1383269 = 259363) (by norm_num)
theorem B1940341 : Blo 1148636 1940341 := bbase (se 5 (by rfl) ⟨90953, by rfl⟩ : syracuseStep 1940341 = 181907) (by norm_num)
theorem B1940429 : Blo 1148636 1940429 := bbase (se 3 (by rfl) ⟨363830, by rfl⟩ : syracuseStep 1940429 = 727661) (by norm_num)
theorem B1383385 : Blo 1148636 1383385 := bbase (se 2 (by rfl) ⟨518769, by rfl⟩ : syracuseStep 1383385 = 1037539) (by norm_num)
theorem B1842149 : Blo 1148636 1842149 := bbase (se 4 (by rfl) ⟨172701, by rfl⟩ : syracuseStep 1842149 = 345403) (by norm_num)
theorem B1383481 : Blo 1148636 1383481 := bbase (se 2 (by rfl) ⟨518805, by rfl⟩ : syracuseStep 1383481 = 1037611) (by norm_num)
theorem B5905477 : Blo 1148636 5905477 := bbase (se 4 (by rfl) ⟨553638, by rfl⟩ : syracuseStep 5905477 = 1107277) (by norm_num)
theorem B1940557 : Blo 1148636 1940557 := bbase (se 3 (by rfl) ⟨363854, by rfl⟩ : syracuseStep 1940557 = 727709) (by norm_num)
theorem B1940645 : Blo 1148636 1940645 := bbase (se 4 (by rfl) ⟨181935, by rfl⟩ : syracuseStep 1940645 = 363871) (by norm_num)
theorem B2759869 : Blo 1148636 2759869 := bbase (se 3 (by rfl) ⟨517475, by rfl⟩ : syracuseStep 2759869 = 1034951) (by norm_num)
theorem B1842373 : Blo 1148636 1842373 := bbase (se 4 (by rfl) ⟨172722, by rfl⟩ : syracuseStep 1842373 = 345445) (by norm_num)
theorem B1383625 : Blo 1148636 1383625 := bbase (se 2 (by rfl) ⟨518859, by rfl⟩ : syracuseStep 1383625 = 1037719) (by norm_num)
theorem B1940773 : Blo 1148636 1940773 := bbase (se 4 (by rfl) ⟨181947, by rfl⟩ : syracuseStep 1940773 = 363895) (by norm_num)
theorem B13114709 : Blo 1148636 13114709 := bbase (se 11 (by rfl) ⟨9605, by rfl⟩ : syracuseStep 13114709 = 19211) (by norm_num)
theorem B1940861 : Blo 1148636 1940861 := bbase (se 3 (by rfl) ⟨363911, by rfl⟩ : syracuseStep 1940861 = 727823) (by norm_num)
theorem B2760101 : Blo 1148636 2760101 := bbase (se 4 (by rfl) ⟨258759, by rfl⟩ : syracuseStep 2760101 = 517519) (by norm_num)
theorem B2956709 : Blo 1148636 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B2760149 : Blo 1148636 2760149 := bbase (se 7 (by rfl) ⟨32345, by rfl⟩ : syracuseStep 2760149 = 64691) (by norm_num)
theorem B4922869 : Blo 1148636 4922869 := bbase (se 5 (by rfl) ⟨230759, by rfl⟩ : syracuseStep 4922869 = 461519) (by norm_num)
theorem B1940989 : Blo 1148636 1940989 := bbase (se 3 (by rfl) ⟨363935, by rfl⟩ : syracuseStep 1940989 = 727871) (by norm_num)
theorem B4365845 : Blo 1148636 4365845 := bbase (se 6 (by rfl) ⟨102324, by rfl⟩ : syracuseStep 4365845 = 204649) (by norm_num)
theorem B1941077 : Blo 1148636 1941077 := bbase (se 8 (by rfl) ⟨11373, by rfl⟩ : syracuseStep 1941077 = 22747) (by norm_num)
theorem B2334349 : Blo 1148636 2334349 := bbase (se 3 (by rfl) ⟨437690, by rfl⟩ : syracuseStep 2334349 = 875381) (by norm_num)
theorem B1941205 : Blo 1148636 1941205 := bbase (se 7 (by rfl) ⟨22748, by rfl⟩ : syracuseStep 1941205 = 45497) (by norm_num)
theorem B2072309 : Blo 1148636 2072309 := bbase (se 5 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 2072309 = 194279) (by norm_num)
theorem B1941293 : Blo 1148636 1941293 := bbase (se 3 (by rfl) ⟨363992, by rfl⟩ : syracuseStep 1941293 = 727985) (by norm_num)
theorem B4366133 : Blo 1148636 4366133 := bbase (se 5 (by rfl) ⟨204662, by rfl⟩ : syracuseStep 4366133 = 409325) (by norm_num)
theorem B1941421 : Blo 1148636 1941421 := bbase (se 3 (by rfl) ⟨364016, by rfl⟩ : syracuseStep 1941421 = 728033) (by norm_num)
theorem B1941509 : Blo 1148636 1941509 := bbase (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) (by norm_num)
theorem B14000149 : Blo 1148636 14000149 := bbase (se 6 (by rfl) ⟨328128, by rfl⟩ : syracuseStep 14000149 = 656257) (by norm_num)
theorem B1941637 : Blo 1148636 1941637 := bbase (se 4 (by rfl) ⟨182028, by rfl⟩ : syracuseStep 1941637 = 364057) (by norm_num)
theorem B1941725 : Blo 1148636 1941725 := bbase (se 3 (by rfl) ⟨364073, by rfl⟩ : syracuseStep 1941725 = 728147) (by norm_num)
theorem B1843501 : Blo 1148636 1843501 := bbase (se 3 (by rfl) ⟨345656, by rfl⟩ : syracuseStep 1843501 = 691313) (by norm_num)
theorem B1941853 : Blo 1148636 1941853 := bbase (se 3 (by rfl) ⟨364097, by rfl⟩ : syracuseStep 1941853 = 728195) (by norm_num)
theorem B1941941 : Blo 1148636 1941941 := bbase (se 5 (by rfl) ⟨91028, by rfl⟩ : syracuseStep 1941941 = 182057) (by norm_num)
theorem B1942069 : Blo 1148636 1942069 := bbase (se 5 (by rfl) ⟨91034, by rfl⟩ : syracuseStep 1942069 = 182069) (by norm_num)
theorem B1942157 : Blo 1148636 1942157 := bbase (se 3 (by rfl) ⟨364154, by rfl⟩ : syracuseStep 1942157 = 728309) (by norm_num)
theorem B1843949 : Blo 1148636 1843949 := bbase (se 3 (by rfl) ⟨345740, by rfl⟩ : syracuseStep 1843949 = 691481) (by norm_num)
theorem B1942285 : Blo 1148636 1942285 := bbase (se 3 (by rfl) ⟨364178, by rfl⟩ : syracuseStep 1942285 = 728357) (by norm_num)
theorem B2761541 : Blo 1148636 2761541 := bbase (se 4 (by rfl) ⟨258894, by rfl⟩ : syracuseStep 2761541 = 517789) (by norm_num)
theorem B1942373 : Blo 1148636 1942373 := bbase (se 4 (by rfl) ⟨182097, by rfl⟩ : syracuseStep 1942373 = 364195) (by norm_num)
theorem B4367317 : Blo 1148636 4367317 := bbase (se 7 (by rfl) ⟨51179, by rfl⟩ : syracuseStep 4367317 = 102359) (by norm_num)
theorem B1942501 : Blo 1148636 1942501 := bbase (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) (by norm_num)
theorem B2761733 : Blo 1148636 2761733 := bbase (se 4 (by rfl) ⟨258912, by rfl⟩ : syracuseStep 2761733 = 517825) (by norm_num)
theorem B1942589 : Blo 1148636 1942589 := bbase (se 3 (by rfl) ⟨364235, by rfl⟩ : syracuseStep 1942589 = 728471) (by norm_num)
theorem B1942717 : Blo 1148636 1942717 := bbase (se 3 (by rfl) ⟨364259, by rfl⟩ : syracuseStep 1942717 = 728519) (by norm_num)
theorem B4367621 : Blo 1148636 4367621 := bbase (se 4 (by rfl) ⟨409464, by rfl⟩ : syracuseStep 4367621 = 818929) (by norm_num)
theorem B1942805 : Blo 1148636 1942805 := bbase (se 6 (by rfl) ⟨45534, by rfl⟩ : syracuseStep 1942805 = 91069) (by norm_num)
theorem B2336053 : Blo 1148636 2336053 := bbase (se 5 (by rfl) ⟨109502, by rfl⟩ : syracuseStep 2336053 = 219005) (by norm_num)
theorem B1942933 : Blo 1148636 1942933 := bbase (se 6 (by rfl) ⟨45537, by rfl⟩ : syracuseStep 1942933 = 91075) (by norm_num)
theorem B1943021 : Blo 1148636 1943021 := bbase (se 3 (by rfl) ⟨364316, by rfl⟩ : syracuseStep 1943021 = 728633) (by norm_num)
theorem B1943149 : Blo 1148636 1943149 := bbase (se 3 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 1943149 = 728681) (by norm_num)
theorem B1943237 : Blo 1148636 1943237 := bbase (se 4 (by rfl) ⟨182178, by rfl⟩ : syracuseStep 1943237 = 364357) (by norm_num)
theorem B1943365 : Blo 1148636 1943365 := bbase (se 4 (by rfl) ⟨182190, by rfl⟩ : syracuseStep 1943365 = 364381) (by norm_num)
theorem B1746773 : Blo 1148636 1746773 := bbase (se 9 (by rfl) ⟨5117, by rfl⟩ : syracuseStep 1746773 = 10235) (by norm_num)
theorem B2074501 : Blo 1148636 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B1943453 : Blo 1148636 1943453 := bbase (se 3 (by rfl) ⟨364397, by rfl⟩ : syracuseStep 1943453 = 728795) (by norm_num)
theorem B3876821 : Blo 1148636 3876821 := bbase (se 7 (by rfl) ⟨45431, by rfl⟩ : syracuseStep 3876821 = 90863) (by norm_num)
theorem B6989813 : Blo 1148636 6989813 := bbase (se 5 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 6989813 = 655295) (by norm_num)
theorem B3680261 : Blo 1148636 3680261 := bbase (se 4 (by rfl) ⟨345024, by rfl⟩ : syracuseStep 3680261 = 690049) (by norm_num)
theorem B1943581 : Blo 1148636 1943581 := bbase (se 3 (by rfl) ⟨364421, by rfl⟩ : syracuseStep 1943581 = 728843) (by norm_num)
theorem B1943669 : Blo 1148636 1943669 := bbase (se 5 (by rfl) ⟨91109, by rfl⟩ : syracuseStep 1943669 = 182219) (by norm_num)
theorem B1845461 : Blo 1148636 1845461 := bbase (se 7 (by rfl) ⟨21626, by rfl⟩ : syracuseStep 1845461 = 43253) (by norm_num)
theorem B1943797 : Blo 1148636 1943797 := bbase (se 5 (by rfl) ⟨91115, by rfl⟩ : syracuseStep 1943797 = 182231) (by norm_num)
theorem B1943885 : Blo 1148636 1943885 := bbase (se 3 (by rfl) ⟨364478, by rfl⟩ : syracuseStep 1943885 = 728957) (by norm_num)
theorem B1845589 : Blo 1148636 1845589 := bbase (se 10 (by rfl) ⟨2703, by rfl⟩ : syracuseStep 1845589 = 5407) (by norm_num)
theorem B3877253 : Blo 1148636 3877253 := bbase (se 4 (by rfl) ⟨363492, by rfl⟩ : syracuseStep 3877253 = 726985) (by norm_num)
theorem B1944013 : Blo 1148636 1944013 := bbase (se 3 (by rfl) ⟨364502, by rfl⟩ : syracuseStep 1944013 = 729005) (by norm_num)
theorem B1944101 : Blo 1148636 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B3156533 : Blo 1148636 3156533 := bbase (se 5 (by rfl) ⟨147962, by rfl⟩ : syracuseStep 3156533 = 295925) (by norm_num)
theorem B1944229 : Blo 1148636 1944229 := bbase (se 4 (by rfl) ⟨182271, by rfl⟩ : syracuseStep 1944229 = 364543) (by norm_num)
theorem B2075365 : Blo 1148636 2075365 := bbase (se 4 (by rfl) ⟨194565, by rfl⟩ : syracuseStep 2075365 = 389131) (by norm_num)
theorem B1944317 : Blo 1148636 1944317 := bbase (se 3 (by rfl) ⟨364559, by rfl⟩ : syracuseStep 1944317 = 729119) (by norm_num)
theorem B5253893 : Blo 1148636 5253893 := bbase (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) (by norm_num)
theorem B3877685 : Blo 1148636 3877685 := bbase (se 5 (by rfl) ⟨181766, by rfl⟩ : syracuseStep 3877685 = 363533) (by norm_num)
theorem B1944445 : Blo 1148636 1944445 := bbase (se 3 (by rfl) ⟨364583, by rfl⟩ : syracuseStep 1944445 = 729167) (by norm_num)
theorem B2763733 : Blo 1148636 2763733 := bbase (se 7 (by rfl) ⟨32387, by rfl⟩ : syracuseStep 2763733 = 64775) (by norm_num)
theorem B1944533 : Blo 1148636 1944533 := bbase (se 7 (by rfl) ⟨22787, by rfl⟩ : syracuseStep 1944533 = 45575) (by norm_num)
theorem B1944661 : Blo 1148636 1944661 := bbase (se 8 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 1944661 = 22789) (by norm_num)
theorem B1944749 : Blo 1148636 1944749 := bbase (se 3 (by rfl) ⟨364640, by rfl⟩ : syracuseStep 1944749 = 729281) (by norm_num)
theorem B3878117 : Blo 1148636 3878117 := bbase (se 4 (by rfl) ⟨363573, by rfl⟩ : syracuseStep 3878117 = 727147) (by norm_num)
theorem B2075885 : Blo 1148636 2075885 := bbase (se 3 (by rfl) ⟨389228, by rfl⟩ : syracuseStep 2075885 = 778457) (by norm_num)
theorem B3681541 : Blo 1148636 3681541 := bbase (se 4 (by rfl) ⟨345144, by rfl⟩ : syracuseStep 3681541 = 690289) (by norm_num)
theorem B1748245 : Blo 1148636 1748245 := bbase (se 6 (by rfl) ⟨40974, by rfl⟩ : syracuseStep 1748245 = 81949) (by norm_num)
theorem B1944877 : Blo 1148636 1944877 := bbase (se 3 (by rfl) ⟨364664, by rfl⟩ : syracuseStep 1944877 = 729329) (by norm_num)
theorem B4369733 : Blo 1148636 4369733 := bbase (se 4 (by rfl) ⟨409662, by rfl⟩ : syracuseStep 4369733 = 819325) (by norm_num)
theorem B1944965 : Blo 1148636 1944965 := bbase (se 4 (by rfl) ⟨182340, by rfl⟩ : syracuseStep 1944965 = 364681) (by norm_num)
theorem B4664837 : Blo 1148636 4664837 := bbase (se 4 (by rfl) ⟨437328, by rfl⟩ : syracuseStep 4664837 = 874657) (by norm_num)
theorem B2764309 : Blo 1148636 2764309 := bbase (se 6 (by rfl) ⟨64788, by rfl⟩ : syracuseStep 2764309 = 129577) (by norm_num)
theorem B4370021 : Blo 1148636 4370021 := bbase (se 4 (by rfl) ⟨409689, by rfl⟩ : syracuseStep 4370021 = 819379) (by norm_num)
theorem B3878549 : Blo 1148636 3878549 := bbase (se 6 (by rfl) ⟨90903, by rfl⟩ : syracuseStep 3878549 = 181807) (by norm_num)
theorem B20983445 : Blo 1148636 20983445 := bbase (se 6 (by rfl) ⟨491799, by rfl⟩ : syracuseStep 20983445 = 983599) (by norm_num)
theorem B3550949 : Blo 1148636 3550949 := bbase (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) (by norm_num)
theorem B1453889 : Blo 1148636 1453889 := bbase (se 2 (by rfl) ⟨545208, by rfl⟩ : syracuseStep 1453889 = 1090417) (by norm_num)
theorem B2764637 : Blo 1148636 2764637 := bbase (se 3 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 2764637 = 1036739) (by norm_num)
theorem B1453945 : Blo 1148636 1453945 := bbase (se 2 (by rfl) ⟨545229, by rfl⟩ : syracuseStep 1453945 = 1090459) (by norm_num)
theorem B2764693 : Blo 1148636 2764693 := bbase (se 6 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 2764693 = 129595) (by norm_num)
theorem B1454041 : Blo 1148636 1454041 := bbase (se 2 (by rfl) ⟨545265, by rfl⟩ : syracuseStep 1454041 = 1090531) (by norm_num)
theorem B3878981 : Blo 1148636 3878981 := bbase (se 4 (by rfl) ⟨363654, by rfl⟩ : syracuseStep 3878981 = 727309) (by norm_num)
theorem B2764925 : Blo 1148636 2764925 := bbase (se 3 (by rfl) ⟨518423, by rfl⟩ : syracuseStep 2764925 = 1036847) (by norm_num)
theorem B1454213 : Blo 1148636 1454213 := bbase (se 4 (by rfl) ⟨136332, by rfl⟩ : syracuseStep 1454213 = 272665) (by norm_num)
theorem B1454269 : Blo 1148636 1454269 := bbase (se 3 (by rfl) ⟨272675, by rfl⟩ : syracuseStep 1454269 = 545351) (by norm_num)
theorem B1454365 : Blo 1148636 1454365 := bbase (se 3 (by rfl) ⟨272693, by rfl⟩ : syracuseStep 1454365 = 545387) (by norm_num)
theorem B2765117 : Blo 1148636 2765117 := bbase (se 3 (by rfl) ⟨518459, by rfl⟩ : syracuseStep 2765117 = 1036919) (by norm_num)
theorem B9318773 : Blo 1148636 9318773 := bbase (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) (by norm_num)
theorem B1749413 : Blo 1148636 1749413 := bbase (se 4 (by rfl) ⟨164007, by rfl⟩ : syracuseStep 1749413 = 328015) (by norm_num)
theorem B1454537 : Blo 1148636 1454537 := bbase (se 2 (by rfl) ⟨545451, by rfl⟩ : syracuseStep 1454537 = 1090903) (by norm_num)
theorem B8729045 : Blo 1148636 8729045 := bbase (se 7 (by rfl) ⟨102293, by rfl⟩ : syracuseStep 8729045 = 204587) (by norm_num)
theorem B3879413 : Blo 1148636 3879413 := bbase (se 5 (by rfl) ⟨181847, by rfl⟩ : syracuseStep 3879413 = 363695) (by norm_num)
theorem B1454593 : Blo 1148636 1454593 := bbase (se 2 (by rfl) ⟨545472, by rfl⟩ : syracuseStep 1454593 = 1090945) (by norm_num)
theorem B3682901 : Blo 1148636 3682901 := bbase (se 8 (by rfl) ⟨21579, by rfl⟩ : syracuseStep 3682901 = 43159) (by norm_num)
theorem B1454689 : Blo 1148636 1454689 := bbase (se 2 (by rfl) ⟨545508, by rfl⟩ : syracuseStep 1454689 = 1091017) (by norm_num)
theorem B3683029 : Blo 1148636 3683029 := bbase (se 7 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 3683029 = 86321) (by norm_num)
theorem B4371205 : Blo 1148636 4371205 := bbase (se 4 (by rfl) ⟨409800, by rfl⟩ : syracuseStep 4371205 = 819601) (by norm_num)
theorem B1454861 : Blo 1148636 1454861 := bbase (se 3 (by rfl) ⟨272786, by rfl⟩ : syracuseStep 1454861 = 545573) (by norm_num)
theorem B1454917 : Blo 1148636 1454917 := bbase (se 4 (by rfl) ⟨136398, by rfl⟩ : syracuseStep 1454917 = 272797) (by norm_num)
theorem B3879845 : Blo 1148636 3879845 := bbase (se 4 (by rfl) ⟨363735, by rfl⟩ : syracuseStep 3879845 = 727471) (by norm_num)
theorem B1455013 : Blo 1148636 1455013 := bbase (se 4 (by rfl) ⟨136407, by rfl⟩ : syracuseStep 1455013 = 272815) (by norm_num)
theorem B3683285 : Blo 1148636 3683285 := bbase (se 7 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 3683285 = 86327) (by norm_num)
theorem B4371509 : Blo 1148636 4371509 := bbase (se 5 (by rfl) ⟨204914, by rfl⟩ : syracuseStep 4371509 = 409829) (by norm_num)
theorem B1455185 : Blo 1148636 1455185 := bbase (se 2 (by rfl) ⟨545694, by rfl⟩ : syracuseStep 1455185 = 1091389) (by norm_num)
theorem B1455241 : Blo 1148636 1455241 := bbase (se 2 (by rfl) ⟨545715, by rfl⟩ : syracuseStep 1455241 = 1091431) (by norm_num)
theorem B1455337 : Blo 1148636 1455337 := bbase (se 2 (by rfl) ⟨545751, by rfl⟩ : syracuseStep 1455337 = 1091503) (by norm_num)
theorem B2766077 : Blo 1148636 2766077 := bbase (se 3 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 2766077 = 1037279) (by norm_num)
theorem B3880277 : Blo 1148636 3880277 := bbase (se 13 (by rfl) ⟨710, by rfl⟩ : syracuseStep 3880277 = 1421) (by norm_num)
theorem B29537621 : Blo 1148636 29537621 := bbase (se 13 (by rfl) ⟨5408, by rfl⟩ : syracuseStep 29537621 = 10817) (by norm_num)
theorem B1455509 : Blo 1148636 1455509 := bbase (se 6 (by rfl) ⟨34113, by rfl⟩ : syracuseStep 1455509 = 68227) (by norm_num)
theorem B1455565 : Blo 1148636 1455565 := bbase (se 3 (by rfl) ⟨272918, by rfl⟩ : syracuseStep 1455565 = 545837) (by norm_num)
theorem B1553941 : Blo 1148636 1553941 := bbase (se 6 (by rfl) ⟨36420, by rfl⟩ : syracuseStep 1553941 = 72841) (by norm_num)
theorem B1455661 : Blo 1148636 1455661 := bbase (se 3 (by rfl) ⟨272936, by rfl⟩ : syracuseStep 1455661 = 545873) (by norm_num)
theorem B4732613 : Blo 1148636 4732613 := bbase (se 4 (by rfl) ⟨443682, by rfl⟩ : syracuseStep 4732613 = 887365) (by norm_num)
theorem B1455833 : Blo 1148636 1455833 := bbase (se 2 (by rfl) ⟨545937, by rfl⟩ : syracuseStep 1455833 = 1091875) (by norm_num)
theorem B3880709 : Blo 1148636 3880709 := bbase (se 4 (by rfl) ⟨363816, by rfl⟩ : syracuseStep 3880709 = 727633) (by norm_num)
theorem B1455889 : Blo 1148636 1455889 := bbase (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) (by norm_num)
theorem B1455985 : Blo 1148636 1455985 := bbase (se 2 (by rfl) ⟨545994, by rfl⟩ : syracuseStep 1455985 = 1091989) (by norm_num)
theorem B1292233 : Blo 1148636 1292233 := bbase (se 2 (by rfl) ⟨484587, by rfl⟩ : syracuseStep 1292233 = 969175) (by norm_num)
theorem B1292269 : Blo 1148636 1292269 := bbase (se 3 (by rfl) ⟨242300, by rfl⟩ : syracuseStep 1292269 = 484601) (by norm_num)
theorem B1292305 : Blo 1148636 1292305 := bbase (se 2 (by rfl) ⟨484614, by rfl⟩ : syracuseStep 1292305 = 969229) (by norm_num)
theorem B1456157 : Blo 1148636 1456157 := bbase (se 3 (by rfl) ⟨273029, by rfl⟩ : syracuseStep 1456157 = 546059) (by norm_num)
theorem B1292341 : Blo 1148636 1292341 := bbase (se 5 (by rfl) ⟨60578, by rfl⟩ : syracuseStep 1292341 = 121157) (by norm_num)
theorem B1456213 : Blo 1148636 1456213 := bbase (se 8 (by rfl) ⟨8532, by rfl⟩ : syracuseStep 1456213 = 17065) (by norm_num)
theorem B1292377 : Blo 1148636 1292377 := bbase (se 2 (by rfl) ⟨484641, by rfl⟩ : syracuseStep 1292377 = 969283) (by norm_num)
theorem B4143221 : Blo 1148636 4143221 := bbase (se 5 (by rfl) ⟨194213, by rfl⟩ : syracuseStep 4143221 = 388427) (by norm_num)
theorem B1226873 : Blo 1148636 1226873 := bbase (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) (by norm_num)
theorem B1292413 : Blo 1148636 1292413 := bbase (se 3 (by rfl) ⟨242327, by rfl⟩ : syracuseStep 1292413 = 484655) (by norm_num)
theorem B1292449 : Blo 1148636 1292449 := bbase (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) (by norm_num)
theorem B3881141 : Blo 1148636 3881141 := bbase (se 5 (by rfl) ⟨181928, by rfl⟩ : syracuseStep 3881141 = 363857) (by norm_num)
theorem B1456309 : Blo 1148636 1456309 := bbase (se 5 (by rfl) ⟨68264, by rfl⟩ : syracuseStep 1456309 = 136529) (by norm_num)
theorem B1292485 : Blo 1148636 1292485 := bbase (se 4 (by rfl) ⟨121170, by rfl⟩ : syracuseStep 1292485 = 242341) (by norm_num)
theorem B1751237 : Blo 1148636 1751237 := bbase (se 4 (by rfl) ⟨164178, by rfl⟩ : syracuseStep 1751237 = 328357) (by norm_num)
theorem B1292521 : Blo 1148636 1292521 := bbase (se 2 (by rfl) ⟨484695, by rfl⟩ : syracuseStep 1292521 = 969391) (by norm_num)
theorem B4143349 : Blo 1148636 4143349 := bbase (se 5 (by rfl) ⟨194219, by rfl⟩ : syracuseStep 4143349 = 388439) (by norm_num)
theorem B1292557 : Blo 1148636 1292557 := bbase (se 3 (by rfl) ⟨242354, by rfl⟩ : syracuseStep 1292557 = 484709) (by norm_num)
theorem B1292593 : Blo 1148636 1292593 := bbase (se 2 (by rfl) ⟨484722, by rfl⟩ : syracuseStep 1292593 = 969445) (by norm_num)
theorem B5257541 : Blo 1148636 5257541 := bbase (se 4 (by rfl) ⟨492894, by rfl⟩ : syracuseStep 5257541 = 985789) (by norm_num)
theorem B1292629 : Blo 1148636 1292629 := bbase (se 10 (by rfl) ⟨1893, by rfl⟩ : syracuseStep 1292629 = 3787) (by norm_num)
theorem B1456481 : Blo 1148636 1456481 := bbase (se 2 (by rfl) ⟨546180, by rfl⟩ : syracuseStep 1456481 = 1092361) (by norm_num)
theorem B1292665 : Blo 1148636 1292665 := bbase (se 2 (by rfl) ⟨484749, by rfl⟩ : syracuseStep 1292665 = 969499) (by norm_num)
theorem B1456537 : Blo 1148636 1456537 := bbase (se 2 (by rfl) ⟨546201, by rfl⟩ : syracuseStep 1456537 = 1092403) (by norm_num)
theorem B1292701 : Blo 1148636 1292701 := bbase (se 3 (by rfl) ⟨242381, by rfl⟩ : syracuseStep 1292701 = 484763) (by norm_num)
theorem B1292737 : Blo 1148636 1292737 := bbase (se 2 (by rfl) ⟨484776, by rfl⟩ : syracuseStep 1292737 = 969553) (by norm_num)
theorem B1292773 : Blo 1148636 1292773 := bbase (se 4 (by rfl) ⟨121197, by rfl⟩ : syracuseStep 1292773 = 242395) (by norm_num)
theorem B1456633 : Blo 1148636 1456633 := bbase (se 2 (by rfl) ⟨546237, by rfl⟩ : syracuseStep 1456633 = 1092475) (by norm_num)
theorem B1292809 : Blo 1148636 1292809 := bbase (se 2 (by rfl) ⟨484803, by rfl⟩ : syracuseStep 1292809 = 969607) (by norm_num)
theorem B1292845 : Blo 1148636 1292845 := bbase (se 3 (by rfl) ⟨242408, by rfl⟩ : syracuseStep 1292845 = 484817) (by norm_num)
theorem B1227317 : Blo 1148636 1227317 := bbase (se 5 (by rfl) ⟨57530, by rfl⟩ : syracuseStep 1227317 = 115061) (by norm_num)
theorem B1292881 : Blo 1148636 1292881 := bbase (se 2 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 1292881 = 969661) (by norm_num)
theorem B3881573 : Blo 1148636 3881573 := bbase (se 4 (by rfl) ⟨363897, by rfl⟩ : syracuseStep 3881573 = 727795) (by norm_num)
theorem B1292917 : Blo 1148636 1292917 := bbase (se 5 (by rfl) ⟨60605, by rfl⟩ : syracuseStep 1292917 = 121211) (by norm_num)
theorem B1292953 : Blo 1148636 1292953 := bbase (se 2 (by rfl) ⟨484857, by rfl⟩ : syracuseStep 1292953 = 969715) (by norm_num)
theorem B1456805 : Blo 1148636 1456805 := bbase (se 4 (by rfl) ⟨136575, by rfl⟩ : syracuseStep 1456805 = 273151) (by norm_num)
theorem B1751717 : Blo 1148636 1751717 := bbase (se 4 (by rfl) ⟨164223, by rfl⟩ : syracuseStep 1751717 = 328447) (by norm_num)
theorem B1292989 : Blo 1148636 1292989 := bbase (se 3 (by rfl) ⟨242435, by rfl⟩ : syracuseStep 1292989 = 484871) (by norm_num)
theorem B1456861 : Blo 1148636 1456861 := bbase (se 3 (by rfl) ⟨273161, by rfl⟩ : syracuseStep 1456861 = 546323) (by norm_num)
theorem B1293025 : Blo 1148636 1293025 := bbase (se 2 (by rfl) ⟨484884, by rfl⟩ : syracuseStep 1293025 = 969769) (by norm_num)
theorem B1293061 : Blo 1148636 1293061 := bbase (se 4 (by rfl) ⟨121224, by rfl⟩ : syracuseStep 1293061 = 242449) (by norm_num)
theorem B1555205 : Blo 1148636 1555205 := bbase (se 4 (by rfl) ⟨145800, by rfl⟩ : syracuseStep 1555205 = 291601) (by norm_num)
theorem B1293097 : Blo 1148636 1293097 := bbase (se 2 (by rfl) ⟨484911, by rfl⟩ : syracuseStep 1293097 = 969823) (by norm_num)
theorem B1227565 : Blo 1148636 1227565 := bbase (se 3 (by rfl) ⟨230168, by rfl⟩ : syracuseStep 1227565 = 460337) (by norm_num)
theorem B1456957 : Blo 1148636 1456957 := bbase (se 3 (by rfl) ⟨273179, by rfl⟩ : syracuseStep 1456957 = 546359) (by norm_num)
theorem B1293133 : Blo 1148636 1293133 := bbase (se 3 (by rfl) ⟨242462, by rfl⟩ : syracuseStep 1293133 = 484925) (by norm_num)
theorem B1293169 : Blo 1148636 1293169 := bbase (se 2 (by rfl) ⟨484938, by rfl⟩ : syracuseStep 1293169 = 969877) (by norm_num)
theorem B1751941 : Blo 1148636 1751941 := bbase (se 4 (by rfl) ⟨164244, by rfl⟩ : syracuseStep 1751941 = 328489) (by norm_num)
theorem B1293205 : Blo 1148636 1293205 := bbase (se 6 (by rfl) ⟨30309, by rfl⟩ : syracuseStep 1293205 = 60619) (by norm_num)
theorem B1293241 : Blo 1148636 1293241 := bbase (se 2 (by rfl) ⟨484965, by rfl⟩ : syracuseStep 1293241 = 969931) (by norm_num)
theorem B1293277 : Blo 1148636 1293277 := bbase (se 3 (by rfl) ⟨242489, by rfl⟩ : syracuseStep 1293277 = 484979) (by norm_num)
theorem B1457129 : Blo 1148636 1457129 := bbase (se 2 (by rfl) ⟨546423, by rfl⟩ : syracuseStep 1457129 = 1092847) (by norm_num)
theorem B1293313 : Blo 1148636 1293313 := bbase (se 2 (by rfl) ⟨484992, by rfl⟩ : syracuseStep 1293313 = 969985) (by norm_num)
theorem B3882005 : Blo 1148636 3882005 := bbase (se 6 (by rfl) ⟨90984, by rfl⟩ : syracuseStep 3882005 = 181969) (by norm_num)
theorem B1457185 : Blo 1148636 1457185 := bbase (se 2 (by rfl) ⟨546444, by rfl⟩ : syracuseStep 1457185 = 1092889) (by norm_num)
theorem B1293349 : Blo 1148636 1293349 := bbase (se 4 (by rfl) ⟨121251, by rfl⟩ : syracuseStep 1293349 = 242503) (by norm_num)
theorem B1293385 : Blo 1148636 1293385 := bbase (se 2 (by rfl) ⟨485019, by rfl⟩ : syracuseStep 1293385 = 970039) (by norm_num)
theorem B1293421 : Blo 1148636 1293421 := bbase (se 3 (by rfl) ⟨242516, by rfl⟩ : syracuseStep 1293421 = 485033) (by norm_num)
theorem B4373621 : Blo 1148636 4373621 := bbase (se 5 (by rfl) ⟨205013, by rfl⟩ : syracuseStep 4373621 = 410027) (by norm_num)
theorem B1457281 : Blo 1148636 1457281 := bbase (se 2 (by rfl) ⟨546480, by rfl⟩ : syracuseStep 1457281 = 1092961) (by norm_num)
theorem B1293457 : Blo 1148636 1293457 := bbase (se 2 (by rfl) ⟨485046, by rfl⟩ : syracuseStep 1293457 = 970093) (by norm_num)
theorem B1293493 : Blo 1148636 1293493 := bbase (se 5 (by rfl) ⟨60632, by rfl⟩ : syracuseStep 1293493 = 121265) (by norm_num)
theorem B1293529 : Blo 1148636 1293529 := bbase (se 2 (by rfl) ⟨485073, by rfl⟩ : syracuseStep 1293529 = 970147) (by norm_num)
theorem B1227997 : Blo 1148636 1227997 := bbase (se 3 (by rfl) ⟨230249, by rfl⟩ : syracuseStep 1227997 = 460499) (by norm_num)
theorem B1293565 : Blo 1148636 1293565 := bbase (se 3 (by rfl) ⟨242543, by rfl⟩ : syracuseStep 1293565 = 485087) (by norm_num)
theorem B1293601 : Blo 1148636 1293601 := bbase (se 2 (by rfl) ⟨485100, by rfl⟩ : syracuseStep 1293601 = 970201) (by norm_num)
theorem B1228069 : Blo 1148636 1228069 := bbase (se 4 (by rfl) ⟨115131, by rfl⟩ : syracuseStep 1228069 = 230263) (by norm_num)
theorem B1457453 : Blo 1148636 1457453 := bbase (se 3 (by rfl) ⟨273272, by rfl⟩ : syracuseStep 1457453 = 546545) (by norm_num)
theorem B1293637 : Blo 1148636 1293637 := bbase (se 4 (by rfl) ⟨121278, by rfl⟩ : syracuseStep 1293637 = 242557) (by norm_num)
theorem B5815637 : Blo 1148636 5815637 := bbase (se 11 (by rfl) ⟨4259, by rfl⟩ : syracuseStep 5815637 = 8519) (by norm_num)
theorem B3685733 : Blo 1148636 3685733 := bbase (se 4 (by rfl) ⟨345537, by rfl⟩ : syracuseStep 3685733 = 691075) (by norm_num)
theorem B1457509 : Blo 1148636 1457509 := bbase (se 4 (by rfl) ⟨136641, by rfl⟩ : syracuseStep 1457509 = 273283) (by norm_num)
theorem B1293673 : Blo 1148636 1293673 := bbase (se 2 (by rfl) ⟨485127, by rfl⟩ : syracuseStep 1293673 = 970255) (by norm_num)
theorem B1293709 : Blo 1148636 1293709 := bbase (se 3 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 1293709 = 485141) (by norm_num)
theorem B4373909 : Blo 1148636 4373909 := bbase (se 6 (by rfl) ⟨102513, by rfl⟩ : syracuseStep 4373909 = 205027) (by norm_num)
theorem B1293745 : Blo 1148636 1293745 := bbase (se 2 (by rfl) ⟨485154, by rfl⟩ : syracuseStep 1293745 = 970309) (by norm_num)
theorem B3882437 : Blo 1148636 3882437 := bbase (se 4 (by rfl) ⟨363978, by rfl⟩ : syracuseStep 3882437 = 727957) (by norm_num)
theorem B1457605 : Blo 1148636 1457605 := bbase (se 4 (by rfl) ⟨136650, by rfl⟩ : syracuseStep 1457605 = 273301) (by norm_num)
theorem B1293781 : Blo 1148636 1293781 := bbase (se 7 (by rfl) ⟨15161, by rfl⟩ : syracuseStep 1293781 = 30323) (by norm_num)
theorem B1555957 : Blo 1148636 1555957 := bbase (se 5 (by rfl) ⟨72935, by rfl⟩ : syracuseStep 1555957 = 145871) (by norm_num)
theorem B1293817 : Blo 1148636 1293817 := bbase (se 2 (by rfl) ⟨485181, by rfl⟩ : syracuseStep 1293817 = 970363) (by norm_num)
theorem B1293853 : Blo 1148636 1293853 := bbase (se 3 (by rfl) ⟨242597, by rfl⟩ : syracuseStep 1293853 = 485195) (by norm_num)
theorem B1293889 : Blo 1148636 1293889 := bbase (se 2 (by rfl) ⟨485208, by rfl⟩ : syracuseStep 1293889 = 970417) (by norm_num)
theorem B1293925 : Blo 1148636 1293925 := bbase (se 4 (by rfl) ⟨121305, by rfl⟩ : syracuseStep 1293925 = 242611) (by norm_num)
theorem B1457777 : Blo 1148636 1457777 := bbase (se 2 (by rfl) ⟨546666, by rfl⟩ : syracuseStep 1457777 = 1093333) (by norm_num)
theorem B1293961 : Blo 1148636 1293961 := bbase (se 2 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 1293961 = 970471) (by norm_num)
theorem B1228441 : Blo 1148636 1228441 := bbase (se 2 (by rfl) ⟨460665, by rfl⟩ : syracuseStep 1228441 = 921331) (by norm_num)
theorem B1457833 : Blo 1148636 1457833 := bbase (se 2 (by rfl) ⟨546687, by rfl⟩ : syracuseStep 1457833 = 1093375) (by norm_num)
theorem B1293997 : Blo 1148636 1293997 := bbase (se 3 (by rfl) ⟨242624, by rfl⟩ : syracuseStep 1293997 = 485249) (by norm_num)
theorem B1294033 : Blo 1148636 1294033 := bbase (se 2 (by rfl) ⟨485262, by rfl⟩ : syracuseStep 1294033 = 970525) (by norm_num)
theorem B1294069 : Blo 1148636 1294069 := bbase (se 5 (by rfl) ⟨60659, by rfl⟩ : syracuseStep 1294069 = 121319) (by norm_num)
theorem B1457929 : Blo 1148636 1457929 := bbase (se 2 (by rfl) ⟨546723, by rfl⟩ : syracuseStep 1457929 = 1093447) (by norm_num)
theorem B1294105 : Blo 1148636 1294105 := bbase (se 2 (by rfl) ⟨485289, by rfl⟩ : syracuseStep 1294105 = 970579) (by norm_num)
theorem B2309917 : Blo 1148636 2309917 := bbase (se 3 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 2309917 = 866219) (by norm_num)
theorem B1294141 : Blo 1148636 1294141 := bbase (se 3 (by rfl) ⟨242651, by rfl⟩ : syracuseStep 1294141 = 485303) (by norm_num)
theorem B1294177 : Blo 1148636 1294177 := bbase (se 2 (by rfl) ⟨485316, by rfl⟩ : syracuseStep 1294177 = 970633) (by norm_num)
theorem B3882869 : Blo 1148636 3882869 := bbase (se 5 (by rfl) ⟨182009, by rfl⟩ : syracuseStep 3882869 = 364019) (by norm_num)
theorem B1294213 : Blo 1148636 1294213 := bbase (se 4 (by rfl) ⟨121332, by rfl⟩ : syracuseStep 1294213 = 242665) (by norm_num)
theorem B1294249 : Blo 1148636 1294249 := bbase (se 2 (by rfl) ⟨485343, by rfl⟩ : syracuseStep 1294249 = 970687) (by norm_num)
theorem B1458101 : Blo 1148636 1458101 := bbase (se 5 (by rfl) ⟨68348, by rfl⟩ : syracuseStep 1458101 = 136697) (by norm_num)
theorem B1294285 : Blo 1148636 1294285 := bbase (se 3 (by rfl) ⟨242678, by rfl⟩ : syracuseStep 1294285 = 485357) (by norm_num)
theorem B2768845 : Blo 1148636 2768845 := bbase (se 3 (by rfl) ⟨519158, by rfl⟩ : syracuseStep 2768845 = 1038317) (by norm_num)
theorem B1458157 : Blo 1148636 1458157 := bbase (se 3 (by rfl) ⟨273404, by rfl⟩ : syracuseStep 1458157 = 546809) (by norm_num)
theorem B1294321 : Blo 1148636 1294321 := bbase (se 2 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 1294321 = 970741) (by norm_num)
theorem B1228817 : Blo 1148636 1228817 := bbase (se 2 (by rfl) ⟨460806, by rfl⟩ : syracuseStep 1228817 = 921613) (by norm_num)
theorem B1294357 : Blo 1148636 1294357 := bbase (se 6 (by rfl) ⟨30336, by rfl⟩ : syracuseStep 1294357 = 60673) (by norm_num)
theorem B11190325 : Blo 1148636 11190325 := bbase (se 5 (by rfl) ⟨524546, by rfl⟩ : syracuseStep 11190325 = 1049093) (by norm_num)
theorem B1294393 : Blo 1148636 1294393 := bbase (se 2 (by rfl) ⟨485397, by rfl⟩ : syracuseStep 1294393 = 970795) (by norm_num)
theorem B1458253 : Blo 1148636 1458253 := bbase (se 3 (by rfl) ⟨273422, by rfl⟩ : syracuseStep 1458253 = 546845) (by norm_num)
theorem B1228889 : Blo 1148636 1228889 := bbase (se 2 (by rfl) ⟨460833, by rfl⟩ : syracuseStep 1228889 = 921667) (by norm_num)
theorem B1294429 : Blo 1148636 1294429 := bbase (se 3 (by rfl) ⟨242705, by rfl⟩ : syracuseStep 1294429 = 485411) (by norm_num)
theorem B1294465 : Blo 1148636 1294465 := bbase (se 2 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 1294465 = 970849) (by norm_num)
theorem B1294501 : Blo 1148636 1294501 := bbase (se 4 (by rfl) ⟨121359, by rfl⟩ : syracuseStep 1294501 = 242719) (by norm_num)
theorem B1294537 : Blo 1148636 1294537 := bbase (se 2 (by rfl) ⟨485451, by rfl⟩ : syracuseStep 1294537 = 970903) (by norm_num)
theorem B5521621 : Blo 1148636 5521621 := bbase (se 7 (by rfl) ⟨64706, by rfl⟩ : syracuseStep 5521621 = 129413) (by norm_num)
theorem B1294573 : Blo 1148636 1294573 := bbase (se 3 (by rfl) ⟨242732, by rfl⟩ : syracuseStep 1294573 = 485465) (by norm_num)
theorem B1458425 : Blo 1148636 1458425 := bbase (se 2 (by rfl) ⟨546909, by rfl⟩ : syracuseStep 1458425 = 1093819) (by norm_num)
theorem B4145413 : Blo 1148636 4145413 := bbase (se 4 (by rfl) ⟨388632, by rfl⟩ : syracuseStep 4145413 = 777265) (by norm_num)
theorem B1294609 : Blo 1148636 1294609 := bbase (se 2 (by rfl) ⟨485478, by rfl⟩ : syracuseStep 1294609 = 970957) (by norm_num)
theorem B1229077 : Blo 1148636 1229077 := bbase (se 6 (by rfl) ⟨28806, by rfl⟩ : syracuseStep 1229077 = 57613) (by norm_num)
theorem B3883301 : Blo 1148636 3883301 := bbase (se 4 (by rfl) ⟨364059, by rfl⟩ : syracuseStep 3883301 = 728119) (by norm_num)
theorem B1458481 : Blo 1148636 1458481 := bbase (se 2 (by rfl) ⟨546930, by rfl⟩ : syracuseStep 1458481 = 1093861) (by norm_num)
theorem B1294645 : Blo 1148636 1294645 := bbase (se 5 (by rfl) ⟨60686, by rfl⟩ : syracuseStep 1294645 = 121373) (by norm_num)
theorem B2769221 : Blo 1148636 2769221 := bbase (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) (by norm_num)
theorem B1294681 : Blo 1148636 1294681 := bbase (se 2 (by rfl) ⟨485505, by rfl⟩ : syracuseStep 1294681 = 971011) (by norm_num)
theorem B1294717 : Blo 1148636 1294717 := bbase (se 3 (by rfl) ⟨242759, by rfl⟩ : syracuseStep 1294717 = 485519) (by norm_num)
theorem B1458577 : Blo 1148636 1458577 := bbase (se 2 (by rfl) ⟨546966, by rfl⟩ : syracuseStep 1458577 = 1093933) (by norm_num)
theorem B1294753 : Blo 1148636 1294753 := bbase (se 2 (by rfl) ⟨485532, by rfl⟩ : syracuseStep 1294753 = 971065) (by norm_num)
theorem B1294789 : Blo 1148636 1294789 := bbase (se 4 (by rfl) ⟨121386, by rfl⟩ : syracuseStep 1294789 = 242773) (by norm_num)
theorem B1229261 : Blo 1148636 1229261 := bbase (se 3 (by rfl) ⟨230486, by rfl⟩ : syracuseStep 1229261 = 460973) (by norm_num)
theorem B1294825 : Blo 1148636 1294825 := bbase (se 2 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 1294825 = 971119) (by norm_num)
theorem B1294861 : Blo 1148636 1294861 := bbase (se 3 (by rfl) ⟨242786, by rfl⟩ : syracuseStep 1294861 = 485573) (by norm_num)
theorem B1294897 : Blo 1148636 1294897 := bbase (se 2 (by rfl) ⟨485586, by rfl⟩ : syracuseStep 1294897 = 971173) (by norm_num)
theorem B4375093 : Blo 1148636 4375093 := bbase (se 5 (by rfl) ⟨205082, by rfl⟩ : syracuseStep 4375093 = 410165) (by norm_num)
theorem B1458749 : Blo 1148636 1458749 := bbase (se 3 (by rfl) ⟨273515, by rfl⟩ : syracuseStep 1458749 = 547031) (by norm_num)
theorem B1294933 : Blo 1148636 1294933 := bbase (se 8 (by rfl) ⟨7587, by rfl⟩ : syracuseStep 1294933 = 15175) (by norm_num)
theorem B5816933 : Blo 1148636 5816933 := bbase (se 4 (by rfl) ⟨545337, by rfl⟩ : syracuseStep 5816933 = 1090675) (by norm_num)
theorem B1458805 : Blo 1148636 1458805 := bbase (se 5 (by rfl) ⟨68381, by rfl⟩ : syracuseStep 1458805 = 136763) (by norm_num)
theorem B1294969 : Blo 1148636 1294969 := bbase (se 2 (by rfl) ⟨485613, by rfl⟩ : syracuseStep 1294969 = 971227) (by norm_num)
theorem B1295005 : Blo 1148636 1295005 := bbase (se 3 (by rfl) ⟨242813, by rfl⟩ : syracuseStep 1295005 = 485627) (by norm_num)
theorem B3687077 : Blo 1148636 3687077 := bbase (se 4 (by rfl) ⟨345663, by rfl⟩ : syracuseStep 3687077 = 691327) (by norm_num)
theorem B9814709 : Blo 1148636 9814709 := bbase (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) (by norm_num)
theorem B1295041 : Blo 1148636 1295041 := bbase (se 2 (by rfl) ⟨485640, by rfl⟩ : syracuseStep 1295041 = 971281) (by norm_num)
theorem B3883733 : Blo 1148636 3883733 := bbase (se 7 (by rfl) ⟨45512, by rfl⟩ : syracuseStep 3883733 = 91025) (by norm_num)
theorem B1295077 : Blo 1148636 1295077 := bbase (se 4 (by rfl) ⟨121413, by rfl⟩ : syracuseStep 1295077 = 242827) (by norm_num)
theorem B1295113 : Blo 1148636 1295113 := bbase (se 2 (by rfl) ⟨485667, by rfl⟩ : syracuseStep 1295113 = 971335) (by norm_num)
theorem B1295149 : Blo 1148636 1295149 := bbase (se 3 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 1295149 = 485681) (by norm_num)
theorem B1295185 : Blo 1148636 1295185 := bbase (se 2 (by rfl) ⟨485694, by rfl⟩ : syracuseStep 1295185 = 971389) (by norm_num)
theorem B4375397 : Blo 1148636 4375397 := bbase (se 4 (by rfl) ⟨410193, by rfl⟩ : syracuseStep 4375397 = 820387) (by norm_num)
theorem B1295221 : Blo 1148636 1295221 := bbase (se 5 (by rfl) ⟨60713, by rfl⟩ : syracuseStep 1295221 = 121427) (by norm_num)
theorem B1295257 : Blo 1148636 1295257 := bbase (se 2 (by rfl) ⟨485721, by rfl⟩ : syracuseStep 1295257 = 971443) (by norm_num)
theorem B1295293 : Blo 1148636 1295293 := bbase (se 3 (by rfl) ⟨242867, by rfl⟩ : syracuseStep 1295293 = 485735) (by norm_num)
theorem B1262557 : Blo 1148636 1262557 := bbase (se 3 (by rfl) ⟨236729, by rfl⟩ : syracuseStep 1262557 = 473459) (by norm_num)
theorem B1295329 : Blo 1148636 1295329 := bbase (se 2 (by rfl) ⟨485748, by rfl⟩ : syracuseStep 1295329 = 971497) (by norm_num)
theorem B1295365 : Blo 1148636 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B1295401 : Blo 1148636 1295401 := bbase (se 2 (by rfl) ⟨485775, by rfl⟩ : syracuseStep 1295401 = 971551) (by norm_num)
theorem B1295437 : Blo 1148636 1295437 := bbase (se 3 (by rfl) ⟨242894, by rfl⟩ : syracuseStep 1295437 = 485789) (by norm_num)
theorem B1295473 : Blo 1148636 1295473 := bbase (se 2 (by rfl) ⟨485802, by rfl⟩ : syracuseStep 1295473 = 971605) (by norm_num)
theorem B3884165 : Blo 1148636 3884165 := bbase (se 4 (by rfl) ⟨364140, by rfl⟩ : syracuseStep 3884165 = 728281) (by norm_num)
theorem B1295509 : Blo 1148636 1295509 := bbase (se 6 (by rfl) ⟨30363, by rfl⟩ : syracuseStep 1295509 = 60727) (by norm_num)
theorem B1295545 : Blo 1148636 1295545 := bbase (se 2 (by rfl) ⟨485829, by rfl⟩ : syracuseStep 1295545 = 971659) (by norm_num)
theorem B1230013 : Blo 1148636 1230013 := bbase (se 3 (by rfl) ⟨230627, by rfl⟩ : syracuseStep 1230013 = 461255) (by norm_num)
theorem B1295581 : Blo 1148636 1295581 := bbase (se 3 (by rfl) ⟨242921, by rfl⟩ : syracuseStep 1295581 = 485843) (by norm_num)
theorem B1295617 : Blo 1148636 1295617 := bbase (se 2 (by rfl) ⟨485856, by rfl⟩ : syracuseStep 1295617 = 971713) (by norm_num)
theorem B1230085 : Blo 1148636 1230085 := bbase (se 4 (by rfl) ⟨115320, by rfl⟩ : syracuseStep 1230085 = 230641) (by norm_num)
theorem B1295653 : Blo 1148636 1295653 := bbase (se 4 (by rfl) ⟨121467, by rfl⟩ : syracuseStep 1295653 = 242935) (by norm_num)
theorem B1295689 : Blo 1148636 1295689 := bbase (se 2 (by rfl) ⟨485883, by rfl⟩ : syracuseStep 1295689 = 971767) (by norm_num)
theorem B1295725 : Blo 1148636 1295725 := bbase (se 3 (by rfl) ⟨242948, by rfl⟩ : syracuseStep 1295725 = 485897) (by norm_num)
theorem B1295761 : Blo 1148636 1295761 := bbase (se 2 (by rfl) ⟨485910, by rfl⟩ : syracuseStep 1295761 = 971821) (by norm_num)
theorem B1295797 : Blo 1148636 1295797 := bbase (se 5 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 1295797 = 121481) (by norm_num)
theorem B1230265 : Blo 1148636 1230265 := bbase (se 2 (by rfl) ⟨461349, by rfl⟩ : syracuseStep 1230265 = 922699) (by norm_num)
theorem B1295833 : Blo 1148636 1295833 := bbase (se 2 (by rfl) ⟨485937, by rfl⟩ : syracuseStep 1295833 = 971875) (by norm_num)
theorem B1295869 : Blo 1148636 1295869 := bbase (se 3 (by rfl) ⟨242975, by rfl⟩ : syracuseStep 1295869 = 485951) (by norm_num)
theorem B2180621 : Blo 1148636 2180621 := bbase (se 3 (by rfl) ⟨408866, by rfl⟩ : syracuseStep 2180621 = 817733) (by norm_num)
theorem B1295905 : Blo 1148636 1295905 := bbase (se 2 (by rfl) ⟨485964, by rfl⟩ : syracuseStep 1295905 = 971929) (by norm_num)
theorem B3884597 : Blo 1148636 3884597 := bbase (se 5 (by rfl) ⟨182090, by rfl⟩ : syracuseStep 3884597 = 364181) (by norm_num)
theorem B1295941 : Blo 1148636 1295941 := bbase (se 4 (by rfl) ⟨121494, by rfl⟩ : syracuseStep 1295941 = 242989) (by norm_num)
theorem B1295977 : Blo 1148636 1295977 := bbase (se 2 (by rfl) ⟨485991, by rfl⟩ : syracuseStep 1295977 = 971983) (by norm_num)
theorem B1296013 : Blo 1148636 1296013 := bbase (se 3 (by rfl) ⟨243002, by rfl⟩ : syracuseStep 1296013 = 486005) (by norm_num)
theorem B2180773 : Blo 1148636 2180773 := bbase (se 4 (by rfl) ⟨204447, by rfl⟩ : syracuseStep 2180773 = 408895) (by norm_num)
theorem B1296049 : Blo 1148636 1296049 := bbase (se 2 (by rfl) ⟨486018, by rfl⟩ : syracuseStep 1296049 = 972037) (by norm_num)
theorem B1296085 : Blo 1148636 1296085 := bbase (se 7 (by rfl) ⟨15188, by rfl⟩ : syracuseStep 1296085 = 30377) (by norm_num)
theorem B8406773 : Blo 1148636 8406773 := bbase (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) (by norm_num)
theorem B1296121 : Blo 1148636 1296121 := bbase (se 2 (by rfl) ⟨486045, by rfl⟩ : syracuseStep 1296121 = 972091) (by norm_num)
theorem B1296157 : Blo 1148636 1296157 := bbase (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) (by norm_num)
theorem B1296193 : Blo 1148636 1296193 := bbase (se 2 (by rfl) ⟨486072, by rfl⟩ : syracuseStep 1296193 = 972145) (by norm_num)
theorem B1296229 : Blo 1148636 1296229 := bbase (se 4 (by rfl) ⟨121521, by rfl⟩ : syracuseStep 1296229 = 243043) (by norm_num)
theorem B5818229 : Blo 1148636 5818229 := bbase (se 5 (by rfl) ⟨272729, by rfl⟩ : syracuseStep 5818229 = 545459) (by norm_num)
theorem B1230709 : Blo 1148636 1230709 := bbase (se 5 (by rfl) ⟨57689, by rfl⟩ : syracuseStep 1230709 = 115379) (by norm_num)
theorem B1296265 : Blo 1148636 1296265 := bbase (se 2 (by rfl) ⟨486099, by rfl⟩ : syracuseStep 1296265 = 972199) (by norm_num)
theorem B1296301 : Blo 1148636 1296301 := bbase (se 3 (by rfl) ⟨243056, by rfl⟩ : syracuseStep 1296301 = 486113) (by norm_num)
theorem B1296337 : Blo 1148636 1296337 := bbase (se 2 (by rfl) ⟨486126, by rfl⟩ : syracuseStep 1296337 = 972253) (by norm_num)
theorem B2181077 : Blo 1148636 2181077 := bbase (se 7 (by rfl) ⟨25559, by rfl⟩ : syracuseStep 2181077 = 51119) (by norm_num)
theorem B3885029 : Blo 1148636 3885029 := bbase (se 4 (by rfl) ⟨364221, by rfl⟩ : syracuseStep 3885029 = 728443) (by norm_num)
theorem B1230833 : Blo 1148636 1230833 := bbase (se 2 (by rfl) ⟨461562, by rfl⟩ : syracuseStep 1230833 = 923125) (by norm_num)
theorem B1296373 : Blo 1148636 1296373 := bbase (se 5 (by rfl) ⟨60767, by rfl⟩ : syracuseStep 1296373 = 121535) (by norm_num)
theorem B1296409 : Blo 1148636 1296409 := bbase (se 2 (by rfl) ⟨486153, by rfl⟩ : syracuseStep 1296409 = 972307) (by norm_num)
theorem B1296445 : Blo 1148636 1296445 := bbase (se 3 (by rfl) ⟨243083, by rfl⟩ : syracuseStep 1296445 = 486167) (by norm_num)
theorem B1296481 : Blo 1148636 1296481 := bbase (se 2 (by rfl) ⟨486180, by rfl⟩ : syracuseStep 1296481 = 972361) (by norm_num)
theorem B1296517 : Blo 1148636 1296517 := bbase (se 4 (by rfl) ⟨121548, by rfl⟩ : syracuseStep 1296517 = 243097) (by norm_num)
theorem B1296553 : Blo 1148636 1296553 := bbase (se 2 (by rfl) ⟨486207, by rfl⟩ : syracuseStep 1296553 = 972415) (by norm_num)
theorem B1296589 : Blo 1148636 1296589 := bbase (se 3 (by rfl) ⟨243110, by rfl⟩ : syracuseStep 1296589 = 486221) (by norm_num)
theorem B1296625 : Blo 1148636 1296625 := bbase (se 2 (by rfl) ⟨486234, by rfl⟩ : syracuseStep 1296625 = 972469) (by norm_num)
theorem B1296661 : Blo 1148636 1296661 := bbase (se 6 (by rfl) ⟨30390, by rfl⟩ : syracuseStep 1296661 = 60781) (by norm_num)
theorem B1296697 : Blo 1148636 1296697 := bbase (se 2 (by rfl) ⟨486261, by rfl⟩ : syracuseStep 1296697 = 972523) (by norm_num)
theorem B1329517 : Blo 1148636 1329517 := bbase (se 3 (by rfl) ⟨249284, by rfl⟩ : syracuseStep 1329517 = 498569) (by norm_num)
theorem B3885461 : Blo 1148636 3885461 := bbase (se 6 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 3885461 = 182131) (by norm_num)
theorem B1722965 : Blo 1148636 1722965 := bbase (se 8 (by rfl) ⟨10095, by rfl⟩ : syracuseStep 1722965 = 20191) (by norm_num)
theorem B1722989 : Blo 1148636 1722989 := bbase (se 3 (by rfl) ⟨323060, by rfl⟩ : syracuseStep 1722989 = 646121) (by norm_num)
theorem B3689077 : Blo 1148636 3689077 := bbase (se 5 (by rfl) ⟨172925, by rfl⟩ : syracuseStep 3689077 = 345851) (by norm_num)
theorem B1723013 : Blo 1148636 1723013 := bbase (se 4 (by rfl) ⟨161532, by rfl⟩ : syracuseStep 1723013 = 323065) (by norm_num)
theorem B1723037 : Blo 1148636 1723037 := bbase (se 3 (by rfl) ⟨323069, by rfl⟩ : syracuseStep 1723037 = 646139) (by norm_num)
theorem B1723061 : Blo 1148636 1723061 := bbase (se 5 (by rfl) ⟨80768, by rfl⟩ : syracuseStep 1723061 = 161537) (by norm_num)
theorem B2181829 : Blo 1148636 2181829 := bbase (se 4 (by rfl) ⟨204546, by rfl⟩ : syracuseStep 2181829 = 409093) (by norm_num)
theorem B1723085 : Blo 1148636 1723085 := bbase (se 3 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 1723085 = 646157) (by norm_num)
theorem B1723109 : Blo 1148636 1723109 := bbase (se 4 (by rfl) ⟨161541, by rfl⟩ : syracuseStep 1723109 = 323083) (by norm_num)
theorem B1723133 : Blo 1148636 1723133 := bbase (se 3 (by rfl) ⟨323087, by rfl⟩ : syracuseStep 1723133 = 646175) (by norm_num)
theorem B1723157 : Blo 1148636 1723157 := bbase (se 6 (by rfl) ⟨40386, by rfl⟩ : syracuseStep 1723157 = 80773) (by norm_num)
theorem B1166113 : Blo 1148636 1166113 := bbase (se 2 (by rfl) ⟨437292, by rfl⟩ : syracuseStep 1166113 = 874585) (by norm_num)
theorem B1723181 : Blo 1148636 1723181 := bbase (se 3 (by rfl) ⟨323096, by rfl⟩ : syracuseStep 1723181 = 646193) (by norm_num)
theorem B1264441 : Blo 1148636 1264441 := bbase (se 2 (by rfl) ⟨474165, by rfl⟩ : syracuseStep 1264441 = 948331) (by norm_num)
theorem B1723205 : Blo 1148636 1723205 := bbase (se 4 (by rfl) ⟨161550, by rfl⟩ : syracuseStep 1723205 = 323101) (by norm_num)
theorem B3885893 : Blo 1148636 3885893 := bbase (se 4 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 3885893 = 728605) (by norm_num)
theorem B2181973 : Blo 1148636 2181973 := bbase (se 9 (by rfl) ⟨6392, by rfl⟩ : syracuseStep 2181973 = 12785) (by norm_num)
theorem B1723229 : Blo 1148636 1723229 := bbase (se 3 (by rfl) ⟨323105, by rfl⟩ : syracuseStep 1723229 = 646211) (by norm_num)
theorem B1723253 : Blo 1148636 1723253 := bbase (se 5 (by rfl) ⟨80777, by rfl⟩ : syracuseStep 1723253 = 161555) (by norm_num)
theorem B1723277 : Blo 1148636 1723277 := bbase (se 3 (by rfl) ⟨323114, by rfl⟩ : syracuseStep 1723277 = 646229) (by norm_num)
theorem B1723301 : Blo 1148636 1723301 := bbase (se 4 (by rfl) ⟨161559, by rfl⟩ : syracuseStep 1723301 = 323119) (by norm_num)
theorem B1723325 : Blo 1148636 1723325 := bbase (se 3 (by rfl) ⟨323123, by rfl⟩ : syracuseStep 1723325 = 646247) (by norm_num)
theorem B1723349 : Blo 1148636 1723349 := bbase (se 7 (by rfl) ⟨20195, by rfl⟩ : syracuseStep 1723349 = 40391) (by norm_num)
theorem B1723373 : Blo 1148636 1723373 := bbase (se 3 (by rfl) ⟨323132, by rfl⟩ : syracuseStep 1723373 = 646265) (by norm_num)
theorem B2182133 : Blo 1148636 2182133 := bbase (se 5 (by rfl) ⟨102287, by rfl⟩ : syracuseStep 2182133 = 204575) (by norm_num)
theorem B1723397 : Blo 1148636 1723397 := bbase (se 4 (by rfl) ⟨161568, by rfl⟩ : syracuseStep 1723397 = 323137) (by norm_num)
theorem B3984389 : Blo 1148636 3984389 := bbase (se 4 (by rfl) ⟨373536, by rfl⟩ : syracuseStep 3984389 = 747073) (by norm_num)
theorem B1723421 : Blo 1148636 1723421 := bbase (se 3 (by rfl) ⟨323141, by rfl⟩ : syracuseStep 1723421 = 646283) (by norm_num)
theorem B1723445 : Blo 1148636 1723445 := bbase (se 5 (by rfl) ⟨80786, by rfl⟩ : syracuseStep 1723445 = 161573) (by norm_num)
theorem B1723469 : Blo 1148636 1723469 := bbase (se 3 (by rfl) ⟨323150, by rfl⟩ : syracuseStep 1723469 = 646301) (by norm_num)
theorem B4148309 : Blo 1148636 4148309 := bbase (se 8 (by rfl) ⟨24306, by rfl⟩ : syracuseStep 4148309 = 48613) (by norm_num)
theorem B1723493 : Blo 1148636 1723493 := bbase (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) (by norm_num)
theorem B1723517 : Blo 1148636 1723517 := bbase (se 3 (by rfl) ⟨323159, by rfl⟩ : syracuseStep 1723517 = 646319) (by norm_num)
theorem B2182277 : Blo 1148636 2182277 := bbase (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) (by norm_num)
theorem B5819525 : Blo 1148636 5819525 := bbase (se 4 (by rfl) ⟨545580, by rfl⟩ : syracuseStep 5819525 = 1091161) (by norm_num)
theorem B1723541 : Blo 1148636 1723541 := bbase (se 6 (by rfl) ⟨40395, by rfl⟩ : syracuseStep 1723541 = 80791) (by norm_num)
theorem B1723565 : Blo 1148636 1723565 := bbase (se 3 (by rfl) ⟨323168, by rfl⟩ : syracuseStep 1723565 = 646337) (by norm_num)
theorem B1723589 : Blo 1148636 1723589 := bbase (se 4 (by rfl) ⟨161586, by rfl⟩ : syracuseStep 1723589 = 323173) (by norm_num)
theorem B1723613 : Blo 1148636 1723613 := bbase (se 3 (by rfl) ⟨323177, by rfl⟩ : syracuseStep 1723613 = 646355) (by norm_num)
theorem B1723637 : Blo 1148636 1723637 := bbase (se 5 (by rfl) ⟨80795, by rfl⟩ : syracuseStep 1723637 = 161591) (by norm_num)
theorem B3886325 : Blo 1148636 3886325 := bbase (se 5 (by rfl) ⟨182171, by rfl⟩ : syracuseStep 3886325 = 364343) (by norm_num)
theorem B1723661 : Blo 1148636 1723661 := bbase (se 3 (by rfl) ⟨323186, by rfl⟩ : syracuseStep 1723661 = 646373) (by norm_num)
theorem B5524757 : Blo 1148636 5524757 := bbase (se 6 (by rfl) ⟨129486, by rfl⟩ : syracuseStep 5524757 = 258973) (by norm_num)
theorem B1723685 : Blo 1148636 1723685 := bbase (se 4 (by rfl) ⟨161595, by rfl⟩ : syracuseStep 1723685 = 323191) (by norm_num)
theorem B1723709 : Blo 1148636 1723709 := bbase (se 3 (by rfl) ⟨323195, by rfl⟩ : syracuseStep 1723709 = 646391) (by norm_num)
theorem B1723733 : Blo 1148636 1723733 := bbase (se 11 (by rfl) ⟨1262, by rfl⟩ : syracuseStep 1723733 = 2525) (by norm_num)
theorem B1723757 : Blo 1148636 1723757 := bbase (se 3 (by rfl) ⟨323204, by rfl⟩ : syracuseStep 1723757 = 646409) (by norm_num)
theorem B4148597 : Blo 1148636 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B1723781 : Blo 1148636 1723781 := bbase (se 4 (by rfl) ⟨161604, by rfl⟩ : syracuseStep 1723781 = 323209) (by norm_num)
theorem B1723805 : Blo 1148636 1723805 := bbase (se 3 (by rfl) ⟨323213, by rfl⟩ : syracuseStep 1723805 = 646427) (by norm_num)
theorem B2182565 : Blo 1148636 2182565 := bbase (se 4 (by rfl) ⟨204615, by rfl⟩ : syracuseStep 2182565 = 409231) (by norm_num)
theorem B1723829 : Blo 1148636 1723829 := bbase (se 5 (by rfl) ⟨80804, by rfl⟩ : syracuseStep 1723829 = 161609) (by norm_num)
theorem B1723853 : Blo 1148636 1723853 := bbase (se 3 (by rfl) ⟨323222, by rfl⟩ : syracuseStep 1723853 = 646445) (by norm_num)
theorem B1723877 : Blo 1148636 1723877 := bbase (se 4 (by rfl) ⟨161613, by rfl⟩ : syracuseStep 1723877 = 323227) (by norm_num)
theorem B1723901 : Blo 1148636 1723901 := bbase (se 3 (by rfl) ⟨323231, by rfl⟩ : syracuseStep 1723901 = 646463) (by norm_num)
theorem B1723925 : Blo 1148636 1723925 := bbase (se 6 (by rfl) ⟨40404, by rfl⟩ : syracuseStep 1723925 = 80809) (by norm_num)
theorem B1723949 : Blo 1148636 1723949 := bbase (se 3 (by rfl) ⟨323240, by rfl⟩ : syracuseStep 1723949 = 646481) (by norm_num)
theorem B7884341 : Blo 1148636 7884341 := bbase (se 5 (by rfl) ⟨369578, by rfl⟩ : syracuseStep 7884341 = 739157) (by norm_num)
theorem B2182717 : Blo 1148636 2182717 := bbase (se 3 (by rfl) ⟨409259, by rfl⟩ : syracuseStep 2182717 = 818519) (by norm_num)
theorem B1723973 : Blo 1148636 1723973 := bbase (se 4 (by rfl) ⟨161622, by rfl⟩ : syracuseStep 1723973 = 323245) (by norm_num)
theorem B9817685 : Blo 1148636 9817685 := bbase (se 8 (by rfl) ⟨57525, by rfl⟩ : syracuseStep 9817685 = 115051) (by norm_num)
theorem B1723997 : Blo 1148636 1723997 := bbase (se 3 (by rfl) ⟨323249, by rfl⟩ : syracuseStep 1723997 = 646499) (by norm_num)
theorem B1724021 : Blo 1148636 1724021 := bbase (se 5 (by rfl) ⟨80813, by rfl⟩ : syracuseStep 1724021 = 161627) (by norm_num)
theorem B4673141 : Blo 1148636 4673141 := bbase (se 5 (by rfl) ⟨219053, by rfl⟩ : syracuseStep 4673141 = 438107) (by norm_num)
theorem B1724045 : Blo 1148636 1724045 := bbase (se 3 (by rfl) ⟨323258, by rfl⟩ : syracuseStep 1724045 = 646517) (by norm_num)
theorem B1724069 : Blo 1148636 1724069 := bbase (se 4 (by rfl) ⟨161631, by rfl⟩ : syracuseStep 1724069 = 323263) (by norm_num)
theorem B3886757 : Blo 1148636 3886757 := bbase (se 4 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 3886757 = 728767) (by norm_num)
theorem B1724093 : Blo 1148636 1724093 := bbase (se 3 (by rfl) ⟨323267, by rfl⟩ : syracuseStep 1724093 = 646535) (by norm_num)
theorem B1724117 : Blo 1148636 1724117 := bbase (se 7 (by rfl) ⟨20204, by rfl⟩ : syracuseStep 1724117 = 40409) (by norm_num)
theorem B1724141 : Blo 1148636 1724141 := bbase (se 3 (by rfl) ⟨323276, by rfl⟩ : syracuseStep 1724141 = 646553) (by norm_num)
theorem B1724165 : Blo 1148636 1724165 := bbase (se 4 (by rfl) ⟨161640, by rfl⟩ : syracuseStep 1724165 = 323281) (by norm_num)
theorem B1724189 : Blo 1148636 1724189 := bbase (se 3 (by rfl) ⟨323285, by rfl⟩ : syracuseStep 1724189 = 646571) (by norm_num)
theorem B1724213 : Blo 1148636 1724213 := bbase (se 5 (by rfl) ⟨80822, by rfl⟩ : syracuseStep 1724213 = 161645) (by norm_num)
theorem B1724237 : Blo 1148636 1724237 := bbase (se 3 (by rfl) ⟨323294, by rfl⟩ : syracuseStep 1724237 = 646589) (by norm_num)
theorem B1724261 : Blo 1148636 1724261 := bbase (se 4 (by rfl) ⟨161649, by rfl⟩ : syracuseStep 1724261 = 323299) (by norm_num)
theorem B2183021 : Blo 1148636 2183021 := bbase (se 3 (by rfl) ⟨409316, by rfl⟩ : syracuseStep 2183021 = 818633) (by norm_num)
theorem B1724285 : Blo 1148636 1724285 := bbase (se 3 (by rfl) ⟨323303, by rfl⟩ : syracuseStep 1724285 = 646607) (by norm_num)
theorem B1724309 : Blo 1148636 1724309 := bbase (se 6 (by rfl) ⟨40413, by rfl⟩ : syracuseStep 1724309 = 80827) (by norm_num)
theorem B1724333 : Blo 1148636 1724333 := bbase (se 3 (by rfl) ⟨323312, by rfl⟩ : syracuseStep 1724333 = 646625) (by norm_num)
theorem B1724357 : Blo 1148636 1724357 := bbase (se 4 (by rfl) ⟨161658, by rfl⟩ : syracuseStep 1724357 = 323317) (by norm_num)
theorem B1724381 : Blo 1148636 1724381 := bbase (se 3 (by rfl) ⟨323321, by rfl⟩ : syracuseStep 1724381 = 646643) (by norm_num)
theorem B1724405 : Blo 1148636 1724405 := bbase (se 5 (by rfl) ⟨80831, by rfl⟩ : syracuseStep 1724405 = 161663) (by norm_num)
theorem B1724429 : Blo 1148636 1724429 := bbase (se 3 (by rfl) ⟨323330, by rfl⟩ : syracuseStep 1724429 = 646661) (by norm_num)
theorem B1724453 : Blo 1148636 1724453 := bbase (se 4 (by rfl) ⟨161667, by rfl⟩ : syracuseStep 1724453 = 323335) (by norm_num)
theorem B8736821 : Blo 1148636 8736821 := bbase (se 5 (by rfl) ⟨409538, by rfl⟩ : syracuseStep 8736821 = 819077) (by norm_num)
theorem B1724477 : Blo 1148636 1724477 := bbase (se 3 (by rfl) ⟨323339, by rfl⟩ : syracuseStep 1724477 = 646679) (by norm_num)
theorem B1724501 : Blo 1148636 1724501 := bbase (se 8 (by rfl) ⟨10104, by rfl⟩ : syracuseStep 1724501 = 20209) (by norm_num)
theorem B3887189 : Blo 1148636 3887189 := bbase (se 8 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 3887189 = 45553) (by norm_num)
theorem B1724525 : Blo 1148636 1724525 := bbase (se 3 (by rfl) ⟨323348, by rfl⟩ : syracuseStep 1724525 = 646697) (by norm_num)
theorem B1724549 : Blo 1148636 1724549 := bbase (se 4 (by rfl) ⟨161676, by rfl⟩ : syracuseStep 1724549 = 323353) (by norm_num)
theorem B1724573 : Blo 1148636 1724573 := bbase (se 3 (by rfl) ⟨323357, by rfl⟩ : syracuseStep 1724573 = 646715) (by norm_num)
theorem B1724597 : Blo 1148636 1724597 := bbase (se 5 (by rfl) ⟨80840, by rfl⟩ : syracuseStep 1724597 = 161681) (by norm_num)
theorem B1724621 : Blo 1148636 1724621 := bbase (se 3 (by rfl) ⟨323366, by rfl⟩ : syracuseStep 1724621 = 646733) (by norm_num)
theorem B1724645 : Blo 1148636 1724645 := bbase (se 4 (by rfl) ⟨161685, by rfl⟩ : syracuseStep 1724645 = 323371) (by norm_num)
theorem B1724669 : Blo 1148636 1724669 := bbase (se 3 (by rfl) ⟨323375, by rfl⟩ : syracuseStep 1724669 = 646751) (by norm_num)
theorem B3035389 : Blo 1148636 3035389 := bbase (se 3 (by rfl) ⟨569135, by rfl⟩ : syracuseStep 3035389 = 1138271) (by norm_num)
theorem B1724693 : Blo 1148636 1724693 := bbase (se 6 (by rfl) ⟨40422, by rfl⟩ : syracuseStep 1724693 = 80845) (by norm_num)
theorem B1724717 : Blo 1148636 1724717 := bbase (se 3 (by rfl) ⟨323384, by rfl⟩ : syracuseStep 1724717 = 646769) (by norm_num)
theorem B1724741 : Blo 1148636 1724741 := bbase (se 4 (by rfl) ⟨161694, by rfl⟩ : syracuseStep 1724741 = 323389) (by norm_num)
theorem B1724765 : Blo 1148636 1724765 := bbase (se 3 (by rfl) ⟨323393, by rfl⟩ : syracuseStep 1724765 = 646787) (by norm_num)
theorem B1724789 : Blo 1148636 1724789 := bbase (se 5 (by rfl) ⟨80849, by rfl⟩ : syracuseStep 1724789 = 161699) (by norm_num)
theorem B1724813 : Blo 1148636 1724813 := bbase (se 3 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 1724813 = 646805) (by norm_num)
theorem B5820821 : Blo 1148636 5820821 := bbase (se 6 (by rfl) ⟨136425, by rfl⟩ : syracuseStep 5820821 = 272851) (by norm_num)
theorem B1724837 : Blo 1148636 1724837 := bbase (se 4 (by rfl) ⟨161703, by rfl⟩ : syracuseStep 1724837 = 323407) (by norm_num)
theorem B1724861 : Blo 1148636 1724861 := bbase (se 3 (by rfl) ⟨323411, by rfl⟩ : syracuseStep 1724861 = 646823) (by norm_num)
theorem B1724885 : Blo 1148636 1724885 := bbase (se 7 (by rfl) ⟨20213, by rfl⟩ : syracuseStep 1724885 = 40427) (by norm_num)
theorem B1724909 : Blo 1148636 1724909 := bbase (se 3 (by rfl) ⟨323420, by rfl⟩ : syracuseStep 1724909 = 646841) (by norm_num)
theorem B1724933 : Blo 1148636 1724933 := bbase (se 4 (by rfl) ⟨161712, by rfl⟩ : syracuseStep 1724933 = 323425) (by norm_num)
theorem B3887621 : Blo 1148636 3887621 := bbase (se 4 (by rfl) ⟨364464, by rfl⟩ : syracuseStep 3887621 = 728929) (by norm_num)
theorem B1724957 : Blo 1148636 1724957 := bbase (se 3 (by rfl) ⟨323429, by rfl⟩ : syracuseStep 1724957 = 646859) (by norm_num)
theorem B1724981 : Blo 1148636 1724981 := bbase (se 5 (by rfl) ⟨80858, by rfl⟩ : syracuseStep 1724981 = 161717) (by norm_num)
theorem B1725005 : Blo 1148636 1725005 := bbase (se 3 (by rfl) ⟨323438, by rfl⟩ : syracuseStep 1725005 = 646877) (by norm_num)
theorem B1167953 : Blo 1148636 1167953 := bbase (se 2 (by rfl) ⟨437982, by rfl⟩ : syracuseStep 1167953 = 875965) (by norm_num)
theorem B2183773 : Blo 1148636 2183773 := bbase (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) (by norm_num)
theorem B1725029 : Blo 1148636 1725029 := bbase (se 4 (by rfl) ⟨161721, by rfl⟩ : syracuseStep 1725029 = 323443) (by norm_num)
theorem B1167977 : Blo 1148636 1167977 := bbase (se 2 (by rfl) ⟨437991, by rfl⟩ : syracuseStep 1167977 = 875983) (by norm_num)
theorem B1725053 : Blo 1148636 1725053 := bbase (se 3 (by rfl) ⟨323447, by rfl⟩ : syracuseStep 1725053 = 646895) (by norm_num)
theorem B1725077 : Blo 1148636 1725077 := bbase (se 6 (by rfl) ⟨40431, by rfl⟩ : syracuseStep 1725077 = 80863) (by norm_num)
theorem B1725101 : Blo 1148636 1725101 := bbase (se 3 (by rfl) ⟨323456, by rfl⟩ : syracuseStep 1725101 = 646913) (by norm_num)
theorem B1725125 : Blo 1148636 1725125 := bbase (se 4 (by rfl) ⟨161730, by rfl⟩ : syracuseStep 1725125 = 323461) (by norm_num)
theorem B1725149 : Blo 1148636 1725149 := bbase (se 3 (by rfl) ⟨323465, by rfl⟩ : syracuseStep 1725149 = 646931) (by norm_num)
theorem B2183917 : Blo 1148636 2183917 := bbase (se 3 (by rfl) ⟨409484, by rfl⟩ : syracuseStep 2183917 = 818969) (by norm_num)
theorem B1725173 : Blo 1148636 1725173 := bbase (se 5 (by rfl) ⟨80867, by rfl⟩ : syracuseStep 1725173 = 161735) (by norm_num)
theorem B1725197 : Blo 1148636 1725197 := bbase (se 3 (by rfl) ⟨323474, by rfl⟩ : syracuseStep 1725197 = 646949) (by norm_num)
theorem B1725221 : Blo 1148636 1725221 := bbase (se 4 (by rfl) ⟨161739, by rfl⟩ : syracuseStep 1725221 = 323479) (by norm_num)
theorem B1725245 : Blo 1148636 1725245 := bbase (se 3 (by rfl) ⟨323483, by rfl⟩ : syracuseStep 1725245 = 646967) (by norm_num)
theorem B1725269 : Blo 1148636 1725269 := bbase (se 9 (by rfl) ⟨5054, by rfl⟩ : syracuseStep 1725269 = 10109) (by norm_num)
theorem B1725293 : Blo 1148636 1725293 := bbase (se 3 (by rfl) ⟨323492, by rfl⟩ : syracuseStep 1725293 = 646985) (by norm_num)
theorem B1725317 : Blo 1148636 1725317 := bbase (se 4 (by rfl) ⟨161748, by rfl⟩ : syracuseStep 1725317 = 323497) (by norm_num)
theorem B2184077 : Blo 1148636 2184077 := bbase (se 3 (by rfl) ⟨409514, by rfl⟩ : syracuseStep 2184077 = 819029) (by norm_num)
theorem B1725341 : Blo 1148636 1725341 := bbase (se 3 (by rfl) ⟨323501, by rfl⟩ : syracuseStep 1725341 = 647003) (by norm_num)
theorem B1725365 : Blo 1148636 1725365 := bbase (se 5 (by rfl) ⟨80876, by rfl⟩ : syracuseStep 1725365 = 161753) (by norm_num)
theorem B3888053 : Blo 1148636 3888053 := bbase (se 5 (by rfl) ⟨182252, by rfl⟩ : syracuseStep 3888053 = 364505) (by norm_num)
theorem B1725389 : Blo 1148636 1725389 := bbase (se 3 (by rfl) ⟨323510, by rfl⟩ : syracuseStep 1725389 = 647021) (by norm_num)
theorem B1725413 : Blo 1148636 1725413 := bbase (se 4 (by rfl) ⟨161757, by rfl⟩ : syracuseStep 1725413 = 323515) (by norm_num)
theorem B1725437 : Blo 1148636 1725437 := bbase (se 3 (by rfl) ⟨323519, by rfl⟩ : syracuseStep 1725437 = 647039) (by norm_num)
theorem B1725461 : Blo 1148636 1725461 := bbase (se 6 (by rfl) ⟨40440, by rfl⟩ : syracuseStep 1725461 = 80881) (by norm_num)
theorem B2184221 : Blo 1148636 2184221 := bbase (se 3 (by rfl) ⟨409541, by rfl⟩ : syracuseStep 2184221 = 819083) (by norm_num)
theorem B1725485 : Blo 1148636 1725485 := bbase (se 3 (by rfl) ⟨323528, by rfl⟩ : syracuseStep 1725485 = 647057) (by norm_num)
theorem B1725509 : Blo 1148636 1725509 := bbase (se 4 (by rfl) ⟨161766, by rfl⟩ : syracuseStep 1725509 = 323533) (by norm_num)
theorem B1725533 : Blo 1148636 1725533 := bbase (se 3 (by rfl) ⟨323537, by rfl⟩ : syracuseStep 1725533 = 647075) (by norm_num)
theorem B1725557 : Blo 1148636 1725557 := bbase (se 5 (by rfl) ⟨80885, by rfl⟩ : syracuseStep 1725557 = 161771) (by norm_num)
theorem B1725581 : Blo 1148636 1725581 := bbase (se 3 (by rfl) ⟨323546, by rfl⟩ : syracuseStep 1725581 = 647093) (by norm_num)
theorem B1725605 : Blo 1148636 1725605 := bbase (se 4 (by rfl) ⟨161775, by rfl⟩ : syracuseStep 1725605 = 323551) (by norm_num)
theorem B9327797 : Blo 1148636 9327797 := bbase (se 5 (by rfl) ⟨437240, by rfl⟩ : syracuseStep 9327797 = 874481) (by norm_num)
theorem B1725629 : Blo 1148636 1725629 := bbase (se 3 (by rfl) ⟨323555, by rfl⟩ : syracuseStep 1725629 = 647111) (by norm_num)
theorem B1725653 : Blo 1148636 1725653 := bbase (se 7 (by rfl) ⟨20222, by rfl⟩ : syracuseStep 1725653 = 40445) (by norm_num)
theorem B1725677 : Blo 1148636 1725677 := bbase (se 3 (by rfl) ⟨323564, by rfl⟩ : syracuseStep 1725677 = 647129) (by norm_num)
theorem B1725701 : Blo 1148636 1725701 := bbase (se 4 (by rfl) ⟨161784, by rfl⟩ : syracuseStep 1725701 = 323569) (by norm_num)
theorem B1725725 : Blo 1148636 1725725 := bbase (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) (by norm_num)
theorem B1725749 : Blo 1148636 1725749 := bbase (se 5 (by rfl) ⟨80894, by rfl⟩ : syracuseStep 1725749 = 161789) (by norm_num)
theorem B2184509 : Blo 1148636 2184509 := bbase (se 3 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 2184509 = 819191) (by norm_num)
theorem B1725773 : Blo 1148636 1725773 := bbase (se 3 (by rfl) ⟨323582, by rfl⟩ : syracuseStep 1725773 = 647165) (by norm_num)
theorem B1725797 : Blo 1148636 1725797 := bbase (se 4 (by rfl) ⟨161793, by rfl⟩ : syracuseStep 1725797 = 323587) (by norm_num)
theorem B3888485 : Blo 1148636 3888485 := bbase (se 4 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 3888485 = 729091) (by norm_num)
theorem B1725821 : Blo 1148636 1725821 := bbase (se 3 (by rfl) ⟨323591, by rfl⟩ : syracuseStep 1725821 = 647183) (by norm_num)
theorem B1725845 : Blo 1148636 1725845 := bbase (se 6 (by rfl) ⟨40449, by rfl⟩ : syracuseStep 1725845 = 80899) (by norm_num)
theorem B1725869 : Blo 1148636 1725869 := bbase (se 3 (by rfl) ⟨323600, by rfl⟩ : syracuseStep 1725869 = 647201) (by norm_num)
theorem B1725893 : Blo 1148636 1725893 := bbase (se 4 (by rfl) ⟨161802, by rfl⟩ : syracuseStep 1725893 = 323605) (by norm_num)
theorem B2184661 : Blo 1148636 2184661 := bbase (se 7 (by rfl) ⟨25601, by rfl⟩ : syracuseStep 2184661 = 51203) (by norm_num)
theorem B1725917 : Blo 1148636 1725917 := bbase (se 3 (by rfl) ⟨323609, by rfl⟩ : syracuseStep 1725917 = 647219) (by norm_num)
theorem B1725941 : Blo 1148636 1725941 := bbase (se 5 (by rfl) ⟨80903, by rfl⟩ : syracuseStep 1725941 = 161807) (by norm_num)
theorem B1725965 : Blo 1148636 1725965 := bbase (se 3 (by rfl) ⟨323618, by rfl⟩ : syracuseStep 1725965 = 647237) (by norm_num)
theorem B1725989 : Blo 1148636 1725989 := bbase (se 4 (by rfl) ⟨161811, by rfl⟩ : syracuseStep 1725989 = 323623) (by norm_num)
theorem B1726013 : Blo 1148636 1726013 := bbase (se 3 (by rfl) ⟨323627, by rfl⟩ : syracuseStep 1726013 = 647255) (by norm_num)
theorem B3692101 : Blo 1148636 3692101 := bbase (se 4 (by rfl) ⟨346134, by rfl⟩ : syracuseStep 3692101 = 692269) (by norm_num)
theorem B1726037 : Blo 1148636 1726037 := bbase (se 8 (by rfl) ⟨10113, by rfl⟩ : syracuseStep 1726037 = 20227) (by norm_num)
theorem B1726061 : Blo 1148636 1726061 := bbase (se 3 (by rfl) ⟨323636, by rfl⟩ : syracuseStep 1726061 = 647273) (by norm_num)
theorem B1726085 : Blo 1148636 1726085 := bbase (se 4 (by rfl) ⟨161820, by rfl⟩ : syracuseStep 1726085 = 323641) (by norm_num)
theorem B1726109 : Blo 1148636 1726109 := bbase (se 3 (by rfl) ⟨323645, by rfl⟩ : syracuseStep 1726109 = 647291) (by norm_num)
theorem B5822117 : Blo 1148636 5822117 := bbase (se 4 (by rfl) ⟨545823, by rfl⟩ : syracuseStep 5822117 = 1091647) (by norm_num)
theorem B1726133 : Blo 1148636 1726133 := bbase (se 5 (by rfl) ⟨80912, by rfl⟩ : syracuseStep 1726133 = 161825) (by norm_num)
theorem B1726157 : Blo 1148636 1726157 := bbase (se 3 (by rfl) ⟨323654, by rfl⟩ : syracuseStep 1726157 = 647309) (by norm_num)
theorem B1726181 : Blo 1148636 1726181 := bbase (se 4 (by rfl) ⟨161829, by rfl⟩ : syracuseStep 1726181 = 323659) (by norm_num)
theorem B1726205 : Blo 1148636 1726205 := bbase (se 3 (by rfl) ⟨323663, by rfl⟩ : syracuseStep 1726205 = 647327) (by norm_num)
theorem B2184965 : Blo 1148636 2184965 := bbase (se 4 (by rfl) ⟨204840, by rfl⟩ : syracuseStep 2184965 = 409681) (by norm_num)
theorem B1726229 : Blo 1148636 1726229 := bbase (se 6 (by rfl) ⟨40458, by rfl⟩ : syracuseStep 1726229 = 80917) (by norm_num)
theorem B3888917 : Blo 1148636 3888917 := bbase (se 6 (by rfl) ⟨91146, by rfl⟩ : syracuseStep 3888917 = 182293) (by norm_num)
theorem B1726253 : Blo 1148636 1726253 := bbase (se 3 (by rfl) ⟨323672, by rfl⟩ : syracuseStep 1726253 = 647345) (by norm_num)
theorem B1726277 : Blo 1148636 1726277 := bbase (se 4 (by rfl) ⟨161838, by rfl⟩ : syracuseStep 1726277 = 323677) (by norm_num)
theorem B1726301 : Blo 1148636 1726301 := bbase (se 3 (by rfl) ⟨323681, by rfl⟩ : syracuseStep 1726301 = 647363) (by norm_num)
theorem B1726325 : Blo 1148636 1726325 := bbase (se 5 (by rfl) ⟨80921, by rfl⟩ : syracuseStep 1726325 = 161843) (by norm_num)
theorem B1726349 : Blo 1148636 1726349 := bbase (se 3 (by rfl) ⟨323690, by rfl⟩ : syracuseStep 1726349 = 647381) (by norm_num)
theorem B1726373 : Blo 1148636 1726373 := bbase (se 4 (by rfl) ⟨161847, by rfl⟩ : syracuseStep 1726373 = 323695) (by norm_num)
theorem B1726397 : Blo 1148636 1726397 := bbase (se 3 (by rfl) ⟨323699, by rfl⟩ : syracuseStep 1726397 = 647399) (by norm_num)
theorem B1726421 : Blo 1148636 1726421 := bbase (se 7 (by rfl) ⟨20231, by rfl⟩ : syracuseStep 1726421 = 40463) (by norm_num)
theorem B1726445 : Blo 1148636 1726445 := bbase (se 3 (by rfl) ⟨323708, by rfl⟩ : syracuseStep 1726445 = 647417) (by norm_num)
theorem B5527541 : Blo 1148636 5527541 := bbase (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) (by norm_num)
theorem B1726469 : Blo 1148636 1726469 := bbase (se 4 (by rfl) ⟨161856, by rfl⟩ : syracuseStep 1726469 = 323713) (by norm_num)
theorem B1726493 : Blo 1148636 1726493 := bbase (se 3 (by rfl) ⟨323717, by rfl⟩ : syracuseStep 1726493 = 647435) (by norm_num)
theorem B6543413 : Blo 1148636 6543413 := bbase (se 5 (by rfl) ⟨306722, by rfl⟩ : syracuseStep 6543413 = 613445) (by norm_num)
theorem B1726517 : Blo 1148636 1726517 := bbase (se 5 (by rfl) ⟨80930, by rfl⟩ : syracuseStep 1726517 = 161861) (by norm_num)
theorem B1726541 : Blo 1148636 1726541 := bbase (se 3 (by rfl) ⟨323726, by rfl⟩ : syracuseStep 1726541 = 647453) (by norm_num)
theorem B1726565 : Blo 1148636 1726565 := bbase (se 4 (by rfl) ⟨161865, by rfl⟩ : syracuseStep 1726565 = 323731) (by norm_num)
theorem B1726589 : Blo 1148636 1726589 := bbase (se 3 (by rfl) ⟨323735, by rfl⟩ : syracuseStep 1726589 = 647471) (by norm_num)
theorem B1726613 : Blo 1148636 1726613 := bbase (se 6 (by rfl) ⟨40467, by rfl⟩ : syracuseStep 1726613 = 80935) (by norm_num)
theorem B1726637 : Blo 1148636 1726637 := bbase (se 3 (by rfl) ⟨323744, by rfl⟩ : syracuseStep 1726637 = 647489) (by norm_num)
theorem B1726661 : Blo 1148636 1726661 := bbase (se 4 (by rfl) ⟨161874, by rfl⟩ : syracuseStep 1726661 = 323749) (by norm_num)
theorem B3889349 : Blo 1148636 3889349 := bbase (se 4 (by rfl) ⟨364626, by rfl⟩ : syracuseStep 3889349 = 729253) (by norm_num)
theorem B1726685 : Blo 1148636 1726685 := bbase (se 3 (by rfl) ⟨323753, by rfl⟩ : syracuseStep 1726685 = 647507) (by norm_num)
theorem B1726709 : Blo 1148636 1726709 := bbase (se 5 (by rfl) ⟨80939, by rfl⟩ : syracuseStep 1726709 = 161879) (by norm_num)
theorem B1726733 : Blo 1148636 1726733 := bbase (se 3 (by rfl) ⟨323762, by rfl⟩ : syracuseStep 1726733 = 647525) (by norm_num)
theorem B1726757 : Blo 1148636 1726757 := bbase (se 4 (by rfl) ⟨161883, by rfl⟩ : syracuseStep 1726757 = 323767) (by norm_num)
theorem B1726781 : Blo 1148636 1726781 := bbase (se 3 (by rfl) ⟨323771, by rfl⟩ : syracuseStep 1726781 = 647543) (by norm_num)
theorem B1726805 : Blo 1148636 1726805 := bbase (se 10 (by rfl) ⟨2529, by rfl⟩ : syracuseStep 1726805 = 5059) (by norm_num)
theorem B1726829 : Blo 1148636 1726829 := bbase (se 3 (by rfl) ⟨323780, by rfl⟩ : syracuseStep 1726829 = 647561) (by norm_num)
theorem B1726853 : Blo 1148636 1726853 := bbase (se 4 (by rfl) ⟨161892, by rfl⟩ : syracuseStep 1726853 = 323785) (by norm_num)
theorem B1726877 : Blo 1148636 1726877 := bbase (se 3 (by rfl) ⟨323789, by rfl⟩ : syracuseStep 1726877 = 647579) (by norm_num)
theorem B1726901 : Blo 1148636 1726901 := bbase (se 5 (by rfl) ⟨80948, by rfl⟩ : syracuseStep 1726901 = 161897) (by norm_num)
theorem B1726925 : Blo 1148636 1726925 := bbase (se 3 (by rfl) ⟨323798, by rfl⟩ : syracuseStep 1726925 = 647597) (by norm_num)
theorem B1726949 : Blo 1148636 1726949 := bbase (se 4 (by rfl) ⟨161901, by rfl⟩ : syracuseStep 1726949 = 323803) (by norm_num)
theorem B2185717 : Blo 1148636 2185717 := bbase (se 5 (by rfl) ⟨102455, by rfl⟩ : syracuseStep 2185717 = 204911) (by norm_num)
theorem B7363061 : Blo 1148636 7363061 := bbase (se 5 (by rfl) ⟨345143, by rfl⟩ : syracuseStep 7363061 = 690287) (by norm_num)
theorem B1726973 : Blo 1148636 1726973 := bbase (se 3 (by rfl) ⟨323807, by rfl⟩ : syracuseStep 1726973 = 647615) (by norm_num)
theorem B1726997 : Blo 1148636 1726997 := bbase (se 6 (by rfl) ⟨40476, by rfl⟩ : syracuseStep 1726997 = 80953) (by norm_num)
theorem B1727021 : Blo 1148636 1727021 := bbase (se 3 (by rfl) ⟨323816, by rfl⟩ : syracuseStep 1727021 = 647633) (by norm_num)
theorem B1727045 : Blo 1148636 1727045 := bbase (se 4 (by rfl) ⟨161910, by rfl⟩ : syracuseStep 1727045 = 323821) (by norm_num)
theorem B1727069 : Blo 1148636 1727069 := bbase (se 3 (by rfl) ⟨323825, by rfl⟩ : syracuseStep 1727069 = 647651) (by norm_num)
theorem B1727093 : Blo 1148636 1727093 := bbase (se 5 (by rfl) ⟨80957, by rfl⟩ : syracuseStep 1727093 = 161915) (by norm_num)
theorem B3889781 : Blo 1148636 3889781 := bbase (se 5 (by rfl) ⟨182333, by rfl⟩ : syracuseStep 3889781 = 364667) (by norm_num)
theorem B2185861 : Blo 1148636 2185861 := bbase (se 4 (by rfl) ⟨204924, by rfl⟩ : syracuseStep 2185861 = 409849) (by norm_num)
theorem B1727117 : Blo 1148636 1727117 := bbase (se 3 (by rfl) ⟨323834, by rfl⟩ : syracuseStep 1727117 = 647669) (by norm_num)
theorem B1727141 : Blo 1148636 1727141 := bbase (se 4 (by rfl) ⟨161919, by rfl⟩ : syracuseStep 1727141 = 323839) (by norm_num)
theorem B1727165 : Blo 1148636 1727165 := bbase (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) (by norm_num)
theorem B1727189 : Blo 1148636 1727189 := bbase (se 7 (by rfl) ⟨20240, by rfl⟩ : syracuseStep 1727189 = 40481) (by norm_num)
theorem B1727213 : Blo 1148636 1727213 := bbase (se 3 (by rfl) ⟨323852, by rfl⟩ : syracuseStep 1727213 = 647705) (by norm_num)
theorem B1727237 : Blo 1148636 1727237 := bbase (se 4 (by rfl) ⟨161928, by rfl⟩ : syracuseStep 1727237 = 323857) (by norm_num)
theorem B1727261 : Blo 1148636 1727261 := bbase (se 3 (by rfl) ⟨323861, by rfl⟩ : syracuseStep 1727261 = 647723) (by norm_num)
theorem B2186021 : Blo 1148636 2186021 := bbase (se 4 (by rfl) ⟨204939, by rfl⟩ : syracuseStep 2186021 = 409879) (by norm_num)
theorem B1727285 : Blo 1148636 1727285 := bbase (se 5 (by rfl) ⟨80966, by rfl⟩ : syracuseStep 1727285 = 161933) (by norm_num)
theorem B1727309 : Blo 1148636 1727309 := bbase (se 3 (by rfl) ⟨323870, by rfl⟩ : syracuseStep 1727309 = 647741) (by norm_num)
theorem B1727333 : Blo 1148636 1727333 := bbase (se 4 (by rfl) ⟨161937, by rfl⟩ : syracuseStep 1727333 = 323875) (by norm_num)
theorem B1727357 : Blo 1148636 1727357 := bbase (se 3 (by rfl) ⟨323879, by rfl⟩ : syracuseStep 1727357 = 647759) (by norm_num)
theorem B1727381 : Blo 1148636 1727381 := bbase (se 6 (by rfl) ⟨40485, by rfl⟩ : syracuseStep 1727381 = 80971) (by norm_num)
theorem B1727405 : Blo 1148636 1727405 := bbase (se 3 (by rfl) ⟨323888, by rfl⟩ : syracuseStep 1727405 = 647777) (by norm_num)
theorem B5823413 : Blo 1148636 5823413 := bbase (se 5 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 5823413 = 545945) (by norm_num)
theorem B2186165 : Blo 1148636 2186165 := bbase (se 5 (by rfl) ⟨102476, by rfl⟩ : syracuseStep 2186165 = 204953) (by norm_num)
theorem B1727429 : Blo 1148636 1727429 := bbase (se 4 (by rfl) ⟨161946, by rfl⟩ : syracuseStep 1727429 = 323893) (by norm_num)
theorem B7003093 : Blo 1148636 7003093 := bbase (se 7 (by rfl) ⟨82067, by rfl⟩ : syracuseStep 7003093 = 164135) (by norm_num)
theorem B1727453 : Blo 1148636 1727453 := bbase (se 3 (by rfl) ⟨323897, by rfl⟩ : syracuseStep 1727453 = 647795) (by norm_num)
theorem B1727477 : Blo 1148636 1727477 := bbase (se 5 (by rfl) ⟨80975, by rfl⟩ : syracuseStep 1727477 = 161951) (by norm_num)
theorem B1727501 : Blo 1148636 1727501 := bbase (se 3 (by rfl) ⟨323906, by rfl⟩ : syracuseStep 1727501 = 647813) (by norm_num)
theorem B1727525 : Blo 1148636 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B7003189 : Blo 1148636 7003189 := bbase (se 5 (by rfl) ⟨328274, by rfl⟩ : syracuseStep 7003189 = 656549) (by norm_num)
theorem B1727549 : Blo 1148636 1727549 := bbase (se 3 (by rfl) ⟨323915, by rfl⟩ : syracuseStep 1727549 = 647831) (by norm_num)
theorem B1727573 : Blo 1148636 1727573 := bbase (se 8 (by rfl) ⟨10122, by rfl⟩ : syracuseStep 1727573 = 20245) (by norm_num)
theorem B1727597 : Blo 1148636 1727597 := bbase (se 3 (by rfl) ⟨323924, by rfl⟩ : syracuseStep 1727597 = 647849) (by norm_num)
theorem B1727621 : Blo 1148636 1727621 := bbase (se 4 (by rfl) ⟨161964, by rfl⟩ : syracuseStep 1727621 = 323929) (by norm_num)
theorem B1727645 : Blo 1148636 1727645 := bbase (se 3 (by rfl) ⟨323933, by rfl⟩ : syracuseStep 1727645 = 647867) (by norm_num)
theorem B1727669 : Blo 1148636 1727669 := bbase (se 5 (by rfl) ⟨80984, by rfl⟩ : syracuseStep 1727669 = 161969) (by norm_num)
theorem B1727693 : Blo 1148636 1727693 := bbase (se 3 (by rfl) ⟨323942, by rfl⟩ : syracuseStep 1727693 = 647885) (by norm_num)
theorem B6544597 : Blo 1148636 6544597 := bbase (se 7 (by rfl) ⟨76694, by rfl⟩ : syracuseStep 6544597 = 153389) (by norm_num)
theorem B2186453 : Blo 1148636 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B1727717 : Blo 1148636 1727717 := bbase (se 4 (by rfl) ⟨161973, by rfl⟩ : syracuseStep 1727717 = 323947) (by norm_num)
theorem B1727741 : Blo 1148636 1727741 := bbase (se 3 (by rfl) ⟨323951, by rfl⟩ : syracuseStep 1727741 = 647903) (by norm_num)
theorem B1727765 : Blo 1148636 1727765 := bbase (se 6 (by rfl) ⟨40494, by rfl⟩ : syracuseStep 1727765 = 80989) (by norm_num)
theorem B1727789 : Blo 1148636 1727789 := bbase (se 3 (by rfl) ⟨323960, by rfl⟩ : syracuseStep 1727789 = 647921) (by norm_num)
theorem B1727813 : Blo 1148636 1727813 := bbase (se 4 (by rfl) ⟨161982, by rfl⟩ : syracuseStep 1727813 = 323965) (by norm_num)
theorem B1727837 : Blo 1148636 1727837 := bbase (se 3 (by rfl) ⟨323969, by rfl⟩ : syracuseStep 1727837 = 647939) (by norm_num)
theorem B2186605 : Blo 1148636 2186605 := bbase (se 3 (by rfl) ⟨409988, by rfl⟩ : syracuseStep 2186605 = 819977) (by norm_num)
theorem B1727861 : Blo 1148636 1727861 := bbase (se 5 (by rfl) ⟨80993, by rfl⟩ : syracuseStep 1727861 = 161987) (by norm_num)
theorem B1727885 : Blo 1148636 1727885 := bbase (se 3 (by rfl) ⟨323978, by rfl⟩ : syracuseStep 1727885 = 647957) (by norm_num)
theorem B1727909 : Blo 1148636 1727909 := bbase (se 4 (by rfl) ⟨161991, by rfl⟩ : syracuseStep 1727909 = 323983) (by norm_num)
theorem B1727933 : Blo 1148636 1727933 := bbase (se 3 (by rfl) ⟨323987, by rfl⟩ : syracuseStep 1727933 = 647975) (by norm_num)
theorem B1727957 : Blo 1148636 1727957 := bbase (se 7 (by rfl) ⟨20249, by rfl⟩ : syracuseStep 1727957 = 40499) (by norm_num)
theorem B1662445 : Blo 1148636 1662445 := bbase (se 3 (by rfl) ⟨311708, by rfl⟩ : syracuseStep 1662445 = 623417) (by norm_num)
theorem B1727981 : Blo 1148636 1727981 := bbase (se 3 (by rfl) ⟨323996, by rfl⟩ : syracuseStep 1727981 = 647993) (by norm_num)
theorem B1728005 : Blo 1148636 1728005 := bbase (se 4 (by rfl) ⟨162000, by rfl⟩ : syracuseStep 1728005 = 324001) (by norm_num)
theorem B2907677 : Blo 1148636 2907677 := bbase (se 3 (by rfl) ⟨545189, by rfl⟩ : syracuseStep 2907677 = 1090379) (by norm_num)
theorem B1728029 : Blo 1148636 1728029 := bbase (se 3 (by rfl) ⟨324005, by rfl⟩ : syracuseStep 1728029 = 648011) (by norm_num)
theorem B3497509 : Blo 1148636 3497509 := bbase (se 4 (by rfl) ⟨327891, by rfl⟩ : syracuseStep 3497509 = 655783) (by norm_num)
theorem B1728053 : Blo 1148636 1728053 := bbase (se 5 (by rfl) ⟨81002, by rfl⟩ : syracuseStep 1728053 = 162005) (by norm_num)
theorem B1728077 : Blo 1148636 1728077 := bbase (se 3 (by rfl) ⟨324014, by rfl⟩ : syracuseStep 1728077 = 648029) (by norm_num)
theorem B1728101 : Blo 1148636 1728101 := bbase (se 4 (by rfl) ⟨162009, by rfl⟩ : syracuseStep 1728101 = 324019) (by norm_num)
theorem B2842229 : Blo 1148636 2842229 := bbase (se 5 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 2842229 = 266459) (by norm_num)
theorem B1728125 : Blo 1148636 1728125 := bbase (se 3 (by rfl) ⟨324023, by rfl⟩ : syracuseStep 1728125 = 648047) (by norm_num)
theorem B1728149 : Blo 1148636 1728149 := bbase (se 6 (by rfl) ⟨40503, by rfl⟩ : syracuseStep 1728149 = 81007) (by norm_num)
theorem B2186909 : Blo 1148636 2186909 := bbase (se 3 (by rfl) ⟨410045, by rfl⟩ : syracuseStep 2186909 = 820091) (by norm_num)
theorem B1728173 : Blo 1148636 1728173 := bbase (se 3 (by rfl) ⟨324032, by rfl⟩ : syracuseStep 1728173 = 648065) (by norm_num)
theorem B1728197 : Blo 1148636 1728197 := bbase (se 4 (by rfl) ⟨162018, by rfl⟩ : syracuseStep 1728197 = 324037) (by norm_num)
theorem B1728221 : Blo 1148636 1728221 := bbase (se 3 (by rfl) ⟨324041, by rfl⟩ : syracuseStep 1728221 = 648083) (by norm_num)
theorem B1728245 : Blo 1148636 1728245 := bbase (se 5 (by rfl) ⟨81011, by rfl⟩ : syracuseStep 1728245 = 162023) (by norm_num)
theorem B1728269 : Blo 1148636 1728269 := bbase (se 3 (by rfl) ⟨324050, by rfl⟩ : syracuseStep 1728269 = 648101) (by norm_num)
theorem B1728293 : Blo 1148636 1728293 := bbase (se 4 (by rfl) ⟨162027, by rfl⟩ : syracuseStep 1728293 = 324055) (by norm_num)
theorem B1662781 : Blo 1148636 1662781 := bbase (se 3 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 1662781 = 623543) (by norm_num)
theorem B1728317 : Blo 1148636 1728317 := bbase (se 3 (by rfl) ⟨324059, by rfl⟩ : syracuseStep 1728317 = 648119) (by norm_num)
theorem B1728341 : Blo 1148636 1728341 := bbase (se 9 (by rfl) ⟨5063, by rfl⟩ : syracuseStep 1728341 = 10127) (by norm_num)
theorem B1728365 : Blo 1148636 1728365 := bbase (se 3 (by rfl) ⟨324068, by rfl⟩ : syracuseStep 1728365 = 648137) (by norm_num)
theorem B2908021 : Blo 1148636 2908021 := bbase (se 5 (by rfl) ⟨136313, by rfl⟩ : syracuseStep 2908021 = 272627) (by norm_num)
theorem B1728389 : Blo 1148636 1728389 := bbase (se 4 (by rfl) ⟨162036, by rfl⟩ : syracuseStep 1728389 = 324073) (by norm_num)
theorem B1728413 : Blo 1148636 1728413 := bbase (se 3 (by rfl) ⟨324077, by rfl⟩ : syracuseStep 1728413 = 648155) (by norm_num)
theorem B1728437 : Blo 1148636 1728437 := bbase (se 5 (by rfl) ⟨81020, by rfl⟩ : syracuseStep 1728437 = 162041) (by norm_num)
theorem B1728461 : Blo 1148636 1728461 := bbase (se 3 (by rfl) ⟨324086, by rfl⟩ : syracuseStep 1728461 = 648173) (by norm_num)
theorem B2908133 : Blo 1148636 2908133 := bbase (se 4 (by rfl) ⟨272637, by rfl⟩ : syracuseStep 2908133 = 545275) (by norm_num)
theorem B1728485 : Blo 1148636 1728485 := bbase (se 4 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 1728485 = 324091) (by norm_num)
theorem B1728509 : Blo 1148636 1728509 := bbase (se 3 (by rfl) ⟨324095, by rfl⟩ : syracuseStep 1728509 = 648191) (by norm_num)
theorem B1728533 : Blo 1148636 1728533 := bbase (se 6 (by rfl) ⟨40512, by rfl⟩ : syracuseStep 1728533 = 81025) (by norm_num)
theorem B1400857 : Blo 1148636 1400857 := bbase (se 2 (by rfl) ⟨525321, by rfl⟩ : syracuseStep 1400857 = 1050643) (by norm_num)
theorem B1728557 : Blo 1148636 1728557 := bbase (se 3 (by rfl) ⟨324104, by rfl⟩ : syracuseStep 1728557 = 648209) (by norm_num)
theorem B1728581 : Blo 1148636 1728581 := bbase (se 4 (by rfl) ⟨162054, by rfl⟩ : syracuseStep 1728581 = 324109) (by norm_num)
theorem B1728605 : Blo 1148636 1728605 := bbase (se 3 (by rfl) ⟨324113, by rfl⟩ : syracuseStep 1728605 = 648227) (by norm_num)
theorem B1728629 : Blo 1148636 1728629 := bbase (se 5 (by rfl) ⟨81029, by rfl⟩ : syracuseStep 1728629 = 162059) (by norm_num)
theorem B1728653 : Blo 1148636 1728653 := bbase (se 3 (by rfl) ⟨324122, by rfl⟩ : syracuseStep 1728653 = 648245) (by norm_num)
theorem B15949973 : Blo 1148636 15949973 := bbase (se 6 (by rfl) ⟨373827, by rfl⟩ : syracuseStep 15949973 = 747655) (by norm_num)
theorem B2908325 : Blo 1148636 2908325 := bbase (se 4 (by rfl) ⟨272655, by rfl⟩ : syracuseStep 2908325 = 545311) (by norm_num)
theorem B1728677 : Blo 1148636 1728677 := bbase (se 4 (by rfl) ⟨162063, by rfl⟩ : syracuseStep 1728677 = 324127) (by norm_num)
theorem B1728701 : Blo 1148636 1728701 := bbase (se 3 (by rfl) ⟨324131, by rfl⟩ : syracuseStep 1728701 = 648263) (by norm_num)
theorem B5824709 : Blo 1148636 5824709 := bbase (se 4 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 5824709 = 1092133) (by norm_num)
theorem B1728725 : Blo 1148636 1728725 := bbase (se 7 (by rfl) ⟨20258, by rfl⟩ : syracuseStep 1728725 = 40517) (by norm_num)
theorem B1728749 : Blo 1148636 1728749 := bbase (se 3 (by rfl) ⟨324140, by rfl⟩ : syracuseStep 1728749 = 648281) (by norm_num)
theorem B1728773 : Blo 1148636 1728773 := bbase (se 4 (by rfl) ⟨162072, by rfl⟩ : syracuseStep 1728773 = 324145) (by norm_num)
theorem B14180629 : Blo 1148636 14180629 := bbase (se 6 (by rfl) ⟨332358, by rfl⟩ : syracuseStep 14180629 = 664717) (by norm_num)
theorem B1728797 : Blo 1148636 1728797 := bbase (se 3 (by rfl) ⟨324149, by rfl⟩ : syracuseStep 1728797 = 648299) (by norm_num)
theorem B1728821 : Blo 1148636 1728821 := bbase (se 5 (by rfl) ⟨81038, by rfl⟩ : syracuseStep 1728821 = 162077) (by norm_num)
theorem B1663301 : Blo 1148636 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B1728845 : Blo 1148636 1728845 := bbase (se 3 (by rfl) ⟨324158, by rfl⟩ : syracuseStep 1728845 = 648317) (by norm_num)
theorem B1728869 : Blo 1148636 1728869 := bbase (se 4 (by rfl) ⟨162081, by rfl⟩ : syracuseStep 1728869 = 324163) (by norm_num)
theorem B1728893 : Blo 1148636 1728893 := bbase (se 3 (by rfl) ⟨324167, by rfl⟩ : syracuseStep 1728893 = 648335) (by norm_num)
theorem B2187661 : Blo 1148636 2187661 := bbase (se 3 (by rfl) ⟨410186, by rfl⟩ : syracuseStep 2187661 = 820373) (by norm_num)
theorem B1728917 : Blo 1148636 1728917 := bbase (se 6 (by rfl) ⟨40521, by rfl⟩ : syracuseStep 1728917 = 81043) (by norm_num)
theorem B1728941 : Blo 1148636 1728941 := bbase (se 3 (by rfl) ⟨324176, by rfl⟩ : syracuseStep 1728941 = 648353) (by norm_num)
theorem B2908669 : Blo 1148636 2908669 := bbase (se 3 (by rfl) ⟨545375, by rfl⟩ : syracuseStep 2908669 = 1090751) (by norm_num)
theorem B2187805 : Blo 1148636 2187805 := bbase (se 3 (by rfl) ⟨410213, by rfl⟩ : syracuseStep 2187805 = 820427) (by norm_num)
theorem B2908781 : Blo 1148636 2908781 := bbase (se 3 (by rfl) ⟨545396, by rfl⟩ : syracuseStep 2908781 = 1090793) (by norm_num)
theorem B2187965 : Blo 1148636 2187965 := bbase (se 3 (by rfl) ⟨410243, by rfl⟩ : syracuseStep 2187965 = 820487) (by norm_num)
theorem B8282837 : Blo 1148636 8282837 := bbase (se 7 (by rfl) ⟨97064, by rfl⟩ : syracuseStep 8282837 = 194129) (by norm_num)
theorem B4907749 : Blo 1148636 4907749 := bbase (se 4 (by rfl) ⟨460101, by rfl⟩ : syracuseStep 4907749 = 920203) (by norm_num)
theorem B4907765 : Blo 1148636 4907765 := bbase (se 5 (by rfl) ⟨230051, by rfl⟩ : syracuseStep 4907765 = 460103) (by norm_num)
theorem B2908973 : Blo 1148636 2908973 := bbase (se 3 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 2908973 = 1090865) (by norm_num)
theorem B2188109 : Blo 1148636 2188109 := bbase (se 3 (by rfl) ⟨410270, by rfl⟩ : syracuseStep 2188109 = 820541) (by norm_num)
theorem B1795061 : Blo 1148636 1795061 := bbase (se 5 (by rfl) ⟨84143, by rfl⟩ : syracuseStep 1795061 = 168287) (by norm_num)
theorem B2909317 : Blo 1148636 2909317 := bbase (se 4 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 2909317 = 545497) (by norm_num)
theorem B6546581 : Blo 1148636 6546581 := bbase (se 6 (by rfl) ⟨153435, by rfl⟩ : syracuseStep 6546581 = 306871) (by norm_num)
theorem B1991861 : Blo 1148636 1991861 := bbase (se 5 (by rfl) ⟨93368, by rfl⟩ : syracuseStep 1991861 = 186737) (by norm_num)
theorem B2909429 : Blo 1148636 2909429 := bbase (se 5 (by rfl) ⟨136379, by rfl⟩ : syracuseStep 2909429 = 272759) (by norm_num)
theorem B1402181 : Blo 1148636 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B2909621 : Blo 1148636 2909621 := bbase (se 5 (by rfl) ⟨136388, by rfl⟩ : syracuseStep 2909621 = 272777) (by norm_num)
theorem B5826005 : Blo 1148636 5826005 := bbase (se 7 (by rfl) ⟨68273, by rfl⟩ : syracuseStep 5826005 = 136547) (by norm_num)
theorem B7366261 : Blo 1148636 7366261 := bbase (se 5 (by rfl) ⟨345293, by rfl⟩ : syracuseStep 7366261 = 690587) (by norm_num)
theorem B2909965 : Blo 1148636 2909965 := bbase (se 3 (by rfl) ⟨545618, by rfl⟩ : syracuseStep 2909965 = 1091237) (by norm_num)
theorem B1664869 : Blo 1148636 1664869 := bbase (se 4 (by rfl) ⟨156081, by rfl⟩ : syracuseStep 1664869 = 312163) (by norm_num)
theorem B2910077 : Blo 1148636 2910077 := bbase (se 3 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 2910077 = 1091279) (by norm_num)
theorem B2910269 : Blo 1148636 2910269 := bbase (se 3 (by rfl) ⟨545675, by rfl⟩ : syracuseStep 2910269 = 1091351) (by norm_num)
theorem B3271013 : Blo 1148636 3271013 := bbase (se 4 (by rfl) ⟨306657, by rfl⟩ : syracuseStep 3271013 = 613315) (by norm_num)
theorem B2910613 : Blo 1148636 2910613 := bbase (se 6 (by rfl) ⟨68217, by rfl⟩ : syracuseStep 2910613 = 136435) (by norm_num)
theorem B2910725 : Blo 1148636 2910725 := bbase (se 4 (by rfl) ⟨272880, by rfl⟩ : syracuseStep 2910725 = 545761) (by norm_num)
theorem B3271205 : Blo 1148636 3271205 := bbase (se 4 (by rfl) ⟨306675, by rfl⟩ : syracuseStep 3271205 = 613351) (by norm_num)
theorem B4549157 : Blo 1148636 4549157 := bbase (se 4 (by rfl) ⟨426483, by rfl⟩ : syracuseStep 4549157 = 852967) (by norm_num)
theorem B2910917 : Blo 1148636 2910917 := bbase (se 4 (by rfl) ⟨272898, by rfl⟩ : syracuseStep 2910917 = 545797) (by norm_num)
theorem B5827301 : Blo 1148636 5827301 := bbase (se 4 (by rfl) ⟨546309, by rfl⟩ : syracuseStep 5827301 = 1092619) (by norm_num)
theorem B11070229 : Blo 1148636 11070229 := bbase (se 6 (by rfl) ⟨259458, by rfl⟩ : syracuseStep 11070229 = 518917) (by norm_num)
theorem B3107621 : Blo 1148636 3107621 := bbase (se 4 (by rfl) ⟨291339, by rfl⟩ : syracuseStep 3107621 = 582679) (by norm_num)
theorem B4910021 : Blo 1148636 4910021 := bbase (se 4 (by rfl) ⟨460314, by rfl⟩ : syracuseStep 4910021 = 920629) (by norm_num)
theorem B2911261 : Blo 1148636 2911261 := bbase (se 3 (by rfl) ⟨545861, by rfl⟩ : syracuseStep 2911261 = 1091723) (by norm_num)
theorem B2911373 : Blo 1148636 2911373 := bbase (se 3 (by rfl) ⟨545882, by rfl⟩ : syracuseStep 2911373 = 1091765) (by norm_num)
theorem B17689877 : Blo 1148636 17689877 := bbase (se 6 (by rfl) ⟨414606, by rfl⟩ : syracuseStep 17689877 = 829213) (by norm_num)
theorem B6548789 : Blo 1148636 6548789 := bbase (se 5 (by rfl) ⟨306974, by rfl⟩ : syracuseStep 6548789 = 613949) (by norm_num)
theorem B2911565 : Blo 1148636 2911565 := bbase (se 3 (by rfl) ⟨545918, by rfl⟩ : syracuseStep 2911565 = 1091837) (by norm_num)
theorem B3272197 : Blo 1148636 3272197 := bbase (se 4 (by rfl) ⟨306768, by rfl⟩ : syracuseStep 3272197 = 613537) (by norm_num)
theorem B8744597 : Blo 1148636 8744597 := bbase (se 6 (by rfl) ⟨204951, by rfl⟩ : syracuseStep 8744597 = 409903) (by norm_num)
theorem B2911909 : Blo 1148636 2911909 := bbase (se 4 (by rfl) ⟨272991, by rfl⟩ : syracuseStep 2911909 = 545983) (by norm_num)
theorem B10481429 : Blo 1148636 10481429 := bbase (se 6 (by rfl) ⟨245658, by rfl⟩ : syracuseStep 10481429 = 491317) (by norm_num)
theorem B2912021 : Blo 1148636 2912021 := bbase (se 6 (by rfl) ⟨68250, by rfl⟩ : syracuseStep 2912021 = 136501) (by norm_num)
theorem B2584493 : Blo 1148636 2584493 := bbase (se 3 (by rfl) ⟨484592, by rfl⟩ : syracuseStep 2584493 = 969185) (by norm_num)
theorem B2912213 : Blo 1148636 2912213 := bbase (se 7 (by rfl) ⟨34127, by rfl⟩ : syracuseStep 2912213 = 68255) (by norm_num)
theorem B2584565 : Blo 1148636 2584565 := bbase (se 5 (by rfl) ⟨121151, by rfl⟩ : syracuseStep 2584565 = 242303) (by norm_num)
theorem B5828597 : Blo 1148636 5828597 := bbase (se 5 (by rfl) ⟨273215, by rfl⟩ : syracuseStep 5828597 = 546431) (by norm_num)
theorem B2584637 : Blo 1148636 2584637 := bbase (se 3 (by rfl) ⟨484619, by rfl⟩ : syracuseStep 2584637 = 969239) (by norm_num)
theorem B2584709 : Blo 1148636 2584709 := bbase (se 4 (by rfl) ⟨242316, by rfl⟩ : syracuseStep 2584709 = 484633) (by norm_num)
theorem B5533829 : Blo 1148636 5533829 := bbase (se 4 (by rfl) ⟨518796, by rfl⟩ : syracuseStep 5533829 = 1037593) (by norm_num)
theorem B2584781 : Blo 1148636 2584781 := bbase (se 3 (by rfl) ⟨484646, by rfl⟩ : syracuseStep 2584781 = 969293) (by norm_num)
theorem B3502325 : Blo 1148636 3502325 := bbase (se 5 (by rfl) ⟨164171, by rfl⟩ : syracuseStep 3502325 = 328343) (by norm_num)
theorem B2584853 : Blo 1148636 2584853 := bbase (se 6 (by rfl) ⟨60582, by rfl⟩ : syracuseStep 2584853 = 121165) (by norm_num)
theorem B3502373 : Blo 1148636 3502373 := bbase (se 4 (by rfl) ⟨328347, by rfl⟩ : syracuseStep 3502373 = 656695) (by norm_num)
theorem B2912557 : Blo 1148636 2912557 := bbase (se 3 (by rfl) ⟨546104, by rfl⟩ : syracuseStep 2912557 = 1092209) (by norm_num)
theorem B2584925 : Blo 1148636 2584925 := bbase (se 3 (by rfl) ⟨484673, by rfl⟩ : syracuseStep 2584925 = 969347) (by norm_num)
theorem B2453917 : Blo 1148636 2453917 := bbase (se 3 (by rfl) ⟨460109, by rfl⟩ : syracuseStep 2453917 = 920219) (by norm_num)
theorem B2912669 : Blo 1148636 2912669 := bbase (se 3 (by rfl) ⟨546125, by rfl⟩ : syracuseStep 2912669 = 1092251) (by norm_num)
theorem B2584997 : Blo 1148636 2584997 := bbase (se 4 (by rfl) ⟨242343, by rfl⟩ : syracuseStep 2584997 = 484687) (by norm_num)
theorem B2585069 : Blo 1148636 2585069 := bbase (se 3 (by rfl) ⟨484700, by rfl⟩ : syracuseStep 2585069 = 969401) (by norm_num)
theorem B2585141 : Blo 1148636 2585141 := bbase (se 5 (by rfl) ⟨121178, by rfl⟩ : syracuseStep 2585141 = 242357) (by norm_num)
theorem B3273301 : Blo 1148636 3273301 := bbase (se 8 (by rfl) ⟨19179, by rfl⟩ : syracuseStep 3273301 = 38359) (by norm_num)
theorem B2912861 : Blo 1148636 2912861 := bbase (se 3 (by rfl) ⟨546161, by rfl⟩ : syracuseStep 2912861 = 1092323) (by norm_num)
theorem B2585213 : Blo 1148636 2585213 := bbase (se 3 (by rfl) ⟨484727, by rfl⟩ : syracuseStep 2585213 = 969455) (by norm_num)
theorem B2486965 : Blo 1148636 2486965 := bbase (se 5 (by rfl) ⟨116576, by rfl⟩ : syracuseStep 2486965 = 233153) (by norm_num)
theorem B2585285 : Blo 1148636 2585285 := bbase (se 4 (by rfl) ⟨242370, by rfl⟩ : syracuseStep 2585285 = 484741) (by norm_num)
theorem B8418005 : Blo 1148636 8418005 := bbase (se 7 (by rfl) ⟨98648, by rfl⟩ : syracuseStep 8418005 = 197297) (by norm_num)
theorem B2585357 : Blo 1148636 2585357 := bbase (se 3 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 2585357 = 969509) (by norm_num)
theorem B2454293 : Blo 1148636 2454293 := bbase (se 6 (by rfl) ⟨57522, by rfl⟩ : syracuseStep 2454293 = 115045) (by norm_num)
theorem B2585429 : Blo 1148636 2585429 := bbase (se 9 (by rfl) ⟨7574, by rfl⟩ : syracuseStep 2585429 = 15149) (by norm_num)
theorem B2585501 : Blo 1148636 2585501 := bbase (se 3 (by rfl) ⟨484781, by rfl⟩ : syracuseStep 2585501 = 969563) (by norm_num)
theorem B2913205 : Blo 1148636 2913205 := bbase (se 5 (by rfl) ⟨136556, by rfl⟩ : syracuseStep 2913205 = 273113) (by norm_num)
theorem B2585573 : Blo 1148636 2585573 := bbase (se 4 (by rfl) ⟨242397, by rfl⟩ : syracuseStep 2585573 = 484795) (by norm_num)
theorem B2913317 : Blo 1148636 2913317 := bbase (se 4 (by rfl) ⟨273123, by rfl⟩ : syracuseStep 2913317 = 546247) (by norm_num)
theorem B2585645 : Blo 1148636 2585645 := bbase (se 3 (by rfl) ⟨484808, by rfl⟩ : syracuseStep 2585645 = 969617) (by norm_num)
theorem B2585717 : Blo 1148636 2585717 := bbase (se 5 (by rfl) ⟨121205, by rfl⟩ : syracuseStep 2585717 = 242411) (by norm_num)
theorem B2585789 : Blo 1148636 2585789 := bbase (se 3 (by rfl) ⟨484835, by rfl⟩ : syracuseStep 2585789 = 969671) (by norm_num)
theorem B2913509 : Blo 1148636 2913509 := bbase (se 4 (by rfl) ⟨273141, by rfl⟩ : syracuseStep 2913509 = 546283) (by norm_num)
theorem B1635557 : Blo 1148636 1635557 := bbase (se 4 (by rfl) ⟨153333, by rfl⟩ : syracuseStep 1635557 = 306667) (by norm_num)
theorem B2585861 : Blo 1148636 2585861 := bbase (se 4 (by rfl) ⟨242424, by rfl⟩ : syracuseStep 2585861 = 484849) (by norm_num)
theorem B5829893 : Blo 1148636 5829893 := bbase (se 4 (by rfl) ⟨546552, by rfl⟩ : syracuseStep 5829893 = 1093105) (by norm_num)
theorem B2585933 : Blo 1148636 2585933 := bbase (se 3 (by rfl) ⟨484862, by rfl⟩ : syracuseStep 2585933 = 969725) (by norm_num)
theorem B2586005 : Blo 1148636 2586005 := bbase (se 6 (by rfl) ⟨60609, by rfl⟩ : syracuseStep 2586005 = 121219) (by norm_num)
theorem B2586077 : Blo 1148636 2586077 := bbase (se 3 (by rfl) ⟨484889, by rfl⟩ : syracuseStep 2586077 = 969779) (by norm_num)
theorem B2586149 : Blo 1148636 2586149 := bbase (se 4 (by rfl) ⟨242451, by rfl⟩ : syracuseStep 2586149 = 484903) (by norm_num)
theorem B2913853 : Blo 1148636 2913853 := bbase (se 3 (by rfl) ⟨546347, by rfl⟩ : syracuseStep 2913853 = 1092695) (by norm_num)
theorem B2586221 : Blo 1148636 2586221 := bbase (se 3 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 2586221 = 969833) (by norm_num)
theorem B2913965 : Blo 1148636 2913965 := bbase (se 3 (by rfl) ⟨546368, by rfl⟩ : syracuseStep 2913965 = 1092737) (by norm_num)
theorem B2487989 : Blo 1148636 2487989 := bbase (se 5 (by rfl) ⟨116624, by rfl⟩ : syracuseStep 2487989 = 233249) (by norm_num)
theorem B2586293 : Blo 1148636 2586293 := bbase (se 5 (by rfl) ⟨121232, by rfl⟩ : syracuseStep 2586293 = 242465) (by norm_num)
theorem B2586365 : Blo 1148636 2586365 := bbase (se 3 (by rfl) ⟨484943, by rfl⟩ : syracuseStep 2586365 = 969887) (by norm_num)
theorem B2586437 : Blo 1148636 2586437 := bbase (se 4 (by rfl) ⟨242478, by rfl⟩ : syracuseStep 2586437 = 484957) (by norm_num)
theorem B2914157 : Blo 1148636 2914157 := bbase (se 3 (by rfl) ⟨546404, by rfl⟩ : syracuseStep 2914157 = 1092809) (by norm_num)
theorem B2586509 : Blo 1148636 2586509 := bbase (se 3 (by rfl) ⟨484970, by rfl⟩ : syracuseStep 2586509 = 969941) (by norm_num)
theorem B1636309 : Blo 1148636 1636309 := bbase (se 7 (by rfl) ⟨19175, by rfl⟩ : syracuseStep 1636309 = 38351) (by norm_num)
theorem B2586581 : Blo 1148636 2586581 := bbase (se 7 (by rfl) ⟨30311, by rfl⟩ : syracuseStep 2586581 = 60623) (by norm_num)
theorem B15759317 : Blo 1148636 15759317 := bbase (se 7 (by rfl) ⟨184679, by rfl⟩ : syracuseStep 15759317 = 369359) (by norm_num)
theorem B2488333 : Blo 1148636 2488333 := bbase (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) (by norm_num)
theorem B2586653 : Blo 1148636 2586653 := bbase (se 3 (by rfl) ⟨484997, by rfl⟩ : syracuseStep 2586653 = 969995) (by norm_num)
theorem B3274805 : Blo 1148636 3274805 := bbase (se 5 (by rfl) ⟨153506, by rfl⟩ : syracuseStep 3274805 = 307013) (by norm_num)
theorem B2586725 : Blo 1148636 2586725 := bbase (se 4 (by rfl) ⟨242505, by rfl⟩ : syracuseStep 2586725 = 485011) (by norm_num)
theorem B2586797 : Blo 1148636 2586797 := bbase (se 3 (by rfl) ⟨485024, by rfl⟩ : syracuseStep 2586797 = 970049) (by norm_num)
theorem B2914501 : Blo 1148636 2914501 := bbase (se 4 (by rfl) ⟨273234, by rfl⟩ : syracuseStep 2914501 = 546469) (by norm_num)
theorem B2586869 : Blo 1148636 2586869 := bbase (se 5 (by rfl) ⟨121259, by rfl⟩ : syracuseStep 2586869 = 242519) (by norm_num)
theorem B2914613 : Blo 1148636 2914613 := bbase (se 5 (by rfl) ⟨136622, by rfl⟩ : syracuseStep 2914613 = 273245) (by norm_num)
theorem B2586941 : Blo 1148636 2586941 := bbase (se 3 (by rfl) ⟨485051, by rfl⟩ : syracuseStep 2586941 = 970103) (by norm_num)
theorem B2455933 : Blo 1148636 2455933 := bbase (se 3 (by rfl) ⟨460487, by rfl⟩ : syracuseStep 2455933 = 920975) (by norm_num)
theorem B2587013 : Blo 1148636 2587013 := bbase (se 4 (by rfl) ⟨242532, by rfl⟩ : syracuseStep 2587013 = 485065) (by norm_num)
theorem B2587085 : Blo 1148636 2587085 := bbase (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) (by norm_num)
theorem B2914805 : Blo 1148636 2914805 := bbase (se 5 (by rfl) ⟨136631, by rfl⟩ : syracuseStep 2914805 = 273263) (by norm_num)
theorem B2587157 : Blo 1148636 2587157 := bbase (se 6 (by rfl) ⟨60636, by rfl⟩ : syracuseStep 2587157 = 121273) (by norm_num)
theorem B5831189 : Blo 1148636 5831189 := bbase (se 6 (by rfl) ⟨136668, by rfl⟩ : syracuseStep 5831189 = 273337) (by norm_num)
theorem B2587229 : Blo 1148636 2587229 := bbase (se 3 (by rfl) ⟨485105, by rfl⟩ : syracuseStep 2587229 = 970211) (by norm_num)
theorem B2587301 : Blo 1148636 2587301 := bbase (se 4 (by rfl) ⟨242559, by rfl⟩ : syracuseStep 2587301 = 485119) (by norm_num)
theorem B1637101 : Blo 1148636 1637101 := bbase (se 3 (by rfl) ⟨306956, by rfl⟩ : syracuseStep 1637101 = 613913) (by norm_num)
theorem B2587373 : Blo 1148636 2587373 := bbase (se 3 (by rfl) ⟨485132, by rfl⟩ : syracuseStep 2587373 = 970265) (by norm_num)
theorem B2587445 : Blo 1148636 2587445 := bbase (se 5 (by rfl) ⟨121286, by rfl⟩ : syracuseStep 2587445 = 242573) (by norm_num)
theorem B2915149 : Blo 1148636 2915149 := bbase (se 3 (by rfl) ⟨546590, by rfl⟩ : syracuseStep 2915149 = 1093181) (by norm_num)
theorem B5536613 : Blo 1148636 5536613 := bbase (se 4 (by rfl) ⟨519057, by rfl⟩ : syracuseStep 5536613 = 1038115) (by norm_num)
theorem B11074421 : Blo 1148636 11074421 := bbase (se 5 (by rfl) ⟨519113, by rfl⟩ : syracuseStep 11074421 = 1038227) (by norm_num)
theorem B2587517 : Blo 1148636 2587517 := bbase (se 3 (by rfl) ⟨485159, by rfl⟩ : syracuseStep 2587517 = 970319) (by norm_num)
theorem B4914053 : Blo 1148636 4914053 := bbase (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) (by norm_num)
theorem B2915261 : Blo 1148636 2915261 := bbase (se 3 (by rfl) ⟨546611, by rfl⟩ : syracuseStep 2915261 = 1093223) (by norm_num)
theorem B2587589 : Blo 1148636 2587589 := bbase (se 4 (by rfl) ⟨242586, by rfl⟩ : syracuseStep 2587589 = 485173) (by norm_num)
theorem B2587661 : Blo 1148636 2587661 := bbase (se 3 (by rfl) ⟨485186, by rfl⟩ : syracuseStep 2587661 = 970373) (by norm_num)
theorem B1637437 : Blo 1148636 1637437 := bbase (se 3 (by rfl) ⟨307019, by rfl⟩ : syracuseStep 1637437 = 614039) (by norm_num)
theorem B2587733 : Blo 1148636 2587733 := bbase (se 8 (by rfl) ⟨15162, by rfl⟩ : syracuseStep 2587733 = 30325) (by norm_num)
theorem B2915453 : Blo 1148636 2915453 := bbase (se 3 (by rfl) ⟨546647, by rfl⟩ : syracuseStep 2915453 = 1093295) (by norm_num)
theorem B2587805 : Blo 1148636 2587805 := bbase (se 3 (by rfl) ⟨485213, by rfl⟩ : syracuseStep 2587805 = 970427) (by norm_num)
theorem B2587877 : Blo 1148636 2587877 := bbase (se 4 (by rfl) ⟨242613, by rfl⟩ : syracuseStep 2587877 = 485227) (by norm_num)
theorem B2456821 : Blo 1148636 2456821 := bbase (se 5 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 2456821 = 230327) (by norm_num)
theorem B1637653 : Blo 1148636 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B2587949 : Blo 1148636 2587949 := bbase (se 3 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 2587949 = 970481) (by norm_num)
theorem B2588021 : Blo 1148636 2588021 := bbase (se 5 (by rfl) ⟨121313, by rfl⟩ : syracuseStep 2588021 = 242627) (by norm_num)
theorem B1867133 : Blo 1148636 1867133 := bbase (se 3 (by rfl) ⟨350087, by rfl⟩ : syracuseStep 1867133 = 700175) (by norm_num)
theorem B2588093 : Blo 1148636 2588093 := bbase (se 3 (by rfl) ⟨485267, by rfl⟩ : syracuseStep 2588093 = 970535) (by norm_num)
theorem B2915797 : Blo 1148636 2915797 := bbase (se 7 (by rfl) ⟨34169, by rfl⟩ : syracuseStep 2915797 = 68339) (by norm_num)
theorem B2588165 : Blo 1148636 2588165 := bbase (se 4 (by rfl) ⟨242640, by rfl⟩ : syracuseStep 2588165 = 485281) (by norm_num)
theorem B7372309 : Blo 1148636 7372309 := bbase (se 6 (by rfl) ⟨172788, by rfl⟩ : syracuseStep 7372309 = 345577) (by norm_num)
theorem B2915909 : Blo 1148636 2915909 := bbase (se 4 (by rfl) ⟨273366, by rfl⟩ : syracuseStep 2915909 = 546733) (by norm_num)
theorem B2588237 : Blo 1148636 2588237 := bbase (se 3 (by rfl) ⟨485294, by rfl⟩ : syracuseStep 2588237 = 970589) (by norm_num)
theorem B3276389 : Blo 1148636 3276389 := bbase (se 4 (by rfl) ⟨307161, by rfl⟩ : syracuseStep 3276389 = 614323) (by norm_num)
theorem B1638029 : Blo 1148636 1638029 := bbase (se 3 (by rfl) ⟨307130, by rfl⟩ : syracuseStep 1638029 = 614261) (by norm_num)
theorem B2588309 : Blo 1148636 2588309 := bbase (se 6 (by rfl) ⟨60663, by rfl⟩ : syracuseStep 2588309 = 121327) (by norm_num)
theorem B2588381 : Blo 1148636 2588381 := bbase (se 3 (by rfl) ⟨485321, by rfl⟩ : syracuseStep 2588381 = 970643) (by norm_num)
theorem B2457317 : Blo 1148636 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B2916101 : Blo 1148636 2916101 := bbase (se 4 (by rfl) ⟨273384, by rfl⟩ : syracuseStep 2916101 = 546769) (by norm_num)
theorem B2588453 : Blo 1148636 2588453 := bbase (se 4 (by rfl) ⟨242667, by rfl⟩ : syracuseStep 2588453 = 485335) (by norm_num)
theorem B5832485 : Blo 1148636 5832485 := bbase (se 4 (by rfl) ⟨546795, by rfl⟩ : syracuseStep 5832485 = 1093591) (by norm_num)
theorem B1474373 : Blo 1148636 1474373 := bbase (se 4 (by rfl) ⟨138222, by rfl⟩ : syracuseStep 1474373 = 276445) (by norm_num)
theorem B8290133 : Blo 1148636 8290133 := bbase (se 9 (by rfl) ⟨24287, by rfl⟩ : syracuseStep 8290133 = 48575) (by norm_num)
theorem B6225749 : Blo 1148636 6225749 := bbase (se 9 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 6225749 = 36479) (by norm_num)
theorem B2588525 : Blo 1148636 2588525 := bbase (se 3 (by rfl) ⟨485348, by rfl⟩ : syracuseStep 2588525 = 970697) (by norm_num)
theorem B1474481 : Blo 1148636 1474481 := bbase (se 2 (by rfl) ⟨552930, by rfl⟩ : syracuseStep 1474481 = 1105861) (by norm_num)
theorem B2588597 : Blo 1148636 2588597 := bbase (se 5 (by rfl) ⟨121340, by rfl⟩ : syracuseStep 2588597 = 242681) (by norm_num)
theorem B2588669 : Blo 1148636 2588669 := bbase (se 3 (by rfl) ⟨485375, by rfl⟩ : syracuseStep 2588669 = 970751) (by norm_num)
theorem B3276845 : Blo 1148636 3276845 := bstep (se 3 (by rfl) ⟨614408, by rfl⟩ : syracuseStep 3276845 = 1228817) B1228817
theorem B7471237 : Blo 1148636 7471237 := bstep (se 4 (by rfl) ⟨700428, by rfl⟩ : syracuseStep 7471237 = 1400857) B1400857
theorem B13992077 : Blo 1148636 13992077 := bstep (se 3 (by rfl) ⟨2623514, by rfl⟩ : syracuseStep 13992077 = 5247029) B5247029
theorem B2588849 : Blo 1148636 2588849 := bstep (se 2 (by rfl) ⟨970818, by rfl⟩ : syracuseStep 2588849 = 1941637) B1941637
theorem B2588867 : Blo 1148636 2588867 := bstep (se 1 (by rfl) ⟨1941650, by rfl⟩ : syracuseStep 2588867 = 3883301) B3883301
theorem B3277037 : Blo 1148636 3277037 := bstep (se 3 (by rfl) ⟨614444, by rfl⟩ : syracuseStep 3277037 = 1228889) B1228889
theorem B18907505 : Blo 1148636 18907505 := bstep (se 2 (by rfl) ⟨7090314, by rfl⟩ : syracuseStep 18907505 = 14180629) B14180629
theorem B1638787 : Blo 1148636 1638787 := bstep (se 1 (by rfl) ⟨1229090, by rfl⟩ : syracuseStep 1638787 = 2458181) B2458181
theorem B2458001 : Blo 1148636 2458001 := bstep (se 2 (by rfl) ⟨921750, by rfl⟩ : syracuseStep 2458001 = 1843501) B1843501
theorem B2589137 : Blo 1148636 2589137 := bstep (se 2 (by rfl) ⟨970926, by rfl⟩ : syracuseStep 2589137 = 1941853) B1941853
theorem B2589155 : Blo 1148636 2589155 := bstep (se 1 (by rfl) ⟨1941866, by rfl⟩ : syracuseStep 2589155 = 3883733) B3883733
theorem B1638883 : Blo 1148636 1638883 := bstep (se 1 (by rfl) ⟨1229162, by rfl⟩ : syracuseStep 1638883 = 2458325) B2458325
theorem B3932675 : Blo 1148636 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B2916881 : Blo 1148636 2916881 := bstep (se 2 (by rfl) ⟨1093830, by rfl⟩ : syracuseStep 2916881 = 2187661) B2187661
theorem B2916931 : Blo 1148636 2916931 := bstep (se 1 (by rfl) ⟨2187698, by rfl⟩ : syracuseStep 2916931 = 4375397) B4375397
theorem B14746211 : Blo 1148636 14746211 := bstep (se 1 (by rfl) ⟨11059658, by rfl⟩ : syracuseStep 14746211 = 22119317) B22119317
theorem B9339533 : Blo 1148636 9339533 := bstep (se 3 (by rfl) ⟨1751162, by rfl⟩ : syracuseStep 9339533 = 3502325) B3502325
theorem B1311379 : Blo 1148636 1311379 := bstep (se 1 (by rfl) ⟨983534, by rfl⟩ : syracuseStep 1311379 = 1967069) B1967069
theorem B6226595 : Blo 1148636 6226595 := bstep (se 1 (by rfl) ⟨4669946, by rfl⟩ : syracuseStep 6226595 = 9339893) B9339893
theorem B2917073 : Blo 1148636 2917073 := bstep (se 2 (by rfl) ⟨1093902, by rfl⟩ : syracuseStep 2917073 = 2187805) B2187805
theorem B2589425 : Blo 1148636 2589425 := bstep (se 2 (by rfl) ⟨971034, by rfl⟩ : syracuseStep 2589425 = 1942069) B1942069
theorem B5833457 : Blo 1148636 5833457 := bstep (se 2 (by rfl) ⟨2187546, by rfl⟩ : syracuseStep 5833457 = 4375093) B4375093
theorem B1311475 : Blo 1148636 1311475 := bstep (se 1 (by rfl) ⟨983606, by rfl⟩ : syracuseStep 1311475 = 1967213) B1967213
theorem B2589443 : Blo 1148636 2589443 := bstep (se 1 (by rfl) ⟨1942082, by rfl⟩ : syracuseStep 2589443 = 3884165) B3884165
theorem B9339661 : Blo 1148636 9339661 := bstep (se 3 (by rfl) ⟨1751186, by rfl⟩ : syracuseStep 9339661 = 3502373) B3502373
theorem B2622257 : Blo 1148636 2622257 := bstep (se 2 (by rfl) ⟨983346, by rfl⟩ : syracuseStep 2622257 = 1966693) B1966693
theorem B1966993 : Blo 1148636 1966993 := bstep (se 2 (by rfl) ⟨737622, by rfl⟩ : syracuseStep 1966993 = 1475245) B1475245
theorem B1639379 : Blo 1148636 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B2589713 : Blo 1148636 2589713 := bstep (se 2 (by rfl) ⟨971142, by rfl⟩ : syracuseStep 2589713 = 1942285) B1942285
theorem B2589731 : Blo 1148636 2589731 := bstep (se 1 (by rfl) ⟨1942298, by rfl⟩ : syracuseStep 2589731 = 3884597) B3884597
theorem B5604515 : Blo 1148636 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B3278029 : Blo 1148636 3278029 := bstep (se 3 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 3278029 = 1229261) B1229261
theorem B2590001 : Blo 1148636 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B2590019 : Blo 1148636 2590019 := bstep (se 1 (by rfl) ⟨1942514, by rfl⟩ : syracuseStep 2590019 = 3885029) B3885029
theorem B1967507 : Blo 1148636 1967507 := bstep (se 1 (by rfl) ⟨1475630, by rfl⟩ : syracuseStep 1967507 = 2951261) B2951261
theorem B6555077 : Blo 1148636 6555077 := bstep (se 4 (by rfl) ⟨614538, by rfl⟩ : syracuseStep 6555077 = 1229077) B1229077
theorem B4916771 : Blo 1148636 4916771 := bstep (se 1 (by rfl) ⟨3687578, by rfl⟩ : syracuseStep 4916771 = 7375157) B7375157
theorem B3114541 : Blo 1148636 3114541 := bstep (se 3 (by rfl) ⟨583976, by rfl⟩ : syracuseStep 3114541 = 1167953) B1167953
theorem B2590289 : Blo 1148636 2590289 := bstep (se 2 (by rfl) ⟨971358, by rfl⟩ : syracuseStep 2590289 = 1942717) B1942717
theorem B1640017 : Blo 1148636 1640017 := bstep (se 2 (by rfl) ⟨615006, by rfl⟩ : syracuseStep 1640017 = 1230013) B1230013
theorem B2590307 : Blo 1148636 2590307 := bstep (se 1 (by rfl) ⟨1942730, by rfl⟩ : syracuseStep 2590307 = 3885461) B3885461
theorem B3114605 : Blo 1148636 3114605 := bstep (se 3 (by rfl) ⟨583988, by rfl⟩ : syracuseStep 3114605 = 1167977) B1167977
theorem B13108877 : Blo 1148636 13108877 := bstep (se 3 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 13108877 = 4915829) B4915829
theorem B1148643 : Blo 1148636 1148643 := bstep (se 1 (by rfl) ⟨861482, by rfl⟩ : syracuseStep 1148643 = 1722965) B1722965
theorem B3114737 : Blo 1148636 3114737 := bstep (se 2 (by rfl) ⟨1168026, by rfl⟩ : syracuseStep 3114737 = 2336053) B2336053
theorem B1148659 : Blo 1148636 1148659 := bstep (se 1 (by rfl) ⟨861494, by rfl⟩ : syracuseStep 1148659 = 1722989) B1722989
theorem B1148675 : Blo 1148636 1148675 := bstep (se 1 (by rfl) ⟨861506, by rfl⟩ : syracuseStep 1148675 = 1723013) B1723013
theorem B9832205 : Blo 1148636 9832205 := bstep (se 3 (by rfl) ⟨1843538, by rfl⟩ : syracuseStep 9832205 = 3687077) B3687077
theorem B1148691 : Blo 1148636 1148691 := bstep (se 1 (by rfl) ⟨861518, by rfl⟩ : syracuseStep 1148691 = 1723037) B1723037
theorem B1148707 : Blo 1148636 1148707 := bstep (se 1 (by rfl) ⟨861530, by rfl⟩ : syracuseStep 1148707 = 1723061) B1723061
theorem B1148723 : Blo 1148636 1148723 := bstep (se 1 (by rfl) ⟨861542, by rfl⟩ : syracuseStep 1148723 = 1723085) B1723085
theorem B1148739 : Blo 1148636 1148739 := bstep (se 1 (by rfl) ⟨861554, by rfl⟩ : syracuseStep 1148739 = 1723109) B1723109
theorem B1148755 : Blo 1148636 1148755 := bstep (se 1 (by rfl) ⟨861566, by rfl⟩ : syracuseStep 1148755 = 1723133) B1723133
theorem B1148771 : Blo 1148636 1148771 := bstep (se 1 (by rfl) ⟨861578, by rfl⟩ : syracuseStep 1148771 = 1723157) B1723157
theorem B2590577 : Blo 1148636 2590577 := bstep (se 2 (by rfl) ⟨971466, by rfl⟩ : syracuseStep 2590577 = 1942933) B1942933
theorem B1148787 : Blo 1148636 1148787 := bstep (se 1 (by rfl) ⟨861590, by rfl⟩ : syracuseStep 1148787 = 1723181) B1723181
theorem B1148803 : Blo 1148636 1148803 := bstep (se 1 (by rfl) ⟨861602, by rfl⟩ : syracuseStep 1148803 = 1723205) B1723205
theorem B2590595 : Blo 1148636 2590595 := bstep (se 1 (by rfl) ⟨1942946, by rfl⟩ : syracuseStep 2590595 = 3885893) B3885893
theorem B1148819 : Blo 1148636 1148819 := bstep (se 1 (by rfl) ⟨861614, by rfl⟩ : syracuseStep 1148819 = 1723229) B1723229
theorem B1640353 : Blo 1148636 1640353 := bstep (se 2 (by rfl) ⟨615132, by rfl⟩ : syracuseStep 1640353 = 1230265) B1230265
theorem B1148835 : Blo 1148636 1148835 := bstep (se 1 (by rfl) ⟨861626, by rfl⟩ : syracuseStep 1148835 = 1723253) B1723253
theorem B1148851 : Blo 1148636 1148851 := bstep (se 1 (by rfl) ⟨861638, by rfl⟩ : syracuseStep 1148851 = 1723277) B1723277
theorem B1148867 : Blo 1148636 1148867 := bstep (se 1 (by rfl) ⟨861650, by rfl⟩ : syracuseStep 1148867 = 1723301) B1723301
theorem B1148883 : Blo 1148636 1148883 := bstep (se 1 (by rfl) ⟨861662, by rfl⟩ : syracuseStep 1148883 = 1723325) B1723325
theorem B1148899 : Blo 1148636 1148899 := bstep (se 1 (by rfl) ⟨861674, by rfl⟩ : syracuseStep 1148899 = 1723349) B1723349
theorem B1148915 : Blo 1148636 1148915 := bstep (se 1 (by rfl) ⟨861686, by rfl⟩ : syracuseStep 1148915 = 1723373) B1723373
theorem B1148931 : Blo 1148636 1148931 := bstep (se 1 (by rfl) ⟨861698, by rfl⟩ : syracuseStep 1148931 = 1723397) B1723397
theorem B2656259 : Blo 1148636 2656259 := bstep (se 1 (by rfl) ⟨1992194, by rfl⟩ : syracuseStep 2656259 = 3984389) B3984389
theorem B1148947 : Blo 1148636 1148947 := bstep (se 1 (by rfl) ⟨861710, by rfl⟩ : syracuseStep 1148947 = 1723421) B1723421
theorem B1148963 : Blo 1148636 1148963 := bstep (se 1 (by rfl) ⟨861722, by rfl⟩ : syracuseStep 1148963 = 1723445) B1723445
theorem B1148979 : Blo 1148636 1148979 := bstep (se 1 (by rfl) ⟨861734, by rfl⟩ : syracuseStep 1148979 = 1723469) B1723469
theorem B1148995 : Blo 1148636 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B1149011 : Blo 1148636 1149011 := bstep (se 1 (by rfl) ⟨861758, by rfl⟩ : syracuseStep 1149011 = 1723517) B1723517
theorem B1149027 : Blo 1148636 1149027 := bstep (se 1 (by rfl) ⟨861770, by rfl⟩ : syracuseStep 1149027 = 1723541) B1723541
theorem B6555761 : Blo 1148636 6555761 := bstep (se 2 (by rfl) ⟨2458410, by rfl⟩ : syracuseStep 6555761 = 4916821) B4916821
theorem B1149043 : Blo 1148636 1149043 := bstep (se 1 (by rfl) ⟨861782, by rfl⟩ : syracuseStep 1149043 = 1723565) B1723565
theorem B1149059 : Blo 1148636 1149059 := bstep (se 1 (by rfl) ⟨861794, by rfl⟩ : syracuseStep 1149059 = 1723589) B1723589
theorem B2590865 : Blo 1148636 2590865 := bstep (se 2 (by rfl) ⟨971574, by rfl⟩ : syracuseStep 2590865 = 1943149) B1943149
theorem B1149075 : Blo 1148636 1149075 := bstep (se 1 (by rfl) ⟨861806, by rfl⟩ : syracuseStep 1149075 = 1723613) B1723613
theorem B1149091 : Blo 1148636 1149091 := bstep (se 1 (by rfl) ⟨861818, by rfl⟩ : syracuseStep 1149091 = 1723637) B1723637
theorem B2590883 : Blo 1148636 2590883 := bstep (se 1 (by rfl) ⟨1943162, by rfl⟩ : syracuseStep 2590883 = 3886325) B3886325
theorem B5834915 : Blo 1148636 5834915 := bstep (se 1 (by rfl) ⟨4376186, by rfl⟩ : syracuseStep 5834915 = 8752373) B8752373
theorem B1149107 : Blo 1148636 1149107 := bstep (se 1 (by rfl) ⟨861830, by rfl⟩ : syracuseStep 1149107 = 1723661) B1723661
theorem B1149123 : Blo 1148636 1149123 := bstep (se 1 (by rfl) ⟨861842, by rfl⟩ : syracuseStep 1149123 = 1723685) B1723685
theorem B1149139 : Blo 1148636 1149139 := bstep (se 1 (by rfl) ⟨861854, by rfl⟩ : syracuseStep 1149139 = 1723709) B1723709
theorem B1149155 : Blo 1148636 1149155 := bstep (se 1 (by rfl) ⟨861866, by rfl⟩ : syracuseStep 1149155 = 1723733) B1723733
theorem B3737827 : Blo 1148636 3737827 := bstep (se 1 (by rfl) ⟨2803370, by rfl⟩ : syracuseStep 3737827 = 5606741) B5606741
theorem B1149171 : Blo 1148636 1149171 := bstep (se 1 (by rfl) ⟨861878, by rfl⟩ : syracuseStep 1149171 = 1723757) B1723757
theorem B1149187 : Blo 1148636 1149187 := bstep (se 1 (by rfl) ⟨861890, by rfl⟩ : syracuseStep 1149187 = 1723781) B1723781
theorem B1149203 : Blo 1148636 1149203 := bstep (se 1 (by rfl) ⟨861902, by rfl⟩ : syracuseStep 1149203 = 1723805) B1723805
theorem B1149219 : Blo 1148636 1149219 := bstep (se 1 (by rfl) ⟨861914, by rfl⟩ : syracuseStep 1149219 = 1723829) B1723829
theorem B1149235 : Blo 1148636 1149235 := bstep (se 1 (by rfl) ⟨861926, by rfl⟩ : syracuseStep 1149235 = 1723853) B1723853
theorem B1149251 : Blo 1148636 1149251 := bstep (se 1 (by rfl) ⟨861938, by rfl⟩ : syracuseStep 1149251 = 1723877) B1723877
theorem B1149267 : Blo 1148636 1149267 := bstep (se 1 (by rfl) ⟨861950, by rfl⟩ : syracuseStep 1149267 = 1723901) B1723901
theorem B1149283 : Blo 1148636 1149283 := bstep (se 1 (by rfl) ⟨861962, by rfl⟩ : syracuseStep 1149283 = 1723925) B1723925
theorem B1149299 : Blo 1148636 1149299 := bstep (se 1 (by rfl) ⟨861974, by rfl⟩ : syracuseStep 1149299 = 1723949) B1723949
theorem B1149315 : Blo 1148636 1149315 := bstep (se 1 (by rfl) ⟨861986, by rfl⟩ : syracuseStep 1149315 = 1723973) B1723973
theorem B1149331 : Blo 1148636 1149331 := bstep (se 1 (by rfl) ⟨861998, by rfl⟩ : syracuseStep 1149331 = 1723997) B1723997
theorem B1149347 : Blo 1148636 1149347 := bstep (se 1 (by rfl) ⟨862010, by rfl⟩ : syracuseStep 1149347 = 1724021) B1724021
theorem B3115427 : Blo 1148636 3115427 := bstep (se 1 (by rfl) ⟨2336570, by rfl⟩ : syracuseStep 3115427 = 4673141) B4673141
theorem B2591153 : Blo 1148636 2591153 := bstep (se 2 (by rfl) ⟨971682, by rfl⟩ : syracuseStep 2591153 = 1943365) B1943365
theorem B1149363 : Blo 1148636 1149363 := bstep (se 1 (by rfl) ⟨862022, by rfl⟩ : syracuseStep 1149363 = 1724045) B1724045
theorem B1149379 : Blo 1148636 1149379 := bstep (se 1 (by rfl) ⟨862034, by rfl⟩ : syracuseStep 1149379 = 1724069) B1724069
theorem B2591171 : Blo 1148636 2591171 := bstep (se 1 (by rfl) ⟨1943378, by rfl⟩ : syracuseStep 2591171 = 3886757) B3886757
theorem B1149395 : Blo 1148636 1149395 := bstep (se 1 (by rfl) ⟨862046, by rfl⟩ : syracuseStep 1149395 = 1724093) B1724093
theorem B1149411 : Blo 1148636 1149411 := bstep (se 1 (by rfl) ⟨862058, by rfl⟩ : syracuseStep 1149411 = 1724117) B1724117
theorem B1640945 : Blo 1148636 1640945 := bstep (se 2 (by rfl) ⟨615354, by rfl⟩ : syracuseStep 1640945 = 1230709) B1230709
theorem B1149427 : Blo 1148636 1149427 := bstep (se 1 (by rfl) ⟨862070, by rfl⟩ : syracuseStep 1149427 = 1724141) B1724141
theorem B1149443 : Blo 1148636 1149443 := bstep (se 1 (by rfl) ⟨862082, by rfl⟩ : syracuseStep 1149443 = 1724165) B1724165
theorem B1149459 : Blo 1148636 1149459 := bstep (se 1 (by rfl) ⟨862094, by rfl⟩ : syracuseStep 1149459 = 1724189) B1724189
theorem B1149475 : Blo 1148636 1149475 := bstep (se 1 (by rfl) ⟨862106, by rfl⟩ : syracuseStep 1149475 = 1724213) B1724213
theorem B1149491 : Blo 1148636 1149491 := bstep (se 1 (by rfl) ⟨862118, by rfl⟩ : syracuseStep 1149491 = 1724237) B1724237
theorem B1149507 : Blo 1148636 1149507 := bstep (se 1 (by rfl) ⟨862130, by rfl⟩ : syracuseStep 1149507 = 1724261) B1724261
theorem B1149523 : Blo 1148636 1149523 := bstep (se 1 (by rfl) ⟨862142, by rfl⟩ : syracuseStep 1149523 = 1724285) B1724285
theorem B1149539 : Blo 1148636 1149539 := bstep (se 1 (by rfl) ⟨862154, by rfl⟩ : syracuseStep 1149539 = 1724309) B1724309
theorem B1149555 : Blo 1148636 1149555 := bstep (se 1 (by rfl) ⟨862166, by rfl⟩ : syracuseStep 1149555 = 1724333) B1724333
theorem B1149571 : Blo 1148636 1149571 := bstep (se 1 (by rfl) ⟨862178, by rfl⟩ : syracuseStep 1149571 = 1724357) B1724357
theorem B4786829 : Blo 1148636 4786829 := bstep (se 3 (by rfl) ⟨897530, by rfl⟩ : syracuseStep 4786829 = 1795061) B1795061
theorem B1149587 : Blo 1148636 1149587 := bstep (se 1 (by rfl) ⟨862190, by rfl⟩ : syracuseStep 1149587 = 1724381) B1724381
theorem B1149603 : Blo 1148636 1149603 := bstep (se 1 (by rfl) ⟨862202, by rfl⟩ : syracuseStep 1149603 = 1724405) B1724405
theorem B7867043 : Blo 1148636 7867043 := bstep (se 1 (by rfl) ⟨5900282, by rfl⟩ : syracuseStep 7867043 = 11800565) B11800565
theorem B1149619 : Blo 1148636 1149619 := bstep (se 1 (by rfl) ⟨862214, by rfl⟩ : syracuseStep 1149619 = 1724429) B1724429
theorem B1149635 : Blo 1148636 1149635 := bstep (se 1 (by rfl) ⟨862226, by rfl⟩ : syracuseStep 1149635 = 1724453) B1724453
theorem B2591441 : Blo 1148636 2591441 := bstep (se 2 (by rfl) ⟨971790, by rfl⟩ : syracuseStep 2591441 = 1943581) B1943581
theorem B1149651 : Blo 1148636 1149651 := bstep (se 1 (by rfl) ⟨862238, by rfl⟩ : syracuseStep 1149651 = 1724477) B1724477
theorem B1149667 : Blo 1148636 1149667 := bstep (se 1 (by rfl) ⟨862250, by rfl⟩ : syracuseStep 1149667 = 1724501) B1724501
theorem B2591459 : Blo 1148636 2591459 := bstep (se 1 (by rfl) ⟨1943594, by rfl⟩ : syracuseStep 2591459 = 3887189) B3887189
theorem B1149683 : Blo 1148636 1149683 := bstep (se 1 (by rfl) ⟨862262, by rfl⟩ : syracuseStep 1149683 = 1724525) B1724525
theorem B1149699 : Blo 1148636 1149699 := bstep (se 1 (by rfl) ⟨862274, by rfl⟩ : syracuseStep 1149699 = 1724549) B1724549
theorem B1149715 : Blo 1148636 1149715 := bstep (se 1 (by rfl) ⟨862286, by rfl⟩ : syracuseStep 1149715 = 1724573) B1724573
theorem B1149731 : Blo 1148636 1149731 := bstep (se 1 (by rfl) ⟨862298, by rfl⟩ : syracuseStep 1149731 = 1724597) B1724597
theorem B1149747 : Blo 1148636 1149747 := bstep (se 1 (by rfl) ⟨862310, by rfl⟩ : syracuseStep 1149747 = 1724621) B1724621
theorem B1149763 : Blo 1148636 1149763 := bstep (se 1 (by rfl) ⟨862322, by rfl⟩ : syracuseStep 1149763 = 1724645) B1724645
theorem B7867205 : Blo 1148636 7867205 := bstep (se 4 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 7867205 = 1475101) B1475101
theorem B1149779 : Blo 1148636 1149779 := bstep (se 1 (by rfl) ⟨862334, by rfl⟩ : syracuseStep 1149779 = 1724669) B1724669
theorem B1149795 : Blo 1148636 1149795 := bstep (se 1 (by rfl) ⟨862346, by rfl⟩ : syracuseStep 1149795 = 1724693) B1724693
theorem B1149811 : Blo 1148636 1149811 := bstep (se 1 (by rfl) ⟨862358, by rfl⟩ : syracuseStep 1149811 = 1724717) B1724717
theorem B1149827 : Blo 1148636 1149827 := bstep (se 1 (by rfl) ⟨862370, by rfl⟩ : syracuseStep 1149827 = 1724741) B1724741
theorem B3279761 : Blo 1148636 3279761 := bstep (se 2 (by rfl) ⟨1229910, by rfl⟩ : syracuseStep 3279761 = 2459821) B2459821
theorem B1149843 : Blo 1148636 1149843 := bstep (se 1 (by rfl) ⟨862382, by rfl⟩ : syracuseStep 1149843 = 1724765) B1724765
theorem B1149859 : Blo 1148636 1149859 := bstep (se 1 (by rfl) ⟨862394, by rfl⟩ : syracuseStep 1149859 = 1724789) B1724789
theorem B1149875 : Blo 1148636 1149875 := bstep (se 1 (by rfl) ⟨862406, by rfl⟩ : syracuseStep 1149875 = 1724813) B1724813
theorem B1149891 : Blo 1148636 1149891 := bstep (se 1 (by rfl) ⟨862418, by rfl⟩ : syracuseStep 1149891 = 1724837) B1724837
theorem B1149907 : Blo 1148636 1149907 := bstep (se 1 (by rfl) ⟨862430, by rfl⟩ : syracuseStep 1149907 = 1724861) B1724861
theorem B1149923 : Blo 1148636 1149923 := bstep (se 1 (by rfl) ⟨862442, by rfl⟩ : syracuseStep 1149923 = 1724885) B1724885
theorem B2591729 : Blo 1148636 2591729 := bstep (se 2 (by rfl) ⟨971898, by rfl⟩ : syracuseStep 2591729 = 1943797) B1943797
theorem B1149939 : Blo 1148636 1149939 := bstep (se 1 (by rfl) ⟨862454, by rfl⟩ : syracuseStep 1149939 = 1724909) B1724909
theorem B1149955 : Blo 1148636 1149955 := bstep (se 1 (by rfl) ⟨862466, by rfl⟩ : syracuseStep 1149955 = 1724933) B1724933
theorem B2591747 : Blo 1148636 2591747 := bstep (se 1 (by rfl) ⟨1943810, by rfl⟩ : syracuseStep 2591747 = 3887621) B3887621
theorem B1149971 : Blo 1148636 1149971 := bstep (se 1 (by rfl) ⟨862478, by rfl⟩ : syracuseStep 1149971 = 1724957) B1724957
theorem B1149987 : Blo 1148636 1149987 := bstep (se 1 (by rfl) ⟨862490, by rfl⟩ : syracuseStep 1149987 = 1724981) B1724981
theorem B1150003 : Blo 1148636 1150003 := bstep (se 1 (by rfl) ⟨862502, by rfl⟩ : syracuseStep 1150003 = 1725005) B1725005
theorem B1150019 : Blo 1148636 1150019 := bstep (se 1 (by rfl) ⟨862514, by rfl⟩ : syracuseStep 1150019 = 1725029) B1725029
theorem B3279953 : Blo 1148636 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B1150035 : Blo 1148636 1150035 := bstep (se 1 (by rfl) ⟨862526, by rfl⟩ : syracuseStep 1150035 = 1725053) B1725053
theorem B1150051 : Blo 1148636 1150051 := bstep (se 1 (by rfl) ⟨862538, by rfl⟩ : syracuseStep 1150051 = 1725077) B1725077
theorem B2460785 : Blo 1148636 2460785 := bstep (se 2 (by rfl) ⟨922794, by rfl⟩ : syracuseStep 2460785 = 1845589) B1845589
theorem B1150067 : Blo 1148636 1150067 := bstep (se 1 (by rfl) ⟨862550, by rfl⟩ : syracuseStep 1150067 = 1725101) B1725101
theorem B1150083 : Blo 1148636 1150083 := bstep (se 1 (by rfl) ⟨862562, by rfl⟩ : syracuseStep 1150083 = 1725125) B1725125
theorem B1772689 : Blo 1148636 1772689 := bstep (se 2 (by rfl) ⟨664758, by rfl⟩ : syracuseStep 1772689 = 1329517) B1329517
theorem B1150099 : Blo 1148636 1150099 := bstep (se 1 (by rfl) ⟨862574, by rfl⟩ : syracuseStep 1150099 = 1725149) B1725149
theorem B1313939 : Blo 1148636 1313939 := bstep (se 1 (by rfl) ⟨985454, by rfl⟩ : syracuseStep 1313939 = 1970909) B1970909
theorem B1150115 : Blo 1148636 1150115 := bstep (se 1 (by rfl) ⟨862586, by rfl⟩ : syracuseStep 1150115 = 1725173) B1725173
theorem B1150131 : Blo 1148636 1150131 := bstep (se 1 (by rfl) ⟨862598, by rfl⟩ : syracuseStep 1150131 = 1725197) B1725197
theorem B1150147 : Blo 1148636 1150147 := bstep (se 1 (by rfl) ⟨862610, by rfl⟩ : syracuseStep 1150147 = 1725221) B1725221
theorem B1150163 : Blo 1148636 1150163 := bstep (se 1 (by rfl) ⟨862622, by rfl⟩ : syracuseStep 1150163 = 1725245) B1725245
theorem B1150179 : Blo 1148636 1150179 := bstep (se 1 (by rfl) ⟨862634, by rfl⟩ : syracuseStep 1150179 = 1725269) B1725269
theorem B1150195 : Blo 1148636 1150195 := bstep (se 1 (by rfl) ⟨862646, by rfl⟩ : syracuseStep 1150195 = 1725293) B1725293
theorem B1150211 : Blo 1148636 1150211 := bstep (se 1 (by rfl) ⟨862658, by rfl⟩ : syracuseStep 1150211 = 1725317) B1725317
theorem B4361485 : Blo 1148636 4361485 := bstep (se 3 (by rfl) ⟨817778, by rfl⟩ : syracuseStep 4361485 = 1635557) B1635557
theorem B2592017 : Blo 1148636 2592017 := bstep (se 2 (by rfl) ⟨972006, by rfl⟩ : syracuseStep 2592017 = 1944013) B1944013
theorem B1150227 : Blo 1148636 1150227 := bstep (se 1 (by rfl) ⟨862670, by rfl⟩ : syracuseStep 1150227 = 1725341) B1725341
theorem B1150243 : Blo 1148636 1150243 := bstep (se 1 (by rfl) ⟨862682, by rfl⟩ : syracuseStep 1150243 = 1725365) B1725365
theorem B2592035 : Blo 1148636 2592035 := bstep (se 1 (by rfl) ⟨1944026, by rfl⟩ : syracuseStep 2592035 = 3888053) B3888053
theorem B1150259 : Blo 1148636 1150259 := bstep (se 1 (by rfl) ⟨862694, by rfl⟩ : syracuseStep 1150259 = 1725389) B1725389
theorem B1150275 : Blo 1148636 1150275 := bstep (se 1 (by rfl) ⟨862706, by rfl⟩ : syracuseStep 1150275 = 1725413) B1725413
theorem B1150291 : Blo 1148636 1150291 := bstep (se 1 (by rfl) ⟨862718, by rfl⟩ : syracuseStep 1150291 = 1725437) B1725437
theorem B1150307 : Blo 1148636 1150307 := bstep (se 1 (by rfl) ⟨862730, by rfl⟩ : syracuseStep 1150307 = 1725461) B1725461
theorem B1150323 : Blo 1148636 1150323 := bstep (se 1 (by rfl) ⟨862742, by rfl⟩ : syracuseStep 1150323 = 1725485) B1725485
theorem B1150339 : Blo 1148636 1150339 := bstep (se 1 (by rfl) ⟨862754, by rfl⟩ : syracuseStep 1150339 = 1725509) B1725509
theorem B1150355 : Blo 1148636 1150355 := bstep (se 1 (by rfl) ⟨862766, by rfl⟩ : syracuseStep 1150355 = 1725533) B1725533
theorem B1150371 : Blo 1148636 1150371 := bstep (se 1 (by rfl) ⟨862778, by rfl⟩ : syracuseStep 1150371 = 1725557) B1725557
theorem B1150387 : Blo 1148636 1150387 := bstep (se 1 (by rfl) ⟨862790, by rfl⟩ : syracuseStep 1150387 = 1725581) B1725581
theorem B1150403 : Blo 1148636 1150403 := bstep (se 1 (by rfl) ⟨862802, by rfl⟩ : syracuseStep 1150403 = 1725605) B1725605
theorem B1150419 : Blo 1148636 1150419 := bstep (se 1 (by rfl) ⟨862814, by rfl⟩ : syracuseStep 1150419 = 1725629) B1725629
theorem B1150435 : Blo 1148636 1150435 := bstep (se 1 (by rfl) ⟨862826, by rfl⟩ : syracuseStep 1150435 = 1725653) B1725653
theorem B4918769 : Blo 1148636 4918769 := bstep (se 2 (by rfl) ⟨1844538, by rfl⟩ : syracuseStep 4918769 = 3689077) B3689077
theorem B1150451 : Blo 1148636 1150451 := bstep (se 1 (by rfl) ⟨862838, by rfl⟩ : syracuseStep 1150451 = 1725677) B1725677
theorem B1150467 : Blo 1148636 1150467 := bstep (se 1 (by rfl) ⟨862850, by rfl⟩ : syracuseStep 1150467 = 1725701) B1725701
theorem B1150483 : Blo 1148636 1150483 := bstep (se 1 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 1150483 = 1725725) B1725725
theorem B1150499 : Blo 1148636 1150499 := bstep (se 1 (by rfl) ⟨862874, by rfl⟩ : syracuseStep 1150499 = 1725749) B1725749
theorem B6557219 : Blo 1148636 6557219 := bstep (se 1 (by rfl) ⟨4917914, by rfl⟩ : syracuseStep 6557219 = 9835829) B9835829
theorem B2592305 : Blo 1148636 2592305 := bstep (se 2 (by rfl) ⟨972114, by rfl⟩ : syracuseStep 2592305 = 1944229) B1944229
theorem B1150515 : Blo 1148636 1150515 := bstep (se 1 (by rfl) ⟨862886, by rfl⟩ : syracuseStep 1150515 = 1725773) B1725773
theorem B1150531 : Blo 1148636 1150531 := bstep (se 1 (by rfl) ⟨862898, by rfl⟩ : syracuseStep 1150531 = 1725797) B1725797
theorem B2592323 : Blo 1148636 2592323 := bstep (se 1 (by rfl) ⟨1944242, by rfl⟩ : syracuseStep 2592323 = 3888485) B3888485
theorem B11046469 : Blo 1148636 11046469 := bstep (se 4 (by rfl) ⟨1035606, by rfl⟩ : syracuseStep 11046469 = 2071213) B2071213
theorem B1150547 : Blo 1148636 1150547 := bstep (se 1 (by rfl) ⟨862910, by rfl⟩ : syracuseStep 1150547 = 1725821) B1725821
theorem B1150563 : Blo 1148636 1150563 := bstep (se 1 (by rfl) ⟨862922, by rfl⟩ : syracuseStep 1150563 = 1725845) B1725845
theorem B1150579 : Blo 1148636 1150579 := bstep (se 1 (by rfl) ⟨862934, by rfl⟩ : syracuseStep 1150579 = 1725869) B1725869
theorem B1150595 : Blo 1148636 1150595 := bstep (se 1 (by rfl) ⟨862946, by rfl⟩ : syracuseStep 1150595 = 1725893) B1725893
theorem B1150611 : Blo 1148636 1150611 := bstep (se 1 (by rfl) ⟨862958, by rfl⟩ : syracuseStep 1150611 = 1725917) B1725917
theorem B1150627 : Blo 1148636 1150627 := bstep (se 1 (by rfl) ⟨862970, by rfl⟩ : syracuseStep 1150627 = 1725941) B1725941
theorem B1150643 : Blo 1148636 1150643 := bstep (se 1 (by rfl) ⟨862982, by rfl⟩ : syracuseStep 1150643 = 1725965) B1725965
theorem B1150659 : Blo 1148636 1150659 := bstep (se 1 (by rfl) ⟨862994, by rfl⟩ : syracuseStep 1150659 = 1725989) B1725989
theorem B1150675 : Blo 1148636 1150675 := bstep (se 1 (by rfl) ⟨863006, by rfl⟩ : syracuseStep 1150675 = 1726013) B1726013
theorem B1150691 : Blo 1148636 1150691 := bstep (se 1 (by rfl) ⟨863018, by rfl⟩ : syracuseStep 1150691 = 1726037) B1726037
theorem B1150707 : Blo 1148636 1150707 := bstep (se 1 (by rfl) ⟨863030, by rfl⟩ : syracuseStep 1150707 = 1726061) B1726061
theorem B1150723 : Blo 1148636 1150723 := bstep (se 1 (by rfl) ⟨863042, by rfl⟩ : syracuseStep 1150723 = 1726085) B1726085
theorem B1969937 : Blo 1148636 1969937 := bstep (se 2 (by rfl) ⟨738726, by rfl⟩ : syracuseStep 1969937 = 1477453) B1477453
theorem B1150739 : Blo 1148636 1150739 := bstep (se 1 (by rfl) ⟨863054, by rfl⟩ : syracuseStep 1150739 = 1726109) B1726109
theorem B1150755 : Blo 1148636 1150755 := bstep (se 1 (by rfl) ⟨863066, by rfl⟩ : syracuseStep 1150755 = 1726133) B1726133
theorem B1150771 : Blo 1148636 1150771 := bstep (se 1 (by rfl) ⟨863078, by rfl⟩ : syracuseStep 1150771 = 1726157) B1726157
theorem B1150787 : Blo 1148636 1150787 := bstep (se 1 (by rfl) ⟨863090, by rfl⟩ : syracuseStep 1150787 = 1726181) B1726181
theorem B2592593 : Blo 1148636 2592593 := bstep (se 2 (by rfl) ⟨972222, by rfl⟩ : syracuseStep 2592593 = 1944445) B1944445
theorem B1150803 : Blo 1148636 1150803 := bstep (se 1 (by rfl) ⟨863102, by rfl⟩ : syracuseStep 1150803 = 1726205) B1726205
theorem B1150819 : Blo 1148636 1150819 := bstep (se 1 (by rfl) ⟨863114, by rfl⟩ : syracuseStep 1150819 = 1726229) B1726229
theorem B2592611 : Blo 1148636 2592611 := bstep (se 1 (by rfl) ⟨1944458, by rfl⟩ : syracuseStep 2592611 = 3888917) B3888917
theorem B1150835 : Blo 1148636 1150835 := bstep (se 1 (by rfl) ⟨863126, by rfl⟩ : syracuseStep 1150835 = 1726253) B1726253
theorem B1150851 : Blo 1148636 1150851 := bstep (se 1 (by rfl) ⟨863138, by rfl⟩ : syracuseStep 1150851 = 1726277) B1726277
theorem B1150867 : Blo 1148636 1150867 := bstep (se 1 (by rfl) ⟨863150, by rfl⟩ : syracuseStep 1150867 = 1726301) B1726301
theorem B1150883 : Blo 1148636 1150883 := bstep (se 1 (by rfl) ⟨863162, by rfl⟩ : syracuseStep 1150883 = 1726325) B1726325
theorem B1150899 : Blo 1148636 1150899 := bstep (se 1 (by rfl) ⟨863174, by rfl⟩ : syracuseStep 1150899 = 1726349) B1726349
theorem B1150915 : Blo 1148636 1150915 := bstep (se 1 (by rfl) ⟨863186, by rfl⟩ : syracuseStep 1150915 = 1726373) B1726373
theorem B1150931 : Blo 1148636 1150931 := bstep (se 1 (by rfl) ⟨863198, by rfl⟩ : syracuseStep 1150931 = 1726397) B1726397
theorem B1150947 : Blo 1148636 1150947 := bstep (se 1 (by rfl) ⟨863210, by rfl⟩ : syracuseStep 1150947 = 1726421) B1726421
theorem B1150963 : Blo 1148636 1150963 := bstep (se 1 (by rfl) ⟨863222, by rfl⟩ : syracuseStep 1150963 = 1726445) B1726445
theorem B1150979 : Blo 1148636 1150979 := bstep (se 1 (by rfl) ⟨863234, by rfl⟩ : syracuseStep 1150979 = 1726469) B1726469
theorem B1150995 : Blo 1148636 1150995 := bstep (se 1 (by rfl) ⟨863246, by rfl⟩ : syracuseStep 1150995 = 1726493) B1726493
theorem B4362275 : Blo 1148636 4362275 := bstep (se 1 (by rfl) ⟨3271706, by rfl⟩ : syracuseStep 4362275 = 6543413) B6543413
theorem B1151011 : Blo 1148636 1151011 := bstep (se 1 (by rfl) ⟨863258, by rfl⟩ : syracuseStep 1151011 = 1726517) B1726517
theorem B3280945 : Blo 1148636 3280945 := bstep (se 2 (by rfl) ⟨1230354, by rfl⟩ : syracuseStep 3280945 = 2460709) B2460709
theorem B1151027 : Blo 1148636 1151027 := bstep (se 1 (by rfl) ⟨863270, by rfl⟩ : syracuseStep 1151027 = 1726541) B1726541
theorem B1151043 : Blo 1148636 1151043 := bstep (se 1 (by rfl) ⟨863282, by rfl⟩ : syracuseStep 1151043 = 1726565) B1726565
theorem B1151059 : Blo 1148636 1151059 := bstep (se 1 (by rfl) ⟨863294, by rfl⟩ : syracuseStep 1151059 = 1726589) B1726589
theorem B1151075 : Blo 1148636 1151075 := bstep (se 1 (by rfl) ⟨863306, by rfl⟩ : syracuseStep 1151075 = 1726613) B1726613
theorem B2592881 : Blo 1148636 2592881 := bstep (se 2 (by rfl) ⟨972330, by rfl⟩ : syracuseStep 2592881 = 1944661) B1944661
theorem B1151091 : Blo 1148636 1151091 := bstep (se 1 (by rfl) ⟨863318, by rfl⟩ : syracuseStep 1151091 = 1726637) B1726637
theorem B1151107 : Blo 1148636 1151107 := bstep (se 1 (by rfl) ⟨863330, by rfl⟩ : syracuseStep 1151107 = 1726661) B1726661
theorem B2592899 : Blo 1148636 2592899 := bstep (se 1 (by rfl) ⟨1944674, by rfl⟩ : syracuseStep 2592899 = 3889349) B3889349
theorem B1151123 : Blo 1148636 1151123 := bstep (se 1 (by rfl) ⟨863342, by rfl⟩ : syracuseStep 1151123 = 1726685) B1726685
theorem B1151139 : Blo 1148636 1151139 := bstep (se 1 (by rfl) ⟨863354, by rfl⟩ : syracuseStep 1151139 = 1726709) B1726709
theorem B1151155 : Blo 1148636 1151155 := bstep (se 1 (by rfl) ⟨863366, by rfl⟩ : syracuseStep 1151155 = 1726733) B1726733
theorem B1151171 : Blo 1148636 1151171 := bstep (se 1 (by rfl) ⟨863378, by rfl⟩ : syracuseStep 1151171 = 1726757) B1726757
theorem B1151187 : Blo 1148636 1151187 := bstep (se 1 (by rfl) ⟨863390, by rfl⟩ : syracuseStep 1151187 = 1726781) B1726781
theorem B1151203 : Blo 1148636 1151203 := bstep (se 1 (by rfl) ⟨863402, by rfl⟩ : syracuseStep 1151203 = 1726805) B1726805
theorem B1151219 : Blo 1148636 1151219 := bstep (se 1 (by rfl) ⟨863414, by rfl⟩ : syracuseStep 1151219 = 1726829) B1726829
theorem B1151235 : Blo 1148636 1151235 := bstep (se 1 (by rfl) ⟨863426, by rfl⟩ : syracuseStep 1151235 = 1726853) B1726853
theorem B1151251 : Blo 1148636 1151251 := bstep (se 1 (by rfl) ⟨863438, by rfl⟩ : syracuseStep 1151251 = 1726877) B1726877
theorem B1151267 : Blo 1148636 1151267 := bstep (se 1 (by rfl) ⟨863450, by rfl⟩ : syracuseStep 1151267 = 1726901) B1726901
theorem B1151283 : Blo 1148636 1151283 := bstep (se 1 (by rfl) ⟨863462, by rfl⟩ : syracuseStep 1151283 = 1726925) B1726925
theorem B1151299 : Blo 1148636 1151299 := bstep (se 1 (by rfl) ⟨863474, by rfl⟩ : syracuseStep 1151299 = 1726949) B1726949
theorem B3281219 : Blo 1148636 3281219 := bstep (se 1 (by rfl) ⟨2460914, by rfl⟩ : syracuseStep 3281219 = 4921829) B4921829
theorem B1151315 : Blo 1148636 1151315 := bstep (se 1 (by rfl) ⟨863486, by rfl⟩ : syracuseStep 1151315 = 1726973) B1726973
theorem B1151331 : Blo 1148636 1151331 := bstep (se 1 (by rfl) ⟨863498, by rfl⟩ : syracuseStep 1151331 = 1726997) B1726997
theorem B2330993 : Blo 1148636 2330993 := bstep (se 2 (by rfl) ⟨874122, by rfl⟩ : syracuseStep 2330993 = 1748245) B1748245
theorem B1151347 : Blo 1148636 1151347 := bstep (se 1 (by rfl) ⟨863510, by rfl⟩ : syracuseStep 1151347 = 1727021) B1727021
theorem B1151363 : Blo 1148636 1151363 := bstep (se 1 (by rfl) ⟨863522, by rfl⟩ : syracuseStep 1151363 = 1727045) B1727045
theorem B2593169 : Blo 1148636 2593169 := bstep (se 2 (by rfl) ⟨972438, by rfl⟩ : syracuseStep 2593169 = 1944877) B1944877
theorem B1151379 : Blo 1148636 1151379 := bstep (se 1 (by rfl) ⟨863534, by rfl⟩ : syracuseStep 1151379 = 1727069) B1727069
theorem B1151395 : Blo 1148636 1151395 := bstep (se 1 (by rfl) ⟨863546, by rfl⟩ : syracuseStep 1151395 = 1727093) B1727093
theorem B2593187 : Blo 1148636 2593187 := bstep (se 1 (by rfl) ⟨1944890, by rfl⟩ : syracuseStep 2593187 = 3889781) B3889781
theorem B1151411 : Blo 1148636 1151411 := bstep (se 1 (by rfl) ⟨863558, by rfl⟩ : syracuseStep 1151411 = 1727117) B1727117
theorem B1151427 : Blo 1148636 1151427 := bstep (se 1 (by rfl) ⟨863570, by rfl⟩ : syracuseStep 1151427 = 1727141) B1727141
theorem B1151443 : Blo 1148636 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B1151459 : Blo 1148636 1151459 := bstep (se 1 (by rfl) ⟨863594, by rfl⟩ : syracuseStep 1151459 = 1727189) B1727189
theorem B13111793 : Blo 1148636 13111793 := bstep (se 2 (by rfl) ⟨4916922, by rfl⟩ : syracuseStep 13111793 = 9833845) B9833845
theorem B1151475 : Blo 1148636 1151475 := bstep (se 1 (by rfl) ⟨863606, by rfl⟩ : syracuseStep 1151475 = 1727213) B1727213
theorem B1151491 : Blo 1148636 1151491 := bstep (se 1 (by rfl) ⟨863618, by rfl⟩ : syracuseStep 1151491 = 1727237) B1727237
theorem B3281411 : Blo 1148636 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B1151507 : Blo 1148636 1151507 := bstep (se 1 (by rfl) ⟨863630, by rfl⟩ : syracuseStep 1151507 = 1727261) B1727261
theorem B1151523 : Blo 1148636 1151523 := bstep (se 1 (by rfl) ⟨863642, by rfl⟩ : syracuseStep 1151523 = 1727285) B1727285
theorem B1151539 : Blo 1148636 1151539 := bstep (se 1 (by rfl) ⟨863654, by rfl⟩ : syracuseStep 1151539 = 1727309) B1727309
theorem B1151555 : Blo 1148636 1151555 := bstep (se 1 (by rfl) ⟨863666, by rfl⟩ : syracuseStep 1151555 = 1727333) B1727333
theorem B1151571 : Blo 1148636 1151571 := bstep (se 1 (by rfl) ⟨863678, by rfl⟩ : syracuseStep 1151571 = 1727357) B1727357
theorem B1151587 : Blo 1148636 1151587 := bstep (se 1 (by rfl) ⟨863690, by rfl⟩ : syracuseStep 1151587 = 1727381) B1727381
theorem B1151603 : Blo 1148636 1151603 := bstep (se 1 (by rfl) ⟨863702, by rfl⟩ : syracuseStep 1151603 = 1727405) B1727405
theorem B1151619 : Blo 1148636 1151619 := bstep (se 1 (by rfl) ⟨863714, by rfl⟩ : syracuseStep 1151619 = 1727429) B1727429
theorem B1151635 : Blo 1148636 1151635 := bstep (se 1 (by rfl) ⟨863726, by rfl⟩ : syracuseStep 1151635 = 1727453) B1727453
theorem B1151651 : Blo 1148636 1151651 := bstep (se 1 (by rfl) ⟨863738, by rfl⟩ : syracuseStep 1151651 = 1727477) B1727477
theorem B4362929 : Blo 1148636 4362929 := bstep (se 2 (by rfl) ⟨1636098, by rfl⟩ : syracuseStep 4362929 = 3272197) B3272197
theorem B1151667 : Blo 1148636 1151667 := bstep (se 1 (by rfl) ⟨863750, by rfl⟩ : syracuseStep 1151667 = 1727501) B1727501
theorem B1151683 : Blo 1148636 1151683 := bstep (se 1 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 1151683 = 1727525) B1727525
theorem B1151699 : Blo 1148636 1151699 := bstep (se 1 (by rfl) ⟨863774, by rfl⟩ : syracuseStep 1151699 = 1727549) B1727549
theorem B1151715 : Blo 1148636 1151715 := bstep (se 1 (by rfl) ⟨863786, by rfl⟩ : syracuseStep 1151715 = 1727573) B1727573
theorem B1151731 : Blo 1148636 1151731 := bstep (se 1 (by rfl) ⟨863798, by rfl⟩ : syracuseStep 1151731 = 1727597) B1727597
theorem B1151747 : Blo 1148636 1151747 := bstep (se 1 (by rfl) ⟨863810, by rfl⟩ : syracuseStep 1151747 = 1727621) B1727621
theorem B1151763 : Blo 1148636 1151763 := bstep (se 1 (by rfl) ⟨863822, by rfl⟩ : syracuseStep 1151763 = 1727645) B1727645
theorem B1151779 : Blo 1148636 1151779 := bstep (se 1 (by rfl) ⟨863834, by rfl⟩ : syracuseStep 1151779 = 1727669) B1727669
theorem B1151795 : Blo 1148636 1151795 := bstep (se 1 (by rfl) ⟨863846, by rfl⟩ : syracuseStep 1151795 = 1727693) B1727693
theorem B1151811 : Blo 1148636 1151811 := bstep (se 1 (by rfl) ⟨863858, by rfl⟩ : syracuseStep 1151811 = 1727717) B1727717
theorem B1151827 : Blo 1148636 1151827 := bstep (se 1 (by rfl) ⟨863870, by rfl⟩ : syracuseStep 1151827 = 1727741) B1727741
theorem B1151843 : Blo 1148636 1151843 := bstep (se 1 (by rfl) ⟨863882, by rfl⟩ : syracuseStep 1151843 = 1727765) B1727765
theorem B1151859 : Blo 1148636 1151859 := bstep (se 1 (by rfl) ⟨863894, by rfl⟩ : syracuseStep 1151859 = 1727789) B1727789
theorem B1151875 : Blo 1148636 1151875 := bstep (se 1 (by rfl) ⟨863906, by rfl⟩ : syracuseStep 1151875 = 1727813) B1727813
theorem B1151891 : Blo 1148636 1151891 := bstep (se 1 (by rfl) ⟨863918, by rfl⟩ : syracuseStep 1151891 = 1727837) B1727837
theorem B1151907 : Blo 1148636 1151907 := bstep (se 1 (by rfl) ⟨863930, by rfl⟩ : syracuseStep 1151907 = 1727861) B1727861
theorem B1151923 : Blo 1148636 1151923 := bstep (se 1 (by rfl) ⟨863942, by rfl⟩ : syracuseStep 1151923 = 1727885) B1727885
theorem B1840067 : Blo 1148636 1840067 := bstep (se 1 (by rfl) ⟨1380050, by rfl⟩ : syracuseStep 1840067 = 2760101) B2760101
theorem B1151939 : Blo 1148636 1151939 := bstep (se 1 (by rfl) ⟨863954, by rfl⟩ : syracuseStep 1151939 = 1727909) B1727909
theorem B1151955 : Blo 1148636 1151955 := bstep (se 1 (by rfl) ⟨863966, by rfl⟩ : syracuseStep 1151955 = 1727933) B1727933
theorem B1840099 : Blo 1148636 1840099 := bstep (se 1 (by rfl) ⟨1380074, by rfl⟩ : syracuseStep 1840099 = 2760149) B2760149
theorem B1151971 : Blo 1148636 1151971 := bstep (se 1 (by rfl) ⟨863978, by rfl⟩ : syracuseStep 1151971 = 1727957) B1727957
theorem B1151987 : Blo 1148636 1151987 := bstep (se 1 (by rfl) ⟨863990, by rfl⟩ : syracuseStep 1151987 = 1727981) B1727981
theorem B1152003 : Blo 1148636 1152003 := bstep (se 1 (by rfl) ⟨864002, by rfl⟩ : syracuseStep 1152003 = 1728005) B1728005
theorem B1938451 : Blo 1148636 1938451 := bstep (se 1 (by rfl) ⟨1453838, by rfl⟩ : syracuseStep 1938451 = 2907677) B2907677
theorem B1152019 : Blo 1148636 1152019 := bstep (se 1 (by rfl) ⟨864014, by rfl⟩ : syracuseStep 1152019 = 1728029) B1728029
theorem B1152035 : Blo 1148636 1152035 := bstep (se 1 (by rfl) ⟨864026, by rfl⟩ : syracuseStep 1152035 = 1728053) B1728053
theorem B1152051 : Blo 1148636 1152051 := bstep (se 1 (by rfl) ⟨864038, by rfl⟩ : syracuseStep 1152051 = 1728077) B1728077
theorem B1152067 : Blo 1148636 1152067 := bstep (se 1 (by rfl) ⟨864050, by rfl⟩ : syracuseStep 1152067 = 1728101) B1728101
theorem B1152083 : Blo 1148636 1152083 := bstep (se 1 (by rfl) ⟨864062, by rfl⟩ : syracuseStep 1152083 = 1728125) B1728125
theorem B1152099 : Blo 1148636 1152099 := bstep (se 1 (by rfl) ⟨864074, by rfl⟩ : syracuseStep 1152099 = 1728149) B1728149
theorem B1152115 : Blo 1148636 1152115 := bstep (se 1 (by rfl) ⟨864086, by rfl⟩ : syracuseStep 1152115 = 1728173) B1728173
theorem B1152131 : Blo 1148636 1152131 := bstep (se 1 (by rfl) ⟨864098, by rfl⟩ : syracuseStep 1152131 = 1728197) B1728197
theorem B1152147 : Blo 1148636 1152147 := bstep (se 1 (by rfl) ⟨864110, by rfl⟩ : syracuseStep 1152147 = 1728221) B1728221
theorem B1938593 : Blo 1148636 1938593 := bstep (se 2 (by rfl) ⟨726972, by rfl⟩ : syracuseStep 1938593 = 1453945) B1453945
theorem B1152163 : Blo 1148636 1152163 := bstep (se 1 (by rfl) ⟨864122, by rfl⟩ : syracuseStep 1152163 = 1728245) B1728245
theorem B1152179 : Blo 1148636 1152179 := bstep (se 1 (by rfl) ⟨864134, by rfl⟩ : syracuseStep 1152179 = 1728269) B1728269
theorem B1152195 : Blo 1148636 1152195 := bstep (se 1 (by rfl) ⟨864146, by rfl⟩ : syracuseStep 1152195 = 1728293) B1728293
theorem B1152211 : Blo 1148636 1152211 := bstep (se 1 (by rfl) ⟨864158, by rfl⟩ : syracuseStep 1152211 = 1728317) B1728317
theorem B1152227 : Blo 1148636 1152227 := bstep (se 1 (by rfl) ⟨864170, by rfl⟩ : syracuseStep 1152227 = 1728341) B1728341
theorem B1152243 : Blo 1148636 1152243 := bstep (se 1 (by rfl) ⟨864182, by rfl⟩ : syracuseStep 1152243 = 1728365) B1728365
theorem B1152259 : Blo 1148636 1152259 := bstep (se 1 (by rfl) ⟨864194, by rfl⟩ : syracuseStep 1152259 = 1728389) B1728389
theorem B1152275 : Blo 1148636 1152275 := bstep (se 1 (by rfl) ⟨864206, by rfl⟩ : syracuseStep 1152275 = 1728413) B1728413
theorem B1938721 : Blo 1148636 1938721 := bstep (se 2 (by rfl) ⟨727020, by rfl⟩ : syracuseStep 1938721 = 1454041) B1454041
theorem B1152291 : Blo 1148636 1152291 := bstep (se 1 (by rfl) ⟨864218, by rfl⟩ : syracuseStep 1152291 = 1728437) B1728437
theorem B3282221 : Blo 1148636 3282221 := bstep (se 3 (by rfl) ⟨615416, by rfl⟩ : syracuseStep 3282221 = 1230833) B1230833
theorem B1152307 : Blo 1148636 1152307 := bstep (se 1 (by rfl) ⟨864230, by rfl⟩ : syracuseStep 1152307 = 1728461) B1728461
theorem B1938755 : Blo 1148636 1938755 := bstep (se 1 (by rfl) ⟨1454066, by rfl⟩ : syracuseStep 1938755 = 2908133) B2908133
theorem B1152323 : Blo 1148636 1152323 := bstep (se 1 (by rfl) ⟨864242, by rfl⟩ : syracuseStep 1152323 = 1728485) B1728485
theorem B1152339 : Blo 1148636 1152339 := bstep (se 1 (by rfl) ⟨864254, by rfl⟩ : syracuseStep 1152339 = 1728509) B1728509
theorem B1152355 : Blo 1148636 1152355 := bstep (se 1 (by rfl) ⟨864266, by rfl⟩ : syracuseStep 1152355 = 1728533) B1728533
theorem B1152371 : Blo 1148636 1152371 := bstep (se 1 (by rfl) ⟨864278, by rfl⟩ : syracuseStep 1152371 = 1728557) B1728557
theorem B1152387 : Blo 1148636 1152387 := bstep (se 1 (by rfl) ⟨864290, by rfl⟩ : syracuseStep 1152387 = 1728581) B1728581
theorem B1152403 : Blo 1148636 1152403 := bstep (se 1 (by rfl) ⟨864302, by rfl⟩ : syracuseStep 1152403 = 1728605) B1728605
theorem B1152419 : Blo 1148636 1152419 := bstep (se 1 (by rfl) ⟨864314, by rfl⟩ : syracuseStep 1152419 = 1728629) B1728629
theorem B1152435 : Blo 1148636 1152435 := bstep (se 1 (by rfl) ⟨864326, by rfl⟩ : syracuseStep 1152435 = 1728653) B1728653
theorem B1938883 : Blo 1148636 1938883 := bstep (se 1 (by rfl) ⟨1454162, by rfl⟩ : syracuseStep 1938883 = 2908325) B2908325
theorem B1152451 : Blo 1148636 1152451 := bstep (se 1 (by rfl) ⟨864338, by rfl⟩ : syracuseStep 1152451 = 1728677) B1728677
theorem B1152467 : Blo 1148636 1152467 := bstep (se 1 (by rfl) ⟨864350, by rfl⟩ : syracuseStep 1152467 = 1728701) B1728701
theorem B1152483 : Blo 1148636 1152483 := bstep (se 1 (by rfl) ⟨864362, by rfl⟩ : syracuseStep 1152483 = 1728725) B1728725
theorem B1152499 : Blo 1148636 1152499 := bstep (se 1 (by rfl) ⟨864374, by rfl⟩ : syracuseStep 1152499 = 1728749) B1728749
theorem B1152515 : Blo 1148636 1152515 := bstep (se 1 (by rfl) ⟨864386, by rfl⟩ : syracuseStep 1152515 = 1728773) B1728773
theorem B1152531 : Blo 1148636 1152531 := bstep (se 1 (by rfl) ⟨864398, by rfl⟩ : syracuseStep 1152531 = 1728797) B1728797
theorem B1152547 : Blo 1148636 1152547 := bstep (se 1 (by rfl) ⟨864410, by rfl⟩ : syracuseStep 1152547 = 1728821) B1728821
theorem B1152563 : Blo 1148636 1152563 := bstep (se 1 (by rfl) ⟨864422, by rfl⟩ : syracuseStep 1152563 = 1728845) B1728845
theorem B1152579 : Blo 1148636 1152579 := bstep (se 1 (by rfl) ⟨864434, by rfl⟩ : syracuseStep 1152579 = 1728869) B1728869
theorem B1939025 : Blo 1148636 1939025 := bstep (se 2 (by rfl) ⟨727134, by rfl⟩ : syracuseStep 1939025 = 1454269) B1454269
theorem B1152595 : Blo 1148636 1152595 := bstep (se 1 (by rfl) ⟨864446, by rfl⟩ : syracuseStep 1152595 = 1728893) B1728893
theorem B1152611 : Blo 1148636 1152611 := bstep (se 1 (by rfl) ⟨864458, by rfl⟩ : syracuseStep 1152611 = 1728917) B1728917
theorem B1152627 : Blo 1148636 1152627 := bstep (se 1 (by rfl) ⟨864470, by rfl⟩ : syracuseStep 1152627 = 1728941) B1728941
theorem B31495877 : Blo 1148636 31495877 := bstep (se 4 (by rfl) ⟨2952738, by rfl⟩ : syracuseStep 31495877 = 5905477) B5905477
theorem B1939153 : Blo 1148636 1939153 := bstep (se 2 (by rfl) ⟨727182, by rfl⟩ : syracuseStep 1939153 = 1454365) B1454365
theorem B1939187 : Blo 1148636 1939187 := bstep (se 1 (by rfl) ⟨1454390, by rfl⟩ : syracuseStep 1939187 = 2908781) B2908781
theorem B1939315 : Blo 1148636 1939315 := bstep (se 1 (by rfl) ⟨1454486, by rfl⟩ : syracuseStep 1939315 = 2908973) B2908973
theorem B1841027 : Blo 1148636 1841027 := bstep (se 1 (by rfl) ⟨1380770, by rfl⟩ : syracuseStep 1841027 = 2761541) B2761541
theorem B4921229 : Blo 1148636 4921229 := bstep (se 3 (by rfl) ⟨922730, by rfl⟩ : syracuseStep 4921229 = 1845461) B1845461
theorem B1841105 : Blo 1148636 1841105 := bstep (se 2 (by rfl) ⟨690414, by rfl⟩ : syracuseStep 1841105 = 1380829) B1380829
theorem B1939457 : Blo 1148636 1939457 := bstep (se 2 (by rfl) ⟨727296, by rfl⟩ : syracuseStep 1939457 = 1454593) B1454593
theorem B4364387 : Blo 1148636 4364387 := bstep (se 1 (by rfl) ⟨3273290, by rfl⟩ : syracuseStep 4364387 = 6546581) B6546581
theorem B4364401 : Blo 1148636 4364401 := bstep (se 2 (by rfl) ⟨1636650, by rfl⟩ : syracuseStep 4364401 = 3273301) B3273301
theorem B1939585 : Blo 1148636 1939585 := bstep (se 2 (by rfl) ⟨727344, by rfl⟩ : syracuseStep 1939585 = 1454689) B1454689
theorem B1939619 : Blo 1148636 1939619 := bstep (se 1 (by rfl) ⟨1454714, by rfl⟩ : syracuseStep 1939619 = 2909429) B2909429
theorem B1841329 : Blo 1148636 1841329 := bstep (se 2 (by rfl) ⟨690498, by rfl⟩ : syracuseStep 1841329 = 1380997) B1380997
theorem B3315953 : Blo 1148636 3315953 := bstep (se 2 (by rfl) ⟨1243482, by rfl⟩ : syracuseStep 3315953 = 2486965) B2486965
theorem B1939747 : Blo 1148636 1939747 := bstep (se 1 (by rfl) ⟨1454810, by rfl⟩ : syracuseStep 1939747 = 2909621) B2909621
theorem B3938669 : Blo 1148636 3938669 := bstep (se 3 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 3938669 = 1477001) B1477001
theorem B7379333 : Blo 1148636 7379333 := bstep (se 4 (by rfl) ⟨691812, by rfl⟩ : syracuseStep 7379333 = 1383625) B1383625
theorem B1939889 : Blo 1148636 1939889 := bstep (se 2 (by rfl) ⟨727458, by rfl⟩ : syracuseStep 1939889 = 1454917) B1454917
theorem B26974741 : Blo 1148636 26974741 := bstep (se 6 (by rfl) ⟨632220, by rfl⟩ : syracuseStep 26974741 = 1264441) B1264441
theorem B1940017 : Blo 1148636 1940017 := bstep (se 2 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 1940017 = 1455013) B1455013
theorem B1940051 : Blo 1148636 1940051 := bstep (se 1 (by rfl) ⟨1455038, by rfl⟩ : syracuseStep 1940051 = 2910077) B2910077
theorem B4659875 : Blo 1148636 4659875 := bstep (se 1 (by rfl) ⟨3494906, by rfl⟩ : syracuseStep 4659875 = 6989813) B6989813
theorem B19634885 : Blo 1148636 19634885 := bstep (se 4 (by rfl) ⟨1840770, by rfl⟩ : syracuseStep 19634885 = 3681541) B3681541
theorem B6560453 : Blo 1148636 6560453 := bstep (se 4 (by rfl) ⟨615042, by rfl⟩ : syracuseStep 6560453 = 1230085) B1230085
theorem B1940179 : Blo 1148636 1940179 := bstep (se 1 (by rfl) ⟨1455134, by rfl⟩ : syracuseStep 1940179 = 2910269) B2910269
theorem B8723213 : Blo 1148636 8723213 := bstep (se 3 (by rfl) ⟨1635602, by rfl⟩ : syracuseStep 8723213 = 3271205) B3271205
theorem B1940321 : Blo 1148636 1940321 := bstep (se 2 (by rfl) ⟨727620, by rfl⟩ : syracuseStep 1940321 = 1455241) B1455241
theorem B1940449 : Blo 1148636 1940449 := bstep (se 2 (by rfl) ⟨727668, by rfl⟩ : syracuseStep 1940449 = 1455337) B1455337
theorem B1940483 : Blo 1148636 1940483 := bstep (se 1 (by rfl) ⟨1455362, by rfl⟩ : syracuseStep 1940483 = 2910725) B2910725
theorem B2104355 : Blo 1148636 2104355 := bstep (se 1 (by rfl) ⟨1578266, by rfl⟩ : syracuseStep 2104355 = 3156533) B3156533
theorem B1940611 : Blo 1148636 1940611 := bstep (se 1 (by rfl) ⟨1455458, by rfl⟩ : syracuseStep 1940611 = 2910917) B2910917
theorem B6560909 : Blo 1148636 6560909 := bstep (se 3 (by rfl) ⟨1230170, by rfl⟩ : syracuseStep 6560909 = 2460341) B2460341
theorem B2071747 : Blo 1148636 2071747 := bstep (se 1 (by rfl) ⟨1553810, by rfl⟩ : syracuseStep 2071747 = 3107621) B3107621
theorem B1940753 : Blo 1148636 1940753 := bstep (se 2 (by rfl) ⟨727782, by rfl⟩ : syracuseStep 1940753 = 1455565) B1455565
theorem B2071921 : Blo 1148636 2071921 := bstep (se 2 (by rfl) ⟨776970, by rfl⟩ : syracuseStep 2071921 = 1553941) B1553941
theorem B1940881 : Blo 1148636 1940881 := bstep (se 2 (by rfl) ⟨727830, by rfl⟩ : syracuseStep 1940881 = 1455661) B1455661
theorem B4922801 : Blo 1148636 4922801 := bstep (se 2 (by rfl) ⟨1846050, by rfl⟩ : syracuseStep 4922801 = 3692101) B3692101
theorem B1940915 : Blo 1148636 1940915 := bstep (se 1 (by rfl) ⟨1455686, by rfl⟩ : syracuseStep 1940915 = 2911373) B2911373
theorem B1383923 : Blo 1148636 1383923 := bstep (se 1 (by rfl) ⟨1037942, by rfl⟩ : syracuseStep 1383923 = 2075885) B2075885
theorem B4365859 : Blo 1148636 4365859 := bstep (se 1 (by rfl) ⟨3274394, by rfl⟩ : syracuseStep 4365859 = 6548789) B6548789
theorem B1941043 : Blo 1148636 1941043 := bstep (se 1 (by rfl) ⟨1455782, by rfl⟩ : syracuseStep 1941043 = 2911565) B2911565
theorem B1941185 : Blo 1148636 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B1941313 : Blo 1148636 1941313 := bstep (se 2 (by rfl) ⟨727992, by rfl⟩ : syracuseStep 1941313 = 1455985) B1455985
theorem B2367299 : Blo 1148636 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B6987619 : Blo 1148636 6987619 := bstep (se 1 (by rfl) ⟨5240714, by rfl⟩ : syracuseStep 6987619 = 10481429) B10481429
theorem B1941347 : Blo 1148636 1941347 := bstep (se 1 (by rfl) ⟨1456010, by rfl⟩ : syracuseStep 1941347 = 2912021) B2912021
theorem B1843091 : Blo 1148636 1843091 := bstep (se 1 (by rfl) ⟨1382318, by rfl⟩ : syracuseStep 1843091 = 2764637) B2764637
theorem B1941475 : Blo 1148636 1941475 := bstep (se 1 (by rfl) ⟨1456106, by rfl⟩ : syracuseStep 1941475 = 2912213) B2912213
theorem B3317777 : Blo 1148636 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B1843283 : Blo 1148636 1843283 := bstep (se 1 (by rfl) ⟨1382462, by rfl⟩ : syracuseStep 1843283 = 2764925) B2764925
theorem B1941617 : Blo 1148636 1941617 := bstep (se 2 (by rfl) ⟨728106, by rfl⟩ : syracuseStep 1941617 = 1456213) B1456213
theorem B1843411 : Blo 1148636 1843411 := bstep (se 1 (by rfl) ⟨1382558, by rfl⟩ : syracuseStep 1843411 = 2765117) B2765117
theorem B1941745 : Blo 1148636 1941745 := bstep (se 2 (by rfl) ⟨728154, by rfl⟩ : syracuseStep 1941745 = 1456309) B1456309
theorem B1941779 : Blo 1148636 1941779 := bstep (se 1 (by rfl) ⟨1456334, by rfl⟩ : syracuseStep 1941779 = 2912669) B2912669
theorem B1941907 : Blo 1148636 1941907 := bstep (se 1 (by rfl) ⟨1456430, by rfl⟩ : syracuseStep 1941907 = 2912861) B2912861
theorem B5612003 : Blo 1148636 5612003 := bstep (se 1 (by rfl) ⟨4209002, by rfl⟩ : syracuseStep 5612003 = 8418005) B8418005
theorem B1942049 : Blo 1148636 1942049 := bstep (se 2 (by rfl) ⟨728268, by rfl⟩ : syracuseStep 1942049 = 1456537) B1456537
theorem B1942177 : Blo 1148636 1942177 := bstep (se 2 (by rfl) ⟨728316, by rfl⟩ : syracuseStep 1942177 = 1456633) B1456633
theorem B1942211 : Blo 1148636 1942211 := bstep (se 1 (by rfl) ⟨1456658, by rfl⟩ : syracuseStep 1942211 = 2913317) B2913317
theorem B1942339 : Blo 1148636 1942339 := bstep (se 1 (by rfl) ⟨1456754, by rfl⟩ : syracuseStep 1942339 = 2913509) B2913509
theorem B1844051 : Blo 1148636 1844051 := bstep (se 1 (by rfl) ⟨1383038, by rfl⟩ : syracuseStep 1844051 = 2766077) B2766077
theorem B1844129 : Blo 1148636 1844129 := bstep (se 2 (by rfl) ⟨691548, by rfl⟩ : syracuseStep 1844129 = 1383097) B1383097
theorem B1942481 : Blo 1148636 1942481 := bstep (se 2 (by rfl) ⟨728430, by rfl⟩ : syracuseStep 1942481 = 1456861) B1456861
theorem B14754869 : Blo 1148636 14754869 := bstep (se 5 (by rfl) ⟨691634, by rfl⟩ : syracuseStep 14754869 = 1383269) B1383269
theorem B1942609 : Blo 1148636 1942609 := bstep (se 2 (by rfl) ⟨728478, by rfl⟩ : syracuseStep 1942609 = 1456957) B1456957
theorem B1942643 : Blo 1148636 1942643 := bstep (se 1 (by rfl) ⟨1456982, by rfl⟩ : syracuseStep 1942643 = 2913965) B2913965
theorem B3155075 : Blo 1148636 3155075 := bstep (se 1 (by rfl) ⟨2366306, by rfl⟩ : syracuseStep 3155075 = 4732613) B4732613
theorem B2335921 : Blo 1148636 2335921 := bstep (se 2 (by rfl) ⟨875970, by rfl⟩ : syracuseStep 2335921 = 1751941) B1751941
theorem B1942771 : Blo 1148636 1942771 := bstep (se 1 (by rfl) ⟨1457078, by rfl⟩ : syracuseStep 1942771 = 2914157) B2914157
theorem B1844513 : Blo 1148636 1844513 := bstep (se 2 (by rfl) ⟨691692, by rfl⟩ : syracuseStep 1844513 = 1383385) B1383385
theorem B1942913 : Blo 1148636 1942913 := bstep (se 2 (by rfl) ⟨728592, by rfl⟩ : syracuseStep 1942913 = 1457185) B1457185
theorem B1844641 : Blo 1148636 1844641 := bstep (se 2 (by rfl) ⟨691740, by rfl⟩ : syracuseStep 1844641 = 1383481) B1383481
theorem B2762147 : Blo 1148636 2762147 := bstep (se 1 (by rfl) ⟨2071610, by rfl⟩ : syracuseStep 2762147 = 4143221) B4143221
theorem B1943041 : Blo 1148636 1943041 := bstep (se 2 (by rfl) ⟨728640, by rfl⟩ : syracuseStep 1943041 = 1457281) B1457281
theorem B1943075 : Blo 1148636 1943075 := bstep (se 1 (by rfl) ⟨1457306, by rfl⟩ : syracuseStep 1943075 = 2914613) B2914613
theorem B3679825 : Blo 1148636 3679825 := bstep (se 2 (by rfl) ⟨1379934, by rfl⟩ : syracuseStep 3679825 = 2759869) B2759869
theorem B8726129 : Blo 1148636 8726129 := bstep (se 2 (by rfl) ⟨3272298, by rfl⟩ : syracuseStep 8726129 = 6544597) B6544597
theorem B1943203 : Blo 1148636 1943203 := bstep (se 1 (by rfl) ⟨1457402, by rfl⟩ : syracuseStep 1943203 = 2914805) B2914805
theorem B4368077 : Blo 1148636 4368077 := bstep (se 3 (by rfl) ⟨819014, by rfl⟩ : syracuseStep 4368077 = 1638029) B1638029
theorem B1943345 : Blo 1148636 1943345 := bstep (se 2 (by rfl) ⟨728754, by rfl⟩ : syracuseStep 1943345 = 1457509) B1457509
theorem B7382947 : Blo 1148636 7382947 := bstep (se 1 (by rfl) ⟨5537210, by rfl⟩ : syracuseStep 7382947 = 11074421) B11074421
theorem B1943473 : Blo 1148636 1943473 := bstep (se 2 (by rfl) ⟨728802, by rfl⟩ : syracuseStep 1943473 = 1457605) B1457605
theorem B1943507 : Blo 1148636 1943507 := bstep (se 1 (by rfl) ⟨1457630, by rfl⟩ : syracuseStep 1943507 = 2915261) B2915261
theorem B2074609 : Blo 1148636 2074609 := bstep (se 2 (by rfl) ⟨777978, by rfl⟩ : syracuseStep 2074609 = 1555957) B1555957
theorem B6563825 : Blo 1148636 6563825 := bstep (se 2 (by rfl) ⟨2461434, by rfl⟩ : syracuseStep 6563825 = 4922869) B4922869
theorem B4663345 : Blo 1148636 4663345 := bstep (se 2 (by rfl) ⟨1748754, by rfl⟩ : syracuseStep 4663345 = 3497509) B3497509
theorem B1943635 : Blo 1148636 1943635 := bstep (se 1 (by rfl) ⟨1457726, by rfl⟩ : syracuseStep 1943635 = 2915453) B2915453
theorem B3877037 : Blo 1148636 3877037 := bstep (se 3 (by rfl) ⟨726944, by rfl⟩ : syracuseStep 3877037 = 1453889) B1453889
theorem B1943777 : Blo 1148636 1943777 := bstep (se 2 (by rfl) ⟨728916, by rfl⟩ : syracuseStep 1943777 = 1457833) B1457833
theorem B3877091 : Blo 1148636 3877091 := bstep (se 1 (by rfl) ⟨2907818, by rfl⟩ : syracuseStep 3877091 = 5815637) B5815637
theorem B1943905 : Blo 1148636 1943905 := bstep (se 2 (by rfl) ⟨728964, by rfl⟩ : syracuseStep 1943905 = 1457929) B1457929
theorem B1943939 : Blo 1148636 1943939 := bstep (se 1 (by rfl) ⟨1457954, by rfl⟩ : syracuseStep 1943939 = 2915909) B2915909
theorem B3877361 : Blo 1148636 3877361 := bstep (se 2 (by rfl) ⟨1454010, by rfl⟩ : syracuseStep 3877361 = 2908021) B2908021
theorem B1944067 : Blo 1148636 1944067 := bstep (se 1 (by rfl) ⟨1458050, by rfl⟩ : syracuseStep 1944067 = 2916101) B2916101
theorem B1944209 : Blo 1148636 1944209 := bstep (se 2 (by rfl) ⟨729078, by rfl⟩ : syracuseStep 1944209 = 1458157) B1458157
theorem B1747649 : Blo 1148636 1747649 := bstep (se 2 (by rfl) ⟨655368, by rfl⟩ : syracuseStep 1747649 = 1310737) B1310737
theorem B14920433 : Blo 1148636 14920433 := bstep (se 2 (by rfl) ⟨5595162, by rfl⟩ : syracuseStep 14920433 = 11190325) B11190325
theorem B2075395 : Blo 1148636 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B1944337 : Blo 1148636 1944337 := bstep (se 2 (by rfl) ⟨729126, by rfl⟩ : syracuseStep 1944337 = 1458253) B1458253
theorem B1944371 : Blo 1148636 1944371 := bstep (se 1 (by rfl) ⟨1458278, by rfl⟩ : syracuseStep 1944371 = 2916557) B2916557
theorem B1846147 : Blo 1148636 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B6990733 : Blo 1148636 6990733 := bstep (se 3 (by rfl) ⟨1310762, by rfl⟩ : syracuseStep 6990733 = 2621525) B2621525
theorem B1944499 : Blo 1148636 1944499 := bstep (se 1 (by rfl) ⟨1458374, by rfl⟩ : syracuseStep 1944499 = 2916749) B2916749
theorem B3877901 : Blo 1148636 3877901 := bstep (se 3 (by rfl) ⟨727106, by rfl⟩ : syracuseStep 3877901 = 1454213) B1454213
theorem B1944641 : Blo 1148636 1944641 := bstep (se 2 (by rfl) ⟨729240, by rfl⟩ : syracuseStep 1944641 = 1458481) B1458481
theorem B3877955 : Blo 1148636 3877955 := bstep (se 1 (by rfl) ⟨2908466, by rfl⟩ : syracuseStep 3877955 = 5816933) B5816933
theorem B3681389 : Blo 1148636 3681389 := bstep (se 3 (by rfl) ⟨690260, by rfl⟩ : syracuseStep 3681389 = 1380521) B1380521
theorem B1944769 : Blo 1148636 1944769 := bstep (se 2 (by rfl) ⟨729288, by rfl⟩ : syracuseStep 1944769 = 1458577) B1458577
theorem B1944803 : Blo 1148636 1944803 := bstep (se 1 (by rfl) ⟨1458602, by rfl⟩ : syracuseStep 1944803 = 2917205) B2917205
theorem B3878225 : Blo 1148636 3878225 := bstep (se 2 (by rfl) ⟨1454334, by rfl⟩ : syracuseStep 3878225 = 2908669) B2908669
theorem B1944931 : Blo 1148636 1944931 := bstep (se 1 (by rfl) ⟨1458698, by rfl⟩ : syracuseStep 1944931 = 2917397) B2917397
theorem B1945073 : Blo 1148636 1945073 := bstep (se 2 (by rfl) ⟨729402, by rfl⟩ : syracuseStep 1945073 = 1458805) B1458805
theorem B4435469 : Blo 1148636 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B24850061 : Blo 1148636 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B1748657 : Blo 1148636 1748657 := bstep (se 2 (by rfl) ⟨655746, by rfl⟩ : syracuseStep 1748657 = 1311493) B1311493
theorem B16789189 : Blo 1148636 16789189 := bstep (se 4 (by rfl) ⟨1573986, by rfl⟩ : syracuseStep 16789189 = 3147973) B3147973
theorem B12431045 : Blo 1148636 12431045 := bstep (se 4 (by rfl) ⟨1165410, by rfl⟩ : syracuseStep 12431045 = 2330821) B2330821
theorem B3878765 : Blo 1148636 3878765 := bstep (se 3 (by rfl) ⟨727268, by rfl⟩ : syracuseStep 3878765 = 1454537) B1454537
theorem B3878819 : Blo 1148636 3878819 := bstep (se 1 (by rfl) ⟨2909114, by rfl⟩ : syracuseStep 3878819 = 5818229) B5818229
theorem B1683409 : Blo 1148636 1683409 := bstep (se 2 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 1683409 = 1262557) B1262557
theorem B1454051 : Blo 1148636 1454051 := bstep (se 1 (by rfl) ⟨1090538, by rfl⟩ : syracuseStep 1454051 = 2181077) B2181077
theorem B5681123 : Blo 1148636 5681123 := bstep (se 1 (by rfl) ⟨4260842, by rfl⟩ : syracuseStep 5681123 = 8521685) B8521685
theorem B3879089 : Blo 1148636 3879089 := bstep (se 2 (by rfl) ⟨1454658, by rfl⟩ : syracuseStep 3879089 = 2909317) B2909317
theorem B1749217 : Blo 1148636 1749217 := bstep (se 2 (by rfl) ⟨655956, by rfl⟩ : syracuseStep 1749217 = 1311913) B1311913
theorem B4370993 : Blo 1148636 4370993 := bstep (se 2 (by rfl) ⟨1639122, by rfl⟩ : syracuseStep 4370993 = 3278245) B3278245
theorem B1454755 : Blo 1148636 1454755 := bstep (se 1 (by rfl) ⟨1091066, by rfl⟩ : syracuseStep 1454755 = 2182133) B2182133
theorem B3879629 : Blo 1148636 3879629 := bstep (se 3 (by rfl) ⟨727430, by rfl⟩ : syracuseStep 3879629 = 1454861) B1454861
theorem B2765539 : Blo 1148636 2765539 := bstep (se 1 (by rfl) ⟨2074154, by rfl⟩ : syracuseStep 2765539 = 4148309) B4148309
theorem B1454851 : Blo 1148636 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B3879683 : Blo 1148636 3879683 := bstep (se 1 (by rfl) ⟨2909762, by rfl⟩ : syracuseStep 3879683 = 5819525) B5819525
theorem B3683171 : Blo 1148636 3683171 := bstep (se 1 (by rfl) ⟨2762378, by rfl⟩ : syracuseStep 3683171 = 5524757) B5524757
theorem B3879953 : Blo 1148636 3879953 := bstep (se 2 (by rfl) ⟨1454982, by rfl⟩ : syracuseStep 3879953 = 2909965) B2909965
theorem B5256227 : Blo 1148636 5256227 := bstep (se 1 (by rfl) ⟨3942170, by rfl⟩ : syracuseStep 5256227 = 7884341) B7884341
theorem B2766001 : Blo 1148636 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B1455347 : Blo 1148636 1455347 := bstep (se 1 (by rfl) ⟨1091510, by rfl⟩ : syracuseStep 1455347 = 2183021) B2183021
theorem B1750337 : Blo 1148636 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B8303971 : Blo 1148636 8303971 := bstep (se 1 (by rfl) ⟨6227978, by rfl⟩ : syracuseStep 8303971 = 12455957) B12455957
theorem B1750385 : Blo 1148636 1750385 := bstep (se 2 (by rfl) ⟨656394, by rfl⟩ : syracuseStep 1750385 = 1312789) B1312789
theorem B3880493 : Blo 1148636 3880493 := bstep (se 3 (by rfl) ⟨727592, by rfl⟩ : syracuseStep 3880493 = 1455185) B1455185
theorem B3880547 : Blo 1148636 3880547 := bstep (se 1 (by rfl) ⟨2910410, by rfl⟩ : syracuseStep 3880547 = 5820821) B5820821
theorem B27997973 : Blo 1148636 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B3880817 : Blo 1148636 3880817 := bstep (se 2 (by rfl) ⟨1455306, by rfl⟩ : syracuseStep 3880817 = 2910613) B2910613
theorem B1456051 : Blo 1148636 1456051 := bstep (se 1 (by rfl) ⟨1092038, by rfl⟩ : syracuseStep 1456051 = 2184077) B2184077
theorem B4372451 : Blo 1148636 4372451 := bstep (se 1 (by rfl) ⟨3279338, by rfl⟩ : syracuseStep 4372451 = 6558677) B6558677
theorem B1751041 : Blo 1148636 1751041 := bstep (se 2 (by rfl) ⟨656640, by rfl⟩ : syracuseStep 1751041 = 1313281) B1313281
theorem B1456147 : Blo 1148636 1456147 := bstep (se 1 (by rfl) ⟨1092110, by rfl⟩ : syracuseStep 1456147 = 2184221) B2184221
theorem B1292323 : Blo 1148636 1292323 := bstep (se 1 (by rfl) ⟨969242, by rfl⟩ : syracuseStep 1292323 = 1938485) B1938485
theorem B14956597 : Blo 1148636 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B1292467 : Blo 1148636 1292467 := bstep (se 1 (by rfl) ⟨969350, by rfl⟩ : syracuseStep 1292467 = 1938701) B1938701
theorem B1034926307 : Blo 1148636 1034926307 := bstep (se 1 (by rfl) ⟨776194730, by rfl⟩ : syracuseStep 1034926307 = 1552389461) B1552389461
theorem B1292611 : Blo 1148636 1292611 := bstep (se 1 (by rfl) ⟨969458, by rfl⟩ : syracuseStep 1292611 = 1938917) B1938917
theorem B14760305 : Blo 1148636 14760305 := bstep (se 2 (by rfl) ⟨5535114, by rfl⟩ : syracuseStep 14760305 = 11070229) B11070229
theorem B1554817 : Blo 1148636 1554817 := bstep (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) B1166113
theorem B3881357 : Blo 1148636 3881357 := bstep (se 3 (by rfl) ⟨727754, by rfl⟩ : syracuseStep 3881357 = 1455509) B1455509
theorem B1227155 : Blo 1148636 1227155 := bstep (se 1 (by rfl) ⟨920366, by rfl⟩ : syracuseStep 1227155 = 1840733) B1840733
theorem B3881411 : Blo 1148636 3881411 := bstep (se 1 (by rfl) ⟨2911058, by rfl⟩ : syracuseStep 3881411 = 5822117) B5822117
theorem B1292755 : Blo 1148636 1292755 := bstep (se 1 (by rfl) ⟨969566, by rfl⟩ : syracuseStep 1292755 = 1939133) B1939133
theorem B1456643 : Blo 1148636 1456643 := bstep (se 1 (by rfl) ⟨1092482, by rfl⟩ : syracuseStep 1456643 = 2184965) B2184965
theorem B1292899 : Blo 1148636 1292899 := bstep (se 1 (by rfl) ⟨969674, by rfl⟩ : syracuseStep 1292899 = 1939349) B1939349
theorem B3684977 : Blo 1148636 3684977 := bstep (se 2 (by rfl) ⟨1381866, by rfl⟩ : syracuseStep 3684977 = 2763733) B2763733
theorem B3685027 : Blo 1148636 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B5814989 : Blo 1148636 5814989 := bstep (se 3 (by rfl) ⟨1090310, by rfl⟩ : syracuseStep 5814989 = 2180621) B2180621
theorem B3881681 : Blo 1148636 3881681 := bstep (se 2 (by rfl) ⟨1455630, by rfl⟩ : syracuseStep 3881681 = 2911261) B2911261
theorem B1293043 : Blo 1148636 1293043 := bstep (se 1 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 1293043 = 1939565) B1939565
theorem B1293187 : Blo 1148636 1293187 := bstep (se 1 (by rfl) ⟨969890, by rfl⟩ : syracuseStep 1293187 = 1939781) B1939781
theorem B9812933 : Blo 1148636 9812933 := bstep (se 4 (by rfl) ⟨919962, by rfl⟩ : syracuseStep 9812933 = 1839925) B1839925
theorem B4373453 : Blo 1148636 4373453 := bstep (se 3 (by rfl) ⟨820022, by rfl⟩ : syracuseStep 4373453 = 1640045) B1640045
theorem B1293331 : Blo 1148636 1293331 := bstep (se 1 (by rfl) ⟨969998, by rfl⟩ : syracuseStep 1293331 = 1939997) B1939997
theorem B1227907 : Blo 1148636 1227907 := bstep (se 1 (by rfl) ⟨920930, by rfl⟩ : syracuseStep 1227907 = 1841861) B1841861
theorem B1293475 : Blo 1148636 1293475 := bstep (se 1 (by rfl) ⟨970106, by rfl⟩ : syracuseStep 1293475 = 1940213) B1940213
theorem B1752257 : Blo 1148636 1752257 := bstep (se 2 (by rfl) ⟨657096, by rfl⟩ : syracuseStep 1752257 = 1314193) B1314193
theorem B1457347 : Blo 1148636 1457347 := bstep (se 1 (by rfl) ⟨1093010, by rfl⟩ : syracuseStep 1457347 = 2186021) B2186021
theorem B3882221 : Blo 1148636 3882221 := bstep (se 3 (by rfl) ⟨727916, by rfl⟩ : syracuseStep 3882221 = 1455833) B1455833
theorem B3882275 : Blo 1148636 3882275 := bstep (se 1 (by rfl) ⟨2911706, by rfl⟩ : syracuseStep 3882275 = 5823413) B5823413
theorem B1457443 : Blo 1148636 1457443 := bstep (se 1 (by rfl) ⟨1093082, by rfl⟩ : syracuseStep 1457443 = 2186165) B2186165
theorem B1293619 : Blo 1148636 1293619 := bstep (se 1 (by rfl) ⟨970214, by rfl⟩ : syracuseStep 1293619 = 1940429) B1940429
theorem B3685745 : Blo 1148636 3685745 := bstep (se 2 (by rfl) ⟨1382154, by rfl⟩ : syracuseStep 3685745 = 2764309) B2764309
theorem B1293763 : Blo 1148636 1293763 := bstep (se 1 (by rfl) ⟨970322, by rfl⟩ : syracuseStep 1293763 = 1940645) B1940645
theorem B6995405 : Blo 1148636 6995405 := bstep (se 3 (by rfl) ⟨1311638, by rfl⟩ : syracuseStep 6995405 = 2623277) B2623277
theorem B3882545 : Blo 1148636 3882545 := bstep (se 2 (by rfl) ⟨1455954, by rfl⟩ : syracuseStep 3882545 = 2911909) B2911909
theorem B1293907 : Blo 1148636 1293907 := bstep (se 1 (by rfl) ⟨970430, by rfl⟩ : syracuseStep 1293907 = 1940861) B1940861
theorem B1294051 : Blo 1148636 1294051 := bstep (se 1 (by rfl) ⟨970538, by rfl⟩ : syracuseStep 1294051 = 1941077) B1941077
theorem B11058929 : Blo 1148636 11058929 := bstep (se 2 (by rfl) ⟨4147098, by rfl⟩ : syracuseStep 11058929 = 8294197) B8294197
theorem B1457939 : Blo 1148636 1457939 := bstep (se 1 (by rfl) ⟨1093454, by rfl⟩ : syracuseStep 1457939 = 2186909) B2186909
theorem B3686257 : Blo 1148636 3686257 := bstep (se 2 (by rfl) ⟨1382346, by rfl⟩ : syracuseStep 3686257 = 2764693) B2764693
theorem B1294195 : Blo 1148636 1294195 := bstep (se 1 (by rfl) ⟨970646, by rfl⟩ : syracuseStep 1294195 = 1941293) B1941293
theorem B42024845 : Blo 1148636 42024845 := bstep (se 3 (by rfl) ⟨7879658, by rfl⟩ : syracuseStep 42024845 = 15759317) B15759317
theorem B1294339 : Blo 1148636 1294339 := bstep (se 1 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 1294339 = 1941509) B1941509
theorem B3883085 : Blo 1148636 3883085 := bstep (se 3 (by rfl) ⟨728078, by rfl⟩ : syracuseStep 3883085 = 1456157) B1456157
theorem B10633315 : Blo 1148636 10633315 := bstep (se 1 (by rfl) ⟨7974986, by rfl⟩ : syracuseStep 10633315 = 15949973) B15949973
theorem B3883139 : Blo 1148636 3883139 := bstep (se 1 (by rfl) ⟨2912354, by rfl⟩ : syracuseStep 3883139 = 5824709) B5824709
theorem B1294483 : Blo 1148636 1294483 := bstep (se 1 (by rfl) ⟨970862, by rfl⟩ : syracuseStep 1294483 = 1941725) B1941725
theorem B1294627 : Blo 1148636 1294627 := bstep (se 1 (by rfl) ⟨970970, by rfl⟩ : syracuseStep 1294627 = 1941941) B1941941
theorem B4047185 : Blo 1148636 4047185 := bstep (se 2 (by rfl) ⟨1517694, by rfl⟩ : syracuseStep 4047185 = 3035389) B3035389
theorem B3883409 : Blo 1148636 3883409 := bstep (se 2 (by rfl) ⟨1456278, by rfl⟩ : syracuseStep 3883409 = 2912557) B2912557
theorem B1294771 : Blo 1148636 1294771 := bstep (se 1 (by rfl) ⟨971078, by rfl⟩ : syracuseStep 1294771 = 1942157) B1942157
theorem B1458643 : Blo 1148636 1458643 := bstep (se 1 (by rfl) ⟨1093982, by rfl⟩ : syracuseStep 1458643 = 2187965) B2187965
theorem B5521891 : Blo 1148636 5521891 := bstep (se 1 (by rfl) ⟨4141418, by rfl⟩ : syracuseStep 5521891 = 8282837) B8282837
theorem B1229299 : Blo 1148636 1229299 := bstep (se 1 (by rfl) ⟨921974, by rfl⟩ : syracuseStep 1229299 = 1843949) B1843949
theorem B1458739 : Blo 1148636 1458739 := bstep (se 1 (by rfl) ⟨1094054, by rfl⟩ : syracuseStep 1458739 = 2188109) B2188109
theorem B13091381 : Blo 1148636 13091381 := bstep (se 5 (by rfl) ⟨613658, by rfl⟩ : syracuseStep 13091381 = 1227317) B1227317
theorem B1294915 : Blo 1148636 1294915 := bstep (se 1 (by rfl) ⟨971186, by rfl⟩ : syracuseStep 1294915 = 1942373) B1942373
theorem B1295059 : Blo 1148636 1295059 := bstep (se 1 (by rfl) ⟨971294, by rfl⟩ : syracuseStep 1295059 = 1942589) B1942589
theorem B1327907 : Blo 1148636 1327907 := bstep (se 1 (by rfl) ⟨995930, by rfl⟩ : syracuseStep 1327907 = 1991861) B1991861
theorem B1295203 : Blo 1148636 1295203 := bstep (se 1 (by rfl) ⟨971402, by rfl⟩ : syracuseStep 1295203 = 1942805) B1942805
theorem B3883949 : Blo 1148636 3883949 := bstep (se 3 (by rfl) ⟨728240, by rfl⟩ : syracuseStep 3883949 = 1456481) B1456481
theorem B3687373 : Blo 1148636 3687373 := bstep (se 3 (by rfl) ⟨691382, by rfl⟩ : syracuseStep 3687373 = 1382765) B1382765
theorem B3884003 : Blo 1148636 3884003 := bstep (se 1 (by rfl) ⟨2913002, by rfl⟩ : syracuseStep 3884003 = 5826005) B5826005
theorem B1295347 : Blo 1148636 1295347 := bstep (se 1 (by rfl) ⟨971510, by rfl⟩ : syracuseStep 1295347 = 1943021) B1943021
theorem B3687437 : Blo 1148636 3687437 := bstep (se 3 (by rfl) ⟨691394, by rfl⟩ : syracuseStep 3687437 = 1382789) B1382789
theorem B4375565 : Blo 1148636 4375565 := bstep (se 3 (by rfl) ⟨820418, by rfl⟩ : syracuseStep 4375565 = 1640837) B1640837
theorem B1295491 : Blo 1148636 1295491 := bstep (se 1 (by rfl) ⟨971618, by rfl⟩ : syracuseStep 1295491 = 1943237) B1943237
theorem B6210701 : Blo 1148636 6210701 := bstep (se 3 (by rfl) ⟨1164506, by rfl⟩ : syracuseStep 6210701 = 2329013) B2329013
theorem B1164515 : Blo 1148636 1164515 := bstep (se 1 (by rfl) ⟨873386, by rfl⟩ : syracuseStep 1164515 = 1746773) B1746773
theorem B3884273 : Blo 1148636 3884273 := bstep (se 2 (by rfl) ⟨1456602, by rfl⟩ : syracuseStep 3884273 = 2913205) B2913205
theorem B1295635 : Blo 1148636 1295635 := bstep (se 1 (by rfl) ⟨971726, by rfl⟩ : syracuseStep 1295635 = 1943453) B1943453
theorem B1295779 : Blo 1148636 1295779 := bstep (se 1 (by rfl) ⟨971834, by rfl⟩ : syracuseStep 1295779 = 1943669) B1943669
theorem B5817905 : Blo 1148636 5817905 := bstep (se 2 (by rfl) ⟨2181714, by rfl⟩ : syracuseStep 5817905 = 4363429) B4363429
theorem B1295923 : Blo 1148636 1295923 := bstep (se 1 (by rfl) ⟨971942, by rfl⟩ : syracuseStep 1295923 = 1943885) B1943885
theorem B2180675 : Blo 1148636 2180675 := bstep (se 1 (by rfl) ⟨1635506, by rfl⟩ : syracuseStep 2180675 = 3271013) B3271013
theorem B3032771 : Blo 1148636 3032771 := bstep (se 1 (by rfl) ⟨2274578, by rfl⟩ : syracuseStep 3032771 = 4549157) B4549157
theorem B1296067 : Blo 1148636 1296067 := bstep (se 1 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 1296067 = 1944101) B1944101
theorem B3884813 : Blo 1148636 3884813 := bstep (se 3 (by rfl) ⟨728402, by rfl⟩ : syracuseStep 3884813 = 1456805) B1456805
theorem B4671245 : Blo 1148636 4671245 := bstep (se 3 (by rfl) ⟨875858, by rfl⟩ : syracuseStep 4671245 = 1751717) B1751717
theorem B4376369 : Blo 1148636 4376369 := bstep (se 2 (by rfl) ⟨1641138, by rfl⟩ : syracuseStep 4376369 = 3282277) B3282277
theorem B3884867 : Blo 1148636 3884867 := bstep (se 1 (by rfl) ⟨2913650, by rfl⟩ : syracuseStep 3884867 = 5827301) B5827301
theorem B1296211 : Blo 1148636 1296211 := bstep (se 1 (by rfl) ⟨972158, by rfl⟩ : syracuseStep 1296211 = 1944317) B1944317
theorem B1296355 : Blo 1148636 1296355 := bstep (se 1 (by rfl) ⟨972266, by rfl⟩ : syracuseStep 1296355 = 1944533) B1944533
theorem B4147213 : Blo 1148636 4147213 := bstep (se 3 (by rfl) ⟨777602, by rfl⟩ : syracuseStep 4147213 = 1555205) B1555205
theorem B3885137 : Blo 1148636 3885137 := bstep (se 2 (by rfl) ⟨1456926, by rfl⟩ : syracuseStep 3885137 = 2913853) B2913853
theorem B1296499 : Blo 1148636 1296499 := bstep (se 1 (by rfl) ⟨972374, by rfl⟩ : syracuseStep 1296499 = 1944749) B1944749
theorem B1296643 : Blo 1148636 1296643 := bstep (se 1 (by rfl) ⟨972482, by rfl⟩ : syracuseStep 1296643 = 1944965) B1944965
theorem B14764301 : Blo 1148636 14764301 := bstep (se 3 (by rfl) ⟨2768306, by rfl⟩ : syracuseStep 14764301 = 5536613) B5536613
theorem B1722977 : Blo 1148636 1722977 := bstep (se 2 (by rfl) ⟨646116, by rfl⟩ : syracuseStep 1722977 = 1292233) B1292233
theorem B3885677 : Blo 1148636 3885677 := bstep (se 3 (by rfl) ⟨728564, by rfl⟩ : syracuseStep 3885677 = 1457129) B1457129
theorem B2181745 : Blo 1148636 2181745 := bstep (se 2 (by rfl) ⟨818154, by rfl⟩ : syracuseStep 2181745 = 1636309) B1636309
theorem B1722995 : Blo 1148636 1722995 := bstep (se 1 (by rfl) ⟨1292246, by rfl⟩ : syracuseStep 1722995 = 2584493) B2584493
theorem B1723025 : Blo 1148636 1723025 := bstep (se 2 (by rfl) ⟨646134, by rfl⟩ : syracuseStep 1723025 = 1292269) B1292269
theorem B1723043 : Blo 1148636 1723043 := bstep (se 1 (by rfl) ⟨1292282, by rfl⟩ : syracuseStep 1723043 = 2584565) B2584565
theorem B3885731 : Blo 1148636 3885731 := bstep (se 1 (by rfl) ⟨2914298, by rfl⟩ : syracuseStep 3885731 = 5828597) B5828597
theorem B1723073 : Blo 1148636 1723073 := bstep (se 2 (by rfl) ⟨646152, by rfl⟩ : syracuseStep 1723073 = 1292305) B1292305
theorem B1723091 : Blo 1148636 1723091 := bstep (se 1 (by rfl) ⟨1292318, by rfl⟩ : syracuseStep 1723091 = 2584637) B2584637
theorem B1723121 : Blo 1148636 1723121 := bstep (se 2 (by rfl) ⟨646170, by rfl⟩ : syracuseStep 1723121 = 1292341) B1292341
theorem B1723139 : Blo 1148636 1723139 := bstep (se 1 (by rfl) ⟨1292354, by rfl⟩ : syracuseStep 1723139 = 2584709) B2584709
theorem B3689219 : Blo 1148636 3689219 := bstep (se 1 (by rfl) ⟨2766914, by rfl⟩ : syracuseStep 3689219 = 5533829) B5533829
theorem B1723169 : Blo 1148636 1723169 := bstep (se 2 (by rfl) ⟨646188, by rfl⟩ : syracuseStep 1723169 = 1292377) B1292377
theorem B1723187 : Blo 1148636 1723187 := bstep (se 1 (by rfl) ⟨1292390, by rfl⟩ : syracuseStep 1723187 = 2584781) B2584781
theorem B1723217 : Blo 1148636 1723217 := bstep (se 2 (by rfl) ⟨646206, by rfl⟩ : syracuseStep 1723217 = 1292413) B1292413
theorem B1723235 : Blo 1148636 1723235 := bstep (se 1 (by rfl) ⟨1292426, by rfl⟩ : syracuseStep 1723235 = 2584853) B2584853
theorem B1723265 : Blo 1148636 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B1723283 : Blo 1148636 1723283 := bstep (se 1 (by rfl) ⟨1292462, by rfl⟩ : syracuseStep 1723283 = 2584925) B2584925
theorem B1723313 : Blo 1148636 1723313 := bstep (se 2 (by rfl) ⟨646242, by rfl⟩ : syracuseStep 1723313 = 1292485) B1292485
theorem B3886001 : Blo 1148636 3886001 := bstep (se 2 (by rfl) ⟨1457250, by rfl⟩ : syracuseStep 3886001 = 2914501) B2914501
theorem B1723331 : Blo 1148636 1723331 := bstep (se 1 (by rfl) ⟨1292498, by rfl⟩ : syracuseStep 1723331 = 2584997) B2584997
theorem B1166275 : Blo 1148636 1166275 := bstep (se 1 (by rfl) ⟨874706, by rfl⟩ : syracuseStep 1166275 = 1749413) B1749413
theorem B1723361 : Blo 1148636 1723361 := bstep (se 2 (by rfl) ⟨646260, by rfl⟩ : syracuseStep 1723361 = 1292521) B1292521
theorem B5819363 : Blo 1148636 5819363 := bstep (se 1 (by rfl) ⟨4364522, by rfl⟩ : syracuseStep 5819363 = 8729045) B8729045
theorem B5524465 : Blo 1148636 5524465 := bstep (se 2 (by rfl) ⟨2071674, by rfl⟩ : syracuseStep 5524465 = 4143349) B4143349
theorem B1723379 : Blo 1148636 1723379 := bstep (se 1 (by rfl) ⟨1292534, by rfl⟩ : syracuseStep 1723379 = 2585069) B2585069
theorem B1723409 : Blo 1148636 1723409 := bstep (se 2 (by rfl) ⟨646278, by rfl⟩ : syracuseStep 1723409 = 1292557) B1292557
theorem B1723427 : Blo 1148636 1723427 := bstep (se 1 (by rfl) ⟨1292570, by rfl⟩ : syracuseStep 1723427 = 2585141) B2585141
theorem B1723457 : Blo 1148636 1723457 := bstep (se 2 (by rfl) ⟨646296, by rfl⟩ : syracuseStep 1723457 = 1292593) B1292593
theorem B1723475 : Blo 1148636 1723475 := bstep (se 1 (by rfl) ⟨1292606, by rfl⟩ : syracuseStep 1723475 = 2585213) B2585213
theorem B1723505 : Blo 1148636 1723505 := bstep (se 2 (by rfl) ⟨646314, by rfl⟩ : syracuseStep 1723505 = 1292629) B1292629
theorem B1723523 : Blo 1148636 1723523 := bstep (se 1 (by rfl) ⟨1292642, by rfl⟩ : syracuseStep 1723523 = 2585285) B2585285
theorem B1723553 : Blo 1148636 1723553 := bstep (se 2 (by rfl) ⟨646332, by rfl⟩ : syracuseStep 1723553 = 1292665) B1292665
theorem B1723571 : Blo 1148636 1723571 := bstep (se 1 (by rfl) ⟨1292678, by rfl⟩ : syracuseStep 1723571 = 2585357) B2585357
theorem B1723601 : Blo 1148636 1723601 := bstep (se 2 (by rfl) ⟨646350, by rfl⟩ : syracuseStep 1723601 = 1292701) B1292701
theorem B1723619 : Blo 1148636 1723619 := bstep (se 1 (by rfl) ⟨1292714, by rfl⟩ : syracuseStep 1723619 = 2585429) B2585429
theorem B1723649 : Blo 1148636 1723649 := bstep (se 2 (by rfl) ⟨646368, by rfl⟩ : syracuseStep 1723649 = 1292737) B1292737
theorem B1723667 : Blo 1148636 1723667 := bstep (se 1 (by rfl) ⟨1292750, by rfl⟩ : syracuseStep 1723667 = 2585501) B2585501
theorem B1723697 : Blo 1148636 1723697 := bstep (se 2 (by rfl) ⟨646386, by rfl⟩ : syracuseStep 1723697 = 1292773) B1292773
theorem B1723715 : Blo 1148636 1723715 := bstep (se 1 (by rfl) ⟨1292786, by rfl⟩ : syracuseStep 1723715 = 2585573) B2585573
theorem B1723745 : Blo 1148636 1723745 := bstep (se 2 (by rfl) ⟨646404, by rfl⟩ : syracuseStep 1723745 = 1292809) B1292809
theorem B1723763 : Blo 1148636 1723763 := bstep (se 1 (by rfl) ⟨1292822, by rfl⟩ : syracuseStep 1723763 = 2585645) B2585645
theorem B1723793 : Blo 1148636 1723793 := bstep (se 2 (by rfl) ⟨646422, by rfl⟩ : syracuseStep 1723793 = 1292845) B1292845
theorem B1723811 : Blo 1148636 1723811 := bstep (se 1 (by rfl) ⟨1292858, by rfl⟩ : syracuseStep 1723811 = 2585717) B2585717
theorem B14732725 : Blo 1148636 14732725 := bstep (se 5 (by rfl) ⟨690596, by rfl⟩ : syracuseStep 14732725 = 1381193) B1381193
theorem B14011829 : Blo 1148636 14011829 := bstep (se 5 (by rfl) ⟨656804, by rfl⟩ : syracuseStep 14011829 = 1313609) B1313609
theorem B1723841 : Blo 1148636 1723841 := bstep (se 2 (by rfl) ⟨646440, by rfl⟩ : syracuseStep 1723841 = 1292881) B1292881
theorem B3886541 : Blo 1148636 3886541 := bstep (se 3 (by rfl) ⟨728726, by rfl⟩ : syracuseStep 3886541 = 1457453) B1457453
theorem B1723859 : Blo 1148636 1723859 := bstep (se 1 (by rfl) ⟨1292894, by rfl⟩ : syracuseStep 1723859 = 2585789) B2585789
theorem B1723889 : Blo 1148636 1723889 := bstep (se 2 (by rfl) ⟨646458, by rfl⟩ : syracuseStep 1723889 = 1292917) B1292917
theorem B3886595 : Blo 1148636 3886595 := bstep (se 1 (by rfl) ⟨2914946, by rfl⟩ : syracuseStep 3886595 = 5829893) B5829893
theorem B1723907 : Blo 1148636 1723907 := bstep (se 1 (by rfl) ⟨1292930, by rfl⟩ : syracuseStep 1723907 = 2585861) B2585861
theorem B1723937 : Blo 1148636 1723937 := bstep (se 2 (by rfl) ⟨646476, by rfl⟩ : syracuseStep 1723937 = 1292953) B1292953
theorem B1723955 : Blo 1148636 1723955 := bstep (se 1 (by rfl) ⟨1292966, by rfl⟩ : syracuseStep 1723955 = 2585933) B2585933
theorem B1723985 : Blo 1148636 1723985 := bstep (se 2 (by rfl) ⟨646494, by rfl⟩ : syracuseStep 1723985 = 1292989) B1292989
theorem B1724003 : Blo 1148636 1724003 := bstep (se 1 (by rfl) ⟨1293002, by rfl⟩ : syracuseStep 1724003 = 2586005) B2586005
theorem B1724033 : Blo 1148636 1724033 := bstep (se 2 (by rfl) ⟨646512, by rfl⟩ : syracuseStep 1724033 = 1293025) B1293025
theorem B11062925 : Blo 1148636 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B2182801 : Blo 1148636 2182801 := bstep (se 2 (by rfl) ⟨818550, by rfl⟩ : syracuseStep 2182801 = 1637101) B1637101
theorem B1724051 : Blo 1148636 1724051 := bstep (se 1 (by rfl) ⟨1293038, by rfl⟩ : syracuseStep 1724051 = 2586077) B2586077
theorem B1724081 : Blo 1148636 1724081 := bstep (se 2 (by rfl) ⟨646530, by rfl⟩ : syracuseStep 1724081 = 1293061) B1293061
theorem B1724099 : Blo 1148636 1724099 := bstep (se 1 (by rfl) ⟨1293074, by rfl⟩ : syracuseStep 1724099 = 2586149) B2586149
theorem B1724129 : Blo 1148636 1724129 := bstep (se 2 (by rfl) ⟨646548, by rfl⟩ : syracuseStep 1724129 = 1293097) B1293097
theorem B1724147 : Blo 1148636 1724147 := bstep (se 1 (by rfl) ⟨1293110, by rfl⟩ : syracuseStep 1724147 = 2586221) B2586221
theorem B5820173 : Blo 1148636 5820173 := bstep (se 3 (by rfl) ⟨1091282, by rfl⟩ : syracuseStep 5820173 = 2182565) B2182565
theorem B7884557 : Blo 1148636 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B3886865 : Blo 1148636 3886865 := bstep (se 2 (by rfl) ⟨1457574, by rfl⟩ : syracuseStep 3886865 = 2915149) B2915149
theorem B1724177 : Blo 1148636 1724177 := bstep (se 2 (by rfl) ⟨646566, by rfl⟩ : syracuseStep 1724177 = 1293133) B1293133
theorem B1658659 : Blo 1148636 1658659 := bstep (se 1 (by rfl) ⟨1243994, by rfl⟩ : syracuseStep 1658659 = 2487989) B2487989
theorem B1724195 : Blo 1148636 1724195 := bstep (se 1 (by rfl) ⟨1293146, by rfl⟩ : syracuseStep 1724195 = 2586293) B2586293
theorem B1724225 : Blo 1148636 1724225 := bstep (se 2 (by rfl) ⟨646584, by rfl⟩ : syracuseStep 1724225 = 1293169) B1293169
theorem B1724243 : Blo 1148636 1724243 := bstep (se 1 (by rfl) ⟨1293182, by rfl⟩ : syracuseStep 1724243 = 2586365) B2586365
theorem B1724273 : Blo 1148636 1724273 := bstep (se 2 (by rfl) ⟨646602, by rfl⟩ : syracuseStep 1724273 = 1293205) B1293205
theorem B1724291 : Blo 1148636 1724291 := bstep (se 1 (by rfl) ⟨1293218, by rfl⟩ : syracuseStep 1724291 = 2586437) B2586437
theorem B1724321 : Blo 1148636 1724321 := bstep (se 2 (by rfl) ⟨646620, by rfl⟩ : syracuseStep 1724321 = 1293241) B1293241
theorem B1724339 : Blo 1148636 1724339 := bstep (se 1 (by rfl) ⟨1293254, by rfl⟩ : syracuseStep 1724339 = 2586509) B2586509
theorem B1724369 : Blo 1148636 1724369 := bstep (se 2 (by rfl) ⟨646638, by rfl⟩ : syracuseStep 1724369 = 1293277) B1293277
theorem B1724387 : Blo 1148636 1724387 := bstep (se 1 (by rfl) ⟨1293290, by rfl⟩ : syracuseStep 1724387 = 2586581) B2586581
theorem B1724417 : Blo 1148636 1724417 := bstep (se 2 (by rfl) ⟨646656, by rfl⟩ : syracuseStep 1724417 = 1293313) B1293313
theorem B12439565 : Blo 1148636 12439565 := bstep (se 3 (by rfl) ⟨2332418, by rfl⟩ : syracuseStep 12439565 = 4664837) B4664837
theorem B1724435 : Blo 1148636 1724435 := bstep (se 1 (by rfl) ⟨1293326, by rfl⟩ : syracuseStep 1724435 = 2586653) B2586653
theorem B2183203 : Blo 1148636 2183203 := bstep (se 1 (by rfl) ⟨1637402, by rfl⟩ : syracuseStep 2183203 = 3274805) B3274805
theorem B1724465 : Blo 1148636 1724465 := bstep (se 2 (by rfl) ⟨646674, by rfl⟩ : syracuseStep 1724465 = 1293349) B1293349
theorem B1724483 : Blo 1148636 1724483 := bstep (se 1 (by rfl) ⟨1293362, by rfl⟩ : syracuseStep 1724483 = 2586725) B2586725
theorem B2183249 : Blo 1148636 2183249 := bstep (se 2 (by rfl) ⟨818718, by rfl⟩ : syracuseStep 2183249 = 1637437) B1637437
theorem B1724513 : Blo 1148636 1724513 := bstep (se 2 (by rfl) ⟨646692, by rfl⟩ : syracuseStep 1724513 = 1293385) B1293385
theorem B1724531 : Blo 1148636 1724531 := bstep (se 1 (by rfl) ⟨1293398, by rfl⟩ : syracuseStep 1724531 = 2586797) B2586797
theorem B1167491 : Blo 1148636 1167491 := bstep (se 1 (by rfl) ⟨875618, by rfl⟩ : syracuseStep 1167491 = 1751237) B1751237
theorem B1724561 : Blo 1148636 1724561 := bstep (se 2 (by rfl) ⟨646710, by rfl⟩ : syracuseStep 1724561 = 1293421) B1293421
theorem B1724579 : Blo 1148636 1724579 := bstep (se 1 (by rfl) ⟨1293434, by rfl⟩ : syracuseStep 1724579 = 2586869) B2586869
theorem B1724609 : Blo 1148636 1724609 := bstep (se 2 (by rfl) ⟨646728, by rfl⟩ : syracuseStep 1724609 = 1293457) B1293457
theorem B1724627 : Blo 1148636 1724627 := bstep (se 1 (by rfl) ⟨1293470, by rfl⟩ : syracuseStep 1724627 = 2586941) B2586941
theorem B1724657 : Blo 1148636 1724657 := bstep (se 2 (by rfl) ⟨646746, by rfl⟩ : syracuseStep 1724657 = 1293493) B1293493
theorem B1724675 : Blo 1148636 1724675 := bstep (se 1 (by rfl) ⟨1293506, by rfl⟩ : syracuseStep 1724675 = 2587013) B2587013
theorem B1724705 : Blo 1148636 1724705 := bstep (se 2 (by rfl) ⟨646764, by rfl⟩ : syracuseStep 1724705 = 1293529) B1293529
theorem B3887405 : Blo 1148636 3887405 := bstep (se 3 (by rfl) ⟨728888, by rfl⟩ : syracuseStep 3887405 = 1457777) B1457777
theorem B1724723 : Blo 1148636 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B1724753 : Blo 1148636 1724753 := bstep (se 2 (by rfl) ⟨646782, by rfl⟩ : syracuseStep 1724753 = 1293565) B1293565
theorem B1724771 : Blo 1148636 1724771 := bstep (se 1 (by rfl) ⟨1293578, by rfl⟩ : syracuseStep 1724771 = 2587157) B2587157
theorem B3887459 : Blo 1148636 3887459 := bstep (se 1 (by rfl) ⟨2915594, by rfl⟩ : syracuseStep 3887459 = 5831189) B5831189
theorem B2183537 : Blo 1148636 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B1724801 : Blo 1148636 1724801 := bstep (se 2 (by rfl) ⟨646800, by rfl⟩ : syracuseStep 1724801 = 1293601) B1293601
theorem B1724819 : Blo 1148636 1724819 := bstep (se 1 (by rfl) ⟨1293614, by rfl⟩ : syracuseStep 1724819 = 2587229) B2587229
theorem B1724849 : Blo 1148636 1724849 := bstep (se 2 (by rfl) ⟨646818, by rfl⟩ : syracuseStep 1724849 = 1293637) B1293637
theorem B1724867 : Blo 1148636 1724867 := bstep (se 1 (by rfl) ⟨1293650, by rfl⟩ : syracuseStep 1724867 = 2587301) B2587301
theorem B1724897 : Blo 1148636 1724897 := bstep (se 2 (by rfl) ⟨646836, by rfl⟩ : syracuseStep 1724897 = 1293673) B1293673
theorem B1724915 : Blo 1148636 1724915 := bstep (se 1 (by rfl) ⟨1293686, by rfl⟩ : syracuseStep 1724915 = 2587373) B2587373
theorem B1724945 : Blo 1148636 1724945 := bstep (se 2 (by rfl) ⟨646854, by rfl⟩ : syracuseStep 1724945 = 1293709) B1293709
theorem B1724963 : Blo 1148636 1724963 := bstep (se 1 (by rfl) ⟨1293722, by rfl⟩ : syracuseStep 1724963 = 2587445) B2587445
theorem B1724993 : Blo 1148636 1724993 := bstep (se 2 (by rfl) ⟨646872, by rfl⟩ : syracuseStep 1724993 = 1293745) B1293745
theorem B1725011 : Blo 1148636 1725011 := bstep (se 1 (by rfl) ⟨1293758, by rfl⟩ : syracuseStep 1725011 = 2587517) B2587517
theorem B1725041 : Blo 1148636 1725041 := bstep (se 2 (by rfl) ⟨646890, by rfl⟩ : syracuseStep 1725041 = 1293781) B1293781
theorem B3887729 : Blo 1148636 3887729 := bstep (se 2 (by rfl) ⟨1457898, by rfl⟩ : syracuseStep 3887729 = 2915797) B2915797
theorem B1725059 : Blo 1148636 1725059 := bstep (se 1 (by rfl) ⟨1293794, by rfl⟩ : syracuseStep 1725059 = 2587589) B2587589
theorem B5526157 : Blo 1148636 5526157 := bstep (se 3 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 5526157 = 2072309) B2072309
theorem B2216593 : Blo 1148636 2216593 := bstep (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) B1662445
theorem B1725089 : Blo 1148636 1725089 := bstep (se 2 (by rfl) ⟨646908, by rfl⟩ : syracuseStep 1725089 = 1293817) B1293817
theorem B1725107 : Blo 1148636 1725107 := bstep (se 1 (by rfl) ⟨1293830, by rfl⟩ : syracuseStep 1725107 = 2587661) B2587661
theorem B1725137 : Blo 1148636 1725137 := bstep (se 2 (by rfl) ⟨646926, by rfl⟩ : syracuseStep 1725137 = 1293853) B1293853
theorem B1725155 : Blo 1148636 1725155 := bstep (se 1 (by rfl) ⟨1293866, by rfl⟩ : syracuseStep 1725155 = 2587733) B2587733
theorem B1725185 : Blo 1148636 1725185 := bstep (se 2 (by rfl) ⟨646944, by rfl⟩ : syracuseStep 1725185 = 1293889) B1293889
theorem B1725203 : Blo 1148636 1725203 := bstep (se 1 (by rfl) ⟨1293902, by rfl⟩ : syracuseStep 1725203 = 2587805) B2587805
theorem B1725233 : Blo 1148636 1725233 := bstep (se 2 (by rfl) ⟨646962, by rfl⟩ : syracuseStep 1725233 = 1293925) B1293925
theorem B1725251 : Blo 1148636 1725251 := bstep (se 1 (by rfl) ⟨1293938, by rfl⟩ : syracuseStep 1725251 = 2587877) B2587877
theorem B1725281 : Blo 1148636 1725281 := bstep (se 2 (by rfl) ⟨646980, by rfl⟩ : syracuseStep 1725281 = 1293961) B1293961
theorem B1725299 : Blo 1148636 1725299 := bstep (se 1 (by rfl) ⟨1293974, by rfl⟩ : syracuseStep 1725299 = 2587949) B2587949
theorem B1725329 : Blo 1148636 1725329 := bstep (se 2 (by rfl) ⟨646998, by rfl⟩ : syracuseStep 1725329 = 1293997) B1293997
theorem B1725347 : Blo 1148636 1725347 := bstep (se 1 (by rfl) ⟨1294010, by rfl⟩ : syracuseStep 1725347 = 2588021) B2588021
theorem B1725377 : Blo 1148636 1725377 := bstep (se 2 (by rfl) ⟨647016, by rfl⟩ : syracuseStep 1725377 = 1294033) B1294033
theorem B1725395 : Blo 1148636 1725395 := bstep (se 1 (by rfl) ⟨1294046, by rfl⟩ : syracuseStep 1725395 = 2588093) B2588093
theorem B1725425 : Blo 1148636 1725425 := bstep (se 2 (by rfl) ⟨647034, by rfl⟩ : syracuseStep 1725425 = 1294069) B1294069
theorem B1725443 : Blo 1148636 1725443 := bstep (se 1 (by rfl) ⟨1294082, by rfl⟩ : syracuseStep 1725443 = 2588165) B2588165
theorem B1725473 : Blo 1148636 1725473 := bstep (se 2 (by rfl) ⟨647052, by rfl⟩ : syracuseStep 1725473 = 1294105) B1294105
theorem B1725491 : Blo 1148636 1725491 := bstep (se 1 (by rfl) ⟨1294118, by rfl⟩ : syracuseStep 1725491 = 2588237) B2588237
theorem B2184259 : Blo 1148636 2184259 := bstep (se 1 (by rfl) ⟨1638194, by rfl⟩ : syracuseStep 2184259 = 3276389) B3276389
theorem B1725521 : Blo 1148636 1725521 := bstep (se 2 (by rfl) ⟨647070, by rfl⟩ : syracuseStep 1725521 = 1294141) B1294141
theorem B2217041 : Blo 1148636 2217041 := bstep (se 2 (by rfl) ⟨831390, by rfl⟩ : syracuseStep 2217041 = 1662781) B1662781
theorem B1725539 : Blo 1148636 1725539 := bstep (se 1 (by rfl) ⟨1294154, by rfl⟩ : syracuseStep 1725539 = 2588309) B2588309
theorem B1725569 : Blo 1148636 1725569 := bstep (se 2 (by rfl) ⟨647088, by rfl⟩ : syracuseStep 1725569 = 1294177) B1294177
theorem B3888269 : Blo 1148636 3888269 := bstep (se 3 (by rfl) ⟨729050, by rfl⟩ : syracuseStep 3888269 = 1458101) B1458101
theorem B1725587 : Blo 1148636 1725587 := bstep (se 1 (by rfl) ⟨1294190, by rfl⟩ : syracuseStep 1725587 = 2588381) B2588381
theorem B1725617 : Blo 1148636 1725617 := bstep (se 2 (by rfl) ⟨647106, by rfl⟩ : syracuseStep 1725617 = 1294213) B1294213
theorem B1725635 : Blo 1148636 1725635 := bstep (se 1 (by rfl) ⟨1294226, by rfl⟩ : syracuseStep 1725635 = 2588453) B2588453
theorem B3888323 : Blo 1148636 3888323 := bstep (se 1 (by rfl) ⟨2916242, by rfl⟩ : syracuseStep 3888323 = 5832485) B5832485
theorem B1725665 : Blo 1148636 1725665 := bstep (se 2 (by rfl) ⟨647124, by rfl⟩ : syracuseStep 1725665 = 1294249) B1294249
theorem B4150499 : Blo 1148636 4150499 := bstep (se 1 (by rfl) ⟨3112874, by rfl⟩ : syracuseStep 4150499 = 6225749) B6225749
theorem B5526755 : Blo 1148636 5526755 := bstep (se 1 (by rfl) ⟨4145066, by rfl⟩ : syracuseStep 5526755 = 8290133) B8290133
theorem B1725683 : Blo 1148636 1725683 := bstep (se 1 (by rfl) ⟨1294262, by rfl⟩ : syracuseStep 1725683 = 2588525) B2588525
theorem B1725713 : Blo 1148636 1725713 := bstep (se 2 (by rfl) ⟨647142, by rfl⟩ : syracuseStep 1725713 = 1294285) B1294285
theorem B3691793 : Blo 1148636 3691793 := bstep (se 2 (by rfl) ⟨1384422, by rfl⟩ : syracuseStep 3691793 = 2768845) B2768845
theorem B1725731 : Blo 1148636 1725731 := bstep (se 1 (by rfl) ⟨1294298, by rfl⟩ : syracuseStep 1725731 = 2588597) B2588597
theorem B1725761 : Blo 1148636 1725761 := bstep (se 2 (by rfl) ⟨647160, by rfl⟩ : syracuseStep 1725761 = 1294321) B1294321
theorem B1725779 : Blo 1148636 1725779 := bstep (se 1 (by rfl) ⟨1294334, by rfl⟩ : syracuseStep 1725779 = 2588669) B2588669
theorem B1725809 : Blo 1148636 1725809 := bstep (se 2 (by rfl) ⟨647178, by rfl⟩ : syracuseStep 1725809 = 1294357) B1294357
theorem B18666865 : Blo 1148636 18666865 := bstep (se 2 (by rfl) ⟨7000074, by rfl⟩ : syracuseStep 18666865 = 14000149) B14000149
theorem B1725827 : Blo 1148636 1725827 := bstep (se 1 (by rfl) ⟨1294370, by rfl⟩ : syracuseStep 1725827 = 2588741) B2588741
theorem B1725857 : Blo 1148636 1725857 := bstep (se 2 (by rfl) ⟨647196, by rfl⟩ : syracuseStep 1725857 = 1294393) B1294393
theorem B1725875 : Blo 1148636 1725875 := bstep (se 1 (by rfl) ⟨1294406, by rfl⟩ : syracuseStep 1725875 = 2588813) B2588813
theorem B1725905 : Blo 1148636 1725905 := bstep (se 2 (by rfl) ⟨647214, by rfl⟩ : syracuseStep 1725905 = 1294429) B1294429
theorem B3888593 : Blo 1148636 3888593 := bstep (se 2 (by rfl) ⟨1458222, by rfl⟩ : syracuseStep 3888593 = 2916445) B2916445
theorem B1725923 : Blo 1148636 1725923 := bstep (se 1 (by rfl) ⟨1294442, by rfl⟩ : syracuseStep 1725923 = 2588885) B2588885
theorem B1725953 : Blo 1148636 1725953 := bstep (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) B1294465
theorem B2184707 : Blo 1148636 2184707 := bstep (se 1 (by rfl) ⟨1638530, by rfl⟩ : syracuseStep 2184707 = 3277061) B3277061
theorem B1725971 : Blo 1148636 1725971 := bstep (se 1 (by rfl) ⟨1294478, by rfl⟩ : syracuseStep 1725971 = 2588957) B2588957
theorem B1726001 : Blo 1148636 1726001 := bstep (se 2 (by rfl) ⟨647250, by rfl⟩ : syracuseStep 1726001 = 1294501) B1294501
theorem B1726019 : Blo 1148636 1726019 := bstep (se 1 (by rfl) ⟨1294514, by rfl⟩ : syracuseStep 1726019 = 2589029) B2589029
theorem B1726049 : Blo 1148636 1726049 := bstep (se 2 (by rfl) ⟨647268, by rfl⟩ : syracuseStep 1726049 = 1294537) B1294537
theorem B7362161 : Blo 1148636 7362161 := bstep (se 2 (by rfl) ⟨2760810, by rfl⟩ : syracuseStep 7362161 = 5521621) B5521621
theorem B1726067 : Blo 1148636 1726067 := bstep (se 1 (by rfl) ⟨1294550, by rfl⟩ : syracuseStep 1726067 = 2589101) B2589101
theorem B1726097 : Blo 1148636 1726097 := bstep (se 2 (by rfl) ⟨647286, by rfl⟩ : syracuseStep 1726097 = 1294573) B1294573
theorem B1726115 : Blo 1148636 1726115 := bstep (se 1 (by rfl) ⟨1294586, by rfl⟩ : syracuseStep 1726115 = 2589173) B2589173
theorem B5527217 : Blo 1148636 5527217 := bstep (se 2 (by rfl) ⟨2072706, by rfl⟩ : syracuseStep 5527217 = 4145413) B4145413
theorem B1726145 : Blo 1148636 1726145 := bstep (se 2 (by rfl) ⟨647304, by rfl⟩ : syracuseStep 1726145 = 1294609) B1294609
theorem B1726163 : Blo 1148636 1726163 := bstep (se 1 (by rfl) ⟨1294622, by rfl⟩ : syracuseStep 1726163 = 2589245) B2589245
theorem B1726193 : Blo 1148636 1726193 := bstep (se 2 (by rfl) ⟨647322, by rfl⟩ : syracuseStep 1726193 = 1294645) B1294645
theorem B1726211 : Blo 1148636 1726211 := bstep (se 1 (by rfl) ⟨1294658, by rfl⟩ : syracuseStep 1726211 = 2589317) B2589317
theorem B1726241 : Blo 1148636 1726241 := bstep (se 2 (by rfl) ⟨647340, by rfl⟩ : syracuseStep 1726241 = 1294681) B1294681
theorem B6543139 : Blo 1148636 6543139 := bstep (se 1 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 6543139 = 9814709) B9814709
theorem B2184995 : Blo 1148636 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B1726259 : Blo 1148636 1726259 := bstep (se 1 (by rfl) ⟨1294694, by rfl⟩ : syracuseStep 1726259 = 2589389) B2589389
theorem B3495757 : Blo 1148636 3495757 := bstep (se 3 (by rfl) ⟨655454, by rfl⟩ : syracuseStep 3495757 = 1310909) B1310909
theorem B1726289 : Blo 1148636 1726289 := bstep (se 2 (by rfl) ⟨647358, by rfl⟩ : syracuseStep 1726289 = 1294717) B1294717
theorem B1726307 : Blo 1148636 1726307 := bstep (se 1 (by rfl) ⟨1294730, by rfl⟩ : syracuseStep 1726307 = 2589461) B2589461
theorem B1726337 : Blo 1148636 1726337 := bstep (se 2 (by rfl) ⟨647376, by rfl⟩ : syracuseStep 1726337 = 1294753) B1294753
theorem B1726355 : Blo 1148636 1726355 := bstep (se 1 (by rfl) ⟨1294766, by rfl⟩ : syracuseStep 1726355 = 2589533) B2589533
theorem B1726385 : Blo 1148636 1726385 := bstep (se 2 (by rfl) ⟨647394, by rfl⟩ : syracuseStep 1726385 = 1294789) B1294789
theorem B1726403 : Blo 1148636 1726403 := bstep (se 1 (by rfl) ⟨1294802, by rfl⟩ : syracuseStep 1726403 = 2589605) B2589605
theorem B1726433 : Blo 1148636 1726433 := bstep (se 2 (by rfl) ⟨647412, by rfl⟩ : syracuseStep 1726433 = 1294825) B1294825
theorem B3889133 : Blo 1148636 3889133 := bstep (se 3 (by rfl) ⟨729212, by rfl⟩ : syracuseStep 3889133 = 1458425) B1458425
theorem B1726451 : Blo 1148636 1726451 := bstep (se 1 (by rfl) ⟨1294838, by rfl⟩ : syracuseStep 1726451 = 2589677) B2589677
theorem B1726481 : Blo 1148636 1726481 := bstep (se 2 (by rfl) ⟨647430, by rfl⟩ : syracuseStep 1726481 = 1294861) B1294861
theorem B1726499 : Blo 1148636 1726499 := bstep (se 1 (by rfl) ⟨1294874, by rfl⟩ : syracuseStep 1726499 = 2589749) B2589749
theorem B3889187 : Blo 1148636 3889187 := bstep (se 1 (by rfl) ⟨2916890, by rfl⟩ : syracuseStep 3889187 = 5833781) B5833781
theorem B1726529 : Blo 1148636 1726529 := bstep (se 2 (by rfl) ⟨647448, by rfl⟩ : syracuseStep 1726529 = 1294897) B1294897
theorem B1726547 : Blo 1148636 1726547 := bstep (se 1 (by rfl) ⟨1294910, by rfl⟩ : syracuseStep 1726547 = 2589821) B2589821
theorem B1726577 : Blo 1148636 1726577 := bstep (se 2 (by rfl) ⟨647466, by rfl⟩ : syracuseStep 1726577 = 1294933) B1294933
theorem B1726595 : Blo 1148636 1726595 := bstep (se 1 (by rfl) ⟨1294946, by rfl⟩ : syracuseStep 1726595 = 2589893) B2589893
theorem B1726625 : Blo 1148636 1726625 := bstep (se 2 (by rfl) ⟨647484, by rfl⟩ : syracuseStep 1726625 = 1294969) B1294969
theorem B1726643 : Blo 1148636 1726643 := bstep (se 1 (by rfl) ⟨1294982, by rfl⟩ : syracuseStep 1726643 = 2589965) B2589965
theorem B1726673 : Blo 1148636 1726673 := bstep (se 2 (by rfl) ⟨647502, by rfl⟩ : syracuseStep 1726673 = 1295005) B1295005
theorem B1726691 : Blo 1148636 1726691 := bstep (se 1 (by rfl) ⟨1295018, by rfl⟩ : syracuseStep 1726691 = 2590037) B2590037
theorem B1726721 : Blo 1148636 1726721 := bstep (se 2 (by rfl) ⟨647520, by rfl⟩ : syracuseStep 1726721 = 1295041) B1295041
theorem B1726739 : Blo 1148636 1726739 := bstep (se 1 (by rfl) ⟨1295054, by rfl⟩ : syracuseStep 1726739 = 2590109) B2590109
theorem B6543665 : Blo 1148636 6543665 := bstep (se 2 (by rfl) ⟨2453874, by rfl⟩ : syracuseStep 6543665 = 4907749) B4907749
theorem B1726769 : Blo 1148636 1726769 := bstep (se 2 (by rfl) ⟨647538, by rfl⟩ : syracuseStep 1726769 = 1295077) B1295077
theorem B3889457 : Blo 1148636 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B1726787 : Blo 1148636 1726787 := bstep (se 1 (by rfl) ⟨1295090, by rfl⟩ : syracuseStep 1726787 = 2590181) B2590181
theorem B1726817 : Blo 1148636 1726817 := bstep (se 2 (by rfl) ⟨647556, by rfl⟩ : syracuseStep 1726817 = 1295113) B1295113
theorem B1726835 : Blo 1148636 1726835 := bstep (se 1 (by rfl) ⟨1295126, by rfl⟩ : syracuseStep 1726835 = 2590253) B2590253
theorem B1726865 : Blo 1148636 1726865 := bstep (se 2 (by rfl) ⟨647574, by rfl⟩ : syracuseStep 1726865 = 1295149) B1295149
theorem B1726883 : Blo 1148636 1726883 := bstep (se 1 (by rfl) ⟨1295162, by rfl⟩ : syracuseStep 1726883 = 2590325) B2590325
theorem B1726913 : Blo 1148636 1726913 := bstep (se 2 (by rfl) ⟨647592, by rfl⟩ : syracuseStep 1726913 = 1295185) B1295185
theorem B1726931 : Blo 1148636 1726931 := bstep (se 1 (by rfl) ⟨1295198, by rfl⟩ : syracuseStep 1726931 = 2590397) B2590397
theorem B1726961 : Blo 1148636 1726961 := bstep (se 2 (by rfl) ⟨647610, by rfl⟩ : syracuseStep 1726961 = 1295221) B1295221
theorem B1726979 : Blo 1148636 1726979 := bstep (se 1 (by rfl) ⟨1295234, by rfl⟩ : syracuseStep 1726979 = 2590469) B2590469
theorem B1727009 : Blo 1148636 1727009 := bstep (se 2 (by rfl) ⟨647628, by rfl⟩ : syracuseStep 1727009 = 1295257) B1295257
theorem B1727027 : Blo 1148636 1727027 := bstep (se 1 (by rfl) ⟨1295270, by rfl⟩ : syracuseStep 1727027 = 2590541) B2590541
theorem B1727057 : Blo 1148636 1727057 := bstep (se 2 (by rfl) ⟨647646, by rfl⟩ : syracuseStep 1727057 = 1295293) B1295293
theorem B1727075 : Blo 1148636 1727075 := bstep (se 1 (by rfl) ⟨1295306, by rfl⟩ : syracuseStep 1727075 = 2590613) B2590613
theorem B5823089 : Blo 1148636 5823089 := bstep (se 2 (by rfl) ⟨2183658, by rfl⟩ : syracuseStep 5823089 = 4367317) B4367317
theorem B1727105 : Blo 1148636 1727105 := bstep (se 2 (by rfl) ⟨647664, by rfl⟩ : syracuseStep 1727105 = 1295329) B1295329
theorem B1727123 : Blo 1148636 1727123 := bstep (se 1 (by rfl) ⟨1295342, by rfl⟩ : syracuseStep 1727123 = 2590685) B2590685
theorem B1727153 : Blo 1148636 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B1727171 : Blo 1148636 1727171 := bstep (se 1 (by rfl) ⟨1295378, by rfl⟩ : syracuseStep 1727171 = 2590757) B2590757
theorem B2185937 : Blo 1148636 2185937 := bstep (se 2 (by rfl) ⟨819726, by rfl⟩ : syracuseStep 2185937 = 1639453) B1639453
theorem B1727201 : Blo 1148636 1727201 := bstep (se 2 (by rfl) ⟨647700, by rfl⟩ : syracuseStep 1727201 = 1295401) B1295401
theorem B1727219 : Blo 1148636 1727219 := bstep (se 1 (by rfl) ⟨1295414, by rfl⟩ : syracuseStep 1727219 = 2590829) B2590829
theorem B1727249 : Blo 1148636 1727249 := bstep (se 2 (by rfl) ⟨647718, by rfl⟩ : syracuseStep 1727249 = 1295437) B1295437
theorem B1727267 : Blo 1148636 1727267 := bstep (se 1 (by rfl) ⟨1295450, by rfl⟩ : syracuseStep 1727267 = 2590901) B2590901
theorem B1727297 : Blo 1148636 1727297 := bstep (se 2 (by rfl) ⟨647736, by rfl⟩ : syracuseStep 1727297 = 1295473) B1295473
theorem B9820997 : Blo 1148636 9820997 := bstep (se 4 (by rfl) ⟨920718, by rfl⟩ : syracuseStep 9820997 = 1841437) B1841437
theorem B3889997 : Blo 1148636 3889997 := bstep (se 3 (by rfl) ⟨729374, by rfl⟩ : syracuseStep 3889997 = 1458749) B1458749
theorem B1727315 : Blo 1148636 1727315 := bstep (se 1 (by rfl) ⟨1295486, by rfl⟩ : syracuseStep 1727315 = 2590973) B2590973
theorem B1727345 : Blo 1148636 1727345 := bstep (se 2 (by rfl) ⟨647754, by rfl⟩ : syracuseStep 1727345 = 1295509) B1295509
theorem B1727363 : Blo 1148636 1727363 := bstep (se 1 (by rfl) ⟨1295522, by rfl⟩ : syracuseStep 1727363 = 2591045) B2591045
theorem B3890051 : Blo 1148636 3890051 := bstep (se 1 (by rfl) ⟨2917538, by rfl⟩ : syracuseStep 3890051 = 5835077) B5835077
theorem B1727393 : Blo 1148636 1727393 := bstep (se 2 (by rfl) ⟨647772, by rfl⟩ : syracuseStep 1727393 = 1295545) B1295545
theorem B1727411 : Blo 1148636 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B1727441 : Blo 1148636 1727441 := bstep (se 2 (by rfl) ⟨647790, by rfl⟩ : syracuseStep 1727441 = 1295581) B1295581
theorem B1727459 : Blo 1148636 1727459 := bstep (se 1 (by rfl) ⟨1295594, by rfl⟩ : syracuseStep 1727459 = 2591189) B2591189
theorem B1727489 : Blo 1148636 1727489 := bstep (se 2 (by rfl) ⟨647808, by rfl⟩ : syracuseStep 1727489 = 1295617) B1295617
theorem B1727507 : Blo 1148636 1727507 := bstep (se 1 (by rfl) ⟨1295630, by rfl⟩ : syracuseStep 1727507 = 2591261) B2591261
theorem B1727537 : Blo 1148636 1727537 := bstep (se 2 (by rfl) ⟨647826, by rfl⟩ : syracuseStep 1727537 = 1295653) B1295653
theorem B1727555 : Blo 1148636 1727555 := bstep (se 1 (by rfl) ⟨1295666, by rfl⟩ : syracuseStep 1727555 = 2591333) B2591333
theorem B1727585 : Blo 1148636 1727585 := bstep (se 2 (by rfl) ⟨647844, by rfl⟩ : syracuseStep 1727585 = 1295689) B1295689
theorem B1727603 : Blo 1148636 1727603 := bstep (se 1 (by rfl) ⟨1295702, by rfl⟩ : syracuseStep 1727603 = 2591405) B2591405
theorem B1727633 : Blo 1148636 1727633 := bstep (se 2 (by rfl) ⟨647862, by rfl⟩ : syracuseStep 1727633 = 1295725) B1295725
theorem B1727651 : Blo 1148636 1727651 := bstep (se 1 (by rfl) ⟨1295738, by rfl⟩ : syracuseStep 1727651 = 2591477) B2591477
theorem B1727681 : Blo 1148636 1727681 := bstep (se 2 (by rfl) ⟨647880, by rfl⟩ : syracuseStep 1727681 = 1295761) B1295761
theorem B1727699 : Blo 1148636 1727699 := bstep (se 1 (by rfl) ⟨1295774, by rfl⟩ : syracuseStep 1727699 = 2591549) B2591549
theorem B1727729 : Blo 1148636 1727729 := bstep (se 2 (by rfl) ⟨647898, by rfl⟩ : syracuseStep 1727729 = 1295797) B1295797
theorem B1727747 : Blo 1148636 1727747 := bstep (se 1 (by rfl) ⟨1295810, by rfl⟩ : syracuseStep 1727747 = 2591621) B2591621
theorem B1727777 : Blo 1148636 1727777 := bstep (se 2 (by rfl) ⟨647916, by rfl⟩ : syracuseStep 1727777 = 1295833) B1295833
theorem B1727795 : Blo 1148636 1727795 := bstep (se 1 (by rfl) ⟨1295846, by rfl⟩ : syracuseStep 1727795 = 2591693) B2591693
theorem B1727825 : Blo 1148636 1727825 := bstep (se 2 (by rfl) ⟨647934, by rfl⟩ : syracuseStep 1727825 = 1295869) B1295869
theorem B1727843 : Blo 1148636 1727843 := bstep (se 1 (by rfl) ⟨1295882, by rfl⟩ : syracuseStep 1727843 = 2591765) B2591765
theorem B1727873 : Blo 1148636 1727873 := bstep (se 2 (by rfl) ⟨647952, by rfl⟩ : syracuseStep 1727873 = 1295905) B1295905
theorem B1727891 : Blo 1148636 1727891 := bstep (se 1 (by rfl) ⟨1295918, by rfl⟩ : syracuseStep 1727891 = 2591837) B2591837
theorem B1727921 : Blo 1148636 1727921 := bstep (se 2 (by rfl) ⟨647970, by rfl⟩ : syracuseStep 1727921 = 1295941) B1295941
theorem B1727939 : Blo 1148636 1727939 := bstep (se 1 (by rfl) ⟨1295954, by rfl⟩ : syracuseStep 1727939 = 2591909) B2591909
theorem B1727969 : Blo 1148636 1727969 := bstep (se 2 (by rfl) ⟨647988, by rfl⟩ : syracuseStep 1727969 = 1295977) B1295977
theorem B9821681 : Blo 1148636 9821681 := bstep (se 2 (by rfl) ⟨3683130, by rfl⟩ : syracuseStep 9821681 = 7366261) B7366261
theorem B1727987 : Blo 1148636 1727987 := bstep (se 1 (by rfl) ⟨1295990, by rfl⟩ : syracuseStep 1727987 = 2591981) B2591981
theorem B1728017 : Blo 1148636 1728017 := bstep (se 2 (by rfl) ⟨648006, by rfl⟩ : syracuseStep 1728017 = 1296013) B1296013
theorem B1728035 : Blo 1148636 1728035 := bstep (se 1 (by rfl) ⟨1296026, by rfl⟩ : syracuseStep 1728035 = 2592053) B2592053
theorem B2907697 : Blo 1148636 2907697 := bstep (se 2 (by rfl) ⟨1090386, by rfl⟩ : syracuseStep 2907697 = 2180773) B2180773
theorem B1728065 : Blo 1148636 1728065 := bstep (se 2 (by rfl) ⟨648024, by rfl⟩ : syracuseStep 1728065 = 1296049) B1296049
theorem B2186833 : Blo 1148636 2186833 := bstep (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) B1640125
theorem B1728083 : Blo 1148636 1728083 := bstep (se 1 (by rfl) ⟨1296062, by rfl⟩ : syracuseStep 1728083 = 2592125) B2592125
theorem B1728113 : Blo 1148636 1728113 := bstep (se 2 (by rfl) ⟨648042, by rfl⟩ : syracuseStep 1728113 = 1296085) B1296085
theorem B1728131 : Blo 1148636 1728131 := bstep (se 1 (by rfl) ⟨1296098, by rfl⟩ : syracuseStep 1728131 = 2592197) B2592197
theorem B1728161 : Blo 1148636 1728161 := bstep (se 2 (by rfl) ⟨648060, by rfl⟩ : syracuseStep 1728161 = 1296121) B1296121
theorem B1728179 : Blo 1148636 1728179 := bstep (se 1 (by rfl) ⟨1296134, by rfl⟩ : syracuseStep 1728179 = 2592269) B2592269
theorem B1728209 : Blo 1148636 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B6545123 : Blo 1148636 6545123 := bstep (se 1 (by rfl) ⟨4908842, by rfl⟩ : syracuseStep 6545123 = 9817685) B9817685
theorem B1728227 : Blo 1148636 1728227 := bstep (se 1 (by rfl) ⟨1296170, by rfl⟩ : syracuseStep 1728227 = 2592341) B2592341
theorem B2186993 : Blo 1148636 2186993 := bstep (se 2 (by rfl) ⟨820122, by rfl⟩ : syracuseStep 2186993 = 1640245) B1640245
theorem B1728257 : Blo 1148636 1728257 := bstep (se 2 (by rfl) ⟨648096, by rfl⟩ : syracuseStep 1728257 = 1296193) B1296193
theorem B1728275 : Blo 1148636 1728275 := bstep (se 1 (by rfl) ⟨1296206, by rfl⟩ : syracuseStep 1728275 = 2592413) B2592413
theorem B1728305 : Blo 1148636 1728305 := bstep (se 2 (by rfl) ⟨648114, by rfl⟩ : syracuseStep 1728305 = 1296229) B1296229
theorem B2907971 : Blo 1148636 2907971 := bstep (se 1 (by rfl) ⟨2180978, by rfl⟩ : syracuseStep 2907971 = 4361957) B4361957
theorem B1728323 : Blo 1148636 1728323 := bstep (se 1 (by rfl) ⟨1296242, by rfl⟩ : syracuseStep 1728323 = 2592485) B2592485
theorem B1728353 : Blo 1148636 1728353 := bstep (se 2 (by rfl) ⟨648132, by rfl⟩ : syracuseStep 1728353 = 1296265) B1296265
theorem B1728371 : Blo 1148636 1728371 := bstep (se 1 (by rfl) ⟨1296278, by rfl⟩ : syracuseStep 1728371 = 2592557) B2592557
theorem B1728401 : Blo 1148636 1728401 := bstep (se 2 (by rfl) ⟨648150, by rfl⟩ : syracuseStep 1728401 = 1296301) B1296301
theorem B1728419 : Blo 1148636 1728419 := bstep (se 1 (by rfl) ⟨1296314, by rfl⟩ : syracuseStep 1728419 = 2592629) B2592629
theorem B1728449 : Blo 1148636 1728449 := bstep (se 2 (by rfl) ⟨648168, by rfl⟩ : syracuseStep 1728449 = 1296337) B1296337
theorem B1728467 : Blo 1148636 1728467 := bstep (se 1 (by rfl) ⟨1296350, by rfl⟩ : syracuseStep 1728467 = 2592701) B2592701
theorem B3366883 : Blo 1148636 3366883 := bstep (se 1 (by rfl) ⟨2525162, by rfl⟩ : syracuseStep 3366883 = 5050325) B5050325
theorem B1728497 : Blo 1148636 1728497 := bstep (se 2 (by rfl) ⟨648186, by rfl⟩ : syracuseStep 1728497 = 1296373) B1296373
theorem B2908163 : Blo 1148636 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B1728515 : Blo 1148636 1728515 := bstep (se 1 (by rfl) ⟨1296386, by rfl⟩ : syracuseStep 1728515 = 2592773) B2592773
theorem B7364621 : Blo 1148636 7364621 := bstep (se 3 (by rfl) ⟨1380866, by rfl⟩ : syracuseStep 7364621 = 2761733) B2761733
theorem B1728545 : Blo 1148636 1728545 := bstep (se 2 (by rfl) ⟨648204, by rfl⟩ : syracuseStep 1728545 = 1296409) B1296409
theorem B5824547 : Blo 1148636 5824547 := bstep (se 1 (by rfl) ⟨4368410, by rfl⟩ : syracuseStep 5824547 = 8736821) B8736821
theorem B1728563 : Blo 1148636 1728563 := bstep (se 1 (by rfl) ⟨1296422, by rfl⟩ : syracuseStep 1728563 = 2592845) B2592845
theorem B1728593 : Blo 1148636 1728593 := bstep (se 2 (by rfl) ⟨648222, by rfl⟩ : syracuseStep 1728593 = 1296445) B1296445
theorem B1728611 : Blo 1148636 1728611 := bstep (se 1 (by rfl) ⟨1296458, by rfl⟩ : syracuseStep 1728611 = 2592917) B2592917
theorem B1728641 : Blo 1148636 1728641 := bstep (se 2 (by rfl) ⟨648240, by rfl⟩ : syracuseStep 1728641 = 1296481) B1296481
theorem B2187395 : Blo 1148636 2187395 := bstep (se 1 (by rfl) ⟨1640546, by rfl⟩ : syracuseStep 2187395 = 3281093) B3281093
theorem B1728659 : Blo 1148636 1728659 := bstep (se 1 (by rfl) ⟨1296494, by rfl⟩ : syracuseStep 1728659 = 2592989) B2592989
theorem B5595299 : Blo 1148636 5595299 := bstep (se 1 (by rfl) ⟨4196474, by rfl⟩ : syracuseStep 5595299 = 8392949) B8392949
theorem B1728689 : Blo 1148636 1728689 := bstep (se 2 (by rfl) ⟨648258, by rfl⟩ : syracuseStep 1728689 = 1296517) B1296517
theorem B1728707 : Blo 1148636 1728707 := bstep (se 1 (by rfl) ⟨1296530, by rfl⟩ : syracuseStep 1728707 = 2593061) B2593061
theorem B1728737 : Blo 1148636 1728737 := bstep (se 2 (by rfl) ⟨648276, by rfl⟩ : syracuseStep 1728737 = 1296553) B1296553
theorem B1728755 : Blo 1148636 1728755 := bstep (se 1 (by rfl) ⟨1296566, by rfl⟩ : syracuseStep 1728755 = 2593133) B2593133
theorem B1728785 : Blo 1148636 1728785 := bstep (se 2 (by rfl) ⟨648294, by rfl⟩ : syracuseStep 1728785 = 1296589) B1296589
theorem B1728803 : Blo 1148636 1728803 := bstep (se 1 (by rfl) ⟨1296602, by rfl⟩ : syracuseStep 1728803 = 2593205) B2593205
theorem B1728833 : Blo 1148636 1728833 := bstep (se 2 (by rfl) ⟨648312, by rfl⟩ : syracuseStep 1728833 = 1296625) B1296625
theorem B1728851 : Blo 1148636 1728851 := bstep (se 1 (by rfl) ⟨1296638, by rfl⟩ : syracuseStep 1728851 = 2593277) B2593277
theorem B1728881 : Blo 1148636 1728881 := bstep (se 2 (by rfl) ⟨648330, by rfl⟩ : syracuseStep 1728881 = 1296661) B1296661
theorem B1728899 : Blo 1148636 1728899 := bstep (se 1 (by rfl) ⟨1296674, by rfl⟩ : syracuseStep 1728899 = 2593349) B2593349
theorem B1728929 : Blo 1148636 1728929 := bstep (se 2 (by rfl) ⟨648348, by rfl⟩ : syracuseStep 1728929 = 1296697) B1296697
theorem B1728947 : Blo 1148636 1728947 := bstep (se 1 (by rfl) ⟨1296710, by rfl⟩ : syracuseStep 1728947 = 2593421) B2593421
theorem B3498481 : Blo 1148636 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B6218531 : Blo 1148636 6218531 := bstep (se 1 (by rfl) ⟨4663898, by rfl⟩ : syracuseStep 6218531 = 9327797) B9327797
theorem B5825357 : Blo 1148636 5825357 := bstep (se 3 (by rfl) ⟨1092254, by rfl⟩ : syracuseStep 5825357 = 2184509) B2184509
theorem B2909105 : Blo 1148636 2909105 := bstep (se 2 (by rfl) ⟨1090914, by rfl⟩ : syracuseStep 2909105 = 2181829) B2181829
theorem B2909155 : Blo 1148636 2909155 := bstep (se 1 (by rfl) ⟨2181866, by rfl⟩ : syracuseStep 2909155 = 4363733) B4363733
theorem B3105859 : Blo 1148636 3105859 := bstep (se 1 (by rfl) ⟨2329394, by rfl⟩ : syracuseStep 3105859 = 4658789) B4658789
theorem B9462853 : Blo 1148636 9462853 := bstep (se 4 (by rfl) ⟨887142, by rfl⟩ : syracuseStep 9462853 = 1774285) B1774285
theorem B2909297 : Blo 1148636 2909297 := bstep (se 2 (by rfl) ⟨1090986, by rfl⟩ : syracuseStep 2909297 = 2181973) B2181973
theorem B3105955 : Blo 1148636 3105955 := bstep (se 1 (by rfl) ⟨2329466, by rfl⟩ : syracuseStep 3105955 = 4658933) B4658933
theorem B11068613 : Blo 1148636 11068613 := bstep (se 4 (by rfl) ⟨1037682, by rfl⟩ : syracuseStep 11068613 = 2075365) B2075365
theorem B6547013 : Blo 1148636 6547013 := bstep (se 4 (by rfl) ⟨613782, by rfl⟩ : syracuseStep 6547013 = 1227565) B1227565
theorem B4908707 : Blo 1148636 4908707 := bstep (se 1 (by rfl) ⟨3681530, by rfl⟩ : syracuseStep 4908707 = 7363061) B7363061
theorem B3237937 : Blo 1148636 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B2910289 : Blo 1148636 2910289 := bstep (se 2 (by rfl) ⟨1091358, by rfl⟩ : syracuseStep 2910289 = 2182717) B2182717
theorem B8743139 : Blo 1148636 8743139 := bstep (se 1 (by rfl) ⟨6557354, by rfl⟩ : syracuseStep 8743139 = 13114709) B13114709
theorem B2910563 : Blo 1148636 2910563 := bstep (se 1 (by rfl) ⟨2182922, by rfl⟩ : syracuseStep 2910563 = 4365845) B4365845
theorem B1894819 : Blo 1148636 1894819 := bstep (se 1 (by rfl) ⟨1421114, by rfl⟩ : syracuseStep 1894819 = 2842229) B2842229
theorem B3500525 : Blo 1148636 3500525 := bstep (se 3 (by rfl) ⟨656348, by rfl⟩ : syracuseStep 3500525 = 1312697) B1312697
theorem B2910755 : Blo 1148636 2910755 := bstep (se 1 (by rfl) ⟨2183066, by rfl⟩ : syracuseStep 2910755 = 4366133) B4366133
theorem B3271661 : Blo 1148636 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B3271843 : Blo 1148636 3271843 := bstep (se 1 (by rfl) ⟨2453882, by rfl⟩ : syracuseStep 3271843 = 4907765) B4907765
theorem B3271889 : Blo 1148636 3271889 := bstep (se 2 (by rfl) ⟨1226958, by rfl⟩ : syracuseStep 3271889 = 2453917) B2453917
theorem B26602805 : Blo 1148636 26602805 := bstep (se 5 (by rfl) ⟨1247006, by rfl⟩ : syracuseStep 26602805 = 2494013) B2494013
theorem B2911697 : Blo 1148636 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B2911747 : Blo 1148636 2911747 := bstep (se 1 (by rfl) ⟨2183810, by rfl⟩ : syracuseStep 2911747 = 4367621) B4367621
theorem B4910705 : Blo 1148636 4910705 := bstep (se 2 (by rfl) ⟨1841514, by rfl⟩ : syracuseStep 4910705 = 3683029) B3683029
theorem B2911889 : Blo 1148636 2911889 := bstep (se 2 (by rfl) ⟨1091958, by rfl⟩ : syracuseStep 2911889 = 2183917) B2183917
theorem B5828273 : Blo 1148636 5828273 := bstep (se 2 (by rfl) ⟨2185602, by rfl⟩ : syracuseStep 5828273 = 4371205) B4371205
theorem B13103045 : Blo 1148636 13103045 := bstep (se 4 (by rfl) ⟨1228410, by rfl⟩ : syracuseStep 13103045 = 2456821) B2456821
theorem B2584529 : Blo 1148636 2584529 := bstep (se 2 (by rfl) ⟨969198, by rfl⟩ : syracuseStep 2584529 = 1938397) B1938397
theorem B2584547 : Blo 1148636 2584547 := bstep (se 1 (by rfl) ⟨1938410, by rfl⟩ : syracuseStep 2584547 = 3876821) B3876821
theorem B2453507 : Blo 1148636 2453507 := bstep (se 1 (by rfl) ⟨1840130, by rfl⟩ : syracuseStep 2453507 = 3680261) B3680261
theorem B4550833 : Blo 1148636 4550833 := bstep (se 2 (by rfl) ⟨1706562, by rfl⟩ : syracuseStep 4550833 = 3413125) B3413125
theorem B2584817 : Blo 1148636 2584817 := bstep (se 2 (by rfl) ⟨969306, by rfl⟩ : syracuseStep 2584817 = 1938613) B1938613
theorem B2584835 : Blo 1148636 2584835 := bstep (se 1 (by rfl) ⟨1938626, by rfl⟩ : syracuseStep 2584835 = 3877253) B3877253
theorem B2453969 : Blo 1148636 2453969 := bstep (se 2 (by rfl) ⟨920238, by rfl⟩ : syracuseStep 2453969 = 1840477) B1840477
theorem B3502595 : Blo 1148636 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B2585105 : Blo 1148636 2585105 := bstep (se 2 (by rfl) ⟨969414, by rfl⟩ : syracuseStep 2585105 = 1938829) B1938829
theorem B2585123 : Blo 1148636 2585123 := bstep (se 1 (by rfl) ⟨1938842, by rfl⟩ : syracuseStep 2585123 = 3877685) B3877685
theorem B2912881 : Blo 1148636 2912881 := bstep (se 2 (by rfl) ⟨1092330, by rfl⟩ : syracuseStep 2912881 = 2184661) B2184661
theorem B3273347 : Blo 1148636 3273347 := bstep (se 1 (by rfl) ⟨2455010, by rfl⟩ : syracuseStep 3273347 = 4910021) B4910021
theorem B35517205 : Blo 1148636 35517205 := bstep (se 6 (by rfl) ⟨832434, by rfl⟩ : syracuseStep 35517205 = 1664869) B1664869
theorem B2585393 : Blo 1148636 2585393 := bstep (se 2 (by rfl) ⟨969522, by rfl⟩ : syracuseStep 2585393 = 1939045) B1939045
theorem B2585411 : Blo 1148636 2585411 := bstep (se 1 (by rfl) ⟨1939058, by rfl⟩ : syracuseStep 2585411 = 3878117) B3878117
theorem B11793251 : Blo 1148636 11793251 := bstep (se 1 (by rfl) ⟨8844938, by rfl⟩ : syracuseStep 11793251 = 17689877) B17689877
theorem B2913155 : Blo 1148636 2913155 := bstep (se 1 (by rfl) ⟨2184866, by rfl⟩ : syracuseStep 2913155 = 4369733) B4369733
theorem B2913347 : Blo 1148636 2913347 := bstep (se 1 (by rfl) ⟨2185010, by rfl⟩ : syracuseStep 2913347 = 4370021) B4370021
theorem B2585681 : Blo 1148636 2585681 := bstep (se 2 (by rfl) ⟨969630, by rfl⟩ : syracuseStep 2585681 = 1939261) B1939261
theorem B2585699 : Blo 1148636 2585699 := bstep (se 1 (by rfl) ⟨1939274, by rfl⟩ : syracuseStep 2585699 = 3878549) B3878549
theorem B13988963 : Blo 1148636 13988963 := bstep (se 1 (by rfl) ⟨10491722, by rfl⟩ : syracuseStep 13988963 = 20983445) B20983445
theorem B5829731 : Blo 1148636 5829731 := bstep (se 1 (by rfl) ⟨4372298, by rfl⟩ : syracuseStep 5829731 = 8744597) B8744597
theorem B4912397 : Blo 1148636 4912397 := bstep (se 3 (by rfl) ⟨921074, by rfl⟩ : syracuseStep 4912397 = 1842149) B1842149
theorem B2585969 : Blo 1148636 2585969 := bstep (se 2 (by rfl) ⟨969738, by rfl⟩ : syracuseStep 2585969 = 1939477) B1939477
theorem B2585987 : Blo 1148636 2585987 := bstep (se 1 (by rfl) ⟨1939490, by rfl⟩ : syracuseStep 2585987 = 3878981) B3878981
theorem B3503665 : Blo 1148636 3503665 := bstep (se 2 (by rfl) ⟨1313874, by rfl⟩ : syracuseStep 3503665 = 2627749) B2627749
theorem B2586257 : Blo 1148636 2586257 := bstep (se 2 (by rfl) ⟨969846, by rfl⟩ : syracuseStep 2586257 = 1939693) B1939693
theorem B2586275 : Blo 1148636 2586275 := bstep (se 1 (by rfl) ⟨1939706, by rfl⟩ : syracuseStep 2586275 = 3879413) B3879413
theorem B2455267 : Blo 1148636 2455267 := bstep (se 1 (by rfl) ⟨1841450, by rfl⟩ : syracuseStep 2455267 = 3682901) B3682901
theorem B3274577 : Blo 1148636 3274577 := bstep (se 2 (by rfl) ⟨1227966, by rfl⟩ : syracuseStep 3274577 = 2455933) B2455933
theorem B1636195 : Blo 1148636 1636195 := bstep (se 1 (by rfl) ⟨1227146, by rfl⟩ : syracuseStep 1636195 = 2454293) B2454293
theorem B5830541 : Blo 1148636 5830541 := bstep (se 3 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 5830541 = 2186453) B2186453
theorem B2586545 : Blo 1148636 2586545 := bstep (se 2 (by rfl) ⟨969954, by rfl⟩ : syracuseStep 2586545 = 1939909) B1939909
theorem B2586563 : Blo 1148636 2586563 := bstep (se 1 (by rfl) ⟨1939922, by rfl⟩ : syracuseStep 2586563 = 3879845) B3879845
theorem B2455523 : Blo 1148636 2455523 := bstep (se 1 (by rfl) ⟨1841642, by rfl⟩ : syracuseStep 2455523 = 3683285) B3683285
theorem B2914289 : Blo 1148636 2914289 := bstep (se 2 (by rfl) ⟨1092858, by rfl⟩ : syracuseStep 2914289 = 2185717) B2185717
theorem B2914339 : Blo 1148636 2914339 := bstep (se 1 (by rfl) ⟨2185754, by rfl⟩ : syracuseStep 2914339 = 4371509) B4371509
theorem B12449861 : Blo 1148636 12449861 := bstep (se 4 (by rfl) ⟨1167174, by rfl⟩ : syracuseStep 12449861 = 2334349) B2334349
theorem B2914481 : Blo 1148636 2914481 := bstep (se 2 (by rfl) ⟨1092930, by rfl⟩ : syracuseStep 2914481 = 2185861) B2185861
theorem B2586833 : Blo 1148636 2586833 := bstep (se 2 (by rfl) ⟨970062, by rfl⟩ : syracuseStep 2586833 = 1940125) B1940125
theorem B2586851 : Blo 1148636 2586851 := bstep (se 1 (by rfl) ⟨1940138, by rfl⟩ : syracuseStep 2586851 = 3880277) B3880277
theorem B19691747 : Blo 1148636 19691747 := bstep (se 1 (by rfl) ⟨14768810, by rfl⟩ : syracuseStep 19691747 = 29537621) B29537621
theorem B2587121 : Blo 1148636 2587121 := bstep (se 2 (by rfl) ⟨970170, by rfl⟩ : syracuseStep 2587121 = 1940341) B1940341
theorem B2587139 : Blo 1148636 2587139 := bstep (se 1 (by rfl) ⟨1940354, by rfl⟩ : syracuseStep 2587139 = 3880709) B3880709
theorem B9337457 : Blo 1148636 9337457 := bstep (se 2 (by rfl) ⟨3501546, by rfl⟩ : syracuseStep 9337457 = 7003093) B7003093
theorem B9337585 : Blo 1148636 9337585 := bstep (se 2 (by rfl) ⟨3501594, by rfl⟩ : syracuseStep 9337585 = 7003189) B7003189
theorem B2587409 : Blo 1148636 2587409 := bstep (se 2 (by rfl) ⟨970278, by rfl⟩ : syracuseStep 2587409 = 1940557) B1940557
theorem B2587427 : Blo 1148636 2587427 := bstep (se 1 (by rfl) ⟨1940570, by rfl⟩ : syracuseStep 2587427 = 3881141) B3881141
theorem B3505027 : Blo 1148636 3505027 := bstep (se 1 (by rfl) ⟨2628770, by rfl⟩ : syracuseStep 3505027 = 5257541) B5257541
theorem B2456497 : Blo 1148636 2456497 := bstep (se 2 (by rfl) ⟨921186, by rfl⟩ : syracuseStep 2456497 = 1842373) B1842373
theorem B1637329 : Blo 1148636 1637329 := bstep (se 2 (by rfl) ⟨613998, by rfl⟩ : syracuseStep 1637329 = 1227997) B1227997
theorem B1637425 : Blo 1148636 1637425 := bstep (se 2 (by rfl) ⟨614034, by rfl⟩ : syracuseStep 1637425 = 1228069) B1228069
theorem B2587697 : Blo 1148636 2587697 := bstep (se 2 (by rfl) ⟨970386, by rfl⟩ : syracuseStep 2587697 = 1940773) B1940773
theorem B2587715 : Blo 1148636 2587715 := bstep (se 1 (by rfl) ⟨1940786, by rfl⟩ : syracuseStep 2587715 = 3881573) B3881573
theorem B2915473 : Blo 1148636 2915473 := bstep (se 2 (by rfl) ⟨1093302, by rfl⟩ : syracuseStep 2915473 = 2186605) B2186605
theorem B3276035 : Blo 1148636 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B6552845 : Blo 1148636 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B2587985 : Blo 1148636 2587985 := bstep (se 2 (by rfl) ⟨970494, by rfl⟩ : syracuseStep 2587985 = 1940989) B1940989
theorem B2588003 : Blo 1148636 2588003 := bstep (se 1 (by rfl) ⟨1941002, by rfl⟩ : syracuseStep 2588003 = 3882005) B3882005
theorem B9829745 : Blo 1148636 9829745 := bstep (se 2 (by rfl) ⟨3686154, by rfl⟩ : syracuseStep 9829745 = 7372309) B7372309
theorem B2915747 : Blo 1148636 2915747 := bstep (se 1 (by rfl) ⟨2186810, by rfl⟩ : syracuseStep 2915747 = 4373621) B4373621
theorem B8748485 : Blo 1148636 8748485 := bstep (se 4 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 8748485 = 1640341) B1640341
theorem B3931661 : Blo 1148636 3931661 := bstep (se 3 (by rfl) ⟨737186, by rfl⟩ : syracuseStep 3931661 = 1474373) B1474373
theorem B1637921 : Blo 1148636 1637921 := bstep (se 2 (by rfl) ⟨614220, by rfl⟩ : syracuseStep 1637921 = 1228441) B1228441
theorem B2457155 : Blo 1148636 2457155 := bstep (se 1 (by rfl) ⟨1842866, by rfl⟩ : syracuseStep 2457155 = 3685733) B3685733
theorem B1244755 : Blo 1148636 1244755 := bstep (se 1 (by rfl) ⟨933566, by rfl⟩ : syracuseStep 1244755 = 1867133) B1867133
theorem B2915939 : Blo 1148636 2915939 := bstep (se 1 (by rfl) ⟨2186954, by rfl⟩ : syracuseStep 2915939 = 4373909) B4373909
theorem B2588273 : Blo 1148636 2588273 := bstep (se 2 (by rfl) ⟨970602, by rfl⟩ : syracuseStep 2588273 = 1941205) B1941205
theorem B2588291 : Blo 1148636 2588291 := bstep (se 1 (by rfl) ⟨1941218, by rfl⟩ : syracuseStep 2588291 = 3882437) B3882437
theorem B3079889 : Blo 1148636 3079889 := bstep (se 2 (by rfl) ⟨1154958, by rfl⟩ : syracuseStep 3079889 = 2309917) B2309917
theorem B3931949 : Blo 1148636 3931949 := bstep (se 3 (by rfl) ⟨737240, by rfl⟩ : syracuseStep 3931949 = 1474481) B1474481
theorem B2588561 : Blo 1148636 2588561 := bstep (se 2 (by rfl) ⟨970710, by rfl⟩ : syracuseStep 2588561 = 1941421) B1941421
theorem B2588579 : Blo 1148636 2588579 := bstep (se 1 (by rfl) ⟨1941434, by rfl⟩ : syracuseStep 2588579 = 3882869) B3882869
theorem B9338885 : Blo 1148636 9338885 := bstep (se 4 (by rfl) ⟨875520, by rfl⟩ : syracuseStep 9338885 = 1751041) B1751041
theorem B2588723 : Blo 1148636 2588723 := bstep (se 1 (by rfl) ⟨1941542, by rfl⟩ : syracuseStep 2588723 = 3883085) B3883085
theorem B2588759 : Blo 1148636 2588759 := bstep (se 1 (by rfl) ⟨1941569, by rfl⟩ : syracuseStep 2588759 = 3883139) B3883139
theorem B9961649 : Blo 1148636 9961649 := bstep (se 2 (by rfl) ⟨3735618, by rfl⟩ : syracuseStep 9961649 = 7471237) B7471237
theorem B17268997 : Blo 1148636 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B2588939 : Blo 1148636 2588939 := bstep (se 1 (by rfl) ⟨1941704, by rfl⟩ : syracuseStep 2588939 = 3883409) B3883409
theorem B1638667 : Blo 1148636 1638667 := bstep (se 1 (by rfl) ⟨1229000, by rfl⟩ : syracuseStep 1638667 = 2458001) B2458001
theorem B2457881 : Blo 1148636 2457881 := bstep (se 2 (by rfl) ⟨921705, by rfl⟩ : syracuseStep 2457881 = 1843411) B1843411
theorem B2588993 : Blo 1148636 2588993 := bstep (se 2 (by rfl) ⟨970872, by rfl⟩ : syracuseStep 2588993 = 1941745) B1941745
theorem B2621783 : Blo 1148636 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B3113309 : Blo 1148636 3113309 := bstep (se 3 (by rfl) ⟨583745, by rfl⟩ : syracuseStep 3113309 = 1167491) B1167491
theorem B9830807 : Blo 1148636 9830807 := bstep (se 1 (by rfl) ⟨7373105, by rfl⟩ : syracuseStep 9830807 = 14746211) B14746211
theorem B6226355 : Blo 1148636 6226355 := bstep (se 1 (by rfl) ⟨4669766, by rfl⟩ : syracuseStep 6226355 = 9339533) B9339533
theorem B2589209 : Blo 1148636 2589209 := bstep (se 2 (by rfl) ⟨970953, by rfl⟩ : syracuseStep 2589209 = 1941907) B1941907
theorem B2589299 : Blo 1148636 2589299 := bstep (se 1 (by rfl) ⟨1941974, by rfl⟩ : syracuseStep 2589299 = 3883949) B3883949
theorem B2589335 : Blo 1148636 2589335 := bstep (se 1 (by rfl) ⟨1942001, by rfl⟩ : syracuseStep 2589335 = 3884003) B3884003
theorem B2458291 : Blo 1148636 2458291 := bstep (se 1 (by rfl) ⟨1843718, by rfl⟩ : syracuseStep 2458291 = 3687437) B3687437
theorem B2917043 : Blo 1148636 2917043 := bstep (se 1 (by rfl) ⟨2187782, by rfl⟩ : syracuseStep 2917043 = 4375565) B4375565
theorem B3736343 : Blo 1148636 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B2589515 : Blo 1148636 2589515 := bstep (se 1 (by rfl) ⟨1942136, by rfl⟩ : syracuseStep 2589515 = 3884273) B3884273
theorem B2589569 : Blo 1148636 2589569 := bstep (se 2 (by rfl) ⟨971088, by rfl⟩ : syracuseStep 2589569 = 1942177) B1942177
theorem B1311671 : Blo 1148636 1311671 := bstep (se 1 (by rfl) ⟨983753, by rfl⟩ : syracuseStep 1311671 = 1967507) B1967507
theorem B12452881 : Blo 1148636 12452881 := bstep (se 2 (by rfl) ⟨4669830, by rfl⟩ : syracuseStep 12452881 = 9339661) B9339661
theorem B3277847 : Blo 1148636 3277847 := bstep (se 1 (by rfl) ⟨2458385, by rfl⟩ : syracuseStep 3277847 = 4916771) B4916771
theorem B2589785 : Blo 1148636 2589785 := bstep (se 2 (by rfl) ⟨971169, by rfl⟩ : syracuseStep 2589785 = 1942339) B1942339
theorem B6554803 : Blo 1148636 6554803 := bstep (se 1 (by rfl) ⟨4916102, by rfl⟩ : syracuseStep 6554803 = 9832205) B9832205
theorem B2589875 : Blo 1148636 2589875 := bstep (se 1 (by rfl) ⟨1942406, by rfl⟩ : syracuseStep 2589875 = 3884813) B3884813
theorem B3114163 : Blo 1148636 3114163 := bstep (se 1 (by rfl) ⟨2335622, by rfl⟩ : syracuseStep 3114163 = 4671245) B4671245
theorem B2917579 : Blo 1148636 2917579 := bstep (se 1 (by rfl) ⟨2188184, by rfl⟩ : syracuseStep 2917579 = 4376369) B4376369
theorem B2589911 : Blo 1148636 2589911 := bstep (se 1 (by rfl) ⟨1942433, by rfl⟩ : syracuseStep 2589911 = 3884867) B3884867
theorem B4916497 : Blo 1148636 4916497 := bstep (se 2 (by rfl) ⟨1843686, by rfl⟩ : syracuseStep 4916497 = 3687373) B3687373
theorem B1770839 : Blo 1148636 1770839 := bstep (se 1 (by rfl) ⟨1328129, by rfl⟩ : syracuseStep 1770839 = 2656259) B2656259
theorem B8750429 : Blo 1148636 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B2590091 : Blo 1148636 2590091 := bstep (se 1 (by rfl) ⟨1942568, by rfl⟩ : syracuseStep 2590091 = 3885137) B3885137
theorem B12617137 : Blo 1148636 12617137 := bstep (se 2 (by rfl) ⟨4731426, by rfl⟩ : syracuseStep 12617137 = 9462853) B9462853
theorem B2590145 : Blo 1148636 2590145 := bstep (se 2 (by rfl) ⟨971304, by rfl⟩ : syracuseStep 2590145 = 1942609) B1942609
theorem B2590361 : Blo 1148636 2590361 := bstep (se 2 (by rfl) ⟨971385, by rfl⟩ : syracuseStep 2590361 = 1942771) B1942771
theorem B1148651 : Blo 1148636 1148651 := bstep (se 1 (by rfl) ⟨861488, by rfl⟩ : syracuseStep 1148651 = 1722977) B1722977
theorem B2590451 : Blo 1148636 2590451 := bstep (se 1 (by rfl) ⟨1942838, by rfl⟩ : syracuseStep 2590451 = 3885677) B3885677
theorem B1148663 : Blo 1148636 1148663 := bstep (se 1 (by rfl) ⟨861497, by rfl⟩ : syracuseStep 1148663 = 1722995) B1722995
theorem B1148683 : Blo 1148636 1148683 := bstep (se 1 (by rfl) ⟨861512, by rfl⟩ : syracuseStep 1148683 = 1723025) B1723025
theorem B1148695 : Blo 1148636 1148695 := bstep (se 1 (by rfl) ⟨861521, by rfl⟩ : syracuseStep 1148695 = 1723043) B1723043
theorem B5244695 : Blo 1148636 5244695 := bstep (se 1 (by rfl) ⟨3933521, by rfl⟩ : syracuseStep 5244695 = 7867043) B7867043
theorem B2590487 : Blo 1148636 2590487 := bstep (se 1 (by rfl) ⟨1942865, by rfl⟩ : syracuseStep 2590487 = 3885731) B3885731
theorem B1148715 : Blo 1148636 1148715 := bstep (se 1 (by rfl) ⟨861536, by rfl⟩ : syracuseStep 1148715 = 1723073) B1723073
theorem B1148727 : Blo 1148636 1148727 := bstep (se 1 (by rfl) ⟨861545, by rfl⟩ : syracuseStep 1148727 = 1723091) B1723091
theorem B1148747 : Blo 1148636 1148747 := bstep (se 1 (by rfl) ⟨861560, by rfl⟩ : syracuseStep 1148747 = 1723121) B1723121
theorem B1148759 : Blo 1148636 1148759 := bstep (se 1 (by rfl) ⟨861569, by rfl⟩ : syracuseStep 1148759 = 1723139) B1723139
theorem B2459479 : Blo 1148636 2459479 := bstep (se 1 (by rfl) ⟨1844609, by rfl⟩ : syracuseStep 2459479 = 3689219) B3689219
theorem B1148779 : Blo 1148636 1148779 := bstep (se 1 (by rfl) ⟨861584, by rfl⟩ : syracuseStep 1148779 = 1723169) B1723169
theorem B1148791 : Blo 1148636 1148791 := bstep (se 1 (by rfl) ⟨861593, by rfl⟩ : syracuseStep 1148791 = 1723187) B1723187
theorem B2459521 : Blo 1148636 2459521 := bstep (se 2 (by rfl) ⟨922320, by rfl⟩ : syracuseStep 2459521 = 1844641) B1844641
theorem B5244803 : Blo 1148636 5244803 := bstep (se 1 (by rfl) ⟨3933602, by rfl⟩ : syracuseStep 5244803 = 7867205) B7867205
theorem B1148811 : Blo 1148636 1148811 := bstep (se 1 (by rfl) ⟨861608, by rfl⟩ : syracuseStep 1148811 = 1723217) B1723217
theorem B1148823 : Blo 1148636 1148823 := bstep (se 1 (by rfl) ⟨861617, by rfl⟩ : syracuseStep 1148823 = 1723235) B1723235
theorem B1148843 : Blo 1148636 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B1148855 : Blo 1148636 1148855 := bstep (se 1 (by rfl) ⟨861641, by rfl⟩ : syracuseStep 1148855 = 1723283) B1723283
theorem B1148875 : Blo 1148636 1148875 := bstep (se 1 (by rfl) ⟨861656, by rfl⟩ : syracuseStep 1148875 = 1723313) B1723313
theorem B2590667 : Blo 1148636 2590667 := bstep (se 1 (by rfl) ⟨1943000, by rfl⟩ : syracuseStep 2590667 = 3886001) B3886001
theorem B1148887 : Blo 1148636 1148887 := bstep (se 1 (by rfl) ⟨861665, by rfl⟩ : syracuseStep 1148887 = 1723331) B1723331
theorem B1148907 : Blo 1148636 1148907 := bstep (se 1 (by rfl) ⟨861680, by rfl⟩ : syracuseStep 1148907 = 1723361) B1723361
theorem B1148919 : Blo 1148636 1148919 := bstep (se 1 (by rfl) ⟨861689, by rfl⟩ : syracuseStep 1148919 = 1723379) B1723379
theorem B2590721 : Blo 1148636 2590721 := bstep (se 2 (by rfl) ⟨971520, by rfl⟩ : syracuseStep 2590721 = 1943041) B1943041
theorem B1148939 : Blo 1148636 1148939 := bstep (se 1 (by rfl) ⟨861704, by rfl⟩ : syracuseStep 1148939 = 1723409) B1723409
theorem B1148951 : Blo 1148636 1148951 := bstep (se 1 (by rfl) ⟨861713, by rfl⟩ : syracuseStep 1148951 = 1723427) B1723427
theorem B1148971 : Blo 1148636 1148971 := bstep (se 1 (by rfl) ⟨861728, by rfl⟩ : syracuseStep 1148971 = 1723457) B1723457
theorem B1148983 : Blo 1148636 1148983 := bstep (se 1 (by rfl) ⟨861737, by rfl⟩ : syracuseStep 1148983 = 1723475) B1723475
theorem B1149003 : Blo 1148636 1149003 := bstep (se 1 (by rfl) ⟨861752, by rfl⟩ : syracuseStep 1149003 = 1723505) B1723505
theorem B1149015 : Blo 1148636 1149015 := bstep (se 1 (by rfl) ⟨861761, by rfl⟩ : syracuseStep 1149015 = 1723523) B1723523
theorem B3541085 : Blo 1148636 3541085 := bstep (se 3 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 3541085 = 1327907) B1327907
theorem B1149035 : Blo 1148636 1149035 := bstep (se 1 (by rfl) ⟨861776, by rfl⟩ : syracuseStep 1149035 = 1723553) B1723553
theorem B1149047 : Blo 1148636 1149047 := bstep (se 1 (by rfl) ⟨861785, by rfl⟩ : syracuseStep 1149047 = 1723571) B1723571
theorem B1149067 : Blo 1148636 1149067 := bstep (se 1 (by rfl) ⟨861800, by rfl⟩ : syracuseStep 1149067 = 1723601) B1723601
theorem B1149079 : Blo 1148636 1149079 := bstep (se 1 (by rfl) ⟨861809, by rfl⟩ : syracuseStep 1149079 = 1723619) B1723619
theorem B1149099 : Blo 1148636 1149099 := bstep (se 1 (by rfl) ⟨861824, by rfl⟩ : syracuseStep 1149099 = 1723649) B1723649
theorem B1149111 : Blo 1148636 1149111 := bstep (se 1 (by rfl) ⟨861833, by rfl⟩ : syracuseStep 1149111 = 1723667) B1723667
theorem B1149131 : Blo 1148636 1149131 := bstep (se 1 (by rfl) ⟨861848, by rfl⟩ : syracuseStep 1149131 = 1723697) B1723697
theorem B1149143 : Blo 1148636 1149143 := bstep (se 1 (by rfl) ⟨861857, by rfl⟩ : syracuseStep 1149143 = 1723715) B1723715
theorem B2590937 : Blo 1148636 2590937 := bstep (se 2 (by rfl) ⟨971601, by rfl⟩ : syracuseStep 2590937 = 1943203) B1943203
theorem B1149163 : Blo 1148636 1149163 := bstep (se 1 (by rfl) ⟨861872, by rfl⟩ : syracuseStep 1149163 = 1723745) B1723745
theorem B1149175 : Blo 1148636 1149175 := bstep (se 1 (by rfl) ⟨861881, by rfl⟩ : syracuseStep 1149175 = 1723763) B1723763
theorem B1149195 : Blo 1148636 1149195 := bstep (se 1 (by rfl) ⟨861896, by rfl⟩ : syracuseStep 1149195 = 1723793) B1723793
theorem B1149207 : Blo 1148636 1149207 := bstep (se 1 (by rfl) ⟨861905, by rfl⟩ : syracuseStep 1149207 = 1723811) B1723811
theorem B9341219 : Blo 1148636 9341219 := bstep (se 1 (by rfl) ⟨7005914, by rfl⟩ : syracuseStep 9341219 = 14011829) B14011829
theorem B1149227 : Blo 1148636 1149227 := bstep (se 1 (by rfl) ⟨861920, by rfl⟩ : syracuseStep 1149227 = 1723841) B1723841
theorem B2591027 : Blo 1148636 2591027 := bstep (se 1 (by rfl) ⟨1943270, by rfl⟩ : syracuseStep 2591027 = 3886541) B3886541
theorem B1149239 : Blo 1148636 1149239 := bstep (se 1 (by rfl) ⟨861929, by rfl⟩ : syracuseStep 1149239 = 1723859) B1723859
theorem B1149259 : Blo 1148636 1149259 := bstep (se 1 (by rfl) ⟨861944, by rfl⟩ : syracuseStep 1149259 = 1723889) B1723889
theorem B3279179 : Blo 1148636 3279179 := bstep (se 1 (by rfl) ⟨2459384, by rfl⟩ : syracuseStep 3279179 = 4918769) B4918769
theorem B1149271 : Blo 1148636 1149271 := bstep (se 1 (by rfl) ⟨861953, by rfl⟩ : syracuseStep 1149271 = 1723907) B1723907
theorem B2591063 : Blo 1148636 2591063 := bstep (se 1 (by rfl) ⟨1943297, by rfl⟩ : syracuseStep 2591063 = 3886595) B3886595
theorem B1149291 : Blo 1148636 1149291 := bstep (se 1 (by rfl) ⟨861968, by rfl⟩ : syracuseStep 1149291 = 1723937) B1723937
theorem B1149303 : Blo 1148636 1149303 := bstep (se 1 (by rfl) ⟨861977, by rfl⟩ : syracuseStep 1149303 = 1723955) B1723955
theorem B1149323 : Blo 1148636 1149323 := bstep (se 1 (by rfl) ⟨861992, by rfl⟩ : syracuseStep 1149323 = 1723985) B1723985
theorem B1149335 : Blo 1148636 1149335 := bstep (se 1 (by rfl) ⟨862001, by rfl⟩ : syracuseStep 1149335 = 1724003) B1724003
theorem B1149355 : Blo 1148636 1149355 := bstep (se 1 (by rfl) ⟨862016, by rfl⟩ : syracuseStep 1149355 = 1724033) B1724033
theorem B7375283 : Blo 1148636 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B1149367 : Blo 1148636 1149367 := bstep (se 1 (by rfl) ⟨862025, by rfl⟩ : syracuseStep 1149367 = 1724051) B1724051
theorem B1149387 : Blo 1148636 1149387 := bstep (se 1 (by rfl) ⟨862040, by rfl⟩ : syracuseStep 1149387 = 1724081) B1724081
theorem B1149399 : Blo 1148636 1149399 := bstep (se 1 (by rfl) ⟨862049, by rfl⟩ : syracuseStep 1149399 = 1724099) B1724099
theorem B1149419 : Blo 1148636 1149419 := bstep (se 1 (by rfl) ⟨862064, by rfl⟩ : syracuseStep 1149419 = 1724129) B1724129
theorem B1149431 : Blo 1148636 1149431 := bstep (se 1 (by rfl) ⟨862073, by rfl⟩ : syracuseStep 1149431 = 1724147) B1724147
theorem B1149451 : Blo 1148636 1149451 := bstep (se 1 (by rfl) ⟨862088, by rfl⟩ : syracuseStep 1149451 = 1724177) B1724177
theorem B1313291 : Blo 1148636 1313291 := bstep (se 1 (by rfl) ⟨984968, by rfl⟩ : syracuseStep 1313291 = 1969937) B1969937
theorem B2591243 : Blo 1148636 2591243 := bstep (se 1 (by rfl) ⟨1943432, by rfl⟩ : syracuseStep 2591243 = 3886865) B3886865
theorem B1149463 : Blo 1148636 1149463 := bstep (se 1 (by rfl) ⟨862097, by rfl⟩ : syracuseStep 1149463 = 1724195) B1724195
theorem B1149483 : Blo 1148636 1149483 := bstep (se 1 (by rfl) ⟨862112, by rfl⟩ : syracuseStep 1149483 = 1724225) B1724225
theorem B1149495 : Blo 1148636 1149495 := bstep (se 1 (by rfl) ⟨862121, by rfl⟩ : syracuseStep 1149495 = 1724243) B1724243
theorem B2591297 : Blo 1148636 2591297 := bstep (se 2 (by rfl) ⟨971736, by rfl⟩ : syracuseStep 2591297 = 1943473) B1943473
theorem B1149515 : Blo 1148636 1149515 := bstep (se 1 (by rfl) ⟨862136, by rfl⟩ : syracuseStep 1149515 = 1724273) B1724273
theorem B1149527 : Blo 1148636 1149527 := bstep (se 1 (by rfl) ⟨862145, by rfl⟩ : syracuseStep 1149527 = 1724291) B1724291
theorem B6556261 : Blo 1148636 6556261 := bstep (se 4 (by rfl) ⟨614649, by rfl⟩ : syracuseStep 6556261 = 1229299) B1229299
theorem B1149547 : Blo 1148636 1149547 := bstep (se 1 (by rfl) ⟨862160, by rfl⟩ : syracuseStep 1149547 = 1724321) B1724321
theorem B1149559 : Blo 1148636 1149559 := bstep (se 1 (by rfl) ⟨862169, by rfl⟩ : syracuseStep 1149559 = 1724339) B1724339
theorem B1149579 : Blo 1148636 1149579 := bstep (se 1 (by rfl) ⟨862184, by rfl⟩ : syracuseStep 1149579 = 1724369) B1724369
theorem B1149591 : Blo 1148636 1149591 := bstep (se 1 (by rfl) ⟨862193, by rfl⟩ : syracuseStep 1149591 = 1724387) B1724387
theorem B1149611 : Blo 1148636 1149611 := bstep (se 1 (by rfl) ⟨862208, by rfl⟩ : syracuseStep 1149611 = 1724417) B1724417
theorem B8293043 : Blo 1148636 8293043 := bstep (se 1 (by rfl) ⟨6219782, by rfl⟩ : syracuseStep 8293043 = 12439565) B12439565
theorem B1149623 : Blo 1148636 1149623 := bstep (se 1 (by rfl) ⟨862217, by rfl⟩ : syracuseStep 1149623 = 1724435) B1724435
theorem B1149643 : Blo 1148636 1149643 := bstep (se 1 (by rfl) ⟨862232, by rfl⟩ : syracuseStep 1149643 = 1724465) B1724465
theorem B1149655 : Blo 1148636 1149655 := bstep (se 1 (by rfl) ⟨862241, by rfl⟩ : syracuseStep 1149655 = 1724483) B1724483
theorem B1149675 : Blo 1148636 1149675 := bstep (se 1 (by rfl) ⟨862256, by rfl⟩ : syracuseStep 1149675 = 1724513) B1724513
theorem B1149687 : Blo 1148636 1149687 := bstep (se 1 (by rfl) ⟨862265, by rfl⟩ : syracuseStep 1149687 = 1724531) B1724531
theorem B1149707 : Blo 1148636 1149707 := bstep (se 1 (by rfl) ⟨862280, by rfl⟩ : syracuseStep 1149707 = 1724561) B1724561
theorem B1149719 : Blo 1148636 1149719 := bstep (se 1 (by rfl) ⟨862289, by rfl⟩ : syracuseStep 1149719 = 1724579) B1724579
theorem B2591513 : Blo 1148636 2591513 := bstep (se 2 (by rfl) ⟨971817, by rfl⟩ : syracuseStep 2591513 = 1943635) B1943635
theorem B1149739 : Blo 1148636 1149739 := bstep (se 1 (by rfl) ⟨862304, by rfl⟩ : syracuseStep 1149739 = 1724609) B1724609
theorem B1149751 : Blo 1148636 1149751 := bstep (se 1 (by rfl) ⟨862313, by rfl⟩ : syracuseStep 1149751 = 1724627) B1724627
theorem B1149771 : Blo 1148636 1149771 := bstep (se 1 (by rfl) ⟨862328, by rfl⟩ : syracuseStep 1149771 = 1724657) B1724657
theorem B1149783 : Blo 1148636 1149783 := bstep (se 1 (by rfl) ⟨862337, by rfl⟩ : syracuseStep 1149783 = 1724675) B1724675
theorem B1149803 : Blo 1148636 1149803 := bstep (se 1 (by rfl) ⟨862352, by rfl⟩ : syracuseStep 1149803 = 1724705) B1724705
theorem B2591603 : Blo 1148636 2591603 := bstep (se 1 (by rfl) ⟨1943702, by rfl⟩ : syracuseStep 2591603 = 3887405) B3887405
theorem B1149815 : Blo 1148636 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B1149835 : Blo 1148636 1149835 := bstep (se 1 (by rfl) ⟨862376, by rfl⟩ : syracuseStep 1149835 = 1724753) B1724753
theorem B1149847 : Blo 1148636 1149847 := bstep (se 1 (by rfl) ⟨862385, by rfl⟩ : syracuseStep 1149847 = 1724771) B1724771
theorem B2591639 : Blo 1148636 2591639 := bstep (se 1 (by rfl) ⟨1943729, by rfl⟩ : syracuseStep 2591639 = 3887459) B3887459
theorem B1149867 : Blo 1148636 1149867 := bstep (se 1 (by rfl) ⟨862400, by rfl⟩ : syracuseStep 1149867 = 1724801) B1724801
theorem B1149879 : Blo 1148636 1149879 := bstep (se 1 (by rfl) ⟨862409, by rfl⟩ : syracuseStep 1149879 = 1724819) B1724819
theorem B1149899 : Blo 1148636 1149899 := bstep (se 1 (by rfl) ⟨862424, by rfl⟩ : syracuseStep 1149899 = 1724849) B1724849
theorem B1149911 : Blo 1148636 1149911 := bstep (se 1 (by rfl) ⟨862433, by rfl⟩ : syracuseStep 1149911 = 1724867) B1724867
theorem B4983769 : Blo 1148636 4983769 := bstep (se 2 (by rfl) ⟨1868913, by rfl⟩ : syracuseStep 4983769 = 3737827) B3737827
theorem B1149931 : Blo 1148636 1149931 := bstep (se 1 (by rfl) ⟨862448, by rfl⟩ : syracuseStep 1149931 = 1724897) B1724897
theorem B1149943 : Blo 1148636 1149943 := bstep (se 1 (by rfl) ⟨862457, by rfl⟩ : syracuseStep 1149943 = 1724915) B1724915
theorem B1149963 : Blo 1148636 1149963 := bstep (se 1 (by rfl) ⟨862472, by rfl⟩ : syracuseStep 1149963 = 1724945) B1724945
theorem B1149975 : Blo 1148636 1149975 := bstep (se 1 (by rfl) ⟨862481, by rfl⟩ : syracuseStep 1149975 = 1724963) B1724963
theorem B1149995 : Blo 1148636 1149995 := bstep (se 1 (by rfl) ⟨862496, by rfl⟩ : syracuseStep 1149995 = 1724993) B1724993
theorem B1150007 : Blo 1148636 1150007 := bstep (se 1 (by rfl) ⟨862505, by rfl⟩ : syracuseStep 1150007 = 1725011) B1725011
theorem B1150027 : Blo 1148636 1150027 := bstep (se 1 (by rfl) ⟨862520, by rfl⟩ : syracuseStep 1150027 = 1725041) B1725041
theorem B2591819 : Blo 1148636 2591819 := bstep (se 1 (by rfl) ⟨1943864, by rfl⟩ : syracuseStep 2591819 = 3887729) B3887729
theorem B1150039 : Blo 1148636 1150039 := bstep (se 1 (by rfl) ⟨862529, by rfl⟩ : syracuseStep 1150039 = 1725059) B1725059
theorem B1150059 : Blo 1148636 1150059 := bstep (se 1 (by rfl) ⟨862544, by rfl⟩ : syracuseStep 1150059 = 1725089) B1725089
theorem B1150071 : Blo 1148636 1150071 := bstep (se 1 (by rfl) ⟨862553, by rfl⟩ : syracuseStep 1150071 = 1725107) B1725107
theorem B2591873 : Blo 1148636 2591873 := bstep (se 2 (by rfl) ⟨971952, by rfl⟩ : syracuseStep 2591873 = 1943905) B1943905
theorem B1150091 : Blo 1148636 1150091 := bstep (se 1 (by rfl) ⟨862568, by rfl⟩ : syracuseStep 1150091 = 1725137) B1725137
theorem B1150103 : Blo 1148636 1150103 := bstep (se 1 (by rfl) ⟨862577, by rfl⟩ : syracuseStep 1150103 = 1725155) B1725155
theorem B1150123 : Blo 1148636 1150123 := bstep (se 1 (by rfl) ⟨862592, by rfl⟩ : syracuseStep 1150123 = 1725185) B1725185
theorem B1150135 : Blo 1148636 1150135 := bstep (se 1 (by rfl) ⟨862601, by rfl⟩ : syracuseStep 1150135 = 1725203) B1725203
theorem B1150155 : Blo 1148636 1150155 := bstep (se 1 (by rfl) ⟨862616, by rfl⟩ : syracuseStep 1150155 = 1725233) B1725233
theorem B1150167 : Blo 1148636 1150167 := bstep (se 1 (by rfl) ⟨862625, by rfl⟩ : syracuseStep 1150167 = 1725251) B1725251
theorem B2526425 : Blo 1148636 2526425 := bstep (se 2 (by rfl) ⟨947409, by rfl⟩ : syracuseStep 2526425 = 1894819) B1894819
theorem B1150187 : Blo 1148636 1150187 := bstep (se 1 (by rfl) ⟨862640, by rfl⟩ : syracuseStep 1150187 = 1725281) B1725281
theorem B1150199 : Blo 1148636 1150199 := bstep (se 1 (by rfl) ⟨862649, by rfl⟩ : syracuseStep 1150199 = 1725299) B1725299
theorem B1150219 : Blo 1148636 1150219 := bstep (se 1 (by rfl) ⟨862664, by rfl⟩ : syracuseStep 1150219 = 1725329) B1725329
theorem B1150231 : Blo 1148636 1150231 := bstep (se 1 (by rfl) ⟨862673, by rfl⟩ : syracuseStep 1150231 = 1725347) B1725347
theorem B1150251 : Blo 1148636 1150251 := bstep (se 1 (by rfl) ⟨862688, by rfl⟩ : syracuseStep 1150251 = 1725377) B1725377
theorem B1150263 : Blo 1148636 1150263 := bstep (se 1 (by rfl) ⟨862697, by rfl⟩ : syracuseStep 1150263 = 1725395) B1725395
theorem B1150283 : Blo 1148636 1150283 := bstep (se 1 (by rfl) ⟨862712, by rfl⟩ : syracuseStep 1150283 = 1725425) B1725425
theorem B1150295 : Blo 1148636 1150295 := bstep (se 1 (by rfl) ⟨862721, by rfl⟩ : syracuseStep 1150295 = 1725443) B1725443
theorem B2592089 : Blo 1148636 2592089 := bstep (se 2 (by rfl) ⟨972033, by rfl⟩ : syracuseStep 2592089 = 1944067) B1944067
theorem B1150315 : Blo 1148636 1150315 := bstep (se 1 (by rfl) ⟨862736, by rfl⟩ : syracuseStep 1150315 = 1725473) B1725473
theorem B1150327 : Blo 1148636 1150327 := bstep (se 1 (by rfl) ⟨862745, by rfl⟩ : syracuseStep 1150327 = 1725491) B1725491
theorem B1150347 : Blo 1148636 1150347 := bstep (se 1 (by rfl) ⟨862760, by rfl⟩ : syracuseStep 1150347 = 1725521) B1725521
theorem B1478027 : Blo 1148636 1478027 := bstep (se 1 (by rfl) ⟨1108520, by rfl⟩ : syracuseStep 1478027 = 2217041) B2217041
theorem B1150359 : Blo 1148636 1150359 := bstep (se 1 (by rfl) ⟨862769, by rfl⟩ : syracuseStep 1150359 = 1725539) B1725539
theorem B1150379 : Blo 1148636 1150379 := bstep (se 1 (by rfl) ⟨862784, by rfl⟩ : syracuseStep 1150379 = 1725569) B1725569
theorem B2592179 : Blo 1148636 2592179 := bstep (se 1 (by rfl) ⟨1944134, by rfl⟩ : syracuseStep 2592179 = 3888269) B3888269
theorem B1150391 : Blo 1148636 1150391 := bstep (se 1 (by rfl) ⟨862793, by rfl⟩ : syracuseStep 1150391 = 1725587) B1725587
theorem B1150411 : Blo 1148636 1150411 := bstep (se 1 (by rfl) ⟨862808, by rfl⟩ : syracuseStep 1150411 = 1725617) B1725617
theorem B1150423 : Blo 1148636 1150423 := bstep (se 1 (by rfl) ⟨862817, by rfl⟩ : syracuseStep 1150423 = 1725635) B1725635
theorem B2592215 : Blo 1148636 2592215 := bstep (se 1 (by rfl) ⟨1944161, by rfl⟩ : syracuseStep 2592215 = 3888323) B3888323
theorem B1150443 : Blo 1148636 1150443 := bstep (se 1 (by rfl) ⟨862832, by rfl⟩ : syracuseStep 1150443 = 1725665) B1725665
theorem B1150455 : Blo 1148636 1150455 := bstep (se 1 (by rfl) ⟨862841, by rfl⟩ : syracuseStep 1150455 = 1725683) B1725683
theorem B1150475 : Blo 1148636 1150475 := bstep (se 1 (by rfl) ⟨862856, by rfl⟩ : syracuseStep 1150475 = 1725713) B1725713
theorem B2461195 : Blo 1148636 2461195 := bstep (se 1 (by rfl) ⟨1845896, by rfl⟩ : syracuseStep 2461195 = 3691793) B3691793
theorem B1150487 : Blo 1148636 1150487 := bstep (se 1 (by rfl) ⟨862865, by rfl⟩ : syracuseStep 1150487 = 1725731) B1725731
theorem B1150507 : Blo 1148636 1150507 := bstep (se 1 (by rfl) ⟨862880, by rfl⟩ : syracuseStep 1150507 = 1725761) B1725761
theorem B1150519 : Blo 1148636 1150519 := bstep (se 1 (by rfl) ⟨862889, by rfl⟩ : syracuseStep 1150519 = 1725779) B1725779
theorem B1150539 : Blo 1148636 1150539 := bstep (se 1 (by rfl) ⟨862904, by rfl⟩ : syracuseStep 1150539 = 1725809) B1725809
theorem B1150551 : Blo 1148636 1150551 := bstep (se 1 (by rfl) ⟨862913, by rfl⟩ : syracuseStep 1150551 = 1725827) B1725827
theorem B1150571 : Blo 1148636 1150571 := bstep (se 1 (by rfl) ⟨862928, by rfl⟩ : syracuseStep 1150571 = 1725857) B1725857
theorem B1150583 : Blo 1148636 1150583 := bstep (se 1 (by rfl) ⟨862937, by rfl⟩ : syracuseStep 1150583 = 1725875) B1725875
theorem B1150603 : Blo 1148636 1150603 := bstep (se 1 (by rfl) ⟨862952, by rfl⟩ : syracuseStep 1150603 = 1725905) B1725905
theorem B2592395 : Blo 1148636 2592395 := bstep (se 1 (by rfl) ⟨1944296, by rfl⟩ : syracuseStep 2592395 = 3888593) B3888593
theorem B1150615 : Blo 1148636 1150615 := bstep (se 1 (by rfl) ⟨862961, by rfl⟩ : syracuseStep 1150615 = 1725923) B1725923
theorem B1150635 : Blo 1148636 1150635 := bstep (se 1 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 1150635 = 1725953) B1725953
theorem B1150647 : Blo 1148636 1150647 := bstep (se 1 (by rfl) ⟨862985, by rfl⟩ : syracuseStep 1150647 = 1725971) B1725971
theorem B2592449 : Blo 1148636 2592449 := bstep (se 2 (by rfl) ⟨972168, by rfl⟩ : syracuseStep 2592449 = 1944337) B1944337
theorem B1150667 : Blo 1148636 1150667 := bstep (se 1 (by rfl) ⟨863000, by rfl⟩ : syracuseStep 1150667 = 1726001) B1726001
theorem B1150679 : Blo 1148636 1150679 := bstep (se 1 (by rfl) ⟨863009, by rfl⟩ : syracuseStep 1150679 = 1726019) B1726019
theorem B1150699 : Blo 1148636 1150699 := bstep (se 1 (by rfl) ⟨863024, by rfl⟩ : syracuseStep 1150699 = 1726049) B1726049
theorem B1150711 : Blo 1148636 1150711 := bstep (se 1 (by rfl) ⟨863033, by rfl⟩ : syracuseStep 1150711 = 1726067) B1726067
theorem B1150731 : Blo 1148636 1150731 := bstep (se 1 (by rfl) ⟨863048, by rfl⟩ : syracuseStep 1150731 = 1726097) B1726097
theorem B1150743 : Blo 1148636 1150743 := bstep (se 1 (by rfl) ⟨863057, by rfl⟩ : syracuseStep 1150743 = 1726115) B1726115
theorem B1150763 : Blo 1148636 1150763 := bstep (se 1 (by rfl) ⟨863072, by rfl⟩ : syracuseStep 1150763 = 1726145) B1726145
theorem B1150775 : Blo 1148636 1150775 := bstep (se 1 (by rfl) ⟨863081, by rfl⟩ : syracuseStep 1150775 = 1726163) B1726163
theorem B1150795 : Blo 1148636 1150795 := bstep (se 1 (by rfl) ⟨863096, by rfl⟩ : syracuseStep 1150795 = 1726193) B1726193
theorem B1150807 : Blo 1148636 1150807 := bstep (se 1 (by rfl) ⟨863105, by rfl⟩ : syracuseStep 1150807 = 1726211) B1726211
theorem B2461529 : Blo 1148636 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B1150827 : Blo 1148636 1150827 := bstep (se 1 (by rfl) ⟨863120, by rfl⟩ : syracuseStep 1150827 = 1726241) B1726241
theorem B1150839 : Blo 1148636 1150839 := bstep (se 1 (by rfl) ⟨863129, by rfl⟩ : syracuseStep 1150839 = 1726259) B1726259
theorem B1150859 : Blo 1148636 1150859 := bstep (se 1 (by rfl) ⟨863144, by rfl⟩ : syracuseStep 1150859 = 1726289) B1726289
theorem B1150871 : Blo 1148636 1150871 := bstep (se 1 (by rfl) ⟨863153, by rfl⟩ : syracuseStep 1150871 = 1726307) B1726307
theorem B2592665 : Blo 1148636 2592665 := bstep (se 2 (by rfl) ⟨972249, by rfl⟩ : syracuseStep 2592665 = 1944499) B1944499
theorem B1150891 : Blo 1148636 1150891 := bstep (se 1 (by rfl) ⟨863168, by rfl⟩ : syracuseStep 1150891 = 1726337) B1726337
theorem B3280819 : Blo 1148636 3280819 := bstep (se 1 (by rfl) ⟨2460614, by rfl⟩ : syracuseStep 3280819 = 4921229) B4921229
theorem B1150903 : Blo 1148636 1150903 := bstep (se 1 (by rfl) ⟨863177, by rfl⟩ : syracuseStep 1150903 = 1726355) B1726355
theorem B1150923 : Blo 1148636 1150923 := bstep (se 1 (by rfl) ⟨863192, by rfl⟩ : syracuseStep 1150923 = 1726385) B1726385
theorem B1150935 : Blo 1148636 1150935 := bstep (se 1 (by rfl) ⟨863201, by rfl⟩ : syracuseStep 1150935 = 1726403) B1726403
theorem B1150955 : Blo 1148636 1150955 := bstep (se 1 (by rfl) ⟨863216, by rfl⟩ : syracuseStep 1150955 = 1726433) B1726433
theorem B2592755 : Blo 1148636 2592755 := bstep (se 1 (by rfl) ⟨1944566, by rfl⟩ : syracuseStep 2592755 = 3889133) B3889133
theorem B1150967 : Blo 1148636 1150967 := bstep (se 1 (by rfl) ⟨863225, by rfl⟩ : syracuseStep 1150967 = 1726451) B1726451
theorem B1150987 : Blo 1148636 1150987 := bstep (se 1 (by rfl) ⟨863240, by rfl⟩ : syracuseStep 1150987 = 1726481) B1726481
theorem B1150999 : Blo 1148636 1150999 := bstep (se 1 (by rfl) ⟨863249, by rfl⟩ : syracuseStep 1150999 = 1726499) B1726499
theorem B2592791 : Blo 1148636 2592791 := bstep (se 1 (by rfl) ⟨1944593, by rfl⟩ : syracuseStep 2592791 = 3889187) B3889187
theorem B1151019 : Blo 1148636 1151019 := bstep (se 1 (by rfl) ⟨863264, by rfl⟩ : syracuseStep 1151019 = 1726529) B1726529
theorem B1151031 : Blo 1148636 1151031 := bstep (se 1 (by rfl) ⟨863273, by rfl⟩ : syracuseStep 1151031 = 1726547) B1726547
theorem B1151051 : Blo 1148636 1151051 := bstep (se 1 (by rfl) ⟨863288, by rfl⟩ : syracuseStep 1151051 = 1726577) B1726577
theorem B1151063 : Blo 1148636 1151063 := bstep (se 1 (by rfl) ⟨863297, by rfl⟩ : syracuseStep 1151063 = 1726595) B1726595
theorem B1151083 : Blo 1148636 1151083 := bstep (se 1 (by rfl) ⟨863312, by rfl⟩ : syracuseStep 1151083 = 1726625) B1726625
theorem B1151095 : Blo 1148636 1151095 := bstep (se 1 (by rfl) ⟨863321, by rfl⟩ : syracuseStep 1151095 = 1726643) B1726643
theorem B1151115 : Blo 1148636 1151115 := bstep (se 1 (by rfl) ⟨863336, by rfl⟩ : syracuseStep 1151115 = 1726673) B1726673
theorem B1151127 : Blo 1148636 1151127 := bstep (se 1 (by rfl) ⟨863345, by rfl⟩ : syracuseStep 1151127 = 1726691) B1726691
theorem B1151147 : Blo 1148636 1151147 := bstep (se 1 (by rfl) ⟨863360, by rfl⟩ : syracuseStep 1151147 = 1726721) B1726721
theorem B1151159 : Blo 1148636 1151159 := bstep (se 1 (by rfl) ⟨863369, by rfl⟩ : syracuseStep 1151159 = 1726739) B1726739
theorem B2363585 : Blo 1148636 2363585 := bstep (se 2 (by rfl) ⟨886344, by rfl⟩ : syracuseStep 2363585 = 1772689) B1772689
theorem B4362443 : Blo 1148636 4362443 := bstep (se 1 (by rfl) ⟨3271832, by rfl⟩ : syracuseStep 4362443 = 6543665) B6543665
theorem B1151179 : Blo 1148636 1151179 := bstep (se 1 (by rfl) ⟨863384, by rfl⟩ : syracuseStep 1151179 = 1726769) B1726769
theorem B2592971 : Blo 1148636 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B1151191 : Blo 1148636 1151191 := bstep (se 1 (by rfl) ⟨863393, by rfl⟩ : syracuseStep 1151191 = 1726787) B1726787
theorem B4362457 : Blo 1148636 4362457 := bstep (se 2 (by rfl) ⟨1635921, by rfl⟩ : syracuseStep 4362457 = 3271843) B3271843
theorem B1151211 : Blo 1148636 1151211 := bstep (se 1 (by rfl) ⟨863408, by rfl⟩ : syracuseStep 1151211 = 1726817) B1726817
theorem B2625779 : Blo 1148636 2625779 := bstep (se 1 (by rfl) ⟨1969334, by rfl⟩ : syracuseStep 2625779 = 3938669) B3938669
theorem B1151223 : Blo 1148636 1151223 := bstep (se 1 (by rfl) ⟨863417, by rfl⟩ : syracuseStep 1151223 = 1726835) B1726835
theorem B2593025 : Blo 1148636 2593025 := bstep (se 2 (by rfl) ⟨972384, by rfl⟩ : syracuseStep 2593025 = 1944769) B1944769
theorem B4919555 : Blo 1148636 4919555 := bstep (se 1 (by rfl) ⟨3689666, by rfl⟩ : syracuseStep 4919555 = 7379333) B7379333
theorem B1151243 : Blo 1148636 1151243 := bstep (se 1 (by rfl) ⟨863432, by rfl⟩ : syracuseStep 1151243 = 1726865) B1726865
theorem B1151255 : Blo 1148636 1151255 := bstep (se 1 (by rfl) ⟨863441, by rfl⟩ : syracuseStep 1151255 = 1726883) B1726883
theorem B1151275 : Blo 1148636 1151275 := bstep (se 1 (by rfl) ⟨863456, by rfl⟩ : syracuseStep 1151275 = 1726913) B1726913
theorem B1151287 : Blo 1148636 1151287 := bstep (se 1 (by rfl) ⟨863465, by rfl⟩ : syracuseStep 1151287 = 1726931) B1726931
theorem B1151307 : Blo 1148636 1151307 := bstep (se 1 (by rfl) ⟨863480, by rfl⟩ : syracuseStep 1151307 = 1726961) B1726961
theorem B1151319 : Blo 1148636 1151319 := bstep (se 1 (by rfl) ⟨863489, by rfl⟩ : syracuseStep 1151319 = 1726979) B1726979
theorem B1151339 : Blo 1148636 1151339 := bstep (se 1 (by rfl) ⟨863504, by rfl⟩ : syracuseStep 1151339 = 1727009) B1727009
theorem B1151351 : Blo 1148636 1151351 := bstep (se 1 (by rfl) ⟨863513, by rfl⟩ : syracuseStep 1151351 = 1727027) B1727027
theorem B1151371 : Blo 1148636 1151371 := bstep (se 1 (by rfl) ⟨863528, by rfl⟩ : syracuseStep 1151371 = 1727057) B1727057
theorem B1151383 : Blo 1148636 1151383 := bstep (se 1 (by rfl) ⟨863537, by rfl⟩ : syracuseStep 1151383 = 1727075) B1727075
theorem B1151403 : Blo 1148636 1151403 := bstep (se 1 (by rfl) ⟨863552, by rfl⟩ : syracuseStep 1151403 = 1727105) B1727105
theorem B1151415 : Blo 1148636 1151415 := bstep (se 1 (by rfl) ⟨863561, by rfl⟩ : syracuseStep 1151415 = 1727123) B1727123
theorem B1151435 : Blo 1148636 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B1151447 : Blo 1148636 1151447 := bstep (se 1 (by rfl) ⟨863585, by rfl⟩ : syracuseStep 1151447 = 1727171) B1727171
theorem B2593241 : Blo 1148636 2593241 := bstep (se 2 (by rfl) ⟨972465, by rfl⟩ : syracuseStep 2593241 = 1944931) B1944931
theorem B1151467 : Blo 1148636 1151467 := bstep (se 1 (by rfl) ⟨863600, by rfl⟩ : syracuseStep 1151467 = 1727201) B1727201
theorem B1151479 : Blo 1148636 1151479 := bstep (se 1 (by rfl) ⟨863609, by rfl⟩ : syracuseStep 1151479 = 1727219) B1727219
theorem B1151499 : Blo 1148636 1151499 := bstep (se 1 (by rfl) ⟨863624, by rfl⟩ : syracuseStep 1151499 = 1727249) B1727249
theorem B1151511 : Blo 1148636 1151511 := bstep (se 1 (by rfl) ⟨863633, by rfl⟩ : syracuseStep 1151511 = 1727267) B1727267
theorem B1151531 : Blo 1148636 1151531 := bstep (se 1 (by rfl) ⟨863648, by rfl⟩ : syracuseStep 1151531 = 1727297) B1727297
theorem B2593331 : Blo 1148636 2593331 := bstep (se 1 (by rfl) ⟨1944998, by rfl⟩ : syracuseStep 2593331 = 3889997) B3889997
theorem B1151543 : Blo 1148636 1151543 := bstep (se 1 (by rfl) ⟨863657, by rfl⟩ : syracuseStep 1151543 = 1727315) B1727315
theorem B1151563 : Blo 1148636 1151563 := bstep (se 1 (by rfl) ⟨863672, by rfl⟩ : syracuseStep 1151563 = 1727345) B1727345
theorem B1151575 : Blo 1148636 1151575 := bstep (se 1 (by rfl) ⟨863681, by rfl⟩ : syracuseStep 1151575 = 1727363) B1727363
theorem B2593367 : Blo 1148636 2593367 := bstep (se 1 (by rfl) ⟨1945025, by rfl⟩ : syracuseStep 2593367 = 3890051) B3890051
theorem B1151595 : Blo 1148636 1151595 := bstep (se 1 (by rfl) ⟨863696, by rfl⟩ : syracuseStep 1151595 = 1727393) B1727393
theorem B1151607 : Blo 1148636 1151607 := bstep (se 1 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 1151607 = 1727411) B1727411
theorem B1151627 : Blo 1148636 1151627 := bstep (se 1 (by rfl) ⟨863720, by rfl⟩ : syracuseStep 1151627 = 1727441) B1727441
theorem B1151639 : Blo 1148636 1151639 := bstep (se 1 (by rfl) ⟨863729, by rfl⟩ : syracuseStep 1151639 = 1727459) B1727459
theorem B1151659 : Blo 1148636 1151659 := bstep (se 1 (by rfl) ⟨863744, by rfl⟩ : syracuseStep 1151659 = 1727489) B1727489
theorem B1151671 : Blo 1148636 1151671 := bstep (se 1 (by rfl) ⟨863753, by rfl⟩ : syracuseStep 1151671 = 1727507) B1727507
theorem B1151691 : Blo 1148636 1151691 := bstep (se 1 (by rfl) ⟨863768, by rfl⟩ : syracuseStep 1151691 = 1727537) B1727537
theorem B1151703 : Blo 1148636 1151703 := bstep (se 1 (by rfl) ⟨863777, by rfl⟩ : syracuseStep 1151703 = 1727555) B1727555
theorem B1151723 : Blo 1148636 1151723 := bstep (se 1 (by rfl) ⟨863792, by rfl⟩ : syracuseStep 1151723 = 1727585) B1727585
theorem B1151735 : Blo 1148636 1151735 := bstep (se 1 (by rfl) ⟨863801, by rfl⟩ : syracuseStep 1151735 = 1727603) B1727603
theorem B10490629 : Blo 1148636 10490629 := bstep (se 4 (by rfl) ⟨983496, by rfl⟩ : syracuseStep 10490629 = 1966993) B1966993
theorem B1151755 : Blo 1148636 1151755 := bstep (se 1 (by rfl) ⟨863816, by rfl⟩ : syracuseStep 1151755 = 1727633) B1727633
theorem B1151767 : Blo 1148636 1151767 := bstep (se 1 (by rfl) ⟨863825, by rfl⟩ : syracuseStep 1151767 = 1727651) B1727651
theorem B1151787 : Blo 1148636 1151787 := bstep (se 1 (by rfl) ⟨863840, by rfl⟩ : syracuseStep 1151787 = 1727681) B1727681
theorem B1151799 : Blo 1148636 1151799 := bstep (se 1 (by rfl) ⟨863849, by rfl⟩ : syracuseStep 1151799 = 1727699) B1727699
theorem B1151819 : Blo 1148636 1151819 := bstep (se 1 (by rfl) ⟨863864, by rfl⟩ : syracuseStep 1151819 = 1727729) B1727729
theorem B1151831 : Blo 1148636 1151831 := bstep (se 1 (by rfl) ⟨863873, by rfl⟩ : syracuseStep 1151831 = 1727747) B1727747
theorem B1151851 : Blo 1148636 1151851 := bstep (se 1 (by rfl) ⟨863888, by rfl⟩ : syracuseStep 1151851 = 1727777) B1727777
theorem B1151863 : Blo 1148636 1151863 := bstep (se 1 (by rfl) ⟨863897, by rfl⟩ : syracuseStep 1151863 = 1727795) B1727795
theorem B1151883 : Blo 1148636 1151883 := bstep (se 1 (by rfl) ⟨863912, by rfl⟩ : syracuseStep 1151883 = 1727825) B1727825
theorem B1151895 : Blo 1148636 1151895 := bstep (se 1 (by rfl) ⟨863921, by rfl⟩ : syracuseStep 1151895 = 1727843) B1727843
theorem B1151915 : Blo 1148636 1151915 := bstep (se 1 (by rfl) ⟨863936, by rfl⟩ : syracuseStep 1151915 = 1727873) B1727873
theorem B22385585 : Blo 1148636 22385585 := bstep (se 2 (by rfl) ⟨8394594, by rfl⟩ : syracuseStep 22385585 = 16789189) B16789189
theorem B1151927 : Blo 1148636 1151927 := bstep (se 1 (by rfl) ⟨863945, by rfl⟩ : syracuseStep 1151927 = 1727891) B1727891
theorem B1151947 : Blo 1148636 1151947 := bstep (se 1 (by rfl) ⟨863960, by rfl⟩ : syracuseStep 1151947 = 1727921) B1727921
theorem B3281867 : Blo 1148636 3281867 := bstep (se 1 (by rfl) ⟨2461400, by rfl⟩ : syracuseStep 3281867 = 4922801) B4922801
theorem B1151959 : Blo 1148636 1151959 := bstep (se 1 (by rfl) ⟨863969, by rfl⟩ : syracuseStep 1151959 = 1727939) B1727939
theorem B1151979 : Blo 1148636 1151979 := bstep (se 1 (by rfl) ⟨863984, by rfl⟩ : syracuseStep 1151979 = 1727969) B1727969
theorem B1151991 : Blo 1148636 1151991 := bstep (se 1 (by rfl) ⟨863993, by rfl⟩ : syracuseStep 1151991 = 1727987) B1727987
theorem B1152011 : Blo 1148636 1152011 := bstep (se 1 (by rfl) ⟨864008, by rfl⟩ : syracuseStep 1152011 = 1728017) B1728017
theorem B1152023 : Blo 1148636 1152023 := bstep (se 1 (by rfl) ⟨864017, by rfl⟩ : syracuseStep 1152023 = 1728035) B1728035
theorem B1152043 : Blo 1148636 1152043 := bstep (se 1 (by rfl) ⟨864032, by rfl⟩ : syracuseStep 1152043 = 1728065) B1728065
theorem B1152055 : Blo 1148636 1152055 := bstep (se 1 (by rfl) ⟨864041, by rfl⟩ : syracuseStep 1152055 = 1728083) B1728083
theorem B1152075 : Blo 1148636 1152075 := bstep (se 1 (by rfl) ⟨864056, by rfl⟩ : syracuseStep 1152075 = 1728113) B1728113
theorem B1152087 : Blo 1148636 1152087 := bstep (se 1 (by rfl) ⟨864065, by rfl⟩ : syracuseStep 1152087 = 1728131) B1728131
theorem B1152107 : Blo 1148636 1152107 := bstep (se 1 (by rfl) ⟨864080, by rfl⟩ : syracuseStep 1152107 = 1728161) B1728161
theorem B1152119 : Blo 1148636 1152119 := bstep (se 1 (by rfl) ⟨864089, by rfl⟩ : syracuseStep 1152119 = 1728179) B1728179
theorem B1152139 : Blo 1148636 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B4363415 : Blo 1148636 4363415 := bstep (se 1 (by rfl) ⟨3272561, by rfl⟩ : syracuseStep 4363415 = 6545123) B6545123
theorem B1152151 : Blo 1148636 1152151 := bstep (se 1 (by rfl) ⟨864113, by rfl⟩ : syracuseStep 1152151 = 1728227) B1728227
theorem B1152171 : Blo 1148636 1152171 := bstep (se 1 (by rfl) ⟨864128, by rfl⟩ : syracuseStep 1152171 = 1728257) B1728257
theorem B1152183 : Blo 1148636 1152183 := bstep (se 1 (by rfl) ⟨864137, by rfl⟩ : syracuseStep 1152183 = 1728275) B1728275
theorem B1152203 : Blo 1148636 1152203 := bstep (se 1 (by rfl) ⟨864152, by rfl⟩ : syracuseStep 1152203 = 1728305) B1728305
theorem B1938647 : Blo 1148636 1938647 := bstep (se 1 (by rfl) ⟨1453985, by rfl⟩ : syracuseStep 1938647 = 2907971) B2907971
theorem B1578199 : Blo 1148636 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B1152215 : Blo 1148636 1152215 := bstep (se 1 (by rfl) ⟨864161, by rfl⟩ : syracuseStep 1152215 = 1728323) B1728323
theorem B1152235 : Blo 1148636 1152235 := bstep (se 1 (by rfl) ⟨864176, by rfl⟩ : syracuseStep 1152235 = 1728353) B1728353
theorem B1152247 : Blo 1148636 1152247 := bstep (se 1 (by rfl) ⟨864185, by rfl⟩ : syracuseStep 1152247 = 1728371) B1728371
theorem B1152267 : Blo 1148636 1152267 := bstep (se 1 (by rfl) ⟨864200, by rfl⟩ : syracuseStep 1152267 = 1728401) B1728401
theorem B1152279 : Blo 1148636 1152279 := bstep (se 1 (by rfl) ⟨864209, by rfl⟩ : syracuseStep 1152279 = 1728419) B1728419
theorem B1152299 : Blo 1148636 1152299 := bstep (se 1 (by rfl) ⟨864224, by rfl⟩ : syracuseStep 1152299 = 1728449) B1728449
theorem B1152311 : Blo 1148636 1152311 := bstep (se 1 (by rfl) ⟨864233, by rfl⟩ : syracuseStep 1152311 = 1728467) B1728467
theorem B1152331 : Blo 1148636 1152331 := bstep (se 1 (by rfl) ⟨864248, by rfl⟩ : syracuseStep 1152331 = 1728497) B1728497
theorem B1938775 : Blo 1148636 1938775 := bstep (se 1 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 1938775 = 2908163) B2908163
theorem B1152343 : Blo 1148636 1152343 := bstep (se 1 (by rfl) ⟨864257, by rfl⟩ : syracuseStep 1152343 = 1728515) B1728515
theorem B1152363 : Blo 1148636 1152363 := bstep (se 1 (by rfl) ⟨864272, by rfl⟩ : syracuseStep 1152363 = 1728545) B1728545
theorem B1152375 : Blo 1148636 1152375 := bstep (se 1 (by rfl) ⟨864281, by rfl⟩ : syracuseStep 1152375 = 1728563) B1728563
theorem B1152395 : Blo 1148636 1152395 := bstep (se 1 (by rfl) ⟨864296, by rfl⟩ : syracuseStep 1152395 = 1728593) B1728593
theorem B1152407 : Blo 1148636 1152407 := bstep (se 1 (by rfl) ⟨864305, by rfl⟩ : syracuseStep 1152407 = 1728611) B1728611
theorem B1152427 : Blo 1148636 1152427 := bstep (se 1 (by rfl) ⟨864320, by rfl⟩ : syracuseStep 1152427 = 1728641) B1728641
theorem B1152439 : Blo 1148636 1152439 := bstep (se 1 (by rfl) ⟨864329, by rfl⟩ : syracuseStep 1152439 = 1728659) B1728659
theorem B1152459 : Blo 1148636 1152459 := bstep (se 1 (by rfl) ⟨864344, by rfl⟩ : syracuseStep 1152459 = 1728689) B1728689
theorem B1152471 : Blo 1148636 1152471 := bstep (se 1 (by rfl) ⟨864353, by rfl⟩ : syracuseStep 1152471 = 1728707) B1728707
theorem B1152491 : Blo 1148636 1152491 := bstep (se 1 (by rfl) ⟨864368, by rfl⟩ : syracuseStep 1152491 = 1728737) B1728737
theorem B1152503 : Blo 1148636 1152503 := bstep (se 1 (by rfl) ⟨864377, by rfl⟩ : syracuseStep 1152503 = 1728755) B1728755
theorem B1152523 : Blo 1148636 1152523 := bstep (se 1 (by rfl) ⟨864392, by rfl⟩ : syracuseStep 1152523 = 1728785) B1728785
theorem B1152535 : Blo 1148636 1152535 := bstep (se 1 (by rfl) ⟨864401, by rfl⟩ : syracuseStep 1152535 = 1728803) B1728803
theorem B1152555 : Blo 1148636 1152555 := bstep (se 1 (by rfl) ⟨864416, by rfl⟩ : syracuseStep 1152555 = 1728833) B1728833
theorem B1152567 : Blo 1148636 1152567 := bstep (se 1 (by rfl) ⟨864425, by rfl⟩ : syracuseStep 1152567 = 1728851) B1728851
theorem B6067777 : Blo 1148636 6067777 := bstep (se 2 (by rfl) ⟨2275416, by rfl⟩ : syracuseStep 6067777 = 4550833) B4550833
theorem B1152587 : Blo 1148636 1152587 := bstep (se 1 (by rfl) ⟨864440, by rfl⟩ : syracuseStep 1152587 = 1728881) B1728881
theorem B1152599 : Blo 1148636 1152599 := bstep (se 1 (by rfl) ⟨864449, by rfl⟩ : syracuseStep 1152599 = 1728899) B1728899
theorem B1152619 : Blo 1148636 1152619 := bstep (se 1 (by rfl) ⟨864464, by rfl⟩ : syracuseStep 1152619 = 1728929) B1728929
theorem B1152631 : Blo 1148636 1152631 := bstep (se 1 (by rfl) ⟨864473, by rfl⟩ : syracuseStep 1152631 = 1728947) B1728947
theorem B2332289 : Blo 1148636 2332289 := bstep (se 2 (by rfl) ⟨874608, by rfl⟩ : syracuseStep 2332289 = 1749217) B1749217
theorem B3741335 : Blo 1148636 3741335 := bstep (se 1 (by rfl) ⟨2806001, by rfl⟩ : syracuseStep 3741335 = 5612003) B5612003
theorem B1939403 : Blo 1148636 1939403 := bstep (se 1 (by rfl) ⟨1454552, by rfl⟩ : syracuseStep 1939403 = 2909105) B2909105
theorem B9836579 : Blo 1148636 9836579 := bstep (se 1 (by rfl) ⟨7377434, by rfl⟩ : syracuseStep 9836579 = 14754869) B14754869
theorem B1939531 : Blo 1148636 1939531 := bstep (se 1 (by rfl) ⟨1454648, by rfl⟩ : syracuseStep 1939531 = 2909297) B2909297
theorem B2103383 : Blo 1148636 2103383 := bstep (se 1 (by rfl) ⟨1577537, by rfl⟩ : syracuseStep 2103383 = 3155075) B3155075
theorem B7379075 : Blo 1148636 7379075 := bstep (se 1 (by rfl) ⟨5534306, by rfl⟩ : syracuseStep 7379075 = 11068613) B11068613
theorem B2955457 : Blo 1148636 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B1939673 : Blo 1148636 1939673 := bstep (se 2 (by rfl) ⟨727377, by rfl⟩ : syracuseStep 1939673 = 1454755) B1454755
theorem B1939801 : Blo 1148636 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B11049317 : Blo 1148636 11049317 := bstep (se 4 (by rfl) ⟨1035873, by rfl⟩ : syracuseStep 11049317 = 2071747) B2071747
theorem B47356273 : Blo 1148636 47356273 := bstep (se 2 (by rfl) ⟨17758602, by rfl⟩ : syracuseStep 47356273 = 35517205) B35517205
theorem B4364675 : Blo 1148636 4364675 := bstep (se 1 (by rfl) ⟨3273506, by rfl⟩ : syracuseStep 4364675 = 6547013) B6547013
theorem B1940375 : Blo 1148636 1940375 := bstep (se 1 (by rfl) ⟨1455281, by rfl⟩ : syracuseStep 1940375 = 2910563) B2910563
theorem B2333683 : Blo 1148636 2333683 := bstep (se 1 (by rfl) ⟨1750262, by rfl⟩ : syracuseStep 2333683 = 3500525) B3500525
theorem B1940503 : Blo 1148636 1940503 := bstep (se 1 (by rfl) ⟨1455377, by rfl⟩ : syracuseStep 1940503 = 2910755) B2910755
theorem B99556613 : Blo 1148636 99556613 := bstep (se 4 (by rfl) ⟨9333432, by rfl⟩ : syracuseStep 99556613 = 18666865) B18666865
theorem B32349557 : Blo 1148636 32349557 := bstep (se 5 (by rfl) ⟨1516385, by rfl⟩ : syracuseStep 32349557 = 3032771) B3032771
theorem B17735203 : Blo 1148636 17735203 := bstep (se 1 (by rfl) ⟨13301402, by rfl⟩ : syracuseStep 17735203 = 26602805) B26602805
theorem B1941131 : Blo 1148636 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B2956979 : Blo 1148636 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B8724185 : Blo 1148636 8724185 := bstep (se 2 (by rfl) ⟨3271569, by rfl⟩ : syracuseStep 8724185 = 6543139) B6543139
theorem B1941259 : Blo 1148636 1941259 := bstep (se 1 (by rfl) ⟨1455944, by rfl⟩ : syracuseStep 1941259 = 2911889) B2911889
theorem B4661009 : Blo 1148636 4661009 := bstep (se 2 (by rfl) ⟨1747878, by rfl⟩ : syracuseStep 4661009 = 3495757) B3495757
theorem B1941401 : Blo 1148636 1941401 := bstep (se 2 (by rfl) ⟨728025, by rfl⟩ : syracuseStep 1941401 = 1456051) B1456051
theorem B1941529 : Blo 1148636 1941529 := bstep (se 2 (by rfl) ⟨728073, by rfl⟩ : syracuseStep 1941529 = 1456147) B1456147
theorem B6562093 : Blo 1148636 6562093 := bstep (se 3 (by rfl) ⟨1230392, by rfl⟩ : syracuseStep 6562093 = 2460785) B2460785
theorem B2335063 : Blo 1148636 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B2073089 : Blo 1148636 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B1942103 : Blo 1148636 1942103 := bstep (se 1 (by rfl) ⟨1456577, by rfl⟩ : syracuseStep 1942103 = 2913155) B2913155
theorem B1942231 : Blo 1148636 1942231 := bstep (se 1 (by rfl) ⟨1456673, by rfl⟩ : syracuseStep 1942231 = 2913347) B2913347
theorem B19669877 : Blo 1148636 19669877 := bstep (se 5 (by rfl) ⟨922025, by rfl⟩ : syracuseStep 19669877 = 1844051) B1844051
theorem B1942859 : Blo 1148636 1942859 := bstep (se 1 (by rfl) ⟨1457144, by rfl⟩ : syracuseStep 1942859 = 2914289) B2914289
theorem B8299907 : Blo 1148636 8299907 := bstep (se 1 (by rfl) ⟨6224930, by rfl⟩ : syracuseStep 8299907 = 12449861) B12449861
theorem B4367789 : Blo 1148636 4367789 := bstep (se 3 (by rfl) ⟨818960, by rfl⟩ : syracuseStep 4367789 = 1637921) B1637921
theorem B1942987 : Blo 1148636 1942987 := bstep (se 1 (by rfl) ⟨1457240, by rfl⟩ : syracuseStep 1942987 = 2914481) B2914481
theorem B9840203 : Blo 1148636 9840203 := bstep (se 1 (by rfl) ⟨7380152, by rfl⟩ : syracuseStep 9840203 = 14760305) B14760305
theorem B1943129 : Blo 1148636 1943129 := bstep (se 2 (by rfl) ⟨728673, by rfl⟩ : syracuseStep 1943129 = 1457347) B1457347
theorem B1943257 : Blo 1148636 1943257 := bstep (se 2 (by rfl) ⟨728721, by rfl⟩ : syracuseStep 1943257 = 1457443) B1457443
theorem B3876659 : Blo 1148636 3876659 := bstep (se 1 (by rfl) ⟨2907494, by rfl⟩ : syracuseStep 3876659 = 5814989) B5814989
theorem B2762561 : Blo 1148636 2762561 := bstep (se 2 (by rfl) ⟨1035960, by rfl⟩ : syracuseStep 2762561 = 2071921) B2071921
theorem B3876929 : Blo 1148636 3876929 := bstep (se 2 (by rfl) ⟨1453848, by rfl⟩ : syracuseStep 3876929 = 2907697) B2907697
theorem B4368563 : Blo 1148636 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B1943831 : Blo 1148636 1943831 := bstep (se 1 (by rfl) ⟨1457873, by rfl⟩ : syracuseStep 1943831 = 2915747) B2915747
theorem B4663603 : Blo 1148636 4663603 := bstep (se 1 (by rfl) ⟨3497702, by rfl⟩ : syracuseStep 4663603 = 6995405) B6995405
theorem B1943959 : Blo 1148636 1943959 := bstep (se 1 (by rfl) ⟨1457969, by rfl⟩ : syracuseStep 1943959 = 2915939) B2915939
theorem B9316825 : Blo 1148636 9316825 := bstep (se 2 (by rfl) ⟨3493809, by rfl⟩ : syracuseStep 9316825 = 6987619) B6987619
theorem B3877469 : Blo 1148636 3877469 := bstep (se 3 (by rfl) ⟨727025, by rfl⟩ : syracuseStep 3877469 = 1454051) B1454051
theorem B2698123 : Blo 1148636 2698123 := bstep (se 1 (by rfl) ⟨2023592, by rfl⟩ : syracuseStep 2698123 = 4047185) B4047185
theorem B1944587 : Blo 1148636 1944587 := bstep (se 1 (by rfl) ⟨1458440, by rfl⟩ : syracuseStep 1944587 = 2916881) B2916881
theorem B8727587 : Blo 1148636 8727587 := bstep (se 1 (by rfl) ⟨6545690, by rfl⟩ : syracuseStep 8727587 = 13091381) B13091381
theorem B1944715 : Blo 1148636 1944715 := bstep (se 1 (by rfl) ⟨1458536, by rfl⟩ : syracuseStep 1944715 = 2917073) B2917073
theorem B1748171 : Blo 1148636 1748171 := bstep (se 1 (by rfl) ⟨1311128, by rfl⟩ : syracuseStep 1748171 = 2622257) B2622257
theorem B1944857 : Blo 1148636 1944857 := bstep (se 2 (by rfl) ⟨729321, by rfl⟩ : syracuseStep 1944857 = 1458643) B1458643
theorem B4664641 : Blo 1148636 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B1944985 : Blo 1148636 1944985 := bstep (se 2 (by rfl) ⟨729369, by rfl⟩ : syracuseStep 1944985 = 1458739) B1458739
theorem B4140467 : Blo 1148636 4140467 := bstep (se 1 (by rfl) ⟨3105350, by rfl⟩ : syracuseStep 4140467 = 6210701) B6210701
theorem B4370051 : Blo 1148636 4370051 := bstep (se 1 (by rfl) ⟨3277538, by rfl⟩ : syracuseStep 4370051 = 6555077) B6555077
theorem B1748633 : Blo 1148636 1748633 := bstep (se 2 (by rfl) ⟨655737, by rfl⟩ : syracuseStep 1748633 = 1311475) B1311475
theorem B3878603 : Blo 1148636 3878603 := bstep (se 1 (by rfl) ⟨2908952, by rfl⟩ : syracuseStep 3878603 = 5817905) B5817905
theorem B1453783 : Blo 1148636 1453783 := bstep (se 1 (by rfl) ⟨1090337, by rfl⟩ : syracuseStep 1453783 = 2180675) B2180675
theorem B2076403 : Blo 1148636 2076403 := bstep (se 1 (by rfl) ⟨1557302, by rfl⟩ : syracuseStep 2076403 = 3114605) B3114605
theorem B2076491 : Blo 1148636 2076491 := bstep (se 1 (by rfl) ⟨1557368, by rfl⟩ : syracuseStep 2076491 = 3114737) B3114737
theorem B3878873 : Blo 1148636 3878873 := bstep (se 2 (by rfl) ⟨1454577, by rfl⟩ : syracuseStep 3878873 = 2909155) B2909155
theorem B4370507 : Blo 1148636 4370507 := bstep (se 1 (by rfl) ⟨3277880, by rfl⟩ : syracuseStep 4370507 = 6555761) B6555761
theorem B4141145 : Blo 1148636 4141145 := bstep (se 2 (by rfl) ⟨1552929, by rfl⟩ : syracuseStep 4141145 = 3105859) B3105859
theorem B9842867 : Blo 1148636 9842867 := bstep (se 1 (by rfl) ⟨7382150, by rfl⟩ : syracuseStep 9842867 = 14764301) B14764301
theorem B4141273 : Blo 1148636 4141273 := bstep (se 2 (by rfl) ⟨1552977, by rfl⟩ : syracuseStep 4141273 = 3105955) B3105955
theorem B4370705 : Blo 1148636 4370705 := bstep (se 2 (by rfl) ⟨1639014, by rfl⟩ : syracuseStep 4370705 = 3278029) B3278029
theorem B59683189 : Blo 1148636 59683189 := bstep (se 5 (by rfl) ⟨2797649, by rfl⟩ : syracuseStep 59683189 = 5595299) B5595299
theorem B3879575 : Blo 1148636 3879575 := bstep (se 1 (by rfl) ⟨2909681, by rfl⟩ : syracuseStep 3879575 = 5819363) B5819363
theorem B4371479 : Blo 1148636 4371479 := bstep (se 1 (by rfl) ⟨3278609, by rfl⟩ : syracuseStep 4371479 = 6557219) B6557219
theorem B3880115 : Blo 1148636 3880115 := bstep (se 1 (by rfl) ⟨2910086, by rfl⟩ : syracuseStep 3880115 = 5820173) B5820173
theorem B5256371 : Blo 1148636 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B9843929 : Blo 1148636 9843929 := bstep (se 2 (by rfl) ⟨3691473, by rfl⟩ : syracuseStep 9843929 = 7382947) B7382947
theorem B4371677 : Blo 1148636 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B2766145 : Blo 1148636 2766145 := bstep (se 2 (by rfl) ⟨1037304, by rfl⟩ : syracuseStep 2766145 = 2074609) B2074609
theorem B1455499 : Blo 1148636 1455499 := bstep (se 1 (by rfl) ⟨1091624, by rfl⟩ : syracuseStep 1455499 = 2183249) B2183249
theorem B3880385 : Blo 1148636 3880385 := bstep (se 2 (by rfl) ⟨1455144, by rfl⟩ : syracuseStep 3880385 = 2910289) B2910289
theorem B1553995 : Blo 1148636 1553995 := bstep (se 1 (by rfl) ⟨1165496, by rfl⟩ : syracuseStep 1553995 = 2330993) B2330993
theorem B37303901 : Blo 1148636 37303901 := bstep (se 3 (by rfl) ⟨6994481, by rfl⟩ : syracuseStep 37303901 = 13988963) B13988963
theorem B1226711 : Blo 1148636 1226711 := bstep (se 1 (by rfl) ⟨920033, by rfl⟩ : syracuseStep 1226711 = 1840067) B1840067
theorem B3880925 : Blo 1148636 3880925 := bstep (se 3 (by rfl) ⟨727673, by rfl⟩ : syracuseStep 3880925 = 1455347) B1455347
theorem B6994021 : Blo 1148636 6994021 := bstep (se 4 (by rfl) ⟨655689, by rfl⟩ : syracuseStep 6994021 = 1311379) B1311379
theorem B1292395 : Blo 1148636 1292395 := bstep (se 1 (by rfl) ⟨969296, by rfl⟩ : syracuseStep 1292395 = 1938593) B1938593
theorem B3684503 : Blo 1148636 3684503 := bstep (se 1 (by rfl) ⟨2763377, by rfl⟩ : syracuseStep 3684503 = 5526755) B5526755
theorem B1292503 : Blo 1148636 1292503 := bstep (se 1 (by rfl) ⟨969377, by rfl⟩ : syracuseStep 1292503 = 1938755) B1938755
theorem B1456471 : Blo 1148636 1456471 := bstep (se 1 (by rfl) ⟨1092353, by rfl⟩ : syracuseStep 1456471 = 2184707) B2184707
theorem B2767193 : Blo 1148636 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B1292683 : Blo 1148636 1292683 := bstep (se 1 (by rfl) ⟨969512, by rfl⟩ : syracuseStep 1292683 = 1939025) B1939025
theorem B3684811 : Blo 1148636 3684811 := bstep (se 1 (by rfl) ⟨2763608, by rfl⟩ : syracuseStep 3684811 = 5527217) B5527217
theorem B1292791 : Blo 1148636 1292791 := bstep (se 1 (by rfl) ⟨969593, by rfl⟩ : syracuseStep 1292791 = 1939187) B1939187
theorem B9320977 : Blo 1148636 9320977 := bstep (se 2 (by rfl) ⟨3495366, by rfl⟩ : syracuseStep 9320977 = 6990733) B6990733
theorem B1555033 : Blo 1148636 1555033 := bstep (se 2 (by rfl) ⟨583137, by rfl⟩ : syracuseStep 1555033 = 1166275) B1166275
theorem B1227403 : Blo 1148636 1227403 := bstep (se 1 (by rfl) ⟨920552, by rfl⟩ : syracuseStep 1227403 = 1841105) B1841105
theorem B1292971 : Blo 1148636 1292971 := bstep (se 1 (by rfl) ⟨969728, by rfl⟩ : syracuseStep 1292971 = 1939457) B1939457
theorem B1293079 : Blo 1148636 1293079 := bstep (se 1 (by rfl) ⟨969809, by rfl⟩ : syracuseStep 1293079 = 1939619) B1939619
theorem B2210635 : Blo 1148636 2210635 := bstep (se 1 (by rfl) ⟨1657976, by rfl⟩ : syracuseStep 2210635 = 3315953) B3315953
theorem B1293259 : Blo 1148636 1293259 := bstep (se 1 (by rfl) ⟨969944, by rfl⟩ : syracuseStep 1293259 = 1939889) B1939889
theorem B5815313 : Blo 1148636 5815313 := bstep (se 2 (by rfl) ⟨2180742, by rfl⟩ : syracuseStep 5815313 = 4361485) B4361485
theorem B1293367 : Blo 1148636 1293367 := bstep (se 1 (by rfl) ⟨970025, by rfl⟩ : syracuseStep 1293367 = 1940051) B1940051
theorem B3882059 : Blo 1148636 3882059 := bstep (se 1 (by rfl) ⟨2911544, by rfl⟩ : syracuseStep 3882059 = 5823089) B5823089
theorem B13089923 : Blo 1148636 13089923 := bstep (se 1 (by rfl) ⟨9817442, by rfl⟩ : syracuseStep 13089923 = 19634885) B19634885
theorem B4373635 : Blo 1148636 4373635 := bstep (se 1 (by rfl) ⟨3280226, by rfl⟩ : syracuseStep 4373635 = 6560453) B6560453
theorem B1457291 : Blo 1148636 1457291 := bstep (se 1 (by rfl) ⟨1092968, by rfl⟩ : syracuseStep 1457291 = 2185937) B2185937
theorem B5815475 : Blo 1148636 5815475 := bstep (se 1 (by rfl) ⟨4361606, by rfl⟩ : syracuseStep 5815475 = 8723213) B8723213
theorem B1293547 : Blo 1148636 1293547 := bstep (se 1 (by rfl) ⟨970160, by rfl⟩ : syracuseStep 1293547 = 1940321) B1940321
theorem B19643633 : Blo 1148636 19643633 := bstep (se 2 (by rfl) ⟨7366362, by rfl⟩ : syracuseStep 19643633 = 14732725) B14732725
theorem B1293655 : Blo 1148636 1293655 := bstep (se 1 (by rfl) ⟨970241, by rfl⟩ : syracuseStep 1293655 = 1940483) B1940483
theorem B3882329 : Blo 1148636 3882329 := bstep (se 2 (by rfl) ⟨1455873, by rfl⟩ : syracuseStep 3882329 = 2911747) B2911747
theorem B14728625 : Blo 1148636 14728625 := bstep (se 2 (by rfl) ⟨5523234, by rfl⟩ : syracuseStep 14728625 = 11046469) B11046469
theorem B4373939 : Blo 1148636 4373939 := bstep (se 1 (by rfl) ⟨3280454, by rfl⟩ : syracuseStep 4373939 = 6560909) B6560909
theorem B1293835 : Blo 1148636 1293835 := bstep (se 1 (by rfl) ⟨970376, by rfl⟩ : syracuseStep 1293835 = 1940753) B1940753
theorem B1293943 : Blo 1148636 1293943 := bstep (se 1 (by rfl) ⟨970457, by rfl⟩ : syracuseStep 1293943 = 1940915) B1940915
theorem B2211545 : Blo 1148636 2211545 := bstep (se 2 (by rfl) ⟨829329, by rfl⟩ : syracuseStep 2211545 = 1658659) B1658659
theorem B1294123 : Blo 1148636 1294123 := bstep (se 1 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 1294123 = 1941185) B1941185
theorem B1457995 : Blo 1148636 1457995 := bstep (se 1 (by rfl) ⟨1093496, by rfl⟩ : syracuseStep 1457995 = 2186993) B2186993
theorem B1294231 : Blo 1148636 1294231 := bstep (se 1 (by rfl) ⟨970673, by rfl⟩ : syracuseStep 1294231 = 1941347) B1941347
theorem B1228727 : Blo 1148636 1228727 := bstep (se 1 (by rfl) ⟨921545, by rfl⟩ : syracuseStep 1228727 = 1843091) B1843091
theorem B2244545 : Blo 1148636 2244545 := bstep (se 2 (by rfl) ⟨841704, by rfl⟩ : syracuseStep 2244545 = 1683409) B1683409
theorem B2211851 : Blo 1148636 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B3883031 : Blo 1148636 3883031 := bstep (se 1 (by rfl) ⟨2912273, by rfl⟩ : syracuseStep 3883031 = 5824547) B5824547
theorem B1228855 : Blo 1148636 1228855 := bstep (se 1 (by rfl) ⟨921641, by rfl⟩ : syracuseStep 1228855 = 1843283) B1843283
theorem B4374593 : Blo 1148636 4374593 := bstep (se 2 (by rfl) ⟨1640472, by rfl⟩ : syracuseStep 4374593 = 3280945) B3280945
theorem B1294411 : Blo 1148636 1294411 := bstep (se 1 (by rfl) ⟨970808, by rfl⟩ : syracuseStep 1294411 = 1941617) B1941617
theorem B1458263 : Blo 1148636 1458263 := bstep (se 1 (by rfl) ⟨1093697, by rfl⟩ : syracuseStep 1458263 = 2187395) B2187395
theorem B1294519 : Blo 1148636 1294519 := bstep (se 1 (by rfl) ⟨970889, by rfl⟩ : syracuseStep 1294519 = 1941779) B1941779
theorem B8732933 : Blo 1148636 8732933 := bstep (se 4 (by rfl) ⟨818712, by rfl⟩ : syracuseStep 8732933 = 1637425) B1637425
theorem B1294699 : Blo 1148636 1294699 := bstep (se 1 (by rfl) ⟨971024, by rfl⟩ : syracuseStep 1294699 = 1942049) B1942049
theorem B1294807 : Blo 1148636 1294807 := bstep (se 1 (by rfl) ⟨971105, by rfl⟩ : syracuseStep 1294807 = 1942211) B1942211
theorem B4145687 : Blo 1148636 4145687 := bstep (se 1 (by rfl) ⟨3109265, by rfl⟩ : syracuseStep 4145687 = 6218531) B6218531
theorem B3883571 : Blo 1148636 3883571 := bstep (se 1 (by rfl) ⟨2912678, by rfl⟩ : syracuseStep 3883571 = 5825357) B5825357
theorem B1229419 : Blo 1148636 1229419 := bstep (se 1 (by rfl) ⟨922064, by rfl⟩ : syracuseStep 1229419 = 1844129) B1844129
theorem B1294987 : Blo 1148636 1294987 := bstep (se 1 (by rfl) ⟨971240, by rfl⟩ : syracuseStep 1294987 = 1942481) B1942481
theorem B1295095 : Blo 1148636 1295095 := bstep (se 1 (by rfl) ⟨971321, by rfl⟩ : syracuseStep 1295095 = 1942643) B1942643
theorem B3883841 : Blo 1148636 3883841 := bstep (se 2 (by rfl) ⟨1456440, by rfl⟩ : syracuseStep 3883841 = 2912881) B2912881
theorem B1229675 : Blo 1148636 1229675 := bstep (se 1 (by rfl) ⟨922256, by rfl⟩ : syracuseStep 1229675 = 1844513) B1844513
theorem B1295275 : Blo 1148636 1295275 := bstep (se 1 (by rfl) ⟨971456, by rfl⟩ : syracuseStep 1295275 = 1942913) B1942913
theorem B3687385 : Blo 1148636 3687385 := bstep (se 2 (by rfl) ⟨1382769, by rfl⟩ : syracuseStep 3687385 = 2765539) B2765539
theorem B1295383 : Blo 1148636 1295383 := bstep (se 1 (by rfl) ⟨971537, by rfl⟩ : syracuseStep 1295383 = 1943075) B1943075
theorem B5817419 : Blo 1148636 5817419 := bstep (se 1 (by rfl) ⟨4363064, by rfl⟩ : syracuseStep 5817419 = 8726129) B8726129
theorem B8307805 : Blo 1148636 8307805 := bstep (se 3 (by rfl) ⟨1557713, by rfl⟩ : syracuseStep 8307805 = 3115427) B3115427
theorem B1295563 : Blo 1148636 1295563 := bstep (se 1 (by rfl) ⟨971672, by rfl⟩ : syracuseStep 1295563 = 1943345) B1943345
theorem B4375853 : Blo 1148636 4375853 := bstep (se 3 (by rfl) ⟨820472, by rfl⟩ : syracuseStep 4375853 = 1640945) B1640945
theorem B1295671 : Blo 1148636 1295671 := bstep (se 1 (by rfl) ⟨971753, by rfl⟩ : syracuseStep 1295671 = 1943507) B1943507
theorem B4375883 : Blo 1148636 4375883 := bstep (se 1 (by rfl) ⟨3281912, by rfl⟩ : syracuseStep 4375883 = 6563825) B6563825
theorem B3884381 : Blo 1148636 3884381 := bstep (se 3 (by rfl) ⟨728321, by rfl⟩ : syracuseStep 3884381 = 1456643) B1456643
theorem B1295851 : Blo 1148636 1295851 := bstep (se 1 (by rfl) ⟨971888, by rfl⟩ : syracuseStep 1295851 = 1943777) B1943777
theorem B3688001 : Blo 1148636 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B1295959 : Blo 1148636 1295959 := bstep (se 1 (by rfl) ⟨971969, by rfl⟩ : syracuseStep 1295959 = 1943939) B1943939
theorem B1296139 : Blo 1148636 1296139 := bstep (se 1 (by rfl) ⟨972104, by rfl⟩ : syracuseStep 1296139 = 1944209) B1944209
theorem B1165099 : Blo 1148636 1165099 := bstep (se 1 (by rfl) ⟨873824, by rfl⟩ : syracuseStep 1165099 = 1747649) B1747649
theorem B9946955 : Blo 1148636 9946955 := bstep (se 1 (by rfl) ⟨7460216, by rfl⟩ : syracuseStep 9946955 = 14920433) B14920433
theorem B1296247 : Blo 1148636 1296247 := bstep (se 1 (by rfl) ⟨972185, by rfl⟩ : syracuseStep 1296247 = 1944371) B1944371
theorem B2181107 : Blo 1148636 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B1296427 : Blo 1148636 1296427 := bstep (se 1 (by rfl) ⟨972320, by rfl⟩ : syracuseStep 1296427 = 1944641) B1944641
theorem B4671553 : Blo 1148636 4671553 := bstep (se 2 (by rfl) ⟨1751832, by rfl⟩ : syracuseStep 4671553 = 3503665) B3503665
theorem B2181259 : Blo 1148636 2181259 := bstep (se 1 (by rfl) ⟨1635944, by rfl⟩ : syracuseStep 2181259 = 3271889) B3271889
theorem B1296535 : Blo 1148636 1296535 := bstep (se 1 (by rfl) ⟨972401, by rfl⟩ : syracuseStep 1296535 = 1944803) B1944803
theorem B1296715 : Blo 1148636 1296715 := bstep (se 1 (by rfl) ⟨972536, by rfl⟩ : syracuseStep 1296715 = 1945073) B1945073
theorem B16566707 : Blo 1148636 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B1165771 : Blo 1148636 1165771 := bstep (se 1 (by rfl) ⟨874328, by rfl⟩ : syracuseStep 1165771 = 1748657) B1748657
theorem B3885515 : Blo 1148636 3885515 := bstep (se 1 (by rfl) ⟨2914136, by rfl⟩ : syracuseStep 3885515 = 5828273) B5828273
theorem B2181593 : Blo 1148636 2181593 := bstep (se 2 (by rfl) ⟨818097, by rfl⟩ : syracuseStep 2181593 = 1636195) B1636195
theorem B8735363 : Blo 1148636 8735363 := bstep (se 1 (by rfl) ⟨6551522, by rfl⟩ : syracuseStep 8735363 = 13103045) B13103045
theorem B1723019 : Blo 1148636 1723019 := bstep (se 1 (by rfl) ⟨1292264, by rfl⟩ : syracuseStep 1723019 = 2584529) B2584529
theorem B1723031 : Blo 1148636 1723031 := bstep (se 1 (by rfl) ⟨1292273, by rfl⟩ : syracuseStep 1723031 = 2584547) B2584547
theorem B3787415 : Blo 1148636 3787415 := bstep (se 1 (by rfl) ⟨2840561, by rfl⟩ : syracuseStep 3787415 = 5681123) B5681123
theorem B1723097 : Blo 1148636 1723097 := bstep (se 2 (by rfl) ⟨646161, by rfl⟩ : syracuseStep 1723097 = 1292323) B1292323
theorem B3885785 : Blo 1148636 3885785 := bstep (se 2 (by rfl) ⟨1457169, by rfl⟩ : syracuseStep 3885785 = 2914339) B2914339
theorem B19942129 : Blo 1148636 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B5819201 : Blo 1148636 5819201 := bstep (se 2 (by rfl) ⟨2182200, by rfl⟩ : syracuseStep 5819201 = 4364401) B4364401
theorem B1723211 : Blo 1148636 1723211 := bstep (se 1 (by rfl) ⟨1292408, by rfl⟩ : syracuseStep 1723211 = 2584817) B2584817
theorem B1723223 : Blo 1148636 1723223 := bstep (se 1 (by rfl) ⟨1292417, by rfl⟩ : syracuseStep 1723223 = 2584835) B2584835
theorem B1723289 : Blo 1148636 1723289 := bstep (se 2 (by rfl) ⟨646233, by rfl⟩ : syracuseStep 1723289 = 1292467) B1292467
theorem B1723403 : Blo 1148636 1723403 := bstep (se 1 (by rfl) ⟨1292552, by rfl⟩ : syracuseStep 1723403 = 2585105) B2585105
theorem B1723415 : Blo 1148636 1723415 := bstep (se 1 (by rfl) ⟨1292561, by rfl⟩ : syracuseStep 1723415 = 2585123) B2585123
theorem B2182231 : Blo 1148636 2182231 := bstep (se 1 (by rfl) ⟨1636673, by rfl⟩ : syracuseStep 2182231 = 3273347) B3273347
theorem B1723481 : Blo 1148636 1723481 := bstep (se 2 (by rfl) ⟨646305, by rfl⟩ : syracuseStep 1723481 = 1292611) B1292611
theorem B4672685 : Blo 1148636 4672685 := bstep (se 3 (by rfl) ⟨876128, by rfl⟩ : syracuseStep 4672685 = 1752257) B1752257
theorem B1723595 : Blo 1148636 1723595 := bstep (se 1 (by rfl) ⟨1292696, by rfl⟩ : syracuseStep 1723595 = 2585393) B2585393
theorem B1723607 : Blo 1148636 1723607 := bstep (se 1 (by rfl) ⟨1292705, by rfl⟩ : syracuseStep 1723607 = 2585411) B2585411
theorem B1723673 : Blo 1148636 1723673 := bstep (se 2 (by rfl) ⟨646377, by rfl⟩ : syracuseStep 1723673 = 1292755) B1292755
theorem B35966321 : Blo 1148636 35966321 := bstep (se 2 (by rfl) ⟨13487370, by rfl⟩ : syracuseStep 35966321 = 26974741) B26974741
theorem B1723787 : Blo 1148636 1723787 := bstep (se 1 (by rfl) ⟨1292840, by rfl⟩ : syracuseStep 1723787 = 2585681) B2585681
theorem B1723799 : Blo 1148636 1723799 := bstep (se 1 (by rfl) ⟨1292849, by rfl⟩ : syracuseStep 1723799 = 2585699) B2585699
theorem B3886487 : Blo 1148636 3886487 := bstep (se 1 (by rfl) ⟨2914865, by rfl⟩ : syracuseStep 3886487 = 5829731) B5829731
theorem B1723865 : Blo 1148636 1723865 := bstep (se 2 (by rfl) ⟨646449, by rfl⟩ : syracuseStep 1723865 = 1292899) B1292899
theorem B1166891 : Blo 1148636 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B1723979 : Blo 1148636 1723979 := bstep (se 1 (by rfl) ⟨1292984, by rfl⟩ : syracuseStep 1723979 = 2585969) B2585969
theorem B1166923 : Blo 1148636 1166923 := bstep (se 1 (by rfl) ⟨875192, by rfl⟩ : syracuseStep 1166923 = 1750385) B1750385
theorem B1723991 : Blo 1148636 1723991 := bstep (se 1 (by rfl) ⟨1292993, by rfl⟩ : syracuseStep 1723991 = 2585987) B2585987
theorem B1724057 : Blo 1148636 1724057 := bstep (se 2 (by rfl) ⟨646521, by rfl⟩ : syracuseStep 1724057 = 1293043) B1293043
theorem B1724171 : Blo 1148636 1724171 := bstep (se 1 (by rfl) ⟨1293128, by rfl⟩ : syracuseStep 1724171 = 2586257) B2586257
theorem B1724183 : Blo 1148636 1724183 := bstep (se 1 (by rfl) ⟨1293137, by rfl⟩ : syracuseStep 1724183 = 2586275) B2586275
theorem B1724249 : Blo 1148636 1724249 := bstep (se 2 (by rfl) ⟨646593, by rfl⟩ : syracuseStep 1724249 = 1293187) B1293187
theorem B4673369 : Blo 1148636 4673369 := bstep (se 2 (by rfl) ⟨1752513, by rfl⟩ : syracuseStep 4673369 = 3505027) B3505027
theorem B18665315 : Blo 1148636 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B2183051 : Blo 1148636 2183051 := bstep (se 1 (by rfl) ⟨1637288, by rfl⟩ : syracuseStep 2183051 = 3274577) B3274577
theorem B3887027 : Blo 1148636 3887027 := bstep (se 1 (by rfl) ⟨2915270, by rfl⟩ : syracuseStep 3887027 = 5830541) B5830541
theorem B2183105 : Blo 1148636 2183105 := bstep (se 2 (by rfl) ⟨818664, by rfl⟩ : syracuseStep 2183105 = 1637329) B1637329
theorem B1724363 : Blo 1148636 1724363 := bstep (se 1 (by rfl) ⟨1293272, by rfl⟩ : syracuseStep 1724363 = 2586545) B2586545
theorem B1724375 : Blo 1148636 1724375 := bstep (se 1 (by rfl) ⟨1293281, by rfl⟩ : syracuseStep 1724375 = 2586563) B2586563
theorem B3690461 : Blo 1148636 3690461 := bstep (se 3 (by rfl) ⟨691961, by rfl⟩ : syracuseStep 3690461 = 1383923) B1383923
theorem B1724441 : Blo 1148636 1724441 := bstep (se 2 (by rfl) ⟨646665, by rfl⟩ : syracuseStep 1724441 = 1293331) B1293331
theorem B1724555 : Blo 1148636 1724555 := bstep (se 1 (by rfl) ⟨1293416, by rfl⟩ : syracuseStep 1724555 = 2586833) B2586833
theorem B1724567 : Blo 1148636 1724567 := bstep (se 1 (by rfl) ⟨1293425, by rfl⟩ : syracuseStep 1724567 = 2586851) B2586851
theorem B689950871 : Blo 1148636 689950871 := bstep (se 1 (by rfl) ⟨517463153, by rfl⟩ : syracuseStep 689950871 = 1034926307) B1034926307
theorem B13127831 : Blo 1148636 13127831 := bstep (se 1 (by rfl) ⟨9845873, by rfl⟩ : syracuseStep 13127831 = 19691747) B19691747
theorem B3887297 : Blo 1148636 3887297 := bstep (se 2 (by rfl) ⟨1457736, by rfl⟩ : syracuseStep 3887297 = 2915473) B2915473
theorem B1724633 : Blo 1148636 1724633 := bstep (se 2 (by rfl) ⟨646737, by rfl⟩ : syracuseStep 1724633 = 1293475) B1293475
theorem B1724747 : Blo 1148636 1724747 := bstep (se 1 (by rfl) ⟨1293560, by rfl⟩ : syracuseStep 1724747 = 2587121) B2587121
theorem B1724759 : Blo 1148636 1724759 := bstep (se 1 (by rfl) ⟨1293569, by rfl⟩ : syracuseStep 1724759 = 2587139) B2587139
theorem B1724825 : Blo 1148636 1724825 := bstep (se 2 (by rfl) ⟨646809, by rfl⟩ : syracuseStep 1724825 = 1293619) B1293619
theorem B1724939 : Blo 1148636 1724939 := bstep (se 1 (by rfl) ⟨1293704, by rfl⟩ : syracuseStep 1724939 = 2587409) B2587409
theorem B1724951 : Blo 1148636 1724951 := bstep (se 1 (by rfl) ⟨1293713, by rfl⟩ : syracuseStep 1724951 = 2587427) B2587427
theorem B1725017 : Blo 1148636 1725017 := bstep (se 2 (by rfl) ⟨646881, by rfl⟩ : syracuseStep 1725017 = 1293763) B1293763
theorem B6541955 : Blo 1148636 6541955 := bstep (se 1 (by rfl) ⟨4906466, by rfl⟩ : syracuseStep 6541955 = 9812933) B9812933
theorem B1725131 : Blo 1148636 1725131 := bstep (se 1 (by rfl) ⟨1293848, by rfl⟩ : syracuseStep 1725131 = 2587697) B2587697
theorem B1725143 : Blo 1148636 1725143 := bstep (se 1 (by rfl) ⟨1293857, by rfl⟩ : syracuseStep 1725143 = 2587715) B2587715
theorem B5821145 : Blo 1148636 5821145 := bstep (se 2 (by rfl) ⟨2182929, by rfl⟩ : syracuseStep 5821145 = 4365859) B4365859
theorem B3887837 : Blo 1148636 3887837 := bstep (se 3 (by rfl) ⟨728969, by rfl⟩ : syracuseStep 3887837 = 1457939) B1457939
theorem B1659673 : Blo 1148636 1659673 := bstep (se 2 (by rfl) ⟨622377, by rfl⟩ : syracuseStep 1659673 = 1244755) B1244755
theorem B1725209 : Blo 1148636 1725209 := bstep (se 2 (by rfl) ⟨646953, by rfl⟩ : syracuseStep 1725209 = 1293907) B1293907
theorem B2184023 : Blo 1148636 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B1725323 : Blo 1148636 1725323 := bstep (se 1 (by rfl) ⟨1293992, by rfl⟩ : syracuseStep 1725323 = 2587985) B2587985
theorem B1725335 : Blo 1148636 1725335 := bstep (se 1 (by rfl) ⟨1294001, by rfl⟩ : syracuseStep 1725335 = 2588003) B2588003
theorem B1725401 : Blo 1148636 1725401 := bstep (se 2 (by rfl) ⟨647025, by rfl⟩ : syracuseStep 1725401 = 1294051) B1294051
theorem B1725515 : Blo 1148636 1725515 := bstep (se 1 (by rfl) ⟨1294136, by rfl⟩ : syracuseStep 1725515 = 2588273) B2588273
theorem B1725527 : Blo 1148636 1725527 := bstep (se 1 (by rfl) ⟨1294145, by rfl⟩ : syracuseStep 1725527 = 2588291) B2588291
theorem B2053259 : Blo 1148636 2053259 := bstep (se 1 (by rfl) ⟨1539944, by rfl⟩ : syracuseStep 2053259 = 3079889) B3079889
theorem B1725593 : Blo 1148636 1725593 := bstep (se 2 (by rfl) ⟨647097, by rfl⟩ : syracuseStep 1725593 = 1294195) B1294195
theorem B1725707 : Blo 1148636 1725707 := bstep (se 1 (by rfl) ⟨1294280, by rfl⟩ : syracuseStep 1725707 = 2588561) B2588561
theorem B1725719 : Blo 1148636 1725719 := bstep (se 1 (by rfl) ⟨1294289, by rfl⟩ : syracuseStep 1725719 = 2588579) B2588579
theorem B1725785 : Blo 1148636 1725785 := bstep (se 2 (by rfl) ⟨647169, by rfl⟩ : syracuseStep 1725785 = 1294339) B1294339
theorem B2184563 : Blo 1148636 2184563 := bstep (se 1 (by rfl) ⟨1638422, by rfl⟩ : syracuseStep 2184563 = 3276845) B3276845
theorem B9328051 : Blo 1148636 9328051 := bstep (se 1 (by rfl) ⟨6996038, by rfl⟩ : syracuseStep 9328051 = 13992077) B13992077
theorem B1725899 : Blo 1148636 1725899 := bstep (se 1 (by rfl) ⟨1294424, by rfl⟩ : syracuseStep 1725899 = 2588849) B2588849
theorem B1725911 : Blo 1148636 1725911 := bstep (se 1 (by rfl) ⟨1294433, by rfl⟩ : syracuseStep 1725911 = 2588867) B2588867
theorem B14177753 : Blo 1148636 14177753 := bstep (se 2 (by rfl) ⟨5316657, by rfl⟩ : syracuseStep 14177753 = 10633315) B10633315
theorem B1725977 : Blo 1148636 1725977 := bstep (se 2 (by rfl) ⟨647241, by rfl⟩ : syracuseStep 1725977 = 1294483) B1294483
theorem B12605003 : Blo 1148636 12605003 := bstep (se 1 (by rfl) ⟨9453752, by rfl⟩ : syracuseStep 12605003 = 18907505) B18907505
theorem B1726091 : Blo 1148636 1726091 := bstep (se 1 (by rfl) ⟨1294568, by rfl⟩ : syracuseStep 1726091 = 2589137) B2589137
theorem B1726103 : Blo 1148636 1726103 := bstep (se 1 (by rfl) ⟨1294577, by rfl⟩ : syracuseStep 1726103 = 2589155) B2589155
theorem B1726169 : Blo 1148636 1726169 := bstep (se 2 (by rfl) ⟨647313, by rfl⟩ : syracuseStep 1726169 = 1294627) B1294627
theorem B4151063 : Blo 1148636 4151063 := bstep (se 1 (by rfl) ⟨3113297, by rfl⟩ : syracuseStep 4151063 = 6226595) B6226595
theorem B1726283 : Blo 1148636 1726283 := bstep (se 1 (by rfl) ⟨1294712, by rfl⟩ : syracuseStep 1726283 = 2589425) B2589425
theorem B3888971 : Blo 1148636 3888971 := bstep (se 1 (by rfl) ⟨2916728, by rfl⟩ : syracuseStep 3888971 = 5833457) B5833457
theorem B1726295 : Blo 1148636 1726295 := bstep (se 1 (by rfl) ⟨1294721, by rfl⟩ : syracuseStep 1726295 = 2589443) B2589443
theorem B2185049 : Blo 1148636 2185049 := bstep (se 2 (by rfl) ⟨819393, by rfl⟩ : syracuseStep 2185049 = 1638787) B1638787
theorem B1726361 : Blo 1148636 1726361 := bstep (se 2 (by rfl) ⟨647385, by rfl⟩ : syracuseStep 1726361 = 1294771) B1294771
theorem B8738765 : Blo 1148636 8738765 := bstep (se 3 (by rfl) ⟨1638518, by rfl⟩ : syracuseStep 8738765 = 3277037) B3277037
theorem B7362521 : Blo 1148636 7362521 := bstep (se 2 (by rfl) ⟨2760945, by rfl⟩ : syracuseStep 7362521 = 5521891) B5521891
theorem B1726475 : Blo 1148636 1726475 := bstep (se 1 (by rfl) ⟨1294856, by rfl⟩ : syracuseStep 1726475 = 2589713) B2589713
theorem B1726487 : Blo 1148636 1726487 := bstep (se 1 (by rfl) ⟨1294865, by rfl⟩ : syracuseStep 1726487 = 2589731) B2589731
theorem B1726553 : Blo 1148636 1726553 := bstep (se 2 (by rfl) ⟨647457, by rfl⟩ : syracuseStep 1726553 = 1294915) B1294915
theorem B3889241 : Blo 1148636 3889241 := bstep (se 2 (by rfl) ⟨1458465, by rfl⟩ : syracuseStep 3889241 = 2916931) B2916931
theorem B1726667 : Blo 1148636 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B1726679 : Blo 1148636 1726679 := bstep (se 1 (by rfl) ⟨1295009, by rfl⟩ : syracuseStep 1726679 = 2590019) B2590019
theorem B1726745 : Blo 1148636 1726745 := bstep (se 2 (by rfl) ⟨647529, by rfl⟩ : syracuseStep 1726745 = 1295059) B1295059
theorem B5822765 : Blo 1148636 5822765 := bstep (se 3 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 5822765 = 2183537) B2183537
theorem B1726859 : Blo 1148636 1726859 := bstep (se 1 (by rfl) ⟨1295144, by rfl⟩ : syracuseStep 1726859 = 2590289) B2590289
theorem B1726871 : Blo 1148636 1726871 := bstep (se 1 (by rfl) ⟨1295153, by rfl⟩ : syracuseStep 1726871 = 2590307) B2590307
theorem B8739251 : Blo 1148636 8739251 := bstep (se 1 (by rfl) ⟨6554438, by rfl⟩ : syracuseStep 8739251 = 13108877) B13108877
theorem B1726937 : Blo 1148636 1726937 := bstep (se 2 (by rfl) ⟨647601, by rfl⟩ : syracuseStep 1726937 = 1295203) B1295203
theorem B1727051 : Blo 1148636 1727051 := bstep (se 1 (by rfl) ⟨1295288, by rfl⟩ : syracuseStep 1727051 = 2590577) B2590577
theorem B1727063 : Blo 1148636 1727063 := bstep (se 1 (by rfl) ⟨1295297, by rfl⟩ : syracuseStep 1727063 = 2590595) B2590595
theorem B1727129 : Blo 1148636 1727129 := bstep (se 2 (by rfl) ⟨647673, by rfl⟩ : syracuseStep 1727129 = 1295347) B1295347
theorem B1727243 : Blo 1148636 1727243 := bstep (se 1 (by rfl) ⟨1295432, by rfl⟩ : syracuseStep 1727243 = 2590865) B2590865
theorem B1727255 : Blo 1148636 1727255 := bstep (se 1 (by rfl) ⟨1295441, by rfl⟩ : syracuseStep 1727255 = 2590883) B2590883
theorem B3889943 : Blo 1148636 3889943 := bstep (se 1 (by rfl) ⟨2917457, by rfl⟩ : syracuseStep 3889943 = 5834915) B5834915
theorem B1727321 : Blo 1148636 1727321 := bstep (se 2 (by rfl) ⟨647745, by rfl⟩ : syracuseStep 1727321 = 1295491) B1295491
theorem B1727435 : Blo 1148636 1727435 := bstep (se 1 (by rfl) ⟨1295576, by rfl⟩ : syracuseStep 1727435 = 2591153) B2591153
theorem B1727447 : Blo 1148636 1727447 := bstep (se 1 (by rfl) ⟨1295585, by rfl⟩ : syracuseStep 1727447 = 2591171) B2591171
theorem B1727513 : Blo 1148636 1727513 := bstep (se 2 (by rfl) ⟨647817, by rfl⟩ : syracuseStep 1727513 = 1295635) B1295635
theorem B1727627 : Blo 1148636 1727627 := bstep (se 1 (by rfl) ⟨1295720, by rfl⟩ : syracuseStep 1727627 = 2591441) B2591441
theorem B1727639 : Blo 1148636 1727639 := bstep (se 1 (by rfl) ⟨1295729, by rfl⟩ : syracuseStep 1727639 = 2591459) B2591459
theorem B1727705 : Blo 1148636 1727705 := bstep (se 2 (by rfl) ⟨647889, by rfl⟩ : syracuseStep 1727705 = 1295779) B1295779
theorem B2186507 : Blo 1148636 2186507 := bstep (se 1 (by rfl) ⟨1639880, by rfl⟩ : syracuseStep 2186507 = 3279761) B3279761
theorem B1727819 : Blo 1148636 1727819 := bstep (se 1 (by rfl) ⟨1295864, by rfl⟩ : syracuseStep 1727819 = 2591729) B2591729
theorem B1727831 : Blo 1148636 1727831 := bstep (se 1 (by rfl) ⟨1295873, by rfl⟩ : syracuseStep 1727831 = 2591747) B2591747
theorem B4152721 : Blo 1148636 4152721 := bstep (se 2 (by rfl) ⟨1557270, by rfl⟩ : syracuseStep 4152721 = 3114541) B3114541
theorem B1727897 : Blo 1148636 1727897 := bstep (se 2 (by rfl) ⟨647961, by rfl⟩ : syracuseStep 1727897 = 1295923) B1295923
theorem B4906433 : Blo 1148636 4906433 := bstep (se 2 (by rfl) ⟨1839912, by rfl⟩ : syracuseStep 4906433 = 3679825) B3679825
theorem B2186689 : Blo 1148636 2186689 := bstep (se 2 (by rfl) ⟨820008, by rfl⟩ : syracuseStep 2186689 = 1640017) B1640017
theorem B1728011 : Blo 1148636 1728011 := bstep (se 1 (by rfl) ⟨1296008, by rfl⟩ : syracuseStep 1728011 = 2592017) B2592017
theorem B1728023 : Blo 1148636 1728023 := bstep (se 1 (by rfl) ⟨1296017, by rfl⟩ : syracuseStep 1728023 = 2592035) B2592035
theorem B1728089 : Blo 1148636 1728089 := bstep (se 2 (by rfl) ⟨648033, by rfl⟩ : syracuseStep 1728089 = 1296067) B1296067
theorem B1728203 : Blo 1148636 1728203 := bstep (se 1 (by rfl) ⟨1296152, by rfl⟩ : syracuseStep 1728203 = 2592305) B2592305
theorem B1728215 : Blo 1148636 1728215 := bstep (se 1 (by rfl) ⟨1296161, by rfl⟩ : syracuseStep 1728215 = 2592323) B2592323
theorem B1728281 : Blo 1148636 1728281 := bstep (se 2 (by rfl) ⟨648105, by rfl⟩ : syracuseStep 1728281 = 1296211) B1296211
theorem B8740709 : Blo 1148636 8740709 := bstep (se 4 (by rfl) ⟨819441, by rfl⟩ : syracuseStep 8740709 = 1638883) B1638883
theorem B2187137 : Blo 1148636 2187137 := bstep (se 2 (by rfl) ⟨820176, by rfl⟩ : syracuseStep 2187137 = 1640353) B1640353
theorem B1728395 : Blo 1148636 1728395 := bstep (se 1 (by rfl) ⟨1296296, by rfl⟩ : syracuseStep 1728395 = 2592593) B2592593
theorem B1728407 : Blo 1148636 1728407 := bstep (se 1 (by rfl) ⟨1296305, by rfl⟩ : syracuseStep 1728407 = 2592611) B2592611
theorem B1728473 : Blo 1148636 1728473 := bstep (se 2 (by rfl) ⟨648177, by rfl⟩ : syracuseStep 1728473 = 1296355) B1296355
theorem B5529617 : Blo 1148636 5529617 := bstep (se 2 (by rfl) ⟨2073606, by rfl⟩ : syracuseStep 5529617 = 4147213) B4147213
theorem B2908183 : Blo 1148636 2908183 := bstep (se 1 (by rfl) ⟨2181137, by rfl⟩ : syracuseStep 2908183 = 4362275) B4362275
theorem B6217793 : Blo 1148636 6217793 := bstep (se 2 (by rfl) ⟨2331672, by rfl⟩ : syracuseStep 6217793 = 4663345) B4663345
theorem B1728587 : Blo 1148636 1728587 := bstep (se 1 (by rfl) ⟨1296440, by rfl⟩ : syracuseStep 1728587 = 2592881) B2592881
theorem B1728599 : Blo 1148636 1728599 := bstep (se 1 (by rfl) ⟨1296449, by rfl⟩ : syracuseStep 1728599 = 2592899) B2592899
theorem B1728665 : Blo 1148636 1728665 := bstep (se 2 (by rfl) ⟨648249, by rfl⟩ : syracuseStep 1728665 = 1296499) B1296499
theorem B2187479 : Blo 1148636 2187479 := bstep (se 1 (by rfl) ⟨1640609, by rfl⟩ : syracuseStep 2187479 = 3281219) B3281219
theorem B1728779 : Blo 1148636 1728779 := bstep (se 1 (by rfl) ⟨1296584, by rfl⟩ : syracuseStep 1728779 = 2593169) B2593169
theorem B1728791 : Blo 1148636 1728791 := bstep (se 1 (by rfl) ⟨1296593, by rfl⟩ : syracuseStep 1728791 = 2593187) B2593187
theorem B8741195 : Blo 1148636 8741195 := bstep (se 1 (by rfl) ⟨6555896, by rfl⟩ : syracuseStep 8741195 = 13111793) B13111793
theorem B1728857 : Blo 1148636 1728857 := bstep (se 2 (by rfl) ⟨648321, by rfl⟩ : syracuseStep 1728857 = 1296643) B1296643
theorem B2908619 : Blo 1148636 2908619 := bstep (se 1 (by rfl) ⟨2181464, by rfl⟩ : syracuseStep 2908619 = 4362929) B4362929
theorem B3105373 : Blo 1148636 3105373 := bstep (se 3 (by rfl) ⟨582257, by rfl⟩ : syracuseStep 3105373 = 1164515) B1164515
theorem B11067997 : Blo 1148636 11067997 := bstep (se 3 (by rfl) ⟨2075249, by rfl⟩ : syracuseStep 11067997 = 4150499) B4150499
theorem B2908993 : Blo 1148636 2908993 := bstep (se 2 (by rfl) ⟨1090872, by rfl⟩ : syracuseStep 2908993 = 2181745) B2181745
theorem B2188147 : Blo 1148636 2188147 := bstep (se 1 (by rfl) ⟨1641110, by rfl⟩ : syracuseStep 2188147 = 3282221) B3282221
theorem B49832981 : Blo 1148636 49832981 := bstep (se 6 (by rfl) ⟨1167960, by rfl⟩ : syracuseStep 49832981 = 2335921) B2335921
theorem B4908107 : Blo 1148636 4908107 := bstep (se 1 (by rfl) ⟨3681080, by rfl⟩ : syracuseStep 4908107 = 7362161) B7362161
theorem B7365725 : Blo 1148636 7365725 := bstep (se 3 (by rfl) ⟨1381073, by rfl⟩ : syracuseStep 7365725 = 2762147) B2762147
theorem B20997251 : Blo 1148636 20997251 := bstep (se 1 (by rfl) ⟨15747938, by rfl⟩ : syracuseStep 20997251 = 31495877) B31495877
theorem B7365953 : Blo 1148636 7365953 := bstep (se 2 (by rfl) ⟨2762232, by rfl⟩ : syracuseStep 7365953 = 5524465) B5524465
theorem B2909591 : Blo 1148636 2909591 := bstep (se 1 (by rfl) ⟨2182193, by rfl⟩ : syracuseStep 2909591 = 4364387) B4364387
theorem B3106583 : Blo 1148636 3106583 := bstep (se 1 (by rfl) ⟨2329937, by rfl⟩ : syracuseStep 3106583 = 4659875) B4659875
theorem B6547331 : Blo 1148636 6547331 := bstep (se 1 (by rfl) ⟨4910498, by rfl⟩ : syracuseStep 6547331 = 9820997) B9820997
theorem B1402903 : Blo 1148636 1402903 := bstep (se 1 (by rfl) ⟨1052177, by rfl⟩ : syracuseStep 1402903 = 2104355) B2104355
theorem B5826653 : Blo 1148636 5826653 := bstep (se 3 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 5826653 = 2184995) B2184995
theorem B2910401 : Blo 1148636 2910401 := bstep (se 2 (by rfl) ⟨1091400, by rfl⟩ : syracuseStep 2910401 = 2182801) B2182801
theorem B6547787 : Blo 1148636 6547787 := bstep (se 1 (by rfl) ⟨4910840, by rfl⟩ : syracuseStep 6547787 = 9821681) B9821681
theorem B4909405 : Blo 1148636 4909405 := bstep (se 3 (by rfl) ⟨920513, by rfl⟩ : syracuseStep 4909405 = 1841027) B1841027
theorem B4909747 : Blo 1148636 4909747 := bstep (se 1 (by rfl) ⟨3682310, by rfl⟩ : syracuseStep 4909747 = 7364621) B7364621
theorem B2910937 : Blo 1148636 2910937 := bstep (se 2 (by rfl) ⟨1091601, by rfl⟩ : syracuseStep 2910937 = 2183203) B2183203
theorem B204238037 : Blo 1148636 204238037 := bstep (se 7 (by rfl) ⟨2393414, by rfl⟩ : syracuseStep 204238037 = 4786829) B4786829
theorem B7368209 : Blo 1148636 7368209 := bstep (se 2 (by rfl) ⟨2763078, by rfl⟩ : syracuseStep 7368209 = 5526157) B5526157
theorem B3272413 : Blo 1148636 3272413 := bstep (se 3 (by rfl) ⟨613577, by rfl⟩ : syracuseStep 3272413 = 1227155) B1227155
theorem B3272471 : Blo 1148636 3272471 := bstep (se 1 (by rfl) ⟨2454353, by rfl⟩ : syracuseStep 3272471 = 4908707) B4908707
theorem B2912051 : Blo 1148636 2912051 := bstep (se 1 (by rfl) ⟨2184038, by rfl⟩ : syracuseStep 2912051 = 4368077) B4368077
theorem B2453465 : Blo 1148636 2453465 := bstep (se 2 (by rfl) ⟨920049, by rfl⟩ : syracuseStep 2453465 = 1840099) B1840099
theorem B2584601 : Blo 1148636 2584601 := bstep (se 2 (by rfl) ⟨969225, by rfl⟩ : syracuseStep 2584601 = 1938451) B1938451
theorem B2912345 : Blo 1148636 2912345 := bstep (se 2 (by rfl) ⟨1092129, by rfl⟩ : syracuseStep 2912345 = 2184259) B2184259
theorem B2584691 : Blo 1148636 2584691 := bstep (se 1 (by rfl) ⟨1938518, by rfl⟩ : syracuseStep 2584691 = 3877037) B3877037
theorem B2584727 : Blo 1148636 2584727 := bstep (se 1 (by rfl) ⟨1938545, by rfl⟩ : syracuseStep 2584727 = 3877091) B3877091
theorem B5828759 : Blo 1148636 5828759 := bstep (se 1 (by rfl) ⟨4371569, by rfl⟩ : syracuseStep 5828759 = 8743139) B8743139
theorem B24899885 : Blo 1148636 24899885 := bstep (se 3 (by rfl) ⟨4668728, by rfl⟩ : syracuseStep 24899885 = 9337457) B9337457
theorem B2584907 : Blo 1148636 2584907 := bstep (se 1 (by rfl) ⟨1938680, by rfl⟩ : syracuseStep 2584907 = 3877361) B3877361
theorem B2584961 : Blo 1148636 2584961 := bstep (se 2 (by rfl) ⟨969360, by rfl⟩ : syracuseStep 2584961 = 1938721) B1938721
theorem B11071961 : Blo 1148636 11071961 := bstep (se 2 (by rfl) ⟨4151985, by rfl⟩ : syracuseStep 11071961 = 8303971) B8303971
theorem B2585177 : Blo 1148636 2585177 := bstep (se 2 (by rfl) ⟨969441, by rfl⟩ : syracuseStep 2585177 = 1938883) B1938883
theorem B2585267 : Blo 1148636 2585267 := bstep (se 1 (by rfl) ⟨1938950, by rfl⟩ : syracuseStep 2585267 = 3877901) B3877901
theorem B2585303 : Blo 1148636 2585303 := bstep (se 1 (by rfl) ⟨1938977, by rfl⟩ : syracuseStep 2585303 = 3877955) B3877955
theorem B2454259 : Blo 1148636 2454259 := bstep (se 1 (by rfl) ⟨1840694, by rfl⟩ : syracuseStep 2454259 = 3681389) B3681389
theorem B2585483 : Blo 1148636 2585483 := bstep (se 1 (by rfl) ⟨1939112, by rfl⟩ : syracuseStep 2585483 = 3878225) B3878225
theorem B2585537 : Blo 1148636 2585537 := bstep (se 2 (by rfl) ⟨969576, by rfl⟩ : syracuseStep 2585537 = 1939153) B1939153
theorem B3273689 : Blo 1148636 3273689 := bstep (se 2 (by rfl) ⟨1227633, by rfl⟩ : syracuseStep 3273689 = 2455267) B2455267
theorem B3273803 : Blo 1148636 3273803 := bstep (se 1 (by rfl) ⟨2455352, by rfl⟩ : syracuseStep 3273803 = 4910705) B4910705
theorem B8287363 : Blo 1148636 8287363 := bstep (se 1 (by rfl) ⟨6215522, by rfl⟩ : syracuseStep 8287363 = 12431045) B12431045
theorem B2585753 : Blo 1148636 2585753 := bstep (se 2 (by rfl) ⟨969657, by rfl⟩ : syracuseStep 2585753 = 1939315) B1939315
theorem B2585843 : Blo 1148636 2585843 := bstep (se 1 (by rfl) ⟨1939382, by rfl⟩ : syracuseStep 2585843 = 3878765) B3878765
theorem B2585879 : Blo 1148636 2585879 := bstep (se 1 (by rfl) ⟨1939409, by rfl⟩ : syracuseStep 2585879 = 3878819) B3878819
theorem B1635671 : Blo 1148636 1635671 := bstep (se 1 (by rfl) ⟨1226753, by rfl⟩ : syracuseStep 1635671 = 2453507) B2453507
theorem B2586059 : Blo 1148636 2586059 := bstep (se 1 (by rfl) ⟨1939544, by rfl⟩ : syracuseStep 2586059 = 3879089) B3879089
theorem B2586113 : Blo 1148636 2586113 := bstep (se 2 (by rfl) ⟨969792, by rfl⟩ : syracuseStep 2586113 = 1939585) B1939585
theorem B8746541 : Blo 1148636 8746541 := bstep (se 3 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 8746541 = 3279953) B3279953
theorem B2455105 : Blo 1148636 2455105 := bstep (se 2 (by rfl) ⟨920664, by rfl⟩ : syracuseStep 2455105 = 1841329) B1841329
theorem B1635979 : Blo 1148636 1635979 := bstep (se 1 (by rfl) ⟨1226984, by rfl⟩ : syracuseStep 1635979 = 2453969) B2453969
theorem B2913995 : Blo 1148636 2913995 := bstep (se 1 (by rfl) ⟨2185496, by rfl⟩ : syracuseStep 2913995 = 4370993) B4370993
theorem B2586329 : Blo 1148636 2586329 := bstep (se 2 (by rfl) ⟨969873, by rfl⟩ : syracuseStep 2586329 = 1939747) B1939747
theorem B3503837 : Blo 1148636 3503837 := bstep (se 3 (by rfl) ⟨656969, by rfl⟩ : syracuseStep 3503837 = 1313939) B1313939
theorem B2586419 : Blo 1148636 2586419 := bstep (se 1 (by rfl) ⟨1939814, by rfl⟩ : syracuseStep 2586419 = 3879629) B3879629
theorem B2586455 : Blo 1148636 2586455 := bstep (se 1 (by rfl) ⟨1939841, by rfl⟩ : syracuseStep 2586455 = 3879683) B3879683
theorem B7862167 : Blo 1148636 7862167 := bstep (se 1 (by rfl) ⟨5896625, by rfl⟩ : syracuseStep 7862167 = 11793251) B11793251
theorem B2455447 : Blo 1148636 2455447 := bstep (se 1 (by rfl) ⟨1841585, by rfl⟩ : syracuseStep 2455447 = 3683171) B3683171
theorem B2586635 : Blo 1148636 2586635 := bstep (se 1 (by rfl) ⟨1939976, by rfl⟩ : syracuseStep 2586635 = 3879953) B3879953
theorem B3504151 : Blo 1148636 3504151 := bstep (se 1 (by rfl) ⟨2628113, by rfl⟩ : syracuseStep 3504151 = 5256227) B5256227
theorem B2586689 : Blo 1148636 2586689 := bstep (se 2 (by rfl) ⟨970008, by rfl⟩ : syracuseStep 2586689 = 1940017) B1940017
theorem B3274931 : Blo 1148636 3274931 := bstep (se 1 (by rfl) ⟨2456198, by rfl⟩ : syracuseStep 3274931 = 4912397) B4912397
theorem B4913369 : Blo 1148636 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B2586905 : Blo 1148636 2586905 := bstep (se 2 (by rfl) ⟨970089, by rfl⟩ : syracuseStep 2586905 = 1940179) B1940179
theorem B12450113 : Blo 1148636 12450113 := bstep (se 2 (by rfl) ⟨4668792, by rfl⟩ : syracuseStep 12450113 = 9337585) B9337585
theorem B2586995 : Blo 1148636 2586995 := bstep (se 1 (by rfl) ⟨1940246, by rfl⟩ : syracuseStep 2586995 = 3880493) B3880493
theorem B2587031 : Blo 1148636 2587031 := bstep (se 1 (by rfl) ⟨1940273, by rfl⟩ : syracuseStep 2587031 = 3880547) B3880547
theorem B3275329 : Blo 1148636 3275329 := bstep (se 2 (by rfl) ⟨1228248, by rfl⟩ : syracuseStep 3275329 = 2456497) B2456497
theorem B2587211 : Blo 1148636 2587211 := bstep (se 1 (by rfl) ⟨1940408, by rfl⟩ : syracuseStep 2587211 = 3880817) B3880817
theorem B2587265 : Blo 1148636 2587265 := bstep (se 2 (by rfl) ⟨970224, by rfl⟩ : syracuseStep 2587265 = 1940449) B1940449
theorem B1637015 : Blo 1148636 1637015 := bstep (se 1 (by rfl) ⟨1227761, by rfl⟩ : syracuseStep 1637015 = 2455523) B2455523
theorem B2914967 : Blo 1148636 2914967 := bstep (se 1 (by rfl) ⟨2186225, by rfl⟩ : syracuseStep 2914967 = 4372451) B4372451
theorem B1637209 : Blo 1148636 1637209 := bstep (se 2 (by rfl) ⟨613953, by rfl⟩ : syracuseStep 1637209 = 1227907) B1227907
theorem B2587481 : Blo 1148636 2587481 := bstep (se 2 (by rfl) ⟨970305, by rfl⟩ : syracuseStep 2587481 = 1940611) B1940611
theorem B6552413 : Blo 1148636 6552413 := bstep (se 3 (by rfl) ⟨1228577, by rfl⟩ : syracuseStep 6552413 = 2457155) B2457155
theorem B2587571 : Blo 1148636 2587571 := bstep (se 1 (by rfl) ⟨1940678, by rfl⟩ : syracuseStep 2587571 = 3881357) B3881357
theorem B2587607 : Blo 1148636 2587607 := bstep (se 1 (by rfl) ⟨1940705, by rfl⟩ : syracuseStep 2587607 = 3881411) B3881411
theorem B2456651 : Blo 1148636 2456651 := bstep (se 1 (by rfl) ⟨1842488, by rfl⟩ : syracuseStep 2456651 = 3684977) B3684977
theorem B2587787 : Blo 1148636 2587787 := bstep (se 1 (by rfl) ⟨1940840, by rfl⟩ : syracuseStep 2587787 = 3881681) B3881681
theorem B2587841 : Blo 1148636 2587841 := bstep (se 2 (by rfl) ⟨970440, by rfl⟩ : syracuseStep 2587841 = 1940881) B1940881
theorem B2915635 : Blo 1148636 2915635 := bstep (se 1 (by rfl) ⟨2186726, by rfl⟩ : syracuseStep 2915635 = 4373453) B4373453
theorem B2588057 : Blo 1148636 2588057 := bstep (se 2 (by rfl) ⟨970521, by rfl⟩ : syracuseStep 2588057 = 1941043) B1941043
theorem B2915777 : Blo 1148636 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B10485197 : Blo 1148636 10485197 := bstep (se 3 (by rfl) ⟨1965974, by rfl⟩ : syracuseStep 10485197 = 3931949) B3931949
theorem B2588147 : Blo 1148636 2588147 := bstep (se 1 (by rfl) ⟨1941110, by rfl⟩ : syracuseStep 2588147 = 3882221) B3882221
theorem B2588183 : Blo 1148636 2588183 := bstep (se 1 (by rfl) ⟨1941137, by rfl⟩ : syracuseStep 2588183 = 3882275) B3882275
theorem B2457163 : Blo 1148636 2457163 := bstep (se 1 (by rfl) ⟨1842872, by rfl⟩ : syracuseStep 2457163 = 3685745) B3685745
theorem B6553163 : Blo 1148636 6553163 := bstep (se 1 (by rfl) ⟨4914872, by rfl⟩ : syracuseStep 6553163 = 9829745) B9829745
theorem B5832323 : Blo 1148636 5832323 := bstep (se 1 (by rfl) ⟨4374242, by rfl⟩ : syracuseStep 5832323 = 8748485) B8748485
theorem B2621107 : Blo 1148636 2621107 := bstep (se 1 (by rfl) ⟨1965830, by rfl⟩ : syracuseStep 2621107 = 3931661) B3931661
theorem B2588363 : Blo 1148636 2588363 := bstep (se 1 (by rfl) ⟨1941272, by rfl⟩ : syracuseStep 2588363 = 3882545) B3882545
theorem B2588417 : Blo 1148636 2588417 := bstep (se 2 (by rfl) ⟨970656, by rfl⟩ : syracuseStep 2588417 = 1941313) B1941313
theorem B4915009 : Blo 1148636 4915009 := bstep (se 2 (by rfl) ⟨1843128, by rfl⟩ : syracuseStep 4915009 = 3686257) B3686257
theorem B7372619 : Blo 1148636 7372619 := bstep (se 1 (by rfl) ⟨5529464, by rfl⟩ : syracuseStep 7372619 = 11058929) B11058929
theorem B28016563 : Blo 1148636 28016563 := bstep (se 1 (by rfl) ⟨21012422, by rfl⟩ : syracuseStep 28016563 = 42024845) B42024845
theorem B2588633 : Blo 1148636 2588633 := bstep (se 2 (by rfl) ⟨970737, by rfl⟩ : syracuseStep 2588633 = 1941475) B1941475
theorem B4489177 : Blo 1148636 4489177 := bstep (se 2 (by rfl) ⟨1683441, by rfl⟩ : syracuseStep 4489177 = 3366883) B3366883
theorem B6225923 : Blo 1148636 6225923 := bstep (se 1 (by rfl) ⟨4669442, by rfl⟩ : syracuseStep 6225923 = 9338885) B9338885
theorem B2588687 : Blo 1148636 2588687 := bstep (se 1 (by rfl) ⟨1941515, by rfl⟩ : syracuseStep 2588687 = 3883031) B3883031
theorem B5898269 : Blo 1148636 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B2588705 : Blo 1148636 2588705 := bstep (se 2 (by rfl) ⟨970764, by rfl⟩ : syracuseStep 2588705 = 1941529) B1941529
theorem B2916395 : Blo 1148636 2916395 := bstep (se 1 (by rfl) ⟨2187296, by rfl⟩ : syracuseStep 2916395 = 4374593) B4374593
theorem B1638473 : Blo 1148636 1638473 := bstep (se 2 (by rfl) ⟨614427, by rfl⟩ : syracuseStep 1638473 = 1228855) B1228855
theorem B1638587 : Blo 1148636 1638587 := bstep (se 1 (by rfl) ⟨1228940, by rfl⟩ : syracuseStep 1638587 = 2457881) B2457881
theorem B11043053 : Blo 1148636 11043053 := bstep (se 3 (by rfl) ⟨2070572, by rfl⟩ : syracuseStep 11043053 = 4141145) B4141145
theorem B6553871 : Blo 1148636 6553871 := bstep (se 1 (by rfl) ⟨4915403, by rfl⟩ : syracuseStep 6553871 = 9830807) B9830807
theorem B2589047 : Blo 1148636 2589047 := bstep (se 1 (by rfl) ⟨1941785, by rfl⟩ : syracuseStep 2589047 = 3883571) B3883571
theorem B8749457 : Blo 1148636 8749457 := bstep (se 2 (by rfl) ⟨3281046, by rfl⟩ : syracuseStep 8749457 = 6562093) B6562093
theorem B3113417 : Blo 1148636 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B2490895 : Blo 1148636 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B2589227 : Blo 1148636 2589227 := bstep (se 1 (by rfl) ⟨1941920, by rfl⟩ : syracuseStep 2589227 = 3883841) B3883841
theorem B1639225 : Blo 1148636 1639225 := bstep (se 2 (by rfl) ⟨614709, by rfl⟩ : syracuseStep 1639225 = 1229419) B1229419
theorem B2917235 : Blo 1148636 2917235 := bstep (se 1 (by rfl) ⟨2187926, by rfl⟩ : syracuseStep 2917235 = 4375853) B4375853
theorem B2917255 : Blo 1148636 2917255 := bstep (se 1 (by rfl) ⟨2187941, by rfl⟩ : syracuseStep 2917255 = 4375883) B4375883
theorem B1180559 : Blo 1148636 1180559 := bstep (se 1 (by rfl) ⟨885419, by rfl⟩ : syracuseStep 1180559 = 1770839) B1770839
theorem B2589587 : Blo 1148636 2589587 := bstep (se 1 (by rfl) ⟨1942190, by rfl⟩ : syracuseStep 2589587 = 3884381) B3884381
theorem B5833619 : Blo 1148636 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B3277721 : Blo 1148636 3277721 := bstep (se 2 (by rfl) ⟨1229145, by rfl⟩ : syracuseStep 3277721 = 2458291) B2458291
theorem B2589641 : Blo 1148636 2589641 := bstep (se 2 (by rfl) ⟨971115, by rfl⟩ : syracuseStep 2589641 = 1942231) B1942231
theorem B15762437 : Blo 1148636 15762437 := bstep (se 4 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 15762437 = 2955457) B2955457
theorem B2458667 : Blo 1148636 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B2917529 : Blo 1148636 2917529 := bstep (se 2 (by rfl) ⟨1094073, by rfl⟩ : syracuseStep 2917529 = 2188147) B2188147
theorem B4916513 : Blo 1148636 4916513 := bstep (se 2 (by rfl) ⟨1843692, by rfl⟩ : syracuseStep 4916513 = 3687385) B3687385
theorem B2360723 : Blo 1148636 2360723 := bstep (se 1 (by rfl) ⟨1770542, by rfl⟩ : syracuseStep 2360723 = 3541085) B3541085
theorem B11077073 : Blo 1148636 11077073 := bstep (se 2 (by rfl) ⟨4153902, by rfl⟩ : syracuseStep 11077073 = 8307805) B8307805
theorem B6227479 : Blo 1148636 6227479 := bstep (se 1 (by rfl) ⟨4670609, by rfl⟩ : syracuseStep 6227479 = 9341219) B9341219
theorem B11044471 : Blo 1148636 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B4916855 : Blo 1148636 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B2590343 : Blo 1148636 2590343 := bstep (se 1 (by rfl) ⟨1942757, by rfl⟩ : syracuseStep 2590343 = 3885515) B3885515
theorem B6555329 : Blo 1148636 6555329 := bstep (se 2 (by rfl) ⟨2458248, by rfl⟩ : syracuseStep 6555329 = 4916497) B4916497
theorem B1148679 : Blo 1148636 1148679 := bstep (se 1 (by rfl) ⟨861509, by rfl⟩ : syracuseStep 1148679 = 1723019) B1723019
theorem B1148687 : Blo 1148636 1148687 := bstep (se 1 (by rfl) ⟨861515, by rfl⟩ : syracuseStep 1148687 = 1723031) B1723031
theorem B2524943 : Blo 1148636 2524943 := bstep (se 1 (by rfl) ⟨1893707, by rfl⟩ : syracuseStep 2524943 = 3787415) B3787415
theorem B1148731 : Blo 1148636 1148731 := bstep (se 1 (by rfl) ⟨861548, by rfl⟩ : syracuseStep 1148731 = 1723097) B1723097
theorem B2590523 : Blo 1148636 2590523 := bstep (se 1 (by rfl) ⟨1942892, by rfl⟩ : syracuseStep 2590523 = 3885785) B3885785
theorem B1148807 : Blo 1148636 1148807 := bstep (se 1 (by rfl) ⟨861605, by rfl⟩ : syracuseStep 1148807 = 1723211) B1723211
theorem B1148815 : Blo 1148636 1148815 := bstep (se 1 (by rfl) ⟨861611, by rfl⟩ : syracuseStep 1148815 = 1723223) B1723223
theorem B2590649 : Blo 1148636 2590649 := bstep (se 2 (by rfl) ⟨971493, by rfl⟩ : syracuseStep 2590649 = 1942987) B1942987
theorem B1148859 : Blo 1148636 1148859 := bstep (se 1 (by rfl) ⟨861644, by rfl⟩ : syracuseStep 1148859 = 1723289) B1723289
theorem B1148935 : Blo 1148636 1148935 := bstep (se 1 (by rfl) ⟨861701, by rfl⟩ : syracuseStep 1148935 = 1723403) B1723403
theorem B1148943 : Blo 1148636 1148943 := bstep (se 1 (by rfl) ⟨861707, by rfl⟩ : syracuseStep 1148943 = 1723415) B1723415
theorem B1148987 : Blo 1148636 1148987 := bstep (se 1 (by rfl) ⟨861740, by rfl⟩ : syracuseStep 1148987 = 1723481) B1723481
theorem B1149063 : Blo 1148636 1149063 := bstep (se 1 (by rfl) ⟨861797, by rfl⟩ : syracuseStep 1149063 = 1723595) B1723595
theorem B1149071 : Blo 1148636 1149071 := bstep (se 1 (by rfl) ⟨861803, by rfl⟩ : syracuseStep 1149071 = 1723607) B1723607
theorem B1149115 : Blo 1148636 1149115 := bstep (se 1 (by rfl) ⟨861836, by rfl⟩ : syracuseStep 1149115 = 1723673) B1723673
theorem B1149191 : Blo 1148636 1149191 := bstep (se 1 (by rfl) ⟨861893, by rfl⟩ : syracuseStep 1149191 = 1723787) B1723787
theorem B1149199 : Blo 1148636 1149199 := bstep (se 1 (by rfl) ⟨861899, by rfl⟩ : syracuseStep 1149199 = 1723799) B1723799
theorem B2590991 : Blo 1148636 2590991 := bstep (se 1 (by rfl) ⟨1943243, by rfl⟩ : syracuseStep 2590991 = 3886487) B3886487
theorem B3279133 : Blo 1148636 3279133 := bstep (se 3 (by rfl) ⟨614837, by rfl⟩ : syracuseStep 3279133 = 1229675) B1229675
theorem B2591009 : Blo 1148636 2591009 := bstep (se 2 (by rfl) ⟨971628, by rfl⟩ : syracuseStep 2591009 = 1943257) B1943257
theorem B1149243 : Blo 1148636 1149243 := bstep (se 1 (by rfl) ⟨861932, by rfl⟩ : syracuseStep 1149243 = 1723865) B1723865
theorem B1149319 : Blo 1148636 1149319 := bstep (se 1 (by rfl) ⟨861989, by rfl⟩ : syracuseStep 1149319 = 1723979) B1723979
theorem B1149327 : Blo 1148636 1149327 := bstep (se 1 (by rfl) ⟨861995, by rfl⟩ : syracuseStep 1149327 = 1723991) B1723991
theorem B1149371 : Blo 1148636 1149371 := bstep (se 1 (by rfl) ⟨862028, by rfl⟩ : syracuseStep 1149371 = 1724057) B1724057
theorem B3279305 : Blo 1148636 3279305 := bstep (se 2 (by rfl) ⟨1229739, by rfl⟩ : syracuseStep 3279305 = 2459479) B2459479
theorem B3279361 : Blo 1148636 3279361 := bstep (se 2 (by rfl) ⟨1229760, by rfl⟩ : syracuseStep 3279361 = 2459521) B2459521
theorem B1149447 : Blo 1148636 1149447 := bstep (se 1 (by rfl) ⟨862085, by rfl⟩ : syracuseStep 1149447 = 1724171) B1724171
theorem B1149455 : Blo 1148636 1149455 := bstep (se 1 (by rfl) ⟨862091, by rfl⟩ : syracuseStep 1149455 = 1724183) B1724183
theorem B1149499 : Blo 1148636 1149499 := bstep (se 1 (by rfl) ⟨862124, by rfl⟩ : syracuseStep 1149499 = 1724249) B1724249
theorem B3115579 : Blo 1148636 3115579 := bstep (se 1 (by rfl) ⟨2336684, by rfl⟩ : syracuseStep 3115579 = 4673369) B4673369
theorem B2591351 : Blo 1148636 2591351 := bstep (se 1 (by rfl) ⟨1943513, by rfl⟩ : syracuseStep 2591351 = 3887027) B3887027
theorem B1149575 : Blo 1148636 1149575 := bstep (se 1 (by rfl) ⟨862181, by rfl⟩ : syracuseStep 1149575 = 1724363) B1724363
theorem B1149583 : Blo 1148636 1149583 := bstep (se 1 (by rfl) ⟨862187, by rfl⟩ : syracuseStep 1149583 = 1724375) B1724375
theorem B2460307 : Blo 1148636 2460307 := bstep (se 1 (by rfl) ⟨1845230, by rfl⟩ : syracuseStep 2460307 = 3690461) B3690461
theorem B1149627 : Blo 1148636 1149627 := bstep (se 1 (by rfl) ⟨862220, by rfl⟩ : syracuseStep 1149627 = 1724441) B1724441
theorem B6228737 : Blo 1148636 6228737 := bstep (se 2 (by rfl) ⟨2335776, by rfl⟩ : syracuseStep 6228737 = 4671553) B4671553
theorem B49711877 : Blo 1148636 49711877 := bstep (se 4 (by rfl) ⟨4660488, by rfl⟩ : syracuseStep 49711877 = 9320977) B9320977
theorem B1149703 : Blo 1148636 1149703 := bstep (se 1 (by rfl) ⟨862277, by rfl⟩ : syracuseStep 1149703 = 1724555) B1724555
theorem B1149711 : Blo 1148636 1149711 := bstep (se 1 (by rfl) ⟨862283, by rfl⟩ : syracuseStep 1149711 = 1724567) B1724567
theorem B459967247 : Blo 1148636 459967247 := bstep (se 1 (by rfl) ⟨344975435, by rfl⟩ : syracuseStep 459967247 = 689950871) B689950871
theorem B8751887 : Blo 1148636 8751887 := bstep (se 1 (by rfl) ⟨6563915, by rfl⟩ : syracuseStep 8751887 = 13127831) B13127831
theorem B2591531 : Blo 1148636 2591531 := bstep (se 1 (by rfl) ⟨1943648, by rfl⟩ : syracuseStep 2591531 = 3887297) B3887297
theorem B1149755 : Blo 1148636 1149755 := bstep (se 1 (by rfl) ⟨862316, by rfl⟩ : syracuseStep 1149755 = 1724633) B1724633
theorem B3279703 : Blo 1148636 3279703 := bstep (se 1 (by rfl) ⟨2459777, by rfl⟩ : syracuseStep 3279703 = 4919555) B4919555
theorem B1149831 : Blo 1148636 1149831 := bstep (se 1 (by rfl) ⟨862373, by rfl⟩ : syracuseStep 1149831 = 1724747) B1724747
theorem B1149839 : Blo 1148636 1149839 := bstep (se 1 (by rfl) ⟨862379, by rfl⟩ : syracuseStep 1149839 = 1724759) B1724759
theorem B1149883 : Blo 1148636 1149883 := bstep (se 1 (by rfl) ⟨862412, by rfl⟩ : syracuseStep 1149883 = 1724825) B1724825
theorem B1149959 : Blo 1148636 1149959 := bstep (se 1 (by rfl) ⟨862469, by rfl⟩ : syracuseStep 1149959 = 1724939) B1724939
theorem B1149967 : Blo 1148636 1149967 := bstep (se 1 (by rfl) ⟨862475, by rfl⟩ : syracuseStep 1149967 = 1724951) B1724951
theorem B1150011 : Blo 1148636 1150011 := bstep (se 1 (by rfl) ⟨862508, by rfl⟩ : syracuseStep 1150011 = 1725017) B1725017
theorem B4361303 : Blo 1148636 4361303 := bstep (se 1 (by rfl) ⟨3270977, by rfl⟩ : syracuseStep 4361303 = 6541955) B6541955
theorem B1150087 : Blo 1148636 1150087 := bstep (se 1 (by rfl) ⟨862565, by rfl⟩ : syracuseStep 1150087 = 1725131) B1725131
theorem B1150095 : Blo 1148636 1150095 := bstep (se 1 (by rfl) ⟨862571, by rfl⟩ : syracuseStep 1150095 = 1725143) B1725143
theorem B2591891 : Blo 1148636 2591891 := bstep (se 1 (by rfl) ⟨1943918, by rfl⟩ : syracuseStep 2591891 = 3887837) B3887837
theorem B1150139 : Blo 1148636 1150139 := bstep (se 1 (by rfl) ⟨862604, by rfl⟩ : syracuseStep 1150139 = 1725209) B1725209
theorem B2591945 : Blo 1148636 2591945 := bstep (se 2 (by rfl) ⟨971979, by rfl⟩ : syracuseStep 2591945 = 1943959) B1943959
theorem B1150215 : Blo 1148636 1150215 := bstep (se 1 (by rfl) ⟨862661, by rfl⟩ : syracuseStep 1150215 = 1725323) B1725323
theorem B1150223 : Blo 1148636 1150223 := bstep (se 1 (by rfl) ⟨862667, by rfl⟩ : syracuseStep 1150223 = 1725335) B1725335
theorem B1150267 : Blo 1148636 1150267 := bstep (se 1 (by rfl) ⟨862700, by rfl⟩ : syracuseStep 1150267 = 1725401) B1725401
theorem B1150343 : Blo 1148636 1150343 := bstep (se 1 (by rfl) ⟨862757, by rfl⟩ : syracuseStep 1150343 = 1725515) B1725515
theorem B1150351 : Blo 1148636 1150351 := bstep (se 1 (by rfl) ⟨862763, by rfl⟩ : syracuseStep 1150351 = 1725527) B1725527
theorem B1150395 : Blo 1148636 1150395 := bstep (se 1 (by rfl) ⟨862796, by rfl⟩ : syracuseStep 1150395 = 1725593) B1725593
theorem B1150471 : Blo 1148636 1150471 := bstep (se 1 (by rfl) ⟨862853, by rfl⟩ : syracuseStep 1150471 = 1725707) B1725707
theorem B1150479 : Blo 1148636 1150479 := bstep (se 1 (by rfl) ⟨862859, by rfl⟩ : syracuseStep 1150479 = 1725719) B1725719
theorem B1150523 : Blo 1148636 1150523 := bstep (se 1 (by rfl) ⟨862892, by rfl⟩ : syracuseStep 1150523 = 1725785) B1725785
theorem B4361789 : Blo 1148636 4361789 := bstep (se 3 (by rfl) ⟨817835, by rfl⟩ : syracuseStep 4361789 = 1635671) B1635671
theorem B1150599 : Blo 1148636 1150599 := bstep (se 1 (by rfl) ⟨862949, by rfl⟩ : syracuseStep 1150599 = 1725899) B1725899
theorem B1150607 : Blo 1148636 1150607 := bstep (se 1 (by rfl) ⟨862955, by rfl⟩ : syracuseStep 1150607 = 1725911) B1725911
theorem B1150651 : Blo 1148636 1150651 := bstep (se 1 (by rfl) ⟨862988, by rfl⟩ : syracuseStep 1150651 = 1725977) B1725977
theorem B1150727 : Blo 1148636 1150727 := bstep (se 1 (by rfl) ⟨863045, by rfl⟩ : syracuseStep 1150727 = 1726091) B1726091
theorem B1150735 : Blo 1148636 1150735 := bstep (se 1 (by rfl) ⟨863051, by rfl⟩ : syracuseStep 1150735 = 1726103) B1726103
theorem B2494223 : Blo 1148636 2494223 := bstep (se 1 (by rfl) ⟨1870667, by rfl⟩ : syracuseStep 2494223 = 3741335) B3741335
theorem B1150779 : Blo 1148636 1150779 := bstep (se 1 (by rfl) ⟨863084, by rfl⟩ : syracuseStep 1150779 = 1726169) B1726169
theorem B1150855 : Blo 1148636 1150855 := bstep (se 1 (by rfl) ⟨863141, by rfl⟩ : syracuseStep 1150855 = 1726283) B1726283
theorem B2592647 : Blo 1148636 2592647 := bstep (se 1 (by rfl) ⟨1944485, by rfl⟩ : syracuseStep 2592647 = 3888971) B3888971
theorem B1150863 : Blo 1148636 1150863 := bstep (se 1 (by rfl) ⟨863147, by rfl⟩ : syracuseStep 1150863 = 1726295) B1726295
theorem B1150907 : Blo 1148636 1150907 := bstep (se 1 (by rfl) ⟨863180, by rfl⟩ : syracuseStep 1150907 = 1726361) B1726361
theorem B1150983 : Blo 1148636 1150983 := bstep (se 1 (by rfl) ⟨863237, by rfl⟩ : syracuseStep 1150983 = 1726475) B1726475
theorem B1150991 : Blo 1148636 1150991 := bstep (se 1 (by rfl) ⟨863243, by rfl⟩ : syracuseStep 1150991 = 1726487) B1726487
theorem B6557719 : Blo 1148636 6557719 := bstep (se 1 (by rfl) ⟨4918289, by rfl⟩ : syracuseStep 6557719 = 9836579) B9836579
theorem B1151035 : Blo 1148636 1151035 := bstep (se 1 (by rfl) ⟨863276, by rfl⟩ : syracuseStep 1151035 = 1726553) B1726553
theorem B2592827 : Blo 1148636 2592827 := bstep (se 1 (by rfl) ⟨1944620, by rfl⟩ : syracuseStep 2592827 = 3889241) B3889241
theorem B4919383 : Blo 1148636 4919383 := bstep (se 1 (by rfl) ⟨3689537, by rfl⟩ : syracuseStep 4919383 = 7379075) B7379075
theorem B8851589 : Blo 1148636 8851589 := bstep (se 4 (by rfl) ⟨829836, by rfl⟩ : syracuseStep 8851589 = 1659673) B1659673
theorem B1151111 : Blo 1148636 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B1151119 : Blo 1148636 1151119 := bstep (se 1 (by rfl) ⟨863339, by rfl⟩ : syracuseStep 1151119 = 1726679) B1726679
theorem B2592953 : Blo 1148636 2592953 := bstep (se 2 (by rfl) ⟨972357, by rfl⟩ : syracuseStep 2592953 = 1944715) B1944715
theorem B1151163 : Blo 1148636 1151163 := bstep (se 1 (by rfl) ⟨863372, by rfl⟩ : syracuseStep 1151163 = 1726745) B1726745
theorem B1151239 : Blo 1148636 1151239 := bstep (se 1 (by rfl) ⟨863429, by rfl⟩ : syracuseStep 1151239 = 1726859) B1726859
theorem B1151247 : Blo 1148636 1151247 := bstep (se 1 (by rfl) ⟨863435, by rfl⟩ : syracuseStep 1151247 = 1726871) B1726871
theorem B1151291 : Blo 1148636 1151291 := bstep (se 1 (by rfl) ⟨863468, by rfl⟩ : syracuseStep 1151291 = 1726937) B1726937
theorem B1151367 : Blo 1148636 1151367 := bstep (se 1 (by rfl) ⟨863525, by rfl⟩ : syracuseStep 1151367 = 1727051) B1727051
theorem B1151375 : Blo 1148636 1151375 := bstep (se 1 (by rfl) ⟨863531, by rfl⟩ : syracuseStep 1151375 = 1727063) B1727063
theorem B1151419 : Blo 1148636 1151419 := bstep (se 1 (by rfl) ⟨863564, by rfl⟩ : syracuseStep 1151419 = 1727129) B1727129
theorem B1151495 : Blo 1148636 1151495 := bstep (se 1 (by rfl) ⟨863621, by rfl⟩ : syracuseStep 1151495 = 1727243) B1727243
theorem B1151503 : Blo 1148636 1151503 := bstep (se 1 (by rfl) ⟨863627, by rfl⟩ : syracuseStep 1151503 = 1727255) B1727255
theorem B2593295 : Blo 1148636 2593295 := bstep (se 1 (by rfl) ⟨1944971, by rfl⟩ : syracuseStep 2593295 = 3889943) B3889943
theorem B2593313 : Blo 1148636 2593313 := bstep (se 2 (by rfl) ⟨972492, by rfl⟩ : syracuseStep 2593313 = 1944985) B1944985
theorem B1151547 : Blo 1148636 1151547 := bstep (se 1 (by rfl) ⟨863660, by rfl⟩ : syracuseStep 1151547 = 1727321) B1727321
theorem B1151623 : Blo 1148636 1151623 := bstep (se 1 (by rfl) ⟨863717, by rfl⟩ : syracuseStep 1151623 = 1727435) B1727435
theorem B1151631 : Blo 1148636 1151631 := bstep (se 1 (by rfl) ⟨863723, by rfl⟩ : syracuseStep 1151631 = 1727447) B1727447
theorem B1151675 : Blo 1148636 1151675 := bstep (se 1 (by rfl) ⟨863756, by rfl⟩ : syracuseStep 1151675 = 1727513) B1727513
theorem B1151751 : Blo 1148636 1151751 := bstep (se 1 (by rfl) ⟨863813, by rfl⟩ : syracuseStep 1151751 = 1727627) B1727627
theorem B1151759 : Blo 1148636 1151759 := bstep (se 1 (by rfl) ⟨863819, by rfl⟩ : syracuseStep 1151759 = 1727639) B1727639
theorem B1151803 : Blo 1148636 1151803 := bstep (se 1 (by rfl) ⟨863852, by rfl⟩ : syracuseStep 1151803 = 1727705) B1727705
theorem B1151879 : Blo 1148636 1151879 := bstep (se 1 (by rfl) ⟨863909, by rfl⟩ : syracuseStep 1151879 = 1727819) B1727819
theorem B1151887 : Blo 1148636 1151887 := bstep (se 1 (by rfl) ⟨863915, by rfl⟩ : syracuseStep 1151887 = 1727831) B1727831
theorem B21566371 : Blo 1148636 21566371 := bstep (se 1 (by rfl) ⟨16174778, by rfl⟩ : syracuseStep 21566371 = 32349557) B32349557
theorem B1151931 : Blo 1148636 1151931 := bstep (se 1 (by rfl) ⟨863948, by rfl⟩ : syracuseStep 1151931 = 1727897) B1727897
theorem B1938377 : Blo 1148636 1938377 := bstep (se 2 (by rfl) ⟨726891, by rfl⟩ : syracuseStep 1938377 = 1453783) B1453783
theorem B4363217 : Blo 1148636 4363217 := bstep (se 2 (by rfl) ⟨1636206, by rfl⟩ : syracuseStep 4363217 = 3272413) B3272413
theorem B1152007 : Blo 1148636 1152007 := bstep (se 1 (by rfl) ⟨864005, by rfl⟩ : syracuseStep 1152007 = 1728011) B1728011
theorem B1152015 : Blo 1148636 1152015 := bstep (se 1 (by rfl) ⟨864011, by rfl⟩ : syracuseStep 1152015 = 1728023) B1728023
theorem B1152059 : Blo 1148636 1152059 := bstep (se 1 (by rfl) ⟨864044, by rfl⟩ : syracuseStep 1152059 = 1728089) B1728089
theorem B1971319 : Blo 1148636 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B1152135 : Blo 1148636 1152135 := bstep (se 1 (by rfl) ⟨864101, by rfl⟩ : syracuseStep 1152135 = 1728203) B1728203
theorem B1152143 : Blo 1148636 1152143 := bstep (se 1 (by rfl) ⟨864107, by rfl⟩ : syracuseStep 1152143 = 1728215) B1728215
theorem B1152187 : Blo 1148636 1152187 := bstep (se 1 (by rfl) ⟨864140, by rfl⟩ : syracuseStep 1152187 = 1728281) B1728281
theorem B1152263 : Blo 1148636 1152263 := bstep (se 1 (by rfl) ⟨864197, by rfl⟩ : syracuseStep 1152263 = 1728395) B1728395
theorem B1152271 : Blo 1148636 1152271 := bstep (se 1 (by rfl) ⟨864203, by rfl⟩ : syracuseStep 1152271 = 1728407) B1728407
theorem B1152315 : Blo 1148636 1152315 := bstep (se 1 (by rfl) ⟨864236, by rfl⟩ : syracuseStep 1152315 = 1728473) B1728473
theorem B1152391 : Blo 1148636 1152391 := bstep (se 1 (by rfl) ⟨864293, by rfl⟩ : syracuseStep 1152391 = 1728587) B1728587
theorem B1152399 : Blo 1148636 1152399 := bstep (se 1 (by rfl) ⟨864299, by rfl⟩ : syracuseStep 1152399 = 1728599) B1728599
theorem B1152443 : Blo 1148636 1152443 := bstep (se 1 (by rfl) ⟨864332, by rfl⟩ : syracuseStep 1152443 = 1728665) B1728665
theorem B1152519 : Blo 1148636 1152519 := bstep (se 1 (by rfl) ⟨864389, by rfl⟩ : syracuseStep 1152519 = 1728779) B1728779
theorem B1152527 : Blo 1148636 1152527 := bstep (se 1 (by rfl) ⟨864395, by rfl⟩ : syracuseStep 1152527 = 1728791) B1728791
theorem B1152571 : Blo 1148636 1152571 := bstep (se 1 (by rfl) ⟨864428, by rfl⟩ : syracuseStep 1152571 = 1728857) B1728857
theorem B5609021 : Blo 1148636 5609021 := bstep (se 3 (by rfl) ⟨1051691, by rfl⟩ : syracuseStep 5609021 = 2103383) B2103383
theorem B1939079 : Blo 1148636 1939079 := bstep (se 1 (by rfl) ⟨1454309, by rfl⟩ : syracuseStep 1939079 = 2908619) B2908619
theorem B1382059 : Blo 1148636 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B13113251 : Blo 1148636 13113251 := bstep (se 1 (by rfl) ⟨9834938, by rfl⟩ : syracuseStep 13113251 = 19669877) B19669877
theorem B13998167 : Blo 1148636 13998167 := bstep (se 1 (by rfl) ⟨10498625, by rfl⟩ : syracuseStep 13998167 = 20997251) B20997251
theorem B1939727 : Blo 1148636 1939727 := bstep (se 1 (by rfl) ⟨1454795, by rfl⟩ : syracuseStep 1939727 = 2909591) B2909591
theorem B6560135 : Blo 1148636 6560135 := bstep (se 1 (by rfl) ⟨4920101, by rfl⟩ : syracuseStep 6560135 = 9840203) B9840203
theorem B2071055 : Blo 1148636 2071055 := bstep (se 1 (by rfl) ⟨1553291, by rfl⟩ : syracuseStep 2071055 = 3106583) B3106583
theorem B1841707 : Blo 1148636 1841707 := bstep (se 1 (by rfl) ⟨1381280, by rfl⟩ : syracuseStep 1841707 = 2762561) B2762561
theorem B4364887 : Blo 1148636 4364887 := bstep (se 1 (by rfl) ⟨3273665, by rfl⟩ : syracuseStep 4364887 = 6547331) B6547331
theorem B1940267 : Blo 1148636 1940267 := bstep (se 1 (by rfl) ⟨1455200, by rfl⟩ : syracuseStep 1940267 = 2910401) B2910401
theorem B11049817 : Blo 1148636 11049817 := bstep (se 2 (by rfl) ⟨4143681, by rfl⟩ : syracuseStep 11049817 = 8287363) B8287363
theorem B4365191 : Blo 1148636 4365191 := bstep (se 1 (by rfl) ⟨3273893, by rfl⟩ : syracuseStep 4365191 = 6547787) B6547787
theorem B2104265 : Blo 1148636 2104265 := bstep (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) B1578199
theorem B4365373 : Blo 1148636 4365373 := bstep (se 3 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 4365373 = 1637015) B1637015
theorem B1940665 : Blo 1148636 1940665 := bstep (se 2 (by rfl) ⟨727749, by rfl⟩ : syracuseStep 1940665 = 1455499) B1455499
theorem B2071993 : Blo 1148636 2071993 := bstep (se 2 (by rfl) ⟨776997, by rfl⟩ : syracuseStep 2071993 = 1553995) B1553995
theorem B136158691 : Blo 1148636 136158691 := bstep (se 1 (by rfl) ⟨102119018, by rfl⟩ : syracuseStep 136158691 = 204238037) B204238037
theorem B2760311 : Blo 1148636 2760311 := bstep (se 1 (by rfl) ⟨2070233, by rfl⟩ : syracuseStep 2760311 = 4140467) B4140467
theorem B1941367 : Blo 1148636 1941367 := bstep (se 1 (by rfl) ⟨1456025, by rfl⟩ : syracuseStep 1941367 = 2912051) B2912051
theorem B1384327 : Blo 1148636 1384327 := bstep (se 1 (by rfl) ⟨1038245, by rfl⟩ : syracuseStep 1384327 = 2076491) B2076491
theorem B1941563 : Blo 1148636 1941563 := bstep (se 1 (by rfl) ⟨1456172, by rfl⟩ : syracuseStep 1941563 = 2912345) B2912345
theorem B6561911 : Blo 1148636 6561911 := bstep (se 1 (by rfl) ⟨4921433, by rfl⟩ : syracuseStep 6561911 = 9842867) B9842867
theorem B7381307 : Blo 1148636 7381307 := bstep (se 1 (by rfl) ⟨5535980, by rfl⟩ : syracuseStep 7381307 = 11071961) B11071961
theorem B1941961 : Blo 1148636 1941961 := bstep (se 2 (by rfl) ⟨728235, by rfl⟩ : syracuseStep 1941961 = 1456471) B1456471
theorem B12460493 : Blo 1148636 12460493 := bstep (se 3 (by rfl) ⟨2336342, by rfl⟩ : syracuseStep 12460493 = 4672685) B4672685
theorem B4367105 : Blo 1148636 4367105 := bstep (se 2 (by rfl) ⟨1637664, by rfl⟩ : syracuseStep 4367105 = 3275329) B3275329
theorem B2073377 : Blo 1148636 2073377 := bstep (se 2 (by rfl) ⟨777516, by rfl⟩ : syracuseStep 2073377 = 1555033) B1555033
theorem B6562619 : Blo 1148636 6562619 := bstep (se 1 (by rfl) ⟨4921964, by rfl⟩ : syracuseStep 6562619 = 9843929) B9843929
theorem B3941405 : Blo 1148636 3941405 := bstep (se 3 (by rfl) ⟨739013, by rfl⟩ : syracuseStep 3941405 = 1478027) B1478027
theorem B1942663 : Blo 1148636 1942663 := bstep (se 1 (by rfl) ⟨1456997, by rfl⟩ : syracuseStep 1942663 = 2913995) B2913995
theorem B2335891 : Blo 1148636 2335891 := bstep (se 1 (by rfl) ⟨1751918, by rfl⟩ : syracuseStep 2335891 = 3503837) B3503837
theorem B8300075 : Blo 1148636 8300075 := bstep (se 1 (by rfl) ⟨6225056, by rfl⟩ : syracuseStep 8300075 = 12450113) B12450113
theorem B1844795 : Blo 1148636 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B4663021 : Blo 1148636 4663021 := bstep (se 3 (by rfl) ⟨874316, by rfl⟩ : syracuseStep 4663021 = 1748633) B1748633
theorem B1943311 : Blo 1148636 1943311 := bstep (se 1 (by rfl) ⟨1457483, by rfl⟩ : syracuseStep 1943311 = 2914967) B2914967
theorem B4368275 : Blo 1148636 4368275 := bstep (se 1 (by rfl) ⟨3276206, by rfl⟩ : syracuseStep 4368275 = 6552413) B6552413
theorem B3876875 : Blo 1148636 3876875 := bstep (se 1 (by rfl) ⟨2907656, by rfl⟩ : syracuseStep 3876875 = 5815313) B5815313
theorem B8726615 : Blo 1148636 8726615 := bstep (se 1 (by rfl) ⟨6544961, by rfl⟩ : syracuseStep 8726615 = 13089923) B13089923
theorem B3876983 : Blo 1148636 3876983 := bstep (se 1 (by rfl) ⟨2907737, by rfl⟩ : syracuseStep 3876983 = 5815475) B5815475
theorem B6564077 : Blo 1148636 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B1943851 : Blo 1148636 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B6990131 : Blo 1148636 6990131 := bstep (se 1 (by rfl) ⟨5242598, by rfl⟩ : syracuseStep 6990131 = 10485197) B10485197
theorem B4368775 : Blo 1148636 4368775 := bstep (se 1 (by rfl) ⟨3276581, by rfl⟩ : syracuseStep 4368775 = 6553163) B6553163
theorem B1943993 : Blo 1148636 1943993 := bstep (se 2 (by rfl) ⟨728997, by rfl⟩ : syracuseStep 1943993 = 1457995) B1457995
theorem B3877577 : Blo 1148636 3877577 := bstep (se 2 (by rfl) ⟨1454091, by rfl⟩ : syracuseStep 3877577 = 2908183) B2908183
theorem B7482149 : Blo 1148636 7482149 := bstep (se 4 (by rfl) ⟨701451, by rfl⟩ : syracuseStep 7482149 = 1402903) B1402903
theorem B18688805 : Blo 1148636 18688805 := bstep (se 4 (by rfl) ⟨1752075, by rfl⟩ : syracuseStep 18688805 = 3504151) B3504151
theorem B1747855 : Blo 1148636 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B2075539 : Blo 1148636 2075539 := bstep (se 1 (by rfl) ⟨1556654, by rfl⟩ : syracuseStep 2075539 = 3113309) B3113309
theorem B2763791 : Blo 1148636 2763791 := bstep (se 1 (by rfl) ⟨2072843, by rfl⟩ : syracuseStep 2763791 = 4145687) B4145687
theorem B1944695 : Blo 1148636 1944695 := bstep (se 1 (by rfl) ⟨1458521, by rfl⟩ : syracuseStep 1944695 = 2917043) B2917043
theorem B6302893 : Blo 1148636 6302893 := bstep (se 3 (by rfl) ⟨1181792, by rfl⟩ : syracuseStep 6302893 = 2363585) B2363585
theorem B3878279 : Blo 1148636 3878279 := bstep (se 1 (by rfl) ⟨2908709, by rfl⟩ : syracuseStep 3878279 = 5817419) B5817419
theorem B4140497 : Blo 1148636 4140497 := bstep (se 2 (by rfl) ⟨1552686, by rfl⟩ : syracuseStep 4140497 = 3105373) B3105373
theorem B14757329 : Blo 1148636 14757329 := bstep (se 2 (by rfl) ⟨5533998, by rfl⟩ : syracuseStep 14757329 = 11067997) B11067997
theorem B3878657 : Blo 1148636 3878657 := bstep (se 2 (by rfl) ⟨1454496, by rfl⟩ : syracuseStep 3878657 = 2908993) B2908993
theorem B6631303 : Blo 1148636 6631303 := bstep (se 1 (by rfl) ⟨4973477, by rfl⟩ : syracuseStep 6631303 = 9946955) B9946955
theorem B3879467 : Blo 1148636 3879467 := bstep (se 1 (by rfl) ⟨2909600, by rfl⟩ : syracuseStep 3879467 = 5819201) B5819201
theorem B16822849 : Blo 1148636 16822849 := bstep (se 2 (by rfl) ⟨6308568, by rfl⟩ : syracuseStep 16822849 = 12617137) B12617137
theorem B1684283 : Blo 1148636 1684283 := bstep (se 1 (by rfl) ⟨1263212, by rfl⟩ : syracuseStep 1684283 = 2526425) B2526425
theorem B1553465 : Blo 1148636 1553465 := bstep (se 2 (by rfl) ⟨582549, by rfl⟩ : syracuseStep 1553465 = 1165099) B1165099
theorem B49689733 : Blo 1148636 49689733 := bstep (se 4 (by rfl) ⟨4658412, by rfl⟩ : syracuseStep 49689733 = 9316825) B9316825
theorem B1455403 : Blo 1148636 1455403 := bstep (se 1 (by rfl) ⟨1091552, by rfl⟩ : syracuseStep 1455403 = 2183105) B2183105
theorem B1750519 : Blo 1148636 1750519 := bstep (se 1 (by rfl) ⟨1312889, by rfl⟩ : syracuseStep 1750519 = 2625779) B2625779
theorem B3880763 : Blo 1148636 3880763 := bstep (se 1 (by rfl) ⟨2910572, by rfl⟩ : syracuseStep 3880763 = 5821145) B5821145
theorem B14923723 : Blo 1148636 14923723 := bstep (se 1 (by rfl) ⟨11192792, by rfl⟩ : syracuseStep 14923723 = 22385585) B22385585
theorem B1292431 : Blo 1148636 1292431 := bstep (se 1 (by rfl) ⟨969323, by rfl⟩ : syracuseStep 1292431 = 1938647) B1938647
theorem B1456375 : Blo 1148636 1456375 := bstep (se 1 (by rfl) ⟨1092281, by rfl⟩ : syracuseStep 1456375 = 2184563) B2184563
theorem B3881249 : Blo 1148636 3881249 := bstep (se 2 (by rfl) ⟨1455468, by rfl⟩ : syracuseStep 3881249 = 2910937) B2910937
theorem B9451835 : Blo 1148636 9451835 := bstep (se 1 (by rfl) ⟨7088876, by rfl⟩ : syracuseStep 9451835 = 14177753) B14177753
theorem B26589505 : Blo 1148636 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B8403335 : Blo 1148636 8403335 := bstep (se 1 (by rfl) ⟨6302501, by rfl⟩ : syracuseStep 8403335 = 12605003) B12605003
theorem B1554859 : Blo 1148636 1554859 := bstep (se 1 (by rfl) ⟨1166144, by rfl⟩ : syracuseStep 1554859 = 2332289) B2332289
theorem B2767375 : Blo 1148636 2767375 := bstep (se 1 (by rfl) ⟨2075531, by rfl⟩ : syracuseStep 2767375 = 4151063) B4151063
theorem B1456699 : Blo 1148636 1456699 := bstep (se 1 (by rfl) ⟨1092524, by rfl⟩ : syracuseStep 1456699 = 2185049) B2185049
theorem B1292935 : Blo 1148636 1292935 := bstep (se 1 (by rfl) ⟨969701, by rfl⟩ : syracuseStep 1292935 = 1939403) B1939403
theorem B1293115 : Blo 1148636 1293115 := bstep (se 1 (by rfl) ⟨969836, by rfl⟩ : syracuseStep 1293115 = 1939673) B1939673
theorem B3881843 : Blo 1148636 3881843 := bstep (se 1 (by rfl) ⟨2911382, by rfl⟩ : syracuseStep 3881843 = 5822765) B5822765
theorem B1293583 : Blo 1148636 1293583 := bstep (se 1 (by rfl) ⟨970187, by rfl⟩ : syracuseStep 1293583 = 1940375) B1940375
theorem B1555897 : Blo 1148636 1555897 := bstep (se 2 (by rfl) ⟨583461, by rfl⟩ : syracuseStep 1555897 = 1166923) B1166923
theorem B66371075 : Blo 1148636 66371075 := bstep (se 1 (by rfl) ⟨49778306, by rfl⟩ : syracuseStep 66371075 = 99556613) B99556613
theorem B1457671 : Blo 1148636 1457671 := bstep (se 1 (by rfl) ⟨1093253, by rfl⟩ : syracuseStep 1457671 = 2186507) B2186507
theorem B2768537 : Blo 1148636 2768537 := bstep (se 2 (by rfl) ⟨1038201, by rfl⟩ : syracuseStep 2768537 = 2076403) B2076403
theorem B1294087 : Blo 1148636 1294087 := bstep (se 1 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 1294087 = 1941131) B1941131
theorem B5816123 : Blo 1148636 5816123 := bstep (se 1 (by rfl) ⟨4362092, by rfl⟩ : syracuseStep 5816123 = 8724185) B8724185
theorem B4374425 : Blo 1148636 4374425 := bstep (se 2 (by rfl) ⟨1640409, by rfl⟩ : syracuseStep 4374425 = 3280819) B3280819
theorem B1458091 : Blo 1148636 1458091 := bstep (se 1 (by rfl) ⟨1093568, by rfl⟩ : syracuseStep 1458091 = 2187137) B2187137
theorem B1294267 : Blo 1148636 1294267 := bstep (se 1 (by rfl) ⟨970700, by rfl⟩ : syracuseStep 1294267 = 1941401) B1941401
theorem B5816285 : Blo 1148636 5816285 := bstep (se 3 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 5816285 = 2181107) B2181107
theorem B3686411 : Blo 1148636 3686411 := bstep (se 1 (by rfl) ⟨2764808, by rfl⟩ : syracuseStep 3686411 = 5529617) B5529617
theorem B4145195 : Blo 1148636 4145195 := bstep (se 1 (by rfl) ⟨3108896, by rfl⟩ : syracuseStep 4145195 = 6217793) B6217793
theorem B1458319 : Blo 1148636 1458319 := bstep (se 1 (by rfl) ⟨1093739, by rfl⟩ : syracuseStep 1458319 = 2187479) B2187479
theorem B5816609 : Blo 1148636 5816609 := bstep (se 2 (by rfl) ⟨2181228, by rfl⟩ : syracuseStep 5816609 = 4362457) B4362457
theorem B5521697 : Blo 1148636 5521697 := bstep (se 2 (by rfl) ⟨2070636, by rfl⟩ : syracuseStep 5521697 = 4141273) B4141273
theorem B1294735 : Blo 1148636 1294735 := bstep (se 1 (by rfl) ⟨971051, by rfl⟩ : syracuseStep 1294735 = 1942103) B1942103
theorem B79577585 : Blo 1148636 79577585 := bstep (se 2 (by rfl) ⟨29841594, by rfl⟩ : syracuseStep 79577585 = 59683189) B59683189
theorem B1295239 : Blo 1148636 1295239 := bstep (se 1 (by rfl) ⟨971429, by rfl⟩ : syracuseStep 1295239 = 1942859) B1942859
theorem B1295419 : Blo 1148636 1295419 := bstep (se 1 (by rfl) ⟨971564, by rfl⟩ : syracuseStep 1295419 = 1943129) B1943129
theorem B5817581 : Blo 1148636 5817581 := bstep (se 3 (by rfl) ⟨1090796, by rfl⟩ : syracuseStep 5817581 = 2181593) B2181593
theorem B3884435 : Blo 1148636 3884435 := bstep (se 1 (by rfl) ⟨2913326, by rfl⟩ : syracuseStep 3884435 = 5826653) B5826653
theorem B1295887 : Blo 1148636 1295887 := bstep (se 1 (by rfl) ⟨971915, by rfl⟩ : syracuseStep 1295887 = 1943831) B1943831
theorem B3688193 : Blo 1148636 3688193 := bstep (se 2 (by rfl) ⟨1383072, by rfl⟩ : syracuseStep 3688193 = 2766145) B2766145
theorem B12437401 : Blo 1148636 12437401 := bstep (se 2 (by rfl) ⟨4664025, by rfl⟩ : syracuseStep 12437401 = 9328051) B9328051
theorem B1296391 : Blo 1148636 1296391 := bstep (se 1 (by rfl) ⟨972293, by rfl⟩ : syracuseStep 1296391 = 1944587) B1944587
theorem B5818391 : Blo 1148636 5818391 := bstep (se 1 (by rfl) ⟨4363793, by rfl⟩ : syracuseStep 5818391 = 8727587) B8727587
theorem B1165447 : Blo 1148636 1165447 := bstep (se 1 (by rfl) ⟨874085, by rfl⟩ : syracuseStep 1165447 = 1748171) B1748171
theorem B2181305 : Blo 1148636 2181305 := bstep (se 2 (by rfl) ⟨817989, by rfl⟩ : syracuseStep 2181305 = 1635979) B1635979
theorem B1296571 : Blo 1148636 1296571 := bstep (se 1 (by rfl) ⟨972428, by rfl⟩ : syracuseStep 1296571 = 1944857) B1944857
theorem B2181647 : Blo 1148636 2181647 := bstep (se 1 (by rfl) ⟨1636235, by rfl⟩ : syracuseStep 2181647 = 3272471) B3272471
theorem B1723067 : Blo 1148636 1723067 := bstep (se 1 (by rfl) ⟨1292300, by rfl⟩ : syracuseStep 1723067 = 2584601) B2584601
theorem B13126373 : Blo 1148636 13126373 := bstep (se 4 (by rfl) ⟨1230597, by rfl⟩ : syracuseStep 13126373 = 2461195) B2461195
theorem B1723127 : Blo 1148636 1723127 := bstep (se 1 (by rfl) ⟨1292345, by rfl⟩ : syracuseStep 1723127 = 2584691) B2584691
theorem B1723151 : Blo 1148636 1723151 := bstep (se 1 (by rfl) ⟨1292363, by rfl⟩ : syracuseStep 1723151 = 2584727) B2584727
theorem B3885839 : Blo 1148636 3885839 := bstep (se 1 (by rfl) ⟨2914379, by rfl⟩ : syracuseStep 3885839 = 5828759) B5828759
theorem B9325361 : Blo 1148636 9325361 := bstep (se 2 (by rfl) ⟨3497010, by rfl⟩ : syracuseStep 9325361 = 6994021) B6994021
theorem B1723193 : Blo 1148636 1723193 := bstep (se 2 (by rfl) ⟨646197, by rfl⟩ : syracuseStep 1723193 = 1292395) B1292395
theorem B16599923 : Blo 1148636 16599923 := bstep (se 1 (by rfl) ⟨12449942, by rfl⟩ : syracuseStep 16599923 = 24899885) B24899885
theorem B1723271 : Blo 1148636 1723271 := bstep (se 1 (by rfl) ⟨1292453, by rfl⟩ : syracuseStep 1723271 = 2584907) B2584907
theorem B1723307 : Blo 1148636 1723307 := bstep (se 1 (by rfl) ⟨1292480, by rfl⟩ : syracuseStep 1723307 = 2584961) B2584961
theorem B1723337 : Blo 1148636 1723337 := bstep (se 2 (by rfl) ⟨646251, by rfl⟩ : syracuseStep 1723337 = 1292503) B1292503
theorem B3886109 : Blo 1148636 3886109 := bstep (se 3 (by rfl) ⟨728645, by rfl⟩ : syracuseStep 3886109 = 1457291) B1457291
theorem B1723451 : Blo 1148636 1723451 := bstep (se 1 (by rfl) ⟨1292588, by rfl⟩ : syracuseStep 1723451 = 2585177) B2585177
theorem B1723511 : Blo 1148636 1723511 := bstep (se 1 (by rfl) ⟨1292633, by rfl⟩ : syracuseStep 1723511 = 2585267) B2585267
theorem B1723535 : Blo 1148636 1723535 := bstep (se 1 (by rfl) ⟨1292651, by rfl⟩ : syracuseStep 1723535 = 2585303) B2585303
theorem B1723577 : Blo 1148636 1723577 := bstep (se 2 (by rfl) ⟨646341, by rfl⟩ : syracuseStep 1723577 = 1292683) B1292683
theorem B1723655 : Blo 1148636 1723655 := bstep (se 1 (by rfl) ⟨1292741, by rfl⟩ : syracuseStep 1723655 = 2585483) B2585483
theorem B1723691 : Blo 1148636 1723691 := bstep (se 1 (by rfl) ⟨1292768, by rfl⟩ : syracuseStep 1723691 = 2585537) B2585537
theorem B2182459 : Blo 1148636 2182459 := bstep (se 1 (by rfl) ⟨1636844, by rfl⟩ : syracuseStep 2182459 = 3273689) B3273689
theorem B1723721 : Blo 1148636 1723721 := bstep (se 2 (by rfl) ⟨646395, by rfl⟩ : syracuseStep 1723721 = 1292791) B1292791
theorem B2182535 : Blo 1148636 2182535 := bstep (se 1 (by rfl) ⟨1636901, by rfl⟩ : syracuseStep 2182535 = 3273803) B3273803
theorem B1723835 : Blo 1148636 1723835 := bstep (se 1 (by rfl) ⟨1292876, by rfl⟩ : syracuseStep 1723835 = 2585753) B2585753
theorem B1723895 : Blo 1148636 1723895 := bstep (se 1 (by rfl) ⟨1292921, by rfl⟩ : syracuseStep 1723895 = 2585843) B2585843
theorem B1723919 : Blo 1148636 1723919 := bstep (se 1 (by rfl) ⟨1292939, by rfl⟩ : syracuseStep 1723919 = 2585879) B2585879
theorem B1723961 : Blo 1148636 1723961 := bstep (se 2 (by rfl) ⟨646485, by rfl⟩ : syracuseStep 1723961 = 1292971) B1292971
theorem B1724039 : Blo 1148636 1724039 := bstep (se 1 (by rfl) ⟨1293029, by rfl⟩ : syracuseStep 1724039 = 2586059) B2586059
theorem B1724075 : Blo 1148636 1724075 := bstep (se 1 (by rfl) ⟨1293056, by rfl⟩ : syracuseStep 1724075 = 2586113) B2586113
theorem B1724105 : Blo 1148636 1724105 := bstep (se 2 (by rfl) ⟨646539, by rfl⟩ : syracuseStep 1724105 = 1293079) B1293079
theorem B2182945 : Blo 1148636 2182945 := bstep (se 2 (by rfl) ⟨818604, by rfl⟩ : syracuseStep 2182945 = 1637209) B1637209
theorem B1724219 : Blo 1148636 1724219 := bstep (se 1 (by rfl) ⟨1293164, by rfl⟩ : syracuseStep 1724219 = 2586329) B2586329
theorem B1724279 : Blo 1148636 1724279 := bstep (se 1 (by rfl) ⟨1293209, by rfl⟩ : syracuseStep 1724279 = 2586419) B2586419
theorem B1724303 : Blo 1148636 1724303 := bstep (se 1 (by rfl) ⟨1293227, by rfl⟩ : syracuseStep 1724303 = 2586455) B2586455
theorem B1724345 : Blo 1148636 1724345 := bstep (se 2 (by rfl) ⟨646629, by rfl⟩ : syracuseStep 1724345 = 1293259) B1293259
theorem B1724423 : Blo 1148636 1724423 := bstep (se 1 (by rfl) ⟨1293317, by rfl⟩ : syracuseStep 1724423 = 2586635) B2586635
theorem B1724459 : Blo 1148636 1724459 := bstep (se 1 (by rfl) ⟨1293344, by rfl⟩ : syracuseStep 1724459 = 2586689) B2586689
theorem B1724489 : Blo 1148636 1724489 := bstep (se 2 (by rfl) ⟨646683, by rfl⟩ : syracuseStep 1724489 = 1293367) B1293367
theorem B2183287 : Blo 1148636 2183287 := bstep (se 1 (by rfl) ⟨1637465, by rfl⟩ : syracuseStep 2183287 = 3274931) B3274931
theorem B1724603 : Blo 1148636 1724603 := bstep (se 1 (by rfl) ⟨1293452, by rfl⟩ : syracuseStep 1724603 = 2586905) B2586905
theorem B1724663 : Blo 1148636 1724663 := bstep (se 1 (by rfl) ⟨1293497, by rfl⟩ : syracuseStep 1724663 = 2586995) B2586995
theorem B1724687 : Blo 1148636 1724687 := bstep (se 1 (by rfl) ⟨1293515, by rfl⟩ : syracuseStep 1724687 = 2587031) B2587031
theorem B1724729 : Blo 1148636 1724729 := bstep (se 2 (by rfl) ⟨646773, by rfl⟩ : syracuseStep 1724729 = 1293547) B1293547
theorem B1724807 : Blo 1148636 1724807 := bstep (se 1 (by rfl) ⟨1293605, by rfl⟩ : syracuseStep 1724807 = 2587211) B2587211
theorem B3887513 : Blo 1148636 3887513 := bstep (se 2 (by rfl) ⟨1457817, by rfl⟩ : syracuseStep 3887513 = 2915635) B2915635
theorem B1724843 : Blo 1148636 1724843 := bstep (se 1 (by rfl) ⟨1293632, by rfl⟩ : syracuseStep 1724843 = 2587265) B2587265
theorem B1724873 : Blo 1148636 1724873 := bstep (se 2 (by rfl) ⟨646827, by rfl⟩ : syracuseStep 1724873 = 1293655) B1293655
theorem B1724987 : Blo 1148636 1724987 := bstep (se 1 (by rfl) ⟨1293740, by rfl⟩ : syracuseStep 1724987 = 2587481) B2587481
theorem B1725047 : Blo 1148636 1725047 := bstep (se 1 (by rfl) ⟨1293785, by rfl⟩ : syracuseStep 1725047 = 2587571) B2587571
theorem B1725071 : Blo 1148636 1725071 := bstep (se 1 (by rfl) ⟨1293803, by rfl⟩ : syracuseStep 1725071 = 2587607) B2587607
theorem B1725113 : Blo 1148636 1725113 := bstep (se 2 (by rfl) ⟨646917, by rfl⟩ : syracuseStep 1725113 = 1293835) B1293835
theorem B23646937 : Blo 1148636 23646937 := bstep (se 2 (by rfl) ⟨8867601, by rfl⟩ : syracuseStep 23646937 = 17735203) B17735203
theorem B1725191 : Blo 1148636 1725191 := bstep (se 1 (by rfl) ⟨1293893, by rfl⟩ : syracuseStep 1725191 = 2587787) B2587787
theorem B41931557 : Blo 1148636 41931557 := bstep (se 4 (by rfl) ⟨3931083, by rfl⟩ : syracuseStep 41931557 = 7862167) B7862167
theorem B1725227 : Blo 1148636 1725227 := bstep (se 1 (by rfl) ⟨1293920, by rfl⟩ : syracuseStep 1725227 = 2587841) B2587841
theorem B1725257 : Blo 1148636 1725257 := bstep (se 2 (by rfl) ⟨646971, by rfl⟩ : syracuseStep 1725257 = 1293943) B1293943
theorem B13095755 : Blo 1148636 13095755 := bstep (se 1 (by rfl) ⟨9821816, by rfl⟩ : syracuseStep 13095755 = 19643633) B19643633
theorem B3494809 : Blo 1148636 3494809 := bstep (se 2 (by rfl) ⟨1310553, by rfl⟩ : syracuseStep 3494809 = 2621107) B2621107
theorem B1725371 : Blo 1148636 1725371 := bstep (se 1 (by rfl) ⟨1294028, by rfl⟩ : syracuseStep 1725371 = 2588057) B2588057
theorem B9819083 : Blo 1148636 9819083 := bstep (se 1 (by rfl) ⟨7364312, by rfl⟩ : syracuseStep 9819083 = 14728625) B14728625
theorem B1725431 : Blo 1148636 1725431 := bstep (se 1 (by rfl) ⟨1294073, by rfl⟩ : syracuseStep 1725431 = 2588147) B2588147
theorem B1725455 : Blo 1148636 1725455 := bstep (se 1 (by rfl) ⟨1294091, by rfl⟩ : syracuseStep 1725455 = 2588183) B2588183
theorem B5821469 : Blo 1148636 5821469 := bstep (se 3 (by rfl) ⟨1091525, by rfl⟩ : syracuseStep 5821469 = 2183051) B2183051
theorem B1725497 : Blo 1148636 1725497 := bstep (se 2 (by rfl) ⟨647061, by rfl⟩ : syracuseStep 1725497 = 1294123) B1294123
theorem B3888215 : Blo 1148636 3888215 := bstep (se 1 (by rfl) ⟨2916161, by rfl⟩ : syracuseStep 3888215 = 5832323) B5832323
theorem B1725575 : Blo 1148636 1725575 := bstep (se 1 (by rfl) ⟨1294181, by rfl⟩ : syracuseStep 1725575 = 2588363) B2588363
theorem B1725611 : Blo 1148636 1725611 := bstep (se 1 (by rfl) ⟨1294208, by rfl⟩ : syracuseStep 1725611 = 2588417) B2588417
theorem B1725641 : Blo 1148636 1725641 := bstep (se 2 (by rfl) ⟨647115, by rfl⟩ : syracuseStep 1725641 = 1294231) B1294231
theorem B5985569 : Blo 1148636 5985569 := bstep (se 2 (by rfl) ⟨2244588, by rfl⟩ : syracuseStep 5985569 = 4489177) B4489177
theorem B1496363 : Blo 1148636 1496363 := bstep (se 1 (by rfl) ⟨1122272, by rfl⟩ : syracuseStep 1496363 = 2244545) B2244545
theorem B1725755 : Blo 1148636 1725755 := bstep (se 1 (by rfl) ⟨1294316, by rfl⟩ : syracuseStep 1725755 = 2588633) B2588633
theorem B1725815 : Blo 1148636 1725815 := bstep (se 1 (by rfl) ⟨1294361, by rfl⟩ : syracuseStep 1725815 = 2588723) B2588723
theorem B1725839 : Blo 1148636 1725839 := bstep (se 1 (by rfl) ⟨1294379, by rfl⟩ : syracuseStep 1725839 = 2588759) B2588759
theorem B1725881 : Blo 1148636 1725881 := bstep (se 2 (by rfl) ⟨647205, by rfl⟩ : syracuseStep 1725881 = 1294411) B1294411
theorem B6641099 : Blo 1148636 6641099 := bstep (se 1 (by rfl) ⟨4980824, by rfl⟩ : syracuseStep 6641099 = 9961649) B9961649
theorem B5821955 : Blo 1148636 5821955 := bstep (se 1 (by rfl) ⟨4366466, by rfl⟩ : syracuseStep 5821955 = 8732933) B8732933
theorem B1725959 : Blo 1148636 1725959 := bstep (se 1 (by rfl) ⟨1294469, by rfl⟩ : syracuseStep 1725959 = 2588939) B2588939
theorem B1725995 : Blo 1148636 1725995 := bstep (se 1 (by rfl) ⟨1294496, by rfl⟩ : syracuseStep 1725995 = 2588993) B2588993
theorem B3888701 : Blo 1148636 3888701 := bstep (se 3 (by rfl) ⟨729131, by rfl⟩ : syracuseStep 3888701 = 1458263) B1458263
theorem B1726025 : Blo 1148636 1726025 := bstep (se 2 (by rfl) ⟨647259, by rfl⟩ : syracuseStep 1726025 = 1294519) B1294519
theorem B23025329 : Blo 1148636 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B2184889 : Blo 1148636 2184889 := bstep (se 2 (by rfl) ⟨819333, by rfl⟩ : syracuseStep 2184889 = 1638667) B1638667
theorem B1726139 : Blo 1148636 1726139 := bstep (se 1 (by rfl) ⟨1294604, by rfl⟩ : syracuseStep 1726139 = 2589209) B2589209
theorem B1726199 : Blo 1148636 1726199 := bstep (se 1 (by rfl) ⟨1294649, by rfl⟩ : syracuseStep 1726199 = 2589299) B2589299
theorem B1726223 : Blo 1148636 1726223 := bstep (se 1 (by rfl) ⟨1294667, by rfl⟩ : syracuseStep 1726223 = 2589335) B2589335
theorem B1726265 : Blo 1148636 1726265 := bstep (se 2 (by rfl) ⟨647349, by rfl⟩ : syracuseStep 1726265 = 1294699) B1294699
theorem B1726343 : Blo 1148636 1726343 := bstep (se 1 (by rfl) ⟨1294757, by rfl⟩ : syracuseStep 1726343 = 2589515) B2589515
theorem B1726379 : Blo 1148636 1726379 := bstep (se 1 (by rfl) ⟨1294784, by rfl⟩ : syracuseStep 1726379 = 2589569) B2589569
theorem B1726409 : Blo 1148636 1726409 := bstep (se 2 (by rfl) ⟨647403, by rfl⟩ : syracuseStep 1726409 = 1294807) B1294807
theorem B2185231 : Blo 1148636 2185231 := bstep (se 1 (by rfl) ⟨1638923, by rfl⟩ : syracuseStep 2185231 = 3277847) B3277847
theorem B1726523 : Blo 1148636 1726523 := bstep (se 1 (by rfl) ⟨1294892, by rfl⟩ : syracuseStep 1726523 = 2589785) B2589785
theorem B1726583 : Blo 1148636 1726583 := bstep (se 1 (by rfl) ⟨1294937, by rfl⟩ : syracuseStep 1726583 = 2589875) B2589875
theorem B1726607 : Blo 1148636 1726607 := bstep (se 1 (by rfl) ⟨1294955, by rfl⟩ : syracuseStep 1726607 = 2589911) B2589911
theorem B1726649 : Blo 1148636 1726649 := bstep (se 2 (by rfl) ⟨647493, by rfl⟩ : syracuseStep 1726649 = 1294987) B1294987
theorem B1726727 : Blo 1148636 1726727 := bstep (se 1 (by rfl) ⟨1295045, by rfl⟩ : syracuseStep 1726727 = 2590091) B2590091
theorem B1726763 : Blo 1148636 1726763 := bstep (se 1 (by rfl) ⟨1295072, by rfl⟩ : syracuseStep 1726763 = 2590145) B2590145
theorem B1726793 : Blo 1148636 1726793 := bstep (se 2 (by rfl) ⟨647547, by rfl⟩ : syracuseStep 1726793 = 1295095) B1295095
theorem B1726907 : Blo 1148636 1726907 := bstep (se 1 (by rfl) ⟨1295180, by rfl⟩ : syracuseStep 1726907 = 2590361) B2590361
theorem B16603613 : Blo 1148636 16603613 := bstep (se 3 (by rfl) ⟨3113177, by rfl⟩ : syracuseStep 16603613 = 6226355) B6226355
theorem B1726967 : Blo 1148636 1726967 := bstep (se 1 (by rfl) ⟨1295225, by rfl⟩ : syracuseStep 1726967 = 2590451) B2590451
theorem B3496463 : Blo 1148636 3496463 := bstep (se 1 (by rfl) ⟨2622347, by rfl⟩ : syracuseStep 3496463 = 5244695) B5244695
theorem B1726991 : Blo 1148636 1726991 := bstep (se 1 (by rfl) ⟨1295243, by rfl⟩ : syracuseStep 1726991 = 2590487) B2590487
theorem B1727033 : Blo 1148636 1727033 := bstep (se 2 (by rfl) ⟨647637, by rfl⟩ : syracuseStep 1727033 = 1295275) B1295275
theorem B3496535 : Blo 1148636 3496535 := bstep (se 1 (by rfl) ⟨2622401, by rfl⟩ : syracuseStep 3496535 = 5244803) B5244803
theorem B1727111 : Blo 1148636 1727111 := bstep (se 1 (by rfl) ⟨1295333, by rfl⟩ : syracuseStep 1727111 = 2590667) B2590667
theorem B1727147 : Blo 1148636 1727147 := bstep (se 1 (by rfl) ⟨1295360, by rfl⟩ : syracuseStep 1727147 = 2590721) B2590721
theorem B16603841 : Blo 1148636 16603841 := bstep (se 2 (by rfl) ⟨6226440, by rfl⟩ : syracuseStep 16603841 = 12452881) B12452881
theorem B1727177 : Blo 1148636 1727177 := bstep (se 2 (by rfl) ⟨647691, by rfl⟩ : syracuseStep 1727177 = 1295383) B1295383
theorem B1727291 : Blo 1148636 1727291 := bstep (se 1 (by rfl) ⟨1295468, by rfl⟩ : syracuseStep 1727291 = 2590937) B2590937
theorem B1727351 : Blo 1148636 1727351 := bstep (se 1 (by rfl) ⟨1295513, by rfl⟩ : syracuseStep 1727351 = 2591027) B2591027
theorem B2186119 : Blo 1148636 2186119 := bstep (se 1 (by rfl) ⟨1639589, by rfl⟩ : syracuseStep 2186119 = 3279179) B3279179
theorem B1727375 : Blo 1148636 1727375 := bstep (se 1 (by rfl) ⟨1295531, by rfl⟩ : syracuseStep 1727375 = 2591063) B2591063
theorem B8739737 : Blo 1148636 8739737 := bstep (se 2 (by rfl) ⟨3277401, by rfl⟩ : syracuseStep 8739737 = 6554803) B6554803
theorem B4152217 : Blo 1148636 4152217 := bstep (se 2 (by rfl) ⟨1557081, by rfl⟩ : syracuseStep 4152217 = 3114163) B3114163
theorem B1727417 : Blo 1148636 1727417 := bstep (se 2 (by rfl) ⟨647781, by rfl⟩ : syracuseStep 1727417 = 1295563) B1295563
theorem B3890105 : Blo 1148636 3890105 := bstep (se 2 (by rfl) ⟨1458789, by rfl⟩ : syracuseStep 3890105 = 2917579) B2917579
theorem B1727495 : Blo 1148636 1727495 := bstep (se 1 (by rfl) ⟨1295621, by rfl⟩ : syracuseStep 1727495 = 2591243) B2591243
theorem B1727531 : Blo 1148636 1727531 := bstep (se 1 (by rfl) ⟨1295648, by rfl⟩ : syracuseStep 1727531 = 2591297) B2591297
theorem B1727561 : Blo 1148636 1727561 := bstep (se 2 (by rfl) ⟨647835, by rfl⟩ : syracuseStep 1727561 = 1295671) B1295671
theorem B5823575 : Blo 1148636 5823575 := bstep (se 1 (by rfl) ⟨4367681, by rfl⟩ : syracuseStep 5823575 = 8735363) B8735363
theorem B5528695 : Blo 1148636 5528695 := bstep (se 1 (by rfl) ⟨4146521, by rfl⟩ : syracuseStep 5528695 = 8293043) B8293043
theorem B1727675 : Blo 1148636 1727675 := bstep (se 1 (by rfl) ⟨1295756, by rfl⟩ : syracuseStep 1727675 = 2591513) B2591513
theorem B1727735 : Blo 1148636 1727735 := bstep (se 1 (by rfl) ⟨1295801, by rfl⟩ : syracuseStep 1727735 = 2591603) B2591603
theorem B1727759 : Blo 1148636 1727759 := bstep (se 1 (by rfl) ⟨1295819, by rfl⟩ : syracuseStep 1727759 = 2591639) B2591639
theorem B1727801 : Blo 1148636 1727801 := bstep (se 2 (by rfl) ⟨647925, by rfl⟩ : syracuseStep 1727801 = 1295851) B1295851
theorem B1727879 : Blo 1148636 1727879 := bstep (se 1 (by rfl) ⟨1295909, by rfl⟩ : syracuseStep 1727879 = 2591819) B2591819
theorem B1727915 : Blo 1148636 1727915 := bstep (se 1 (by rfl) ⟨1295936, by rfl⟩ : syracuseStep 1727915 = 2591873) B2591873
theorem B1727945 : Blo 1148636 1727945 := bstep (se 2 (by rfl) ⟨647979, by rfl⟩ : syracuseStep 1727945 = 1295959) B1295959
theorem B1728059 : Blo 1148636 1728059 := bstep (se 1 (by rfl) ⟨1296044, by rfl⟩ : syracuseStep 1728059 = 2592089) B2592089
theorem B5824061 : Blo 1148636 5824061 := bstep (se 3 (by rfl) ⟨1092011, by rfl⟩ : syracuseStep 5824061 = 2184023) B2184023
theorem B23977547 : Blo 1148636 23977547 := bstep (se 1 (by rfl) ⟨17983160, by rfl⟩ : syracuseStep 23977547 = 35966321) B35966321
theorem B1728119 : Blo 1148636 1728119 := bstep (se 1 (by rfl) ⟨1296089, by rfl⟩ : syracuseStep 1728119 = 2592179) B2592179
theorem B1728143 : Blo 1148636 1728143 := bstep (se 1 (by rfl) ⟨1296107, by rfl⟩ : syracuseStep 1728143 = 2592215) B2592215
theorem B1728185 : Blo 1148636 1728185 := bstep (se 2 (by rfl) ⟨648069, by rfl⟩ : syracuseStep 1728185 = 1296139) B1296139
theorem B6217445 : Blo 1148636 6217445 := bstep (se 4 (by rfl) ⟨582885, by rfl⟩ : syracuseStep 6217445 = 1165771) B1165771
theorem B1728263 : Blo 1148636 1728263 := bstep (se 1 (by rfl) ⟨1296197, by rfl⟩ : syracuseStep 1728263 = 2592395) B2592395
theorem B1728299 : Blo 1148636 1728299 := bstep (se 1 (by rfl) ⟨1296224, by rfl⟩ : syracuseStep 1728299 = 2592449) B2592449
theorem B3497789 : Blo 1148636 3497789 := bstep (se 3 (by rfl) ⟨655835, by rfl⟩ : syracuseStep 3497789 = 1311671) B1311671
theorem B1728329 : Blo 1148636 1728329 := bstep (se 2 (by rfl) ⟨648123, by rfl⟩ : syracuseStep 1728329 = 1296247) B1296247
theorem B12443543 : Blo 1148636 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B1728443 : Blo 1148636 1728443 := bstep (se 1 (by rfl) ⟨1296332, by rfl⟩ : syracuseStep 1728443 = 2592665) B2592665
theorem B1728503 : Blo 1148636 1728503 := bstep (se 1 (by rfl) ⟨1296377, by rfl⟩ : syracuseStep 1728503 = 2592755) B2592755
theorem B1728527 : Blo 1148636 1728527 := bstep (se 1 (by rfl) ⟨1296395, by rfl⟩ : syracuseStep 1728527 = 2592791) B2592791
theorem B1728569 : Blo 1148636 1728569 := bstep (se 2 (by rfl) ⟨648213, by rfl⟩ : syracuseStep 1728569 = 1296427) B1296427
theorem B2908295 : Blo 1148636 2908295 := bstep (se 1 (by rfl) ⟨2181221, by rfl⟩ : syracuseStep 2908295 = 4362443) B4362443
theorem B1728647 : Blo 1148636 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B1728683 : Blo 1148636 1728683 := bstep (se 1 (by rfl) ⟨1296512, by rfl⟩ : syracuseStep 1728683 = 2593025) B2593025
theorem B2908345 : Blo 1148636 2908345 := bstep (se 2 (by rfl) ⟨1090629, by rfl⟩ : syracuseStep 2908345 = 2181259) B2181259
theorem B1728713 : Blo 1148636 1728713 := bstep (se 2 (by rfl) ⟨648267, by rfl⟩ : syracuseStep 1728713 = 1296535) B1296535
theorem B1728827 : Blo 1148636 1728827 := bstep (se 1 (by rfl) ⟨1296620, by rfl⟩ : syracuseStep 1728827 = 2593241) B2593241
theorem B1728887 : Blo 1148636 1728887 := bstep (se 1 (by rfl) ⟨1296665, by rfl⟩ : syracuseStep 1728887 = 2593331) B2593331
theorem B1728911 : Blo 1148636 1728911 := bstep (se 1 (by rfl) ⟨1296683, by rfl⟩ : syracuseStep 1728911 = 2593367) B2593367
theorem B6218137 : Blo 1148636 6218137 := bstep (se 2 (by rfl) ⟨2331801, by rfl⟩ : syracuseStep 6218137 = 4663603) B4663603
theorem B1728953 : Blo 1148636 1728953 := bstep (se 2 (by rfl) ⟨648357, by rfl⟩ : syracuseStep 1728953 = 1296715) B1296715
theorem B6545873 : Blo 1148636 6545873 := bstep (se 2 (by rfl) ⟨2454702, by rfl⟩ : syracuseStep 6545873 = 4909405) B4909405
theorem B14016989 : Blo 1148636 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B2187911 : Blo 1148636 2187911 := bstep (se 1 (by rfl) ⟨1640933, by rfl⟩ : syracuseStep 2187911 = 3281867) B3281867
theorem B1368839 : Blo 1148636 1368839 := bstep (se 1 (by rfl) ⟨1026629, by rfl⟩ : syracuseStep 1368839 = 2053259) B2053259
theorem B2908943 : Blo 1148636 2908943 := bstep (se 1 (by rfl) ⟨2181707, by rfl⟩ : syracuseStep 2908943 = 4363415) B4363415
theorem B8741681 : Blo 1148636 8741681 := bstep (se 2 (by rfl) ⟨3278130, by rfl⟩ : syracuseStep 8741681 = 6556261) B6556261
theorem B6546329 : Blo 1148636 6546329 := bstep (se 2 (by rfl) ⟨2454873, by rfl⟩ : syracuseStep 6546329 = 4909747) B4909747
theorem B3597497 : Blo 1148636 3597497 := bstep (se 2 (by rfl) ⟨1349061, by rfl⟩ : syracuseStep 3597497 = 2698123) B2698123
theorem B6645025 : Blo 1148636 6645025 := bstep (se 2 (by rfl) ⟨2491884, by rfl⟩ : syracuseStep 6645025 = 4983769) B4983769
theorem B5825843 : Blo 1148636 5825843 := bstep (se 1 (by rfl) ⟨4369382, by rfl⟩ : syracuseStep 5825843 = 8738765) B8738765
theorem B4908347 : Blo 1148636 4908347 := bstep (se 1 (by rfl) ⟨3681260, by rfl⟩ : syracuseStep 4908347 = 7362521) B7362521
theorem B2909641 : Blo 1148636 2909641 := bstep (se 2 (by rfl) ⟨1091115, by rfl⟩ : syracuseStep 2909641 = 2182231) B2182231
theorem B7366211 : Blo 1148636 7366211 := bstep (se 1 (by rfl) ⟨5524658, by rfl⟩ : syracuseStep 7366211 = 11049317) B11049317
theorem B2909783 : Blo 1148636 2909783 := bstep (se 1 (by rfl) ⟨2182337, by rfl⟩ : syracuseStep 2909783 = 4364675) B4364675
theorem B5826167 : Blo 1148636 5826167 := bstep (se 1 (by rfl) ⟨4369625, by rfl⟩ : syracuseStep 5826167 = 8739251) B8739251
theorem B6219521 : Blo 1148636 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B3270955 : Blo 1148636 3270955 := bstep (se 1 (by rfl) ⟨2453216, by rfl⟩ : syracuseStep 3270955 = 4906433) B4906433
theorem B3107339 : Blo 1148636 3107339 := bstep (se 1 (by rfl) ⟨2330504, by rfl⟩ : syracuseStep 3107339 = 4661009) B4661009
theorem B3271229 : Blo 1148636 3271229 := bstep (se 3 (by rfl) ⟨613355, by rfl⟩ : syracuseStep 3271229 = 1226711) B1226711
theorem B5827139 : Blo 1148636 5827139 := bstep (se 1 (by rfl) ⟨4370354, by rfl⟩ : syracuseStep 5827139 = 8740709) B8740709
theorem B5827463 : Blo 1148636 5827463 := bstep (se 1 (by rfl) ⟨4370597, by rfl⟩ : syracuseStep 5827463 = 8741195) B8741195
theorem B33221987 : Blo 1148636 33221987 := bstep (se 1 (by rfl) ⟨24916490, by rfl⟩ : syracuseStep 33221987 = 49832981) B49832981
theorem B3272071 : Blo 1148636 3272071 := bstep (se 1 (by rfl) ⟨2454053, by rfl⟩ : syracuseStep 3272071 = 4908107) B4908107
theorem B4910483 : Blo 1148636 4910483 := bstep (se 1 (by rfl) ⟨3682862, by rfl⟩ : syracuseStep 4910483 = 7365725) B7365725
theorem B4910635 : Blo 1148636 4910635 := bstep (se 1 (by rfl) ⟨3682976, by rfl⟩ : syracuseStep 4910635 = 7365953) B7365953
theorem B5533271 : Blo 1148636 5533271 := bstep (se 1 (by rfl) ⟨4149953, by rfl⟩ : syracuseStep 5533271 = 8299907) B8299907
theorem B2911859 : Blo 1148636 2911859 := bstep (se 1 (by rfl) ⟨2183894, by rfl⟩ : syracuseStep 2911859 = 4367789) B4367789
theorem B3272345 : Blo 1148636 3272345 := bstep (se 2 (by rfl) ⟨1227129, by rfl⟩ : syracuseStep 3272345 = 2454259) B2454259
theorem B13987505 : Blo 1148636 13987505 := bstep (se 2 (by rfl) ⟨5245314, by rfl⟩ : syracuseStep 13987505 = 10490629) B10490629
theorem B2584439 : Blo 1148636 2584439 := bstep (se 1 (by rfl) ⟨1938329, by rfl⟩ : syracuseStep 2584439 = 3876659) B3876659
theorem B3502109 : Blo 1148636 3502109 := bstep (se 3 (by rfl) ⟨656645, by rfl⟩ : syracuseStep 3502109 = 1313291) B1313291
theorem B2584619 : Blo 1148636 2584619 := bstep (se 1 (by rfl) ⟨1938464, by rfl⟩ : syracuseStep 2584619 = 3876929) B3876929
theorem B2912375 : Blo 1148636 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B2584979 : Blo 1148636 2584979 := bstep (se 1 (by rfl) ⟨1938734, by rfl⟩ : syracuseStep 2584979 = 3877469) B3877469
theorem B2585033 : Blo 1148636 2585033 := bstep (se 2 (by rfl) ⟨969387, by rfl⟩ : syracuseStep 2585033 = 1938775) B1938775
theorem B3273473 : Blo 1148636 3273473 := bstep (se 2 (by rfl) ⟨1227552, by rfl⟩ : syracuseStep 3273473 = 2455105) B2455105
theorem B8090369 : Blo 1148636 8090369 := bstep (se 2 (by rfl) ⟨3033888, by rfl⟩ : syracuseStep 8090369 = 6067777) B6067777
theorem B4912139 : Blo 1148636 4912139 := bstep (se 1 (by rfl) ⟨3684104, by rfl⟩ : syracuseStep 4912139 = 7368209) B7368209
theorem B2913367 : Blo 1148636 2913367 := bstep (se 1 (by rfl) ⟨2185025, by rfl⟩ : syracuseStep 2913367 = 4370051) B4370051
theorem B2585735 : Blo 1148636 2585735 := bstep (se 1 (by rfl) ⟨1939301, by rfl⟩ : syracuseStep 2585735 = 3878603) B3878603
theorem B3273929 : Blo 1148636 3273929 := bstep (se 2 (by rfl) ⟨1227723, by rfl⟩ : syracuseStep 3273929 = 2455447) B2455447
theorem B1635643 : Blo 1148636 1635643 := bstep (se 1 (by rfl) ⟨1226732, by rfl⟩ : syracuseStep 1635643 = 2453465) B2453465
theorem B2585915 : Blo 1148636 2585915 := bstep (se 1 (by rfl) ⟨1939436, by rfl⟩ : syracuseStep 2585915 = 3878873) B3878873
theorem B2913671 : Blo 1148636 2913671 := bstep (se 1 (by rfl) ⟨2185253, by rfl⟩ : syracuseStep 2913671 = 4370507) B4370507
theorem B2586041 : Blo 1148636 2586041 := bstep (se 2 (by rfl) ⟨969765, by rfl⟩ : syracuseStep 2586041 = 1939531) B1939531
theorem B2913803 : Blo 1148636 2913803 := bstep (se 1 (by rfl) ⟨2185352, by rfl⟩ : syracuseStep 2913803 = 4370705) B4370705
theorem B2586383 : Blo 1148636 2586383 := bstep (se 1 (by rfl) ⟨1939787, by rfl⟩ : syracuseStep 2586383 = 3879575) B3879575
theorem B2586401 : Blo 1148636 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B63141697 : Blo 1148636 63141697 := bstep (se 2 (by rfl) ⟨23678136, by rfl⟩ : syracuseStep 63141697 = 47356273) B47356273
theorem B4913081 : Blo 1148636 4913081 := bstep (se 2 (by rfl) ⟨1842405, by rfl⟩ : syracuseStep 4913081 = 3684811) B3684811
theorem B2914319 : Blo 1148636 2914319 := bstep (se 1 (by rfl) ⟨2185739, by rfl⟩ : syracuseStep 2914319 = 4371479) B4371479
theorem B2586743 : Blo 1148636 2586743 := bstep (se 1 (by rfl) ⟨1940057, by rfl⟩ : syracuseStep 2586743 = 3880115) B3880115
theorem B2914451 : Blo 1148636 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B1636537 : Blo 1148636 1636537 := bstep (se 2 (by rfl) ⟨613701, by rfl⟩ : syracuseStep 1636537 = 1227403) B1227403
theorem B2586923 : Blo 1148636 2586923 := bstep (se 1 (by rfl) ⟨1940192, by rfl⟩ : syracuseStep 2586923 = 3880385) B3880385
theorem B5831027 : Blo 1148636 5831027 := bstep (se 1 (by rfl) ⟨4373270, by rfl⟩ : syracuseStep 5831027 = 8746541) B8746541
theorem B24869267 : Blo 1148636 24869267 := bstep (se 1 (by rfl) ⟨18651950, by rfl⟩ : syracuseStep 24869267 = 37303901) B37303901
theorem B2947513 : Blo 1148636 2947513 := bstep (se 2 (by rfl) ⟨1105317, by rfl⟩ : syracuseStep 2947513 = 2210635) B2210635
theorem B2587283 : Blo 1148636 2587283 := bstep (se 1 (by rfl) ⟨1940462, by rfl⟩ : syracuseStep 2587283 = 3880925) B3880925
theorem B3111577 : Blo 1148636 3111577 := bstep (se 2 (by rfl) ⟨1166841, by rfl⟩ : syracuseStep 3111577 = 2333683) B2333683
theorem B2587337 : Blo 1148636 2587337 := bstep (se 2 (by rfl) ⟨970251, by rfl⟩ : syracuseStep 2587337 = 1940503) B1940503
theorem B2456335 : Blo 1148636 2456335 := bstep (se 1 (by rfl) ⟨1842251, by rfl⟩ : syracuseStep 2456335 = 3684503) B3684503
theorem B3111709 : Blo 1148636 3111709 := bstep (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) B1166891
theorem B3275579 : Blo 1148636 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B5831513 : Blo 1148636 5831513 := bstep (se 2 (by rfl) ⟨2186817, by rfl⟩ : syracuseStep 5831513 = 4373635) B4373635
theorem B5536961 : Blo 1148636 5536961 := bstep (se 2 (by rfl) ⟨2076360, by rfl⟩ : syracuseStep 5536961 = 4152721) B4152721
theorem B2915585 : Blo 1148636 2915585 := bstep (se 2 (by rfl) ⟨1093344, by rfl⟩ : syracuseStep 2915585 = 2186689) B2186689
theorem B2588039 : Blo 1148636 2588039 := bstep (se 1 (by rfl) ⟨1941029, by rfl⟩ : syracuseStep 2588039 = 3882059) B3882059
theorem B1637767 : Blo 1148636 1637767 := bstep (se 1 (by rfl) ⟨1228325, by rfl⟩ : syracuseStep 1637767 = 2456651) B2456651
theorem B3276217 : Blo 1148636 3276217 := bstep (se 2 (by rfl) ⟨1228581, by rfl⟩ : syracuseStep 3276217 = 2457163) B2457163
theorem B2588219 : Blo 1148636 2588219 := bstep (se 1 (by rfl) ⟨1941164, by rfl⟩ : syracuseStep 2588219 = 3882329) B3882329
theorem B2915959 : Blo 1148636 2915959 := bstep (se 1 (by rfl) ⟨2186969, by rfl⟩ : syracuseStep 2915959 = 4373939) B4373939
theorem B2588345 : Blo 1148636 2588345 := bstep (se 2 (by rfl) ⟨970629, by rfl⟩ : syracuseStep 2588345 = 1941259) B1941259
theorem B6553345 : Blo 1148636 6553345 := bstep (se 2 (by rfl) ⟨2457504, by rfl⟩ : syracuseStep 6553345 = 4915009) B4915009
theorem B1474363 : Blo 1148636 1474363 := bstep (se 1 (by rfl) ⟨1105772, by rfl⟩ : syracuseStep 1474363 = 2211545) B2211545
theorem B3276605 : Blo 1148636 3276605 := bstep (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) B1228727
theorem B4915079 : Blo 1148636 4915079 := bstep (se 1 (by rfl) ⟨3686309, by rfl⟩ : syracuseStep 4915079 = 7372619) B7372619
theorem B37355417 : Blo 1148636 37355417 := bstep (se 2 (by rfl) ⟨14008281, by rfl⟩ : syracuseStep 37355417 = 28016563) B28016563
theorem B9830429 : Blo 1148636 9830429 := bstep (se 3 (by rfl) ⟨1843205, by rfl⟩ : syracuseStep 9830429 = 3686411) B3686411
theorem B15728717 : Blo 1148636 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B5832971 : Blo 1148636 5832971 := bstep (se 1 (by rfl) ⟨4374728, by rfl⟩ : syracuseStep 5832971 = 8749457) B8749457
theorem B53051723 : Blo 1148636 53051723 := bstep (se 1 (by rfl) ⟨39788792, by rfl⟩ : syracuseStep 53051723 = 79577585) B79577585
theorem B8290849 : Blo 1148636 8290849 := bstep (se 2 (by rfl) ⟨3109068, by rfl⟩ : syracuseStep 8290849 = 6218137) B6218137
theorem B2589281 : Blo 1148636 2589281 := bstep (se 2 (by rfl) ⟨970980, by rfl⟩ : syracuseStep 2589281 = 1941961) B1941961
theorem B1639111 : Blo 1148636 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B3277675 : Blo 1148636 3277675 := bstep (se 1 (by rfl) ⟨2458256, by rfl⟩ : syracuseStep 3277675 = 4916513) B4916513
theorem B2589623 : Blo 1148636 2589623 := bstep (se 1 (by rfl) ⟨1942217, by rfl⟩ : syracuseStep 2589623 = 3884435) B3884435
theorem B3277903 : Blo 1148636 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B33227981 : Blo 1148636 33227981 := bstep (se 3 (by rfl) ⟨6230246, by rfl⟩ : syracuseStep 33227981 = 12460493) B12460493
theorem B2590217 : Blo 1148636 2590217 := bstep (se 2 (by rfl) ⟨971331, by rfl⟩ : syracuseStep 2590217 = 1942663) B1942663
theorem B3114521 : Blo 1148636 3114521 := bstep (se 2 (by rfl) ⟨1167945, by rfl⟩ : syracuseStep 3114521 = 2335891) B2335891
theorem B5834429 : Blo 1148636 5834429 := bstep (se 3 (by rfl) ⟨1093955, by rfl⟩ : syracuseStep 5834429 = 2187911) B2187911
theorem B1148711 : Blo 1148636 1148711 := bstep (se 1 (by rfl) ⟨861533, by rfl⟩ : syracuseStep 1148711 = 1723067) B1723067
theorem B8750915 : Blo 1148636 8750915 := bstep (se 1 (by rfl) ⟨6563186, by rfl⟩ : syracuseStep 8750915 = 13126373) B13126373
theorem B1148751 : Blo 1148636 1148751 := bstep (se 1 (by rfl) ⟨861563, by rfl⟩ : syracuseStep 1148751 = 1723127) B1723127
theorem B1148767 : Blo 1148636 1148767 := bstep (se 1 (by rfl) ⟨861575, by rfl⟩ : syracuseStep 1148767 = 1723151) B1723151
theorem B306644831 : Blo 1148636 306644831 := bstep (se 1 (by rfl) ⟨229983623, by rfl⟩ : syracuseStep 306644831 = 459967247) B459967247
theorem B2590559 : Blo 1148636 2590559 := bstep (se 1 (by rfl) ⟨1942919, by rfl⟩ : syracuseStep 2590559 = 3885839) B3885839
theorem B5834591 : Blo 1148636 5834591 := bstep (se 1 (by rfl) ⟨4375943, by rfl⟩ : syracuseStep 5834591 = 8751887) B8751887
theorem B1148795 : Blo 1148636 1148795 := bstep (se 1 (by rfl) ⟨861596, by rfl⟩ : syracuseStep 1148795 = 1723193) B1723193
theorem B1148847 : Blo 1148636 1148847 := bstep (se 1 (by rfl) ⟨861635, by rfl⟩ : syracuseStep 1148847 = 1723271) B1723271
theorem B1148871 : Blo 1148636 1148871 := bstep (se 1 (by rfl) ⟨861653, by rfl⟩ : syracuseStep 1148871 = 1723307) B1723307
theorem B1148891 : Blo 1148636 1148891 := bstep (se 1 (by rfl) ⟨861668, by rfl⟩ : syracuseStep 1148891 = 1723337) B1723337
theorem B2590739 : Blo 1148636 2590739 := bstep (se 1 (by rfl) ⟨1943054, by rfl⟩ : syracuseStep 2590739 = 3886109) B3886109
theorem B1148967 : Blo 1148636 1148967 := bstep (se 1 (by rfl) ⟨861725, by rfl⟩ : syracuseStep 1148967 = 1723451) B1723451
theorem B1149007 : Blo 1148636 1149007 := bstep (se 1 (by rfl) ⟨861755, by rfl⟩ : syracuseStep 1149007 = 1723511) B1723511
theorem B1149023 : Blo 1148636 1149023 := bstep (se 1 (by rfl) ⟨861767, by rfl⟩ : syracuseStep 1149023 = 1723535) B1723535
theorem B1149051 : Blo 1148636 1149051 := bstep (se 1 (by rfl) ⟨861788, by rfl⟩ : syracuseStep 1149051 = 1723577) B1723577
theorem B4491421 : Blo 1148636 4491421 := bstep (se 3 (by rfl) ⟨842141, by rfl⟩ : syracuseStep 4491421 = 1684283) B1684283
theorem B1149103 : Blo 1148636 1149103 := bstep (se 1 (by rfl) ⟨861827, by rfl⟩ : syracuseStep 1149103 = 1723655) B1723655
theorem B1149127 : Blo 1148636 1149127 := bstep (se 1 (by rfl) ⟨861845, by rfl⟩ : syracuseStep 1149127 = 1723691) B1723691
theorem B1149147 : Blo 1148636 1149147 := bstep (se 1 (by rfl) ⟨861860, by rfl⟩ : syracuseStep 1149147 = 1723721) B1723721
theorem B8292581 : Blo 1148636 8292581 := bstep (se 4 (by rfl) ⟨777429, by rfl⟩ : syracuseStep 8292581 = 1554859) B1554859
theorem B1149223 : Blo 1148636 1149223 := bstep (se 1 (by rfl) ⟨861917, by rfl⟩ : syracuseStep 1149223 = 1723835) B1723835
theorem B1149263 : Blo 1148636 1149263 := bstep (se 1 (by rfl) ⟨861947, by rfl⟩ : syracuseStep 1149263 = 1723895) B1723895
theorem B1149279 : Blo 1148636 1149279 := bstep (se 1 (by rfl) ⟨861959, by rfl⟩ : syracuseStep 1149279 = 1723919) B1723919
theorem B2591081 : Blo 1148636 2591081 := bstep (se 2 (by rfl) ⟨971655, by rfl⟩ : syracuseStep 2591081 = 1943311) B1943311
theorem B1149307 : Blo 1148636 1149307 := bstep (se 1 (by rfl) ⟨861980, by rfl⟩ : syracuseStep 1149307 = 1723961) B1723961
theorem B3148157 : Blo 1148636 3148157 := bstep (se 3 (by rfl) ⟨590279, by rfl⟩ : syracuseStep 3148157 = 1180559) B1180559
theorem B1149359 : Blo 1148636 1149359 := bstep (se 1 (by rfl) ⟨862019, by rfl⟩ : syracuseStep 1149359 = 1724039) B1724039
theorem B1149383 : Blo 1148636 1149383 := bstep (se 1 (by rfl) ⟨862037, by rfl⟩ : syracuseStep 1149383 = 1724075) B1724075
theorem B1149403 : Blo 1148636 1149403 := bstep (se 1 (by rfl) ⟨862052, by rfl⟩ : syracuseStep 1149403 = 1724105) B1724105
theorem B16583201 : Blo 1148636 16583201 := bstep (se 2 (by rfl) ⟨6218700, by rfl⟩ : syracuseStep 16583201 = 12437401) B12437401
theorem B1149479 : Blo 1148636 1149479 := bstep (se 1 (by rfl) ⟨862109, by rfl⟩ : syracuseStep 1149479 = 1724219) B1724219
theorem B1149519 : Blo 1148636 1149519 := bstep (se 1 (by rfl) ⟨862139, by rfl⟩ : syracuseStep 1149519 = 1724279) B1724279
theorem B1149535 : Blo 1148636 1149535 := bstep (se 1 (by rfl) ⟨862151, by rfl⟩ : syracuseStep 1149535 = 1724303) B1724303
theorem B1149563 : Blo 1148636 1149563 := bstep (se 1 (by rfl) ⟨862172, by rfl⟩ : syracuseStep 1149563 = 1724345) B1724345
theorem B1149615 : Blo 1148636 1149615 := bstep (se 1 (by rfl) ⟨862211, by rfl⟩ : syracuseStep 1149615 = 1724423) B1724423
theorem B1149639 : Blo 1148636 1149639 := bstep (se 1 (by rfl) ⟨862229, by rfl⟩ : syracuseStep 1149639 = 1724459) B1724459
theorem B1149659 : Blo 1148636 1149659 := bstep (se 1 (by rfl) ⟨862244, by rfl⟩ : syracuseStep 1149659 = 1724489) B1724489
theorem B5901059 : Blo 1148636 5901059 := bstep (se 1 (by rfl) ⟨4425794, by rfl⟩ : syracuseStep 5901059 = 8851589) B8851589
theorem B1149735 : Blo 1148636 1149735 := bstep (se 1 (by rfl) ⟨862301, by rfl⟩ : syracuseStep 1149735 = 1724603) B1724603
theorem B1149775 : Blo 1148636 1149775 := bstep (se 1 (by rfl) ⟨862331, by rfl⟩ : syracuseStep 1149775 = 1724663) B1724663
theorem B1149791 : Blo 1148636 1149791 := bstep (se 1 (by rfl) ⟨862343, by rfl⟩ : syracuseStep 1149791 = 1724687) B1724687
theorem B1149819 : Blo 1148636 1149819 := bstep (se 1 (by rfl) ⟨862364, by rfl⟩ : syracuseStep 1149819 = 1724729) B1724729
theorem B1149871 : Blo 1148636 1149871 := bstep (se 1 (by rfl) ⟨862403, by rfl⟩ : syracuseStep 1149871 = 1724807) B1724807
theorem B2591675 : Blo 1148636 2591675 := bstep (se 1 (by rfl) ⟨1943756, by rfl⟩ : syracuseStep 2591675 = 3887513) B3887513
theorem B1149895 : Blo 1148636 1149895 := bstep (se 1 (by rfl) ⟨862421, by rfl⟩ : syracuseStep 1149895 = 1724843) B1724843
theorem B1149915 : Blo 1148636 1149915 := bstep (se 1 (by rfl) ⟨862436, by rfl⟩ : syracuseStep 1149915 = 1724873) B1724873
theorem B1149991 : Blo 1148636 1149991 := bstep (se 1 (by rfl) ⟨862493, by rfl⟩ : syracuseStep 1149991 = 1724987) B1724987
theorem B4361273 : Blo 1148636 4361273 := bstep (se 2 (by rfl) ⟨1635477, by rfl⟩ : syracuseStep 4361273 = 3270955) B3270955
theorem B2591801 : Blo 1148636 2591801 := bstep (se 2 (by rfl) ⟨971925, by rfl⟩ : syracuseStep 2591801 = 1943851) B1943851
theorem B1150031 : Blo 1148636 1150031 := bstep (se 1 (by rfl) ⟨862523, by rfl⟩ : syracuseStep 1150031 = 1725047) B1725047
theorem B1150047 : Blo 1148636 1150047 := bstep (se 1 (by rfl) ⟨862535, by rfl⟩ : syracuseStep 1150047 = 1725071) B1725071
theorem B15961205 : Blo 1148636 15961205 := bstep (se 5 (by rfl) ⟨748181, by rfl⟩ : syracuseStep 15961205 = 1496363) B1496363
theorem B1150075 : Blo 1148636 1150075 := bstep (se 1 (by rfl) ⟨862556, by rfl⟩ : syracuseStep 1150075 = 1725113) B1725113
theorem B1150127 : Blo 1148636 1150127 := bstep (se 1 (by rfl) ⟨862595, by rfl⟩ : syracuseStep 1150127 = 1725191) B1725191
theorem B27954371 : Blo 1148636 27954371 := bstep (se 1 (by rfl) ⟨20965778, by rfl⟩ : syracuseStep 27954371 = 41931557) B41931557
theorem B1150151 : Blo 1148636 1150151 := bstep (se 1 (by rfl) ⟨862613, by rfl⟩ : syracuseStep 1150151 = 1725227) B1725227
theorem B1150171 : Blo 1148636 1150171 := bstep (se 1 (by rfl) ⟨862628, by rfl⟩ : syracuseStep 1150171 = 1725257) B1725257
theorem B1150247 : Blo 1148636 1150247 := bstep (se 1 (by rfl) ⟨862685, by rfl⟩ : syracuseStep 1150247 = 1725371) B1725371
theorem B1150287 : Blo 1148636 1150287 := bstep (se 1 (by rfl) ⟨862715, by rfl⟩ : syracuseStep 1150287 = 1725431) B1725431
theorem B1150303 : Blo 1148636 1150303 := bstep (se 1 (by rfl) ⟨862727, by rfl⟩ : syracuseStep 1150303 = 1725455) B1725455
theorem B1150331 : Blo 1148636 1150331 := bstep (se 1 (by rfl) ⟨862748, by rfl⟩ : syracuseStep 1150331 = 1725497) B1725497
theorem B2592143 : Blo 1148636 2592143 := bstep (se 1 (by rfl) ⟨1944107, by rfl⟩ : syracuseStep 2592143 = 3888215) B3888215
theorem B1150383 : Blo 1148636 1150383 := bstep (se 1 (by rfl) ⟨862787, by rfl⟩ : syracuseStep 1150383 = 1725575) B1725575
theorem B1150407 : Blo 1148636 1150407 := bstep (se 1 (by rfl) ⟨862805, by rfl⟩ : syracuseStep 1150407 = 1725611) B1725611
theorem B1150427 : Blo 1148636 1150427 := bstep (se 1 (by rfl) ⟨862820, by rfl⟩ : syracuseStep 1150427 = 1725641) B1725641
theorem B3280409 : Blo 1148636 3280409 := bstep (se 2 (by rfl) ⟨1230153, by rfl⟩ : syracuseStep 3280409 = 2460307) B2460307
theorem B1150503 : Blo 1148636 1150503 := bstep (se 1 (by rfl) ⟨862877, by rfl⟩ : syracuseStep 1150503 = 1725755) B1725755
theorem B1150543 : Blo 1148636 1150543 := bstep (se 1 (by rfl) ⟨862907, by rfl⟩ : syracuseStep 1150543 = 1725815) B1725815
theorem B1150559 : Blo 1148636 1150559 := bstep (se 1 (by rfl) ⟨862919, by rfl⟩ : syracuseStep 1150559 = 1725839) B1725839
theorem B1150587 : Blo 1148636 1150587 := bstep (se 1 (by rfl) ⟨862940, by rfl⟩ : syracuseStep 1150587 = 1725881) B1725881
theorem B4427399 : Blo 1148636 4427399 := bstep (se 1 (by rfl) ⟨3320549, by rfl⟩ : syracuseStep 4427399 = 6641099) B6641099
theorem B1150639 : Blo 1148636 1150639 := bstep (se 1 (by rfl) ⟨862979, by rfl⟩ : syracuseStep 1150639 = 1725959) B1725959
theorem B1150663 : Blo 1148636 1150663 := bstep (se 1 (by rfl) ⟨862997, by rfl⟩ : syracuseStep 1150663 = 1725995) B1725995
theorem B2592467 : Blo 1148636 2592467 := bstep (se 1 (by rfl) ⟨1944350, by rfl⟩ : syracuseStep 2592467 = 3888701) B3888701
theorem B1150683 : Blo 1148636 1150683 := bstep (se 1 (by rfl) ⟨863012, by rfl⟩ : syracuseStep 1150683 = 1726025) B1726025
theorem B6295261 : Blo 1148636 6295261 := bstep (se 3 (by rfl) ⟨1180361, by rfl⟩ : syracuseStep 6295261 = 2360723) B2360723
theorem B1150759 : Blo 1148636 1150759 := bstep (se 1 (by rfl) ⟨863069, by rfl⟩ : syracuseStep 1150759 = 1726139) B1726139
theorem B1150799 : Blo 1148636 1150799 := bstep (se 1 (by rfl) ⟨863099, by rfl⟩ : syracuseStep 1150799 = 1726199) B1726199
theorem B1150815 : Blo 1148636 1150815 := bstep (se 1 (by rfl) ⟨863111, by rfl⟩ : syracuseStep 1150815 = 1726223) B1726223
theorem B2330473 : Blo 1148636 2330473 := bstep (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) B1747855
theorem B1150843 : Blo 1148636 1150843 := bstep (se 1 (by rfl) ⟨863132, by rfl⟩ : syracuseStep 1150843 = 1726265) B1726265
theorem B1150895 : Blo 1148636 1150895 := bstep (se 1 (by rfl) ⟨863171, by rfl⟩ : syracuseStep 1150895 = 1726343) B1726343
theorem B1150919 : Blo 1148636 1150919 := bstep (se 1 (by rfl) ⟨863189, by rfl⟩ : syracuseStep 1150919 = 1726379) B1726379
theorem B1150939 : Blo 1148636 1150939 := bstep (se 1 (by rfl) ⟨863204, by rfl⟩ : syracuseStep 1150939 = 1726409) B1726409
theorem B1151015 : Blo 1148636 1151015 := bstep (se 1 (by rfl) ⟨863261, by rfl⟩ : syracuseStep 1151015 = 1726523) B1726523
theorem B1151055 : Blo 1148636 1151055 := bstep (se 1 (by rfl) ⟨863291, by rfl⟩ : syracuseStep 1151055 = 1726583) B1726583
theorem B1151071 : Blo 1148636 1151071 := bstep (se 1 (by rfl) ⟨863303, by rfl⟩ : syracuseStep 1151071 = 1726607) B1726607
theorem B1151099 : Blo 1148636 1151099 := bstep (se 1 (by rfl) ⟨863324, by rfl⟩ : syracuseStep 1151099 = 1726649) B1726649
theorem B4919453 : Blo 1148636 4919453 := bstep (se 3 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 4919453 = 1844795) B1844795
theorem B1151151 : Blo 1148636 1151151 := bstep (se 1 (by rfl) ⟨863363, by rfl⟩ : syracuseStep 1151151 = 1726727) B1726727
theorem B1151175 : Blo 1148636 1151175 := bstep (se 1 (by rfl) ⟨863381, by rfl⟩ : syracuseStep 1151175 = 1726763) B1726763
theorem B1151195 : Blo 1148636 1151195 := bstep (se 1 (by rfl) ⟨863396, by rfl⟩ : syracuseStep 1151195 = 1726793) B1726793
theorem B1151271 : Blo 1148636 1151271 := bstep (se 1 (by rfl) ⟨863453, by rfl⟩ : syracuseStep 1151271 = 1726907) B1726907
theorem B1151311 : Blo 1148636 1151311 := bstep (se 1 (by rfl) ⟨863483, by rfl⟩ : syracuseStep 1151311 = 1726967) B1726967
theorem B2330975 : Blo 1148636 2330975 := bstep (se 1 (by rfl) ⟨1748231, by rfl⟩ : syracuseStep 2330975 = 3496463) B3496463
theorem B1151327 : Blo 1148636 1151327 := bstep (se 1 (by rfl) ⟨863495, by rfl⟩ : syracuseStep 1151327 = 1726991) B1726991
theorem B1151355 : Blo 1148636 1151355 := bstep (se 1 (by rfl) ⟨863516, by rfl⟩ : syracuseStep 1151355 = 1727033) B1727033
theorem B2331023 : Blo 1148636 2331023 := bstep (se 1 (by rfl) ⟨1748267, by rfl⟩ : syracuseStep 2331023 = 3496535) B3496535
theorem B1151407 : Blo 1148636 1151407 := bstep (se 1 (by rfl) ⟨863555, by rfl⟩ : syracuseStep 1151407 = 1727111) B1727111
theorem B1151431 : Blo 1148636 1151431 := bstep (se 1 (by rfl) ⟨863573, by rfl⟩ : syracuseStep 1151431 = 1727147) B1727147
theorem B1151451 : Blo 1148636 1151451 := bstep (se 1 (by rfl) ⟨863588, by rfl⟩ : syracuseStep 1151451 = 1727177) B1727177
theorem B4362761 : Blo 1148636 4362761 := bstep (se 2 (by rfl) ⟨1636035, by rfl⟩ : syracuseStep 4362761 = 3272071) B3272071
theorem B1151527 : Blo 1148636 1151527 := bstep (se 1 (by rfl) ⟨863645, by rfl⟩ : syracuseStep 1151527 = 1727291) B1727291
theorem B1151567 : Blo 1148636 1151567 := bstep (se 1 (by rfl) ⟨863675, by rfl⟩ : syracuseStep 1151567 = 1727351) B1727351
theorem B1151583 : Blo 1148636 1151583 := bstep (se 1 (by rfl) ⟨863687, by rfl⟩ : syracuseStep 1151583 = 1727375) B1727375
theorem B1151611 : Blo 1148636 1151611 := bstep (se 1 (by rfl) ⟨863708, by rfl⟩ : syracuseStep 1151611 = 1727417) B1727417
theorem B2593403 : Blo 1148636 2593403 := bstep (se 1 (by rfl) ⟨1945052, by rfl⟩ : syracuseStep 2593403 = 3890105) B3890105
theorem B9835181 : Blo 1148636 9835181 := bstep (se 3 (by rfl) ⟨1844096, by rfl⟩ : syracuseStep 9835181 = 3688193) B3688193
theorem B1151663 : Blo 1148636 1151663 := bstep (se 1 (by rfl) ⟨863747, by rfl⟩ : syracuseStep 1151663 = 1727495) B1727495
theorem B1151687 : Blo 1148636 1151687 := bstep (se 1 (by rfl) ⟨863765, by rfl⟩ : syracuseStep 1151687 = 1727531) B1727531
theorem B1151707 : Blo 1148636 1151707 := bstep (se 1 (by rfl) ⟨863780, by rfl⟩ : syracuseStep 1151707 = 1727561) B1727561
theorem B1151783 : Blo 1148636 1151783 := bstep (se 1 (by rfl) ⟨863837, by rfl⟩ : syracuseStep 1151783 = 1727675) B1727675
theorem B1151823 : Blo 1148636 1151823 := bstep (se 1 (by rfl) ⟨863867, by rfl⟩ : syracuseStep 1151823 = 1727735) B1727735
theorem B1151839 : Blo 1148636 1151839 := bstep (se 1 (by rfl) ⟨863879, by rfl⟩ : syracuseStep 1151839 = 1727759) B1727759
theorem B1151867 : Blo 1148636 1151867 := bstep (se 1 (by rfl) ⟨863900, by rfl⟩ : syracuseStep 1151867 = 1727801) B1727801
theorem B1151919 : Blo 1148636 1151919 := bstep (se 1 (by rfl) ⟨863939, by rfl⟩ : syracuseStep 1151919 = 1727879) B1727879
theorem B1151943 : Blo 1148636 1151943 := bstep (se 1 (by rfl) ⟨863957, by rfl⟩ : syracuseStep 1151943 = 1727915) B1727915
theorem B1151963 : Blo 1148636 1151963 := bstep (se 1 (by rfl) ⟨863972, by rfl⟩ : syracuseStep 1151963 = 1727945) B1727945
theorem B1152039 : Blo 1148636 1152039 := bstep (se 1 (by rfl) ⟨864029, by rfl⟩ : syracuseStep 1152039 = 1728059) B1728059
theorem B1840207 : Blo 1148636 1840207 := bstep (se 1 (by rfl) ⟨1380155, by rfl⟩ : syracuseStep 1840207 = 2760311) B2760311
theorem B1152079 : Blo 1148636 1152079 := bstep (se 1 (by rfl) ⟨864059, by rfl⟩ : syracuseStep 1152079 = 1728119) B1728119
theorem B1152095 : Blo 1148636 1152095 := bstep (se 1 (by rfl) ⟨864071, by rfl⟩ : syracuseStep 1152095 = 1728143) B1728143
theorem B1152123 : Blo 1148636 1152123 := bstep (se 1 (by rfl) ⟨864092, by rfl⟩ : syracuseStep 1152123 = 1728185) B1728185
theorem B1152175 : Blo 1148636 1152175 := bstep (se 1 (by rfl) ⟨864131, by rfl⟩ : syracuseStep 1152175 = 1728263) B1728263
theorem B1152199 : Blo 1148636 1152199 := bstep (se 1 (by rfl) ⟨864149, by rfl⟩ : syracuseStep 1152199 = 1728299) B1728299
theorem B1152219 : Blo 1148636 1152219 := bstep (se 1 (by rfl) ⟨864164, by rfl⟩ : syracuseStep 1152219 = 1728329) B1728329
theorem B8295695 : Blo 1148636 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B1152295 : Blo 1148636 1152295 := bstep (se 1 (by rfl) ⟨864221, by rfl⟩ : syracuseStep 1152295 = 1728443) B1728443
theorem B1152335 : Blo 1148636 1152335 := bstep (se 1 (by rfl) ⟨864251, by rfl⟩ : syracuseStep 1152335 = 1728503) B1728503
theorem B1152351 : Blo 1148636 1152351 := bstep (se 1 (by rfl) ⟨864263, by rfl⟩ : syracuseStep 1152351 = 1728527) B1728527
theorem B1152379 : Blo 1148636 1152379 := bstep (se 1 (by rfl) ⟨864284, by rfl⟩ : syracuseStep 1152379 = 1728569) B1728569
theorem B1938863 : Blo 1148636 1938863 := bstep (se 1 (by rfl) ⟨1454147, by rfl⟩ : syracuseStep 1938863 = 2908295) B2908295
theorem B1152431 : Blo 1148636 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B1152455 : Blo 1148636 1152455 := bstep (se 1 (by rfl) ⟨864341, by rfl⟩ : syracuseStep 1152455 = 1728683) B1728683
theorem B6559177 : Blo 1148636 6559177 := bstep (se 2 (by rfl) ⟨2459691, by rfl⟩ : syracuseStep 6559177 = 4919383) B4919383
theorem B1152475 : Blo 1148636 1152475 := bstep (se 1 (by rfl) ⟨864356, by rfl⟩ : syracuseStep 1152475 = 1728713) B1728713
theorem B4920871 : Blo 1148636 4920871 := bstep (se 1 (by rfl) ⟨3690653, by rfl⟩ : syracuseStep 4920871 = 7381307) B7381307
theorem B1152551 : Blo 1148636 1152551 := bstep (se 1 (by rfl) ⟨864413, by rfl⟩ : syracuseStep 1152551 = 1728827) B1728827
theorem B1152591 : Blo 1148636 1152591 := bstep (se 1 (by rfl) ⟨864443, by rfl⟩ : syracuseStep 1152591 = 1728887) B1728887
theorem B1152607 : Blo 1148636 1152607 := bstep (se 1 (by rfl) ⟨864455, by rfl⟩ : syracuseStep 1152607 = 1728911) B1728911
theorem B1152635 : Blo 1148636 1152635 := bstep (se 1 (by rfl) ⟨864476, by rfl⟩ : syracuseStep 1152635 = 1728953) B1728953
theorem B4363915 : Blo 1148636 4363915 := bstep (se 1 (by rfl) ⟨3272936, by rfl⟩ : syracuseStep 4363915 = 6545873) B6545873
theorem B9344659 : Blo 1148636 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B1939295 : Blo 1148636 1939295 := bstep (se 1 (by rfl) ⟨1454471, by rfl⟩ : syracuseStep 1939295 = 2908943) B2908943
theorem B1382251 : Blo 1148636 1382251 := bstep (se 1 (by rfl) ⟨1036688, by rfl⟩ : syracuseStep 1382251 = 2073377) B2073377
theorem B4364219 : Blo 1148636 4364219 := bstep (se 1 (by rfl) ⟨3273164, by rfl⟩ : syracuseStep 4364219 = 6546329) B6546329
theorem B2627603 : Blo 1148636 2627603 := bstep (se 1 (by rfl) ⟨1970702, by rfl⟩ : syracuseStep 2627603 = 3941405) B3941405
theorem B2398331 : Blo 1148636 2398331 := bstep (se 1 (by rfl) ⟨1798748, by rfl⟩ : syracuseStep 2398331 = 3597497) B3597497
theorem B31529249 : Blo 1148636 31529249 := bstep (se 2 (by rfl) ⟨11823468, by rfl⟩ : syracuseStep 31529249 = 23646937) B23646937
theorem B1939855 : Blo 1148636 1939855 := bstep (se 1 (by rfl) ⟨1454891, by rfl⟩ : syracuseStep 1939855 = 2909783) B2909783
theorem B2628425 : Blo 1148636 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B4660087 : Blo 1148636 4660087 := bstep (se 1 (by rfl) ⟨3495065, by rfl⟩ : syracuseStep 4660087 = 6990131) B6990131
theorem B2071559 : Blo 1148636 2071559 := bstep (se 1 (by rfl) ⟨1553669, by rfl⟩ : syracuseStep 2071559 = 3107339) B3107339
theorem B1940537 : Blo 1148636 1940537 := bstep (se 2 (by rfl) ⟨727701, by rfl⟩ : syracuseStep 1940537 = 1455403) B1455403
theorem B4988099 : Blo 1148636 4988099 := bstep (se 1 (by rfl) ⟨3741074, by rfl⟩ : syracuseStep 4988099 = 7482149) B7482149
theorem B12459203 : Blo 1148636 12459203 := bstep (se 1 (by rfl) ⟨9344402, by rfl⟩ : syracuseStep 12459203 = 18688805) B18688805
theorem B2334025 : Blo 1148636 2334025 := bstep (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) B1750519
theorem B1842527 : Blo 1148636 1842527 := bstep (se 1 (by rfl) ⟨1381895, by rfl⟩ : syracuseStep 1842527 = 2763791) B2763791
theorem B1842745 : Blo 1148636 1842745 := bstep (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) B1382059
theorem B2760331 : Blo 1148636 2760331 := bstep (se 1 (by rfl) ⟨2070248, by rfl⟩ : syracuseStep 2760331 = 4140497) B4140497
theorem B9838219 : Blo 1148636 9838219 := bstep (se 1 (by rfl) ⟨7378664, by rfl⟩ : syracuseStep 9838219 = 14757329) B14757329
theorem B1941239 : Blo 1148636 1941239 := bstep (se 1 (by rfl) ⟨1455929, by rfl⟩ : syracuseStep 1941239 = 2911859) B2911859
theorem B84188929 : Blo 1148636 84188929 := bstep (se 2 (by rfl) ⟨31570848, by rfl⟩ : syracuseStep 84188929 = 63141697) B63141697
theorem B5611373 : Blo 1148636 5611373 := bstep (se 3 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 5611373 = 2104265) B2104265
theorem B19898297 : Blo 1148636 19898297 := bstep (se 2 (by rfl) ⟨7461861, by rfl⟩ : syracuseStep 19898297 = 14923723) B14923723
theorem B2334739 : Blo 1148636 2334739 := bstep (se 1 (by rfl) ⟨1751054, by rfl⟩ : syracuseStep 2334739 = 3502109) B3502109
theorem B1941583 : Blo 1148636 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B1941833 : Blo 1148636 1941833 := bstep (se 2 (by rfl) ⟨728187, by rfl⟩ : syracuseStep 1941833 = 1456375) B1456375
theorem B1942265 : Blo 1148636 1942265 := bstep (se 2 (by rfl) ⟨728349, by rfl⟩ : syracuseStep 1942265 = 1456699) B1456699
theorem B1942447 : Blo 1148636 1942447 := bstep (se 1 (by rfl) ⟨1456835, by rfl⟩ : syracuseStep 1942447 = 2913671) B2913671
theorem B1942535 : Blo 1148636 1942535 := bstep (se 1 (by rfl) ⟨1456901, by rfl⟩ : syracuseStep 1942535 = 2913803) B2913803
theorem B1942879 : Blo 1148636 1942879 := bstep (se 1 (by rfl) ⟨1457159, by rfl⟩ : syracuseStep 1942879 = 2914319) B2914319
theorem B1942967 : Blo 1148636 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B6301223 : Blo 1148636 6301223 := bstep (se 1 (by rfl) ⟨4725917, by rfl⟩ : syracuseStep 6301223 = 9451835) B9451835
theorem B7382765 : Blo 1148636 7382765 := bstep (se 3 (by rfl) ⟨1384268, by rfl⟩ : syracuseStep 7382765 = 2768537) B2768537
theorem B2762657 : Blo 1148636 2762657 := bstep (se 2 (by rfl) ⟨1035996, by rfl⟩ : syracuseStep 2762657 = 2071993) B2071993
theorem B4368289 : Blo 1148636 4368289 := bstep (se 2 (by rfl) ⟨1638108, by rfl⟩ : syracuseStep 4368289 = 3276217) B3276217
theorem B2074529 : Blo 1148636 2074529 := bstep (se 2 (by rfl) ⟨777948, by rfl⟩ : syracuseStep 2074529 = 1555897) B1555897
theorem B181544921 : Blo 1148636 181544921 := bstep (se 2 (by rfl) ⟨68079345, by rfl⟩ : syracuseStep 181544921 = 136158691) B136158691
theorem B1943561 : Blo 1148636 1943561 := bstep (se 2 (by rfl) ⟨728835, by rfl⟩ : syracuseStep 1943561 = 1457671) B1457671
theorem B1943723 : Blo 1148636 1943723 := bstep (se 1 (by rfl) ⟨1457792, by rfl⟩ : syracuseStep 1943723 = 2915585) B2915585
theorem B44247383 : Blo 1148636 44247383 := bstep (se 1 (by rfl) ⟨33185537, by rfl⟩ : syracuseStep 44247383 = 66371075) B66371075
theorem B1845769 : Blo 1148636 1845769 := bstep (se 2 (by rfl) ⟨692163, by rfl⟩ : syracuseStep 1845769 = 1384327) B1384327
theorem B3877415 : Blo 1148636 3877415 := bstep (se 1 (by rfl) ⟨2908061, by rfl⟩ : syracuseStep 3877415 = 5816123) B5816123
theorem B1944121 : Blo 1148636 1944121 := bstep (se 2 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 1944121 = 1458091) B1458091
theorem B3877523 : Blo 1148636 3877523 := bstep (se 1 (by rfl) ⟨2908142, by rfl⟩ : syracuseStep 3877523 = 5816285) B5816285
theorem B2763463 : Blo 1148636 2763463 := bstep (se 1 (by rfl) ⟨2072597, by rfl⟩ : syracuseStep 2763463 = 4145195) B4145195
theorem B1944263 : Blo 1148636 1944263 := bstep (se 1 (by rfl) ⟨1458197, by rfl⟩ : syracuseStep 1944263 = 2916395) B2916395
theorem B4369247 : Blo 1148636 4369247 := bstep (se 1 (by rfl) ⟨3276935, by rfl⟩ : syracuseStep 4369247 = 6553871) B6553871
theorem B1944425 : Blo 1148636 1944425 := bstep (se 2 (by rfl) ⟨729159, by rfl⟩ : syracuseStep 1944425 = 1458319) B1458319
theorem B3877739 : Blo 1148636 3877739 := bstep (se 1 (by rfl) ⟨2908304, by rfl⟩ : syracuseStep 3877739 = 5816609) B5816609
theorem B3681131 : Blo 1148636 3681131 := bstep (se 1 (by rfl) ⟨2760848, by rfl⟩ : syracuseStep 3681131 = 5521697) B5521697
theorem B4369261 : Blo 1148636 4369261 := bstep (se 3 (by rfl) ⟨819236, by rfl⟩ : syracuseStep 4369261 = 1638473) B1638473
theorem B3877793 : Blo 1148636 3877793 := bstep (se 2 (by rfl) ⟨1454172, by rfl⟩ : syracuseStep 3877793 = 2908345) B2908345
theorem B4369565 : Blo 1148636 4369565 := bstep (se 3 (by rfl) ⟨819293, by rfl⟩ : syracuseStep 4369565 = 1638587) B1638587
theorem B1944823 : Blo 1148636 1944823 := bstep (se 1 (by rfl) ⟨1458617, by rfl⟩ : syracuseStep 1944823 = 2917235) B2917235
theorem B1945019 : Blo 1148636 1945019 := bstep (se 1 (by rfl) ⟨1458764, by rfl⟩ : syracuseStep 1945019 = 2917529) B2917529
theorem B3878387 : Blo 1148636 3878387 := bstep (se 1 (by rfl) ⟨2908790, by rfl⟩ : syracuseStep 3878387 = 5817581) B5817581
theorem B7384715 : Blo 1148636 7384715 := bstep (se 1 (by rfl) ⟨5538536, by rfl⟩ : syracuseStep 7384715 = 11077073) B11077073
theorem B4370219 : Blo 1148636 4370219 := bstep (se 1 (by rfl) ⟨3277664, by rfl⟩ : syracuseStep 4370219 = 6555329) B6555329
theorem B8302445 : Blo 1148636 8302445 := bstep (se 3 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 8302445 = 3113417) B3113417
theorem B3878927 : Blo 1148636 3878927 := bstep (se 1 (by rfl) ⟨2909195, by rfl⟩ : syracuseStep 3878927 = 5818391) B5818391
theorem B1454203 : Blo 1148636 1454203 := bstep (se 1 (by rfl) ⟨1090652, by rfl⟩ : syracuseStep 1454203 = 2181305) B2181305
theorem B1454431 : Blo 1148636 1454431 := bstep (se 1 (by rfl) ⟨1090823, by rfl⟩ : syracuseStep 1454431 = 2181647) B2181647
theorem B8860033 : Blo 1148636 8860033 := bstep (se 2 (by rfl) ⟨3322512, by rfl⟩ : syracuseStep 8860033 = 6645025) B6645025
theorem B33141251 : Blo 1148636 33141251 := bstep (se 1 (by rfl) ⟨24855938, by rfl⟩ : syracuseStep 33141251 = 49711877) B49711877
theorem B3879521 : Blo 1148636 3879521 := bstep (se 2 (by rfl) ⟨1454820, by rfl⟩ : syracuseStep 3879521 = 2909641) B2909641
theorem B3650237 : Blo 1148636 3650237 := bstep (se 3 (by rfl) ⟨684419, by rfl⟩ : syracuseStep 3650237 = 1368839) B1368839
theorem B8303305 : Blo 1148636 8303305 := bstep (se 2 (by rfl) ⟨3113739, by rfl⟩ : syracuseStep 8303305 = 6227479) B6227479
theorem B14725961 : Blo 1148636 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B1455023 : Blo 1148636 1455023 := bstep (se 1 (by rfl) ⟨1091267, by rfl⟩ : syracuseStep 1455023 = 2182535) B2182535
theorem B13284773 : Blo 1148636 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B14759333 : Blo 1148636 14759333 := bstep (se 4 (by rfl) ⟨1383687, by rfl⟩ : syracuseStep 14759333 = 2767375) B2767375
theorem B4142573 : Blo 1148636 4142573 := bstep (se 3 (by rfl) ⟨776732, by rfl⟩ : syracuseStep 4142573 = 1553465) B1553465
theorem B4372177 : Blo 1148636 4372177 := bstep (se 2 (by rfl) ⟨1639566, by rfl⟩ : syracuseStep 4372177 = 3279133) B3279133
theorem B8730503 : Blo 1148636 8730503 := bstep (se 1 (by rfl) ⟨6547877, by rfl⟩ : syracuseStep 8730503 = 13095755) B13095755
theorem B1292251 : Blo 1148636 1292251 := bstep (se 1 (by rfl) ⟨969188, by rfl⟩ : syracuseStep 1292251 = 1938377) B1938377
theorem B4372481 : Blo 1148636 4372481 := bstep (se 2 (by rfl) ⟨1639680, by rfl⟩ : syracuseStep 4372481 = 3279361) B3279361
theorem B3880979 : Blo 1148636 3880979 := bstep (se 1 (by rfl) ⟨2910734, by rfl⟩ : syracuseStep 3880979 = 5821469) B5821469
theorem B16595077 : Blo 1148636 16595077 := bstep (se 4 (by rfl) ⟨1555788, by rfl⟩ : syracuseStep 16595077 = 3111577) B3111577
theorem B3881303 : Blo 1148636 3881303 := bstep (se 1 (by rfl) ⟨2910977, by rfl⟩ : syracuseStep 3881303 = 5821955) B5821955
theorem B1292719 : Blo 1148636 1292719 := bstep (se 1 (by rfl) ⟨969539, by rfl⟩ : syracuseStep 1292719 = 1939079) B1939079
theorem B4372937 : Blo 1148636 4372937 := bstep (se 2 (by rfl) ⟨1639851, by rfl⟩ : syracuseStep 4372937 = 3279703) B3279703
theorem B15350219 : Blo 1148636 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B2767385 : Blo 1148636 2767385 := bstep (se 2 (by rfl) ⟨1037769, by rfl⟩ : syracuseStep 2767385 = 2075539) B2075539
theorem B22133533 : Blo 1148636 22133533 := bstep (se 3 (by rfl) ⟨4150037, by rfl⟩ : syracuseStep 22133533 = 8300075) B8300075
theorem B14957389 : Blo 1148636 14957389 := bstep (se 3 (by rfl) ⟨2804510, by rfl⟩ : syracuseStep 14957389 = 5609021) B5609021
theorem B1293151 : Blo 1148636 1293151 := bstep (se 1 (by rfl) ⟨969863, by rfl⟩ : syracuseStep 1293151 = 1939727) B1939727
theorem B8403857 : Blo 1148636 8403857 := bstep (se 2 (by rfl) ⟨3151446, by rfl⟩ : syracuseStep 8403857 = 6302893) B6302893
theorem B4373423 : Blo 1148636 4373423 := bstep (se 1 (by rfl) ⟨3280067, by rfl⟩ : syracuseStep 4373423 = 6560135) B6560135
theorem B1293511 : Blo 1148636 1293511 := bstep (se 1 (by rfl) ⟨970133, by rfl⟩ : syracuseStep 1293511 = 1940267) B1940267
theorem B6733181 : Blo 1148636 6733181 := bstep (se 3 (by rfl) ⟨1262471, by rfl⟩ : syracuseStep 6733181 = 2524943) B2524943
theorem B3882383 : Blo 1148636 3882383 := bstep (se 1 (by rfl) ⟨2911787, by rfl⟩ : syracuseStep 3882383 = 5823575) B5823575
theorem B3882707 : Blo 1148636 3882707 := bstep (se 1 (by rfl) ⟨2912030, by rfl⟩ : syracuseStep 3882707 = 5824061) B5824061
theorem B1294375 : Blo 1148636 1294375 := bstep (se 1 (by rfl) ⟨970781, by rfl⟩ : syracuseStep 1294375 = 1941563) B1941563
theorem B4374607 : Blo 1148636 4374607 := bstep (se 1 (by rfl) ⟨3280955, by rfl⟩ : syracuseStep 4374607 = 6561911) B6561911
theorem B4375079 : Blo 1148636 4375079 := bstep (se 1 (by rfl) ⟨3281309, by rfl⟩ : syracuseStep 4375079 = 6562619) B6562619
theorem B22430465 : Blo 1148636 22430465 := bstep (se 2 (by rfl) ⟨8411424, by rfl⟩ : syracuseStep 22430465 = 16822849) B16822849
theorem B3883895 : Blo 1148636 3883895 := bstep (se 1 (by rfl) ⟨2912921, by rfl⟩ : syracuseStep 3883895 = 5825843) B5825843
theorem B3884111 : Blo 1148636 3884111 := bstep (se 1 (by rfl) ⟨2913083, by rfl⟩ : syracuseStep 3884111 = 5826167) B5826167
theorem B4146347 : Blo 1148636 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B28755161 : Blo 1148636 28755161 := bstep (se 2 (by rfl) ⟨10783185, by rfl⟩ : syracuseStep 28755161 = 21566371) B21566371
theorem B5522813 : Blo 1148636 5522813 := bstep (se 3 (by rfl) ⟨1035527, by rfl⟩ : syracuseStep 5522813 = 2071055) B2071055
theorem B5817743 : Blo 1148636 5817743 := bstep (se 1 (by rfl) ⟨4363307, by rfl⟩ : syracuseStep 5817743 = 8726615) B8726615
theorem B3884489 : Blo 1148636 3884489 := bstep (se 2 (by rfl) ⟨1456683, by rfl⟩ : syracuseStep 3884489 = 2913367) B2913367
theorem B4376051 : Blo 1148636 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B1295995 : Blo 1148636 1295995 := bstep (se 1 (by rfl) ⟨971996, by rfl⟩ : syracuseStep 1295995 = 1943993) B1943993
theorem B2180819 : Blo 1148636 2180819 := bstep (se 1 (by rfl) ⟨1635614, by rfl⟩ : syracuseStep 2180819 = 3271229) B3271229
theorem B3884759 : Blo 1148636 3884759 := bstep (se 1 (by rfl) ⟨2913569, by rfl⟩ : syracuseStep 3884759 = 5827139) B5827139
theorem B2180857 : Blo 1148636 2180857 := bstep (se 2 (by rfl) ⟨817821, by rfl⟩ : syracuseStep 2180857 = 1635643) B1635643
theorem B3884975 : Blo 1148636 3884975 := bstep (se 1 (by rfl) ⟨2913731, by rfl⟩ : syracuseStep 3884975 = 5827463) B5827463
theorem B1296463 : Blo 1148636 1296463 := bstep (se 1 (by rfl) ⟨972347, by rfl⟩ : syracuseStep 1296463 = 1944695) B1944695
theorem B8734877 : Blo 1148636 8734877 := bstep (se 3 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 8734877 = 3275579) B3275579
theorem B3688847 : Blo 1148636 3688847 := bstep (se 1 (by rfl) ⟨2766635, by rfl⟩ : syracuseStep 3688847 = 5533271) B5533271
theorem B2181563 : Blo 1148636 2181563 := bstep (se 1 (by rfl) ⟨1636172, by rfl⟩ : syracuseStep 2181563 = 3272345) B3272345
theorem B9325003 : Blo 1148636 9325003 := bstep (se 1 (by rfl) ⟨6993752, by rfl⟩ : syracuseStep 9325003 = 13987505) B13987505
theorem B1722959 : Blo 1148636 1722959 := bstep (se 1 (by rfl) ⟨1292219, by rfl⟩ : syracuseStep 1722959 = 2584439) B2584439
theorem B1723079 : Blo 1148636 1723079 := bstep (se 1 (by rfl) ⟨1292309, by rfl⟩ : syracuseStep 1723079 = 2584619) B2584619
theorem B1723241 : Blo 1148636 1723241 := bstep (se 2 (by rfl) ⟨646215, by rfl⟩ : syracuseStep 1723241 = 1292431) B1292431
theorem B2182049 : Blo 1148636 2182049 := bstep (se 2 (by rfl) ⟨818268, by rfl⟩ : syracuseStep 2182049 = 1636537) B1636537
theorem B1723319 : Blo 1148636 1723319 := bstep (se 1 (by rfl) ⟨1292489, by rfl⟩ : syracuseStep 1723319 = 2584979) B2584979
theorem B1723355 : Blo 1148636 1723355 := bstep (se 1 (by rfl) ⟨1292516, by rfl⟩ : syracuseStep 1723355 = 2585033) B2585033
theorem B2182315 : Blo 1148636 2182315 := bstep (se 1 (by rfl) ⟨1636736, by rfl⟩ : syracuseStep 2182315 = 3273473) B3273473
theorem B5393579 : Blo 1148636 5393579 := bstep (se 1 (by rfl) ⟨4045184, by rfl⟩ : syracuseStep 5393579 = 8090369) B8090369
theorem B1723823 : Blo 1148636 1723823 := bstep (se 1 (by rfl) ⟨1292867, by rfl⟩ : syracuseStep 1723823 = 2585735) B2585735
theorem B5819849 : Blo 1148636 5819849 := bstep (se 2 (by rfl) ⟨2182443, by rfl⟩ : syracuseStep 5819849 = 4364887) B4364887
theorem B2182619 : Blo 1148636 2182619 := bstep (se 1 (by rfl) ⟨1636964, by rfl⟩ : syracuseStep 2182619 = 3273929) B3273929
theorem B1723913 : Blo 1148636 1723913 := bstep (se 2 (by rfl) ⟨646467, by rfl⟩ : syracuseStep 1723913 = 1292935) B1292935
theorem B1723943 : Blo 1148636 1723943 := bstep (se 1 (by rfl) ⟨1292957, by rfl⟩ : syracuseStep 1723943 = 2585915) B2585915
theorem B1724027 : Blo 1148636 1724027 := bstep (se 1 (by rfl) ⟨1293020, by rfl⟩ : syracuseStep 1724027 = 2586041) B2586041
theorem B4148945 : Blo 1148636 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B1724153 : Blo 1148636 1724153 := bstep (se 2 (by rfl) ⟨646557, by rfl⟩ : syracuseStep 1724153 = 1293115) B1293115
theorem B14733089 : Blo 1148636 14733089 := bstep (se 2 (by rfl) ⟨5524908, by rfl⟩ : syracuseStep 14733089 = 11049817) B11049817
theorem B1724255 : Blo 1148636 1724255 := bstep (se 1 (by rfl) ⟨1293191, by rfl⟩ : syracuseStep 1724255 = 2586383) B2586383
theorem B1724267 : Blo 1148636 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B1724495 : Blo 1148636 1724495 := bstep (se 1 (by rfl) ⟨1293371, by rfl⟩ : syracuseStep 1724495 = 2586743) B2586743
theorem B5820497 : Blo 1148636 5820497 := bstep (se 2 (by rfl) ⟨2182686, by rfl⟩ : syracuseStep 5820497 = 4365373) B4365373
theorem B1724615 : Blo 1148636 1724615 := bstep (se 1 (by rfl) ⟨1293461, by rfl⟩ : syracuseStep 1724615 = 2586923) B2586923
theorem B3887351 : Blo 1148636 3887351 := bstep (se 1 (by rfl) ⟨2915513, by rfl⟩ : syracuseStep 3887351 = 5831027) B5831027
theorem B1724777 : Blo 1148636 1724777 := bstep (se 2 (by rfl) ⟨646791, by rfl⟩ : syracuseStep 1724777 = 1293583) B1293583
theorem B1724855 : Blo 1148636 1724855 := bstep (se 1 (by rfl) ⟨1293641, by rfl⟩ : syracuseStep 1724855 = 2587283) B2587283
theorem B1724891 : Blo 1148636 1724891 := bstep (se 1 (by rfl) ⟨1293668, by rfl⟩ : syracuseStep 1724891 = 2587337) B2587337
theorem B2183689 : Blo 1148636 2183689 := bstep (se 2 (by rfl) ⟨818883, by rfl⟩ : syracuseStep 2183689 = 1637767) B1637767
theorem B3887675 : Blo 1148636 3887675 := bstep (se 1 (by rfl) ⟨2915756, by rfl⟩ : syracuseStep 3887675 = 5831513) B5831513
theorem B3691307 : Blo 1148636 3691307 := bstep (se 1 (by rfl) ⟨2768480, by rfl⟩ : syracuseStep 3691307 = 5536961) B5536961
theorem B3887945 : Blo 1148636 3887945 := bstep (se 2 (by rfl) ⟨1457979, by rfl⟩ : syracuseStep 3887945 = 2915959) B2915959
theorem B9327437 : Blo 1148636 9327437 := bstep (se 3 (by rfl) ⟨1748894, by rfl⟩ : syracuseStep 9327437 = 3497789) B3497789
theorem B1725359 : Blo 1148636 1725359 := bstep (se 1 (by rfl) ⟨1294019, by rfl⟩ : syracuseStep 1725359 = 2588039) B2588039
theorem B8737793 : Blo 1148636 8737793 := bstep (se 2 (by rfl) ⟨3276672, by rfl⟩ : syracuseStep 8737793 = 6553345) B6553345
theorem B1725449 : Blo 1148636 1725449 := bstep (se 2 (by rfl) ⟨647043, by rfl⟩ : syracuseStep 1725449 = 1294087) B1294087
theorem B1725479 : Blo 1148636 1725479 := bstep (se 1 (by rfl) ⟨1294109, by rfl⟩ : syracuseStep 1725479 = 2588219) B2588219
theorem B1725563 : Blo 1148636 1725563 := bstep (se 1 (by rfl) ⟨1294172, by rfl⟩ : syracuseStep 1725563 = 2588345) B2588345
theorem B2184403 : Blo 1148636 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B1725689 : Blo 1148636 1725689 := bstep (se 2 (by rfl) ⟨647133, by rfl⟩ : syracuseStep 1725689 = 1294267) B1294267
theorem B4150615 : Blo 1148636 4150615 := bstep (se 1 (by rfl) ⟨3112961, by rfl⟩ : syracuseStep 4150615 = 6225923) B6225923
theorem B1725791 : Blo 1148636 1725791 := bstep (se 1 (by rfl) ⟨1294343, by rfl⟩ : syracuseStep 1725791 = 2588687) B2588687
theorem B1725803 : Blo 1148636 1725803 := bstep (se 1 (by rfl) ⟨1294352, by rfl⟩ : syracuseStep 1725803 = 2588705) B2588705
theorem B7362035 : Blo 1148636 7362035 := bstep (se 1 (by rfl) ⟨5521526, by rfl⟩ : syracuseStep 7362035 = 11043053) B11043053
theorem B1726031 : Blo 1148636 1726031 := bstep (se 1 (by rfl) ⟨1294523, by rfl⟩ : syracuseStep 1726031 = 2589047) B2589047
theorem B1726151 : Blo 1148636 1726151 := bstep (se 1 (by rfl) ⟨1294613, by rfl⟩ : syracuseStep 1726151 = 2589227) B2589227
theorem B1726313 : Blo 1148636 1726313 := bstep (se 2 (by rfl) ⟨647367, by rfl⟩ : syracuseStep 1726313 = 1294735) B1294735
theorem B1726391 : Blo 1148636 1726391 := bstep (se 1 (by rfl) ⟨1294793, by rfl⟩ : syracuseStep 1726391 = 2589587) B2589587
theorem B3889079 : Blo 1148636 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B2185147 : Blo 1148636 2185147 := bstep (se 1 (by rfl) ⟨1638860, by rfl⟩ : syracuseStep 2185147 = 3277721) B3277721
theorem B1726427 : Blo 1148636 1726427 := bstep (se 1 (by rfl) ⟨1294820, by rfl⟩ : syracuseStep 1726427 = 2589641) B2589641
theorem B10508291 : Blo 1148636 10508291 := bstep (se 1 (by rfl) ⟨7881218, by rfl⟩ : syracuseStep 10508291 = 15762437) B15762437
theorem B6215717 : Blo 1148636 6215717 := bstep (se 4 (by rfl) ⟨582723, by rfl⟩ : syracuseStep 6215717 = 1165447) B1165447
theorem B2185633 : Blo 1148636 2185633 := bstep (se 2 (by rfl) ⟨819612, by rfl⟩ : syracuseStep 2185633 = 1639225) B1639225
theorem B1726895 : Blo 1148636 1726895 := bstep (se 1 (by rfl) ⟨1295171, by rfl⟩ : syracuseStep 1726895 = 2590343) B2590343
theorem B1726985 : Blo 1148636 1726985 := bstep (se 2 (by rfl) ⟨647619, by rfl⟩ : syracuseStep 1726985 = 1295239) B1295239
theorem B3889673 : Blo 1148636 3889673 := bstep (se 2 (by rfl) ⟨1458627, by rfl⟩ : syracuseStep 3889673 = 2917255) B2917255
theorem B1727015 : Blo 1148636 1727015 := bstep (se 1 (by rfl) ⟨1295261, by rfl⟩ : syracuseStep 1727015 = 2590523) B2590523
theorem B1727099 : Blo 1148636 1727099 := bstep (se 1 (by rfl) ⟨1295324, by rfl⟩ : syracuseStep 1727099 = 2590649) B2590649
theorem B1727225 : Blo 1148636 1727225 := bstep (se 2 (by rfl) ⟨647709, by rfl⟩ : syracuseStep 1727225 = 1295419) B1295419
theorem B1727327 : Blo 1148636 1727327 := bstep (se 1 (by rfl) ⟨1295495, by rfl⟩ : syracuseStep 1727327 = 2590991) B2590991
theorem B1727339 : Blo 1148636 1727339 := bstep (se 1 (by rfl) ⟨1295504, by rfl⟩ : syracuseStep 1727339 = 2591009) B2591009
theorem B2186203 : Blo 1148636 2186203 := bstep (se 1 (by rfl) ⟨1639652, by rfl⟩ : syracuseStep 2186203 = 3279305) B3279305
theorem B1727567 : Blo 1148636 1727567 := bstep (se 1 (by rfl) ⟨1295675, by rfl⟩ : syracuseStep 1727567 = 2591351) B2591351
theorem B4152491 : Blo 1148636 4152491 := bstep (se 1 (by rfl) ⟨3114368, by rfl⟩ : syracuseStep 4152491 = 6228737) B6228737
theorem B1727687 : Blo 1148636 1727687 := bstep (se 1 (by rfl) ⟨1295765, by rfl⟩ : syracuseStep 1727687 = 2591531) B2591531
theorem B6216907 : Blo 1148636 6216907 := bstep (se 1 (by rfl) ⟨4662680, by rfl⟩ : syracuseStep 6216907 = 9325361) B9325361
theorem B11066615 : Blo 1148636 11066615 := bstep (se 1 (by rfl) ⟨8299961, by rfl⟩ : syracuseStep 11066615 = 16599923) B16599923
theorem B1727849 : Blo 1148636 1727849 := bstep (se 2 (by rfl) ⟨647943, by rfl⟩ : syracuseStep 1727849 = 1295887) B1295887
theorem B2907535 : Blo 1148636 2907535 := bstep (se 1 (by rfl) ⟨2180651, by rfl⟩ : syracuseStep 2907535 = 4361303) B4361303
theorem B1727927 : Blo 1148636 1727927 := bstep (se 1 (by rfl) ⟨1295945, by rfl⟩ : syracuseStep 1727927 = 2591891) B2591891
theorem B1727963 : Blo 1148636 1727963 := bstep (se 1 (by rfl) ⟨1295972, by rfl⟩ : syracuseStep 1727963 = 2591945) B2591945
theorem B6217361 : Blo 1148636 6217361 := bstep (se 2 (by rfl) ⟨2331510, by rfl⟩ : syracuseStep 6217361 = 4663021) B4663021
theorem B2907859 : Blo 1148636 2907859 := bstep (se 1 (by rfl) ⟨2180894, by rfl⟩ : syracuseStep 2907859 = 4361789) B4361789
theorem B1662815 : Blo 1148636 1662815 := bstep (se 1 (by rfl) ⟨1247111, by rfl⟩ : syracuseStep 1662815 = 2494223) B2494223
theorem B1728431 : Blo 1148636 1728431 := bstep (se 1 (by rfl) ⟨1296323, by rfl⟩ : syracuseStep 1728431 = 2592647) B2592647
theorem B1728521 : Blo 1148636 1728521 := bstep (se 2 (by rfl) ⟨648195, by rfl⟩ : syracuseStep 1728521 = 1296391) B1296391
theorem B1728551 : Blo 1148636 1728551 := bstep (se 1 (by rfl) ⟨1296413, by rfl⟩ : syracuseStep 1728551 = 2592827) B2592827
theorem B1728635 : Blo 1148636 1728635 := bstep (se 1 (by rfl) ⟨1296476, by rfl⟩ : syracuseStep 1728635 = 2592953) B2592953
theorem B1728761 : Blo 1148636 1728761 := bstep (se 2 (by rfl) ⟨648285, by rfl⟩ : syracuseStep 1728761 = 1296571) B1296571
theorem B1728863 : Blo 1148636 1728863 := bstep (se 1 (by rfl) ⟨1296647, by rfl⟩ : syracuseStep 1728863 = 2593295) B2593295
theorem B1728875 : Blo 1148636 1728875 := bstep (se 1 (by rfl) ⟨1296656, by rfl⟩ : syracuseStep 1728875 = 2593313) B2593313
theorem B5825033 : Blo 1148636 5825033 := bstep (se 2 (by rfl) ⟨2184387, by rfl⟩ : syracuseStep 5825033 = 4368775) B4368775
theorem B6546055 : Blo 1148636 6546055 := bstep (se 1 (by rfl) ⟨4909541, by rfl⟩ : syracuseStep 6546055 = 9819083) B9819083
theorem B2908811 : Blo 1148636 2908811 := bstep (se 1 (by rfl) ⟨2181608, by rfl⟩ : syracuseStep 2908811 = 4363217) B4363217
theorem B4154105 : Blo 1148636 4154105 := bstep (se 2 (by rfl) ⟨1557789, by rfl⟩ : syracuseStep 4154105 = 3115579) B3115579
theorem B3990379 : Blo 1148636 3990379 := bstep (se 1 (by rfl) ⟨2992784, by rfl⟩ : syracuseStep 3990379 = 5985569) B5985569
theorem B8742167 : Blo 1148636 8742167 := bstep (se 1 (by rfl) ⟨6556625, by rfl⟩ : syracuseStep 8742167 = 13113251) B13113251
theorem B9332111 : Blo 1148636 9332111 := bstep (se 1 (by rfl) ⟨6999083, by rfl⟩ : syracuseStep 9332111 = 13998167) B13998167
theorem B11069075 : Blo 1148636 11069075 := bstep (se 1 (by rfl) ⟨8301806, by rfl⟩ : syracuseStep 11069075 = 16603613) B16603613
theorem B2909945 : Blo 1148636 2909945 := bstep (se 2 (by rfl) ⟨1091229, by rfl⟩ : syracuseStep 2909945 = 2182459) B2182459
theorem B11069227 : Blo 1148636 11069227 := bstep (se 1 (by rfl) ⟨8301920, by rfl⟩ : syracuseStep 11069227 = 16603841) B16603841
theorem B2910127 : Blo 1148636 2910127 := bstep (se 1 (by rfl) ⟨2182595, by rfl⟩ : syracuseStep 2910127 = 4365191) B4365191
theorem B5826491 : Blo 1148636 5826491 := bstep (se 1 (by rfl) ⟨4369868, by rfl⟩ : syracuseStep 5826491 = 8739737) B8739737
theorem B6547513 : Blo 1148636 6547513 := bstep (se 2 (by rfl) ⟨2455317, by rfl⟩ : syracuseStep 6547513 = 4910635) B4910635
theorem B18638981 : Blo 1148636 18638981 := bstep (se 4 (by rfl) ⟨1747404, by rfl⟩ : syracuseStep 18638981 = 3494809) B3494809
theorem B2910593 : Blo 1148636 2910593 := bstep (se 2 (by rfl) ⟨1091472, by rfl⟩ : syracuseStep 2910593 = 2182945) B2182945
theorem B15985031 : Blo 1148636 15985031 := bstep (se 1 (by rfl) ⟨11988773, by rfl⟩ : syracuseStep 15985031 = 23977547) B23977547
theorem B8841737 : Blo 1148636 8841737 := bstep (se 2 (by rfl) ⟨3315651, by rfl⟩ : syracuseStep 8841737 = 6631303) B6631303
theorem B8743625 : Blo 1148636 8743625 := bstep (se 2 (by rfl) ⟨3278859, by rfl⟩ : syracuseStep 8743625 = 6557719) B6557719
theorem B2911049 : Blo 1148636 2911049 := bstep (se 2 (by rfl) ⟨1091643, by rfl⟩ : syracuseStep 2911049 = 2183287) B2183287
theorem B2911403 : Blo 1148636 2911403 := bstep (se 1 (by rfl) ⟨2183552, by rfl⟩ : syracuseStep 2911403 = 4367105) B4367105
theorem B5827787 : Blo 1148636 5827787 := bstep (se 1 (by rfl) ⟨4370840, by rfl⟩ : syracuseStep 5827787 = 8741681) B8741681
theorem B3272231 : Blo 1148636 3272231 := bstep (se 1 (by rfl) ⟨2454173, by rfl⟩ : syracuseStep 3272231 = 4908347) B4908347
theorem B4910807 : Blo 1148636 4910807 := bstep (se 1 (by rfl) ⟨3683105, by rfl⟩ : syracuseStep 4910807 = 7366211) B7366211
theorem B2912183 : Blo 1148636 2912183 := bstep (se 1 (by rfl) ⟨2184137, by rfl⟩ : syracuseStep 2912183 = 4368275) B4368275
theorem B2584583 : Blo 1148636 2584583 := bstep (se 1 (by rfl) ⟨1938437, by rfl⟩ : syracuseStep 2584583 = 3876875) B3876875
theorem B2584655 : Blo 1148636 2584655 := bstep (se 1 (by rfl) ⟨1938491, by rfl⟩ : syracuseStep 2584655 = 3876983) B3876983
theorem B66252977 : Blo 1148636 66252977 := bstep (se 2 (by rfl) ⟨24844866, by rfl⟩ : syracuseStep 66252977 = 49689733) B49689733
theorem B2585051 : Blo 1148636 2585051 := bstep (se 1 (by rfl) ⟨1938788, by rfl⟩ : syracuseStep 2585051 = 3877577) B3877577
theorem B22147991 : Blo 1148636 22147991 := bstep (se 1 (by rfl) ⟨16610993, by rfl⟩ : syracuseStep 22147991 = 33221987) B33221987
theorem B2913185 : Blo 1148636 2913185 := bstep (se 2 (by rfl) ⟨1092444, by rfl⟩ : syracuseStep 2913185 = 2184889) B2184889
theorem B2585519 : Blo 1148636 2585519 := bstep (se 1 (by rfl) ⟨1939139, by rfl⟩ : syracuseStep 2585519 = 3878279) B3878279
theorem B3273655 : Blo 1148636 3273655 := bstep (se 1 (by rfl) ⟨2455241, by rfl⟩ : syracuseStep 3273655 = 4910483) B4910483
theorem B2585771 : Blo 1148636 2585771 := bstep (se 1 (by rfl) ⟨1939328, by rfl⟩ : syracuseStep 2585771 = 3878657) B3878657
theorem B2913641 : Blo 1148636 2913641 := bstep (se 2 (by rfl) ⟨1092615, by rfl⟩ : syracuseStep 2913641 = 2185231) B2185231
theorem B2586311 : Blo 1148636 2586311 := bstep (se 1 (by rfl) ⟨1939733, by rfl⟩ : syracuseStep 2586311 = 3879467) B3879467
theorem B35452673 : Blo 1148636 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B3930017 : Blo 1148636 3930017 := bstep (se 2 (by rfl) ⟨1473756, by rfl⟩ : syracuseStep 3930017 = 2947513) B2947513
theorem B3274759 : Blo 1148636 3274759 := bstep (se 1 (by rfl) ⟨2456069, by rfl⟩ : syracuseStep 3274759 = 4912139) B4912139
theorem B2455609 : Blo 1148636 2455609 := bstep (se 2 (by rfl) ⟨920853, by rfl⟩ : syracuseStep 2455609 = 1841707) B1841707
theorem B3275113 : Blo 1148636 3275113 := bstep (se 2 (by rfl) ⟨1228167, by rfl⟩ : syracuseStep 3275113 = 2456335) B2456335
theorem B2914825 : Blo 1148636 2914825 := bstep (se 2 (by rfl) ⟨1093059, by rfl⟩ : syracuseStep 2914825 = 2186119) B2186119
theorem B5536289 : Blo 1148636 5536289 := bstep (se 2 (by rfl) ⟨2076108, by rfl⟩ : syracuseStep 5536289 = 4152217) B4152217
theorem B2587175 : Blo 1148636 2587175 := bstep (se 1 (by rfl) ⟨1940381, by rfl⟩ : syracuseStep 2587175 = 3880763) B3880763
theorem B3275387 : Blo 1148636 3275387 := bstep (se 1 (by rfl) ⟨2456540, by rfl⟩ : syracuseStep 3275387 = 4913081) B4913081
theorem B7371593 : Blo 1148636 7371593 := bstep (se 2 (by rfl) ⟨2764347, by rfl⟩ : syracuseStep 7371593 = 5528695) B5528695
theorem B2587499 : Blo 1148636 2587499 := bstep (se 1 (by rfl) ⟨1940624, by rfl⟩ : syracuseStep 2587499 = 3881249) B3881249
theorem B2587553 : Blo 1148636 2587553 := bstep (se 2 (by rfl) ⟨970332, by rfl⟩ : syracuseStep 2587553 = 1940665) B1940665
theorem B5602223 : Blo 1148636 5602223 := bstep (se 1 (by rfl) ⟨4201667, by rfl⟩ : syracuseStep 5602223 = 8403335) B8403335
theorem B16579511 : Blo 1148636 16579511 := bstep (se 1 (by rfl) ⟨12434633, by rfl⟩ : syracuseStep 16579511 = 24869267) B24869267
theorem B2587895 : Blo 1148636 2587895 := bstep (se 1 (by rfl) ⟨1940921, by rfl⟩ : syracuseStep 2587895 = 3881843) B3881843
theorem B16579853 : Blo 1148636 16579853 := bstep (se 3 (by rfl) ⟨3108722, by rfl⟩ : syracuseStep 16579853 = 6217445) B6217445
theorem B1965817 : Blo 1148636 1965817 := bstep (se 2 (by rfl) ⟨737181, by rfl⟩ : syracuseStep 1965817 = 1474363) B1474363
theorem B2588489 : Blo 1148636 2588489 := bstep (se 2 (by rfl) ⟨970683, by rfl⟩ : syracuseStep 2588489 = 1941367) B1941367
theorem B3276719 : Blo 1148636 3276719 := bstep (se 1 (by rfl) ⟨2457539, by rfl⟩ : syracuseStep 3276719 = 4915079) B4915079
theorem B24903611 : Blo 1148636 24903611 := bstep (se 1 (by rfl) ⟨18677708, by rfl⟩ : syracuseStep 24903611 = 37355417) B37355417
theorem B2916283 : Blo 1148636 2916283 := bstep (se 1 (by rfl) ⟨2187212, by rfl⟩ : syracuseStep 2916283 = 4374425) B4374425
theorem B6553619 : Blo 1148636 6553619 := bstep (se 1 (by rfl) ⟨4915214, by rfl⟩ : syracuseStep 6553619 = 9830429) B9830429
theorem B3112985 : Blo 1148636 3112985 := bstep (se 2 (by rfl) ⟨1167369, by rfl⟩ : syracuseStep 3112985 = 2334739) B2334739
theorem B10485811 : Blo 1148636 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B2588777 : Blo 1148636 2588777 := bstep (se 2 (by rfl) ⟨970791, by rfl⟩ : syracuseStep 2588777 = 1941583) B1941583
theorem B5832809 : Blo 1148636 5832809 := bstep (se 2 (by rfl) ⟨2187303, by rfl⟩ : syracuseStep 5832809 = 4374607) B4374607
theorem B2916719 : Blo 1148636 2916719 := bstep (se 1 (by rfl) ⟨2187539, by rfl⟩ : syracuseStep 2916719 = 4375079) B4375079
theorem B2589263 : Blo 1148636 2589263 := bstep (se 1 (by rfl) ⟨1941947, by rfl⟩ : syracuseStep 2589263 = 3883895) B3883895
theorem B2589407 : Blo 1148636 2589407 := bstep (se 1 (by rfl) ⟨1942055, by rfl⟩ : syracuseStep 2589407 = 3884111) B3884111
theorem B22151987 : Blo 1148636 22151987 := bstep (se 1 (by rfl) ⟨16613990, by rfl⟩ : syracuseStep 22151987 = 33227981) B33227981
theorem B19170107 : Blo 1148636 19170107 := bstep (se 1 (by rfl) ⟨14377580, by rfl⟩ : syracuseStep 19170107 = 28755161) B28755161
theorem B2589659 : Blo 1148636 2589659 := bstep (se 1 (by rfl) ⟨1942244, by rfl⟩ : syracuseStep 2589659 = 3884489) B3884489
theorem B2917367 : Blo 1148636 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B2589839 : Blo 1148636 2589839 := bstep (se 1 (by rfl) ⟨1942379, by rfl⟩ : syracuseStep 2589839 = 3884759) B3884759
theorem B5833943 : Blo 1148636 5833943 := bstep (se 1 (by rfl) ⟨4375457, by rfl⟩ : syracuseStep 5833943 = 8750915) B8750915
theorem B2589929 : Blo 1148636 2589929 := bstep (se 2 (by rfl) ⟨971223, by rfl⟩ : syracuseStep 2589929 = 1942447) B1942447
theorem B2589983 : Blo 1148636 2589983 := bstep (se 1 (by rfl) ⟨1942487, by rfl⟩ : syracuseStep 2589983 = 3884975) B3884975
theorem B2459231 : Blo 1148636 2459231 := bstep (se 1 (by rfl) ⟨1844423, by rfl⟩ : syracuseStep 2459231 = 3688847) B3688847
theorem B1148639 : Blo 1148636 1148639 := bstep (se 1 (by rfl) ⟨861479, by rfl⟩ : syracuseStep 1148639 = 1722959) B1722959
theorem B2590505 : Blo 1148636 2590505 := bstep (se 2 (by rfl) ⟨971439, by rfl⟩ : syracuseStep 2590505 = 1942879) B1942879
theorem B1148719 : Blo 1148636 1148719 := bstep (se 1 (by rfl) ⟨861539, by rfl⟩ : syracuseStep 1148719 = 1723079) B1723079
theorem B1148827 : Blo 1148636 1148827 := bstep (se 1 (by rfl) ⟨861620, by rfl⟩ : syracuseStep 1148827 = 1723241) B1723241
theorem B1148879 : Blo 1148636 1148879 := bstep (se 1 (by rfl) ⟨861659, by rfl⟩ : syracuseStep 1148879 = 1723319) B1723319
theorem B1148903 : Blo 1148636 1148903 := bstep (se 1 (by rfl) ⟨861677, by rfl⟩ : syracuseStep 1148903 = 1723355) B1723355
theorem B1149215 : Blo 1148636 1149215 := bstep (se 1 (by rfl) ⟨861911, by rfl⟩ : syracuseStep 1149215 = 1723823) B1723823
theorem B1149275 : Blo 1148636 1149275 := bstep (se 1 (by rfl) ⟨861956, by rfl⟩ : syracuseStep 1149275 = 1723913) B1723913
theorem B1149295 : Blo 1148636 1149295 := bstep (se 1 (by rfl) ⟨861971, by rfl⟩ : syracuseStep 1149295 = 1723943) B1723943
theorem B1149351 : Blo 1148636 1149351 := bstep (se 1 (by rfl) ⟨862013, by rfl⟩ : syracuseStep 1149351 = 1724027) B1724027
theorem B1149435 : Blo 1148636 1149435 := bstep (se 1 (by rfl) ⟨862076, by rfl⟩ : syracuseStep 1149435 = 1724153) B1724153
theorem B1149503 : Blo 1148636 1149503 := bstep (se 1 (by rfl) ⟨862127, by rfl⟩ : syracuseStep 1149503 = 1724255) B1724255
theorem B1149511 : Blo 1148636 1149511 := bstep (se 1 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 1149511 = 1724267) B1724267
theorem B1149663 : Blo 1148636 1149663 := bstep (se 1 (by rfl) ⟨862247, by rfl⟩ : syracuseStep 1149663 = 1724495) B1724495
theorem B3279635 : Blo 1148636 3279635 := bstep (se 1 (by rfl) ⟨2459726, by rfl⟩ : syracuseStep 3279635 = 4919453) B4919453
theorem B1149743 : Blo 1148636 1149743 := bstep (se 1 (by rfl) ⟨862307, by rfl⟩ : syracuseStep 1149743 = 1724615) B1724615
theorem B2591567 : Blo 1148636 2591567 := bstep (se 1 (by rfl) ⟨1943675, by rfl⟩ : syracuseStep 2591567 = 3887351) B3887351
theorem B1149851 : Blo 1148636 1149851 := bstep (se 1 (by rfl) ⟨862388, by rfl⟩ : syracuseStep 1149851 = 1724777) B1724777
theorem B1149903 : Blo 1148636 1149903 := bstep (se 1 (by rfl) ⟨862427, by rfl⟩ : syracuseStep 1149903 = 1724855) B1724855
theorem B1149927 : Blo 1148636 1149927 := bstep (se 1 (by rfl) ⟨862445, by rfl⟩ : syracuseStep 1149927 = 1724891) B1724891
theorem B2591783 : Blo 1148636 2591783 := bstep (se 1 (by rfl) ⟨1943837, by rfl⟩ : syracuseStep 2591783 = 3887675) B3887675
theorem B6556787 : Blo 1148636 6556787 := bstep (se 1 (by rfl) ⟨4917590, by rfl⟩ : syracuseStep 6556787 = 9835181) B9835181
theorem B2460871 : Blo 1148636 2460871 := bstep (se 1 (by rfl) ⟨1845653, by rfl⟩ : syracuseStep 2460871 = 3691307) B3691307
theorem B2591963 : Blo 1148636 2591963 := bstep (se 1 (by rfl) ⟨1943972, by rfl⟩ : syracuseStep 2591963 = 3887945) B3887945
theorem B95816981 : Blo 1148636 95816981 := bstep (se 6 (by rfl) ⟨2245710, by rfl⟩ : syracuseStep 95816981 = 4491421) B4491421
theorem B1150239 : Blo 1148636 1150239 := bstep (se 1 (by rfl) ⟨862679, by rfl⟩ : syracuseStep 1150239 = 1725359) B1725359
theorem B1150299 : Blo 1148636 1150299 := bstep (se 1 (by rfl) ⟨862724, by rfl⟩ : syracuseStep 1150299 = 1725449) B1725449
theorem B2461025 : Blo 1148636 2461025 := bstep (se 2 (by rfl) ⟨922884, by rfl⟩ : syracuseStep 2461025 = 1845769) B1845769
theorem B1150319 : Blo 1148636 1150319 := bstep (se 1 (by rfl) ⟨862739, by rfl⟩ : syracuseStep 1150319 = 1725479) B1725479
theorem B2592161 : Blo 1148636 2592161 := bstep (se 2 (by rfl) ⟨972060, by rfl⟩ : syracuseStep 2592161 = 1944121) B1944121
theorem B1150375 : Blo 1148636 1150375 := bstep (se 1 (by rfl) ⟨862781, by rfl⟩ : syracuseStep 1150375 = 1725563) B1725563
theorem B1150459 : Blo 1148636 1150459 := bstep (se 1 (by rfl) ⟨862844, by rfl⟩ : syracuseStep 1150459 = 1725689) B1725689
theorem B1150527 : Blo 1148636 1150527 := bstep (se 1 (by rfl) ⟨862895, by rfl⟩ : syracuseStep 1150527 = 1725791) B1725791
theorem B1150535 : Blo 1148636 1150535 := bstep (se 1 (by rfl) ⟨862901, by rfl⟩ : syracuseStep 1150535 = 1725803) B1725803
theorem B1150687 : Blo 1148636 1150687 := bstep (se 1 (by rfl) ⟨863015, by rfl⟩ : syracuseStep 1150687 = 1726031) B1726031
theorem B1150767 : Blo 1148636 1150767 := bstep (se 1 (by rfl) ⟨863075, by rfl⟩ : syracuseStep 1150767 = 1726151) B1726151
theorem B1150875 : Blo 1148636 1150875 := bstep (se 1 (by rfl) ⟨863156, by rfl⟩ : syracuseStep 1150875 = 1726313) B1726313
theorem B1150927 : Blo 1148636 1150927 := bstep (se 1 (by rfl) ⟨863195, by rfl⟩ : syracuseStep 1150927 = 1726391) B1726391
theorem B2592719 : Blo 1148636 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B1150951 : Blo 1148636 1150951 := bstep (se 1 (by rfl) ⟨863213, by rfl⟩ : syracuseStep 1150951 = 1726427) B1726427
theorem B1151263 : Blo 1148636 1151263 := bstep (se 1 (by rfl) ⟨863447, by rfl⟩ : syracuseStep 1151263 = 1726895) B1726895
theorem B2593097 : Blo 1148636 2593097 := bstep (se 2 (by rfl) ⟨972411, by rfl⟩ : syracuseStep 2593097 = 1944823) B1944823
theorem B1151323 : Blo 1148636 1151323 := bstep (se 1 (by rfl) ⟨863492, by rfl⟩ : syracuseStep 1151323 = 1726985) B1726985
theorem B2593115 : Blo 1148636 2593115 := bstep (se 1 (by rfl) ⟨1944836, by rfl⟩ : syracuseStep 2593115 = 3889673) B3889673
theorem B1151343 : Blo 1148636 1151343 := bstep (se 1 (by rfl) ⟨863507, by rfl⟩ : syracuseStep 1151343 = 1727015) B1727015
theorem B1151399 : Blo 1148636 1151399 := bstep (se 1 (by rfl) ⟨863549, by rfl⟩ : syracuseStep 1151399 = 1727099) B1727099
theorem B1151483 : Blo 1148636 1151483 := bstep (se 1 (by rfl) ⟨863612, by rfl⟩ : syracuseStep 1151483 = 1727225) B1727225
theorem B1151551 : Blo 1148636 1151551 := bstep (se 1 (by rfl) ⟨863663, by rfl⟩ : syracuseStep 1151551 = 1727327) B1727327
theorem B1151559 : Blo 1148636 1151559 := bstep (se 1 (by rfl) ⟨863669, by rfl⟩ : syracuseStep 1151559 = 1727339) B1727339
theorem B1151711 : Blo 1148636 1151711 := bstep (se 1 (by rfl) ⟨863783, by rfl⟩ : syracuseStep 1151711 = 1727567) B1727567
theorem B1151791 : Blo 1148636 1151791 := bstep (se 1 (by rfl) ⟨863843, by rfl⟩ : syracuseStep 1151791 = 1727687) B1727687
theorem B7377743 : Blo 1148636 7377743 := bstep (se 1 (by rfl) ⟨5533307, by rfl⟩ : syracuseStep 7377743 = 11066615) B11066615
theorem B1151899 : Blo 1148636 1151899 := bstep (se 1 (by rfl) ⟨863924, by rfl⟩ : syracuseStep 1151899 = 1727849) B1727849
theorem B1151951 : Blo 1148636 1151951 := bstep (se 1 (by rfl) ⟨863963, by rfl⟩ : syracuseStep 1151951 = 1727927) B1727927
theorem B8393681 : Blo 1148636 8393681 := bstep (se 2 (by rfl) ⟨3147630, by rfl⟩ : syracuseStep 8393681 = 6295261) B6295261
theorem B1151975 : Blo 1148636 1151975 := bstep (se 1 (by rfl) ⟨863981, by rfl⟩ : syracuseStep 1151975 = 1727963) B1727963
theorem B3740915 : Blo 1148636 3740915 := bstep (se 1 (by rfl) ⟨2805686, by rfl⟩ : syracuseStep 3740915 = 5611373) B5611373
theorem B1152287 : Blo 1148636 1152287 := bstep (se 1 (by rfl) ⟨864215, by rfl⟩ : syracuseStep 1152287 = 1728431) B1728431
theorem B1152347 : Blo 1148636 1152347 := bstep (se 1 (by rfl) ⟨864260, by rfl⟩ : syracuseStep 1152347 = 1728521) B1728521
theorem B1152367 : Blo 1148636 1152367 := bstep (se 1 (by rfl) ⟨864275, by rfl⟩ : syracuseStep 1152367 = 1728551) B1728551
theorem B1152423 : Blo 1148636 1152423 := bstep (se 1 (by rfl) ⟨864317, by rfl⟩ : syracuseStep 1152423 = 1728635) B1728635
theorem B1938937 : Blo 1148636 1938937 := bstep (se 2 (by rfl) ⟨727101, by rfl⟩ : syracuseStep 1938937 = 1454203) B1454203
theorem B1152507 : Blo 1148636 1152507 := bstep (se 1 (by rfl) ⟨864380, by rfl⟩ : syracuseStep 1152507 = 1728761) B1728761
theorem B1152575 : Blo 1148636 1152575 := bstep (se 1 (by rfl) ⟨864431, by rfl⟩ : syracuseStep 1152575 = 1728863) B1728863
theorem B1152583 : Blo 1148636 1152583 := bstep (se 1 (by rfl) ⟨864437, by rfl⟩ : syracuseStep 1152583 = 1728875) B1728875
theorem B1939207 : Blo 1148636 1939207 := bstep (se 1 (by rfl) ⟨1454405, by rfl⟩ : syracuseStep 1939207 = 2908811) B2908811
theorem B1939241 : Blo 1148636 1939241 := bstep (se 2 (by rfl) ⟨727215, by rfl⟩ : syracuseStep 1939241 = 1454431) B1454431
theorem B8395085 : Blo 1148636 8395085 := bstep (se 3 (by rfl) ⟨1574078, by rfl⟩ : syracuseStep 8395085 = 3148157) B3148157
theorem B4200815 : Blo 1148636 4200815 := bstep (se 1 (by rfl) ⟨3150611, by rfl⟩ : syracuseStep 4200815 = 6301223) B6301223
theorem B7379383 : Blo 1148636 7379383 := bstep (se 1 (by rfl) ⟨5534537, by rfl⟩ : syracuseStep 7379383 = 11069075) B11069075
theorem B1939963 : Blo 1148636 1939963 := bstep (se 1 (by rfl) ⟨1454972, by rfl⟩ : syracuseStep 1939963 = 2909945) B2909945
theorem B4364873 : Blo 1148636 4364873 := bstep (se 2 (by rfl) ⟨1636827, by rfl⟩ : syracuseStep 4364873 = 3273655) B3273655
theorem B1841771 : Blo 1148636 1841771 := bstep (se 1 (by rfl) ⟨1381328, by rfl⟩ : syracuseStep 1841771 = 2762657) B2762657
theorem B12425987 : Blo 1148636 12425987 := bstep (se 1 (by rfl) ⟨9319490, by rfl⟩ : syracuseStep 12425987 = 18638981) B18638981
theorem B29498255 : Blo 1148636 29498255 := bstep (se 1 (by rfl) ⟨22123691, by rfl⟩ : syracuseStep 29498255 = 44247383) B44247383
theorem B1940395 : Blo 1148636 1940395 := bstep (se 1 (by rfl) ⟨1455296, by rfl⟩ : syracuseStep 1940395 = 2910593) B2910593
theorem B1940699 : Blo 1148636 1940699 := bstep (se 1 (by rfl) ⟨1455524, by rfl⟩ : syracuseStep 1940699 = 2911049) B2911049
theorem B15736157 : Blo 1148636 15736157 := bstep (se 3 (by rfl) ⟨2950529, by rfl⟩ : syracuseStep 15736157 = 5901059) B5901059
theorem B6561161 : Blo 1148636 6561161 := bstep (se 2 (by rfl) ⟨2460435, by rfl⟩ : syracuseStep 6561161 = 4920871) B4920871
theorem B1940935 : Blo 1148636 1940935 := bstep (se 1 (by rfl) ⟨1455701, by rfl⟩ : syracuseStep 1940935 = 2911403) B2911403
theorem B12459545 : Blo 1148636 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B4923143 : Blo 1148636 4923143 := bstep (se 1 (by rfl) ⟨3692357, by rfl⟩ : syracuseStep 4923143 = 7384715) B7384715
theorem B1843001 : Blo 1148636 1843001 := bstep (se 2 (by rfl) ⟨691125, by rfl⟩ : syracuseStep 1843001 = 1382251) B1382251
theorem B1941455 : Blo 1148636 1941455 := bstep (se 1 (by rfl) ⟨1456091, by rfl⟩ : syracuseStep 1941455 = 2912183) B2912183
theorem B4366345 : Blo 1148636 4366345 := bstep (se 2 (by rfl) ⟨1637379, by rfl⟩ : syracuseStep 4366345 = 3274759) B3274759
theorem B22126769 : Blo 1148636 22126769 := bstep (se 2 (by rfl) ⟨8297538, by rfl⟩ : syracuseStep 22126769 = 16595077) B16595077
theorem B22094167 : Blo 1148636 22094167 := bstep (se 1 (by rfl) ⟨16570625, by rfl⟩ : syracuseStep 22094167 = 33141251) B33141251
theorem B2433491 : Blo 1148636 2433491 := bstep (se 1 (by rfl) ⟨1825118, by rfl⟩ : syracuseStep 2433491 = 3650237) B3650237
theorem B4366817 : Blo 1148636 4366817 := bstep (se 2 (by rfl) ⟨1637556, by rfl⟩ : syracuseStep 4366817 = 3275113) B3275113
theorem B1942123 : Blo 1148636 1942123 := bstep (se 1 (by rfl) ⟨1456592, by rfl⟩ : syracuseStep 1942123 = 2913185) B2913185
theorem B1942427 : Blo 1148636 1942427 := bstep (se 1 (by rfl) ⟨1456820, by rfl⟩ : syracuseStep 1942427 = 2913641) B2913641
theorem B8856515 : Blo 1148636 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B9839555 : Blo 1148636 9839555 := bstep (se 1 (by rfl) ⟨7379666, by rfl⟩ : syracuseStep 9839555 = 14759333) B14759333
theorem B2761715 : Blo 1148636 2761715 := bstep (se 1 (by rfl) ⟨2071286, by rfl⟩ : syracuseStep 2761715 = 4142573) B4142573
theorem B23635115 : Blo 1148636 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B10233479 : Blo 1148636 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B1844923 : Blo 1148636 1844923 := bstep (se 1 (by rfl) ⟨1383692, by rfl⟩ : syracuseStep 1844923 = 2767385) B2767385
theorem B11806397 : Blo 1148636 11806397 := bstep (se 3 (by rfl) ⟨2213699, by rfl⟩ : syracuseStep 11806397 = 4427399) B4427399
theorem B3876713 : Blo 1148636 3876713 := bstep (se 2 (by rfl) ⟨1453767, by rfl⟩ : syracuseStep 3876713 = 2907535) B2907535
theorem B11053007 : Blo 1148636 11053007 := bstep (se 1 (by rfl) ⟨8289755, by rfl⟩ : syracuseStep 11053007 = 16579511) B16579511
theorem B11053235 : Blo 1148636 11053235 := bstep (se 1 (by rfl) ⟨8289926, by rfl⟩ : syracuseStep 11053235 = 16579853) B16579853
theorem B3680441 : Blo 1148636 3680441 := bstep (se 2 (by rfl) ⟨1380165, by rfl⟩ : syracuseStep 3680441 = 2760331) B2760331
theorem B13117625 : Blo 1148636 13117625 := bstep (se 2 (by rfl) ⟨4919109, by rfl⟩ : syracuseStep 13117625 = 9838219) B9838219
theorem B4434173 : Blo 1148636 4434173 := bstep (se 3 (by rfl) ⟨831407, by rfl⟩ : syracuseStep 4434173 = 1662815) B1662815
theorem B3877145 : Blo 1148636 3877145 := bstep (se 2 (by rfl) ⟨1453929, by rfl⟩ : syracuseStep 3877145 = 2907859) B2907859
theorem B35367815 : Blo 1148636 35367815 := bstep (se 1 (by rfl) ⟨26525861, by rfl⟩ : syracuseStep 35367815 = 53051723) B53051723
theorem B14953643 : Blo 1148636 14953643 := bstep (se 1 (by rfl) ⟨11215232, by rfl⟩ : syracuseStep 14953643 = 22430465) B22430465
theorem B11054465 : Blo 1148636 11054465 := bstep (se 2 (by rfl) ⟨4145424, by rfl⟩ : syracuseStep 11054465 = 8290849) B8290849
theorem B8728073 : Blo 1148636 8728073 := bstep (se 2 (by rfl) ⟨3273027, by rfl⟩ : syracuseStep 8728073 = 6546055) B6546055
theorem B3681875 : Blo 1148636 3681875 := bstep (se 1 (by rfl) ⟨2761406, by rfl⟩ : syracuseStep 3681875 = 5522813) B5522813
theorem B3878495 : Blo 1148636 3878495 := bstep (se 1 (by rfl) ⟨2908871, by rfl⟩ : syracuseStep 3878495 = 5817743) B5817743
theorem B2076347 : Blo 1148636 2076347 := bstep (se 1 (by rfl) ⟨1557260, by rfl⟩ : syracuseStep 2076347 = 3114521) B3114521
theorem B1453879 : Blo 1148636 1453879 := bstep (se 1 (by rfl) ⟨1090409, by rfl⟩ : syracuseStep 1453879 = 2180819) B2180819
theorem B5320505 : Blo 1148636 5320505 := bstep (se 2 (by rfl) ⟨1995189, by rfl⟩ : syracuseStep 5320505 = 3990379) B3990379
theorem B4370233 : Blo 1148636 4370233 := bstep (se 2 (by rfl) ⟨1638837, by rfl⟩ : syracuseStep 4370233 = 3277675) B3277675
theorem B4370537 : Blo 1148636 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B1454375 : Blo 1148636 1454375 := bstep (se 1 (by rfl) ⟨1090781, by rfl⟩ : syracuseStep 1454375 = 2181563) B2181563
theorem B11055467 : Blo 1148636 11055467 := bstep (se 1 (by rfl) ⟨8291600, by rfl⟩ : syracuseStep 11055467 = 16583201) B16583201
theorem B1454699 : Blo 1148636 1454699 := bstep (se 1 (by rfl) ⟨1091024, by rfl⟩ : syracuseStep 1454699 = 2182049) B2182049
theorem B3879899 : Blo 1148636 3879899 := bstep (se 1 (by rfl) ⟨2909924, by rfl⟩ : syracuseStep 3879899 = 5819849) B5819849
theorem B1455079 : Blo 1148636 1455079 := bstep (se 1 (by rfl) ⟨1091309, by rfl⟩ : syracuseStep 1455079 = 2182619) B2182619
theorem B14758969 : Blo 1148636 14758969 := bstep (se 2 (by rfl) ⟨5534613, by rfl⟩ : syracuseStep 14758969 = 11069227) B11069227
theorem B3880061 : Blo 1148636 3880061 := bstep (se 3 (by rfl) ⟨727511, by rfl⟩ : syracuseStep 3880061 = 1455023) B1455023
theorem B2765963 : Blo 1148636 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B3880169 : Blo 1148636 3880169 := bstep (se 2 (by rfl) ⟨1455063, by rfl⟩ : syracuseStep 3880169 = 2910127) B2910127
theorem B3880331 : Blo 1148636 3880331 := bstep (se 1 (by rfl) ⟨2910248, by rfl⟩ : syracuseStep 3880331 = 5820497) B5820497
theorem B8730017 : Blo 1148636 8730017 := bstep (se 2 (by rfl) ⟨3273756, by rfl⟩ : syracuseStep 8730017 = 6547513) B6547513
theorem B11056925 : Blo 1148636 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B12433337 : Blo 1148636 12433337 := bstep (se 2 (by rfl) ⟨4662501, by rfl⟩ : syracuseStep 12433337 = 9325003) B9325003
theorem B3684617 : Blo 1148636 3684617 := bstep (se 2 (by rfl) ⟨1381731, by rfl⟩ : syracuseStep 3684617 = 2763463) B2763463
theorem B1292575 : Blo 1148636 1292575 := bstep (se 1 (by rfl) ⟨969431, by rfl⟩ : syracuseStep 1292575 = 1938863) B1938863
theorem B1292863 : Blo 1148636 1292863 := bstep (se 1 (by rfl) ⟨969647, by rfl⟩ : syracuseStep 1292863 = 1939295) B1939295
theorem B1751735 : Blo 1148636 1751735 := bstep (se 1 (by rfl) ⟨1313801, by rfl⟩ : syracuseStep 1751735 = 2627603) B2627603
theorem B4143811 : Blo 1148636 4143811 := bstep (se 1 (by rfl) ⟨3107858, by rfl⟩ : syracuseStep 4143811 = 6215717) B6215717
theorem B21019499 : Blo 1148636 21019499 := bstep (se 1 (by rfl) ⟨15764624, by rfl⟩ : syracuseStep 21019499 = 31529249) B31529249
theorem B1752283 : Blo 1148636 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B1293691 : Blo 1148636 1293691 := bstep (se 1 (by rfl) ⟨970268, by rfl⟩ : syracuseStep 1293691 = 1940537) B1940537
theorem B2768327 : Blo 1148636 2768327 := bstep (se 1 (by rfl) ⟨2076245, by rfl⟩ : syracuseStep 2768327 = 4152491) B4152491
theorem B8306135 : Blo 1148636 8306135 := bstep (se 1 (by rfl) ⟨6229601, by rfl⟩ : syracuseStep 8306135 = 12459203) B12459203
theorem B4144907 : Blo 1148636 4144907 := bstep (se 1 (by rfl) ⟨3108680, by rfl⟩ : syracuseStep 4144907 = 6217361) B6217361
theorem B1294159 : Blo 1148636 1294159 := bstep (se 1 (by rfl) ⟨970619, by rfl⟩ : syracuseStep 1294159 = 1941239) B1941239
theorem B1294555 : Blo 1148636 1294555 := bstep (se 1 (by rfl) ⟨970916, by rfl⟩ : syracuseStep 1294555 = 1941833) B1941833
theorem B3883355 : Blo 1148636 3883355 := bstep (se 1 (by rfl) ⟨2912516, by rfl⟩ : syracuseStep 3883355 = 5825033) B5825033
theorem B1294843 : Blo 1148636 1294843 := bstep (se 1 (by rfl) ⟨971132, by rfl⟩ : syracuseStep 1294843 = 1942265) B1942265
theorem B2769403 : Blo 1148636 2769403 := bstep (se 1 (by rfl) ⟨2077052, by rfl⟩ : syracuseStep 2769403 = 4154105) B4154105
theorem B11813377 : Blo 1148636 11813377 := bstep (se 2 (by rfl) ⟨4430016, by rfl⟩ : syracuseStep 11813377 = 8860033) B8860033
theorem B1295023 : Blo 1148636 1295023 := bstep (se 1 (by rfl) ⟨971267, by rfl⟩ : syracuseStep 1295023 = 1942535) B1942535
theorem B1295311 : Blo 1148636 1295311 := bstep (se 1 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 1295311 = 1942967) B1942967
theorem B3884327 : Blo 1148636 3884327 := bstep (se 1 (by rfl) ⟨2913245, by rfl⟩ : syracuseStep 3884327 = 5826491) B5826491
theorem B121029947 : Blo 1148636 121029947 := bstep (se 1 (by rfl) ⟨90772460, by rfl⟩ : syracuseStep 121029947 = 181544921) B181544921
theorem B1295707 : Blo 1148636 1295707 := bstep (se 1 (by rfl) ⟨971780, by rfl⟩ : syracuseStep 1295707 = 1943561) B1943561
theorem B23577965 : Blo 1148636 23577965 := bstep (se 3 (by rfl) ⟨4420868, by rfl⟩ : syracuseStep 23577965 = 8841737) B8841737
theorem B1295815 : Blo 1148636 1295815 := bstep (se 1 (by rfl) ⟨971861, by rfl⟩ : syracuseStep 1295815 = 1943723) B1943723
theorem B1296175 : Blo 1148636 1296175 := bstep (se 1 (by rfl) ⟨972131, by rfl⟩ : syracuseStep 1296175 = 1944263) B1944263
theorem B1296283 : Blo 1148636 1296283 := bstep (se 1 (by rfl) ⟨972212, by rfl⟩ : syracuseStep 1296283 = 1944425) B1944425
theorem B3885191 : Blo 1148636 3885191 := bstep (se 1 (by rfl) ⟨2913893, by rfl⟩ : syracuseStep 3885191 = 5827787) B5827787
theorem B5818553 : Blo 1148636 5818553 := bstep (se 2 (by rfl) ⟨2181957, by rfl⟩ : syracuseStep 5818553 = 4363915) B4363915
theorem B9816349 : Blo 1148636 9816349 := bstep (se 3 (by rfl) ⟨1840565, by rfl⟩ : syracuseStep 9816349 = 3681131) B3681131
theorem B1296679 : Blo 1148636 1296679 := bstep (se 1 (by rfl) ⟨972509, by rfl⟩ : syracuseStep 1296679 = 1945019) B1945019
theorem B2181487 : Blo 1148636 2181487 := bstep (se 1 (by rfl) ⟨1636115, by rfl⟩ : syracuseStep 2181487 = 3272231) B3272231
theorem B1723001 : Blo 1148636 1723001 := bstep (se 2 (by rfl) ⟨646125, by rfl⟩ : syracuseStep 1723001 = 1292251) B1292251
theorem B1723055 : Blo 1148636 1723055 := bstep (se 1 (by rfl) ⟨1292291, by rfl⟩ : syracuseStep 1723055 = 2584583) B2584583
theorem B5524157 : Blo 1148636 5524157 := bstep (se 3 (by rfl) ⟨1035779, by rfl⟩ : syracuseStep 5524157 = 2071559) B2071559
theorem B1723103 : Blo 1148636 1723103 := bstep (se 1 (by rfl) ⟨1292327, by rfl⟩ : syracuseStep 1723103 = 2584655) B2584655
theorem B1723367 : Blo 1148636 1723367 := bstep (se 1 (by rfl) ⟨1292525, by rfl⟩ : syracuseStep 1723367 = 2585051) B2585051
theorem B9817307 : Blo 1148636 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B1723625 : Blo 1148636 1723625 := bstep (se 2 (by rfl) ⟨646359, by rfl⟩ : syracuseStep 1723625 = 1292719) B1292719
theorem B14765327 : Blo 1148636 14765327 := bstep (se 1 (by rfl) ⟨11073995, by rfl⟩ : syracuseStep 14765327 = 22147991) B22147991
theorem B1723679 : Blo 1148636 1723679 := bstep (se 1 (by rfl) ⟨1292759, by rfl⟩ : syracuseStep 1723679 = 2585519) B2585519
theorem B3886433 : Blo 1148636 3886433 := bstep (se 2 (by rfl) ⟨1457412, by rfl⟩ : syracuseStep 3886433 = 2914825) B2914825
theorem B1723847 : Blo 1148636 1723847 := bstep (se 1 (by rfl) ⟨1292885, by rfl⟩ : syracuseStep 1723847 = 2585771) B2585771
theorem B29511377 : Blo 1148636 29511377 := bstep (se 2 (by rfl) ⟨11066766, by rfl⟩ : syracuseStep 29511377 = 22133533) B22133533
theorem B19943185 : Blo 1148636 19943185 := bstep (se 2 (by rfl) ⟨7478694, by rfl⟩ : syracuseStep 19943185 = 14957389) B14957389
theorem B1724201 : Blo 1148636 1724201 := bstep (se 2 (by rfl) ⟨646575, by rfl⟩ : syracuseStep 1724201 = 1293151) B1293151
theorem B1724207 : Blo 1148636 1724207 := bstep (se 1 (by rfl) ⟨1293155, by rfl⟩ : syracuseStep 1724207 = 2586311) B2586311
theorem B6213449 : Blo 1148636 6213449 := bstep (se 2 (by rfl) ⟨2330043, by rfl⟩ : syracuseStep 6213449 = 4660087) B4660087
theorem B5820335 : Blo 1148636 5820335 := bstep (se 1 (by rfl) ⟨4365251, by rfl⟩ : syracuseStep 5820335 = 8730503) B8730503
theorem B1724681 : Blo 1148636 1724681 := bstep (se 2 (by rfl) ⟨646755, by rfl⟩ : syracuseStep 1724681 = 1293511) B1293511
theorem B3690859 : Blo 1148636 3690859 := bstep (se 1 (by rfl) ⟨2768144, by rfl⟩ : syracuseStep 3690859 = 5536289) B5536289
theorem B1724783 : Blo 1148636 1724783 := bstep (se 1 (by rfl) ⟨1293587, by rfl⟩ : syracuseStep 1724783 = 2587175) B2587175
theorem B2183591 : Blo 1148636 2183591 := bstep (se 1 (by rfl) ⟨1637693, by rfl⟩ : syracuseStep 2183591 = 3275387) B3275387
theorem B1724999 : Blo 1148636 1724999 := bstep (se 1 (by rfl) ⟨1293749, by rfl⟩ : syracuseStep 1724999 = 2587499) B2587499
theorem B1725035 : Blo 1148636 1725035 := bstep (se 1 (by rfl) ⟨1293776, by rfl⟩ : syracuseStep 1725035 = 2587553) B2587553
theorem B1725263 : Blo 1148636 1725263 := bstep (se 1 (by rfl) ⟨1293947, by rfl⟩ : syracuseStep 1725263 = 2587895) B2587895
theorem B112251905 : Blo 1148636 112251905 := bstep (se 2 (by rfl) ⟨42094464, by rfl⟩ : syracuseStep 112251905 = 84188929) B84188929
theorem B1725659 : Blo 1148636 1725659 := bstep (se 1 (by rfl) ⟨1294244, by rfl⟩ : syracuseStep 1725659 = 2588489) B2588489
theorem B3888377 : Blo 1148636 3888377 := bstep (se 2 (by rfl) ⟨1458141, by rfl⟩ : syracuseStep 3888377 = 2916283) B2916283
theorem B2184479 : Blo 1148636 2184479 := bstep (se 1 (by rfl) ⟨1638359, by rfl⟩ : syracuseStep 2184479 = 3276719) B3276719
theorem B16602407 : Blo 1148636 16602407 := bstep (se 1 (by rfl) ⟨12451805, by rfl⟩ : syracuseStep 16602407 = 24903611) B24903611
theorem B1725833 : Blo 1148636 1725833 := bstep (se 2 (by rfl) ⟨647187, by rfl⟩ : syracuseStep 1725833 = 1294375) B1294375
theorem B3888647 : Blo 1148636 3888647 := bstep (se 1 (by rfl) ⟨2916485, by rfl⟩ : syracuseStep 3888647 = 5832971) B5832971
theorem B1726187 : Blo 1148636 1726187 := bstep (se 1 (by rfl) ⟨1294640, by rfl⟩ : syracuseStep 1726187 = 2589281) B2589281
theorem B1726415 : Blo 1148636 1726415 := bstep (se 1 (by rfl) ⟨1294811, by rfl⟩ : syracuseStep 1726415 = 2589623) B2589623
theorem B6215933 : Blo 1148636 6215933 := bstep (se 3 (by rfl) ⟨1165487, by rfl⟩ : syracuseStep 6215933 = 2330975) B2330975
theorem B2185481 : Blo 1148636 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B1726811 : Blo 1148636 1726811 := bstep (se 1 (by rfl) ⟨1295108, by rfl⟩ : syracuseStep 1726811 = 2590217) B2590217
theorem B3889619 : Blo 1148636 3889619 := bstep (se 1 (by rfl) ⟨2917214, by rfl⟩ : syracuseStep 3889619 = 5834429) B5834429
theorem B204429887 : Blo 1148636 204429887 := bstep (se 1 (by rfl) ⟨153322415, by rfl⟩ : syracuseStep 204429887 = 306644831) B306644831
theorem B1727039 : Blo 1148636 1727039 := bstep (se 1 (by rfl) ⟨1295279, by rfl⟩ : syracuseStep 1727039 = 2590559) B2590559
theorem B3889727 : Blo 1148636 3889727 := bstep (se 1 (by rfl) ⟨2917295, by rfl⟩ : syracuseStep 3889727 = 5834591) B5834591
theorem B1727159 : Blo 1148636 1727159 := bstep (se 1 (by rfl) ⟨1295369, by rfl⟩ : syracuseStep 1727159 = 2590739) B2590739
theorem B5823251 : Blo 1148636 5823251 := bstep (se 1 (by rfl) ⟨4367438, by rfl⟩ : syracuseStep 5823251 = 8734877) B8734877
theorem B5528387 : Blo 1148636 5528387 := bstep (se 1 (by rfl) ⟨4146290, by rfl⟩ : syracuseStep 5528387 = 8292581) B8292581
theorem B1727387 : Blo 1148636 1727387 := bstep (se 1 (by rfl) ⟨1295540, by rfl⟩ : syracuseStep 1727387 = 2591081) B2591081
theorem B1727783 : Blo 1148636 1727783 := bstep (se 1 (by rfl) ⟨1295837, by rfl⟩ : syracuseStep 1727783 = 2591675) B2591675
theorem B2907515 : Blo 1148636 2907515 := bstep (se 1 (by rfl) ⟨2180636, by rfl⟩ : syracuseStep 2907515 = 4361273) B4361273
theorem B1727867 : Blo 1148636 1727867 := bstep (se 1 (by rfl) ⟨1295900, by rfl⟩ : syracuseStep 1727867 = 2591801) B2591801
theorem B10640803 : Blo 1148636 10640803 := bstep (se 1 (by rfl) ⟨7980602, by rfl⟩ : syracuseStep 10640803 = 15961205) B15961205
theorem B18636247 : Blo 1148636 18636247 := bstep (se 1 (by rfl) ⟨13977185, by rfl⟩ : syracuseStep 18636247 = 27954371) B27954371
theorem B1727993 : Blo 1148636 1727993 := bstep (se 2 (by rfl) ⟨647997, by rfl⟩ : syracuseStep 1727993 = 1295995) B1295995
theorem B1728095 : Blo 1148636 1728095 := bstep (se 1 (by rfl) ⟨1296071, by rfl⟩ : syracuseStep 1728095 = 2592143) B2592143
theorem B2907809 : Blo 1148636 2907809 := bstep (se 2 (by rfl) ⟨1090428, by rfl⟩ : syracuseStep 2907809 = 2180857) B2180857
theorem B2186939 : Blo 1148636 2186939 := bstep (se 1 (by rfl) ⟨1640204, by rfl⟩ : syracuseStep 2186939 = 3280409) B3280409
theorem B1728311 : Blo 1148636 1728311 := bstep (se 1 (by rfl) ⟨1296233, by rfl⟩ : syracuseStep 1728311 = 2592467) B2592467
theorem B9822059 : Blo 1148636 9822059 := bstep (se 1 (by rfl) ⟨7366544, by rfl⟩ : syracuseStep 9822059 = 14733089) B14733089
theorem B5824385 : Blo 1148636 5824385 := bstep (se 2 (by rfl) ⟨2184144, by rfl⟩ : syracuseStep 5824385 = 4368289) B4368289
theorem B1728617 : Blo 1148636 1728617 := bstep (se 2 (by rfl) ⟨648231, by rfl⟩ : syracuseStep 1728617 = 1296463) B1296463
theorem B2908507 : Blo 1148636 2908507 := bstep (se 1 (by rfl) ⟨2181380, by rfl⟩ : syracuseStep 2908507 = 4362761) B4362761
theorem B1728935 : Blo 1148636 1728935 := bstep (se 1 (by rfl) ⟨1296701, by rfl⟩ : syracuseStep 1728935 = 2593403) B2593403
theorem B6218291 : Blo 1148636 6218291 := bstep (se 1 (by rfl) ⟨4663718, by rfl⟩ : syracuseStep 6218291 = 9327437) B9327437
theorem B5825195 : Blo 1148636 5825195 := bstep (se 1 (by rfl) ⟨4368896, by rfl⟩ : syracuseStep 5825195 = 8737793) B8737793
theorem B5530463 : Blo 1148636 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B4908023 : Blo 1148636 4908023 := bstep (se 1 (by rfl) ⟨3681017, by rfl⟩ : syracuseStep 4908023 = 7362035) B7362035
theorem B5825681 : Blo 1148636 5825681 := bstep (se 2 (by rfl) ⟨2184630, by rfl⟩ : syracuseStep 5825681 = 4369261) B4369261
theorem B2909479 : Blo 1148636 2909479 := bstep (se 1 (by rfl) ⟨2182109, by rfl⟩ : syracuseStep 2909479 = 4364219) B4364219
theorem B7005527 : Blo 1148636 7005527 := bstep (se 1 (by rfl) ⟨5254145, by rfl⟩ : syracuseStep 7005527 = 10508291) B10508291
theorem B1598887 : Blo 1148636 1598887 := bstep (se 1 (by rfl) ⟨1199165, by rfl⟩ : syracuseStep 1598887 = 2398331) B2398331
theorem B24864245 : Blo 1148636 24864245 := bstep (se 5 (by rfl) ⟨1165511, by rfl⟩ : syracuseStep 24864245 = 2331023) B2331023
theorem B2909753 : Blo 1148636 2909753 := bstep (se 2 (by rfl) ⟨1091157, by rfl⟩ : syracuseStep 2909753 = 2182315) B2182315
theorem B19687373 : Blo 1148636 19687373 := bstep (se 3 (by rfl) ⟨3691382, by rfl⟩ : syracuseStep 19687373 = 7382765) B7382765
theorem B10480045 : Blo 1148636 10480045 := bstep (se 3 (by rfl) ⟨1965008, by rfl⟩ : syracuseStep 10480045 = 3930017) B3930017
theorem B5532077 : Blo 1148636 5532077 := bstep (se 3 (by rfl) ⟨1037264, by rfl⟩ : syracuseStep 5532077 = 2074529) B2074529
theorem B3107297 : Blo 1148636 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B13265531 : Blo 1148636 13265531 := bstep (se 1 (by rfl) ⟨9949148, by rfl⟩ : syracuseStep 13265531 = 19898297) B19898297
theorem B2911585 : Blo 1148636 2911585 := bstep (se 2 (by rfl) ⟨1091844, by rfl⟩ : syracuseStep 2911585 = 2183689) B2183689
theorem B5828111 : Blo 1148636 5828111 := bstep (se 1 (by rfl) ⟨4371083, by rfl⟩ : syracuseStep 5828111 = 8742167) B8742167
theorem B6221407 : Blo 1148636 6221407 := bstep (se 1 (by rfl) ⟨4666055, by rfl⟩ : syracuseStep 6221407 = 9332111) B9332111
theorem B11071073 : Blo 1148636 11071073 := bstep (se 2 (by rfl) ⟨4151652, by rfl⟩ : syracuseStep 11071073 = 8303305) B8303305
theorem B42626749 : Blo 1148636 42626749 := bstep (se 3 (by rfl) ⟨7992515, by rfl⟩ : syracuseStep 42626749 = 15985031) B15985031
theorem B2453609 : Blo 1148636 2453609 := bstep (se 2 (by rfl) ⟨920103, by rfl⟩ : syracuseStep 2453609 = 1840207) B1840207
theorem B2912537 : Blo 1148636 2912537 := bstep (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) B2184403
theorem B2584943 : Blo 1148636 2584943 := bstep (se 1 (by rfl) ⟨1938707, by rfl⟩ : syracuseStep 2584943 = 3877415) B3877415
theorem B2585015 : Blo 1148636 2585015 := bstep (se 1 (by rfl) ⟨1938761, by rfl⟩ : syracuseStep 2585015 = 3877523) B3877523
theorem B5534153 : Blo 1148636 5534153 := bstep (se 2 (by rfl) ⟨2075307, by rfl⟩ : syracuseStep 5534153 = 4150615) B4150615
theorem B5829083 : Blo 1148636 5829083 := bstep (se 1 (by rfl) ⟨4371812, by rfl⟩ : syracuseStep 5829083 = 8743625) B8743625
theorem B2912831 : Blo 1148636 2912831 := bstep (se 1 (by rfl) ⟨2184623, by rfl⟩ : syracuseStep 2912831 = 4369247) B4369247
theorem B2585159 : Blo 1148636 2585159 := bstep (se 1 (by rfl) ⟨1938869, by rfl⟩ : syracuseStep 2585159 = 3877739) B3877739
theorem B8745569 : Blo 1148636 8745569 := bstep (se 2 (by rfl) ⟨3279588, by rfl⟩ : syracuseStep 8745569 = 6559177) B6559177
theorem B2585195 : Blo 1148636 2585195 := bstep (se 1 (by rfl) ⟨1938896, by rfl⟩ : syracuseStep 2585195 = 3877793) B3877793
theorem B2913043 : Blo 1148636 2913043 := bstep (se 1 (by rfl) ⟨2184782, by rfl⟩ : syracuseStep 2913043 = 4369565) B4369565
theorem B5829569 : Blo 1148636 5829569 := bstep (se 2 (by rfl) ⟨2186088, by rfl⟩ : syracuseStep 5829569 = 4372177) B4372177
theorem B2585591 : Blo 1148636 2585591 := bstep (se 1 (by rfl) ⟨1939193, by rfl⟩ : syracuseStep 2585591 = 3878387) B3878387
theorem B14939261 : Blo 1148636 14939261 := bstep (se 3 (by rfl) ⟨2801111, by rfl⟩ : syracuseStep 14939261 = 5602223) B5602223
theorem B3273871 : Blo 1148636 3273871 := bstep (se 1 (by rfl) ⟨2455403, by rfl⟩ : syracuseStep 3273871 = 4910807) B4910807
theorem B2913479 : Blo 1148636 2913479 := bstep (se 1 (by rfl) ⟨2185109, by rfl⟩ : syracuseStep 2913479 = 4370219) B4370219
theorem B5534963 : Blo 1148636 5534963 := bstep (se 1 (by rfl) ⟨4151222, by rfl⟩ : syracuseStep 5534963 = 8302445) B8302445
theorem B2913529 : Blo 1148636 2913529 := bstep (se 2 (by rfl) ⟨1092573, by rfl⟩ : syracuseStep 2913529 = 2185147) B2185147
theorem B2585951 : Blo 1148636 2585951 := bstep (se 1 (by rfl) ⟨1939463, by rfl⟩ : syracuseStep 2585951 = 3878927) B3878927
theorem B3274145 : Blo 1148636 3274145 := bstep (se 2 (by rfl) ⟨1227804, by rfl⟩ : syracuseStep 3274145 = 2455609) B2455609
theorem B44168651 : Blo 1148636 44168651 := bstep (se 1 (by rfl) ⟨33126488, by rfl⟩ : syracuseStep 44168651 = 66252977) B66252977
theorem B2586347 : Blo 1148636 2586347 := bstep (se 1 (by rfl) ⟨1939760, by rfl⟩ : syracuseStep 2586347 = 3879521) B3879521
theorem B14382877 : Blo 1148636 14382877 := bstep (se 3 (by rfl) ⟨2696789, by rfl⟩ : syracuseStep 14382877 = 5393579) B5393579
theorem B13301597 : Blo 1148636 13301597 := bstep (se 3 (by rfl) ⟨2494049, by rfl⟩ : syracuseStep 13301597 = 4988099) B4988099
theorem B2586473 : Blo 1148636 2586473 := bstep (se 2 (by rfl) ⟨969927, by rfl⟩ : syracuseStep 2586473 = 1939855) B1939855
theorem B2914177 : Blo 1148636 2914177 := bstep (se 2 (by rfl) ⟨1092816, by rfl⟩ : syracuseStep 2914177 = 2185633) B2185633
theorem B4913405 : Blo 1148636 4913405 := bstep (se 3 (by rfl) ⟨921263, by rfl⟩ : syracuseStep 4913405 = 1842527) B1842527
theorem B2914937 : Blo 1148636 2914937 := bstep (se 2 (by rfl) ⟨1093101, by rfl⟩ : syracuseStep 2914937 = 2186203) B2186203
theorem B2914987 : Blo 1148636 2914987 := bstep (se 1 (by rfl) ⟨2186240, by rfl⟩ : syracuseStep 2914987 = 4372481) B4372481
theorem B2587319 : Blo 1148636 2587319 := bstep (se 1 (by rfl) ⟨1940489, by rfl⟩ : syracuseStep 2587319 = 3880979) B3880979
theorem B2587535 : Blo 1148636 2587535 := bstep (se 1 (by rfl) ⟨1940651, by rfl⟩ : syracuseStep 2587535 = 3881303) B3881303
theorem B8289209 : Blo 1148636 8289209 := bstep (se 2 (by rfl) ⟨3108453, by rfl⟩ : syracuseStep 8289209 = 6216907) B6216907
theorem B2915291 : Blo 1148636 2915291 := bstep (se 1 (by rfl) ⟨2186468, by rfl⟩ : syracuseStep 2915291 = 4372937) B4372937
theorem B3112033 : Blo 1148636 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B4914395 : Blo 1148636 4914395 := bstep (se 1 (by rfl) ⟨3685796, by rfl⟩ : syracuseStep 4914395 = 7371593) B7371593
theorem B5602571 : Blo 1148636 5602571 := bstep (se 1 (by rfl) ⟨4201928, by rfl⟩ : syracuseStep 5602571 = 8403857) B8403857
theorem B2915615 : Blo 1148636 2915615 := bstep (se 1 (by rfl) ⟨2186711, by rfl⟩ : syracuseStep 2915615 = 4373423) B4373423
theorem B2456993 : Blo 1148636 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B4488787 : Blo 1148636 4488787 := bstep (se 1 (by rfl) ⟨3366590, by rfl⟩ : syracuseStep 4488787 = 6733181) B6733181
theorem B2588255 : Blo 1148636 2588255 := bstep (se 1 (by rfl) ⟨1941191, by rfl⟩ : syracuseStep 2588255 = 3882383) B3882383
theorem B2621089 : Blo 1148636 2621089 := bstep (se 2 (by rfl) ⟨982908, by rfl⟩ : syracuseStep 2621089 = 1965817) B1965817
theorem B2588471 : Blo 1148636 2588471 := bstep (se 1 (by rfl) ⟨1941353, by rfl⟩ : syracuseStep 2588471 = 3882707) B3882707
theorem B2588903 : Blo 1148636 2588903 := bstep (se 1 (by rfl) ⟨1941677, by rfl⟩ : syracuseStep 2588903 = 3883355) B3883355
theorem B29458889 : Blo 1148636 29458889 := bstep (se 2 (by rfl) ⟨11047083, by rfl⟩ : syracuseStep 29458889 = 22094167) B22094167
theorem B12780071 : Blo 1148636 12780071 := bstep (se 1 (by rfl) ⟨9585053, by rfl⟩ : syracuseStep 12780071 = 19170107) B19170107
theorem B2589497 : Blo 1148636 2589497 := bstep (se 2 (by rfl) ⟨971061, by rfl⟩ : syracuseStep 2589497 = 1942123) B1942123
theorem B2589551 : Blo 1148636 2589551 := bstep (se 1 (by rfl) ⟨1942163, by rfl⟩ : syracuseStep 2589551 = 3884327) B3884327
theorem B1639487 : Blo 1148636 1639487 := bstep (se 1 (by rfl) ⟨1229615, by rfl⟩ : syracuseStep 1639487 = 2459231) B2459231
theorem B2590127 : Blo 1148636 2590127 := bstep (se 1 (by rfl) ⟨1942595, by rfl⟩ : syracuseStep 2590127 = 3885191) B3885191
theorem B1148667 : Blo 1148636 1148667 := bstep (se 1 (by rfl) ⟨861500, by rfl⟩ : syracuseStep 1148667 = 1723001) B1723001
theorem B1148703 : Blo 1148636 1148703 := bstep (se 1 (by rfl) ⟨861527, by rfl⟩ : syracuseStep 1148703 = 1723055) B1723055
theorem B1148735 : Blo 1148636 1148735 := bstep (se 1 (by rfl) ⟨861551, by rfl⟩ : syracuseStep 1148735 = 1723103) B1723103
theorem B2131849 : Blo 1148636 2131849 := bstep (se 2 (by rfl) ⟨799443, by rfl⟩ : syracuseStep 2131849 = 1598887) B1598887
theorem B1148911 : Blo 1148636 1148911 := bstep (se 1 (by rfl) ⟨861683, by rfl⟩ : syracuseStep 1148911 = 1723367) B1723367
theorem B1149083 : Blo 1148636 1149083 := bstep (se 1 (by rfl) ⟨861812, by rfl⟩ : syracuseStep 1149083 = 1723625) B1723625
theorem B1149119 : Blo 1148636 1149119 := bstep (se 1 (by rfl) ⟨861839, by rfl⟩ : syracuseStep 1149119 = 1723679) B1723679
theorem B2590955 : Blo 1148636 2590955 := bstep (se 1 (by rfl) ⟨1943216, by rfl⟩ : syracuseStep 2590955 = 3886433) B3886433
theorem B1640683 : Blo 1148636 1640683 := bstep (se 1 (by rfl) ⟨1230512, by rfl⟩ : syracuseStep 1640683 = 2461025) B2461025
theorem B2459897 : Blo 1148636 2459897 := bstep (se 2 (by rfl) ⟨922461, by rfl⟩ : syracuseStep 2459897 = 1844923) B1844923
theorem B1149231 : Blo 1148636 1149231 := bstep (se 1 (by rfl) ⟨861923, by rfl⟩ : syracuseStep 1149231 = 1723847) B1723847
theorem B1149467 : Blo 1148636 1149467 := bstep (se 1 (by rfl) ⟨862100, by rfl⟩ : syracuseStep 1149467 = 1724201) B1724201
theorem B1149471 : Blo 1148636 1149471 := bstep (se 1 (by rfl) ⟨862103, by rfl⟩ : syracuseStep 1149471 = 1724207) B1724207
theorem B1149787 : Blo 1148636 1149787 := bstep (se 1 (by rfl) ⟨862340, by rfl⟩ : syracuseStep 1149787 = 1724681) B1724681
theorem B1149855 : Blo 1148636 1149855 := bstep (se 1 (by rfl) ⟨862391, by rfl⟩ : syracuseStep 1149855 = 1724783) B1724783
theorem B1149999 : Blo 1148636 1149999 := bstep (se 1 (by rfl) ⟨862499, by rfl⟩ : syracuseStep 1149999 = 1724999) B1724999
theorem B1150023 : Blo 1148636 1150023 := bstep (se 1 (by rfl) ⟨862517, by rfl⟩ : syracuseStep 1150023 = 1725035) B1725035
theorem B1150175 : Blo 1148636 1150175 := bstep (se 1 (by rfl) ⟨862631, by rfl⟩ : syracuseStep 1150175 = 1725263) B1725263
theorem B4918495 : Blo 1148636 4918495 := bstep (se 1 (by rfl) ⟨3688871, by rfl⟩ : syracuseStep 4918495 = 7377743) B7377743
theorem B1150439 : Blo 1148636 1150439 := bstep (se 1 (by rfl) ⟨862829, by rfl⟩ : syracuseStep 1150439 = 1725659) B1725659
theorem B2592251 : Blo 1148636 2592251 := bstep (se 1 (by rfl) ⟨1944188, by rfl⟩ : syracuseStep 2592251 = 3888377) B3888377
theorem B1150555 : Blo 1148636 1150555 := bstep (se 1 (by rfl) ⟨862916, by rfl⟩ : syracuseStep 1150555 = 1725833) B1725833
theorem B2592431 : Blo 1148636 2592431 := bstep (se 1 (by rfl) ⟨1944323, by rfl⟩ : syracuseStep 2592431 = 3888647) B3888647
theorem B1150791 : Blo 1148636 1150791 := bstep (se 1 (by rfl) ⟨863093, by rfl⟩ : syracuseStep 1150791 = 1726187) B1726187
theorem B1150943 : Blo 1148636 1150943 := bstep (se 1 (by rfl) ⟨863207, by rfl⟩ : syracuseStep 1150943 = 1726415) B1726415
theorem B1151207 : Blo 1148636 1151207 := bstep (se 1 (by rfl) ⟨863405, by rfl⟩ : syracuseStep 1151207 = 1726811) B1726811
theorem B3281161 : Blo 1148636 3281161 := bstep (se 2 (by rfl) ⟨1230435, by rfl⟩ : syracuseStep 3281161 = 2460871) B2460871
theorem B2593079 : Blo 1148636 2593079 := bstep (se 1 (by rfl) ⟨1944809, by rfl⟩ : syracuseStep 2593079 = 3889619) B3889619
theorem B1151359 : Blo 1148636 1151359 := bstep (se 1 (by rfl) ⟨863519, by rfl⟩ : syracuseStep 1151359 = 1727039) B1727039
theorem B2593151 : Blo 1148636 2593151 := bstep (se 1 (by rfl) ⟨1944863, by rfl⟩ : syracuseStep 2593151 = 3889727) B3889727
theorem B1151439 : Blo 1148636 1151439 := bstep (se 1 (by rfl) ⟨863579, by rfl⟩ : syracuseStep 1151439 = 1727159) B1727159
theorem B19665503 : Blo 1148636 19665503 := bstep (se 1 (by rfl) ⟨14749127, by rfl⟩ : syracuseStep 19665503 = 29498255) B29498255
theorem B1151591 : Blo 1148636 1151591 := bstep (se 1 (by rfl) ⟨863693, by rfl⟩ : syracuseStep 1151591 = 1727387) B1727387
theorem B8295209 : Blo 1148636 8295209 := bstep (se 2 (by rfl) ⟨3110703, by rfl⟩ : syracuseStep 8295209 = 6221407) B6221407
theorem B1151855 : Blo 1148636 1151855 := bstep (se 1 (by rfl) ⟨863891, by rfl⟩ : syracuseStep 1151855 = 1727783) B1727783
theorem B10490771 : Blo 1148636 10490771 := bstep (se 1 (by rfl) ⟨7868078, by rfl⟩ : syracuseStep 10490771 = 15736157) B15736157
theorem B1938343 : Blo 1148636 1938343 := bstep (se 1 (by rfl) ⟨1453757, by rfl⟩ : syracuseStep 1938343 = 2907515) B2907515
theorem B1151911 : Blo 1148636 1151911 := bstep (se 1 (by rfl) ⟨863933, by rfl⟩ : syracuseStep 1151911 = 1727867) B1727867
theorem B1151995 : Blo 1148636 1151995 := bstep (se 1 (by rfl) ⟨863996, by rfl⟩ : syracuseStep 1151995 = 1727993) B1727993
theorem B1152063 : Blo 1148636 1152063 := bstep (se 1 (by rfl) ⟨864047, by rfl⟩ : syracuseStep 1152063 = 1728095) B1728095
theorem B1938505 : Blo 1148636 1938505 := bstep (se 2 (by rfl) ⟨726939, by rfl⟩ : syracuseStep 1938505 = 1453879) B1453879
theorem B1938539 : Blo 1148636 1938539 := bstep (se 1 (by rfl) ⟨1453904, by rfl⟩ : syracuseStep 1938539 = 2907809) B2907809
theorem B3282095 : Blo 1148636 3282095 := bstep (se 1 (by rfl) ⟨2461571, by rfl⟩ : syracuseStep 3282095 = 4923143) B4923143
theorem B1152207 : Blo 1148636 1152207 := bstep (se 1 (by rfl) ⟨864155, by rfl⟩ : syracuseStep 1152207 = 1728311) B1728311
theorem B1152411 : Blo 1148636 1152411 := bstep (se 1 (by rfl) ⟨864308, by rfl⟩ : syracuseStep 1152411 = 1728617) B1728617
theorem B14751179 : Blo 1148636 14751179 := bstep (se 1 (by rfl) ⟨11063384, by rfl⟩ : syracuseStep 14751179 = 22126769) B22126769
theorem B1152623 : Blo 1148636 1152623 := bstep (se 1 (by rfl) ⟨864467, by rfl⟩ : syracuseStep 1152623 = 1728935) B1728935
theorem B4921145 : Blo 1148636 4921145 := bstep (se 2 (by rfl) ⟨1845429, by rfl⟩ : syracuseStep 4921145 = 3690859) B3690859
theorem B5904343 : Blo 1148636 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B6559703 : Blo 1148636 6559703 := bstep (se 1 (by rfl) ⟨4919777, by rfl⟩ : syracuseStep 6559703 = 9839555) B9839555
theorem B2180585461 : Blo 1148636 2180585461 := bstep (se 5 (by rfl) ⟨102214943, by rfl⟩ : syracuseStep 2180585461 = 204429887) B204429887
theorem B1841143 : Blo 1148636 1841143 := bstep (se 1 (by rfl) ⟨1380857, by rfl⟩ : syracuseStep 1841143 = 2761715) B2761715
theorem B1939835 : Blo 1148636 1939835 := bstep (se 1 (by rfl) ⟨1454876, by rfl⟩ : syracuseStep 1939835 = 2909753) B2909753
theorem B6822319 : Blo 1148636 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B14752205 : Blo 1148636 14752205 := bstep (se 3 (by rfl) ⟨2766038, by rfl⟩ : syracuseStep 14752205 = 5532077) B5532077
theorem B7870931 : Blo 1148636 7870931 := bstep (se 1 (by rfl) ⟨5903198, by rfl⟩ : syracuseStep 7870931 = 11806397) B11806397
theorem B1940105 : Blo 1148636 1940105 := bstep (se 2 (by rfl) ⟨727539, by rfl⟩ : syracuseStep 1940105 = 1455079) B1455079
theorem B2956115 : Blo 1148636 2956115 := bstep (se 1 (by rfl) ⟨2217086, by rfl⟩ : syracuseStep 2956115 = 4434173) B4434173
theorem B4365161 : Blo 1148636 4365161 := bstep (se 2 (by rfl) ⟨1636935, by rfl⟩ : syracuseStep 4365161 = 3273871) B3273871
theorem B2071531 : Blo 1148636 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B9969095 : Blo 1148636 9969095 := bstep (se 1 (by rfl) ⟨7476821, by rfl⟩ : syracuseStep 9969095 = 14953643) B14953643
theorem B19177169 : Blo 1148636 19177169 := bstep (se 2 (by rfl) ⟨7191438, by rfl⟩ : syracuseStep 19177169 = 14382877) B14382877
theorem B7380715 : Blo 1148636 7380715 := bstep (se 1 (by rfl) ⟨5535536, by rfl⟩ : syracuseStep 7380715 = 11071073) B11071073
theorem B1384231 : Blo 1148636 1384231 := bstep (se 1 (by rfl) ⟨1038173, by rfl⟩ : syracuseStep 1384231 = 2076347) B2076347
theorem B3547003 : Blo 1148636 3547003 := bstep (se 1 (by rfl) ⟨2660252, by rfl⟩ : syracuseStep 3547003 = 5320505) B5320505
theorem B1941691 : Blo 1148636 1941691 := bstep (se 1 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 1941691 = 2912537) B2912537
theorem B1941887 : Blo 1148636 1941887 := bstep (se 1 (by rfl) ⟨1456415, by rfl⟩ : syracuseStep 1941887 = 2912831) B2912831
theorem B9839177 : Blo 1148636 9839177 := bstep (se 2 (by rfl) ⟨3689691, by rfl⟩ : syracuseStep 9839177 = 7379383) B7379383
theorem B1843975 : Blo 1148636 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B1942319 : Blo 1148636 1942319 := bstep (se 1 (by rfl) ⟨1456739, by rfl⟩ : syracuseStep 1942319 = 2913479) B2913479
theorem B2336377 : Blo 1148636 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B1943291 : Blo 1148636 1943291 := bstep (se 1 (by rfl) ⟨1457468, by rfl⟩ : syracuseStep 1943291 = 2914937) B2914937
theorem B24848329 : Blo 1148636 24848329 := bstep (se 2 (by rfl) ⟨9318123, by rfl⟩ : syracuseStep 24848329 = 18636247) B18636247
theorem B1943527 : Blo 1148636 1943527 := bstep (se 1 (by rfl) ⟨1457645, by rfl⟩ : syracuseStep 1943527 = 2915291) B2915291
theorem B1943743 : Blo 1148636 1943743 := bstep (se 1 (by rfl) ⟨1457807, by rfl⟩ : syracuseStep 1943743 = 2915615) B2915615
theorem B1845551 : Blo 1148636 1845551 := bstep (se 1 (by rfl) ⟨1384163, by rfl⟩ : syracuseStep 1845551 = 2768327) B2768327
theorem B2763271 : Blo 1148636 2763271 := bstep (se 1 (by rfl) ⟨2072453, by rfl⟩ : syracuseStep 2763271 = 4144907) B4144907
theorem B4369079 : Blo 1148636 4369079 := bstep (se 1 (by rfl) ⟨3276809, by rfl⟩ : syracuseStep 4369079 = 6553619) B6553619
theorem B2075323 : Blo 1148636 2075323 := bstep (se 1 (by rfl) ⟨1556492, by rfl⟩ : syracuseStep 2075323 = 3112985) B3112985
theorem B1944479 : Blo 1148636 1944479 := bstep (se 1 (by rfl) ⟨1458359, by rfl⟩ : syracuseStep 1944479 = 2916719) B2916719
theorem B3878009 : Blo 1148636 3878009 := bstep (se 2 (by rfl) ⟨1454253, by rfl⟩ : syracuseStep 3878009 = 2908507) B2908507
theorem B1944911 : Blo 1148636 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B3878333 : Blo 1148636 3878333 := bstep (se 3 (by rfl) ⟨727187, by rfl⟩ : syracuseStep 3878333 = 1454375) B1454375
theorem B80686631 : Blo 1148636 80686631 := bstep (se 1 (by rfl) ⟨60514973, by rfl⟩ : syracuseStep 80686631 = 121029947) B121029947
theorem B3879035 : Blo 1148636 3879035 := bstep (se 1 (by rfl) ⟨2909276, by rfl⟩ : syracuseStep 3879035 = 5818553) B5818553
theorem B3879197 : Blo 1148636 3879197 := bstep (se 3 (by rfl) ⟨727349, by rfl⟩ : syracuseStep 3879197 = 1454699) B1454699
theorem B3879305 : Blo 1148636 3879305 := bstep (se 2 (by rfl) ⟨1454739, by rfl⟩ : syracuseStep 3879305 = 2909479) B2909479
theorem B4371191 : Blo 1148636 4371191 := bstep (se 1 (by rfl) ⟨3278393, by rfl⟩ : syracuseStep 4371191 = 6556787) B6556787
theorem B9843551 : Blo 1148636 9843551 := bstep (se 1 (by rfl) ⟨7382663, by rfl⟩ : syracuseStep 9843551 = 14765327) B14765327
theorem B63877987 : Blo 1148636 63877987 := bstep (se 1 (by rfl) ⟨47908490, by rfl⟩ : syracuseStep 63877987 = 95816981) B95816981
theorem B19674251 : Blo 1148636 19674251 := bstep (se 1 (by rfl) ⟨14755688, by rfl⟩ : syracuseStep 19674251 = 29511377) B29511377
theorem B4142299 : Blo 1148636 4142299 := bstep (se 1 (by rfl) ⟨3106724, by rfl⟩ : syracuseStep 4142299 = 6213449) B6213449
theorem B3880223 : Blo 1148636 3880223 := bstep (se 1 (by rfl) ⟨2910167, by rfl⟩ : syracuseStep 3880223 = 5820335) B5820335
theorem B1455727 : Blo 1148636 1455727 := bstep (se 1 (by rfl) ⟨1091795, by rfl⟩ : syracuseStep 1455727 = 2183591) B2183591
theorem B13088465 : Blo 1148636 13088465 := bstep (se 2 (by rfl) ⟨4908174, by rfl⟩ : syracuseStep 13088465 = 9816349) B9816349
theorem B13973393 : Blo 1148636 13973393 := bstep (se 2 (by rfl) ⟨5240022, by rfl⟩ : syracuseStep 13973393 = 10480045) B10480045
theorem B9975773 : Blo 1148636 9975773 := bstep (se 3 (by rfl) ⟨1870457, by rfl⟩ : syracuseStep 9975773 = 3740915) B3740915
theorem B1456319 : Blo 1148636 1456319 := bstep (se 1 (by rfl) ⟨1092239, by rfl⟩ : syracuseStep 1456319 = 2184479) B2184479
theorem B1292827 : Blo 1148636 1292827 := bstep (se 1 (by rfl) ⟨969620, by rfl⟩ : syracuseStep 1292827 = 1939241) B1939241
theorem B4143955 : Blo 1148636 4143955 := bstep (se 1 (by rfl) ⟨3107966, by rfl⟩ : syracuseStep 4143955 = 6215933) B6215933
theorem B2800543 : Blo 1148636 2800543 := bstep (se 1 (by rfl) ⟨2100407, by rfl⟩ : syracuseStep 2800543 = 4200815) B4200815
theorem B1227847 : Blo 1148636 1227847 := bstep (se 1 (by rfl) ⟨920885, by rfl⟩ : syracuseStep 1227847 = 1841771) B1841771
theorem B3882113 : Blo 1148636 3882113 := bstep (se 2 (by rfl) ⟨1455792, by rfl⟩ : syracuseStep 3882113 = 2911585) B2911585
theorem B3882167 : Blo 1148636 3882167 := bstep (se 1 (by rfl) ⟨2911625, by rfl⟩ : syracuseStep 3882167 = 5823251) B5823251
theorem B3685591 : Blo 1148636 3685591 := bstep (se 1 (by rfl) ⟨2764193, by rfl⟩ : syracuseStep 3685591 = 5528387) B5528387
theorem B1293799 : Blo 1148636 1293799 := bstep (se 1 (by rfl) ⟨970349, by rfl⟩ : syracuseStep 1293799 = 1940699) B1940699
theorem B56835665 : Blo 1148636 56835665 := bstep (se 2 (by rfl) ⟨21313374, by rfl⟩ : syracuseStep 56835665 = 42626749) B42626749
theorem B4374107 : Blo 1148636 4374107 := bstep (se 1 (by rfl) ⟨3280580, by rfl⟩ : syracuseStep 4374107 = 6561161) B6561161
theorem B8306363 : Blo 1148636 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B26590913 : Blo 1148636 26590913 := bstep (se 2 (by rfl) ⟨9971592, by rfl⟩ : syracuseStep 26590913 = 19943185) B19943185
theorem B1228667 : Blo 1148636 1228667 := bstep (se 1 (by rfl) ⟨921500, by rfl⟩ : syracuseStep 1228667 = 1843001) B1843001
theorem B3882923 : Blo 1148636 3882923 := bstep (se 1 (by rfl) ⟨2912192, by rfl⟩ : syracuseStep 3882923 = 5824385) B5824385
theorem B1294303 : Blo 1148636 1294303 := bstep (se 1 (by rfl) ⟨970727, by rfl⟩ : syracuseStep 1294303 = 1941455) B1941455
theorem B1622327 : Blo 1148636 1622327 := bstep (se 1 (by rfl) ⟨1216745, by rfl⟩ : syracuseStep 1622327 = 2433491) B2433491
theorem B4145527 : Blo 1148636 4145527 := bstep (se 1 (by rfl) ⟨3109145, by rfl⟩ : syracuseStep 4145527 = 6218291) B6218291
theorem B3883463 : Blo 1148636 3883463 := bstep (se 1 (by rfl) ⟨2912597, by rfl⟩ : syracuseStep 3883463 = 5825195) B5825195
theorem B3686975 : Blo 1148636 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B1294951 : Blo 1148636 1294951 := bstep (se 1 (by rfl) ⟨971213, by rfl⟩ : syracuseStep 1294951 = 1942427) B1942427
theorem B3883787 : Blo 1148636 3883787 := bstep (se 1 (by rfl) ⟨2912840, by rfl⟩ : syracuseStep 3883787 = 5825681) B5825681
theorem B4670351 : Blo 1148636 4670351 := bstep (se 1 (by rfl) ⟨3502763, by rfl⟩ : syracuseStep 4670351 = 7005527) B7005527
theorem B3884057 : Blo 1148636 3884057 := bstep (se 2 (by rfl) ⟨1456521, by rfl⟩ : syracuseStep 3884057 = 2913043) B2913043
theorem B13124915 : Blo 1148636 13124915 := bstep (se 1 (by rfl) ⟨9843686, by rfl⟩ : syracuseStep 13124915 = 19687373) B19687373
theorem B19678625 : Blo 1148636 19678625 := bstep (se 2 (by rfl) ⟨7379484, by rfl⟩ : syracuseStep 19678625 = 14758969) B14758969
theorem B3884705 : Blo 1148636 3884705 := bstep (se 2 (by rfl) ⟨1456764, by rfl⟩ : syracuseStep 3884705 = 2913529) B2913529
theorem B14731085 : Blo 1148636 14731085 := bstep (se 3 (by rfl) ⟨2762078, by rfl⟩ : syracuseStep 14731085 = 5524157) B5524157
theorem B23578543 : Blo 1148636 23578543 := bstep (se 1 (by rfl) ⟨17683907, by rfl⟩ : syracuseStep 23578543 = 35367815) B35367815
theorem B5818715 : Blo 1148636 5818715 := bstep (se 1 (by rfl) ⟨4364036, by rfl⟩ : syracuseStep 5818715 = 8728073) B8728073
theorem B3885407 : Blo 1148636 3885407 := bstep (se 1 (by rfl) ⟨2914055, by rfl⟩ : syracuseStep 3885407 = 5828111) B5828111
theorem B3885569 : Blo 1148636 3885569 := bstep (se 2 (by rfl) ⟨1457088, by rfl⟩ : syracuseStep 3885569 = 2914177) B2914177
theorem B1723295 : Blo 1148636 1723295 := bstep (se 1 (by rfl) ⟨1292471, by rfl⟩ : syracuseStep 1723295 = 2584943) B2584943
theorem B1723343 : Blo 1148636 1723343 := bstep (se 1 (by rfl) ⟨1292507, by rfl⟩ : syracuseStep 1723343 = 2585015) B2585015
theorem B3689435 : Blo 1148636 3689435 := bstep (se 1 (by rfl) ⟨2767076, by rfl⟩ : syracuseStep 3689435 = 5534153) B5534153
theorem B3886055 : Blo 1148636 3886055 := bstep (se 1 (by rfl) ⟨2914541, by rfl⟩ : syracuseStep 3886055 = 5829083) B5829083
theorem B1723433 : Blo 1148636 1723433 := bstep (se 2 (by rfl) ⟨646287, by rfl⟩ : syracuseStep 1723433 = 1292575) B1292575
theorem B1723439 : Blo 1148636 1723439 := bstep (se 1 (by rfl) ⟨1292579, by rfl⟩ : syracuseStep 1723439 = 2585159) B2585159
theorem B1723463 : Blo 1148636 1723463 := bstep (se 1 (by rfl) ⟨1292597, by rfl⟩ : syracuseStep 1723463 = 2585195) B2585195
theorem B3886379 : Blo 1148636 3886379 := bstep (se 1 (by rfl) ⟨2914784, by rfl⟩ : syracuseStep 3886379 = 5829569) B5829569
theorem B1723727 : Blo 1148636 1723727 := bstep (se 1 (by rfl) ⟨1292795, by rfl⟩ : syracuseStep 1723727 = 2585591) B2585591
theorem B1723817 : Blo 1148636 1723817 := bstep (se 2 (by rfl) ⟨646431, by rfl⟩ : syracuseStep 1723817 = 1292863) B1292863
theorem B3689975 : Blo 1148636 3689975 := bstep (se 1 (by rfl) ⟨2767481, by rfl⟩ : syracuseStep 3689975 = 5534963) B5534963
theorem B3886649 : Blo 1148636 3886649 := bstep (se 2 (by rfl) ⟨1457493, by rfl⟩ : syracuseStep 3886649 = 2914987) B2914987
theorem B1723967 : Blo 1148636 1723967 := bstep (se 1 (by rfl) ⟨1292975, by rfl⟩ : syracuseStep 1723967 = 2585951) B2585951
theorem B5525081 : Blo 1148636 5525081 := bstep (se 2 (by rfl) ⟨2071905, by rfl⟩ : syracuseStep 5525081 = 4143811) B4143811
theorem B5820011 : Blo 1148636 5820011 := bstep (se 1 (by rfl) ⟨4365008, by rfl⟩ : syracuseStep 5820011 = 8730017) B8730017
theorem B2182763 : Blo 1148636 2182763 := bstep (se 1 (by rfl) ⟨1637072, by rfl⟩ : syracuseStep 2182763 = 3274145) B3274145
theorem B29445767 : Blo 1148636 29445767 := bstep (se 1 (by rfl) ⟨22084325, by rfl⟩ : syracuseStep 29445767 = 44168651) B44168651
theorem B1724231 : Blo 1148636 1724231 := bstep (se 1 (by rfl) ⟨1293173, by rfl⟩ : syracuseStep 1724231 = 2586347) B2586347
theorem B8867731 : Blo 1148636 8867731 := bstep (se 1 (by rfl) ⟨6650798, by rfl⟩ : syracuseStep 8867731 = 13301597) B13301597
theorem B1724315 : Blo 1148636 1724315 := bstep (se 1 (by rfl) ⟨1293236, by rfl⟩ : syracuseStep 1724315 = 2586473) B2586473
theorem B4149377 : Blo 1148636 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B9818333 : Blo 1148636 9818333 := bstep (se 3 (by rfl) ⟨1840937, by rfl⟩ : syracuseStep 9818333 = 3681875) B3681875
theorem B1724879 : Blo 1148636 1724879 := bstep (se 1 (by rfl) ⟨1293659, by rfl⟩ : syracuseStep 1724879 = 2587319) B2587319
theorem B1167823 : Blo 1148636 1167823 := bstep (se 1 (by rfl) ⟨875867, by rfl⟩ : syracuseStep 1167823 = 1751735) B1751735
theorem B1724921 : Blo 1148636 1724921 := bstep (se 2 (by rfl) ⟨646845, by rfl⟩ : syracuseStep 1724921 = 1293691) B1293691
theorem B14012999 : Blo 1148636 14012999 := bstep (se 1 (by rfl) ⟨10509749, by rfl⟩ : syracuseStep 14012999 = 21019499) B21019499
theorem B1725023 : Blo 1148636 1725023 := bstep (se 1 (by rfl) ⟨1293767, by rfl⟩ : syracuseStep 1725023 = 2587535) B2587535
theorem B5526139 : Blo 1148636 5526139 := bstep (se 1 (by rfl) ⟨4144604, by rfl⟩ : syracuseStep 5526139 = 8289209) B8289209
theorem B5985049 : Blo 1148636 5985049 := bstep (se 2 (by rfl) ⟨2244393, by rfl⟩ : syracuseStep 5985049 = 4488787) B4488787
theorem B3494785 : Blo 1148636 3494785 := bstep (se 2 (by rfl) ⟨1310544, by rfl⟩ : syracuseStep 3494785 = 2621089) B2621089
theorem B1725503 : Blo 1148636 1725503 := bstep (se 1 (by rfl) ⟨1294127, by rfl⟩ : syracuseStep 1725503 = 2588255) B2588255
theorem B1725545 : Blo 1148636 1725545 := bstep (se 2 (by rfl) ⟨647079, by rfl⟩ : syracuseStep 1725545 = 1294159) B1294159
theorem B1725647 : Blo 1148636 1725647 := bstep (se 1 (by rfl) ⟨1294235, by rfl⟩ : syracuseStep 1725647 = 2588471) B2588471
theorem B5821793 : Blo 1148636 5821793 := bstep (se 2 (by rfl) ⟨2183172, by rfl⟩ : syracuseStep 5821793 = 4366345) B4366345
theorem B13981081 : Blo 1148636 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B1725851 : Blo 1148636 1725851 := bstep (se 1 (by rfl) ⟨1294388, by rfl⟩ : syracuseStep 1725851 = 2588777) B2588777
theorem B3888539 : Blo 1148636 3888539 := bstep (se 1 (by rfl) ⟨2916404, by rfl⟩ : syracuseStep 3888539 = 5832809) B5832809
theorem B6542957 : Blo 1148636 6542957 := bstep (se 3 (by rfl) ⟨1226804, by rfl⟩ : syracuseStep 6542957 = 2453609) B2453609
theorem B1726073 : Blo 1148636 1726073 := bstep (se 2 (by rfl) ⟨647277, by rfl⟩ : syracuseStep 1726073 = 1294555) B1294555
theorem B1726175 : Blo 1148636 1726175 := bstep (se 1 (by rfl) ⟨1294631, by rfl⟩ : syracuseStep 1726175 = 2589263) B2589263
theorem B1726271 : Blo 1148636 1726271 := bstep (se 1 (by rfl) ⟨1294703, by rfl⟩ : syracuseStep 1726271 = 2589407) B2589407
theorem B14767991 : Blo 1148636 14767991 := bstep (se 1 (by rfl) ⟨11075993, by rfl⟩ : syracuseStep 14767991 = 22151987) B22151987
theorem B1726439 : Blo 1148636 1726439 := bstep (se 1 (by rfl) ⟨1294829, by rfl⟩ : syracuseStep 1726439 = 2589659) B2589659
theorem B1726457 : Blo 1148636 1726457 := bstep (se 2 (by rfl) ⟨647421, by rfl⟩ : syracuseStep 1726457 = 1294843) B1294843
theorem B3692537 : Blo 1148636 3692537 := bstep (se 2 (by rfl) ⟨1384701, by rfl⟩ : syracuseStep 3692537 = 2769403) B2769403
theorem B15751169 : Blo 1148636 15751169 := bstep (se 2 (by rfl) ⟨5906688, by rfl⟩ : syracuseStep 15751169 = 11813377) B11813377
theorem B1726559 : Blo 1148636 1726559 := bstep (se 1 (by rfl) ⟨1294919, by rfl⟩ : syracuseStep 1726559 = 2589839) B2589839
theorem B3889295 : Blo 1148636 3889295 := bstep (se 1 (by rfl) ⟨2916971, by rfl⟩ : syracuseStep 3889295 = 5833943) B5833943
theorem B1726619 : Blo 1148636 1726619 := bstep (se 1 (by rfl) ⟨1294964, by rfl⟩ : syracuseStep 1726619 = 2589929) B2589929
theorem B1726655 : Blo 1148636 1726655 := bstep (se 1 (by rfl) ⟨1294991, by rfl⟩ : syracuseStep 1726655 = 2589983) B2589983
theorem B1726697 : Blo 1148636 1726697 := bstep (se 2 (by rfl) ⟨647511, by rfl⟩ : syracuseStep 1726697 = 1295023) B1295023
theorem B15718643 : Blo 1148636 15718643 := bstep (se 1 (by rfl) ⟨11788982, by rfl⟩ : syracuseStep 15718643 = 23577965) B23577965
theorem B1727003 : Blo 1148636 1727003 := bstep (se 1 (by rfl) ⟨1295252, by rfl⟩ : syracuseStep 1727003 = 2590505) B2590505
theorem B1727081 : Blo 1148636 1727081 := bstep (se 2 (by rfl) ⟨647655, by rfl⟩ : syracuseStep 1727081 = 1295311) B1295311
theorem B1727609 : Blo 1148636 1727609 := bstep (se 2 (by rfl) ⟨647853, by rfl⟩ : syracuseStep 1727609 = 1295707) B1295707
theorem B2186423 : Blo 1148636 2186423 := bstep (se 1 (by rfl) ⟨1639817, by rfl⟩ : syracuseStep 2186423 = 3279635) B3279635
theorem B1727711 : Blo 1148636 1727711 := bstep (se 1 (by rfl) ⟨1295783, by rfl⟩ : syracuseStep 1727711 = 2591567) B2591567
theorem B1727753 : Blo 1148636 1727753 := bstep (se 2 (by rfl) ⟨647907, by rfl⟩ : syracuseStep 1727753 = 1295815) B1295815
theorem B1727855 : Blo 1148636 1727855 := bstep (se 1 (by rfl) ⟨1295891, by rfl⟩ : syracuseStep 1727855 = 2591783) B2591783
theorem B6544871 : Blo 1148636 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B1727975 : Blo 1148636 1727975 := bstep (se 1 (by rfl) ⟨1295981, by rfl⟩ : syracuseStep 1727975 = 2591963) B2591963
theorem B1728107 : Blo 1148636 1728107 := bstep (se 1 (by rfl) ⟨1296080, by rfl⟩ : syracuseStep 1728107 = 2592161) B2592161
theorem B1728233 : Blo 1148636 1728233 := bstep (se 2 (by rfl) ⟨648087, by rfl⟩ : syracuseStep 1728233 = 1296175) B1296175
theorem B1728377 : Blo 1148636 1728377 := bstep (se 2 (by rfl) ⟨648141, by rfl⟩ : syracuseStep 1728377 = 1296283) B1296283
theorem B1728479 : Blo 1148636 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B1728731 : Blo 1148636 1728731 := bstep (se 1 (by rfl) ⟨1296548, by rfl⟩ : syracuseStep 1728731 = 2593097) B2593097
theorem B1728743 : Blo 1148636 1728743 := bstep (se 1 (by rfl) ⟨1296557, by rfl⟩ : syracuseStep 1728743 = 2593115) B2593115
theorem B1728905 : Blo 1148636 1728905 := bstep (se 2 (by rfl) ⟨648339, by rfl⟩ : syracuseStep 1728905 = 1296679) B1296679
theorem B2908649 : Blo 1148636 2908649 := bstep (se 2 (by rfl) ⟨1090743, by rfl⟩ : syracuseStep 2908649 = 2181487) B2181487
theorem B5595787 : Blo 1148636 5595787 := bstep (se 1 (by rfl) ⟨4196840, by rfl⟩ : syracuseStep 5595787 = 8393681) B8393681
theorem B74834603 : Blo 1148636 74834603 := bstep (se 1 (by rfl) ⟨56125952, by rfl⟩ : syracuseStep 74834603 = 112251905) B112251905
theorem B11068271 : Blo 1148636 11068271 := bstep (se 1 (by rfl) ⟨8301203, by rfl⟩ : syracuseStep 11068271 = 16602407) B16602407
theorem B5596723 : Blo 1148636 5596723 := bstep (se 1 (by rfl) ⟨4197542, by rfl⟩ : syracuseStep 5596723 = 8395085) B8395085
theorem B2909915 : Blo 1148636 2909915 := bstep (se 1 (by rfl) ⟨2182436, by rfl⟩ : syracuseStep 2909915 = 4364873) B4364873
theorem B8283991 : Blo 1148636 8283991 := bstep (se 1 (by rfl) ⟨6212993, by rfl⟩ : syracuseStep 8283991 = 12425987) B12425987
theorem B29485133 : Blo 1148636 29485133 := bstep (se 3 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 29485133 = 11056925) B11056925
theorem B5826977 : Blo 1148636 5826977 := bstep (se 2 (by rfl) ⟨2185116, by rfl⟩ : syracuseStep 5826977 = 4370233) B4370233
theorem B6548039 : Blo 1148636 6548039 := bstep (se 1 (by rfl) ⟨4911029, by rfl⟩ : syracuseStep 6548039 = 9822059) B9822059
theorem B2911211 : Blo 1148636 2911211 := bstep (se 1 (by rfl) ⟨2183408, by rfl⟩ : syracuseStep 2911211 = 4366817) B4366817
theorem B3272015 : Blo 1148636 3272015 := bstep (se 1 (by rfl) ⟨2454011, by rfl⟩ : syracuseStep 3272015 = 4908023) B4908023
theorem B5827949 : Blo 1148636 5827949 := bstep (se 3 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 5827949 = 2185481) B2185481
theorem B15756743 : Blo 1148636 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B16576163 : Blo 1148636 16576163 := bstep (se 1 (by rfl) ⟨12432122, by rfl⟩ : syracuseStep 16576163 = 24864245) B24864245
theorem B2584475 : Blo 1148636 2584475 := bstep (se 1 (by rfl) ⟨1938356, by rfl⟩ : syracuseStep 2584475 = 3876713) B3876713
theorem B7368671 : Blo 1148636 7368671 := bstep (se 1 (by rfl) ⟨5526503, by rfl⟩ : syracuseStep 7368671 = 11053007) B11053007
theorem B7368823 : Blo 1148636 7368823 := bstep (se 1 (by rfl) ⟨5526617, by rfl⟩ : syracuseStep 7368823 = 11053235) B11053235
theorem B2453627 : Blo 1148636 2453627 := bstep (se 1 (by rfl) ⟨1840220, by rfl⟩ : syracuseStep 2453627 = 3680441) B3680441
theorem B8745083 : Blo 1148636 8745083 := bstep (se 1 (by rfl) ⟨6558812, by rfl⟩ : syracuseStep 8745083 = 13117625) B13117625
theorem B2584763 : Blo 1148636 2584763 := bstep (se 1 (by rfl) ⟨1938572, by rfl⟩ : syracuseStep 2584763 = 3877145) B3877145
theorem B8843687 : Blo 1148636 8843687 := bstep (se 1 (by rfl) ⟨6632765, by rfl⟩ : syracuseStep 8843687 = 13265531) B13265531
theorem B2585249 : Blo 1148636 2585249 := bstep (se 2 (by rfl) ⟨969468, by rfl⟩ : syracuseStep 2585249 = 1938937) B1938937
theorem B7369643 : Blo 1148636 7369643 := bstep (se 1 (by rfl) ⟨5527232, by rfl⟩ : syracuseStep 7369643 = 11054465) B11054465
theorem B2585609 : Blo 1148636 2585609 := bstep (se 2 (by rfl) ⟨969603, by rfl⟩ : syracuseStep 2585609 = 1939207) B1939207
theorem B2585663 : Blo 1148636 2585663 := bstep (se 1 (by rfl) ⟨1939247, by rfl⟩ : syracuseStep 2585663 = 3878495) B3878495
theorem B2913691 : Blo 1148636 2913691 := bstep (se 1 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 2913691 = 4370537) B4370537
theorem B7370311 : Blo 1148636 7370311 := bstep (se 1 (by rfl) ⟨5527733, by rfl⟩ : syracuseStep 7370311 = 11055467) B11055467
theorem B5830379 : Blo 1148636 5830379 := bstep (se 1 (by rfl) ⟨4372784, by rfl⟩ : syracuseStep 5830379 = 8745569) B8745569
theorem B2586599 : Blo 1148636 2586599 := bstep (se 1 (by rfl) ⟨1939949, by rfl⟩ : syracuseStep 2586599 = 3879899) B3879899
theorem B2586617 : Blo 1148636 2586617 := bstep (se 2 (by rfl) ⟨969981, by rfl⟩ : syracuseStep 2586617 = 1939963) B1939963
theorem B2586707 : Blo 1148636 2586707 := bstep (se 1 (by rfl) ⟨1940030, by rfl⟩ : syracuseStep 2586707 = 3880061) B3880061
theorem B9959507 : Blo 1148636 9959507 := bstep (se 1 (by rfl) ⟨7469630, by rfl⟩ : syracuseStep 9959507 = 14939261) B14939261
theorem B2586779 : Blo 1148636 2586779 := bstep (se 1 (by rfl) ⟨1940084, by rfl⟩ : syracuseStep 2586779 = 3880169) B3880169
theorem B2586887 : Blo 1148636 2586887 := bstep (se 1 (by rfl) ⟨1940165, by rfl⟩ : syracuseStep 2586887 = 3880331) B3880331
theorem B2587193 : Blo 1148636 2587193 := bstep (se 2 (by rfl) ⟨970197, by rfl⟩ : syracuseStep 2587193 = 1940395) B1940395
theorem B8288891 : Blo 1148636 8288891 := bstep (se 1 (by rfl) ⟨6216668, by rfl⟩ : syracuseStep 8288891 = 12433337) B12433337
theorem B3275603 : Blo 1148636 3275603 := bstep (se 1 (by rfl) ⟨2456702, by rfl⟩ : syracuseStep 3275603 = 4913405) B4913405
theorem B2456411 : Blo 1148636 2456411 := bstep (se 1 (by rfl) ⟨1842308, by rfl⟩ : syracuseStep 2456411 = 3684617) B3684617
theorem B5831837 : Blo 1148636 5831837 := bstep (se 3 (by rfl) ⟨1093469, by rfl⟩ : syracuseStep 5831837 = 2186939) B2186939
theorem B14187737 : Blo 1148636 14187737 := bstep (se 2 (by rfl) ⟨5320401, by rfl⟩ : syracuseStep 14187737 = 10640803) B10640803
theorem B2587913 : Blo 1148636 2587913 := bstep (se 2 (by rfl) ⟨970467, by rfl⟩ : syracuseStep 2587913 = 1940935) B1940935
theorem B3276263 : Blo 1148636 3276263 := bstep (se 1 (by rfl) ⟨2457197, by rfl⟩ : syracuseStep 3276263 = 4914395) B4914395
theorem B3735047 : Blo 1148636 3735047 := bstep (se 1 (by rfl) ⟨2801285, by rfl⟩ : syracuseStep 3735047 = 5602571) B5602571
theorem B1637995 : Blo 1148636 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B5537423 : Blo 1148636 5537423 := bstep (se 1 (by rfl) ⟨4153067, by rfl⟩ : syracuseStep 5537423 = 8306135) B8306135
theorem B2588921 : Blo 1148636 2588921 := bstep (se 2 (by rfl) ⟨970845, by rfl⟩ : syracuseStep 2588921 = 1941691) B1941691
theorem B2588975 : Blo 1148636 2588975 := bstep (se 1 (by rfl) ⟨1941731, by rfl⟩ : syracuseStep 2588975 = 3883463) B3883463
theorem B8520047 : Blo 1148636 8520047 := bstep (se 1 (by rfl) ⟨6390035, by rfl⟩ : syracuseStep 8520047 = 12780071) B12780071
theorem B2457983 : Blo 1148636 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B2589191 : Blo 1148636 2589191 := bstep (se 1 (by rfl) ⟨1941893, by rfl⟩ : syracuseStep 2589191 = 3883787) B3883787
theorem B3113567 : Blo 1148636 3113567 := bstep (se 1 (by rfl) ⟨2335175, by rfl⟩ : syracuseStep 3113567 = 4670351) B4670351
theorem B2589371 : Blo 1148636 2589371 := bstep (se 1 (by rfl) ⟨1942028, by rfl⟩ : syracuseStep 2589371 = 3884057) B3884057
theorem B4326205 : Blo 1148636 4326205 := bstep (se 3 (by rfl) ⟨811163, by rfl⟩ : syracuseStep 4326205 = 1622327) B1622327
theorem B8749943 : Blo 1148636 8749943 := bstep (se 1 (by rfl) ⟨6562457, by rfl⟩ : syracuseStep 8749943 = 13124915) B13124915
theorem B2458633 : Blo 1148636 2458633 := bstep (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) B1843975
theorem B2589803 : Blo 1148636 2589803 := bstep (se 1 (by rfl) ⟨1942352, by rfl⟩ : syracuseStep 2589803 = 3884705) B3884705
theorem B1639931 : Blo 1148636 1639931 := bstep (se 1 (by rfl) ⟨1229948, by rfl⟩ : syracuseStep 1639931 = 2459897) B2459897
theorem B2590271 : Blo 1148636 2590271 := bstep (se 1 (by rfl) ⟨1942703, by rfl⟩ : syracuseStep 2590271 = 3885407) B3885407
theorem B2590379 : Blo 1148636 2590379 := bstep (se 1 (by rfl) ⟨1942784, by rfl⟩ : syracuseStep 2590379 = 3885569) B3885569
theorem B1148863 : Blo 1148636 1148863 := bstep (se 1 (by rfl) ⟨861647, by rfl⟩ : syracuseStep 1148863 = 1723295) B1723295
theorem B1148895 : Blo 1148636 1148895 := bstep (se 1 (by rfl) ⟨861671, by rfl⟩ : syracuseStep 1148895 = 1723343) B1723343
theorem B2590703 : Blo 1148636 2590703 := bstep (se 1 (by rfl) ⟨1943027, by rfl⟩ : syracuseStep 2590703 = 3886055) B3886055
theorem B1148955 : Blo 1148636 1148955 := bstep (se 1 (by rfl) ⟨861716, by rfl⟩ : syracuseStep 1148955 = 1723433) B1723433
theorem B1148959 : Blo 1148636 1148959 := bstep (se 1 (by rfl) ⟨861719, by rfl⟩ : syracuseStep 1148959 = 1723439) B1723439
theorem B1148975 : Blo 1148636 1148975 := bstep (se 1 (by rfl) ⟨861731, by rfl⟩ : syracuseStep 1148975 = 1723463) B1723463
theorem B3115169 : Blo 1148636 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B2590919 : Blo 1148636 2590919 := bstep (se 1 (by rfl) ⟨1943189, by rfl⟩ : syracuseStep 2590919 = 3886379) B3886379
theorem B1149151 : Blo 1148636 1149151 := bstep (se 1 (by rfl) ⟨861863, by rfl⟩ : syracuseStep 1149151 = 1723727) B1723727
theorem B1149211 : Blo 1148636 1149211 := bstep (se 1 (by rfl) ⟨861908, by rfl⟩ : syracuseStep 1149211 = 1723817) B1723817
theorem B2459983 : Blo 1148636 2459983 := bstep (se 1 (by rfl) ⟨1844987, by rfl⟩ : syracuseStep 2459983 = 3689975) B3689975
theorem B2591099 : Blo 1148636 2591099 := bstep (se 1 (by rfl) ⟨1943324, by rfl⟩ : syracuseStep 2591099 = 3886649) B3886649
theorem B1149311 : Blo 1148636 1149311 := bstep (se 1 (by rfl) ⟨861983, by rfl⟩ : syracuseStep 1149311 = 1723967) B1723967
theorem B6228389 : Blo 1148636 6228389 := bstep (se 4 (by rfl) ⟨583911, by rfl⟩ : syracuseStep 6228389 = 1167823) B1167823
theorem B19630511 : Blo 1148636 19630511 := bstep (se 1 (by rfl) ⟨14722883, by rfl⟩ : syracuseStep 19630511 = 29445767) B29445767
theorem B11045321 : Blo 1148636 11045321 := bstep (se 2 (by rfl) ⟨4141995, by rfl⟩ : syracuseStep 11045321 = 8283991) B8283991
theorem B1149487 : Blo 1148636 1149487 := bstep (se 1 (by rfl) ⟨862115, by rfl⟩ : syracuseStep 1149487 = 1724231) B1724231
theorem B33131105 : Blo 1148636 33131105 := bstep (se 2 (by rfl) ⟨12424164, by rfl⟩ : syracuseStep 33131105 = 24848329) B24848329
theorem B1149543 : Blo 1148636 1149543 := bstep (se 1 (by rfl) ⟨862157, by rfl⟩ : syracuseStep 1149543 = 1724315) B1724315
theorem B2591369 : Blo 1148636 2591369 := bstep (se 2 (by rfl) ⟨971763, by rfl⟩ : syracuseStep 2591369 = 1943527) B1943527
theorem B2591657 : Blo 1148636 2591657 := bstep (se 2 (by rfl) ⟨971871, by rfl⟩ : syracuseStep 2591657 = 1943743) B1943743
theorem B1149919 : Blo 1148636 1149919 := bstep (se 1 (by rfl) ⟨862439, by rfl⟩ : syracuseStep 1149919 = 1724879) B1724879
theorem B1149947 : Blo 1148636 1149947 := bstep (se 1 (by rfl) ⟨862460, by rfl⟩ : syracuseStep 1149947 = 1724921) B1724921
theorem B9341999 : Blo 1148636 9341999 := bstep (se 1 (by rfl) ⟨7006499, by rfl⟩ : syracuseStep 9341999 = 14012999) B14012999
theorem B1150015 : Blo 1148636 1150015 := bstep (se 1 (by rfl) ⟨862511, by rfl⟩ : syracuseStep 1150015 = 1725023) B1725023
theorem B13110335 : Blo 1148636 13110335 := bstep (se 1 (by rfl) ⟨9832751, by rfl⟩ : syracuseStep 13110335 = 19665503) B19665503
theorem B1150335 : Blo 1148636 1150335 := bstep (se 1 (by rfl) ⟨862751, by rfl⟩ : syracuseStep 1150335 = 1725503) B1725503
theorem B1150363 : Blo 1148636 1150363 := bstep (se 1 (by rfl) ⟨862772, by rfl⟩ : syracuseStep 1150363 = 1725545) B1725545
theorem B1150431 : Blo 1148636 1150431 := bstep (se 1 (by rfl) ⟨862823, by rfl⟩ : syracuseStep 1150431 = 1725647) B1725647
theorem B1150567 : Blo 1148636 1150567 := bstep (se 1 (by rfl) ⟨862925, by rfl⟩ : syracuseStep 1150567 = 1725851) B1725851
theorem B2592359 : Blo 1148636 2592359 := bstep (se 1 (by rfl) ⟨1944269, by rfl⟩ : syracuseStep 2592359 = 3888539) B3888539
theorem B9834119 : Blo 1148636 9834119 := bstep (se 1 (by rfl) ⟨7375589, by rfl⟩ : syracuseStep 9834119 = 14751179) B14751179
theorem B4361971 : Blo 1148636 4361971 := bstep (se 1 (by rfl) ⟨3271478, by rfl⟩ : syracuseStep 4361971 = 6542957) B6542957
theorem B1150715 : Blo 1148636 1150715 := bstep (se 1 (by rfl) ⟨863036, by rfl⟩ : syracuseStep 1150715 = 1726073) B1726073
theorem B1150783 : Blo 1148636 1150783 := bstep (se 1 (by rfl) ⟨863087, by rfl⟩ : syracuseStep 1150783 = 1726175) B1726175
theorem B3280763 : Blo 1148636 3280763 := bstep (se 1 (by rfl) ⟨2460572, by rfl⟩ : syracuseStep 3280763 = 4921145) B4921145
theorem B1150847 : Blo 1148636 1150847 := bstep (se 1 (by rfl) ⟨863135, by rfl⟩ : syracuseStep 1150847 = 1726271) B1726271
theorem B1150959 : Blo 1148636 1150959 := bstep (se 1 (by rfl) ⟨863219, by rfl⟩ : syracuseStep 1150959 = 1726439) B1726439
theorem B1150971 : Blo 1148636 1150971 := bstep (se 1 (by rfl) ⟨863228, by rfl⟩ : syracuseStep 1150971 = 1726457) B1726457
theorem B2461691 : Blo 1148636 2461691 := bstep (se 1 (by rfl) ⟨1846268, by rfl⟩ : syracuseStep 2461691 = 3692537) B3692537
theorem B1151039 : Blo 1148636 1151039 := bstep (se 1 (by rfl) ⟨863279, by rfl⟩ : syracuseStep 1151039 = 1726559) B1726559
theorem B2592863 : Blo 1148636 2592863 := bstep (se 1 (by rfl) ⟨1944647, by rfl⟩ : syracuseStep 2592863 = 3889295) B3889295
theorem B1151079 : Blo 1148636 1151079 := bstep (se 1 (by rfl) ⟨863309, by rfl⟩ : syracuseStep 1151079 = 1726619) B1726619
theorem B1151103 : Blo 1148636 1151103 := bstep (se 1 (by rfl) ⟨863327, by rfl⟩ : syracuseStep 1151103 = 1726655) B1726655
theorem B1151131 : Blo 1148636 1151131 := bstep (se 1 (by rfl) ⟨863348, by rfl⟩ : syracuseStep 1151131 = 1726697) B1726697
theorem B6557993 : Blo 1148636 6557993 := bstep (se 2 (by rfl) ⟨2459247, by rfl⟩ : syracuseStep 6557993 = 4918495) B4918495
theorem B9834803 : Blo 1148636 9834803 := bstep (se 1 (by rfl) ⟨7376102, by rfl⟩ : syracuseStep 9834803 = 14752205) B14752205
theorem B5247287 : Blo 1148636 5247287 := bstep (se 1 (by rfl) ⟨3935465, by rfl⟩ : syracuseStep 5247287 = 7870931) B7870931
theorem B1151335 : Blo 1148636 1151335 := bstep (se 1 (by rfl) ⟨863501, by rfl⟩ : syracuseStep 1151335 = 1727003) B1727003
theorem B1151387 : Blo 1148636 1151387 := bstep (se 1 (by rfl) ⟨863540, by rfl⟩ : syracuseStep 1151387 = 1727081) B1727081
theorem B1970743 : Blo 1148636 1970743 := bstep (se 1 (by rfl) ⟨1478057, by rfl⟩ : syracuseStep 1970743 = 2956115) B2956115
theorem B1151739 : Blo 1148636 1151739 := bstep (se 1 (by rfl) ⟨863804, by rfl⟩ : syracuseStep 1151739 = 1727609) B1727609
theorem B1151807 : Blo 1148636 1151807 := bstep (se 1 (by rfl) ⟨863855, by rfl⟩ : syracuseStep 1151807 = 1727711) B1727711
theorem B1151835 : Blo 1148636 1151835 := bstep (se 1 (by rfl) ⟨863876, by rfl⟩ : syracuseStep 1151835 = 1727753) B1727753
theorem B1151903 : Blo 1148636 1151903 := bstep (se 1 (by rfl) ⟨863927, by rfl⟩ : syracuseStep 1151903 = 1727855) B1727855
theorem B4363247 : Blo 1148636 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B1151983 : Blo 1148636 1151983 := bstep (se 1 (by rfl) ⟨863987, by rfl⟩ : syracuseStep 1151983 = 1727975) B1727975
theorem B1152071 : Blo 1148636 1152071 := bstep (se 1 (by rfl) ⟨864053, by rfl⟩ : syracuseStep 1152071 = 1728107) B1728107
theorem B1152155 : Blo 1148636 1152155 := bstep (se 1 (by rfl) ⟨864116, by rfl⟩ : syracuseStep 1152155 = 1728233) B1728233
theorem B1152251 : Blo 1148636 1152251 := bstep (se 1 (by rfl) ⟨864188, by rfl⟩ : syracuseStep 1152251 = 1728377) B1728377
theorem B1152319 : Blo 1148636 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B1152487 : Blo 1148636 1152487 := bstep (se 1 (by rfl) ⟨864365, by rfl⟩ : syracuseStep 1152487 = 1728731) B1728731
theorem B1152495 : Blo 1148636 1152495 := bstep (se 1 (by rfl) ⟨864371, by rfl⟩ : syracuseStep 1152495 = 1728743) B1728743
theorem B1152603 : Blo 1148636 1152603 := bstep (se 1 (by rfl) ⟨864452, by rfl⟩ : syracuseStep 1152603 = 1728905) B1728905
theorem B1939099 : Blo 1148636 1939099 := bstep (se 1 (by rfl) ⟨1454324, by rfl⟩ : syracuseStep 1939099 = 2908649) B2908649
theorem B6559451 : Blo 1148636 6559451 := bstep (se 1 (by rfl) ⟨4919588, by rfl⟩ : syracuseStep 6559451 = 9839177) B9839177
theorem B7378847 : Blo 1148636 7378847 := bstep (se 1 (by rfl) ⟨5534135, by rfl⟩ : syracuseStep 7378847 = 11068271) B11068271
theorem B4921469 : Blo 1148636 4921469 := bstep (se 3 (by rfl) ⟨922775, by rfl⟩ : syracuseStep 4921469 = 1845551) B1845551
theorem B85170649 : Blo 1148636 85170649 := bstep (se 2 (by rfl) ⟨31938993, by rfl⟩ : syracuseStep 85170649 = 63877987) B63877987
theorem B1939943 : Blo 1148636 1939943 := bstep (se 1 (by rfl) ⟨1454957, by rfl⟩ : syracuseStep 1939943 = 2909915) B2909915
theorem B4659713 : Blo 1148636 4659713 := bstep (se 2 (by rfl) ⟨1747392, by rfl⟩ : syracuseStep 4659713 = 3494785) B3494785
theorem B4365359 : Blo 1148636 4365359 := bstep (se 1 (by rfl) ⟨3274019, by rfl⟩ : syracuseStep 4365359 = 6548039) B6548039
theorem B1940807 : Blo 1148636 1940807 := bstep (se 1 (by rfl) ⟨1455605, by rfl⟩ : syracuseStep 1940807 = 2911211) B2911211
theorem B1940969 : Blo 1148636 1940969 := bstep (se 2 (by rfl) ⟨727863, by rfl⟩ : syracuseStep 1940969 = 1455727) B1455727
theorem B11050775 : Blo 1148636 11050775 := bstep (se 1 (by rfl) ⟨8288081, by rfl⟩ : syracuseStep 11050775 = 16576163) B16576163
theorem B9838493 : Blo 1148636 9838493 := bstep (se 3 (by rfl) ⟨1844717, by rfl⟩ : syracuseStep 9838493 = 3689435) B3689435
theorem B2907447281 : Blo 1148636 2907447281 := bstep (se 2 (by rfl) ⟨1090292730, by rfl⟩ : syracuseStep 2907447281 = 2180585461) B2180585461
theorem B6562367 : Blo 1148636 6562367 := bstep (se 1 (by rfl) ⟨4921775, by rfl⟩ : syracuseStep 6562367 = 9843551) B9843551
theorem B13116167 : Blo 1148636 13116167 := bstep (se 1 (by rfl) ⟨9837125, by rfl⟩ : syracuseStep 13116167 = 19674251) B19674251
theorem B8725643 : Blo 1148636 8725643 := bstep (se 1 (by rfl) ⟨6544232, by rfl⟩ : syracuseStep 8725643 = 13088465) B13088465
theorem B9315595 : Blo 1148636 9315595 := bstep (se 1 (by rfl) ⟨6986696, by rfl⟩ : syracuseStep 9315595 = 13973393) B13973393
theorem B2762041 : Blo 1148636 2762041 := bstep (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) B2071531
theorem B9840953 : Blo 1148636 9840953 := bstep (se 2 (by rfl) ⟨3690357, by rfl⟩ : syracuseStep 9840953 = 7380715) B7380715
theorem B1845641 : Blo 1148636 1845641 := bstep (se 2 (by rfl) ⟨692115, by rfl⟩ : syracuseStep 1845641 = 1384231) B1384231
theorem B37890443 : Blo 1148636 37890443 := bstep (se 1 (by rfl) ⟨28417832, by rfl⟩ : syracuseStep 37890443 = 56835665) B56835665
theorem B4729337 : Blo 1148636 4729337 := bstep (se 2 (by rfl) ⟨1773501, by rfl⟩ : syracuseStep 4729337 = 3547003) B3547003
theorem B19639259 : Blo 1148636 19639259 := bstep (se 1 (by rfl) ⟨14729444, by rfl⟩ : syracuseStep 19639259 = 29458889) B29458889
theorem B13119083 : Blo 1148636 13119083 := bstep (se 1 (by rfl) ⟨9839312, by rfl⟩ : syracuseStep 13119083 = 19678625) B19678625
theorem B3879143 : Blo 1148636 3879143 := bstep (se 1 (by rfl) ⟨2909357, by rfl⟩ : syracuseStep 3879143 = 5818715) B5818715
theorem B3683387 : Blo 1148636 3683387 := bstep (se 1 (by rfl) ⟨2762540, by rfl⟩ : syracuseStep 3683387 = 5525081) B5525081
theorem B3880007 : Blo 1148636 3880007 := bstep (se 1 (by rfl) ⟨2910005, by rfl⟩ : syracuseStep 3880007 = 5820011) B5820011
theorem B1455175 : Blo 1148636 1455175 := bstep (se 1 (by rfl) ⟨1091381, by rfl⟩ : syracuseStep 1455175 = 2182763) B2182763
theorem B31438057 : Blo 1148636 31438057 := bstep (se 2 (by rfl) ⟨11789271, by rfl⟩ : syracuseStep 31438057 = 23578543) B23578543
theorem B2766251 : Blo 1148636 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B4371965 : Blo 1148636 4371965 := bstep (se 3 (by rfl) ⟨819743, by rfl⟩ : syracuseStep 4371965 = 1639487) B1639487
theorem B6993847 : Blo 1148636 6993847 := bstep (se 1 (by rfl) ⟨5245385, by rfl⟩ : syracuseStep 6993847 = 10490771) B10490771
theorem B3684361 : Blo 1148636 3684361 := bstep (se 2 (by rfl) ⟨1381635, by rfl⟩ : syracuseStep 3684361 = 2763271) B2763271
theorem B1292359 : Blo 1148636 1292359 := bstep (se 1 (by rfl) ⟨969269, by rfl⟩ : syracuseStep 1292359 = 1938539) B1938539
theorem B3881195 : Blo 1148636 3881195 := bstep (se 1 (by rfl) ⟨2910896, by rfl⟩ : syracuseStep 3881195 = 5821793) B5821793
theorem B2767097 : Blo 1148636 2767097 := bstep (se 2 (by rfl) ⟨1037661, by rfl⟩ : syracuseStep 2767097 = 2075323) B2075323
theorem B9845327 : Blo 1148636 9845327 := bstep (se 1 (by rfl) ⟨7383995, by rfl⟩ : syracuseStep 9845327 = 14767991) B14767991
theorem B4373135 : Blo 1148636 4373135 := bstep (se 1 (by rfl) ⟨3279851, by rfl⟩ : syracuseStep 4373135 = 6559703) B6559703
theorem B10500779 : Blo 1148636 10500779 := bstep (se 1 (by rfl) ⟨7875584, by rfl⟩ : syracuseStep 10500779 = 15751169) B15751169
theorem B1293223 : Blo 1148636 1293223 := bstep (se 1 (by rfl) ⟨969917, by rfl⟩ : syracuseStep 1293223 = 1939835) B1939835
theorem B1293403 : Blo 1148636 1293403 := bstep (se 1 (by rfl) ⟨970052, by rfl⟩ : syracuseStep 1293403 = 1940105) B1940105
theorem B1457615 : Blo 1148636 1457615 := bstep (se 1 (by rfl) ⟨1093211, by rfl⟩ : syracuseStep 1457615 = 2186423) B2186423
theorem B1294591 : Blo 1148636 1294591 := bstep (se 1 (by rfl) ⟨970943, by rfl⟩ : syracuseStep 1294591 = 1941887) B1941887
theorem B4374881 : Blo 1148636 4374881 := bstep (se 2 (by rfl) ⟨1640580, by rfl⟩ : syracuseStep 4374881 = 3281161) B3281161
theorem B49889735 : Blo 1148636 49889735 := bstep (se 1 (by rfl) ⟨37417301, by rfl⟩ : syracuseStep 49889735 = 74834603) B74834603
theorem B3883517 : Blo 1148636 3883517 := bstep (se 3 (by rfl) ⟨728159, by rfl⟩ : syracuseStep 3883517 = 1456319) B1456319
theorem B1294879 : Blo 1148636 1294879 := bstep (se 1 (by rfl) ⟨971159, by rfl⟩ : syracuseStep 1294879 = 1942319) B1942319
theorem B7980065 : Blo 1148636 7980065 := bstep (se 2 (by rfl) ⟨2992524, by rfl⟩ : syracuseStep 7980065 = 5985049) B5985049
theorem B1295527 : Blo 1148636 1295527 := bstep (se 1 (by rfl) ⟨971645, by rfl⟩ : syracuseStep 1295527 = 1943291) B1943291
theorem B3884651 : Blo 1148636 3884651 := bstep (se 1 (by rfl) ⟨2913488, by rfl⟩ : syracuseStep 3884651 = 5826977) B5826977
theorem B5523065 : Blo 1148636 5523065 := bstep (se 2 (by rfl) ⟨2071149, by rfl⟩ : syracuseStep 5523065 = 4142299) B4142299
theorem B3884921 : Blo 1148636 3884921 := bstep (se 2 (by rfl) ⟨1456845, by rfl⟩ : syracuseStep 3884921 = 2913691) B2913691
theorem B1296319 : Blo 1148636 1296319 := bstep (se 1 (by rfl) ⟨972239, by rfl⟩ : syracuseStep 1296319 = 1944479) B1944479
theorem B2181343 : Blo 1148636 2181343 := bstep (se 1 (by rfl) ⟨1636007, by rfl⟩ : syracuseStep 2181343 = 3272015) B3272015
theorem B1296607 : Blo 1148636 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B3885299 : Blo 1148636 3885299 := bstep (se 1 (by rfl) ⟨2913974, by rfl⟩ : syracuseStep 3885299 = 5827949) B5827949
theorem B10504495 : Blo 1148636 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B53791087 : Blo 1148636 53791087 := bstep (se 1 (by rfl) ⟨40343315, by rfl⟩ : syracuseStep 53791087 = 80686631) B80686631
theorem B1722983 : Blo 1148636 1722983 := bstep (se 1 (by rfl) ⟨1292237, by rfl⟩ : syracuseStep 1722983 = 2584475) B2584475
theorem B1723175 : Blo 1148636 1723175 := bstep (se 1 (by rfl) ⟨1292381, by rfl⟩ : syracuseStep 1723175 = 2584763) B2584763
theorem B1723499 : Blo 1148636 1723499 := bstep (se 1 (by rfl) ⟨1292624, by rfl⟩ : syracuseStep 1723499 = 2585249) B2585249
theorem B9096425 : Blo 1148636 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B1723739 : Blo 1148636 1723739 := bstep (se 1 (by rfl) ⟨1292804, by rfl⟩ : syracuseStep 1723739 = 2585609) B2585609
theorem B1723769 : Blo 1148636 1723769 := bstep (se 2 (by rfl) ⟨646413, by rfl⟩ : syracuseStep 1723769 = 1292827) B1292827
theorem B1723775 : Blo 1148636 1723775 := bstep (se 1 (by rfl) ⟨1292831, by rfl⟩ : syracuseStep 1723775 = 2585663) B2585663
theorem B5525273 : Blo 1148636 5525273 := bstep (se 2 (by rfl) ⟨2071977, by rfl⟩ : syracuseStep 5525273 = 4143955) B4143955
theorem B3886919 : Blo 1148636 3886919 := bstep (se 1 (by rfl) ⟨2915189, by rfl⟩ : syracuseStep 3886919 = 5830379) B5830379
theorem B1724399 : Blo 1148636 1724399 := bstep (se 1 (by rfl) ⟨1293299, by rfl⟩ : syracuseStep 1724399 = 2586599) B2586599
theorem B1724411 : Blo 1148636 1724411 := bstep (se 1 (by rfl) ⟨1293308, by rfl⟩ : syracuseStep 1724411 = 2586617) B2586617
theorem B1724471 : Blo 1148636 1724471 := bstep (se 1 (by rfl) ⟨1293353, by rfl⟩ : syracuseStep 1724471 = 2586707) B2586707
theorem B6639671 : Blo 1148636 6639671 := bstep (se 1 (by rfl) ⟨4979753, by rfl⟩ : syracuseStep 6639671 = 9959507) B9959507
theorem B1724519 : Blo 1148636 1724519 := bstep (se 1 (by rfl) ⟨1293389, by rfl⟩ : syracuseStep 1724519 = 2586779) B2586779
theorem B1724591 : Blo 1148636 1724591 := bstep (se 1 (by rfl) ⟨1293443, by rfl⟩ : syracuseStep 1724591 = 2586887) B2586887
theorem B1724795 : Blo 1148636 1724795 := bstep (se 1 (by rfl) ⟨1293596, by rfl⟩ : syracuseStep 1724795 = 2587193) B2587193
theorem B5525927 : Blo 1148636 5525927 := bstep (se 1 (by rfl) ⟨4144445, by rfl⟩ : syracuseStep 5525927 = 8288891) B8288891
theorem B51139117 : Blo 1148636 51139117 := bstep (se 3 (by rfl) ⟨9588584, by rfl⟩ : syracuseStep 51139117 = 19177169) B19177169
theorem B2183735 : Blo 1148636 2183735 := bstep (se 1 (by rfl) ⟨1637801, by rfl⟩ : syracuseStep 2183735 = 3275603) B3275603
theorem B1725065 : Blo 1148636 1725065 := bstep (se 2 (by rfl) ⟨646899, by rfl⟩ : syracuseStep 1725065 = 1293799) B1293799
theorem B3887891 : Blo 1148636 3887891 := bstep (se 1 (by rfl) ⟨2915918, by rfl⟩ : syracuseStep 3887891 = 5831837) B5831837
theorem B2183993 : Blo 1148636 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B9458491 : Blo 1148636 9458491 := bstep (se 1 (by rfl) ⟨7093868, by rfl⟩ : syracuseStep 9458491 = 14187737) B14187737
theorem B1725275 : Blo 1148636 1725275 := bstep (se 1 (by rfl) ⟨1293956, by rfl⟩ : syracuseStep 1725275 = 2587913) B2587913
theorem B2184175 : Blo 1148636 2184175 := bstep (se 1 (by rfl) ⟨1638131, by rfl⟩ : syracuseStep 2184175 = 3276263) B3276263
theorem B3691615 : Blo 1148636 3691615 := bstep (se 1 (by rfl) ⟨2768711, by rfl⟩ : syracuseStep 3691615 = 5537423) B5537423
theorem B1725737 : Blo 1148636 1725737 := bstep (se 2 (by rfl) ⟨647151, by rfl⟩ : syracuseStep 1725737 = 1294303) B1294303
theorem B1725935 : Blo 1148636 1725935 := bstep (se 1 (by rfl) ⟨1294451, by rfl⟩ : syracuseStep 1725935 = 2588903) B2588903
theorem B5527369 : Blo 1148636 5527369 := bstep (se 2 (by rfl) ⟨2072763, by rfl⟩ : syracuseStep 5527369 = 4145527) B4145527
theorem B1726331 : Blo 1148636 1726331 := bstep (se 1 (by rfl) ⟨1294748, by rfl⟩ : syracuseStep 1726331 = 2589497) B2589497
theorem B1726367 : Blo 1148636 1726367 := bstep (se 1 (by rfl) ⟨1294775, by rfl⟩ : syracuseStep 1726367 = 2589551) B2589551
theorem B1726601 : Blo 1148636 1726601 := bstep (se 2 (by rfl) ⟨647475, by rfl⟩ : syracuseStep 1726601 = 1294951) B1294951
theorem B1726751 : Blo 1148636 1726751 := bstep (se 1 (by rfl) ⟨1295063, by rfl⟩ : syracuseStep 1726751 = 2590127) B2590127
theorem B9820723 : Blo 1148636 9820723 := bstep (se 1 (by rfl) ⟨7365542, by rfl⟩ : syracuseStep 9820723 = 14731085) B14731085
theorem B1727303 : Blo 1148636 1727303 := bstep (se 1 (by rfl) ⟨1295477, by rfl⟩ : syracuseStep 1727303 = 2590955) B2590955
theorem B7462297 : Blo 1148636 7462297 := bstep (se 2 (by rfl) ⟨2798361, by rfl⟩ : syracuseStep 7462297 = 5596723) B5596723
theorem B1728167 : Blo 1148636 1728167 := bstep (se 1 (by rfl) ⟨1296125, by rfl⟩ : syracuseStep 1728167 = 2592251) B2592251
theorem B19652381 : Blo 1148636 19652381 := bstep (se 3 (by rfl) ⟨3684821, by rfl⟩ : syracuseStep 19652381 = 7369643) B7369643
theorem B1728287 : Blo 1148636 1728287 := bstep (se 1 (by rfl) ⟨1296215, by rfl⟩ : syracuseStep 1728287 = 2592431) B2592431
theorem B6545555 : Blo 1148636 6545555 := bstep (se 1 (by rfl) ⟨4909166, by rfl⟩ : syracuseStep 6545555 = 9818333) B9818333
theorem B1728719 : Blo 1148636 1728719 := bstep (se 1 (by rfl) ⟨1296539, by rfl⟩ : syracuseStep 1728719 = 2593079) B2593079
theorem B1728767 : Blo 1148636 1728767 := bstep (se 1 (by rfl) ⟨1296575, by rfl⟩ : syracuseStep 1728767 = 2593151) B2593151
theorem B2187577 : Blo 1148636 2187577 := bstep (se 2 (by rfl) ⟨820341, by rfl⟩ : syracuseStep 2187577 = 1640683) B1640683
theorem B5530139 : Blo 1148636 5530139 := bstep (se 1 (by rfl) ⟨4147604, by rfl⟩ : syracuseStep 5530139 = 8295209) B8295209
theorem B29844197 : Blo 1148636 29844197 := bstep (se 4 (by rfl) ⟨2797893, by rfl⟩ : syracuseStep 29844197 = 5595787) B5595787
theorem B2188063 : Blo 1148636 2188063 := bstep (se 1 (by rfl) ⟨1641047, by rfl⟩ : syracuseStep 2188063 = 3282095) B3282095
theorem B10479095 : Blo 1148636 10479095 := bstep (se 1 (by rfl) ⟨7859321, by rfl⟩ : syracuseStep 10479095 = 15718643) B15718643
theorem B2910107 : Blo 1148636 2910107 := bstep (se 1 (by rfl) ⟨2182580, by rfl⟩ : syracuseStep 2910107 = 4365161) B4365161
theorem B6646063 : Blo 1148636 6646063 := bstep (se 1 (by rfl) ⟨4984547, by rfl⟩ : syracuseStep 6646063 = 9969095) B9969095
theorem B11823641 : Blo 1148636 11823641 := bstep (se 2 (by rfl) ⟨4433865, by rfl⟩ : syracuseStep 11823641 = 8867731) B8867731
theorem B9825097 : Blo 1148636 9825097 := bstep (se 2 (by rfl) ⟨3684411, by rfl⟩ : syracuseStep 9825097 = 7368823) B7368823
theorem B7368185 : Blo 1148636 7368185 := bstep (se 2 (by rfl) ⟨2763069, by rfl⟩ : syracuseStep 7368185 = 5526139) B5526139
theorem B2584457 : Blo 1148636 2584457 := bstep (se 2 (by rfl) ⟨969171, by rfl⟩ : syracuseStep 2584457 = 1938343) B1938343
theorem B19656755 : Blo 1148636 19656755 := bstep (se 1 (by rfl) ⟨14742566, by rfl⟩ : syracuseStep 19656755 = 29485133) B29485133
theorem B2584673 : Blo 1148636 2584673 := bstep (se 2 (by rfl) ⟨969252, by rfl⟩ : syracuseStep 2584673 = 1938505) B1938505
theorem B2912719 : Blo 1148636 2912719 := bstep (se 1 (by rfl) ⟨2184539, by rfl⟩ : syracuseStep 2912719 = 4369079) B4369079
theorem B18641441 : Blo 1148636 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B2585339 : Blo 1148636 2585339 := bstep (se 1 (by rfl) ⟨1939004, by rfl⟩ : syracuseStep 2585339 = 3878009) B3878009
theorem B9827081 : Blo 1148636 9827081 := bstep (se 2 (by rfl) ⟨3685155, by rfl⟩ : syracuseStep 9827081 = 7370311) B7370311
theorem B6550429 : Blo 1148636 6550429 := bstep (se 3 (by rfl) ⟨1228205, by rfl⟩ : syracuseStep 6550429 = 2456411) B2456411
theorem B2585555 : Blo 1148636 2585555 := bstep (se 1 (by rfl) ⟨1939166, by rfl⟩ : syracuseStep 2585555 = 3878333) B3878333
theorem B4912447 : Blo 1148636 4912447 := bstep (se 1 (by rfl) ⟨3684335, by rfl⟩ : syracuseStep 4912447 = 7368671) B7368671
theorem B2454857 : Blo 1148636 2454857 := bstep (se 2 (by rfl) ⟨920571, by rfl⟩ : syracuseStep 2454857 = 1841143) B1841143
theorem B1635751 : Blo 1148636 1635751 := bstep (se 1 (by rfl) ⟨1226813, by rfl⟩ : syracuseStep 1635751 = 2453627) B2453627
theorem B2586023 : Blo 1148636 2586023 := bstep (se 1 (by rfl) ⟨1939517, by rfl⟩ : syracuseStep 2586023 = 3879035) B3879035
theorem B5830055 : Blo 1148636 5830055 := bstep (se 1 (by rfl) ⟨4372541, by rfl⟩ : syracuseStep 5830055 = 8745083) B8745083
theorem B2586131 : Blo 1148636 2586131 := bstep (se 1 (by rfl) ⟨1939598, by rfl⟩ : syracuseStep 2586131 = 3879197) B3879197
theorem B2586203 : Blo 1148636 2586203 := bstep (se 1 (by rfl) ⟨1939652, by rfl⟩ : syracuseStep 2586203 = 3879305) B3879305
theorem B5895791 : Blo 1148636 5895791 := bstep (se 1 (by rfl) ⟨4421843, by rfl⟩ : syracuseStep 5895791 = 8843687) B8843687
theorem B2914127 : Blo 1148636 2914127 := bstep (se 1 (by rfl) ⟨2185595, by rfl⟩ : syracuseStep 2914127 = 4371191) B4371191
theorem B2586815 : Blo 1148636 2586815 := bstep (se 1 (by rfl) ⟨1940111, by rfl⟩ : syracuseStep 2586815 = 3880223) B3880223
theorem B3734057 : Blo 1148636 3734057 := bstep (se 2 (by rfl) ⟨1400271, by rfl⟩ : syracuseStep 3734057 = 2800543) B2800543
theorem B6650515 : Blo 1148636 6650515 := bstep (se 1 (by rfl) ⟨4987886, by rfl⟩ : syracuseStep 6650515 = 9975773) B9975773
theorem B1637129 : Blo 1148636 1637129 := bstep (se 2 (by rfl) ⟨613923, by rfl⟩ : syracuseStep 1637129 = 1227847) B1227847
theorem B4914121 : Blo 1148636 4914121 := bstep (se 2 (by rfl) ⟨1842795, by rfl⟩ : syracuseStep 4914121 = 3685591) B3685591
theorem B11369861 : Blo 1148636 11369861 := bstep (se 4 (by rfl) ⟨1065924, by rfl⟩ : syracuseStep 11369861 = 2131849) B2131849
theorem B2588075 : Blo 1148636 2588075 := bstep (se 1 (by rfl) ⟨1941056, by rfl⟩ : syracuseStep 2588075 = 3882113) B3882113
theorem B2588111 : Blo 1148636 2588111 := bstep (se 1 (by rfl) ⟨1941083, by rfl⟩ : syracuseStep 2588111 = 3882167) B3882167
theorem B3276445 : Blo 1148636 3276445 := bstep (se 3 (by rfl) ⟨614333, by rfl⟩ : syracuseStep 3276445 = 1228667) B1228667
theorem B2490031 : Blo 1148636 2490031 := bstep (se 1 (by rfl) ⟨1867523, by rfl⟩ : syracuseStep 2490031 = 3735047) B3735047
theorem B2916071 : Blo 1148636 2916071 := bstep (se 1 (by rfl) ⟨2187053, by rfl⟩ : syracuseStep 2916071 = 4374107) B4374107
theorem B31489829 : Blo 1148636 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B5537575 : Blo 1148636 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B17727275 : Blo 1148636 17727275 := bstep (se 1 (by rfl) ⟨13295456, by rfl⟩ : syracuseStep 17727275 = 26590913) B26590913
theorem B2588615 : Blo 1148636 2588615 := bstep (se 1 (by rfl) ⟨1941461, by rfl⟩ : syracuseStep 2588615 = 3882923) B3882923
theorem B2916587 : Blo 1148636 2916587 := bstep (se 1 (by rfl) ⟨2187440, by rfl⟩ : syracuseStep 2916587 = 4374881) B4374881
theorem B33259823 : Blo 1148636 33259823 := bstep (se 1 (by rfl) ⟨24944867, by rfl⟩ : syracuseStep 33259823 = 49889735) B49889735
theorem B2589011 : Blo 1148636 2589011 := bstep (se 1 (by rfl) ⟨1941758, by rfl⟩ : syracuseStep 2589011 = 3883517) B3883517
theorem B2916769 : Blo 1148636 2916769 := bstep (se 2 (by rfl) ⟨1093788, by rfl⟩ : syracuseStep 2916769 = 2187577) B2187577
theorem B5833295 : Blo 1148636 5833295 := bstep (se 1 (by rfl) ⟨4374971, by rfl⟩ : syracuseStep 5833295 = 8749943) B8749943
theorem B6554621 : Blo 1148636 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B2917417 : Blo 1148636 2917417 := bstep (se 2 (by rfl) ⟨1094031, by rfl⟩ : syracuseStep 2917417 = 2188063) B2188063
theorem B2589767 : Blo 1148636 2589767 := bstep (se 1 (by rfl) ⟨1942325, by rfl⟩ : syracuseStep 2589767 = 3884651) B3884651
theorem B5768273 : Blo 1148636 5768273 := bstep (se 2 (by rfl) ⟨2163102, by rfl⟩ : syracuseStep 5768273 = 4326205) B4326205
theorem B2589947 : Blo 1148636 2589947 := bstep (se 1 (by rfl) ⟨1942460, by rfl⟩ : syracuseStep 2589947 = 3884921) B3884921
theorem B3278177 : Blo 1148636 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B2590199 : Blo 1148636 2590199 := bstep (se 1 (by rfl) ⟨1942649, by rfl⟩ : syracuseStep 2590199 = 3885299) B3885299
theorem B12420793 : Blo 1148636 12420793 := bstep (se 2 (by rfl) ⟨4657797, by rfl⟩ : syracuseStep 12420793 = 9315595) B9315595
theorem B22087403 : Blo 1148636 22087403 := bstep (se 1 (by rfl) ⟨16565552, by rfl⟩ : syracuseStep 22087403 = 33131105) B33131105
theorem B1148655 : Blo 1148636 1148655 := bstep (se 1 (by rfl) ⟨861491, by rfl⟩ : syracuseStep 1148655 = 1722983) B1722983
theorem B1148783 : Blo 1148636 1148783 := bstep (se 1 (by rfl) ⟨861587, by rfl⟩ : syracuseStep 1148783 = 1723175) B1723175
theorem B6227999 : Blo 1148636 6227999 := bstep (se 1 (by rfl) ⟨4670999, by rfl⟩ : syracuseStep 6227999 = 9341999) B9341999
theorem B1148999 : Blo 1148636 1148999 := bstep (se 1 (by rfl) ⟨861749, by rfl⟩ : syracuseStep 1148999 = 1723499) B1723499
theorem B6064283 : Blo 1148636 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B1149159 : Blo 1148636 1149159 := bstep (se 1 (by rfl) ⟨861869, by rfl⟩ : syracuseStep 1149159 = 1723739) B1723739
theorem B1149179 : Blo 1148636 1149179 := bstep (se 1 (by rfl) ⟨861884, by rfl⟩ : syracuseStep 1149179 = 1723769) B1723769
theorem B1149183 : Blo 1148636 1149183 := bstep (se 1 (by rfl) ⟨861887, by rfl⟩ : syracuseStep 1149183 = 1723775) B1723775
theorem B6556079 : Blo 1148636 6556079 := bstep (se 1 (by rfl) ⟨4917059, by rfl⟩ : syracuseStep 6556079 = 9834119) B9834119
theorem B2591279 : Blo 1148636 2591279 := bstep (se 1 (by rfl) ⟨1943459, by rfl⟩ : syracuseStep 2591279 = 3886919) B3886919
theorem B1149599 : Blo 1148636 1149599 := bstep (se 1 (by rfl) ⟨862199, by rfl⟩ : syracuseStep 1149599 = 1724399) B1724399
theorem B1149607 : Blo 1148636 1149607 := bstep (se 1 (by rfl) ⟨862205, by rfl⟩ : syracuseStep 1149607 = 1724411) B1724411
theorem B1149647 : Blo 1148636 1149647 := bstep (se 1 (by rfl) ⟨862235, by rfl⟩ : syracuseStep 1149647 = 1724471) B1724471
theorem B4426447 : Blo 1148636 4426447 := bstep (se 1 (by rfl) ⟨3319835, by rfl⟩ : syracuseStep 4426447 = 6639671) B6639671
theorem B1149679 : Blo 1148636 1149679 := bstep (se 1 (by rfl) ⟨862259, by rfl⟩ : syracuseStep 1149679 = 1724519) B1724519
theorem B1149727 : Blo 1148636 1149727 := bstep (se 1 (by rfl) ⟨862295, by rfl⟩ : syracuseStep 1149727 = 1724591) B1724591
theorem B6556535 : Blo 1148636 6556535 := bstep (se 1 (by rfl) ⟨4917401, by rfl⟩ : syracuseStep 6556535 = 9834803) B9834803
theorem B1149863 : Blo 1148636 1149863 := bstep (se 1 (by rfl) ⟨862397, by rfl⟩ : syracuseStep 1149863 = 1724795) B1724795
theorem B1150043 : Blo 1148636 1150043 := bstep (se 1 (by rfl) ⟨862532, by rfl⟩ : syracuseStep 1150043 = 1725065) B1725065
theorem B3279977 : Blo 1148636 3279977 := bstep (se 2 (by rfl) ⟨1229991, by rfl⟩ : syracuseStep 3279977 = 2459983) B2459983
theorem B2591927 : Blo 1148636 2591927 := bstep (se 1 (by rfl) ⟨1943945, by rfl⟩ : syracuseStep 2591927 = 3887891) B3887891
theorem B1150183 : Blo 1148636 1150183 := bstep (se 1 (by rfl) ⟨862637, by rfl⟩ : syracuseStep 1150183 = 1725275) B1725275
theorem B1150491 : Blo 1148636 1150491 := bstep (se 1 (by rfl) ⟨862868, by rfl⟩ : syracuseStep 1150491 = 1725737) B1725737
theorem B1150623 : Blo 1148636 1150623 := bstep (se 1 (by rfl) ⟨862967, by rfl⟩ : syracuseStep 1150623 = 1725935) B1725935
theorem B7376669 : Blo 1148636 7376669 := bstep (se 3 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 7376669 = 2766251) B2766251
theorem B1150887 : Blo 1148636 1150887 := bstep (se 1 (by rfl) ⟨863165, by rfl⟩ : syracuseStep 1150887 = 1726331) B1726331
theorem B1150911 : Blo 1148636 1150911 := bstep (se 1 (by rfl) ⟨863183, by rfl⟩ : syracuseStep 1150911 = 1726367) B1726367
theorem B4919231 : Blo 1148636 4919231 := bstep (se 1 (by rfl) ⟨3689423, by rfl⟩ : syracuseStep 4919231 = 7378847) B7378847
theorem B3280979 : Blo 1148636 3280979 := bstep (se 1 (by rfl) ⟨2460734, by rfl⟩ : syracuseStep 3280979 = 4921469) B4921469
theorem B1151067 : Blo 1148636 1151067 := bstep (se 1 (by rfl) ⟨863300, by rfl⟩ : syracuseStep 1151067 = 1726601) B1726601
theorem B1151167 : Blo 1148636 1151167 := bstep (se 1 (by rfl) ⟨863375, by rfl⟩ : syracuseStep 1151167 = 1726751) B1726751
theorem B1151535 : Blo 1148636 1151535 := bstep (se 1 (by rfl) ⟨863651, by rfl⟩ : syracuseStep 1151535 = 1727303) B1727303
theorem B1152111 : Blo 1148636 1152111 := bstep (se 1 (by rfl) ⟨864083, by rfl⟩ : syracuseStep 1152111 = 1728167) B1728167
theorem B1152191 : Blo 1148636 1152191 := bstep (se 1 (by rfl) ⟨864143, by rfl⟩ : syracuseStep 1152191 = 1728287) B1728287
theorem B6558995 : Blo 1148636 6558995 := bstep (se 1 (by rfl) ⟨4919246, by rfl⟩ : syracuseStep 6558995 = 9838493) B9838493
theorem B1938298187 : Blo 1148636 1938298187 := bstep (se 1 (by rfl) ⟨1453723640, by rfl⟩ : syracuseStep 1938298187 = 2907447281) B2907447281
theorem B4363703 : Blo 1148636 4363703 := bstep (se 1 (by rfl) ⟨3272777, by rfl⟩ : syracuseStep 4363703 = 6545555) B6545555
theorem B1152479 : Blo 1148636 1152479 := bstep (se 1 (by rfl) ⟨864359, by rfl⟩ : syracuseStep 1152479 = 1728719) B1728719
theorem B1152511 : Blo 1148636 1152511 := bstep (se 1 (by rfl) ⟨864383, by rfl⟩ : syracuseStep 1152511 = 1728767) B1728767
theorem B19896131 : Blo 1148636 19896131 := bstep (se 1 (by rfl) ⟨14922098, by rfl⟩ : syracuseStep 19896131 = 29844197) B29844197
theorem B2627657 : Blo 1148636 2627657 := bstep (se 2 (by rfl) ⟨985371, by rfl⟩ : syracuseStep 2627657 = 1970743) B1970743
theorem B6986063 : Blo 1148636 6986063 := bstep (se 1 (by rfl) ⟨5239547, by rfl⟩ : syracuseStep 6986063 = 10479095) B10479095
theorem B1940071 : Blo 1148636 1940071 := bstep (se 1 (by rfl) ⟨1455053, by rfl⟩ : syracuseStep 1940071 = 2910107) B2910107
theorem B1940233 : Blo 1148636 1940233 := bstep (se 2 (by rfl) ⟨727587, by rfl⟩ : syracuseStep 1940233 = 1455175) B1455175
theorem B4922153 : Blo 1148636 4922153 := bstep (se 2 (by rfl) ⟨1845807, by rfl⟩ : syracuseStep 4922153 = 3691615) B3691615
theorem B6560635 : Blo 1148636 6560635 := bstep (se 1 (by rfl) ⟨4920476, by rfl⟩ : syracuseStep 6560635 = 9840953) B9840953
theorem B41917409 : Blo 1148636 41917409 := bstep (se 2 (by rfl) ⟨15719028, by rfl⟩ : syracuseStep 41917409 = 31438057) B31438057
theorem B3152891 : Blo 1148636 3152891 := bstep (se 1 (by rfl) ⟨2364668, by rfl⟩ : syracuseStep 3152891 = 4729337) B4729337
theorem B4365677 : Blo 1148636 4365677 := bstep (se 3 (by rfl) ⟨818564, by rfl⟩ : syracuseStep 4365677 = 1637129) B1637129
theorem B12427627 : Blo 1148636 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B1942751 : Blo 1148636 1942751 := bstep (se 1 (by rfl) ⟨1457063, by rfl⟩ : syracuseStep 1942751 = 2914127) B2914127
theorem B1844731 : Blo 1148636 1844731 := bstep (se 1 (by rfl) ⟨1383548, by rfl⟩ : syracuseStep 1844731 = 2767097) B2767097
theorem B6563551 : Blo 1148636 6563551 := bstep (se 1 (by rfl) ⟨4922663, by rfl⟩ : syracuseStep 6563551 = 9845327) B9845327
theorem B4368593 : Blo 1148636 4368593 := bstep (se 2 (by rfl) ⟨1638222, by rfl⟩ : syracuseStep 4368593 = 3276445) B3276445
theorem B3320041 : Blo 1148636 3320041 := bstep (se 2 (by rfl) ⟨1245015, by rfl⟩ : syracuseStep 3320041 = 2490031) B2490031
theorem B7579907 : Blo 1148636 7579907 := bstep (se 1 (by rfl) ⟨5684930, by rfl⟩ : syracuseStep 7579907 = 11369861) B11369861
theorem B7383433 : Blo 1148636 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B1944047 : Blo 1148636 1944047 := bstep (se 1 (by rfl) ⟨1458035, by rfl⟩ : syracuseStep 1944047 = 2916071) B2916071
theorem B6564509 : Blo 1148636 6564509 := bstep (se 3 (by rfl) ⟨1230845, by rfl⟩ : syracuseStep 6564509 = 2461691) B2461691
theorem B2075711 : Blo 1148636 2075711 := bstep (se 1 (by rfl) ⟨1556783, by rfl⟩ : syracuseStep 2075711 = 3113567) B3113567
theorem B5320043 : Blo 1148636 5320043 := bstep (se 1 (by rfl) ⟨3990032, by rfl⟩ : syracuseStep 5320043 = 7980065) B7980065
theorem B3682043 : Blo 1148636 3682043 := bstep (se 1 (by rfl) ⟨2761532, by rfl⟩ : syracuseStep 3682043 = 5523065) B5523065
theorem B2076779 : Blo 1148636 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B13087007 : Blo 1148636 13087007 := bstep (se 1 (by rfl) ⟨9815255, by rfl⟩ : syracuseStep 13087007 = 19630511) B19630511
theorem B3682721 : Blo 1148636 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B4371995 : Blo 1148636 4371995 := bstep (se 1 (by rfl) ⟨3278996, by rfl⟩ : syracuseStep 4371995 = 6557993) B6557993
theorem B3683951 : Blo 1148636 3683951 := bstep (se 1 (by rfl) ⟨2762963, by rfl⟩ : syracuseStep 3683951 = 5525927) B5525927
theorem B1455823 : Blo 1148636 1455823 := bstep (se 1 (by rfl) ⟨1091867, by rfl⟩ : syracuseStep 1455823 = 2183735) B2183735
theorem B8861417 : Blo 1148636 8861417 := bstep (se 2 (by rfl) ⟨3323031, by rfl⟩ : syracuseStep 8861417 = 6646063) B6646063
theorem B14005993 : Blo 1148636 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B1455995 : Blo 1148636 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B4372967 : Blo 1148636 4372967 := bstep (se 1 (by rfl) ⟨3279725, by rfl⟩ : syracuseStep 4372967 = 6559451) B6559451
theorem B90880501 : Blo 1148636 90880501 := bstep (se 5 (by rfl) ⟨4260023, by rfl⟩ : syracuseStep 90880501 = 8520047) B8520047
theorem B4373149 : Blo 1148636 4373149 := bstep (se 3 (by rfl) ⟨819965, by rfl⟩ : syracuseStep 4373149 = 1639931) B1639931
theorem B1293295 : Blo 1148636 1293295 := bstep (se 1 (by rfl) ⟨969971, by rfl⟩ : syracuseStep 1293295 = 1939943) B1939943
theorem B1293871 : Blo 1148636 1293871 := bstep (se 1 (by rfl) ⟨970403, by rfl⟩ : syracuseStep 1293871 = 1940807) B1940807
theorem B5815961 : Blo 1148636 5815961 := bstep (se 2 (by rfl) ⟨2180985, by rfl⟩ : syracuseStep 5815961 = 4361971) B4361971
theorem B1293979 : Blo 1148636 1293979 := bstep (se 1 (by rfl) ⟨970484, by rfl⟩ : syracuseStep 1293979 = 1940969) B1940969
theorem B3686759 : Blo 1148636 3686759 := bstep (se 1 (by rfl) ⟨2765069, by rfl⟩ : syracuseStep 3686759 = 5530139) B5530139
theorem B4374911 : Blo 1148636 4374911 := bstep (se 1 (by rfl) ⟨3281183, by rfl⟩ : syracuseStep 4374911 = 6562367) B6562367
theorem B3883625 : Blo 1148636 3883625 := bstep (se 2 (by rfl) ⟨1456359, by rfl⟩ : syracuseStep 3883625 = 2912719) B2912719
theorem B5817095 : Blo 1148636 5817095 := bstep (se 1 (by rfl) ⟨4362821, by rfl⟩ : syracuseStep 5817095 = 8725643) B8725643
theorem B8733905 : Blo 1148636 8733905 := bstep (se 2 (by rfl) ⟨3275214, by rfl⟩ : syracuseStep 8733905 = 6550429) B6550429
theorem B1230427 : Blo 1148636 1230427 := bstep (se 1 (by rfl) ⟨922820, by rfl⟩ : syracuseStep 1230427 = 1845641) B1845641
theorem B7882427 : Blo 1148636 7882427 := bstep (se 1 (by rfl) ⟨5911820, by rfl⟩ : syracuseStep 7882427 = 11823641) B11823641
theorem B2181001 : Blo 1148636 2181001 := bstep (se 2 (by rfl) ⟨817875, by rfl⟩ : syracuseStep 2181001 = 1635751) B1635751
theorem B13092839 : Blo 1148636 13092839 := bstep (se 1 (by rfl) ⟨9819629, by rfl⟩ : syracuseStep 13092839 = 19639259) B19639259
theorem B9325129 : Blo 1148636 9325129 := bstep (se 2 (by rfl) ⟨3496923, by rfl⟩ : syracuseStep 9325129 = 6993847) B6993847
theorem B1722971 : Blo 1148636 1722971 := bstep (se 1 (by rfl) ⟨1292228, by rfl⟩ : syracuseStep 1722971 = 2584457) B2584457
theorem B1723115 : Blo 1148636 1723115 := bstep (se 1 (by rfl) ⟨1292336, by rfl⟩ : syracuseStep 1723115 = 2584673) B2584673
theorem B1723145 : Blo 1148636 1723145 := bstep (se 2 (by rfl) ⟨646179, by rfl⟩ : syracuseStep 1723145 = 1292359) B1292359
theorem B1723559 : Blo 1148636 1723559 := bstep (se 1 (by rfl) ⟨1292669, by rfl⟩ : syracuseStep 1723559 = 2585339) B2585339
theorem B113560865 : Blo 1148636 113560865 := bstep (se 2 (by rfl) ⟨42585324, by rfl⟩ : syracuseStep 113560865 = 85170649) B85170649
theorem B1723703 : Blo 1148636 1723703 := bstep (se 1 (by rfl) ⟨1292777, by rfl⟩ : syracuseStep 1723703 = 2585555) B2585555
theorem B13094297 : Blo 1148636 13094297 := bstep (se 2 (by rfl) ⟨4910361, by rfl⟩ : syracuseStep 13094297 = 9820723) B9820723
theorem B8867353 : Blo 1148636 8867353 := bstep (se 2 (by rfl) ⟨3325257, by rfl⟩ : syracuseStep 8867353 = 6650515) B6650515
theorem B1724015 : Blo 1148636 1724015 := bstep (se 1 (by rfl) ⟨1293011, by rfl⟩ : syracuseStep 1724015 = 2586023) B2586023
theorem B3886703 : Blo 1148636 3886703 := bstep (se 1 (by rfl) ⟨2915027, by rfl⟩ : syracuseStep 3886703 = 5830055) B5830055
theorem B1724087 : Blo 1148636 1724087 := bstep (se 1 (by rfl) ⟨1293065, by rfl⟩ : syracuseStep 1724087 = 2586131) B2586131
theorem B1724135 : Blo 1148636 1724135 := bstep (se 1 (by rfl) ⟨1293101, by rfl⟩ : syracuseStep 1724135 = 2586203) B2586203
theorem B3886973 : Blo 1148636 3886973 := bstep (se 3 (by rfl) ⟨728807, by rfl⟩ : syracuseStep 3886973 = 1457615) B1457615
theorem B1724297 : Blo 1148636 1724297 := bstep (se 2 (by rfl) ⟨646611, by rfl⟩ : syracuseStep 1724297 = 1293223) B1293223
theorem B1724537 : Blo 1148636 1724537 := bstep (se 2 (by rfl) ⟨646701, by rfl⟩ : syracuseStep 1724537 = 1293403) B1293403
theorem B1724543 : Blo 1148636 1724543 := bstep (se 1 (by rfl) ⟨1293407, by rfl⟩ : syracuseStep 1724543 = 2586815) B2586815
theorem B7000519 : Blo 1148636 7000519 := bstep (se 1 (by rfl) ⟨5250389, by rfl⟩ : syracuseStep 7000519 = 10500779) B10500779
theorem B9949729 : Blo 1148636 9949729 := bstep (se 2 (by rfl) ⟨3731148, by rfl⟩ : syracuseStep 9949729 = 7462297) B7462297
theorem B14734061 : Blo 1148636 14734061 := bstep (se 3 (by rfl) ⟨2762636, by rfl⟩ : syracuseStep 14734061 = 5525273) B5525273
theorem B1725383 : Blo 1148636 1725383 := bstep (se 1 (by rfl) ⟨1294037, by rfl⟩ : syracuseStep 1725383 = 2588075) B2588075
theorem B1725407 : Blo 1148636 1725407 := bstep (se 1 (by rfl) ⟨1294055, by rfl⟩ : syracuseStep 1725407 = 2588111) B2588111
theorem B20993219 : Blo 1148636 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B11818183 : Blo 1148636 11818183 := bstep (se 1 (by rfl) ⟨8863637, by rfl⟩ : syracuseStep 11818183 = 17727275) B17727275
theorem B1725743 : Blo 1148636 1725743 := bstep (se 1 (by rfl) ⟨1294307, by rfl⟩ : syracuseStep 1725743 = 2588615) B2588615
theorem B1725947 : Blo 1148636 1725947 := bstep (se 1 (by rfl) ⟨1294460, by rfl⟩ : syracuseStep 1725947 = 2588921) B2588921
theorem B1725983 : Blo 1148636 1725983 := bstep (se 1 (by rfl) ⟨1294487, by rfl⟩ : syracuseStep 1725983 = 2588975) B2588975
theorem B1726121 : Blo 1148636 1726121 := bstep (se 2 (by rfl) ⟨647295, by rfl⟩ : syracuseStep 1726121 = 1294591) B1294591
theorem B1726127 : Blo 1148636 1726127 := bstep (se 1 (by rfl) ⟨1294595, by rfl⟩ : syracuseStep 1726127 = 2589191) B2589191
theorem B1726247 : Blo 1148636 1726247 := bstep (se 1 (by rfl) ⟨1294685, by rfl⟩ : syracuseStep 1726247 = 2589371) B2589371
theorem B1726505 : Blo 1148636 1726505 := bstep (se 2 (by rfl) ⟨647439, by rfl⟩ : syracuseStep 1726505 = 1294879) B1294879
theorem B1726535 : Blo 1148636 1726535 := bstep (se 1 (by rfl) ⟨1294901, by rfl⟩ : syracuseStep 1726535 = 2589803) B2589803
theorem B1726847 : Blo 1148636 1726847 := bstep (se 1 (by rfl) ⟨1295135, by rfl⟩ : syracuseStep 1726847 = 2590271) B2590271
theorem B1726919 : Blo 1148636 1726919 := bstep (se 1 (by rfl) ⟨1295189, by rfl⟩ : syracuseStep 1726919 = 2590379) B2590379
theorem B1727135 : Blo 1148636 1727135 := bstep (se 1 (by rfl) ⟨1295351, by rfl⟩ : syracuseStep 1727135 = 2590703) B2590703
theorem B1727279 : Blo 1148636 1727279 := bstep (se 1 (by rfl) ⟨1295459, by rfl⟩ : syracuseStep 1727279 = 2590919) B2590919
theorem B1727369 : Blo 1148636 1727369 := bstep (se 2 (by rfl) ⟨647763, by rfl⟩ : syracuseStep 1727369 = 1295527) B1295527
theorem B1727399 : Blo 1148636 1727399 := bstep (se 1 (by rfl) ⟨1295549, by rfl⟩ : syracuseStep 1727399 = 2591099) B2591099
theorem B4152259 : Blo 1148636 4152259 := bstep (se 1 (by rfl) ⟨3114194, by rfl⟩ : syracuseStep 4152259 = 6228389) B6228389
theorem B7363547 : Blo 1148636 7363547 := bstep (se 1 (by rfl) ⟨5522660, by rfl⟩ : syracuseStep 7363547 = 11045321) B11045321
theorem B1727579 : Blo 1148636 1727579 := bstep (se 1 (by rfl) ⟨1295684, by rfl⟩ : syracuseStep 1727579 = 2591369) B2591369
theorem B1727771 : Blo 1148636 1727771 := bstep (se 1 (by rfl) ⟨1295828, by rfl⟩ : syracuseStep 1727771 = 2591657) B2591657
theorem B8740223 : Blo 1148636 8740223 := bstep (se 1 (by rfl) ⟨6555167, by rfl⟩ : syracuseStep 8740223 = 13110335) B13110335
theorem B1728239 : Blo 1148636 1728239 := bstep (se 1 (by rfl) ⟨1296179, by rfl⟩ : syracuseStep 1728239 = 2592359) B2592359
theorem B2187175 : Blo 1148636 2187175 := bstep (se 1 (by rfl) ⟨1640381, by rfl⟩ : syracuseStep 2187175 = 3280763) B3280763
theorem B1728425 : Blo 1148636 1728425 := bstep (se 2 (by rfl) ⟨648159, by rfl⟩ : syracuseStep 1728425 = 1296319) B1296319
theorem B1728575 : Blo 1148636 1728575 := bstep (se 1 (by rfl) ⟨1296431, by rfl⟩ : syracuseStep 1728575 = 2592863) B2592863
theorem B3498191 : Blo 1148636 3498191 := bstep (se 1 (by rfl) ⟨2623643, by rfl⟩ : syracuseStep 3498191 = 5247287) B5247287
theorem B2908457 : Blo 1148636 2908457 := bstep (se 2 (by rfl) ⟨1090671, by rfl⟩ : syracuseStep 2908457 = 2181343) B2181343
theorem B1728809 : Blo 1148636 1728809 := bstep (se 2 (by rfl) ⟨648303, by rfl⟩ : syracuseStep 1728809 = 1296607) B1296607
theorem B71721449 : Blo 1148636 71721449 := bstep (se 2 (by rfl) ⟨26895543, by rfl⟩ : syracuseStep 71721449 = 53791087) B53791087
theorem B2908831 : Blo 1148636 2908831 := bstep (se 1 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 2908831 = 4363247) B4363247
theorem B13100129 : Blo 1148636 13100129 := bstep (se 2 (by rfl) ⟨4912548, by rfl⟩ : syracuseStep 13100129 = 9825097) B9825097
theorem B3106475 : Blo 1148636 3106475 := bstep (se 1 (by rfl) ⟨2329856, by rfl⟩ : syracuseStep 3106475 = 4659713) B4659713
theorem B2910239 : Blo 1148636 2910239 := bstep (se 1 (by rfl) ⟨2182679, by rfl⟩ : syracuseStep 2910239 = 4365359) B4365359
theorem B7367183 : Blo 1148636 7367183 := bstep (se 1 (by rfl) ⟨5525387, by rfl⟩ : syracuseStep 7367183 = 11050775) B11050775
theorem B13101587 : Blo 1148636 13101587 := bstep (se 1 (by rfl) ⟨9826190, by rfl⟩ : syracuseStep 13101587 = 19652381) B19652381
theorem B8744111 : Blo 1148636 8744111 := bstep (se 1 (by rfl) ⟨6558083, by rfl⟩ : syracuseStep 8744111 = 13116167) B13116167
theorem B68185489 : Blo 1148636 68185489 := bstep (se 2 (by rfl) ⟨25569558, by rfl⟩ : syracuseStep 68185489 = 51139117) B51139117
theorem B12611321 : Blo 1148636 12611321 := bstep (se 2 (by rfl) ⟨4729245, by rfl⟩ : syracuseStep 12611321 = 9458491) B9458491
theorem B2912233 : Blo 1148636 2912233 := bstep (se 2 (by rfl) ⟨1092087, by rfl⟩ : syracuseStep 2912233 = 2184175) B2184175
theorem B9957485 : Blo 1148636 9957485 := bstep (se 3 (by rfl) ⟨1867028, by rfl⟩ : syracuseStep 9957485 = 3734057) B3734057
theorem B25260295 : Blo 1148636 25260295 := bstep (se 1 (by rfl) ⟨18945221, by rfl⟩ : syracuseStep 25260295 = 37890443) B37890443
theorem B6549929 : Blo 1148636 6549929 := bstep (se 2 (by rfl) ⟨2456223, by rfl⟩ : syracuseStep 6549929 = 4912447) B4912447
theorem B2585465 : Blo 1148636 2585465 := bstep (se 2 (by rfl) ⟨969549, by rfl⟩ : syracuseStep 2585465 = 1939099) B1939099
theorem B4912123 : Blo 1148636 4912123 := bstep (se 1 (by rfl) ⟨3684092, by rfl⟩ : syracuseStep 4912123 = 7368185) B7368185
theorem B8746055 : Blo 1148636 8746055 := bstep (se 1 (by rfl) ⟨6559541, by rfl⟩ : syracuseStep 8746055 = 13119083) B13119083
theorem B7369825 : Blo 1148636 7369825 := bstep (se 2 (by rfl) ⟨2763684, by rfl⟩ : syracuseStep 7369825 = 5527369) B5527369
theorem B4912481 : Blo 1148636 4912481 := bstep (se 2 (by rfl) ⟨1842180, by rfl⟩ : syracuseStep 4912481 = 3684361) B3684361
theorem B13104503 : Blo 1148636 13104503 := bstep (se 1 (by rfl) ⟨9828377, by rfl⟩ : syracuseStep 13104503 = 19656755) B19656755
theorem B2586095 : Blo 1148636 2586095 := bstep (se 1 (by rfl) ⟨1939571, by rfl⟩ : syracuseStep 2586095 = 3879143) B3879143
theorem B6551387 : Blo 1148636 6551387 := bstep (se 1 (by rfl) ⟨4913540, by rfl⟩ : syracuseStep 6551387 = 9827081) B9827081
theorem B2455591 : Blo 1148636 2455591 := bstep (se 1 (by rfl) ⟨1841693, by rfl⟩ : syracuseStep 2455591 = 3683387) B3683387
theorem B2586671 : Blo 1148636 2586671 := bstep (se 1 (by rfl) ⟨1940003, by rfl⟩ : syracuseStep 2586671 = 3880007) B3880007
theorem B1636571 : Blo 1148636 1636571 := bstep (se 1 (by rfl) ⟨1227428, by rfl⟩ : syracuseStep 1636571 = 2454857) B2454857
theorem B2914643 : Blo 1148636 2914643 := bstep (se 1 (by rfl) ⟨2185982, by rfl⟩ : syracuseStep 2914643 = 4371965) B4371965
theorem B3930527 : Blo 1148636 3930527 := bstep (se 1 (by rfl) ⟨2947895, by rfl⟩ : syracuseStep 3930527 = 5895791) B5895791
theorem B6552161 : Blo 1148636 6552161 := bstep (se 2 (by rfl) ⟨2457060, by rfl⟩ : syracuseStep 6552161 = 4914121) B4914121
theorem B2587463 : Blo 1148636 2587463 := bstep (se 1 (by rfl) ⟨1940597, by rfl⟩ : syracuseStep 2587463 = 3881195) B3881195
theorem B2915423 : Blo 1148636 2915423 := bstep (se 1 (by rfl) ⟨2186567, by rfl⟩ : syracuseStep 2915423 = 4373135) B4373135
theorem B2457839 : Blo 1148636 2457839 := bstep (se 1 (by rfl) ⟨1843379, by rfl⟩ : syracuseStep 2457839 = 3686759) B3686759
theorem B2916607 : Blo 1148636 2916607 := bstep (se 1 (by rfl) ⟨2187455, by rfl⟩ : syracuseStep 2916607 = 4374911) B4374911
theorem B5538077 : Blo 1148636 5538077 := bstep (se 3 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 5538077 = 2076779) B2076779
theorem B2589083 : Blo 1148636 2589083 := bstep (se 1 (by rfl) ⟨1941812, by rfl⟩ : syracuseStep 2589083 = 3883625) B3883625
theorem B1148647 : Blo 1148636 1148647 := bstep (se 1 (by rfl) ⟨861485, by rfl⟩ : syracuseStep 1148647 = 1722971) B1722971
theorem B1148743 : Blo 1148636 1148743 := bstep (se 1 (by rfl) ⟨861557, by rfl⟩ : syracuseStep 1148743 = 1723115) B1723115
theorem B1148763 : Blo 1148636 1148763 := bstep (se 1 (by rfl) ⟨861572, by rfl⟩ : syracuseStep 1148763 = 1723145) B1723145
theorem B2459641 : Blo 1148636 2459641 := bstep (se 2 (by rfl) ⟨922365, by rfl⟩ : syracuseStep 2459641 = 1844731) B1844731
theorem B1149039 : Blo 1148636 1149039 := bstep (se 1 (by rfl) ⟨861779, by rfl⟩ : syracuseStep 1149039 = 1723559) B1723559
theorem B1640569 : Blo 1148636 1640569 := bstep (se 2 (by rfl) ⟨615213, by rfl⟩ : syracuseStep 1640569 = 1230427) B1230427
theorem B1149135 : Blo 1148636 1149135 := bstep (se 1 (by rfl) ⟨861851, by rfl⟩ : syracuseStep 1149135 = 1723703) B1723703
theorem B8751401 : Blo 1148636 8751401 := bstep (se 2 (by rfl) ⟨3281775, by rfl⟩ : syracuseStep 8751401 = 6563551) B6563551
theorem B1149343 : Blo 1148636 1149343 := bstep (se 1 (by rfl) ⟨862007, by rfl⟩ : syracuseStep 1149343 = 1724015) B1724015
theorem B2591135 : Blo 1148636 2591135 := bstep (se 1 (by rfl) ⟨1943351, by rfl⟩ : syracuseStep 2591135 = 3886703) B3886703
theorem B1149391 : Blo 1148636 1149391 := bstep (se 1 (by rfl) ⟨862043, by rfl⟩ : syracuseStep 1149391 = 1724087) B1724087
theorem B1149423 : Blo 1148636 1149423 := bstep (se 1 (by rfl) ⟨862067, by rfl⟩ : syracuseStep 1149423 = 1724135) B1724135
theorem B4917779 : Blo 1148636 4917779 := bstep (se 1 (by rfl) ⟨3688334, by rfl⟩ : syracuseStep 4917779 = 7376669) B7376669
theorem B2591315 : Blo 1148636 2591315 := bstep (se 1 (by rfl) ⟨1943486, by rfl⟩ : syracuseStep 2591315 = 3886973) B3886973
theorem B1149531 : Blo 1148636 1149531 := bstep (se 1 (by rfl) ⟨862148, by rfl⟩ : syracuseStep 1149531 = 1724297) B1724297
theorem B3279487 : Blo 1148636 3279487 := bstep (se 1 (by rfl) ⟨2459615, by rfl⟩ : syracuseStep 3279487 = 4919231) B4919231
theorem B1149691 : Blo 1148636 1149691 := bstep (se 1 (by rfl) ⟨862268, by rfl⟩ : syracuseStep 1149691 = 1724537) B1724537
theorem B1149695 : Blo 1148636 1149695 := bstep (se 1 (by rfl) ⟨862271, by rfl⟩ : syracuseStep 1149695 = 1724543) B1724543
theorem B4426721 : Blo 1148636 4426721 := bstep (se 2 (by rfl) ⟨1660020, by rfl⟩ : syracuseStep 4426721 = 3320041) B3320041
theorem B1150255 : Blo 1148636 1150255 := bstep (se 1 (by rfl) ⟨862691, by rfl⟩ : syracuseStep 1150255 = 1725383) B1725383
theorem B1150271 : Blo 1148636 1150271 := bstep (se 1 (by rfl) ⟨862703, by rfl⟩ : syracuseStep 1150271 = 1725407) B1725407
theorem B13995479 : Blo 1148636 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B1150495 : Blo 1148636 1150495 := bstep (se 1 (by rfl) ⟨862871, by rfl⟩ : syracuseStep 1150495 = 1725743) B1725743
theorem B5901929 : Blo 1148636 5901929 := bstep (se 2 (by rfl) ⟨2213223, by rfl⟩ : syracuseStep 5901929 = 4426447) B4426447
theorem B1150631 : Blo 1148636 1150631 := bstep (se 1 (by rfl) ⟨862973, by rfl⟩ : syracuseStep 1150631 = 1725947) B1725947
theorem B1150655 : Blo 1148636 1150655 := bstep (se 1 (by rfl) ⟨862991, by rfl⟩ : syracuseStep 1150655 = 1725983) B1725983
theorem B1150747 : Blo 1148636 1150747 := bstep (se 1 (by rfl) ⟨863060, by rfl⟩ : syracuseStep 1150747 = 1726121) B1726121
theorem B1150751 : Blo 1148636 1150751 := bstep (se 1 (by rfl) ⟨863063, by rfl⟩ : syracuseStep 1150751 = 1726127) B1726127
theorem B1150831 : Blo 1148636 1150831 := bstep (se 1 (by rfl) ⟨863123, by rfl⟩ : syracuseStep 1150831 = 1726247) B1726247
theorem B1151003 : Blo 1148636 1151003 := bstep (se 1 (by rfl) ⟨863252, by rfl⟩ : syracuseStep 1151003 = 1726505) B1726505
theorem B1151023 : Blo 1148636 1151023 := bstep (se 1 (by rfl) ⟨863267, by rfl⟩ : syracuseStep 1151023 = 1726535) B1726535
theorem B4657375 : Blo 1148636 4657375 := bstep (se 1 (by rfl) ⟨3493031, by rfl⟩ : syracuseStep 4657375 = 6986063) B6986063
theorem B1151231 : Blo 1148636 1151231 := bstep (se 1 (by rfl) ⟨863423, by rfl⟩ : syracuseStep 1151231 = 1726847) B1726847
theorem B1151279 : Blo 1148636 1151279 := bstep (se 1 (by rfl) ⟨863459, by rfl⟩ : syracuseStep 1151279 = 1726919) B1726919
theorem B1151423 : Blo 1148636 1151423 := bstep (se 1 (by rfl) ⟨863567, by rfl⟩ : syracuseStep 1151423 = 1727135) B1727135
theorem B3281435 : Blo 1148636 3281435 := bstep (se 1 (by rfl) ⟨2461076, by rfl⟩ : syracuseStep 3281435 = 4922153) B4922153
theorem B1151519 : Blo 1148636 1151519 := bstep (se 1 (by rfl) ⟨863639, by rfl⟩ : syracuseStep 1151519 = 1727279) B1727279
theorem B1151579 : Blo 1148636 1151579 := bstep (se 1 (by rfl) ⟨863684, by rfl⟩ : syracuseStep 1151579 = 1727369) B1727369
theorem B1151599 : Blo 1148636 1151599 := bstep (se 1 (by rfl) ⟨863699, by rfl⟩ : syracuseStep 1151599 = 1727399) B1727399
theorem B1151719 : Blo 1148636 1151719 := bstep (se 1 (by rfl) ⟨863789, by rfl⟩ : syracuseStep 1151719 = 1727579) B1727579
theorem B1151847 : Blo 1148636 1151847 := bstep (se 1 (by rfl) ⟨863885, by rfl⟩ : syracuseStep 1151847 = 1727771) B1727771
theorem B1152159 : Blo 1148636 1152159 := bstep (se 1 (by rfl) ⟨864119, by rfl⟩ : syracuseStep 1152159 = 1728239) B1728239
theorem B1152283 : Blo 1148636 1152283 := bstep (se 1 (by rfl) ⟨864212, by rfl⟩ : syracuseStep 1152283 = 1728425) B1728425
theorem B1152383 : Blo 1148636 1152383 := bstep (se 1 (by rfl) ⟨864287, by rfl⟩ : syracuseStep 1152383 = 1728575) B1728575
theorem B2332127 : Blo 1148636 2332127 := bstep (se 1 (by rfl) ⟨1749095, by rfl⟩ : syracuseStep 2332127 = 3498191) B3498191
theorem B1938971 : Blo 1148636 1938971 := bstep (se 1 (by rfl) ⟨1454228, by rfl⟩ : syracuseStep 1938971 = 2908457) B2908457
theorem B1152539 : Blo 1148636 1152539 := bstep (se 1 (by rfl) ⟨864404, by rfl⟩ : syracuseStep 1152539 = 1728809) B1728809
theorem B47814299 : Blo 1148636 47814299 := bstep (se 1 (by rfl) ⟨35860724, by rfl⟩ : syracuseStep 47814299 = 71721449) B71721449
theorem B4364189 : Blo 1148636 4364189 := bstep (se 3 (by rfl) ⟨818285, by rfl⟩ : syracuseStep 4364189 = 1636571) B1636571
theorem B2070983 : Blo 1148636 2070983 := bstep (se 1 (by rfl) ⟨1553237, by rfl⟩ : syracuseStep 2070983 = 3106475) B3106475
theorem B1940159 : Blo 1148636 1940159 := bstep (se 1 (by rfl) ⟨1455119, by rfl⟩ : syracuseStep 1940159 = 2910239) B2910239
theorem B5053271 : Blo 1148636 5053271 := bstep (se 1 (by rfl) ⟨3789953, by rfl⟩ : syracuseStep 5053271 = 7579907) B7579907
theorem B3546695 : Blo 1148636 3546695 := bstep (se 1 (by rfl) ⟨2660021, by rfl⟩ : syracuseStep 3546695 = 5320043) B5320043
theorem B1941097 : Blo 1148636 1941097 := bstep (se 2 (by rfl) ⟨727911, by rfl⟩ : syracuseStep 1941097 = 1455823) B1455823
theorem B8724671 : Blo 1148636 8724671 := bstep (se 1 (by rfl) ⟨6543503, by rfl⟩ : syracuseStep 8724671 = 13087007) B13087007
theorem B4366619 : Blo 1148636 4366619 := bstep (se 1 (by rfl) ⟨3274964, by rfl⟩ : syracuseStep 4366619 = 6549929) B6549929
theorem B5907611 : Blo 1148636 5907611 := bstep (se 1 (by rfl) ⟨4430708, by rfl⟩ : syracuseStep 5907611 = 8861417) B8861417
theorem B4367591 : Blo 1148636 4367591 := bstep (se 1 (by rfl) ⟨3275693, by rfl⟩ : syracuseStep 4367591 = 6551387) B6551387
theorem B1943095 : Blo 1148636 1943095 := bstep (se 1 (by rfl) ⟨1457321, by rfl⟩ : syracuseStep 1943095 = 2914643) B2914643
theorem B4368107 : Blo 1148636 4368107 := bstep (se 1 (by rfl) ⟨3276080, by rfl⟩ : syracuseStep 4368107 = 6552161) B6552161
theorem B1943615 : Blo 1148636 1943615 := bstep (se 1 (by rfl) ⟨1457711, by rfl⟩ : syracuseStep 1943615 = 2915423) B2915423
theorem B3877307 : Blo 1148636 3877307 := bstep (se 1 (by rfl) ⟨2907980, by rfl⟩ : syracuseStep 3877307 = 5815961) B5815961
theorem B1944391 : Blo 1148636 1944391 := bstep (se 1 (by rfl) ⟨1458293, by rfl⟩ : syracuseStep 1944391 = 2916587) B2916587
theorem B3878063 : Blo 1148636 3878063 := bstep (se 1 (by rfl) ⟨2908547, by rfl⟩ : syracuseStep 3878063 = 5817095) B5817095
theorem B4369747 : Blo 1148636 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B3878441 : Blo 1148636 3878441 := bstep (se 2 (by rfl) ⟨1454415, by rfl⟩ : syracuseStep 3878441 = 2908831) B2908831
theorem B5254951 : Blo 1148636 5254951 := bstep (se 1 (by rfl) ⟨3941213, by rfl⟩ : syracuseStep 5254951 = 7882427) B7882427
theorem B14724935 : Blo 1148636 14724935 := bstep (se 1 (by rfl) ⟨11043701, by rfl⟩ : syracuseStep 14724935 = 22087403) B22087403
theorem B8728559 : Blo 1148636 8728559 := bstep (se 1 (by rfl) ⟨6546419, by rfl⟩ : syracuseStep 8728559 = 13092839) B13092839
theorem B4042855 : Blo 1148636 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B4370719 : Blo 1148636 4370719 := bstep (se 1 (by rfl) ⟨3278039, by rfl⟩ : syracuseStep 4370719 = 6556079) B6556079
theorem B4371023 : Blo 1148636 4371023 := bstep (se 1 (by rfl) ⟨3278267, by rfl⟩ : syracuseStep 4371023 = 6556535) B6556535
theorem B75707243 : Blo 1148636 75707243 := bstep (se 1 (by rfl) ⟨56780432, by rfl⟩ : syracuseStep 75707243 = 113560865) B113560865
theorem B16561057 : Blo 1148636 16561057 := bstep (se 2 (by rfl) ⟨6210396, by rfl⟩ : syracuseStep 16561057 = 12420793) B12420793
theorem B8729531 : Blo 1148636 8729531 := bstep (se 1 (by rfl) ⟨6547148, by rfl⟩ : syracuseStep 8729531 = 13094297) B13094297
theorem B15382061 : Blo 1148636 15382061 := bstep (se 3 (by rfl) ⟨2884136, by rfl⟩ : syracuseStep 15382061 = 5768273) B5768273
theorem B9844577 : Blo 1148636 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B12433505 : Blo 1148636 12433505 := bstep (se 2 (by rfl) ⟨4662564, by rfl⟩ : syracuseStep 12433505 = 9325129) B9325129
theorem B4372663 : Blo 1148636 4372663 := bstep (se 1 (by rfl) ⟨3279497, by rfl⟩ : syracuseStep 4372663 = 6558995) B6558995
theorem B1751771 : Blo 1148636 1751771 := bstep (se 1 (by rfl) ⟨1313828, by rfl⟩ : syracuseStep 1751771 = 2627657) B2627657
theorem B90913985 : Blo 1148636 90913985 := bstep (se 2 (by rfl) ⟨34092744, by rfl⟩ : syracuseStep 90913985 = 68185489) B68185489
theorem B3882653 : Blo 1148636 3882653 := bstep (se 3 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 3882653 = 1455995) B1455995
theorem B3882977 : Blo 1148636 3882977 := bstep (se 2 (by rfl) ⟨1456116, by rfl⟩ : syracuseStep 3882977 = 2912233) B2912233
theorem B8733419 : Blo 1148636 8733419 := bstep (se 1 (by rfl) ⟨6550064, by rfl⟩ : syracuseStep 8733419 = 13100129) B13100129
theorem B1295167 : Blo 1148636 1295167 := bstep (se 1 (by rfl) ⟨971375, by rfl⟩ : syracuseStep 1295167 = 1942751) B1942751
theorem B1296031 : Blo 1148636 1296031 := bstep (se 1 (by rfl) ⟨972023, by rfl⟩ : syracuseStep 1296031 = 1944047) B1944047
theorem B8734391 : Blo 1148636 8734391 := bstep (se 1 (by rfl) ⟨6550793, by rfl⟩ : syracuseStep 8734391 = 13101587) B13101587
theorem B4376339 : Blo 1148636 4376339 := bstep (se 1 (by rfl) ⟨3282254, by rfl⟩ : syracuseStep 4376339 = 6564509) B6564509
theorem B8407547 : Blo 1148636 8407547 := bstep (se 1 (by rfl) ⟨6305660, by rfl⟩ : syracuseStep 8407547 = 12611321) B12611321
theorem B8407709 : Blo 1148636 8407709 := bstep (se 3 (by rfl) ⟨1576445, by rfl⟩ : syracuseStep 8407709 = 3152891) B3152891
theorem B6638323 : Blo 1148636 6638323 := bstep (se 1 (by rfl) ⟨4978742, by rfl⟩ : syracuseStep 6638323 = 9957485) B9957485
theorem B1723643 : Blo 1148636 1723643 := bstep (se 1 (by rfl) ⟨1292732, by rfl⟩ : syracuseStep 1723643 = 2585465) B2585465
theorem B8736335 : Blo 1148636 8736335 := bstep (se 1 (by rfl) ⟨6552251, by rfl⟩ : syracuseStep 8736335 = 13104503) B13104503
theorem B1724063 : Blo 1148636 1724063 := bstep (se 1 (by rfl) ⟨1293047, by rfl⟩ : syracuseStep 1724063 = 2586095) B2586095
theorem B1724393 : Blo 1148636 1724393 := bstep (se 2 (by rfl) ⟨646647, by rfl⟩ : syracuseStep 1724393 = 1293295) B1293295
theorem B1724447 : Blo 1148636 1724447 := bstep (se 1 (by rfl) ⟨1293335, by rfl⟩ : syracuseStep 1724447 = 2586671) B2586671
theorem B1724975 : Blo 1148636 1724975 := bstep (se 1 (by rfl) ⟨1293731, by rfl⟩ : syracuseStep 1724975 = 2587463) B2587463
theorem B1725161 : Blo 1148636 1725161 := bstep (se 2 (by rfl) ⟨646935, by rfl⟩ : syracuseStep 1725161 = 1293871) B1293871
theorem B1725305 : Blo 1148636 1725305 := bstep (se 2 (by rfl) ⟨646989, by rfl⟩ : syracuseStep 1725305 = 1293979) B1293979
theorem B22173215 : Blo 1148636 22173215 := bstep (se 1 (by rfl) ⟨16629911, by rfl⟩ : syracuseStep 22173215 = 33259823) B33259823
theorem B1726007 : Blo 1148636 1726007 := bstep (se 1 (by rfl) ⟨1294505, by rfl⟩ : syracuseStep 1726007 = 2589011) B2589011
theorem B3888863 : Blo 1148636 3888863 := bstep (se 1 (by rfl) ⟨2916647, by rfl⟩ : syracuseStep 3888863 = 5833295) B5833295
theorem B16570169 : Blo 1148636 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B3889025 : Blo 1148636 3889025 := bstep (se 2 (by rfl) ⟨1458384, by rfl⟩ : syracuseStep 3889025 = 2916769) B2916769
theorem B1726511 : Blo 1148636 1726511 := bstep (se 1 (by rfl) ⟨1294883, by rfl⟩ : syracuseStep 1726511 = 2589767) B2589767
theorem B5822603 : Blo 1148636 5822603 := bstep (se 1 (by rfl) ⟨4366952, by rfl⟩ : syracuseStep 5822603 = 8733905) B8733905
theorem B1726631 : Blo 1148636 1726631 := bstep (se 1 (by rfl) ⟨1294973, by rfl⟩ : syracuseStep 1726631 = 2589947) B2589947
theorem B2185451 : Blo 1148636 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B1726799 : Blo 1148636 1726799 := bstep (se 1 (by rfl) ⟨1295099, by rfl⟩ : syracuseStep 1726799 = 2590199) B2590199
theorem B4151999 : Blo 1148636 4151999 := bstep (se 1 (by rfl) ⟨3113999, by rfl⟩ : syracuseStep 4151999 = 6227999) B6227999
theorem B3889889 : Blo 1148636 3889889 := bstep (se 2 (by rfl) ⟨1458708, by rfl⟩ : syracuseStep 3889889 = 2917417) B2917417
theorem B1727519 : Blo 1148636 1727519 := bstep (se 1 (by rfl) ⟨1295639, by rfl⟩ : syracuseStep 1727519 = 2591279) B2591279
theorem B2186651 : Blo 1148636 2186651 := bstep (se 1 (by rfl) ⟨1639988, by rfl⟩ : syracuseStep 2186651 = 3279977) B3279977
theorem B1727951 : Blo 1148636 1727951 := bstep (se 1 (by rfl) ⟨1295963, by rfl⟩ : syracuseStep 1727951 = 2591927) B2591927
theorem B2908001 : Blo 1148636 2908001 := bstep (se 2 (by rfl) ⟨1090500, by rfl⟩ : syracuseStep 2908001 = 2181001) B2181001
theorem B2187319 : Blo 1148636 2187319 := bstep (se 1 (by rfl) ⟨1640489, by rfl⟩ : syracuseStep 2187319 = 3280979) B3280979
theorem B9822707 : Blo 1148636 9822707 := bstep (se 1 (by rfl) ⟨7367030, by rfl⟩ : syracuseStep 9822707 = 14734061) B14734061
theorem B1292198791 : Blo 1148636 1292198791 := bstep (se 1 (by rfl) ⟨969149093, by rfl⟩ : syracuseStep 1292198791 = 1938298187) B1938298187
theorem B2909135 : Blo 1148636 2909135 := bstep (se 1 (by rfl) ⟨2181851, by rfl⟩ : syracuseStep 2909135 = 4363703) B4363703
theorem B13264087 : Blo 1148636 13264087 := bstep (se 1 (by rfl) ⟨9948065, by rfl⟩ : syracuseStep 13264087 = 19896131) B19896131
theorem B4909031 : Blo 1148636 4909031 := bstep (se 1 (by rfl) ⟨3681773, by rfl⟩ : syracuseStep 4909031 = 7363547) B7363547
theorem B27944939 : Blo 1148636 27944939 := bstep (se 1 (by rfl) ⟨20958704, by rfl⟩ : syracuseStep 27944939 = 41917409) B41917409
theorem B11823137 : Blo 1148636 11823137 := bstep (se 2 (by rfl) ⟨4433676, by rfl⟩ : syracuseStep 11823137 = 8867353) B8867353
theorem B2910451 : Blo 1148636 2910451 := bstep (se 1 (by rfl) ⟨2182838, by rfl⟩ : syracuseStep 2910451 = 4365677) B4365677
theorem B5826815 : Blo 1148636 5826815 := bstep (se 1 (by rfl) ⟨4370111, by rfl⟩ : syracuseStep 5826815 = 8740223) B8740223
theorem B33680393 : Blo 1148636 33680393 := bstep (se 2 (by rfl) ⟨12630147, by rfl⟩ : syracuseStep 33680393 = 25260295) B25260295
theorem B9334025 : Blo 1148636 9334025 := bstep (se 2 (by rfl) ⟨3500259, by rfl⟩ : syracuseStep 9334025 = 7000519) B7000519
theorem B13266305 : Blo 1148636 13266305 := bstep (se 2 (by rfl) ⟨4974864, by rfl⟩ : syracuseStep 13266305 = 9949729) B9949729
theorem B6549497 : Blo 1148636 6549497 := bstep (se 2 (by rfl) ⟨2456061, by rfl⟩ : syracuseStep 6549497 = 4912123) B4912123
theorem B9826433 : Blo 1148636 9826433 := bstep (se 2 (by rfl) ⟨3684912, by rfl⟩ : syracuseStep 9826433 = 7369825) B7369825
theorem B2912395 : Blo 1148636 2912395 := bstep (se 1 (by rfl) ⟨2184296, by rfl⟩ : syracuseStep 2912395 = 4368593) B4368593
theorem B15757577 : Blo 1148636 15757577 := bstep (se 2 (by rfl) ⟨5909091, by rfl⟩ : syracuseStep 15757577 = 11818183) B11818183
theorem B4911455 : Blo 1148636 4911455 := bstep (se 1 (by rfl) ⟨3683591, by rfl⟩ : syracuseStep 4911455 = 7367183) B7367183
theorem B5829407 : Blo 1148636 5829407 := bstep (se 1 (by rfl) ⟨4372055, by rfl⟩ : syracuseStep 5829407 = 8744111) B8744111
theorem B18674657 : Blo 1148636 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B2454695 : Blo 1148636 2454695 := bstep (se 1 (by rfl) ⟨1841021, by rfl⟩ : syracuseStep 2454695 = 3682043) B3682043
theorem B3274121 : Blo 1148636 3274121 := bstep (se 2 (by rfl) ⟨1227795, by rfl⟩ : syracuseStep 3274121 = 2455591) B2455591
theorem B5535229 : Blo 1148636 5535229 := bstep (se 3 (by rfl) ⟨1037855, by rfl⟩ : syracuseStep 5535229 = 2075711) B2075711
theorem B2455147 : Blo 1148636 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B121174001 : Blo 1148636 121174001 := bstep (se 2 (by rfl) ⟨45440250, by rfl⟩ : syracuseStep 121174001 = 90880501) B90880501
theorem B5830703 : Blo 1148636 5830703 := bstep (se 1 (by rfl) ⟨4373027, by rfl⟩ : syracuseStep 5830703 = 8746055) B8746055
theorem B2586761 : Blo 1148636 2586761 := bstep (se 2 (by rfl) ⟨970035, by rfl⟩ : syracuseStep 2586761 = 1940071) B1940071
theorem B5830865 : Blo 1148636 5830865 := bstep (se 2 (by rfl) ⟨2186574, by rfl⟩ : syracuseStep 5830865 = 4373149) B4373149
theorem B3274987 : Blo 1148636 3274987 := bstep (se 1 (by rfl) ⟨2456240, by rfl⟩ : syracuseStep 3274987 = 4912481) B4912481
theorem B2586977 : Blo 1148636 2586977 := bstep (se 2 (by rfl) ⟨970116, by rfl⟩ : syracuseStep 2586977 = 1940233) B1940233
theorem B2914663 : Blo 1148636 2914663 := bstep (se 1 (by rfl) ⟨2185997, by rfl⟩ : syracuseStep 2914663 = 4371995) B4371995
theorem B2455967 : Blo 1148636 2455967 := bstep (se 1 (by rfl) ⟨1841975, by rfl⟩ : syracuseStep 2455967 = 3683951) B3683951
theorem B8747513 : Blo 1148636 8747513 := bstep (se 2 (by rfl) ⟨3280317, by rfl⟩ : syracuseStep 8747513 = 6560635) B6560635
theorem B5536345 : Blo 1148636 5536345 := bstep (se 2 (by rfl) ⟨2076129, by rfl⟩ : syracuseStep 5536345 = 4152259) B4152259
theorem B2620351 : Blo 1148636 2620351 := bstep (se 1 (by rfl) ⟨1965263, by rfl⟩ : syracuseStep 2620351 = 3930527) B3930527
theorem B2915311 : Blo 1148636 2915311 := bstep (se 1 (by rfl) ⟨2186483, by rfl⟩ : syracuseStep 2915311 = 4372967) B4372967
theorem B2916233 : Blo 1148636 2916233 := bstep (se 2 (by rfl) ⟨1093587, by rfl⟩ : syracuseStep 2916233 = 2187175) B2187175
theorem B2916425 : Blo 1148636 2916425 := bstep (se 2 (by rfl) ⟨1093659, by rfl⟩ : syracuseStep 2916425 = 2187319) B2187319
theorem B1638559 : Blo 1148636 1638559 := bstep (se 1 (by rfl) ⟨1228919, by rfl⟩ : syracuseStep 1638559 = 2457839) B2457839
theorem B2917559 : Blo 1148636 2917559 := bstep (se 1 (by rfl) ⟨2188169, by rfl⟩ : syracuseStep 2917559 = 4376339) B4376339
theorem B5834267 : Blo 1148636 5834267 := bstep (se 1 (by rfl) ⟨4375700, by rfl⟩ : syracuseStep 5834267 = 8751401) B8751401
theorem B5605031 : Blo 1148636 5605031 := bstep (se 1 (by rfl) ⟨4203773, by rfl⟩ : syracuseStep 5605031 = 8407547) B8407547
theorem B3278519 : Blo 1148636 3278519 := bstep (se 1 (by rfl) ⟨2458889, by rfl⟩ : syracuseStep 3278519 = 4917779) B4917779
theorem B5605139 : Blo 1148636 5605139 := bstep (se 1 (by rfl) ⟨4203854, by rfl⟩ : syracuseStep 5605139 = 8407709) B8407709
theorem B2951147 : Blo 1148636 2951147 := bstep (se 1 (by rfl) ⟨2213360, by rfl⟩ : syracuseStep 2951147 = 4426721) B4426721
theorem B2590793 : Blo 1148636 2590793 := bstep (se 2 (by rfl) ⟨971547, by rfl⟩ : syracuseStep 2590793 = 1943095) B1943095
theorem B1149095 : Blo 1148636 1149095 := bstep (se 1 (by rfl) ⟨861821, by rfl⟩ : syracuseStep 1149095 = 1723643) B1723643
theorem B3934619 : Blo 1148636 3934619 := bstep (se 1 (by rfl) ⟨2950964, by rfl⟩ : syracuseStep 3934619 = 5901929) B5901929
theorem B1149375 : Blo 1148636 1149375 := bstep (se 1 (by rfl) ⟨862031, by rfl⟩ : syracuseStep 1149375 = 1724063) B1724063
theorem B1149595 : Blo 1148636 1149595 := bstep (se 1 (by rfl) ⟨862196, by rfl⟩ : syracuseStep 1149595 = 1724393) B1724393
theorem B3279521 : Blo 1148636 3279521 := bstep (se 2 (by rfl) ⟨1229820, by rfl⟩ : syracuseStep 3279521 = 2459641) B2459641
theorem B1149631 : Blo 1148636 1149631 := bstep (se 1 (by rfl) ⟨862223, by rfl⟩ : syracuseStep 1149631 = 1724447) B1724447
theorem B1149983 : Blo 1148636 1149983 := bstep (se 1 (by rfl) ⟨862487, by rfl⟩ : syracuseStep 1149983 = 1724975) B1724975
theorem B1150107 : Blo 1148636 1150107 := bstep (se 1 (by rfl) ⟨862580, by rfl⟩ : syracuseStep 1150107 = 1725161) B1725161
theorem B1150203 : Blo 1148636 1150203 := bstep (se 1 (by rfl) ⟨862652, by rfl⟩ : syracuseStep 1150203 = 1725305) B1725305
theorem B8851097 : Blo 1148636 8851097 := bstep (se 2 (by rfl) ⟨3319161, by rfl⟩ : syracuseStep 8851097 = 6638323) B6638323
theorem B1150671 : Blo 1148636 1150671 := bstep (se 1 (by rfl) ⟨863003, by rfl⟩ : syracuseStep 1150671 = 1726007) B1726007
theorem B2592521 : Blo 1148636 2592521 := bstep (se 2 (by rfl) ⟨972195, by rfl⟩ : syracuseStep 2592521 = 1944391) B1944391
theorem B2592575 : Blo 1148636 2592575 := bstep (se 1 (by rfl) ⟨1944431, by rfl⟩ : syracuseStep 2592575 = 3888863) B3888863
theorem B11046779 : Blo 1148636 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B2592683 : Blo 1148636 2592683 := bstep (se 1 (by rfl) ⟨1944512, by rfl⟩ : syracuseStep 2592683 = 3889025) B3889025
theorem B1151007 : Blo 1148636 1151007 := bstep (se 1 (by rfl) ⟨863255, by rfl⟩ : syracuseStep 1151007 = 1726511) B1726511
theorem B1151087 : Blo 1148636 1151087 := bstep (se 1 (by rfl) ⟨863315, by rfl⟩ : syracuseStep 1151087 = 1726631) B1726631
theorem B1151199 : Blo 1148636 1151199 := bstep (se 1 (by rfl) ⟨863399, by rfl⟩ : syracuseStep 1151199 = 1726799) B1726799
theorem B1380655 : Blo 1148636 1380655 := bstep (se 1 (by rfl) ⟨1035491, by rfl⟩ : syracuseStep 1380655 = 2070983) B2070983
theorem B2593259 : Blo 1148636 2593259 := bstep (se 1 (by rfl) ⟨1944944, by rfl⟩ : syracuseStep 2593259 = 3889889) B3889889
theorem B1151679 : Blo 1148636 1151679 := bstep (se 1 (by rfl) ⟨863759, by rfl⟩ : syracuseStep 1151679 = 1727519) B1727519
theorem B1151967 : Blo 1148636 1151967 := bstep (se 1 (by rfl) ⟨863975, by rfl⟩ : syracuseStep 1151967 = 1727951) B1727951
theorem B2364463 : Blo 1148636 2364463 := bstep (se 1 (by rfl) ⟨1773347, by rfl⟩ : syracuseStep 2364463 = 3546695) B3546695
theorem B1938667 : Blo 1148636 1938667 := bstep (se 1 (by rfl) ⟨1454000, by rfl⟩ : syracuseStep 1938667 = 2908001) B2908001
theorem B74519837 : Blo 1148636 74519837 := bstep (se 3 (by rfl) ⟨13972469, by rfl⟩ : syracuseStep 74519837 = 27944939) B27944939
theorem B1939423 : Blo 1148636 1939423 := bstep (se 1 (by rfl) ⟨1454567, by rfl⟩ : syracuseStep 1939423 = 2909135) B2909135
theorem B7380305 : Blo 1148636 7380305 := bstep (se 2 (by rfl) ⟨2767614, by rfl⟩ : syracuseStep 7380305 = 5535229) B5535229
theorem B22453595 : Blo 1148636 22453595 := bstep (se 1 (by rfl) ⟨16840196, by rfl⟩ : syracuseStep 22453595 = 33680393) B33680393
theorem B13475389 : Blo 1148636 13475389 := bstep (se 3 (by rfl) ⟨2526635, by rfl⟩ : syracuseStep 13475389 = 5053271) B5053271
theorem B4366331 : Blo 1148636 4366331 := bstep (se 1 (by rfl) ⟨3274748, by rfl⟩ : syracuseStep 4366331 = 6549497) B6549497
theorem B4366649 : Blo 1148636 4366649 := bstep (se 2 (by rfl) ⟨1637493, by rfl⟩ : syracuseStep 4366649 = 3274987) B3274987
theorem B50471495 : Blo 1148636 50471495 := bstep (se 1 (by rfl) ⟨37853621, by rfl⟩ : syracuseStep 50471495 = 75707243) B75707243
theorem B7381793 : Blo 1148636 7381793 := bstep (se 2 (by rfl) ⟨2768172, by rfl⟩ : syracuseStep 7381793 = 5536345) B5536345
theorem B6563051 : Blo 1148636 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B80782667 : Blo 1148636 80782667 := bstep (se 1 (by rfl) ⟨60587000, by rfl⟩ : syracuseStep 80782667 = 121174001) B121174001
theorem B1944155 : Blo 1148636 1944155 := bstep (se 1 (by rfl) ⟨1458116, by rfl⟩ : syracuseStep 1944155 = 2916233) B2916233
theorem B3880601 : Blo 1148636 3880601 := bstep (se 2 (by rfl) ⟨1455225, by rfl⟩ : syracuseStep 3880601 = 2910451) B2910451
theorem B4372649 : Blo 1148636 4372649 := bstep (se 2 (by rfl) ⟨1639743, by rfl⟩ : syracuseStep 4372649 = 3279487) B3279487
theorem B1554751 : Blo 1148636 1554751 := bstep (se 1 (by rfl) ⟨1166063, by rfl⟩ : syracuseStep 1554751 = 2332127) B2332127
theorem B1292647 : Blo 1148636 1292647 := bstep (se 1 (by rfl) ⟨969485, by rfl⟩ : syracuseStep 1292647 = 1938971) B1938971
theorem B8730989 : Blo 1148636 8730989 := bstep (se 3 (by rfl) ⟨1637060, by rfl⟩ : syracuseStep 8730989 = 3274121) B3274121
theorem B59128573 : Blo 1148636 59128573 := bstep (se 3 (by rfl) ⟨11086607, by rfl⟩ : syracuseStep 59128573 = 22173215) B22173215
theorem B3881735 : Blo 1148636 3881735 := bstep (se 1 (by rfl) ⟨2911301, by rfl⟩ : syracuseStep 3881735 = 5822603) B5822603
theorem B1456967 : Blo 1148636 1456967 := bstep (se 1 (by rfl) ⟨1092725, by rfl⟩ : syracuseStep 1456967 = 2185451) B2185451
theorem B1293439 : Blo 1148636 1293439 := bstep (se 1 (by rfl) ⟨970079, by rfl⟩ : syracuseStep 1293439 = 1940159) B1940159
theorem B1457767 : Blo 1148636 1457767 := bstep (se 1 (by rfl) ⟨1093325, by rfl⟩ : syracuseStep 1457767 = 2186651) B2186651
theorem B5816447 : Blo 1148636 5816447 := bstep (se 1 (by rfl) ⟨4362335, by rfl⟩ : syracuseStep 5816447 = 8724671) B8724671
theorem B5390473 : Blo 1148636 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B3883193 : Blo 1148636 3883193 := bstep (se 2 (by rfl) ⟨1456197, by rfl⟩ : syracuseStep 3883193 = 2912395) B2912395
theorem B6209833 : Blo 1148636 6209833 := bstep (se 2 (by rfl) ⟨2328687, by rfl⟩ : syracuseStep 6209833 = 4657375) B4657375
theorem B7882091 : Blo 1148636 7882091 := bstep (se 1 (by rfl) ⟨5911568, by rfl⟩ : syracuseStep 7882091 = 11823137) B11823137
theorem B1295743 : Blo 1148636 1295743 := bstep (se 1 (by rfl) ⟨971807, by rfl⟩ : syracuseStep 1295743 = 1943615) B1943615
theorem B3884543 : Blo 1148636 3884543 := bstep (se 1 (by rfl) ⟨2913407, by rfl⟩ : syracuseStep 3884543 = 5826815) B5826815
theorem B9816623 : Blo 1148636 9816623 := bstep (se 1 (by rfl) ⟨7362467, by rfl⟩ : syracuseStep 9816623 = 14724935) B14724935
theorem B5819039 : Blo 1148636 5819039 := bstep (se 1 (by rfl) ⟨4364279, by rfl⟩ : syracuseStep 5819039 = 8728559) B8728559
theorem B10505051 : Blo 1148636 10505051 := bstep (se 1 (by rfl) ⟨7878788, by rfl⟩ : syracuseStep 10505051 = 15757577) B15757577
theorem B3886217 : Blo 1148636 3886217 := bstep (se 2 (by rfl) ⟨1457331, by rfl⟩ : syracuseStep 3886217 = 2914663) B2914663
theorem B3886271 : Blo 1148636 3886271 := bstep (se 1 (by rfl) ⟨2914703, by rfl⟩ : syracuseStep 3886271 = 5829407) B5829407
theorem B5819687 : Blo 1148636 5819687 := bstep (se 1 (by rfl) ⟨4364765, by rfl⟩ : syracuseStep 5819687 = 8729531) B8729531
theorem B3493801 : Blo 1148636 3493801 := bstep (se 2 (by rfl) ⟨1310175, by rfl⟩ : syracuseStep 3493801 = 2620351) B2620351
theorem B3887081 : Blo 1148636 3887081 := bstep (se 2 (by rfl) ⟨1457655, by rfl⟩ : syracuseStep 3887081 = 2915311) B2915311
theorem B3887135 : Blo 1148636 3887135 := bstep (se 1 (by rfl) ⟨2915351, by rfl⟩ : syracuseStep 3887135 = 5830703) B5830703
theorem B1724507 : Blo 1148636 1724507 := bstep (se 1 (by rfl) ⟨1293380, by rfl⟩ : syracuseStep 1724507 = 2586761) B2586761
theorem B3887243 : Blo 1148636 3887243 := bstep (se 1 (by rfl) ⟨2915432, by rfl⟩ : syracuseStep 3887243 = 5830865) B5830865
theorem B1724651 : Blo 1148636 1724651 := bstep (se 1 (by rfl) ⟨1293488, by rfl⟩ : syracuseStep 1724651 = 2586977) B2586977
theorem B1167847 : Blo 1148636 1167847 := bstep (se 1 (by rfl) ⟨875885, by rfl⟩ : syracuseStep 1167847 = 1751771) B1751771
theorem B60609323 : Blo 1148636 60609323 := bstep (se 1 (by rfl) ⟨45456992, by rfl⟩ : syracuseStep 60609323 = 90913985) B90913985
theorem B3692051 : Blo 1148636 3692051 := bstep (se 1 (by rfl) ⟨2769038, by rfl⟩ : syracuseStep 3692051 = 5538077) B5538077
theorem B1726055 : Blo 1148636 1726055 := bstep (se 1 (by rfl) ⟨1294541, by rfl⟩ : syracuseStep 1726055 = 2589083) B2589083
theorem B3888809 : Blo 1148636 3888809 := bstep (se 2 (by rfl) ⟨1458303, by rfl⟩ : syracuseStep 3888809 = 2916607) B2916607
theorem B5822279 : Blo 1148636 5822279 := bstep (se 1 (by rfl) ⟨4366709, by rfl⟩ : syracuseStep 5822279 = 8733419) B8733419
theorem B13097213 : Blo 1148636 13097213 := bstep (se 3 (by rfl) ⟨2455727, by rfl⟩ : syracuseStep 13097213 = 4911455) B4911455
theorem B1726889 : Blo 1148636 1726889 := bstep (se 2 (by rfl) ⟨647583, by rfl⟩ : syracuseStep 1726889 = 1295167) B1295167
theorem B5822927 : Blo 1148636 5822927 := bstep (se 1 (by rfl) ⟨4367195, by rfl⟩ : syracuseStep 5822927 = 8734391) B8734391
theorem B1722931721 : Blo 1148636 1722931721 := bstep (se 2 (by rfl) ⟨646099395, by rfl⟩ : syracuseStep 1722931721 = 1292198791) B1292198791
theorem B1727423 : Blo 1148636 1727423 := bstep (se 1 (by rfl) ⟨1295567, by rfl⟩ : syracuseStep 1727423 = 2591135) B2591135
theorem B17685449 : Blo 1148636 17685449 := bstep (se 2 (by rfl) ⟨6632043, by rfl⟩ : syracuseStep 17685449 = 13264087) B13264087
theorem B1727543 : Blo 1148636 1727543 := bstep (se 1 (by rfl) ⟨1295657, by rfl⟩ : syracuseStep 1727543 = 2591315) B2591315
theorem B1728041 : Blo 1148636 1728041 := bstep (se 2 (by rfl) ⟨648015, by rfl⟩ : syracuseStep 1728041 = 1296031) B1296031
theorem B9330319 : Blo 1148636 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B5824223 : Blo 1148636 5824223 := bstep (se 1 (by rfl) ⟨4368167, by rfl⟩ : syracuseStep 5824223 = 8736335) B8736335
theorem B2187425 : Blo 1148636 2187425 := bstep (se 2 (by rfl) ⟨820284, by rfl⟩ : syracuseStep 2187425 = 1640569) B1640569
theorem B2187623 : Blo 1148636 2187623 := bstep (se 1 (by rfl) ⟨1640717, by rfl⟩ : syracuseStep 2187623 = 3281435) B3281435
theorem B15753629 : Blo 1148636 15753629 := bstep (se 3 (by rfl) ⟨2953805, by rfl⟩ : syracuseStep 15753629 = 5907611) B5907611
theorem B31876199 : Blo 1148636 31876199 := bstep (se 1 (by rfl) ⟨23907149, by rfl⟩ : syracuseStep 31876199 = 47814299) B47814299
theorem B2909459 : Blo 1148636 2909459 := bstep (se 1 (by rfl) ⟨2182094, by rfl⟩ : syracuseStep 2909459 = 4364189) B4364189
theorem B5826329 : Blo 1148636 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B7006601 : Blo 1148636 7006601 := bstep (se 2 (by rfl) ⟨2627475, by rfl⟩ : syracuseStep 7006601 = 5254951) B5254951
theorem B2911079 : Blo 1148636 2911079 := bstep (se 1 (by rfl) ⟨2183309, by rfl⟩ : syracuseStep 2911079 = 4366619) B4366619
theorem B33156013 : Blo 1148636 33156013 := bstep (se 3 (by rfl) ⟨6216752, by rfl⟩ : syracuseStep 33156013 = 12433505) B12433505
theorem B6548471 : Blo 1148636 6548471 := bstep (se 1 (by rfl) ⟨4911353, by rfl⟩ : syracuseStep 6548471 = 9822707) B9822707
theorem B5827625 : Blo 1148636 5827625 := bstep (se 2 (by rfl) ⟨2185359, by rfl⟩ : syracuseStep 5827625 = 4370719) B4370719
theorem B2911727 : Blo 1148636 2911727 := bstep (se 1 (by rfl) ⟨2183795, by rfl⟩ : syracuseStep 2911727 = 4367591) B4367591
theorem B6549245 : Blo 1148636 6549245 := bstep (se 3 (by rfl) ⟨1227983, by rfl⟩ : syracuseStep 6549245 = 2455967) B2455967
theorem B2912071 : Blo 1148636 2912071 := bstep (se 1 (by rfl) ⟨2184053, by rfl⟩ : syracuseStep 2912071 = 4368107) B4368107
theorem B22081409 : Blo 1148636 22081409 := bstep (se 2 (by rfl) ⟨8280528, by rfl⟩ : syracuseStep 22081409 = 16561057) B16561057
theorem B3272687 : Blo 1148636 3272687 := bstep (se 1 (by rfl) ⟨2454515, by rfl⟩ : syracuseStep 3272687 = 4909031) B4909031
theorem B2584871 : Blo 1148636 2584871 := bstep (se 1 (by rfl) ⟨1938653, by rfl⟩ : syracuseStep 2584871 = 3877307) B3877307
theorem B11071997 : Blo 1148636 11071997 := bstep (se 3 (by rfl) ⟨2075999, by rfl⟩ : syracuseStep 11071997 = 4151999) B4151999
theorem B2585375 : Blo 1148636 2585375 := bstep (se 1 (by rfl) ⟨1939031, by rfl⟩ : syracuseStep 2585375 = 3878063) B3878063
theorem B3273529 : Blo 1148636 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B6222683 : Blo 1148636 6222683 := bstep (se 1 (by rfl) ⟨4667012, by rfl⟩ : syracuseStep 6222683 = 9334025) B9334025
theorem B8844203 : Blo 1148636 8844203 := bstep (se 1 (by rfl) ⟨6633152, by rfl⟩ : syracuseStep 8844203 = 13266305) B13266305
theorem B2585627 : Blo 1148636 2585627 := bstep (se 1 (by rfl) ⟨1939220, by rfl⟩ : syracuseStep 2585627 = 3878441) B3878441
theorem B6550955 : Blo 1148636 6550955 := bstep (se 1 (by rfl) ⟨4913216, by rfl⟩ : syracuseStep 6550955 = 9826433) B9826433
theorem B5830217 : Blo 1148636 5830217 := bstep (se 2 (by rfl) ⟨2186331, by rfl⟩ : syracuseStep 5830217 = 4372663) B4372663
theorem B2914015 : Blo 1148636 2914015 := bstep (se 1 (by rfl) ⟨2185511, by rfl⟩ : syracuseStep 2914015 = 4371023) B4371023
theorem B12449771 : Blo 1148636 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B1636463 : Blo 1148636 1636463 := bstep (se 1 (by rfl) ⟨1227347, by rfl⟩ : syracuseStep 1636463 = 2454695) B2454695
theorem B10254707 : Blo 1148636 10254707 := bstep (se 1 (by rfl) ⟨7691030, by rfl⟩ : syracuseStep 10254707 = 15382061) B15382061
theorem B5831675 : Blo 1148636 5831675 := bstep (se 1 (by rfl) ⟨4373756, by rfl⟩ : syracuseStep 5831675 = 8747513) B8747513
theorem B2588129 : Blo 1148636 2588129 := bstep (se 2 (by rfl) ⟨970548, by rfl⟩ : syracuseStep 2588129 = 1941097) B1941097
theorem B2588435 : Blo 1148636 2588435 := bstep (se 1 (by rfl) ⟨1941326, by rfl⟩ : syracuseStep 2588435 = 3882653) B3882653
theorem B2588651 : Blo 1148636 2588651 := bstep (se 1 (by rfl) ⟨1941488, by rfl⟩ : syracuseStep 2588651 = 3882977) B3882977
theorem B2588795 : Blo 1148636 2588795 := bstep (se 1 (by rfl) ⟨1941596, by rfl⟩ : syracuseStep 2588795 = 3883193) B3883193
theorem B5833133 : Blo 1148636 5833133 := bstep (se 3 (by rfl) ⟨1093712, by rfl⟩ : syracuseStep 5833133 = 2187425) B2187425
theorem B2589695 : Blo 1148636 2589695 := bstep (se 1 (by rfl) ⟨1942271, by rfl⟩ : syracuseStep 2589695 = 3884543) B3884543
theorem B3736687 : Blo 1148636 3736687 := bstep (se 1 (by rfl) ⟨2802515, by rfl⟩ : syracuseStep 3736687 = 5605031) B5605031
theorem B1967431 : Blo 1148636 1967431 := bstep (se 1 (by rfl) ⟨1475573, by rfl⟩ : syracuseStep 1967431 = 2951147) B2951147
theorem B2623079 : Blo 1148636 2623079 := bstep (se 1 (by rfl) ⟨1967309, by rfl⟩ : syracuseStep 2623079 = 3934619) B3934619
theorem B2590811 : Blo 1148636 2590811 := bstep (se 1 (by rfl) ⟨1943108, by rfl⟩ : syracuseStep 2590811 = 3886217) B3886217
theorem B2590847 : Blo 1148636 2590847 := bstep (se 1 (by rfl) ⟨1943135, by rfl⟩ : syracuseStep 2590847 = 3886271) B3886271
theorem B5900731 : Blo 1148636 5900731 := bstep (se 1 (by rfl) ⟨4425548, by rfl⟩ : syracuseStep 5900731 = 8851097) B8851097
theorem B6228517 : Blo 1148636 6228517 := bstep (se 4 (by rfl) ⟨583923, by rfl⟩ : syracuseStep 6228517 = 1167847) B1167847
theorem B2591387 : Blo 1148636 2591387 := bstep (se 1 (by rfl) ⟨1943540, by rfl⟩ : syracuseStep 2591387 = 3887081) B3887081
theorem B2591423 : Blo 1148636 2591423 := bstep (se 1 (by rfl) ⟨1943567, by rfl⟩ : syracuseStep 2591423 = 3887135) B3887135
theorem B1149671 : Blo 1148636 1149671 := bstep (se 1 (by rfl) ⟨862253, by rfl⟩ : syracuseStep 1149671 = 1724507) B1724507
theorem B2591495 : Blo 1148636 2591495 := bstep (se 1 (by rfl) ⟨1943621, by rfl⟩ : syracuseStep 2591495 = 3887243) B3887243
theorem B1149767 : Blo 1148636 1149767 := bstep (se 1 (by rfl) ⟨862325, by rfl⟩ : syracuseStep 1149767 = 1724651) B1724651
theorem B40406215 : Blo 1148636 40406215 := bstep (se 1 (by rfl) ⟨30304661, by rfl⟩ : syracuseStep 40406215 = 60609323) B60609323
theorem B49679891 : Blo 1148636 49679891 := bstep (se 1 (by rfl) ⟨37259918, by rfl⟩ : syracuseStep 49679891 = 74519837) B74519837
theorem B2461367 : Blo 1148636 2461367 := bstep (se 1 (by rfl) ⟨1846025, by rfl⟩ : syracuseStep 2461367 = 3692051) B3692051
theorem B1150703 : Blo 1148636 1150703 := bstep (se 1 (by rfl) ⟨863027, by rfl⟩ : syracuseStep 1150703 = 1726055) B1726055
theorem B2592539 : Blo 1148636 2592539 := bstep (se 1 (by rfl) ⟨1944404, by rfl⟩ : syracuseStep 2592539 = 3888809) B3888809
theorem B44208017 : Blo 1148636 44208017 := bstep (se 2 (by rfl) ⟨16578006, by rfl⟩ : syracuseStep 44208017 = 33156013) B33156013
theorem B1151259 : Blo 1148636 1151259 := bstep (se 1 (by rfl) ⟨863444, by rfl⟩ : syracuseStep 1151259 = 1726889) B1726889
theorem B1148621147 : Blo 1148636 1148621147 := bstep (se 1 (by rfl) ⟨861465860, by rfl⟩ : syracuseStep 1148621147 = 1722931721) B1722931721
theorem B1151615 : Blo 1148636 1151615 := bstep (se 1 (by rfl) ⟨863711, by rfl⟩ : syracuseStep 1151615 = 1727423) B1727423
theorem B1151695 : Blo 1148636 1151695 := bstep (se 1 (by rfl) ⟨863771, by rfl⟩ : syracuseStep 1151695 = 1727543) B1727543
theorem B14947037 : Blo 1148636 14947037 := bstep (se 3 (by rfl) ⟨2802569, by rfl⟩ : syracuseStep 14947037 = 5605139) B5605139
theorem B4920203 : Blo 1148636 4920203 := bstep (se 1 (by rfl) ⟨3690152, by rfl⟩ : syracuseStep 4920203 = 7380305) B7380305
theorem B1152027 : Blo 1148636 1152027 := bstep (se 1 (by rfl) ⟨864020, by rfl⟩ : syracuseStep 1152027 = 1728041) B1728041
theorem B4658401 : Blo 1148636 4658401 := bstep (se 2 (by rfl) ⟨1746900, by rfl⟩ : syracuseStep 4658401 = 3493801) B3493801
theorem B1261409557 : Blo 1148636 1261409557 := bstep (se 6 (by rfl) ⟨29564286, by rfl⟩ : syracuseStep 1261409557 = 59128573) B59128573
theorem B4363901 : Blo 1148636 4363901 := bstep (se 3 (by rfl) ⟨818231, by rfl⟩ : syracuseStep 4363901 = 1636463) B1636463
theorem B4921195 : Blo 1148636 4921195 := bstep (se 1 (by rfl) ⟨3690896, by rfl⟩ : syracuseStep 4921195 = 7381793) B7381793
theorem B1939639 : Blo 1148636 1939639 := bstep (se 1 (by rfl) ⟨1454729, by rfl⟩ : syracuseStep 1939639 = 2909459) B2909459
theorem B4364705 : Blo 1148636 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B1940719 : Blo 1148636 1940719 := bstep (se 1 (by rfl) ⟨1455539, by rfl⟩ : syracuseStep 1940719 = 2911079) B2911079
theorem B4365647 : Blo 1148636 4365647 := bstep (se 1 (by rfl) ⟨3274235, by rfl⟩ : syracuseStep 4365647 = 6548471) B6548471
theorem B1941151 : Blo 1148636 1941151 := bstep (se 1 (by rfl) ⟨1455863, by rfl⟩ : syracuseStep 1941151 = 2911727) B2911727
theorem B4366163 : Blo 1148636 4366163 := bstep (se 1 (by rfl) ⟨3274622, by rfl⟩ : syracuseStep 4366163 = 6549245) B6549245
theorem B14720939 : Blo 1148636 14720939 := bstep (se 1 (by rfl) ⟨11040704, by rfl⟩ : syracuseStep 14720939 = 22081409) B22081409
theorem B7381331 : Blo 1148636 7381331 := bstep (se 1 (by rfl) ⟨5535998, by rfl⟩ : syracuseStep 7381331 = 11071997) B11071997
theorem B2073001 : Blo 1148636 2073001 := bstep (se 2 (by rfl) ⟨777375, by rfl⟩ : syracuseStep 2073001 = 1554751) B1554751
theorem B4367303 : Blo 1148636 4367303 := bstep (se 1 (by rfl) ⟨3275477, by rfl⟩ : syracuseStep 4367303 = 6550955) B6550955
theorem B8299847 : Blo 1148636 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B17967185 : Blo 1148636 17967185 := bstep (se 2 (by rfl) ⟨6737694, by rfl⟩ : syracuseStep 17967185 = 13475389) B13475389
theorem B1943689 : Blo 1148636 1943689 := bstep (se 2 (by rfl) ⟨728883, by rfl⟩ : syracuseStep 1943689 = 1457767) B1457767
theorem B1944283 : Blo 1148636 1944283 := bstep (se 1 (by rfl) ⟨1458212, by rfl⟩ : syracuseStep 1944283 = 2916425) B2916425
theorem B3877631 : Blo 1148636 3877631 := bstep (se 1 (by rfl) ⟨2908223, by rfl⟩ : syracuseStep 3877631 = 5816447) B5816447
theorem B7187297 : Blo 1148636 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B1945039 : Blo 1148636 1945039 := bstep (se 1 (by rfl) ⟨1458779, by rfl⟩ : syracuseStep 1945039 = 2917559) B2917559
theorem B5254727 : Blo 1148636 5254727 := bstep (se 1 (by rfl) ⟨3941045, by rfl⟩ : syracuseStep 5254727 = 7882091) B7882091
theorem B3879359 : Blo 1148636 3879359 := bstep (se 1 (by rfl) ⟨2909519, by rfl⟩ : syracuseStep 3879359 = 5819039) B5819039
theorem B3879791 : Blo 1148636 3879791 := bstep (se 1 (by rfl) ⟨2909843, by rfl⟩ : syracuseStep 3879791 = 5819687) B5819687
theorem B3881519 : Blo 1148636 3881519 := bstep (se 1 (by rfl) ⟨2911139, by rfl⟩ : syracuseStep 3881519 = 5822279) B5822279
theorem B8731475 : Blo 1148636 8731475 := bstep (se 1 (by rfl) ⟨6548606, by rfl⟩ : syracuseStep 8731475 = 13097213) B13097213
theorem B3881951 : Blo 1148636 3881951 := bstep (se 1 (by rfl) ⟨2911463, by rfl⟩ : syracuseStep 3881951 = 5822927) B5822927
theorem B3882761 : Blo 1148636 3882761 := bstep (se 2 (by rfl) ⟨1456035, by rfl⟩ : syracuseStep 3882761 = 2912071) B2912071
theorem B3882815 : Blo 1148636 3882815 := bstep (se 1 (by rfl) ⟨2912111, by rfl⟩ : syracuseStep 3882815 = 5824223) B5824223
theorem B1458415 : Blo 1148636 1458415 := bstep (se 1 (by rfl) ⟨1093811, by rfl⟩ : syracuseStep 1458415 = 2187623) B2187623
theorem B10502419 : Blo 1148636 10502419 := bstep (se 1 (by rfl) ⟨7876814, by rfl⟩ : syracuseStep 10502419 = 15753629) B15753629
theorem B21250799 : Blo 1148636 21250799 := bstep (se 1 (by rfl) ⟨15938099, by rfl⟩ : syracuseStep 21250799 = 31876199) B31876199
theorem B4375367 : Blo 1148636 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B53855111 : Blo 1148636 53855111 := bstep (se 1 (by rfl) ⟨40391333, by rfl⟩ : syracuseStep 53855111 = 80782667) B80782667
theorem B3884219 : Blo 1148636 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B4671067 : Blo 1148636 4671067 := bstep (se 1 (by rfl) ⟨3503300, by rfl⟩ : syracuseStep 4671067 = 7006601) B7006601
theorem B1296103 : Blo 1148636 1296103 := bstep (se 1 (by rfl) ⟨972077, by rfl⟩ : syracuseStep 1296103 = 1944155) B1944155
theorem B3885083 : Blo 1148636 3885083 := bstep (se 1 (by rfl) ⟨2913812, by rfl⟩ : syracuseStep 3885083 = 5827625) B5827625
theorem B3885245 : Blo 1148636 3885245 := bstep (se 3 (by rfl) ⟨728483, by rfl⟩ : syracuseStep 3885245 = 1456967) B1456967
theorem B3885353 : Blo 1148636 3885353 := bstep (se 2 (by rfl) ⟨1457007, by rfl⟩ : syracuseStep 3885353 = 2914015) B2914015
theorem B2181791 : Blo 1148636 2181791 := bstep (se 1 (by rfl) ⟨1636343, by rfl⟩ : syracuseStep 2181791 = 3272687) B3272687
theorem B1723247 : Blo 1148636 1723247 := bstep (se 1 (by rfl) ⟨1292435, by rfl⟩ : syracuseStep 1723247 = 2584871) B2584871
theorem B1723529 : Blo 1148636 1723529 := bstep (se 2 (by rfl) ⟨646323, by rfl⟩ : syracuseStep 1723529 = 1292647) B1292647
theorem B1723583 : Blo 1148636 1723583 := bstep (se 1 (by rfl) ⟨1292687, by rfl⟩ : syracuseStep 1723583 = 2585375) B2585375
theorem B4148455 : Blo 1148636 4148455 := bstep (se 1 (by rfl) ⟨3111341, by rfl⟩ : syracuseStep 4148455 = 6222683) B6222683
theorem B1723751 : Blo 1148636 1723751 := bstep (se 1 (by rfl) ⟨1292813, by rfl⟩ : syracuseStep 1723751 = 2585627) B2585627
theorem B49761701 : Blo 1148636 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B3886811 : Blo 1148636 3886811 := bstep (se 1 (by rfl) ⟨2915108, by rfl⟩ : syracuseStep 3886811 = 5830217) B5830217
theorem B1724585 : Blo 1148636 1724585 := bstep (se 2 (by rfl) ⟨646719, by rfl⟩ : syracuseStep 1724585 = 1293439) B1293439
theorem B5820659 : Blo 1148636 5820659 := bstep (se 1 (by rfl) ⟨4365494, by rfl⟩ : syracuseStep 5820659 = 8730989) B8730989
theorem B6836471 : Blo 1148636 6836471 := bstep (se 1 (by rfl) ⟨5127353, by rfl⟩ : syracuseStep 6836471 = 10254707) B10254707
theorem B3887783 : Blo 1148636 3887783 := bstep (se 1 (by rfl) ⟨2915837, by rfl⟩ : syracuseStep 3887783 = 5831675) B5831675
theorem B1725419 : Blo 1148636 1725419 := bstep (se 1 (by rfl) ⟨1294064, by rfl⟩ : syracuseStep 1725419 = 2588129) B2588129
theorem B1725623 : Blo 1148636 1725623 := bstep (se 1 (by rfl) ⟨1294217, by rfl⟩ : syracuseStep 1725623 = 2588435) B2588435
theorem B1725767 : Blo 1148636 1725767 := bstep (se 1 (by rfl) ⟨1294325, by rfl⟩ : syracuseStep 1725767 = 2588651) B2588651
theorem B2184745 : Blo 1148636 2184745 := bstep (se 2 (by rfl) ⟨819279, by rfl⟩ : syracuseStep 2184745 = 1638559) B1638559
theorem B8279777 : Blo 1148636 8279777 := bstep (se 2 (by rfl) ⟨3104916, by rfl⟩ : syracuseStep 8279777 = 6209833) B6209833
theorem B3889511 : Blo 1148636 3889511 := bstep (se 1 (by rfl) ⟨2917133, by rfl⟩ : syracuseStep 3889511 = 5834267) B5834267
theorem B2185679 : Blo 1148636 2185679 := bstep (se 1 (by rfl) ⟨1639259, by rfl⟩ : syracuseStep 2185679 = 3278519) B3278519
theorem B1727195 : Blo 1148636 1727195 := bstep (se 1 (by rfl) ⟨1295396, by rfl⟩ : syracuseStep 1727195 = 2590793) B2590793
theorem B7363493 : Blo 1148636 7363493 := bstep (se 4 (by rfl) ⟨690327, by rfl⟩ : syracuseStep 7363493 = 1380655) B1380655
theorem B6544415 : Blo 1148636 6544415 := bstep (se 1 (by rfl) ⟨4908311, by rfl⟩ : syracuseStep 6544415 = 9816623) B9816623
theorem B2186347 : Blo 1148636 2186347 := bstep (se 1 (by rfl) ⟨1639760, by rfl⟩ : syracuseStep 2186347 = 3279521) B3279521
theorem B1727657 : Blo 1148636 1727657 := bstep (se 2 (by rfl) ⟨647871, by rfl⟩ : syracuseStep 1727657 = 1295743) B1295743
theorem B7003367 : Blo 1148636 7003367 := bstep (se 1 (by rfl) ⟨5252525, by rfl⟩ : syracuseStep 7003367 = 10505051) B10505051
theorem B1728347 : Blo 1148636 1728347 := bstep (se 1 (by rfl) ⟨1296260, by rfl⟩ : syracuseStep 1728347 = 2592521) B2592521
theorem B1728383 : Blo 1148636 1728383 := bstep (se 1 (by rfl) ⟨1296287, by rfl⟩ : syracuseStep 1728383 = 2592575) B2592575
theorem B7364519 : Blo 1148636 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B1728455 : Blo 1148636 1728455 := bstep (se 1 (by rfl) ⟨1296341, by rfl⟩ : syracuseStep 1728455 = 2592683) B2592683
theorem B1728839 : Blo 1148636 1728839 := bstep (se 1 (by rfl) ⟨1296629, by rfl⟩ : syracuseStep 1728839 = 2593259) B2593259
theorem B11790299 : Blo 1148636 11790299 := bstep (se 1 (by rfl) ⟨8842724, by rfl⟩ : syracuseStep 11790299 = 17685449) B17685449
theorem B14969063 : Blo 1148636 14969063 := bstep (se 1 (by rfl) ⟨11226797, by rfl⟩ : syracuseStep 14969063 = 22453595) B22453595
theorem B2910887 : Blo 1148636 2910887 := bstep (se 1 (by rfl) ⟨2183165, by rfl⟩ : syracuseStep 2910887 = 4366331) B4366331
theorem B2911099 : Blo 1148636 2911099 := bstep (se 1 (by rfl) ⟨2183324, by rfl⟩ : syracuseStep 2911099 = 4366649) B4366649
theorem B12610469 : Blo 1148636 12610469 := bstep (se 4 (by rfl) ⟨1182231, by rfl⟩ : syracuseStep 12610469 = 2364463) B2364463
theorem B33647663 : Blo 1148636 33647663 := bstep (se 1 (by rfl) ⟨25235747, by rfl⟩ : syracuseStep 33647663 = 50471495) B50471495
theorem B2584889 : Blo 1148636 2584889 := bstep (se 2 (by rfl) ⟨969333, by rfl⟩ : syracuseStep 2584889 = 1938667) B1938667
theorem B2585897 : Blo 1148636 2585897 := bstep (se 2 (by rfl) ⟨969711, by rfl⟩ : syracuseStep 2585897 = 1939423) B1939423
theorem B5896135 : Blo 1148636 5896135 := bstep (se 1 (by rfl) ⟨4422101, by rfl⟩ : syracuseStep 5896135 = 8844203) B8844203
theorem B2587067 : Blo 1148636 2587067 := bstep (se 1 (by rfl) ⟨1940300, by rfl⟩ : syracuseStep 2587067 = 3880601) B3880601
theorem B2915099 : Blo 1148636 2915099 := bstep (se 1 (by rfl) ⟨2186324, by rfl⟩ : syracuseStep 2915099 = 4372649) B4372649
theorem B2587823 : Blo 1148636 2587823 := bstep (se 1 (by rfl) ⟨1940867, by rfl⟩ : syracuseStep 2587823 = 3881735) B3881735
theorem B2916911 : Blo 1148636 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B2589479 : Blo 1148636 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B2590055 : Blo 1148636 2590055 := bstep (se 1 (by rfl) ⟨1942541, by rfl⟩ : syracuseStep 2590055 = 3885083) B3885083
theorem B2590163 : Blo 1148636 2590163 := bstep (se 1 (by rfl) ⟨1942622, by rfl⟩ : syracuseStep 2590163 = 3885245) B3885245
theorem B4982249 : Blo 1148636 4982249 := bstep (se 2 (by rfl) ⟨1868343, by rfl⟩ : syracuseStep 4982249 = 3736687) B3736687
theorem B2590235 : Blo 1148636 2590235 := bstep (se 1 (by rfl) ⟨1942676, by rfl⟩ : syracuseStep 2590235 = 3885353) B3885353
theorem B2623241 : Blo 1148636 2623241 := bstep (se 2 (by rfl) ⟨983715, by rfl⟩ : syracuseStep 2623241 = 1967431) B1967431
theorem B1148831 : Blo 1148636 1148831 := bstep (se 1 (by rfl) ⟨861623, by rfl⟩ : syracuseStep 1148831 = 1723247) B1723247
theorem B1149019 : Blo 1148636 1149019 := bstep (se 1 (by rfl) ⟨861764, by rfl⟩ : syracuseStep 1149019 = 1723529) B1723529
theorem B6228089 : Blo 1148636 6228089 := bstep (se 2 (by rfl) ⟨2335533, by rfl⟩ : syracuseStep 6228089 = 4671067) B4671067
theorem B1149055 : Blo 1148636 1149055 := bstep (se 1 (by rfl) ⟨861791, by rfl⟩ : syracuseStep 1149055 = 1723583) B1723583
theorem B1149167 : Blo 1148636 1149167 := bstep (se 1 (by rfl) ⟨861875, by rfl⟩ : syracuseStep 1149167 = 1723751) B1723751
theorem B1640911 : Blo 1148636 1640911 := bstep (se 1 (by rfl) ⟨1230683, by rfl⟩ : syracuseStep 1640911 = 2461367) B2461367
theorem B2591207 : Blo 1148636 2591207 := bstep (se 1 (by rfl) ⟨1943405, by rfl⟩ : syracuseStep 2591207 = 3886811) B3886811
theorem B1149723 : Blo 1148636 1149723 := bstep (se 1 (by rfl) ⟨862292, by rfl⟩ : syracuseStep 1149723 = 1724585) B1724585
theorem B4557647 : Blo 1148636 4557647 := bstep (se 1 (by rfl) ⟨3418235, by rfl⟩ : syracuseStep 4557647 = 6836471) B6836471
theorem B2591585 : Blo 1148636 2591585 := bstep (se 2 (by rfl) ⟨971844, by rfl⟩ : syracuseStep 2591585 = 1943689) B1943689
theorem B2591855 : Blo 1148636 2591855 := bstep (se 1 (by rfl) ⟨1943891, by rfl⟩ : syracuseStep 2591855 = 3887783) B3887783
theorem B9964691 : Blo 1148636 9964691 := bstep (se 1 (by rfl) ⟨7473518, by rfl⟩ : syracuseStep 9964691 = 14947037) B14947037
theorem B1150279 : Blo 1148636 1150279 := bstep (se 1 (by rfl) ⟨862709, by rfl⟩ : syracuseStep 1150279 = 1725419) B1725419
theorem B1150415 : Blo 1148636 1150415 := bstep (se 1 (by rfl) ⟨862811, by rfl⟩ : syracuseStep 1150415 = 1725623) B1725623
theorem B1150511 : Blo 1148636 1150511 := bstep (se 1 (by rfl) ⟨862883, by rfl⟩ : syracuseStep 1150511 = 1725767) B1725767
theorem B2592377 : Blo 1148636 2592377 := bstep (se 2 (by rfl) ⟨972141, by rfl⟩ : syracuseStep 2592377 = 1944283) B1944283
theorem B2593007 : Blo 1148636 2593007 := bstep (se 1 (by rfl) ⟨1944755, by rfl⟩ : syracuseStep 2593007 = 3889511) B3889511
theorem B53874953 : Blo 1148636 53874953 := bstep (se 2 (by rfl) ⟨20203107, by rfl⟩ : syracuseStep 53874953 = 40406215) B40406215
theorem B1151463 : Blo 1148636 1151463 := bstep (se 1 (by rfl) ⟨863597, by rfl⟩ : syracuseStep 1151463 = 1727195) B1727195
theorem B2593385 : Blo 1148636 2593385 := bstep (se 2 (by rfl) ⟨972519, by rfl⟩ : syracuseStep 2593385 = 1945039) B1945039
theorem B4362943 : Blo 1148636 4362943 := bstep (se 1 (by rfl) ⟨3272207, by rfl⟩ : syracuseStep 4362943 = 6544415) B6544415
theorem B1151771 : Blo 1148636 1151771 := bstep (se 1 (by rfl) ⟨863828, by rfl⟩ : syracuseStep 1151771 = 1727657) B1727657
theorem B1152231 : Blo 1148636 1152231 := bstep (se 1 (by rfl) ⟨864173, by rfl⟩ : syracuseStep 1152231 = 1728347) B1728347
theorem B1152255 : Blo 1148636 1152255 := bstep (se 1 (by rfl) ⟨864191, by rfl⟩ : syracuseStep 1152255 = 1728383) B1728383
theorem B1152303 : Blo 1148636 1152303 := bstep (se 1 (by rfl) ⟨864227, by rfl⟩ : syracuseStep 1152303 = 1728455) B1728455
theorem B1152559 : Blo 1148636 1152559 := bstep (se 1 (by rfl) ⟨864419, by rfl⟩ : syracuseStep 1152559 = 1728839) B1728839
theorem B4920887 : Blo 1148636 4920887 := bstep (se 1 (by rfl) ⟨3690665, by rfl⟩ : syracuseStep 4920887 = 7381331) B7381331
theorem B39917501 : Blo 1148636 39917501 := bstep (se 3 (by rfl) ⟨7484531, by rfl⟩ : syracuseStep 39917501 = 14969063) B14969063
theorem B1940591 : Blo 1148636 1940591 := bstep (se 1 (by rfl) ⟨1455443, by rfl⟩ : syracuseStep 1940591 = 2910887) B2910887
theorem B6561593 : Blo 1148636 6561593 := bstep (se 2 (by rfl) ⟨2460597, by rfl⟩ : syracuseStep 6561593 = 4921195) B4921195
theorem B1943399 : Blo 1148636 1943399 := bstep (se 1 (by rfl) ⟨1457549, by rfl⟩ : syracuseStep 1943399 = 2915099) B2915099
theorem B1944553 : Blo 1148636 1944553 := bstep (se 2 (by rfl) ⟨729207, by rfl⟩ : syracuseStep 1944553 = 1458415) B1458415
theorem B14003225 : Blo 1148636 14003225 := bstep (se 2 (by rfl) ⟨5251209, by rfl⟩ : syracuseStep 14003225 = 10502419) B10502419
theorem B14167199 : Blo 1148636 14167199 := bstep (se 1 (by rfl) ⟨10625399, by rfl⟩ : syracuseStep 14167199 = 21250799) B21250799
theorem B2764001 : Blo 1148636 2764001 := bstep (se 2 (by rfl) ⟨1036500, by rfl⟩ : syracuseStep 2764001 = 2073001) B2073001
theorem B1748719 : Blo 1148636 1748719 := bstep (se 1 (by rfl) ⟨1311539, by rfl⟩ : syracuseStep 1748719 = 2623079) B2623079
theorem B1454527 : Blo 1148636 1454527 := bstep (se 1 (by rfl) ⟨1090895, by rfl⟩ : syracuseStep 1454527 = 2181791) B2181791
theorem B33174467 : Blo 1148636 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B31470565 : Blo 1148636 31470565 := bstep (se 4 (by rfl) ⟨2950365, by rfl⟩ : syracuseStep 31470565 = 5900731) B5900731
theorem B13120541 : Blo 1148636 13120541 := bstep (se 3 (by rfl) ⟨2460101, by rfl⟩ : syracuseStep 13120541 = 4920203) B4920203
theorem B29472011 : Blo 1148636 29472011 := bstep (se 1 (by rfl) ⟨22104008, by rfl⟩ : syracuseStep 29472011 = 44208017) B44208017
theorem B3880439 : Blo 1148636 3880439 := bstep (se 1 (by rfl) ⟨2910329, by rfl⟩ : syracuseStep 3880439 = 5820659) B5820659
theorem B8304689 : Blo 1148636 8304689 := bstep (se 2 (by rfl) ⟨3114258, by rfl⟩ : syracuseStep 8304689 = 6228517) B6228517
theorem B3881465 : Blo 1148636 3881465 := bstep (se 2 (by rfl) ⟨1455549, by rfl⟩ : syracuseStep 3881465 = 2911099) B2911099
theorem B1457119 : Blo 1148636 1457119 := bstep (se 1 (by rfl) ⟨1092839, by rfl⟩ : syracuseStep 1457119 = 2185679) B2185679
theorem B4668911 : Blo 1148636 4668911 := bstep (se 1 (by rfl) ⟨3501683, by rfl⟩ : syracuseStep 4668911 = 7003367) B7003367
theorem B9813959 : Blo 1148636 9813959 := bstep (se 1 (by rfl) ⟨7360469, by rfl⟩ : syracuseStep 9813959 = 14720939) B14720939
theorem B11978123 : Blo 1148636 11978123 := bstep (se 1 (by rfl) ⟨8983592, by rfl⟩ : syracuseStep 11978123 = 17967185) B17967185
theorem B6211201 : Blo 1148636 6211201 := bstep (se 2 (by rfl) ⟨2329200, by rfl⟩ : syracuseStep 6211201 = 4658401) B4658401
theorem B8406979 : Blo 1148636 8406979 := bstep (se 1 (by rfl) ⟨6305234, by rfl⟩ : syracuseStep 8406979 = 12610469) B12610469
theorem B22431775 : Blo 1148636 22431775 := bstep (se 1 (by rfl) ⟨16823831, by rfl⟩ : syracuseStep 22431775 = 33647663) B33647663
theorem B1723259 : Blo 1148636 1723259 := bstep (se 1 (by rfl) ⟨1292444, by rfl⟩ : syracuseStep 1723259 = 2584889) B2584889
theorem B1723931 : Blo 1148636 1723931 := bstep (se 1 (by rfl) ⟨1292948, by rfl⟩ : syracuseStep 1723931 = 2585897) B2585897
theorem B76664501 : Blo 1148636 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B14012605 : Blo 1148636 14012605 := bstep (se 3 (by rfl) ⟨2627363, by rfl⟩ : syracuseStep 14012605 = 5254727) B5254727
theorem B1724711 : Blo 1148636 1724711 := bstep (se 1 (by rfl) ⟨1293533, by rfl⟩ : syracuseStep 1724711 = 2587067) B2587067
theorem B5820983 : Blo 1148636 5820983 := bstep (se 1 (by rfl) ⟨4365737, by rfl⟩ : syracuseStep 5820983 = 8731475) B8731475
theorem B1725215 : Blo 1148636 1725215 := bstep (se 1 (by rfl) ⟨1293911, by rfl⟩ : syracuseStep 1725215 = 2587823) B2587823
theorem B31446053 : Blo 1148636 31446053 := bstep (se 4 (by rfl) ⟨2948067, by rfl⟩ : syracuseStep 31446053 = 5896135) B5896135
theorem B1725863 : Blo 1148636 1725863 := bstep (se 1 (by rfl) ⟨1294397, by rfl⟩ : syracuseStep 1725863 = 2588795) B2588795
theorem B3888755 : Blo 1148636 3888755 := bstep (se 1 (by rfl) ⟨2916566, by rfl⟩ : syracuseStep 3888755 = 5833133) B5833133
theorem B35903407 : Blo 1148636 35903407 := bstep (se 1 (by rfl) ⟨26927555, by rfl⟩ : syracuseStep 35903407 = 53855111) B53855111
theorem B1726463 : Blo 1148636 1726463 := bstep (se 1 (by rfl) ⟨1294847, by rfl⟩ : syracuseStep 1726463 = 2589695) B2589695
theorem B1727207 : Blo 1148636 1727207 := bstep (se 1 (by rfl) ⟨1295405, by rfl⟩ : syracuseStep 1727207 = 2590811) B2590811
theorem B1727231 : Blo 1148636 1727231 := bstep (se 1 (by rfl) ⟨1295423, by rfl⟩ : syracuseStep 1727231 = 2590847) B2590847
theorem B1727591 : Blo 1148636 1727591 := bstep (se 1 (by rfl) ⟨1295693, by rfl⟩ : syracuseStep 1727591 = 2591387) B2591387
theorem B1727615 : Blo 1148636 1727615 := bstep (se 1 (by rfl) ⟨1295711, by rfl⟩ : syracuseStep 1727615 = 2591423) B2591423
theorem B1727663 : Blo 1148636 1727663 := bstep (se 1 (by rfl) ⟨1295747, by rfl⟩ : syracuseStep 1727663 = 2591495) B2591495
theorem B1728137 : Blo 1148636 1728137 := bstep (se 2 (by rfl) ⟨648051, by rfl⟩ : syracuseStep 1728137 = 1296103) B1296103
theorem B33119927 : Blo 1148636 33119927 := bstep (se 1 (by rfl) ⟨24839945, by rfl⟩ : syracuseStep 33119927 = 49679891) B49679891
theorem B1728359 : Blo 1148636 1728359 := bstep (se 1 (by rfl) ⟨1296269, by rfl⟩ : syracuseStep 1728359 = 2592539) B2592539
theorem B765747431 : Blo 1148636 765747431 := bstep (se 1 (by rfl) ⟨574310573, by rfl⟩ : syracuseStep 765747431 = 1148621147) B1148621147
theorem B2909267 : Blo 1148636 2909267 := bstep (se 1 (by rfl) ⟨2181950, by rfl⟩ : syracuseStep 2909267 = 4363901) B4363901
theorem B2909803 : Blo 1148636 2909803 := bstep (se 1 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 2909803 = 4364705) B4364705
theorem B5531273 : Blo 1148636 5531273 := bstep (se 2 (by rfl) ⟨2074227, by rfl⟩ : syracuseStep 5531273 = 4148455) B4148455
theorem B22079405 : Blo 1148636 22079405 := bstep (se 3 (by rfl) ⟨4139888, by rfl⟩ : syracuseStep 22079405 = 8279777) B8279777
theorem B4908995 : Blo 1148636 4908995 := bstep (se 1 (by rfl) ⟨3681746, by rfl⟩ : syracuseStep 4908995 = 7363493) B7363493
theorem B2910431 : Blo 1148636 2910431 := bstep (se 1 (by rfl) ⟨2182823, by rfl⟩ : syracuseStep 2910431 = 4365647) B4365647
theorem B2910775 : Blo 1148636 2910775 := bstep (se 1 (by rfl) ⟨2183081, by rfl⟩ : syracuseStep 2910775 = 4366163) B4366163
theorem B4909679 : Blo 1148636 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B2911535 : Blo 1148636 2911535 := bstep (se 1 (by rfl) ⟨2183651, by rfl⟩ : syracuseStep 2911535 = 4367303) B4367303
theorem B5533231 : Blo 1148636 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B7860199 : Blo 1148636 7860199 := bstep (se 1 (by rfl) ⟨5895149, by rfl⟩ : syracuseStep 7860199 = 11790299) B11790299
theorem B1681879409 : Blo 1148636 1681879409 := bstep (se 2 (by rfl) ⟨630704778, by rfl⟩ : syracuseStep 1681879409 = 1261409557) B1261409557
theorem B2585087 : Blo 1148636 2585087 := bstep (se 1 (by rfl) ⟨1938815, by rfl⟩ : syracuseStep 2585087 = 3877631) B3877631
theorem B2912993 : Blo 1148636 2912993 := bstep (se 2 (by rfl) ⟨1092372, by rfl⟩ : syracuseStep 2912993 = 2184745) B2184745
theorem B2586185 : Blo 1148636 2586185 := bstep (se 2 (by rfl) ⟨969819, by rfl⟩ : syracuseStep 2586185 = 1939639) B1939639
theorem B2586239 : Blo 1148636 2586239 := bstep (se 1 (by rfl) ⟨1939679, by rfl⟩ : syracuseStep 2586239 = 3879359) B3879359
theorem B2586527 : Blo 1148636 2586527 := bstep (se 1 (by rfl) ⟨1939895, by rfl⟩ : syracuseStep 2586527 = 3879791) B3879791
theorem B2915129 : Blo 1148636 2915129 := bstep (se 2 (by rfl) ⟨1093173, by rfl⟩ : syracuseStep 2915129 = 2186347) B2186347
theorem B2587625 : Blo 1148636 2587625 := bstep (se 2 (by rfl) ⟨970359, by rfl⟩ : syracuseStep 2587625 = 1940719) B1940719
theorem B2587679 : Blo 1148636 2587679 := bstep (se 1 (by rfl) ⟨1940759, by rfl⟩ : syracuseStep 2587679 = 3881519) B3881519
theorem B2587967 : Blo 1148636 2587967 := bstep (se 1 (by rfl) ⟨1940975, by rfl⟩ : syracuseStep 2587967 = 3881951) B3881951
theorem B2588201 : Blo 1148636 2588201 := bstep (se 2 (by rfl) ⟨970575, by rfl⟩ : syracuseStep 2588201 = 1941151) B1941151
theorem B2588507 : Blo 1148636 2588507 := bstep (se 1 (by rfl) ⟨1941380, by rfl⟩ : syracuseStep 2588507 = 3882761) B3882761
theorem B2588543 : Blo 1148636 2588543 := bstep (se 1 (by rfl) ⟨1941407, by rfl⟩ : syracuseStep 2588543 = 3882815) B3882815
theorem B1148839 : Blo 1148636 1148839 := bstep (se 1 (by rfl) ⟨861629, by rfl⟩ : syracuseStep 1148839 = 1723259) B1723259
theorem B1149287 : Blo 1148636 1149287 := bstep (se 1 (by rfl) ⟨861965, by rfl⟩ : syracuseStep 1149287 = 1723931) B1723931
theorem B35916635 : Blo 1148636 35916635 := bstep (se 1 (by rfl) ⟨26937476, by rfl⟩ : syracuseStep 35916635 = 53874953) B53874953
theorem B1149807 : Blo 1148636 1149807 := bstep (se 1 (by rfl) ⟨862355, by rfl⟩ : syracuseStep 1149807 = 1724711) B1724711
theorem B1150143 : Blo 1148636 1150143 := bstep (se 1 (by rfl) ⟨862607, by rfl⟩ : syracuseStep 1150143 = 1725215) B1725215
theorem B1150575 : Blo 1148636 1150575 := bstep (se 1 (by rfl) ⟨862931, by rfl⟩ : syracuseStep 1150575 = 1725863) B1725863
theorem B3280591 : Blo 1148636 3280591 := bstep (se 1 (by rfl) ⟨2460443, by rfl⟩ : syracuseStep 3280591 = 4920887) B4920887
theorem B2592503 : Blo 1148636 2592503 := bstep (se 1 (by rfl) ⟨1944377, by rfl⟩ : syracuseStep 2592503 = 3888755) B3888755
theorem B26611667 : Blo 1148636 26611667 := bstep (se 1 (by rfl) ⟨19958750, by rfl⟩ : syracuseStep 26611667 = 39917501) B39917501
theorem B2592737 : Blo 1148636 2592737 := bstep (se 2 (by rfl) ⟨972276, by rfl⟩ : syracuseStep 2592737 = 1944553) B1944553
theorem B1150975 : Blo 1148636 1150975 := bstep (se 1 (by rfl) ⟨863231, by rfl⟩ : syracuseStep 1150975 = 1726463) B1726463
theorem B127766645 : Blo 1148636 127766645 := bstep (se 5 (by rfl) ⟨5989061, by rfl⟩ : syracuseStep 127766645 = 11978123) B11978123
theorem B1151471 : Blo 1148636 1151471 := bstep (se 1 (by rfl) ⟨863603, by rfl⟩ : syracuseStep 1151471 = 1727207) B1727207
theorem B1151487 : Blo 1148636 1151487 := bstep (se 1 (by rfl) ⟨863615, by rfl⟩ : syracuseStep 1151487 = 1727231) B1727231
theorem B7377641 : Blo 1148636 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B1151727 : Blo 1148636 1151727 := bstep (se 1 (by rfl) ⟨863795, by rfl⟩ : syracuseStep 1151727 = 1727591) B1727591
theorem B1151743 : Blo 1148636 1151743 := bstep (se 1 (by rfl) ⟨863807, by rfl⟩ : syracuseStep 1151743 = 1727615) B1727615
theorem B1151775 : Blo 1148636 1151775 := bstep (se 1 (by rfl) ⟨863831, by rfl⟩ : syracuseStep 1151775 = 1727663) B1727663
theorem B2331625 : Blo 1148636 2331625 := bstep (se 2 (by rfl) ⟨874359, by rfl⟩ : syracuseStep 2331625 = 1748719) B1748719
theorem B1152091 : Blo 1148636 1152091 := bstep (se 1 (by rfl) ⟨864068, by rfl⟩ : syracuseStep 1152091 = 1728137) B1728137
theorem B1152239 : Blo 1148636 1152239 := bstep (se 1 (by rfl) ⟨864179, by rfl⟩ : syracuseStep 1152239 = 1728359) B1728359
theorem B510498287 : Blo 1148636 510498287 := bstep (se 1 (by rfl) ⟨382873715, by rfl⟩ : syracuseStep 510498287 = 765747431) B765747431
theorem B18683473 : Blo 1148636 18683473 := bstep (se 2 (by rfl) ⟨7006302, by rfl⟩ : syracuseStep 18683473 = 14012605) B14012605
theorem B1939369 : Blo 1148636 1939369 := bstep (se 2 (by rfl) ⟨727263, by rfl⟩ : syracuseStep 1939369 = 1454527) B1454527
theorem B1939511 : Blo 1148636 1939511 := bstep (se 1 (by rfl) ⟨1454633, by rfl⟩ : syracuseStep 1939511 = 2909267) B2909267
theorem B14719603 : Blo 1148636 14719603 := bstep (se 1 (by rfl) ⟨11039702, by rfl⟩ : syracuseStep 14719603 = 22079405) B22079405
theorem B1940287 : Blo 1148636 1940287 := bstep (se 1 (by rfl) ⟨1455215, by rfl⟩ : syracuseStep 1940287 = 2910431) B2910431
theorem B9444799 : Blo 1148636 9444799 := bstep (se 1 (by rfl) ⟨7083599, by rfl⟩ : syracuseStep 9444799 = 14167199) B14167199
theorem B1941023 : Blo 1148636 1941023 := bstep (se 1 (by rfl) ⟨1455767, by rfl⟩ : syracuseStep 1941023 = 2911535) B2911535
theorem B1941995 : Blo 1148636 1941995 := bstep (se 1 (by rfl) ⟨1456496, by rfl⟩ : syracuseStep 1941995 = 2912993) B2912993
theorem B1942825 : Blo 1148636 1942825 := bstep (se 2 (by rfl) ⟨728559, by rfl⟩ : syracuseStep 1942825 = 1457119) B1457119
theorem B1943419 : Blo 1148636 1943419 := bstep (se 1 (by rfl) ⟨1457564, by rfl⟩ : syracuseStep 1943419 = 2915129) B2915129
theorem B44837221 : Blo 1148636 44837221 := bstep (se 4 (by rfl) ⟨4203489, by rfl⟩ : syracuseStep 44837221 = 8406979) B8406979
theorem B1944607 : Blo 1148636 1944607 := bstep (se 1 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 1944607 = 2916911) B2916911
theorem B3321499 : Blo 1148636 3321499 := bstep (se 1 (by rfl) ⟨2491124, by rfl⟩ : syracuseStep 3321499 = 4982249) B4982249
theorem B1748827 : Blo 1148636 1748827 := bstep (se 1 (by rfl) ⟨1311620, by rfl⟩ : syracuseStep 1748827 = 2623241) B2623241
theorem B3879737 : Blo 1148636 3879737 := bstep (se 2 (by rfl) ⟨1454901, by rfl⟩ : syracuseStep 3879737 = 2909803) B2909803
theorem B3880655 : Blo 1148636 3880655 := bstep (se 1 (by rfl) ⟨2910491, by rfl⟩ : syracuseStep 3880655 = 5820983) B5820983
theorem B3881033 : Blo 1148636 3881033 := bstep (se 2 (by rfl) ⟨1455387, by rfl⟩ : syracuseStep 3881033 = 2910775) B2910775
theorem B1293727 : Blo 1148636 1293727 := bstep (se 1 (by rfl) ⟨970295, by rfl⟩ : syracuseStep 1293727 = 1940591) B1940591
theorem B4374395 : Blo 1148636 4374395 := bstep (se 1 (by rfl) ⟨3280796, by rfl⟩ : syracuseStep 4374395 = 6561593) B6561593
theorem B5817257 : Blo 1148636 5817257 := bstep (se 2 (by rfl) ⟨2181471, by rfl⟩ : syracuseStep 5817257 = 4362943) B4362943
theorem B3687515 : Blo 1148636 3687515 := bstep (se 1 (by rfl) ⟨2765636, by rfl⟩ : syracuseStep 3687515 = 5531273) B5531273
theorem B1295599 : Blo 1148636 1295599 := bstep (se 1 (by rfl) ⟨971699, by rfl⟩ : syracuseStep 1295599 = 1943399) B1943399
theorem B41960753 : Blo 1148636 41960753 := bstep (se 2 (by rfl) ⟨15735282, by rfl⟩ : syracuseStep 41960753 = 31470565) B31470565
theorem B1723391 : Blo 1148636 1723391 := bstep (se 1 (by rfl) ⟨1292543, by rfl⟩ : syracuseStep 1723391 = 2585087) B2585087
theorem B19648007 : Blo 1148636 19648007 := bstep (se 1 (by rfl) ⟨14736005, by rfl⟩ : syracuseStep 19648007 = 29472011) B29472011
theorem B1724123 : Blo 1148636 1724123 := bstep (se 1 (by rfl) ⟨1293092, by rfl⟩ : syracuseStep 1724123 = 2586185) B2586185
theorem B1724159 : Blo 1148636 1724159 := bstep (se 1 (by rfl) ⟨1293119, by rfl⟩ : syracuseStep 1724159 = 2586239) B2586239
theorem B1724351 : Blo 1148636 1724351 := bstep (se 1 (by rfl) ⟨1293263, by rfl⟩ : syracuseStep 1724351 = 2586527) B2586527
theorem B1725083 : Blo 1148636 1725083 := bstep (se 1 (by rfl) ⟨1293812, by rfl⟩ : syracuseStep 1725083 = 2587625) B2587625
theorem B1725119 : Blo 1148636 1725119 := bstep (se 1 (by rfl) ⟨1293839, by rfl⟩ : syracuseStep 1725119 = 2587679) B2587679
theorem B1725311 : Blo 1148636 1725311 := bstep (se 1 (by rfl) ⟨1293983, by rfl⟩ : syracuseStep 1725311 = 2587967) B2587967
theorem B1725467 : Blo 1148636 1725467 := bstep (se 1 (by rfl) ⟨1294100, by rfl⟩ : syracuseStep 1725467 = 2588201) B2588201
theorem B1725671 : Blo 1148636 1725671 := bstep (se 1 (by rfl) ⟨1294253, by rfl⟩ : syracuseStep 1725671 = 2588507) B2588507
theorem B1725695 : Blo 1148636 1725695 := bstep (se 1 (by rfl) ⟨1294271, by rfl⟩ : syracuseStep 1725695 = 2588543) B2588543
theorem B6542639 : Blo 1148636 6542639 := bstep (se 1 (by rfl) ⟨4906979, by rfl⟩ : syracuseStep 6542639 = 9813959) B9813959
theorem B1726319 : Blo 1148636 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B1726703 : Blo 1148636 1726703 := bstep (se 1 (by rfl) ⟨1295027, by rfl⟩ : syracuseStep 1726703 = 2590055) B2590055
theorem B1726775 : Blo 1148636 1726775 := bstep (se 1 (by rfl) ⟨1295081, by rfl⟩ : syracuseStep 1726775 = 2590163) B2590163
theorem B1726823 : Blo 1148636 1726823 := bstep (se 1 (by rfl) ⟨1295117, by rfl⟩ : syracuseStep 1726823 = 2590235) B2590235
theorem B4152059 : Blo 1148636 4152059 := bstep (se 1 (by rfl) ⟨3114044, by rfl⟩ : syracuseStep 4152059 = 6228089) B6228089
theorem B1727471 : Blo 1148636 1727471 := bstep (se 1 (by rfl) ⟨1295603, by rfl⟩ : syracuseStep 1727471 = 2591207) B2591207
theorem B3038431 : Blo 1148636 3038431 := bstep (se 1 (by rfl) ⟨2278823, by rfl⟩ : syracuseStep 3038431 = 4557647) B4557647
theorem B1727723 : Blo 1148636 1727723 := bstep (se 1 (by rfl) ⟨1295792, by rfl⟩ : syracuseStep 1727723 = 2591585) B2591585
theorem B1727903 : Blo 1148636 1727903 := bstep (se 1 (by rfl) ⟨1295927, by rfl⟩ : syracuseStep 1727903 = 2591855) B2591855
theorem B6643127 : Blo 1148636 6643127 := bstep (se 1 (by rfl) ⟨4982345, by rfl⟩ : syracuseStep 6643127 = 9964691) B9964691
theorem B8281601 : Blo 1148636 8281601 := bstep (se 2 (by rfl) ⟨3105600, by rfl⟩ : syracuseStep 8281601 = 6211201) B6211201
theorem B1728251 : Blo 1148636 1728251 := bstep (se 1 (by rfl) ⟨1296188, by rfl⟩ : syracuseStep 1728251 = 2592377) B2592377
theorem B51109667 : Blo 1148636 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B29909033 : Blo 1148636 29909033 := bstep (se 2 (by rfl) ⟨11215887, by rfl⟩ : syracuseStep 29909033 = 22431775) B22431775
theorem B1728671 : Blo 1148636 1728671 := bstep (se 1 (by rfl) ⟨1296503, by rfl⟩ : syracuseStep 1728671 = 2593007) B2593007
theorem B1728923 : Blo 1148636 1728923 := bstep (se 1 (by rfl) ⟨1296692, by rfl⟩ : syracuseStep 1728923 = 2593385) B2593385
theorem B2187881 : Blo 1148636 2187881 := bstep (se 2 (by rfl) ⟨820455, by rfl⟩ : syracuseStep 2187881 = 1640911) B1640911
theorem B20964035 : Blo 1148636 20964035 := bstep (se 1 (by rfl) ⟨15723026, by rfl⟩ : syracuseStep 20964035 = 31446053) B31446053
theorem B22079951 : Blo 1148636 22079951 := bstep (se 1 (by rfl) ⟨16559963, by rfl⟩ : syracuseStep 22079951 = 33119927) B33119927
theorem B10480265 : Blo 1148636 10480265 := bstep (se 2 (by rfl) ⟨3930099, by rfl⟩ : syracuseStep 10480265 = 7860199) B7860199
theorem B3272663 : Blo 1148636 3272663 := bstep (se 1 (by rfl) ⟨2454497, by rfl⟩ : syracuseStep 3272663 = 4908995) B4908995
theorem B3273119 : Blo 1148636 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B9335483 : Blo 1148636 9335483 := bstep (se 1 (by rfl) ⟨7001612, by rfl⟩ : syracuseStep 9335483 = 14003225) B14003225
theorem B47871209 : Blo 1148636 47871209 := bstep (se 2 (by rfl) ⟨17951703, by rfl⟩ : syracuseStep 47871209 = 35903407) B35903407
theorem B1121252939 : Blo 1148636 1121252939 := bstep (se 1 (by rfl) ⟨840939704, by rfl⟩ : syracuseStep 1121252939 = 1681879409) B1681879409
theorem B7370669 : Blo 1148636 7370669 := bstep (se 3 (by rfl) ⟨1382000, by rfl⟩ : syracuseStep 7370669 = 2764001) B2764001
theorem B22116311 : Blo 1148636 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B8747027 : Blo 1148636 8747027 := bstep (se 1 (by rfl) ⟨6560270, by rfl⟩ : syracuseStep 8747027 = 13120541) B13120541
theorem B2586959 : Blo 1148636 2586959 := bstep (se 1 (by rfl) ⟨1940219, by rfl⟩ : syracuseStep 2586959 = 3880439) B3880439
theorem B5536459 : Blo 1148636 5536459 := bstep (se 1 (by rfl) ⟨4152344, by rfl⟩ : syracuseStep 5536459 = 8304689) B8304689
theorem B2587643 : Blo 1148636 2587643 := bstep (se 1 (by rfl) ⟨1940732, by rfl⟩ : syracuseStep 2587643 = 3881465) B3881465
theorem B3112607 : Blo 1148636 3112607 := bstep (se 1 (by rfl) ⟨2334455, by rfl⟩ : syracuseStep 3112607 = 4668911) B4668911
theorem B2458343 : Blo 1148636 2458343 := bstep (se 1 (by rfl) ⟨1843757, by rfl⟩ : syracuseStep 2458343 = 3687515) B3687515
theorem B2590433 : Blo 1148636 2590433 := bstep (se 2 (by rfl) ⟨971412, by rfl⟩ : syracuseStep 2590433 = 1942825) B1942825
theorem B1148927 : Blo 1148636 1148927 := bstep (se 1 (by rfl) ⟨861695, by rfl⟩ : syracuseStep 1148927 = 1723391) B1723391
theorem B1149415 : Blo 1148636 1149415 := bstep (se 1 (by rfl) ⟨862061, by rfl⟩ : syracuseStep 1149415 = 1724123) B1724123
theorem B2591225 : Blo 1148636 2591225 := bstep (se 2 (by rfl) ⟨971709, by rfl⟩ : syracuseStep 2591225 = 1943419) B1943419
theorem B1149439 : Blo 1148636 1149439 := bstep (se 1 (by rfl) ⟨862079, by rfl⟩ : syracuseStep 1149439 = 1724159) B1724159
theorem B1149567 : Blo 1148636 1149567 := bstep (se 1 (by rfl) ⟨862175, by rfl⟩ : syracuseStep 1149567 = 1724351) B1724351
theorem B1150055 : Blo 1148636 1150055 := bstep (se 1 (by rfl) ⟨862541, by rfl⟩ : syracuseStep 1150055 = 1725083) B1725083
theorem B1150079 : Blo 1148636 1150079 := bstep (se 1 (by rfl) ⟨862559, by rfl⟩ : syracuseStep 1150079 = 1725119) B1725119
theorem B4918427 : Blo 1148636 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B1150207 : Blo 1148636 1150207 := bstep (se 1 (by rfl) ⟨862655, by rfl⟩ : syracuseStep 1150207 = 1725311) B1725311
theorem B1150311 : Blo 1148636 1150311 := bstep (se 1 (by rfl) ⟨862733, by rfl⟩ : syracuseStep 1150311 = 1725467) B1725467
theorem B1150447 : Blo 1148636 1150447 := bstep (se 1 (by rfl) ⟨862835, by rfl⟩ : syracuseStep 1150447 = 1725671) B1725671
theorem B1150463 : Blo 1148636 1150463 := bstep (se 1 (by rfl) ⟨862847, by rfl⟩ : syracuseStep 1150463 = 1725695) B1725695
theorem B4361759 : Blo 1148636 4361759 := bstep (se 1 (by rfl) ⟨3271319, by rfl⟩ : syracuseStep 4361759 = 6542639) B6542639
theorem B340332191 : Blo 1148636 340332191 := bstep (se 1 (by rfl) ⟨255249143, by rfl⟩ : syracuseStep 340332191 = 510498287) B510498287
theorem B1150879 : Blo 1148636 1150879 := bstep (se 1 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 1150879 = 1726319) B1726319
theorem B2592809 : Blo 1148636 2592809 := bstep (se 2 (by rfl) ⟨972303, by rfl⟩ : syracuseStep 2592809 = 1944607) B1944607
theorem B1151135 : Blo 1148636 1151135 := bstep (se 1 (by rfl) ⟨863351, by rfl⟩ : syracuseStep 1151135 = 1726703) B1726703
theorem B1151183 : Blo 1148636 1151183 := bstep (se 1 (by rfl) ⟨863387, by rfl⟩ : syracuseStep 1151183 = 1726775) B1726775
theorem B1151215 : Blo 1148636 1151215 := bstep (se 1 (by rfl) ⟨863411, by rfl⟩ : syracuseStep 1151215 = 1726823) B1726823
theorem B1151647 : Blo 1148636 1151647 := bstep (se 1 (by rfl) ⟨863735, by rfl⟩ : syracuseStep 1151647 = 1727471) B1727471
theorem B1151815 : Blo 1148636 1151815 := bstep (se 1 (by rfl) ⟨863861, by rfl⟩ : syracuseStep 1151815 = 1727723) B1727723
theorem B4428665 : Blo 1148636 4428665 := bstep (se 2 (by rfl) ⟨1660749, by rfl⟩ : syracuseStep 4428665 = 3321499) B3321499
theorem B1151935 : Blo 1148636 1151935 := bstep (se 1 (by rfl) ⟨863951, by rfl⟩ : syracuseStep 1151935 = 1727903) B1727903
theorem B4428751 : Blo 1148636 4428751 := bstep (se 1 (by rfl) ⟨3321563, by rfl⟩ : syracuseStep 4428751 = 6643127) B6643127
theorem B1152167 : Blo 1148636 1152167 := bstep (se 1 (by rfl) ⟨864125, by rfl⟩ : syracuseStep 1152167 = 1728251) B1728251
theorem B1152447 : Blo 1148636 1152447 := bstep (se 1 (by rfl) ⟨864335, by rfl⟩ : syracuseStep 1152447 = 1728671) B1728671
theorem B1152615 : Blo 1148636 1152615 := bstep (se 1 (by rfl) ⟨864461, by rfl⟩ : syracuseStep 1152615 = 1728923) B1728923
theorem B14719967 : Blo 1148636 14719967 := bstep (se 1 (by rfl) ⟨11039975, by rfl⟩ : syracuseStep 14719967 = 22079951) B22079951
theorem B6986843 : Blo 1148636 6986843 := bstep (se 1 (by rfl) ⟨5240132, by rfl⟩ : syracuseStep 6986843 = 10480265) B10480265
theorem B24911297 : Blo 1148636 24911297 := bstep (se 2 (by rfl) ⟨9341736, by rfl⟩ : syracuseStep 24911297 = 18683473) B18683473
theorem B7381945 : Blo 1148636 7381945 := bstep (se 2 (by rfl) ⟨2768229, by rfl⟩ : syracuseStep 7381945 = 5536459) B5536459
theorem B12593065 : Blo 1148636 12593065 := bstep (se 2 (by rfl) ⟨4722399, by rfl⟩ : syracuseStep 12593065 = 9444799) B9444799
theorem B2075071 : Blo 1148636 2075071 := bstep (se 1 (by rfl) ⟨1556303, by rfl⟩ : syracuseStep 2075071 = 3112607) B3112607
theorem B8727101 : Blo 1148636 8727101 := bstep (se 3 (by rfl) ⟨1636331, by rfl⟩ : syracuseStep 8727101 = 3272663) B3272663
theorem B3878171 : Blo 1148636 3878171 := bstep (se 1 (by rfl) ⟨2908628, by rfl⟩ : syracuseStep 3878171 = 5817257) B5817257
theorem B17741111 : Blo 1148636 17741111 := bstep (se 1 (by rfl) ⟨13305833, by rfl⟩ : syracuseStep 17741111 = 26611667) B26611667
theorem B85177763 : Blo 1148636 85177763 := bstep (se 1 (by rfl) ⟨63883322, by rfl⟩ : syracuseStep 85177763 = 127766645) B127766645
theorem B59782961 : Blo 1148636 59782961 := bstep (se 2 (by rfl) ⟨22418610, by rfl⟩ : syracuseStep 59782961 = 44837221) B44837221
theorem B1293007 : Blo 1148636 1293007 := bstep (se 1 (by rfl) ⟨969755, by rfl⟩ : syracuseStep 1293007 = 1939511) B1939511
theorem B2768039 : Blo 1148636 2768039 := bstep (se 1 (by rfl) ⟨2076029, by rfl⟩ : syracuseStep 2768039 = 4152059) B4152059
theorem B4374121 : Blo 1148636 4374121 := bstep (se 2 (by rfl) ⟨1640295, by rfl⟩ : syracuseStep 4374121 = 3280591) B3280591
theorem B5521067 : Blo 1148636 5521067 := bstep (se 1 (by rfl) ⟨4140800, by rfl⟩ : syracuseStep 5521067 = 8281601) B8281601
theorem B1294015 : Blo 1148636 1294015 := bstep (se 1 (by rfl) ⟨970511, by rfl⟩ : syracuseStep 1294015 = 1941023) B1941023
theorem B19939355 : Blo 1148636 19939355 := bstep (se 1 (by rfl) ⟨14954516, by rfl⟩ : syracuseStep 19939355 = 29909033) B29909033
theorem B1294663 : Blo 1148636 1294663 := bstep (se 1 (by rfl) ⟨970997, by rfl⟩ : syracuseStep 1294663 = 1941995) B1941995
theorem B1458587 : Blo 1148636 1458587 := bstep (se 1 (by rfl) ⟨1093940, by rfl⟩ : syracuseStep 1458587 = 2187881) B2187881
theorem B13976023 : Blo 1148636 13976023 := bstep (se 1 (by rfl) ⟨10482017, by rfl⟩ : syracuseStep 13976023 = 20964035) B20964035
theorem B2182079 : Blo 1148636 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B1724639 : Blo 1148636 1724639 := bstep (se 1 (by rfl) ⟨1293479, by rfl⟩ : syracuseStep 1724639 = 2586959) B2586959
theorem B4051241 : Blo 1148636 4051241 := bstep (se 2 (by rfl) ⟨1519215, by rfl⟩ : syracuseStep 4051241 = 3038431) B3038431
theorem B9327077 : Blo 1148636 9327077 := bstep (se 4 (by rfl) ⟨874413, by rfl⟩ : syracuseStep 9327077 = 1748827) B1748827
theorem B1724969 : Blo 1148636 1724969 := bstep (se 2 (by rfl) ⟨646863, by rfl⟩ : syracuseStep 1724969 = 1293727) B1293727
theorem B1725095 : Blo 1148636 1725095 := bstep (se 1 (by rfl) ⟨1293821, by rfl⟩ : syracuseStep 1725095 = 2587643) B2587643
theorem B27973835 : Blo 1148636 27973835 := bstep (se 1 (by rfl) ⟨20980376, by rfl⟩ : syracuseStep 27973835 = 41960753) B41960753
theorem B1727465 : Blo 1148636 1727465 := bstep (se 2 (by rfl) ⟨647799, by rfl⟩ : syracuseStep 1727465 = 1295599) B1295599
theorem B23944423 : Blo 1148636 23944423 := bstep (se 1 (by rfl) ⟨17958317, by rfl⟩ : syracuseStep 23944423 = 35916635) B35916635
theorem B13098671 : Blo 1148636 13098671 := bstep (se 1 (by rfl) ⟨9824003, by rfl⟩ : syracuseStep 13098671 = 19648007) B19648007
theorem B1728335 : Blo 1148636 1728335 := bstep (se 1 (by rfl) ⟨1296251, by rfl⟩ : syracuseStep 1728335 = 2592503) B2592503
theorem B1728491 : Blo 1148636 1728491 := bstep (se 1 (by rfl) ⟨1296368, by rfl⟩ : syracuseStep 1728491 = 2592737) B2592737
theorem B127656557 : Blo 1148636 127656557 := bstep (se 3 (by rfl) ⟨23935604, by rfl⟩ : syracuseStep 127656557 = 47871209) B47871209
theorem B34073111 : Blo 1148636 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B3108833 : Blo 1148636 3108833 := bstep (se 2 (by rfl) ⟨1165812, by rfl⟩ : syracuseStep 3108833 = 2331625) B2331625
theorem B2585825 : Blo 1148636 2585825 := bstep (se 2 (by rfl) ⟨969684, by rfl⟩ : syracuseStep 2585825 = 1939369) B1939369
theorem B6223655 : Blo 1148636 6223655 := bstep (se 1 (by rfl) ⟨4667741, by rfl⟩ : syracuseStep 6223655 = 9335483) B9335483
theorem B2586491 : Blo 1148636 2586491 := bstep (se 1 (by rfl) ⟨1939868, by rfl⟩ : syracuseStep 2586491 = 3879737) B3879737
theorem B19626137 : Blo 1148636 19626137 := bstep (se 2 (by rfl) ⟨7359801, by rfl⟩ : syracuseStep 19626137 = 14719603) B14719603
theorem B747501959 : Blo 1148636 747501959 := bstep (se 1 (by rfl) ⟨560626469, by rfl⟩ : syracuseStep 747501959 = 1121252939) B1121252939
theorem B2587049 : Blo 1148636 2587049 := bstep (se 2 (by rfl) ⟨970143, by rfl⟩ : syracuseStep 2587049 = 1940287) B1940287
theorem B2587103 : Blo 1148636 2587103 := bstep (se 1 (by rfl) ⟨1940327, by rfl⟩ : syracuseStep 2587103 = 3880655) B3880655
theorem B4913779 : Blo 1148636 4913779 := bstep (se 1 (by rfl) ⟨3685334, by rfl⟩ : syracuseStep 4913779 = 7370669) B7370669
theorem B14744207 : Blo 1148636 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B5831351 : Blo 1148636 5831351 := bstep (se 1 (by rfl) ⟨4373513, by rfl⟩ : syracuseStep 5831351 = 8747027) B8747027
theorem B2587355 : Blo 1148636 2587355 := bstep (se 1 (by rfl) ⟨1940516, by rfl⟩ : syracuseStep 2587355 = 3881033) B3881033
theorem B2916263 : Blo 1148636 2916263 := bstep (se 1 (by rfl) ⟨2187197, by rfl⟩ : syracuseStep 2916263 = 4374395) B4374395
theorem B1638895 : Blo 1148636 1638895 := bstep (se 1 (by rfl) ⟨1229171, by rfl⟩ : syracuseStep 1638895 = 2458343) B2458343
theorem B3278951 : Blo 1148636 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B226888127 : Blo 1148636 226888127 := bstep (se 1 (by rfl) ⟨170166095, by rfl⟩ : syracuseStep 226888127 = 340332191) B340332191
theorem B1149759 : Blo 1148636 1149759 := bstep (se 1 (by rfl) ⟨862319, by rfl⟩ : syracuseStep 1149759 = 1724639) B1724639
theorem B1149979 : Blo 1148636 1149979 := bstep (se 1 (by rfl) ⟨862484, by rfl⟩ : syracuseStep 1149979 = 1724969) B1724969
theorem B1150063 : Blo 1148636 1150063 := bstep (se 1 (by rfl) ⟨862547, by rfl⟩ : syracuseStep 1150063 = 1725095) B1725095
theorem B2952443 : Blo 1148636 2952443 := bstep (se 1 (by rfl) ⟨2214332, by rfl⟩ : syracuseStep 2952443 = 4428665) B4428665
theorem B18649223 : Blo 1148636 18649223 := bstep (se 1 (by rfl) ⟨13986917, by rfl⟩ : syracuseStep 18649223 = 27973835) B27973835
theorem B1151643 : Blo 1148636 1151643 := bstep (se 1 (by rfl) ⟨863732, by rfl⟩ : syracuseStep 1151643 = 1727465) B1727465
theorem B4657895 : Blo 1148636 4657895 := bstep (se 1 (by rfl) ⟨3493421, by rfl⟩ : syracuseStep 4657895 = 6986843) B6986843
theorem B159421229 : Blo 1148636 159421229 := bstep (se 3 (by rfl) ⟨29891480, by rfl⟩ : syracuseStep 159421229 = 59782961) B59782961
theorem B1152223 : Blo 1148636 1152223 := bstep (se 1 (by rfl) ⟨864167, by rfl⟩ : syracuseStep 1152223 = 1728335) B1728335
theorem B1152327 : Blo 1148636 1152327 := bstep (se 1 (by rfl) ⟨864245, by rfl⟩ : syracuseStep 1152327 = 1728491) B1728491
theorem B85104371 : Blo 1148636 85104371 := bstep (se 1 (by rfl) ⟨63828278, by rfl⟩ : syracuseStep 85104371 = 127656557) B127656557
theorem B5905001 : Blo 1148636 5905001 := bstep (se 2 (by rfl) ⟨2214375, by rfl⟩ : syracuseStep 5905001 = 4428751) B4428751
theorem B22715407 : Blo 1148636 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B2072555 : Blo 1148636 2072555 := bstep (se 1 (by rfl) ⟨1554416, by rfl⟩ : syracuseStep 2072555 = 3108833) B3108833
theorem B13084091 : Blo 1148636 13084091 := bstep (se 1 (by rfl) ⟨9813068, by rfl⟩ : syracuseStep 13084091 = 19626137) B19626137
theorem B31925897 : Blo 1148636 31925897 := bstep (se 2 (by rfl) ⟨11972211, by rfl⟩ : syracuseStep 31925897 = 23944423) B23944423
theorem B1845359 : Blo 1148636 1845359 := bstep (se 1 (by rfl) ⟨1384019, by rfl⟩ : syracuseStep 1845359 = 2768039) B2768039
theorem B3680711 : Blo 1148636 3680711 := bstep (se 1 (by rfl) ⟨2760533, by rfl⟩ : syracuseStep 3680711 = 5521067) B5521067
theorem B1944175 : Blo 1148636 1944175 := bstep (se 1 (by rfl) ⟨1458131, by rfl⟩ : syracuseStep 1944175 = 2916263) B2916263
theorem B9842593 : Blo 1148636 9842593 := bstep (se 2 (by rfl) ⟨3690972, by rfl⟩ : syracuseStep 9842593 = 7381945) B7381945
theorem B16790753 : Blo 1148636 16790753 := bstep (se 2 (by rfl) ⟨6296532, by rfl⟩ : syracuseStep 16790753 = 12593065) B12593065
theorem B2700827 : Blo 1148636 2700827 := bstep (se 1 (by rfl) ⟨2025620, by rfl⟩ : syracuseStep 2700827 = 4051241) B4051241
theorem B2766761 : Blo 1148636 2766761 := bstep (se 2 (by rfl) ⟨1037535, by rfl⟩ : syracuseStep 2766761 = 2075071) B2075071
theorem B9813311 : Blo 1148636 9813311 := bstep (se 1 (by rfl) ⟨7359983, by rfl⟩ : syracuseStep 9813311 = 14719967) B14719967
theorem B16596413 : Blo 1148636 16596413 := bstep (se 3 (by rfl) ⟨3111827, by rfl⟩ : syracuseStep 16596413 = 6223655) B6223655
theorem B8732447 : Blo 1148636 8732447 := bstep (se 1 (by rfl) ⟨6549335, by rfl⟩ : syracuseStep 8732447 = 13098671) B13098671
theorem B5818067 : Blo 1148636 5818067 := bstep (se 1 (by rfl) ⟨4363550, by rfl⟩ : syracuseStep 5818067 = 8727101) B8727101
theorem B5818877 : Blo 1148636 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B1723883 : Blo 1148636 1723883 := bstep (se 1 (by rfl) ⟨1292912, by rfl⟩ : syracuseStep 1723883 = 2585825) B2585825
theorem B1724009 : Blo 1148636 1724009 := bstep (se 2 (by rfl) ⟨646503, by rfl⟩ : syracuseStep 1724009 = 1293007) B1293007
theorem B1724327 : Blo 1148636 1724327 := bstep (se 1 (by rfl) ⟨1293245, by rfl⟩ : syracuseStep 1724327 = 2586491) B2586491
theorem B1724699 : Blo 1148636 1724699 := bstep (se 1 (by rfl) ⟨1293524, by rfl⟩ : syracuseStep 1724699 = 2587049) B2587049
theorem B1724735 : Blo 1148636 1724735 := bstep (se 1 (by rfl) ⟨1293551, by rfl⟩ : syracuseStep 1724735 = 2587103) B2587103
theorem B3887567 : Blo 1148636 3887567 := bstep (se 1 (by rfl) ⟨2915675, by rfl⟩ : syracuseStep 3887567 = 5831351) B5831351
theorem B1724903 : Blo 1148636 1724903 := bstep (se 1 (by rfl) ⟨1293677, by rfl⟩ : syracuseStep 1724903 = 2587355) B2587355
theorem B1725353 : Blo 1148636 1725353 := bstep (se 2 (by rfl) ⟨647007, by rfl⟩ : syracuseStep 1725353 = 1294015) B1294015
theorem B13292903 : Blo 1148636 13292903 := bstep (se 1 (by rfl) ⟨9969677, by rfl⟩ : syracuseStep 13292903 = 19939355) B19939355
theorem B1726217 : Blo 1148636 1726217 := bstep (se 2 (by rfl) ⟨647331, by rfl⟩ : syracuseStep 1726217 = 1294663) B1294663
theorem B18634697 : Blo 1148636 18634697 := bstep (se 2 (by rfl) ⟨6988011, by rfl⟩ : syracuseStep 18634697 = 13976023) B13976023
theorem B3889565 : Blo 1148636 3889565 := bstep (se 3 (by rfl) ⟨729293, by rfl⟩ : syracuseStep 3889565 = 1458587) B1458587
theorem B1726955 : Blo 1148636 1726955 := bstep (se 1 (by rfl) ⟨1295216, by rfl⟩ : syracuseStep 1726955 = 2590433) B2590433
theorem B1727483 : Blo 1148636 1727483 := bstep (se 1 (by rfl) ⟨1295612, by rfl⟩ : syracuseStep 1727483 = 2591225) B2591225
theorem B2907839 : Blo 1148636 2907839 := bstep (se 1 (by rfl) ⟨2180879, by rfl⟩ : syracuseStep 2907839 = 4361759) B4361759
theorem B1728539 : Blo 1148636 1728539 := bstep (se 1 (by rfl) ⟨1296404, by rfl⟩ : syracuseStep 1728539 = 2592809) B2592809
theorem B6218051 : Blo 1148636 6218051 := bstep (se 1 (by rfl) ⟨4663538, by rfl⟩ : syracuseStep 6218051 = 9327077) B9327077
theorem B47309629 : Blo 1148636 47309629 := bstep (se 3 (by rfl) ⟨8870555, by rfl⟩ : syracuseStep 47309629 = 17741111) B17741111
theorem B16607531 : Blo 1148636 16607531 := bstep (se 1 (by rfl) ⟨12455648, by rfl⟩ : syracuseStep 16607531 = 24911297) B24911297
theorem B2585447 : Blo 1148636 2585447 := bstep (se 1 (by rfl) ⟨1939085, by rfl⟩ : syracuseStep 2585447 = 3878171) B3878171
theorem B6551705 : Blo 1148636 6551705 := bstep (se 2 (by rfl) ⟨2456889, by rfl⟩ : syracuseStep 6551705 = 4913779) B4913779
theorem B56785175 : Blo 1148636 56785175 := bstep (se 1 (by rfl) ⟨42588881, by rfl⟩ : syracuseStep 56785175 = 85177763) B85177763
theorem B498334639 : Blo 1148636 498334639 := bstep (se 1 (by rfl) ⟨373750979, by rfl⟩ : syracuseStep 498334639 = 747501959) B747501959
theorem B9829471 : Blo 1148636 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B5832161 : Blo 1148636 5832161 := bstep (se 2 (by rfl) ⟨2187060, by rfl⟩ : syracuseStep 5832161 = 4374121) B4374121
theorem B16581469 : Blo 1148636 16581469 := bstep (se 3 (by rfl) ⟨3109025, by rfl⟩ : syracuseStep 16581469 = 6218051) B6218051
theorem B63079505 : Blo 1148636 63079505 := bstep (se 2 (by rfl) ⟨23654814, by rfl⟩ : syracuseStep 63079505 = 47309629) B47309629
theorem B151258751 : Blo 1148636 151258751 := bstep (se 1 (by rfl) ⟨113444063, by rfl⟩ : syracuseStep 151258751 = 226888127) B226888127
theorem B1968295 : Blo 1148636 1968295 := bstep (se 1 (by rfl) ⟨1476221, by rfl⟩ : syracuseStep 1968295 = 2952443) B2952443
theorem B1149255 : Blo 1148636 1149255 := bstep (se 1 (by rfl) ⟨861941, by rfl⟩ : syracuseStep 1149255 = 1723883) B1723883
theorem B1149339 : Blo 1148636 1149339 := bstep (se 1 (by rfl) ⟨862004, by rfl⟩ : syracuseStep 1149339 = 1724009) B1724009
theorem B1149551 : Blo 1148636 1149551 := bstep (se 1 (by rfl) ⟨862163, by rfl⟩ : syracuseStep 1149551 = 1724327) B1724327
theorem B1149799 : Blo 1148636 1149799 := bstep (se 1 (by rfl) ⟨862349, by rfl⟩ : syracuseStep 1149799 = 1724699) B1724699
theorem B1149823 : Blo 1148636 1149823 := bstep (se 1 (by rfl) ⟨862367, by rfl⟩ : syracuseStep 1149823 = 1724735) B1724735
theorem B2591711 : Blo 1148636 2591711 := bstep (se 1 (by rfl) ⟨1943783, by rfl⟩ : syracuseStep 2591711 = 3887567) B3887567
theorem B1149935 : Blo 1148636 1149935 := bstep (se 1 (by rfl) ⟨862451, by rfl⟩ : syracuseStep 1149935 = 1724903) B1724903
theorem B1150235 : Blo 1148636 1150235 := bstep (se 1 (by rfl) ⟨862676, by rfl⟩ : syracuseStep 1150235 = 1725353) B1725353
theorem B2592233 : Blo 1148636 2592233 := bstep (se 2 (by rfl) ⟨972087, by rfl⟩ : syracuseStep 2592233 = 1944175) B1944175
theorem B1150811 : Blo 1148636 1150811 := bstep (se 1 (by rfl) ⟨863108, by rfl⟩ : syracuseStep 1150811 = 1726217) B1726217
theorem B12423131 : Blo 1148636 12423131 := bstep (se 1 (by rfl) ⟨9317348, by rfl⟩ : syracuseStep 12423131 = 18634697) B18634697
theorem B2593043 : Blo 1148636 2593043 := bstep (se 1 (by rfl) ⟨1944782, by rfl⟩ : syracuseStep 2593043 = 3889565) B3889565
theorem B1151303 : Blo 1148636 1151303 := bstep (se 1 (by rfl) ⟨863477, by rfl⟩ : syracuseStep 1151303 = 1726955) B1726955
theorem B3936667 : Blo 1148636 3936667 := bstep (se 1 (by rfl) ⟨2952500, by rfl⟩ : syracuseStep 3936667 = 5905001) B5905001
theorem B1151655 : Blo 1148636 1151655 := bstep (se 1 (by rfl) ⟨863741, by rfl⟩ : syracuseStep 1151655 = 1727483) B1727483
theorem B1938559 : Blo 1148636 1938559 := bstep (se 1 (by rfl) ⟨1453919, by rfl⟩ : syracuseStep 1938559 = 2907839) B2907839
theorem B1381703 : Blo 1148636 1381703 := bstep (se 1 (by rfl) ⟨1036277, by rfl⟩ : syracuseStep 1381703 = 2072555) B2072555
theorem B1152359 : Blo 1148636 1152359 := bstep (se 1 (by rfl) ⟨864269, by rfl⟩ : syracuseStep 1152359 = 1728539) B1728539
theorem B8722727 : Blo 1148636 8722727 := bstep (se 1 (by rfl) ⟨6542045, by rfl⟩ : syracuseStep 8722727 = 13084091) B13084091
theorem B664446185 : Blo 1148636 664446185 := bstep (se 2 (by rfl) ⟨249167319, by rfl⟩ : syracuseStep 664446185 = 498334639) B498334639
theorem B1844507 : Blo 1148636 1844507 := bstep (se 1 (by rfl) ⟨1383380, by rfl⟩ : syracuseStep 1844507 = 2766761) B2766761
theorem B30287209 : Blo 1148636 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B4367803 : Blo 1148636 4367803 := bstep (se 1 (by rfl) ⟨3275852, by rfl⟩ : syracuseStep 4367803 = 6551705) B6551705
theorem B37856783 : Blo 1148636 37856783 := bstep (se 1 (by rfl) ⟨28392587, by rfl⟩ : syracuseStep 37856783 = 56785175) B56785175
theorem B3878711 : Blo 1148636 3878711 := bstep (se 1 (by rfl) ⟨2909033, by rfl⟩ : syracuseStep 3878711 = 5818067) B5818067
theorem B3879251 : Blo 1148636 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B12432815 : Blo 1148636 12432815 := bstep (se 1 (by rfl) ⟨9324611, by rfl⟩ : syracuseStep 12432815 = 18649223) B18649223
theorem B106280819 : Blo 1148636 106280819 := bstep (se 1 (by rfl) ⟨79710614, by rfl⟩ : syracuseStep 106280819 = 159421229) B159421229
theorem B44775341 : Blo 1148636 44775341 := bstep (se 3 (by rfl) ⟨8395376, by rfl⟩ : syracuseStep 44775341 = 16790753) B16790753
theorem B8861935 : Blo 1148636 8861935 := bstep (se 1 (by rfl) ⟨6646451, by rfl⟩ : syracuseStep 8861935 = 13292903) B13292903
theorem B56736247 : Blo 1148636 56736247 := bstep (se 1 (by rfl) ⟨42552185, by rfl⟩ : syracuseStep 56736247 = 85104371) B85104371
theorem B13123457 : Blo 1148636 13123457 := bstep (se 2 (by rfl) ⟨4921296, by rfl⟩ : syracuseStep 13123457 = 9842593) B9842593
theorem B44286749 : Blo 1148636 44286749 := bstep (se 3 (by rfl) ⟨8303765, by rfl⟩ : syracuseStep 44286749 = 16607531) B16607531
theorem B21283931 : Blo 1148636 21283931 := bstep (se 1 (by rfl) ⟨15962948, by rfl⟩ : syracuseStep 21283931 = 31925897) B31925897
theorem B1230239 : Blo 1148636 1230239 := bstep (se 1 (by rfl) ⟨922679, by rfl⟩ : syracuseStep 1230239 = 1845359) B1845359
theorem B1723631 : Blo 1148636 1723631 := bstep (se 1 (by rfl) ⟨1292723, by rfl⟩ : syracuseStep 1723631 = 2585447) B2585447
theorem B6542207 : Blo 1148636 6542207 := bstep (se 1 (by rfl) ⟨4906655, by rfl⟩ : syracuseStep 6542207 = 9813311) B9813311
theorem B11064275 : Blo 1148636 11064275 := bstep (se 1 (by rfl) ⟨8298206, by rfl⟩ : syracuseStep 11064275 = 16596413) B16596413
theorem B3888107 : Blo 1148636 3888107 := bstep (se 1 (by rfl) ⟨2916080, by rfl⟩ : syracuseStep 3888107 = 5832161) B5832161
theorem B5821631 : Blo 1148636 5821631 := bstep (se 1 (by rfl) ⟨4366223, by rfl⟩ : syracuseStep 5821631 = 8732447) B8732447
theorem B2185193 : Blo 1148636 2185193 := bstep (se 2 (by rfl) ⟨819447, by rfl⟩ : syracuseStep 2185193 = 1638895) B1638895
theorem B2185967 : Blo 1148636 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B3105263 : Blo 1148636 3105263 := bstep (se 1 (by rfl) ⟨2328947, by rfl⟩ : syracuseStep 3105263 = 4657895) B4657895
theorem B2453807 : Blo 1148636 2453807 := bstep (se 1 (by rfl) ⟨1840355, by rfl⟩ : syracuseStep 2453807 = 3680711) B3680711
theorem B1800551 : Blo 1148636 1800551 := bstep (se 1 (by rfl) ⟨1350413, by rfl⟩ : syracuseStep 1800551 = 2700827) B2700827
theorem B13105961 : Blo 1148636 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B29524499 : Blo 1148636 29524499 := bstep (se 1 (by rfl) ⟨22143374, by rfl⟩ : syracuseStep 29524499 = 44286749) B44286749
theorem B14189287 : Blo 1148636 14189287 := bstep (se 1 (by rfl) ⟨10641965, by rfl⟩ : syracuseStep 14189287 = 21283931) B21283931
theorem B1149087 : Blo 1148636 1149087 := bstep (se 1 (by rfl) ⟨861815, by rfl⟩ : syracuseStep 1149087 = 1723631) B1723631
theorem B2624393 : Blo 1148636 2624393 := bstep (se 2 (by rfl) ⟨984147, by rfl⟩ : syracuseStep 2624393 = 1968295) B1968295
theorem B4361471 : Blo 1148636 4361471 := bstep (se 1 (by rfl) ⟨3271103, by rfl⟩ : syracuseStep 4361471 = 6542207) B6542207
theorem B7376183 : Blo 1148636 7376183 := bstep (se 1 (by rfl) ⟨5532137, by rfl⟩ : syracuseStep 7376183 = 11064275) B11064275
theorem B2592071 : Blo 1148636 2592071 := bstep (se 1 (by rfl) ⟨1944053, by rfl⟩ : syracuseStep 2592071 = 3888107) B3888107
theorem B3280637 : Blo 1148636 3280637 := bstep (se 3 (by rfl) ⟨615119, by rfl⟩ : syracuseStep 3280637 = 1230239) B1230239
theorem B5248889 : Blo 1148636 5248889 := bstep (se 2 (by rfl) ⟨1968333, by rfl⟩ : syracuseStep 5248889 = 3936667) B3936667
theorem B442964123 : Blo 1148636 442964123 := bstep (se 1 (by rfl) ⟨332223092, by rfl⟩ : syracuseStep 442964123 = 664446185) B664446185
theorem B25237855 : Blo 1148636 25237855 := bstep (se 1 (by rfl) ⟨18928391, by rfl⟩ : syracuseStep 25237855 = 37856783) B37856783
theorem B70853879 : Blo 1148636 70853879 := bstep (se 1 (by rfl) ⟨53140409, by rfl⟩ : syracuseStep 70853879 = 106280819) B106280819
theorem B42053003 : Blo 1148636 42053003 := bstep (se 1 (by rfl) ⟨31539752, by rfl⟩ : syracuseStep 42053003 = 63079505) B63079505
theorem B100839167 : Blo 1148636 100839167 := bstep (se 1 (by rfl) ⟨75629375, by rfl⟩ : syracuseStep 100839167 = 151258751) B151258751
theorem B40382945 : Blo 1148636 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B3881087 : Blo 1148636 3881087 := bstep (se 1 (by rfl) ⟨2910815, by rfl⟩ : syracuseStep 3881087 = 5821631) B5821631
theorem B3684541 : Blo 1148636 3684541 := bstep (se 3 (by rfl) ⟨690851, by rfl⟩ : syracuseStep 3684541 = 1381703) B1381703
theorem B1456795 : Blo 1148636 1456795 := bstep (se 1 (by rfl) ⟨1092596, by rfl⟩ : syracuseStep 1456795 = 2185193) B2185193
theorem B5815151 : Blo 1148636 5815151 := bstep (se 1 (by rfl) ⟨4361363, by rfl⟩ : syracuseStep 5815151 = 8722727) B8722727
theorem B1229671 : Blo 1148636 1229671 := bstep (se 1 (by rfl) ⟨922253, by rfl⟩ : syracuseStep 1229671 = 1844507) B1844507
theorem B11815913 : Blo 1148636 11815913 := bstep (se 2 (by rfl) ⟨4430967, by rfl⟩ : syracuseStep 11815913 = 8861935) B8861935
theorem B75648329 : Blo 1148636 75648329 := bstep (se 2 (by rfl) ⟨28368123, by rfl⟩ : syracuseStep 75648329 = 56736247) B56736247
theorem B1200367 : Blo 1148636 1200367 := bstep (se 1 (by rfl) ⟨900275, by rfl⟩ : syracuseStep 1200367 = 1800551) B1800551
theorem B8737307 : Blo 1148636 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B22108625 : Blo 1148636 22108625 := bstep (se 2 (by rfl) ⟨8290734, by rfl⟩ : syracuseStep 22108625 = 16581469) B16581469
theorem B8280701 : Blo 1148636 8280701 := bstep (se 3 (by rfl) ⟨1552631, by rfl⟩ : syracuseStep 8280701 = 3105263) B3105263
theorem B5823737 : Blo 1148636 5823737 := bstep (se 2 (by rfl) ⟨2183901, by rfl⟩ : syracuseStep 5823737 = 4367803) B4367803
theorem B1727807 : Blo 1148636 1727807 := bstep (se 1 (by rfl) ⟨1295855, by rfl⟩ : syracuseStep 1727807 = 2591711) B2591711
theorem B1728155 : Blo 1148636 1728155 := bstep (se 1 (by rfl) ⟨1296116, by rfl⟩ : syracuseStep 1728155 = 2592233) B2592233
theorem B8282087 : Blo 1148636 8282087 := bstep (se 1 (by rfl) ⟨6211565, by rfl⟩ : syracuseStep 8282087 = 12423131) B12423131
theorem B1728695 : Blo 1148636 1728695 := bstep (se 1 (by rfl) ⟨1296521, by rfl⟩ : syracuseStep 1728695 = 2593043) B2593043
theorem B2584745 : Blo 1148636 2584745 := bstep (se 2 (by rfl) ⟨969279, by rfl⟩ : syracuseStep 2584745 = 1938559) B1938559
theorem B5829245 : Blo 1148636 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B2585807 : Blo 1148636 2585807 := bstep (se 1 (by rfl) ⟨1939355, by rfl⟩ : syracuseStep 2585807 = 3878711) B3878711
theorem B1635871 : Blo 1148636 1635871 := bstep (se 1 (by rfl) ⟨1226903, by rfl⟩ : syracuseStep 1635871 = 2453807) B2453807
theorem B2586167 : Blo 1148636 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B8288543 : Blo 1148636 8288543 := bstep (se 1 (by rfl) ⟨6216407, by rfl⟩ : syracuseStep 8288543 = 12432815) B12432815
theorem B29850227 : Blo 1148636 29850227 := bstep (se 1 (by rfl) ⟨22387670, by rfl⟩ : syracuseStep 29850227 = 44775341) B44775341
theorem B8748971 : Blo 1148636 8748971 := bstep (se 1 (by rfl) ⟨6561728, by rfl⟩ : syracuseStep 8748971 = 13123457) B13123457
theorem B4917455 : Blo 1148636 4917455 := bstep (se 1 (by rfl) ⟨3688091, by rfl⟩ : syracuseStep 4917455 = 7376183) B7376183
theorem B50432219 : Blo 1148636 50432219 := bstep (se 1 (by rfl) ⟨37824164, by rfl⟩ : syracuseStep 50432219 = 75648329) B75648329
theorem B295309415 : Blo 1148636 295309415 := bstep (se 1 (by rfl) ⟨221482061, by rfl⟩ : syracuseStep 295309415 = 442964123) B442964123
theorem B6558245 : Blo 1148636 6558245 := bstep (se 4 (by rfl) ⟨614835, by rfl⟩ : syracuseStep 6558245 = 1229671) B1229671
theorem B1151871 : Blo 1148636 1151871 := bstep (se 1 (by rfl) ⟨863903, by rfl⟩ : syracuseStep 1151871 = 1727807) B1727807
theorem B1152103 : Blo 1148636 1152103 := bstep (se 1 (by rfl) ⟨864077, by rfl⟩ : syracuseStep 1152103 = 1728155) B1728155
theorem B1152463 : Blo 1148636 1152463 := bstep (se 1 (by rfl) ⟨864347, by rfl⟩ : syracuseStep 1152463 = 1728695) B1728695
theorem B1942393 : Blo 1148636 1942393 := bstep (se 2 (by rfl) ⟨728397, by rfl⟩ : syracuseStep 1942393 = 1456795) B1456795
theorem B19900151 : Blo 1148636 19900151 := bstep (se 1 (by rfl) ⟨14925113, by rfl⟩ : syracuseStep 19900151 = 29850227) B29850227
theorem B3876767 : Blo 1148636 3876767 := bstep (se 1 (by rfl) ⟨2907575, by rfl⟩ : syracuseStep 3876767 = 5815151) B5815151
theorem B18919049 : Blo 1148636 18919049 := bstep (se 2 (by rfl) ⟨7094643, by rfl⟩ : syracuseStep 18919049 = 14189287) B14189287
theorem B1749595 : Blo 1148636 1749595 := bstep (se 1 (by rfl) ⟨1312196, by rfl⟩ : syracuseStep 1749595 = 2624393) B2624393
theorem B5520467 : Blo 1148636 5520467 := bstep (se 1 (by rfl) ⟨4140350, by rfl⟩ : syracuseStep 5520467 = 8280701) B8280701
theorem B3882491 : Blo 1148636 3882491 := bstep (se 1 (by rfl) ⟨2911868, by rfl⟩ : syracuseStep 3882491 = 5823737) B5823737
theorem B5521391 : Blo 1148636 5521391 := bstep (se 1 (by rfl) ⟨4141043, by rfl⟩ : syracuseStep 5521391 = 8282087) B8282087
theorem B47235919 : Blo 1148636 47235919 := bstep (se 1 (by rfl) ⟨35426939, by rfl⟩ : syracuseStep 47235919 = 70853879) B70853879
theorem B2181161 : Blo 1148636 2181161 := bstep (se 2 (by rfl) ⟨817935, by rfl⟩ : syracuseStep 2181161 = 1635871) B1635871
theorem B28035335 : Blo 1148636 28035335 := bstep (se 1 (by rfl) ⟨21026501, by rfl⟩ : syracuseStep 28035335 = 42053003) B42053003
theorem B67226111 : Blo 1148636 67226111 := bstep (se 1 (by rfl) ⟨50419583, by rfl⟩ : syracuseStep 67226111 = 100839167) B100839167
theorem B31509101 : Blo 1148636 31509101 := bstep (se 3 (by rfl) ⟨5907956, by rfl⟩ : syracuseStep 31509101 = 11815913) B11815913
theorem B1723163 : Blo 1148636 1723163 := bstep (se 1 (by rfl) ⟨1292372, by rfl⟩ : syracuseStep 1723163 = 2584745) B2584745
theorem B26921963 : Blo 1148636 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B3886163 : Blo 1148636 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B1723871 : Blo 1148636 1723871 := bstep (se 1 (by rfl) ⟨1292903, by rfl⟩ : syracuseStep 1723871 = 2585807) B2585807
theorem B1724111 : Blo 1148636 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B5525695 : Blo 1148636 5525695 := bstep (se 1 (by rfl) ⟨4144271, by rfl⟩ : syracuseStep 5525695 = 8288543) B8288543
theorem B19682999 : Blo 1148636 19682999 := bstep (se 1 (by rfl) ⟨14762249, by rfl⟩ : syracuseStep 19682999 = 29524499) B29524499
theorem B2907647 : Blo 1148636 2907647 := bstep (se 1 (by rfl) ⟨2180735, by rfl⟩ : syracuseStep 2907647 = 4361471) B4361471
theorem B1728047 : Blo 1148636 1728047 := bstep (se 1 (by rfl) ⟨1296035, by rfl⟩ : syracuseStep 1728047 = 2592071) B2592071
theorem B2187091 : Blo 1148636 2187091 := bstep (se 1 (by rfl) ⟨1640318, by rfl⟩ : syracuseStep 2187091 = 3280637) B3280637
theorem B5824871 : Blo 1148636 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B3499259 : Blo 1148636 3499259 := bstep (se 1 (by rfl) ⟨2624444, by rfl⟩ : syracuseStep 3499259 = 5248889) B5248889
theorem B14739083 : Blo 1148636 14739083 := bstep (se 1 (by rfl) ⟨11054312, by rfl⟩ : syracuseStep 14739083 = 22108625) B22108625
theorem B1600489 : Blo 1148636 1600489 := bstep (se 2 (by rfl) ⟨600183, by rfl⟩ : syracuseStep 1600489 = 1200367) B1200367
theorem B4912721 : Blo 1148636 4912721 := bstep (se 2 (by rfl) ⟨1842270, by rfl⟩ : syracuseStep 4912721 = 3684541) B3684541
theorem B33650473 : Blo 1148636 33650473 := bstep (se 2 (by rfl) ⟨12618927, by rfl⟩ : syracuseStep 33650473 = 25237855) B25237855
theorem B2587391 : Blo 1148636 2587391 := bstep (se 1 (by rfl) ⟨1940543, by rfl⟩ : syracuseStep 2587391 = 3881087) B3881087
theorem B5832647 : Blo 1148636 5832647 := bstep (se 1 (by rfl) ⟨4374485, by rfl⟩ : syracuseStep 5832647 = 8748971) B8748971
theorem B62981225 : Blo 1148636 62981225 := bstep (se 2 (by rfl) ⟨23617959, by rfl⟩ : syracuseStep 62981225 = 47235919) B47235919
theorem B2589857 : Blo 1148636 2589857 := bstep (se 2 (by rfl) ⟨971196, by rfl⟩ : syracuseStep 2589857 = 1942393) B1942393
theorem B3278303 : Blo 1148636 3278303 := bstep (se 1 (by rfl) ⟨2458727, by rfl⟩ : syracuseStep 3278303 = 4917455) B4917455
theorem B33621479 : Blo 1148636 33621479 := bstep (se 1 (by rfl) ⟨25216109, by rfl⟩ : syracuseStep 33621479 = 50432219) B50432219
theorem B21006067 : Blo 1148636 21006067 := bstep (se 1 (by rfl) ⟨15754550, by rfl⟩ : syracuseStep 21006067 = 31509101) B31509101
theorem B1148775 : Blo 1148636 1148775 := bstep (se 1 (by rfl) ⟨861581, by rfl⟩ : syracuseStep 1148775 = 1723163) B1723163
theorem B2590775 : Blo 1148636 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B1149247 : Blo 1148636 1149247 := bstep (se 1 (by rfl) ⟨861935, by rfl⟩ : syracuseStep 1149247 = 1723871) B1723871
theorem B1149407 : Blo 1148636 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B196872943 : Blo 1148636 196872943 := bstep (se 1 (by rfl) ⟨147654707, by rfl⟩ : syracuseStep 196872943 = 295309415) B295309415
theorem B2133985 : Blo 1148636 2133985 := bstep (se 2 (by rfl) ⟨800244, by rfl⟩ : syracuseStep 2133985 = 1600489) B1600489
theorem B1938431 : Blo 1148636 1938431 := bstep (se 1 (by rfl) ⟨1453823, by rfl⟩ : syracuseStep 1938431 = 2907647) B2907647
theorem B1152031 : Blo 1148636 1152031 := bstep (se 1 (by rfl) ⟨864023, by rfl⟩ : syracuseStep 1152031 = 1728047) B1728047
theorem B2332793 : Blo 1148636 2332793 := bstep (se 2 (by rfl) ⟨874797, by rfl⟩ : syracuseStep 2332793 = 1749595) B1749595
theorem B44867297 : Blo 1148636 44867297 := bstep (se 2 (by rfl) ⟨16825236, by rfl⟩ : syracuseStep 44867297 = 33650473) B33650473
theorem B3680311 : Blo 1148636 3680311 := bstep (se 1 (by rfl) ⟨2760233, by rfl⟩ : syracuseStep 3680311 = 5520467) B5520467
theorem B3680927 : Blo 1148636 3680927 := bstep (se 1 (by rfl) ⟨2760695, by rfl⟩ : syracuseStep 3680927 = 5521391) B5521391
theorem B1454107 : Blo 1148636 1454107 := bstep (se 1 (by rfl) ⟨1090580, by rfl⟩ : syracuseStep 1454107 = 2181161) B2181161
theorem B18690223 : Blo 1148636 18690223 := bstep (se 1 (by rfl) ⟨14017667, by rfl⟩ : syracuseStep 18690223 = 28035335) B28035335
theorem B4372163 : Blo 1148636 4372163 := bstep (se 1 (by rfl) ⟨3279122, by rfl⟩ : syracuseStep 4372163 = 6558245) B6558245
theorem B13121999 : Blo 1148636 13121999 := bstep (se 1 (by rfl) ⟨9841499, by rfl⟩ : syracuseStep 13121999 = 19682999) B19682999
theorem B3883247 : Blo 1148636 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B50450797 : Blo 1148636 50450797 := bstep (se 3 (by rfl) ⟨9459524, by rfl⟩ : syracuseStep 50450797 = 18919049) B18919049
theorem B1724927 : Blo 1148636 1724927 := bstep (se 1 (by rfl) ⟨1293695, by rfl⟩ : syracuseStep 1724927 = 2587391) B2587391
theorem B3888431 : Blo 1148636 3888431 := bstep (se 1 (by rfl) ⟨2916323, by rfl⟩ : syracuseStep 3888431 = 5832647) B5832647
theorem B44817407 : Blo 1148636 44817407 := bstep (se 1 (by rfl) ⟨33613055, by rfl⟩ : syracuseStep 44817407 = 67226111) B67226111
theorem B17947975 : Blo 1148636 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B9331357 : Blo 1148636 9331357 := bstep (se 3 (by rfl) ⟨1749629, by rfl⟩ : syracuseStep 9331357 = 3499259) B3499259
theorem B7367593 : Blo 1148636 7367593 := bstep (se 2 (by rfl) ⟨2762847, by rfl⟩ : syracuseStep 7367593 = 5525695) B5525695
theorem B9826055 : Blo 1148636 9826055 := bstep (se 1 (by rfl) ⟨7369541, by rfl⟩ : syracuseStep 9826055 = 14739083) B14739083
theorem B13266767 : Blo 1148636 13266767 := bstep (se 1 (by rfl) ⟨9950075, by rfl⟩ : syracuseStep 13266767 = 19900151) B19900151
theorem B2584511 : Blo 1148636 2584511 := bstep (se 1 (by rfl) ⟨1938383, by rfl⟩ : syracuseStep 2584511 = 3876767) B3876767
theorem B3275147 : Blo 1148636 3275147 := bstep (se 1 (by rfl) ⟨2456360, by rfl⟩ : syracuseStep 3275147 = 4912721) B4912721
theorem B2588327 : Blo 1148636 2588327 := bstep (se 1 (by rfl) ⟨1941245, by rfl⟩ : syracuseStep 2588327 = 3882491) B3882491
theorem B2916121 : Blo 1148636 2916121 := bstep (se 2 (by rfl) ⟨1093545, by rfl⟩ : syracuseStep 2916121 = 2187091) B2187091
theorem B2588831 : Blo 1148636 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B22414319 : Blo 1148636 22414319 := bstep (se 1 (by rfl) ⟨16810739, by rfl⟩ : syracuseStep 22414319 = 33621479) B33621479
theorem B1149951 : Blo 1148636 1149951 := bstep (se 1 (by rfl) ⟨862463, by rfl⟩ : syracuseStep 1149951 = 1724927) B1724927
theorem B2592287 : Blo 1148636 2592287 := bstep (se 1 (by rfl) ⟨1944215, by rfl⟩ : syracuseStep 2592287 = 3888431) B3888431
theorem B1938809 : Blo 1148636 1938809 := bstep (se 2 (by rfl) ⟨727053, by rfl⟩ : syracuseStep 1938809 = 1454107) B1454107
theorem B23930633 : Blo 1148636 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B41987483 : Blo 1148636 41987483 := bstep (se 1 (by rfl) ⟨31490612, by rfl⟩ : syracuseStep 41987483 = 62981225) B62981225
theorem B1292287 : Blo 1148636 1292287 := bstep (se 1 (by rfl) ⟨969215, by rfl⟩ : syracuseStep 1292287 = 1938431) B1938431
theorem B1555195 : Blo 1148636 1555195 := bstep (se 1 (by rfl) ⟨1166396, by rfl⟩ : syracuseStep 1555195 = 2332793) B2332793
theorem B24920297 : Blo 1148636 24920297 := bstep (se 2 (by rfl) ⟨9345111, by rfl⟩ : syracuseStep 24920297 = 18690223) B18690223
theorem B1723007 : Blo 1148636 1723007 := bstep (se 1 (by rfl) ⟨1292255, by rfl⟩ : syracuseStep 1723007 = 2584511) B2584511
theorem B2183431 : Blo 1148636 2183431 := bstep (se 1 (by rfl) ⟨1637573, by rfl⟩ : syracuseStep 2183431 = 3275147) B3275147
theorem B3888161 : Blo 1148636 3888161 := bstep (se 2 (by rfl) ⟨1458060, by rfl⟩ : syracuseStep 3888161 = 2916121) B2916121
theorem B1725551 : Blo 1148636 1725551 := bstep (se 1 (by rfl) ⟨1294163, by rfl⟩ : syracuseStep 1725551 = 2588327) B2588327
theorem B1726571 : Blo 1148636 1726571 := bstep (se 1 (by rfl) ⟨1294928, by rfl⟩ : syracuseStep 1726571 = 2589857) B2589857
theorem B12441809 : Blo 1148636 12441809 := bstep (se 2 (by rfl) ⟨4665678, by rfl⟩ : syracuseStep 12441809 = 9331357) B9331357
theorem B2185535 : Blo 1148636 2185535 := bstep (se 1 (by rfl) ⟨1639151, by rfl⟩ : syracuseStep 2185535 = 3278303) B3278303
theorem B1727183 : Blo 1148636 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B28008089 : Blo 1148636 28008089 := bstep (se 2 (by rfl) ⟨10503033, by rfl⟩ : syracuseStep 28008089 = 21006067) B21006067
theorem B4907081 : Blo 1148636 4907081 := bstep (se 2 (by rfl) ⟨1840155, by rfl⟩ : syracuseStep 4907081 = 3680311) B3680311
theorem B262497257 : Blo 1148636 262497257 := bstep (se 2 (by rfl) ⟨98436471, by rfl⟩ : syracuseStep 262497257 = 196872943) B196872943
theorem B9823457 : Blo 1148636 9823457 := bstep (se 2 (by rfl) ⟨3683796, by rfl⟩ : syracuseStep 9823457 = 7367593) B7367593
theorem B29878271 : Blo 1148636 29878271 := bstep (se 1 (by rfl) ⟨22408703, by rfl⟩ : syracuseStep 29878271 = 44817407) B44817407
theorem B29911531 : Blo 1148636 29911531 := bstep (se 1 (by rfl) ⟨22433648, by rfl⟩ : syracuseStep 29911531 = 44867297) B44867297
theorem B2845313 : Blo 1148636 2845313 := bstep (se 2 (by rfl) ⟨1066992, by rfl⟩ : syracuseStep 2845313 = 2133985) B2133985
theorem B67267729 : Blo 1148636 67267729 := bstep (se 2 (by rfl) ⟨25225398, by rfl⟩ : syracuseStep 67267729 = 50450797) B50450797
theorem B2453951 : Blo 1148636 2453951 := bstep (se 1 (by rfl) ⟨1840463, by rfl⟩ : syracuseStep 2453951 = 3680927) B3680927
theorem B6550703 : Blo 1148636 6550703 := bstep (se 1 (by rfl) ⟨4913027, by rfl⟩ : syracuseStep 6550703 = 9826055) B9826055
theorem B8844511 : Blo 1148636 8844511 := bstep (se 1 (by rfl) ⟨6633383, by rfl⟩ : syracuseStep 8844511 = 13266767) B13266767
theorem B2914775 : Blo 1148636 2914775 := bstep (se 1 (by rfl) ⟨2186081, by rfl⟩ : syracuseStep 2914775 = 4372163) B4372163
theorem B8747999 : Blo 1148636 8747999 := bstep (se 1 (by rfl) ⟨6560999, by rfl⟩ : syracuseStep 8747999 = 13121999) B13121999
theorem B16613531 : Blo 1148636 16613531 := bstep (se 1 (by rfl) ⟨12460148, by rfl⟩ : syracuseStep 16613531 = 24920297) B24920297
theorem B14942879 : Blo 1148636 14942879 := bstep (se 1 (by rfl) ⟨11207159, by rfl⟩ : syracuseStep 14942879 = 22414319) B22414319
theorem B1148671 : Blo 1148636 1148671 := bstep (se 1 (by rfl) ⟨861503, by rfl⟩ : syracuseStep 1148671 = 1723007) B1723007
theorem B39882041 : Blo 1148636 39882041 := bstep (se 2 (by rfl) ⟨14955765, by rfl⟩ : syracuseStep 39882041 = 29911531) B29911531
theorem B2592107 : Blo 1148636 2592107 := bstep (se 1 (by rfl) ⟨1944080, by rfl⟩ : syracuseStep 2592107 = 3888161) B3888161
theorem B1150367 : Blo 1148636 1150367 := bstep (se 1 (by rfl) ⟨862775, by rfl⟩ : syracuseStep 1150367 = 1725551) B1725551
theorem B1151047 : Blo 1148636 1151047 := bstep (se 1 (by rfl) ⟨863285, by rfl⟩ : syracuseStep 1151047 = 1726571) B1726571
theorem B1151455 : Blo 1148636 1151455 := bstep (se 1 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 1151455 = 1727183) B1727183
theorem B27991655 : Blo 1148636 27991655 := bstep (se 1 (by rfl) ⟨20993741, by rfl⟩ : syracuseStep 27991655 = 41987483) B41987483
theorem B4367135 : Blo 1148636 4367135 := bstep (se 1 (by rfl) ⟨3275351, by rfl⟩ : syracuseStep 4367135 = 6550703) B6550703
theorem B2073593 : Blo 1148636 2073593 := bstep (se 2 (by rfl) ⟨777597, by rfl⟩ : syracuseStep 2073593 = 1555195) B1555195
theorem B1943183 : Blo 1148636 1943183 := bstep (se 1 (by rfl) ⟨1457387, by rfl⟩ : syracuseStep 1943183 = 2914775) B2914775
theorem B13085549 : Blo 1148636 13085549 := bstep (se 3 (by rfl) ⟨2453540, by rfl⟩ : syracuseStep 13085549 = 4907081) B4907081
theorem B1292539 : Blo 1148636 1292539 := bstep (se 1 (by rfl) ⟨969404, by rfl⟩ : syracuseStep 1292539 = 1938809) B1938809
theorem B1457023 : Blo 1148636 1457023 := bstep (se 1 (by rfl) ⟨1092767, by rfl⟩ : syracuseStep 1457023 = 2185535) B2185535
theorem B33178157 : Blo 1148636 33178157 := bstep (se 3 (by rfl) ⟨6220904, by rfl⟩ : syracuseStep 33178157 = 12441809) B12441809
theorem B174998171 : Blo 1148636 174998171 := bstep (se 1 (by rfl) ⟨131248628, by rfl⟩ : syracuseStep 174998171 = 262497257) B262497257
theorem B358761221 : Blo 1148636 358761221 := bstep (se 4 (by rfl) ⟨33633864, by rfl⟩ : syracuseStep 358761221 = 67267729) B67267729
theorem B1723049 : Blo 1148636 1723049 := bstep (se 2 (by rfl) ⟨646143, by rfl⟩ : syracuseStep 1723049 = 1292287) B1292287
theorem B1725887 : Blo 1148636 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B1728191 : Blo 1148636 1728191 := bstep (se 1 (by rfl) ⟨1296143, by rfl⟩ : syracuseStep 1728191 = 2592287) B2592287
theorem B18672059 : Blo 1148636 18672059 := bstep (se 1 (by rfl) ⟨14004044, by rfl⟩ : syracuseStep 18672059 = 28008089) B28008089
theorem B2911241 : Blo 1148636 2911241 := bstep (se 2 (by rfl) ⟨1091715, by rfl⟩ : syracuseStep 2911241 = 2183431) B2183431
theorem B6548971 : Blo 1148636 6548971 := bstep (se 1 (by rfl) ⟨4911728, by rfl⟩ : syracuseStep 6548971 = 9823457) B9823457
theorem B15953755 : Blo 1148636 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B19918847 : Blo 1148636 19918847 := bstep (se 1 (by rfl) ⟨14939135, by rfl⟩ : syracuseStep 19918847 = 29878271) B29878271
theorem B11792681 : Blo 1148636 11792681 := bstep (se 2 (by rfl) ⟨4422255, by rfl⟩ : syracuseStep 11792681 = 8844511) B8844511
theorem B1896875 : Blo 1148636 1896875 := bstep (se 1 (by rfl) ⟨1422656, by rfl⟩ : syracuseStep 1896875 = 2845313) B2845313
theorem B1635967 : Blo 1148636 1635967 := bstep (se 1 (by rfl) ⟨1226975, by rfl⟩ : syracuseStep 1635967 = 2453951) B2453951
theorem B5831999 : Blo 1148636 5831999 := bstep (se 1 (by rfl) ⟨4373999, by rfl⟩ : syracuseStep 5831999 = 8747999) B8747999
theorem B11075687 : Blo 1148636 11075687 := bstep (se 1 (by rfl) ⟨8306765, by rfl⟩ : syracuseStep 11075687 = 16613531) B16613531
theorem B22118771 : Blo 1148636 22118771 := bstep (se 1 (by rfl) ⟨16589078, by rfl⟩ : syracuseStep 22118771 = 33178157) B33178157
theorem B9961919 : Blo 1148636 9961919 := bstep (se 1 (by rfl) ⟨7471439, by rfl⟩ : syracuseStep 9961919 = 14942879) B14942879
theorem B239174147 : Blo 1148636 239174147 := bstep (se 1 (by rfl) ⟨179380610, by rfl⟩ : syracuseStep 239174147 = 358761221) B358761221
theorem B1148699 : Blo 1148636 1148699 := bstep (se 1 (by rfl) ⟨861524, by rfl⟩ : syracuseStep 1148699 = 1723049) B1723049
theorem B1150591 : Blo 1148636 1150591 := bstep (se 1 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 1150591 = 1725887) B1725887
theorem B21271673 : Blo 1148636 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B1152127 : Blo 1148636 1152127 := bstep (se 1 (by rfl) ⟨864095, by rfl⟩ : syracuseStep 1152127 = 1728191) B1728191
theorem B1382395 : Blo 1148636 1382395 := bstep (se 1 (by rfl) ⟨1036796, by rfl⟩ : syracuseStep 1382395 = 2073593) B2073593
theorem B8723699 : Blo 1148636 8723699 := bstep (se 1 (by rfl) ⟨6542774, by rfl⟩ : syracuseStep 8723699 = 13085549) B13085549
theorem B1940827 : Blo 1148636 1940827 := bstep (se 1 (by rfl) ⟨1455620, by rfl⟩ : syracuseStep 1940827 = 2911241) B2911241
theorem B13279231 : Blo 1148636 13279231 := bstep (se 1 (by rfl) ⟨9959423, by rfl⟩ : syracuseStep 13279231 = 19918847) B19918847
theorem B8725157 : Blo 1148636 8725157 := bstep (se 4 (by rfl) ⟨817983, by rfl⟩ : syracuseStep 8725157 = 1635967) B1635967
theorem B1942697 : Blo 1148636 1942697 := bstep (se 2 (by rfl) ⟨728511, by rfl⟩ : syracuseStep 1942697 = 1457023) B1457023
theorem B116665447 : Blo 1148636 116665447 := bstep (se 1 (by rfl) ⟨87499085, by rfl⟩ : syracuseStep 116665447 = 174998171) B174998171
theorem B26588027 : Blo 1148636 26588027 := bstep (se 1 (by rfl) ⟨19941020, by rfl⟩ : syracuseStep 26588027 = 39882041) B39882041
theorem B8731961 : Blo 1148636 8731961 := bstep (se 2 (by rfl) ⟨3274485, by rfl⟩ : syracuseStep 8731961 = 6548971) B6548971
theorem B18661103 : Blo 1148636 18661103 := bstep (se 1 (by rfl) ⟨13995827, by rfl⟩ : syracuseStep 18661103 = 27991655) B27991655
theorem B1295455 : Blo 1148636 1295455 := bstep (se 1 (by rfl) ⟨971591, by rfl⟩ : syracuseStep 1295455 = 1943183) B1943183
theorem B1264583 : Blo 1148636 1264583 := bstep (se 1 (by rfl) ⟨948437, by rfl⟩ : syracuseStep 1264583 = 1896875) B1896875
theorem B1723385 : Blo 1148636 1723385 := bstep (se 2 (by rfl) ⟨646269, by rfl⟩ : syracuseStep 1723385 = 1292539) B1292539
theorem B3887999 : Blo 1148636 3887999 := bstep (se 1 (by rfl) ⟨2915999, by rfl⟩ : syracuseStep 3887999 = 5831999) B5831999
theorem B1728071 : Blo 1148636 1728071 := bstep (se 1 (by rfl) ⟨1296053, by rfl⟩ : syracuseStep 1728071 = 2592107) B2592107
theorem B2911423 : Blo 1148636 2911423 := bstep (se 1 (by rfl) ⟨2183567, by rfl⟩ : syracuseStep 2911423 = 4367135) B4367135
theorem B12448039 : Blo 1148636 12448039 := bstep (se 1 (by rfl) ⟨9336029, by rfl⟩ : syracuseStep 12448039 = 18672059) B18672059
theorem B7861787 : Blo 1148636 7861787 := bstep (se 1 (by rfl) ⟨5896340, by rfl⟩ : syracuseStep 7861787 = 11792681) B11792681
theorem B14745847 : Blo 1148636 14745847 := bstep (se 1 (by rfl) ⟨11059385, by rfl⟩ : syracuseStep 14745847 = 22118771) B22118771
theorem B159449431 : Blo 1148636 159449431 := bstep (se 1 (by rfl) ⟨119587073, by rfl⟩ : syracuseStep 159449431 = 239174147) B239174147
theorem B1148923 : Blo 1148636 1148923 := bstep (se 1 (by rfl) ⟨861692, by rfl⟩ : syracuseStep 1148923 = 1723385) B1723385
theorem B56724461 : Blo 1148636 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B2591999 : Blo 1148636 2591999 := bstep (se 1 (by rfl) ⟨1943999, by rfl⟩ : syracuseStep 2591999 = 3887999) B3887999
theorem B155553929 : Blo 1148636 155553929 := bstep (se 2 (by rfl) ⟨58332723, by rfl⟩ : syracuseStep 155553929 = 116665447) B116665447
theorem B1152047 : Blo 1148636 1152047 := bstep (se 1 (by rfl) ⟨864035, by rfl⟩ : syracuseStep 1152047 = 1728071) B1728071
theorem B1843193 : Blo 1148636 1843193 := bstep (se 2 (by rfl) ⟨691197, by rfl⟩ : syracuseStep 1843193 = 1382395) B1382395
theorem B17705641 : Blo 1148636 17705641 := bstep (se 2 (by rfl) ⟨6639615, by rfl⟩ : syracuseStep 17705641 = 13279231) B13279231
theorem B7383791 : Blo 1148636 7383791 := bstep (se 1 (by rfl) ⟨5537843, by rfl⟩ : syracuseStep 7383791 = 11075687) B11075687
theorem B3881897 : Blo 1148636 3881897 := bstep (se 2 (by rfl) ⟨1455711, by rfl⟩ : syracuseStep 3881897 = 2911423) B2911423
theorem B5815799 : Blo 1148636 5815799 := bstep (se 1 (by rfl) ⟨4361849, by rfl⟩ : syracuseStep 5815799 = 8723699) B8723699
theorem B16597385 : Blo 1148636 16597385 := bstep (se 2 (by rfl) ⟨6224019, by rfl⟩ : syracuseStep 16597385 = 12448039) B12448039
theorem B5816771 : Blo 1148636 5816771 := bstep (se 1 (by rfl) ⟨4362578, by rfl⟩ : syracuseStep 5816771 = 8725157) B8725157
theorem B1295131 : Blo 1148636 1295131 := bstep (se 1 (by rfl) ⟨971348, by rfl⟩ : syracuseStep 1295131 = 1942697) B1942697
theorem B5821307 : Blo 1148636 5821307 := bstep (se 1 (by rfl) ⟨4365980, by rfl⟩ : syracuseStep 5821307 = 8731961) B8731961
theorem B12440735 : Blo 1148636 12440735 := bstep (se 1 (by rfl) ⟨9330551, by rfl⟩ : syracuseStep 12440735 = 18661103) B18661103
theorem B6641279 : Blo 1148636 6641279 := bstep (se 1 (by rfl) ⟨4980959, by rfl⟩ : syracuseStep 6641279 = 9961919) B9961919
theorem B1727273 : Blo 1148636 1727273 := bstep (se 2 (by rfl) ⟨647727, by rfl⟩ : syracuseStep 1727273 = 1295455) B1295455
theorem B3372221 : Blo 1148636 3372221 := bstep (se 3 (by rfl) ⟨632291, by rfl⟩ : syracuseStep 3372221 = 1264583) B1264583
theorem B17725351 : Blo 1148636 17725351 := bstep (se 1 (by rfl) ⟨13294013, by rfl⟩ : syracuseStep 17725351 = 26588027) B26588027
theorem B5241191 : Blo 1148636 5241191 := bstep (se 1 (by rfl) ⟨3930893, by rfl⟩ : syracuseStep 5241191 = 7861787) B7861787
theorem B2587769 : Blo 1148636 2587769 := bstep (se 2 (by rfl) ⟨970413, by rfl⟩ : syracuseStep 2587769 = 1940827) B1940827
theorem B19661129 : Blo 1148636 19661129 := bstep (se 2 (by rfl) ⟨7372923, by rfl⟩ : syracuseStep 19661129 = 14745847) B14745847
theorem B212599241 : Blo 1148636 212599241 := bstep (se 2 (by rfl) ⟨79724715, by rfl⟩ : syracuseStep 212599241 = 159449431) B159449431
theorem B37816307 : Blo 1148636 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B8293823 : Blo 1148636 8293823 := bstep (se 1 (by rfl) ⟨6220367, by rfl⟩ : syracuseStep 8293823 = 12440735) B12440735
theorem B4427519 : Blo 1148636 4427519 := bstep (se 1 (by rfl) ⟨3320639, by rfl⟩ : syracuseStep 4427519 = 6641279) B6641279
theorem B1151515 : Blo 1148636 1151515 := bstep (se 1 (by rfl) ⟨863636, by rfl⟩ : syracuseStep 1151515 = 1727273) B1727273
theorem B4922527 : Blo 1148636 4922527 := bstep (se 1 (by rfl) ⟨3691895, by rfl⟩ : syracuseStep 4922527 = 7383791) B7383791
theorem B23633801 : Blo 1148636 23633801 := bstep (se 2 (by rfl) ⟨8862675, by rfl⟩ : syracuseStep 23633801 = 17725351) B17725351
theorem B3877199 : Blo 1148636 3877199 := bstep (se 1 (by rfl) ⟨2907899, by rfl⟩ : syracuseStep 3877199 = 5815799) B5815799
theorem B3877847 : Blo 1148636 3877847 := bstep (se 1 (by rfl) ⟨2908385, by rfl⟩ : syracuseStep 3877847 = 5816771) B5816771
theorem B8992589 : Blo 1148636 8992589 := bstep (se 3 (by rfl) ⟨1686110, by rfl⟩ : syracuseStep 8992589 = 3372221) B3372221
theorem B3880871 : Blo 1148636 3880871 := bstep (se 1 (by rfl) ⟨2910653, by rfl⟩ : syracuseStep 3880871 = 5821307) B5821307
theorem B23607521 : Blo 1148636 23607521 := bstep (se 2 (by rfl) ⟨8852820, by rfl⟩ : syracuseStep 23607521 = 17705641) B17705641
theorem B13976509 : Blo 1148636 13976509 := bstep (se 3 (by rfl) ⟨2620595, by rfl⟩ : syracuseStep 13976509 = 5241191) B5241191
theorem B1725179 : Blo 1148636 1725179 := bstep (se 1 (by rfl) ⟨1293884, by rfl⟩ : syracuseStep 1725179 = 2587769) B2587769
theorem B11064923 : Blo 1148636 11064923 := bstep (se 1 (by rfl) ⟨8298692, by rfl⟩ : syracuseStep 11064923 = 16597385) B16597385
theorem B1726841 : Blo 1148636 1726841 := bstep (se 2 (by rfl) ⟨647565, by rfl⟩ : syracuseStep 1726841 = 1295131) B1295131
theorem B1727999 : Blo 1148636 1727999 := bstep (se 1 (by rfl) ⟨1295999, by rfl⟩ : syracuseStep 1727999 = 2591999) B2591999
theorem B103702619 : Blo 1148636 103702619 := bstep (se 1 (by rfl) ⟨77776964, by rfl⟩ : syracuseStep 103702619 = 155553929) B155553929
theorem B2587931 : Blo 1148636 2587931 := bstep (se 1 (by rfl) ⟨1940948, by rfl⟩ : syracuseStep 2587931 = 3881897) B3881897
theorem B4915181 : Blo 1148636 4915181 := bstep (se 3 (by rfl) ⟨921596, by rfl⟩ : syracuseStep 4915181 = 1843193) B1843193
theorem B13107419 : Blo 1148636 13107419 := bstep (se 1 (by rfl) ⟨9830564, by rfl⟩ : syracuseStep 13107419 = 19661129) B19661129
theorem B1150119 : Blo 1148636 1150119 := bstep (se 1 (by rfl) ⟨862589, by rfl⟩ : syracuseStep 1150119 = 1725179) B1725179
theorem B7376615 : Blo 1148636 7376615 := bstep (se 1 (by rfl) ⟨5532461, by rfl⟩ : syracuseStep 7376615 = 11064923) B11064923
theorem B1151227 : Blo 1148636 1151227 := bstep (se 1 (by rfl) ⟨863420, by rfl⟩ : syracuseStep 1151227 = 1726841) B1726841
theorem B1151999 : Blo 1148636 1151999 := bstep (se 1 (by rfl) ⟨863999, by rfl⟩ : syracuseStep 1151999 = 1727999) B1727999
theorem B95920949 : Blo 1148636 95920949 := bstep (se 5 (by rfl) ⟨4496294, by rfl⟩ : syracuseStep 95920949 = 8992589) B8992589
theorem B15738347 : Blo 1148636 15738347 := bstep (se 1 (by rfl) ⟨11803760, by rfl⟩ : syracuseStep 15738347 = 23607521) B23607521
theorem B6563369 : Blo 1148636 6563369 := bstep (se 2 (by rfl) ⟨2461263, by rfl⟩ : syracuseStep 6563369 = 4922527) B4922527
theorem B11806717 : Blo 1148636 11806717 := bstep (se 3 (by rfl) ⟨2213759, by rfl⟩ : syracuseStep 11806717 = 4427519) B4427519
theorem B141732827 : Blo 1148636 141732827 := bstep (se 1 (by rfl) ⟨106299620, by rfl⟩ : syracuseStep 141732827 = 212599241) B212599241
theorem B25210871 : Blo 1148636 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B1725287 : Blo 1148636 1725287 := bstep (se 1 (by rfl) ⟨1293965, by rfl⟩ : syracuseStep 1725287 = 2587931) B2587931
theorem B18635345 : Blo 1148636 18635345 := bstep (se 2 (by rfl) ⟨6988254, by rfl⟩ : syracuseStep 18635345 = 13976509) B13976509
theorem B5529215 : Blo 1148636 5529215 := bstep (se 1 (by rfl) ⟨4146911, by rfl⟩ : syracuseStep 5529215 = 8293823) B8293823
theorem B15755867 : Blo 1148636 15755867 := bstep (se 1 (by rfl) ⟨11816900, by rfl⟩ : syracuseStep 15755867 = 23633801) B23633801
theorem B69135079 : Blo 1148636 69135079 := bstep (se 1 (by rfl) ⟨51851309, by rfl⟩ : syracuseStep 69135079 = 103702619) B103702619
theorem B2584799 : Blo 1148636 2584799 := bstep (se 1 (by rfl) ⟨1938599, by rfl⟩ : syracuseStep 2584799 = 3877199) B3877199
theorem B2585231 : Blo 1148636 2585231 := bstep (se 1 (by rfl) ⟨1938923, by rfl⟩ : syracuseStep 2585231 = 3877847) B3877847
theorem B2587247 : Blo 1148636 2587247 := bstep (se 1 (by rfl) ⟨1940435, by rfl⟩ : syracuseStep 2587247 = 3880871) B3880871
theorem B3276787 : Blo 1148636 3276787 := bstep (se 1 (by rfl) ⟨2457590, by rfl⟩ : syracuseStep 3276787 = 4915181) B4915181
theorem B255789197 : Blo 1148636 255789197 := bstep (se 3 (by rfl) ⟨47960474, by rfl⟩ : syracuseStep 255789197 = 95920949) B95920949
theorem B4917743 : Blo 1148636 4917743 := bstep (se 1 (by rfl) ⟨3688307, by rfl⟩ : syracuseStep 4917743 = 7376615) B7376615
theorem B1150191 : Blo 1148636 1150191 := bstep (se 1 (by rfl) ⟨862643, by rfl⟩ : syracuseStep 1150191 = 1725287) B1725287
theorem B92180105 : Blo 1148636 92180105 := bstep (se 2 (by rfl) ⟨34567539, by rfl⟩ : syracuseStep 92180105 = 69135079) B69135079
theorem B12423563 : Blo 1148636 12423563 := bstep (se 1 (by rfl) ⟨9317672, by rfl⟩ : syracuseStep 12423563 = 18635345) B18635345
theorem B4369049 : Blo 1148636 4369049 := bstep (se 2 (by rfl) ⟨1638393, by rfl⟩ : syracuseStep 4369049 = 3276787) B3276787
theorem B15742289 : Blo 1148636 15742289 := bstep (se 2 (by rfl) ⟨5903358, by rfl⟩ : syracuseStep 15742289 = 11806717) B11806717
theorem B3686143 : Blo 1148636 3686143 := bstep (se 1 (by rfl) ⟨2764607, by rfl⟩ : syracuseStep 3686143 = 5529215) B5529215
theorem B4375579 : Blo 1148636 4375579 := bstep (se 1 (by rfl) ⟨3281684, by rfl⟩ : syracuseStep 4375579 = 6563369) B6563369
theorem B10503911 : Blo 1148636 10503911 := bstep (se 1 (by rfl) ⟨7877933, by rfl⟩ : syracuseStep 10503911 = 15755867) B15755867
theorem B94488551 : Blo 1148636 94488551 := bstep (se 1 (by rfl) ⟨70866413, by rfl⟩ : syracuseStep 94488551 = 141732827) B141732827
theorem B1723199 : Blo 1148636 1723199 := bstep (se 1 (by rfl) ⟨1292399, by rfl⟩ : syracuseStep 1723199 = 2584799) B2584799
theorem B1723487 : Blo 1148636 1723487 := bstep (se 1 (by rfl) ⟨1292615, by rfl⟩ : syracuseStep 1723487 = 2585231) B2585231
theorem B1724831 : Blo 1148636 1724831 := bstep (se 1 (by rfl) ⟨1293623, by rfl⟩ : syracuseStep 1724831 = 2587247) B2587247
theorem B8738279 : Blo 1148636 8738279 := bstep (se 1 (by rfl) ⟨6553709, by rfl⟩ : syracuseStep 8738279 = 13107419) B13107419
theorem B41968925 : Blo 1148636 41968925 := bstep (se 3 (by rfl) ⟨7869173, by rfl⟩ : syracuseStep 41968925 = 15738347) B15738347
theorem B16807247 : Blo 1148636 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B5834105 : Blo 1148636 5834105 := bstep (se 2 (by rfl) ⟨2187789, by rfl⟩ : syracuseStep 5834105 = 4375579) B4375579
theorem B170526131 : Blo 1148636 170526131 := bstep (se 1 (by rfl) ⟨127894598, by rfl⟩ : syracuseStep 170526131 = 255789197) B255789197
theorem B3278495 : Blo 1148636 3278495 := bstep (se 1 (by rfl) ⟨2458871, by rfl⟩ : syracuseStep 3278495 = 4917743) B4917743
theorem B1148799 : Blo 1148636 1148799 := bstep (se 1 (by rfl) ⟨861599, by rfl⟩ : syracuseStep 1148799 = 1723199) B1723199
theorem B1148991 : Blo 1148636 1148991 := bstep (se 1 (by rfl) ⟨861743, by rfl⟩ : syracuseStep 1148991 = 1723487) B1723487
theorem B1149887 : Blo 1148636 1149887 := bstep (se 1 (by rfl) ⟨862415, by rfl⟩ : syracuseStep 1149887 = 1724831) B1724831
theorem B10494859 : Blo 1148636 10494859 := bstep (se 1 (by rfl) ⟨7871144, by rfl⟩ : syracuseStep 10494859 = 15742289) B15742289
theorem B62992367 : Blo 1148636 62992367 := bstep (se 1 (by rfl) ⟨47244275, by rfl⟩ : syracuseStep 62992367 = 94488551) B94488551
theorem B61453403 : Blo 1148636 61453403 := bstep (se 1 (by rfl) ⟨46090052, by rfl⟩ : syracuseStep 61453403 = 92180105) B92180105
theorem B7002607 : Blo 1148636 7002607 := bstep (se 1 (by rfl) ⟨5251955, by rfl⟩ : syracuseStep 7002607 = 10503911) B10503911
theorem B8282375 : Blo 1148636 8282375 := bstep (se 1 (by rfl) ⟨6211781, by rfl⟩ : syracuseStep 8282375 = 12423563) B12423563
theorem B5825519 : Blo 1148636 5825519 := bstep (se 1 (by rfl) ⟨4369139, by rfl⟩ : syracuseStep 5825519 = 8738279) B8738279
theorem B27979283 : Blo 1148636 27979283 := bstep (se 1 (by rfl) ⟨20984462, by rfl⟩ : syracuseStep 27979283 = 41968925) B41968925
theorem B2912699 : Blo 1148636 2912699 := bstep (se 1 (by rfl) ⟨2184524, by rfl⟩ : syracuseStep 2912699 = 4369049) B4369049
theorem B11204831 : Blo 1148636 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B4914857 : Blo 1148636 4914857 := bstep (se 2 (by rfl) ⟨1843071, by rfl⟩ : syracuseStep 4914857 = 3686143) B3686143
theorem B13993145 : Blo 1148636 13993145 := bstep (se 2 (by rfl) ⟨5247429, by rfl⟩ : syracuseStep 13993145 = 10494859) B10494859
theorem B18652855 : Blo 1148636 18652855 := bstep (se 1 (by rfl) ⟨13989641, by rfl⟩ : syracuseStep 18652855 = 27979283) B27979283
theorem B1941799 : Blo 1148636 1941799 := bstep (se 1 (by rfl) ⟨1456349, by rfl⟩ : syracuseStep 1941799 = 2912699) B2912699
theorem B40968935 : Blo 1148636 40968935 := bstep (se 1 (by rfl) ⟨30726701, by rfl⟩ : syracuseStep 40968935 = 61453403) B61453403
theorem B113684087 : Blo 1148636 113684087 := bstep (se 1 (by rfl) ⟨85263065, by rfl⟩ : syracuseStep 113684087 = 170526131) B170526131
theorem B5521583 : Blo 1148636 5521583 := bstep (se 1 (by rfl) ⟨4141187, by rfl⟩ : syracuseStep 5521583 = 8282375) B8282375
theorem B3883679 : Blo 1148636 3883679 := bstep (se 1 (by rfl) ⟨2912759, by rfl⟩ : syracuseStep 3883679 = 5825519) B5825519
theorem B41994911 : Blo 1148636 41994911 := bstep (se 1 (by rfl) ⟨31496183, by rfl⟩ : syracuseStep 41994911 = 62992367) B62992367
theorem B3889403 : Blo 1148636 3889403 := bstep (se 1 (by rfl) ⟨2917052, by rfl⟩ : syracuseStep 3889403 = 5834105) B5834105
theorem B8742653 : Blo 1148636 8742653 := bstep (se 3 (by rfl) ⟨1639247, by rfl⟩ : syracuseStep 8742653 = 3278495) B3278495
theorem B9336809 : Blo 1148636 9336809 := bstep (se 2 (by rfl) ⟨3501303, by rfl⟩ : syracuseStep 9336809 = 7002607) B7002607
theorem B7469887 : Blo 1148636 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B3276571 : Blo 1148636 3276571 := bstep (se 1 (by rfl) ⟨2457428, by rfl⟩ : syracuseStep 3276571 = 4914857) B4914857
theorem B2589065 : Blo 1148636 2589065 := bstep (se 2 (by rfl) ⟨970899, by rfl⟩ : syracuseStep 2589065 = 1941799) B1941799
theorem B2589119 : Blo 1148636 2589119 := bstep (se 1 (by rfl) ⟨1941839, by rfl⟩ : syracuseStep 2589119 = 3883679) B3883679
theorem B2592935 : Blo 1148636 2592935 := bstep (se 1 (by rfl) ⟨1944701, by rfl⟩ : syracuseStep 2592935 = 3889403) B3889403
theorem B4368761 : Blo 1148636 4368761 := bstep (se 2 (by rfl) ⟨1638285, by rfl⟩ : syracuseStep 4368761 = 3276571) B3276571
theorem B3681055 : Blo 1148636 3681055 := bstep (se 1 (by rfl) ⟨2760791, by rfl⟩ : syracuseStep 3681055 = 5521583) B5521583
theorem B27996607 : Blo 1148636 27996607 := bstep (se 1 (by rfl) ⟨20997455, by rfl⟩ : syracuseStep 27996607 = 41994911) B41994911
theorem B27312623 : Blo 1148636 27312623 := bstep (se 1 (by rfl) ⟨20484467, by rfl⟩ : syracuseStep 27312623 = 40968935) B40968935
theorem B9328763 : Blo 1148636 9328763 := bstep (se 1 (by rfl) ⟨6996572, by rfl⟩ : syracuseStep 9328763 = 13993145) B13993145
theorem B5828435 : Blo 1148636 5828435 := bstep (se 1 (by rfl) ⟨4371326, by rfl⟩ : syracuseStep 5828435 = 8742653) B8742653
theorem B75789391 : Blo 1148636 75789391 := bstep (se 1 (by rfl) ⟨56842043, by rfl⟩ : syracuseStep 75789391 = 113684087) B113684087
theorem B9959849 : Blo 1148636 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B6224539 : Blo 1148636 6224539 := bstep (se 1 (by rfl) ⟨4668404, by rfl⟩ : syracuseStep 6224539 = 9336809) B9336809
theorem B24870473 : Blo 1148636 24870473 := bstep (se 2 (by rfl) ⟨9326427, by rfl⟩ : syracuseStep 24870473 = 18652855) B18652855
theorem B37328809 : Blo 1148636 37328809 := bstep (se 2 (by rfl) ⟨13998303, by rfl⟩ : syracuseStep 37328809 = 27996607) B27996607
theorem B8299385 : Blo 1148636 8299385 := bstep (se 2 (by rfl) ⟨3112269, by rfl⟩ : syracuseStep 8299385 = 6224539) B6224539
theorem B3885623 : Blo 1148636 3885623 := bstep (se 1 (by rfl) ⟨2914217, by rfl⟩ : syracuseStep 3885623 = 5828435) B5828435
theorem B6639899 : Blo 1148636 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B1726043 : Blo 1148636 1726043 := bstep (se 1 (by rfl) ⟨1294532, by rfl⟩ : syracuseStep 1726043 = 2589065) B2589065
theorem B1726079 : Blo 1148636 1726079 := bstep (se 1 (by rfl) ⟨1294559, by rfl⟩ : syracuseStep 1726079 = 2589119) B2589119
theorem B18208415 : Blo 1148636 18208415 := bstep (se 1 (by rfl) ⟨13656311, by rfl⟩ : syracuseStep 18208415 = 27312623) B27312623
theorem B1728623 : Blo 1148636 1728623 := bstep (se 1 (by rfl) ⟨1296467, by rfl⟩ : syracuseStep 1728623 = 2592935) B2592935
theorem B4908073 : Blo 1148636 4908073 := bstep (se 2 (by rfl) ⟨1840527, by rfl⟩ : syracuseStep 4908073 = 3681055) B3681055
theorem B6219175 : Blo 1148636 6219175 := bstep (se 1 (by rfl) ⟨4664381, by rfl⟩ : syracuseStep 6219175 = 9328763) B9328763
theorem B101052521 : Blo 1148636 101052521 := bstep (se 2 (by rfl) ⟨37894695, by rfl⟩ : syracuseStep 101052521 = 75789391) B75789391
theorem B2912507 : Blo 1148636 2912507 := bstep (se 1 (by rfl) ⟨2184380, by rfl⟩ : syracuseStep 2912507 = 4368761) B4368761
theorem B16580315 : Blo 1148636 16580315 := bstep (se 1 (by rfl) ⟨12435236, by rfl⟩ : syracuseStep 16580315 = 24870473) B24870473
theorem B2590415 : Blo 1148636 2590415 := bstep (se 1 (by rfl) ⟨1942811, by rfl⟩ : syracuseStep 2590415 = 3885623) B3885623
theorem B8292233 : Blo 1148636 8292233 := bstep (se 2 (by rfl) ⟨3109587, by rfl⟩ : syracuseStep 8292233 = 6219175) B6219175
theorem B1150695 : Blo 1148636 1150695 := bstep (se 1 (by rfl) ⟨863021, by rfl⟩ : syracuseStep 1150695 = 1726043) B1726043
theorem B1150719 : Blo 1148636 1150719 := bstep (se 1 (by rfl) ⟨863039, by rfl⟩ : syracuseStep 1150719 = 1726079) B1726079
theorem B1152415 : Blo 1148636 1152415 := bstep (se 1 (by rfl) ⟨864311, by rfl⟩ : syracuseStep 1152415 = 1728623) B1728623
theorem B1941671 : Blo 1148636 1941671 := bstep (se 1 (by rfl) ⟨1456253, by rfl⟩ : syracuseStep 1941671 = 2912507) B2912507
theorem B11053543 : Blo 1148636 11053543 := bstep (se 1 (by rfl) ⟨8290157, by rfl⟩ : syracuseStep 11053543 = 16580315) B16580315
theorem B17706397 : Blo 1148636 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B12138943 : Blo 1148636 12138943 := bstep (se 1 (by rfl) ⟨9104207, by rfl⟩ : syracuseStep 12138943 = 18208415) B18208415
theorem B6544097 : Blo 1148636 6544097 := bstep (se 2 (by rfl) ⟨2454036, by rfl⟩ : syracuseStep 6544097 = 4908073) B4908073
theorem B5532923 : Blo 1148636 5532923 := bstep (se 1 (by rfl) ⟨4149692, by rfl⟩ : syracuseStep 5532923 = 8299385) B8299385
theorem B49771745 : Blo 1148636 49771745 := bstep (se 2 (by rfl) ⟨18664404, by rfl⟩ : syracuseStep 49771745 = 37328809) B37328809
theorem B67368347 : Blo 1148636 67368347 := bstep (se 1 (by rfl) ⟨50526260, by rfl⟩ : syracuseStep 67368347 = 101052521) B101052521
theorem B4362731 : Blo 1148636 4362731 := bstep (se 1 (by rfl) ⟨3272048, by rfl⟩ : syracuseStep 4362731 = 6544097) B6544097
theorem B23608529 : Blo 1148636 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B1294447 : Blo 1148636 1294447 := bstep (se 1 (by rfl) ⟨970835, by rfl⟩ : syracuseStep 1294447 = 1941671) B1941671
theorem B3688615 : Blo 1148636 3688615 := bstep (se 1 (by rfl) ⟨2766461, by rfl⟩ : syracuseStep 3688615 = 5532923) B5532923
theorem B33181163 : Blo 1148636 33181163 := bstep (se 1 (by rfl) ⟨24885872, by rfl⟩ : syracuseStep 33181163 = 49771745) B49771745
theorem B44912231 : Blo 1148636 44912231 := bstep (se 1 (by rfl) ⟨33684173, by rfl⟩ : syracuseStep 44912231 = 67368347) B67368347
theorem B1726943 : Blo 1148636 1726943 := bstep (se 1 (by rfl) ⟨1295207, by rfl⟩ : syracuseStep 1726943 = 2590415) B2590415
theorem B14738057 : Blo 1148636 14738057 := bstep (se 2 (by rfl) ⟨5526771, by rfl⟩ : syracuseStep 14738057 = 11053543) B11053543
theorem B22112621 : Blo 1148636 22112621 := bstep (se 3 (by rfl) ⟨4146116, by rfl⟩ : syracuseStep 22112621 = 8292233) B8292233
theorem B16185257 : Blo 1148636 16185257 := bstep (se 2 (by rfl) ⟨6069471, by rfl⟩ : syracuseStep 16185257 = 12138943) B12138943
theorem B22120775 : Blo 1148636 22120775 := bstep (se 1 (by rfl) ⟨16590581, by rfl⟩ : syracuseStep 22120775 = 33181163) B33181163
theorem B4918153 : Blo 1148636 4918153 := bstep (se 2 (by rfl) ⟨1844307, by rfl⟩ : syracuseStep 4918153 = 3688615) B3688615
theorem B1151295 : Blo 1148636 1151295 := bstep (se 1 (by rfl) ⟨863471, by rfl⟩ : syracuseStep 1151295 = 1726943) B1726943
theorem B10790171 : Blo 1148636 10790171 := bstep (se 1 (by rfl) ⟨8092628, by rfl⟩ : syracuseStep 10790171 = 16185257) B16185257
theorem B15739019 : Blo 1148636 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B1725929 : Blo 1148636 1725929 := bstep (se 2 (by rfl) ⟨647223, by rfl⟩ : syracuseStep 1725929 = 1294447) B1294447
theorem B29941487 : Blo 1148636 29941487 := bstep (se 1 (by rfl) ⟨22456115, by rfl⟩ : syracuseStep 29941487 = 44912231) B44912231
theorem B2908487 : Blo 1148636 2908487 := bstep (se 1 (by rfl) ⟨2181365, by rfl⟩ : syracuseStep 2908487 = 4362731) B4362731
theorem B9825371 : Blo 1148636 9825371 := bstep (se 1 (by rfl) ⟨7369028, by rfl⟩ : syracuseStep 9825371 = 14738057) B14738057
theorem B14741747 : Blo 1148636 14741747 := bstep (se 1 (by rfl) ⟨11056310, by rfl⟩ : syracuseStep 14741747 = 22112621) B22112621
theorem B14747183 : Blo 1148636 14747183 := bstep (se 1 (by rfl) ⟨11060387, by rfl⟩ : syracuseStep 14747183 = 22120775) B22120775
theorem B1150619 : Blo 1148636 1150619 := bstep (se 1 (by rfl) ⟨862964, by rfl⟩ : syracuseStep 1150619 = 1725929) B1725929
theorem B6557537 : Blo 1148636 6557537 := bstep (se 2 (by rfl) ⟨2459076, by rfl⟩ : syracuseStep 6557537 = 4918153) B4918153
theorem B19960991 : Blo 1148636 19960991 := bstep (se 1 (by rfl) ⟨14970743, by rfl⟩ : syracuseStep 19960991 = 29941487) B29941487
theorem B1938991 : Blo 1148636 1938991 := bstep (se 1 (by rfl) ⟨1454243, by rfl⟩ : syracuseStep 1938991 = 2908487) B2908487
theorem B10492679 : Blo 1148636 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B7193447 : Blo 1148636 7193447 := bstep (se 1 (by rfl) ⟨5395085, by rfl⟩ : syracuseStep 7193447 = 10790171) B10790171
theorem B6550247 : Blo 1148636 6550247 := bstep (se 1 (by rfl) ⟨4912685, by rfl⟩ : syracuseStep 6550247 = 9825371) B9825371
theorem B9827831 : Blo 1148636 9827831 := bstep (se 1 (by rfl) ⟨7370873, by rfl⟩ : syracuseStep 9827831 = 14741747) B14741747
theorem B9831455 : Blo 1148636 9831455 := bstep (se 1 (by rfl) ⟨7373591, by rfl⟩ : syracuseStep 9831455 = 14747183) B14747183
theorem B13307327 : Blo 1148636 13307327 := bstep (se 1 (by rfl) ⟨9980495, by rfl⟩ : syracuseStep 13307327 = 19960991) B19960991
theorem B4366831 : Blo 1148636 4366831 := bstep (se 1 (by rfl) ⟨3275123, by rfl⟩ : syracuseStep 4366831 = 6550247) B6550247
theorem B4795631 : Blo 1148636 4795631 := bstep (se 1 (by rfl) ⟨3596723, by rfl⟩ : syracuseStep 4795631 = 7193447) B7193447
theorem B4371691 : Blo 1148636 4371691 := bstep (se 1 (by rfl) ⟨3278768, by rfl⟩ : syracuseStep 4371691 = 6557537) B6557537
theorem B6995119 : Blo 1148636 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B2585321 : Blo 1148636 2585321 := bstep (se 2 (by rfl) ⟨969495, by rfl⟩ : syracuseStep 2585321 = 1938991) B1938991
theorem B6551887 : Blo 1148636 6551887 := bstep (se 1 (by rfl) ⟨4913915, by rfl⟩ : syracuseStep 6551887 = 9827831) B9827831
theorem B6554303 : Blo 1148636 6554303 := bstep (se 1 (by rfl) ⟨4915727, by rfl⟩ : syracuseStep 6554303 = 9831455) B9831455
theorem B3197087 : Blo 1148636 3197087 := bstep (se 1 (by rfl) ⟨2397815, by rfl⟩ : syracuseStep 3197087 = 4795631) B4795631
theorem B8735849 : Blo 1148636 8735849 := bstep (se 2 (by rfl) ⟨3275943, by rfl⟩ : syracuseStep 8735849 = 6551887) B6551887
theorem B1723547 : Blo 1148636 1723547 := bstep (se 1 (by rfl) ⟨1292660, by rfl⟩ : syracuseStep 1723547 = 2585321) B2585321
theorem B9326825 : Blo 1148636 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B5822441 : Blo 1148636 5822441 := bstep (se 2 (by rfl) ⟨2183415, by rfl⟩ : syracuseStep 5822441 = 4366831) B4366831
theorem B8871551 : Blo 1148636 8871551 := bstep (se 1 (by rfl) ⟨6653663, by rfl⟩ : syracuseStep 8871551 = 13307327) B13307327
theorem B5828921 : Blo 1148636 5828921 := bstep (se 2 (by rfl) ⟨2185845, by rfl⟩ : syracuseStep 5828921 = 4371691) B4371691
theorem B2131391 : Blo 1148636 2131391 := bstep (se 1 (by rfl) ⟨1598543, by rfl⟩ : syracuseStep 2131391 = 3197087) B3197087
theorem B1149031 : Blo 1148636 1149031 := bstep (se 1 (by rfl) ⟨861773, by rfl⟩ : syracuseStep 1149031 = 1723547) B1723547
theorem B4369535 : Blo 1148636 4369535 := bstep (se 1 (by rfl) ⟨3277151, by rfl⟩ : syracuseStep 4369535 = 6554303) B6554303
theorem B3881627 : Blo 1148636 3881627 := bstep (se 1 (by rfl) ⟨2911220, by rfl⟩ : syracuseStep 3881627 = 5822441) B5822441
theorem B5914367 : Blo 1148636 5914367 := bstep (se 1 (by rfl) ⟨4435775, by rfl⟩ : syracuseStep 5914367 = 8871551) B8871551
theorem B3885947 : Blo 1148636 3885947 := bstep (se 1 (by rfl) ⟨2914460, by rfl⟩ : syracuseStep 3885947 = 5828921) B5828921
theorem B5823899 : Blo 1148636 5823899 := bstep (se 1 (by rfl) ⟨4367924, by rfl⟩ : syracuseStep 5823899 = 8735849) B8735849
theorem B6217883 : Blo 1148636 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B2590631 : Blo 1148636 2590631 := bstep (se 1 (by rfl) ⟨1942973, by rfl⟩ : syracuseStep 2590631 = 3885947) B3885947
theorem B3942911 : Blo 1148636 3942911 := bstep (se 1 (by rfl) ⟨2957183, by rfl⟩ : syracuseStep 3942911 = 5914367) B5914367
theorem B5683709 : Blo 1148636 5683709 := bstep (se 3 (by rfl) ⟨1065695, by rfl⟩ : syracuseStep 5683709 = 2131391) B2131391
theorem B3882599 : Blo 1148636 3882599 := bstep (se 1 (by rfl) ⟨2911949, by rfl⟩ : syracuseStep 3882599 = 5823899) B5823899
theorem B4145255 : Blo 1148636 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B2913023 : Blo 1148636 2913023 := bstep (se 1 (by rfl) ⟨2184767, by rfl⟩ : syracuseStep 2913023 = 4369535) B4369535
theorem B2587751 : Blo 1148636 2587751 := bstep (se 1 (by rfl) ⟨1940813, by rfl⟩ : syracuseStep 2587751 = 3881627) B3881627
theorem B2628607 : Blo 1148636 2628607 := bstep (se 1 (by rfl) ⟨1971455, by rfl⟩ : syracuseStep 2628607 = 3942911) B3942911
theorem B1942015 : Blo 1148636 1942015 := bstep (se 1 (by rfl) ⟨1456511, by rfl⟩ : syracuseStep 1942015 = 2913023) B2913023
theorem B2763503 : Blo 1148636 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B3789139 : Blo 1148636 3789139 := bstep (se 1 (by rfl) ⟨2841854, by rfl⟩ : syracuseStep 3789139 = 5683709) B5683709
theorem B1725167 : Blo 1148636 1725167 := bstep (se 1 (by rfl) ⟨1293875, by rfl⟩ : syracuseStep 1725167 = 2587751) B2587751
theorem B1727087 : Blo 1148636 1727087 := bstep (se 1 (by rfl) ⟨1295315, by rfl⟩ : syracuseStep 1727087 = 2590631) B2590631
theorem B2588399 : Blo 1148636 2588399 := bstep (se 1 (by rfl) ⟨1941299, by rfl⟩ : syracuseStep 2588399 = 3882599) B3882599
theorem B2589353 : Blo 1148636 2589353 := bstep (se 2 (by rfl) ⟨971007, by rfl⟩ : syracuseStep 2589353 = 1942015) B1942015
theorem B1150111 : Blo 1148636 1150111 := bstep (se 1 (by rfl) ⟨862583, by rfl⟩ : syracuseStep 1150111 = 1725167) B1725167
theorem B1151391 : Blo 1148636 1151391 := bstep (se 1 (by rfl) ⟨863543, by rfl⟩ : syracuseStep 1151391 = 1727087) B1727087
theorem B5052185 : Blo 1148636 5052185 := bstep (se 2 (by rfl) ⟨1894569, by rfl⟩ : syracuseStep 5052185 = 3789139) B3789139
theorem B1842335 : Blo 1148636 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B1725599 : Blo 1148636 1725599 := bstep (se 1 (by rfl) ⟨1294199, by rfl⟩ : syracuseStep 1725599 = 2588399) B2588399
theorem B3504809 : Blo 1148636 3504809 := bstep (se 2 (by rfl) ⟨1314303, by rfl⟩ : syracuseStep 3504809 = 2628607) B2628607
theorem B1150399 : Blo 1148636 1150399 := bstep (se 1 (by rfl) ⟨862799, by rfl⟩ : syracuseStep 1150399 = 1725599) B1725599
theorem B2336539 : Blo 1148636 2336539 := bstep (se 1 (by rfl) ⟨1752404, by rfl⟩ : syracuseStep 2336539 = 3504809) B3504809
theorem B1228223 : Blo 1148636 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B1726235 : Blo 1148636 1726235 := bstep (se 1 (by rfl) ⟨1294676, by rfl⟩ : syracuseStep 1726235 = 2589353) B2589353
theorem B3368123 : Blo 1148636 3368123 := bstep (se 1 (by rfl) ⟨2526092, by rfl⟩ : syracuseStep 3368123 = 5052185) B5052185
theorem B3115385 : Blo 1148636 3115385 := bstep (se 2 (by rfl) ⟨1168269, by rfl⟩ : syracuseStep 3115385 = 2336539) B2336539
theorem B1150823 : Blo 1148636 1150823 := bstep (se 1 (by rfl) ⟨863117, by rfl⟩ : syracuseStep 1150823 = 1726235) B1726235
theorem B2245415 : Blo 1148636 2245415 := bstep (se 1 (by rfl) ⟨1684061, by rfl⟩ : syracuseStep 2245415 = 3368123) B3368123
theorem B3275261 : Blo 1148636 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B2076923 : Blo 1148636 2076923 := bstep (se 1 (by rfl) ⟨1557692, by rfl⟩ : syracuseStep 2076923 = 3115385) B3115385
theorem B2183507 : Blo 1148636 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B5987773 : Blo 1148636 5987773 := bstep (se 3 (by rfl) ⟨1122707, by rfl⟩ : syracuseStep 5987773 = 2245415) B2245415
theorem B1384615 : Blo 1148636 1384615 := bstep (se 1 (by rfl) ⟨1038461, by rfl⟩ : syracuseStep 1384615 = 2076923) B2076923
theorem B1455671 : Blo 1148636 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B7983697 : Blo 1148636 7983697 := bstep (se 2 (by rfl) ⟨2993886, by rfl⟩ : syracuseStep 7983697 = 5987773) B5987773
theorem B1846153 : Blo 1148636 1846153 := bstep (se 2 (by rfl) ⟨692307, by rfl⟩ : syracuseStep 1846153 = 1384615) B1384615
theorem B3881789 : Blo 1148636 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B10644929 : Blo 1148636 10644929 := bstep (se 2 (by rfl) ⟨3991848, by rfl⟩ : syracuseStep 10644929 = 7983697) B7983697
theorem B2461537 : Blo 1148636 2461537 := bstep (se 2 (by rfl) ⟨923076, by rfl⟩ : syracuseStep 2461537 = 1846153) B1846153
theorem B7096619 : Blo 1148636 7096619 := bstep (se 1 (by rfl) ⟨5322464, by rfl⟩ : syracuseStep 7096619 = 10644929) B10644929
theorem B2587859 : Blo 1148636 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B3282049 : Blo 1148636 3282049 := bstep (se 2 (by rfl) ⟨1230768, by rfl⟩ : syracuseStep 3282049 = 2461537) B2461537
theorem B4731079 : Blo 1148636 4731079 := bstep (se 1 (by rfl) ⟨3548309, by rfl⟩ : syracuseStep 4731079 = 7096619) B7096619
theorem B1725239 : Blo 1148636 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B1150159 : Blo 1148636 1150159 := bstep (se 1 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 1150159 = 1725239) B1725239
theorem B6308105 : Blo 1148636 6308105 := bstep (se 2 (by rfl) ⟨2365539, by rfl⟩ : syracuseStep 6308105 = 4731079) B4731079
theorem B4376065 : Blo 1148636 4376065 := bstep (se 2 (by rfl) ⟨1641024, by rfl⟩ : syracuseStep 4376065 = 3282049) B3282049
theorem B5834753 : Blo 1148636 5834753 := bstep (se 2 (by rfl) ⟨2188032, by rfl⟩ : syracuseStep 5834753 = 4376065) B4376065
theorem B16821613 : Blo 1148636 16821613 := bstep (se 3 (by rfl) ⟨3154052, by rfl⟩ : syracuseStep 16821613 = 6308105) B6308105
theorem B3889835 : Blo 1148636 3889835 := bstep (se 1 (by rfl) ⟨2917376, by rfl⟩ : syracuseStep 3889835 = 5834753) B5834753
theorem B89715269 : Blo 1148636 89715269 := bstep (se 4 (by rfl) ⟨8410806, by rfl⟩ : syracuseStep 89715269 = 16821613) B16821613
theorem B2593223 : Blo 1148636 2593223 := bstep (se 1 (by rfl) ⟨1944917, by rfl⟩ : syracuseStep 2593223 = 3889835) B3889835
theorem B59810179 : Blo 1148636 59810179 := bstep (se 1 (by rfl) ⟨44857634, by rfl⟩ : syracuseStep 59810179 = 89715269) B89715269
theorem B79746905 : Blo 1148636 79746905 := bstep (se 2 (by rfl) ⟨29905089, by rfl⟩ : syracuseStep 79746905 = 59810179) B59810179
theorem B1728815 : Blo 1148636 1728815 := bstep (se 1 (by rfl) ⟨1296611, by rfl⟩ : syracuseStep 1728815 = 2593223) B2593223
theorem B1152543 : Blo 1148636 1152543 := bstep (se 1 (by rfl) ⟨864407, by rfl⟩ : syracuseStep 1152543 = 1728815) B1728815
theorem B53164603 : Blo 1148636 53164603 := bstep (se 1 (by rfl) ⟨39873452, by rfl⟩ : syracuseStep 53164603 = 79746905) B79746905
theorem B70886137 : Blo 1148636 70886137 := bstep (se 2 (by rfl) ⟨26582301, by rfl⟩ : syracuseStep 70886137 = 53164603) B53164603
theorem B94514849 : Blo 1148636 94514849 := bstep (se 2 (by rfl) ⟨35443068, by rfl⟩ : syracuseStep 94514849 = 70886137) B70886137
theorem B63009899 : Blo 1148636 63009899 := bstep (se 1 (by rfl) ⟨47257424, by rfl⟩ : syracuseStep 63009899 = 94514849) B94514849
theorem B42006599 : Blo 1148636 42006599 := bstep (se 1 (by rfl) ⟨31504949, by rfl⟩ : syracuseStep 42006599 = 63009899) B63009899
theorem B28004399 : Blo 1148636 28004399 := bstep (se 1 (by rfl) ⟨21003299, by rfl⟩ : syracuseStep 28004399 = 42006599) B42006599
theorem B18669599 : Blo 1148636 18669599 := bstep (se 1 (by rfl) ⟨14002199, by rfl⟩ : syracuseStep 18669599 = 28004399) B28004399
theorem B12446399 : Blo 1148636 12446399 := bstep (se 1 (by rfl) ⟨9334799, by rfl⟩ : syracuseStep 12446399 = 18669599) B18669599
theorem B8297599 : Blo 1148636 8297599 := bstep (se 1 (by rfl) ⟨6223199, by rfl⟩ : syracuseStep 8297599 = 12446399) B12446399
theorem B11063465 : Blo 1148636 11063465 := bstep (se 2 (by rfl) ⟨4148799, by rfl⟩ : syracuseStep 11063465 = 8297599) B8297599
theorem B7375643 : Blo 1148636 7375643 := bstep (se 1 (by rfl) ⟨5531732, by rfl⟩ : syracuseStep 7375643 = 11063465) B11063465
theorem B4917095 : Blo 1148636 4917095 := bstep (se 1 (by rfl) ⟨3687821, by rfl⟩ : syracuseStep 4917095 = 7375643) B7375643
theorem B3278063 : Blo 1148636 3278063 := bstep (se 1 (by rfl) ⟨2458547, by rfl⟩ : syracuseStep 3278063 = 4917095) B4917095
theorem B2185375 : Blo 1148636 2185375 := bstep (se 1 (by rfl) ⟨1639031, by rfl⟩ : syracuseStep 2185375 = 3278063) B3278063
theorem B2913833 : Blo 1148636 2913833 := bstep (se 2 (by rfl) ⟨1092687, by rfl⟩ : syracuseStep 2913833 = 2185375) B2185375
theorem B1942555 : Blo 1148636 1942555 := bstep (se 1 (by rfl) ⟨1456916, by rfl⟩ : syracuseStep 1942555 = 2913833) B2913833
theorem B2590073 : Blo 1148636 2590073 := bstep (se 2 (by rfl) ⟨971277, by rfl⟩ : syracuseStep 2590073 = 1942555) B1942555
theorem B1726715 : Blo 1148636 1726715 := bstep (se 1 (by rfl) ⟨1295036, by rfl⟩ : syracuseStep 1726715 = 2590073) B2590073
theorem B1151143 : Blo 1148636 1151143 := bstep (se 1 (by rfl) ⟨863357, by rfl⟩ : syracuseStep 1151143 = 1726715) B1726715

theorem C0 (j : ℕ) (h1 : 287159 ≤ j) (h2 : j ≤ 287858) : Blo 1148636 (4 * j + 3) := by
  interval_cases j
  · exact B1148639
  · exact B1148643
  · exact B1148647
  · exact B1148651
  · exact B1148655
  · exact B1148659
  · exact B1148663
  · exact B1148667
  · exact B1148671
  · exact B1148675
  · exact B1148679
  · exact B1148683
  · exact B1148687
  · exact B1148691
  · exact B1148695
  · exact B1148699
  · exact B1148703
  · exact B1148707
  · exact B1148711
  · exact B1148715
  · exact B1148719
  · exact B1148723
  · exact B1148727
  · exact B1148731
  · exact B1148735
  · exact B1148739
  · exact B1148743
  · exact B1148747
  · exact B1148751
  · exact B1148755
  · exact B1148759
  · exact B1148763
  · exact B1148767
  · exact B1148771
  · exact B1148775
  · exact B1148779
  · exact B1148783
  · exact B1148787
  · exact B1148791
  · exact B1148795
  · exact B1148799
  · exact B1148803
  · exact B1148807
  · exact B1148811
  · exact B1148815
  · exact B1148819
  · exact B1148823
  · exact B1148827
  · exact B1148831
  · exact B1148835
  · exact B1148839
  · exact B1148843
  · exact B1148847
  · exact B1148851
  · exact B1148855
  · exact B1148859
  · exact B1148863
  · exact B1148867
  · exact B1148871
  · exact B1148875
  · exact B1148879
  · exact B1148883
  · exact B1148887
  · exact B1148891
  · exact B1148895
  · exact B1148899
  · exact B1148903
  · exact B1148907
  · exact B1148911
  · exact B1148915
  · exact B1148919
  · exact B1148923
  · exact B1148927
  · exact B1148931
  · exact B1148935
  · exact B1148939
  · exact B1148943
  · exact B1148947
  · exact B1148951
  · exact B1148955
  · exact B1148959
  · exact B1148963
  · exact B1148967
  · exact B1148971
  · exact B1148975
  · exact B1148979
  · exact B1148983
  · exact B1148987
  · exact B1148991
  · exact B1148995
  · exact B1148999
  · exact B1149003
  · exact B1149007
  · exact B1149011
  · exact B1149015
  · exact B1149019
  · exact B1149023
  · exact B1149027
  · exact B1149031
  · exact B1149035
  · exact B1149039
  · exact B1149043
  · exact B1149047
  · exact B1149051
  · exact B1149055
  · exact B1149059
  · exact B1149063
  · exact B1149067
  · exact B1149071
  · exact B1149075
  · exact B1149079
  · exact B1149083
  · exact B1149087
  · exact B1149091
  · exact B1149095
  · exact B1149099
  · exact B1149103
  · exact B1149107
  · exact B1149111
  · exact B1149115
  · exact B1149119
  · exact B1149123
  · exact B1149127
  · exact B1149131
  · exact B1149135
  · exact B1149139
  · exact B1149143
  · exact B1149147
  · exact B1149151
  · exact B1149155
  · exact B1149159
  · exact B1149163
  · exact B1149167
  · exact B1149171
  · exact B1149175
  · exact B1149179
  · exact B1149183
  · exact B1149187
  · exact B1149191
  · exact B1149195
  · exact B1149199
  · exact B1149203
  · exact B1149207
  · exact B1149211
  · exact B1149215
  · exact B1149219
  · exact B1149223
  · exact B1149227
  · exact B1149231
  · exact B1149235
  · exact B1149239
  · exact B1149243
  · exact B1149247
  · exact B1149251
  · exact B1149255
  · exact B1149259
  · exact B1149263
  · exact B1149267
  · exact B1149271
  · exact B1149275
  · exact B1149279
  · exact B1149283
  · exact B1149287
  · exact B1149291
  · exact B1149295
  · exact B1149299
  · exact B1149303
  · exact B1149307
  · exact B1149311
  · exact B1149315
  · exact B1149319
  · exact B1149323
  · exact B1149327
  · exact B1149331
  · exact B1149335
  · exact B1149339
  · exact B1149343
  · exact B1149347
  · exact B1149351
  · exact B1149355
  · exact B1149359
  · exact B1149363
  · exact B1149367
  · exact B1149371
  · exact B1149375
  · exact B1149379
  · exact B1149383
  · exact B1149387
  · exact B1149391
  · exact B1149395
  · exact B1149399
  · exact B1149403
  · exact B1149407
  · exact B1149411
  · exact B1149415
  · exact B1149419
  · exact B1149423
  · exact B1149427
  · exact B1149431
  · exact B1149435
  · exact B1149439
  · exact B1149443
  · exact B1149447
  · exact B1149451
  · exact B1149455
  · exact B1149459
  · exact B1149463
  · exact B1149467
  · exact B1149471
  · exact B1149475
  · exact B1149479
  · exact B1149483
  · exact B1149487
  · exact B1149491
  · exact B1149495
  · exact B1149499
  · exact B1149503
  · exact B1149507
  · exact B1149511
  · exact B1149515
  · exact B1149519
  · exact B1149523
  · exact B1149527
  · exact B1149531
  · exact B1149535
  · exact B1149539
  · exact B1149543
  · exact B1149547
  · exact B1149551
  · exact B1149555
  · exact B1149559
  · exact B1149563
  · exact B1149567
  · exact B1149571
  · exact B1149575
  · exact B1149579
  · exact B1149583
  · exact B1149587
  · exact B1149591
  · exact B1149595
  · exact B1149599
  · exact B1149603
  · exact B1149607
  · exact B1149611
  · exact B1149615
  · exact B1149619
  · exact B1149623
  · exact B1149627
  · exact B1149631
  · exact B1149635
  · exact B1149639
  · exact B1149643
  · exact B1149647
  · exact B1149651
  · exact B1149655
  · exact B1149659
  · exact B1149663
  · exact B1149667
  · exact B1149671
  · exact B1149675
  · exact B1149679
  · exact B1149683
  · exact B1149687
  · exact B1149691
  · exact B1149695
  · exact B1149699
  · exact B1149703
  · exact B1149707
  · exact B1149711
  · exact B1149715
  · exact B1149719
  · exact B1149723
  · exact B1149727
  · exact B1149731
  · exact B1149735
  · exact B1149739
  · exact B1149743
  · exact B1149747
  · exact B1149751
  · exact B1149755
  · exact B1149759
  · exact B1149763
  · exact B1149767
  · exact B1149771
  · exact B1149775
  · exact B1149779
  · exact B1149783
  · exact B1149787
  · exact B1149791
  · exact B1149795
  · exact B1149799
  · exact B1149803
  · exact B1149807
  · exact B1149811
  · exact B1149815
  · exact B1149819
  · exact B1149823
  · exact B1149827
  · exact B1149831
  · exact B1149835
  · exact B1149839
  · exact B1149843
  · exact B1149847
  · exact B1149851
  · exact B1149855
  · exact B1149859
  · exact B1149863
  · exact B1149867
  · exact B1149871
  · exact B1149875
  · exact B1149879
  · exact B1149883
  · exact B1149887
  · exact B1149891
  · exact B1149895
  · exact B1149899
  · exact B1149903
  · exact B1149907
  · exact B1149911
  · exact B1149915
  · exact B1149919
  · exact B1149923
  · exact B1149927
  · exact B1149931
  · exact B1149935
  · exact B1149939
  · exact B1149943
  · exact B1149947
  · exact B1149951
  · exact B1149955
  · exact B1149959
  · exact B1149963
  · exact B1149967
  · exact B1149971
  · exact B1149975
  · exact B1149979
  · exact B1149983
  · exact B1149987
  · exact B1149991
  · exact B1149995
  · exact B1149999
  · exact B1150003
  · exact B1150007
  · exact B1150011
  · exact B1150015
  · exact B1150019
  · exact B1150023
  · exact B1150027
  · exact B1150031
  · exact B1150035
  · exact B1150039
  · exact B1150043
  · exact B1150047
  · exact B1150051
  · exact B1150055
  · exact B1150059
  · exact B1150063
  · exact B1150067
  · exact B1150071
  · exact B1150075
  · exact B1150079
  · exact B1150083
  · exact B1150087
  · exact B1150091
  · exact B1150095
  · exact B1150099
  · exact B1150103
  · exact B1150107
  · exact B1150111
  · exact B1150115
  · exact B1150119
  · exact B1150123
  · exact B1150127
  · exact B1150131
  · exact B1150135
  · exact B1150139
  · exact B1150143
  · exact B1150147
  · exact B1150151
  · exact B1150155
  · exact B1150159
  · exact B1150163
  · exact B1150167
  · exact B1150171
  · exact B1150175
  · exact B1150179
  · exact B1150183
  · exact B1150187
  · exact B1150191
  · exact B1150195
  · exact B1150199
  · exact B1150203
  · exact B1150207
  · exact B1150211
  · exact B1150215
  · exact B1150219
  · exact B1150223
  · exact B1150227
  · exact B1150231
  · exact B1150235
  · exact B1150239
  · exact B1150243
  · exact B1150247
  · exact B1150251
  · exact B1150255
  · exact B1150259
  · exact B1150263
  · exact B1150267
  · exact B1150271
  · exact B1150275
  · exact B1150279
  · exact B1150283
  · exact B1150287
  · exact B1150291
  · exact B1150295
  · exact B1150299
  · exact B1150303
  · exact B1150307
  · exact B1150311
  · exact B1150315
  · exact B1150319
  · exact B1150323
  · exact B1150327
  · exact B1150331
  · exact B1150335
  · exact B1150339
  · exact B1150343
  · exact B1150347
  · exact B1150351
  · exact B1150355
  · exact B1150359
  · exact B1150363
  · exact B1150367
  · exact B1150371
  · exact B1150375
  · exact B1150379
  · exact B1150383
  · exact B1150387
  · exact B1150391
  · exact B1150395
  · exact B1150399
  · exact B1150403
  · exact B1150407
  · exact B1150411
  · exact B1150415
  · exact B1150419
  · exact B1150423
  · exact B1150427
  · exact B1150431
  · exact B1150435
  · exact B1150439
  · exact B1150443
  · exact B1150447
  · exact B1150451
  · exact B1150455
  · exact B1150459
  · exact B1150463
  · exact B1150467
  · exact B1150471
  · exact B1150475
  · exact B1150479
  · exact B1150483
  · exact B1150487
  · exact B1150491
  · exact B1150495
  · exact B1150499
  · exact B1150503
  · exact B1150507
  · exact B1150511
  · exact B1150515
  · exact B1150519
  · exact B1150523
  · exact B1150527
  · exact B1150531
  · exact B1150535
  · exact B1150539
  · exact B1150543
  · exact B1150547
  · exact B1150551
  · exact B1150555
  · exact B1150559
  · exact B1150563
  · exact B1150567
  · exact B1150571
  · exact B1150575
  · exact B1150579
  · exact B1150583
  · exact B1150587
  · exact B1150591
  · exact B1150595
  · exact B1150599
  · exact B1150603
  · exact B1150607
  · exact B1150611
  · exact B1150615
  · exact B1150619
  · exact B1150623
  · exact B1150627
  · exact B1150631
  · exact B1150635
  · exact B1150639
  · exact B1150643
  · exact B1150647
  · exact B1150651
  · exact B1150655
  · exact B1150659
  · exact B1150663
  · exact B1150667
  · exact B1150671
  · exact B1150675
  · exact B1150679
  · exact B1150683
  · exact B1150687
  · exact B1150691
  · exact B1150695
  · exact B1150699
  · exact B1150703
  · exact B1150707
  · exact B1150711
  · exact B1150715
  · exact B1150719
  · exact B1150723
  · exact B1150727
  · exact B1150731
  · exact B1150735
  · exact B1150739
  · exact B1150743
  · exact B1150747
  · exact B1150751
  · exact B1150755
  · exact B1150759
  · exact B1150763
  · exact B1150767
  · exact B1150771
  · exact B1150775
  · exact B1150779
  · exact B1150783
  · exact B1150787
  · exact B1150791
  · exact B1150795
  · exact B1150799
  · exact B1150803
  · exact B1150807
  · exact B1150811
  · exact B1150815
  · exact B1150819
  · exact B1150823
  · exact B1150827
  · exact B1150831
  · exact B1150835
  · exact B1150839
  · exact B1150843
  · exact B1150847
  · exact B1150851
  · exact B1150855
  · exact B1150859
  · exact B1150863
  · exact B1150867
  · exact B1150871
  · exact B1150875
  · exact B1150879
  · exact B1150883
  · exact B1150887
  · exact B1150891
  · exact B1150895
  · exact B1150899
  · exact B1150903
  · exact B1150907
  · exact B1150911
  · exact B1150915
  · exact B1150919
  · exact B1150923
  · exact B1150927
  · exact B1150931
  · exact B1150935
  · exact B1150939
  · exact B1150943
  · exact B1150947
  · exact B1150951
  · exact B1150955
  · exact B1150959
  · exact B1150963
  · exact B1150967
  · exact B1150971
  · exact B1150975
  · exact B1150979
  · exact B1150983
  · exact B1150987
  · exact B1150991
  · exact B1150995
  · exact B1150999
  · exact B1151003
  · exact B1151007
  · exact B1151011
  · exact B1151015
  · exact B1151019
  · exact B1151023
  · exact B1151027
  · exact B1151031
  · exact B1151035
  · exact B1151039
  · exact B1151043
  · exact B1151047
  · exact B1151051
  · exact B1151055
  · exact B1151059
  · exact B1151063
  · exact B1151067
  · exact B1151071
  · exact B1151075
  · exact B1151079
  · exact B1151083
  · exact B1151087
  · exact B1151091
  · exact B1151095
  · exact B1151099
  · exact B1151103
  · exact B1151107
  · exact B1151111
  · exact B1151115
  · exact B1151119
  · exact B1151123
  · exact B1151127
  · exact B1151131
  · exact B1151135
  · exact B1151139
  · exact B1151143
  · exact B1151147
  · exact B1151151
  · exact B1151155
  · exact B1151159
  · exact B1151163
  · exact B1151167
  · exact B1151171
  · exact B1151175
  · exact B1151179
  · exact B1151183
  · exact B1151187
  · exact B1151191
  · exact B1151195
  · exact B1151199
  · exact B1151203
  · exact B1151207
  · exact B1151211
  · exact B1151215
  · exact B1151219
  · exact B1151223
  · exact B1151227
  · exact B1151231
  · exact B1151235
  · exact B1151239
  · exact B1151243
  · exact B1151247
  · exact B1151251
  · exact B1151255
  · exact B1151259
  · exact B1151263
  · exact B1151267
  · exact B1151271
  · exact B1151275
  · exact B1151279
  · exact B1151283
  · exact B1151287
  · exact B1151291
  · exact B1151295
  · exact B1151299
  · exact B1151303
  · exact B1151307
  · exact B1151311
  · exact B1151315
  · exact B1151319
  · exact B1151323
  · exact B1151327
  · exact B1151331
  · exact B1151335
  · exact B1151339
  · exact B1151343
  · exact B1151347
  · exact B1151351
  · exact B1151355
  · exact B1151359
  · exact B1151363
  · exact B1151367
  · exact B1151371
  · exact B1151375
  · exact B1151379
  · exact B1151383
  · exact B1151387
  · exact B1151391
  · exact B1151395
  · exact B1151399
  · exact B1151403
  · exact B1151407
  · exact B1151411
  · exact B1151415
  · exact B1151419
  · exact B1151423
  · exact B1151427
  · exact B1151431
  · exact B1151435

theorem C1 (j : ℕ) (h1 : 287859 ≤ j) (h2 : j ≤ 288158) : Blo 1148636 (4 * j + 3) := by
  interval_cases j
  · exact B1151439
  · exact B1151443
  · exact B1151447
  · exact B1151451
  · exact B1151455
  · exact B1151459
  · exact B1151463
  · exact B1151467
  · exact B1151471
  · exact B1151475
  · exact B1151479
  · exact B1151483
  · exact B1151487
  · exact B1151491
  · exact B1151495
  · exact B1151499
  · exact B1151503
  · exact B1151507
  · exact B1151511
  · exact B1151515
  · exact B1151519
  · exact B1151523
  · exact B1151527
  · exact B1151531
  · exact B1151535
  · exact B1151539
  · exact B1151543
  · exact B1151547
  · exact B1151551
  · exact B1151555
  · exact B1151559
  · exact B1151563
  · exact B1151567
  · exact B1151571
  · exact B1151575
  · exact B1151579
  · exact B1151583
  · exact B1151587
  · exact B1151591
  · exact B1151595
  · exact B1151599
  · exact B1151603
  · exact B1151607
  · exact B1151611
  · exact B1151615
  · exact B1151619
  · exact B1151623
  · exact B1151627
  · exact B1151631
  · exact B1151635
  · exact B1151639
  · exact B1151643
  · exact B1151647
  · exact B1151651
  · exact B1151655
  · exact B1151659
  · exact B1151663
  · exact B1151667
  · exact B1151671
  · exact B1151675
  · exact B1151679
  · exact B1151683
  · exact B1151687
  · exact B1151691
  · exact B1151695
  · exact B1151699
  · exact B1151703
  · exact B1151707
  · exact B1151711
  · exact B1151715
  · exact B1151719
  · exact B1151723
  · exact B1151727
  · exact B1151731
  · exact B1151735
  · exact B1151739
  · exact B1151743
  · exact B1151747
  · exact B1151751
  · exact B1151755
  · exact B1151759
  · exact B1151763
  · exact B1151767
  · exact B1151771
  · exact B1151775
  · exact B1151779
  · exact B1151783
  · exact B1151787
  · exact B1151791
  · exact B1151795
  · exact B1151799
  · exact B1151803
  · exact B1151807
  · exact B1151811
  · exact B1151815
  · exact B1151819
  · exact B1151823
  · exact B1151827
  · exact B1151831
  · exact B1151835
  · exact B1151839
  · exact B1151843
  · exact B1151847
  · exact B1151851
  · exact B1151855
  · exact B1151859
  · exact B1151863
  · exact B1151867
  · exact B1151871
  · exact B1151875
  · exact B1151879
  · exact B1151883
  · exact B1151887
  · exact B1151891
  · exact B1151895
  · exact B1151899
  · exact B1151903
  · exact B1151907
  · exact B1151911
  · exact B1151915
  · exact B1151919
  · exact B1151923
  · exact B1151927
  · exact B1151931
  · exact B1151935
  · exact B1151939
  · exact B1151943
  · exact B1151947
  · exact B1151951
  · exact B1151955
  · exact B1151959
  · exact B1151963
  · exact B1151967
  · exact B1151971
  · exact B1151975
  · exact B1151979
  · exact B1151983
  · exact B1151987
  · exact B1151991
  · exact B1151995
  · exact B1151999
  · exact B1152003
  · exact B1152007
  · exact B1152011
  · exact B1152015
  · exact B1152019
  · exact B1152023
  · exact B1152027
  · exact B1152031
  · exact B1152035
  · exact B1152039
  · exact B1152043
  · exact B1152047
  · exact B1152051
  · exact B1152055
  · exact B1152059
  · exact B1152063
  · exact B1152067
  · exact B1152071
  · exact B1152075
  · exact B1152079
  · exact B1152083
  · exact B1152087
  · exact B1152091
  · exact B1152095
  · exact B1152099
  · exact B1152103
  · exact B1152107
  · exact B1152111
  · exact B1152115
  · exact B1152119
  · exact B1152123
  · exact B1152127
  · exact B1152131
  · exact B1152135
  · exact B1152139
  · exact B1152143
  · exact B1152147
  · exact B1152151
  · exact B1152155
  · exact B1152159
  · exact B1152163
  · exact B1152167
  · exact B1152171
  · exact B1152175
  · exact B1152179
  · exact B1152183
  · exact B1152187
  · exact B1152191
  · exact B1152195
  · exact B1152199
  · exact B1152203
  · exact B1152207
  · exact B1152211
  · exact B1152215
  · exact B1152219
  · exact B1152223
  · exact B1152227
  · exact B1152231
  · exact B1152235
  · exact B1152239
  · exact B1152243
  · exact B1152247
  · exact B1152251
  · exact B1152255
  · exact B1152259
  · exact B1152263
  · exact B1152267
  · exact B1152271
  · exact B1152275
  · exact B1152279
  · exact B1152283
  · exact B1152287
  · exact B1152291
  · exact B1152295
  · exact B1152299
  · exact B1152303
  · exact B1152307
  · exact B1152311
  · exact B1152315
  · exact B1152319
  · exact B1152323
  · exact B1152327
  · exact B1152331
  · exact B1152335
  · exact B1152339
  · exact B1152343
  · exact B1152347
  · exact B1152351
  · exact B1152355
  · exact B1152359
  · exact B1152363
  · exact B1152367
  · exact B1152371
  · exact B1152375
  · exact B1152379
  · exact B1152383
  · exact B1152387
  · exact B1152391
  · exact B1152395
  · exact B1152399
  · exact B1152403
  · exact B1152407
  · exact B1152411
  · exact B1152415
  · exact B1152419
  · exact B1152423
  · exact B1152427
  · exact B1152431
  · exact B1152435
  · exact B1152439
  · exact B1152443
  · exact B1152447
  · exact B1152451
  · exact B1152455
  · exact B1152459
  · exact B1152463
  · exact B1152467
  · exact B1152471
  · exact B1152475
  · exact B1152479
  · exact B1152483
  · exact B1152487
  · exact B1152491
  · exact B1152495
  · exact B1152499
  · exact B1152503
  · exact B1152507
  · exact B1152511
  · exact B1152515
  · exact B1152519
  · exact B1152523
  · exact B1152527
  · exact B1152531
  · exact B1152535
  · exact B1152539
  · exact B1152543
  · exact B1152547
  · exact B1152551
  · exact B1152555
  · exact B1152559
  · exact B1152563
  · exact B1152567
  · exact B1152571
  · exact B1152575
  · exact B1152579
  · exact B1152583
  · exact B1152587
  · exact B1152591
  · exact B1152595
  · exact B1152599
  · exact B1152603
  · exact B1152607
  · exact B1152611
  · exact B1152615
  · exact B1152619
  · exact B1152623
  · exact B1152627
  · exact B1152631
  · exact B1152635

theorem solution (m : ℕ) (hlo : 1148636 ≤ m) (hhi : m ≤ 1152636) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 287159 ≤ j := by omega
    have hj2 : j ≤ 288158 := by omega
    have hb : Blo 1148636 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 287859 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
