-- Prove2me | solution 1 for syracuse_descends_range_1206420_1207920
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:46.924978+00:00
-- url     : https://prove2.me/submissions/06ce791f-311d-4ff2-b2a2-10c545e420e4

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


theorem B1810445 : Blo 1206420 1810445 := bbase (se 3 (by rfl) ⟨339458, by rfl⟩ : syracuseStep 1810445 = 678917) (by norm_num)
theorem B1835045 : Blo 1206420 1835045 := bbase (se 4 (by rfl) ⟨172035, by rfl⟩ : syracuseStep 1835045 = 344071) (by norm_num)
theorem B1810469 : Blo 1206420 1810469 := bbase (se 4 (by rfl) ⟨169731, by rfl⟩ : syracuseStep 1810469 = 339463) (by norm_num)
theorem B1810493 : Blo 1206420 1810493 := bbase (se 3 (by rfl) ⟨339467, by rfl⟩ : syracuseStep 1810493 = 678935) (by norm_num)
theorem B6873173 : Blo 1206420 6873173 := bbase (se 8 (by rfl) ⟨40272, by rfl⟩ : syracuseStep 6873173 = 80545) (by norm_num)
theorem B2900053 : Blo 1206420 2900053 := bbase (se 8 (by rfl) ⟨16992, by rfl⟩ : syracuseStep 2900053 = 33985) (by norm_num)
theorem B1810517 : Blo 1206420 1810517 := bbase (se 8 (by rfl) ⟨10608, by rfl⟩ : syracuseStep 1810517 = 21217) (by norm_num)
theorem B3096677 : Blo 1206420 3096677 := bbase (se 4 (by rfl) ⟨290313, by rfl⟩ : syracuseStep 3096677 = 580627) (by norm_num)
theorem B1810541 : Blo 1206420 1810541 := bbase (se 3 (by rfl) ⟨339476, by rfl⟩ : syracuseStep 1810541 = 678953) (by norm_num)
theorem B1810565 : Blo 1206420 1810565 := bbase (se 4 (by rfl) ⟨169740, by rfl⟩ : syracuseStep 1810565 = 339481) (by norm_num)
theorem B3055765 : Blo 1206420 3055765 := bbase (se 6 (by rfl) ⟨71619, by rfl⟩ : syracuseStep 3055765 = 143239) (by norm_num)
theorem B1810589 : Blo 1206420 1810589 := bbase (se 3 (by rfl) ⟨339485, by rfl⟩ : syracuseStep 1810589 = 678971) (by norm_num)
theorem B1810613 : Blo 1206420 1810613 := bbase (se 5 (by rfl) ⟨84872, by rfl⟩ : syracuseStep 1810613 = 169745) (by norm_num)
theorem B1810637 : Blo 1206420 1810637 := bbase (se 3 (by rfl) ⟨339494, by rfl⟩ : syracuseStep 1810637 = 678989) (by norm_num)
theorem B1810661 : Blo 1206420 1810661 := bbase (se 4 (by rfl) ⟨169749, by rfl⟩ : syracuseStep 1810661 = 339499) (by norm_num)
theorem B1810685 : Blo 1206420 1810685 := bbase (se 3 (by rfl) ⟨339503, by rfl⟩ : syracuseStep 1810685 = 679007) (by norm_num)
theorem B3055877 : Blo 1206420 3055877 := bbase (se 4 (by rfl) ⟨286488, by rfl⟩ : syracuseStep 3055877 = 572977) (by norm_num)
theorem B2900245 : Blo 1206420 2900245 := bbase (se 6 (by rfl) ⟨67974, by rfl⟩ : syracuseStep 2900245 = 135949) (by norm_num)
theorem B1810709 : Blo 1206420 1810709 := bbase (se 6 (by rfl) ⟨42438, by rfl⟩ : syracuseStep 1810709 = 84877) (by norm_num)
theorem B1810733 : Blo 1206420 1810733 := bbase (se 3 (by rfl) ⟨339512, by rfl⟩ : syracuseStep 1810733 = 679025) (by norm_num)
theorem B1810757 : Blo 1206420 1810757 := bbase (se 4 (by rfl) ⟨169758, by rfl⟩ : syracuseStep 1810757 = 339517) (by norm_num)
theorem B1810781 : Blo 1206420 1810781 := bbase (se 3 (by rfl) ⟨339521, by rfl⟩ : syracuseStep 1810781 = 679043) (by norm_num)
theorem B1548649 : Blo 1206420 1548649 := bbase (se 2 (by rfl) ⟨580743, by rfl⟩ : syracuseStep 1548649 = 1161487) (by norm_num)
theorem B1810805 : Blo 1206420 1810805 := bbase (se 5 (by rfl) ⟨84881, by rfl⟩ : syracuseStep 1810805 = 169763) (by norm_num)
theorem B2064781 : Blo 1206420 2064781 := bbase (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) (by norm_num)
theorem B1810829 : Blo 1206420 1810829 := bbase (se 3 (by rfl) ⟨339530, by rfl⟩ : syracuseStep 1810829 = 679061) (by norm_num)
theorem B1630621 : Blo 1206420 1630621 := bbase (se 3 (by rfl) ⟨305741, by rfl⟩ : syracuseStep 1630621 = 611483) (by norm_num)
theorem B3096997 : Blo 1206420 3096997 := bbase (se 4 (by rfl) ⟨290343, by rfl⟩ : syracuseStep 3096997 = 580687) (by norm_num)
theorem B1810853 : Blo 1206420 1810853 := bbase (se 4 (by rfl) ⟨169767, by rfl⟩ : syracuseStep 1810853 = 339535) (by norm_num)
theorem B1810877 : Blo 1206420 1810877 := bbase (se 3 (by rfl) ⟨339539, by rfl⟩ : syracuseStep 1810877 = 679079) (by norm_num)
theorem B3056069 : Blo 1206420 3056069 := bbase (se 4 (by rfl) ⟨286506, by rfl⟩ : syracuseStep 3056069 = 573013) (by norm_num)
theorem B1810901 : Blo 1206420 1810901 := bbase (se 7 (by rfl) ⟨21221, by rfl⟩ : syracuseStep 1810901 = 42443) (by norm_num)
theorem B1810925 : Blo 1206420 1810925 := bbase (se 3 (by rfl) ⟨339548, by rfl⟩ : syracuseStep 1810925 = 679097) (by norm_num)
theorem B1810949 : Blo 1206420 1810949 := bbase (se 4 (by rfl) ⟨169776, by rfl⟩ : syracuseStep 1810949 = 339553) (by norm_num)
theorem B1810973 : Blo 1206420 1810973 := bbase (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) (by norm_num)
theorem B1810997 : Blo 1206420 1810997 := bbase (se 5 (by rfl) ⟨84890, by rfl⟩ : syracuseStep 1810997 = 169781) (by norm_num)
theorem B1811021 : Blo 1206420 1811021 := bbase (se 3 (by rfl) ⟨339566, by rfl⟩ : syracuseStep 1811021 = 679133) (by norm_num)
theorem B2900573 : Blo 1206420 2900573 := bbase (se 3 (by rfl) ⟨543857, by rfl⟩ : syracuseStep 2900573 = 1087715) (by norm_num)
theorem B1811045 : Blo 1206420 1811045 := bbase (se 4 (by rfl) ⟨169785, by rfl⟩ : syracuseStep 1811045 = 339571) (by norm_num)
theorem B1811069 : Blo 1206420 1811069 := bbase (se 3 (by rfl) ⟨339575, by rfl⟩ : syracuseStep 1811069 = 679151) (by norm_num)
theorem B4072085 : Blo 1206420 4072085 := bbase (se 6 (by rfl) ⟨95439, by rfl⟩ : syracuseStep 4072085 = 190879) (by norm_num)
theorem B1811093 : Blo 1206420 1811093 := bbase (se 6 (by rfl) ⟨42447, by rfl⟩ : syracuseStep 1811093 = 84895) (by norm_num)
theorem B1811117 : Blo 1206420 1811117 := bbase (se 3 (by rfl) ⟨339584, by rfl⟩ : syracuseStep 1811117 = 679169) (by norm_num)
theorem B1811141 : Blo 1206420 1811141 := bbase (se 4 (by rfl) ⟨169794, by rfl⟩ : syracuseStep 1811141 = 339589) (by norm_num)
theorem B1811165 : Blo 1206420 1811165 := bbase (se 3 (by rfl) ⟨339593, by rfl⟩ : syracuseStep 1811165 = 679187) (by norm_num)
theorem B1811189 : Blo 1206420 1811189 := bbase (se 5 (by rfl) ⟨84899, by rfl⟩ : syracuseStep 1811189 = 169799) (by norm_num)
theorem B1450757 : Blo 1206420 1450757 := bbase (se 4 (by rfl) ⟨136008, by rfl⟩ : syracuseStep 1450757 = 272017) (by norm_num)
theorem B1811213 : Blo 1206420 1811213 := bbase (se 3 (by rfl) ⟨339602, by rfl⟩ : syracuseStep 1811213 = 679205) (by norm_num)
theorem B18588437 : Blo 1206420 18588437 := bbase (se 6 (by rfl) ⟨435666, by rfl⟩ : syracuseStep 18588437 = 871333) (by norm_num)
theorem B3056413 : Blo 1206420 3056413 := bbase (se 3 (by rfl) ⟨573077, by rfl⟩ : syracuseStep 3056413 = 1146155) (by norm_num)
theorem B1811237 : Blo 1206420 1811237 := bbase (se 4 (by rfl) ⟨169803, by rfl⟩ : syracuseStep 1811237 = 339607) (by norm_num)
theorem B1811261 : Blo 1206420 1811261 := bbase (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) (by norm_num)
theorem B1811285 : Blo 1206420 1811285 := bbase (se 9 (by rfl) ⟨5306, by rfl⟩ : syracuseStep 1811285 = 10613) (by norm_num)
theorem B1934189 : Blo 1206420 1934189 := bbase (se 3 (by rfl) ⟨362660, by rfl⟩ : syracuseStep 1934189 = 725321) (by norm_num)
theorem B1811309 : Blo 1206420 1811309 := bbase (se 3 (by rfl) ⟨339620, by rfl⟩ : syracuseStep 1811309 = 679241) (by norm_num)
theorem B1811333 : Blo 1206420 1811333 := bbase (se 4 (by rfl) ⟨169812, by rfl⟩ : syracuseStep 1811333 = 339625) (by norm_num)
theorem B3056525 : Blo 1206420 3056525 := bbase (se 3 (by rfl) ⟨573098, by rfl⟩ : syracuseStep 3056525 = 1146197) (by norm_num)
theorem B1811357 : Blo 1206420 1811357 := bbase (se 3 (by rfl) ⟨339629, by rfl⟩ : syracuseStep 1811357 = 679259) (by norm_num)
theorem B1811381 : Blo 1206420 1811381 := bbase (se 5 (by rfl) ⟨84908, by rfl⟩ : syracuseStep 1811381 = 169817) (by norm_num)
theorem B1811405 : Blo 1206420 1811405 := bbase (se 3 (by rfl) ⟨339638, by rfl⟩ : syracuseStep 1811405 = 679277) (by norm_num)
theorem B1811429 : Blo 1206420 1811429 := bbase (se 4 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 1811429 = 339643) (by norm_num)
theorem B1811453 : Blo 1206420 1811453 := bbase (se 3 (by rfl) ⟨339647, by rfl⟩ : syracuseStep 1811453 = 679295) (by norm_num)
theorem B2901005 : Blo 1206420 2901005 := bbase (se 3 (by rfl) ⟨543938, by rfl⟩ : syracuseStep 2901005 = 1087877) (by norm_num)
theorem B1811477 : Blo 1206420 1811477 := bbase (se 6 (by rfl) ⟨42456, by rfl⟩ : syracuseStep 1811477 = 84913) (by norm_num)
theorem B1451045 : Blo 1206420 1451045 := bbase (se 4 (by rfl) ⟨136035, by rfl⟩ : syracuseStep 1451045 = 272071) (by norm_num)
theorem B1934381 : Blo 1206420 1934381 := bbase (se 3 (by rfl) ⟨362696, by rfl⟩ : syracuseStep 1934381 = 725393) (by norm_num)
theorem B1811501 : Blo 1206420 1811501 := bbase (se 3 (by rfl) ⟨339656, by rfl⟩ : syracuseStep 1811501 = 679313) (by norm_num)
theorem B4072517 : Blo 1206420 4072517 := bbase (se 4 (by rfl) ⟨381798, by rfl⟩ : syracuseStep 4072517 = 763597) (by norm_num)
theorem B1811525 : Blo 1206420 1811525 := bbase (se 4 (by rfl) ⟨169830, by rfl⟩ : syracuseStep 1811525 = 339661) (by norm_num)
theorem B3056717 : Blo 1206420 3056717 := bbase (se 3 (by rfl) ⟨573134, by rfl⟩ : syracuseStep 3056717 = 1146269) (by norm_num)
theorem B1811549 : Blo 1206420 1811549 := bbase (se 3 (by rfl) ⟨339665, by rfl⟩ : syracuseStep 1811549 = 679331) (by norm_num)
theorem B4891765 : Blo 1206420 4891765 := bbase (se 5 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 4891765 = 458603) (by norm_num)
theorem B1811573 : Blo 1206420 1811573 := bbase (se 5 (by rfl) ⟨84917, by rfl⟩ : syracuseStep 1811573 = 169835) (by norm_num)
theorem B1811597 : Blo 1206420 1811597 := bbase (se 3 (by rfl) ⟨339674, by rfl⟩ : syracuseStep 1811597 = 679349) (by norm_num)
theorem B1549469 : Blo 1206420 1549469 := bbase (se 3 (by rfl) ⟨290525, by rfl⟩ : syracuseStep 1549469 = 581051) (by norm_num)
theorem B6112421 : Blo 1206420 6112421 := bbase (se 4 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 6112421 = 1146079) (by norm_num)
theorem B1811621 : Blo 1206420 1811621 := bbase (se 4 (by rfl) ⟨169839, by rfl⟩ : syracuseStep 1811621 = 339679) (by norm_num)
theorem B1811645 : Blo 1206420 1811645 := bbase (se 3 (by rfl) ⟨339683, by rfl⟩ : syracuseStep 1811645 = 679367) (by norm_num)
theorem B1811669 : Blo 1206420 1811669 := bbase (se 7 (by rfl) ⟨21230, by rfl⟩ : syracuseStep 1811669 = 42461) (by norm_num)
theorem B1811693 : Blo 1206420 1811693 := bbase (se 3 (by rfl) ⟨339692, by rfl⟩ : syracuseStep 1811693 = 679385) (by norm_num)
theorem B1631485 : Blo 1206420 1631485 := bbase (se 3 (by rfl) ⟨305903, by rfl⟩ : syracuseStep 1631485 = 611807) (by norm_num)
theorem B1811717 : Blo 1206420 1811717 := bbase (se 4 (by rfl) ⟨169848, by rfl⟩ : syracuseStep 1811717 = 339697) (by norm_num)
theorem B1811741 : Blo 1206420 1811741 := bbase (se 3 (by rfl) ⟨339701, by rfl⟩ : syracuseStep 1811741 = 679403) (by norm_num)
theorem B1811765 : Blo 1206420 1811765 := bbase (se 5 (by rfl) ⟨84926, by rfl⟩ : syracuseStep 1811765 = 169853) (by norm_num)
theorem B1811789 : Blo 1206420 1811789 := bbase (se 3 (by rfl) ⟨339710, by rfl⟩ : syracuseStep 1811789 = 679421) (by norm_num)
theorem B2901341 : Blo 1206420 2901341 := bbase (se 3 (by rfl) ⟨544001, by rfl⟩ : syracuseStep 2901341 = 1088003) (by norm_num)
theorem B1811813 : Blo 1206420 1811813 := bbase (se 4 (by rfl) ⟨169857, by rfl⟩ : syracuseStep 1811813 = 339715) (by norm_num)
theorem B1811837 : Blo 1206420 1811837 := bbase (se 3 (by rfl) ⟨339719, by rfl⟩ : syracuseStep 1811837 = 679439) (by norm_num)
theorem B1811861 : Blo 1206420 1811861 := bbase (se 6 (by rfl) ⟨42465, by rfl⟩ : syracuseStep 1811861 = 84931) (by norm_num)
theorem B3868069 : Blo 1206420 3868069 := bbase (se 4 (by rfl) ⟨362631, by rfl⟩ : syracuseStep 3868069 = 725263) (by norm_num)
theorem B3057061 : Blo 1206420 3057061 := bbase (se 4 (by rfl) ⟨286599, by rfl⟩ : syracuseStep 3057061 = 573199) (by norm_num)
theorem B1631669 : Blo 1206420 1631669 := bbase (se 5 (by rfl) ⟨76484, by rfl⟩ : syracuseStep 1631669 = 152969) (by norm_num)
theorem B4072949 : Blo 1206420 4072949 := bbase (se 5 (by rfl) ⟨190919, by rfl⟩ : syracuseStep 4072949 = 381839) (by norm_num)
theorem B3057173 : Blo 1206420 3057173 := bbase (se 6 (by rfl) ⟨71652, by rfl⟩ : syracuseStep 3057173 = 143305) (by norm_num)
theorem B3671621 : Blo 1206420 3671621 := bbase (se 4 (by rfl) ⟨344214, by rfl⟩ : syracuseStep 3671621 = 688429) (by norm_num)
theorem B3868325 : Blo 1206420 3868325 := bbase (se 4 (by rfl) ⟨362655, by rfl⟩ : syracuseStep 3868325 = 725311) (by norm_num)
theorem B3057365 : Blo 1206420 3057365 := bbase (se 7 (by rfl) ⟨35828, by rfl⟩ : syracuseStep 3057365 = 71657) (by norm_num)
theorem B2041573 : Blo 1206420 2041573 := bbase (se 4 (by rfl) ⟨191397, by rfl⟩ : syracuseStep 2041573 = 382795) (by norm_num)
theorem B5801701 : Blo 1206420 5801701 := bbase (se 4 (by rfl) ⟨543909, by rfl⟩ : syracuseStep 5801701 = 1087819) (by norm_num)
theorem B4581157 : Blo 1206420 4581157 := bbase (se 4 (by rfl) ⟨429483, by rfl⟩ : syracuseStep 4581157 = 858967) (by norm_num)
theorem B4351781 : Blo 1206420 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B4073381 : Blo 1206420 4073381 := bbase (se 4 (by rfl) ⟨381879, by rfl⟩ : syracuseStep 4073381 = 763759) (by norm_num)
theorem B10307573 : Blo 1206420 10307573 := bbase (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) (by norm_num)
theorem B1632253 : Blo 1206420 1632253 := bbase (se 3 (by rfl) ⟨306047, by rfl⟩ : syracuseStep 1632253 = 612095) (by norm_num)
theorem B4581461 : Blo 1206420 4581461 := bbase (se 8 (by rfl) ⟨26844, by rfl⟩ : syracuseStep 4581461 = 53689) (by norm_num)
theorem B5154965 : Blo 1206420 5154965 := bbase (se 6 (by rfl) ⟨120819, by rfl⟩ : syracuseStep 5154965 = 241639) (by norm_num)
theorem B1394857 : Blo 1206420 1394857 := bbase (se 2 (by rfl) ⟨523071, by rfl⟩ : syracuseStep 1394857 = 1046143) (by norm_num)
theorem B1632421 : Blo 1206420 1632421 := bbase (se 4 (by rfl) ⟨153039, by rfl⟩ : syracuseStep 1632421 = 306079) (by norm_num)
theorem B6875381 : Blo 1206420 6875381 := bbase (se 5 (by rfl) ⟨322283, by rfl⟩ : syracuseStep 6875381 = 644567) (by norm_num)
theorem B1222973 : Blo 1206420 1222973 := bbase (se 3 (by rfl) ⟨229307, by rfl⟩ : syracuseStep 1222973 = 458615) (by norm_num)
theorem B27871573 : Blo 1206420 27871573 := bbase (se 10 (by rfl) ⟨40827, by rfl⟩ : syracuseStep 27871573 = 81655) (by norm_num)
theorem B4073813 : Blo 1206420 4073813 := bbase (se 10 (by rfl) ⟨5967, by rfl⟩ : syracuseStep 4073813 = 11935) (by norm_num)
theorem B1288553 : Blo 1206420 1288553 := bbase (se 2 (by rfl) ⟨483207, by rfl⟩ : syracuseStep 1288553 = 966415) (by norm_num)
theorem B6113717 : Blo 1206420 6113717 := bbase (se 5 (by rfl) ⟨286580, by rfl⟩ : syracuseStep 6113717 = 573161) (by norm_num)
theorem B1288801 : Blo 1206420 1288801 := bbase (se 2 (by rfl) ⟨483300, by rfl⟩ : syracuseStep 1288801 = 966601) (by norm_num)
theorem B6965909 : Blo 1206420 6965909 := bbase (se 6 (by rfl) ⟨163263, by rfl⟩ : syracuseStep 6965909 = 326527) (by norm_num)
theorem B4074245 : Blo 1206420 4074245 := bbase (se 4 (by rfl) ⟨381960, by rfl⟩ : syracuseStep 4074245 = 763921) (by norm_num)
theorem B5958421 : Blo 1206420 5958421 := bbase (se 6 (by rfl) ⟨139650, by rfl⟩ : syracuseStep 5958421 = 279301) (by norm_num)
theorem B2714453 : Blo 1206420 2714453 := bbase (se 9 (by rfl) ⟨7952, by rfl⟩ : syracuseStep 2714453 = 15905) (by norm_num)
theorem B1223537 : Blo 1206420 1223537 := bbase (se 2 (by rfl) ⟨458826, by rfl⟩ : syracuseStep 1223537 = 917653) (by norm_num)
theorem B2714525 : Blo 1206420 2714525 := bbase (se 3 (by rfl) ⟨508973, by rfl⟩ : syracuseStep 2714525 = 1017947) (by norm_num)
theorem B3435493 : Blo 1206420 3435493 := bbase (se 4 (by rfl) ⟨322077, by rfl⟩ : syracuseStep 3435493 = 644155) (by norm_num)
theorem B2714597 : Blo 1206420 2714597 := bbase (se 4 (by rfl) ⟨254493, by rfl⟩ : syracuseStep 2714597 = 508987) (by norm_num)
theorem B1289233 : Blo 1206420 1289233 := bbase (se 2 (by rfl) ⟨483462, by rfl⟩ : syracuseStep 1289233 = 966925) (by norm_num)
theorem B2714669 : Blo 1206420 2714669 := bbase (se 3 (by rfl) ⟨509000, by rfl⟩ : syracuseStep 2714669 = 1018001) (by norm_num)
theorem B1289305 : Blo 1206420 1289305 := bbase (se 2 (by rfl) ⟨483489, by rfl⟩ : syracuseStep 1289305 = 966979) (by norm_num)
theorem B2174045 : Blo 1206420 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B2714741 : Blo 1206420 2714741 := bbase (se 5 (by rfl) ⟨127253, by rfl⟩ : syracuseStep 2714741 = 254507) (by norm_num)
theorem B1526941 : Blo 1206420 1526941 := bbase (se 3 (by rfl) ⟨286301, by rfl⟩ : syracuseStep 1526941 = 572603) (by norm_num)
theorem B4074677 : Blo 1206420 4074677 := bbase (se 5 (by rfl) ⟨191000, by rfl⟩ : syracuseStep 4074677 = 382001) (by norm_num)
theorem B2714813 : Blo 1206420 2714813 := bbase (se 3 (by rfl) ⟨509027, by rfl⟩ : syracuseStep 2714813 = 1018055) (by norm_num)
theorem B2174197 : Blo 1206420 2174197 := bbase (se 5 (by rfl) ⟨101915, by rfl⟩ : syracuseStep 2174197 = 203831) (by norm_num)
theorem B2714885 : Blo 1206420 2714885 := bbase (se 4 (by rfl) ⟨254520, by rfl⟩ : syracuseStep 2714885 = 509041) (by norm_num)
theorem B1527113 : Blo 1206420 1527113 := bbase (se 2 (by rfl) ⟨572667, by rfl⟩ : syracuseStep 1527113 = 1145335) (by norm_num)
theorem B2714957 : Blo 1206420 2714957 := bbase (se 3 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 2714957 = 1018109) (by norm_num)
theorem B1527169 : Blo 1206420 1527169 := bbase (se 2 (by rfl) ⟨572688, by rfl⟩ : syracuseStep 1527169 = 1145377) (by norm_num)
theorem B2715029 : Blo 1206420 2715029 := bbase (se 6 (by rfl) ⟨63633, by rfl⟩ : syracuseStep 2715029 = 127267) (by norm_num)
theorem B19582357 : Blo 1206420 19582357 := bbase (se 6 (by rfl) ⟨458961, by rfl⟩ : syracuseStep 19582357 = 917923) (by norm_num)
theorem B1469869 : Blo 1206420 1469869 := bbase (se 3 (by rfl) ⟨275600, by rfl⟩ : syracuseStep 1469869 = 551201) (by norm_num)
theorem B9293237 : Blo 1206420 9293237 := bbase (se 5 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 9293237 = 871241) (by norm_num)
theorem B3182029 : Blo 1206420 3182029 := bbase (se 3 (by rfl) ⟨596630, by rfl⟩ : syracuseStep 3182029 = 1193261) (by norm_num)
theorem B1289677 : Blo 1206420 1289677 := bbase (se 3 (by rfl) ⟨241814, by rfl⟩ : syracuseStep 1289677 = 483629) (by norm_num)
theorem B2715101 : Blo 1206420 2715101 := bbase (se 3 (by rfl) ⟨509081, by rfl⟩ : syracuseStep 2715101 = 1018163) (by norm_num)
theorem B1527265 : Blo 1206420 1527265 := bbase (se 2 (by rfl) ⟨572724, by rfl⟩ : syracuseStep 1527265 = 1145449) (by norm_num)
theorem B2715173 : Blo 1206420 2715173 := bbase (se 4 (by rfl) ⟨254547, by rfl⟩ : syracuseStep 2715173 = 509095) (by norm_num)
theorem B12381781 : Blo 1206420 12381781 := bbase (se 8 (by rfl) ⟨72549, by rfl⟩ : syracuseStep 12381781 = 145099) (by norm_num)
theorem B4075109 : Blo 1206420 4075109 := bbase (se 4 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 4075109 = 764083) (by norm_num)
theorem B2715245 : Blo 1206420 2715245 := bbase (se 3 (by rfl) ⟨509108, by rfl⟩ : syracuseStep 2715245 = 1018217) (by norm_num)
theorem B1527437 : Blo 1206420 1527437 := bbase (se 3 (by rfl) ⟨286394, by rfl⟩ : syracuseStep 1527437 = 572789) (by norm_num)
theorem B3264149 : Blo 1206420 3264149 := bbase (se 6 (by rfl) ⟨76503, by rfl⟩ : syracuseStep 3264149 = 153007) (by norm_num)
theorem B2715317 : Blo 1206420 2715317 := bbase (se 5 (by rfl) ⟨127280, by rfl⟩ : syracuseStep 2715317 = 254561) (by norm_num)
theorem B1527493 : Blo 1206420 1527493 := bbase (se 4 (by rfl) ⟨143202, by rfl⟩ : syracuseStep 1527493 = 286405) (by norm_num)
theorem B6115013 : Blo 1206420 6115013 := bbase (se 4 (by rfl) ⟨573282, by rfl⟩ : syracuseStep 6115013 = 1146565) (by norm_num)
theorem B1224401 : Blo 1206420 1224401 := bbase (se 2 (by rfl) ⟨459150, by rfl⟩ : syracuseStep 1224401 = 918301) (by norm_num)
theorem B2715389 : Blo 1206420 2715389 := bbase (se 3 (by rfl) ⟨509135, by rfl⟩ : syracuseStep 2715389 = 1018271) (by norm_num)
theorem B1306373 : Blo 1206420 1306373 := bbase (se 4 (by rfl) ⟨122472, by rfl⟩ : syracuseStep 1306373 = 244945) (by norm_num)
theorem B1527589 : Blo 1206420 1527589 := bbase (se 4 (by rfl) ⟨143211, by rfl⟩ : syracuseStep 1527589 = 286423) (by norm_num)
theorem B2715461 : Blo 1206420 2715461 := bbase (se 4 (by rfl) ⟨254574, by rfl⟩ : syracuseStep 2715461 = 509149) (by norm_num)
theorem B2715533 : Blo 1206420 2715533 := bbase (se 3 (by rfl) ⟨509162, by rfl⟩ : syracuseStep 2715533 = 1018325) (by norm_num)
theorem B1527761 : Blo 1206420 1527761 := bbase (se 2 (by rfl) ⟨572910, by rfl⟩ : syracuseStep 1527761 = 1145821) (by norm_num)
theorem B2715605 : Blo 1206420 2715605 := bbase (se 7 (by rfl) ⟨31823, by rfl⟩ : syracuseStep 2715605 = 63647) (by norm_num)
theorem B1527817 : Blo 1206420 1527817 := bbase (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) (by norm_num)
theorem B4075541 : Blo 1206420 4075541 := bbase (se 6 (by rfl) ⟨95520, by rfl⟩ : syracuseStep 4075541 = 191041) (by norm_num)
theorem B2715677 : Blo 1206420 2715677 := bbase (se 3 (by rfl) ⟨509189, by rfl⟩ : syracuseStep 2715677 = 1018379) (by norm_num)
theorem B3436597 : Blo 1206420 3436597 := bbase (se 5 (by rfl) ⟨161090, by rfl⟩ : syracuseStep 3436597 = 322181) (by norm_num)
theorem B32206933 : Blo 1206420 32206933 := bbase (se 8 (by rfl) ⟨188712, by rfl⟩ : syracuseStep 32206933 = 377425) (by norm_num)
theorem B2715749 : Blo 1206420 2715749 := bbase (se 4 (by rfl) ⟨254601, by rfl⟩ : syracuseStep 2715749 = 509203) (by norm_num)
theorem B1527913 : Blo 1206420 1527913 := bbase (se 2 (by rfl) ⟨572967, by rfl⟩ : syracuseStep 1527913 = 1145935) (by norm_num)
theorem B4583573 : Blo 1206420 4583573 := bbase (se 6 (by rfl) ⟨107427, by rfl⟩ : syracuseStep 4583573 = 214855) (by norm_num)
theorem B2715821 : Blo 1206420 2715821 := bbase (se 3 (by rfl) ⟨509216, by rfl⟩ : syracuseStep 2715821 = 1018433) (by norm_num)
theorem B2035901 : Blo 1206420 2035901 := bbase (se 3 (by rfl) ⟨381731, by rfl⟩ : syracuseStep 2035901 = 763463) (by norm_num)
theorem B1675453 : Blo 1206420 1675453 := bbase (se 3 (by rfl) ⟨314147, by rfl⟩ : syracuseStep 1675453 = 628295) (by norm_num)
theorem B2355437 : Blo 1206420 2355437 := bbase (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) (by norm_num)
theorem B2715893 : Blo 1206420 2715893 := bbase (se 5 (by rfl) ⟨127307, by rfl⟩ : syracuseStep 2715893 = 254615) (by norm_num)
theorem B1528085 : Blo 1206420 1528085 := bbase (se 6 (by rfl) ⟨35814, by rfl⟩ : syracuseStep 1528085 = 71629) (by norm_num)
theorem B2036029 : Blo 1206420 2036029 := bbase (se 3 (by rfl) ⟨381755, by rfl⟩ : syracuseStep 2036029 = 763511) (by norm_num)
theorem B2715965 : Blo 1206420 2715965 := bbase (se 3 (by rfl) ⟨509243, by rfl⟩ : syracuseStep 2715965 = 1018487) (by norm_num)
theorem B1528141 : Blo 1206420 1528141 := bbase (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) (by norm_num)
theorem B2576765 : Blo 1206420 2576765 := bbase (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) (by norm_num)
theorem B2716037 : Blo 1206420 2716037 := bbase (se 4 (by rfl) ⟨254628, by rfl⟩ : syracuseStep 2716037 = 509257) (by norm_num)
theorem B2036117 : Blo 1206420 2036117 := bbase (se 6 (by rfl) ⟨47721, by rfl⟩ : syracuseStep 2036117 = 95443) (by norm_num)
theorem B1528237 : Blo 1206420 1528237 := bbase (se 3 (by rfl) ⟨286544, by rfl⟩ : syracuseStep 1528237 = 573089) (by norm_num)
theorem B4583861 : Blo 1206420 4583861 := bbase (se 5 (by rfl) ⟨214868, by rfl⟩ : syracuseStep 4583861 = 429737) (by norm_num)
theorem B4075973 : Blo 1206420 4075973 := bbase (se 4 (by rfl) ⟨382122, by rfl⟩ : syracuseStep 4075973 = 764245) (by norm_num)
theorem B2716109 : Blo 1206420 2716109 := bbase (se 3 (by rfl) ⟨509270, by rfl⟩ : syracuseStep 2716109 = 1018541) (by norm_num)
theorem B2036245 : Blo 1206420 2036245 := bbase (se 6 (by rfl) ⟨47724, by rfl⟩ : syracuseStep 2036245 = 95449) (by norm_num)
theorem B2716181 : Blo 1206420 2716181 := bbase (se 6 (by rfl) ⟨63660, by rfl⟩ : syracuseStep 2716181 = 127321) (by norm_num)
theorem B1528409 : Blo 1206420 1528409 := bbase (se 2 (by rfl) ⟨573153, by rfl⟩ : syracuseStep 1528409 = 1146307) (by norm_num)
theorem B2716253 : Blo 1206420 2716253 := bbase (se 3 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 2716253 = 1018595) (by norm_num)
theorem B2036333 : Blo 1206420 2036333 := bbase (se 3 (by rfl) ⟨381812, by rfl⟩ : syracuseStep 2036333 = 763625) (by norm_num)
theorem B1766021 : Blo 1206420 1766021 := bbase (se 4 (by rfl) ⟨165564, by rfl⟩ : syracuseStep 1766021 = 331129) (by norm_num)
theorem B1528465 : Blo 1206420 1528465 := bbase (se 2 (by rfl) ⟨573174, by rfl⟩ : syracuseStep 1528465 = 1146349) (by norm_num)
theorem B2716325 : Blo 1206420 2716325 := bbase (se 4 (by rfl) ⟨254655, by rfl⟩ : syracuseStep 2716325 = 509311) (by norm_num)
theorem B2036461 : Blo 1206420 2036461 := bbase (se 3 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 2036461 = 763673) (by norm_num)
theorem B2716397 : Blo 1206420 2716397 := bbase (se 3 (by rfl) ⟨509324, by rfl⟩ : syracuseStep 2716397 = 1018649) (by norm_num)
theorem B1528561 : Blo 1206420 1528561 := bbase (se 2 (by rfl) ⟨573210, by rfl⟩ : syracuseStep 1528561 = 1146421) (by norm_num)
theorem B2446109 : Blo 1206420 2446109 := bbase (se 3 (by rfl) ⟨458645, by rfl⟩ : syracuseStep 2446109 = 917291) (by norm_num)
theorem B2716469 : Blo 1206420 2716469 := bbase (se 5 (by rfl) ⟨127334, by rfl⟩ : syracuseStep 2716469 = 254669) (by norm_num)
theorem B2036549 : Blo 1206420 2036549 := bbase (se 4 (by rfl) ⟨190926, by rfl⟩ : syracuseStep 2036549 = 381853) (by norm_num)
theorem B4076405 : Blo 1206420 4076405 := bbase (se 5 (by rfl) ⟨191081, by rfl⟩ : syracuseStep 4076405 = 382163) (by norm_num)
theorem B2716541 : Blo 1206420 2716541 := bbase (se 3 (by rfl) ⟨509351, by rfl⟩ : syracuseStep 2716541 = 1018703) (by norm_num)
theorem B2175869 : Blo 1206420 2175869 := bbase (se 3 (by rfl) ⟨407975, by rfl⟩ : syracuseStep 2175869 = 815951) (by norm_num)
theorem B1528733 : Blo 1206420 1528733 := bbase (se 3 (by rfl) ⟨286637, by rfl⟩ : syracuseStep 1528733 = 573275) (by norm_num)
theorem B2036677 : Blo 1206420 2036677 := bbase (se 4 (by rfl) ⟨190938, by rfl⟩ : syracuseStep 2036677 = 381877) (by norm_num)
theorem B2716613 : Blo 1206420 2716613 := bbase (se 4 (by rfl) ⟨254682, by rfl⟩ : syracuseStep 2716613 = 509365) (by norm_num)
theorem B2290693 : Blo 1206420 2290693 := bbase (se 4 (by rfl) ⟨214752, by rfl⟩ : syracuseStep 2290693 = 429505) (by norm_num)
theorem B2716685 : Blo 1206420 2716685 := bbase (se 3 (by rfl) ⟨509378, by rfl⟩ : syracuseStep 2716685 = 1018757) (by norm_num)
theorem B2036765 : Blo 1206420 2036765 := bbase (se 3 (by rfl) ⟨381893, by rfl⟩ : syracuseStep 2036765 = 763787) (by norm_num)
theorem B2716757 : Blo 1206420 2716757 := bbase (se 8 (by rfl) ⟨15918, by rfl⟩ : syracuseStep 2716757 = 31837) (by norm_num)
theorem B2290837 : Blo 1206420 2290837 := bbase (se 6 (by rfl) ⟨53691, by rfl⟩ : syracuseStep 2290837 = 107383) (by norm_num)
theorem B2036893 : Blo 1206420 2036893 := bbase (se 3 (by rfl) ⟨381917, by rfl⟩ : syracuseStep 2036893 = 763835) (by norm_num)
theorem B2716829 : Blo 1206420 2716829 := bbase (se 3 (by rfl) ⟨509405, by rfl⟩ : syracuseStep 2716829 = 1018811) (by norm_num)
theorem B2716901 : Blo 1206420 2716901 := bbase (se 4 (by rfl) ⟨254709, by rfl⟩ : syracuseStep 2716901 = 509419) (by norm_num)
theorem B2036981 : Blo 1206420 2036981 := bbase (se 5 (by rfl) ⟨95483, by rfl⟩ : syracuseStep 2036981 = 190967) (by norm_num)
theorem B1766677 : Blo 1206420 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B2716973 : Blo 1206420 2716973 := bbase (se 3 (by rfl) ⟨509432, by rfl⟩ : syracuseStep 2716973 = 1018865) (by norm_num)
theorem B2290997 : Blo 1206420 2290997 := bbase (se 5 (by rfl) ⟨107390, by rfl⟩ : syracuseStep 2290997 = 214781) (by norm_num)
theorem B9172277 : Blo 1206420 9172277 := bbase (se 5 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 9172277 = 859901) (by norm_num)
theorem B6108533 : Blo 1206420 6108533 := bbase (se 5 (by rfl) ⟨286337, by rfl⟩ : syracuseStep 6108533 = 572675) (by norm_num)
theorem B2037109 : Blo 1206420 2037109 := bbase (se 5 (by rfl) ⟨95489, by rfl⟩ : syracuseStep 2037109 = 190979) (by norm_num)
theorem B2717045 : Blo 1206420 2717045 := bbase (se 5 (by rfl) ⟨127361, by rfl⟩ : syracuseStep 2717045 = 254723) (by norm_num)
theorem B2717117 : Blo 1206420 2717117 := bbase (se 3 (by rfl) ⟨509459, by rfl⟩ : syracuseStep 2717117 = 1018919) (by norm_num)
theorem B1357249 : Blo 1206420 1357249 := bbase (se 2 (by rfl) ⟨508968, by rfl⟩ : syracuseStep 1357249 = 1017937) (by norm_num)
theorem B2291141 : Blo 1206420 2291141 := bbase (se 4 (by rfl) ⟨214794, by rfl⟩ : syracuseStep 2291141 = 429589) (by norm_num)
theorem B2037197 : Blo 1206420 2037197 := bbase (se 3 (by rfl) ⟨381974, by rfl⟩ : syracuseStep 2037197 = 763949) (by norm_num)
theorem B1357285 : Blo 1206420 1357285 := bbase (se 4 (by rfl) ⟨127245, by rfl⟩ : syracuseStep 1357285 = 254491) (by norm_num)
theorem B2717189 : Blo 1206420 2717189 := bbase (se 4 (by rfl) ⟨254736, by rfl⟩ : syracuseStep 2717189 = 509473) (by norm_num)
theorem B1357321 : Blo 1206420 1357321 := bbase (se 2 (by rfl) ⟨508995, by rfl⟩ : syracuseStep 1357321 = 1017991) (by norm_num)
theorem B3438101 : Blo 1206420 3438101 := bbase (se 6 (by rfl) ⟨80580, by rfl⟩ : syracuseStep 3438101 = 161161) (by norm_num)
theorem B1357357 : Blo 1206420 1357357 := bbase (se 3 (by rfl) ⟨254504, by rfl⟩ : syracuseStep 1357357 = 509009) (by norm_num)
theorem B2037325 : Blo 1206420 2037325 := bbase (se 3 (by rfl) ⟨381998, by rfl⟩ : syracuseStep 2037325 = 763997) (by norm_num)
theorem B2717261 : Blo 1206420 2717261 := bbase (se 3 (by rfl) ⟨509486, by rfl⟩ : syracuseStep 2717261 = 1018973) (by norm_num)
theorem B1357393 : Blo 1206420 1357393 := bbase (se 2 (by rfl) ⟨509022, by rfl⟩ : syracuseStep 1357393 = 1018045) (by norm_num)
theorem B11605589 : Blo 1206420 11605589 := bbase (se 8 (by rfl) ⟨68001, by rfl⟩ : syracuseStep 11605589 = 136003) (by norm_num)
theorem B4585045 : Blo 1206420 4585045 := bbase (se 8 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 4585045 = 53731) (by norm_num)
theorem B37189205 : Blo 1206420 37189205 := bbase (se 8 (by rfl) ⟨217905, by rfl⟩ : syracuseStep 37189205 = 435811) (by norm_num)
theorem B1357429 : Blo 1206420 1357429 := bbase (se 5 (by rfl) ⟨63629, by rfl⟩ : syracuseStep 1357429 = 127259) (by norm_num)
theorem B2717333 : Blo 1206420 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B1357465 : Blo 1206420 1357465 := bbase (se 2 (by rfl) ⟨509049, by rfl⟩ : syracuseStep 1357465 = 1018099) (by norm_num)
theorem B2479781 : Blo 1206420 2479781 := bbase (se 4 (by rfl) ⟨232479, by rfl⟩ : syracuseStep 2479781 = 464959) (by norm_num)
theorem B2037413 : Blo 1206420 2037413 := bbase (se 4 (by rfl) ⟨191007, by rfl⟩ : syracuseStep 2037413 = 382015) (by norm_num)
theorem B1357501 : Blo 1206420 1357501 := bbase (se 3 (by rfl) ⟨254531, by rfl⟩ : syracuseStep 1357501 = 509063) (by norm_num)
theorem B1717957 : Blo 1206420 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B9164501 : Blo 1206420 9164501 := bbase (se 7 (by rfl) ⟨107396, by rfl⟩ : syracuseStep 9164501 = 214793) (by norm_num)
theorem B2717405 : Blo 1206420 2717405 := bbase (se 3 (by rfl) ⟨509513, by rfl⟩ : syracuseStep 2717405 = 1019027) (by norm_num)
theorem B1357537 : Blo 1206420 1357537 := bbase (se 2 (by rfl) ⟨509076, by rfl⟩ : syracuseStep 1357537 = 1018153) (by norm_num)
theorem B2291429 : Blo 1206420 2291429 := bbase (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) (by norm_num)
theorem B1357573 : Blo 1206420 1357573 := bbase (se 4 (by rfl) ⟨127272, by rfl⟩ : syracuseStep 1357573 = 254545) (by norm_num)
theorem B2037541 : Blo 1206420 2037541 := bbase (se 4 (by rfl) ⟨191019, by rfl⟩ : syracuseStep 2037541 = 382039) (by norm_num)
theorem B2717477 : Blo 1206420 2717477 := bbase (se 4 (by rfl) ⟨254763, by rfl⟩ : syracuseStep 2717477 = 509527) (by norm_num)
theorem B1357609 : Blo 1206420 1357609 := bbase (se 2 (by rfl) ⟨509103, by rfl⟩ : syracuseStep 1357609 = 1018207) (by norm_num)
theorem B2447165 : Blo 1206420 2447165 := bbase (se 3 (by rfl) ⟨458843, by rfl⟩ : syracuseStep 2447165 = 917687) (by norm_num)
theorem B1357645 : Blo 1206420 1357645 := bbase (se 3 (by rfl) ⟨254558, by rfl⟩ : syracuseStep 1357645 = 509117) (by norm_num)
theorem B2717549 : Blo 1206420 2717549 := bbase (se 3 (by rfl) ⟨509540, by rfl⟩ : syracuseStep 2717549 = 1019081) (by norm_num)
theorem B1357681 : Blo 1206420 1357681 := bbase (se 2 (by rfl) ⟨509130, by rfl⟩ : syracuseStep 1357681 = 1018261) (by norm_num)
theorem B2291581 : Blo 1206420 2291581 := bbase (se 3 (by rfl) ⟨429671, by rfl⟩ : syracuseStep 2291581 = 859343) (by norm_num)
theorem B2037629 : Blo 1206420 2037629 := bbase (se 3 (by rfl) ⟨382055, by rfl⟩ : syracuseStep 2037629 = 764111) (by norm_num)
theorem B4585349 : Blo 1206420 4585349 := bbase (se 4 (by rfl) ⟨429876, by rfl⟩ : syracuseStep 4585349 = 859753) (by norm_num)
theorem B1357717 : Blo 1206420 1357717 := bbase (se 6 (by rfl) ⟨31821, by rfl⟩ : syracuseStep 1357717 = 63643) (by norm_num)
theorem B2717621 : Blo 1206420 2717621 := bbase (se 5 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 2717621 = 254777) (by norm_num)
theorem B1357753 : Blo 1206420 1357753 := bbase (se 2 (by rfl) ⟨509157, by rfl⟩ : syracuseStep 1357753 = 1018315) (by norm_num)
theorem B1357789 : Blo 1206420 1357789 := bbase (se 3 (by rfl) ⟨254585, by rfl⟩ : syracuseStep 1357789 = 509171) (by norm_num)
theorem B2578405 : Blo 1206420 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B8706037 : Blo 1206420 8706037 := bbase (se 5 (by rfl) ⟨408095, by rfl⟩ : syracuseStep 8706037 = 816191) (by norm_num)
theorem B2037757 : Blo 1206420 2037757 := bbase (se 3 (by rfl) ⟨382079, by rfl⟩ : syracuseStep 2037757 = 764159) (by norm_num)
theorem B2717693 : Blo 1206420 2717693 := bbase (se 3 (by rfl) ⟨509567, by rfl⟩ : syracuseStep 2717693 = 1019135) (by norm_num)
theorem B1357825 : Blo 1206420 1357825 := bbase (se 2 (by rfl) ⟨509184, by rfl⟩ : syracuseStep 1357825 = 1018369) (by norm_num)
theorem B1357861 : Blo 1206420 1357861 := bbase (se 4 (by rfl) ⟨127299, by rfl⟩ : syracuseStep 1357861 = 254599) (by norm_num)
theorem B2717765 : Blo 1206420 2717765 := bbase (se 4 (by rfl) ⟨254790, by rfl⟩ : syracuseStep 2717765 = 509581) (by norm_num)
theorem B1357897 : Blo 1206420 1357897 := bbase (se 2 (by rfl) ⟨509211, by rfl⟩ : syracuseStep 1357897 = 1018423) (by norm_num)
theorem B8697941 : Blo 1206420 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B2037845 : Blo 1206420 2037845 := bbase (se 8 (by rfl) ⟨11940, by rfl⟩ : syracuseStep 2037845 = 23881) (by norm_num)
theorem B5158997 : Blo 1206420 5158997 := bbase (se 8 (by rfl) ⟨30228, by rfl⟩ : syracuseStep 5158997 = 60457) (by norm_num)
theorem B1357933 : Blo 1206420 1357933 := bbase (se 3 (by rfl) ⟨254612, by rfl⟩ : syracuseStep 1357933 = 509225) (by norm_num)
theorem B1357969 : Blo 1206420 1357969 := bbase (se 2 (by rfl) ⟨509238, by rfl⟩ : syracuseStep 1357969 = 1018477) (by norm_num)
theorem B6871189 : Blo 1206420 6871189 := bbase (se 6 (by rfl) ⟨161043, by rfl⟩ : syracuseStep 6871189 = 322087) (by norm_num)
theorem B2291885 : Blo 1206420 2291885 := bbase (se 3 (by rfl) ⟨429728, by rfl⟩ : syracuseStep 2291885 = 859457) (by norm_num)
theorem B1358005 : Blo 1206420 1358005 := bbase (se 5 (by rfl) ⟨63656, by rfl⟩ : syracuseStep 1358005 = 127313) (by norm_num)
theorem B2037973 : Blo 1206420 2037973 := bbase (se 7 (by rfl) ⟨23882, by rfl⟩ : syracuseStep 2037973 = 47765) (by norm_num)
theorem B1358041 : Blo 1206420 1358041 := bbase (se 2 (by rfl) ⟨509265, by rfl⟩ : syracuseStep 1358041 = 1018531) (by norm_num)
theorem B3053821 : Blo 1206420 3053821 := bbase (se 3 (by rfl) ⟨572591, by rfl⟩ : syracuseStep 3053821 = 1145183) (by norm_num)
theorem B1358077 : Blo 1206420 1358077 := bbase (se 3 (by rfl) ⟨254639, by rfl⟩ : syracuseStep 1358077 = 509279) (by norm_num)
theorem B1358113 : Blo 1206420 1358113 := bbase (se 2 (by rfl) ⟨509292, by rfl⟩ : syracuseStep 1358113 = 1018585) (by norm_num)
theorem B2038061 : Blo 1206420 2038061 := bbase (se 3 (by rfl) ⟨382136, by rfl⟩ : syracuseStep 2038061 = 764273) (by norm_num)
theorem B1358149 : Blo 1206420 1358149 := bbase (se 4 (by rfl) ⟨127326, by rfl⟩ : syracuseStep 1358149 = 254653) (by norm_num)
theorem B1358185 : Blo 1206420 1358185 := bbase (se 2 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 1358185 = 1018639) (by norm_num)
theorem B3053933 : Blo 1206420 3053933 := bbase (se 3 (by rfl) ⟨572612, by rfl⟩ : syracuseStep 3053933 = 1145225) (by norm_num)
theorem B2685317 : Blo 1206420 2685317 := bbase (se 4 (by rfl) ⟨251748, by rfl⟩ : syracuseStep 2685317 = 503497) (by norm_num)
theorem B1358221 : Blo 1206420 1358221 := bbase (se 3 (by rfl) ⟨254666, by rfl⟩ : syracuseStep 1358221 = 509333) (by norm_num)
theorem B2038189 : Blo 1206420 2038189 := bbase (se 3 (by rfl) ⟨382160, by rfl⟩ : syracuseStep 2038189 = 764321) (by norm_num)
theorem B1358257 : Blo 1206420 1358257 := bbase (se 2 (by rfl) ⟨509346, by rfl⟩ : syracuseStep 1358257 = 1018693) (by norm_num)
theorem B1358293 : Blo 1206420 1358293 := bbase (se 7 (by rfl) ⟨15917, by rfl⟩ : syracuseStep 1358293 = 31835) (by norm_num)
theorem B1718749 : Blo 1206420 1718749 := bbase (se 3 (by rfl) ⟨322265, by rfl⟩ : syracuseStep 1718749 = 644531) (by norm_num)
theorem B1358329 : Blo 1206420 1358329 := bbase (se 2 (by rfl) ⟨509373, by rfl⟩ : syracuseStep 1358329 = 1018747) (by norm_num)
theorem B2038277 : Blo 1206420 2038277 := bbase (se 4 (by rfl) ⟨191088, by rfl⟩ : syracuseStep 2038277 = 382177) (by norm_num)
theorem B1358365 : Blo 1206420 1358365 := bbase (se 3 (by rfl) ⟨254693, by rfl⟩ : syracuseStep 1358365 = 509387) (by norm_num)
theorem B3054125 : Blo 1206420 3054125 := bbase (se 3 (by rfl) ⟨572648, by rfl⟩ : syracuseStep 3054125 = 1145297) (by norm_num)
theorem B1358401 : Blo 1206420 1358401 := bbase (se 2 (by rfl) ⟨509400, by rfl⟩ : syracuseStep 1358401 = 1018801) (by norm_num)
theorem B1358437 : Blo 1206420 1358437 := bbase (se 4 (by rfl) ⟨127353, by rfl⟩ : syracuseStep 1358437 = 254707) (by norm_num)
theorem B6109829 : Blo 1206420 6109829 := bbase (se 4 (by rfl) ⟨572796, by rfl⟩ : syracuseStep 6109829 = 1145593) (by norm_num)
theorem B1358473 : Blo 1206420 1358473 := bbase (se 2 (by rfl) ⟨509427, by rfl⟩ : syracuseStep 1358473 = 1018855) (by norm_num)
theorem B1358509 : Blo 1206420 1358509 := bbase (se 3 (by rfl) ⟨254720, by rfl⟩ : syracuseStep 1358509 = 509441) (by norm_num)
theorem B1358545 : Blo 1206420 1358545 := bbase (se 2 (by rfl) ⟨509454, by rfl⟩ : syracuseStep 1358545 = 1018909) (by norm_num)
theorem B1358581 : Blo 1206420 1358581 := bbase (se 5 (by rfl) ⟨63683, by rfl⟩ : syracuseStep 1358581 = 127367) (by norm_num)
theorem B23214869 : Blo 1206420 23214869 := bbase (se 6 (by rfl) ⟨544098, by rfl⟩ : syracuseStep 23214869 = 1088197) (by norm_num)
theorem B1358617 : Blo 1206420 1358617 := bbase (se 2 (by rfl) ⟨509481, by rfl⟩ : syracuseStep 1358617 = 1018963) (by norm_num)
theorem B1719085 : Blo 1206420 1719085 := bbase (se 3 (by rfl) ⟨322328, by rfl⟩ : syracuseStep 1719085 = 644657) (by norm_num)
theorem B1358653 : Blo 1206420 1358653 := bbase (se 3 (by rfl) ⟨254747, by rfl⟩ : syracuseStep 1358653 = 509495) (by norm_num)
theorem B2579293 : Blo 1206420 2579293 := bbase (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) (by norm_num)
theorem B1358689 : Blo 1206420 1358689 := bbase (se 2 (by rfl) ⟨509508, by rfl⟩ : syracuseStep 1358689 = 1019017) (by norm_num)
theorem B3054469 : Blo 1206420 3054469 := bbase (se 4 (by rfl) ⟨286356, by rfl⟩ : syracuseStep 3054469 = 572713) (by norm_num)
theorem B1358725 : Blo 1206420 1358725 := bbase (se 4 (by rfl) ⟨127380, by rfl⟩ : syracuseStep 1358725 = 254761) (by norm_num)
theorem B2292637 : Blo 1206420 2292637 := bbase (se 3 (by rfl) ⟨429869, by rfl⟩ : syracuseStep 2292637 = 859739) (by norm_num)
theorem B1358761 : Blo 1206420 1358761 := bbase (se 2 (by rfl) ⟨509535, by rfl⟩ : syracuseStep 1358761 = 1019071) (by norm_num)
theorem B7650229 : Blo 1206420 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B1358797 : Blo 1206420 1358797 := bbase (se 3 (by rfl) ⟨254774, by rfl⟩ : syracuseStep 1358797 = 509549) (by norm_num)
theorem B27884501 : Blo 1206420 27884501 := bbase (se 7 (by rfl) ⟨326771, by rfl⟩ : syracuseStep 27884501 = 653543) (by norm_num)
theorem B1358833 : Blo 1206420 1358833 := bbase (se 2 (by rfl) ⟨509562, by rfl⟩ : syracuseStep 1358833 = 1019125) (by norm_num)
theorem B3054581 : Blo 1206420 3054581 := bbase (se 5 (by rfl) ⟨143183, by rfl⟩ : syracuseStep 3054581 = 286367) (by norm_num)
theorem B1719301 : Blo 1206420 1719301 := bbase (se 4 (by rfl) ⟨161184, by rfl⟩ : syracuseStep 1719301 = 322369) (by norm_num)
theorem B1358869 : Blo 1206420 1358869 := bbase (se 6 (by rfl) ⟨31848, by rfl⟩ : syracuseStep 1358869 = 63697) (by norm_num)
theorem B2292781 : Blo 1206420 2292781 := bbase (se 3 (by rfl) ⟨429896, by rfl⟩ : syracuseStep 2292781 = 859793) (by norm_num)
theorem B1358905 : Blo 1206420 1358905 := bbase (se 2 (by rfl) ⟨509589, by rfl⟩ : syracuseStep 1358905 = 1019179) (by norm_num)
theorem B3439685 : Blo 1206420 3439685 := bbase (se 4 (by rfl) ⟨322470, by rfl⟩ : syracuseStep 3439685 = 644941) (by norm_num)
theorem B3054773 : Blo 1206420 3054773 := bbase (se 5 (by rfl) ⟨143192, by rfl⟩ : syracuseStep 3054773 = 286385) (by norm_num)
theorem B2292941 : Blo 1206420 2292941 := bbase (se 3 (by rfl) ⟨429926, by rfl⟩ : syracuseStep 2292941 = 859853) (by norm_num)
theorem B1809653 : Blo 1206420 1809653 := bbase (se 5 (by rfl) ⟨84827, by rfl⟩ : syracuseStep 1809653 = 169655) (by norm_num)
theorem B1809677 : Blo 1206420 1809677 := bbase (se 3 (by rfl) ⟨339314, by rfl⟩ : syracuseStep 1809677 = 678629) (by norm_num)
theorem B1809701 : Blo 1206420 1809701 := bbase (se 4 (by rfl) ⟨169659, by rfl⟩ : syracuseStep 1809701 = 339319) (by norm_num)
theorem B1809725 : Blo 1206420 1809725 := bbase (se 3 (by rfl) ⟨339323, by rfl⟩ : syracuseStep 1809725 = 678647) (by norm_num)
theorem B2579789 : Blo 1206420 2579789 := bbase (se 3 (by rfl) ⟨483710, by rfl⟩ : syracuseStep 2579789 = 967421) (by norm_num)
theorem B1809749 : Blo 1206420 1809749 := bbase (se 11 (by rfl) ⟨1325, by rfl⟩ : syracuseStep 1809749 = 2651) (by norm_num)
theorem B2293085 : Blo 1206420 2293085 := bbase (se 3 (by rfl) ⟨429953, by rfl⟩ : syracuseStep 2293085 = 859907) (by norm_num)
theorem B1809773 : Blo 1206420 1809773 := bbase (se 3 (by rfl) ⟨339332, by rfl⟩ : syracuseStep 1809773 = 678665) (by norm_num)
theorem B1719677 : Blo 1206420 1719677 := bbase (se 3 (by rfl) ⟨322439, by rfl⟩ : syracuseStep 1719677 = 644879) (by norm_num)
theorem B1809797 : Blo 1206420 1809797 := bbase (se 4 (by rfl) ⟨169668, by rfl⟩ : syracuseStep 1809797 = 339337) (by norm_num)
theorem B1809821 : Blo 1206420 1809821 := bbase (se 3 (by rfl) ⟨339341, by rfl⟩ : syracuseStep 1809821 = 678683) (by norm_num)
theorem B1809845 : Blo 1206420 1809845 := bbase (se 5 (by rfl) ⟨84836, by rfl⟩ : syracuseStep 1809845 = 169673) (by norm_num)
theorem B1809869 : Blo 1206420 1809869 := bbase (se 3 (by rfl) ⟨339350, by rfl⟩ : syracuseStep 1809869 = 678701) (by norm_num)
theorem B1809893 : Blo 1206420 1809893 := bbase (se 4 (by rfl) ⟨169677, by rfl⟩ : syracuseStep 1809893 = 339355) (by norm_num)
theorem B1809917 : Blo 1206420 1809917 := bbase (se 3 (by rfl) ⟨339359, by rfl⟩ : syracuseStep 1809917 = 678719) (by norm_num)
theorem B3055117 : Blo 1206420 3055117 := bbase (se 3 (by rfl) ⟨572834, by rfl⟩ : syracuseStep 3055117 = 1145669) (by norm_num)
theorem B1809941 : Blo 1206420 1809941 := bbase (se 6 (by rfl) ⟨42420, by rfl⟩ : syracuseStep 1809941 = 84841) (by norm_num)
theorem B1809965 : Blo 1206420 1809965 := bbase (se 3 (by rfl) ⟨339368, by rfl⟩ : syracuseStep 1809965 = 678737) (by norm_num)
theorem B1809989 : Blo 1206420 1809989 := bbase (se 4 (by rfl) ⟨169686, by rfl⟩ : syracuseStep 1809989 = 339373) (by norm_num)
theorem B1810013 : Blo 1206420 1810013 := bbase (se 3 (by rfl) ⟨339377, by rfl⟩ : syracuseStep 1810013 = 678755) (by norm_num)
theorem B1810037 : Blo 1206420 1810037 := bbase (se 5 (by rfl) ⟨84845, by rfl⟩ : syracuseStep 1810037 = 169691) (by norm_num)
theorem B3055229 : Blo 1206420 3055229 := bbase (se 3 (by rfl) ⟨572855, by rfl⟩ : syracuseStep 3055229 = 1145711) (by norm_num)
theorem B1810061 : Blo 1206420 1810061 := bbase (se 3 (by rfl) ⟨339386, by rfl⟩ : syracuseStep 1810061 = 678773) (by norm_num)
theorem B5226133 : Blo 1206420 5226133 := bbase (se 6 (by rfl) ⟨122487, by rfl⟩ : syracuseStep 5226133 = 244975) (by norm_num)
theorem B2612893 : Blo 1206420 2612893 := bbase (se 3 (by rfl) ⟨489917, by rfl⟩ : syracuseStep 2612893 = 979835) (by norm_num)
theorem B1810085 : Blo 1206420 1810085 := bbase (se 4 (by rfl) ⟨169695, by rfl⟩ : syracuseStep 1810085 = 339391) (by norm_num)
theorem B1449661 : Blo 1206420 1449661 := bbase (se 3 (by rfl) ⟨271811, by rfl⟩ : syracuseStep 1449661 = 543623) (by norm_num)
theorem B1810109 : Blo 1206420 1810109 := bbase (se 3 (by rfl) ⟨339395, by rfl⟩ : syracuseStep 1810109 = 678791) (by norm_num)
theorem B1932997 : Blo 1206420 1932997 := bbase (se 4 (by rfl) ⟨181218, by rfl⟩ : syracuseStep 1932997 = 362437) (by norm_num)
theorem B1810133 : Blo 1206420 1810133 := bbase (se 7 (by rfl) ⟨21212, by rfl⟩ : syracuseStep 1810133 = 42425) (by norm_num)
theorem B2752237 : Blo 1206420 2752237 := bbase (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) (by norm_num)
theorem B1810157 : Blo 1206420 1810157 := bbase (se 3 (by rfl) ⟨339404, by rfl⟩ : syracuseStep 1810157 = 678809) (by norm_num)
theorem B1810181 : Blo 1206420 1810181 := bbase (se 4 (by rfl) ⟨169704, by rfl⟩ : syracuseStep 1810181 = 339409) (by norm_num)
theorem B1449757 : Blo 1206420 1449757 := bbase (se 3 (by rfl) ⟨271829, by rfl⟩ : syracuseStep 1449757 = 543659) (by norm_num)
theorem B1810205 : Blo 1206420 1810205 := bbase (se 3 (by rfl) ⟨339413, by rfl⟩ : syracuseStep 1810205 = 678827) (by norm_num)
theorem B1810229 : Blo 1206420 1810229 := bbase (se 5 (by rfl) ⟨84854, by rfl⟩ : syracuseStep 1810229 = 169709) (by norm_num)
theorem B3055421 : Blo 1206420 3055421 := bbase (se 3 (by rfl) ⟨572891, by rfl⟩ : syracuseStep 3055421 = 1145783) (by norm_num)
theorem B1810253 : Blo 1206420 1810253 := bbase (se 3 (by rfl) ⟨339422, by rfl⟩ : syracuseStep 1810253 = 678845) (by norm_num)
theorem B88137557 : Blo 1206420 88137557 := bbase (se 9 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 88137557 = 516431) (by norm_num)
theorem B1810277 : Blo 1206420 1810277 := bbase (se 4 (by rfl) ⟨169713, by rfl⟩ : syracuseStep 1810277 = 339427) (by norm_num)
theorem B1810301 : Blo 1206420 1810301 := bbase (se 3 (by rfl) ⟨339431, by rfl⟩ : syracuseStep 1810301 = 678863) (by norm_num)
theorem B1810325 : Blo 1206420 1810325 := bbase (se 6 (by rfl) ⟨42429, by rfl⟩ : syracuseStep 1810325 = 84859) (by norm_num)
theorem B7733141 : Blo 1206420 7733141 := bbase (se 6 (by rfl) ⟨181245, by rfl⟩ : syracuseStep 7733141 = 362491) (by norm_num)
theorem B6111125 : Blo 1206420 6111125 := bbase (se 6 (by rfl) ⟨143229, by rfl⟩ : syracuseStep 6111125 = 286459) (by norm_num)
theorem B1810349 : Blo 1206420 1810349 := bbase (se 3 (by rfl) ⟨339440, by rfl⟩ : syracuseStep 1810349 = 678881) (by norm_num)
theorem B1810373 : Blo 1206420 1810373 := bbase (se 4 (by rfl) ⟨169722, by rfl⟩ : syracuseStep 1810373 = 339445) (by norm_num)
theorem B1810397 : Blo 1206420 1810397 := bbase (se 3 (by rfl) ⟨339449, by rfl⟩ : syracuseStep 1810397 = 678899) (by norm_num)
theorem B1810421 : Blo 1206420 1810421 := bbase (se 5 (by rfl) ⟨84863, by rfl⟩ : syracuseStep 1810421 = 169727) (by norm_num)
theorem B2899957 : Blo 1206420 2899957 := bbase (se 5 (by rfl) ⟨135935, by rfl⟩ : syracuseStep 2899957 = 271871) (by norm_num)
theorem B1810433 : Blo 1206420 1810433 := bstep (se 2 (by rfl) ⟨678912, by rfl⟩ : syracuseStep 1810433 = 1357825) B1357825
theorem B1810451 : Blo 1206420 1810451 := bstep (se 1 (by rfl) ⟨1357838, by rfl⟩ : syracuseStep 1810451 = 2715677) B2715677
theorem B1810481 : Blo 1206420 1810481 := bstep (se 2 (by rfl) ⟨678930, by rfl⟩ : syracuseStep 1810481 = 1357861) B1357861
theorem B1810499 : Blo 1206420 1810499 := bstep (se 1 (by rfl) ⟨1357874, by rfl⟩ : syracuseStep 1810499 = 2715749) B2715749
theorem B1810529 : Blo 1206420 1810529 := bstep (se 2 (by rfl) ⟨678948, by rfl⟩ : syracuseStep 1810529 = 1357897) B1357897
theorem B3055715 : Blo 1206420 3055715 := bstep (se 1 (by rfl) ⟨2291786, by rfl⟩ : syracuseStep 3055715 = 4583573) B4583573
theorem B42942577 : Blo 1206420 42942577 := bstep (se 2 (by rfl) ⟨16103466, by rfl⟩ : syracuseStep 42942577 = 32206933) B32206933
theorem B3866737 : Blo 1206420 3866737 := bstep (se 2 (by rfl) ⟨1450026, by rfl⟩ : syracuseStep 3866737 = 2900053) B2900053
theorem B1810547 : Blo 1206420 1810547 := bstep (se 1 (by rfl) ⟨1357910, by rfl⟩ : syracuseStep 1810547 = 2715821) B2715821
theorem B1810577 : Blo 1206420 1810577 := bstep (se 2 (by rfl) ⟨678966, by rfl⟩ : syracuseStep 1810577 = 1357933) B1357933
theorem B1810595 : Blo 1206420 1810595 := bstep (se 1 (by rfl) ⟨1357946, by rfl⟩ : syracuseStep 1810595 = 2715893) B2715893
theorem B1810625 : Blo 1206420 1810625 := bstep (se 2 (by rfl) ⟨678984, by rfl⟩ : syracuseStep 1810625 = 1357969) B1357969
theorem B1810643 : Blo 1206420 1810643 := bstep (se 1 (by rfl) ⟨1357982, by rfl⟩ : syracuseStep 1810643 = 2715965) B2715965
theorem B1859809 : Blo 1206420 1859809 := bstep (se 2 (by rfl) ⟨697428, by rfl⟩ : syracuseStep 1859809 = 1394857) B1394857
theorem B1810673 : Blo 1206420 1810673 := bstep (se 2 (by rfl) ⟨679002, by rfl⟩ : syracuseStep 1810673 = 1358005) B1358005
theorem B1810691 : Blo 1206420 1810691 := bstep (se 1 (by rfl) ⟨1358018, by rfl⟩ : syracuseStep 1810691 = 2716037) B2716037
theorem B8257805 : Blo 1206420 8257805 := bstep (se 3 (by rfl) ⟨1548338, by rfl⟩ : syracuseStep 8257805 = 3096677) B3096677
theorem B1810721 : Blo 1206420 1810721 := bstep (se 2 (by rfl) ⟨679020, by rfl⟩ : syracuseStep 1810721 = 1358041) B1358041
theorem B3055907 : Blo 1206420 3055907 := bstep (se 1 (by rfl) ⟨2291930, by rfl⟩ : syracuseStep 3055907 = 4583861) B4583861
theorem B1810739 : Blo 1206420 1810739 := bstep (se 1 (by rfl) ⟨1358054, by rfl⟩ : syracuseStep 1810739 = 2716109) B2716109
theorem B4071761 : Blo 1206420 4071761 := bstep (se 2 (by rfl) ⟨1526910, by rfl⟩ : syracuseStep 4071761 = 3053821) B3053821
theorem B1810769 : Blo 1206420 1810769 := bstep (se 2 (by rfl) ⟨679038, by rfl⟩ : syracuseStep 1810769 = 1358077) B1358077
theorem B1810787 : Blo 1206420 1810787 := bstep (se 1 (by rfl) ⟨1358090, by rfl⟩ : syracuseStep 1810787 = 2716181) B2716181
theorem B3866993 : Blo 1206420 3866993 := bstep (se 2 (by rfl) ⟨1450122, by rfl⟩ : syracuseStep 3866993 = 2900245) B2900245
theorem B1810817 : Blo 1206420 1810817 := bstep (se 2 (by rfl) ⟨679056, by rfl⟩ : syracuseStep 1810817 = 1358113) B1358113
theorem B1933715 : Blo 1206420 1933715 := bstep (se 1 (by rfl) ⟨1450286, by rfl⟩ : syracuseStep 1933715 = 2900573) B2900573
theorem B1810835 : Blo 1206420 1810835 := bstep (se 1 (by rfl) ⟨1358126, by rfl⟩ : syracuseStep 1810835 = 2716253) B2716253
theorem B1810865 : Blo 1206420 1810865 := bstep (se 2 (by rfl) ⟨679074, by rfl⟩ : syracuseStep 1810865 = 1358149) B1358149
theorem B1810883 : Blo 1206420 1810883 := bstep (se 1 (by rfl) ⟨1358162, by rfl⟩ : syracuseStep 1810883 = 2716325) B2716325
theorem B2064865 : Blo 1206420 2064865 := bstep (se 2 (by rfl) ⟨774324, by rfl⟩ : syracuseStep 2064865 = 1548649) B1548649
theorem B1810913 : Blo 1206420 1810913 := bstep (se 2 (by rfl) ⟨679092, by rfl⟩ : syracuseStep 1810913 = 1358185) B1358185
theorem B1810931 : Blo 1206420 1810931 := bstep (se 1 (by rfl) ⟨1358198, by rfl⟩ : syracuseStep 1810931 = 2716397) B2716397
theorem B6873605 : Blo 1206420 6873605 := bstep (se 4 (by rfl) ⟨644400, by rfl⟩ : syracuseStep 6873605 = 1288801) B1288801
theorem B2753041 : Blo 1206420 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B1810961 : Blo 1206420 1810961 := bstep (se 2 (by rfl) ⟨679110, by rfl⟩ : syracuseStep 1810961 = 1358221) B1358221
theorem B1630739 : Blo 1206420 1630739 := bstep (se 1 (by rfl) ⟨1223054, by rfl⟩ : syracuseStep 1630739 = 2446109) B2446109
theorem B1810979 : Blo 1206420 1810979 := bstep (se 1 (by rfl) ⟨1358234, by rfl⟩ : syracuseStep 1810979 = 2716469) B2716469
theorem B1811009 : Blo 1206420 1811009 := bstep (se 2 (by rfl) ⟨679128, by rfl⟩ : syracuseStep 1811009 = 1358257) B1358257
theorem B1811027 : Blo 1206420 1811027 := bstep (se 1 (by rfl) ⟨1358270, by rfl⟩ : syracuseStep 1811027 = 2716541) B2716541
theorem B1811057 : Blo 1206420 1811057 := bstep (se 2 (by rfl) ⟨679146, by rfl⟩ : syracuseStep 1811057 = 1358293) B1358293
theorem B1811075 : Blo 1206420 1811075 := bstep (se 1 (by rfl) ⟨1358306, by rfl⟩ : syracuseStep 1811075 = 2716613) B2716613
theorem B1811105 : Blo 1206420 1811105 := bstep (se 2 (by rfl) ⟨679164, by rfl⟩ : syracuseStep 1811105 = 1358329) B1358329
theorem B1934003 : Blo 1206420 1934003 := bstep (se 1 (by rfl) ⟨1450502, by rfl⟩ : syracuseStep 1934003 = 2901005) B2901005
theorem B1811123 : Blo 1206420 1811123 := bstep (se 1 (by rfl) ⟨1358342, by rfl⟩ : syracuseStep 1811123 = 2716685) B2716685
theorem B1811153 : Blo 1206420 1811153 := bstep (se 2 (by rfl) ⟨679182, by rfl⟩ : syracuseStep 1811153 = 1358365) B1358365
theorem B1811171 : Blo 1206420 1811171 := bstep (se 1 (by rfl) ⟨1358378, by rfl⟩ : syracuseStep 1811171 = 2716757) B2716757
theorem B1811201 : Blo 1206420 1811201 := bstep (se 2 (by rfl) ⟨679200, by rfl⟩ : syracuseStep 1811201 = 1358401) B1358401
theorem B1811219 : Blo 1206420 1811219 := bstep (se 1 (by rfl) ⟨1358414, by rfl⟩ : syracuseStep 1811219 = 2716829) B2716829
theorem B66069269 : Blo 1206420 66069269 := bstep (se 6 (by rfl) ⟨1548498, by rfl⟩ : syracuseStep 66069269 = 3096997) B3096997
theorem B1811249 : Blo 1206420 1811249 := bstep (se 2 (by rfl) ⟨679218, by rfl⟩ : syracuseStep 1811249 = 1358437) B1358437
theorem B1811267 : Blo 1206420 1811267 := bstep (se 1 (by rfl) ⟨1358450, by rfl⟩ : syracuseStep 1811267 = 2716901) B2716901
theorem B1811297 : Blo 1206420 1811297 := bstep (se 2 (by rfl) ⟨679236, by rfl⟩ : syracuseStep 1811297 = 1358473) B1358473
theorem B4072301 : Blo 1206420 4072301 := bstep (se 3 (by rfl) ⟨763556, by rfl⟩ : syracuseStep 4072301 = 1527113) B1527113
theorem B1811315 : Blo 1206420 1811315 := bstep (se 1 (by rfl) ⟨1358486, by rfl⟩ : syracuseStep 1811315 = 2716973) B2716973
theorem B1811345 : Blo 1206420 1811345 := bstep (se 2 (by rfl) ⟨679254, by rfl⟩ : syracuseStep 1811345 = 1358509) B1358509
theorem B1934227 : Blo 1206420 1934227 := bstep (se 1 (by rfl) ⟨1450670, by rfl⟩ : syracuseStep 1934227 = 2901341) B2901341
theorem B4072355 : Blo 1206420 4072355 := bstep (se 1 (by rfl) ⟨3054266, by rfl⟩ : syracuseStep 4072355 = 6108533) B6108533
theorem B1811363 : Blo 1206420 1811363 := bstep (se 1 (by rfl) ⟨1358522, by rfl⟩ : syracuseStep 1811363 = 2717045) B2717045
theorem B1811393 : Blo 1206420 1811393 := bstep (se 2 (by rfl) ⟨679272, by rfl⟩ : syracuseStep 1811393 = 1358545) B1358545
theorem B1811411 : Blo 1206420 1811411 := bstep (se 1 (by rfl) ⟨1358558, by rfl⟩ : syracuseStep 1811411 = 2717117) B2717117
theorem B1811441 : Blo 1206420 1811441 := bstep (se 2 (by rfl) ⟨679290, by rfl⟩ : syracuseStep 1811441 = 1358581) B1358581
theorem B1811459 : Blo 1206420 1811459 := bstep (se 1 (by rfl) ⟨1358594, by rfl⟩ : syracuseStep 1811459 = 2717189) B2717189
theorem B1811489 : Blo 1206420 1811489 := bstep (se 2 (by rfl) ⟨679308, by rfl⟩ : syracuseStep 1811489 = 1358617) B1358617
theorem B1811507 : Blo 1206420 1811507 := bstep (se 1 (by rfl) ⟨1358630, by rfl⟩ : syracuseStep 1811507 = 2717261) B2717261
theorem B1811537 : Blo 1206420 1811537 := bstep (se 2 (by rfl) ⟨679326, by rfl⟩ : syracuseStep 1811537 = 1358653) B1358653
theorem B1811555 : Blo 1206420 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B1811585 : Blo 1206420 1811585 := bstep (se 2 (by rfl) ⟨679344, by rfl⟩ : syracuseStep 1811585 = 1358689) B1358689
theorem B4351117 : Blo 1206420 4351117 := bstep (se 3 (by rfl) ⟨815834, by rfl⟩ : syracuseStep 4351117 = 1631669) B1631669
theorem B1811603 : Blo 1206420 1811603 := bstep (se 1 (by rfl) ⟨1358702, by rfl⟩ : syracuseStep 1811603 = 2717405) B2717405
theorem B4072625 : Blo 1206420 4072625 := bstep (se 2 (by rfl) ⟨1527234, by rfl⟩ : syracuseStep 4072625 = 3054469) B3054469
theorem B1811633 : Blo 1206420 1811633 := bstep (se 2 (by rfl) ⟨679362, by rfl⟩ : syracuseStep 1811633 = 1358725) B1358725
theorem B2901187 : Blo 1206420 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B1811651 : Blo 1206420 1811651 := bstep (se 1 (by rfl) ⟨1358738, by rfl⟩ : syracuseStep 1811651 = 2717477) B2717477
theorem B3056849 : Blo 1206420 3056849 := bstep (se 2 (by rfl) ⟨1146318, by rfl⟩ : syracuseStep 3056849 = 2292637) B2292637
theorem B1631443 : Blo 1206420 1631443 := bstep (se 1 (by rfl) ⟨1223582, by rfl⟩ : syracuseStep 1631443 = 2447165) B2447165
theorem B1811681 : Blo 1206420 1811681 := bstep (se 2 (by rfl) ⟨679380, by rfl⟩ : syracuseStep 1811681 = 1358761) B1358761
theorem B10200305 : Blo 1206420 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B1811699 : Blo 1206420 1811699 := bstep (se 1 (by rfl) ⟨1358774, by rfl⟩ : syracuseStep 1811699 = 2717549) B2717549
theorem B3056899 : Blo 1206420 3056899 := bstep (se 1 (by rfl) ⟨2292674, by rfl⟩ : syracuseStep 3056899 = 4585349) B4585349
theorem B1811729 : Blo 1206420 1811729 := bstep (se 2 (by rfl) ⟨679398, by rfl⟩ : syracuseStep 1811729 = 1358797) B1358797
theorem B1811747 : Blo 1206420 1811747 := bstep (se 1 (by rfl) ⟨1358810, by rfl⟩ : syracuseStep 1811747 = 2717621) B2717621
theorem B4580657 : Blo 1206420 4580657 := bstep (se 2 (by rfl) ⟨1717746, by rfl⟩ : syracuseStep 4580657 = 3435493) B3435493
theorem B1811777 : Blo 1206420 1811777 := bstep (se 2 (by rfl) ⟨679416, by rfl⟩ : syracuseStep 1811777 = 1358833) B1358833
theorem B8701253 : Blo 1206420 8701253 := bstep (se 4 (by rfl) ⟨815742, by rfl⟩ : syracuseStep 8701253 = 1631485) B1631485
theorem B1811795 : Blo 1206420 1811795 := bstep (se 1 (by rfl) ⟨1358846, by rfl⟩ : syracuseStep 1811795 = 2717693) B2717693
theorem B1811825 : Blo 1206420 1811825 := bstep (se 2 (by rfl) ⟨679434, by rfl⟩ : syracuseStep 1811825 = 1358869) B1358869
theorem B1811843 : Blo 1206420 1811843 := bstep (se 1 (by rfl) ⟨1358882, by rfl⟩ : syracuseStep 1811843 = 2717765) B2717765
theorem B3057041 : Blo 1206420 3057041 := bstep (se 2 (by rfl) ⟨1146390, by rfl⟩ : syracuseStep 3057041 = 2292781) B2292781
theorem B1811873 : Blo 1206420 1811873 := bstep (se 2 (by rfl) ⟨679452, by rfl⟩ : syracuseStep 1811873 = 1358905) B1358905
theorem B6522353 : Blo 1206420 6522353 := bstep (se 2 (by rfl) ⟨2445882, by rfl⟩ : syracuseStep 6522353 = 4891765) B4891765
theorem B4073165 : Blo 1206420 4073165 := bstep (se 3 (by rfl) ⟨763718, by rfl⟩ : syracuseStep 4073165 = 1527437) B1527437
theorem B4073219 : Blo 1206420 4073219 := bstep (se 1 (by rfl) ⟨3054914, by rfl⟩ : syracuseStep 4073219 = 6109829) B6109829
theorem B6612749 : Blo 1206420 6612749 := bstep (se 3 (by rfl) ⟨1239890, by rfl⟩ : syracuseStep 6612749 = 2479781) B2479781
theorem B13756229 : Blo 1206420 13756229 := bstep (se 4 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 13756229 = 2579293) B2579293
theorem B15476579 : Blo 1206420 15476579 := bstep (se 1 (by rfl) ⟨11607434, by rfl⟩ : syracuseStep 15476579 = 23214869) B23214869
theorem B26109809 : Blo 1206420 26109809 := bstep (se 2 (by rfl) ⟨9791178, by rfl⟩ : syracuseStep 26109809 = 19582357) B19582357
theorem B18589667 : Blo 1206420 18589667 := bstep (se 1 (by rfl) ⟨13942250, by rfl⟩ : syracuseStep 18589667 = 27884501) B27884501
theorem B3483661 : Blo 1206420 3483661 := bstep (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) B1306373
theorem B3868685 : Blo 1206420 3868685 := bstep (se 3 (by rfl) ⟨725378, by rfl⟩ : syracuseStep 3868685 = 1450757) B1450757
theorem B4073489 : Blo 1206420 4073489 := bstep (se 2 (by rfl) ⟨1527558, by rfl⟩ : syracuseStep 4073489 = 3055117) B3055117
theorem B16509041 : Blo 1206420 16509041 := bstep (se 2 (by rfl) ⟨6190890, by rfl⟩ : syracuseStep 16509041 = 12381781) B12381781
theorem B6113393 : Blo 1206420 6113393 := bstep (se 2 (by rfl) ⟨2292522, by rfl⟩ : syracuseStep 6113393 = 4585045) B4585045
theorem B1206435 : Blo 1206420 1206435 := bstep (se 1 (by rfl) ⟨904826, by rfl⟩ : syracuseStep 1206435 = 1809653) B1809653
theorem B1206451 : Blo 1206420 1206451 := bstep (se 1 (by rfl) ⟨904838, by rfl⟩ : syracuseStep 1206451 = 1809677) B1809677
theorem B1206467 : Blo 1206420 1206467 := bstep (se 1 (by rfl) ⟨904850, by rfl⟩ : syracuseStep 1206467 = 1809701) B1809701
theorem B3483857 : Blo 1206420 3483857 := bstep (se 2 (by rfl) ⟨1306446, by rfl⟩ : syracuseStep 3483857 = 2612893) B2612893
theorem B1206483 : Blo 1206420 1206483 := bstep (se 1 (by rfl) ⟨904862, by rfl⟩ : syracuseStep 1206483 = 1809725) B1809725
theorem B1206499 : Blo 1206420 1206499 := bstep (se 1 (by rfl) ⟨904874, by rfl⟩ : syracuseStep 1206499 = 1809749) B1809749
theorem B1206515 : Blo 1206420 1206515 := bstep (se 1 (by rfl) ⟨904886, by rfl⟩ : syracuseStep 1206515 = 1809773) B1809773
theorem B1206531 : Blo 1206420 1206531 := bstep (se 1 (by rfl) ⟨904898, by rfl⟩ : syracuseStep 1206531 = 1809797) B1809797
theorem B1206547 : Blo 1206420 1206547 := bstep (se 1 (by rfl) ⟨904910, by rfl⟩ : syracuseStep 1206547 = 1809821) B1809821
theorem B1206563 : Blo 1206420 1206563 := bstep (se 1 (by rfl) ⟨904922, by rfl⟩ : syracuseStep 1206563 = 1809845) B1809845
theorem B6195491 : Blo 1206420 6195491 := bstep (se 1 (by rfl) ⟨4646618, by rfl⟩ : syracuseStep 6195491 = 9293237) B9293237
theorem B3262765 : Blo 1206420 3262765 := bstep (se 3 (by rfl) ⟨611768, by rfl⟩ : syracuseStep 3262765 = 1223537) B1223537
theorem B2722097 : Blo 1206420 2722097 := bstep (se 2 (by rfl) ⟨1020786, by rfl⟩ : syracuseStep 2722097 = 2041573) B2041573
theorem B1206579 : Blo 1206420 1206579 := bstep (se 1 (by rfl) ⟨904934, by rfl⟩ : syracuseStep 1206579 = 1809869) B1809869
theorem B7735601 : Blo 1206420 7735601 := bstep (se 2 (by rfl) ⟨2900850, by rfl⟩ : syracuseStep 7735601 = 5801701) B5801701
theorem B1206595 : Blo 1206420 1206595 := bstep (se 1 (by rfl) ⟨904946, by rfl⟩ : syracuseStep 1206595 = 1809893) B1809893
theorem B5802317 : Blo 1206420 5802317 := bstep (se 3 (by rfl) ⟨1087934, by rfl⟩ : syracuseStep 5802317 = 2175869) B2175869
theorem B1206611 : Blo 1206420 1206611 := bstep (se 1 (by rfl) ⟨904958, by rfl⟩ : syracuseStep 1206611 = 1809917) B1809917
theorem B1206627 : Blo 1206420 1206627 := bstep (se 1 (by rfl) ⟨904970, by rfl⟩ : syracuseStep 1206627 = 1809941) B1809941
theorem B1206643 : Blo 1206420 1206643 := bstep (se 1 (by rfl) ⟨904982, by rfl⟩ : syracuseStep 1206643 = 1809965) B1809965
theorem B1206659 : Blo 1206420 1206659 := bstep (se 1 (by rfl) ⟨904994, by rfl⟩ : syracuseStep 1206659 = 1809989) B1809989
theorem B1206675 : Blo 1206420 1206675 := bstep (se 1 (by rfl) ⟨905006, by rfl⟩ : syracuseStep 1206675 = 1810013) B1810013
theorem B1206691 : Blo 1206420 1206691 := bstep (se 1 (by rfl) ⟨905018, by rfl⟩ : syracuseStep 1206691 = 1810037) B1810037
theorem B1206707 : Blo 1206420 1206707 := bstep (se 1 (by rfl) ⟨905030, by rfl⟩ : syracuseStep 1206707 = 1810061) B1810061
theorem B1206723 : Blo 1206420 1206723 := bstep (se 1 (by rfl) ⟨905042, by rfl⟩ : syracuseStep 1206723 = 1810085) B1810085
theorem B1206739 : Blo 1206420 1206739 := bstep (se 1 (by rfl) ⟨905054, by rfl⟩ : syracuseStep 1206739 = 1810109) B1810109
theorem B1206755 : Blo 1206420 1206755 := bstep (se 1 (by rfl) ⟨905066, by rfl⟩ : syracuseStep 1206755 = 1810133) B1810133
theorem B1206771 : Blo 1206420 1206771 := bstep (se 1 (by rfl) ⟨905078, by rfl⟩ : syracuseStep 1206771 = 1810157) B1810157
theorem B1206787 : Blo 1206420 1206787 := bstep (se 1 (by rfl) ⟨905090, by rfl⟩ : syracuseStep 1206787 = 1810181) B1810181
theorem B1206803 : Blo 1206420 1206803 := bstep (se 1 (by rfl) ⟨905102, by rfl⟩ : syracuseStep 1206803 = 1810205) B1810205
theorem B1206819 : Blo 1206420 1206819 := bstep (se 1 (by rfl) ⟨905114, by rfl⟩ : syracuseStep 1206819 = 1810229) B1810229
theorem B4074029 : Blo 1206420 4074029 := bstep (se 3 (by rfl) ⟨763880, by rfl⟩ : syracuseStep 4074029 = 1527761) B1527761
theorem B1206835 : Blo 1206420 1206835 := bstep (se 1 (by rfl) ⟨905126, by rfl⟩ : syracuseStep 1206835 = 1810253) B1810253
theorem B1206851 : Blo 1206420 1206851 := bstep (se 1 (by rfl) ⟨905138, by rfl⟩ : syracuseStep 1206851 = 1810277) B1810277
theorem B1206867 : Blo 1206420 1206867 := bstep (se 1 (by rfl) ⟨905150, by rfl⟩ : syracuseStep 1206867 = 1810301) B1810301
theorem B1206883 : Blo 1206420 1206883 := bstep (se 1 (by rfl) ⟨905162, by rfl⟩ : syracuseStep 1206883 = 1810325) B1810325
theorem B5155427 : Blo 1206420 5155427 := bstep (se 1 (by rfl) ⟨3866570, by rfl⟩ : syracuseStep 5155427 = 7733141) B7733141
theorem B4074083 : Blo 1206420 4074083 := bstep (se 1 (by rfl) ⟨3055562, by rfl⟩ : syracuseStep 4074083 = 6111125) B6111125
theorem B1206899 : Blo 1206420 1206899 := bstep (se 1 (by rfl) ⟨905174, by rfl⟩ : syracuseStep 1206899 = 1810349) B1810349
theorem B1206915 : Blo 1206420 1206915 := bstep (se 1 (by rfl) ⟨905186, by rfl⟩ : syracuseStep 1206915 = 1810373) B1810373
theorem B1206931 : Blo 1206420 1206931 := bstep (se 1 (by rfl) ⟨905198, by rfl⟩ : syracuseStep 1206931 = 1810397) B1810397
theorem B1206947 : Blo 1206420 1206947 := bstep (se 1 (by rfl) ⟨905210, by rfl⟩ : syracuseStep 1206947 = 1810421) B1810421
theorem B1206963 : Blo 1206420 1206963 := bstep (se 1 (by rfl) ⟨905222, by rfl⟩ : syracuseStep 1206963 = 1810445) B1810445
theorem B1223363 : Blo 1206420 1223363 := bstep (se 1 (by rfl) ⟨917522, by rfl⟩ : syracuseStep 1223363 = 1835045) B1835045
theorem B1206979 : Blo 1206420 1206979 := bstep (se 1 (by rfl) ⟨905234, by rfl⟩ : syracuseStep 1206979 = 1810469) B1810469
theorem B1206995 : Blo 1206420 1206995 := bstep (se 1 (by rfl) ⟨905246, by rfl⟩ : syracuseStep 1206995 = 1810493) B1810493
theorem B4582115 : Blo 1206420 4582115 := bstep (se 1 (by rfl) ⟨3436586, by rfl⟩ : syracuseStep 4582115 = 6873173) B6873173
theorem B1207011 : Blo 1206420 1207011 := bstep (se 1 (by rfl) ⟨905258, by rfl⟩ : syracuseStep 1207011 = 1810517) B1810517
theorem B4582129 : Blo 1206420 4582129 := bstep (se 2 (by rfl) ⟨1718298, by rfl⟩ : syracuseStep 4582129 = 3436597) B3436597
theorem B1207027 : Blo 1206420 1207027 := bstep (se 1 (by rfl) ⟨905270, by rfl⟩ : syracuseStep 1207027 = 1810541) B1810541
theorem B1207043 : Blo 1206420 1207043 := bstep (se 1 (by rfl) ⟨905282, by rfl⟩ : syracuseStep 1207043 = 1810565) B1810565
theorem B3869453 : Blo 1206420 3869453 := bstep (se 3 (by rfl) ⟨725522, by rfl⟩ : syracuseStep 3869453 = 1451045) B1451045
theorem B1207059 : Blo 1206420 1207059 := bstep (se 1 (by rfl) ⟨905294, by rfl⟩ : syracuseStep 1207059 = 1810589) B1810589
theorem B1207075 : Blo 1206420 1207075 := bstep (se 1 (by rfl) ⟨905306, by rfl⟩ : syracuseStep 1207075 = 1810613) B1810613
theorem B1207091 : Blo 1206420 1207091 := bstep (se 1 (by rfl) ⟨905318, by rfl⟩ : syracuseStep 1207091 = 1810637) B1810637
theorem B1207107 : Blo 1206420 1207107 := bstep (se 1 (by rfl) ⟨905330, by rfl⟩ : syracuseStep 1207107 = 1810661) B1810661
theorem B1207123 : Blo 1206420 1207123 := bstep (se 1 (by rfl) ⟨905342, by rfl⟩ : syracuseStep 1207123 = 1810685) B1810685
theorem B1207139 : Blo 1206420 1207139 := bstep (se 1 (by rfl) ⟨905354, by rfl⟩ : syracuseStep 1207139 = 1810709) B1810709
theorem B9161585 : Blo 1206420 9161585 := bstep (se 2 (by rfl) ⟨3435594, by rfl⟩ : syracuseStep 9161585 = 6871189) B6871189
theorem B1207155 : Blo 1206420 1207155 := bstep (se 1 (by rfl) ⟨905366, by rfl⟩ : syracuseStep 1207155 = 1810733) B1810733
theorem B4074353 : Blo 1206420 4074353 := bstep (se 2 (by rfl) ⟨1527882, by rfl⟩ : syracuseStep 4074353 = 3055765) B3055765
theorem B1207171 : Blo 1206420 1207171 := bstep (se 1 (by rfl) ⟨905378, by rfl⟩ : syracuseStep 1207171 = 1810757) B1810757
theorem B1207187 : Blo 1206420 1207187 := bstep (se 1 (by rfl) ⟨905390, by rfl⟩ : syracuseStep 1207187 = 1810781) B1810781
theorem B1207203 : Blo 1206420 1207203 := bstep (se 1 (by rfl) ⟨905402, by rfl⟩ : syracuseStep 1207203 = 1810805) B1810805
theorem B1207219 : Blo 1206420 1207219 := bstep (se 1 (by rfl) ⟨905414, by rfl⟩ : syracuseStep 1207219 = 1810829) B1810829
theorem B1207235 : Blo 1206420 1207235 := bstep (se 1 (by rfl) ⟨905426, by rfl⟩ : syracuseStep 1207235 = 1810853) B1810853
theorem B1207251 : Blo 1206420 1207251 := bstep (se 1 (by rfl) ⟨905438, by rfl⟩ : syracuseStep 1207251 = 1810877) B1810877
theorem B1207267 : Blo 1206420 1207267 := bstep (se 1 (by rfl) ⟨905450, by rfl⟩ : syracuseStep 1207267 = 1810901) B1810901
theorem B1207283 : Blo 1206420 1207283 := bstep (se 1 (by rfl) ⟨905462, by rfl⟩ : syracuseStep 1207283 = 1810925) B1810925
theorem B1207299 : Blo 1206420 1207299 := bstep (se 1 (by rfl) ⟨905474, by rfl⟩ : syracuseStep 1207299 = 1810949) B1810949
theorem B1207315 : Blo 1206420 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B1207331 : Blo 1206420 1207331 := bstep (se 1 (by rfl) ⟨905498, by rfl⟩ : syracuseStep 1207331 = 1810997) B1810997
theorem B1207347 : Blo 1206420 1207347 := bstep (se 1 (by rfl) ⟨905510, by rfl⟩ : syracuseStep 1207347 = 1811021) B1811021
theorem B1207363 : Blo 1206420 1207363 := bstep (se 1 (by rfl) ⟨905522, by rfl⟩ : syracuseStep 1207363 = 1811045) B1811045
theorem B4131917 : Blo 1206420 4131917 := bstep (se 3 (by rfl) ⟨774734, by rfl⟩ : syracuseStep 4131917 = 1549469) B1549469
theorem B2714705 : Blo 1206420 2714705 := bstep (se 2 (by rfl) ⟨1018014, by rfl⟩ : syracuseStep 2714705 = 2036029) B2036029
theorem B1207379 : Blo 1206420 1207379 := bstep (se 1 (by rfl) ⟨905534, by rfl⟩ : syracuseStep 1207379 = 1811069) B1811069
theorem B2714723 : Blo 1206420 2714723 := bstep (se 1 (by rfl) ⟨2036042, by rfl⟩ : syracuseStep 2714723 = 4072085) B4072085
theorem B1207395 : Blo 1206420 1207395 := bstep (se 1 (by rfl) ⟨905546, by rfl⟩ : syracuseStep 1207395 = 1811093) B1811093
theorem B37162097 : Blo 1206420 37162097 := bstep (se 2 (by rfl) ⟨13935786, by rfl⟩ : syracuseStep 37162097 = 27871573) B27871573
theorem B1207411 : Blo 1206420 1207411 := bstep (se 1 (by rfl) ⟨905558, by rfl⟩ : syracuseStep 1207411 = 1811117) B1811117
theorem B1207427 : Blo 1206420 1207427 := bstep (se 1 (by rfl) ⟨905570, by rfl⟩ : syracuseStep 1207427 = 1811141) B1811141
theorem B1207443 : Blo 1206420 1207443 := bstep (se 1 (by rfl) ⟨905582, by rfl⟩ : syracuseStep 1207443 = 1811165) B1811165
theorem B1207459 : Blo 1206420 1207459 := bstep (se 1 (by rfl) ⟨905594, by rfl⟩ : syracuseStep 1207459 = 1811189) B1811189
theorem B1207475 : Blo 1206420 1207475 := bstep (se 1 (by rfl) ⟨905606, by rfl⟩ : syracuseStep 1207475 = 1811213) B1811213
theorem B1207491 : Blo 1206420 1207491 := bstep (se 1 (by rfl) ⟨905618, by rfl⟩ : syracuseStep 1207491 = 1811237) B1811237
theorem B2174161 : Blo 1206420 2174161 := bstep (se 2 (by rfl) ⟨815310, by rfl⟩ : syracuseStep 2174161 = 1630621) B1630621
theorem B1207507 : Blo 1206420 1207507 := bstep (se 1 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 1207507 = 1811261) B1811261
theorem B1207523 : Blo 1206420 1207523 := bstep (se 1 (by rfl) ⟨905642, by rfl⟩ : syracuseStep 1207523 = 1811285) B1811285
theorem B1289459 : Blo 1206420 1289459 := bstep (se 1 (by rfl) ⟨967094, by rfl⟩ : syracuseStep 1289459 = 1934189) B1934189
theorem B1207539 : Blo 1206420 1207539 := bstep (se 1 (by rfl) ⟨905654, by rfl⟩ : syracuseStep 1207539 = 1811309) B1811309
theorem B1207555 : Blo 1206420 1207555 := bstep (se 1 (by rfl) ⟨905666, by rfl⟩ : syracuseStep 1207555 = 1811333) B1811333
theorem B1207571 : Blo 1206420 1207571 := bstep (se 1 (by rfl) ⟨905678, by rfl⟩ : syracuseStep 1207571 = 1811357) B1811357
theorem B1207587 : Blo 1206420 1207587 := bstep (se 1 (by rfl) ⟨905690, by rfl⟩ : syracuseStep 1207587 = 1811381) B1811381
theorem B1207603 : Blo 1206420 1207603 := bstep (se 1 (by rfl) ⟨905702, by rfl⟩ : syracuseStep 1207603 = 1811405) B1811405
theorem B13045045 : Blo 1206420 13045045 := bstep (se 5 (by rfl) ⟨611486, by rfl⟩ : syracuseStep 13045045 = 1222973) B1222973
theorem B1207619 : Blo 1206420 1207619 := bstep (se 1 (by rfl) ⟨905714, by rfl⟩ : syracuseStep 1207619 = 1811429) B1811429
theorem B1207635 : Blo 1206420 1207635 := bstep (se 1 (by rfl) ⟨905726, by rfl⟩ : syracuseStep 1207635 = 1811453) B1811453
theorem B1207651 : Blo 1206420 1207651 := bstep (se 1 (by rfl) ⟨905738, by rfl⟩ : syracuseStep 1207651 = 1811477) B1811477
theorem B2714993 : Blo 1206420 2714993 := bstep (se 2 (by rfl) ⟨1018122, by rfl⟩ : syracuseStep 2714993 = 2036245) B2036245
theorem B1207667 : Blo 1206420 1207667 := bstep (se 1 (by rfl) ⟨905750, by rfl⟩ : syracuseStep 1207667 = 1811501) B1811501
theorem B2715011 : Blo 1206420 2715011 := bstep (se 1 (by rfl) ⟨2036258, by rfl⟩ : syracuseStep 2715011 = 4072517) B4072517
theorem B1207683 : Blo 1206420 1207683 := bstep (se 1 (by rfl) ⟨905762, by rfl⟩ : syracuseStep 1207683 = 1811525) B1811525
theorem B4074893 : Blo 1206420 4074893 := bstep (se 3 (by rfl) ⟨764042, by rfl⟩ : syracuseStep 4074893 = 1528085) B1528085
theorem B1207699 : Blo 1206420 1207699 := bstep (se 1 (by rfl) ⟨905774, by rfl⟩ : syracuseStep 1207699 = 1811549) B1811549
theorem B1207715 : Blo 1206420 1207715 := bstep (se 1 (by rfl) ⟨905786, by rfl⟩ : syracuseStep 1207715 = 1811573) B1811573
theorem B1207731 : Blo 1206420 1207731 := bstep (se 1 (by rfl) ⟨905798, by rfl⟩ : syracuseStep 1207731 = 1811597) B1811597
theorem B4074947 : Blo 1206420 4074947 := bstep (se 1 (by rfl) ⟨3056210, by rfl⟩ : syracuseStep 4074947 = 6112421) B6112421
theorem B1207747 : Blo 1206420 1207747 := bstep (se 1 (by rfl) ⟨905810, by rfl⟩ : syracuseStep 1207747 = 1811621) B1811621
theorem B1207763 : Blo 1206420 1207763 := bstep (se 1 (by rfl) ⟨905822, by rfl⟩ : syracuseStep 1207763 = 1811645) B1811645
theorem B1207779 : Blo 1206420 1207779 := bstep (se 1 (by rfl) ⟨905834, by rfl⟩ : syracuseStep 1207779 = 1811669) B1811669
theorem B1207795 : Blo 1206420 1207795 := bstep (se 1 (by rfl) ⟨905846, by rfl⟩ : syracuseStep 1207795 = 1811693) B1811693
theorem B1207811 : Blo 1206420 1207811 := bstep (se 1 (by rfl) ⟨905858, by rfl⟩ : syracuseStep 1207811 = 1811717) B1811717
theorem B1207827 : Blo 1206420 1207827 := bstep (se 1 (by rfl) ⟨905870, by rfl⟩ : syracuseStep 1207827 = 1811741) B1811741
theorem B1527331 : Blo 1206420 1527331 := bstep (se 1 (by rfl) ⟨1145498, by rfl⟩ : syracuseStep 1527331 = 2290997) B2290997
theorem B1207843 : Blo 1206420 1207843 := bstep (se 1 (by rfl) ⟨905882, by rfl⟩ : syracuseStep 1207843 = 1811765) B1811765
theorem B6114851 : Blo 1206420 6114851 := bstep (se 1 (by rfl) ⟨4586138, by rfl⟩ : syracuseStep 6114851 = 9172277) B9172277
theorem B1207859 : Blo 1206420 1207859 := bstep (se 1 (by rfl) ⟨905894, by rfl⟩ : syracuseStep 1207859 = 1811789) B1811789
theorem B1207875 : Blo 1206420 1207875 := bstep (se 1 (by rfl) ⟨905906, by rfl⟩ : syracuseStep 1207875 = 1811813) B1811813
theorem B1207891 : Blo 1206420 1207891 := bstep (se 1 (by rfl) ⟨905918, by rfl⟩ : syracuseStep 1207891 = 1811837) B1811837
theorem B1207907 : Blo 1206420 1207907 := bstep (se 1 (by rfl) ⟨905930, by rfl⟩ : syracuseStep 1207907 = 1811861) B1811861
theorem B1527427 : Blo 1206420 1527427 := bstep (se 1 (by rfl) ⟨1145570, by rfl⟩ : syracuseStep 1527427 = 2291141) B2291141
theorem B2715281 : Blo 1206420 2715281 := bstep (se 2 (by rfl) ⟨1018230, by rfl⟩ : syracuseStep 2715281 = 2036461) B2036461
theorem B2715299 : Blo 1206420 2715299 := bstep (se 1 (by rfl) ⟨2036474, by rfl⟩ : syracuseStep 2715299 = 4072949) B4072949
theorem B4075217 : Blo 1206420 4075217 := bstep (se 2 (by rfl) ⟨1528206, by rfl⟩ : syracuseStep 4075217 = 3056413) B3056413
theorem B7737059 : Blo 1206420 7737059 := bstep (se 1 (by rfl) ⟨5802794, by rfl⟩ : syracuseStep 7737059 = 11605589) B11605589
theorem B24792803 : Blo 1206420 24792803 := bstep (se 1 (by rfl) ⟨18594602, by rfl⟩ : syracuseStep 24792803 = 37189205) B37189205
theorem B2715569 : Blo 1206420 2715569 := bstep (se 2 (by rfl) ⟨1018338, by rfl⟩ : syracuseStep 2715569 = 2036677) B2036677
theorem B2715587 : Blo 1206420 2715587 := bstep (se 1 (by rfl) ⟨2036690, by rfl⟩ : syracuseStep 2715587 = 4073381) B4073381
theorem B28643381 : Blo 1206420 28643381 := bstep (se 5 (by rfl) ⟨1342658, by rfl⟩ : syracuseStep 28643381 = 2685317) B2685317
theorem B3436643 : Blo 1206420 3436643 := bstep (se 1 (by rfl) ⟨2577482, by rfl⟩ : syracuseStep 3436643 = 5154965) B5154965
theorem B1527923 : Blo 1206420 1527923 := bstep (se 1 (by rfl) ⟨1145942, by rfl⟩ : syracuseStep 1527923 = 2291885) B2291885
theorem B4583587 : Blo 1206420 4583587 := bstep (se 1 (by rfl) ⟨3437690, by rfl⟩ : syracuseStep 4583587 = 6875381) B6875381
theorem B2035921 : Blo 1206420 2035921 := bstep (se 2 (by rfl) ⟨763470, by rfl⟩ : syracuseStep 2035921 = 1526941) B1526941
theorem B2715857 : Blo 1206420 2715857 := bstep (se 2 (by rfl) ⟨1018446, by rfl⟩ : syracuseStep 2715857 = 2036893) B2036893
theorem B2715875 : Blo 1206420 2715875 := bstep (se 1 (by rfl) ⟨2036906, by rfl⟩ : syracuseStep 2715875 = 4073813) B4073813
theorem B4075757 : Blo 1206420 4075757 := bstep (se 3 (by rfl) ⟨764204, by rfl⟩ : syracuseStep 4075757 = 1528409) B1528409
theorem B2035955 : Blo 1206420 2035955 := bstep (se 1 (by rfl) ⟨1526966, by rfl⟩ : syracuseStep 2035955 = 3053933) B3053933
theorem B67883285 : Blo 1206420 67883285 := bstep (se 6 (by rfl) ⟨1591014, by rfl⟩ : syracuseStep 67883285 = 3182029) B3182029
theorem B4075811 : Blo 1206420 4075811 := bstep (se 1 (by rfl) ⟨3056858, by rfl⟩ : syracuseStep 4075811 = 6113717) B6113717
theorem B2355569 : Blo 1206420 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B2036083 : Blo 1206420 2036083 := bstep (se 1 (by rfl) ⟨1527062, by rfl⟩ : syracuseStep 2036083 = 3054125) B3054125
theorem B8704397 : Blo 1206420 8704397 := bstep (se 3 (by rfl) ⟨1632074, by rfl⟩ : syracuseStep 8704397 = 3264149) B3264149
theorem B2716145 : Blo 1206420 2716145 := bstep (se 2 (by rfl) ⟨1018554, by rfl⟩ : syracuseStep 2716145 = 2037109) B2037109
theorem B2036225 : Blo 1206420 2036225 := bstep (se 2 (by rfl) ⟨763584, by rfl⟩ : syracuseStep 2036225 = 1527169) B1527169
theorem B2716163 : Blo 1206420 2716163 := bstep (se 1 (by rfl) ⟨2037122, by rfl⟩ : syracuseStep 2716163 = 4074245) B4074245
theorem B3265069 : Blo 1206420 3265069 := bstep (se 3 (by rfl) ⟨612200, by rfl⟩ : syracuseStep 3265069 = 1224401) B1224401
theorem B5157425 : Blo 1206420 5157425 := bstep (se 2 (by rfl) ⟨1934034, by rfl⟩ : syracuseStep 5157425 = 3868069) B3868069
theorem B4076081 : Blo 1206420 4076081 := bstep (se 2 (by rfl) ⟨1528530, by rfl⟩ : syracuseStep 4076081 = 3057061) B3057061
theorem B2036353 : Blo 1206420 2036353 := bstep (se 2 (by rfl) ⟨763632, by rfl⟩ : syracuseStep 2036353 = 1527265) B1527265
theorem B2036387 : Blo 1206420 2036387 := bstep (se 1 (by rfl) ⟨1527290, by rfl⟩ : syracuseStep 2036387 = 3054581) B3054581
theorem B2716433 : Blo 1206420 2716433 := bstep (se 2 (by rfl) ⟨1018662, by rfl⟩ : syracuseStep 2716433 = 2037325) B2037325
theorem B2036515 : Blo 1206420 2036515 := bstep (se 1 (by rfl) ⟨1527386, by rfl⟩ : syracuseStep 2036515 = 3054773) B3054773
theorem B2716451 : Blo 1206420 2716451 := bstep (se 1 (by rfl) ⟨2037338, by rfl⟩ : syracuseStep 2716451 = 4074677) B4074677
theorem B1528627 : Blo 1206420 1528627 := bstep (se 1 (by rfl) ⟨1146470, by rfl⟩ : syracuseStep 1528627 = 2292941) B2292941
theorem B6968177 : Blo 1206420 6968177 := bstep (se 2 (by rfl) ⟨2613066, by rfl⟩ : syracuseStep 6968177 = 5226133) B5226133
theorem B1528723 : Blo 1206420 1528723 := bstep (se 1 (by rfl) ⟨1146542, by rfl⟩ : syracuseStep 1528723 = 2293085) B2293085
theorem B2290609 : Blo 1206420 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B2577329 : Blo 1206420 2577329 := bstep (se 2 (by rfl) ⟨966498, by rfl⟩ : syracuseStep 2577329 = 1932997) B1932997
theorem B2036657 : Blo 1206420 2036657 := bstep (se 2 (by rfl) ⟨763746, by rfl⟩ : syracuseStep 2036657 = 1527493) B1527493
theorem B6108209 : Blo 1206420 6108209 := bstep (se 2 (by rfl) ⟨2290578, by rfl⟩ : syracuseStep 6108209 = 4581157) B4581157
theorem B2036785 : Blo 1206420 2036785 := bstep (se 2 (by rfl) ⟨763794, by rfl⟩ : syracuseStep 2036785 = 1527589) B1527589
theorem B2716721 : Blo 1206420 2716721 := bstep (se 2 (by rfl) ⟨1018770, by rfl⟩ : syracuseStep 2716721 = 2037541) B2037541
theorem B2716739 : Blo 1206420 2716739 := bstep (se 1 (by rfl) ⟨2037554, by rfl⟩ : syracuseStep 2716739 = 4075109) B4075109
theorem B4076621 : Blo 1206420 4076621 := bstep (se 3 (by rfl) ⟨764366, by rfl⟩ : syracuseStep 4076621 = 1528733) B1528733
theorem B2036819 : Blo 1206420 2036819 := bstep (se 1 (by rfl) ⟨1527614, by rfl⟩ : syracuseStep 2036819 = 3055229) B3055229
theorem B4076675 : Blo 1206420 4076675 := bstep (se 1 (by rfl) ⟨3057506, by rfl⟩ : syracuseStep 4076675 = 6115013) B6115013
theorem B2036947 : Blo 1206420 2036947 := bstep (se 1 (by rfl) ⟨1527710, by rfl⟩ : syracuseStep 2036947 = 3055421) B3055421
theorem B58758371 : Blo 1206420 58758371 := bstep (se 1 (by rfl) ⟨44068778, by rfl⟩ : syracuseStep 58758371 = 88137557) B88137557
theorem B3437873 : Blo 1206420 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B2717009 : Blo 1206420 2717009 := bstep (se 2 (by rfl) ⟨1018878, by rfl⟩ : syracuseStep 2717009 = 2037757) B2037757
theorem B2176337 : Blo 1206420 2176337 := bstep (se 2 (by rfl) ⟨816126, by rfl⟩ : syracuseStep 2176337 = 1632253) B1632253
theorem B2037089 : Blo 1206420 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B2717027 : Blo 1206420 2717027 := bstep (se 1 (by rfl) ⟨2037770, by rfl⟩ : syracuseStep 2717027 = 4075541) B4075541
theorem B5158349 : Blo 1206420 5158349 := bstep (se 3 (by rfl) ⟨967190, by rfl⟩ : syracuseStep 5158349 = 1934381) B1934381
theorem B1357267 : Blo 1206420 1357267 := bstep (se 1 (by rfl) ⟨1017950, by rfl⟩ : syracuseStep 1357267 = 2035901) B2035901
theorem B2037217 : Blo 1206420 2037217 := bstep (se 2 (by rfl) ⟨763956, by rfl⟩ : syracuseStep 2037217 = 1527913) B1527913
theorem B1570291 : Blo 1206420 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B2037251 : Blo 1206420 2037251 := bstep (se 1 (by rfl) ⟨1527938, by rfl⟩ : syracuseStep 2037251 = 3055877) B3055877
theorem B2176561 : Blo 1206420 2176561 := bstep (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) B1632421
theorem B5797453 : Blo 1206420 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B2233937 : Blo 1206420 2233937 := bstep (se 2 (by rfl) ⟨837726, by rfl⟩ : syracuseStep 2233937 = 1675453) B1675453
theorem B1717843 : Blo 1206420 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B1357411 : Blo 1206420 1357411 := bstep (se 1 (by rfl) ⟨1018058, by rfl⟩ : syracuseStep 1357411 = 2036117) B2036117
theorem B2717297 : Blo 1206420 2717297 := bstep (se 2 (by rfl) ⟨1018986, by rfl⟩ : syracuseStep 2717297 = 2037973) B2037973
theorem B2037379 : Blo 1206420 2037379 := bstep (se 1 (by rfl) ⟨1528034, by rfl⟩ : syracuseStep 2037379 = 3056069) B3056069
theorem B2717315 : Blo 1206420 2717315 := bstep (se 1 (by rfl) ⟨2037986, by rfl⟩ : syracuseStep 2717315 = 4075973) B4075973
theorem B1357555 : Blo 1206420 1357555 := bstep (se 1 (by rfl) ⟨1018166, by rfl⟩ : syracuseStep 1357555 = 2036333) B2036333
theorem B2037521 : Blo 1206420 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B127112981 : Blo 1206420 127112981 := bstep (se 6 (by rfl) ⟨2979210, by rfl⟩ : syracuseStep 127112981 = 5958421) B5958421
theorem B12392291 : Blo 1206420 12392291 := bstep (se 1 (by rfl) ⟨9294218, by rfl⟩ : syracuseStep 12392291 = 18588437) B18588437
theorem B1357699 : Blo 1206420 1357699 := bstep (se 1 (by rfl) ⟨1018274, by rfl⟩ : syracuseStep 1357699 = 2036549) B2036549
theorem B2037649 : Blo 1206420 2037649 := bstep (se 2 (by rfl) ⟨764118, by rfl⟩ : syracuseStep 2037649 = 1528237) B1528237
theorem B2717585 : Blo 1206420 2717585 := bstep (se 2 (by rfl) ⟨1019094, by rfl⟩ : syracuseStep 2717585 = 2038189) B2038189
theorem B2717603 : Blo 1206420 2717603 := bstep (se 1 (by rfl) ⟨2038202, by rfl⟩ : syracuseStep 2717603 = 4076405) B4076405
theorem B2037683 : Blo 1206420 2037683 := bstep (se 1 (by rfl) ⟨1528262, by rfl⟩ : syracuseStep 2037683 = 3056525) B3056525
theorem B2291665 : Blo 1206420 2291665 := bstep (se 2 (by rfl) ⟨859374, by rfl⟩ : syracuseStep 2291665 = 1718749) B1718749
theorem B1357843 : Blo 1206420 1357843 := bstep (se 1 (by rfl) ⟨1018382, by rfl⟩ : syracuseStep 1357843 = 2036765) B2036765
theorem B2037811 : Blo 1206420 2037811 := bstep (se 1 (by rfl) ⟨1528358, by rfl⟩ : syracuseStep 2037811 = 3056717) B3056717
theorem B1357987 : Blo 1206420 1357987 := bstep (se 1 (by rfl) ⟨1018490, by rfl⟩ : syracuseStep 1357987 = 2036981) B2036981
theorem B2037953 : Blo 1206420 2037953 := bstep (se 2 (by rfl) ⟨764232, by rfl⟩ : syracuseStep 2037953 = 1528465) B1528465
theorem B6879437 : Blo 1206420 6879437 := bstep (se 3 (by rfl) ⟨1289894, by rfl⟩ : syracuseStep 6879437 = 2579789) B2579789
theorem B1358131 : Blo 1206420 1358131 := bstep (se 1 (by rfl) ⟨1018598, by rfl⟩ : syracuseStep 1358131 = 2037197) B2037197
theorem B2038081 : Blo 1206420 2038081 := bstep (se 2 (by rfl) ⟨764280, by rfl⟩ : syracuseStep 2038081 = 1528561) B1528561
theorem B4585805 : Blo 1206420 4585805 := bstep (se 3 (by rfl) ⟨859838, by rfl⟩ : syracuseStep 4585805 = 1719677) B1719677
theorem B2292067 : Blo 1206420 2292067 := bstep (se 1 (by rfl) ⟨1719050, by rfl⟩ : syracuseStep 2292067 = 3438101) B3438101
theorem B2038115 : Blo 1206420 2038115 := bstep (se 1 (by rfl) ⟨1528586, by rfl⟩ : syracuseStep 2038115 = 3057173) B3057173
theorem B2447747 : Blo 1206420 2447747 := bstep (se 1 (by rfl) ⟨1835810, by rfl⟩ : syracuseStep 2447747 = 3671621) B3671621
theorem B2292113 : Blo 1206420 2292113 := bstep (se 2 (by rfl) ⟨859542, by rfl⟩ : syracuseStep 2292113 = 1719085) B1719085
theorem B13744565 : Blo 1206420 13744565 := bstep (se 5 (by rfl) ⟨644276, by rfl⟩ : syracuseStep 13744565 = 1288553) B1288553
theorem B1358275 : Blo 1206420 1358275 := bstep (se 1 (by rfl) ⟨1018706, by rfl⟩ : syracuseStep 1358275 = 2037413) B2037413
theorem B2578883 : Blo 1206420 2578883 := bstep (se 1 (by rfl) ⟨1934162, by rfl⟩ : syracuseStep 2578883 = 3868325) B3868325
theorem B6109667 : Blo 1206420 6109667 := bstep (se 1 (by rfl) ⟨4582250, by rfl⟩ : syracuseStep 6109667 = 9164501) B9164501
theorem B2038243 : Blo 1206420 2038243 := bstep (se 1 (by rfl) ⟨1528682, by rfl⟩ : syracuseStep 2038243 = 3057365) B3057365
theorem B14678597 : Blo 1206420 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B1358419 : Blo 1206420 1358419 := bstep (se 1 (by rfl) ⟨1018814, by rfl⟩ : syracuseStep 1358419 = 2037629) B2037629
theorem B6871715 : Blo 1206420 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B3054257 : Blo 1206420 3054257 := bstep (se 2 (by rfl) ⟨1145346, by rfl⟩ : syracuseStep 3054257 = 2290693) B2290693
theorem B2292401 : Blo 1206420 2292401 := bstep (se 2 (by rfl) ⟨859650, by rfl⟩ : syracuseStep 2292401 = 1719301) B1719301
theorem B1718977 : Blo 1206420 1718977 := bstep (se 2 (by rfl) ⟨644616, by rfl⟩ : syracuseStep 1718977 = 1289233) B1289233
theorem B3054307 : Blo 1206420 3054307 := bstep (se 1 (by rfl) ⟨2290730, by rfl⟩ : syracuseStep 3054307 = 4581461) B4581461
theorem B5798627 : Blo 1206420 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B1358563 : Blo 1206420 1358563 := bstep (se 1 (by rfl) ⟨1018922, by rfl⟩ : syracuseStep 1358563 = 2037845) B2037845
theorem B3439331 : Blo 1206420 3439331 := bstep (se 1 (by rfl) ⟨2579498, by rfl⟩ : syracuseStep 3439331 = 5158997) B5158997
theorem B1719073 : Blo 1206420 1719073 := bstep (se 2 (by rfl) ⟨644652, by rfl⟩ : syracuseStep 1719073 = 1289305) B1289305
theorem B7732037 : Blo 1206420 7732037 := bstep (se 4 (by rfl) ⟨724878, by rfl⟩ : syracuseStep 7732037 = 1449757) B1449757
theorem B3054449 : Blo 1206420 3054449 := bstep (se 2 (by rfl) ⟨1145418, by rfl⟩ : syracuseStep 3054449 = 2290837) B2290837
theorem B1358707 : Blo 1206420 1358707 := bstep (se 1 (by rfl) ⟨1019030, by rfl⟩ : syracuseStep 1358707 = 2038061) B2038061
theorem B2898929 : Blo 1206420 2898929 := bstep (se 2 (by rfl) ⟨1087098, by rfl⟩ : syracuseStep 2898929 = 2174197) B2174197
theorem B1358851 : Blo 1206420 1358851 := bstep (se 1 (by rfl) ⟨1019138, by rfl⟩ : syracuseStep 1358851 = 2038277) B2038277
theorem B4709389 : Blo 1206420 4709389 := bstep (se 3 (by rfl) ⟨883010, by rfl⟩ : syracuseStep 4709389 = 1766021) B1766021
theorem B4643939 : Blo 1206420 4643939 := bstep (se 1 (by rfl) ⟨3482954, by rfl⟩ : syracuseStep 4643939 = 6965909) B6965909
theorem B1809635 : Blo 1206420 1809635 := bstep (se 1 (by rfl) ⟨1357226, by rfl⟩ : syracuseStep 1809635 = 2714453) B2714453
theorem B1809665 : Blo 1206420 1809665 := bstep (se 2 (by rfl) ⟨678624, by rfl⟩ : syracuseStep 1809665 = 1357249) B1357249
theorem B6110477 : Blo 1206420 6110477 := bstep (se 3 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 6110477 = 2291429) B2291429
theorem B1719569 : Blo 1206420 1719569 := bstep (se 2 (by rfl) ⟨644838, by rfl⟩ : syracuseStep 1719569 = 1289677) B1289677
theorem B1809683 : Blo 1206420 1809683 := bstep (se 1 (by rfl) ⟨1357262, by rfl⟩ : syracuseStep 1809683 = 2714525) B2714525
theorem B1809713 : Blo 1206420 1809713 := bstep (se 2 (by rfl) ⟨678642, by rfl⟩ : syracuseStep 1809713 = 1357285) B1357285
theorem B1809731 : Blo 1206420 1809731 := bstep (se 1 (by rfl) ⟨1357298, by rfl⟩ : syracuseStep 1809731 = 2714597) B2714597
theorem B1809761 : Blo 1206420 1809761 := bstep (se 2 (by rfl) ⟨678660, by rfl⟩ : syracuseStep 1809761 = 1357321) B1357321
theorem B1809779 : Blo 1206420 1809779 := bstep (se 1 (by rfl) ⟨1357334, by rfl⟩ : syracuseStep 1809779 = 2714669) B2714669
theorem B2293123 : Blo 1206420 2293123 := bstep (se 1 (by rfl) ⟨1719842, by rfl⟩ : syracuseStep 2293123 = 3439685) B3439685
theorem B1809809 : Blo 1206420 1809809 := bstep (se 2 (by rfl) ⟨678678, by rfl⟩ : syracuseStep 1809809 = 1357357) B1357357
theorem B1809827 : Blo 1206420 1809827 := bstep (se 1 (by rfl) ⟨1357370, by rfl⟩ : syracuseStep 1809827 = 2714741) B2714741
theorem B1809857 : Blo 1206420 1809857 := bstep (se 2 (by rfl) ⟨678696, by rfl⟩ : syracuseStep 1809857 = 1357393) B1357393
theorem B1809875 : Blo 1206420 1809875 := bstep (se 1 (by rfl) ⟨1357406, by rfl⟩ : syracuseStep 1809875 = 2714813) B2714813
theorem B1809905 : Blo 1206420 1809905 := bstep (se 2 (by rfl) ⟨678714, by rfl⟩ : syracuseStep 1809905 = 1357429) B1357429
theorem B1809923 : Blo 1206420 1809923 := bstep (se 1 (by rfl) ⟨1357442, by rfl⟩ : syracuseStep 1809923 = 2714885) B2714885
theorem B1809953 : Blo 1206420 1809953 := bstep (se 2 (by rfl) ⟨678732, by rfl⟩ : syracuseStep 1809953 = 1357465) B1357465
theorem B1809971 : Blo 1206420 1809971 := bstep (se 1 (by rfl) ⟨1357478, by rfl⟩ : syracuseStep 1809971 = 2714957) B2714957
theorem B7839301 : Blo 1206420 7839301 := bstep (se 4 (by rfl) ⟨734934, by rfl⟩ : syracuseStep 7839301 = 1469869) B1469869
theorem B1810001 : Blo 1206420 1810001 := bstep (se 2 (by rfl) ⟨678750, by rfl⟩ : syracuseStep 1810001 = 1357501) B1357501
theorem B1932881 : Blo 1206420 1932881 := bstep (se 2 (by rfl) ⟨724830, by rfl⟩ : syracuseStep 1932881 = 1449661) B1449661
theorem B1810019 : Blo 1206420 1810019 := bstep (se 1 (by rfl) ⟨1357514, by rfl⟩ : syracuseStep 1810019 = 2715029) B2715029
theorem B1810049 : Blo 1206420 1810049 := bstep (se 2 (by rfl) ⟨678768, by rfl⟩ : syracuseStep 1810049 = 1357537) B1357537
theorem B1810067 : Blo 1206420 1810067 := bstep (se 1 (by rfl) ⟨1357550, by rfl⟩ : syracuseStep 1810067 = 2715101) B2715101
theorem B1810097 : Blo 1206420 1810097 := bstep (se 2 (by rfl) ⟨678786, by rfl⟩ : syracuseStep 1810097 = 1357573) B1357573
theorem B1810115 : Blo 1206420 1810115 := bstep (se 1 (by rfl) ⟨1357586, by rfl⟩ : syracuseStep 1810115 = 2715173) B2715173
theorem B1810145 : Blo 1206420 1810145 := bstep (se 2 (by rfl) ⟨678804, by rfl⟩ : syracuseStep 1810145 = 1357609) B1357609
theorem B1810163 : Blo 1206420 1810163 := bstep (se 1 (by rfl) ⟨1357622, by rfl⟩ : syracuseStep 1810163 = 2715245) B2715245
theorem B1810193 : Blo 1206420 1810193 := bstep (se 2 (by rfl) ⟨678822, by rfl⟩ : syracuseStep 1810193 = 1357645) B1357645
theorem B1810211 : Blo 1206420 1810211 := bstep (se 1 (by rfl) ⟨1357658, by rfl⟩ : syracuseStep 1810211 = 2715317) B2715317
theorem B1810241 : Blo 1206420 1810241 := bstep (se 2 (by rfl) ⟨678840, by rfl⟩ : syracuseStep 1810241 = 1357681) B1357681
theorem B3055441 : Blo 1206420 3055441 := bstep (se 2 (by rfl) ⟨1145790, by rfl⟩ : syracuseStep 3055441 = 2291581) B2291581
theorem B1810259 : Blo 1206420 1810259 := bstep (se 1 (by rfl) ⟨1357694, by rfl⟩ : syracuseStep 1810259 = 2715389) B2715389
theorem B1810289 : Blo 1206420 1810289 := bstep (se 2 (by rfl) ⟨678858, by rfl⟩ : syracuseStep 1810289 = 1357717) B1357717
theorem B1810307 : Blo 1206420 1810307 := bstep (se 1 (by rfl) ⟨1357730, by rfl⟩ : syracuseStep 1810307 = 2715461) B2715461
theorem B1810337 : Blo 1206420 1810337 := bstep (se 2 (by rfl) ⟨678876, by rfl⟩ : syracuseStep 1810337 = 1357753) B1357753
theorem B1810355 : Blo 1206420 1810355 := bstep (se 1 (by rfl) ⟨1357766, by rfl⟩ : syracuseStep 1810355 = 2715533) B2715533
theorem B1810385 : Blo 1206420 1810385 := bstep (se 2 (by rfl) ⟨678894, by rfl⟩ : syracuseStep 1810385 = 1357789) B1357789
theorem B1810403 : Blo 1206420 1810403 := bstep (se 1 (by rfl) ⟨1357802, by rfl⟩ : syracuseStep 1810403 = 2715605) B2715605
theorem B3866609 : Blo 1206420 3866609 := bstep (se 2 (by rfl) ⟨1449978, by rfl⟩ : syracuseStep 3866609 = 2899957) B2899957
theorem B11608049 : Blo 1206420 11608049 := bstep (se 2 (by rfl) ⟨4353018, by rfl⟩ : syracuseStep 11608049 = 8706037) B8706037
theorem B4644881 : Blo 1206420 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B1810457 : Blo 1206420 1810457 := bstep (se 2 (by rfl) ⟨678921, by rfl⟩ : syracuseStep 1810457 = 1357843) B1357843
theorem B19095587 : Blo 1206420 19095587 := bstep (se 1 (by rfl) ⟨14321690, by rfl⟩ : syracuseStep 19095587 = 28643381) B28643381
theorem B1810571 : Blo 1206420 1810571 := bstep (se 1 (by rfl) ⟨1357928, by rfl⟩ : syracuseStep 1810571 = 2715857) B2715857
theorem B1810583 : Blo 1206420 1810583 := bstep (se 1 (by rfl) ⟨1357937, by rfl⟩ : syracuseStep 1810583 = 2715875) B2715875
theorem B5505203 : Blo 1206420 5505203 := bstep (se 1 (by rfl) ⟨4128902, by rfl⟩ : syracuseStep 5505203 = 8257805) B8257805
theorem B1810649 : Blo 1206420 1810649 := bstep (se 2 (by rfl) ⟨678993, by rfl⟩ : syracuseStep 1810649 = 1357987) B1357987
theorem B6111449 : Blo 1206420 6111449 := bstep (se 2 (by rfl) ⟨2291793, by rfl⟩ : syracuseStep 6111449 = 4583587) B4583587
theorem B1810763 : Blo 1206420 1810763 := bstep (se 1 (by rfl) ⟨1358072, by rfl⟩ : syracuseStep 1810763 = 2716145) B2716145
theorem B1810775 : Blo 1206420 1810775 := bstep (se 1 (by rfl) ⟨1358081, by rfl⟩ : syracuseStep 1810775 = 2716163) B2716163
theorem B4350353 : Blo 1206420 4350353 := bstep (se 2 (by rfl) ⟨1631382, by rfl⟩ : syracuseStep 4350353 = 3262765) B3262765
theorem B1810841 : Blo 1206420 1810841 := bstep (se 2 (by rfl) ⟨679065, by rfl⟩ : syracuseStep 1810841 = 1358131) B1358131
theorem B3056089 : Blo 1206420 3056089 := bstep (se 2 (by rfl) ⟨1146033, by rfl⟩ : syracuseStep 3056089 = 2292067) B2292067
theorem B1810955 : Blo 1206420 1810955 := bstep (se 1 (by rfl) ⟨1358216, by rfl⟩ : syracuseStep 1810955 = 2716433) B2716433
theorem B1810967 : Blo 1206420 1810967 := bstep (se 1 (by rfl) ⟨1358225, by rfl⟩ : syracuseStep 1810967 = 2716451) B2716451
theorem B9290285 : Blo 1206420 9290285 := bstep (se 3 (by rfl) ⟨1741928, by rfl⟩ : syracuseStep 9290285 = 3483857) B3483857
theorem B4645451 : Blo 1206420 4645451 := bstep (se 1 (by rfl) ⟨3484088, by rfl⟩ : syracuseStep 4645451 = 6968177) B6968177
theorem B1811033 : Blo 1206420 1811033 := bstep (se 2 (by rfl) ⟨679137, by rfl⟩ : syracuseStep 1811033 = 1358275) B1358275
theorem B2753153 : Blo 1206420 2753153 := bstep (se 2 (by rfl) ⟨1032432, by rfl⟩ : syracuseStep 2753153 = 2064865) B2064865
theorem B3670721 : Blo 1206420 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B4072139 : Blo 1206420 4072139 := bstep (se 1 (by rfl) ⟨3054104, by rfl⟩ : syracuseStep 4072139 = 6108209) B6108209
theorem B1811147 : Blo 1206420 1811147 := bstep (se 1 (by rfl) ⟨1358360, by rfl⟩ : syracuseStep 1811147 = 2716721) B2716721
theorem B1811159 : Blo 1206420 1811159 := bstep (se 1 (by rfl) ⟨1358369, by rfl⟩ : syracuseStep 1811159 = 2716739) B2716739
theorem B1811225 : Blo 1206420 1811225 := bstep (se 2 (by rfl) ⟨679209, by rfl⟩ : syracuseStep 1811225 = 1358419) B1358419
theorem B6800203 : Blo 1206420 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B5800835 : Blo 1206420 5800835 := bstep (se 1 (by rfl) ⟨4350626, by rfl⟩ : syracuseStep 5800835 = 8701253) B8701253
theorem B1811339 : Blo 1206420 1811339 := bstep (se 1 (by rfl) ⟨1358504, by rfl⟩ : syracuseStep 1811339 = 2717009) B2717009
theorem B1450891 : Blo 1206420 1450891 := bstep (se 1 (by rfl) ⟨1088168, by rfl⟩ : syracuseStep 1450891 = 2176337) B2176337
theorem B1811351 : Blo 1206420 1811351 := bstep (se 1 (by rfl) ⟨1358513, by rfl⟩ : syracuseStep 1811351 = 2717027) B2717027
theorem B4072409 : Blo 1206420 4072409 := bstep (se 2 (by rfl) ⟨1527153, by rfl⟩ : syracuseStep 4072409 = 3054307) B3054307
theorem B1811417 : Blo 1206420 1811417 := bstep (se 2 (by rfl) ⟨679281, by rfl⟩ : syracuseStep 1811417 = 1358563) B1358563
theorem B1811531 : Blo 1206420 1811531 := bstep (se 1 (by rfl) ⟨1358648, by rfl⟩ : syracuseStep 1811531 = 2717297) B2717297
theorem B1811543 : Blo 1206420 1811543 := bstep (se 1 (by rfl) ⟨1358657, by rfl⟩ : syracuseStep 1811543 = 2717315) B2717315
theorem B1811609 : Blo 1206420 1811609 := bstep (se 2 (by rfl) ⟨679353, by rfl⟩ : syracuseStep 1811609 = 1358707) B1358707
theorem B4408499 : Blo 1206420 4408499 := bstep (se 1 (by rfl) ⟨3306374, by rfl⟩ : syracuseStep 4408499 = 6612749) B6612749
theorem B1811723 : Blo 1206420 1811723 := bstep (se 1 (by rfl) ⟨1358792, by rfl⟩ : syracuseStep 1811723 = 2717585) B2717585
theorem B1811735 : Blo 1206420 1811735 := bstep (se 1 (by rfl) ⟨1358801, by rfl⟩ : syracuseStep 1811735 = 2717603) B2717603
theorem B1811801 : Blo 1206420 1811801 := bstep (se 2 (by rfl) ⟨679425, by rfl⟩ : syracuseStep 1811801 = 1358851) B1358851
theorem B9168389 : Blo 1206420 9168389 := bstep (se 4 (by rfl) ⟨859536, by rfl⟩ : syracuseStep 9168389 = 1719073) B1719073
theorem B39142925 : Blo 1206420 39142925 := bstep (se 3 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 39142925 = 14678597) B14678597
theorem B5801489 : Blo 1206420 5801489 := bstep (se 2 (by rfl) ⟨2175558, by rfl⟩ : syracuseStep 5801489 = 4351117) B4351117
theorem B4130327 : Blo 1206420 4130327 := bstep (se 1 (by rfl) ⟨3097745, by rfl⟩ : syracuseStep 4130327 = 6195491) B6195491
theorem B5154349 : Blo 1206420 5154349 := bstep (se 3 (by rfl) ⟨966440, by rfl⟩ : syracuseStep 5154349 = 1932881) B1932881
theorem B3868211 : Blo 1206420 3868211 := bstep (se 1 (by rfl) ⟨2901158, by rfl⟩ : syracuseStep 3868211 = 5802317) B5802317
theorem B3057203 : Blo 1206420 3057203 := bstep (se 1 (by rfl) ⟨2292902, by rfl⟩ : syracuseStep 3057203 = 4585805) B4585805
theorem B1631831 : Blo 1206420 1631831 := bstep (se 1 (by rfl) ⟨1223873, by rfl⟩ : syracuseStep 1631831 = 2447747) B2447747
theorem B3868249 : Blo 1206420 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B4073111 : Blo 1206420 4073111 := bstep (se 1 (by rfl) ⟨3054833, by rfl⟩ : syracuseStep 4073111 = 6109667) B6109667
theorem B17393393 : Blo 1206420 17393393 := bstep (se 2 (by rfl) ⟨6522522, by rfl⟩ : syracuseStep 17393393 = 13045045) B13045045
theorem B4581143 : Blo 1206420 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B6113069 : Blo 1206420 6113069 := bstep (se 3 (by rfl) ⟨1146200, by rfl⟩ : syracuseStep 6113069 = 2292401) B2292401
theorem B3057497 : Blo 1206420 3057497 := bstep (se 2 (by rfl) ⟨1146561, by rfl⟩ : syracuseStep 3057497 = 2293123) B2293123
theorem B3262301 : Blo 1206420 3262301 := bstep (se 3 (by rfl) ⟨611681, by rfl⟩ : syracuseStep 3262301 = 1223363) B1223363
theorem B5154691 : Blo 1206420 5154691 := bstep (se 1 (by rfl) ⟨3866018, by rfl⟩ : syracuseStep 5154691 = 7732037) B7732037
theorem B2754611 : Blo 1206420 2754611 := bstep (se 1 (by rfl) ⟨2065958, by rfl⟩ : syracuseStep 2754611 = 4131917) B4131917
theorem B2902081 : Blo 1206420 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B24774731 : Blo 1206420 24774731 := bstep (se 1 (by rfl) ⟨18581048, by rfl⟩ : syracuseStep 24774731 = 37162097) B37162097
theorem B1206423 : Blo 1206420 1206423 := bstep (se 1 (by rfl) ⟨904817, by rfl⟩ : syracuseStep 1206423 = 1809635) B1809635
theorem B1206443 : Blo 1206420 1206443 := bstep (se 1 (by rfl) ⟨904832, by rfl⟩ : syracuseStep 1206443 = 1809665) B1809665
theorem B4073651 : Blo 1206420 4073651 := bstep (se 1 (by rfl) ⟨3055238, by rfl⟩ : syracuseStep 4073651 = 6110477) B6110477
theorem B1206455 : Blo 1206420 1206455 := bstep (se 1 (by rfl) ⟨904841, by rfl⟩ : syracuseStep 1206455 = 1809683) B1809683
theorem B1206475 : Blo 1206420 1206475 := bstep (se 1 (by rfl) ⟨904856, by rfl⟩ : syracuseStep 1206475 = 1809713) B1809713
theorem B1206487 : Blo 1206420 1206487 := bstep (se 1 (by rfl) ⟨904865, by rfl⟩ : syracuseStep 1206487 = 1809731) B1809731
theorem B1206507 : Blo 1206420 1206507 := bstep (se 1 (by rfl) ⟨904880, by rfl⟩ : syracuseStep 1206507 = 1809761) B1809761
theorem B1206519 : Blo 1206420 1206519 := bstep (se 1 (by rfl) ⟨904889, by rfl⟩ : syracuseStep 1206519 = 1809779) B1809779
theorem B1206539 : Blo 1206420 1206539 := bstep (se 1 (by rfl) ⟨904904, by rfl⟩ : syracuseStep 1206539 = 1809809) B1809809
theorem B1206551 : Blo 1206420 1206551 := bstep (se 1 (by rfl) ⟨904913, by rfl⟩ : syracuseStep 1206551 = 1809827) B1809827
theorem B1206571 : Blo 1206420 1206571 := bstep (se 1 (by rfl) ⟨904928, by rfl⟩ : syracuseStep 1206571 = 1809857) B1809857
theorem B1206583 : Blo 1206420 1206583 := bstep (se 1 (by rfl) ⟨904937, by rfl⟩ : syracuseStep 1206583 = 1809875) B1809875
theorem B1206603 : Blo 1206420 1206603 := bstep (se 1 (by rfl) ⟨904952, by rfl⟩ : syracuseStep 1206603 = 1809905) B1809905
theorem B1206615 : Blo 1206420 1206615 := bstep (se 1 (by rfl) ⟨904961, by rfl⟩ : syracuseStep 1206615 = 1809923) B1809923
theorem B1206635 : Blo 1206420 1206635 := bstep (se 1 (by rfl) ⟨904976, by rfl⟩ : syracuseStep 1206635 = 1809953) B1809953
theorem B1206647 : Blo 1206420 1206647 := bstep (se 1 (by rfl) ⟨904985, by rfl⟩ : syracuseStep 1206647 = 1809971) B1809971
theorem B1206667 : Blo 1206420 1206667 := bstep (se 1 (by rfl) ⟨905000, by rfl⟩ : syracuseStep 1206667 = 1810001) B1810001
theorem B33499541 : Blo 1206420 33499541 := bstep (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) B1570291
theorem B1206679 : Blo 1206420 1206679 := bstep (se 1 (by rfl) ⟨905009, by rfl⟩ : syracuseStep 1206679 = 1810019) B1810019
theorem B1206699 : Blo 1206420 1206699 := bstep (se 1 (by rfl) ⟨905024, by rfl⟩ : syracuseStep 1206699 = 1810049) B1810049
theorem B1206711 : Blo 1206420 1206711 := bstep (se 1 (by rfl) ⟨905033, by rfl⟩ : syracuseStep 1206711 = 1810067) B1810067
theorem B4073921 : Blo 1206420 4073921 := bstep (se 2 (by rfl) ⟨1527720, by rfl⟩ : syracuseStep 4073921 = 3055441) B3055441
theorem B1206731 : Blo 1206420 1206731 := bstep (se 1 (by rfl) ⟨905048, by rfl⟩ : syracuseStep 1206731 = 1810097) B1810097
theorem B1206743 : Blo 1206420 1206743 := bstep (se 1 (by rfl) ⟨905057, by rfl⟩ : syracuseStep 1206743 = 1810115) B1810115
theorem B1206763 : Blo 1206420 1206763 := bstep (se 1 (by rfl) ⟨905072, by rfl⟩ : syracuseStep 1206763 = 1810145) B1810145
theorem B1206775 : Blo 1206420 1206775 := bstep (se 1 (by rfl) ⟨905081, by rfl⟩ : syracuseStep 1206775 = 1810163) B1810163
theorem B1206795 : Blo 1206420 1206795 := bstep (se 1 (by rfl) ⟨905096, by rfl⟩ : syracuseStep 1206795 = 1810193) B1810193
theorem B1206807 : Blo 1206420 1206807 := bstep (se 1 (by rfl) ⟨905105, by rfl⟩ : syracuseStep 1206807 = 1810211) B1810211
theorem B1206827 : Blo 1206420 1206827 := bstep (se 1 (by rfl) ⟨905120, by rfl⟩ : syracuseStep 1206827 = 1810241) B1810241
theorem B1206839 : Blo 1206420 1206839 := bstep (se 1 (by rfl) ⟨905129, by rfl⟩ : syracuseStep 1206839 = 1810259) B1810259
theorem B1206859 : Blo 1206420 1206859 := bstep (se 1 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 1206859 = 1810289) B1810289
theorem B1206871 : Blo 1206420 1206871 := bstep (se 1 (by rfl) ⟨905153, by rfl⟩ : syracuseStep 1206871 = 1810307) B1810307
theorem B49572445 : Blo 1206420 49572445 := bstep (se 3 (by rfl) ⟨9294833, by rfl⟩ : syracuseStep 49572445 = 18589667) B18589667
theorem B1206891 : Blo 1206420 1206891 := bstep (se 1 (by rfl) ⟨905168, by rfl⟩ : syracuseStep 1206891 = 1810337) B1810337
theorem B1206903 : Blo 1206420 1206903 := bstep (se 1 (by rfl) ⟨905177, by rfl⟩ : syracuseStep 1206903 = 1810355) B1810355
theorem B1206923 : Blo 1206420 1206923 := bstep (se 1 (by rfl) ⟨905192, by rfl⟩ : syracuseStep 1206923 = 1810385) B1810385
theorem B1206935 : Blo 1206420 1206935 := bstep (se 1 (by rfl) ⟨905201, by rfl⟩ : syracuseStep 1206935 = 1810403) B1810403
theorem B1206955 : Blo 1206420 1206955 := bstep (se 1 (by rfl) ⟨905216, by rfl⟩ : syracuseStep 1206955 = 1810433) B1810433
theorem B1206967 : Blo 1206420 1206967 := bstep (se 1 (by rfl) ⟨905225, by rfl⟩ : syracuseStep 1206967 = 1810451) B1810451
theorem B1206987 : Blo 1206420 1206987 := bstep (se 1 (by rfl) ⟨905240, by rfl⟩ : syracuseStep 1206987 = 1810481) B1810481
theorem B1206999 : Blo 1206420 1206999 := bstep (se 1 (by rfl) ⟨905249, by rfl⟩ : syracuseStep 1206999 = 1810499) B1810499
theorem B1207019 : Blo 1206420 1207019 := bstep (se 1 (by rfl) ⟨905264, by rfl⟩ : syracuseStep 1207019 = 1810529) B1810529
theorem B1207031 : Blo 1206420 1207031 := bstep (se 1 (by rfl) ⟨905273, by rfl⟩ : syracuseStep 1207031 = 1810547) B1810547
theorem B1207051 : Blo 1206420 1207051 := bstep (se 1 (by rfl) ⟨905288, by rfl⟩ : syracuseStep 1207051 = 1810577) B1810577
theorem B1207063 : Blo 1206420 1207063 := bstep (se 1 (by rfl) ⟨905297, by rfl⟩ : syracuseStep 1207063 = 1810595) B1810595
theorem B1207083 : Blo 1206420 1207083 := bstep (se 1 (by rfl) ⟨905312, by rfl⟩ : syracuseStep 1207083 = 1810625) B1810625
theorem B1207095 : Blo 1206420 1207095 := bstep (se 1 (by rfl) ⟨905321, by rfl⟩ : syracuseStep 1207095 = 1810643) B1810643
theorem B57256769 : Blo 1206420 57256769 := bstep (se 2 (by rfl) ⟨21471288, by rfl⟩ : syracuseStep 57256769 = 42942577) B42942577
theorem B5155649 : Blo 1206420 5155649 := bstep (se 2 (by rfl) ⟨1933368, by rfl⟩ : syracuseStep 5155649 = 3866737) B3866737
theorem B1207115 : Blo 1206420 1207115 := bstep (se 1 (by rfl) ⟨905336, by rfl⟩ : syracuseStep 1207115 = 1810673) B1810673
theorem B1207127 : Blo 1206420 1207127 := bstep (se 1 (by rfl) ⟨905345, by rfl⟩ : syracuseStep 1207127 = 1810691) B1810691
theorem B45255523 : Blo 1206420 45255523 := bstep (se 1 (by rfl) ⟨33941642, by rfl⟩ : syracuseStep 45255523 = 67883285) B67883285
theorem B1207147 : Blo 1206420 1207147 := bstep (se 1 (by rfl) ⟨905360, by rfl⟩ : syracuseStep 1207147 = 1810721) B1810721
theorem B1207159 : Blo 1206420 1207159 := bstep (se 1 (by rfl) ⟨905369, by rfl⟩ : syracuseStep 1207159 = 1810739) B1810739
theorem B2714507 : Blo 1206420 2714507 := bstep (se 1 (by rfl) ⟨2035880, by rfl⟩ : syracuseStep 2714507 = 4071761) B4071761
theorem B1207179 : Blo 1206420 1207179 := bstep (se 1 (by rfl) ⟨905384, by rfl⟩ : syracuseStep 1207179 = 1810769) B1810769
theorem B1207191 : Blo 1206420 1207191 := bstep (se 1 (by rfl) ⟨905393, by rfl⟩ : syracuseStep 1207191 = 1810787) B1810787
theorem B1207211 : Blo 1206420 1207211 := bstep (se 1 (by rfl) ⟨905408, by rfl⟩ : syracuseStep 1207211 = 1810817) B1810817
theorem B5802931 : Blo 1206420 5802931 := bstep (se 1 (by rfl) ⟨4352198, by rfl⟩ : syracuseStep 5802931 = 8704397) B8704397
theorem B1289143 : Blo 1206420 1289143 := bstep (se 1 (by rfl) ⟨966857, by rfl⟩ : syracuseStep 1289143 = 1933715) B1933715
theorem B1207223 : Blo 1206420 1207223 := bstep (se 1 (by rfl) ⟨905417, by rfl⟩ : syracuseStep 1207223 = 1810835) B1810835
theorem B2714561 : Blo 1206420 2714561 := bstep (se 2 (by rfl) ⟨1017960, by rfl⟩ : syracuseStep 2714561 = 2035921) B2035921
theorem B1207243 : Blo 1206420 1207243 := bstep (se 1 (by rfl) ⟨905432, by rfl⟩ : syracuseStep 1207243 = 1810865) B1810865
theorem B1207255 : Blo 1206420 1207255 := bstep (se 1 (by rfl) ⟨905441, by rfl⟩ : syracuseStep 1207255 = 1810883) B1810883
theorem B4074461 : Blo 1206420 4074461 := bstep (se 3 (by rfl) ⟨763961, by rfl⟩ : syracuseStep 4074461 = 1527923) B1527923
theorem B1207275 : Blo 1206420 1207275 := bstep (se 1 (by rfl) ⟨905456, by rfl⟩ : syracuseStep 1207275 = 1810913) B1810913
theorem B1207287 : Blo 1206420 1207287 := bstep (se 1 (by rfl) ⟨905465, by rfl⟩ : syracuseStep 1207287 = 1810931) B1810931
theorem B4582403 : Blo 1206420 4582403 := bstep (se 1 (by rfl) ⟨3436802, by rfl⟩ : syracuseStep 4582403 = 6873605) B6873605
theorem B1207307 : Blo 1206420 1207307 := bstep (se 1 (by rfl) ⟨905480, by rfl⟩ : syracuseStep 1207307 = 1810961) B1810961
theorem B1207319 : Blo 1206420 1207319 := bstep (se 1 (by rfl) ⟨905489, by rfl⟩ : syracuseStep 1207319 = 1810979) B1810979
theorem B1207339 : Blo 1206420 1207339 := bstep (se 1 (by rfl) ⟨905504, by rfl⟩ : syracuseStep 1207339 = 1811009) B1811009
theorem B1207351 : Blo 1206420 1207351 := bstep (se 1 (by rfl) ⟨905513, by rfl⟩ : syracuseStep 1207351 = 1811027) B1811027
theorem B1207371 : Blo 1206420 1207371 := bstep (se 1 (by rfl) ⟨905528, by rfl⟩ : syracuseStep 1207371 = 1811057) B1811057
theorem B1207383 : Blo 1206420 1207383 := bstep (se 1 (by rfl) ⟨905537, by rfl⟩ : syracuseStep 1207383 = 1811075) B1811075
theorem B1207403 : Blo 1206420 1207403 := bstep (se 1 (by rfl) ⟨905552, by rfl⟩ : syracuseStep 1207403 = 1811105) B1811105
theorem B1207415 : Blo 1206420 1207415 := bstep (se 1 (by rfl) ⟨905561, by rfl⟩ : syracuseStep 1207415 = 1811123) B1811123
theorem B1207435 : Blo 1206420 1207435 := bstep (se 1 (by rfl) ⟨905576, by rfl⟩ : syracuseStep 1207435 = 1811153) B1811153
theorem B1207447 : Blo 1206420 1207447 := bstep (se 1 (by rfl) ⟨905585, by rfl⟩ : syracuseStep 1207447 = 1811171) B1811171
theorem B2714777 : Blo 1206420 2714777 := bstep (se 2 (by rfl) ⟨1018041, by rfl⟩ : syracuseStep 2714777 = 2036083) B2036083
theorem B1207467 : Blo 1206420 1207467 := bstep (se 1 (by rfl) ⟨905600, by rfl⟩ : syracuseStep 1207467 = 1811201) B1811201
theorem B1207479 : Blo 1206420 1207479 := bstep (se 1 (by rfl) ⟨905609, by rfl⟩ : syracuseStep 1207479 = 1811219) B1811219
theorem B1207499 : Blo 1206420 1207499 := bstep (se 1 (by rfl) ⟨905624, by rfl⟩ : syracuseStep 1207499 = 1811249) B1811249
theorem B1207511 : Blo 1206420 1207511 := bstep (se 1 (by rfl) ⟨905633, by rfl⟩ : syracuseStep 1207511 = 1811267) B1811267
theorem B1207531 : Blo 1206420 1207531 := bstep (se 1 (by rfl) ⟨905648, by rfl⟩ : syracuseStep 1207531 = 1811297) B1811297
theorem B2714867 : Blo 1206420 2714867 := bstep (se 1 (by rfl) ⟨2036150, by rfl⟩ : syracuseStep 2714867 = 4072301) B4072301
theorem B1207543 : Blo 1206420 1207543 := bstep (se 1 (by rfl) ⟨905657, by rfl⟩ : syracuseStep 1207543 = 1811315) B1811315
theorem B1207563 : Blo 1206420 1207563 := bstep (se 1 (by rfl) ⟨905672, by rfl⟩ : syracuseStep 1207563 = 1811345) B1811345
theorem B2714903 : Blo 1206420 2714903 := bstep (se 1 (by rfl) ⟨2036177, by rfl⟩ : syracuseStep 2714903 = 4072355) B4072355
theorem B1207575 : Blo 1206420 1207575 := bstep (se 1 (by rfl) ⟨905681, by rfl⟩ : syracuseStep 1207575 = 1811363) B1811363
theorem B1207595 : Blo 1206420 1207595 := bstep (se 1 (by rfl) ⟨905696, by rfl⟩ : syracuseStep 1207595 = 1811393) B1811393
theorem B1207607 : Blo 1206420 1207607 := bstep (se 1 (by rfl) ⟨905705, by rfl⟩ : syracuseStep 1207607 = 1811411) B1811411
theorem B1207627 : Blo 1206420 1207627 := bstep (se 1 (by rfl) ⟨905720, by rfl⟩ : syracuseStep 1207627 = 1811441) B1811441
theorem B1207639 : Blo 1206420 1207639 := bstep (se 1 (by rfl) ⟨905729, by rfl⟩ : syracuseStep 1207639 = 1811459) B1811459
theorem B1207659 : Blo 1206420 1207659 := bstep (se 1 (by rfl) ⟨905744, by rfl⟩ : syracuseStep 1207659 = 1811489) B1811489
theorem B1207671 : Blo 1206420 1207671 := bstep (se 1 (by rfl) ⟨905753, by rfl⟩ : syracuseStep 1207671 = 1811507) B1811507
theorem B1207691 : Blo 1206420 1207691 := bstep (se 1 (by rfl) ⟨905768, by rfl⟩ : syracuseStep 1207691 = 1811537) B1811537
theorem B4353425 : Blo 1206420 4353425 := bstep (se 2 (by rfl) ⟨1632534, by rfl⟩ : syracuseStep 4353425 = 3265069) B3265069
theorem B1207703 : Blo 1206420 1207703 := bstep (se 1 (by rfl) ⟨905777, by rfl⟩ : syracuseStep 1207703 = 1811555) B1811555
theorem B1207723 : Blo 1206420 1207723 := bstep (se 1 (by rfl) ⟨905792, by rfl⟩ : syracuseStep 1207723 = 1811585) B1811585
theorem B1207735 : Blo 1206420 1207735 := bstep (se 1 (by rfl) ⟨905801, by rfl⟩ : syracuseStep 1207735 = 1811603) B1811603
theorem B2715083 : Blo 1206420 2715083 := bstep (se 1 (by rfl) ⟨2036312, by rfl⟩ : syracuseStep 2715083 = 4072625) B4072625
theorem B1207755 : Blo 1206420 1207755 := bstep (se 1 (by rfl) ⟨905816, by rfl⟩ : syracuseStep 1207755 = 1811633) B1811633
theorem B1207767 : Blo 1206420 1207767 := bstep (se 1 (by rfl) ⟨905825, by rfl⟩ : syracuseStep 1207767 = 1811651) B1811651
theorem B1207787 : Blo 1206420 1207787 := bstep (se 1 (by rfl) ⟨905840, by rfl⟩ : syracuseStep 1207787 = 1811681) B1811681
theorem B1207799 : Blo 1206420 1207799 := bstep (se 1 (by rfl) ⟨905849, by rfl⟩ : syracuseStep 1207799 = 1811699) B1811699
theorem B2715137 : Blo 1206420 2715137 := bstep (se 2 (by rfl) ⟨1018176, by rfl⟩ : syracuseStep 2715137 = 2036353) B2036353
theorem B1207819 : Blo 1206420 1207819 := bstep (se 1 (by rfl) ⟨905864, by rfl⟩ : syracuseStep 1207819 = 1811729) B1811729
theorem B1207831 : Blo 1206420 1207831 := bstep (se 1 (by rfl) ⟨905873, by rfl⟩ : syracuseStep 1207831 = 1811747) B1811747
theorem B1207851 : Blo 1206420 1207851 := bstep (se 1 (by rfl) ⟨905888, by rfl⟩ : syracuseStep 1207851 = 1811777) B1811777
theorem B1207863 : Blo 1206420 1207863 := bstep (se 1 (by rfl) ⟨905897, by rfl⟩ : syracuseStep 1207863 = 1811795) B1811795
theorem B1207883 : Blo 1206420 1207883 := bstep (se 1 (by rfl) ⟨905912, by rfl⟩ : syracuseStep 1207883 = 1811825) B1811825
theorem B1207895 : Blo 1206420 1207895 := bstep (se 1 (by rfl) ⟨905921, by rfl⟩ : syracuseStep 1207895 = 1811843) B1811843
theorem B1207915 : Blo 1206420 1207915 := bstep (se 1 (by rfl) ⟨905936, by rfl⟩ : syracuseStep 1207915 = 1811873) B1811873
theorem B2715353 : Blo 1206420 2715353 := bstep (se 2 (by rfl) ⟨1018257, by rfl⟩ : syracuseStep 2715353 = 2036515) B2036515
theorem B2715443 : Blo 1206420 2715443 := bstep (se 1 (by rfl) ⟨2036582, by rfl⟩ : syracuseStep 2715443 = 4073165) B4073165
theorem B2715479 : Blo 1206420 2715479 := bstep (se 1 (by rfl) ⟨2036609, by rfl⟩ : syracuseStep 2715479 = 4073219) B4073219
theorem B6877021 : Blo 1206420 6877021 := bstep (se 3 (by rfl) ⟨1289441, by rfl⟩ : syracuseStep 6877021 = 2578883) B2578883
theorem B9170819 : Blo 1206420 9170819 := bstep (se 1 (by rfl) ⟨6878114, by rfl⟩ : syracuseStep 9170819 = 13756229) B13756229
theorem B8261527 : Blo 1206420 8261527 := bstep (se 1 (by rfl) ⟨6196145, by rfl⟩ : syracuseStep 8261527 = 12392291) B12392291
theorem B10317719 : Blo 1206420 10317719 := bstep (se 1 (by rfl) ⟨7738289, by rfl⟩ : syracuseStep 10317719 = 15476579) B15476579
theorem B2715659 : Blo 1206420 2715659 := bstep (se 1 (by rfl) ⟨2036744, by rfl⟩ : syracuseStep 2715659 = 4073489) B4073489
theorem B6279185 : Blo 1206420 6279185 := bstep (se 2 (by rfl) ⟨2354694, by rfl⟩ : syracuseStep 6279185 = 4709389) B4709389
theorem B2715713 : Blo 1206420 2715713 := bstep (se 2 (by rfl) ⟨1018392, by rfl⟩ : syracuseStep 2715713 = 2036785) B2036785
theorem B11006027 : Blo 1206420 11006027 := bstep (se 1 (by rfl) ⟨8254520, by rfl⟩ : syracuseStep 11006027 = 16509041) B16509041
theorem B4075595 : Blo 1206420 4075595 := bstep (se 1 (by rfl) ⟨3056696, by rfl⟩ : syracuseStep 4075595 = 6113393) B6113393
theorem B1814731 : Blo 1206420 1814731 := bstep (se 1 (by rfl) ⟨1361048, by rfl⟩ : syracuseStep 1814731 = 2722097) B2722097
theorem B5157067 : Blo 1206420 5157067 := bstep (se 1 (by rfl) ⟨3867800, by rfl⟩ : syracuseStep 5157067 = 7735601) B7735601
theorem B1528075 : Blo 1206420 1528075 := bstep (se 1 (by rfl) ⟨1146056, by rfl⟩ : syracuseStep 1528075 = 2292113) B2292113
theorem B2715929 : Blo 1206420 2715929 := bstep (se 2 (by rfl) ⟨1018473, by rfl⟩ : syracuseStep 2715929 = 2036947) B2036947
theorem B2175257 : Blo 1206420 2175257 := bstep (se 2 (by rfl) ⟨815721, by rfl⟩ : syracuseStep 2175257 = 1631443) B1631443
theorem B9163043 : Blo 1206420 9163043 := bstep (se 1 (by rfl) ⟨6872282, by rfl⟩ : syracuseStep 9163043 = 13744565) B13744565
theorem B4075865 : Blo 1206420 4075865 := bstep (se 2 (by rfl) ⟨1528449, by rfl⟩ : syracuseStep 4075865 = 3056899) B3056899
theorem B2716019 : Blo 1206420 2716019 := bstep (se 1 (by rfl) ⟨2037014, by rfl⟩ : syracuseStep 2716019 = 4074029) B4074029
theorem B3436951 : Blo 1206420 3436951 := bstep (se 1 (by rfl) ⟨2577713, by rfl⟩ : syracuseStep 3436951 = 5155427) B5155427
theorem B2716055 : Blo 1206420 2716055 := bstep (se 1 (by rfl) ⟨2037041, by rfl⟩ : syracuseStep 2716055 = 4074083) B4074083
theorem B2036171 : Blo 1206420 2036171 := bstep (se 1 (by rfl) ⟨1527128, by rfl⟩ : syracuseStep 2036171 = 3054257) B3054257
theorem B5157341 : Blo 1206420 5157341 := bstep (se 3 (by rfl) ⟨967001, by rfl⟩ : syracuseStep 5157341 = 1934003) B1934003
theorem B6107723 : Blo 1206420 6107723 := bstep (se 1 (by rfl) ⟨4580792, by rfl⟩ : syracuseStep 6107723 = 9161585) B9161585
theorem B2036299 : Blo 1206420 2036299 := bstep (se 1 (by rfl) ⟨1527224, by rfl⟩ : syracuseStep 2036299 = 3054449) B3054449
theorem B2716235 : Blo 1206420 2716235 := bstep (se 1 (by rfl) ⟨2037176, by rfl⟩ : syracuseStep 2716235 = 4074353) B4074353
theorem B20632157 : Blo 1206420 20632157 := bstep (se 3 (by rfl) ⟨3868529, by rfl⟩ : syracuseStep 20632157 = 7737059) B7737059
theorem B2716289 : Blo 1206420 2716289 := bstep (se 2 (by rfl) ⟨1018608, by rfl⟩ : syracuseStep 2716289 = 2037217) B2037217
theorem B2036441 : Blo 1206420 2036441 := bstep (se 2 (by rfl) ⟨763665, by rfl⟩ : syracuseStep 2036441 = 1527331) B1527331
theorem B7729937 : Blo 1206420 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B2290457 : Blo 1206420 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B2036569 : Blo 1206420 2036569 := bstep (se 2 (by rfl) ⟨763713, by rfl⟩ : syracuseStep 2036569 = 1527427) B1527427
theorem B2716505 : Blo 1206420 2716505 := bstep (se 2 (by rfl) ⟨1018689, by rfl⟩ : syracuseStep 2716505 = 2037379) B2037379
theorem B2716595 : Blo 1206420 2716595 := bstep (se 1 (by rfl) ⟨2037446, by rfl⟩ : syracuseStep 2716595 = 4074893) B4074893
theorem B2716631 : Blo 1206420 2716631 := bstep (se 1 (by rfl) ⟨2037473, by rfl⟩ : syracuseStep 2716631 = 4074947) B4074947
theorem B4076567 : Blo 1206420 4076567 := bstep (se 1 (by rfl) ⟨3057425, by rfl⟩ : syracuseStep 4076567 = 6114851) B6114851
theorem B2716811 : Blo 1206420 2716811 := bstep (se 1 (by rfl) ⟨2037608, by rfl⟩ : syracuseStep 2716811 = 4075217) B4075217
theorem B16528535 : Blo 1206420 16528535 := bstep (se 1 (by rfl) ⟨12396401, by rfl⟩ : syracuseStep 16528535 = 24792803) B24792803
theorem B2716865 : Blo 1206420 2716865 := bstep (se 2 (by rfl) ⟨1018824, by rfl⟩ : syracuseStep 2716865 = 2037649) B2037649
theorem B7730477 : Blo 1206420 7730477 := bstep (se 3 (by rfl) ⟨1449464, by rfl⟩ : syracuseStep 7730477 = 2898929) B2898929
theorem B30954797 : Blo 1206420 30954797 := bstep (se 3 (by rfl) ⟨5804024, by rfl⟩ : syracuseStep 30954797 = 11608049) B11608049
theorem B2577739 : Blo 1206420 2577739 := bstep (se 1 (by rfl) ⟨1933304, by rfl⟩ : syracuseStep 2577739 = 3866609) B3866609
theorem B2291095 : Blo 1206420 2291095 := bstep (se 1 (by rfl) ⟨1718321, by rfl⟩ : syracuseStep 2291095 = 3436643) B3436643
theorem B2037143 : Blo 1206420 2037143 := bstep (se 1 (by rfl) ⟨1527857, by rfl⟩ : syracuseStep 2037143 = 3055715) B3055715
theorem B2717081 : Blo 1206420 2717081 := bstep (se 2 (by rfl) ⟨1018905, by rfl⟩ : syracuseStep 2717081 = 2037811) B2037811
theorem B2717171 : Blo 1206420 2717171 := bstep (se 1 (by rfl) ⟨2037878, by rfl⟩ : syracuseStep 2717171 = 4075757) B4075757
theorem B1357303 : Blo 1206420 1357303 := bstep (se 1 (by rfl) ⟨1017977, by rfl⟩ : syracuseStep 1357303 = 2035955) B2035955
theorem B2037271 : Blo 1206420 2037271 := bstep (se 1 (by rfl) ⟨1527953, by rfl⟩ : syracuseStep 2037271 = 3055907) B3055907
theorem B2717207 : Blo 1206420 2717207 := bstep (se 1 (by rfl) ⟨2037905, by rfl⟩ : syracuseStep 2717207 = 4075811) B4075811
theorem B2577995 : Blo 1206420 2577995 := bstep (se 1 (by rfl) ⟨1933496, by rfl⟩ : syracuseStep 2577995 = 3866993) B3866993
theorem B1570379 : Blo 1206420 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B12383837 : Blo 1206420 12383837 := bstep (se 3 (by rfl) ⟨2321969, by rfl⟩ : syracuseStep 12383837 = 4643939) B4643939
theorem B2479745 : Blo 1206420 2479745 := bstep (se 2 (by rfl) ⟨929904, by rfl⟩ : syracuseStep 2479745 = 1859809) B1859809
theorem B1357483 : Blo 1206420 1357483 := bstep (se 1 (by rfl) ⟨1018112, by rfl⟩ : syracuseStep 1357483 = 2036225) B2036225
theorem B3438283 : Blo 1206420 3438283 := bstep (se 1 (by rfl) ⟨2578712, by rfl⟩ : syracuseStep 3438283 = 5157425) B5157425
theorem B2717387 : Blo 1206420 2717387 := bstep (se 1 (by rfl) ⟨2038040, by rfl⟩ : syracuseStep 2717387 = 4076081) B4076081
theorem B2717441 : Blo 1206420 2717441 := bstep (se 2 (by rfl) ⟨1019040, by rfl⟩ : syracuseStep 2717441 = 2038081) B2038081
theorem B1357591 : Blo 1206420 1357591 := bstep (se 1 (by rfl) ⟨1018193, by rfl⟩ : syracuseStep 1357591 = 2036387) B2036387
theorem B44046179 : Blo 1206420 44046179 := bstep (se 1 (by rfl) ⟨33034634, by rfl⟩ : syracuseStep 44046179 = 66069269) B66069269
theorem B1718219 : Blo 1206420 1718219 := bstep (se 1 (by rfl) ⟨1288664, by rfl⟩ : syracuseStep 1718219 = 2577329) B2577329
theorem B1357771 : Blo 1206420 1357771 := bstep (se 1 (by rfl) ⟨1018328, by rfl⟩ : syracuseStep 1357771 = 2036657) B2036657
theorem B2717657 : Blo 1206420 2717657 := bstep (se 2 (by rfl) ⟨1019121, by rfl⟩ : syracuseStep 2717657 = 2038243) B2038243
theorem B3438557 : Blo 1206420 3438557 := bstep (se 3 (by rfl) ⟨644729, by rfl⟩ : syracuseStep 3438557 = 1289459) B1289459
theorem B4585517 : Blo 1206420 4585517 := bstep (se 3 (by rfl) ⟨859784, by rfl⟩ : syracuseStep 4585517 = 1719569) B1719569
theorem B2717747 : Blo 1206420 2717747 := bstep (se 1 (by rfl) ⟨2038310, by rfl⟩ : syracuseStep 2717747 = 4076621) B4076621
theorem B1357879 : Blo 1206420 1357879 := bstep (se 1 (by rfl) ⟨1018409, by rfl⟩ : syracuseStep 1357879 = 2036819) B2036819
theorem B2717783 : Blo 1206420 2717783 := bstep (se 1 (by rfl) ⟨2038337, by rfl⟩ : syracuseStep 2717783 = 4076675) B4076675
theorem B2037899 : Blo 1206420 2037899 := bstep (se 1 (by rfl) ⟨1528424, by rfl⟩ : syracuseStep 2037899 = 3056849) B3056849
theorem B39172247 : Blo 1206420 39172247 := bstep (se 1 (by rfl) ⟨29379185, by rfl⟩ : syracuseStep 39172247 = 58758371) B58758371
theorem B3053771 : Blo 1206420 3053771 := bstep (se 1 (by rfl) ⟨2290328, by rfl⟩ : syracuseStep 3053771 = 4580657) B4580657
theorem B2291915 : Blo 1206420 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B1358059 : Blo 1206420 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B2291969 : Blo 1206420 2291969 := bstep (se 2 (by rfl) ⟨859488, by rfl⟩ : syracuseStep 2291969 = 1718977) B1718977
theorem B2038027 : Blo 1206420 2038027 := bstep (se 1 (by rfl) ⟨1528520, by rfl⟩ : syracuseStep 2038027 = 3057041) B3057041
theorem B3438899 : Blo 1206420 3438899 := bstep (se 1 (by rfl) ⟨2579174, by rfl⟩ : syracuseStep 3438899 = 5158349) B5158349
theorem B6109505 : Blo 1206420 6109505 := bstep (se 2 (by rfl) ⟨2291064, by rfl⟩ : syracuseStep 6109505 = 4582129) B4582129
theorem B4348235 : Blo 1206420 4348235 := bstep (se 1 (by rfl) ⟨3261176, by rfl⟩ : syracuseStep 4348235 = 6522353) B6522353
theorem B1358167 : Blo 1206420 1358167 := bstep (se 1 (by rfl) ⟨1018625, by rfl⟩ : syracuseStep 1358167 = 2037251) B2037251
theorem B1489291 : Blo 1206420 1489291 := bstep (se 1 (by rfl) ⟨1116968, by rfl⟩ : syracuseStep 1489291 = 2233937) B2233937
theorem B2038169 : Blo 1206420 2038169 := bstep (se 2 (by rfl) ⟨764313, by rfl⟩ : syracuseStep 2038169 = 1528627) B1528627
theorem B1358347 : Blo 1206420 1358347 := bstep (se 1 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 1358347 = 2037521) B2037521
theorem B2578969 : Blo 1206420 2578969 := bstep (se 2 (by rfl) ⟨967113, by rfl⟩ : syracuseStep 2578969 = 1934227) B1934227
theorem B2038297 : Blo 1206420 2038297 := bstep (se 2 (by rfl) ⟨764361, by rfl⟩ : syracuseStep 2038297 = 1528723) B1528723
theorem B3054145 : Blo 1206420 3054145 := bstep (se 2 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 3054145 = 2290609) B2290609
theorem B17406539 : Blo 1206420 17406539 := bstep (se 1 (by rfl) ⟨13054904, by rfl⟩ : syracuseStep 17406539 = 26109809) B26109809
theorem B1358455 : Blo 1206420 1358455 := bstep (se 1 (by rfl) ⟨1018841, by rfl⟩ : syracuseStep 1358455 = 2037683) B2037683
theorem B2579123 : Blo 1206420 2579123 := bstep (se 1 (by rfl) ⟨1934342, by rfl⟩ : syracuseStep 2579123 = 3868685) B3868685
theorem B4348637 : Blo 1206420 4348637 := bstep (se 3 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 4348637 = 1630739) B1630739
theorem B1358635 : Blo 1206420 1358635 := bstep (se 1 (by rfl) ⟨1018976, by rfl⟩ : syracuseStep 1358635 = 2037953) B2037953
theorem B4586291 : Blo 1206420 4586291 := bstep (se 1 (by rfl) ⟨3439718, by rfl⟩ : syracuseStep 4586291 = 6879437) B6879437
theorem B1358743 : Blo 1206420 1358743 := bstep (se 1 (by rfl) ⟨1019057, by rfl⟩ : syracuseStep 1358743 = 2038115) B2038115
theorem B2898881 : Blo 1206420 2898881 := bstep (se 2 (by rfl) ⟨1087080, by rfl⟩ : syracuseStep 2898881 = 2174161) B2174161
theorem B3865751 : Blo 1206420 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B3054743 : Blo 1206420 3054743 := bstep (se 1 (by rfl) ⟨2291057, by rfl⟩ : syracuseStep 3054743 = 4582115) B4582115
theorem B2292887 : Blo 1206420 2292887 := bstep (se 1 (by rfl) ⟨1719665, by rfl⟩ : syracuseStep 2292887 = 3439331) B3439331
theorem B2579635 : Blo 1206420 2579635 := bstep (se 1 (by rfl) ⟨1934726, by rfl⟩ : syracuseStep 2579635 = 3869453) B3869453
theorem B1809689 : Blo 1206420 1809689 := bstep (se 2 (by rfl) ⟨678633, by rfl⟩ : syracuseStep 1809689 = 1357267) B1357267
theorem B1809803 : Blo 1206420 1809803 := bstep (se 1 (by rfl) ⟨1357352, by rfl⟩ : syracuseStep 1809803 = 2714705) B2714705
theorem B338967949 : Blo 1206420 338967949 := bstep (se 3 (by rfl) ⟨63556490, by rfl⟩ : syracuseStep 338967949 = 127112981) B127112981
theorem B1809815 : Blo 1206420 1809815 := bstep (se 1 (by rfl) ⟨1357361, by rfl⟩ : syracuseStep 1809815 = 2714723) B2714723
theorem B10452401 : Blo 1206420 10452401 := bstep (se 2 (by rfl) ⟨3919650, by rfl⟩ : syracuseStep 10452401 = 7839301) B7839301
theorem B1809881 : Blo 1206420 1809881 := bstep (se 2 (by rfl) ⟨678705, by rfl⟩ : syracuseStep 1809881 = 1357411) B1357411
theorem B1809995 : Blo 1206420 1809995 := bstep (se 1 (by rfl) ⟨1357496, by rfl⟩ : syracuseStep 1809995 = 2714993) B2714993
theorem B1810007 : Blo 1206420 1810007 := bstep (se 1 (by rfl) ⟨1357505, by rfl⟩ : syracuseStep 1810007 = 2715011) B2715011
theorem B1810073 : Blo 1206420 1810073 := bstep (se 2 (by rfl) ⟨678777, by rfl⟩ : syracuseStep 1810073 = 1357555) B1357555
theorem B1810187 : Blo 1206420 1810187 := bstep (se 1 (by rfl) ⟨1357640, by rfl⟩ : syracuseStep 1810187 = 2715281) B2715281
theorem B1810199 : Blo 1206420 1810199 := bstep (se 1 (by rfl) ⟨1357649, by rfl⟩ : syracuseStep 1810199 = 2715299) B2715299
theorem B1810265 : Blo 1206420 1810265 := bstep (se 2 (by rfl) ⟨678849, by rfl⟩ : syracuseStep 1810265 = 1357699) B1357699
theorem B3055553 : Blo 1206420 3055553 := bstep (se 2 (by rfl) ⟨1145832, by rfl⟩ : syracuseStep 3055553 = 2291665) B2291665
theorem B1810379 : Blo 1206420 1810379 := bstep (se 1 (by rfl) ⟨1357784, by rfl⟩ : syracuseStep 1810379 = 2715569) B2715569
theorem B1810391 : Blo 1206420 1810391 := bstep (se 1 (by rfl) ⟨1357793, by rfl⟩ : syracuseStep 1810391 = 2715587) B2715587
theorem B1810439 : Blo 1206420 1810439 := bstep (se 1 (by rfl) ⟨1357829, by rfl⟩ : syracuseStep 1810439 = 2715659) B2715659
theorem B3096587 : Blo 1206420 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B4186123 : Blo 1206420 4186123 := bstep (se 1 (by rfl) ⟨3139592, by rfl⟩ : syracuseStep 4186123 = 6279185) B6279185
theorem B12730391 : Blo 1206420 12730391 := bstep (se 1 (by rfl) ⟨9547793, by rfl⟩ : syracuseStep 12730391 = 19095587) B19095587
theorem B1810475 : Blo 1206420 1810475 := bstep (se 1 (by rfl) ⟨1357856, by rfl⟩ : syracuseStep 1810475 = 2715713) B2715713
theorem B1810505 : Blo 1206420 1810505 := bstep (se 2 (by rfl) ⟨678939, by rfl⟩ : syracuseStep 1810505 = 1357879) B1357879
theorem B1810619 : Blo 1206420 1810619 := bstep (se 1 (by rfl) ⟨1357964, by rfl⟩ : syracuseStep 1810619 = 2715929) B2715929
theorem B1450171 : Blo 1206420 1450171 := bstep (se 1 (by rfl) ⟨1087628, by rfl⟩ : syracuseStep 1450171 = 2175257) B2175257
theorem B1810679 : Blo 1206420 1810679 := bstep (se 1 (by rfl) ⟨1358009, by rfl⟩ : syracuseStep 1810679 = 2716019) B2716019
theorem B1810703 : Blo 1206420 1810703 := bstep (se 1 (by rfl) ⟨1358027, by rfl⟩ : syracuseStep 1810703 = 2716055) B2716055
theorem B1810745 : Blo 1206420 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B6193523 : Blo 1206420 6193523 := bstep (se 1 (by rfl) ⟨4645142, by rfl⟩ : syracuseStep 6193523 = 9290285) B9290285
theorem B4071815 : Blo 1206420 4071815 := bstep (se 1 (by rfl) ⟨3053861, by rfl⟩ : syracuseStep 4071815 = 6107723) B6107723
theorem B3096967 : Blo 1206420 3096967 := bstep (se 1 (by rfl) ⟨2322725, by rfl⟩ : syracuseStep 3096967 = 4645451) B4645451
theorem B1810823 : Blo 1206420 1810823 := bstep (se 1 (by rfl) ⟨1358117, by rfl⟩ : syracuseStep 1810823 = 2716235) B2716235
theorem B13754771 : Blo 1206420 13754771 := bstep (se 1 (by rfl) ⟨10316078, by rfl⟩ : syracuseStep 13754771 = 20632157) B20632157
theorem B1835435 : Blo 1206420 1835435 := bstep (se 1 (by rfl) ⟨1376576, by rfl⟩ : syracuseStep 1835435 = 2753153) B2753153
theorem B1810859 : Blo 1206420 1810859 := bstep (se 1 (by rfl) ⟨1358144, by rfl⟩ : syracuseStep 1810859 = 2716289) B2716289
theorem B1810889 : Blo 1206420 1810889 := bstep (se 2 (by rfl) ⟨679083, by rfl⟩ : syracuseStep 1810889 = 1358167) B1358167
theorem B14680541 : Blo 1206420 14680541 := bstep (se 3 (by rfl) ⟨2752601, by rfl⟩ : syracuseStep 14680541 = 5505203) B5505203
theorem B5153291 : Blo 1206420 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B6111773 : Blo 1206420 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B1811003 : Blo 1206420 1811003 := bstep (se 1 (by rfl) ⟨1358252, by rfl⟩ : syracuseStep 1811003 = 2716505) B2716505
theorem B1811063 : Blo 1206420 1811063 := bstep (se 1 (by rfl) ⟨1358297, by rfl⟩ : syracuseStep 1811063 = 2716595) B2716595
theorem B1811087 : Blo 1206420 1811087 := bstep (se 1 (by rfl) ⟨1358315, by rfl⟩ : syracuseStep 1811087 = 2716631) B2716631
theorem B1811129 : Blo 1206420 1811129 := bstep (se 2 (by rfl) ⟨679173, by rfl⟩ : syracuseStep 1811129 = 1358347) B1358347
theorem B4072193 : Blo 1206420 4072193 := bstep (se 2 (by rfl) ⟨1527072, by rfl⟩ : syracuseStep 4072193 = 3054145) B3054145
theorem B1811207 : Blo 1206420 1811207 := bstep (se 1 (by rfl) ⟨1358405, by rfl⟩ : syracuseStep 1811207 = 2716811) B2716811
theorem B11019023 : Blo 1206420 11019023 := bstep (se 1 (by rfl) ⟨8264267, by rfl⟩ : syracuseStep 11019023 = 16528535) B16528535
theorem B1811243 : Blo 1206420 1811243 := bstep (se 1 (by rfl) ⟨1358432, by rfl⟩ : syracuseStep 1811243 = 2716865) B2716865
theorem B1811273 : Blo 1206420 1811273 := bstep (se 2 (by rfl) ⟨679227, by rfl⟩ : syracuseStep 1811273 = 1358455) B1358455
theorem B5153651 : Blo 1206420 5153651 := bstep (se 1 (by rfl) ⟨3865238, by rfl⟩ : syracuseStep 5153651 = 7730477) B7730477
theorem B20636531 : Blo 1206420 20636531 := bstep (se 1 (by rfl) ⟨15477398, by rfl⟩ : syracuseStep 20636531 = 30954797) B30954797
theorem B1811387 : Blo 1206420 1811387 := bstep (se 1 (by rfl) ⟨1358540, by rfl⟩ : syracuseStep 1811387 = 2717081) B2717081
theorem B1811447 : Blo 1206420 1811447 := bstep (se 1 (by rfl) ⟨1358585, by rfl⟩ : syracuseStep 1811447 = 2717171) B2717171
theorem B6112259 : Blo 1206420 6112259 := bstep (se 1 (by rfl) ⟨4584194, by rfl⟩ : syracuseStep 6112259 = 9168389) B9168389
theorem B3867659 : Blo 1206420 3867659 := bstep (se 1 (by rfl) ⟨2900744, by rfl⟩ : syracuseStep 3867659 = 5801489) B5801489
theorem B2753551 : Blo 1206420 2753551 := bstep (se 1 (by rfl) ⟨2065163, by rfl⟩ : syracuseStep 2753551 = 4130327) B4130327
theorem B1811471 : Blo 1206420 1811471 := bstep (se 1 (by rfl) ⟨1358603, by rfl⟩ : syracuseStep 1811471 = 2717207) B2717207
theorem B11600941 : Blo 1206420 11600941 := bstep (se 3 (by rfl) ⟨2175176, by rfl⟩ : syracuseStep 11600941 = 4350353) B4350353
theorem B1811513 : Blo 1206420 1811513 := bstep (se 2 (by rfl) ⟨679317, by rfl⟩ : syracuseStep 1811513 = 1358635) B1358635
theorem B1811591 : Blo 1206420 1811591 := bstep (se 1 (by rfl) ⟨1358693, by rfl⟩ : syracuseStep 1811591 = 2717387) B2717387
theorem B1811627 : Blo 1206420 1811627 := bstep (se 1 (by rfl) ⟨1358720, by rfl⟩ : syracuseStep 1811627 = 2717441) B2717441
theorem B1811657 : Blo 1206420 1811657 := bstep (se 2 (by rfl) ⟨679371, by rfl⟩ : syracuseStep 1811657 = 1358743) B1358743
theorem B1811771 : Blo 1206420 1811771 := bstep (se 1 (by rfl) ⟨1358828, by rfl⟩ : syracuseStep 1811771 = 2717657) B2717657
theorem B3057011 : Blo 1206420 3057011 := bstep (se 1 (by rfl) ⟨2292758, by rfl⟩ : syracuseStep 3057011 = 4585517) B4585517
theorem B1836407 : Blo 1206420 1836407 := bstep (se 1 (by rfl) ⟨1377305, by rfl⟩ : syracuseStep 1836407 = 2754611) B2754611
theorem B1811831 : Blo 1206420 1811831 := bstep (se 1 (by rfl) ⟨1358873, by rfl⟩ : syracuseStep 1811831 = 2717747) B2717747
theorem B16516487 : Blo 1206420 16516487 := bstep (se 1 (by rfl) ⟨12387365, by rfl⟩ : syracuseStep 16516487 = 24774731) B24774731
theorem B1811855 : Blo 1206420 1811855 := bstep (se 1 (by rfl) ⟨1358891, by rfl⟩ : syracuseStep 1811855 = 2717783) B2717783
theorem B4073003 : Blo 1206420 4073003 := bstep (se 1 (by rfl) ⟨3054752, by rfl⟩ : syracuseStep 4073003 = 6109505) B6109505
theorem B6612653 : Blo 1206420 6612653 := bstep (se 3 (by rfl) ⟨1239872, by rfl⟩ : syracuseStep 6612653 = 2479745) B2479745
theorem B3057527 : Blo 1206420 3057527 := bstep (se 1 (by rfl) ⟨2293145, by rfl⟩ : syracuseStep 3057527 = 4586291) B4586291
theorem B1206459 : Blo 1206420 1206459 := bstep (se 1 (by rfl) ⟨904844, by rfl⟩ : syracuseStep 1206459 = 1809689) B1809689
theorem B1206535 : Blo 1206420 1206535 := bstep (se 1 (by rfl) ⟨904901, by rfl⟩ : syracuseStep 1206535 = 1809803) B1809803
theorem B2902283 : Blo 1206420 2902283 := bstep (se 1 (by rfl) ⟨2176712, by rfl⟩ : syracuseStep 2902283 = 4353425) B4353425
theorem B1206543 : Blo 1206420 1206543 := bstep (se 1 (by rfl) ⟨904907, by rfl⟩ : syracuseStep 1206543 = 1809815) B1809815
theorem B1206587 : Blo 1206420 1206587 := bstep (se 1 (by rfl) ⟨904940, by rfl⟩ : syracuseStep 1206587 = 1809881) B1809881
theorem B15468893 : Blo 1206420 15468893 := bstep (se 3 (by rfl) ⟨2900417, by rfl⟩ : syracuseStep 15468893 = 5800835) B5800835
theorem B1206663 : Blo 1206420 1206663 := bstep (se 1 (by rfl) ⟨904997, by rfl⟩ : syracuseStep 1206663 = 1809995) B1809995
theorem B1206671 : Blo 1206420 1206671 := bstep (se 1 (by rfl) ⟨905003, by rfl⟩ : syracuseStep 1206671 = 1810007) B1810007
theorem B1206715 : Blo 1206420 1206715 := bstep (se 1 (by rfl) ⟨905036, by rfl⟩ : syracuseStep 1206715 = 1810073) B1810073
theorem B9169361 : Blo 1206420 9169361 := bstep (se 2 (by rfl) ⟨3438510, by rfl⟩ : syracuseStep 9169361 = 6877021) B6877021
theorem B1206791 : Blo 1206420 1206791 := bstep (se 1 (by rfl) ⟨905093, by rfl⟩ : syracuseStep 1206791 = 1810187) B1810187
theorem B1206799 : Blo 1206420 1206799 := bstep (se 1 (by rfl) ⟨905099, by rfl⟩ : syracuseStep 1206799 = 1810199) B1810199
theorem B4581917 : Blo 1206420 4581917 := bstep (se 3 (by rfl) ⟨859109, by rfl⟩ : syracuseStep 4581917 = 1718219) B1718219
theorem B1206843 : Blo 1206420 1206843 := bstep (se 1 (by rfl) ⟨905132, by rfl⟩ : syracuseStep 1206843 = 1810265) B1810265
theorem B6113879 : Blo 1206420 6113879 := bstep (se 1 (by rfl) ⟨4585409, by rfl⟩ : syracuseStep 6113879 = 9170819) B9170819
theorem B1206919 : Blo 1206420 1206919 := bstep (se 1 (by rfl) ⟨905189, by rfl⟩ : syracuseStep 1206919 = 1810379) B1810379
theorem B1206927 : Blo 1206420 1206927 := bstep (se 1 (by rfl) ⟨905195, by rfl⟩ : syracuseStep 1206927 = 1810391) B1810391
theorem B1206971 : Blo 1206420 1206971 := bstep (se 1 (by rfl) ⟨905228, by rfl⟩ : syracuseStep 1206971 = 1810457) B1810457
theorem B3869441 : Blo 1206420 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B1207047 : Blo 1206420 1207047 := bstep (se 1 (by rfl) ⟨905285, by rfl⟩ : syracuseStep 1207047 = 1810571) B1810571
theorem B1207055 : Blo 1206420 1207055 := bstep (se 1 (by rfl) ⟨905291, by rfl⟩ : syracuseStep 1207055 = 1810583) B1810583
theorem B1207099 : Blo 1206420 1207099 := bstep (se 1 (by rfl) ⟨905324, by rfl⟩ : syracuseStep 1207099 = 1810649) B1810649
theorem B4074299 : Blo 1206420 4074299 := bstep (se 1 (by rfl) ⟨3055724, by rfl⟩ : syracuseStep 4074299 = 6111449) B6111449
theorem B1207175 : Blo 1206420 1207175 := bstep (se 1 (by rfl) ⟨905381, by rfl⟩ : syracuseStep 1207175 = 1810763) B1810763
theorem B1207183 : Blo 1206420 1207183 := bstep (se 1 (by rfl) ⟨905387, by rfl⟩ : syracuseStep 1207183 = 1810775) B1810775
theorem B31771541 : Blo 1206420 31771541 := bstep (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) B1489291
theorem B6876089 : Blo 1206420 6876089 := bstep (se 2 (by rfl) ⟨2578533, by rfl⟩ : syracuseStep 6876089 = 5157067) B5157067
theorem B1207227 : Blo 1206420 1207227 := bstep (se 1 (by rfl) ⟨905420, by rfl⟩ : syracuseStep 1207227 = 1810841) B1810841
theorem B1207303 : Blo 1206420 1207303 := bstep (se 1 (by rfl) ⟨905477, by rfl⟩ : syracuseStep 1207303 = 1810955) B1810955
theorem B1207311 : Blo 1206420 1207311 := bstep (se 1 (by rfl) ⟨905483, by rfl⟩ : syracuseStep 1207311 = 1810967) B1810967
theorem B1207355 : Blo 1206420 1207355 := bstep (se 1 (by rfl) ⟨905516, by rfl⟩ : syracuseStep 1207355 = 1811033) B1811033
theorem B6114365 : Blo 1206420 6114365 := bstep (se 3 (by rfl) ⟨1146443, by rfl⟩ : syracuseStep 6114365 = 2292887) B2292887
theorem B2714759 : Blo 1206420 2714759 := bstep (se 1 (by rfl) ⟨2036069, by rfl⟩ : syracuseStep 2714759 = 4072139) B4072139
theorem B1207431 : Blo 1206420 1207431 := bstep (se 1 (by rfl) ⟨905573, by rfl⟩ : syracuseStep 1207431 = 1811147) B1811147
theorem B1207439 : Blo 1206420 1207439 := bstep (se 1 (by rfl) ⟨905579, by rfl⟩ : syracuseStep 1207439 = 1811159) B1811159
theorem B1207483 : Blo 1206420 1207483 := bstep (se 1 (by rfl) ⟨905612, by rfl⟩ : syracuseStep 1207483 = 1811225) B1811225
theorem B4582601 : Blo 1206420 4582601 := bstep (se 2 (by rfl) ⟨1718475, by rfl⟩ : syracuseStep 4582601 = 3436951) B3436951
theorem B1207559 : Blo 1206420 1207559 := bstep (se 1 (by rfl) ⟨905669, by rfl⟩ : syracuseStep 1207559 = 1811339) B1811339
theorem B1207567 : Blo 1206420 1207567 := bstep (se 1 (by rfl) ⟨905675, by rfl⟩ : syracuseStep 1207567 = 1811351) B1811351
theorem B4074785 : Blo 1206420 4074785 := bstep (se 2 (by rfl) ⟨1528044, by rfl⟩ : syracuseStep 4074785 = 3056089) B3056089
theorem B2714939 : Blo 1206420 2714939 := bstep (se 1 (by rfl) ⟨2036204, by rfl⟩ : syracuseStep 2714939 = 4072409) B4072409
theorem B1207611 : Blo 1206420 1207611 := bstep (se 1 (by rfl) ⟨905708, by rfl⟩ : syracuseStep 1207611 = 1811417) B1811417
theorem B1207687 : Blo 1206420 1207687 := bstep (se 1 (by rfl) ⟨905765, by rfl⟩ : syracuseStep 1207687 = 1811531) B1811531
theorem B1207695 : Blo 1206420 1207695 := bstep (se 1 (by rfl) ⟨905771, by rfl⟩ : syracuseStep 1207695 = 1811543) B1811543
theorem B2715065 : Blo 1206420 2715065 := bstep (se 2 (by rfl) ⟨1018149, by rfl⟩ : syracuseStep 2715065 = 2036299) B2036299
theorem B1207739 : Blo 1206420 1207739 := bstep (se 1 (by rfl) ⟨905804, by rfl⟩ : syracuseStep 1207739 = 1811609) B1811609
theorem B66096593 : Blo 1206420 66096593 := bstep (se 2 (by rfl) ⟨24786222, by rfl⟩ : syracuseStep 66096593 = 49572445) B49572445
theorem B1207815 : Blo 1206420 1207815 := bstep (se 1 (by rfl) ⟨905861, by rfl⟩ : syracuseStep 1207815 = 1811723) B1811723
theorem B1207823 : Blo 1206420 1207823 := bstep (se 1 (by rfl) ⟨905867, by rfl⟩ : syracuseStep 1207823 = 1811735) B1811735
theorem B1207867 : Blo 1206420 1207867 := bstep (se 1 (by rfl) ⟨905900, by rfl⟩ : syracuseStep 1207867 = 1811801) B1811801
theorem B26095283 : Blo 1206420 26095283 := bstep (se 1 (by rfl) ⟨19571462, by rfl⟩ : syracuseStep 26095283 = 39142925) B39142925
theorem B9678565 : Blo 1206420 9678565 := bstep (se 4 (by rfl) ⟨907365, by rfl⟩ : syracuseStep 9678565 = 1814731) B1814731
theorem B2715407 : Blo 1206420 2715407 := bstep (se 1 (by rfl) ⟨2036555, by rfl⟩ : syracuseStep 2715407 = 4073111) B4073111
theorem B2715425 : Blo 1206420 2715425 := bstep (se 2 (by rfl) ⟨1018284, by rfl⟩ : syracuseStep 2715425 = 2036569) B2036569
theorem B11595595 : Blo 1206420 11595595 := bstep (se 1 (by rfl) ⟨8696696, by rfl⟩ : syracuseStep 11595595 = 17393393) B17393393
theorem B4075379 : Blo 1206420 4075379 := bstep (se 1 (by rfl) ⟨3056534, by rfl⟩ : syracuseStep 4075379 = 6113069) B6113069
theorem B2174867 : Blo 1206420 2174867 := bstep (se 1 (by rfl) ⟨1631150, by rfl⟩ : syracuseStep 2174867 = 3262301) B3262301
theorem B29364119 : Blo 1206420 29364119 := bstep (se 1 (by rfl) ⟨22023089, by rfl⟩ : syracuseStep 29364119 = 44046179) B44046179
theorem B7737241 : Blo 1206420 7737241 := bstep (se 2 (by rfl) ⟨2901465, by rfl⟩ : syracuseStep 7737241 = 5802931) B5802931
theorem B2715767 : Blo 1206420 2715767 := bstep (se 1 (by rfl) ⟨2036825, by rfl⟩ : syracuseStep 2715767 = 4073651) B4073651
theorem B2035847 : Blo 1206420 2035847 := bstep (se 1 (by rfl) ⟨1526885, by rfl⟩ : syracuseStep 2035847 = 3053771) B3053771
theorem B1527979 : Blo 1206420 1527979 := bstep (se 1 (by rfl) ⟨1145984, by rfl⟩ : syracuseStep 1527979 = 2291969) B2291969
theorem B2715947 : Blo 1206420 2715947 := bstep (se 1 (by rfl) ⟨2036960, by rfl⟩ : syracuseStep 2715947 = 4073921) B4073921
theorem B11604359 : Blo 1206420 11604359 := bstep (se 1 (by rfl) ⟨8703269, by rfl⟩ : syracuseStep 11604359 = 17406539) B17406539
theorem B3436985 : Blo 1206420 3436985 := bstep (se 2 (by rfl) ⟨1288869, by rfl⟩ : syracuseStep 3436985 = 2577739) B2577739
theorem B451957265 : Blo 1206420 451957265 := bstep (se 2 (by rfl) ⟨169483974, by rfl⟩ : syracuseStep 451957265 = 338967949) B338967949
theorem B38171179 : Blo 1206420 38171179 := bstep (se 1 (by rfl) ⟨28628384, by rfl⟩ : syracuseStep 38171179 = 57256769) B57256769
theorem B3437099 : Blo 1206420 3437099 := bstep (se 1 (by rfl) ⟨2577824, by rfl⟩ : syracuseStep 3437099 = 5155649) B5155649
theorem B2716307 : Blo 1206420 2716307 := bstep (se 1 (by rfl) ⟨2037230, by rfl⟩ : syracuseStep 2716307 = 4074461) B4074461
theorem B2716361 : Blo 1206420 2716361 := bstep (se 2 (by rfl) ⟨1018635, by rfl⟩ : syracuseStep 2716361 = 2037271) B2037271
theorem B7738085 : Blo 1206420 7738085 := bstep (se 4 (by rfl) ⟨725445, by rfl⟩ : syracuseStep 7738085 = 1450891) B1450891
theorem B6107885 : Blo 1206420 6107885 := bstep (se 3 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 6107885 = 2290457) B2290457
theorem B2577167 : Blo 1206420 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B2036495 : Blo 1206420 2036495 := bstep (se 1 (by rfl) ⟨1527371, by rfl⟩ : syracuseStep 2036495 = 3054743) B3054743
theorem B5157665 : Blo 1206420 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B4584377 : Blo 1206420 4584377 := bstep (se 2 (by rfl) ⟨1719141, by rfl⟩ : syracuseStep 4584377 = 3438283) B3438283
theorem B6968267 : Blo 1206420 6968267 := bstep (se 1 (by rfl) ⟨5226200, by rfl⟩ : syracuseStep 6968267 = 10452401) B10452401
theorem B11015369 : Blo 1206420 11015369 := bstep (se 2 (by rfl) ⟨4130763, by rfl⟩ : syracuseStep 11015369 = 8261527) B8261527
theorem B6878479 : Blo 1206420 6878479 := bstep (se 1 (by rfl) ⟨5158859, by rfl⟩ : syracuseStep 6878479 = 10317719) B10317719
theorem B2037035 : Blo 1206420 2037035 := bstep (se 1 (by rfl) ⟨1527776, by rfl⟩ : syracuseStep 2037035 = 3055553) B3055553
theorem B7337351 : Blo 1206420 7337351 := bstep (se 1 (by rfl) ⟨5503013, by rfl⟩ : syracuseStep 7337351 = 11006027) B11006027
theorem B2717063 : Blo 1206420 2717063 := bstep (se 1 (by rfl) ⟨2037797, by rfl⟩ : syracuseStep 2717063 = 4075595) B4075595
theorem B6108695 : Blo 1206420 6108695 := bstep (se 1 (by rfl) ⟨4581521, by rfl⟩ : syracuseStep 6108695 = 9163043) B9163043
theorem B2717243 : Blo 1206420 2717243 := bstep (se 1 (by rfl) ⟨2037932, by rfl⟩ : syracuseStep 2717243 = 4075865) B4075865
theorem B1357447 : Blo 1206420 1357447 := bstep (se 1 (by rfl) ⟨1018085, by rfl⟩ : syracuseStep 1357447 = 2036171) B2036171
theorem B3438227 : Blo 1206420 3438227 := bstep (se 1 (by rfl) ⟨2578670, by rfl⟩ : syracuseStep 3438227 = 5157341) B5157341
theorem B2037433 : Blo 1206420 2037433 := bstep (se 2 (by rfl) ⟨764037, by rfl⟩ : syracuseStep 2037433 = 1528075) B1528075
theorem B2717369 : Blo 1206420 2717369 := bstep (se 2 (by rfl) ⟨1019013, by rfl⟩ : syracuseStep 2717369 = 2038027) B2038027
theorem B2447147 : Blo 1206420 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B1357627 : Blo 1206420 1357627 := bstep (se 1 (by rfl) ⟨1018220, by rfl⟩ : syracuseStep 1357627 = 2036441) B2036441
theorem B2717711 : Blo 1206420 2717711 := bstep (se 1 (by rfl) ⟨2038283, by rfl⟩ : syracuseStep 2717711 = 4076567) B4076567
theorem B3438625 : Blo 1206420 3438625 := bstep (se 2 (by rfl) ⟨1289484, by rfl⟩ : syracuseStep 3438625 = 2578969) B2578969
theorem B2717729 : Blo 1206420 2717729 := bstep (se 2 (by rfl) ⟨1019148, by rfl⟩ : syracuseStep 2717729 = 2038297) B2038297
theorem B16750709 : Blo 1206420 16750709 := bstep (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) B1570379
theorem B2938999 : Blo 1206420 2938999 := bstep (se 1 (by rfl) ⟨2204249, by rfl⟩ : syracuseStep 2938999 = 4408499) B4408499
theorem B17406197 : Blo 1206420 17406197 := bstep (se 5 (by rfl) ⟨815915, by rfl⟩ : syracuseStep 17406197 = 1631831) B1631831
theorem B1358095 : Blo 1206420 1358095 := bstep (se 1 (by rfl) ⟨1018571, by rfl⟩ : syracuseStep 1358095 = 2037143) B2037143
theorem B2578807 : Blo 1206420 2578807 := bstep (se 1 (by rfl) ⟨1934105, by rfl⟩ : syracuseStep 2578807 = 3868211) B3868211
theorem B2038135 : Blo 1206420 2038135 := bstep (se 1 (by rfl) ⟨1528601, by rfl⟩ : syracuseStep 2038135 = 3057203) B3057203
theorem B1718663 : Blo 1206420 1718663 := bstep (se 1 (by rfl) ⟨1288997, by rfl⟩ : syracuseStep 1718663 = 2577995) B2577995
theorem B89332109 : Blo 1206420 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B8255891 : Blo 1206420 8255891 := bstep (se 1 (by rfl) ⟨6191918, by rfl⟩ : syracuseStep 8255891 = 12383837) B12383837
theorem B9066937 : Blo 1206420 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B60340697 : Blo 1206420 60340697 := bstep (se 2 (by rfl) ⟨22627761, by rfl⟩ : syracuseStep 60340697 = 45255523) B45255523
theorem B3054095 : Blo 1206420 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B2038331 : Blo 1206420 2038331 := bstep (se 1 (by rfl) ⟨1528748, by rfl⟩ : syracuseStep 2038331 = 3057497) B3057497
theorem B1718857 : Blo 1206420 1718857 := bstep (se 2 (by rfl) ⟨644571, by rfl⟩ : syracuseStep 1718857 = 1289143) B1289143
theorem B2292371 : Blo 1206420 2292371 := bstep (se 1 (by rfl) ⟨1719278, by rfl⟩ : syracuseStep 2292371 = 3438557) B3438557
theorem B1358599 : Blo 1206420 1358599 := bstep (se 1 (by rfl) ⟨1018949, by rfl⟩ : syracuseStep 1358599 = 2037899) B2037899
theorem B26114831 : Blo 1206420 26114831 := bstep (se 1 (by rfl) ⟨19586123, by rfl⟩ : syracuseStep 26114831 = 39172247) B39172247
theorem B2292599 : Blo 1206420 2292599 := bstep (se 1 (by rfl) ⟨1719449, by rfl⟩ : syracuseStep 2292599 = 3438899) B3438899
theorem B2898823 : Blo 1206420 2898823 := bstep (se 1 (by rfl) ⟨2174117, by rfl⟩ : syracuseStep 2898823 = 4348235) B4348235
theorem B3439513 : Blo 1206420 3439513 := bstep (se 2 (by rfl) ⟨1289817, by rfl⟩ : syracuseStep 3439513 = 2579635) B2579635
theorem B1358779 : Blo 1206420 1358779 := bstep (se 1 (by rfl) ⟨1019084, by rfl⟩ : syracuseStep 1358779 = 2038169) B2038169
theorem B1719415 : Blo 1206420 1719415 := bstep (se 1 (by rfl) ⟨1289561, by rfl⟩ : syracuseStep 1719415 = 2579123) B2579123
theorem B2899091 : Blo 1206420 2899091 := bstep (se 1 (by rfl) ⟨2174318, by rfl⟩ : syracuseStep 2899091 = 4348637) B4348637
theorem B3054793 : Blo 1206420 3054793 := bstep (se 2 (by rfl) ⟨1145547, by rfl⟩ : syracuseStep 3054793 = 2291095) B2291095
theorem B1809671 : Blo 1206420 1809671 := bstep (se 1 (by rfl) ⟨1357253, by rfl⟩ : syracuseStep 1809671 = 2714507) B2714507
theorem B1809707 : Blo 1206420 1809707 := bstep (se 1 (by rfl) ⟨1357280, by rfl⟩ : syracuseStep 1809707 = 2714561) B2714561
theorem B1932587 : Blo 1206420 1932587 := bstep (se 1 (by rfl) ⟨1449440, by rfl⟩ : syracuseStep 1932587 = 2898881) B2898881
theorem B1809737 : Blo 1206420 1809737 := bstep (se 2 (by rfl) ⟨678651, by rfl⟩ : syracuseStep 1809737 = 1357303) B1357303
theorem B3054935 : Blo 1206420 3054935 := bstep (se 1 (by rfl) ⟨2291201, by rfl⟩ : syracuseStep 3054935 = 4582403) B4582403
theorem B6872465 : Blo 1206420 6872465 := bstep (se 2 (by rfl) ⟨2577174, by rfl⟩ : syracuseStep 6872465 = 5154349) B5154349
theorem B1809851 : Blo 1206420 1809851 := bstep (se 1 (by rfl) ⟨1357388, by rfl⟩ : syracuseStep 1809851 = 2714777) B2714777
theorem B1809911 : Blo 1206420 1809911 := bstep (se 1 (by rfl) ⟨1357433, by rfl⟩ : syracuseStep 1809911 = 2714867) B2714867
theorem B1809935 : Blo 1206420 1809935 := bstep (se 1 (by rfl) ⟨1357451, by rfl⟩ : syracuseStep 1809935 = 2714903) B2714903
theorem B1809977 : Blo 1206420 1809977 := bstep (se 2 (by rfl) ⟨678741, by rfl⟩ : syracuseStep 1809977 = 1357483) B1357483
theorem B1810055 : Blo 1206420 1810055 := bstep (se 1 (by rfl) ⟨1357541, by rfl⟩ : syracuseStep 1810055 = 2715083) B2715083
theorem B1810091 : Blo 1206420 1810091 := bstep (se 1 (by rfl) ⟨1357568, by rfl⟩ : syracuseStep 1810091 = 2715137) B2715137
theorem B1810121 : Blo 1206420 1810121 := bstep (se 2 (by rfl) ⟨678795, by rfl⟩ : syracuseStep 1810121 = 1357591) B1357591
theorem B1810235 : Blo 1206420 1810235 := bstep (se 1 (by rfl) ⟨1357676, by rfl⟩ : syracuseStep 1810235 = 2715353) B2715353
theorem B6872921 : Blo 1206420 6872921 := bstep (se 2 (by rfl) ⟨2577345, by rfl⟩ : syracuseStep 6872921 = 5154691) B5154691
theorem B1810295 : Blo 1206420 1810295 := bstep (se 1 (by rfl) ⟨1357721, by rfl⟩ : syracuseStep 1810295 = 2715443) B2715443
theorem B1810319 : Blo 1206420 1810319 := bstep (se 1 (by rfl) ⟨1357739, by rfl⟩ : syracuseStep 1810319 = 2715479) B2715479
theorem B1810361 : Blo 1206420 1810361 := bstep (se 2 (by rfl) ⟨678885, by rfl⟩ : syracuseStep 1810361 = 1357771) B1357771
theorem B8486927 : Blo 1206420 8486927 := bstep (se 1 (by rfl) ⟨6365195, by rfl⟩ : syracuseStep 8486927 = 12730391) B12730391
theorem B8257565 : Blo 1206420 8257565 := bstep (se 3 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 8257565 = 3096587) B3096587
theorem B1810511 : Blo 1206420 1810511 := bstep (se 1 (by rfl) ⟨1357883, by rfl⟩ : syracuseStep 1810511 = 2715767) B2715767
theorem B1810631 : Blo 1206420 1810631 := bstep (se 1 (by rfl) ⟨1357973, by rfl⟩ : syracuseStep 1810631 = 2715947) B2715947
theorem B4129015 : Blo 1206420 4129015 := bstep (se 1 (by rfl) ⟨3096761, by rfl⟩ : syracuseStep 4129015 = 6193523) B6193523
theorem B1933561 : Blo 1206420 1933561 := bstep (se 2 (by rfl) ⟨725085, by rfl⟩ : syracuseStep 1933561 = 1450171) B1450171
theorem B1810793 : Blo 1206420 1810793 := bstep (se 2 (by rfl) ⟨679047, by rfl⟩ : syracuseStep 1810793 = 1358095) B1358095
theorem B1810871 : Blo 1206420 1810871 := bstep (se 1 (by rfl) ⟨1358153, by rfl⟩ : syracuseStep 1810871 = 2716307) B2716307
theorem B1810907 : Blo 1206420 1810907 := bstep (se 1 (by rfl) ⟨1358180, by rfl⟩ : syracuseStep 1810907 = 2716361) B2716361
theorem B4071923 : Blo 1206420 4071923 := bstep (se 1 (by rfl) ⟨3053942, by rfl⟩ : syracuseStep 4071923 = 6107885) B6107885
theorem B4129289 : Blo 1206420 4129289 := bstep (se 2 (by rfl) ⟨1548483, by rfl⟩ : syracuseStep 4129289 = 3096967) B3096967
theorem B3056251 : Blo 1206420 3056251 := bstep (se 1 (by rfl) ⟨2292188, by rfl⟩ : syracuseStep 3056251 = 4584377) B4584377
theorem B4645511 : Blo 1206420 4645511 := bstep (se 1 (by rfl) ⟨3484133, by rfl⟩ : syracuseStep 4645511 = 6968267) B6968267
theorem B11010991 : Blo 1206420 11010991 := bstep (se 1 (by rfl) ⟨8258243, by rfl⟩ : syracuseStep 11010991 = 16516487) B16516487
theorem B1811375 : Blo 1206420 1811375 := bstep (se 1 (by rfl) ⟨1358531, by rfl⟩ : syracuseStep 1811375 = 2717063) B2717063
theorem B1811465 : Blo 1206420 1811465 := bstep (se 2 (by rfl) ⟨679299, by rfl⟩ : syracuseStep 1811465 = 1358599) B1358599
theorem B4072463 : Blo 1206420 4072463 := bstep (se 1 (by rfl) ⟨3054347, by rfl⟩ : syracuseStep 4072463 = 6108695) B6108695
theorem B1811495 : Blo 1206420 1811495 := bstep (se 1 (by rfl) ⟨1358621, by rfl⟩ : syracuseStep 1811495 = 2717243) B2717243
theorem B4408435 : Blo 1206420 4408435 := bstep (se 1 (by rfl) ⟨3306326, by rfl⟩ : syracuseStep 4408435 = 6612653) B6612653
theorem B1811579 : Blo 1206420 1811579 := bstep (se 1 (by rfl) ⟨1358684, by rfl⟩ : syracuseStep 1811579 = 2717369) B2717369
theorem B1631431 : Blo 1206420 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B1811705 : Blo 1206420 1811705 := bstep (se 2 (by rfl) ⟨679389, by rfl⟩ : syracuseStep 1811705 = 1358779) B1358779
theorem B1811807 : Blo 1206420 1811807 := bstep (se 1 (by rfl) ⟨1358855, by rfl⟩ : syracuseStep 1811807 = 2717711) B2717711
theorem B3671401 : Blo 1206420 3671401 := bstep (se 2 (by rfl) ⟨1376775, by rfl⟩ : syracuseStep 3671401 = 2753551) B2753551
theorem B1811819 : Blo 1206420 1811819 := bstep (se 1 (by rfl) ⟨1358864, by rfl⟩ : syracuseStep 1811819 = 2717729) B2717729
theorem B15467921 : Blo 1206420 15467921 := bstep (se 2 (by rfl) ⟨5800470, by rfl⟩ : syracuseStep 15467921 = 11600941) B11600941
theorem B11167139 : Blo 1206420 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B1934855 : Blo 1206420 1934855 := bstep (se 1 (by rfl) ⟨1451141, by rfl⟩ : syracuseStep 1934855 = 2902283) B2902283
theorem B4073057 : Blo 1206420 4073057 := bstep (se 2 (by rfl) ⟨1527396, by rfl⟩ : syracuseStep 4073057 = 3054793) B3054793
theorem B6112907 : Blo 1206420 6112907 := bstep (se 1 (by rfl) ⟨4584680, by rfl⟩ : syracuseStep 6112907 = 9169361) B9169361
theorem B17409887 : Blo 1206420 17409887 := bstep (se 1 (by rfl) ⟨13057415, by rfl⟩ : syracuseStep 17409887 = 26114831) B26114831
theorem B1206447 : Blo 1206420 1206447 := bstep (se 1 (by rfl) ⟨904835, by rfl⟩ : syracuseStep 1206447 = 1809671) B1809671
theorem B1206471 : Blo 1206420 1206471 := bstep (se 1 (by rfl) ⟨904853, by rfl⟩ : syracuseStep 1206471 = 1809707) B1809707
theorem B1288391 : Blo 1206420 1288391 := bstep (se 1 (by rfl) ⟨966293, by rfl⟩ : syracuseStep 1288391 = 1932587) B1932587
theorem B1206491 : Blo 1206420 1206491 := bstep (se 1 (by rfl) ⟨904868, by rfl⟩ : syracuseStep 1206491 = 1809737) B1809737
theorem B4581643 : Blo 1206420 4581643 := bstep (se 1 (by rfl) ⟨3436232, by rfl⟩ : syracuseStep 4581643 = 6872465) B6872465
theorem B1206567 : Blo 1206420 1206567 := bstep (se 1 (by rfl) ⟨904925, by rfl⟩ : syracuseStep 1206567 = 1809851) B1809851
theorem B12904753 : Blo 1206420 12904753 := bstep (se 2 (by rfl) ⟨4839282, by rfl⟩ : syracuseStep 12904753 = 9678565) B9678565
theorem B1206607 : Blo 1206420 1206607 := bstep (se 1 (by rfl) ⟨904955, by rfl⟩ : syracuseStep 1206607 = 1809911) B1809911
theorem B1206623 : Blo 1206420 1206623 := bstep (se 1 (by rfl) ⟨904967, by rfl⟩ : syracuseStep 1206623 = 1809935) B1809935
theorem B1206651 : Blo 1206420 1206651 := bstep (se 1 (by rfl) ⟨904988, by rfl⟩ : syracuseStep 1206651 = 1809977) B1809977
theorem B1206703 : Blo 1206420 1206703 := bstep (se 1 (by rfl) ⟨905027, by rfl⟩ : syracuseStep 1206703 = 1810055) B1810055
theorem B15460793 : Blo 1206420 15460793 := bstep (se 2 (by rfl) ⟨5797797, by rfl⟩ : syracuseStep 15460793 = 11595595) B11595595
theorem B1206727 : Blo 1206420 1206727 := bstep (se 1 (by rfl) ⟨905045, by rfl⟩ : syracuseStep 1206727 = 1810091) B1810091
theorem B1206747 : Blo 1206420 1206747 := bstep (se 1 (by rfl) ⟨905060, by rfl⟩ : syracuseStep 1206747 = 1810121) B1810121
theorem B10316321 : Blo 1206420 10316321 := bstep (se 2 (by rfl) ⟨3868620, by rfl⟩ : syracuseStep 10316321 = 7737241) B7737241
theorem B1206823 : Blo 1206420 1206823 := bstep (se 1 (by rfl) ⟨905117, by rfl⟩ : syracuseStep 1206823 = 1810235) B1810235
theorem B4581947 : Blo 1206420 4581947 := bstep (se 1 (by rfl) ⟨3436460, by rfl⟩ : syracuseStep 4581947 = 6872921) B6872921
theorem B1206863 : Blo 1206420 1206863 := bstep (se 1 (by rfl) ⟨905147, by rfl⟩ : syracuseStep 1206863 = 1810295) B1810295
theorem B1206879 : Blo 1206420 1206879 := bstep (se 1 (by rfl) ⟨905159, by rfl⟩ : syracuseStep 1206879 = 1810319) B1810319
theorem B1206907 : Blo 1206420 1206907 := bstep (se 1 (by rfl) ⟨905180, by rfl⟩ : syracuseStep 1206907 = 1810361) B1810361
theorem B1206959 : Blo 1206420 1206959 := bstep (se 1 (by rfl) ⟨905219, by rfl⟩ : syracuseStep 1206959 = 1810439) B1810439
theorem B1206983 : Blo 1206420 1206983 := bstep (se 1 (by rfl) ⟨905237, by rfl⟩ : syracuseStep 1206983 = 1810475) B1810475
theorem B1207003 : Blo 1206420 1207003 := bstep (se 1 (by rfl) ⟨905252, by rfl⟩ : syracuseStep 1207003 = 1810505) B1810505
theorem B1207079 : Blo 1206420 1207079 := bstep (se 1 (by rfl) ⟨905309, by rfl⟩ : syracuseStep 1207079 = 1810619) B1810619
theorem B3918665 : Blo 1206420 3918665 := bstep (se 2 (by rfl) ⟨1469499, by rfl⟩ : syracuseStep 3918665 = 2938999) B2938999
theorem B1207119 : Blo 1206420 1207119 := bstep (se 1 (by rfl) ⟨905339, by rfl⟩ : syracuseStep 1207119 = 1810679) B1810679
theorem B1207135 : Blo 1206420 1207135 := bstep (se 1 (by rfl) ⟨905351, by rfl⟩ : syracuseStep 1207135 = 1810703) B1810703
theorem B1207163 : Blo 1206420 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B89303957 : Blo 1206420 89303957 := bstep (se 6 (by rfl) ⟨2093061, by rfl⟩ : syracuseStep 89303957 = 4186123) B4186123
theorem B2714543 : Blo 1206420 2714543 := bstep (se 1 (by rfl) ⟨2035907, by rfl⟩ : syracuseStep 2714543 = 4071815) B4071815
theorem B1207215 : Blo 1206420 1207215 := bstep (se 1 (by rfl) ⟨905411, by rfl⟩ : syracuseStep 1207215 = 1810823) B1810823
theorem B7736239 : Blo 1206420 7736239 := bstep (se 1 (by rfl) ⟨5802179, by rfl⟩ : syracuseStep 7736239 = 11604359) B11604359
theorem B9169847 : Blo 1206420 9169847 := bstep (se 1 (by rfl) ⟨6877385, by rfl⟩ : syracuseStep 9169847 = 13754771) B13754771
theorem B1223623 : Blo 1206420 1223623 := bstep (se 1 (by rfl) ⟨917717, by rfl⟩ : syracuseStep 1223623 = 1835435) B1835435
theorem B1207239 : Blo 1206420 1207239 := bstep (se 1 (by rfl) ⟨905429, by rfl⟩ : syracuseStep 1207239 = 1810859) B1810859
theorem B1207259 : Blo 1206420 1207259 := bstep (se 1 (by rfl) ⟨905444, by rfl⟩ : syracuseStep 1207259 = 1810889) B1810889
theorem B3435527 : Blo 1206420 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B301304843 : Blo 1206420 301304843 := bstep (se 1 (by rfl) ⟨225978632, by rfl⟩ : syracuseStep 301304843 = 451957265) B451957265
theorem B4074515 : Blo 1206420 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B1207335 : Blo 1206420 1207335 := bstep (se 1 (by rfl) ⟨905501, by rfl⟩ : syracuseStep 1207335 = 1811003) B1811003
theorem B1207375 : Blo 1206420 1207375 := bstep (se 1 (by rfl) ⟨905531, by rfl⟩ : syracuseStep 1207375 = 1811063) B1811063
theorem B1207391 : Blo 1206420 1207391 := bstep (se 1 (by rfl) ⟨905543, by rfl⟩ : syracuseStep 1207391 = 1811087) B1811087
theorem B1207419 : Blo 1206420 1207419 := bstep (se 1 (by rfl) ⟨905564, by rfl⟩ : syracuseStep 1207419 = 1811129) B1811129
theorem B2714795 : Blo 1206420 2714795 := bstep (se 1 (by rfl) ⟨2036096, by rfl⟩ : syracuseStep 2714795 = 4072193) B4072193
theorem B1207471 : Blo 1206420 1207471 := bstep (se 1 (by rfl) ⟨905603, by rfl⟩ : syracuseStep 1207471 = 1811207) B1811207
theorem B1207495 : Blo 1206420 1207495 := bstep (se 1 (by rfl) ⟨905621, by rfl⟩ : syracuseStep 1207495 = 1811243) B1811243
theorem B1207515 : Blo 1206420 1207515 := bstep (se 1 (by rfl) ⟨905636, by rfl⟩ : syracuseStep 1207515 = 1811273) B1811273
theorem B3435767 : Blo 1206420 3435767 := bstep (se 1 (by rfl) ⟨2576825, by rfl⟩ : syracuseStep 3435767 = 5153651) B5153651
theorem B13757687 : Blo 1206420 13757687 := bstep (se 1 (by rfl) ⟨10318265, by rfl⟩ : syracuseStep 13757687 = 20636531) B20636531
theorem B1207591 : Blo 1206420 1207591 := bstep (se 1 (by rfl) ⟨905693, by rfl⟩ : syracuseStep 1207591 = 1811387) B1811387
theorem B1207631 : Blo 1206420 1207631 := bstep (se 1 (by rfl) ⟨905723, by rfl⟩ : syracuseStep 1207631 = 1811447) B1811447
theorem B4074839 : Blo 1206420 4074839 := bstep (se 1 (by rfl) ⟨3056129, by rfl⟩ : syracuseStep 4074839 = 6112259) B6112259
theorem B1207647 : Blo 1206420 1207647 := bstep (se 1 (by rfl) ⟨905735, by rfl⟩ : syracuseStep 1207647 = 1811471) B1811471
theorem B1207675 : Blo 1206420 1207675 := bstep (se 1 (by rfl) ⟨905756, by rfl⟩ : syracuseStep 1207675 = 1811513) B1811513
theorem B1207727 : Blo 1206420 1207727 := bstep (se 1 (by rfl) ⟨905795, by rfl⟩ : syracuseStep 1207727 = 1811591) B1811591
theorem B1207751 : Blo 1206420 1207751 := bstep (se 1 (by rfl) ⟨905813, by rfl⟩ : syracuseStep 1207751 = 1811627) B1811627
theorem B7343579 : Blo 1206420 7343579 := bstep (se 1 (by rfl) ⟨5507684, by rfl⟩ : syracuseStep 7343579 = 11015369) B11015369
theorem B1207771 : Blo 1206420 1207771 := bstep (se 1 (by rfl) ⟨905828, by rfl⟩ : syracuseStep 1207771 = 1811657) B1811657
theorem B1207847 : Blo 1206420 1207847 := bstep (se 1 (by rfl) ⟨905885, by rfl⟩ : syracuseStep 1207847 = 1811771) B1811771
theorem B1224271 : Blo 1206420 1224271 := bstep (se 1 (by rfl) ⟨918203, by rfl⟩ : syracuseStep 1224271 = 1836407) B1836407
theorem B1207887 : Blo 1206420 1207887 := bstep (se 1 (by rfl) ⟨905915, by rfl⟩ : syracuseStep 1207887 = 1811831) B1811831
theorem B1207903 : Blo 1206420 1207903 := bstep (se 1 (by rfl) ⟨905927, by rfl⟩ : syracuseStep 1207903 = 1811855) B1811855
theorem B19566269 : Blo 1206420 19566269 := bstep (se 3 (by rfl) ⟨3668675, by rfl⟩ : syracuseStep 19566269 = 7337351) B7337351
theorem B4583101 : Blo 1206420 4583101 := bstep (se 3 (by rfl) ⟨859331, by rfl⟩ : syracuseStep 4583101 = 1718663) B1718663
theorem B2715335 : Blo 1206420 2715335 := bstep (se 1 (by rfl) ⟨2036501, by rfl⟩ : syracuseStep 2715335 = 4073003) B4073003
theorem B22015709 : Blo 1206420 22015709 := bstep (se 3 (by rfl) ⟨4127945, by rfl⟩ : syracuseStep 22015709 = 8255891) B8255891
theorem B11604131 : Blo 1206420 11604131 := bstep (se 1 (by rfl) ⟨8703098, by rfl⟩ : syracuseStep 11604131 = 17406197) B17406197
theorem B40227131 : Blo 1206420 40227131 := bstep (se 1 (by rfl) ⟨30170348, by rfl⟩ : syracuseStep 40227131 = 60340697) B60340697
theorem B2036063 : Blo 1206420 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B9171305 : Blo 1206420 9171305 := bstep (se 2 (by rfl) ⟨3439239, by rfl⟩ : syracuseStep 9171305 = 6878479) B6878479
theorem B4075919 : Blo 1206420 4075919 := bstep (se 1 (by rfl) ⟨3056939, by rfl⟩ : syracuseStep 4075919 = 6113879) B6113879
theorem B1528247 : Blo 1206420 1528247 := bstep (se 1 (by rfl) ⟨1146185, by rfl⟩ : syracuseStep 1528247 = 2292371) B2292371
theorem B2716199 : Blo 1206420 2716199 := bstep (se 1 (by rfl) ⟨2037149, by rfl⟩ : syracuseStep 2716199 = 4074299) B4074299
theorem B1528399 : Blo 1206420 1528399 := bstep (se 1 (by rfl) ⟨1146299, by rfl⟩ : syracuseStep 1528399 = 2292599) B2292599
theorem B21181027 : Blo 1206420 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B4584059 : Blo 1206420 4584059 := bstep (se 1 (by rfl) ⟨3438044, by rfl⟩ : syracuseStep 4584059 = 6876089) B6876089
theorem B4076243 : Blo 1206420 4076243 := bstep (se 1 (by rfl) ⟨3057182, by rfl⟩ : syracuseStep 4076243 = 6114365) B6114365
theorem B2716523 : Blo 1206420 2716523 := bstep (se 1 (by rfl) ⟨2037392, by rfl⟩ : syracuseStep 2716523 = 4074785) B4074785
theorem B2036623 : Blo 1206420 2036623 := bstep (se 1 (by rfl) ⟨1527467, by rfl⟩ : syracuseStep 2036623 = 3054935) B3054935
theorem B2716577 : Blo 1206420 2716577 := bstep (se 2 (by rfl) ⟨1018716, by rfl⟩ : syracuseStep 2716577 = 2037433) B2037433
theorem B17396855 : Blo 1206420 17396855 := bstep (se 1 (by rfl) ⟨13047641, by rfl⟩ : syracuseStep 17396855 = 26095283) B26095283
theorem B2716919 : Blo 1206420 2716919 := bstep (se 1 (by rfl) ⟨2037689, by rfl⟩ : syracuseStep 2716919 = 4075379) B4075379
theorem B19576079 : Blo 1206420 19576079 := bstep (se 1 (by rfl) ⟨14682059, by rfl⟩ : syracuseStep 19576079 = 29364119) B29364119
theorem B4584833 : Blo 1206420 4584833 := bstep (se 2 (by rfl) ⟨1719312, by rfl⟩ : syracuseStep 4584833 = 3438625) B3438625
theorem B1357231 : Blo 1206420 1357231 := bstep (se 1 (by rfl) ⟨1017923, by rfl⟩ : syracuseStep 1357231 = 2035847) B2035847
theorem B2037305 : Blo 1206420 2037305 := bstep (se 2 (by rfl) ⟨763989, by rfl⟩ : syracuseStep 2037305 = 1527979) B1527979
theorem B2291323 : Blo 1206420 2291323 := bstep (se 1 (by rfl) ⟨1718492, by rfl⟩ : syracuseStep 2291323 = 3436985) B3436985
theorem B9787027 : Blo 1206420 9787027 := bstep (se 1 (by rfl) ⟨7340270, by rfl⟩ : syracuseStep 9787027 = 14680541) B14680541
theorem B2291399 : Blo 1206420 2291399 := bstep (se 1 (by rfl) ⟨1718549, by rfl⟩ : syracuseStep 2291399 = 3437099) B3437099
theorem B7730909 : Blo 1206420 7730909 := bstep (se 3 (by rfl) ⟨1449545, by rfl⟩ : syracuseStep 7730909 = 2899091) B2899091
theorem B5158723 : Blo 1206420 5158723 := bstep (se 1 (by rfl) ⟨3869042, by rfl⟩ : syracuseStep 5158723 = 7738085) B7738085
theorem B3438409 : Blo 1206420 3438409 := bstep (se 2 (by rfl) ⟨1289403, by rfl⟩ : syracuseStep 3438409 = 2578807) B2578807
theorem B2717513 : Blo 1206420 2717513 := bstep (se 2 (by rfl) ⟨1019067, by rfl⟩ : syracuseStep 2717513 = 2038135) B2038135
theorem B1718111 : Blo 1206420 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B1357663 : Blo 1206420 1357663 := bstep (se 1 (by rfl) ⟨1018247, by rfl⟩ : syracuseStep 1357663 = 2036495) B2036495
theorem B7346015 : Blo 1206420 7346015 := bstep (se 1 (by rfl) ⟨5509511, by rfl⟩ : syracuseStep 7346015 = 11019023) B11019023
theorem B3438443 : Blo 1206420 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B12089249 : Blo 1206420 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B2578439 : Blo 1206420 2578439 := bstep (se 1 (by rfl) ⟨1933829, by rfl⟩ : syracuseStep 2578439 = 3867659) B3867659
theorem B50894905 : Blo 1206420 50894905 := bstep (se 2 (by rfl) ⟨19085589, by rfl⟩ : syracuseStep 50894905 = 38171179) B38171179
theorem B2291809 : Blo 1206420 2291809 := bstep (se 2 (by rfl) ⟨859428, by rfl⟩ : syracuseStep 2291809 = 1718857) B1718857
theorem B1358023 : Blo 1206420 1358023 := bstep (se 1 (by rfl) ⟨1018517, by rfl⟩ : syracuseStep 1358023 = 2037035) B2037035
theorem B2038007 : Blo 1206420 2038007 := bstep (se 1 (by rfl) ⟨1528505, by rfl⟩ : syracuseStep 2038007 = 3057011) B3057011
theorem B2292151 : Blo 1206420 2292151 := bstep (se 1 (by rfl) ⟨1719113, by rfl⟩ : syracuseStep 2292151 = 3438227) B3438227
theorem B3865097 : Blo 1206420 3865097 := bstep (se 2 (by rfl) ⟨1449411, by rfl⟩ : syracuseStep 3865097 = 2898823) B2898823
theorem B4586017 : Blo 1206420 4586017 := bstep (se 2 (by rfl) ⟨1719756, by rfl⟩ : syracuseStep 4586017 = 3439513) B3439513
theorem B2038351 : Blo 1206420 2038351 := bstep (se 1 (by rfl) ⟨1528763, by rfl⟩ : syracuseStep 2038351 = 3057527) B3057527
theorem B2292553 : Blo 1206420 2292553 := bstep (se 2 (by rfl) ⟨859707, by rfl⟩ : syracuseStep 2292553 = 1719415) B1719415
theorem B10312595 : Blo 1206420 10312595 := bstep (se 1 (by rfl) ⟨7734446, by rfl⟩ : syracuseStep 10312595 = 15468893) B15468893
theorem B59554739 : Blo 1206420 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B3054611 : Blo 1206420 3054611 := bstep (se 1 (by rfl) ⟨2290958, by rfl⟩ : syracuseStep 3054611 = 4581917) B4581917
theorem B1358887 : Blo 1206420 1358887 := bstep (se 1 (by rfl) ⟨1019165, by rfl⟩ : syracuseStep 1358887 = 2038331) B2038331
theorem B2579627 : Blo 1206420 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B1809839 : Blo 1206420 1809839 := bstep (se 1 (by rfl) ⟨1357379, by rfl⟩ : syracuseStep 1809839 = 2714759) B2714759
theorem B3055067 : Blo 1206420 3055067 := bstep (se 1 (by rfl) ⟨2291300, by rfl⟩ : syracuseStep 3055067 = 4582601) B4582601
theorem B1809929 : Blo 1206420 1809929 := bstep (se 2 (by rfl) ⟨678723, by rfl⟩ : syracuseStep 1809929 = 1357447) B1357447
theorem B1809959 : Blo 1206420 1809959 := bstep (se 1 (by rfl) ⟨1357469, by rfl⟩ : syracuseStep 1809959 = 2714939) B2714939
theorem B1810043 : Blo 1206420 1810043 := bstep (se 1 (by rfl) ⟨1357532, by rfl⟩ : syracuseStep 1810043 = 2715065) B2715065
theorem B44064395 : Blo 1206420 44064395 := bstep (se 1 (by rfl) ⟨33048296, by rfl⟩ : syracuseStep 44064395 = 66096593) B66096593
theorem B1810169 : Blo 1206420 1810169 := bstep (se 2 (by rfl) ⟨678813, by rfl⟩ : syracuseStep 1810169 = 1357627) B1357627
theorem B1810271 : Blo 1206420 1810271 := bstep (se 1 (by rfl) ⟨1357703, by rfl⟩ : syracuseStep 1810271 = 2715407) B2715407
theorem B1810283 : Blo 1206420 1810283 := bstep (se 1 (by rfl) ⟨1357712, by rfl⟩ : syracuseStep 1810283 = 2715425) B2715425
theorem B1449911 : Blo 1206420 1449911 := bstep (se 1 (by rfl) ⟨1087433, by rfl⟩ : syracuseStep 1449911 = 2174867) B2174867
theorem B22020173 : Blo 1206420 22020173 := bstep (se 3 (by rfl) ⟨4128782, by rfl⟩ : syracuseStep 22020173 = 8257565) B8257565
theorem B3055745 : Blo 1206420 3055745 := bstep (se 2 (by rfl) ⟨1145904, by rfl⟩ : syracuseStep 3055745 = 2291809) B2291809
theorem B1810697 : Blo 1206420 1810697 := bstep (se 2 (by rfl) ⟨679011, by rfl⟩ : syracuseStep 1810697 = 1358023) B1358023
theorem B5505353 : Blo 1206420 5505353 := bstep (se 2 (by rfl) ⟨2064507, by rfl⟩ : syracuseStep 5505353 = 4129015) B4129015
theorem B2752859 : Blo 1206420 2752859 := bstep (se 1 (by rfl) ⟨2064644, by rfl⟩ : syracuseStep 2752859 = 4129289) B4129289
theorem B1810799 : Blo 1206420 1810799 := bstep (se 1 (by rfl) ⟨1358099, by rfl⟩ : syracuseStep 1810799 = 2716199) B2716199
theorem B3056039 : Blo 1206420 3056039 := bstep (se 1 (by rfl) ⟨2292029, by rfl⟩ : syracuseStep 3056039 = 4584059) B4584059
theorem B3097007 : Blo 1206420 3097007 := bstep (se 1 (by rfl) ⟨2322755, by rfl⟩ : syracuseStep 3097007 = 4645511) B4645511
theorem B1811015 : Blo 1206420 1811015 := bstep (se 1 (by rfl) ⟨1358261, by rfl⟩ : syracuseStep 1811015 = 2716523) B2716523
theorem B3056201 : Blo 1206420 3056201 := bstep (se 2 (by rfl) ⟨1146075, by rfl⟩ : syracuseStep 3056201 = 2292151) B2292151
theorem B23511653 : Blo 1206420 23511653 := bstep (se 4 (by rfl) ⟨2204217, by rfl⟩ : syracuseStep 23511653 = 4408435) B4408435
theorem B1811051 : Blo 1206420 1811051 := bstep (se 1 (by rfl) ⟨1358288, by rfl⟩ : syracuseStep 1811051 = 2716577) B2716577
theorem B1811279 : Blo 1206420 1811279 := bstep (se 1 (by rfl) ⟨1358459, by rfl⟩ : syracuseStep 1811279 = 2716919) B2716919
theorem B13050719 : Blo 1206420 13050719 := bstep (se 1 (by rfl) ⟨9788039, by rfl⟩ : syracuseStep 13050719 = 19576079) B19576079
theorem B3056555 : Blo 1206420 3056555 := bstep (se 1 (by rfl) ⟨2292416, by rfl⟩ : syracuseStep 3056555 = 4584833) B4584833
theorem B8700965 : Blo 1206420 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B3056737 : Blo 1206420 3056737 := bstep (se 2 (by rfl) ⟨1146276, by rfl⟩ : syracuseStep 3056737 = 2292553) B2292553
theorem B5153939 : Blo 1206420 5153939 := bstep (se 1 (by rfl) ⟨3865454, by rfl⟩ : syracuseStep 5153939 = 7730909) B7730909
theorem B1811675 : Blo 1206420 1811675 := bstep (se 1 (by rfl) ⟨1358756, by rfl⟩ : syracuseStep 1811675 = 2717513) B2717513
theorem B14681321 : Blo 1206420 14681321 := bstep (se 2 (by rfl) ⟨5505495, by rfl⟩ : syracuseStep 14681321 = 11010991) B11010991
theorem B10314985 : Blo 1206420 10314985 := bstep (se 2 (by rfl) ⟨3868119, by rfl⟩ : syracuseStep 10314985 = 7736239) B7736239
theorem B1631497 : Blo 1206420 1631497 := bstep (se 2 (by rfl) ⟨611811, by rfl⟩ : syracuseStep 1631497 = 1223623) B1223623
theorem B1811849 : Blo 1206420 1811849 := bstep (se 2 (by rfl) ⟨679443, by rfl⟩ : syracuseStep 1811849 = 1358887) B1358887
theorem B10307195 : Blo 1206420 10307195 := bstep (se 1 (by rfl) ⟨7730396, by rfl⟩ : syracuseStep 10307195 = 15460793) B15460793
theorem B6875063 : Blo 1206420 6875063 := bstep (se 1 (by rfl) ⟨5156297, by rfl⟩ : syracuseStep 6875063 = 10312595) B10312595
theorem B6113231 : Blo 1206420 6113231 := bstep (se 1 (by rfl) ⟨4584923, by rfl⟩ : syracuseStep 6113231 = 9169847) B9169847
theorem B200869895 : Blo 1206420 200869895 := bstep (se 1 (by rfl) ⟨150652421, by rfl⟩ : syracuseStep 200869895 = 301304843) B301304843
theorem B1632361 : Blo 1206420 1632361 := bstep (se 2 (by rfl) ⟨612135, by rfl⟩ : syracuseStep 1632361 = 1224271) B1224271
theorem B4581629 : Blo 1206420 4581629 := bstep (se 3 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 4581629 = 1718111) B1718111
theorem B1206559 : Blo 1206420 1206559 := bstep (se 1 (by rfl) ⟨904919, by rfl⟩ : syracuseStep 1206559 = 1809839) B1809839
theorem B1206619 : Blo 1206420 1206619 := bstep (se 1 (by rfl) ⟨904964, by rfl⟩ : syracuseStep 1206619 = 1809929) B1809929
theorem B1206639 : Blo 1206420 1206639 := bstep (se 1 (by rfl) ⟨904979, by rfl⟩ : syracuseStep 1206639 = 1809959) B1809959
theorem B1206695 : Blo 1206420 1206695 := bstep (se 1 (by rfl) ⟨905021, by rfl⟩ : syracuseStep 1206695 = 1810043) B1810043
theorem B13044179 : Blo 1206420 13044179 := bstep (se 1 (by rfl) ⟨9783134, by rfl⟩ : syracuseStep 13044179 = 19566269) B19566269
theorem B1206779 : Blo 1206420 1206779 := bstep (se 1 (by rfl) ⟨905084, by rfl⟩ : syracuseStep 1206779 = 1810169) B1810169
theorem B1206847 : Blo 1206420 1206847 := bstep (se 1 (by rfl) ⟨905135, by rfl⟩ : syracuseStep 1206847 = 1810271) B1810271
theorem B1206855 : Blo 1206420 1206855 := bstep (se 1 (by rfl) ⟨905141, by rfl⟩ : syracuseStep 1206855 = 1810283) B1810283
theorem B6875837 : Blo 1206420 6875837 := bstep (se 3 (by rfl) ⟨1289219, by rfl⟩ : syracuseStep 6875837 = 2578439) B2578439
theorem B1207007 : Blo 1206420 1207007 := bstep (se 1 (by rfl) ⟨905255, by rfl⟩ : syracuseStep 1207007 = 1810511) B1810511
theorem B7736087 : Blo 1206420 7736087 := bstep (se 1 (by rfl) ⟨5802065, by rfl⟩ : syracuseStep 7736087 = 11604131) B11604131
theorem B1207087 : Blo 1206420 1207087 := bstep (se 1 (by rfl) ⟨905315, by rfl⟩ : syracuseStep 1207087 = 1810631) B1810631
theorem B1207195 : Blo 1206420 1207195 := bstep (se 1 (by rfl) ⟨905396, by rfl⟩ : syracuseStep 1207195 = 1810793) B1810793
theorem B6114203 : Blo 1206420 6114203 := bstep (se 1 (by rfl) ⟨4585652, by rfl⟩ : syracuseStep 6114203 = 9171305) B9171305
theorem B1207247 : Blo 1206420 1207247 := bstep (se 1 (by rfl) ⟨905435, by rfl⟩ : syracuseStep 1207247 = 1810871) B1810871
theorem B1207271 : Blo 1206420 1207271 := bstep (se 1 (by rfl) ⟨905453, by rfl⟩ : syracuseStep 1207271 = 1810907) B1810907
theorem B2714615 : Blo 1206420 2714615 := bstep (se 1 (by rfl) ⟨2035961, by rfl⟩ : syracuseStep 2714615 = 4071923) B4071923
theorem B17206337 : Blo 1206420 17206337 := bstep (se 2 (by rfl) ⟨6452376, by rfl⟩ : syracuseStep 17206337 = 12904753) B12904753
theorem B3435709 : Blo 1206420 3435709 := bstep (se 3 (by rfl) ⟨644195, by rfl⟩ : syracuseStep 3435709 = 1288391) B1288391
theorem B1207583 : Blo 1206420 1207583 := bstep (se 1 (by rfl) ⟨905687, by rfl⟩ : syracuseStep 1207583 = 1811375) B1811375
theorem B1207643 : Blo 1206420 1207643 := bstep (se 1 (by rfl) ⟨905732, by rfl⟩ : syracuseStep 1207643 = 1811465) B1811465
theorem B2714975 : Blo 1206420 2714975 := bstep (se 1 (by rfl) ⟨2036231, by rfl⟩ : syracuseStep 2714975 = 4072463) B4072463
theorem B1207663 : Blo 1206420 1207663 := bstep (se 1 (by rfl) ⟨905747, by rfl⟩ : syracuseStep 1207663 = 1811495) B1811495
theorem B6114689 : Blo 1206420 6114689 := bstep (se 2 (by rfl) ⟨2293008, by rfl⟩ : syracuseStep 6114689 = 4586017) B4586017
theorem B1207719 : Blo 1206420 1207719 := bstep (se 1 (by rfl) ⟨905789, by rfl⟩ : syracuseStep 1207719 = 1811579) B1811579
theorem B28241369 : Blo 1206420 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B4075001 : Blo 1206420 4075001 := bstep (se 2 (by rfl) ⟨1528125, by rfl⟩ : syracuseStep 4075001 = 3056251) B3056251
theorem B1207803 : Blo 1206420 1207803 := bstep (se 1 (by rfl) ⟨905852, by rfl⟩ : syracuseStep 1207803 = 1811705) B1811705
theorem B1207871 : Blo 1206420 1207871 := bstep (se 1 (by rfl) ⟨905903, by rfl⟩ : syracuseStep 1207871 = 1811807) B1811807
theorem B1207879 : Blo 1206420 1207879 := bstep (se 1 (by rfl) ⟨905909, by rfl⟩ : syracuseStep 1207879 = 1811819) B1811819
theorem B1289903 : Blo 1206420 1289903 := bstep (se 1 (by rfl) ⟨967427, by rfl⟩ : syracuseStep 1289903 = 1934855) B1934855
theorem B2715371 : Blo 1206420 2715371 := bstep (se 1 (by rfl) ⟨2036528, by rfl⟩ : syracuseStep 2715371 = 4073057) B4073057
theorem B4075271 : Blo 1206420 4075271 := bstep (se 1 (by rfl) ⟨3056453, by rfl⟩ : syracuseStep 4075271 = 6112907) B6112907
theorem B1527599 : Blo 1206420 1527599 := bstep (se 1 (by rfl) ⟨1145699, by rfl⟩ : syracuseStep 1527599 = 2291399) B2291399
theorem B4075325 : Blo 1206420 4075325 := bstep (se 3 (by rfl) ⟨764123, by rfl⟩ : syracuseStep 4075325 = 1528247) B1528247
theorem B2715497 : Blo 1206420 2715497 := bstep (se 2 (by rfl) ⟨1018311, by rfl⟩ : syracuseStep 2715497 = 2036623) B2036623
theorem B19582877 : Blo 1206420 19582877 := bstep (se 3 (by rfl) ⟨3671789, by rfl⟩ : syracuseStep 19582877 = 7343579) B7343579
theorem B2576731 : Blo 1206420 2576731 := bstep (se 1 (by rfl) ⟨1932548, by rfl⟩ : syracuseStep 2576731 = 3865097) B3865097
theorem B6877547 : Blo 1206420 6877547 := bstep (se 1 (by rfl) ⟨5158160, by rfl⟩ : syracuseStep 6877547 = 10316321) B10316321
theorem B4895201 : Blo 1206420 4895201 := bstep (se 2 (by rfl) ⟨1835700, by rfl⟩ : syracuseStep 4895201 = 3671401) B3671401
theorem B59535971 : Blo 1206420 59535971 := bstep (se 1 (by rfl) ⟨44651978, by rfl⟩ : syracuseStep 59535971 = 89303957) B89303957
theorem B39703159 : Blo 1206420 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B2290351 : Blo 1206420 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B2036407 : Blo 1206420 2036407 := bstep (se 1 (by rfl) ⟨1527305, by rfl⟩ : syracuseStep 2036407 = 3054611) B3054611
theorem B2716343 : Blo 1206420 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B2290511 : Blo 1206420 2290511 := bstep (se 1 (by rfl) ⟨1717883, by rfl⟩ : syracuseStep 2290511 = 3435767) B3435767
theorem B9171791 : Blo 1206420 9171791 := bstep (se 1 (by rfl) ⟨6878843, by rfl⟩ : syracuseStep 9171791 = 13757687) B13757687
theorem B2716559 : Blo 1206420 2716559 := bstep (se 1 (by rfl) ⟨2037419, by rfl⟩ : syracuseStep 2716559 = 4074839) B4074839
theorem B2036711 : Blo 1206420 2036711 := bstep (se 1 (by rfl) ⟨1527533, by rfl⟩ : syracuseStep 2036711 = 3055067) B3055067
theorem B6878297 : Blo 1206420 6878297 := bstep (se 2 (by rfl) ⟨2579361, by rfl⟩ : syracuseStep 6878297 = 5158723) B5158723
theorem B4584545 : Blo 1206420 4584545 := bstep (se 2 (by rfl) ⟨1719204, by rfl⟩ : syracuseStep 4584545 = 3438409) B3438409
theorem B14677139 : Blo 1206420 14677139 := bstep (se 1 (by rfl) ⟨11007854, by rfl⟩ : syracuseStep 14677139 = 22015709) B22015709
theorem B5657951 : Blo 1206420 5657951 := bstep (se 1 (by rfl) ⟨4243463, by rfl⟩ : syracuseStep 5657951 = 8486927) B8486927
theorem B67859873 : Blo 1206420 67859873 := bstep (se 2 (by rfl) ⟨25447452, by rfl⟩ : syracuseStep 67859873 = 50894905) B50894905
theorem B26818087 : Blo 1206420 26818087 := bstep (se 1 (by rfl) ⟨20113565, by rfl⟩ : syracuseStep 26818087 = 40227131) B40227131
theorem B1357375 : Blo 1206420 1357375 := bstep (se 1 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 1357375 = 2036063) B2036063
theorem B2717279 : Blo 1206420 2717279 := bstep (se 1 (by rfl) ⟨2037959, by rfl⟩ : syracuseStep 2717279 = 4075919) B4075919
theorem B2578081 : Blo 1206420 2578081 := bstep (se 2 (by rfl) ⟨966780, by rfl⟩ : syracuseStep 2578081 = 1933561) B1933561
theorem B6108857 : Blo 1206420 6108857 := bstep (se 2 (by rfl) ⟨2290821, by rfl⟩ : syracuseStep 6108857 = 4581643) B4581643
theorem B6879005 : Blo 1206420 6879005 := bstep (se 3 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 6879005 = 2579627) B2579627
theorem B2717495 : Blo 1206420 2717495 := bstep (se 1 (by rfl) ⟨2038121, by rfl⟩ : syracuseStep 2717495 = 4076243) B4076243
theorem B11597903 : Blo 1206420 11597903 := bstep (se 1 (by rfl) ⟨8698427, by rfl⟩ : syracuseStep 11597903 = 17396855) B17396855
theorem B2037865 : Blo 1206420 2037865 := bstep (se 2 (by rfl) ⟨764199, by rfl⟩ : syracuseStep 2037865 = 1528399) B1528399
theorem B2717801 : Blo 1206420 2717801 := bstep (se 2 (by rfl) ⟨1019175, by rfl⟩ : syracuseStep 2717801 = 2038351) B2038351
theorem B10311947 : Blo 1206420 10311947 := bstep (se 1 (by rfl) ⟨7733960, by rfl⟩ : syracuseStep 10311947 = 15467921) B15467921
theorem B7444759 : Blo 1206420 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B1358203 : Blo 1206420 1358203 := bstep (se 1 (by rfl) ⟨1018652, by rfl⟩ : syracuseStep 1358203 = 2037305) B2037305
theorem B11606591 : Blo 1206420 11606591 := bstep (se 1 (by rfl) ⟨8704943, by rfl⟩ : syracuseStep 11606591 = 17409887) B17409887
theorem B4897343 : Blo 1206420 4897343 := bstep (se 1 (by rfl) ⟨3673007, by rfl⟩ : syracuseStep 4897343 = 7346015) B7346015
theorem B2292295 : Blo 1206420 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B8059499 : Blo 1206420 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B1358671 : Blo 1206420 1358671 := bstep (se 1 (by rfl) ⟨1019003, by rfl⟩ : syracuseStep 1358671 = 2038007) B2038007
theorem B3054631 : Blo 1206420 3054631 := bstep (se 1 (by rfl) ⟨2290973, by rfl⟩ : syracuseStep 3054631 = 4581947) B4581947
theorem B2612443 : Blo 1206420 2612443 := bstep (se 1 (by rfl) ⟨1959332, by rfl⟩ : syracuseStep 2612443 = 3918665) B3918665
theorem B1809641 : Blo 1206420 1809641 := bstep (se 2 (by rfl) ⟨678615, by rfl⟩ : syracuseStep 1809641 = 1357231) B1357231
theorem B1809695 : Blo 1206420 1809695 := bstep (se 1 (by rfl) ⟨1357271, by rfl⟩ : syracuseStep 1809695 = 2714543) B2714543
theorem B1809863 : Blo 1206420 1809863 := bstep (se 1 (by rfl) ⟨1357397, by rfl⟩ : syracuseStep 1809863 = 2714795) B2714795
theorem B3055097 : Blo 1206420 3055097 := bstep (se 2 (by rfl) ⟨1145661, by rfl⟩ : syracuseStep 3055097 = 2291323) B2291323
theorem B13049369 : Blo 1206420 13049369 := bstep (se 2 (by rfl) ⟨4893513, by rfl⟩ : syracuseStep 13049369 = 9787027) B9787027
theorem B6110801 : Blo 1206420 6110801 := bstep (se 2 (by rfl) ⟨2291550, by rfl⟩ : syracuseStep 6110801 = 4583101) B4583101
theorem B29376263 : Blo 1206420 29376263 := bstep (se 1 (by rfl) ⟨22032197, by rfl⟩ : syracuseStep 29376263 = 44064395) B44064395
theorem B1810217 : Blo 1206420 1810217 := bstep (se 2 (by rfl) ⟨678831, by rfl⟩ : syracuseStep 1810217 = 1357663) B1357663
theorem B1810223 : Blo 1206420 1810223 := bstep (se 1 (by rfl) ⟨1357667, by rfl⟩ : syracuseStep 1810223 = 2715335) B2715335
theorem B3866429 : Blo 1206420 3866429 := bstep (se 3 (by rfl) ⟨724955, by rfl⟩ : syracuseStep 3866429 = 1449911) B1449911
theorem B14680115 : Blo 1206420 14680115 := bstep (se 1 (by rfl) ⟨11010086, by rfl⟩ : syracuseStep 14680115 = 22020173) B22020173
theorem B3670235 : Blo 1206420 3670235 := bstep (se 1 (by rfl) ⟨2752676, by rfl⟩ : syracuseStep 3670235 = 5505353) B5505353
theorem B1835239 : Blo 1206420 1835239 := bstep (se 1 (by rfl) ⟨1376429, by rfl⟩ : syracuseStep 1835239 = 2752859) B2752859
theorem B2064671 : Blo 1206420 2064671 := bstep (se 1 (by rfl) ⟨1548503, by rfl⟩ : syracuseStep 2064671 = 3097007) B3097007
theorem B39690647 : Blo 1206420 39690647 := bstep (se 1 (by rfl) ⟨29767985, by rfl⟩ : syracuseStep 39690647 = 59535971) B59535971
theorem B1810895 : Blo 1206420 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B1810937 : Blo 1206420 1810937 := bstep (se 2 (by rfl) ⟨679101, by rfl⟩ : syracuseStep 1810937 = 1358203) B1358203
theorem B8700479 : Blo 1206420 8700479 := bstep (se 1 (by rfl) ⟨6525359, by rfl⟩ : syracuseStep 8700479 = 13050719) B13050719
theorem B1811039 : Blo 1206420 1811039 := bstep (se 1 (by rfl) ⟨1358279, by rfl⟩ : syracuseStep 1811039 = 2716559) B2716559
theorem B5800643 : Blo 1206420 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B3056363 : Blo 1206420 3056363 := bstep (se 1 (by rfl) ⟨2292272, by rfl⟩ : syracuseStep 3056363 = 4584545) B4584545
theorem B3056393 : Blo 1206420 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B52937545 : Blo 1206420 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B1811519 : Blo 1206420 1811519 := bstep (se 1 (by rfl) ⟨1358639, by rfl⟩ : syracuseStep 1811519 = 2717279) B2717279
theorem B1811561 : Blo 1206420 1811561 := bstep (se 2 (by rfl) ⟨679335, by rfl⟩ : syracuseStep 1811561 = 1358671) B1358671
theorem B4072571 : Blo 1206420 4072571 := bstep (se 1 (by rfl) ⟨3054428, by rfl⟩ : syracuseStep 4072571 = 6108857) B6108857
theorem B1811663 : Blo 1206420 1811663 := bstep (se 1 (by rfl) ⟨1358747, by rfl⟩ : syracuseStep 1811663 = 2717495) B2717495
theorem B34784477 : Blo 1206420 34784477 := bstep (se 3 (by rfl) ⟨6522089, by rfl⟩ : syracuseStep 34784477 = 13044179) B13044179
theorem B4072841 : Blo 1206420 4072841 := bstep (se 2 (by rfl) ⟨1527315, by rfl⟩ : syracuseStep 4072841 = 3054631) B3054631
theorem B1811867 : Blo 1206420 1811867 := bstep (se 1 (by rfl) ⟨1358900, by rfl⟩ : syracuseStep 1811867 = 2717801) B2717801
theorem B6874631 : Blo 1206420 6874631 := bstep (se 1 (by rfl) ⟨5155973, by rfl⟩ : syracuseStep 6874631 = 10311947) B10311947
theorem B4580945 : Blo 1206420 4580945 := bstep (se 2 (by rfl) ⟨1717854, by rfl⟩ : syracuseStep 4580945 = 3435709) B3435709
theorem B3483257 : Blo 1206420 3483257 := bstep (se 2 (by rfl) ⟨1306221, by rfl⟩ : syracuseStep 3483257 = 2612443) B2612443
theorem B11470891 : Blo 1206420 11470891 := bstep (se 1 (by rfl) ⟨8603168, by rfl⟩ : syracuseStep 11470891 = 17206337) B17206337
theorem B4073597 : Blo 1206420 4073597 := bstep (se 3 (by rfl) ⟨763799, by rfl⟩ : syracuseStep 4073597 = 1527599) B1527599
theorem B1206427 : Blo 1206420 1206427 := bstep (se 1 (by rfl) ⟨904820, by rfl⟩ : syracuseStep 1206427 = 1809641) B1809641
theorem B1206463 : Blo 1206420 1206463 := bstep (se 1 (by rfl) ⟨904847, by rfl⟩ : syracuseStep 1206463 = 1809695) B1809695
theorem B1206575 : Blo 1206420 1206575 := bstep (se 1 (by rfl) ⟨904931, by rfl⟩ : syracuseStep 1206575 = 1809863) B1809863
theorem B18827579 : Blo 1206420 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B4073867 : Blo 1206420 4073867 := bstep (se 1 (by rfl) ⟨3055400, by rfl⟩ : syracuseStep 4073867 = 6110801) B6110801
theorem B1206811 : Blo 1206420 1206811 := bstep (se 1 (by rfl) ⟨905108, by rfl⟩ : syracuseStep 1206811 = 1810217) B1810217
theorem B1206815 : Blo 1206420 1206815 := bstep (se 1 (by rfl) ⟨905111, by rfl⟩ : syracuseStep 1206815 = 1810223) B1810223
theorem B1207131 : Blo 1206420 1207131 := bstep (se 1 (by rfl) ⟨905348, by rfl⟩ : syracuseStep 1207131 = 1810697) B1810697
theorem B1207199 : Blo 1206420 1207199 := bstep (se 1 (by rfl) ⟨905399, by rfl⟩ : syracuseStep 1207199 = 1810799) B1810799
theorem B1207343 : Blo 1206420 1207343 := bstep (se 1 (by rfl) ⟨905507, by rfl⟩ : syracuseStep 1207343 = 1811015) B1811015
theorem B15674435 : Blo 1206420 15674435 := bstep (se 1 (by rfl) ⟨11755826, by rfl⟩ : syracuseStep 15674435 = 23511653) B23511653
theorem B1207367 : Blo 1206420 1207367 := bstep (se 1 (by rfl) ⟨905525, by rfl⟩ : syracuseStep 1207367 = 1811051) B1811051
theorem B3435641 : Blo 1206420 3435641 := bstep (se 2 (by rfl) ⟨1288365, by rfl⟩ : syracuseStep 3435641 = 2576731) B2576731
theorem B1527007 : Blo 1206420 1527007 := bstep (se 1 (by rfl) ⟨1145255, by rfl⟩ : syracuseStep 1527007 = 2290511) B2290511
theorem B1207519 : Blo 1206420 1207519 := bstep (se 1 (by rfl) ⟨905639, by rfl⟩ : syracuseStep 1207519 = 1811279) B1811279
theorem B6114527 : Blo 1206420 6114527 := bstep (se 1 (by rfl) ⟨4585895, by rfl⟩ : syracuseStep 6114527 = 9171791) B9171791
theorem B3435959 : Blo 1206420 3435959 := bstep (se 1 (by rfl) ⟨2576969, by rfl⟩ : syracuseStep 3435959 = 5153939) B5153939
theorem B9784759 : Blo 1206420 9784759 := bstep (se 1 (by rfl) ⟨7338569, by rfl⟩ : syracuseStep 9784759 = 14677139) B14677139
theorem B1207783 : Blo 1206420 1207783 := bstep (se 1 (by rfl) ⟨905837, by rfl⟩ : syracuseStep 1207783 = 1811675) B1811675
theorem B2715209 : Blo 1206420 2715209 := bstep (se 2 (by rfl) ⟨1018203, by rfl⟩ : syracuseStep 2715209 = 2036407) B2036407
theorem B1207899 : Blo 1206420 1207899 := bstep (se 1 (by rfl) ⟨905924, by rfl⟩ : syracuseStep 1207899 = 1811849) B1811849
theorem B45239915 : Blo 1206420 45239915 := bstep (se 1 (by rfl) ⟨33929936, by rfl⟩ : syracuseStep 45239915 = 67859873) B67859873
theorem B13053869 : Blo 1206420 13053869 := bstep (se 3 (by rfl) ⟨2447600, by rfl⟩ : syracuseStep 13053869 = 4895201) B4895201
theorem B4583375 : Blo 1206420 4583375 := bstep (se 1 (by rfl) ⟨3437531, by rfl⟩ : syracuseStep 4583375 = 6875063) B6875063
theorem B4075487 : Blo 1206420 4075487 := bstep (se 1 (by rfl) ⟨3056615, by rfl⟩ : syracuseStep 4075487 = 6113231) B6113231
theorem B4075649 : Blo 1206420 4075649 := bstep (se 2 (by rfl) ⟨1528368, by rfl⟩ : syracuseStep 4075649 = 3056737) B3056737
theorem B2175329 : Blo 1206420 2175329 := bstep (se 2 (by rfl) ⟨815748, by rfl⟩ : syracuseStep 2175329 = 1631497) B1631497
theorem B7737727 : Blo 1206420 7737727 := bstep (se 1 (by rfl) ⟨5803295, by rfl⟩ : syracuseStep 7737727 = 11606591) B11606591
theorem B3264895 : Blo 1206420 3264895 := bstep (se 1 (by rfl) ⟨2448671, by rfl⟩ : syracuseStep 3264895 = 4897343) B4897343
theorem B4583891 : Blo 1206420 4583891 := bstep (se 1 (by rfl) ⟨3437918, by rfl⟩ : syracuseStep 4583891 = 6875837) B6875837
theorem B5157391 : Blo 1206420 5157391 := bstep (se 1 (by rfl) ⟨3868043, by rfl⟩ : syracuseStep 5157391 = 7736087) B7736087
theorem B4076135 : Blo 1206420 4076135 := bstep (se 1 (by rfl) ⟨3057101, by rfl⟩ : syracuseStep 4076135 = 6114203) B6114203
theorem B3437441 : Blo 1206420 3437441 := bstep (se 2 (by rfl) ⟨1289040, by rfl⟩ : syracuseStep 3437441 = 2578081) B2578081
theorem B4076459 : Blo 1206420 4076459 := bstep (se 1 (by rfl) ⟨3057344, by rfl⟩ : syracuseStep 4076459 = 6114689) B6114689
theorem B2036731 : Blo 1206420 2036731 := bstep (se 1 (by rfl) ⟨1527548, by rfl⟩ : syracuseStep 2036731 = 3055097) B3055097
theorem B2716667 : Blo 1206420 2716667 := bstep (se 1 (by rfl) ⟨2037500, by rfl⟩ : syracuseStep 2716667 = 4075001) B4075001
theorem B2716847 : Blo 1206420 2716847 := bstep (se 1 (by rfl) ⟨2037635, by rfl⟩ : syracuseStep 2716847 = 4075271) B4075271
theorem B19584175 : Blo 1206420 19584175 := bstep (se 1 (by rfl) ⟨14688131, by rfl⟩ : syracuseStep 19584175 = 29376263) B29376263
theorem B2577619 : Blo 1206420 2577619 := bstep (se 1 (by rfl) ⟨1933214, by rfl⟩ : syracuseStep 2577619 = 3866429) B3866429
theorem B2716883 : Blo 1206420 2716883 := bstep (se 1 (by rfl) ⟨2037662, by rfl⟩ : syracuseStep 2716883 = 4075325) B4075325
theorem B13055251 : Blo 1206420 13055251 := bstep (se 1 (by rfl) ⟨9791438, by rfl⟩ : syracuseStep 13055251 = 19582877) B19582877
theorem B2037163 : Blo 1206420 2037163 := bstep (se 1 (by rfl) ⟨1527872, by rfl⟩ : syracuseStep 2037163 = 3055745) B3055745
theorem B2717153 : Blo 1206420 2717153 := bstep (se 2 (by rfl) ⟨1018932, by rfl⟩ : syracuseStep 2717153 = 2037865) B2037865
theorem B2176481 : Blo 1206420 2176481 := bstep (se 2 (by rfl) ⟨816180, by rfl⟩ : syracuseStep 2176481 = 1632361) B1632361
theorem B4585031 : Blo 1206420 4585031 := bstep (se 1 (by rfl) ⟨3438773, by rfl⟩ : syracuseStep 4585031 = 6877547) B6877547
theorem B2037359 : Blo 1206420 2037359 := bstep (se 1 (by rfl) ⟨1528019, by rfl⟩ : syracuseStep 2037359 = 3056039) B3056039
theorem B9926345 : Blo 1206420 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B2037467 : Blo 1206420 2037467 := bstep (se 1 (by rfl) ⟨1528100, by rfl⟩ : syracuseStep 2037467 = 3056201) B3056201
theorem B2037703 : Blo 1206420 2037703 := bstep (se 1 (by rfl) ⟨1528277, by rfl⟩ : syracuseStep 2037703 = 3056555) B3056555
theorem B1357807 : Blo 1206420 1357807 := bstep (se 1 (by rfl) ⟨1018355, by rfl⟩ : syracuseStep 1357807 = 2036711) B2036711
theorem B4585531 : Blo 1206420 4585531 := bstep (se 1 (by rfl) ⟨3439148, by rfl⟩ : syracuseStep 4585531 = 6878297) B6878297
theorem B9787547 : Blo 1206420 9787547 := bstep (se 1 (by rfl) ⟨7340660, by rfl⟩ : syracuseStep 9787547 = 14681321) B14681321
theorem B3053801 : Blo 1206420 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B15087869 : Blo 1206420 15087869 := bstep (se 3 (by rfl) ⟨2828975, by rfl⟩ : syracuseStep 15087869 = 5657951) B5657951
theorem B6871463 : Blo 1206420 6871463 := bstep (se 1 (by rfl) ⟨5153597, by rfl⟩ : syracuseStep 6871463 = 10307195) B10307195
theorem B4586003 : Blo 1206420 4586003 := bstep (se 1 (by rfl) ⟨3439502, by rfl⟩ : syracuseStep 4586003 = 6879005) B6879005
theorem B133913263 : Blo 1206420 133913263 := bstep (se 1 (by rfl) ⟨100434947, by rfl⟩ : syracuseStep 133913263 = 200869895) B200869895
theorem B7731935 : Blo 1206420 7731935 := bstep (se 1 (by rfl) ⟨5798951, by rfl⟩ : syracuseStep 7731935 = 11597903) B11597903
theorem B3054419 : Blo 1206420 3054419 := bstep (se 1 (by rfl) ⟨2290814, by rfl⟩ : syracuseStep 3054419 = 4581629) B4581629
theorem B13753313 : Blo 1206420 13753313 := bstep (se 2 (by rfl) ⟨5157492, by rfl⟩ : syracuseStep 13753313 = 10314985) B10314985
theorem B5372999 : Blo 1206420 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B3439741 : Blo 1206420 3439741 := bstep (se 3 (by rfl) ⟨644951, by rfl⟩ : syracuseStep 3439741 = 1289903) B1289903
theorem B1809743 : Blo 1206420 1809743 := bstep (se 1 (by rfl) ⟨1357307, by rfl⟩ : syracuseStep 1809743 = 2714615) B2714615
theorem B35757449 : Blo 1206420 35757449 := bstep (se 2 (by rfl) ⟨13409043, by rfl⟩ : syracuseStep 35757449 = 26818087) B26818087
theorem B1809833 : Blo 1206420 1809833 := bstep (se 2 (by rfl) ⟨678687, by rfl⟩ : syracuseStep 1809833 = 1357375) B1357375
theorem B1809983 : Blo 1206420 1809983 := bstep (se 1 (by rfl) ⟨1357487, by rfl⟩ : syracuseStep 1809983 = 2714975) B2714975
theorem B8699579 : Blo 1206420 8699579 := bstep (se 1 (by rfl) ⟨6524684, by rfl⟩ : syracuseStep 8699579 = 13049369) B13049369
theorem B1810247 : Blo 1206420 1810247 := bstep (se 1 (by rfl) ⟨1357685, by rfl⟩ : syracuseStep 1810247 = 2715371) B2715371
theorem B1810331 : Blo 1206420 1810331 := bstep (se 1 (by rfl) ⟨1357748, by rfl⟩ : syracuseStep 1810331 = 2715497) B2715497
theorem B15294521 : Blo 1206420 15294521 := bstep (se 2 (by rfl) ⟨5735445, by rfl⟩ : syracuseStep 15294521 = 11470891) B11470891
theorem B1376447 : Blo 1206420 1376447 := bstep (se 1 (by rfl) ⟨1032335, by rfl⟩ : syracuseStep 1376447 = 2064671) B2064671
theorem B1450219 : Blo 1206420 1450219 := bstep (se 1 (by rfl) ⟨1087664, by rfl⟩ : syracuseStep 1450219 = 2175329) B2175329
theorem B26460431 : Blo 1206420 26460431 := bstep (se 1 (by rfl) ⟨19845323, by rfl⟩ : syracuseStep 26460431 = 39690647) B39690647
theorem B3055927 : Blo 1206420 3055927 := bstep (se 1 (by rfl) ⟨2291945, by rfl⟩ : syracuseStep 3055927 = 4583891) B4583891
theorem B5800319 : Blo 1206420 5800319 := bstep (se 1 (by rfl) ⟨4350239, by rfl⟩ : syracuseStep 5800319 = 8700479) B8700479
theorem B3867095 : Blo 1206420 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B1811111 : Blo 1206420 1811111 := bstep (se 1 (by rfl) ⟨1358333, by rfl⟩ : syracuseStep 1811111 = 2716667) B2716667
theorem B1811231 : Blo 1206420 1811231 := bstep (se 1 (by rfl) ⟨1358423, by rfl⟩ : syracuseStep 1811231 = 2716847) B2716847
theorem B1811255 : Blo 1206420 1811255 := bstep (se 1 (by rfl) ⟨1358441, by rfl⟩ : syracuseStep 1811255 = 2716883) B2716883
theorem B1811435 : Blo 1206420 1811435 := bstep (se 1 (by rfl) ⟨1358576, by rfl⟩ : syracuseStep 1811435 = 2717153) B2717153
theorem B3056687 : Blo 1206420 3056687 := bstep (se 1 (by rfl) ⟨2292515, by rfl⟩ : syracuseStep 3056687 = 4585031) B4585031
theorem B70583393 : Blo 1206420 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B4580975 : Blo 1206420 4580975 := bstep (se 1 (by rfl) ⟨3435731, by rfl⟩ : syracuseStep 4580975 = 6871463) B6871463
theorem B3057335 : Blo 1206420 3057335 := bstep (se 1 (by rfl) ⟨2293001, by rfl⟩ : syracuseStep 3057335 = 4586003) B4586003
theorem B5154623 : Blo 1206420 5154623 := bstep (se 1 (by rfl) ⟨3865967, by rfl⟩ : syracuseStep 5154623 = 7731935) B7731935
theorem B26470253 : Blo 1206420 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B9168875 : Blo 1206420 9168875 := bstep (se 1 (by rfl) ⟨6876656, by rfl⟩ : syracuseStep 9168875 = 13753313) B13753313
theorem B3581999 : Blo 1206420 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B1206495 : Blo 1206420 1206495 := bstep (se 1 (by rfl) ⟨904871, by rfl⟩ : syracuseStep 1206495 = 1809743) B1809743
theorem B1206555 : Blo 1206420 1206555 := bstep (se 1 (by rfl) ⟨904916, by rfl⟩ : syracuseStep 1206555 = 1809833) B1809833
theorem B1206655 : Blo 1206420 1206655 := bstep (se 1 (by rfl) ⟨904991, by rfl⟩ : syracuseStep 1206655 = 1809983) B1809983
theorem B1206831 : Blo 1206420 1206831 := bstep (se 1 (by rfl) ⟨905123, by rfl⟩ : syracuseStep 1206831 = 1810247) B1810247
theorem B1206887 : Blo 1206420 1206887 := bstep (se 1 (by rfl) ⟨905165, by rfl⟩ : syracuseStep 1206887 = 1810331) B1810331
theorem B8702579 : Blo 1206420 8702579 := bstep (se 1 (by rfl) ⟨6526934, by rfl⟩ : syracuseStep 8702579 = 13053869) B13053869
theorem B6114041 : Blo 1206420 6114041 := bstep (se 2 (by rfl) ⟨2292765, by rfl⟩ : syracuseStep 6114041 = 4585531) B4585531
theorem B1207263 : Blo 1206420 1207263 := bstep (se 1 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 1207263 = 1810895) B1810895
theorem B1207291 : Blo 1206420 1207291 := bstep (se 1 (by rfl) ⟨905468, by rfl⟩ : syracuseStep 1207291 = 1810937) B1810937
theorem B1207359 : Blo 1206420 1207359 := bstep (se 1 (by rfl) ⟨905519, by rfl⟩ : syracuseStep 1207359 = 1811039) B1811039
theorem B10316969 : Blo 1206420 10316969 := bstep (se 2 (by rfl) ⟨3868863, by rfl⟩ : syracuseStep 10316969 = 7737727) B7737727
theorem B4353193 : Blo 1206420 4353193 := bstep (se 2 (by rfl) ⟨1632447, by rfl⟩ : syracuseStep 4353193 = 3264895) B3264895
theorem B6876521 : Blo 1206420 6876521 := bstep (se 2 (by rfl) ⟨2578695, by rfl⟩ : syracuseStep 6876521 = 5157391) B5157391
theorem B1207679 : Blo 1206420 1207679 := bstep (se 1 (by rfl) ⟨905759, by rfl⟩ : syracuseStep 1207679 = 1811519) B1811519
theorem B1207707 : Blo 1206420 1207707 := bstep (se 1 (by rfl) ⟨905780, by rfl⟩ : syracuseStep 1207707 = 1811561) B1811561
theorem B2715047 : Blo 1206420 2715047 := bstep (se 1 (by rfl) ⟨2036285, by rfl⟩ : syracuseStep 2715047 = 4072571) B4072571
theorem B1207775 : Blo 1206420 1207775 := bstep (se 1 (by rfl) ⟨905831, by rfl⟩ : syracuseStep 1207775 = 1811663) B1811663
theorem B2715227 : Blo 1206420 2715227 := bstep (se 1 (by rfl) ⟨2036420, by rfl⟩ : syracuseStep 2715227 = 4072841) B4072841
theorem B1207911 : Blo 1206420 1207911 := bstep (se 1 (by rfl) ⟨905933, by rfl⟩ : syracuseStep 1207911 = 1811867) B1811867
theorem B4583087 : Blo 1206420 4583087 := bstep (se 1 (by rfl) ⟨3437315, by rfl⟩ : syracuseStep 4583087 = 6874631) B6874631
theorem B9162557 : Blo 1206420 9162557 := bstep (se 3 (by rfl) ⟨1717979, by rfl⟩ : syracuseStep 9162557 = 3435959) B3435959
theorem B5803949 : Blo 1206420 5803949 := bstep (se 3 (by rfl) ⟨1088240, by rfl⟩ : syracuseStep 5803949 = 2176481) B2176481
theorem B2715641 : Blo 1206420 2715641 := bstep (se 2 (by rfl) ⟨1018365, by rfl⟩ : syracuseStep 2715641 = 2036731) B2036731
theorem B2715731 : Blo 1206420 2715731 := bstep (se 1 (by rfl) ⟨2036798, by rfl⟩ : syracuseStep 2715731 = 4073597) B4073597
theorem B6525031 : Blo 1206420 6525031 := bstep (se 1 (by rfl) ⟨4893773, by rfl⟩ : syracuseStep 6525031 = 9787547) B9787547
theorem B2035867 : Blo 1206420 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B26112233 : Blo 1206420 26112233 := bstep (se 2 (by rfl) ⟨9792087, by rfl⟩ : syracuseStep 26112233 = 19584175) B19584175
theorem B2715911 : Blo 1206420 2715911 := bstep (se 1 (by rfl) ⟨2036933, by rfl⟩ : syracuseStep 2715911 = 4073867) B4073867
theorem B3436825 : Blo 1206420 3436825 := bstep (se 2 (by rfl) ⟨1288809, by rfl⟩ : syracuseStep 3436825 = 2577619) B2577619
theorem B120639773 : Blo 1206420 120639773 := bstep (se 3 (by rfl) ⟨22619957, by rfl⟩ : syracuseStep 120639773 = 45239915) B45239915
theorem B2036009 : Blo 1206420 2036009 := bstep (se 2 (by rfl) ⟨763503, by rfl⟩ : syracuseStep 2036009 = 1527007) B1527007
theorem B2036279 : Blo 1206420 2036279 := bstep (se 1 (by rfl) ⟨1527209, by rfl⟩ : syracuseStep 2036279 = 3054419) B3054419
theorem B2716217 : Blo 1206420 2716217 := bstep (se 2 (by rfl) ⟨1018581, by rfl⟩ : syracuseStep 2716217 = 2037163) B2037163
theorem B13046345 : Blo 1206420 13046345 := bstep (se 2 (by rfl) ⟨4892379, by rfl⟩ : syracuseStep 13046345 = 9784759) B9784759
theorem B10449623 : Blo 1206420 10449623 := bstep (se 1 (by rfl) ⟨7837217, by rfl⟩ : syracuseStep 10449623 = 15674435) B15674435
theorem B2290427 : Blo 1206420 2290427 := bstep (se 1 (by rfl) ⟨1717820, by rfl⟩ : syracuseStep 2290427 = 3435641) B3435641
theorem B4076351 : Blo 1206420 4076351 := bstep (se 1 (by rfl) ⟨3057263, by rfl⟩ : syracuseStep 4076351 = 6114527) B6114527
theorem B2716937 : Blo 1206420 2716937 := bstep (se 2 (by rfl) ⟨1018851, by rfl⟩ : syracuseStep 2716937 = 2037703) B2037703
theorem B2716991 : Blo 1206420 2716991 := bstep (se 1 (by rfl) ⟨2037743, by rfl⟩ : syracuseStep 2716991 = 4075487) B4075487
theorem B9786743 : Blo 1206420 9786743 := bstep (se 1 (by rfl) ⟨7340057, by rfl⟩ : syracuseStep 9786743 = 14680115) B14680115
theorem B2717099 : Blo 1206420 2717099 := bstep (se 1 (by rfl) ⟨2037824, by rfl⟩ : syracuseStep 2717099 = 4075649) B4075649
theorem B2446823 : Blo 1206420 2446823 := bstep (se 1 (by rfl) ⟨1835117, by rfl⟩ : syracuseStep 2446823 = 3670235) B3670235
theorem B2446985 : Blo 1206420 2446985 := bstep (se 2 (by rfl) ⟨917619, by rfl⟩ : syracuseStep 2446985 = 1835239) B1835239
theorem B2717423 : Blo 1206420 2717423 := bstep (se 1 (by rfl) ⟨2038067, by rfl⟩ : syracuseStep 2717423 = 4076135) B4076135
theorem B2037575 : Blo 1206420 2037575 := bstep (se 1 (by rfl) ⟨1528181, by rfl⟩ : syracuseStep 2037575 = 3056363) B3056363
theorem B2037595 : Blo 1206420 2037595 := bstep (se 1 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 2037595 = 3056393) B3056393
theorem B2291627 : Blo 1206420 2291627 := bstep (se 1 (by rfl) ⟨1718720, by rfl⟩ : syracuseStep 2291627 = 3437441) B3437441
theorem B2717639 : Blo 1206420 2717639 := bstep (se 1 (by rfl) ⟨2038229, by rfl⟩ : syracuseStep 2717639 = 4076459) B4076459
theorem B23189651 : Blo 1206420 23189651 := bstep (se 1 (by rfl) ⟨17392238, by rfl⟩ : syracuseStep 23189651 = 34784477) B34784477
theorem B50206877 : Blo 1206420 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B178551017 : Blo 1206420 178551017 := bstep (se 2 (by rfl) ⟨66956631, by rfl⟩ : syracuseStep 178551017 = 133913263) B133913263
theorem B3053963 : Blo 1206420 3053963 := bstep (se 1 (by rfl) ⟨2290472, by rfl⟩ : syracuseStep 3053963 = 4580945) B4580945
theorem B1358239 : Blo 1206420 1358239 := bstep (se 1 (by rfl) ⟨1018679, by rfl⟩ : syracuseStep 1358239 = 2037359) B2037359
theorem B1358311 : Blo 1206420 1358311 := bstep (se 1 (by rfl) ⟨1018733, by rfl⟩ : syracuseStep 1358311 = 2037467) B2037467
theorem B4586321 : Blo 1206420 4586321 := bstep (se 2 (by rfl) ⟨1719870, by rfl⟩ : syracuseStep 4586321 = 3439741) B3439741
theorem B10058579 : Blo 1206420 10058579 := bstep (se 1 (by rfl) ⟨7543934, by rfl⟩ : syracuseStep 10058579 = 15087869) B15087869
theorem B9288685 : Blo 1206420 9288685 := bstep (se 3 (by rfl) ⟨1741628, by rfl⟩ : syracuseStep 9288685 = 3483257) B3483257
theorem B17407001 : Blo 1206420 17407001 := bstep (se 2 (by rfl) ⟨6527625, by rfl⟩ : syracuseStep 17407001 = 13055251) B13055251
theorem B23838299 : Blo 1206420 23838299 := bstep (se 1 (by rfl) ⟨17878724, by rfl⟩ : syracuseStep 23838299 = 35757449) B35757449
theorem B1810139 : Blo 1206420 1810139 := bstep (se 1 (by rfl) ⟨1357604, by rfl⟩ : syracuseStep 1810139 = 2715209) B2715209
theorem B5799719 : Blo 1206420 5799719 := bstep (se 1 (by rfl) ⟨4349789, by rfl⟩ : syracuseStep 5799719 = 8699579) B8699579
theorem B3055583 : Blo 1206420 3055583 := bstep (se 1 (by rfl) ⟨2291687, by rfl⟩ : syracuseStep 3055583 = 4583375) B4583375
theorem B1810409 : Blo 1206420 1810409 := bstep (se 2 (by rfl) ⟨678903, by rfl⟩ : syracuseStep 1810409 = 1357807) B1357807
theorem B1810487 : Blo 1206420 1810487 := bstep (se 1 (by rfl) ⟨1357865, by rfl⟩ : syracuseStep 1810487 = 2715731) B2715731
theorem B8700041 : Blo 1206420 8700041 := bstep (se 2 (by rfl) ⟨3262515, by rfl⟩ : syracuseStep 8700041 = 6525031) B6525031
theorem B17408155 : Blo 1206420 17408155 := bstep (se 1 (by rfl) ⟨13056116, by rfl⟩ : syracuseStep 17408155 = 26112233) B26112233
theorem B1810607 : Blo 1206420 1810607 := bstep (se 1 (by rfl) ⟨1357955, by rfl⟩ : syracuseStep 1810607 = 2715911) B2715911
theorem B3866879 : Blo 1206420 3866879 := bstep (se 1 (by rfl) ⟨2900159, by rfl⟩ : syracuseStep 3866879 = 5800319) B5800319
theorem B1933625 : Blo 1206420 1933625 := bstep (se 2 (by rfl) ⟨725109, by rfl⟩ : syracuseStep 1933625 = 1450219) B1450219
theorem B1810811 : Blo 1206420 1810811 := bstep (se 1 (by rfl) ⟨1358108, by rfl⟩ : syracuseStep 1810811 = 2716217) B2716217
theorem B3670525 : Blo 1206420 3670525 := bstep (se 3 (by rfl) ⟨688223, by rfl⟩ : syracuseStep 3670525 = 1376447) B1376447
theorem B1810985 : Blo 1206420 1810985 := bstep (se 2 (by rfl) ⟨679119, by rfl⟩ : syracuseStep 1810985 = 1358239) B1358239
theorem B1811081 : Blo 1206420 1811081 := bstep (se 2 (by rfl) ⟨679155, by rfl⟩ : syracuseStep 1811081 = 1358311) B1358311
theorem B47055595 : Blo 1206420 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B1811291 : Blo 1206420 1811291 := bstep (se 1 (by rfl) ⟨1358468, by rfl⟩ : syracuseStep 1811291 = 2716937) B2716937
theorem B1811327 : Blo 1206420 1811327 := bstep (se 1 (by rfl) ⟨1358495, by rfl⟩ : syracuseStep 1811327 = 2716991) B2716991
theorem B1811399 : Blo 1206420 1811399 := bstep (se 1 (by rfl) ⟨1358549, by rfl⟩ : syracuseStep 1811399 = 2717099) B2717099
theorem B1631215 : Blo 1206420 1631215 := bstep (se 1 (by rfl) ⟨1223411, by rfl⟩ : syracuseStep 1631215 = 2446823) B2446823
theorem B1631323 : Blo 1206420 1631323 := bstep (se 1 (by rfl) ⟨1223492, by rfl⟩ : syracuseStep 1631323 = 2446985) B2446985
theorem B1811615 : Blo 1206420 1811615 := bstep (se 1 (by rfl) ⟨1358711, by rfl⟩ : syracuseStep 1811615 = 2717423) B2717423
theorem B17646835 : Blo 1206420 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B1811759 : Blo 1206420 1811759 := bstep (se 1 (by rfl) ⟨1358819, by rfl⟩ : syracuseStep 1811759 = 2717639) B2717639
theorem B6112583 : Blo 1206420 6112583 := bstep (se 1 (by rfl) ⟨4584437, by rfl⟩ : syracuseStep 6112583 = 9168875) B9168875
theorem B15459767 : Blo 1206420 15459767 := bstep (se 1 (by rfl) ⟨11594825, by rfl⟩ : syracuseStep 15459767 = 23189651) B23189651
theorem B5801719 : Blo 1206420 5801719 := bstep (se 1 (by rfl) ⟨4351289, by rfl⟩ : syracuseStep 5801719 = 8702579) B8702579
theorem B3057547 : Blo 1206420 3057547 := bstep (se 1 (by rfl) ⟨2293160, by rfl⟩ : syracuseStep 3057547 = 4586321) B4586321
theorem B1206759 : Blo 1206420 1206759 := bstep (se 1 (by rfl) ⟨905069, by rfl⟩ : syracuseStep 1206759 = 1810139) B1810139
theorem B3869299 : Blo 1206420 3869299 := bstep (se 1 (by rfl) ⟨2901974, by rfl⟩ : syracuseStep 3869299 = 5803949) B5803949
theorem B1206939 : Blo 1206420 1206939 := bstep (se 1 (by rfl) ⟨905204, by rfl⟩ : syracuseStep 1206939 = 1810409) B1810409
theorem B17640287 : Blo 1206420 17640287 := bstep (se 1 (by rfl) ⟨13230215, by rfl⟩ : syracuseStep 17640287 = 26460431) B26460431
theorem B2714489 : Blo 1206420 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B4582433 : Blo 1206420 4582433 := bstep (se 2 (by rfl) ⟨1718412, by rfl⟩ : syracuseStep 4582433 = 3436825) B3436825
theorem B4074569 : Blo 1206420 4074569 := bstep (se 2 (by rfl) ⟨1527963, by rfl⟩ : syracuseStep 4074569 = 3055927) B3055927
theorem B1207407 : Blo 1206420 1207407 := bstep (se 1 (by rfl) ⟨905555, by rfl⟩ : syracuseStep 1207407 = 1811111) B1811111
theorem B6966415 : Blo 1206420 6966415 := bstep (se 1 (by rfl) ⟨5224811, by rfl⟩ : syracuseStep 6966415 = 10449623) B10449623
theorem B1526951 : Blo 1206420 1526951 := bstep (se 1 (by rfl) ⟨1145213, by rfl⟩ : syracuseStep 1526951 = 2290427) B2290427
theorem B1207487 : Blo 1206420 1207487 := bstep (se 1 (by rfl) ⟨905615, by rfl⟩ : syracuseStep 1207487 = 1811231) B1811231
theorem B1207503 : Blo 1206420 1207503 := bstep (se 1 (by rfl) ⟨905627, by rfl⟩ : syracuseStep 1207503 = 1811255) B1811255
theorem B1207623 : Blo 1206420 1207623 := bstep (se 1 (by rfl) ⟨905717, by rfl⟩ : syracuseStep 1207623 = 1811435) B1811435
theorem B6524495 : Blo 1206420 6524495 := bstep (se 1 (by rfl) ⟨4893371, by rfl⟩ : syracuseStep 6524495 = 9786743) B9786743
theorem B3436415 : Blo 1206420 3436415 := bstep (se 1 (by rfl) ⟨2577311, by rfl⟩ : syracuseStep 3436415 = 5154623) B5154623
theorem B1527751 : Blo 1206420 1527751 := bstep (se 1 (by rfl) ⟨1145813, by rfl⟩ : syracuseStep 1527751 = 2291627) B2291627
theorem B2387999 : Blo 1206420 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B119034011 : Blo 1206420 119034011 := bstep (se 1 (by rfl) ⟨89275508, by rfl⟩ : syracuseStep 119034011 = 178551017) B178551017
theorem B5804257 : Blo 1206420 5804257 := bstep (se 2 (by rfl) ⟨2176596, by rfl⟩ : syracuseStep 5804257 = 4353193) B4353193
theorem B2035975 : Blo 1206420 2035975 := bstep (se 1 (by rfl) ⟨1526981, by rfl⟩ : syracuseStep 2035975 = 3053963) B3053963
theorem B4076027 : Blo 1206420 4076027 := bstep (se 1 (by rfl) ⟨3057020, by rfl⟩ : syracuseStep 4076027 = 6114041) B6114041
theorem B6705719 : Blo 1206420 6705719 := bstep (se 1 (by rfl) ⟨5029289, by rfl⟩ : syracuseStep 6705719 = 10058579) B10058579
theorem B11604667 : Blo 1206420 11604667 := bstep (se 1 (by rfl) ⟨8703500, by rfl⟩ : syracuseStep 11604667 = 17407001) B17407001
theorem B6877979 : Blo 1206420 6877979 := bstep (se 1 (by rfl) ⟨5158484, by rfl⟩ : syracuseStep 6877979 = 10316969) B10316969
theorem B4584347 : Blo 1206420 4584347 := bstep (se 1 (by rfl) ⟨3438260, by rfl⟩ : syracuseStep 4584347 = 6876521) B6876521
theorem B2716793 : Blo 1206420 2716793 := bstep (se 2 (by rfl) ⟨1018797, by rfl⟩ : syracuseStep 2716793 = 2037595) B2037595
theorem B6108371 : Blo 1206420 6108371 := bstep (se 1 (by rfl) ⟨4581278, by rfl⟩ : syracuseStep 6108371 = 9162557) B9162557
theorem B2037055 : Blo 1206420 2037055 := bstep (se 1 (by rfl) ⟨1527791, by rfl⟩ : syracuseStep 2037055 = 3055583) B3055583
theorem B10196347 : Blo 1206420 10196347 := bstep (se 1 (by rfl) ⟨7647260, by rfl⟩ : syracuseStep 10196347 = 15294521) B15294521
theorem B80426515 : Blo 1206420 80426515 := bstep (se 1 (by rfl) ⟨60319886, by rfl⟩ : syracuseStep 80426515 = 120639773) B120639773
theorem B1357339 : Blo 1206420 1357339 := bstep (se 1 (by rfl) ⟨1018004, by rfl⟩ : syracuseStep 1357339 = 2036009) B2036009
theorem B2578063 : Blo 1206420 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B1357519 : Blo 1206420 1357519 := bstep (se 1 (by rfl) ⟨1018139, by rfl⟩ : syracuseStep 1357519 = 2036279) B2036279
theorem B8697563 : Blo 1206420 8697563 := bstep (se 1 (by rfl) ⟨6523172, by rfl⟩ : syracuseStep 8697563 = 13046345) B13046345
theorem B2717567 : Blo 1206420 2717567 := bstep (se 1 (by rfl) ⟨2038175, by rfl⟩ : syracuseStep 2717567 = 4076351) B4076351
theorem B2037791 : Blo 1206420 2037791 := bstep (se 1 (by rfl) ⟨1528343, by rfl⟩ : syracuseStep 2037791 = 3056687) B3056687
theorem B3053983 : Blo 1206420 3053983 := bstep (se 1 (by rfl) ⟨2290487, by rfl⟩ : syracuseStep 3053983 = 4580975) B4580975
theorem B2038223 : Blo 1206420 2038223 := bstep (se 1 (by rfl) ⟨1528667, by rfl⟩ : syracuseStep 2038223 = 3057335) B3057335
theorem B1358383 : Blo 1206420 1358383 := bstep (se 1 (by rfl) ⟨1018787, by rfl⟩ : syracuseStep 1358383 = 2037575) B2037575
theorem B12384913 : Blo 1206420 12384913 := bstep (se 2 (by rfl) ⟨4644342, by rfl⟩ : syracuseStep 12384913 = 9288685) B9288685
theorem B33471251 : Blo 1206420 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B15465917 : Blo 1206420 15465917 := bstep (se 3 (by rfl) ⟨2899859, by rfl⟩ : syracuseStep 15465917 = 5799719) B5799719
theorem B1810031 : Blo 1206420 1810031 := bstep (se 1 (by rfl) ⟨1357523, by rfl⟩ : syracuseStep 1810031 = 2715047) B2715047
theorem B1810151 : Blo 1206420 1810151 := bstep (se 1 (by rfl) ⟨1357613, by rfl⟩ : syracuseStep 1810151 = 2715227) B2715227
theorem B15892199 : Blo 1206420 15892199 := bstep (se 1 (by rfl) ⟨11919149, by rfl⟩ : syracuseStep 15892199 = 23838299) B23838299
theorem B3055391 : Blo 1206420 3055391 := bstep (se 1 (by rfl) ⟨2291543, by rfl⟩ : syracuseStep 3055391 = 4583087) B4583087
theorem B1810427 : Blo 1206420 1810427 := bstep (se 1 (by rfl) ⟨1357820, by rfl⟩ : syracuseStep 1810427 = 2715641) B2715641
theorem B5800027 : Blo 1206420 5800027 := bstep (se 1 (by rfl) ⟨4350020, by rfl⟩ : syracuseStep 5800027 = 8700041) B8700041
theorem B79356007 : Blo 1206420 79356007 := bstep (se 1 (by rfl) ⟨59517005, by rfl⟩ : syracuseStep 79356007 = 119034011) B119034011
theorem B4071869 : Blo 1206420 4071869 := bstep (se 3 (by rfl) ⟨763475, by rfl⟩ : syracuseStep 4071869 = 1526951) B1526951
theorem B4071977 : Blo 1206420 4071977 := bstep (se 2 (by rfl) ⟨1526991, by rfl⟩ : syracuseStep 4071977 = 3053983) B3053983
theorem B3056231 : Blo 1206420 3056231 := bstep (se 1 (by rfl) ⟨2292173, by rfl⟩ : syracuseStep 3056231 = 4584347) B4584347
theorem B1811177 : Blo 1206420 1811177 := bstep (se 2 (by rfl) ⟨679191, by rfl⟩ : syracuseStep 1811177 = 1358383) B1358383
theorem B1811195 : Blo 1206420 1811195 := bstep (se 1 (by rfl) ⟨1358396, by rfl⟩ : syracuseStep 1811195 = 2716793) B2716793
theorem B4072247 : Blo 1206420 4072247 := bstep (se 1 (by rfl) ⟨3054185, by rfl⟩ : syracuseStep 4072247 = 6108371) B6108371
theorem B10306511 : Blo 1206420 10306511 := bstep (se 1 (by rfl) ⟨7729883, by rfl⟩ : syracuseStep 10306511 = 15459767) B15459767
theorem B1811711 : Blo 1206420 1811711 := bstep (se 1 (by rfl) ⟨1358783, by rfl⟩ : syracuseStep 1811711 = 2717567) B2717567
theorem B23529113 : Blo 1206420 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B107235353 : Blo 1206420 107235353 := bstep (se 2 (by rfl) ⟨40213257, by rfl⟩ : syracuseStep 107235353 = 80426515) B80426515
theorem B7735625 : Blo 1206420 7735625 := bstep (se 2 (by rfl) ⟨2900859, by rfl⟩ : syracuseStep 7735625 = 5801719) B5801719
theorem B1206687 : Blo 1206420 1206687 := bstep (se 1 (by rfl) ⟨905015, by rfl⟩ : syracuseStep 1206687 = 1810031) B1810031
theorem B1206767 : Blo 1206420 1206767 := bstep (se 1 (by rfl) ⟨905075, by rfl⟩ : syracuseStep 1206767 = 1810151) B1810151
theorem B10594799 : Blo 1206420 10594799 := bstep (se 1 (by rfl) ⟨7946099, by rfl⟩ : syracuseStep 10594799 = 15892199) B15892199
theorem B1206951 : Blo 1206420 1206951 := bstep (se 1 (by rfl) ⟨905213, by rfl⟩ : syracuseStep 1206951 = 1810427) B1810427
theorem B1206991 : Blo 1206420 1206991 := bstep (se 1 (by rfl) ⟨905243, by rfl⟩ : syracuseStep 1206991 = 1810487) B1810487
theorem B6367997 : Blo 1206420 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B1207071 : Blo 1206420 1207071 := bstep (se 1 (by rfl) ⟨905303, by rfl⟩ : syracuseStep 1207071 = 1810607) B1810607
theorem B23210873 : Blo 1206420 23210873 := bstep (se 2 (by rfl) ⟨8704077, by rfl⟩ : syracuseStep 23210873 = 17408155) B17408155
theorem B1289083 : Blo 1206420 1289083 := bstep (se 1 (by rfl) ⟨966812, by rfl⟩ : syracuseStep 1289083 = 1933625) B1933625
theorem B1207207 : Blo 1206420 1207207 := bstep (se 1 (by rfl) ⟨905405, by rfl⟩ : syracuseStep 1207207 = 1810811) B1810811
theorem B2714633 : Blo 1206420 2714633 := bstep (se 2 (by rfl) ⟨1017987, by rfl⟩ : syracuseStep 2714633 = 2035975) B2035975
theorem B1207323 : Blo 1206420 1207323 := bstep (se 1 (by rfl) ⟨905492, by rfl⟩ : syracuseStep 1207323 = 1810985) B1810985
theorem B1207387 : Blo 1206420 1207387 := bstep (se 1 (by rfl) ⟨905540, by rfl⟩ : syracuseStep 1207387 = 1811081) B1811081
theorem B1207527 : Blo 1206420 1207527 := bstep (se 1 (by rfl) ⟨905645, by rfl⟩ : syracuseStep 1207527 = 1811291) B1811291
theorem B1207551 : Blo 1206420 1207551 := bstep (se 1 (by rfl) ⟨905663, by rfl⟩ : syracuseStep 1207551 = 1811327) B1811327
theorem B1207599 : Blo 1206420 1207599 := bstep (se 1 (by rfl) ⟨905699, by rfl⟩ : syracuseStep 1207599 = 1811399) B1811399
theorem B4894033 : Blo 1206420 4894033 := bstep (se 2 (by rfl) ⟨1835262, by rfl⟩ : syracuseStep 4894033 = 3670525) B3670525
theorem B37154213 : Blo 1206420 37154213 := bstep (se 4 (by rfl) ⟨3483207, by rfl⟩ : syracuseStep 37154213 = 6966415) B6966415
theorem B1207743 : Blo 1206420 1207743 := bstep (se 1 (by rfl) ⟨905807, by rfl⟩ : syracuseStep 1207743 = 1811615) B1811615
theorem B1207839 : Blo 1206420 1207839 := bstep (se 1 (by rfl) ⟨905879, by rfl⟩ : syracuseStep 1207839 = 1811759) B1811759
theorem B4075055 : Blo 1206420 4075055 := bstep (se 1 (by rfl) ⟨3056291, by rfl⟩ : syracuseStep 4075055 = 6112583) B6112583
theorem B2174953 : Blo 1206420 2174953 := bstep (se 2 (by rfl) ⟨815607, by rfl⟩ : syracuseStep 2174953 = 1631215) B1631215
theorem B2175097 : Blo 1206420 2175097 := bstep (se 2 (by rfl) ⟨815661, by rfl⟩ : syracuseStep 2175097 = 1631323) B1631323
theorem B2716073 : Blo 1206420 2716073 := bstep (se 2 (by rfl) ⟨1018527, by rfl⟩ : syracuseStep 2716073 = 2037055) B2037055
theorem B13595129 : Blo 1206420 13595129 := bstep (se 2 (by rfl) ⟨5098173, by rfl⟩ : syracuseStep 13595129 = 10196347) B10196347
theorem B11760191 : Blo 1206420 11760191 := bstep (se 1 (by rfl) ⟨8820143, by rfl⟩ : syracuseStep 11760191 = 17640287) B17640287
theorem B2716379 : Blo 1206420 2716379 := bstep (se 1 (by rfl) ⟨2037284, by rfl⟩ : syracuseStep 2716379 = 4074569) B4074569
theorem B3437417 : Blo 1206420 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B10310611 : Blo 1206420 10310611 := bstep (se 1 (by rfl) ⟨7732958, by rfl⟩ : syracuseStep 10310611 = 15465917) B15465917
theorem B4076729 : Blo 1206420 4076729 := bstep (se 2 (by rfl) ⟨1528773, by rfl⟩ : syracuseStep 4076729 = 3057547) B3057547
theorem B2036927 : Blo 1206420 2036927 := bstep (se 1 (by rfl) ⟨1527695, by rfl⟩ : syracuseStep 2036927 = 3055391) B3055391
theorem B2290943 : Blo 1206420 2290943 := bstep (se 1 (by rfl) ⟨1718207, by rfl⟩ : syracuseStep 2290943 = 3436415) B3436415
theorem B2037001 : Blo 1206420 2037001 := bstep (se 2 (by rfl) ⟨763875, by rfl⟩ : syracuseStep 2037001 = 1527751) B1527751
theorem B2577919 : Blo 1206420 2577919 := bstep (se 1 (by rfl) ⟨1933439, by rfl⟩ : syracuseStep 2577919 = 3866879) B3866879
theorem B7739009 : Blo 1206420 7739009 := bstep (se 2 (by rfl) ⟨2902128, by rfl⟩ : syracuseStep 7739009 = 5804257) B5804257
theorem B2717351 : Blo 1206420 2717351 := bstep (se 1 (by rfl) ⟨2038013, by rfl⟩ : syracuseStep 2717351 = 4076027) B4076027
theorem B4470479 : Blo 1206420 4470479 := bstep (se 1 (by rfl) ⟨3352859, by rfl⟩ : syracuseStep 4470479 = 6705719) B6705719
theorem B4585319 : Blo 1206420 4585319 := bstep (se 1 (by rfl) ⟨3438989, by rfl⟩ : syracuseStep 4585319 = 6877979) B6877979
theorem B5159065 : Blo 1206420 5159065 := bstep (se 2 (by rfl) ⟨1934649, by rfl⟩ : syracuseStep 5159065 = 3869299) B3869299
theorem B16513217 : Blo 1206420 16513217 := bstep (se 2 (by rfl) ⟨6192456, by rfl⟩ : syracuseStep 16513217 = 12384913) B12384913
theorem B15472889 : Blo 1206420 15472889 := bstep (se 2 (by rfl) ⟨5802333, by rfl⟩ : syracuseStep 15472889 = 11604667) B11604667
theorem B62740793 : Blo 1206420 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B5798375 : Blo 1206420 5798375 := bstep (se 1 (by rfl) ⟨4348781, by rfl⟩ : syracuseStep 5798375 = 8697563) B8697563
theorem B1358527 : Blo 1206420 1358527 := bstep (se 1 (by rfl) ⟨1018895, by rfl⟩ : syracuseStep 1358527 = 2037791) B2037791
theorem B1358815 : Blo 1206420 1358815 := bstep (se 1 (by rfl) ⟨1019111, by rfl⟩ : syracuseStep 1358815 = 2038223) B2038223
theorem B22314167 : Blo 1206420 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B1809659 : Blo 1206420 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B3054955 : Blo 1206420 3054955 := bstep (se 1 (by rfl) ⟨2291216, by rfl⟩ : syracuseStep 3054955 = 4582433) B4582433
theorem B1809785 : Blo 1206420 1809785 := bstep (se 2 (by rfl) ⟨678669, by rfl⟩ : syracuseStep 1809785 = 1357339) B1357339
theorem B1810025 : Blo 1206420 1810025 := bstep (se 2 (by rfl) ⟨678759, by rfl⟩ : syracuseStep 1810025 = 1357519) B1357519
theorem B4349663 : Blo 1206420 4349663 := bstep (se 1 (by rfl) ⟨3262247, by rfl⟩ : syracuseStep 4349663 = 6524495) B6524495
theorem B7733369 : Blo 1206420 7733369 := bstep (se 2 (by rfl) ⟨2900013, by rfl⟩ : syracuseStep 7733369 = 5800027) B5800027
theorem B2900129 : Blo 1206420 2900129 := bstep (se 2 (by rfl) ⟨1087548, by rfl⟩ : syracuseStep 2900129 = 2175097) B2175097
theorem B1810715 : Blo 1206420 1810715 := bstep (se 1 (by rfl) ⟨1358036, by rfl⟩ : syracuseStep 1810715 = 2716073) B2716073
theorem B7840127 : Blo 1206420 7840127 := bstep (se 1 (by rfl) ⟨5880095, by rfl⟩ : syracuseStep 7840127 = 11760191) B11760191
theorem B1810919 : Blo 1206420 1810919 := bstep (se 1 (by rfl) ⟨1358189, by rfl⟩ : syracuseStep 1810919 = 2716379) B2716379
theorem B423232037 : Blo 1206420 423232037 := bstep (se 4 (by rfl) ⟨39678003, by rfl⟩ : syracuseStep 423232037 = 79356007) B79356007
theorem B1811369 : Blo 1206420 1811369 := bstep (se 2 (by rfl) ⟨679263, by rfl⟩ : syracuseStep 1811369 = 1358527) B1358527
theorem B1811567 : Blo 1206420 1811567 := bstep (se 1 (by rfl) ⟨1358675, by rfl⟩ : syracuseStep 1811567 = 2717351) B2717351
theorem B3056879 : Blo 1206420 3056879 := bstep (se 1 (by rfl) ⟨2292659, by rfl⟩ : syracuseStep 3056879 = 4585319) B4585319
theorem B13747481 : Blo 1206420 13747481 := bstep (se 2 (by rfl) ⟨5155305, by rfl⟩ : syracuseStep 13747481 = 10310611) B10310611
theorem B1811753 : Blo 1206420 1811753 := bstep (se 2 (by rfl) ⟨679407, by rfl⟩ : syracuseStep 1811753 = 1358815) B1358815
theorem B10315259 : Blo 1206420 10315259 := bstep (se 1 (by rfl) ⟨7736444, by rfl⟩ : syracuseStep 10315259 = 15472889) B15472889
theorem B7063199 : Blo 1206420 7063199 := bstep (se 1 (by rfl) ⟨5297399, by rfl⟩ : syracuseStep 7063199 = 10594799) B10594799
theorem B4073273 : Blo 1206420 4073273 := bstep (se 2 (by rfl) ⟨1527477, by rfl⟩ : syracuseStep 4073273 = 3054955) B3054955
theorem B1206439 : Blo 1206420 1206439 := bstep (se 1 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 1206439 = 1809659) B1809659
theorem B1206523 : Blo 1206420 1206523 := bstep (se 1 (by rfl) ⟨904892, by rfl⟩ : syracuseStep 1206523 = 1809785) B1809785
theorem B1206683 : Blo 1206420 1206683 := bstep (se 1 (by rfl) ⟨905012, by rfl⟩ : syracuseStep 1206683 = 1810025) B1810025
theorem B2714579 : Blo 1206420 2714579 := bstep (se 1 (by rfl) ⟨2035934, by rfl⟩ : syracuseStep 2714579 = 4071869) B4071869
theorem B9063419 : Blo 1206420 9063419 := bstep (se 1 (by rfl) ⟨6797564, by rfl⟩ : syracuseStep 9063419 = 13595129) B13595129
theorem B2714651 : Blo 1206420 2714651 := bstep (se 1 (by rfl) ⟨2035988, by rfl⟩ : syracuseStep 2714651 = 4071977) B4071977
theorem B1207451 : Blo 1206420 1207451 := bstep (se 1 (by rfl) ⟨905588, by rfl⟩ : syracuseStep 1207451 = 1811177) B1811177
theorem B1207463 : Blo 1206420 1207463 := bstep (se 1 (by rfl) ⟨905597, by rfl⟩ : syracuseStep 1207463 = 1811195) B1811195
theorem B2714831 : Blo 1206420 2714831 := bstep (se 1 (by rfl) ⟨2036123, by rfl⟩ : syracuseStep 2714831 = 4072247) B4072247
theorem B1207807 : Blo 1206420 1207807 := bstep (se 1 (by rfl) ⟨905855, by rfl⟩ : syracuseStep 1207807 = 1811711) B1811711
theorem B5157083 : Blo 1206420 5157083 := bstep (se 1 (by rfl) ⟨3867812, by rfl⟩ : syracuseStep 5157083 = 7735625) B7735625
theorem B2716001 : Blo 1206420 2716001 := bstep (se 2 (by rfl) ⟨1018500, by rfl⟩ : syracuseStep 2716001 = 2037001) B2037001
theorem B6525377 : Blo 1206420 6525377 := bstep (se 2 (by rfl) ⟨2447016, by rfl⟩ : syracuseStep 6525377 = 4894033) B4894033
theorem B3437225 : Blo 1206420 3437225 := bstep (se 2 (by rfl) ⟨1288959, by rfl⟩ : syracuseStep 3437225 = 2577919) B2577919
theorem B24769475 : Blo 1206420 24769475 := bstep (se 1 (by rfl) ⟨18577106, by rfl⟩ : syracuseStep 24769475 = 37154213) B37154213
theorem B2716703 : Blo 1206420 2716703 := bstep (se 1 (by rfl) ⟨2037527, by rfl⟩ : syracuseStep 2716703 = 4075055) B4075055
theorem B6878753 : Blo 1206420 6878753 := bstep (se 2 (by rfl) ⟨2579532, by rfl⟩ : syracuseStep 6878753 = 5159065) B5159065
theorem B2037487 : Blo 1206420 2037487 := bstep (se 1 (by rfl) ⟨1528115, by rfl⟩ : syracuseStep 2037487 = 3056231) B3056231
theorem B6871007 : Blo 1206420 6871007 := bstep (se 1 (by rfl) ⟨5153255, by rfl⟩ : syracuseStep 6871007 = 10306511) B10306511
theorem B6109181 : Blo 1206420 6109181 := bstep (se 3 (by rfl) ⟨1145471, by rfl⟩ : syracuseStep 6109181 = 2290943) B2290943
theorem B2717819 : Blo 1206420 2717819 := bstep (se 1 (by rfl) ⟨2038364, by rfl⟩ : syracuseStep 2717819 = 4076729) B4076729
theorem B1357951 : Blo 1206420 1357951 := bstep (se 1 (by rfl) ⟨1018463, by rfl⟩ : syracuseStep 1357951 = 2036927) B2036927
theorem B5159339 : Blo 1206420 5159339 := bstep (se 1 (by rfl) ⟨3869504, by rfl⟩ : syracuseStep 5159339 = 7739009) B7739009
theorem B15686075 : Blo 1206420 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B2980319 : Blo 1206420 2980319 := bstep (se 1 (by rfl) ⟨2235239, by rfl⟩ : syracuseStep 2980319 = 4470479) B4470479
theorem B1718777 : Blo 1206420 1718777 := bstep (se 2 (by rfl) ⟨644541, by rfl⟩ : syracuseStep 1718777 = 1289083) B1289083
theorem B71490235 : Blo 1206420 71490235 := bstep (se 1 (by rfl) ⟨53617676, by rfl⟩ : syracuseStep 71490235 = 107235353) B107235353
theorem B11008811 : Blo 1206420 11008811 := bstep (se 1 (by rfl) ⟨8256608, by rfl⟩ : syracuseStep 11008811 = 16513217) B16513217
theorem B41827195 : Blo 1206420 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B3865583 : Blo 1206420 3865583 := bstep (se 1 (by rfl) ⟨2899187, by rfl⟩ : syracuseStep 3865583 = 5798375) B5798375
theorem B15473915 : Blo 1206420 15473915 := bstep (se 1 (by rfl) ⟨11605436, by rfl⟩ : syracuseStep 15473915 = 23210873) B23210873
theorem B16981325 : Blo 1206420 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B1809755 : Blo 1206420 1809755 := bstep (se 1 (by rfl) ⟨1357316, by rfl⟩ : syracuseStep 1809755 = 2714633) B2714633
theorem B14876111 : Blo 1206420 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B9166445 : Blo 1206420 9166445 := bstep (se 3 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 9166445 = 3437417) B3437417
theorem B2899775 : Blo 1206420 2899775 := bstep (se 1 (by rfl) ⟨2174831, by rfl⟩ : syracuseStep 2899775 = 4349663) B4349663
theorem B2899937 : Blo 1206420 2899937 := bstep (se 2 (by rfl) ⟨1087476, by rfl⟩ : syracuseStep 2899937 = 2174953) B2174953
theorem B1810601 : Blo 1206420 1810601 := bstep (se 2 (by rfl) ⟨678975, by rfl⟩ : syracuseStep 1810601 = 1357951) B1357951
theorem B1810667 : Blo 1206420 1810667 := bstep (se 1 (by rfl) ⟨1358000, by rfl⟩ : syracuseStep 1810667 = 2716001) B2716001
theorem B5226751 : Blo 1206420 5226751 := bstep (se 1 (by rfl) ⟨3920063, by rfl⟩ : syracuseStep 5226751 = 7840127) B7840127
theorem B4350251 : Blo 1206420 4350251 := bstep (se 1 (by rfl) ⟨3262688, by rfl⟩ : syracuseStep 4350251 = 6525377) B6525377
theorem B7733677 : Blo 1206420 7733677 := bstep (se 3 (by rfl) ⟨1450064, by rfl⟩ : syracuseStep 7733677 = 2900129) B2900129
theorem B1811135 : Blo 1206420 1811135 := bstep (se 1 (by rfl) ⟨1358351, by rfl⟩ : syracuseStep 1811135 = 2716703) B2716703
theorem B41829533 : Blo 1206420 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B7947517 : Blo 1206420 7947517 := bstep (se 3 (by rfl) ⟨1490159, by rfl⟩ : syracuseStep 7947517 = 2980319) B2980319
theorem B4580671 : Blo 1206420 4580671 := bstep (se 1 (by rfl) ⟨3435503, by rfl⟩ : syracuseStep 4580671 = 6871007) B6871007
theorem B4072787 : Blo 1206420 4072787 := bstep (se 1 (by rfl) ⟨3054590, by rfl⟩ : syracuseStep 4072787 = 6109181) B6109181
theorem B1811879 : Blo 1206420 1811879 := bstep (se 1 (by rfl) ⟨1358909, by rfl⟩ : syracuseStep 1811879 = 2717819) B2717819
theorem B10315943 : Blo 1206420 10315943 := bstep (se 1 (by rfl) ⟨7736957, by rfl⟩ : syracuseStep 10315943 = 15473915) B15473915
theorem B1206503 : Blo 1206420 1206503 := bstep (se 1 (by rfl) ⟨904877, by rfl⟩ : syracuseStep 1206503 = 1809755) B1809755
theorem B10308221 : Blo 1206420 10308221 := bstep (se 3 (by rfl) ⟨1932791, by rfl⟩ : syracuseStep 10308221 = 3865583) B3865583
theorem B24169117 : Blo 1206420 24169117 := bstep (se 3 (by rfl) ⟨4531709, by rfl⟩ : syracuseStep 24169117 = 9063419) B9063419
theorem B5155579 : Blo 1206420 5155579 := bstep (se 1 (by rfl) ⟨3866684, by rfl⟩ : syracuseStep 5155579 = 7733369) B7733369
theorem B1207143 : Blo 1206420 1207143 := bstep (se 1 (by rfl) ⟨905357, by rfl⟩ : syracuseStep 1207143 = 1810715) B1810715
theorem B1207279 : Blo 1206420 1207279 := bstep (se 1 (by rfl) ⟨905459, by rfl⟩ : syracuseStep 1207279 = 1810919) B1810919
theorem B1207579 : Blo 1206420 1207579 := bstep (se 1 (by rfl) ⟨905684, by rfl⟩ : syracuseStep 1207579 = 1811369) B1811369
theorem B1207711 : Blo 1206420 1207711 := bstep (se 1 (by rfl) ⟨905783, by rfl⟩ : syracuseStep 1207711 = 1811567) B1811567
theorem B1207835 : Blo 1206420 1207835 := bstep (se 1 (by rfl) ⟨905876, by rfl⟩ : syracuseStep 1207835 = 1811753) B1811753
theorem B6876839 : Blo 1206420 6876839 := bstep (se 1 (by rfl) ⟨5157629, by rfl⟩ : syracuseStep 6876839 = 10315259) B10315259
theorem B2715515 : Blo 1206420 2715515 := bstep (se 1 (by rfl) ⟨2036636, by rfl⟩ : syracuseStep 2715515 = 4073273) B4073273
theorem B4583405 : Blo 1206420 4583405 := bstep (se 3 (by rfl) ⟨859388, by rfl⟩ : syracuseStep 4583405 = 1718777) B1718777
theorem B9917407 : Blo 1206420 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B2716649 : Blo 1206420 2716649 := bstep (se 2 (by rfl) ⟨1018743, by rfl⟩ : syracuseStep 2716649 = 2037487) B2037487
theorem B3438055 : Blo 1206420 3438055 := bstep (se 1 (by rfl) ⟨2578541, by rfl⟩ : syracuseStep 3438055 = 5157083) B5157083
theorem B282154691 : Blo 1206420 282154691 := bstep (se 1 (by rfl) ⟨211616018, by rfl⟩ : syracuseStep 282154691 = 423232037) B423232037
theorem B2291483 : Blo 1206420 2291483 := bstep (se 1 (by rfl) ⟨1718612, by rfl⟩ : syracuseStep 2291483 = 3437225) B3437225
theorem B16512983 : Blo 1206420 16512983 := bstep (se 1 (by rfl) ⟨12384737, by rfl⟩ : syracuseStep 16512983 = 24769475) B24769475
theorem B2037919 : Blo 1206420 2037919 := bstep (se 1 (by rfl) ⟨1528439, by rfl⟩ : syracuseStep 2037919 = 3056879) B3056879
theorem B9164987 : Blo 1206420 9164987 := bstep (se 1 (by rfl) ⟨6873740, by rfl⟩ : syracuseStep 9164987 = 13747481) B13747481
theorem B95320313 : Blo 1206420 95320313 := bstep (se 2 (by rfl) ⟨35745117, by rfl⟩ : syracuseStep 95320313 = 71490235) B71490235
theorem B4585835 : Blo 1206420 4585835 := bstep (se 1 (by rfl) ⟨3439376, by rfl⟩ : syracuseStep 4585835 = 6878753) B6878753
theorem B4708799 : Blo 1206420 4708799 := bstep (se 1 (by rfl) ⟨3531599, by rfl⟩ : syracuseStep 4708799 = 7063199) B7063199
theorem B55769593 : Blo 1206420 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B3439559 : Blo 1206420 3439559 := bstep (se 1 (by rfl) ⟨2579669, by rfl⟩ : syracuseStep 3439559 = 5159339) B5159339
theorem B7339207 : Blo 1206420 7339207 := bstep (se 1 (by rfl) ⟨5504405, by rfl⟩ : syracuseStep 7339207 = 11008811) B11008811
theorem B1809719 : Blo 1206420 1809719 := bstep (se 1 (by rfl) ⟨1357289, by rfl⟩ : syracuseStep 1809719 = 2714579) B2714579
theorem B1809767 : Blo 1206420 1809767 := bstep (se 1 (by rfl) ⟨1357325, by rfl⟩ : syracuseStep 1809767 = 2714651) B2714651
theorem B1809887 : Blo 1206420 1809887 := bstep (se 1 (by rfl) ⟨1357415, by rfl⟩ : syracuseStep 1809887 = 2714831) B2714831
theorem B11320883 : Blo 1206420 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B6110963 : Blo 1206420 6110963 := bstep (se 1 (by rfl) ⟨4583222, by rfl⟩ : syracuseStep 6110963 = 9166445) B9166445
theorem B1933183 : Blo 1206420 1933183 := bstep (se 1 (by rfl) ⟨1449887, by rfl⟩ : syracuseStep 1933183 = 2899775) B2899775
theorem B1933291 : Blo 1206420 1933291 := bstep (se 1 (by rfl) ⟨1449968, by rfl⟩ : syracuseStep 1933291 = 2899937) B2899937
theorem B2900167 : Blo 1206420 2900167 := bstep (se 1 (by rfl) ⟨2175125, by rfl⟩ : syracuseStep 2900167 = 4350251) B4350251
theorem B1811099 : Blo 1206420 1811099 := bstep (se 1 (by rfl) ⟨1358324, by rfl⟩ : syracuseStep 1811099 = 2716649) B2716649
theorem B74359457 : Blo 1206420 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B27886355 : Blo 1206420 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B6874105 : Blo 1206420 6874105 := bstep (se 2 (by rfl) ⟨2577789, by rfl⟩ : syracuseStep 6874105 = 5155579) B5155579
theorem B63546875 : Blo 1206420 63546875 := bstep (se 1 (by rfl) ⟨47660156, by rfl⟩ : syracuseStep 63546875 = 95320313) B95320313
theorem B3057223 : Blo 1206420 3057223 := bstep (se 1 (by rfl) ⟨2292917, by rfl⟩ : syracuseStep 3057223 = 4585835) B4585835
theorem B3139199 : Blo 1206420 3139199 := bstep (se 1 (by rfl) ⟨2354399, by rfl⟩ : syracuseStep 3139199 = 4708799) B4708799
theorem B752412509 : Blo 1206420 752412509 := bstep (se 3 (by rfl) ⟨141077345, by rfl⟩ : syracuseStep 752412509 = 282154691) B282154691
theorem B1206479 : Blo 1206420 1206479 := bstep (se 1 (by rfl) ⟨904859, by rfl⟩ : syracuseStep 1206479 = 1809719) B1809719
theorem B1206511 : Blo 1206420 1206511 := bstep (se 1 (by rfl) ⟨904883, by rfl⟩ : syracuseStep 1206511 = 1809767) B1809767
theorem B1206591 : Blo 1206420 1206591 := bstep (se 1 (by rfl) ⟨904943, by rfl⟩ : syracuseStep 1206591 = 1809887) B1809887
theorem B7547255 : Blo 1206420 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B4073975 : Blo 1206420 4073975 := bstep (se 1 (by rfl) ⟨3055481, by rfl⟩ : syracuseStep 4073975 = 6110963) B6110963
theorem B1207067 : Blo 1206420 1207067 := bstep (se 1 (by rfl) ⟨905300, by rfl⟩ : syracuseStep 1207067 = 1810601) B1810601
theorem B1207111 : Blo 1206420 1207111 := bstep (se 1 (by rfl) ⟨905333, by rfl⟩ : syracuseStep 1207111 = 1810667) B1810667
theorem B1207423 : Blo 1206420 1207423 := bstep (se 1 (by rfl) ⟨905567, by rfl⟩ : syracuseStep 1207423 = 1811135) B1811135
theorem B2715191 : Blo 1206420 2715191 := bstep (se 1 (by rfl) ⟨2036393, by rfl⟩ : syracuseStep 2715191 = 4072787) B4072787
theorem B1207919 : Blo 1206420 1207919 := bstep (se 1 (by rfl) ⟨905939, by rfl⟩ : syracuseStep 1207919 = 1811879) B1811879
theorem B1527655 : Blo 1206420 1527655 := bstep (se 1 (by rfl) ⟨1145741, by rfl⟩ : syracuseStep 1527655 = 2291483) B2291483
theorem B6877295 : Blo 1206420 6877295 := bstep (se 1 (by rfl) ⟨5157971, by rfl⟩ : syracuseStep 6877295 = 10315943) B10315943
theorem B9785609 : Blo 1206420 9785609 := bstep (se 2 (by rfl) ⟨3669603, by rfl⟩ : syracuseStep 9785609 = 7339207) B7339207
theorem B10596689 : Blo 1206420 10596689 := bstep (se 2 (by rfl) ⟨3973758, by rfl⟩ : syracuseStep 10596689 = 7947517) B7947517
theorem B6107561 : Blo 1206420 6107561 := bstep (se 2 (by rfl) ⟨2290335, by rfl⟩ : syracuseStep 6107561 = 4580671) B4580671
theorem B4584073 : Blo 1206420 4584073 := bstep (se 2 (by rfl) ⟨1719027, by rfl⟩ : syracuseStep 4584073 = 3438055) B3438055
theorem B4584559 : Blo 1206420 4584559 := bstep (se 1 (by rfl) ⟨3438419, by rfl⟩ : syracuseStep 4584559 = 6876839) B6876839
theorem B52892837 : Blo 1206420 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B2577577 : Blo 1206420 2577577 := bstep (se 2 (by rfl) ⟨966591, by rfl⟩ : syracuseStep 2577577 = 1933183) B1933183
theorem B10310885 : Blo 1206420 10310885 := bstep (se 4 (by rfl) ⟨966645, by rfl⟩ : syracuseStep 10310885 = 1933291) B1933291
theorem B2717225 : Blo 1206420 2717225 := bstep (se 2 (by rfl) ⟨1018959, by rfl⟩ : syracuseStep 2717225 = 2037919) B2037919
theorem B6969001 : Blo 1206420 6969001 := bstep (se 2 (by rfl) ⟨2613375, by rfl⟩ : syracuseStep 6969001 = 5226751) B5226751
theorem B10311569 : Blo 1206420 10311569 := bstep (se 2 (by rfl) ⟨3866838, by rfl⟩ : syracuseStep 10311569 = 7733677) B7733677
theorem B32225489 : Blo 1206420 32225489 := bstep (se 2 (by rfl) ⟨12084558, by rfl⟩ : syracuseStep 32225489 = 24169117) B24169117
theorem B11008655 : Blo 1206420 11008655 := bstep (se 1 (by rfl) ⟨8256491, by rfl⟩ : syracuseStep 11008655 = 16512983) B16512983
theorem B6109991 : Blo 1206420 6109991 := bstep (se 1 (by rfl) ⟨4582493, by rfl⟩ : syracuseStep 6109991 = 9164987) B9164987
theorem B6872147 : Blo 1206420 6872147 := bstep (se 1 (by rfl) ⟨5154110, by rfl⟩ : syracuseStep 6872147 = 10308221) B10308221
theorem B2293039 : Blo 1206420 2293039 := bstep (se 1 (by rfl) ⟨1719779, by rfl⟩ : syracuseStep 2293039 = 3439559) B3439559
theorem B1810343 : Blo 1206420 1810343 := bstep (se 1 (by rfl) ⟨1357757, by rfl⟩ : syracuseStep 1810343 = 2715515) B2715515
theorem B3055603 : Blo 1206420 3055603 := bstep (se 1 (by rfl) ⟨2291702, by rfl⟩ : syracuseStep 3055603 = 4583405) B4583405
theorem B4071707 : Blo 1206420 4071707 := bstep (se 1 (by rfl) ⟨3053780, by rfl⟩ : syracuseStep 4071707 = 6107561) B6107561
theorem B6873923 : Blo 1206420 6873923 := bstep (se 1 (by rfl) ⟨5155442, by rfl⟩ : syracuseStep 6873923 = 10310885) B10310885
theorem B6112097 : Blo 1206420 6112097 := bstep (se 2 (by rfl) ⟨2292036, by rfl⟩ : syracuseStep 6112097 = 4584073) B4584073
theorem B1811483 : Blo 1206420 1811483 := bstep (se 1 (by rfl) ⟨1358612, by rfl⟩ : syracuseStep 1811483 = 2717225) B2717225
theorem B15467557 : Blo 1206420 15467557 := bstep (se 4 (by rfl) ⟨1450083, by rfl⟩ : syracuseStep 15467557 = 2900167) B2900167
theorem B6874379 : Blo 1206420 6874379 := bstep (se 1 (by rfl) ⟨5155784, by rfl⟩ : syracuseStep 6874379 = 10311569) B10311569
theorem B6112745 : Blo 1206420 6112745 := bstep (se 2 (by rfl) ⟨2292279, by rfl⟩ : syracuseStep 6112745 = 4584559) B4584559
theorem B5031503 : Blo 1206420 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B3057385 : Blo 1206420 3057385 := bstep (se 2 (by rfl) ⟨1146519, by rfl⟩ : syracuseStep 3057385 = 2293039) B2293039
theorem B4073327 : Blo 1206420 4073327 := bstep (se 1 (by rfl) ⟨3054995, by rfl⟩ : syracuseStep 4073327 = 6109991) B6109991
theorem B4581431 : Blo 1206420 4581431 := bstep (se 1 (by rfl) ⟨3436073, by rfl⟩ : syracuseStep 4581431 = 6872147) B6872147
theorem B9292001 : Blo 1206420 9292001 := bstep (se 2 (by rfl) ⟨3484500, by rfl⟩ : syracuseStep 9292001 = 6969001) B6969001
theorem B1206895 : Blo 1206420 1206895 := bstep (se 1 (by rfl) ⟨905171, by rfl⟩ : syracuseStep 1206895 = 1810343) B1810343
theorem B4074137 : Blo 1206420 4074137 := bstep (se 2 (by rfl) ⟨1527801, by rfl⟩ : syracuseStep 4074137 = 3055603) B3055603
theorem B6523739 : Blo 1206420 6523739 := bstep (se 1 (by rfl) ⟨4892804, by rfl⟩ : syracuseStep 6523739 = 9785609) B9785609
theorem B7064459 : Blo 1206420 7064459 := bstep (se 1 (by rfl) ⟨5298344, by rfl⟩ : syracuseStep 7064459 = 10596689) B10596689
theorem B1207399 : Blo 1206420 1207399 := bstep (se 1 (by rfl) ⟨905549, by rfl⟩ : syracuseStep 1207399 = 1811099) B1811099
theorem B49572971 : Blo 1206420 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B18590903 : Blo 1206420 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B35261891 : Blo 1206420 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B42364583 : Blo 1206420 42364583 := bstep (se 1 (by rfl) ⟨31773437, by rfl⟩ : syracuseStep 42364583 = 63546875) B63546875
theorem B2092799 : Blo 1206420 2092799 := bstep (se 1 (by rfl) ⟨1569599, by rfl⟩ : syracuseStep 2092799 = 3139199) B3139199
theorem B501608339 : Blo 1206420 501608339 := bstep (se 1 (by rfl) ⟨376206254, by rfl⟩ : syracuseStep 501608339 = 752412509) B752412509
theorem B21483659 : Blo 1206420 21483659 := bstep (se 1 (by rfl) ⟨16112744, by rfl⟩ : syracuseStep 21483659 = 32225489) B32225489
theorem B3436769 : Blo 1206420 3436769 := bstep (se 2 (by rfl) ⟨1288788, by rfl⟩ : syracuseStep 3436769 = 2577577) B2577577
theorem B2715983 : Blo 1206420 2715983 := bstep (se 1 (by rfl) ⟨2036987, by rfl⟩ : syracuseStep 2715983 = 4073975) B4073975
theorem B4076297 : Blo 1206420 4076297 := bstep (se 2 (by rfl) ⟨1528611, by rfl⟩ : syracuseStep 4076297 = 3057223) B3057223
theorem B2036873 : Blo 1206420 2036873 := bstep (se 2 (by rfl) ⟨763827, by rfl⟩ : syracuseStep 2036873 = 1527655) B1527655
theorem B4584863 : Blo 1206420 4584863 := bstep (se 1 (by rfl) ⟨3438647, by rfl⟩ : syracuseStep 4584863 = 6877295) B6877295
theorem B9165473 : Blo 1206420 9165473 := bstep (se 2 (by rfl) ⟨3437052, by rfl⟩ : syracuseStep 9165473 = 6874105) B6874105
theorem B7339103 : Blo 1206420 7339103 := bstep (se 1 (by rfl) ⟨5504327, by rfl⟩ : syracuseStep 7339103 = 11008655) B11008655
theorem B1810127 : Blo 1206420 1810127 := bstep (se 1 (by rfl) ⟨1357595, by rfl⟩ : syracuseStep 1810127 = 2715191) B2715191
theorem B1810655 : Blo 1206420 1810655 := bstep (se 1 (by rfl) ⟨1357991, by rfl⟩ : syracuseStep 1810655 = 2715983) B2715983
theorem B3056575 : Blo 1206420 3056575 := bstep (se 1 (by rfl) ⟨2292431, by rfl⟩ : syracuseStep 3056575 = 4584863) B4584863
theorem B5580797 : Blo 1206420 5580797 := bstep (se 3 (by rfl) ⟨1046399, by rfl⟩ : syracuseStep 5580797 = 2092799) B2092799
theorem B4892735 : Blo 1206420 4892735 := bstep (se 1 (by rfl) ⟨3669551, by rfl⟩ : syracuseStep 4892735 = 7339103) B7339103
theorem B33048647 : Blo 1206420 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B1206751 : Blo 1206420 1206751 := bstep (se 1 (by rfl) ⟨905063, by rfl⟩ : syracuseStep 1206751 = 1810127) B1810127
theorem B14322439 : Blo 1206420 14322439 := bstep (se 1 (by rfl) ⟨10741829, by rfl⟩ : syracuseStep 14322439 = 21483659) B21483659
theorem B2714471 : Blo 1206420 2714471 := bstep (se 1 (by rfl) ⟨2035853, by rfl⟩ : syracuseStep 2714471 = 4071707) B4071707
theorem B4582615 : Blo 1206420 4582615 := bstep (se 1 (by rfl) ⟨3436961, by rfl⟩ : syracuseStep 4582615 = 6873923) B6873923
theorem B4074731 : Blo 1206420 4074731 := bstep (se 1 (by rfl) ⟨3056048, by rfl⟩ : syracuseStep 4074731 = 6112097) B6112097
theorem B1207655 : Blo 1206420 1207655 := bstep (se 1 (by rfl) ⟨905741, by rfl⟩ : syracuseStep 1207655 = 1811483) B1811483
theorem B4582919 : Blo 1206420 4582919 := bstep (se 1 (by rfl) ⟨3437189, by rfl⟩ : syracuseStep 4582919 = 6874379) B6874379
theorem B4075163 : Blo 1206420 4075163 := bstep (se 1 (by rfl) ⟨3056372, by rfl⟩ : syracuseStep 4075163 = 6112745) B6112745
theorem B3354335 : Blo 1206420 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B2715551 : Blo 1206420 2715551 := bstep (se 1 (by rfl) ⟨2036663, by rfl⟩ : syracuseStep 2715551 = 4073327) B4073327
theorem B20623409 : Blo 1206420 20623409 := bstep (se 2 (by rfl) ⟨7733778, by rfl⟩ : syracuseStep 20623409 = 15467557) B15467557
theorem B2716091 : Blo 1206420 2716091 := bstep (se 1 (by rfl) ⟨2037068, by rfl⟩ : syracuseStep 2716091 = 4074137) B4074137
theorem B23507927 : Blo 1206420 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B4076513 : Blo 1206420 4076513 := bstep (se 2 (by rfl) ⟨1528692, by rfl⟩ : syracuseStep 4076513 = 3057385) B3057385
theorem B28243055 : Blo 1206420 28243055 := bstep (se 1 (by rfl) ⟨21182291, by rfl⟩ : syracuseStep 28243055 = 42364583) B42364583
theorem B2291179 : Blo 1206420 2291179 := bstep (se 1 (by rfl) ⟨1718384, by rfl⟩ : syracuseStep 2291179 = 3436769) B3436769
theorem B2717531 : Blo 1206420 2717531 := bstep (se 1 (by rfl) ⟨2038148, by rfl⟩ : syracuseStep 2717531 = 4076297) B4076297
theorem B24778669 : Blo 1206420 24778669 := bstep (se 3 (by rfl) ⟨4646000, by rfl⟩ : syracuseStep 24778669 = 9292001) B9292001
theorem B1357915 : Blo 1206420 1357915 := bstep (se 1 (by rfl) ⟨1018436, by rfl⟩ : syracuseStep 1357915 = 2036873) B2036873
theorem B3054287 : Blo 1206420 3054287 := bstep (se 1 (by rfl) ⟨2290715, by rfl⟩ : syracuseStep 3054287 = 4581431) B4581431
theorem B6110315 : Blo 1206420 6110315 := bstep (se 1 (by rfl) ⟨4582736, by rfl⟩ : syracuseStep 6110315 = 9165473) B9165473
theorem B4349159 : Blo 1206420 4349159 := bstep (se 1 (by rfl) ⟨3261869, by rfl⟩ : syracuseStep 4349159 = 6523739) B6523739
theorem B4709639 : Blo 1206420 4709639 := bstep (se 1 (by rfl) ⟨3532229, by rfl⟩ : syracuseStep 4709639 = 7064459) B7064459
theorem B12393935 : Blo 1206420 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B334405559 : Blo 1206420 334405559 := bstep (se 1 (by rfl) ⟨250804169, by rfl⟩ : syracuseStep 334405559 = 501608339) B501608339
theorem B1810553 : Blo 1206420 1810553 := bstep (se 2 (by rfl) ⟨678957, by rfl⟩ : syracuseStep 1810553 = 1357915) B1357915
theorem B1810727 : Blo 1206420 1810727 := bstep (se 1 (by rfl) ⟨1358045, by rfl⟩ : syracuseStep 1810727 = 2716091) B2716091
theorem B15671951 : Blo 1206420 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B1811687 : Blo 1206420 1811687 := bstep (se 1 (by rfl) ⟨1358765, by rfl⟩ : syracuseStep 1811687 = 2717531) B2717531
theorem B4073543 : Blo 1206420 4073543 := bstep (se 1 (by rfl) ⟨3055157, by rfl⟩ : syracuseStep 4073543 = 6110315) B6110315
theorem B3139759 : Blo 1206420 3139759 := bstep (se 1 (by rfl) ⟨2354819, by rfl⟩ : syracuseStep 3139759 = 4709639) B4709639
theorem B13748939 : Blo 1206420 13748939 := bstep (se 1 (by rfl) ⟨10311704, by rfl⟩ : syracuseStep 13748939 = 20623409) B20623409
theorem B1207103 : Blo 1206420 1207103 := bstep (se 1 (by rfl) ⟨905327, by rfl⟩ : syracuseStep 1207103 = 1810655) B1810655
theorem B18828703 : Blo 1206420 18828703 := bstep (se 1 (by rfl) ⟨14121527, by rfl⟩ : syracuseStep 18828703 = 28243055) B28243055
theorem B4075433 : Blo 1206420 4075433 := bstep (se 2 (by rfl) ⟨1528287, by rfl⟩ : syracuseStep 4075433 = 3056575) B3056575
theorem B76386341 : Blo 1206420 76386341 := bstep (se 4 (by rfl) ⟨7161219, by rfl⟩ : syracuseStep 76386341 = 14322439) B14322439
theorem B22032431 : Blo 1206420 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B2036191 : Blo 1206420 2036191 := bstep (se 1 (by rfl) ⟨1527143, by rfl⟩ : syracuseStep 2036191 = 3054287) B3054287
theorem B2716487 : Blo 1206420 2716487 := bstep (se 1 (by rfl) ⟨2037365, by rfl⟩ : syracuseStep 2716487 = 4074731) B4074731
theorem B8262623 : Blo 1206420 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B2716775 : Blo 1206420 2716775 := bstep (se 1 (by rfl) ⟨2037581, by rfl⟩ : syracuseStep 2716775 = 4075163) B4075163
theorem B14882125 : Blo 1206420 14882125 := bstep (se 3 (by rfl) ⟨2790398, by rfl⟩ : syracuseStep 14882125 = 5580797) B5580797
theorem B13047293 : Blo 1206420 13047293 := bstep (se 3 (by rfl) ⟨2446367, by rfl⟩ : syracuseStep 13047293 = 4892735) B4892735
theorem B2717675 : Blo 1206420 2717675 := bstep (se 1 (by rfl) ⟨2038256, by rfl⟩ : syracuseStep 2717675 = 4076513) B4076513
theorem B6110153 : Blo 1206420 6110153 := bstep (se 2 (by rfl) ⟨2291307, by rfl⟩ : syracuseStep 6110153 = 4582615) B4582615
theorem B1809647 : Blo 1206420 1809647 := bstep (se 1 (by rfl) ⟨1357235, by rfl⟩ : syracuseStep 1809647 = 2714471) B2714471
theorem B3054905 : Blo 1206420 3054905 := bstep (se 2 (by rfl) ⟨1145589, by rfl⟩ : syracuseStep 3054905 = 2291179) B2291179
theorem B2899439 : Blo 1206420 2899439 := bstep (se 1 (by rfl) ⟨2174579, by rfl⟩ : syracuseStep 2899439 = 4349159) B4349159
theorem B3055279 : Blo 1206420 3055279 := bstep (se 1 (by rfl) ⟨2291459, by rfl⟩ : syracuseStep 3055279 = 4582919) B4582919
theorem B2236223 : Blo 1206420 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B33038225 : Blo 1206420 33038225 := bstep (se 2 (by rfl) ⟨12389334, by rfl⟩ : syracuseStep 33038225 = 24778669) B24778669
theorem B1810367 : Blo 1206420 1810367 := bstep (se 1 (by rfl) ⟨1357775, by rfl⟩ : syracuseStep 1810367 = 2715551) B2715551
theorem B222937039 : Blo 1206420 222937039 := bstep (se 1 (by rfl) ⟨167202779, by rfl⟩ : syracuseStep 222937039 = 334405559) B334405559
theorem B14688287 : Blo 1206420 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B1810991 : Blo 1206420 1810991 := bstep (se 1 (by rfl) ⟨1358243, by rfl⟩ : syracuseStep 1810991 = 2716487) B2716487
theorem B1811183 : Blo 1206420 1811183 := bstep (se 1 (by rfl) ⟨1358387, by rfl⟩ : syracuseStep 1811183 = 2716775) B2716775
theorem B16745381 : Blo 1206420 16745381 := bstep (se 4 (by rfl) ⟨1569879, by rfl⟩ : syracuseStep 16745381 = 3139759) B3139759
theorem B1811783 : Blo 1206420 1811783 := bstep (se 1 (by rfl) ⟨1358837, by rfl⟩ : syracuseStep 1811783 = 2717675) B2717675
theorem B19842833 : Blo 1206420 19842833 := bstep (se 2 (by rfl) ⟨7441062, by rfl⟩ : syracuseStep 19842833 = 14882125) B14882125
theorem B4073435 : Blo 1206420 4073435 := bstep (se 1 (by rfl) ⟨3055076, by rfl⟩ : syracuseStep 4073435 = 6110153) B6110153
theorem B1206431 : Blo 1206420 1206431 := bstep (se 1 (by rfl) ⟨904823, by rfl⟩ : syracuseStep 1206431 = 1809647) B1809647
theorem B100419749 : Blo 1206420 100419749 := bstep (se 4 (by rfl) ⟨9414351, by rfl⟩ : syracuseStep 100419749 = 18828703) B18828703
theorem B4073705 : Blo 1206420 4073705 := bstep (se 2 (by rfl) ⟨1527639, by rfl⟩ : syracuseStep 4073705 = 3055279) B3055279
theorem B297249385 : Blo 1206420 297249385 := bstep (se 2 (by rfl) ⟨111468519, by rfl⟩ : syracuseStep 297249385 = 222937039) B222937039
theorem B1206911 : Blo 1206420 1206911 := bstep (se 1 (by rfl) ⟨905183, by rfl⟩ : syracuseStep 1206911 = 1810367) B1810367
theorem B50924227 : Blo 1206420 50924227 := bstep (se 1 (by rfl) ⟨38193170, by rfl⟩ : syracuseStep 50924227 = 76386341) B76386341
theorem B1207035 : Blo 1206420 1207035 := bstep (se 1 (by rfl) ⟨905276, by rfl⟩ : syracuseStep 1207035 = 1810553) B1810553
theorem B1207151 : Blo 1206420 1207151 := bstep (se 1 (by rfl) ⟨905363, by rfl⟩ : syracuseStep 1207151 = 1810727) B1810727
theorem B10447967 : Blo 1206420 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B2714921 : Blo 1206420 2714921 := bstep (se 2 (by rfl) ⟨1018095, by rfl⟩ : syracuseStep 2714921 = 2036191) B2036191
theorem B5508415 : Blo 1206420 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B1207791 : Blo 1206420 1207791 := bstep (se 1 (by rfl) ⟨905843, by rfl⟩ : syracuseStep 1207791 = 1811687) B1811687
theorem B2715695 : Blo 1206420 2715695 := bstep (se 1 (by rfl) ⟨2036771, by rfl⟩ : syracuseStep 2715695 = 4073543) B4073543
theorem B2036603 : Blo 1206420 2036603 := bstep (se 1 (by rfl) ⟨1527452, by rfl⟩ : syracuseStep 2036603 = 3054905) B3054905
theorem B22025483 : Blo 1206420 22025483 := bstep (se 1 (by rfl) ⟨16519112, by rfl⟩ : syracuseStep 22025483 = 33038225) B33038225
theorem B2716955 : Blo 1206420 2716955 := bstep (se 1 (by rfl) ⟨2037716, by rfl⟩ : syracuseStep 2716955 = 4075433) B4075433
theorem B8698195 : Blo 1206420 8698195 := bstep (se 1 (by rfl) ⟨6523646, by rfl⟩ : syracuseStep 8698195 = 13047293) B13047293
theorem B9165959 : Blo 1206420 9165959 := bstep (se 1 (by rfl) ⟨6874469, by rfl⟩ : syracuseStep 9165959 = 13748939) B13748939
theorem B1932959 : Blo 1206420 1932959 := bstep (se 1 (by rfl) ⟨1449719, by rfl⟩ : syracuseStep 1932959 = 2899439) B2899439
theorem B1490815 : Blo 1206420 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B1810463 : Blo 1206420 1810463 := bstep (se 1 (by rfl) ⟨1357847, by rfl⟩ : syracuseStep 1810463 = 2715695) B2715695
theorem B1811303 : Blo 1206420 1811303 := bstep (se 1 (by rfl) ⟨1358477, by rfl⟩ : syracuseStep 1811303 = 2716955) B2716955
theorem B66946499 : Blo 1206420 66946499 := bstep (se 1 (by rfl) ⟨50209874, by rfl⟩ : syracuseStep 66946499 = 100419749) B100419749
theorem B29378213 : Blo 1206420 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B6965311 : Blo 1206420 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B1288639 : Blo 1206420 1288639 := bstep (se 1 (by rfl) ⟨966479, by rfl⟩ : syracuseStep 1288639 = 1932959) B1932959
theorem B9792191 : Blo 1206420 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B1207327 : Blo 1206420 1207327 := bstep (se 1 (by rfl) ⟨905495, by rfl⟩ : syracuseStep 1207327 = 1810991) B1810991
theorem B1207455 : Blo 1206420 1207455 := bstep (se 1 (by rfl) ⟨905591, by rfl⟩ : syracuseStep 1207455 = 1811183) B1811183
theorem B396332513 : Blo 1206420 396332513 := bstep (se 2 (by rfl) ⟨148624692, by rfl⟩ : syracuseStep 396332513 = 297249385) B297249385
theorem B14683655 : Blo 1206420 14683655 := bstep (se 1 (by rfl) ⟨11012741, by rfl⟩ : syracuseStep 14683655 = 22025483) B22025483
theorem B1207855 : Blo 1206420 1207855 := bstep (se 1 (by rfl) ⟨905891, by rfl⟩ : syracuseStep 1207855 = 1811783) B1811783
theorem B67898969 : Blo 1206420 67898969 := bstep (se 2 (by rfl) ⟨25462113, by rfl⟩ : syracuseStep 67898969 = 50924227) B50924227
theorem B2715623 : Blo 1206420 2715623 := bstep (se 1 (by rfl) ⟨2036717, by rfl⟩ : syracuseStep 2715623 = 4073435) B4073435
theorem B2715803 : Blo 1206420 2715803 := bstep (se 1 (by rfl) ⟨2036852, by rfl⟩ : syracuseStep 2715803 = 4073705) B4073705
theorem B1987753 : Blo 1206420 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B11597593 : Blo 1206420 11597593 := bstep (se 2 (by rfl) ⟨4349097, by rfl⟩ : syracuseStep 11597593 = 8698195) B8698195
theorem B1357735 : Blo 1206420 1357735 := bstep (se 1 (by rfl) ⟨1018301, by rfl⟩ : syracuseStep 1357735 = 2036603) B2036603
theorem B11163587 : Blo 1206420 11163587 := bstep (se 1 (by rfl) ⟨8372690, by rfl⟩ : syracuseStep 11163587 = 16745381) B16745381
theorem B13228555 : Blo 1206420 13228555 := bstep (se 1 (by rfl) ⟨9921416, by rfl⟩ : syracuseStep 13228555 = 19842833) B19842833
theorem B6110639 : Blo 1206420 6110639 := bstep (se 1 (by rfl) ⟨4582979, by rfl⟩ : syracuseStep 6110639 = 9165959) B9165959
theorem B1809947 : Blo 1206420 1809947 := bstep (se 1 (by rfl) ⟨1357460, by rfl⟩ : syracuseStep 1809947 = 2714921) B2714921
theorem B1810535 : Blo 1206420 1810535 := bstep (se 1 (by rfl) ⟨1357901, by rfl⟩ : syracuseStep 1810535 = 2715803) B2715803
theorem B17638073 : Blo 1206420 17638073 := bstep (se 2 (by rfl) ⟨6614277, by rfl⟩ : syracuseStep 17638073 = 13228555) B13228555
theorem B44630999 : Blo 1206420 44630999 := bstep (se 1 (by rfl) ⟨33473249, by rfl⟩ : syracuseStep 44630999 = 66946499) B66946499
theorem B4073759 : Blo 1206420 4073759 := bstep (se 1 (by rfl) ⟨3055319, by rfl⟩ : syracuseStep 4073759 = 6110639) B6110639
theorem B1206631 : Blo 1206420 1206631 := bstep (se 1 (by rfl) ⟨904973, by rfl⟩ : syracuseStep 1206631 = 1809947) B1809947
theorem B1206975 : Blo 1206420 1206975 := bstep (se 1 (by rfl) ⟨905231, by rfl⟩ : syracuseStep 1206975 = 1810463) B1810463
theorem B1207535 : Blo 1206420 1207535 := bstep (se 1 (by rfl) ⟨905651, by rfl⟩ : syracuseStep 1207535 = 1811303) B1811303
theorem B2650337 : Blo 1206420 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B264221675 : Blo 1206420 264221675 := bstep (se 1 (by rfl) ⟨198166256, by rfl⟩ : syracuseStep 264221675 = 396332513) B396332513
theorem B15463457 : Blo 1206420 15463457 := bstep (se 2 (by rfl) ⟨5798796, by rfl⟩ : syracuseStep 15463457 = 11597593) B11597593
theorem B45265979 : Blo 1206420 45265979 := bstep (se 1 (by rfl) ⟨33949484, by rfl⟩ : syracuseStep 45265979 = 67898969) B67898969
theorem B9287081 : Blo 1206420 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B1718185 : Blo 1206420 1718185 := bstep (se 2 (by rfl) ⟨644319, by rfl⟩ : syracuseStep 1718185 = 1288639) B1288639
theorem B19585475 : Blo 1206420 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B6528127 : Blo 1206420 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B9789103 : Blo 1206420 9789103 := bstep (se 1 (by rfl) ⟨7341827, by rfl⟩ : syracuseStep 9789103 = 14683655) B14683655
theorem B29769565 : Blo 1206420 29769565 := bstep (se 3 (by rfl) ⟨5581793, by rfl⟩ : syracuseStep 29769565 = 11163587) B11163587
theorem B1810313 : Blo 1206420 1810313 := bstep (se 2 (by rfl) ⟨678867, by rfl⟩ : syracuseStep 1810313 = 1357735) B1357735
theorem B1810415 : Blo 1206420 1810415 := bstep (se 1 (by rfl) ⟨1357811, by rfl⟩ : syracuseStep 1810415 = 2715623) B2715623
theorem B29753999 : Blo 1206420 29753999 := bstep (se 1 (by rfl) ⟨22315499, by rfl⟩ : syracuseStep 29753999 = 44630999) B44630999
theorem B13052137 : Blo 1206420 13052137 := bstep (se 2 (by rfl) ⟨4894551, by rfl⟩ : syracuseStep 13052137 = 9789103) B9789103
theorem B39692753 : Blo 1206420 39692753 := bstep (se 2 (by rfl) ⟨14884782, by rfl⟩ : syracuseStep 39692753 = 29769565) B29769565
theorem B1206875 : Blo 1206420 1206875 := bstep (se 1 (by rfl) ⟨905156, by rfl⟩ : syracuseStep 1206875 = 1810313) B1810313
theorem B1206943 : Blo 1206420 1206943 := bstep (se 1 (by rfl) ⟨905207, by rfl⟩ : syracuseStep 1206943 = 1810415) B1810415
theorem B1207023 : Blo 1206420 1207023 := bstep (se 1 (by rfl) ⟨905267, by rfl⟩ : syracuseStep 1207023 = 1810535) B1810535
theorem B11758715 : Blo 1206420 11758715 := bstep (se 1 (by rfl) ⟨8819036, by rfl⟩ : syracuseStep 11758715 = 17638073) B17638073
theorem B176147783 : Blo 1206420 176147783 := bstep (se 1 (by rfl) ⟨132110837, by rfl⟩ : syracuseStep 176147783 = 264221675) B264221675
theorem B10308971 : Blo 1206420 10308971 := bstep (se 1 (by rfl) ⟨7731728, by rfl⟩ : syracuseStep 10308971 = 15463457) B15463457
theorem B8704169 : Blo 1206420 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B2715839 : Blo 1206420 2715839 := bstep (se 1 (by rfl) ⟨2036879, by rfl⟩ : syracuseStep 2715839 = 4073759) B4073759
theorem B2290913 : Blo 1206420 2290913 := bstep (se 2 (by rfl) ⟨859092, by rfl⟩ : syracuseStep 2290913 = 1718185) B1718185
theorem B1766891 : Blo 1206420 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B30177319 : Blo 1206420 30177319 := bstep (se 1 (by rfl) ⟨22632989, by rfl⟩ : syracuseStep 30177319 = 45265979) B45265979
theorem B6191387 : Blo 1206420 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B13056983 : Blo 1206420 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B1810559 : Blo 1206420 1810559 := bstep (se 1 (by rfl) ⟨1357919, by rfl⟩ : syracuseStep 1810559 = 2715839) B2715839
theorem B4711709 : Blo 1206420 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B26461835 : Blo 1206420 26461835 := bstep (se 1 (by rfl) ⟨19846376, by rfl⟩ : syracuseStep 26461835 = 39692753) B39692753
theorem B5802779 : Blo 1206420 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B17402849 : Blo 1206420 17402849 := bstep (se 2 (by rfl) ⟨6526068, by rfl⟩ : syracuseStep 17402849 = 13052137) B13052137
theorem B19835999 : Blo 1206420 19835999 := bstep (se 1 (by rfl) ⟨14876999, by rfl⟩ : syracuseStep 19835999 = 29753999) B29753999
theorem B1527275 : Blo 1206420 1527275 := bstep (se 1 (by rfl) ⟨1145456, by rfl⟩ : syracuseStep 1527275 = 2290913) B2290913
theorem B8704655 : Blo 1206420 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B40236425 : Blo 1206420 40236425 := bstep (se 2 (by rfl) ⟨15088659, by rfl⟩ : syracuseStep 40236425 = 30177319) B30177319
theorem B4127591 : Blo 1206420 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B7839143 : Blo 1206420 7839143 := bstep (se 1 (by rfl) ⟨5879357, by rfl⟩ : syracuseStep 7839143 = 11758715) B11758715
theorem B117431855 : Blo 1206420 117431855 := bstep (se 1 (by rfl) ⟨88073891, by rfl⟩ : syracuseStep 117431855 = 176147783) B176147783
theorem B6872647 : Blo 1206420 6872647 := bstep (se 1 (by rfl) ⟨5154485, by rfl⟩ : syracuseStep 6872647 = 10308971) B10308971
theorem B4072733 : Blo 1206420 4072733 := bstep (se 3 (by rfl) ⟨763637, by rfl⟩ : syracuseStep 4072733 = 1527275) B1527275
theorem B3868519 : Blo 1206420 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B11601899 : Blo 1206420 11601899 := bstep (se 1 (by rfl) ⟨8701424, by rfl⟩ : syracuseStep 11601899 = 17402849) B17402849
theorem B13223999 : Blo 1206420 13223999 := bstep (se 1 (by rfl) ⟨9917999, by rfl⟩ : syracuseStep 13223999 = 19835999) B19835999
theorem B1207039 : Blo 1206420 1207039 := bstep (se 1 (by rfl) ⟨905279, by rfl⟩ : syracuseStep 1207039 = 1810559) B1810559
theorem B5803103 : Blo 1206420 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B26824283 : Blo 1206420 26824283 := bstep (se 1 (by rfl) ⟨20118212, by rfl⟩ : syracuseStep 26824283 = 40236425) B40236425
theorem B17641223 : Blo 1206420 17641223 := bstep (se 1 (by rfl) ⟨13230917, by rfl⟩ : syracuseStep 17641223 = 26461835) B26461835
theorem B9163529 : Blo 1206420 9163529 := bstep (se 2 (by rfl) ⟨3436323, by rfl⟩ : syracuseStep 9163529 = 6872647) B6872647
theorem B78287903 : Blo 1206420 78287903 := bstep (se 1 (by rfl) ⟨58715927, by rfl⟩ : syracuseStep 78287903 = 117431855) B117431855
theorem B12564557 : Blo 1206420 12564557 := bstep (se 3 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 12564557 = 4711709) B4711709
theorem B2751727 : Blo 1206420 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B5226095 : Blo 1206420 5226095 := bstep (se 1 (by rfl) ⟨3919571, by rfl⟩ : syracuseStep 5226095 = 7839143) B7839143
theorem B52191935 : Blo 1206420 52191935 := bstep (se 1 (by rfl) ⟨39143951, by rfl⟩ : syracuseStep 52191935 = 78287903) B78287903
theorem B7734599 : Blo 1206420 7734599 := bstep (se 1 (by rfl) ⟨5800949, by rfl⟩ : syracuseStep 7734599 = 11601899) B11601899
theorem B8815999 : Blo 1206420 8815999 := bstep (se 1 (by rfl) ⟨6611999, by rfl⟩ : syracuseStep 8815999 = 13223999) B13223999
theorem B3868735 : Blo 1206420 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B3484063 : Blo 1206420 3484063 := bstep (se 1 (by rfl) ⟨2613047, by rfl⟩ : syracuseStep 3484063 = 5226095) B5226095
theorem B2715155 : Blo 1206420 2715155 := bstep (se 1 (by rfl) ⟨2036366, by rfl⟩ : syracuseStep 2715155 = 4072733) B4072733
theorem B8376371 : Blo 1206420 8376371 := bstep (se 1 (by rfl) ⟨6282278, by rfl⟩ : syracuseStep 8376371 = 12564557) B12564557
theorem B5158025 : Blo 1206420 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B11760815 : Blo 1206420 11760815 := bstep (se 1 (by rfl) ⟨8820611, by rfl⟩ : syracuseStep 11760815 = 17641223) B17641223
theorem B6109019 : Blo 1206420 6109019 := bstep (se 1 (by rfl) ⟨4581764, by rfl⟩ : syracuseStep 6109019 = 9163529) B9163529
theorem B3668969 : Blo 1206420 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B17882855 : Blo 1206420 17882855 := bstep (se 1 (by rfl) ⟨13412141, by rfl⟩ : syracuseStep 17882855 = 26824283) B26824283
theorem B4072679 : Blo 1206420 4072679 := bstep (se 1 (by rfl) ⟨3054509, by rfl⟩ : syracuseStep 4072679 = 6109019) B6109019
theorem B18581669 : Blo 1206420 18581669 := bstep (se 4 (by rfl) ⟨1742031, by rfl⟩ : syracuseStep 18581669 = 3484063) B3484063
theorem B11921903 : Blo 1206420 11921903 := bstep (se 1 (by rfl) ⟨8941427, by rfl⟩ : syracuseStep 11921903 = 17882855) B17882855
theorem B31362173 : Blo 1206420 31362173 := bstep (se 3 (by rfl) ⟨5880407, by rfl⟩ : syracuseStep 31362173 = 11760815) B11760815
theorem B34794623 : Blo 1206420 34794623 := bstep (se 1 (by rfl) ⟨26095967, by rfl⟩ : syracuseStep 34794623 = 52191935) B52191935
theorem B5156399 : Blo 1206420 5156399 := bstep (se 1 (by rfl) ⟨3867299, by rfl⟩ : syracuseStep 5156399 = 7734599) B7734599
theorem B2445979 : Blo 1206420 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B5584247 : Blo 1206420 5584247 := bstep (se 1 (by rfl) ⟨4188185, by rfl⟩ : syracuseStep 5584247 = 8376371) B8376371
theorem B5158313 : Blo 1206420 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B3438683 : Blo 1206420 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B11754665 : Blo 1206420 11754665 := bstep (se 2 (by rfl) ⟨4407999, by rfl⟩ : syracuseStep 11754665 = 8815999) B8815999
theorem B1810103 : Blo 1206420 1810103 := bstep (se 1 (by rfl) ⟨1357577, by rfl⟩ : syracuseStep 1810103 = 2715155) B2715155
theorem B3261305 : Blo 1206420 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B12387779 : Blo 1206420 12387779 := bstep (se 1 (by rfl) ⟨9290834, by rfl⟩ : syracuseStep 12387779 = 18581669) B18581669
theorem B7947935 : Blo 1206420 7947935 := bstep (se 1 (by rfl) ⟨5960951, by rfl⟩ : syracuseStep 7947935 = 11921903) B11921903
theorem B20908115 : Blo 1206420 20908115 := bstep (se 1 (by rfl) ⟨15681086, by rfl⟩ : syracuseStep 20908115 = 31362173) B31362173
theorem B1206735 : Blo 1206420 1206735 := bstep (se 1 (by rfl) ⟨905051, by rfl⟩ : syracuseStep 1206735 = 1810103) B1810103
theorem B2715119 : Blo 1206420 2715119 := bstep (se 1 (by rfl) ⟨2036339, by rfl⟩ : syracuseStep 2715119 = 4072679) B4072679
theorem B3722831 : Blo 1206420 3722831 := bstep (se 1 (by rfl) ⟨2792123, by rfl⟩ : syracuseStep 3722831 = 5584247) B5584247
theorem B13750397 : Blo 1206420 13750397 := bstep (se 3 (by rfl) ⟨2578199, by rfl⟩ : syracuseStep 13750397 = 5156399) B5156399
theorem B23196415 : Blo 1206420 23196415 := bstep (se 1 (by rfl) ⟨17397311, by rfl⟩ : syracuseStep 23196415 = 34794623) B34794623
theorem B7836443 : Blo 1206420 7836443 := bstep (se 1 (by rfl) ⟨5877332, by rfl⟩ : syracuseStep 7836443 = 11754665) B11754665
theorem B3438875 : Blo 1206420 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B2292455 : Blo 1206420 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B9166931 : Blo 1206420 9166931 := bstep (se 1 (by rfl) ⟨6875198, by rfl⟩ : syracuseStep 9166931 = 13750397) B13750397
theorem B8258519 : Blo 1206420 8258519 := bstep (se 1 (by rfl) ⟨6193889, by rfl⟩ : syracuseStep 8258519 = 12387779) B12387779
theorem B2174203 : Blo 1206420 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B9170333 : Blo 1206420 9170333 := bstep (se 3 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 9170333 = 3438875) B3438875
theorem B30928553 : Blo 1206420 30928553 := bstep (se 2 (by rfl) ⟨11598207, by rfl⟩ : syracuseStep 30928553 = 23196415) B23196415
theorem B13938743 : Blo 1206420 13938743 := bstep (se 1 (by rfl) ⟨10454057, by rfl⟩ : syracuseStep 13938743 = 20908115) B20908115
theorem B1528303 : Blo 1206420 1528303 := bstep (se 1 (by rfl) ⟨1146227, by rfl⟩ : syracuseStep 1528303 = 2292455) B2292455
theorem B5224295 : Blo 1206420 5224295 := bstep (se 1 (by rfl) ⟨3918221, by rfl⟩ : syracuseStep 5224295 = 7836443) B7836443
theorem B5298623 : Blo 1206420 5298623 := bstep (se 1 (by rfl) ⟨3973967, by rfl⟩ : syracuseStep 5298623 = 7947935) B7947935
theorem B1810079 : Blo 1206420 1810079 := bstep (se 1 (by rfl) ⟨1357559, by rfl⟩ : syracuseStep 1810079 = 2715119) B2715119
theorem B2481887 : Blo 1206420 2481887 := bstep (se 1 (by rfl) ⟨1861415, by rfl⟩ : syracuseStep 2481887 = 3722831) B3722831
theorem B6111287 : Blo 1206420 6111287 := bstep (se 1 (by rfl) ⟨4583465, by rfl⟩ : syracuseStep 6111287 = 9166931) B9166931
theorem B5505679 : Blo 1206420 5505679 := bstep (se 1 (by rfl) ⟨4129259, by rfl⟩ : syracuseStep 5505679 = 8258519) B8258519
theorem B3532415 : Blo 1206420 3532415 := bstep (se 1 (by rfl) ⟨2649311, by rfl⟩ : syracuseStep 3532415 = 5298623) B5298623
theorem B6113555 : Blo 1206420 6113555 := bstep (se 1 (by rfl) ⟨4585166, by rfl⟩ : syracuseStep 6113555 = 9170333) B9170333
theorem B1206719 : Blo 1206420 1206719 := bstep (se 1 (by rfl) ⟨905039, by rfl⟩ : syracuseStep 1206719 = 1810079) B1810079
theorem B9292495 : Blo 1206420 9292495 := bstep (se 1 (by rfl) ⟨6969371, by rfl⟩ : syracuseStep 9292495 = 13938743) B13938743
theorem B13931453 : Blo 1206420 13931453 := bstep (se 3 (by rfl) ⟨2612147, by rfl⟩ : syracuseStep 13931453 = 5224295) B5224295
theorem B2037737 : Blo 1206420 2037737 := bstep (se 2 (by rfl) ⟨764151, by rfl⟩ : syracuseStep 2037737 = 1528303) B1528303
theorem B2898937 : Blo 1206420 2898937 := bstep (se 2 (by rfl) ⟨1087101, by rfl⟩ : syracuseStep 2898937 = 2174203) B2174203
theorem B20619035 : Blo 1206420 20619035 := bstep (se 1 (by rfl) ⟨15464276, by rfl⟩ : syracuseStep 20619035 = 30928553) B30928553
theorem B1654591 : Blo 1206420 1654591 := bstep (se 1 (by rfl) ⟨1240943, by rfl⟩ : syracuseStep 1654591 = 2481887) B2481887
theorem B7340905 : Blo 1206420 7340905 := bstep (se 2 (by rfl) ⟨2752839, by rfl⟩ : syracuseStep 7340905 = 5505679) B5505679
theorem B2206121 : Blo 1206420 2206121 := bstep (se 2 (by rfl) ⟨827295, by rfl⟩ : syracuseStep 2206121 = 1654591) B1654591
theorem B4074191 : Blo 1206420 4074191 := bstep (se 1 (by rfl) ⟨3055643, by rfl⟩ : syracuseStep 4074191 = 6111287) B6111287
theorem B12389993 : Blo 1206420 12389993 := bstep (se 2 (by rfl) ⟨4646247, by rfl⟩ : syracuseStep 12389993 = 9292495) B9292495
theorem B37679093 : Blo 1206420 37679093 := bstep (se 5 (by rfl) ⟨1766207, by rfl⟩ : syracuseStep 37679093 = 3532415) B3532415
theorem B4075703 : Blo 1206420 4075703 := bstep (se 1 (by rfl) ⟨3056777, by rfl⟩ : syracuseStep 4075703 = 6113555) B6113555
theorem B9287635 : Blo 1206420 9287635 := bstep (se 1 (by rfl) ⟨6965726, by rfl⟩ : syracuseStep 9287635 = 13931453) B13931453
theorem B1358491 : Blo 1206420 1358491 := bstep (se 1 (by rfl) ⟨1018868, by rfl⟩ : syracuseStep 1358491 = 2037737) B2037737
theorem B3865249 : Blo 1206420 3865249 := bstep (se 2 (by rfl) ⟨1449468, by rfl⟩ : syracuseStep 3865249 = 2898937) B2898937
theorem B13746023 : Blo 1206420 13746023 := bstep (se 1 (by rfl) ⟨10309517, by rfl⟩ : syracuseStep 13746023 = 20619035) B20619035
theorem B1811321 : Blo 1206420 1811321 := bstep (se 2 (by rfl) ⟨679245, by rfl⟩ : syracuseStep 1811321 = 1358491) B1358491
theorem B5882989 : Blo 1206420 5882989 := bstep (se 3 (by rfl) ⟨1103060, by rfl⟩ : syracuseStep 5882989 = 2206121) B2206121
theorem B8259995 : Blo 1206420 8259995 := bstep (se 1 (by rfl) ⟨6194996, by rfl⟩ : syracuseStep 8259995 = 12389993) B12389993
theorem B25119395 : Blo 1206420 25119395 := bstep (se 1 (by rfl) ⟨18839546, by rfl⟩ : syracuseStep 25119395 = 37679093) B37679093
theorem B20614661 : Blo 1206420 20614661 := bstep (se 4 (by rfl) ⟨1932624, by rfl⟩ : syracuseStep 20614661 = 3865249) B3865249
theorem B2716127 : Blo 1206420 2716127 := bstep (se 1 (by rfl) ⟨2037095, by rfl⟩ : syracuseStep 2716127 = 4074191) B4074191
theorem B9164015 : Blo 1206420 9164015 := bstep (se 1 (by rfl) ⟨6873011, by rfl⟩ : syracuseStep 9164015 = 13746023) B13746023
theorem B12383513 : Blo 1206420 12383513 := bstep (se 2 (by rfl) ⟨4643817, by rfl⟩ : syracuseStep 12383513 = 9287635) B9287635
theorem B2717135 : Blo 1206420 2717135 := bstep (se 1 (by rfl) ⟨2037851, by rfl⟩ : syracuseStep 2717135 = 4075703) B4075703
theorem B9787873 : Blo 1206420 9787873 := bstep (se 2 (by rfl) ⟨3670452, by rfl⟩ : syracuseStep 9787873 = 7340905) B7340905
theorem B1810751 : Blo 1206420 1810751 := bstep (se 1 (by rfl) ⟨1358063, by rfl⟩ : syracuseStep 1810751 = 2716127) B2716127
theorem B13050497 : Blo 1206420 13050497 := bstep (se 2 (by rfl) ⟨4893936, by rfl⟩ : syracuseStep 13050497 = 9787873) B9787873
theorem B1811423 : Blo 1206420 1811423 := bstep (se 1 (by rfl) ⟨1358567, by rfl⟩ : syracuseStep 1811423 = 2717135) B2717135
theorem B16746263 : Blo 1206420 16746263 := bstep (se 1 (by rfl) ⟨12559697, by rfl⟩ : syracuseStep 16746263 = 25119395) B25119395
theorem B1207547 : Blo 1206420 1207547 := bstep (se 1 (by rfl) ⟨905660, by rfl⟩ : syracuseStep 1207547 = 1811321) B1811321
theorem B7843985 : Blo 1206420 7843985 := bstep (se 2 (by rfl) ⟨2941494, by rfl⟩ : syracuseStep 7843985 = 5882989) B5882989
theorem B13743107 : Blo 1206420 13743107 := bstep (se 1 (by rfl) ⟨10307330, by rfl⟩ : syracuseStep 13743107 = 20614661) B20614661
theorem B6109343 : Blo 1206420 6109343 := bstep (se 1 (by rfl) ⟨4582007, by rfl⟩ : syracuseStep 6109343 = 9164015) B9164015
theorem B8255675 : Blo 1206420 8255675 := bstep (se 1 (by rfl) ⟨6191756, by rfl⟩ : syracuseStep 8255675 = 12383513) B12383513
theorem B22026653 : Blo 1206420 22026653 := bstep (se 3 (by rfl) ⟨4129997, by rfl⟩ : syracuseStep 22026653 = 8259995) B8259995
theorem B8700331 : Blo 1206420 8700331 := bstep (se 1 (by rfl) ⟨6525248, by rfl⟩ : syracuseStep 8700331 = 13050497) B13050497
theorem B4072895 : Blo 1206420 4072895 := bstep (se 1 (by rfl) ⟨3054671, by rfl⟩ : syracuseStep 4072895 = 6109343) B6109343
theorem B5229323 : Blo 1206420 5229323 := bstep (se 1 (by rfl) ⟨3921992, by rfl⟩ : syracuseStep 5229323 = 7843985) B7843985
theorem B1207167 : Blo 1206420 1207167 := bstep (se 1 (by rfl) ⟨905375, by rfl⟩ : syracuseStep 1207167 = 1810751) B1810751
theorem B1207615 : Blo 1206420 1207615 := bstep (se 1 (by rfl) ⟨905711, by rfl⟩ : syracuseStep 1207615 = 1811423) B1811423
theorem B9162071 : Blo 1206420 9162071 := bstep (se 1 (by rfl) ⟨6871553, by rfl⟩ : syracuseStep 9162071 = 13743107) B13743107
theorem B14684435 : Blo 1206420 14684435 := bstep (se 1 (by rfl) ⟨11013326, by rfl⟩ : syracuseStep 14684435 = 22026653) B22026653
theorem B11164175 : Blo 1206420 11164175 := bstep (se 1 (by rfl) ⟨8373131, by rfl⟩ : syracuseStep 11164175 = 16746263) B16746263
theorem B5503783 : Blo 1206420 5503783 := bstep (se 1 (by rfl) ⟨4127837, by rfl⟩ : syracuseStep 5503783 = 8255675) B8255675
theorem B9789623 : Blo 1206420 9789623 := bstep (se 1 (by rfl) ⟨7342217, by rfl⟩ : syracuseStep 9789623 = 14684435) B14684435
theorem B11600441 : Blo 1206420 11600441 := bstep (se 2 (by rfl) ⟨4350165, by rfl⟩ : syracuseStep 11600441 = 8700331) B8700331
theorem B2715263 : Blo 1206420 2715263 := bstep (se 1 (by rfl) ⟨2036447, by rfl⟩ : syracuseStep 2715263 = 4072895) B4072895
theorem B7442783 : Blo 1206420 7442783 := bstep (se 1 (by rfl) ⟨5582087, by rfl⟩ : syracuseStep 7442783 = 11164175) B11164175
theorem B3486215 : Blo 1206420 3486215 := bstep (se 1 (by rfl) ⟨2614661, by rfl⟩ : syracuseStep 3486215 = 5229323) B5229323
theorem B6108047 : Blo 1206420 6108047 := bstep (se 1 (by rfl) ⟨4581035, by rfl⟩ : syracuseStep 6108047 = 9162071) B9162071
theorem B7338377 : Blo 1206420 7338377 := bstep (se 2 (by rfl) ⟨2751891, by rfl⟩ : syracuseStep 7338377 = 5503783) B5503783
theorem B7733627 : Blo 1206420 7733627 := bstep (se 1 (by rfl) ⟨5800220, by rfl⟩ : syracuseStep 7733627 = 11600441) B11600441
theorem B4072031 : Blo 1206420 4072031 := bstep (se 1 (by rfl) ⟨3054023, by rfl⟩ : syracuseStep 4072031 = 6108047) B6108047
theorem B4892251 : Blo 1206420 4892251 := bstep (se 1 (by rfl) ⟨3669188, by rfl⟩ : syracuseStep 4892251 = 7338377) B7338377
theorem B6526415 : Blo 1206420 6526415 := bstep (se 1 (by rfl) ⟨4894811, by rfl⟩ : syracuseStep 6526415 = 9789623) B9789623
theorem B4961855 : Blo 1206420 4961855 := bstep (se 1 (by rfl) ⟨3721391, by rfl⟩ : syracuseStep 4961855 = 7442783) B7442783
theorem B2324143 : Blo 1206420 2324143 := bstep (se 1 (by rfl) ⟨1743107, by rfl⟩ : syracuseStep 2324143 = 3486215) B3486215
theorem B1810175 : Blo 1206420 1810175 := bstep (se 1 (by rfl) ⟨1357631, by rfl⟩ : syracuseStep 1810175 = 2715263) B2715263
theorem B4350943 : Blo 1206420 4350943 := bstep (se 1 (by rfl) ⟨3263207, by rfl⟩ : syracuseStep 4350943 = 6526415) B6526415
theorem B13231613 : Blo 1206420 13231613 := bstep (se 3 (by rfl) ⟨2480927, by rfl⟩ : syracuseStep 13231613 = 4961855) B4961855
theorem B6523001 : Blo 1206420 6523001 := bstep (se 2 (by rfl) ⟨2446125, by rfl⟩ : syracuseStep 6523001 = 4892251) B4892251
theorem B3098857 : Blo 1206420 3098857 := bstep (se 2 (by rfl) ⟨1162071, by rfl⟩ : syracuseStep 3098857 = 2324143) B2324143
theorem B1206783 : Blo 1206420 1206783 := bstep (se 1 (by rfl) ⟨905087, by rfl⟩ : syracuseStep 1206783 = 1810175) B1810175
theorem B5155751 : Blo 1206420 5155751 := bstep (se 1 (by rfl) ⟨3866813, by rfl⟩ : syracuseStep 5155751 = 7733627) B7733627
theorem B2714687 : Blo 1206420 2714687 := bstep (se 1 (by rfl) ⟨2036015, by rfl⟩ : syracuseStep 2714687 = 4072031) B4072031
theorem B5801257 : Blo 1206420 5801257 := bstep (se 2 (by rfl) ⟨2175471, by rfl⟩ : syracuseStep 5801257 = 4350943) B4350943
theorem B35284301 : Blo 1206420 35284301 := bstep (se 3 (by rfl) ⟨6615806, by rfl⟩ : syracuseStep 35284301 = 13231613) B13231613
theorem B4131809 : Blo 1206420 4131809 := bstep (se 2 (by rfl) ⟨1549428, by rfl⟩ : syracuseStep 4131809 = 3098857) B3098857
theorem B3437167 : Blo 1206420 3437167 := bstep (se 1 (by rfl) ⟨2577875, by rfl⟩ : syracuseStep 3437167 = 5155751) B5155751
theorem B4348667 : Blo 1206420 4348667 := bstep (se 1 (by rfl) ⟨3261500, by rfl⟩ : syracuseStep 4348667 = 6523001) B6523001
theorem B1809791 : Blo 1206420 1809791 := bstep (se 1 (by rfl) ⟨1357343, by rfl⟩ : syracuseStep 1809791 = 2714687) B2714687
theorem B7735009 : Blo 1206420 7735009 := bstep (se 2 (by rfl) ⟨2900628, by rfl⟩ : syracuseStep 7735009 = 5801257) B5801257
theorem B2754539 : Blo 1206420 2754539 := bstep (se 1 (by rfl) ⟨2065904, by rfl⟩ : syracuseStep 2754539 = 4131809) B4131809
theorem B1206527 : Blo 1206420 1206527 := bstep (se 1 (by rfl) ⟨904895, by rfl⟩ : syracuseStep 1206527 = 1809791) B1809791
theorem B4582889 : Blo 1206420 4582889 := bstep (se 2 (by rfl) ⟨1718583, by rfl⟩ : syracuseStep 4582889 = 3437167) B3437167
theorem B23522867 : Blo 1206420 23522867 := bstep (se 1 (by rfl) ⟨17642150, by rfl⟩ : syracuseStep 23522867 = 35284301) B35284301
theorem B11596445 : Blo 1206420 11596445 := bstep (se 3 (by rfl) ⟨2174333, by rfl⟩ : syracuseStep 11596445 = 4348667) B4348667
theorem B1836359 : Blo 1206420 1836359 := bstep (se 1 (by rfl) ⟨1377269, by rfl⟩ : syracuseStep 1836359 = 2754539) B2754539
theorem B7730963 : Blo 1206420 7730963 := bstep (se 1 (by rfl) ⟨5798222, by rfl⟩ : syracuseStep 7730963 = 11596445) B11596445
theorem B250910581 : Blo 1206420 250910581 := bstep (se 5 (by rfl) ⟨11761433, by rfl⟩ : syracuseStep 250910581 = 23522867) B23522867
theorem B10313345 : Blo 1206420 10313345 := bstep (se 2 (by rfl) ⟨3867504, by rfl⟩ : syracuseStep 10313345 = 7735009) B7735009
theorem B3055259 : Blo 1206420 3055259 := bstep (se 1 (by rfl) ⟨2291444, by rfl⟩ : syracuseStep 3055259 = 4582889) B4582889
theorem B5153975 : Blo 1206420 5153975 := bstep (se 1 (by rfl) ⟨3865481, by rfl⟩ : syracuseStep 5153975 = 7730963) B7730963
theorem B6875563 : Blo 1206420 6875563 := bstep (se 1 (by rfl) ⟨5156672, by rfl⟩ : syracuseStep 6875563 = 10313345) B10313345
theorem B334547441 : Blo 1206420 334547441 := bstep (se 2 (by rfl) ⟨125455290, by rfl⟩ : syracuseStep 334547441 = 250910581) B250910581
theorem B1224239 : Blo 1206420 1224239 := bstep (se 1 (by rfl) ⟨918179, by rfl⟩ : syracuseStep 1224239 = 1836359) B1836359
theorem B2036839 : Blo 1206420 2036839 := bstep (se 1 (by rfl) ⟨1527629, by rfl⟩ : syracuseStep 2036839 = 3055259) B3055259
theorem B9167417 : Blo 1206420 9167417 := bstep (se 2 (by rfl) ⟨3437781, by rfl⟩ : syracuseStep 9167417 = 6875563) B6875563
theorem B3435983 : Blo 1206420 3435983 := bstep (se 1 (by rfl) ⟨2576987, by rfl⟩ : syracuseStep 3435983 = 5153975) B5153975
theorem B3264637 : Blo 1206420 3264637 := bstep (se 3 (by rfl) ⟨612119, by rfl⟩ : syracuseStep 3264637 = 1224239) B1224239
theorem B2715785 : Blo 1206420 2715785 := bstep (se 2 (by rfl) ⟨1018419, by rfl⟩ : syracuseStep 2715785 = 2036839) B2036839
theorem B223031627 : Blo 1206420 223031627 := bstep (se 1 (by rfl) ⟨167273720, by rfl⟩ : syracuseStep 223031627 = 334547441) B334547441
theorem B1810523 : Blo 1206420 1810523 := bstep (se 1 (by rfl) ⟨1357892, by rfl⟩ : syracuseStep 1810523 = 2715785) B2715785
theorem B6111611 : Blo 1206420 6111611 := bstep (se 1 (by rfl) ⟨4583708, by rfl⟩ : syracuseStep 6111611 = 9167417) B9167417
theorem B4352849 : Blo 1206420 4352849 := bstep (se 2 (by rfl) ⟨1632318, by rfl⟩ : syracuseStep 4352849 = 3264637) B3264637
theorem B148687751 : Blo 1206420 148687751 := bstep (se 1 (by rfl) ⟨111515813, by rfl⟩ : syracuseStep 148687751 = 223031627) B223031627
theorem B2290655 : Blo 1206420 2290655 := bstep (se 1 (by rfl) ⟨1717991, by rfl⟩ : syracuseStep 2290655 = 3435983) B3435983
theorem B2901899 : Blo 1206420 2901899 := bstep (se 1 (by rfl) ⟨2176424, by rfl⟩ : syracuseStep 2901899 = 4352849) B4352849
theorem B99125167 : Blo 1206420 99125167 := bstep (se 1 (by rfl) ⟨74343875, by rfl⟩ : syracuseStep 99125167 = 148687751) B148687751
theorem B1207015 : Blo 1206420 1207015 := bstep (se 1 (by rfl) ⟨905261, by rfl⟩ : syracuseStep 1207015 = 1810523) B1810523
theorem B4074407 : Blo 1206420 4074407 := bstep (se 1 (by rfl) ⟨3055805, by rfl⟩ : syracuseStep 4074407 = 6111611) B6111611
theorem B1527103 : Blo 1206420 1527103 := bstep (se 1 (by rfl) ⟨1145327, by rfl⟩ : syracuseStep 1527103 = 2290655) B2290655
theorem B1934599 : Blo 1206420 1934599 := bstep (se 1 (by rfl) ⟨1450949, by rfl⟩ : syracuseStep 1934599 = 2901899) B2901899
theorem B2036137 : Blo 1206420 2036137 := bstep (se 2 (by rfl) ⟨763551, by rfl⟩ : syracuseStep 2036137 = 1527103) B1527103
theorem B2716271 : Blo 1206420 2716271 := bstep (se 1 (by rfl) ⟨2037203, by rfl⟩ : syracuseStep 2716271 = 4074407) B4074407
theorem B132166889 : Blo 1206420 132166889 := bstep (se 2 (by rfl) ⟨49562583, by rfl⟩ : syracuseStep 132166889 = 99125167) B99125167
theorem B1810847 : Blo 1206420 1810847 := bstep (se 1 (by rfl) ⟨1358135, by rfl⟩ : syracuseStep 1810847 = 2716271) B2716271
theorem B2714849 : Blo 1206420 2714849 := bstep (se 2 (by rfl) ⟨1018068, by rfl⟩ : syracuseStep 2714849 = 2036137) B2036137
theorem B88111259 : Blo 1206420 88111259 := bstep (se 1 (by rfl) ⟨66083444, by rfl⟩ : syracuseStep 88111259 = 132166889) B132166889
theorem B2579465 : Blo 1206420 2579465 := bstep (se 2 (by rfl) ⟨967299, by rfl⟩ : syracuseStep 2579465 = 1934599) B1934599
theorem B1207231 : Blo 1206420 1207231 := bstep (se 1 (by rfl) ⟨905423, by rfl⟩ : syracuseStep 1207231 = 1810847) B1810847
theorem B58740839 : Blo 1206420 58740839 := bstep (se 1 (by rfl) ⟨44055629, by rfl⟩ : syracuseStep 58740839 = 88111259) B88111259
theorem B1719643 : Blo 1206420 1719643 := bstep (se 1 (by rfl) ⟨1289732, by rfl⟩ : syracuseStep 1719643 = 2579465) B2579465
theorem B1809899 : Blo 1206420 1809899 := bstep (se 1 (by rfl) ⟨1357424, by rfl⟩ : syracuseStep 1809899 = 2714849) B2714849
theorem B1206599 : Blo 1206420 1206599 := bstep (se 1 (by rfl) ⟨904949, by rfl⟩ : syracuseStep 1206599 = 1809899) B1809899
theorem B39160559 : Blo 1206420 39160559 := bstep (se 1 (by rfl) ⟨29370419, by rfl⟩ : syracuseStep 39160559 = 58740839) B58740839
theorem B2292857 : Blo 1206420 2292857 := bstep (se 2 (by rfl) ⟨859821, by rfl⟩ : syracuseStep 2292857 = 1719643) B1719643
theorem B1528571 : Blo 1206420 1528571 := bstep (se 1 (by rfl) ⟨1146428, by rfl⟩ : syracuseStep 1528571 = 2292857) B2292857
theorem B26107039 : Blo 1206420 26107039 := bstep (se 1 (by rfl) ⟨19580279, by rfl⟩ : syracuseStep 26107039 = 39160559) B39160559
theorem B34809385 : Blo 1206420 34809385 := bstep (se 2 (by rfl) ⟨13053519, by rfl⟩ : syracuseStep 34809385 = 26107039) B26107039
theorem B4076189 : Blo 1206420 4076189 := bstep (se 3 (by rfl) ⟨764285, by rfl⟩ : syracuseStep 4076189 = 1528571) B1528571
theorem B46412513 : Blo 1206420 46412513 := bstep (se 2 (by rfl) ⟨17404692, by rfl⟩ : syracuseStep 46412513 = 34809385) B34809385
theorem B2717459 : Blo 1206420 2717459 := bstep (se 1 (by rfl) ⟨2038094, by rfl⟩ : syracuseStep 2717459 = 4076189) B4076189
theorem B30941675 : Blo 1206420 30941675 := bstep (se 1 (by rfl) ⟨23206256, by rfl⟩ : syracuseStep 30941675 = 46412513) B46412513
theorem B1811639 : Blo 1206420 1811639 := bstep (se 1 (by rfl) ⟨1358729, by rfl⟩ : syracuseStep 1811639 = 2717459) B2717459
theorem B20627783 : Blo 1206420 20627783 := bstep (se 1 (by rfl) ⟨15470837, by rfl⟩ : syracuseStep 20627783 = 30941675) B30941675
theorem B1207759 : Blo 1206420 1207759 := bstep (se 1 (by rfl) ⟨905819, by rfl⟩ : syracuseStep 1207759 = 1811639) B1811639
theorem B13751855 : Blo 1206420 13751855 := bstep (se 1 (by rfl) ⟨10313891, by rfl⟩ : syracuseStep 13751855 = 20627783) B20627783
theorem B9167903 : Blo 1206420 9167903 := bstep (se 1 (by rfl) ⟨6875927, by rfl⟩ : syracuseStep 9167903 = 13751855) B13751855
theorem B6111935 : Blo 1206420 6111935 := bstep (se 1 (by rfl) ⟨4583951, by rfl⟩ : syracuseStep 6111935 = 9167903) B9167903
theorem B4074623 : Blo 1206420 4074623 := bstep (se 1 (by rfl) ⟨3055967, by rfl⟩ : syracuseStep 4074623 = 6111935) B6111935
theorem B2716415 : Blo 1206420 2716415 := bstep (se 1 (by rfl) ⟨2037311, by rfl⟩ : syracuseStep 2716415 = 4074623) B4074623
theorem B1810943 : Blo 1206420 1810943 := bstep (se 1 (by rfl) ⟨1358207, by rfl⟩ : syracuseStep 1810943 = 2716415) B2716415
theorem B1207295 : Blo 1206420 1207295 := bstep (se 1 (by rfl) ⟨905471, by rfl⟩ : syracuseStep 1207295 = 1810943) B1810943

theorem C0 (j : ℕ) (h1 : 301605 ≤ j) (h2 : j ≤ 301979) : Blo 1206420 (4 * j + 3) := by
  interval_cases j
  · exact B1206423
  · exact B1206427
  · exact B1206431
  · exact B1206435
  · exact B1206439
  · exact B1206443
  · exact B1206447
  · exact B1206451
  · exact B1206455
  · exact B1206459
  · exact B1206463
  · exact B1206467
  · exact B1206471
  · exact B1206475
  · exact B1206479
  · exact B1206483
  · exact B1206487
  · exact B1206491
  · exact B1206495
  · exact B1206499
  · exact B1206503
  · exact B1206507
  · exact B1206511
  · exact B1206515
  · exact B1206519
  · exact B1206523
  · exact B1206527
  · exact B1206531
  · exact B1206535
  · exact B1206539
  · exact B1206543
  · exact B1206547
  · exact B1206551
  · exact B1206555
  · exact B1206559
  · exact B1206563
  · exact B1206567
  · exact B1206571
  · exact B1206575
  · exact B1206579
  · exact B1206583
  · exact B1206587
  · exact B1206591
  · exact B1206595
  · exact B1206599
  · exact B1206603
  · exact B1206607
  · exact B1206611
  · exact B1206615
  · exact B1206619
  · exact B1206623
  · exact B1206627
  · exact B1206631
  · exact B1206635
  · exact B1206639
  · exact B1206643
  · exact B1206647
  · exact B1206651
  · exact B1206655
  · exact B1206659
  · exact B1206663
  · exact B1206667
  · exact B1206671
  · exact B1206675
  · exact B1206679
  · exact B1206683
  · exact B1206687
  · exact B1206691
  · exact B1206695
  · exact B1206699
  · exact B1206703
  · exact B1206707
  · exact B1206711
  · exact B1206715
  · exact B1206719
  · exact B1206723
  · exact B1206727
  · exact B1206731
  · exact B1206735
  · exact B1206739
  · exact B1206743
  · exact B1206747
  · exact B1206751
  · exact B1206755
  · exact B1206759
  · exact B1206763
  · exact B1206767
  · exact B1206771
  · exact B1206775
  · exact B1206779
  · exact B1206783
  · exact B1206787
  · exact B1206791
  · exact B1206795
  · exact B1206799
  · exact B1206803
  · exact B1206807
  · exact B1206811
  · exact B1206815
  · exact B1206819
  · exact B1206823
  · exact B1206827
  · exact B1206831
  · exact B1206835
  · exact B1206839
  · exact B1206843
  · exact B1206847
  · exact B1206851
  · exact B1206855
  · exact B1206859
  · exact B1206863
  · exact B1206867
  · exact B1206871
  · exact B1206875
  · exact B1206879
  · exact B1206883
  · exact B1206887
  · exact B1206891
  · exact B1206895
  · exact B1206899
  · exact B1206903
  · exact B1206907
  · exact B1206911
  · exact B1206915
  · exact B1206919
  · exact B1206923
  · exact B1206927
  · exact B1206931
  · exact B1206935
  · exact B1206939
  · exact B1206943
  · exact B1206947
  · exact B1206951
  · exact B1206955
  · exact B1206959
  · exact B1206963
  · exact B1206967
  · exact B1206971
  · exact B1206975
  · exact B1206979
  · exact B1206983
  · exact B1206987
  · exact B1206991
  · exact B1206995
  · exact B1206999
  · exact B1207003
  · exact B1207007
  · exact B1207011
  · exact B1207015
  · exact B1207019
  · exact B1207023
  · exact B1207027
  · exact B1207031
  · exact B1207035
  · exact B1207039
  · exact B1207043
  · exact B1207047
  · exact B1207051
  · exact B1207055
  · exact B1207059
  · exact B1207063
  · exact B1207067
  · exact B1207071
  · exact B1207075
  · exact B1207079
  · exact B1207083
  · exact B1207087
  · exact B1207091
  · exact B1207095
  · exact B1207099
  · exact B1207103
  · exact B1207107
  · exact B1207111
  · exact B1207115
  · exact B1207119
  · exact B1207123
  · exact B1207127
  · exact B1207131
  · exact B1207135
  · exact B1207139
  · exact B1207143
  · exact B1207147
  · exact B1207151
  · exact B1207155
  · exact B1207159
  · exact B1207163
  · exact B1207167
  · exact B1207171
  · exact B1207175
  · exact B1207179
  · exact B1207183
  · exact B1207187
  · exact B1207191
  · exact B1207195
  · exact B1207199
  · exact B1207203
  · exact B1207207
  · exact B1207211
  · exact B1207215
  · exact B1207219
  · exact B1207223
  · exact B1207227
  · exact B1207231
  · exact B1207235
  · exact B1207239
  · exact B1207243
  · exact B1207247
  · exact B1207251
  · exact B1207255
  · exact B1207259
  · exact B1207263
  · exact B1207267
  · exact B1207271
  · exact B1207275
  · exact B1207279
  · exact B1207283
  · exact B1207287
  · exact B1207291
  · exact B1207295
  · exact B1207299
  · exact B1207303
  · exact B1207307
  · exact B1207311
  · exact B1207315
  · exact B1207319
  · exact B1207323
  · exact B1207327
  · exact B1207331
  · exact B1207335
  · exact B1207339
  · exact B1207343
  · exact B1207347
  · exact B1207351
  · exact B1207355
  · exact B1207359
  · exact B1207363
  · exact B1207367
  · exact B1207371
  · exact B1207375
  · exact B1207379
  · exact B1207383
  · exact B1207387
  · exact B1207391
  · exact B1207395
  · exact B1207399
  · exact B1207403
  · exact B1207407
  · exact B1207411
  · exact B1207415
  · exact B1207419
  · exact B1207423
  · exact B1207427
  · exact B1207431
  · exact B1207435
  · exact B1207439
  · exact B1207443
  · exact B1207447
  · exact B1207451
  · exact B1207455
  · exact B1207459
  · exact B1207463
  · exact B1207467
  · exact B1207471
  · exact B1207475
  · exact B1207479
  · exact B1207483
  · exact B1207487
  · exact B1207491
  · exact B1207495
  · exact B1207499
  · exact B1207503
  · exact B1207507
  · exact B1207511
  · exact B1207515
  · exact B1207519
  · exact B1207523
  · exact B1207527
  · exact B1207531
  · exact B1207535
  · exact B1207539
  · exact B1207543
  · exact B1207547
  · exact B1207551
  · exact B1207555
  · exact B1207559
  · exact B1207563
  · exact B1207567
  · exact B1207571
  · exact B1207575
  · exact B1207579
  · exact B1207583
  · exact B1207587
  · exact B1207591
  · exact B1207595
  · exact B1207599
  · exact B1207603
  · exact B1207607
  · exact B1207611
  · exact B1207615
  · exact B1207619
  · exact B1207623
  · exact B1207627
  · exact B1207631
  · exact B1207635
  · exact B1207639
  · exact B1207643
  · exact B1207647
  · exact B1207651
  · exact B1207655
  · exact B1207659
  · exact B1207663
  · exact B1207667
  · exact B1207671
  · exact B1207675
  · exact B1207679
  · exact B1207683
  · exact B1207687
  · exact B1207691
  · exact B1207695
  · exact B1207699
  · exact B1207703
  · exact B1207707
  · exact B1207711
  · exact B1207715
  · exact B1207719
  · exact B1207723
  · exact B1207727
  · exact B1207731
  · exact B1207735
  · exact B1207739
  · exact B1207743
  · exact B1207747
  · exact B1207751
  · exact B1207755
  · exact B1207759
  · exact B1207763
  · exact B1207767
  · exact B1207771
  · exact B1207775
  · exact B1207779
  · exact B1207783
  · exact B1207787
  · exact B1207791
  · exact B1207795
  · exact B1207799
  · exact B1207803
  · exact B1207807
  · exact B1207811
  · exact B1207815
  · exact B1207819
  · exact B1207823
  · exact B1207827
  · exact B1207831
  · exact B1207835
  · exact B1207839
  · exact B1207843
  · exact B1207847
  · exact B1207851
  · exact B1207855
  · exact B1207859
  · exact B1207863
  · exact B1207867
  · exact B1207871
  · exact B1207875
  · exact B1207879
  · exact B1207883
  · exact B1207887
  · exact B1207891
  · exact B1207895
  · exact B1207899
  · exact B1207903
  · exact B1207907
  · exact B1207911
  · exact B1207915
  · exact B1207919

theorem solution (m : ℕ) (hlo : 1206420 ≤ m) (hhi : m ≤ 1207920) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 301605 ≤ j := by omega
    have hj2 : j ≤ 301979 := by omega
    have hb : Blo 1206420 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
