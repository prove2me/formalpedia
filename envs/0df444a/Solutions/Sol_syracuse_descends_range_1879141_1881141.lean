-- Prove2me | solution 1 for syracuse_descends_range_1879141_1881141
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:17:16.127188+00:00
-- url     : https://prove2.me/submissions/cd9d4ef4-e386-4c49-b51a-2c262214dc65

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


theorem B68591701 : Blo 1879141 68591701 := bbase (se 8 (by rfl) ⟨401904, by rfl⟩ : syracuseStep 68591701 = 803809) (by norm_num)
theorem B4759661 : Blo 1879141 4759661 := bbase (se 3 (by rfl) ⟨892436, by rfl⟩ : syracuseStep 4759661 = 1784873) (by norm_num)
theorem B8028341 : Blo 1879141 8028341 := bbase (se 5 (by rfl) ⟨376328, by rfl⟩ : syracuseStep 8028341 = 752657) (by norm_num)
theorem B2859205 : Blo 1879141 2859205 := bbase (se 4 (by rfl) ⟨268050, by rfl⟩ : syracuseStep 2859205 = 536101) (by norm_num)
theorem B7135573 : Blo 1879141 7135573 := bbase (se 10 (by rfl) ⟨10452, by rfl⟩ : syracuseStep 7135573 = 20905) (by norm_num)
theorem B6021461 : Blo 1879141 6021461 := bbase (se 10 (by rfl) ⟨8820, by rfl⟩ : syracuseStep 6021461 = 17641) (by norm_num)
theorem B2007389 : Blo 1879141 2007389 := bbase (se 3 (by rfl) ⟨376385, by rfl⟩ : syracuseStep 2007389 = 752771) (by norm_num)
theorem B4014461 : Blo 1879141 4014461 := bbase (se 3 (by rfl) ⟨752711, by rfl⟩ : syracuseStep 4014461 = 1505423) (by norm_num)
theorem B2007461 : Blo 1879141 2007461 := bbase (se 4 (by rfl) ⟨188199, by rfl⟩ : syracuseStep 2007461 = 376399) (by norm_num)
theorem B4760005 : Blo 1879141 4760005 := bbase (se 4 (by rfl) ⟨446250, by rfl⟩ : syracuseStep 4760005 = 892501) (by norm_num)
theorem B6775285 : Blo 1879141 6775285 := bbase (se 5 (by rfl) ⟨317591, by rfl⟩ : syracuseStep 6775285 = 635183) (by norm_num)
theorem B9519605 : Blo 1879141 9519605 := bbase (se 5 (by rfl) ⟨446231, by rfl⟩ : syracuseStep 9519605 = 892463) (by norm_num)
theorem B2114041 : Blo 1879141 2114041 := bbase (se 2 (by rfl) ⟨792765, by rfl⟩ : syracuseStep 2114041 = 1585531) (by norm_num)
theorem B2114077 : Blo 1879141 2114077 := bbase (se 3 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 2114077 = 792779) (by norm_num)
theorem B4760117 : Blo 1879141 4760117 := bbase (se 5 (by rfl) ⟨223130, by rfl⟩ : syracuseStep 4760117 = 446261) (by norm_num)
theorem B2114113 : Blo 1879141 2114113 := bbase (se 2 (by rfl) ⟨792792, by rfl⟩ : syracuseStep 2114113 = 1585585) (by norm_num)
theorem B2646605 : Blo 1879141 2646605 := bbase (se 3 (by rfl) ⟨496238, by rfl⟩ : syracuseStep 2646605 = 992477) (by norm_num)
theorem B1884749 : Blo 1879141 1884749 := bbase (se 3 (by rfl) ⟨353390, by rfl⟩ : syracuseStep 1884749 = 706781) (by norm_num)
theorem B4891229 : Blo 1879141 4891229 := bbase (se 3 (by rfl) ⟨917105, by rfl⟩ : syracuseStep 4891229 = 1834211) (by norm_num)
theorem B2007649 : Blo 1879141 2007649 := bbase (se 2 (by rfl) ⟨752868, by rfl⟩ : syracuseStep 2007649 = 1505737) (by norm_num)
theorem B2114149 : Blo 1879141 2114149 := bbase (se 4 (by rfl) ⟨198201, by rfl⟩ : syracuseStep 2114149 = 396403) (by norm_num)
theorem B7135877 : Blo 1879141 7135877 := bbase (se 4 (by rfl) ⟨668988, by rfl⟩ : syracuseStep 7135877 = 1337977) (by norm_num)
theorem B2114185 : Blo 1879141 2114185 := bbase (se 2 (by rfl) ⟨792819, by rfl⟩ : syracuseStep 2114185 = 1585639) (by norm_num)
theorem B2540197 : Blo 1879141 2540197 := bbase (se 4 (by rfl) ⟨238143, by rfl⟩ : syracuseStep 2540197 = 476287) (by norm_num)
theorem B2818733 : Blo 1879141 2818733 := bbase (se 3 (by rfl) ⟨528512, by rfl⟩ : syracuseStep 2818733 = 1057025) (by norm_num)
theorem B2114221 : Blo 1879141 2114221 := bbase (se 3 (by rfl) ⟨396416, by rfl⟩ : syracuseStep 2114221 = 792833) (by norm_num)
theorem B2818757 : Blo 1879141 2818757 := bbase (se 4 (by rfl) ⟨264258, by rfl⟩ : syracuseStep 2818757 = 528517) (by norm_num)
theorem B2114257 : Blo 1879141 2114257 := bbase (se 2 (by rfl) ⟨792846, by rfl⟩ : syracuseStep 2114257 = 1585693) (by norm_num)
theorem B2818781 : Blo 1879141 2818781 := bbase (se 3 (by rfl) ⟨528521, by rfl⟩ : syracuseStep 2818781 = 1057043) (by norm_num)
theorem B2818805 : Blo 1879141 2818805 := bbase (se 5 (by rfl) ⟨132131, by rfl⟩ : syracuseStep 2818805 = 264263) (by norm_num)
theorem B2114293 : Blo 1879141 2114293 := bbase (se 5 (by rfl) ⟨99107, by rfl⟩ : syracuseStep 2114293 = 198215) (by norm_num)
theorem B4760309 : Blo 1879141 4760309 := bbase (se 5 (by rfl) ⟨223139, by rfl⟩ : syracuseStep 4760309 = 446279) (by norm_num)
theorem B2818829 : Blo 1879141 2818829 := bbase (se 3 (by rfl) ⟨528530, by rfl⟩ : syracuseStep 2818829 = 1057061) (by norm_num)
theorem B5079829 : Blo 1879141 5079829 := bbase (se 6 (by rfl) ⟨119058, by rfl⟩ : syracuseStep 5079829 = 238117) (by norm_num)
theorem B2114329 : Blo 1879141 2114329 := bbase (se 2 (by rfl) ⟨792873, by rfl⟩ : syracuseStep 2114329 = 1585747) (by norm_num)
theorem B2007833 : Blo 1879141 2007833 := bbase (se 2 (by rfl) ⟨752937, by rfl⟩ : syracuseStep 2007833 = 1505875) (by norm_num)
theorem B3171109 : Blo 1879141 3171109 := bbase (se 4 (by rfl) ⟨297291, by rfl⟩ : syracuseStep 3171109 = 594583) (by norm_num)
theorem B2818853 : Blo 1879141 2818853 := bbase (se 4 (by rfl) ⟨264267, by rfl⟩ : syracuseStep 2818853 = 528535) (by norm_num)
theorem B6275893 : Blo 1879141 6275893 := bbase (se 5 (by rfl) ⟨294182, by rfl⟩ : syracuseStep 6275893 = 588365) (by norm_num)
theorem B2818877 : Blo 1879141 2818877 := bbase (se 3 (by rfl) ⟨528539, by rfl⟩ : syracuseStep 2818877 = 1057079) (by norm_num)
theorem B2114365 : Blo 1879141 2114365 := bbase (se 3 (by rfl) ⟨396443, by rfl⟩ : syracuseStep 2114365 = 792887) (by norm_num)
theorem B2818901 : Blo 1879141 2818901 := bbase (se 9 (by rfl) ⟨8258, by rfl⟩ : syracuseStep 2818901 = 16517) (by norm_num)
theorem B6021973 : Blo 1879141 6021973 := bbase (se 9 (by rfl) ⟨17642, by rfl⟩ : syracuseStep 6021973 = 35285) (by norm_num)
theorem B2114401 : Blo 1879141 2114401 := bbase (se 2 (by rfl) ⟨792900, by rfl⟩ : syracuseStep 2114401 = 1585801) (by norm_num)
theorem B2818925 : Blo 1879141 2818925 := bbase (se 3 (by rfl) ⟨528548, by rfl⟩ : syracuseStep 2818925 = 1057097) (by norm_num)
theorem B3171197 : Blo 1879141 3171197 := bbase (se 3 (by rfl) ⟨594599, by rfl⟩ : syracuseStep 3171197 = 1189199) (by norm_num)
theorem B2540413 : Blo 1879141 2540413 := bbase (se 3 (by rfl) ⟨476327, by rfl⟩ : syracuseStep 2540413 = 952655) (by norm_num)
theorem B2818949 : Blo 1879141 2818949 := bbase (se 4 (by rfl) ⟨264276, by rfl⟩ : syracuseStep 2818949 = 528553) (by norm_num)
theorem B2114437 : Blo 1879141 2114437 := bbase (se 4 (by rfl) ⟨198228, by rfl⟩ : syracuseStep 2114437 = 396457) (by norm_num)
theorem B2818973 : Blo 1879141 2818973 := bbase (se 3 (by rfl) ⟨528557, by rfl⟩ : syracuseStep 2818973 = 1057115) (by norm_num)
theorem B2114473 : Blo 1879141 2114473 := bbase (se 2 (by rfl) ⟨792927, by rfl⟩ : syracuseStep 2114473 = 1585855) (by norm_num)
theorem B2818997 : Blo 1879141 2818997 := bbase (se 5 (by rfl) ⟨132140, by rfl⟩ : syracuseStep 2818997 = 264281) (by norm_num)
theorem B2540477 : Blo 1879141 2540477 := bbase (se 3 (by rfl) ⟨476339, by rfl⟩ : syracuseStep 2540477 = 952679) (by norm_num)
theorem B2819021 : Blo 1879141 2819021 := bbase (se 3 (by rfl) ⟨528566, by rfl⟩ : syracuseStep 2819021 = 1057133) (by norm_num)
theorem B2114509 : Blo 1879141 2114509 := bbase (se 3 (by rfl) ⟨396470, by rfl⟩ : syracuseStep 2114509 = 792941) (by norm_num)
theorem B32990165 : Blo 1879141 32990165 := bbase (se 7 (by rfl) ⟨386603, by rfl⟩ : syracuseStep 32990165 = 773207) (by norm_num)
theorem B2819045 : Blo 1879141 2819045 := bbase (se 4 (by rfl) ⟨264285, by rfl⟩ : syracuseStep 2819045 = 528571) (by norm_num)
theorem B2114545 : Blo 1879141 2114545 := bbase (se 2 (by rfl) ⟨792954, by rfl⟩ : syracuseStep 2114545 = 1585909) (by norm_num)
theorem B3171325 : Blo 1879141 3171325 := bbase (se 3 (by rfl) ⟨594623, by rfl⟩ : syracuseStep 3171325 = 1189247) (by norm_num)
theorem B2819069 : Blo 1879141 2819069 := bbase (se 3 (by rfl) ⟨528575, by rfl⟩ : syracuseStep 2819069 = 1057151) (by norm_num)
theorem B9036805 : Blo 1879141 9036805 := bbase (se 4 (by rfl) ⟨847200, by rfl⟩ : syracuseStep 9036805 = 1694401) (by norm_num)
theorem B4228109 : Blo 1879141 4228109 := bbase (se 3 (by rfl) ⟨792770, by rfl⟩ : syracuseStep 4228109 = 1585541) (by norm_num)
theorem B2819093 : Blo 1879141 2819093 := bbase (se 6 (by rfl) ⟨66072, by rfl⟩ : syracuseStep 2819093 = 132145) (by norm_num)
theorem B2114581 : Blo 1879141 2114581 := bbase (se 6 (by rfl) ⟨49560, by rfl⟩ : syracuseStep 2114581 = 99121) (by norm_num)
theorem B2819117 : Blo 1879141 2819117 := bbase (se 3 (by rfl) ⟨528584, by rfl⟩ : syracuseStep 2819117 = 1057169) (by norm_num)
theorem B2114617 : Blo 1879141 2114617 := bbase (se 2 (by rfl) ⟨792981, by rfl⟩ : syracuseStep 2114617 = 1585963) (by norm_num)
theorem B2819141 : Blo 1879141 2819141 := bbase (se 4 (by rfl) ⟨264294, by rfl⟩ : syracuseStep 2819141 = 528589) (by norm_num)
theorem B4760653 : Blo 1879141 4760653 := bbase (se 3 (by rfl) ⟨892622, by rfl⟩ : syracuseStep 4760653 = 1785245) (by norm_num)
theorem B4228181 : Blo 1879141 4228181 := bbase (se 8 (by rfl) ⟨24774, by rfl⟩ : syracuseStep 4228181 = 49549) (by norm_num)
theorem B3171413 : Blo 1879141 3171413 := bbase (se 8 (by rfl) ⟨18582, by rfl⟩ : syracuseStep 3171413 = 37165) (by norm_num)
theorem B2819165 : Blo 1879141 2819165 := bbase (se 3 (by rfl) ⟨528593, by rfl⟩ : syracuseStep 2819165 = 1057187) (by norm_num)
theorem B2114653 : Blo 1879141 2114653 := bbase (se 3 (by rfl) ⟨396497, by rfl⟩ : syracuseStep 2114653 = 792995) (by norm_num)
theorem B2819189 : Blo 1879141 2819189 := bbase (se 5 (by rfl) ⟨132149, by rfl⟩ : syracuseStep 2819189 = 264299) (by norm_num)
theorem B2114689 : Blo 1879141 2114689 := bbase (se 2 (by rfl) ⟨793008, by rfl⟩ : syracuseStep 2114689 = 1586017) (by norm_num)
theorem B2819213 : Blo 1879141 2819213 := bbase (se 3 (by rfl) ⟨528602, by rfl⟩ : syracuseStep 2819213 = 1057205) (by norm_num)
theorem B4228253 : Blo 1879141 4228253 := bbase (se 3 (by rfl) ⟨792797, by rfl⟩ : syracuseStep 4228253 = 1585595) (by norm_num)
theorem B2819237 : Blo 1879141 2819237 := bbase (se 4 (by rfl) ⟨264303, by rfl⟩ : syracuseStep 2819237 = 528607) (by norm_num)
theorem B2114725 : Blo 1879141 2114725 := bbase (se 4 (by rfl) ⟨198255, by rfl⟩ : syracuseStep 2114725 = 396511) (by norm_num)
theorem B2819261 : Blo 1879141 2819261 := bbase (se 3 (by rfl) ⟨528611, by rfl⟩ : syracuseStep 2819261 = 1057223) (by norm_num)
theorem B4760765 : Blo 1879141 4760765 := bbase (se 3 (by rfl) ⟨892643, by rfl⟩ : syracuseStep 4760765 = 1785287) (by norm_num)
theorem B2114761 : Blo 1879141 2114761 := bbase (se 2 (by rfl) ⟨793035, by rfl⟩ : syracuseStep 2114761 = 1586071) (by norm_num)
theorem B3171541 : Blo 1879141 3171541 := bbase (se 7 (by rfl) ⟨37166, by rfl⟩ : syracuseStep 3171541 = 74333) (by norm_num)
theorem B2819285 : Blo 1879141 2819285 := bbase (se 7 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 2819285 = 66077) (by norm_num)
theorem B3433693 : Blo 1879141 3433693 := bbase (se 3 (by rfl) ⟨643817, by rfl⟩ : syracuseStep 3433693 = 1287635) (by norm_num)
theorem B4015325 : Blo 1879141 4015325 := bbase (se 3 (by rfl) ⟨752873, by rfl⟩ : syracuseStep 4015325 = 1505747) (by norm_num)
theorem B4228325 : Blo 1879141 4228325 := bbase (se 4 (by rfl) ⟨396405, by rfl⟩ : syracuseStep 4228325 = 792811) (by norm_num)
theorem B2819309 : Blo 1879141 2819309 := bbase (se 3 (by rfl) ⟨528620, by rfl⟩ : syracuseStep 2819309 = 1057241) (by norm_num)
theorem B2114797 : Blo 1879141 2114797 := bbase (se 3 (by rfl) ⟨396524, by rfl⟩ : syracuseStep 2114797 = 793049) (by norm_num)
theorem B2819333 : Blo 1879141 2819333 := bbase (se 4 (by rfl) ⟨264312, by rfl⟩ : syracuseStep 2819333 = 528625) (by norm_num)
theorem B2114833 : Blo 1879141 2114833 := bbase (se 2 (by rfl) ⟨793062, by rfl⟩ : syracuseStep 2114833 = 1586125) (by norm_num)
theorem B2819357 : Blo 1879141 2819357 := bbase (se 3 (by rfl) ⟨528629, by rfl⟩ : syracuseStep 2819357 = 1057259) (by norm_num)
theorem B4228397 : Blo 1879141 4228397 := bbase (se 3 (by rfl) ⟨792824, by rfl⟩ : syracuseStep 4228397 = 1585649) (by norm_num)
theorem B3171629 : Blo 1879141 3171629 := bbase (se 3 (by rfl) ⟨594680, by rfl⟩ : syracuseStep 3171629 = 1189361) (by norm_num)
theorem B2819381 : Blo 1879141 2819381 := bbase (se 5 (by rfl) ⟨132158, by rfl⟩ : syracuseStep 2819381 = 264317) (by norm_num)
theorem B2114869 : Blo 1879141 2114869 := bbase (se 5 (by rfl) ⟨99134, by rfl⟩ : syracuseStep 2114869 = 198269) (by norm_num)
theorem B2819405 : Blo 1879141 2819405 := bbase (se 3 (by rfl) ⟨528638, by rfl⟩ : syracuseStep 2819405 = 1057277) (by norm_num)
theorem B2114905 : Blo 1879141 2114905 := bbase (se 2 (by rfl) ⟨793089, by rfl⟩ : syracuseStep 2114905 = 1586179) (by norm_num)
theorem B2819429 : Blo 1879141 2819429 := bbase (se 4 (by rfl) ⟨264321, by rfl⟩ : syracuseStep 2819429 = 528643) (by norm_num)
theorem B4015469 : Blo 1879141 4015469 := bbase (se 3 (by rfl) ⟨752900, by rfl⟩ : syracuseStep 4015469 = 1505801) (by norm_num)
theorem B4228469 : Blo 1879141 4228469 := bbase (se 5 (by rfl) ⟨198209, by rfl⟩ : syracuseStep 4228469 = 396419) (by norm_num)
theorem B2819453 : Blo 1879141 2819453 := bbase (se 3 (by rfl) ⟨528647, by rfl⟩ : syracuseStep 2819453 = 1057295) (by norm_num)
theorem B2114941 : Blo 1879141 2114941 := bbase (se 3 (by rfl) ⟨396551, by rfl⟩ : syracuseStep 2114941 = 793103) (by norm_num)
theorem B4760957 : Blo 1879141 4760957 := bbase (se 3 (by rfl) ⟨892679, by rfl⟩ : syracuseStep 4760957 = 1785359) (by norm_num)
theorem B2819477 : Blo 1879141 2819477 := bbase (se 6 (by rfl) ⟨66081, by rfl⟩ : syracuseStep 2819477 = 132163) (by norm_num)
theorem B14476693 : Blo 1879141 14476693 := bbase (se 6 (by rfl) ⟨339297, by rfl⟩ : syracuseStep 14476693 = 678595) (by norm_num)
theorem B2114977 : Blo 1879141 2114977 := bbase (se 2 (by rfl) ⟨793116, by rfl⟩ : syracuseStep 2114977 = 1586233) (by norm_num)
theorem B3171757 : Blo 1879141 3171757 := bbase (se 3 (by rfl) ⟨594704, by rfl⟩ : syracuseStep 3171757 = 1189409) (by norm_num)
theorem B2819501 : Blo 1879141 2819501 := bbase (se 3 (by rfl) ⟨528656, by rfl⟩ : syracuseStep 2819501 = 1057313) (by norm_num)
theorem B4228541 : Blo 1879141 4228541 := bbase (se 3 (by rfl) ⟨792851, by rfl⟩ : syracuseStep 4228541 = 1585703) (by norm_num)
theorem B2819525 : Blo 1879141 2819525 := bbase (se 4 (by rfl) ⟨264330, by rfl⟩ : syracuseStep 2819525 = 528661) (by norm_num)
theorem B2115013 : Blo 1879141 2115013 := bbase (se 4 (by rfl) ⟨198282, by rfl⟩ : syracuseStep 2115013 = 396565) (by norm_num)
theorem B2819549 : Blo 1879141 2819549 := bbase (se 3 (by rfl) ⟨528665, by rfl⟩ : syracuseStep 2819549 = 1057331) (by norm_num)
theorem B2115049 : Blo 1879141 2115049 := bbase (se 2 (by rfl) ⟨793143, by rfl⟩ : syracuseStep 2115049 = 1586287) (by norm_num)
theorem B2819573 : Blo 1879141 2819573 := bbase (se 5 (by rfl) ⟨132167, by rfl⟩ : syracuseStep 2819573 = 264335) (by norm_num)
theorem B4228613 : Blo 1879141 4228613 := bbase (se 4 (by rfl) ⟨396432, by rfl⟩ : syracuseStep 4228613 = 792865) (by norm_num)
theorem B3171845 : Blo 1879141 3171845 := bbase (se 4 (by rfl) ⟨297360, by rfl⟩ : syracuseStep 3171845 = 594721) (by norm_num)
theorem B2008585 : Blo 1879141 2008585 := bbase (se 2 (by rfl) ⟨753219, by rfl⟩ : syracuseStep 2008585 = 1506439) (by norm_num)
theorem B2819597 : Blo 1879141 2819597 := bbase (se 3 (by rfl) ⟨528674, by rfl⟩ : syracuseStep 2819597 = 1057349) (by norm_num)
theorem B2115085 : Blo 1879141 2115085 := bbase (se 3 (by rfl) ⟨396578, by rfl⟩ : syracuseStep 2115085 = 793157) (by norm_num)
theorem B2819621 : Blo 1879141 2819621 := bbase (se 4 (by rfl) ⟨264339, by rfl⟩ : syracuseStep 2819621 = 528679) (by norm_num)
theorem B2115121 : Blo 1879141 2115121 := bbase (se 2 (by rfl) ⟨793170, by rfl⟩ : syracuseStep 2115121 = 1586341) (by norm_num)
theorem B15238709 : Blo 1879141 15238709 := bbase (se 5 (by rfl) ⟨714314, by rfl⟩ : syracuseStep 15238709 = 1428629) (by norm_num)
theorem B2819645 : Blo 1879141 2819645 := bbase (se 3 (by rfl) ⟨528683, by rfl⟩ : syracuseStep 2819645 = 1057367) (by norm_num)
theorem B4228685 : Blo 1879141 4228685 := bbase (se 3 (by rfl) ⟨792878, by rfl⟩ : syracuseStep 4228685 = 1585757) (by norm_num)
theorem B2008657 : Blo 1879141 2008657 := bbase (se 2 (by rfl) ⟨753246, by rfl⟩ : syracuseStep 2008657 = 1506493) (by norm_num)
theorem B2819669 : Blo 1879141 2819669 := bbase (se 8 (by rfl) ⟨16521, by rfl⟩ : syracuseStep 2819669 = 33043) (by norm_num)
theorem B2115157 : Blo 1879141 2115157 := bbase (se 8 (by rfl) ⟨12393, by rfl⟩ : syracuseStep 2115157 = 24787) (by norm_num)
theorem B6342245 : Blo 1879141 6342245 := bbase (se 4 (by rfl) ⟨594585, by rfl⟩ : syracuseStep 6342245 = 1189171) (by norm_num)
theorem B2819693 : Blo 1879141 2819693 := bbase (se 3 (by rfl) ⟨528692, by rfl⟩ : syracuseStep 2819693 = 1057385) (by norm_num)
theorem B2115193 : Blo 1879141 2115193 := bbase (se 2 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 2115193 = 1586395) (by norm_num)
theorem B3171973 : Blo 1879141 3171973 := bbase (se 4 (by rfl) ⟨297372, by rfl⟩ : syracuseStep 3171973 = 594745) (by norm_num)
theorem B2819717 : Blo 1879141 2819717 := bbase (se 4 (by rfl) ⟨264348, by rfl⟩ : syracuseStep 2819717 = 528697) (by norm_num)
theorem B4228757 : Blo 1879141 4228757 := bbase (se 6 (by rfl) ⟨99111, by rfl⟩ : syracuseStep 4228757 = 198223) (by norm_num)
theorem B2819741 : Blo 1879141 2819741 := bbase (se 3 (by rfl) ⟨528701, by rfl⟩ : syracuseStep 2819741 = 1057403) (by norm_num)
theorem B2115229 : Blo 1879141 2115229 := bbase (se 3 (by rfl) ⟨396605, by rfl⟩ : syracuseStep 2115229 = 793211) (by norm_num)
theorem B2819765 : Blo 1879141 2819765 := bbase (se 5 (by rfl) ⟨132176, by rfl⟩ : syracuseStep 2819765 = 264353) (by norm_num)
theorem B2115265 : Blo 1879141 2115265 := bbase (se 2 (by rfl) ⟨793224, by rfl⟩ : syracuseStep 2115265 = 1586449) (by norm_num)
theorem B2713285 : Blo 1879141 2713285 := bbase (se 4 (by rfl) ⟨254370, by rfl⟩ : syracuseStep 2713285 = 508741) (by norm_num)
theorem B2819789 : Blo 1879141 2819789 := bbase (se 3 (by rfl) ⟨528710, by rfl⟩ : syracuseStep 2819789 = 1057421) (by norm_num)
theorem B4761301 : Blo 1879141 4761301 := bbase (se 7 (by rfl) ⟨55796, by rfl⟩ : syracuseStep 4761301 = 111593) (by norm_num)
theorem B4228829 : Blo 1879141 4228829 := bbase (se 3 (by rfl) ⟨792905, by rfl⟩ : syracuseStep 4228829 = 1585811) (by norm_num)
theorem B3172061 : Blo 1879141 3172061 := bbase (se 3 (by rfl) ⟨594761, by rfl⟩ : syracuseStep 3172061 = 1189523) (by norm_num)
theorem B2541277 : Blo 1879141 2541277 := bbase (se 3 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 2541277 = 952979) (by norm_num)
theorem B2819813 : Blo 1879141 2819813 := bbase (se 4 (by rfl) ⟨264357, by rfl⟩ : syracuseStep 2819813 = 528715) (by norm_num)
theorem B2115301 : Blo 1879141 2115301 := bbase (se 4 (by rfl) ⟨198309, by rfl⟩ : syracuseStep 2115301 = 396619) (by norm_num)
theorem B2819837 : Blo 1879141 2819837 := bbase (se 3 (by rfl) ⟨528719, by rfl⟩ : syracuseStep 2819837 = 1057439) (by norm_num)
theorem B9520901 : Blo 1879141 9520901 := bbase (se 4 (by rfl) ⟨892584, by rfl⟩ : syracuseStep 9520901 = 1785169) (by norm_num)
theorem B2115337 : Blo 1879141 2115337 := bbase (se 2 (by rfl) ⟨793251, by rfl⟩ : syracuseStep 2115337 = 1586503) (by norm_num)
theorem B2819861 : Blo 1879141 2819861 := bbase (se 6 (by rfl) ⟨66090, by rfl⟩ : syracuseStep 2819861 = 132181) (by norm_num)
theorem B4228901 : Blo 1879141 4228901 := bbase (se 4 (by rfl) ⟨396459, by rfl⟩ : syracuseStep 4228901 = 792919) (by norm_num)
theorem B2819885 : Blo 1879141 2819885 := bbase (se 3 (by rfl) ⟨528728, by rfl⟩ : syracuseStep 2819885 = 1057457) (by norm_num)
theorem B2115373 : Blo 1879141 2115373 := bbase (se 3 (by rfl) ⟨396632, by rfl⟩ : syracuseStep 2115373 = 793265) (by norm_num)
theorem B3434293 : Blo 1879141 3434293 := bbase (se 5 (by rfl) ⟨160982, by rfl⟩ : syracuseStep 3434293 = 321965) (by norm_num)
theorem B2819909 : Blo 1879141 2819909 := bbase (se 4 (by rfl) ⟨264366, by rfl⟩ : syracuseStep 2819909 = 528733) (by norm_num)
theorem B4761413 : Blo 1879141 4761413 := bbase (se 4 (by rfl) ⟨446382, by rfl⟩ : syracuseStep 4761413 = 892765) (by norm_num)
theorem B2115409 : Blo 1879141 2115409 := bbase (se 2 (by rfl) ⟨793278, by rfl⟩ : syracuseStep 2115409 = 1586557) (by norm_num)
theorem B2541397 : Blo 1879141 2541397 := bbase (se 9 (by rfl) ⟨7445, by rfl⟩ : syracuseStep 2541397 = 14891) (by norm_num)
theorem B3172189 : Blo 1879141 3172189 := bbase (se 3 (by rfl) ⟨594785, by rfl⟩ : syracuseStep 3172189 = 1189571) (by norm_num)
theorem B2819933 : Blo 1879141 2819933 := bbase (se 3 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 2819933 = 1057475) (by norm_num)
theorem B4228973 : Blo 1879141 4228973 := bbase (se 3 (by rfl) ⟨792932, by rfl⟩ : syracuseStep 4228973 = 1585865) (by norm_num)
theorem B2819957 : Blo 1879141 2819957 := bbase (se 5 (by rfl) ⟨132185, by rfl⟩ : syracuseStep 2819957 = 264371) (by norm_num)
theorem B2115445 : Blo 1879141 2115445 := bbase (se 5 (by rfl) ⟨99161, by rfl⟩ : syracuseStep 2115445 = 198323) (by norm_num)
theorem B2819981 : Blo 1879141 2819981 := bbase (se 3 (by rfl) ⟨528746, by rfl⟩ : syracuseStep 2819981 = 1057493) (by norm_num)
theorem B2115481 : Blo 1879141 2115481 := bbase (se 2 (by rfl) ⟨793305, by rfl⟩ : syracuseStep 2115481 = 1586611) (by norm_num)
theorem B8030117 : Blo 1879141 8030117 := bbase (se 4 (by rfl) ⟨752823, by rfl⟩ : syracuseStep 8030117 = 1505647) (by norm_num)
theorem B2820005 : Blo 1879141 2820005 := bbase (se 4 (by rfl) ⟨264375, by rfl⟩ : syracuseStep 2820005 = 528751) (by norm_num)
theorem B4229045 : Blo 1879141 4229045 := bbase (se 5 (by rfl) ⟨198236, by rfl⟩ : syracuseStep 4229045 = 396473) (by norm_num)
theorem B3172277 : Blo 1879141 3172277 := bbase (se 5 (by rfl) ⟨148700, by rfl⟩ : syracuseStep 3172277 = 297401) (by norm_num)
theorem B2820029 : Blo 1879141 2820029 := bbase (se 3 (by rfl) ⟨528755, by rfl⟩ : syracuseStep 2820029 = 1057511) (by norm_num)
theorem B2115517 : Blo 1879141 2115517 := bbase (se 3 (by rfl) ⟨396659, by rfl⟩ : syracuseStep 2115517 = 793319) (by norm_num)
theorem B2820053 : Blo 1879141 2820053 := bbase (se 7 (by rfl) ⟨33047, by rfl⟩ : syracuseStep 2820053 = 66095) (by norm_num)
theorem B2115553 : Blo 1879141 2115553 := bbase (se 2 (by rfl) ⟨793332, by rfl⟩ : syracuseStep 2115553 = 1586665) (by norm_num)
theorem B2820077 : Blo 1879141 2820077 := bbase (se 3 (by rfl) ⟨528764, by rfl⟩ : syracuseStep 2820077 = 1057529) (by norm_num)
theorem B4229117 : Blo 1879141 4229117 := bbase (se 3 (by rfl) ⟨792959, by rfl⟩ : syracuseStep 4229117 = 1585919) (by norm_num)
theorem B2820101 : Blo 1879141 2820101 := bbase (se 4 (by rfl) ⟨264384, by rfl⟩ : syracuseStep 2820101 = 528769) (by norm_num)
theorem B2115589 : Blo 1879141 2115589 := bbase (se 4 (by rfl) ⟨198336, by rfl⟩ : syracuseStep 2115589 = 396673) (by norm_num)
theorem B4761605 : Blo 1879141 4761605 := bbase (se 4 (by rfl) ⟨446400, by rfl⟩ : syracuseStep 4761605 = 892801) (by norm_num)
theorem B6342677 : Blo 1879141 6342677 := bbase (se 6 (by rfl) ⟨148656, by rfl⟩ : syracuseStep 6342677 = 297313) (by norm_num)
theorem B2820125 : Blo 1879141 2820125 := bbase (se 3 (by rfl) ⟨528773, by rfl⟩ : syracuseStep 2820125 = 1057547) (by norm_num)
theorem B2115625 : Blo 1879141 2115625 := bbase (se 2 (by rfl) ⟨793359, by rfl⟩ : syracuseStep 2115625 = 1586719) (by norm_num)
theorem B2541613 : Blo 1879141 2541613 := bbase (se 3 (by rfl) ⟨476552, by rfl⟩ : syracuseStep 2541613 = 953105) (by norm_num)
theorem B3172405 : Blo 1879141 3172405 := bbase (se 5 (by rfl) ⟨148706, by rfl⟩ : syracuseStep 3172405 = 297413) (by norm_num)
theorem B2820149 : Blo 1879141 2820149 := bbase (se 5 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 2820149 = 264389) (by norm_num)
theorem B4229189 : Blo 1879141 4229189 := bbase (se 4 (by rfl) ⟨396486, by rfl⟩ : syracuseStep 4229189 = 792973) (by norm_num)
theorem B2820173 : Blo 1879141 2820173 := bbase (se 3 (by rfl) ⟨528782, by rfl⟩ : syracuseStep 2820173 = 1057565) (by norm_num)
theorem B2115661 : Blo 1879141 2115661 := bbase (se 3 (by rfl) ⟨396686, by rfl⟩ : syracuseStep 2115661 = 793373) (by norm_num)
theorem B4016213 : Blo 1879141 4016213 := bbase (se 8 (by rfl) ⟨23532, by rfl⟩ : syracuseStep 4016213 = 47065) (by norm_num)
theorem B2820197 : Blo 1879141 2820197 := bbase (se 4 (by rfl) ⟨264393, by rfl⟩ : syracuseStep 2820197 = 528787) (by norm_num)
theorem B2115697 : Blo 1879141 2115697 := bbase (se 2 (by rfl) ⟨793386, by rfl⟩ : syracuseStep 2115697 = 1586773) (by norm_num)
theorem B7940213 : Blo 1879141 7940213 := bbase (se 5 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 7940213 = 744395) (by norm_num)
theorem B2820221 : Blo 1879141 2820221 := bbase (se 3 (by rfl) ⟨528791, by rfl⟩ : syracuseStep 2820221 = 1057583) (by norm_num)
theorem B4229261 : Blo 1879141 4229261 := bbase (se 3 (by rfl) ⟨792986, by rfl⟩ : syracuseStep 4229261 = 1585973) (by norm_num)
theorem B3172493 : Blo 1879141 3172493 := bbase (se 3 (by rfl) ⟨594842, by rfl⟩ : syracuseStep 3172493 = 1189685) (by norm_num)
theorem B2820245 : Blo 1879141 2820245 := bbase (se 6 (by rfl) ⟨66099, by rfl⟩ : syracuseStep 2820245 = 132199) (by norm_num)
theorem B2115733 : Blo 1879141 2115733 := bbase (se 6 (by rfl) ⟨49587, by rfl⟩ : syracuseStep 2115733 = 99175) (by norm_num)
theorem B2820269 : Blo 1879141 2820269 := bbase (se 3 (by rfl) ⟨528800, by rfl⟩ : syracuseStep 2820269 = 1057601) (by norm_num)
theorem B2115769 : Blo 1879141 2115769 := bbase (se 2 (by rfl) ⟨793413, by rfl⟩ : syracuseStep 2115769 = 1586827) (by norm_num)
theorem B2820293 : Blo 1879141 2820293 := bbase (se 4 (by rfl) ⟨264402, by rfl⟩ : syracuseStep 2820293 = 528805) (by norm_num)
theorem B4229333 : Blo 1879141 4229333 := bbase (se 7 (by rfl) ⟨49562, by rfl⟩ : syracuseStep 4229333 = 99125) (by norm_num)
theorem B2820317 : Blo 1879141 2820317 := bbase (se 3 (by rfl) ⟨528809, by rfl⟩ : syracuseStep 2820317 = 1057619) (by norm_num)
theorem B2115805 : Blo 1879141 2115805 := bbase (se 3 (by rfl) ⟨396713, by rfl⟩ : syracuseStep 2115805 = 793427) (by norm_num)
theorem B2820341 : Blo 1879141 2820341 := bbase (se 5 (by rfl) ⟨132203, by rfl⟩ : syracuseStep 2820341 = 264407) (by norm_num)
theorem B2115841 : Blo 1879141 2115841 := bbase (se 2 (by rfl) ⟨793440, by rfl⟩ : syracuseStep 2115841 = 1586881) (by norm_num)
theorem B3172621 : Blo 1879141 3172621 := bbase (se 3 (by rfl) ⟨594866, by rfl⟩ : syracuseStep 3172621 = 1189733) (by norm_num)
theorem B2820365 : Blo 1879141 2820365 := bbase (se 3 (by rfl) ⟨528818, by rfl⟩ : syracuseStep 2820365 = 1057637) (by norm_num)
theorem B4229405 : Blo 1879141 4229405 := bbase (se 3 (by rfl) ⟨793013, by rfl⟩ : syracuseStep 4229405 = 1586027) (by norm_num)
theorem B2820389 : Blo 1879141 2820389 := bbase (se 4 (by rfl) ⟨264411, by rfl⟩ : syracuseStep 2820389 = 528823) (by norm_num)
theorem B2115877 : Blo 1879141 2115877 := bbase (se 4 (by rfl) ⟨198363, by rfl⟩ : syracuseStep 2115877 = 396727) (by norm_num)
theorem B2820413 : Blo 1879141 2820413 := bbase (se 3 (by rfl) ⟨528827, by rfl⟩ : syracuseStep 2820413 = 1057655) (by norm_num)
theorem B2115913 : Blo 1879141 2115913 := bbase (se 2 (by rfl) ⟨793467, by rfl⟩ : syracuseStep 2115913 = 1586935) (by norm_num)
theorem B2820437 : Blo 1879141 2820437 := bbase (se 10 (by rfl) ⟨4131, by rfl⟩ : syracuseStep 2820437 = 8263) (by norm_num)
theorem B4229477 : Blo 1879141 4229477 := bbase (se 4 (by rfl) ⟨396513, by rfl⟩ : syracuseStep 4229477 = 793027) (by norm_num)
theorem B3172709 : Blo 1879141 3172709 := bbase (se 4 (by rfl) ⟨297441, by rfl⟩ : syracuseStep 3172709 = 594883) (by norm_num)
theorem B2820461 : Blo 1879141 2820461 := bbase (se 3 (by rfl) ⟨528836, by rfl⟩ : syracuseStep 2820461 = 1057673) (by norm_num)
theorem B2115949 : Blo 1879141 2115949 := bbase (se 3 (by rfl) ⟨396740, by rfl⟩ : syracuseStep 2115949 = 793481) (by norm_num)
theorem B2820485 : Blo 1879141 2820485 := bbase (se 4 (by rfl) ⟨264420, by rfl⟩ : syracuseStep 2820485 = 528841) (by norm_num)
theorem B2115985 : Blo 1879141 2115985 := bbase (se 2 (by rfl) ⟨793494, by rfl⟩ : syracuseStep 2115985 = 1586989) (by norm_num)
theorem B14281109 : Blo 1879141 14281109 := bbase (se 6 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 14281109 = 669427) (by norm_num)
theorem B2820509 : Blo 1879141 2820509 := bbase (se 3 (by rfl) ⟨528845, by rfl⟩ : syracuseStep 2820509 = 1057691) (by norm_num)
theorem B4229549 : Blo 1879141 4229549 := bbase (se 3 (by rfl) ⟨793040, by rfl⟩ : syracuseStep 4229549 = 1586081) (by norm_num)
theorem B2820533 : Blo 1879141 2820533 := bbase (se 5 (by rfl) ⟨132212, by rfl⟩ : syracuseStep 2820533 = 264425) (by norm_num)
theorem B2116021 : Blo 1879141 2116021 := bbase (se 5 (by rfl) ⟨99188, by rfl⟩ : syracuseStep 2116021 = 198377) (by norm_num)
theorem B6343109 : Blo 1879141 6343109 := bbase (se 4 (by rfl) ⟨594666, by rfl⟩ : syracuseStep 6343109 = 1189333) (by norm_num)
theorem B2820557 : Blo 1879141 2820557 := bbase (se 3 (by rfl) ⟨528854, by rfl⟩ : syracuseStep 2820557 = 1057709) (by norm_num)
theorem B2116057 : Blo 1879141 2116057 := bbase (se 2 (by rfl) ⟨793521, by rfl⟩ : syracuseStep 2116057 = 1587043) (by norm_num)
theorem B3172837 : Blo 1879141 3172837 := bbase (se 4 (by rfl) ⟨297453, by rfl⟩ : syracuseStep 3172837 = 594907) (by norm_num)
theorem B2820581 : Blo 1879141 2820581 := bbase (se 4 (by rfl) ⟨264429, by rfl⟩ : syracuseStep 2820581 = 528859) (by norm_num)
theorem B4229621 : Blo 1879141 4229621 := bbase (se 5 (by rfl) ⟨198263, by rfl⟩ : syracuseStep 4229621 = 396527) (by norm_num)
theorem B2820605 : Blo 1879141 2820605 := bbase (se 3 (by rfl) ⟨528863, by rfl⟩ : syracuseStep 2820605 = 1057727) (by norm_num)
theorem B2116093 : Blo 1879141 2116093 := bbase (se 3 (by rfl) ⟨396767, by rfl⟩ : syracuseStep 2116093 = 793535) (by norm_num)
theorem B3811853 : Blo 1879141 3811853 := bbase (se 3 (by rfl) ⟨714722, by rfl⟩ : syracuseStep 3811853 = 1429445) (by norm_num)
theorem B2820629 : Blo 1879141 2820629 := bbase (se 6 (by rfl) ⟨66108, by rfl⟩ : syracuseStep 2820629 = 132217) (by norm_num)
theorem B2116129 : Blo 1879141 2116129 := bbase (se 2 (by rfl) ⟨793548, by rfl⟩ : syracuseStep 2116129 = 1587097) (by norm_num)
theorem B6023717 : Blo 1879141 6023717 := bbase (se 4 (by rfl) ⟨564723, by rfl⟩ : syracuseStep 6023717 = 1129447) (by norm_num)
theorem B2820653 : Blo 1879141 2820653 := bbase (se 3 (by rfl) ⟨528872, by rfl⟩ : syracuseStep 2820653 = 1057745) (by norm_num)
theorem B4229693 : Blo 1879141 4229693 := bbase (se 3 (by rfl) ⟨793067, by rfl⟩ : syracuseStep 4229693 = 1586135) (by norm_num)
theorem B3172925 : Blo 1879141 3172925 := bbase (se 3 (by rfl) ⟨594923, by rfl⟩ : syracuseStep 3172925 = 1189847) (by norm_num)
theorem B2820677 : Blo 1879141 2820677 := bbase (se 4 (by rfl) ⟨264438, by rfl⟩ : syracuseStep 2820677 = 528877) (by norm_num)
theorem B2116165 : Blo 1879141 2116165 := bbase (se 4 (by rfl) ⟨198390, by rfl⟩ : syracuseStep 2116165 = 396781) (by norm_num)
theorem B2378317 : Blo 1879141 2378317 := bbase (se 3 (by rfl) ⟨445934, by rfl⟩ : syracuseStep 2378317 = 891869) (by norm_num)
theorem B2820701 : Blo 1879141 2820701 := bbase (se 3 (by rfl) ⟨528881, by rfl⟩ : syracuseStep 2820701 = 1057763) (by norm_num)
theorem B2116201 : Blo 1879141 2116201 := bbase (se 2 (by rfl) ⟨793575, by rfl⟩ : syracuseStep 2116201 = 1587151) (by norm_num)
theorem B2820725 : Blo 1879141 2820725 := bbase (se 5 (by rfl) ⟨132221, by rfl⟩ : syracuseStep 2820725 = 264443) (by norm_num)
theorem B4229765 : Blo 1879141 4229765 := bbase (se 4 (by rfl) ⟨396540, by rfl⟩ : syracuseStep 4229765 = 793081) (by norm_num)
theorem B2820749 : Blo 1879141 2820749 := bbase (se 3 (by rfl) ⟨528890, by rfl⟩ : syracuseStep 2820749 = 1057781) (by norm_num)
theorem B2116237 : Blo 1879141 2116237 := bbase (se 3 (by rfl) ⟨396794, by rfl⟩ : syracuseStep 2116237 = 793589) (by norm_num)
theorem B2820773 : Blo 1879141 2820773 := bbase (se 4 (by rfl) ⟨264447, by rfl⟩ : syracuseStep 2820773 = 528895) (by norm_num)
theorem B2378413 : Blo 1879141 2378413 := bbase (se 3 (by rfl) ⟨445952, by rfl⟩ : syracuseStep 2378413 = 891905) (by norm_num)
theorem B2116273 : Blo 1879141 2116273 := bbase (se 2 (by rfl) ⟨793602, by rfl⟩ : syracuseStep 2116273 = 1587205) (by norm_num)
theorem B3173053 : Blo 1879141 3173053 := bbase (se 3 (by rfl) ⟨594947, by rfl⟩ : syracuseStep 3173053 = 1189895) (by norm_num)
theorem B2820797 : Blo 1879141 2820797 := bbase (se 3 (by rfl) ⟨528899, by rfl⟩ : syracuseStep 2820797 = 1057799) (by norm_num)
theorem B7137989 : Blo 1879141 7137989 := bbase (se 4 (by rfl) ⟨669186, by rfl⟩ : syracuseStep 7137989 = 1338373) (by norm_num)
theorem B4229837 : Blo 1879141 4229837 := bbase (se 3 (by rfl) ⟨793094, by rfl⟩ : syracuseStep 4229837 = 1586189) (by norm_num)
theorem B2820821 : Blo 1879141 2820821 := bbase (se 7 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 2820821 = 66113) (by norm_num)
theorem B6023909 : Blo 1879141 6023909 := bbase (se 4 (by rfl) ⟨564741, by rfl⟩ : syracuseStep 6023909 = 1129483) (by norm_num)
theorem B2820845 : Blo 1879141 2820845 := bbase (se 3 (by rfl) ⟨528908, by rfl⟩ : syracuseStep 2820845 = 1057817) (by norm_num)
theorem B2820869 : Blo 1879141 2820869 := bbase (se 4 (by rfl) ⟨264456, by rfl⟩ : syracuseStep 2820869 = 528913) (by norm_num)
theorem B4229909 : Blo 1879141 4229909 := bbase (se 6 (by rfl) ⟨99138, by rfl⟩ : syracuseStep 4229909 = 198277) (by norm_num)
theorem B3173141 : Blo 1879141 3173141 := bbase (se 6 (by rfl) ⟨74370, by rfl⟩ : syracuseStep 3173141 = 148741) (by norm_num)
theorem B2820893 : Blo 1879141 2820893 := bbase (se 3 (by rfl) ⟨528917, by rfl⟩ : syracuseStep 2820893 = 1057835) (by norm_num)
theorem B14273333 : Blo 1879141 14273333 := bbase (se 5 (by rfl) ⟨669062, by rfl⟩ : syracuseStep 14273333 = 1338125) (by norm_num)
theorem B2820917 : Blo 1879141 2820917 := bbase (se 5 (by rfl) ⟨132230, by rfl⟩ : syracuseStep 2820917 = 264461) (by norm_num)
theorem B4016965 : Blo 1879141 4016965 := bbase (se 4 (by rfl) ⟨376590, by rfl⟩ : syracuseStep 4016965 = 753181) (by norm_num)
theorem B2820941 : Blo 1879141 2820941 := bbase (se 3 (by rfl) ⟨528926, by rfl⟩ : syracuseStep 2820941 = 1057853) (by norm_num)
theorem B12864341 : Blo 1879141 12864341 := bbase (se 9 (by rfl) ⟨37688, by rfl⟩ : syracuseStep 12864341 = 75377) (by norm_num)
theorem B2378585 : Blo 1879141 2378585 := bbase (se 2 (by rfl) ⟨891969, by rfl⟩ : syracuseStep 2378585 = 1783939) (by norm_num)
theorem B4229981 : Blo 1879141 4229981 := bbase (se 3 (by rfl) ⟨793121, by rfl⟩ : syracuseStep 4229981 = 1586243) (by norm_num)
theorem B2288485 : Blo 1879141 2288485 := bbase (se 4 (by rfl) ⟨214545, by rfl⟩ : syracuseStep 2288485 = 429091) (by norm_num)
theorem B2820965 : Blo 1879141 2820965 := bbase (se 4 (by rfl) ⟨264465, by rfl⟩ : syracuseStep 2820965 = 528931) (by norm_num)
theorem B6343541 : Blo 1879141 6343541 := bbase (se 5 (by rfl) ⟨297353, by rfl⟩ : syracuseStep 6343541 = 594707) (by norm_num)
theorem B12217205 : Blo 1879141 12217205 := bbase (se 5 (by rfl) ⟨572681, by rfl⟩ : syracuseStep 12217205 = 1145363) (by norm_num)
theorem B2820989 : Blo 1879141 2820989 := bbase (se 3 (by rfl) ⟨528935, by rfl⟩ : syracuseStep 2820989 = 1057871) (by norm_num)
theorem B8031109 : Blo 1879141 8031109 := bbase (se 4 (by rfl) ⟨752916, by rfl⟩ : syracuseStep 8031109 = 1505833) (by norm_num)
theorem B2378641 : Blo 1879141 2378641 := bbase (se 2 (by rfl) ⟨891990, by rfl⟩ : syracuseStep 2378641 = 1783981) (by norm_num)
theorem B3173269 : Blo 1879141 3173269 := bbase (se 6 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 3173269 = 148747) (by norm_num)
theorem B2821013 : Blo 1879141 2821013 := bbase (se 6 (by rfl) ⟨66117, by rfl⟩ : syracuseStep 2821013 = 132235) (by norm_num)
theorem B4230053 : Blo 1879141 4230053 := bbase (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) (by norm_num)
theorem B2821037 : Blo 1879141 2821037 := bbase (se 3 (by rfl) ⟨528944, by rfl⟩ : syracuseStep 2821037 = 1057889) (by norm_num)
theorem B2821061 : Blo 1879141 2821061 := bbase (se 4 (by rfl) ⟨264474, by rfl⟩ : syracuseStep 2821061 = 528949) (by norm_num)
theorem B4017109 : Blo 1879141 4017109 := bbase (se 7 (by rfl) ⟨47075, by rfl⟩ : syracuseStep 4017109 = 94151) (by norm_num)
theorem B2821085 : Blo 1879141 2821085 := bbase (se 3 (by rfl) ⟨528953, by rfl⟩ : syracuseStep 2821085 = 1057907) (by norm_num)
theorem B7138277 : Blo 1879141 7138277 := bbase (se 4 (by rfl) ⟨669213, by rfl⟩ : syracuseStep 7138277 = 1338427) (by norm_num)
theorem B4230125 : Blo 1879141 4230125 := bbase (se 3 (by rfl) ⟨793148, by rfl⟩ : syracuseStep 4230125 = 1586297) (by norm_num)
theorem B3173357 : Blo 1879141 3173357 := bbase (se 3 (by rfl) ⟨595004, by rfl⟩ : syracuseStep 3173357 = 1190009) (by norm_num)
theorem B2378737 : Blo 1879141 2378737 := bbase (se 2 (by rfl) ⟨892026, by rfl⟩ : syracuseStep 2378737 = 1784053) (by norm_num)
theorem B2821109 : Blo 1879141 2821109 := bbase (se 5 (by rfl) ⟨132239, by rfl⟩ : syracuseStep 2821109 = 264479) (by norm_num)
theorem B2821133 : Blo 1879141 2821133 := bbase (se 3 (by rfl) ⟨528962, by rfl⟩ : syracuseStep 2821133 = 1057925) (by norm_num)
theorem B9522197 : Blo 1879141 9522197 := bbase (se 6 (by rfl) ⟨223176, by rfl⟩ : syracuseStep 9522197 = 446353) (by norm_num)
theorem B6777893 : Blo 1879141 6777893 := bbase (se 4 (by rfl) ⟨635427, by rfl⟩ : syracuseStep 6777893 = 1270855) (by norm_num)
theorem B2821157 : Blo 1879141 2821157 := bbase (se 4 (by rfl) ⟨264483, by rfl⟩ : syracuseStep 2821157 = 528967) (by norm_num)
theorem B4230197 : Blo 1879141 4230197 := bbase (se 5 (by rfl) ⟨198290, by rfl⟩ : syracuseStep 4230197 = 396581) (by norm_num)
theorem B2821181 : Blo 1879141 2821181 := bbase (se 3 (by rfl) ⟨528971, by rfl⟩ : syracuseStep 2821181 = 1057943) (by norm_num)
theorem B3861589 : Blo 1879141 3861589 := bbase (se 8 (by rfl) ⟨22626, by rfl⟩ : syracuseStep 3861589 = 45253) (by norm_num)
theorem B2821205 : Blo 1879141 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B3173485 : Blo 1879141 3173485 := bbase (se 3 (by rfl) ⟨595028, by rfl⟩ : syracuseStep 3173485 = 1190057) (by norm_num)
theorem B2821229 : Blo 1879141 2821229 := bbase (se 3 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 2821229 = 1057961) (by norm_num)
theorem B4230269 : Blo 1879141 4230269 := bbase (se 3 (by rfl) ⟨793175, by rfl⟩ : syracuseStep 4230269 = 1586351) (by norm_num)
theorem B5352581 : Blo 1879141 5352581 := bbase (se 4 (by rfl) ⟨501804, by rfl⟩ : syracuseStep 5352581 = 1003609) (by norm_num)
theorem B2821253 : Blo 1879141 2821253 := bbase (se 4 (by rfl) ⟨264492, by rfl⟩ : syracuseStep 2821253 = 528985) (by norm_num)
theorem B2378909 : Blo 1879141 2378909 := bbase (se 3 (by rfl) ⟨446045, by rfl⟩ : syracuseStep 2378909 = 892091) (by norm_num)
theorem B2821277 : Blo 1879141 2821277 := bbase (se 3 (by rfl) ⟨528989, by rfl⟩ : syracuseStep 2821277 = 1057979) (by norm_num)
theorem B2821301 : Blo 1879141 2821301 := bbase (se 5 (by rfl) ⟨132248, by rfl⟩ : syracuseStep 2821301 = 264497) (by norm_num)
theorem B4230341 : Blo 1879141 4230341 := bbase (se 4 (by rfl) ⟨396594, by rfl⟩ : syracuseStep 4230341 = 793189) (by norm_num)
theorem B3173573 : Blo 1879141 3173573 := bbase (se 4 (by rfl) ⟨297522, by rfl⟩ : syracuseStep 3173573 = 595045) (by norm_num)
theorem B3214541 : Blo 1879141 3214541 := bbase (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) (by norm_num)
theorem B2821325 : Blo 1879141 2821325 := bbase (se 3 (by rfl) ⟨528998, by rfl⟩ : syracuseStep 2821325 = 1057997) (by norm_num)
theorem B2378965 : Blo 1879141 2378965 := bbase (se 7 (by rfl) ⟨27878, by rfl⟩ : syracuseStep 2378965 = 55757) (by norm_num)
theorem B2821349 : Blo 1879141 2821349 := bbase (se 4 (by rfl) ⟨264501, by rfl⟩ : syracuseStep 2821349 = 529003) (by norm_num)
theorem B2821373 : Blo 1879141 2821373 := bbase (se 3 (by rfl) ⟨529007, by rfl⟩ : syracuseStep 2821373 = 1058015) (by norm_num)
theorem B4230413 : Blo 1879141 4230413 := bbase (se 3 (by rfl) ⟨793202, by rfl⟩ : syracuseStep 4230413 = 1586405) (by norm_num)
theorem B2821397 : Blo 1879141 2821397 := bbase (se 6 (by rfl) ⟨66126, by rfl⟩ : syracuseStep 2821397 = 132253) (by norm_num)
theorem B6343973 : Blo 1879141 6343973 := bbase (se 4 (by rfl) ⟨594747, by rfl⟩ : syracuseStep 6343973 = 1189495) (by norm_num)
theorem B2821421 : Blo 1879141 2821421 := bbase (se 3 (by rfl) ⟨529016, by rfl⟩ : syracuseStep 2821421 = 1058033) (by norm_num)
theorem B2379061 : Blo 1879141 2379061 := bbase (se 5 (by rfl) ⟨111518, by rfl⟩ : syracuseStep 2379061 = 223037) (by norm_num)
theorem B3173701 : Blo 1879141 3173701 := bbase (se 4 (by rfl) ⟨297534, by rfl⟩ : syracuseStep 3173701 = 595069) (by norm_num)
theorem B2821445 : Blo 1879141 2821445 := bbase (se 4 (by rfl) ⟨264510, by rfl⟩ : syracuseStep 2821445 = 529021) (by norm_num)
theorem B4017485 : Blo 1879141 4017485 := bbase (se 3 (by rfl) ⟨753278, by rfl⟩ : syracuseStep 4017485 = 1506557) (by norm_num)
theorem B4230485 : Blo 1879141 4230485 := bbase (se 11 (by rfl) ⟨3098, by rfl⟩ : syracuseStep 4230485 = 6197) (by norm_num)
theorem B2821469 : Blo 1879141 2821469 := bbase (se 3 (by rfl) ⟨529025, by rfl⟩ : syracuseStep 2821469 = 1058051) (by norm_num)
theorem B2821493 : Blo 1879141 2821493 := bbase (se 5 (by rfl) ⟨132257, by rfl⟩ : syracuseStep 2821493 = 264515) (by norm_num)
theorem B2821517 : Blo 1879141 2821517 := bbase (se 3 (by rfl) ⟨529034, by rfl⟩ : syracuseStep 2821517 = 1058069) (by norm_num)
theorem B4230557 : Blo 1879141 4230557 := bbase (se 3 (by rfl) ⟨793229, by rfl⟩ : syracuseStep 4230557 = 1586459) (by norm_num)
theorem B3173789 : Blo 1879141 3173789 := bbase (se 3 (by rfl) ⟨595085, by rfl⟩ : syracuseStep 3173789 = 1190171) (by norm_num)
theorem B2821541 : Blo 1879141 2821541 := bbase (se 4 (by rfl) ⟨264519, by rfl⟩ : syracuseStep 2821541 = 529039) (by norm_num)
theorem B9514421 : Blo 1879141 9514421 := bbase (se 5 (by rfl) ⟨445988, by rfl⟩ : syracuseStep 9514421 = 891977) (by norm_num)
theorem B2821565 : Blo 1879141 2821565 := bbase (se 3 (by rfl) ⟨529043, by rfl⟩ : syracuseStep 2821565 = 1058087) (by norm_num)
theorem B4517317 : Blo 1879141 4517317 := bbase (se 4 (by rfl) ⟨423498, by rfl⟩ : syracuseStep 4517317 = 846997) (by norm_num)
theorem B2821589 : Blo 1879141 2821589 := bbase (se 7 (by rfl) ⟨33065, by rfl⟩ : syracuseStep 2821589 = 66131) (by norm_num)
theorem B2379233 : Blo 1879141 2379233 := bbase (se 2 (by rfl) ⟨892212, by rfl⟩ : syracuseStep 2379233 = 1784425) (by norm_num)
theorem B4230629 : Blo 1879141 4230629 := bbase (se 4 (by rfl) ⟨396621, by rfl⟩ : syracuseStep 4230629 = 793243) (by norm_num)
theorem B2821613 : Blo 1879141 2821613 := bbase (se 3 (by rfl) ⟨529052, by rfl⟩ : syracuseStep 2821613 = 1058105) (by norm_num)
theorem B4517365 : Blo 1879141 4517365 := bbase (se 5 (by rfl) ⟨211751, by rfl⟩ : syracuseStep 4517365 = 423503) (by norm_num)
theorem B2821637 : Blo 1879141 2821637 := bbase (se 4 (by rfl) ⟨264528, by rfl⟩ : syracuseStep 2821637 = 529057) (by norm_num)
theorem B2379289 : Blo 1879141 2379289 := bbase (se 2 (by rfl) ⟨892233, by rfl⟩ : syracuseStep 2379289 = 1784467) (by norm_num)
theorem B3173917 : Blo 1879141 3173917 := bbase (se 3 (by rfl) ⟨595109, by rfl⟩ : syracuseStep 3173917 = 1190219) (by norm_num)
theorem B2821661 : Blo 1879141 2821661 := bbase (se 3 (by rfl) ⟨529061, by rfl⟩ : syracuseStep 2821661 = 1058123) (by norm_num)
theorem B4230701 : Blo 1879141 4230701 := bbase (se 3 (by rfl) ⟨793256, by rfl⟩ : syracuseStep 4230701 = 1586513) (by norm_num)
theorem B2821685 : Blo 1879141 2821685 := bbase (se 5 (by rfl) ⟨132266, by rfl⟩ : syracuseStep 2821685 = 264533) (by norm_num)
theorem B4288069 : Blo 1879141 4288069 := bbase (se 4 (by rfl) ⟨402006, by rfl⟩ : syracuseStep 4288069 = 804013) (by norm_num)
theorem B2821709 : Blo 1879141 2821709 := bbase (se 3 (by rfl) ⟨529070, by rfl⟩ : syracuseStep 2821709 = 1058141) (by norm_num)
theorem B4230773 : Blo 1879141 4230773 := bbase (se 5 (by rfl) ⟨198317, by rfl⟩ : syracuseStep 4230773 = 396635) (by norm_num)
theorem B3174005 : Blo 1879141 3174005 := bbase (se 5 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 3174005 = 297563) (by norm_num)
theorem B2379385 : Blo 1879141 2379385 := bbase (se 2 (by rfl) ⟨892269, by rfl⟩ : syracuseStep 2379385 = 1784539) (by norm_num)
theorem B3616397 : Blo 1879141 3616397 := bbase (se 3 (by rfl) ⟨678074, by rfl⟩ : syracuseStep 3616397 = 1356149) (by norm_num)
theorem B4230845 : Blo 1879141 4230845 := bbase (se 3 (by rfl) ⟨793283, by rfl⟩ : syracuseStep 4230845 = 1586567) (by norm_num)
theorem B6344405 : Blo 1879141 6344405 := bbase (se 7 (by rfl) ⟨74348, by rfl⟩ : syracuseStep 6344405 = 148697) (by norm_num)
theorem B3387101 : Blo 1879141 3387101 := bbase (se 3 (by rfl) ⟨635081, by rfl⟩ : syracuseStep 3387101 = 1270163) (by norm_num)
theorem B3174133 : Blo 1879141 3174133 := bbase (se 5 (by rfl) ⟨148787, by rfl⟩ : syracuseStep 3174133 = 297575) (by norm_num)
theorem B4230917 : Blo 1879141 4230917 := bbase (se 4 (by rfl) ⟨396648, by rfl⟩ : syracuseStep 4230917 = 793297) (by norm_num)
theorem B5353253 : Blo 1879141 5353253 := bbase (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) (by norm_num)
theorem B2379557 : Blo 1879141 2379557 := bbase (se 4 (by rfl) ⟨223083, by rfl⟩ : syracuseStep 2379557 = 446167) (by norm_num)
theorem B4230989 : Blo 1879141 4230989 := bbase (se 3 (by rfl) ⟨793310, by rfl⟩ : syracuseStep 4230989 = 1586621) (by norm_num)
theorem B3813197 : Blo 1879141 3813197 := bbase (se 3 (by rfl) ⟨714974, by rfl⟩ : syracuseStep 3813197 = 1429949) (by norm_num)
theorem B3174221 : Blo 1879141 3174221 := bbase (se 3 (by rfl) ⟨595166, by rfl⟩ : syracuseStep 3174221 = 1190333) (by norm_num)
theorem B2379613 : Blo 1879141 2379613 := bbase (se 3 (by rfl) ⟨446177, by rfl⟩ : syracuseStep 2379613 = 892355) (by norm_num)
theorem B4231061 : Blo 1879141 4231061 := bbase (se 6 (by rfl) ⟨99165, by rfl⟩ : syracuseStep 4231061 = 198331) (by norm_num)
theorem B2379709 : Blo 1879141 2379709 := bbase (se 3 (by rfl) ⟨446195, by rfl⟩ : syracuseStep 2379709 = 892391) (by norm_num)
theorem B3174349 : Blo 1879141 3174349 := bbase (se 3 (by rfl) ⟨595190, by rfl⟩ : syracuseStep 3174349 = 1190381) (by norm_num)
theorem B4231133 : Blo 1879141 4231133 := bbase (se 3 (by rfl) ⟨793337, by rfl⟩ : syracuseStep 4231133 = 1586675) (by norm_num)
theorem B10711061 : Blo 1879141 10711061 := bbase (se 6 (by rfl) ⟨251040, by rfl⟩ : syracuseStep 10711061 = 502081) (by norm_num)
theorem B4231205 : Blo 1879141 4231205 := bbase (se 4 (by rfl) ⟨396675, by rfl⟩ : syracuseStep 4231205 = 793351) (by norm_num)
theorem B4517981 : Blo 1879141 4517981 := bbase (se 3 (by rfl) ⟨847121, by rfl⟩ : syracuseStep 4517981 = 1694243) (by norm_num)
theorem B2379881 : Blo 1879141 2379881 := bbase (se 2 (by rfl) ⟨892455, by rfl⟩ : syracuseStep 2379881 = 1784911) (by norm_num)
theorem B4231277 : Blo 1879141 4231277 := bbase (se 3 (by rfl) ⟨793364, by rfl⟩ : syracuseStep 4231277 = 1586729) (by norm_num)
theorem B6344837 : Blo 1879141 6344837 := bbase (se 4 (by rfl) ⟨594828, by rfl⟩ : syracuseStep 6344837 = 1189657) (by norm_num)
theorem B7139461 : Blo 1879141 7139461 := bbase (se 4 (by rfl) ⟨669324, by rfl⟩ : syracuseStep 7139461 = 1338649) (by norm_num)
theorem B2379937 : Blo 1879141 2379937 := bbase (se 2 (by rfl) ⟨892476, by rfl⟩ : syracuseStep 2379937 = 1784953) (by norm_num)
theorem B8138917 : Blo 1879141 8138917 := bbase (se 4 (by rfl) ⟨763023, by rfl⟩ : syracuseStep 8138917 = 1526047) (by norm_num)
theorem B4231349 : Blo 1879141 4231349 := bbase (se 5 (by rfl) ⟨198344, by rfl⟩ : syracuseStep 4231349 = 396689) (by norm_num)
theorem B5353685 : Blo 1879141 5353685 := bbase (se 7 (by rfl) ⟨62738, by rfl⟩ : syracuseStep 5353685 = 125477) (by norm_num)
theorem B4231421 : Blo 1879141 4231421 := bbase (se 3 (by rfl) ⟨793391, by rfl⟩ : syracuseStep 4231421 = 1586783) (by norm_num)
theorem B2380033 : Blo 1879141 2380033 := bbase (se 2 (by rfl) ⟨892512, by rfl⟩ : syracuseStep 2380033 = 1785025) (by norm_num)
theorem B3567901 : Blo 1879141 3567901 := bbase (se 3 (by rfl) ⟨668981, by rfl⟩ : syracuseStep 3567901 = 1337963) (by norm_num)
theorem B4231493 : Blo 1879141 4231493 := bbase (se 4 (by rfl) ⟨396702, by rfl⟩ : syracuseStep 4231493 = 793405) (by norm_num)
theorem B1905001 : Blo 1879141 1905001 := bbase (se 2 (by rfl) ⟨714375, by rfl⟩ : syracuseStep 1905001 = 1428751) (by norm_num)
theorem B10580341 : Blo 1879141 10580341 := bbase (se 5 (by rfl) ⟨495953, by rfl⟩ : syracuseStep 10580341 = 991907) (by norm_num)
theorem B3010949 : Blo 1879141 3010949 := bbase (se 4 (by rfl) ⟨282276, by rfl⟩ : syracuseStep 3010949 = 564553) (by norm_num)
theorem B4231565 : Blo 1879141 4231565 := bbase (se 3 (by rfl) ⟨793418, by rfl⟩ : syracuseStep 4231565 = 1586837) (by norm_num)
theorem B3568045 : Blo 1879141 3568045 := bbase (se 3 (by rfl) ⟨669008, by rfl⟩ : syracuseStep 3568045 = 1338017) (by norm_num)
theorem B2380205 : Blo 1879141 2380205 := bbase (se 3 (by rfl) ⟨446288, by rfl⟩ : syracuseStep 2380205 = 892577) (by norm_num)
theorem B7139765 : Blo 1879141 7139765 := bbase (se 5 (by rfl) ⟨334676, by rfl⟩ : syracuseStep 7139765 = 669353) (by norm_num)
theorem B4518325 : Blo 1879141 4518325 := bbase (se 5 (by rfl) ⟨211796, by rfl⟩ : syracuseStep 4518325 = 423593) (by norm_num)
theorem B6779333 : Blo 1879141 6779333 := bbase (se 4 (by rfl) ⟨635562, by rfl⟩ : syracuseStep 6779333 = 1271125) (by norm_num)
theorem B4231637 : Blo 1879141 4231637 := bbase (se 7 (by rfl) ⟨49589, by rfl⟩ : syracuseStep 4231637 = 99179) (by norm_num)
theorem B7336421 : Blo 1879141 7336421 := bbase (se 4 (by rfl) ⟨687789, by rfl⟩ : syracuseStep 7336421 = 1375579) (by norm_num)
theorem B2380261 : Blo 1879141 2380261 := bbase (se 4 (by rfl) ⟨223149, by rfl⟩ : syracuseStep 2380261 = 446299) (by norm_num)
theorem B3215893 : Blo 1879141 3215893 := bbase (se 6 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 3215893 = 150745) (by norm_num)
theorem B16282133 : Blo 1879141 16282133 := bbase (se 6 (by rfl) ⟨381612, by rfl⟩ : syracuseStep 16282133 = 763225) (by norm_num)
theorem B6107669 : Blo 1879141 6107669 := bbase (se 6 (by rfl) ⟨143148, by rfl⟩ : syracuseStep 6107669 = 286297) (by norm_num)
theorem B4231709 : Blo 1879141 4231709 := bbase (se 3 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 4231709 = 1586891) (by norm_num)
theorem B6345269 : Blo 1879141 6345269 := bbase (se 5 (by rfl) ⟨297434, by rfl⟩ : syracuseStep 6345269 = 594869) (by norm_num)
theorem B3011141 : Blo 1879141 3011141 := bbase (se 4 (by rfl) ⟨282294, by rfl⟩ : syracuseStep 3011141 = 564589) (by norm_num)
theorem B2380357 : Blo 1879141 2380357 := bbase (se 4 (by rfl) ⟨223158, by rfl⟩ : syracuseStep 2380357 = 446317) (by norm_num)
theorem B3568205 : Blo 1879141 3568205 := bbase (se 3 (by rfl) ⟨669038, by rfl⟩ : syracuseStep 3568205 = 1338077) (by norm_num)
theorem B3617357 : Blo 1879141 3617357 := bbase (se 3 (by rfl) ⟨678254, by rfl⟩ : syracuseStep 3617357 = 1356509) (by norm_num)
theorem B4231781 : Blo 1879141 4231781 := bbase (se 4 (by rfl) ⟨396729, by rfl⟩ : syracuseStep 4231781 = 793459) (by norm_num)
theorem B2257529 : Blo 1879141 2257529 := bbase (se 2 (by rfl) ⟨846573, by rfl⟩ : syracuseStep 2257529 = 1693147) (by norm_num)
theorem B4518557 : Blo 1879141 4518557 := bbase (se 3 (by rfl) ⟨847229, by rfl⟩ : syracuseStep 4518557 = 1694459) (by norm_num)
theorem B4231853 : Blo 1879141 4231853 := bbase (se 3 (by rfl) ⟨793472, by rfl⟩ : syracuseStep 4231853 = 1586945) (by norm_num)
theorem B9515717 : Blo 1879141 9515717 := bbase (se 4 (by rfl) ⟨892098, by rfl⟩ : syracuseStep 9515717 = 1784197) (by norm_num)
theorem B3011269 : Blo 1879141 3011269 := bbase (se 4 (by rfl) ⟨282306, by rfl⟩ : syracuseStep 3011269 = 564613) (by norm_num)
theorem B2257625 : Blo 1879141 2257625 := bbase (se 2 (by rfl) ⟨846609, by rfl⟩ : syracuseStep 2257625 = 1693219) (by norm_num)
theorem B3568349 : Blo 1879141 3568349 := bbase (se 3 (by rfl) ⟨669065, by rfl⟩ : syracuseStep 3568349 = 1338131) (by norm_num)
theorem B2257645 : Blo 1879141 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B2380529 : Blo 1879141 2380529 := bbase (se 2 (by rfl) ⟨892698, by rfl⟩ : syracuseStep 2380529 = 1785397) (by norm_num)
theorem B4231925 : Blo 1879141 4231925 := bbase (se 5 (by rfl) ⟨198371, by rfl⟩ : syracuseStep 4231925 = 396743) (by norm_num)
theorem B4289317 : Blo 1879141 4289317 := bbase (se 4 (by rfl) ⟨402123, by rfl⟩ : syracuseStep 4289317 = 804247) (by norm_num)
theorem B2380585 : Blo 1879141 2380585 := bbase (se 2 (by rfl) ⟨892719, by rfl⟩ : syracuseStep 2380585 = 1785439) (by norm_num)
theorem B4231997 : Blo 1879141 4231997 := bbase (se 3 (by rfl) ⟨793499, by rfl⟩ : syracuseStep 4231997 = 1586999) (by norm_num)
theorem B4518749 : Blo 1879141 4518749 := bbase (se 3 (by rfl) ⟨847265, by rfl⟩ : syracuseStep 4518749 = 1694531) (by norm_num)
theorem B2257789 : Blo 1879141 2257789 := bbase (se 3 (by rfl) ⟨423335, by rfl⟩ : syracuseStep 2257789 = 846671) (by norm_num)
theorem B4232069 : Blo 1879141 4232069 := bbase (se 4 (by rfl) ⟨396756, by rfl⟩ : syracuseStep 4232069 = 793513) (by norm_num)
theorem B2380681 : Blo 1879141 2380681 := bbase (se 2 (by rfl) ⟨892755, by rfl⟩ : syracuseStep 2380681 = 1785511) (by norm_num)
theorem B5354437 : Blo 1879141 5354437 := bbase (se 4 (by rfl) ⟨501978, by rfl⟩ : syracuseStep 5354437 = 1003957) (by norm_num)
theorem B4232141 : Blo 1879141 4232141 := bbase (se 3 (by rfl) ⟨793526, by rfl⟩ : syracuseStep 4232141 = 1587053) (by norm_num)
theorem B6345701 : Blo 1879141 6345701 := bbase (se 4 (by rfl) ⟨594909, by rfl⟩ : syracuseStep 6345701 = 1189819) (by norm_num)
theorem B3568637 : Blo 1879141 3568637 := bbase (se 3 (by rfl) ⟨669119, by rfl⟩ : syracuseStep 3568637 = 1338239) (by norm_num)
theorem B4232213 : Blo 1879141 4232213 := bbase (se 6 (by rfl) ⟨99192, by rfl⟩ : syracuseStep 4232213 = 198385) (by norm_num)
theorem B2675749 : Blo 1879141 2675749 := bbase (se 4 (by rfl) ⟨250851, by rfl⟩ : syracuseStep 2675749 = 501703) (by norm_num)
theorem B9032789 : Blo 1879141 9032789 := bbase (se 8 (by rfl) ⟨52926, by rfl⟩ : syracuseStep 9032789 = 105853) (by norm_num)
theorem B4232285 : Blo 1879141 4232285 := bbase (se 3 (by rfl) ⟨793553, by rfl⟩ : syracuseStep 4232285 = 1587107) (by norm_num)
theorem B2143345 : Blo 1879141 2143345 := bbase (se 2 (by rfl) ⟨803754, by rfl⟩ : syracuseStep 2143345 = 1607509) (by norm_num)
theorem B4519037 : Blo 1879141 4519037 := bbase (se 3 (by rfl) ⟨847319, by rfl⟩ : syracuseStep 4519037 = 1694639) (by norm_num)
theorem B3568789 : Blo 1879141 3568789 := bbase (se 6 (by rfl) ⟨83643, by rfl⟩ : syracuseStep 3568789 = 167287) (by norm_num)
theorem B4232357 : Blo 1879141 4232357 := bbase (se 4 (by rfl) ⟨396783, by rfl⟩ : syracuseStep 4232357 = 793567) (by norm_num)
theorem B5715125 : Blo 1879141 5715125 := bbase (se 5 (by rfl) ⟨267896, by rfl⟩ : syracuseStep 5715125 = 535793) (by norm_num)
theorem B4232429 : Blo 1879141 4232429 := bbase (se 3 (by rfl) ⟨793580, by rfl⟩ : syracuseStep 4232429 = 1587161) (by norm_num)
theorem B4756765 : Blo 1879141 4756765 := bbase (se 3 (by rfl) ⟨891893, by rfl⟩ : syracuseStep 4756765 = 1783787) (by norm_num)
theorem B4232501 : Blo 1879141 4232501 := bbase (se 5 (by rfl) ⟨198398, by rfl⟩ : syracuseStep 4232501 = 396797) (by norm_num)
theorem B3011909 : Blo 1879141 3011909 := bbase (se 4 (by rfl) ⟨282366, by rfl⟩ : syracuseStep 3011909 = 564733) (by norm_num)
theorem B5797205 : Blo 1879141 5797205 := bbase (se 13 (by rfl) ⟨1061, by rfl⟩ : syracuseStep 5797205 = 2123) (by norm_num)
theorem B4756877 : Blo 1879141 4756877 := bbase (se 3 (by rfl) ⟨891914, by rfl⟩ : syracuseStep 4756877 = 1783829) (by norm_num)
theorem B6346133 : Blo 1879141 6346133 := bbase (se 6 (by rfl) ⟨148737, by rfl⟩ : syracuseStep 6346133 = 297475) (by norm_num)
theorem B2676125 : Blo 1879141 2676125 := bbase (se 3 (by rfl) ⟨501773, by rfl⟩ : syracuseStep 2676125 = 1003547) (by norm_num)
theorem B3569093 : Blo 1879141 3569093 := bbase (se 4 (by rfl) ⟨334602, by rfl⟩ : syracuseStep 3569093 = 669205) (by norm_num)
theorem B21419477 : Blo 1879141 21419477 := bbase (se 7 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 21419477 = 502019) (by norm_num)
theorem B4757069 : Blo 1879141 4757069 := bbase (se 3 (by rfl) ⟨891950, by rfl⟩ : syracuseStep 4757069 = 1783901) (by norm_num)
theorem B34289365 : Blo 1879141 34289365 := bbase (se 7 (by rfl) ⟨401828, by rfl⟩ : syracuseStep 34289365 = 803657) (by norm_num)
theorem B8574677 : Blo 1879141 8574677 := bbase (se 7 (by rfl) ⟨100484, by rfl⟩ : syracuseStep 8574677 = 200969) (by norm_num)
theorem B3012365 : Blo 1879141 3012365 := bbase (se 3 (by rfl) ⟨564818, by rfl⟩ : syracuseStep 3012365 = 1129637) (by norm_num)
theorem B6346565 : Blo 1879141 6346565 := bbase (se 4 (by rfl) ⟨594990, by rfl⟩ : syracuseStep 6346565 = 1189981) (by norm_num)
theorem B4757413 : Blo 1879141 4757413 := bbase (se 4 (by rfl) ⟨446007, by rfl⟩ : syracuseStep 4757413 = 892015) (by norm_num)
theorem B9517013 : Blo 1879141 9517013 := bbase (se 7 (by rfl) ⟨111527, by rfl⟩ : syracuseStep 9517013 = 223055) (by norm_num)
theorem B16062421 : Blo 1879141 16062421 := bbase (se 7 (by rfl) ⟨188231, by rfl⟩ : syracuseStep 16062421 = 376463) (by norm_num)
theorem B3012589 : Blo 1879141 3012589 := bbase (se 3 (by rfl) ⟨564860, by rfl⟩ : syracuseStep 3012589 = 1129721) (by norm_num)
theorem B4757525 : Blo 1879141 4757525 := bbase (se 6 (by rfl) ⟨111504, by rfl⟩ : syracuseStep 4757525 = 223009) (by norm_num)
theorem B3012653 : Blo 1879141 3012653 := bbase (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) (by norm_num)
theorem B4405301 : Blo 1879141 4405301 := bbase (se 5 (by rfl) ⟨206498, by rfl⟩ : syracuseStep 4405301 = 412997) (by norm_num)
theorem B3012781 : Blo 1879141 3012781 := bbase (se 3 (by rfl) ⟨564896, by rfl⟩ : syracuseStep 3012781 = 1129793) (by norm_num)
theorem B2062517 : Blo 1879141 2062517 := bbase (se 5 (by rfl) ⟨96680, by rfl⟩ : syracuseStep 2062517 = 193361) (by norm_num)
theorem B3569845 : Blo 1879141 3569845 := bbase (se 5 (by rfl) ⟨167336, by rfl⟩ : syracuseStep 3569845 = 334673) (by norm_num)
theorem B4757717 : Blo 1879141 4757717 := bbase (se 7 (by rfl) ⟨55754, by rfl⟩ : syracuseStep 4757717 = 111509) (by norm_num)
theorem B3217645 : Blo 1879141 3217645 := bbase (se 3 (by rfl) ⟨603308, by rfl⟩ : syracuseStep 3217645 = 1206617) (by norm_num)
theorem B6346997 : Blo 1879141 6346997 := bbase (se 5 (by rfl) ⟨297515, by rfl⟩ : syracuseStep 6346997 = 595031) (by norm_num)
theorem B2144513 : Blo 1879141 2144513 := bbase (se 2 (by rfl) ⟨804192, by rfl⟩ : syracuseStep 2144513 = 1608385) (by norm_num)
theorem B3389725 : Blo 1879141 3389725 := bbase (se 3 (by rfl) ⟨635573, by rfl⟩ : syracuseStep 3389725 = 1271147) (by norm_num)
theorem B2857253 : Blo 1879141 2857253 := bbase (se 4 (by rfl) ⟨267867, by rfl⟩ : syracuseStep 2857253 = 535735) (by norm_num)
theorem B9034037 : Blo 1879141 9034037 := bbase (se 5 (by rfl) ⟨423470, by rfl⟩ : syracuseStep 9034037 = 846941) (by norm_num)
theorem B4577597 : Blo 1879141 4577597 := bbase (se 3 (by rfl) ⟨858299, by rfl⟩ : syracuseStep 4577597 = 1716599) (by norm_num)
theorem B3569989 : Blo 1879141 3569989 := bbase (se 4 (by rfl) ⟨334686, by rfl⟩ : syracuseStep 3569989 = 669373) (by norm_num)
theorem B19298645 : Blo 1879141 19298645 := bbase (se 10 (by rfl) ⟨28269, by rfl⟩ : syracuseStep 19298645 = 56539) (by norm_num)
theorem B1931749 : Blo 1879141 1931749 := bbase (se 4 (by rfl) ⟨181101, by rfl⟩ : syracuseStep 1931749 = 362203) (by norm_num)
theorem B3570149 : Blo 1879141 3570149 := bbase (se 4 (by rfl) ⟨334701, by rfl⟩ : syracuseStep 3570149 = 669403) (by norm_num)
theorem B7141877 : Blo 1879141 7141877 := bbase (se 5 (by rfl) ⟨334775, by rfl⟩ : syracuseStep 7141877 = 669551) (by norm_num)
theorem B4758061 : Blo 1879141 4758061 := bbase (se 3 (by rfl) ⟨892136, by rfl⟩ : syracuseStep 4758061 = 1784273) (by norm_num)
theorem B5429861 : Blo 1879141 5429861 := bbase (se 4 (by rfl) ⟨509049, by rfl⟩ : syracuseStep 5429861 = 1018099) (by norm_num)
theorem B3570293 : Blo 1879141 3570293 := bbase (se 5 (by rfl) ⟨167357, by rfl⟩ : syracuseStep 3570293 = 334715) (by norm_num)
theorem B2259581 : Blo 1879141 2259581 := bbase (se 3 (by rfl) ⟨423671, by rfl⟩ : syracuseStep 2259581 = 847343) (by norm_num)
theorem B4758173 : Blo 1879141 4758173 := bbase (se 3 (by rfl) ⟨892157, by rfl⟩ : syracuseStep 4758173 = 1784315) (by norm_num)
theorem B6347429 : Blo 1879141 6347429 := bbase (se 4 (by rfl) ⟨595071, by rfl⟩ : syracuseStep 6347429 = 1190143) (by norm_num)
theorem B7142165 : Blo 1879141 7142165 := bbase (se 6 (by rfl) ⟨167394, by rfl⟩ : syracuseStep 7142165 = 334789) (by norm_num)
theorem B2677549 : Blo 1879141 2677549 := bbase (se 3 (by rfl) ⟨502040, by rfl⟩ : syracuseStep 2677549 = 1004081) (by norm_num)
theorem B4758365 : Blo 1879141 4758365 := bbase (se 3 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 4758365 = 1784387) (by norm_num)
theorem B2857837 : Blo 1879141 2857837 := bbase (se 3 (by rfl) ⟨535844, by rfl⟩ : syracuseStep 2857837 = 1071689) (by norm_num)
theorem B3570581 : Blo 1879141 3570581 := bbase (se 6 (by rfl) ⟨83685, by rfl⟩ : syracuseStep 3570581 = 167371) (by norm_num)
theorem B2259913 : Blo 1879141 2259913 := bbase (se 2 (by rfl) ⟨847467, by rfl⟩ : syracuseStep 2259913 = 1694935) (by norm_num)
theorem B6773797 : Blo 1879141 6773797 := bbase (se 4 (by rfl) ⟨635043, by rfl⟩ : syracuseStep 6773797 = 1270087) (by norm_num)
theorem B3570733 : Blo 1879141 3570733 := bbase (se 3 (by rfl) ⟨669512, by rfl⟩ : syracuseStep 3570733 = 1339025) (by norm_num)
theorem B15252533 : Blo 1879141 15252533 := bbase (se 5 (by rfl) ⟨714962, by rfl⟩ : syracuseStep 15252533 = 1429925) (by norm_num)
theorem B18070613 : Blo 1879141 18070613 := bbase (se 8 (by rfl) ⟨105882, by rfl⟩ : syracuseStep 18070613 = 211765) (by norm_num)
theorem B13556821 : Blo 1879141 13556821 := bbase (se 8 (by rfl) ⟨79434, by rfl⟩ : syracuseStep 13556821 = 158869) (by norm_num)
theorem B6347861 : Blo 1879141 6347861 := bbase (se 8 (by rfl) ⟨37194, by rfl⟩ : syracuseStep 6347861 = 74389) (by norm_num)
theorem B4758709 : Blo 1879141 4758709 := bbase (se 5 (by rfl) ⟨223064, by rfl⟩ : syracuseStep 4758709 = 446129) (by norm_num)
theorem B9518309 : Blo 1879141 9518309 := bbase (se 4 (by rfl) ⟨892341, by rfl⟩ : syracuseStep 9518309 = 1784683) (by norm_num)
theorem B4758821 : Blo 1879141 4758821 := bbase (se 4 (by rfl) ⟨446139, by rfl⟩ : syracuseStep 4758821 = 892279) (by norm_num)
theorem B3571037 : Blo 1879141 3571037 := bbase (se 3 (by rfl) ⟨669569, by rfl⟩ : syracuseStep 3571037 = 1339139) (by norm_num)
theorem B2678141 : Blo 1879141 2678141 := bbase (se 3 (by rfl) ⟨502151, by rfl⟩ : syracuseStep 2678141 = 1004303) (by norm_num)
theorem B4578725 : Blo 1879141 4578725 := bbase (se 4 (by rfl) ⟨429255, by rfl⟩ : syracuseStep 4578725 = 858511) (by norm_num)
theorem B2678221 : Blo 1879141 2678221 := bbase (se 3 (by rfl) ⟨502166, by rfl⟩ : syracuseStep 2678221 = 1004333) (by norm_num)
theorem B4759013 : Blo 1879141 4759013 := bbase (se 4 (by rfl) ⟨446157, by rfl⟩ : syracuseStep 4759013 = 892315) (by norm_num)
theorem B6348293 : Blo 1879141 6348293 := bbase (se 4 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 6348293 = 1190305) (by norm_num)
theorem B2678341 : Blo 1879141 2678341 := bbase (se 4 (by rfl) ⟨251094, by rfl⟩ : syracuseStep 2678341 = 502189) (by norm_num)
theorem B6020693 : Blo 1879141 6020693 := bbase (se 8 (by rfl) ⟨35277, by rfl⟩ : syracuseStep 6020693 = 70555) (by norm_num)
theorem B4759357 : Blo 1879141 4759357 := bbase (se 3 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 4759357 = 1784759) (by norm_num)
theorem B12042101 : Blo 1879141 12042101 := bbase (se 5 (by rfl) ⟨564473, by rfl⟩ : syracuseStep 12042101 = 1128947) (by norm_num)
theorem B4013965 : Blo 1879141 4013965 := bbase (se 3 (by rfl) ⟨752618, by rfl⟩ : syracuseStep 4013965 = 1505237) (by norm_num)
theorem B16064405 : Blo 1879141 16064405 := bbase (se 6 (by rfl) ⟨376509, by rfl⟩ : syracuseStep 16064405 = 753019) (by norm_num)
theorem B4759469 : Blo 1879141 4759469 := bbase (se 3 (by rfl) ⟨892400, by rfl⟩ : syracuseStep 4759469 = 1784801) (by norm_num)
theorem B6348725 : Blo 1879141 6348725 := bbase (se 5 (by rfl) ⟨297596, by rfl⟩ : syracuseStep 6348725 = 595193) (by norm_num)
theorem B2007013 : Blo 1879141 2007013 := bbase (se 4 (by rfl) ⟨188157, by rfl⟩ : syracuseStep 2007013 = 376315) (by norm_num)
theorem B91455601 : Blo 1879141 91455601 := bstep (se 2 (by rfl) ⟨34295850, by rfl⟩ : syracuseStep 91455601 = 68591701) B68591701
theorem B9519281 : Blo 1879141 9519281 := bstep (se 2 (by rfl) ⟨3569730, by rfl⟩ : syracuseStep 9519281 = 7139461) B7139461
theorem B36126917 : Blo 1879141 36126917 := bstep (se 4 (by rfl) ⟨3386898, by rfl⟩ : syracuseStep 36126917 = 6773797) B6773797
theorem B4014307 : Blo 1879141 4014307 := bstep (se 1 (by rfl) ⟨3010730, by rfl⟩ : syracuseStep 4014307 = 6021461) B6021461
theorem B4759793 : Blo 1879141 4759793 := bstep (se 2 (by rfl) ⟨1784922, by rfl⟩ : syracuseStep 4759793 = 3569845) B3569845
theorem B2007299 : Blo 1879141 2007299 := bstep (se 1 (by rfl) ⟨1505474, by rfl⟩ : syracuseStep 2007299 = 3010949) B3010949
theorem B4759843 : Blo 1879141 4759843 := bstep (se 1 (by rfl) ⟨3569882, by rfl⟩ : syracuseStep 4759843 = 7139765) B7139765
theorem B4890947 : Blo 1879141 4890947 := bstep (se 1 (by rfl) ⟨3668210, by rfl⟩ : syracuseStep 4890947 = 7336421) B7336421
theorem B12050765 : Blo 1879141 12050765 := bstep (se 3 (by rfl) ⟨2259518, by rfl⟩ : syracuseStep 12050765 = 4519037) B4519037
theorem B10854755 : Blo 1879141 10854755 := bstep (se 1 (by rfl) ⟨8141066, by rfl⟩ : syracuseStep 10854755 = 16282133) B16282133
theorem B4071779 : Blo 1879141 4071779 := bstep (se 1 (by rfl) ⟨3053834, by rfl⟩ : syracuseStep 4071779 = 6107669) B6107669
theorem B2007427 : Blo 1879141 2007427 := bstep (se 1 (by rfl) ⟨1505570, by rfl⟩ : syracuseStep 2007427 = 3011141) B3011141
theorem B3260819 : Blo 1879141 3260819 := bstep (se 1 (by rfl) ⟨2445614, by rfl⟩ : syracuseStep 3260819 = 4891229) B4891229
theorem B4759985 : Blo 1879141 4759985 := bstep (se 2 (by rfl) ⟨1784994, by rfl⟩ : syracuseStep 4759985 = 3569989) B3569989
theorem B14107121 : Blo 1879141 14107121 := bstep (se 2 (by rfl) ⟨5290170, by rfl⟩ : syracuseStep 14107121 = 10580341) B10580341
theorem B10707461 : Blo 1879141 10707461 := bstep (se 4 (by rfl) ⟨1003824, by rfl⟩ : syracuseStep 10707461 = 2007649) B2007649
theorem B46989877 : Blo 1879141 46989877 := bstep (se 5 (by rfl) ⟨2202650, by rfl⟩ : syracuseStep 46989877 = 4405301) B4405301
theorem B2114131 : Blo 1879141 2114131 := bstep (se 1 (by rfl) ⟨1585598, by rfl⟩ : syracuseStep 2114131 = 3171197) B3171197
theorem B2818721 : Blo 1879141 2818721 := bstep (se 2 (by rfl) ⟨1057020, by rfl⟩ : syracuseStep 2818721 = 2114041) B2114041
theorem B5718701 : Blo 1879141 5718701 := bstep (se 3 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 5718701 = 2144513) B2144513
theorem B2818739 : Blo 1879141 2818739 := bstep (se 1 (by rfl) ⟨2114054, by rfl⟩ : syracuseStep 2818739 = 4228109) B4228109
theorem B2818769 : Blo 1879141 2818769 := bstep (se 2 (by rfl) ⟨1057038, by rfl⟩ : syracuseStep 2818769 = 2114077) B2114077
theorem B2818787 : Blo 1879141 2818787 := bstep (se 1 (by rfl) ⟨2114090, by rfl⟩ : syracuseStep 2818787 = 4228181) B4228181
theorem B2114275 : Blo 1879141 2114275 := bstep (se 1 (by rfl) ⟨1585706, by rfl⟩ : syracuseStep 2114275 = 3171413) B3171413
theorem B6021859 : Blo 1879141 6021859 := bstep (se 1 (by rfl) ⟨4516394, by rfl⟩ : syracuseStep 6021859 = 9032789) B9032789
theorem B2818817 : Blo 1879141 2818817 := bstep (se 2 (by rfl) ⟨1057056, by rfl⟩ : syracuseStep 2818817 = 2114113) B2114113
theorem B7619341 : Blo 1879141 7619341 := bstep (se 3 (by rfl) ⟨1428626, by rfl⟩ : syracuseStep 7619341 = 2857253) B2857253
theorem B3171089 : Blo 1879141 3171089 := bstep (se 2 (by rfl) ⟨1189158, by rfl⟩ : syracuseStep 3171089 = 2378317) B2378317
theorem B2818835 : Blo 1879141 2818835 := bstep (se 1 (by rfl) ⟨2114126, by rfl⟩ : syracuseStep 2818835 = 4228253) B4228253
theorem B3810083 : Blo 1879141 3810083 := bstep (se 1 (by rfl) ⟨2857562, by rfl⟩ : syracuseStep 3810083 = 5715125) B5715125
theorem B2818865 : Blo 1879141 2818865 := bstep (se 2 (by rfl) ⟨1057074, by rfl⟩ : syracuseStep 2818865 = 2114149) B2114149
theorem B2818883 : Blo 1879141 2818883 := bstep (se 1 (by rfl) ⟨2114162, by rfl⟩ : syracuseStep 2818883 = 4228325) B4228325
theorem B2818913 : Blo 1879141 2818913 := bstep (se 2 (by rfl) ⟨1057092, by rfl⟩ : syracuseStep 2818913 = 2114185) B2114185
theorem B2818931 : Blo 1879141 2818931 := bstep (se 1 (by rfl) ⟨2114198, by rfl⟩ : syracuseStep 2818931 = 4228397) B4228397
theorem B2114419 : Blo 1879141 2114419 := bstep (se 1 (by rfl) ⟨1585814, by rfl⟩ : syracuseStep 2114419 = 3171629) B3171629
theorem B3171217 : Blo 1879141 3171217 := bstep (se 2 (by rfl) ⟨1189206, by rfl⟩ : syracuseStep 3171217 = 2378413) B2378413
theorem B2818961 : Blo 1879141 2818961 := bstep (se 2 (by rfl) ⟨1057110, by rfl⟩ : syracuseStep 2818961 = 2114221) B2114221
theorem B2818979 : Blo 1879141 2818979 := bstep (se 1 (by rfl) ⟨2114234, by rfl⟩ : syracuseStep 2818979 = 4228469) B4228469
theorem B4015025 : Blo 1879141 4015025 := bstep (se 2 (by rfl) ⟨1505634, by rfl⟩ : syracuseStep 4015025 = 3011269) B3011269
theorem B3171251 : Blo 1879141 3171251 := bstep (se 1 (by rfl) ⟨2378438, by rfl⟩ : syracuseStep 3171251 = 4756877) B4756877
theorem B2819009 : Blo 1879141 2819009 := bstep (se 2 (by rfl) ⟨1057128, by rfl⟩ : syracuseStep 2819009 = 2114257) B2114257
theorem B2819027 : Blo 1879141 2819027 := bstep (se 1 (by rfl) ⟨2114270, by rfl⟩ : syracuseStep 2819027 = 4228541) B4228541
theorem B14279651 : Blo 1879141 14279651 := bstep (se 1 (by rfl) ⟨10709738, by rfl⟩ : syracuseStep 14279651 = 21419477) B21419477
theorem B2819057 : Blo 1879141 2819057 := bstep (se 2 (by rfl) ⟨1057146, by rfl⟩ : syracuseStep 2819057 = 2114293) B2114293
theorem B2819075 : Blo 1879141 2819075 := bstep (se 1 (by rfl) ⟨2114306, by rfl⟩ : syracuseStep 2819075 = 4228613) B4228613
theorem B2114563 : Blo 1879141 2114563 := bstep (se 1 (by rfl) ⟨1585922, by rfl⟩ : syracuseStep 2114563 = 3171845) B3171845
theorem B2819105 : Blo 1879141 2819105 := bstep (se 2 (by rfl) ⟨1057164, by rfl⟩ : syracuseStep 2819105 = 2114329) B2114329
theorem B10159139 : Blo 1879141 10159139 := bstep (se 1 (by rfl) ⟨7619354, by rfl⟩ : syracuseStep 10159139 = 15238709) B15238709
theorem B4228145 : Blo 1879141 4228145 := bstep (se 2 (by rfl) ⟨1585554, by rfl⟩ : syracuseStep 4228145 = 3171109) B3171109
theorem B3171379 : Blo 1879141 3171379 := bstep (se 1 (by rfl) ⟨2378534, by rfl⟩ : syracuseStep 3171379 = 4757069) B4757069
theorem B2819123 : Blo 1879141 2819123 := bstep (se 1 (by rfl) ⟨2114342, by rfl⟩ : syracuseStep 2819123 = 4228685) B4228685
theorem B4228163 : Blo 1879141 4228163 := bstep (se 1 (by rfl) ⟨3171122, by rfl⟩ : syracuseStep 4228163 = 6342245) B6342245
theorem B7136333 : Blo 1879141 7136333 := bstep (se 3 (by rfl) ⟨1338062, by rfl⟩ : syracuseStep 7136333 = 2676125) B2676125
theorem B2819153 : Blo 1879141 2819153 := bstep (se 2 (by rfl) ⟨1057182, by rfl⟩ : syracuseStep 2819153 = 2114365) B2114365
theorem B2819171 : Blo 1879141 2819171 := bstep (se 1 (by rfl) ⟨2114378, by rfl⟩ : syracuseStep 2819171 = 4228757) B4228757
theorem B8029297 : Blo 1879141 8029297 := bstep (se 2 (by rfl) ⟨3010986, by rfl⟩ : syracuseStep 8029297 = 6021973) B6021973
theorem B2819201 : Blo 1879141 2819201 := bstep (se 2 (by rfl) ⟨1057200, by rfl⟩ : syracuseStep 2819201 = 2114401) B2114401
theorem B3810449 : Blo 1879141 3810449 := bstep (se 2 (by rfl) ⟨1428918, by rfl⟩ : syracuseStep 3810449 = 2857837) B2857837
theorem B2819219 : Blo 1879141 2819219 := bstep (se 1 (by rfl) ⟨2114414, by rfl⟩ : syracuseStep 2819219 = 4228829) B4228829
theorem B2114707 : Blo 1879141 2114707 := bstep (se 1 (by rfl) ⟨1586030, by rfl⟩ : syracuseStep 2114707 = 3172061) B3172061
theorem B2819249 : Blo 1879141 2819249 := bstep (se 2 (by rfl) ⟨1057218, by rfl⟩ : syracuseStep 2819249 = 2114437) B2114437
theorem B10708145 : Blo 1879141 10708145 := bstep (se 2 (by rfl) ⟨4015554, by rfl⟩ : syracuseStep 10708145 = 8031109) B8031109
theorem B2008243 : Blo 1879141 2008243 := bstep (se 1 (by rfl) ⟨1506182, by rfl⟩ : syracuseStep 2008243 = 3012365) B3012365
theorem B3171521 : Blo 1879141 3171521 := bstep (se 2 (by rfl) ⟨1189320, by rfl⟩ : syracuseStep 3171521 = 2378641) B2378641
theorem B2819267 : Blo 1879141 2819267 := bstep (se 1 (by rfl) ⟨2114450, by rfl⟩ : syracuseStep 2819267 = 4228901) B4228901
theorem B2819297 : Blo 1879141 2819297 := bstep (se 2 (by rfl) ⟨1057236, by rfl⟩ : syracuseStep 2819297 = 2114473) B2114473
theorem B2819315 : Blo 1879141 2819315 := bstep (se 1 (by rfl) ⟨2114486, by rfl⟩ : syracuseStep 2819315 = 4228973) B4228973
theorem B2819345 : Blo 1879141 2819345 := bstep (se 2 (by rfl) ⟨1057254, by rfl⟩ : syracuseStep 2819345 = 2114509) B2114509
theorem B2819363 : Blo 1879141 2819363 := bstep (se 1 (by rfl) ⟨2114522, by rfl⟩ : syracuseStep 2819363 = 4229045) B4229045
theorem B2114851 : Blo 1879141 2114851 := bstep (se 1 (by rfl) ⟨1586138, by rfl⟩ : syracuseStep 2114851 = 3172277) B3172277
theorem B24102197 : Blo 1879141 24102197 := bstep (se 5 (by rfl) ⟨1129790, by rfl⟩ : syracuseStep 24102197 = 2259581) B2259581
theorem B3171649 : Blo 1879141 3171649 := bstep (se 2 (by rfl) ⟨1189368, by rfl⟩ : syracuseStep 3171649 = 2378737) B2378737
theorem B2819393 : Blo 1879141 2819393 := bstep (se 2 (by rfl) ⟨1057272, by rfl⟩ : syracuseStep 2819393 = 2114545) B2114545
theorem B4228433 : Blo 1879141 4228433 := bstep (se 2 (by rfl) ⟨1585662, by rfl⟩ : syracuseStep 4228433 = 3171325) B3171325
theorem B2819411 : Blo 1879141 2819411 := bstep (se 1 (by rfl) ⟨2114558, by rfl⟩ : syracuseStep 2819411 = 4229117) B4229117
theorem B4228451 : Blo 1879141 4228451 := bstep (se 1 (by rfl) ⟨3171338, by rfl⟩ : syracuseStep 4228451 = 6342677) B6342677
theorem B3171683 : Blo 1879141 3171683 := bstep (se 1 (by rfl) ⟨2378762, by rfl⟩ : syracuseStep 3171683 = 4757525) B4757525
theorem B2819441 : Blo 1879141 2819441 := bstep (se 2 (by rfl) ⟨1057290, by rfl⟩ : syracuseStep 2819441 = 2114581) B2114581
theorem B2819459 : Blo 1879141 2819459 := bstep (se 1 (by rfl) ⟨2114594, by rfl⟩ : syracuseStep 2819459 = 4229189) B4229189
theorem B4760977 : Blo 1879141 4760977 := bstep (se 2 (by rfl) ⟨1785366, by rfl⟩ : syracuseStep 4760977 = 3570733) B3570733
theorem B2819489 : Blo 1879141 2819489 := bstep (se 2 (by rfl) ⟨1057308, by rfl⟩ : syracuseStep 2819489 = 2114617) B2114617
theorem B5293475 : Blo 1879141 5293475 := bstep (se 1 (by rfl) ⟨3970106, by rfl⟩ : syracuseStep 5293475 = 7940213) B7940213
theorem B2819507 : Blo 1879141 2819507 := bstep (se 1 (by rfl) ⟨2114630, by rfl⟩ : syracuseStep 2819507 = 4229261) B4229261
theorem B2114995 : Blo 1879141 2114995 := bstep (se 1 (by rfl) ⟨1586246, by rfl⟩ : syracuseStep 2114995 = 3172493) B3172493
theorem B2819537 : Blo 1879141 2819537 := bstep (se 2 (by rfl) ⟨1057326, by rfl⟩ : syracuseStep 2819537 = 2114653) B2114653
theorem B3171811 : Blo 1879141 3171811 := bstep (se 1 (by rfl) ⟨2378858, by rfl⟩ : syracuseStep 3171811 = 4757717) B4757717
theorem B2819555 : Blo 1879141 2819555 := bstep (se 1 (by rfl) ⟨2114666, by rfl⟩ : syracuseStep 2819555 = 4229333) B4229333
theorem B2819585 : Blo 1879141 2819585 := bstep (se 2 (by rfl) ⟨1057344, by rfl⟩ : syracuseStep 2819585 = 2114689) B2114689
theorem B2819603 : Blo 1879141 2819603 := bstep (se 1 (by rfl) ⟨2114702, by rfl⟩ : syracuseStep 2819603 = 4229405) B4229405
theorem B6022691 : Blo 1879141 6022691 := bstep (se 1 (by rfl) ⟨4517018, by rfl⟩ : syracuseStep 6022691 = 9034037) B9034037
theorem B2819633 : Blo 1879141 2819633 := bstep (se 2 (by rfl) ⟨1057362, by rfl⟩ : syracuseStep 2819633 = 2114725) B2114725
theorem B2819651 : Blo 1879141 2819651 := bstep (se 1 (by rfl) ⟨2114738, by rfl⟩ : syracuseStep 2819651 = 4229477) B4229477
theorem B2115139 : Blo 1879141 2115139 := bstep (se 1 (by rfl) ⟨1586354, by rfl⟩ : syracuseStep 2115139 = 3172709) B3172709
theorem B2819681 : Blo 1879141 2819681 := bstep (se 2 (by rfl) ⟨1057380, by rfl⟩ : syracuseStep 2819681 = 2114761) B2114761
theorem B9520739 : Blo 1879141 9520739 := bstep (se 1 (by rfl) ⟨7140554, by rfl⟩ : syracuseStep 9520739 = 14281109) B14281109
theorem B4228721 : Blo 1879141 4228721 := bstep (se 2 (by rfl) ⟨1585770, by rfl⟩ : syracuseStep 4228721 = 3171541) B3171541
theorem B3171953 : Blo 1879141 3171953 := bstep (se 2 (by rfl) ⟨1189482, by rfl⟩ : syracuseStep 3171953 = 2378965) B2378965
theorem B2819699 : Blo 1879141 2819699 := bstep (se 1 (by rfl) ⟨2114774, by rfl⟩ : syracuseStep 2819699 = 4229549) B4229549
theorem B4228739 : Blo 1879141 4228739 := bstep (se 1 (by rfl) ⟨3171554, by rfl⟩ : syracuseStep 4228739 = 6343109) B6343109
theorem B2819729 : Blo 1879141 2819729 := bstep (se 2 (by rfl) ⟨1057398, by rfl⟩ : syracuseStep 2819729 = 2114797) B2114797
theorem B2819747 : Blo 1879141 2819747 := bstep (se 1 (by rfl) ⟨2114810, by rfl⟩ : syracuseStep 2819747 = 4229621) B4229621
theorem B4761251 : Blo 1879141 4761251 := bstep (se 1 (by rfl) ⟨3570938, by rfl⟩ : syracuseStep 4761251 = 7141877) B7141877
theorem B2541235 : Blo 1879141 2541235 := bstep (se 1 (by rfl) ⟨1905926, by rfl⟩ : syracuseStep 2541235 = 3811853) B3811853
theorem B2819777 : Blo 1879141 2819777 := bstep (se 2 (by rfl) ⟨1057416, by rfl⟩ : syracuseStep 2819777 = 2114833) B2114833
theorem B4015811 : Blo 1879141 4015811 := bstep (se 1 (by rfl) ⟨3011858, by rfl⟩ : syracuseStep 4015811 = 6023717) B6023717
theorem B6342353 : Blo 1879141 6342353 := bstep (se 2 (by rfl) ⟨2378382, by rfl⟩ : syracuseStep 6342353 = 4756765) B4756765
theorem B2819795 : Blo 1879141 2819795 := bstep (se 1 (by rfl) ⟨2114846, by rfl⟩ : syracuseStep 2819795 = 4229693) B4229693
theorem B2115283 : Blo 1879141 2115283 := bstep (se 1 (by rfl) ⟨1586462, by rfl⟩ : syracuseStep 2115283 = 3172925) B3172925
theorem B3172081 : Blo 1879141 3172081 := bstep (se 2 (by rfl) ⟨1189530, by rfl⟩ : syracuseStep 3172081 = 2379061) B2379061
theorem B2819825 : Blo 1879141 2819825 := bstep (se 2 (by rfl) ⟨1057434, by rfl⟩ : syracuseStep 2819825 = 2114869) B2114869
theorem B2819843 : Blo 1879141 2819843 := bstep (se 1 (by rfl) ⟨2114882, by rfl⟩ : syracuseStep 2819843 = 4229765) B4229765
theorem B3172115 : Blo 1879141 3172115 := bstep (se 1 (by rfl) ⟨2379086, by rfl⟩ : syracuseStep 3172115 = 4758173) B4758173
theorem B2819873 : Blo 1879141 2819873 := bstep (se 2 (by rfl) ⟨1057452, by rfl⟩ : syracuseStep 2819873 = 2114905) B2114905
theorem B2819891 : Blo 1879141 2819891 := bstep (se 1 (by rfl) ⟨2114918, by rfl⟩ : syracuseStep 2819891 = 4229837) B4229837
theorem B2819921 : Blo 1879141 2819921 := bstep (se 2 (by rfl) ⟨1057470, by rfl⟩ : syracuseStep 2819921 = 2114941) B2114941
theorem B2819939 : Blo 1879141 2819939 := bstep (se 1 (by rfl) ⟨2114954, by rfl⟩ : syracuseStep 2819939 = 4229909) B4229909
theorem B2115427 : Blo 1879141 2115427 := bstep (se 1 (by rfl) ⟨1586570, by rfl⟩ : syracuseStep 2115427 = 3173141) B3173141
theorem B4761443 : Blo 1879141 4761443 := bstep (se 1 (by rfl) ⟨3571082, by rfl⟩ : syracuseStep 4761443 = 7142165) B7142165
theorem B19302257 : Blo 1879141 19302257 := bstep (se 2 (by rfl) ⟨7238346, by rfl⟩ : syracuseStep 19302257 = 14476693) B14476693
theorem B2819969 : Blo 1879141 2819969 := bstep (se 2 (by rfl) ⟨1057488, by rfl⟩ : syracuseStep 2819969 = 2114977) B2114977
theorem B10160005 : Blo 1879141 10160005 := bstep (se 4 (by rfl) ⟨952500, by rfl⟩ : syracuseStep 10160005 = 1905001) B1905001
theorem B4229009 : Blo 1879141 4229009 := bstep (se 2 (by rfl) ⟨1585878, by rfl⟩ : syracuseStep 4229009 = 3171757) B3171757
theorem B3172243 : Blo 1879141 3172243 := bstep (se 1 (by rfl) ⟨2379182, by rfl⟩ : syracuseStep 3172243 = 4758365) B4758365
theorem B2819987 : Blo 1879141 2819987 := bstep (se 1 (by rfl) ⟨2114990, by rfl⟩ : syracuseStep 2819987 = 4229981) B4229981
theorem B4229027 : Blo 1879141 4229027 := bstep (se 1 (by rfl) ⟨3171770, by rfl⟩ : syracuseStep 4229027 = 6343541) B6343541
theorem B8144803 : Blo 1879141 8144803 := bstep (se 1 (by rfl) ⟨6108602, by rfl⟩ : syracuseStep 8144803 = 12217205) B12217205
theorem B2820017 : Blo 1879141 2820017 := bstep (se 2 (by rfl) ⟨1057506, by rfl⟩ : syracuseStep 2820017 = 2115013) B2115013
theorem B6023089 : Blo 1879141 6023089 := bstep (se 2 (by rfl) ⟨2258658, by rfl⟩ : syracuseStep 6023089 = 4517317) B4517317
theorem B2820035 : Blo 1879141 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B2820065 : Blo 1879141 2820065 := bstep (se 2 (by rfl) ⟨1057524, by rfl⟩ : syracuseStep 2820065 = 2115049) B2115049
theorem B6023153 : Blo 1879141 6023153 := bstep (se 2 (by rfl) ⟨2258682, by rfl⟩ : syracuseStep 6023153 = 4517365) B4517365
theorem B2820083 : Blo 1879141 2820083 := bstep (se 1 (by rfl) ⟨2115062, by rfl⟩ : syracuseStep 2820083 = 4230125) B4230125
theorem B2115571 : Blo 1879141 2115571 := bstep (se 1 (by rfl) ⟨1586678, by rfl⟩ : syracuseStep 2115571 = 3173357) B3173357
theorem B2820113 : Blo 1879141 2820113 := bstep (se 2 (by rfl) ⟨1057542, by rfl⟩ : syracuseStep 2820113 = 2115085) B2115085
theorem B3172385 : Blo 1879141 3172385 := bstep (se 2 (by rfl) ⟨1189644, by rfl⟩ : syracuseStep 3172385 = 2379289) B2379289
theorem B2820131 : Blo 1879141 2820131 := bstep (se 1 (by rfl) ⟨2115098, by rfl⟩ : syracuseStep 2820131 = 4230197) B4230197
theorem B10168355 : Blo 1879141 10168355 := bstep (se 1 (by rfl) ⟨7626266, by rfl⟩ : syracuseStep 10168355 = 15252533) B15252533
theorem B2820161 : Blo 1879141 2820161 := bstep (se 2 (by rfl) ⟨1057560, by rfl⟩ : syracuseStep 2820161 = 2115121) B2115121
theorem B21407813 : Blo 1879141 21407813 := bstep (se 4 (by rfl) ⟨2006982, by rfl⟩ : syracuseStep 21407813 = 4013965) B4013965
theorem B2820179 : Blo 1879141 2820179 := bstep (se 1 (by rfl) ⟨2115134, by rfl⟩ : syracuseStep 2820179 = 4230269) B4230269
theorem B2820209 : Blo 1879141 2820209 := bstep (se 2 (by rfl) ⟨1057578, by rfl⟩ : syracuseStep 2820209 = 2115157) B2115157
theorem B2820227 : Blo 1879141 2820227 := bstep (se 1 (by rfl) ⟨2115170, by rfl⟩ : syracuseStep 2820227 = 4230341) B4230341
theorem B2115715 : Blo 1879141 2115715 := bstep (se 1 (by rfl) ⟨1586786, by rfl⟩ : syracuseStep 2115715 = 3173573) B3173573
theorem B3172513 : Blo 1879141 3172513 := bstep (se 2 (by rfl) ⟨1189692, by rfl⟩ : syracuseStep 3172513 = 2379385) B2379385
theorem B2820257 : Blo 1879141 2820257 := bstep (se 2 (by rfl) ⟨1057596, by rfl⟩ : syracuseStep 2820257 = 2115193) B2115193
theorem B4229297 : Blo 1879141 4229297 := bstep (se 2 (by rfl) ⟨1585986, by rfl⟩ : syracuseStep 4229297 = 3171973) B3171973
theorem B2820275 : Blo 1879141 2820275 := bstep (se 1 (by rfl) ⟨2115206, by rfl⟩ : syracuseStep 2820275 = 4230413) B4230413
theorem B4229315 : Blo 1879141 4229315 := bstep (se 1 (by rfl) ⟨3171986, by rfl⟩ : syracuseStep 4229315 = 6343973) B6343973
theorem B3172547 : Blo 1879141 3172547 := bstep (se 1 (by rfl) ⟨2379410, by rfl⟩ : syracuseStep 3172547 = 4758821) B4758821
theorem B10168525 : Blo 1879141 10168525 := bstep (se 3 (by rfl) ⟨1906598, by rfl⟩ : syracuseStep 10168525 = 3813197) B3813197
theorem B2820305 : Blo 1879141 2820305 := bstep (se 2 (by rfl) ⟨1057614, by rfl⟩ : syracuseStep 2820305 = 2115229) B2115229
theorem B2820323 : Blo 1879141 2820323 := bstep (se 1 (by rfl) ⟨2115242, by rfl⟩ : syracuseStep 2820323 = 4230485) B4230485
theorem B6342893 : Blo 1879141 6342893 := bstep (se 3 (by rfl) ⟨1189292, by rfl⟩ : syracuseStep 6342893 = 2378585) B2378585
theorem B2820353 : Blo 1879141 2820353 := bstep (se 2 (by rfl) ⟨1057632, by rfl⟩ : syracuseStep 2820353 = 2115265) B2115265
theorem B2820371 : Blo 1879141 2820371 := bstep (se 1 (by rfl) ⟨2115278, by rfl⟩ : syracuseStep 2820371 = 4230557) B4230557
theorem B2115859 : Blo 1879141 2115859 := bstep (se 1 (by rfl) ⟨1586894, by rfl⟩ : syracuseStep 2115859 = 3173789) B3173789
theorem B6342947 : Blo 1879141 6342947 := bstep (se 1 (by rfl) ⟨4757210, by rfl⟩ : syracuseStep 6342947 = 9514421) B9514421
theorem B2820401 : Blo 1879141 2820401 := bstep (se 2 (by rfl) ⟨1057650, by rfl⟩ : syracuseStep 2820401 = 2115301) B2115301
theorem B3172675 : Blo 1879141 3172675 := bstep (se 1 (by rfl) ⟨2379506, by rfl⟩ : syracuseStep 3172675 = 4759013) B4759013
theorem B2820419 : Blo 1879141 2820419 := bstep (se 1 (by rfl) ⟨2115314, by rfl⟩ : syracuseStep 2820419 = 4230629) B4230629
theorem B2820449 : Blo 1879141 2820449 := bstep (se 2 (by rfl) ⟨1057668, by rfl⟩ : syracuseStep 2820449 = 2115337) B2115337
theorem B2820467 : Blo 1879141 2820467 := bstep (se 1 (by rfl) ⟨2115350, by rfl⟩ : syracuseStep 2820467 = 4230701) B4230701
theorem B9521549 : Blo 1879141 9521549 := bstep (se 3 (by rfl) ⟨1785290, by rfl⟩ : syracuseStep 9521549 = 3570581) B3570581
theorem B2820497 : Blo 1879141 2820497 := bstep (se 2 (by rfl) ⟨1057686, by rfl⟩ : syracuseStep 2820497 = 2115373) B2115373
theorem B2820515 : Blo 1879141 2820515 := bstep (se 1 (by rfl) ⟨2115386, by rfl⟩ : syracuseStep 2820515 = 4230773) B4230773
theorem B2116003 : Blo 1879141 2116003 := bstep (se 1 (by rfl) ⟨1587002, by rfl⟩ : syracuseStep 2116003 = 3174005) B3174005
theorem B2410931 : Blo 1879141 2410931 := bstep (se 1 (by rfl) ⟨1808198, by rfl⟩ : syracuseStep 2410931 = 3616397) B3616397
theorem B2820545 : Blo 1879141 2820545 := bstep (se 2 (by rfl) ⟨1057704, by rfl⟩ : syracuseStep 2820545 = 2115409) B2115409
theorem B4229585 : Blo 1879141 4229585 := bstep (se 2 (by rfl) ⟨1586094, by rfl⟩ : syracuseStep 4229585 = 3172189) B3172189
theorem B3172817 : Blo 1879141 3172817 := bstep (se 2 (by rfl) ⟨1189806, by rfl⟩ : syracuseStep 3172817 = 2379613) B2379613
theorem B2820563 : Blo 1879141 2820563 := bstep (se 1 (by rfl) ⟨2115422, by rfl⟩ : syracuseStep 2820563 = 4230845) B4230845
theorem B4229603 : Blo 1879141 4229603 := bstep (se 1 (by rfl) ⟨3172202, by rfl⟩ : syracuseStep 4229603 = 6344405) B6344405
theorem B2820593 : Blo 1879141 2820593 := bstep (se 2 (by rfl) ⟨1057722, by rfl⟩ : syracuseStep 2820593 = 2115445) B2115445
theorem B2820611 : Blo 1879141 2820611 := bstep (se 1 (by rfl) ⟨2115458, by rfl⟩ : syracuseStep 2820611 = 4230917) B4230917
theorem B2820641 : Blo 1879141 2820641 := bstep (se 2 (by rfl) ⟨1057740, by rfl⟩ : syracuseStep 2820641 = 2115481) B2115481
theorem B6343217 : Blo 1879141 6343217 := bstep (se 2 (by rfl) ⟨2378706, by rfl⟩ : syracuseStep 6343217 = 4757413) B4757413
theorem B2820659 : Blo 1879141 2820659 := bstep (se 1 (by rfl) ⟨2115494, by rfl⟩ : syracuseStep 2820659 = 4230989) B4230989
theorem B2116147 : Blo 1879141 2116147 := bstep (se 1 (by rfl) ⟨1587110, by rfl⟩ : syracuseStep 2116147 = 3174221) B3174221
theorem B3172945 : Blo 1879141 3172945 := bstep (se 2 (by rfl) ⟨1189854, by rfl⟩ : syracuseStep 3172945 = 2379709) B2379709
theorem B2820689 : Blo 1879141 2820689 := bstep (se 2 (by rfl) ⟨1057758, by rfl⟩ : syracuseStep 2820689 = 2115517) B2115517
theorem B10709603 : Blo 1879141 10709603 := bstep (se 1 (by rfl) ⟨8032202, by rfl⟩ : syracuseStep 10709603 = 16064405) B16064405
theorem B2820707 : Blo 1879141 2820707 := bstep (se 1 (by rfl) ⟨2115530, by rfl⟩ : syracuseStep 2820707 = 4231061) B4231061
theorem B21416561 : Blo 1879141 21416561 := bstep (se 2 (by rfl) ⟨8031210, by rfl⟩ : syracuseStep 21416561 = 16062421) B16062421
theorem B3172979 : Blo 1879141 3172979 := bstep (se 1 (by rfl) ⟨2379734, by rfl⟩ : syracuseStep 3172979 = 4759469) B4759469
theorem B2820737 : Blo 1879141 2820737 := bstep (se 2 (by rfl) ⟨1057776, by rfl⟩ : syracuseStep 2820737 = 2115553) B2115553
theorem B4016785 : Blo 1879141 4016785 := bstep (se 2 (by rfl) ⟨1506294, by rfl⟩ : syracuseStep 4016785 = 3012589) B3012589
theorem B2820755 : Blo 1879141 2820755 := bstep (se 1 (by rfl) ⟨2115566, by rfl⟩ : syracuseStep 2820755 = 4231133) B4231133
theorem B2820785 : Blo 1879141 2820785 := bstep (se 2 (by rfl) ⟨1057794, by rfl⟩ : syracuseStep 2820785 = 2115589) B2115589
theorem B2820803 : Blo 1879141 2820803 := bstep (se 1 (by rfl) ⟨2115602, by rfl⟩ : syracuseStep 2820803 = 4231205) B4231205
theorem B2820833 : Blo 1879141 2820833 := bstep (se 2 (by rfl) ⟨1057812, by rfl⟩ : syracuseStep 2820833 = 2115625) B2115625
theorem B4229873 : Blo 1879141 4229873 := bstep (se 2 (by rfl) ⟨1586202, by rfl⟩ : syracuseStep 4229873 = 3172405) B3172405
theorem B3173107 : Blo 1879141 3173107 := bstep (se 1 (by rfl) ⟨2379830, by rfl⟩ : syracuseStep 3173107 = 4759661) B4759661
theorem B2820851 : Blo 1879141 2820851 := bstep (se 1 (by rfl) ⟨2115638, by rfl⟩ : syracuseStep 2820851 = 4231277) B4231277
theorem B4229891 : Blo 1879141 4229891 := bstep (se 1 (by rfl) ⟨3172418, by rfl⟩ : syracuseStep 4229891 = 6344837) B6344837
theorem B2820881 : Blo 1879141 2820881 := bstep (se 2 (by rfl) ⟨1057830, by rfl⟩ : syracuseStep 2820881 = 2115661) B2115661
theorem B5352227 : Blo 1879141 5352227 := bstep (se 1 (by rfl) ⟨4014170, by rfl⟩ : syracuseStep 5352227 = 8028341) B8028341
theorem B2820899 : Blo 1879141 2820899 := bstep (se 1 (by rfl) ⟨2115674, by rfl⟩ : syracuseStep 2820899 = 4231349) B4231349
theorem B2820929 : Blo 1879141 2820929 := bstep (se 2 (by rfl) ⟨1057848, by rfl⟩ : syracuseStep 2820929 = 2115697) B2115697
theorem B2820947 : Blo 1879141 2820947 := bstep (se 1 (by rfl) ⟨2115710, by rfl⟩ : syracuseStep 2820947 = 4231421) B4231421
theorem B2820977 : Blo 1879141 2820977 := bstep (se 2 (by rfl) ⟨1057866, by rfl⟩ : syracuseStep 2820977 = 2115733) B2115733
theorem B3173249 : Blo 1879141 3173249 := bstep (se 2 (by rfl) ⟨1189968, by rfl⟩ : syracuseStep 3173249 = 2379937) B2379937
theorem B2820995 : Blo 1879141 2820995 := bstep (se 1 (by rfl) ⟨2115746, by rfl⟩ : syracuseStep 2820995 = 4231493) B4231493
theorem B4017041 : Blo 1879141 4017041 := bstep (se 2 (by rfl) ⟨1506390, by rfl⟩ : syracuseStep 4017041 = 3012781) B3012781
theorem B2821025 : Blo 1879141 2821025 := bstep (se 2 (by rfl) ⟨1057884, by rfl⟩ : syracuseStep 2821025 = 2115769) B2115769
theorem B3812273 : Blo 1879141 3812273 := bstep (se 2 (by rfl) ⟨1429602, by rfl⟩ : syracuseStep 3812273 = 2859205) B2859205
theorem B2821043 : Blo 1879141 2821043 := bstep (se 1 (by rfl) ⟨2115782, by rfl⟩ : syracuseStep 2821043 = 4231565) B4231565
theorem B2821073 : Blo 1879141 2821073 := bstep (se 2 (by rfl) ⟨1057902, by rfl⟩ : syracuseStep 2821073 = 2115805) B2115805
theorem B2821091 : Blo 1879141 2821091 := bstep (se 1 (by rfl) ⟨2115818, by rfl⟩ : syracuseStep 2821091 = 4231637) B4231637
theorem B3173377 : Blo 1879141 3173377 := bstep (se 2 (by rfl) ⟨1190016, by rfl⟩ : syracuseStep 3173377 = 2380033) B2380033
theorem B2821121 : Blo 1879141 2821121 := bstep (se 2 (by rfl) ⟨1057920, by rfl⟩ : syracuseStep 2821121 = 2115841) B2115841
theorem B4230161 : Blo 1879141 4230161 := bstep (se 2 (by rfl) ⟨1586310, by rfl⟩ : syracuseStep 4230161 = 3172621) B3172621
theorem B2821139 : Blo 1879141 2821139 := bstep (se 1 (by rfl) ⟨2115854, by rfl⟩ : syracuseStep 2821139 = 4231709) B4231709
theorem B4230179 : Blo 1879141 4230179 := bstep (se 1 (by rfl) ⟨3172634, by rfl⟩ : syracuseStep 4230179 = 6345269) B6345269
theorem B3173411 : Blo 1879141 3173411 := bstep (se 1 (by rfl) ⟨2380058, by rfl⟩ : syracuseStep 3173411 = 4760117) B4760117
theorem B2821169 : Blo 1879141 2821169 := bstep (se 2 (by rfl) ⟨1057938, by rfl⟩ : syracuseStep 2821169 = 2115877) B2115877
theorem B2378803 : Blo 1879141 2378803 := bstep (se 1 (by rfl) ⟨1784102, by rfl⟩ : syracuseStep 2378803 = 3568205) B3568205
theorem B2821187 : Blo 1879141 2821187 := bstep (se 1 (by rfl) ⟨2115890, by rfl⟩ : syracuseStep 2821187 = 4231781) B4231781
theorem B6343757 : Blo 1879141 6343757 := bstep (se 3 (by rfl) ⟨1189454, by rfl⟩ : syracuseStep 6343757 = 2378909) B2378909
theorem B2821217 : Blo 1879141 2821217 := bstep (se 2 (by rfl) ⟨1057956, by rfl⟩ : syracuseStep 2821217 = 2115913) B2115913
theorem B9514097 : Blo 1879141 9514097 := bstep (se 2 (by rfl) ⟨3567786, by rfl⟩ : syracuseStep 9514097 = 7135573) B7135573
theorem B1879155 : Blo 1879141 1879155 := bstep (se 1 (by rfl) ⟨1409366, by rfl⟩ : syracuseStep 1879155 = 2818733) B2818733
theorem B2821235 : Blo 1879141 2821235 := bstep (se 1 (by rfl) ⟨2115926, by rfl⟩ : syracuseStep 2821235 = 4231853) B4231853
theorem B1879171 : Blo 1879141 1879171 := bstep (se 1 (by rfl) ⟨1409378, by rfl⟩ : syracuseStep 1879171 = 2818757) B2818757
theorem B6343811 : Blo 1879141 6343811 := bstep (se 1 (by rfl) ⟨4757858, by rfl⟩ : syracuseStep 6343811 = 9515717) B9515717
theorem B5500045 : Blo 1879141 5500045 := bstep (se 3 (by rfl) ⟨1031258, by rfl⟩ : syracuseStep 5500045 = 2062517) B2062517
theorem B1879187 : Blo 1879141 1879187 := bstep (se 1 (by rfl) ⟨1409390, by rfl⟩ : syracuseStep 1879187 = 2818781) B2818781
theorem B2378899 : Blo 1879141 2378899 := bstep (se 1 (by rfl) ⟨1784174, by rfl⟩ : syracuseStep 2378899 = 3568349) B3568349
theorem B2821265 : Blo 1879141 2821265 := bstep (se 2 (by rfl) ⟨1057974, by rfl⟩ : syracuseStep 2821265 = 2115949) B2115949
theorem B1879203 : Blo 1879141 1879203 := bstep (se 1 (by rfl) ⟨1409402, by rfl⟩ : syracuseStep 1879203 = 2818805) B2818805
theorem B3173539 : Blo 1879141 3173539 := bstep (se 1 (by rfl) ⟨2380154, by rfl⟩ : syracuseStep 3173539 = 4760309) B4760309
theorem B2821283 : Blo 1879141 2821283 := bstep (se 1 (by rfl) ⟨2115962, by rfl⟩ : syracuseStep 2821283 = 4231925) B4231925
theorem B1879219 : Blo 1879141 1879219 := bstep (se 1 (by rfl) ⟨1409414, by rfl⟩ : syracuseStep 1879219 = 2818829) B2818829
theorem B2821313 : Blo 1879141 2821313 := bstep (se 2 (by rfl) ⟨1057992, by rfl⟩ : syracuseStep 2821313 = 2115985) B2115985
theorem B1879235 : Blo 1879141 1879235 := bstep (se 1 (by rfl) ⟨1409426, by rfl⟩ : syracuseStep 1879235 = 2818853) B2818853
theorem B1879251 : Blo 1879141 1879251 := bstep (se 1 (by rfl) ⟨1409438, by rfl⟩ : syracuseStep 1879251 = 2818877) B2818877
theorem B2821331 : Blo 1879141 2821331 := bstep (se 1 (by rfl) ⟨2115998, by rfl⟩ : syracuseStep 2821331 = 4231997) B4231997
theorem B1879267 : Blo 1879141 1879267 := bstep (se 1 (by rfl) ⟨1409450, by rfl⟩ : syracuseStep 1879267 = 2818901) B2818901
theorem B2821361 : Blo 1879141 2821361 := bstep (se 2 (by rfl) ⟨1058010, by rfl⟩ : syracuseStep 2821361 = 2116021) B2116021
theorem B1879283 : Blo 1879141 1879283 := bstep (se 1 (by rfl) ⟨1409462, by rfl⟩ : syracuseStep 1879283 = 2818925) B2818925
theorem B1879299 : Blo 1879141 1879299 := bstep (se 1 (by rfl) ⟨1409474, by rfl⟩ : syracuseStep 1879299 = 2818949) B2818949
theorem B2821379 : Blo 1879141 2821379 := bstep (se 1 (by rfl) ⟨2116034, by rfl⟩ : syracuseStep 2821379 = 4232069) B4232069
theorem B1879315 : Blo 1879141 1879315 := bstep (se 1 (by rfl) ⟨1409486, by rfl⟩ : syracuseStep 1879315 = 2818973) B2818973
theorem B2821409 : Blo 1879141 2821409 := bstep (se 2 (by rfl) ⟨1058028, by rfl⟩ : syracuseStep 2821409 = 2116057) B2116057
theorem B1879331 : Blo 1879141 1879331 := bstep (se 1 (by rfl) ⟨1409498, by rfl⟩ : syracuseStep 1879331 = 2818997) B2818997
theorem B4230449 : Blo 1879141 4230449 := bstep (se 2 (by rfl) ⟨1586418, by rfl⟩ : syracuseStep 4230449 = 3172837) B3172837
theorem B3173681 : Blo 1879141 3173681 := bstep (se 2 (by rfl) ⟨1190130, by rfl⟩ : syracuseStep 3173681 = 2380261) B2380261
theorem B1879347 : Blo 1879141 1879347 := bstep (se 1 (by rfl) ⟨1409510, by rfl⟩ : syracuseStep 1879347 = 2819021) B2819021
theorem B2821427 : Blo 1879141 2821427 := bstep (se 1 (by rfl) ⟨2116070, by rfl⟩ : syracuseStep 2821427 = 4232141) B4232141
theorem B1879363 : Blo 1879141 1879363 := bstep (se 1 (by rfl) ⟨1409522, by rfl⟩ : syracuseStep 1879363 = 2819045) B2819045
theorem B4230467 : Blo 1879141 4230467 := bstep (se 1 (by rfl) ⟨3172850, by rfl⟩ : syracuseStep 4230467 = 6345701) B6345701
theorem B2821457 : Blo 1879141 2821457 := bstep (se 2 (by rfl) ⟨1058046, by rfl⟩ : syracuseStep 2821457 = 2116093) B2116093
theorem B1879379 : Blo 1879141 1879379 := bstep (se 1 (by rfl) ⟨1409534, by rfl⟩ : syracuseStep 1879379 = 2819069) B2819069
theorem B1879395 : Blo 1879141 1879395 := bstep (se 1 (by rfl) ⟨1409546, by rfl⟩ : syracuseStep 1879395 = 2819093) B2819093
theorem B2821475 : Blo 1879141 2821475 := bstep (se 1 (by rfl) ⟨2116106, by rfl⟩ : syracuseStep 2821475 = 4232213) B4232213
theorem B4287857 : Blo 1879141 4287857 := bstep (se 2 (by rfl) ⟨1607946, by rfl⟩ : syracuseStep 4287857 = 3215893) B3215893
theorem B1879411 : Blo 1879141 1879411 := bstep (se 1 (by rfl) ⟨1409558, by rfl⟩ : syracuseStep 1879411 = 2819117) B2819117
theorem B1879427 : Blo 1879141 1879427 := bstep (se 1 (by rfl) ⟨1409570, by rfl⟩ : syracuseStep 1879427 = 2819141) B2819141
theorem B2821505 : Blo 1879141 2821505 := bstep (se 2 (by rfl) ⟨1058064, by rfl⟩ : syracuseStep 2821505 = 2116129) B2116129
theorem B6344081 : Blo 1879141 6344081 := bstep (se 2 (by rfl) ⟨2379030, by rfl⟩ : syracuseStep 6344081 = 4758061) B4758061
theorem B1879443 : Blo 1879141 1879443 := bstep (se 1 (by rfl) ⟨1409582, by rfl⟩ : syracuseStep 1879443 = 2819165) B2819165
theorem B2821523 : Blo 1879141 2821523 := bstep (se 1 (by rfl) ⟨2116142, by rfl⟩ : syracuseStep 2821523 = 4232285) B4232285
theorem B1879459 : Blo 1879141 1879459 := bstep (se 1 (by rfl) ⟨1409594, by rfl⟩ : syracuseStep 1879459 = 2819189) B2819189
theorem B3173809 : Blo 1879141 3173809 := bstep (se 2 (by rfl) ⟨1190178, by rfl⟩ : syracuseStep 3173809 = 2380357) B2380357
theorem B2821553 : Blo 1879141 2821553 := bstep (se 2 (by rfl) ⟨1058082, by rfl⟩ : syracuseStep 2821553 = 2116165) B2116165
theorem B1879475 : Blo 1879141 1879475 := bstep (se 1 (by rfl) ⟨1409606, by rfl⟩ : syracuseStep 1879475 = 2819213) B2819213
theorem B1879491 : Blo 1879141 1879491 := bstep (se 1 (by rfl) ⟨1409618, by rfl⟩ : syracuseStep 1879491 = 2819237) B2819237
theorem B2821571 : Blo 1879141 2821571 := bstep (se 1 (by rfl) ⟨2116178, by rfl⟩ : syracuseStep 2821571 = 4232357) B4232357
theorem B1879507 : Blo 1879141 1879507 := bstep (se 1 (by rfl) ⟨1409630, by rfl⟩ : syracuseStep 1879507 = 2819261) B2819261
theorem B3173843 : Blo 1879141 3173843 := bstep (se 1 (by rfl) ⟨2380382, by rfl⟩ : syracuseStep 3173843 = 4760765) B4760765
theorem B2821601 : Blo 1879141 2821601 := bstep (se 2 (by rfl) ⟨1058100, by rfl⟩ : syracuseStep 2821601 = 2116201) B2116201
theorem B1879523 : Blo 1879141 1879523 := bstep (se 1 (by rfl) ⟨1409642, by rfl⟩ : syracuseStep 1879523 = 2819285) B2819285
theorem B1879539 : Blo 1879141 1879539 := bstep (se 1 (by rfl) ⟨1409654, by rfl⟩ : syracuseStep 1879539 = 2819309) B2819309
theorem B2821619 : Blo 1879141 2821619 := bstep (se 1 (by rfl) ⟨2116214, by rfl⟩ : syracuseStep 2821619 = 4232429) B4232429
theorem B1879555 : Blo 1879141 1879555 := bstep (se 1 (by rfl) ⟨1409666, by rfl⟩ : syracuseStep 1879555 = 2819333) B2819333
theorem B2821649 : Blo 1879141 2821649 := bstep (se 2 (by rfl) ⟨1058118, by rfl⟩ : syracuseStep 2821649 = 2116237) B2116237
theorem B1879571 : Blo 1879141 1879571 := bstep (se 1 (by rfl) ⟨1409678, by rfl⟩ : syracuseStep 1879571 = 2819357) B2819357
theorem B1879587 : Blo 1879141 1879587 := bstep (se 1 (by rfl) ⟨1409690, by rfl⟩ : syracuseStep 1879587 = 2819381) B2819381
theorem B2821667 : Blo 1879141 2821667 := bstep (se 1 (by rfl) ⟨2116250, by rfl⟩ : syracuseStep 2821667 = 4232501) B4232501
theorem B3386929 : Blo 1879141 3386929 := bstep (se 2 (by rfl) ⟨1270098, by rfl⟩ : syracuseStep 3386929 = 2540197) B2540197
theorem B1879603 : Blo 1879141 1879603 := bstep (se 1 (by rfl) ⟨1409702, by rfl⟩ : syracuseStep 1879603 = 2819405) B2819405
theorem B2821697 : Blo 1879141 2821697 := bstep (se 2 (by rfl) ⟨1058136, by rfl⟩ : syracuseStep 2821697 = 2116273) B2116273
theorem B1879619 : Blo 1879141 1879619 := bstep (se 1 (by rfl) ⟨1409714, by rfl⟩ : syracuseStep 1879619 = 2819429) B2819429
theorem B5353037 : Blo 1879141 5353037 := bstep (se 3 (by rfl) ⟨1003694, by rfl⟩ : syracuseStep 5353037 = 2007389) B2007389
theorem B4230737 : Blo 1879141 4230737 := bstep (se 2 (by rfl) ⟨1586526, by rfl⟩ : syracuseStep 4230737 = 3173053) B3173053
theorem B1879635 : Blo 1879141 1879635 := bstep (se 1 (by rfl) ⟨1409726, by rfl⟩ : syracuseStep 1879635 = 2819453) B2819453
theorem B3173971 : Blo 1879141 3173971 := bstep (se 1 (by rfl) ⟨2380478, by rfl⟩ : syracuseStep 3173971 = 4760957) B4760957
theorem B1879651 : Blo 1879141 1879651 := bstep (se 1 (by rfl) ⟨1409738, by rfl⟩ : syracuseStep 1879651 = 2819477) B2819477
theorem B4230755 : Blo 1879141 4230755 := bstep (se 1 (by rfl) ⟨3173066, by rfl⟩ : syracuseStep 4230755 = 6346133) B6346133
theorem B1879667 : Blo 1879141 1879667 := bstep (se 1 (by rfl) ⟨1409750, by rfl⟩ : syracuseStep 1879667 = 2819501) B2819501
theorem B1879683 : Blo 1879141 1879683 := bstep (se 1 (by rfl) ⟨1409762, by rfl⟩ : syracuseStep 1879683 = 2819525) B2819525
theorem B2379395 : Blo 1879141 2379395 := bstep (se 1 (by rfl) ⟨1784546, by rfl⟩ : syracuseStep 2379395 = 3569093) B3569093
theorem B3010193 : Blo 1879141 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B1879699 : Blo 1879141 1879699 := bstep (se 1 (by rfl) ⟨1409774, by rfl⟩ : syracuseStep 1879699 = 2819549) B2819549
theorem B1879715 : Blo 1879141 1879715 := bstep (se 1 (by rfl) ⟨1409786, by rfl⟩ : syracuseStep 1879715 = 2819573) B2819573
theorem B1879731 : Blo 1879141 1879731 := bstep (se 1 (by rfl) ⟨1409798, by rfl⟩ : syracuseStep 1879731 = 2819597) B2819597
theorem B1879747 : Blo 1879141 1879747 := bstep (se 1 (by rfl) ⟨1409810, by rfl⟩ : syracuseStep 1879747 = 2819621) B2819621
theorem B1879763 : Blo 1879141 1879763 := bstep (se 1 (by rfl) ⟨1409822, by rfl⟩ : syracuseStep 1879763 = 2819645) B2819645
theorem B3174113 : Blo 1879141 3174113 := bstep (se 2 (by rfl) ⟨1190292, by rfl⟩ : syracuseStep 3174113 = 2380585) B2380585
theorem B1879779 : Blo 1879141 1879779 := bstep (se 1 (by rfl) ⟨1409834, by rfl⟩ : syracuseStep 1879779 = 2819669) B2819669
theorem B8367857 : Blo 1879141 8367857 := bstep (se 2 (by rfl) ⟨3137946, by rfl⟩ : syracuseStep 8367857 = 6275893) B6275893
theorem B1879795 : Blo 1879141 1879795 := bstep (se 1 (by rfl) ⟨1409846, by rfl⟩ : syracuseStep 1879795 = 2819693) B2819693
theorem B1879811 : Blo 1879141 1879811 := bstep (se 1 (by rfl) ⟨1409858, by rfl⟩ : syracuseStep 1879811 = 2819717) B2819717
theorem B5353229 : Blo 1879141 5353229 := bstep (se 3 (by rfl) ⟨1003730, by rfl⟩ : syracuseStep 5353229 = 2007461) B2007461
theorem B12209933 : Blo 1879141 12209933 := bstep (se 3 (by rfl) ⟨2289362, by rfl⟩ : syracuseStep 12209933 = 4578725) B4578725
theorem B1879827 : Blo 1879141 1879827 := bstep (se 1 (by rfl) ⟨1409870, by rfl⟩ : syracuseStep 1879827 = 2819741) B2819741
theorem B1879843 : Blo 1879141 1879843 := bstep (se 1 (by rfl) ⟨1409882, by rfl⟩ : syracuseStep 1879843 = 2819765) B2819765
theorem B1879859 : Blo 1879141 1879859 := bstep (se 1 (by rfl) ⟨1409894, by rfl⟩ : syracuseStep 1879859 = 2819789) B2819789
theorem B1879875 : Blo 1879141 1879875 := bstep (se 1 (by rfl) ⟨1409906, by rfl⟩ : syracuseStep 1879875 = 2819813) B2819813
theorem B13553477 : Blo 1879141 13553477 := bstep (se 4 (by rfl) ⟨1270638, by rfl⟩ : syracuseStep 13553477 = 2541277) B2541277
theorem B3010385 : Blo 1879141 3010385 := bstep (se 2 (by rfl) ⟨1128894, by rfl⟩ : syracuseStep 3010385 = 2257789) B2257789
theorem B3387217 : Blo 1879141 3387217 := bstep (se 2 (by rfl) ⟨1270206, by rfl⟩ : syracuseStep 3387217 = 2540413) B2540413
theorem B1879891 : Blo 1879141 1879891 := bstep (se 1 (by rfl) ⟨1409918, by rfl⟩ : syracuseStep 1879891 = 2819837) B2819837
theorem B3174241 : Blo 1879141 3174241 := bstep (se 2 (by rfl) ⟨1190340, by rfl⟩ : syracuseStep 3174241 = 2380681) B2380681
theorem B1879907 : Blo 1879141 1879907 := bstep (se 1 (by rfl) ⟨1409930, by rfl⟩ : syracuseStep 1879907 = 2819861) B2819861
theorem B4231025 : Blo 1879141 4231025 := bstep (se 2 (by rfl) ⟨1586634, by rfl⟩ : syracuseStep 4231025 = 3173269) B3173269
theorem B1879923 : Blo 1879141 1879923 := bstep (se 1 (by rfl) ⟨1409942, by rfl⟩ : syracuseStep 1879923 = 2819885) B2819885
theorem B1879939 : Blo 1879141 1879939 := bstep (se 1 (by rfl) ⟨1409954, by rfl⟩ : syracuseStep 1879939 = 2819909) B2819909
theorem B4231043 : Blo 1879141 4231043 := bstep (se 1 (by rfl) ⟨3173282, by rfl⟩ : syracuseStep 4231043 = 6346565) B6346565
theorem B3174275 : Blo 1879141 3174275 := bstep (se 1 (by rfl) ⟨2380706, by rfl⟩ : syracuseStep 3174275 = 4761413) B4761413
theorem B1879955 : Blo 1879141 1879955 := bstep (se 1 (by rfl) ⟨1409966, by rfl⟩ : syracuseStep 1879955 = 2819933) B2819933
theorem B1879971 : Blo 1879141 1879971 := bstep (se 1 (by rfl) ⟨1409978, by rfl⟩ : syracuseStep 1879971 = 2819957) B2819957
theorem B6344621 : Blo 1879141 6344621 := bstep (se 3 (by rfl) ⟨1189616, by rfl⟩ : syracuseStep 6344621 = 2379233) B2379233
theorem B7139249 : Blo 1879141 7139249 := bstep (se 2 (by rfl) ⟨2677218, by rfl⟩ : syracuseStep 7139249 = 5354437) B5354437
theorem B1879987 : Blo 1879141 1879987 := bstep (se 1 (by rfl) ⟨1409990, by rfl⟩ : syracuseStep 1879987 = 2819981) B2819981
theorem B1880003 : Blo 1879141 1880003 := bstep (se 1 (by rfl) ⟨1410002, by rfl⟩ : syracuseStep 1880003 = 2820005) B2820005
theorem B1880019 : Blo 1879141 1880019 := bstep (se 1 (by rfl) ⟨1410014, by rfl⟩ : syracuseStep 1880019 = 2820029) B2820029
theorem B6344675 : Blo 1879141 6344675 := bstep (se 1 (by rfl) ⟨4758506, by rfl⟩ : syracuseStep 6344675 = 9517013) B9517013
theorem B1880035 : Blo 1879141 1880035 := bstep (se 1 (by rfl) ⟨1410026, by rfl⟩ : syracuseStep 1880035 = 2820053) B2820053
theorem B1880051 : Blo 1879141 1880051 := bstep (se 1 (by rfl) ⟨1410038, by rfl⟩ : syracuseStep 1880051 = 2820077) B2820077
theorem B1880067 : Blo 1879141 1880067 := bstep (se 1 (by rfl) ⟨1410050, by rfl⟩ : syracuseStep 1880067 = 2820101) B2820101
theorem B3174403 : Blo 1879141 3174403 := bstep (se 1 (by rfl) ⟨2380802, by rfl⟩ : syracuseStep 3174403 = 4761605) B4761605
theorem B1880083 : Blo 1879141 1880083 := bstep (se 1 (by rfl) ⟨1410062, by rfl⟩ : syracuseStep 1880083 = 2820125) B2820125
theorem B1880099 : Blo 1879141 1880099 := bstep (se 1 (by rfl) ⟨1410074, by rfl⟩ : syracuseStep 1880099 = 2820149) B2820149
theorem B3567665 : Blo 1879141 3567665 := bstep (se 2 (by rfl) ⟨1337874, by rfl⟩ : syracuseStep 3567665 = 2675749) B2675749
theorem B1880115 : Blo 1879141 1880115 := bstep (se 1 (by rfl) ⟨1410086, by rfl⟩ : syracuseStep 1880115 = 2820173) B2820173
theorem B1880131 : Blo 1879141 1880131 := bstep (se 1 (by rfl) ⟨1410098, by rfl⟩ : syracuseStep 1880131 = 2820197) B2820197
theorem B1880147 : Blo 1879141 1880147 := bstep (se 1 (by rfl) ⟨1410110, by rfl⟩ : syracuseStep 1880147 = 2820221) B2820221
theorem B1880163 : Blo 1879141 1880163 := bstep (se 1 (by rfl) ⟨1410122, by rfl⟩ : syracuseStep 1880163 = 2820245) B2820245
theorem B5148785 : Blo 1879141 5148785 := bstep (se 2 (by rfl) ⟨1930794, by rfl⟩ : syracuseStep 5148785 = 3861589) B3861589
theorem B18075761 : Blo 1879141 18075761 := bstep (se 2 (by rfl) ⟨6778410, by rfl⟩ : syracuseStep 18075761 = 13556821) B13556821
theorem B1880179 : Blo 1879141 1880179 := bstep (se 1 (by rfl) ⟨1410134, by rfl⟩ : syracuseStep 1880179 = 2820269) B2820269
theorem B1880195 : Blo 1879141 1880195 := bstep (se 1 (by rfl) ⟨1410146, by rfl⟩ : syracuseStep 1880195 = 2820293) B2820293
theorem B4231313 : Blo 1879141 4231313 := bstep (se 2 (by rfl) ⟨1586742, by rfl⟩ : syracuseStep 4231313 = 3173485) B3173485
theorem B1880211 : Blo 1879141 1880211 := bstep (se 1 (by rfl) ⟨1410158, by rfl⟩ : syracuseStep 1880211 = 2820317) B2820317
theorem B1880227 : Blo 1879141 1880227 := bstep (se 1 (by rfl) ⟨1410170, by rfl⟩ : syracuseStep 1880227 = 2820341) B2820341
theorem B4231331 : Blo 1879141 4231331 := bstep (se 1 (by rfl) ⟨3173498, by rfl⟩ : syracuseStep 4231331 = 6346997) B6346997
theorem B1880243 : Blo 1879141 1880243 := bstep (se 1 (by rfl) ⟨1410182, by rfl⟩ : syracuseStep 1880243 = 2820365) B2820365
theorem B1880259 : Blo 1879141 1880259 := bstep (se 1 (by rfl) ⟨1410194, by rfl⟩ : syracuseStep 1880259 = 2820389) B2820389
theorem B22876357 : Blo 1879141 22876357 := bstep (se 4 (by rfl) ⟨2144658, by rfl⟩ : syracuseStep 22876357 = 4289317) B4289317
theorem B9646285 : Blo 1879141 9646285 := bstep (se 3 (by rfl) ⟨1808678, by rfl⟩ : syracuseStep 9646285 = 3617357) B3617357
theorem B7057613 : Blo 1879141 7057613 := bstep (se 3 (by rfl) ⟨1323302, by rfl⟩ : syracuseStep 7057613 = 2646605) B2646605
theorem B5025997 : Blo 1879141 5025997 := bstep (se 3 (by rfl) ⟨942374, by rfl⟩ : syracuseStep 5025997 = 1884749) B1884749
theorem B3051731 : Blo 1879141 3051731 := bstep (se 1 (by rfl) ⟨2288798, by rfl⟩ : syracuseStep 3051731 = 4577597) B4577597
theorem B1880275 : Blo 1879141 1880275 := bstep (se 1 (by rfl) ⟨1410206, by rfl⟩ : syracuseStep 1880275 = 2820413) B2820413
theorem B1880291 : Blo 1879141 1880291 := bstep (se 1 (by rfl) ⟨1410218, by rfl⟩ : syracuseStep 1880291 = 2820437) B2820437
theorem B12865763 : Blo 1879141 12865763 := bstep (se 1 (by rfl) ⟨9649322, by rfl⟩ : syracuseStep 12865763 = 19298645) B19298645
theorem B6344945 : Blo 1879141 6344945 := bstep (se 2 (by rfl) ⟨2379354, by rfl⟩ : syracuseStep 6344945 = 4758709) B4758709
theorem B1880307 : Blo 1879141 1880307 := bstep (se 1 (by rfl) ⟨1410230, by rfl⟩ : syracuseStep 1880307 = 2820461) B2820461
theorem B1880323 : Blo 1879141 1880323 := bstep (se 1 (by rfl) ⟨1410242, by rfl⟩ : syracuseStep 1880323 = 2820485) B2820485
theorem B1880339 : Blo 1879141 1880339 := bstep (se 1 (by rfl) ⟨1410254, by rfl⟩ : syracuseStep 1880339 = 2820509) B2820509
theorem B1880355 : Blo 1879141 1880355 := bstep (se 1 (by rfl) ⟨1410266, by rfl⟩ : syracuseStep 1880355 = 2820533) B2820533
theorem B1880371 : Blo 1879141 1880371 := bstep (se 1 (by rfl) ⟨1410278, by rfl⟩ : syracuseStep 1880371 = 2820557) B2820557
theorem B1880387 : Blo 1879141 1880387 := bstep (se 1 (by rfl) ⟨1410290, by rfl⟩ : syracuseStep 1880387 = 2820581) B2820581
theorem B2380099 : Blo 1879141 2380099 := bstep (se 1 (by rfl) ⟨1785074, by rfl⟩ : syracuseStep 2380099 = 3570149) B3570149
theorem B1880403 : Blo 1879141 1880403 := bstep (se 1 (by rfl) ⟨1410302, by rfl⟩ : syracuseStep 1880403 = 2820605) B2820605
theorem B1880419 : Blo 1879141 1880419 := bstep (se 1 (by rfl) ⟨1410314, by rfl⟩ : syracuseStep 1880419 = 2820629) B2820629
theorem B1880435 : Blo 1879141 1880435 := bstep (se 1 (by rfl) ⟨1410326, by rfl⟩ : syracuseStep 1880435 = 2820653) B2820653
theorem B1880451 : Blo 1879141 1880451 := bstep (se 1 (by rfl) ⟨1410338, by rfl⟩ : syracuseStep 1880451 = 2820677) B2820677
theorem B1880467 : Blo 1879141 1880467 := bstep (se 1 (by rfl) ⟨1410350, by rfl⟩ : syracuseStep 1880467 = 2820701) B2820701
theorem B1880483 : Blo 1879141 1880483 := bstep (se 1 (by rfl) ⟨1410362, by rfl⟩ : syracuseStep 1880483 = 2820725) B2820725
theorem B2380195 : Blo 1879141 2380195 := bstep (se 1 (by rfl) ⟨1785146, by rfl⟩ : syracuseStep 2380195 = 3570293) B3570293
theorem B4231601 : Blo 1879141 4231601 := bstep (se 2 (by rfl) ⟨1586850, by rfl⟩ : syracuseStep 4231601 = 3173701) B3173701
theorem B1880499 : Blo 1879141 1880499 := bstep (se 1 (by rfl) ⟨1410374, by rfl⟩ : syracuseStep 1880499 = 2820749) B2820749
theorem B1880515 : Blo 1879141 1880515 := bstep (se 1 (by rfl) ⟨1410386, by rfl⟩ : syracuseStep 1880515 = 2820773) B2820773
theorem B4231619 : Blo 1879141 4231619 := bstep (se 1 (by rfl) ⟨3173714, by rfl⟩ : syracuseStep 4231619 = 6347429) B6347429
theorem B1880531 : Blo 1879141 1880531 := bstep (se 1 (by rfl) ⟨1410398, by rfl⟩ : syracuseStep 1880531 = 2820797) B2820797
theorem B1880547 : Blo 1879141 1880547 := bstep (se 1 (by rfl) ⟨1410410, by rfl⟩ : syracuseStep 1880547 = 2820821) B2820821
theorem B1880563 : Blo 1879141 1880563 := bstep (se 1 (by rfl) ⟨1410422, by rfl⟩ : syracuseStep 1880563 = 2820845) B2820845
theorem B1880579 : Blo 1879141 1880579 := bstep (se 1 (by rfl) ⟨1410434, by rfl⟩ : syracuseStep 1880579 = 2820869) B2820869
theorem B1880595 : Blo 1879141 1880595 := bstep (se 1 (by rfl) ⟨1410446, by rfl⟩ : syracuseStep 1880595 = 2820893) B2820893
theorem B9515555 : Blo 1879141 9515555 := bstep (se 1 (by rfl) ⟨7136666, by rfl⟩ : syracuseStep 9515555 = 14273333) B14273333
theorem B1880611 : Blo 1879141 1880611 := bstep (se 1 (by rfl) ⟨1410458, by rfl⟩ : syracuseStep 1880611 = 2820917) B2820917
theorem B1880627 : Blo 1879141 1880627 := bstep (se 1 (by rfl) ⟨1410470, by rfl⟩ : syracuseStep 1880627 = 2820941) B2820941
theorem B1880643 : Blo 1879141 1880643 := bstep (se 1 (by rfl) ⟨1410482, by rfl⟩ : syracuseStep 1880643 = 2820965) B2820965
theorem B9032269 : Blo 1879141 9032269 := bstep (se 3 (by rfl) ⟨1693550, by rfl⟩ : syracuseStep 9032269 = 3387101) B3387101
theorem B1880659 : Blo 1879141 1880659 := bstep (se 1 (by rfl) ⟨1410494, by rfl⟩ : syracuseStep 1880659 = 2820989) B2820989
theorem B1880675 : Blo 1879141 1880675 := bstep (se 1 (by rfl) ⟨1410506, by rfl⟩ : syracuseStep 1880675 = 2821013) B2821013
theorem B1880691 : Blo 1879141 1880691 := bstep (se 1 (by rfl) ⟨1410518, by rfl⟩ : syracuseStep 1880691 = 2821037) B2821037
theorem B1880707 : Blo 1879141 1880707 := bstep (se 1 (by rfl) ⟨1410530, by rfl⟩ : syracuseStep 1880707 = 2821061) B2821061
theorem B1880723 : Blo 1879141 1880723 := bstep (se 1 (by rfl) ⟨1410542, by rfl⟩ : syracuseStep 1880723 = 2821085) B2821085
theorem B1880739 : Blo 1879141 1880739 := bstep (se 1 (by rfl) ⟨1410554, by rfl⟩ : syracuseStep 1880739 = 2821109) B2821109
theorem B1880755 : Blo 1879141 1880755 := bstep (se 1 (by rfl) ⟨1410566, by rfl⟩ : syracuseStep 1880755 = 2821133) B2821133
theorem B4518595 : Blo 1879141 4518595 := bstep (se 1 (by rfl) ⟨3388946, by rfl⟩ : syracuseStep 4518595 = 6777893) B6777893
theorem B1880771 : Blo 1879141 1880771 := bstep (se 1 (by rfl) ⟨1410578, by rfl⟩ : syracuseStep 1880771 = 2821157) B2821157
theorem B4231889 : Blo 1879141 4231889 := bstep (se 2 (by rfl) ⟨1586958, by rfl⟩ : syracuseStep 4231889 = 3173917) B3173917
theorem B1880787 : Blo 1879141 1880787 := bstep (se 1 (by rfl) ⟨1410590, by rfl⟩ : syracuseStep 1880787 = 2821181) B2821181
theorem B12047075 : Blo 1879141 12047075 := bstep (se 1 (by rfl) ⟨9035306, by rfl⟩ : syracuseStep 12047075 = 18070613) B18070613
theorem B1880803 : Blo 1879141 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B4231907 : Blo 1879141 4231907 := bstep (se 1 (by rfl) ⟨3173930, by rfl⟩ : syracuseStep 4231907 = 6347861) B6347861
theorem B5354221 : Blo 1879141 5354221 := bstep (se 3 (by rfl) ⟨1003916, by rfl⟩ : syracuseStep 5354221 = 2007833) B2007833
theorem B1880819 : Blo 1879141 1880819 := bstep (se 1 (by rfl) ⟨1410614, by rfl⟩ : syracuseStep 1880819 = 2821229) B2821229
theorem B3568387 : Blo 1879141 3568387 := bstep (se 1 (by rfl) ⟨2676290, by rfl⟩ : syracuseStep 3568387 = 5352581) B5352581
theorem B1880835 : Blo 1879141 1880835 := bstep (se 1 (by rfl) ⟨1410626, by rfl⟩ : syracuseStep 1880835 = 2821253) B2821253
theorem B6345485 : Blo 1879141 6345485 := bstep (se 3 (by rfl) ⟨1189778, by rfl⟩ : syracuseStep 6345485 = 2379557) B2379557
theorem B1880851 : Blo 1879141 1880851 := bstep (se 1 (by rfl) ⟨1410638, by rfl⟩ : syracuseStep 1880851 = 2821277) B2821277
theorem B1880867 : Blo 1879141 1880867 := bstep (se 1 (by rfl) ⟨1410650, by rfl⟩ : syracuseStep 1880867 = 2821301) B2821301
theorem B2143027 : Blo 1879141 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B1880883 : Blo 1879141 1880883 := bstep (se 1 (by rfl) ⟨1410662, by rfl⟩ : syracuseStep 1880883 = 2821325) B2821325
theorem B6345539 : Blo 1879141 6345539 := bstep (se 1 (by rfl) ⟨4759154, by rfl⟩ : syracuseStep 6345539 = 9518309) B9518309
theorem B1880899 : Blo 1879141 1880899 := bstep (se 1 (by rfl) ⟨1410674, by rfl⟩ : syracuseStep 1880899 = 2821349) B2821349
theorem B1880915 : Blo 1879141 1880915 := bstep (se 1 (by rfl) ⟨1410686, by rfl⟩ : syracuseStep 1880915 = 2821373) B2821373
theorem B1880931 : Blo 1879141 1880931 := bstep (se 1 (by rfl) ⟨1410698, by rfl⟩ : syracuseStep 1880931 = 2821397) B2821397
theorem B1880947 : Blo 1879141 1880947 := bstep (se 1 (by rfl) ⟨1410710, by rfl⟩ : syracuseStep 1880947 = 2821421) B2821421
theorem B1880963 : Blo 1879141 1880963 := bstep (se 1 (by rfl) ⟨1410722, by rfl⟩ : syracuseStep 1880963 = 2821445) B2821445
theorem B1880979 : Blo 1879141 1880979 := bstep (se 1 (by rfl) ⟨1410734, by rfl⟩ : syracuseStep 1880979 = 2821469) B2821469
theorem B2380691 : Blo 1879141 2380691 := bstep (se 1 (by rfl) ⟨1785518, by rfl⟩ : syracuseStep 2380691 = 3571037) B3571037
theorem B1880995 : Blo 1879141 1880995 := bstep (se 1 (by rfl) ⟨1410746, by rfl⟩ : syracuseStep 1880995 = 2821493) B2821493
theorem B3617713 : Blo 1879141 3617713 := bstep (se 2 (by rfl) ⟨1356642, by rfl⟩ : syracuseStep 3617713 = 2713285) B2713285
theorem B1881011 : Blo 1879141 1881011 := bstep (se 1 (by rfl) ⟨1410758, by rfl⟩ : syracuseStep 1881011 = 2821517) B2821517
theorem B1881027 : Blo 1879141 1881027 := bstep (se 1 (by rfl) ⟨1410770, by rfl⟩ : syracuseStep 1881027 = 2821541) B2821541
theorem B24097733 : Blo 1879141 24097733 := bstep (se 4 (by rfl) ⟨2259162, by rfl⟩ : syracuseStep 24097733 = 4518325) B4518325
theorem B1881043 : Blo 1879141 1881043 := bstep (se 1 (by rfl) ⟨1410782, by rfl⟩ : syracuseStep 1881043 = 2821565) B2821565
theorem B1881059 : Blo 1879141 1881059 := bstep (se 1 (by rfl) ⟨1410794, by rfl⟩ : syracuseStep 1881059 = 2821589) B2821589
theorem B4232177 : Blo 1879141 4232177 := bstep (se 2 (by rfl) ⟨1587066, by rfl⟩ : syracuseStep 4232177 = 3174133) B3174133
theorem B1881075 : Blo 1879141 1881075 := bstep (se 1 (by rfl) ⟨1410806, by rfl⟩ : syracuseStep 1881075 = 2821613) B2821613
theorem B4232195 : Blo 1879141 4232195 := bstep (se 1 (by rfl) ⟨3174146, by rfl⟩ : syracuseStep 4232195 = 6348293) B6348293
theorem B1881091 : Blo 1879141 1881091 := bstep (se 1 (by rfl) ⟨1410818, by rfl⟩ : syracuseStep 1881091 = 2821637) B2821637
theorem B1881107 : Blo 1879141 1881107 := bstep (se 1 (by rfl) ⟨1410830, by rfl⟩ : syracuseStep 1881107 = 2821661) B2821661
theorem B1881123 : Blo 1879141 1881123 := bstep (se 1 (by rfl) ⟨1410842, by rfl⟩ : syracuseStep 1881123 = 2821685) B2821685
theorem B1881139 : Blo 1879141 1881139 := bstep (se 1 (by rfl) ⟨1410854, by rfl⟩ : syracuseStep 1881139 = 2821709) B2821709
theorem B6345809 : Blo 1879141 6345809 := bstep (se 2 (by rfl) ⟨2379678, by rfl⟩ : syracuseStep 6345809 = 4759357) B4759357
theorem B3388529 : Blo 1879141 3388529 := bstep (se 2 (by rfl) ⟨1270698, by rfl⟩ : syracuseStep 3388529 = 2541397) B2541397
theorem B3568835 : Blo 1879141 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B10302661 : Blo 1879141 10302661 := bstep (se 4 (by rfl) ⟨965874, by rfl⟩ : syracuseStep 10302661 = 1931749) B1931749
theorem B4232465 : Blo 1879141 4232465 := bstep (se 2 (by rfl) ⟨1587174, by rfl⟩ : syracuseStep 4232465 = 3174349) B3174349
theorem B4232483 : Blo 1879141 4232483 := bstep (se 1 (by rfl) ⟨3174362, by rfl⟩ : syracuseStep 4232483 = 6348725) B6348725
theorem B2676017 : Blo 1879141 2676017 := bstep (se 2 (by rfl) ⟨1003506, by rfl⟩ : syracuseStep 2676017 = 2007013) B2007013
theorem B9516365 : Blo 1879141 9516365 := bstep (se 3 (by rfl) ⟨1784318, by rfl⟩ : syracuseStep 9516365 = 3568637) B3568637
theorem B7140707 : Blo 1879141 7140707 := bstep (se 1 (by rfl) ⟨5355530, by rfl⟩ : syracuseStep 7140707 = 10711061) B10711061
theorem B3388817 : Blo 1879141 3388817 := bstep (se 2 (by rfl) ⟨1270806, by rfl⟩ : syracuseStep 3388817 = 2541613) B2541613
theorem B3011987 : Blo 1879141 3011987 := bstep (se 1 (by rfl) ⟨2258990, by rfl⟩ : syracuseStep 3011987 = 4517981) B4517981
theorem B8033741 : Blo 1879141 8033741 := bstep (se 3 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 8033741 = 3012653) B3012653
theorem B3569123 : Blo 1879141 3569123 := bstep (se 1 (by rfl) ⟨2676842, by rfl⟩ : syracuseStep 3569123 = 5353685) B5353685
theorem B10851889 : Blo 1879141 10851889 := bstep (se 2 (by rfl) ⟨4069458, by rfl⟩ : syracuseStep 10851889 = 8138917) B8138917
theorem B6346349 : Blo 1879141 6346349 := bstep (se 3 (by rfl) ⟨1189940, by rfl⟩ : syracuseStep 6346349 = 2379881) B2379881
theorem B4290193 : Blo 1879141 4290193 := bstep (se 2 (by rfl) ⟨1608822, by rfl⟩ : syracuseStep 4290193 = 3217645) B3217645
theorem B6346403 : Blo 1879141 6346403 := bstep (se 1 (by rfl) ⟨4759802, by rfl⟩ : syracuseStep 6346403 = 9519605) B9519605
theorem B22869701 : Blo 1879141 22869701 := bstep (se 4 (by rfl) ⟨2144034, by rfl⟩ : syracuseStep 22869701 = 4288069) B4288069
theorem B4757201 : Blo 1879141 4757201 := bstep (se 2 (by rfl) ⟨1783950, by rfl⟩ : syracuseStep 4757201 = 3567901) B3567901
theorem B4519633 : Blo 1879141 4519633 := bstep (se 2 (by rfl) ⟨1694862, by rfl⟩ : syracuseStep 4519633 = 3389725) B3389725
theorem B4757251 : Blo 1879141 4757251 := bstep (se 1 (by rfl) ⟨3567938, by rfl⟩ : syracuseStep 4757251 = 7135877) B7135877
theorem B10712837 : Blo 1879141 10712837 := bstep (se 4 (by rfl) ⟨1004328, by rfl⟩ : syracuseStep 10712837 = 2008657) B2008657
theorem B3012371 : Blo 1879141 3012371 := bstep (se 1 (by rfl) ⟨2259278, by rfl⟩ : syracuseStep 3012371 = 4518557) B4518557
theorem B4757393 : Blo 1879141 4757393 := bstep (se 2 (by rfl) ⟨1784022, by rfl⟩ : syracuseStep 4757393 = 3568045) B3568045
theorem B3012499 : Blo 1879141 3012499 := bstep (se 1 (by rfl) ⟨2259374, by rfl⟩ : syracuseStep 3012499 = 4518749) B4518749
theorem B6346673 : Blo 1879141 6346673 := bstep (se 2 (by rfl) ⟨2380002, by rfl⟩ : syracuseStep 6346673 = 4760005) B4760005
theorem B21993443 : Blo 1879141 21993443 := bstep (se 1 (by rfl) ⟨16495082, by rfl⟩ : syracuseStep 21993443 = 32990165) B32990165
theorem B9033713 : Blo 1879141 9033713 := bstep (se 2 (by rfl) ⟨3387642, by rfl⟩ : syracuseStep 9033713 = 6775285) B6775285
theorem B32127029 : Blo 1879141 32127029 := bstep (se 5 (by rfl) ⟨1505954, by rfl⟩ : syracuseStep 32127029 = 3011909) B3011909
theorem B2676883 : Blo 1879141 2676883 := bstep (se 1 (by rfl) ⟨2007662, by rfl⟩ : syracuseStep 2676883 = 4015325) B4015325
theorem B10713293 : Blo 1879141 10713293 := bstep (se 3 (by rfl) ⟨2008742, by rfl⟩ : syracuseStep 10713293 = 4017485) B4017485
theorem B3864803 : Blo 1879141 3864803 := bstep (se 1 (by rfl) ⟨2898602, by rfl⟩ : syracuseStep 3864803 = 5797205) B5797205
theorem B2676979 : Blo 1879141 2676979 := bstep (se 1 (by rfl) ⟨2007734, by rfl⟩ : syracuseStep 2676979 = 4015469) B4015469
theorem B10705229 : Blo 1879141 10705229 := bstep (se 3 (by rfl) ⟨2007230, by rfl⟩ : syracuseStep 10705229 = 4014461) B4014461
theorem B7141709 : Blo 1879141 7141709 := bstep (se 3 (by rfl) ⟨1339070, by rfl⟩ : syracuseStep 7141709 = 2678141) B2678141
theorem B6773105 : Blo 1879141 6773105 := bstep (se 2 (by rfl) ⟨2539914, by rfl⟩ : syracuseStep 6773105 = 5079829) B5079829
theorem B3570065 : Blo 1879141 3570065 := bstep (se 2 (by rfl) ⟨1338774, by rfl⟩ : syracuseStep 3570065 = 2677549) B2677549
theorem B5355953 : Blo 1879141 5355953 := bstep (se 2 (by rfl) ⟨2008482, by rfl⟩ : syracuseStep 5355953 = 4016965) B4016965
theorem B6347213 : Blo 1879141 6347213 := bstep (se 3 (by rfl) ⟨1190102, by rfl⟩ : syracuseStep 6347213 = 2380205) B2380205
theorem B5716451 : Blo 1879141 5716451 := bstep (se 1 (by rfl) ⟨4287338, by rfl⟩ : syracuseStep 5716451 = 8574677) B8574677
theorem B6347267 : Blo 1879141 6347267 := bstep (se 1 (by rfl) ⟨4760450, by rfl⟩ : syracuseStep 6347267 = 9520901) B9520901
theorem B18078221 : Blo 1879141 18078221 := bstep (se 3 (by rfl) ⟨3389666, by rfl⟩ : syracuseStep 18078221 = 6779333) B6779333
theorem B3013217 : Blo 1879141 3013217 := bstep (se 2 (by rfl) ⟨1129956, by rfl⟩ : syracuseStep 3013217 = 2259913) B2259913
theorem B5356145 : Blo 1879141 5356145 := bstep (se 2 (by rfl) ⟨2008554, by rfl⟩ : syracuseStep 5356145 = 4017109) B4017109
theorem B12049073 : Blo 1879141 12049073 := bstep (se 2 (by rfl) ⟨4518402, by rfl⟩ : syracuseStep 12049073 = 9036805) B9036805
theorem B2677475 : Blo 1879141 2677475 := bstep (se 1 (by rfl) ⟨2008106, by rfl⟩ : syracuseStep 2677475 = 4016213) B4016213
theorem B6347537 : Blo 1879141 6347537 := bstep (se 2 (by rfl) ⟨2380326, by rfl⟩ : syracuseStep 6347537 = 4760653) B4760653
theorem B2857793 : Blo 1879141 2857793 := bstep (se 2 (by rfl) ⟨1071672, by rfl⟩ : syracuseStep 2857793 = 2143345) B2143345
theorem B4758385 : Blo 1879141 4758385 := bstep (se 2 (by rfl) ⟨1784394, by rfl⟩ : syracuseStep 4758385 = 3568789) B3568789
theorem B4578257 : Blo 1879141 4578257 := bstep (se 2 (by rfl) ⟨1716846, by rfl⟩ : syracuseStep 4578257 = 3433693) B3433693
theorem B6020077 : Blo 1879141 6020077 := bstep (se 3 (by rfl) ⟨1128764, by rfl⟩ : syracuseStep 6020077 = 2257529) B2257529
theorem B3619907 : Blo 1879141 3619907 := bstep (se 1 (by rfl) ⟨2714930, by rfl⟩ : syracuseStep 3619907 = 5429861) B5429861
theorem B4758659 : Blo 1879141 4758659 := bstep (se 1 (by rfl) ⟨3568994, by rfl⟩ : syracuseStep 4758659 = 7137989) B7137989
theorem B12205253 : Blo 1879141 12205253 := bstep (se 4 (by rfl) ⟨1144242, by rfl⟩ : syracuseStep 12205253 = 2288485) B2288485
theorem B8576227 : Blo 1879141 8576227 := bstep (se 1 (by rfl) ⟨6432170, by rfl⟩ : syracuseStep 8576227 = 12864341) B12864341
theorem B6020333 : Blo 1879141 6020333 := bstep (se 3 (by rfl) ⟨1128812, by rfl⟩ : syracuseStep 6020333 = 2257625) B2257625
theorem B16063757 : Blo 1879141 16063757 := bstep (se 3 (by rfl) ⟨3011954, by rfl⟩ : syracuseStep 16063757 = 6023909) B6023909
theorem B3570961 : Blo 1879141 3570961 := bstep (se 2 (by rfl) ⟨1339110, by rfl⟩ : syracuseStep 3570961 = 2678221) B2678221
theorem B6348077 : Blo 1879141 6348077 := bstep (se 3 (by rfl) ⟨1190264, by rfl⟩ : syracuseStep 6348077 = 2380529) B2380529
theorem B4758851 : Blo 1879141 4758851 := bstep (se 1 (by rfl) ⟨3569138, by rfl⟩ : syracuseStep 4758851 = 7138277) B7138277
theorem B2678113 : Blo 1879141 2678113 := bstep (se 2 (by rfl) ⟨1004292, by rfl⟩ : syracuseStep 2678113 = 2008585) B2008585
theorem B6348131 : Blo 1879141 6348131 := bstep (se 1 (by rfl) ⟨4761098, by rfl⟩ : syracuseStep 6348131 = 9522197) B9522197
theorem B3571121 : Blo 1879141 3571121 := bstep (se 2 (by rfl) ⟨1339170, by rfl⟩ : syracuseStep 3571121 = 2678341) B2678341
theorem B45719153 : Blo 1879141 45719153 := bstep (se 2 (by rfl) ⟨17144682, by rfl⟩ : syracuseStep 45719153 = 34289365) B34289365
theorem B6348401 : Blo 1879141 6348401 := bstep (se 2 (by rfl) ⟨2380650, by rfl⟩ : syracuseStep 6348401 = 4761301) B4761301
theorem B4013795 : Blo 1879141 4013795 := bstep (se 1 (by rfl) ⟨3010346, by rfl⟩ : syracuseStep 4013795 = 6020693) B6020693
theorem B4579057 : Blo 1879141 4579057 := bstep (se 2 (by rfl) ⟨1717146, by rfl⟩ : syracuseStep 4579057 = 3434293) B3434293
theorem B21413645 : Blo 1879141 21413645 := bstep (se 3 (by rfl) ⟨4015058, by rfl⟩ : syracuseStep 21413645 = 8030117) B8030117
theorem B6774605 : Blo 1879141 6774605 := bstep (se 3 (by rfl) ⟨1270238, by rfl⟩ : syracuseStep 6774605 = 2540477) B2540477
theorem B8028067 : Blo 1879141 8028067 := bstep (se 1 (by rfl) ⟨6021050, by rfl⟩ : syracuseStep 8028067 = 12042101) B12042101
theorem B12050507 : Blo 1879141 12050507 := bstep (se 1 (by rfl) ⟨9037880, by rfl⟩ : syracuseStep 12050507 = 18075761) B18075761
theorem B27091037 : Blo 1879141 27091037 := bstep (se 3 (by rfl) ⟨5079569, by rfl⟩ : syracuseStep 27091037 = 10159139) B10159139
theorem B24084611 : Blo 1879141 24084611 := bstep (se 1 (by rfl) ⟨18063458, by rfl⟩ : syracuseStep 24084611 = 36126917) B36126917
theorem B8577175 : Blo 1879141 8577175 := bstep (se 1 (by rfl) ⟨6432881, by rfl⟩ : syracuseStep 8577175 = 12865763) B12865763
theorem B12861713 : Blo 1879141 12861713 := bstep (se 2 (by rfl) ⟨4823142, by rfl⟩ : syracuseStep 12861713 = 9646285) B9646285
theorem B6701329 : Blo 1879141 6701329 := bstep (se 2 (by rfl) ⟨2512998, by rfl⟩ : syracuseStep 6701329 = 5025997) B5025997
theorem B13558033 : Blo 1879141 13558033 := bstep (se 2 (by rfl) ⟨5084262, by rfl⟩ : syracuseStep 13558033 = 10168525) B10168525
theorem B13730093 : Blo 1879141 13730093 := bstep (se 3 (by rfl) ⟨2574392, by rfl⟩ : syracuseStep 13730093 = 5148785) B5148785
theorem B9404747 : Blo 1879141 9404747 := bstep (se 1 (by rfl) ⟨7053560, by rfl⟩ : syracuseStep 9404747 = 14107121) B14107121
theorem B40640885 : Blo 1879141 40640885 := bstep (se 5 (by rfl) ⟨1905041, by rfl⟩ : syracuseStep 40640885 = 3810083) B3810083
theorem B2114059 : Blo 1879141 2114059 := bstep (se 1 (by rfl) ⟨1585544, by rfl⟩ : syracuseStep 2114059 = 3171089) B3171089
theorem B32547341 : Blo 1879141 32547341 := bstep (se 3 (by rfl) ⟨6102626, by rfl⟩ : syracuseStep 32547341 = 12205253) B12205253
theorem B2114167 : Blo 1879141 2114167 := bstep (se 1 (by rfl) ⟨1585625, by rfl⟩ : syracuseStep 2114167 = 3171251) B3171251
theorem B16065155 : Blo 1879141 16065155 := bstep (se 1 (by rfl) ⟨12048866, by rfl⟩ : syracuseStep 16065155 = 24097733) B24097733
theorem B9519767 : Blo 1879141 9519767 := bstep (se 1 (by rfl) ⟨7139825, by rfl⟩ : syracuseStep 9519767 = 14279651) B14279651
theorem B30483125 : Blo 1879141 30483125 := bstep (se 5 (by rfl) ⟨1428896, by rfl⟩ : syracuseStep 30483125 = 2857793) B2857793
theorem B2818763 : Blo 1879141 2818763 := bstep (se 1 (by rfl) ⟨2114072, by rfl⟩ : syracuseStep 2818763 = 4228145) B4228145
theorem B2818775 : Blo 1879141 2818775 := bstep (se 1 (by rfl) ⟨2114081, by rfl⟩ : syracuseStep 2818775 = 4228163) B4228163
theorem B62653169 : Blo 1879141 62653169 := bstep (se 2 (by rfl) ⟨23494938, by rfl⟩ : syracuseStep 62653169 = 46989877) B46989877
theorem B12043025 : Blo 1879141 12043025 := bstep (se 2 (by rfl) ⟨4516134, by rfl⟩ : syracuseStep 12043025 = 9032269) B9032269
theorem B2818841 : Blo 1879141 2818841 := bstep (se 2 (by rfl) ⟨1057065, by rfl⟩ : syracuseStep 2818841 = 2114131) B2114131
theorem B2114347 : Blo 1879141 2114347 := bstep (se 1 (by rfl) ⟨1585760, by rfl⟩ : syracuseStep 2114347 = 3171521) B3171521
theorem B7136045 : Blo 1879141 7136045 := bstep (se 3 (by rfl) ⟨1338008, by rfl⟩ : syracuseStep 7136045 = 2676017) B2676017
theorem B2818955 : Blo 1879141 2818955 := bstep (se 1 (by rfl) ⟨2114216, by rfl⟩ : syracuseStep 2818955 = 4228433) B4228433
theorem B2818967 : Blo 1879141 2818967 := bstep (se 1 (by rfl) ⟨2114225, by rfl⟩ : syracuseStep 2818967 = 4228451) B4228451
theorem B2114455 : Blo 1879141 2114455 := bstep (se 1 (by rfl) ⟨1585841, by rfl⟩ : syracuseStep 2114455 = 3171683) B3171683
theorem B4760471 : Blo 1879141 4760471 := bstep (se 1 (by rfl) ⟨3570353, by rfl⟩ : syracuseStep 4760471 = 7140707) B7140707
theorem B2007991 : Blo 1879141 2007991 := bstep (se 1 (by rfl) ⟨1505993, by rfl⟩ : syracuseStep 2007991 = 3011987) B3011987
theorem B2819033 : Blo 1879141 2819033 := bstep (se 2 (by rfl) ⟨1057137, by rfl⟩ : syracuseStep 2819033 = 2114275) B2114275
theorem B8029145 : Blo 1879141 8029145 := bstep (se 2 (by rfl) ⟨3010929, by rfl⟩ : syracuseStep 8029145 = 6021859) B6021859
theorem B10159121 : Blo 1879141 10159121 := bstep (se 2 (by rfl) ⟨3809670, by rfl⟩ : syracuseStep 10159121 = 7619341) B7619341
theorem B4015127 : Blo 1879141 4015127 := bstep (se 1 (by rfl) ⟨3011345, by rfl⟩ : syracuseStep 4015127 = 6022691) B6022691
theorem B9036845 : Blo 1879141 9036845 := bstep (se 3 (by rfl) ⟨1694408, by rfl⟩ : syracuseStep 9036845 = 3388817) B3388817
theorem B2819147 : Blo 1879141 2819147 := bstep (se 1 (by rfl) ⟨2114360, by rfl⟩ : syracuseStep 2819147 = 4228721) B4228721
theorem B2114635 : Blo 1879141 2114635 := bstep (se 1 (by rfl) ⟨1585976, by rfl⟩ : syracuseStep 2114635 = 3171953) B3171953
theorem B2819159 : Blo 1879141 2819159 := bstep (se 1 (by rfl) ⟨2114369, by rfl⟩ : syracuseStep 2819159 = 4228739) B4228739
theorem B15246467 : Blo 1879141 15246467 := bstep (se 1 (by rfl) ⟨11434850, by rfl⟩ : syracuseStep 15246467 = 22869701) B22869701
theorem B4228235 : Blo 1879141 4228235 := bstep (se 1 (by rfl) ⟨3171176, by rfl⟩ : syracuseStep 4228235 = 6342353) B6342353
theorem B3171467 : Blo 1879141 3171467 := bstep (se 1 (by rfl) ⟨2378600, by rfl⟩ : syracuseStep 3171467 = 4757201) B4757201
theorem B2819225 : Blo 1879141 2819225 := bstep (se 2 (by rfl) ⟨1057209, by rfl⟩ : syracuseStep 2819225 = 2114419) B2114419
theorem B45737141 : Blo 1879141 45737141 := bstep (se 5 (by rfl) ⟨2143928, by rfl⟩ : syracuseStep 45737141 = 4287857) B4287857
theorem B2114743 : Blo 1879141 2114743 := bstep (se 1 (by rfl) ⟨1586057, by rfl⟩ : syracuseStep 2114743 = 3172115) B3172115
theorem B2008247 : Blo 1879141 2008247 := bstep (se 1 (by rfl) ⟨1506185, by rfl⟩ : syracuseStep 2008247 = 3012371) B3012371
theorem B4228289 : Blo 1879141 4228289 := bstep (se 2 (by rfl) ⟨1585608, by rfl⟩ : syracuseStep 4228289 = 3171217) B3171217
theorem B24421637 : Blo 1879141 24421637 := bstep (se 4 (by rfl) ⟨2289528, by rfl⟩ : syracuseStep 24421637 = 4579057) B4579057
theorem B3171595 : Blo 1879141 3171595 := bstep (se 1 (by rfl) ⟨2378696, by rfl⟩ : syracuseStep 3171595 = 4757393) B4757393
theorem B2819339 : Blo 1879141 2819339 := bstep (se 1 (by rfl) ⟨2114504, by rfl⟩ : syracuseStep 2819339 = 4229009) B4229009
theorem B2819351 : Blo 1879141 2819351 := bstep (se 1 (by rfl) ⟨2114513, by rfl⟩ : syracuseStep 2819351 = 4229027) B4229027
theorem B6022475 : Blo 1879141 6022475 := bstep (se 1 (by rfl) ⟨4516856, by rfl⟩ : syracuseStep 6022475 = 9033713) B9033713
theorem B4015435 : Blo 1879141 4015435 := bstep (se 1 (by rfl) ⟨3011576, by rfl⟩ : syracuseStep 4015435 = 6023153) B6023153
theorem B2819417 : Blo 1879141 2819417 := bstep (se 2 (by rfl) ⟨1057281, by rfl⟩ : syracuseStep 2819417 = 2114563) B2114563
theorem B2114923 : Blo 1879141 2114923 := bstep (se 1 (by rfl) ⟨1586192, by rfl⟩ : syracuseStep 2114923 = 3172385) B3172385
theorem B14271875 : Blo 1879141 14271875 := bstep (se 1 (by rfl) ⟨10703906, by rfl⟩ : syracuseStep 14271875 = 21407813) B21407813
theorem B4228505 : Blo 1879141 4228505 := bstep (se 2 (by rfl) ⟨1585689, by rfl⟩ : syracuseStep 4228505 = 3171379) B3171379
theorem B3171737 : Blo 1879141 3171737 := bstep (se 2 (by rfl) ⟨1189401, by rfl⟩ : syracuseStep 3171737 = 2378803) B2378803
theorem B2819531 : Blo 1879141 2819531 := bstep (se 1 (by rfl) ⟨2114648, by rfl⟩ : syracuseStep 2819531 = 4229297) B4229297
theorem B2819543 : Blo 1879141 2819543 := bstep (se 1 (by rfl) ⟨2114657, by rfl⟩ : syracuseStep 2819543 = 4229315) B4229315
theorem B2115031 : Blo 1879141 2115031 := bstep (se 1 (by rfl) ⟨1586273, by rfl⟩ : syracuseStep 2115031 = 3172547) B3172547
theorem B4228595 : Blo 1879141 4228595 := bstep (se 1 (by rfl) ⟨3171446, by rfl⟩ : syracuseStep 4228595 = 6342893) B6342893
theorem B4228631 : Blo 1879141 4228631 := bstep (se 1 (by rfl) ⟨3171473, by rfl⟩ : syracuseStep 4228631 = 6342947) B6342947
theorem B3171865 : Blo 1879141 3171865 := bstep (se 2 (by rfl) ⟨1189449, by rfl⟩ : syracuseStep 3171865 = 2378899) B2378899
theorem B2819609 : Blo 1879141 2819609 := bstep (se 2 (by rfl) ⟨1057353, by rfl⟩ : syracuseStep 2819609 = 2114707) B2114707
theorem B7136819 : Blo 1879141 7136819 := bstep (se 1 (by rfl) ⟨5352614, by rfl⟩ : syracuseStep 7136819 = 10705229) B10705229
theorem B4761139 : Blo 1879141 4761139 := bstep (se 1 (by rfl) ⟨3570854, by rfl⟩ : syracuseStep 4761139 = 7141709) B7141709
theorem B2819723 : Blo 1879141 2819723 := bstep (se 1 (by rfl) ⟨2114792, by rfl⟩ : syracuseStep 2819723 = 4229585) B4229585
theorem B2115211 : Blo 1879141 2115211 := bstep (se 1 (by rfl) ⟨1586408, by rfl⟩ : syracuseStep 2115211 = 3172817) B3172817
theorem B2819735 : Blo 1879141 2819735 := bstep (se 1 (by rfl) ⟨2114801, by rfl⟩ : syracuseStep 2819735 = 4229603) B4229603
theorem B12052147 : Blo 1879141 12052147 := bstep (se 1 (by rfl) ⟨9039110, by rfl⟩ : syracuseStep 12052147 = 18078221) B18078221
theorem B4761281 : Blo 1879141 4761281 := bstep (se 2 (by rfl) ⟨1785480, by rfl⟩ : syracuseStep 4761281 = 3570961) B3570961
theorem B4228811 : Blo 1879141 4228811 := bstep (se 1 (by rfl) ⟨3171608, by rfl⟩ : syracuseStep 4228811 = 6343217) B6343217
theorem B2819801 : Blo 1879141 2819801 := bstep (se 2 (by rfl) ⟨1057425, by rfl⟩ : syracuseStep 2819801 = 2114851) B2114851
theorem B2008811 : Blo 1879141 2008811 := bstep (se 1 (by rfl) ⟨1506608, by rfl⟩ : syracuseStep 2008811 = 3013217) B3013217
theorem B2115319 : Blo 1879141 2115319 := bstep (se 1 (by rfl) ⟨1586489, by rfl⟩ : syracuseStep 2115319 = 3172979) B3172979
theorem B4228865 : Blo 1879141 4228865 := bstep (se 2 (by rfl) ⟨1585824, by rfl⟩ : syracuseStep 4228865 = 3171649) B3171649
theorem B2819915 : Blo 1879141 2819915 := bstep (se 1 (by rfl) ⟨2114936, by rfl⟩ : syracuseStep 2819915 = 4229873) B4229873
theorem B2819927 : Blo 1879141 2819927 := bstep (se 1 (by rfl) ⟨2114945, by rfl⟩ : syracuseStep 2819927 = 4229891) B4229891
theorem B2819993 : Blo 1879141 2819993 := bstep (se 2 (by rfl) ⟨1057497, by rfl⟩ : syracuseStep 2819993 = 2114995) B2114995
theorem B2115499 : Blo 1879141 2115499 := bstep (se 1 (by rfl) ⟨1586624, by rfl⟩ : syracuseStep 2115499 = 3173249) B3173249
theorem B2541515 : Blo 1879141 2541515 := bstep (se 1 (by rfl) ⟨1906136, by rfl⟩ : syracuseStep 2541515 = 3812273) B3812273
theorem B4229081 : Blo 1879141 4229081 := bstep (se 2 (by rfl) ⟨1585905, by rfl⟩ : syracuseStep 4229081 = 3171811) B3171811
theorem B2820107 : Blo 1879141 2820107 := bstep (se 1 (by rfl) ⟨2115080, by rfl⟩ : syracuseStep 2820107 = 4230161) B4230161
theorem B2820119 : Blo 1879141 2820119 := bstep (se 1 (by rfl) ⟨2115089, by rfl⟩ : syracuseStep 2820119 = 4230179) B4230179
theorem B2115607 : Blo 1879141 2115607 := bstep (se 1 (by rfl) ⟨1586705, by rfl⟩ : syracuseStep 2115607 = 3173411) B3173411
theorem B4229171 : Blo 1879141 4229171 := bstep (se 1 (by rfl) ⟨3171878, by rfl⟩ : syracuseStep 4229171 = 6343757) B6343757
theorem B4515905 : Blo 1879141 4515905 := bstep (se 2 (by rfl) ⟨1693464, by rfl⟩ : syracuseStep 4515905 = 3386929) B3386929
theorem B14469185 : Blo 1879141 14469185 := bstep (se 2 (by rfl) ⟨5425944, by rfl⟩ : syracuseStep 14469185 = 10851889) B10851889
theorem B6342731 : Blo 1879141 6342731 := bstep (se 1 (by rfl) ⟨4757048, by rfl⟩ : syracuseStep 6342731 = 9514097) B9514097
theorem B4229207 : Blo 1879141 4229207 := bstep (se 1 (by rfl) ⟨3171905, by rfl⟩ : syracuseStep 4229207 = 6343811) B6343811
theorem B3172439 : Blo 1879141 3172439 := bstep (se 1 (by rfl) ⟨2379329, by rfl⟩ : syracuseStep 3172439 = 4758659) B4758659
theorem B2820185 : Blo 1879141 2820185 := bstep (se 2 (by rfl) ⟨1057569, by rfl⟩ : syracuseStep 2820185 = 2115139) B2115139
theorem B10709171 : Blo 1879141 10709171 := bstep (se 1 (by rfl) ⟨8031878, by rfl⟩ : syracuseStep 10709171 = 16063757) B16063757
theorem B5720257 : Blo 1879141 5720257 := bstep (se 2 (by rfl) ⟨2145096, by rfl⟩ : syracuseStep 5720257 = 4290193) B4290193
theorem B2820299 : Blo 1879141 2820299 := bstep (se 1 (by rfl) ⟨2115224, by rfl⟩ : syracuseStep 2820299 = 4230449) B4230449
theorem B2115787 : Blo 1879141 2115787 := bstep (se 1 (by rfl) ⟨1586840, by rfl⟩ : syracuseStep 2115787 = 3173681) B3173681
theorem B3172567 : Blo 1879141 3172567 := bstep (se 1 (by rfl) ⟨2379425, by rfl⟩ : syracuseStep 3172567 = 4758851) B4758851
theorem B2820311 : Blo 1879141 2820311 := bstep (se 1 (by rfl) ⟨2115233, by rfl⟩ : syracuseStep 2820311 = 4230467) B4230467
theorem B4229387 : Blo 1879141 4229387 := bstep (se 1 (by rfl) ⟨3172040, by rfl⟩ : syracuseStep 4229387 = 6344081) B6344081
theorem B2820377 : Blo 1879141 2820377 := bstep (se 2 (by rfl) ⟨1057641, by rfl⟩ : syracuseStep 2820377 = 2115283) B2115283
theorem B51472685 : Blo 1879141 51472685 := bstep (se 3 (by rfl) ⟨9651128, by rfl⟩ : syracuseStep 51472685 = 19302257) B19302257
theorem B2115895 : Blo 1879141 2115895 := bstep (se 1 (by rfl) ⟨1586921, by rfl⟩ : syracuseStep 2115895 = 3173843) B3173843
theorem B4229441 : Blo 1879141 4229441 := bstep (se 2 (by rfl) ⟨1586040, by rfl⟩ : syracuseStep 4229441 = 3172081) B3172081
theorem B6343001 : Blo 1879141 6343001 := bstep (se 2 (by rfl) ⟨2378625, by rfl⟩ : syracuseStep 6343001 = 4757251) B4757251
theorem B41224565 : Blo 1879141 41224565 := bstep (se 5 (by rfl) ⟨1932401, by rfl⟩ : syracuseStep 41224565 = 3864803) B3864803
theorem B2820491 : Blo 1879141 2820491 := bstep (se 1 (by rfl) ⟨2115368, by rfl⟩ : syracuseStep 2820491 = 4230737) B4230737
theorem B2820503 : Blo 1879141 2820503 := bstep (se 1 (by rfl) ⟨2115377, by rfl⟩ : syracuseStep 2820503 = 4230755) B4230755
theorem B4516289 : Blo 1879141 4516289 := bstep (se 2 (by rfl) ⟨1693608, by rfl⟩ : syracuseStep 4516289 = 3387217) B3387217
theorem B2820569 : Blo 1879141 2820569 := bstep (se 2 (by rfl) ⟨1057713, by rfl⟩ : syracuseStep 2820569 = 2115427) B2115427
theorem B2116075 : Blo 1879141 2116075 := bstep (se 1 (by rfl) ⟨1587056, by rfl⟩ : syracuseStep 2116075 = 3174113) B3174113
theorem B4229657 : Blo 1879141 4229657 := bstep (se 2 (by rfl) ⟨1586121, by rfl⟩ : syracuseStep 4229657 = 3172243) B3172243
theorem B4016665 : Blo 1879141 4016665 := bstep (se 2 (by rfl) ⟨1506249, by rfl⟩ : syracuseStep 4016665 = 3012499) B3012499
theorem B4516403 : Blo 1879141 4516403 := bstep (se 1 (by rfl) ⟨3387302, by rfl⟩ : syracuseStep 4516403 = 6774605) B6774605
theorem B8030785 : Blo 1879141 8030785 := bstep (se 2 (by rfl) ⟨3011544, by rfl⟩ : syracuseStep 8030785 = 6023089) B6023089
theorem B2820683 : Blo 1879141 2820683 := bstep (se 1 (by rfl) ⟨2115512, by rfl⟩ : syracuseStep 2820683 = 4231025) B4231025
theorem B2820695 : Blo 1879141 2820695 := bstep (se 1 (by rfl) ⟨2115521, by rfl⟩ : syracuseStep 2820695 = 4231043) B4231043
theorem B2116183 : Blo 1879141 2116183 := bstep (se 1 (by rfl) ⟨1587137, by rfl⟩ : syracuseStep 2116183 = 3174275) B3174275
theorem B4229747 : Blo 1879141 4229747 := bstep (se 1 (by rfl) ⟨3172310, by rfl⟩ : syracuseStep 4229747 = 6344621) B6344621
theorem B4229783 : Blo 1879141 4229783 := bstep (se 1 (by rfl) ⟨3172337, by rfl⟩ : syracuseStep 4229783 = 6344675) B6344675
theorem B2820761 : Blo 1879141 2820761 := bstep (se 2 (by rfl) ⟨1057785, by rfl⟩ : syracuseStep 2820761 = 2115571) B2115571
theorem B2820875 : Blo 1879141 2820875 := bstep (se 1 (by rfl) ⟨2115656, by rfl⟩ : syracuseStep 2820875 = 4231313) B4231313
theorem B2820887 : Blo 1879141 2820887 := bstep (se 1 (by rfl) ⟨2115665, by rfl⟩ : syracuseStep 2820887 = 4231331) B4231331
theorem B9513773 : Blo 1879141 9513773 := bstep (se 3 (by rfl) ⟨1783832, by rfl⟩ : syracuseStep 9513773 = 3567665) B3567665
theorem B4705075 : Blo 1879141 4705075 := bstep (se 1 (by rfl) ⟨3528806, by rfl⟩ : syracuseStep 4705075 = 7057613) B7057613
theorem B2034487 : Blo 1879141 2034487 := bstep (se 1 (by rfl) ⟨1525865, by rfl⟩ : syracuseStep 2034487 = 3051731) B3051731
theorem B121940801 : Blo 1879141 121940801 := bstep (se 2 (by rfl) ⟨45727800, by rfl⟩ : syracuseStep 121940801 = 91455601) B91455601
theorem B4229963 : Blo 1879141 4229963 := bstep (se 1 (by rfl) ⟨3172472, by rfl⟩ : syracuseStep 4229963 = 6344945) B6344945
theorem B3173195 : Blo 1879141 3173195 := bstep (se 1 (by rfl) ⟨2379896, by rfl⟩ : syracuseStep 3173195 = 4759793) B4759793
theorem B2820953 : Blo 1879141 2820953 := bstep (se 2 (by rfl) ⟨1057857, by rfl⟩ : syracuseStep 2820953 = 2115715) B2115715
theorem B4230017 : Blo 1879141 4230017 := bstep (se 2 (by rfl) ⟨1586256, by rfl⟩ : syracuseStep 4230017 = 3172513) B3172513
theorem B7236503 : Blo 1879141 7236503 := bstep (se 1 (by rfl) ⟨5427377, by rfl⟩ : syracuseStep 7236503 = 10854755) B10854755
theorem B2714519 : Blo 1879141 2714519 := bstep (se 1 (by rfl) ⟨2035889, by rfl⟩ : syracuseStep 2714519 = 4071779) B4071779
theorem B30501809 : Blo 1879141 30501809 := bstep (se 2 (by rfl) ⟨11438178, by rfl⟩ : syracuseStep 30501809 = 22876357) B22876357
theorem B2173879 : Blo 1879141 2173879 := bstep (se 1 (by rfl) ⟨1630409, by rfl⟩ : syracuseStep 2173879 = 3260819) B3260819
theorem B3173323 : Blo 1879141 3173323 := bstep (se 1 (by rfl) ⟨2379992, by rfl⟩ : syracuseStep 3173323 = 4759985) B4759985
theorem B2821067 : Blo 1879141 2821067 := bstep (se 1 (by rfl) ⟨2115800, by rfl⟩ : syracuseStep 2821067 = 4231601) B4231601
theorem B2821079 : Blo 1879141 2821079 := bstep (se 1 (by rfl) ⟨2115809, by rfl⟩ : syracuseStep 2821079 = 4231619) B4231619
theorem B5352409 : Blo 1879141 5352409 := bstep (se 2 (by rfl) ⟨2007153, by rfl⟩ : syracuseStep 5352409 = 4014307) B4014307
theorem B7138307 : Blo 1879141 7138307 := bstep (se 1 (by rfl) ⟨5353730, by rfl⟩ : syracuseStep 7138307 = 10707461) B10707461
theorem B6343703 : Blo 1879141 6343703 := bstep (se 1 (by rfl) ⟨4757777, by rfl⟩ : syracuseStep 6343703 = 9515555) B9515555
theorem B2821145 : Blo 1879141 2821145 := bstep (se 2 (by rfl) ⟨1057929, by rfl⟩ : syracuseStep 2821145 = 2115859) B2115859
theorem B10161197 : Blo 1879141 10161197 := bstep (se 3 (by rfl) ⟨1905224, by rfl⟩ : syracuseStep 10161197 = 3810449) B3810449
theorem B4230233 : Blo 1879141 4230233 := bstep (se 2 (by rfl) ⟨1586337, by rfl⟩ : syracuseStep 4230233 = 3172675) B3172675
theorem B3173465 : Blo 1879141 3173465 := bstep (se 2 (by rfl) ⟨1190049, by rfl⟩ : syracuseStep 3173465 = 2380099) B2380099
theorem B1879147 : Blo 1879141 1879147 := bstep (se 1 (by rfl) ⟨1409360, by rfl⟩ : syracuseStep 1879147 = 2818721) B2818721
theorem B3812467 : Blo 1879141 3812467 := bstep (se 1 (by rfl) ⟨2859350, by rfl⟩ : syracuseStep 3812467 = 5718701) B5718701
theorem B1879159 : Blo 1879141 1879159 := bstep (se 1 (by rfl) ⟨1409369, by rfl⟩ : syracuseStep 1879159 = 2818739) B2818739
theorem B1879179 : Blo 1879141 1879179 := bstep (se 1 (by rfl) ⟨1409384, by rfl⟩ : syracuseStep 1879179 = 2818769) B2818769
theorem B2821259 : Blo 1879141 2821259 := bstep (se 1 (by rfl) ⟨2115944, by rfl⟩ : syracuseStep 2821259 = 4231889) B4231889
theorem B1879191 : Blo 1879141 1879191 := bstep (se 1 (by rfl) ⟨1409393, by rfl⟩ : syracuseStep 1879191 = 2818787) B2818787
theorem B8031383 : Blo 1879141 8031383 := bstep (se 1 (by rfl) ⟨6023537, by rfl⟩ : syracuseStep 8031383 = 12047075) B12047075
theorem B2821271 : Blo 1879141 2821271 := bstep (se 1 (by rfl) ⟨2115953, by rfl⟩ : syracuseStep 2821271 = 4231907) B4231907
theorem B1879211 : Blo 1879141 1879211 := bstep (se 1 (by rfl) ⟨1409408, by rfl⟩ : syracuseStep 1879211 = 2818817) B2818817
theorem B4230323 : Blo 1879141 4230323 := bstep (se 1 (by rfl) ⟨3172742, by rfl⟩ : syracuseStep 4230323 = 6345485) B6345485
theorem B1879223 : Blo 1879141 1879223 := bstep (se 1 (by rfl) ⟨1409417, by rfl⟩ : syracuseStep 1879223 = 2818835) B2818835
theorem B1879243 : Blo 1879141 1879243 := bstep (se 1 (by rfl) ⟨1409432, by rfl⟩ : syracuseStep 1879243 = 2818865) B2818865
theorem B1879255 : Blo 1879141 1879255 := bstep (se 1 (by rfl) ⟨1409441, by rfl⟩ : syracuseStep 1879255 = 2818883) B2818883
theorem B4230359 : Blo 1879141 4230359 := bstep (se 1 (by rfl) ⟨3172769, by rfl⟩ : syracuseStep 4230359 = 6345539) B6345539
theorem B3173593 : Blo 1879141 3173593 := bstep (se 2 (by rfl) ⟨1190097, by rfl⟩ : syracuseStep 3173593 = 2380195) B2380195
theorem B2821337 : Blo 1879141 2821337 := bstep (se 2 (by rfl) ⟨1058001, by rfl⟩ : syracuseStep 2821337 = 2116003) B2116003
theorem B1879275 : Blo 1879141 1879275 := bstep (se 1 (by rfl) ⟨1409456, by rfl⟩ : syracuseStep 1879275 = 2818913) B2818913
theorem B1879287 : Blo 1879141 1879287 := bstep (se 1 (by rfl) ⟨1409465, by rfl⟩ : syracuseStep 1879287 = 2818931) B2818931
theorem B1879307 : Blo 1879141 1879307 := bstep (se 1 (by rfl) ⟨1409480, by rfl⟩ : syracuseStep 1879307 = 2818961) B2818961
theorem B1879319 : Blo 1879141 1879319 := bstep (se 1 (by rfl) ⟨1409489, by rfl⟩ : syracuseStep 1879319 = 2818979) B2818979
theorem B1879339 : Blo 1879141 1879339 := bstep (se 1 (by rfl) ⟨1409504, by rfl⟩ : syracuseStep 1879339 = 2819009) B2819009
theorem B1879351 : Blo 1879141 1879351 := bstep (se 1 (by rfl) ⟨1409513, by rfl⟩ : syracuseStep 1879351 = 2819027) B2819027
theorem B1879371 : Blo 1879141 1879371 := bstep (se 1 (by rfl) ⟨1409528, by rfl⟩ : syracuseStep 1879371 = 2819057) B2819057
theorem B2821451 : Blo 1879141 2821451 := bstep (se 1 (by rfl) ⟨2116088, by rfl⟩ : syracuseStep 2821451 = 4232177) B4232177
theorem B1879383 : Blo 1879141 1879383 := bstep (se 1 (by rfl) ⟨1409537, by rfl⟩ : syracuseStep 1879383 = 2819075) B2819075
theorem B2821463 : Blo 1879141 2821463 := bstep (se 1 (by rfl) ⟨2116097, by rfl⟩ : syracuseStep 2821463 = 4232195) B4232195
theorem B5352797 : Blo 1879141 5352797 := bstep (se 3 (by rfl) ⟨1003649, by rfl⟩ : syracuseStep 5352797 = 2007299) B2007299
theorem B1879403 : Blo 1879141 1879403 := bstep (se 1 (by rfl) ⟨1409552, by rfl⟩ : syracuseStep 1879403 = 2819105) B2819105
theorem B52170101 : Blo 1879141 52170101 := bstep (se 5 (by rfl) ⟨2445473, by rfl⟩ : syracuseStep 52170101 = 4890947) B4890947
theorem B1879415 : Blo 1879141 1879415 := bstep (se 1 (by rfl) ⟨1409561, by rfl⟩ : syracuseStep 1879415 = 2819123) B2819123
theorem B1879435 : Blo 1879141 1879435 := bstep (se 1 (by rfl) ⟨1409576, by rfl⟩ : syracuseStep 1879435 = 2819153) B2819153
theorem B4230539 : Blo 1879141 4230539 := bstep (se 1 (by rfl) ⟨3172904, by rfl⟩ : syracuseStep 4230539 = 6345809) B6345809
theorem B1879447 : Blo 1879141 1879447 := bstep (se 1 (by rfl) ⟨1409585, by rfl⟩ : syracuseStep 1879447 = 2819171) B2819171
theorem B2821529 : Blo 1879141 2821529 := bstep (se 2 (by rfl) ⟨1058073, by rfl⟩ : syracuseStep 2821529 = 2116147) B2116147
theorem B1879467 : Blo 1879141 1879467 := bstep (se 1 (by rfl) ⟨1409600, by rfl⟩ : syracuseStep 1879467 = 2819201) B2819201
theorem B1879479 : Blo 1879141 1879479 := bstep (se 1 (by rfl) ⟨1409609, by rfl⟩ : syracuseStep 1879479 = 2819219) B2819219
theorem B4230593 : Blo 1879141 4230593 := bstep (se 2 (by rfl) ⟨1586472, by rfl⟩ : syracuseStep 4230593 = 3172945) B3172945
theorem B1879499 : Blo 1879141 1879499 := bstep (se 1 (by rfl) ⟨1409624, by rfl⟩ : syracuseStep 1879499 = 2819249) B2819249
theorem B7138763 : Blo 1879141 7138763 := bstep (se 1 (by rfl) ⟨5354072, by rfl⟩ : syracuseStep 7138763 = 10708145) B10708145
theorem B1879511 : Blo 1879141 1879511 := bstep (se 1 (by rfl) ⟨1409633, by rfl⟩ : syracuseStep 1879511 = 2819267) B2819267
theorem B2379223 : Blo 1879141 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B1879531 : Blo 1879141 1879531 := bstep (se 1 (by rfl) ⟨1409648, by rfl⟩ : syracuseStep 1879531 = 2819297) B2819297
theorem B1879543 : Blo 1879141 1879543 := bstep (se 1 (by rfl) ⟨1409657, by rfl⟩ : syracuseStep 1879543 = 2819315) B2819315
theorem B1879563 : Blo 1879141 1879563 := bstep (se 1 (by rfl) ⟨1409672, by rfl⟩ : syracuseStep 1879563 = 2819345) B2819345
theorem B2821643 : Blo 1879141 2821643 := bstep (se 1 (by rfl) ⟨2116232, by rfl⟩ : syracuseStep 2821643 = 4232465) B4232465
theorem B1879575 : Blo 1879141 1879575 := bstep (se 1 (by rfl) ⟨1409681, by rfl⟩ : syracuseStep 1879575 = 2819363) B2819363
theorem B2821655 : Blo 1879141 2821655 := bstep (se 1 (by rfl) ⟨2116241, by rfl⟩ : syracuseStep 2821655 = 4232483) B4232483
theorem B16068131 : Blo 1879141 16068131 := bstep (se 1 (by rfl) ⟨12051098, by rfl⟩ : syracuseStep 16068131 = 24102197) B24102197
theorem B1879595 : Blo 1879141 1879595 := bstep (se 1 (by rfl) ⟨1409696, by rfl⟩ : syracuseStep 1879595 = 2819393) B2819393
theorem B6344243 : Blo 1879141 6344243 := bstep (se 1 (by rfl) ⟨4758182, by rfl⟩ : syracuseStep 6344243 = 9516365) B9516365
theorem B1879607 : Blo 1879141 1879607 := bstep (se 1 (by rfl) ⟨1409705, by rfl⟩ : syracuseStep 1879607 = 2819411) B2819411
theorem B1879627 : Blo 1879141 1879627 := bstep (se 1 (by rfl) ⟨1409720, by rfl⟩ : syracuseStep 1879627 = 2819441) B2819441
theorem B1879639 : Blo 1879141 1879639 := bstep (se 1 (by rfl) ⟨1409729, by rfl⟩ : syracuseStep 1879639 = 2819459) B2819459
theorem B6024793 : Blo 1879141 6024793 := bstep (se 2 (by rfl) ⟨2259297, by rfl⟩ : syracuseStep 6024793 = 4518595) B4518595
theorem B10710629 : Blo 1879141 10710629 := bstep (se 4 (by rfl) ⟨1004121, by rfl⟩ : syracuseStep 10710629 = 2008243) B2008243
theorem B1879659 : Blo 1879141 1879659 := bstep (se 1 (by rfl) ⟨1409744, by rfl⟩ : syracuseStep 1879659 = 2819489) B2819489
theorem B1879671 : Blo 1879141 1879671 := bstep (se 1 (by rfl) ⟨1409753, by rfl⟩ : syracuseStep 1879671 = 2819507) B2819507
theorem B1879691 : Blo 1879141 1879691 := bstep (se 1 (by rfl) ⟨1409768, by rfl⟩ : syracuseStep 1879691 = 2819537) B2819537
theorem B7138961 : Blo 1879141 7138961 := bstep (se 2 (by rfl) ⟨2677110, by rfl⟩ : syracuseStep 7138961 = 5354221) B5354221
theorem B1879703 : Blo 1879141 1879703 := bstep (se 1 (by rfl) ⟨1409777, by rfl⟩ : syracuseStep 1879703 = 2819555) B2819555
theorem B4230809 : Blo 1879141 4230809 := bstep (se 2 (by rfl) ⟨1586553, by rfl⟩ : syracuseStep 4230809 = 3173107) B3173107
theorem B1879723 : Blo 1879141 1879723 := bstep (se 1 (by rfl) ⟨1409792, by rfl⟩ : syracuseStep 1879723 = 2819585) B2819585
theorem B1879735 : Blo 1879141 1879735 := bstep (se 1 (by rfl) ⟨1409801, by rfl⟩ : syracuseStep 1879735 = 2819603) B2819603
theorem B1879755 : Blo 1879141 1879755 := bstep (se 1 (by rfl) ⟨1409816, by rfl⟩ : syracuseStep 1879755 = 2819633) B2819633
theorem B1879767 : Blo 1879141 1879767 := bstep (se 1 (by rfl) ⟨1409825, by rfl⟩ : syracuseStep 1879767 = 2819651) B2819651
theorem B1879787 : Blo 1879141 1879787 := bstep (se 1 (by rfl) ⟨1409840, by rfl⟩ : syracuseStep 1879787 = 2819681) B2819681
theorem B4230899 : Blo 1879141 4230899 := bstep (se 1 (by rfl) ⟨3173174, by rfl⟩ : syracuseStep 4230899 = 6346349) B6346349
theorem B1879799 : Blo 1879141 1879799 := bstep (se 1 (by rfl) ⟨1409849, by rfl⟩ : syracuseStep 1879799 = 2819699) B2819699
theorem B1879819 : Blo 1879141 1879819 := bstep (se 1 (by rfl) ⟨1409864, by rfl⟩ : syracuseStep 1879819 = 2819729) B2819729
theorem B1879831 : Blo 1879141 1879831 := bstep (se 1 (by rfl) ⟨1409873, by rfl⟩ : syracuseStep 1879831 = 2819747) B2819747
theorem B4230935 : Blo 1879141 4230935 := bstep (se 1 (by rfl) ⟨3173201, by rfl⟩ : syracuseStep 4230935 = 6346403) B6346403
theorem B3174167 : Blo 1879141 3174167 := bstep (se 1 (by rfl) ⟨2380625, by rfl⟩ : syracuseStep 3174167 = 4761251) B4761251
theorem B1879851 : Blo 1879141 1879851 := bstep (se 1 (by rfl) ⟨1409888, by rfl⟩ : syracuseStep 1879851 = 2819777) B2819777
theorem B1879863 : Blo 1879141 1879863 := bstep (se 1 (by rfl) ⟨1409897, by rfl⟩ : syracuseStep 1879863 = 2819795) B2819795
theorem B6344513 : Blo 1879141 6344513 := bstep (se 2 (by rfl) ⟨2379192, by rfl⟩ : syracuseStep 6344513 = 4758385) B4758385
theorem B1879883 : Blo 1879141 1879883 := bstep (se 1 (by rfl) ⟨1409912, by rfl⟩ : syracuseStep 1879883 = 2819825) B2819825
theorem B1879895 : Blo 1879141 1879895 := bstep (se 1 (by rfl) ⟨1409921, by rfl⟩ : syracuseStep 1879895 = 2819843) B2819843
theorem B1879915 : Blo 1879141 1879915 := bstep (se 1 (by rfl) ⟨1409936, by rfl⟩ : syracuseStep 1879915 = 2819873) B2819873
theorem B1879927 : Blo 1879141 1879927 := bstep (se 1 (by rfl) ⟨1409945, by rfl⟩ : syracuseStep 1879927 = 2819891) B2819891
theorem B1879947 : Blo 1879141 1879947 := bstep (se 1 (by rfl) ⟨1409960, by rfl⟩ : syracuseStep 1879947 = 2819921) B2819921
theorem B1879959 : Blo 1879141 1879959 := bstep (se 1 (by rfl) ⟨1409969, by rfl⟩ : syracuseStep 1879959 = 2819939) B2819939
theorem B3174295 : Blo 1879141 3174295 := bstep (se 1 (by rfl) ⟨2380721, by rfl⟩ : syracuseStep 3174295 = 4761443) B4761443
theorem B1879979 : Blo 1879141 1879979 := bstep (se 1 (by rfl) ⟨1409984, by rfl⟩ : syracuseStep 1879979 = 2819969) B2819969
theorem B1879991 : Blo 1879141 1879991 := bstep (se 1 (by rfl) ⟨1409993, by rfl⟩ : syracuseStep 1879991 = 2819987) B2819987
theorem B1880011 : Blo 1879141 1880011 := bstep (se 1 (by rfl) ⟨1410008, by rfl⟩ : syracuseStep 1880011 = 2820017) B2820017
theorem B4231115 : Blo 1879141 4231115 := bstep (se 1 (by rfl) ⟨3173336, by rfl⟩ : syracuseStep 4231115 = 6346673) B6346673
theorem B1880023 : Blo 1879141 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B1880043 : Blo 1879141 1880043 := bstep (se 1 (by rfl) ⟨1410032, by rfl⟩ : syracuseStep 1880043 = 2820065) B2820065
theorem B1880055 : Blo 1879141 1880055 := bstep (se 1 (by rfl) ⟨1410041, by rfl⟩ : syracuseStep 1880055 = 2820083) B2820083
theorem B4231169 : Blo 1879141 4231169 := bstep (se 2 (by rfl) ⟨1586688, by rfl⟩ : syracuseStep 4231169 = 3173377) B3173377
theorem B1880075 : Blo 1879141 1880075 := bstep (se 1 (by rfl) ⟨1410056, by rfl⟩ : syracuseStep 1880075 = 2820113) B2820113
theorem B1880087 : Blo 1879141 1880087 := bstep (se 1 (by rfl) ⟨1410065, by rfl⟩ : syracuseStep 1880087 = 2820131) B2820131
theorem B6778903 : Blo 1879141 6778903 := bstep (se 1 (by rfl) ⟨5084177, by rfl⟩ : syracuseStep 6778903 = 10168355) B10168355
theorem B21418019 : Blo 1879141 21418019 := bstep (se 1 (by rfl) ⟨16063514, by rfl⟩ : syracuseStep 21418019 = 32127029) B32127029
theorem B1880107 : Blo 1879141 1880107 := bstep (se 1 (by rfl) ⟨1410080, by rfl⟩ : syracuseStep 1880107 = 2820161) B2820161
theorem B1880119 : Blo 1879141 1880119 := bstep (se 1 (by rfl) ⟨1410089, by rfl⟩ : syracuseStep 1880119 = 2820179) B2820179
theorem B1880139 : Blo 1879141 1880139 := bstep (se 1 (by rfl) ⟨1410104, by rfl⟩ : syracuseStep 1880139 = 2820209) B2820209
theorem B1880151 : Blo 1879141 1880151 := bstep (se 1 (by rfl) ⟨1410113, by rfl⟩ : syracuseStep 1880151 = 2820227) B2820227
theorem B1880171 : Blo 1879141 1880171 := bstep (se 1 (by rfl) ⟨1410128, by rfl⟩ : syracuseStep 1880171 = 2820257) B2820257
theorem B1880183 : Blo 1879141 1880183 := bstep (se 1 (by rfl) ⟨1410137, by rfl⟩ : syracuseStep 1880183 = 2820275) B2820275
theorem B1880203 : Blo 1879141 1880203 := bstep (se 1 (by rfl) ⟨1410152, by rfl⟩ : syracuseStep 1880203 = 2820305) B2820305
theorem B1880215 : Blo 1879141 1880215 := bstep (se 1 (by rfl) ⟨1410161, by rfl⟩ : syracuseStep 1880215 = 2820323) B2820323
theorem B1880235 : Blo 1879141 1880235 := bstep (se 1 (by rfl) ⟨1410176, by rfl⟩ : syracuseStep 1880235 = 2820353) B2820353
theorem B1880247 : Blo 1879141 1880247 := bstep (se 1 (by rfl) ⟨1410185, by rfl⟩ : syracuseStep 1880247 = 2820371) B2820371
theorem B1880267 : Blo 1879141 1880267 := bstep (se 1 (by rfl) ⟨1410200, by rfl⟩ : syracuseStep 1880267 = 2820401) B2820401
theorem B1880279 : Blo 1879141 1880279 := bstep (se 1 (by rfl) ⟨1410209, by rfl⟩ : syracuseStep 1880279 = 2820419) B2820419
theorem B4231385 : Blo 1879141 4231385 := bstep (se 2 (by rfl) ⟨1586769, by rfl⟩ : syracuseStep 4231385 = 3173539) B3173539
theorem B1880299 : Blo 1879141 1880299 := bstep (se 1 (by rfl) ⟨1410224, by rfl⟩ : syracuseStep 1880299 = 2820449) B2820449
theorem B1880311 : Blo 1879141 1880311 := bstep (se 1 (by rfl) ⟨1410233, by rfl⟩ : syracuseStep 1880311 = 2820467) B2820467
theorem B1880331 : Blo 1879141 1880331 := bstep (se 1 (by rfl) ⟨1410248, by rfl⟩ : syracuseStep 1880331 = 2820497) B2820497
theorem B2380043 : Blo 1879141 2380043 := bstep (se 1 (by rfl) ⟨1785032, by rfl⟩ : syracuseStep 2380043 = 3570065) B3570065
theorem B1880343 : Blo 1879141 1880343 := bstep (se 1 (by rfl) ⟨1410257, by rfl⟩ : syracuseStep 1880343 = 2820515) B2820515
theorem B1880363 : Blo 1879141 1880363 := bstep (se 1 (by rfl) ⟨1410272, by rfl⟩ : syracuseStep 1880363 = 2820545) B2820545
theorem B14283053 : Blo 1879141 14283053 := bstep (se 3 (by rfl) ⟨2678072, by rfl⟩ : syracuseStep 14283053 = 5356145) B5356145
theorem B4231475 : Blo 1879141 4231475 := bstep (se 1 (by rfl) ⟨3173606, by rfl⟩ : syracuseStep 4231475 = 6347213) B6347213
theorem B1880375 : Blo 1879141 1880375 := bstep (se 1 (by rfl) ⟨1410281, by rfl⟩ : syracuseStep 1880375 = 2820563) B2820563
theorem B1880395 : Blo 1879141 1880395 := bstep (se 1 (by rfl) ⟨1410296, by rfl⟩ : syracuseStep 1880395 = 2820593) B2820593
theorem B1880407 : Blo 1879141 1880407 := bstep (se 1 (by rfl) ⟨1410305, by rfl⟩ : syracuseStep 1880407 = 2820611) B2820611
theorem B4231511 : Blo 1879141 4231511 := bstep (se 1 (by rfl) ⟨3173633, by rfl⟩ : syracuseStep 4231511 = 6347267) B6347267
theorem B6345053 : Blo 1879141 6345053 := bstep (se 3 (by rfl) ⟨1189697, by rfl⟩ : syracuseStep 6345053 = 2379395) B2379395
theorem B1880427 : Blo 1879141 1880427 := bstep (se 1 (by rfl) ⟨1410320, by rfl⟩ : syracuseStep 1880427 = 2820641) B2820641
theorem B1880439 : Blo 1879141 1880439 := bstep (se 1 (by rfl) ⟨1410329, by rfl⟩ : syracuseStep 1880439 = 2820659) B2820659
theorem B1880459 : Blo 1879141 1880459 := bstep (se 1 (by rfl) ⟨1410344, by rfl⟩ : syracuseStep 1880459 = 2820689) B2820689
theorem B7139735 : Blo 1879141 7139735 := bstep (se 1 (by rfl) ⟨5354801, by rfl⟩ : syracuseStep 7139735 = 10709603) B10709603
theorem B1880471 : Blo 1879141 1880471 := bstep (se 1 (by rfl) ⟨1410353, by rfl⟩ : syracuseStep 1880471 = 2820707) B2820707
theorem B1880491 : Blo 1879141 1880491 := bstep (se 1 (by rfl) ⟨1410368, by rfl⟩ : syracuseStep 1880491 = 2820737) B2820737
theorem B1880503 : Blo 1879141 1880503 := bstep (se 1 (by rfl) ⟨1410377, by rfl⟩ : syracuseStep 1880503 = 2820755) B2820755
theorem B1880523 : Blo 1879141 1880523 := bstep (se 1 (by rfl) ⟨1410392, by rfl⟩ : syracuseStep 1880523 = 2820785) B2820785
theorem B8032715 : Blo 1879141 8032715 := bstep (se 1 (by rfl) ⟨6024536, by rfl⟩ : syracuseStep 8032715 = 12049073) B12049073
theorem B1880535 : Blo 1879141 1880535 := bstep (se 1 (by rfl) ⟨1410401, by rfl⟩ : syracuseStep 1880535 = 2820803) B2820803
theorem B1880555 : Blo 1879141 1880555 := bstep (se 1 (by rfl) ⟨1410416, by rfl⟩ : syracuseStep 1880555 = 2820833) B2820833
theorem B1880567 : Blo 1879141 1880567 := bstep (se 1 (by rfl) ⟨1410425, by rfl⟩ : syracuseStep 1880567 = 2820851) B2820851
theorem B1880587 : Blo 1879141 1880587 := bstep (se 1 (by rfl) ⟨1410440, by rfl⟩ : syracuseStep 1880587 = 2820881) B2820881
theorem B4231691 : Blo 1879141 4231691 := bstep (se 1 (by rfl) ⟨3173768, by rfl⟩ : syracuseStep 4231691 = 6347537) B6347537
theorem B3568151 : Blo 1879141 3568151 := bstep (se 1 (by rfl) ⟨2676113, by rfl⟩ : syracuseStep 3568151 = 5352227) B5352227
theorem B1880599 : Blo 1879141 1880599 := bstep (se 1 (by rfl) ⟨1410449, by rfl⟩ : syracuseStep 1880599 = 2820899) B2820899
theorem B1880619 : Blo 1879141 1880619 := bstep (se 1 (by rfl) ⟨1410464, by rfl⟩ : syracuseStep 1880619 = 2820929) B2820929
theorem B1880631 : Blo 1879141 1880631 := bstep (se 1 (by rfl) ⟨1410473, by rfl⟩ : syracuseStep 1880631 = 2820947) B2820947
theorem B4231745 : Blo 1879141 4231745 := bstep (se 2 (by rfl) ⟨1586904, by rfl⟩ : syracuseStep 4231745 = 3173809) B3173809
theorem B1880651 : Blo 1879141 1880651 := bstep (se 1 (by rfl) ⟨1410488, by rfl⟩ : syracuseStep 1880651 = 2820977) B2820977
theorem B1880663 : Blo 1879141 1880663 := bstep (se 1 (by rfl) ⟨1410497, by rfl⟩ : syracuseStep 1880663 = 2820995) B2820995
theorem B7139933 : Blo 1879141 7139933 := bstep (se 3 (by rfl) ⟨1338737, by rfl⟩ : syracuseStep 7139933 = 2677475) B2677475
theorem B1880683 : Blo 1879141 1880683 := bstep (se 1 (by rfl) ⟨1410512, by rfl⟩ : syracuseStep 1880683 = 2821025) B2821025
theorem B1880695 : Blo 1879141 1880695 := bstep (se 1 (by rfl) ⟨1410521, by rfl⟩ : syracuseStep 1880695 = 2821043) B2821043
theorem B3052171 : Blo 1879141 3052171 := bstep (se 1 (by rfl) ⟨2289128, by rfl⟩ : syracuseStep 3052171 = 4578257) B4578257
theorem B1880715 : Blo 1879141 1880715 := bstep (se 1 (by rfl) ⟨1410536, by rfl⟩ : syracuseStep 1880715 = 2821073) B2821073
theorem B1880727 : Blo 1879141 1880727 := bstep (se 1 (by rfl) ⟨1410545, by rfl⟩ : syracuseStep 1880727 = 2821091) B2821091
theorem B1880747 : Blo 1879141 1880747 := bstep (se 1 (by rfl) ⟨1410560, by rfl⟩ : syracuseStep 1880747 = 2821121) B2821121
theorem B1880759 : Blo 1879141 1880759 := bstep (se 1 (by rfl) ⟨1410569, by rfl⟩ : syracuseStep 1880759 = 2821139) B2821139
theorem B1880779 : Blo 1879141 1880779 := bstep (se 1 (by rfl) ⟨1410584, by rfl⟩ : syracuseStep 1880779 = 2821169) B2821169
theorem B14275277 : Blo 1879141 14275277 := bstep (se 3 (by rfl) ⟨2676614, by rfl⟩ : syracuseStep 14275277 = 5353229) B5353229
theorem B1880791 : Blo 1879141 1880791 := bstep (se 1 (by rfl) ⟨1410593, by rfl⟩ : syracuseStep 1880791 = 2821187) B2821187
theorem B2413271 : Blo 1879141 2413271 := bstep (se 1 (by rfl) ⟨1809953, by rfl⟩ : syracuseStep 2413271 = 3619907) B3619907
theorem B1880811 : Blo 1879141 1880811 := bstep (se 1 (by rfl) ⟨1410608, by rfl⟩ : syracuseStep 1880811 = 2821217) B2821217
theorem B1880823 : Blo 1879141 1880823 := bstep (se 1 (by rfl) ⟨1410617, by rfl⟩ : syracuseStep 1880823 = 2821235) B2821235
theorem B1880843 : Blo 1879141 1880843 := bstep (se 1 (by rfl) ⟨1410632, by rfl⟩ : syracuseStep 1880843 = 2821265) B2821265
theorem B1880855 : Blo 1879141 1880855 := bstep (se 1 (by rfl) ⟨1410641, by rfl⟩ : syracuseStep 1880855 = 2821283) B2821283
theorem B4231961 : Blo 1879141 4231961 := bstep (se 2 (by rfl) ⟨1586985, by rfl⟩ : syracuseStep 4231961 = 3173971) B3173971
theorem B1880875 : Blo 1879141 1880875 := bstep (se 1 (by rfl) ⟨1410656, by rfl⟩ : syracuseStep 1880875 = 2821313) B2821313
theorem B1880887 : Blo 1879141 1880887 := bstep (se 1 (by rfl) ⟨1410665, by rfl⟩ : syracuseStep 1880887 = 2821331) B2821331
theorem B1880907 : Blo 1879141 1880907 := bstep (se 1 (by rfl) ⟨1410680, by rfl⟩ : syracuseStep 1880907 = 2821361) B2821361
theorem B1880919 : Blo 1879141 1880919 := bstep (se 1 (by rfl) ⟨1410689, by rfl⟩ : syracuseStep 1880919 = 2821379) B2821379
theorem B1880939 : Blo 1879141 1880939 := bstep (se 1 (by rfl) ⟨1410704, by rfl⟩ : syracuseStep 1880939 = 2821409) B2821409
theorem B4232051 : Blo 1879141 4232051 := bstep (se 1 (by rfl) ⟨3174038, by rfl⟩ : syracuseStep 4232051 = 6348077) B6348077
theorem B1880951 : Blo 1879141 1880951 := bstep (se 1 (by rfl) ⟨1410713, by rfl⟩ : syracuseStep 1880951 = 2821427) B2821427
theorem B1880971 : Blo 1879141 1880971 := bstep (se 1 (by rfl) ⟨1410728, by rfl⟩ : syracuseStep 1880971 = 2821457) B2821457
theorem B4232087 : Blo 1879141 4232087 := bstep (se 1 (by rfl) ⟨3174065, by rfl⟩ : syracuseStep 4232087 = 6348131) B6348131
theorem B1880983 : Blo 1879141 1880983 := bstep (se 1 (by rfl) ⟨1410737, by rfl⟩ : syracuseStep 1880983 = 2821475) B2821475
theorem B3388313 : Blo 1879141 3388313 := bstep (se 2 (by rfl) ⟨1270617, by rfl⟩ : syracuseStep 3388313 = 2541235) B2541235
theorem B1881003 : Blo 1879141 1881003 := bstep (se 1 (by rfl) ⟨1410752, by rfl⟩ : syracuseStep 1881003 = 2821505) B2821505
theorem B1881015 : Blo 1879141 1881015 := bstep (se 1 (by rfl) ⟨1410761, by rfl⟩ : syracuseStep 1881015 = 2821523) B2821523
theorem B6026177 : Blo 1879141 6026177 := bstep (se 2 (by rfl) ⟨2259816, by rfl⟩ : syracuseStep 6026177 = 4519633) B4519633
theorem B1881035 : Blo 1879141 1881035 := bstep (se 1 (by rfl) ⟨1410776, by rfl⟩ : syracuseStep 1881035 = 2821553) B2821553
theorem B2380747 : Blo 1879141 2380747 := bstep (se 1 (by rfl) ⟨1785560, by rfl⟩ : syracuseStep 2380747 = 3571121) B3571121
theorem B1881047 : Blo 1879141 1881047 := bstep (se 1 (by rfl) ⟨1410785, by rfl⟩ : syracuseStep 1881047 = 2821571) B2821571
theorem B1881067 : Blo 1879141 1881067 := bstep (se 1 (by rfl) ⟨1410800, by rfl⟩ : syracuseStep 1881067 = 2821601) B2821601
theorem B1881079 : Blo 1879141 1881079 := bstep (se 1 (by rfl) ⟨1410809, by rfl⟩ : syracuseStep 1881079 = 2821619) B2821619
theorem B1881099 : Blo 1879141 1881099 := bstep (se 1 (by rfl) ⟨1410824, by rfl⟩ : syracuseStep 1881099 = 2821649) B2821649
theorem B1881111 : Blo 1879141 1881111 := bstep (se 1 (by rfl) ⟨1410833, by rfl⟩ : syracuseStep 1881111 = 2821667) B2821667
theorem B1881131 : Blo 1879141 1881131 := bstep (se 1 (by rfl) ⟨1410848, by rfl⟩ : syracuseStep 1881131 = 2821697) B2821697
theorem B3568691 : Blo 1879141 3568691 := bstep (se 1 (by rfl) ⟨2676518, by rfl⟩ : syracuseStep 3568691 = 5353037) B5353037
theorem B30479435 : Blo 1879141 30479435 := bstep (se 1 (by rfl) ⟨22859576, by rfl⟩ : syracuseStep 30479435 = 45719153) B45719153
theorem B4232267 : Blo 1879141 4232267 := bstep (se 1 (by rfl) ⟨3174200, by rfl⟩ : syracuseStep 4232267 = 6348401) B6348401
theorem B4232321 : Blo 1879141 4232321 := bstep (se 2 (by rfl) ⟨1587120, by rfl⟩ : syracuseStep 4232321 = 3174241) B3174241
theorem B2675863 : Blo 1879141 2675863 := bstep (se 1 (by rfl) ⟨2006897, by rfl⟩ : syracuseStep 2675863 = 4013795) B4013795
theorem B13546673 : Blo 1879141 13546673 := bstep (se 2 (by rfl) ⟨5080002, by rfl⟩ : syracuseStep 13546673 = 10160005) B10160005
theorem B14275763 : Blo 1879141 14275763 := bstep (se 1 (by rfl) ⟨10706822, by rfl⟩ : syracuseStep 14275763 = 21413645) B21413645
theorem B8139955 : Blo 1879141 8139955 := bstep (se 1 (by rfl) ⟨6104966, by rfl⟩ : syracuseStep 8139955 = 12209933) B12209933
theorem B10704089 : Blo 1879141 10704089 := bstep (se 2 (by rfl) ⟨4014033, by rfl⟩ : syracuseStep 10704089 = 8028067) B8028067
theorem B10859737 : Blo 1879141 10859737 := bstep (se 2 (by rfl) ⟨4072401, by rfl⟩ : syracuseStep 10859737 = 8144803) B8144803
theorem B4232537 : Blo 1879141 4232537 := bstep (se 2 (by rfl) ⟨1587201, by rfl⟩ : syracuseStep 4232537 = 3174403) B3174403
theorem B6346187 : Blo 1879141 6346187 := bstep (se 1 (by rfl) ⟨4759640, by rfl⟩ : syracuseStep 6346187 = 9519281) B9519281
theorem B3569177 : Blo 1879141 3569177 := bstep (se 2 (by rfl) ⟨1338441, by rfl⟩ : syracuseStep 3569177 = 2676883) B2676883
theorem B8033843 : Blo 1879141 8033843 := bstep (se 1 (by rfl) ⟨6025382, by rfl⟩ : syracuseStep 8033843 = 12050765) B12050765
theorem B6346457 : Blo 1879141 6346457 := bstep (se 2 (by rfl) ⟨2379921, by rfl⟩ : syracuseStep 6346457 = 4759843) B4759843
theorem B2676569 : Blo 1879141 2676569 := bstep (se 2 (by rfl) ⟨1003713, by rfl⟩ : syracuseStep 2676569 = 2007427) B2007427
theorem B2676683 : Blo 1879141 2676683 := bstep (se 1 (by rfl) ⟨2007512, by rfl⟩ : syracuseStep 2676683 = 4015025) B4015025
theorem B4757555 : Blo 1879141 4757555 := bstep (se 1 (by rfl) ⟨3568166, by rfl⟩ : syracuseStep 4757555 = 7136333) B7136333
theorem B29333573 : Blo 1879141 29333573 := bstep (se 4 (by rfl) ⟨2750022, by rfl⟩ : syracuseStep 29333573 = 5500045) B5500045
theorem B2259019 : Blo 1879141 2259019 := bstep (se 1 (by rfl) ⟨1694264, by rfl⟩ : syracuseStep 2259019 = 3388529) B3388529
theorem B5355713 : Blo 1879141 5355713 := bstep (se 2 (by rfl) ⟨2008392, by rfl⟩ : syracuseStep 5355713 = 4016785) B4016785
theorem B3528983 : Blo 1879141 3528983 := bstep (se 1 (by rfl) ⟨2646737, by rfl⟩ : syracuseStep 3528983 = 5293475) B5293475
theorem B18061613 : Blo 1879141 18061613 := bstep (se 3 (by rfl) ⟨3386552, by rfl⟩ : syracuseStep 18061613 = 6773105) B6773105
theorem B5355827 : Blo 1879141 5355827 := bstep (se 1 (by rfl) ⟨4016870, by rfl⟩ : syracuseStep 5355827 = 8033741) B8033741
theorem B4757849 : Blo 1879141 4757849 := bstep (se 2 (by rfl) ⟨1784193, by rfl⟩ : syracuseStep 4757849 = 3568387) B3568387
theorem B6347159 : Blo 1879141 6347159 := bstep (se 1 (by rfl) ⟨4760369, by rfl⟩ : syracuseStep 6347159 = 9520739) B9520739
theorem B2857369 : Blo 1879141 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B2677207 : Blo 1879141 2677207 := bstep (se 1 (by rfl) ⟨2007905, by rfl⟩ : syracuseStep 2677207 = 4015811) B4015811
theorem B6429149 : Blo 1879141 6429149 := bstep (se 3 (by rfl) ⟨1205465, by rfl⟩ : syracuseStep 6429149 = 2410931) B2410931
theorem B7141891 : Blo 1879141 7141891 := bstep (se 1 (by rfl) ⟨5356418, by rfl⟩ : syracuseStep 7141891 = 10712837) B10712837
theorem B4823617 : Blo 1879141 4823617 := bstep (se 2 (by rfl) ⟨1808856, by rfl⟩ : syracuseStep 4823617 = 3617713) B3617713
theorem B15243869 : Blo 1879141 15243869 := bstep (se 3 (by rfl) ⟨2858225, by rfl⟩ : syracuseStep 15243869 = 5716451) B5716451
theorem B9517661 : Blo 1879141 9517661 := bstep (se 3 (by rfl) ⟨1784561, by rfl⟩ : syracuseStep 9517661 = 3569123) B3569123
theorem B14277221 : Blo 1879141 14277221 := bstep (se 4 (by rfl) ⟨1338489, by rfl⟩ : syracuseStep 14277221 = 2676979) B2676979
theorem B8026769 : Blo 1879141 8026769 := bstep (se 2 (by rfl) ⟨3010038, by rfl⟩ : syracuseStep 8026769 = 6020077) B6020077
theorem B14662295 : Blo 1879141 14662295 := bstep (se 1 (by rfl) ⟨10996721, by rfl⟩ : syracuseStep 14662295 = 21993443) B21993443
theorem B7142195 : Blo 1879141 7142195 := bstep (se 1 (by rfl) ⟨5356646, by rfl⟩ : syracuseStep 7142195 = 10713293) B10713293
theorem B10705729 : Blo 1879141 10705729 := bstep (se 2 (by rfl) ⟨4014648, by rfl⟩ : syracuseStep 10705729 = 8029297) B8029297
theorem B13736881 : Blo 1879141 13736881 := bstep (se 2 (by rfl) ⟨5151330, by rfl⟩ : syracuseStep 13736881 = 10302661) B10302661
theorem B6347699 : Blo 1879141 6347699 := bstep (se 1 (by rfl) ⟨4760774, by rfl⟩ : syracuseStep 6347699 = 9521549) B9521549
theorem B3570635 : Blo 1879141 3570635 := bstep (se 1 (by rfl) ⟨2677976, by rfl⟩ : syracuseStep 3570635 = 5355953) B5355953
theorem B11434969 : Blo 1879141 11434969 := bstep (se 2 (by rfl) ⟨4288113, by rfl⟩ : syracuseStep 11434969 = 8576227) B8576227
theorem B14277707 : Blo 1879141 14277707 := bstep (se 1 (by rfl) ⟨10708280, by rfl⟩ : syracuseStep 14277707 = 21416561) B21416561
theorem B3570817 : Blo 1879141 3570817 := bstep (se 2 (by rfl) ⟨1339056, by rfl⟩ : syracuseStep 3570817 = 2678113) B2678113
theorem B6347969 : Blo 1879141 6347969 := bstep (se 2 (by rfl) ⟨2380488, by rfl⟩ : syracuseStep 6347969 = 4760977) B4760977
theorem B2678027 : Blo 1879141 2678027 := bstep (se 1 (by rfl) ⟨2008520, by rfl⟩ : syracuseStep 2678027 = 4017041) B4017041
theorem B4013555 : Blo 1879141 4013555 := bstep (se 1 (by rfl) ⟨3010166, by rfl⟩ : syracuseStep 4013555 = 6020333) B6020333
theorem B8027693 : Blo 1879141 8027693 := bstep (se 3 (by rfl) ⟨1505192, by rfl⟩ : syracuseStep 8027693 = 3010385) B3010385
theorem B6348509 : Blo 1879141 6348509 := bstep (se 3 (by rfl) ⟨1190345, by rfl⟩ : syracuseStep 6348509 = 2380691) B2380691
theorem B2006795 : Blo 1879141 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B5578571 : Blo 1879141 5578571 := bstep (se 1 (by rfl) ⟨4183928, by rfl⟩ : syracuseStep 5578571 = 8367857) B8367857
theorem B9035651 : Blo 1879141 9035651 := bstep (se 1 (by rfl) ⟨6776738, by rfl⟩ : syracuseStep 9035651 = 13553477) B13553477
theorem B4759499 : Blo 1879141 4759499 := bstep (se 1 (by rfl) ⟨3569624, by rfl⟩ : syracuseStep 4759499 = 7139249) B7139249
theorem B14278679 : Blo 1879141 14278679 := bstep (se 1 (by rfl) ⟨10709009, by rfl⟩ : syracuseStep 14278679 = 21418019) B21418019
theorem B10707005 : Blo 1879141 10707005 := bstep (se 3 (by rfl) ⟨2007563, by rfl⟩ : syracuseStep 10707005 = 4015127) B4015127
theorem B16056407 : Blo 1879141 16056407 := bstep (se 1 (by rfl) ⟨12042305, by rfl⟩ : syracuseStep 16056407 = 24084611) B24084611
theorem B11436233 : Blo 1879141 11436233 := bstep (se 2 (by rfl) ⟨4288587, by rfl⟩ : syracuseStep 11436233 = 8577175) B8577175
theorem B7627009 : Blo 1879141 7627009 := bstep (se 2 (by rfl) ⟨2860128, by rfl⟩ : syracuseStep 7627009 = 5720257) B5720257
theorem B4759823 : Blo 1879141 4759823 := bstep (se 1 (by rfl) ⟨3569867, by rfl⟩ : syracuseStep 4759823 = 7139735) B7139735
theorem B4759955 : Blo 1879141 4759955 := bstep (se 1 (by rfl) ⟨3569966, by rfl⟩ : syracuseStep 4759955 = 7139933) B7139933
theorem B8028683 : Blo 1879141 8028683 := bstep (se 1 (by rfl) ⟨6021512, by rfl⟩ : syracuseStep 8028683 = 12043025) B12043025
theorem B3809825 : Blo 1879141 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B2818745 : Blo 1879141 2818745 := bstep (se 2 (by rfl) ⟨1057029, by rfl⟩ : syracuseStep 2818745 = 2114059) B2114059
theorem B16278245 : Blo 1879141 16278245 := bstep (se 4 (by rfl) ⟨1526085, by rfl⟩ : syracuseStep 16278245 = 3052171) B3052171
theorem B6431489 : Blo 1879141 6431489 := bstep (se 2 (by rfl) ⟨2411808, by rfl⟩ : syracuseStep 6431489 = 4823617) B4823617
theorem B10707713 : Blo 1879141 10707713 := bstep (se 2 (by rfl) ⟨4015392, by rfl⟩ : syracuseStep 10707713 = 8030785) B8030785
theorem B2818823 : Blo 1879141 2818823 := bstep (se 1 (by rfl) ⟨2114117, by rfl⟩ : syracuseStep 2818823 = 4228235) B4228235
theorem B2114311 : Blo 1879141 2114311 := bstep (se 1 (by rfl) ⟨1585733, by rfl⟩ : syracuseStep 2114311 = 3171467) B3171467
theorem B2818859 : Blo 1879141 2818859 := bstep (se 1 (by rfl) ⟨2114144, by rfl⟩ : syracuseStep 2818859 = 4228289) B4228289
theorem B7136059 : Blo 1879141 7136059 := bstep (se 1 (by rfl) ⟨5352044, by rfl⟩ : syracuseStep 7136059 = 10704089) B10704089
theorem B2818889 : Blo 1879141 2818889 := bstep (se 2 (by rfl) ⟨1057083, by rfl⟩ : syracuseStep 2818889 = 2114167) B2114167
theorem B4014983 : Blo 1879141 4014983 := bstep (se 1 (by rfl) ⟨3011237, by rfl⟩ : syracuseStep 4014983 = 6022475) B6022475
theorem B2819003 : Blo 1879141 2819003 := bstep (se 1 (by rfl) ⟨2114252, by rfl⟩ : syracuseStep 2819003 = 4228505) B4228505
theorem B2114491 : Blo 1879141 2114491 := bstep (se 1 (by rfl) ⟨1585868, by rfl⟩ : syracuseStep 2114491 = 3171737) B3171737
theorem B2819063 : Blo 1879141 2819063 := bstep (se 1 (by rfl) ⟨2114297, by rfl⟩ : syracuseStep 2819063 = 4228595) B4228595
theorem B2819087 : Blo 1879141 2819087 := bstep (se 1 (by rfl) ⟨2114315, by rfl⟩ : syracuseStep 2819087 = 4228631) B4228631
theorem B2819129 : Blo 1879141 2819129 := bstep (se 2 (by rfl) ⟨1057173, by rfl⟩ : syracuseStep 2819129 = 2114347) B2114347
theorem B2819207 : Blo 1879141 2819207 := bstep (se 1 (by rfl) ⟨2114405, by rfl⟩ : syracuseStep 2819207 = 4228811) B4228811
theorem B2819243 : Blo 1879141 2819243 := bstep (se 1 (by rfl) ⟨2114432, by rfl⟩ : syracuseStep 2819243 = 4228865) B4228865
theorem B2819273 : Blo 1879141 2819273 := bstep (se 2 (by rfl) ⟨1057227, by rfl⟩ : syracuseStep 2819273 = 2114455) B2114455
theorem B7136545 : Blo 1879141 7136545 := bstep (se 2 (by rfl) ⟨2676204, by rfl⟩ : syracuseStep 7136545 = 5352409) B5352409
theorem B15246625 : Blo 1879141 15246625 := bstep (se 2 (by rfl) ⟨5717484, by rfl⟩ : syracuseStep 15246625 = 11434969) B11434969
theorem B2819387 : Blo 1879141 2819387 := bstep (se 1 (by rfl) ⟨2114540, by rfl⟩ : syracuseStep 2819387 = 4229081) B4229081
theorem B3171703 : Blo 1879141 3171703 := bstep (se 1 (by rfl) ⟨2378777, by rfl⟩ : syracuseStep 3171703 = 4757555) B4757555
theorem B2819447 : Blo 1879141 2819447 := bstep (se 1 (by rfl) ⟨2114585, by rfl⟩ : syracuseStep 2819447 = 4229171) B4229171
theorem B19555715 : Blo 1879141 19555715 := bstep (se 1 (by rfl) ⟨14666786, by rfl⟩ : syracuseStep 19555715 = 29333573) B29333573
theorem B4228487 : Blo 1879141 4228487 := bstep (se 1 (by rfl) ⟨3171365, by rfl⟩ : syracuseStep 4228487 = 6342731) B6342731
theorem B2819471 : Blo 1879141 2819471 := bstep (se 1 (by rfl) ⟨2114603, by rfl⟩ : syracuseStep 2819471 = 4229207) B4229207
theorem B2114959 : Blo 1879141 2114959 := bstep (se 1 (by rfl) ⟨1586219, by rfl⟩ : syracuseStep 2114959 = 3172439) B3172439
theorem B2819513 : Blo 1879141 2819513 := bstep (se 2 (by rfl) ⟨1057317, by rfl⟩ : syracuseStep 2819513 = 2114635) B2114635
theorem B12043741 : Blo 1879141 12043741 := bstep (se 3 (by rfl) ⟨2258201, by rfl⟩ : syracuseStep 12043741 = 4516403) B4516403
theorem B4761089 : Blo 1879141 4761089 := bstep (se 2 (by rfl) ⟨1785408, by rfl⟩ : syracuseStep 4761089 = 3570817) B3570817
theorem B2819591 : Blo 1879141 2819591 := bstep (se 1 (by rfl) ⟨2114693, by rfl⟩ : syracuseStep 2819591 = 4229387) B4229387
theorem B2352655 : Blo 1879141 2352655 := bstep (se 1 (by rfl) ⟨1764491, by rfl⟩ : syracuseStep 2352655 = 3528983) B3528983
theorem B2819627 : Blo 1879141 2819627 := bstep (se 1 (by rfl) ⟨2114720, by rfl⟩ : syracuseStep 2819627 = 4229441) B4229441
theorem B4228667 : Blo 1879141 4228667 := bstep (se 1 (by rfl) ⟨3171500, by rfl⟩ : syracuseStep 4228667 = 6343001) B6343001
theorem B3171899 : Blo 1879141 3171899 := bstep (se 1 (by rfl) ⟨2378924, by rfl⟩ : syracuseStep 3171899 = 4757849) B4757849
theorem B2819657 : Blo 1879141 2819657 := bstep (se 2 (by rfl) ⟨1057371, by rfl⟩ : syracuseStep 2819657 = 2114743) B2114743
theorem B4286099 : Blo 1879141 4286099 := bstep (se 1 (by rfl) ⟨3214574, by rfl⟩ : syracuseStep 4286099 = 6429149) B6429149
theorem B4228793 : Blo 1879141 4228793 := bstep (se 2 (by rfl) ⟨1585797, by rfl⟩ : syracuseStep 4228793 = 3171595) B3171595
theorem B2819771 : Blo 1879141 2819771 := bstep (se 1 (by rfl) ⟨2114828, by rfl⟩ : syracuseStep 2819771 = 4229657) B4229657
theorem B2819831 : Blo 1879141 2819831 := bstep (se 1 (by rfl) ⟨2114873, by rfl⟩ : syracuseStep 2819831 = 4229747) B4229747
theorem B5351179 : Blo 1879141 5351179 := bstep (se 1 (by rfl) ⟨4013384, by rfl⟩ : syracuseStep 5351179 = 8026769) B8026769
theorem B9774863 : Blo 1879141 9774863 := bstep (se 1 (by rfl) ⟨7331147, by rfl⟩ : syracuseStep 9774863 = 14662295) B14662295
theorem B2819855 : Blo 1879141 2819855 := bstep (se 1 (by rfl) ⟨2114891, by rfl⟩ : syracuseStep 2819855 = 4229783) B4229783
theorem B2819897 : Blo 1879141 2819897 := bstep (se 2 (by rfl) ⟨1057461, by rfl⟩ : syracuseStep 2819897 = 2114923) B2114923
theorem B6342515 : Blo 1879141 6342515 := bstep (se 1 (by rfl) ⟨4756886, by rfl⟩ : syracuseStep 6342515 = 9513773) B9513773
theorem B4761463 : Blo 1879141 4761463 := bstep (se 1 (by rfl) ⟨3571097, by rfl⟩ : syracuseStep 4761463 = 7142195) B7142195
theorem B2819975 : Blo 1879141 2819975 := bstep (se 1 (by rfl) ⟨2114981, by rfl⟩ : syracuseStep 2819975 = 4229963) B4229963
theorem B2115463 : Blo 1879141 2115463 := bstep (se 1 (by rfl) ⟨1586597, by rfl⟩ : syracuseStep 2115463 = 3173195) B3173195
theorem B2820011 : Blo 1879141 2820011 := bstep (se 1 (by rfl) ⟨2115008, by rfl⟩ : syracuseStep 2820011 = 4230017) B4230017
theorem B3172297 : Blo 1879141 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B2820041 : Blo 1879141 2820041 := bstep (se 2 (by rfl) ⟨1057515, by rfl⟩ : syracuseStep 2820041 = 2115031) B2115031
theorem B20334539 : Blo 1879141 20334539 := bstep (se 1 (by rfl) ⟨15250904, by rfl⟩ : syracuseStep 20334539 = 30501809) B30501809
theorem B4229135 : Blo 1879141 4229135 := bstep (se 1 (by rfl) ⟨3171851, by rfl⟩ : syracuseStep 4229135 = 6343703) B6343703
theorem B5351453 : Blo 1879141 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B4229153 : Blo 1879141 4229153 := bstep (se 2 (by rfl) ⟨1585932, by rfl⟩ : syracuseStep 4229153 = 3171865) B3171865
theorem B2820155 : Blo 1879141 2820155 := bstep (se 1 (by rfl) ⟨2115116, by rfl⟩ : syracuseStep 2820155 = 4230233) B4230233
theorem B2115643 : Blo 1879141 2115643 := bstep (se 1 (by rfl) ⟨1586732, by rfl⟩ : syracuseStep 2115643 = 3173465) B3173465
theorem B2820215 : Blo 1879141 2820215 := bstep (se 1 (by rfl) ⟨2115161, by rfl⟩ : syracuseStep 2820215 = 4230323) B4230323
theorem B2820239 : Blo 1879141 2820239 := bstep (se 1 (by rfl) ⟨2115179, by rfl⟩ : syracuseStep 2820239 = 4230359) B4230359
theorem B2820281 : Blo 1879141 2820281 := bstep (se 2 (by rfl) ⟨1057605, by rfl⟩ : syracuseStep 2820281 = 2115211) B2115211
theorem B7137517 : Blo 1879141 7137517 := bstep (se 3 (by rfl) ⟨1338284, by rfl⟩ : syracuseStep 7137517 = 2676569) B2676569
theorem B2820359 : Blo 1879141 2820359 := bstep (se 1 (by rfl) ⟨2115269, by rfl⟩ : syracuseStep 2820359 = 4230539) B4230539
theorem B2820395 : Blo 1879141 2820395 := bstep (se 1 (by rfl) ⟨2115296, by rfl⟩ : syracuseStep 2820395 = 4230593) B4230593
theorem B2820425 : Blo 1879141 2820425 := bstep (se 2 (by rfl) ⟨1057659, by rfl⟩ : syracuseStep 2820425 = 2115319) B2115319
theorem B24095069 : Blo 1879141 24095069 := bstep (se 3 (by rfl) ⟨4517825, by rfl⟩ : syracuseStep 24095069 = 9035651) B9035651
theorem B5351795 : Blo 1879141 5351795 := bstep (se 1 (by rfl) ⟨4013846, by rfl⟩ : syracuseStep 5351795 = 8027693) B8027693
theorem B4229495 : Blo 1879141 4229495 := bstep (se 1 (by rfl) ⟨3172121, by rfl⟩ : syracuseStep 4229495 = 6344243) B6344243
theorem B2820539 : Blo 1879141 2820539 := bstep (se 1 (by rfl) ⟨2115404, by rfl⟩ : syracuseStep 2820539 = 4230809) B4230809
theorem B2820599 : Blo 1879141 2820599 := bstep (se 1 (by rfl) ⟨2115449, by rfl⟩ : syracuseStep 2820599 = 4230899) B4230899
theorem B2820623 : Blo 1879141 2820623 := bstep (se 1 (by rfl) ⟨2115467, by rfl⟩ : syracuseStep 2820623 = 4230935) B4230935
theorem B2116111 : Blo 1879141 2116111 := bstep (se 1 (by rfl) ⟨1587083, by rfl⟩ : syracuseStep 2116111 = 3174167) B3174167
theorem B7137821 : Blo 1879141 7137821 := bstep (se 3 (by rfl) ⟨1338341, by rfl⟩ : syracuseStep 7137821 = 2676683) B2676683
theorem B6777373 : Blo 1879141 6777373 := bstep (se 3 (by rfl) ⟨1270757, by rfl⟩ : syracuseStep 6777373 = 2541515) B2541515
theorem B4229675 : Blo 1879141 4229675 := bstep (se 1 (by rfl) ⟨3172256, by rfl⟩ : syracuseStep 4229675 = 6344513) B6344513
theorem B2820665 : Blo 1879141 2820665 := bstep (se 2 (by rfl) ⟨1057749, by rfl⟩ : syracuseStep 2820665 = 2115499) B2115499
theorem B3172999 : Blo 1879141 3172999 := bstep (se 1 (by rfl) ⟨2379749, by rfl⟩ : syracuseStep 3172999 = 4759499) B4759499
theorem B2820743 : Blo 1879141 2820743 := bstep (se 1 (by rfl) ⟨2115557, by rfl⟩ : syracuseStep 2820743 = 4231115) B4231115
theorem B2820779 : Blo 1879141 2820779 := bstep (se 1 (by rfl) ⟨2115584, by rfl⟩ : syracuseStep 2820779 = 4231169) B4231169
theorem B2820809 : Blo 1879141 2820809 := bstep (se 2 (by rfl) ⟨1057803, by rfl⟩ : syracuseStep 2820809 = 2115607) B2115607
theorem B9038537 : Blo 1879141 9038537 := bstep (se 2 (by rfl) ⟨3389451, by rfl⟩ : syracuseStep 9038537 = 6778903) B6778903
theorem B2820923 : Blo 1879141 2820923 := bstep (se 1 (by rfl) ⟨2115692, by rfl⟩ : syracuseStep 2820923 = 4231385) B4231385
theorem B9153395 : Blo 1879141 9153395 := bstep (se 1 (by rfl) ⟨6865046, by rfl⟩ : syracuseStep 9153395 = 13730093) B13730093
theorem B9522035 : Blo 1879141 9522035 := bstep (se 1 (by rfl) ⟨7141526, by rfl⟩ : syracuseStep 9522035 = 14283053) B14283053
theorem B2820983 : Blo 1879141 2820983 := bstep (se 1 (by rfl) ⟨2115737, by rfl⟩ : syracuseStep 2820983 = 4231475) B4231475
theorem B6269831 : Blo 1879141 6269831 := bstep (se 1 (by rfl) ⟨4702373, by rfl⟩ : syracuseStep 6269831 = 9404747) B9404747
theorem B2821007 : Blo 1879141 2821007 := bstep (se 1 (by rfl) ⟨2115755, by rfl⟩ : syracuseStep 2821007 = 4231511) B4231511
theorem B4230035 : Blo 1879141 4230035 := bstep (se 1 (by rfl) ⟨3172526, by rfl⟩ : syracuseStep 4230035 = 6345053) B6345053
theorem B27093923 : Blo 1879141 27093923 := bstep (se 1 (by rfl) ⟨20320442, by rfl⟩ : syracuseStep 27093923 = 40640885) B40640885
theorem B2821049 : Blo 1879141 2821049 := bstep (se 2 (by rfl) ⟨1057893, by rfl⟩ : syracuseStep 2821049 = 2115787) B2115787
theorem B4230089 : Blo 1879141 4230089 := bstep (se 2 (by rfl) ⟨1586283, by rfl⟩ : syracuseStep 4230089 = 3172567) B3172567
theorem B2821127 : Blo 1879141 2821127 := bstep (se 1 (by rfl) ⟨2115845, by rfl⟩ : syracuseStep 2821127 = 4231691) B4231691
theorem B2821163 : Blo 1879141 2821163 := bstep (se 1 (by rfl) ⟨2115872, by rfl⟩ : syracuseStep 2821163 = 4231745) B4231745
theorem B2821193 : Blo 1879141 2821193 := bstep (se 2 (by rfl) ⟨1057947, by rfl⟩ : syracuseStep 2821193 = 2115895) B2115895
theorem B10710103 : Blo 1879141 10710103 := bstep (se 1 (by rfl) ⟨8032577, by rfl⟩ : syracuseStep 10710103 = 16065155) B16065155
theorem B1879175 : Blo 1879141 1879175 := bstep (se 1 (by rfl) ⟨1409381, by rfl⟩ : syracuseStep 1879175 = 2818763) B2818763
theorem B121965709 : Blo 1879141 121965709 := bstep (se 3 (by rfl) ⟨22868570, by rfl⟩ : syracuseStep 121965709 = 45737141) B45737141
theorem B1879183 : Blo 1879141 1879183 := bstep (se 1 (by rfl) ⟨1409387, by rfl⟩ : syracuseStep 1879183 = 2818775) B2818775
theorem B1879227 : Blo 1879141 1879227 := bstep (se 1 (by rfl) ⟨1409420, by rfl⟩ : syracuseStep 1879227 = 2818841) B2818841
theorem B2821307 : Blo 1879141 2821307 := bstep (se 1 (by rfl) ⟨2115980, by rfl⟩ : syracuseStep 2821307 = 4231961) B4231961
theorem B2821367 : Blo 1879141 2821367 := bstep (se 1 (by rfl) ⟨2116025, by rfl⟩ : syracuseStep 2821367 = 4232051) B4232051
theorem B1879303 : Blo 1879141 1879303 := bstep (se 1 (by rfl) ⟨1409477, by rfl⟩ : syracuseStep 1879303 = 2818955) B2818955
theorem B1879311 : Blo 1879141 1879311 := bstep (se 1 (by rfl) ⟨1409483, by rfl⟩ : syracuseStep 1879311 = 2818967) B2818967
theorem B3173647 : Blo 1879141 3173647 := bstep (se 1 (by rfl) ⟨2380235, by rfl⟩ : syracuseStep 3173647 = 4760471) B4760471
theorem B2821391 : Blo 1879141 2821391 := bstep (se 1 (by rfl) ⟨2116043, by rfl⟩ : syracuseStep 2821391 = 4232087) B4232087
theorem B4017451 : Blo 1879141 4017451 := bstep (se 1 (by rfl) ⟨3013088, by rfl⟩ : syracuseStep 4017451 = 6026177) B6026177
theorem B2821433 : Blo 1879141 2821433 := bstep (se 2 (by rfl) ⟨1058037, by rfl⟩ : syracuseStep 2821433 = 2116075) B2116075
theorem B1879355 : Blo 1879141 1879355 := bstep (se 1 (by rfl) ⟨1409516, by rfl⟩ : syracuseStep 1879355 = 2819033) B2819033
theorem B5352763 : Blo 1879141 5352763 := bstep (se 1 (by rfl) ⟨4014572, by rfl⟩ : syracuseStep 5352763 = 8029145) B8029145
theorem B9522521 : Blo 1879141 9522521 := bstep (se 2 (by rfl) ⟨3570945, by rfl⟩ : syracuseStep 9522521 = 7141891) B7141891
theorem B6024563 : Blo 1879141 6024563 := bstep (se 1 (by rfl) ⟨4518422, by rfl⟩ : syracuseStep 6024563 = 9036845) B9036845
theorem B2379127 : Blo 1879141 2379127 := bstep (se 1 (by rfl) ⟨1784345, by rfl⟩ : syracuseStep 2379127 = 3568691) B3568691
theorem B20319623 : Blo 1879141 20319623 := bstep (se 1 (by rfl) ⟨15239717, by rfl⟩ : syracuseStep 20319623 = 30479435) B30479435
theorem B1879431 : Blo 1879141 1879431 := bstep (se 1 (by rfl) ⟨1409573, by rfl⟩ : syracuseStep 1879431 = 2819147) B2819147
theorem B2821511 : Blo 1879141 2821511 := bstep (se 1 (by rfl) ⟨2116133, by rfl⟩ : syracuseStep 2821511 = 4232267) B4232267
theorem B1879439 : Blo 1879141 1879439 := bstep (se 1 (by rfl) ⟨1409579, by rfl⟩ : syracuseStep 1879439 = 2819159) B2819159
theorem B2821547 : Blo 1879141 2821547 := bstep (se 1 (by rfl) ⟨2116160, by rfl⟩ : syracuseStep 2821547 = 4232321) B4232321
theorem B1879483 : Blo 1879141 1879483 := bstep (se 1 (by rfl) ⟨1409612, by rfl⟩ : syracuseStep 1879483 = 2819225) B2819225
theorem B2821577 : Blo 1879141 2821577 := bstep (se 2 (by rfl) ⟨1058091, by rfl⟩ : syracuseStep 2821577 = 2116183) B2116183
theorem B9031115 : Blo 1879141 9031115 := bstep (se 1 (by rfl) ⟨6773336, by rfl⟩ : syracuseStep 9031115 = 13546673) B13546673
theorem B16281091 : Blo 1879141 16281091 := bstep (se 1 (by rfl) ⟨12210818, by rfl⟩ : syracuseStep 16281091 = 24421637) B24421637
theorem B1879559 : Blo 1879141 1879559 := bstep (se 1 (by rfl) ⟨1409669, by rfl⟩ : syracuseStep 1879559 = 2819339) B2819339
theorem B1879567 : Blo 1879141 1879567 := bstep (se 1 (by rfl) ⟨1409675, by rfl⟩ : syracuseStep 1879567 = 2819351) B2819351
theorem B1879611 : Blo 1879141 1879611 := bstep (se 1 (by rfl) ⟨1409708, by rfl⟩ : syracuseStep 1879611 = 2819417) B2819417
theorem B2821691 : Blo 1879141 2821691 := bstep (se 1 (by rfl) ⟨2116268, by rfl⟩ : syracuseStep 2821691 = 4232537) B4232537
theorem B9514583 : Blo 1879141 9514583 := bstep (se 1 (by rfl) ⟨7135937, by rfl⟩ : syracuseStep 9514583 = 14271875) B14271875
theorem B1879687 : Blo 1879141 1879687 := bstep (se 1 (by rfl) ⟨1409765, by rfl⟩ : syracuseStep 1879687 = 2819531) B2819531
theorem B4230791 : Blo 1879141 4230791 := bstep (se 1 (by rfl) ⟨3173093, by rfl⟩ : syracuseStep 4230791 = 6346187) B6346187
theorem B1879695 : Blo 1879141 1879695 := bstep (se 1 (by rfl) ⟨1409771, by rfl⟩ : syracuseStep 1879695 = 2819543) B2819543
theorem B1879739 : Blo 1879141 1879739 := bstep (se 1 (by rfl) ⟨1409804, by rfl⟩ : syracuseStep 1879739 = 2819609) B2819609
theorem B2379451 : Blo 1879141 2379451 := bstep (se 1 (by rfl) ⟨1784588, by rfl⟩ : syracuseStep 2379451 = 3569177) B3569177
theorem B14274305 : Blo 1879141 14274305 := bstep (se 2 (by rfl) ⟨5352864, by rfl⟩ : syracuseStep 14274305 = 10705729) B10705729
theorem B1879815 : Blo 1879141 1879815 := bstep (se 1 (by rfl) ⟨1409861, by rfl⟩ : syracuseStep 1879815 = 2819723) B2819723
theorem B1879823 : Blo 1879141 1879823 := bstep (se 1 (by rfl) ⟨1409867, by rfl⟩ : syracuseStep 1879823 = 2819735) B2819735
theorem B3174187 : Blo 1879141 3174187 := bstep (se 1 (by rfl) ⟨2380640, by rfl⟩ : syracuseStep 3174187 = 4761281) B4761281
theorem B1879867 : Blo 1879141 1879867 := bstep (se 1 (by rfl) ⟨1409900, by rfl⟩ : syracuseStep 1879867 = 2819801) B2819801
theorem B4230971 : Blo 1879141 4230971 := bstep (se 1 (by rfl) ⟨3173228, by rfl⟩ : syracuseStep 4230971 = 6346457) B6346457
theorem B1879943 : Blo 1879141 1879943 := bstep (se 1 (by rfl) ⟨1409957, by rfl⟩ : syracuseStep 1879943 = 2819915) B2819915
theorem B1879951 : Blo 1879141 1879951 := bstep (se 1 (by rfl) ⟨1409963, by rfl⟩ : syracuseStep 1879951 = 2819927) B2819927
theorem B4231097 : Blo 1879141 4231097 := bstep (se 2 (by rfl) ⟨1586661, by rfl⟩ : syracuseStep 4231097 = 3173323) B3173323
theorem B3174329 : Blo 1879141 3174329 := bstep (se 2 (by rfl) ⟨1190373, by rfl⟩ : syracuseStep 3174329 = 2380747) B2380747
theorem B1879995 : Blo 1879141 1879995 := bstep (se 1 (by rfl) ⟨1409996, by rfl⟩ : syracuseStep 1879995 = 2819993) B2819993
theorem B10702813 : Blo 1879141 10702813 := bstep (se 3 (by rfl) ⟨2006777, by rfl⟩ : syracuseStep 10702813 = 4013555) B4013555
theorem B1880071 : Blo 1879141 1880071 := bstep (se 1 (by rfl) ⟨1410053, by rfl⟩ : syracuseStep 1880071 = 2820107) B2820107
theorem B1880079 : Blo 1879141 1880079 := bstep (se 1 (by rfl) ⟨1410059, by rfl⟩ : syracuseStep 1880079 = 2820119) B2820119
theorem B3010603 : Blo 1879141 3010603 := bstep (se 1 (by rfl) ⟨2257952, by rfl⟩ : syracuseStep 3010603 = 4515905) B4515905
theorem B9646123 : Blo 1879141 9646123 := bstep (se 1 (by rfl) ⟨7234592, by rfl⟩ : syracuseStep 9646123 = 14469185) B14469185
theorem B1880123 : Blo 1879141 1880123 := bstep (se 1 (by rfl) ⟨1410092, by rfl⟩ : syracuseStep 1880123 = 2820185) B2820185
theorem B9515069 : Blo 1879141 9515069 := bstep (se 3 (by rfl) ⟨1784075, by rfl⟩ : syracuseStep 9515069 = 3568151) B3568151
theorem B7139447 : Blo 1879141 7139447 := bstep (se 1 (by rfl) ⟨5354585, by rfl⟩ : syracuseStep 7139447 = 10709171) B10709171
theorem B1880199 : Blo 1879141 1880199 := bstep (se 1 (by rfl) ⟨1410149, by rfl⟩ : syracuseStep 1880199 = 2820299) B2820299
theorem B1880207 : Blo 1879141 1880207 := bstep (se 1 (by rfl) ⟨1410155, by rfl⟩ : syracuseStep 1880207 = 2820311) B2820311
theorem B5083289 : Blo 1879141 5083289 := bstep (se 2 (by rfl) ⟨1906233, by rfl⟩ : syracuseStep 5083289 = 3812467) B3812467
theorem B1880251 : Blo 1879141 1880251 := bstep (se 1 (by rfl) ⟨1410188, by rfl⟩ : syracuseStep 1880251 = 2820377) B2820377
theorem B3567817 : Blo 1879141 3567817 := bstep (se 2 (by rfl) ⟨1337931, by rfl⟩ : syracuseStep 3567817 = 2675863) B2675863
theorem B1880327 : Blo 1879141 1880327 := bstep (se 1 (by rfl) ⟨1410245, by rfl⟩ : syracuseStep 1880327 = 2820491) B2820491
theorem B1880335 : Blo 1879141 1880335 := bstep (se 1 (by rfl) ⟨1410251, by rfl⟩ : syracuseStep 1880335 = 2820503) B2820503
theorem B4231439 : Blo 1879141 4231439 := bstep (se 1 (by rfl) ⟨3173579, by rfl⟩ : syracuseStep 4231439 = 6347159) B6347159
theorem B4231457 : Blo 1879141 4231457 := bstep (se 2 (by rfl) ⟨1586796, by rfl⟩ : syracuseStep 4231457 = 3173593) B3173593
theorem B14479649 : Blo 1879141 14479649 := bstep (se 2 (by rfl) ⟨5429868, by rfl⟩ : syracuseStep 14479649 = 10859737) B10859737
theorem B10850597 : Blo 1879141 10850597 := bstep (se 4 (by rfl) ⟨1017243, by rfl⟩ : syracuseStep 10850597 = 2034487) B2034487
theorem B3010859 : Blo 1879141 3010859 := bstep (se 1 (by rfl) ⟨2258144, by rfl⟩ : syracuseStep 3010859 = 4516289) B4516289
theorem B1880379 : Blo 1879141 1880379 := bstep (se 1 (by rfl) ⟨1410284, by rfl⟩ : syracuseStep 1880379 = 2820569) B2820569
theorem B1880455 : Blo 1879141 1880455 := bstep (se 1 (by rfl) ⟨1410341, by rfl⟩ : syracuseStep 1880455 = 2820683) B2820683
theorem B1880463 : Blo 1879141 1880463 := bstep (se 1 (by rfl) ⟨1410347, by rfl⟩ : syracuseStep 1880463 = 2820695) B2820695
theorem B10162579 : Blo 1879141 10162579 := bstep (se 1 (by rfl) ⟨7621934, by rfl⟩ : syracuseStep 10162579 = 15243869) B15243869
theorem B6345107 : Blo 1879141 6345107 := bstep (se 1 (by rfl) ⟨4758830, by rfl⟩ : syracuseStep 6345107 = 9517661) B9517661
theorem B5353913 : Blo 1879141 5353913 := bstep (se 2 (by rfl) ⟨2007717, by rfl⟩ : syracuseStep 5353913 = 4015435) B4015435
theorem B1880507 : Blo 1879141 1880507 := bstep (se 1 (by rfl) ⟨1410380, by rfl⟩ : syracuseStep 1880507 = 2820761) B2820761
theorem B1880583 : Blo 1879141 1880583 := bstep (se 1 (by rfl) ⟨1410437, by rfl⟩ : syracuseStep 1880583 = 2820875) B2820875
theorem B1880591 : Blo 1879141 1880591 := bstep (se 1 (by rfl) ⟨1410443, by rfl⟩ : syracuseStep 1880591 = 2820887) B2820887
theorem B81293867 : Blo 1879141 81293867 := bstep (se 1 (by rfl) ⟨60970400, by rfl⟩ : syracuseStep 81293867 = 121940801) B121940801
theorem B1880635 : Blo 1879141 1880635 := bstep (se 1 (by rfl) ⟨1410476, by rfl⟩ : syracuseStep 1880635 = 2820953) B2820953
theorem B6435389 : Blo 1879141 6435389 := bstep (se 3 (by rfl) ⟨1206635, by rfl⟩ : syracuseStep 6435389 = 2413271) B2413271
theorem B4231799 : Blo 1879141 4231799 := bstep (se 1 (by rfl) ⟨3173849, by rfl⟩ : syracuseStep 4231799 = 6347699) B6347699
theorem B1880711 : Blo 1879141 1880711 := bstep (se 1 (by rfl) ⟨1410533, by rfl⟩ : syracuseStep 1880711 = 2821067) B2821067
theorem B2380423 : Blo 1879141 2380423 := bstep (se 1 (by rfl) ⟨1785317, by rfl⟩ : syracuseStep 2380423 = 3570635) B3570635
theorem B1880719 : Blo 1879141 1880719 := bstep (se 1 (by rfl) ⟨1410539, by rfl⟩ : syracuseStep 1880719 = 2821079) B2821079
theorem B1880763 : Blo 1879141 1880763 := bstep (se 1 (by rfl) ⟨1410572, by rfl⟩ : syracuseStep 1880763 = 2821145) B2821145
theorem B1880839 : Blo 1879141 1880839 := bstep (se 1 (by rfl) ⟨1410629, by rfl⟩ : syracuseStep 1880839 = 2821259) B2821259
theorem B5354255 : Blo 1879141 5354255 := bstep (se 1 (by rfl) ⟨4015691, by rfl⟩ : syracuseStep 5354255 = 8031383) B8031383
theorem B1880847 : Blo 1879141 1880847 := bstep (se 1 (by rfl) ⟨1410635, by rfl⟩ : syracuseStep 1880847 = 2821271) B2821271
theorem B8033057 : Blo 1879141 8033057 := bstep (se 2 (by rfl) ⟨3012396, by rfl⟩ : syracuseStep 8033057 = 6024793) B6024793
theorem B4231979 : Blo 1879141 4231979 := bstep (se 1 (by rfl) ⟨3173984, by rfl⟩ : syracuseStep 4231979 = 6347969) B6347969
theorem B1880891 : Blo 1879141 1880891 := bstep (se 1 (by rfl) ⟨1410668, by rfl⟩ : syracuseStep 1880891 = 2821337) B2821337
theorem B1880967 : Blo 1879141 1880967 := bstep (se 1 (by rfl) ⟨1410725, by rfl⟩ : syracuseStep 1880967 = 2821451) B2821451
theorem B1880975 : Blo 1879141 1880975 := bstep (se 1 (by rfl) ⟨1410731, by rfl⟩ : syracuseStep 1880975 = 2821463) B2821463
theorem B3568531 : Blo 1879141 3568531 := bstep (se 1 (by rfl) ⟨2676398, by rfl⟩ : syracuseStep 3568531 = 5352797) B5352797
theorem B16069529 : Blo 1879141 16069529 := bstep (se 2 (by rfl) ⟨6026073, by rfl⟩ : syracuseStep 16069529 = 12052147) B12052147
theorem B34780067 : Blo 1879141 34780067 := bstep (se 1 (by rfl) ⟨26085050, by rfl⟩ : syracuseStep 34780067 = 52170101) B52170101
theorem B1881019 : Blo 1879141 1881019 := bstep (se 1 (by rfl) ⟨1410764, by rfl⟩ : syracuseStep 1881019 = 2821529) B2821529
theorem B1881095 : Blo 1879141 1881095 := bstep (se 1 (by rfl) ⟨1410821, by rfl⟩ : syracuseStep 1881095 = 2821643) B2821643
theorem B1881103 : Blo 1879141 1881103 := bstep (se 1 (by rfl) ⟨1410827, by rfl⟩ : syracuseStep 1881103 = 2821655) B2821655
theorem B10712087 : Blo 1879141 10712087 := bstep (se 1 (by rfl) ⟨8034065, by rfl⟩ : syracuseStep 10712087 = 16068131) B16068131
theorem B7238717 : Blo 1879141 7238717 := bstep (se 3 (by rfl) ⟨1357259, by rfl⟩ : syracuseStep 7238717 = 2714519) B2714519
theorem B7140419 : Blo 1879141 7140419 := bstep (se 1 (by rfl) ⟨5355314, by rfl⟩ : syracuseStep 7140419 = 10710629) B10710629
theorem B4232339 : Blo 1879141 4232339 := bstep (se 1 (by rfl) ⟨3174254, by rfl⟩ : syracuseStep 4232339 = 6348509) B6348509
theorem B4232393 : Blo 1879141 4232393 := bstep (se 2 (by rfl) ⟨1587147, by rfl⟩ : syracuseStep 4232393 = 3174295) B3174295
theorem B8033671 : Blo 1879141 8033671 := bstep (se 1 (by rfl) ⟨6025253, by rfl⟩ : syracuseStep 8033671 = 12050507) B12050507
theorem B18060691 : Blo 1879141 18060691 := bstep (se 1 (by rfl) ⟨13545518, by rfl⟩ : syracuseStep 18060691 = 27091037) B27091037
theorem B5355143 : Blo 1879141 5355143 := bstep (se 1 (by rfl) ⟨4016357, by rfl⟩ : syracuseStep 5355143 = 8032715) B8032715
theorem B21698227 : Blo 1879141 21698227 := bstep (se 1 (by rfl) ⟨16273670, by rfl⟩ : syracuseStep 21698227 = 32547341) B32547341
theorem B8935105 : Blo 1879141 8935105 := bstep (se 2 (by rfl) ⟨3350664, by rfl⟩ : syracuseStep 8935105 = 6701329) B6701329
theorem B18077377 : Blo 1879141 18077377 := bstep (se 2 (by rfl) ⟨6779016, by rfl⟩ : syracuseStep 18077377 = 13558033) B13558033
theorem B12048101 : Blo 1879141 12048101 := bstep (se 4 (by rfl) ⟨1129509, by rfl⟩ : syracuseStep 12048101 = 2259019) B2259019
theorem B6346511 : Blo 1879141 6346511 := bstep (se 1 (by rfl) ⟨4759883, by rfl⟩ : syracuseStep 6346511 = 9519767) B9519767
theorem B20322083 : Blo 1879141 20322083 := bstep (se 1 (by rfl) ⟨15241562, by rfl⟩ : syracuseStep 20322083 = 30483125) B30483125
theorem B9516851 : Blo 1879141 9516851 := bstep (se 1 (by rfl) ⟨7137638, by rfl⟩ : syracuseStep 9516851 = 14275277) B14275277
theorem B5355325 : Blo 1879141 5355325 := bstep (se 3 (by rfl) ⟨1004123, by rfl⟩ : syracuseStep 5355325 = 2008247) B2008247
theorem B41768779 : Blo 1879141 41768779 := bstep (se 1 (by rfl) ⟨31326584, by rfl⟩ : syracuseStep 41768779 = 62653169) B62653169
theorem B4757363 : Blo 1879141 4757363 := bstep (se 1 (by rfl) ⟨3568022, by rfl⟩ : syracuseStep 4757363 = 7136045) B7136045
theorem B2258875 : Blo 1879141 2258875 := bstep (se 1 (by rfl) ⟨1694156, by rfl⟩ : syracuseStep 2258875 = 3388313) B3388313
theorem B3569609 : Blo 1879141 3569609 := bstep (se 2 (by rfl) ⟨1338603, by rfl⟩ : syracuseStep 3569609 = 2677207) B2677207
theorem B6772747 : Blo 1879141 6772747 := bstep (se 1 (by rfl) ⟨5079560, by rfl⟩ : syracuseStep 6772747 = 10159121) B10159121
theorem B6346781 : Blo 1879141 6346781 := bstep (se 3 (by rfl) ⟨1190021, by rfl⟩ : syracuseStep 6346781 = 2380043) B2380043
theorem B7141405 : Blo 1879141 7141405 := bstep (se 3 (by rfl) ⟨1339013, by rfl⟩ : syracuseStep 7141405 = 2678027) B2678027
theorem B5355553 : Blo 1879141 5355553 := bstep (se 2 (by rfl) ⟨2008332, by rfl⟩ : syracuseStep 5355553 = 4016665) B4016665
theorem B34297901 : Blo 1879141 34297901 := bstep (se 3 (by rfl) ⟨6430856, by rfl⟩ : syracuseStep 34297901 = 12861713) B12861713
theorem B10164311 : Blo 1879141 10164311 := bstep (se 1 (by rfl) ⟨7623233, by rfl⟩ : syracuseStep 10164311 = 15246467) B15246467
theorem B9517175 : Blo 1879141 9517175 := bstep (se 1 (by rfl) ⟨7137881, by rfl⟩ : syracuseStep 9517175 = 14275763) B14275763
theorem B4757879 : Blo 1879141 4757879 := bstep (se 1 (by rfl) ⟨3568409, by rfl⟩ : syracuseStep 4757879 = 7136819) B7136819
theorem B5355895 : Blo 1879141 5355895 := bstep (se 1 (by rfl) ⟨4016921, by rfl⟩ : syracuseStep 5355895 = 8033843) B8033843
theorem B6273433 : Blo 1879141 6273433 := bstep (se 2 (by rfl) ⟨2352537, by rfl⟩ : syracuseStep 6273433 = 4705075) B4705075
theorem B18315841 : Blo 1879141 18315841 := bstep (se 2 (by rfl) ⟨6868440, by rfl⟩ : syracuseStep 18315841 = 13736881) B13736881
theorem B2677321 : Blo 1879141 2677321 := bstep (se 2 (by rfl) ⟨1003995, by rfl⟩ : syracuseStep 2677321 = 2007991) B2007991
theorem B2898505 : Blo 1879141 2898505 := bstep (se 2 (by rfl) ⟨1086939, by rfl⟩ : syracuseStep 2898505 = 2173879) B2173879
theorem B3570475 : Blo 1879141 3570475 := bstep (se 1 (by rfl) ⟨2677856, by rfl⟩ : syracuseStep 3570475 = 5355713) B5355713
theorem B12041075 : Blo 1879141 12041075 := bstep (se 1 (by rfl) ⟨9030806, by rfl⟩ : syracuseStep 12041075 = 18061613) B18061613
theorem B34315123 : Blo 1879141 34315123 := bstep (se 1 (by rfl) ⟨25736342, by rfl⟩ : syracuseStep 34315123 = 51472685) B51472685
theorem B3570551 : Blo 1879141 3570551 := bstep (se 1 (by rfl) ⟨2677913, by rfl⟩ : syracuseStep 3570551 = 5355827) B5355827
theorem B10853273 : Blo 1879141 10853273 := bstep (se 2 (by rfl) ⟨4069977, by rfl⟩ : syracuseStep 10853273 = 8139955) B8139955
theorem B27483043 : Blo 1879141 27483043 := bstep (se 1 (by rfl) ⟨20612282, by rfl⟩ : syracuseStep 27483043 = 41224565) B41224565
theorem B9518147 : Blo 1879141 9518147 := bstep (se 1 (by rfl) ⟨7138610, by rfl⟩ : syracuseStep 9518147 = 14277221) B14277221
theorem B4824335 : Blo 1879141 4824335 := bstep (se 1 (by rfl) ⟨3618251, by rfl⟩ : syracuseStep 4824335 = 7236503) B7236503
theorem B5356829 : Blo 1879141 5356829 := bstep (se 3 (by rfl) ⟨1004405, by rfl⟩ : syracuseStep 5356829 = 2008811) B2008811
theorem B4758871 : Blo 1879141 4758871 := bstep (se 1 (by rfl) ⟨3569153, by rfl⟩ : syracuseStep 4758871 = 7138307) B7138307
theorem B6774131 : Blo 1879141 6774131 := bstep (se 1 (by rfl) ⟨5080598, by rfl⟩ : syracuseStep 6774131 = 10161197) B10161197
theorem B9518471 : Blo 1879141 9518471 := bstep (se 1 (by rfl) ⟨7138853, by rfl⟩ : syracuseStep 9518471 = 14277707) B14277707
theorem B6348185 : Blo 1879141 6348185 := bstep (se 2 (by rfl) ⟨2380569, by rfl⟩ : syracuseStep 6348185 = 4761139) B4761139
theorem B4759175 : Blo 1879141 4759175 := bstep (se 1 (by rfl) ⟨3569381, by rfl⟩ : syracuseStep 4759175 = 7138763) B7138763
theorem B4759307 : Blo 1879141 4759307 := bstep (se 1 (by rfl) ⟨3569480, by rfl⟩ : syracuseStep 4759307 = 7138961) B7138961
theorem B3719047 : Blo 1879141 3719047 := bstep (se 1 (by rfl) ⟨2789285, by rfl⟩ : syracuseStep 3719047 = 5578571) B5578571
theorem B9519119 : Blo 1879141 9519119 := bstep (se 1 (by rfl) ⟨7139339, by rfl⟩ : syracuseStep 9519119 = 14278679) B14278679
theorem B4014137 : Blo 1879141 4014137 := bstep (se 2 (by rfl) ⟨1505301, by rfl⟩ : syracuseStep 4014137 = 3010603) B3010603
theorem B12861497 : Blo 1879141 12861497 := bstep (se 2 (by rfl) ⟨4823061, by rfl⟩ : syracuseStep 12861497 = 9646123) B9646123
theorem B4759631 : Blo 1879141 4759631 := bstep (se 1 (by rfl) ⟨3569723, by rfl⟩ : syracuseStep 4759631 = 7139447) B7139447
theorem B7233731 : Blo 1879141 7233731 := bstep (se 1 (by rfl) ⟨5425298, by rfl⟩ : syracuseStep 7233731 = 10850597) B10850597
theorem B2007239 : Blo 1879141 2007239 := bstep (se 1 (by rfl) ⟨1505429, by rfl⟩ : syracuseStep 2007239 = 3010859) B3010859
theorem B2539883 : Blo 1879141 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B13550105 : Blo 1879141 13550105 := bstep (se 2 (by rfl) ⟨5081289, by rfl⟩ : syracuseStep 13550105 = 10162579) B10162579
theorem B8364577 : Blo 1879141 8364577 := bstep (se 2 (by rfl) ⟨3136716, by rfl⟩ : syracuseStep 8364577 = 6273433) B6273433
theorem B9036497 : Blo 1879141 9036497 := bstep (se 2 (by rfl) ⟨3388686, by rfl⟩ : syracuseStep 9036497 = 6777373) B6777373
theorem B4825811 : Blo 1879141 4825811 := bstep (se 1 (by rfl) ⟨3619358, by rfl⟩ : syracuseStep 4825811 = 7238717) B7238717
theorem B4760279 : Blo 1879141 4760279 := bstep (se 1 (by rfl) ⟨3570209, by rfl⟩ : syracuseStep 4760279 = 7140419) B7140419
theorem B24421121 : Blo 1879141 24421121 := bstep (se 2 (by rfl) ⟨9157920, by rfl⟩ : syracuseStep 24421121 = 18315841) B18315841
theorem B2818991 : Blo 1879141 2818991 := bstep (se 1 (by rfl) ⟨2114243, by rfl⟩ : syracuseStep 2818991 = 4228487) B4228487
theorem B2819081 : Blo 1879141 2819081 := bstep (se 2 (by rfl) ⟨1057155, by rfl⟩ : syracuseStep 2819081 = 2114311) B2114311
theorem B2819111 : Blo 1879141 2819111 := bstep (se 1 (by rfl) ⟨2114333, by rfl⟩ : syracuseStep 2819111 = 4228667) B4228667
theorem B2114599 : Blo 1879141 2114599 := bstep (se 1 (by rfl) ⟨1585949, by rfl⟩ : syracuseStep 2114599 = 3171899) B3171899
theorem B4760633 : Blo 1879141 4760633 := bstep (se 2 (by rfl) ⟨1785237, by rfl⟩ : syracuseStep 4760633 = 3570475) B3570475
theorem B2819195 : Blo 1879141 2819195 := bstep (se 1 (by rfl) ⟨2114396, by rfl⟩ : syracuseStep 2819195 = 4228793) B4228793
theorem B45753497 : Blo 1879141 45753497 := bstep (se 2 (by rfl) ⟨17157561, by rfl⟩ : syracuseStep 45753497 = 34315123) B34315123
theorem B36644057 : Blo 1879141 36644057 := bstep (se 2 (by rfl) ⟨13741521, by rfl⟩ : syracuseStep 36644057 = 27483043) B27483043
theorem B4228343 : Blo 1879141 4228343 := bstep (se 1 (by rfl) ⟨3171257, by rfl⟩ : syracuseStep 4228343 = 6342515) B6342515
theorem B3171575 : Blo 1879141 3171575 := bstep (se 1 (by rfl) ⟨2378681, by rfl⟩ : syracuseStep 3171575 = 4757363) B4757363
theorem B2819321 : Blo 1879141 2819321 := bstep (se 2 (by rfl) ⟨1057245, by rfl⟩ : syracuseStep 2819321 = 2114491) B2114491
theorem B2819423 : Blo 1879141 2819423 := bstep (se 1 (by rfl) ⟨2114567, by rfl⟩ : syracuseStep 2819423 = 4229135) B4229135
theorem B2819435 : Blo 1879141 2819435 := bstep (se 1 (by rfl) ⟨2114576, by rfl⟩ : syracuseStep 2819435 = 4229153) B4229153
theorem B22865267 : Blo 1879141 22865267 := bstep (se 1 (by rfl) ⟨17148950, by rfl⟩ : syracuseStep 22865267 = 34297901) B34297901
theorem B6776207 : Blo 1879141 6776207 := bstep (se 1 (by rfl) ⟨5082155, by rfl⟩ : syracuseStep 6776207 = 10164311) B10164311
theorem B14280137 : Blo 1879141 14280137 := bstep (se 2 (by rfl) ⟨5355051, by rfl⟩ : syracuseStep 14280137 = 10710103) B10710103
theorem B162620945 : Blo 1879141 162620945 := bstep (se 2 (by rfl) ⟨60982854, by rfl⟩ : syracuseStep 162620945 = 121965709) B121965709
theorem B3171919 : Blo 1879141 3171919 := bstep (se 1 (by rfl) ⟨2378939, by rfl⟩ : syracuseStep 3171919 = 4757879) B4757879
theorem B2819663 : Blo 1879141 2819663 := bstep (se 1 (by rfl) ⟨2114747, by rfl⟩ : syracuseStep 2819663 = 4229495) B4229495
theorem B2819783 : Blo 1879141 2819783 := bstep (se 1 (by rfl) ⟨2114837, by rfl⟩ : syracuseStep 2819783 = 4229675) B4229675
theorem B7137017 : Blo 1879141 7137017 := bstep (se 2 (by rfl) ⟨2676381, by rfl⟩ : syracuseStep 7137017 = 5352763) B5352763
theorem B4228937 : Blo 1879141 4228937 := bstep (se 2 (by rfl) ⟨1585851, by rfl⟩ : syracuseStep 4228937 = 3171703) B3171703
theorem B3172169 : Blo 1879141 3172169 := bstep (se 2 (by rfl) ⟨1189563, by rfl⟩ : syracuseStep 3172169 = 2379127) B2379127
theorem B2819945 : Blo 1879141 2819945 := bstep (se 2 (by rfl) ⟨1057479, by rfl⟩ : syracuseStep 2819945 = 2114959) B2114959
theorem B4179887 : Blo 1879141 4179887 := bstep (se 1 (by rfl) ⟨3134915, by rfl⟩ : syracuseStep 4179887 = 6269831) B6269831
theorem B2820023 : Blo 1879141 2820023 := bstep (se 1 (by rfl) ⟨2115017, by rfl⟩ : syracuseStep 2820023 = 4230035) B4230035
theorem B7235515 : Blo 1879141 7235515 := bstep (se 1 (by rfl) ⟨5426636, by rfl⟩ : syracuseStep 7235515 = 10853273) B10853273
theorem B16058321 : Blo 1879141 16058321 := bstep (se 2 (by rfl) ⟨6021870, by rfl⟩ : syracuseStep 16058321 = 12043741) B12043741
theorem B2820059 : Blo 1879141 2820059 := bstep (se 1 (by rfl) ⟨2115044, by rfl⟩ : syracuseStep 2820059 = 4230089) B4230089
theorem B4516087 : Blo 1879141 4516087 := bstep (se 1 (by rfl) ⟨3387065, by rfl⟩ : syracuseStep 4516087 = 6774131) B6774131
theorem B4016375 : Blo 1879141 4016375 := bstep (se 1 (by rfl) ⟨3012281, by rfl⟩ : syracuseStep 4016375 = 6024563) B6024563
theorem B3172601 : Blo 1879141 3172601 := bstep (se 2 (by rfl) ⟨1189725, by rfl⟩ : syracuseStep 3172601 = 2379451) B2379451
theorem B11913473 : Blo 1879141 11913473 := bstep (se 2 (by rfl) ⟨4467552, by rfl⟩ : syracuseStep 11913473 = 8935105) B8935105
theorem B24103169 : Blo 1879141 24103169 := bstep (se 2 (by rfl) ⟨9038688, by rfl⟩ : syracuseStep 24103169 = 18077377) B18077377
theorem B6343055 : Blo 1879141 6343055 := bstep (se 1 (by rfl) ⟨4757291, by rfl⟩ : syracuseStep 6343055 = 9514583) B9514583
theorem B3172783 : Blo 1879141 3172783 := bstep (se 1 (by rfl) ⟨2379587, by rfl⟩ : syracuseStep 3172783 = 4759175) B4759175
theorem B2820527 : Blo 1879141 2820527 := bstep (se 1 (by rfl) ⟨2115395, by rfl⟩ : syracuseStep 2820527 = 4230791) B4230791
theorem B55691705 : Blo 1879141 55691705 := bstep (se 2 (by rfl) ⟨20884389, by rfl⟩ : syracuseStep 55691705 = 41768779) B41768779
theorem B3172871 : Blo 1879141 3172871 := bstep (se 1 (by rfl) ⟨2379653, by rfl⟩ : syracuseStep 3172871 = 4759307) B4759307
theorem B2820617 : Blo 1879141 2820617 := bstep (se 2 (by rfl) ⟨1057731, by rfl⟩ : syracuseStep 2820617 = 2115463) B2115463
theorem B4958729 : Blo 1879141 4958729 := bstep (se 2 (by rfl) ⟨1859523, by rfl⟩ : syracuseStep 4958729 = 3719047) B3719047
theorem B2820647 : Blo 1879141 2820647 := bstep (se 1 (by rfl) ⟨2115485, by rfl⟩ : syracuseStep 2820647 = 4230971) B4230971
theorem B4229729 : Blo 1879141 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B2820731 : Blo 1879141 2820731 := bstep (se 1 (by rfl) ⟨2115548, by rfl⟩ : syracuseStep 2820731 = 4231097) B4231097
theorem B2116219 : Blo 1879141 2116219 := bstep (se 1 (by rfl) ⟨1587164, by rfl⟩ : syracuseStep 2116219 = 3174329) B3174329
theorem B9030329 : Blo 1879141 9030329 := bstep (se 2 (by rfl) ⟨3386373, by rfl⟩ : syracuseStep 9030329 = 6772747) B6772747
theorem B9521873 : Blo 1879141 9521873 := bstep (se 2 (by rfl) ⟨3570702, by rfl⟩ : syracuseStep 9521873 = 7141405) B7141405
theorem B6343379 : Blo 1879141 6343379 := bstep (se 1 (by rfl) ⟨4757534, by rfl⟩ : syracuseStep 6343379 = 9515069) B9515069
theorem B7138003 : Blo 1879141 7138003 := bstep (se 1 (by rfl) ⟨5353502, by rfl⟩ : syracuseStep 7138003 = 10707005) B10707005
theorem B2820857 : Blo 1879141 2820857 := bstep (se 2 (by rfl) ⟨1057821, by rfl⟩ : syracuseStep 2820857 = 2115643) B2115643
theorem B3173215 : Blo 1879141 3173215 := bstep (se 1 (by rfl) ⟨2379911, by rfl⟩ : syracuseStep 3173215 = 4759823) B4759823
theorem B2820959 : Blo 1879141 2820959 := bstep (se 1 (by rfl) ⟨2115719, by rfl⟩ : syracuseStep 2820959 = 4231439) B4231439
theorem B2820971 : Blo 1879141 2820971 := bstep (se 1 (by rfl) ⟨2115728, by rfl⟩ : syracuseStep 2820971 = 4231457) B4231457
theorem B9653099 : Blo 1879141 9653099 := bstep (se 1 (by rfl) ⟨7239824, by rfl⟩ : syracuseStep 9653099 = 14479649) B14479649
theorem B4230071 : Blo 1879141 4230071 := bstep (se 1 (by rfl) ⟨3172553, by rfl⟩ : syracuseStep 4230071 = 6345107) B6345107
theorem B3173303 : Blo 1879141 3173303 := bstep (se 1 (by rfl) ⟨2379977, by rfl⟩ : syracuseStep 3173303 = 4759955) B4759955
theorem B10169345 : Blo 1879141 10169345 := bstep (se 2 (by rfl) ⟨3813504, by rfl⟩ : syracuseStep 10169345 = 7627009) B7627009
theorem B5352455 : Blo 1879141 5352455 := bstep (se 1 (by rfl) ⟨4014341, by rfl⟩ : syracuseStep 5352455 = 8028683) B8028683
theorem B2821199 : Blo 1879141 2821199 := bstep (se 1 (by rfl) ⟨2115899, by rfl⟩ : syracuseStep 2821199 = 4231799) B4231799
theorem B1879163 : Blo 1879141 1879163 := bstep (se 1 (by rfl) ⟨1409372, by rfl⟩ : syracuseStep 1879163 = 2818745) B2818745
theorem B4287659 : Blo 1879141 4287659 := bstep (se 1 (by rfl) ⟨3215744, by rfl⟩ : syracuseStep 4287659 = 6431489) B6431489
theorem B7138475 : Blo 1879141 7138475 := bstep (se 1 (by rfl) ⟨5353856, by rfl⟩ : syracuseStep 7138475 = 10707713) B10707713
theorem B1879215 : Blo 1879141 1879215 := bstep (se 1 (by rfl) ⟨1409411, by rfl⟩ : syracuseStep 1879215 = 2818823) B2818823
theorem B1879239 : Blo 1879141 1879239 := bstep (se 1 (by rfl) ⟨1409429, by rfl⟩ : syracuseStep 1879239 = 2818859) B2818859
theorem B2821319 : Blo 1879141 2821319 := bstep (se 1 (by rfl) ⟨2115989, by rfl⟩ : syracuseStep 2821319 = 4231979) B4231979
theorem B1879259 : Blo 1879141 1879259 := bstep (se 1 (by rfl) ⟨1409444, by rfl⟩ : syracuseStep 1879259 = 2818889) B2818889
theorem B23186711 : Blo 1879141 23186711 := bstep (se 1 (by rfl) ⟨17390033, by rfl⟩ : syracuseStep 23186711 = 34780067) B34780067
theorem B1879335 : Blo 1879141 1879335 := bstep (se 1 (by rfl) ⟨1409501, by rfl⟩ : syracuseStep 1879335 = 2819003) B2819003
theorem B1879375 : Blo 1879141 1879375 := bstep (se 1 (by rfl) ⟨1409531, by rfl⟩ : syracuseStep 1879375 = 2819063) B2819063
theorem B1879391 : Blo 1879141 1879391 := bstep (se 1 (by rfl) ⟨1409543, by rfl⟩ : syracuseStep 1879391 = 2819087) B2819087
theorem B2821481 : Blo 1879141 2821481 := bstep (se 2 (by rfl) ⟨1058055, by rfl⟩ : syracuseStep 2821481 = 2116111) B2116111
theorem B1879419 : Blo 1879141 1879419 := bstep (se 1 (by rfl) ⟨1409564, by rfl⟩ : syracuseStep 1879419 = 2819129) B2819129
theorem B1879471 : Blo 1879141 1879471 := bstep (se 1 (by rfl) ⟨1409603, by rfl⟩ : syracuseStep 1879471 = 2819207) B2819207
theorem B2821559 : Blo 1879141 2821559 := bstep (se 1 (by rfl) ⟨2116169, by rfl⟩ : syracuseStep 2821559 = 4232339) B4232339
theorem B1879495 : Blo 1879141 1879495 := bstep (se 1 (by rfl) ⟨1409621, by rfl⟩ : syracuseStep 1879495 = 2819243) B2819243
theorem B1879515 : Blo 1879141 1879515 := bstep (se 1 (by rfl) ⟨1409636, by rfl⟩ : syracuseStep 1879515 = 2819273) B2819273
theorem B2821595 : Blo 1879141 2821595 := bstep (se 1 (by rfl) ⟨2116196, by rfl⟩ : syracuseStep 2821595 = 4232393) B4232393
theorem B4230665 : Blo 1879141 4230665 := bstep (se 2 (by rfl) ⟨1586499, by rfl⟩ : syracuseStep 4230665 = 3172999) B3172999
theorem B3173897 : Blo 1879141 3173897 := bstep (se 2 (by rfl) ⟨1190211, by rfl⟩ : syracuseStep 3173897 = 2380423) B2380423
theorem B1879591 : Blo 1879141 1879591 := bstep (se 1 (by rfl) ⟨1409693, by rfl⟩ : syracuseStep 1879591 = 2819387) B2819387
theorem B1879631 : Blo 1879141 1879631 := bstep (se 1 (by rfl) ⟨1409723, by rfl⟩ : syracuseStep 1879631 = 2819447) B2819447
theorem B13037143 : Blo 1879141 13037143 := bstep (se 1 (by rfl) ⟨9777857, by rfl⟩ : syracuseStep 13037143 = 19555715) B19555715
theorem B1879647 : Blo 1879141 1879647 := bstep (se 1 (by rfl) ⟨1409735, by rfl⟩ : syracuseStep 1879647 = 2819471) B2819471
theorem B1879675 : Blo 1879141 1879675 := bstep (se 1 (by rfl) ⟨1409756, by rfl⟩ : syracuseStep 1879675 = 2819513) B2819513
theorem B1879727 : Blo 1879141 1879727 := bstep (se 1 (by rfl) ⟨1409795, by rfl⟩ : syracuseStep 1879727 = 2819591) B2819591
theorem B3174059 : Blo 1879141 3174059 := bstep (se 1 (by rfl) ⟨2380544, by rfl⟩ : syracuseStep 3174059 = 4761089) B4761089
theorem B1879751 : Blo 1879141 1879751 := bstep (se 1 (by rfl) ⟨1409813, by rfl⟩ : syracuseStep 1879751 = 2819627) B2819627
theorem B1879771 : Blo 1879141 1879771 := bstep (se 1 (by rfl) ⟨1409828, by rfl⟩ : syracuseStep 1879771 = 2819657) B2819657
theorem B9514745 : Blo 1879141 9514745 := bstep (se 2 (by rfl) ⟨3568029, by rfl⟩ : syracuseStep 9514745 = 7136059) B7136059
theorem B1879847 : Blo 1879141 1879847 := bstep (se 1 (by rfl) ⟨1409885, by rfl⟩ : syracuseStep 1879847 = 2819771) B2819771
theorem B8032067 : Blo 1879141 8032067 := bstep (se 1 (by rfl) ⟨6024050, by rfl⟩ : syracuseStep 8032067 = 12048101) B12048101
theorem B1879887 : Blo 1879141 1879887 := bstep (se 1 (by rfl) ⟨1409915, by rfl⟩ : syracuseStep 1879887 = 2819831) B2819831
theorem B6516575 : Blo 1879141 6516575 := bstep (se 1 (by rfl) ⟨4887431, by rfl⟩ : syracuseStep 6516575 = 9774863) B9774863
theorem B1879903 : Blo 1879141 1879903 := bstep (se 1 (by rfl) ⟨1409927, by rfl⟩ : syracuseStep 1879903 = 2819855) B2819855
theorem B4231007 : Blo 1879141 4231007 := bstep (se 1 (by rfl) ⟨3173255, by rfl⟩ : syracuseStep 4231007 = 6346511) B6346511
theorem B6344567 : Blo 1879141 6344567 := bstep (se 1 (by rfl) ⟨4758425, by rfl⟩ : syracuseStep 6344567 = 9516851) B9516851
theorem B1879931 : Blo 1879141 1879931 := bstep (se 1 (by rfl) ⟨1409948, by rfl⟩ : syracuseStep 1879931 = 2819897) B2819897
theorem B1879983 : Blo 1879141 1879983 := bstep (se 1 (by rfl) ⟨1409987, by rfl⟩ : syracuseStep 1879983 = 2819975) B2819975
theorem B1880007 : Blo 1879141 1880007 := bstep (se 1 (by rfl) ⟨1410005, by rfl⟩ : syracuseStep 1880007 = 2820011) B2820011
theorem B1880027 : Blo 1879141 1880027 := bstep (se 1 (by rfl) ⟨1410020, by rfl⟩ : syracuseStep 1880027 = 2820041) B2820041
theorem B3567635 : Blo 1879141 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B4231187 : Blo 1879141 4231187 := bstep (se 1 (by rfl) ⟨3173390, by rfl⟩ : syracuseStep 4231187 = 6346781) B6346781
theorem B1880103 : Blo 1879141 1880103 := bstep (se 1 (by rfl) ⟨1410077, by rfl⟩ : syracuseStep 1880103 = 2820155) B2820155
theorem B6344783 : Blo 1879141 6344783 := bstep (se 1 (by rfl) ⟨4758587, by rfl⟩ : syracuseStep 6344783 = 9517175) B9517175
theorem B1880143 : Blo 1879141 1880143 := bstep (se 1 (by rfl) ⟨1410107, by rfl⟩ : syracuseStep 1880143 = 2820215) B2820215
theorem B1880159 : Blo 1879141 1880159 := bstep (se 1 (by rfl) ⟨1410119, by rfl⟩ : syracuseStep 1880159 = 2820239) B2820239
theorem B1880187 : Blo 1879141 1880187 := bstep (se 1 (by rfl) ⟨1410140, by rfl⟩ : syracuseStep 1880187 = 2820281) B2820281
theorem B1880239 : Blo 1879141 1880239 := bstep (se 1 (by rfl) ⟨1410179, by rfl⟩ : syracuseStep 1880239 = 2820359) B2820359
theorem B1880263 : Blo 1879141 1880263 := bstep (se 1 (by rfl) ⟨1410197, by rfl⟩ : syracuseStep 1880263 = 2820395) B2820395
theorem B1880283 : Blo 1879141 1880283 := bstep (se 1 (by rfl) ⟨1410212, by rfl⟩ : syracuseStep 1880283 = 2820425) B2820425
theorem B3567863 : Blo 1879141 3567863 := bstep (se 1 (by rfl) ⟨2675897, by rfl⟩ : syracuseStep 3567863 = 5351795) B5351795
theorem B1880359 : Blo 1879141 1880359 := bstep (se 1 (by rfl) ⟨1410269, by rfl⟩ : syracuseStep 1880359 = 2820539) B2820539
theorem B1880399 : Blo 1879141 1880399 := bstep (se 1 (by rfl) ⟨1410299, by rfl⟩ : syracuseStep 1880399 = 2820599) B2820599
theorem B1880415 : Blo 1879141 1880415 := bstep (se 1 (by rfl) ⟨1410311, by rfl⟩ : syracuseStep 1880415 = 2820623) B2820623
theorem B4231529 : Blo 1879141 4231529 := bstep (se 2 (by rfl) ⟨1586823, by rfl⟩ : syracuseStep 4231529 = 3173647) B3173647
theorem B1880443 : Blo 1879141 1880443 := bstep (se 1 (by rfl) ⟨1410332, by rfl⟩ : syracuseStep 1880443 = 2820665) B2820665
theorem B9515393 : Blo 1879141 9515393 := bstep (se 2 (by rfl) ⟨3568272, by rfl⟩ : syracuseStep 9515393 = 7136545) B7136545
theorem B20328833 : Blo 1879141 20328833 := bstep (se 2 (by rfl) ⟨7623312, by rfl⟩ : syracuseStep 20328833 = 15246625) B15246625
theorem B1880495 : Blo 1879141 1880495 := bstep (se 1 (by rfl) ⟨1410371, by rfl⟩ : syracuseStep 1880495 = 2820743) B2820743
theorem B1880519 : Blo 1879141 1880519 := bstep (se 1 (by rfl) ⟨1410389, by rfl⟩ : syracuseStep 1880519 = 2820779) B2820779
theorem B6345161 : Blo 1879141 6345161 := bstep (se 2 (by rfl) ⟨2379435, by rfl⟩ : syracuseStep 6345161 = 4758871) B4758871
theorem B1880539 : Blo 1879141 1880539 := bstep (se 1 (by rfl) ⟨1410404, by rfl⟩ : syracuseStep 1880539 = 2820809) B2820809
theorem B6025691 : Blo 1879141 6025691 := bstep (se 1 (by rfl) ⟨4519268, by rfl⟩ : syracuseStep 6025691 = 9038537) B9038537
theorem B10711561 : Blo 1879141 10711561 := bstep (se 2 (by rfl) ⟨4016835, by rfl⟩ : syracuseStep 10711561 = 8033671) B8033671
theorem B24080921 : Blo 1879141 24080921 := bstep (se 2 (by rfl) ⟨9030345, by rfl⟩ : syracuseStep 24080921 = 18060691) B18060691
theorem B1880615 : Blo 1879141 1880615 := bstep (se 1 (by rfl) ⟨1410461, by rfl⟩ : syracuseStep 1880615 = 2820923) B2820923
theorem B1880655 : Blo 1879141 1880655 := bstep (se 1 (by rfl) ⟨1410491, by rfl⟩ : syracuseStep 1880655 = 2820983) B2820983
theorem B2380367 : Blo 1879141 2380367 := bstep (se 1 (by rfl) ⟨1785275, by rfl⟩ : syracuseStep 2380367 = 3570551) B3570551
theorem B1880671 : Blo 1879141 1880671 := bstep (se 1 (by rfl) ⟨1410503, by rfl⟩ : syracuseStep 1880671 = 2821007) B2821007
theorem B1880699 : Blo 1879141 1880699 := bstep (se 1 (by rfl) ⟨1410524, by rfl⟩ : syracuseStep 1880699 = 2821049) B2821049
theorem B1880751 : Blo 1879141 1880751 := bstep (se 1 (by rfl) ⟨1410563, by rfl⟩ : syracuseStep 1880751 = 2821127) B2821127
theorem B1880775 : Blo 1879141 1880775 := bstep (se 1 (by rfl) ⟨1410581, by rfl⟩ : syracuseStep 1880775 = 2821163) B2821163
theorem B6345431 : Blo 1879141 6345431 := bstep (se 1 (by rfl) ⟨4759073, by rfl⟩ : syracuseStep 6345431 = 9518147) B9518147
theorem B1880795 : Blo 1879141 1880795 := bstep (se 1 (by rfl) ⟨1410596, by rfl⟩ : syracuseStep 1880795 = 2821193) B2821193
theorem B1880871 : Blo 1879141 1880871 := bstep (se 1 (by rfl) ⟨1410653, by rfl⟩ : syracuseStep 1880871 = 2821307) B2821307
theorem B1880911 : Blo 1879141 1880911 := bstep (se 1 (by rfl) ⟨1410683, by rfl⟩ : syracuseStep 1880911 = 2821367) B2821367
theorem B3216223 : Blo 1879141 3216223 := bstep (se 1 (by rfl) ⟨2412167, by rfl⟩ : syracuseStep 3216223 = 4824335) B4824335
theorem B1880927 : Blo 1879141 1880927 := bstep (se 1 (by rfl) ⟨1410695, by rfl⟩ : syracuseStep 1880927 = 2821391) B2821391
theorem B1880955 : Blo 1879141 1880955 := bstep (se 1 (by rfl) ⟨1410716, by rfl⟩ : syracuseStep 1880955 = 2821433) B2821433
theorem B28930969 : Blo 1879141 28930969 := bstep (se 2 (by rfl) ⟨10849113, by rfl⟩ : syracuseStep 28930969 = 21698227) B21698227
theorem B13546415 : Blo 1879141 13546415 := bstep (se 1 (by rfl) ⟨10159811, by rfl⟩ : syracuseStep 13546415 = 20319623) B20319623
theorem B6345647 : Blo 1879141 6345647 := bstep (se 1 (by rfl) ⟨4759235, by rfl⟩ : syracuseStep 6345647 = 9518471) B9518471
theorem B1881007 : Blo 1879141 1881007 := bstep (se 1 (by rfl) ⟨1410755, by rfl⟩ : syracuseStep 1881007 = 2821511) B2821511
theorem B4232123 : Blo 1879141 4232123 := bstep (se 1 (by rfl) ⟨3174092, by rfl⟩ : syracuseStep 4232123 = 6348185) B6348185
theorem B1881031 : Blo 1879141 1881031 := bstep (se 1 (by rfl) ⟨1410773, by rfl⟩ : syracuseStep 1881031 = 2821547) B2821547
theorem B1881051 : Blo 1879141 1881051 := bstep (se 1 (by rfl) ⟨1410788, by rfl⟩ : syracuseStep 1881051 = 2821577) B2821577
theorem B32109533 : Blo 1879141 32109533 := bstep (se 3 (by rfl) ⟨6020537, by rfl⟩ : syracuseStep 32109533 = 12041075) B12041075
theorem B1881127 : Blo 1879141 1881127 := bstep (se 1 (by rfl) ⟨1410845, by rfl⟩ : syracuseStep 1881127 = 2821691) B2821691
theorem B4232249 : Blo 1879141 4232249 := bstep (se 2 (by rfl) ⟨1587093, by rfl⟩ : syracuseStep 4232249 = 3174187) B3174187
theorem B7140433 : Blo 1879141 7140433 := bstep (se 2 (by rfl) ⟨2677662, by rfl⟩ : syracuseStep 7140433 = 5355325) B5355325
theorem B9516203 : Blo 1879141 9516203 := bstep (se 1 (by rfl) ⟨7137152, by rfl⟩ : syracuseStep 9516203 = 14274305) B14274305
theorem B3011833 : Blo 1879141 3011833 := bstep (se 2 (by rfl) ⟨1129437, by rfl⟩ : syracuseStep 3011833 = 2258875) B2258875
theorem B7140737 : Blo 1879141 7140737 := bstep (se 2 (by rfl) ⟨2677776, by rfl⟩ : syracuseStep 7140737 = 5355553) B5355553
theorem B10704271 : Blo 1879141 10704271 := bstep (se 1 (by rfl) ⟨8028203, by rfl⟩ : syracuseStep 10704271 = 16056407) B16056407
theorem B12547493 : Blo 1879141 12547493 := bstep (se 4 (by rfl) ⟨1176327, by rfl⟩ : syracuseStep 12547493 = 2352655) B2352655
theorem B3388859 : Blo 1879141 3388859 := bstep (se 1 (by rfl) ⟨2541644, by rfl⟩ : syracuseStep 3388859 = 5083289) B5083289
theorem B4757089 : Blo 1879141 4757089 := bstep (se 2 (by rfl) ⟨1783908, by rfl⟩ : syracuseStep 4757089 = 3567817) B3567817
theorem B3569275 : Blo 1879141 3569275 := bstep (se 1 (by rfl) ⟨2676956, by rfl⟩ : syracuseStep 3569275 = 5353913) B5353913
theorem B9516689 : Blo 1879141 9516689 := bstep (se 2 (by rfl) ⟨3568758, by rfl⟩ : syracuseStep 9516689 = 7137517) B7137517
theorem B54195911 : Blo 1879141 54195911 := bstep (se 1 (by rfl) ⟨40646933, by rfl⟩ : syracuseStep 54195911 = 81293867) B81293867
theorem B4290259 : Blo 1879141 4290259 := bstep (se 1 (by rfl) ⟨3217694, by rfl⟩ : syracuseStep 4290259 = 6435389) B6435389
theorem B10852163 : Blo 1879141 10852163 := bstep (se 1 (by rfl) ⟨8139122, by rfl⟩ : syracuseStep 10852163 = 16278245) B16278245
theorem B7141193 : Blo 1879141 7141193 := bstep (se 2 (by rfl) ⟨2677947, by rfl⟩ : syracuseStep 7141193 = 5355895) B5355895
theorem B3569503 : Blo 1879141 3569503 := bstep (se 1 (by rfl) ⟨2677127, by rfl⟩ : syracuseStep 3569503 = 5354255) B5354255
theorem B5355371 : Blo 1879141 5355371 := bstep (se 1 (by rfl) ⟨4016528, by rfl⟩ : syracuseStep 5355371 = 8033057) B8033057
theorem B30496621 : Blo 1879141 30496621 := bstep (se 3 (by rfl) ⟨5718116, by rfl⟩ : syracuseStep 30496621 = 11436233) B11436233
theorem B2676655 : Blo 1879141 2676655 := bstep (se 1 (by rfl) ⟨2007491, by rfl⟩ : syracuseStep 2676655 = 4014983) B4014983
theorem B10713019 : Blo 1879141 10713019 := bstep (se 1 (by rfl) ⟨8034764, by rfl⟩ : syracuseStep 10713019 = 16069529) B16069529
theorem B7141391 : Blo 1879141 7141391 := bstep (se 1 (by rfl) ⟨5356043, by rfl⟩ : syracuseStep 7141391 = 10712087) B10712087
theorem B3569761 : Blo 1879141 3569761 := bstep (se 2 (by rfl) ⟨1338660, by rfl⟩ : syracuseStep 3569761 = 2677321) B2677321
theorem B3864673 : Blo 1879141 3864673 := bstep (se 2 (by rfl) ⟨1449252, by rfl⟩ : syracuseStep 3864673 = 2898505) B2898505
theorem B3570095 : Blo 1879141 3570095 := bstep (se 1 (by rfl) ⟨2677571, by rfl⟩ : syracuseStep 3570095 = 5355143) B5355143
theorem B2857399 : Blo 1879141 2857399 := bstep (se 1 (by rfl) ⟨2143049, by rfl⟩ : syracuseStep 2857399 = 4286099) B4286099
theorem B13548055 : Blo 1879141 13548055 := bstep (se 1 (by rfl) ⟨10161041, by rfl⟩ : syracuseStep 13548055 = 20322083) B20322083
theorem B4758041 : Blo 1879141 4758041 := bstep (se 2 (by rfl) ⟨1784265, by rfl⟩ : syracuseStep 4758041 = 3568531) B3568531
theorem B13556359 : Blo 1879141 13556359 := bstep (se 1 (by rfl) ⟨10167269, by rfl⟩ : syracuseStep 13556359 = 20334539) B20334539
theorem B16063379 : Blo 1879141 16063379 := bstep (se 1 (by rfl) ⟨12047534, by rfl⟩ : syracuseStep 16063379 = 24095069) B24095069
theorem B4758547 : Blo 1879141 4758547 := bstep (se 1 (by rfl) ⟨3568910, by rfl⟩ : syracuseStep 4758547 = 7137821) B7137821
theorem B5356601 : Blo 1879141 5356601 := bstep (se 2 (by rfl) ⟨2008725, by rfl⟩ : syracuseStep 5356601 = 4017451) B4017451
theorem B6102263 : Blo 1879141 6102263 := bstep (se 1 (by rfl) ⟨4576697, by rfl⟩ : syracuseStep 6102263 = 9153395) B9153395
theorem B6348023 : Blo 1879141 6348023 := bstep (se 1 (by rfl) ⟨4761017, by rfl⟩ : syracuseStep 6348023 = 9522035) B9522035
theorem B18062615 : Blo 1879141 18062615 := bstep (se 1 (by rfl) ⟨13546961, by rfl⟩ : syracuseStep 18062615 = 27093923) B27093923
theorem B21708121 : Blo 1879141 21708121 := bstep (se 2 (by rfl) ⟨8140545, by rfl⟩ : syracuseStep 21708121 = 16281091) B16281091
theorem B3571219 : Blo 1879141 3571219 := bstep (se 1 (by rfl) ⟨2678414, by rfl⟩ : syracuseStep 3571219 = 5356829) B5356829
theorem B6348347 : Blo 1879141 6348347 := bstep (se 1 (by rfl) ⟨4761260, by rfl⟩ : syracuseStep 6348347 = 9522521) B9522521
theorem B6020743 : Blo 1879141 6020743 := bstep (se 1 (by rfl) ⟨4515557, by rfl⟩ : syracuseStep 6020743 = 9031115) B9031115
theorem B7134905 : Blo 1879141 7134905 := bstep (se 2 (by rfl) ⟨2675589, by rfl⟩ : syracuseStep 7134905 = 5351179) B5351179
theorem B6348617 : Blo 1879141 6348617 := bstep (se 2 (by rfl) ⟨2380731, by rfl⟩ : syracuseStep 6348617 = 4761463) B4761463
theorem B9518957 : Blo 1879141 9518957 := bstep (se 3 (by rfl) ⟨1784804, by rfl⟩ : syracuseStep 9518957 = 3569609) B3569609
theorem B14270417 : Blo 1879141 14270417 := bstep (se 2 (by rfl) ⟨5351406, by rfl⟩ : syracuseStep 14270417 = 10702813) B10702813
theorem B4759681 : Blo 1879141 4759681 := bstep (se 2 (by rfl) ⟨1784880, by rfl⟩ : syracuseStep 4759681 = 3569761) B3569761
theorem B5152897 : Blo 1879141 5152897 := bstep (se 2 (by rfl) ⟨1932336, by rfl⟩ : syracuseStep 5152897 = 3864673) B3864673
theorem B6021449 : Blo 1879141 6021449 := bstep (se 2 (by rfl) ⟨2258043, by rfl⟩ : syracuseStep 6021449 = 4516087) B4516087
theorem B21406355 : Blo 1879141 21406355 := bstep (se 1 (by rfl) ⟨16054766, by rfl⟩ : syracuseStep 21406355 = 32109533) B32109533
theorem B18064073 : Blo 1879141 18064073 := bstep (se 2 (by rfl) ⟨6774027, by rfl⟩ : syracuseStep 18064073 = 13548055) B13548055
theorem B24429371 : Blo 1879141 24429371 := bstep (se 1 (by rfl) ⟨18322028, by rfl⟩ : syracuseStep 24429371 = 36644057) B36644057
theorem B2818895 : Blo 1879141 2818895 := bstep (se 1 (by rfl) ⟨2114171, by rfl⟩ : syracuseStep 2818895 = 4228343) B4228343
theorem B2114383 : Blo 1879141 2114383 := bstep (se 1 (by rfl) ⟨1585787, by rfl⟩ : syracuseStep 2114383 = 3171575) B3171575
theorem B4760491 : Blo 1879141 4760491 := bstep (se 1 (by rfl) ⟨3570368, by rfl⟩ : syracuseStep 4760491 = 7140737) B7140737
theorem B8364995 : Blo 1879141 8364995 := bstep (se 1 (by rfl) ⟨6273746, by rfl⟩ : syracuseStep 8364995 = 12547493) B12547493
theorem B9520091 : Blo 1879141 9520091 := bstep (se 1 (by rfl) ⟨7140068, by rfl⟩ : syracuseStep 9520091 = 14280137) B14280137
theorem B108413963 : Blo 1879141 108413963 := bstep (se 1 (by rfl) ⟨81310472, by rfl⟩ : syracuseStep 108413963 = 162620945) B162620945
theorem B102966389 : Blo 1879141 102966389 := bstep (se 5 (by rfl) ⟨4826549, by rfl⟩ : syracuseStep 102966389 = 9653099) B9653099
theorem B9520253 : Blo 1879141 9520253 := bstep (se 3 (by rfl) ⟨1785047, by rfl⟩ : syracuseStep 9520253 = 3570095) B3570095
theorem B7234775 : Blo 1879141 7234775 := bstep (se 1 (by rfl) ⟨5426081, by rfl⟩ : syracuseStep 7234775 = 10852163) B10852163
theorem B2819291 : Blo 1879141 2819291 := bstep (se 1 (by rfl) ⟨2114468, by rfl⟩ : syracuseStep 2819291 = 4228937) B4228937
theorem B2114779 : Blo 1879141 2114779 := bstep (se 1 (by rfl) ⟨1586084, by rfl⟩ : syracuseStep 2114779 = 3172169) B3172169
theorem B4760795 : Blo 1879141 4760795 := bstep (se 1 (by rfl) ⟨3570596, by rfl⟩ : syracuseStep 4760795 = 7141193) B7141193
theorem B2786591 : Blo 1879141 2786591 := bstep (se 1 (by rfl) ⟨2089943, by rfl⟩ : syracuseStep 2786591 = 4179887) B4179887
theorem B4760927 : Blo 1879141 4760927 := bstep (se 1 (by rfl) ⟨3570695, by rfl⟩ : syracuseStep 4760927 = 7141391) B7141391
theorem B2819465 : Blo 1879141 2819465 := bstep (se 2 (by rfl) ⟨1057299, by rfl⟩ : syracuseStep 2819465 = 2114599) B2114599
theorem B9520577 : Blo 1879141 9520577 := bstep (se 2 (by rfl) ⟨3570216, by rfl⟩ : syracuseStep 9520577 = 7140433) B7140433
theorem B2115067 : Blo 1879141 2115067 := bstep (se 1 (by rfl) ⟨1586300, by rfl⟩ : syracuseStep 2115067 = 3172601) B3172601
theorem B4228703 : Blo 1879141 4228703 := bstep (se 1 (by rfl) ⟨3171527, by rfl⟩ : syracuseStep 4228703 = 6343055) B6343055
theorem B37127803 : Blo 1879141 37127803 := bstep (se 1 (by rfl) ⟨27845852, by rfl⟩ : syracuseStep 37127803 = 55691705) B55691705
theorem B4015777 : Blo 1879141 4015777 := bstep (se 2 (by rfl) ⟨1505916, by rfl⟩ : syracuseStep 4015777 = 3011833) B3011833
theorem B2115247 : Blo 1879141 2115247 := bstep (se 1 (by rfl) ⟨1586435, by rfl⟩ : syracuseStep 2115247 = 3172871) B3172871
theorem B3172027 : Blo 1879141 3172027 := bstep (se 1 (by rfl) ⟨2379020, by rfl⟩ : syracuseStep 3172027 = 4758041) B4758041
theorem B2819819 : Blo 1879141 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B28944161 : Blo 1879141 28944161 := bstep (se 2 (by rfl) ⟨10854060, by rfl⟩ : syracuseStep 28944161 = 21708121) B21708121
theorem B4228919 : Blo 1879141 4228919 := bstep (se 1 (by rfl) ⟨3171689, by rfl⟩ : syracuseStep 4228919 = 6343379) B6343379
theorem B14272361 : Blo 1879141 14272361 := bstep (se 2 (by rfl) ⟨5352135, by rfl⟩ : syracuseStep 14272361 = 10704271) B10704271
theorem B10708919 : Blo 1879141 10708919 := bstep (se 1 (by rfl) ⟨8031689, by rfl⟩ : syracuseStep 10708919 = 16063379) B16063379
theorem B2820047 : Blo 1879141 2820047 := bstep (se 1 (by rfl) ⟨2115035, by rfl⟩ : syracuseStep 2820047 = 4230071) B4230071
theorem B2115535 : Blo 1879141 2115535 := bstep (se 1 (by rfl) ⟨1586651, by rfl⟩ : syracuseStep 2115535 = 3173303) B3173303
theorem B4761625 : Blo 1879141 4761625 := bstep (se 2 (by rfl) ⟨1785609, by rfl⟩ : syracuseStep 4761625 = 3571219) B3571219
theorem B4229225 : Blo 1879141 4229225 := bstep (se 2 (by rfl) ⟨1585959, by rfl⟩ : syracuseStep 4229225 = 3171919) B3171919
theorem B6342785 : Blo 1879141 6342785 := bstep (se 2 (by rfl) ⟨2378544, by rfl⟩ : syracuseStep 6342785 = 4757089) B4757089
theorem B5720345 : Blo 1879141 5720345 := bstep (se 2 (by rfl) ⟨2145129, by rfl⟩ : syracuseStep 5720345 = 4290259) B4290259
theorem B15239461 : Blo 1879141 15239461 := bstep (se 4 (by rfl) ⟨1428699, by rfl⟩ : syracuseStep 15239461 = 2857399) B2857399
theorem B2820443 : Blo 1879141 2820443 := bstep (se 1 (by rfl) ⟨2115332, by rfl⟩ : syracuseStep 2820443 = 4230665) B4230665
theorem B2115931 : Blo 1879141 2115931 := bstep (se 1 (by rfl) ⟨1586948, by rfl⟩ : syracuseStep 2115931 = 3173897) B3173897
theorem B2116039 : Blo 1879141 2116039 := bstep (se 1 (by rfl) ⟨1587029, by rfl⟩ : syracuseStep 2116039 = 3174059) B3174059
theorem B6343163 : Blo 1879141 6343163 := bstep (se 1 (by rfl) ⟨4757372, by rfl⟩ : syracuseStep 6343163 = 9514745) B9514745
theorem B4344383 : Blo 1879141 4344383 := bstep (se 1 (by rfl) ⟨3258287, by rfl⟩ : syracuseStep 4344383 = 6516575) B6516575
theorem B2820671 : Blo 1879141 2820671 := bstep (se 1 (by rfl) ⟨2115503, by rfl⟩ : syracuseStep 2820671 = 4231007) B4231007
theorem B4229711 : Blo 1879141 4229711 := bstep (se 1 (by rfl) ⟨3172283, by rfl⟩ : syracuseStep 4229711 = 6344567) B6344567
theorem B9513611 : Blo 1879141 9513611 := bstep (se 1 (by rfl) ⟨7135208, by rfl⟩ : syracuseStep 9513611 = 14270417) B14270417
theorem B27118253 : Blo 1879141 27118253 := bstep (se 3 (by rfl) ⟨5084672, by rfl⟩ : syracuseStep 27118253 = 10169345) B10169345
theorem B2378423 : Blo 1879141 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B2820791 : Blo 1879141 2820791 := bstep (se 1 (by rfl) ⟨2115593, by rfl⟩ : syracuseStep 2820791 = 4231187) B4231187
theorem B4229855 : Blo 1879141 4229855 := bstep (se 1 (by rfl) ⟨3172391, by rfl⟩ : syracuseStep 4229855 = 6344783) B6344783
theorem B3173087 : Blo 1879141 3173087 := bstep (se 1 (by rfl) ⟨2379815, by rfl⟩ : syracuseStep 3173087 = 4759631) B4759631
theorem B2378575 : Blo 1879141 2378575 := bstep (se 1 (by rfl) ⟨1783931, by rfl⟩ : syracuseStep 2378575 = 3567863) B3567863
theorem B2821019 : Blo 1879141 2821019 := bstep (se 1 (by rfl) ⟨2115764, by rfl⟩ : syracuseStep 2821019 = 4231529) B4231529
theorem B6343595 : Blo 1879141 6343595 := bstep (se 1 (by rfl) ⟨4757696, by rfl⟩ : syracuseStep 6343595 = 9515393) B9515393
theorem B13552555 : Blo 1879141 13552555 := bstep (se 1 (by rfl) ⟨10164416, by rfl⟩ : syracuseStep 13552555 = 20328833) B20328833
theorem B4230107 : Blo 1879141 4230107 := bstep (se 1 (by rfl) ⟨3172580, by rfl⟩ : syracuseStep 4230107 = 6345161) B6345161
theorem B4017127 : Blo 1879141 4017127 := bstep (se 1 (by rfl) ⟨3012845, by rfl⟩ : syracuseStep 4017127 = 6025691) B6025691
theorem B6024331 : Blo 1879141 6024331 := bstep (se 1 (by rfl) ⟨4518248, by rfl⟩ : syracuseStep 6024331 = 9036497) B9036497
theorem B4230287 : Blo 1879141 4230287 := bstep (se 1 (by rfl) ⟨3172715, by rfl⟩ : syracuseStep 4230287 = 6345431) B6345431
theorem B3173519 : Blo 1879141 3173519 := bstep (se 1 (by rfl) ⟨2380139, by rfl⟩ : syracuseStep 3173519 = 4760279) B4760279
theorem B16280747 : Blo 1879141 16280747 := bstep (se 1 (by rfl) ⟨12210560, by rfl⟩ : syracuseStep 16280747 = 24421121) B24421121
theorem B5352637 : Blo 1879141 5352637 := bstep (se 3 (by rfl) ⟨1003619, by rfl⟩ : syracuseStep 5352637 = 2007239) B2007239
theorem B4230377 : Blo 1879141 4230377 := bstep (se 2 (by rfl) ⟨1586391, by rfl⟩ : syracuseStep 4230377 = 3172783) B3172783
theorem B9030943 : Blo 1879141 9030943 := bstep (se 1 (by rfl) ⟨6773207, by rfl⟩ : syracuseStep 9030943 = 13546415) B13546415
theorem B1879327 : Blo 1879141 1879327 := bstep (se 1 (by rfl) ⟨1409495, by rfl⟩ : syracuseStep 1879327 = 2818991) B2818991
theorem B4230431 : Blo 1879141 4230431 := bstep (se 1 (by rfl) ⟨3172823, by rfl⟩ : syracuseStep 4230431 = 6345647) B6345647
theorem B2821415 : Blo 1879141 2821415 := bstep (se 1 (by rfl) ⟨2116061, by rfl⟩ : syracuseStep 2821415 = 4232123) B4232123
theorem B16272701 : Blo 1879141 16272701 := bstep (se 3 (by rfl) ⟨3051131, by rfl⟩ : syracuseStep 16272701 = 6102263) B6102263
theorem B1879387 : Blo 1879141 1879387 := bstep (se 1 (by rfl) ⟨1409540, by rfl⟩ : syracuseStep 1879387 = 2819081) B2819081
theorem B14282081 : Blo 1879141 14282081 := bstep (se 2 (by rfl) ⟨5355780, by rfl⟩ : syracuseStep 14282081 = 10711561) B10711561
theorem B1879407 : Blo 1879141 1879407 := bstep (se 1 (by rfl) ⟨1409555, by rfl⟩ : syracuseStep 1879407 = 2819111) B2819111
theorem B3173755 : Blo 1879141 3173755 := bstep (se 1 (by rfl) ⟨2380316, by rfl⟩ : syracuseStep 3173755 = 4760633) B4760633
theorem B2821499 : Blo 1879141 2821499 := bstep (se 1 (by rfl) ⟨2116124, by rfl⟩ : syracuseStep 2821499 = 4232249) B4232249
theorem B11152769 : Blo 1879141 11152769 := bstep (se 2 (by rfl) ⟨4182288, by rfl⟩ : syracuseStep 11152769 = 8364577) B8364577
theorem B1879463 : Blo 1879141 1879463 := bstep (se 1 (by rfl) ⟨1409597, by rfl⟩ : syracuseStep 1879463 = 2819195) B2819195
theorem B30502331 : Blo 1879141 30502331 := bstep (se 1 (by rfl) ⟨22876748, by rfl⟩ : syracuseStep 30502331 = 45753497) B45753497
theorem B6344135 : Blo 1879141 6344135 := bstep (se 1 (by rfl) ⟨4758101, by rfl⟩ : syracuseStep 6344135 = 9516203) B9516203
theorem B2821625 : Blo 1879141 2821625 := bstep (se 2 (by rfl) ⟨1058109, by rfl⟩ : syracuseStep 2821625 = 2116219) B2116219
theorem B1879547 : Blo 1879141 1879547 := bstep (se 1 (by rfl) ⟨1409660, by rfl⟩ : syracuseStep 1879547 = 2819321) B2819321
theorem B18075145 : Blo 1879141 18075145 := bstep (se 2 (by rfl) ⟨6778179, by rfl⟩ : syracuseStep 18075145 = 13556359) B13556359
theorem B1879615 : Blo 1879141 1879615 := bstep (se 1 (by rfl) ⟨1409711, by rfl⟩ : syracuseStep 1879615 = 2819423) B2819423
theorem B1879623 : Blo 1879141 1879623 := bstep (se 1 (by rfl) ⟨1409717, by rfl⟩ : syracuseStep 1879623 = 2819435) B2819435
theorem B4517471 : Blo 1879141 4517471 := bstep (se 1 (by rfl) ⟨3388103, by rfl⟩ : syracuseStep 4517471 = 6776207) B6776207
theorem B1879775 : Blo 1879141 1879775 := bstep (se 1 (by rfl) ⟨1409831, by rfl⟩ : syracuseStep 1879775 = 2819663) B2819663
theorem B6344459 : Blo 1879141 6344459 := bstep (se 1 (by rfl) ⟨4758344, by rfl⟩ : syracuseStep 6344459 = 9516689) B9516689
theorem B4288297 : Blo 1879141 4288297 := bstep (se 2 (by rfl) ⟨1608111, by rfl⟩ : syracuseStep 4288297 = 3216223) B3216223
theorem B4230953 : Blo 1879141 4230953 := bstep (se 2 (by rfl) ⟨1586607, by rfl⟩ : syracuseStep 4230953 = 3173215) B3173215
theorem B36130607 : Blo 1879141 36130607 := bstep (se 1 (by rfl) ⟨27097955, by rfl⟩ : syracuseStep 36130607 = 54195911) B54195911
theorem B1879855 : Blo 1879141 1879855 := bstep (se 1 (by rfl) ⟨1409891, by rfl⟩ : syracuseStep 1879855 = 2819783) B2819783
theorem B1879963 : Blo 1879141 1879963 := bstep (se 1 (by rfl) ⟨1409972, by rfl⟩ : syracuseStep 1879963 = 2819945) B2819945
theorem B1880015 : Blo 1879141 1880015 := bstep (se 1 (by rfl) ⟨1410011, by rfl⟩ : syracuseStep 1880015 = 2820023) B2820023
theorem B1880039 : Blo 1879141 1880039 := bstep (se 1 (by rfl) ⟨1410029, by rfl⟩ : syracuseStep 1880039 = 2820059) B2820059
theorem B6344729 : Blo 1879141 6344729 := bstep (se 2 (by rfl) ⟨2379273, by rfl⟩ : syracuseStep 6344729 = 4758547) B4758547
theorem B7942315 : Blo 1879141 7942315 := bstep (se 1 (by rfl) ⟨5956736, by rfl⟩ : syracuseStep 7942315 = 11913473) B11913473
theorem B16068779 : Blo 1879141 16068779 := bstep (se 1 (by rfl) ⟨12051584, by rfl⟩ : syracuseStep 16068779 = 24103169) B24103169
theorem B1880351 : Blo 1879141 1880351 := bstep (se 1 (by rfl) ⟨1410263, by rfl⟩ : syracuseStep 1880351 = 2820527) B2820527
theorem B1880411 : Blo 1879141 1880411 := bstep (se 1 (by rfl) ⟨1410308, by rfl⟩ : syracuseStep 1880411 = 2820617) B2820617
theorem B3305819 : Blo 1879141 3305819 := bstep (se 1 (by rfl) ⟨2479364, by rfl⟩ : syracuseStep 3305819 = 4958729) B4958729
theorem B1880431 : Blo 1879141 1880431 := bstep (se 1 (by rfl) ⟨1410323, by rfl⟩ : syracuseStep 1880431 = 2820647) B2820647
theorem B1880487 : Blo 1879141 1880487 := bstep (se 1 (by rfl) ⟨1410365, by rfl⟩ : syracuseStep 1880487 = 2820731) B2820731
theorem B1880571 : Blo 1879141 1880571 := bstep (se 1 (by rfl) ⟨1410428, by rfl⟩ : syracuseStep 1880571 = 2820857) B2820857
theorem B1880639 : Blo 1879141 1880639 := bstep (se 1 (by rfl) ⟨1410479, by rfl⟩ : syracuseStep 1880639 = 2820959) B2820959
theorem B1880647 : Blo 1879141 1880647 := bstep (se 1 (by rfl) ⟨1410485, by rfl⟩ : syracuseStep 1880647 = 2820971) B2820971
theorem B36147829 : Blo 1879141 36147829 := bstep (se 5 (by rfl) ⟨1694429, by rfl⟩ : syracuseStep 36147829 = 3388859) B3388859
theorem B3568303 : Blo 1879141 3568303 := bstep (se 1 (by rfl) ⟨2676227, by rfl⟩ : syracuseStep 3568303 = 5352455) B5352455
theorem B1880799 : Blo 1879141 1880799 := bstep (se 1 (by rfl) ⟨1410599, by rfl⟩ : syracuseStep 1880799 = 2821199) B2821199
theorem B1880879 : Blo 1879141 1880879 := bstep (se 1 (by rfl) ⟨1410659, by rfl⟩ : syracuseStep 1880879 = 2821319) B2821319
theorem B4232015 : Blo 1879141 4232015 := bstep (se 1 (by rfl) ⟨3174011, by rfl⟩ : syracuseStep 4232015 = 6348023) B6348023
theorem B1880987 : Blo 1879141 1880987 := bstep (se 1 (by rfl) ⟨1410740, by rfl⟩ : syracuseStep 1880987 = 2821481) B2821481
theorem B1881039 : Blo 1879141 1881039 := bstep (se 1 (by rfl) ⟨1410779, by rfl⟩ : syracuseStep 1881039 = 2821559) B2821559
theorem B1881063 : Blo 1879141 1881063 := bstep (se 1 (by rfl) ⟨1410797, by rfl⟩ : syracuseStep 1881063 = 2821595) B2821595
theorem B4232231 : Blo 1879141 4232231 := bstep (se 1 (by rfl) ⟨3174173, by rfl⟩ : syracuseStep 4232231 = 6348347) B6348347
theorem B4756603 : Blo 1879141 4756603 := bstep (se 1 (by rfl) ⟨3567452, by rfl⟩ : syracuseStep 4756603 = 7134905) B7134905
theorem B40662161 : Blo 1879141 40662161 := bstep (se 2 (by rfl) ⟨15248310, by rfl⟩ : syracuseStep 40662161 = 30496621) B30496621
theorem B5354711 : Blo 1879141 5354711 := bstep (se 1 (by rfl) ⟨4016033, by rfl⟩ : syracuseStep 5354711 = 8032067) B8032067
theorem B4232411 : Blo 1879141 4232411 := bstep (se 1 (by rfl) ⟨3174308, by rfl⟩ : syracuseStep 4232411 = 6348617) B6348617
theorem B3568873 : Blo 1879141 3568873 := bstep (se 2 (by rfl) ⟨1338327, by rfl⟩ : syracuseStep 3568873 = 2676655) B2676655
theorem B6345971 : Blo 1879141 6345971 := bstep (se 1 (by rfl) ⟨4759478, by rfl⟩ : syracuseStep 6345971 = 9518957) B9518957
theorem B9647353 : Blo 1879141 9647353 := bstep (se 2 (by rfl) ⟨3617757, by rfl⟩ : syracuseStep 9647353 = 7235515) B7235515
theorem B14284025 : Blo 1879141 14284025 := bstep (se 2 (by rfl) ⟨5356509, by rfl⟩ : syracuseStep 14284025 = 10713019) B10713019
theorem B6346079 : Blo 1879141 6346079 := bstep (se 1 (by rfl) ⟨4759559, by rfl⟩ : syracuseStep 6346079 = 9519119) B9519119
theorem B2676091 : Blo 1879141 2676091 := bstep (se 1 (by rfl) ⟨2007068, by rfl⟩ : syracuseStep 2676091 = 4014137) B4014137
theorem B8574331 : Blo 1879141 8574331 := bstep (se 1 (by rfl) ⟨6430748, by rfl⟩ : syracuseStep 8574331 = 12861497) B12861497
theorem B4822487 : Blo 1879141 4822487 := bstep (se 1 (by rfl) ⟨3616865, by rfl⟩ : syracuseStep 4822487 = 7233731) B7233731
theorem B16053947 : Blo 1879141 16053947 := bstep (se 1 (by rfl) ⟨12040460, by rfl⟩ : syracuseStep 16053947 = 24080921) B24080921
theorem B11433757 : Blo 1879141 11433757 := bstep (se 3 (by rfl) ⟨2143829, by rfl⟩ : syracuseStep 11433757 = 4287659) B4287659
theorem B3217207 : Blo 1879141 3217207 := bstep (se 1 (by rfl) ⟨2412905, by rfl⟩ : syracuseStep 3217207 = 4825811) B4825811
theorem B15243511 : Blo 1879141 15243511 := bstep (se 1 (by rfl) ⟨11432633, by rfl⟩ : syracuseStep 15243511 = 22865267) B22865267
theorem B9517337 : Blo 1879141 9517337 := bstep (se 2 (by rfl) ⟨3569001, by rfl⟩ : syracuseStep 9517337 = 7138003) B7138003
theorem B6773021 : Blo 1879141 6773021 := bstep (se 3 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 6773021 = 2539883) B2539883
theorem B4758011 : Blo 1879141 4758011 := bstep (se 1 (by rfl) ⟨3568508, by rfl⟩ : syracuseStep 4758011 = 7137017) B7137017
theorem B38574625 : Blo 1879141 38574625 := bstep (se 2 (by rfl) ⟨14465484, by rfl⟩ : syracuseStep 38574625 = 28930969) B28930969
theorem B3570247 : Blo 1879141 3570247 := bstep (se 1 (by rfl) ⟨2677685, by rfl⟩ : syracuseStep 3570247 = 5355371) B5355371
theorem B10705547 : Blo 1879141 10705547 := bstep (se 1 (by rfl) ⟨8029160, by rfl⟩ : syracuseStep 10705547 = 16058321) B16058321
theorem B36133613 : Blo 1879141 36133613 := bstep (se 3 (by rfl) ⟨6775052, by rfl⟩ : syracuseStep 36133613 = 13550105) B13550105
theorem B2677583 : Blo 1879141 2677583 := bstep (se 1 (by rfl) ⟨2008187, by rfl⟩ : syracuseStep 2677583 = 4016375) B4016375
theorem B6347645 : Blo 1879141 6347645 := bstep (se 3 (by rfl) ⟨1190183, by rfl⟩ : syracuseStep 6347645 = 2380367) B2380367
theorem B6020219 : Blo 1879141 6020219 := bstep (se 1 (by rfl) ⟨4515164, by rfl⟩ : syracuseStep 6020219 = 9030329) B9030329
theorem B6347915 : Blo 1879141 6347915 := bstep (se 1 (by rfl) ⟨4760936, by rfl⟩ : syracuseStep 6347915 = 9521873) B9521873
theorem B3571067 : Blo 1879141 3571067 := bstep (se 1 (by rfl) ⟨2678300, by rfl⟩ : syracuseStep 3571067 = 5356601) B5356601
theorem B4758983 : Blo 1879141 4758983 := bstep (se 1 (by rfl) ⟨3569237, by rfl⟩ : syracuseStep 4758983 = 7138475) B7138475
theorem B17382857 : Blo 1879141 17382857 := bstep (se 2 (by rfl) ⟨6518571, by rfl⟩ : syracuseStep 17382857 = 13037143) B13037143
theorem B4759033 : Blo 1879141 4759033 := bstep (se 2 (by rfl) ⟨1784637, by rfl⟩ : syracuseStep 4759033 = 3569275) B3569275
theorem B8027657 : Blo 1879141 8027657 := bstep (se 2 (by rfl) ⟨3010371, by rfl⟩ : syracuseStep 8027657 = 6020743) B6020743
theorem B12041743 : Blo 1879141 12041743 := bstep (se 1 (by rfl) ⟨9031307, by rfl⟩ : syracuseStep 12041743 = 18062615) B18062615
theorem B15457807 : Blo 1879141 15457807 := bstep (se 1 (by rfl) ⟨11593355, by rfl⟩ : syracuseStep 15457807 = 23186711) B23186711
theorem B4759337 : Blo 1879141 4759337 := bstep (se 2 (by rfl) ⟨1784751, by rfl⟩ : syracuseStep 4759337 = 3569503) B3569503
theorem B6348833 : Blo 1879141 6348833 := bstep (se 2 (by rfl) ⟨2380812, by rfl⟩ : syracuseStep 6348833 = 4761625) B4761625
theorem B4014299 : Blo 1879141 4014299 := bstep (se 1 (by rfl) ⟨3010724, by rfl⟩ : syracuseStep 4014299 = 6021449) B6021449
theorem B20324681 : Blo 1879141 20324681 := bstep (se 2 (by rfl) ⟨7621755, by rfl⟩ : syracuseStep 20324681 = 15243511) B15243511
theorem B14270903 : Blo 1879141 14270903 := bstep (se 1 (by rfl) ⟨10703177, by rfl⟩ : syracuseStep 14270903 = 21406355) B21406355
theorem B7430909 : Blo 1879141 7430909 := bstep (se 3 (by rfl) ⟨1393295, by rfl⟩ : syracuseStep 7430909 = 2786591) B2786591
theorem B4760329 : Blo 1879141 4760329 := bstep (se 2 (by rfl) ⟨1785123, by rfl⟩ : syracuseStep 4760329 = 3570247) B3570247
theorem B27108107 : Blo 1879141 27108107 := bstep (se 1 (by rfl) ⟨20331080, by rfl⟩ : syracuseStep 27108107 = 40662161) B40662161
theorem B8815517 : Blo 1879141 8815517 := bstep (se 3 (by rfl) ⟨1652909, by rfl⟩ : syracuseStep 8815517 = 3305819) B3305819
theorem B2819135 : Blo 1879141 2819135 := bstep (se 1 (by rfl) ⟨2114351, by rfl⟩ : syracuseStep 2819135 = 4228703) B4228703
theorem B3171433 : Blo 1879141 3171433 := bstep (se 2 (by rfl) ⟨1189287, by rfl⟩ : syracuseStep 3171433 = 2378575) B2378575
theorem B2819177 : Blo 1879141 2819177 := bstep (se 2 (by rfl) ⟨1057191, by rfl⟩ : syracuseStep 2819177 = 2114383) B2114383
theorem B2819279 : Blo 1879141 2819279 := bstep (se 1 (by rfl) ⟨2114459, by rfl⟩ : syracuseStep 2819279 = 4228919) B4228919
theorem B2819483 : Blo 1879141 2819483 := bstep (se 1 (by rfl) ⟨2114612, by rfl⟩ : syracuseStep 2819483 = 4229225) B4229225
theorem B4228523 : Blo 1879141 4228523 := bstep (se 1 (by rfl) ⟨3171392, by rfl⟩ : syracuseStep 4228523 = 6342785) B6342785
theorem B6342137 : Blo 1879141 6342137 := bstep (se 2 (by rfl) ⟨2378301, by rfl⟩ : syracuseStep 6342137 = 4756603) B4756603
theorem B4515347 : Blo 1879141 4515347 := bstep (se 1 (by rfl) ⟨3386510, by rfl⟩ : syracuseStep 4515347 = 6773021) B6773021
theorem B7136849 : Blo 1879141 7136849 := bstep (se 2 (by rfl) ⟨2676318, by rfl⟩ : syracuseStep 7136849 = 5352637) B5352637
theorem B2819705 : Blo 1879141 2819705 := bstep (se 2 (by rfl) ⟨1057389, by rfl⟩ : syracuseStep 2819705 = 2114779) B2114779
theorem B12863137 : Blo 1879141 12863137 := bstep (se 2 (by rfl) ⟨4823676, by rfl⟩ : syracuseStep 12863137 = 9647353) B9647353
theorem B4228775 : Blo 1879141 4228775 := bstep (se 1 (by rfl) ⟨3171581, by rfl⟩ : syracuseStep 4228775 = 6343163) B6343163
theorem B3172007 : Blo 1879141 3172007 := bstep (se 1 (by rfl) ⟨2379005, by rfl⟩ : syracuseStep 3172007 = 4758011) B4758011
theorem B2819807 : Blo 1879141 2819807 := bstep (se 1 (by rfl) ⟨2114855, by rfl⟩ : syracuseStep 2819807 = 4229711) B4229711
theorem B6342407 : Blo 1879141 6342407 := bstep (se 1 (by rfl) ⟨4756805, by rfl⟩ : syracuseStep 6342407 = 9513611) B9513611
theorem B7137031 : Blo 1879141 7137031 := bstep (se 1 (by rfl) ⟨5352773, by rfl⟩ : syracuseStep 7137031 = 10705547) B10705547
theorem B6342461 : Blo 1879141 6342461 := bstep (se 3 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 6342461 = 2378423) B2378423
theorem B2819903 : Blo 1879141 2819903 := bstep (se 1 (by rfl) ⟨2114927, by rfl⟩ : syracuseStep 2819903 = 4229855) B4229855
theorem B2115391 : Blo 1879141 2115391 := bstep (se 1 (by rfl) ⟨1586543, by rfl⟩ : syracuseStep 2115391 = 3173087) B3173087
theorem B48170861 : Blo 1879141 48170861 := bstep (se 3 (by rfl) ⟨9032036, by rfl⟩ : syracuseStep 48170861 = 18064073) B18064073
theorem B4229063 : Blo 1879141 4229063 := bstep (se 1 (by rfl) ⟨3171797, by rfl⟩ : syracuseStep 4229063 = 6343595) B6343595
theorem B2820071 : Blo 1879141 2820071 := bstep (se 1 (by rfl) ⟨2115053, by rfl⟩ : syracuseStep 2820071 = 4230107) B4230107
theorem B2820089 : Blo 1879141 2820089 := bstep (se 2 (by rfl) ⟨1057533, by rfl⟩ : syracuseStep 2820089 = 2115067) B2115067
theorem B2820191 : Blo 1879141 2820191 := bstep (se 1 (by rfl) ⟨2115143, by rfl⟩ : syracuseStep 2820191 = 4230287) B4230287
theorem B2115679 : Blo 1879141 2115679 := bstep (se 1 (by rfl) ⟨1586759, by rfl⟩ : syracuseStep 2115679 = 3173519) B3173519
theorem B2820251 : Blo 1879141 2820251 := bstep (se 1 (by rfl) ⟨2115188, by rfl⟩ : syracuseStep 2820251 = 4230377) B4230377
theorem B65144989 : Blo 1879141 65144989 := bstep (se 3 (by rfl) ⟨12214685, by rfl⟩ : syracuseStep 65144989 = 24429371) B24429371
theorem B2820287 : Blo 1879141 2820287 := bstep (se 1 (by rfl) ⟨2115215, by rfl⟩ : syracuseStep 2820287 = 4230431) B4230431
theorem B10848467 : Blo 1879141 10848467 := bstep (se 1 (by rfl) ⟨8136350, by rfl⟩ : syracuseStep 10848467 = 16272701) B16272701
theorem B2820329 : Blo 1879141 2820329 := bstep (se 2 (by rfl) ⟨1057623, by rfl⟩ : syracuseStep 2820329 = 2115247) B2115247
theorem B9521387 : Blo 1879141 9521387 := bstep (se 1 (by rfl) ⟨7141040, by rfl⟩ : syracuseStep 9521387 = 14282081) B14282081
theorem B4229369 : Blo 1879141 4229369 := bstep (se 2 (by rfl) ⟨1586013, by rfl⟩ : syracuseStep 4229369 = 3172027) B3172027
theorem B20334887 : Blo 1879141 20334887 := bstep (se 1 (by rfl) ⟨15251165, by rfl⟩ : syracuseStep 20334887 = 30502331) B30502331
theorem B4229423 : Blo 1879141 4229423 := bstep (se 1 (by rfl) ⟨3172067, by rfl⟩ : syracuseStep 4229423 = 6344135) B6344135
theorem B3172655 : Blo 1879141 3172655 := bstep (se 1 (by rfl) ⟨2379491, by rfl⟩ : syracuseStep 3172655 = 4758983) B4758983
theorem B5351771 : Blo 1879141 5351771 := bstep (se 1 (by rfl) ⟨4013828, by rfl⟩ : syracuseStep 5351771 = 8027657) B8027657
theorem B4229639 : Blo 1879141 4229639 := bstep (se 1 (by rfl) ⟨3172229, by rfl⟩ : syracuseStep 4229639 = 6344459) B6344459
theorem B3172891 : Blo 1879141 3172891 := bstep (se 1 (by rfl) ⟨2379668, by rfl⟩ : syracuseStep 3172891 = 4759337) B4759337
theorem B2820635 : Blo 1879141 2820635 := bstep (se 1 (by rfl) ⟨2115476, by rfl⟩ : syracuseStep 2820635 = 4230953) B4230953
theorem B24087071 : Blo 1879141 24087071 := bstep (se 1 (by rfl) ⟨18065303, by rfl⟩ : syracuseStep 24087071 = 36130607) B36130607
theorem B2820713 : Blo 1879141 2820713 := bstep (se 2 (by rfl) ⟨1057767, by rfl⟩ : syracuseStep 2820713 = 2115535) B2115535
theorem B4229819 : Blo 1879141 4229819 := bstep (se 1 (by rfl) ⟨3172364, by rfl⟩ : syracuseStep 4229819 = 6344729) B6344729
theorem B20319281 : Blo 1879141 20319281 := bstep (se 2 (by rfl) ⟨7619730, by rfl⟩ : syracuseStep 20319281 = 15239461) B15239461
theorem B2821241 : Blo 1879141 2821241 := bstep (se 2 (by rfl) ⟨1057965, by rfl⟩ : syracuseStep 2821241 = 2115931) B2115931
theorem B1879263 : Blo 1879141 1879263 := bstep (se 1 (by rfl) ⟨1409447, by rfl⟩ : syracuseStep 1879263 = 2818895) B2818895
theorem B2821343 : Blo 1879141 2821343 := bstep (se 1 (by rfl) ⟨2116007, by rfl⟩ : syracuseStep 2821343 = 4232015) B4232015
theorem B2821385 : Blo 1879141 2821385 := bstep (se 2 (by rfl) ⟨1058019, by rfl⟩ : syracuseStep 2821385 = 2116039) B2116039
theorem B2821487 : Blo 1879141 2821487 := bstep (se 1 (by rfl) ⟨2116115, by rfl⟩ : syracuseStep 2821487 = 4232231) B4232231
theorem B51432833 : Blo 1879141 51432833 := bstep (se 2 (by rfl) ⟨19287312, by rfl⟩ : syracuseStep 51432833 = 38574625) B38574625
theorem B68644259 : Blo 1879141 68644259 := bstep (se 1 (by rfl) ⟨51483194, by rfl⟩ : syracuseStep 68644259 = 102966389) B102966389
theorem B1879527 : Blo 1879141 1879527 := bstep (se 1 (by rfl) ⟨1409645, by rfl⟩ : syracuseStep 1879527 = 2819291) B2819291
theorem B3173863 : Blo 1879141 3173863 := bstep (se 1 (by rfl) ⟨2380397, by rfl⟩ : syracuseStep 3173863 = 4760795) B4760795
theorem B2821607 : Blo 1879141 2821607 := bstep (se 1 (by rfl) ⟨2116205, by rfl⟩ : syracuseStep 2821607 = 4232411) B4232411
theorem B48197105 : Blo 1879141 48197105 := bstep (se 2 (by rfl) ⟨18073914, by rfl⟩ : syracuseStep 48197105 = 36147829) B36147829
theorem B4230647 : Blo 1879141 4230647 := bstep (se 1 (by rfl) ⟨3172985, by rfl⟩ : syracuseStep 4230647 = 6345971) B6345971
theorem B9522683 : Blo 1879141 9522683 := bstep (se 1 (by rfl) ⟨7142012, by rfl⟩ : syracuseStep 9522683 = 14284025) B14284025
theorem B4230719 : Blo 1879141 4230719 := bstep (se 1 (by rfl) ⟨3173039, by rfl⟩ : syracuseStep 4230719 = 6346079) B6346079
theorem B3173951 : Blo 1879141 3173951 := bstep (se 1 (by rfl) ⟨2380463, by rfl⟩ : syracuseStep 3173951 = 4760927) B4760927
theorem B1879643 : Blo 1879141 1879643 := bstep (se 1 (by rfl) ⟨1409732, by rfl⟩ : syracuseStep 1879643 = 2819465) B2819465
theorem B3214991 : Blo 1879141 3214991 := bstep (se 1 (by rfl) ⟨2411243, by rfl⟩ : syracuseStep 3214991 = 4822487) B4822487
theorem B9522845 : Blo 1879141 9522845 := bstep (se 3 (by rfl) ⟨1785533, by rfl⟩ : syracuseStep 9522845 = 3571067) B3571067
theorem B29740717 : Blo 1879141 29740717 := bstep (se 3 (by rfl) ⟨5576384, by rfl⟩ : syracuseStep 29740717 = 11152769) B11152769
theorem B10702631 : Blo 1879141 10702631 := bstep (se 1 (by rfl) ⟨8026973, by rfl⟩ : syracuseStep 10702631 = 16053947) B16053947
theorem B1879879 : Blo 1879141 1879879 := bstep (se 1 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 1879879 = 2819819) B2819819
theorem B19296107 : Blo 1879141 19296107 := bstep (se 1 (by rfl) ⟨14472080, by rfl⟩ : syracuseStep 19296107 = 28944161) B28944161
theorem B46354285 : Blo 1879141 46354285 := bstep (se 3 (by rfl) ⟨8691428, by rfl⟩ : syracuseStep 46354285 = 17382857) B17382857
theorem B9514907 : Blo 1879141 9514907 := bstep (se 1 (by rfl) ⟨7136180, by rfl⟩ : syracuseStep 9514907 = 14272361) B14272361
theorem B7139279 : Blo 1879141 7139279 := bstep (se 1 (by rfl) ⟨5354459, by rfl⟩ : syracuseStep 7139279 = 10708919) B10708919
theorem B1880031 : Blo 1879141 1880031 := bstep (se 1 (by rfl) ⟨1410023, by rfl⟩ : syracuseStep 1880031 = 2820047) B2820047
theorem B8032441 : Blo 1879141 8032441 := bstep (se 2 (by rfl) ⟨3012165, by rfl⟩ : syracuseStep 8032441 = 6024331) B6024331
theorem B6344891 : Blo 1879141 6344891 := bstep (se 1 (by rfl) ⟨4758668, by rfl⟩ : syracuseStep 6344891 = 9517337) B9517337
theorem B3813563 : Blo 1879141 3813563 := bstep (se 1 (by rfl) ⟨2860172, by rfl⟩ : syracuseStep 3813563 = 5720345) B5720345
theorem B1880295 : Blo 1879141 1880295 := bstep (se 1 (by rfl) ⟨1410221, by rfl⟩ : syracuseStep 1880295 = 2820443) B2820443
theorem B12046589 : Blo 1879141 12046589 := bstep (se 3 (by rfl) ⟨2258735, by rfl⟩ : syracuseStep 12046589 = 4517471) B4517471
theorem B2896255 : Blo 1879141 2896255 := bstep (se 1 (by rfl) ⟨2172191, by rfl⟩ : syracuseStep 2896255 = 4344383) B4344383
theorem B1880447 : Blo 1879141 1880447 := bstep (se 1 (by rfl) ⟨1410335, by rfl⟩ : syracuseStep 1880447 = 2820671) B2820671
theorem B72315341 : Blo 1879141 72315341 := bstep (se 3 (by rfl) ⟨13559126, by rfl⟩ : syracuseStep 72315341 = 27118253) B27118253
theorem B1880527 : Blo 1879141 1880527 := bstep (se 1 (by rfl) ⟨1410395, by rfl⟩ : syracuseStep 1880527 = 2820791) B2820791
theorem B24089075 : Blo 1879141 24089075 := bstep (se 1 (by rfl) ⟨18066806, by rfl⟩ : syracuseStep 24089075 = 36133613) B36133613
theorem B3568121 : Blo 1879141 3568121 := bstep (se 2 (by rfl) ⟨1338045, by rfl⟩ : syracuseStep 3568121 = 2676091) B2676091
theorem B11432441 : Blo 1879141 11432441 := bstep (se 2 (by rfl) ⟨4287165, by rfl⟩ : syracuseStep 11432441 = 8574331) B8574331
theorem B4231673 : Blo 1879141 4231673 := bstep (se 2 (by rfl) ⟨1586877, by rfl⟩ : syracuseStep 4231673 = 3173755) B3173755
theorem B4231763 : Blo 1879141 4231763 := bstep (se 1 (by rfl) ⟨3173822, by rfl⟩ : syracuseStep 4231763 = 6347645) B6347645
theorem B1880679 : Blo 1879141 1880679 := bstep (se 1 (by rfl) ⟨1410509, by rfl⟩ : syracuseStep 1880679 = 2821019) B2821019
theorem B6345377 : Blo 1879141 6345377 := bstep (se 2 (by rfl) ⟨2379516, by rfl⟩ : syracuseStep 6345377 = 4759033) B4759033
theorem B4231943 : Blo 1879141 4231943 := bstep (se 1 (by rfl) ⟨3173957, by rfl⟩ : syracuseStep 4231943 = 6347915) B6347915
theorem B1880943 : Blo 1879141 1880943 := bstep (se 1 (by rfl) ⟨1410707, by rfl⟩ : syracuseStep 1880943 = 2821415) B2821415
theorem B7140221 : Blo 1879141 7140221 := bstep (se 3 (by rfl) ⟨1338791, by rfl⟩ : syracuseStep 7140221 = 2677583) B2677583
theorem B5354369 : Blo 1879141 5354369 := bstep (se 2 (by rfl) ⟨2007888, by rfl⟩ : syracuseStep 5354369 = 4015777) B4015777
theorem B1880999 : Blo 1879141 1880999 := bstep (se 1 (by rfl) ⟨1410749, by rfl⟩ : syracuseStep 1880999 = 2821499) B2821499
theorem B1881083 : Blo 1879141 1881083 := bstep (se 1 (by rfl) ⟨1410812, by rfl⟩ : syracuseStep 1881083 = 2821625) B2821625
theorem B4289609 : Blo 1879141 4289609 := bstep (se 2 (by rfl) ⟨1608603, by rfl⟩ : syracuseStep 4289609 = 3217207) B3217207
theorem B10712519 : Blo 1879141 10712519 := bstep (se 1 (by rfl) ⟨8034389, by rfl⟩ : syracuseStep 10712519 = 16068779) B16068779
theorem B6346241 : Blo 1879141 6346241 := bstep (se 2 (by rfl) ⟨2379840, by rfl⟩ : syracuseStep 6346241 = 4759681) B4759681
theorem B6870529 : Blo 1879141 6870529 := bstep (se 2 (by rfl) ⟨2576448, by rfl⟩ : syracuseStep 6870529 = 5152897) B5152897
theorem B10589753 : Blo 1879141 10589753 := bstep (se 2 (by rfl) ⟨3971157, by rfl⟩ : syracuseStep 10589753 = 7942315) B7942315
theorem B5576663 : Blo 1879141 5576663 := bstep (se 1 (by rfl) ⟨4182497, by rfl⟩ : syracuseStep 5576663 = 8364995) B8364995
theorem B6346727 : Blo 1879141 6346727 := bstep (se 1 (by rfl) ⟨4760045, by rfl⟩ : syracuseStep 6346727 = 9520091) B9520091
theorem B72275975 : Blo 1879141 72275975 := bstep (se 1 (by rfl) ⟨54206981, by rfl⟩ : syracuseStep 72275975 = 108413963) B108413963
theorem B6346835 : Blo 1879141 6346835 := bstep (se 1 (by rfl) ⟨4760126, by rfl⟩ : syracuseStep 6346835 = 9520253) B9520253
theorem B4823183 : Blo 1879141 4823183 := bstep (se 1 (by rfl) ⟨3617387, by rfl⟩ : syracuseStep 4823183 = 7234775) B7234775
theorem B3569807 : Blo 1879141 3569807 := bstep (se 1 (by rfl) ⟨2677355, by rfl⟩ : syracuseStep 3569807 = 5354711) B5354711
theorem B4757737 : Blo 1879141 4757737 := bstep (se 2 (by rfl) ⟨1784151, by rfl⟩ : syracuseStep 4757737 = 3568303) B3568303
theorem B6347051 : Blo 1879141 6347051 := bstep (se 1 (by rfl) ⟨4760288, by rfl⟩ : syracuseStep 6347051 = 9520577) B9520577
theorem B18070073 : Blo 1879141 18070073 := bstep (se 2 (by rfl) ⟨6776277, by rfl⟩ : syracuseStep 18070073 = 13552555) B13552555
theorem B6347321 : Blo 1879141 6347321 := bstep (se 2 (by rfl) ⟨2380245, by rfl⟩ : syracuseStep 6347321 = 4760491) B4760491
theorem B5356169 : Blo 1879141 5356169 := bstep (se 2 (by rfl) ⟨2008563, by rfl⟩ : syracuseStep 5356169 = 4017127) B4017127
theorem B4758497 : Blo 1879141 4758497 := bstep (se 2 (by rfl) ⟨1784436, by rfl⟩ : syracuseStep 4758497 = 3568873) B3568873
theorem B12041257 : Blo 1879141 12041257 := bstep (se 2 (by rfl) ⟨4515471, by rfl⟩ : syracuseStep 12041257 = 9030943) B9030943
theorem B24100193 : Blo 1879141 24100193 := bstep (se 2 (by rfl) ⟨9037572, by rfl⟩ : syracuseStep 24100193 = 18075145) B18075145
theorem B16055657 : Blo 1879141 16055657 := bstep (se 2 (by rfl) ⟨6020871, by rfl⟩ : syracuseStep 16055657 = 12041743) B12041743
theorem B20610409 : Blo 1879141 20610409 := bstep (se 2 (by rfl) ⟨7728903, by rfl⟩ : syracuseStep 20610409 = 15457807) B15457807
theorem B4013479 : Blo 1879141 4013479 := bstep (se 1 (by rfl) ⟨3010109, by rfl⟩ : syracuseStep 4013479 = 6020219) B6020219
theorem B10853831 : Blo 1879141 10853831 := bstep (se 1 (by rfl) ⟨8140373, by rfl⟩ : syracuseStep 10853831 = 16280747) B16280747
theorem B49503737 : Blo 1879141 49503737 := bstep (se 2 (by rfl) ⟨18563901, by rfl⟩ : syracuseStep 49503737 = 37127803) B37127803
theorem B15245009 : Blo 1879141 15245009 := bstep (se 2 (by rfl) ⟨5716878, by rfl⟩ : syracuseStep 15245009 = 11433757) B11433757
theorem B5717729 : Blo 1879141 5717729 := bstep (se 2 (by rfl) ⟨2144148, by rfl⟩ : syracuseStep 5717729 = 4288297) B4288297
theorem B13549787 : Blo 1879141 13549787 := bstep (se 1 (by rfl) ⟨10162340, by rfl⟩ : syracuseStep 13549787 = 20324681) B20324681
theorem B48210227 : Blo 1879141 48210227 := bstep (se 1 (by rfl) ⟨36157670, by rfl⟩ : syracuseStep 48210227 = 72315341) B72315341
theorem B12861821 : Blo 1879141 12861821 := bstep (se 3 (by rfl) ⟨2411591, by rfl⟩ : syracuseStep 12861821 = 4823183) B4823183
theorem B18072071 : Blo 1879141 18072071 := bstep (se 1 (by rfl) ⟨13554053, by rfl⟩ : syracuseStep 18072071 = 27108107) B27108107
theorem B4760147 : Blo 1879141 4760147 := bstep (se 1 (by rfl) ⟨3570110, by rfl⟩ : syracuseStep 4760147 = 7140221) B7140221
theorem B347439941 : Blo 1879141 347439941 := bstep (se 4 (by rfl) ⟨32572494, by rfl⟩ : syracuseStep 347439941 = 65144989) B65144989
theorem B14271389 : Blo 1879141 14271389 := bstep (se 3 (by rfl) ⟨2675885, by rfl⟩ : syracuseStep 14271389 = 5351771) B5351771
theorem B2819015 : Blo 1879141 2819015 := bstep (se 1 (by rfl) ⟨2114261, by rfl⟩ : syracuseStep 2819015 = 4228523) B4228523
theorem B4228091 : Blo 1879141 4228091 := bstep (se 1 (by rfl) ⟨3171068, by rfl⟩ : syracuseStep 4228091 = 6342137) B6342137
theorem B2819183 : Blo 1879141 2819183 := bstep (se 1 (by rfl) ⟨2114387, by rfl⟩ : syracuseStep 2819183 = 4228775) B4228775
theorem B2114671 : Blo 1879141 2114671 := bstep (se 1 (by rfl) ⟨1586003, by rfl⟩ : syracuseStep 2114671 = 3172007) B3172007
theorem B4228271 : Blo 1879141 4228271 := bstep (se 1 (by rfl) ⟨3171203, by rfl⟩ : syracuseStep 4228271 = 6342407) B6342407
theorem B4228307 : Blo 1879141 4228307 := bstep (se 1 (by rfl) ⟨3171230, by rfl⟩ : syracuseStep 4228307 = 6342461) B6342461
theorem B32113907 : Blo 1879141 32113907 := bstep (se 1 (by rfl) ⟨24085430, by rfl⟩ : syracuseStep 32113907 = 48170861) B48170861
theorem B2819375 : Blo 1879141 2819375 := bstep (se 1 (by rfl) ⟨2114531, by rfl⟩ : syracuseStep 2819375 = 4229063) B4229063
theorem B4228577 : Blo 1879141 4228577 := bstep (se 2 (by rfl) ⟨1585716, by rfl⟩ : syracuseStep 4228577 = 3171433) B3171433
theorem B2819579 : Blo 1879141 2819579 := bstep (se 1 (by rfl) ⟨2114684, by rfl⟩ : syracuseStep 2819579 = 4229369) B4229369
theorem B2819615 : Blo 1879141 2819615 := bstep (se 1 (by rfl) ⟨2114711, by rfl⟩ : syracuseStep 2819615 = 4229423) B4229423
theorem B2115103 : Blo 1879141 2115103 := bstep (se 1 (by rfl) ⟨1586327, by rfl⟩ : syracuseStep 2115103 = 3172655) B3172655
theorem B2819759 : Blo 1879141 2819759 := bstep (se 1 (by rfl) ⟨2114819, by rfl⟩ : syracuseStep 2819759 = 4229639) B4229639
theorem B16058047 : Blo 1879141 16058047 := bstep (se 1 (by rfl) ⟨12043535, by rfl⟩ : syracuseStep 16058047 = 24087071) B24087071
theorem B2819879 : Blo 1879141 2819879 := bstep (se 1 (by rfl) ⟨2114909, by rfl⟩ : syracuseStep 2819879 = 4229819) B4229819
theorem B5351305 : Blo 1879141 5351305 := bstep (se 2 (by rfl) ⟨2006739, by rfl⟩ : syracuseStep 5351305 = 4013479) B4013479
theorem B15247277 : Blo 1879141 15247277 := bstep (se 3 (by rfl) ⟨2858864, by rfl⟩ : syracuseStep 15247277 = 5717729) B5717729
theorem B3172331 : Blo 1879141 3172331 := bstep (se 1 (by rfl) ⟨2379248, by rfl⟩ : syracuseStep 3172331 = 4758497) B4758497
theorem B9160705 : Blo 1879141 9160705 := bstep (se 2 (by rfl) ⟨3435264, by rfl⟩ : syracuseStep 9160705 = 6870529) B6870529
theorem B16066795 : Blo 1879141 16066795 := bstep (se 1 (by rfl) ⟨12050096, by rfl⟩ : syracuseStep 16066795 = 24100193) B24100193
theorem B45762839 : Blo 1879141 45762839 := bstep (se 1 (by rfl) ⟨34322129, by rfl⟩ : syracuseStep 45762839 = 68644259) B68644259
theorem B7235887 : Blo 1879141 7235887 := bstep (se 1 (by rfl) ⟨5426915, by rfl⟩ : syracuseStep 7235887 = 10853831) B10853831
theorem B32131403 : Blo 1879141 32131403 := bstep (se 1 (by rfl) ⟨24098552, by rfl⟩ : syracuseStep 32131403 = 48197105) B48197105
theorem B2820431 : Blo 1879141 2820431 := bstep (se 1 (by rfl) ⟨2115323, by rfl⟩ : syracuseStep 2820431 = 4230647) B4230647
theorem B2820479 : Blo 1879141 2820479 := bstep (se 1 (by rfl) ⟨2115359, by rfl⟩ : syracuseStep 2820479 = 4230719) B4230719
theorem B2115967 : Blo 1879141 2115967 := bstep (se 1 (by rfl) ⟨1586975, by rfl⟩ : syracuseStep 2115967 = 3173951) B3173951
theorem B2820521 : Blo 1879141 2820521 := bstep (se 2 (by rfl) ⟨1057695, by rfl⟩ : syracuseStep 2820521 = 2115391) B2115391
theorem B12864071 : Blo 1879141 12864071 := bstep (se 1 (by rfl) ⟨9648053, by rfl⟩ : syracuseStep 12864071 = 19296107) B19296107
theorem B6343271 : Blo 1879141 6343271 := bstep (se 1 (by rfl) ⟨4757453, by rfl⟩ : syracuseStep 6343271 = 9514907) B9514907
theorem B4229927 : Blo 1879141 4229927 := bstep (se 1 (by rfl) ⟨3172445, by rfl⟩ : syracuseStep 4229927 = 6344891) B6344891
theorem B2542375 : Blo 1879141 2542375 := bstep (se 1 (by rfl) ⟨1906781, by rfl⟩ : syracuseStep 2542375 = 3813563) B3813563
theorem B2820905 : Blo 1879141 2820905 := bstep (se 2 (by rfl) ⟨1057839, by rfl⟩ : syracuseStep 2820905 = 2115679) B2115679
theorem B8031059 : Blo 1879141 8031059 := bstep (se 1 (by rfl) ⟨6023294, by rfl⟩ : syracuseStep 8031059 = 12046589) B12046589
theorem B11438957 : Blo 1879141 11438957 := bstep (se 3 (by rfl) ⟨2144804, by rfl⟩ : syracuseStep 11438957 = 4289609) B4289609
theorem B10709921 : Blo 1879141 10709921 := bstep (se 2 (by rfl) ⟨4016220, by rfl⟩ : syracuseStep 10709921 = 8032441) B8032441
theorem B9513935 : Blo 1879141 9513935 := bstep (se 1 (by rfl) ⟨7135451, by rfl⟩ : syracuseStep 9513935 = 14270903) B14270903
theorem B6343649 : Blo 1879141 6343649 := bstep (se 2 (by rfl) ⟨2378868, by rfl⟩ : syracuseStep 6343649 = 4757737) B4757737
theorem B16059383 : Blo 1879141 16059383 := bstep (se 1 (by rfl) ⟨12044537, by rfl⟩ : syracuseStep 16059383 = 24089075) B24089075
theorem B2378747 : Blo 1879141 2378747 := bstep (se 1 (by rfl) ⟨1784060, by rfl⟩ : syracuseStep 2378747 = 3568121) B3568121
theorem B7621627 : Blo 1879141 7621627 := bstep (se 1 (by rfl) ⟨5716220, by rfl⟩ : syracuseStep 7621627 = 11432441) B11432441
theorem B2821115 : Blo 1879141 2821115 := bstep (se 1 (by rfl) ⟨2115836, by rfl⟩ : syracuseStep 2821115 = 4231673) B4231673
theorem B2821175 : Blo 1879141 2821175 := bstep (se 1 (by rfl) ⟨2115881, by rfl⟩ : syracuseStep 2821175 = 4231763) B4231763
theorem B4230251 : Blo 1879141 4230251 := bstep (se 1 (by rfl) ⟨3172688, by rfl⟩ : syracuseStep 4230251 = 6345377) B6345377
theorem B2821295 : Blo 1879141 2821295 := bstep (se 1 (by rfl) ⟨2115971, by rfl⟩ : syracuseStep 2821295 = 4231943) B4231943
theorem B5877011 : Blo 1879141 5877011 := bstep (se 1 (by rfl) ⟨4407758, by rfl⟩ : syracuseStep 5877011 = 8815517) B8815517
theorem B4230521 : Blo 1879141 4230521 := bstep (se 2 (by rfl) ⟨1586445, by rfl⟩ : syracuseStep 4230521 = 3172891) B3172891
theorem B1879423 : Blo 1879141 1879423 := bstep (se 1 (by rfl) ⟨1409567, by rfl⟩ : syracuseStep 1879423 = 2819135) B2819135
theorem B1879451 : Blo 1879141 1879451 := bstep (se 1 (by rfl) ⟨1409588, by rfl⟩ : syracuseStep 1879451 = 2819177) B2819177
theorem B1879519 : Blo 1879141 1879519 := bstep (se 1 (by rfl) ⟨1409639, by rfl⟩ : syracuseStep 1879519 = 2819279) B2819279
theorem B1879655 : Blo 1879141 1879655 := bstep (se 1 (by rfl) ⟨1409741, by rfl⟩ : syracuseStep 1879655 = 2819483) B2819483
theorem B4230827 : Blo 1879141 4230827 := bstep (se 1 (by rfl) ⟨3173120, by rfl⟩ : syracuseStep 4230827 = 6346241) B6346241
theorem B137154221 : Blo 1879141 137154221 := bstep (se 3 (by rfl) ⟨25716416, by rfl⟩ : syracuseStep 137154221 = 51432833) B51432833
theorem B3010231 : Blo 1879141 3010231 := bstep (se 1 (by rfl) ⟨2257673, by rfl⟩ : syracuseStep 3010231 = 4515347) B4515347
theorem B1879803 : Blo 1879141 1879803 := bstep (se 1 (by rfl) ⟨1409852, by rfl⟩ : syracuseStep 1879803 = 2819705) B2819705
theorem B1879871 : Blo 1879141 1879871 := bstep (se 1 (by rfl) ⟨1409903, by rfl⟩ : syracuseStep 1879871 = 2819807) B2819807
theorem B1879935 : Blo 1879141 1879935 := bstep (se 1 (by rfl) ⟨1409951, by rfl⟩ : syracuseStep 1879935 = 2819903) B2819903
theorem B1880047 : Blo 1879141 1880047 := bstep (se 1 (by rfl) ⟨1410035, by rfl⟩ : syracuseStep 1880047 = 2820071) B2820071
theorem B4231151 : Blo 1879141 4231151 := bstep (se 1 (by rfl) ⟨3173363, by rfl⟩ : syracuseStep 4231151 = 6346727) B6346727
theorem B1880059 : Blo 1879141 1880059 := bstep (se 1 (by rfl) ⟨1410044, by rfl⟩ : syracuseStep 1880059 = 2820089) B2820089
theorem B4231223 : Blo 1879141 4231223 := bstep (se 1 (by rfl) ⟨3173417, by rfl⟩ : syracuseStep 4231223 = 6346835) B6346835
theorem B1880127 : Blo 1879141 1880127 := bstep (se 1 (by rfl) ⟨1410095, by rfl⟩ : syracuseStep 1880127 = 2820191) B2820191
theorem B2379871 : Blo 1879141 2379871 := bstep (se 1 (by rfl) ⟨1784903, by rfl⟩ : syracuseStep 2379871 = 3569807) B3569807
theorem B1880167 : Blo 1879141 1880167 := bstep (se 1 (by rfl) ⟨1410125, by rfl⟩ : syracuseStep 1880167 = 2820251) B2820251
theorem B1880191 : Blo 1879141 1880191 := bstep (se 1 (by rfl) ⟨1410143, by rfl⟩ : syracuseStep 1880191 = 2820287) B2820287
theorem B1880219 : Blo 1879141 1880219 := bstep (se 1 (by rfl) ⟨1410164, by rfl⟩ : syracuseStep 1880219 = 2820329) B2820329
theorem B4231367 : Blo 1879141 4231367 := bstep (se 1 (by rfl) ⟨3173525, by rfl⟩ : syracuseStep 4231367 = 6347051) B6347051
theorem B1880423 : Blo 1879141 1880423 := bstep (se 1 (by rfl) ⟨1410317, by rfl⟩ : syracuseStep 1880423 = 2820635) B2820635
theorem B12046715 : Blo 1879141 12046715 := bstep (se 1 (by rfl) ⟨9035036, by rfl⟩ : syracuseStep 12046715 = 18070073) B18070073
theorem B8573309 : Blo 1879141 8573309 := bstep (se 3 (by rfl) ⟨1607495, by rfl⟩ : syracuseStep 8573309 = 3214991) B3214991
theorem B4231547 : Blo 1879141 4231547 := bstep (se 1 (by rfl) ⟨3173660, by rfl⟩ : syracuseStep 4231547 = 6347321) B6347321
theorem B1880475 : Blo 1879141 1880475 := bstep (se 1 (by rfl) ⟨1410356, by rfl⟩ : syracuseStep 1880475 = 2820713) B2820713
theorem B27480545 : Blo 1879141 27480545 := bstep (se 2 (by rfl) ⟨10305204, by rfl⟩ : syracuseStep 27480545 = 20610409) B20610409
theorem B4231817 : Blo 1879141 4231817 := bstep (se 2 (by rfl) ⟨1586931, by rfl⟩ : syracuseStep 4231817 = 3173863) B3173863
theorem B15446693 : Blo 1879141 15446693 := bstep (se 4 (by rfl) ⟨1448127, by rfl⟩ : syracuseStep 15446693 = 2896255) B2896255
theorem B13546187 : Blo 1879141 13546187 := bstep (se 1 (by rfl) ⟨10159640, by rfl⟩ : syracuseStep 13546187 = 20319281) B20319281
theorem B1880827 : Blo 1879141 1880827 := bstep (se 1 (by rfl) ⟨1410620, by rfl⟩ : syracuseStep 1880827 = 2821241) B2821241
theorem B1880895 : Blo 1879141 1880895 := bstep (se 1 (by rfl) ⟨1410671, by rfl⟩ : syracuseStep 1880895 = 2821343) B2821343
theorem B1880923 : Blo 1879141 1880923 := bstep (se 1 (by rfl) ⟨1410692, by rfl⟩ : syracuseStep 1880923 = 2821385) B2821385
theorem B17150849 : Blo 1879141 17150849 := bstep (se 2 (by rfl) ⟨6431568, by rfl⟩ : syracuseStep 17150849 = 12863137) B12863137
theorem B39654289 : Blo 1879141 39654289 := bstep (se 2 (by rfl) ⟨14870358, by rfl⟩ : syracuseStep 39654289 = 29740717) B29740717
theorem B10703771 : Blo 1879141 10703771 := bstep (se 1 (by rfl) ⟨8027828, by rfl⟩ : syracuseStep 10703771 = 16055657) B16055657
theorem B1880991 : Blo 1879141 1880991 := bstep (se 1 (by rfl) ⟨1410743, by rfl⟩ : syracuseStep 1880991 = 2821487) B2821487
theorem B1881071 : Blo 1879141 1881071 := bstep (se 1 (by rfl) ⟨1410803, by rfl⟩ : syracuseStep 1881071 = 2821607) B2821607
theorem B33002491 : Blo 1879141 33002491 := bstep (se 1 (by rfl) ⟨24751868, by rfl⟩ : syracuseStep 33002491 = 49503737) B49503737
theorem B9516041 : Blo 1879141 9516041 := bstep (se 2 (by rfl) ⟨3568515, by rfl⟩ : syracuseStep 9516041 = 7137031) B7137031
theorem B10163339 : Blo 1879141 10163339 := bstep (se 1 (by rfl) ⟨7622504, by rfl⟩ : syracuseStep 10163339 = 15245009) B15245009
theorem B61805713 : Blo 1879141 61805713 := bstep (se 2 (by rfl) ⟨23177142, by rfl⟩ : syracuseStep 61805713 = 46354285) B46354285
theorem B79263029 : Blo 1879141 79263029 := bstep (se 5 (by rfl) ⟨3715454, by rfl⟩ : syracuseStep 79263029 = 7430909) B7430909
theorem B4232555 : Blo 1879141 4232555 := bstep (se 1 (by rfl) ⟨3174416, by rfl⟩ : syracuseStep 4232555 = 6348833) B6348833
theorem B10704797 : Blo 1879141 10704797 := bstep (se 3 (by rfl) ⟨2007149, by rfl⟩ : syracuseStep 10704797 = 4014299) B4014299
theorem B3569579 : Blo 1879141 3569579 := bstep (se 1 (by rfl) ⟨2677184, by rfl⟩ : syracuseStep 3569579 = 5354369) B5354369
theorem B7141679 : Blo 1879141 7141679 := bstep (se 1 (by rfl) ⟨5356259, by rfl⟩ : syracuseStep 7141679 = 10712519) B10712519
theorem B6347105 : Blo 1879141 6347105 := bstep (se 2 (by rfl) ⟨2380164, by rfl⟩ : syracuseStep 6347105 = 4760329) B4760329
theorem B7059835 : Blo 1879141 7059835 := bstep (se 1 (by rfl) ⟨5294876, by rfl⟩ : syracuseStep 7059835 = 10589753) B10589753
theorem B4757899 : Blo 1879141 4757899 := bstep (se 1 (by rfl) ⟨3568424, by rfl⟩ : syracuseStep 4757899 = 7136849) B7136849
theorem B3717775 : Blo 1879141 3717775 := bstep (se 1 (by rfl) ⟨2788331, by rfl⟩ : syracuseStep 3717775 = 5576663) B5576663
theorem B48183983 : Blo 1879141 48183983 := bstep (se 1 (by rfl) ⟨36137987, by rfl⟩ : syracuseStep 48183983 = 72275975) B72275975
theorem B16055009 : Blo 1879141 16055009 := bstep (se 2 (by rfl) ⟨6020628, by rfl⟩ : syracuseStep 16055009 = 12041257) B12041257
theorem B7232311 : Blo 1879141 7232311 := bstep (se 1 (by rfl) ⟨5424233, by rfl⟩ : syracuseStep 7232311 = 10848467) B10848467
theorem B6347591 : Blo 1879141 6347591 := bstep (se 1 (by rfl) ⟨4760693, by rfl⟩ : syracuseStep 6347591 = 9521387) B9521387
theorem B13556591 : Blo 1879141 13556591 := bstep (se 1 (by rfl) ⟨10167443, by rfl⟩ : syracuseStep 13556591 = 20334887) B20334887
theorem B3570779 : Blo 1879141 3570779 := bstep (se 1 (by rfl) ⟨2678084, by rfl⟩ : syracuseStep 3570779 = 5356169) B5356169
theorem B6348455 : Blo 1879141 6348455 := bstep (se 1 (by rfl) ⟨4761341, by rfl⟩ : syracuseStep 6348455 = 9522683) B9522683
theorem B6348563 : Blo 1879141 6348563 := bstep (se 1 (by rfl) ⟨4761422, by rfl⟩ : syracuseStep 6348563 = 9522845) B9522845
theorem B7135087 : Blo 1879141 7135087 := bstep (se 1 (by rfl) ⟨5351315, by rfl⟩ : syracuseStep 7135087 = 10702631) B10702631
theorem B4759519 : Blo 1879141 4759519 := bstep (se 1 (by rfl) ⟨3569639, by rfl⟩ : syracuseStep 4759519 = 7139279) B7139279
theorem B48857093 : Blo 1879141 48857093 := bstep (se 4 (by rfl) ⟨4580352, by rfl⟩ : syracuseStep 48857093 = 9160705) B9160705
theorem B21422393 : Blo 1879141 21422393 := bstep (se 2 (by rfl) ⟨8033397, by rfl⟩ : syracuseStep 21422393 = 16066795) B16066795
theorem B10297795 : Blo 1879141 10297795 := bstep (se 1 (by rfl) ⟨7723346, by rfl⟩ : syracuseStep 10297795 = 15446693) B15446693
theorem B7135847 : Blo 1879141 7135847 := bstep (se 1 (by rfl) ⟨5351885, by rfl⟩ : syracuseStep 7135847 = 10703771) B10703771
theorem B2818727 : Blo 1879141 2818727 := bstep (se 1 (by rfl) ⟨2114045, by rfl⟩ : syracuseStep 2818727 = 4228091) B4228091
theorem B6775559 : Blo 1879141 6775559 := bstep (se 1 (by rfl) ⟨5081669, by rfl⟩ : syracuseStep 6775559 = 10163339) B10163339
theorem B2818847 : Blo 1879141 2818847 := bstep (se 1 (by rfl) ⟨2114135, by rfl⟩ : syracuseStep 2818847 = 4228271) B4228271
theorem B2818871 : Blo 1879141 2818871 := bstep (se 1 (by rfl) ⟨2114153, by rfl⟩ : syracuseStep 2818871 = 4228307) B4228307
theorem B4957033 : Blo 1879141 4957033 := bstep (se 2 (by rfl) ⟨1858887, by rfl⟩ : syracuseStep 4957033 = 3717775) B3717775
theorem B2819051 : Blo 1879141 2819051 := bstep (se 1 (by rfl) ⟨2114288, by rfl⟩ : syracuseStep 2819051 = 4228577) B4228577
theorem B52872385 : Blo 1879141 52872385 := bstep (se 2 (by rfl) ⟨19827144, by rfl⟩ : syracuseStep 52872385 = 39654289) B39654289
theorem B7136531 : Blo 1879141 7136531 := bstep (se 1 (by rfl) ⟨5352398, by rfl⟩ : syracuseStep 7136531 = 10704797) B10704797
theorem B2114887 : Blo 1879141 2114887 := bstep (se 1 (by rfl) ⟨1586165, by rfl⟩ : syracuseStep 2114887 = 3172331) B3172331
theorem B2819561 : Blo 1879141 2819561 := bstep (se 2 (by rfl) ⟨1057335, by rfl⟩ : syracuseStep 2819561 = 2114671) B2114671
theorem B30508559 : Blo 1879141 30508559 := bstep (se 1 (by rfl) ⟨22881419, by rfl⟩ : syracuseStep 30508559 = 45762839) B45762839
theorem B4761119 : Blo 1879141 4761119 := bstep (se 1 (by rfl) ⟨3570839, by rfl⟩ : syracuseStep 4761119 = 7141679) B7141679
theorem B4228847 : Blo 1879141 4228847 := bstep (se 1 (by rfl) ⟨3171635, by rfl⟩ : syracuseStep 4228847 = 6343271) B6343271
theorem B32122655 : Blo 1879141 32122655 := bstep (se 1 (by rfl) ⟨24091991, by rfl⟩ : syracuseStep 32122655 = 48183983) B48183983
theorem B2819951 : Blo 1879141 2819951 := bstep (se 1 (by rfl) ⟨2114963, by rfl⟩ : syracuseStep 2819951 = 4229927) B4229927
theorem B9037727 : Blo 1879141 9037727 := bstep (se 1 (by rfl) ⟨6778295, by rfl⟩ : syracuseStep 9037727 = 13556591) B13556591
theorem B6342623 : Blo 1879141 6342623 := bstep (se 1 (by rfl) ⟨4756967, by rfl⟩ : syracuseStep 6342623 = 9513935) B9513935
theorem B37652453 : Blo 1879141 37652453 := bstep (se 4 (by rfl) ⟨3529917, by rfl⟩ : syracuseStep 37652453 = 7059835) B7059835
theorem B4229099 : Blo 1879141 4229099 := bstep (se 1 (by rfl) ⟨3171824, by rfl⟩ : syracuseStep 4229099 = 6343649) B6343649
theorem B2820137 : Blo 1879141 2820137 := bstep (se 2 (by rfl) ⟨1057551, by rfl⟩ : syracuseStep 2820137 = 2115103) B2115103
theorem B2820167 : Blo 1879141 2820167 := bstep (se 1 (by rfl) ⟨2115125, by rfl⟩ : syracuseStep 2820167 = 4230251) B4230251
theorem B3918007 : Blo 1879141 3918007 := bstep (se 1 (by rfl) ⟨2938505, by rfl⟩ : syracuseStep 3918007 = 5877011) B5877011
theorem B2820347 : Blo 1879141 2820347 := bstep (se 1 (by rfl) ⟨2115260, by rfl⟩ : syracuseStep 2820347 = 4230521) B4230521
theorem B2820551 : Blo 1879141 2820551 := bstep (se 1 (by rfl) ⟨2115413, by rfl⟩ : syracuseStep 2820551 = 4230827) B4230827
theorem B9513449 : Blo 1879141 9513449 := bstep (se 2 (by rfl) ⟨3567543, by rfl⟩ : syracuseStep 9513449 = 7135087) B7135087
theorem B6343325 : Blo 1879141 6343325 := bstep (se 3 (by rfl) ⟨1189373, by rfl⟩ : syracuseStep 6343325 = 2378747) B2378747
theorem B2820767 : Blo 1879141 2820767 := bstep (se 1 (by rfl) ⟨2115575, by rfl⟩ : syracuseStep 2820767 = 4231151) B4231151
theorem B2820815 : Blo 1879141 2820815 := bstep (se 1 (by rfl) ⟨2115611, by rfl⟩ : syracuseStep 2820815 = 4231223) B4231223
theorem B3173161 : Blo 1879141 3173161 := bstep (se 2 (by rfl) ⟨1189935, by rfl⟩ : syracuseStep 3173161 = 2379871) B2379871
theorem B2820911 : Blo 1879141 2820911 := bstep (se 1 (by rfl) ⟨2115683, by rfl⟩ : syracuseStep 2820911 = 4231367) B4231367
theorem B32140151 : Blo 1879141 32140151 := bstep (se 1 (by rfl) ⟨24105113, by rfl⟩ : syracuseStep 32140151 = 48210227) B48210227
theorem B8031143 : Blo 1879141 8031143 := bstep (se 1 (by rfl) ⟨6023357, by rfl⟩ : syracuseStep 8031143 = 12046715) B12046715
theorem B2821031 : Blo 1879141 2821031 := bstep (se 1 (by rfl) ⟨2115773, by rfl⟩ : syracuseStep 2821031 = 4231547) B4231547
theorem B18320363 : Blo 1879141 18320363 := bstep (se 1 (by rfl) ⟨13740272, by rfl⟩ : syracuseStep 18320363 = 27480545) B27480545
theorem B3173431 : Blo 1879141 3173431 := bstep (se 1 (by rfl) ⟨2380073, by rfl⟩ : syracuseStep 3173431 = 4760147) B4760147
theorem B2821211 : Blo 1879141 2821211 := bstep (se 1 (by rfl) ⟨2115908, by rfl⟩ : syracuseStep 2821211 = 4231817) B4231817
theorem B9030791 : Blo 1879141 9030791 := bstep (se 1 (by rfl) ⟨6773093, by rfl⟩ : syracuseStep 9030791 = 13546187) B13546187
theorem B2821289 : Blo 1879141 2821289 := bstep (se 2 (by rfl) ⟨1057983, by rfl⟩ : syracuseStep 2821289 = 2115967) B2115967
theorem B6343865 : Blo 1879141 6343865 := bstep (se 2 (by rfl) ⟨2378949, by rfl⟩ : syracuseStep 6343865 = 4757899) B4757899
theorem B9514259 : Blo 1879141 9514259 := bstep (se 1 (by rfl) ⟨7135694, by rfl⟩ : syracuseStep 9514259 = 14271389) B14271389
theorem B1879343 : Blo 1879141 1879343 := bstep (se 1 (by rfl) ⟨1409507, by rfl⟩ : syracuseStep 1879343 = 2819015) B2819015
theorem B6344027 : Blo 1879141 6344027 := bstep (se 1 (by rfl) ⟨4758020, by rfl⟩ : syracuseStep 6344027 = 9516041) B9516041
theorem B1879455 : Blo 1879141 1879455 := bstep (se 1 (by rfl) ⟨1409591, by rfl⟩ : syracuseStep 1879455 = 2819183) B2819183
theorem B21409271 : Blo 1879141 21409271 := bstep (se 1 (by rfl) ⟨16056953, by rfl⟩ : syracuseStep 21409271 = 32113907) B32113907
theorem B1879583 : Blo 1879141 1879583 := bstep (se 1 (by rfl) ⟨1409687, by rfl⟩ : syracuseStep 1879583 = 2819375) B2819375
theorem B52842019 : Blo 1879141 52842019 := bstep (se 1 (by rfl) ⟨39631514, by rfl⟩ : syracuseStep 52842019 = 79263029) B79263029
theorem B2821703 : Blo 1879141 2821703 := bstep (se 1 (by rfl) ⟨2116277, by rfl⟩ : syracuseStep 2821703 = 4232555) B4232555
theorem B1879719 : Blo 1879141 1879719 := bstep (se 1 (by rfl) ⟨1409789, by rfl⟩ : syracuseStep 1879719 = 2819579) B2819579
theorem B1879743 : Blo 1879141 1879743 := bstep (se 1 (by rfl) ⟨1409807, by rfl⟩ : syracuseStep 1879743 = 2819615) B2819615
theorem B1879839 : Blo 1879141 1879839 := bstep (se 1 (by rfl) ⟨1409879, by rfl⟩ : syracuseStep 1879839 = 2819759) B2819759
theorem B1879919 : Blo 1879141 1879919 := bstep (se 1 (by rfl) ⟨1409939, by rfl⟩ : syracuseStep 1879919 = 2819879) B2819879
theorem B2379719 : Blo 1879141 2379719 := bstep (se 1 (by rfl) ⟨1784789, by rfl⟩ : syracuseStep 2379719 = 3569579) B3569579
theorem B44003321 : Blo 1879141 44003321 := bstep (se 2 (by rfl) ⟨16501245, by rfl⟩ : syracuseStep 44003321 = 33002491) B33002491
theorem B10162169 : Blo 1879141 10162169 := bstep (se 2 (by rfl) ⟨3810813, by rfl⟩ : syracuseStep 10162169 = 7621627) B7621627
theorem B82407617 : Blo 1879141 82407617 := bstep (se 2 (by rfl) ⟨30902856, by rfl⟩ : syracuseStep 82407617 = 61805713) B61805713
theorem B1880287 : Blo 1879141 1880287 := bstep (se 1 (by rfl) ⟨1410215, by rfl⟩ : syracuseStep 1880287 = 2820431) B2820431
theorem B4231403 : Blo 1879141 4231403 := bstep (se 1 (by rfl) ⟨3173552, by rfl⟩ : syracuseStep 4231403 = 6347105) B6347105
theorem B1880319 : Blo 1879141 1880319 := bstep (se 1 (by rfl) ⟨1410239, by rfl⟩ : syracuseStep 1880319 = 2820479) B2820479
theorem B1880347 : Blo 1879141 1880347 := bstep (se 1 (by rfl) ⟨1410260, by rfl⟩ : syracuseStep 1880347 = 2820521) B2820521
theorem B38572325 : Blo 1879141 38572325 := bstep (se 4 (by rfl) ⟨3616155, by rfl⟩ : syracuseStep 38572325 = 7232311) B7232311
theorem B10703339 : Blo 1879141 10703339 := bstep (se 1 (by rfl) ⟨8027504, by rfl⟩ : syracuseStep 10703339 = 16055009) B16055009
theorem B1880603 : Blo 1879141 1880603 := bstep (se 1 (by rfl) ⟨1410452, by rfl⟩ : syracuseStep 1880603 = 2820905) B2820905
theorem B4231727 : Blo 1879141 4231727 := bstep (se 1 (by rfl) ⟨3173795, by rfl⟩ : syracuseStep 4231727 = 6347591) B6347591
theorem B5354039 : Blo 1879141 5354039 := bstep (se 1 (by rfl) ⟨4015529, by rfl⟩ : syracuseStep 5354039 = 8031059) B8031059
theorem B7139947 : Blo 1879141 7139947 := bstep (se 1 (by rfl) ⟨5354960, by rfl⟩ : syracuseStep 7139947 = 10709921) B10709921
theorem B1880743 : Blo 1879141 1880743 := bstep (se 1 (by rfl) ⟨1410557, by rfl⟩ : syracuseStep 1880743 = 2821115) B2821115
theorem B1880783 : Blo 1879141 1880783 := bstep (se 1 (by rfl) ⟨1410587, by rfl⟩ : syracuseStep 1880783 = 2821175) B2821175
theorem B2380519 : Blo 1879141 2380519 := bstep (se 1 (by rfl) ⟨1785389, by rfl⟩ : syracuseStep 2380519 = 3570779) B3570779
theorem B1880863 : Blo 1879141 1880863 := bstep (se 1 (by rfl) ⟨1410647, by rfl⟩ : syracuseStep 1880863 = 2821295) B2821295
theorem B21410729 : Blo 1879141 21410729 := bstep (se 2 (by rfl) ⟨8029023, by rfl⟩ : syracuseStep 21410729 = 16058047) B16058047
theorem B4232303 : Blo 1879141 4232303 := bstep (se 1 (by rfl) ⟨3174227, by rfl⟩ : syracuseStep 4232303 = 6348455) B6348455
theorem B91436147 : Blo 1879141 91436147 := bstep (se 1 (by rfl) ⟨68577110, by rfl⟩ : syracuseStep 91436147 = 137154221) B137154221
theorem B4232375 : Blo 1879141 4232375 := bstep (se 1 (by rfl) ⟨3174281, by rfl⟩ : syracuseStep 4232375 = 6348563) B6348563
theorem B6346025 : Blo 1879141 6346025 := bstep (se 2 (by rfl) ⟨2379759, by rfl⟩ : syracuseStep 6346025 = 4759519) B4759519
theorem B9033191 : Blo 1879141 9033191 := bstep (se 1 (by rfl) ⟨6774893, by rfl⟩ : syracuseStep 9033191 = 13549787) B13549787
theorem B5715539 : Blo 1879141 5715539 := bstep (se 1 (by rfl) ⟨4286654, by rfl⟩ : syracuseStep 5715539 = 8573309) B8573309
theorem B8574547 : Blo 1879141 8574547 := bstep (se 1 (by rfl) ⟨6430910, by rfl⟩ : syracuseStep 8574547 = 12861821) B12861821
theorem B12048047 : Blo 1879141 12048047 := bstep (se 1 (by rfl) ⟨9036035, by rfl⟩ : syracuseStep 12048047 = 18072071) B18072071
theorem B9647849 : Blo 1879141 9647849 := bstep (se 2 (by rfl) ⟨3617943, by rfl⟩ : syracuseStep 9647849 = 7235887) B7235887
theorem B231626627 : Blo 1879141 231626627 := bstep (se 1 (by rfl) ⟨173719970, by rfl⟩ : syracuseStep 231626627 = 347439941) B347439941
theorem B11433899 : Blo 1879141 11433899 := bstep (se 1 (by rfl) ⟨8575424, by rfl⟩ : syracuseStep 11433899 = 17150849) B17150849
theorem B3389833 : Blo 1879141 3389833 := bstep (se 2 (by rfl) ⟨1271187, by rfl⟩ : syracuseStep 3389833 = 2542375) B2542375
theorem B10164851 : Blo 1879141 10164851 := bstep (se 1 (by rfl) ⟨7623638, by rfl⟩ : syracuseStep 10164851 = 15247277) B15247277
theorem B21420935 : Blo 1879141 21420935 := bstep (se 1 (by rfl) ⟨16065701, by rfl⟩ : syracuseStep 21420935 = 32131403) B32131403
theorem B8576047 : Blo 1879141 8576047 := bstep (se 1 (by rfl) ⟨6432035, by rfl⟩ : syracuseStep 8576047 = 12864071) B12864071
theorem B7625971 : Blo 1879141 7625971 := bstep (se 1 (by rfl) ⟨5719478, by rfl⟩ : syracuseStep 7625971 = 11438957) B11438957
theorem B10706255 : Blo 1879141 10706255 := bstep (se 1 (by rfl) ⟨8029691, by rfl⟩ : syracuseStep 10706255 = 16059383) B16059383
theorem B4013641 : Blo 1879141 4013641 := bstep (se 2 (by rfl) ⟨1505115, by rfl⟩ : syracuseStep 4013641 = 3010231) B3010231
theorem B7135073 : Blo 1879141 7135073 := bstep (se 2 (by rfl) ⟨2675652, by rfl⟩ : syracuseStep 7135073 = 5351305) B5351305
theorem B32571395 : Blo 1879141 32571395 := bstep (se 1 (by rfl) ⟨24428546, by rfl⟩ : syracuseStep 32571395 = 48857093) B48857093
theorem B25714883 : Blo 1879141 25714883 := bstep (se 1 (by rfl) ⟨19286162, by rfl⟩ : syracuseStep 25714883 = 38572325) B38572325
theorem B7135559 : Blo 1879141 7135559 := bstep (se 1 (by rfl) ⟨5351669, by rfl⟩ : syracuseStep 7135559 = 10703339) B10703339
theorem B13730393 : Blo 1879141 13730393 := bstep (se 2 (by rfl) ⟨5148897, by rfl⟩ : syracuseStep 13730393 = 10297795) B10297795
theorem B60957431 : Blo 1879141 60957431 := bstep (se 1 (by rfl) ⟨45718073, by rfl⟩ : syracuseStep 60957431 = 91436147) B91436147
theorem B9519929 : Blo 1879141 9519929 := bstep (se 2 (by rfl) ⟨3569973, by rfl⟩ : syracuseStep 9519929 = 7139947) B7139947
theorem B6022127 : Blo 1879141 6022127 := bstep (se 1 (by rfl) ⟨4516595, by rfl⟩ : syracuseStep 6022127 = 9033191) B9033191
theorem B3810359 : Blo 1879141 3810359 := bstep (se 1 (by rfl) ⟨2857769, by rfl⟩ : syracuseStep 3810359 = 5715539) B5715539
theorem B6431899 : Blo 1879141 6431899 := bstep (se 1 (by rfl) ⟨4823924, by rfl⟩ : syracuseStep 6431899 = 9647849) B9647849
theorem B2819231 : Blo 1879141 2819231 := bstep (se 1 (by rfl) ⟨2114423, by rfl⟩ : syracuseStep 2819231 = 4228847) B4228847
theorem B21415103 : Blo 1879141 21415103 := bstep (se 1 (by rfl) ⟨16061327, by rfl⟩ : syracuseStep 21415103 = 32122655) B32122655
theorem B4228415 : Blo 1879141 4228415 := bstep (se 1 (by rfl) ⟨3171311, by rfl⟩ : syracuseStep 4228415 = 6342623) B6342623
theorem B25101635 : Blo 1879141 25101635 := bstep (se 1 (by rfl) ⟨18826226, by rfl⟩ : syracuseStep 25101635 = 37652453) B37652453
theorem B2819399 : Blo 1879141 2819399 := bstep (se 1 (by rfl) ⟨2114549, by rfl⟩ : syracuseStep 2819399 = 4229099) B4229099
theorem B6342299 : Blo 1879141 6342299 := bstep (se 1 (by rfl) ⟨4756724, by rfl⟩ : syracuseStep 6342299 = 9513449) B9513449
theorem B6776567 : Blo 1879141 6776567 := bstep (se 1 (by rfl) ⟨5082425, by rfl⟩ : syracuseStep 6776567 = 10164851) B10164851
theorem B2819849 : Blo 1879141 2819849 := bstep (se 2 (by rfl) ⟨1057443, by rfl⟩ : syracuseStep 2819849 = 2114887) B2114887
theorem B4228883 : Blo 1879141 4228883 := bstep (se 1 (by rfl) ⟨3171662, by rfl⟩ : syracuseStep 4228883 = 6343325) B6343325
theorem B14280623 : Blo 1879141 14280623 := bstep (se 1 (by rfl) ⟨10710467, by rfl⟩ : syracuseStep 14280623 = 21420935) B21420935
theorem B5351521 : Blo 1879141 5351521 := bstep (se 2 (by rfl) ⟨2006820, by rfl⟩ : syracuseStep 5351521 = 4013641) B4013641
theorem B4229243 : Blo 1879141 4229243 := bstep (se 1 (by rfl) ⟨3171932, by rfl⟩ : syracuseStep 4229243 = 6343865) B6343865
theorem B6342839 : Blo 1879141 6342839 := bstep (se 1 (by rfl) ⟨4757129, by rfl⟩ : syracuseStep 6342839 = 9514259) B9514259
theorem B7137503 : Blo 1879141 7137503 := bstep (se 1 (by rfl) ⟨5353127, by rfl⟩ : syracuseStep 7137503 = 10706255) B10706255
theorem B4229351 : Blo 1879141 4229351 := bstep (se 1 (by rfl) ⟨3172013, by rfl⟩ : syracuseStep 4229351 = 6344027) B6344027
theorem B14272847 : Blo 1879141 14272847 := bstep (se 1 (by rfl) ⟨10704635, by rfl⟩ : syracuseStep 14272847 = 21409271) B21409271
theorem B54938411 : Blo 1879141 54938411 := bstep (se 1 (by rfl) ⟨41203808, by rfl⟩ : syracuseStep 54938411 = 82407617) B82407617
theorem B2820935 : Blo 1879141 2820935 := bstep (se 1 (by rfl) ⟨2115701, by rfl⟩ : syracuseStep 2820935 = 4231403) B4231403
theorem B14281595 : Blo 1879141 14281595 := bstep (se 1 (by rfl) ⟨10711196, by rfl⟩ : syracuseStep 14281595 = 21422393) B21422393
theorem B45738917 : Blo 1879141 45738917 := bstep (se 4 (by rfl) ⟨4288023, by rfl⟩ : syracuseStep 45738917 = 8576047) B8576047
theorem B2821151 : Blo 1879141 2821151 := bstep (se 1 (by rfl) ⟨2115863, by rfl⟩ : syracuseStep 2821151 = 4231727) B4231727
theorem B1879151 : Blo 1879141 1879151 := bstep (se 1 (by rfl) ⟨1409363, by rfl⟩ : syracuseStep 1879151 = 2818727) B2818727
theorem B4517039 : Blo 1879141 4517039 := bstep (se 1 (by rfl) ⟨3387779, by rfl⟩ : syracuseStep 4517039 = 6775559) B6775559
theorem B1879231 : Blo 1879141 1879231 := bstep (se 1 (by rfl) ⟨1409423, by rfl⟩ : syracuseStep 1879231 = 2818847) B2818847
theorem B1879247 : Blo 1879141 1879247 := bstep (se 1 (by rfl) ⟨1409435, by rfl⟩ : syracuseStep 1879247 = 2818871) B2818871
theorem B14273819 : Blo 1879141 14273819 := bstep (se 1 (by rfl) ⟨10705364, by rfl⟩ : syracuseStep 14273819 = 21410729) B21410729
theorem B1879367 : Blo 1879141 1879367 := bstep (se 1 (by rfl) ⟨1409525, by rfl⟩ : syracuseStep 1879367 = 2819051) B2819051
theorem B2821535 : Blo 1879141 2821535 := bstep (se 1 (by rfl) ⟨2116151, by rfl⟩ : syracuseStep 2821535 = 4232303) B4232303
theorem B2821583 : Blo 1879141 2821583 := bstep (se 1 (by rfl) ⟨2116187, by rfl⟩ : syracuseStep 2821583 = 4232375) B4232375
theorem B4230683 : Blo 1879141 4230683 := bstep (se 1 (by rfl) ⟨3173012, by rfl⟩ : syracuseStep 4230683 = 6346025) B6346025
theorem B3174025 : Blo 1879141 3174025 := bstep (se 2 (by rfl) ⟨1190259, by rfl⟩ : syracuseStep 3174025 = 2380519) B2380519
theorem B1879707 : Blo 1879141 1879707 := bstep (se 1 (by rfl) ⟨1409780, by rfl⟩ : syracuseStep 1879707 = 2819561) B2819561
theorem B3174079 : Blo 1879141 3174079 := bstep (se 1 (by rfl) ⟨2380559, by rfl⟩ : syracuseStep 3174079 = 4761119) B4761119
theorem B4230881 : Blo 1879141 4230881 := bstep (se 2 (by rfl) ⟨1586580, by rfl⟩ : syracuseStep 4230881 = 3173161) B3173161
theorem B8032031 : Blo 1879141 8032031 := bstep (se 1 (by rfl) ⟨6024023, by rfl⟩ : syracuseStep 8032031 = 12048047) B12048047
theorem B1879967 : Blo 1879141 1879967 := bstep (se 1 (by rfl) ⟨1409975, by rfl⟩ : syracuseStep 1879967 = 2819951) B2819951
theorem B6025151 : Blo 1879141 6025151 := bstep (se 1 (by rfl) ⟨4518863, by rfl⟩ : syracuseStep 6025151 = 9037727) B9037727
theorem B7622599 : Blo 1879141 7622599 := bstep (se 1 (by rfl) ⟨5716949, by rfl⟩ : syracuseStep 7622599 = 11433899) B11433899
theorem B1880091 : Blo 1879141 1880091 := bstep (se 1 (by rfl) ⟨1410068, by rfl⟩ : syracuseStep 1880091 = 2820137) B2820137
theorem B1880111 : Blo 1879141 1880111 := bstep (se 1 (by rfl) ⟨1410083, by rfl⟩ : syracuseStep 1880111 = 2820167) B2820167
theorem B4231241 : Blo 1879141 4231241 := bstep (se 2 (by rfl) ⟨1586715, by rfl⟩ : syracuseStep 4231241 = 3173431) B3173431
theorem B1880231 : Blo 1879141 1880231 := bstep (se 1 (by rfl) ⟨1410173, by rfl⟩ : syracuseStep 1880231 = 2820347) B2820347
theorem B70496513 : Blo 1879141 70496513 := bstep (se 2 (by rfl) ⟨26436192, by rfl⟩ : syracuseStep 70496513 = 52872385) B52872385
theorem B1880367 : Blo 1879141 1880367 := bstep (se 1 (by rfl) ⟨1410275, by rfl⟩ : syracuseStep 1880367 = 2820551) B2820551
theorem B1880511 : Blo 1879141 1880511 := bstep (se 1 (by rfl) ⟨1410383, by rfl⟩ : syracuseStep 1880511 = 2820767) B2820767
theorem B1880543 : Blo 1879141 1880543 := bstep (se 1 (by rfl) ⟨1410407, by rfl⟩ : syracuseStep 1880543 = 2820815) B2820815
theorem B1880607 : Blo 1879141 1880607 := bstep (se 1 (by rfl) ⟨1410455, by rfl⟩ : syracuseStep 1880607 = 2820911) B2820911
theorem B21426767 : Blo 1879141 21426767 := bstep (se 1 (by rfl) ⟨16070075, by rfl⟩ : syracuseStep 21426767 = 32140151) B32140151
theorem B5354095 : Blo 1879141 5354095 := bstep (se 1 (by rfl) ⟨4015571, by rfl⟩ : syracuseStep 5354095 = 8031143) B8031143
theorem B1880687 : Blo 1879141 1880687 := bstep (se 1 (by rfl) ⟨1410515, by rfl⟩ : syracuseStep 1880687 = 2821031) B2821031
theorem B70456025 : Blo 1879141 70456025 := bstep (se 2 (by rfl) ⟨26421009, by rfl⟩ : syracuseStep 70456025 = 52842019) B52842019
theorem B1880807 : Blo 1879141 1880807 := bstep (se 1 (by rfl) ⟨1410605, by rfl⟩ : syracuseStep 1880807 = 2821211) B2821211
theorem B11432729 : Blo 1879141 11432729 := bstep (se 2 (by rfl) ⟨4287273, by rfl⟩ : syracuseStep 11432729 = 8574547) B8574547
theorem B1880859 : Blo 1879141 1880859 := bstep (se 1 (by rfl) ⟨1410644, by rfl⟩ : syracuseStep 1880859 = 2821289) B2821289
theorem B1881135 : Blo 1879141 1881135 := bstep (se 1 (by rfl) ⟨1410851, by rfl⟩ : syracuseStep 1881135 = 2821703) B2821703
theorem B6345917 : Blo 1879141 6345917 := bstep (se 3 (by rfl) ⟨1189859, by rfl⟩ : syracuseStep 6345917 = 2379719) B2379719
theorem B4756715 : Blo 1879141 4756715 := bstep (se 1 (by rfl) ⟨3567536, by rfl⟩ : syracuseStep 4756715 = 7135073) B7135073
theorem B3569359 : Blo 1879141 3569359 := bstep (se 1 (by rfl) ⟨2677019, by rfl⟩ : syracuseStep 3569359 = 5354039) B5354039
theorem B4757231 : Blo 1879141 4757231 := bstep (se 1 (by rfl) ⟨3567923, by rfl⟩ : syracuseStep 4757231 = 7135847) B7135847
theorem B4757687 : Blo 1879141 4757687 := bstep (se 1 (by rfl) ⟨3568265, by rfl⟩ : syracuseStep 4757687 = 7136531) B7136531
theorem B20896037 : Blo 1879141 20896037 := bstep (se 4 (by rfl) ⟨1959003, by rfl⟩ : syracuseStep 20896037 = 3918007) B3918007
theorem B20339039 : Blo 1879141 20339039 := bstep (se 1 (by rfl) ⟨15254279, by rfl⟩ : syracuseStep 20339039 = 30508559) B30508559
theorem B6609377 : Blo 1879141 6609377 := bstep (se 2 (by rfl) ⟨2478516, by rfl⟩ : syracuseStep 6609377 = 4957033) B4957033
theorem B154417751 : Blo 1879141 154417751 := bstep (se 1 (by rfl) ⟨115813313, by rfl⟩ : syracuseStep 154417751 = 231626627) B231626627
theorem B40671845 : Blo 1879141 40671845 := bstep (se 4 (by rfl) ⟨3812985, by rfl⟩ : syracuseStep 40671845 = 7625971) B7625971
theorem B6774779 : Blo 1879141 6774779 := bstep (se 1 (by rfl) ⟨5081084, by rfl⟩ : syracuseStep 6774779 = 10162169) B10162169
theorem B12213575 : Blo 1879141 12213575 := bstep (se 1 (by rfl) ⟨9160181, by rfl⟩ : syracuseStep 12213575 = 18320363) B18320363
theorem B18079109 : Blo 1879141 18079109 := bstep (se 4 (by rfl) ⟨1694916, by rfl⟩ : syracuseStep 18079109 = 3389833) B3389833
theorem B6020527 : Blo 1879141 6020527 := bstep (se 1 (by rfl) ⟨4515395, by rfl⟩ : syracuseStep 6020527 = 9030791) B9030791
theorem B29335547 : Blo 1879141 29335547 := bstep (se 1 (by rfl) ⟨22001660, by rfl⟩ : syracuseStep 29335547 = 44003321) B44003321
theorem B7135361 : Blo 1879141 7135361 := bstep (se 2 (by rfl) ⟨2675760, by rfl⟩ : syracuseStep 7135361 = 5351521) B5351521
theorem B46997675 : Blo 1879141 46997675 := bstep (se 1 (by rfl) ⟨35248256, by rfl⟩ : syracuseStep 46997675 = 70496513) B70496513
theorem B3171143 : Blo 1879141 3171143 := bstep (se 1 (by rfl) ⟨2378357, by rfl⟩ : syracuseStep 3171143 = 4756715) B4756715
theorem B66937693 : Blo 1879141 66937693 := bstep (se 3 (by rfl) ⟨12550817, by rfl⟩ : syracuseStep 66937693 = 25101635) B25101635
theorem B2818943 : Blo 1879141 2818943 := bstep (se 1 (by rfl) ⟨2114207, by rfl⟩ : syracuseStep 2818943 = 4228415) B4228415
theorem B4228199 : Blo 1879141 4228199 := bstep (se 1 (by rfl) ⟨3171149, by rfl⟩ : syracuseStep 4228199 = 6342299) B6342299
theorem B3171487 : Blo 1879141 3171487 := bstep (se 1 (by rfl) ⟨2378615, by rfl⟩ : syracuseStep 3171487 = 4757231) B4757231
theorem B2819255 : Blo 1879141 2819255 := bstep (se 1 (by rfl) ⟨2114441, by rfl⟩ : syracuseStep 2819255 = 4228883) B4228883
theorem B9520415 : Blo 1879141 9520415 := bstep (se 1 (by rfl) ⟨7140311, by rfl⟩ : syracuseStep 9520415 = 14280623) B14280623
theorem B2819495 : Blo 1879141 2819495 := bstep (se 1 (by rfl) ⟨2114621, by rfl⟩ : syracuseStep 2819495 = 4229243) B4229243
theorem B4228559 : Blo 1879141 4228559 := bstep (se 1 (by rfl) ⟨3171419, by rfl⟩ : syracuseStep 4228559 = 6342839) B6342839
theorem B3171791 : Blo 1879141 3171791 := bstep (se 1 (by rfl) ⟨2378843, by rfl⟩ : syracuseStep 3171791 = 4757687) B4757687
theorem B2819567 : Blo 1879141 2819567 := bstep (se 1 (by rfl) ⟨2114675, by rfl⟩ : syracuseStep 2819567 = 4229351) B4229351
theorem B13559359 : Blo 1879141 13559359 := bstep (se 1 (by rfl) ⟨10169519, by rfl⟩ : syracuseStep 13559359 = 20339039) B20339039
theorem B9521063 : Blo 1879141 9521063 := bstep (se 1 (by rfl) ⟨7140797, by rfl⟩ : syracuseStep 9521063 = 14281595) B14281595
theorem B30492611 : Blo 1879141 30492611 := bstep (se 1 (by rfl) ⟨22869458, by rfl⟩ : syracuseStep 30492611 = 45738917) B45738917
theorem B12052739 : Blo 1879141 12052739 := bstep (se 1 (by rfl) ⟨9039554, by rfl⟩ : syracuseStep 12052739 = 18079109) B18079109
theorem B2820455 : Blo 1879141 2820455 := bstep (se 1 (by rfl) ⟨2115341, by rfl⟩ : syracuseStep 2820455 = 4230683) B4230683
theorem B2820587 : Blo 1879141 2820587 := bstep (se 1 (by rfl) ⟨2115440, by rfl⟩ : syracuseStep 2820587 = 4230881) B4230881
theorem B16067069 : Blo 1879141 16067069 := bstep (se 3 (by rfl) ⟨3012575, by rfl⟩ : syracuseStep 16067069 = 6025151) B6025151
theorem B16059005 : Blo 1879141 16059005 := bstep (se 3 (by rfl) ⟨3011063, by rfl⟩ : syracuseStep 16059005 = 6022127) B6022127
theorem B18066077 : Blo 1879141 18066077 := bstep (se 3 (by rfl) ⟨3387389, by rfl⟩ : syracuseStep 18066077 = 6774779) B6774779
theorem B78228125 : Blo 1879141 78228125 := bstep (se 3 (by rfl) ⟨14667773, by rfl⟩ : syracuseStep 78228125 = 29335547) B29335547
theorem B2820827 : Blo 1879141 2820827 := bstep (se 1 (by rfl) ⟨2115620, by rfl⟩ : syracuseStep 2820827 = 4231241) B4231241
theorem B10160957 : Blo 1879141 10160957 := bstep (se 3 (by rfl) ⟨1905179, by rfl⟩ : syracuseStep 10160957 = 3810359) B3810359
theorem B9153595 : Blo 1879141 9153595 := bstep (se 1 (by rfl) ⟨6865196, by rfl⟩ : syracuseStep 9153595 = 13730393) B13730393
theorem B7621819 : Blo 1879141 7621819 := bstep (se 1 (by rfl) ⟨5716364, by rfl⟩ : syracuseStep 7621819 = 11432729) B11432729
theorem B1879487 : Blo 1879141 1879487 := bstep (se 1 (by rfl) ⟨1409615, by rfl⟩ : syracuseStep 1879487 = 2819231) B2819231
theorem B4230611 : Blo 1879141 4230611 := bstep (se 1 (by rfl) ⟨3172958, by rfl⟩ : syracuseStep 4230611 = 6345917) B6345917
theorem B7138793 : Blo 1879141 7138793 := bstep (se 2 (by rfl) ⟨2677047, by rfl⟩ : syracuseStep 7138793 = 5354095) B5354095
theorem B1879599 : Blo 1879141 1879599 := bstep (se 1 (by rfl) ⟨1409699, by rfl⟩ : syracuseStep 1879599 = 2819399) B2819399
theorem B4517711 : Blo 1879141 4517711 := bstep (se 1 (by rfl) ⟨3388283, by rfl⟩ : syracuseStep 4517711 = 6776567) B6776567
theorem B1879899 : Blo 1879141 1879899 := bstep (se 1 (by rfl) ⟨1409924, by rfl⟩ : syracuseStep 1879899 = 2819849) B2819849
theorem B891564245 : Blo 1879141 891564245 := bstep (se 7 (by rfl) ⟨10448018, by rfl⟩ : syracuseStep 891564245 = 20896037) B20896037
theorem B9515231 : Blo 1879141 9515231 := bstep (se 1 (by rfl) ⟨7136423, by rfl⟩ : syracuseStep 9515231 = 14272847) B14272847
theorem B102945167 : Blo 1879141 102945167 := bstep (se 1 (by rfl) ⟨77208875, by rfl⟩ : syracuseStep 102945167 = 154417751) B154417751
theorem B1880623 : Blo 1879141 1880623 := bstep (se 1 (by rfl) ⟨1410467, by rfl⟩ : syracuseStep 1880623 = 2820935) B2820935
theorem B1880767 : Blo 1879141 1880767 := bstep (se 1 (by rfl) ⟨1410575, by rfl⟩ : syracuseStep 1880767 = 2821151) B2821151
theorem B3011359 : Blo 1879141 3011359 := bstep (se 1 (by rfl) ⟨2258519, by rfl⟩ : syracuseStep 3011359 = 4517039) B4517039
theorem B4232033 : Blo 1879141 4232033 := bstep (se 2 (by rfl) ⟨1587012, by rfl⟩ : syracuseStep 4232033 = 3174025) B3174025
theorem B9515879 : Blo 1879141 9515879 := bstep (se 1 (by rfl) ⟨7136909, by rfl⟩ : syracuseStep 9515879 = 14273819) B14273819
theorem B4232105 : Blo 1879141 4232105 := bstep (se 2 (by rfl) ⟨1587039, by rfl⟩ : syracuseStep 4232105 = 3174079) B3174079
theorem B1881023 : Blo 1879141 1881023 := bstep (se 1 (by rfl) ⟨1410767, by rfl⟩ : syracuseStep 1881023 = 2821535) B2821535
theorem B1881055 : Blo 1879141 1881055 := bstep (se 1 (by rfl) ⟨1410791, by rfl⟩ : syracuseStep 1881055 = 2821583) B2821583
theorem B5354687 : Blo 1879141 5354687 := bstep (se 1 (by rfl) ⟨4016015, by rfl⟩ : syracuseStep 5354687 = 8032031) B8032031
theorem B10163465 : Blo 1879141 10163465 := bstep (se 2 (by rfl) ⟨3811299, by rfl⟩ : syracuseStep 10163465 = 7622599) B7622599
theorem B21714263 : Blo 1879141 21714263 := bstep (se 1 (by rfl) ⟨16285697, by rfl⟩ : syracuseStep 21714263 = 32571395) B32571395
theorem B17143255 : Blo 1879141 17143255 := bstep (se 1 (by rfl) ⟨12857441, by rfl⟩ : syracuseStep 17143255 = 25714883) B25714883
theorem B4757039 : Blo 1879141 4757039 := bstep (se 1 (by rfl) ⟨3567779, by rfl⟩ : syracuseStep 4757039 = 7135559) B7135559
theorem B14284511 : Blo 1879141 14284511 := bstep (se 1 (by rfl) ⟨10713383, by rfl⟩ : syracuseStep 14284511 = 21426767) B21426767
theorem B40638287 : Blo 1879141 40638287 := bstep (se 1 (by rfl) ⟨30478715, by rfl⟩ : syracuseStep 40638287 = 60957431) B60957431
theorem B6346619 : Blo 1879141 6346619 := bstep (se 1 (by rfl) ⟨4759964, by rfl⟩ : syracuseStep 6346619 = 9519929) B9519929
theorem B14276735 : Blo 1879141 14276735 := bstep (se 1 (by rfl) ⟨10707551, by rfl⟩ : syracuseStep 14276735 = 21415103) B21415103
theorem B4758335 : Blo 1879141 4758335 := bstep (se 1 (by rfl) ⟨3568751, by rfl⟩ : syracuseStep 4758335 = 7137503) B7137503
theorem B8575865 : Blo 1879141 8575865 := bstep (se 2 (by rfl) ⟨3215949, by rfl⟩ : syracuseStep 8575865 = 6431899) B6431899
theorem B4406251 : Blo 1879141 4406251 := bstep (se 1 (by rfl) ⟨3304688, by rfl⟩ : syracuseStep 4406251 = 6609377) B6609377
theorem B27114563 : Blo 1879141 27114563 := bstep (se 1 (by rfl) ⟨20335922, by rfl⟩ : syracuseStep 27114563 = 40671845) B40671845
theorem B36625607 : Blo 1879141 36625607 := bstep (se 1 (by rfl) ⟨27469205, by rfl⟩ : syracuseStep 36625607 = 54938411) B54938411
theorem B8027369 : Blo 1879141 8027369 := bstep (se 2 (by rfl) ⟨3010263, by rfl⟩ : syracuseStep 8027369 = 6020527) B6020527
theorem B187882733 : Blo 1879141 187882733 := bstep (se 3 (by rfl) ⟨35228012, by rfl⟩ : syracuseStep 187882733 = 70456025) B70456025
theorem B8142383 : Blo 1879141 8142383 := bstep (se 1 (by rfl) ⟨6106787, by rfl⟩ : syracuseStep 8142383 = 12213575) B12213575
theorem B4759145 : Blo 1879141 4759145 := bstep (se 2 (by rfl) ⟨1784679, by rfl⟩ : syracuseStep 4759145 = 3569359) B3569359
theorem B14279165 : Blo 1879141 14279165 := bstep (se 3 (by rfl) ⟨2677343, by rfl⟩ : syracuseStep 14279165 = 5354687) B5354687
theorem B2114095 : Blo 1879141 2114095 := bstep (se 1 (by rfl) ⟨1585571, by rfl⟩ : syracuseStep 2114095 = 3171143) B3171143
theorem B2818799 : Blo 1879141 2818799 := bstep (se 1 (by rfl) ⟨2114099, by rfl⟩ : syracuseStep 2818799 = 4228199) B4228199
theorem B6775643 : Blo 1879141 6775643 := bstep (se 1 (by rfl) ⟨5081732, by rfl⟩ : syracuseStep 6775643 = 10163465) B10163465
theorem B14476175 : Blo 1879141 14476175 := bstep (se 1 (by rfl) ⟨10857131, by rfl⟩ : syracuseStep 14476175 = 21714263) B21714263
theorem B2819039 : Blo 1879141 2819039 := bstep (se 1 (by rfl) ⟨2114279, by rfl⟩ : syracuseStep 2819039 = 4228559) B4228559
theorem B2114527 : Blo 1879141 2114527 := bstep (se 1 (by rfl) ⟨1585895, by rfl⟩ : syracuseStep 2114527 = 3171791) B3171791
theorem B40649701 : Blo 1879141 40649701 := bstep (se 4 (by rfl) ⟨3810909, by rfl⟩ : syracuseStep 40649701 = 7621819) B7621819
theorem B3171359 : Blo 1879141 3171359 := bstep (se 1 (by rfl) ⟨2378519, by rfl⟩ : syracuseStep 3171359 = 4757039) B4757039
theorem B4015145 : Blo 1879141 4015145 := bstep (se 2 (by rfl) ⟨1505679, by rfl⟩ : syracuseStep 4015145 = 3011359) B3011359
theorem B27092191 : Blo 1879141 27092191 := bstep (se 1 (by rfl) ⟨20319143, by rfl⟩ : syracuseStep 27092191 = 40638287) B40638287
theorem B5875001 : Blo 1879141 5875001 := bstep (se 2 (by rfl) ⟨2203125, by rfl⟩ : syracuseStep 5875001 = 4406251) B4406251
theorem B4228649 : Blo 1879141 4228649 := bstep (se 2 (by rfl) ⟨1585743, by rfl⟩ : syracuseStep 4228649 = 3171487) B3171487
theorem B12044051 : Blo 1879141 12044051 := bstep (se 1 (by rfl) ⟨9033038, by rfl⟩ : syracuseStep 12044051 = 18066077) B18066077
theorem B52152083 : Blo 1879141 52152083 := bstep (se 1 (by rfl) ⟨39114062, by rfl⟩ : syracuseStep 52152083 = 78228125) B78228125
theorem B3172223 : Blo 1879141 3172223 := bstep (se 1 (by rfl) ⟨2379167, by rfl⟩ : syracuseStep 3172223 = 4758335) B4758335
theorem B5351579 : Blo 1879141 5351579 := bstep (se 1 (by rfl) ⟨4013684, by rfl⟩ : syracuseStep 5351579 = 8027369) B8027369
theorem B2820407 : Blo 1879141 2820407 := bstep (se 1 (by rfl) ⟨2115305, by rfl⟩ : syracuseStep 2820407 = 4230611) B4230611
theorem B3172763 : Blo 1879141 3172763 := bstep (se 1 (by rfl) ⟨2379572, by rfl⟩ : syracuseStep 3172763 = 4759145) B4759145
theorem B6343487 : Blo 1879141 6343487 := bstep (se 1 (by rfl) ⟨4757615, by rfl⟩ : syracuseStep 6343487 = 9515231) B9515231
theorem B2821355 : Blo 1879141 2821355 := bstep (se 1 (by rfl) ⟨2116016, by rfl⟩ : syracuseStep 2821355 = 4232033) B4232033
theorem B6343919 : Blo 1879141 6343919 := bstep (se 1 (by rfl) ⟨4757939, by rfl⟩ : syracuseStep 6343919 = 9515879) B9515879
theorem B1879295 : Blo 1879141 1879295 := bstep (se 1 (by rfl) ⟨1409471, by rfl⟩ : syracuseStep 1879295 = 2818943) B2818943
theorem B2821403 : Blo 1879141 2821403 := bstep (se 1 (by rfl) ⟨2116052, by rfl⟩ : syracuseStep 2821403 = 4232105) B4232105
theorem B1879503 : Blo 1879141 1879503 := bstep (se 1 (by rfl) ⟨1409627, by rfl⟩ : syracuseStep 1879503 = 2819255) B2819255
theorem B1879663 : Blo 1879141 1879663 := bstep (se 1 (by rfl) ⟨1409747, by rfl⟩ : syracuseStep 1879663 = 2819495) B2819495
theorem B1879711 : Blo 1879141 1879711 := bstep (se 1 (by rfl) ⟨1409783, by rfl⟩ : syracuseStep 1879711 = 2819567) B2819567
theorem B9523007 : Blo 1879141 9523007 := bstep (se 1 (by rfl) ⟨7142255, by rfl⟩ : syracuseStep 9523007 = 14284511) B14284511
theorem B4231079 : Blo 1879141 4231079 := bstep (se 1 (by rfl) ⟨3173309, by rfl⟩ : syracuseStep 4231079 = 6346619) B6346619
theorem B20328407 : Blo 1879141 20328407 := bstep (se 1 (by rfl) ⟨15246305, by rfl⟩ : syracuseStep 20328407 = 30492611) B30492611
theorem B1880303 : Blo 1879141 1880303 := bstep (se 1 (by rfl) ⟨1410227, by rfl⟩ : syracuseStep 1880303 = 2820455) B2820455
theorem B1880391 : Blo 1879141 1880391 := bstep (se 1 (by rfl) ⟨1410293, by rfl⟩ : syracuseStep 1880391 = 2820587) B2820587
theorem B10711379 : Blo 1879141 10711379 := bstep (se 1 (by rfl) ⟨8033534, by rfl⟩ : syracuseStep 10711379 = 16067069) B16067069
theorem B1880551 : Blo 1879141 1880551 := bstep (se 1 (by rfl) ⟨1410413, by rfl⟩ : syracuseStep 1880551 = 2820827) B2820827
theorem B18076375 : Blo 1879141 18076375 := bstep (se 1 (by rfl) ⟨13557281, by rfl⟩ : syracuseStep 18076375 = 27114563) B27114563
theorem B24417071 : Blo 1879141 24417071 := bstep (se 1 (by rfl) ⟨18312803, by rfl⟩ : syracuseStep 24417071 = 36625607) B36625607
theorem B5428255 : Blo 1879141 5428255 := bstep (se 1 (by rfl) ⟨4071191, by rfl⟩ : syracuseStep 5428255 = 8142383) B8142383
theorem B3011807 : Blo 1879141 3011807 := bstep (se 1 (by rfl) ⟨2258855, by rfl⟩ : syracuseStep 3011807 = 4517711) B4517711
theorem B4756907 : Blo 1879141 4756907 := bstep (se 1 (by rfl) ⟨3567680, by rfl⟩ : syracuseStep 4756907 = 7135361) B7135361
theorem B31331783 : Blo 1879141 31331783 := bstep (se 1 (by rfl) ⟨23498837, by rfl⟩ : syracuseStep 31331783 = 46997675) B46997675
theorem B594376163 : Blo 1879141 594376163 := bstep (se 1 (by rfl) ⟨445782122, by rfl⟩ : syracuseStep 594376163 = 891564245) B891564245
theorem B68630111 : Blo 1879141 68630111 := bstep (se 1 (by rfl) ⟨51472583, by rfl⟩ : syracuseStep 68630111 = 102945167) B102945167
theorem B6346943 : Blo 1879141 6346943 := bstep (se 1 (by rfl) ⟨4760207, by rfl⟩ : syracuseStep 6346943 = 9520415) B9520415
theorem B89250257 : Blo 1879141 89250257 := bstep (se 2 (by rfl) ⟨33468846, by rfl⟩ : syracuseStep 89250257 = 66937693) B66937693
theorem B6347375 : Blo 1879141 6347375 := bstep (se 1 (by rfl) ⟨4760531, by rfl⟩ : syracuseStep 6347375 = 9521063) B9521063
theorem B12204793 : Blo 1879141 12204793 := bstep (se 2 (by rfl) ⟨4576797, by rfl⟩ : syracuseStep 12204793 = 9153595) B9153595
theorem B9517823 : Blo 1879141 9517823 := bstep (se 1 (by rfl) ⟨7138367, by rfl⟩ : syracuseStep 9517823 = 14276735) B14276735
theorem B8035159 : Blo 1879141 8035159 := bstep (se 1 (by rfl) ⟨6026369, by rfl⟩ : syracuseStep 8035159 = 12052739) B12052739
theorem B10706003 : Blo 1879141 10706003 := bstep (se 1 (by rfl) ⟨8029502, by rfl⟩ : syracuseStep 10706003 = 16059005) B16059005
theorem B6773971 : Blo 1879141 6773971 := bstep (se 1 (by rfl) ⟨5080478, by rfl⟩ : syracuseStep 6773971 = 10160957) B10160957
theorem B5717243 : Blo 1879141 5717243 := bstep (se 1 (by rfl) ⟨4287932, by rfl⟩ : syracuseStep 5717243 = 8575865) B8575865
theorem B18079145 : Blo 1879141 18079145 := bstep (se 2 (by rfl) ⟨6779679, by rfl⟩ : syracuseStep 18079145 = 13559359) B13559359
theorem B125255155 : Blo 1879141 125255155 := bstep (se 1 (by rfl) ⟨93941366, by rfl⟩ : syracuseStep 125255155 = 187882733) B187882733
theorem B4759195 : Blo 1879141 4759195 := bstep (se 1 (by rfl) ⟨3569396, by rfl⟩ : syracuseStep 4759195 = 7138793) B7138793
theorem B91430693 : Blo 1879141 91430693 := bstep (se 4 (by rfl) ⟨8571627, by rfl⟩ : syracuseStep 91430693 = 17143255) B17143255
theorem B9519443 : Blo 1879141 9519443 := bstep (se 1 (by rfl) ⟨7139582, by rfl⟩ : syracuseStep 9519443 = 14279165) B14279165
theorem B16278047 : Blo 1879141 16278047 := bstep (se 1 (by rfl) ⟨12208535, by rfl⟩ : syracuseStep 16278047 = 24417071) B24417071
theorem B9650783 : Blo 1879141 9650783 := bstep (se 1 (by rfl) ⟨7238087, by rfl⟩ : syracuseStep 9650783 = 14476175) B14476175
theorem B2114239 : Blo 1879141 2114239 := bstep (se 1 (by rfl) ⟨1585679, by rfl⟩ : syracuseStep 2114239 = 3171359) B3171359
theorem B2818793 : Blo 1879141 2818793 := bstep (se 2 (by rfl) ⟨1057047, by rfl⟩ : syracuseStep 2818793 = 2114095) B2114095
theorem B2007871 : Blo 1879141 2007871 := bstep (se 1 (by rfl) ⟨1505903, by rfl⟩ : syracuseStep 2007871 = 3011807) B3011807
theorem B3916667 : Blo 1879141 3916667 := bstep (se 1 (by rfl) ⟨2937500, by rfl⟩ : syracuseStep 3916667 = 5875001) B5875001
theorem B3171271 : Blo 1879141 3171271 := bstep (se 1 (by rfl) ⟨2378453, by rfl⟩ : syracuseStep 3171271 = 4756907) B4756907
theorem B24101833 : Blo 1879141 24101833 := bstep (se 2 (by rfl) ⟨9038187, by rfl⟩ : syracuseStep 24101833 = 18076375) B18076375
theorem B2819099 : Blo 1879141 2819099 := bstep (se 1 (by rfl) ⟨2114324, by rfl⟩ : syracuseStep 2819099 = 4228649) B4228649
theorem B45753407 : Blo 1879141 45753407 := bstep (se 1 (by rfl) ⟨34315055, by rfl⟩ : syracuseStep 45753407 = 68630111) B68630111
theorem B34768055 : Blo 1879141 34768055 := bstep (se 1 (by rfl) ⟨26076041, by rfl⟩ : syracuseStep 34768055 = 52152083) B52152083
theorem B8029367 : Blo 1879141 8029367 := bstep (se 1 (by rfl) ⟨6022025, by rfl⟩ : syracuseStep 8029367 = 12044051) B12044051
theorem B83551421 : Blo 1879141 83551421 := bstep (se 3 (by rfl) ⟨15665891, by rfl⟩ : syracuseStep 83551421 = 31331783) B31331783
theorem B2114815 : Blo 1879141 2114815 := bstep (se 1 (by rfl) ⟨1586111, by rfl⟩ : syracuseStep 2114815 = 3172223) B3172223
theorem B2819369 : Blo 1879141 2819369 := bstep (se 2 (by rfl) ⟨1057263, by rfl⟩ : syracuseStep 2819369 = 2114527) B2114527
theorem B54199601 : Blo 1879141 54199601 := bstep (se 2 (by rfl) ⟨20324850, by rfl⟩ : syracuseStep 54199601 = 40649701) B40649701
theorem B2115175 : Blo 1879141 2115175 := bstep (se 1 (by rfl) ⟨1586381, by rfl⟩ : syracuseStep 2115175 = 3172763) B3172763
theorem B59500171 : Blo 1879141 59500171 := bstep (se 1 (by rfl) ⟨44625128, by rfl⟩ : syracuseStep 59500171 = 89250257) B89250257
theorem B4228991 : Blo 1879141 4228991 := bstep (se 1 (by rfl) ⟨3171743, by rfl⟩ : syracuseStep 4228991 = 6343487) B6343487
theorem B7137335 : Blo 1879141 7137335 := bstep (se 1 (by rfl) ⟨5353001, by rfl⟩ : syracuseStep 7137335 = 10706003) B10706003
theorem B4229279 : Blo 1879141 4229279 := bstep (se 1 (by rfl) ⟨3171959, by rfl⟩ : syracuseStep 4229279 = 6343919) B6343919
theorem B3811495 : Blo 1879141 3811495 := bstep (se 1 (by rfl) ⟨2858621, by rfl⟩ : syracuseStep 3811495 = 5717243) B5717243
theorem B12052763 : Blo 1879141 12052763 := bstep (se 1 (by rfl) ⟨9039572, by rfl⟩ : syracuseStep 12052763 = 18079145) B18079145
theorem B2820719 : Blo 1879141 2820719 := bstep (se 1 (by rfl) ⟨2115539, by rfl⟩ : syracuseStep 2820719 = 4231079) B4231079
theorem B13552271 : Blo 1879141 13552271 := bstep (se 1 (by rfl) ⟨10164203, by rfl⟩ : syracuseStep 13552271 = 20328407) B20328407
theorem B1879199 : Blo 1879141 1879199 := bstep (se 1 (by rfl) ⟨1409399, by rfl⟩ : syracuseStep 1879199 = 2818799) B2818799
theorem B4517095 : Blo 1879141 4517095 := bstep (se 1 (by rfl) ⟨3387821, by rfl⟩ : syracuseStep 4517095 = 6775643) B6775643
theorem B1879359 : Blo 1879141 1879359 := bstep (se 1 (by rfl) ⟨1409519, by rfl⟩ : syracuseStep 1879359 = 2819039) B2819039
theorem B396250775 : Blo 1879141 396250775 := bstep (se 1 (by rfl) ⟨297188081, by rfl⟩ : syracuseStep 396250775 = 594376163) B594376163
theorem B16273057 : Blo 1879141 16273057 := bstep (se 2 (by rfl) ⟨6102396, by rfl⟩ : syracuseStep 16273057 = 12204793) B12204793
theorem B7237673 : Blo 1879141 7237673 := bstep (se 2 (by rfl) ⟨2714127, by rfl⟩ : syracuseStep 7237673 = 5428255) B5428255
theorem B3567719 : Blo 1879141 3567719 := bstep (se 1 (by rfl) ⟨2675789, by rfl⟩ : syracuseStep 3567719 = 5351579) B5351579
theorem B4231295 : Blo 1879141 4231295 := bstep (se 1 (by rfl) ⟨3173471, by rfl⟩ : syracuseStep 4231295 = 6346943) B6346943
theorem B1880271 : Blo 1879141 1880271 := bstep (se 1 (by rfl) ⟨1410203, by rfl⟩ : syracuseStep 1880271 = 2820407) B2820407
theorem B9031961 : Blo 1879141 9031961 := bstep (se 2 (by rfl) ⟨3386985, by rfl⟩ : syracuseStep 9031961 = 6773971) B6773971
theorem B36122921 : Blo 1879141 36122921 := bstep (se 2 (by rfl) ⟨13546095, by rfl⟩ : syracuseStep 36122921 = 27092191) B27092191
theorem B4231583 : Blo 1879141 4231583 := bstep (se 1 (by rfl) ⟨3173687, by rfl⟩ : syracuseStep 4231583 = 6347375) B6347375
theorem B6345215 : Blo 1879141 6345215 := bstep (se 1 (by rfl) ⟨4758911, by rfl⟩ : syracuseStep 6345215 = 9517823) B9517823
theorem B167006873 : Blo 1879141 167006873 := bstep (se 2 (by rfl) ⟨62627577, by rfl⟩ : syracuseStep 167006873 = 125255155) B125255155
theorem B1880903 : Blo 1879141 1880903 := bstep (se 1 (by rfl) ⟨1410677, by rfl⟩ : syracuseStep 1880903 = 2821355) B2821355
theorem B1880935 : Blo 1879141 1880935 := bstep (se 1 (by rfl) ⟨1410701, by rfl⟩ : syracuseStep 1880935 = 2821403) B2821403
theorem B6345593 : Blo 1879141 6345593 := bstep (se 2 (by rfl) ⟨2379597, by rfl⟩ : syracuseStep 6345593 = 4759195) B4759195
theorem B60953795 : Blo 1879141 60953795 := bstep (se 1 (by rfl) ⟨45715346, by rfl⟩ : syracuseStep 60953795 = 91430693) B91430693
theorem B7140919 : Blo 1879141 7140919 := bstep (se 1 (by rfl) ⟨5355689, by rfl⟩ : syracuseStep 7140919 = 10711379) B10711379
theorem B2676763 : Blo 1879141 2676763 := bstep (se 1 (by rfl) ⟨2007572, by rfl⟩ : syracuseStep 2676763 = 4015145) B4015145
theorem B10713545 : Blo 1879141 10713545 := bstep (se 2 (by rfl) ⟨4017579, by rfl⟩ : syracuseStep 10713545 = 8035159) B8035159
theorem B6348671 : Blo 1879141 6348671 := bstep (se 1 (by rfl) ⟨4761503, by rfl⟩ : syracuseStep 6348671 = 9523007) B9523007
theorem B4825115 : Blo 1879141 4825115 := bstep (se 1 (by rfl) ⟨3618836, by rfl⟩ : syracuseStep 4825115 = 7237673) B7237673
theorem B6021307 : Blo 1879141 6021307 := bstep (se 1 (by rfl) ⟨4515980, by rfl⟩ : syracuseStep 6021307 = 9031961) B9031961
theorem B111337915 : Blo 1879141 111337915 := bstep (se 1 (by rfl) ⟨83503436, by rfl⟩ : syracuseStep 111337915 = 167006873) B167006873
theorem B2818985 : Blo 1879141 2818985 := bstep (se 2 (by rfl) ⟨1057119, by rfl⟩ : syracuseStep 2818985 = 2114239) B2114239
theorem B2819327 : Blo 1879141 2819327 := bstep (se 1 (by rfl) ⟨2114495, by rfl⟩ : syracuseStep 2819327 = 4228991) B4228991
theorem B4228361 : Blo 1879141 4228361 := bstep (se 2 (by rfl) ⟨1585635, by rfl⟩ : syracuseStep 4228361 = 3171271) B3171271
theorem B2819519 : Blo 1879141 2819519 := bstep (se 1 (by rfl) ⟨2114639, by rfl⟩ : syracuseStep 2819519 = 4229279) B4229279
theorem B6022793 : Blo 1879141 6022793 := bstep (se 2 (by rfl) ⟨2258547, by rfl⟩ : syracuseStep 6022793 = 4517095) B4517095
theorem B10708645 : Blo 1879141 10708645 := bstep (se 4 (by rfl) ⟨1003935, by rfl⟩ : syracuseStep 10708645 = 2007871) B2007871
theorem B2819753 : Blo 1879141 2819753 := bstep (se 2 (by rfl) ⟨1057407, by rfl⟩ : syracuseStep 2819753 = 2114815) B2114815
theorem B9521225 : Blo 1879141 9521225 := bstep (se 2 (by rfl) ⟨3570459, by rfl⟩ : syracuseStep 9521225 = 7140919) B7140919
theorem B2820233 : Blo 1879141 2820233 := bstep (se 2 (by rfl) ⟨1057587, by rfl⟩ : syracuseStep 2820233 = 2115175) B2115175
theorem B79333561 : Blo 1879141 79333561 := bstep (se 2 (by rfl) ⟨29750085, by rfl⟩ : syracuseStep 79333561 = 59500171) B59500171
theorem B2378479 : Blo 1879141 2378479 := bstep (se 1 (by rfl) ⟨1783859, by rfl⟩ : syracuseStep 2378479 = 3567719) B3567719
theorem B2820863 : Blo 1879141 2820863 := bstep (se 1 (by rfl) ⟨2115647, by rfl⟩ : syracuseStep 2820863 = 4231295) B4231295
theorem B5081993 : Blo 1879141 5081993 := bstep (se 2 (by rfl) ⟨1905747, by rfl⟩ : syracuseStep 5081993 = 3811495) B3811495
theorem B2821055 : Blo 1879141 2821055 := bstep (se 1 (by rfl) ⟨2115791, by rfl⟩ : syracuseStep 2821055 = 4231583) B4231583
theorem B4230143 : Blo 1879141 4230143 := bstep (se 1 (by rfl) ⟨3172607, by rfl⟩ : syracuseStep 4230143 = 6345215) B6345215
theorem B1879195 : Blo 1879141 1879195 := bstep (se 1 (by rfl) ⟨1409396, by rfl⟩ : syracuseStep 1879195 = 2818793) B2818793
theorem B4230395 : Blo 1879141 4230395 := bstep (se 1 (by rfl) ⟨3172796, by rfl⟩ : syracuseStep 4230395 = 6345593) B6345593
theorem B1879399 : Blo 1879141 1879399 := bstep (se 1 (by rfl) ⟨1409549, by rfl⟩ : syracuseStep 1879399 = 2819099) B2819099
theorem B30502271 : Blo 1879141 30502271 := bstep (se 1 (by rfl) ⟨22876703, by rfl⟩ : syracuseStep 30502271 = 45753407) B45753407
theorem B5352911 : Blo 1879141 5352911 := bstep (se 1 (by rfl) ⟨4014683, by rfl⟩ : syracuseStep 5352911 = 8029367) B8029367
theorem B55700947 : Blo 1879141 55700947 := bstep (se 1 (by rfl) ⟨41775710, by rfl⟩ : syracuseStep 55700947 = 83551421) B83551421
theorem B40635863 : Blo 1879141 40635863 := bstep (se 1 (by rfl) ⟨30476897, by rfl⟩ : syracuseStep 40635863 = 60953795) B60953795
theorem B1879579 : Blo 1879141 1879579 := bstep (se 1 (by rfl) ⟨1409684, by rfl⟩ : syracuseStep 1879579 = 2819369) B2819369
theorem B25735421 : Blo 1879141 25735421 := bstep (se 3 (by rfl) ⟨4825391, by rfl⟩ : syracuseStep 25735421 = 9650783) B9650783
theorem B1880479 : Blo 1879141 1880479 := bstep (se 1 (by rfl) ⟨1410359, by rfl⟩ : syracuseStep 1880479 = 2820719) B2820719
theorem B21697409 : Blo 1879141 21697409 := bstep (se 2 (by rfl) ⟨8136528, by rfl⟩ : syracuseStep 21697409 = 16273057) B16273057
theorem B4232447 : Blo 1879141 4232447 := bstep (se 1 (by rfl) ⟨3174335, by rfl⟩ : syracuseStep 4232447 = 6348671) B6348671
theorem B3569017 : Blo 1879141 3569017 := bstep (se 2 (by rfl) ⟨1338381, by rfl⟩ : syracuseStep 3569017 = 2676763) B2676763
theorem B24081947 : Blo 1879141 24081947 := bstep (se 1 (by rfl) ⟨18061460, by rfl⟩ : syracuseStep 24081947 = 36122921) B36122921
theorem B6346295 : Blo 1879141 6346295 := bstep (se 1 (by rfl) ⟨4759721, by rfl⟩ : syracuseStep 6346295 = 9519443) B9519443
theorem B10852031 : Blo 1879141 10852031 := bstep (se 1 (by rfl) ⟨8139023, by rfl⟩ : syracuseStep 10852031 = 16278047) B16278047
theorem B92714813 : Blo 1879141 92714813 := bstep (se 3 (by rfl) ⟨17384027, by rfl⟩ : syracuseStep 92714813 = 34768055) B34768055
theorem B2611111 : Blo 1879141 2611111 := bstep (se 1 (by rfl) ⟨1958333, by rfl⟩ : syracuseStep 2611111 = 3916667) B3916667
theorem B36133067 : Blo 1879141 36133067 := bstep (se 1 (by rfl) ⟨27099800, by rfl⟩ : syracuseStep 36133067 = 54199601) B54199601
theorem B32135777 : Blo 1879141 32135777 := bstep (se 2 (by rfl) ⟨12050916, by rfl⟩ : syracuseStep 32135777 = 24101833) B24101833
theorem B4758223 : Blo 1879141 4758223 := bstep (se 1 (by rfl) ⟨3568667, by rfl⟩ : syracuseStep 4758223 = 7137335) B7137335
theorem B8035175 : Blo 1879141 8035175 := bstep (se 1 (by rfl) ⟨6026381, by rfl⟩ : syracuseStep 8035175 = 12052763) B12052763
theorem B7142363 : Blo 1879141 7142363 := bstep (se 1 (by rfl) ⟨5356772, by rfl⟩ : syracuseStep 7142363 = 10713545) B10713545
theorem B9034847 : Blo 1879141 9034847 := bstep (se 1 (by rfl) ⟨6776135, by rfl⟩ : syracuseStep 9034847 = 13552271) B13552271
theorem B264167183 : Blo 1879141 264167183 := bstep (se 1 (by rfl) ⟨198125387, by rfl⟩ : syracuseStep 264167183 = 396250775) B396250775
theorem B8028409 : Blo 1879141 8028409 := bstep (se 2 (by rfl) ⟨3010653, by rfl⟩ : syracuseStep 8028409 = 6021307) B6021307
theorem B2818907 : Blo 1879141 2818907 := bstep (se 1 (by rfl) ⟨2114180, by rfl⟩ : syracuseStep 2818907 = 4228361) B4228361
theorem B3171305 : Blo 1879141 3171305 := bstep (se 2 (by rfl) ⟨1189239, by rfl⟩ : syracuseStep 3171305 = 2378479) B2378479
theorem B7234687 : Blo 1879141 7234687 := bstep (se 1 (by rfl) ⟨5426015, by rfl⟩ : syracuseStep 7234687 = 10852031) B10852031
theorem B61809875 : Blo 1879141 61809875 := bstep (se 1 (by rfl) ⟨46357406, by rfl⟩ : syracuseStep 61809875 = 92714813) B92714813
theorem B21423851 : Blo 1879141 21423851 := bstep (se 1 (by rfl) ⟨16067888, by rfl⟩ : syracuseStep 21423851 = 32135777) B32135777
theorem B4761575 : Blo 1879141 4761575 := bstep (se 1 (by rfl) ⟨3571181, by rfl⟩ : syracuseStep 4761575 = 7142363) B7142363
theorem B2820095 : Blo 1879141 2820095 := bstep (se 1 (by rfl) ⟨2115071, by rfl⟩ : syracuseStep 2820095 = 4230143) B4230143
theorem B6023231 : Blo 1879141 6023231 := bstep (se 1 (by rfl) ⟨4517423, by rfl⟩ : syracuseStep 6023231 = 9034847) B9034847
theorem B2820263 : Blo 1879141 2820263 := bstep (se 1 (by rfl) ⟨2115197, by rfl⟩ : syracuseStep 2820263 = 4230395) B4230395
theorem B20334847 : Blo 1879141 20334847 := bstep (se 1 (by rfl) ⟨15251135, by rfl⟩ : syracuseStep 20334847 = 30502271) B30502271
theorem B17156947 : Blo 1879141 17156947 := bstep (se 1 (by rfl) ⟨12867710, by rfl⟩ : syracuseStep 17156947 = 25735421) B25735421
theorem B105778081 : Blo 1879141 105778081 := bstep (se 2 (by rfl) ⟨39666780, by rfl⟩ : syracuseStep 105778081 = 79333561) B79333561
theorem B148450553 : Blo 1879141 148450553 := bstep (se 2 (by rfl) ⟨55668957, by rfl⟩ : syracuseStep 148450553 = 111337915) B111337915
theorem B1879323 : Blo 1879141 1879323 := bstep (se 1 (by rfl) ⟨1409492, by rfl⟩ : syracuseStep 1879323 = 2818985) B2818985
theorem B1879551 : Blo 1879141 1879551 := bstep (se 1 (by rfl) ⟨1409663, by rfl⟩ : syracuseStep 1879551 = 2819327) B2819327
theorem B2821631 : Blo 1879141 2821631 := bstep (se 1 (by rfl) ⟨2116223, by rfl⟩ : syracuseStep 2821631 = 4232447) B4232447
theorem B6344297 : Blo 1879141 6344297 := bstep (se 2 (by rfl) ⟨2379111, by rfl⟩ : syracuseStep 6344297 = 4758223) B4758223
theorem B1879679 : Blo 1879141 1879679 := bstep (se 1 (by rfl) ⟨1409759, by rfl⟩ : syracuseStep 1879679 = 2819519) B2819519
theorem B4230863 : Blo 1879141 4230863 := bstep (se 1 (by rfl) ⟨3173147, by rfl⟩ : syracuseStep 4230863 = 6346295) B6346295
theorem B1879835 : Blo 1879141 1879835 := bstep (se 1 (by rfl) ⟨1409876, by rfl⟩ : syracuseStep 1879835 = 2819753) B2819753
theorem B1880155 : Blo 1879141 1880155 := bstep (se 1 (by rfl) ⟨1410116, by rfl⟩ : syracuseStep 1880155 = 2820233) B2820233
theorem B24088711 : Blo 1879141 24088711 := bstep (se 1 (by rfl) ⟨18066533, by rfl⟩ : syracuseStep 24088711 = 36133067) B36133067
theorem B16060781 : Blo 1879141 16060781 := bstep (se 3 (by rfl) ⟨3011396, by rfl⟩ : syracuseStep 16060781 = 6022793) B6022793
theorem B1880575 : Blo 1879141 1880575 := bstep (se 1 (by rfl) ⟨1410431, by rfl⟩ : syracuseStep 1880575 = 2820863) B2820863
theorem B3387995 : Blo 1879141 3387995 := bstep (se 1 (by rfl) ⟨2540996, by rfl⟩ : syracuseStep 3387995 = 5081993) B5081993
theorem B1880703 : Blo 1879141 1880703 := bstep (se 1 (by rfl) ⟨1410527, by rfl⟩ : syracuseStep 1880703 = 2821055) B2821055
theorem B3568607 : Blo 1879141 3568607 := bstep (se 1 (by rfl) ⟨2676455, by rfl⟩ : syracuseStep 3568607 = 5352911) B5352911
theorem B3216743 : Blo 1879141 3216743 := bstep (se 1 (by rfl) ⟨2412557, by rfl⟩ : syracuseStep 3216743 = 4825115) B4825115
theorem B14464939 : Blo 1879141 14464939 := bstep (se 1 (by rfl) ⟨10848704, by rfl⟩ : syracuseStep 14464939 = 21697409) B21697409
theorem B16054631 : Blo 1879141 16054631 := bstep (se 1 (by rfl) ⟨12040973, by rfl⟩ : syracuseStep 16054631 = 24081947) B24081947
theorem B6347483 : Blo 1879141 6347483 := bstep (se 1 (by rfl) ⟨4760612, by rfl⟩ : syracuseStep 6347483 = 9521225) B9521225
theorem B4758689 : Blo 1879141 4758689 := bstep (se 2 (by rfl) ⟨1784508, by rfl⟩ : syracuseStep 4758689 = 3569017) B3569017
theorem B5356783 : Blo 1879141 5356783 := bstep (se 1 (by rfl) ⟨4017587, by rfl⟩ : syracuseStep 5356783 = 8035175) B8035175
theorem B74267929 : Blo 1879141 74267929 := bstep (se 2 (by rfl) ⟨27850473, by rfl⟩ : syracuseStep 74267929 = 55700947) B55700947
theorem B14278193 : Blo 1879141 14278193 := bstep (se 2 (by rfl) ⟨5354322, by rfl⟩ : syracuseStep 14278193 = 10708645) B10708645
theorem B27090575 : Blo 1879141 27090575 := bstep (se 1 (by rfl) ⟨20317931, by rfl⟩ : syracuseStep 27090575 = 40635863) B40635863
theorem B176111455 : Blo 1879141 176111455 := bstep (se 1 (by rfl) ⟨132083591, by rfl⟩ : syracuseStep 176111455 = 264167183) B264167183
theorem B3481481 : Blo 1879141 3481481 := bstep (se 2 (by rfl) ⟨1305555, by rfl⟩ : syracuseStep 3481481 = 2611111) B2611111
theorem B10707187 : Blo 1879141 10707187 := bstep (se 1 (by rfl) ⟨8030390, by rfl⟩ : syracuseStep 10707187 = 16060781) B16060781
theorem B2114203 : Blo 1879141 2114203 := bstep (se 1 (by rfl) ⟨1585652, by rfl⟩ : syracuseStep 2114203 = 3171305) B3171305
theorem B41206583 : Blo 1879141 41206583 := bstep (se 1 (by rfl) ⟨30904937, by rfl⟩ : syracuseStep 41206583 = 61809875) B61809875
theorem B4015487 : Blo 1879141 4015487 := bstep (se 1 (by rfl) ⟨3011615, by rfl⟩ : syracuseStep 4015487 = 6023231) B6023231
theorem B3172459 : Blo 1879141 3172459 := bstep (se 1 (by rfl) ⟨2379344, by rfl⟩ : syracuseStep 3172459 = 4758689) B4758689
theorem B9283949 : Blo 1879141 9283949 := bstep (se 3 (by rfl) ⟨1740740, by rfl⟩ : syracuseStep 9283949 = 3481481) B3481481
theorem B4229531 : Blo 1879141 4229531 := bstep (se 1 (by rfl) ⟨3172148, by rfl⟩ : syracuseStep 4229531 = 6344297) B6344297
theorem B2820575 : Blo 1879141 2820575 := bstep (se 1 (by rfl) ⟨2115431, by rfl⟩ : syracuseStep 2820575 = 4230863) B4230863
theorem B19286585 : Blo 1879141 19286585 := bstep (se 2 (by rfl) ⟨7232469, by rfl⟩ : syracuseStep 19286585 = 14464939) B14464939
theorem B1879271 : Blo 1879141 1879271 := bstep (se 1 (by rfl) ⟨1409453, by rfl⟩ : syracuseStep 1879271 = 2818907) B2818907
theorem B2379071 : Blo 1879141 2379071 := bstep (se 1 (by rfl) ⟨1784303, by rfl⟩ : syracuseStep 2379071 = 3568607) B3568607
theorem B22875929 : Blo 1879141 22875929 := bstep (se 2 (by rfl) ⟨8578473, by rfl⟩ : syracuseStep 22875929 = 17156947) B17156947
theorem B14282567 : Blo 1879141 14282567 := bstep (se 1 (by rfl) ⟨10711925, by rfl⟩ : syracuseStep 14282567 = 21423851) B21423851
theorem B3174383 : Blo 1879141 3174383 := bstep (se 1 (by rfl) ⟨2380787, by rfl⟩ : syracuseStep 3174383 = 4761575) B4761575
theorem B1880063 : Blo 1879141 1880063 := bstep (se 1 (by rfl) ⟨1410047, by rfl⟩ : syracuseStep 1880063 = 2820095) B2820095
theorem B1880175 : Blo 1879141 1880175 := bstep (se 1 (by rfl) ⟨1410131, by rfl⟩ : syracuseStep 1880175 = 2820263) B2820263
theorem B9646249 : Blo 1879141 9646249 := bstep (se 2 (by rfl) ⟨3617343, by rfl⟩ : syracuseStep 9646249 = 7234687) B7234687
theorem B10703087 : Blo 1879141 10703087 := bstep (se 1 (by rfl) ⟨8027315, by rfl⟩ : syracuseStep 10703087 = 16054631) B16054631
theorem B4231655 : Blo 1879141 4231655 := bstep (se 1 (by rfl) ⟨3173741, by rfl⟩ : syracuseStep 4231655 = 6347483) B6347483
theorem B1881087 : Blo 1879141 1881087 := bstep (se 1 (by rfl) ⟨1410815, by rfl⟩ : syracuseStep 1881087 = 2821631) B2821631
theorem B18060383 : Blo 1879141 18060383 := bstep (se 1 (by rfl) ⟨13545287, by rfl⟩ : syracuseStep 18060383 = 27090575) B27090575
theorem B32118281 : Blo 1879141 32118281 := bstep (se 2 (by rfl) ⟨12044355, by rfl⟩ : syracuseStep 32118281 = 24088711) B24088711
theorem B10704545 : Blo 1879141 10704545 := bstep (se 2 (by rfl) ⟨4014204, by rfl⟩ : syracuseStep 10704545 = 8028409) B8028409
theorem B27113129 : Blo 1879141 27113129 := bstep (se 2 (by rfl) ⟨10167423, by rfl⟩ : syracuseStep 27113129 = 20334847) B20334847
theorem B2258663 : Blo 1879141 2258663 := bstep (se 1 (by rfl) ⟨1693997, by rfl⟩ : syracuseStep 2258663 = 3387995) B3387995
theorem B2144495 : Blo 1879141 2144495 := bstep (se 1 (by rfl) ⟨1608371, by rfl⟩ : syracuseStep 2144495 = 3216743) B3216743
theorem B7142377 : Blo 1879141 7142377 := bstep (se 2 (by rfl) ⟨2678391, by rfl⟩ : syracuseStep 7142377 = 5356783) B5356783
theorem B99023905 : Blo 1879141 99023905 := bstep (se 2 (by rfl) ⟨37133964, by rfl⟩ : syracuseStep 99023905 = 74267929) B74267929
theorem B98967035 : Blo 1879141 98967035 := bstep (se 1 (by rfl) ⟨74225276, by rfl⟩ : syracuseStep 98967035 = 148450553) B148450553
theorem B564149765 : Blo 1879141 564149765 := bstep (se 4 (by rfl) ⟨52889040, by rfl⟩ : syracuseStep 564149765 = 105778081) B105778081
theorem B9518795 : Blo 1879141 9518795 := bstep (se 1 (by rfl) ⟨7139096, by rfl⟩ : syracuseStep 9518795 = 14278193) B14278193
theorem B234815273 : Blo 1879141 234815273 := bstep (se 2 (by rfl) ⟨88055727, by rfl⟩ : syracuseStep 234815273 = 176111455) B176111455
theorem B7135391 : Blo 1879141 7135391 := bstep (se 1 (by rfl) ⟨5351543, by rfl⟩ : syracuseStep 7135391 = 10703087) B10703087
theorem B12861665 : Blo 1879141 12861665 := bstep (se 2 (by rfl) ⟨4823124, by rfl⟩ : syracuseStep 12861665 = 9646249) B9646249
theorem B5718653 : Blo 1879141 5718653 := bstep (se 3 (by rfl) ⟨1072247, by rfl⟩ : syracuseStep 5718653 = 2144495) B2144495
theorem B2818937 : Blo 1879141 2818937 := bstep (se 2 (by rfl) ⟨1057101, by rfl⟩ : syracuseStep 2818937 = 2114203) B2114203
theorem B7136363 : Blo 1879141 7136363 := bstep (se 1 (by rfl) ⟨5352272, by rfl⟩ : syracuseStep 7136363 = 10704545) B10704545
theorem B132031873 : Blo 1879141 132031873 := bstep (se 2 (by rfl) ⟨49511952, by rfl⟩ : syracuseStep 132031873 = 99023905) B99023905
theorem B2819687 : Blo 1879141 2819687 := bstep (se 1 (by rfl) ⟨2114765, by rfl⟩ : syracuseStep 2819687 = 4229531) B4229531
theorem B6023101 : Blo 1879141 6023101 := bstep (se 3 (by rfl) ⟨1129331, by rfl⟩ : syracuseStep 6023101 = 2258663) B2258663
theorem B156543515 : Blo 1879141 156543515 := bstep (se 1 (by rfl) ⟨117407636, by rfl⟩ : syracuseStep 156543515 = 234815273) B234815273
theorem B9521711 : Blo 1879141 9521711 := bstep (se 1 (by rfl) ⟨7141283, by rfl⟩ : syracuseStep 9521711 = 14282567) B14282567
theorem B2116255 : Blo 1879141 2116255 := bstep (se 1 (by rfl) ⟨1587191, by rfl⟩ : syracuseStep 2116255 = 3174383) B3174383
theorem B4229945 : Blo 1879141 4229945 := bstep (se 2 (by rfl) ⟨1586229, by rfl⟩ : syracuseStep 4229945 = 3172459) B3172459
theorem B2821103 : Blo 1879141 2821103 := bstep (se 1 (by rfl) ⟨2115827, by rfl⟩ : syracuseStep 2821103 = 4231655) B4231655
theorem B27471055 : Blo 1879141 27471055 := bstep (se 1 (by rfl) ⟨20603291, by rfl⟩ : syracuseStep 27471055 = 41206583) B41206583
theorem B6344189 : Blo 1879141 6344189 := bstep (se 3 (by rfl) ⟨1189535, by rfl⟩ : syracuseStep 6344189 = 2379071) B2379071
theorem B18075419 : Blo 1879141 18075419 := bstep (se 1 (by rfl) ⟨13556564, by rfl⟩ : syracuseStep 18075419 = 27113129) B27113129
theorem B9523169 : Blo 1879141 9523169 := bstep (se 2 (by rfl) ⟨3571188, by rfl⟩ : syracuseStep 9523169 = 7142377) B7142377
theorem B6189299 : Blo 1879141 6189299 := bstep (se 1 (by rfl) ⟨4641974, by rfl⟩ : syracuseStep 6189299 = 9283949) B9283949
theorem B1880383 : Blo 1879141 1880383 := bstep (se 1 (by rfl) ⟨1410287, by rfl⟩ : syracuseStep 1880383 = 2820575) B2820575
theorem B12857723 : Blo 1879141 12857723 := bstep (se 1 (by rfl) ⟨9643292, by rfl⟩ : syracuseStep 12857723 = 19286585) B19286585
theorem B376099843 : Blo 1879141 376099843 := bstep (se 1 (by rfl) ⟨282074882, by rfl⟩ : syracuseStep 376099843 = 564149765) B564149765
theorem B6345863 : Blo 1879141 6345863 := bstep (se 1 (by rfl) ⟨4759397, by rfl⟩ : syracuseStep 6345863 = 9518795) B9518795
theorem B15250619 : Blo 1879141 15250619 := bstep (se 1 (by rfl) ⟨11437964, by rfl⟩ : syracuseStep 15250619 = 22875929) B22875929
theorem B14276249 : Blo 1879141 14276249 := bstep (se 2 (by rfl) ⟨5353593, by rfl⟩ : syracuseStep 14276249 = 10707187) B10707187
theorem B12040255 : Blo 1879141 12040255 := bstep (se 1 (by rfl) ⟨9030191, by rfl⟩ : syracuseStep 12040255 = 18060383) B18060383
theorem B2676991 : Blo 1879141 2676991 := bstep (se 1 (by rfl) ⟨2007743, by rfl⟩ : syracuseStep 2676991 = 4015487) B4015487
theorem B21412187 : Blo 1879141 21412187 := bstep (se 1 (by rfl) ⟨16059140, by rfl⟩ : syracuseStep 21412187 = 32118281) B32118281
theorem B263912093 : Blo 1879141 263912093 := bstep (se 3 (by rfl) ⟨49483517, by rfl⟩ : syracuseStep 263912093 = 98967035) B98967035
theorem B10167079 : Blo 1879141 10167079 := bstep (se 1 (by rfl) ⟨7625309, by rfl⟩ : syracuseStep 10167079 = 15250619) B15250619
theorem B501466457 : Blo 1879141 501466457 := bstep (se 2 (by rfl) ⟨188049921, by rfl⟩ : syracuseStep 501466457 = 376099843) B376099843
theorem B36628073 : Blo 1879141 36628073 := bstep (se 2 (by rfl) ⟨13735527, by rfl⟩ : syracuseStep 36628073 = 27471055) B27471055
theorem B175941395 : Blo 1879141 175941395 := bstep (se 1 (by rfl) ⟨131956046, by rfl⟩ : syracuseStep 175941395 = 263912093) B263912093
theorem B2819963 : Blo 1879141 2819963 := bstep (se 1 (by rfl) ⟨2114972, by rfl⟩ : syracuseStep 2819963 = 4229945) B4229945
theorem B4229459 : Blo 1879141 4229459 := bstep (se 1 (by rfl) ⟨3172094, by rfl⟩ : syracuseStep 4229459 = 6344189) B6344189
theorem B8030801 : Blo 1879141 8030801 := bstep (se 2 (by rfl) ⟨3011550, by rfl⟩ : syracuseStep 8030801 = 6023101) B6023101
theorem B8571815 : Blo 1879141 8571815 := bstep (se 1 (by rfl) ⟨6428861, by rfl⟩ : syracuseStep 8571815 = 12857723) B12857723
theorem B3812435 : Blo 1879141 3812435 := bstep (se 1 (by rfl) ⟨2859326, by rfl⟩ : syracuseStep 3812435 = 5718653) B5718653
theorem B1879291 : Blo 1879141 1879291 := bstep (se 1 (by rfl) ⟨1409468, by rfl⟩ : syracuseStep 1879291 = 2818937) B2818937
theorem B4230575 : Blo 1879141 4230575 := bstep (se 1 (by rfl) ⟨3172931, by rfl⟩ : syracuseStep 4230575 = 6345863) B6345863
theorem B2821673 : Blo 1879141 2821673 := bstep (se 2 (by rfl) ⟨1058127, by rfl⟩ : syracuseStep 2821673 = 2116255) B2116255
theorem B1879791 : Blo 1879141 1879791 := bstep (se 1 (by rfl) ⟨1409843, by rfl⟩ : syracuseStep 1879791 = 2819687) B2819687
theorem B14274791 : Blo 1879141 14274791 := bstep (se 1 (by rfl) ⟨10706093, by rfl⟩ : syracuseStep 14274791 = 21412187) B21412187
theorem B104362343 : Blo 1879141 104362343 := bstep (se 1 (by rfl) ⟨78271757, by rfl⟩ : syracuseStep 104362343 = 156543515) B156543515
theorem B176042497 : Blo 1879141 176042497 := bstep (se 2 (by rfl) ⟨66015936, by rfl⟩ : syracuseStep 176042497 = 132031873) B132031873
theorem B1880735 : Blo 1879141 1880735 := bstep (se 1 (by rfl) ⟨1410551, by rfl⟩ : syracuseStep 1880735 = 2821103) B2821103
theorem B16053673 : Blo 1879141 16053673 := bstep (se 2 (by rfl) ⟨6020127, by rfl⟩ : syracuseStep 16053673 = 12040255) B12040255
theorem B4756927 : Blo 1879141 4756927 := bstep (se 1 (by rfl) ⟨3567695, by rfl⟩ : syracuseStep 4756927 = 7135391) B7135391
theorem B8574443 : Blo 1879141 8574443 := bstep (se 1 (by rfl) ⟨6430832, by rfl⟩ : syracuseStep 8574443 = 12861665) B12861665
theorem B4126199 : Blo 1879141 4126199 := bstep (se 1 (by rfl) ⟨3094649, by rfl⟩ : syracuseStep 4126199 = 6189299) B6189299
theorem B3569321 : Blo 1879141 3569321 := bstep (se 2 (by rfl) ⟨1338495, by rfl⟩ : syracuseStep 3569321 = 2676991) B2676991
theorem B4757575 : Blo 1879141 4757575 := bstep (se 1 (by rfl) ⟨3568181, by rfl⟩ : syracuseStep 4757575 = 7136363) B7136363
theorem B9517499 : Blo 1879141 9517499 := bstep (se 1 (by rfl) ⟨7138124, by rfl⟩ : syracuseStep 9517499 = 14276249) B14276249
theorem B6347807 : Blo 1879141 6347807 := bstep (se 1 (by rfl) ⟨4760855, by rfl⟩ : syracuseStep 6347807 = 9521711) B9521711
theorem B12050279 : Blo 1879141 12050279 := bstep (se 1 (by rfl) ⟨9037709, by rfl⟩ : syracuseStep 12050279 = 18075419) B18075419
theorem B6348779 : Blo 1879141 6348779 := bstep (se 1 (by rfl) ⟨4761584, by rfl⟩ : syracuseStep 6348779 = 9523169) B9523169
theorem B69574895 : Blo 1879141 69574895 := bstep (se 1 (by rfl) ⟨52181171, by rfl⟩ : syracuseStep 69574895 = 104362343) B104362343
theorem B117294263 : Blo 1879141 117294263 := bstep (se 1 (by rfl) ⟨87970697, by rfl⟩ : syracuseStep 117294263 = 175941395) B175941395
theorem B2819639 : Blo 1879141 2819639 := bstep (se 1 (by rfl) ⟨2114729, by rfl⟩ : syracuseStep 2819639 = 4229459) B4229459
theorem B6342569 : Blo 1879141 6342569 := bstep (se 2 (by rfl) ⟨2378463, by rfl⟩ : syracuseStep 6342569 = 4756927) B4756927
theorem B2541623 : Blo 1879141 2541623 := bstep (se 1 (by rfl) ⟨1906217, by rfl⟩ : syracuseStep 2541623 = 3812435) B3812435
theorem B2820383 : Blo 1879141 2820383 := bstep (se 1 (by rfl) ⟨2115287, by rfl⟩ : syracuseStep 2820383 = 4230575) B4230575
theorem B6343433 : Blo 1879141 6343433 := bstep (se 2 (by rfl) ⟨2378787, by rfl⟩ : syracuseStep 6343433 = 4757575) B4757575
theorem B334310971 : Blo 1879141 334310971 := bstep (se 1 (by rfl) ⟨250733228, by rfl⟩ : syracuseStep 334310971 = 501466457) B501466457
theorem B2379547 : Blo 1879141 2379547 := bstep (se 1 (by rfl) ⟨1784660, by rfl⟩ : syracuseStep 2379547 = 3569321) B3569321
theorem B1879975 : Blo 1879141 1879975 := bstep (se 1 (by rfl) ⟨1409981, by rfl⟩ : syracuseStep 1879975 = 2819963) B2819963
theorem B6344999 : Blo 1879141 6344999 := bstep (se 1 (by rfl) ⟨4758749, by rfl⟩ : syracuseStep 6344999 = 9517499) B9517499
theorem B5353867 : Blo 1879141 5353867 := bstep (se 1 (by rfl) ⟨4015400, by rfl⟩ : syracuseStep 5353867 = 8030801) B8030801
theorem B5714543 : Blo 1879141 5714543 := bstep (se 1 (by rfl) ⟨4285907, by rfl⟩ : syracuseStep 5714543 = 8571815) B8571815
theorem B4231871 : Blo 1879141 4231871 := bstep (se 1 (by rfl) ⟨3173903, by rfl⟩ : syracuseStep 4231871 = 6347807) B6347807
theorem B1881115 : Blo 1879141 1881115 := bstep (se 1 (by rfl) ⟨1410836, by rfl⟩ : syracuseStep 1881115 = 2821673) B2821673
theorem B8033519 : Blo 1879141 8033519 := bstep (se 1 (by rfl) ⟨6025139, by rfl⟩ : syracuseStep 8033519 = 12050279) B12050279
theorem B44012789 : Blo 1879141 44012789 := bstep (se 5 (by rfl) ⟨2063099, by rfl⟩ : syracuseStep 44012789 = 4126199) B4126199
theorem B4232519 : Blo 1879141 4232519 := bstep (se 1 (by rfl) ⟨3174389, by rfl⟩ : syracuseStep 4232519 = 6348779) B6348779
theorem B9516527 : Blo 1879141 9516527 := bstep (se 1 (by rfl) ⟨7137395, by rfl⟩ : syracuseStep 9516527 = 14274791) B14274791
theorem B234723329 : Blo 1879141 234723329 := bstep (se 2 (by rfl) ⟨88021248, by rfl⟩ : syracuseStep 234723329 = 176042497) B176042497
theorem B5716295 : Blo 1879141 5716295 := bstep (se 1 (by rfl) ⟨4287221, by rfl⟩ : syracuseStep 5716295 = 8574443) B8574443
theorem B13556105 : Blo 1879141 13556105 := bstep (se 2 (by rfl) ⟨5083539, by rfl⟩ : syracuseStep 13556105 = 10167079) B10167079
theorem B24418715 : Blo 1879141 24418715 := bstep (se 1 (by rfl) ⟨18314036, by rfl⟩ : syracuseStep 24418715 = 36628073) B36628073
theorem B21404897 : Blo 1879141 21404897 := bstep (se 2 (by rfl) ⟨8026836, by rfl⟩ : syracuseStep 21404897 = 16053673) B16053673
theorem B46383263 : Blo 1879141 46383263 := bstep (se 1 (by rfl) ⟨34787447, by rfl⟩ : syracuseStep 46383263 = 69574895) B69574895
theorem B3809695 : Blo 1879141 3809695 := bstep (se 1 (by rfl) ⟨2857271, by rfl⟩ : syracuseStep 3809695 = 5714543) B5714543
theorem B4228379 : Blo 1879141 4228379 := bstep (se 1 (by rfl) ⟨3171284, by rfl⟩ : syracuseStep 4228379 = 6342569) B6342569
theorem B3810863 : Blo 1879141 3810863 := bstep (se 1 (by rfl) ⟨2858147, by rfl⟩ : syracuseStep 3810863 = 5716295) B5716295
theorem B9037403 : Blo 1879141 9037403 := bstep (se 1 (by rfl) ⟨6778052, by rfl⟩ : syracuseStep 9037403 = 13556105) B13556105
theorem B260466293 : Blo 1879141 260466293 := bstep (se 5 (by rfl) ⟨12209357, by rfl⟩ : syracuseStep 260466293 = 24418715) B24418715
theorem B4228955 : Blo 1879141 4228955 := bstep (se 1 (by rfl) ⟨3171716, by rfl⟩ : syracuseStep 4228955 = 6343433) B6343433
theorem B3172729 : Blo 1879141 3172729 := bstep (se 2 (by rfl) ⟨1189773, by rfl⟩ : syracuseStep 3172729 = 2379547) B2379547
theorem B4229999 : Blo 1879141 4229999 := bstep (se 1 (by rfl) ⟨3172499, by rfl⟩ : syracuseStep 4229999 = 6344999) B6344999
theorem B2821247 : Blo 1879141 2821247 := bstep (se 1 (by rfl) ⟨2115935, by rfl⟩ : syracuseStep 2821247 = 4231871) B4231871
theorem B7138489 : Blo 1879141 7138489 := bstep (se 2 (by rfl) ⟨2676933, by rfl⟩ : syracuseStep 7138489 = 5353867) B5353867
theorem B27110645 : Blo 1879141 27110645 := bstep (se 5 (by rfl) ⟨1270811, by rfl⟩ : syracuseStep 27110645 = 2541623) B2541623
theorem B78196175 : Blo 1879141 78196175 := bstep (se 1 (by rfl) ⟨58647131, by rfl⟩ : syracuseStep 78196175 = 117294263) B117294263
theorem B2821679 : Blo 1879141 2821679 := bstep (se 1 (by rfl) ⟨2116259, by rfl⟩ : syracuseStep 2821679 = 4232519) B4232519
theorem B6344351 : Blo 1879141 6344351 := bstep (se 1 (by rfl) ⟨4758263, by rfl⟩ : syracuseStep 6344351 = 9516527) B9516527
theorem B1879759 : Blo 1879141 1879759 := bstep (se 1 (by rfl) ⟨1409819, by rfl⟩ : syracuseStep 1879759 = 2819639) B2819639
theorem B1880255 : Blo 1879141 1880255 := bstep (se 1 (by rfl) ⟨1410191, by rfl⟩ : syracuseStep 1880255 = 2820383) B2820383
theorem B445747961 : Blo 1879141 445747961 := bstep (se 2 (by rfl) ⟨167155485, by rfl⟩ : syracuseStep 445747961 = 334310971) B334310971
theorem B5355679 : Blo 1879141 5355679 := bstep (se 1 (by rfl) ⟨4016759, by rfl⟩ : syracuseStep 5355679 = 8033519) B8033519
theorem B29341859 : Blo 1879141 29341859 := bstep (se 1 (by rfl) ⟨22006394, by rfl⟩ : syracuseStep 29341859 = 44012789) B44012789
theorem B156482219 : Blo 1879141 156482219 := bstep (se 1 (by rfl) ⟨117361664, by rfl⟩ : syracuseStep 156482219 = 234723329) B234723329
theorem B14269931 : Blo 1879141 14269931 := bstep (se 1 (by rfl) ⟨10702448, by rfl⟩ : syracuseStep 14269931 = 21404897) B21404897
theorem B297165307 : Blo 1879141 297165307 := bstep (se 1 (by rfl) ⟨222873980, by rfl⟩ : syracuseStep 297165307 = 445747961) B445747961
theorem B5079593 : Blo 1879141 5079593 := bstep (se 2 (by rfl) ⟨1904847, by rfl⟩ : syracuseStep 5079593 = 3809695) B3809695
theorem B2818919 : Blo 1879141 2818919 := bstep (se 1 (by rfl) ⟨2114189, by rfl⟩ : syracuseStep 2818919 = 4228379) B4228379
theorem B2540575 : Blo 1879141 2540575 := bstep (se 1 (by rfl) ⟨1905431, by rfl⟩ : syracuseStep 2540575 = 3810863) B3810863
theorem B2819303 : Blo 1879141 2819303 := bstep (se 1 (by rfl) ⟨2114477, by rfl⟩ : syracuseStep 2819303 = 4228955) B4228955
theorem B694576781 : Blo 1879141 694576781 := bstep (se 3 (by rfl) ⟨130233146, by rfl⟩ : syracuseStep 694576781 = 260466293) B260466293
theorem B2819999 : Blo 1879141 2819999 := bstep (se 1 (by rfl) ⟨2114999, by rfl⟩ : syracuseStep 2819999 = 4229999) B4229999
theorem B18073763 : Blo 1879141 18073763 := bstep (se 1 (by rfl) ⟨13555322, by rfl⟩ : syracuseStep 18073763 = 27110645) B27110645
theorem B9513287 : Blo 1879141 9513287 := bstep (se 1 (by rfl) ⟨7134965, by rfl⟩ : syracuseStep 9513287 = 14269931) B14269931
theorem B4229567 : Blo 1879141 4229567 := bstep (se 1 (by rfl) ⟨3172175, by rfl⟩ : syracuseStep 4229567 = 6344351) B6344351
theorem B78244957 : Blo 1879141 78244957 := bstep (se 3 (by rfl) ⟨14670929, by rfl⟩ : syracuseStep 78244957 = 29341859) B29341859
theorem B4230305 : Blo 1879141 4230305 := bstep (se 2 (by rfl) ⟨1586364, by rfl⟩ : syracuseStep 4230305 = 3172729) B3172729
theorem B6024935 : Blo 1879141 6024935 := bstep (se 1 (by rfl) ⟨4518701, by rfl⟩ : syracuseStep 6024935 = 9037403) B9037403
theorem B104321479 : Blo 1879141 104321479 := bstep (se 1 (by rfl) ⟨78241109, by rfl⟩ : syracuseStep 104321479 = 156482219) B156482219
theorem B1880831 : Blo 1879141 1880831 := bstep (se 1 (by rfl) ⟨1410623, by rfl⟩ : syracuseStep 1880831 = 2821247) B2821247
theorem B52130783 : Blo 1879141 52130783 := bstep (se 1 (by rfl) ⟨39098087, by rfl⟩ : syracuseStep 52130783 = 78196175) B78196175
theorem B1881119 : Blo 1879141 1881119 := bstep (se 1 (by rfl) ⟨1410839, by rfl⟩ : syracuseStep 1881119 = 2821679) B2821679
theorem B30922175 : Blo 1879141 30922175 := bstep (se 1 (by rfl) ⟨23191631, by rfl⟩ : syracuseStep 30922175 = 46383263) B46383263
theorem B7140905 : Blo 1879141 7140905 := bstep (se 2 (by rfl) ⟨2677839, by rfl⟩ : syracuseStep 7140905 = 5355679) B5355679
theorem B9517985 : Blo 1879141 9517985 := bstep (se 2 (by rfl) ⟨3569244, by rfl⟩ : syracuseStep 9517985 = 7138489) B7138489
theorem B4760603 : Blo 1879141 4760603 := bstep (se 1 (by rfl) ⟨3570452, by rfl⟩ : syracuseStep 4760603 = 7140905) B7140905
theorem B6342191 : Blo 1879141 6342191 := bstep (se 1 (by rfl) ⟨4756643, by rfl⟩ : syracuseStep 6342191 = 9513287) B9513287
theorem B2819711 : Blo 1879141 2819711 := bstep (se 1 (by rfl) ⟨2114783, by rfl⟩ : syracuseStep 2819711 = 4229567) B4229567
theorem B2820203 : Blo 1879141 2820203 := bstep (se 1 (by rfl) ⟨2115152, by rfl⟩ : syracuseStep 2820203 = 4230305) B4230305
theorem B4016623 : Blo 1879141 4016623 := bstep (se 1 (by rfl) ⟨3012467, by rfl⟩ : syracuseStep 4016623 = 6024935) B6024935
theorem B3386395 : Blo 1879141 3386395 := bstep (se 1 (by rfl) ⟨2539796, by rfl⟩ : syracuseStep 3386395 = 5079593) B5079593
theorem B1879279 : Blo 1879141 1879279 := bstep (se 1 (by rfl) ⟨1409459, by rfl⟩ : syracuseStep 1879279 = 2818919) B2818919
theorem B139095305 : Blo 1879141 139095305 := bstep (se 2 (by rfl) ⟨52160739, by rfl⟩ : syracuseStep 139095305 = 104321479) B104321479
theorem B34753855 : Blo 1879141 34753855 := bstep (se 1 (by rfl) ⟨26065391, by rfl⟩ : syracuseStep 34753855 = 52130783) B52130783
theorem B1879535 : Blo 1879141 1879535 := bstep (se 1 (by rfl) ⟨1409651, by rfl⟩ : syracuseStep 1879535 = 2819303) B2819303
theorem B20614783 : Blo 1879141 20614783 := bstep (se 1 (by rfl) ⟨15461087, by rfl⟩ : syracuseStep 20614783 = 30922175) B30922175
theorem B1879999 : Blo 1879141 1879999 := bstep (se 1 (by rfl) ⟨1409999, by rfl⟩ : syracuseStep 1879999 = 2819999) B2819999
theorem B3387433 : Blo 1879141 3387433 := bstep (se 2 (by rfl) ⟨1270287, by rfl⟩ : syracuseStep 3387433 = 2540575) B2540575
theorem B6345323 : Blo 1879141 6345323 := bstep (se 1 (by rfl) ⟨4758992, by rfl⟩ : syracuseStep 6345323 = 9517985) B9517985
theorem B417306437 : Blo 1879141 417306437 := bstep (se 4 (by rfl) ⟨39122478, by rfl⟩ : syracuseStep 417306437 = 78244957) B78244957
theorem B396220409 : Blo 1879141 396220409 := bstep (se 2 (by rfl) ⟨148582653, by rfl⟩ : syracuseStep 396220409 = 297165307) B297165307
theorem B463051187 : Blo 1879141 463051187 := bstep (se 1 (by rfl) ⟨347288390, by rfl⟩ : syracuseStep 463051187 = 694576781) B694576781
theorem B12049175 : Blo 1879141 12049175 := bstep (se 1 (by rfl) ⟨9036881, by rfl⟩ : syracuseStep 12049175 = 18073763) B18073763
theorem B4228127 : Blo 1879141 4228127 := bstep (se 1 (by rfl) ⟨3171095, by rfl⟩ : syracuseStep 4228127 = 6342191) B6342191
theorem B4515193 : Blo 1879141 4515193 := bstep (se 2 (by rfl) ⟨1693197, by rfl⟩ : syracuseStep 4515193 = 3386395) B3386395
theorem B308700791 : Blo 1879141 308700791 := bstep (se 1 (by rfl) ⟨231525593, by rfl⟩ : syracuseStep 308700791 = 463051187) B463051187
theorem B27486377 : Blo 1879141 27486377 := bstep (se 2 (by rfl) ⟨10307391, by rfl⟩ : syracuseStep 27486377 = 20614783) B20614783
theorem B4516577 : Blo 1879141 4516577 := bstep (se 2 (by rfl) ⟨1693716, by rfl⟩ : syracuseStep 4516577 = 3387433) B3387433
theorem B4230215 : Blo 1879141 4230215 := bstep (se 1 (by rfl) ⟨3172661, by rfl⟩ : syracuseStep 4230215 = 6345323) B6345323
theorem B3173735 : Blo 1879141 3173735 := bstep (se 1 (by rfl) ⟨2380301, by rfl⟩ : syracuseStep 3173735 = 4760603) B4760603
theorem B1879807 : Blo 1879141 1879807 := bstep (se 1 (by rfl) ⟨1409855, by rfl⟩ : syracuseStep 1879807 = 2819711) B2819711
theorem B278204291 : Blo 1879141 278204291 := bstep (se 1 (by rfl) ⟨208653218, by rfl⟩ : syracuseStep 278204291 = 417306437) B417306437
theorem B264146939 : Blo 1879141 264146939 := bstep (se 1 (by rfl) ⟨198110204, by rfl⟩ : syracuseStep 264146939 = 396220409) B396220409
theorem B1880135 : Blo 1879141 1880135 := bstep (se 1 (by rfl) ⟨1410101, by rfl⟩ : syracuseStep 1880135 = 2820203) B2820203
theorem B46338473 : Blo 1879141 46338473 := bstep (se 2 (by rfl) ⟨17376927, by rfl⟩ : syracuseStep 46338473 = 34753855) B34753855
theorem B8032783 : Blo 1879141 8032783 := bstep (se 1 (by rfl) ⟨6024587, by rfl⟩ : syracuseStep 8032783 = 12049175) B12049175
theorem B92730203 : Blo 1879141 92730203 := bstep (se 1 (by rfl) ⟨69547652, by rfl⟩ : syracuseStep 92730203 = 139095305) B139095305
theorem B5355497 : Blo 1879141 5355497 := bstep (se 2 (by rfl) ⟨2008311, by rfl⟩ : syracuseStep 5355497 = 4016623) B4016623
theorem B30892315 : Blo 1879141 30892315 := bstep (se 1 (by rfl) ⟨23169236, by rfl⟩ : syracuseStep 30892315 = 46338473) B46338473
theorem B2818751 : Blo 1879141 2818751 := bstep (se 1 (by rfl) ⟨2114063, by rfl⟩ : syracuseStep 2818751 = 4228127) B4228127
theorem B205800527 : Blo 1879141 205800527 := bstep (se 1 (by rfl) ⟨154350395, by rfl⟩ : syracuseStep 205800527 = 308700791) B308700791
theorem B2820143 : Blo 1879141 2820143 := bstep (se 1 (by rfl) ⟨2115107, by rfl⟩ : syracuseStep 2820143 = 4230215) B4230215
theorem B2115823 : Blo 1879141 2115823 := bstep (se 1 (by rfl) ⟨1586867, by rfl⟩ : syracuseStep 2115823 = 3173735) B3173735
theorem B185469527 : Blo 1879141 185469527 := bstep (se 1 (by rfl) ⟨139102145, by rfl⟩ : syracuseStep 185469527 = 278204291) B278204291
theorem B176097959 : Blo 1879141 176097959 := bstep (se 1 (by rfl) ⟨132073469, by rfl⟩ : syracuseStep 176097959 = 264146939) B264146939
theorem B61820135 : Blo 1879141 61820135 := bstep (se 1 (by rfl) ⟨46365101, by rfl⟩ : syracuseStep 61820135 = 92730203) B92730203
theorem B10710377 : Blo 1879141 10710377 := bstep (se 2 (by rfl) ⟨4016391, by rfl⟩ : syracuseStep 10710377 = 8032783) B8032783
theorem B3011051 : Blo 1879141 3011051 := bstep (se 1 (by rfl) ⟨2258288, by rfl⟩ : syracuseStep 3011051 = 4516577) B4516577
theorem B3570331 : Blo 1879141 3570331 := bstep (se 1 (by rfl) ⟨2677748, by rfl⟩ : syracuseStep 3570331 = 5355497) B5355497
theorem B18324251 : Blo 1879141 18324251 := bstep (se 1 (by rfl) ⟨13743188, by rfl⟩ : syracuseStep 18324251 = 27486377) B27486377
theorem B6020257 : Blo 1879141 6020257 := bstep (se 2 (by rfl) ⟨2257596, by rfl⟩ : syracuseStep 6020257 = 4515193) B4515193
theorem B41189753 : Blo 1879141 41189753 := bstep (se 2 (by rfl) ⟨15446157, by rfl⟩ : syracuseStep 41189753 = 30892315) B30892315
theorem B137200351 : Blo 1879141 137200351 := bstep (se 1 (by rfl) ⟨102900263, by rfl⟩ : syracuseStep 137200351 = 205800527) B205800527
theorem B4760441 : Blo 1879141 4760441 := bstep (se 2 (by rfl) ⟨1785165, by rfl⟩ : syracuseStep 4760441 = 3570331) B3570331
theorem B8029469 : Blo 1879141 8029469 := bstep (se 3 (by rfl) ⟨1505525, by rfl⟩ : syracuseStep 8029469 = 3011051) B3011051
theorem B12216167 : Blo 1879141 12216167 := bstep (se 1 (by rfl) ⟨9162125, by rfl⟩ : syracuseStep 12216167 = 18324251) B18324251
theorem B2821097 : Blo 1879141 2821097 := bstep (se 2 (by rfl) ⟨1057911, by rfl⟩ : syracuseStep 2821097 = 2115823) B2115823
theorem B1879167 : Blo 1879141 1879167 := bstep (se 1 (by rfl) ⟨1409375, by rfl⟩ : syracuseStep 1879167 = 2818751) B2818751
theorem B1880095 : Blo 1879141 1880095 := bstep (se 1 (by rfl) ⟨1410071, by rfl⟩ : syracuseStep 1880095 = 2820143) B2820143
theorem B123646351 : Blo 1879141 123646351 := bstep (se 1 (by rfl) ⟨92734763, by rfl⟩ : syracuseStep 123646351 = 185469527) B185469527
theorem B7140251 : Blo 1879141 7140251 := bstep (se 1 (by rfl) ⟨5355188, by rfl⟩ : syracuseStep 7140251 = 10710377) B10710377
theorem B8027009 : Blo 1879141 8027009 := bstep (se 2 (by rfl) ⟨3010128, by rfl⟩ : syracuseStep 8027009 = 6020257) B6020257
theorem B117398639 : Blo 1879141 117398639 := bstep (se 1 (by rfl) ⟨88048979, by rfl⟩ : syracuseStep 117398639 = 176097959) B176097959
theorem B41213423 : Blo 1879141 41213423 := bstep (se 1 (by rfl) ⟨30910067, by rfl⟩ : syracuseStep 41213423 = 61820135) B61820135
theorem B4760167 : Blo 1879141 4760167 := bstep (se 1 (by rfl) ⟨3570125, by rfl⟩ : syracuseStep 4760167 = 7140251) B7140251
theorem B109839341 : Blo 1879141 109839341 := bstep (se 3 (by rfl) ⟨20594876, by rfl⟩ : syracuseStep 109839341 = 41189753) B41189753
theorem B8144111 : Blo 1879141 8144111 := bstep (se 1 (by rfl) ⟨6108083, by rfl⟩ : syracuseStep 8144111 = 12216167) B12216167
theorem B5351339 : Blo 1879141 5351339 := bstep (se 1 (by rfl) ⟨4013504, by rfl⟩ : syracuseStep 5351339 = 8027009) B8027009
theorem B3173627 : Blo 1879141 3173627 := bstep (se 1 (by rfl) ⟨2380220, by rfl⟩ : syracuseStep 3173627 = 4760441) B4760441
theorem B5352979 : Blo 1879141 5352979 := bstep (se 1 (by rfl) ⟨4014734, by rfl⟩ : syracuseStep 5352979 = 8029469) B8029469
theorem B1880731 : Blo 1879141 1880731 := bstep (se 1 (by rfl) ⟨1410548, by rfl⟩ : syracuseStep 1880731 = 2821097) B2821097
theorem B164861801 : Blo 1879141 164861801 := bstep (se 2 (by rfl) ⟨61823175, by rfl⟩ : syracuseStep 164861801 = 123646351) B123646351
theorem B182933801 : Blo 1879141 182933801 := bstep (se 2 (by rfl) ⟨68600175, by rfl⟩ : syracuseStep 182933801 = 137200351) B137200351
theorem B78265759 : Blo 1879141 78265759 := bstep (se 1 (by rfl) ⟨58699319, by rfl⟩ : syracuseStep 78265759 = 117398639) B117398639
theorem B27475615 : Blo 1879141 27475615 := bstep (se 1 (by rfl) ⟨20606711, by rfl⟩ : syracuseStep 27475615 = 41213423) B41213423
theorem B21717629 : Blo 1879141 21717629 := bstep (se 3 (by rfl) ⟨4072055, by rfl⟩ : syracuseStep 21717629 = 8144111) B8144111
theorem B121955867 : Blo 1879141 121955867 := bstep (se 1 (by rfl) ⟨91466900, by rfl⟩ : syracuseStep 121955867 = 182933801) B182933801
theorem B7137305 : Blo 1879141 7137305 := bstep (se 2 (by rfl) ⟨2676489, by rfl⟩ : syracuseStep 7137305 = 5352979) B5352979
theorem B2115751 : Blo 1879141 2115751 := bstep (se 1 (by rfl) ⟨1586813, by rfl⟩ : syracuseStep 2115751 = 3173627) B3173627
theorem B109907867 : Blo 1879141 109907867 := bstep (se 1 (by rfl) ⟨82430900, by rfl⟩ : syracuseStep 109907867 = 164861801) B164861801
theorem B3567559 : Blo 1879141 3567559 := bstep (se 1 (by rfl) ⟨2675669, by rfl⟩ : syracuseStep 3567559 = 5351339) B5351339
theorem B104354345 : Blo 1879141 104354345 := bstep (se 2 (by rfl) ⟨39132879, by rfl⟩ : syracuseStep 104354345 = 78265759) B78265759
theorem B6346889 : Blo 1879141 6346889 := bstep (se 2 (by rfl) ⟨2380083, by rfl⟩ : syracuseStep 6346889 = 4760167) B4760167
theorem B36634153 : Blo 1879141 36634153 := bstep (se 2 (by rfl) ⟨13737807, by rfl⟩ : syracuseStep 36634153 = 27475615) B27475615
theorem B292904909 : Blo 1879141 292904909 := bstep (se 3 (by rfl) ⟨54919670, by rfl⟩ : syracuseStep 292904909 = 109839341) B109839341
theorem B73271911 : Blo 1879141 73271911 := bstep (se 1 (by rfl) ⟨54953933, by rfl⟩ : syracuseStep 73271911 = 109907867) B109907867
theorem B2821001 : Blo 1879141 2821001 := bstep (se 2 (by rfl) ⟨1057875, by rfl⟩ : syracuseStep 2821001 = 2115751) B2115751
theorem B69569563 : Blo 1879141 69569563 := bstep (se 1 (by rfl) ⟨52177172, by rfl⟩ : syracuseStep 69569563 = 104354345) B104354345
theorem B14478419 : Blo 1879141 14478419 := bstep (se 1 (by rfl) ⟨10858814, by rfl⟩ : syracuseStep 14478419 = 21717629) B21717629
theorem B4231259 : Blo 1879141 4231259 := bstep (se 1 (by rfl) ⟨3173444, by rfl⟩ : syracuseStep 4231259 = 6346889) B6346889
theorem B48845537 : Blo 1879141 48845537 := bstep (se 2 (by rfl) ⟨18317076, by rfl⟩ : syracuseStep 48845537 = 36634153) B36634153
theorem B4756745 : Blo 1879141 4756745 := bstep (se 2 (by rfl) ⟨1783779, by rfl⟩ : syracuseStep 4756745 = 3567559) B3567559
theorem B195269939 : Blo 1879141 195269939 := bstep (se 1 (by rfl) ⟨146452454, by rfl⟩ : syracuseStep 195269939 = 292904909) B292904909
theorem B81303911 : Blo 1879141 81303911 := bstep (se 1 (by rfl) ⟨60977933, by rfl⟩ : syracuseStep 81303911 = 121955867) B121955867
theorem B4758203 : Blo 1879141 4758203 := bstep (se 1 (by rfl) ⟨3568652, by rfl⟩ : syracuseStep 4758203 = 7137305) B7137305
theorem B32563691 : Blo 1879141 32563691 := bstep (se 1 (by rfl) ⟨24422768, by rfl⟩ : syracuseStep 32563691 = 48845537) B48845537
theorem B3171163 : Blo 1879141 3171163 := bstep (se 1 (by rfl) ⟨2378372, by rfl⟩ : syracuseStep 3171163 = 4756745) B4756745
theorem B130179959 : Blo 1879141 130179959 := bstep (se 1 (by rfl) ⟨97634969, by rfl⟩ : syracuseStep 130179959 = 195269939) B195269939
theorem B92759417 : Blo 1879141 92759417 := bstep (se 2 (by rfl) ⟨34784781, by rfl⟩ : syracuseStep 92759417 = 69569563) B69569563
theorem B3172135 : Blo 1879141 3172135 := bstep (se 1 (by rfl) ⟨2379101, by rfl⟩ : syracuseStep 3172135 = 4758203) B4758203
theorem B9652279 : Blo 1879141 9652279 := bstep (se 1 (by rfl) ⟨7239209, by rfl⟩ : syracuseStep 9652279 = 14478419) B14478419
theorem B2820839 : Blo 1879141 2820839 := bstep (se 1 (by rfl) ⟨2115629, by rfl⟩ : syracuseStep 2820839 = 4231259) B4231259
theorem B54202607 : Blo 1879141 54202607 := bstep (se 1 (by rfl) ⟨40651955, by rfl⟩ : syracuseStep 54202607 = 81303911) B81303911
theorem B1880667 : Blo 1879141 1880667 := bstep (se 1 (by rfl) ⟨1410500, by rfl⟩ : syracuseStep 1880667 = 2821001) B2821001
theorem B97695881 : Blo 1879141 97695881 := bstep (se 2 (by rfl) ⟨36635955, by rfl⟩ : syracuseStep 97695881 = 73271911) B73271911
theorem B12869705 : Blo 1879141 12869705 := bstep (se 2 (by rfl) ⟨4826139, by rfl⟩ : syracuseStep 12869705 = 9652279) B9652279
theorem B36135071 : Blo 1879141 36135071 := bstep (se 1 (by rfl) ⟨27101303, by rfl⟩ : syracuseStep 36135071 = 54202607) B54202607
theorem B21709127 : Blo 1879141 21709127 := bstep (se 1 (by rfl) ⟨16281845, by rfl⟩ : syracuseStep 21709127 = 32563691) B32563691
theorem B86786639 : Blo 1879141 86786639 := bstep (se 1 (by rfl) ⟨65089979, by rfl⟩ : syracuseStep 86786639 = 130179959) B130179959
theorem B4228217 : Blo 1879141 4228217 := bstep (se 2 (by rfl) ⟨1585581, by rfl⟩ : syracuseStep 4228217 = 3171163) B3171163
theorem B4229513 : Blo 1879141 4229513 := bstep (se 2 (by rfl) ⟨1586067, by rfl⟩ : syracuseStep 4229513 = 3172135) B3172135
theorem B65130587 : Blo 1879141 65130587 := bstep (se 1 (by rfl) ⟨48847940, by rfl⟩ : syracuseStep 65130587 = 97695881) B97695881
theorem B1880559 : Blo 1879141 1880559 := bstep (se 1 (by rfl) ⟨1410419, by rfl⟩ : syracuseStep 1880559 = 2820839) B2820839
theorem B61839611 : Blo 1879141 61839611 := bstep (se 1 (by rfl) ⟨46379708, by rfl⟩ : syracuseStep 61839611 = 92759417) B92759417
theorem B2818811 : Blo 1879141 2818811 := bstep (se 1 (by rfl) ⟨2114108, by rfl⟩ : syracuseStep 2818811 = 4228217) B4228217
theorem B2819675 : Blo 1879141 2819675 := bstep (se 1 (by rfl) ⟨2114756, by rfl⟩ : syracuseStep 2819675 = 4229513) B4229513
theorem B8579803 : Blo 1879141 8579803 := bstep (se 1 (by rfl) ⟨6434852, by rfl⟩ : syracuseStep 8579803 = 12869705) B12869705
theorem B43420391 : Blo 1879141 43420391 := bstep (se 1 (by rfl) ⟨32565293, by rfl⟩ : syracuseStep 43420391 = 65130587) B65130587
theorem B41226407 : Blo 1879141 41226407 := bstep (se 1 (by rfl) ⟨30919805, by rfl⟩ : syracuseStep 41226407 = 61839611) B61839611
theorem B24090047 : Blo 1879141 24090047 := bstep (se 1 (by rfl) ⟨18067535, by rfl⟩ : syracuseStep 24090047 = 36135071) B36135071
theorem B14472751 : Blo 1879141 14472751 := bstep (se 1 (by rfl) ⟨10854563, by rfl⟩ : syracuseStep 14472751 = 21709127) B21709127
theorem B57857759 : Blo 1879141 57857759 := bstep (se 1 (by rfl) ⟨43393319, by rfl⟩ : syracuseStep 57857759 = 86786639) B86786639
theorem B27484271 : Blo 1879141 27484271 := bstep (se 1 (by rfl) ⟨20613203, by rfl⟩ : syracuseStep 27484271 = 41226407) B41226407
theorem B1879207 : Blo 1879141 1879207 := bstep (se 1 (by rfl) ⟨1409405, by rfl⟩ : syracuseStep 1879207 = 2818811) B2818811
theorem B11439737 : Blo 1879141 11439737 := bstep (se 2 (by rfl) ⟨4289901, by rfl⟩ : syracuseStep 11439737 = 8579803) B8579803
theorem B16060031 : Blo 1879141 16060031 := bstep (se 1 (by rfl) ⟨12045023, by rfl⟩ : syracuseStep 16060031 = 24090047) B24090047
theorem B1879783 : Blo 1879141 1879783 := bstep (se 1 (by rfl) ⟨1409837, by rfl⟩ : syracuseStep 1879783 = 2819675) B2819675
theorem B38571839 : Blo 1879141 38571839 := bstep (se 1 (by rfl) ⟨28928879, by rfl⟩ : syracuseStep 38571839 = 57857759) B57857759
theorem B28946927 : Blo 1879141 28946927 := bstep (se 1 (by rfl) ⟨21710195, by rfl⟩ : syracuseStep 28946927 = 43420391) B43420391
theorem B19297001 : Blo 1879141 19297001 := bstep (se 2 (by rfl) ⟨7236375, by rfl⟩ : syracuseStep 19297001 = 14472751) B14472751
theorem B12864667 : Blo 1879141 12864667 := bstep (se 1 (by rfl) ⟨9648500, by rfl⟩ : syracuseStep 12864667 = 19297001) B19297001
theorem B18322847 : Blo 1879141 18322847 := bstep (se 1 (by rfl) ⟨13742135, by rfl⟩ : syracuseStep 18322847 = 27484271) B27484271
theorem B77191805 : Blo 1879141 77191805 := bstep (se 3 (by rfl) ⟨14473463, by rfl⟩ : syracuseStep 77191805 = 28946927) B28946927
theorem B7626491 : Blo 1879141 7626491 := bstep (se 1 (by rfl) ⟨5719868, by rfl⟩ : syracuseStep 7626491 = 11439737) B11439737
theorem B10706687 : Blo 1879141 10706687 := bstep (se 1 (by rfl) ⟨8030015, by rfl⟩ : syracuseStep 10706687 = 16060031) B16060031
theorem B25714559 : Blo 1879141 25714559 := bstep (se 1 (by rfl) ⟨19285919, by rfl⟩ : syracuseStep 25714559 = 38571839) B38571839
theorem B12215231 : Blo 1879141 12215231 := bstep (se 1 (by rfl) ⟨9161423, by rfl⟩ : syracuseStep 12215231 = 18322847) B18322847
theorem B7137791 : Blo 1879141 7137791 := bstep (se 1 (by rfl) ⟨5353343, by rfl⟩ : syracuseStep 7137791 = 10706687) B10706687
theorem B205844813 : Blo 1879141 205844813 := bstep (se 3 (by rfl) ⟨38595902, by rfl⟩ : syracuseStep 205844813 = 77191805) B77191805
theorem B5084327 : Blo 1879141 5084327 := bstep (se 1 (by rfl) ⟨3813245, by rfl⟩ : syracuseStep 5084327 = 7626491) B7626491
theorem B17143039 : Blo 1879141 17143039 := bstep (se 1 (by rfl) ⟨12857279, by rfl⟩ : syracuseStep 17143039 = 25714559) B25714559
theorem B17152889 : Blo 1879141 17152889 := bstep (se 2 (by rfl) ⟨6432333, by rfl⟩ : syracuseStep 17152889 = 12864667) B12864667
theorem B13558205 : Blo 1879141 13558205 := bstep (se 3 (by rfl) ⟨2542163, by rfl⟩ : syracuseStep 13558205 = 5084327) B5084327
theorem B8143487 : Blo 1879141 8143487 := bstep (se 1 (by rfl) ⟨6107615, by rfl⟩ : syracuseStep 8143487 = 12215231) B12215231
theorem B22857385 : Blo 1879141 22857385 := bstep (se 2 (by rfl) ⟨8571519, by rfl⟩ : syracuseStep 22857385 = 17143039) B17143039
theorem B45741037 : Blo 1879141 45741037 := bstep (se 3 (by rfl) ⟨8576444, by rfl⟩ : syracuseStep 45741037 = 17152889) B17152889
theorem B137229875 : Blo 1879141 137229875 := bstep (se 1 (by rfl) ⟨102922406, by rfl⟩ : syracuseStep 137229875 = 205844813) B205844813
theorem B4758527 : Blo 1879141 4758527 := bstep (se 1 (by rfl) ⟨3568895, by rfl⟩ : syracuseStep 4758527 = 7137791) B7137791
theorem B3172351 : Blo 1879141 3172351 := bstep (se 1 (by rfl) ⟨2379263, by rfl⟩ : syracuseStep 3172351 = 4758527) B4758527
theorem B30476513 : Blo 1879141 30476513 := bstep (se 2 (by rfl) ⟨11428692, by rfl⟩ : syracuseStep 30476513 = 22857385) B22857385
theorem B9038803 : Blo 1879141 9038803 := bstep (se 1 (by rfl) ⟨6779102, by rfl⟩ : syracuseStep 9038803 = 13558205) B13558205
theorem B5428991 : Blo 1879141 5428991 := bstep (se 1 (by rfl) ⟨4071743, by rfl⟩ : syracuseStep 5428991 = 8143487) B8143487
theorem B91486583 : Blo 1879141 91486583 := bstep (se 1 (by rfl) ⟨68614937, by rfl⟩ : syracuseStep 91486583 = 137229875) B137229875
theorem B60988049 : Blo 1879141 60988049 := bstep (se 2 (by rfl) ⟨22870518, by rfl⟩ : syracuseStep 60988049 = 45741037) B45741037
theorem B12051737 : Blo 1879141 12051737 := bstep (se 2 (by rfl) ⟨4519401, by rfl⟩ : syracuseStep 12051737 = 9038803) B9038803
theorem B20317675 : Blo 1879141 20317675 := bstep (se 1 (by rfl) ⟨15238256, by rfl⟩ : syracuseStep 20317675 = 30476513) B30476513
theorem B60991055 : Blo 1879141 60991055 := bstep (se 1 (by rfl) ⟨45743291, by rfl⟩ : syracuseStep 60991055 = 91486583) B91486583
theorem B40658699 : Blo 1879141 40658699 := bstep (se 1 (by rfl) ⟨30494024, by rfl⟩ : syracuseStep 40658699 = 60988049) B60988049
theorem B14477309 : Blo 1879141 14477309 := bstep (se 3 (by rfl) ⟨2714495, by rfl⟩ : syracuseStep 14477309 = 5428991) B5428991
theorem B4229801 : Blo 1879141 4229801 := bstep (se 2 (by rfl) ⟨1586175, by rfl⟩ : syracuseStep 4229801 = 3172351) B3172351
theorem B9651539 : Blo 1879141 9651539 := bstep (se 1 (by rfl) ⟨7238654, by rfl⟩ : syracuseStep 9651539 = 14477309) B14477309
theorem B2819867 : Blo 1879141 2819867 := bstep (se 1 (by rfl) ⟨2114900, by rfl⟩ : syracuseStep 2819867 = 4229801) B4229801
theorem B40660703 : Blo 1879141 40660703 := bstep (se 1 (by rfl) ⟨30495527, by rfl⟩ : syracuseStep 40660703 = 60991055) B60991055
theorem B8034491 : Blo 1879141 8034491 := bstep (se 1 (by rfl) ⟨6025868, by rfl⟩ : syracuseStep 8034491 = 12051737) B12051737
theorem B27105799 : Blo 1879141 27105799 := bstep (se 1 (by rfl) ⟨20329349, by rfl⟩ : syracuseStep 27105799 = 40658699) B40658699
theorem B27090233 : Blo 1879141 27090233 := bstep (se 2 (by rfl) ⟨10158837, by rfl⟩ : syracuseStep 27090233 = 20317675) B20317675
theorem B21425309 : Blo 1879141 21425309 := bstep (se 3 (by rfl) ⟨4017245, by rfl⟩ : syracuseStep 21425309 = 8034491) B8034491
theorem B6434359 : Blo 1879141 6434359 := bstep (se 1 (by rfl) ⟨4825769, by rfl⟩ : syracuseStep 6434359 = 9651539) B9651539
theorem B1879911 : Blo 1879141 1879911 := bstep (se 1 (by rfl) ⟨1409933, by rfl⟩ : syracuseStep 1879911 = 2819867) B2819867
theorem B18060155 : Blo 1879141 18060155 := bstep (se 1 (by rfl) ⟨13545116, by rfl⟩ : syracuseStep 18060155 = 27090233) B27090233
theorem B36141065 : Blo 1879141 36141065 := bstep (se 2 (by rfl) ⟨13552899, by rfl⟩ : syracuseStep 36141065 = 27105799) B27105799
theorem B27107135 : Blo 1879141 27107135 := bstep (se 1 (by rfl) ⟨20330351, by rfl⟩ : syracuseStep 27107135 = 40660703) B40660703
theorem B137266325 : Blo 1879141 137266325 := bstep (se 6 (by rfl) ⟨3217179, by rfl⟩ : syracuseStep 137266325 = 6434359) B6434359
theorem B24094043 : Blo 1879141 24094043 := bstep (se 1 (by rfl) ⟨18070532, by rfl⟩ : syracuseStep 24094043 = 36141065) B36141065
theorem B14283539 : Blo 1879141 14283539 := bstep (se 1 (by rfl) ⟨10712654, by rfl⟩ : syracuseStep 14283539 = 21425309) B21425309
theorem B12040103 : Blo 1879141 12040103 := bstep (se 1 (by rfl) ⟨9030077, by rfl⟩ : syracuseStep 12040103 = 18060155) B18060155
theorem B18071423 : Blo 1879141 18071423 := bstep (se 1 (by rfl) ⟨13553567, by rfl⟩ : syracuseStep 18071423 = 27107135) B27107135
theorem B9522359 : Blo 1879141 9522359 := bstep (se 1 (by rfl) ⟨7141769, by rfl⟩ : syracuseStep 9522359 = 14283539) B14283539
theorem B12047615 : Blo 1879141 12047615 := bstep (se 1 (by rfl) ⟨9035711, by rfl⟩ : syracuseStep 12047615 = 18071423) B18071423
theorem B91510883 : Blo 1879141 91510883 := bstep (se 1 (by rfl) ⟨68633162, by rfl⟩ : syracuseStep 91510883 = 137266325) B137266325
theorem B16062695 : Blo 1879141 16062695 := bstep (se 1 (by rfl) ⟨12047021, by rfl⟩ : syracuseStep 16062695 = 24094043) B24094043
theorem B8026735 : Blo 1879141 8026735 := bstep (se 1 (by rfl) ⟨6020051, by rfl⟩ : syracuseStep 8026735 = 12040103) B12040103
theorem B61007255 : Blo 1879141 61007255 := bstep (se 1 (by rfl) ⟨45755441, by rfl⟩ : syracuseStep 61007255 = 91510883) B91510883
theorem B10708463 : Blo 1879141 10708463 := bstep (se 1 (by rfl) ⟨8031347, by rfl⟩ : syracuseStep 10708463 = 16062695) B16062695
theorem B10702313 : Blo 1879141 10702313 := bstep (se 2 (by rfl) ⟨4013367, by rfl⟩ : syracuseStep 10702313 = 8026735) B8026735
theorem B8031743 : Blo 1879141 8031743 := bstep (se 1 (by rfl) ⟨6023807, by rfl⟩ : syracuseStep 8031743 = 12047615) B12047615
theorem B6348239 : Blo 1879141 6348239 := bstep (se 1 (by rfl) ⟨4761179, by rfl⟩ : syracuseStep 6348239 = 9522359) B9522359
theorem B7138975 : Blo 1879141 7138975 := bstep (se 1 (by rfl) ⟨5354231, by rfl⟩ : syracuseStep 7138975 = 10708463) B10708463
theorem B4232159 : Blo 1879141 4232159 := bstep (se 1 (by rfl) ⟨3174119, by rfl⟩ : syracuseStep 4232159 = 6348239) B6348239
theorem B5354495 : Blo 1879141 5354495 := bstep (se 1 (by rfl) ⟨4015871, by rfl⟩ : syracuseStep 5354495 = 8031743) B8031743
theorem B40671503 : Blo 1879141 40671503 := bstep (se 1 (by rfl) ⟨30503627, by rfl⟩ : syracuseStep 40671503 = 61007255) B61007255
theorem B7134875 : Blo 1879141 7134875 := bstep (se 1 (by rfl) ⟨5351156, by rfl⟩ : syracuseStep 7134875 = 10702313) B10702313
theorem B2821439 : Blo 1879141 2821439 := bstep (se 1 (by rfl) ⟨2116079, by rfl⟩ : syracuseStep 2821439 = 4232159) B4232159
theorem B4756583 : Blo 1879141 4756583 := bstep (se 1 (by rfl) ⟨3567437, by rfl⟩ : syracuseStep 4756583 = 7134875) B7134875
theorem B3569663 : Blo 1879141 3569663 := bstep (se 1 (by rfl) ⟨2677247, by rfl⟩ : syracuseStep 3569663 = 5354495) B5354495
theorem B27114335 : Blo 1879141 27114335 := bstep (se 1 (by rfl) ⟨20335751, by rfl⟩ : syracuseStep 27114335 = 40671503) B40671503
theorem B9518633 : Blo 1879141 9518633 := bstep (se 2 (by rfl) ⟨3569487, by rfl⟩ : syracuseStep 9518633 = 7138975) B7138975
theorem B3171055 : Blo 1879141 3171055 := bstep (se 1 (by rfl) ⟨2378291, by rfl⟩ : syracuseStep 3171055 = 4756583) B4756583
theorem B2379775 : Blo 1879141 2379775 := bstep (se 1 (by rfl) ⟨1784831, by rfl⟩ : syracuseStep 2379775 = 3569663) B3569663
theorem B18076223 : Blo 1879141 18076223 := bstep (se 1 (by rfl) ⟨13557167, by rfl⟩ : syracuseStep 18076223 = 27114335) B27114335
theorem B1880959 : Blo 1879141 1880959 := bstep (se 1 (by rfl) ⟨1410719, by rfl⟩ : syracuseStep 1880959 = 2821439) B2821439
theorem B6345755 : Blo 1879141 6345755 := bstep (se 1 (by rfl) ⟨4759316, by rfl⟩ : syracuseStep 6345755 = 9518633) B9518633
theorem B12050815 : Blo 1879141 12050815 := bstep (se 1 (by rfl) ⟨9038111, by rfl⟩ : syracuseStep 12050815 = 18076223) B18076223
theorem B4228073 : Blo 1879141 4228073 := bstep (se 2 (by rfl) ⟨1585527, by rfl⟩ : syracuseStep 4228073 = 3171055) B3171055
theorem B3173033 : Blo 1879141 3173033 := bstep (se 2 (by rfl) ⟨1189887, by rfl⟩ : syracuseStep 3173033 = 2379775) B2379775
theorem B4230503 : Blo 1879141 4230503 := bstep (se 1 (by rfl) ⟨3172877, by rfl⟩ : syracuseStep 4230503 = 6345755) B6345755
theorem B2818715 : Blo 1879141 2818715 := bstep (se 1 (by rfl) ⟨2114036, by rfl⟩ : syracuseStep 2818715 = 4228073) B4228073
theorem B2115355 : Blo 1879141 2115355 := bstep (se 1 (by rfl) ⟨1586516, by rfl⟩ : syracuseStep 2115355 = 3173033) B3173033
theorem B2820335 : Blo 1879141 2820335 := bstep (se 1 (by rfl) ⟨2115251, by rfl⟩ : syracuseStep 2820335 = 4230503) B4230503
theorem B16067753 : Blo 1879141 16067753 := bstep (se 2 (by rfl) ⟨6025407, by rfl⟩ : syracuseStep 16067753 = 12050815) B12050815
theorem B2820473 : Blo 1879141 2820473 := bstep (se 2 (by rfl) ⟨1057677, by rfl⟩ : syracuseStep 2820473 = 2115355) B2115355
theorem B1879143 : Blo 1879141 1879143 := bstep (se 1 (by rfl) ⟨1409357, by rfl⟩ : syracuseStep 1879143 = 2818715) B2818715
theorem B1880223 : Blo 1879141 1880223 := bstep (se 1 (by rfl) ⟨1410167, by rfl⟩ : syracuseStep 1880223 = 2820335) B2820335
theorem B10711835 : Blo 1879141 10711835 := bstep (se 1 (by rfl) ⟨8033876, by rfl⟩ : syracuseStep 10711835 = 16067753) B16067753
theorem B1880315 : Blo 1879141 1880315 := bstep (se 1 (by rfl) ⟨1410236, by rfl⟩ : syracuseStep 1880315 = 2820473) B2820473
theorem B7141223 : Blo 1879141 7141223 := bstep (se 1 (by rfl) ⟨5355917, by rfl⟩ : syracuseStep 7141223 = 10711835) B10711835
theorem B4760815 : Blo 1879141 4760815 := bstep (se 1 (by rfl) ⟨3570611, by rfl⟩ : syracuseStep 4760815 = 7141223) B7141223
theorem B6347753 : Blo 1879141 6347753 := bstep (se 2 (by rfl) ⟨2380407, by rfl⟩ : syracuseStep 6347753 = 4760815) B4760815
theorem B4231835 : Blo 1879141 4231835 := bstep (se 1 (by rfl) ⟨3173876, by rfl⟩ : syracuseStep 4231835 = 6347753) B6347753
theorem B2821223 : Blo 1879141 2821223 := bstep (se 1 (by rfl) ⟨2115917, by rfl⟩ : syracuseStep 2821223 = 4231835) B4231835
theorem B1880815 : Blo 1879141 1880815 := bstep (se 1 (by rfl) ⟨1410611, by rfl⟩ : syracuseStep 1880815 = 2821223) B2821223

theorem C0 (j : ℕ) (h1 : 469785 ≤ j) (h2 : j ≤ 470284) : Blo 1879141 (4 * j + 3) := by
  interval_cases j
  · exact B1879143
  · exact B1879147
  · exact B1879151
  · exact B1879155
  · exact B1879159
  · exact B1879163
  · exact B1879167
  · exact B1879171
  · exact B1879175
  · exact B1879179
  · exact B1879183
  · exact B1879187
  · exact B1879191
  · exact B1879195
  · exact B1879199
  · exact B1879203
  · exact B1879207
  · exact B1879211
  · exact B1879215
  · exact B1879219
  · exact B1879223
  · exact B1879227
  · exact B1879231
  · exact B1879235
  · exact B1879239
  · exact B1879243
  · exact B1879247
  · exact B1879251
  · exact B1879255
  · exact B1879259
  · exact B1879263
  · exact B1879267
  · exact B1879271
  · exact B1879275
  · exact B1879279
  · exact B1879283
  · exact B1879287
  · exact B1879291
  · exact B1879295
  · exact B1879299
  · exact B1879303
  · exact B1879307
  · exact B1879311
  · exact B1879315
  · exact B1879319
  · exact B1879323
  · exact B1879327
  · exact B1879331
  · exact B1879335
  · exact B1879339
  · exact B1879343
  · exact B1879347
  · exact B1879351
  · exact B1879355
  · exact B1879359
  · exact B1879363
  · exact B1879367
  · exact B1879371
  · exact B1879375
  · exact B1879379
  · exact B1879383
  · exact B1879387
  · exact B1879391
  · exact B1879395
  · exact B1879399
  · exact B1879403
  · exact B1879407
  · exact B1879411
  · exact B1879415
  · exact B1879419
  · exact B1879423
  · exact B1879427
  · exact B1879431
  · exact B1879435
  · exact B1879439
  · exact B1879443
  · exact B1879447
  · exact B1879451
  · exact B1879455
  · exact B1879459
  · exact B1879463
  · exact B1879467
  · exact B1879471
  · exact B1879475
  · exact B1879479
  · exact B1879483
  · exact B1879487
  · exact B1879491
  · exact B1879495
  · exact B1879499
  · exact B1879503
  · exact B1879507
  · exact B1879511
  · exact B1879515
  · exact B1879519
  · exact B1879523
  · exact B1879527
  · exact B1879531
  · exact B1879535
  · exact B1879539
  · exact B1879543
  · exact B1879547
  · exact B1879551
  · exact B1879555
  · exact B1879559
  · exact B1879563
  · exact B1879567
  · exact B1879571
  · exact B1879575
  · exact B1879579
  · exact B1879583
  · exact B1879587
  · exact B1879591
  · exact B1879595
  · exact B1879599
  · exact B1879603
  · exact B1879607
  · exact B1879611
  · exact B1879615
  · exact B1879619
  · exact B1879623
  · exact B1879627
  · exact B1879631
  · exact B1879635
  · exact B1879639
  · exact B1879643
  · exact B1879647
  · exact B1879651
  · exact B1879655
  · exact B1879659
  · exact B1879663
  · exact B1879667
  · exact B1879671
  · exact B1879675
  · exact B1879679
  · exact B1879683
  · exact B1879687
  · exact B1879691
  · exact B1879695
  · exact B1879699
  · exact B1879703
  · exact B1879707
  · exact B1879711
  · exact B1879715
  · exact B1879719
  · exact B1879723
  · exact B1879727
  · exact B1879731
  · exact B1879735
  · exact B1879739
  · exact B1879743
  · exact B1879747
  · exact B1879751
  · exact B1879755
  · exact B1879759
  · exact B1879763
  · exact B1879767
  · exact B1879771
  · exact B1879775
  · exact B1879779
  · exact B1879783
  · exact B1879787
  · exact B1879791
  · exact B1879795
  · exact B1879799
  · exact B1879803
  · exact B1879807
  · exact B1879811
  · exact B1879815
  · exact B1879819
  · exact B1879823
  · exact B1879827
  · exact B1879831
  · exact B1879835
  · exact B1879839
  · exact B1879843
  · exact B1879847
  · exact B1879851
  · exact B1879855
  · exact B1879859
  · exact B1879863
  · exact B1879867
  · exact B1879871
  · exact B1879875
  · exact B1879879
  · exact B1879883
  · exact B1879887
  · exact B1879891
  · exact B1879895
  · exact B1879899
  · exact B1879903
  · exact B1879907
  · exact B1879911
  · exact B1879915
  · exact B1879919
  · exact B1879923
  · exact B1879927
  · exact B1879931
  · exact B1879935
  · exact B1879939
  · exact B1879943
  · exact B1879947
  · exact B1879951
  · exact B1879955
  · exact B1879959
  · exact B1879963
  · exact B1879967
  · exact B1879971
  · exact B1879975
  · exact B1879979
  · exact B1879983
  · exact B1879987
  · exact B1879991
  · exact B1879995
  · exact B1879999
  · exact B1880003
  · exact B1880007
  · exact B1880011
  · exact B1880015
  · exact B1880019
  · exact B1880023
  · exact B1880027
  · exact B1880031
  · exact B1880035
  · exact B1880039
  · exact B1880043
  · exact B1880047
  · exact B1880051
  · exact B1880055
  · exact B1880059
  · exact B1880063
  · exact B1880067
  · exact B1880071
  · exact B1880075
  · exact B1880079
  · exact B1880083
  · exact B1880087
  · exact B1880091
  · exact B1880095
  · exact B1880099
  · exact B1880103
  · exact B1880107
  · exact B1880111
  · exact B1880115
  · exact B1880119
  · exact B1880123
  · exact B1880127
  · exact B1880131
  · exact B1880135
  · exact B1880139
  · exact B1880143
  · exact B1880147
  · exact B1880151
  · exact B1880155
  · exact B1880159
  · exact B1880163
  · exact B1880167
  · exact B1880171
  · exact B1880175
  · exact B1880179
  · exact B1880183
  · exact B1880187
  · exact B1880191
  · exact B1880195
  · exact B1880199
  · exact B1880203
  · exact B1880207
  · exact B1880211
  · exact B1880215
  · exact B1880219
  · exact B1880223
  · exact B1880227
  · exact B1880231
  · exact B1880235
  · exact B1880239
  · exact B1880243
  · exact B1880247
  · exact B1880251
  · exact B1880255
  · exact B1880259
  · exact B1880263
  · exact B1880267
  · exact B1880271
  · exact B1880275
  · exact B1880279
  · exact B1880283
  · exact B1880287
  · exact B1880291
  · exact B1880295
  · exact B1880299
  · exact B1880303
  · exact B1880307
  · exact B1880311
  · exact B1880315
  · exact B1880319
  · exact B1880323
  · exact B1880327
  · exact B1880331
  · exact B1880335
  · exact B1880339
  · exact B1880343
  · exact B1880347
  · exact B1880351
  · exact B1880355
  · exact B1880359
  · exact B1880363
  · exact B1880367
  · exact B1880371
  · exact B1880375
  · exact B1880379
  · exact B1880383
  · exact B1880387
  · exact B1880391
  · exact B1880395
  · exact B1880399
  · exact B1880403
  · exact B1880407
  · exact B1880411
  · exact B1880415
  · exact B1880419
  · exact B1880423
  · exact B1880427
  · exact B1880431
  · exact B1880435
  · exact B1880439
  · exact B1880443
  · exact B1880447
  · exact B1880451
  · exact B1880455
  · exact B1880459
  · exact B1880463
  · exact B1880467
  · exact B1880471
  · exact B1880475
  · exact B1880479
  · exact B1880483
  · exact B1880487
  · exact B1880491
  · exact B1880495
  · exact B1880499
  · exact B1880503
  · exact B1880507
  · exact B1880511
  · exact B1880515
  · exact B1880519
  · exact B1880523
  · exact B1880527
  · exact B1880531
  · exact B1880535
  · exact B1880539
  · exact B1880543
  · exact B1880547
  · exact B1880551
  · exact B1880555
  · exact B1880559
  · exact B1880563
  · exact B1880567
  · exact B1880571
  · exact B1880575
  · exact B1880579
  · exact B1880583
  · exact B1880587
  · exact B1880591
  · exact B1880595
  · exact B1880599
  · exact B1880603
  · exact B1880607
  · exact B1880611
  · exact B1880615
  · exact B1880619
  · exact B1880623
  · exact B1880627
  · exact B1880631
  · exact B1880635
  · exact B1880639
  · exact B1880643
  · exact B1880647
  · exact B1880651
  · exact B1880655
  · exact B1880659
  · exact B1880663
  · exact B1880667
  · exact B1880671
  · exact B1880675
  · exact B1880679
  · exact B1880683
  · exact B1880687
  · exact B1880691
  · exact B1880695
  · exact B1880699
  · exact B1880703
  · exact B1880707
  · exact B1880711
  · exact B1880715
  · exact B1880719
  · exact B1880723
  · exact B1880727
  · exact B1880731
  · exact B1880735
  · exact B1880739
  · exact B1880743
  · exact B1880747
  · exact B1880751
  · exact B1880755
  · exact B1880759
  · exact B1880763
  · exact B1880767
  · exact B1880771
  · exact B1880775
  · exact B1880779
  · exact B1880783
  · exact B1880787
  · exact B1880791
  · exact B1880795
  · exact B1880799
  · exact B1880803
  · exact B1880807
  · exact B1880811
  · exact B1880815
  · exact B1880819
  · exact B1880823
  · exact B1880827
  · exact B1880831
  · exact B1880835
  · exact B1880839
  · exact B1880843
  · exact B1880847
  · exact B1880851
  · exact B1880855
  · exact B1880859
  · exact B1880863
  · exact B1880867
  · exact B1880871
  · exact B1880875
  · exact B1880879
  · exact B1880883
  · exact B1880887
  · exact B1880891
  · exact B1880895
  · exact B1880899
  · exact B1880903
  · exact B1880907
  · exact B1880911
  · exact B1880915
  · exact B1880919
  · exact B1880923
  · exact B1880927
  · exact B1880931
  · exact B1880935
  · exact B1880939
  · exact B1880943
  · exact B1880947
  · exact B1880951
  · exact B1880955
  · exact B1880959
  · exact B1880963
  · exact B1880967
  · exact B1880971
  · exact B1880975
  · exact B1880979
  · exact B1880983
  · exact B1880987
  · exact B1880991
  · exact B1880995
  · exact B1880999
  · exact B1881003
  · exact B1881007
  · exact B1881011
  · exact B1881015
  · exact B1881019
  · exact B1881023
  · exact B1881027
  · exact B1881031
  · exact B1881035
  · exact B1881039
  · exact B1881043
  · exact B1881047
  · exact B1881051
  · exact B1881055
  · exact B1881059
  · exact B1881063
  · exact B1881067
  · exact B1881071
  · exact B1881075
  · exact B1881079
  · exact B1881083
  · exact B1881087
  · exact B1881091
  · exact B1881095
  · exact B1881099
  · exact B1881103
  · exact B1881107
  · exact B1881111
  · exact B1881115
  · exact B1881119
  · exact B1881123
  · exact B1881127
  · exact B1881131
  · exact B1881135
  · exact B1881139

theorem solution (m : ℕ) (hlo : 1879141 ≤ m) (hhi : m ≤ 1881141) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 469785 ≤ j := by omega
    have hj2 : j ≤ 470284 := by omega
    have hb : Blo 1879141 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
