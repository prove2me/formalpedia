-- Prove2me | solution 1 for syracuse_descends_range_1283960_1285960
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:20.338771+00:00
-- url     : https://prove2.me/submissions/d4f5b34a-5f0b-4c0a-a34f-9b49280b97d4

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


theorem B2891789 : Blo 1283960 2891789 := bbase (se 3 (by rfl) ⟨542210, by rfl⟩ : syracuseStep 2891789 = 1084421) (by norm_num)
theorem B2441269 : Blo 1283960 2441269 := bbase (se 5 (by rfl) ⟨114434, by rfl⟩ : syracuseStep 2441269 = 228869) (by norm_num)
theorem B1302589 : Blo 1283960 1302589 := bbase (se 3 (by rfl) ⟨244235, by rfl⟩ : syracuseStep 1302589 = 488471) (by norm_num)
theorem B2891861 : Blo 1283960 2891861 := bbase (se 8 (by rfl) ⟨16944, by rfl⟩ : syracuseStep 2891861 = 33889) (by norm_num)
theorem B30097493 : Blo 1283960 30097493 := bbase (se 8 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 30097493 = 352705) (by norm_num)
theorem B3661973 : Blo 1283960 3661973 := bbase (se 6 (by rfl) ⟨85827, by rfl⟩ : syracuseStep 3661973 = 171655) (by norm_num)
theorem B2891933 : Blo 1283960 2891933 := bbase (se 3 (by rfl) ⟨542237, by rfl⟩ : syracuseStep 2891933 = 1084475) (by norm_num)
theorem B3252413 : Blo 1283960 3252413 := bbase (se 3 (by rfl) ⟨609827, by rfl⟩ : syracuseStep 3252413 = 1219655) (by norm_num)
theorem B2892005 : Blo 1283960 2892005 := bbase (se 4 (by rfl) ⟨271125, by rfl⟩ : syracuseStep 2892005 = 542251) (by norm_num)
theorem B1564949 : Blo 1283960 1564949 := bbase (se 6 (by rfl) ⟨36678, by rfl⟩ : syracuseStep 1564949 = 73357) (by norm_num)
theorem B2892077 : Blo 1283960 2892077 := bbase (se 3 (by rfl) ⟨542264, by rfl⟩ : syracuseStep 2892077 = 1084529) (by norm_num)
theorem B4333877 : Blo 1283960 4333877 := bbase (se 5 (by rfl) ⟨203150, by rfl⟩ : syracuseStep 4333877 = 406301) (by norm_num)
theorem B3760453 : Blo 1283960 3760453 := bbase (se 4 (by rfl) ⟨352542, by rfl⟩ : syracuseStep 3760453 = 705085) (by norm_num)
theorem B2892149 : Blo 1283960 2892149 := bbase (se 5 (by rfl) ⟨135569, by rfl⟩ : syracuseStep 2892149 = 271139) (by norm_num)
theorem B2892221 : Blo 1283960 2892221 := bbase (se 3 (by rfl) ⟨542291, by rfl⟩ : syracuseStep 2892221 = 1084583) (by norm_num)
theorem B2892293 : Blo 1283960 2892293 := bbase (se 4 (by rfl) ⟨271152, by rfl⟩ : syracuseStep 2892293 = 542305) (by norm_num)
theorem B3252757 : Blo 1283960 3252757 := bbase (se 6 (by rfl) ⟨76236, by rfl⟩ : syracuseStep 3252757 = 152473) (by norm_num)
theorem B3088925 : Blo 1283960 3088925 := bbase (se 3 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 3088925 = 1158347) (by norm_num)
theorem B2892365 : Blo 1283960 2892365 := bbase (se 3 (by rfl) ⟨542318, by rfl⟩ : syracuseStep 2892365 = 1084637) (by norm_num)
theorem B3252869 : Blo 1283960 3252869 := bbase (se 4 (by rfl) ⟨304956, by rfl⟩ : syracuseStep 3252869 = 609913) (by norm_num)
theorem B6505109 : Blo 1283960 6505109 := bbase (se 6 (by rfl) ⟨152463, by rfl⟩ : syracuseStep 6505109 = 304927) (by norm_num)
theorem B2892437 : Blo 1283960 2892437 := bbase (se 6 (by rfl) ⟨67791, by rfl⟩ : syracuseStep 2892437 = 135583) (by norm_num)
theorem B2056925 : Blo 1283960 2056925 := bbase (se 3 (by rfl) ⟨385673, by rfl⟩ : syracuseStep 2056925 = 771347) (by norm_num)
theorem B2892509 : Blo 1283960 2892509 := bbase (se 3 (by rfl) ⟨542345, by rfl⟩ : syracuseStep 2892509 = 1084691) (by norm_num)
theorem B3089117 : Blo 1283960 3089117 := bbase (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) (by norm_num)
theorem B4334309 : Blo 1283960 4334309 := bbase (se 4 (by rfl) ⟨406341, by rfl⟩ : syracuseStep 4334309 = 812683) (by norm_num)
theorem B9265909 : Blo 1283960 9265909 := bbase (se 5 (by rfl) ⟨434339, by rfl⟩ : syracuseStep 9265909 = 868679) (by norm_num)
theorem B6177541 : Blo 1283960 6177541 := bbase (se 4 (by rfl) ⟨579144, by rfl⟩ : syracuseStep 6177541 = 1158289) (by norm_num)
theorem B2892581 : Blo 1283960 2892581 := bbase (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) (by norm_num)
theorem B1925957 : Blo 1283960 1925957 := bbase (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) (by norm_num)
theorem B3253061 : Blo 1283960 3253061 := bbase (se 4 (by rfl) ⟨304974, by rfl⟩ : syracuseStep 3253061 = 609949) (by norm_num)
theorem B1925981 : Blo 1283960 1925981 := bbase (se 3 (by rfl) ⟨361121, by rfl⟩ : syracuseStep 1925981 = 722243) (by norm_num)
theorem B2745181 : Blo 1283960 2745181 := bbase (se 3 (by rfl) ⟨514721, by rfl⟩ : syracuseStep 2745181 = 1029443) (by norm_num)
theorem B2605925 : Blo 1283960 2605925 := bbase (se 4 (by rfl) ⟨244305, by rfl⟩ : syracuseStep 2605925 = 488611) (by norm_num)
theorem B2892653 : Blo 1283960 2892653 := bbase (se 3 (by rfl) ⟨542372, by rfl⟩ : syracuseStep 2892653 = 1084745) (by norm_num)
theorem B1409905 : Blo 1283960 1409905 := bbase (se 2 (by rfl) ⟨528714, by rfl⟩ : syracuseStep 1409905 = 1057429) (by norm_num)
theorem B1926005 : Blo 1283960 1926005 := bbase (se 5 (by rfl) ⟨90281, by rfl⟩ : syracuseStep 1926005 = 180563) (by norm_num)
theorem B1926029 : Blo 1283960 1926029 := bbase (se 3 (by rfl) ⟨361130, by rfl⟩ : syracuseStep 1926029 = 722261) (by norm_num)
theorem B4875173 : Blo 1283960 4875173 := bbase (se 4 (by rfl) ⟨457047, by rfl⟩ : syracuseStep 4875173 = 914095) (by norm_num)
theorem B1926053 : Blo 1283960 1926053 := bbase (se 4 (by rfl) ⟨180567, by rfl⟩ : syracuseStep 1926053 = 361135) (by norm_num)
theorem B7316405 : Blo 1283960 7316405 := bbase (se 5 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 7316405 = 685913) (by norm_num)
theorem B2892725 : Blo 1283960 2892725 := bbase (se 5 (by rfl) ⟨135596, by rfl⟩ : syracuseStep 2892725 = 271193) (by norm_num)
theorem B1926077 : Blo 1283960 1926077 := bbase (se 3 (by rfl) ⟨361139, by rfl⟩ : syracuseStep 1926077 = 722279) (by norm_num)
theorem B1926101 : Blo 1283960 1926101 := bbase (se 7 (by rfl) ⟨22571, by rfl⟩ : syracuseStep 1926101 = 45143) (by norm_num)
theorem B1926125 : Blo 1283960 1926125 := bbase (se 3 (by rfl) ⟨361148, by rfl⟩ : syracuseStep 1926125 = 722297) (by norm_num)
theorem B2892797 : Blo 1283960 2892797 := bbase (se 3 (by rfl) ⟨542399, by rfl⟩ : syracuseStep 2892797 = 1084799) (by norm_num)
theorem B1926149 : Blo 1283960 1926149 := bbase (se 4 (by rfl) ⟨180576, by rfl⟩ : syracuseStep 1926149 = 361153) (by norm_num)
theorem B1647625 : Blo 1283960 1647625 := bbase (se 2 (by rfl) ⟨617859, by rfl⟩ : syracuseStep 1647625 = 1235719) (by norm_num)
theorem B1926173 : Blo 1283960 1926173 := bbase (se 3 (by rfl) ⟨361157, by rfl⟩ : syracuseStep 1926173 = 722315) (by norm_num)
theorem B1926197 : Blo 1283960 1926197 := bbase (se 5 (by rfl) ⟨90290, by rfl⟩ : syracuseStep 1926197 = 180581) (by norm_num)
theorem B2892869 : Blo 1283960 2892869 := bbase (se 4 (by rfl) ⟨271206, by rfl⟩ : syracuseStep 2892869 = 542413) (by norm_num)
theorem B1926221 : Blo 1283960 1926221 := bbase (se 3 (by rfl) ⟨361166, by rfl⟩ : syracuseStep 1926221 = 722333) (by norm_num)
theorem B1926245 : Blo 1283960 1926245 := bbase (se 4 (by rfl) ⟨180585, by rfl⟩ : syracuseStep 1926245 = 361171) (by norm_num)
theorem B5489765 : Blo 1283960 5489765 := bbase (se 4 (by rfl) ⟨514665, by rfl⟩ : syracuseStep 5489765 = 1029331) (by norm_num)
theorem B1926269 : Blo 1283960 1926269 := bbase (se 3 (by rfl) ⟨361175, by rfl⟩ : syracuseStep 1926269 = 722351) (by norm_num)
theorem B2892941 : Blo 1283960 2892941 := bbase (se 3 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 2892941 = 1084853) (by norm_num)
theorem B1926293 : Blo 1283960 1926293 := bbase (se 6 (by rfl) ⟨45147, by rfl⟩ : syracuseStep 1926293 = 90295) (by norm_num)
theorem B4334741 : Blo 1283960 4334741 := bbase (se 6 (by rfl) ⟨101595, by rfl⟩ : syracuseStep 4334741 = 203191) (by norm_num)
theorem B3253405 : Blo 1283960 3253405 := bbase (se 3 (by rfl) ⟨610013, by rfl⟩ : syracuseStep 3253405 = 1220027) (by norm_num)
theorem B1926317 : Blo 1283960 1926317 := bbase (se 3 (by rfl) ⟨361184, by rfl⟩ : syracuseStep 1926317 = 722369) (by norm_num)
theorem B4875461 : Blo 1283960 4875461 := bbase (se 4 (by rfl) ⟨457074, by rfl⟩ : syracuseStep 4875461 = 914149) (by norm_num)
theorem B1926341 : Blo 1283960 1926341 := bbase (se 4 (by rfl) ⟨180594, by rfl⟩ : syracuseStep 1926341 = 361189) (by norm_num)
theorem B15623381 : Blo 1283960 15623381 := bbase (se 7 (by rfl) ⟨183086, by rfl⟩ : syracuseStep 15623381 = 366173) (by norm_num)
theorem B2893013 : Blo 1283960 2893013 := bbase (se 7 (by rfl) ⟨33902, by rfl⟩ : syracuseStep 2893013 = 67805) (by norm_num)
theorem B1926365 : Blo 1283960 1926365 := bbase (se 3 (by rfl) ⟨361193, by rfl⟩ : syracuseStep 1926365 = 722387) (by norm_num)
theorem B1926389 : Blo 1283960 1926389 := bbase (se 5 (by rfl) ⟨90299, by rfl⟩ : syracuseStep 1926389 = 180599) (by norm_num)
theorem B1926413 : Blo 1283960 1926413 := bbase (se 3 (by rfl) ⟨361202, by rfl⟩ : syracuseStep 1926413 = 722405) (by norm_num)
theorem B3253517 : Blo 1283960 3253517 := bbase (se 3 (by rfl) ⟨610034, by rfl⟩ : syracuseStep 3253517 = 1220069) (by norm_num)
theorem B8234261 : Blo 1283960 8234261 := bbase (se 6 (by rfl) ⟨192990, by rfl⟩ : syracuseStep 8234261 = 385981) (by norm_num)
theorem B4695317 : Blo 1283960 4695317 := bbase (se 6 (by rfl) ⟨110046, by rfl⟩ : syracuseStep 4695317 = 220093) (by norm_num)
theorem B2893085 : Blo 1283960 2893085 := bbase (se 3 (by rfl) ⟨542453, by rfl⟩ : syracuseStep 2893085 = 1084907) (by norm_num)
theorem B1926437 : Blo 1283960 1926437 := bbase (se 4 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 1926437 = 361207) (by norm_num)
theorem B1926461 : Blo 1283960 1926461 := bbase (se 3 (by rfl) ⟨361211, by rfl⟩ : syracuseStep 1926461 = 722423) (by norm_num)
theorem B2745677 : Blo 1283960 2745677 := bbase (se 3 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 2745677 = 1029629) (by norm_num)
theorem B1926485 : Blo 1283960 1926485 := bbase (se 12 (by rfl) ⟨705, by rfl⟩ : syracuseStep 1926485 = 1411) (by norm_num)
theorem B2893157 : Blo 1283960 2893157 := bbase (se 4 (by rfl) ⟨271233, by rfl⟩ : syracuseStep 2893157 = 542467) (by norm_num)
theorem B1926509 : Blo 1283960 1926509 := bbase (se 3 (by rfl) ⟨361220, by rfl⟩ : syracuseStep 1926509 = 722441) (by norm_num)
theorem B1926533 : Blo 1283960 1926533 := bbase (se 4 (by rfl) ⟨180612, by rfl⟩ : syracuseStep 1926533 = 361225) (by norm_num)
theorem B1926557 : Blo 1283960 1926557 := bbase (se 3 (by rfl) ⟨361229, by rfl⟩ : syracuseStep 1926557 = 722459) (by norm_num)
theorem B2893229 : Blo 1283960 2893229 := bbase (se 3 (by rfl) ⟨542480, by rfl⟩ : syracuseStep 2893229 = 1084961) (by norm_num)
theorem B1926581 : Blo 1283960 1926581 := bbase (se 5 (by rfl) ⟨90308, by rfl⟩ : syracuseStep 1926581 = 180617) (by norm_num)
theorem B1926605 : Blo 1283960 1926605 := bbase (se 3 (by rfl) ⟨361238, by rfl⟩ : syracuseStep 1926605 = 722477) (by norm_num)
theorem B3253709 : Blo 1283960 3253709 := bbase (se 3 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 3253709 = 1220141) (by norm_num)
theorem B8455637 : Blo 1283960 8455637 := bbase (se 7 (by rfl) ⟨99089, by rfl⟩ : syracuseStep 8455637 = 198179) (by norm_num)
theorem B1926629 : Blo 1283960 1926629 := bbase (se 4 (by rfl) ⟨180621, by rfl⟩ : syracuseStep 1926629 = 361243) (by norm_num)
theorem B2893301 : Blo 1283960 2893301 := bbase (se 5 (by rfl) ⟨135623, by rfl⟩ : syracuseStep 2893301 = 271247) (by norm_num)
theorem B1926653 : Blo 1283960 1926653 := bbase (se 3 (by rfl) ⟨361247, by rfl⟩ : syracuseStep 1926653 = 722495) (by norm_num)
theorem B1926677 : Blo 1283960 1926677 := bbase (se 6 (by rfl) ⟨45156, by rfl⟩ : syracuseStep 1926677 = 90313) (by norm_num)
theorem B1926701 : Blo 1283960 1926701 := bbase (se 3 (by rfl) ⟨361256, by rfl⟩ : syracuseStep 1926701 = 722513) (by norm_num)
theorem B2893373 : Blo 1283960 2893373 := bbase (se 3 (by rfl) ⟨542507, by rfl⟩ : syracuseStep 2893373 = 1085015) (by norm_num)
theorem B1926725 : Blo 1283960 1926725 := bbase (se 4 (by rfl) ⟨180630, by rfl⟩ : syracuseStep 1926725 = 361261) (by norm_num)
theorem B4335173 : Blo 1283960 4335173 := bbase (se 4 (by rfl) ⟨406422, by rfl⟩ : syracuseStep 4335173 = 812845) (by norm_num)
theorem B1926749 : Blo 1283960 1926749 := bbase (se 3 (by rfl) ⟨361265, by rfl⟩ : syracuseStep 1926749 = 722531) (by norm_num)
theorem B1926773 : Blo 1283960 1926773 := bbase (se 5 (by rfl) ⟨90317, by rfl⟩ : syracuseStep 1926773 = 180635) (by norm_num)
theorem B8914549 : Blo 1283960 8914549 := bbase (se 5 (by rfl) ⟨417869, by rfl⟩ : syracuseStep 8914549 = 835739) (by norm_num)
theorem B2057861 : Blo 1283960 2057861 := bbase (se 4 (by rfl) ⟨192924, by rfl⟩ : syracuseStep 2057861 = 385849) (by norm_num)
theorem B1926797 : Blo 1283960 1926797 := bbase (se 3 (by rfl) ⟨361274, by rfl⟩ : syracuseStep 1926797 = 722549) (by norm_num)
theorem B1926821 : Blo 1283960 1926821 := bbase (se 4 (by rfl) ⟨180639, by rfl⟩ : syracuseStep 1926821 = 361279) (by norm_num)
theorem B1926845 : Blo 1283960 1926845 := bbase (se 3 (by rfl) ⟨361283, by rfl⟩ : syracuseStep 1926845 = 722567) (by norm_num)
theorem B1926869 : Blo 1283960 1926869 := bbase (se 7 (by rfl) ⟨22580, by rfl⟩ : syracuseStep 1926869 = 45161) (by norm_num)
theorem B1926893 : Blo 1283960 1926893 := bbase (se 3 (by rfl) ⟨361292, by rfl⟩ : syracuseStep 1926893 = 722585) (by norm_num)
theorem B1926917 : Blo 1283960 1926917 := bbase (se 4 (by rfl) ⟨180648, by rfl⟩ : syracuseStep 1926917 = 361297) (by norm_num)
theorem B3131149 : Blo 1283960 3131149 := bbase (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) (by norm_num)
theorem B1926941 : Blo 1283960 1926941 := bbase (se 3 (by rfl) ⟨361301, by rfl⟩ : syracuseStep 1926941 = 722603) (by norm_num)
theorem B3254053 : Blo 1283960 3254053 := bbase (se 4 (by rfl) ⟨305067, by rfl⟩ : syracuseStep 3254053 = 610135) (by norm_num)
theorem B1926965 : Blo 1283960 1926965 := bbase (se 5 (by rfl) ⟨90326, by rfl⟩ : syracuseStep 1926965 = 180653) (by norm_num)
theorem B1926989 : Blo 1283960 1926989 := bbase (se 3 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 1926989 = 722621) (by norm_num)
theorem B1927013 : Blo 1283960 1927013 := bbase (se 4 (by rfl) ⟨180657, by rfl⟩ : syracuseStep 1927013 = 361315) (by norm_num)
theorem B1927037 : Blo 1283960 1927037 := bbase (se 3 (by rfl) ⟨361319, by rfl⟩ : syracuseStep 1927037 = 722639) (by norm_num)
theorem B1927061 : Blo 1283960 1927061 := bbase (se 6 (by rfl) ⟨45165, by rfl⟩ : syracuseStep 1927061 = 90331) (by norm_num)
theorem B3254165 : Blo 1283960 3254165 := bbase (se 6 (by rfl) ⟨76269, by rfl⟩ : syracuseStep 3254165 = 152539) (by norm_num)
theorem B1828765 : Blo 1283960 1828765 := bbase (se 3 (by rfl) ⟨342893, by rfl⟩ : syracuseStep 1828765 = 685787) (by norm_num)
theorem B6506405 : Blo 1283960 6506405 := bbase (se 4 (by rfl) ⟨609975, by rfl⟩ : syracuseStep 6506405 = 1219951) (by norm_num)
theorem B3762085 : Blo 1283960 3762085 := bbase (se 4 (by rfl) ⟨352695, by rfl⟩ : syracuseStep 3762085 = 705391) (by norm_num)
theorem B1927085 : Blo 1283960 1927085 := bbase (se 3 (by rfl) ⟨361328, by rfl⟩ : syracuseStep 1927085 = 722657) (by norm_num)
theorem B1927109 : Blo 1283960 1927109 := bbase (se 4 (by rfl) ⟨180666, by rfl⟩ : syracuseStep 1927109 = 361333) (by norm_num)
theorem B1927133 : Blo 1283960 1927133 := bbase (se 3 (by rfl) ⟨361337, by rfl⟩ : syracuseStep 1927133 = 722675) (by norm_num)
theorem B5564389 : Blo 1283960 5564389 := bbase (se 4 (by rfl) ⟨521661, by rfl⟩ : syracuseStep 5564389 = 1043323) (by norm_num)
theorem B4335605 : Blo 1283960 4335605 := bbase (se 5 (by rfl) ⟨203231, by rfl⟩ : syracuseStep 4335605 = 406463) (by norm_num)
theorem B1927157 : Blo 1283960 1927157 := bbase (se 5 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 1927157 = 180671) (by norm_num)
theorem B1927181 : Blo 1283960 1927181 := bbase (se 3 (by rfl) ⟨361346, by rfl⟩ : syracuseStep 1927181 = 722693) (by norm_num)
theorem B1927205 : Blo 1283960 1927205 := bbase (se 4 (by rfl) ⟨180675, by rfl⟩ : syracuseStep 1927205 = 361351) (by norm_num)
theorem B1927229 : Blo 1283960 1927229 := bbase (se 3 (by rfl) ⟨361355, by rfl⟩ : syracuseStep 1927229 = 722711) (by norm_num)
theorem B1927253 : Blo 1283960 1927253 := bbase (se 8 (by rfl) ⟨11292, by rfl⟩ : syracuseStep 1927253 = 22585) (by norm_num)
theorem B5490773 : Blo 1283960 5490773 := bbase (se 8 (by rfl) ⟨32172, by rfl⟩ : syracuseStep 5490773 = 64345) (by norm_num)
theorem B3254357 : Blo 1283960 3254357 := bbase (se 8 (by rfl) ⟨19068, by rfl⟩ : syracuseStep 3254357 = 38137) (by norm_num)
theorem B1927277 : Blo 1283960 1927277 := bbase (se 3 (by rfl) ⟨361364, by rfl⟩ : syracuseStep 1927277 = 722729) (by norm_num)
theorem B5859461 : Blo 1283960 5859461 := bbase (se 4 (by rfl) ⟨549324, by rfl⟩ : syracuseStep 5859461 = 1098649) (by norm_num)
theorem B1927301 : Blo 1283960 1927301 := bbase (se 4 (by rfl) ⟨180684, by rfl⟩ : syracuseStep 1927301 = 361369) (by norm_num)
theorem B1927325 : Blo 1283960 1927325 := bbase (se 3 (by rfl) ⟨361373, by rfl⟩ : syracuseStep 1927325 = 722747) (by norm_num)
theorem B1321117 : Blo 1283960 1321117 := bbase (se 3 (by rfl) ⟨247709, by rfl⟩ : syracuseStep 1321117 = 495419) (by norm_num)
theorem B1927349 : Blo 1283960 1927349 := bbase (se 5 (by rfl) ⟨90344, by rfl⟩ : syracuseStep 1927349 = 180689) (by norm_num)
theorem B1927373 : Blo 1283960 1927373 := bbase (se 3 (by rfl) ⟨361382, by rfl⟩ : syracuseStep 1927373 = 722765) (by norm_num)
theorem B1927397 : Blo 1283960 1927397 := bbase (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) (by norm_num)
theorem B1648873 : Blo 1283960 1648873 := bbase (se 2 (by rfl) ⟨618327, by rfl⟩ : syracuseStep 1648873 = 1236655) (by norm_num)
theorem B1927421 : Blo 1283960 1927421 := bbase (se 3 (by rfl) ⟨361391, by rfl⟩ : syracuseStep 1927421 = 722783) (by norm_num)
theorem B2058509 : Blo 1283960 2058509 := bbase (se 3 (by rfl) ⟨385970, by rfl⟩ : syracuseStep 2058509 = 771941) (by norm_num)
theorem B1927445 : Blo 1283960 1927445 := bbase (se 6 (by rfl) ⟨45174, by rfl⟩ : syracuseStep 1927445 = 90349) (by norm_num)
theorem B1927469 : Blo 1283960 1927469 := bbase (se 3 (by rfl) ⟨361400, by rfl⟩ : syracuseStep 1927469 = 722801) (by norm_num)
theorem B1927493 : Blo 1283960 1927493 := bbase (se 4 (by rfl) ⟨180702, by rfl⟩ : syracuseStep 1927493 = 361405) (by norm_num)
theorem B1927517 : Blo 1283960 1927517 := bbase (se 3 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 1927517 = 722819) (by norm_num)
theorem B4876645 : Blo 1283960 4876645 := bbase (se 4 (by rfl) ⟨457185, by rfl⟩ : syracuseStep 4876645 = 914371) (by norm_num)
theorem B1927541 : Blo 1283960 1927541 := bbase (se 5 (by rfl) ⟨90353, by rfl⟩ : syracuseStep 1927541 = 180707) (by norm_num)
theorem B2197901 : Blo 1283960 2197901 := bbase (se 3 (by rfl) ⟨412106, by rfl⟩ : syracuseStep 2197901 = 824213) (by norm_num)
theorem B1927565 : Blo 1283960 1927565 := bbase (se 3 (by rfl) ⟨361418, by rfl⟩ : syracuseStep 1927565 = 722837) (by norm_num)
theorem B4336037 : Blo 1283960 4336037 := bbase (se 4 (by rfl) ⟨406503, by rfl⟩ : syracuseStep 4336037 = 813007) (by norm_num)
theorem B1927589 : Blo 1283960 1927589 := bbase (se 4 (by rfl) ⟨180711, by rfl⟩ : syracuseStep 1927589 = 361423) (by norm_num)
theorem B3254701 : Blo 1283960 3254701 := bbase (se 3 (by rfl) ⟨610256, by rfl⟩ : syracuseStep 3254701 = 1220513) (by norm_num)
theorem B1927613 : Blo 1283960 1927613 := bbase (se 3 (by rfl) ⟨361427, by rfl⟩ : syracuseStep 1927613 = 722855) (by norm_num)
theorem B4114901 : Blo 1283960 4114901 := bbase (se 7 (by rfl) ⟨48221, by rfl⟩ : syracuseStep 4114901 = 96443) (by norm_num)
theorem B1927637 : Blo 1283960 1927637 := bbase (se 7 (by rfl) ⟨22589, by rfl⟩ : syracuseStep 1927637 = 45179) (by norm_num)
theorem B1927661 : Blo 1283960 1927661 := bbase (se 3 (by rfl) ⟨361436, by rfl⟩ : syracuseStep 1927661 = 722873) (by norm_num)
theorem B1927685 : Blo 1283960 1927685 := bbase (se 4 (by rfl) ⟨180720, by rfl⟩ : syracuseStep 1927685 = 361441) (by norm_num)
theorem B1649165 : Blo 1283960 1649165 := bbase (se 3 (by rfl) ⟨309218, by rfl⟩ : syracuseStep 1649165 = 618437) (by norm_num)
theorem B1927709 : Blo 1283960 1927709 := bbase (se 3 (by rfl) ⟨361445, by rfl⟩ : syracuseStep 1927709 = 722891) (by norm_num)
theorem B3254813 : Blo 1283960 3254813 := bbase (se 3 (by rfl) ⟨610277, by rfl⟩ : syracuseStep 3254813 = 1220555) (by norm_num)
theorem B1878565 : Blo 1283960 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B1927733 : Blo 1283960 1927733 := bbase (se 5 (by rfl) ⟨90362, by rfl⟩ : syracuseStep 1927733 = 180725) (by norm_num)
theorem B1927757 : Blo 1283960 1927757 := bbase (se 3 (by rfl) ⟨361454, by rfl⟩ : syracuseStep 1927757 = 722909) (by norm_num)
theorem B1927781 : Blo 1283960 1927781 := bbase (se 4 (by rfl) ⟨180729, by rfl⟩ : syracuseStep 1927781 = 361459) (by norm_num)
theorem B1444477 : Blo 1283960 1444477 := bbase (se 3 (by rfl) ⟨270839, by rfl⟩ : syracuseStep 1444477 = 541679) (by norm_num)
theorem B1927805 : Blo 1283960 1927805 := bbase (se 3 (by rfl) ⟨361463, by rfl⟩ : syracuseStep 1927805 = 722927) (by norm_num)
theorem B4876949 : Blo 1283960 4876949 := bbase (se 6 (by rfl) ⟨114303, by rfl⟩ : syracuseStep 4876949 = 228607) (by norm_num)
theorem B1927829 : Blo 1283960 1927829 := bbase (se 6 (by rfl) ⟨45183, by rfl⟩ : syracuseStep 1927829 = 90367) (by norm_num)
theorem B1542809 : Blo 1283960 1542809 := bbase (se 2 (by rfl) ⟨578553, by rfl⟩ : syracuseStep 1542809 = 1157107) (by norm_num)
theorem B1444513 : Blo 1283960 1444513 := bbase (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) (by norm_num)
theorem B1927853 : Blo 1283960 1927853 := bbase (se 3 (by rfl) ⟨361472, by rfl⟩ : syracuseStep 1927853 = 722945) (by norm_num)
theorem B1829557 : Blo 1283960 1829557 := bbase (se 5 (by rfl) ⟨85760, by rfl⟩ : syracuseStep 1829557 = 171521) (by norm_num)
theorem B1444549 : Blo 1283960 1444549 := bbase (se 4 (by rfl) ⟨135426, by rfl⟩ : syracuseStep 1444549 = 270853) (by norm_num)
theorem B1927877 : Blo 1283960 1927877 := bbase (se 4 (by rfl) ⟨180738, by rfl⟩ : syracuseStep 1927877 = 361477) (by norm_num)
theorem B1927901 : Blo 1283960 1927901 := bbase (se 3 (by rfl) ⟨361481, by rfl⟩ : syracuseStep 1927901 = 722963) (by norm_num)
theorem B3255005 : Blo 1283960 3255005 := bbase (se 3 (by rfl) ⟨610313, by rfl⟩ : syracuseStep 3255005 = 1220627) (by norm_num)
theorem B1444585 : Blo 1283960 1444585 := bbase (se 2 (by rfl) ⟨541719, by rfl⟩ : syracuseStep 1444585 = 1083439) (by norm_num)
theorem B1927925 : Blo 1283960 1927925 := bbase (se 5 (by rfl) ⟨90371, by rfl⟩ : syracuseStep 1927925 = 180743) (by norm_num)
theorem B1444621 : Blo 1283960 1444621 := bbase (se 3 (by rfl) ⟨270866, by rfl⟩ : syracuseStep 1444621 = 541733) (by norm_num)
theorem B1542925 : Blo 1283960 1542925 := bbase (se 3 (by rfl) ⟨289298, by rfl⟩ : syracuseStep 1542925 = 578597) (by norm_num)
theorem B1927949 : Blo 1283960 1927949 := bbase (se 3 (by rfl) ⟨361490, by rfl⟩ : syracuseStep 1927949 = 722981) (by norm_num)
theorem B1927973 : Blo 1283960 1927973 := bbase (se 4 (by rfl) ⟨180747, by rfl⟩ : syracuseStep 1927973 = 361495) (by norm_num)
theorem B1444657 : Blo 1283960 1444657 := bbase (se 2 (by rfl) ⟨541746, by rfl⟩ : syracuseStep 1444657 = 1083493) (by norm_num)
theorem B1927997 : Blo 1283960 1927997 := bbase (se 3 (by rfl) ⟨361499, by rfl⟩ : syracuseStep 1927997 = 722999) (by norm_num)
theorem B1444693 : Blo 1283960 1444693 := bbase (se 9 (by rfl) ⟨4232, by rfl⟩ : syracuseStep 1444693 = 8465) (by norm_num)
theorem B1542997 : Blo 1283960 1542997 := bbase (se 9 (by rfl) ⟨4520, by rfl⟩ : syracuseStep 1542997 = 9041) (by norm_num)
theorem B4336469 : Blo 1283960 4336469 := bbase (se 9 (by rfl) ⟨12704, by rfl⟩ : syracuseStep 4336469 = 25409) (by norm_num)
theorem B1928021 : Blo 1283960 1928021 := bbase (se 9 (by rfl) ⟨5648, by rfl⟩ : syracuseStep 1928021 = 11297) (by norm_num)
theorem B37071701 : Blo 1283960 37071701 := bbase (se 9 (by rfl) ⟨108608, by rfl⟩ : syracuseStep 37071701 = 217217) (by norm_num)
theorem B1928045 : Blo 1283960 1928045 := bbase (se 3 (by rfl) ⟨361508, by rfl⟩ : syracuseStep 1928045 = 723017) (by norm_num)
theorem B1444729 : Blo 1283960 1444729 := bbase (se 2 (by rfl) ⟨541773, by rfl⟩ : syracuseStep 1444729 = 1083547) (by norm_num)
theorem B1928069 : Blo 1283960 1928069 := bbase (se 4 (by rfl) ⟨180756, by rfl⟩ : syracuseStep 1928069 = 361513) (by norm_num)
theorem B1444765 : Blo 1283960 1444765 := bbase (se 3 (by rfl) ⟨270893, by rfl⟩ : syracuseStep 1444765 = 541787) (by norm_num)
theorem B1928093 : Blo 1283960 1928093 := bbase (se 3 (by rfl) ⟨361517, by rfl⟩ : syracuseStep 1928093 = 723035) (by norm_num)
theorem B1928117 : Blo 1283960 1928117 := bbase (se 5 (by rfl) ⟨90380, by rfl⟩ : syracuseStep 1928117 = 180761) (by norm_num)
theorem B1625017 : Blo 1283960 1625017 := bbase (se 2 (by rfl) ⟨609381, by rfl⟩ : syracuseStep 1625017 = 1218763) (by norm_num)
theorem B1444801 : Blo 1283960 1444801 := bbase (se 2 (by rfl) ⟨541800, by rfl⟩ : syracuseStep 1444801 = 1083601) (by norm_num)
theorem B1543117 : Blo 1283960 1543117 := bbase (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) (by norm_num)
theorem B1928141 : Blo 1283960 1928141 := bbase (se 3 (by rfl) ⟨361526, by rfl⟩ : syracuseStep 1928141 = 723053) (by norm_num)
theorem B1444837 : Blo 1283960 1444837 := bbase (se 4 (by rfl) ⟨135453, by rfl⟩ : syracuseStep 1444837 = 270907) (by norm_num)
theorem B1928165 : Blo 1283960 1928165 := bbase (se 4 (by rfl) ⟨180765, by rfl⟩ : syracuseStep 1928165 = 361531) (by norm_num)
theorem B1928189 : Blo 1283960 1928189 := bbase (se 3 (by rfl) ⟨361535, by rfl⟩ : syracuseStep 1928189 = 723071) (by norm_num)
theorem B1829893 : Blo 1283960 1829893 := bbase (se 4 (by rfl) ⟨171552, by rfl⟩ : syracuseStep 1829893 = 343105) (by norm_num)
theorem B1444873 : Blo 1283960 1444873 := bbase (se 2 (by rfl) ⟨541827, by rfl⟩ : syracuseStep 1444873 = 1083655) (by norm_num)
theorem B1928213 : Blo 1283960 1928213 := bbase (se 6 (by rfl) ⟨45192, by rfl⟩ : syracuseStep 1928213 = 90385) (by norm_num)
theorem B1625113 : Blo 1283960 1625113 := bbase (se 2 (by rfl) ⟨609417, by rfl⟩ : syracuseStep 1625113 = 1218835) (by norm_num)
theorem B1952813 : Blo 1283960 1952813 := bbase (se 3 (by rfl) ⟨366152, by rfl⟩ : syracuseStep 1952813 = 732305) (by norm_num)
theorem B1444909 : Blo 1283960 1444909 := bbase (se 3 (by rfl) ⟨270920, by rfl⟩ : syracuseStep 1444909 = 541841) (by norm_num)
theorem B1928237 : Blo 1283960 1928237 := bbase (se 3 (by rfl) ⟨361544, by rfl⟩ : syracuseStep 1928237 = 723089) (by norm_num)
theorem B1928261 : Blo 1283960 1928261 := bbase (se 4 (by rfl) ⟨180774, by rfl⟩ : syracuseStep 1928261 = 361549) (by norm_num)
theorem B1444945 : Blo 1283960 1444945 := bbase (se 2 (by rfl) ⟨541854, by rfl⟩ : syracuseStep 1444945 = 1083709) (by norm_num)
theorem B7318613 : Blo 1283960 7318613 := bbase (se 8 (by rfl) ⟨42882, by rfl⟩ : syracuseStep 7318613 = 85765) (by norm_num)
theorem B1928285 : Blo 1283960 1928285 := bbase (se 3 (by rfl) ⟨361553, by rfl⟩ : syracuseStep 1928285 = 723107) (by norm_num)
theorem B1444981 : Blo 1283960 1444981 := bbase (se 5 (by rfl) ⟨67733, by rfl⟩ : syracuseStep 1444981 = 135467) (by norm_num)
theorem B1928309 : Blo 1283960 1928309 := bbase (se 5 (by rfl) ⟨90389, by rfl⟩ : syracuseStep 1928309 = 180779) (by norm_num)
theorem B1928333 : Blo 1283960 1928333 := bbase (se 3 (by rfl) ⟨361562, by rfl⟩ : syracuseStep 1928333 = 723125) (by norm_num)
theorem B4942997 : Blo 1283960 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B1445017 : Blo 1283960 1445017 := bbase (se 2 (by rfl) ⟨541881, by rfl⟩ : syracuseStep 1445017 = 1083763) (by norm_num)
theorem B1928357 : Blo 1283960 1928357 := bbase (se 4 (by rfl) ⟨180783, by rfl⟩ : syracuseStep 1928357 = 361567) (by norm_num)
theorem B6507701 : Blo 1283960 6507701 := bbase (se 5 (by rfl) ⟨305048, by rfl⟩ : syracuseStep 6507701 = 610097) (by norm_num)
theorem B1445053 : Blo 1283960 1445053 := bbase (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) (by norm_num)
theorem B1928381 : Blo 1283960 1928381 := bbase (se 3 (by rfl) ⟨361571, by rfl⟩ : syracuseStep 1928381 = 723143) (by norm_num)
theorem B1625285 : Blo 1283960 1625285 := bbase (se 4 (by rfl) ⟨152370, by rfl⟩ : syracuseStep 1625285 = 304741) (by norm_num)
theorem B4943045 : Blo 1283960 4943045 := bbase (se 4 (by rfl) ⟨463410, by rfl⟩ : syracuseStep 4943045 = 926821) (by norm_num)
theorem B1928405 : Blo 1283960 1928405 := bbase (se 7 (by rfl) ⟨22598, by rfl⟩ : syracuseStep 1928405 = 45197) (by norm_num)
theorem B1830109 : Blo 1283960 1830109 := bbase (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) (by norm_num)
theorem B1445089 : Blo 1283960 1445089 := bbase (se 2 (by rfl) ⟨541908, by rfl⟩ : syracuseStep 1445089 = 1083817) (by norm_num)
theorem B1928429 : Blo 1283960 1928429 := bbase (se 3 (by rfl) ⟨361580, by rfl⟩ : syracuseStep 1928429 = 723161) (by norm_num)
theorem B2059501 : Blo 1283960 2059501 := bbase (se 3 (by rfl) ⟨386156, by rfl⟩ : syracuseStep 2059501 = 772313) (by norm_num)
theorem B1625341 : Blo 1283960 1625341 := bbase (se 3 (by rfl) ⟨304751, by rfl⟩ : syracuseStep 1625341 = 609503) (by norm_num)
theorem B1445125 : Blo 1283960 1445125 := bbase (se 4 (by rfl) ⟨135480, by rfl⟩ : syracuseStep 1445125 = 270961) (by norm_num)
theorem B4336901 : Blo 1283960 4336901 := bbase (se 4 (by rfl) ⟨406584, by rfl⟩ : syracuseStep 4336901 = 813169) (by norm_num)
theorem B1928453 : Blo 1283960 1928453 := bbase (se 4 (by rfl) ⟨180792, by rfl⟩ : syracuseStep 1928453 = 361585) (by norm_num)
theorem B1928477 : Blo 1283960 1928477 := bbase (se 3 (by rfl) ⟨361589, by rfl⟩ : syracuseStep 1928477 = 723179) (by norm_num)
theorem B1445161 : Blo 1283960 1445161 := bbase (se 2 (by rfl) ⟨541935, by rfl⟩ : syracuseStep 1445161 = 1083871) (by norm_num)
theorem B1928501 : Blo 1283960 1928501 := bbase (se 5 (by rfl) ⟨90398, by rfl⟩ : syracuseStep 1928501 = 180797) (by norm_num)
theorem B1445197 : Blo 1283960 1445197 := bbase (se 3 (by rfl) ⟨270974, by rfl⟩ : syracuseStep 1445197 = 541949) (by norm_num)
theorem B1543501 : Blo 1283960 1543501 := bbase (se 3 (by rfl) ⟨289406, by rfl⟩ : syracuseStep 1543501 = 578813) (by norm_num)
theorem B1928525 : Blo 1283960 1928525 := bbase (se 3 (by rfl) ⟨361598, by rfl⟩ : syracuseStep 1928525 = 723197) (by norm_num)
theorem B1625437 : Blo 1283960 1625437 := bbase (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) (by norm_num)
theorem B1928549 : Blo 1283960 1928549 := bbase (se 4 (by rfl) ⟨180801, by rfl⟩ : syracuseStep 1928549 = 361603) (by norm_num)
theorem B1371497 : Blo 1283960 1371497 := bbase (se 2 (by rfl) ⟨514311, by rfl⟩ : syracuseStep 1371497 = 1028623) (by norm_num)
theorem B1445233 : Blo 1283960 1445233 := bbase (se 2 (by rfl) ⟨541962, by rfl⟩ : syracuseStep 1445233 = 1083925) (by norm_num)
theorem B8228213 : Blo 1283960 8228213 := bbase (se 5 (by rfl) ⟨385697, by rfl⟩ : syracuseStep 8228213 = 771395) (by norm_num)
theorem B1928573 : Blo 1283960 1928573 := bbase (se 3 (by rfl) ⟨361607, by rfl⟩ : syracuseStep 1928573 = 723215) (by norm_num)
theorem B3657109 : Blo 1283960 3657109 := bbase (se 6 (by rfl) ⟨85713, by rfl⟩ : syracuseStep 3657109 = 171427) (by norm_num)
theorem B1445269 : Blo 1283960 1445269 := bbase (se 6 (by rfl) ⟨33873, by rfl⟩ : syracuseStep 1445269 = 67747) (by norm_num)
theorem B1928597 : Blo 1283960 1928597 := bbase (se 6 (by rfl) ⟨45201, by rfl⟩ : syracuseStep 1928597 = 90403) (by norm_num)
theorem B1928621 : Blo 1283960 1928621 := bbase (se 3 (by rfl) ⟨361616, by rfl⟩ : syracuseStep 1928621 = 723233) (by norm_num)
theorem B1445305 : Blo 1283960 1445305 := bbase (se 2 (by rfl) ⟨541989, by rfl⟩ : syracuseStep 1445305 = 1083979) (by norm_num)
theorem B1928645 : Blo 1283960 1928645 := bbase (se 4 (by rfl) ⟨180810, by rfl⟩ : syracuseStep 1928645 = 361621) (by norm_num)
theorem B1445341 : Blo 1283960 1445341 := bbase (se 3 (by rfl) ⟨271001, by rfl⟩ : syracuseStep 1445341 = 542003) (by norm_num)
theorem B1928669 : Blo 1283960 1928669 := bbase (se 3 (by rfl) ⟨361625, by rfl⟩ : syracuseStep 1928669 = 723251) (by norm_num)
theorem B1928693 : Blo 1283960 1928693 := bbase (se 5 (by rfl) ⟨90407, by rfl⟩ : syracuseStep 1928693 = 180815) (by norm_num)
theorem B1445377 : Blo 1283960 1445377 := bbase (se 2 (by rfl) ⟨542016, by rfl⟩ : syracuseStep 1445377 = 1084033) (by norm_num)
theorem B1625609 : Blo 1283960 1625609 := bbase (se 2 (by rfl) ⟨609603, by rfl⟩ : syracuseStep 1625609 = 1219207) (by norm_num)
theorem B1928717 : Blo 1283960 1928717 := bbase (se 3 (by rfl) ⟨361634, by rfl⟩ : syracuseStep 1928717 = 723269) (by norm_num)
theorem B5213717 : Blo 1283960 5213717 := bbase (se 6 (by rfl) ⟨122196, by rfl⟩ : syracuseStep 5213717 = 244393) (by norm_num)
theorem B1445413 : Blo 1283960 1445413 := bbase (se 4 (by rfl) ⟨135507, by rfl⟩ : syracuseStep 1445413 = 271015) (by norm_num)
theorem B1928741 : Blo 1283960 1928741 := bbase (se 4 (by rfl) ⟨180819, by rfl⟩ : syracuseStep 1928741 = 361639) (by norm_num)
theorem B1928765 : Blo 1283960 1928765 := bbase (se 3 (by rfl) ⟨361643, by rfl⟩ : syracuseStep 1928765 = 723287) (by norm_num)
theorem B1625665 : Blo 1283960 1625665 := bbase (se 2 (by rfl) ⟨609624, by rfl⟩ : syracuseStep 1625665 = 1219249) (by norm_num)
theorem B1445449 : Blo 1283960 1445449 := bbase (se 2 (by rfl) ⟨542043, by rfl⟩ : syracuseStep 1445449 = 1084087) (by norm_num)
theorem B1830485 : Blo 1283960 1830485 := bbase (se 8 (by rfl) ⟨10725, by rfl⟩ : syracuseStep 1830485 = 21451) (by norm_num)
theorem B1928789 : Blo 1283960 1928789 := bbase (se 8 (by rfl) ⟨11301, by rfl⟩ : syracuseStep 1928789 = 22603) (by norm_num)
theorem B1371745 : Blo 1283960 1371745 := bbase (se 2 (by rfl) ⟨514404, by rfl⟩ : syracuseStep 1371745 = 1028809) (by norm_num)
theorem B1445485 : Blo 1283960 1445485 := bbase (se 3 (by rfl) ⟨271028, by rfl⟩ : syracuseStep 1445485 = 542057) (by norm_num)
theorem B1928813 : Blo 1283960 1928813 := bbase (se 3 (by rfl) ⟨361652, by rfl⟩ : syracuseStep 1928813 = 723305) (by norm_num)
theorem B1928837 : Blo 1283960 1928837 := bbase (se 4 (by rfl) ⟨180828, by rfl⟩ : syracuseStep 1928837 = 361657) (by norm_num)
theorem B1445521 : Blo 1283960 1445521 := bbase (se 2 (by rfl) ⟨542070, by rfl⟩ : syracuseStep 1445521 = 1084141) (by norm_num)
theorem B1928861 : Blo 1283960 1928861 := bbase (se 3 (by rfl) ⟨361661, by rfl⟩ : syracuseStep 1928861 = 723323) (by norm_num)
theorem B1625761 : Blo 1283960 1625761 := bbase (se 2 (by rfl) ⟨609660, by rfl⟩ : syracuseStep 1625761 = 1219321) (by norm_num)
theorem B1445557 : Blo 1283960 1445557 := bbase (se 5 (by rfl) ⟨67760, by rfl⟩ : syracuseStep 1445557 = 135521) (by norm_num)
theorem B4337333 : Blo 1283960 4337333 := bbase (se 5 (by rfl) ⟨203312, by rfl⟩ : syracuseStep 4337333 = 406625) (by norm_num)
theorem B1928885 : Blo 1283960 1928885 := bbase (se 5 (by rfl) ⟨90416, by rfl⟩ : syracuseStep 1928885 = 180833) (by norm_num)
theorem B1928909 : Blo 1283960 1928909 := bbase (se 3 (by rfl) ⟨361670, by rfl⟩ : syracuseStep 1928909 = 723341) (by norm_num)
theorem B1445593 : Blo 1283960 1445593 := bbase (se 2 (by rfl) ⟨542097, by rfl⟩ : syracuseStep 1445593 = 1084195) (by norm_num)
theorem B4116197 : Blo 1283960 4116197 := bbase (se 4 (by rfl) ⟨385893, by rfl⟩ : syracuseStep 4116197 = 771787) (by norm_num)
theorem B1928933 : Blo 1283960 1928933 := bbase (se 4 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 1928933 = 361675) (by norm_num)
theorem B1445629 : Blo 1283960 1445629 := bbase (se 3 (by rfl) ⟨271055, by rfl⟩ : syracuseStep 1445629 = 542111) (by norm_num)
theorem B1445665 : Blo 1283960 1445665 := bbase (se 2 (by rfl) ⟨542124, by rfl⟩ : syracuseStep 1445665 = 1084249) (by norm_num)
theorem B2928437 : Blo 1283960 2928437 := bbase (se 5 (by rfl) ⟨137270, by rfl⟩ : syracuseStep 2928437 = 274541) (by norm_num)
theorem B1445701 : Blo 1283960 1445701 := bbase (se 4 (by rfl) ⟨135534, by rfl⟩ : syracuseStep 1445701 = 271069) (by norm_num)
theorem B5492549 : Blo 1283960 5492549 := bbase (se 4 (by rfl) ⟨514926, by rfl⟩ : syracuseStep 5492549 = 1029853) (by norm_num)
theorem B1625933 : Blo 1283960 1625933 := bbase (se 3 (by rfl) ⟨304862, by rfl⟩ : syracuseStep 1625933 = 609725) (by norm_num)
theorem B35163989 : Blo 1283960 35163989 := bbase (se 9 (by rfl) ⟨103019, by rfl⟩ : syracuseStep 35163989 = 206039) (by norm_num)
theorem B1445737 : Blo 1283960 1445737 := bbase (se 2 (by rfl) ⟨542151, by rfl⟩ : syracuseStep 1445737 = 1084303) (by norm_num)
theorem B1625989 : Blo 1283960 1625989 := bbase (se 4 (by rfl) ⟨152436, by rfl⟩ : syracuseStep 1625989 = 304873) (by norm_num)
theorem B1445773 : Blo 1283960 1445773 := bbase (se 3 (by rfl) ⟨271082, by rfl⟩ : syracuseStep 1445773 = 542165) (by norm_num)
theorem B25022357 : Blo 1283960 25022357 := bbase (se 6 (by rfl) ⟨586461, by rfl⟩ : syracuseStep 25022357 = 1172923) (by norm_num)
theorem B1445809 : Blo 1283960 1445809 := bbase (se 2 (by rfl) ⟨542178, by rfl⟩ : syracuseStep 1445809 = 1084357) (by norm_num)
theorem B2166709 : Blo 1283960 2166709 := bbase (se 5 (by rfl) ⟨101564, by rfl⟩ : syracuseStep 2166709 = 203129) (by norm_num)
theorem B1445845 : Blo 1283960 1445845 := bbase (se 7 (by rfl) ⟨16943, by rfl⟩ : syracuseStep 1445845 = 33887) (by norm_num)
theorem B1626085 : Blo 1283960 1626085 := bbase (se 4 (by rfl) ⟨152445, by rfl⟩ : syracuseStep 1626085 = 304891) (by norm_num)
theorem B2928629 : Blo 1283960 2928629 := bbase (se 5 (by rfl) ⟨137279, by rfl⟩ : syracuseStep 2928629 = 274559) (by norm_num)
theorem B1445881 : Blo 1283960 1445881 := bbase (se 2 (by rfl) ⟨542205, by rfl⟩ : syracuseStep 1445881 = 1084411) (by norm_num)
theorem B1544189 : Blo 1283960 1544189 := bbase (se 3 (by rfl) ⟨289535, by rfl⟩ : syracuseStep 1544189 = 579071) (by norm_num)
theorem B2166797 : Blo 1283960 2166797 := bbase (se 3 (by rfl) ⟨406274, by rfl⟩ : syracuseStep 2166797 = 812549) (by norm_num)
theorem B1372189 : Blo 1283960 1372189 := bbase (se 3 (by rfl) ⟨257285, by rfl⟩ : syracuseStep 1372189 = 514571) (by norm_num)
theorem B1445917 : Blo 1283960 1445917 := bbase (se 3 (by rfl) ⟨271109, by rfl⟩ : syracuseStep 1445917 = 542219) (by norm_num)
theorem B1445953 : Blo 1283960 1445953 := bbase (se 2 (by rfl) ⟨542232, by rfl⟩ : syracuseStep 1445953 = 1084465) (by norm_num)
theorem B1372249 : Blo 1283960 1372249 := bbase (se 2 (by rfl) ⟨514593, by rfl⟩ : syracuseStep 1372249 = 1029187) (by norm_num)
theorem B4337765 : Blo 1283960 4337765 := bbase (se 4 (by rfl) ⟨406665, by rfl⟩ : syracuseStep 4337765 = 813331) (by norm_num)
theorem B1445989 : Blo 1283960 1445989 := bbase (se 4 (by rfl) ⟨135561, by rfl⟩ : syracuseStep 1445989 = 271123) (by norm_num)
theorem B2199653 : Blo 1283960 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B1446025 : Blo 1283960 1446025 := bbase (se 2 (by rfl) ⟨542259, by rfl⟩ : syracuseStep 1446025 = 1084519) (by norm_num)
theorem B2166925 : Blo 1283960 2166925 := bbase (se 3 (by rfl) ⟨406298, by rfl⟩ : syracuseStep 2166925 = 812597) (by norm_num)
theorem B1626257 : Blo 1283960 1626257 := bbase (se 2 (by rfl) ⟨609846, by rfl⟩ : syracuseStep 1626257 = 1219693) (by norm_num)
theorem B1446061 : Blo 1283960 1446061 := bbase (se 3 (by rfl) ⟨271136, by rfl⟩ : syracuseStep 1446061 = 542273) (by norm_num)
theorem B1626313 : Blo 1283960 1626313 := bbase (se 2 (by rfl) ⟨609867, by rfl⟩ : syracuseStep 1626313 = 1219735) (by norm_num)
theorem B1446097 : Blo 1283960 1446097 := bbase (se 2 (by rfl) ⟨542286, by rfl⟩ : syracuseStep 1446097 = 1084573) (by norm_num)
theorem B2167013 : Blo 1283960 2167013 := bbase (se 4 (by rfl) ⟨203157, by rfl⟩ : syracuseStep 2167013 = 406315) (by norm_num)
theorem B1446133 : Blo 1283960 1446133 := bbase (se 5 (by rfl) ⟨67787, by rfl⟩ : syracuseStep 1446133 = 135575) (by norm_num)
theorem B1446169 : Blo 1283960 1446169 := bbase (se 2 (by rfl) ⟨542313, by rfl⟩ : syracuseStep 1446169 = 1084627) (by norm_num)
theorem B1626409 : Blo 1283960 1626409 := bbase (se 2 (by rfl) ⟨609903, by rfl⟩ : syracuseStep 1626409 = 1219807) (by norm_num)
theorem B1446205 : Blo 1283960 1446205 := bbase (se 3 (by rfl) ⟨271163, by rfl⟩ : syracuseStep 1446205 = 542327) (by norm_num)
theorem B19796309 : Blo 1283960 19796309 := bbase (se 10 (by rfl) ⟨28998, by rfl⟩ : syracuseStep 19796309 = 57997) (by norm_num)
theorem B1446241 : Blo 1283960 1446241 := bbase (se 2 (by rfl) ⟨542340, by rfl⟩ : syracuseStep 1446241 = 1084681) (by norm_num)
theorem B2167141 : Blo 1283960 2167141 := bbase (se 4 (by rfl) ⟨203169, by rfl⟩ : syracuseStep 2167141 = 406339) (by norm_num)
theorem B1446277 : Blo 1283960 1446277 := bbase (se 4 (by rfl) ⟨135588, by rfl⟩ : syracuseStep 1446277 = 271177) (by norm_num)
theorem B1372565 : Blo 1283960 1372565 := bbase (se 6 (by rfl) ⟨32169, by rfl⟩ : syracuseStep 1372565 = 64339) (by norm_num)
theorem B1446313 : Blo 1283960 1446313 := bbase (se 2 (by rfl) ⟨542367, by rfl⟩ : syracuseStep 1446313 = 1084735) (by norm_num)
theorem B2167229 : Blo 1283960 2167229 := bbase (se 3 (by rfl) ⟨406355, by rfl⟩ : syracuseStep 2167229 = 812711) (by norm_num)
theorem B6508997 : Blo 1283960 6508997 := bbase (se 4 (by rfl) ⟨610218, by rfl⟩ : syracuseStep 6508997 = 1220437) (by norm_num)
theorem B1446349 : Blo 1283960 1446349 := bbase (se 3 (by rfl) ⟨271190, by rfl⟩ : syracuseStep 1446349 = 542381) (by norm_num)
theorem B1626581 : Blo 1283960 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B3658213 : Blo 1283960 3658213 := bbase (se 4 (by rfl) ⟨342957, by rfl⟩ : syracuseStep 3658213 = 685915) (by norm_num)
theorem B1446385 : Blo 1283960 1446385 := bbase (se 2 (by rfl) ⟨542394, by rfl⟩ : syracuseStep 1446385 = 1084789) (by norm_num)
theorem B1626637 : Blo 1283960 1626637 := bbase (se 3 (by rfl) ⟨304994, by rfl⟩ : syracuseStep 1626637 = 609989) (by norm_num)
theorem B4338197 : Blo 1283960 4338197 := bbase (se 6 (by rfl) ⟨101676, by rfl⟩ : syracuseStep 4338197 = 203353) (by norm_num)
theorem B1446421 : Blo 1283960 1446421 := bbase (se 6 (by rfl) ⟨33900, by rfl⟩ : syracuseStep 1446421 = 67801) (by norm_num)
theorem B2437685 : Blo 1283960 2437685 := bbase (se 5 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 2437685 = 228533) (by norm_num)
theorem B1446457 : Blo 1283960 1446457 := bbase (se 2 (by rfl) ⟨542421, by rfl⟩ : syracuseStep 1446457 = 1084843) (by norm_num)
theorem B2167357 : Blo 1283960 2167357 := bbase (se 3 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 2167357 = 812759) (by norm_num)
theorem B1544789 : Blo 1283960 1544789 := bbase (se 8 (by rfl) ⟨9051, by rfl⟩ : syracuseStep 1544789 = 18103) (by norm_num)
theorem B1446493 : Blo 1283960 1446493 := bbase (se 3 (by rfl) ⟨271217, by rfl⟩ : syracuseStep 1446493 = 542435) (by norm_num)
theorem B1626733 : Blo 1283960 1626733 := bbase (se 3 (by rfl) ⟨305012, by rfl⟩ : syracuseStep 1626733 = 610025) (by norm_num)
theorem B2314877 : Blo 1283960 2314877 := bbase (se 3 (by rfl) ⟨434039, by rfl⟩ : syracuseStep 2314877 = 868079) (by norm_num)
theorem B1446529 : Blo 1283960 1446529 := bbase (se 2 (by rfl) ⟨542448, by rfl⟩ : syracuseStep 1446529 = 1084897) (by norm_num)
theorem B2167445 : Blo 1283960 2167445 := bbase (se 6 (by rfl) ⟨50799, by rfl⟩ : syracuseStep 2167445 = 101599) (by norm_num)
theorem B1446565 : Blo 1283960 1446565 := bbase (se 4 (by rfl) ⟨135615, by rfl⟩ : syracuseStep 1446565 = 271231) (by norm_num)
theorem B5943989 : Blo 1283960 5943989 := bbase (se 5 (by rfl) ⟨278624, by rfl⟩ : syracuseStep 5943989 = 557249) (by norm_num)
theorem B2347717 : Blo 1283960 2347717 := bbase (se 4 (by rfl) ⟨220098, by rfl⟩ : syracuseStep 2347717 = 440197) (by norm_num)
theorem B1446601 : Blo 1283960 1446601 := bbase (se 2 (by rfl) ⟨542475, by rfl⟩ : syracuseStep 1446601 = 1084951) (by norm_num)
theorem B4879061 : Blo 1283960 4879061 := bbase (se 7 (by rfl) ⟨57176, by rfl⟩ : syracuseStep 4879061 = 114353) (by norm_num)
theorem B1446637 : Blo 1283960 1446637 := bbase (se 3 (by rfl) ⟨271244, by rfl⟩ : syracuseStep 1446637 = 542489) (by norm_num)
theorem B1446673 : Blo 1283960 1446673 := bbase (se 2 (by rfl) ⟨542502, by rfl⟩ : syracuseStep 1446673 = 1085005) (by norm_num)
theorem B2167573 : Blo 1283960 2167573 := bbase (se 6 (by rfl) ⟨50802, by rfl⟩ : syracuseStep 2167573 = 101605) (by norm_num)
theorem B1626905 : Blo 1283960 1626905 := bbase (se 2 (by rfl) ⟨610089, by rfl⟩ : syracuseStep 1626905 = 1220179) (by norm_num)
theorem B5206837 : Blo 1283960 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B1626961 : Blo 1283960 1626961 := bbase (se 2 (by rfl) ⟨610110, by rfl⟩ : syracuseStep 1626961 = 1220221) (by norm_num)
theorem B1373009 : Blo 1283960 1373009 := bbase (se 2 (by rfl) ⟨514878, by rfl⟩ : syracuseStep 1373009 = 1029757) (by norm_num)
theorem B3085157 : Blo 1283960 3085157 := bbase (se 4 (by rfl) ⟨289233, by rfl⟩ : syracuseStep 3085157 = 578467) (by norm_num)
theorem B6501221 : Blo 1283960 6501221 := bbase (se 4 (by rfl) ⟨609489, by rfl⟩ : syracuseStep 6501221 = 1218979) (by norm_num)
theorem B4633445 : Blo 1283960 4633445 := bbase (se 4 (by rfl) ⟨434385, by rfl⟩ : syracuseStep 4633445 = 868771) (by norm_num)
theorem B2167661 : Blo 1283960 2167661 := bbase (se 3 (by rfl) ⟨406436, by rfl⟩ : syracuseStep 2167661 = 812873) (by norm_num)
theorem B1373069 : Blo 1283960 1373069 := bbase (se 3 (by rfl) ⟨257450, by rfl⟩ : syracuseStep 1373069 = 514901) (by norm_num)
theorem B1627057 : Blo 1283960 1627057 := bbase (se 2 (by rfl) ⟨610146, by rfl⟩ : syracuseStep 1627057 = 1220293) (by norm_num)
theorem B6173621 : Blo 1283960 6173621 := bbase (se 5 (by rfl) ⟨289388, by rfl⟩ : syracuseStep 6173621 = 578777) (by norm_num)
theorem B4338629 : Blo 1283960 4338629 := bbase (se 4 (by rfl) ⟨406746, by rfl⟩ : syracuseStep 4338629 = 813493) (by norm_num)
theorem B2167789 : Blo 1283960 2167789 := bbase (se 3 (by rfl) ⟨406460, by rfl⟩ : syracuseStep 2167789 = 812921) (by norm_num)
theorem B4879349 : Blo 1283960 4879349 := bbase (se 5 (by rfl) ⟨228719, by rfl⟩ : syracuseStep 4879349 = 457439) (by norm_num)
theorem B1373197 : Blo 1283960 1373197 := bbase (se 3 (by rfl) ⟨257474, by rfl⟩ : syracuseStep 1373197 = 514949) (by norm_num)
theorem B2167877 : Blo 1283960 2167877 := bbase (se 4 (by rfl) ⟨203238, by rfl⟩ : syracuseStep 2167877 = 406477) (by norm_num)
theorem B40096853 : Blo 1283960 40096853 := bbase (se 8 (by rfl) ⟨234942, by rfl⟩ : syracuseStep 40096853 = 469885) (by norm_num)
theorem B1627229 : Blo 1283960 1627229 := bbase (se 3 (by rfl) ⟨305105, by rfl⟩ : syracuseStep 1627229 = 610211) (by norm_num)
theorem B5944421 : Blo 1283960 5944421 := bbase (se 4 (by rfl) ⟨557289, by rfl⟩ : syracuseStep 5944421 = 1114579) (by norm_num)
theorem B1627285 : Blo 1283960 1627285 := bbase (se 6 (by rfl) ⟨38139, by rfl⟩ : syracuseStep 1627285 = 76279) (by norm_num)
theorem B2168005 : Blo 1283960 2168005 := bbase (se 4 (by rfl) ⟨203250, by rfl⟩ : syracuseStep 2168005 = 406501) (by norm_num)
theorem B1627381 : Blo 1283960 1627381 := bbase (se 5 (by rfl) ⟨76283, by rfl⟩ : syracuseStep 1627381 = 152567) (by norm_num)
theorem B4945157 : Blo 1283960 4945157 := bbase (se 4 (by rfl) ⟨463608, by rfl⟩ : syracuseStep 4945157 = 927217) (by norm_num)
theorem B2888981 : Blo 1283960 2888981 := bbase (se 6 (by rfl) ⟨67710, by rfl⟩ : syracuseStep 2888981 = 135421) (by norm_num)
theorem B9385237 : Blo 1283960 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B2168093 : Blo 1283960 2168093 := bbase (se 3 (by rfl) ⟨406517, by rfl⟩ : syracuseStep 2168093 = 813035) (by norm_num)
theorem B3470629 : Blo 1283960 3470629 := bbase (se 4 (by rfl) ⟨325371, by rfl⟩ : syracuseStep 3470629 = 650743) (by norm_num)
theorem B2438437 : Blo 1283960 2438437 := bbase (se 4 (by rfl) ⟨228603, by rfl⟩ : syracuseStep 2438437 = 457207) (by norm_num)
theorem B5862709 : Blo 1283960 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B16463189 : Blo 1283960 16463189 := bbase (se 13 (by rfl) ⟨3014, by rfl⟩ : syracuseStep 16463189 = 6029) (by norm_num)
theorem B2889053 : Blo 1283960 2889053 := bbase (se 3 (by rfl) ⟨541697, by rfl⟩ : syracuseStep 2889053 = 1083395) (by norm_num)
theorem B4339061 : Blo 1283960 4339061 := bbase (se 5 (by rfl) ⟨203393, by rfl⟩ : syracuseStep 4339061 = 406787) (by norm_num)
theorem B2168221 : Blo 1283960 2168221 := bbase (se 3 (by rfl) ⟨406541, by rfl⟩ : syracuseStep 2168221 = 813083) (by norm_num)
theorem B2889125 : Blo 1283960 2889125 := bbase (se 4 (by rfl) ⟨270855, by rfl⟩ : syracuseStep 2889125 = 541711) (by norm_num)
theorem B2438581 : Blo 1283960 2438581 := bbase (se 5 (by rfl) ⟨114308, by rfl⟩ : syracuseStep 2438581 = 228617) (by norm_num)
theorem B2889197 : Blo 1283960 2889197 := bbase (se 3 (by rfl) ⟨541724, by rfl⟩ : syracuseStep 2889197 = 1083449) (by norm_num)
theorem B2168309 : Blo 1283960 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B4118053 : Blo 1283960 4118053 := bbase (se 4 (by rfl) ⟨386067, by rfl⟩ : syracuseStep 4118053 = 772135) (by norm_num)
theorem B2889269 : Blo 1283960 2889269 := bbase (se 5 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 2889269 = 270869) (by norm_num)
theorem B2438741 : Blo 1283960 2438741 := bbase (se 8 (by rfl) ⟨14289, by rfl⟩ : syracuseStep 2438741 = 28579) (by norm_num)
theorem B2168437 : Blo 1283960 2168437 := bbase (se 5 (by rfl) ⟨101645, by rfl⟩ : syracuseStep 2168437 = 203291) (by norm_num)
theorem B2889341 : Blo 1283960 2889341 := bbase (se 3 (by rfl) ⟨541751, by rfl⟩ : syracuseStep 2889341 = 1083503) (by norm_num)
theorem B2889413 : Blo 1283960 2889413 := bbase (se 4 (by rfl) ⟨270882, by rfl⟩ : syracuseStep 2889413 = 541765) (by norm_num)
theorem B2168525 : Blo 1283960 2168525 := bbase (se 3 (by rfl) ⟨406598, by rfl⟩ : syracuseStep 2168525 = 813197) (by norm_num)
theorem B2438885 : Blo 1283960 2438885 := bbase (se 4 (by rfl) ⟨228645, by rfl⟩ : syracuseStep 2438885 = 457291) (by norm_num)
theorem B2889485 : Blo 1283960 2889485 := bbase (se 3 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 2889485 = 1083557) (by norm_num)
theorem B4339493 : Blo 1283960 4339493 := bbase (se 4 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 4339493 = 813655) (by norm_num)
theorem B3708725 : Blo 1283960 3708725 := bbase (se 5 (by rfl) ⟨173846, by rfl⟩ : syracuseStep 3708725 = 347693) (by norm_num)
theorem B2168653 : Blo 1283960 2168653 := bbase (se 3 (by rfl) ⟨406622, by rfl⟩ : syracuseStep 2168653 = 813245) (by norm_num)
theorem B7313237 : Blo 1283960 7313237 := bbase (se 9 (by rfl) ⟨21425, by rfl⟩ : syracuseStep 7313237 = 42851) (by norm_num)
theorem B2889557 : Blo 1283960 2889557 := bbase (se 9 (by rfl) ⟨8465, by rfl⟩ : syracuseStep 2889557 = 16931) (by norm_num)
theorem B2889629 : Blo 1283960 2889629 := bbase (se 3 (by rfl) ⟨541805, by rfl⟩ : syracuseStep 2889629 = 1083611) (by norm_num)
theorem B2168741 : Blo 1283960 2168741 := bbase (se 4 (by rfl) ⟨203319, by rfl⟩ : syracuseStep 2168741 = 406639) (by norm_num)
theorem B3659717 : Blo 1283960 3659717 := bbase (se 4 (by rfl) ⟨343098, by rfl⟩ : syracuseStep 3659717 = 686197) (by norm_num)
theorem B2889701 : Blo 1283960 2889701 := bbase (se 4 (by rfl) ⟨270909, by rfl⟩ : syracuseStep 2889701 = 541819) (by norm_num)
theorem B3250165 : Blo 1283960 3250165 := bbase (se 5 (by rfl) ⟨152351, by rfl⟩ : syracuseStep 3250165 = 304703) (by norm_num)
theorem B2439173 : Blo 1283960 2439173 := bbase (se 4 (by rfl) ⟨228672, by rfl⟩ : syracuseStep 2439173 = 457345) (by norm_num)
theorem B2742293 : Blo 1283960 2742293 := bbase (se 6 (by rfl) ⟨64272, by rfl⟩ : syracuseStep 2742293 = 128545) (by norm_num)
theorem B2168869 : Blo 1283960 2168869 := bbase (se 4 (by rfl) ⟨203331, by rfl⟩ : syracuseStep 2168869 = 406663) (by norm_num)
theorem B2889773 : Blo 1283960 2889773 := bbase (se 3 (by rfl) ⟨541832, by rfl⟩ : syracuseStep 2889773 = 1083665) (by norm_num)
theorem B2316341 : Blo 1283960 2316341 := bbase (se 5 (by rfl) ⟨108578, by rfl⟩ : syracuseStep 2316341 = 217157) (by norm_num)
theorem B3250277 : Blo 1283960 3250277 := bbase (se 4 (by rfl) ⟨304713, by rfl⟩ : syracuseStep 3250277 = 609427) (by norm_num)
theorem B1464437 : Blo 1283960 1464437 := bbase (se 5 (by rfl) ⟨68645, by rfl⟩ : syracuseStep 1464437 = 137291) (by norm_num)
theorem B2889845 : Blo 1283960 2889845 := bbase (se 5 (by rfl) ⟨135461, by rfl⟩ : syracuseStep 2889845 = 270923) (by norm_num)
theorem B6502517 : Blo 1283960 6502517 := bbase (se 5 (by rfl) ⟨304805, by rfl⟩ : syracuseStep 6502517 = 609611) (by norm_num)
theorem B2168957 : Blo 1283960 2168957 := bbase (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) (by norm_num)
theorem B4880533 : Blo 1283960 4880533 := bbase (se 6 (by rfl) ⟨114387, by rfl⟩ : syracuseStep 4880533 = 228775) (by norm_num)
theorem B2439325 : Blo 1283960 2439325 := bbase (se 3 (by rfl) ⟨457373, by rfl⟩ : syracuseStep 2439325 = 914747) (by norm_num)
theorem B5486773 : Blo 1283960 5486773 := bbase (se 5 (by rfl) ⟨257192, by rfl⟩ : syracuseStep 5486773 = 514385) (by norm_num)
theorem B2889917 : Blo 1283960 2889917 := bbase (se 3 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 2889917 = 1083719) (by norm_num)
theorem B1390789 : Blo 1283960 1390789 := bbase (se 4 (by rfl) ⟨130386, by rfl⟩ : syracuseStep 1390789 = 260773) (by norm_num)
theorem B4339925 : Blo 1283960 4339925 := bbase (se 7 (by rfl) ⟨50858, by rfl⟩ : syracuseStep 4339925 = 101717) (by norm_num)
theorem B2169085 : Blo 1283960 2169085 := bbase (se 3 (by rfl) ⟨406703, by rfl⟩ : syracuseStep 2169085 = 813407) (by norm_num)
theorem B2889989 : Blo 1283960 2889989 := bbase (se 4 (by rfl) ⟨270936, by rfl⟩ : syracuseStep 2889989 = 541873) (by norm_num)
theorem B3250469 : Blo 1283960 3250469 := bbase (se 4 (by rfl) ⟨304731, by rfl⟩ : syracuseStep 3250469 = 609463) (by norm_num)
theorem B2890061 : Blo 1283960 2890061 := bbase (se 3 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 2890061 = 1083773) (by norm_num)
theorem B2169173 : Blo 1283960 2169173 := bbase (se 10 (by rfl) ⟨3177, by rfl⟩ : syracuseStep 2169173 = 6355) (by norm_num)
theorem B6256997 : Blo 1283960 6256997 := bbase (se 4 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 6256997 = 1173187) (by norm_num)
theorem B2742653 : Blo 1283960 2742653 := bbase (se 3 (by rfl) ⟨514247, by rfl⟩ : syracuseStep 2742653 = 1028495) (by norm_num)
theorem B2890133 : Blo 1283960 2890133 := bbase (se 6 (by rfl) ⟨67737, by rfl⟩ : syracuseStep 2890133 = 135475) (by norm_num)
theorem B9763253 : Blo 1283960 9763253 := bbase (se 5 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 9763253 = 915305) (by norm_num)
theorem B1391033 : Blo 1283960 1391033 := bbase (se 2 (by rfl) ⟨521637, by rfl⟩ : syracuseStep 1391033 = 1043275) (by norm_num)
theorem B4880837 : Blo 1283960 4880837 := bbase (se 4 (by rfl) ⟨457578, by rfl⟩ : syracuseStep 4880837 = 915157) (by norm_num)
theorem B2439629 : Blo 1283960 2439629 := bbase (se 3 (by rfl) ⟨457430, by rfl⟩ : syracuseStep 2439629 = 914861) (by norm_num)
theorem B2783693 : Blo 1283960 2783693 := bbase (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) (by norm_num)
theorem B2169301 : Blo 1283960 2169301 := bbase (se 7 (by rfl) ⟨25421, by rfl⟩ : syracuseStep 2169301 = 50843) (by norm_num)
theorem B2890205 : Blo 1283960 2890205 := bbase (se 3 (by rfl) ⟨541913, by rfl⟩ : syracuseStep 2890205 = 1083827) (by norm_num)
theorem B10975733 : Blo 1283960 10975733 := bbase (se 5 (by rfl) ⟨514487, by rfl⟩ : syracuseStep 10975733 = 1028975) (by norm_num)
theorem B3389957 : Blo 1283960 3389957 := bbase (se 4 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 3389957 = 635617) (by norm_num)
theorem B1391137 : Blo 1283960 1391137 := bbase (se 2 (by rfl) ⟨521676, by rfl⟩ : syracuseStep 1391137 = 1043353) (by norm_num)
theorem B2890277 : Blo 1283960 2890277 := bbase (se 4 (by rfl) ⟨270963, by rfl⟩ : syracuseStep 2890277 = 541927) (by norm_num)
theorem B2169389 : Blo 1283960 2169389 := bbase (se 3 (by rfl) ⟨406760, by rfl⟩ : syracuseStep 2169389 = 813521) (by norm_num)
theorem B2603573 : Blo 1283960 2603573 := bbase (se 5 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 2603573 = 244085) (by norm_num)
theorem B12352085 : Blo 1283960 12352085 := bbase (se 8 (by rfl) ⟨72375, by rfl⟩ : syracuseStep 12352085 = 144751) (by norm_num)
theorem B2890349 : Blo 1283960 2890349 := bbase (se 3 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 2890349 = 1083881) (by norm_num)
theorem B3250813 : Blo 1283960 3250813 := bbase (se 3 (by rfl) ⟨609527, by rfl⟩ : syracuseStep 3250813 = 1219055) (by norm_num)
theorem B2169517 : Blo 1283960 2169517 := bbase (se 3 (by rfl) ⟨406784, by rfl⟩ : syracuseStep 2169517 = 813569) (by norm_num)
theorem B2890421 : Blo 1283960 2890421 := bbase (se 5 (by rfl) ⟨135488, by rfl⟩ : syracuseStep 2890421 = 270977) (by norm_num)
theorem B3250925 : Blo 1283960 3250925 := bbase (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) (by norm_num)
theorem B2890493 : Blo 1283960 2890493 := bbase (se 3 (by rfl) ⟨541967, by rfl⟩ : syracuseStep 2890493 = 1083935) (by norm_num)
theorem B2169605 : Blo 1283960 2169605 := bbase (se 4 (by rfl) ⟨203400, by rfl⟩ : syracuseStep 2169605 = 406801) (by norm_num)
theorem B1735445 : Blo 1283960 1735445 := bbase (se 6 (by rfl) ⟨40674, by rfl⟩ : syracuseStep 1735445 = 81349) (by norm_num)
theorem B2890565 : Blo 1283960 2890565 := bbase (se 4 (by rfl) ⟨270990, by rfl⟩ : syracuseStep 2890565 = 541981) (by norm_num)
theorem B9755477 : Blo 1283960 9755477 := bbase (se 9 (by rfl) ⟨28580, by rfl⟩ : syracuseStep 9755477 = 57161) (by norm_num)
theorem B2169733 : Blo 1283960 2169733 := bbase (se 4 (by rfl) ⟨203412, by rfl⟩ : syracuseStep 2169733 = 406825) (by norm_num)
theorem B2890637 : Blo 1283960 2890637 := bbase (se 3 (by rfl) ⟨541994, by rfl⟩ : syracuseStep 2890637 = 1083989) (by norm_num)
theorem B3251117 : Blo 1283960 3251117 := bbase (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) (by norm_num)
theorem B2890709 : Blo 1283960 2890709 := bbase (se 7 (by rfl) ⟨33875, by rfl⟩ : syracuseStep 2890709 = 67751) (by norm_num)
theorem B2169821 : Blo 1283960 2169821 := bbase (se 3 (by rfl) ⟨406841, by rfl⟩ : syracuseStep 2169821 = 813683) (by norm_num)
theorem B7314421 : Blo 1283960 7314421 := bbase (se 5 (by rfl) ⟨342863, by rfl⟩ : syracuseStep 7314421 = 685727) (by norm_num)
theorem B2890781 : Blo 1283960 2890781 := bbase (se 3 (by rfl) ⟨542021, by rfl⟩ : syracuseStep 2890781 = 1084043) (by norm_num)
theorem B2169949 : Blo 1283960 2169949 := bbase (se 3 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 2169949 = 813731) (by norm_num)
theorem B2890853 : Blo 1283960 2890853 := bbase (se 4 (by rfl) ⟨271017, by rfl⟩ : syracuseStep 2890853 = 542035) (by norm_num)
theorem B1301665 : Blo 1283960 1301665 := bbase (se 2 (by rfl) ⟨488124, by rfl⟩ : syracuseStep 1301665 = 976249) (by norm_num)
theorem B2890925 : Blo 1283960 2890925 := bbase (se 3 (by rfl) ⟨542048, by rfl⟩ : syracuseStep 2890925 = 1084097) (by norm_num)
theorem B1301681 : Blo 1283960 1301681 := bbase (se 2 (by rfl) ⟨488130, by rfl⟩ : syracuseStep 1301681 = 976261) (by norm_num)
theorem B2170037 : Blo 1283960 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B2440381 : Blo 1283960 2440381 := bbase (se 3 (by rfl) ⟨457571, by rfl⟩ : syracuseStep 2440381 = 915143) (by norm_num)
theorem B2604269 : Blo 1283960 2604269 := bbase (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) (by norm_num)
theorem B2743541 : Blo 1283960 2743541 := bbase (se 5 (by rfl) ⟨128603, by rfl⟩ : syracuseStep 2743541 = 257207) (by norm_num)
theorem B2890997 : Blo 1283960 2890997 := bbase (se 5 (by rfl) ⟨135515, by rfl⟩ : syracuseStep 2890997 = 271031) (by norm_num)
theorem B3251461 : Blo 1283960 3251461 := bbase (se 4 (by rfl) ⟨304824, by rfl⟩ : syracuseStep 3251461 = 609649) (by norm_num)
theorem B2891069 : Blo 1283960 2891069 := bbase (se 3 (by rfl) ⟨542075, by rfl⟩ : syracuseStep 2891069 = 1084151) (by norm_num)
theorem B2440525 : Blo 1283960 2440525 := bbase (se 3 (by rfl) ⟨457598, by rfl⟩ : syracuseStep 2440525 = 915197) (by norm_num)
theorem B3906917 : Blo 1283960 3906917 := bbase (se 4 (by rfl) ⟨366273, by rfl⟩ : syracuseStep 3906917 = 732547) (by norm_num)
theorem B1465705 : Blo 1283960 1465705 := bbase (se 2 (by rfl) ⟨549639, by rfl⟩ : syracuseStep 1465705 = 1099279) (by norm_num)
theorem B3251573 : Blo 1283960 3251573 := bbase (se 5 (by rfl) ⟨152417, by rfl⟩ : syracuseStep 3251573 = 304835) (by norm_num)
theorem B3087733 : Blo 1283960 3087733 := bbase (se 5 (by rfl) ⟨144737, by rfl⟩ : syracuseStep 3087733 = 289475) (by norm_num)
theorem B6503813 : Blo 1283960 6503813 := bbase (se 4 (by rfl) ⟨609732, by rfl⟩ : syracuseStep 6503813 = 1219465) (by norm_num)
theorem B2891141 : Blo 1283960 2891141 := bbase (se 4 (by rfl) ⟨271044, by rfl⟩ : syracuseStep 2891141 = 542089) (by norm_num)
theorem B1465777 : Blo 1283960 1465777 := bbase (se 2 (by rfl) ⟨549666, by rfl⟩ : syracuseStep 1465777 = 1099333) (by norm_num)
theorem B2891213 : Blo 1283960 2891213 := bbase (se 3 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 2891213 = 1084205) (by norm_num)
theorem B2743789 : Blo 1283960 2743789 := bbase (se 3 (by rfl) ⟨514460, by rfl⟩ : syracuseStep 2743789 = 1028921) (by norm_num)
theorem B2440685 : Blo 1283960 2440685 := bbase (se 3 (by rfl) ⟨457628, by rfl⟩ : syracuseStep 2440685 = 915257) (by norm_num)
theorem B2932213 : Blo 1283960 2932213 := bbase (se 5 (by rfl) ⟨137447, by rfl⟩ : syracuseStep 2932213 = 274895) (by norm_num)
theorem B3661301 : Blo 1283960 3661301 := bbase (se 5 (by rfl) ⟨171623, by rfl⟩ : syracuseStep 3661301 = 343247) (by norm_num)
theorem B2891285 : Blo 1283960 2891285 := bbase (se 6 (by rfl) ⟨67764, by rfl⟩ : syracuseStep 2891285 = 135529) (by norm_num)
theorem B3251765 : Blo 1283960 3251765 := bbase (se 5 (by rfl) ⟨152426, by rfl⟩ : syracuseStep 3251765 = 304853) (by norm_num)
theorem B1736245 : Blo 1283960 1736245 := bbase (se 5 (by rfl) ⟨81386, by rfl⟩ : syracuseStep 1736245 = 162773) (by norm_num)
theorem B2891357 : Blo 1283960 2891357 := bbase (se 3 (by rfl) ⟨542129, by rfl⟩ : syracuseStep 2891357 = 1084259) (by norm_num)
theorem B4628069 : Blo 1283960 4628069 := bbase (se 4 (by rfl) ⟨433881, by rfl⟩ : syracuseStep 4628069 = 867763) (by norm_num)
theorem B2440829 : Blo 1283960 2440829 := bbase (se 3 (by rfl) ⟨457655, by rfl⟩ : syracuseStep 2440829 = 915311) (by norm_num)
theorem B4947605 : Blo 1283960 4947605 := bbase (se 6 (by rfl) ⟨115959, by rfl⟩ : syracuseStep 4947605 = 231919) (by norm_num)
theorem B2891429 : Blo 1283960 2891429 := bbase (se 4 (by rfl) ⟨271071, by rfl⟩ : syracuseStep 2891429 = 542143) (by norm_num)
theorem B2891501 : Blo 1283960 2891501 := bbase (se 3 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 2891501 = 1084313) (by norm_num)
theorem B1736461 : Blo 1283960 1736461 := bbase (se 3 (by rfl) ⟨325586, by rfl⟩ : syracuseStep 1736461 = 651173) (by norm_num)
theorem B2891573 : Blo 1283960 2891573 := bbase (se 5 (by rfl) ⟨135542, by rfl⟩ : syracuseStep 2891573 = 271085) (by norm_num)
theorem B52748117 : Blo 1283960 52748117 := bbase (se 9 (by rfl) ⟨154535, by rfl⟩ : syracuseStep 52748117 = 309071) (by norm_num)
theorem B2891645 : Blo 1283960 2891645 := bbase (se 3 (by rfl) ⟨542183, by rfl⟩ : syracuseStep 2891645 = 1084367) (by norm_num)
theorem B4333445 : Blo 1283960 4333445 := bbase (se 4 (by rfl) ⟨406260, by rfl⟩ : syracuseStep 4333445 = 812521) (by norm_num)
theorem B3252109 : Blo 1283960 3252109 := bbase (se 3 (by rfl) ⟨609770, by rfl⟩ : syracuseStep 3252109 = 1219541) (by norm_num)
theorem B2441117 : Blo 1283960 2441117 := bbase (se 3 (by rfl) ⟨457709, by rfl⟩ : syracuseStep 2441117 = 915419) (by norm_num)
theorem B3473333 : Blo 1283960 3473333 := bbase (se 5 (by rfl) ⟨162812, by rfl⟩ : syracuseStep 3473333 = 325625) (by norm_num)
theorem B2891717 : Blo 1283960 2891717 := bbase (se 4 (by rfl) ⟨271098, by rfl⟩ : syracuseStep 2891717 = 542197) (by norm_num)
theorem B2744293 : Blo 1283960 2744293 := bbase (se 4 (by rfl) ⟨257277, by rfl⟩ : syracuseStep 2744293 = 514555) (by norm_num)
theorem B3252221 : Blo 1283960 3252221 := bbase (se 3 (by rfl) ⟨609791, by rfl⟩ : syracuseStep 3252221 = 1219583) (by norm_num)
theorem B6504461 : Blo 1283960 6504461 := bstep (se 3 (by rfl) ⟨1219586, by rfl⟩ : syracuseStep 6504461 = 2439173) B2439173
theorem B2891825 : Blo 1283960 2891825 := bstep (se 2 (by rfl) ⟨1084434, by rfl⟩ : syracuseStep 2891825 = 2168869) B2168869
theorem B2891843 : Blo 1283960 2891843 := bstep (se 1 (by rfl) ⟨2168882, by rfl⟩ : syracuseStep 2891843 = 4337765) B4337765
theorem B1466435 : Blo 1283960 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B1736785 : Blo 1283960 1736785 := bstep (se 2 (by rfl) ⟨651294, by rfl⟩ : syracuseStep 1736785 = 1302589) B1302589
theorem B2441315 : Blo 1283960 2441315 := bstep (se 1 (by rfl) ⟨1830986, by rfl⟩ : syracuseStep 2441315 = 3661973) B3661973
theorem B3252433 : Blo 1283960 3252433 := bstep (se 2 (by rfl) ⟨1219662, by rfl⟩ : syracuseStep 3252433 = 2439325) B2439325
theorem B13197539 : Blo 1283960 13197539 := bstep (se 1 (by rfl) ⟨9898154, by rfl⟩ : syracuseStep 13197539 = 19796309) B19796309
theorem B7315697 : Blo 1283960 7315697 := bstep (se 2 (by rfl) ⟨2743386, by rfl⟩ : syracuseStep 7315697 = 5486773) B5486773
theorem B2892113 : Blo 1283960 2892113 := bstep (se 2 (by rfl) ⟨1084542, by rfl⟩ : syracuseStep 2892113 = 2169085) B2169085
theorem B2892131 : Blo 1283960 2892131 := bstep (se 1 (by rfl) ⟨2169098, by rfl⟩ : syracuseStep 2892131 = 4338197) B4338197
theorem B5013937 : Blo 1283960 5013937 := bstep (se 2 (by rfl) ⟨1880226, by rfl⟩ : syracuseStep 5013937 = 3760453) B3760453
theorem B3252707 : Blo 1283960 3252707 := bstep (se 1 (by rfl) ⟨2439530, by rfl⟩ : syracuseStep 3252707 = 4879061) B4879061
theorem B4334093 : Blo 1283960 4334093 := bstep (se 3 (by rfl) ⟨812642, by rfl⟩ : syracuseStep 4334093 = 1625285) B1625285
theorem B13181453 : Blo 1283960 13181453 := bstep (se 3 (by rfl) ⟨2471522, by rfl⟩ : syracuseStep 13181453 = 4943045) B4943045
theorem B2056771 : Blo 1283960 2056771 := bstep (se 1 (by rfl) ⟨1542578, by rfl⟩ : syracuseStep 2056771 = 3085157) B3085157
theorem B4334147 : Blo 1283960 4334147 := bstep (se 1 (by rfl) ⟨3250610, by rfl⟩ : syracuseStep 4334147 = 6501221) B6501221
theorem B1737283 : Blo 1283960 1737283 := bstep (se 1 (by rfl) ⟨1302962, by rfl⟩ : syracuseStep 1737283 = 2605925) B2605925
theorem B3088963 : Blo 1283960 3088963 := bstep (se 1 (by rfl) ⟨2316722, by rfl⟩ : syracuseStep 3088963 = 4633445) B4633445
theorem B2892401 : Blo 1283960 2892401 := bstep (se 2 (by rfl) ⟨1084650, by rfl⟩ : syracuseStep 2892401 = 2169301) B2169301
theorem B2892419 : Blo 1283960 2892419 := bstep (se 1 (by rfl) ⟨2169314, by rfl⟩ : syracuseStep 2892419 = 4338629) B4338629
theorem B3252899 : Blo 1283960 3252899 := bstep (se 1 (by rfl) ⟨2439674, by rfl⟩ : syracuseStep 3252899 = 4879349) B4879349
theorem B26731235 : Blo 1283960 26731235 := bstep (se 1 (by rfl) ⟨20048426, by rfl⟩ : syracuseStep 26731235 = 40096853) B40096853
theorem B7045957 : Blo 1283960 7045957 := bstep (se 4 (by rfl) ⟨660558, by rfl⟩ : syracuseStep 7045957 = 1321117) B1321117
theorem B1925969 : Blo 1283960 1925969 := bstep (se 2 (by rfl) ⟨722238, by rfl⟩ : syracuseStep 1925969 = 1444477) B1444477
theorem B4334417 : Blo 1283960 4334417 := bstep (se 2 (by rfl) ⟨1625406, by rfl⟩ : syracuseStep 4334417 = 3250813) B3250813
theorem B1925987 : Blo 1283960 1925987 := bstep (se 1 (by rfl) ⟨1444490, by rfl⟩ : syracuseStep 1925987 = 2888981) B2888981
theorem B5489507 : Blo 1283960 5489507 := bstep (se 1 (by rfl) ⟨4117130, by rfl⟩ : syracuseStep 5489507 = 8234261) B8234261
theorem B3130211 : Blo 1283960 3130211 := bstep (se 1 (by rfl) ⟨2347658, by rfl⟩ : syracuseStep 3130211 = 4695317) B4695317
theorem B1926017 : Blo 1283960 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B2892689 : Blo 1283960 2892689 := bstep (se 2 (by rfl) ⟨1084758, by rfl⟩ : syracuseStep 2892689 = 2169517) B2169517
theorem B1926035 : Blo 1283960 1926035 := bstep (se 1 (by rfl) ⟨1444526, by rfl⟩ : syracuseStep 1926035 = 2889053) B2889053
theorem B2892707 : Blo 1283960 2892707 := bstep (se 1 (by rfl) ⟨2169530, by rfl⟩ : syracuseStep 2892707 = 4339061) B4339061
theorem B1926065 : Blo 1283960 1926065 := bstep (se 2 (by rfl) ⟨722274, by rfl⟩ : syracuseStep 1926065 = 1444549) B1444549
theorem B3130289 : Blo 1283960 3130289 := bstep (se 2 (by rfl) ⟨1173858, by rfl⟩ : syracuseStep 3130289 = 2347717) B2347717
theorem B1926083 : Blo 1283960 1926083 := bstep (se 1 (by rfl) ⟨1444562, by rfl⟩ : syracuseStep 1926083 = 2889125) B2889125
theorem B1926113 : Blo 1283960 1926113 := bstep (se 2 (by rfl) ⟨722292, by rfl⟩ : syracuseStep 1926113 = 1444585) B1444585
theorem B12354545 : Blo 1283960 12354545 := bstep (se 2 (by rfl) ⟨4632954, by rfl⟩ : syracuseStep 12354545 = 9265909) B9265909
theorem B1926131 : Blo 1283960 1926131 := bstep (se 1 (by rfl) ⟨1444598, by rfl⟩ : syracuseStep 1926131 = 2889197) B2889197
theorem B1926161 : Blo 1283960 1926161 := bstep (se 2 (by rfl) ⟨722310, by rfl⟩ : syracuseStep 1926161 = 1444621) B1444621
theorem B2057233 : Blo 1283960 2057233 := bstep (se 2 (by rfl) ⟨771462, by rfl⟩ : syracuseStep 2057233 = 1542925) B1542925
theorem B1926179 : Blo 1283960 1926179 := bstep (se 1 (by rfl) ⟨1444634, by rfl⟩ : syracuseStep 1926179 = 2889269) B2889269
theorem B1926209 : Blo 1283960 1926209 := bstep (se 2 (by rfl) ⟨722328, by rfl⟩ : syracuseStep 1926209 = 1444657) B1444657
theorem B1926227 : Blo 1283960 1926227 := bstep (se 1 (by rfl) ⟨1444670, by rfl⟩ : syracuseStep 1926227 = 2889341) B2889341
theorem B1926257 : Blo 1283960 1926257 := bstep (se 2 (by rfl) ⟨722346, by rfl⟩ : syracuseStep 1926257 = 1444693) B1444693
theorem B2057329 : Blo 1283960 2057329 := bstep (se 2 (by rfl) ⟨771498, by rfl⟩ : syracuseStep 2057329 = 1542997) B1542997
theorem B1926275 : Blo 1283960 1926275 := bstep (se 1 (by rfl) ⟨1444706, by rfl⟩ : syracuseStep 1926275 = 2889413) B2889413
theorem B1926305 : Blo 1283960 1926305 := bstep (se 2 (by rfl) ⟨722364, by rfl⟩ : syracuseStep 1926305 = 1444729) B1444729
theorem B2892977 : Blo 1283960 2892977 := bstep (se 2 (by rfl) ⟨1084866, by rfl⟩ : syracuseStep 2892977 = 2169733) B2169733
theorem B1926323 : Blo 1283960 1926323 := bstep (se 1 (by rfl) ⟨1444742, by rfl⟩ : syracuseStep 1926323 = 2889485) B2889485
theorem B2892995 : Blo 1283960 2892995 := bstep (se 1 (by rfl) ⟨2169746, by rfl⟩ : syracuseStep 2892995 = 4339493) B4339493
theorem B1926353 : Blo 1283960 1926353 := bstep (se 2 (by rfl) ⟨722382, by rfl⟩ : syracuseStep 1926353 = 1444765) B1444765
theorem B4875491 : Blo 1283960 4875491 := bstep (se 1 (by rfl) ⟨3656618, by rfl⟩ : syracuseStep 4875491 = 7313237) B7313237
theorem B1926371 : Blo 1283960 1926371 := bstep (se 1 (by rfl) ⟨1444778, by rfl⟩ : syracuseStep 1926371 = 2889557) B2889557
theorem B1926401 : Blo 1283960 1926401 := bstep (se 2 (by rfl) ⟨722400, by rfl⟩ : syracuseStep 1926401 = 1444801) B1444801
theorem B2057489 : Blo 1283960 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B1926419 : Blo 1283960 1926419 := bstep (se 1 (by rfl) ⟨1444814, by rfl⟩ : syracuseStep 1926419 = 2889629) B2889629
theorem B1926449 : Blo 1283960 1926449 := bstep (se 2 (by rfl) ⟨722418, by rfl⟩ : syracuseStep 1926449 = 1444837) B1444837
theorem B1926467 : Blo 1283960 1926467 := bstep (se 1 (by rfl) ⟨1444850, by rfl⟩ : syracuseStep 1926467 = 2889701) B2889701
theorem B2196833 : Blo 1283960 2196833 := bstep (se 2 (by rfl) ⟨823812, by rfl⟩ : syracuseStep 2196833 = 1647625) B1647625
theorem B1926497 : Blo 1283960 1926497 := bstep (se 2 (by rfl) ⟨722436, by rfl⟩ : syracuseStep 1926497 = 1444873) B1444873
theorem B4334957 : Blo 1283960 4334957 := bstep (se 3 (by rfl) ⟨812804, by rfl⟩ : syracuseStep 4334957 = 1625609) B1625609
theorem B1926515 : Blo 1283960 1926515 := bstep (se 1 (by rfl) ⟨1444886, by rfl⟩ : syracuseStep 1926515 = 2889773) B2889773
theorem B1926545 : Blo 1283960 1926545 := bstep (se 2 (by rfl) ⟨722454, by rfl⟩ : syracuseStep 1926545 = 1444909) B1444909
theorem B1926563 : Blo 1283960 1926563 := bstep (se 1 (by rfl) ⟨1444922, by rfl⟩ : syracuseStep 1926563 = 2889845) B2889845
theorem B4335011 : Blo 1283960 4335011 := bstep (se 1 (by rfl) ⟨3251258, by rfl⟩ : syracuseStep 4335011 = 6502517) B6502517
theorem B1926593 : Blo 1283960 1926593 := bstep (se 2 (by rfl) ⟨722472, by rfl⟩ : syracuseStep 1926593 = 1444945) B1444945
theorem B2893265 : Blo 1283960 2893265 := bstep (se 2 (by rfl) ⟨1084974, by rfl⟩ : syracuseStep 2893265 = 2169949) B2169949
theorem B1926611 : Blo 1283960 1926611 := bstep (se 1 (by rfl) ⟨1444958, by rfl⟩ : syracuseStep 1926611 = 2889917) B2889917
theorem B2893283 : Blo 1283960 2893283 := bstep (se 1 (by rfl) ⟨2169962, by rfl⟩ : syracuseStep 2893283 = 4339925) B4339925
theorem B1926641 : Blo 1283960 1926641 := bstep (se 2 (by rfl) ⟨722490, by rfl⟩ : syracuseStep 1926641 = 1444981) B1444981
theorem B1926659 : Blo 1283960 1926659 := bstep (se 1 (by rfl) ⟨1444994, by rfl⟩ : syracuseStep 1926659 = 2889989) B2889989
theorem B1926689 : Blo 1283960 1926689 := bstep (se 2 (by rfl) ⟨722508, by rfl⟩ : syracuseStep 1926689 = 1445017) B1445017
theorem B1926707 : Blo 1283960 1926707 := bstep (se 1 (by rfl) ⟨1445030, by rfl⟩ : syracuseStep 1926707 = 2890061) B2890061
theorem B4171331 : Blo 1283960 4171331 := bstep (se 1 (by rfl) ⟨3128498, by rfl⟩ : syracuseStep 4171331 = 6256997) B6256997
theorem B1926737 : Blo 1283960 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B3253841 : Blo 1283960 3253841 := bstep (se 2 (by rfl) ⟨1220190, by rfl⟩ : syracuseStep 3253841 = 2440381) B2440381
theorem B1828435 : Blo 1283960 1828435 := bstep (se 1 (by rfl) ⟨1371326, by rfl⟩ : syracuseStep 1828435 = 2742653) B2742653
theorem B1926755 : Blo 1283960 1926755 := bstep (se 1 (by rfl) ⟨1445066, by rfl⟩ : syracuseStep 1926755 = 2890133) B2890133
theorem B1926785 : Blo 1283960 1926785 := bstep (se 2 (by rfl) ⟨722544, by rfl⟩ : syracuseStep 1926785 = 1445089) B1445089
theorem B3253891 : Blo 1283960 3253891 := bstep (se 1 (by rfl) ⟨2440418, by rfl⟩ : syracuseStep 3253891 = 4880837) B4880837
theorem B2746001 : Blo 1283960 2746001 := bstep (se 2 (by rfl) ⟨1029750, by rfl⟩ : syracuseStep 2746001 = 2059501) B2059501
theorem B1926803 : Blo 1283960 1926803 := bstep (se 1 (by rfl) ⟨1445102, by rfl⟩ : syracuseStep 1926803 = 2890205) B2890205
theorem B7317155 : Blo 1283960 7317155 := bstep (se 1 (by rfl) ⟨5487866, by rfl⟩ : syracuseStep 7317155 = 10975733) B10975733
theorem B4335281 : Blo 1283960 4335281 := bstep (se 2 (by rfl) ⟨1625730, by rfl⟩ : syracuseStep 4335281 = 3251461) B3251461
theorem B1926833 : Blo 1283960 1926833 := bstep (se 2 (by rfl) ⟨722562, by rfl⟩ : syracuseStep 1926833 = 1445125) B1445125
theorem B1926851 : Blo 1283960 1926851 := bstep (se 1 (by rfl) ⟨1445138, by rfl⟩ : syracuseStep 1926851 = 2890277) B2890277
theorem B1926881 : Blo 1283960 1926881 := bstep (se 2 (by rfl) ⟨722580, by rfl⟩ : syracuseStep 1926881 = 1445161) B1445161
theorem B8234723 : Blo 1283960 8234723 := bstep (se 1 (by rfl) ⟨6176042, by rfl⟩ : syracuseStep 8234723 = 12352085) B12352085
theorem B4114157 : Blo 1283960 4114157 := bstep (se 3 (by rfl) ⟨771404, by rfl⟩ : syracuseStep 4114157 = 1542809) B1542809
theorem B1926899 : Blo 1283960 1926899 := bstep (se 1 (by rfl) ⟨1445174, by rfl⟩ : syracuseStep 1926899 = 2890349) B2890349
theorem B1926929 : Blo 1283960 1926929 := bstep (se 2 (by rfl) ⟨722598, by rfl⟩ : syracuseStep 1926929 = 1445197) B1445197
theorem B3254033 : Blo 1283960 3254033 := bstep (se 2 (by rfl) ⟨1220262, by rfl⟩ : syracuseStep 3254033 = 2440525) B2440525
theorem B1926947 : Blo 1283960 1926947 := bstep (se 1 (by rfl) ⟨1445210, by rfl⟩ : syracuseStep 1926947 = 2890421) B2890421
theorem B1926977 : Blo 1283960 1926977 := bstep (se 2 (by rfl) ⟨722616, by rfl⟩ : syracuseStep 1926977 = 1445233) B1445233
theorem B1926995 : Blo 1283960 1926995 := bstep (se 1 (by rfl) ⟨1445246, by rfl⟩ : syracuseStep 1926995 = 2890493) B2890493
theorem B4876145 : Blo 1283960 4876145 := bstep (se 2 (by rfl) ⟨1828554, by rfl⟩ : syracuseStep 4876145 = 3657109) B3657109
theorem B1927025 : Blo 1283960 1927025 := bstep (se 2 (by rfl) ⟨722634, by rfl⟩ : syracuseStep 1927025 = 1445269) B1445269
theorem B1927043 : Blo 1283960 1927043 := bstep (se 1 (by rfl) ⟨1445282, by rfl⟩ : syracuseStep 1927043 = 2890565) B2890565
theorem B1927073 : Blo 1283960 1927073 := bstep (se 2 (by rfl) ⟨722652, by rfl⟩ : syracuseStep 1927073 = 1445305) B1445305
theorem B1927091 : Blo 1283960 1927091 := bstep (se 1 (by rfl) ⟨1445318, by rfl⟩ : syracuseStep 1927091 = 2890637) B2890637
theorem B1927121 : Blo 1283960 1927121 := bstep (se 2 (by rfl) ⟨722670, by rfl⟩ : syracuseStep 1927121 = 1445341) B1445341
theorem B1927139 : Blo 1283960 1927139 := bstep (se 1 (by rfl) ⟨1445354, by rfl⟩ : syracuseStep 1927139 = 2890709) B2890709
theorem B3909617 : Blo 1283960 3909617 := bstep (se 2 (by rfl) ⟨1466106, by rfl⟩ : syracuseStep 3909617 = 2932213) B2932213
theorem B1927169 : Blo 1283960 1927169 := bstep (se 2 (by rfl) ⟨722688, by rfl⟩ : syracuseStep 1927169 = 1445377) B1445377
theorem B1927187 : Blo 1283960 1927187 := bstep (se 1 (by rfl) ⟨1445390, by rfl⟩ : syracuseStep 1927187 = 2890781) B2890781
theorem B1927217 : Blo 1283960 1927217 := bstep (se 2 (by rfl) ⟨722706, by rfl⟩ : syracuseStep 1927217 = 1445413) B1445413
theorem B5490737 : Blo 1283960 5490737 := bstep (se 2 (by rfl) ⟨2059026, by rfl⟩ : syracuseStep 5490737 = 4118053) B4118053
theorem B1927235 : Blo 1283960 1927235 := bstep (se 1 (by rfl) ⟨1445426, by rfl⟩ : syracuseStep 1927235 = 2890853) B2890853
theorem B1927265 : Blo 1283960 1927265 := bstep (se 2 (by rfl) ⟨722724, by rfl⟩ : syracuseStep 1927265 = 1445449) B1445449
theorem B3295331 : Blo 1283960 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B1927283 : Blo 1283960 1927283 := bstep (se 1 (by rfl) ⟨1445462, by rfl⟩ : syracuseStep 1927283 = 2890925) B2890925
theorem B1828993 : Blo 1283960 1828993 := bstep (se 2 (by rfl) ⟨685872, by rfl⟩ : syracuseStep 1828993 = 1371745) B1371745
theorem B9889933 : Blo 1283960 9889933 := bstep (se 3 (by rfl) ⟨1854362, by rfl⟩ : syracuseStep 9889933 = 3708725) B3708725
theorem B1927313 : Blo 1283960 1927313 := bstep (se 2 (by rfl) ⟨722742, by rfl⟩ : syracuseStep 1927313 = 1445485) B1445485
theorem B1829027 : Blo 1283960 1829027 := bstep (se 1 (by rfl) ⟨1371770, by rfl⟩ : syracuseStep 1829027 = 2743541) B2743541
theorem B1927331 : Blo 1283960 1927331 := bstep (se 1 (by rfl) ⟨1445498, by rfl⟩ : syracuseStep 1927331 = 2890997) B2890997
theorem B1927361 : Blo 1283960 1927361 := bstep (se 2 (by rfl) ⟨722760, by rfl⟩ : syracuseStep 1927361 = 1445521) B1445521
theorem B4335821 : Blo 1283960 4335821 := bstep (se 3 (by rfl) ⟨812966, by rfl⟩ : syracuseStep 4335821 = 1625933) B1625933
theorem B1927379 : Blo 1283960 1927379 := bstep (se 1 (by rfl) ⟨1445534, by rfl⟩ : syracuseStep 1927379 = 2891069) B2891069
theorem B1927409 : Blo 1283960 1927409 := bstep (se 2 (by rfl) ⟨722778, by rfl⟩ : syracuseStep 1927409 = 1445557) B1445557
theorem B4335875 : Blo 1283960 4335875 := bstep (se 1 (by rfl) ⟨3251906, by rfl⟩ : syracuseStep 4335875 = 6503813) B6503813
theorem B1927427 : Blo 1283960 1927427 := bstep (se 1 (by rfl) ⟨1445570, by rfl⟩ : syracuseStep 1927427 = 2891141) B2891141
theorem B7817477 : Blo 1283960 7817477 := bstep (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) B1465777
theorem B1927457 : Blo 1283960 1927457 := bstep (se 2 (by rfl) ⟨722796, by rfl⟩ : syracuseStep 1927457 = 1445593) B1445593
theorem B1927475 : Blo 1283960 1927475 := bstep (se 1 (by rfl) ⟨1445606, by rfl⟩ : syracuseStep 1927475 = 2891213) B2891213
theorem B1927505 : Blo 1283960 1927505 := bstep (se 2 (by rfl) ⟨722814, by rfl⟩ : syracuseStep 1927505 = 1445629) B1445629
theorem B1927523 : Blo 1283960 1927523 := bstep (se 1 (by rfl) ⟨1445642, by rfl⟩ : syracuseStep 1927523 = 2891285) B2891285
theorem B3475811 : Blo 1283960 3475811 := bstep (se 1 (by rfl) ⟨2606858, by rfl⟩ : syracuseStep 3475811 = 5213717) B5213717
theorem B1927553 : Blo 1283960 1927553 := bstep (se 2 (by rfl) ⟨722832, by rfl⟩ : syracuseStep 1927553 = 1445665) B1445665
theorem B1927571 : Blo 1283960 1927571 := bstep (se 1 (by rfl) ⟨1445678, by rfl⟩ : syracuseStep 1927571 = 2891357) B2891357
theorem B1927601 : Blo 1283960 1927601 := bstep (se 2 (by rfl) ⟨722850, by rfl⟩ : syracuseStep 1927601 = 1445701) B1445701
theorem B1927619 : Blo 1283960 1927619 := bstep (se 1 (by rfl) ⟨1445714, by rfl⟩ : syracuseStep 1927619 = 2891429) B2891429
theorem B1927649 : Blo 1283960 1927649 := bstep (se 2 (by rfl) ⟨722868, by rfl⟩ : syracuseStep 1927649 = 1445737) B1445737
theorem B1927667 : Blo 1283960 1927667 := bstep (se 1 (by rfl) ⟨1445750, by rfl⟩ : syracuseStep 1927667 = 2891501) B2891501
theorem B4336145 : Blo 1283960 4336145 := bstep (se 2 (by rfl) ⟨1626054, by rfl⟩ : syracuseStep 4336145 = 3252109) B3252109
theorem B1927697 : Blo 1283960 1927697 := bstep (se 2 (by rfl) ⟨722886, by rfl⟩ : syracuseStep 1927697 = 1445773) B1445773
theorem B1952291 : Blo 1283960 1952291 := bstep (se 1 (by rfl) ⟨1464218, by rfl⟩ : syracuseStep 1952291 = 2928437) B2928437
theorem B1927715 : Blo 1283960 1927715 := bstep (se 1 (by rfl) ⟨1445786, by rfl⟩ : syracuseStep 1927715 = 2891573) B2891573
theorem B5016113 : Blo 1283960 5016113 := bstep (se 2 (by rfl) ⟨1881042, by rfl⟩ : syracuseStep 5016113 = 3762085) B3762085
theorem B1927745 : Blo 1283960 1927745 := bstep (se 2 (by rfl) ⟨722904, by rfl⟩ : syracuseStep 1927745 = 1445809) B1445809
theorem B1927763 : Blo 1283960 1927763 := bstep (se 1 (by rfl) ⟨1445822, by rfl⟩ : syracuseStep 1927763 = 2891645) B2891645
theorem B16681571 : Blo 1283960 16681571 := bstep (se 1 (by rfl) ⟨12511178, by rfl⟩ : syracuseStep 16681571 = 25022357) B25022357
theorem B1927793 : Blo 1283960 1927793 := bstep (se 2 (by rfl) ⟨722922, by rfl⟩ : syracuseStep 1927793 = 1445845) B1445845
theorem B1927811 : Blo 1283960 1927811 := bstep (se 1 (by rfl) ⟨1445858, by rfl⟩ : syracuseStep 1927811 = 2891717) B2891717
theorem B1927841 : Blo 1283960 1927841 := bstep (se 2 (by rfl) ⟨722940, by rfl⟩ : syracuseStep 1927841 = 1445881) B1445881
theorem B1952419 : Blo 1283960 1952419 := bstep (se 1 (by rfl) ⟨1464314, by rfl⟩ : syracuseStep 1952419 = 2928629) B2928629
theorem B1444531 : Blo 1283960 1444531 := bstep (se 1 (by rfl) ⟨1083398, by rfl⟩ : syracuseStep 1444531 = 2166797) B2166797
theorem B1927859 : Blo 1283960 1927859 := bstep (se 1 (by rfl) ⟨1445894, by rfl⟩ : syracuseStep 1927859 = 2891789) B2891789
theorem B1829585 : Blo 1283960 1829585 := bstep (se 2 (by rfl) ⟨686094, by rfl⟩ : syracuseStep 1829585 = 1372189) B1372189
theorem B1927889 : Blo 1283960 1927889 := bstep (se 2 (by rfl) ⟨722958, by rfl⟩ : syracuseStep 1927889 = 1445917) B1445917
theorem B1927907 : Blo 1283960 1927907 := bstep (se 1 (by rfl) ⟨1445930, by rfl⟩ : syracuseStep 1927907 = 2891861) B2891861
theorem B20064995 : Blo 1283960 20064995 := bstep (se 1 (by rfl) ⟨15048746, by rfl⟩ : syracuseStep 20064995 = 30097493) B30097493
theorem B3255025 : Blo 1283960 3255025 := bstep (se 2 (by rfl) ⟨1220634, by rfl⟩ : syracuseStep 3255025 = 2441269) B2441269
theorem B1927937 : Blo 1283960 1927937 := bstep (se 2 (by rfl) ⟨722976, by rfl⟩ : syracuseStep 1927937 = 1445953) B1445953
theorem B1927955 : Blo 1283960 1927955 := bstep (se 1 (by rfl) ⟨1445966, by rfl⟩ : syracuseStep 1927955 = 2891933) B2891933
theorem B1829665 : Blo 1283960 1829665 := bstep (se 2 (by rfl) ⟨686124, by rfl⟩ : syracuseStep 1829665 = 1372249) B1372249
theorem B1927985 : Blo 1283960 1927985 := bstep (se 2 (by rfl) ⟨722994, by rfl⟩ : syracuseStep 1927985 = 1445989) B1445989
theorem B1444675 : Blo 1283960 1444675 := bstep (se 1 (by rfl) ⟨1083506, by rfl⟩ : syracuseStep 1444675 = 2167013) B2167013
theorem B1928003 : Blo 1283960 1928003 := bstep (se 1 (by rfl) ⟨1446002, by rfl⟩ : syracuseStep 1928003 = 2892005) B2892005
theorem B1928033 : Blo 1283960 1928033 := bstep (se 2 (by rfl) ⟨723012, by rfl⟩ : syracuseStep 1928033 = 1446025) B1446025
theorem B6507377 : Blo 1283960 6507377 := bstep (se 2 (by rfl) ⟨2440266, by rfl⟩ : syracuseStep 6507377 = 4880533) B4880533
theorem B1928051 : Blo 1283960 1928051 := bstep (se 1 (by rfl) ⟨1446038, by rfl⟩ : syracuseStep 1928051 = 2892077) B2892077
theorem B1928081 : Blo 1283960 1928081 := bstep (se 2 (by rfl) ⟨723030, by rfl⟩ : syracuseStep 1928081 = 1446061) B1446061
theorem B1928099 : Blo 1283960 1928099 := bstep (se 1 (by rfl) ⟨1446074, by rfl⟩ : syracuseStep 1928099 = 2892149) B2892149
theorem B1928129 : Blo 1283960 1928129 := bstep (se 2 (by rfl) ⟨723048, by rfl⟩ : syracuseStep 1928129 = 1446097) B1446097
theorem B1444819 : Blo 1283960 1444819 := bstep (se 1 (by rfl) ⟨1083614, by rfl⟩ : syracuseStep 1444819 = 2167229) B2167229
theorem B1928147 : Blo 1283960 1928147 := bstep (se 1 (by rfl) ⟨1446110, by rfl⟩ : syracuseStep 1928147 = 2892221) B2892221
theorem B2198497 : Blo 1283960 2198497 := bstep (se 2 (by rfl) ⟨824436, by rfl⟩ : syracuseStep 2198497 = 1648873) B1648873
theorem B1928177 : Blo 1283960 1928177 := bstep (se 2 (by rfl) ⟨723066, by rfl⟩ : syracuseStep 1928177 = 1446133) B1446133
theorem B1928195 : Blo 1283960 1928195 := bstep (se 1 (by rfl) ⟨1446146, by rfl⟩ : syracuseStep 1928195 = 2892293) B2892293
theorem B2059283 : Blo 1283960 2059283 := bstep (se 1 (by rfl) ⟨1544462, by rfl⟩ : syracuseStep 2059283 = 3088925) B3088925
theorem B1928225 : Blo 1283960 1928225 := bstep (se 2 (by rfl) ⟨723084, by rfl⟩ : syracuseStep 1928225 = 1446169) B1446169
theorem B1625123 : Blo 1283960 1625123 := bstep (se 1 (by rfl) ⟨1218842, by rfl⟩ : syracuseStep 1625123 = 2437685) B2437685
theorem B4336685 : Blo 1283960 4336685 := bstep (se 3 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 4336685 = 1626257) B1626257
theorem B1928243 : Blo 1283960 1928243 := bstep (se 1 (by rfl) ⟨1446182, by rfl⟩ : syracuseStep 1928243 = 2892365) B2892365
theorem B1928273 : Blo 1283960 1928273 := bstep (se 2 (by rfl) ⟨723102, by rfl⟩ : syracuseStep 1928273 = 1446205) B1446205
theorem B1444963 : Blo 1283960 1444963 := bstep (se 1 (by rfl) ⟨1083722, by rfl⟩ : syracuseStep 1444963 = 2167445) B2167445
theorem B4336739 : Blo 1283960 4336739 := bstep (se 1 (by rfl) ⟨3252554, by rfl⟩ : syracuseStep 4336739 = 6505109) B6505109
theorem B1928291 : Blo 1283960 1928291 := bstep (se 1 (by rfl) ⟨1446218, by rfl⟩ : syracuseStep 1928291 = 2892437) B2892437
theorem B1928321 : Blo 1283960 1928321 := bstep (se 2 (by rfl) ⟨723120, by rfl⟩ : syracuseStep 1928321 = 1446241) B1446241
theorem B1928339 : Blo 1283960 1928339 := bstep (se 1 (by rfl) ⟨1446254, by rfl⟩ : syracuseStep 1928339 = 2892509) B2892509
theorem B1928369 : Blo 1283960 1928369 := bstep (se 2 (by rfl) ⟨723138, by rfl⟩ : syracuseStep 1928369 = 1446277) B1446277
theorem B1928387 : Blo 1283960 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B1928417 : Blo 1283960 1928417 := bstep (se 2 (by rfl) ⟨723156, by rfl⟩ : syracuseStep 1928417 = 1446313) B1446313
theorem B1445107 : Blo 1283960 1445107 := bstep (se 1 (by rfl) ⟨1083830, by rfl⟩ : syracuseStep 1445107 = 2167661) B2167661
theorem B1928435 : Blo 1283960 1928435 := bstep (se 1 (by rfl) ⟨1446326, by rfl⟩ : syracuseStep 1928435 = 2892653) B2892653
theorem B1928465 : Blo 1283960 1928465 := bstep (se 2 (by rfl) ⟨723174, by rfl⟩ : syracuseStep 1928465 = 1446349) B1446349
theorem B4877603 : Blo 1283960 4877603 := bstep (se 1 (by rfl) ⟨3658202, by rfl⟩ : syracuseStep 4877603 = 7316405) B7316405
theorem B4115747 : Blo 1283960 4115747 := bstep (se 1 (by rfl) ⟨3086810, by rfl⟩ : syracuseStep 4115747 = 6173621) B6173621
theorem B1928483 : Blo 1283960 1928483 := bstep (se 1 (by rfl) ⟨1446362, by rfl⟩ : syracuseStep 1928483 = 2892725) B2892725
theorem B4877617 : Blo 1283960 4877617 := bstep (se 2 (by rfl) ⟨1829106, by rfl⟩ : syracuseStep 4877617 = 3658213) B3658213
theorem B1928513 : Blo 1283960 1928513 := bstep (se 2 (by rfl) ⟨723192, by rfl⟩ : syracuseStep 1928513 = 1446385) B1446385
theorem B1928531 : Blo 1283960 1928531 := bstep (se 1 (by rfl) ⟨1446398, by rfl⟩ : syracuseStep 1928531 = 2892797) B2892797
theorem B4337009 : Blo 1283960 4337009 := bstep (se 2 (by rfl) ⟨1626378, by rfl⟩ : syracuseStep 4337009 = 3252757) B3252757
theorem B1928561 : Blo 1283960 1928561 := bstep (se 2 (by rfl) ⟨723210, by rfl⟩ : syracuseStep 1928561 = 1446421) B1446421
theorem B1445251 : Blo 1283960 1445251 := bstep (se 1 (by rfl) ⟨1083938, by rfl⟩ : syracuseStep 1445251 = 2167877) B2167877
theorem B1928579 : Blo 1283960 1928579 := bstep (se 1 (by rfl) ⟨1446434, by rfl⟩ : syracuseStep 1928579 = 2892869) B2892869
theorem B1928609 : Blo 1283960 1928609 := bstep (se 2 (by rfl) ⟨723228, by rfl⟩ : syracuseStep 1928609 = 1446457) B1446457
theorem B1928627 : Blo 1283960 1928627 := bstep (se 1 (by rfl) ⟨1446470, by rfl⟩ : syracuseStep 1928627 = 2892941) B2892941
theorem B1928657 : Blo 1283960 1928657 := bstep (se 2 (by rfl) ⟨723246, by rfl⟩ : syracuseStep 1928657 = 1446493) B1446493
theorem B1928675 : Blo 1283960 1928675 := bstep (se 1 (by rfl) ⟨1446506, by rfl⟩ : syracuseStep 1928675 = 2893013) B2893013
theorem B3296771 : Blo 1283960 3296771 := bstep (se 1 (by rfl) ⟨2472578, by rfl⟩ : syracuseStep 3296771 = 4945157) B4945157
theorem B1928705 : Blo 1283960 1928705 := bstep (se 2 (by rfl) ⟨723264, by rfl⟩ : syracuseStep 1928705 = 1446529) B1446529
theorem B1445395 : Blo 1283960 1445395 := bstep (se 1 (by rfl) ⟨1084046, by rfl⟩ : syracuseStep 1445395 = 2168093) B2168093
theorem B1928723 : Blo 1283960 1928723 := bstep (se 1 (by rfl) ⟨1446542, by rfl⟩ : syracuseStep 1928723 = 2893085) B2893085
theorem B1928753 : Blo 1283960 1928753 := bstep (se 2 (by rfl) ⟨723282, by rfl⟩ : syracuseStep 1928753 = 1446565) B1446565
theorem B1830451 : Blo 1283960 1830451 := bstep (se 1 (by rfl) ⟨1372838, by rfl⟩ : syracuseStep 1830451 = 2745677) B2745677
theorem B1928771 : Blo 1283960 1928771 := bstep (se 1 (by rfl) ⟨1446578, by rfl⟩ : syracuseStep 1928771 = 2893157) B2893157
theorem B1928801 : Blo 1283960 1928801 := bstep (se 2 (by rfl) ⟨723300, by rfl⟩ : syracuseStep 1928801 = 1446601) B1446601
theorem B3657325 : Blo 1283960 3657325 := bstep (se 3 (by rfl) ⟨685748, by rfl⟩ : syracuseStep 3657325 = 1371497) B1371497
theorem B1928819 : Blo 1283960 1928819 := bstep (se 1 (by rfl) ⟨1446614, by rfl⟩ : syracuseStep 1928819 = 2893229) B2893229
theorem B1928849 : Blo 1283960 1928849 := bstep (se 2 (by rfl) ⟨723318, by rfl⟩ : syracuseStep 1928849 = 1446637) B1446637
theorem B1445539 : Blo 1283960 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B1928867 : Blo 1283960 1928867 := bstep (se 1 (by rfl) ⟨1446650, by rfl⟩ : syracuseStep 1928867 = 2893301) B2893301
theorem B8236721 : Blo 1283960 8236721 := bstep (se 2 (by rfl) ⟨3088770, by rfl⟩ : syracuseStep 8236721 = 6177541) B6177541
theorem B1928897 : Blo 1283960 1928897 := bstep (se 2 (by rfl) ⟨723336, by rfl⟩ : syracuseStep 1928897 = 1446673) B1446673
theorem B7417541 : Blo 1283960 7417541 := bstep (se 4 (by rfl) ⟨695394, by rfl⟩ : syracuseStep 7417541 = 1390789) B1390789
theorem B5861069 : Blo 1283960 5861069 := bstep (se 3 (by rfl) ⟨1098950, by rfl⟩ : syracuseStep 5861069 = 2197901) B2197901
theorem B1928915 : Blo 1283960 1928915 := bstep (se 1 (by rfl) ⟨1446686, by rfl⟩ : syracuseStep 1928915 = 2893373) B2893373
theorem B1625827 : Blo 1283960 1625827 := bstep (se 1 (by rfl) ⟨1219370, by rfl⟩ : syracuseStep 1625827 = 2438741) B2438741
theorem B6942449 : Blo 1283960 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B1371907 : Blo 1283960 1371907 := bstep (se 1 (by rfl) ⟨1028930, by rfl⟩ : syracuseStep 1371907 = 2057861) B2057861
theorem B1445683 : Blo 1283960 1445683 := bstep (se 1 (by rfl) ⟨1084262, by rfl⟩ : syracuseStep 1445683 = 2168525) B2168525
theorem B1625923 : Blo 1283960 1625923 := bstep (se 1 (by rfl) ⟨1219442, by rfl⟩ : syracuseStep 1625923 = 2438885) B2438885
theorem B22548365 : Blo 1283960 22548365 := bstep (se 3 (by rfl) ⟨4227818, by rfl⟩ : syracuseStep 22548365 = 8455637) B8455637
theorem B10973069 : Blo 1283960 10973069 := bstep (se 3 (by rfl) ⟨2057450, by rfl⟩ : syracuseStep 10973069 = 4114901) B4114901
theorem B4337549 : Blo 1283960 4337549 := bstep (se 3 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 4337549 = 1626581) B1626581
theorem B2166689 : Blo 1283960 2166689 := bstep (se 2 (by rfl) ⟨812508, by rfl⟩ : syracuseStep 2166689 = 1625017) B1625017
theorem B1445827 : Blo 1283960 1445827 := bstep (se 1 (by rfl) ⟨1084370, by rfl⟩ : syracuseStep 1445827 = 2168741) B2168741
theorem B4337603 : Blo 1283960 4337603 := bstep (se 1 (by rfl) ⟨3253202, by rfl⟩ : syracuseStep 4337603 = 6506405) B6506405
theorem B9752561 : Blo 1283960 9752561 := bstep (se 2 (by rfl) ⟨3657210, by rfl⟩ : syracuseStep 9752561 = 7314421) B7314421
theorem B1830929 : Blo 1283960 1830929 := bstep (se 2 (by rfl) ⟨686598, by rfl⟩ : syracuseStep 1830929 = 1373197) B1373197
theorem B2166817 : Blo 1283960 2166817 := bstep (se 2 (by rfl) ⟨812556, by rfl⟩ : syracuseStep 2166817 = 1625113) B1625113
theorem B1544227 : Blo 1283960 1544227 := bstep (se 1 (by rfl) ⟨1158170, by rfl⟩ : syracuseStep 1544227 = 2316341) B2316341
theorem B2166851 : Blo 1283960 2166851 := bstep (se 1 (by rfl) ⟨1625138, by rfl⟩ : syracuseStep 2166851 = 3250277) B3250277
theorem B9261125 : Blo 1283960 9261125 := bstep (se 4 (by rfl) ⟨868230, by rfl⟩ : syracuseStep 9261125 = 1736461) B1736461
theorem B1445971 : Blo 1283960 1445971 := bstep (se 1 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 1445971 = 2168957) B2168957
theorem B1372339 : Blo 1283960 1372339 := bstep (se 1 (by rfl) ⟨1029254, by rfl⟩ : syracuseStep 1372339 = 2058509) B2058509
theorem B2166979 : Blo 1283960 2166979 := bstep (se 1 (by rfl) ⟨1625234, by rfl⟩ : syracuseStep 2166979 = 3250469) B3250469
theorem B4337873 : Blo 1283960 4337873 := bstep (se 2 (by rfl) ⟨1626702, by rfl⟩ : syracuseStep 4337873 = 3253405) B3253405
theorem B1446115 : Blo 1283960 1446115 := bstep (se 1 (by rfl) ⟨1084586, by rfl⟩ : syracuseStep 1446115 = 2169173) B2169173
theorem B6508835 : Blo 1283960 6508835 := bstep (se 1 (by rfl) ⟨4881626, by rfl⟩ : syracuseStep 6508835 = 9763253) B9763253
theorem B1626419 : Blo 1283960 1626419 := bstep (se 1 (by rfl) ⟨1219814, by rfl⟩ : syracuseStep 1626419 = 2439629) B2439629
theorem B1855795 : Blo 1283960 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B6173005 : Blo 1283960 6173005 := bstep (se 3 (by rfl) ⟨1157438, by rfl⟩ : syracuseStep 6173005 = 2314877) B2314877
theorem B2167121 : Blo 1283960 2167121 := bstep (se 2 (by rfl) ⟨812670, by rfl⟩ : syracuseStep 2167121 = 1625341) B1625341
theorem B12513649 : Blo 1283960 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B1446259 : Blo 1283960 1446259 := bstep (se 1 (by rfl) ⟨1084694, by rfl⟩ : syracuseStep 1446259 = 2169389) B2169389
theorem B2167249 : Blo 1283960 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B1954273 : Blo 1283960 1954273 := bstep (se 2 (by rfl) ⟨732852, by rfl⟩ : syracuseStep 1954273 = 1465705) B1465705
theorem B4116977 : Blo 1283960 4116977 := bstep (se 2 (by rfl) ⟨1543866, by rfl⟩ : syracuseStep 4116977 = 3087733) B3087733
theorem B2167283 : Blo 1283960 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B1446403 : Blo 1283960 1446403 := bstep (se 1 (by rfl) ⟨1084802, by rfl⟩ : syracuseStep 1446403 = 2169605) B2169605
theorem B5485133 : Blo 1283960 5485133 := bstep (se 3 (by rfl) ⟨1028462, by rfl⟩ : syracuseStep 5485133 = 2056925) B2056925
theorem B8237645 : Blo 1283960 8237645 := bstep (se 3 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 8237645 = 3089117) B3089117
theorem B2167411 : Blo 1283960 2167411 := bstep (se 1 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 2167411 = 3251117) B3251117
theorem B3658385 : Blo 1283960 3658385 := bstep (se 2 (by rfl) ⟨1371894, by rfl⟩ : syracuseStep 3658385 = 2743789) B2743789
theorem B1446547 : Blo 1283960 1446547 := bstep (se 1 (by rfl) ⟨1084910, by rfl⟩ : syracuseStep 1446547 = 2169821) B2169821
theorem B4879075 : Blo 1283960 4879075 := bstep (se 1 (by rfl) ⟨3659306, by rfl⟩ : syracuseStep 4879075 = 7318613) B7318613
theorem B4338413 : Blo 1283960 4338413 := bstep (se 3 (by rfl) ⟨813452, by rfl⟩ : syracuseStep 4338413 = 1626905) B1626905
theorem B2314993 : Blo 1283960 2314993 := bstep (se 2 (by rfl) ⟨868122, by rfl⟩ : syracuseStep 2314993 = 1736245) B1736245
theorem B2167553 : Blo 1283960 2167553 := bstep (se 2 (by rfl) ⟨812832, by rfl⟩ : syracuseStep 2167553 = 1625665) B1625665
theorem B4338467 : Blo 1283960 4338467 := bstep (se 1 (by rfl) ⟨3253850, by rfl⟩ : syracuseStep 4338467 = 6507701) B6507701
theorem B1446691 : Blo 1283960 1446691 := bstep (se 1 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 1446691 = 2170037) B2170037
theorem B2167681 : Blo 1283960 2167681 := bstep (se 2 (by rfl) ⟨812880, by rfl⟩ : syracuseStep 2167681 = 1625761) B1625761
theorem B5485475 : Blo 1283960 5485475 := bstep (se 1 (by rfl) ⟨4114106, by rfl⟩ : syracuseStep 5485475 = 8228213) B8228213
theorem B2167715 : Blo 1283960 2167715 := bstep (se 1 (by rfl) ⟨1625786, by rfl⟩ : syracuseStep 2167715 = 3251573) B3251573
theorem B1627123 : Blo 1283960 1627123 := bstep (se 1 (by rfl) ⟨1220342, by rfl⟩ : syracuseStep 1627123 = 2440685) B2440685
theorem B4174865 : Blo 1283960 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B2167843 : Blo 1283960 2167843 := bstep (se 1 (by rfl) ⟨1625882, by rfl⟩ : syracuseStep 2167843 = 3251765) B3251765
theorem B4338737 : Blo 1283960 4338737 := bstep (se 2 (by rfl) ⟨1627026, by rfl⟩ : syracuseStep 4338737 = 3254053) B3254053
theorem B3085379 : Blo 1283960 3085379 := bstep (se 1 (by rfl) ⟨2314034, by rfl⟩ : syracuseStep 3085379 = 4628069) B4628069
theorem B6509645 : Blo 1283960 6509645 := bstep (se 3 (by rfl) ⟨1220558, by rfl⟩ : syracuseStep 6509645 = 2441117) B2441117
theorem B1627219 : Blo 1283960 1627219 := bstep (se 1 (by rfl) ⟨1220414, by rfl⟩ : syracuseStep 1627219 = 2440829) B2440829
theorem B3298403 : Blo 1283960 3298403 := bstep (se 1 (by rfl) ⟨2473802, by rfl⟩ : syracuseStep 3298403 = 4947605) B4947605
theorem B2167985 : Blo 1283960 2167985 := bstep (se 2 (by rfl) ⟨812994, by rfl⟩ : syracuseStep 2167985 = 1625989) B1625989
theorem B2438353 : Blo 1283960 2438353 := bstep (se 2 (by rfl) ⟨914382, by rfl⟩ : syracuseStep 2438353 = 1828765) B1828765
theorem B23442659 : Blo 1283960 23442659 := bstep (se 1 (by rfl) ⟨17581994, by rfl⟩ : syracuseStep 23442659 = 35163989) B35163989
theorem B35165411 : Blo 1283960 35165411 := bstep (se 1 (by rfl) ⟨26374058, by rfl⟩ : syracuseStep 35165411 = 52748117) B52748117
theorem B2888945 : Blo 1283960 2888945 := bstep (se 2 (by rfl) ⟨1083354, by rfl⟩ : syracuseStep 2888945 = 2166709) B2166709
theorem B2888963 : Blo 1283960 2888963 := bstep (se 1 (by rfl) ⟨2166722, by rfl⟩ : syracuseStep 2888963 = 4333445) B4333445
theorem B2315555 : Blo 1283960 2315555 := bstep (se 1 (by rfl) ⟨1736666, by rfl⟩ : syracuseStep 2315555 = 3473333) B3473333
theorem B2168113 : Blo 1283960 2168113 := bstep (se 2 (by rfl) ⟨813042, by rfl⟩ : syracuseStep 2168113 = 1626085) B1626085
theorem B3659057 : Blo 1283960 3659057 := bstep (se 2 (by rfl) ⟨1372146, by rfl⟩ : syracuseStep 3659057 = 2744293) B2744293
theorem B7419185 : Blo 1283960 7419185 := bstep (se 2 (by rfl) ⟨2782194, by rfl⟩ : syracuseStep 7419185 = 5564389) B5564389
theorem B4117837 : Blo 1283960 4117837 := bstep (se 3 (by rfl) ⟨772094, by rfl⟩ : syracuseStep 4117837 = 1544189) B1544189
theorem B2168147 : Blo 1283960 2168147 := bstep (se 1 (by rfl) ⟨1626110, by rfl⟩ : syracuseStep 2168147 = 3252221) B3252221
theorem B7312781 : Blo 1283960 7312781 := bstep (se 3 (by rfl) ⟨1371146, by rfl⟩ : syracuseStep 7312781 = 2742293) B2742293
theorem B2168275 : Blo 1283960 2168275 := bstep (se 1 (by rfl) ⟨1626206, by rfl⟩ : syracuseStep 2168275 = 3252413) B3252413
theorem B2889233 : Blo 1283960 2889233 := bstep (se 2 (by rfl) ⟨1083462, by rfl⟩ : syracuseStep 2889233 = 2166925) B2166925
theorem B2889251 : Blo 1283960 2889251 := bstep (se 1 (by rfl) ⟨2166938, by rfl⟩ : syracuseStep 2889251 = 4333877) B4333877
theorem B4339277 : Blo 1283960 4339277 := bstep (se 3 (by rfl) ⟨813614, by rfl⟩ : syracuseStep 4339277 = 1627229) B1627229
theorem B2168417 : Blo 1283960 2168417 := bstep (se 2 (by rfl) ⟨813156, by rfl⟩ : syracuseStep 2168417 = 1626313) B1626313
theorem B4339331 : Blo 1283960 4339331 := bstep (se 1 (by rfl) ⟨3254498, by rfl⟩ : syracuseStep 4339331 = 6508997) B6508997
theorem B3905165 : Blo 1283960 3905165 := bstep (se 3 (by rfl) ⟨732218, by rfl⟩ : syracuseStep 3905165 = 1464437) B1464437
theorem B2168545 : Blo 1283960 2168545 := bstep (se 2 (by rfl) ⟨813204, by rfl⟩ : syracuseStep 2168545 = 1626409) B1626409
theorem B2168579 : Blo 1283960 2168579 := bstep (se 1 (by rfl) ⟨1626434, by rfl⟩ : syracuseStep 2168579 = 3252869) B3252869
theorem B3471149 : Blo 1283960 3471149 := bstep (se 3 (by rfl) ⟨650840, by rfl⟩ : syracuseStep 3471149 = 1301681) B1301681
theorem B2889521 : Blo 1283960 2889521 := bstep (se 2 (by rfl) ⟨1083570, by rfl⟩ : syracuseStep 2889521 = 2167141) B2167141
theorem B6502193 : Blo 1283960 6502193 := bstep (se 2 (by rfl) ⟨2438322, by rfl⟩ : syracuseStep 6502193 = 4876645) B4876645
theorem B2889539 : Blo 1283960 2889539 := bstep (se 1 (by rfl) ⟨2167154, by rfl⟩ : syracuseStep 2889539 = 4334309) B4334309
theorem B1283971 : Blo 1283960 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B2168707 : Blo 1283960 2168707 := bstep (se 1 (by rfl) ⟨1626530, by rfl⟩ : syracuseStep 2168707 = 3253061) B3253061
theorem B41662349 : Blo 1283960 41662349 := bstep (se 3 (by rfl) ⟨7811690, by rfl⟩ : syracuseStep 41662349 = 15623381) B15623381
theorem B4339601 : Blo 1283960 4339601 := bstep (se 2 (by rfl) ⟨1627350, by rfl⟩ : syracuseStep 4339601 = 3254701) B3254701
theorem B1283987 : Blo 1283960 1283987 := bstep (se 1 (by rfl) ⟨962990, by rfl⟩ : syracuseStep 1283987 = 1925981) B1925981
theorem B1284003 : Blo 1283960 1284003 := bstep (se 1 (by rfl) ⟨963002, by rfl⟩ : syracuseStep 1284003 = 1926005) B1926005
theorem B1284019 : Blo 1283960 1284019 := bstep (se 1 (by rfl) ⟨963014, by rfl⟩ : syracuseStep 1284019 = 1926029) B1926029
theorem B3250115 : Blo 1283960 3250115 := bstep (se 1 (by rfl) ⟨2437586, by rfl⟩ : syracuseStep 3250115 = 4875173) B4875173
theorem B1284035 : Blo 1283960 1284035 := bstep (se 1 (by rfl) ⟨963026, by rfl⟩ : syracuseStep 1284035 = 1926053) B1926053
theorem B1284051 : Blo 1283960 1284051 := bstep (se 1 (by rfl) ⟨963038, by rfl⟩ : syracuseStep 1284051 = 1926077) B1926077
theorem B1284067 : Blo 1283960 1284067 := bstep (se 1 (by rfl) ⟨963050, by rfl⟩ : syracuseStep 1284067 = 1926101) B1926101
theorem B1284083 : Blo 1283960 1284083 := bstep (se 1 (by rfl) ⟨963062, by rfl⟩ : syracuseStep 1284083 = 1926125) B1926125
theorem B1284099 : Blo 1283960 1284099 := bstep (se 1 (by rfl) ⟨963074, by rfl⟩ : syracuseStep 1284099 = 1926149) B1926149
theorem B2168849 : Blo 1283960 2168849 := bstep (se 2 (by rfl) ⟨813318, by rfl⟩ : syracuseStep 2168849 = 1626637) B1626637
theorem B1284115 : Blo 1283960 1284115 := bstep (se 1 (by rfl) ⟨963086, by rfl⟩ : syracuseStep 1284115 = 1926173) B1926173
theorem B29677589 : Blo 1283960 29677589 := bstep (se 6 (by rfl) ⟨695568, by rfl⟩ : syracuseStep 29677589 = 1391137) B1391137
theorem B1284131 : Blo 1283960 1284131 := bstep (se 1 (by rfl) ⟨963098, by rfl⟩ : syracuseStep 1284131 = 1926197) B1926197
theorem B2504753 : Blo 1283960 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B1284147 : Blo 1283960 1284147 := bstep (se 1 (by rfl) ⟨963110, by rfl⟩ : syracuseStep 1284147 = 1926221) B1926221
theorem B1284163 : Blo 1283960 1284163 := bstep (se 1 (by rfl) ⟨963122, by rfl⟩ : syracuseStep 1284163 = 1926245) B1926245
theorem B3659843 : Blo 1283960 3659843 := bstep (se 1 (by rfl) ⟨2744882, by rfl⟩ : syracuseStep 3659843 = 5489765) B5489765
theorem B3962947 : Blo 1283960 3962947 := bstep (se 1 (by rfl) ⟨2972210, by rfl⟩ : syracuseStep 3962947 = 5944421) B5944421
theorem B2889809 : Blo 1283960 2889809 := bstep (se 2 (by rfl) ⟨1083678, by rfl⟩ : syracuseStep 2889809 = 2167357) B2167357
theorem B1284179 : Blo 1283960 1284179 := bstep (se 1 (by rfl) ⟨963134, by rfl⟩ : syracuseStep 1284179 = 1926269) B1926269
theorem B1284195 : Blo 1283960 1284195 := bstep (se 1 (by rfl) ⟨963146, by rfl⟩ : syracuseStep 1284195 = 1926293) B1926293
theorem B2889827 : Blo 1283960 2889827 := bstep (se 1 (by rfl) ⟨2167370, by rfl⟩ : syracuseStep 2889827 = 4334741) B4334741
theorem B1284211 : Blo 1283960 1284211 := bstep (se 1 (by rfl) ⟨963158, by rfl⟩ : syracuseStep 1284211 = 1926317) B1926317
theorem B3250307 : Blo 1283960 3250307 := bstep (se 1 (by rfl) ⟨2437730, by rfl⟩ : syracuseStep 3250307 = 4875461) B4875461
theorem B1284227 : Blo 1283960 1284227 := bstep (se 1 (by rfl) ⟨963170, by rfl⟩ : syracuseStep 1284227 = 1926341) B1926341
theorem B2168977 : Blo 1283960 2168977 := bstep (se 2 (by rfl) ⟨813366, by rfl⟩ : syracuseStep 2168977 = 1626733) B1626733
theorem B1284243 : Blo 1283960 1284243 := bstep (se 1 (by rfl) ⟨963182, by rfl⟩ : syracuseStep 1284243 = 1926365) B1926365
theorem B1284259 : Blo 1283960 1284259 := bstep (se 1 (by rfl) ⟨963194, by rfl⟩ : syracuseStep 1284259 = 1926389) B1926389
theorem B1284275 : Blo 1283960 1284275 := bstep (se 1 (by rfl) ⟨963206, by rfl⟩ : syracuseStep 1284275 = 1926413) B1926413
theorem B2169011 : Blo 1283960 2169011 := bstep (se 1 (by rfl) ⟨1626758, by rfl⟩ : syracuseStep 2169011 = 3253517) B3253517
theorem B1284291 : Blo 1283960 1284291 := bstep (se 1 (by rfl) ⟨963218, by rfl⟩ : syracuseStep 1284291 = 1926437) B1926437
theorem B1284307 : Blo 1283960 1284307 := bstep (se 1 (by rfl) ⟨963230, by rfl⟩ : syracuseStep 1284307 = 1926461) B1926461
theorem B66771157 : Blo 1283960 66771157 := bstep (se 7 (by rfl) ⟨782474, by rfl⟩ : syracuseStep 66771157 = 1564949) B1564949
theorem B1284323 : Blo 1283960 1284323 := bstep (se 1 (by rfl) ⟨963242, by rfl⟩ : syracuseStep 1284323 = 1926485) B1926485
theorem B10975459 : Blo 1283960 10975459 := bstep (se 1 (by rfl) ⟨8231594, by rfl⟩ : syracuseStep 10975459 = 16463189) B16463189
theorem B2439409 : Blo 1283960 2439409 := bstep (se 2 (by rfl) ⟨914778, by rfl⟩ : syracuseStep 2439409 = 1829557) B1829557
theorem B1284339 : Blo 1283960 1284339 := bstep (se 1 (by rfl) ⟨963254, by rfl⟩ : syracuseStep 1284339 = 1926509) B1926509
theorem B1284355 : Blo 1283960 1284355 := bstep (se 1 (by rfl) ⟨963266, by rfl⟩ : syracuseStep 1284355 = 1926533) B1926533
theorem B1284371 : Blo 1283960 1284371 := bstep (se 1 (by rfl) ⟨963278, by rfl⟩ : syracuseStep 1284371 = 1926557) B1926557
theorem B1284387 : Blo 1283960 1284387 := bstep (se 1 (by rfl) ⟨963290, by rfl⟩ : syracuseStep 1284387 = 1926581) B1926581
theorem B1284403 : Blo 1283960 1284403 := bstep (se 1 (by rfl) ⟨963302, by rfl⟩ : syracuseStep 1284403 = 1926605) B1926605
theorem B2169139 : Blo 1283960 2169139 := bstep (se 1 (by rfl) ⟨1626854, by rfl⟩ : syracuseStep 2169139 = 3253709) B3253709
theorem B1284419 : Blo 1283960 1284419 := bstep (se 1 (by rfl) ⟨963314, by rfl⟩ : syracuseStep 1284419 = 1926629) B1926629
theorem B1284435 : Blo 1283960 1284435 := bstep (se 1 (by rfl) ⟨963326, by rfl⟩ : syracuseStep 1284435 = 1926653) B1926653
theorem B1284451 : Blo 1283960 1284451 := bstep (se 1 (by rfl) ⟨963338, by rfl⟩ : syracuseStep 1284451 = 1926677) B1926677
theorem B2890097 : Blo 1283960 2890097 := bstep (se 2 (by rfl) ⟨1083786, by rfl⟩ : syracuseStep 2890097 = 2167573) B2167573
theorem B1284467 : Blo 1283960 1284467 := bstep (se 1 (by rfl) ⟨963350, by rfl⟩ : syracuseStep 1284467 = 1926701) B1926701
theorem B1284483 : Blo 1283960 1284483 := bstep (se 1 (by rfl) ⟨963362, by rfl⟩ : syracuseStep 1284483 = 1926725) B1926725
theorem B2890115 : Blo 1283960 2890115 := bstep (se 1 (by rfl) ⟨2167586, by rfl⟩ : syracuseStep 2890115 = 4335173) B4335173
theorem B3660173 : Blo 1283960 3660173 := bstep (se 3 (by rfl) ⟨686282, by rfl⟩ : syracuseStep 3660173 = 1372565) B1372565
theorem B1284499 : Blo 1283960 1284499 := bstep (se 1 (by rfl) ⟨963374, by rfl⟩ : syracuseStep 1284499 = 1926749) B1926749
theorem B1284515 : Blo 1283960 1284515 := bstep (se 1 (by rfl) ⟨963386, by rfl⟩ : syracuseStep 1284515 = 1926773) B1926773
theorem B1284531 : Blo 1283960 1284531 := bstep (se 1 (by rfl) ⟨963398, by rfl⟩ : syracuseStep 1284531 = 1926797) B1926797
theorem B2169281 : Blo 1283960 2169281 := bstep (se 2 (by rfl) ⟨813480, by rfl⟩ : syracuseStep 2169281 = 1626961) B1626961
theorem B1284547 : Blo 1283960 1284547 := bstep (se 1 (by rfl) ⟨963410, by rfl⟩ : syracuseStep 1284547 = 1926821) B1926821
theorem B3660241 : Blo 1283960 3660241 := bstep (se 2 (by rfl) ⟨1372590, by rfl⟩ : syracuseStep 3660241 = 2745181) B2745181
theorem B1284563 : Blo 1283960 1284563 := bstep (se 1 (by rfl) ⟨963422, by rfl⟩ : syracuseStep 1284563 = 1926845) B1926845
theorem B1284579 : Blo 1283960 1284579 := bstep (se 1 (by rfl) ⟨963434, by rfl⟩ : syracuseStep 1284579 = 1926869) B1926869
theorem B3709421 : Blo 1283960 3709421 := bstep (se 3 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 3709421 = 1391033) B1391033
theorem B1284595 : Blo 1283960 1284595 := bstep (se 1 (by rfl) ⟨963446, by rfl⟩ : syracuseStep 1284595 = 1926893) B1926893
theorem B1284611 : Blo 1283960 1284611 := bstep (se 1 (by rfl) ⟨963458, by rfl⟩ : syracuseStep 1284611 = 1926917) B1926917
theorem B1284627 : Blo 1283960 1284627 := bstep (se 1 (by rfl) ⟨963470, by rfl⟩ : syracuseStep 1284627 = 1926941) B1926941
theorem B1284643 : Blo 1283960 1284643 := bstep (se 1 (by rfl) ⟨963482, by rfl⟩ : syracuseStep 1284643 = 1926965) B1926965
theorem B1284659 : Blo 1283960 1284659 := bstep (se 1 (by rfl) ⟨963494, by rfl⟩ : syracuseStep 1284659 = 1926989) B1926989
theorem B2169409 : Blo 1283960 2169409 := bstep (se 2 (by rfl) ⟨813528, by rfl⟩ : syracuseStep 2169409 = 1627057) B1627057
theorem B1284675 : Blo 1283960 1284675 := bstep (se 1 (by rfl) ⟨963506, by rfl⟩ : syracuseStep 1284675 = 1927013) B1927013
theorem B1284691 : Blo 1283960 1284691 := bstep (se 1 (by rfl) ⟨963518, by rfl⟩ : syracuseStep 1284691 = 1927037) B1927037
theorem B1284707 : Blo 1283960 1284707 := bstep (se 1 (by rfl) ⟨963530, by rfl⟩ : syracuseStep 1284707 = 1927061) B1927061
theorem B2169443 : Blo 1283960 2169443 := bstep (se 1 (by rfl) ⟨1627082, by rfl⟩ : syracuseStep 2169443 = 3254165) B3254165
theorem B1284723 : Blo 1283960 1284723 := bstep (se 1 (by rfl) ⟨963542, by rfl⟩ : syracuseStep 1284723 = 1927085) B1927085
theorem B1284739 : Blo 1283960 1284739 := bstep (se 1 (by rfl) ⟨963554, by rfl⟩ : syracuseStep 1284739 = 1927109) B1927109
theorem B2439811 : Blo 1283960 2439811 := bstep (se 1 (by rfl) ⟨1829858, by rfl⟩ : syracuseStep 2439811 = 3659717) B3659717
theorem B2890385 : Blo 1283960 2890385 := bstep (se 2 (by rfl) ⟨1083894, by rfl⟩ : syracuseStep 2890385 = 2167789) B2167789
theorem B1284755 : Blo 1283960 1284755 := bstep (se 1 (by rfl) ⟨963566, by rfl⟩ : syracuseStep 1284755 = 1927133) B1927133
theorem B2890403 : Blo 1283960 2890403 := bstep (se 1 (by rfl) ⟨2167802, by rfl⟩ : syracuseStep 2890403 = 4335605) B4335605
theorem B1284771 : Blo 1283960 1284771 := bstep (se 1 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 1284771 = 1927157) B1927157
theorem B2439857 : Blo 1283960 2439857 := bstep (se 2 (by rfl) ⟨914946, by rfl⟩ : syracuseStep 2439857 = 1829893) B1829893
theorem B1284787 : Blo 1283960 1284787 := bstep (se 1 (by rfl) ⟨963590, by rfl⟩ : syracuseStep 1284787 = 1927181) B1927181
theorem B1284803 : Blo 1283960 1284803 := bstep (se 1 (by rfl) ⟨963602, by rfl⟩ : syracuseStep 1284803 = 1927205) B1927205
theorem B4397773 : Blo 1283960 4397773 := bstep (se 3 (by rfl) ⟨824582, by rfl⟩ : syracuseStep 4397773 = 1649165) B1649165
theorem B1284819 : Blo 1283960 1284819 := bstep (se 1 (by rfl) ⟨963614, by rfl⟩ : syracuseStep 1284819 = 1927229) B1927229
theorem B1284835 : Blo 1283960 1284835 := bstep (se 1 (by rfl) ⟨963626, by rfl⟩ : syracuseStep 1284835 = 1927253) B1927253
theorem B3660515 : Blo 1283960 3660515 := bstep (se 1 (by rfl) ⟨2745386, by rfl⟩ : syracuseStep 3660515 = 5490773) B5490773
theorem B2169571 : Blo 1283960 2169571 := bstep (se 1 (by rfl) ⟨1627178, by rfl⟩ : syracuseStep 2169571 = 3254357) B3254357
theorem B1284851 : Blo 1283960 1284851 := bstep (se 1 (by rfl) ⟨963638, by rfl⟩ : syracuseStep 1284851 = 1927277) B1927277
theorem B3906307 : Blo 1283960 3906307 := bstep (se 1 (by rfl) ⟨2929730, by rfl⟩ : syracuseStep 3906307 = 5859461) B5859461
theorem B1284867 : Blo 1283960 1284867 := bstep (se 1 (by rfl) ⟨963650, by rfl⟩ : syracuseStep 1284867 = 1927301) B1927301
theorem B1284883 : Blo 1283960 1284883 := bstep (se 1 (by rfl) ⟨963662, by rfl⟩ : syracuseStep 1284883 = 1927325) B1927325
theorem B1284899 : Blo 1283960 1284899 := bstep (se 1 (by rfl) ⟨963674, by rfl⟩ : syracuseStep 1284899 = 1927349) B1927349
theorem B1284915 : Blo 1283960 1284915 := bstep (se 1 (by rfl) ⟨963686, by rfl⟩ : syracuseStep 1284915 = 1927373) B1927373
theorem B1284931 : Blo 1283960 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B1284947 : Blo 1283960 1284947 := bstep (se 1 (by rfl) ⟨963710, by rfl⟩ : syracuseStep 1284947 = 1927421) B1927421
theorem B1284963 : Blo 1283960 1284963 := bstep (se 1 (by rfl) ⟨963722, by rfl⟩ : syracuseStep 1284963 = 1927445) B1927445
theorem B2169713 : Blo 1283960 2169713 := bstep (se 2 (by rfl) ⟨813642, by rfl⟩ : syracuseStep 2169713 = 1627285) B1627285
theorem B1284979 : Blo 1283960 1284979 := bstep (se 1 (by rfl) ⟨963734, by rfl⟩ : syracuseStep 1284979 = 1927469) B1927469
theorem B1735553 : Blo 1283960 1735553 := bstep (se 2 (by rfl) ⟨650832, by rfl⟩ : syracuseStep 1735553 = 1301665) B1301665
theorem B1284995 : Blo 1283960 1284995 := bstep (se 1 (by rfl) ⟨963746, by rfl⟩ : syracuseStep 1284995 = 1927493) B1927493
theorem B4881293 : Blo 1283960 4881293 := bstep (se 3 (by rfl) ⟨915242, by rfl⟩ : syracuseStep 4881293 = 1830485) B1830485
theorem B4119437 : Blo 1283960 4119437 := bstep (se 3 (by rfl) ⟨772394, by rfl⟩ : syracuseStep 4119437 = 1544789) B1544789
theorem B1285011 : Blo 1283960 1285011 := bstep (se 1 (by rfl) ⟨963758, by rfl⟩ : syracuseStep 1285011 = 1927517) B1927517
theorem B1285027 : Blo 1283960 1285027 := bstep (se 1 (by rfl) ⟨963770, by rfl⟩ : syracuseStep 1285027 = 1927541) B1927541
theorem B2890673 : Blo 1283960 2890673 := bstep (se 2 (by rfl) ⟨1084002, by rfl⟩ : syracuseStep 2890673 = 2168005) B2168005
theorem B1285043 : Blo 1283960 1285043 := bstep (se 1 (by rfl) ⟨963782, by rfl⟩ : syracuseStep 1285043 = 1927565) B1927565
theorem B2890691 : Blo 1283960 2890691 := bstep (se 1 (by rfl) ⟨2168018, by rfl⟩ : syracuseStep 2890691 = 4336037) B4336037
theorem B1285059 : Blo 1283960 1285059 := bstep (se 1 (by rfl) ⟨963794, by rfl⟩ : syracuseStep 1285059 = 1927589) B1927589
theorem B31267781 : Blo 1283960 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B2440145 : Blo 1283960 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B1285075 : Blo 1283960 1285075 := bstep (se 1 (by rfl) ⟨963806, by rfl⟩ : syracuseStep 1285075 = 1927613) B1927613
theorem B1285091 : Blo 1283960 1285091 := bstep (se 1 (by rfl) ⟨963818, by rfl⟩ : syracuseStep 1285091 = 1927637) B1927637
theorem B2169841 : Blo 1283960 2169841 := bstep (se 2 (by rfl) ⟨813690, by rfl⟩ : syracuseStep 2169841 = 1627381) B1627381
theorem B1285107 : Blo 1283960 1285107 := bstep (se 1 (by rfl) ⟨963830, by rfl⟩ : syracuseStep 1285107 = 1927661) B1927661
theorem B1285123 : Blo 1283960 1285123 := bstep (se 1 (by rfl) ⟨963842, by rfl⟩ : syracuseStep 1285123 = 1927685) B1927685
theorem B2259971 : Blo 1283960 2259971 := bstep (se 1 (by rfl) ⟨1694978, by rfl⟩ : syracuseStep 2259971 = 3389957) B3389957
theorem B1285139 : Blo 1283960 1285139 := bstep (se 1 (by rfl) ⟨963854, by rfl⟩ : syracuseStep 1285139 = 1927709) B1927709
theorem B2169875 : Blo 1283960 2169875 := bstep (se 1 (by rfl) ⟨1627406, by rfl⟩ : syracuseStep 2169875 = 3254813) B3254813
theorem B1735715 : Blo 1283960 1735715 := bstep (se 1 (by rfl) ⟨1301786, by rfl⟩ : syracuseStep 1735715 = 2603573) B2603573
theorem B1285155 : Blo 1283960 1285155 := bstep (se 1 (by rfl) ⟨963866, by rfl⟩ : syracuseStep 1285155 = 1927733) B1927733
theorem B4627505 : Blo 1283960 4627505 := bstep (se 2 (by rfl) ⟨1735314, by rfl⟩ : syracuseStep 4627505 = 3470629) B3470629
theorem B3251249 : Blo 1283960 3251249 := bstep (se 2 (by rfl) ⟨1219218, by rfl⟩ : syracuseStep 3251249 = 2438437) B2438437
theorem B1285171 : Blo 1283960 1285171 := bstep (se 1 (by rfl) ⟨963878, by rfl⟩ : syracuseStep 1285171 = 1927757) B1927757
theorem B1285187 : Blo 1283960 1285187 := bstep (se 1 (by rfl) ⟨963890, by rfl⟩ : syracuseStep 1285187 = 1927781) B1927781
theorem B8232005 : Blo 1283960 8232005 := bstep (se 4 (by rfl) ⟨771750, by rfl⟩ : syracuseStep 8232005 = 1543501) B1543501
theorem B1285203 : Blo 1283960 1285203 := bstep (se 1 (by rfl) ⟨963902, by rfl⟩ : syracuseStep 1285203 = 1927805) B1927805
theorem B3251299 : Blo 1283960 3251299 := bstep (se 1 (by rfl) ⟨2438474, by rfl⟩ : syracuseStep 3251299 = 4876949) B4876949
theorem B1285219 : Blo 1283960 1285219 := bstep (se 1 (by rfl) ⟨963914, by rfl⟩ : syracuseStep 1285219 = 1927829) B1927829
theorem B1285235 : Blo 1283960 1285235 := bstep (se 1 (by rfl) ⟨963926, by rfl⟩ : syracuseStep 1285235 = 1927853) B1927853
theorem B1285251 : Blo 1283960 1285251 := bstep (se 1 (by rfl) ⟨963938, by rfl⟩ : syracuseStep 1285251 = 1927877) B1927877
theorem B15850637 : Blo 1283960 15850637 := bstep (se 3 (by rfl) ⟨2971994, by rfl⟩ : syracuseStep 15850637 = 5943989) B5943989
theorem B1285267 : Blo 1283960 1285267 := bstep (se 1 (by rfl) ⟨963950, by rfl⟩ : syracuseStep 1285267 = 1927901) B1927901
theorem B2170003 : Blo 1283960 2170003 := bstep (se 1 (by rfl) ⟨1627502, by rfl⟩ : syracuseStep 2170003 = 3255005) B3255005
theorem B1285283 : Blo 1283960 1285283 := bstep (se 1 (by rfl) ⟨963962, by rfl⟩ : syracuseStep 1285283 = 1927925) B1927925
theorem B1285299 : Blo 1283960 1285299 := bstep (se 1 (by rfl) ⟨963974, by rfl⟩ : syracuseStep 1285299 = 1927949) B1927949
theorem B1285315 : Blo 1283960 1285315 := bstep (se 1 (by rfl) ⟨963986, by rfl⟩ : syracuseStep 1285315 = 1927973) B1927973
theorem B2890961 : Blo 1283960 2890961 := bstep (se 2 (by rfl) ⟨1084110, by rfl⟩ : syracuseStep 2890961 = 2168221) B2168221
theorem B1285331 : Blo 1283960 1285331 := bstep (se 1 (by rfl) ⟨963998, by rfl⟩ : syracuseStep 1285331 = 1927997) B1927997
theorem B6503651 : Blo 1283960 6503651 := bstep (se 1 (by rfl) ⟨4877738, by rfl⟩ : syracuseStep 6503651 = 9755477) B9755477
theorem B2890979 : Blo 1283960 2890979 := bstep (se 1 (by rfl) ⟨2168234, by rfl⟩ : syracuseStep 2890979 = 4336469) B4336469
theorem B1285347 : Blo 1283960 1285347 := bstep (se 1 (by rfl) ⟨964010, by rfl⟩ : syracuseStep 1285347 = 1928021) B1928021
theorem B24714467 : Blo 1283960 24714467 := bstep (se 1 (by rfl) ⟨18535850, by rfl⟩ : syracuseStep 24714467 = 37071701) B37071701
theorem B3251441 : Blo 1283960 3251441 := bstep (se 2 (by rfl) ⟨1219290, by rfl⟩ : syracuseStep 3251441 = 2438581) B2438581
theorem B1285363 : Blo 1283960 1285363 := bstep (se 1 (by rfl) ⟨964022, by rfl⟩ : syracuseStep 1285363 = 1928045) B1928045
theorem B1285379 : Blo 1283960 1285379 := bstep (se 1 (by rfl) ⟨964034, by rfl⟩ : syracuseStep 1285379 = 1928069) B1928069
theorem B7519493 : Blo 1283960 7519493 := bstep (se 4 (by rfl) ⟨704952, by rfl⟩ : syracuseStep 7519493 = 1409905) B1409905
theorem B1285395 : Blo 1283960 1285395 := bstep (se 1 (by rfl) ⟨964046, by rfl⟩ : syracuseStep 1285395 = 1928093) B1928093
theorem B1285411 : Blo 1283960 1285411 := bstep (se 1 (by rfl) ⟨964058, by rfl⟩ : syracuseStep 1285411 = 1928117) B1928117
theorem B1285427 : Blo 1283960 1285427 := bstep (se 1 (by rfl) ⟨964070, by rfl⟩ : syracuseStep 1285427 = 1928141) B1928141
theorem B1285443 : Blo 1283960 1285443 := bstep (se 1 (by rfl) ⟨964082, by rfl⟩ : syracuseStep 1285443 = 1928165) B1928165
theorem B1285459 : Blo 1283960 1285459 := bstep (se 1 (by rfl) ⟨964094, by rfl⟩ : syracuseStep 1285459 = 1928189) B1928189
theorem B1285475 : Blo 1283960 1285475 := bstep (se 1 (by rfl) ⟨964106, by rfl⟩ : syracuseStep 1285475 = 1928213) B1928213
theorem B1301875 : Blo 1283960 1301875 := bstep (se 1 (by rfl) ⟨976406, by rfl⟩ : syracuseStep 1301875 = 1952813) B1952813
theorem B1285491 : Blo 1283960 1285491 := bstep (se 1 (by rfl) ⟨964118, by rfl⟩ : syracuseStep 1285491 = 1928237) B1928237
theorem B1285507 : Blo 1283960 1285507 := bstep (se 1 (by rfl) ⟨964130, by rfl⟩ : syracuseStep 1285507 = 1928261) B1928261
theorem B4627853 : Blo 1283960 4627853 := bstep (se 3 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 4627853 = 1735445) B1735445
theorem B1285523 : Blo 1283960 1285523 := bstep (se 1 (by rfl) ⟨964142, by rfl⟩ : syracuseStep 1285523 = 1928285) B1928285
theorem B1285539 : Blo 1283960 1285539 := bstep (se 1 (by rfl) ⟨964154, by rfl⟩ : syracuseStep 1285539 = 1928309) B1928309
theorem B1285555 : Blo 1283960 1285555 := bstep (se 1 (by rfl) ⟨964166, by rfl⟩ : syracuseStep 1285555 = 1928333) B1928333
theorem B1285571 : Blo 1283960 1285571 := bstep (se 1 (by rfl) ⟨964178, by rfl⟩ : syracuseStep 1285571 = 1928357) B1928357
theorem B1285587 : Blo 1283960 1285587 := bstep (se 1 (by rfl) ⟨964190, by rfl⟩ : syracuseStep 1285587 = 1928381) B1928381
theorem B1285603 : Blo 1283960 1285603 := bstep (se 1 (by rfl) ⟨964202, by rfl⟩ : syracuseStep 1285603 = 1928405) B1928405
theorem B2891249 : Blo 1283960 2891249 := bstep (se 2 (by rfl) ⟨1084218, by rfl⟩ : syracuseStep 2891249 = 2168437) B2168437
theorem B11886065 : Blo 1283960 11886065 := bstep (se 2 (by rfl) ⟨4457274, by rfl⟩ : syracuseStep 11886065 = 8914549) B8914549
theorem B1736179 : Blo 1283960 1736179 := bstep (se 1 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 1736179 = 2604269) B2604269
theorem B1285619 : Blo 1283960 1285619 := bstep (se 1 (by rfl) ⟨964214, by rfl⟩ : syracuseStep 1285619 = 1928429) B1928429
theorem B2891267 : Blo 1283960 2891267 := bstep (se 1 (by rfl) ⟨2168450, by rfl⟩ : syracuseStep 2891267 = 4336901) B4336901
theorem B1285635 : Blo 1283960 1285635 := bstep (se 1 (by rfl) ⟨964226, by rfl⟩ : syracuseStep 1285635 = 1928453) B1928453
theorem B1285651 : Blo 1283960 1285651 := bstep (se 1 (by rfl) ⟨964238, by rfl⟩ : syracuseStep 1285651 = 1928477) B1928477
theorem B1285667 : Blo 1283960 1285667 := bstep (se 1 (by rfl) ⟨964250, by rfl⟩ : syracuseStep 1285667 = 1928501) B1928501
theorem B3661357 : Blo 1283960 3661357 := bstep (se 3 (by rfl) ⟨686504, by rfl⟩ : syracuseStep 3661357 = 1373009) B1373009
theorem B1285683 : Blo 1283960 1285683 := bstep (se 1 (by rfl) ⟨964262, by rfl⟩ : syracuseStep 1285683 = 1928525) B1928525
theorem B2604611 : Blo 1283960 2604611 := bstep (se 1 (by rfl) ⟨1953458, by rfl⟩ : syracuseStep 2604611 = 3906917) B3906917
theorem B1285699 : Blo 1283960 1285699 := bstep (se 1 (by rfl) ⟨964274, by rfl⟩ : syracuseStep 1285699 = 1928549) B1928549
theorem B1285715 : Blo 1283960 1285715 := bstep (se 1 (by rfl) ⟨964286, by rfl⟩ : syracuseStep 1285715 = 1928573) B1928573
theorem B1285731 : Blo 1283960 1285731 := bstep (se 1 (by rfl) ⟨964298, by rfl⟩ : syracuseStep 1285731 = 1928597) B1928597
theorem B1285747 : Blo 1283960 1285747 := bstep (se 1 (by rfl) ⟨964310, by rfl⟩ : syracuseStep 1285747 = 1928621) B1928621
theorem B1285763 : Blo 1283960 1285763 := bstep (se 1 (by rfl) ⟨964322, by rfl⟩ : syracuseStep 1285763 = 1928645) B1928645
theorem B1285779 : Blo 1283960 1285779 := bstep (se 1 (by rfl) ⟨964334, by rfl⟩ : syracuseStep 1285779 = 1928669) B1928669
theorem B2440867 : Blo 1283960 2440867 := bstep (se 1 (by rfl) ⟨1830650, by rfl⟩ : syracuseStep 2440867 = 3661301) B3661301
theorem B1285795 : Blo 1283960 1285795 := bstep (se 1 (by rfl) ⟨964346, by rfl⟩ : syracuseStep 1285795 = 1928693) B1928693
theorem B1285811 : Blo 1283960 1285811 := bstep (se 1 (by rfl) ⟨964358, by rfl⟩ : syracuseStep 1285811 = 1928717) B1928717
theorem B1285827 : Blo 1283960 1285827 := bstep (se 1 (by rfl) ⟨964370, by rfl⟩ : syracuseStep 1285827 = 1928741) B1928741
theorem B3661517 : Blo 1283960 3661517 := bstep (se 3 (by rfl) ⟨686534, by rfl⟩ : syracuseStep 3661517 = 1373069) B1373069
theorem B1285843 : Blo 1283960 1285843 := bstep (se 1 (by rfl) ⟨964382, by rfl⟩ : syracuseStep 1285843 = 1928765) B1928765
theorem B1285859 : Blo 1283960 1285859 := bstep (se 1 (by rfl) ⟨964394, by rfl⟩ : syracuseStep 1285859 = 1928789) B1928789
theorem B1285875 : Blo 1283960 1285875 := bstep (se 1 (by rfl) ⟨964406, by rfl⟩ : syracuseStep 1285875 = 1928813) B1928813
theorem B1285891 : Blo 1283960 1285891 := bstep (se 1 (by rfl) ⟨964418, by rfl⟩ : syracuseStep 1285891 = 1928837) B1928837
theorem B2891537 : Blo 1283960 2891537 := bstep (se 2 (by rfl) ⟨1084326, by rfl⟩ : syracuseStep 2891537 = 2168653) B2168653
theorem B1285907 : Blo 1283960 1285907 := bstep (se 1 (by rfl) ⟨964430, by rfl⟩ : syracuseStep 1285907 = 1928861) B1928861
theorem B2891555 : Blo 1283960 2891555 := bstep (se 1 (by rfl) ⟨2168666, by rfl⟩ : syracuseStep 2891555 = 4337333) B4337333
theorem B1285923 : Blo 1283960 1285923 := bstep (se 1 (by rfl) ⟨964442, by rfl⟩ : syracuseStep 1285923 = 1928885) B1928885
theorem B1285939 : Blo 1283960 1285939 := bstep (se 1 (by rfl) ⟨964454, by rfl⟩ : syracuseStep 1285939 = 1928909) B1928909
theorem B2744131 : Blo 1283960 2744131 := bstep (se 1 (by rfl) ⟨2058098, by rfl⟩ : syracuseStep 2744131 = 4116197) B4116197
theorem B1285955 : Blo 1283960 1285955 := bstep (se 1 (by rfl) ⟨964466, by rfl⟩ : syracuseStep 1285955 = 1928933) B1928933
theorem B3661699 : Blo 1283960 3661699 := bstep (se 1 (by rfl) ⟨2746274, by rfl⟩ : syracuseStep 3661699 = 5492549) B5492549
theorem B4333553 : Blo 1283960 4333553 := bstep (se 2 (by rfl) ⟨1625082, by rfl⟩ : syracuseStep 4333553 = 3250165) B3250165
theorem B4882477 : Blo 1283960 4882477 := bstep (se 3 (by rfl) ⟨915464, by rfl⟩ : syracuseStep 4882477 = 1830929) B1830929
theorem B5283929 : Blo 1283960 5283929 := bstep (se 2 (by rfl) ⟨1981473, by rfl⟩ : syracuseStep 5283929 = 3962947) B3962947
theorem B4333661 : Blo 1283960 4333661 := bstep (se 3 (by rfl) ⟨812561, by rfl⟩ : syracuseStep 4333661 = 1625123) B1625123
theorem B4628573 : Blo 1283960 4628573 := bstep (se 3 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 4628573 = 1735715) B1735715
theorem B2891915 : Blo 1283960 2891915 := bstep (se 1 (by rfl) ⟨2168936, by rfl⟩ : syracuseStep 2891915 = 4337873) B4337873
theorem B2891969 : Blo 1283960 2891969 := bstep (se 2 (by rfl) ⟨1084488, by rfl⟩ : syracuseStep 2891969 = 2168977) B2168977
theorem B3252545 : Blo 1283960 3252545 := bstep (se 2 (by rfl) ⟨1219704, by rfl⟩ : syracuseStep 3252545 = 2439409) B2439409
theorem B2744651 : Blo 1283960 2744651 := bstep (se 1 (by rfl) ⟨2058488, by rfl⟩ : syracuseStep 2744651 = 4116977) B4116977
theorem B10969445 : Blo 1283960 10969445 := bstep (se 4 (by rfl) ⟨1028385, by rfl⟩ : syracuseStep 10969445 = 2056771) B2056771
theorem B2892185 : Blo 1283960 2892185 := bstep (se 2 (by rfl) ⟨1084569, by rfl⟩ : syracuseStep 2892185 = 2169139) B2169139
theorem B2474393 : Blo 1283960 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B2892275 : Blo 1283960 2892275 := bstep (se 1 (by rfl) ⟨2169206, by rfl⟩ : syracuseStep 2892275 = 4338413) B4338413
theorem B2892311 : Blo 1283960 2892311 := bstep (se 1 (by rfl) ⟨2169233, by rfl⟩ : syracuseStep 2892311 = 4338467) B4338467
theorem B6685249 : Blo 1283960 6685249 := bstep (se 2 (by rfl) ⟨2506968, by rfl⟩ : syracuseStep 6685249 = 5013937) B5013937
theorem B35193437 : Blo 1283960 35193437 := bstep (se 3 (by rfl) ⟨6598769, by rfl⟩ : syracuseStep 35193437 = 13197539) B13197539
theorem B2605697 : Blo 1283960 2605697 := bstep (se 2 (by rfl) ⟨977136, by rfl⟩ : syracuseStep 2605697 = 1954273) B1954273
theorem B2892491 : Blo 1283960 2892491 := bstep (se 1 (by rfl) ⟨2169368, by rfl⟩ : syracuseStep 2892491 = 4338737) B4338737
theorem B2056919 : Blo 1283960 2056919 := bstep (se 1 (by rfl) ⟨1542689, by rfl⟩ : syracuseStep 2056919 = 3085379) B3085379
theorem B2892545 : Blo 1283960 2892545 := bstep (se 2 (by rfl) ⟨1084704, by rfl⟩ : syracuseStep 2892545 = 2169409) B2169409
theorem B1925963 : Blo 1283960 1925963 := bstep (se 1 (by rfl) ⟨1444472, by rfl⟩ : syracuseStep 1925963 = 2888945) B2888945
theorem B1925975 : Blo 1283960 1925975 := bstep (se 1 (by rfl) ⟨1444481, by rfl⟩ : syracuseStep 1925975 = 2888963) B2888963
theorem B3253081 : Blo 1283960 3253081 := bstep (se 2 (by rfl) ⟨1219905, by rfl⟩ : syracuseStep 3253081 = 2439811) B2439811
theorem B1926041 : Blo 1283960 1926041 := bstep (se 2 (by rfl) ⟨722265, by rfl⟩ : syracuseStep 1926041 = 1444531) B1444531
theorem B4875187 : Blo 1283960 4875187 := bstep (se 1 (by rfl) ⟨3656390, by rfl⟩ : syracuseStep 4875187 = 7312781) B7312781
theorem B6505433 : Blo 1283960 6505433 := bstep (se 2 (by rfl) ⟨2439537, by rfl⟩ : syracuseStep 6505433 = 4879075) B4879075
theorem B2892761 : Blo 1283960 2892761 := bstep (se 2 (by rfl) ⟨1084785, by rfl⟩ : syracuseStep 2892761 = 2169571) B2169571
theorem B1926155 : Blo 1283960 1926155 := bstep (se 1 (by rfl) ⟨1444616, by rfl⟩ : syracuseStep 1926155 = 2889233) B2889233
theorem B1926167 : Blo 1283960 1926167 := bstep (se 1 (by rfl) ⟨1444625, by rfl⟩ : syracuseStep 1926167 = 2889251) B2889251
theorem B2892851 : Blo 1283960 2892851 := bstep (se 1 (by rfl) ⟨2169638, by rfl⟩ : syracuseStep 2892851 = 4339277) B4339277
theorem B2892887 : Blo 1283960 2892887 := bstep (se 1 (by rfl) ⟨2169665, by rfl⟩ : syracuseStep 2892887 = 4339331) B4339331
theorem B1926233 : Blo 1283960 1926233 := bstep (se 2 (by rfl) ⟨722337, by rfl⟩ : syracuseStep 1926233 = 1444675) B1444675
theorem B5489815 : Blo 1283960 5489815 := bstep (se 1 (by rfl) ⟨4117361, by rfl⟩ : syracuseStep 5489815 = 8234723) B8234723
theorem B1926347 : Blo 1283960 1926347 := bstep (se 1 (by rfl) ⟨1444760, by rfl⟩ : syracuseStep 1926347 = 2889521) B2889521
theorem B4334795 : Blo 1283960 4334795 := bstep (se 1 (by rfl) ⟨3251096, by rfl⟩ : syracuseStep 4334795 = 6502193) B6502193
theorem B1926359 : Blo 1283960 1926359 := bstep (se 1 (by rfl) ⟨1444769, by rfl⟩ : syracuseStep 1926359 = 2889539) B2889539
theorem B2893067 : Blo 1283960 2893067 := bstep (se 1 (by rfl) ⟨2169800, by rfl⟩ : syracuseStep 2893067 = 4339601) B4339601
theorem B1926425 : Blo 1283960 1926425 := bstep (se 2 (by rfl) ⟨722409, by rfl⟩ : syracuseStep 1926425 = 1444819) B1444819
theorem B2893121 : Blo 1283960 2893121 := bstep (se 2 (by rfl) ⟨1084920, by rfl⟩ : syracuseStep 2893121 = 2169841) B2169841
theorem B2606411 : Blo 1283960 2606411 := bstep (se 1 (by rfl) ⟨1954808, by rfl⟩ : syracuseStep 2606411 = 3909617) B3909617
theorem B19785059 : Blo 1283960 19785059 := bstep (se 1 (by rfl) ⟨14838794, by rfl⟩ : syracuseStep 19785059 = 29677589) B29677589
theorem B7316837 : Blo 1283960 7316837 := bstep (se 4 (by rfl) ⟨685953, by rfl⟩ : syracuseStep 7316837 = 1371907) B1371907
theorem B1926539 : Blo 1283960 1926539 := bstep (se 1 (by rfl) ⟨1444904, by rfl⟩ : syracuseStep 1926539 = 2889809) B2889809
theorem B2196887 : Blo 1283960 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B1926551 : Blo 1283960 1926551 := bstep (se 1 (by rfl) ⟨1444913, by rfl⟩ : syracuseStep 1926551 = 2889827) B2889827
theorem B1926617 : Blo 1283960 1926617 := bstep (se 2 (by rfl) ⟨722481, by rfl⟩ : syracuseStep 1926617 = 1444963) B1444963
theorem B4335065 : Blo 1283960 4335065 := bstep (se 2 (by rfl) ⟨1625649, by rfl⟩ : syracuseStep 4335065 = 3251299) B3251299
theorem B2893337 : Blo 1283960 2893337 := bstep (se 2 (by rfl) ⟨1085001, by rfl⟩ : syracuseStep 2893337 = 2170003) B2170003
theorem B1926731 : Blo 1283960 1926731 := bstep (se 1 (by rfl) ⟨1445048, by rfl⟩ : syracuseStep 1926731 = 2890097) B2890097
theorem B1926743 : Blo 1283960 1926743 := bstep (se 1 (by rfl) ⟨1445057, by rfl⟩ : syracuseStep 1926743 = 2890115) B2890115
theorem B1926809 : Blo 1283960 1926809 := bstep (se 2 (by rfl) ⟨722553, by rfl⟩ : syracuseStep 1926809 = 1445107) B1445107
theorem B37578437 : Blo 1283960 37578437 := bstep (se 4 (by rfl) ⟨3522978, by rfl⟩ : syracuseStep 37578437 = 7045957) B7045957
theorem B3344075 : Blo 1283960 3344075 := bstep (se 1 (by rfl) ⟨2508056, by rfl⟩ : syracuseStep 3344075 = 5016113) B5016113
theorem B1926923 : Blo 1283960 1926923 := bstep (se 1 (by rfl) ⟨1445192, by rfl⟩ : syracuseStep 1926923 = 2890385) B2890385
theorem B5490449 : Blo 1283960 5490449 := bstep (se 2 (by rfl) ⟨2058918, by rfl⟩ : syracuseStep 5490449 = 4117837) B4117837
theorem B1926935 : Blo 1283960 1926935 := bstep (se 1 (by rfl) ⟨1445201, by rfl⟩ : syracuseStep 1926935 = 2890403) B2890403
theorem B1927001 : Blo 1283960 1927001 := bstep (se 2 (by rfl) ⟨722625, by rfl⟩ : syracuseStep 1927001 = 1445251) B1445251
theorem B3254195 : Blo 1283960 3254195 := bstep (se 1 (by rfl) ⟨2440646, by rfl⟩ : syracuseStep 3254195 = 4881293) B4881293
theorem B1927115 : Blo 1283960 1927115 := bstep (se 1 (by rfl) ⟨1445336, by rfl⟩ : syracuseStep 1927115 = 2890673) B2890673
theorem B10971085 : Blo 1283960 10971085 := bstep (se 3 (by rfl) ⟨2057078, by rfl⟩ : syracuseStep 10971085 = 4114157) B4114157
theorem B1927127 : Blo 1283960 1927127 := bstep (se 1 (by rfl) ⟨1445345, by rfl⟩ : syracuseStep 1927127 = 2890691) B2890691
theorem B1927193 : Blo 1283960 1927193 := bstep (se 2 (by rfl) ⟨722697, by rfl⟩ : syracuseStep 1927193 = 1445395) B1445395
theorem B1927307 : Blo 1283960 1927307 := bstep (se 1 (by rfl) ⟨1445480, by rfl⟩ : syracuseStep 1927307 = 2890961) B2890961
theorem B4876433 : Blo 1283960 4876433 := bstep (se 2 (by rfl) ⟨1828662, by rfl⟩ : syracuseStep 4876433 = 3657325) B3657325
theorem B4335767 : Blo 1283960 4335767 := bstep (se 1 (by rfl) ⟨3251825, by rfl⟩ : syracuseStep 4335767 = 6503651) B6503651
theorem B1927319 : Blo 1283960 1927319 := bstep (se 1 (by rfl) ⟨1445489, by rfl⟩ : syracuseStep 1927319 = 2890979) B2890979
theorem B16476311 : Blo 1283960 16476311 := bstep (se 1 (by rfl) ⟨12357233, by rfl⟩ : syracuseStep 16476311 = 24714467) B24714467
theorem B1927385 : Blo 1283960 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B3254489 : Blo 1283960 3254489 := bstep (se 2 (by rfl) ⟨1220433, by rfl⟩ : syracuseStep 3254489 = 2440867) B2440867
theorem B1927499 : Blo 1283960 1927499 := bstep (se 1 (by rfl) ⟨1445624, by rfl⟩ : syracuseStep 1927499 = 2891249) B2891249
theorem B7924043 : Blo 1283960 7924043 := bstep (se 1 (by rfl) ⟨5943032, by rfl⟩ : syracuseStep 7924043 = 11886065) B11886065
theorem B2197847 : Blo 1283960 2197847 := bstep (se 1 (by rfl) ⟨1648385, by rfl⟩ : syracuseStep 2197847 = 3296771) B3296771
theorem B1927511 : Blo 1283960 1927511 := bstep (se 1 (by rfl) ⟨1445633, by rfl⟩ : syracuseStep 1927511 = 2891267) B2891267
theorem B37038485 : Blo 1283960 37038485 := bstep (se 6 (by rfl) ⟨868089, by rfl⟩ : syracuseStep 37038485 = 1736179) B1736179
theorem B1927577 : Blo 1283960 1927577 := bstep (se 2 (by rfl) ⟨722841, by rfl⟩ : syracuseStep 1927577 = 1445683) B1445683
theorem B5491147 : Blo 1283960 5491147 := bstep (se 1 (by rfl) ⟨4118360, by rfl⟩ : syracuseStep 5491147 = 8236721) B8236721
theorem B1927691 : Blo 1283960 1927691 := bstep (se 1 (by rfl) ⟨1445768, by rfl⟩ : syracuseStep 1927691 = 2891537) B2891537
theorem B1927703 : Blo 1283960 1927703 := bstep (se 1 (by rfl) ⟨1445777, by rfl⟩ : syracuseStep 1927703 = 2891555) B2891555
theorem B6507053 : Blo 1283960 6507053 := bstep (se 3 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 6507053 = 2440145) B2440145
theorem B1927769 : Blo 1283960 1927769 := bstep (se 2 (by rfl) ⟨722913, by rfl⟩ : syracuseStep 1927769 = 1445827) B1445827
theorem B1444459 : Blo 1283960 1444459 := bstep (se 1 (by rfl) ⟨1083344, by rfl⟩ : syracuseStep 1444459 = 2166689) B2166689
theorem B4336307 : Blo 1283960 4336307 := bstep (se 1 (by rfl) ⟨3252230, by rfl⟩ : syracuseStep 4336307 = 6504461) B6504461
theorem B1927883 : Blo 1283960 1927883 := bstep (se 1 (by rfl) ⟨1445912, by rfl⟩ : syracuseStep 1927883 = 2891825) B2891825
theorem B1444567 : Blo 1283960 1444567 := bstep (se 1 (by rfl) ⟨1083425, by rfl⟩ : syracuseStep 1444567 = 2166851) B2166851
theorem B1927895 : Blo 1283960 1927895 := bstep (se 1 (by rfl) ⟨1445921, by rfl⟩ : syracuseStep 1927895 = 2891843) B2891843
theorem B5491421 : Blo 1283960 5491421 := bstep (se 3 (by rfl) ⟨1029641, by rfl⟩ : syracuseStep 5491421 = 2059283) B2059283
theorem B1927961 : Blo 1283960 1927961 := bstep (se 2 (by rfl) ⟨722985, by rfl⟩ : syracuseStep 1927961 = 1445971) B1445971
theorem B4877131 : Blo 1283960 4877131 := bstep (se 1 (by rfl) ⟨3657848, by rfl⟩ : syracuseStep 4877131 = 7315697) B7315697
theorem B3910493 : Blo 1283960 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B8235877 : Blo 1283960 8235877 := bstep (se 4 (by rfl) ⟨772113, by rfl⟩ : syracuseStep 8235877 = 1544227) B1544227
theorem B1444747 : Blo 1283960 1444747 := bstep (se 1 (by rfl) ⟨1083560, by rfl⟩ : syracuseStep 1444747 = 2167121) B2167121
theorem B1928075 : Blo 1283960 1928075 := bstep (se 1 (by rfl) ⟨1446056, by rfl⟩ : syracuseStep 1928075 = 2892113) B2892113
theorem B1928087 : Blo 1283960 1928087 := bstep (se 1 (by rfl) ⟨1446065, by rfl⟩ : syracuseStep 1928087 = 2892131) B2892131
theorem B1829785 : Blo 1283960 1829785 := bstep (se 2 (by rfl) ⟨686169, by rfl⟩ : syracuseStep 1829785 = 1372339) B1372339
theorem B4336577 : Blo 1283960 4336577 := bstep (se 2 (by rfl) ⟨1626216, by rfl⟩ : syracuseStep 4336577 = 3252433) B3252433
theorem B14633945 : Blo 1283960 14633945 := bstep (se 2 (by rfl) ⟨5487729, by rfl⟩ : syracuseStep 14633945 = 10975459) B10975459
theorem B1928153 : Blo 1283960 1928153 := bstep (se 2 (by rfl) ⟨723057, by rfl⟩ : syracuseStep 1928153 = 1446115) B1446115
theorem B1444855 : Blo 1283960 1444855 := bstep (se 1 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 1444855 = 2167283) B2167283
theorem B3656755 : Blo 1283960 3656755 := bstep (se 1 (by rfl) ⟨2742566, by rfl⟩ : syracuseStep 3656755 = 5485133) B5485133
theorem B5491763 : Blo 1283960 5491763 := bstep (se 1 (by rfl) ⟨4118822, by rfl⟩ : syracuseStep 5491763 = 8237645) B8237645
theorem B1928267 : Blo 1283960 1928267 := bstep (se 1 (by rfl) ⟨1446200, by rfl⟩ : syracuseStep 1928267 = 2892401) B2892401
theorem B1928279 : Blo 1283960 1928279 := bstep (se 1 (by rfl) ⟨1446209, by rfl⟩ : syracuseStep 1928279 = 2892419) B2892419
theorem B4877405 : Blo 1283960 4877405 := bstep (se 3 (by rfl) ⟨914513, by rfl⟩ : syracuseStep 4877405 = 1829027) B1829027
theorem B17820823 : Blo 1283960 17820823 := bstep (se 1 (by rfl) ⟨13365617, by rfl⟩ : syracuseStep 17820823 = 26731235) B26731235
theorem B1928345 : Blo 1283960 1928345 := bstep (se 2 (by rfl) ⟨723129, by rfl⟩ : syracuseStep 1928345 = 1446259) B1446259
theorem B1445035 : Blo 1283960 1445035 := bstep (se 1 (by rfl) ⟨1083776, by rfl⟩ : syracuseStep 1445035 = 2167553) B2167553
theorem B10972421 : Blo 1283960 10972421 := bstep (se 4 (by rfl) ⟨1028664, by rfl⟩ : syracuseStep 10972421 = 2057329) B2057329
theorem B1928459 : Blo 1283960 1928459 := bstep (se 1 (by rfl) ⟨1446344, by rfl⟩ : syracuseStep 1928459 = 2892689) B2892689
theorem B3656983 : Blo 1283960 3656983 := bstep (se 1 (by rfl) ⟨2742737, by rfl⟩ : syracuseStep 3656983 = 5485475) B5485475
theorem B1445143 : Blo 1283960 1445143 := bstep (se 1 (by rfl) ⟨1083857, by rfl⟩ : syracuseStep 1445143 = 2167715) B2167715
theorem B1928471 : Blo 1283960 1928471 := bstep (se 1 (by rfl) ⟨1446353, by rfl⟩ : syracuseStep 1928471 = 2892707) B2892707
theorem B8236363 : Blo 1283960 8236363 := bstep (se 1 (by rfl) ⟨6177272, by rfl⟩ : syracuseStep 8236363 = 12354545) B12354545
theorem B1928537 : Blo 1283960 1928537 := bstep (se 2 (by rfl) ⟨723201, by rfl⟩ : syracuseStep 1928537 = 1446403) B1446403
theorem B2198935 : Blo 1283960 2198935 := bstep (se 1 (by rfl) ⟨1649201, by rfl⟩ : syracuseStep 2198935 = 3298403) B3298403
theorem B1445323 : Blo 1283960 1445323 := bstep (se 1 (by rfl) ⟨1083992, by rfl⟩ : syracuseStep 1445323 = 2167985) B2167985
theorem B1928651 : Blo 1283960 1928651 := bstep (se 1 (by rfl) ⟨1446488, by rfl⟩ : syracuseStep 1928651 = 2892977) B2892977
theorem B1928663 : Blo 1283960 1928663 := bstep (se 1 (by rfl) ⟨1446497, by rfl⟩ : syracuseStep 1928663 = 2892995) B2892995
theorem B4337117 : Blo 1283960 4337117 := bstep (se 3 (by rfl) ⟨813209, by rfl⟩ : syracuseStep 4337117 = 1626419) B1626419
theorem B1371659 : Blo 1283960 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B1543703 : Blo 1283960 1543703 := bstep (se 1 (by rfl) ⟨1157777, by rfl⟩ : syracuseStep 1543703 = 2315555) B2315555
theorem B1928729 : Blo 1283960 1928729 := bstep (se 2 (by rfl) ⟨723273, by rfl⟩ : syracuseStep 1928729 = 1446547) B1446547
theorem B1445431 : Blo 1283960 1445431 := bstep (se 1 (by rfl) ⟨1084073, by rfl⟩ : syracuseStep 1445431 = 2168147) B2168147
theorem B1928843 : Blo 1283960 1928843 := bstep (se 1 (by rfl) ⟨1446632, by rfl⟩ : syracuseStep 1928843 = 2893265) B2893265
theorem B1928855 : Blo 1283960 1928855 := bstep (se 1 (by rfl) ⟨1446641, by rfl⟩ : syracuseStep 1928855 = 2893283) B2893283
theorem B23432885 : Blo 1283960 23432885 := bstep (se 5 (by rfl) ⟨1098416, by rfl⟩ : syracuseStep 23432885 = 2196833) B2196833
theorem B2780887 : Blo 1283960 2780887 := bstep (se 1 (by rfl) ⟨2085665, by rfl⟩ : syracuseStep 2780887 = 4171331) B4171331
theorem B1928921 : Blo 1283960 1928921 := bstep (se 2 (by rfl) ⟨723345, by rfl⟩ : syracuseStep 1928921 = 1446691) B1446691
theorem B1445611 : Blo 1283960 1445611 := bstep (se 1 (by rfl) ⟨1084208, by rfl⟩ : syracuseStep 1445611 = 2168417) B2168417
theorem B4878103 : Blo 1283960 4878103 := bstep (se 1 (by rfl) ⟨3658577, by rfl⟩ : syracuseStep 4878103 = 7317155) B7317155
theorem B1445719 : Blo 1283960 1445719 := bstep (se 1 (by rfl) ⟨1084289, by rfl⟩ : syracuseStep 1445719 = 2168579) B2168579
theorem B2314099 : Blo 1283960 2314099 := bstep (se 1 (by rfl) ⟨1735574, by rfl⟩ : syracuseStep 2314099 = 3471149) B3471149
theorem B27774899 : Blo 1283960 27774899 := bstep (se 1 (by rfl) ⟨20831174, by rfl⟩ : syracuseStep 27774899 = 41662349) B41662349
theorem B2166743 : Blo 1283960 2166743 := bstep (se 1 (by rfl) ⟨1625057, by rfl⟩ : syracuseStep 2166743 = 3250115) B3250115
theorem B1445899 : Blo 1283960 1445899 := bstep (se 1 (by rfl) ⟨1084424, by rfl⟩ : syracuseStep 1445899 = 2168849) B2168849
theorem B2166871 : Blo 1283960 2166871 := bstep (se 1 (by rfl) ⟨1625153, by rfl⟩ : syracuseStep 2166871 = 3250307) B3250307
theorem B1446007 : Blo 1283960 1446007 := bstep (se 1 (by rfl) ⟨1084505, by rfl⟩ : syracuseStep 1446007 = 2169011) B2169011
theorem B1446187 : Blo 1283960 1446187 := bstep (se 1 (by rfl) ⟨1084640, by rfl⟩ : syracuseStep 1446187 = 2169281) B2169281
theorem B11121047 : Blo 1283960 11121047 := bstep (se 1 (by rfl) ⟨8340785, by rfl⟩ : syracuseStep 11121047 = 16681571) B16681571
theorem B1446295 : Blo 1283960 1446295 := bstep (se 1 (by rfl) ⟨1084721, by rfl⟩ : syracuseStep 1446295 = 2169443) B2169443
theorem B1626571 : Blo 1283960 1626571 := bstep (se 1 (by rfl) ⟨1219928, by rfl⟩ : syracuseStep 1626571 = 2439857) B2439857
theorem B19780109 : Blo 1283960 19780109 := bstep (se 3 (by rfl) ⟨3708770, by rfl⟩ : syracuseStep 19780109 = 7417541) B7417541
theorem B4878893 : Blo 1283960 4878893 := bstep (se 3 (by rfl) ⟨914792, by rfl⟩ : syracuseStep 4878893 = 1829585) B1829585
theorem B4338251 : Blo 1283960 4338251 := bstep (se 1 (by rfl) ⟨3253688, by rfl⟩ : syracuseStep 4338251 = 6507377) B6507377
theorem B1446475 : Blo 1283960 1446475 := bstep (se 1 (by rfl) ⟨1084856, by rfl⟩ : syracuseStep 1446475 = 2169713) B2169713
theorem B6943333 : Blo 1283960 6943333 := bstep (se 4 (by rfl) ⟨650937, by rfl⟩ : syracuseStep 6943333 = 1301875) B1301875
theorem B20845187 : Blo 1283960 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B1446583 : Blo 1283960 1446583 := bstep (se 1 (by rfl) ⟨1084937, by rfl⟩ : syracuseStep 1446583 = 2169875) B2169875
theorem B3085003 : Blo 1283960 3085003 := bstep (se 1 (by rfl) ⟨2313752, by rfl⟩ : syracuseStep 3085003 = 4627505) B4627505
theorem B2167499 : Blo 1283960 2167499 := bstep (se 1 (by rfl) ⟨1625624, by rfl⟩ : syracuseStep 2167499 = 3251249) B3251249
theorem B2437913 : Blo 1283960 2437913 := bstep (se 2 (by rfl) ⟨914217, by rfl⟩ : syracuseStep 2437913 = 1828435) B1828435
theorem B2167627 : Blo 1283960 2167627 := bstep (se 1 (by rfl) ⟨1625720, by rfl⟩ : syracuseStep 2167627 = 3251441) B3251441
theorem B4338521 : Blo 1283960 4338521 := bstep (se 2 (by rfl) ⟨1626945, by rfl⟩ : syracuseStep 4338521 = 3253891) B3253891
theorem B3085235 : Blo 1283960 3085235 := bstep (se 1 (by rfl) ⟨2313926, by rfl⟩ : syracuseStep 3085235 = 4627853) B4627853
theorem B2167769 : Blo 1283960 2167769 := bstep (se 2 (by rfl) ⟨812913, by rfl⟩ : syracuseStep 2167769 = 1625827) B1625827
theorem B2167897 : Blo 1283960 2167897 := bstep (se 2 (by rfl) ⟨812961, by rfl⟩ : syracuseStep 2167897 = 1625923) B1625923
theorem B3658841 : Blo 1283960 3658841 := bstep (se 2 (by rfl) ⟨1372065, by rfl⟩ : syracuseStep 3658841 = 2744131) B2744131
theorem B2889035 : Blo 1283960 2889035 := bstep (se 1 (by rfl) ⟨2166776, by rfl⟩ : syracuseStep 2889035 = 4333553) B4333553
theorem B6501707 : Blo 1283960 6501707 := bstep (se 1 (by rfl) ⟨4876280, by rfl⟩ : syracuseStep 6501707 = 9752561) B9752561
theorem B2889089 : Blo 1283960 2889089 := bstep (se 2 (by rfl) ⟨1083408, by rfl⟩ : syracuseStep 2889089 = 2166817) B2166817
theorem B6174083 : Blo 1283960 6174083 := bstep (se 1 (by rfl) ⟨4630562, by rfl⟩ : syracuseStep 6174083 = 9261125) B9261125
theorem B1627543 : Blo 1283960 1627543 := bstep (se 1 (by rfl) ⟨1220657, by rfl⟩ : syracuseStep 1627543 = 2441315) B2441315
theorem B2315713 : Blo 1283960 2315713 := bstep (se 2 (by rfl) ⟨868392, by rfl⟩ : syracuseStep 2315713 = 1736785) B1736785
theorem B2438657 : Blo 1283960 2438657 := bstep (se 2 (by rfl) ⟨914496, by rfl⟩ : syracuseStep 2438657 = 1828993) B1828993
theorem B13186577 : Blo 1283960 13186577 := bstep (se 2 (by rfl) ⟨4944966, by rfl⟩ : syracuseStep 13186577 = 9889933) B9889933
theorem B4339223 : Blo 1283960 4339223 := bstep (se 1 (by rfl) ⟨3254417, by rfl⟩ : syracuseStep 4339223 = 6508835) B6508835
theorem B2889305 : Blo 1283960 2889305 := bstep (se 2 (by rfl) ⟨1083489, by rfl⟩ : syracuseStep 2889305 = 2166979) B2166979
theorem B89028209 : Blo 1283960 89028209 := bstep (se 2 (by rfl) ⟨33385578, by rfl⟩ : syracuseStep 89028209 = 66771157) B66771157
theorem B2168471 : Blo 1283960 2168471 := bstep (se 1 (by rfl) ⟨1626353, by rfl⟩ : syracuseStep 2168471 = 3252707) B3252707
theorem B2889395 : Blo 1283960 2889395 := bstep (se 1 (by rfl) ⟨2167046, by rfl⟩ : syracuseStep 2889395 = 4334093) B4334093
theorem B8787635 : Blo 1283960 8787635 := bstep (se 1 (by rfl) ⟨6590726, by rfl⟩ : syracuseStep 8787635 = 13181453) B13181453
theorem B2889431 : Blo 1283960 2889431 := bstep (se 1 (by rfl) ⟨2167073, by rfl⟩ : syracuseStep 2889431 = 4334147) B4334147
theorem B2438923 : Blo 1283960 2438923 := bstep (se 1 (by rfl) ⟨1829192, by rfl⟩ : syracuseStep 2438923 = 3658385) B3658385
theorem B8230673 : Blo 1283960 8230673 := bstep (se 2 (by rfl) ⟨3086502, by rfl⟩ : syracuseStep 8230673 = 6173005) B6173005
theorem B2168599 : Blo 1283960 2168599 := bstep (se 1 (by rfl) ⟨1626449, by rfl⟩ : syracuseStep 2168599 = 3252899) B3252899
theorem B16684865 : Blo 1283960 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B1283979 : Blo 1283960 1283979 := bstep (se 1 (by rfl) ⟨962984, by rfl⟩ : syracuseStep 1283979 = 1925969) B1925969
theorem B2889611 : Blo 1283960 2889611 := bstep (se 1 (by rfl) ⟨2167208, by rfl⟩ : syracuseStep 2889611 = 4334417) B4334417
theorem B1283991 : Blo 1283960 1283991 := bstep (se 1 (by rfl) ⟨962993, by rfl⟩ : syracuseStep 1283991 = 1925987) B1925987
theorem B3659671 : Blo 1283960 3659671 := bstep (se 1 (by rfl) ⟨2744753, by rfl⟩ : syracuseStep 3659671 = 5489507) B5489507
theorem B1284011 : Blo 1283960 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B1284023 : Blo 1283960 1284023 := bstep (se 1 (by rfl) ⟨963017, by rfl⟩ : syracuseStep 1284023 = 1926035) B1926035
theorem B2889665 : Blo 1283960 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B4880321 : Blo 1283960 4880321 := bstep (se 2 (by rfl) ⟨1830120, by rfl⟩ : syracuseStep 4880321 = 3660241) B3660241
theorem B1284043 : Blo 1283960 1284043 := bstep (se 1 (by rfl) ⟨963032, by rfl⟩ : syracuseStep 1284043 = 1926065) B1926065
theorem B1284055 : Blo 1283960 1284055 := bstep (se 1 (by rfl) ⟨963041, by rfl⟩ : syracuseStep 1284055 = 1926083) B1926083
theorem B1284075 : Blo 1283960 1284075 := bstep (se 1 (by rfl) ⟨963056, by rfl⟩ : syracuseStep 1284075 = 1926113) B1926113
theorem B1284087 : Blo 1283960 1284087 := bstep (se 1 (by rfl) ⟨963065, by rfl⟩ : syracuseStep 1284087 = 1926131) B1926131
theorem B1284107 : Blo 1283960 1284107 := bstep (se 1 (by rfl) ⟨963080, by rfl⟩ : syracuseStep 1284107 = 1926161) B1926161
theorem B2783243 : Blo 1283960 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B20051981 : Blo 1283960 20051981 := bstep (se 3 (by rfl) ⟨3759746, by rfl⟩ : syracuseStep 20051981 = 7519493) B7519493
theorem B20846605 : Blo 1283960 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B1284119 : Blo 1283960 1284119 := bstep (se 1 (by rfl) ⟨963089, by rfl⟩ : syracuseStep 1284119 = 1926179) B1926179
theorem B1284139 : Blo 1283960 1284139 := bstep (se 1 (by rfl) ⟨963104, by rfl⟩ : syracuseStep 1284139 = 1926209) B1926209
theorem B4339763 : Blo 1283960 4339763 := bstep (se 1 (by rfl) ⟨3254822, by rfl⟩ : syracuseStep 4339763 = 6509645) B6509645
theorem B1284151 : Blo 1283960 1284151 := bstep (se 1 (by rfl) ⟨963113, by rfl⟩ : syracuseStep 1284151 = 1926227) B1926227
theorem B1284171 : Blo 1283960 1284171 := bstep (se 1 (by rfl) ⟨963128, by rfl⟩ : syracuseStep 1284171 = 1926257) B1926257
theorem B1284183 : Blo 1283960 1284183 := bstep (se 1 (by rfl) ⟨963137, by rfl⟩ : syracuseStep 1284183 = 1926275) B1926275
theorem B2316377 : Blo 1283960 2316377 := bstep (se 2 (by rfl) ⟨868641, by rfl⟩ : syracuseStep 2316377 = 1737283) B1737283
theorem B4118617 : Blo 1283960 4118617 := bstep (se 2 (by rfl) ⟨1544481, by rfl⟩ : syracuseStep 4118617 = 3088963) B3088963
theorem B1284203 : Blo 1283960 1284203 := bstep (se 1 (by rfl) ⟨963152, by rfl⟩ : syracuseStep 1284203 = 1926305) B1926305
theorem B1284215 : Blo 1283960 1284215 := bstep (se 1 (by rfl) ⟨963161, by rfl⟩ : syracuseStep 1284215 = 1926323) B1926323
theorem B1284235 : Blo 1283960 1284235 := bstep (se 1 (by rfl) ⟨963176, by rfl⟩ : syracuseStep 1284235 = 1926353) B1926353
theorem B3250327 : Blo 1283960 3250327 := bstep (se 1 (by rfl) ⟨2437745, by rfl⟩ : syracuseStep 3250327 = 4875491) B4875491
theorem B1284247 : Blo 1283960 1284247 := bstep (se 1 (by rfl) ⟨963185, by rfl⟩ : syracuseStep 1284247 = 1926371) B1926371
theorem B2889881 : Blo 1283960 2889881 := bstep (se 2 (by rfl) ⟨1083705, by rfl⟩ : syracuseStep 2889881 = 2167411) B2167411
theorem B15628439 : Blo 1283960 15628439 := bstep (se 1 (by rfl) ⟨11721329, by rfl⟩ : syracuseStep 15628439 = 23442659) B23442659
theorem B23443607 : Blo 1283960 23443607 := bstep (se 1 (by rfl) ⟨17582705, by rfl⟩ : syracuseStep 23443607 = 35165411) B35165411
theorem B1284267 : Blo 1283960 1284267 := bstep (se 1 (by rfl) ⟨963200, by rfl⟩ : syracuseStep 1284267 = 1926401) B1926401
theorem B1284279 : Blo 1283960 1284279 := bstep (se 1 (by rfl) ⟨963209, by rfl⟩ : syracuseStep 1284279 = 1926419) B1926419
theorem B1284299 : Blo 1283960 1284299 := bstep (se 1 (by rfl) ⟨963224, by rfl⟩ : syracuseStep 1284299 = 1926449) B1926449
theorem B2439371 : Blo 1283960 2439371 := bstep (se 1 (by rfl) ⟨1829528, by rfl⟩ : syracuseStep 2439371 = 3659057) B3659057
theorem B4946123 : Blo 1283960 4946123 := bstep (se 1 (by rfl) ⟨3709592, by rfl⟩ : syracuseStep 4946123 = 7419185) B7419185
theorem B1284311 : Blo 1283960 1284311 := bstep (se 1 (by rfl) ⟨963233, by rfl⟩ : syracuseStep 1284311 = 1926467) B1926467
theorem B2603225 : Blo 1283960 2603225 := bstep (se 2 (by rfl) ⟨976209, by rfl⟩ : syracuseStep 2603225 = 1952419) B1952419
theorem B1284331 : Blo 1283960 1284331 := bstep (se 1 (by rfl) ⟨963248, by rfl⟩ : syracuseStep 1284331 = 1926497) B1926497
theorem B2889971 : Blo 1283960 2889971 := bstep (se 1 (by rfl) ⟨2167478, by rfl⟩ : syracuseStep 2889971 = 4334957) B4334957
theorem B1284343 : Blo 1283960 1284343 := bstep (se 1 (by rfl) ⟨963257, by rfl⟩ : syracuseStep 1284343 = 1926515) B1926515
theorem B1284363 : Blo 1283960 1284363 := bstep (se 1 (by rfl) ⟨963272, by rfl⟩ : syracuseStep 1284363 = 1926545) B1926545
theorem B5863697 : Blo 1283960 5863697 := bstep (se 2 (by rfl) ⟨2198886, by rfl⟩ : syracuseStep 5863697 = 4397773) B4397773
theorem B1284375 : Blo 1283960 1284375 := bstep (se 1 (by rfl) ⟨963281, by rfl⟩ : syracuseStep 1284375 = 1926563) B1926563
theorem B2890007 : Blo 1283960 2890007 := bstep (se 1 (by rfl) ⟨2167505, by rfl⟩ : syracuseStep 2890007 = 4335011) B4335011
theorem B1284395 : Blo 1283960 1284395 := bstep (se 1 (by rfl) ⟨963296, by rfl⟩ : syracuseStep 1284395 = 1926593) B1926593
theorem B1284407 : Blo 1283960 1284407 := bstep (se 1 (by rfl) ⟨963305, by rfl⟩ : syracuseStep 1284407 = 1926611) B1926611
theorem B3086657 : Blo 1283960 3086657 := bstep (se 2 (by rfl) ⟨1157496, by rfl⟩ : syracuseStep 3086657 = 2314993) B2314993
theorem B4340033 : Blo 1283960 4340033 := bstep (se 2 (by rfl) ⟨1627512, by rfl⟩ : syracuseStep 4340033 = 3255025) B3255025
theorem B1284427 : Blo 1283960 1284427 := bstep (se 1 (by rfl) ⟨963320, by rfl⟩ : syracuseStep 1284427 = 1926641) B1926641
theorem B1284439 : Blo 1283960 1284439 := bstep (se 1 (by rfl) ⟨963329, by rfl⟩ : syracuseStep 1284439 = 1926659) B1926659
theorem B5208409 : Blo 1283960 5208409 := bstep (se 2 (by rfl) ⟨1953153, by rfl⟩ : syracuseStep 5208409 = 3906307) B3906307
theorem B1284459 : Blo 1283960 1284459 := bstep (se 1 (by rfl) ⟨963344, by rfl⟩ : syracuseStep 1284459 = 1926689) B1926689
theorem B1284471 : Blo 1283960 1284471 := bstep (se 1 (by rfl) ⟨963353, by rfl⟩ : syracuseStep 1284471 = 1926707) B1926707
theorem B2439553 : Blo 1283960 2439553 := bstep (se 2 (by rfl) ⟨914832, by rfl⟩ : syracuseStep 2439553 = 1829665) B1829665
theorem B1284491 : Blo 1283960 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B2169227 : Blo 1283960 2169227 := bstep (se 1 (by rfl) ⟨1626920, by rfl⟩ : syracuseStep 2169227 = 3253841) B3253841
theorem B1284503 : Blo 1283960 1284503 := bstep (se 1 (by rfl) ⟨963377, by rfl⟩ : syracuseStep 1284503 = 1926755) B1926755
theorem B1284523 : Blo 1283960 1284523 := bstep (se 1 (by rfl) ⟨963392, by rfl⟩ : syracuseStep 1284523 = 1926785) B1926785
theorem B2603443 : Blo 1283960 2603443 := bstep (se 1 (by rfl) ⟨1952582, by rfl⟩ : syracuseStep 2603443 = 3905165) B3905165
theorem B1284535 : Blo 1283960 1284535 := bstep (se 1 (by rfl) ⟨963401, by rfl⟩ : syracuseStep 1284535 = 1926803) B1926803
theorem B2890187 : Blo 1283960 2890187 := bstep (se 1 (by rfl) ⟨2167640, by rfl⟩ : syracuseStep 2890187 = 4335281) B4335281
theorem B1284555 : Blo 1283960 1284555 := bstep (se 1 (by rfl) ⟨963416, by rfl⟩ : syracuseStep 1284555 = 1926833) B1926833
theorem B1284567 : Blo 1283960 1284567 := bstep (se 1 (by rfl) ⟨963425, by rfl⟩ : syracuseStep 1284567 = 1926851) B1926851
theorem B1284587 : Blo 1283960 1284587 := bstep (se 1 (by rfl) ⟨963440, by rfl⟩ : syracuseStep 1284587 = 1926881) B1926881
theorem B1284599 : Blo 1283960 1284599 := bstep (se 1 (by rfl) ⟨963449, by rfl⟩ : syracuseStep 1284599 = 1926899) B1926899
theorem B2890241 : Blo 1283960 2890241 := bstep (se 2 (by rfl) ⟨1083840, by rfl⟩ : syracuseStep 2890241 = 2167681) B2167681
theorem B1284619 : Blo 1283960 1284619 := bstep (se 1 (by rfl) ⟨963464, by rfl⟩ : syracuseStep 1284619 = 1926929) B1926929
theorem B2169355 : Blo 1283960 2169355 := bstep (se 1 (by rfl) ⟨1627016, by rfl⟩ : syracuseStep 2169355 = 3254033) B3254033
theorem B1284631 : Blo 1283960 1284631 := bstep (se 1 (by rfl) ⟨963473, by rfl⟩ : syracuseStep 1284631 = 1926947) B1926947
theorem B1284651 : Blo 1283960 1284651 := bstep (se 1 (by rfl) ⟨963488, by rfl⟩ : syracuseStep 1284651 = 1926977) B1926977
theorem B1284663 : Blo 1283960 1284663 := bstep (se 1 (by rfl) ⟨963497, by rfl⟩ : syracuseStep 1284663 = 1926995) B1926995
theorem B3250763 : Blo 1283960 3250763 := bstep (se 1 (by rfl) ⟨2438072, by rfl⟩ : syracuseStep 3250763 = 4876145) B4876145
theorem B1284683 : Blo 1283960 1284683 := bstep (se 1 (by rfl) ⟨963512, by rfl⟩ : syracuseStep 1284683 = 1927025) B1927025
theorem B1284695 : Blo 1283960 1284695 := bstep (se 1 (by rfl) ⟨963521, by rfl⟩ : syracuseStep 1284695 = 1927043) B1927043
theorem B1284715 : Blo 1283960 1284715 := bstep (se 1 (by rfl) ⟨963536, by rfl⟩ : syracuseStep 1284715 = 1927073) B1927073
theorem B1284727 : Blo 1283960 1284727 := bstep (se 1 (by rfl) ⟨963545, by rfl⟩ : syracuseStep 1284727 = 1927091) B1927091
theorem B2931329 : Blo 1283960 2931329 := bstep (se 2 (by rfl) ⟨1099248, by rfl⟩ : syracuseStep 2931329 = 2198497) B2198497
theorem B1284747 : Blo 1283960 1284747 := bstep (se 1 (by rfl) ⟨963560, by rfl⟩ : syracuseStep 1284747 = 1927121) B1927121
theorem B1284759 : Blo 1283960 1284759 := bstep (se 1 (by rfl) ⟨963569, by rfl⟩ : syracuseStep 1284759 = 1927139) B1927139
theorem B2169497 : Blo 1283960 2169497 := bstep (se 2 (by rfl) ⟨813561, by rfl⟩ : syracuseStep 2169497 = 1627123) B1627123
theorem B1284779 : Blo 1283960 1284779 := bstep (se 1 (by rfl) ⟨963584, by rfl⟩ : syracuseStep 1284779 = 1927169) B1927169
theorem B1284791 : Blo 1283960 1284791 := bstep (se 1 (by rfl) ⟨963593, by rfl⟩ : syracuseStep 1284791 = 1927187) B1927187
theorem B2742977 : Blo 1283960 2742977 := bstep (se 2 (by rfl) ⟨1028616, by rfl⟩ : syracuseStep 2742977 = 2057233) B2057233
theorem B1669835 : Blo 1283960 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B1284811 : Blo 1283960 1284811 := bstep (se 1 (by rfl) ⟨963608, by rfl⟩ : syracuseStep 1284811 = 1927217) B1927217
theorem B3660491 : Blo 1283960 3660491 := bstep (se 1 (by rfl) ⟨2745368, by rfl⟩ : syracuseStep 3660491 = 5490737) B5490737
theorem B1284823 : Blo 1283960 1284823 := bstep (se 1 (by rfl) ⟨963617, by rfl⟩ : syracuseStep 1284823 = 1927235) B1927235
theorem B2439895 : Blo 1283960 2439895 := bstep (se 1 (by rfl) ⟨1829921, by rfl⟩ : syracuseStep 2439895 = 3659843) B3659843
theorem B2890457 : Blo 1283960 2890457 := bstep (se 2 (by rfl) ⟨1083921, by rfl⟩ : syracuseStep 2890457 = 2167843) B2167843
theorem B1284843 : Blo 1283960 1284843 := bstep (se 1 (by rfl) ⟨963632, by rfl⟩ : syracuseStep 1284843 = 1927265) B1927265
theorem B1284855 : Blo 1283960 1284855 := bstep (se 1 (by rfl) ⟨963641, by rfl⟩ : syracuseStep 1284855 = 1927283) B1927283
theorem B1284875 : Blo 1283960 1284875 := bstep (se 1 (by rfl) ⟨963656, by rfl⟩ : syracuseStep 1284875 = 1927313) B1927313
theorem B1284887 : Blo 1283960 1284887 := bstep (se 1 (by rfl) ⟨963665, by rfl⟩ : syracuseStep 1284887 = 1927331) B1927331
theorem B2169625 : Blo 1283960 2169625 := bstep (se 2 (by rfl) ⟨813609, by rfl⟩ : syracuseStep 2169625 = 1627219) B1627219
theorem B1284907 : Blo 1283960 1284907 := bstep (se 1 (by rfl) ⟨963680, by rfl⟩ : syracuseStep 1284907 = 1927361) B1927361
theorem B2890547 : Blo 1283960 2890547 := bstep (se 1 (by rfl) ⟨2167910, by rfl⟩ : syracuseStep 2890547 = 4335821) B4335821
theorem B1284919 : Blo 1283960 1284919 := bstep (se 1 (by rfl) ⟨963689, by rfl⟩ : syracuseStep 1284919 = 1927379) B1927379
theorem B1284939 : Blo 1283960 1284939 := bstep (se 1 (by rfl) ⟨963704, by rfl⟩ : syracuseStep 1284939 = 1927409) B1927409
theorem B2890583 : Blo 1283960 2890583 := bstep (se 1 (by rfl) ⟨2167937, by rfl⟩ : syracuseStep 2890583 = 4335875) B4335875
theorem B1284951 : Blo 1283960 1284951 := bstep (se 1 (by rfl) ⟨963713, by rfl⟩ : syracuseStep 1284951 = 1927427) B1927427
theorem B1284971 : Blo 1283960 1284971 := bstep (se 1 (by rfl) ⟨963728, by rfl⟩ : syracuseStep 1284971 = 1927457) B1927457
theorem B1284983 : Blo 1283960 1284983 := bstep (se 1 (by rfl) ⟨963737, by rfl⟩ : syracuseStep 1284983 = 1927475) B1927475
theorem B1285003 : Blo 1283960 1285003 := bstep (se 1 (by rfl) ⟨963752, by rfl⟩ : syracuseStep 1285003 = 1927505) B1927505
theorem B1285015 : Blo 1283960 1285015 := bstep (se 1 (by rfl) ⟨963761, by rfl⟩ : syracuseStep 1285015 = 1927523) B1927523
theorem B2317207 : Blo 1283960 2317207 := bstep (se 1 (by rfl) ⟨1737905, by rfl⟩ : syracuseStep 2317207 = 3475811) B3475811
theorem B1285035 : Blo 1283960 1285035 := bstep (se 1 (by rfl) ⟨963776, by rfl⟩ : syracuseStep 1285035 = 1927553) B1927553
theorem B2440115 : Blo 1283960 2440115 := bstep (se 1 (by rfl) ⟨1830086, by rfl⟩ : syracuseStep 2440115 = 3660173) B3660173
theorem B1285047 : Blo 1283960 1285047 := bstep (se 1 (by rfl) ⟨963785, by rfl⟩ : syracuseStep 1285047 = 1927571) B1927571
theorem B3251137 : Blo 1283960 3251137 := bstep (se 2 (by rfl) ⟨1219176, by rfl⟩ : syracuseStep 3251137 = 2438353) B2438353
theorem B1285067 : Blo 1283960 1285067 := bstep (se 1 (by rfl) ⟨963800, by rfl⟩ : syracuseStep 1285067 = 1927601) B1927601
theorem B1285079 : Blo 1283960 1285079 := bstep (se 1 (by rfl) ⟨963809, by rfl⟩ : syracuseStep 1285079 = 1927619) B1927619
theorem B1285099 : Blo 1283960 1285099 := bstep (se 1 (by rfl) ⟨963824, by rfl⟩ : syracuseStep 1285099 = 1927649) B1927649
theorem B2472947 : Blo 1283960 2472947 := bstep (se 1 (by rfl) ⟨1854710, by rfl⟩ : syracuseStep 2472947 = 3709421) B3709421
theorem B1285111 : Blo 1283960 1285111 := bstep (se 1 (by rfl) ⟨963833, by rfl⟩ : syracuseStep 1285111 = 1927667) B1927667
theorem B2890763 : Blo 1283960 2890763 := bstep (se 1 (by rfl) ⟨2168072, by rfl⟩ : syracuseStep 2890763 = 4336145) B4336145
theorem B1285131 : Blo 1283960 1285131 := bstep (se 1 (by rfl) ⟨963848, by rfl⟩ : syracuseStep 1285131 = 1927697) B1927697
theorem B1301527 : Blo 1283960 1301527 := bstep (se 1 (by rfl) ⟨976145, by rfl⟩ : syracuseStep 1301527 = 1952291) B1952291
theorem B1285143 : Blo 1283960 1285143 := bstep (se 1 (by rfl) ⟨963857, by rfl⟩ : syracuseStep 1285143 = 1927715) B1927715
theorem B1285163 : Blo 1283960 1285163 := bstep (se 1 (by rfl) ⟨963872, by rfl⟩ : syracuseStep 1285163 = 1927745) B1927745
theorem B7322669 : Blo 1283960 7322669 := bstep (se 3 (by rfl) ⟨1373000, by rfl⟩ : syracuseStep 7322669 = 2746001) B2746001
theorem B1285175 : Blo 1283960 1285175 := bstep (se 1 (by rfl) ⟨963881, by rfl⟩ : syracuseStep 1285175 = 1927763) B1927763
theorem B6503489 : Blo 1283960 6503489 := bstep (se 2 (by rfl) ⟨2438808, by rfl⟩ : syracuseStep 6503489 = 4877617) B4877617
theorem B2890817 : Blo 1283960 2890817 := bstep (se 2 (by rfl) ⟨1084056, by rfl⟩ : syracuseStep 2890817 = 2168113) B2168113
theorem B1285195 : Blo 1283960 1285195 := bstep (se 1 (by rfl) ⟨963896, by rfl⟩ : syracuseStep 1285195 = 1927793) B1927793
theorem B1285207 : Blo 1283960 1285207 := bstep (se 1 (by rfl) ⟨963905, by rfl⟩ : syracuseStep 1285207 = 1927811) B1927811
theorem B1285227 : Blo 1283960 1285227 := bstep (se 1 (by rfl) ⟨963920, by rfl⟩ : syracuseStep 1285227 = 1927841) B1927841
theorem B1285239 : Blo 1283960 1285239 := bstep (se 1 (by rfl) ⟨963929, by rfl⟩ : syracuseStep 1285239 = 1927859) B1927859
theorem B1285259 : Blo 1283960 1285259 := bstep (se 1 (by rfl) ⟨963944, by rfl⟩ : syracuseStep 1285259 = 1927889) B1927889
theorem B1285271 : Blo 1283960 1285271 := bstep (se 1 (by rfl) ⟨963953, by rfl⟩ : syracuseStep 1285271 = 1927907) B1927907
theorem B2440343 : Blo 1283960 2440343 := bstep (se 1 (by rfl) ⟨1830257, by rfl⟩ : syracuseStep 2440343 = 3660515) B3660515
theorem B13376663 : Blo 1283960 13376663 := bstep (se 1 (by rfl) ⟨10032497, by rfl⟩ : syracuseStep 13376663 = 20064995) B20064995
theorem B1285291 : Blo 1283960 1285291 := bstep (se 1 (by rfl) ⟨963968, by rfl⟩ : syracuseStep 1285291 = 1927937) B1927937
theorem B33389749 : Blo 1283960 33389749 := bstep (se 5 (by rfl) ⟨1565144, by rfl⟩ : syracuseStep 33389749 = 3130289) B3130289
theorem B1285303 : Blo 1283960 1285303 := bstep (se 1 (by rfl) ⟨963977, by rfl⟩ : syracuseStep 1285303 = 1927955) B1927955
theorem B1285323 : Blo 1283960 1285323 := bstep (se 1 (by rfl) ⟨963992, by rfl⟩ : syracuseStep 1285323 = 1927985) B1927985
theorem B1285335 : Blo 1283960 1285335 := bstep (se 1 (by rfl) ⟨964001, by rfl⟩ : syracuseStep 1285335 = 1928003) B1928003
theorem B1285355 : Blo 1283960 1285355 := bstep (se 1 (by rfl) ⟨964016, by rfl⟩ : syracuseStep 1285355 = 1928033) B1928033
theorem B1285367 : Blo 1283960 1285367 := bstep (se 1 (by rfl) ⟨964025, by rfl⟩ : syracuseStep 1285367 = 1928051) B1928051
theorem B1285387 : Blo 1283960 1285387 := bstep (se 1 (by rfl) ⟨964040, by rfl⟩ : syracuseStep 1285387 = 1928081) B1928081
theorem B1285399 : Blo 1283960 1285399 := bstep (se 1 (by rfl) ⟨964049, by rfl⟩ : syracuseStep 1285399 = 1928099) B1928099
theorem B2891033 : Blo 1283960 2891033 := bstep (se 2 (by rfl) ⟨1084137, by rfl⟩ : syracuseStep 2891033 = 2168275) B2168275
theorem B1285419 : Blo 1283960 1285419 := bstep (se 1 (by rfl) ⟨964064, by rfl⟩ : syracuseStep 1285419 = 1928129) B1928129
theorem B18513197 : Blo 1283960 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B1285431 : Blo 1283960 1285431 := bstep (se 1 (by rfl) ⟨964073, by rfl⟩ : syracuseStep 1285431 = 1928147) B1928147
theorem B1285451 : Blo 1283960 1285451 := bstep (se 1 (by rfl) ⟨964088, by rfl⟩ : syracuseStep 1285451 = 1928177) B1928177
theorem B1285463 : Blo 1283960 1285463 := bstep (se 1 (by rfl) ⟨964097, by rfl⟩ : syracuseStep 1285463 = 1928195) B1928195
theorem B1506647 : Blo 1283960 1506647 := bstep (se 1 (by rfl) ⟨1129985, by rfl⟩ : syracuseStep 1506647 = 2259971) B2259971
theorem B1285483 : Blo 1283960 1285483 := bstep (se 1 (by rfl) ⟨964112, by rfl⟩ : syracuseStep 1285483 = 1928225) B1928225
theorem B2891123 : Blo 1283960 2891123 := bstep (se 1 (by rfl) ⟨2168342, by rfl⟩ : syracuseStep 2891123 = 4336685) B4336685
theorem B1285495 : Blo 1283960 1285495 := bstep (se 1 (by rfl) ⟨964121, by rfl⟩ : syracuseStep 1285495 = 1928243) B1928243
theorem B5488003 : Blo 1283960 5488003 := bstep (se 1 (by rfl) ⟨4116002, by rfl⟩ : syracuseStep 5488003 = 8232005) B8232005
theorem B1285515 : Blo 1283960 1285515 := bstep (se 1 (by rfl) ⟨964136, by rfl⟩ : syracuseStep 1285515 = 1928273) B1928273
theorem B4881809 : Blo 1283960 4881809 := bstep (se 2 (by rfl) ⟨1830678, by rfl⟩ : syracuseStep 4881809 = 3661357) B3661357
theorem B2891159 : Blo 1283960 2891159 := bstep (se 1 (by rfl) ⟨2168369, by rfl⟩ : syracuseStep 2891159 = 4336739) B4336739
theorem B1285527 : Blo 1283960 1285527 := bstep (se 1 (by rfl) ⟨964145, by rfl⟩ : syracuseStep 1285527 = 1928291) B1928291
theorem B2440601 : Blo 1283960 2440601 := bstep (se 2 (by rfl) ⟨915225, by rfl⟩ : syracuseStep 2440601 = 1830451) B1830451
theorem B1285547 : Blo 1283960 1285547 := bstep (se 1 (by rfl) ⟨964160, by rfl⟩ : syracuseStep 1285547 = 1928321) B1928321
theorem B10567091 : Blo 1283960 10567091 := bstep (se 1 (by rfl) ⟨7925318, by rfl⟩ : syracuseStep 10567091 = 15850637) B15850637
theorem B1285559 : Blo 1283960 1285559 := bstep (se 1 (by rfl) ⟨964169, by rfl⟩ : syracuseStep 1285559 = 1928339) B1928339
theorem B1285579 : Blo 1283960 1285579 := bstep (se 1 (by rfl) ⟨964184, by rfl⟩ : syracuseStep 1285579 = 1928369) B1928369
theorem B1285591 : Blo 1283960 1285591 := bstep (se 1 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 1285591 = 1928387) B1928387
theorem B1285611 : Blo 1283960 1285611 := bstep (se 1 (by rfl) ⟨964208, by rfl⟩ : syracuseStep 1285611 = 1928417) B1928417
theorem B1285623 : Blo 1283960 1285623 := bstep (se 1 (by rfl) ⟨964217, by rfl⟩ : syracuseStep 1285623 = 1928435) B1928435
theorem B1285643 : Blo 1283960 1285643 := bstep (se 1 (by rfl) ⟨964232, by rfl⟩ : syracuseStep 1285643 = 1928465) B1928465
theorem B3251735 : Blo 1283960 3251735 := bstep (se 1 (by rfl) ⟨2438801, by rfl⟩ : syracuseStep 3251735 = 4877603) B4877603
theorem B2743831 : Blo 1283960 2743831 := bstep (se 1 (by rfl) ⟨2057873, by rfl⟩ : syracuseStep 2743831 = 4115747) B4115747
theorem B1285655 : Blo 1283960 1285655 := bstep (se 1 (by rfl) ⟨964241, by rfl⟩ : syracuseStep 1285655 = 1928483) B1928483
theorem B1285675 : Blo 1283960 1285675 := bstep (se 1 (by rfl) ⟨964256, by rfl⟩ : syracuseStep 1285675 = 1928513) B1928513
theorem B1285687 : Blo 1283960 1285687 := bstep (se 1 (by rfl) ⟨964265, by rfl⟩ : syracuseStep 1285687 = 1928531) B1928531
theorem B2891339 : Blo 1283960 2891339 := bstep (se 1 (by rfl) ⟨2168504, by rfl⟩ : syracuseStep 2891339 = 4337009) B4337009
theorem B1285707 : Blo 1283960 1285707 := bstep (se 1 (by rfl) ⟨964280, by rfl⟩ : syracuseStep 1285707 = 1928561) B1928561
theorem B1285719 : Blo 1283960 1285719 := bstep (se 1 (by rfl) ⟨964289, by rfl⟩ : syracuseStep 1285719 = 1928579) B1928579
theorem B8347229 : Blo 1283960 8347229 := bstep (se 3 (by rfl) ⟨1565105, by rfl⟩ : syracuseStep 8347229 = 3130211) B3130211
theorem B1285739 : Blo 1283960 1285739 := bstep (se 1 (by rfl) ⟨964304, by rfl⟩ : syracuseStep 1285739 = 1928609) B1928609
theorem B1285751 : Blo 1283960 1285751 := bstep (se 1 (by rfl) ⟨964313, by rfl⟩ : syracuseStep 1285751 = 1928627) B1928627
theorem B2891393 : Blo 1283960 2891393 := bstep (se 2 (by rfl) ⟨1084272, by rfl⟩ : syracuseStep 2891393 = 2168545) B2168545
theorem B1285771 : Blo 1283960 1285771 := bstep (se 1 (by rfl) ⟨964328, by rfl⟩ : syracuseStep 1285771 = 1928657) B1928657
theorem B1285783 : Blo 1283960 1285783 := bstep (se 1 (by rfl) ⟨964337, by rfl⟩ : syracuseStep 1285783 = 1928675) B1928675
theorem B1285803 : Blo 1283960 1285803 := bstep (se 1 (by rfl) ⟨964352, by rfl⟩ : syracuseStep 1285803 = 1928705) B1928705
theorem B4628141 : Blo 1283960 4628141 := bstep (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) B1735553
theorem B1285815 : Blo 1283960 1285815 := bstep (se 1 (by rfl) ⟨964361, by rfl⟩ : syracuseStep 1285815 = 1928723) B1928723
theorem B1285835 : Blo 1283960 1285835 := bstep (se 1 (by rfl) ⟨964376, by rfl⟩ : syracuseStep 1285835 = 1928753) B1928753
theorem B10985165 : Blo 1283960 10985165 := bstep (se 3 (by rfl) ⟨2059718, by rfl⟩ : syracuseStep 10985165 = 4119437) B4119437
theorem B1736407 : Blo 1283960 1736407 := bstep (se 1 (by rfl) ⟨1302305, by rfl⟩ : syracuseStep 1736407 = 2604611) B2604611
theorem B1285847 : Blo 1283960 1285847 := bstep (se 1 (by rfl) ⟨964385, by rfl⟩ : syracuseStep 1285847 = 1928771) B1928771
theorem B1285867 : Blo 1283960 1285867 := bstep (se 1 (by rfl) ⟨964400, by rfl⟩ : syracuseStep 1285867 = 1928801) B1928801
theorem B1285879 : Blo 1283960 1285879 := bstep (se 1 (by rfl) ⟨964409, by rfl⟩ : syracuseStep 1285879 = 1928819) B1928819
theorem B1285899 : Blo 1283960 1285899 := bstep (se 1 (by rfl) ⟨964424, by rfl⟩ : syracuseStep 1285899 = 1928849) B1928849
theorem B1285911 : Blo 1283960 1285911 := bstep (se 1 (by rfl) ⟨964433, by rfl⟩ : syracuseStep 1285911 = 1928867) B1928867
theorem B1285931 : Blo 1283960 1285931 := bstep (se 1 (by rfl) ⟨964448, by rfl⟩ : syracuseStep 1285931 = 1928897) B1928897
theorem B3907379 : Blo 1283960 3907379 := bstep (se 1 (by rfl) ⟨2930534, by rfl⟩ : syracuseStep 3907379 = 5861069) B5861069
theorem B2441011 : Blo 1283960 2441011 := bstep (se 1 (by rfl) ⟨1830758, by rfl⟩ : syracuseStep 2441011 = 3661517) B3661517
theorem B1285943 : Blo 1283960 1285943 := bstep (se 1 (by rfl) ⟨964457, by rfl⟩ : syracuseStep 1285943 = 1928915) B1928915
theorem B2891609 : Blo 1283960 2891609 := bstep (se 2 (by rfl) ⟨1084353, by rfl⟩ : syracuseStep 2891609 = 2168707) B2168707
theorem B4882265 : Blo 1283960 4882265 := bstep (se 2 (by rfl) ⟨1830849, by rfl⟩ : syracuseStep 4882265 = 3661699) B3661699
theorem B15032243 : Blo 1283960 15032243 := bstep (se 1 (by rfl) ⟨11274182, by rfl⟩ : syracuseStep 15032243 = 22548365) B22548365
theorem B7315379 : Blo 1283960 7315379 := bstep (se 1 (by rfl) ⟨5486534, by rfl⟩ : syracuseStep 7315379 = 10973069) B10973069
theorem B2891699 : Blo 1283960 2891699 := bstep (se 1 (by rfl) ⟨2168774, by rfl⟩ : syracuseStep 2891699 = 4337549) B4337549
theorem B2891735 : Blo 1283960 2891735 := bstep (se 1 (by rfl) ⟨2168801, by rfl⟩ : syracuseStep 2891735 = 4337603) B4337603
theorem B27795473 : Blo 1283960 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B3522619 : Blo 1283960 3522619 := bstep (se 1 (by rfl) ⟨2641964, by rfl⟩ : syracuseStep 3522619 = 5283929) B5283929
theorem B14631029 : Blo 1283960 14631029 := bstep (se 5 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 14631029 = 1371659) B1371659
theorem B4333769 : Blo 1283960 4333769 := bstep (se 2 (by rfl) ⟨1625163, by rfl⟩ : syracuseStep 4333769 = 3250327) B3250327
theorem B6177005 : Blo 1283960 6177005 := bstep (se 3 (by rfl) ⟨1158188, by rfl⟩ : syracuseStep 6177005 = 2316377) B2316377
theorem B16466165 : Blo 1283960 16466165 := bstep (se 5 (by rfl) ⟨771851, by rfl⟩ : syracuseStep 16466165 = 1543703) B1543703
theorem B7414031 : Blo 1283960 7414031 := bstep (se 1 (by rfl) ⟨5560523, by rfl⟩ : syracuseStep 7414031 = 11121047) B11121047
theorem B3252595 : Blo 1283960 3252595 := bstep (se 1 (by rfl) ⟨2439446, by rfl⟩ : syracuseStep 3252595 = 4878893) B4878893
theorem B2892167 : Blo 1283960 2892167 := bstep (se 1 (by rfl) ⟨2169125, by rfl⟩ : syracuseStep 2892167 = 4338251) B4338251
theorem B23462291 : Blo 1283960 23462291 := bstep (se 1 (by rfl) ⟨17596718, by rfl⟩ : syracuseStep 23462291 = 35193437) B35193437
theorem B1737131 : Blo 1283960 1737131 := bstep (se 1 (by rfl) ⟨1302848, by rfl⟩ : syracuseStep 1737131 = 2605697) B2605697
theorem B3252737 : Blo 1283960 3252737 := bstep (se 2 (by rfl) ⟨1219776, by rfl⟩ : syracuseStep 3252737 = 2439553) B2439553
theorem B13189661 : Blo 1283960 13189661 := bstep (se 3 (by rfl) ⟨2473061, by rfl⟩ : syracuseStep 13189661 = 4946123) B4946123
theorem B2892347 : Blo 1283960 2892347 := bstep (se 1 (by rfl) ⟨2169260, by rfl⟩ : syracuseStep 2892347 = 4338521) B4338521
theorem B2056823 : Blo 1283960 2056823 := bstep (se 1 (by rfl) ⟨1542617, by rfl⟩ : syracuseStep 2056823 = 3085235) B3085235
theorem B2892473 : Blo 1283960 2892473 := bstep (se 2 (by rfl) ⟨1084677, by rfl⟩ : syracuseStep 2892473 = 2169355) B2169355
theorem B8913665 : Blo 1283960 8913665 := bstep (se 2 (by rfl) ⟨3342624, by rfl⟩ : syracuseStep 8913665 = 6685249) B6685249
theorem B9257777 : Blo 1283960 9257777 := bstep (se 2 (by rfl) ⟨3471666, by rfl⟩ : syracuseStep 9257777 = 6943333) B6943333
theorem B1925945 : Blo 1283960 1925945 := bstep (se 2 (by rfl) ⟨722229, by rfl⟩ : syracuseStep 1925945 = 1444459) B1444459
theorem B1926023 : Blo 1283960 1926023 := bstep (se 1 (by rfl) ⟨1444517, by rfl⟩ : syracuseStep 1926023 = 2889035) B2889035
theorem B4334471 : Blo 1283960 4334471 := bstep (se 1 (by rfl) ⟨3250853, by rfl⟩ : syracuseStep 4334471 = 6501707) B6501707
theorem B1737607 : Blo 1283960 1737607 := bstep (se 1 (by rfl) ⟨1303205, by rfl⟩ : syracuseStep 1737607 = 2606411) B2606411
theorem B13190039 : Blo 1283960 13190039 := bstep (se 1 (by rfl) ⟨9892529, by rfl⟩ : syracuseStep 13190039 = 19785059) B19785059
theorem B1926059 : Blo 1283960 1926059 := bstep (se 1 (by rfl) ⟨1444544, by rfl⟩ : syracuseStep 1926059 = 2889089) B2889089
theorem B4113337 : Blo 1283960 4113337 := bstep (se 2 (by rfl) ⟨1542501, by rfl⟩ : syracuseStep 4113337 = 3085003) B3085003
theorem B1926089 : Blo 1283960 1926089 := bstep (se 2 (by rfl) ⟨722283, by rfl⟩ : syracuseStep 1926089 = 1444567) B1444567
theorem B3253193 : Blo 1283960 3253193 := bstep (se 2 (by rfl) ⟨1219947, by rfl⟩ : syracuseStep 3253193 = 2439895) B2439895
theorem B2892815 : Blo 1283960 2892815 := bstep (se 1 (by rfl) ⟨2169611, by rfl⟩ : syracuseStep 2892815 = 4339223) B4339223
theorem B2892833 : Blo 1283960 2892833 := bstep (se 2 (by rfl) ⟨1084812, by rfl⟩ : syracuseStep 2892833 = 2169625) B2169625
theorem B1926203 : Blo 1283960 1926203 := bstep (se 1 (by rfl) ⟨1444652, by rfl⟩ : syracuseStep 1926203 = 2889305) B2889305
theorem B59352139 : Blo 1283960 59352139 := bstep (se 1 (by rfl) ⟨44514104, by rfl⟩ : syracuseStep 59352139 = 89028209) B89028209
theorem B1926263 : Blo 1283960 1926263 := bstep (se 1 (by rfl) ⟨1444697, by rfl⟩ : syracuseStep 1926263 = 2889395) B2889395
theorem B5858423 : Blo 1283960 5858423 := bstep (se 1 (by rfl) ⟨4393817, by rfl⟩ : syracuseStep 5858423 = 8787635) B8787635
theorem B25052291 : Blo 1283960 25052291 := bstep (se 1 (by rfl) ⟨18789218, by rfl⟩ : syracuseStep 25052291 = 37578437) B37578437
theorem B2229383 : Blo 1283960 2229383 := bstep (se 1 (by rfl) ⟨1672037, by rfl⟩ : syracuseStep 2229383 = 3344075) B3344075
theorem B1926287 : Blo 1283960 1926287 := bstep (se 1 (by rfl) ⟨1444715, by rfl⟩ : syracuseStep 1926287 = 2889431) B2889431
theorem B1926329 : Blo 1283960 1926329 := bstep (se 2 (by rfl) ⟨722373, by rfl⟩ : syracuseStep 1926329 = 1444747) B1444747
theorem B3089609 : Blo 1283960 3089609 := bstep (se 2 (by rfl) ⟨1158603, by rfl⟩ : syracuseStep 3089609 = 2317207) B2317207
theorem B4334849 : Blo 1283960 4334849 := bstep (se 2 (by rfl) ⟨1625568, by rfl⟩ : syracuseStep 4334849 = 3251137) B3251137
theorem B1926407 : Blo 1283960 1926407 := bstep (se 1 (by rfl) ⟨1444805, by rfl⟩ : syracuseStep 1926407 = 2889611) B2889611
theorem B1926443 : Blo 1283960 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B3253547 : Blo 1283960 3253547 := bstep (se 1 (by rfl) ⟨2440160, by rfl⟩ : syracuseStep 3253547 = 4880321) B4880321
theorem B1926473 : Blo 1283960 1926473 := bstep (se 2 (by rfl) ⟨722427, by rfl⟩ : syracuseStep 1926473 = 1444855) B1444855
theorem B2893175 : Blo 1283960 2893175 := bstep (se 1 (by rfl) ⟨2169881, by rfl⟩ : syracuseStep 2893175 = 4339763) B4339763
theorem B4875673 : Blo 1283960 4875673 := bstep (se 2 (by rfl) ⟨1828377, by rfl⟩ : syracuseStep 4875673 = 3656755) B3656755
theorem B1926587 : Blo 1283960 1926587 := bstep (se 1 (by rfl) ⟨1444940, by rfl⟩ : syracuseStep 1926587 = 2889881) B2889881
theorem B1926647 : Blo 1283960 1926647 := bstep (se 1 (by rfl) ⟨1444985, by rfl⟩ : syracuseStep 1926647 = 2889971) B2889971
theorem B3909131 : Blo 1283960 3909131 := bstep (se 1 (by rfl) ⟨2931848, by rfl⟩ : syracuseStep 3909131 = 5863697) B5863697
theorem B1926671 : Blo 1283960 1926671 := bstep (se 1 (by rfl) ⟨1445003, by rfl⟩ : syracuseStep 1926671 = 2890007) B2890007
theorem B2057771 : Blo 1283960 2057771 := bstep (se 1 (by rfl) ⟨1543328, by rfl⟩ : syracuseStep 2057771 = 3086657) B3086657
theorem B2893355 : Blo 1283960 2893355 := bstep (se 1 (by rfl) ⟨2170016, by rfl⟩ : syracuseStep 2893355 = 4340033) B4340033
theorem B1926713 : Blo 1283960 1926713 := bstep (se 2 (by rfl) ⟨722517, by rfl⟩ : syracuseStep 1926713 = 1445035) B1445035
theorem B24692323 : Blo 1283960 24692323 := bstep (se 1 (by rfl) ⟨18519242, by rfl⟩ : syracuseStep 24692323 = 37038485) B37038485
theorem B1926791 : Blo 1283960 1926791 := bstep (se 1 (by rfl) ⟨1445093, by rfl⟩ : syracuseStep 1926791 = 2890187) B2890187
theorem B1926827 : Blo 1283960 1926827 := bstep (se 1 (by rfl) ⟨1445120, by rfl⟩ : syracuseStep 1926827 = 2890241) B2890241
theorem B4875977 : Blo 1283960 4875977 := bstep (se 2 (by rfl) ⟨1828491, by rfl⟩ : syracuseStep 4875977 = 3656983) B3656983
theorem B1926857 : Blo 1283960 1926857 := bstep (se 2 (by rfl) ⟨722571, by rfl⟩ : syracuseStep 1926857 = 1445143) B1445143
theorem B1828651 : Blo 1283960 1828651 := bstep (se 1 (by rfl) ⟨1371488, by rfl⟩ : syracuseStep 1828651 = 2742977) B2742977
theorem B1926971 : Blo 1283960 1926971 := bstep (se 1 (by rfl) ⟨1445228, by rfl⟩ : syracuseStep 1926971 = 2890457) B2890457
theorem B7317337 : Blo 1283960 7317337 := bstep (se 2 (by rfl) ⟨2744001, by rfl⟩ : syracuseStep 7317337 = 5488003) B5488003
theorem B1927031 : Blo 1283960 1927031 := bstep (se 1 (by rfl) ⟨1445273, by rfl⟩ : syracuseStep 1927031 = 2890547) B2890547
theorem B1927055 : Blo 1283960 1927055 := bstep (se 1 (by rfl) ⟨1445291, by rfl⟩ : syracuseStep 1927055 = 2890583) B2890583
theorem B2606995 : Blo 1283960 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B1927097 : Blo 1283960 1927097 := bstep (se 2 (by rfl) ⟨722661, by rfl⟩ : syracuseStep 1927097 = 1445323) B1445323
theorem B1648631 : Blo 1283960 1648631 := bstep (se 1 (by rfl) ⟨1236473, by rfl⟩ : syracuseStep 1648631 = 2472947) B2472947
theorem B1927175 : Blo 1283960 1927175 := bstep (se 1 (by rfl) ⟨1445381, by rfl⟩ : syracuseStep 1927175 = 2890763) B2890763
theorem B4335659 : Blo 1283960 4335659 := bstep (se 1 (by rfl) ⟨3251744, by rfl⟩ : syracuseStep 4335659 = 6503489) B6503489
theorem B1927211 : Blo 1283960 1927211 := bstep (se 1 (by rfl) ⟨1445408, by rfl⟩ : syracuseStep 1927211 = 2890817) B2890817
theorem B1927241 : Blo 1283960 1927241 := bstep (se 2 (by rfl) ⟨722715, by rfl⟩ : syracuseStep 1927241 = 1445431) B1445431
theorem B1927355 : Blo 1283960 1927355 := bstep (se 1 (by rfl) ⟨1445516, by rfl⟩ : syracuseStep 1927355 = 2891033) B2891033
theorem B1927415 : Blo 1283960 1927415 := bstep (se 1 (by rfl) ⟨1445561, by rfl⟩ : syracuseStep 1927415 = 2891123) B2891123
theorem B3254539 : Blo 1283960 3254539 := bstep (se 1 (by rfl) ⟨2440904, by rfl⟩ : syracuseStep 3254539 = 4881809) B4881809
theorem B1927439 : Blo 1283960 1927439 := bstep (se 1 (by rfl) ⟨1445579, by rfl⟩ : syracuseStep 1927439 = 2891159) B2891159
theorem B1927481 : Blo 1283960 1927481 := bstep (se 2 (by rfl) ⟨722805, by rfl⟩ : syracuseStep 1927481 = 1445611) B1445611
theorem B1927559 : Blo 1283960 1927559 := bstep (se 1 (by rfl) ⟨1445669, by rfl⟩ : syracuseStep 1927559 = 2891339) B2891339
theorem B5564819 : Blo 1283960 5564819 := bstep (se 1 (by rfl) ⟨4173614, by rfl⟩ : syracuseStep 5564819 = 8347229) B8347229
theorem B3254681 : Blo 1283960 3254681 := bstep (se 2 (by rfl) ⟨1220505, by rfl⟩ : syracuseStep 3254681 = 2441011) B2441011
theorem B1927595 : Blo 1283960 1927595 := bstep (se 1 (by rfl) ⟨1445696, by rfl⟩ : syracuseStep 1927595 = 2891393) B2891393
theorem B1927625 : Blo 1283960 1927625 := bstep (se 2 (by rfl) ⟨722859, by rfl⟩ : syracuseStep 1927625 = 1445719) B1445719
theorem B1927739 : Blo 1283960 1927739 := bstep (se 1 (by rfl) ⟨1445804, by rfl⟩ : syracuseStep 1927739 = 2891609) B2891609
theorem B3254843 : Blo 1283960 3254843 := bstep (se 1 (by rfl) ⟨2441132, by rfl⟩ : syracuseStep 3254843 = 4882265) B4882265
theorem B10021495 : Blo 1283960 10021495 := bstep (se 1 (by rfl) ⟨7516121, by rfl⟩ : syracuseStep 10021495 = 15032243) B15032243
theorem B18516599 : Blo 1283960 18516599 := bstep (se 1 (by rfl) ⟨13887449, by rfl⟩ : syracuseStep 18516599 = 27774899) B27774899
theorem B4876919 : Blo 1283960 4876919 := bstep (se 1 (by rfl) ⟨3657689, by rfl⟩ : syracuseStep 4876919 = 7315379) B7315379
theorem B1927799 : Blo 1283960 1927799 := bstep (se 1 (by rfl) ⟨1445849, by rfl⟩ : syracuseStep 1927799 = 2891699) B2891699
theorem B1444495 : Blo 1283960 1444495 := bstep (se 1 (by rfl) ⟨1083371, by rfl⟩ : syracuseStep 1444495 = 2166743) B2166743
theorem B1927823 : Blo 1283960 1927823 := bstep (se 1 (by rfl) ⟨1445867, by rfl⟩ : syracuseStep 1927823 = 2891735) B2891735
theorem B1927865 : Blo 1283960 1927865 := bstep (se 2 (by rfl) ⟨722949, by rfl⟩ : syracuseStep 1927865 = 1445899) B1445899
theorem B1927943 : Blo 1283960 1927943 := bstep (se 1 (by rfl) ⟨1445957, by rfl⟩ : syracuseStep 1927943 = 2891915) B2891915
theorem B5491489 : Blo 1283960 5491489 := bstep (se 2 (by rfl) ⟨2059308, by rfl⟩ : syracuseStep 5491489 = 4118617) B4118617
theorem B6941477 : Blo 1283960 6941477 := bstep (se 4 (by rfl) ⟨650763, by rfl⟩ : syracuseStep 6941477 = 1301527) B1301527
theorem B1927979 : Blo 1283960 1927979 := bstep (se 1 (by rfl) ⟨1445984, by rfl⟩ : syracuseStep 1927979 = 2891969) B2891969
theorem B1928009 : Blo 1283960 1928009 := bstep (se 2 (by rfl) ⟨723003, by rfl⟩ : syracuseStep 1928009 = 1446007) B1446007
theorem B1928123 : Blo 1283960 1928123 := bstep (se 1 (by rfl) ⟨1446092, by rfl⟩ : syracuseStep 1928123 = 2892185) B2892185
theorem B1928183 : Blo 1283960 1928183 := bstep (se 1 (by rfl) ⟨1446137, by rfl⟩ : syracuseStep 1928183 = 2892275) B2892275
theorem B1928207 : Blo 1283960 1928207 := bstep (se 1 (by rfl) ⟨1446155, by rfl⟩ : syracuseStep 1928207 = 2892311) B2892311
theorem B1928249 : Blo 1283960 1928249 := bstep (se 2 (by rfl) ⟨723093, by rfl⟩ : syracuseStep 1928249 = 1446187) B1446187
theorem B62516285 : Blo 1283960 62516285 := bstep (se 3 (by rfl) ⟨11721803, by rfl⟩ : syracuseStep 62516285 = 23443607) B23443607
theorem B13896791 : Blo 1283960 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B1444999 : Blo 1283960 1444999 := bstep (se 1 (by rfl) ⟨1083749, by rfl⟩ : syracuseStep 1444999 = 2167499) B2167499
theorem B1928327 : Blo 1283960 1928327 := bstep (se 1 (by rfl) ⟨1446245, by rfl⟩ : syracuseStep 1928327 = 2892491) B2892491
theorem B1928363 : Blo 1283960 1928363 := bstep (se 1 (by rfl) ⟨1446272, by rfl⟩ : syracuseStep 1928363 = 2892545) B2892545
theorem B1625275 : Blo 1283960 1625275 := bstep (se 1 (by rfl) ⟨1218956, by rfl⟩ : syracuseStep 1625275 = 2437913) B2437913
theorem B1928393 : Blo 1283960 1928393 := bstep (se 2 (by rfl) ⟨723147, by rfl⟩ : syracuseStep 1928393 = 1446295) B1446295
theorem B6941933 : Blo 1283960 6941933 := bstep (se 3 (by rfl) ⟨1301612, by rfl⟩ : syracuseStep 6941933 = 2603225) B2603225
theorem B1445179 : Blo 1283960 1445179 := bstep (se 1 (by rfl) ⟨1083884, by rfl⟩ : syracuseStep 1445179 = 2167769) B2167769
theorem B4336955 : Blo 1283960 4336955 := bstep (se 1 (by rfl) ⟨3252716, by rfl⟩ : syracuseStep 4336955 = 6505433) B6505433
theorem B1928507 : Blo 1283960 1928507 := bstep (se 1 (by rfl) ⟨1446380, by rfl⟩ : syracuseStep 1928507 = 2892761) B2892761
theorem B1928567 : Blo 1283960 1928567 := bstep (se 1 (by rfl) ⟨1446425, by rfl⟩ : syracuseStep 1928567 = 2892851) B2892851
theorem B1928591 : Blo 1283960 1928591 := bstep (se 1 (by rfl) ⟨1446443, by rfl⟩ : syracuseStep 1928591 = 2892887) B2892887
theorem B1928633 : Blo 1283960 1928633 := bstep (se 2 (by rfl) ⟨723237, by rfl⟩ : syracuseStep 1928633 = 1446475) B1446475
theorem B1928711 : Blo 1283960 1928711 := bstep (se 1 (by rfl) ⟨1446533, by rfl⟩ : syracuseStep 1928711 = 2893067) B2893067
theorem B7319069 : Blo 1283960 7319069 := bstep (se 3 (by rfl) ⟨1372325, by rfl⟩ : syracuseStep 7319069 = 2744651) B2744651
theorem B1928747 : Blo 1283960 1928747 := bstep (se 1 (by rfl) ⟨1446560, by rfl⟩ : syracuseStep 1928747 = 2893121) B2893121
theorem B4017725 : Blo 1283960 4017725 := bstep (se 3 (by rfl) ⟨753323, by rfl⟩ : syracuseStep 4017725 = 1506647) B1506647
theorem B4877891 : Blo 1283960 4877891 := bstep (se 1 (by rfl) ⟨3658418, by rfl⟩ : syracuseStep 4877891 = 7316837) B7316837
theorem B1928777 : Blo 1283960 1928777 := bstep (se 2 (by rfl) ⟨723291, by rfl⟩ : syracuseStep 1928777 = 1446583) B1446583
theorem B4116055 : Blo 1283960 4116055 := bstep (se 1 (by rfl) ⟨3087041, by rfl⟩ : syracuseStep 4116055 = 6174083) B6174083
theorem B1625771 : Blo 1283960 1625771 := bstep (se 1 (by rfl) ⟨1219328, by rfl⟩ : syracuseStep 1625771 = 2438657) B2438657
theorem B1928891 : Blo 1283960 1928891 := bstep (se 1 (by rfl) ⟨1446668, by rfl⟩ : syracuseStep 1928891 = 2893337) B2893337
theorem B6598381 : Blo 1283960 6598381 := bstep (se 3 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 6598381 = 2474393) B2474393
theorem B1445647 : Blo 1283960 1445647 := bstep (se 1 (by rfl) ⟨1084235, by rfl⟩ : syracuseStep 1445647 = 2168471) B2168471
theorem B4337441 : Blo 1283960 4337441 := bstep (se 2 (by rfl) ⟨1626540, by rfl⟩ : syracuseStep 4337441 = 3253081) B3253081
theorem B9260837 : Blo 1283960 9260837 := bstep (se 4 (by rfl) ⟨868203, by rfl⟩ : syracuseStep 9260837 = 1736407) B1736407
theorem B10981169 : Blo 1283960 10981169 := bstep (se 2 (by rfl) ⟨4117938, by rfl⟩ : syracuseStep 10981169 = 8235877) B8235877
theorem B6500249 : Blo 1283960 6500249 := bstep (se 2 (by rfl) ⟨2437593, by rfl⟩ : syracuseStep 6500249 = 4875187) B4875187
theorem B1855495 : Blo 1283960 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B35164205 : Blo 1283960 35164205 := bstep (se 3 (by rfl) ⟨6593288, by rfl⟩ : syracuseStep 35164205 = 13186577) B13186577
theorem B1626247 : Blo 1283960 1626247 := bstep (se 1 (by rfl) ⟨1219685, by rfl⟩ : syracuseStep 1626247 = 2439371) B2439371
theorem B23761097 : Blo 1283960 23761097 := bstep (se 2 (by rfl) ⟨8910411, by rfl⟩ : syracuseStep 23761097 = 17820823) B17820823
theorem B7319753 : Blo 1283960 7319753 := bstep (se 2 (by rfl) ⟨2744907, by rfl⟩ : syracuseStep 7319753 = 5489815) B5489815
theorem B44519665 : Blo 1283960 44519665 := bstep (se 2 (by rfl) ⟨16694874, by rfl⟩ : syracuseStep 44519665 = 33389749) B33389749
theorem B23433461 : Blo 1283960 23433461 := bstep (se 5 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 23433461 = 2196887) B2196887
theorem B1446151 : Blo 1283960 1446151 := bstep (se 1 (by rfl) ⟨1084613, by rfl⟩ : syracuseStep 1446151 = 2169227) B2169227
theorem B4338035 : Blo 1283960 4338035 := bstep (se 1 (by rfl) ⟨3253526, by rfl⟩ : syracuseStep 4338035 = 6507053) B6507053
theorem B2167175 : Blo 1283960 2167175 := bstep (se 1 (by rfl) ⟨1625381, by rfl⟩ : syracuseStep 2167175 = 3250763) B3250763
theorem B1954219 : Blo 1283960 1954219 := bstep (se 1 (by rfl) ⟨1465664, by rfl⟩ : syracuseStep 1954219 = 2931329) B2931329
theorem B10981817 : Blo 1283960 10981817 := bstep (se 2 (by rfl) ⟨4118181, by rfl⟩ : syracuseStep 10981817 = 8236363) B8236363
theorem B1446331 : Blo 1283960 1446331 := bstep (se 1 (by rfl) ⟨1084748, by rfl⟩ : syracuseStep 1446331 = 2169497) B2169497
theorem B4452893 : Blo 1283960 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B9761309 : Blo 1283960 9761309 := bstep (se 3 (by rfl) ⟨1830245, by rfl⟩ : syracuseStep 9761309 = 3660491) B3660491
theorem B5485117 : Blo 1283960 5485117 := bstep (se 3 (by rfl) ⟨1028459, by rfl⟩ : syracuseStep 5485117 = 2056919) B2056919
theorem B1626743 : Blo 1283960 1626743 := bstep (se 1 (by rfl) ⟨1220057, by rfl⟩ : syracuseStep 1626743 = 2440115) B2440115
theorem B3658441 : Blo 1283960 3658441 := bstep (se 2 (by rfl) ⟨1371915, by rfl⟩ : syracuseStep 3658441 = 2743831) B2743831
theorem B1626895 : Blo 1283960 1626895 := bstep (se 1 (by rfl) ⟨1220171, by rfl⟩ : syracuseStep 1626895 = 2440343) B2440343
theorem B8917775 : Blo 1283960 8917775 := bstep (se 1 (by rfl) ⟨6688331, by rfl⟩ : syracuseStep 8917775 = 13376663) B13376663
theorem B12342131 : Blo 1283960 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B1627067 : Blo 1283960 1627067 := bstep (se 1 (by rfl) ⟨1220300, by rfl⟩ : syracuseStep 1627067 = 2440601) B2440601
theorem B3707849 : Blo 1283960 3707849 := bstep (se 2 (by rfl) ⟨1390443, by rfl⟩ : syracuseStep 3707849 = 2780887) B2780887
theorem B2167823 : Blo 1283960 2167823 := bstep (se 1 (by rfl) ⟨1625867, by rfl⟩ : syracuseStep 2167823 = 3251735) B3251735
theorem B3085427 : Blo 1283960 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B3085465 : Blo 1283960 3085465 := bstep (se 2 (by rfl) ⟨1157049, by rfl⟩ : syracuseStep 3085465 = 2314099) B2314099
theorem B4879561 : Blo 1283960 4879561 := bstep (se 2 (by rfl) ⟨1829835, by rfl⟩ : syracuseStep 4879561 = 3659671) B3659671
theorem B14628113 : Blo 1283960 14628113 := bstep (se 2 (by rfl) ⟨5485542, by rfl⟩ : syracuseStep 14628113 = 10971085) B10971085
theorem B6509969 : Blo 1283960 6509969 := bstep (se 2 (by rfl) ⟨2441238, by rfl⟩ : syracuseStep 6509969 = 4882477) B4882477
theorem B2889107 : Blo 1283960 2889107 := bstep (se 1 (by rfl) ⟨2166830, by rfl⟩ : syracuseStep 2889107 = 4333661) B4333661
theorem B3085715 : Blo 1283960 3085715 := bstep (se 1 (by rfl) ⟨2314286, by rfl⟩ : syracuseStep 3085715 = 4628573) B4628573
theorem B2889161 : Blo 1283960 2889161 := bstep (se 2 (by rfl) ⟨1083435, by rfl⟩ : syracuseStep 2889161 = 2166871) B2166871
theorem B2168363 : Blo 1283960 2168363 := bstep (se 1 (by rfl) ⟨1626272, by rfl⟩ : syracuseStep 2168363 = 3252545) B3252545
theorem B7312963 : Blo 1283960 7312963 := bstep (se 1 (by rfl) ⟨5484722, by rfl⟩ : syracuseStep 7312963 = 10969445) B10969445
theorem B13186739 : Blo 1283960 13186739 := bstep (se 1 (by rfl) ⟨9890054, by rfl⟩ : syracuseStep 13186739 = 19780109) B19780109
theorem B6944545 : Blo 1283960 6944545 := bstep (se 2 (by rfl) ⟨2604204, by rfl⟩ : syracuseStep 6944545 = 5208409) B5208409
theorem B1283975 : Blo 1283960 1283975 := bstep (se 1 (by rfl) ⟨962981, by rfl⟩ : syracuseStep 1283975 = 1925963) B1925963
theorem B1283983 : Blo 1283960 1283983 := bstep (se 1 (by rfl) ⟨962987, by rfl⟩ : syracuseStep 1283983 = 1925975) B1925975
theorem B3471257 : Blo 1283960 3471257 := bstep (se 2 (by rfl) ⟨1301721, by rfl⟩ : syracuseStep 3471257 = 2603443) B2603443
theorem B2168761 : Blo 1283960 2168761 := bstep (se 2 (by rfl) ⟨813285, by rfl⟩ : syracuseStep 2168761 = 1626571) B1626571
theorem B7321529 : Blo 1283960 7321529 := bstep (se 2 (by rfl) ⟨2745573, by rfl⟩ : syracuseStep 7321529 = 5491147) B5491147
theorem B1284027 : Blo 1283960 1284027 := bstep (se 1 (by rfl) ⟨963020, by rfl⟩ : syracuseStep 1284027 = 1926041) B1926041
theorem B1284103 : Blo 1283960 1284103 := bstep (se 1 (by rfl) ⟨963077, by rfl⟩ : syracuseStep 1284103 = 1926155) B1926155
theorem B1284111 : Blo 1283960 1284111 := bstep (se 1 (by rfl) ⟨963083, by rfl⟩ : syracuseStep 1284111 = 1926167) B1926167
theorem B1284155 : Blo 1283960 1284155 := bstep (se 1 (by rfl) ⟨963116, by rfl⟩ : syracuseStep 1284155 = 1926233) B1926233
theorem B2439227 : Blo 1283960 2439227 := bstep (se 1 (by rfl) ⟨1829420, by rfl⟩ : syracuseStep 2439227 = 3658841) B3658841
theorem B1284231 : Blo 1283960 1284231 := bstep (se 1 (by rfl) ⟨963173, by rfl⟩ : syracuseStep 1284231 = 1926347) B1926347
theorem B2889863 : Blo 1283960 2889863 := bstep (se 1 (by rfl) ⟨2167397, by rfl⟩ : syracuseStep 2889863 = 4334795) B4334795
theorem B1284239 : Blo 1283960 1284239 := bstep (se 1 (by rfl) ⟨963179, by rfl⟩ : syracuseStep 1284239 = 1926359) B1926359
theorem B1284283 : Blo 1283960 1284283 := bstep (se 1 (by rfl) ⟨963212, by rfl⟩ : syracuseStep 1284283 = 1926425) B1926425
theorem B1284359 : Blo 1283960 1284359 := bstep (se 1 (by rfl) ⟨963269, by rfl⟩ : syracuseStep 1284359 = 1926539) B1926539
theorem B1284367 : Blo 1283960 1284367 := bstep (se 1 (by rfl) ⟨963275, by rfl⟩ : syracuseStep 1284367 = 1926551) B1926551
theorem B1284411 : Blo 1283960 1284411 := bstep (se 1 (by rfl) ⟨963308, by rfl⟩ : syracuseStep 1284411 = 1926617) B1926617
theorem B2890043 : Blo 1283960 2890043 := bstep (se 1 (by rfl) ⟨2167532, by rfl⟩ : syracuseStep 2890043 = 4335065) B4335065
theorem B1284487 : Blo 1283960 1284487 := bstep (se 1 (by rfl) ⟨963365, by rfl⟩ : syracuseStep 1284487 = 1926731) B1926731
theorem B1284495 : Blo 1283960 1284495 := bstep (se 1 (by rfl) ⟨963371, by rfl⟩ : syracuseStep 1284495 = 1926743) B1926743
theorem B6502841 : Blo 1283960 6502841 := bstep (se 2 (by rfl) ⟨2438565, by rfl⟩ : syracuseStep 6502841 = 4877131) B4877131
theorem B2890169 : Blo 1283960 2890169 := bstep (se 2 (by rfl) ⟨1083813, by rfl⟩ : syracuseStep 2890169 = 2167627) B2167627
theorem B1284539 : Blo 1283960 1284539 := bstep (se 1 (by rfl) ⟨963404, by rfl⟩ : syracuseStep 1284539 = 1926809) B1926809
theorem B1284615 : Blo 1283960 1284615 := bstep (se 1 (by rfl) ⟨963461, by rfl⟩ : syracuseStep 1284615 = 1926923) B1926923
theorem B5487115 : Blo 1283960 5487115 := bstep (se 1 (by rfl) ⟨4115336, by rfl⟩ : syracuseStep 5487115 = 8230673) B8230673
theorem B3660299 : Blo 1283960 3660299 := bstep (se 1 (by rfl) ⟨2745224, by rfl⟩ : syracuseStep 3660299 = 5490449) B5490449
theorem B1284623 : Blo 1283960 1284623 := bstep (se 1 (by rfl) ⟨963467, by rfl⟩ : syracuseStep 1284623 = 1926935) B1926935
theorem B2439713 : Blo 1283960 2439713 := bstep (se 2 (by rfl) ⟨914892, by rfl⟩ : syracuseStep 2439713 = 1829785) B1829785
theorem B11123243 : Blo 1283960 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B1284667 : Blo 1283960 1284667 := bstep (se 1 (by rfl) ⟨963500, by rfl⟩ : syracuseStep 1284667 = 1927001) B1927001
theorem B2169463 : Blo 1283960 2169463 := bstep (se 1 (by rfl) ⟨1627097, by rfl⟩ : syracuseStep 2169463 = 3254195) B3254195
theorem B1284743 : Blo 1283960 1284743 := bstep (se 1 (by rfl) ⟨963557, by rfl⟩ : syracuseStep 1284743 = 1927115) B1927115
theorem B1284751 : Blo 1283960 1284751 := bstep (se 1 (by rfl) ⟨963563, by rfl⟩ : syracuseStep 1284751 = 1927127) B1927127
theorem B13367987 : Blo 1283960 13367987 := bstep (se 1 (by rfl) ⟨10025990, by rfl⟩ : syracuseStep 13367987 = 20051981) B20051981
theorem B1284795 : Blo 1283960 1284795 := bstep (se 1 (by rfl) ⟨963596, by rfl⟩ : syracuseStep 1284795 = 1927193) B1927193
theorem B1284871 : Blo 1283960 1284871 := bstep (se 1 (by rfl) ⟨963653, by rfl⟩ : syracuseStep 1284871 = 1927307) B1927307
theorem B3250955 : Blo 1283960 3250955 := bstep (se 1 (by rfl) ⟨2438216, by rfl⟩ : syracuseStep 3250955 = 4876433) B4876433
theorem B2890511 : Blo 1283960 2890511 := bstep (se 1 (by rfl) ⟨2167883, by rfl⟩ : syracuseStep 2890511 = 4335767) B4335767
theorem B10418959 : Blo 1283960 10418959 := bstep (se 1 (by rfl) ⟨7814219, by rfl⟩ : syracuseStep 10418959 = 15628439) B15628439
theorem B1284879 : Blo 1283960 1284879 := bstep (se 1 (by rfl) ⟨963659, by rfl⟩ : syracuseStep 1284879 = 1927319) B1927319
theorem B10984207 : Blo 1283960 10984207 := bstep (se 1 (by rfl) ⟨8238155, by rfl⟩ : syracuseStep 10984207 = 16476311) B16476311
theorem B2890529 : Blo 1283960 2890529 := bstep (se 2 (by rfl) ⟨1083948, by rfl⟩ : syracuseStep 2890529 = 2167897) B2167897
theorem B1284923 : Blo 1283960 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B2169659 : Blo 1283960 2169659 := bstep (se 1 (by rfl) ⟨1627244, by rfl⟩ : syracuseStep 2169659 = 3254489) B3254489
theorem B1284999 : Blo 1283960 1284999 := bstep (se 1 (by rfl) ⟨963749, by rfl⟩ : syracuseStep 1284999 = 1927499) B1927499
theorem B5282695 : Blo 1283960 5282695 := bstep (se 1 (by rfl) ⟨3962021, by rfl⟩ : syracuseStep 5282695 = 7924043) B7924043
theorem B1465231 : Blo 1283960 1465231 := bstep (se 1 (by rfl) ⟨1098923, by rfl⟩ : syracuseStep 1465231 = 2197847) B2197847
theorem B1285007 : Blo 1283960 1285007 := bstep (se 1 (by rfl) ⟨963755, by rfl⟩ : syracuseStep 1285007 = 1927511) B1927511
theorem B1285051 : Blo 1283960 1285051 := bstep (se 1 (by rfl) ⟨963788, by rfl⟩ : syracuseStep 1285051 = 1927577) B1927577
theorem B1285127 : Blo 1283960 1285127 := bstep (se 1 (by rfl) ⟨963845, by rfl⟩ : syracuseStep 1285127 = 1927691) B1927691
theorem B1285135 : Blo 1283960 1285135 := bstep (se 1 (by rfl) ⟨963851, by rfl⟩ : syracuseStep 1285135 = 1927703) B1927703
theorem B1285179 : Blo 1283960 1285179 := bstep (se 1 (by rfl) ⟨963884, by rfl⟩ : syracuseStep 1285179 = 1927769) B1927769
theorem B2890871 : Blo 1283960 2890871 := bstep (se 1 (by rfl) ⟨2168153, by rfl⟩ : syracuseStep 2890871 = 4336307) B4336307
theorem B1285255 : Blo 1283960 1285255 := bstep (se 1 (by rfl) ⟨963941, by rfl⟩ : syracuseStep 1285255 = 1927883) B1927883
theorem B1285263 : Blo 1283960 1285263 := bstep (se 1 (by rfl) ⟨963947, by rfl⟩ : syracuseStep 1285263 = 1927895) B1927895
theorem B3660947 : Blo 1283960 3660947 := bstep (se 1 (by rfl) ⟨2745710, by rfl⟩ : syracuseStep 3660947 = 5491421) B5491421
theorem B1285307 : Blo 1283960 1285307 := bstep (se 1 (by rfl) ⟨963980, by rfl⟩ : syracuseStep 1285307 = 1927961) B1927961
theorem B2931913 : Blo 1283960 2931913 := bstep (se 2 (by rfl) ⟨1099467, by rfl⟩ : syracuseStep 2931913 = 2198935) B2198935
theorem B2170057 : Blo 1283960 2170057 := bstep (se 2 (by rfl) ⟨813771, by rfl⟩ : syracuseStep 2170057 = 1627543) B1627543
theorem B3087617 : Blo 1283960 3087617 := bstep (se 2 (by rfl) ⟨1157856, by rfl⟩ : syracuseStep 3087617 = 2315713) B2315713
theorem B1285383 : Blo 1283960 1285383 := bstep (se 1 (by rfl) ⟨964037, by rfl⟩ : syracuseStep 1285383 = 1928075) B1928075
theorem B1285391 : Blo 1283960 1285391 := bstep (se 1 (by rfl) ⟨964043, by rfl⟩ : syracuseStep 1285391 = 1928087) B1928087
theorem B2891051 : Blo 1283960 2891051 := bstep (se 1 (by rfl) ⟨2168288, by rfl⟩ : syracuseStep 2891051 = 4336577) B4336577
theorem B9755963 : Blo 1283960 9755963 := bstep (se 1 (by rfl) ⟨7316972, by rfl⟩ : syracuseStep 9755963 = 14633945) B14633945
theorem B1285435 : Blo 1283960 1285435 := bstep (se 1 (by rfl) ⟨964076, by rfl⟩ : syracuseStep 1285435 = 1928153) B1928153
theorem B3661175 : Blo 1283960 3661175 := bstep (se 1 (by rfl) ⟨2745881, by rfl⟩ : syracuseStep 3661175 = 5491763) B5491763
theorem B4881779 : Blo 1283960 4881779 := bstep (se 1 (by rfl) ⟨3661334, by rfl⟩ : syracuseStep 4881779 = 7322669) B7322669
theorem B1285511 : Blo 1283960 1285511 := bstep (se 1 (by rfl) ⟨964133, by rfl⟩ : syracuseStep 1285511 = 1928267) B1928267
theorem B1285519 : Blo 1283960 1285519 := bstep (se 1 (by rfl) ⟨964139, by rfl⟩ : syracuseStep 1285519 = 1928279) B1928279
theorem B3251603 : Blo 1283960 3251603 := bstep (se 1 (by rfl) ⟨2438702, by rfl⟩ : syracuseStep 3251603 = 4877405) B4877405
theorem B1285563 : Blo 1283960 1285563 := bstep (se 1 (by rfl) ⟨964172, by rfl⟩ : syracuseStep 1285563 = 1928345) B1928345
theorem B7314947 : Blo 1283960 7314947 := bstep (se 1 (by rfl) ⟨5486210, by rfl⟩ : syracuseStep 7314947 = 10972421) B10972421
theorem B1285639 : Blo 1283960 1285639 := bstep (se 1 (by rfl) ⟨964229, by rfl⟩ : syracuseStep 1285639 = 1928459) B1928459
theorem B1285647 : Blo 1283960 1285647 := bstep (se 1 (by rfl) ⟨964235, by rfl⟩ : syracuseStep 1285647 = 1928471) B1928471
theorem B1285691 : Blo 1283960 1285691 := bstep (se 1 (by rfl) ⟨964268, by rfl⟩ : syracuseStep 1285691 = 1928537) B1928537
theorem B7044727 : Blo 1283960 7044727 := bstep (se 1 (by rfl) ⟨5283545, by rfl⟩ : syracuseStep 7044727 = 10567091) B10567091
theorem B1285767 : Blo 1283960 1285767 := bstep (se 1 (by rfl) ⟨964325, by rfl⟩ : syracuseStep 1285767 = 1928651) B1928651
theorem B1285775 : Blo 1283960 1285775 := bstep (se 1 (by rfl) ⟨964331, by rfl⟩ : syracuseStep 1285775 = 1928663) B1928663
theorem B2891411 : Blo 1283960 2891411 := bstep (se 1 (by rfl) ⟨2168558, by rfl⟩ : syracuseStep 2891411 = 4337117) B4337117
theorem B3251897 : Blo 1283960 3251897 := bstep (se 2 (by rfl) ⟨1219461, by rfl⟩ : syracuseStep 3251897 = 2438923) B2438923
theorem B1285819 : Blo 1283960 1285819 := bstep (se 1 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 1285819 = 1928729) B1928729
theorem B6504137 : Blo 1283960 6504137 := bstep (se 2 (by rfl) ⟨2439051, by rfl⟩ : syracuseStep 6504137 = 4878103) B4878103
theorem B2891465 : Blo 1283960 2891465 := bstep (se 2 (by rfl) ⟨1084299, by rfl⟩ : syracuseStep 2891465 = 2168599) B2168599
theorem B1285895 : Blo 1283960 1285895 := bstep (se 1 (by rfl) ⟨964421, by rfl⟩ : syracuseStep 1285895 = 1928843) B1928843
theorem B1285903 : Blo 1283960 1285903 := bstep (se 1 (by rfl) ⟨964427, by rfl⟩ : syracuseStep 1285903 = 1928855) B1928855
theorem B15621923 : Blo 1283960 15621923 := bstep (se 1 (by rfl) ⟨11716442, by rfl⟩ : syracuseStep 15621923 = 23432885) B23432885
theorem B7323443 : Blo 1283960 7323443 := bstep (se 1 (by rfl) ⟨5492582, by rfl⟩ : syracuseStep 7323443 = 10985165) B10985165
theorem B1285947 : Blo 1283960 1285947 := bstep (se 1 (by rfl) ⟨964460, by rfl⟩ : syracuseStep 1285947 = 1928921) B1928921
theorem B2604919 : Blo 1283960 2604919 := bstep (se 1 (by rfl) ⟨1953689, by rfl⟩ : syracuseStep 2604919 = 3907379) B3907379
theorem B2473993 : Blo 1283960 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B18530315 : Blo 1283960 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B15622307 : Blo 1283960 15622307 := bstep (se 1 (by rfl) ⟨11716730, by rfl⟩ : syracuseStep 15622307 = 23433461) B23433461
theorem B10977443 : Blo 1283960 10977443 := bstep (se 1 (by rfl) ⟨8233082, by rfl⟩ : syracuseStep 10977443 = 16466165) B16466165
theorem B2892023 : Blo 1283960 2892023 := bstep (se 1 (by rfl) ⟨2169017, by rfl⟩ : syracuseStep 2892023 = 4338035) B4338035
theorem B59359553 : Blo 1283960 59359553 := bstep (se 2 (by rfl) ⟨22259832, by rfl⟩ : syracuseStep 59359553 = 44519665) B44519665
theorem B2605625 : Blo 1283960 2605625 := bstep (se 2 (by rfl) ⟨977109, by rfl⟩ : syracuseStep 2605625 = 1954219) B1954219
theorem B8233645 : Blo 1283960 8233645 := bstep (se 3 (by rfl) ⟨1543808, by rfl⟩ : syracuseStep 8233645 = 3087617) B3087617
theorem B7316153 : Blo 1283960 7316153 := bstep (se 2 (by rfl) ⟨2743557, by rfl⟩ : syracuseStep 7316153 = 5487115) B5487115
theorem B2056951 : Blo 1283960 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B13361993 : Blo 1283960 13361993 := bstep (se 2 (by rfl) ⟨5010747, by rfl⟩ : syracuseStep 13361993 = 10021495) B10021495
theorem B2892617 : Blo 1283960 2892617 := bstep (se 2 (by rfl) ⟨1084731, by rfl⟩ : syracuseStep 2892617 = 2169463) B2169463
theorem B1925993 : Blo 1283960 1925993 := bstep (se 2 (by rfl) ⟨722247, by rfl⟩ : syracuseStep 1925993 = 1444495) B1444495
theorem B1926071 : Blo 1283960 1926071 := bstep (se 1 (by rfl) ⟨1444553, by rfl⟩ : syracuseStep 1926071 = 2889107) B2889107
theorem B1926107 : Blo 1283960 1926107 := bstep (se 1 (by rfl) ⟨1444580, by rfl⟩ : syracuseStep 1926107 = 2889161) B2889161
theorem B2606087 : Blo 1283960 2606087 := bstep (se 1 (by rfl) ⟨1954565, by rfl⟩ : syracuseStep 2606087 = 3909131) B3909131
theorem B1926575 : Blo 1283960 1926575 := bstep (se 1 (by rfl) ⟨1444931, by rfl⟩ : syracuseStep 1926575 = 2889863) B2889863
theorem B79136185 : Blo 1283960 79136185 := bstep (se 2 (by rfl) ⟨29676069, by rfl⟩ : syracuseStep 79136185 = 59352139) B59352139
theorem B1926665 : Blo 1283960 1926665 := bstep (se 2 (by rfl) ⟨722499, by rfl⟩ : syracuseStep 1926665 = 1444999) B1444999
theorem B4113953 : Blo 1283960 4113953 := bstep (se 2 (by rfl) ⟨1542732, by rfl⟩ : syracuseStep 4113953 = 3085465) B3085465
theorem B1926695 : Blo 1283960 1926695 := bstep (se 1 (by rfl) ⟨1445021, by rfl⟩ : syracuseStep 1926695 = 2890043) B2890043
theorem B6506081 : Blo 1283960 6506081 := bstep (se 2 (by rfl) ⟨2439780, by rfl⟩ : syracuseStep 6506081 = 4879561) B4879561
theorem B3909217 : Blo 1283960 3909217 := bstep (se 2 (by rfl) ⟨1465956, by rfl⟩ : syracuseStep 3909217 = 2931913) B2931913
theorem B2893409 : Blo 1283960 2893409 := bstep (se 2 (by rfl) ⟨1085028, by rfl⟩ : syracuseStep 2893409 = 2170057) B2170057
theorem B4335227 : Blo 1283960 4335227 := bstep (se 1 (by rfl) ⟨3251420, by rfl⟩ : syracuseStep 4335227 = 6502841) B6502841
theorem B1926779 : Blo 1283960 1926779 := bstep (se 1 (by rfl) ⟨1445084, by rfl⟩ : syracuseStep 1926779 = 2890169) B2890169
theorem B7415495 : Blo 1283960 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B1926905 : Blo 1283960 1926905 := bstep (se 2 (by rfl) ⟨722589, by rfl⟩ : syracuseStep 1926905 = 1445179) B1445179
theorem B4335389 : Blo 1283960 4335389 := bstep (se 3 (by rfl) ⟨812885, by rfl⟩ : syracuseStep 4335389 = 1625771) B1625771
theorem B1927007 : Blo 1283960 1927007 := bstep (se 1 (by rfl) ⟨1445255, by rfl⟩ : syracuseStep 1927007 = 2890511) B2890511
theorem B1927019 : Blo 1283960 1927019 := bstep (se 1 (by rfl) ⟨1445264, by rfl⟩ : syracuseStep 1927019 = 2890529) B2890529
theorem B1927247 : Blo 1283960 1927247 := bstep (se 1 (by rfl) ⟨1445435, by rfl⟩ : syracuseStep 1927247 = 2890871) B2890871
theorem B9750617 : Blo 1283960 9750617 := bstep (se 2 (by rfl) ⟨3656481, by rfl⟩ : syracuseStep 9750617 = 7312963) B7312963
theorem B1927367 : Blo 1283960 1927367 := bstep (se 1 (by rfl) ⟨1445525, by rfl⟩ : syracuseStep 1927367 = 2891051) B2891051
theorem B3254519 : Blo 1283960 3254519 := bstep (se 1 (by rfl) ⟨2440889, by rfl⟩ : syracuseStep 3254519 = 4881779) B4881779
theorem B4876631 : Blo 1283960 4876631 := bstep (se 1 (by rfl) ⟨3657473, by rfl⟩ : syracuseStep 4876631 = 7314947) B7314947
theorem B1927529 : Blo 1283960 1927529 := bstep (se 2 (by rfl) ⟨722823, by rfl⟩ : syracuseStep 1927529 = 1445647) B1445647
theorem B9259393 : Blo 1283960 9259393 := bstep (se 2 (by rfl) ⟨3472272, by rfl⟩ : syracuseStep 9259393 = 6944545) B6944545
theorem B1927607 : Blo 1283960 1927607 := bstep (se 1 (by rfl) ⟨1445705, by rfl⟩ : syracuseStep 1927607 = 2891411) B2891411
theorem B4336091 : Blo 1283960 4336091 := bstep (se 1 (by rfl) ⟨3252068, by rfl⟩ : syracuseStep 4336091 = 6504137) B6504137
theorem B1927643 : Blo 1283960 1927643 := bstep (se 1 (by rfl) ⟨1445732, by rfl⟩ : syracuseStep 1927643 = 2891465) B2891465
theorem B10414615 : Blo 1283960 10414615 := bstep (se 1 (by rfl) ⟨7810961, by rfl⟩ : syracuseStep 10414615 = 15621923) B15621923
theorem B3475993 : Blo 1283960 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B1444783 : Blo 1283960 1444783 := bstep (se 1 (by rfl) ⟨1083587, by rfl⟩ : syracuseStep 1444783 = 2167175) B2167175
theorem B1928111 : Blo 1283960 1928111 := bstep (se 1 (by rfl) ⟨1446083, by rfl⟩ : syracuseStep 1928111 = 2892167) B2892167
theorem B15641527 : Blo 1283960 15641527 := bstep (se 1 (by rfl) ⟨11731145, by rfl⟩ : syracuseStep 15641527 = 23462291) B23462291
theorem B18787301 : Blo 1283960 18787301 := bstep (se 4 (by rfl) ⟨1761309, by rfl⟩ : syracuseStep 18787301 = 3522619) B3522619
theorem B1928201 : Blo 1283960 1928201 := bstep (se 2 (by rfl) ⟨723075, by rfl⟩ : syracuseStep 1928201 = 1446151) B1446151
theorem B2968595 : Blo 1283960 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B8793107 : Blo 1283960 8793107 := bstep (se 1 (by rfl) ⟨6594830, by rfl⟩ : syracuseStep 8793107 = 13189661) B13189661
theorem B6507539 : Blo 1283960 6507539 := bstep (se 1 (by rfl) ⟨4880654, by rfl⟩ : syracuseStep 6507539 = 9761309) B9761309
theorem B1928231 : Blo 1283960 1928231 := bstep (se 1 (by rfl) ⟨1446173, by rfl⟩ : syracuseStep 1928231 = 2892347) B2892347
theorem B1371215 : Blo 1283960 1371215 := bstep (se 1 (by rfl) ⟨1028411, by rfl⟩ : syracuseStep 1371215 = 2056823) B2056823
theorem B1928315 : Blo 1283960 1928315 := bstep (se 1 (by rfl) ⟨1446236, by rfl⟩ : syracuseStep 1928315 = 2892473) B2892473
theorem B4336793 : Blo 1283960 4336793 := bstep (se 2 (by rfl) ⟨1626297, by rfl⟩ : syracuseStep 4336793 = 3252595) B3252595
theorem B5942443 : Blo 1283960 5942443 := bstep (se 1 (by rfl) ⟨4456832, by rfl⟩ : syracuseStep 5942443 = 8913665) B8913665
theorem B6171851 : Blo 1283960 6171851 := bstep (se 1 (by rfl) ⟨4628888, by rfl⟩ : syracuseStep 6171851 = 9257777) B9257777
theorem B8228087 : Blo 1283960 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B1928441 : Blo 1283960 1928441 := bstep (se 2 (by rfl) ⟨723165, by rfl⟩ : syracuseStep 1928441 = 1446331) B1446331
theorem B8793359 : Blo 1283960 8793359 := bstep (se 1 (by rfl) ⟨6595019, by rfl⟩ : syracuseStep 8793359 = 13190039) B13190039
theorem B1445215 : Blo 1283960 1445215 := bstep (se 1 (by rfl) ⟨1083911, by rfl⟩ : syracuseStep 1445215 = 2167823) B2167823
theorem B1928543 : Blo 1283960 1928543 := bstep (se 1 (by rfl) ⟨1446407, by rfl⟩ : syracuseStep 1928543 = 2892815) B2892815
theorem B1928555 : Blo 1283960 1928555 := bstep (se 1 (by rfl) ⟨1446416, by rfl⟩ : syracuseStep 1928555 = 2892833) B2892833
theorem B19770749 : Blo 1283960 19770749 := bstep (se 3 (by rfl) ⟨3707015, by rfl⟩ : syracuseStep 19770749 = 7414031) B7414031
theorem B1486255 : Blo 1283960 1486255 := bstep (se 1 (by rfl) ⟨1114691, by rfl⟩ : syracuseStep 1486255 = 2229383) B2229383
theorem B2059739 : Blo 1283960 2059739 := bstep (se 1 (by rfl) ⟨1544804, by rfl⟩ : syracuseStep 2059739 = 3089609) B3089609
theorem B9752075 : Blo 1283960 9752075 := bstep (se 1 (by rfl) ⟨7314056, by rfl⟩ : syracuseStep 9752075 = 14628113) B14628113
theorem B1928783 : Blo 1283960 1928783 := bstep (se 1 (by rfl) ⟨1446587, by rfl⟩ : syracuseStep 1928783 = 2893175) B2893175
theorem B4877921 : Blo 1283960 4877921 := bstep (se 2 (by rfl) ⟨1829220, by rfl⟩ : syracuseStep 4877921 = 3658441) B3658441
theorem B1445575 : Blo 1283960 1445575 := bstep (se 1 (by rfl) ⟨1084181, by rfl⟩ : syracuseStep 1445575 = 2168363) B2168363
theorem B1928903 : Blo 1283960 1928903 := bstep (se 1 (by rfl) ⟨1446677, by rfl⟩ : syracuseStep 1928903 = 2893355) B2893355
theorem B8228573 : Blo 1283960 8228573 := bstep (se 3 (by rfl) ⟨1542857, by rfl⟩ : syracuseStep 8228573 = 3085715) B3085715
theorem B14839517 : Blo 1283960 14839517 := bstep (se 3 (by rfl) ⟨2782409, by rfl⟩ : syracuseStep 14839517 = 5564819) B5564819
theorem B4632349 : Blo 1283960 4632349 := bstep (se 3 (by rfl) ⟨868565, by rfl⟩ : syracuseStep 4632349 = 1737131) B1737131
theorem B1953641 : Blo 1283960 1953641 := bstep (se 2 (by rfl) ⟨732615, by rfl⟩ : syracuseStep 1953641 = 1465231) B1465231
theorem B5484449 : Blo 1283960 5484449 := bstep (se 2 (by rfl) ⟨2056668, by rfl⟩ : syracuseStep 5484449 = 4113337) B4113337
theorem B2314171 : Blo 1283960 2314171 := bstep (se 1 (by rfl) ⟨1735628, by rfl⟩ : syracuseStep 2314171 = 3471257) B3471257
theorem B1626151 : Blo 1283960 1626151 := bstep (se 1 (by rfl) ⟨1219613, by rfl⟩ : syracuseStep 1626151 = 2439227) B2439227
theorem B2167033 : Blo 1283960 2167033 := bstep (se 2 (by rfl) ⟨812637, by rfl⟩ : syracuseStep 2167033 = 1625275) B1625275
theorem B4337981 : Blo 1283960 4337981 := bstep (se 3 (by rfl) ⟨813371, by rfl⟩ : syracuseStep 4337981 = 1626743) B1626743
theorem B1626475 : Blo 1283960 1626475 := bstep (se 1 (by rfl) ⟨1219856, by rfl⟩ : syracuseStep 1626475 = 2439713) B2439713
theorem B35164637 : Blo 1283960 35164637 := bstep (se 3 (by rfl) ⟨6593369, by rfl⟩ : syracuseStep 35164637 = 13186739) B13186739
theorem B2167303 : Blo 1283960 2167303 := bstep (se 1 (by rfl) ⟨1625477, by rfl⟩ : syracuseStep 2167303 = 3250955) B3250955
theorem B6500897 : Blo 1283960 6500897 := bstep (se 2 (by rfl) ⟨2437836, by rfl⟩ : syracuseStep 6500897 = 4875673) B4875673
theorem B1446439 : Blo 1283960 1446439 := bstep (se 1 (by rfl) ⟨1084829, by rfl⟩ : syracuseStep 1446439 = 2169659) B2169659
theorem B41677523 : Blo 1283960 41677523 := bstep (se 1 (by rfl) ⟨31258142, by rfl⟩ : syracuseStep 41677523 = 62516285) B62516285
theorem B9392969 : Blo 1283960 9392969 := bstep (se 2 (by rfl) ⟨3522363, by rfl⟩ : syracuseStep 9392969 = 7044727) B7044727
theorem B2167735 : Blo 1283960 2167735 := bstep (se 1 (by rfl) ⟨1625801, by rfl⟩ : syracuseStep 2167735 = 3251603) B3251603
theorem B4879379 : Blo 1283960 4879379 := bstep (se 1 (by rfl) ⟨3659534, by rfl⟩ : syracuseStep 4879379 = 7319069) B7319069
theorem B2438201 : Blo 1283960 2438201 := bstep (se 2 (by rfl) ⟨914325, by rfl⟩ : syracuseStep 2438201 = 1828651) B1828651
theorem B2167931 : Blo 1283960 2167931 := bstep (se 1 (by rfl) ⟨1625948, by rfl⟩ : syracuseStep 2167931 = 3251897) B3251897
theorem B4338845 : Blo 1283960 4338845 := bstep (se 3 (by rfl) ⟨813533, by rfl⟩ : syracuseStep 4338845 = 1627067) B1627067
theorem B6173891 : Blo 1283960 6173891 := bstep (se 1 (by rfl) ⟨4630418, by rfl⟩ : syracuseStep 6173891 = 9260837) B9260837
theorem B7320779 : Blo 1283960 7320779 := bstep (se 1 (by rfl) ⟨5490584, by rfl⟩ : syracuseStep 7320779 = 10981169) B10981169
theorem B4396349 : Blo 1283960 4396349 := bstep (se 3 (by rfl) ⟨824315, by rfl⟩ : syracuseStep 4396349 = 1648631) B1648631
theorem B23442803 : Blo 1283960 23442803 := bstep (se 1 (by rfl) ⟨17582102, by rfl⟩ : syracuseStep 23442803 = 35164205) B35164205
theorem B9754019 : Blo 1283960 9754019 := bstep (se 1 (by rfl) ⟨7315514, by rfl⟩ : syracuseStep 9754019 = 14631029) B14631029
theorem B2889179 : Blo 1283960 2889179 := bstep (se 1 (by rfl) ⟨2166884, by rfl⟩ : syracuseStep 2889179 = 4333769) B4333769
theorem B15840731 : Blo 1283960 15840731 := bstep (se 1 (by rfl) ⟨11880548, by rfl⟩ : syracuseStep 15840731 = 23761097) B23761097
theorem B4879835 : Blo 1283960 4879835 := bstep (se 1 (by rfl) ⟨3659876, by rfl⟩ : syracuseStep 4879835 = 7319753) B7319753
theorem B4118003 : Blo 1283960 4118003 := bstep (se 1 (by rfl) ⟨3088502, by rfl⟩ : syracuseStep 4118003 = 6177005) B6177005
theorem B2168329 : Blo 1283960 2168329 := bstep (se 2 (by rfl) ⟨813123, by rfl⟩ : syracuseStep 2168329 = 1626247) B1626247
theorem B7321211 : Blo 1283960 7321211 := bstep (se 1 (by rfl) ⟨5490908, by rfl⟩ : syracuseStep 7321211 = 10981817) B10981817
theorem B2168491 : Blo 1283960 2168491 := bstep (se 1 (by rfl) ⟨1626368, by rfl⟩ : syracuseStep 2168491 = 3252737) B3252737
theorem B4339385 : Blo 1283960 4339385 := bstep (se 2 (by rfl) ⟨1627269, by rfl⟩ : syracuseStep 4339385 = 3254539) B3254539
theorem B5945183 : Blo 1283960 5945183 := bstep (se 1 (by rfl) ⟨4458887, by rfl⟩ : syracuseStep 5945183 = 8917775) B8917775
theorem B1283963 : Blo 1283960 1283963 := bstep (se 1 (by rfl) ⟨962972, by rfl⟩ : syracuseStep 1283963 = 1925945) B1925945
theorem B1284015 : Blo 1283960 1284015 := bstep (se 1 (by rfl) ⟨963011, by rfl⟩ : syracuseStep 1284015 = 1926023) B1926023
theorem B2889647 : Blo 1283960 2889647 := bstep (se 1 (by rfl) ⟨2167235, by rfl⟩ : syracuseStep 2889647 = 4334471) B4334471
theorem B1284039 : Blo 1283960 1284039 := bstep (se 1 (by rfl) ⟨963029, by rfl⟩ : syracuseStep 1284039 = 1926059) B1926059
theorem B1284059 : Blo 1283960 1284059 := bstep (se 1 (by rfl) ⟨963044, by rfl⟩ : syracuseStep 1284059 = 1926089) B1926089
theorem B2471899 : Blo 1283960 2471899 := bstep (se 1 (by rfl) ⟨1853924, by rfl⟩ : syracuseStep 2471899 = 3707849) B3707849
theorem B2168795 : Blo 1283960 2168795 := bstep (se 1 (by rfl) ⟨1626596, by rfl⟩ : syracuseStep 2168795 = 3253193) B3253193
theorem B1284135 : Blo 1283960 1284135 := bstep (se 1 (by rfl) ⟨963101, by rfl⟩ : syracuseStep 1284135 = 1926203) B1926203
theorem B1284175 : Blo 1283960 1284175 := bstep (se 1 (by rfl) ⟨963131, by rfl⟩ : syracuseStep 1284175 = 1926263) B1926263
theorem B3905615 : Blo 1283960 3905615 := bstep (se 1 (by rfl) ⟨2929211, by rfl⟩ : syracuseStep 3905615 = 5858423) B5858423
theorem B7313489 : Blo 1283960 7313489 := bstep (se 2 (by rfl) ⟨2742558, by rfl⟩ : syracuseStep 7313489 = 5485117) B5485117
theorem B16701527 : Blo 1283960 16701527 := bstep (se 1 (by rfl) ⟨12526145, by rfl⟩ : syracuseStep 16701527 = 25052291) B25052291
theorem B1284191 : Blo 1283960 1284191 := bstep (se 1 (by rfl) ⟨963143, by rfl⟩ : syracuseStep 1284191 = 1926287) B1926287
theorem B1284219 : Blo 1283960 1284219 := bstep (se 1 (by rfl) ⟨963164, by rfl⟩ : syracuseStep 1284219 = 1926329) B1926329
theorem B2889899 : Blo 1283960 2889899 := bstep (se 1 (by rfl) ⟨2167424, by rfl⟩ : syracuseStep 2889899 = 4334849) B4334849
theorem B1284271 : Blo 1283960 1284271 := bstep (se 1 (by rfl) ⟨963203, by rfl⟩ : syracuseStep 1284271 = 1926407) B1926407
theorem B1284295 : Blo 1283960 1284295 := bstep (se 1 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 1284295 = 1926443) B1926443
theorem B2169031 : Blo 1283960 2169031 := bstep (se 1 (by rfl) ⟨1626773, by rfl⟩ : syracuseStep 2169031 = 3253547) B3253547
theorem B1284315 : Blo 1283960 1284315 := bstep (se 1 (by rfl) ⟨963236, by rfl⟩ : syracuseStep 1284315 = 1926473) B1926473
theorem B4339979 : Blo 1283960 4339979 := bstep (se 1 (by rfl) ⟨3254984, by rfl⟩ : syracuseStep 4339979 = 6509969) B6509969
theorem B1284391 : Blo 1283960 1284391 := bstep (se 1 (by rfl) ⟨963293, by rfl⟩ : syracuseStep 1284391 = 1926587) B1926587
theorem B1284431 : Blo 1283960 1284431 := bstep (se 1 (by rfl) ⟨963323, by rfl⟩ : syracuseStep 1284431 = 1926647) B1926647
theorem B1284447 : Blo 1283960 1284447 := bstep (se 1 (by rfl) ⟨963335, by rfl⟩ : syracuseStep 1284447 = 1926671) B1926671
theorem B13891945 : Blo 1283960 13891945 := bstep (se 2 (by rfl) ⟨5209479, by rfl⟩ : syracuseStep 13891945 = 10418959) B10418959
theorem B2169193 : Blo 1283960 2169193 := bstep (se 2 (by rfl) ⟨813447, by rfl⟩ : syracuseStep 2169193 = 1626895) B1626895
theorem B14645609 : Blo 1283960 14645609 := bstep (se 2 (by rfl) ⟨5492103, by rfl⟩ : syracuseStep 14645609 = 10984207) B10984207
theorem B1284475 : Blo 1283960 1284475 := bstep (se 1 (by rfl) ⟨963356, by rfl⟩ : syracuseStep 1284475 = 1926713) B1926713
theorem B7321985 : Blo 1283960 7321985 := bstep (se 2 (by rfl) ⟨2745744, by rfl⟩ : syracuseStep 7321985 = 5491489) B5491489
theorem B1284527 : Blo 1283960 1284527 := bstep (se 1 (by rfl) ⟨963395, by rfl⟩ : syracuseStep 1284527 = 1926791) B1926791
theorem B1284551 : Blo 1283960 1284551 := bstep (se 1 (by rfl) ⟨963413, by rfl⟩ : syracuseStep 1284551 = 1926827) B1926827
theorem B3250651 : Blo 1283960 3250651 := bstep (se 1 (by rfl) ⟨2437988, by rfl⟩ : syracuseStep 3250651 = 4875977) B4875977
theorem B1284571 : Blo 1283960 1284571 := bstep (se 1 (by rfl) ⟨963428, by rfl⟩ : syracuseStep 1284571 = 1926857) B1926857
theorem B7043593 : Blo 1283960 7043593 := bstep (se 2 (by rfl) ⟨2641347, by rfl⟩ : syracuseStep 7043593 = 5282695) B5282695
theorem B2316809 : Blo 1283960 2316809 := bstep (se 2 (by rfl) ⟨868803, by rfl⟩ : syracuseStep 2316809 = 1737607) B1737607
theorem B1284647 : Blo 1283960 1284647 := bstep (se 1 (by rfl) ⟨963485, by rfl⟩ : syracuseStep 1284647 = 1926971) B1926971
theorem B1284687 : Blo 1283960 1284687 := bstep (se 1 (by rfl) ⟨963515, by rfl⟩ : syracuseStep 1284687 = 1927031) B1927031
theorem B1284703 : Blo 1283960 1284703 := bstep (se 1 (by rfl) ⟨963527, by rfl⟩ : syracuseStep 1284703 = 1927055) B1927055
theorem B1284731 : Blo 1283960 1284731 := bstep (se 1 (by rfl) ⟨963548, by rfl⟩ : syracuseStep 1284731 = 1927097) B1927097
theorem B4881019 : Blo 1283960 4881019 := bstep (se 1 (by rfl) ⟨3660764, by rfl⟩ : syracuseStep 4881019 = 7321529) B7321529
theorem B1284783 : Blo 1283960 1284783 := bstep (se 1 (by rfl) ⟨963587, by rfl⟩ : syracuseStep 1284783 = 1927175) B1927175
theorem B2890439 : Blo 1283960 2890439 := bstep (se 1 (by rfl) ⟨2167829, by rfl⟩ : syracuseStep 2890439 = 4335659) B4335659
theorem B1284807 : Blo 1283960 1284807 := bstep (se 1 (by rfl) ⟨963605, by rfl⟩ : syracuseStep 1284807 = 1927211) B1927211
theorem B1284827 : Blo 1283960 1284827 := bstep (se 1 (by rfl) ⟨963620, by rfl⟩ : syracuseStep 1284827 = 1927241) B1927241
theorem B5487389 : Blo 1283960 5487389 := bstep (se 3 (by rfl) ⟨1028885, by rfl⟩ : syracuseStep 5487389 = 2057771) B2057771
theorem B1284903 : Blo 1283960 1284903 := bstep (se 1 (by rfl) ⟨963677, by rfl⟩ : syracuseStep 1284903 = 1927355) B1927355
theorem B1284943 : Blo 1283960 1284943 := bstep (se 1 (by rfl) ⟨963707, by rfl⟩ : syracuseStep 1284943 = 1927415) B1927415
theorem B1284959 : Blo 1283960 1284959 := bstep (se 1 (by rfl) ⟨963719, by rfl⟩ : syracuseStep 1284959 = 1927439) B1927439
theorem B1284987 : Blo 1283960 1284987 := bstep (se 1 (by rfl) ⟨963740, by rfl⟩ : syracuseStep 1284987 = 1927481) B1927481
theorem B1285039 : Blo 1283960 1285039 := bstep (se 1 (by rfl) ⟨963779, by rfl⟩ : syracuseStep 1285039 = 1927559) B1927559
theorem B2169787 : Blo 1283960 2169787 := bstep (se 1 (by rfl) ⟨1627340, by rfl⟩ : syracuseStep 2169787 = 3254681) B3254681
theorem B1285063 : Blo 1283960 1285063 := bstep (se 1 (by rfl) ⟨963797, by rfl⟩ : syracuseStep 1285063 = 1927595) B1927595
theorem B1285083 : Blo 1283960 1285083 := bstep (se 1 (by rfl) ⟨963812, by rfl⟩ : syracuseStep 1285083 = 1927625) B1927625
theorem B2440199 : Blo 1283960 2440199 := bstep (se 1 (by rfl) ⟨1830149, by rfl⟩ : syracuseStep 2440199 = 3660299) B3660299
theorem B1285159 : Blo 1283960 1285159 := bstep (se 1 (by rfl) ⟨963869, by rfl⟩ : syracuseStep 1285159 = 1927739) B1927739
theorem B2169895 : Blo 1283960 2169895 := bstep (se 1 (by rfl) ⟨1627421, by rfl⟩ : syracuseStep 2169895 = 3254843) B3254843
theorem B12344399 : Blo 1283960 12344399 := bstep (se 1 (by rfl) ⟨9258299, by rfl⟩ : syracuseStep 12344399 = 18516599) B18516599
theorem B3251279 : Blo 1283960 3251279 := bstep (se 1 (by rfl) ⟨2438459, by rfl⟩ : syracuseStep 3251279 = 4876919) B4876919
theorem B1285199 : Blo 1283960 1285199 := bstep (se 1 (by rfl) ⟨963899, by rfl⟩ : syracuseStep 1285199 = 1927799) B1927799
theorem B1285215 : Blo 1283960 1285215 := bstep (se 1 (by rfl) ⟨963911, by rfl⟩ : syracuseStep 1285215 = 1927823) B1927823
theorem B8911991 : Blo 1283960 8911991 := bstep (se 1 (by rfl) ⟨6683993, by rfl⟩ : syracuseStep 8911991 = 13367987) B13367987
theorem B1285243 : Blo 1283960 1285243 := bstep (se 1 (by rfl) ⟨963932, by rfl⟩ : syracuseStep 1285243 = 1927865) B1927865
theorem B1285295 : Blo 1283960 1285295 := bstep (se 1 (by rfl) ⟨963971, by rfl⟩ : syracuseStep 1285295 = 1927943) B1927943
theorem B4627651 : Blo 1283960 4627651 := bstep (se 1 (by rfl) ⟨3470738, by rfl⟩ : syracuseStep 4627651 = 6941477) B6941477
theorem B1285319 : Blo 1283960 1285319 := bstep (se 1 (by rfl) ⟨963989, by rfl⟩ : syracuseStep 1285319 = 1927979) B1927979
theorem B1285339 : Blo 1283960 1285339 := bstep (se 1 (by rfl) ⟨964004, by rfl⟩ : syracuseStep 1285339 = 1928009) B1928009
theorem B1285415 : Blo 1283960 1285415 := bstep (se 1 (by rfl) ⟨964061, by rfl⟩ : syracuseStep 1285415 = 1928123) B1928123
theorem B1285455 : Blo 1283960 1285455 := bstep (se 1 (by rfl) ⟨964091, by rfl⟩ : syracuseStep 1285455 = 1928183) B1928183
theorem B1285471 : Blo 1283960 1285471 := bstep (se 1 (by rfl) ⟨964103, by rfl⟩ : syracuseStep 1285471 = 1928207) B1928207
theorem B1285499 : Blo 1283960 1285499 := bstep (se 1 (by rfl) ⟨964124, by rfl⟩ : syracuseStep 1285499 = 1928249) B1928249
theorem B9264527 : Blo 1283960 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B1285551 : Blo 1283960 1285551 := bstep (se 1 (by rfl) ⟨964163, by rfl⟩ : syracuseStep 1285551 = 1928327) B1928327
theorem B2440631 : Blo 1283960 2440631 := bstep (se 1 (by rfl) ⟨1830473, by rfl⟩ : syracuseStep 2440631 = 3660947) B3660947
theorem B1285575 : Blo 1283960 1285575 := bstep (se 1 (by rfl) ⟨964181, by rfl⟩ : syracuseStep 1285575 = 1928363) B1928363
theorem B5488073 : Blo 1283960 5488073 := bstep (se 2 (by rfl) ⟨2058027, by rfl⟩ : syracuseStep 5488073 = 4116055) B4116055
theorem B32923097 : Blo 1283960 32923097 := bstep (se 2 (by rfl) ⟨12346161, by rfl⟩ : syracuseStep 32923097 = 24692323) B24692323
theorem B1285595 : Blo 1283960 1285595 := bstep (se 1 (by rfl) ⟨964196, by rfl⟩ : syracuseStep 1285595 = 1928393) B1928393
theorem B4627955 : Blo 1283960 4627955 := bstep (se 1 (by rfl) ⟨3470966, by rfl⟩ : syracuseStep 4627955 = 6941933) B6941933
theorem B6503975 : Blo 1283960 6503975 := bstep (se 1 (by rfl) ⟨4877981, by rfl⟩ : syracuseStep 6503975 = 9755963) B9755963
theorem B2891303 : Blo 1283960 2891303 := bstep (se 1 (by rfl) ⟨2168477, by rfl⟩ : syracuseStep 2891303 = 4336955) B4336955
theorem B1285671 : Blo 1283960 1285671 := bstep (se 1 (by rfl) ⟨964253, by rfl⟩ : syracuseStep 1285671 = 1928507) B1928507
theorem B2440783 : Blo 1283960 2440783 := bstep (se 1 (by rfl) ⟨1830587, by rfl⟩ : syracuseStep 2440783 = 3661175) B3661175
theorem B1285711 : Blo 1283960 1285711 := bstep (se 1 (by rfl) ⟨964283, by rfl⟩ : syracuseStep 1285711 = 1928567) B1928567
theorem B1285727 : Blo 1283960 1285727 := bstep (se 1 (by rfl) ⟨964295, by rfl⟩ : syracuseStep 1285727 = 1928591) B1928591
theorem B1285755 : Blo 1283960 1285755 := bstep (se 1 (by rfl) ⟨964316, by rfl⟩ : syracuseStep 1285755 = 1928633) B1928633
theorem B8797841 : Blo 1283960 8797841 := bstep (se 2 (by rfl) ⟨3299190, by rfl⟩ : syracuseStep 8797841 = 6598381) B6598381
theorem B1285807 : Blo 1283960 1285807 := bstep (se 1 (by rfl) ⟨964355, by rfl⟩ : syracuseStep 1285807 = 1928711) B1928711
theorem B1285831 : Blo 1283960 1285831 := bstep (se 1 (by rfl) ⟨964373, by rfl⟩ : syracuseStep 1285831 = 1928747) B1928747
theorem B2678483 : Blo 1283960 2678483 := bstep (se 1 (by rfl) ⟨2008862, by rfl⟩ : syracuseStep 2678483 = 4017725) B4017725
theorem B3251927 : Blo 1283960 3251927 := bstep (se 1 (by rfl) ⟨2438945, by rfl⟩ : syracuseStep 3251927 = 4877891) B4877891
theorem B1285851 : Blo 1283960 1285851 := bstep (se 1 (by rfl) ⟨964388, by rfl⟩ : syracuseStep 1285851 = 1928777) B1928777
theorem B9756449 : Blo 1283960 9756449 := bstep (se 2 (by rfl) ⟨3658668, by rfl⟩ : syracuseStep 9756449 = 7317337) B7317337
theorem B1285927 : Blo 1283960 1285927 := bstep (se 1 (by rfl) ⟨964445, by rfl⟩ : syracuseStep 1285927 = 1928891) B1928891
theorem B3473225 : Blo 1283960 3473225 := bstep (se 2 (by rfl) ⟨1302459, by rfl⟩ : syracuseStep 3473225 = 2604919) B2604919
theorem B2891627 : Blo 1283960 2891627 := bstep (se 1 (by rfl) ⟨2168720, by rfl⟩ : syracuseStep 2891627 = 4337441) B4337441
theorem B4882295 : Blo 1283960 4882295 := bstep (se 1 (by rfl) ⟨3661721, by rfl⟩ : syracuseStep 4882295 = 7323443) B7323443
theorem B2891681 : Blo 1283960 2891681 := bstep (se 2 (by rfl) ⟨1084380, by rfl⟩ : syracuseStep 2891681 = 2168761) B2168761
theorem B4333499 : Blo 1283960 4333499 := bstep (se 1 (by rfl) ⟨3250124, by rfl⟩ : syracuseStep 4333499 = 6500249) B6500249
theorem B12353543 : Blo 1283960 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B2891987 : Blo 1283960 2891987 := bstep (se 1 (by rfl) ⟨2168990, by rfl⟩ : syracuseStep 2891987 = 4337981) B4337981
theorem B2892041 : Blo 1283960 2892041 := bstep (se 2 (by rfl) ⟨1084515, by rfl⟩ : syracuseStep 2892041 = 2169031) B2169031
theorem B23765309 : Blo 1283960 23765309 := bstep (se 3 (by rfl) ⟨4455995, by rfl⟩ : syracuseStep 23765309 = 8911991) B8911991
theorem B4333931 : Blo 1283960 4333931 := bstep (se 1 (by rfl) ⟨3250448, by rfl⟩ : syracuseStep 4333931 = 6500897) B6500897
theorem B1737083 : Blo 1283960 1737083 := bstep (se 1 (by rfl) ⟨1302812, by rfl⟩ : syracuseStep 1737083 = 2605625) B2605625
theorem B18522593 : Blo 1283960 18522593 := bstep (se 2 (by rfl) ⟨6945972, by rfl⟩ : syracuseStep 18522593 = 13891945) B13891945
theorem B2892257 : Blo 1283960 2892257 := bstep (se 2 (by rfl) ⟨1084596, by rfl⟩ : syracuseStep 2892257 = 2169193) B2169193
theorem B12345857 : Blo 1283960 12345857 := bstep (se 2 (by rfl) ⟨4629696, by rfl⟩ : syracuseStep 12345857 = 9259393) B9259393
theorem B4334201 : Blo 1283960 4334201 := bstep (se 2 (by rfl) ⟨1625325, by rfl⟩ : syracuseStep 4334201 = 3250651) B3250651
theorem B1737391 : Blo 1283960 1737391 := bstep (se 1 (by rfl) ⟨1303043, by rfl⟩ : syracuseStep 1737391 = 2606087) B2606087
theorem B3252919 : Blo 1283960 3252919 := bstep (se 1 (by rfl) ⟨2439689, by rfl⟩ : syracuseStep 3252919 = 4879379) B4879379
theorem B13886153 : Blo 1283960 13886153 := bstep (se 2 (by rfl) ⟨5207307, by rfl⟩ : syracuseStep 13886153 = 10414615) B10414615
theorem B2892563 : Blo 1283960 2892563 := bstep (se 1 (by rfl) ⟨2169422, by rfl⟩ : syracuseStep 2892563 = 4338845) B4338845
theorem B10978193 : Blo 1283960 10978193 := bstep (se 2 (by rfl) ⟨4116822, by rfl⟩ : syracuseStep 10978193 = 8233645) B8233645
theorem B1926119 : Blo 1283960 1926119 := bstep (se 1 (by rfl) ⟨1444589, by rfl⟩ : syracuseStep 1926119 = 2889179) B2889179
theorem B3253223 : Blo 1283960 3253223 := bstep (se 1 (by rfl) ⟨2439917, by rfl⟩ : syracuseStep 3253223 = 4879835) B4879835
theorem B2745335 : Blo 1283960 2745335 := bstep (se 1 (by rfl) ⟨2059001, by rfl⟩ : syracuseStep 2745335 = 4118003) B4118003
theorem B2892923 : Blo 1283960 2892923 := bstep (se 1 (by rfl) ⟨2169692, by rfl⟩ : syracuseStep 2892923 = 4339385) B4339385
theorem B1926377 : Blo 1283960 1926377 := bstep (se 2 (by rfl) ⟨722391, by rfl⟩ : syracuseStep 1926377 = 1444783) B1444783
theorem B2893049 : Blo 1283960 2893049 := bstep (se 2 (by rfl) ⟨1084893, by rfl⟩ : syracuseStep 2893049 = 2169787) B2169787
theorem B1926431 : Blo 1283960 1926431 := bstep (se 1 (by rfl) ⟨1444823, by rfl⟩ : syracuseStep 1926431 = 2889647) B2889647
theorem B6178157 : Blo 1283960 6178157 := bstep (se 3 (by rfl) ⟨1158404, by rfl⟩ : syracuseStep 6178157 = 2316809) B2316809
theorem B2893193 : Blo 1283960 2893193 := bstep (se 2 (by rfl) ⟨1084947, by rfl⟩ : syracuseStep 2893193 = 2169895) B2169895
theorem B4875659 : Blo 1283960 4875659 := bstep (se 1 (by rfl) ⟨3656744, by rfl⟩ : syracuseStep 4875659 = 7313489) B7313489
theorem B11134351 : Blo 1283960 11134351 := bstep (se 1 (by rfl) ⟨8350763, by rfl⟩ : syracuseStep 11134351 = 16701527) B16701527
theorem B1926599 : Blo 1283960 1926599 := bstep (se 1 (by rfl) ⟨1444949, by rfl⟩ : syracuseStep 1926599 = 2889899) B2889899
theorem B2893319 : Blo 1283960 2893319 := bstep (se 1 (by rfl) ⟨2169989, by rfl⟩ : syracuseStep 2893319 = 4339979) B4339979
theorem B7923257 : Blo 1283960 7923257 := bstep (se 2 (by rfl) ⟨2971221, by rfl⟩ : syracuseStep 7923257 = 5942443) B5942443
theorem B6170201 : Blo 1283960 6170201 := bstep (se 2 (by rfl) ⟨2313825, by rfl⟩ : syracuseStep 6170201 = 4627651) B4627651
theorem B1926953 : Blo 1283960 1926953 := bstep (se 2 (by rfl) ⟨722607, by rfl⟩ : syracuseStep 1926953 = 1445215) B1445215
theorem B1926959 : Blo 1283960 1926959 := bstep (se 1 (by rfl) ⟨1445219, by rfl⟩ : syracuseStep 1926959 = 2890439) B2890439
theorem B105514913 : Blo 1283960 105514913 := bstep (se 2 (by rfl) ⟨39568092, by rfl⟩ : syracuseStep 105514913 = 79136185) B79136185
theorem B3254377 : Blo 1283960 3254377 := bstep (se 2 (by rfl) ⟨1220391, by rfl⟩ : syracuseStep 3254377 = 2440783) B2440783
theorem B5212289 : Blo 1283960 5212289 := bstep (se 2 (by rfl) ⟨1954608, by rfl⟩ : syracuseStep 5212289 = 3909217) B3909217
theorem B4114567 : Blo 1283960 4114567 := bstep (se 1 (by rfl) ⟨3085925, by rfl⟩ : syracuseStep 4114567 = 6171851) B6171851
theorem B1927433 : Blo 1283960 1927433 := bstep (se 2 (by rfl) ⟨722787, by rfl⟩ : syracuseStep 1927433 = 1445575) B1445575
theorem B21948731 : Blo 1283960 21948731 := bstep (se 1 (by rfl) ⟨16461548, by rfl⟩ : syracuseStep 21948731 = 32923097) B32923097
theorem B4335983 : Blo 1283960 4335983 := bstep (se 1 (by rfl) ⟨3251987, by rfl⟩ : syracuseStep 4335983 = 6503975) B6503975
theorem B1927535 : Blo 1283960 1927535 := bstep (se 1 (by rfl) ⟨1445651, by rfl⟩ : syracuseStep 1927535 = 2891303) B2891303
theorem B14625197 : Blo 1283960 14625197 := bstep (se 3 (by rfl) ⟨2742224, by rfl⟩ : syracuseStep 14625197 = 5484449) B5484449
theorem B1927751 : Blo 1283960 1927751 := bstep (se 1 (by rfl) ⟨1445813, by rfl⟩ : syracuseStep 1927751 = 2891627) B2891627
theorem B3254863 : Blo 1283960 3254863 := bstep (se 1 (by rfl) ⟨2441147, by rfl⟩ : syracuseStep 3254863 = 4882295) B4882295
theorem B1927787 : Blo 1283960 1927787 := bstep (se 1 (by rfl) ⟨1445840, by rfl⟩ : syracuseStep 1927787 = 2891681) B2891681
theorem B3295865 : Blo 1283960 3295865 := bstep (se 2 (by rfl) ⟨1235949, by rfl⟩ : syracuseStep 3295865 = 2471899) B2471899
theorem B10414871 : Blo 1283960 10414871 := bstep (se 1 (by rfl) ⟨7811153, by rfl⟩ : syracuseStep 10414871 = 15622307) B15622307
theorem B7318295 : Blo 1283960 7318295 := bstep (se 1 (by rfl) ⟨5488721, by rfl⟩ : syracuseStep 7318295 = 10977443) B10977443
theorem B1928015 : Blo 1283960 1928015 := bstep (se 1 (by rfl) ⟨1446011, by rfl⟩ : syracuseStep 1928015 = 2892023) B2892023
theorem B3656573 : Blo 1283960 3656573 := bstep (se 3 (by rfl) ⟨685607, by rfl⟩ : syracuseStep 3656573 = 1371215) B1371215
theorem B10414973 : Blo 1283960 10414973 := bstep (se 3 (by rfl) ⟨1952807, by rfl⟩ : syracuseStep 10414973 = 3905615) B3905615
theorem B4877435 : Blo 1283960 4877435 := bstep (se 1 (by rfl) ⟨3658076, by rfl⟩ : syracuseStep 4877435 = 7316153) B7316153
theorem B8907995 : Blo 1283960 8907995 := bstep (se 1 (by rfl) ⟨6680996, by rfl⟩ : syracuseStep 8907995 = 13361993) B13361993
theorem B1928411 : Blo 1283960 1928411 := bstep (se 1 (by rfl) ⟨1446308, by rfl⟩ : syracuseStep 1928411 = 2892617) B2892617
theorem B9391457 : Blo 1283960 9391457 := bstep (se 2 (by rfl) ⟨3521796, by rfl⟩ : syracuseStep 9391457 = 7043593) B7043593
theorem B1928585 : Blo 1283960 1928585 := bstep (se 2 (by rfl) ⟨723219, by rfl⟩ : syracuseStep 1928585 = 1446439) B1446439
theorem B1445287 : Blo 1283960 1445287 := bstep (se 1 (by rfl) ⟨1083965, by rfl⟩ : syracuseStep 1445287 = 2167931) B2167931
theorem B4115927 : Blo 1283960 4115927 := bstep (se 1 (by rfl) ⟨3086945, by rfl⟩ : syracuseStep 4115927 = 6173891) B6173891
theorem B6508025 : Blo 1283960 6508025 := bstep (se 2 (by rfl) ⟨2440509, by rfl⟩ : syracuseStep 6508025 = 4881019) B4881019
theorem B4337387 : Blo 1283960 4337387 := bstep (se 1 (by rfl) ⟨3253040, by rfl⟩ : syracuseStep 4337387 = 6506081) B6506081
theorem B1928939 : Blo 1283960 1928939 := bstep (se 1 (by rfl) ⟨1446704, by rfl⟩ : syracuseStep 1928939 = 2893409) B2893409
theorem B4943663 : Blo 1283960 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B6508349 : Blo 1283960 6508349 := bstep (se 3 (by rfl) ⟨1220315, by rfl⟩ : syracuseStep 6508349 = 2440631) B2440631
theorem B42241949 : Blo 1283960 42241949 := bstep (se 3 (by rfl) ⟨7920365, by rfl⟩ : syracuseStep 42241949 = 15840731) B15840731
theorem B1445863 : Blo 1283960 1445863 := bstep (se 1 (by rfl) ⟨1084397, by rfl⟩ : syracuseStep 1445863 = 2168795) B2168795
theorem B6500411 : Blo 1283960 6500411 := bstep (se 1 (by rfl) ⟨4875308, by rfl⟩ : syracuseStep 6500411 = 9750617) B9750617
theorem B3658259 : Blo 1283960 3658259 := bstep (se 1 (by rfl) ⟨2743694, by rfl⟩ : syracuseStep 3658259 = 5487389) B5487389
theorem B1626799 : Blo 1283960 1626799 := bstep (se 1 (by rfl) ⟨1220099, by rfl⟩ : syracuseStep 1626799 = 2440199) B2440199
theorem B1979063 : Blo 1283960 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B5862071 : Blo 1283960 5862071 := bstep (se 1 (by rfl) ⟨4396553, by rfl⟩ : syracuseStep 5862071 = 8793107) B8793107
theorem B4338359 : Blo 1283960 4338359 := bstep (se 1 (by rfl) ⟨3253769, by rfl⟩ : syracuseStep 4338359 = 6507539) B6507539
theorem B8229599 : Blo 1283960 8229599 := bstep (se 1 (by rfl) ⟨6172199, by rfl⟩ : syracuseStep 8229599 = 12344399) B12344399
theorem B2167519 : Blo 1283960 2167519 := bstep (se 1 (by rfl) ⟨1625639, by rfl⟩ : syracuseStep 2167519 = 3251279) B3251279
theorem B5485391 : Blo 1283960 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B5862239 : Blo 1283960 5862239 := bstep (se 1 (by rfl) ⟨4396679, by rfl⟩ : syracuseStep 5862239 = 8793359) B8793359
theorem B25047917 : Blo 1283960 25047917 := bstep (se 3 (by rfl) ⟨4696484, by rfl⟩ : syracuseStep 25047917 = 9392969) B9392969
theorem B3658715 : Blo 1283960 3658715 := bstep (se 1 (by rfl) ⟨2744036, by rfl⟩ : syracuseStep 3658715 = 5488073) B5488073
theorem B1373159 : Blo 1283960 1373159 := bstep (se 1 (by rfl) ⟨1029869, by rfl⟩ : syracuseStep 1373159 = 2059739) B2059739
theorem B3085303 : Blo 1283960 3085303 := bstep (se 1 (by rfl) ⟨2313977, by rfl⟩ : syracuseStep 3085303 = 4627955) B4627955
theorem B6501383 : Blo 1283960 6501383 := bstep (se 1 (by rfl) ⟨4876037, by rfl⟩ : syracuseStep 6501383 = 9752075) B9752075
theorem B2167951 : Blo 1283960 2167951 := bstep (se 1 (by rfl) ⟨1625963, by rfl⟩ : syracuseStep 2167951 = 3251927) B3251927
theorem B5485715 : Blo 1283960 5485715 := bstep (se 1 (by rfl) ⟨4114286, by rfl⟩ : syracuseStep 5485715 = 8228573) B8228573
theorem B9893011 : Blo 1283960 9893011 := bstep (se 1 (by rfl) ⟨7419758, by rfl⟩ : syracuseStep 9893011 = 14839517) B14839517
theorem B2315483 : Blo 1283960 2315483 := bstep (se 1 (by rfl) ⟨1736612, by rfl⟩ : syracuseStep 2315483 = 3473225) B3473225
theorem B3085561 : Blo 1283960 3085561 := bstep (se 2 (by rfl) ⟨1157085, by rfl⟩ : syracuseStep 3085561 = 2314171) B2314171
theorem B2888999 : Blo 1283960 2888999 := bstep (se 1 (by rfl) ⟨2166749, by rfl⟩ : syracuseStep 2888999 = 4333499) B4333499
theorem B3298657 : Blo 1283960 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B2168201 : Blo 1283960 2168201 := bstep (se 2 (by rfl) ⟨813075, by rfl⟩ : syracuseStep 2168201 = 1626151) B1626151
theorem B6501869 : Blo 1283960 6501869 := bstep (se 3 (by rfl) ⟨1219100, by rfl⟩ : syracuseStep 6501869 = 2438201) B2438201
theorem B39573035 : Blo 1283960 39573035 := bstep (se 1 (by rfl) ⟨29679776, by rfl⟩ : syracuseStep 39573035 = 59359553) B59359553
theorem B23443091 : Blo 1283960 23443091 := bstep (se 1 (by rfl) ⟨17582318, by rfl⟩ : syracuseStep 23443091 = 35164637) B35164637
theorem B2889377 : Blo 1283960 2889377 := bstep (se 2 (by rfl) ⟨1083516, by rfl⟩ : syracuseStep 2889377 = 2167033) B2167033
theorem B27785015 : Blo 1283960 27785015 := bstep (se 1 (by rfl) ⟨20838761, by rfl⟩ : syracuseStep 27785015 = 41677523) B41677523
theorem B2168633 : Blo 1283960 2168633 := bstep (se 2 (by rfl) ⟨813237, by rfl⟩ : syracuseStep 2168633 = 1626475) B1626475
theorem B1283995 : Blo 1283960 1283995 := bstep (se 1 (by rfl) ⟨962996, by rfl⟩ : syracuseStep 1283995 = 1925993) B1925993
theorem B1284047 : Blo 1283960 1284047 := bstep (se 1 (by rfl) ⟨963035, by rfl⟩ : syracuseStep 1284047 = 1926071) B1926071
theorem B1284071 : Blo 1283960 1284071 := bstep (se 1 (by rfl) ⟨963053, by rfl⟩ : syracuseStep 1284071 = 1926107) B1926107
theorem B2889737 : Blo 1283960 2889737 := bstep (se 2 (by rfl) ⟨1083651, by rfl⟩ : syracuseStep 2889737 = 2167303) B2167303
theorem B4634657 : Blo 1283960 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B4880519 : Blo 1283960 4880519 := bstep (se 1 (by rfl) ⟨3660389, by rfl⟩ : syracuseStep 4880519 = 7320779) B7320779
theorem B2930899 : Blo 1283960 2930899 := bstep (se 1 (by rfl) ⟨2198174, by rfl⟩ : syracuseStep 2930899 = 4396349) B4396349
theorem B15628535 : Blo 1283960 15628535 := bstep (se 1 (by rfl) ⟨11721401, by rfl⟩ : syracuseStep 15628535 = 23442803) B23442803
theorem B6502679 : Blo 1283960 6502679 := bstep (se 1 (by rfl) ⟨4877009, by rfl⟩ : syracuseStep 6502679 = 9754019) B9754019
theorem B1284383 : Blo 1283960 1284383 := bstep (se 1 (by rfl) ⟨963287, by rfl⟩ : syracuseStep 1284383 = 1926575) B1926575
theorem B2742601 : Blo 1283960 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B1284443 : Blo 1283960 1284443 := bstep (se 1 (by rfl) ⟨963332, by rfl⟩ : syracuseStep 1284443 = 1926665) B1926665
theorem B2742635 : Blo 1283960 2742635 := bstep (se 1 (by rfl) ⟨2056976, by rfl⟩ : syracuseStep 2742635 = 4113953) B4113953
theorem B1284463 : Blo 1283960 1284463 := bstep (se 1 (by rfl) ⟨963347, by rfl⟩ : syracuseStep 1284463 = 1926695) B1926695
theorem B2890151 : Blo 1283960 2890151 := bstep (se 1 (by rfl) ⟨2167613, by rfl⟩ : syracuseStep 2890151 = 4335227) B4335227
theorem B1284519 : Blo 1283960 1284519 := bstep (se 1 (by rfl) ⟨963389, by rfl⟩ : syracuseStep 1284519 = 1926779) B1926779
theorem B4880807 : Blo 1283960 4880807 := bstep (se 1 (by rfl) ⟨3660605, by rfl⟩ : syracuseStep 4880807 = 7321211) B7321211
theorem B1284603 : Blo 1283960 1284603 := bstep (se 1 (by rfl) ⟨963452, by rfl⟩ : syracuseStep 1284603 = 1926905) B1926905
theorem B2890259 : Blo 1283960 2890259 := bstep (se 1 (by rfl) ⟨2167694, by rfl⟩ : syracuseStep 2890259 = 4335389) B4335389
theorem B1284671 : Blo 1283960 1284671 := bstep (se 1 (by rfl) ⟨963503, by rfl⟩ : syracuseStep 1284671 = 1927007) B1927007
theorem B3963455 : Blo 1283960 3963455 := bstep (se 1 (by rfl) ⟨2972591, by rfl⟩ : syracuseStep 3963455 = 5945183) B5945183
theorem B1284679 : Blo 1283960 1284679 := bstep (se 1 (by rfl) ⟨963509, by rfl⟩ : syracuseStep 1284679 = 1927019) B1927019
theorem B2890313 : Blo 1283960 2890313 := bstep (se 2 (by rfl) ⟨1083867, by rfl⟩ : syracuseStep 2890313 = 2167735) B2167735
theorem B20855369 : Blo 1283960 20855369 := bstep (se 2 (by rfl) ⟨7820763, by rfl⟩ : syracuseStep 20855369 = 15641527) B15641527
theorem B1284831 : Blo 1283960 1284831 := bstep (se 1 (by rfl) ⟨963623, by rfl⟩ : syracuseStep 1284831 = 1927247) B1927247
theorem B1284911 : Blo 1283960 1284911 := bstep (se 1 (by rfl) ⟨963683, by rfl⟩ : syracuseStep 1284911 = 1927367) B1927367
theorem B2169679 : Blo 1283960 2169679 := bstep (se 1 (by rfl) ⟨1627259, by rfl⟩ : syracuseStep 2169679 = 3254519) B3254519
theorem B3251087 : Blo 1283960 3251087 := bstep (se 1 (by rfl) ⟨2438315, by rfl⟩ : syracuseStep 3251087 = 4876631) B4876631
theorem B1285019 : Blo 1283960 1285019 := bstep (se 1 (by rfl) ⟨963764, by rfl⟩ : syracuseStep 1285019 = 1927529) B1927529
theorem B9763739 : Blo 1283960 9763739 := bstep (se 1 (by rfl) ⟨7322804, by rfl⟩ : syracuseStep 9763739 = 14645609) B14645609
theorem B4881323 : Blo 1283960 4881323 := bstep (se 1 (by rfl) ⟨3660992, by rfl⟩ : syracuseStep 4881323 = 7321985) B7321985
theorem B1285071 : Blo 1283960 1285071 := bstep (se 1 (by rfl) ⟨963803, by rfl⟩ : syracuseStep 1285071 = 1927607) B1927607
theorem B2890727 : Blo 1283960 2890727 := bstep (se 1 (by rfl) ⟨2168045, by rfl⟩ : syracuseStep 2890727 = 4336091) B4336091
theorem B1285095 : Blo 1283960 1285095 := bstep (se 1 (by rfl) ⟨963821, by rfl⟩ : syracuseStep 1285095 = 1927643) B1927643
theorem B1981673 : Blo 1283960 1981673 := bstep (se 2 (by rfl) ⟨743127, by rfl⟩ : syracuseStep 1981673 = 1486255) B1486255
theorem B1285407 : Blo 1283960 1285407 := bstep (se 1 (by rfl) ⟨964055, by rfl⟩ : syracuseStep 1285407 = 1928111) B1928111
theorem B12524867 : Blo 1283960 12524867 := bstep (se 1 (by rfl) ⟨9393650, by rfl⟩ : syracuseStep 12524867 = 18787301) B18787301
theorem B1285467 : Blo 1283960 1285467 := bstep (se 1 (by rfl) ⟨964100, by rfl⟩ : syracuseStep 1285467 = 1928201) B1928201
theorem B2891105 : Blo 1283960 2891105 := bstep (se 2 (by rfl) ⟨1084164, by rfl⟩ : syracuseStep 2891105 = 2168329) B2168329
theorem B1285487 : Blo 1283960 1285487 := bstep (se 1 (by rfl) ⟨964115, by rfl⟩ : syracuseStep 1285487 = 1928231) B1928231
theorem B1285543 : Blo 1283960 1285543 := bstep (se 1 (by rfl) ⟨964157, by rfl⟩ : syracuseStep 1285543 = 1928315) B1928315
theorem B2891195 : Blo 1283960 2891195 := bstep (se 1 (by rfl) ⟨2168396, by rfl⟩ : syracuseStep 2891195 = 4336793) B4336793
theorem B1285627 : Blo 1283960 1285627 := bstep (se 1 (by rfl) ⟨964220, by rfl⟩ : syracuseStep 1285627 = 1928441) B1928441
theorem B2891321 : Blo 1283960 2891321 := bstep (se 2 (by rfl) ⟨1084245, by rfl⟩ : syracuseStep 2891321 = 2168491) B2168491
theorem B1285695 : Blo 1283960 1285695 := bstep (se 1 (by rfl) ⟨964271, by rfl⟩ : syracuseStep 1285695 = 1928543) B1928543
theorem B1285703 : Blo 1283960 1285703 := bstep (se 1 (by rfl) ⟨964277, by rfl⟩ : syracuseStep 1285703 = 1928555) B1928555
theorem B13180499 : Blo 1283960 13180499 := bstep (se 1 (by rfl) ⟨9885374, by rfl⟩ : syracuseStep 13180499 = 19770749) B19770749
theorem B6176351 : Blo 1283960 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B6176465 : Blo 1283960 6176465 := bstep (se 2 (by rfl) ⟨2316174, by rfl⟩ : syracuseStep 6176465 = 4632349) B4632349
theorem B1285855 : Blo 1283960 1285855 := bstep (se 1 (by rfl) ⟨964391, by rfl⟩ : syracuseStep 1285855 = 1928783) B1928783
theorem B3251947 : Blo 1283960 3251947 := bstep (se 1 (by rfl) ⟨2438960, by rfl⟩ : syracuseStep 3251947 = 4877921) B4877921
theorem B5865227 : Blo 1283960 5865227 := bstep (se 1 (by rfl) ⟨4398920, by rfl⟩ : syracuseStep 5865227 = 8797841) B8797841
theorem B1285935 : Blo 1283960 1285935 := bstep (se 1 (by rfl) ⟨964451, by rfl⟩ : syracuseStep 1285935 = 1928903) B1928903
theorem B1785655 : Blo 1283960 1785655 := bstep (se 1 (by rfl) ⟨1339241, by rfl⟩ : syracuseStep 1785655 = 2678483) B2678483
theorem B6504299 : Blo 1283960 6504299 := bstep (se 1 (by rfl) ⟨4878224, by rfl⟩ : syracuseStep 6504299 = 9756449) B9756449
theorem B1302427 : Blo 1283960 1302427 := bstep (se 1 (by rfl) ⟨976820, by rfl⟩ : syracuseStep 1302427 = 1953641) B1953641
theorem B4333607 : Blo 1283960 4333607 := bstep (se 1 (by rfl) ⟨3250205, by rfl⟩ : syracuseStep 4333607 = 6500411) B6500411
theorem B15843539 : Blo 1283960 15843539 := bstep (se 1 (by rfl) ⟨11882654, by rfl⟩ : syracuseStep 15843539 = 23765309) B23765309
theorem B3907865 : Blo 1283960 3907865 := bstep (se 2 (by rfl) ⟨1465449, by rfl⟩ : syracuseStep 3907865 = 2930899) B2930899
theorem B1319375 : Blo 1283960 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B2892239 : Blo 1283960 2892239 := bstep (se 1 (by rfl) ⟨2169179, by rfl⟩ : syracuseStep 2892239 = 4338359) B4338359
theorem B9257435 : Blo 1283960 9257435 := bstep (se 1 (by rfl) ⟨6943076, by rfl⟩ : syracuseStep 9257435 = 13886153) B13886153
theorem B3908159 : Blo 1283960 3908159 := bstep (se 1 (by rfl) ⟨2931119, by rfl⟩ : syracuseStep 3908159 = 5862239) B5862239
theorem B4334255 : Blo 1283960 4334255 := bstep (se 1 (by rfl) ⟨3250691, by rfl⟩ : syracuseStep 4334255 = 6501383) B6501383
theorem B1925999 : Blo 1283960 1925999 := bstep (se 1 (by rfl) ⟨1444499, by rfl⟩ : syracuseStep 1925999 = 2888999) B2888999
theorem B4334579 : Blo 1283960 4334579 := bstep (se 1 (by rfl) ⟨3250934, by rfl⟩ : syracuseStep 4334579 = 6501869) B6501869
theorem B4113467 : Blo 1283960 4113467 := bstep (se 1 (by rfl) ⟨3085100, by rfl⟩ : syracuseStep 4113467 = 6170201) B6170201
theorem B2892905 : Blo 1283960 2892905 := bstep (se 2 (by rfl) ⟨1084839, by rfl⟩ : syracuseStep 2892905 = 2169679) B2169679
theorem B1926251 : Blo 1283960 1926251 := bstep (se 1 (by rfl) ⟨1444688, by rfl⟩ : syracuseStep 1926251 = 2889377) B2889377
theorem B18523343 : Blo 1283960 18523343 := bstep (se 1 (by rfl) ⟨13892507, by rfl⟩ : syracuseStep 18523343 = 27785015) B27785015
theorem B4113737 : Blo 1283960 4113737 := bstep (se 2 (by rfl) ⟨1542651, by rfl⟩ : syracuseStep 4113737 = 3085303) B3085303
theorem B1926491 : Blo 1283960 1926491 := bstep (se 1 (by rfl) ⟨1444868, by rfl⟩ : syracuseStep 1926491 = 2889737) B2889737
theorem B3089771 : Blo 1283960 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B3474859 : Blo 1283960 3474859 := bstep (se 1 (by rfl) ⟨2606144, by rfl⟩ : syracuseStep 3474859 = 5212289) B5212289
theorem B3253679 : Blo 1283960 3253679 := bstep (se 1 (by rfl) ⟨2440259, by rfl⟩ : syracuseStep 3253679 = 4880519) B4880519
theorem B4335119 : Blo 1283960 4335119 := bstep (se 1 (by rfl) ⟨3251339, by rfl⟩ : syracuseStep 4335119 = 6502679) B6502679
theorem B13190681 : Blo 1283960 13190681 := bstep (se 2 (by rfl) ⟨4946505, by rfl⟩ : syracuseStep 13190681 = 9893011) B9893011
theorem B14632487 : Blo 1283960 14632487 := bstep (se 1 (by rfl) ⟨10974365, by rfl⟩ : syracuseStep 14632487 = 21948731) B21948731
theorem B1828423 : Blo 1283960 1828423 := bstep (se 1 (by rfl) ⟨1371317, by rfl⟩ : syracuseStep 1828423 = 2742635) B2742635
theorem B1926767 : Blo 1283960 1926767 := bstep (se 1 (by rfl) ⟨1445075, by rfl⟩ : syracuseStep 1926767 = 2890151) B2890151
theorem B3253871 : Blo 1283960 3253871 := bstep (se 1 (by rfl) ⟨2440403, by rfl⟩ : syracuseStep 3253871 = 4880807) B4880807
theorem B9750131 : Blo 1283960 9750131 := bstep (se 1 (by rfl) ⟨7312598, by rfl⟩ : syracuseStep 9750131 = 14625197) B14625197
theorem B4114081 : Blo 1283960 4114081 := bstep (se 2 (by rfl) ⟨1542780, by rfl⟩ : syracuseStep 4114081 = 3085561) B3085561
theorem B1926839 : Blo 1283960 1926839 := bstep (se 1 (by rfl) ⟨1445129, by rfl⟩ : syracuseStep 1926839 = 2890259) B2890259
theorem B1926875 : Blo 1283960 1926875 := bstep (se 1 (by rfl) ⟨1445156, by rfl⟩ : syracuseStep 1926875 = 2890313) B2890313
theorem B13903579 : Blo 1283960 13903579 := bstep (se 1 (by rfl) ⟨10427684, by rfl⟩ : syracuseStep 13903579 = 20855369) B20855369
theorem B2197243 : Blo 1283960 2197243 := bstep (se 1 (by rfl) ⟨1647932, by rfl⟩ : syracuseStep 2197243 = 3295865) B3295865
theorem B15632189 : Blo 1283960 15632189 := bstep (se 3 (by rfl) ⟨2931035, by rfl⟩ : syracuseStep 15632189 = 5862071) B5862071
theorem B14845801 : Blo 1283960 14845801 := bstep (se 2 (by rfl) ⟨5567175, by rfl⟩ : syracuseStep 14845801 = 11134351) B11134351
theorem B1927049 : Blo 1283960 1927049 := bstep (se 2 (by rfl) ⟨722643, by rfl⟩ : syracuseStep 1927049 = 1445287) B1445287
theorem B3254215 : Blo 1283960 3254215 := bstep (se 1 (by rfl) ⟨2440661, by rfl⟩ : syracuseStep 3254215 = 4881323) B4881323
theorem B1927151 : Blo 1283960 1927151 := bstep (se 1 (by rfl) ⟨1445363, by rfl⟩ : syracuseStep 1927151 = 2890727) B2890727
theorem B1321115 : Blo 1283960 1321115 := bstep (se 1 (by rfl) ⟨990836, by rfl⟩ : syracuseStep 1321115 = 1981673) B1981673
theorem B8349911 : Blo 1283960 8349911 := bstep (se 1 (by rfl) ⟨6262433, by rfl⟩ : syracuseStep 8349911 = 12524867) B12524867
theorem B1927403 : Blo 1283960 1927403 := bstep (se 1 (by rfl) ⟨1445552, by rfl⟩ : syracuseStep 1927403 = 2891105) B2891105
theorem B6260971 : Blo 1283960 6260971 := bstep (se 1 (by rfl) ⟨4695728, by rfl⟩ : syracuseStep 6260971 = 9391457) B9391457
theorem B1927463 : Blo 1283960 1927463 := bstep (se 1 (by rfl) ⟨1445597, by rfl⟩ : syracuseStep 1927463 = 2891195) B2891195
theorem B4335929 : Blo 1283960 4335929 := bstep (se 2 (by rfl) ⟨1625973, by rfl⟩ : syracuseStep 4335929 = 3251947) B3251947
theorem B1927547 : Blo 1283960 1927547 := bstep (se 1 (by rfl) ⟨1445660, by rfl⟩ : syracuseStep 1927547 = 2891321) B2891321
theorem B281373101 : Blo 1283960 281373101 := bstep (se 3 (by rfl) ⟨52757456, by rfl⟩ : syracuseStep 281373101 = 105514913) B105514913
theorem B3910151 : Blo 1283960 3910151 := bstep (se 1 (by rfl) ⟨2932613, by rfl⟩ : syracuseStep 3910151 = 5865227) B5865227
theorem B3295775 : Blo 1283960 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B4336199 : Blo 1283960 4336199 := bstep (se 1 (by rfl) ⟨3252149, by rfl⟩ : syracuseStep 4336199 = 6504299) B6504299
theorem B1927817 : Blo 1283960 1927817 := bstep (se 2 (by rfl) ⟨722931, by rfl⟩ : syracuseStep 1927817 = 1445863) B1445863
theorem B8235695 : Blo 1283960 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B1927991 : Blo 1283960 1927991 := bstep (se 1 (by rfl) ⟨1445993, by rfl⟩ : syracuseStep 1927991 = 2891987) B2891987
theorem B1928027 : Blo 1283960 1928027 := bstep (se 1 (by rfl) ⟨1446020, by rfl⟩ : syracuseStep 1928027 = 2892041) B2892041
theorem B12348395 : Blo 1283960 12348395 := bstep (se 1 (by rfl) ⟨9261296, by rfl⟩ : syracuseStep 12348395 = 18522593) B18522593
theorem B1928171 : Blo 1283960 1928171 := bstep (se 1 (by rfl) ⟨1446128, by rfl⟩ : syracuseStep 1928171 = 2892257) B2892257
theorem B3656801 : Blo 1283960 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B1928375 : Blo 1283960 1928375 := bstep (se 1 (by rfl) ⟨1446281, by rfl⟩ : syracuseStep 1928375 = 2892563) B2892563
theorem B3656927 : Blo 1283960 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B16698611 : Blo 1283960 16698611 := bstep (se 1 (by rfl) ⟨12523958, by rfl⟩ : syracuseStep 16698611 = 25047917) B25047917
theorem B7318795 : Blo 1283960 7318795 := bstep (se 1 (by rfl) ⟨5489096, by rfl⟩ : syracuseStep 7318795 = 10978193) B10978193
theorem B1830223 : Blo 1283960 1830223 := bstep (se 1 (by rfl) ⟨1372667, by rfl⟩ : syracuseStep 1830223 = 2745335) B2745335
theorem B1928615 : Blo 1283960 1928615 := bstep (se 1 (by rfl) ⟨1446461, by rfl⟩ : syracuseStep 1928615 = 2892923) B2892923
theorem B3657143 : Blo 1283960 3657143 := bstep (se 1 (by rfl) ⟨2742857, by rfl⟩ : syracuseStep 3657143 = 5485715) B5485715
theorem B1543655 : Blo 1283960 1543655 := bstep (se 1 (by rfl) ⟨1157741, by rfl⟩ : syracuseStep 1543655 = 2315483) B2315483
theorem B1928699 : Blo 1283960 1928699 := bstep (se 1 (by rfl) ⟨1446524, by rfl⟩ : syracuseStep 1928699 = 2893049) B2893049
theorem B4337225 : Blo 1283960 4337225 := bstep (se 2 (by rfl) ⟨1626459, by rfl⟩ : syracuseStep 4337225 = 3252919) B3252919
theorem B1445467 : Blo 1283960 1445467 := bstep (se 1 (by rfl) ⟨1084100, by rfl⟩ : syracuseStep 1445467 = 2168201) B2168201
theorem B1928795 : Blo 1283960 1928795 := bstep (se 1 (by rfl) ⟨1446596, by rfl⟩ : syracuseStep 1928795 = 2893193) B2893193
theorem B4632221 : Blo 1283960 4632221 := bstep (se 3 (by rfl) ⟨868541, by rfl⟩ : syracuseStep 4632221 = 1737083) B1737083
theorem B1928879 : Blo 1283960 1928879 := bstep (se 1 (by rfl) ⟨1446659, by rfl⟩ : syracuseStep 1928879 = 2893319) B2893319
theorem B26382023 : Blo 1283960 26382023 := bstep (se 1 (by rfl) ⟨19786517, by rfl⟩ : syracuseStep 26382023 = 39573035) B39573035
theorem B1445755 : Blo 1283960 1445755 := bstep (se 1 (by rfl) ⟨1084316, by rfl⟩ : syracuseStep 1445755 = 2168633) B2168633
theorem B9523493 : Blo 1283960 9523493 := bstep (se 4 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 9523493 = 1785655) B1785655
theorem B2642303 : Blo 1283960 2642303 := bstep (se 1 (by rfl) ⟨1981727, by rfl⟩ : syracuseStep 2642303 = 3963455) B3963455
theorem B6943247 : Blo 1283960 6943247 := bstep (se 1 (by rfl) ⟨5207435, by rfl⟩ : syracuseStep 6943247 = 10414871) B10414871
theorem B4878863 : Blo 1283960 4878863 := bstep (se 1 (by rfl) ⟨3659147, by rfl⟩ : syracuseStep 4878863 = 7318295) B7318295
theorem B2437715 : Blo 1283960 2437715 := bstep (se 1 (by rfl) ⟨1828286, by rfl⟩ : syracuseStep 2437715 = 3656573) B3656573
theorem B6943315 : Blo 1283960 6943315 := bstep (se 1 (by rfl) ⟨5207486, by rfl⟩ : syracuseStep 6943315 = 10414973) B10414973
theorem B2167391 : Blo 1283960 2167391 := bstep (se 1 (by rfl) ⟨1625543, by rfl⟩ : syracuseStep 2167391 = 3251087) B3251087
theorem B6509159 : Blo 1283960 6509159 := bstep (se 1 (by rfl) ⟨4881869, by rfl⟩ : syracuseStep 6509159 = 9763739) B9763739
theorem B4338683 : Blo 1283960 4338683 := bstep (se 1 (by rfl) ⟨3254012, by rfl⟩ : syracuseStep 4338683 = 6508025) B6508025
theorem B8786999 : Blo 1283960 8786999 := bstep (se 1 (by rfl) ⟨6590249, by rfl⟩ : syracuseStep 8786999 = 13180499) B13180499
theorem B4117567 : Blo 1283960 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B4117643 : Blo 1283960 4117643 := bstep (se 1 (by rfl) ⟨3088232, by rfl⟩ : syracuseStep 4117643 = 6176465) B6176465
theorem B4338899 : Blo 1283960 4338899 := bstep (se 1 (by rfl) ⟨3254174, by rfl⟩ : syracuseStep 4338899 = 6508349) B6508349
theorem B28161299 : Blo 1283960 28161299 := bstep (se 1 (by rfl) ⟨21120974, by rfl⟩ : syracuseStep 28161299 = 42241949) B42241949
theorem B4339169 : Blo 1283960 4339169 := bstep (se 2 (by rfl) ⟨1627188, by rfl⟩ : syracuseStep 4339169 = 3254377) B3254377
theorem B2889287 : Blo 1283960 2889287 := bstep (se 1 (by rfl) ⟨2166965, by rfl⟩ : syracuseStep 2889287 = 4333931) B4333931
theorem B8230571 : Blo 1283960 8230571 := bstep (se 1 (by rfl) ⟨6172928, by rfl⟩ : syracuseStep 8230571 = 12345857) B12345857
theorem B2438839 : Blo 1283960 2438839 := bstep (se 1 (by rfl) ⟨1829129, by rfl⟩ : syracuseStep 2438839 = 3658259) B3658259
theorem B2889467 : Blo 1283960 2889467 := bstep (se 1 (by rfl) ⟨2167100, by rfl⟩ : syracuseStep 2889467 = 4334201) B4334201
theorem B5486399 : Blo 1283960 5486399 := bstep (se 1 (by rfl) ⟨4114799, by rfl⟩ : syracuseStep 5486399 = 8229599) B8229599
theorem B23754653 : Blo 1283960 23754653 := bstep (se 3 (by rfl) ⟨4453997, by rfl⟩ : syracuseStep 23754653 = 8907995) B8907995
theorem B2439143 : Blo 1283960 2439143 := bstep (se 1 (by rfl) ⟨1829357, by rfl⟩ : syracuseStep 2439143 = 3658715) B3658715
theorem B1284079 : Blo 1283960 1284079 := bstep (se 1 (by rfl) ⟨963059, by rfl⟩ : syracuseStep 1284079 = 1926119) B1926119
theorem B2168815 : Blo 1283960 2168815 := bstep (se 1 (by rfl) ⟨1626611, by rfl⟩ : syracuseStep 2168815 = 3253223) B3253223
theorem B21944357 : Blo 1283960 21944357 := bstep (se 4 (by rfl) ⟨2057283, by rfl⟩ : syracuseStep 21944357 = 4114567) B4114567
theorem B4339817 : Blo 1283960 4339817 := bstep (se 2 (by rfl) ⟨1627431, by rfl⟩ : syracuseStep 4339817 = 3254863) B3254863
theorem B1284251 : Blo 1283960 1284251 := bstep (se 1 (by rfl) ⟨963188, by rfl⟩ : syracuseStep 1284251 = 1926377) B1926377
theorem B1284287 : Blo 1283960 1284287 := bstep (se 1 (by rfl) ⟨963215, by rfl⟩ : syracuseStep 1284287 = 1926431) B1926431
theorem B2169065 : Blo 1283960 2169065 := bstep (se 2 (by rfl) ⟨813399, by rfl⟩ : syracuseStep 2169065 = 1626799) B1626799
theorem B2316521 : Blo 1283960 2316521 := bstep (se 2 (by rfl) ⟨868695, by rfl⟩ : syracuseStep 2316521 = 1737391) B1737391
theorem B4118771 : Blo 1283960 4118771 := bstep (se 1 (by rfl) ⟨3089078, by rfl⟩ : syracuseStep 4118771 = 6178157) B6178157
theorem B3250439 : Blo 1283960 3250439 := bstep (se 1 (by rfl) ⟨2437829, by rfl⟩ : syracuseStep 3250439 = 4875659) B4875659
theorem B2890025 : Blo 1283960 2890025 := bstep (se 2 (by rfl) ⟨1083759, by rfl⟩ : syracuseStep 2890025 = 2167519) B2167519
theorem B1284399 : Blo 1283960 1284399 := bstep (se 1 (by rfl) ⟨963299, by rfl⟩ : syracuseStep 1284399 = 1926599) B1926599
theorem B5282171 : Blo 1283960 5282171 := bstep (se 1 (by rfl) ⟨3961628, by rfl⟩ : syracuseStep 5282171 = 7923257) B7923257
theorem B15628727 : Blo 1283960 15628727 := bstep (se 1 (by rfl) ⟨11721545, by rfl⟩ : syracuseStep 15628727 = 23443091) B23443091
theorem B1284635 : Blo 1283960 1284635 := bstep (se 1 (by rfl) ⟨963476, by rfl⟩ : syracuseStep 1284635 = 1926953) B1926953
theorem B1284639 : Blo 1283960 1284639 := bstep (se 1 (by rfl) ⟨963479, by rfl⟩ : syracuseStep 1284639 = 1926959) B1926959
theorem B10419023 : Blo 1283960 10419023 := bstep (se 1 (by rfl) ⟨7814267, by rfl⟩ : syracuseStep 10419023 = 15628535) B15628535
theorem B1284955 : Blo 1283960 1284955 := bstep (se 1 (by rfl) ⟨963716, by rfl⟩ : syracuseStep 1284955 = 1927433) B1927433
theorem B2890601 : Blo 1283960 2890601 := bstep (se 2 (by rfl) ⟨1083975, by rfl⟩ : syracuseStep 2890601 = 2167951) B2167951
theorem B2890655 : Blo 1283960 2890655 := bstep (se 1 (by rfl) ⟨2167991, by rfl⟩ : syracuseStep 2890655 = 4335983) B4335983
theorem B1285023 : Blo 1283960 1285023 := bstep (se 1 (by rfl) ⟨963767, by rfl⟩ : syracuseStep 1285023 = 1927535) B1927535
theorem B1285167 : Blo 1283960 1285167 := bstep (se 1 (by rfl) ⟨963875, by rfl⟩ : syracuseStep 1285167 = 1927751) B1927751
theorem B1285191 : Blo 1283960 1285191 := bstep (se 1 (by rfl) ⟨963893, by rfl⟩ : syracuseStep 1285191 = 1927787) B1927787
theorem B4398209 : Blo 1283960 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B1285343 : Blo 1283960 1285343 := bstep (se 1 (by rfl) ⟨964007, by rfl⟩ : syracuseStep 1285343 = 1928015) B1928015
theorem B3251623 : Blo 1283960 3251623 := bstep (se 1 (by rfl) ⟨2438717, by rfl⟩ : syracuseStep 3251623 = 4877435) B4877435
theorem B1285607 : Blo 1283960 1285607 := bstep (se 1 (by rfl) ⟨964205, by rfl⟩ : syracuseStep 1285607 = 1928411) B1928411
theorem B1285723 : Blo 1283960 1285723 := bstep (se 1 (by rfl) ⟨964292, by rfl⟩ : syracuseStep 1285723 = 1928585) B1928585
theorem B2743951 : Blo 1283960 2743951 := bstep (se 1 (by rfl) ⟨2057963, by rfl⟩ : syracuseStep 2743951 = 4115927) B4115927
theorem B2891591 : Blo 1283960 2891591 := bstep (se 1 (by rfl) ⟨2168693, by rfl⟩ : syracuseStep 2891591 = 4337387) B4337387
theorem B1285959 : Blo 1283960 1285959 := bstep (se 1 (by rfl) ⟨964469, by rfl⟩ : syracuseStep 1285959 = 1928939) B1928939
theorem B1736569 : Blo 1283960 1736569 := bstep (se 2 (by rfl) ⟨651213, by rfl⟩ : syracuseStep 1736569 = 1302427) B1302427
theorem B3661757 : Blo 1283960 3661757 := bstep (se 3 (by rfl) ⟨686579, by rfl⟩ : syracuseStep 3661757 = 1373159) B1373159
theorem B6348995 : Blo 1283960 6348995 := bstep (se 1 (by rfl) ⟨4761746, by rfl⟩ : syracuseStep 6348995 = 9523493) B9523493
theorem B1761535 : Blo 1283960 1761535 := bstep (se 1 (by rfl) ⟨1321151, by rfl⟩ : syracuseStep 1761535 = 2642303) B2642303
theorem B8347961 : Blo 1283960 8347961 := bstep (se 2 (by rfl) ⟨3130485, by rfl⟩ : syracuseStep 8347961 = 6260971) B6260971
theorem B4628831 : Blo 1283960 4628831 := bstep (se 1 (by rfl) ⟨3471623, by rfl⟩ : syracuseStep 4628831 = 6943247) B6943247
theorem B3252575 : Blo 1283960 3252575 := bstep (se 1 (by rfl) ⟨2439431, by rfl⟩ : syracuseStep 3252575 = 4878863) B4878863
theorem B2605439 : Blo 1283960 2605439 := bstep (se 1 (by rfl) ⟨1954079, by rfl⟩ : syracuseStep 2605439 = 3908159) B3908159
theorem B3522973 : Blo 1283960 3522973 := bstep (se 3 (by rfl) ⟨660557, by rfl⟩ : syracuseStep 3522973 = 1321115) B1321115
theorem B2892455 : Blo 1283960 2892455 := bstep (se 1 (by rfl) ⟨2169341, by rfl⟩ : syracuseStep 2892455 = 4338683) B4338683
theorem B10420973 : Blo 1283960 10420973 := bstep (se 3 (by rfl) ⟨1953932, by rfl⟩ : syracuseStep 10420973 = 3907865) B3907865
theorem B2745095 : Blo 1283960 2745095 := bstep (se 1 (by rfl) ⟨2058821, by rfl⟩ : syracuseStep 2745095 = 4117643) B4117643
theorem B9257753 : Blo 1283960 9257753 := bstep (se 2 (by rfl) ⟨3471657, by rfl⟩ : syracuseStep 9257753 = 6943315) B6943315
theorem B2892599 : Blo 1283960 2892599 := bstep (se 1 (by rfl) ⟨2169449, by rfl⟩ : syracuseStep 2892599 = 4338899) B4338899
theorem B2892779 : Blo 1283960 2892779 := bstep (se 1 (by rfl) ⟨2169584, by rfl⟩ : syracuseStep 2892779 = 4339169) B4339169
theorem B1926191 : Blo 1283960 1926191 := bstep (se 1 (by rfl) ⟨1444643, by rfl⟩ : syracuseStep 1926191 = 2889287) B2889287
theorem B1926311 : Blo 1283960 1926311 := bstep (se 1 (by rfl) ⟨1444733, by rfl⟩ : syracuseStep 1926311 = 2889467) B2889467
theorem B10421459 : Blo 1283960 10421459 := bstep (se 1 (by rfl) ⟨7816094, by rfl⟩ : syracuseStep 10421459 = 15632189) B15632189
theorem B15836435 : Blo 1283960 15836435 := bstep (se 1 (by rfl) ⟨11877326, by rfl⟩ : syracuseStep 15836435 = 23754653) B23754653
theorem B2893211 : Blo 1283960 2893211 := bstep (se 1 (by rfl) ⟨2169908, by rfl⟩ : syracuseStep 2893211 = 4339817) B4339817
theorem B5490089 : Blo 1283960 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B2745847 : Blo 1283960 2745847 := bstep (se 1 (by rfl) ⟨2059385, by rfl⟩ : syracuseStep 2745847 = 4118771) B4118771
theorem B1926683 : Blo 1283960 1926683 := bstep (se 1 (by rfl) ⟨1445012, by rfl⟩ : syracuseStep 1926683 = 2890025) B2890025
theorem B187582067 : Blo 1283960 187582067 := bstep (se 1 (by rfl) ⟨140686550, by rfl⟩ : syracuseStep 187582067 = 281373101) B281373101
theorem B9758393 : Blo 1283960 9758393 := bstep (se 2 (by rfl) ⟨3659397, by rfl⟩ : syracuseStep 9758393 = 7318795) B7318795
theorem B4335497 : Blo 1283960 4335497 := bstep (se 2 (by rfl) ⟨1625811, by rfl⟩ : syracuseStep 4335497 = 3251623) B3251623
theorem B1927067 : Blo 1283960 1927067 := bstep (se 1 (by rfl) ⟨1445300, by rfl⟩ : syracuseStep 1927067 = 2890601) B2890601
theorem B1927103 : Blo 1283960 1927103 := bstep (se 1 (by rfl) ⟨1445327, by rfl⟩ : syracuseStep 1927103 = 2890655) B2890655
theorem B1927289 : Blo 1283960 1927289 := bstep (se 2 (by rfl) ⟨722733, by rfl⟩ : syracuseStep 1927289 = 1445467) B1445467
theorem B19794401 : Blo 1283960 19794401 := bstep (se 2 (by rfl) ⟨7422900, by rfl⟩ : syracuseStep 19794401 = 14845801) B14845801
theorem B1927673 : Blo 1283960 1927673 := bstep (se 2 (by rfl) ⟨722877, by rfl⟩ : syracuseStep 1927673 = 1445755) B1445755
theorem B1927727 : Blo 1283960 1927727 := bstep (se 1 (by rfl) ⟨1445795, by rfl⟩ : syracuseStep 1927727 = 2891591) B2891591
theorem B23431997 : Blo 1283960 23431997 := bstep (se 3 (by rfl) ⟨4393499, by rfl⟩ : syracuseStep 23431997 = 8786999) B8786999
theorem B1928159 : Blo 1283960 1928159 := bstep (se 1 (by rfl) ⟨1446119, by rfl⟩ : syracuseStep 1928159 = 2892239) B2892239
theorem B6171623 : Blo 1283960 6171623 := bstep (se 1 (by rfl) ⟨4628717, by rfl⟩ : syracuseStep 6171623 = 9257435) B9257435
theorem B9751589 : Blo 1283960 9751589 := bstep (se 4 (by rfl) ⟨914211, by rfl⟩ : syracuseStep 9751589 = 1828423) B1828423
theorem B1444927 : Blo 1283960 1444927 := bstep (se 1 (by rfl) ⟨1083695, by rfl⟩ : syracuseStep 1444927 = 2167391) B2167391
theorem B42249437 : Blo 1283960 42249437 := bstep (se 3 (by rfl) ⟨7921769, by rfl⟩ : syracuseStep 42249437 = 15843539) B15843539
theorem B1928603 : Blo 1283960 1928603 := bstep (se 1 (by rfl) ⟨1446452, by rfl⟩ : syracuseStep 1928603 = 2892905) B2892905
theorem B12348895 : Blo 1283960 12348895 := bstep (se 1 (by rfl) ⟨9261671, by rfl⟩ : syracuseStep 12348895 = 18523343) B18523343
theorem B2059847 : Blo 1283960 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B8793787 : Blo 1283960 8793787 := bstep (se 1 (by rfl) ⟨6595340, by rfl⟩ : syracuseStep 8793787 = 13190681) B13190681
theorem B6500087 : Blo 1283960 6500087 := bstep (se 1 (by rfl) ⟨4875065, by rfl⟩ : syracuseStep 6500087 = 9750131) B9750131
theorem B3518333 : Blo 1283960 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B3657599 : Blo 1283960 3657599 := bstep (se 1 (by rfl) ⟨2743199, by rfl⟩ : syracuseStep 3657599 = 5486399) B5486399
theorem B4116413 : Blo 1283960 4116413 := bstep (se 3 (by rfl) ⟨771827, by rfl⟩ : syracuseStep 4116413 = 1543655) B1543655
theorem B1626095 : Blo 1283960 1626095 := bstep (se 1 (by rfl) ⟨1219571, by rfl⟩ : syracuseStep 1626095 = 2439143) B2439143
theorem B5566607 : Blo 1283960 5566607 := bstep (se 1 (by rfl) ⟨4174955, by rfl⟩ : syracuseStep 5566607 = 8349911) B8349911
theorem B1446043 : Blo 1283960 1446043 := bstep (se 1 (by rfl) ⟨1084532, by rfl⟩ : syracuseStep 1446043 = 2169065) B2169065
theorem B1544347 : Blo 1283960 1544347 := bstep (se 1 (by rfl) ⟨1158260, by rfl⟩ : syracuseStep 1544347 = 2316521) B2316521
theorem B2166959 : Blo 1283960 2166959 := bstep (se 1 (by rfl) ⟨1625219, by rfl⟩ : syracuseStep 2166959 = 3250439) B3250439
theorem B6500573 : Blo 1283960 6500573 := bstep (se 3 (by rfl) ⟨1218857, by rfl⟩ : syracuseStep 6500573 = 2437715) B2437715
theorem B4633145 : Blo 1283960 4633145 := bstep (se 2 (by rfl) ⟨1737429, by rfl⟩ : syracuseStep 4633145 = 3474859) B3474859
theorem B9261701 : Blo 1283960 9261701 := bstep (se 4 (by rfl) ⟨868284, by rfl⟩ : syracuseStep 9261701 = 1736569) B1736569
theorem B2437867 : Blo 1283960 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B2437951 : Blo 1283960 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B3658601 : Blo 1283960 3658601 := bstep (se 2 (by rfl) ⟨1371975, by rfl⟩ : syracuseStep 3658601 = 2743951) B2743951
theorem B5485441 : Blo 1283960 5485441 := bstep (se 2 (by rfl) ⟨2057040, by rfl⟩ : syracuseStep 5485441 = 4114081) B4114081
theorem B2438095 : Blo 1283960 2438095 := bstep (se 1 (by rfl) ⟨1828571, by rfl⟩ : syracuseStep 2438095 = 3657143) B3657143
theorem B2929657 : Blo 1283960 2929657 := bstep (se 2 (by rfl) ⟨1098621, by rfl⟩ : syracuseStep 2929657 = 2197243) B2197243
theorem B4338953 : Blo 1283960 4338953 := bstep (se 2 (by rfl) ⟨1627107, by rfl⟩ : syracuseStep 4338953 = 3254215) B3254215
theorem B2889071 : Blo 1283960 2889071 := bstep (se 1 (by rfl) ⟨2166803, by rfl⟩ : syracuseStep 2889071 = 4333607) B4333607
theorem B4339439 : Blo 1283960 4339439 := bstep (se 1 (by rfl) ⟨3254579, by rfl⟩ : syracuseStep 4339439 = 6509159) B6509159
theorem B2889503 : Blo 1283960 2889503 := bstep (se 1 (by rfl) ⟨2167127, by rfl⟩ : syracuseStep 2889503 = 4334255) B4334255
theorem B1283999 : Blo 1283960 1283999 := bstep (se 1 (by rfl) ⟨962999, by rfl⟩ : syracuseStep 1283999 = 1925999) B1925999
theorem B2889719 : Blo 1283960 2889719 := bstep (se 1 (by rfl) ⟨2167289, by rfl⟩ : syracuseStep 2889719 = 4334579) B4334579
theorem B2742311 : Blo 1283960 2742311 := bstep (se 1 (by rfl) ⟨2056733, by rfl⟩ : syracuseStep 2742311 = 4113467) B4113467
theorem B1284167 : Blo 1283960 1284167 := bstep (se 1 (by rfl) ⟨963125, by rfl⟩ : syracuseStep 1284167 = 1926251) B1926251
theorem B18774199 : Blo 1283960 18774199 := bstep (se 1 (by rfl) ⟨14080649, by rfl⟩ : syracuseStep 18774199 = 28161299) B28161299
theorem B2742491 : Blo 1283960 2742491 := bstep (se 1 (by rfl) ⟨2056868, by rfl⟩ : syracuseStep 2742491 = 4113737) B4113737
theorem B1284327 : Blo 1283960 1284327 := bstep (se 1 (by rfl) ⟨963245, by rfl⟩ : syracuseStep 1284327 = 1926491) B1926491
theorem B2169119 : Blo 1283960 2169119 := bstep (se 1 (by rfl) ⟨1626839, by rfl⟩ : syracuseStep 2169119 = 3253679) B3253679
theorem B2890079 : Blo 1283960 2890079 := bstep (se 1 (by rfl) ⟨2167559, by rfl⟩ : syracuseStep 2890079 = 4335119) B4335119
theorem B9754991 : Blo 1283960 9754991 := bstep (se 1 (by rfl) ⟨7316243, by rfl⟩ : syracuseStep 9754991 = 14632487) B14632487
theorem B1284511 : Blo 1283960 1284511 := bstep (se 1 (by rfl) ⟨963383, by rfl⟩ : syracuseStep 1284511 = 1926767) B1926767
theorem B2169247 : Blo 1283960 2169247 := bstep (se 1 (by rfl) ⟨1626935, by rfl⟩ : syracuseStep 2169247 = 3253871) B3253871
theorem B5487047 : Blo 1283960 5487047 := bstep (se 1 (by rfl) ⟨4115285, by rfl⟩ : syracuseStep 5487047 = 8230571) B8230571
theorem B1284559 : Blo 1283960 1284559 := bstep (se 1 (by rfl) ⟨963419, by rfl⟩ : syracuseStep 1284559 = 1926839) B1926839
theorem B1284583 : Blo 1283960 1284583 := bstep (se 1 (by rfl) ⟨963437, by rfl⟩ : syracuseStep 1284583 = 1926875) B1926875
theorem B1284699 : Blo 1283960 1284699 := bstep (se 1 (by rfl) ⟨963524, by rfl⟩ : syracuseStep 1284699 = 1927049) B1927049
theorem B1284767 : Blo 1283960 1284767 := bstep (se 1 (by rfl) ⟨963575, by rfl⟩ : syracuseStep 1284767 = 1927151) B1927151
theorem B10427069 : Blo 1283960 10427069 := bstep (se 3 (by rfl) ⟨1955075, by rfl⟩ : syracuseStep 10427069 = 3910151) B3910151
theorem B14629571 : Blo 1283960 14629571 := bstep (se 1 (by rfl) ⟨10972178, by rfl⟩ : syracuseStep 14629571 = 21944357) B21944357
theorem B8788733 : Blo 1283960 8788733 := bstep (se 3 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 8788733 = 3295775) B3295775
theorem B1284935 : Blo 1283960 1284935 := bstep (se 1 (by rfl) ⟨963701, by rfl⟩ : syracuseStep 1284935 = 1927403) B1927403
theorem B1284975 : Blo 1283960 1284975 := bstep (se 1 (by rfl) ⟨963731, by rfl⟩ : syracuseStep 1284975 = 1927463) B1927463
theorem B2890619 : Blo 1283960 2890619 := bstep (se 1 (by rfl) ⟨2167964, by rfl⟩ : syracuseStep 2890619 = 4335929) B4335929
theorem B1285031 : Blo 1283960 1285031 := bstep (se 1 (by rfl) ⟨963773, by rfl⟩ : syracuseStep 1285031 = 1927547) B1927547
theorem B3521447 : Blo 1283960 3521447 := bstep (se 1 (by rfl) ⟨2641085, by rfl⟩ : syracuseStep 3521447 = 5282171) B5282171
theorem B10419151 : Blo 1283960 10419151 := bstep (se 1 (by rfl) ⟨7814363, by rfl⟩ : syracuseStep 10419151 = 15628727) B15628727
theorem B2890799 : Blo 1283960 2890799 := bstep (se 1 (by rfl) ⟨2168099, by rfl⟩ : syracuseStep 2890799 = 4336199) B4336199
theorem B1285211 : Blo 1283960 1285211 := bstep (se 1 (by rfl) ⟨963908, by rfl⟩ : syracuseStep 1285211 = 1927817) B1927817
theorem B2440297 : Blo 1283960 2440297 := bstep (se 2 (by rfl) ⟨915111, by rfl⟩ : syracuseStep 2440297 = 1830223) B1830223
theorem B21961853 : Blo 1283960 21961853 := bstep (se 3 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 21961853 = 8235695) B8235695
theorem B1285327 : Blo 1283960 1285327 := bstep (se 1 (by rfl) ⟨963995, by rfl⟩ : syracuseStep 1285327 = 1927991) B1927991
theorem B6946015 : Blo 1283960 6946015 := bstep (se 1 (by rfl) ⟨5209511, by rfl⟩ : syracuseStep 6946015 = 10419023) B10419023
theorem B1285351 : Blo 1283960 1285351 := bstep (se 1 (by rfl) ⟨964013, by rfl⟩ : syracuseStep 1285351 = 1928027) B1928027
theorem B8232263 : Blo 1283960 8232263 := bstep (se 1 (by rfl) ⟨6174197, by rfl⟩ : syracuseStep 8232263 = 12348395) B12348395
theorem B1285447 : Blo 1283960 1285447 := bstep (se 1 (by rfl) ⟨964085, by rfl⟩ : syracuseStep 1285447 = 1928171) B1928171
theorem B2932139 : Blo 1283960 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B1285583 : Blo 1283960 1285583 := bstep (se 1 (by rfl) ⟨964187, by rfl⟩ : syracuseStep 1285583 = 1928375) B1928375
theorem B11132407 : Blo 1283960 11132407 := bstep (se 1 (by rfl) ⟨8349305, by rfl⟩ : syracuseStep 11132407 = 16698611) B16698611
theorem B3251785 : Blo 1283960 3251785 := bstep (se 2 (by rfl) ⟨1219419, by rfl⟩ : syracuseStep 3251785 = 2438839) B2438839
theorem B1285743 : Blo 1283960 1285743 := bstep (se 1 (by rfl) ⟨964307, by rfl⟩ : syracuseStep 1285743 = 1928615) B1928615
theorem B18538105 : Blo 1283960 18538105 := bstep (se 2 (by rfl) ⟨6951789, by rfl⟩ : syracuseStep 18538105 = 13903579) B13903579
theorem B1285799 : Blo 1283960 1285799 := bstep (se 1 (by rfl) ⟨964349, by rfl⟩ : syracuseStep 1285799 = 1928699) B1928699
theorem B2891483 : Blo 1283960 2891483 := bstep (se 1 (by rfl) ⟨2168612, by rfl⟩ : syracuseStep 2891483 = 4337225) B4337225
theorem B1285863 : Blo 1283960 1285863 := bstep (se 1 (by rfl) ⟨964397, by rfl⟩ : syracuseStep 1285863 = 1928795) B1928795
theorem B3088147 : Blo 1283960 3088147 := bstep (se 1 (by rfl) ⟨2316110, by rfl⟩ : syracuseStep 3088147 = 4632221) B4632221
theorem B1285919 : Blo 1283960 1285919 := bstep (se 1 (by rfl) ⟨964439, by rfl⟩ : syracuseStep 1285919 = 1928879) B1928879
theorem B17588015 : Blo 1283960 17588015 := bstep (se 1 (by rfl) ⟨13191011, by rfl⟩ : syracuseStep 17588015 = 26382023) B26382023
theorem B2441171 : Blo 1283960 2441171 := bstep (se 1 (by rfl) ⟨1830878, by rfl⟩ : syracuseStep 2441171 = 3661757) B3661757
theorem B2891753 : Blo 1283960 2891753 := bstep (se 2 (by rfl) ⟨1084407, by rfl⟩ : syracuseStep 2891753 = 2168815) B2168815
theorem B3711071 : Blo 1283960 3711071 := bstep (se 1 (by rfl) ⟨2783303, by rfl⟩ : syracuseStep 3711071 = 5566607) B5566607
theorem B4333715 : Blo 1283960 4333715 := bstep (se 1 (by rfl) ⟨3250286, by rfl⟩ : syracuseStep 4333715 = 6500573) B6500573
theorem B1736959 : Blo 1283960 1736959 := bstep (se 1 (by rfl) ⟨1302719, by rfl⟩ : syracuseStep 1736959 = 2605439) B2605439
theorem B3088763 : Blo 1283960 3088763 := bstep (se 1 (by rfl) ⟨2316572, by rfl⟩ : syracuseStep 3088763 = 4633145) B4633145
theorem B6947315 : Blo 1283960 6947315 := bstep (se 1 (by rfl) ⟨5210486, by rfl⟩ : syracuseStep 6947315 = 10420973) B10420973
theorem B2892329 : Blo 1283960 2892329 := bstep (se 2 (by rfl) ⟨1084623, by rfl⟩ : syracuseStep 2892329 = 2169247) B2169247
theorem B6947639 : Blo 1283960 6947639 := bstep (se 1 (by rfl) ⟨5210729, by rfl⟩ : syracuseStep 6947639 = 10421459) B10421459
theorem B2892635 : Blo 1283960 2892635 := bstep (se 1 (by rfl) ⟨2169476, by rfl⟩ : syracuseStep 2892635 = 4338953) B4338953
theorem B1926047 : Blo 1283960 1926047 := bstep (se 1 (by rfl) ⟨1444535, by rfl⟩ : syracuseStep 1926047 = 2889071) B2889071
theorem B6505595 : Blo 1283960 6505595 := bstep (se 1 (by rfl) ⟨4879196, by rfl⟩ : syracuseStep 6505595 = 9758393) B9758393
theorem B2892959 : Blo 1283960 2892959 := bstep (se 1 (by rfl) ⟨2169719, by rfl⟩ : syracuseStep 2892959 = 4339439) B4339439
theorem B1926335 : Blo 1283960 1926335 := bstep (se 1 (by rfl) ⟨1444751, by rfl⟩ : syracuseStep 1926335 = 2889503) B2889503
theorem B1926479 : Blo 1283960 1926479 := bstep (se 1 (by rfl) ⟨1444859, by rfl⟩ : syracuseStep 1926479 = 2889719) B2889719
theorem B1828207 : Blo 1283960 1828207 := bstep (se 1 (by rfl) ⟨1371155, by rfl⟩ : syracuseStep 1828207 = 2742311) B2742311
theorem B1926569 : Blo 1283960 1926569 := bstep (se 2 (by rfl) ⟨722463, by rfl⟩ : syracuseStep 1926569 = 1444927) B1444927
theorem B3253729 : Blo 1283960 3253729 := bstep (se 2 (by rfl) ⟨1220148, by rfl⟩ : syracuseStep 3253729 = 2440297) B2440297
theorem B1828327 : Blo 1283960 1828327 := bstep (se 1 (by rfl) ⟨1371245, by rfl⟩ : syracuseStep 1828327 = 2742491) B2742491
theorem B1926719 : Blo 1283960 1926719 := bstep (se 1 (by rfl) ⟨1445039, by rfl⟩ : syracuseStep 1926719 = 2890079) B2890079
theorem B27805517 : Blo 1283960 27805517 := bstep (se 3 (by rfl) ⟨5213534, by rfl⟩ : syracuseStep 27805517 = 10427069) B10427069
theorem B5859155 : Blo 1283960 5859155 := bstep (se 1 (by rfl) ⟨4394366, by rfl⟩ : syracuseStep 5859155 = 8788733) B8788733
theorem B1927079 : Blo 1283960 1927079 := bstep (se 1 (by rfl) ⟨1445309, by rfl⟩ : syracuseStep 1927079 = 2890619) B2890619
theorem B4114415 : Blo 1283960 4114415 := bstep (se 1 (by rfl) ⟨3085811, by rfl⟩ : syracuseStep 4114415 = 6171623) B6171623
theorem B1927199 : Blo 1283960 1927199 := bstep (se 1 (by rfl) ⟨1445399, by rfl⟩ : syracuseStep 1927199 = 2890799) B2890799
theorem B14641235 : Blo 1283960 14641235 := bstep (se 1 (by rfl) ⟨10980926, by rfl⟩ : syracuseStep 14641235 = 21961853) B21961853
theorem B4335713 : Blo 1283960 4335713 := bstep (se 2 (by rfl) ⟨1625892, by rfl⟩ : syracuseStep 4335713 = 3251785) B3251785
theorem B28166291 : Blo 1283960 28166291 := bstep (se 1 (by rfl) ⟨21124718, by rfl⟩ : syracuseStep 28166291 = 42249437) B42249437
theorem B24717473 : Blo 1283960 24717473 := bstep (se 2 (by rfl) ⟨9269052, by rfl⟩ : syracuseStep 24717473 = 18538105) B18538105
theorem B11725049 : Blo 1283960 11725049 := bstep (se 2 (by rfl) ⟨4396893, by rfl⟩ : syracuseStep 11725049 = 8793787) B8793787
theorem B1927655 : Blo 1283960 1927655 := bstep (se 1 (by rfl) ⟨1445741, by rfl⟩ : syracuseStep 1927655 = 2891483) B2891483
theorem B11725343 : Blo 1283960 11725343 := bstep (se 1 (by rfl) ⟨8794007, by rfl⟩ : syracuseStep 11725343 = 17588015) B17588015
theorem B2345555 : Blo 1283960 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B4336253 : Blo 1283960 4336253 := bstep (se 3 (by rfl) ⟨813047, by rfl⟩ : syracuseStep 4336253 = 1626095) B1626095
theorem B1927835 : Blo 1283960 1927835 := bstep (se 1 (by rfl) ⟨1445876, by rfl⟩ : syracuseStep 1927835 = 2891753) B2891753
theorem B1444639 : Blo 1283960 1444639 := bstep (se 1 (by rfl) ⟨1083479, by rfl⟩ : syracuseStep 1444639 = 2166959) B2166959
theorem B1928057 : Blo 1283960 1928057 := bstep (se 2 (by rfl) ⟨723021, by rfl⟩ : syracuseStep 1928057 = 1446043) B1446043
theorem B5565307 : Blo 1283960 5565307 := bstep (se 1 (by rfl) ⟨4173980, by rfl⟩ : syracuseStep 5565307 = 8347961) B8347961
theorem B2059129 : Blo 1283960 2059129 := bstep (se 2 (by rfl) ⟨772173, by rfl⟩ : syracuseStep 2059129 = 1544347) B1544347
theorem B1928303 : Blo 1283960 1928303 := bstep (se 1 (by rfl) ⟨1446227, by rfl⟩ : syracuseStep 1928303 = 2892455) B2892455
theorem B6171835 : Blo 1283960 6171835 := bstep (se 1 (by rfl) ⟨4628876, by rfl⟩ : syracuseStep 6171835 = 9257753) B9257753
theorem B1928399 : Blo 1283960 1928399 := bstep (se 1 (by rfl) ⟨1446299, by rfl⟩ : syracuseStep 1928399 = 2892599) B2892599
theorem B4697297 : Blo 1283960 4697297 := bstep (se 2 (by rfl) ⟨1761486, by rfl⟩ : syracuseStep 4697297 = 3522973) B3522973
theorem B1928519 : Blo 1283960 1928519 := bstep (se 1 (by rfl) ⟨1446389, by rfl⟩ : syracuseStep 1928519 = 2892779) B2892779
theorem B1928807 : Blo 1283960 1928807 := bstep (se 1 (by rfl) ⟨1446605, by rfl⟩ : syracuseStep 1928807 = 2893211) B2893211
theorem B125054711 : Blo 1283960 125054711 := bstep (se 1 (by rfl) ⟨93791033, by rfl⟩ : syracuseStep 125054711 = 187582067) B187582067
theorem B1446079 : Blo 1283960 1446079 := bstep (se 1 (by rfl) ⟨1084559, by rfl⟩ : syracuseStep 1446079 = 2169119) B2169119
theorem B9261353 : Blo 1283960 9261353 := bstep (se 2 (by rfl) ⟨3473007, by rfl⟩ : syracuseStep 9261353 = 6946015) B6946015
theorem B3658031 : Blo 1283960 3658031 := bstep (se 1 (by rfl) ⟨2743523, by rfl⟩ : syracuseStep 3658031 = 5487047) B5487047
theorem B9753047 : Blo 1283960 9753047 := bstep (se 1 (by rfl) ⟨7314785, by rfl⟩ : syracuseStep 9753047 = 14629571) B14629571
theorem B2347631 : Blo 1283960 2347631 := bstep (se 1 (by rfl) ⟨1760723, by rfl⟩ : syracuseStep 2347631 = 3521447) B3521447
theorem B7320253 : Blo 1283960 7320253 := bstep (se 3 (by rfl) ⟨1372547, by rfl⟩ : syracuseStep 7320253 = 2745095) B2745095
theorem B6501059 : Blo 1283960 6501059 := bstep (se 1 (by rfl) ⟨4875794, by rfl⟩ : syracuseStep 6501059 = 9751589) B9751589
theorem B1954759 : Blo 1283960 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B4117529 : Blo 1283960 4117529 := bstep (se 2 (by rfl) ⟨1544073, by rfl⟩ : syracuseStep 4117529 = 3088147) B3088147
theorem B1373231 : Blo 1283960 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B2438399 : Blo 1283960 2438399 := bstep (se 1 (by rfl) ⟨1828799, by rfl⟩ : syracuseStep 2438399 = 3657599) B3657599
theorem B59372837 : Blo 1283960 59372837 := bstep (se 4 (by rfl) ⟨5566203, by rfl⟩ : syracuseStep 59372837 = 11132407) B11132407
theorem B1627447 : Blo 1283960 1627447 := bstep (se 1 (by rfl) ⟨1220585, by rfl⟩ : syracuseStep 1627447 = 2441171) B2441171
theorem B4232663 : Blo 1283960 4232663 := bstep (se 1 (by rfl) ⟨3174497, by rfl⟩ : syracuseStep 4232663 = 6348995) B6348995
theorem B2168383 : Blo 1283960 2168383 := bstep (se 1 (by rfl) ⟨1626287, by rfl⟩ : syracuseStep 2168383 = 3252575) B3252575
theorem B2348713 : Blo 1283960 2348713 := bstep (se 2 (by rfl) ⟨880767, by rfl⟩ : syracuseStep 2348713 = 1761535) B1761535
theorem B6174467 : Blo 1283960 6174467 := bstep (se 1 (by rfl) ⟨4630850, by rfl⟩ : syracuseStep 6174467 = 9261701) B9261701
theorem B2439067 : Blo 1283960 2439067 := bstep (se 1 (by rfl) ⟨1829300, by rfl⟩ : syracuseStep 2439067 = 3658601) B3658601
theorem B1284127 : Blo 1283960 1284127 := bstep (se 1 (by rfl) ⟨963095, by rfl⟩ : syracuseStep 1284127 = 1926191) B1926191
theorem B1284207 : Blo 1283960 1284207 := bstep (se 1 (by rfl) ⟨963155, by rfl⟩ : syracuseStep 1284207 = 1926311) B1926311
theorem B10557623 : Blo 1283960 10557623 := bstep (se 1 (by rfl) ⟨7918217, by rfl⟩ : syracuseStep 10557623 = 15836435) B15836435
theorem B12343549 : Blo 1283960 12343549 := bstep (se 3 (by rfl) ⟨2314415, by rfl⟩ : syracuseStep 12343549 = 4628831) B4628831
theorem B3660059 : Blo 1283960 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B100129061 : Blo 1283960 100129061 := bstep (se 4 (by rfl) ⟨9387099, by rfl⟩ : syracuseStep 100129061 = 18774199) B18774199
theorem B3250489 : Blo 1283960 3250489 := bstep (se 2 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 3250489 = 2437867) B2437867
theorem B1284455 : Blo 1283960 1284455 := bstep (se 1 (by rfl) ⟨963341, by rfl⟩ : syracuseStep 1284455 = 1926683) B1926683
theorem B3250601 : Blo 1283960 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B7313921 : Blo 1283960 7313921 := bstep (se 2 (by rfl) ⟨2742720, by rfl⟩ : syracuseStep 7313921 = 5485441) B5485441
theorem B2890331 : Blo 1283960 2890331 := bstep (se 1 (by rfl) ⟨2167748, by rfl⟩ : syracuseStep 2890331 = 4335497) B4335497
theorem B1284711 : Blo 1283960 1284711 := bstep (se 1 (by rfl) ⟨963533, by rfl⟩ : syracuseStep 1284711 = 1927067) B1927067
theorem B3250793 : Blo 1283960 3250793 := bstep (se 2 (by rfl) ⟨1219047, by rfl⟩ : syracuseStep 3250793 = 2438095) B2438095
theorem B13892201 : Blo 1283960 13892201 := bstep (se 2 (by rfl) ⟨5209575, by rfl⟩ : syracuseStep 13892201 = 10419151) B10419151
theorem B1284735 : Blo 1283960 1284735 := bstep (se 1 (by rfl) ⟨963551, by rfl⟩ : syracuseStep 1284735 = 1927103) B1927103
theorem B3906209 : Blo 1283960 3906209 := bstep (se 2 (by rfl) ⟨1464828, by rfl⟩ : syracuseStep 3906209 = 2929657) B2929657
theorem B1284859 : Blo 1283960 1284859 := bstep (se 1 (by rfl) ⟨963644, by rfl⟩ : syracuseStep 1284859 = 1927289) B1927289
theorem B6503327 : Blo 1283960 6503327 := bstep (se 1 (by rfl) ⟨4877495, by rfl⟩ : syracuseStep 6503327 = 9754991) B9754991
theorem B13196267 : Blo 1283960 13196267 := bstep (se 1 (by rfl) ⟨9897200, by rfl⟩ : syracuseStep 13196267 = 19794401) B19794401
theorem B1285115 : Blo 1283960 1285115 := bstep (se 1 (by rfl) ⟨963836, by rfl⟩ : syracuseStep 1285115 = 1927673) B1927673
theorem B1285151 : Blo 1283960 1285151 := bstep (se 1 (by rfl) ⟨963863, by rfl⟩ : syracuseStep 1285151 = 1927727) B1927727
theorem B15621331 : Blo 1283960 15621331 := bstep (se 1 (by rfl) ⟨11715998, by rfl⟩ : syracuseStep 15621331 = 23431997) B23431997
theorem B16465193 : Blo 1283960 16465193 := bstep (se 2 (by rfl) ⟨6174447, by rfl⟩ : syracuseStep 16465193 = 12348895) B12348895
theorem B1285439 : Blo 1283960 1285439 := bstep (se 1 (by rfl) ⟨964079, by rfl⟩ : syracuseStep 1285439 = 1928159) B1928159
theorem B3661129 : Blo 1283960 3661129 := bstep (se 2 (by rfl) ⟨1372923, by rfl⟩ : syracuseStep 3661129 = 2745847) B2745847
theorem B5488175 : Blo 1283960 5488175 := bstep (se 1 (by rfl) ⟨4116131, by rfl⟩ : syracuseStep 5488175 = 8232263) B8232263
theorem B1285735 : Blo 1283960 1285735 := bstep (se 1 (by rfl) ⟨964301, by rfl⟩ : syracuseStep 1285735 = 1928603) B1928603
theorem B4333391 : Blo 1283960 4333391 := bstep (se 1 (by rfl) ⟨3250043, by rfl⟩ : syracuseStep 4333391 = 6500087) B6500087
theorem B2744275 : Blo 1283960 2744275 := bstep (se 1 (by rfl) ⟨2058206, by rfl⟩ : syracuseStep 2744275 = 4116413) B4116413
theorem B2474047 : Blo 1283960 2474047 := bstep (se 1 (by rfl) ⟨1855535, by rfl⟩ : syracuseStep 2474047 = 3711071) B3711071
theorem B3661949 : Blo 1283960 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B16458065 : Blo 1283960 16458065 := bstep (se 2 (by rfl) ⟨6171774, by rfl⟩ : syracuseStep 16458065 = 12343549) B12343549
theorem B1565087 : Blo 1283960 1565087 := bstep (se 1 (by rfl) ⟨1173815, by rfl⟩ : syracuseStep 1565087 = 2347631) B2347631
theorem B4333985 : Blo 1283960 4333985 := bstep (se 2 (by rfl) ⟨1625244, by rfl⟩ : syracuseStep 4333985 = 3250489) B3250489
theorem B4334039 : Blo 1283960 4334039 := bstep (se 1 (by rfl) ⟨3250529, by rfl⟩ : syracuseStep 4334039 = 6501059) B6501059
theorem B2745019 : Blo 1283960 2745019 := bstep (se 1 (by rfl) ⟨2058764, by rfl⟩ : syracuseStep 2745019 = 4117529) B4117529
theorem B1926185 : Blo 1283960 1926185 := bstep (se 2 (by rfl) ⟨722319, by rfl⟩ : syracuseStep 1926185 = 1444639) B1444639
theorem B2745505 : Blo 1283960 2745505 := bstep (se 2 (by rfl) ⟨1029564, by rfl⟩ : syracuseStep 2745505 = 2059129) B2059129
theorem B2606345 : Blo 1283960 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B18777527 : Blo 1283960 18777527 := bstep (se 1 (by rfl) ⟨14083145, by rfl⟩ : syracuseStep 18777527 = 28166291) B28166291
theorem B7038415 : Blo 1283960 7038415 := bstep (se 1 (by rfl) ⟨5278811, by rfl⟩ : syracuseStep 7038415 = 10557623) B10557623
theorem B7816699 : Blo 1283960 7816699 := bstep (se 1 (by rfl) ⟨5862524, by rfl⟩ : syracuseStep 7816699 = 11725049) B11725049
theorem B4875947 : Blo 1283960 4875947 := bstep (se 1 (by rfl) ⟨3656960, by rfl⟩ : syracuseStep 4875947 = 7313921) B7313921
theorem B7816895 : Blo 1283960 7816895 := bstep (se 1 (by rfl) ⟨5862671, by rfl⟩ : syracuseStep 7816895 = 11725343) B11725343
theorem B1926887 : Blo 1283960 1926887 := bstep (se 1 (by rfl) ⟨1445165, by rfl⟩ : syracuseStep 1926887 = 2890331) B2890331
theorem B4335551 : Blo 1283960 4335551 := bstep (se 1 (by rfl) ⟨3251663, by rfl⟩ : syracuseStep 4335551 = 6503327) B6503327
theorem B3131531 : Blo 1283960 3131531 := bstep (se 1 (by rfl) ⟨2348648, by rfl⟩ : syracuseStep 3131531 = 4697297) B4697297
theorem B3131617 : Blo 1283960 3131617 := bstep (se 2 (by rfl) ⟨1174356, by rfl⟩ : syracuseStep 3131617 = 2348713) B2348713
theorem B2059175 : Blo 1283960 2059175 := bstep (se 1 (by rfl) ⟨1544381, by rfl⟩ : syracuseStep 2059175 = 3088763) B3088763
theorem B1928105 : Blo 1283960 1928105 := bstep (se 2 (by rfl) ⟨723039, by rfl⟩ : syracuseStep 1928105 = 1446079) B1446079
theorem B4631543 : Blo 1283960 4631543 := bstep (se 1 (by rfl) ⟨3473657, by rfl⟩ : syracuseStep 4631543 = 6947315) B6947315
theorem B1928219 : Blo 1283960 1928219 := bstep (se 1 (by rfl) ⟨1446164, by rfl⟩ : syracuseStep 1928219 = 2892329) B2892329
theorem B4631759 : Blo 1283960 4631759 := bstep (se 1 (by rfl) ⟨3473819, by rfl⟩ : syracuseStep 4631759 = 6947639) B6947639
theorem B1928423 : Blo 1283960 1928423 := bstep (se 1 (by rfl) ⟨1446317, by rfl⟩ : syracuseStep 1928423 = 2892635) B2892635
theorem B4337063 : Blo 1283960 4337063 := bstep (se 1 (by rfl) ⟨3252797, by rfl⟩ : syracuseStep 4337063 = 6505595) B6505595
theorem B1928639 : Blo 1283960 1928639 := bstep (se 1 (by rfl) ⟨1446479, by rfl⟩ : syracuseStep 1928639 = 2892959) B2892959
theorem B1625599 : Blo 1283960 1625599 := bstep (se 1 (by rfl) ⟨1219199, by rfl⟩ : syracuseStep 1625599 = 2438399) B2438399
theorem B9760337 : Blo 1283960 9760337 := bstep (se 2 (by rfl) ⟨3660126, by rfl⟩ : syracuseStep 9760337 = 7320253) B7320253
theorem B2821775 : Blo 1283960 2821775 := bstep (se 1 (by rfl) ⟨2116331, by rfl⟩ : syracuseStep 2821775 = 4232663) B4232663
theorem B4116311 : Blo 1283960 4116311 := bstep (se 1 (by rfl) ⟨3087233, by rfl⟩ : syracuseStep 4116311 = 6174467) B6174467
theorem B9760823 : Blo 1283960 9760823 := bstep (se 1 (by rfl) ⟨7320617, by rfl⟩ : syracuseStep 9760823 = 14641235) B14641235
theorem B16478315 : Blo 1283960 16478315 := bstep (se 1 (by rfl) ⟨12358736, by rfl⟩ : syracuseStep 16478315 = 24717473) B24717473
theorem B66752707 : Blo 1283960 66752707 := bstep (se 1 (by rfl) ⟨50064530, by rfl⟩ : syracuseStep 66752707 = 100129061) B100129061
theorem B6254813 : Blo 1283960 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B8229113 : Blo 1283960 8229113 := bstep (se 2 (by rfl) ⟨3085917, by rfl⟩ : syracuseStep 8229113 = 6171835) B6171835
theorem B20828441 : Blo 1283960 20828441 := bstep (se 2 (by rfl) ⟨7810665, by rfl⟩ : syracuseStep 20828441 = 15621331) B15621331
theorem B2167067 : Blo 1283960 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B2167195 : Blo 1283960 2167195 := bstep (se 1 (by rfl) ⟨1625396, by rfl⟩ : syracuseStep 2167195 = 3250793) B3250793
theorem B9261467 : Blo 1283960 9261467 := bstep (se 1 (by rfl) ⟨6946100, by rfl⟩ : syracuseStep 9261467 = 13892201) B13892201
theorem B2437609 : Blo 1283960 2437609 := bstep (se 2 (by rfl) ⟨914103, by rfl⟩ : syracuseStep 2437609 = 1828207) B1828207
theorem B4338305 : Blo 1283960 4338305 := bstep (se 2 (by rfl) ⟨1626864, by rfl⟩ : syracuseStep 4338305 = 3253729) B3253729
theorem B2437769 : Blo 1283960 2437769 := bstep (se 2 (by rfl) ⟨914163, by rfl⟩ : syracuseStep 2437769 = 1828327) B1828327
theorem B3658783 : Blo 1283960 3658783 := bstep (se 1 (by rfl) ⟨2744087, by rfl⟩ : syracuseStep 3658783 = 5488175) B5488175
theorem B2888927 : Blo 1283960 2888927 := bstep (se 1 (by rfl) ⟨2166695, by rfl⟩ : syracuseStep 2888927 = 4333391) B4333391
theorem B3659033 : Blo 1283960 3659033 := bstep (se 2 (by rfl) ⟨1372137, by rfl⟩ : syracuseStep 3659033 = 2744275) B2744275
theorem B2889143 : Blo 1283960 2889143 := bstep (se 1 (by rfl) ⟨2166857, by rfl⟩ : syracuseStep 2889143 = 4333715) B4333715
theorem B6174235 : Blo 1283960 6174235 := bstep (se 1 (by rfl) ⟨4630676, by rfl⟩ : syracuseStep 6174235 = 9261353) B9261353
theorem B2438687 : Blo 1283960 2438687 := bstep (se 1 (by rfl) ⟨1829015, by rfl⟩ : syracuseStep 2438687 = 3658031) B3658031
theorem B6502031 : Blo 1283960 6502031 := bstep (se 1 (by rfl) ⟨4876523, by rfl⟩ : syracuseStep 6502031 = 9753047) B9753047
theorem B2315945 : Blo 1283960 2315945 := bstep (se 2 (by rfl) ⟨868479, by rfl⟩ : syracuseStep 2315945 = 1736959) B1736959
theorem B1284031 : Blo 1283960 1284031 := bstep (se 1 (by rfl) ⟨963023, by rfl⟩ : syracuseStep 1284031 = 1926047) B1926047
theorem B1284223 : Blo 1283960 1284223 := bstep (se 1 (by rfl) ⟨963167, by rfl⟩ : syracuseStep 1284223 = 1926335) B1926335
theorem B39581891 : Blo 1283960 39581891 := bstep (se 1 (by rfl) ⟨29686418, by rfl⟩ : syracuseStep 39581891 = 59372837) B59372837
theorem B1284319 : Blo 1283960 1284319 := bstep (se 1 (by rfl) ⟨963239, by rfl⟩ : syracuseStep 1284319 = 1926479) B1926479
theorem B1284379 : Blo 1283960 1284379 := bstep (se 1 (by rfl) ⟨963284, by rfl⟩ : syracuseStep 1284379 = 1926569) B1926569
theorem B1284479 : Blo 1283960 1284479 := bstep (se 1 (by rfl) ⟨963359, by rfl⟩ : syracuseStep 1284479 = 1926719) B1926719
theorem B7420409 : Blo 1283960 7420409 := bstep (se 2 (by rfl) ⟨2782653, by rfl⟩ : syracuseStep 7420409 = 5565307) B5565307
theorem B18537011 : Blo 1283960 18537011 := bstep (se 1 (by rfl) ⟨13902758, by rfl⟩ : syracuseStep 18537011 = 27805517) B27805517
theorem B3906103 : Blo 1283960 3906103 := bstep (se 1 (by rfl) ⟨2929577, by rfl⟩ : syracuseStep 3906103 = 5859155) B5859155
theorem B1284719 : Blo 1283960 1284719 := bstep (se 1 (by rfl) ⟨963539, by rfl⟩ : syracuseStep 1284719 = 1927079) B1927079
theorem B2742943 : Blo 1283960 2742943 := bstep (se 1 (by rfl) ⟨2057207, by rfl⟩ : syracuseStep 2742943 = 4114415) B4114415
theorem B1284799 : Blo 1283960 1284799 := bstep (se 1 (by rfl) ⟨963599, by rfl⟩ : syracuseStep 1284799 = 1927199) B1927199
theorem B2890475 : Blo 1283960 2890475 := bstep (se 1 (by rfl) ⟨2167856, by rfl⟩ : syracuseStep 2890475 = 4335713) B4335713
theorem B2440039 : Blo 1283960 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B1285103 : Blo 1283960 1285103 := bstep (se 1 (by rfl) ⟨963827, by rfl⟩ : syracuseStep 1285103 = 1927655) B1927655
theorem B2169929 : Blo 1283960 2169929 := bstep (se 2 (by rfl) ⟨813723, by rfl⟩ : syracuseStep 2169929 = 1627447) B1627447
theorem B2890835 : Blo 1283960 2890835 := bstep (se 1 (by rfl) ⟨2168126, by rfl⟩ : syracuseStep 2890835 = 4336253) B4336253
theorem B4881505 : Blo 1283960 4881505 := bstep (se 2 (by rfl) ⟨1830564, by rfl⟩ : syracuseStep 4881505 = 3661129) B3661129
theorem B1285223 : Blo 1283960 1285223 := bstep (se 1 (by rfl) ⟨963917, by rfl⟩ : syracuseStep 1285223 = 1927835) B1927835
theorem B2604139 : Blo 1283960 2604139 := bstep (se 1 (by rfl) ⟨1953104, by rfl⟩ : syracuseStep 2604139 = 3906209) B3906209
theorem B1285371 : Blo 1283960 1285371 := bstep (se 1 (by rfl) ⟨964028, by rfl⟩ : syracuseStep 1285371 = 1928057) B1928057
theorem B8797511 : Blo 1283960 8797511 := bstep (se 1 (by rfl) ⟨6598133, by rfl⟩ : syracuseStep 8797511 = 13196267) B13196267
theorem B1285535 : Blo 1283960 1285535 := bstep (se 1 (by rfl) ⟨964151, by rfl⟩ : syracuseStep 1285535 = 1928303) B1928303
theorem B2891177 : Blo 1283960 2891177 := bstep (se 2 (by rfl) ⟨1084191, by rfl⟩ : syracuseStep 2891177 = 2168383) B2168383
theorem B1285599 : Blo 1283960 1285599 := bstep (se 1 (by rfl) ⟨964199, by rfl⟩ : syracuseStep 1285599 = 1928399) B1928399
theorem B10976795 : Blo 1283960 10976795 := bstep (se 1 (by rfl) ⟨8232596, by rfl⟩ : syracuseStep 10976795 = 16465193) B16465193
theorem B1285679 : Blo 1283960 1285679 := bstep (se 1 (by rfl) ⟨964259, by rfl⟩ : syracuseStep 1285679 = 1928519) B1928519
theorem B1285871 : Blo 1283960 1285871 := bstep (se 1 (by rfl) ⟨964403, by rfl⟩ : syracuseStep 1285871 = 1928807) B1928807
theorem B83369807 : Blo 1283960 83369807 := bstep (se 1 (by rfl) ⟨62527355, by rfl⟩ : syracuseStep 83369807 = 125054711) B125054711
theorem B3252089 : Blo 1283960 3252089 := bstep (se 2 (by rfl) ⟨1219533, by rfl⟩ : syracuseStep 3252089 = 2439067) B2439067
theorem B10985543 : Blo 1283960 10985543 := bstep (se 1 (by rfl) ⟨8239157, by rfl⟩ : syracuseStep 10985543 = 16478315) B16478315
theorem B4169875 : Blo 1283960 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B9765197 : Blo 1283960 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B2892203 : Blo 1283960 2892203 := bstep (se 1 (by rfl) ⟨2169152, by rfl⟩ : syracuseStep 2892203 = 4338305) B4338305
theorem B55542509 : Blo 1283960 55542509 := bstep (se 3 (by rfl) ⟨10414220, by rfl⟩ : syracuseStep 55542509 = 20828441) B20828441
theorem B9757421 : Blo 1283960 9757421 := bstep (se 3 (by rfl) ⟨1829516, by rfl⟩ : syracuseStep 9757421 = 3659033) B3659033
theorem B1925951 : Blo 1283960 1925951 := bstep (se 1 (by rfl) ⟨1444463, by rfl⟩ : syracuseStep 1925951 = 2888927) B2888927
theorem B1737563 : Blo 1283960 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B1926095 : Blo 1283960 1926095 := bstep (se 1 (by rfl) ⟨1444571, by rfl⟩ : syracuseStep 1926095 = 2889143) B2889143
theorem B12518351 : Blo 1283960 12518351 := bstep (se 1 (by rfl) ⟨9388763, by rfl⟩ : syracuseStep 12518351 = 18777527) B18777527
theorem B4334687 : Blo 1283960 4334687 := bstep (se 1 (by rfl) ⟨3251015, by rfl⟩ : syracuseStep 4334687 = 6502031) B6502031
theorem B5211263 : Blo 1283960 5211263 := bstep (se 1 (by rfl) ⟨3908447, by rfl⟩ : syracuseStep 5211263 = 7816895) B7816895
theorem B3253385 : Blo 1283960 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B26387927 : Blo 1283960 26387927 := bstep (se 1 (by rfl) ⟨19790945, by rfl⟩ : syracuseStep 26387927 = 39581891) B39581891
theorem B1926983 : Blo 1283960 1926983 := bstep (se 1 (by rfl) ⟨1445237, by rfl⟩ : syracuseStep 1926983 = 2890475) B2890475
theorem B10422265 : Blo 1283960 10422265 := bstep (se 2 (by rfl) ⟨3908349, by rfl⟩ : syracuseStep 10422265 = 7816699) B7816699
theorem B1927223 : Blo 1283960 1927223 := bstep (se 1 (by rfl) ⟨1445417, by rfl⟩ : syracuseStep 1927223 = 2890835) B2890835
theorem B1927451 : Blo 1283960 1927451 := bstep (se 1 (by rfl) ⟨1445588, by rfl⟩ : syracuseStep 1927451 = 2891177) B2891177
theorem B7317863 : Blo 1283960 7317863 := bstep (se 1 (by rfl) ⟨5488397, by rfl⟩ : syracuseStep 7317863 = 10976795) B10976795
theorem B6506891 : Blo 1283960 6506891 := bstep (se 1 (by rfl) ⟨4880168, by rfl⟩ : syracuseStep 6506891 = 9760337) B9760337
theorem B6507215 : Blo 1283960 6507215 := bstep (se 1 (by rfl) ⟨4880411, by rfl⟩ : syracuseStep 6507215 = 9760823) B9760823
theorem B1444711 : Blo 1283960 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B10972043 : Blo 1283960 10972043 := bstep (se 1 (by rfl) ⟨8229032, by rfl⟩ : syracuseStep 10972043 = 16458065) B16458065
theorem B1625179 : Blo 1283960 1625179 := bstep (se 1 (by rfl) ⟨1218884, by rfl⟩ : syracuseStep 1625179 = 2437769) B2437769
theorem B13888741 : Blo 1283960 13888741 := bstep (se 4 (by rfl) ⟨1302069, by rfl⟩ : syracuseStep 13888741 = 2604139) B2604139
theorem B14642693 : Blo 1283960 14642693 := bstep (se 4 (by rfl) ⟨1372752, by rfl⟩ : syracuseStep 14642693 = 2745505) B2745505
theorem B3657257 : Blo 1283960 3657257 := bstep (se 2 (by rfl) ⟨1371471, by rfl⟩ : syracuseStep 3657257 = 2742943) B2742943
theorem B1543963 : Blo 1283960 1543963 := bstep (se 1 (by rfl) ⟨1157972, by rfl⟩ : syracuseStep 1543963 = 2315945) B2315945
theorem B4878377 : Blo 1283960 4878377 := bstep (se 2 (by rfl) ⟨1829391, by rfl⟩ : syracuseStep 4878377 = 3658783) B3658783
theorem B6508673 : Blo 1283960 6508673 := bstep (se 2 (by rfl) ⟨2440752, by rfl⟩ : syracuseStep 6508673 = 4881505) B4881505
theorem B12358007 : Blo 1283960 12358007 := bstep (se 1 (by rfl) ⟨9268505, by rfl⟩ : syracuseStep 12358007 = 18537011) B18537011
theorem B7524733 : Blo 1283960 7524733 := bstep (se 3 (by rfl) ⟨1410887, by rfl⟩ : syracuseStep 7524733 = 2821775) B2821775
theorem B9384553 : Blo 1283960 9384553 := bstep (se 2 (by rfl) ⟨3519207, by rfl⟩ : syracuseStep 9384553 = 7038415) B7038415
theorem B1372783 : Blo 1283960 1372783 := bstep (se 1 (by rfl) ⟨1029587, by rfl⟩ : syracuseStep 1372783 = 2059175) B2059175
theorem B2167465 : Blo 1283960 2167465 := bstep (se 2 (by rfl) ⟨812799, by rfl⟩ : syracuseStep 2167465 = 1625599) B1625599
theorem B1446619 : Blo 1283960 1446619 := bstep (se 1 (by rfl) ⟨1084964, by rfl⟩ : syracuseStep 1446619 = 2169929) B2169929
theorem B55579871 : Blo 1283960 55579871 := bstep (se 1 (by rfl) ⟨41684903, by rfl⟩ : syracuseStep 55579871 = 83369807) B83369807
theorem B2168059 : Blo 1283960 2168059 := bstep (se 1 (by rfl) ⟨1626044, by rfl⟩ : syracuseStep 2168059 = 3252089) B3252089
theorem B3298729 : Blo 1283960 3298729 := bstep (se 2 (by rfl) ⟨1237023, by rfl⟩ : syracuseStep 3298729 = 2474047) B2474047
theorem B5486075 : Blo 1283960 5486075 := bstep (se 1 (by rfl) ⟨4114556, by rfl⟩ : syracuseStep 5486075 = 8229113) B8229113
theorem B89003609 : Blo 1283960 89003609 := bstep (se 2 (by rfl) ⟨33376353, by rfl⟩ : syracuseStep 89003609 = 66752707) B66752707
theorem B6174311 : Blo 1283960 6174311 := bstep (se 1 (by rfl) ⟨4630733, by rfl⟩ : syracuseStep 6174311 = 9261467) B9261467
theorem B2889323 : Blo 1283960 2889323 := bstep (se 1 (by rfl) ⟨2166992, by rfl⟩ : syracuseStep 2889323 = 4333985) B4333985
theorem B4175489 : Blo 1283960 4175489 := bstep (se 2 (by rfl) ⟨1565808, by rfl⟩ : syracuseStep 4175489 = 3131617) B3131617
theorem B2889359 : Blo 1283960 2889359 := bstep (se 1 (by rfl) ⟨2167019, by rfl⟩ : syracuseStep 2889359 = 4334039) B4334039
theorem B2889593 : Blo 1283960 2889593 := bstep (se 2 (by rfl) ⟨1083597, by rfl⟩ : syracuseStep 2889593 = 2167195) B2167195
theorem B3250145 : Blo 1283960 3250145 := bstep (se 2 (by rfl) ⟨1218804, by rfl⟩ : syracuseStep 3250145 = 2437609) B2437609
theorem B1284123 : Blo 1283960 1284123 := bstep (se 1 (by rfl) ⟨963092, by rfl⟩ : syracuseStep 1284123 = 1926185) B1926185
theorem B5208137 : Blo 1283960 5208137 := bstep (se 2 (by rfl) ⟨1953051, by rfl⟩ : syracuseStep 5208137 = 3906103) B3906103
theorem B3660025 : Blo 1283960 3660025 := bstep (se 2 (by rfl) ⟨1372509, by rfl⟩ : syracuseStep 3660025 = 2745019) B2745019
theorem B3250631 : Blo 1283960 3250631 := bstep (se 1 (by rfl) ⟨2437973, by rfl⟩ : syracuseStep 3250631 = 4875947) B4875947
theorem B1284591 : Blo 1283960 1284591 := bstep (se 1 (by rfl) ⟨963443, by rfl⟩ : syracuseStep 1284591 = 1926887) B1926887
theorem B2890367 : Blo 1283960 2890367 := bstep (se 1 (by rfl) ⟨2167775, by rfl⟩ : syracuseStep 2890367 = 4335551) B4335551
theorem B6503165 : Blo 1283960 6503165 := bstep (se 3 (by rfl) ⟨1219343, by rfl⟩ : syracuseStep 6503165 = 2438687) B2438687
theorem B2087687 : Blo 1283960 2087687 := bstep (se 1 (by rfl) ⟨1565765, by rfl⟩ : syracuseStep 2087687 = 3131531) B3131531
theorem B16694261 : Blo 1283960 16694261 := bstep (se 5 (by rfl) ⟨782543, by rfl⟩ : syracuseStep 16694261 = 1565087) B1565087
theorem B4946939 : Blo 1283960 4946939 := bstep (se 1 (by rfl) ⟨3710204, by rfl⟩ : syracuseStep 4946939 = 7420409) B7420409
theorem B1285403 : Blo 1283960 1285403 := bstep (se 1 (by rfl) ⟨964052, by rfl⟩ : syracuseStep 1285403 = 1928105) B1928105
theorem B3087695 : Blo 1283960 3087695 := bstep (se 1 (by rfl) ⟨2315771, by rfl⟩ : syracuseStep 3087695 = 4631543) B4631543
theorem B1285479 : Blo 1283960 1285479 := bstep (se 1 (by rfl) ⟨964109, by rfl⟩ : syracuseStep 1285479 = 1928219) B1928219
theorem B8232313 : Blo 1283960 8232313 := bstep (se 2 (by rfl) ⟨3087117, by rfl⟩ : syracuseStep 8232313 = 6174235) B6174235
theorem B3087839 : Blo 1283960 3087839 := bstep (se 1 (by rfl) ⟨2315879, by rfl⟩ : syracuseStep 3087839 = 4631759) B4631759
theorem B1285615 : Blo 1283960 1285615 := bstep (se 1 (by rfl) ⟨964211, by rfl⟩ : syracuseStep 1285615 = 1928423) B1928423
theorem B5865007 : Blo 1283960 5865007 := bstep (se 1 (by rfl) ⟨4398755, by rfl⟩ : syracuseStep 5865007 = 8797511) B8797511
theorem B2891375 : Blo 1283960 2891375 := bstep (se 1 (by rfl) ⟨2168531, by rfl⟩ : syracuseStep 2891375 = 4337063) B4337063
theorem B1285759 : Blo 1283960 1285759 := bstep (se 1 (by rfl) ⟨964319, by rfl⟩ : syracuseStep 1285759 = 1928639) B1928639
theorem B2744207 : Blo 1283960 2744207 := bstep (se 1 (by rfl) ⟨2058155, by rfl⟩ : syracuseStep 2744207 = 4116311) B4116311
theorem B3252251 : Blo 1283960 3252251 := bstep (se 1 (by rfl) ⟨2439188, by rfl⟩ : syracuseStep 3252251 = 4878377) B4878377
theorem B7323695 : Blo 1283960 7323695 := bstep (se 1 (by rfl) ⟨5492771, by rfl⟩ : syracuseStep 7323695 = 10985543) B10985543
theorem B37028339 : Blo 1283960 37028339 := bstep (se 1 (by rfl) ⟨27771254, by rfl⟩ : syracuseStep 37028339 = 55542509) B55542509
theorem B6504947 : Blo 1283960 6504947 := bstep (se 1 (by rfl) ⟨4878710, by rfl⟩ : syracuseStep 6504947 = 9757421) B9757421
theorem B3474175 : Blo 1283960 3474175 := bstep (se 1 (by rfl) ⟨2605631, by rfl⟩ : syracuseStep 3474175 = 5211263) B5211263
theorem B37053247 : Blo 1283960 37053247 := bstep (se 1 (by rfl) ⟨27789935, by rfl⟩ : syracuseStep 37053247 = 55579871) B55579871
theorem B59335739 : Blo 1283960 59335739 := bstep (se 1 (by rfl) ⟨44501804, by rfl⟩ : syracuseStep 59335739 = 89003609) B89003609
theorem B1926215 : Blo 1283960 1926215 := bstep (se 1 (by rfl) ⟨1444661, by rfl⟩ : syracuseStep 1926215 = 2889323) B2889323
theorem B1926239 : Blo 1283960 1926239 := bstep (se 1 (by rfl) ⟨1444679, by rfl⟩ : syracuseStep 1926239 = 2889359) B2889359
theorem B1926281 : Blo 1283960 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B1926395 : Blo 1283960 1926395 := bstep (se 1 (by rfl) ⟨1444796, by rfl⟩ : syracuseStep 1926395 = 2889593) B2889593
theorem B8234237 : Blo 1283960 8234237 := bstep (se 3 (by rfl) ⟨1543919, by rfl⟩ : syracuseStep 8234237 = 3087839) B3087839
theorem B1926911 : Blo 1283960 1926911 := bstep (se 1 (by rfl) ⟨1445183, by rfl⟩ : syracuseStep 1926911 = 2890367) B2890367
theorem B4335443 : Blo 1283960 4335443 := bstep (se 1 (by rfl) ⟨3251582, by rfl⟩ : syracuseStep 4335443 = 6503165) B6503165
theorem B2058463 : Blo 1283960 2058463 := bstep (se 1 (by rfl) ⟨1543847, by rfl⟩ : syracuseStep 2058463 = 3087695) B3087695
theorem B2058617 : Blo 1283960 2058617 := bstep (se 2 (by rfl) ⟨771981, by rfl⟩ : syracuseStep 2058617 = 1543963) B1543963
theorem B1927583 : Blo 1283960 1927583 := bstep (se 1 (by rfl) ⟨1445687, by rfl⟩ : syracuseStep 1927583 = 2891375) B2891375
theorem B1829471 : Blo 1283960 1829471 := bstep (se 1 (by rfl) ⟨1372103, by rfl⟩ : syracuseStep 1829471 = 2744207) B2744207
theorem B13896353 : Blo 1283960 13896353 := bstep (se 2 (by rfl) ⟨5211132, by rfl⟩ : syracuseStep 13896353 = 10422265) B10422265
theorem B1928135 : Blo 1283960 1928135 := bstep (se 1 (by rfl) ⟨1446101, by rfl⟩ : syracuseStep 1928135 = 2892203) B2892203
theorem B12512737 : Blo 1283960 12512737 := bstep (se 2 (by rfl) ⟨4692276, by rfl⟩ : syracuseStep 12512737 = 9384553) B9384553
theorem B1830377 : Blo 1283960 1830377 := bstep (se 2 (by rfl) ⟨686391, by rfl⟩ : syracuseStep 1830377 = 1372783) B1372783
theorem B18534005 : Blo 1283960 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B1928825 : Blo 1283960 1928825 := bstep (se 2 (by rfl) ⟨723309, by rfl⟩ : syracuseStep 1928825 = 1446619) B1446619
theorem B17591951 : Blo 1283960 17591951 := bstep (se 1 (by rfl) ⟨13193963, by rfl⟩ : syracuseStep 17591951 = 26387927) B26387927
theorem B3657383 : Blo 1283960 3657383 := bstep (se 1 (by rfl) ⟨2743037, by rfl⟩ : syracuseStep 3657383 = 5486075) B5486075
theorem B2166763 : Blo 1283960 2166763 := bstep (se 1 (by rfl) ⟨1625072, by rfl⟩ : syracuseStep 2166763 = 3250145) B3250145
theorem B2166905 : Blo 1283960 2166905 := bstep (se 2 (by rfl) ⟨812589, by rfl⟩ : syracuseStep 2166905 = 1625179) B1625179
theorem B4878575 : Blo 1283960 4878575 := bstep (se 1 (by rfl) ⟨3658931, by rfl⟩ : syracuseStep 4878575 = 7317863) B7317863
theorem B4337927 : Blo 1283960 4337927 := bstep (se 1 (by rfl) ⟨3253445, by rfl⟩ : syracuseStep 4337927 = 6506891) B6506891
theorem B2167087 : Blo 1283960 2167087 := bstep (se 1 (by rfl) ⟨1625315, by rfl⟩ : syracuseStep 2167087 = 3250631) B3250631
theorem B18518321 : Blo 1283960 18518321 := bstep (se 2 (by rfl) ⟨6944370, by rfl⟩ : syracuseStep 18518321 = 13888741) B13888741
theorem B4338143 : Blo 1283960 4338143 := bstep (se 1 (by rfl) ⟨3253607, by rfl⟩ : syracuseStep 4338143 = 6507215) B6507215
theorem B11129507 : Blo 1283960 11129507 := bstep (se 1 (by rfl) ⟨8347130, by rfl⟩ : syracuseStep 11129507 = 16694261) B16694261
theorem B3297959 : Blo 1283960 3297959 := bstep (se 1 (by rfl) ⟨2473469, by rfl⟩ : syracuseStep 3297959 = 4946939) B4946939
theorem B7820009 : Blo 1283960 7820009 := bstep (se 2 (by rfl) ⟨2932503, by rfl⟩ : syracuseStep 7820009 = 5865007) B5865007
theorem B9761795 : Blo 1283960 9761795 := bstep (se 1 (by rfl) ⟨7321346, by rfl⟩ : syracuseStep 9761795 = 14642693) B14642693
theorem B2438171 : Blo 1283960 2438171 := bstep (se 1 (by rfl) ⟨1828628, by rfl⟩ : syracuseStep 2438171 = 3657257) B3657257
theorem B4339115 : Blo 1283960 4339115 := bstep (se 1 (by rfl) ⟨3254336, by rfl⟩ : syracuseStep 4339115 = 6508673) B6508673
theorem B5559833 : Blo 1283960 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B6510131 : Blo 1283960 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B8238671 : Blo 1283960 8238671 := bstep (se 1 (by rfl) ⟨6179003, by rfl⟩ : syracuseStep 8238671 = 12358007) B12358007
theorem B4880033 : Blo 1283960 4880033 := bstep (se 2 (by rfl) ⟨1830012, by rfl⟩ : syracuseStep 4880033 = 3660025) B3660025
theorem B10032977 : Blo 1283960 10032977 := bstep (se 2 (by rfl) ⟨3762366, by rfl⟩ : syracuseStep 10032977 = 7524733) B7524733
theorem B1283967 : Blo 1283960 1283967 := bstep (se 1 (by rfl) ⟨962975, by rfl⟩ : syracuseStep 1283967 = 1925951) B1925951
theorem B1284063 : Blo 1283960 1284063 := bstep (se 1 (by rfl) ⟨963047, by rfl⟩ : syracuseStep 1284063 = 1926095) B1926095
theorem B8345567 : Blo 1283960 8345567 := bstep (se 1 (by rfl) ⟨6259175, by rfl⟩ : syracuseStep 8345567 = 12518351) B12518351
theorem B2889791 : Blo 1283960 2889791 := bstep (se 1 (by rfl) ⟨2167343, by rfl⟩ : syracuseStep 2889791 = 4334687) B4334687
theorem B2168923 : Blo 1283960 2168923 := bstep (se 1 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 2168923 = 3253385) B3253385
theorem B2889953 : Blo 1283960 2889953 := bstep (se 2 (by rfl) ⟨1083732, by rfl⟩ : syracuseStep 2889953 = 2167465) B2167465
theorem B2783659 : Blo 1283960 2783659 := bstep (se 1 (by rfl) ⟨2087744, by rfl⟩ : syracuseStep 2783659 = 4175489) B4175489
theorem B1284655 : Blo 1283960 1284655 := bstep (se 1 (by rfl) ⟨963491, by rfl⟩ : syracuseStep 1284655 = 1926983) B1926983
theorem B1284815 : Blo 1283960 1284815 := bstep (se 1 (by rfl) ⟨963611, by rfl⟩ : syracuseStep 1284815 = 1927223) B1927223
theorem B3472091 : Blo 1283960 3472091 := bstep (se 1 (by rfl) ⟨2604068, by rfl⟩ : syracuseStep 3472091 = 5208137) B5208137
theorem B1284967 : Blo 1283960 1284967 := bstep (se 1 (by rfl) ⟨963725, by rfl⟩ : syracuseStep 1284967 = 1927451) B1927451
theorem B16464829 : Blo 1283960 16464829 := bstep (se 3 (by rfl) ⟨3087155, by rfl⟩ : syracuseStep 16464829 = 6174311) B6174311
theorem B2890745 : Blo 1283960 2890745 := bstep (se 2 (by rfl) ⟨1084029, by rfl⟩ : syracuseStep 2890745 = 2168059) B2168059
theorem B10976417 : Blo 1283960 10976417 := bstep (se 2 (by rfl) ⟨4116156, by rfl⟩ : syracuseStep 10976417 = 8232313) B8232313
theorem B1391791 : Blo 1283960 1391791 := bstep (se 1 (by rfl) ⟨1043843, by rfl⟩ : syracuseStep 1391791 = 2087687) B2087687
theorem B4398305 : Blo 1283960 4398305 := bstep (se 2 (by rfl) ⟨1649364, by rfl⟩ : syracuseStep 4398305 = 3298729) B3298729
theorem B7314695 : Blo 1283960 7314695 := bstep (se 1 (by rfl) ⟨5486021, by rfl⟩ : syracuseStep 7314695 = 10972043) B10972043
theorem B4882463 : Blo 1283960 4882463 := bstep (se 1 (by rfl) ⟨3661847, by rfl⟩ : syracuseStep 4882463 = 7323695) B7323695
theorem B2891897 : Blo 1283960 2891897 := bstep (se 2 (by rfl) ⟨1084461, by rfl⟩ : syracuseStep 2891897 = 2168923) B2168923
theorem B3252383 : Blo 1283960 3252383 := bstep (se 1 (by rfl) ⟨2439287, by rfl⟩ : syracuseStep 3252383 = 4878575) B4878575
theorem B2891951 : Blo 1283960 2891951 := bstep (se 1 (by rfl) ⟨2168963, by rfl⟩ : syracuseStep 2891951 = 4337927) B4337927
theorem B12345547 : Blo 1283960 12345547 := bstep (se 1 (by rfl) ⟨9259160, by rfl⟩ : syracuseStep 12345547 = 18518321) B18518321
theorem B2744617 : Blo 1283960 2744617 := bstep (se 2 (by rfl) ⟨1029231, by rfl⟩ : syracuseStep 2744617 = 2058463) B2058463
theorem B2892095 : Blo 1283960 2892095 := bstep (se 1 (by rfl) ⟨2169071, by rfl⟩ : syracuseStep 2892095 = 4338143) B4338143
theorem B3711545 : Blo 1283960 3711545 := bstep (se 2 (by rfl) ⟨1391829, by rfl⟩ : syracuseStep 3711545 = 2783659) B2783659
theorem B5489491 : Blo 1283960 5489491 := bstep (se 1 (by rfl) ⟨4117118, by rfl⟩ : syracuseStep 5489491 = 8234237) B8234237
theorem B2892743 : Blo 1283960 2892743 := bstep (se 1 (by rfl) ⟨2169557, by rfl⟩ : syracuseStep 2892743 = 4339115) B4339115
theorem B3253355 : Blo 1283960 3253355 := bstep (se 1 (by rfl) ⟨2440016, by rfl⟩ : syracuseStep 3253355 = 4880033) B4880033
theorem B5563711 : Blo 1283960 5563711 := bstep (se 1 (by rfl) ⟨4172783, by rfl⟩ : syracuseStep 5563711 = 8345567) B8345567
theorem B1926527 : Blo 1283960 1926527 := bstep (se 1 (by rfl) ⟨1444895, by rfl⟩ : syracuseStep 1926527 = 2889791) B2889791
theorem B1926635 : Blo 1283960 1926635 := bstep (se 1 (by rfl) ⟨1444976, by rfl⟩ : syracuseStep 1926635 = 2889953) B2889953
theorem B1927163 : Blo 1283960 1927163 := bstep (se 1 (by rfl) ⟨1445372, by rfl⟩ : syracuseStep 1927163 = 2890745) B2890745
theorem B7317611 : Blo 1283960 7317611 := bstep (se 1 (by rfl) ⟨5488208, by rfl⟩ : syracuseStep 7317611 = 10976417) B10976417
theorem B4876463 : Blo 1283960 4876463 := bstep (se 1 (by rfl) ⟨3657347, by rfl⟩ : syracuseStep 4876463 = 7314695) B7314695
theorem B12356003 : Blo 1283960 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B66734597 : Blo 1283960 66734597 := bstep (se 4 (by rfl) ⟨6256368, by rfl⟩ : syracuseStep 66734597 = 12512737) B12512737
theorem B1444603 : Blo 1283960 1444603 := bstep (se 1 (by rfl) ⟨1083452, by rfl⟩ : syracuseStep 1444603 = 2166905) B2166905
theorem B24685559 : Blo 1283960 24685559 := bstep (se 1 (by rfl) ⟨18514169, by rfl⟩ : syracuseStep 24685559 = 37028339) B37028339
theorem B4336631 : Blo 1283960 4336631 := bstep (se 1 (by rfl) ⟨3252473, by rfl⟩ : syracuseStep 4336631 = 6504947) B6504947
theorem B2198639 : Blo 1283960 2198639 := bstep (se 1 (by rfl) ⟨1648979, by rfl⟩ : syracuseStep 2198639 = 3297959) B3297959
theorem B5213339 : Blo 1283960 5213339 := bstep (se 1 (by rfl) ⟨3910004, by rfl⟩ : syracuseStep 5213339 = 7820009) B7820009
theorem B6507863 : Blo 1283960 6507863 := bstep (se 1 (by rfl) ⟨4880897, by rfl⟩ : syracuseStep 6507863 = 9761795) B9761795
theorem B1625447 : Blo 1283960 1625447 := bstep (se 1 (by rfl) ⟨1219085, by rfl⟩ : syracuseStep 1625447 = 2438171) B2438171
theorem B4632233 : Blo 1283960 4632233 := bstep (se 2 (by rfl) ⟨1737087, by rfl⟩ : syracuseStep 4632233 = 3474175) B3474175
theorem B3706555 : Blo 1283960 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B5492447 : Blo 1283960 5492447 := bstep (se 1 (by rfl) ⟨4119335, by rfl⟩ : syracuseStep 5492447 = 8238671) B8238671
theorem B6688651 : Blo 1283960 6688651 := bstep (se 1 (by rfl) ⟨5016488, by rfl⟩ : syracuseStep 6688651 = 10032977) B10032977
theorem B1855721 : Blo 1283960 1855721 := bstep (se 2 (by rfl) ⟨695895, by rfl⟩ : syracuseStep 1855721 = 1391791) B1391791
theorem B1372411 : Blo 1283960 1372411 := bstep (se 1 (by rfl) ⟨1029308, by rfl⟩ : syracuseStep 1372411 = 2058617) B2058617
theorem B4878589 : Blo 1283960 4878589 := bstep (se 3 (by rfl) ⟨914735, by rfl⟩ : syracuseStep 4878589 = 1829471) B1829471
theorem B46911869 : Blo 1283960 46911869 := bstep (se 3 (by rfl) ⟨8795975, by rfl⟩ : syracuseStep 46911869 = 17591951) B17591951
theorem B2314727 : Blo 1283960 2314727 := bstep (se 1 (by rfl) ⟨1736045, by rfl⟩ : syracuseStep 2314727 = 3472091) B3472091
theorem B2438255 : Blo 1283960 2438255 := bstep (se 1 (by rfl) ⟨1828691, by rfl⟩ : syracuseStep 2438255 = 3657383) B3657383
theorem B2889017 : Blo 1283960 2889017 := bstep (se 2 (by rfl) ⟨1083381, by rfl⟩ : syracuseStep 2889017 = 2166763) B2166763
theorem B2168167 : Blo 1283960 2168167 := bstep (se 1 (by rfl) ⟨1626125, by rfl⟩ : syracuseStep 2168167 = 3252251) B3252251
theorem B2889449 : Blo 1283960 2889449 := bstep (se 2 (by rfl) ⟨1083543, by rfl⟩ : syracuseStep 2889449 = 2167087) B2167087
theorem B7419671 : Blo 1283960 7419671 := bstep (se 1 (by rfl) ⟨5564753, by rfl⟩ : syracuseStep 7419671 = 11129507) B11129507
theorem B11728813 : Blo 1283960 11728813 := bstep (se 3 (by rfl) ⟨2199152, by rfl⟩ : syracuseStep 11728813 = 4398305) B4398305
theorem B39557159 : Blo 1283960 39557159 := bstep (se 1 (by rfl) ⟨29667869, by rfl⟩ : syracuseStep 39557159 = 59335739) B59335739
theorem B1284143 : Blo 1283960 1284143 := bstep (se 1 (by rfl) ⟨963107, by rfl⟩ : syracuseStep 1284143 = 1926215) B1926215
theorem B1284159 : Blo 1283960 1284159 := bstep (se 1 (by rfl) ⟨963119, by rfl⟩ : syracuseStep 1284159 = 1926239) B1926239
theorem B1284187 : Blo 1283960 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B1284263 : Blo 1283960 1284263 := bstep (se 1 (by rfl) ⟨963197, by rfl⟩ : syracuseStep 1284263 = 1926395) B1926395
theorem B4340087 : Blo 1283960 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B49404329 : Blo 1283960 49404329 := bstep (se 2 (by rfl) ⟨18526623, by rfl⟩ : syracuseStep 49404329 = 37053247) B37053247
theorem B1284607 : Blo 1283960 1284607 := bstep (se 1 (by rfl) ⟨963455, by rfl⟩ : syracuseStep 1284607 = 1926911) B1926911
theorem B2890295 : Blo 1283960 2890295 := bstep (se 1 (by rfl) ⟨2167721, by rfl⟩ : syracuseStep 2890295 = 4335443) B4335443
theorem B21953105 : Blo 1283960 21953105 := bstep (se 2 (by rfl) ⟨8232414, by rfl⟩ : syracuseStep 21953105 = 16464829) B16464829
theorem B4881005 : Blo 1283960 4881005 := bstep (se 3 (by rfl) ⟨915188, by rfl⟩ : syracuseStep 4881005 = 1830377) B1830377
theorem B1285055 : Blo 1283960 1285055 := bstep (se 1 (by rfl) ⟨963791, by rfl⟩ : syracuseStep 1285055 = 1927583) B1927583
theorem B9264235 : Blo 1283960 9264235 := bstep (se 1 (by rfl) ⟨6948176, by rfl⟩ : syracuseStep 9264235 = 13896353) B13896353
theorem B1285423 : Blo 1283960 1285423 := bstep (se 1 (by rfl) ⟨964067, by rfl⟩ : syracuseStep 1285423 = 1928135) B1928135
theorem B1285883 : Blo 1283960 1285883 := bstep (se 1 (by rfl) ⟨964412, by rfl⟩ : syracuseStep 1285883 = 1928825) B1928825
theorem B6504785 : Blo 1283960 6504785 := bstep (se 2 (by rfl) ⟨2439294, by rfl⟩ : syracuseStep 6504785 = 4878589) B4878589
theorem B2474363 : Blo 1283960 2474363 := bstep (se 1 (by rfl) ⟨1855772, by rfl⟩ : syracuseStep 2474363 = 3711545) B3711545
theorem B4948589 : Blo 1283960 4948589 := bstep (se 3 (by rfl) ⟨927860, by rfl⟩ : syracuseStep 4948589 = 1855721) B1855721
theorem B1926011 : Blo 1283960 1926011 := bstep (se 1 (by rfl) ⟨1444508, by rfl⟩ : syracuseStep 1926011 = 2889017) B2889017
theorem B4334525 : Blo 1283960 4334525 := bstep (se 3 (by rfl) ⟨812723, by rfl⟩ : syracuseStep 4334525 = 1625447) B1625447
theorem B1926137 : Blo 1283960 1926137 := bstep (se 2 (by rfl) ⟨722301, by rfl⟩ : syracuseStep 1926137 = 1444603) B1444603
theorem B32949341 : Blo 1283960 32949341 := bstep (se 3 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 32949341 = 12356003) B12356003
theorem B1926299 : Blo 1283960 1926299 := bstep (se 1 (by rfl) ⟨1444724, by rfl⟩ : syracuseStep 1926299 = 2889449) B2889449
theorem B26371439 : Blo 1283960 26371439 := bstep (se 1 (by rfl) ⟨19778579, by rfl⟩ : syracuseStep 26371439 = 39557159) B39557159
theorem B2893391 : Blo 1283960 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B29673125 : Blo 1283960 29673125 := bstep (se 4 (by rfl) ⟨2781855, by rfl⟩ : syracuseStep 29673125 = 5563711) B5563711
theorem B1926863 : Blo 1283960 1926863 := bstep (se 1 (by rfl) ⟨1445147, by rfl⟩ : syracuseStep 1926863 = 2890295) B2890295
theorem B3254003 : Blo 1283960 3254003 := bstep (se 1 (by rfl) ⟨2440502, by rfl⟩ : syracuseStep 3254003 = 4881005) B4881005
theorem B3475559 : Blo 1283960 3475559 := bstep (se 1 (by rfl) ⟨2606669, by rfl⟩ : syracuseStep 3475559 = 5213339) B5213339
theorem B4942073 : Blo 1283960 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B3254975 : Blo 1283960 3254975 := bstep (se 1 (by rfl) ⟨2441231, by rfl⟩ : syracuseStep 3254975 = 4882463) B4882463
theorem B1927931 : Blo 1283960 1927931 := bstep (se 1 (by rfl) ⟨1445948, by rfl⟩ : syracuseStep 1927931 = 2891897) B2891897
theorem B1927967 : Blo 1283960 1927967 := bstep (se 1 (by rfl) ⟨1445975, by rfl⟩ : syracuseStep 1927967 = 2891951) B2891951
theorem B1928063 : Blo 1283960 1928063 := bstep (se 1 (by rfl) ⟨1446047, by rfl⟩ : syracuseStep 1928063 = 2892095) B2892095
theorem B16460729 : Blo 1283960 16460729 := bstep (se 2 (by rfl) ⟨6172773, by rfl⟩ : syracuseStep 16460729 = 12345547) B12345547
theorem B1543151 : Blo 1283960 1543151 := bstep (se 1 (by rfl) ⟨1157363, by rfl⟩ : syracuseStep 1543151 = 2314727) B2314727
theorem B1829881 : Blo 1283960 1829881 := bstep (se 2 (by rfl) ⟨686205, by rfl⟩ : syracuseStep 1829881 = 1372411) B1372411
theorem B1928495 : Blo 1283960 1928495 := bstep (se 1 (by rfl) ⟨1446371, by rfl⟩ : syracuseStep 1928495 = 2892743) B2892743
theorem B1625503 : Blo 1283960 1625503 := bstep (se 1 (by rfl) ⟨1219127, by rfl⟩ : syracuseStep 1625503 = 2438255) B2438255
theorem B7319321 : Blo 1283960 7319321 := bstep (se 2 (by rfl) ⟨2744745, by rfl⟩ : syracuseStep 7319321 = 5489491) B5489491
theorem B4878407 : Blo 1283960 4878407 := bstep (se 1 (by rfl) ⟨3658805, by rfl⟩ : syracuseStep 4878407 = 7317611) B7317611
theorem B32936219 : Blo 1283960 32936219 := bstep (se 1 (by rfl) ⟨24702164, by rfl⟩ : syracuseStep 32936219 = 49404329) B49404329
theorem B14635403 : Blo 1283960 14635403 := bstep (se 1 (by rfl) ⟨10976552, by rfl⟩ : syracuseStep 14635403 = 21953105) B21953105
theorem B4338575 : Blo 1283960 4338575 := bstep (se 1 (by rfl) ⟨3253931, by rfl⟩ : syracuseStep 4338575 = 6507863) B6507863
theorem B8918201 : Blo 1283960 8918201 := bstep (se 2 (by rfl) ⟨3344325, by rfl⟩ : syracuseStep 8918201 = 6688651) B6688651
theorem B2168255 : Blo 1283960 2168255 := bstep (se 1 (by rfl) ⟨1626191, by rfl⟩ : syracuseStep 2168255 = 3252383) B3252383
theorem B31274579 : Blo 1283960 31274579 := bstep (se 1 (by rfl) ⟨23455934, by rfl⟩ : syracuseStep 31274579 = 46911869) B46911869
theorem B3659489 : Blo 1283960 3659489 := bstep (se 2 (by rfl) ⟨1372308, by rfl⟩ : syracuseStep 3659489 = 2744617) B2744617
theorem B2168903 : Blo 1283960 2168903 := bstep (se 1 (by rfl) ⟨1626677, by rfl⟩ : syracuseStep 2168903 = 3253355) B3253355
theorem B1284351 : Blo 1283960 1284351 := bstep (se 1 (by rfl) ⟨963263, by rfl⟩ : syracuseStep 1284351 = 1926527) B1926527
theorem B1284423 : Blo 1283960 1284423 := bstep (se 1 (by rfl) ⟨963317, by rfl⟩ : syracuseStep 1284423 = 1926635) B1926635
theorem B4946447 : Blo 1283960 4946447 := bstep (se 1 (by rfl) ⟨3709835, by rfl⟩ : syracuseStep 4946447 = 7419671) B7419671
theorem B1284775 : Blo 1283960 1284775 := bstep (se 1 (by rfl) ⟨963581, by rfl⟩ : syracuseStep 1284775 = 1927163) B1927163
theorem B3250975 : Blo 1283960 3250975 := bstep (se 1 (by rfl) ⟨2438231, by rfl⟩ : syracuseStep 3250975 = 4876463) B4876463
theorem B12352313 : Blo 1283960 12352313 := bstep (se 2 (by rfl) ⟨4632117, by rfl⟩ : syracuseStep 12352313 = 9264235) B9264235
theorem B44489731 : Blo 1283960 44489731 := bstep (se 1 (by rfl) ⟨33367298, by rfl⟩ : syracuseStep 44489731 = 66734597) B66734597
theorem B12352621 : Blo 1283960 12352621 := bstep (se 3 (by rfl) ⟨2316116, by rfl⟩ : syracuseStep 12352621 = 4632233) B4632233
theorem B2890889 : Blo 1283960 2890889 := bstep (se 2 (by rfl) ⟨1084083, by rfl⟩ : syracuseStep 2890889 = 2168167) B2168167
theorem B16457039 : Blo 1283960 16457039 := bstep (se 1 (by rfl) ⟨12342779, by rfl⟩ : syracuseStep 16457039 = 24685559) B24685559
theorem B2891087 : Blo 1283960 2891087 := bstep (se 1 (by rfl) ⟨2168315, by rfl⟩ : syracuseStep 2891087 = 4336631) B4336631
theorem B1465759 : Blo 1283960 1465759 := bstep (se 1 (by rfl) ⟨1099319, by rfl⟩ : syracuseStep 1465759 = 2198639) B2198639
theorem B3661631 : Blo 1283960 3661631 := bstep (se 1 (by rfl) ⟨2746223, by rfl⟩ : syracuseStep 3661631 = 5492447) B5492447
theorem B15638417 : Blo 1283960 15638417 := bstep (se 2 (by rfl) ⟨5864406, by rfl⟩ : syracuseStep 15638417 = 11728813) B11728813
theorem B3252271 : Blo 1283960 3252271 := bstep (se 1 (by rfl) ⟨2439203, by rfl⟩ : syracuseStep 3252271 = 4878407) B4878407
theorem B9756935 : Blo 1283960 9756935 := bstep (se 1 (by rfl) ⟨7317701, by rfl⟩ : syracuseStep 9756935 = 14635403) B14635403
theorem B2892383 : Blo 1283960 2892383 := bstep (se 1 (by rfl) ⟨2169287, by rfl⟩ : syracuseStep 2892383 = 4338575) B4338575
theorem B17580959 : Blo 1283960 17580959 := bstep (se 1 (by rfl) ⟨13185719, by rfl⟩ : syracuseStep 17580959 = 26371439) B26371439
theorem B4334633 : Blo 1283960 4334633 := bstep (se 2 (by rfl) ⟨1625487, by rfl⟩ : syracuseStep 4334633 = 3250975) B3250975
theorem B20849719 : Blo 1283960 20849719 := bstep (se 1 (by rfl) ⟨15637289, by rfl⟩ : syracuseStep 20849719 = 31274579) B31274579
theorem B59319641 : Blo 1283960 59319641 := bstep (se 2 (by rfl) ⟨22244865, by rfl⟩ : syracuseStep 59319641 = 44489731) B44489731
theorem B13190525 : Blo 1283960 13190525 := bstep (se 3 (by rfl) ⟨2473223, by rfl⟩ : syracuseStep 13190525 = 4946447) B4946447
theorem B8234875 : Blo 1283960 8234875 := bstep (se 1 (by rfl) ⟨6176156, by rfl⟩ : syracuseStep 8234875 = 12352313) B12352313
theorem B1927259 : Blo 1283960 1927259 := bstep (se 1 (by rfl) ⟨1445444, by rfl⟩ : syracuseStep 1927259 = 2890889) B2890889
theorem B7817381 : Blo 1283960 7817381 := bstep (se 4 (by rfl) ⟨732879, by rfl⟩ : syracuseStep 7817381 = 1465759) B1465759
theorem B10971359 : Blo 1283960 10971359 := bstep (se 1 (by rfl) ⟨8228519, by rfl⟩ : syracuseStep 10971359 = 16457039) B16457039
theorem B1927391 : Blo 1283960 1927391 := bstep (se 1 (by rfl) ⟨1445543, by rfl⟩ : syracuseStep 1927391 = 2891087) B2891087
theorem B4115069 : Blo 1283960 4115069 := bstep (se 3 (by rfl) ⟨771575, by rfl⟩ : syracuseStep 4115069 = 1543151) B1543151
theorem B9759365 : Blo 1283960 9759365 := bstep (se 4 (by rfl) ⟨914940, by rfl⟩ : syracuseStep 9759365 = 1829881) B1829881
theorem B21957479 : Blo 1283960 21957479 := bstep (se 1 (by rfl) ⟨16468109, by rfl⟩ : syracuseStep 21957479 = 32936219) B32936219
theorem B4336523 : Blo 1283960 4336523 := bstep (se 1 (by rfl) ⟨3252392, by rfl⟩ : syracuseStep 4336523 = 6504785) B6504785
theorem B1649575 : Blo 1283960 1649575 := bstep (se 1 (by rfl) ⟨1237181, by rfl⟩ : syracuseStep 1649575 = 2474363) B2474363
theorem B9268157 : Blo 1283960 9268157 := bstep (se 3 (by rfl) ⟨1737779, by rfl⟩ : syracuseStep 9268157 = 3475559) B3475559
theorem B21966227 : Blo 1283960 21966227 := bstep (se 1 (by rfl) ⟨16474670, by rfl⟩ : syracuseStep 21966227 = 32949341) B32949341
theorem B1445503 : Blo 1283960 1445503 := bstep (se 1 (by rfl) ⟨1084127, by rfl⟩ : syracuseStep 1445503 = 2168255) B2168255
theorem B1928927 : Blo 1283960 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B1445935 : Blo 1283960 1445935 := bstep (se 1 (by rfl) ⟨1084451, by rfl⟩ : syracuseStep 1445935 = 2168903) B2168903
theorem B16470161 : Blo 1283960 16470161 := bstep (se 2 (by rfl) ⟨6176310, by rfl⟩ : syracuseStep 16470161 = 12352621) B12352621
theorem B2167337 : Blo 1283960 2167337 := bstep (se 2 (by rfl) ⟨812751, by rfl⟩ : syracuseStep 2167337 = 1625503) B1625503
theorem B10973819 : Blo 1283960 10973819 := bstep (se 1 (by rfl) ⟨8230364, by rfl⟩ : syracuseStep 10973819 = 16460729) B16460729
theorem B4879547 : Blo 1283960 4879547 := bstep (se 1 (by rfl) ⟨3659660, by rfl⟩ : syracuseStep 4879547 = 7319321) B7319321
theorem B10425611 : Blo 1283960 10425611 := bstep (se 1 (by rfl) ⟨7819208, by rfl⟩ : syracuseStep 10425611 = 15638417) B15638417
theorem B3299059 : Blo 1283960 3299059 := bstep (se 1 (by rfl) ⟨2474294, by rfl⟩ : syracuseStep 3299059 = 4948589) B4948589
theorem B1284007 : Blo 1283960 1284007 := bstep (se 1 (by rfl) ⟨963005, by rfl⟩ : syracuseStep 1284007 = 1926011) B1926011
theorem B2889683 : Blo 1283960 2889683 := bstep (se 1 (by rfl) ⟨2167262, by rfl⟩ : syracuseStep 2889683 = 4334525) B4334525
theorem B13178861 : Blo 1283960 13178861 := bstep (se 3 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 13178861 = 4942073) B4942073
theorem B1284091 : Blo 1283960 1284091 := bstep (se 1 (by rfl) ⟨963068, by rfl⟩ : syracuseStep 1284091 = 1926137) B1926137
theorem B1284199 : Blo 1283960 1284199 := bstep (se 1 (by rfl) ⟨963149, by rfl⟩ : syracuseStep 1284199 = 1926299) B1926299
theorem B5945467 : Blo 1283960 5945467 := bstep (se 1 (by rfl) ⟨4459100, by rfl⟩ : syracuseStep 5945467 = 8918201) B8918201
theorem B19782083 : Blo 1283960 19782083 := bstep (se 1 (by rfl) ⟨14836562, by rfl⟩ : syracuseStep 19782083 = 29673125) B29673125
theorem B1284575 : Blo 1283960 1284575 := bstep (se 1 (by rfl) ⟨963431, by rfl⟩ : syracuseStep 1284575 = 1926863) B1926863
theorem B2439659 : Blo 1283960 2439659 := bstep (se 1 (by rfl) ⟨1829744, by rfl⟩ : syracuseStep 2439659 = 3659489) B3659489
theorem B2169335 : Blo 1283960 2169335 := bstep (se 1 (by rfl) ⟨1627001, by rfl⟩ : syracuseStep 2169335 = 3254003) B3254003
theorem B2169983 : Blo 1283960 2169983 := bstep (se 1 (by rfl) ⟨1627487, by rfl⟩ : syracuseStep 2169983 = 3254975) B3254975
theorem B1285287 : Blo 1283960 1285287 := bstep (se 1 (by rfl) ⟨963965, by rfl⟩ : syracuseStep 1285287 = 1927931) B1927931
theorem B1285311 : Blo 1283960 1285311 := bstep (se 1 (by rfl) ⟨963983, by rfl⟩ : syracuseStep 1285311 = 1927967) B1927967
theorem B1285375 : Blo 1283960 1285375 := bstep (se 1 (by rfl) ⟨964031, by rfl⟩ : syracuseStep 1285375 = 1928063) B1928063
theorem B1285663 : Blo 1283960 1285663 := bstep (se 1 (by rfl) ⟨964247, by rfl⟩ : syracuseStep 1285663 = 1928495) B1928495
theorem B2441087 : Blo 1283960 2441087 := bstep (se 1 (by rfl) ⟨1830815, by rfl⟩ : syracuseStep 2441087 = 3661631) B3661631
theorem B6504623 : Blo 1283960 6504623 := bstep (se 1 (by rfl) ⟨4878467, by rfl⟩ : syracuseStep 6504623 = 9756935) B9756935
theorem B7315879 : Blo 1283960 7315879 := bstep (se 1 (by rfl) ⟨5486909, by rfl⟩ : syracuseStep 7315879 = 10973819) B10973819
theorem B3253031 : Blo 1283960 3253031 := bstep (se 1 (by rfl) ⟨2439773, by rfl⟩ : syracuseStep 3253031 = 4879547) B4879547
theorem B6505757 : Blo 1283960 6505757 := bstep (se 3 (by rfl) ⟨1219829, by rfl⟩ : syracuseStep 6505757 = 2439659) B2439659
theorem B1926455 : Blo 1283960 1926455 := bstep (se 1 (by rfl) ⟨1444841, by rfl⟩ : syracuseStep 1926455 = 2889683) B2889683
theorem B5211587 : Blo 1283960 5211587 := bstep (se 1 (by rfl) ⟨3908690, by rfl⟩ : syracuseStep 5211587 = 7817381) B7817381
theorem B6506243 : Blo 1283960 6506243 := bstep (se 1 (by rfl) ⟨4879682, by rfl⟩ : syracuseStep 6506243 = 9759365) B9759365
theorem B6178771 : Blo 1283960 6178771 := bstep (se 1 (by rfl) ⟨4634078, by rfl⟩ : syracuseStep 6178771 = 9268157) B9268157
theorem B1927337 : Blo 1283960 1927337 := bstep (se 2 (by rfl) ⟨722751, by rfl⟩ : syracuseStep 1927337 = 1445503) B1445503
theorem B10979833 : Blo 1283960 10979833 := bstep (se 2 (by rfl) ⟨4117437, by rfl⟩ : syracuseStep 10979833 = 8234875) B8234875
theorem B4336361 : Blo 1283960 4336361 := bstep (se 2 (by rfl) ⟨1626135, by rfl⟩ : syracuseStep 4336361 = 3252271) B3252271
theorem B1927913 : Blo 1283960 1927913 := bstep (se 2 (by rfl) ⟨722967, by rfl⟩ : syracuseStep 1927913 = 1445935) B1445935
theorem B10980107 : Blo 1283960 10980107 := bstep (se 1 (by rfl) ⟨8235080, by rfl⟩ : syracuseStep 10980107 = 16470161) B16470161
theorem B1444891 : Blo 1283960 1444891 := bstep (se 1 (by rfl) ⟨1083668, by rfl⟩ : syracuseStep 1444891 = 2167337) B2167337
theorem B1928255 : Blo 1283960 1928255 := bstep (se 1 (by rfl) ⟨1446191, by rfl⟩ : syracuseStep 1928255 = 2892383) B2892383
theorem B6950407 : Blo 1283960 6950407 := bstep (se 1 (by rfl) ⟨5212805, by rfl⟩ : syracuseStep 6950407 = 10425611) B10425611
theorem B8793683 : Blo 1283960 8793683 := bstep (se 1 (by rfl) ⟨6595262, by rfl⟩ : syracuseStep 8793683 = 13190525) B13190525
theorem B8785907 : Blo 1283960 8785907 := bstep (se 1 (by rfl) ⟨6589430, by rfl⟩ : syracuseStep 8785907 = 13178861) B13178861
theorem B27799625 : Blo 1283960 27799625 := bstep (se 2 (by rfl) ⟨10424859, by rfl⟩ : syracuseStep 27799625 = 20849719) B20849719
theorem B1446223 : Blo 1283960 1446223 := bstep (se 1 (by rfl) ⟨1084667, by rfl⟩ : syracuseStep 1446223 = 2169335) B2169335
theorem B1446655 : Blo 1283960 1446655 := bstep (se 1 (by rfl) ⟨1084991, by rfl⟩ : syracuseStep 1446655 = 2169983) B2169983
theorem B14644151 : Blo 1283960 14644151 := bstep (se 1 (by rfl) ⟨10983113, by rfl⟩ : syracuseStep 14644151 = 21966227) B21966227
theorem B1627391 : Blo 1283960 1627391 := bstep (se 1 (by rfl) ⟨1220543, by rfl⟩ : syracuseStep 1627391 = 2441087) B2441087
theorem B7927289 : Blo 1283960 7927289 := bstep (se 2 (by rfl) ⟨2972733, by rfl⟩ : syracuseStep 7927289 = 5945467) B5945467
theorem B11720639 : Blo 1283960 11720639 := bstep (se 1 (by rfl) ⟨8790479, by rfl⟩ : syracuseStep 11720639 = 17580959) B17580959
theorem B2889755 : Blo 1283960 2889755 := bstep (se 1 (by rfl) ⟨2167316, by rfl⟩ : syracuseStep 2889755 = 4334633) B4334633
theorem B158185709 : Blo 1283960 158185709 := bstep (se 3 (by rfl) ⟨29659820, by rfl⟩ : syracuseStep 158185709 = 59319641) B59319641
theorem B1284839 : Blo 1283960 1284839 := bstep (se 1 (by rfl) ⟨963629, by rfl⟩ : syracuseStep 1284839 = 1927259) B1927259
theorem B7314239 : Blo 1283960 7314239 := bstep (se 1 (by rfl) ⟨5485679, by rfl⟩ : syracuseStep 7314239 = 10971359) B10971359
theorem B1284927 : Blo 1283960 1284927 := bstep (se 1 (by rfl) ⟨963695, by rfl⟩ : syracuseStep 1284927 = 1927391) B1927391
theorem B13188055 : Blo 1283960 13188055 := bstep (se 1 (by rfl) ⟨9891041, by rfl⟩ : syracuseStep 13188055 = 19782083) B19782083
theorem B2743379 : Blo 1283960 2743379 := bstep (se 1 (by rfl) ⟨2057534, by rfl⟩ : syracuseStep 2743379 = 4115069) B4115069
theorem B14638319 : Blo 1283960 14638319 := bstep (se 1 (by rfl) ⟨10978739, by rfl⟩ : syracuseStep 14638319 = 21957479) B21957479
theorem B2891015 : Blo 1283960 2891015 := bstep (se 1 (by rfl) ⟨2168261, by rfl⟩ : syracuseStep 2891015 = 4336523) B4336523
theorem B8797733 : Blo 1283960 8797733 := bstep (se 4 (by rfl) ⟨824787, by rfl⟩ : syracuseStep 8797733 = 1649575) B1649575
theorem B4398745 : Blo 1283960 4398745 := bstep (se 2 (by rfl) ⟨1649529, by rfl⟩ : syracuseStep 4398745 = 3299059) B3299059
theorem B1285951 : Blo 1283960 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B14639777 : Blo 1283960 14639777 := bstep (se 2 (by rfl) ⟨5489916, by rfl⟩ : syracuseStep 14639777 = 10979833) B10979833
theorem B1926503 : Blo 1283960 1926503 := bstep (se 1 (by rfl) ⟨1444877, by rfl⟩ : syracuseStep 1926503 = 2889755) B2889755
theorem B1926521 : Blo 1283960 1926521 := bstep (se 2 (by rfl) ⟨722445, by rfl⟩ : syracuseStep 1926521 = 1444891) B1444891
theorem B105457139 : Blo 1283960 105457139 := bstep (se 1 (by rfl) ⟨79092854, by rfl⟩ : syracuseStep 105457139 = 158185709) B158185709
theorem B4876159 : Blo 1283960 4876159 := bstep (se 1 (by rfl) ⟨3657119, by rfl⟩ : syracuseStep 4876159 = 7314239) B7314239
theorem B9267209 : Blo 1283960 9267209 := bstep (se 2 (by rfl) ⟨3475203, by rfl⟩ : syracuseStep 9267209 = 6950407) B6950407
theorem B1828919 : Blo 1283960 1828919 := bstep (se 1 (by rfl) ⟨1371689, by rfl⟩ : syracuseStep 1828919 = 2743379) B2743379
theorem B9758879 : Blo 1283960 9758879 := bstep (se 1 (by rfl) ⟨7319159, by rfl⟩ : syracuseStep 9758879 = 14638319) B14638319
theorem B1927343 : Blo 1283960 1927343 := bstep (se 1 (by rfl) ⟨1445507, by rfl⟩ : syracuseStep 1927343 = 2891015) B2891015
theorem B18533083 : Blo 1283960 18533083 := bstep (se 1 (by rfl) ⟨13899812, by rfl⟩ : syracuseStep 18533083 = 27799625) B27799625
theorem B4336415 : Blo 1283960 4336415 := bstep (se 1 (by rfl) ⟨3252311, by rfl⟩ : syracuseStep 4336415 = 6504623) B6504623
theorem B1928297 : Blo 1283960 1928297 := bstep (se 2 (by rfl) ⟨723111, by rfl⟩ : syracuseStep 1928297 = 1446223) B1446223
theorem B4337171 : Blo 1283960 4337171 := bstep (se 1 (by rfl) ⟨3252878, by rfl⟩ : syracuseStep 4337171 = 6505757) B6505757
theorem B1928873 : Blo 1283960 1928873 := bstep (se 2 (by rfl) ⟨723327, by rfl⟩ : syracuseStep 1928873 = 1446655) B1446655
theorem B4337495 : Blo 1283960 4337495 := bstep (se 1 (by rfl) ⟨3253121, by rfl⟩ : syracuseStep 4337495 = 6506243) B6506243
theorem B13897565 : Blo 1283960 13897565 := bstep (se 3 (by rfl) ⟨2605793, by rfl⟩ : syracuseStep 13897565 = 5211587) B5211587
theorem B17584073 : Blo 1283960 17584073 := bstep (se 2 (by rfl) ⟨6594027, by rfl⟩ : syracuseStep 17584073 = 13188055) B13188055
theorem B7320071 : Blo 1283960 7320071 := bstep (se 1 (by rfl) ⟨5490053, by rfl⟩ : syracuseStep 7320071 = 10980107) B10980107
theorem B5862455 : Blo 1283960 5862455 := bstep (se 1 (by rfl) ⟨4396841, by rfl⟩ : syracuseStep 5862455 = 8793683) B8793683
theorem B8238361 : Blo 1283960 8238361 := bstep (se 2 (by rfl) ⟨3089385, by rfl⟩ : syracuseStep 8238361 = 6178771) B6178771
theorem B2168687 : Blo 1283960 2168687 := bstep (se 1 (by rfl) ⟨1626515, by rfl⟩ : syracuseStep 2168687 = 3253031) B3253031
theorem B9754505 : Blo 1283960 9754505 := bstep (se 2 (by rfl) ⟨3657939, by rfl⟩ : syracuseStep 9754505 = 7315879) B7315879
theorem B9762767 : Blo 1283960 9762767 := bstep (se 1 (by rfl) ⟨7322075, by rfl⟩ : syracuseStep 9762767 = 14644151) B14644151
theorem B4339709 : Blo 1283960 4339709 := bstep (se 3 (by rfl) ⟨813695, by rfl⟩ : syracuseStep 4339709 = 1627391) B1627391
theorem B1284303 : Blo 1283960 1284303 := bstep (se 1 (by rfl) ⟨963227, by rfl⟩ : syracuseStep 1284303 = 1926455) B1926455
theorem B7813759 : Blo 1283960 7813759 := bstep (se 1 (by rfl) ⟨5860319, by rfl⟩ : syracuseStep 7813759 = 11720639) B11720639
theorem B1284891 : Blo 1283960 1284891 := bstep (se 1 (by rfl) ⟨963668, by rfl⟩ : syracuseStep 1284891 = 1927337) B1927337
theorem B2890907 : Blo 1283960 2890907 := bstep (se 1 (by rfl) ⟨2168180, by rfl⟩ : syracuseStep 2890907 = 4336361) B4336361
theorem B1285275 : Blo 1283960 1285275 := bstep (se 1 (by rfl) ⟨963956, by rfl⟩ : syracuseStep 1285275 = 1927913) B1927913
theorem B1285503 : Blo 1283960 1285503 := bstep (se 1 (by rfl) ⟨964127, by rfl⟩ : syracuseStep 1285503 = 1928255) B1928255
theorem B5864993 : Blo 1283960 5864993 := bstep (se 2 (by rfl) ⟨2199372, by rfl⟩ : syracuseStep 5864993 = 4398745) B4398745
theorem B5865155 : Blo 1283960 5865155 := bstep (se 1 (by rfl) ⟨4398866, by rfl⟩ : syracuseStep 5865155 = 8797733) B8797733
theorem B84557749 : Blo 1283960 84557749 := bstep (se 5 (by rfl) ⟨3963644, by rfl⟩ : syracuseStep 84557749 = 7927289) B7927289
theorem B5857271 : Blo 1283960 5857271 := bstep (se 1 (by rfl) ⟨4392953, by rfl⟩ : syracuseStep 5857271 = 8785907) B8785907
theorem B3908303 : Blo 1283960 3908303 := bstep (se 1 (by rfl) ⟨2931227, by rfl⟩ : syracuseStep 3908303 = 5862455) B5862455
theorem B70304759 : Blo 1283960 70304759 := bstep (se 1 (by rfl) ⟨52728569, by rfl⟩ : syracuseStep 70304759 = 105457139) B105457139
theorem B2893139 : Blo 1283960 2893139 := bstep (se 1 (by rfl) ⟨2169854, by rfl⟩ : syracuseStep 2893139 = 4339709) B4339709
theorem B6178139 : Blo 1283960 6178139 := bstep (se 1 (by rfl) ⟨4633604, by rfl⟩ : syracuseStep 6178139 = 9267209) B9267209
theorem B6505919 : Blo 1283960 6505919 := bstep (se 1 (by rfl) ⟨4879439, by rfl⟩ : syracuseStep 6505919 = 9758879) B9758879
theorem B1927271 : Blo 1283960 1927271 := bstep (se 1 (by rfl) ⟨1445453, by rfl⟩ : syracuseStep 1927271 = 2890907) B2890907
theorem B3909995 : Blo 1283960 3909995 := bstep (se 1 (by rfl) ⟨2932496, by rfl⟩ : syracuseStep 3909995 = 5864993) B5864993
theorem B3910103 : Blo 1283960 3910103 := bstep (se 1 (by rfl) ⟨2932577, by rfl⟩ : syracuseStep 3910103 = 5865155) B5865155
theorem B4877117 : Blo 1283960 4877117 := bstep (se 3 (by rfl) ⟨914459, by rfl⟩ : syracuseStep 4877117 = 1828919) B1828919
theorem B9759851 : Blo 1283960 9759851 := bstep (se 1 (by rfl) ⟨7319888, by rfl⟩ : syracuseStep 9759851 = 14639777) B14639777
theorem B24710777 : Blo 1283960 24710777 := bstep (se 2 (by rfl) ⟨9266541, by rfl⟩ : syracuseStep 24710777 = 18533083) B18533083
theorem B1445791 : Blo 1283960 1445791 := bstep (se 1 (by rfl) ⟨1084343, by rfl⟩ : syracuseStep 1445791 = 2168687) B2168687
theorem B6508511 : Blo 1283960 6508511 := bstep (se 1 (by rfl) ⟨4881383, by rfl⟩ : syracuseStep 6508511 = 9762767) B9762767
theorem B6501545 : Blo 1283960 6501545 := bstep (se 2 (by rfl) ⟨2438079, by rfl⟩ : syracuseStep 6501545 = 4876159) B4876159
theorem B112743665 : Blo 1283960 112743665 := bstep (se 2 (by rfl) ⟨42278874, by rfl⟩ : syracuseStep 112743665 = 84557749) B84557749
theorem B3904847 : Blo 1283960 3904847 := bstep (se 1 (by rfl) ⟨2928635, by rfl⟩ : syracuseStep 3904847 = 5857271) B5857271
theorem B4880047 : Blo 1283960 4880047 := bstep (se 1 (by rfl) ⟨3660035, by rfl⟩ : syracuseStep 4880047 = 7320071) B7320071
theorem B10418345 : Blo 1283960 10418345 := bstep (se 2 (by rfl) ⟨3906879, by rfl⟩ : syracuseStep 10418345 = 7813759) B7813759
theorem B1284335 : Blo 1283960 1284335 := bstep (se 1 (by rfl) ⟨963251, by rfl⟩ : syracuseStep 1284335 = 1926503) B1926503
theorem B1284347 : Blo 1283960 1284347 := bstep (se 1 (by rfl) ⟨963260, by rfl⟩ : syracuseStep 1284347 = 1926521) B1926521
theorem B6503003 : Blo 1283960 6503003 := bstep (se 1 (by rfl) ⟨4877252, by rfl⟩ : syracuseStep 6503003 = 9754505) B9754505
theorem B1284895 : Blo 1283960 1284895 := bstep (se 1 (by rfl) ⟨963671, by rfl⟩ : syracuseStep 1284895 = 1927343) B1927343
theorem B10984481 : Blo 1283960 10984481 := bstep (se 2 (by rfl) ⟨4119180, by rfl⟩ : syracuseStep 10984481 = 8238361) B8238361
theorem B2890943 : Blo 1283960 2890943 := bstep (se 1 (by rfl) ⟨2168207, by rfl⟩ : syracuseStep 2890943 = 4336415) B4336415
theorem B1285531 : Blo 1283960 1285531 := bstep (se 1 (by rfl) ⟨964148, by rfl⟩ : syracuseStep 1285531 = 1928297) B1928297
theorem B2891447 : Blo 1283960 2891447 := bstep (se 1 (by rfl) ⟨2168585, by rfl⟩ : syracuseStep 2891447 = 4337171) B4337171
theorem B1285915 : Blo 1283960 1285915 := bstep (se 1 (by rfl) ⟨964436, by rfl⟩ : syracuseStep 1285915 = 1928873) B1928873
theorem B2891663 : Blo 1283960 2891663 := bstep (se 1 (by rfl) ⟨2168747, by rfl⟩ : syracuseStep 2891663 = 4337495) B4337495
theorem B9265043 : Blo 1283960 9265043 := bstep (se 1 (by rfl) ⟨6948782, by rfl⟩ : syracuseStep 9265043 = 13897565) B13897565
theorem B11722715 : Blo 1283960 11722715 := bstep (se 1 (by rfl) ⟨8792036, by rfl⟩ : syracuseStep 11722715 = 17584073) B17584073
theorem B2605535 : Blo 1283960 2605535 := bstep (se 1 (by rfl) ⟨1954151, by rfl⟩ : syracuseStep 2605535 = 3908303) B3908303
theorem B4334363 : Blo 1283960 4334363 := bstep (se 1 (by rfl) ⟨3250772, by rfl⟩ : syracuseStep 4334363 = 6501545) B6501545
theorem B75162443 : Blo 1283960 75162443 := bstep (se 1 (by rfl) ⟨56371832, by rfl⟩ : syracuseStep 75162443 = 112743665) B112743665
theorem B2606663 : Blo 1283960 2606663 := bstep (se 1 (by rfl) ⟨1954997, by rfl⟩ : syracuseStep 2606663 = 3909995) B3909995
theorem B2606735 : Blo 1283960 2606735 := bstep (se 1 (by rfl) ⟨1955051, by rfl⟩ : syracuseStep 2606735 = 3910103) B3910103
theorem B4335335 : Blo 1283960 4335335 := bstep (se 1 (by rfl) ⟨3251501, by rfl⟩ : syracuseStep 4335335 = 6503003) B6503003
theorem B6506567 : Blo 1283960 6506567 := bstep (se 1 (by rfl) ⟨4879925, by rfl⟩ : syracuseStep 6506567 = 9759851) B9759851
theorem B1927295 : Blo 1283960 1927295 := bstep (se 1 (by rfl) ⟨1445471, by rfl⟩ : syracuseStep 1927295 = 2890943) B2890943
theorem B6506729 : Blo 1283960 6506729 := bstep (se 2 (by rfl) ⟨2440023, by rfl⟩ : syracuseStep 6506729 = 4880047) B4880047
theorem B1927631 : Blo 1283960 1927631 := bstep (se 1 (by rfl) ⟨1445723, by rfl⟩ : syracuseStep 1927631 = 2891447) B2891447
theorem B1927721 : Blo 1283960 1927721 := bstep (se 2 (by rfl) ⟨722895, by rfl⟩ : syracuseStep 1927721 = 1445791) B1445791
theorem B1927775 : Blo 1283960 1927775 := bstep (se 1 (by rfl) ⟨1445831, by rfl⟩ : syracuseStep 1927775 = 2891663) B2891663
theorem B46869839 : Blo 1283960 46869839 := bstep (se 1 (by rfl) ⟨35152379, by rfl⟩ : syracuseStep 46869839 = 70304759) B70304759
theorem B1928759 : Blo 1283960 1928759 := bstep (se 1 (by rfl) ⟨1446569, by rfl⟩ : syracuseStep 1928759 = 2893139) B2893139
theorem B4337279 : Blo 1283960 4337279 := bstep (se 1 (by rfl) ⟨3252959, by rfl⟩ : syracuseStep 4337279 = 6505919) B6505919
theorem B4339007 : Blo 1283960 4339007 := bstep (se 1 (by rfl) ⟨3254255, by rfl⟩ : syracuseStep 4339007 = 6508511) B6508511
theorem B2603231 : Blo 1283960 2603231 := bstep (se 1 (by rfl) ⟨1952423, by rfl⟩ : syracuseStep 2603231 = 3904847) B3904847
theorem B4118759 : Blo 1283960 4118759 := bstep (se 1 (by rfl) ⟨3089069, by rfl⟩ : syracuseStep 4118759 = 6178139) B6178139
theorem B1284847 : Blo 1283960 1284847 := bstep (se 1 (by rfl) ⟨963635, by rfl⟩ : syracuseStep 1284847 = 1927271) B1927271
theorem B6945563 : Blo 1283960 6945563 := bstep (se 1 (by rfl) ⟨5209172, by rfl⟩ : syracuseStep 6945563 = 10418345) B10418345
theorem B3251411 : Blo 1283960 3251411 := bstep (se 1 (by rfl) ⟨2438558, by rfl⟩ : syracuseStep 3251411 = 4877117) B4877117
theorem B7322987 : Blo 1283960 7322987 := bstep (se 1 (by rfl) ⟨5492240, by rfl⟩ : syracuseStep 7322987 = 10984481) B10984481
theorem B24706781 : Blo 1283960 24706781 := bstep (se 3 (by rfl) ⟨4632521, by rfl⟩ : syracuseStep 24706781 = 9265043) B9265043
theorem B16473851 : Blo 1283960 16473851 := bstep (se 1 (by rfl) ⟨12355388, by rfl⟩ : syracuseStep 16473851 = 24710777) B24710777
theorem B7815143 : Blo 1283960 7815143 := bstep (se 1 (by rfl) ⟨5861357, by rfl⟩ : syracuseStep 7815143 = 11722715) B11722715
theorem B1737023 : Blo 1283960 1737023 := bstep (se 1 (by rfl) ⟨1302767, by rfl⟩ : syracuseStep 1737023 = 2605535) B2605535
theorem B2892671 : Blo 1283960 2892671 := bstep (se 1 (by rfl) ⟨2169503, by rfl⟩ : syracuseStep 2892671 = 4339007) B4339007
theorem B1737775 : Blo 1283960 1737775 := bstep (se 1 (by rfl) ⟨1303331, by rfl⟩ : syracuseStep 1737775 = 2606663) B2606663
theorem B1737823 : Blo 1283960 1737823 := bstep (se 1 (by rfl) ⟨1303367, by rfl⟩ : syracuseStep 1737823 = 2606735) B2606735
theorem B2745839 : Blo 1283960 2745839 := bstep (se 1 (by rfl) ⟨2059379, by rfl⟩ : syracuseStep 2745839 = 4118759) B4118759
theorem B4630375 : Blo 1283960 4630375 := bstep (se 1 (by rfl) ⟨3472781, by rfl⟩ : syracuseStep 4630375 = 6945563) B6945563
theorem B31246559 : Blo 1283960 31246559 := bstep (se 1 (by rfl) ⟨23434919, by rfl⟩ : syracuseStep 31246559 = 46869839) B46869839
theorem B4337711 : Blo 1283960 4337711 := bstep (se 1 (by rfl) ⟨3253283, by rfl⟩ : syracuseStep 4337711 = 6506567) B6506567
theorem B4337819 : Blo 1283960 4337819 := bstep (se 1 (by rfl) ⟨3253364, by rfl⟩ : syracuseStep 4337819 = 6506729) B6506729
theorem B2167607 : Blo 1283960 2167607 := bstep (se 1 (by rfl) ⟨1625705, by rfl⟩ : syracuseStep 2167607 = 3251411) B3251411
theorem B16471187 : Blo 1283960 16471187 := bstep (se 1 (by rfl) ⟨12353390, by rfl⟩ : syracuseStep 16471187 = 24706781) B24706781
theorem B10982567 : Blo 1283960 10982567 := bstep (se 1 (by rfl) ⟨8236925, by rfl⟩ : syracuseStep 10982567 = 16473851) B16473851
theorem B2889575 : Blo 1283960 2889575 := bstep (se 1 (by rfl) ⟨2167181, by rfl⟩ : syracuseStep 2889575 = 4334363) B4334363
theorem B801732725 : Blo 1283960 801732725 := bstep (se 5 (by rfl) ⟨37581221, by rfl⟩ : syracuseStep 801732725 = 75162443) B75162443
theorem B2890223 : Blo 1283960 2890223 := bstep (se 1 (by rfl) ⟨2167667, by rfl⟩ : syracuseStep 2890223 = 4335335) B4335335
theorem B1284863 : Blo 1283960 1284863 := bstep (se 1 (by rfl) ⟨963647, by rfl⟩ : syracuseStep 1284863 = 1927295) B1927295
theorem B1735487 : Blo 1283960 1735487 := bstep (se 1 (by rfl) ⟨1301615, by rfl⟩ : syracuseStep 1735487 = 2603231) B2603231
theorem B1285087 : Blo 1283960 1285087 := bstep (se 1 (by rfl) ⟨963815, by rfl⟩ : syracuseStep 1285087 = 1927631) B1927631
theorem B1285147 : Blo 1283960 1285147 := bstep (se 1 (by rfl) ⟨963860, by rfl⟩ : syracuseStep 1285147 = 1927721) B1927721
theorem B1285183 : Blo 1283960 1285183 := bstep (se 1 (by rfl) ⟨963887, by rfl⟩ : syracuseStep 1285183 = 1927775) B1927775
theorem B4881991 : Blo 1283960 4881991 := bstep (se 1 (by rfl) ⟨3661493, by rfl⟩ : syracuseStep 4881991 = 7322987) B7322987
theorem B1285839 : Blo 1283960 1285839 := bstep (se 1 (by rfl) ⟨964379, by rfl⟩ : syracuseStep 1285839 = 1928759) B1928759
theorem B2891519 : Blo 1283960 2891519 := bstep (se 1 (by rfl) ⟨2168639, by rfl⟩ : syracuseStep 2891519 = 4337279) B4337279
theorem B5210095 : Blo 1283960 5210095 := bstep (se 1 (by rfl) ⟨3907571, by rfl⟩ : syracuseStep 5210095 = 7815143) B7815143
theorem B2891807 : Blo 1283960 2891807 := bstep (se 1 (by rfl) ⟨2168855, by rfl⟩ : syracuseStep 2891807 = 4337711) B4337711
theorem B2891879 : Blo 1283960 2891879 := bstep (se 1 (by rfl) ⟨2168909, by rfl⟩ : syracuseStep 2891879 = 4337819) B4337819
theorem B1926383 : Blo 1283960 1926383 := bstep (se 1 (by rfl) ⟨1444787, by rfl⟩ : syracuseStep 1926383 = 2889575) B2889575
theorem B534488483 : Blo 1283960 534488483 := bstep (se 1 (by rfl) ⟨400866362, by rfl⟩ : syracuseStep 534488483 = 801732725) B801732725
theorem B1926815 : Blo 1283960 1926815 := bstep (se 1 (by rfl) ⟨1445111, by rfl⟩ : syracuseStep 1926815 = 2890223) B2890223
theorem B1927679 : Blo 1283960 1927679 := bstep (se 1 (by rfl) ⟨1445759, by rfl⟩ : syracuseStep 1927679 = 2891519) B2891519
theorem B1445071 : Blo 1283960 1445071 := bstep (se 1 (by rfl) ⟨1083803, by rfl⟩ : syracuseStep 1445071 = 2167607) B2167607
theorem B1928447 : Blo 1283960 1928447 := bstep (se 1 (by rfl) ⟨1446335, by rfl⟩ : syracuseStep 1928447 = 2892671) B2892671
theorem B10980791 : Blo 1283960 10980791 := bstep (se 1 (by rfl) ⟨8235593, by rfl⟩ : syracuseStep 10980791 = 16471187) B16471187
theorem B4632061 : Blo 1283960 4632061 := bstep (se 3 (by rfl) ⟨868511, by rfl⟩ : syracuseStep 4632061 = 1737023) B1737023
theorem B6509321 : Blo 1283960 6509321 := bstep (se 2 (by rfl) ⟨2440995, by rfl⟩ : syracuseStep 6509321 = 4881991) B4881991
theorem B6173833 : Blo 1283960 6173833 := bstep (se 2 (by rfl) ⟨2315187, by rfl⟩ : syracuseStep 6173833 = 4630375) B4630375
theorem B7321711 : Blo 1283960 7321711 := bstep (se 1 (by rfl) ⟨5491283, by rfl⟩ : syracuseStep 7321711 = 10982567) B10982567
theorem B7322237 : Blo 1283960 7322237 := bstep (se 3 (by rfl) ⟨1372919, by rfl⟩ : syracuseStep 7322237 = 2745839) B2745839
theorem B2317033 : Blo 1283960 2317033 := bstep (se 2 (by rfl) ⟨868887, by rfl⟩ : syracuseStep 2317033 = 1737775) B1737775
theorem B2317097 : Blo 1283960 2317097 := bstep (se 2 (by rfl) ⟨868911, by rfl⟩ : syracuseStep 2317097 = 1737823) B1737823
theorem B20831039 : Blo 1283960 20831039 := bstep (se 1 (by rfl) ⟨15623279, by rfl⟩ : syracuseStep 20831039 = 31246559) B31246559
theorem B74047445 : Blo 1283960 74047445 := bstep (se 7 (by rfl) ⟨867743, by rfl⟩ : syracuseStep 74047445 = 1735487) B1735487
theorem B6946793 : Blo 1283960 6946793 := bstep (se 2 (by rfl) ⟨2605047, by rfl⟩ : syracuseStep 6946793 = 5210095) B5210095
theorem B3089377 : Blo 1283960 3089377 := bstep (se 2 (by rfl) ⟨1158516, by rfl⟩ : syracuseStep 3089377 = 2317033) B2317033
theorem B1926761 : Blo 1283960 1926761 := bstep (se 2 (by rfl) ⟨722535, by rfl⟩ : syracuseStep 1926761 = 1445071) B1445071
theorem B13887359 : Blo 1283960 13887359 := bstep (se 1 (by rfl) ⟨10415519, by rfl⟩ : syracuseStep 13887359 = 20831039) B20831039
theorem B6178925 : Blo 1283960 6178925 := bstep (se 3 (by rfl) ⟨1158548, by rfl⟩ : syracuseStep 6178925 = 2317097) B2317097
theorem B4631195 : Blo 1283960 4631195 := bstep (se 1 (by rfl) ⟨3473396, by rfl⟩ : syracuseStep 4631195 = 6946793) B6946793
theorem B1927871 : Blo 1283960 1927871 := bstep (se 1 (by rfl) ⟨1445903, by rfl⟩ : syracuseStep 1927871 = 2891807) B2891807
theorem B1927919 : Blo 1283960 1927919 := bstep (se 1 (by rfl) ⟨1445939, by rfl⟩ : syracuseStep 1927919 = 2891879) B2891879
theorem B7320527 : Blo 1283960 7320527 := bstep (se 1 (by rfl) ⟨5490395, by rfl⟩ : syracuseStep 7320527 = 10980791) B10980791
theorem B9762281 : Blo 1283960 9762281 := bstep (se 2 (by rfl) ⟨3660855, by rfl⟩ : syracuseStep 9762281 = 7321711) B7321711
theorem B4339547 : Blo 1283960 4339547 := bstep (se 1 (by rfl) ⟨3254660, by rfl⟩ : syracuseStep 4339547 = 6509321) B6509321
theorem B1284255 : Blo 1283960 1284255 := bstep (se 1 (by rfl) ⟨963191, by rfl⟩ : syracuseStep 1284255 = 1926383) B1926383
theorem B356325655 : Blo 1283960 356325655 := bstep (se 1 (by rfl) ⟨267244241, by rfl⟩ : syracuseStep 356325655 = 534488483) B534488483
theorem B1284543 : Blo 1283960 1284543 := bstep (se 1 (by rfl) ⟨963407, by rfl⟩ : syracuseStep 1284543 = 1926815) B1926815
theorem B8231777 : Blo 1283960 8231777 := bstep (se 2 (by rfl) ⟨3086916, by rfl⟩ : syracuseStep 8231777 = 6173833) B6173833
theorem B1285119 : Blo 1283960 1285119 := bstep (se 1 (by rfl) ⟨963839, by rfl⟩ : syracuseStep 1285119 = 1927679) B1927679
theorem B4881491 : Blo 1283960 4881491 := bstep (se 1 (by rfl) ⟨3661118, by rfl⟩ : syracuseStep 4881491 = 7322237) B7322237
theorem B6176081 : Blo 1283960 6176081 := bstep (se 2 (by rfl) ⟨2316030, by rfl⟩ : syracuseStep 6176081 = 4632061) B4632061
theorem B1285631 : Blo 1283960 1285631 := bstep (se 1 (by rfl) ⟨964223, by rfl⟩ : syracuseStep 1285631 = 1928447) B1928447
theorem B49364963 : Blo 1283960 49364963 := bstep (se 1 (by rfl) ⟨37023722, by rfl⟩ : syracuseStep 49364963 = 74047445) B74047445
theorem B2893031 : Blo 1283960 2893031 := bstep (se 1 (by rfl) ⟨2169773, by rfl⟩ : syracuseStep 2893031 = 4339547) B4339547
theorem B9258239 : Blo 1283960 9258239 := bstep (se 1 (by rfl) ⟨6943679, by rfl⟩ : syracuseStep 9258239 = 13887359) B13887359
theorem B3254327 : Blo 1283960 3254327 := bstep (se 1 (by rfl) ⟨2440745, by rfl⟩ : syracuseStep 3254327 = 4881491) B4881491
theorem B32909975 : Blo 1283960 32909975 := bstep (se 1 (by rfl) ⟨24682481, by rfl⟩ : syracuseStep 32909975 = 49364963) B49364963
theorem B6508187 : Blo 1283960 6508187 := bstep (se 1 (by rfl) ⟨4881140, by rfl⟩ : syracuseStep 6508187 = 9762281) B9762281
theorem B12349853 : Blo 1283960 12349853 := bstep (se 3 (by rfl) ⟨2315597, by rfl⟩ : syracuseStep 12349853 = 4631195) B4631195
theorem B4117387 : Blo 1283960 4117387 := bstep (se 1 (by rfl) ⟨3088040, by rfl⟩ : syracuseStep 4117387 = 6176081) B6176081
theorem B475100873 : Blo 1283960 475100873 := bstep (se 2 (by rfl) ⟨178162827, by rfl⟩ : syracuseStep 475100873 = 356325655) B356325655
theorem B4880351 : Blo 1283960 4880351 := bstep (se 1 (by rfl) ⟨3660263, by rfl⟩ : syracuseStep 4880351 = 7320527) B7320527
theorem B1284507 : Blo 1283960 1284507 := bstep (se 1 (by rfl) ⟨963380, by rfl⟩ : syracuseStep 1284507 = 1926761) B1926761
theorem B4119169 : Blo 1283960 4119169 := bstep (se 2 (by rfl) ⟨1544688, by rfl⟩ : syracuseStep 4119169 = 3089377) B3089377
theorem B4119283 : Blo 1283960 4119283 := bstep (se 1 (by rfl) ⟨3089462, by rfl⟩ : syracuseStep 4119283 = 6178925) B6178925
theorem B1285247 : Blo 1283960 1285247 := bstep (se 1 (by rfl) ⟨963935, by rfl⟩ : syracuseStep 1285247 = 1927871) B1927871
theorem B1285279 : Blo 1283960 1285279 := bstep (se 1 (by rfl) ⟨963959, by rfl⟩ : syracuseStep 1285279 = 1927919) B1927919
theorem B5487851 : Blo 1283960 5487851 := bstep (se 1 (by rfl) ⟨4115888, by rfl⟩ : syracuseStep 5487851 = 8231777) B8231777
theorem B8233235 : Blo 1283960 8233235 := bstep (se 1 (by rfl) ⟨6174926, by rfl⟩ : syracuseStep 8233235 = 12349853) B12349853
theorem B5489849 : Blo 1283960 5489849 := bstep (se 2 (by rfl) ⟨2058693, by rfl⟩ : syracuseStep 5489849 = 4117387) B4117387
theorem B3253567 : Blo 1283960 3253567 := bstep (se 1 (by rfl) ⟨2440175, by rfl⟩ : syracuseStep 3253567 = 4880351) B4880351
theorem B21939983 : Blo 1283960 21939983 := bstep (se 1 (by rfl) ⟨16454987, by rfl⟩ : syracuseStep 21939983 = 32909975) B32909975
theorem B1928687 : Blo 1283960 1928687 := bstep (se 1 (by rfl) ⟨1446515, by rfl⟩ : syracuseStep 1928687 = 2893031) B2893031
theorem B6172159 : Blo 1283960 6172159 := bstep (se 1 (by rfl) ⟨4629119, by rfl⟩ : syracuseStep 6172159 = 9258239) B9258239
theorem B5492225 : Blo 1283960 5492225 := bstep (se 2 (by rfl) ⟨2059584, by rfl⟩ : syracuseStep 5492225 = 4119169) B4119169
theorem B5492377 : Blo 1283960 5492377 := bstep (se 2 (by rfl) ⟨2059641, by rfl⟩ : syracuseStep 5492377 = 4119283) B4119283
theorem B3658567 : Blo 1283960 3658567 := bstep (se 1 (by rfl) ⟨2743925, by rfl⟩ : syracuseStep 3658567 = 5487851) B5487851
theorem B4338791 : Blo 1283960 4338791 := bstep (se 1 (by rfl) ⟨3254093, by rfl⟩ : syracuseStep 4338791 = 6508187) B6508187
theorem B316733915 : Blo 1283960 316733915 := bstep (se 1 (by rfl) ⟨237550436, by rfl⟩ : syracuseStep 316733915 = 475100873) B475100873
theorem B2169551 : Blo 1283960 2169551 := bstep (se 1 (by rfl) ⟨1627163, by rfl⟩ : syracuseStep 2169551 = 3254327) B3254327
theorem B5488823 : Blo 1283960 5488823 := bstep (se 1 (by rfl) ⟨4116617, by rfl⟩ : syracuseStep 5488823 = 8233235) B8233235
theorem B2892527 : Blo 1283960 2892527 := bstep (se 1 (by rfl) ⟨2169395, by rfl⟩ : syracuseStep 2892527 = 4338791) B4338791
theorem B4878089 : Blo 1283960 4878089 := bstep (se 2 (by rfl) ⟨1829283, by rfl⟩ : syracuseStep 4878089 = 3658567) B3658567
theorem B14626655 : Blo 1283960 14626655 := bstep (se 1 (by rfl) ⟨10969991, by rfl⟩ : syracuseStep 14626655 = 21939983) B21939983
theorem B4338089 : Blo 1283960 4338089 := bstep (se 2 (by rfl) ⟨1626783, by rfl⟩ : syracuseStep 4338089 = 3253567) B3253567
theorem B1446367 : Blo 1283960 1446367 := bstep (se 1 (by rfl) ⟨1084775, by rfl⟩ : syracuseStep 1446367 = 2169551) B2169551
theorem B8229545 : Blo 1283960 8229545 := bstep (se 2 (by rfl) ⟨3086079, by rfl⟩ : syracuseStep 8229545 = 6172159) B6172159
theorem B3659899 : Blo 1283960 3659899 := bstep (se 1 (by rfl) ⟨2744924, by rfl⟩ : syracuseStep 3659899 = 5489849) B5489849
theorem B211155943 : Blo 1283960 211155943 := bstep (se 1 (by rfl) ⟨158366957, by rfl⟩ : syracuseStep 211155943 = 316733915) B316733915
theorem B7323169 : Blo 1283960 7323169 := bstep (se 2 (by rfl) ⟨2746188, by rfl⟩ : syracuseStep 7323169 = 5492377) B5492377
theorem B1285791 : Blo 1283960 1285791 := bstep (se 1 (by rfl) ⟨964343, by rfl⟩ : syracuseStep 1285791 = 1928687) B1928687
theorem B3661483 : Blo 1283960 3661483 := bstep (se 1 (by rfl) ⟨2746112, by rfl⟩ : syracuseStep 3661483 = 5492225) B5492225
theorem B2892059 : Blo 1283960 2892059 := bstep (se 1 (by rfl) ⟨2169044, by rfl⟩ : syracuseStep 2892059 = 4338089) B4338089
theorem B9751103 : Blo 1283960 9751103 := bstep (se 1 (by rfl) ⟨7313327, by rfl⟩ : syracuseStep 9751103 = 14626655) B14626655
theorem B1928351 : Blo 1283960 1928351 := bstep (se 1 (by rfl) ⟨1446263, by rfl⟩ : syracuseStep 1928351 = 2892527) B2892527
theorem B1928489 : Blo 1283960 1928489 := bstep (se 2 (by rfl) ⟨723183, by rfl⟩ : syracuseStep 1928489 = 1446367) B1446367
theorem B4879865 : Blo 1283960 4879865 := bstep (se 2 (by rfl) ⟨1829949, by rfl⟩ : syracuseStep 4879865 = 3659899) B3659899
theorem B5486363 : Blo 1283960 5486363 := bstep (se 1 (by rfl) ⟨4114772, by rfl⟩ : syracuseStep 5486363 = 8229545) B8229545
theorem B14636861 : Blo 1283960 14636861 := bstep (se 3 (by rfl) ⟨2744411, by rfl⟩ : syracuseStep 14636861 = 5488823) B5488823
theorem B281541257 : Blo 1283960 281541257 := bstep (se 2 (by rfl) ⟨105577971, by rfl⟩ : syracuseStep 281541257 = 211155943) B211155943
theorem B9764225 : Blo 1283960 9764225 := bstep (se 2 (by rfl) ⟨3661584, by rfl⟩ : syracuseStep 9764225 = 7323169) B7323169
theorem B4881977 : Blo 1283960 4881977 := bstep (se 2 (by rfl) ⟨1830741, by rfl⟩ : syracuseStep 4881977 = 3661483) B3661483
theorem B3252059 : Blo 1283960 3252059 := bstep (se 1 (by rfl) ⟨2439044, by rfl⟩ : syracuseStep 3252059 = 4878089) B4878089
theorem B3253243 : Blo 1283960 3253243 := bstep (se 1 (by rfl) ⟨2439932, by rfl⟩ : syracuseStep 3253243 = 4879865) B4879865
theorem B9757907 : Blo 1283960 9757907 := bstep (se 1 (by rfl) ⟨7318430, by rfl⟩ : syracuseStep 9757907 = 14636861) B14636861
theorem B3254651 : Blo 1283960 3254651 := bstep (se 1 (by rfl) ⟨2440988, by rfl⟩ : syracuseStep 3254651 = 4881977) B4881977
theorem B1928039 : Blo 1283960 1928039 := bstep (se 1 (by rfl) ⟨1446029, by rfl⟩ : syracuseStep 1928039 = 2892059) B2892059
theorem B3657575 : Blo 1283960 3657575 := bstep (se 1 (by rfl) ⟨2743181, by rfl⟩ : syracuseStep 3657575 = 5486363) B5486363
theorem B6500735 : Blo 1283960 6500735 := bstep (se 1 (by rfl) ⟨4875551, by rfl⟩ : syracuseStep 6500735 = 9751103) B9751103
theorem B6509483 : Blo 1283960 6509483 := bstep (se 1 (by rfl) ⟨4882112, by rfl⟩ : syracuseStep 6509483 = 9764225) B9764225
theorem B2168039 : Blo 1283960 2168039 := bstep (se 1 (by rfl) ⟨1626029, by rfl⟩ : syracuseStep 2168039 = 3252059) B3252059
theorem B187694171 : Blo 1283960 187694171 := bstep (se 1 (by rfl) ⟨140770628, by rfl⟩ : syracuseStep 187694171 = 281541257) B281541257
theorem B1285567 : Blo 1283960 1285567 := bstep (se 1 (by rfl) ⟨964175, by rfl⟩ : syracuseStep 1285567 = 1928351) B1928351
theorem B1285659 : Blo 1283960 1285659 := bstep (se 1 (by rfl) ⟨964244, by rfl⟩ : syracuseStep 1285659 = 1928489) B1928489
theorem B4333823 : Blo 1283960 4333823 := bstep (se 1 (by rfl) ⟨3250367, by rfl⟩ : syracuseStep 4333823 = 6500735) B6500735
theorem B6505271 : Blo 1283960 6505271 := bstep (se 1 (by rfl) ⟨4878953, by rfl⟩ : syracuseStep 6505271 = 9757907) B9757907
theorem B1445359 : Blo 1283960 1445359 := bstep (se 1 (by rfl) ⟨1084019, by rfl⟩ : syracuseStep 1445359 = 2168039) B2168039
theorem B4337657 : Blo 1283960 4337657 := bstep (se 2 (by rfl) ⟨1626621, by rfl⟩ : syracuseStep 4337657 = 3253243) B3253243
theorem B125129447 : Blo 1283960 125129447 := bstep (se 1 (by rfl) ⟨93847085, by rfl⟩ : syracuseStep 125129447 = 187694171) B187694171
theorem B9753533 : Blo 1283960 9753533 := bstep (se 3 (by rfl) ⟨1828787, by rfl⟩ : syracuseStep 9753533 = 3657575) B3657575
theorem B4339655 : Blo 1283960 4339655 := bstep (se 1 (by rfl) ⟨3254741, by rfl⟩ : syracuseStep 4339655 = 6509483) B6509483
theorem B2169767 : Blo 1283960 2169767 := bstep (se 1 (by rfl) ⟨1627325, by rfl⟩ : syracuseStep 2169767 = 3254651) B3254651
theorem B1285359 : Blo 1283960 1285359 := bstep (se 1 (by rfl) ⟨964019, by rfl⟩ : syracuseStep 1285359 = 1928039) B1928039
theorem B83419631 : Blo 1283960 83419631 := bstep (se 1 (by rfl) ⟨62564723, by rfl⟩ : syracuseStep 83419631 = 125129447) B125129447
theorem B2893103 : Blo 1283960 2893103 := bstep (se 1 (by rfl) ⟨2169827, by rfl⟩ : syracuseStep 2893103 = 4339655) B4339655
theorem B1927145 : Blo 1283960 1927145 := bstep (se 2 (by rfl) ⟨722679, by rfl⟩ : syracuseStep 1927145 = 1445359) B1445359
theorem B4336847 : Blo 1283960 4336847 := bstep (se 1 (by rfl) ⟨3252635, by rfl⟩ : syracuseStep 4336847 = 6505271) B6505271
theorem B1446511 : Blo 1283960 1446511 := bstep (se 1 (by rfl) ⟨1084883, by rfl⟩ : syracuseStep 1446511 = 2169767) B2169767
theorem B2889215 : Blo 1283960 2889215 := bstep (se 1 (by rfl) ⟨2166911, by rfl⟩ : syracuseStep 2889215 = 4333823) B4333823
theorem B6502355 : Blo 1283960 6502355 := bstep (se 1 (by rfl) ⟨4876766, by rfl⟩ : syracuseStep 6502355 = 9753533) B9753533
theorem B2891771 : Blo 1283960 2891771 := bstep (se 1 (by rfl) ⟨2168828, by rfl⟩ : syracuseStep 2891771 = 4337657) B4337657
theorem B1926143 : Blo 1283960 1926143 := bstep (se 1 (by rfl) ⟨1444607, by rfl⟩ : syracuseStep 1926143 = 2889215) B2889215
theorem B4334903 : Blo 1283960 4334903 := bstep (se 1 (by rfl) ⟨3251177, by rfl⟩ : syracuseStep 4334903 = 6502355) B6502355
theorem B1927847 : Blo 1283960 1927847 := bstep (se 1 (by rfl) ⟨1445885, by rfl⟩ : syracuseStep 1927847 = 2891771) B2891771
theorem B1928681 : Blo 1283960 1928681 := bstep (se 2 (by rfl) ⟨723255, by rfl⟩ : syracuseStep 1928681 = 1446511) B1446511
theorem B1928735 : Blo 1283960 1928735 := bstep (se 1 (by rfl) ⟨1446551, by rfl⟩ : syracuseStep 1928735 = 2893103) B2893103
theorem B55613087 : Blo 1283960 55613087 := bstep (se 1 (by rfl) ⟨41709815, by rfl⟩ : syracuseStep 55613087 = 83419631) B83419631
theorem B1284763 : Blo 1283960 1284763 := bstep (se 1 (by rfl) ⟨963572, by rfl⟩ : syracuseStep 1284763 = 1927145) B1927145
theorem B2891231 : Blo 1283960 2891231 := bstep (se 1 (by rfl) ⟨2168423, by rfl⟩ : syracuseStep 2891231 = 4336847) B4336847
theorem B1927487 : Blo 1283960 1927487 := bstep (se 1 (by rfl) ⟨1445615, by rfl⟩ : syracuseStep 1927487 = 2891231) B2891231
theorem B1284095 : Blo 1283960 1284095 := bstep (se 1 (by rfl) ⟨963071, by rfl⟩ : syracuseStep 1284095 = 1926143) B1926143
theorem B2889935 : Blo 1283960 2889935 := bstep (se 1 (by rfl) ⟨2167451, by rfl⟩ : syracuseStep 2889935 = 4334903) B4334903
theorem B37075391 : Blo 1283960 37075391 := bstep (se 1 (by rfl) ⟨27806543, by rfl⟩ : syracuseStep 37075391 = 55613087) B55613087
theorem B1285231 : Blo 1283960 1285231 := bstep (se 1 (by rfl) ⟨963923, by rfl⟩ : syracuseStep 1285231 = 1927847) B1927847
theorem B1285787 : Blo 1283960 1285787 := bstep (se 1 (by rfl) ⟨964340, by rfl⟩ : syracuseStep 1285787 = 1928681) B1928681
theorem B1285823 : Blo 1283960 1285823 := bstep (se 1 (by rfl) ⟨964367, by rfl⟩ : syracuseStep 1285823 = 1928735) B1928735
theorem B1926623 : Blo 1283960 1926623 := bstep (se 1 (by rfl) ⟨1444967, by rfl⟩ : syracuseStep 1926623 = 2889935) B2889935
theorem B24716927 : Blo 1283960 24716927 := bstep (se 1 (by rfl) ⟨18537695, by rfl⟩ : syracuseStep 24716927 = 37075391) B37075391
theorem B1284991 : Blo 1283960 1284991 := bstep (se 1 (by rfl) ⟨963743, by rfl⟩ : syracuseStep 1284991 = 1927487) B1927487
theorem B16477951 : Blo 1283960 16477951 := bstep (se 1 (by rfl) ⟨12358463, by rfl⟩ : syracuseStep 16477951 = 24716927) B24716927
theorem B1284415 : Blo 1283960 1284415 := bstep (se 1 (by rfl) ⟨963311, by rfl⟩ : syracuseStep 1284415 = 1926623) B1926623
theorem B21970601 : Blo 1283960 21970601 := bstep (se 2 (by rfl) ⟨8238975, by rfl⟩ : syracuseStep 21970601 = 16477951) B16477951
theorem B14647067 : Blo 1283960 14647067 := bstep (se 1 (by rfl) ⟨10985300, by rfl⟩ : syracuseStep 14647067 = 21970601) B21970601
theorem B9764711 : Blo 1283960 9764711 := bstep (se 1 (by rfl) ⟨7323533, by rfl⟩ : syracuseStep 9764711 = 14647067) B14647067
theorem B6509807 : Blo 1283960 6509807 := bstep (se 1 (by rfl) ⟨4882355, by rfl⟩ : syracuseStep 6509807 = 9764711) B9764711
theorem B4339871 : Blo 1283960 4339871 := bstep (se 1 (by rfl) ⟨3254903, by rfl⟩ : syracuseStep 4339871 = 6509807) B6509807
theorem B2893247 : Blo 1283960 2893247 := bstep (se 1 (by rfl) ⟨2169935, by rfl⟩ : syracuseStep 2893247 = 4339871) B4339871
theorem B1928831 : Blo 1283960 1928831 := bstep (se 1 (by rfl) ⟨1446623, by rfl⟩ : syracuseStep 1928831 = 2893247) B2893247
theorem B1285887 : Blo 1283960 1285887 := bstep (se 1 (by rfl) ⟨964415, by rfl⟩ : syracuseStep 1285887 = 1928831) B1928831

theorem C0 (j : ℕ) (h1 : 320990 ≤ j) (h2 : j ≤ 321489) : Blo 1283960 (4 * j + 3) := by
  interval_cases j
  · exact B1283963
  · exact B1283967
  · exact B1283971
  · exact B1283975
  · exact B1283979
  · exact B1283983
  · exact B1283987
  · exact B1283991
  · exact B1283995
  · exact B1283999
  · exact B1284003
  · exact B1284007
  · exact B1284011
  · exact B1284015
  · exact B1284019
  · exact B1284023
  · exact B1284027
  · exact B1284031
  · exact B1284035
  · exact B1284039
  · exact B1284043
  · exact B1284047
  · exact B1284051
  · exact B1284055
  · exact B1284059
  · exact B1284063
  · exact B1284067
  · exact B1284071
  · exact B1284075
  · exact B1284079
  · exact B1284083
  · exact B1284087
  · exact B1284091
  · exact B1284095
  · exact B1284099
  · exact B1284103
  · exact B1284107
  · exact B1284111
  · exact B1284115
  · exact B1284119
  · exact B1284123
  · exact B1284127
  · exact B1284131
  · exact B1284135
  · exact B1284139
  · exact B1284143
  · exact B1284147
  · exact B1284151
  · exact B1284155
  · exact B1284159
  · exact B1284163
  · exact B1284167
  · exact B1284171
  · exact B1284175
  · exact B1284179
  · exact B1284183
  · exact B1284187
  · exact B1284191
  · exact B1284195
  · exact B1284199
  · exact B1284203
  · exact B1284207
  · exact B1284211
  · exact B1284215
  · exact B1284219
  · exact B1284223
  · exact B1284227
  · exact B1284231
  · exact B1284235
  · exact B1284239
  · exact B1284243
  · exact B1284247
  · exact B1284251
  · exact B1284255
  · exact B1284259
  · exact B1284263
  · exact B1284267
  · exact B1284271
  · exact B1284275
  · exact B1284279
  · exact B1284283
  · exact B1284287
  · exact B1284291
  · exact B1284295
  · exact B1284299
  · exact B1284303
  · exact B1284307
  · exact B1284311
  · exact B1284315
  · exact B1284319
  · exact B1284323
  · exact B1284327
  · exact B1284331
  · exact B1284335
  · exact B1284339
  · exact B1284343
  · exact B1284347
  · exact B1284351
  · exact B1284355
  · exact B1284359
  · exact B1284363
  · exact B1284367
  · exact B1284371
  · exact B1284375
  · exact B1284379
  · exact B1284383
  · exact B1284387
  · exact B1284391
  · exact B1284395
  · exact B1284399
  · exact B1284403
  · exact B1284407
  · exact B1284411
  · exact B1284415
  · exact B1284419
  · exact B1284423
  · exact B1284427
  · exact B1284431
  · exact B1284435
  · exact B1284439
  · exact B1284443
  · exact B1284447
  · exact B1284451
  · exact B1284455
  · exact B1284459
  · exact B1284463
  · exact B1284467
  · exact B1284471
  · exact B1284475
  · exact B1284479
  · exact B1284483
  · exact B1284487
  · exact B1284491
  · exact B1284495
  · exact B1284499
  · exact B1284503
  · exact B1284507
  · exact B1284511
  · exact B1284515
  · exact B1284519
  · exact B1284523
  · exact B1284527
  · exact B1284531
  · exact B1284535
  · exact B1284539
  · exact B1284543
  · exact B1284547
  · exact B1284551
  · exact B1284555
  · exact B1284559
  · exact B1284563
  · exact B1284567
  · exact B1284571
  · exact B1284575
  · exact B1284579
  · exact B1284583
  · exact B1284587
  · exact B1284591
  · exact B1284595
  · exact B1284599
  · exact B1284603
  · exact B1284607
  · exact B1284611
  · exact B1284615
  · exact B1284619
  · exact B1284623
  · exact B1284627
  · exact B1284631
  · exact B1284635
  · exact B1284639
  · exact B1284643
  · exact B1284647
  · exact B1284651
  · exact B1284655
  · exact B1284659
  · exact B1284663
  · exact B1284667
  · exact B1284671
  · exact B1284675
  · exact B1284679
  · exact B1284683
  · exact B1284687
  · exact B1284691
  · exact B1284695
  · exact B1284699
  · exact B1284703
  · exact B1284707
  · exact B1284711
  · exact B1284715
  · exact B1284719
  · exact B1284723
  · exact B1284727
  · exact B1284731
  · exact B1284735
  · exact B1284739
  · exact B1284743
  · exact B1284747
  · exact B1284751
  · exact B1284755
  · exact B1284759
  · exact B1284763
  · exact B1284767
  · exact B1284771
  · exact B1284775
  · exact B1284779
  · exact B1284783
  · exact B1284787
  · exact B1284791
  · exact B1284795
  · exact B1284799
  · exact B1284803
  · exact B1284807
  · exact B1284811
  · exact B1284815
  · exact B1284819
  · exact B1284823
  · exact B1284827
  · exact B1284831
  · exact B1284835
  · exact B1284839
  · exact B1284843
  · exact B1284847
  · exact B1284851
  · exact B1284855
  · exact B1284859
  · exact B1284863
  · exact B1284867
  · exact B1284871
  · exact B1284875
  · exact B1284879
  · exact B1284883
  · exact B1284887
  · exact B1284891
  · exact B1284895
  · exact B1284899
  · exact B1284903
  · exact B1284907
  · exact B1284911
  · exact B1284915
  · exact B1284919
  · exact B1284923
  · exact B1284927
  · exact B1284931
  · exact B1284935
  · exact B1284939
  · exact B1284943
  · exact B1284947
  · exact B1284951
  · exact B1284955
  · exact B1284959
  · exact B1284963
  · exact B1284967
  · exact B1284971
  · exact B1284975
  · exact B1284979
  · exact B1284983
  · exact B1284987
  · exact B1284991
  · exact B1284995
  · exact B1284999
  · exact B1285003
  · exact B1285007
  · exact B1285011
  · exact B1285015
  · exact B1285019
  · exact B1285023
  · exact B1285027
  · exact B1285031
  · exact B1285035
  · exact B1285039
  · exact B1285043
  · exact B1285047
  · exact B1285051
  · exact B1285055
  · exact B1285059
  · exact B1285063
  · exact B1285067
  · exact B1285071
  · exact B1285075
  · exact B1285079
  · exact B1285083
  · exact B1285087
  · exact B1285091
  · exact B1285095
  · exact B1285099
  · exact B1285103
  · exact B1285107
  · exact B1285111
  · exact B1285115
  · exact B1285119
  · exact B1285123
  · exact B1285127
  · exact B1285131
  · exact B1285135
  · exact B1285139
  · exact B1285143
  · exact B1285147
  · exact B1285151
  · exact B1285155
  · exact B1285159
  · exact B1285163
  · exact B1285167
  · exact B1285171
  · exact B1285175
  · exact B1285179
  · exact B1285183
  · exact B1285187
  · exact B1285191
  · exact B1285195
  · exact B1285199
  · exact B1285203
  · exact B1285207
  · exact B1285211
  · exact B1285215
  · exact B1285219
  · exact B1285223
  · exact B1285227
  · exact B1285231
  · exact B1285235
  · exact B1285239
  · exact B1285243
  · exact B1285247
  · exact B1285251
  · exact B1285255
  · exact B1285259
  · exact B1285263
  · exact B1285267
  · exact B1285271
  · exact B1285275
  · exact B1285279
  · exact B1285283
  · exact B1285287
  · exact B1285291
  · exact B1285295
  · exact B1285299
  · exact B1285303
  · exact B1285307
  · exact B1285311
  · exact B1285315
  · exact B1285319
  · exact B1285323
  · exact B1285327
  · exact B1285331
  · exact B1285335
  · exact B1285339
  · exact B1285343
  · exact B1285347
  · exact B1285351
  · exact B1285355
  · exact B1285359
  · exact B1285363
  · exact B1285367
  · exact B1285371
  · exact B1285375
  · exact B1285379
  · exact B1285383
  · exact B1285387
  · exact B1285391
  · exact B1285395
  · exact B1285399
  · exact B1285403
  · exact B1285407
  · exact B1285411
  · exact B1285415
  · exact B1285419
  · exact B1285423
  · exact B1285427
  · exact B1285431
  · exact B1285435
  · exact B1285439
  · exact B1285443
  · exact B1285447
  · exact B1285451
  · exact B1285455
  · exact B1285459
  · exact B1285463
  · exact B1285467
  · exact B1285471
  · exact B1285475
  · exact B1285479
  · exact B1285483
  · exact B1285487
  · exact B1285491
  · exact B1285495
  · exact B1285499
  · exact B1285503
  · exact B1285507
  · exact B1285511
  · exact B1285515
  · exact B1285519
  · exact B1285523
  · exact B1285527
  · exact B1285531
  · exact B1285535
  · exact B1285539
  · exact B1285543
  · exact B1285547
  · exact B1285551
  · exact B1285555
  · exact B1285559
  · exact B1285563
  · exact B1285567
  · exact B1285571
  · exact B1285575
  · exact B1285579
  · exact B1285583
  · exact B1285587
  · exact B1285591
  · exact B1285595
  · exact B1285599
  · exact B1285603
  · exact B1285607
  · exact B1285611
  · exact B1285615
  · exact B1285619
  · exact B1285623
  · exact B1285627
  · exact B1285631
  · exact B1285635
  · exact B1285639
  · exact B1285643
  · exact B1285647
  · exact B1285651
  · exact B1285655
  · exact B1285659
  · exact B1285663
  · exact B1285667
  · exact B1285671
  · exact B1285675
  · exact B1285679
  · exact B1285683
  · exact B1285687
  · exact B1285691
  · exact B1285695
  · exact B1285699
  · exact B1285703
  · exact B1285707
  · exact B1285711
  · exact B1285715
  · exact B1285719
  · exact B1285723
  · exact B1285727
  · exact B1285731
  · exact B1285735
  · exact B1285739
  · exact B1285743
  · exact B1285747
  · exact B1285751
  · exact B1285755
  · exact B1285759
  · exact B1285763
  · exact B1285767
  · exact B1285771
  · exact B1285775
  · exact B1285779
  · exact B1285783
  · exact B1285787
  · exact B1285791
  · exact B1285795
  · exact B1285799
  · exact B1285803
  · exact B1285807
  · exact B1285811
  · exact B1285815
  · exact B1285819
  · exact B1285823
  · exact B1285827
  · exact B1285831
  · exact B1285835
  · exact B1285839
  · exact B1285843
  · exact B1285847
  · exact B1285851
  · exact B1285855
  · exact B1285859
  · exact B1285863
  · exact B1285867
  · exact B1285871
  · exact B1285875
  · exact B1285879
  · exact B1285883
  · exact B1285887
  · exact B1285891
  · exact B1285895
  · exact B1285899
  · exact B1285903
  · exact B1285907
  · exact B1285911
  · exact B1285915
  · exact B1285919
  · exact B1285923
  · exact B1285927
  · exact B1285931
  · exact B1285935
  · exact B1285939
  · exact B1285943
  · exact B1285947
  · exact B1285951
  · exact B1285955
  · exact B1285959

theorem solution (m : ℕ) (hlo : 1283960 ≤ m) (hhi : m ≤ 1285960) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 320990 ≤ j := by omega
    have hj2 : j ≤ 321489 := by omega
    have hb : Blo 1283960 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
