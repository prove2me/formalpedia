-- Prove2me | solution 1 for syracuse_descends_range_1260448_1262448
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:23.466064+00:00
-- url     : https://prove2.me/submissions/681aef6f-db32-4963-ae2c-275fee3a1a9a

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


theorem B1892357 : Blo 1260448 1892357 := bbase (se 4 (by rfl) ⟨177408, by rfl⟩ : syracuseStep 1892357 = 354817) (by norm_num)
theorem B6389765 : Blo 1260448 6389765 := bbase (se 4 (by rfl) ⟨599040, by rfl⟩ : syracuseStep 6389765 = 1198081) (by norm_num)
theorem B1892381 : Blo 1260448 1892381 := bbase (se 3 (by rfl) ⟨354821, by rfl⟩ : syracuseStep 1892381 = 709643) (by norm_num)
theorem B1597477 : Blo 1260448 1597477 := bbase (se 4 (by rfl) ⟨149763, by rfl⟩ : syracuseStep 1597477 = 299527) (by norm_num)
theorem B1892405 : Blo 1260448 1892405 := bbase (se 5 (by rfl) ⟨88706, by rfl⟩ : syracuseStep 1892405 = 177413) (by norm_num)
theorem B2129989 : Blo 1260448 2129989 := bbase (se 4 (by rfl) ⟨199686, by rfl⟩ : syracuseStep 2129989 = 399373) (by norm_num)
theorem B1892429 : Blo 1260448 1892429 := bbase (se 3 (by rfl) ⟨354830, by rfl⟩ : syracuseStep 1892429 = 709661) (by norm_num)
theorem B1892453 : Blo 1260448 1892453 := bbase (se 4 (by rfl) ⟨177417, by rfl⟩ : syracuseStep 1892453 = 354835) (by norm_num)
theorem B1892477 : Blo 1260448 1892477 := bbase (se 3 (by rfl) ⟨354839, by rfl⟩ : syracuseStep 1892477 = 709679) (by norm_num)
theorem B1597573 : Blo 1260448 1597573 := bbase (se 4 (by rfl) ⟨149772, by rfl⟩ : syracuseStep 1597573 = 299545) (by norm_num)
theorem B12116117 : Blo 1260448 12116117 := bbase (se 6 (by rfl) ⟨283971, by rfl⟩ : syracuseStep 12116117 = 567943) (by norm_num)
theorem B1892501 : Blo 1260448 1892501 := bbase (se 6 (by rfl) ⟨44355, by rfl⟩ : syracuseStep 1892501 = 88711) (by norm_num)
theorem B2130077 : Blo 1260448 2130077 := bbase (se 3 (by rfl) ⟨399389, by rfl⟩ : syracuseStep 2130077 = 798779) (by norm_num)
theorem B4260005 : Blo 1260448 4260005 := bbase (se 4 (by rfl) ⟨399375, by rfl⟩ : syracuseStep 4260005 = 798751) (by norm_num)
theorem B1917101 : Blo 1260448 1917101 := bbase (se 3 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 1917101 = 718913) (by norm_num)
theorem B1892525 : Blo 1260448 1892525 := bbase (se 3 (by rfl) ⟨354848, by rfl⟩ : syracuseStep 1892525 = 709697) (by norm_num)
theorem B9576629 : Blo 1260448 9576629 := bbase (se 5 (by rfl) ⟨448904, by rfl⟩ : syracuseStep 9576629 = 897809) (by norm_num)
theorem B1892549 : Blo 1260448 1892549 := bbase (se 4 (by rfl) ⟨177426, by rfl⟩ : syracuseStep 1892549 = 354853) (by norm_num)
theorem B3195085 : Blo 1260448 3195085 := bbase (se 3 (by rfl) ⟨599078, by rfl⟩ : syracuseStep 3195085 = 1198157) (by norm_num)
theorem B1892573 : Blo 1260448 1892573 := bbase (se 3 (by rfl) ⟨354857, by rfl⟩ : syracuseStep 1892573 = 709715) (by norm_num)
theorem B1515745 : Blo 1260448 1515745 := bbase (se 2 (by rfl) ⟨568404, by rfl⟩ : syracuseStep 1515745 = 1136809) (by norm_num)
theorem B1892597 : Blo 1260448 1892597 := bbase (se 5 (by rfl) ⟨88715, by rfl⟩ : syracuseStep 1892597 = 177431) (by norm_num)
theorem B1892621 : Blo 1260448 1892621 := bbase (se 3 (by rfl) ⟨354866, by rfl⟩ : syracuseStep 1892621 = 709733) (by norm_num)
theorem B2130205 : Blo 1260448 2130205 := bbase (se 3 (by rfl) ⟨399413, by rfl⟩ : syracuseStep 2130205 = 798827) (by norm_num)
theorem B1892645 : Blo 1260448 1892645 := bbase (se 4 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 1892645 = 354871) (by norm_num)
theorem B1597745 : Blo 1260448 1597745 := bbase (se 2 (by rfl) ⟨599154, by rfl⟩ : syracuseStep 1597745 = 1198309) (by norm_num)
theorem B3031357 : Blo 1260448 3031357 := bbase (se 3 (by rfl) ⟨568379, by rfl⟩ : syracuseStep 3031357 = 1136759) (by norm_num)
theorem B1892669 : Blo 1260448 1892669 := bbase (se 3 (by rfl) ⟨354875, by rfl⟩ : syracuseStep 1892669 = 709751) (by norm_num)
theorem B1384765 : Blo 1260448 1384765 := bbase (se 3 (by rfl) ⟨259643, by rfl⟩ : syracuseStep 1384765 = 519287) (by norm_num)
theorem B3195197 : Blo 1260448 3195197 := bbase (se 3 (by rfl) ⟨599099, by rfl⟩ : syracuseStep 3195197 = 1198199) (by norm_num)
theorem B6472021 : Blo 1260448 6472021 := bbase (se 10 (by rfl) ⟨9480, by rfl⟩ : syracuseStep 6472021 = 18961) (by norm_num)
theorem B1892693 : Blo 1260448 1892693 := bbase (se 10 (by rfl) ⟨2772, by rfl⟩ : syracuseStep 1892693 = 5545) (by norm_num)
theorem B1892717 : Blo 1260448 1892717 := bbase (se 3 (by rfl) ⟨354884, by rfl⟩ : syracuseStep 1892717 = 709769) (by norm_num)
theorem B2130293 : Blo 1260448 2130293 := bbase (se 5 (by rfl) ⟨99857, by rfl⟩ : syracuseStep 2130293 = 199715) (by norm_num)
theorem B1892741 : Blo 1260448 1892741 := bbase (se 4 (by rfl) ⟨177444, by rfl⟩ : syracuseStep 1892741 = 354889) (by norm_num)
theorem B1892765 : Blo 1260448 1892765 := bbase (se 3 (by rfl) ⟨354893, by rfl⟩ : syracuseStep 1892765 = 709787) (by norm_num)
theorem B6381989 : Blo 1260448 6381989 := bbase (se 4 (by rfl) ⟨598311, by rfl⟩ : syracuseStep 6381989 = 1196623) (by norm_num)
theorem B6062501 : Blo 1260448 6062501 := bbase (se 4 (by rfl) ⟨568359, by rfl⟩ : syracuseStep 6062501 = 1136719) (by norm_num)
theorem B1892789 : Blo 1260448 1892789 := bbase (se 5 (by rfl) ⟨88724, by rfl⟩ : syracuseStep 1892789 = 177449) (by norm_num)
theorem B1892813 : Blo 1260448 1892813 := bbase (se 3 (by rfl) ⟨354902, by rfl⟩ : syracuseStep 1892813 = 709805) (by norm_num)
theorem B1892837 : Blo 1260448 1892837 := bbase (se 4 (by rfl) ⟨177453, by rfl⟩ : syracuseStep 1892837 = 354907) (by norm_num)
theorem B1892861 : Blo 1260448 1892861 := bbase (se 3 (by rfl) ⟨354911, by rfl⟩ : syracuseStep 1892861 = 709823) (by norm_num)
theorem B3195389 : Blo 1260448 3195389 := bbase (se 3 (by rfl) ⟨599135, by rfl⟩ : syracuseStep 3195389 = 1198271) (by norm_num)
theorem B6062597 : Blo 1260448 6062597 := bbase (se 4 (by rfl) ⟨568368, by rfl⟩ : syracuseStep 6062597 = 1136737) (by norm_num)
theorem B1892885 : Blo 1260448 1892885 := bbase (se 6 (by rfl) ⟨44364, by rfl⟩ : syracuseStep 1892885 = 88729) (by norm_num)
theorem B2695717 : Blo 1260448 2695717 := bbase (se 4 (by rfl) ⟨252723, by rfl⟩ : syracuseStep 2695717 = 505447) (by norm_num)
theorem B1278505 : Blo 1260448 1278505 := bbase (se 2 (by rfl) ⟨479439, by rfl⟩ : syracuseStep 1278505 = 958879) (by norm_num)
theorem B1892909 : Blo 1260448 1892909 := bbase (se 3 (by rfl) ⟨354920, by rfl⟩ : syracuseStep 1892909 = 709841) (by norm_num)
theorem B3408437 : Blo 1260448 3408437 := bbase (se 5 (by rfl) ⟨159770, by rfl⟩ : syracuseStep 3408437 = 319541) (by norm_num)
theorem B1892933 : Blo 1260448 1892933 := bbase (se 4 (by rfl) ⟨177462, by rfl⟩ : syracuseStep 1892933 = 354925) (by norm_num)
theorem B4260437 : Blo 1260448 4260437 := bbase (se 8 (by rfl) ⟨24963, by rfl⟩ : syracuseStep 4260437 = 49927) (by norm_num)
theorem B1892957 : Blo 1260448 1892957 := bbase (se 3 (by rfl) ⟨354929, by rfl⟩ : syracuseStep 1892957 = 709859) (by norm_num)
theorem B1892981 : Blo 1260448 1892981 := bbase (se 5 (by rfl) ⟨88733, by rfl⟩ : syracuseStep 1892981 = 177467) (by norm_num)
theorem B1893005 : Blo 1260448 1893005 := bbase (se 3 (by rfl) ⟨354938, by rfl⟩ : syracuseStep 1893005 = 709877) (by norm_num)
theorem B1819285 : Blo 1260448 1819285 := bbase (se 6 (by rfl) ⟨42639, by rfl⟩ : syracuseStep 1819285 = 85279) (by norm_num)
theorem B2695837 : Blo 1260448 2695837 := bbase (se 3 (by rfl) ⟨505469, by rfl⟩ : syracuseStep 2695837 = 1010939) (by norm_num)
theorem B1893029 : Blo 1260448 1893029 := bbase (se 4 (by rfl) ⟨177471, by rfl⟩ : syracuseStep 1893029 = 354943) (by norm_num)
theorem B1893053 : Blo 1260448 1893053 := bbase (se 3 (by rfl) ⟨354947, by rfl⟩ : syracuseStep 1893053 = 709895) (by norm_num)
theorem B5186261 : Blo 1260448 5186261 := bbase (se 7 (by rfl) ⟨60776, by rfl⟩ : syracuseStep 5186261 = 121553) (by norm_num)
theorem B8086229 : Blo 1260448 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B1893077 : Blo 1260448 1893077 := bbase (se 7 (by rfl) ⟨22184, by rfl⟩ : syracuseStep 1893077 = 44369) (by norm_num)
theorem B1893101 : Blo 1260448 1893101 := bbase (se 3 (by rfl) ⟨354956, by rfl⟩ : syracuseStep 1893101 = 709913) (by norm_num)
theorem B1893125 : Blo 1260448 1893125 := bbase (se 4 (by rfl) ⟨177480, by rfl⟩ : syracuseStep 1893125 = 354961) (by norm_num)
theorem B1893149 : Blo 1260448 1893149 := bbase (se 3 (by rfl) ⟨354965, by rfl⟩ : syracuseStep 1893149 = 709931) (by norm_num)
theorem B1418017 : Blo 1260448 1418017 := bbase (se 2 (by rfl) ⟨531756, by rfl⟩ : syracuseStep 1418017 = 1063513) (by norm_num)
theorem B1893173 : Blo 1260448 1893173 := bbase (se 5 (by rfl) ⟨88742, by rfl⟩ : syracuseStep 1893173 = 177485) (by norm_num)
theorem B1418053 : Blo 1260448 1418053 := bbase (se 4 (by rfl) ⟨132942, by rfl⟩ : syracuseStep 1418053 = 265885) (by norm_num)
theorem B1893197 : Blo 1260448 1893197 := bbase (se 3 (by rfl) ⟨354974, by rfl⟩ : syracuseStep 1893197 = 709949) (by norm_num)
theorem B1794901 : Blo 1260448 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B34530133 : Blo 1260448 34530133 := bbase (se 9 (by rfl) ⟨101162, by rfl⟩ : syracuseStep 34530133 = 202325) (by norm_num)
theorem B1893221 : Blo 1260448 1893221 := bbase (se 4 (by rfl) ⟨177489, by rfl⟩ : syracuseStep 1893221 = 354979) (by norm_num)
theorem B1418089 : Blo 1260448 1418089 := bbase (se 2 (by rfl) ⟨531783, by rfl⟩ : syracuseStep 1418089 = 1063567) (by norm_num)
theorem B1893245 : Blo 1260448 1893245 := bbase (se 3 (by rfl) ⟨354983, by rfl⟩ : syracuseStep 1893245 = 709967) (by norm_num)
theorem B2392973 : Blo 1260448 2392973 := bbase (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) (by norm_num)
theorem B1418125 : Blo 1260448 1418125 := bbase (se 3 (by rfl) ⟨265898, by rfl⟩ : syracuseStep 1418125 = 531797) (by norm_num)
theorem B1893269 : Blo 1260448 1893269 := bbase (se 6 (by rfl) ⟨44373, by rfl⟩ : syracuseStep 1893269 = 88747) (by norm_num)
theorem B2696093 : Blo 1260448 2696093 := bbase (se 3 (by rfl) ⟨505517, by rfl⟩ : syracuseStep 2696093 = 1011035) (by norm_num)
theorem B1893293 : Blo 1260448 1893293 := bbase (se 3 (by rfl) ⟨354992, by rfl⟩ : syracuseStep 1893293 = 709985) (by norm_num)
theorem B1418161 : Blo 1260448 1418161 := bbase (se 2 (by rfl) ⟨531810, by rfl⟩ : syracuseStep 1418161 = 1063621) (by norm_num)
theorem B1893317 : Blo 1260448 1893317 := bbase (se 4 (by rfl) ⟨177498, by rfl⟩ : syracuseStep 1893317 = 354997) (by norm_num)
theorem B1418197 : Blo 1260448 1418197 := bbase (se 7 (by rfl) ⟨16619, by rfl⟩ : syracuseStep 1418197 = 33239) (by norm_num)
theorem B1893341 : Blo 1260448 1893341 := bbase (se 3 (by rfl) ⟨355001, by rfl⟩ : syracuseStep 1893341 = 710003) (by norm_num)
theorem B1893365 : Blo 1260448 1893365 := bbase (se 5 (by rfl) ⟨88751, by rfl⟩ : syracuseStep 1893365 = 177503) (by norm_num)
theorem B1418233 : Blo 1260448 1418233 := bbase (se 2 (by rfl) ⟨531837, by rfl⟩ : syracuseStep 1418233 = 1063675) (by norm_num)
theorem B1893389 : Blo 1260448 1893389 := bbase (se 3 (by rfl) ⟨355010, by rfl⟩ : syracuseStep 1893389 = 710021) (by norm_num)
theorem B1418269 : Blo 1260448 1418269 := bbase (se 3 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 1418269 = 531851) (by norm_num)
theorem B1893413 : Blo 1260448 1893413 := bbase (se 4 (by rfl) ⟨177507, by rfl⟩ : syracuseStep 1893413 = 355015) (by norm_num)
theorem B1795117 : Blo 1260448 1795117 := bbase (se 3 (by rfl) ⟨336584, by rfl⟩ : syracuseStep 1795117 = 673169) (by norm_num)
theorem B1516601 : Blo 1260448 1516601 := bbase (se 2 (by rfl) ⟨568725, by rfl⟩ : syracuseStep 1516601 = 1137451) (by norm_num)
theorem B1893437 : Blo 1260448 1893437 := bbase (se 3 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 1893437 = 710039) (by norm_num)
theorem B1418305 : Blo 1260448 1418305 := bbase (se 2 (by rfl) ⟨531864, by rfl⟩ : syracuseStep 1418305 = 1063729) (by norm_num)
theorem B1893461 : Blo 1260448 1893461 := bbase (se 8 (by rfl) ⟨11094, by rfl⟩ : syracuseStep 1893461 = 22189) (by norm_num)
theorem B1418341 : Blo 1260448 1418341 := bbase (se 4 (by rfl) ⟨132969, by rfl⟩ : syracuseStep 1418341 = 265939) (by norm_num)
theorem B1893485 : Blo 1260448 1893485 := bbase (se 3 (by rfl) ⟨355028, by rfl⟩ : syracuseStep 1893485 = 710057) (by norm_num)
theorem B1893509 : Blo 1260448 1893509 := bbase (se 4 (by rfl) ⟨177516, by rfl⟩ : syracuseStep 1893509 = 355033) (by norm_num)
theorem B1418377 : Blo 1260448 1418377 := bbase (se 2 (by rfl) ⟨531891, by rfl⟩ : syracuseStep 1418377 = 1063783) (by norm_num)
theorem B1893533 : Blo 1260448 1893533 := bbase (se 3 (by rfl) ⟨355037, by rfl⟩ : syracuseStep 1893533 = 710075) (by norm_num)
theorem B1418413 : Blo 1260448 1418413 := bbase (se 3 (by rfl) ⟨265952, by rfl⟩ : syracuseStep 1418413 = 531905) (by norm_num)
theorem B1893557 : Blo 1260448 1893557 := bbase (se 5 (by rfl) ⟨88760, by rfl⟩ : syracuseStep 1893557 = 177521) (by norm_num)
theorem B1893581 : Blo 1260448 1893581 := bbase (se 3 (by rfl) ⟨355046, by rfl⟩ : syracuseStep 1893581 = 710093) (by norm_num)
theorem B1418449 : Blo 1260448 1418449 := bbase (se 2 (by rfl) ⟨531918, by rfl⟩ : syracuseStep 1418449 = 1063837) (by norm_num)
theorem B1893605 : Blo 1260448 1893605 := bbase (se 4 (by rfl) ⟨177525, by rfl⟩ : syracuseStep 1893605 = 355051) (by norm_num)
theorem B1418485 : Blo 1260448 1418485 := bbase (se 5 (by rfl) ⟨66491, by rfl⟩ : syracuseStep 1418485 = 132983) (by norm_num)
theorem B1893629 : Blo 1260448 1893629 := bbase (se 3 (by rfl) ⟨355055, by rfl⟩ : syracuseStep 1893629 = 710111) (by norm_num)
theorem B6391061 : Blo 1260448 6391061 := bbase (se 6 (by rfl) ⟨149790, by rfl⟩ : syracuseStep 6391061 = 299581) (by norm_num)
theorem B1893653 : Blo 1260448 1893653 := bbase (se 6 (by rfl) ⟨44382, by rfl⟩ : syracuseStep 1893653 = 88765) (by norm_num)
theorem B1418521 : Blo 1260448 1418521 := bbase (se 2 (by rfl) ⟨531945, by rfl⟩ : syracuseStep 1418521 = 1063891) (by norm_num)
theorem B1418557 : Blo 1260448 1418557 := bbase (se 3 (by rfl) ⟨265979, by rfl⟩ : syracuseStep 1418557 = 531959) (by norm_num)
theorem B1418593 : Blo 1260448 1418593 := bbase (se 2 (by rfl) ⟨531972, by rfl⟩ : syracuseStep 1418593 = 1063945) (by norm_num)
theorem B1418629 : Blo 1260448 1418629 := bbase (se 4 (by rfl) ⟨132996, by rfl⟩ : syracuseStep 1418629 = 265993) (by norm_num)
theorem B1795493 : Blo 1260448 1795493 := bbase (se 4 (by rfl) ⟨168327, by rfl⟩ : syracuseStep 1795493 = 336655) (by norm_num)
theorem B1418665 : Blo 1260448 1418665 := bbase (se 2 (by rfl) ⟨531999, by rfl⟩ : syracuseStep 1418665 = 1063999) (by norm_num)
theorem B3237317 : Blo 1260448 3237317 := bbase (se 4 (by rfl) ⟨303498, by rfl⟩ : syracuseStep 3237317 = 606997) (by norm_num)
theorem B1418701 : Blo 1260448 1418701 := bbase (se 3 (by rfl) ⟨266006, by rfl⟩ : syracuseStep 1418701 = 532013) (by norm_num)
theorem B5391845 : Blo 1260448 5391845 := bbase (se 4 (by rfl) ⟨505485, by rfl⟩ : syracuseStep 5391845 = 1010971) (by norm_num)
theorem B2876909 : Blo 1260448 2876909 := bbase (se 3 (by rfl) ⟨539420, by rfl⟩ : syracuseStep 2876909 = 1078841) (by norm_num)
theorem B1418737 : Blo 1260448 1418737 := bbase (se 2 (by rfl) ⟨532026, by rfl⟩ : syracuseStep 1418737 = 1064053) (by norm_num)
theorem B2336261 : Blo 1260448 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B1418773 : Blo 1260448 1418773 := bbase (se 6 (by rfl) ⟨33252, by rfl⟩ : syracuseStep 1418773 = 66505) (by norm_num)
theorem B1418809 : Blo 1260448 1418809 := bbase (se 2 (by rfl) ⟨532053, by rfl⟩ : syracuseStep 1418809 = 1064107) (by norm_num)
theorem B2836061 : Blo 1260448 2836061 := bbase (se 3 (by rfl) ⟨531761, by rfl⟩ : syracuseStep 2836061 = 1063523) (by norm_num)
theorem B1418845 : Blo 1260448 1418845 := bbase (se 3 (by rfl) ⟨266033, by rfl⟩ : syracuseStep 1418845 = 532067) (by norm_num)
theorem B3589733 : Blo 1260448 3589733 := bbase (se 4 (by rfl) ⟨336537, by rfl⟩ : syracuseStep 3589733 = 673075) (by norm_num)
theorem B2393725 : Blo 1260448 2393725 := bbase (se 3 (by rfl) ⟨448823, by rfl⟩ : syracuseStep 2393725 = 897647) (by norm_num)
theorem B1418881 : Blo 1260448 1418881 := bbase (se 2 (by rfl) ⟨532080, by rfl⟩ : syracuseStep 1418881 = 1064161) (by norm_num)
theorem B2836133 : Blo 1260448 2836133 := bbase (se 4 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 2836133 = 531775) (by norm_num)
theorem B1418917 : Blo 1260448 1418917 := bbase (se 4 (by rfl) ⟨133023, by rfl⟩ : syracuseStep 1418917 = 266047) (by norm_num)
theorem B6383285 : Blo 1260448 6383285 := bbase (se 5 (by rfl) ⟨299216, by rfl⟩ : syracuseStep 6383285 = 598433) (by norm_num)
theorem B1418953 : Blo 1260448 1418953 := bbase (se 2 (by rfl) ⟨532107, by rfl⟩ : syracuseStep 1418953 = 1064215) (by norm_num)
theorem B3155669 : Blo 1260448 3155669 := bbase (se 7 (by rfl) ⟨36980, by rfl⟩ : syracuseStep 3155669 = 73961) (by norm_num)
theorem B3032797 : Blo 1260448 3032797 := bbase (se 3 (by rfl) ⟨568649, by rfl⟩ : syracuseStep 3032797 = 1137299) (by norm_num)
theorem B2836205 : Blo 1260448 2836205 := bbase (se 3 (by rfl) ⟨531788, by rfl⟩ : syracuseStep 2836205 = 1063577) (by norm_num)
theorem B1418989 : Blo 1260448 1418989 := bbase (se 3 (by rfl) ⟨266060, by rfl⟩ : syracuseStep 1418989 = 532121) (by norm_num)
theorem B4040437 : Blo 1260448 4040437 := bbase (se 5 (by rfl) ⟨189395, by rfl⟩ : syracuseStep 4040437 = 378791) (by norm_num)
theorem B2393869 : Blo 1260448 2393869 := bbase (se 3 (by rfl) ⟨448850, by rfl⟩ : syracuseStep 2393869 = 897701) (by norm_num)
theorem B1419025 : Blo 1260448 1419025 := bbase (se 2 (by rfl) ⟨532134, by rfl⟩ : syracuseStep 1419025 = 1064269) (by norm_num)
theorem B2877221 : Blo 1260448 2877221 := bbase (se 4 (by rfl) ⟨269739, by rfl⟩ : syracuseStep 2877221 = 539479) (by norm_num)
theorem B2836277 : Blo 1260448 2836277 := bbase (se 5 (by rfl) ⟨132950, by rfl⟩ : syracuseStep 2836277 = 265901) (by norm_num)
theorem B1419061 : Blo 1260448 1419061 := bbase (se 5 (by rfl) ⟨66518, by rfl⟩ : syracuseStep 1419061 = 133037) (by norm_num)
theorem B1419097 : Blo 1260448 1419097 := bbase (se 2 (by rfl) ⟨532161, by rfl⟩ : syracuseStep 1419097 = 1064323) (by norm_num)
theorem B4786037 : Blo 1260448 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B2836349 : Blo 1260448 2836349 := bbase (se 3 (by rfl) ⟨531815, by rfl⟩ : syracuseStep 2836349 = 1063631) (by norm_num)
theorem B1419133 : Blo 1260448 1419133 := bbase (se 3 (by rfl) ⟨266087, by rfl⟩ : syracuseStep 1419133 = 532175) (by norm_num)
theorem B1419169 : Blo 1260448 1419169 := bbase (se 2 (by rfl) ⟨532188, by rfl⟩ : syracuseStep 1419169 = 1064377) (by norm_num)
theorem B2394029 : Blo 1260448 2394029 := bbase (se 3 (by rfl) ⟨448880, by rfl⟩ : syracuseStep 2394029 = 897761) (by norm_num)
theorem B1402805 : Blo 1260448 1402805 := bbase (se 5 (by rfl) ⟨65756, by rfl⟩ : syracuseStep 1402805 = 131513) (by norm_num)
theorem B8636341 : Blo 1260448 8636341 := bbase (se 5 (by rfl) ⟨404828, by rfl⟩ : syracuseStep 8636341 = 809657) (by norm_num)
theorem B2557885 : Blo 1260448 2557885 := bbase (se 3 (by rfl) ⟨479603, by rfl⟩ : syracuseStep 2557885 = 959207) (by norm_num)
theorem B2836421 : Blo 1260448 2836421 := bbase (se 4 (by rfl) ⟨265914, by rfl⟩ : syracuseStep 2836421 = 531829) (by norm_num)
theorem B1419205 : Blo 1260448 1419205 := bbase (se 4 (by rfl) ⟨133050, by rfl⟩ : syracuseStep 1419205 = 266101) (by norm_num)
theorem B1918925 : Blo 1260448 1918925 := bbase (se 3 (by rfl) ⟨359798, by rfl⟩ : syracuseStep 1918925 = 719597) (by norm_num)
theorem B1419241 : Blo 1260448 1419241 := bbase (se 2 (by rfl) ⟨532215, by rfl⟩ : syracuseStep 1419241 = 1064431) (by norm_num)
theorem B2836493 : Blo 1260448 2836493 := bbase (se 3 (by rfl) ⟨531842, by rfl⟩ : syracuseStep 2836493 = 1063685) (by norm_num)
theorem B1419277 : Blo 1260448 1419277 := bbase (se 3 (by rfl) ⟨266114, by rfl⟩ : syracuseStep 1419277 = 532229) (by norm_num)
theorem B1419313 : Blo 1260448 1419313 := bbase (se 2 (by rfl) ⟨532242, by rfl⟩ : syracuseStep 1419313 = 1064485) (by norm_num)
theorem B2394173 : Blo 1260448 2394173 := bbase (se 3 (by rfl) ⟨448907, by rfl⟩ : syracuseStep 2394173 = 897815) (by norm_num)
theorem B2836565 : Blo 1260448 2836565 := bbase (se 8 (by rfl) ⟨16620, by rfl⟩ : syracuseStep 2836565 = 33241) (by norm_num)
theorem B1419349 : Blo 1260448 1419349 := bbase (se 8 (by rfl) ⟨8316, by rfl⟩ : syracuseStep 1419349 = 16633) (by norm_num)
theorem B1419385 : Blo 1260448 1419385 := bbase (se 2 (by rfl) ⟨532269, by rfl⟩ : syracuseStep 1419385 = 1064539) (by norm_num)
theorem B2836637 : Blo 1260448 2836637 := bbase (se 3 (by rfl) ⟨531869, by rfl⟩ : syracuseStep 2836637 = 1063739) (by norm_num)
theorem B1419421 : Blo 1260448 1419421 := bbase (se 3 (by rfl) ⟨266141, by rfl⟩ : syracuseStep 1419421 = 532283) (by norm_num)
theorem B1419457 : Blo 1260448 1419457 := bbase (se 2 (by rfl) ⟨532296, by rfl⟩ : syracuseStep 1419457 = 1064593) (by norm_num)
theorem B44902613 : Blo 1260448 44902613 := bbase (se 7 (by rfl) ⟨526202, by rfl⟩ : syracuseStep 44902613 = 1052405) (by norm_num)
theorem B2427101 : Blo 1260448 2427101 := bbase (se 3 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 2427101 = 910163) (by norm_num)
theorem B2836709 : Blo 1260448 2836709 := bbase (se 4 (by rfl) ⟨265941, by rfl⟩ : syracuseStep 2836709 = 531883) (by norm_num)
theorem B1419493 : Blo 1260448 1419493 := bbase (se 4 (by rfl) ⟨133077, by rfl⟩ : syracuseStep 1419493 = 266155) (by norm_num)
theorem B2271485 : Blo 1260448 2271485 := bbase (se 3 (by rfl) ⟨425903, by rfl⟩ : syracuseStep 2271485 = 851807) (by norm_num)
theorem B1419529 : Blo 1260448 1419529 := bbase (se 2 (by rfl) ⟨532323, by rfl⟩ : syracuseStep 1419529 = 1064647) (by norm_num)
theorem B2836781 : Blo 1260448 2836781 := bbase (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) (by norm_num)
theorem B1419565 : Blo 1260448 1419565 := bbase (se 3 (by rfl) ⟨266168, by rfl⟩ : syracuseStep 1419565 = 532337) (by norm_num)
theorem B1419601 : Blo 1260448 1419601 := bbase (se 2 (by rfl) ⟨532350, by rfl⟩ : syracuseStep 1419601 = 1064701) (by norm_num)
theorem B5114197 : Blo 1260448 5114197 := bbase (se 10 (by rfl) ⟨7491, by rfl⟩ : syracuseStep 5114197 = 14983) (by norm_num)
theorem B2394461 : Blo 1260448 2394461 := bbase (se 3 (by rfl) ⟨448961, by rfl⟩ : syracuseStep 2394461 = 897923) (by norm_num)
theorem B2836853 : Blo 1260448 2836853 := bbase (se 5 (by rfl) ⟨132977, by rfl⟩ : syracuseStep 2836853 = 265955) (by norm_num)
theorem B1419637 : Blo 1260448 1419637 := bbase (se 5 (by rfl) ⟨66545, by rfl⟩ : syracuseStep 1419637 = 133091) (by norm_num)
theorem B6064517 : Blo 1260448 6064517 := bbase (se 4 (by rfl) ⟨568548, by rfl⟩ : syracuseStep 6064517 = 1137097) (by norm_num)
theorem B24234389 : Blo 1260448 24234389 := bbase (se 6 (by rfl) ⟨567993, by rfl⟩ : syracuseStep 24234389 = 1135987) (by norm_num)
theorem B1919381 : Blo 1260448 1919381 := bbase (se 6 (by rfl) ⟨44985, by rfl⟩ : syracuseStep 1919381 = 89971) (by norm_num)
theorem B1419673 : Blo 1260448 1419673 := bbase (se 2 (by rfl) ⟨532377, by rfl⟩ : syracuseStep 1419673 = 1064755) (by norm_num)
theorem B2156957 : Blo 1260448 2156957 := bbase (se 3 (by rfl) ⟨404429, by rfl⟩ : syracuseStep 2156957 = 808859) (by norm_num)
theorem B2836925 : Blo 1260448 2836925 := bbase (se 3 (by rfl) ⟨531923, by rfl⟩ : syracuseStep 2836925 = 1063847) (by norm_num)
theorem B1419709 : Blo 1260448 1419709 := bbase (se 3 (by rfl) ⟨266195, by rfl⟩ : syracuseStep 1419709 = 532391) (by norm_num)
theorem B2558405 : Blo 1260448 2558405 := bbase (se 4 (by rfl) ⟨239850, by rfl⟩ : syracuseStep 2558405 = 479701) (by norm_num)
theorem B1346005 : Blo 1260448 1346005 := bbase (se 7 (by rfl) ⟨15773, by rfl⟩ : syracuseStep 1346005 = 31547) (by norm_num)
theorem B1419745 : Blo 1260448 1419745 := bbase (se 2 (by rfl) ⟨532404, by rfl⟩ : syracuseStep 1419745 = 1064809) (by norm_num)
theorem B2394613 : Blo 1260448 2394613 := bbase (se 5 (by rfl) ⟨112247, by rfl⟩ : syracuseStep 2394613 = 224495) (by norm_num)
theorem B2836997 : Blo 1260448 2836997 := bbase (se 4 (by rfl) ⟨265968, by rfl⟩ : syracuseStep 2836997 = 531937) (by norm_num)
theorem B1419781 : Blo 1260448 1419781 := bbase (se 4 (by rfl) ⟨133104, by rfl⟩ : syracuseStep 1419781 = 266209) (by norm_num)
theorem B1419817 : Blo 1260448 1419817 := bbase (se 2 (by rfl) ⟨532431, by rfl⟩ : syracuseStep 1419817 = 1064863) (by norm_num)
theorem B4041269 : Blo 1260448 4041269 := bbase (se 5 (by rfl) ⟨189434, by rfl⟩ : syracuseStep 4041269 = 378869) (by norm_num)
theorem B2837069 : Blo 1260448 2837069 := bbase (se 3 (by rfl) ⟨531950, by rfl⟩ : syracuseStep 2837069 = 1063901) (by norm_num)
theorem B1419853 : Blo 1260448 1419853 := bbase (se 3 (by rfl) ⟨266222, by rfl⟩ : syracuseStep 1419853 = 532445) (by norm_num)
theorem B5384789 : Blo 1260448 5384789 := bbase (se 8 (by rfl) ⟨31551, by rfl⟩ : syracuseStep 5384789 = 63103) (by norm_num)
theorem B2271845 : Blo 1260448 2271845 := bbase (se 4 (by rfl) ⟨212985, by rfl⟩ : syracuseStep 2271845 = 425971) (by norm_num)
theorem B1419889 : Blo 1260448 1419889 := bbase (se 2 (by rfl) ⟨532458, by rfl⟩ : syracuseStep 1419889 = 1064917) (by norm_num)
theorem B2837141 : Blo 1260448 2837141 := bbase (se 6 (by rfl) ⟨66495, by rfl⟩ : syracuseStep 2837141 = 132991) (by norm_num)
theorem B1419925 : Blo 1260448 1419925 := bbase (se 6 (by rfl) ⟨33279, by rfl⟩ : syracuseStep 1419925 = 66559) (by norm_num)
theorem B4254389 : Blo 1260448 4254389 := bbase (se 5 (by rfl) ⟨199424, by rfl⟩ : syracuseStep 4254389 = 398849) (by norm_num)
theorem B1419961 : Blo 1260448 1419961 := bbase (se 2 (by rfl) ⟨532485, by rfl⟩ : syracuseStep 1419961 = 1064971) (by norm_num)
theorem B2837213 : Blo 1260448 2837213 := bbase (se 3 (by rfl) ⟨531977, by rfl⟩ : syracuseStep 2837213 = 1063955) (by norm_num)
theorem B1419997 : Blo 1260448 1419997 := bbase (se 3 (by rfl) ⟨266249, by rfl⟩ : syracuseStep 1419997 = 532499) (by norm_num)
theorem B2271997 : Blo 1260448 2271997 := bbase (se 3 (by rfl) ⟨425999, by rfl⟩ : syracuseStep 2271997 = 851999) (by norm_num)
theorem B1420033 : Blo 1260448 1420033 := bbase (se 2 (by rfl) ⟨532512, by rfl⟩ : syracuseStep 1420033 = 1065025) (by norm_num)
theorem B1346321 : Blo 1260448 1346321 := bbase (se 2 (by rfl) ⟨504870, by rfl⟩ : syracuseStep 1346321 = 1009741) (by norm_num)
theorem B1944341 : Blo 1260448 1944341 := bbase (se 6 (by rfl) ⟨45570, by rfl⟩ : syracuseStep 1944341 = 91141) (by norm_num)
theorem B2837285 : Blo 1260448 2837285 := bbase (se 4 (by rfl) ⟨265995, by rfl⟩ : syracuseStep 2837285 = 531991) (by norm_num)
theorem B2394917 : Blo 1260448 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B1420069 : Blo 1260448 1420069 := bbase (se 4 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 1420069 = 266263) (by norm_num)
theorem B8080181 : Blo 1260448 8080181 := bbase (se 5 (by rfl) ⟨378758, by rfl⟩ : syracuseStep 8080181 = 757517) (by norm_num)
theorem B1796917 : Blo 1260448 1796917 := bbase (se 5 (by rfl) ⟨84230, by rfl⟩ : syracuseStep 1796917 = 168461) (by norm_num)
theorem B3640133 : Blo 1260448 3640133 := bbase (se 4 (by rfl) ⟨341262, by rfl⟩ : syracuseStep 3640133 = 682525) (by norm_num)
theorem B1420105 : Blo 1260448 1420105 := bbase (se 2 (by rfl) ⟨532539, by rfl⟩ : syracuseStep 1420105 = 1065079) (by norm_num)
theorem B2837357 : Blo 1260448 2837357 := bbase (se 3 (by rfl) ⟨532004, by rfl⟩ : syracuseStep 2837357 = 1064009) (by norm_num)
theorem B1420141 : Blo 1260448 1420141 := bbase (se 3 (by rfl) ⟨266276, by rfl⟩ : syracuseStep 1420141 = 532553) (by norm_num)
theorem B1420177 : Blo 1260448 1420177 := bbase (se 2 (by rfl) ⟨532566, by rfl⟩ : syracuseStep 1420177 = 1065133) (by norm_num)
theorem B4549541 : Blo 1260448 4549541 := bbase (se 4 (by rfl) ⟨426519, by rfl⟩ : syracuseStep 4549541 = 853039) (by norm_num)
theorem B2837429 : Blo 1260448 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B12127157 : Blo 1260448 12127157 := bbase (se 5 (by rfl) ⟨568460, by rfl⟩ : syracuseStep 12127157 = 1136921) (by norm_num)
theorem B1420213 : Blo 1260448 1420213 := bbase (se 5 (by rfl) ⟨66572, by rfl⟩ : syracuseStep 1420213 = 133145) (by norm_num)
theorem B6384581 : Blo 1260448 6384581 := bbase (se 4 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 6384581 = 1197109) (by norm_num)
theorem B1420249 : Blo 1260448 1420249 := bbase (se 2 (by rfl) ⟨532593, by rfl⟩ : syracuseStep 1420249 = 1065187) (by norm_num)
theorem B2837501 : Blo 1260448 2837501 := bbase (se 3 (by rfl) ⟨532031, by rfl⟩ : syracuseStep 2837501 = 1064063) (by norm_num)
theorem B4787221 : Blo 1260448 4787221 := bbase (se 6 (by rfl) ⟨112200, by rfl⟩ : syracuseStep 4787221 = 224401) (by norm_num)
theorem B2837573 : Blo 1260448 2837573 := bbase (se 4 (by rfl) ⟨266022, by rfl⟩ : syracuseStep 2837573 = 532045) (by norm_num)
theorem B4254821 : Blo 1260448 4254821 := bbase (se 4 (by rfl) ⟨398889, by rfl⟩ : syracuseStep 4254821 = 797779) (by norm_num)
theorem B2837645 : Blo 1260448 2837645 := bbase (se 3 (by rfl) ⟨532058, by rfl⟩ : syracuseStep 2837645 = 1064117) (by norm_num)
theorem B3591317 : Blo 1260448 3591317 := bbase (se 6 (by rfl) ⟨84171, by rfl⟩ : syracuseStep 3591317 = 168343) (by norm_num)
theorem B1346765 : Blo 1260448 1346765 := bbase (se 3 (by rfl) ⟨252518, by rfl⟩ : syracuseStep 1346765 = 505037) (by norm_num)
theorem B2837717 : Blo 1260448 2837717 := bbase (se 7 (by rfl) ⟨33254, by rfl⟩ : syracuseStep 2837717 = 66509) (by norm_num)
theorem B5115109 : Blo 1260448 5115109 := bbase (se 4 (by rfl) ⟨479541, by rfl⟩ : syracuseStep 5115109 = 959083) (by norm_num)
theorem B4549877 : Blo 1260448 4549877 := bbase (se 5 (by rfl) ⟨213275, by rfl⟩ : syracuseStep 4549877 = 426551) (by norm_num)
theorem B1346825 : Blo 1260448 1346825 := bbase (se 2 (by rfl) ⟨505059, by rfl⟩ : syracuseStep 1346825 = 1010119) (by norm_num)
theorem B2837789 : Blo 1260448 2837789 := bbase (se 3 (by rfl) ⟨532085, by rfl⟩ : syracuseStep 2837789 = 1064171) (by norm_num)
theorem B4787525 : Blo 1260448 4787525 := bbase (se 4 (by rfl) ⟨448830, by rfl⟩ : syracuseStep 4787525 = 897661) (by norm_num)
theorem B2837861 : Blo 1260448 2837861 := bbase (se 4 (by rfl) ⟨266049, by rfl⟩ : syracuseStep 2837861 = 532099) (by norm_num)
theorem B1797509 : Blo 1260448 1797509 := bbase (se 4 (by rfl) ⟨168516, by rfl⟩ : syracuseStep 1797509 = 337033) (by norm_num)
theorem B1346953 : Blo 1260448 1346953 := bbase (se 2 (by rfl) ⟨505107, by rfl⟩ : syracuseStep 1346953 = 1010215) (by norm_num)
theorem B2837933 : Blo 1260448 2837933 := bbase (se 3 (by rfl) ⟨532112, by rfl⟩ : syracuseStep 2837933 = 1064225) (by norm_num)
theorem B2157997 : Blo 1260448 2157997 := bbase (se 3 (by rfl) ⟨404624, by rfl⟩ : syracuseStep 2157997 = 809249) (by norm_num)
theorem B1617389 : Blo 1260448 1617389 := bbase (se 3 (by rfl) ⟨303260, by rfl⟩ : syracuseStep 1617389 = 606521) (by norm_num)
theorem B2838005 : Blo 1260448 2838005 := bbase (se 5 (by rfl) ⟨133031, by rfl⟩ : syracuseStep 2838005 = 266063) (by norm_num)
theorem B4255253 : Blo 1260448 4255253 := bbase (se 6 (by rfl) ⟨99732, by rfl⟩ : syracuseStep 4255253 = 199465) (by norm_num)
theorem B2395669 : Blo 1260448 2395669 := bbase (se 6 (by rfl) ⟨56148, by rfl⟩ : syracuseStep 2395669 = 112297) (by norm_num)
theorem B2838077 : Blo 1260448 2838077 := bbase (se 3 (by rfl) ⟨532139, by rfl⟩ : syracuseStep 2838077 = 1064279) (by norm_num)
theorem B5385797 : Blo 1260448 5385797 := bbase (se 4 (by rfl) ⟨504918, by rfl⟩ : syracuseStep 5385797 = 1009837) (by norm_num)
theorem B2838149 : Blo 1260448 2838149 := bbase (se 4 (by rfl) ⟨266076, by rfl⟩ : syracuseStep 2838149 = 532153) (by norm_num)
theorem B2395813 : Blo 1260448 2395813 := bbase (se 4 (by rfl) ⟨224607, by rfl⟩ : syracuseStep 2395813 = 449215) (by norm_num)
theorem B2838221 : Blo 1260448 2838221 := bbase (se 3 (by rfl) ⟨532166, by rfl⟩ : syracuseStep 2838221 = 1064333) (by norm_num)
theorem B3190549 : Blo 1260448 3190549 := bbase (se 6 (by rfl) ⟨74778, by rfl⟩ : syracuseStep 3190549 = 149557) (by norm_num)
theorem B2838293 : Blo 1260448 2838293 := bbase (se 6 (by rfl) ⟨66522, by rfl⟩ : syracuseStep 2838293 = 133045) (by norm_num)
theorem B6065941 : Blo 1260448 6065941 := bbase (se 6 (by rfl) ⟨142170, by rfl⟩ : syracuseStep 6065941 = 284341) (by norm_num)
theorem B3591989 : Blo 1260448 3591989 := bbase (se 5 (by rfl) ⟨168374, by rfl⟩ : syracuseStep 3591989 = 336749) (by norm_num)
theorem B2273093 : Blo 1260448 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B1347397 : Blo 1260448 1347397 := bbase (se 4 (by rfl) ⟨126318, by rfl⟩ : syracuseStep 1347397 = 252637) (by norm_num)
theorem B2395973 : Blo 1260448 2395973 := bbase (se 4 (by rfl) ⟨224622, by rfl⟩ : syracuseStep 2395973 = 449245) (by norm_num)
theorem B2838365 : Blo 1260448 2838365 := bbase (se 3 (by rfl) ⟨532193, by rfl⟩ : syracuseStep 2838365 = 1064387) (by norm_num)
theorem B2158429 : Blo 1260448 2158429 := bbase (se 3 (by rfl) ⟨404705, by rfl⟩ : syracuseStep 2158429 = 809411) (by norm_num)
theorem B3190661 : Blo 1260448 3190661 := bbase (se 4 (by rfl) ⟨299124, by rfl⟩ : syracuseStep 3190661 = 598249) (by norm_num)
theorem B2838437 : Blo 1260448 2838437 := bbase (se 4 (by rfl) ⟨266103, by rfl⟩ : syracuseStep 2838437 = 532207) (by norm_num)
theorem B1347517 : Blo 1260448 1347517 := bbase (se 3 (by rfl) ⟨252659, by rfl⟩ : syracuseStep 1347517 = 505319) (by norm_num)
theorem B4255685 : Blo 1260448 4255685 := bbase (se 4 (by rfl) ⟨398970, by rfl⟩ : syracuseStep 4255685 = 797941) (by norm_num)
theorem B2396117 : Blo 1260448 2396117 := bbase (se 7 (by rfl) ⟨28079, by rfl⟩ : syracuseStep 2396117 = 56159) (by norm_num)
theorem B2838509 : Blo 1260448 2838509 := bbase (se 3 (by rfl) ⟨532220, by rfl⟩ : syracuseStep 2838509 = 1064441) (by norm_num)
theorem B2838581 : Blo 1260448 2838581 := bbase (se 5 (by rfl) ⟨133058, by rfl⟩ : syracuseStep 2838581 = 266117) (by norm_num)
theorem B7188533 : Blo 1260448 7188533 := bbase (se 5 (by rfl) ⟨336962, by rfl⟩ : syracuseStep 7188533 = 673925) (by norm_num)
theorem B3190853 : Blo 1260448 3190853 := bbase (se 4 (by rfl) ⟨299142, by rfl⟩ : syracuseStep 3190853 = 598285) (by norm_num)
theorem B2838653 : Blo 1260448 2838653 := bbase (se 3 (by rfl) ⟨532247, by rfl⟩ : syracuseStep 2838653 = 1064495) (by norm_num)
theorem B1347769 : Blo 1260448 1347769 := bbase (se 2 (by rfl) ⟨505413, by rfl⟩ : syracuseStep 1347769 = 1010827) (by norm_num)
theorem B1347773 : Blo 1260448 1347773 := bbase (se 3 (by rfl) ⟨252707, by rfl⟩ : syracuseStep 1347773 = 505415) (by norm_num)
theorem B2838725 : Blo 1260448 2838725 := bbase (se 4 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 2838725 = 532261) (by norm_num)
theorem B10367189 : Blo 1260448 10367189 := bbase (se 7 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 10367189 = 242981) (by norm_num)
theorem B6385877 : Blo 1260448 6385877 := bbase (se 7 (by rfl) ⟨74834, by rfl⟩ : syracuseStep 6385877 = 149669) (by norm_num)
theorem B3592421 : Blo 1260448 3592421 := bbase (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) (by norm_num)
theorem B2396405 : Blo 1260448 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B2838797 : Blo 1260448 2838797 := bbase (se 3 (by rfl) ⟨532274, by rfl⟩ : syracuseStep 2838797 = 1064549) (by norm_num)
theorem B2806037 : Blo 1260448 2806037 := bbase (se 6 (by rfl) ⟨65766, by rfl⟩ : syracuseStep 2806037 = 131533) (by norm_num)
theorem B2158901 : Blo 1260448 2158901 := bbase (se 5 (by rfl) ⟨101198, by rfl⟩ : syracuseStep 2158901 = 202397) (by norm_num)
theorem B2838869 : Blo 1260448 2838869 := bbase (se 10 (by rfl) ⟨4158, by rfl⟩ : syracuseStep 2838869 = 8317) (by norm_num)
theorem B1536349 : Blo 1260448 1536349 := bbase (se 3 (by rfl) ⟨288065, by rfl⟩ : syracuseStep 1536349 = 576131) (by norm_num)
theorem B4256117 : Blo 1260448 4256117 := bbase (se 5 (by rfl) ⟨199505, by rfl⟩ : syracuseStep 4256117 = 399011) (by norm_num)
theorem B4043141 : Blo 1260448 4043141 := bbase (se 4 (by rfl) ⟨379044, by rfl⟩ : syracuseStep 4043141 = 758089) (by norm_num)
theorem B2396557 : Blo 1260448 2396557 := bbase (se 3 (by rfl) ⟨449354, by rfl⟩ : syracuseStep 2396557 = 898709) (by norm_num)
theorem B3191197 : Blo 1260448 3191197 := bbase (se 3 (by rfl) ⟨598349, by rfl⟩ : syracuseStep 3191197 = 1196699) (by norm_num)
theorem B2838941 : Blo 1260448 2838941 := bbase (se 3 (by rfl) ⟨532301, by rfl⟩ : syracuseStep 2838941 = 1064603) (by norm_num)
theorem B2839013 : Blo 1260448 2839013 := bbase (se 4 (by rfl) ⟨266157, by rfl⟩ : syracuseStep 2839013 = 532315) (by norm_num)
theorem B3191309 : Blo 1260448 3191309 := bbase (se 3 (by rfl) ⟨598370, by rfl⟩ : syracuseStep 3191309 = 1196741) (by norm_num)
theorem B2839085 : Blo 1260448 2839085 := bbase (se 3 (by rfl) ⟨532328, by rfl⟩ : syracuseStep 2839085 = 1064657) (by norm_num)
theorem B2019917 : Blo 1260448 2019917 := bbase (se 3 (by rfl) ⟨378734, by rfl⟩ : syracuseStep 2019917 = 757469) (by norm_num)
theorem B2839157 : Blo 1260448 2839157 := bbase (se 5 (by rfl) ⟨133085, by rfl⟩ : syracuseStep 2839157 = 266171) (by norm_num)
theorem B2839229 : Blo 1260448 2839229 := bbase (se 3 (by rfl) ⟨532355, by rfl⟩ : syracuseStep 2839229 = 1064711) (by norm_num)
theorem B3191501 : Blo 1260448 3191501 := bbase (se 3 (by rfl) ⟨598406, by rfl⟩ : syracuseStep 3191501 = 1196813) (by norm_num)
theorem B2839301 : Blo 1260448 2839301 := bbase (se 4 (by rfl) ⟨266184, by rfl⟩ : syracuseStep 2839301 = 532369) (by norm_num)
theorem B4256549 : Blo 1260448 4256549 := bbase (se 4 (by rfl) ⟨399051, by rfl⟩ : syracuseStep 4256549 = 798103) (by norm_num)
theorem B6820661 : Blo 1260448 6820661 := bbase (se 5 (by rfl) ⟨319718, by rfl⟩ : syracuseStep 6820661 = 639437) (by norm_num)
theorem B2839373 : Blo 1260448 2839373 := bbase (se 3 (by rfl) ⟨532382, by rfl⟩ : syracuseStep 2839373 = 1064765) (by norm_num)
theorem B2839445 : Blo 1260448 2839445 := bbase (se 6 (by rfl) ⟨66549, by rfl⟩ : syracuseStep 2839445 = 133099) (by norm_num)
theorem B3593173 : Blo 1260448 3593173 := bbase (se 7 (by rfl) ⟨42107, by rfl⟩ : syracuseStep 3593173 = 84215) (by norm_num)
theorem B2839517 : Blo 1260448 2839517 := bbase (se 3 (by rfl) ⟨532409, by rfl⟩ : syracuseStep 2839517 = 1064819) (by norm_num)
theorem B2020373 : Blo 1260448 2020373 := bbase (se 6 (by rfl) ⟨47352, by rfl⟩ : syracuseStep 2020373 = 94705) (by norm_num)
theorem B3191845 : Blo 1260448 3191845 := bbase (se 4 (by rfl) ⟨299235, by rfl⟩ : syracuseStep 3191845 = 598471) (by norm_num)
theorem B2839589 : Blo 1260448 2839589 := bbase (se 4 (by rfl) ⟨266211, by rfl⟩ : syracuseStep 2839589 = 532423) (by norm_num)
theorem B2839661 : Blo 1260448 2839661 := bbase (se 3 (by rfl) ⟨532436, by rfl⟩ : syracuseStep 2839661 = 1064873) (by norm_num)
theorem B3191957 : Blo 1260448 3191957 := bbase (se 6 (by rfl) ⟨74811, by rfl⟩ : syracuseStep 3191957 = 149623) (by norm_num)
theorem B1365157 : Blo 1260448 1365157 := bbase (se 4 (by rfl) ⟨127983, by rfl⟩ : syracuseStep 1365157 = 255967) (by norm_num)
theorem B2839733 : Blo 1260448 2839733 := bbase (se 5 (by rfl) ⟨133112, by rfl⟩ : syracuseStep 2839733 = 266225) (by norm_num)
theorem B2127053 : Blo 1260448 2127053 := bbase (se 3 (by rfl) ⟨398822, by rfl⟩ : syracuseStep 2127053 = 797645) (by norm_num)
theorem B4256981 : Blo 1260448 4256981 := bbase (se 7 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 4256981 = 99773) (by norm_num)
theorem B2839805 : Blo 1260448 2839805 := bbase (se 3 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 2839805 = 1064927) (by norm_num)
theorem B1438993 : Blo 1260448 1438993 := bbase (se 2 (by rfl) ⟨539622, by rfl⟩ : syracuseStep 1438993 = 1079245) (by norm_num)
theorem B5387573 : Blo 1260448 5387573 := bbase (se 5 (by rfl) ⟨252542, by rfl⟩ : syracuseStep 5387573 = 505085) (by norm_num)
theorem B2839877 : Blo 1260448 2839877 := bbase (se 4 (by rfl) ⟨266238, by rfl⟩ : syracuseStep 2839877 = 532477) (by norm_num)
theorem B2127181 : Blo 1260448 2127181 := bbase (se 3 (by rfl) ⟨398846, by rfl⟩ : syracuseStep 2127181 = 797693) (by norm_num)
theorem B3192149 : Blo 1260448 3192149 := bbase (se 13 (by rfl) ⟨584, by rfl⟩ : syracuseStep 3192149 = 1169) (by norm_num)
theorem B4789637 : Blo 1260448 4789637 := bbase (se 4 (by rfl) ⟨449028, by rfl⟩ : syracuseStep 4789637 = 898057) (by norm_num)
theorem B2839949 : Blo 1260448 2839949 := bbase (se 3 (by rfl) ⟨532490, by rfl⟩ : syracuseStep 2839949 = 1064981) (by norm_num)
theorem B2127269 : Blo 1260448 2127269 := bbase (se 4 (by rfl) ⟨199431, by rfl⟩ : syracuseStep 2127269 = 398863) (by norm_num)
theorem B2840021 : Blo 1260448 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B6387173 : Blo 1260448 6387173 := bbase (se 4 (by rfl) ⟨598797, by rfl⟩ : syracuseStep 6387173 = 1197595) (by norm_num)
theorem B14374421 : Blo 1260448 14374421 := bbase (se 6 (by rfl) ⟨336900, by rfl⟩ : syracuseStep 14374421 = 673801) (by norm_num)
theorem B2840093 : Blo 1260448 2840093 := bbase (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) (by norm_num)
theorem B2127397 : Blo 1260448 2127397 := bbase (se 4 (by rfl) ⟨199443, by rfl⟩ : syracuseStep 2127397 = 398887) (by norm_num)
theorem B1619525 : Blo 1260448 1619525 := bbase (se 4 (by rfl) ⟨151830, by rfl⟩ : syracuseStep 1619525 = 303661) (by norm_num)
theorem B2692693 : Blo 1260448 2692693 := bbase (se 8 (by rfl) ⟨15777, by rfl⟩ : syracuseStep 2692693 = 31555) (by norm_num)
theorem B2840165 : Blo 1260448 2840165 := bbase (se 4 (by rfl) ⟨266265, by rfl⟩ : syracuseStep 2840165 = 532531) (by norm_num)
theorem B2127485 : Blo 1260448 2127485 := bbase (se 3 (by rfl) ⟨398903, by rfl⟩ : syracuseStep 2127485 = 797807) (by norm_num)
theorem B4257413 : Blo 1260448 4257413 := bbase (se 4 (by rfl) ⟨399132, by rfl⟩ : syracuseStep 4257413 = 798265) (by norm_num)
theorem B5117573 : Blo 1260448 5117573 := bbase (se 4 (by rfl) ⟨479772, by rfl⟩ : syracuseStep 5117573 = 959545) (by norm_num)
theorem B4789925 : Blo 1260448 4789925 := bbase (se 4 (by rfl) ⟨449055, by rfl⟩ : syracuseStep 4789925 = 898111) (by norm_num)
theorem B3192493 : Blo 1260448 3192493 := bbase (se 3 (by rfl) ⟨598592, by rfl⟩ : syracuseStep 3192493 = 1197185) (by norm_num)
theorem B2840237 : Blo 1260448 2840237 := bbase (se 3 (by rfl) ⟨532544, by rfl⟩ : syracuseStep 2840237 = 1065089) (by norm_num)
theorem B2840309 : Blo 1260448 2840309 := bbase (se 5 (by rfl) ⟨133139, by rfl⟩ : syracuseStep 2840309 = 266279) (by norm_num)
theorem B2127613 : Blo 1260448 2127613 := bbase (se 3 (by rfl) ⟨398927, by rfl⟩ : syracuseStep 2127613 = 797855) (by norm_num)
theorem B3192605 : Blo 1260448 3192605 := bbase (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) (by norm_num)
theorem B2840381 : Blo 1260448 2840381 := bbase (se 3 (by rfl) ⟨532571, by rfl⟩ : syracuseStep 2840381 = 1065143) (by norm_num)
theorem B1365833 : Blo 1260448 1365833 := bbase (se 2 (by rfl) ⟨512187, by rfl⟩ : syracuseStep 1365833 = 1024375) (by norm_num)
theorem B2127701 : Blo 1260448 2127701 := bbase (se 9 (by rfl) ⟨6233, by rfl⟩ : syracuseStep 2127701 = 12467) (by norm_num)
theorem B2840453 : Blo 1260448 2840453 := bbase (se 4 (by rfl) ⟨266292, by rfl⟩ : syracuseStep 2840453 = 532585) (by norm_num)
theorem B3028877 : Blo 1260448 3028877 := bbase (se 3 (by rfl) ⟨567914, by rfl⟩ : syracuseStep 3028877 = 1135829) (by norm_num)
theorem B1595305 : Blo 1260448 1595305 := bbase (se 2 (by rfl) ⟨598239, by rfl⟩ : syracuseStep 1595305 = 1196479) (by norm_num)
theorem B2127829 : Blo 1260448 2127829 := bbase (se 7 (by rfl) ⟨24935, by rfl⟩ : syracuseStep 2127829 = 49871) (by norm_num)
theorem B3192797 : Blo 1260448 3192797 := bbase (se 3 (by rfl) ⟨598649, by rfl⟩ : syracuseStep 3192797 = 1197299) (by norm_num)
theorem B2021365 : Blo 1260448 2021365 := bbase (se 5 (by rfl) ⟨94751, by rfl⟩ : syracuseStep 2021365 = 189503) (by norm_num)
theorem B1366021 : Blo 1260448 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B18176021 : Blo 1260448 18176021 := bbase (se 6 (by rfl) ⟨426000, by rfl⟩ : syracuseStep 18176021 = 852001) (by norm_num)
theorem B2127917 : Blo 1260448 2127917 := bbase (se 3 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 2127917 = 797969) (by norm_num)
theorem B4257845 : Blo 1260448 4257845 := bbase (se 5 (by rfl) ⟨199586, by rfl⟩ : syracuseStep 4257845 = 399173) (by norm_num)
theorem B3889205 : Blo 1260448 3889205 := bbase (se 5 (by rfl) ⟨182306, by rfl⟩ : syracuseStep 3889205 = 364613) (by norm_num)
theorem B2693189 : Blo 1260448 2693189 := bbase (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) (by norm_num)
theorem B1595477 : Blo 1260448 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B1595533 : Blo 1260448 1595533 := bbase (se 3 (by rfl) ⟨299162, by rfl⟩ : syracuseStep 1595533 = 598325) (by norm_num)
theorem B21559445 : Blo 1260448 21559445 := bbase (se 6 (by rfl) ⟨505299, by rfl⟩ : syracuseStep 21559445 = 1010599) (by norm_num)
theorem B2128045 : Blo 1260448 2128045 := bbase (se 3 (by rfl) ⟨399008, by rfl⟩ : syracuseStep 2128045 = 798017) (by norm_num)
theorem B1595629 : Blo 1260448 1595629 := bbase (se 3 (by rfl) ⟨299180, by rfl⟩ : syracuseStep 1595629 = 598361) (by norm_num)
theorem B2128133 : Blo 1260448 2128133 := bbase (se 4 (by rfl) ⟨199512, by rfl⟩ : syracuseStep 2128133 = 399025) (by norm_num)
theorem B3193141 : Blo 1260448 3193141 := bbase (se 5 (by rfl) ⟨149678, by rfl⟩ : syracuseStep 3193141 = 299357) (by norm_num)
theorem B1890677 : Blo 1260448 1890677 := bbase (se 5 (by rfl) ⟨88625, by rfl⟩ : syracuseStep 1890677 = 177251) (by norm_num)
theorem B2128261 : Blo 1260448 2128261 := bbase (se 4 (by rfl) ⟨199524, by rfl⟩ : syracuseStep 2128261 = 399049) (by norm_num)
theorem B1890701 : Blo 1260448 1890701 := bbase (se 3 (by rfl) ⟨354506, by rfl⟩ : syracuseStep 1890701 = 709013) (by norm_num)
theorem B1595801 : Blo 1260448 1595801 := bbase (se 2 (by rfl) ⟨598425, by rfl⟩ : syracuseStep 1595801 = 1196851) (by norm_num)
theorem B3029405 : Blo 1260448 3029405 := bbase (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) (by norm_num)
theorem B1890725 : Blo 1260448 1890725 := bbase (se 4 (by rfl) ⟨177255, by rfl⟩ : syracuseStep 1890725 = 354511) (by norm_num)
theorem B3193253 : Blo 1260448 3193253 := bbase (se 4 (by rfl) ⟨299367, by rfl⟩ : syracuseStep 3193253 = 598735) (by norm_num)
theorem B1890749 : Blo 1260448 1890749 := bbase (se 3 (by rfl) ⟨354515, by rfl⟩ : syracuseStep 1890749 = 709031) (by norm_num)
theorem B1595857 : Blo 1260448 1595857 := bbase (se 2 (by rfl) ⟨598446, by rfl⟩ : syracuseStep 1595857 = 1196893) (by norm_num)
theorem B1890773 : Blo 1260448 1890773 := bbase (se 7 (by rfl) ⟨22157, by rfl⟩ : syracuseStep 1890773 = 44315) (by norm_num)
theorem B2128349 : Blo 1260448 2128349 := bbase (se 3 (by rfl) ⟨399065, by rfl⟩ : syracuseStep 2128349 = 798131) (by norm_num)
theorem B4258277 : Blo 1260448 4258277 := bbase (se 4 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 4258277 = 798427) (by norm_num)
theorem B1890797 : Blo 1260448 1890797 := bbase (se 3 (by rfl) ⟨354524, by rfl⟩ : syracuseStep 1890797 = 709049) (by norm_num)
theorem B1366517 : Blo 1260448 1366517 := bbase (se 5 (by rfl) ⟨64055, by rfl⟩ : syracuseStep 1366517 = 128111) (by norm_num)
theorem B1890821 : Blo 1260448 1890821 := bbase (se 4 (by rfl) ⟨177264, by rfl⟩ : syracuseStep 1890821 = 354529) (by norm_num)
theorem B1890845 : Blo 1260448 1890845 := bbase (se 3 (by rfl) ⟨354533, by rfl⟩ : syracuseStep 1890845 = 709067) (by norm_num)
theorem B1595953 : Blo 1260448 1595953 := bbase (se 2 (by rfl) ⟨598482, by rfl⟩ : syracuseStep 1595953 = 1196965) (by norm_num)
theorem B1890869 : Blo 1260448 1890869 := bbase (se 5 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 1890869 = 177269) (by norm_num)
theorem B1890893 : Blo 1260448 1890893 := bbase (se 3 (by rfl) ⟨354542, by rfl⟩ : syracuseStep 1890893 = 709085) (by norm_num)
theorem B26950229 : Blo 1260448 26950229 := bbase (se 8 (by rfl) ⟨157911, by rfl⟩ : syracuseStep 26950229 = 315823) (by norm_num)
theorem B2128477 : Blo 1260448 2128477 := bbase (se 3 (by rfl) ⟨399089, by rfl⟩ : syracuseStep 2128477 = 798179) (by norm_num)
theorem B1890917 : Blo 1260448 1890917 := bbase (se 4 (by rfl) ⟨177273, by rfl⟩ : syracuseStep 1890917 = 354547) (by norm_num)
theorem B3193445 : Blo 1260448 3193445 := bbase (se 4 (by rfl) ⟨299385, by rfl⟩ : syracuseStep 3193445 = 598771) (by norm_num)
theorem B1890941 : Blo 1260448 1890941 := bbase (se 3 (by rfl) ⟨354551, by rfl⟩ : syracuseStep 1890941 = 709103) (by norm_num)
theorem B2022013 : Blo 1260448 2022013 := bbase (se 3 (by rfl) ⟨379127, by rfl⟩ : syracuseStep 2022013 = 758255) (by norm_num)
theorem B3029645 : Blo 1260448 3029645 := bbase (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) (by norm_num)
theorem B1890965 : Blo 1260448 1890965 := bbase (se 6 (by rfl) ⟨44319, by rfl⟩ : syracuseStep 1890965 = 88639) (by norm_num)
theorem B1890989 : Blo 1260448 1890989 := bbase (se 3 (by rfl) ⟨354560, by rfl⟩ : syracuseStep 1890989 = 709121) (by norm_num)
theorem B2128565 : Blo 1260448 2128565 := bbase (se 5 (by rfl) ⟨99776, by rfl⟩ : syracuseStep 2128565 = 199553) (by norm_num)
theorem B1891013 : Blo 1260448 1891013 := bbase (se 4 (by rfl) ⟨177282, by rfl⟩ : syracuseStep 1891013 = 354565) (by norm_num)
theorem B3693269 : Blo 1260448 3693269 := bbase (se 7 (by rfl) ⟨43280, by rfl⟩ : syracuseStep 3693269 = 86561) (by norm_num)
theorem B1891037 : Blo 1260448 1891037 := bbase (se 3 (by rfl) ⟨354569, by rfl⟩ : syracuseStep 1891037 = 709139) (by norm_num)
theorem B1596125 : Blo 1260448 1596125 := bbase (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) (by norm_num)
theorem B1891061 : Blo 1260448 1891061 := bbase (se 5 (by rfl) ⟨88643, by rfl⟩ : syracuseStep 1891061 = 177287) (by norm_num)
theorem B6388469 : Blo 1260448 6388469 := bbase (se 5 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 6388469 = 598919) (by norm_num)
theorem B1891085 : Blo 1260448 1891085 := bbase (se 3 (by rfl) ⟨354578, by rfl⟩ : syracuseStep 1891085 = 709157) (by norm_num)
theorem B1596181 : Blo 1260448 1596181 := bbase (se 6 (by rfl) ⟨37410, by rfl⟩ : syracuseStep 1596181 = 74821) (by norm_num)
theorem B1891109 : Blo 1260448 1891109 := bbase (se 4 (by rfl) ⟨177291, by rfl⟩ : syracuseStep 1891109 = 354583) (by norm_num)
theorem B2128693 : Blo 1260448 2128693 := bbase (se 5 (by rfl) ⟨99782, by rfl⟩ : syracuseStep 2128693 = 199565) (by norm_num)
theorem B1891133 : Blo 1260448 1891133 := bbase (se 3 (by rfl) ⟨354587, by rfl⟩ : syracuseStep 1891133 = 709175) (by norm_num)
theorem B4791109 : Blo 1260448 4791109 := bbase (se 4 (by rfl) ⟨449166, by rfl⟩ : syracuseStep 4791109 = 898333) (by norm_num)
theorem B8624981 : Blo 1260448 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B1891157 : Blo 1260448 1891157 := bbase (se 9 (by rfl) ⟨5540, by rfl⟩ : syracuseStep 1891157 = 11081) (by norm_num)
theorem B1891181 : Blo 1260448 1891181 := bbase (se 3 (by rfl) ⟨354596, by rfl⟩ : syracuseStep 1891181 = 709193) (by norm_num)
theorem B1596277 : Blo 1260448 1596277 := bbase (se 5 (by rfl) ⟨74825, by rfl⟩ : syracuseStep 1596277 = 149651) (by norm_num)
theorem B1891205 : Blo 1260448 1891205 := bbase (se 4 (by rfl) ⟨177300, by rfl⟩ : syracuseStep 1891205 = 354601) (by norm_num)
theorem B2128781 : Blo 1260448 2128781 := bbase (se 3 (by rfl) ⟨399146, by rfl⟩ : syracuseStep 2128781 = 798293) (by norm_num)
theorem B8076181 : Blo 1260448 8076181 := bbase (se 6 (by rfl) ⟨189285, by rfl⟩ : syracuseStep 8076181 = 378571) (by norm_num)
theorem B4258709 : Blo 1260448 4258709 := bbase (se 6 (by rfl) ⟨99813, by rfl⟩ : syracuseStep 4258709 = 199627) (by norm_num)
theorem B1891229 : Blo 1260448 1891229 := bbase (se 3 (by rfl) ⟨354605, by rfl⟩ : syracuseStep 1891229 = 709211) (by norm_num)
theorem B1891253 : Blo 1260448 1891253 := bbase (se 5 (by rfl) ⟨88652, by rfl⟩ : syracuseStep 1891253 = 177305) (by norm_num)
theorem B2694077 : Blo 1260448 2694077 := bbase (se 3 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 2694077 = 1010279) (by norm_num)
theorem B3193789 : Blo 1260448 3193789 := bbase (se 3 (by rfl) ⟨598835, by rfl⟩ : syracuseStep 3193789 = 1197671) (by norm_num)
theorem B1891277 : Blo 1260448 1891277 := bbase (se 3 (by rfl) ⟨354614, by rfl⟩ : syracuseStep 1891277 = 709229) (by norm_num)
theorem B3070925 : Blo 1260448 3070925 := bbase (se 3 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 3070925 = 1151597) (by norm_num)
theorem B1891301 : Blo 1260448 1891301 := bbase (se 4 (by rfl) ⟨177309, by rfl⟩ : syracuseStep 1891301 = 354619) (by norm_num)
theorem B1891325 : Blo 1260448 1891325 := bbase (se 3 (by rfl) ⟨354623, by rfl⟩ : syracuseStep 1891325 = 709247) (by norm_num)
theorem B2128909 : Blo 1260448 2128909 := bbase (se 3 (by rfl) ⟨399170, by rfl⟩ : syracuseStep 2128909 = 798341) (by norm_num)
theorem B1891349 : Blo 1260448 1891349 := bbase (se 6 (by rfl) ⟨44328, by rfl⟩ : syracuseStep 1891349 = 88657) (by norm_num)
theorem B1596449 : Blo 1260448 1596449 := bbase (se 2 (by rfl) ⟨598668, by rfl⟩ : syracuseStep 1596449 = 1197337) (by norm_num)
theorem B1891373 : Blo 1260448 1891373 := bbase (se 3 (by rfl) ⟨354632, by rfl⟩ : syracuseStep 1891373 = 709265) (by norm_num)
theorem B3193901 : Blo 1260448 3193901 := bbase (se 3 (by rfl) ⟨598856, by rfl⟩ : syracuseStep 3193901 = 1197713) (by norm_num)
theorem B1514549 : Blo 1260448 1514549 := bbase (se 5 (by rfl) ⟨70994, by rfl⟩ : syracuseStep 1514549 = 141989) (by norm_num)
theorem B2694197 : Blo 1260448 2694197 := bbase (se 5 (by rfl) ⟨126290, by rfl⟩ : syracuseStep 2694197 = 252581) (by norm_num)
theorem B5749829 : Blo 1260448 5749829 := bbase (se 4 (by rfl) ⟨539046, by rfl⟩ : syracuseStep 5749829 = 1078093) (by norm_num)
theorem B1891397 : Blo 1260448 1891397 := bbase (se 4 (by rfl) ⟨177318, by rfl⟩ : syracuseStep 1891397 = 354637) (by norm_num)
theorem B2915405 : Blo 1260448 2915405 := bbase (se 3 (by rfl) ⟨546638, by rfl⟩ : syracuseStep 2915405 = 1093277) (by norm_num)
theorem B1596505 : Blo 1260448 1596505 := bbase (se 2 (by rfl) ⟨598689, by rfl⟩ : syracuseStep 1596505 = 1197379) (by norm_num)
theorem B1891421 : Blo 1260448 1891421 := bbase (se 3 (by rfl) ⟨354641, by rfl⟩ : syracuseStep 1891421 = 709283) (by norm_num)
theorem B2128997 : Blo 1260448 2128997 := bbase (se 4 (by rfl) ⟨199593, by rfl⟩ : syracuseStep 2128997 = 399187) (by norm_num)
theorem B1891445 : Blo 1260448 1891445 := bbase (se 5 (by rfl) ⟨88661, by rfl⟩ : syracuseStep 1891445 = 177323) (by norm_num)
theorem B4791413 : Blo 1260448 4791413 := bbase (se 5 (by rfl) ⟨224597, by rfl⟩ : syracuseStep 4791413 = 449195) (by norm_num)
theorem B1891469 : Blo 1260448 1891469 := bbase (se 3 (by rfl) ⟨354650, by rfl⟩ : syracuseStep 1891469 = 709301) (by norm_num)
theorem B1891493 : Blo 1260448 1891493 := bbase (se 4 (by rfl) ⟨177327, by rfl⟩ : syracuseStep 1891493 = 354655) (by norm_num)
theorem B1596601 : Blo 1260448 1596601 := bbase (se 2 (by rfl) ⟨598725, by rfl⟩ : syracuseStep 1596601 = 1197451) (by norm_num)
theorem B1891517 : Blo 1260448 1891517 := bbase (se 3 (by rfl) ⟨354659, by rfl⟩ : syracuseStep 1891517 = 709319) (by norm_num)
theorem B5749973 : Blo 1260448 5749973 := bbase (se 7 (by rfl) ⟨67382, by rfl⟩ : syracuseStep 5749973 = 134765) (by norm_num)
theorem B1891541 : Blo 1260448 1891541 := bbase (se 7 (by rfl) ⟨22166, by rfl⟩ : syracuseStep 1891541 = 44333) (by norm_num)
theorem B2129125 : Blo 1260448 2129125 := bbase (se 4 (by rfl) ⟨199605, by rfl⟩ : syracuseStep 2129125 = 399211) (by norm_num)
theorem B1891565 : Blo 1260448 1891565 := bbase (se 3 (by rfl) ⟨354668, by rfl⟩ : syracuseStep 1891565 = 709337) (by norm_num)
theorem B3194093 : Blo 1260448 3194093 := bbase (se 3 (by rfl) ⟨598892, by rfl⟩ : syracuseStep 3194093 = 1197785) (by norm_num)
theorem B1891589 : Blo 1260448 1891589 := bbase (se 4 (by rfl) ⟨177336, by rfl⟩ : syracuseStep 1891589 = 354673) (by norm_num)
theorem B1457425 : Blo 1260448 1457425 := bbase (se 2 (by rfl) ⟨546534, by rfl⟩ : syracuseStep 1457425 = 1093069) (by norm_num)
theorem B1891613 : Blo 1260448 1891613 := bbase (se 3 (by rfl) ⟨354677, by rfl⟩ : syracuseStep 1891613 = 709355) (by norm_num)
theorem B1891637 : Blo 1260448 1891637 := bbase (se 5 (by rfl) ⟨88670, by rfl⟩ : syracuseStep 1891637 = 177341) (by norm_num)
theorem B2129213 : Blo 1260448 2129213 := bbase (se 3 (by rfl) ⟨399227, by rfl⟩ : syracuseStep 2129213 = 798455) (by norm_num)
theorem B4259141 : Blo 1260448 4259141 := bbase (se 4 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 4259141 = 798589) (by norm_num)
theorem B1891661 : Blo 1260448 1891661 := bbase (se 3 (by rfl) ⟨354686, by rfl⟩ : syracuseStep 1891661 = 709373) (by norm_num)
theorem B1891685 : Blo 1260448 1891685 := bbase (se 4 (by rfl) ⟨177345, by rfl⟩ : syracuseStep 1891685 = 354691) (by norm_num)
theorem B1596773 : Blo 1260448 1596773 := bbase (se 4 (by rfl) ⟨149697, by rfl⟩ : syracuseStep 1596773 = 299395) (by norm_num)
theorem B1514857 : Blo 1260448 1514857 := bbase (se 2 (by rfl) ⟨568071, by rfl⟩ : syracuseStep 1514857 = 1136143) (by norm_num)
theorem B1891709 : Blo 1260448 1891709 := bbase (se 3 (by rfl) ⟨354695, by rfl⟩ : syracuseStep 1891709 = 709391) (by norm_num)
theorem B1891733 : Blo 1260448 1891733 := bbase (se 6 (by rfl) ⟨44337, by rfl⟩ : syracuseStep 1891733 = 88675) (by norm_num)
theorem B1596829 : Blo 1260448 1596829 := bbase (se 3 (by rfl) ⟨299405, by rfl⟩ : syracuseStep 1596829 = 598811) (by norm_num)
theorem B4095397 : Blo 1260448 4095397 := bbase (se 4 (by rfl) ⟨383943, by rfl⟩ : syracuseStep 4095397 = 767887) (by norm_num)
theorem B1891757 : Blo 1260448 1891757 := bbase (se 3 (by rfl) ⟨354704, by rfl⟩ : syracuseStep 1891757 = 709409) (by norm_num)
theorem B2129341 : Blo 1260448 2129341 := bbase (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) (by norm_num)
theorem B1891781 : Blo 1260448 1891781 := bbase (se 4 (by rfl) ⟨177354, by rfl⟩ : syracuseStep 1891781 = 354709) (by norm_num)
theorem B1514957 : Blo 1260448 1514957 := bbase (se 3 (by rfl) ⟨284054, by rfl⟩ : syracuseStep 1514957 = 568109) (by norm_num)
theorem B1891805 : Blo 1260448 1891805 := bbase (se 3 (by rfl) ⟨354713, by rfl⟩ : syracuseStep 1891805 = 709427) (by norm_num)
theorem B1891829 : Blo 1260448 1891829 := bbase (se 5 (by rfl) ⟨88679, by rfl⟩ : syracuseStep 1891829 = 177359) (by norm_num)
theorem B1596925 : Blo 1260448 1596925 := bbase (se 3 (by rfl) ⟨299423, by rfl⟩ : syracuseStep 1596925 = 598847) (by norm_num)
theorem B1891853 : Blo 1260448 1891853 := bbase (se 3 (by rfl) ⟨354722, by rfl⟩ : syracuseStep 1891853 = 709445) (by norm_num)
theorem B2129429 : Blo 1260448 2129429 := bbase (se 6 (by rfl) ⟨49908, by rfl⟩ : syracuseStep 2129429 = 99817) (by norm_num)
theorem B1891877 : Blo 1260448 1891877 := bbase (se 4 (by rfl) ⟨177363, by rfl⟩ : syracuseStep 1891877 = 354727) (by norm_num)
theorem B1891901 : Blo 1260448 1891901 := bbase (se 3 (by rfl) ⟨354731, by rfl⟩ : syracuseStep 1891901 = 709463) (by norm_num)
theorem B3194437 : Blo 1260448 3194437 := bbase (se 4 (by rfl) ⟨299478, by rfl⟩ : syracuseStep 3194437 = 598957) (by norm_num)
theorem B1891925 : Blo 1260448 1891925 := bbase (se 8 (by rfl) ⟨11085, by rfl⟩ : syracuseStep 1891925 = 22171) (by norm_num)
theorem B4038245 : Blo 1260448 4038245 := bbase (se 4 (by rfl) ⟨378585, by rfl⟩ : syracuseStep 4038245 = 757171) (by norm_num)
theorem B1891949 : Blo 1260448 1891949 := bbase (se 3 (by rfl) ⟨354740, by rfl⟩ : syracuseStep 1891949 = 709481) (by norm_num)
theorem B12131957 : Blo 1260448 12131957 := bbase (se 5 (by rfl) ⟨568685, by rfl⟩ : syracuseStep 12131957 = 1137371) (by norm_num)
theorem B1891973 : Blo 1260448 1891973 := bbase (se 4 (by rfl) ⟨177372, by rfl⟩ : syracuseStep 1891973 = 354745) (by norm_num)
theorem B2129557 : Blo 1260448 2129557 := bbase (se 6 (by rfl) ⟨49911, by rfl⟩ : syracuseStep 2129557 = 99823) (by norm_num)
theorem B1891997 : Blo 1260448 1891997 := bbase (se 3 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 1891997 = 709499) (by norm_num)
theorem B1597097 : Blo 1260448 1597097 := bbase (se 2 (by rfl) ⟨598911, by rfl⟩ : syracuseStep 1597097 = 1197823) (by norm_num)
theorem B2694829 : Blo 1260448 2694829 := bbase (se 3 (by rfl) ⟨505280, by rfl⟩ : syracuseStep 2694829 = 1010561) (by norm_num)
theorem B1892021 : Blo 1260448 1892021 := bbase (se 5 (by rfl) ⟨88688, by rfl⟩ : syracuseStep 1892021 = 177377) (by norm_num)
theorem B3194549 : Blo 1260448 3194549 := bbase (se 5 (by rfl) ⟨149744, by rfl⟩ : syracuseStep 3194549 = 299489) (by norm_num)
theorem B1892045 : Blo 1260448 1892045 := bbase (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) (by norm_num)
theorem B1597153 : Blo 1260448 1597153 := bbase (se 2 (by rfl) ⟨598932, by rfl⟩ : syracuseStep 1597153 = 1197865) (by norm_num)
theorem B1892069 : Blo 1260448 1892069 := bbase (se 4 (by rfl) ⟨177381, by rfl⟩ : syracuseStep 1892069 = 354763) (by norm_num)
theorem B2129645 : Blo 1260448 2129645 := bbase (se 3 (by rfl) ⟨399308, by rfl⟩ : syracuseStep 2129645 = 798617) (by norm_num)
theorem B4259573 : Blo 1260448 4259573 := bbase (se 5 (by rfl) ⟨199667, by rfl⟩ : syracuseStep 4259573 = 399335) (by norm_num)
theorem B1892093 : Blo 1260448 1892093 := bbase (se 3 (by rfl) ⟨354767, by rfl⟩ : syracuseStep 1892093 = 709535) (by norm_num)
theorem B1892117 : Blo 1260448 1892117 := bbase (se 6 (by rfl) ⟨44346, by rfl⟩ : syracuseStep 1892117 = 88693) (by norm_num)
theorem B9584405 : Blo 1260448 9584405 := bbase (se 6 (by rfl) ⟨224634, by rfl⟩ : syracuseStep 9584405 = 449269) (by norm_num)
theorem B1892141 : Blo 1260448 1892141 := bbase (se 3 (by rfl) ⟨354776, by rfl⟩ : syracuseStep 1892141 = 709553) (by norm_num)
theorem B1597249 : Blo 1260448 1597249 := bbase (se 2 (by rfl) ⟨598968, by rfl⟩ : syracuseStep 1597249 = 1197937) (by norm_num)
theorem B1892165 : Blo 1260448 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B92118869 : Blo 1260448 92118869 := bbase (se 9 (by rfl) ⟨269879, by rfl⟩ : syracuseStep 92118869 = 539759) (by norm_num)
theorem B1892189 : Blo 1260448 1892189 := bbase (se 3 (by rfl) ⟨354785, by rfl⟩ : syracuseStep 1892189 = 709571) (by norm_num)
theorem B1515361 : Blo 1260448 1515361 := bbase (se 2 (by rfl) ⟨568260, by rfl⟩ : syracuseStep 1515361 = 1136521) (by norm_num)
theorem B2129773 : Blo 1260448 2129773 := bbase (se 3 (by rfl) ⟨399332, by rfl⟩ : syracuseStep 2129773 = 798665) (by norm_num)
theorem B1703797 : Blo 1260448 1703797 := bbase (se 5 (by rfl) ⟨79865, by rfl⟩ : syracuseStep 1703797 = 159731) (by norm_num)
theorem B1892213 : Blo 1260448 1892213 := bbase (se 5 (by rfl) ⟨88697, by rfl⟩ : syracuseStep 1892213 = 177395) (by norm_num)
theorem B3194741 : Blo 1260448 3194741 := bbase (se 5 (by rfl) ⟨149753, by rfl⟩ : syracuseStep 3194741 = 299507) (by norm_num)
theorem B1892237 : Blo 1260448 1892237 := bbase (se 3 (by rfl) ⟨354794, by rfl⟩ : syracuseStep 1892237 = 709589) (by norm_num)
theorem B2875285 : Blo 1260448 2875285 := bbase (se 6 (by rfl) ⟨67389, by rfl⟩ : syracuseStep 2875285 = 134779) (by norm_num)
theorem B1892261 : Blo 1260448 1892261 := bbase (se 4 (by rfl) ⟨177399, by rfl⟩ : syracuseStep 1892261 = 354799) (by norm_num)
theorem B1458109 : Blo 1260448 1458109 := bbase (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) (by norm_num)
theorem B1892285 : Blo 1260448 1892285 := bbase (se 3 (by rfl) ⟨354803, by rfl⟩ : syracuseStep 1892285 = 709607) (by norm_num)
theorem B2129861 : Blo 1260448 2129861 := bbase (se 4 (by rfl) ⟨199674, by rfl⟩ : syracuseStep 2129861 = 399349) (by norm_num)
theorem B1892309 : Blo 1260448 1892309 := bbase (se 7 (by rfl) ⟨22175, by rfl⟩ : syracuseStep 1892309 = 44351) (by norm_num)
theorem B1892333 : Blo 1260448 1892333 := bbase (se 3 (by rfl) ⟨354812, by rfl⟩ : syracuseStep 1892333 = 709625) (by norm_num)
theorem B1597421 : Blo 1260448 1597421 := bbase (se 3 (by rfl) ⟨299516, by rfl⟩ : syracuseStep 1597421 = 599033) (by norm_num)
theorem B1261571 : Blo 1260448 1261571 := bstep (se 1 (by rfl) ⟨946178, by rfl⟩ : syracuseStep 1261571 = 1892357) B1892357
theorem B4259843 : Blo 1260448 4259843 := bstep (se 1 (by rfl) ⟨3194882, by rfl⟩ : syracuseStep 4259843 = 6389765) B6389765
theorem B1892369 : Blo 1260448 1892369 := bstep (se 2 (by rfl) ⟨709638, by rfl⟩ : syracuseStep 1892369 = 1419277) B1419277
theorem B1261587 : Blo 1260448 1261587 := bstep (se 1 (by rfl) ⟨946190, by rfl⟩ : syracuseStep 1261587 = 1892381) B1892381
theorem B1892387 : Blo 1260448 1892387 := bstep (se 1 (by rfl) ⟨1419290, by rfl⟩ : syracuseStep 1892387 = 2838581) B2838581
theorem B1261603 : Blo 1260448 1261603 := bstep (se 1 (by rfl) ⟨946202, by rfl⟩ : syracuseStep 1261603 = 1892405) B1892405
theorem B4792355 : Blo 1260448 4792355 := bstep (se 1 (by rfl) ⟨3594266, by rfl⟩ : syracuseStep 4792355 = 7188533) B7188533
theorem B2129969 : Blo 1260448 2129969 := bstep (se 2 (by rfl) ⟨798738, by rfl⟩ : syracuseStep 2129969 = 1597477) B1597477
theorem B1261619 : Blo 1260448 1261619 := bstep (se 1 (by rfl) ⟨946214, by rfl⟩ : syracuseStep 1261619 = 1892429) B1892429
theorem B1892417 : Blo 1260448 1892417 := bstep (se 2 (by rfl) ⟨709656, by rfl⟩ : syracuseStep 1892417 = 1419313) B1419313
theorem B1261635 : Blo 1260448 1261635 := bstep (se 1 (by rfl) ⟨946226, by rfl⟩ : syracuseStep 1261635 = 1892453) B1892453
theorem B1892435 : Blo 1260448 1892435 := bstep (se 1 (by rfl) ⟨1419326, by rfl⟩ : syracuseStep 1892435 = 2838653) B2838653
theorem B1261651 : Blo 1260448 1261651 := bstep (se 1 (by rfl) ⟨946238, by rfl⟩ : syracuseStep 1261651 = 1892477) B1892477
theorem B8077411 : Blo 1260448 8077411 := bstep (se 1 (by rfl) ⟨6058058, by rfl⟩ : syracuseStep 8077411 = 12116117) B12116117
theorem B1261667 : Blo 1260448 1261667 := bstep (se 1 (by rfl) ⟨946250, by rfl⟩ : syracuseStep 1261667 = 1892501) B1892501
theorem B1892465 : Blo 1260448 1892465 := bstep (se 2 (by rfl) ⟨709674, by rfl⟩ : syracuseStep 1892465 = 1419349) B1419349
theorem B1278067 : Blo 1260448 1278067 := bstep (se 1 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 1278067 = 1917101) B1917101
theorem B1261683 : Blo 1260448 1261683 := bstep (se 1 (by rfl) ⟨946262, by rfl⟩ : syracuseStep 1261683 = 1892525) B1892525
theorem B1892483 : Blo 1260448 1892483 := bstep (se 1 (by rfl) ⟨1419362, by rfl⟩ : syracuseStep 1892483 = 2838725) B2838725
theorem B1261699 : Blo 1260448 1261699 := bstep (se 1 (by rfl) ⟨946274, by rfl⟩ : syracuseStep 1261699 = 1892549) B1892549
theorem B4038797 : Blo 1260448 4038797 := bstep (se 3 (by rfl) ⟨757274, by rfl⟩ : syracuseStep 4038797 = 1514549) B1514549
theorem B1261715 : Blo 1260448 1261715 := bstep (se 1 (by rfl) ⟨946286, by rfl⟩ : syracuseStep 1261715 = 1892573) B1892573
theorem B1892513 : Blo 1260448 1892513 := bstep (se 2 (by rfl) ⟨709692, by rfl⟩ : syracuseStep 1892513 = 1419385) B1419385
theorem B1261731 : Blo 1260448 1261731 := bstep (se 1 (by rfl) ⟨946298, by rfl⟩ : syracuseStep 1261731 = 1892597) B1892597
theorem B2130097 : Blo 1260448 2130097 := bstep (se 2 (by rfl) ⟨798786, by rfl⟩ : syracuseStep 2130097 = 1597573) B1597573
theorem B1892531 : Blo 1260448 1892531 := bstep (se 1 (by rfl) ⟨1419398, by rfl⟩ : syracuseStep 1892531 = 2838797) B2838797
theorem B1261747 : Blo 1260448 1261747 := bstep (se 1 (by rfl) ⟨946310, by rfl⟩ : syracuseStep 1261747 = 1892621) B1892621
theorem B1261763 : Blo 1260448 1261763 := bstep (se 1 (by rfl) ⟨946322, by rfl⟩ : syracuseStep 1261763 = 1892645) B1892645
theorem B1892561 : Blo 1260448 1892561 := bstep (se 2 (by rfl) ⟨709710, by rfl⟩ : syracuseStep 1892561 = 1419421) B1419421
theorem B1261779 : Blo 1260448 1261779 := bstep (se 1 (by rfl) ⟨946334, by rfl⟩ : syracuseStep 1261779 = 1892669) B1892669
theorem B2130131 : Blo 1260448 2130131 := bstep (se 1 (by rfl) ⟨1597598, by rfl⟩ : syracuseStep 2130131 = 3195197) B3195197
theorem B1892579 : Blo 1260448 1892579 := bstep (se 1 (by rfl) ⟨1419434, by rfl⟩ : syracuseStep 1892579 = 2838869) B2838869
theorem B1261795 : Blo 1260448 1261795 := bstep (se 1 (by rfl) ⟨946346, by rfl⟩ : syracuseStep 1261795 = 1892693) B1892693
theorem B1261811 : Blo 1260448 1261811 := bstep (se 1 (by rfl) ⟨946358, by rfl⟩ : syracuseStep 1261811 = 1892717) B1892717
theorem B1892609 : Blo 1260448 1892609 := bstep (se 2 (by rfl) ⟨709728, by rfl⟩ : syracuseStep 1892609 = 1419457) B1419457
theorem B1261827 : Blo 1260448 1261827 := bstep (se 1 (by rfl) ⟨946370, by rfl⟩ : syracuseStep 1261827 = 1892741) B1892741
theorem B2695427 : Blo 1260448 2695427 := bstep (se 1 (by rfl) ⟨2021570, by rfl⟩ : syracuseStep 2695427 = 4043141) B4043141
theorem B4260113 : Blo 1260448 4260113 := bstep (se 2 (by rfl) ⟨1597542, by rfl⟩ : syracuseStep 4260113 = 3195085) B3195085
theorem B1892627 : Blo 1260448 1892627 := bstep (se 1 (by rfl) ⟨1419470, by rfl⟩ : syracuseStep 1892627 = 2838941) B2838941
theorem B1261843 : Blo 1260448 1261843 := bstep (se 1 (by rfl) ⟨946382, by rfl⟩ : syracuseStep 1261843 = 1892765) B1892765
theorem B1261859 : Blo 1260448 1261859 := bstep (se 1 (by rfl) ⟨946394, by rfl⟩ : syracuseStep 1261859 = 1892789) B1892789
theorem B1892657 : Blo 1260448 1892657 := bstep (se 2 (by rfl) ⟨709746, by rfl⟩ : syracuseStep 1892657 = 1419493) B1419493
theorem B1261875 : Blo 1260448 1261875 := bstep (se 1 (by rfl) ⟨946406, by rfl⟩ : syracuseStep 1261875 = 1892813) B1892813
theorem B1892675 : Blo 1260448 1892675 := bstep (se 1 (by rfl) ⟨1419506, by rfl⟩ : syracuseStep 1892675 = 2839013) B2839013
theorem B1261891 : Blo 1260448 1261891 := bstep (se 1 (by rfl) ⟨946418, by rfl⟩ : syracuseStep 1261891 = 1892837) B1892837
theorem B1261907 : Blo 1260448 1261907 := bstep (se 1 (by rfl) ⟨946430, by rfl⟩ : syracuseStep 1261907 = 1892861) B1892861
theorem B2130259 : Blo 1260448 2130259 := bstep (se 1 (by rfl) ⟨1597694, by rfl⟩ : syracuseStep 2130259 = 3195389) B3195389
theorem B1892705 : Blo 1260448 1892705 := bstep (se 2 (by rfl) ⟨709764, by rfl⟩ : syracuseStep 1892705 = 1419529) B1419529
theorem B1261923 : Blo 1260448 1261923 := bstep (se 1 (by rfl) ⟨946442, by rfl⟩ : syracuseStep 1261923 = 1892885) B1892885
theorem B1892723 : Blo 1260448 1892723 := bstep (se 1 (by rfl) ⟨1419542, by rfl⟩ : syracuseStep 1892723 = 2839085) B2839085
theorem B1261939 : Blo 1260448 1261939 := bstep (se 1 (by rfl) ⟨946454, by rfl⟩ : syracuseStep 1261939 = 1892909) B1892909
theorem B1261955 : Blo 1260448 1261955 := bstep (se 1 (by rfl) ⟨946466, by rfl⟩ : syracuseStep 1261955 = 1892933) B1892933
theorem B1892753 : Blo 1260448 1892753 := bstep (se 2 (by rfl) ⟨709782, by rfl⟩ : syracuseStep 1892753 = 1419565) B1419565
theorem B1261971 : Blo 1260448 1261971 := bstep (se 1 (by rfl) ⟨946478, by rfl⟩ : syracuseStep 1261971 = 1892957) B1892957
theorem B1892771 : Blo 1260448 1892771 := bstep (se 1 (by rfl) ⟨1419578, by rfl⟩ : syracuseStep 1892771 = 2839157) B2839157
theorem B1261987 : Blo 1260448 1261987 := bstep (se 1 (by rfl) ⟨946490, by rfl⟩ : syracuseStep 1261987 = 1892981) B1892981
theorem B1262003 : Blo 1260448 1262003 := bstep (se 1 (by rfl) ⟨946502, by rfl⟩ : syracuseStep 1262003 = 1893005) B1893005
theorem B1892801 : Blo 1260448 1892801 := bstep (se 2 (by rfl) ⟨709800, by rfl⟩ : syracuseStep 1892801 = 1419601) B1419601
theorem B1262019 : Blo 1260448 1262019 := bstep (se 1 (by rfl) ⟨946514, by rfl⟩ : syracuseStep 1262019 = 1893029) B1893029
theorem B2048465 : Blo 1260448 2048465 := bstep (se 2 (by rfl) ⟨768174, by rfl⟩ : syracuseStep 2048465 = 1536349) B1536349
theorem B1892819 : Blo 1260448 1892819 := bstep (se 1 (by rfl) ⟨1419614, by rfl⟩ : syracuseStep 1892819 = 2839229) B2839229
theorem B1262035 : Blo 1260448 1262035 := bstep (se 1 (by rfl) ⟨946526, by rfl⟩ : syracuseStep 1262035 = 1893053) B1893053
theorem B3457507 : Blo 1260448 3457507 := bstep (se 1 (by rfl) ⟨2593130, by rfl⟩ : syracuseStep 3457507 = 5186261) B5186261
theorem B5390819 : Blo 1260448 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B1262051 : Blo 1260448 1262051 := bstep (se 1 (by rfl) ⟨946538, by rfl⟩ : syracuseStep 1262051 = 1893077) B1893077
theorem B1892849 : Blo 1260448 1892849 := bstep (se 2 (by rfl) ⟨709818, by rfl⟩ : syracuseStep 1892849 = 1419637) B1419637
theorem B1262067 : Blo 1260448 1262067 := bstep (se 1 (by rfl) ⟨946550, by rfl⟩ : syracuseStep 1262067 = 1893101) B1893101
theorem B1892867 : Blo 1260448 1892867 := bstep (se 1 (by rfl) ⟨1419650, by rfl⟩ : syracuseStep 1892867 = 2839301) B2839301
theorem B1262083 : Blo 1260448 1262083 := bstep (se 1 (by rfl) ⟨946562, by rfl⟩ : syracuseStep 1262083 = 1893125) B1893125
theorem B3195409 : Blo 1260448 3195409 := bstep (se 2 (by rfl) ⟨1198278, by rfl⟩ : syracuseStep 3195409 = 2396557) B2396557
theorem B1262099 : Blo 1260448 1262099 := bstep (se 1 (by rfl) ⟨946574, by rfl⟩ : syracuseStep 1262099 = 1893149) B1893149
theorem B1892897 : Blo 1260448 1892897 := bstep (se 2 (by rfl) ⟨709836, by rfl⟩ : syracuseStep 1892897 = 1419673) B1419673
theorem B4547107 : Blo 1260448 4547107 := bstep (se 1 (by rfl) ⟨3410330, by rfl⟩ : syracuseStep 4547107 = 6820661) B6820661
theorem B1262115 : Blo 1260448 1262115 := bstep (se 1 (by rfl) ⟨946586, by rfl⟩ : syracuseStep 1262115 = 1893173) B1893173
theorem B1892915 : Blo 1260448 1892915 := bstep (se 1 (by rfl) ⟨1419686, by rfl⟩ : syracuseStep 1892915 = 2839373) B2839373
theorem B1262131 : Blo 1260448 1262131 := bstep (se 1 (by rfl) ⟨946598, by rfl⟩ : syracuseStep 1262131 = 1893197) B1893197
theorem B1262147 : Blo 1260448 1262147 := bstep (se 1 (by rfl) ⟨946610, by rfl⟩ : syracuseStep 1262147 = 1893221) B1893221
theorem B1892945 : Blo 1260448 1892945 := bstep (se 2 (by rfl) ⟨709854, by rfl⟩ : syracuseStep 1892945 = 1419709) B1419709
theorem B1262163 : Blo 1260448 1262163 := bstep (se 1 (by rfl) ⟨946622, by rfl⟩ : syracuseStep 1262163 = 1893245) B1893245
theorem B1892963 : Blo 1260448 1892963 := bstep (se 1 (by rfl) ⟨1419722, by rfl⟩ : syracuseStep 1892963 = 2839445) B2839445
theorem B1262179 : Blo 1260448 1262179 := bstep (se 1 (by rfl) ⟨946634, by rfl⟩ : syracuseStep 1262179 = 1893269) B1893269
theorem B1794673 : Blo 1260448 1794673 := bstep (se 2 (by rfl) ⟨673002, by rfl⟩ : syracuseStep 1794673 = 1346005) B1346005
theorem B1262195 : Blo 1260448 1262195 := bstep (se 1 (by rfl) ⟨946646, by rfl⟩ : syracuseStep 1262195 = 1893293) B1893293
theorem B1892993 : Blo 1260448 1892993 := bstep (se 2 (by rfl) ⟨709872, by rfl⟩ : syracuseStep 1892993 = 1419745) B1419745
theorem B1262211 : Blo 1260448 1262211 := bstep (se 1 (by rfl) ⟨946658, by rfl⟩ : syracuseStep 1262211 = 1893317) B1893317
theorem B6390413 : Blo 1260448 6390413 := bstep (se 3 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 6390413 = 2396405) B2396405
theorem B1893011 : Blo 1260448 1893011 := bstep (se 1 (by rfl) ⟨1419758, by rfl⟩ : syracuseStep 1893011 = 2839517) B2839517
theorem B1262227 : Blo 1260448 1262227 := bstep (se 1 (by rfl) ⟨946670, by rfl⟩ : syracuseStep 1262227 = 1893341) B1893341
theorem B1262243 : Blo 1260448 1262243 := bstep (se 1 (by rfl) ⟨946682, by rfl⟩ : syracuseStep 1262243 = 1893365) B1893365
theorem B1893041 : Blo 1260448 1893041 := bstep (se 2 (by rfl) ⟨709890, by rfl⟩ : syracuseStep 1893041 = 1419781) B1419781
theorem B1262259 : Blo 1260448 1262259 := bstep (se 1 (by rfl) ⟨946694, by rfl⟩ : syracuseStep 1262259 = 1893389) B1893389
theorem B1893059 : Blo 1260448 1893059 := bstep (se 1 (by rfl) ⟨1419794, by rfl⟩ : syracuseStep 1893059 = 2839589) B2839589
theorem B1262275 : Blo 1260448 1262275 := bstep (se 1 (by rfl) ⟨946706, by rfl⟩ : syracuseStep 1262275 = 1893413) B1893413
theorem B1262291 : Blo 1260448 1262291 := bstep (se 1 (by rfl) ⟨946718, by rfl⟩ : syracuseStep 1262291 = 1893437) B1893437
theorem B1704673 : Blo 1260448 1704673 := bstep (se 2 (by rfl) ⟨639252, by rfl⟩ : syracuseStep 1704673 = 1278505) B1278505
theorem B1893089 : Blo 1260448 1893089 := bstep (se 2 (by rfl) ⟨709908, by rfl⟩ : syracuseStep 1893089 = 1419817) B1419817
theorem B1262307 : Blo 1260448 1262307 := bstep (se 1 (by rfl) ⟨946730, by rfl⟩ : syracuseStep 1262307 = 1893461) B1893461
theorem B1893107 : Blo 1260448 1893107 := bstep (se 1 (by rfl) ⟨1419830, by rfl⟩ : syracuseStep 1893107 = 2839661) B2839661
theorem B1262323 : Blo 1260448 1262323 := bstep (se 1 (by rfl) ⟨946742, by rfl⟩ : syracuseStep 1262323 = 1893485) B1893485
theorem B1262339 : Blo 1260448 1262339 := bstep (se 1 (by rfl) ⟨946754, by rfl⟩ : syracuseStep 1262339 = 1893509) B1893509
theorem B1893137 : Blo 1260448 1893137 := bstep (se 2 (by rfl) ⟨709926, by rfl⟩ : syracuseStep 1893137 = 1419853) B1419853
theorem B1262355 : Blo 1260448 1262355 := bstep (se 1 (by rfl) ⟨946766, by rfl⟩ : syracuseStep 1262355 = 1893533) B1893533
theorem B1893155 : Blo 1260448 1893155 := bstep (se 1 (by rfl) ⟨1419866, by rfl⟩ : syracuseStep 1893155 = 2839733) B2839733
theorem B1262371 : Blo 1260448 1262371 := bstep (se 1 (by rfl) ⟨946778, by rfl⟩ : syracuseStep 1262371 = 1893557) B1893557
theorem B4260653 : Blo 1260448 4260653 := bstep (se 3 (by rfl) ⟨798872, by rfl⟩ : syracuseStep 4260653 = 1597745) B1597745
theorem B1418035 : Blo 1260448 1418035 := bstep (se 1 (by rfl) ⟨1063526, by rfl⟩ : syracuseStep 1418035 = 2127053) B2127053
theorem B1262387 : Blo 1260448 1262387 := bstep (se 1 (by rfl) ⟨946790, by rfl⟩ : syracuseStep 1262387 = 1893581) B1893581
theorem B1893185 : Blo 1260448 1893185 := bstep (se 2 (by rfl) ⟨709944, by rfl⟩ : syracuseStep 1893185 = 1419889) B1419889
theorem B1262403 : Blo 1260448 1262403 := bstep (se 1 (by rfl) ⟨946802, by rfl⟩ : syracuseStep 1262403 = 1893605) B1893605
theorem B2696017 : Blo 1260448 2696017 := bstep (se 2 (by rfl) ⟨1011006, by rfl⟩ : syracuseStep 2696017 = 2022013) B2022013
theorem B1893203 : Blo 1260448 1893203 := bstep (se 1 (by rfl) ⟨1419902, by rfl⟩ : syracuseStep 1893203 = 2839805) B2839805
theorem B1262419 : Blo 1260448 1262419 := bstep (se 1 (by rfl) ⟨946814, by rfl⟩ : syracuseStep 1262419 = 1893629) B1893629
theorem B4260707 : Blo 1260448 4260707 := bstep (se 1 (by rfl) ⟨3195530, by rfl⟩ : syracuseStep 4260707 = 6391061) B6391061
theorem B1262435 : Blo 1260448 1262435 := bstep (se 1 (by rfl) ⟨946826, by rfl⟩ : syracuseStep 1262435 = 1893653) B1893653
theorem B1893233 : Blo 1260448 1893233 := bstep (se 2 (by rfl) ⟨709962, by rfl⟩ : syracuseStep 1893233 = 1419925) B1419925
theorem B1893251 : Blo 1260448 1893251 := bstep (se 1 (by rfl) ⟨1419938, by rfl⟩ : syracuseStep 1893251 = 2839877) B2839877
theorem B1893281 : Blo 1260448 1893281 := bstep (se 2 (by rfl) ⟨709980, by rfl⟩ : syracuseStep 1893281 = 1419961) B1419961
theorem B1893299 : Blo 1260448 1893299 := bstep (se 1 (by rfl) ⟨1419974, by rfl⟩ : syracuseStep 1893299 = 2839949) B2839949
theorem B1418179 : Blo 1260448 1418179 := bstep (se 1 (by rfl) ⟨1063634, by rfl⟩ : syracuseStep 1418179 = 2127269) B2127269
theorem B1893329 : Blo 1260448 1893329 := bstep (se 2 (by rfl) ⟨709998, by rfl⟩ : syracuseStep 1893329 = 1419997) B1419997
theorem B1893347 : Blo 1260448 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B1893377 : Blo 1260448 1893377 := bstep (se 2 (by rfl) ⟨710016, by rfl⟩ : syracuseStep 1893377 = 1420033) B1420033
theorem B16172045 : Blo 1260448 16172045 := bstep (se 3 (by rfl) ⟨3032258, by rfl⟩ : syracuseStep 16172045 = 6064517) B6064517
theorem B4793357 : Blo 1260448 4793357 := bstep (se 3 (by rfl) ⟨898754, by rfl⟩ : syracuseStep 4793357 = 1797509) B1797509
theorem B1893395 : Blo 1260448 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B1893425 : Blo 1260448 1893425 := bstep (se 2 (by rfl) ⟨710034, by rfl⟩ : syracuseStep 1893425 = 1420069) B1420069
theorem B2393155 : Blo 1260448 2393155 := bstep (se 1 (by rfl) ⟨1794866, by rfl⟩ : syracuseStep 2393155 = 3589733) B3589733
theorem B1893443 : Blo 1260448 1893443 := bstep (se 1 (by rfl) ⟨1420082, by rfl⟩ : syracuseStep 1893443 = 2840165) B2840165
theorem B8078413 : Blo 1260448 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B1418323 : Blo 1260448 1418323 := bstep (se 1 (by rfl) ⟨1063742, by rfl⟩ : syracuseStep 1418323 = 2127485) B2127485
theorem B1893473 : Blo 1260448 1893473 := bstep (se 2 (by rfl) ⟨710052, by rfl⟩ : syracuseStep 1893473 = 1420105) B1420105
theorem B2393201 : Blo 1260448 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B46040177 : Blo 1260448 46040177 := bstep (se 2 (by rfl) ⟨17265066, by rfl⟩ : syracuseStep 46040177 = 34530133) B34530133
theorem B1893491 : Blo 1260448 1893491 := bstep (se 1 (by rfl) ⟨1420118, by rfl⟩ : syracuseStep 1893491 = 2840237) B2840237
theorem B1893521 : Blo 1260448 1893521 := bstep (se 2 (by rfl) ⟨710070, by rfl⟩ : syracuseStep 1893521 = 1420141) B1420141
theorem B1893539 : Blo 1260448 1893539 := bstep (se 1 (by rfl) ⟨1420154, by rfl⟩ : syracuseStep 1893539 = 2840309) B2840309
theorem B1893569 : Blo 1260448 1893569 := bstep (se 2 (by rfl) ⟨710088, by rfl⟩ : syracuseStep 1893569 = 1420177) B1420177
theorem B4039885 : Blo 1260448 4039885 := bstep (se 3 (by rfl) ⟨757478, by rfl⟩ : syracuseStep 4039885 = 1514957) B1514957
theorem B1893587 : Blo 1260448 1893587 := bstep (se 1 (by rfl) ⟨1420190, by rfl⟩ : syracuseStep 1893587 = 2840381) B2840381
theorem B1418467 : Blo 1260448 1418467 := bstep (se 1 (by rfl) ⟨1063850, by rfl⟩ : syracuseStep 1418467 = 2127701) B2127701
theorem B1893617 : Blo 1260448 1893617 := bstep (se 2 (by rfl) ⟨710106, by rfl⟩ : syracuseStep 1893617 = 1420213) B1420213
theorem B1893635 : Blo 1260448 1893635 := bstep (se 1 (by rfl) ⟨1420226, by rfl⟩ : syracuseStep 1893635 = 2840453) B2840453
theorem B29541653 : Blo 1260448 29541653 := bstep (se 6 (by rfl) ⟨692382, by rfl⟩ : syracuseStep 29541653 = 1384765) B1384765
theorem B1893665 : Blo 1260448 1893665 := bstep (se 2 (by rfl) ⟨710124, by rfl⟩ : syracuseStep 1893665 = 1420249) B1420249
theorem B1279283 : Blo 1260448 1279283 := bstep (se 1 (by rfl) ⟨959462, by rfl⟩ : syracuseStep 1279283 = 1918925) B1918925
theorem B12117347 : Blo 1260448 12117347 := bstep (se 1 (by rfl) ⟨9088010, by rfl⟩ : syracuseStep 12117347 = 18176021) B18176021
theorem B6382961 : Blo 1260448 6382961 := bstep (se 2 (by rfl) ⟨2393610, by rfl⟩ : syracuseStep 6382961 = 4787221) B4787221
theorem B1418611 : Blo 1260448 1418611 := bstep (se 1 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 1418611 = 2127917) B2127917
theorem B1795459 : Blo 1260448 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B2393489 : Blo 1260448 2393489 := bstep (se 2 (by rfl) ⟨897558, by rfl⟩ : syracuseStep 2393489 = 1795117) B1795117
theorem B1418755 : Blo 1260448 1418755 := bstep (se 1 (by rfl) ⟨1064066, by rfl⟩ : syracuseStep 1418755 = 2128133) B2128133
theorem B4318733 : Blo 1260448 4318733 := bstep (se 3 (by rfl) ⟨809762, by rfl⟩ : syracuseStep 4318733 = 1619525) B1619525
theorem B1820209 : Blo 1260448 1820209 := bstep (se 2 (by rfl) ⟨682578, by rfl⟩ : syracuseStep 1820209 = 1365157) B1365157
theorem B20473397 : Blo 1260448 20473397 := bstep (se 5 (by rfl) ⟨959690, by rfl⟩ : syracuseStep 20473397 = 1919381) B1919381
theorem B16156259 : Blo 1260448 16156259 := bstep (se 1 (by rfl) ⟨12117194, by rfl⟩ : syracuseStep 16156259 = 24234389) B24234389
theorem B1705603 : Blo 1260448 1705603 := bstep (se 1 (by rfl) ⟨1279202, by rfl⟩ : syracuseStep 1705603 = 2558405) B2558405
theorem B1418899 : Blo 1260448 1418899 := bstep (se 1 (by rfl) ⟨1064174, by rfl⟩ : syracuseStep 1418899 = 2128349) B2128349
theorem B1943233 : Blo 1260448 1943233 := bstep (se 2 (by rfl) ⟨728712, by rfl⟩ : syracuseStep 1943233 = 1457425) B1457425
theorem B1918657 : Blo 1260448 1918657 := bstep (se 2 (by rfl) ⟨719496, by rfl⟩ : syracuseStep 1918657 = 1438993) B1438993
theorem B7186117 : Blo 1260448 7186117 := bstep (se 4 (by rfl) ⟨673698, by rfl⟩ : syracuseStep 7186117 = 1347397) B1347397
theorem B3589859 : Blo 1260448 3589859 := bstep (se 1 (by rfl) ⟨2692394, by rfl⟩ : syracuseStep 3589859 = 5384789) B5384789
theorem B17966819 : Blo 1260448 17966819 := bstep (se 1 (by rfl) ⟨13475114, by rfl⟩ : syracuseStep 17966819 = 26950229) B26950229
theorem B2836241 : Blo 1260448 2836241 := bstep (se 2 (by rfl) ⟨1063590, by rfl⟩ : syracuseStep 2836241 = 2127181) B2127181
theorem B2836259 : Blo 1260448 2836259 := bstep (se 1 (by rfl) ⟨2127194, by rfl⟩ : syracuseStep 2836259 = 4254389) B4254389
theorem B1419043 : Blo 1260448 1419043 := bstep (se 1 (by rfl) ⟨1064282, by rfl⟩ : syracuseStep 1419043 = 2128565) B2128565
theorem B1795937 : Blo 1260448 1795937 := bstep (se 2 (by rfl) ⟨673476, by rfl⟩ : syracuseStep 1795937 = 1346953) B1346953
theorem B1296227 : Blo 1260448 1296227 := bstep (se 1 (by rfl) ⟨972170, by rfl⟩ : syracuseStep 1296227 = 1944341) B1944341
theorem B2426755 : Blo 1260448 2426755 := bstep (se 1 (by rfl) ⟨1820066, by rfl⟩ : syracuseStep 2426755 = 3640133) B3640133
theorem B9848717 : Blo 1260448 9848717 := bstep (se 3 (by rfl) ⟨1846634, by rfl⟩ : syracuseStep 9848717 = 3693269) B3693269
theorem B2877329 : Blo 1260448 2877329 := bstep (se 2 (by rfl) ⟨1078998, by rfl⟩ : syracuseStep 2877329 = 2157997) B2157997
theorem B1419187 : Blo 1260448 1419187 := bstep (se 1 (by rfl) ⟨1064390, by rfl⟩ : syracuseStep 1419187 = 2128781) B2128781
theorem B9086917 : Blo 1260448 9086917 := bstep (se 4 (by rfl) ⟨851898, by rfl⟩ : syracuseStep 9086917 = 1703797) B1703797
theorem B1796051 : Blo 1260448 1796051 := bstep (se 1 (by rfl) ⟨1347038, by rfl⟩ : syracuseStep 1796051 = 2694077) B2694077
theorem B1796131 : Blo 1260448 1796131 := bstep (se 1 (by rfl) ⟨1347098, by rfl⟩ : syracuseStep 1796131 = 2694197) B2694197
theorem B3590189 : Blo 1260448 3590189 := bstep (se 3 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 3590189 = 1346321) B1346321
theorem B2836529 : Blo 1260448 2836529 := bstep (se 2 (by rfl) ⟨1063698, by rfl⟩ : syracuseStep 2836529 = 2127397) B2127397
theorem B1943603 : Blo 1260448 1943603 := bstep (se 1 (by rfl) ⟨1457702, by rfl⟩ : syracuseStep 1943603 = 2915405) B2915405
theorem B2836547 : Blo 1260448 2836547 := bstep (se 1 (by rfl) ⟨2127410, by rfl⟩ : syracuseStep 2836547 = 4254821) B4254821
theorem B1419331 : Blo 1260448 1419331 := bstep (se 1 (by rfl) ⟨1064498, by rfl⟩ : syracuseStep 1419331 = 2128997) B2128997
theorem B2394211 : Blo 1260448 2394211 := bstep (se 1 (by rfl) ⟨1795658, by rfl⟩ : syracuseStep 2394211 = 3591317) B3591317
theorem B3590257 : Blo 1260448 3590257 := bstep (se 2 (by rfl) ⟨1346346, by rfl⟩ : syracuseStep 3590257 = 2692693) B2692693
theorem B3033251 : Blo 1260448 3033251 := bstep (se 1 (by rfl) ⟨2274938, by rfl⟩ : syracuseStep 3033251 = 4549877) B4549877
theorem B1419475 : Blo 1260448 1419475 := bstep (se 1 (by rfl) ⟨1064606, by rfl⟩ : syracuseStep 1419475 = 2129213) B2129213
theorem B2836817 : Blo 1260448 2836817 := bstep (se 2 (by rfl) ⟨1063806, by rfl⟩ : syracuseStep 2836817 = 2127613) B2127613
theorem B2836835 : Blo 1260448 2836835 := bstep (se 1 (by rfl) ⟨2127626, by rfl⟩ : syracuseStep 2836835 = 4255253) B4255253
theorem B1419619 : Blo 1260448 1419619 := bstep (se 1 (by rfl) ⟨1064714, by rfl⟩ : syracuseStep 1419619 = 2129429) B2129429
theorem B4254065 : Blo 1260448 4254065 := bstep (se 2 (by rfl) ⟨1595274, by rfl⟩ : syracuseStep 4254065 = 3190549) B3190549
theorem B8087921 : Blo 1260448 8087921 := bstep (se 2 (by rfl) ⟨3032970, by rfl⟩ : syracuseStep 8087921 = 6065941) B6065941
theorem B3590531 : Blo 1260448 3590531 := bstep (se 1 (by rfl) ⟨2692898, by rfl⟩ : syracuseStep 3590531 = 5385797) B5385797
theorem B8087971 : Blo 1260448 8087971 := bstep (se 1 (by rfl) ⟨6065978, by rfl⟩ : syracuseStep 8087971 = 12131957) B12131957
theorem B2877905 : Blo 1260448 2877905 := bstep (se 2 (by rfl) ⟨1079214, by rfl⟩ : syracuseStep 2877905 = 2158429) B2158429
theorem B1419763 : Blo 1260448 1419763 := bstep (se 1 (by rfl) ⟨1064822, by rfl⟩ : syracuseStep 1419763 = 2129645) B2129645
theorem B2394659 : Blo 1260448 2394659 := bstep (se 1 (by rfl) ⟨1795994, by rfl⟩ : syracuseStep 2394659 = 3591989) B3591989
theorem B1944145 : Blo 1260448 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B3410513 : Blo 1260448 3410513 := bstep (se 2 (by rfl) ⟨1278942, by rfl⟩ : syracuseStep 3410513 = 2557885) B2557885
theorem B1796689 : Blo 1260448 1796689 := bstep (se 2 (by rfl) ⟨673758, by rfl⟩ : syracuseStep 1796689 = 1347517) B1347517
theorem B2837105 : Blo 1260448 2837105 := bstep (se 2 (by rfl) ⟨1063914, by rfl⟩ : syracuseStep 2837105 = 2127829) B2127829
theorem B2837123 : Blo 1260448 2837123 := bstep (se 1 (by rfl) ⟨2127842, by rfl⟩ : syracuseStep 2837123 = 4255685) B4255685
theorem B1419907 : Blo 1260448 1419907 := bstep (se 1 (by rfl) ⟨1064930, by rfl⟩ : syracuseStep 1419907 = 2129861) B2129861
theorem B1821361 : Blo 1260448 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1420051 : Blo 1260448 1420051 := bstep (se 1 (by rfl) ⟨1065038, by rfl⟩ : syracuseStep 1420051 = 2130077) B2130077
theorem B6384419 : Blo 1260448 6384419 := bstep (se 1 (by rfl) ⟨4788314, by rfl⟩ : syracuseStep 6384419 = 9576629) B9576629
theorem B2394947 : Blo 1260448 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B1870691 : Blo 1260448 1870691 := bstep (se 1 (by rfl) ⟨1403018, by rfl⟩ : syracuseStep 1870691 = 2806037) B2806037
theorem B4254605 : Blo 1260448 4254605 := bstep (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) B1595477
theorem B2837393 : Blo 1260448 2837393 := bstep (se 2 (by rfl) ⟨1064022, by rfl⟩ : syracuseStep 2837393 = 2128045) B2128045
theorem B2837411 : Blo 1260448 2837411 := bstep (se 1 (by rfl) ⟨2128058, by rfl⟩ : syracuseStep 2837411 = 4256117) B4256117
theorem B1420195 : Blo 1260448 1420195 := bstep (se 1 (by rfl) ⟨1065146, by rfl⟩ : syracuseStep 1420195 = 2130293) B2130293
theorem B4254659 : Blo 1260448 4254659 := bstep (se 1 (by rfl) ⟨3190994, by rfl⟩ : syracuseStep 4254659 = 6381989) B6381989
theorem B4041667 : Blo 1260448 4041667 := bstep (se 1 (by rfl) ⟨3031250, by rfl⟩ : syracuseStep 4041667 = 6062501) B6062501
theorem B4041731 : Blo 1260448 4041731 := bstep (se 1 (by rfl) ⟨3031298, by rfl⟩ : syracuseStep 4041731 = 6062597) B6062597
theorem B4041809 : Blo 1260448 4041809 := bstep (se 2 (by rfl) ⟨1515678, by rfl⟩ : syracuseStep 4041809 = 3031357) B3031357
theorem B8629361 : Blo 1260448 8629361 := bstep (se 2 (by rfl) ⟨3236010, by rfl⟩ : syracuseStep 8629361 = 6472021) B6472021
theorem B2837681 : Blo 1260448 2837681 := bstep (se 2 (by rfl) ⟨1064130, by rfl⟩ : syracuseStep 2837681 = 2128261) B2128261
theorem B2837699 : Blo 1260448 2837699 := bstep (se 1 (by rfl) ⟨2128274, by rfl⟩ : syracuseStep 2837699 = 4256549) B4256549
theorem B3591373 : Blo 1260448 3591373 := bstep (se 3 (by rfl) ⟨673382, by rfl⟩ : syracuseStep 3591373 = 1346765) B1346765
theorem B4254929 : Blo 1260448 4254929 := bstep (se 2 (by rfl) ⟨1595598, by rfl⟩ : syracuseStep 4254929 = 3191197) B3191197
theorem B1797395 : Blo 1260448 1797395 := bstep (se 1 (by rfl) ⟨1348046, by rfl⟩ : syracuseStep 1797395 = 2696093) B2696093
theorem B1346915 : Blo 1260448 1346915 := bstep (se 1 (by rfl) ⟨1010186, by rfl⟩ : syracuseStep 1346915 = 2020373) B2020373
theorem B3591533 : Blo 1260448 3591533 := bstep (se 3 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 3591533 = 1346825) B1346825
theorem B2837969 : Blo 1260448 2837969 := bstep (se 2 (by rfl) ⟨1064238, by rfl⟩ : syracuseStep 2837969 = 2128477) B2128477
theorem B2837987 : Blo 1260448 2837987 := bstep (se 1 (by rfl) ⟨2128490, by rfl⟩ : syracuseStep 2837987 = 4256981) B4256981
theorem B3591715 : Blo 1260448 3591715 := bstep (se 1 (by rfl) ⟨2693786, by rfl⟩ : syracuseStep 3591715 = 5387573) B5387573
theorem B6385229 : Blo 1260448 6385229 := bstep (se 3 (by rfl) ⟨1197230, by rfl⟩ : syracuseStep 6385229 = 2394461) B2394461
theorem B2158211 : Blo 1260448 2158211 := bstep (se 1 (by rfl) ⟨1618658, by rfl⟩ : syracuseStep 2158211 = 3237317) B3237317
theorem B7188101 : Blo 1260448 7188101 := bstep (se 4 (by rfl) ⟨673884, by rfl⟩ : syracuseStep 7188101 = 1347769) B1347769
theorem B4255469 : Blo 1260448 4255469 := bstep (se 3 (by rfl) ⟨797900, by rfl⟩ : syracuseStep 4255469 = 1595801) B1595801
theorem B2838257 : Blo 1260448 2838257 := bstep (se 2 (by rfl) ⟨1064346, by rfl⟩ : syracuseStep 2838257 = 2128693) B2128693
theorem B2395889 : Blo 1260448 2395889 := bstep (se 2 (by rfl) ⟨898458, by rfl⟩ : syracuseStep 2395889 = 1796917) B1796917
theorem B2838275 : Blo 1260448 2838275 := bstep (se 1 (by rfl) ⟨2128706, by rfl⟩ : syracuseStep 2838275 = 4257413) B4257413
theorem B3411715 : Blo 1260448 3411715 := bstep (se 1 (by rfl) ⟨2558786, by rfl⟩ : syracuseStep 3411715 = 5117573) B5117573
theorem B4787981 : Blo 1260448 4787981 := bstep (se 3 (by rfl) ⟨897746, by rfl⟩ : syracuseStep 4787981 = 1795493) B1795493
theorem B4255523 : Blo 1260448 4255523 := bstep (se 1 (by rfl) ⟨3191642, by rfl⟩ : syracuseStep 4255523 = 6383285) B6383285
theorem B10768241 : Blo 1260448 10768241 := bstep (se 2 (by rfl) ⟨4038090, by rfl⟩ : syracuseStep 10768241 = 8076181) B8076181
theorem B3190691 : Blo 1260448 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B2019251 : Blo 1260448 2019251 := bstep (se 1 (by rfl) ⟨1514438, by rfl⟩ : syracuseStep 2019251 = 3028877) B3028877
theorem B7671757 : Blo 1260448 7671757 := bstep (se 3 (by rfl) ⟨1438454, by rfl⟩ : syracuseStep 7671757 = 2876909) B2876909
theorem B6230029 : Blo 1260448 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B2838545 : Blo 1260448 2838545 := bstep (se 2 (by rfl) ⟨1064454, by rfl⟩ : syracuseStep 2838545 = 2128909) B2128909
theorem B2838563 : Blo 1260448 2838563 := bstep (se 1 (by rfl) ⟨2128922, by rfl⟩ : syracuseStep 2838563 = 4257845) B4257845
theorem B2592803 : Blo 1260448 2592803 := bstep (se 1 (by rfl) ⟨1944602, by rfl⟩ : syracuseStep 2592803 = 3889205) B3889205
theorem B4255793 : Blo 1260448 4255793 := bstep (se 2 (by rfl) ⟨1595922, by rfl⟩ : syracuseStep 4255793 = 3191845) B3191845
theorem B14372963 : Blo 1260448 14372963 := bstep (se 1 (by rfl) ⟨10779722, by rfl⟩ : syracuseStep 14372963 = 21559445) B21559445
theorem B9089165 : Blo 1260448 9089165 := bstep (se 3 (by rfl) ⟨1704218, by rfl⟩ : syracuseStep 9089165 = 3408437) B3408437
theorem B1618067 : Blo 1260448 1618067 := bstep (se 1 (by rfl) ⟨1213550, by rfl⟩ : syracuseStep 1618067 = 2427101) B2427101
theorem B5386445 : Blo 1260448 5386445 := bstep (se 3 (by rfl) ⟨1009958, by rfl⟩ : syracuseStep 5386445 = 2019917) B2019917
theorem B6058253 : Blo 1260448 6058253 := bstep (se 3 (by rfl) ⟨1135922, by rfl⟩ : syracuseStep 6058253 = 2271845) B2271845
theorem B1437971 : Blo 1260448 1437971 := bstep (se 1 (by rfl) ⟨1078478, by rfl⟩ : syracuseStep 1437971 = 2156957) B2156957
theorem B6820145 : Blo 1260448 6820145 := bstep (se 2 (by rfl) ⟨2557554, by rfl⟩ : syracuseStep 6820145 = 5115109) B5115109
theorem B2838833 : Blo 1260448 2838833 := bstep (se 2 (by rfl) ⟨1064562, by rfl⟩ : syracuseStep 2838833 = 2129125) B2129125
theorem B2838851 : Blo 1260448 2838851 := bstep (se 1 (by rfl) ⟨2129138, by rfl⟩ : syracuseStep 2838851 = 4258277) B4258277
theorem B2019763 : Blo 1260448 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B27275717 : Blo 1260448 27275717 := bstep (se 4 (by rfl) ⟨2557098, by rfl⟩ : syracuseStep 27275717 = 5114197) B5114197
theorem B2019809 : Blo 1260448 2019809 := bstep (se 2 (by rfl) ⟨757428, by rfl⟩ : syracuseStep 2019809 = 1514857) B1514857
theorem B5386787 : Blo 1260448 5386787 := bstep (se 1 (by rfl) ⟨4040090, by rfl⟩ : syracuseStep 5386787 = 8080181) B8080181
theorem B5460529 : Blo 1260448 5460529 := bstep (se 2 (by rfl) ⟨2047698, by rfl⟩ : syracuseStep 5460529 = 4095397) B4095397
theorem B4256333 : Blo 1260448 4256333 := bstep (se 3 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 4256333 = 1596125) B1596125
theorem B2839121 : Blo 1260448 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B2839139 : Blo 1260448 2839139 := bstep (se 1 (by rfl) ⟨2129354, by rfl⟩ : syracuseStep 2839139 = 4258709) B4258709
theorem B4256387 : Blo 1260448 4256387 := bstep (se 1 (by rfl) ⟨3192290, by rfl⟩ : syracuseStep 4256387 = 6384581) B6384581
theorem B7672589 : Blo 1260448 7672589 := bstep (se 3 (by rfl) ⟨1438610, by rfl⟩ : syracuseStep 7672589 = 2877221) B2877221
theorem B3191633 : Blo 1260448 3191633 := bstep (se 2 (by rfl) ⟨1196862, by rfl⟩ : syracuseStep 3191633 = 2393725) B2393725
theorem B3642221 : Blo 1260448 3642221 := bstep (se 3 (by rfl) ⟨682916, by rfl⟩ : syracuseStep 3642221 = 1365833) B1365833
theorem B2839409 : Blo 1260448 2839409 := bstep (se 2 (by rfl) ⟨1064778, by rfl⟩ : syracuseStep 2839409 = 2129557) B2129557
theorem B3191683 : Blo 1260448 3191683 := bstep (se 1 (by rfl) ⟨2393762, by rfl⟩ : syracuseStep 3191683 = 4787525) B4787525
theorem B2839427 : Blo 1260448 2839427 := bstep (se 1 (by rfl) ⟨2129570, by rfl⟩ : syracuseStep 2839427 = 4259141) B4259141
theorem B22999949 : Blo 1260448 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B4256657 : Blo 1260448 4256657 := bstep (se 2 (by rfl) ⟨1596246, by rfl⟩ : syracuseStep 4256657 = 3192493) B3192493
theorem B3593105 : Blo 1260448 3593105 := bstep (se 2 (by rfl) ⟨1347414, by rfl⟩ : syracuseStep 3593105 = 2694829) B2694829
theorem B4043729 : Blo 1260448 4043729 := bstep (se 2 (by rfl) ⟨1516398, by rfl⟩ : syracuseStep 4043729 = 3032797) B3032797
theorem B5387249 : Blo 1260448 5387249 := bstep (se 2 (by rfl) ⟨2020218, by rfl⟩ : syracuseStep 5387249 = 4040437) B4040437
theorem B3191825 : Blo 1260448 3191825 := bstep (se 2 (by rfl) ⟨1196934, by rfl⟩ : syracuseStep 3191825 = 2393869) B2393869
theorem B2692163 : Blo 1260448 2692163 := bstep (se 1 (by rfl) ⟨2019122, by rfl⟩ : syracuseStep 2692163 = 4038245) B4038245
theorem B2020481 : Blo 1260448 2020481 := bstep (se 2 (by rfl) ⟨757680, by rfl⟩ : syracuseStep 2020481 = 1515361) B1515361
theorem B3740813 : Blo 1260448 3740813 := bstep (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) B1402805
theorem B2839697 : Blo 1260448 2839697 := bstep (se 2 (by rfl) ⟨1064886, by rfl⟩ : syracuseStep 2839697 = 2129773) B2129773
theorem B2839715 : Blo 1260448 2839715 := bstep (se 1 (by rfl) ⟨2129786, by rfl⟩ : syracuseStep 2839715 = 4259573) B4259573
theorem B2127073 : Blo 1260448 2127073 := bstep (se 2 (by rfl) ⟨797652, by rfl⟩ : syracuseStep 2127073 = 1595305) B1595305
theorem B61412579 : Blo 1260448 61412579 := bstep (se 1 (by rfl) ⟨46059434, by rfl⟩ : syracuseStep 61412579 = 92118869) B92118869
theorem B11515121 : Blo 1260448 11515121 := bstep (se 2 (by rfl) ⟨4318170, by rfl⟩ : syracuseStep 11515121 = 8636341) B8636341
theorem B2127107 : Blo 1260448 2127107 := bstep (se 1 (by rfl) ⟨1595330, by rfl⟩ : syracuseStep 2127107 = 3190661) B3190661
theorem B2127235 : Blo 1260448 2127235 := bstep (se 1 (by rfl) ⟨1595426, by rfl⟩ : syracuseStep 2127235 = 3190853) B3190853
theorem B4257197 : Blo 1260448 4257197 := bstep (se 3 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 4257197 = 1596449) B1596449
theorem B2839985 : Blo 1260448 2839985 := bstep (se 2 (by rfl) ⟨1064994, by rfl⟩ : syracuseStep 2839985 = 2129989) B2129989
theorem B2840003 : Blo 1260448 2840003 := bstep (se 1 (by rfl) ⟨2130002, by rfl⟩ : syracuseStep 2840003 = 4260005) B4260005
theorem B6911459 : Blo 1260448 6911459 := bstep (se 1 (by rfl) ⟨5183594, by rfl⟩ : syracuseStep 6911459 = 10367189) B10367189
theorem B4257251 : Blo 1260448 4257251 := bstep (se 1 (by rfl) ⟨3192938, by rfl⟩ : syracuseStep 4257251 = 6385877) B6385877
theorem B4044269 : Blo 1260448 4044269 := bstep (se 3 (by rfl) ⟨758300, by rfl⟩ : syracuseStep 4044269 = 1516601) B1516601
theorem B2127377 : Blo 1260448 2127377 := bstep (se 2 (by rfl) ⟨797766, by rfl⟩ : syracuseStep 2127377 = 1595533) B1595533
theorem B1439267 : Blo 1260448 1439267 := bstep (se 1 (by rfl) ⟨1079450, by rfl⟩ : syracuseStep 1439267 = 2158901) B2158901
theorem B2020993 : Blo 1260448 2020993 := bstep (se 2 (by rfl) ⟨757872, by rfl⟩ : syracuseStep 2020993 = 1515745) B1515745
theorem B2127505 : Blo 1260448 2127505 := bstep (se 2 (by rfl) ⟨797814, by rfl⟩ : syracuseStep 2127505 = 1595629) B1595629
theorem B2127539 : Blo 1260448 2127539 := bstep (se 1 (by rfl) ⟨1595654, by rfl⟩ : syracuseStep 2127539 = 3191309) B3191309
theorem B2840273 : Blo 1260448 2840273 := bstep (se 2 (by rfl) ⟨1065102, by rfl⟩ : syracuseStep 2840273 = 2130205) B2130205
theorem B2840291 : Blo 1260448 2840291 := bstep (se 1 (by rfl) ⟨2130218, by rfl⟩ : syracuseStep 2840291 = 4260437) B4260437
theorem B4257521 : Blo 1260448 4257521 := bstep (se 2 (by rfl) ⟨1596570, by rfl⟩ : syracuseStep 4257521 = 3193141) B3193141
theorem B38811413 : Blo 1260448 38811413 := bstep (se 6 (by rfl) ⟨909642, by rfl⟩ : syracuseStep 38811413 = 1819285) B1819285
theorem B2127667 : Blo 1260448 2127667 := bstep (se 1 (by rfl) ⟨1595750, by rfl⟩ : syracuseStep 2127667 = 3191501) B3191501
theorem B3594061 : Blo 1260448 3594061 := bstep (se 3 (by rfl) ⟨673886, by rfl⟩ : syracuseStep 3594061 = 1347773) B1347773
theorem B119740301 : Blo 1260448 119740301 := bstep (se 3 (by rfl) ⟨22451306, by rfl⟩ : syracuseStep 119740301 = 44902613) B44902613
theorem B1595315 : Blo 1260448 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B2127809 : Blo 1260448 2127809 := bstep (se 2 (by rfl) ⟨797928, by rfl⟩ : syracuseStep 2127809 = 1595857) B1595857
theorem B3192817 : Blo 1260448 3192817 := bstep (se 2 (by rfl) ⟨1197306, by rfl⟩ : syracuseStep 3192817 = 2394613) B2394613
theorem B3594289 : Blo 1260448 3594289 := bstep (se 2 (by rfl) ⟨1347858, by rfl⟩ : syracuseStep 3594289 = 2695717) B2695717
theorem B2127937 : Blo 1260448 2127937 := bstep (se 2 (by rfl) ⟨797976, by rfl⟩ : syracuseStep 2127937 = 1595953) B1595953
theorem B2127971 : Blo 1260448 2127971 := bstep (se 1 (by rfl) ⟨1595978, by rfl⟩ : syracuseStep 2127971 = 3191957) B3191957
theorem B3594449 : Blo 1260448 3594449 := bstep (se 2 (by rfl) ⟨1347918, by rfl⟩ : syracuseStep 3594449 = 2695837) B2695837
theorem B2128099 : Blo 1260448 2128099 := bstep (se 1 (by rfl) ⟨1596074, by rfl⟩ : syracuseStep 2128099 = 3192149) B3192149
theorem B3193091 : Blo 1260448 3193091 := bstep (se 1 (by rfl) ⟨2394818, by rfl⟩ : syracuseStep 3193091 = 4789637) B4789637
theorem B4258061 : Blo 1260448 4258061 := bstep (se 3 (by rfl) ⟨798386, by rfl⟩ : syracuseStep 4258061 = 1596773) B1596773
theorem B4258115 : Blo 1260448 4258115 := bstep (se 1 (by rfl) ⟨3193586, by rfl⟩ : syracuseStep 4258115 = 6387173) B6387173
theorem B3594563 : Blo 1260448 3594563 := bstep (se 1 (by rfl) ⟨2695922, by rfl⟩ : syracuseStep 3594563 = 5391845) B5391845
theorem B3029329 : Blo 1260448 3029329 := bstep (se 2 (by rfl) ⟨1135998, by rfl⟩ : syracuseStep 3029329 = 2271997) B2271997
theorem B9582947 : Blo 1260448 9582947 := bstep (se 1 (by rfl) ⟨7187210, by rfl⟩ : syracuseStep 9582947 = 14374421) B14374421
theorem B2128241 : Blo 1260448 2128241 := bstep (se 2 (by rfl) ⟨798090, by rfl⟩ : syracuseStep 2128241 = 1596181) B1596181
theorem B1890689 : Blo 1260448 1890689 := bstep (se 2 (by rfl) ⟨709008, by rfl⟩ : syracuseStep 1890689 = 1418017) B1418017
theorem B1890707 : Blo 1260448 1890707 := bstep (se 1 (by rfl) ⟨1418030, by rfl⟩ : syracuseStep 1890707 = 2836061) B2836061
theorem B1890737 : Blo 1260448 1890737 := bstep (se 2 (by rfl) ⟨709026, by rfl⟩ : syracuseStep 1890737 = 1418053) B1418053
theorem B6388145 : Blo 1260448 6388145 := bstep (se 2 (by rfl) ⟨2395554, by rfl⟩ : syracuseStep 6388145 = 4791109) B4791109
theorem B1890755 : Blo 1260448 1890755 := bstep (se 1 (by rfl) ⟨1418066, by rfl⟩ : syracuseStep 1890755 = 2836133) B2836133
theorem B3193283 : Blo 1260448 3193283 := bstep (se 1 (by rfl) ⟨2394962, by rfl⟩ : syracuseStep 3193283 = 4789925) B4789925
theorem B1890785 : Blo 1260448 1890785 := bstep (se 2 (by rfl) ⟨709044, by rfl⟩ : syracuseStep 1890785 = 1418089) B1418089
theorem B2103779 : Blo 1260448 2103779 := bstep (se 1 (by rfl) ⟨1577834, by rfl⟩ : syracuseStep 2103779 = 3155669) B3155669
theorem B2128369 : Blo 1260448 2128369 := bstep (se 2 (by rfl) ⟨798138, by rfl⟩ : syracuseStep 2128369 = 1596277) B1596277
theorem B1890803 : Blo 1260448 1890803 := bstep (se 1 (by rfl) ⟨1418102, by rfl⟩ : syracuseStep 1890803 = 2836205) B2836205
theorem B1890833 : Blo 1260448 1890833 := bstep (se 2 (by rfl) ⟨709062, by rfl⟩ : syracuseStep 1890833 = 1418125) B1418125
theorem B2128403 : Blo 1260448 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B1890851 : Blo 1260448 1890851 := bstep (se 1 (by rfl) ⟨1418138, by rfl⟩ : syracuseStep 1890851 = 2836277) B2836277
theorem B1890881 : Blo 1260448 1890881 := bstep (se 2 (by rfl) ⟨709080, by rfl⟩ : syracuseStep 1890881 = 1418161) B1418161
theorem B4258385 : Blo 1260448 4258385 := bstep (se 2 (by rfl) ⟨1596894, by rfl⟩ : syracuseStep 4258385 = 3193789) B3193789
theorem B1890899 : Blo 1260448 1890899 := bstep (se 1 (by rfl) ⟨1418174, by rfl⟩ : syracuseStep 1890899 = 2836349) B2836349
theorem B1890929 : Blo 1260448 1890929 := bstep (se 2 (by rfl) ⟨709098, by rfl⟩ : syracuseStep 1890929 = 1418197) B1418197
theorem B4790897 : Blo 1260448 4790897 := bstep (se 2 (by rfl) ⟨1796586, by rfl⟩ : syracuseStep 4790897 = 3593173) B3593173
theorem B1596019 : Blo 1260448 1596019 := bstep (se 1 (by rfl) ⟨1197014, by rfl⟩ : syracuseStep 1596019 = 2394029) B2394029
theorem B1890947 : Blo 1260448 1890947 := bstep (se 1 (by rfl) ⟨1418210, by rfl⟩ : syracuseStep 1890947 = 2836421) B2836421
theorem B3644045 : Blo 1260448 3644045 := bstep (se 3 (by rfl) ⟨683258, by rfl⟩ : syracuseStep 3644045 = 1366517) B1366517
theorem B2128531 : Blo 1260448 2128531 := bstep (se 1 (by rfl) ⟨1596398, by rfl⟩ : syracuseStep 2128531 = 3192797) B3192797
theorem B1890977 : Blo 1260448 1890977 := bstep (se 2 (by rfl) ⟨709116, by rfl⟩ : syracuseStep 1890977 = 1418233) B1418233
theorem B1890995 : Blo 1260448 1890995 := bstep (se 1 (by rfl) ⟨1418246, by rfl⟩ : syracuseStep 1890995 = 2836493) B2836493
theorem B1891025 : Blo 1260448 1891025 := bstep (se 2 (by rfl) ⟨709134, by rfl⟩ : syracuseStep 1891025 = 1418269) B1418269
theorem B1596115 : Blo 1260448 1596115 := bstep (se 1 (by rfl) ⟨1197086, by rfl⟩ : syracuseStep 1596115 = 2394173) B2394173
theorem B1891043 : Blo 1260448 1891043 := bstep (se 1 (by rfl) ⟨1418282, by rfl⟩ : syracuseStep 1891043 = 2836565) B2836565
theorem B1891073 : Blo 1260448 1891073 := bstep (se 2 (by rfl) ⟨709152, by rfl⟩ : syracuseStep 1891073 = 1418305) B1418305
theorem B1891091 : Blo 1260448 1891091 := bstep (se 1 (by rfl) ⟨1418318, by rfl⟩ : syracuseStep 1891091 = 2836637) B2836637
theorem B2128673 : Blo 1260448 2128673 := bstep (se 2 (by rfl) ⟨798252, by rfl⟩ : syracuseStep 2128673 = 1596505) B1596505
theorem B1891121 : Blo 1260448 1891121 := bstep (se 2 (by rfl) ⟨709170, by rfl⟩ : syracuseStep 1891121 = 1418341) B1418341
theorem B1891139 : Blo 1260448 1891139 := bstep (se 1 (by rfl) ⟨1418354, by rfl⟩ : syracuseStep 1891139 = 2836709) B2836709
theorem B1514323 : Blo 1260448 1514323 := bstep (se 1 (by rfl) ⟨1135742, by rfl⟩ : syracuseStep 1514323 = 2271485) B2271485
theorem B1891169 : Blo 1260448 1891169 := bstep (se 2 (by rfl) ⟨709188, by rfl⟩ : syracuseStep 1891169 = 1418377) B1418377
theorem B1891187 : Blo 1260448 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B1891217 : Blo 1260448 1891217 := bstep (se 2 (by rfl) ⟨709206, by rfl⟩ : syracuseStep 1891217 = 1418413) B1418413
theorem B2128801 : Blo 1260448 2128801 := bstep (se 2 (by rfl) ⟨798300, by rfl⟩ : syracuseStep 2128801 = 1596601) B1596601
theorem B1260451 : Blo 1260448 1260451 := bstep (se 1 (by rfl) ⟨945338, by rfl⟩ : syracuseStep 1260451 = 1890677) B1890677
theorem B1891235 : Blo 1260448 1891235 := bstep (se 1 (by rfl) ⟨1418426, by rfl⟩ : syracuseStep 1891235 = 2836853) B2836853
theorem B1260467 : Blo 1260448 1260467 := bstep (se 1 (by rfl) ⟨945350, by rfl⟩ : syracuseStep 1260467 = 1890701) B1890701
theorem B1891265 : Blo 1260448 1891265 := bstep (se 2 (by rfl) ⟨709224, by rfl⟩ : syracuseStep 1891265 = 1418449) B1418449
theorem B1260483 : Blo 1260448 1260483 := bstep (se 1 (by rfl) ⟨945362, by rfl⟩ : syracuseStep 1260483 = 1890725) B1890725
theorem B2128835 : Blo 1260448 2128835 := bstep (se 1 (by rfl) ⟨1596626, by rfl⟩ : syracuseStep 2128835 = 3193253) B3193253
theorem B1260499 : Blo 1260448 1260499 := bstep (se 1 (by rfl) ⟨945374, by rfl⟩ : syracuseStep 1260499 = 1890749) B1890749
theorem B1891283 : Blo 1260448 1891283 := bstep (se 1 (by rfl) ⟨1418462, by rfl⟩ : syracuseStep 1891283 = 2836925) B2836925
theorem B1260515 : Blo 1260448 1260515 := bstep (se 1 (by rfl) ⟨945386, by rfl⟩ : syracuseStep 1260515 = 1890773) B1890773
theorem B1891313 : Blo 1260448 1891313 := bstep (se 2 (by rfl) ⟨709242, by rfl⟩ : syracuseStep 1891313 = 1418485) B1418485
theorem B1260531 : Blo 1260448 1260531 := bstep (se 1 (by rfl) ⟨945398, by rfl⟩ : syracuseStep 1260531 = 1890797) B1890797
theorem B1260547 : Blo 1260448 1260547 := bstep (se 1 (by rfl) ⟨945410, by rfl⟩ : syracuseStep 1260547 = 1890821) B1890821
theorem B1891331 : Blo 1260448 1891331 := bstep (se 1 (by rfl) ⟨1418498, by rfl⟩ : syracuseStep 1891331 = 2836997) B2836997
theorem B1260563 : Blo 1260448 1260563 := bstep (se 1 (by rfl) ⟨945422, by rfl⟩ : syracuseStep 1260563 = 1890845) B1890845
theorem B1891361 : Blo 1260448 1891361 := bstep (se 2 (by rfl) ⟨709260, by rfl⟩ : syracuseStep 1891361 = 1418521) B1418521
theorem B1260579 : Blo 1260448 1260579 := bstep (se 1 (by rfl) ⟨945434, by rfl⟩ : syracuseStep 1260579 = 1890869) B1890869
theorem B2694179 : Blo 1260448 2694179 := bstep (se 1 (by rfl) ⟨2020634, by rfl⟩ : syracuseStep 2694179 = 4041269) B4041269
theorem B1260595 : Blo 1260448 1260595 := bstep (se 1 (by rfl) ⟨945446, by rfl⟩ : syracuseStep 1260595 = 1890893) B1890893
theorem B1891379 : Blo 1260448 1891379 := bstep (se 1 (by rfl) ⟨1418534, by rfl⟩ : syracuseStep 1891379 = 2837069) B2837069
theorem B1260611 : Blo 1260448 1260611 := bstep (se 1 (by rfl) ⟨945458, by rfl⟩ : syracuseStep 1260611 = 1890917) B1890917
theorem B2128963 : Blo 1260448 2128963 := bstep (se 1 (by rfl) ⟨1596722, by rfl⟩ : syracuseStep 2128963 = 3193445) B3193445
theorem B1891409 : Blo 1260448 1891409 := bstep (se 2 (by rfl) ⟨709278, by rfl⟩ : syracuseStep 1891409 = 1418557) B1418557
theorem B1260627 : Blo 1260448 1260627 := bstep (se 1 (by rfl) ⟨945470, by rfl⟩ : syracuseStep 1260627 = 1890941) B1890941
theorem B1260643 : Blo 1260448 1260643 := bstep (se 1 (by rfl) ⟨945482, by rfl⟩ : syracuseStep 1260643 = 1890965) B1890965
theorem B1891427 : Blo 1260448 1891427 := bstep (se 1 (by rfl) ⟨1418570, by rfl⟩ : syracuseStep 1891427 = 2837141) B2837141
theorem B4258925 : Blo 1260448 4258925 := bstep (se 3 (by rfl) ⟨798548, by rfl⟩ : syracuseStep 4258925 = 1597097) B1597097
theorem B1260659 : Blo 1260448 1260659 := bstep (se 1 (by rfl) ⟨945494, by rfl⟩ : syracuseStep 1260659 = 1890989) B1890989
theorem B1891457 : Blo 1260448 1891457 := bstep (se 2 (by rfl) ⟨709296, by rfl⟩ : syracuseStep 1891457 = 1418593) B1418593
theorem B1260675 : Blo 1260448 1260675 := bstep (se 1 (by rfl) ⟨945506, by rfl⟩ : syracuseStep 1260675 = 1891013) B1891013
theorem B1260691 : Blo 1260448 1260691 := bstep (se 1 (by rfl) ⟨945518, by rfl⟩ : syracuseStep 1260691 = 1891037) B1891037
theorem B1891475 : Blo 1260448 1891475 := bstep (se 1 (by rfl) ⟨1418606, by rfl⟩ : syracuseStep 1891475 = 2837213) B2837213
theorem B1260707 : Blo 1260448 1260707 := bstep (se 1 (by rfl) ⟨945530, by rfl⟩ : syracuseStep 1260707 = 1891061) B1891061
theorem B4258979 : Blo 1260448 4258979 := bstep (se 1 (by rfl) ⟨3194234, by rfl⟩ : syracuseStep 4258979 = 6388469) B6388469
theorem B1891505 : Blo 1260448 1891505 := bstep (se 2 (by rfl) ⟨709314, by rfl⟩ : syracuseStep 1891505 = 1418629) B1418629
theorem B1260723 : Blo 1260448 1260723 := bstep (se 1 (by rfl) ⟨945542, by rfl⟩ : syracuseStep 1260723 = 1891085) B1891085
theorem B1260739 : Blo 1260448 1260739 := bstep (se 1 (by rfl) ⟨945554, by rfl⟩ : syracuseStep 1260739 = 1891109) B1891109
theorem B1891523 : Blo 1260448 1891523 := bstep (se 1 (by rfl) ⟨1418642, by rfl⟩ : syracuseStep 1891523 = 2837285) B2837285
theorem B1596611 : Blo 1260448 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B2129105 : Blo 1260448 2129105 := bstep (se 2 (by rfl) ⟨798414, by rfl⟩ : syracuseStep 2129105 = 1596829) B1596829
theorem B1260755 : Blo 1260448 1260755 := bstep (se 1 (by rfl) ⟨945566, by rfl⟩ : syracuseStep 1260755 = 1891133) B1891133
theorem B69008597 : Blo 1260448 69008597 := bstep (se 7 (by rfl) ⟨808694, by rfl⟩ : syracuseStep 69008597 = 1617389) B1617389
theorem B1891553 : Blo 1260448 1891553 := bstep (se 2 (by rfl) ⟨709332, by rfl⟩ : syracuseStep 1891553 = 1418665) B1418665
theorem B1260771 : Blo 1260448 1260771 := bstep (se 1 (by rfl) ⟨945578, by rfl⟩ : syracuseStep 1260771 = 1891157) B1891157
theorem B1260787 : Blo 1260448 1260787 := bstep (se 1 (by rfl) ⟨945590, by rfl⟩ : syracuseStep 1260787 = 1891181) B1891181
theorem B1891571 : Blo 1260448 1891571 := bstep (se 1 (by rfl) ⟨1418678, by rfl⟩ : syracuseStep 1891571 = 2837357) B2837357
theorem B1260803 : Blo 1260448 1260803 := bstep (se 1 (by rfl) ⟨945602, by rfl⟩ : syracuseStep 1260803 = 1891205) B1891205
theorem B1891601 : Blo 1260448 1891601 := bstep (se 2 (by rfl) ⟨709350, by rfl⟩ : syracuseStep 1891601 = 1418701) B1418701
theorem B1260819 : Blo 1260448 1260819 := bstep (se 1 (by rfl) ⟨945614, by rfl⟩ : syracuseStep 1260819 = 1891229) B1891229
theorem B1260835 : Blo 1260448 1260835 := bstep (se 1 (by rfl) ⟨945626, by rfl⟩ : syracuseStep 1260835 = 1891253) B1891253
theorem B1891619 : Blo 1260448 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B8084771 : Blo 1260448 8084771 := bstep (se 1 (by rfl) ⟨6063578, by rfl⟩ : syracuseStep 8084771 = 12127157) B12127157
theorem B1260851 : Blo 1260448 1260851 := bstep (se 1 (by rfl) ⟨945638, by rfl⟩ : syracuseStep 1260851 = 1891277) B1891277
theorem B2047283 : Blo 1260448 2047283 := bstep (se 1 (by rfl) ⟨1535462, by rfl⟩ : syracuseStep 2047283 = 3070925) B3070925
theorem B1891649 : Blo 1260448 1891649 := bstep (se 2 (by rfl) ⟨709368, by rfl⟩ : syracuseStep 1891649 = 1418737) B1418737
theorem B1260867 : Blo 1260448 1260867 := bstep (se 1 (by rfl) ⟨945650, by rfl⟩ : syracuseStep 1260867 = 1891301) B1891301
theorem B2129233 : Blo 1260448 2129233 := bstep (se 2 (by rfl) ⟨798462, by rfl⟩ : syracuseStep 2129233 = 1596925) B1596925
theorem B1260883 : Blo 1260448 1260883 := bstep (se 1 (by rfl) ⟨945662, by rfl⟩ : syracuseStep 1260883 = 1891325) B1891325
theorem B1891667 : Blo 1260448 1891667 := bstep (se 1 (by rfl) ⟨1418750, by rfl⟩ : syracuseStep 1891667 = 2837501) B2837501
theorem B1260899 : Blo 1260448 1260899 := bstep (se 1 (by rfl) ⟨945674, by rfl⟩ : syracuseStep 1260899 = 1891349) B1891349
theorem B1891697 : Blo 1260448 1891697 := bstep (se 2 (by rfl) ⟨709386, by rfl⟩ : syracuseStep 1891697 = 1418773) B1418773
theorem B3194225 : Blo 1260448 3194225 := bstep (se 2 (by rfl) ⟨1197834, by rfl⟩ : syracuseStep 3194225 = 2395669) B2395669
theorem B1260915 : Blo 1260448 1260915 := bstep (se 1 (by rfl) ⟨945686, by rfl⟩ : syracuseStep 1260915 = 1891373) B1891373
theorem B2129267 : Blo 1260448 2129267 := bstep (se 1 (by rfl) ⟨1596950, by rfl⟩ : syracuseStep 2129267 = 3193901) B3193901
theorem B3833219 : Blo 1260448 3833219 := bstep (se 1 (by rfl) ⟨2874914, by rfl⟩ : syracuseStep 3833219 = 5749829) B5749829
theorem B1260931 : Blo 1260448 1260931 := bstep (se 1 (by rfl) ⟨945698, by rfl⟩ : syracuseStep 1260931 = 1891397) B1891397
theorem B1891715 : Blo 1260448 1891715 := bstep (se 1 (by rfl) ⟨1418786, by rfl⟩ : syracuseStep 1891715 = 2837573) B2837573
theorem B1260947 : Blo 1260448 1260947 := bstep (se 1 (by rfl) ⟨945710, by rfl⟩ : syracuseStep 1260947 = 1891421) B1891421
theorem B1891745 : Blo 1260448 1891745 := bstep (se 2 (by rfl) ⟨709404, by rfl⟩ : syracuseStep 1891745 = 1418809) B1418809
theorem B1260963 : Blo 1260448 1260963 := bstep (se 1 (by rfl) ⟨945722, by rfl⟩ : syracuseStep 1260963 = 1891445) B1891445
theorem B3194275 : Blo 1260448 3194275 := bstep (se 1 (by rfl) ⟨2395706, by rfl⟩ : syracuseStep 3194275 = 4791413) B4791413
theorem B4259249 : Blo 1260448 4259249 := bstep (se 2 (by rfl) ⟨1597218, by rfl⟩ : syracuseStep 4259249 = 3194437) B3194437
theorem B1260979 : Blo 1260448 1260979 := bstep (se 1 (by rfl) ⟨945734, by rfl⟩ : syracuseStep 1260979 = 1891469) B1891469
theorem B1891763 : Blo 1260448 1891763 := bstep (se 1 (by rfl) ⟨1418822, by rfl⟩ : syracuseStep 1891763 = 2837645) B2837645
theorem B1260995 : Blo 1260448 1260995 := bstep (se 1 (by rfl) ⟨945746, by rfl⟩ : syracuseStep 1260995 = 1891493) B1891493
theorem B1891793 : Blo 1260448 1891793 := bstep (se 2 (by rfl) ⟨709422, by rfl⟩ : syracuseStep 1891793 = 1418845) B1418845
theorem B1261011 : Blo 1260448 1261011 := bstep (se 1 (by rfl) ⟨945758, by rfl⟩ : syracuseStep 1261011 = 1891517) B1891517
theorem B3833315 : Blo 1260448 3833315 := bstep (se 1 (by rfl) ⟨2874986, by rfl⟩ : syracuseStep 3833315 = 5749973) B5749973
theorem B1261027 : Blo 1260448 1261027 := bstep (se 1 (by rfl) ⟨945770, by rfl⟩ : syracuseStep 1261027 = 1891541) B1891541
theorem B1891811 : Blo 1260448 1891811 := bstep (se 1 (by rfl) ⟨1418858, by rfl⟩ : syracuseStep 1891811 = 2837717) B2837717
theorem B1261043 : Blo 1260448 1261043 := bstep (se 1 (by rfl) ⟨945782, by rfl⟩ : syracuseStep 1261043 = 1891565) B1891565
theorem B2129395 : Blo 1260448 2129395 := bstep (se 1 (by rfl) ⟨1597046, by rfl⟩ : syracuseStep 2129395 = 3194093) B3194093
theorem B1891841 : Blo 1260448 1891841 := bstep (se 2 (by rfl) ⟨709440, by rfl⟩ : syracuseStep 1891841 = 1418881) B1418881
theorem B1261059 : Blo 1260448 1261059 := bstep (se 1 (by rfl) ⟨945794, by rfl⟩ : syracuseStep 1261059 = 1891589) B1891589
theorem B1261075 : Blo 1260448 1261075 := bstep (se 1 (by rfl) ⟨945806, by rfl⟩ : syracuseStep 1261075 = 1891613) B1891613
theorem B1891859 : Blo 1260448 1891859 := bstep (se 1 (by rfl) ⟨1418894, by rfl⟩ : syracuseStep 1891859 = 2837789) B2837789
theorem B1261091 : Blo 1260448 1261091 := bstep (se 1 (by rfl) ⟨945818, by rfl⟩ : syracuseStep 1261091 = 1891637) B1891637
theorem B1891889 : Blo 1260448 1891889 := bstep (se 2 (by rfl) ⟨709458, by rfl⟩ : syracuseStep 1891889 = 1418917) B1418917
theorem B3194417 : Blo 1260448 3194417 := bstep (se 2 (by rfl) ⟨1197906, by rfl⟩ : syracuseStep 3194417 = 2395813) B2395813
theorem B1261107 : Blo 1260448 1261107 := bstep (se 1 (by rfl) ⟨945830, by rfl⟩ : syracuseStep 1261107 = 1891661) B1891661
theorem B1261123 : Blo 1260448 1261123 := bstep (se 1 (by rfl) ⟨945842, by rfl⟩ : syracuseStep 1261123 = 1891685) B1891685
theorem B1891907 : Blo 1260448 1891907 := bstep (se 1 (by rfl) ⟨1418930, by rfl⟩ : syracuseStep 1891907 = 2837861) B2837861
theorem B1261139 : Blo 1260448 1261139 := bstep (se 1 (by rfl) ⟨945854, by rfl⟩ : syracuseStep 1261139 = 1891709) B1891709
theorem B1891937 : Blo 1260448 1891937 := bstep (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) B1418953
theorem B1261155 : Blo 1260448 1261155 := bstep (se 1 (by rfl) ⟨945866, by rfl⟩ : syracuseStep 1261155 = 1891733) B1891733
theorem B1261171 : Blo 1260448 1261171 := bstep (se 1 (by rfl) ⟨945878, by rfl⟩ : syracuseStep 1261171 = 1891757) B1891757
theorem B1891955 : Blo 1260448 1891955 := bstep (se 1 (by rfl) ⟨1418966, by rfl⟩ : syracuseStep 1891955 = 2837933) B2837933
theorem B2129537 : Blo 1260448 2129537 := bstep (se 2 (by rfl) ⟨798576, by rfl⟩ : syracuseStep 2129537 = 1597153) B1597153
theorem B1261187 : Blo 1260448 1261187 := bstep (se 1 (by rfl) ⟨945890, by rfl⟩ : syracuseStep 1261187 = 1891781) B1891781
theorem B1891985 : Blo 1260448 1891985 := bstep (se 2 (by rfl) ⟨709494, by rfl⟩ : syracuseStep 1891985 = 1418989) B1418989
theorem B1261203 : Blo 1260448 1261203 := bstep (se 1 (by rfl) ⟨945902, by rfl⟩ : syracuseStep 1261203 = 1891805) B1891805
theorem B1261219 : Blo 1260448 1261219 := bstep (se 1 (by rfl) ⟨945914, by rfl⟩ : syracuseStep 1261219 = 1891829) B1891829
theorem B1892003 : Blo 1260448 1892003 := bstep (se 1 (by rfl) ⟨1419002, by rfl⟩ : syracuseStep 1892003 = 2838005) B2838005
theorem B1261235 : Blo 1260448 1261235 := bstep (se 1 (by rfl) ⟨945926, by rfl⟩ : syracuseStep 1261235 = 1891853) B1891853
theorem B1892033 : Blo 1260448 1892033 := bstep (se 2 (by rfl) ⟨709512, by rfl⟩ : syracuseStep 1892033 = 1419025) B1419025
theorem B1261251 : Blo 1260448 1261251 := bstep (se 1 (by rfl) ⟨945938, by rfl⟩ : syracuseStep 1261251 = 1891877) B1891877
theorem B1261267 : Blo 1260448 1261267 := bstep (se 1 (by rfl) ⟨945950, by rfl⟩ : syracuseStep 1261267 = 1891901) B1891901
theorem B1892051 : Blo 1260448 1892051 := bstep (se 1 (by rfl) ⟨1419038, by rfl⟩ : syracuseStep 1892051 = 2838077) B2838077
theorem B1261283 : Blo 1260448 1261283 := bstep (se 1 (by rfl) ⟨945962, by rfl⟩ : syracuseStep 1261283 = 1891925) B1891925
theorem B1892081 : Blo 1260448 1892081 := bstep (se 2 (by rfl) ⟨709530, by rfl⟩ : syracuseStep 1892081 = 1419061) B1419061
theorem B1261299 : Blo 1260448 1261299 := bstep (se 1 (by rfl) ⟨945974, by rfl⟩ : syracuseStep 1261299 = 1891949) B1891949
theorem B2129665 : Blo 1260448 2129665 := bstep (se 2 (by rfl) ⟨798624, by rfl⟩ : syracuseStep 2129665 = 1597249) B1597249
theorem B1261315 : Blo 1260448 1261315 := bstep (se 1 (by rfl) ⟨945986, by rfl⟩ : syracuseStep 1261315 = 1891973) B1891973
theorem B1892099 : Blo 1260448 1892099 := bstep (se 1 (by rfl) ⟨1419074, by rfl⟩ : syracuseStep 1892099 = 2838149) B2838149
theorem B12132109 : Blo 1260448 12132109 := bstep (se 3 (by rfl) ⟨2274770, by rfl⟩ : syracuseStep 12132109 = 4549541) B4549541
theorem B1261331 : Blo 1260448 1261331 := bstep (se 1 (by rfl) ⟨945998, by rfl⟩ : syracuseStep 1261331 = 1891997) B1891997
theorem B1892129 : Blo 1260448 1892129 := bstep (se 2 (by rfl) ⟨709548, by rfl⟩ : syracuseStep 1892129 = 1419097) B1419097
theorem B1261347 : Blo 1260448 1261347 := bstep (se 1 (by rfl) ⟨946010, by rfl⟩ : syracuseStep 1261347 = 1892021) B1892021
theorem B2129699 : Blo 1260448 2129699 := bstep (se 1 (by rfl) ⟨1597274, by rfl⟩ : syracuseStep 2129699 = 3194549) B3194549
theorem B1261363 : Blo 1260448 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B1892147 : Blo 1260448 1892147 := bstep (se 1 (by rfl) ⟨1419110, by rfl⟩ : syracuseStep 1892147 = 2838221) B2838221
theorem B1261379 : Blo 1260448 1261379 := bstep (se 1 (by rfl) ⟨946034, by rfl⟩ : syracuseStep 1261379 = 1892069) B1892069
theorem B1892177 : Blo 1260448 1892177 := bstep (se 2 (by rfl) ⟨709566, by rfl⟩ : syracuseStep 1892177 = 1419133) B1419133
theorem B1261395 : Blo 1260448 1261395 := bstep (se 1 (by rfl) ⟨946046, by rfl⟩ : syracuseStep 1261395 = 1892093) B1892093
theorem B1261411 : Blo 1260448 1261411 := bstep (se 1 (by rfl) ⟨946058, by rfl⟩ : syracuseStep 1261411 = 1892117) B1892117
theorem B1892195 : Blo 1260448 1892195 := bstep (se 1 (by rfl) ⟨1419146, by rfl⟩ : syracuseStep 1892195 = 2838293) B2838293
theorem B6389603 : Blo 1260448 6389603 := bstep (se 1 (by rfl) ⟨4792202, by rfl⟩ : syracuseStep 6389603 = 9584405) B9584405
theorem B3833713 : Blo 1260448 3833713 := bstep (se 2 (by rfl) ⟨1437642, by rfl⟩ : syracuseStep 3833713 = 2875285) B2875285
theorem B1261427 : Blo 1260448 1261427 := bstep (se 1 (by rfl) ⟨946070, by rfl⟩ : syracuseStep 1261427 = 1892141) B1892141
theorem B1892225 : Blo 1260448 1892225 := bstep (se 2 (by rfl) ⟨709584, by rfl⟩ : syracuseStep 1892225 = 1419169) B1419169
theorem B1515395 : Blo 1260448 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B1261443 : Blo 1260448 1261443 := bstep (se 1 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 1261443 = 1892165) B1892165
theorem B1597315 : Blo 1260448 1597315 := bstep (se 1 (by rfl) ⟨1197986, by rfl⟩ : syracuseStep 1597315 = 2395973) B2395973
theorem B1261459 : Blo 1260448 1261459 := bstep (se 1 (by rfl) ⟨946094, by rfl⟩ : syracuseStep 1261459 = 1892189) B1892189
theorem B1892243 : Blo 1260448 1892243 := bstep (se 1 (by rfl) ⟨1419182, by rfl⟩ : syracuseStep 1892243 = 2838365) B2838365
theorem B1261475 : Blo 1260448 1261475 := bstep (se 1 (by rfl) ⟨946106, by rfl⟩ : syracuseStep 1261475 = 1892213) B1892213
theorem B2129827 : Blo 1260448 2129827 := bstep (se 1 (by rfl) ⟨1597370, by rfl⟩ : syracuseStep 2129827 = 3194741) B3194741
theorem B1892273 : Blo 1260448 1892273 := bstep (se 2 (by rfl) ⟨709602, by rfl⟩ : syracuseStep 1892273 = 1419205) B1419205
theorem B1261491 : Blo 1260448 1261491 := bstep (se 1 (by rfl) ⟨946118, by rfl⟩ : syracuseStep 1261491 = 1892237) B1892237
theorem B1261507 : Blo 1260448 1261507 := bstep (se 1 (by rfl) ⟨946130, by rfl⟩ : syracuseStep 1261507 = 1892261) B1892261
theorem B1892291 : Blo 1260448 1892291 := bstep (se 1 (by rfl) ⟨1419218, by rfl⟩ : syracuseStep 1892291 = 2838437) B2838437
theorem B10780613 : Blo 1260448 10780613 := bstep (se 4 (by rfl) ⟨1010682, by rfl⟩ : syracuseStep 10780613 = 2021365) B2021365
theorem B4259789 : Blo 1260448 4259789 := bstep (se 3 (by rfl) ⟨798710, by rfl⟩ : syracuseStep 4259789 = 1597421) B1597421
theorem B1261523 : Blo 1260448 1261523 := bstep (se 1 (by rfl) ⟨946142, by rfl⟩ : syracuseStep 1261523 = 1892285) B1892285
theorem B1892321 : Blo 1260448 1892321 := bstep (se 2 (by rfl) ⟨709620, by rfl⟩ : syracuseStep 1892321 = 1419241) B1419241
theorem B1261539 : Blo 1260448 1261539 := bstep (se 1 (by rfl) ⟨946154, by rfl⟩ : syracuseStep 1261539 = 1892309) B1892309
theorem B1597411 : Blo 1260448 1597411 := bstep (se 1 (by rfl) ⟨1198058, by rfl⟩ : syracuseStep 1597411 = 2396117) B2396117
theorem B1261555 : Blo 1260448 1261555 := bstep (se 1 (by rfl) ⟨946166, by rfl⟩ : syracuseStep 1261555 = 1892333) B1892333
theorem B1892339 : Blo 1260448 1892339 := bstep (se 1 (by rfl) ⟨1419254, by rfl⟩ : syracuseStep 1892339 = 2838509) B2838509
theorem B1892363 : Blo 1260448 1892363 := bstep (se 1 (by rfl) ⟨1419272, by rfl⟩ : syracuseStep 1892363 = 2838545) B2838545
theorem B1261579 : Blo 1260448 1261579 := bstep (se 1 (by rfl) ⟨946184, by rfl⟩ : syracuseStep 1261579 = 1892369) B1892369
theorem B8306705 : Blo 1260448 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B1892375 : Blo 1260448 1892375 := bstep (se 1 (by rfl) ⟨1419281, by rfl⟩ : syracuseStep 1892375 = 2838563) B2838563
theorem B1261591 : Blo 1260448 1261591 := bstep (se 1 (by rfl) ⟨946193, by rfl⟩ : syracuseStep 1261591 = 1892387) B1892387
theorem B1728535 : Blo 1260448 1728535 := bstep (se 1 (by rfl) ⟨1296401, by rfl⟩ : syracuseStep 1728535 = 2592803) B2592803
theorem B3194903 : Blo 1260448 3194903 := bstep (se 1 (by rfl) ⟨2396177, by rfl⟩ : syracuseStep 3194903 = 4792355) B4792355
theorem B1261611 : Blo 1260448 1261611 := bstep (se 1 (by rfl) ⟨946208, by rfl⟩ : syracuseStep 1261611 = 1892417) B1892417
theorem B1261623 : Blo 1260448 1261623 := bstep (se 1 (by rfl) ⟨946217, by rfl⟩ : syracuseStep 1261623 = 1892435) B1892435
theorem B4792385 : Blo 1260448 4792385 := bstep (se 2 (by rfl) ⟨1797144, by rfl⟩ : syracuseStep 4792385 = 3594289) B3594289
theorem B1261643 : Blo 1260448 1261643 := bstep (se 1 (by rfl) ⟨946232, by rfl⟩ : syracuseStep 1261643 = 1892465) B1892465
theorem B1261655 : Blo 1260448 1261655 := bstep (se 1 (by rfl) ⟨946241, by rfl⟩ : syracuseStep 1261655 = 1892483) B1892483
theorem B1892441 : Blo 1260448 1892441 := bstep (se 2 (by rfl) ⟨709665, by rfl⟩ : syracuseStep 1892441 = 1419331) B1419331
theorem B7184477 : Blo 1260448 7184477 := bstep (se 3 (by rfl) ⟨1347089, by rfl⟩ : syracuseStep 7184477 = 2694179) B2694179
theorem B1261675 : Blo 1260448 1261675 := bstep (se 1 (by rfl) ⟨946256, by rfl⟩ : syracuseStep 1261675 = 1892513) B1892513
theorem B1261687 : Blo 1260448 1261687 := bstep (se 1 (by rfl) ⟨946265, by rfl⟩ : syracuseStep 1261687 = 1892531) B1892531
theorem B1261707 : Blo 1260448 1261707 := bstep (se 1 (by rfl) ⟨946280, by rfl⟩ : syracuseStep 1261707 = 1892561) B1892561
theorem B1261719 : Blo 1260448 1261719 := bstep (se 1 (by rfl) ⟨946289, by rfl⟩ : syracuseStep 1261719 = 1892579) B1892579
theorem B1704089 : Blo 1260448 1704089 := bstep (se 2 (by rfl) ⟨639033, by rfl⟩ : syracuseStep 1704089 = 1278067) B1278067
theorem B1261739 : Blo 1260448 1261739 := bstep (se 1 (by rfl) ⟨946304, by rfl⟩ : syracuseStep 1261739 = 1892609) B1892609
theorem B4038835 : Blo 1260448 4038835 := bstep (se 1 (by rfl) ⟨3029126, by rfl⟩ : syracuseStep 4038835 = 6058253) B6058253
theorem B1261751 : Blo 1260448 1261751 := bstep (se 1 (by rfl) ⟨946313, by rfl⟩ : syracuseStep 1261751 = 1892627) B1892627
theorem B4546763 : Blo 1260448 4546763 := bstep (se 1 (by rfl) ⟨3410072, by rfl⟩ : syracuseStep 4546763 = 6820145) B6820145
theorem B1892555 : Blo 1260448 1892555 := bstep (se 1 (by rfl) ⟨1419416, by rfl⟩ : syracuseStep 1892555 = 2838833) B2838833
theorem B1261771 : Blo 1260448 1261771 := bstep (se 1 (by rfl) ⟨946328, by rfl⟩ : syracuseStep 1261771 = 1892657) B1892657
theorem B1892567 : Blo 1260448 1892567 := bstep (se 1 (by rfl) ⟨1419425, by rfl⟩ : syracuseStep 1892567 = 2838851) B2838851
theorem B1261783 : Blo 1260448 1261783 := bstep (se 1 (by rfl) ⟨946337, by rfl⟩ : syracuseStep 1261783 = 1892675) B1892675
theorem B1261803 : Blo 1260448 1261803 := bstep (se 1 (by rfl) ⟨946352, by rfl⟩ : syracuseStep 1261803 = 1892705) B1892705
theorem B1261815 : Blo 1260448 1261815 := bstep (se 1 (by rfl) ⟨946361, by rfl⟩ : syracuseStep 1261815 = 1892723) B1892723
theorem B1261835 : Blo 1260448 1261835 := bstep (se 1 (by rfl) ⟨946376, by rfl⟩ : syracuseStep 1261835 = 1892753) B1892753
theorem B1261847 : Blo 1260448 1261847 := bstep (se 1 (by rfl) ⟨946385, by rfl⟩ : syracuseStep 1261847 = 1892771) B1892771
theorem B1892633 : Blo 1260448 1892633 := bstep (se 2 (by rfl) ⟨709737, by rfl⟩ : syracuseStep 1892633 = 1419475) B1419475
theorem B1261867 : Blo 1260448 1261867 := bstep (se 1 (by rfl) ⟨946400, by rfl⟩ : syracuseStep 1261867 = 1892801) B1892801
theorem B1261879 : Blo 1260448 1261879 := bstep (se 1 (by rfl) ⟨946409, by rfl⟩ : syracuseStep 1261879 = 1892819) B1892819
theorem B1261899 : Blo 1260448 1261899 := bstep (se 1 (by rfl) ⟨946424, by rfl⟩ : syracuseStep 1261899 = 1892849) B1892849
theorem B1261911 : Blo 1260448 1261911 := bstep (se 1 (by rfl) ⟨946433, by rfl⟩ : syracuseStep 1261911 = 1892867) B1892867
theorem B1261931 : Blo 1260448 1261931 := bstep (se 1 (by rfl) ⟨946448, by rfl⟩ : syracuseStep 1261931 = 1892897) B1892897
theorem B1261943 : Blo 1260448 1261943 := bstep (se 1 (by rfl) ⟨946457, by rfl⟩ : syracuseStep 1261943 = 1892915) B1892915
theorem B1892747 : Blo 1260448 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B1261963 : Blo 1260448 1261963 := bstep (se 1 (by rfl) ⟨946472, by rfl⟩ : syracuseStep 1261963 = 1892945) B1892945
theorem B1892759 : Blo 1260448 1892759 := bstep (se 1 (by rfl) ⟨1419569, by rfl⟩ : syracuseStep 1892759 = 2839139) B2839139
theorem B1261975 : Blo 1260448 1261975 := bstep (se 1 (by rfl) ⟨946481, by rfl⟩ : syracuseStep 1261975 = 1892963) B1892963
theorem B1261995 : Blo 1260448 1261995 := bstep (se 1 (by rfl) ⟨946496, by rfl⟩ : syracuseStep 1261995 = 1892993) B1892993
theorem B4260275 : Blo 1260448 4260275 := bstep (se 1 (by rfl) ⟨3195206, by rfl⟩ : syracuseStep 4260275 = 6390413) B6390413
theorem B1262007 : Blo 1260448 1262007 := bstep (se 1 (by rfl) ⟨946505, by rfl⟩ : syracuseStep 1262007 = 1893011) B1893011
theorem B4039105 : Blo 1260448 4039105 := bstep (se 2 (by rfl) ⟨1514664, by rfl⟩ : syracuseStep 4039105 = 3029329) B3029329
theorem B1262027 : Blo 1260448 1262027 := bstep (se 1 (by rfl) ⟨946520, by rfl⟩ : syracuseStep 1262027 = 1893041) B1893041
theorem B1262039 : Blo 1260448 1262039 := bstep (se 1 (by rfl) ⟨946529, by rfl⟩ : syracuseStep 1262039 = 1893059) B1893059
theorem B1892825 : Blo 1260448 1892825 := bstep (se 2 (by rfl) ⟨709809, by rfl⟩ : syracuseStep 1892825 = 1419619) B1419619
theorem B1262059 : Blo 1260448 1262059 := bstep (se 1 (by rfl) ⟨946544, by rfl⟩ : syracuseStep 1262059 = 1893089) B1893089
theorem B1262071 : Blo 1260448 1262071 := bstep (se 1 (by rfl) ⟨946553, by rfl⟩ : syracuseStep 1262071 = 1893107) B1893107
theorem B1262091 : Blo 1260448 1262091 := bstep (se 1 (by rfl) ⟨946568, by rfl⟩ : syracuseStep 1262091 = 1893137) B1893137
theorem B1262103 : Blo 1260448 1262103 := bstep (se 1 (by rfl) ⟨946577, by rfl⟩ : syracuseStep 1262103 = 1893155) B1893155
theorem B1262123 : Blo 1260448 1262123 := bstep (se 1 (by rfl) ⟨946592, by rfl⟩ : syracuseStep 1262123 = 1893185) B1893185
theorem B1262135 : Blo 1260448 1262135 := bstep (se 1 (by rfl) ⟨946601, by rfl⟩ : syracuseStep 1262135 = 1893203) B1893203
theorem B1892939 : Blo 1260448 1892939 := bstep (se 1 (by rfl) ⟨1419704, by rfl⟩ : syracuseStep 1892939 = 2839409) B2839409
theorem B1262155 : Blo 1260448 1262155 := bstep (se 1 (by rfl) ⟨946616, by rfl⟩ : syracuseStep 1262155 = 1893233) B1893233
theorem B1892951 : Blo 1260448 1892951 := bstep (se 1 (by rfl) ⟨1419713, by rfl⟩ : syracuseStep 1892951 = 2839427) B2839427
theorem B1262167 : Blo 1260448 1262167 := bstep (se 1 (by rfl) ⟨946625, by rfl⟩ : syracuseStep 1262167 = 1893251) B1893251
theorem B1262187 : Blo 1260448 1262187 := bstep (se 1 (by rfl) ⟨946640, by rfl⟩ : syracuseStep 1262187 = 1893281) B1893281
theorem B1262199 : Blo 1260448 1262199 := bstep (se 1 (by rfl) ⟨946649, by rfl⟩ : syracuseStep 1262199 = 1893299) B1893299
theorem B1262219 : Blo 1260448 1262219 := bstep (se 1 (by rfl) ⟨946664, by rfl⟩ : syracuseStep 1262219 = 1893329) B1893329
theorem B1262231 : Blo 1260448 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B1893017 : Blo 1260448 1893017 := bstep (se 2 (by rfl) ⟨709881, by rfl⟩ : syracuseStep 1893017 = 1419763) B1419763
theorem B1262251 : Blo 1260448 1262251 := bstep (se 1 (by rfl) ⟨946688, by rfl⟩ : syracuseStep 1262251 = 1893377) B1893377
theorem B10781363 : Blo 1260448 10781363 := bstep (se 1 (by rfl) ⟨8086022, by rfl⟩ : syracuseStep 10781363 = 16172045) B16172045
theorem B3195571 : Blo 1260448 3195571 := bstep (se 1 (by rfl) ⟨2396678, by rfl⟩ : syracuseStep 3195571 = 4793357) B4793357
theorem B1262263 : Blo 1260448 1262263 := bstep (se 1 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 1262263 = 1893395) B1893395
theorem B4260545 : Blo 1260448 4260545 := bstep (se 2 (by rfl) ⟨1597704, by rfl⟩ : syracuseStep 4260545 = 3195409) B3195409
theorem B1262283 : Blo 1260448 1262283 := bstep (se 1 (by rfl) ⟨946712, by rfl⟩ : syracuseStep 1262283 = 1893425) B1893425
theorem B6062809 : Blo 1260448 6062809 := bstep (se 2 (by rfl) ⟨2273553, by rfl⟩ : syracuseStep 6062809 = 4547107) B4547107
theorem B1262295 : Blo 1260448 1262295 := bstep (se 1 (by rfl) ⟨946721, by rfl⟩ : syracuseStep 1262295 = 1893443) B1893443
theorem B3834589 : Blo 1260448 3834589 := bstep (se 3 (by rfl) ⟨718985, by rfl⟩ : syracuseStep 3834589 = 1437971) B1437971
theorem B4793053 : Blo 1260448 4793053 := bstep (se 3 (by rfl) ⟨898697, by rfl⟩ : syracuseStep 4793053 = 1797395) B1797395
theorem B1262315 : Blo 1260448 1262315 := bstep (se 1 (by rfl) ⟨946736, by rfl⟩ : syracuseStep 1262315 = 1893473) B1893473
theorem B1262327 : Blo 1260448 1262327 := bstep (se 1 (by rfl) ⟨946745, by rfl⟩ : syracuseStep 1262327 = 1893491) B1893491
theorem B1893131 : Blo 1260448 1893131 := bstep (se 1 (by rfl) ⟨1419848, by rfl⟩ : syracuseStep 1893131 = 2839697) B2839697
theorem B1262347 : Blo 1260448 1262347 := bstep (se 1 (by rfl) ⟨946760, by rfl⟩ : syracuseStep 1262347 = 1893521) B1893521
theorem B1893143 : Blo 1260448 1893143 := bstep (se 1 (by rfl) ⟨1419857, by rfl⟩ : syracuseStep 1893143 = 2839715) B2839715
theorem B1262359 : Blo 1260448 1262359 := bstep (se 1 (by rfl) ⟨946769, by rfl⟩ : syracuseStep 1262359 = 1893539) B1893539
theorem B1262379 : Blo 1260448 1262379 := bstep (se 1 (by rfl) ⟨946784, by rfl⟩ : syracuseStep 1262379 = 1893569) B1893569
theorem B1262391 : Blo 1260448 1262391 := bstep (se 1 (by rfl) ⟨946793, by rfl⟩ : syracuseStep 1262391 = 1893587) B1893587
theorem B2392897 : Blo 1260448 2392897 := bstep (se 2 (by rfl) ⟨897336, by rfl⟩ : syracuseStep 2392897 = 1794673) B1794673
theorem B7676747 : Blo 1260448 7676747 := bstep (se 1 (by rfl) ⟨5757560, by rfl⟩ : syracuseStep 7676747 = 11515121) B11515121
theorem B1262411 : Blo 1260448 1262411 := bstep (se 1 (by rfl) ⟨946808, by rfl⟩ : syracuseStep 1262411 = 1893617) B1893617
theorem B1418071 : Blo 1260448 1418071 := bstep (se 1 (by rfl) ⟨1063553, by rfl⟩ : syracuseStep 1418071 = 2127107) B2127107
theorem B1262423 : Blo 1260448 1262423 := bstep (se 1 (by rfl) ⟨946817, by rfl⟩ : syracuseStep 1262423 = 1893635) B1893635
theorem B1893209 : Blo 1260448 1893209 := bstep (se 2 (by rfl) ⟨709953, by rfl⟩ : syracuseStep 1893209 = 1419907) B1419907
theorem B19694435 : Blo 1260448 19694435 := bstep (se 1 (by rfl) ⟨14770826, by rfl⟩ : syracuseStep 19694435 = 29541653) B29541653
theorem B1262443 : Blo 1260448 1262443 := bstep (se 1 (by rfl) ⟨946832, by rfl⟩ : syracuseStep 1262443 = 1893665) B1893665
theorem B8078231 : Blo 1260448 8078231 := bstep (se 1 (by rfl) ⟨6058673, by rfl⟩ : syracuseStep 8078231 = 12117347) B12117347
theorem B1893323 : Blo 1260448 1893323 := bstep (se 1 (by rfl) ⟨1419992, by rfl⟩ : syracuseStep 1893323 = 2839985) B2839985
theorem B1893335 : Blo 1260448 1893335 := bstep (se 1 (by rfl) ⟨1420001, by rfl⟩ : syracuseStep 1893335 = 2840003) B2840003
theorem B2696179 : Blo 1260448 2696179 := bstep (se 1 (by rfl) ⟨2022134, by rfl⟩ : syracuseStep 2696179 = 4044269) B4044269
theorem B10363909 : Blo 1260448 10363909 := bstep (se 4 (by rfl) ⟨971616, by rfl⟩ : syracuseStep 10363909 = 1943233) B1943233
theorem B10232837 : Blo 1260448 10232837 := bstep (se 4 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 10232837 = 1918657) B1918657
theorem B1418251 : Blo 1260448 1418251 := bstep (se 1 (by rfl) ⟨1063688, by rfl⟩ : syracuseStep 1418251 = 2127377) B2127377
theorem B1893401 : Blo 1260448 1893401 := bstep (se 2 (by rfl) ⟨710025, by rfl⟩ : syracuseStep 1893401 = 1420051) B1420051
theorem B13648931 : Blo 1260448 13648931 := bstep (se 1 (by rfl) ⟨10236698, by rfl⟩ : syracuseStep 13648931 = 20473397) B20473397
theorem B6382637 : Blo 1260448 6382637 := bstep (se 3 (by rfl) ⟨1196744, by rfl⟩ : syracuseStep 6382637 = 2393489) B2393489
theorem B1418359 : Blo 1260448 1418359 := bstep (se 1 (by rfl) ⟨1063769, by rfl⟩ : syracuseStep 1418359 = 2127539) B2127539
theorem B1893515 : Blo 1260448 1893515 := bstep (se 1 (by rfl) ⟨1420136, by rfl⟩ : syracuseStep 1893515 = 2840273) B2840273
theorem B2393239 : Blo 1260448 2393239 := bstep (se 1 (by rfl) ⟨1794929, by rfl⟩ : syracuseStep 2393239 = 3589859) B3589859
theorem B11977879 : Blo 1260448 11977879 := bstep (se 1 (by rfl) ⟨8983409, by rfl⟩ : syracuseStep 11977879 = 17966819) B17966819
theorem B1893527 : Blo 1260448 1893527 := bstep (se 1 (by rfl) ⟨1420145, by rfl⟩ : syracuseStep 1893527 = 2840291) B2840291
theorem B1893593 : Blo 1260448 1893593 := bstep (se 2 (by rfl) ⟨710097, by rfl⟩ : syracuseStep 1893593 = 1420195) B1420195
theorem B1418539 : Blo 1260448 1418539 := bstep (se 1 (by rfl) ⟨1063904, by rfl⟩ : syracuseStep 1418539 = 2127809) B2127809
theorem B2393459 : Blo 1260448 2393459 := bstep (se 1 (by rfl) ⟨1795094, by rfl⟩ : syracuseStep 2393459 = 3590189) B3590189
theorem B1295735 : Blo 1260448 1295735 := bstep (se 1 (by rfl) ⟨971801, by rfl⟩ : syracuseStep 1295735 = 1943603) B1943603
theorem B1418647 : Blo 1260448 1418647 := bstep (se 1 (by rfl) ⟨1063985, by rfl⟩ : syracuseStep 1418647 = 2127971) B2127971
theorem B2836043 : Blo 1260448 2836043 := bstep (se 1 (by rfl) ⟨2127032, by rfl⟩ : syracuseStep 2836043 = 4254065) B4254065
theorem B1418827 : Blo 1260448 1418827 := bstep (se 1 (by rfl) ⟨1064120, by rfl⟩ : syracuseStep 1418827 = 2128241) B2128241
theorem B5391947 : Blo 1260448 5391947 := bstep (se 1 (by rfl) ⟨4043960, by rfl⟩ : syracuseStep 5391947 = 8087921) B8087921
theorem B2393687 : Blo 1260448 2393687 := bstep (se 1 (by rfl) ⟨1795265, by rfl⟩ : syracuseStep 2393687 = 3590531) B3590531
theorem B2836097 : Blo 1260448 2836097 := bstep (se 2 (by rfl) ⟨1063536, by rfl⟩ : syracuseStep 2836097 = 2127073) B2127073
theorem B1918603 : Blo 1260448 1918603 := bstep (se 1 (by rfl) ⟨1438952, by rfl⟩ : syracuseStep 1918603 = 2877905) B2877905
theorem B1402519 : Blo 1260448 1402519 := bstep (se 1 (by rfl) ⟨1051889, by rfl⟩ : syracuseStep 1402519 = 2103779) B2103779
theorem B1418935 : Blo 1260448 1418935 := bstep (se 1 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 1418935 = 2128403) B2128403
theorem B2836313 : Blo 1260448 2836313 := bstep (se 2 (by rfl) ⟨1063617, by rfl⟩ : syracuseStep 2836313 = 2127235) B2127235
theorem B2393945 : Blo 1260448 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B1419115 : Blo 1260448 1419115 := bstep (se 1 (by rfl) ⟨1064336, by rfl⟩ : syracuseStep 1419115 = 2128673) B2128673
theorem B2836403 : Blo 1260448 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B2836439 : Blo 1260448 2836439 := bstep (se 1 (by rfl) ⟨2127329, by rfl⟩ : syracuseStep 2836439 = 4254659) B4254659
theorem B1419223 : Blo 1260448 1419223 := bstep (se 1 (by rfl) ⟨1064417, by rfl⟩ : syracuseStep 1419223 = 2128835) B2128835
theorem B2426945 : Blo 1260448 2426945 := bstep (se 2 (by rfl) ⟨910104, by rfl⟩ : syracuseStep 2426945 = 1820209) B1820209
theorem B5752907 : Blo 1260448 5752907 := bstep (se 1 (by rfl) ⟨4314680, by rfl⟩ : syracuseStep 5752907 = 8629361) B8629361
theorem B2836619 : Blo 1260448 2836619 := bstep (se 1 (by rfl) ⟨2127464, by rfl⟩ : syracuseStep 2836619 = 4254929) B4254929
theorem B1419403 : Blo 1260448 1419403 := bstep (se 1 (by rfl) ⟨1064552, by rfl⟩ : syracuseStep 1419403 = 2129105) B2129105
theorem B2836673 : Blo 1260448 2836673 := bstep (se 2 (by rfl) ⟨1063752, by rfl⟩ : syracuseStep 2836673 = 2127505) B2127505
theorem B2394355 : Blo 1260448 2394355 := bstep (se 1 (by rfl) ⟨1795766, by rfl⟩ : syracuseStep 2394355 = 3591533) B3591533
theorem B1419511 : Blo 1260448 1419511 := bstep (se 1 (by rfl) ⟨1064633, by rfl⟩ : syracuseStep 1419511 = 2129267) B2129267
theorem B4548953 : Blo 1260448 4548953 := bstep (se 2 (by rfl) ⟨1705857, by rfl⟩ : syracuseStep 4548953 = 3411715) B3411715
theorem B4041053 : Blo 1260448 4041053 := bstep (se 3 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 4041053 = 1515395) B1515395
theorem B2836889 : Blo 1260448 2836889 := bstep (se 2 (by rfl) ⟨1063833, by rfl⟩ : syracuseStep 2836889 = 2127667) B2127667
theorem B1419691 : Blo 1260448 1419691 := bstep (se 1 (by rfl) ⟨1064768, by rfl⟩ : syracuseStep 1419691 = 2129537) B2129537
theorem B4254173 : Blo 1260448 4254173 := bstep (se 3 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 4254173 = 1595315) B1595315
theorem B2836979 : Blo 1260448 2836979 := bstep (se 1 (by rfl) ⟨2127734, by rfl⟩ : syracuseStep 2836979 = 4255469) B4255469
theorem B2837015 : Blo 1260448 2837015 := bstep (se 1 (by rfl) ⟨2127761, by rfl⟩ : syracuseStep 2837015 = 4255523) B4255523
theorem B1419799 : Blo 1260448 1419799 := bstep (se 1 (by rfl) ⟨1064849, by rfl⟩ : syracuseStep 1419799 = 2129699) B2129699
theorem B10783277 : Blo 1260448 10783277 := bstep (se 3 (by rfl) ⟨2021864, by rfl⟩ : syracuseStep 10783277 = 4043729) B4043729
theorem B7178827 : Blo 1260448 7178827 := bstep (se 1 (by rfl) ⟨5384120, by rfl⟩ : syracuseStep 7178827 = 10768241) B10768241
theorem B1346167 : Blo 1260448 1346167 := bstep (se 1 (by rfl) ⟨1009625, by rfl⟩ : syracuseStep 1346167 = 2019251) B2019251
theorem B7187075 : Blo 1260448 7187075 := bstep (se 1 (by rfl) ⟨5390306, by rfl⟩ : syracuseStep 7187075 = 10780613) B10780613
theorem B2837195 : Blo 1260448 2837195 := bstep (se 1 (by rfl) ⟨2127896, by rfl⟩ : syracuseStep 2837195 = 4255793) B4255793
theorem B1419979 : Blo 1260448 1419979 := bstep (se 1 (by rfl) ⟨1064984, by rfl⟩ : syracuseStep 1419979 = 2129969) B2129969
theorem B2394841 : Blo 1260448 2394841 := bstep (se 2 (by rfl) ⟨898065, by rfl⟩ : syracuseStep 2394841 = 1796131) B1796131
theorem B2837249 : Blo 1260448 2837249 := bstep (se 2 (by rfl) ⟨1063968, by rfl⟩ : syracuseStep 2837249 = 2127937) B2127937
theorem B3590963 : Blo 1260448 3590963 := bstep (se 1 (by rfl) ⟨2693222, by rfl⟩ : syracuseStep 3590963 = 5386445) B5386445
theorem B1420087 : Blo 1260448 1420087 := bstep (se 1 (by rfl) ⟨1065065, by rfl⟩ : syracuseStep 1420087 = 2130131) B2130131
theorem B4787009 : Blo 1260448 4787009 := bstep (se 2 (by rfl) ⟨1795128, by rfl⟩ : syracuseStep 4787009 = 3590257) B3590257
theorem B1796951 : Blo 1260448 1796951 := bstep (se 1 (by rfl) ⟨1347713, by rfl⟩ : syracuseStep 1796951 = 2695427) B2695427
theorem B7179101 : Blo 1260448 7179101 := bstep (se 3 (by rfl) ⟨1346081, by rfl⟩ : syracuseStep 7179101 = 2692163) B2692163
theorem B2837465 : Blo 1260448 2837465 := bstep (se 2 (by rfl) ⟨1064049, by rfl⟩ : syracuseStep 2837465 = 2128099) B2128099
theorem B1346539 : Blo 1260448 1346539 := bstep (se 1 (by rfl) ⟨1009904, by rfl⟩ : syracuseStep 1346539 = 2019809) B2019809
theorem B3591191 : Blo 1260448 3591191 := bstep (se 1 (by rfl) ⟨2693393, by rfl⟩ : syracuseStep 3591191 = 5386787) B5386787
theorem B2837555 : Blo 1260448 2837555 := bstep (se 1 (by rfl) ⟨2128166, by rfl⟩ : syracuseStep 2837555 = 4256333) B4256333
theorem B2837591 : Blo 1260448 2837591 := bstep (se 1 (by rfl) ⟨2128193, by rfl⟩ : syracuseStep 2837591 = 4256387) B4256387
theorem B5115059 : Blo 1260448 5115059 := bstep (se 1 (by rfl) ⟨3836294, by rfl⟩ : syracuseStep 5115059 = 7672589) B7672589
theorem B10783961 : Blo 1260448 10783961 := bstep (se 2 (by rfl) ⟨4043985, by rfl⟩ : syracuseStep 10783961 = 8087971) B8087971
theorem B2428147 : Blo 1260448 2428147 := bstep (se 1 (by rfl) ⟨1821110, by rfl⟩ : syracuseStep 2428147 = 3642221) B3642221
theorem B2837771 : Blo 1260448 2837771 := bstep (se 1 (by rfl) ⟨2128328, by rfl⟩ : syracuseStep 2837771 = 4256657) B4256657
theorem B2395403 : Blo 1260448 2395403 := bstep (se 1 (by rfl) ⟨1796552, by rfl⟩ : syracuseStep 2395403 = 3593105) B3593105
theorem B2837825 : Blo 1260448 2837825 := bstep (se 2 (by rfl) ⟨1064184, by rfl⟩ : syracuseStep 2837825 = 2128369) B2128369
theorem B3591499 : Blo 1260448 3591499 := bstep (se 1 (by rfl) ⟨2693624, by rfl⟩ : syracuseStep 3591499 = 5387249) B5387249
theorem B1346987 : Blo 1260448 1346987 := bstep (se 1 (by rfl) ⟨1010240, by rfl⟩ : syracuseStep 1346987 = 2020481) B2020481
theorem B2493875 : Blo 1260448 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B2395585 : Blo 1260448 2395585 := bstep (se 2 (by rfl) ⟨898344, by rfl⟩ : syracuseStep 2395585 = 1796689) B1796689
theorem B2838041 : Blo 1260448 2838041 := bstep (se 2 (by rfl) ⟨1064265, by rfl⟩ : syracuseStep 2838041 = 2128531) B2128531
theorem B2428481 : Blo 1260448 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B4255307 : Blo 1260448 4255307 := bstep (se 1 (by rfl) ⟨3191480, by rfl⟩ : syracuseStep 4255307 = 6382961) B6382961
theorem B3591773 : Blo 1260448 3591773 := bstep (se 3 (by rfl) ⟨673457, by rfl⟩ : syracuseStep 3591773 = 1346915) B1346915
theorem B2838131 : Blo 1260448 2838131 := bstep (se 1 (by rfl) ⟨2128598, by rfl⟩ : syracuseStep 2838131 = 4257197) B4257197
theorem B2272897 : Blo 1260448 2272897 := bstep (se 2 (by rfl) ⟨852336, by rfl⟩ : syracuseStep 2272897 = 1704673) B1704673
theorem B4607639 : Blo 1260448 4607639 := bstep (se 1 (by rfl) ⟨3455729, by rfl⟩ : syracuseStep 4607639 = 6911459) B6911459
theorem B2838167 : Blo 1260448 2838167 := bstep (se 1 (by rfl) ⟨2128625, by rfl⟩ : syracuseStep 2838167 = 4257251) B4257251
theorem B2879155 : Blo 1260448 2879155 := bstep (se 1 (by rfl) ⟨2159366, by rfl⟩ : syracuseStep 2879155 = 4318733) B4318733
theorem B2019097 : Blo 1260448 2019097 := bstep (se 2 (by rfl) ⟨757161, by rfl⟩ : syracuseStep 2019097 = 1514323) B1514323
theorem B2838347 : Blo 1260448 2838347 := bstep (se 1 (by rfl) ⟨2128760, by rfl⟩ : syracuseStep 2838347 = 4257521) B4257521
theorem B4255577 : Blo 1260448 4255577 := bstep (se 2 (by rfl) ⟨1595841, by rfl⟩ : syracuseStep 4255577 = 3191683) B3191683
theorem B2838401 : Blo 1260448 2838401 := bstep (se 2 (by rfl) ⟨1064400, by rfl⟩ : syracuseStep 2838401 = 2128801) B2128801
theorem B79826867 : Blo 1260448 79826867 := bstep (se 1 (by rfl) ⟨59870150, by rfl⟩ : syracuseStep 79826867 = 119740301) B119740301
theorem B6565811 : Blo 1260448 6565811 := bstep (se 1 (by rfl) ⟨4924358, by rfl⟩ : syracuseStep 6565811 = 9848717) B9848717
theorem B3190873 : Blo 1260448 3190873 := bstep (se 2 (by rfl) ⟨1196577, by rfl⟩ : syracuseStep 3190873 = 2393155) B2393155
theorem B2838617 : Blo 1260448 2838617 := bstep (se 2 (by rfl) ⟨1064481, by rfl⟩ : syracuseStep 2838617 = 2128963) B2128963
theorem B3838045 : Blo 1260448 3838045 := bstep (se 3 (by rfl) ⟨719633, by rfl⟩ : syracuseStep 3838045 = 1439267) B1439267
theorem B2396299 : Blo 1260448 2396299 := bstep (se 1 (by rfl) ⟨1797224, by rfl⟩ : syracuseStep 2396299 = 3594449) B3594449
theorem B2838707 : Blo 1260448 2838707 := bstep (se 1 (by rfl) ⟨2129030, by rfl⟩ : syracuseStep 2838707 = 4258061) B4258061
theorem B2838743 : Blo 1260448 2838743 := bstep (se 1 (by rfl) ⟨2129057, by rfl⟩ : syracuseStep 2838743 = 4258115) B4258115
theorem B2396375 : Blo 1260448 2396375 := bstep (se 1 (by rfl) ⟨1797281, by rfl⟩ : syracuseStep 2396375 = 3594563) B3594563
theorem B5386513 : Blo 1260448 5386513 := bstep (se 2 (by rfl) ⟨2019942, by rfl⟩ : syracuseStep 5386513 = 4039885) B4039885
theorem B4788497 : Blo 1260448 4788497 := bstep (se 2 (by rfl) ⟨1795686, by rfl⟩ : syracuseStep 4788497 = 3591373) B3591373
theorem B2273675 : Blo 1260448 2273675 := bstep (se 1 (by rfl) ⟨1705256, by rfl⟩ : syracuseStep 2273675 = 3410513) B3410513
theorem B2838923 : Blo 1260448 2838923 := bstep (se 1 (by rfl) ⟨2129192, by rfl⟩ : syracuseStep 2838923 = 4258385) B4258385
theorem B2429363 : Blo 1260448 2429363 := bstep (se 1 (by rfl) ⟨1822022, by rfl⟩ : syracuseStep 2429363 = 3644045) B3644045
theorem B2838977 : Blo 1260448 2838977 := bstep (se 2 (by rfl) ⟨1064616, by rfl⟩ : syracuseStep 2838977 = 2129233) B2129233
theorem B4256279 : Blo 1260448 4256279 := bstep (se 1 (by rfl) ⟨3192209, by rfl⟩ : syracuseStep 4256279 = 6384419) B6384419
theorem B2839193 : Blo 1260448 2839193 := bstep (se 2 (by rfl) ⟨1064697, by rfl⟩ : syracuseStep 2839193 = 2129395) B2129395
theorem B4788953 : Blo 1260448 4788953 := bstep (se 2 (by rfl) ⟨1795857, by rfl⟩ : syracuseStep 4788953 = 3591715) B3591715
theorem B2839283 : Blo 1260448 2839283 := bstep (se 1 (by rfl) ⟨2129462, by rfl⟩ : syracuseStep 2839283 = 4258925) B4258925
theorem B2839319 : Blo 1260448 2839319 := bstep (se 1 (by rfl) ⟨2129489, by rfl⟩ : syracuseStep 2839319 = 4258979) B4258979
theorem B2274137 : Blo 1260448 2274137 := bstep (se 2 (by rfl) ⟨852801, by rfl⟩ : syracuseStep 2274137 = 1705603) B1705603
theorem B6386525 : Blo 1260448 6386525 := bstep (se 3 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 6386525 = 2394947) B2394947
theorem B1364855 : Blo 1260448 1364855 := bstep (se 1 (by rfl) ⟨1023641, by rfl⟩ : syracuseStep 1364855 = 2047283) B2047283
theorem B4789165 : Blo 1260448 4789165 := bstep (se 3 (by rfl) ⟨897968, by rfl⟩ : syracuseStep 4789165 = 1795937) B1795937
theorem B9581489 : Blo 1260448 9581489 := bstep (se 2 (by rfl) ⟨3593058, by rfl⟩ : syracuseStep 9581489 = 7186117) B7186117
theorem B2839499 : Blo 1260448 2839499 := bstep (se 1 (by rfl) ⟨2129624, by rfl⟩ : syracuseStep 2839499 = 4259249) B4259249
theorem B2839553 : Blo 1260448 2839553 := bstep (se 2 (by rfl) ⟨1064832, by rfl⟩ : syracuseStep 2839553 = 2129665) B2129665
theorem B16176145 : Blo 1260448 16176145 := bstep (se 2 (by rfl) ⟨6066054, by rfl⟩ : syracuseStep 16176145 = 12132109) B12132109
theorem B7672877 : Blo 1260448 7672877 := bstep (se 3 (by rfl) ⟨1438664, by rfl⟩ : syracuseStep 7672877 = 2877329) B2877329
theorem B4256819 : Blo 1260448 4256819 := bstep (se 1 (by rfl) ⟨3192614, by rfl⟩ : syracuseStep 4256819 = 6385229) B6385229
theorem B1438807 : Blo 1260448 1438807 := bstep (se 1 (by rfl) ⟨1079105, by rfl⟩ : syracuseStep 1438807 = 2158211) B2158211
theorem B3191987 : Blo 1260448 3191987 := bstep (se 1 (by rfl) ⟨2393990, by rfl⟩ : syracuseStep 3191987 = 4787981) B4787981
theorem B2839769 : Blo 1260448 2839769 := bstep (se 2 (by rfl) ⟨1064913, by rfl⟩ : syracuseStep 2839769 = 2129827) B2129827
theorem B4789469 : Blo 1260448 4789469 := bstep (se 3 (by rfl) ⟨898025, by rfl⟩ : syracuseStep 4789469 = 1796051) B1796051
theorem B10229009 : Blo 1260448 10229009 := bstep (se 2 (by rfl) ⟨3835878, by rfl⟩ : syracuseStep 10229009 = 7671757) B7671757
theorem B2127127 : Blo 1260448 2127127 := bstep (se 1 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 2127127 = 3190691) B3190691
theorem B2839859 : Blo 1260448 2839859 := bstep (se 1 (by rfl) ⟨2129894, by rfl⟩ : syracuseStep 2839859 = 4259789) B4259789
theorem B4257089 : Blo 1260448 4257089 := bstep (se 2 (by rfl) ⟨1596408, by rfl⟩ : syracuseStep 4257089 = 3192817) B3192817
theorem B2839895 : Blo 1260448 2839895 := bstep (se 1 (by rfl) ⟨2129921, by rfl⟩ : syracuseStep 2839895 = 4259843) B4259843
theorem B9581975 : Blo 1260448 9581975 := bstep (se 1 (by rfl) ⟨7186481, by rfl⟩ : syracuseStep 9581975 = 14372963) B14372963
theorem B2692531 : Blo 1260448 2692531 := bstep (se 1 (by rfl) ⟨2019398, by rfl⟩ : syracuseStep 2692531 = 4038797) B4038797
theorem B6059443 : Blo 1260448 6059443 := bstep (se 1 (by rfl) ⟨4544582, by rfl⟩ : syracuseStep 6059443 = 9089165) B9089165
theorem B10769881 : Blo 1260448 10769881 := bstep (se 2 (by rfl) ⟨4038705, by rfl⟩ : syracuseStep 10769881 = 8077411) B8077411
theorem B3192281 : Blo 1260448 3192281 := bstep (se 2 (by rfl) ⟨1197105, by rfl⟩ : syracuseStep 3192281 = 2394211) B2394211
theorem B2840075 : Blo 1260448 2840075 := bstep (se 1 (by rfl) ⟨2130056, by rfl⟩ : syracuseStep 2840075 = 4260113) B4260113
theorem B2840129 : Blo 1260448 2840129 := bstep (se 2 (by rfl) ⟨1065048, by rfl⟩ : syracuseStep 2840129 = 2130097) B2130097
theorem B18183811 : Blo 1260448 18183811 := bstep (se 1 (by rfl) ⟨13637858, by rfl⟩ : syracuseStep 18183811 = 27275717) B27275717
theorem B1365643 : Blo 1260448 1365643 := bstep (se 1 (by rfl) ⟨1024232, by rfl⟩ : syracuseStep 1365643 = 2048465) B2048465
theorem B3593879 : Blo 1260448 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B4314845 : Blo 1260448 4314845 := bstep (se 3 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 4314845 = 1618067) B1618067
theorem B10368773 : Blo 1260448 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B2840345 : Blo 1260448 2840345 := bstep (se 2 (by rfl) ⟨1065129, by rfl⟩ : syracuseStep 2840345 = 2130259) B2130259
theorem B4257629 : Blo 1260448 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B2840435 : Blo 1260448 2840435 := bstep (se 1 (by rfl) ⟨2130326, by rfl⟩ : syracuseStep 2840435 = 4260653) B4260653
theorem B13645685 : Blo 1260448 13645685 := bstep (se 5 (by rfl) ⟨639641, by rfl⟩ : syracuseStep 13645685 = 1279283) B1279283
theorem B2127755 : Blo 1260448 2127755 := bstep (se 1 (by rfl) ⟨1595816, by rfl⟩ : syracuseStep 2127755 = 3191633) B3191633
theorem B2840471 : Blo 1260448 2840471 := bstep (se 1 (by rfl) ⟨2130353, by rfl⟩ : syracuseStep 2840471 = 4260707) B4260707
theorem B2693017 : Blo 1260448 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B15333299 : Blo 1260448 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B4610009 : Blo 1260448 4610009 := bstep (se 2 (by rfl) ⟨1728753, by rfl⟩ : syracuseStep 4610009 = 3457507) B3457507
theorem B10778629 : Blo 1260448 10778629 := bstep (se 4 (by rfl) ⟨1010496, by rfl⟩ : syracuseStep 10778629 = 2020993) B2020993
theorem B2127883 : Blo 1260448 2127883 := bstep (se 1 (by rfl) ⟨1595912, by rfl⟩ : syracuseStep 2127883 = 3191825) B3191825
theorem B7280705 : Blo 1260448 7280705 := bstep (se 2 (by rfl) ⟨2730264, by rfl⟩ : syracuseStep 7280705 = 5460529) B5460529
theorem B1595467 : Blo 1260448 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B30693451 : Blo 1260448 30693451 := bstep (se 1 (by rfl) ⟨23020088, by rfl⟩ : syracuseStep 30693451 = 46040177) B46040177
theorem B40941719 : Blo 1260448 40941719 := bstep (se 1 (by rfl) ⟨30706289, by rfl⟩ : syracuseStep 40941719 = 61412579) B61412579
theorem B2128025 : Blo 1260448 2128025 := bstep (se 2 (by rfl) ⟨798009, by rfl⟩ : syracuseStep 2128025 = 1596019) B1596019
theorem B2128153 : Blo 1260448 2128153 := bstep (se 2 (by rfl) ⟨798057, by rfl⟩ : syracuseStep 2128153 = 1596115) B1596115
theorem B10770839 : Blo 1260448 10770839 := bstep (se 1 (by rfl) ⟨8078129, by rfl⟩ : syracuseStep 10770839 = 16156259) B16156259
theorem B1890713 : Blo 1260448 1890713 := bstep (se 2 (by rfl) ⟨709017, by rfl⟩ : syracuseStep 1890713 = 1418035) B1418035
theorem B3594689 : Blo 1260448 3594689 := bstep (se 2 (by rfl) ⟨1348008, by rfl⟩ : syracuseStep 3594689 = 2696017) B2696017
theorem B1890827 : Blo 1260448 1890827 := bstep (se 1 (by rfl) ⟨1418120, by rfl⟩ : syracuseStep 1890827 = 2836241) B2836241
theorem B1890839 : Blo 1260448 1890839 := bstep (se 1 (by rfl) ⟨1418129, by rfl⟩ : syracuseStep 1890839 = 2836259) B2836259
theorem B1890905 : Blo 1260448 1890905 := bstep (se 2 (by rfl) ⟨709089, by rfl⟩ : syracuseStep 1890905 = 1418179) B1418179
theorem B5388889 : Blo 1260448 5388889 := bstep (se 2 (by rfl) ⟨2020833, by rfl⟩ : syracuseStep 5388889 = 4041667) B4041667
theorem B1891019 : Blo 1260448 1891019 := bstep (se 1 (by rfl) ⟨1418264, by rfl⟩ : syracuseStep 1891019 = 2836529) B2836529
theorem B1891031 : Blo 1260448 1891031 := bstep (se 1 (by rfl) ⟨1418273, by rfl⟩ : syracuseStep 1891031 = 2836547) B2836547
theorem B10771217 : Blo 1260448 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B2022167 : Blo 1260448 2022167 := bstep (se 1 (by rfl) ⟨1516625, by rfl⟩ : syracuseStep 2022167 = 3033251) B3033251
theorem B1891097 : Blo 1260448 1891097 := bstep (se 2 (by rfl) ⟨709161, by rfl⟩ : syracuseStep 1891097 = 1418323) B1418323
theorem B2128727 : Blo 1260448 2128727 := bstep (se 1 (by rfl) ⟨1596545, by rfl⟩ : syracuseStep 2128727 = 3193091) B3193091
theorem B1891211 : Blo 1260448 1891211 := bstep (se 1 (by rfl) ⟨1418408, by rfl⟩ : syracuseStep 1891211 = 2836817) B2836817
theorem B1891223 : Blo 1260448 1891223 := bstep (se 1 (by rfl) ⟨1418417, by rfl⟩ : syracuseStep 1891223 = 2836835) B2836835
theorem B6388631 : Blo 1260448 6388631 := bstep (se 1 (by rfl) ⟨4791473, by rfl⟩ : syracuseStep 6388631 = 9582947) B9582947
theorem B1260459 : Blo 1260448 1260459 := bstep (se 1 (by rfl) ⟨945344, by rfl⟩ : syracuseStep 1260459 = 1890689) B1890689
theorem B1260471 : Blo 1260448 1260471 := bstep (se 1 (by rfl) ⟨945353, by rfl⟩ : syracuseStep 1260471 = 1890707) B1890707
theorem B1260491 : Blo 1260448 1260491 := bstep (se 1 (by rfl) ⟨945368, by rfl⟩ : syracuseStep 1260491 = 1890737) B1890737
theorem B4258763 : Blo 1260448 4258763 := bstep (se 1 (by rfl) ⟨3194072, by rfl⟩ : syracuseStep 4258763 = 6388145) B6388145
theorem B1260503 : Blo 1260448 1260503 := bstep (se 1 (by rfl) ⟨945377, by rfl⟩ : syracuseStep 1260503 = 1890755) B1890755
theorem B2128855 : Blo 1260448 2128855 := bstep (se 1 (by rfl) ⟨1596641, by rfl⟩ : syracuseStep 2128855 = 3193283) B3193283
theorem B1891289 : Blo 1260448 1891289 := bstep (se 2 (by rfl) ⟨709233, by rfl⟩ : syracuseStep 1891289 = 1418467) B1418467
theorem B1260523 : Blo 1260448 1260523 := bstep (se 1 (by rfl) ⟨945392, by rfl⟩ : syracuseStep 1260523 = 1890785) B1890785
theorem B1260535 : Blo 1260448 1260535 := bstep (se 1 (by rfl) ⟨945401, by rfl⟩ : syracuseStep 1260535 = 1890803) B1890803
theorem B1260555 : Blo 1260448 1260555 := bstep (se 1 (by rfl) ⟨945416, by rfl⟩ : syracuseStep 1260555 = 1890833) B1890833
theorem B1260567 : Blo 1260448 1260567 := bstep (se 1 (by rfl) ⟨945425, by rfl⟩ : syracuseStep 1260567 = 1890851) B1890851
theorem B1596439 : Blo 1260448 1596439 := bstep (se 1 (by rfl) ⟨1197329, by rfl⟩ : syracuseStep 1596439 = 2394659) B2394659
theorem B1260587 : Blo 1260448 1260587 := bstep (se 1 (by rfl) ⟨945440, by rfl⟩ : syracuseStep 1260587 = 1890881) B1890881
theorem B1260599 : Blo 1260448 1260599 := bstep (se 1 (by rfl) ⟨945449, by rfl⟩ : syracuseStep 1260599 = 1890899) B1890899
theorem B1260619 : Blo 1260448 1260619 := bstep (se 1 (by rfl) ⟨945464, by rfl⟩ : syracuseStep 1260619 = 1890929) B1890929
theorem B1891403 : Blo 1260448 1891403 := bstep (se 1 (by rfl) ⟨1418552, by rfl⟩ : syracuseStep 1891403 = 2837105) B2837105
theorem B3193931 : Blo 1260448 3193931 := bstep (se 1 (by rfl) ⟨2395448, by rfl⟩ : syracuseStep 3193931 = 4790897) B4790897
theorem B1260631 : Blo 1260448 1260631 := bstep (se 1 (by rfl) ⟨945473, by rfl⟩ : syracuseStep 1260631 = 1890947) B1890947
theorem B1891415 : Blo 1260448 1891415 := bstep (se 1 (by rfl) ⟨1418561, by rfl⟩ : syracuseStep 1891415 = 2837123) B2837123
theorem B1260651 : Blo 1260448 1260651 := bstep (se 1 (by rfl) ⟨945488, by rfl⟩ : syracuseStep 1260651 = 1890977) B1890977
theorem B1260663 : Blo 1260448 1260663 := bstep (se 1 (by rfl) ⟨945497, by rfl⟩ : syracuseStep 1260663 = 1890995) B1890995
theorem B1260683 : Blo 1260448 1260683 := bstep (se 1 (by rfl) ⟨945512, by rfl⟩ : syracuseStep 1260683 = 1891025) B1891025
theorem B1260695 : Blo 1260448 1260695 := bstep (se 1 (by rfl) ⟨945521, by rfl⟩ : syracuseStep 1260695 = 1891043) B1891043
theorem B1891481 : Blo 1260448 1891481 := bstep (se 2 (by rfl) ⟨709305, by rfl⟩ : syracuseStep 1891481 = 1418611) B1418611
theorem B1260715 : Blo 1260448 1260715 := bstep (se 1 (by rfl) ⟨945536, by rfl⟩ : syracuseStep 1260715 = 1891073) B1891073
theorem B1260727 : Blo 1260448 1260727 := bstep (se 1 (by rfl) ⟨945545, by rfl⟩ : syracuseStep 1260727 = 1891091) B1891091
theorem B1260747 : Blo 1260448 1260747 := bstep (se 1 (by rfl) ⟨945560, by rfl⟩ : syracuseStep 1260747 = 1891121) B1891121
theorem B1260759 : Blo 1260448 1260759 := bstep (se 1 (by rfl) ⟨945569, by rfl⟩ : syracuseStep 1260759 = 1891139) B1891139
theorem B4259033 : Blo 1260448 4259033 := bstep (se 2 (by rfl) ⟨1597137, by rfl⟩ : syracuseStep 4259033 = 3194275) B3194275
theorem B1260779 : Blo 1260448 1260779 := bstep (se 1 (by rfl) ⟨945584, by rfl⟩ : syracuseStep 1260779 = 1891169) B1891169
theorem B1260791 : Blo 1260448 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B20446469 : Blo 1260448 20446469 := bstep (se 4 (by rfl) ⟨1916856, by rfl⟩ : syracuseStep 20446469 = 3833713) B3833713
theorem B1260811 : Blo 1260448 1260811 := bstep (se 1 (by rfl) ⟨945608, by rfl⟩ : syracuseStep 1260811 = 1891217) B1891217
theorem B1891595 : Blo 1260448 1891595 := bstep (se 1 (by rfl) ⟨1418696, by rfl⟩ : syracuseStep 1891595 = 2837393) B2837393
theorem B1260823 : Blo 1260448 1260823 := bstep (se 1 (by rfl) ⟨945617, by rfl⟩ : syracuseStep 1260823 = 1891235) B1891235
theorem B1891607 : Blo 1260448 1891607 := bstep (se 1 (by rfl) ⟨1418705, by rfl⟩ : syracuseStep 1891607 = 2837411) B2837411
theorem B1260843 : Blo 1260448 1260843 := bstep (se 1 (by rfl) ⟨945632, by rfl⟩ : syracuseStep 1260843 = 1891265) B1891265
theorem B1260855 : Blo 1260448 1260855 := bstep (se 1 (by rfl) ⟨945641, by rfl⟩ : syracuseStep 1260855 = 1891283) B1891283
theorem B1260875 : Blo 1260448 1260875 := bstep (se 1 (by rfl) ⟨945656, by rfl⟩ : syracuseStep 1260875 = 1891313) B1891313
theorem B1260887 : Blo 1260448 1260887 := bstep (se 1 (by rfl) ⟨945665, by rfl⟩ : syracuseStep 1260887 = 1891331) B1891331
theorem B2694487 : Blo 1260448 2694487 := bstep (se 1 (by rfl) ⟨2020865, by rfl⟩ : syracuseStep 2694487 = 4041731) B4041731
theorem B1891673 : Blo 1260448 1891673 := bstep (se 2 (by rfl) ⟨709377, by rfl⟩ : syracuseStep 1891673 = 1418755) B1418755
theorem B1260907 : Blo 1260448 1260907 := bstep (se 1 (by rfl) ⟨945680, by rfl⟩ : syracuseStep 1260907 = 1891361) B1891361
theorem B1260919 : Blo 1260448 1260919 := bstep (se 1 (by rfl) ⟨945689, by rfl⟩ : syracuseStep 1260919 = 1891379) B1891379
theorem B1260939 : Blo 1260448 1260939 := bstep (se 1 (by rfl) ⟨945704, by rfl⟩ : syracuseStep 1260939 = 1891409) B1891409
theorem B103497101 : Blo 1260448 103497101 := bstep (se 3 (by rfl) ⟨19405706, by rfl⟩ : syracuseStep 103497101 = 38811413) B38811413
theorem B2694539 : Blo 1260448 2694539 := bstep (se 1 (by rfl) ⟨2020904, by rfl⟩ : syracuseStep 2694539 = 4041809) B4041809
theorem B1260951 : Blo 1260448 1260951 := bstep (se 1 (by rfl) ⟨945713, by rfl⟩ : syracuseStep 1260951 = 1891427) B1891427
theorem B1260971 : Blo 1260448 1260971 := bstep (se 1 (by rfl) ⟨945728, by rfl⟩ : syracuseStep 1260971 = 1891457) B1891457
theorem B1260983 : Blo 1260448 1260983 := bstep (se 1 (by rfl) ⟨945737, by rfl⟩ : syracuseStep 1260983 = 1891475) B1891475
theorem B1261003 : Blo 1260448 1261003 := bstep (se 1 (by rfl) ⟨945752, by rfl⟩ : syracuseStep 1261003 = 1891505) B1891505
theorem B1891787 : Blo 1260448 1891787 := bstep (se 1 (by rfl) ⟨1418840, by rfl⟩ : syracuseStep 1891787 = 2837681) B2837681
theorem B1261015 : Blo 1260448 1261015 := bstep (se 1 (by rfl) ⟨945761, by rfl⟩ : syracuseStep 1261015 = 1891523) B1891523
theorem B1891799 : Blo 1260448 1891799 := bstep (se 1 (by rfl) ⟨1418849, by rfl⟩ : syracuseStep 1891799 = 2837699) B2837699
theorem B46005731 : Blo 1260448 46005731 := bstep (se 1 (by rfl) ⟨34504298, by rfl⟩ : syracuseStep 46005731 = 69008597) B69008597
theorem B1261035 : Blo 1260448 1261035 := bstep (se 1 (by rfl) ⟨945776, by rfl⟩ : syracuseStep 1261035 = 1891553) B1891553
theorem B1261047 : Blo 1260448 1261047 := bstep (se 1 (by rfl) ⟨945785, by rfl⟩ : syracuseStep 1261047 = 1891571) B1891571
theorem B1261067 : Blo 1260448 1261067 := bstep (se 1 (by rfl) ⟨945800, by rfl⟩ : syracuseStep 1261067 = 1891601) B1891601
theorem B1261079 : Blo 1260448 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B5389847 : Blo 1260448 5389847 := bstep (se 1 (by rfl) ⟨4042385, by rfl⟩ : syracuseStep 5389847 = 8084771) B8084771
theorem B1891865 : Blo 1260448 1891865 := bstep (se 2 (by rfl) ⟨709449, by rfl⟩ : syracuseStep 1891865 = 1418899) B1418899
theorem B1261099 : Blo 1260448 1261099 := bstep (se 1 (by rfl) ⟨945824, by rfl⟩ : syracuseStep 1261099 = 1891649) B1891649
theorem B1261111 : Blo 1260448 1261111 := bstep (se 1 (by rfl) ⟨945833, by rfl⟩ : syracuseStep 1261111 = 1891667) B1891667
theorem B1261131 : Blo 1260448 1261131 := bstep (se 1 (by rfl) ⟨945848, by rfl⟩ : syracuseStep 1261131 = 1891697) B1891697
theorem B2129483 : Blo 1260448 2129483 := bstep (se 1 (by rfl) ⟨1597112, by rfl⟩ : syracuseStep 2129483 = 3194225) B3194225
theorem B2555479 : Blo 1260448 2555479 := bstep (se 1 (by rfl) ⟨1916609, by rfl⟩ : syracuseStep 2555479 = 3833219) B3833219
theorem B1261143 : Blo 1260448 1261143 := bstep (se 1 (by rfl) ⟨945857, by rfl⟩ : syracuseStep 1261143 = 1891715) B1891715
theorem B4988509 : Blo 1260448 4988509 := bstep (se 3 (by rfl) ⟨935345, by rfl⟩ : syracuseStep 4988509 = 1870691) B1870691
theorem B3456605 : Blo 1260448 3456605 := bstep (se 3 (by rfl) ⟨648113, by rfl⟩ : syracuseStep 3456605 = 1296227) B1296227
theorem B1261163 : Blo 1260448 1261163 := bstep (se 1 (by rfl) ⟨945872, by rfl⟩ : syracuseStep 1261163 = 1891745) B1891745
theorem B1261175 : Blo 1260448 1261175 := bstep (se 1 (by rfl) ⟨945881, by rfl⟩ : syracuseStep 1261175 = 1891763) B1891763
theorem B1261195 : Blo 1260448 1261195 := bstep (se 1 (by rfl) ⟨945896, by rfl⟩ : syracuseStep 1261195 = 1891793) B1891793
theorem B1891979 : Blo 1260448 1891979 := bstep (se 1 (by rfl) ⟨1418984, by rfl⟩ : syracuseStep 1891979 = 2837969) B2837969
theorem B2555543 : Blo 1260448 2555543 := bstep (se 1 (by rfl) ⟨1916657, by rfl⟩ : syracuseStep 2555543 = 3833315) B3833315
theorem B1261207 : Blo 1260448 1261207 := bstep (se 1 (by rfl) ⟨945905, by rfl⟩ : syracuseStep 1261207 = 1891811) B1891811
theorem B1891991 : Blo 1260448 1891991 := bstep (se 1 (by rfl) ⟨1418993, by rfl⟩ : syracuseStep 1891991 = 2837987) B2837987
theorem B1261227 : Blo 1260448 1261227 := bstep (se 1 (by rfl) ⟨945920, by rfl⟩ : syracuseStep 1261227 = 1891841) B1891841
theorem B1261239 : Blo 1260448 1261239 := bstep (se 1 (by rfl) ⟨945929, by rfl⟩ : syracuseStep 1261239 = 1891859) B1891859
theorem B1261259 : Blo 1260448 1261259 := bstep (se 1 (by rfl) ⟨945944, by rfl⟩ : syracuseStep 1261259 = 1891889) B1891889
theorem B2129611 : Blo 1260448 2129611 := bstep (se 1 (by rfl) ⟨1597208, by rfl⟩ : syracuseStep 2129611 = 3194417) B3194417
theorem B1261271 : Blo 1260448 1261271 := bstep (se 1 (by rfl) ⟨945953, by rfl⟩ : syracuseStep 1261271 = 1891907) B1891907
theorem B1892057 : Blo 1260448 1892057 := bstep (se 2 (by rfl) ⟨709521, by rfl⟩ : syracuseStep 1892057 = 1419043) B1419043
theorem B1261291 : Blo 1260448 1261291 := bstep (se 1 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 1261291 = 1891937) B1891937
theorem B1261303 : Blo 1260448 1261303 := bstep (se 1 (by rfl) ⟨945977, by rfl⟩ : syracuseStep 1261303 = 1891955) B1891955
theorem B4792067 : Blo 1260448 4792067 := bstep (se 1 (by rfl) ⟨3594050, by rfl⟩ : syracuseStep 4792067 = 7188101) B7188101
theorem B1261323 : Blo 1260448 1261323 := bstep (se 1 (by rfl) ⟨945992, by rfl⟩ : syracuseStep 1261323 = 1891985) B1891985
theorem B4792081 : Blo 1260448 4792081 := bstep (se 2 (by rfl) ⟨1797030, by rfl⟩ : syracuseStep 4792081 = 3594061) B3594061
theorem B1261335 : Blo 1260448 1261335 := bstep (se 1 (by rfl) ⟨946001, by rfl⟩ : syracuseStep 1261335 = 1892003) B1892003
theorem B1261355 : Blo 1260448 1261355 := bstep (se 1 (by rfl) ⟨946016, by rfl⟩ : syracuseStep 1261355 = 1892033) B1892033
theorem B1261367 : Blo 1260448 1261367 := bstep (se 1 (by rfl) ⟨946025, by rfl⟩ : syracuseStep 1261367 = 1892051) B1892051
theorem B1261387 : Blo 1260448 1261387 := bstep (se 1 (by rfl) ⟨946040, by rfl⟩ : syracuseStep 1261387 = 1892081) B1892081
theorem B1892171 : Blo 1260448 1892171 := bstep (se 1 (by rfl) ⟨1419128, by rfl⟩ : syracuseStep 1892171 = 2838257) B2838257
theorem B1597259 : Blo 1260448 1597259 := bstep (se 1 (by rfl) ⟨1197944, by rfl⟩ : syracuseStep 1597259 = 2395889) B2395889
theorem B1261399 : Blo 1260448 1261399 := bstep (se 1 (by rfl) ⟨946049, by rfl⟩ : syracuseStep 1261399 = 1892099) B1892099
theorem B1892183 : Blo 1260448 1892183 := bstep (se 1 (by rfl) ⟨1419137, by rfl⟩ : syracuseStep 1892183 = 2838275) B2838275
theorem B3235673 : Blo 1260448 3235673 := bstep (se 2 (by rfl) ⟨1213377, by rfl⟩ : syracuseStep 3235673 = 2426755) B2426755
theorem B2129753 : Blo 1260448 2129753 := bstep (se 2 (by rfl) ⟨798657, by rfl⟩ : syracuseStep 2129753 = 1597315) B1597315
theorem B1261419 : Blo 1260448 1261419 := bstep (se 1 (by rfl) ⟨946064, by rfl⟩ : syracuseStep 1261419 = 1892129) B1892129
theorem B1261431 : Blo 1260448 1261431 := bstep (se 1 (by rfl) ⟨946073, by rfl⟩ : syracuseStep 1261431 = 1892147) B1892147
theorem B1261451 : Blo 1260448 1261451 := bstep (se 1 (by rfl) ⟨946088, by rfl⟩ : syracuseStep 1261451 = 1892177) B1892177
theorem B1261463 : Blo 1260448 1261463 := bstep (se 1 (by rfl) ⟨946097, by rfl⟩ : syracuseStep 1261463 = 1892195) B1892195
theorem B4259735 : Blo 1260448 4259735 := bstep (se 1 (by rfl) ⟨3194801, by rfl⟩ : syracuseStep 4259735 = 6389603) B6389603
theorem B1892249 : Blo 1260448 1892249 := bstep (se 2 (by rfl) ⟨709593, by rfl⟩ : syracuseStep 1892249 = 1419187) B1419187
theorem B1261483 : Blo 1260448 1261483 := bstep (se 1 (by rfl) ⟨946112, by rfl⟩ : syracuseStep 1261483 = 1892225) B1892225
theorem B12115889 : Blo 1260448 12115889 := bstep (se 2 (by rfl) ⟨4543458, by rfl⟩ : syracuseStep 12115889 = 9086917) B9086917
theorem B1261495 : Blo 1260448 1261495 := bstep (se 1 (by rfl) ⟨946121, by rfl⟩ : syracuseStep 1261495 = 1892243) B1892243
theorem B1261515 : Blo 1260448 1261515 := bstep (se 1 (by rfl) ⟨946136, by rfl⟩ : syracuseStep 1261515 = 1892273) B1892273
theorem B1261527 : Blo 1260448 1261527 := bstep (se 1 (by rfl) ⟨946145, by rfl⟩ : syracuseStep 1261527 = 1892291) B1892291
theorem B2129881 : Blo 1260448 2129881 := bstep (se 2 (by rfl) ⟨798705, by rfl⟩ : syracuseStep 2129881 = 1597411) B1597411
theorem B1261547 : Blo 1260448 1261547 := bstep (se 1 (by rfl) ⟨946160, by rfl⟩ : syracuseStep 1261547 = 1892321) B1892321
theorem B1261559 : Blo 1260448 1261559 := bstep (se 1 (by rfl) ⟨946169, by rfl⟩ : syracuseStep 1261559 = 1892339) B1892339
theorem B1261575 : Blo 1260448 1261575 := bstep (se 1 (by rfl) ⟨946181, by rfl⟩ : syracuseStep 1261575 = 1892363) B1892363
theorem B5537803 : Blo 1260448 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B1261583 : Blo 1260448 1261583 := bstep (se 1 (by rfl) ⟨946187, by rfl⟩ : syracuseStep 1261583 = 1892375) B1892375
theorem B2129935 : Blo 1260448 2129935 := bstep (se 1 (by rfl) ⟨1597451, by rfl⟩ : syracuseStep 2129935 = 3194903) B3194903
theorem B3194923 : Blo 1260448 3194923 := bstep (se 1 (by rfl) ⟨2396192, by rfl⟩ : syracuseStep 3194923 = 4792385) B4792385
theorem B1892411 : Blo 1260448 1892411 := bstep (se 1 (by rfl) ⟨1419308, by rfl⟩ : syracuseStep 1892411 = 2838617) B2838617
theorem B1261627 : Blo 1260448 1261627 := bstep (se 1 (by rfl) ⟨946220, by rfl⟩ : syracuseStep 1261627 = 1892441) B1892441
theorem B1892471 : Blo 1260448 1892471 := bstep (se 1 (by rfl) ⟨1419353, by rfl⟩ : syracuseStep 1892471 = 2838707) B2838707
theorem B3031175 : Blo 1260448 3031175 := bstep (se 1 (by rfl) ⟨2273381, by rfl⟩ : syracuseStep 3031175 = 4546763) B4546763
theorem B1261703 : Blo 1260448 1261703 := bstep (se 1 (by rfl) ⟨946277, by rfl⟩ : syracuseStep 1261703 = 1892555) B1892555
theorem B1892495 : Blo 1260448 1892495 := bstep (se 1 (by rfl) ⟨1419371, by rfl⟩ : syracuseStep 1892495 = 2838743) B2838743
theorem B1261711 : Blo 1260448 1261711 := bstep (se 1 (by rfl) ⟨946283, by rfl⟩ : syracuseStep 1261711 = 1892567) B1892567
theorem B1597583 : Blo 1260448 1597583 := bstep (se 1 (by rfl) ⟨1198187, by rfl⟩ : syracuseStep 1597583 = 2396375) B2396375
theorem B1892537 : Blo 1260448 1892537 := bstep (se 2 (by rfl) ⟨709701, by rfl⟩ : syracuseStep 1892537 = 1419403) B1419403
theorem B3195065 : Blo 1260448 3195065 := bstep (se 2 (by rfl) ⟨1198149, by rfl⟩ : syracuseStep 3195065 = 2396299) B2396299
theorem B1261755 : Blo 1260448 1261755 := bstep (se 1 (by rfl) ⟨946316, by rfl⟩ : syracuseStep 1261755 = 1892633) B1892633
theorem B1892615 : Blo 1260448 1892615 := bstep (se 1 (by rfl) ⟨1419461, by rfl⟩ : syracuseStep 1892615 = 2838923) B2838923
theorem B1261831 : Blo 1260448 1261831 := bstep (se 1 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 1261831 = 1892747) B1892747
theorem B1261839 : Blo 1260448 1261839 := bstep (se 1 (by rfl) ⟨946379, by rfl⟩ : syracuseStep 1261839 = 1892759) B1892759
theorem B1892651 : Blo 1260448 1892651 := bstep (se 1 (by rfl) ⟨1419488, by rfl⟩ : syracuseStep 1892651 = 2838977) B2838977
theorem B1261883 : Blo 1260448 1261883 := bstep (se 1 (by rfl) ⟨946412, by rfl⟩ : syracuseStep 1261883 = 1892825) B1892825
theorem B1892681 : Blo 1260448 1892681 := bstep (se 2 (by rfl) ⟨709755, by rfl⟩ : syracuseStep 1892681 = 1419511) B1419511
theorem B1261959 : Blo 1260448 1261959 := bstep (se 1 (by rfl) ⟨946469, by rfl⟩ : syracuseStep 1261959 = 1892939) B1892939
theorem B1261967 : Blo 1260448 1261967 := bstep (se 1 (by rfl) ⟨946475, by rfl⟩ : syracuseStep 1261967 = 1892951) B1892951
theorem B1892795 : Blo 1260448 1892795 := bstep (se 1 (by rfl) ⟨1419596, by rfl⟩ : syracuseStep 1892795 = 2839193) B2839193
theorem B1262011 : Blo 1260448 1262011 := bstep (se 1 (by rfl) ⟨946508, by rfl⟩ : syracuseStep 1262011 = 1893017) B1893017
theorem B1892855 : Blo 1260448 1892855 := bstep (se 1 (by rfl) ⟨1419641, by rfl⟩ : syracuseStep 1892855 = 2839283) B2839283
theorem B1262087 : Blo 1260448 1262087 := bstep (se 1 (by rfl) ⟨946565, by rfl⟩ : syracuseStep 1262087 = 1893131) B1893131
theorem B1892879 : Blo 1260448 1892879 := bstep (se 1 (by rfl) ⟨1419659, by rfl⟩ : syracuseStep 1892879 = 2839319) B2839319
theorem B1262095 : Blo 1260448 1262095 := bstep (se 1 (by rfl) ⟨946571, by rfl⟩ : syracuseStep 1262095 = 1893143) B1893143
theorem B1892921 : Blo 1260448 1892921 := bstep (se 2 (by rfl) ⟨709845, by rfl⟩ : syracuseStep 1892921 = 1419691) B1419691
theorem B1516091 : Blo 1260448 1516091 := bstep (se 1 (by rfl) ⟨1137068, by rfl⟩ : syracuseStep 1516091 = 2274137) B2274137
theorem B1262139 : Blo 1260448 1262139 := bstep (se 1 (by rfl) ⟨946604, by rfl⟩ : syracuseStep 1262139 = 1893209) B1893209
theorem B1892999 : Blo 1260448 1892999 := bstep (se 1 (by rfl) ⟨1419749, by rfl⟩ : syracuseStep 1892999 = 2839499) B2839499
theorem B1262215 : Blo 1260448 1262215 := bstep (se 1 (by rfl) ⟨946661, by rfl⟩ : syracuseStep 1262215 = 1893323) B1893323
theorem B1262223 : Blo 1260448 1262223 := bstep (se 1 (by rfl) ⟨946667, by rfl⟩ : syracuseStep 1262223 = 1893335) B1893335
theorem B1893035 : Blo 1260448 1893035 := bstep (se 1 (by rfl) ⟨1419776, by rfl⟩ : syracuseStep 1893035 = 2839553) B2839553
theorem B3194711 : Blo 1260448 3194711 := bstep (se 1 (by rfl) ⟨2396033, by rfl⟩ : syracuseStep 3194711 = 4792067) B4792067
theorem B25887413 : Blo 1260448 25887413 := bstep (se 5 (by rfl) ⟨1213472, by rfl⟩ : syracuseStep 25887413 = 2426945) B2426945
theorem B1262267 : Blo 1260448 1262267 := bstep (se 1 (by rfl) ⟨946700, by rfl⟩ : syracuseStep 1262267 = 1893401) B1893401
theorem B1893065 : Blo 1260448 1893065 := bstep (se 2 (by rfl) ⟨709899, by rfl⟩ : syracuseStep 1893065 = 1419799) B1419799
theorem B7283429 : Blo 1260448 7283429 := bstep (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) B1365643
theorem B1262343 : Blo 1260448 1262343 := bstep (se 1 (by rfl) ⟨946757, by rfl⟩ : syracuseStep 1262343 = 1893515) B1893515
theorem B1262351 : Blo 1260448 1262351 := bstep (se 1 (by rfl) ⟨946763, by rfl⟩ : syracuseStep 1262351 = 1893527) B1893527
theorem B7185185 : Blo 1260448 7185185 := bstep (se 2 (by rfl) ⟨2694444, by rfl⟩ : syracuseStep 7185185 = 5388889) B5388889
theorem B1893179 : Blo 1260448 1893179 := bstep (se 1 (by rfl) ⟨1419884, by rfl⟩ : syracuseStep 1893179 = 2839769) B2839769
theorem B1262395 : Blo 1260448 1262395 := bstep (se 1 (by rfl) ⟨946796, by rfl⟩ : syracuseStep 1262395 = 1893593) B1893593
theorem B1794889 : Blo 1260448 1794889 := bstep (se 2 (by rfl) ⟨673083, by rfl⟩ : syracuseStep 1794889 = 1346167) B1346167
theorem B1893239 : Blo 1260448 1893239 := bstep (se 1 (by rfl) ⟨1419929, by rfl⟩ : syracuseStep 1893239 = 2839859) B2839859
theorem B1893263 : Blo 1260448 1893263 := bstep (se 1 (by rfl) ⟨1419947, by rfl⟩ : syracuseStep 1893263 = 2839895) B2839895
theorem B4260761 : Blo 1260448 4260761 := bstep (se 2 (by rfl) ⟨1597785, by rfl⟩ : syracuseStep 4260761 = 3195571) B3195571
theorem B1893305 : Blo 1260448 1893305 := bstep (se 2 (by rfl) ⟨709989, by rfl⟩ : syracuseStep 1893305 = 1419979) B1419979
theorem B5112785 : Blo 1260448 5112785 := bstep (se 2 (by rfl) ⟨1917294, by rfl⟩ : syracuseStep 5112785 = 3834589) B3834589
theorem B6390737 : Blo 1260448 6390737 := bstep (se 2 (by rfl) ⟨2396526, by rfl⟩ : syracuseStep 6390737 = 4793053) B4793053
theorem B1893383 : Blo 1260448 1893383 := bstep (se 1 (by rfl) ⟨1420037, by rfl⟩ : syracuseStep 1893383 = 2840075) B2840075
theorem B1893419 : Blo 1260448 1893419 := bstep (se 1 (by rfl) ⟨1420064, by rfl⟩ : syracuseStep 1893419 = 2840129) B2840129
theorem B1893449 : Blo 1260448 1893449 := bstep (se 2 (by rfl) ⟨710043, by rfl⟩ : syracuseStep 1893449 = 1420087) B1420087
theorem B2876563 : Blo 1260448 2876563 := bstep (se 1 (by rfl) ⟨2157422, by rfl⟩ : syracuseStep 2876563 = 4314845) B4314845
theorem B1893563 : Blo 1260448 1893563 := bstep (se 1 (by rfl) ⟨1420172, by rfl⟩ : syracuseStep 1893563 = 2840345) B2840345
theorem B1893623 : Blo 1260448 1893623 := bstep (se 1 (by rfl) ⟨1420217, by rfl⟩ : syracuseStep 1893623 = 2840435) B2840435
theorem B1418503 : Blo 1260448 1418503 := bstep (se 1 (by rfl) ⟨1063877, by rfl⟩ : syracuseStep 1418503 = 2127755) B2127755
theorem B1893647 : Blo 1260448 1893647 := bstep (se 1 (by rfl) ⟨1420235, by rfl⟩ : syracuseStep 1893647 = 2840471) B2840471
theorem B1795385 : Blo 1260448 1795385 := bstep (se 2 (by rfl) ⟨673269, by rfl⟩ : syracuseStep 1795385 = 1346539) B1346539
theorem B3073339 : Blo 1260448 3073339 := bstep (se 1 (by rfl) ⟨2305004, by rfl⟩ : syracuseStep 3073339 = 4610009) B4610009
theorem B3835271 : Blo 1260448 3835271 := bstep (se 1 (by rfl) ⟨2876453, by rfl⟩ : syracuseStep 3835271 = 5752907) B5752907
theorem B1418683 : Blo 1260448 1418683 := bstep (se 1 (by rfl) ⟨1064012, by rfl⟩ : syracuseStep 1418683 = 2128025) B2128025
theorem B1918409 : Blo 1260448 1918409 := bstep (se 2 (by rfl) ⟨719403, by rfl⟩ : syracuseStep 1918409 = 1438807) B1438807
theorem B3032635 : Blo 1260448 3032635 := bstep (se 1 (by rfl) ⟨2274476, by rfl⟩ : syracuseStep 3032635 = 4548953) B4548953
theorem B9217613 : Blo 1260448 9217613 := bstep (se 3 (by rfl) ⟨1728302, by rfl⟩ : syracuseStep 9217613 = 3456605) B3456605
theorem B2836115 : Blo 1260448 2836115 := bstep (se 1 (by rfl) ⟨2127086, by rfl⟩ : syracuseStep 2836115 = 4254173) B4254173
theorem B2836169 : Blo 1260448 2836169 := bstep (se 2 (by rfl) ⟨1063563, by rfl⟩ : syracuseStep 2836169 = 2127127) B2127127
theorem B2393975 : Blo 1260448 2393975 := bstep (se 1 (by rfl) ⟨1795481, by rfl⟩ : syracuseStep 2393975 = 3590963) B3590963
theorem B1419151 : Blo 1260448 1419151 := bstep (se 1 (by rfl) ⟨1064363, by rfl⟩ : syracuseStep 1419151 = 2128727) B2128727
theorem B4786067 : Blo 1260448 4786067 := bstep (se 1 (by rfl) ⟨3589550, by rfl⟩ : syracuseStep 4786067 = 7179101) B7179101
theorem B3590041 : Blo 1260448 3590041 := bstep (se 2 (by rfl) ⟨1346265, by rfl⟩ : syracuseStep 3590041 = 2692531) B2692531
theorem B8079257 : Blo 1260448 8079257 := bstep (se 2 (by rfl) ⟨3029721, by rfl⟩ : syracuseStep 8079257 = 6059443) B6059443
theorem B2394127 : Blo 1260448 2394127 := bstep (se 1 (by rfl) ⟨1795595, by rfl⟩ : syracuseStep 2394127 = 3591191) B3591191
theorem B3410039 : Blo 1260448 3410039 := bstep (se 1 (by rfl) ⟨2557529, by rfl⟩ : syracuseStep 3410039 = 5115059) B5115059
theorem B14362757 : Blo 1260448 14362757 := bstep (se 4 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 14362757 = 2693017) B2693017
theorem B2558137 : Blo 1260448 2558137 := bstep (se 2 (by rfl) ⟨959301, by rfl⟩ : syracuseStep 2558137 = 1918603) B1918603
theorem B1870025 : Blo 1260448 1870025 := bstep (se 2 (by rfl) ⟨701259, by rfl⟩ : syracuseStep 1870025 = 1402519) B1402519
theorem B1796359 : Blo 1260448 1796359 := bstep (se 1 (by rfl) ⟨1347269, by rfl⟩ : syracuseStep 1796359 = 2694539) B2694539
theorem B3639613 : Blo 1260448 3639613 := bstep (se 3 (by rfl) ⟨682427, by rfl⟩ : syracuseStep 3639613 = 1364855) B1364855
theorem B2836871 : Blo 1260448 2836871 := bstep (se 1 (by rfl) ⟨2127653, by rfl⟩ : syracuseStep 2836871 = 4255307) B4255307
theorem B1419655 : Blo 1260448 1419655 := bstep (se 1 (by rfl) ⟨1064741, by rfl⟩ : syracuseStep 1419655 = 2129483) B2129483
theorem B2394515 : Blo 1260448 2394515 := bstep (se 1 (by rfl) ⟨1795886, by rfl⟩ : syracuseStep 2394515 = 3591773) B3591773
theorem B17508829 : Blo 1260448 17508829 := bstep (se 3 (by rfl) ⟨3282905, by rfl⟩ : syracuseStep 17508829 = 6565811) B6565811
theorem B2837051 : Blo 1260448 2837051 := bstep (se 1 (by rfl) ⟨2127788, by rfl⟩ : syracuseStep 2837051 = 4255577) B4255577
theorem B2157115 : Blo 1260448 2157115 := bstep (se 1 (by rfl) ⟨1617836, by rfl⟩ : syracuseStep 2157115 = 3235673) B3235673
theorem B1419835 : Blo 1260448 1419835 := bstep (se 1 (by rfl) ⟨1064876, by rfl⟩ : syracuseStep 1419835 = 2129753) B2129753
theorem B53217911 : Blo 1260448 53217911 := bstep (se 1 (by rfl) ⟨39913433, by rfl⟩ : syracuseStep 53217911 = 79826867) B79826867
theorem B14371505 : Blo 1260448 14371505 := bstep (se 2 (by rfl) ⟨5389314, by rfl⟩ : syracuseStep 14371505 = 10778629) B10778629
theorem B2837177 : Blo 1260448 2837177 := bstep (se 2 (by rfl) ⟨1063941, by rfl⟩ : syracuseStep 2837177 = 2127883) B2127883
theorem B2304713 : Blo 1260448 2304713 := bstep (se 2 (by rfl) ⟨864267, by rfl⟩ : syracuseStep 2304713 = 1728535) B1728535
theorem B4254497 : Blo 1260448 4254497 := bstep (se 2 (by rfl) ⟨1595436, by rfl⟩ : syracuseStep 4254497 = 3190873) B3190873
theorem B5385113 : Blo 1260448 5385113 := bstep (se 2 (by rfl) ⟨2019417, by rfl⟩ : syracuseStep 5385113 = 4038835) B4038835
theorem B2837519 : Blo 1260448 2837519 := bstep (se 1 (by rfl) ⟨2128139, by rfl⟩ : syracuseStep 2837519 = 4256279) B4256279
theorem B2837537 : Blo 1260448 2837537 := bstep (se 2 (by rfl) ⟨1064076, by rfl⟩ : syracuseStep 2837537 = 2128153) B2128153
theorem B7187575 : Blo 1260448 7187575 := bstep (se 1 (by rfl) ⟨5390681, by rfl⟩ : syracuseStep 7187575 = 10781363) B10781363
theorem B5385473 : Blo 1260448 5385473 := bstep (se 2 (by rfl) ⟨2019552, by rfl⟩ : syracuseStep 5385473 = 4039105) B4039105
theorem B4255091 : Blo 1260448 4255091 := bstep (se 1 (by rfl) ⟨3191318, by rfl⟩ : syracuseStep 4255091 = 6382637) B6382637
theorem B5115251 : Blo 1260448 5115251 := bstep (se 1 (by rfl) ⟨3836438, by rfl⟩ : syracuseStep 5115251 = 7672877) B7672877
theorem B2837879 : Blo 1260448 2837879 := bstep (se 1 (by rfl) ⟨2128409, by rfl⟩ : syracuseStep 2837879 = 4256819) B4256819
theorem B9571769 : Blo 1260448 9571769 := bstep (se 2 (by rfl) ⟨3589413, by rfl⟩ : syracuseStep 9571769 = 7178827) B7178827
theorem B2838059 : Blo 1260448 2838059 := bstep (se 1 (by rfl) ⟨2128544, by rfl⟩ : syracuseStep 2838059 = 4257089) B4257089
theorem B3190529 : Blo 1260448 3190529 := bstep (se 2 (by rfl) ⟨1196448, by rfl⟩ : syracuseStep 3190529 = 2392897) B2392897
theorem B2395919 : Blo 1260448 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B3591965 : Blo 1260448 3591965 := bstep (se 3 (by rfl) ⟨673493, by rfl⟩ : syracuseStep 3591965 = 1346987) B1346987
theorem B6385553 : Blo 1260448 6385553 := bstep (se 2 (by rfl) ⟨2394582, by rfl⟩ : syracuseStep 6385553 = 4789165) B4789165
theorem B2838419 : Blo 1260448 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B9097123 : Blo 1260448 9097123 := bstep (se 1 (by rfl) ⟨6822842, by rfl⟩ : syracuseStep 9097123 = 13645685) B13645685
theorem B2838473 : Blo 1260448 2838473 := bstep (se 2 (by rfl) ⟨1064427, by rfl⟩ : syracuseStep 2838473 = 2128855) B2128855
theorem B4853803 : Blo 1260448 4853803 := bstep (se 1 (by rfl) ⟨3640352, by rfl⟩ : syracuseStep 4853803 = 7280705) B7280705
theorem B24252533 : Blo 1260448 24252533 := bstep (se 5 (by rfl) ⟨1136837, by rfl⟩ : syracuseStep 24252533 = 2273675) B2273675
theorem B6475949 : Blo 1260448 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B3190985 : Blo 1260448 3190985 := bstep (se 2 (by rfl) ⟨1196619, by rfl⟩ : syracuseStep 3190985 = 2393239) B2393239
theorem B15970505 : Blo 1260448 15970505 := bstep (se 2 (by rfl) ⟨5988939, by rfl⟩ : syracuseStep 15970505 = 11977879) B11977879
theorem B7180559 : Blo 1260448 7180559 := bstep (se 1 (by rfl) ⟨5385419, by rfl⟩ : syracuseStep 7180559 = 10770839) B10770839
theorem B2396459 : Blo 1260448 2396459 := bstep (se 1 (by rfl) ⟨1797344, by rfl⟩ : syracuseStep 2396459 = 3594689) B3594689
theorem B7188851 : Blo 1260448 7188851 := bstep (se 1 (by rfl) ⟨5391638, by rfl⟩ : syracuseStep 7188851 = 10783277) B10783277
theorem B4788665 : Blo 1260448 4788665 := bstep (se 2 (by rfl) ⟨1795749, by rfl⟩ : syracuseStep 4788665 = 3591499) B3591499
theorem B3592649 : Blo 1260448 3592649 := bstep (se 2 (by rfl) ⟨1347243, by rfl⟩ : syracuseStep 3592649 = 2694487) B2694487
theorem B7180811 : Blo 1260448 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B1348111 : Blo 1260448 1348111 := bstep (se 1 (by rfl) ⟨1011083, by rfl⟩ : syracuseStep 1348111 = 2022167) B2022167
theorem B3191339 : Blo 1260448 3191339 := bstep (se 1 (by rfl) ⟨2393504, by rfl⟩ : syracuseStep 3191339 = 4787009) B4787009
theorem B2839175 : Blo 1260448 2839175 := bstep (se 1 (by rfl) ⟨2129381, by rfl⟩ : syracuseStep 2839175 = 4258763) B4258763
theorem B2839355 : Blo 1260448 2839355 := bstep (se 1 (by rfl) ⟨2129516, by rfl⟩ : syracuseStep 2839355 = 4259033) B4259033
theorem B7189307 : Blo 1260448 7189307 := bstep (se 1 (by rfl) ⟨5391980, by rfl⟩ : syracuseStep 7189307 = 10783961) B10783961
theorem B24245081 : Blo 1260448 24245081 := bstep (se 2 (by rfl) ⟨9091905, by rfl⟩ : syracuseStep 24245081 = 18183811) B18183811
theorem B3838873 : Blo 1260448 3838873 := bstep (se 2 (by rfl) ⟨1439577, by rfl⟩ : syracuseStep 3838873 = 2879155) B2879155
theorem B68998067 : Blo 1260448 68998067 := bstep (se 1 (by rfl) ⟨51748550, by rfl⟩ : syracuseStep 68998067 = 103497101) B103497101
theorem B2839481 : Blo 1260448 2839481 := bstep (se 2 (by rfl) ⟨1064805, by rfl⟩ : syracuseStep 2839481 = 2129611) B2129611
theorem B3593231 : Blo 1260448 3593231 := bstep (se 1 (by rfl) ⟨2694923, by rfl⟩ : syracuseStep 3593231 = 5389847) B5389847
theorem B2692129 : Blo 1260448 2692129 := bstep (se 2 (by rfl) ⟨1009548, by rfl⟩ : syracuseStep 2692129 = 2019097) B2019097
theorem B21541949 : Blo 1260448 21541949 := bstep (se 3 (by rfl) ⟨4039115, by rfl⟩ : syracuseStep 21541949 = 8078231) B8078231
theorem B2839823 : Blo 1260448 2839823 := bstep (se 1 (by rfl) ⟨2129867, by rfl⟩ : syracuseStep 2839823 = 4259735) B4259735
theorem B2839841 : Blo 1260448 2839841 := bstep (se 2 (by rfl) ⟨1064940, by rfl⟩ : syracuseStep 2839841 = 2129881) B2129881
theorem B4789651 : Blo 1260448 4789651 := bstep (se 1 (by rfl) ⟨3592238, by rfl⟩ : syracuseStep 4789651 = 7184477) B7184477
theorem B2127289 : Blo 1260448 2127289 := bstep (se 2 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 2127289 = 1595467) B1595467
theorem B40924601 : Blo 1260448 40924601 := bstep (se 2 (by rfl) ⟨15346725, by rfl⟩ : syracuseStep 40924601 = 30693451) B30693451
theorem B5117393 : Blo 1260448 5117393 := bstep (se 2 (by rfl) ⟨1919022, by rfl⟩ : syracuseStep 5117393 = 3838045) B3838045
theorem B3192331 : Blo 1260448 3192331 := bstep (se 1 (by rfl) ⟨2394248, by rfl⟩ : syracuseStep 3192331 = 4788497) B4788497
theorem B2840183 : Blo 1260448 2840183 := bstep (se 1 (by rfl) ⟨2130137, by rfl⟩ : syracuseStep 2840183 = 4260275) B4260275
theorem B3192473 : Blo 1260448 3192473 := bstep (se 2 (by rfl) ⟨1197177, by rfl⟩ : syracuseStep 3192473 = 2394355) B2394355
theorem B7182017 : Blo 1260448 7182017 := bstep (se 2 (by rfl) ⟨2693256, by rfl⟩ : syracuseStep 7182017 = 5386513) B5386513
theorem B4544237 : Blo 1260448 4544237 := bstep (se 3 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 4544237 = 1704089) B1704089
theorem B2840363 : Blo 1260448 2840363 := bstep (se 1 (by rfl) ⟨2130272, by rfl⟩ : syracuseStep 2840363 = 4260545) B4260545
theorem B3192635 : Blo 1260448 3192635 := bstep (se 1 (by rfl) ⟨2394476, by rfl⟩ : syracuseStep 3192635 = 4788953) B4788953
theorem B5117831 : Blo 1260448 5117831 := bstep (se 1 (by rfl) ⟨3838373, by rfl⟩ : syracuseStep 5117831 = 7676747) B7676747
theorem B4257683 : Blo 1260448 4257683 := bstep (se 1 (by rfl) ⟨3193262, by rfl⟩ : syracuseStep 4257683 = 6386525) B6386525
theorem B6387659 : Blo 1260448 6387659 := bstep (se 1 (by rfl) ⟨4790744, by rfl⟩ : syracuseStep 6387659 = 9581489) B9581489
theorem B6821891 : Blo 1260448 6821891 := bstep (se 1 (by rfl) ⟨5116418, by rfl⟩ : syracuseStep 6821891 = 10232837) B10232837
theorem B9099287 : Blo 1260448 9099287 := bstep (se 1 (by rfl) ⟨6824465, by rfl⟩ : syracuseStep 9099287 = 13648931) B13648931
theorem B27277357 : Blo 1260448 27277357 := bstep (se 3 (by rfl) ⟨5114504, by rfl⟩ : syracuseStep 27277357 = 10229009) B10229009
theorem B2127991 : Blo 1260448 2127991 := bstep (se 1 (by rfl) ⟨1595993, by rfl⟩ : syracuseStep 2127991 = 3191987) B3191987
theorem B3192979 : Blo 1260448 3192979 := bstep (se 1 (by rfl) ⟨2394734, by rfl⟩ : syracuseStep 3192979 = 4789469) B4789469
theorem B1595639 : Blo 1260448 1595639 := bstep (se 1 (by rfl) ⟨1196729, by rfl⟩ : syracuseStep 1595639 = 2393459) B2393459
theorem B6387983 : Blo 1260448 6387983 := bstep (se 1 (by rfl) ⟨4790987, by rfl⟩ : syracuseStep 6387983 = 9581975) B9581975
theorem B3193121 : Blo 1260448 3193121 := bstep (se 2 (by rfl) ⟨1197420, by rfl⟩ : syracuseStep 3193121 = 2394841) B2394841
theorem B8083745 : Blo 1260448 8083745 := bstep (se 2 (by rfl) ⟨3031404, by rfl⟩ : syracuseStep 8083745 = 6062809) B6062809
theorem B2128187 : Blo 1260448 2128187 := bstep (se 1 (by rfl) ⟨1596140, by rfl⟩ : syracuseStep 2128187 = 3192281) B3192281
theorem B3455293 : Blo 1260448 3455293 := bstep (se 3 (by rfl) ⟨647867, by rfl⟩ : syracuseStep 3455293 = 1295735) B1295735
theorem B1890695 : Blo 1260448 1890695 := bstep (se 1 (by rfl) ⟨1418021, by rfl⟩ : syracuseStep 1890695 = 2836043) B2836043
theorem B3594631 : Blo 1260448 3594631 := bstep (se 1 (by rfl) ⟨2695973, by rfl⟩ : syracuseStep 3594631 = 5391947) B5391947
theorem B1595791 : Blo 1260448 1595791 := bstep (se 1 (by rfl) ⟨1196843, by rfl⟩ : syracuseStep 1595791 = 2393687) B2393687
theorem B1890731 : Blo 1260448 1890731 := bstep (se 1 (by rfl) ⟨1418048, by rfl⟩ : syracuseStep 1890731 = 2836097) B2836097
theorem B1890761 : Blo 1260448 1890761 := bstep (se 2 (by rfl) ⟨709035, by rfl⟩ : syracuseStep 1890761 = 1418071) B1418071
theorem B6650333 : Blo 1260448 6650333 := bstep (se 3 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 6650333 = 2493875) B2493875
theorem B6478301 : Blo 1260448 6478301 := bstep (se 3 (by rfl) ⟨1214681, by rfl⟩ : syracuseStep 6478301 = 2429363) B2429363
theorem B6912515 : Blo 1260448 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B1890875 : Blo 1260448 1890875 := bstep (se 1 (by rfl) ⟨1418156, by rfl⟩ : syracuseStep 1890875 = 2836313) B2836313
theorem B1595963 : Blo 1260448 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B12950117 : Blo 1260448 12950117 := bstep (se 4 (by rfl) ⟨1214073, by rfl⟩ : syracuseStep 12950117 = 2428147) B2428147
theorem B10222199 : Blo 1260448 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B1890935 : Blo 1260448 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B1890959 : Blo 1260448 1890959 := bstep (se 1 (by rfl) ⟨1418219, by rfl⟩ : syracuseStep 1890959 = 2836439) B2836439
theorem B3594905 : Blo 1260448 3594905 := bstep (se 2 (by rfl) ⟨1348089, by rfl⟩ : syracuseStep 3594905 = 2696179) B2696179
theorem B13818545 : Blo 1260448 13818545 := bstep (se 2 (by rfl) ⟨5181954, by rfl⟩ : syracuseStep 13818545 = 10363909) B10363909
theorem B1891001 : Blo 1260448 1891001 := bstep (se 2 (by rfl) ⟨709125, by rfl⟩ : syracuseStep 1891001 = 1418251) B1418251
theorem B21568193 : Blo 1260448 21568193 := bstep (se 2 (by rfl) ⟨8088072, by rfl⟩ : syracuseStep 21568193 = 16176145) B16176145
theorem B2128585 : Blo 1260448 2128585 := bstep (se 2 (by rfl) ⟨798219, by rfl⟩ : syracuseStep 2128585 = 1596439) B1596439
theorem B1891079 : Blo 1260448 1891079 := bstep (se 1 (by rfl) ⟨1418309, by rfl⟩ : syracuseStep 1891079 = 2836619) B2836619
theorem B27294479 : Blo 1260448 27294479 := bstep (se 1 (by rfl) ⟨20470859, by rfl⟩ : syracuseStep 27294479 = 40941719) B40941719
theorem B1891115 : Blo 1260448 1891115 := bstep (se 1 (by rfl) ⟨1418336, by rfl⟩ : syracuseStep 1891115 = 2836673) B2836673
theorem B1891145 : Blo 1260448 1891145 := bstep (se 2 (by rfl) ⟨709179, by rfl⟩ : syracuseStep 1891145 = 1418359) B1418359
theorem B2694035 : Blo 1260448 2694035 := bstep (se 1 (by rfl) ⟨2020526, by rfl⟩ : syracuseStep 2694035 = 4041053) B4041053
theorem B1260475 : Blo 1260448 1260475 := bstep (se 1 (by rfl) ⟨945356, by rfl⟩ : syracuseStep 1260475 = 1890713) B1890713
theorem B1891259 : Blo 1260448 1891259 := bstep (se 1 (by rfl) ⟨1418444, by rfl⟩ : syracuseStep 1891259 = 2836889) B2836889
theorem B1891319 : Blo 1260448 1891319 := bstep (se 1 (by rfl) ⟨1418489, by rfl⟩ : syracuseStep 1891319 = 2836979) B2836979
theorem B1260551 : Blo 1260448 1260551 := bstep (se 1 (by rfl) ⟨945413, by rfl⟩ : syracuseStep 1260551 = 1890827) B1890827
theorem B1260559 : Blo 1260448 1260559 := bstep (se 1 (by rfl) ⟨945419, by rfl⟩ : syracuseStep 1260559 = 1890839) B1890839
theorem B1891343 : Blo 1260448 1891343 := bstep (se 1 (by rfl) ⟨1418507, by rfl⟩ : syracuseStep 1891343 = 2837015) B2837015
theorem B1891385 : Blo 1260448 1891385 := bstep (se 2 (by rfl) ⟨709269, by rfl⟩ : syracuseStep 1891385 = 1418539) B1418539
theorem B1260603 : Blo 1260448 1260603 := bstep (se 1 (by rfl) ⟨945452, by rfl⟩ : syracuseStep 1260603 = 1890905) B1890905
theorem B4791383 : Blo 1260448 4791383 := bstep (se 1 (by rfl) ⟨3593537, by rfl⟩ : syracuseStep 4791383 = 7187075) B7187075
theorem B1260679 : Blo 1260448 1260679 := bstep (se 1 (by rfl) ⟨945509, by rfl⟩ : syracuseStep 1260679 = 1891019) B1891019
theorem B1891463 : Blo 1260448 1891463 := bstep (se 1 (by rfl) ⟨1418597, by rfl⟩ : syracuseStep 1891463 = 2837195) B2837195
theorem B1260687 : Blo 1260448 1260687 := bstep (se 1 (by rfl) ⟨945515, by rfl⟩ : syracuseStep 1260687 = 1891031) B1891031
theorem B1891499 : Blo 1260448 1891499 := bstep (se 1 (by rfl) ⟨1418624, by rfl⟩ : syracuseStep 1891499 = 2837249) B2837249
theorem B1260731 : Blo 1260448 1260731 := bstep (se 1 (by rfl) ⟨945548, by rfl⟩ : syracuseStep 1260731 = 1891097) B1891097
theorem B1891529 : Blo 1260448 1891529 := bstep (se 2 (by rfl) ⟨709323, by rfl⟩ : syracuseStep 1891529 = 1418647) B1418647
theorem B3194113 : Blo 1260448 3194113 := bstep (se 2 (by rfl) ⟨1197792, by rfl⟩ : syracuseStep 3194113 = 2395585) B2395585
theorem B1260807 : Blo 1260448 1260807 := bstep (se 1 (by rfl) ⟨945605, by rfl⟩ : syracuseStep 1260807 = 1891211) B1891211
theorem B1260815 : Blo 1260448 1260815 := bstep (se 1 (by rfl) ⟨945611, by rfl⟩ : syracuseStep 1260815 = 1891223) B1891223
theorem B4259087 : Blo 1260448 4259087 := bstep (se 1 (by rfl) ⟨3194315, by rfl⟩ : syracuseStep 4259087 = 6388631) B6388631
theorem B106421525 : Blo 1260448 106421525 := bstep (se 6 (by rfl) ⟨2494254, by rfl⟩ : syracuseStep 106421525 = 4988509) B4988509
theorem B14359841 : Blo 1260448 14359841 := bstep (se 2 (by rfl) ⟨5384940, by rfl⟩ : syracuseStep 14359841 = 10769881) B10769881
theorem B1260859 : Blo 1260448 1260859 := bstep (se 1 (by rfl) ⟨945644, by rfl⟩ : syracuseStep 1260859 = 1891289) B1891289
theorem B1891643 : Blo 1260448 1891643 := bstep (se 1 (by rfl) ⟨1418732, by rfl⟩ : syracuseStep 1891643 = 2837465) B2837465
theorem B1891703 : Blo 1260448 1891703 := bstep (se 1 (by rfl) ⟨1418777, by rfl⟩ : syracuseStep 1891703 = 2837555) B2837555
theorem B1260935 : Blo 1260448 1260935 := bstep (se 1 (by rfl) ⟨945701, by rfl⟩ : syracuseStep 1260935 = 1891403) B1891403
theorem B2129287 : Blo 1260448 2129287 := bstep (se 1 (by rfl) ⟨1596965, by rfl⟩ : syracuseStep 2129287 = 3193931) B3193931
theorem B1260943 : Blo 1260448 1260943 := bstep (se 1 (by rfl) ⟨945707, by rfl⟩ : syracuseStep 1260943 = 1891415) B1891415
theorem B1891727 : Blo 1260448 1891727 := bstep (se 1 (by rfl) ⟨1418795, by rfl⟩ : syracuseStep 1891727 = 2837591) B2837591
theorem B1891769 : Blo 1260448 1891769 := bstep (se 2 (by rfl) ⟨709413, by rfl⟩ : syracuseStep 1891769 = 1418827) B1418827
theorem B1260987 : Blo 1260448 1260987 := bstep (se 1 (by rfl) ⟨945740, by rfl⟩ : syracuseStep 1260987 = 1891481) B1891481
theorem B3407305 : Blo 1260448 3407305 := bstep (se 2 (by rfl) ⟨1277739, by rfl⟩ : syracuseStep 3407305 = 2555479) B2555479
theorem B3030529 : Blo 1260448 3030529 := bstep (se 2 (by rfl) ⟨1136448, by rfl⟩ : syracuseStep 3030529 = 2272897) B2272897
theorem B13630979 : Blo 1260448 13630979 := bstep (se 1 (by rfl) ⟨10223234, by rfl⟩ : syracuseStep 13630979 = 20446469) B20446469
theorem B1261063 : Blo 1260448 1261063 := bstep (se 1 (by rfl) ⟨945797, by rfl⟩ : syracuseStep 1261063 = 1891595) B1891595
theorem B1891847 : Blo 1260448 1891847 := bstep (se 1 (by rfl) ⟨1418885, by rfl⟩ : syracuseStep 1891847 = 2837771) B2837771
theorem B1596935 : Blo 1260448 1596935 := bstep (se 1 (by rfl) ⟨1197701, by rfl⟩ : syracuseStep 1596935 = 2395403) B2395403
theorem B1261071 : Blo 1260448 1261071 := bstep (se 1 (by rfl) ⟨945803, by rfl⟩ : syracuseStep 1261071 = 1891607) B1891607
theorem B4259357 : Blo 1260448 4259357 := bstep (se 3 (by rfl) ⟨798629, by rfl⟩ : syracuseStep 4259357 = 1597259) B1597259
theorem B1891883 : Blo 1260448 1891883 := bstep (se 1 (by rfl) ⟨1418912, by rfl⟩ : syracuseStep 1891883 = 2837825) B2837825
theorem B1261115 : Blo 1260448 1261115 := bstep (se 1 (by rfl) ⟨945836, by rfl⟩ : syracuseStep 1261115 = 1891673) B1891673
theorem B4791869 : Blo 1260448 4791869 := bstep (se 3 (by rfl) ⟨898475, by rfl⟩ : syracuseStep 4791869 = 1796951) B1796951
theorem B1891913 : Blo 1260448 1891913 := bstep (se 2 (by rfl) ⟨709467, by rfl⟩ : syracuseStep 1891913 = 1418935) B1418935
theorem B52518493 : Blo 1260448 52518493 := bstep (se 3 (by rfl) ⟨9847217, by rfl⟩ : syracuseStep 52518493 = 19694435) B19694435
theorem B1261191 : Blo 1260448 1261191 := bstep (se 1 (by rfl) ⟨945893, by rfl⟩ : syracuseStep 1261191 = 1891787) B1891787
theorem B1261199 : Blo 1260448 1261199 := bstep (se 1 (by rfl) ⟨945899, by rfl⟩ : syracuseStep 1261199 = 1891799) B1891799
theorem B30670487 : Blo 1260448 30670487 := bstep (se 1 (by rfl) ⟨23002865, by rfl⟩ : syracuseStep 30670487 = 46005731) B46005731
theorem B1261243 : Blo 1260448 1261243 := bstep (se 1 (by rfl) ⟨945932, by rfl⟩ : syracuseStep 1261243 = 1891865) B1891865
theorem B1892027 : Blo 1260448 1892027 := bstep (se 1 (by rfl) ⟨1419020, by rfl⟩ : syracuseStep 1892027 = 2838041) B2838041
theorem B6389441 : Blo 1260448 6389441 := bstep (se 2 (by rfl) ⟨2396040, by rfl⟩ : syracuseStep 6389441 = 4792081) B4792081
theorem B1892087 : Blo 1260448 1892087 := bstep (se 1 (by rfl) ⟨1419065, by rfl⟩ : syracuseStep 1892087 = 2838131) B2838131
theorem B1261319 : Blo 1260448 1261319 := bstep (se 1 (by rfl) ⟨945989, by rfl⟩ : syracuseStep 1261319 = 1891979) B1891979
theorem B1703695 : Blo 1260448 1703695 := bstep (se 1 (by rfl) ⟨1277771, by rfl⟩ : syracuseStep 1703695 = 2555543) B2555543
theorem B3071759 : Blo 1260448 3071759 := bstep (se 1 (by rfl) ⟨2303819, by rfl⟩ : syracuseStep 3071759 = 4607639) B4607639
theorem B1261327 : Blo 1260448 1261327 := bstep (se 1 (by rfl) ⟨945995, by rfl⟩ : syracuseStep 1261327 = 1891991) B1891991
theorem B1892111 : Blo 1260448 1892111 := bstep (se 1 (by rfl) ⟨1419083, by rfl⟩ : syracuseStep 1892111 = 2838167) B2838167
theorem B1892153 : Blo 1260448 1892153 := bstep (se 2 (by rfl) ⟨709557, by rfl⟩ : syracuseStep 1892153 = 1419115) B1419115
theorem B1261371 : Blo 1260448 1261371 := bstep (se 1 (by rfl) ⟨946028, by rfl⟩ : syracuseStep 1261371 = 1892057) B1892057
theorem B1261447 : Blo 1260448 1261447 := bstep (se 1 (by rfl) ⟨946085, by rfl⟩ : syracuseStep 1261447 = 1892171) B1892171
theorem B1892231 : Blo 1260448 1892231 := bstep (se 1 (by rfl) ⟨1419173, by rfl⟩ : syracuseStep 1892231 = 2838347) B2838347
theorem B1261455 : Blo 1260448 1261455 := bstep (se 1 (by rfl) ⟨946091, by rfl⟩ : syracuseStep 1261455 = 1892183) B1892183
theorem B1892267 : Blo 1260448 1892267 := bstep (se 1 (by rfl) ⟨1419200, by rfl⟩ : syracuseStep 1892267 = 2838401) B2838401
theorem B1261499 : Blo 1260448 1261499 := bstep (se 1 (by rfl) ⟨946124, by rfl⟩ : syracuseStep 1261499 = 1892249) B1892249
theorem B1892297 : Blo 1260448 1892297 := bstep (se 2 (by rfl) ⟨709611, by rfl⟩ : syracuseStep 1892297 = 1419223) B1419223
theorem B8077259 : Blo 1260448 8077259 := bstep (se 1 (by rfl) ⟨6057944, by rfl⟩ : syracuseStep 8077259 = 12115889) B12115889
theorem B1261607 : Blo 1260448 1261607 := bstep (se 1 (by rfl) ⟨946205, by rfl⟩ : syracuseStep 1261607 = 1892411) B1892411
theorem B6471737 : Blo 1260448 6471737 := bstep (se 2 (by rfl) ⟨2426901, by rfl⟩ : syracuseStep 6471737 = 4853803) B4853803
theorem B4259897 : Blo 1260448 4259897 := bstep (se 2 (by rfl) ⟨1597461, by rfl⟩ : syracuseStep 4259897 = 3194923) B3194923
theorem B1261647 : Blo 1260448 1261647 := bstep (se 1 (by rfl) ⟨946235, by rfl⟩ : syracuseStep 1261647 = 1892471) B1892471
theorem B1261663 : Blo 1260448 1261663 := bstep (se 1 (by rfl) ⟨946247, by rfl⟩ : syracuseStep 1261663 = 1892495) B1892495
theorem B4317299 : Blo 1260448 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B1261691 : Blo 1260448 1261691 := bstep (se 1 (by rfl) ⟨946268, by rfl⟩ : syracuseStep 1261691 = 1892537) B1892537
theorem B2130043 : Blo 1260448 2130043 := bstep (se 1 (by rfl) ⟨1597532, by rfl⟩ : syracuseStep 2130043 = 3195065) B3195065
theorem B1261743 : Blo 1260448 1261743 := bstep (se 1 (by rfl) ⟨946307, by rfl⟩ : syracuseStep 1261743 = 1892615) B1892615
theorem B1261767 : Blo 1260448 1261767 := bstep (se 1 (by rfl) ⟨946325, by rfl⟩ : syracuseStep 1261767 = 1892651) B1892651
theorem B1597639 : Blo 1260448 1597639 := bstep (se 1 (by rfl) ⟨1198229, by rfl⟩ : syracuseStep 1597639 = 2396459) B2396459
theorem B1261787 : Blo 1260448 1261787 := bstep (se 1 (by rfl) ⟨946340, by rfl⟩ : syracuseStep 1261787 = 1892681) B1892681
theorem B4792567 : Blo 1260448 4792567 := bstep (se 1 (by rfl) ⟨3594425, by rfl⟩ : syracuseStep 4792567 = 7188851) B7188851
theorem B1261863 : Blo 1260448 1261863 := bstep (se 1 (by rfl) ⟨946397, by rfl⟩ : syracuseStep 1261863 = 1892795) B1892795
theorem B1261903 : Blo 1260448 1261903 := bstep (se 1 (by rfl) ⟨946427, by rfl⟩ : syracuseStep 1261903 = 1892855) B1892855
theorem B1261919 : Blo 1260448 1261919 := bstep (se 1 (by rfl) ⟨946439, by rfl⟩ : syracuseStep 1261919 = 1892879) B1892879
theorem B1261947 : Blo 1260448 1261947 := bstep (se 1 (by rfl) ⟨946460, by rfl⟩ : syracuseStep 1261947 = 1892921) B1892921
theorem B4260221 : Blo 1260448 4260221 := bstep (se 3 (by rfl) ⟨798791, by rfl⟩ : syracuseStep 4260221 = 1597583) B1597583
theorem B1892783 : Blo 1260448 1892783 := bstep (se 1 (by rfl) ⟨1419587, by rfl⟩ : syracuseStep 1892783 = 2839175) B2839175
theorem B1261999 : Blo 1260448 1261999 := bstep (se 1 (by rfl) ⟨946499, by rfl⟩ : syracuseStep 1261999 = 1892999) B1892999
theorem B1262023 : Blo 1260448 1262023 := bstep (se 1 (by rfl) ⟨946517, by rfl⟩ : syracuseStep 1262023 = 1893035) B1893035
theorem B1262043 : Blo 1260448 1262043 := bstep (se 1 (by rfl) ⟨946532, by rfl⟩ : syracuseStep 1262043 = 1893065) B1893065
theorem B1892873 : Blo 1260448 1892873 := bstep (se 2 (by rfl) ⟨709827, by rfl⟩ : syracuseStep 1892873 = 1419655) B1419655
theorem B4792841 : Blo 1260448 4792841 := bstep (se 2 (by rfl) ⟨1797315, by rfl⟩ : syracuseStep 4792841 = 3594631) B3594631
theorem B1892903 : Blo 1260448 1892903 := bstep (se 1 (by rfl) ⟨1419677, by rfl⟩ : syracuseStep 1892903 = 2839355) B2839355
theorem B1262119 : Blo 1260448 1262119 := bstep (se 1 (by rfl) ⟨946589, by rfl⟩ : syracuseStep 1262119 = 1893179) B1893179
theorem B4792871 : Blo 1260448 4792871 := bstep (se 1 (by rfl) ⟨3594653, by rfl⟩ : syracuseStep 4792871 = 7189307) B7189307
theorem B16163387 : Blo 1260448 16163387 := bstep (se 1 (by rfl) ⟨12122540, by rfl⟩ : syracuseStep 16163387 = 24245081) B24245081
theorem B1262159 : Blo 1260448 1262159 := bstep (se 1 (by rfl) ⟨946619, by rfl⟩ : syracuseStep 1262159 = 1893239) B1893239
theorem B1262175 : Blo 1260448 1262175 := bstep (se 1 (by rfl) ⟨946631, by rfl⟩ : syracuseStep 1262175 = 1893263) B1893263
theorem B45998711 : Blo 1260448 45998711 := bstep (se 1 (by rfl) ⟨34499033, by rfl⟩ : syracuseStep 45998711 = 68998067) B68998067
theorem B1892987 : Blo 1260448 1892987 := bstep (se 1 (by rfl) ⟨1419740, by rfl⟩ : syracuseStep 1892987 = 2839481) B2839481
theorem B1262203 : Blo 1260448 1262203 := bstep (se 1 (by rfl) ⟨946652, by rfl⟩ : syracuseStep 1262203 = 1893305) B1893305
theorem B3408523 : Blo 1260448 3408523 := bstep (se 1 (by rfl) ⟨2556392, by rfl⟩ : syracuseStep 3408523 = 5112785) B5112785
theorem B4260491 : Blo 1260448 4260491 := bstep (se 1 (by rfl) ⟨3195368, by rfl⟩ : syracuseStep 4260491 = 6390737) B6390737
theorem B1262255 : Blo 1260448 1262255 := bstep (se 1 (by rfl) ⟨946691, by rfl⟩ : syracuseStep 1262255 = 1893383) B1893383
theorem B1262279 : Blo 1260448 1262279 := bstep (se 1 (by rfl) ⟨946709, by rfl⟩ : syracuseStep 1262279 = 1893419) B1893419
theorem B14361299 : Blo 1260448 14361299 := bstep (se 1 (by rfl) ⟨10770974, by rfl⟩ : syracuseStep 14361299 = 21541949) B21541949
theorem B1262299 : Blo 1260448 1262299 := bstep (se 1 (by rfl) ⟨946724, by rfl⟩ : syracuseStep 1262299 = 1893449) B1893449
theorem B2876153 : Blo 1260448 2876153 := bstep (se 2 (by rfl) ⟨1078557, by rfl⟩ : syracuseStep 2876153 = 2157115) B2157115
theorem B1893113 : Blo 1260448 1893113 := bstep (se 2 (by rfl) ⟨709917, by rfl⟩ : syracuseStep 1893113 = 1419835) B1419835
theorem B1262375 : Blo 1260448 1262375 := bstep (se 1 (by rfl) ⟨946781, by rfl⟩ : syracuseStep 1262375 = 1893563) B1893563
theorem B1262415 : Blo 1260448 1262415 := bstep (se 1 (by rfl) ⟨946811, by rfl⟩ : syracuseStep 1262415 = 1893623) B1893623
theorem B1893215 : Blo 1260448 1893215 := bstep (se 1 (by rfl) ⟨1419911, by rfl⟩ : syracuseStep 1893215 = 2839823) B2839823
theorem B1262431 : Blo 1260448 1262431 := bstep (se 1 (by rfl) ⟨946823, by rfl⟩ : syracuseStep 1262431 = 1893647) B1893647
theorem B1893227 : Blo 1260448 1893227 := bstep (se 1 (by rfl) ⟨1419920, by rfl⟩ : syracuseStep 1893227 = 2839841) B2839841
theorem B2556847 : Blo 1260448 2556847 := bstep (se 1 (by rfl) ⟨1917635, by rfl⟩ : syracuseStep 2556847 = 3835271) B3835271
theorem B13640669 : Blo 1260448 13640669 := bstep (se 3 (by rfl) ⟨2557625, by rfl⟩ : syracuseStep 13640669 = 5115251) B5115251
theorem B6145075 : Blo 1260448 6145075 := bstep (se 1 (by rfl) ⟨4608806, by rfl⟩ : syracuseStep 6145075 = 9217613) B9217613
theorem B1893455 : Blo 1260448 1893455 := bstep (se 1 (by rfl) ⟨1420091, by rfl⟩ : syracuseStep 1893455 = 2840183) B2840183
theorem B1893575 : Blo 1260448 1893575 := bstep (se 1 (by rfl) ⟨1420181, by rfl⟩ : syracuseStep 1893575 = 2840363) B2840363
theorem B4547927 : Blo 1260448 4547927 := bstep (se 1 (by rfl) ⟨3410945, by rfl⟩ : syracuseStep 4547927 = 6821891) B6821891
theorem B3589505 : Blo 1260448 3589505 := bstep (se 2 (by rfl) ⟨1346064, by rfl⟩ : syracuseStep 3589505 = 2692129) B2692129
theorem B1418791 : Blo 1260448 1418791 := bstep (se 1 (by rfl) ⟨1064093, by rfl⟩ : syracuseStep 1418791 = 2128187) B2128187
theorem B4433555 : Blo 1260448 4433555 := bstep (se 1 (by rfl) ⟨3325166, by rfl⟩ : syracuseStep 4433555 = 6650333) B6650333
theorem B4318867 : Blo 1260448 4318867 := bstep (se 1 (by rfl) ⟨3239150, by rfl⟩ : syracuseStep 4318867 = 6478301) B6478301
theorem B4097785 : Blo 1260448 4097785 := bstep (se 2 (by rfl) ⟨1536669, by rfl⟩ : syracuseStep 4097785 = 3073339) B3073339
theorem B14378795 : Blo 1260448 14378795 := bstep (se 1 (by rfl) ⟨10784096, by rfl⟩ : syracuseStep 14378795 = 21568193) B21568193
theorem B18196319 : Blo 1260448 18196319 := bstep (se 1 (by rfl) ⟨13647239, by rfl⟩ : syracuseStep 18196319 = 27294479) B27294479
theorem B2836331 : Blo 1260448 2836331 := bstep (se 1 (by rfl) ⟨2127248, by rfl⟩ : syracuseStep 2836331 = 4254497) B4254497
theorem B2836385 : Blo 1260448 2836385 := bstep (se 2 (by rfl) ⟨1063644, by rfl⟩ : syracuseStep 2836385 = 2127289) B2127289
theorem B1796023 : Blo 1260448 1796023 := bstep (se 1 (by rfl) ⟨1347017, by rfl⟩ : syracuseStep 1796023 = 2694035) B2694035
theorem B3590075 : Blo 1260448 3590075 := bstep (se 1 (by rfl) ⟨2692556, by rfl⟩ : syracuseStep 3590075 = 5385113) B5385113
theorem B4040705 : Blo 1260448 4040705 := bstep (se 2 (by rfl) ⟨1515264, by rfl⟩ : syracuseStep 4040705 = 3030529) B3030529
theorem B9578573 : Blo 1260448 9578573 := bstep (se 3 (by rfl) ⟨1795982, by rfl⟩ : syracuseStep 9578573 = 3591965) B3591965
theorem B3590315 : Blo 1260448 3590315 := bstep (se 1 (by rfl) ⟨2692736, by rfl⟩ : syracuseStep 3590315 = 5385473) B5385473
theorem B2836727 : Blo 1260448 2836727 := bstep (se 1 (by rfl) ⟨2127545, by rfl⟩ : syracuseStep 2836727 = 4255091) B4255091
theorem B6383933 : Blo 1260448 6383933 := bstep (se 3 (by rfl) ⟨1196987, by rfl⟩ : syracuseStep 6383933 = 2393975) B2393975
theorem B9087319 : Blo 1260448 9087319 := bstep (se 1 (by rfl) ⟨6815489, by rfl⟩ : syracuseStep 9087319 = 13630979) B13630979
theorem B2271593 : Blo 1260448 2271593 := bstep (se 2 (by rfl) ⟨851847, by rfl⟩ : syracuseStep 2271593 = 1703695) B1703695
theorem B4786721 : Blo 1260448 4786721 := bstep (se 2 (by rfl) ⟨1795020, by rfl⟩ : syracuseStep 4786721 = 3590041) B3590041
theorem B5384839 : Blo 1260448 5384839 := bstep (se 1 (by rfl) ⟨4038629, by rfl⟩ : syracuseStep 5384839 = 8077259) B8077259
theorem B7383737 : Blo 1260448 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B2837321 : Blo 1260448 2837321 := bstep (se 2 (by rfl) ⟨1063995, by rfl⟩ : syracuseStep 2837321 = 2127991) B2127991
theorem B4787039 : Blo 1260448 4787039 := bstep (se 1 (by rfl) ⟨3590279, by rfl⟩ : syracuseStep 4787039 = 7180559) B7180559
theorem B3410849 : Blo 1260448 3410849 := bstep (se 2 (by rfl) ⟨1279068, by rfl⟩ : syracuseStep 3410849 = 2558137) B2558137
theorem B2395099 : Blo 1260448 2395099 := bstep (se 1 (by rfl) ⟨1796324, by rfl⟩ : syracuseStep 2395099 = 3592649) B3592649
theorem B4787207 : Blo 1260448 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B2395145 : Blo 1260448 2395145 := bstep (se 2 (by rfl) ⟨898179, by rfl⟩ : syracuseStep 2395145 = 1796359) B1796359
theorem B4852817 : Blo 1260448 4852817 := bstep (se 2 (by rfl) ⟨1819806, by rfl⟩ : syracuseStep 4852817 = 3639613) B3639613
theorem B4607057 : Blo 1260448 4607057 := bstep (se 2 (by rfl) ⟨1727646, by rfl⟩ : syracuseStep 4607057 = 3455293) B3455293
theorem B4255037 : Blo 1260448 4255037 := bstep (se 3 (by rfl) ⟨797819, by rfl⟩ : syracuseStep 4255037 = 1595639) B1595639
theorem B2395487 : Blo 1260448 2395487 := bstep (se 1 (by rfl) ⟨1796615, by rfl⟩ : syracuseStep 2395487 = 3593231) B3593231
theorem B1797481 : Blo 1260448 1797481 := bstep (se 2 (by rfl) ⟨674055, by rfl⟩ : syracuseStep 1797481 = 1348111) B1348111
theorem B4787693 : Blo 1260448 4787693 := bstep (se 3 (by rfl) ⟨897692, by rfl⟩ : syracuseStep 4787693 = 1795385) B1795385
theorem B2838113 : Blo 1260448 2838113 := bstep (se 2 (by rfl) ⟨1064292, by rfl⟩ : syracuseStep 2838113 = 2128585) B2128585
theorem B27283067 : Blo 1260448 27283067 := bstep (se 1 (by rfl) ⟨20462300, by rfl⟩ : syracuseStep 27283067 = 40924601) B40924601
theorem B3411595 : Blo 1260448 3411595 := bstep (se 1 (by rfl) ⟨2558696, by rfl⟩ : syracuseStep 3411595 = 5117393) B5117393
theorem B4788011 : Blo 1260448 4788011 := bstep (se 1 (by rfl) ⟨3591008, by rfl⟩ : syracuseStep 4788011 = 7182017) B7182017
theorem B5115757 : Blo 1260448 5115757 := bstep (se 3 (by rfl) ⟨959204, by rfl⟩ : syracuseStep 5115757 = 1918409) B1918409
theorem B3411887 : Blo 1260448 3411887 := bstep (se 1 (by rfl) ⟨2558915, by rfl⟩ : syracuseStep 3411887 = 5117831) B5117831
theorem B3190711 : Blo 1260448 3190711 := bstep (se 1 (by rfl) ⟨2393033, by rfl⟩ : syracuseStep 3190711 = 4786067) B4786067
theorem B2838455 : Blo 1260448 2838455 := bstep (se 1 (by rfl) ⟨2128841, by rfl⟩ : syracuseStep 2838455 = 4257683) B4257683
theorem B5386171 : Blo 1260448 5386171 := bstep (se 1 (by rfl) ⟨4039628, by rfl⟩ : syracuseStep 5386171 = 8079257) B8079257
theorem B6066191 : Blo 1260448 6066191 := bstep (se 1 (by rfl) ⟨4549643, by rfl⟩ : syracuseStep 6066191 = 9099287) B9099287
theorem B2273359 : Blo 1260448 2273359 := bstep (se 1 (by rfl) ⟨1705019, by rfl⟩ : syracuseStep 2273359 = 3410039) B3410039
theorem B4255901 : Blo 1260448 4255901 := bstep (se 3 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 4255901 = 1595963) B1595963
theorem B4042909 : Blo 1260448 4042909 := bstep (se 3 (by rfl) ⟨758045, by rfl⟩ : syracuseStep 4042909 = 1516091) B1516091
theorem B141914429 : Blo 1260448 141914429 := bstep (se 3 (by rfl) ⟨26608955, by rfl⟩ : syracuseStep 141914429 = 53217911) B53217911
theorem B4608343 : Blo 1260448 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B9572741 : Blo 1260448 9572741 := bstep (se 4 (by rfl) ⟨897444, by rfl⟩ : syracuseStep 9572741 = 1794889) B1794889
theorem B2396603 : Blo 1260448 2396603 := bstep (se 1 (by rfl) ⟨1797452, by rfl⟩ : syracuseStep 2396603 = 3594905) B3594905
theorem B9212363 : Blo 1260448 9212363 := bstep (se 1 (by rfl) ⟨6909272, by rfl⟩ : syracuseStep 9212363 = 13818545) B13818545
theorem B9581003 : Blo 1260448 9581003 := bstep (se 1 (by rfl) ⟨7185752, by rfl⟩ : syracuseStep 9581003 = 14371505) B14371505
theorem B1536475 : Blo 1260448 1536475 := bstep (se 1 (by rfl) ⟨1152356, by rfl⟩ : syracuseStep 1536475 = 2304713) B2304713
theorem B2839049 : Blo 1260448 2839049 := bstep (se 2 (by rfl) ⟨1064643, by rfl⟩ : syracuseStep 2839049 = 2129287) B2129287
theorem B6386201 : Blo 1260448 6386201 := bstep (se 2 (by rfl) ⟨2394825, by rfl⟩ : syracuseStep 6386201 = 4789651) B4789651
theorem B4543073 : Blo 1260448 4543073 := bstep (se 2 (by rfl) ⟨1703652, by rfl⟩ : syracuseStep 4543073 = 3407305) B3407305
theorem B4256441 : Blo 1260448 4256441 := bstep (se 2 (by rfl) ⟨1596165, by rfl⟩ : syracuseStep 4256441 = 3192331) B3192331
theorem B4043513 : Blo 1260448 4043513 := bstep (se 2 (by rfl) ⟨1516317, by rfl⟩ : syracuseStep 4043513 = 3032635) B3032635
theorem B2839391 : Blo 1260448 2839391 := bstep (se 1 (by rfl) ⟨2129543, by rfl⟩ : syracuseStep 2839391 = 4259087) B4259087
theorem B70947683 : Blo 1260448 70947683 := bstep (se 1 (by rfl) ⟨53210762, by rfl⟩ : syracuseStep 70947683 = 106421525) B106421525
theorem B9573227 : Blo 1260448 9573227 := bstep (se 1 (by rfl) ⟨7179920, by rfl⟩ : syracuseStep 9573227 = 14359841) B14359841
theorem B2839571 : Blo 1260448 2839571 := bstep (se 1 (by rfl) ⟨2129678, by rfl⟩ : syracuseStep 2839571 = 4259357) B4259357
theorem B2127019 : Blo 1260448 2127019 := bstep (se 1 (by rfl) ⟨1595264, by rfl⟩ : syracuseStep 2127019 = 3190529) B3190529
theorem B12129497 : Blo 1260448 12129497 := bstep (se 2 (by rfl) ⟨4548561, by rfl⟩ : syracuseStep 12129497 = 9097123) B9097123
theorem B4257035 : Blo 1260448 4257035 := bstep (se 1 (by rfl) ⟨3192776, by rfl⟩ : syracuseStep 4257035 = 6385553) B6385553
theorem B3192169 : Blo 1260448 3192169 := bstep (se 2 (by rfl) ⟨1197063, by rfl⟩ : syracuseStep 3192169 = 2394127) B2394127
theorem B2839913 : Blo 1260448 2839913 := bstep (se 2 (by rfl) ⟨1064967, by rfl⟩ : syracuseStep 2839913 = 2129935) B2129935
theorem B36369809 : Blo 1260448 36369809 := bstep (se 2 (by rfl) ⟨13638678, by rfl⟩ : syracuseStep 36369809 = 27277357) B27277357
theorem B16168355 : Blo 1260448 16168355 := bstep (se 1 (by rfl) ⟨12126266, by rfl⟩ : syracuseStep 16168355 = 24252533) B24252533
theorem B2020783 : Blo 1260448 2020783 := bstep (se 1 (by rfl) ⟨1515587, by rfl⟩ : syracuseStep 2020783 = 3031175) B3031175
theorem B2127323 : Blo 1260448 2127323 := bstep (se 1 (by rfl) ⟨1595492, by rfl⟩ : syracuseStep 2127323 = 3190985) B3190985
theorem B32765429 : Blo 1260448 32765429 := bstep (se 5 (by rfl) ⟨1535879, by rfl⟩ : syracuseStep 32765429 = 3071759) B3071759
theorem B4257305 : Blo 1260448 4257305 := bstep (se 2 (by rfl) ⟨1596489, by rfl⟩ : syracuseStep 4257305 = 3192979) B3192979
theorem B3192443 : Blo 1260448 3192443 := bstep (se 1 (by rfl) ⟨2394332, by rfl⟩ : syracuseStep 3192443 = 4788665) B4788665
theorem B2127559 : Blo 1260448 2127559 := bstep (se 1 (by rfl) ⟨1595669, by rfl⟩ : syracuseStep 2127559 = 3191339) B3191339
theorem B17258275 : Blo 1260448 17258275 := bstep (se 1 (by rfl) ⟨12943706, by rfl⟩ : syracuseStep 17258275 = 25887413) B25887413
theorem B4855619 : Blo 1260448 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B2127721 : Blo 1260448 2127721 := bstep (se 2 (by rfl) ⟨797895, by rfl⟩ : syracuseStep 2127721 = 1595791) B1595791
theorem B4790123 : Blo 1260448 4790123 := bstep (se 1 (by rfl) ⟨3592592, by rfl⟩ : syracuseStep 4790123 = 7185185) B7185185
theorem B42588013 : Blo 1260448 42588013 := bstep (se 3 (by rfl) ⟨7985252, by rfl⟩ : syracuseStep 42588013 = 15970505) B15970505
theorem B2840507 : Blo 1260448 2840507 := bstep (se 1 (by rfl) ⟨2130380, by rfl⟩ : syracuseStep 2840507 = 4260761) B4260761
theorem B23345105 : Blo 1260448 23345105 := bstep (se 2 (by rfl) ⟨8754414, by rfl⟩ : syracuseStep 23345105 = 17508829) B17508829
theorem B15341669 : Blo 1260448 15341669 := bstep (se 4 (by rfl) ⟨1438281, by rfl⟩ : syracuseStep 15341669 = 2876563) B2876563
theorem B1890743 : Blo 1260448 1890743 := bstep (se 1 (by rfl) ⟨1418057, by rfl⟩ : syracuseStep 1890743 = 2836115) B2836115
theorem B2128315 : Blo 1260448 2128315 := bstep (se 1 (by rfl) ⟨1596236, by rfl⟩ : syracuseStep 2128315 = 3192473) B3192473
theorem B1890779 : Blo 1260448 1890779 := bstep (se 1 (by rfl) ⟨1418084, by rfl⟩ : syracuseStep 1890779 = 2836169) B2836169
theorem B3029491 : Blo 1260448 3029491 := bstep (se 1 (by rfl) ⟨2272118, by rfl⟩ : syracuseStep 3029491 = 4544237) B4544237
theorem B5118497 : Blo 1260448 5118497 := bstep (se 2 (by rfl) ⟨1919436, by rfl⟩ : syracuseStep 5118497 = 3838873) B3838873
theorem B2128423 : Blo 1260448 2128423 := bstep (se 1 (by rfl) ⟨1596317, by rfl⟩ : syracuseStep 2128423 = 3192635) B3192635
theorem B4258439 : Blo 1260448 4258439 := bstep (se 1 (by rfl) ⟨3193829, by rfl⟩ : syracuseStep 4258439 = 6387659) B6387659
theorem B4258493 : Blo 1260448 4258493 := bstep (se 3 (by rfl) ⟨798467, by rfl⟩ : syracuseStep 4258493 = 1596935) B1596935
theorem B9575171 : Blo 1260448 9575171 := bstep (se 1 (by rfl) ⟨7181378, by rfl⟩ : syracuseStep 9575171 = 14362757) B14362757
theorem B9583433 : Blo 1260448 9583433 := bstep (se 2 (by rfl) ⟨3593787, by rfl⟩ : syracuseStep 9583433 = 7187575) B7187575
theorem B4258655 : Blo 1260448 4258655 := bstep (se 1 (by rfl) ⟨3193991, by rfl⟩ : syracuseStep 4258655 = 6387983) B6387983
theorem B2128747 : Blo 1260448 2128747 := bstep (se 1 (by rfl) ⟨1596560, by rfl⟩ : syracuseStep 2128747 = 3193121) B3193121
theorem B5389163 : Blo 1260448 5389163 := bstep (se 1 (by rfl) ⟨4041872, by rfl⟩ : syracuseStep 5389163 = 8083745) B8083745
theorem B1260463 : Blo 1260448 1260463 := bstep (se 1 (by rfl) ⟨945347, by rfl⟩ : syracuseStep 1260463 = 1890695) B1890695
theorem B1891247 : Blo 1260448 1891247 := bstep (se 1 (by rfl) ⟨1418435, by rfl⟩ : syracuseStep 1891247 = 2836871) B2836871
theorem B1596343 : Blo 1260448 1596343 := bstep (se 1 (by rfl) ⟨1197257, by rfl⟩ : syracuseStep 1596343 = 2394515) B2394515
theorem B1260487 : Blo 1260448 1260487 := bstep (se 1 (by rfl) ⟨945365, by rfl⟩ : syracuseStep 1260487 = 1890731) B1890731
theorem B1260507 : Blo 1260448 1260507 := bstep (se 1 (by rfl) ⟨945380, by rfl⟩ : syracuseStep 1260507 = 1890761) B1890761
theorem B4258817 : Blo 1260448 4258817 := bstep (se 2 (by rfl) ⟨1597056, by rfl⟩ : syracuseStep 4258817 = 3194113) B3194113
theorem B1891337 : Blo 1260448 1891337 := bstep (se 2 (by rfl) ⟨709251, by rfl⟩ : syracuseStep 1891337 = 1418503) B1418503
theorem B1260583 : Blo 1260448 1260583 := bstep (se 1 (by rfl) ⟨945437, by rfl⟩ : syracuseStep 1260583 = 1890875) B1890875
theorem B1891367 : Blo 1260448 1891367 := bstep (se 1 (by rfl) ⟨1418525, by rfl⟩ : syracuseStep 1891367 = 2837051) B2837051
theorem B8633411 : Blo 1260448 8633411 := bstep (se 1 (by rfl) ⟨6475058, by rfl⟩ : syracuseStep 8633411 = 12950117) B12950117
theorem B6814799 : Blo 1260448 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B1260623 : Blo 1260448 1260623 := bstep (se 1 (by rfl) ⟨945467, by rfl⟩ : syracuseStep 1260623 = 1890935) B1890935
theorem B1260639 : Blo 1260448 1260639 := bstep (se 1 (by rfl) ⟨945479, by rfl⟩ : syracuseStep 1260639 = 1890959) B1890959
theorem B1260667 : Blo 1260448 1260667 := bstep (se 1 (by rfl) ⟨945500, by rfl⟩ : syracuseStep 1260667 = 1891001) B1891001
theorem B1891451 : Blo 1260448 1891451 := bstep (se 1 (by rfl) ⟨1418588, by rfl⟩ : syracuseStep 1891451 = 2837177) B2837177
theorem B1260719 : Blo 1260448 1260719 := bstep (se 1 (by rfl) ⟨945539, by rfl⟩ : syracuseStep 1260719 = 1891079) B1891079
theorem B1260743 : Blo 1260448 1260743 := bstep (se 1 (by rfl) ⟨945557, by rfl⟩ : syracuseStep 1260743 = 1891115) B1891115
theorem B1260763 : Blo 1260448 1260763 := bstep (se 1 (by rfl) ⟨945572, by rfl⟩ : syracuseStep 1260763 = 1891145) B1891145
theorem B1891577 : Blo 1260448 1891577 := bstep (se 2 (by rfl) ⟨709341, by rfl⟩ : syracuseStep 1891577 = 1418683) B1418683
theorem B1260839 : Blo 1260448 1260839 := bstep (se 1 (by rfl) ⟨945629, by rfl⟩ : syracuseStep 1260839 = 1891259) B1891259
theorem B1260879 : Blo 1260448 1260879 := bstep (se 1 (by rfl) ⟨945659, by rfl⟩ : syracuseStep 1260879 = 1891319) B1891319
theorem B1260895 : Blo 1260448 1260895 := bstep (se 1 (by rfl) ⟨945671, by rfl⟩ : syracuseStep 1260895 = 1891343) B1891343
theorem B1891679 : Blo 1260448 1891679 := bstep (se 1 (by rfl) ⟨1418759, by rfl⟩ : syracuseStep 1891679 = 2837519) B2837519
theorem B1891691 : Blo 1260448 1891691 := bstep (se 1 (by rfl) ⟨1418768, by rfl⟩ : syracuseStep 1891691 = 2837537) B2837537
theorem B1260923 : Blo 1260448 1260923 := bstep (se 1 (by rfl) ⟨945692, by rfl⟩ : syracuseStep 1260923 = 1891385) B1891385
theorem B6389117 : Blo 1260448 6389117 := bstep (se 3 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 6389117 = 2395919) B2395919
theorem B3194255 : Blo 1260448 3194255 := bstep (se 1 (by rfl) ⟨2395691, by rfl⟩ : syracuseStep 3194255 = 4791383) B4791383
theorem B1260975 : Blo 1260448 1260975 := bstep (se 1 (by rfl) ⟨945731, by rfl⟩ : syracuseStep 1260975 = 1891463) B1891463
theorem B19946933 : Blo 1260448 19946933 := bstep (se 5 (by rfl) ⟨935012, by rfl⟩ : syracuseStep 19946933 = 1870025) B1870025
theorem B1260999 : Blo 1260448 1260999 := bstep (se 1 (by rfl) ⟨945749, by rfl⟩ : syracuseStep 1260999 = 1891499) B1891499
theorem B70024657 : Blo 1260448 70024657 := bstep (se 2 (by rfl) ⟨26259246, by rfl⟩ : syracuseStep 70024657 = 52518493) B52518493
theorem B1261019 : Blo 1260448 1261019 := bstep (se 1 (by rfl) ⟨945764, by rfl⟩ : syracuseStep 1261019 = 1891529) B1891529
theorem B1261095 : Blo 1260448 1261095 := bstep (se 1 (by rfl) ⟨945821, by rfl⟩ : syracuseStep 1261095 = 1891643) B1891643
theorem B1261135 : Blo 1260448 1261135 := bstep (se 1 (by rfl) ⟨945851, by rfl⟩ : syracuseStep 1261135 = 1891703) B1891703
theorem B1891919 : Blo 1260448 1891919 := bstep (se 1 (by rfl) ⟨1418939, by rfl⟩ : syracuseStep 1891919 = 2837879) B2837879
theorem B1261151 : Blo 1260448 1261151 := bstep (se 1 (by rfl) ⟨945863, by rfl⟩ : syracuseStep 1261151 = 1891727) B1891727
theorem B6381179 : Blo 1260448 6381179 := bstep (se 1 (by rfl) ⟨4785884, by rfl⟩ : syracuseStep 6381179 = 9571769) B9571769
theorem B1261179 : Blo 1260448 1261179 := bstep (se 1 (by rfl) ⟨945884, by rfl⟩ : syracuseStep 1261179 = 1891769) B1891769
theorem B1261231 : Blo 1260448 1261231 := bstep (se 1 (by rfl) ⟨945923, by rfl⟩ : syracuseStep 1261231 = 1891847) B1891847
theorem B1261255 : Blo 1260448 1261255 := bstep (se 1 (by rfl) ⟨945941, by rfl⟩ : syracuseStep 1261255 = 1891883) B1891883
theorem B1892039 : Blo 1260448 1892039 := bstep (se 1 (by rfl) ⟨1419029, by rfl⟩ : syracuseStep 1892039 = 2838059) B2838059
theorem B3194579 : Blo 1260448 3194579 := bstep (se 1 (by rfl) ⟨2395934, by rfl⟩ : syracuseStep 3194579 = 4791869) B4791869
theorem B1261275 : Blo 1260448 1261275 := bstep (se 1 (by rfl) ⟨945956, by rfl⟩ : syracuseStep 1261275 = 1891913) B1891913
theorem B20446991 : Blo 1260448 20446991 := bstep (se 1 (by rfl) ⟨15335243, by rfl⟩ : syracuseStep 20446991 = 30670487) B30670487
theorem B1261351 : Blo 1260448 1261351 := bstep (se 1 (by rfl) ⟨946013, by rfl⟩ : syracuseStep 1261351 = 1892027) B1892027
theorem B4259627 : Blo 1260448 4259627 := bstep (se 1 (by rfl) ⟨3194720, by rfl⟩ : syracuseStep 4259627 = 6389441) B6389441
theorem B1261391 : Blo 1260448 1261391 := bstep (se 1 (by rfl) ⟨946043, by rfl⟩ : syracuseStep 1261391 = 1892087) B1892087
theorem B1261407 : Blo 1260448 1261407 := bstep (se 1 (by rfl) ⟨946055, by rfl⟩ : syracuseStep 1261407 = 1892111) B1892111
theorem B1892201 : Blo 1260448 1892201 := bstep (se 2 (by rfl) ⟨709575, by rfl⟩ : syracuseStep 1892201 = 1419151) B1419151
theorem B1261435 : Blo 1260448 1261435 := bstep (se 1 (by rfl) ⟨946076, by rfl⟩ : syracuseStep 1261435 = 1892153) B1892153
theorem B2129807 : Blo 1260448 2129807 := bstep (se 1 (by rfl) ⟨1597355, by rfl⟩ : syracuseStep 2129807 = 3194711) B3194711
theorem B1261487 : Blo 1260448 1261487 := bstep (se 1 (by rfl) ⟨946115, by rfl⟩ : syracuseStep 1261487 = 1892231) B1892231
theorem B1892279 : Blo 1260448 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B1261511 : Blo 1260448 1261511 := bstep (se 1 (by rfl) ⟨946133, by rfl⟩ : syracuseStep 1261511 = 1892267) B1892267
theorem B1261531 : Blo 1260448 1261531 := bstep (se 1 (by rfl) ⟨946148, by rfl⟩ : syracuseStep 1261531 = 1892297) B1892297
theorem B1892315 : Blo 1260448 1892315 := bstep (se 1 (by rfl) ⟨1419236, by rfl⟩ : syracuseStep 1892315 = 2838473) B2838473
theorem B3031145 : Blo 1260448 3031145 := bstep (se 2 (by rfl) ⟨1136679, by rfl⟩ : syracuseStep 3031145 = 2273359) B2273359
theorem B94609619 : Blo 1260448 94609619 := bstep (se 1 (by rfl) ⟨70957214, by rfl⟩ : syracuseStep 94609619 = 141914429) B141914429
theorem B5390545 : Blo 1260448 5390545 := bstep (se 2 (by rfl) ⟨2021454, by rfl⟩ : syracuseStep 5390545 = 4042909) B4042909
theorem B6381827 : Blo 1260448 6381827 := bstep (se 1 (by rfl) ⟨4786370, by rfl⟩ : syracuseStep 6381827 = 9572741) B9572741
theorem B2130185 : Blo 1260448 2130185 := bstep (se 2 (by rfl) ⟨798819, by rfl⟩ : syracuseStep 2130185 = 1597639) B1597639
theorem B1261855 : Blo 1260448 1261855 := bstep (se 1 (by rfl) ⟨946391, by rfl⟩ : syracuseStep 1261855 = 1892783) B1892783
theorem B1597735 : Blo 1260448 1597735 := bstep (se 1 (by rfl) ⟨1198301, by rfl⟩ : syracuseStep 1597735 = 2396603) B2396603
theorem B6390089 : Blo 1260448 6390089 := bstep (se 2 (by rfl) ⟨2396283, by rfl⟩ : syracuseStep 6390089 = 4792567) B4792567
theorem B1892699 : Blo 1260448 1892699 := bstep (se 1 (by rfl) ⟨1419524, by rfl⟩ : syracuseStep 1892699 = 2839049) B2839049
theorem B1261915 : Blo 1260448 1261915 := bstep (se 1 (by rfl) ⟨946436, by rfl⟩ : syracuseStep 1261915 = 1892873) B1892873
theorem B3195227 : Blo 1260448 3195227 := bstep (se 1 (by rfl) ⟨2396420, by rfl⟩ : syracuseStep 3195227 = 4792841) B4792841
theorem B1261935 : Blo 1260448 1261935 := bstep (se 1 (by rfl) ⟨946451, by rfl⟩ : syracuseStep 1261935 = 1892903) B1892903
theorem B3195247 : Blo 1260448 3195247 := bstep (se 1 (by rfl) ⟨2396435, by rfl⟩ : syracuseStep 3195247 = 4792871) B4792871
theorem B1261991 : Blo 1260448 1261991 := bstep (se 1 (by rfl) ⟨946493, by rfl⟩ : syracuseStep 1261991 = 1892987) B1892987
theorem B12116425 : Blo 1260448 12116425 := bstep (se 2 (by rfl) ⟨4543659, by rfl⟩ : syracuseStep 12116425 = 9087319) B9087319
theorem B6144457 : Blo 1260448 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B1262075 : Blo 1260448 1262075 := bstep (se 1 (by rfl) ⟨946556, by rfl⟩ : syracuseStep 1262075 = 1893113) B1893113
theorem B2695675 : Blo 1260448 2695675 := bstep (se 1 (by rfl) ⟨2021756, by rfl⟩ : syracuseStep 2695675 = 4043513) B4043513
theorem B1892927 : Blo 1260448 1892927 := bstep (se 1 (by rfl) ⟨1419695, by rfl⟩ : syracuseStep 1892927 = 2839391) B2839391
theorem B1262143 : Blo 1260448 1262143 := bstep (se 1 (by rfl) ⟨946607, by rfl⟩ : syracuseStep 1262143 = 1893215) B1893215
theorem B6382151 : Blo 1260448 6382151 := bstep (se 1 (by rfl) ⟨4786613, by rfl⟩ : syracuseStep 6382151 = 9573227) B9573227
theorem B1262151 : Blo 1260448 1262151 := bstep (se 1 (by rfl) ⟨946613, by rfl⟩ : syracuseStep 1262151 = 1893227) B1893227
theorem B2048633 : Blo 1260448 2048633 := bstep (se 2 (by rfl) ⟨768237, by rfl⟩ : syracuseStep 2048633 = 1536475) B1536475
theorem B9093779 : Blo 1260448 9093779 := bstep (se 1 (by rfl) ⟨6820334, by rfl⟩ : syracuseStep 9093779 = 13640669) B13640669
theorem B4039321 : Blo 1260448 4039321 := bstep (se 2 (by rfl) ⟨1514745, by rfl⟩ : syracuseStep 4039321 = 3029491) B3029491
theorem B1893047 : Blo 1260448 1893047 := bstep (se 1 (by rfl) ⟨1419785, by rfl⟩ : syracuseStep 1893047 = 2839571) B2839571
theorem B1262303 : Blo 1260448 1262303 := bstep (se 1 (by rfl) ⟨946727, by rfl⟩ : syracuseStep 1262303 = 1893455) B1893455
theorem B18178789 : Blo 1260448 18178789 := bstep (se 4 (by rfl) ⟨1704261, by rfl⟩ : syracuseStep 18178789 = 3408523) B3408523
theorem B1262383 : Blo 1260448 1262383 := bstep (se 1 (by rfl) ⟨946787, by rfl⟩ : syracuseStep 1262383 = 1893575) B1893575
theorem B8086331 : Blo 1260448 8086331 := bstep (se 1 (by rfl) ⟨6064748, by rfl⟩ : syracuseStep 8086331 = 12129497) B12129497
theorem B1893275 : Blo 1260448 1893275 := bstep (se 1 (by rfl) ⟨1419956, by rfl⟩ : syracuseStep 1893275 = 2839913) B2839913
theorem B2393003 : Blo 1260448 2393003 := bstep (se 1 (by rfl) ⟨1794752, by rfl⟩ : syracuseStep 2393003 = 3589505) B3589505
theorem B1418215 : Blo 1260448 1418215 := bstep (se 1 (by rfl) ⟨1063661, by rfl⟩ : syracuseStep 1418215 = 2127323) B2127323
theorem B9585863 : Blo 1260448 9585863 := bstep (se 1 (by rfl) ⟨7189397, by rfl⟩ : syracuseStep 9585863 = 14378795) B14378795
theorem B3237079 : Blo 1260448 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B3409129 : Blo 1260448 3409129 := bstep (se 2 (by rfl) ⟨1278423, by rfl⟩ : syracuseStep 3409129 = 2556847) B2556847
theorem B2393383 : Blo 1260448 2393383 := bstep (se 1 (by rfl) ⟨1795037, by rfl⟩ : syracuseStep 2393383 = 3590075) B3590075
theorem B1893671 : Blo 1260448 1893671 := bstep (se 1 (by rfl) ⟨1420253, by rfl⟩ : syracuseStep 1893671 = 2840507) B2840507
theorem B2393543 : Blo 1260448 2393543 := bstep (se 1 (by rfl) ⟨1795157, by rfl⟩ : syracuseStep 2393543 = 3590315) B3590315
theorem B2836025 : Blo 1260448 2836025 := bstep (se 2 (by rfl) ⟨1063509, by rfl⟩ : syracuseStep 2836025 = 2127019) B2127019
theorem B6383447 : Blo 1260448 6383447 := bstep (se 1 (by rfl) ⟨4787585, by rfl⟩ : syracuseStep 6383447 = 9575171) B9575171
theorem B93366209 : Blo 1260448 93366209 := bstep (se 2 (by rfl) ⟨35012328, by rfl⟩ : syracuseStep 93366209 = 70024657) B70024657
theorem B7669741 : Blo 1260448 7669741 := bstep (se 3 (by rfl) ⟨1438076, by rfl⟩ : syracuseStep 7669741 = 2876153) B2876153
theorem B4548793 : Blo 1260448 4548793 := bstep (se 2 (by rfl) ⟨1705797, by rfl⟩ : syracuseStep 4548793 = 3411595) B3411595
theorem B2836691 : Blo 1260448 2836691 := bstep (se 1 (by rfl) ⟨2127518, by rfl⟩ : syracuseStep 2836691 = 4255037) B4255037
theorem B2836745 : Blo 1260448 2836745 := bstep (se 2 (by rfl) ⟨1063779, by rfl⟩ : syracuseStep 2836745 = 2127559) B2127559
theorem B13297955 : Blo 1260448 13297955 := bstep (se 1 (by rfl) ⟨9973466, by rfl⟩ : syracuseStep 13297955 = 19946933) B19946933
theorem B4254119 : Blo 1260448 4254119 := bstep (se 1 (by rfl) ⟨3190589, by rfl⟩ : syracuseStep 4254119 = 6381179) B6381179
theorem B18188711 : Blo 1260448 18188711 := bstep (se 1 (by rfl) ⟨13641533, by rfl⟩ : syracuseStep 18188711 = 27283067) B27283067
theorem B9095597 : Blo 1260448 9095597 := bstep (se 3 (by rfl) ⟨1705424, by rfl⟩ : syracuseStep 9095597 = 3410849) B3410849
theorem B2836961 : Blo 1260448 2836961 := bstep (se 2 (by rfl) ⟨1063860, by rfl⟩ : syracuseStep 2836961 = 2127721) B2127721
theorem B62253613 : Blo 1260448 62253613 := bstep (se 3 (by rfl) ⟨11672552, by rfl⟩ : syracuseStep 62253613 = 23345105) B23345105
theorem B4254281 : Blo 1260448 4254281 := bstep (se 2 (by rfl) ⟨1595355, by rfl⟩ : syracuseStep 4254281 = 3190711) B3190711
theorem B2394697 : Blo 1260448 2394697 := bstep (se 2 (by rfl) ⟨898011, by rfl⟩ : syracuseStep 2394697 = 1796023) B1796023
theorem B1419871 : Blo 1260448 1419871 := bstep (se 1 (by rfl) ⟨1064903, by rfl⟩ : syracuseStep 1419871 = 2129807) B2129807
theorem B10775213 : Blo 1260448 10775213 := bstep (se 3 (by rfl) ⟨2020352, by rfl⟩ : syracuseStep 10775213 = 4040705) B4040705
theorem B2878199 : Blo 1260448 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B2837267 : Blo 1260448 2837267 := bstep (se 1 (by rfl) ⟨2127950, by rfl⟩ : syracuseStep 2837267 = 4255901) B4255901
theorem B10775591 : Blo 1260448 10775591 := bstep (se 1 (by rfl) ⟨8081693, by rfl⟩ : syracuseStep 10775591 = 16163387) B16163387
theorem B30665807 : Blo 1260448 30665807 := bstep (se 1 (by rfl) ⟨22999355, by rfl⟩ : syracuseStep 30665807 = 45998711) B45998711
theorem B2837627 : Blo 1260448 2837627 := bstep (se 1 (by rfl) ⟨2128220, by rfl⟩ : syracuseStep 2837627 = 4256441) B4256441
theorem B2837753 : Blo 1260448 2837753 := bstep (se 2 (by rfl) ⟨1064157, by rfl⟩ : syracuseStep 2837753 = 2128315) B2128315
theorem B2837897 : Blo 1260448 2837897 := bstep (se 2 (by rfl) ⟨1064211, by rfl⟩ : syracuseStep 2837897 = 2128423) B2128423
theorem B2838023 : Blo 1260448 2838023 := bstep (se 1 (by rfl) ⟨2128517, by rfl⟩ : syracuseStep 2838023 = 4257035) B4257035
theorem B7179785 : Blo 1260448 7179785 := bstep (se 2 (by rfl) ⟨2692419, by rfl⟩ : syracuseStep 7179785 = 5384839) B5384839
theorem B12127805 : Blo 1260448 12127805 := bstep (se 3 (by rfl) ⟨2273963, by rfl⟩ : syracuseStep 12127805 = 4547927) B4547927
theorem B2838203 : Blo 1260448 2838203 := bstep (se 1 (by rfl) ⟨2128652, by rfl⟩ : syracuseStep 2838203 = 4257305) B4257305
theorem B2838329 : Blo 1260448 2838329 := bstep (se 2 (by rfl) ⟨1064373, by rfl⟩ : syracuseStep 2838329 = 2128747) B2128747
theorem B6385715 : Blo 1260448 6385715 := bstep (se 1 (by rfl) ⟨4789286, by rfl⟩ : syracuseStep 6385715 = 9578573) B9578573
theorem B10227779 : Blo 1260448 10227779 := bstep (se 1 (by rfl) ⟨7670834, by rfl⟩ : syracuseStep 10227779 = 15341669) B15341669
theorem B4255955 : Blo 1260448 4255955 := bstep (se 1 (by rfl) ⟨3191966, by rfl⟩ : syracuseStep 4255955 = 6383933) B6383933
theorem B3191147 : Blo 1260448 3191147 := bstep (se 1 (by rfl) ⟨2393360, by rfl⟩ : syracuseStep 3191147 = 4786721) B4786721
theorem B3412331 : Blo 1260448 3412331 := bstep (se 1 (by rfl) ⟨2559248, by rfl⟩ : syracuseStep 3412331 = 5118497) B5118497
theorem B2838959 : Blo 1260448 2838959 := bstep (se 1 (by rfl) ⟨2129219, by rfl⟩ : syracuseStep 2838959 = 4258439) B4258439
theorem B2838995 : Blo 1260448 2838995 := bstep (se 1 (by rfl) ⟨2129246, by rfl⟩ : syracuseStep 2838995 = 4258493) B4258493
theorem B4256225 : Blo 1260448 4256225 := bstep (se 2 (by rfl) ⟨1596084, by rfl⟩ : syracuseStep 4256225 = 3192169) B3192169
theorem B2396641 : Blo 1260448 2396641 := bstep (se 2 (by rfl) ⟨898740, by rfl⟩ : syracuseStep 2396641 = 1797481) B1797481
theorem B3191359 : Blo 1260448 3191359 := bstep (se 1 (by rfl) ⟨2393519, by rfl⟩ : syracuseStep 3191359 = 4787039) B4787039
theorem B2839103 : Blo 1260448 2839103 := bstep (se 1 (by rfl) ⟨2129327, by rfl⟩ : syracuseStep 2839103 = 4258655) B4258655
theorem B3592775 : Blo 1260448 3592775 := bstep (se 1 (by rfl) ⟨2694581, by rfl⟩ : syracuseStep 3592775 = 5389163) B5389163
theorem B2839211 : Blo 1260448 2839211 := bstep (se 1 (by rfl) ⟨2129408, by rfl⟩ : syracuseStep 2839211 = 4258817) B4258817
theorem B3191471 : Blo 1260448 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B5755607 : Blo 1260448 5755607 := bstep (se 1 (by rfl) ⟨4316705, by rfl⟩ : syracuseStep 5755607 = 8633411) B8633411
theorem B4543199 : Blo 1260448 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B3191795 : Blo 1260448 3191795 := bstep (se 1 (by rfl) ⟨2393846, by rfl⟩ : syracuseStep 3191795 = 4787693) B4787693
theorem B9098365 : Blo 1260448 9098365 := bstep (se 3 (by rfl) ⟨1705943, by rfl⟩ : syracuseStep 9098365 = 3411887) B3411887
theorem B56784017 : Blo 1260448 56784017 := bstep (se 2 (by rfl) ⟨21294006, by rfl⟩ : syracuseStep 56784017 = 42588013) B42588013
theorem B6821009 : Blo 1260448 6821009 := bstep (se 2 (by rfl) ⟨2557878, by rfl⟩ : syracuseStep 6821009 = 5115757) B5115757
theorem B3192007 : Blo 1260448 3192007 := bstep (se 1 (by rfl) ⟨2394005, by rfl⟩ : syracuseStep 3192007 = 4788011) B4788011
theorem B2839751 : Blo 1260448 2839751 := bstep (se 1 (by rfl) ⟨2129813, by rfl⟩ : syracuseStep 2839751 = 4259627) B4259627
theorem B7181561 : Blo 1260448 7181561 := bstep (se 2 (by rfl) ⟨2693085, by rfl⟩ : syracuseStep 7181561 = 5386171) B5386171
theorem B4314491 : Blo 1260448 4314491 := bstep (se 1 (by rfl) ⟨3235868, by rfl⟩ : syracuseStep 4314491 = 6471737) B6471737
theorem B2839931 : Blo 1260448 2839931 := bstep (se 1 (by rfl) ⟨2129948, by rfl⟩ : syracuseStep 2839931 = 4259897) B4259897
theorem B16176509 : Blo 1260448 16176509 := bstep (se 3 (by rfl) ⟨3033095, by rfl⟩ : syracuseStep 16176509 = 6066191) B6066191
theorem B2840057 : Blo 1260448 2840057 := bstep (se 2 (by rfl) ⟨1065021, by rfl⟩ : syracuseStep 2840057 = 2130043) B2130043
theorem B2840147 : Blo 1260448 2840147 := bstep (se 1 (by rfl) ⟨2130110, by rfl⟩ : syracuseStep 2840147 = 4260221) B4260221
theorem B32773733 : Blo 1260448 32773733 := bstep (se 4 (by rfl) ⟨3072537, by rfl⟩ : syracuseStep 32773733 = 6145075) B6145075
theorem B6141575 : Blo 1260448 6141575 := bstep (se 1 (by rfl) ⟨4606181, by rfl⟩ : syracuseStep 6141575 = 9212363) B9212363
theorem B6387335 : Blo 1260448 6387335 := bstep (se 1 (by rfl) ⟨4790501, by rfl⟩ : syracuseStep 6387335 = 9581003) B9581003
theorem B4257467 : Blo 1260448 4257467 := bstep (se 1 (by rfl) ⟨3193100, by rfl⟩ : syracuseStep 4257467 = 6386201) B6386201
theorem B3028715 : Blo 1260448 3028715 := bstep (se 1 (by rfl) ⟨2271536, by rfl⟩ : syracuseStep 3028715 = 4543073) B4543073
theorem B2840327 : Blo 1260448 2840327 := bstep (se 1 (by rfl) ⟨2130245, by rfl⟩ : syracuseStep 2840327 = 4260491) B4260491
theorem B9574199 : Blo 1260448 9574199 := bstep (se 1 (by rfl) ⟨7180649, by rfl⟩ : syracuseStep 9574199 = 14361299) B14361299
theorem B47298455 : Blo 1260448 47298455 := bstep (se 1 (by rfl) ⟨35473841, by rfl⟩ : syracuseStep 47298455 = 70947683) B70947683
theorem B24246539 : Blo 1260448 24246539 := bstep (se 1 (by rfl) ⟨18184904, by rfl⟩ : syracuseStep 24246539 = 36369809) B36369809
theorem B10778903 : Blo 1260448 10778903 := bstep (se 1 (by rfl) ⟨8084177, by rfl⟩ : syracuseStep 10778903 = 16168355) B16168355
theorem B2128295 : Blo 1260448 2128295 := bstep (se 1 (by rfl) ⟨1596221, by rfl⟩ : syracuseStep 2128295 = 3192443) B3192443
theorem B2955703 : Blo 1260448 2955703 := bstep (se 1 (by rfl) ⟨2216777, by rfl⟩ : syracuseStep 2955703 = 4433555) B4433555
theorem B12130879 : Blo 1260448 12130879 := bstep (se 1 (by rfl) ⟨9098159, by rfl⟩ : syracuseStep 12130879 = 18196319) B18196319
theorem B1890887 : Blo 1260448 1890887 := bstep (se 1 (by rfl) ⟨1418165, by rfl⟩ : syracuseStep 1890887 = 2836331) B2836331
theorem B3193415 : Blo 1260448 3193415 := bstep (se 1 (by rfl) ⟨2395061, by rfl⟩ : syracuseStep 3193415 = 4790123) B4790123
theorem B2128457 : Blo 1260448 2128457 := bstep (se 2 (by rfl) ⟨798171, by rfl⟩ : syracuseStep 2128457 = 1596343) B1596343
theorem B1890923 : Blo 1260448 1890923 := bstep (se 1 (by rfl) ⟨1418192, by rfl⟩ : syracuseStep 1890923 = 2836385) B2836385
theorem B3193465 : Blo 1260448 3193465 := bstep (se 2 (by rfl) ⟨1197549, by rfl⟩ : syracuseStep 3193465 = 2395099) B2395099
theorem B87374477 : Blo 1260448 87374477 := bstep (se 3 (by rfl) ⟨16382714, by rfl⟩ : syracuseStep 87374477 = 32765429) B32765429
theorem B1891151 : Blo 1260448 1891151 := bstep (se 1 (by rfl) ⟨1418363, by rfl⟩ : syracuseStep 1891151 = 2836727) B2836727
theorem B92044133 : Blo 1260448 92044133 := bstep (se 4 (by rfl) ⟨8629137, by rfl⟩ : syracuseStep 92044133 = 17258275) B17258275
theorem B1514395 : Blo 1260448 1514395 := bstep (se 1 (by rfl) ⟨1135796, by rfl⟩ : syracuseStep 1514395 = 2271593) B2271593
theorem B1260495 : Blo 1260448 1260495 := bstep (se 1 (by rfl) ⟨945371, by rfl⟩ : syracuseStep 1260495 = 1890743) B1890743
theorem B1260519 : Blo 1260448 1260519 := bstep (se 1 (by rfl) ⟨945389, by rfl⟩ : syracuseStep 1260519 = 1890779) B1890779
theorem B4922491 : Blo 1260448 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B1891547 : Blo 1260448 1891547 := bstep (se 1 (by rfl) ⟨1418660, by rfl⟩ : syracuseStep 1891547 = 2837321) B2837321
theorem B6388955 : Blo 1260448 6388955 := bstep (se 1 (by rfl) ⟨4791716, by rfl⟩ : syracuseStep 6388955 = 9583433) B9583433
theorem B2694377 : Blo 1260448 2694377 := bstep (se 2 (by rfl) ⟨1010391, by rfl⟩ : syracuseStep 2694377 = 2020783) B2020783
theorem B1260831 : Blo 1260448 1260831 := bstep (se 1 (by rfl) ⟨945623, by rfl⟩ : syracuseStep 1260831 = 1891247) B1891247
theorem B1260891 : Blo 1260448 1260891 := bstep (se 1 (by rfl) ⟨945668, by rfl⟩ : syracuseStep 1260891 = 1891337) B1891337
theorem B1596763 : Blo 1260448 1596763 := bstep (se 1 (by rfl) ⟨1197572, by rfl⟩ : syracuseStep 1596763 = 2395145) B2395145
theorem B1260911 : Blo 1260448 1260911 := bstep (se 1 (by rfl) ⟨945683, by rfl⟩ : syracuseStep 1260911 = 1891367) B1891367
theorem B1891721 : Blo 1260448 1891721 := bstep (se 2 (by rfl) ⟨709395, by rfl⟩ : syracuseStep 1891721 = 1418791) B1418791
theorem B3235211 : Blo 1260448 3235211 := bstep (se 1 (by rfl) ⟨2426408, by rfl⟩ : syracuseStep 3235211 = 4852817) B4852817
theorem B3071371 : Blo 1260448 3071371 := bstep (se 1 (by rfl) ⟨2303528, by rfl⟩ : syracuseStep 3071371 = 4607057) B4607057
theorem B1260967 : Blo 1260448 1260967 := bstep (se 1 (by rfl) ⟨945725, by rfl⟩ : syracuseStep 1260967 = 1891451) B1891451
theorem B1261051 : Blo 1260448 1261051 := bstep (se 1 (by rfl) ⟨945788, by rfl⟩ : syracuseStep 1261051 = 1891577) B1891577
theorem B5758489 : Blo 1260448 5758489 := bstep (se 2 (by rfl) ⟨2159433, by rfl⟩ : syracuseStep 5758489 = 4318867) B4318867
theorem B1261119 : Blo 1260448 1261119 := bstep (se 1 (by rfl) ⟨945839, by rfl⟩ : syracuseStep 1261119 = 1891679) B1891679
theorem B1596991 : Blo 1260448 1596991 := bstep (se 1 (by rfl) ⟨1197743, by rfl⟩ : syracuseStep 1596991 = 2395487) B2395487
theorem B1261127 : Blo 1260448 1261127 := bstep (se 1 (by rfl) ⟨945845, by rfl⟩ : syracuseStep 1261127 = 1891691) B1891691
theorem B4259411 : Blo 1260448 4259411 := bstep (se 1 (by rfl) ⟨3194558, by rfl⟩ : syracuseStep 4259411 = 6389117) B6389117
theorem B2129503 : Blo 1260448 2129503 := bstep (se 1 (by rfl) ⟨1597127, by rfl⟩ : syracuseStep 2129503 = 3194255) B3194255
theorem B5463713 : Blo 1260448 5463713 := bstep (se 2 (by rfl) ⟨2048892, by rfl⟩ : syracuseStep 5463713 = 4097785) B4097785
theorem B1261279 : Blo 1260448 1261279 := bstep (se 1 (by rfl) ⟨945959, by rfl⟩ : syracuseStep 1261279 = 1891919) B1891919
theorem B1892075 : Blo 1260448 1892075 := bstep (se 1 (by rfl) ⟨1419056, by rfl⟩ : syracuseStep 1892075 = 2838113) B2838113
theorem B1261359 : Blo 1260448 1261359 := bstep (se 1 (by rfl) ⟨946019, by rfl⟩ : syracuseStep 1261359 = 1892039) B1892039
theorem B2129719 : Blo 1260448 2129719 := bstep (se 1 (by rfl) ⟨1597289, by rfl⟩ : syracuseStep 2129719 = 3194579) B3194579
theorem B13631327 : Blo 1260448 13631327 := bstep (se 1 (by rfl) ⟨10223495, by rfl⟩ : syracuseStep 13631327 = 20446991) B20446991
theorem B1261467 : Blo 1260448 1261467 := bstep (se 1 (by rfl) ⟨946100, by rfl⟩ : syracuseStep 1261467 = 1892201) B1892201
theorem B1261519 : Blo 1260448 1261519 := bstep (se 1 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 1261519 = 1892279) B1892279
theorem B1892303 : Blo 1260448 1892303 := bstep (se 1 (by rfl) ⟨1419227, by rfl⟩ : syracuseStep 1892303 = 2838455) B2838455
theorem B1261543 : Blo 1260448 1261543 := bstep (se 1 (by rfl) ⟨946157, by rfl⟩ : syracuseStep 1261543 = 1892315) B1892315
theorem B4260059 : Blo 1260448 4260059 := bstep (se 1 (by rfl) ⟨3195044, by rfl⟩ : syracuseStep 4260059 = 6390089) B6390089
theorem B1261799 : Blo 1260448 1261799 := bstep (se 1 (by rfl) ⟨946349, by rfl⟩ : syracuseStep 1261799 = 1892699) B1892699
theorem B2130151 : Blo 1260448 2130151 := bstep (se 1 (by rfl) ⟨1597613, by rfl⟩ : syracuseStep 2130151 = 3195227) B3195227
theorem B1892639 : Blo 1260448 1892639 := bstep (se 1 (by rfl) ⟨1419479, by rfl⟩ : syracuseStep 1892639 = 2838959) B2838959
theorem B1892663 : Blo 1260448 1892663 := bstep (se 1 (by rfl) ⟨1419497, by rfl⟩ : syracuseStep 1892663 = 2838995) B2838995
theorem B141844853 : Blo 1260448 141844853 := bstep (se 5 (by rfl) ⟨6648977, by rfl⟩ : syracuseStep 141844853 = 13297955) B13297955
theorem B1892735 : Blo 1260448 1892735 := bstep (se 1 (by rfl) ⟨1419551, by rfl⟩ : syracuseStep 1892735 = 2839103) B2839103
theorem B1261951 : Blo 1260448 1261951 := bstep (se 1 (by rfl) ⟨946463, by rfl⟩ : syracuseStep 1261951 = 1892927) B1892927
theorem B2130313 : Blo 1260448 2130313 := bstep (se 2 (by rfl) ⟨798867, by rfl⟩ : syracuseStep 2130313 = 1597735) B1597735
theorem B6062519 : Blo 1260448 6062519 := bstep (se 1 (by rfl) ⟨4546889, by rfl⟩ : syracuseStep 6062519 = 9093779) B9093779
theorem B1892807 : Blo 1260448 1892807 := bstep (se 1 (by rfl) ⟨1419605, by rfl⟩ : syracuseStep 1892807 = 2839211) B2839211
theorem B1262031 : Blo 1260448 1262031 := bstep (se 1 (by rfl) ⟨946523, by rfl⟩ : syracuseStep 1262031 = 1893047) B1893047
theorem B4260329 : Blo 1260448 4260329 := bstep (se 2 (by rfl) ⟨1597623, by rfl⟩ : syracuseStep 4260329 = 3195247) B3195247
theorem B5390887 : Blo 1260448 5390887 := bstep (se 1 (by rfl) ⟨4043165, by rfl⟩ : syracuseStep 5390887 = 8086331) B8086331
theorem B3940937 : Blo 1260448 3940937 := bstep (se 2 (by rfl) ⟨1477851, by rfl⟩ : syracuseStep 3940937 = 2955703) B2955703
theorem B16155233 : Blo 1260448 16155233 := bstep (se 2 (by rfl) ⟨6058212, by rfl⟩ : syracuseStep 16155233 = 12116425) B12116425
theorem B8192609 : Blo 1260448 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B1262183 : Blo 1260448 1262183 := bstep (se 1 (by rfl) ⟨946637, by rfl⟩ : syracuseStep 1262183 = 1893275) B1893275
theorem B3195521 : Blo 1260448 3195521 := bstep (se 2 (by rfl) ⟨1198320, by rfl⟩ : syracuseStep 3195521 = 2396641) B2396641
theorem B37856011 : Blo 1260448 37856011 := bstep (se 1 (by rfl) ⟨28392008, by rfl⟩ : syracuseStep 37856011 = 56784017) B56784017
theorem B4547339 : Blo 1260448 4547339 := bstep (se 1 (by rfl) ⟨3410504, by rfl⟩ : syracuseStep 4547339 = 6821009) B6821009
theorem B1893161 : Blo 1260448 1893161 := bstep (se 2 (by rfl) ⟨709935, by rfl⟩ : syracuseStep 1893161 = 1419871) B1419871
theorem B1893167 : Blo 1260448 1893167 := bstep (se 1 (by rfl) ⟨1419875, by rfl⟩ : syracuseStep 1893167 = 2839751) B2839751
theorem B6390575 : Blo 1260448 6390575 := bstep (se 1 (by rfl) ⟨4792931, by rfl⟩ : syracuseStep 6390575 = 9585863) B9585863
theorem B1262447 : Blo 1260448 1262447 := bstep (se 1 (by rfl) ⟨946835, by rfl⟩ : syracuseStep 1262447 = 1893671) B1893671
theorem B2876327 : Blo 1260448 2876327 := bstep (se 1 (by rfl) ⟨2157245, by rfl⟩ : syracuseStep 2876327 = 4314491) B4314491
theorem B1893287 : Blo 1260448 1893287 := bstep (se 1 (by rfl) ⟨1419965, by rfl⟩ : syracuseStep 1893287 = 2839931) B2839931
theorem B1893371 : Blo 1260448 1893371 := bstep (se 1 (by rfl) ⟨1420028, by rfl⟩ : syracuseStep 1893371 = 2840057) B2840057
theorem B1893431 : Blo 1260448 1893431 := bstep (se 1 (by rfl) ⟨1420073, by rfl⟩ : syracuseStep 1893431 = 2840147) B2840147
theorem B21849155 : Blo 1260448 21849155 := bstep (se 1 (by rfl) ⟨16386866, by rfl⟩ : syracuseStep 21849155 = 32773733) B32773733
theorem B1893551 : Blo 1260448 1893551 := bstep (se 1 (by rfl) ⟨1420163, by rfl⟩ : syracuseStep 1893551 = 2840327) B2840327
theorem B6382799 : Blo 1260448 6382799 := bstep (se 1 (by rfl) ⟨4787099, by rfl⟩ : syracuseStep 6382799 = 9574199) B9574199
theorem B31532303 : Blo 1260448 31532303 := bstep (se 1 (by rfl) ⟨23649227, by rfl⟩ : syracuseStep 31532303 = 47298455) B47298455
theorem B62244139 : Blo 1260448 62244139 := bstep (se 1 (by rfl) ⟨46683104, by rfl⟩ : syracuseStep 62244139 = 93366209) B93366209
theorem B6563321 : Blo 1260448 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B16164359 : Blo 1260448 16164359 := bstep (se 1 (by rfl) ⟨12123269, by rfl⟩ : syracuseStep 16164359 = 24246539) B24246539
theorem B7185935 : Blo 1260448 7185935 := bstep (se 1 (by rfl) ⟨5389451, by rfl⟩ : syracuseStep 7185935 = 10778903) B10778903
theorem B2836079 : Blo 1260448 2836079 := bstep (se 1 (by rfl) ⟨2127059, by rfl⟩ : syracuseStep 2836079 = 4254119) B4254119
theorem B1418863 : Blo 1260448 1418863 := bstep (se 1 (by rfl) ⟨1064147, by rfl⟩ : syracuseStep 1418863 = 2128295) B2128295
theorem B12125807 : Blo 1260448 12125807 := bstep (se 1 (by rfl) ⟨9094355, by rfl⟩ : syracuseStep 12125807 = 18188711) B18188711
theorem B6063731 : Blo 1260448 6063731 := bstep (se 1 (by rfl) ⟨4547798, by rfl⟩ : syracuseStep 6063731 = 9095597) B9095597
theorem B2836187 : Blo 1260448 2836187 := bstep (se 1 (by rfl) ⟨2127140, by rfl⟩ : syracuseStep 2836187 = 4254281) B4254281
theorem B1418971 : Blo 1260448 1418971 := bstep (se 1 (by rfl) ⟨1064228, by rfl⟩ : syracuseStep 1418971 = 2128457) B2128457
theorem B1918799 : Blo 1260448 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B7677985 : Blo 1260448 7677985 := bstep (se 2 (by rfl) ⟨2879244, by rfl⟩ : syracuseStep 7677985 = 5758489) B5758489
theorem B1796251 : Blo 1260448 1796251 := bstep (se 1 (by rfl) ⟨1347188, by rfl⟩ : syracuseStep 1796251 = 2694377) B2694377
theorem B2156807 : Blo 1260448 2156807 := bstep (se 1 (by rfl) ⟨1617605, by rfl⟩ : syracuseStep 2156807 = 3235211) B3235211
theorem B4786523 : Blo 1260448 4786523 := bstep (se 1 (by rfl) ⟨3589892, by rfl⟩ : syracuseStep 4786523 = 7179785) B7179785
theorem B9087551 : Blo 1260448 9087551 := bstep (se 1 (by rfl) ⟨6815663, by rfl⟩ : syracuseStep 9087551 = 13631327) B13631327
theorem B10226321 : Blo 1260448 10226321 := bstep (se 2 (by rfl) ⟨3834870, by rfl⟩ : syracuseStep 10226321 = 7669741) B7669741
theorem B6818519 : Blo 1260448 6818519 := bstep (se 1 (by rfl) ⟨5113889, by rfl⟩ : syracuseStep 6818519 = 10227779) B10227779
theorem B2837303 : Blo 1260448 2837303 := bstep (se 1 (by rfl) ⟨2127977, by rfl⟩ : syracuseStep 2837303 = 4255955) B4255955
theorem B63073079 : Blo 1260448 63073079 := bstep (se 1 (by rfl) ⟨47304809, by rfl⟩ : syracuseStep 63073079 = 94609619) B94609619
theorem B4254551 : Blo 1260448 4254551 := bstep (se 1 (by rfl) ⟨3190913, by rfl⟩ : syracuseStep 4254551 = 6381827) B6381827
theorem B1420123 : Blo 1260448 1420123 := bstep (se 1 (by rfl) ⟨1065092, by rfl⟩ : syracuseStep 1420123 = 2130185) B2130185
theorem B6065057 : Blo 1260448 6065057 := bstep (se 2 (by rfl) ⟨2274396, by rfl⟩ : syracuseStep 6065057 = 4548793) B4548793
theorem B7187393 : Blo 1260448 7187393 := bstep (se 2 (by rfl) ⟨2695272, by rfl⟩ : syracuseStep 7187393 = 5390545) B5390545
theorem B2837483 : Blo 1260448 2837483 := bstep (se 1 (by rfl) ⟨2128112, by rfl⟩ : syracuseStep 2837483 = 4256225) B4256225
theorem B4254767 : Blo 1260448 4254767 := bstep (se 1 (by rfl) ⟨3191075, by rfl⟩ : syracuseStep 4254767 = 6382151) B6382151
theorem B2395183 : Blo 1260448 2395183 := bstep (se 1 (by rfl) ⟨1796387, by rfl⟩ : syracuseStep 2395183 = 3592775) B3592775
theorem B3837071 : Blo 1260448 3837071 := bstep (se 1 (by rfl) ⟨2877803, by rfl⟩ : syracuseStep 3837071 = 5755607) B5755607
theorem B4255145 : Blo 1260448 4255145 := bstep (se 2 (by rfl) ⟨1595679, by rfl⟩ : syracuseStep 4255145 = 3191359) B3191359
theorem B16174505 : Blo 1260448 16174505 := bstep (se 2 (by rfl) ⟨6065439, by rfl⟩ : syracuseStep 16174505 = 12130879) B12130879
theorem B4787707 : Blo 1260448 4787707 := bstep (se 1 (by rfl) ⟨3590780, by rfl⟩ : syracuseStep 4787707 = 7181561) B7181561
theorem B5385761 : Blo 1260448 5385761 := bstep (se 2 (by rfl) ⟨2019660, by rfl⟩ : syracuseStep 5385761 = 4039321) B4039321
theorem B10784339 : Blo 1260448 10784339 := bstep (se 1 (by rfl) ⟨8088254, by rfl⟩ : syracuseStep 10784339 = 16176509) B16176509
theorem B2838311 : Blo 1260448 2838311 := bstep (se 1 (by rfl) ⟨2128733, by rfl⟩ : syracuseStep 2838311 = 4257467) B4257467
theorem B2019143 : Blo 1260448 2019143 := bstep (se 1 (by rfl) ⟨1514357, by rfl⟩ : syracuseStep 2019143 = 3028715) B3028715
theorem B4255631 : Blo 1260448 4255631 := bstep (se 1 (by rfl) ⟨3191723, by rfl⟩ : syracuseStep 4255631 = 6383447) B6383447
theorem B4256009 : Blo 1260448 4256009 := bstep (se 2 (by rfl) ⟨1596003, by rfl⟩ : syracuseStep 4256009 = 3192007) B3192007
theorem B3191177 : Blo 1260448 3191177 := bstep (se 2 (by rfl) ⟨1196691, by rfl⟩ : syracuseStep 3191177 = 2393383) B2393383
theorem B14569901 : Blo 1260448 14569901 := bstep (se 3 (by rfl) ⟨2731856, by rfl⟩ : syracuseStep 14569901 = 5463713) B5463713
theorem B58249651 : Blo 1260448 58249651 := bstep (se 1 (by rfl) ⟨43687238, by rfl⟩ : syracuseStep 58249651 = 87374477) B87374477
theorem B61362755 : Blo 1260448 61362755 := bstep (se 1 (by rfl) ⟨46022066, by rfl⟩ : syracuseStep 61362755 = 92044133) B92044133
theorem B20443871 : Blo 1260448 20443871 := bstep (se 1 (by rfl) ⟨15332903, by rfl⟩ : syracuseStep 20443871 = 30665807) B30665807
theorem B2839337 : Blo 1260448 2839337 := bstep (se 2 (by rfl) ⟨1064751, by rfl⟩ : syracuseStep 2839337 = 2129503) B2129503
theorem B2839607 : Blo 1260448 2839607 := bstep (se 1 (by rfl) ⟨2129705, by rfl⟩ : syracuseStep 2839607 = 4259411) B4259411
theorem B2839625 : Blo 1260448 2839625 := bstep (se 2 (by rfl) ⟨1064859, by rfl⟩ : syracuseStep 2839625 = 2129719) B2129719
theorem B4257143 : Blo 1260448 4257143 := bstep (se 1 (by rfl) ⟨3192857, by rfl⟩ : syracuseStep 4257143 = 6385715) B6385715
theorem B2020763 : Blo 1260448 2020763 := bstep (se 1 (by rfl) ⟨1515572, by rfl⟩ : syracuseStep 2020763 = 3031145) B3031145
theorem B332019269 : Blo 1260448 332019269 := bstep (se 4 (by rfl) ⟨31126806, by rfl⟩ : syracuseStep 332019269 = 62253613) B62253613
theorem B2127431 : Blo 1260448 2127431 := bstep (se 1 (by rfl) ⟨1595573, by rfl⟩ : syracuseStep 2127431 = 3191147) B3191147
theorem B2274887 : Blo 1260448 2274887 := bstep (se 1 (by rfl) ⟨1706165, by rfl⟩ : syracuseStep 2274887 = 3412331) B3412331
theorem B1365755 : Blo 1260448 1365755 := bstep (se 1 (by rfl) ⟨1024316, by rfl⟩ : syracuseStep 1365755 = 2048633) B2048633
theorem B2127647 : Blo 1260448 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B3028799 : Blo 1260448 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B2127863 : Blo 1260448 2127863 := bstep (se 1 (by rfl) ⟨1595897, by rfl⟩ : syracuseStep 2127863 = 3191795) B3191795
theorem B3594233 : Blo 1260448 3594233 := bstep (se 2 (by rfl) ⟨1347837, by rfl⟩ : syracuseStep 3594233 = 2695675) B2695675
theorem B3192929 : Blo 1260448 3192929 := bstep (se 2 (by rfl) ⟨1197348, by rfl⟩ : syracuseStep 3192929 = 2394697) B2394697
theorem B4257953 : Blo 1260448 4257953 := bstep (se 2 (by rfl) ⟨1596732, by rfl⟩ : syracuseStep 4257953 = 3193465) B3193465
theorem B1595695 : Blo 1260448 1595695 := bstep (se 1 (by rfl) ⟨1196771, by rfl⟩ : syracuseStep 1595695 = 2393543) B2393543
theorem B24238385 : Blo 1260448 24238385 := bstep (se 2 (by rfl) ⟨9089394, by rfl⟩ : syracuseStep 24238385 = 18178789) B18178789
theorem B1890683 : Blo 1260448 1890683 := bstep (se 1 (by rfl) ⟨1418012, by rfl⟩ : syracuseStep 1890683 = 2836025) B2836025
theorem B4094383 : Blo 1260448 4094383 := bstep (se 1 (by rfl) ⟨3070787, by rfl⟩ : syracuseStep 4094383 = 6141575) B6141575
theorem B4258223 : Blo 1260448 4258223 := bstep (se 1 (by rfl) ⟨3193667, by rfl⟩ : syracuseStep 4258223 = 6387335) B6387335
theorem B1890953 : Blo 1260448 1890953 := bstep (se 2 (by rfl) ⟨709107, by rfl⟩ : syracuseStep 1890953 = 1418215) B1418215
theorem B1891127 : Blo 1260448 1891127 := bstep (se 1 (by rfl) ⟨1418345, by rfl⟩ : syracuseStep 1891127 = 2836691) B2836691
theorem B12131153 : Blo 1260448 12131153 := bstep (se 2 (by rfl) ⟨4549182, by rfl⟩ : syracuseStep 12131153 = 9098365) B9098365
theorem B1891163 : Blo 1260448 1891163 := bstep (se 1 (by rfl) ⟨1418372, by rfl⟩ : syracuseStep 1891163 = 2836745) B2836745
theorem B4316105 : Blo 1260448 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B4545505 : Blo 1260448 4545505 := bstep (se 2 (by rfl) ⟨1704564, by rfl⟩ : syracuseStep 4545505 = 3409129) B3409129
theorem B1891307 : Blo 1260448 1891307 := bstep (se 1 (by rfl) ⟨1418480, by rfl⟩ : syracuseStep 1891307 = 2836961) B2836961
theorem B1260591 : Blo 1260448 1260591 := bstep (se 1 (by rfl) ⟨945443, by rfl⟩ : syracuseStep 1260591 = 1890887) B1890887
theorem B2128943 : Blo 1260448 2128943 := bstep (se 1 (by rfl) ⟨1596707, by rfl⟩ : syracuseStep 2128943 = 3193415) B3193415
theorem B1260615 : Blo 1260448 1260615 := bstep (se 1 (by rfl) ⟨945461, by rfl⟩ : syracuseStep 1260615 = 1890923) B1890923
theorem B7183475 : Blo 1260448 7183475 := bstep (se 1 (by rfl) ⟨5387606, by rfl⟩ : syracuseStep 7183475 = 10775213) B10775213
theorem B2129017 : Blo 1260448 2129017 := bstep (se 2 (by rfl) ⟨798381, by rfl⟩ : syracuseStep 2129017 = 1596763) B1596763
theorem B1891511 : Blo 1260448 1891511 := bstep (se 1 (by rfl) ⟨1418633, by rfl⟩ : syracuseStep 1891511 = 2837267) B2837267
theorem B4095161 : Blo 1260448 4095161 := bstep (se 2 (by rfl) ⟨1535685, by rfl⟩ : syracuseStep 4095161 = 3071371) B3071371
theorem B1260767 : Blo 1260448 1260767 := bstep (se 1 (by rfl) ⟨945575, by rfl⟩ : syracuseStep 1260767 = 1891151) B1891151
theorem B7183727 : Blo 1260448 7183727 := bstep (se 1 (by rfl) ⟨5387795, by rfl⟩ : syracuseStep 7183727 = 10775591) B10775591
theorem B1891751 : Blo 1260448 1891751 := bstep (se 1 (by rfl) ⟨1418813, by rfl⟩ : syracuseStep 1891751 = 2837627) B2837627
theorem B2129321 : Blo 1260448 2129321 := bstep (se 2 (by rfl) ⟨798495, by rfl⟩ : syracuseStep 2129321 = 1596991) B1596991
theorem B8076773 : Blo 1260448 8076773 := bstep (se 4 (by rfl) ⟨757197, by rfl⟩ : syracuseStep 8076773 = 1514395) B1514395
theorem B1261031 : Blo 1260448 1261031 := bstep (se 1 (by rfl) ⟨945773, by rfl⟩ : syracuseStep 1261031 = 1891547) B1891547
theorem B4259303 : Blo 1260448 4259303 := bstep (se 1 (by rfl) ⟨3194477, by rfl⟩ : syracuseStep 4259303 = 6388955) B6388955
theorem B1891835 : Blo 1260448 1891835 := bstep (se 1 (by rfl) ⟨1418876, by rfl⟩ : syracuseStep 1891835 = 2837753) B2837753
theorem B1261147 : Blo 1260448 1261147 := bstep (se 1 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 1261147 = 1891721) B1891721
theorem B1891931 : Blo 1260448 1891931 := bstep (se 1 (by rfl) ⟨1418948, by rfl⟩ : syracuseStep 1891931 = 2837897) B2837897
theorem B1892015 : Blo 1260448 1892015 := bstep (se 1 (by rfl) ⟨1419011, by rfl⟩ : syracuseStep 1892015 = 2838023) B2838023
theorem B8085203 : Blo 1260448 8085203 := bstep (se 1 (by rfl) ⟨6063902, by rfl⟩ : syracuseStep 8085203 = 12127805) B12127805
theorem B6381341 : Blo 1260448 6381341 := bstep (se 3 (by rfl) ⟨1196501, by rfl⟩ : syracuseStep 6381341 = 2393003) B2393003
theorem B1892135 : Blo 1260448 1892135 := bstep (se 1 (by rfl) ⟨1419101, by rfl⟩ : syracuseStep 1892135 = 2838203) B2838203
theorem B1261383 : Blo 1260448 1261383 := bstep (se 1 (by rfl) ⟨946037, by rfl⟩ : syracuseStep 1261383 = 1892075) B1892075
theorem B1892219 : Blo 1260448 1892219 := bstep (se 1 (by rfl) ⟨1419164, by rfl⟩ : syracuseStep 1892219 = 2838329) B2838329
theorem B1261535 : Blo 1260448 1261535 := bstep (se 1 (by rfl) ⟨946151, by rfl⟩ : syracuseStep 1261535 = 1892303) B1892303
theorem B1261759 : Blo 1260448 1261759 := bstep (se 1 (by rfl) ⟨946319, by rfl⟩ : syracuseStep 1261759 = 1892639) B1892639
theorem B1261775 : Blo 1260448 1261775 := bstep (se 1 (by rfl) ⟨946331, by rfl⟩ : syracuseStep 1261775 = 1892663) B1892663
theorem B1261823 : Blo 1260448 1261823 := bstep (se 1 (by rfl) ⟨946367, by rfl⟩ : syracuseStep 1261823 = 1892735) B1892735
theorem B1261871 : Blo 1260448 1261871 := bstep (se 1 (by rfl) ⟨946403, by rfl⟩ : syracuseStep 1261871 = 1892807) B1892807
theorem B10232189 : Blo 1260448 10232189 := bstep (se 3 (by rfl) ⟨1918535, by rfl⟩ : syracuseStep 10232189 = 3837071) B3837071
theorem B2130347 : Blo 1260448 2130347 := bstep (se 1 (by rfl) ⟨1597760, by rfl⟩ : syracuseStep 2130347 = 3195521) B3195521
theorem B3031559 : Blo 1260448 3031559 := bstep (se 1 (by rfl) ⟨2273669, by rfl⟩ : syracuseStep 3031559 = 4547339) B4547339
theorem B1892891 : Blo 1260448 1892891 := bstep (se 1 (by rfl) ⟨1419668, by rfl⟩ : syracuseStep 1892891 = 2839337) B2839337
theorem B1262107 : Blo 1260448 1262107 := bstep (se 1 (by rfl) ⟨946580, by rfl⟩ : syracuseStep 1262107 = 1893161) B1893161
theorem B1262111 : Blo 1260448 1262111 := bstep (se 1 (by rfl) ⟨946583, by rfl⟩ : syracuseStep 1262111 = 1893167) B1893167
theorem B4260383 : Blo 1260448 4260383 := bstep (se 1 (by rfl) ⟨3195287, by rfl⟩ : syracuseStep 4260383 = 6390575) B6390575
theorem B1917551 : Blo 1260448 1917551 := bstep (se 1 (by rfl) ⟨1438163, by rfl⟩ : syracuseStep 1917551 = 2876327) B2876327
theorem B1262191 : Blo 1260448 1262191 := bstep (se 1 (by rfl) ⟨946643, by rfl⟩ : syracuseStep 1262191 = 1893287) B1893287
theorem B1262247 : Blo 1260448 1262247 := bstep (se 1 (by rfl) ⟨946685, by rfl⟩ : syracuseStep 1262247 = 1893371) B1893371
theorem B5751485 : Blo 1260448 5751485 := bstep (se 3 (by rfl) ⟨1078403, by rfl⟩ : syracuseStep 5751485 = 2156807) B2156807
theorem B1893071 : Blo 1260448 1893071 := bstep (se 1 (by rfl) ⟨1419803, by rfl⟩ : syracuseStep 1893071 = 2839607) B2839607
theorem B1262287 : Blo 1260448 1262287 := bstep (se 1 (by rfl) ⟨946715, by rfl⟩ : syracuseStep 1262287 = 1893431) B1893431
theorem B14566103 : Blo 1260448 14566103 := bstep (se 1 (by rfl) ⟨10924577, by rfl⟩ : syracuseStep 14566103 = 21849155) B21849155
theorem B1893083 : Blo 1260448 1893083 := bstep (se 1 (by rfl) ⟨1419812, by rfl⟩ : syracuseStep 1893083 = 2839625) B2839625
theorem B1262367 : Blo 1260448 1262367 := bstep (se 1 (by rfl) ⟨946775, by rfl⟩ : syracuseStep 1262367 = 1893551) B1893551
theorem B21021535 : Blo 1260448 21021535 := bstep (se 1 (by rfl) ⟨15766151, by rfl⟩ : syracuseStep 21021535 = 31532303) B31532303
theorem B4375547 : Blo 1260448 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B1418287 : Blo 1260448 1418287 := bstep (se 1 (by rfl) ⟨1063715, by rfl⟩ : syracuseStep 1418287 = 2127431) B2127431
theorem B1516591 : Blo 1260448 1516591 := bstep (se 1 (by rfl) ⟨1137443, by rfl⟩ : syracuseStep 1516591 = 2274887) B2274887
theorem B1893497 : Blo 1260448 1893497 := bstep (se 2 (by rfl) ⟨710061, by rfl⟩ : syracuseStep 1893497 = 1420123) B1420123
theorem B1418431 : Blo 1260448 1418431 := bstep (se 1 (by rfl) ⟨1063823, by rfl⟩ : syracuseStep 1418431 = 2127647) B2127647
theorem B1279199 : Blo 1260448 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B1418575 : Blo 1260448 1418575 := bstep (se 1 (by rfl) ⟨1063931, by rfl⟩ : syracuseStep 1418575 = 2127863) B2127863
theorem B6817547 : Blo 1260448 6817547 := bstep (se 1 (by rfl) ⟨5113160, by rfl⟩ : syracuseStep 6817547 = 10226321) B10226321
theorem B8087435 : Blo 1260448 8087435 := bstep (se 1 (by rfl) ⟨6065576, by rfl⟩ : syracuseStep 8087435 = 12131153) B12131153
theorem B2836367 : Blo 1260448 2836367 := bstep (se 1 (by rfl) ⟨2127275, by rfl⟩ : syracuseStep 2836367 = 4254551) B4254551
theorem B6383609 : Blo 1260448 6383609 := bstep (se 2 (by rfl) ⟨2393853, by rfl⟩ : syracuseStep 6383609 = 4787707) B4787707
theorem B2836511 : Blo 1260448 2836511 := bstep (se 1 (by rfl) ⟨2127383, by rfl⟩ : syracuseStep 2836511 = 4254767) B4254767
theorem B1419295 : Blo 1260448 1419295 := bstep (se 1 (by rfl) ⟨1064471, by rfl⟩ : syracuseStep 1419295 = 2128943) B2128943
theorem B2730107 : Blo 1260448 2730107 := bstep (se 1 (by rfl) ⟨2047580, by rfl⟩ : syracuseStep 2730107 = 4095161) B4095161
theorem B2836763 : Blo 1260448 2836763 := bstep (se 1 (by rfl) ⟨2127572, by rfl⟩ : syracuseStep 2836763 = 4255145) B4255145
theorem B1419547 : Blo 1260448 1419547 := bstep (se 1 (by rfl) ⟨1064660, by rfl⟩ : syracuseStep 1419547 = 2129321) B2129321
theorem B10783003 : Blo 1260448 10783003 := bstep (se 1 (by rfl) ⟨8087252, by rfl⟩ : syracuseStep 10783003 = 16174505) B16174505
theorem B5384515 : Blo 1260448 5384515 := bstep (se 1 (by rfl) ⟨4038386, by rfl⟩ : syracuseStep 5384515 = 8076773) B8076773
theorem B3590507 : Blo 1260448 3590507 := bstep (se 1 (by rfl) ⟨2692880, by rfl⟩ : syracuseStep 3590507 = 5385761) B5385761
theorem B4254227 : Blo 1260448 4254227 := bstep (se 1 (by rfl) ⟨3190670, by rfl⟩ : syracuseStep 4254227 = 6381341) B6381341
theorem B1346095 : Blo 1260448 1346095 := bstep (se 1 (by rfl) ⟨1009571, by rfl⟩ : syracuseStep 1346095 = 2019143) B2019143
theorem B2837087 : Blo 1260448 2837087 := bstep (se 1 (by rfl) ⟨2127815, by rfl⟩ : syracuseStep 2837087 = 4255631) B4255631
theorem B2837339 : Blo 1260448 2837339 := bstep (se 1 (by rfl) ⟨2128004, by rfl⟩ : syracuseStep 2837339 = 4256009) B4256009
theorem B2395001 : Blo 1260448 2395001 := bstep (se 2 (by rfl) ⟨898125, by rfl⟩ : syracuseStep 2395001 = 1796251) B1796251
theorem B94563235 : Blo 1260448 94563235 := bstep (se 1 (by rfl) ⟨70922426, by rfl⟩ : syracuseStep 94563235 = 141844853) B141844853
theorem B4041679 : Blo 1260448 4041679 := bstep (se 1 (by rfl) ⟨3031259, by rfl⟩ : syracuseStep 4041679 = 6062519) B6062519
theorem B5459177 : Blo 1260448 5459177 := bstep (se 2 (by rfl) ⟨2047191, by rfl⟩ : syracuseStep 5459177 = 4094383) B4094383
theorem B7187849 : Blo 1260448 7187849 := bstep (se 2 (by rfl) ⟨2695443, by rfl⟩ : syracuseStep 7187849 = 5390887) B5390887
theorem B42036661 : Blo 1260448 42036661 := bstep (se 5 (by rfl) ⟨1970468, by rfl⟩ : syracuseStep 42036661 = 3940937) B3940937
theorem B4255199 : Blo 1260448 4255199 := bstep (se 1 (by rfl) ⟨3191399, by rfl⟩ : syracuseStep 4255199 = 6382799) B6382799
theorem B2838095 : Blo 1260448 2838095 := bstep (se 1 (by rfl) ⟨2128571, by rfl⟩ : syracuseStep 2838095 = 4257143) B4257143
theorem B1347175 : Blo 1260448 1347175 := bstep (se 1 (by rfl) ⟨1010381, by rfl⟩ : syracuseStep 1347175 = 2020763) B2020763
theorem B10776239 : Blo 1260448 10776239 := bstep (se 1 (by rfl) ⟨8082179, by rfl⟩ : syracuseStep 10776239 = 16164359) B16164359
theorem B50474681 : Blo 1260448 50474681 := bstep (se 2 (by rfl) ⟨18928005, by rfl⟩ : syracuseStep 50474681 = 37856011) B37856011
theorem B4042487 : Blo 1260448 4042487 := bstep (se 1 (by rfl) ⟨3031865, by rfl⟩ : syracuseStep 4042487 = 6063731) B6063731
theorem B2396155 : Blo 1260448 2396155 := bstep (se 1 (by rfl) ⟨1797116, by rfl⟩ : syracuseStep 2396155 = 3594233) B3594233
theorem B2838635 : Blo 1260448 2838635 := bstep (se 1 (by rfl) ⟨2128976, by rfl⟩ : syracuseStep 2838635 = 4257953) B4257953
theorem B2838689 : Blo 1260448 2838689 := bstep (se 2 (by rfl) ⟨1064508, by rfl⟩ : syracuseStep 2838689 = 2129017) B2129017
theorem B16158923 : Blo 1260448 16158923 := bstep (se 1 (by rfl) ⟨12119192, by rfl⟩ : syracuseStep 16158923 = 24238385) B24238385
theorem B3191015 : Blo 1260448 3191015 := bstep (se 1 (by rfl) ⟨2393261, by rfl⟩ : syracuseStep 3191015 = 4786523) B4786523
theorem B2838815 : Blo 1260448 2838815 := bstep (se 1 (by rfl) ⟨2129111, by rfl⟩ : syracuseStep 2838815 = 4258223) B4258223
theorem B6058367 : Blo 1260448 6058367 := bstep (se 1 (by rfl) ⟨4543775, by rfl⟩ : syracuseStep 6058367 = 9087551) B9087551
theorem B18182717 : Blo 1260448 18182717 := bstep (se 3 (by rfl) ⟨3409259, by rfl⟩ : syracuseStep 18182717 = 6818519) B6818519
theorem B4043371 : Blo 1260448 4043371 := bstep (se 1 (by rfl) ⟨3032528, by rfl⟩ : syracuseStep 4043371 = 6065057) B6065057
theorem B3642013 : Blo 1260448 3642013 := bstep (se 3 (by rfl) ⟨682877, by rfl⟩ : syracuseStep 3642013 = 1365755) B1365755
theorem B4788983 : Blo 1260448 4788983 := bstep (se 1 (by rfl) ⟨3591737, by rfl⟩ : syracuseStep 4788983 = 7183475) B7183475
theorem B4789151 : Blo 1260448 4789151 := bstep (se 1 (by rfl) ⟨3591863, by rfl⟩ : syracuseStep 4789151 = 7183727) B7183727
theorem B2839535 : Blo 1260448 2839535 := bstep (se 1 (by rfl) ⟨2129651, by rfl⟩ : syracuseStep 2839535 = 4259303) B4259303
theorem B7189559 : Blo 1260448 7189559 := bstep (se 1 (by rfl) ⟨5392169, by rfl⟩ : syracuseStep 7189559 = 10784339) B10784339
theorem B10237313 : Blo 1260448 10237313 := bstep (se 2 (by rfl) ⟨3838992, by rfl⟩ : syracuseStep 10237313 = 7677985) B7677985
theorem B2840039 : Blo 1260448 2840039 := bstep (se 1 (by rfl) ⟨2130029, by rfl⟩ : syracuseStep 2840039 = 4260059) B4260059
theorem B2127451 : Blo 1260448 2127451 := bstep (se 1 (by rfl) ⟨1595588, by rfl⟩ : syracuseStep 2127451 = 3191177) B3191177
theorem B9713267 : Blo 1260448 9713267 := bstep (se 1 (by rfl) ⟨7284950, by rfl⟩ : syracuseStep 9713267 = 14569901) B14569901
theorem B2840201 : Blo 1260448 2840201 := bstep (se 2 (by rfl) ⟨1065075, by rfl⟩ : syracuseStep 2840201 = 2130151) B2130151
theorem B2840219 : Blo 1260448 2840219 := bstep (se 1 (by rfl) ⟨2130164, by rfl⟩ : syracuseStep 2840219 = 4260329) B4260329
theorem B40908503 : Blo 1260448 40908503 := bstep (se 1 (by rfl) ⟨30681377, by rfl⟩ : syracuseStep 40908503 = 61362755) B61362755
theorem B2127593 : Blo 1260448 2127593 := bstep (se 2 (by rfl) ⟨797847, by rfl⟩ : syracuseStep 2127593 = 1595695) B1595695
theorem B10770155 : Blo 1260448 10770155 := bstep (se 1 (by rfl) ⟨8077616, by rfl⟩ : syracuseStep 10770155 = 16155233) B16155233
theorem B5461739 : Blo 1260448 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B2840417 : Blo 1260448 2840417 := bstep (se 2 (by rfl) ⟨1065156, by rfl⟩ : syracuseStep 2840417 = 2130313) B2130313
theorem B77666201 : Blo 1260448 77666201 := bstep (se 2 (by rfl) ⟨29124825, by rfl⟩ : syracuseStep 77666201 = 58249651) B58249651
theorem B4790623 : Blo 1260448 4790623 := bstep (se 1 (by rfl) ⟨3592967, by rfl⟩ : syracuseStep 4790623 = 7185935) B7185935
theorem B221346179 : Blo 1260448 221346179 := bstep (se 1 (by rfl) ⟨166009634, by rfl⟩ : syracuseStep 221346179 = 332019269) B332019269
theorem B1890719 : Blo 1260448 1890719 := bstep (se 1 (by rfl) ⟨1418039, by rfl⟩ : syracuseStep 1890719 = 2836079) B2836079
theorem B8083871 : Blo 1260448 8083871 := bstep (se 1 (by rfl) ⟨6062903, by rfl⟩ : syracuseStep 8083871 = 12125807) B12125807
theorem B1890791 : Blo 1260448 1890791 := bstep (se 1 (by rfl) ⟨1418093, by rfl⟩ : syracuseStep 1890791 = 2836187) B2836187
theorem B6060673 : Blo 1260448 6060673 := bstep (se 2 (by rfl) ⟨2272752, by rfl⟩ : syracuseStep 6060673 = 4545505) B4545505
theorem B3193577 : Blo 1260448 3193577 := bstep (se 2 (by rfl) ⟨1197591, by rfl⟩ : syracuseStep 3193577 = 2395183) B2395183
theorem B2128619 : Blo 1260448 2128619 := bstep (se 1 (by rfl) ⟨1596464, by rfl⟩ : syracuseStep 2128619 = 3192929) B3192929
theorem B1260455 : Blo 1260448 1260455 := bstep (se 1 (by rfl) ⟨945341, by rfl⟩ : syracuseStep 1260455 = 1890683) B1890683
theorem B82992185 : Blo 1260448 82992185 := bstep (se 2 (by rfl) ⟨31122069, by rfl⟩ : syracuseStep 82992185 = 62244139) B62244139
theorem B1260635 : Blo 1260448 1260635 := bstep (se 1 (by rfl) ⟨945476, by rfl⟩ : syracuseStep 1260635 = 1890953) B1890953
theorem B1260751 : Blo 1260448 1260751 := bstep (se 1 (by rfl) ⟨945563, by rfl⟩ : syracuseStep 1260751 = 1891127) B1891127
theorem B1891535 : Blo 1260448 1891535 := bstep (se 1 (by rfl) ⟨1418651, by rfl⟩ : syracuseStep 1891535 = 2837303) B2837303
theorem B42048719 : Blo 1260448 42048719 := bstep (se 1 (by rfl) ⟨31536539, by rfl⟩ : syracuseStep 42048719 = 63073079) B63073079
theorem B1260775 : Blo 1260448 1260775 := bstep (se 1 (by rfl) ⟨945581, by rfl⟩ : syracuseStep 1260775 = 1891163) B1891163
theorem B54516989 : Blo 1260448 54516989 := bstep (se 3 (by rfl) ⟨10221935, by rfl⟩ : syracuseStep 54516989 = 20443871) B20443871
theorem B4791595 : Blo 1260448 4791595 := bstep (se 1 (by rfl) ⟨3593696, by rfl⟩ : syracuseStep 4791595 = 7187393) B7187393
theorem B1260871 : Blo 1260448 1260871 := bstep (se 1 (by rfl) ⟨945653, by rfl⟩ : syracuseStep 1260871 = 1891307) B1891307
theorem B1891655 : Blo 1260448 1891655 := bstep (se 1 (by rfl) ⟨1418741, by rfl⟩ : syracuseStep 1891655 = 2837483) B2837483
theorem B1261007 : Blo 1260448 1261007 := bstep (se 1 (by rfl) ⟨945755, by rfl⟩ : syracuseStep 1261007 = 1891511) B1891511
theorem B1891817 : Blo 1260448 1891817 := bstep (se 2 (by rfl) ⟨709431, by rfl⟩ : syracuseStep 1891817 = 1418863) B1418863
theorem B8076797 : Blo 1260448 8076797 := bstep (se 3 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 8076797 = 3028799) B3028799
theorem B1261167 : Blo 1260448 1261167 := bstep (se 1 (by rfl) ⟨945875, by rfl⟩ : syracuseStep 1261167 = 1891751) B1891751
theorem B1891961 : Blo 1260448 1891961 := bstep (se 2 (by rfl) ⟨709485, by rfl⟩ : syracuseStep 1891961 = 1418971) B1418971
theorem B1261223 : Blo 1260448 1261223 := bstep (se 1 (by rfl) ⟨945917, by rfl⟩ : syracuseStep 1261223 = 1891835) B1891835
theorem B1261287 : Blo 1260448 1261287 := bstep (se 1 (by rfl) ⟨945965, by rfl⟩ : syracuseStep 1261287 = 1891931) B1891931
theorem B1261343 : Blo 1260448 1261343 := bstep (se 1 (by rfl) ⟨946007, by rfl⟩ : syracuseStep 1261343 = 1892015) B1892015
theorem B5390135 : Blo 1260448 5390135 := bstep (se 1 (by rfl) ⟨4042601, by rfl⟩ : syracuseStep 5390135 = 8085203) B8085203
theorem B11509613 : Blo 1260448 11509613 := bstep (se 3 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 11509613 = 4316105) B4316105
theorem B1261423 : Blo 1260448 1261423 := bstep (se 1 (by rfl) ⟨946067, by rfl⟩ : syracuseStep 1261423 = 1892135) B1892135
theorem B1892207 : Blo 1260448 1892207 := bstep (se 1 (by rfl) ⟨1419155, by rfl⟩ : syracuseStep 1892207 = 2838311) B2838311
theorem B1261479 : Blo 1260448 1261479 := bstep (se 1 (by rfl) ⟨946109, by rfl⟩ : syracuseStep 1261479 = 1892219) B1892219
theorem B1892393 : Blo 1260448 1892393 := bstep (se 2 (by rfl) ⟨709647, by rfl⟩ : syracuseStep 1892393 = 1419295) B1419295
theorem B1892423 : Blo 1260448 1892423 := bstep (se 1 (by rfl) ⟨1419317, by rfl⟩ : syracuseStep 1892423 = 2838635) B2838635
theorem B1892459 : Blo 1260448 1892459 := bstep (se 1 (by rfl) ⟨1419344, by rfl⟩ : syracuseStep 1892459 = 2838689) B2838689
theorem B10772615 : Blo 1260448 10772615 := bstep (se 1 (by rfl) ⟨8079461, by rfl⟩ : syracuseStep 10772615 = 16158923) B16158923
theorem B1892543 : Blo 1260448 1892543 := bstep (se 1 (by rfl) ⟨1419407, by rfl⟩ : syracuseStep 1892543 = 2838815) B2838815
theorem B4038911 : Blo 1260448 4038911 := bstep (se 1 (by rfl) ⟨3029183, by rfl⟩ : syracuseStep 4038911 = 6058367) B6058367
theorem B1261927 : Blo 1260448 1261927 := bstep (se 1 (by rfl) ⟨946445, by rfl⟩ : syracuseStep 1261927 = 1892891) B1892891
theorem B1892729 : Blo 1260448 1892729 := bstep (se 2 (by rfl) ⟨709773, by rfl⟩ : syracuseStep 1892729 = 1419547) B1419547
theorem B14377337 : Blo 1260448 14377337 := bstep (se 2 (by rfl) ⟨5391501, by rfl⟩ : syracuseStep 14377337 = 10783003) B10783003
theorem B3834323 : Blo 1260448 3834323 := bstep (se 1 (by rfl) ⟨2875742, by rfl⟩ : syracuseStep 3834323 = 5751485) B5751485
theorem B1262047 : Blo 1260448 1262047 := bstep (se 1 (by rfl) ⟨946535, by rfl⟩ : syracuseStep 1262047 = 1893071) B1893071
theorem B1262055 : Blo 1260448 1262055 := bstep (se 1 (by rfl) ⟨946541, by rfl⟩ : syracuseStep 1262055 = 1893083) B1893083
theorem B7184933 : Blo 1260448 7184933 := bstep (se 4 (by rfl) ⟨673587, by rfl⟩ : syracuseStep 7184933 = 1347175) B1347175
theorem B1893023 : Blo 1260448 1893023 := bstep (se 1 (by rfl) ⟨1419767, by rfl⟩ : syracuseStep 1893023 = 2839535) B2839535
theorem B2917031 : Blo 1260448 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B4793039 : Blo 1260448 4793039 := bstep (se 1 (by rfl) ⟨3594779, by rfl⟩ : syracuseStep 4793039 = 7189559) B7189559
theorem B1794793 : Blo 1260448 1794793 := bstep (se 2 (by rfl) ⟨673047, by rfl⟩ : syracuseStep 1794793 = 1346095) B1346095
theorem B1262331 : Blo 1260448 1262331 := bstep (se 1 (by rfl) ⟨946748, by rfl⟩ : syracuseStep 1262331 = 1893497) B1893497
theorem B5391161 : Blo 1260448 5391161 := bstep (se 2 (by rfl) ⟨2021685, by rfl⟩ : syracuseStep 5391161 = 4043371) B4043371
theorem B19424069 : Blo 1260448 19424069 := bstep (se 4 (by rfl) ⟨1821006, by rfl⟩ : syracuseStep 19424069 = 3642013) B3642013
theorem B1893359 : Blo 1260448 1893359 := bstep (se 1 (by rfl) ⟨1420019, by rfl⟩ : syracuseStep 1893359 = 2840039) B2840039
theorem B1893467 : Blo 1260448 1893467 := bstep (se 1 (by rfl) ⟨1420100, by rfl⟩ : syracuseStep 1893467 = 2840201) B2840201
theorem B1893479 : Blo 1260448 1893479 := bstep (se 1 (by rfl) ⟨1420109, by rfl⟩ : syracuseStep 1893479 = 2840219) B2840219
theorem B27272335 : Blo 1260448 27272335 := bstep (se 1 (by rfl) ⟨20454251, by rfl⟩ : syracuseStep 27272335 = 40908503) B40908503
theorem B1418395 : Blo 1260448 1418395 := bstep (se 1 (by rfl) ⟨1063796, by rfl⟩ : syracuseStep 1418395 = 2127593) B2127593
theorem B126084313 : Blo 1260448 126084313 := bstep (se 2 (by rfl) ⟨47281617, by rfl⟩ : syracuseStep 126084313 = 94563235) B94563235
theorem B1893611 : Blo 1260448 1893611 := bstep (se 1 (by rfl) ⟨1420208, by rfl⟩ : syracuseStep 1893611 = 2840417) B2840417
theorem B5391623 : Blo 1260448 5391623 := bstep (se 1 (by rfl) ⟨4043717, by rfl⟩ : syracuseStep 5391623 = 8087435) B8087435
theorem B1820071 : Blo 1260448 1820071 := bstep (se 1 (by rfl) ⟨1365053, by rfl⟩ : syracuseStep 1820071 = 2730107) B2730107
theorem B3194873 : Blo 1260448 3194873 := bstep (se 2 (by rfl) ⟨1198077, by rfl⟩ : syracuseStep 3194873 = 2396155) B2396155
theorem B147564119 : Blo 1260448 147564119 := bstep (se 1 (by rfl) ⟨110673089, by rfl⟩ : syracuseStep 147564119 = 221346179) B221346179
theorem B5113469 : Blo 1260448 5113469 := bstep (se 3 (by rfl) ⟨958775, by rfl⟩ : syracuseStep 5113469 = 1917551) B1917551
theorem B2836151 : Blo 1260448 2836151 := bstep (se 1 (by rfl) ⟨2127113, by rfl⟩ : syracuseStep 2836151 = 4254227) B4254227
theorem B1419079 : Blo 1260448 1419079 := bstep (se 1 (by rfl) ⟨1064309, by rfl⟩ : syracuseStep 1419079 = 2128619) B2128619
theorem B2836601 : Blo 1260448 2836601 := bstep (se 2 (by rfl) ⟨1063725, by rfl⟩ : syracuseStep 2836601 = 2127451) B2127451
theorem B3639451 : Blo 1260448 3639451 := bstep (se 1 (by rfl) ⟨2729588, by rfl⟩ : syracuseStep 3639451 = 5459177) B5459177
theorem B2836799 : Blo 1260448 2836799 := bstep (se 1 (by rfl) ⟨2127599, by rfl⟩ : syracuseStep 2836799 = 4255199) B4255199
theorem B5384531 : Blo 1260448 5384531 := bstep (se 1 (by rfl) ⟨4038398, by rfl⟩ : syracuseStep 5384531 = 8076797) B8076797
theorem B1420231 : Blo 1260448 1420231 := bstep (se 1 (by rfl) ⟨1065173, by rfl⟩ : syracuseStep 1420231 = 2130347) B2130347
theorem B7179353 : Blo 1260448 7179353 := bstep (se 2 (by rfl) ⟨2692257, by rfl⟩ : syracuseStep 7179353 = 5384515) B5384515
theorem B9710735 : Blo 1260448 9710735 := bstep (se 1 (by rfl) ⟨7283051, by rfl⟩ : syracuseStep 9710735 = 14566103) B14566103
theorem B3411197 : Blo 1260448 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B8080897 : Blo 1260448 8080897 := bstep (se 2 (by rfl) ⟨3030336, by rfl⟩ : syracuseStep 8080897 = 6060673) B6060673
theorem B27299501 : Blo 1260448 27299501 := bstep (se 3 (by rfl) ⟨5118656, by rfl⟩ : syracuseStep 27299501 = 10237313) B10237313
theorem B6475511 : Blo 1260448 6475511 := bstep (se 1 (by rfl) ⟨4856633, by rfl⟩ : syracuseStep 6475511 = 9713267) B9713267
theorem B7180103 : Blo 1260448 7180103 := bstep (se 1 (by rfl) ⟨5385077, by rfl⟩ : syracuseStep 7180103 = 10770155) B10770155
theorem B3641159 : Blo 1260448 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B51777467 : Blo 1260448 51777467 := bstep (se 1 (by rfl) ⟨38833100, by rfl⟩ : syracuseStep 51777467 = 77666201) B77666201
theorem B4255739 : Blo 1260448 4255739 := bstep (se 1 (by rfl) ⟨3191804, by rfl⟩ : syracuseStep 4255739 = 6383609) B6383609
theorem B36344659 : Blo 1260448 36344659 := bstep (se 1 (by rfl) ⟨27258494, by rfl⟩ : syracuseStep 36344659 = 54516989) B54516989
theorem B33649787 : Blo 1260448 33649787 := bstep (se 1 (by rfl) ⟨25237340, by rfl⟩ : syracuseStep 33649787 = 50474681) B50474681
theorem B3593423 : Blo 1260448 3593423 := bstep (se 1 (by rfl) ⟨2695067, by rfl⟩ : syracuseStep 3593423 = 5390135) B5390135
theorem B7673075 : Blo 1260448 7673075 := bstep (se 1 (by rfl) ⟨5754806, by rfl⟩ : syracuseStep 7673075 = 11509613) B11509613
theorem B2127343 : Blo 1260448 2127343 := bstep (se 1 (by rfl) ⟨1595507, by rfl⟩ : syracuseStep 2127343 = 3191015) B3191015
theorem B6821459 : Blo 1260448 6821459 := bstep (se 1 (by rfl) ⟨5116094, by rfl⟩ : syracuseStep 6821459 = 10232189) B10232189
theorem B2021039 : Blo 1260448 2021039 := bstep (se 1 (by rfl) ⟨1515779, by rfl⟩ : syracuseStep 2021039 = 3031559) B3031559
theorem B2840255 : Blo 1260448 2840255 := bstep (se 1 (by rfl) ⟨2130191, by rfl⟩ : syracuseStep 2840255 = 4260383) B4260383
theorem B12121811 : Blo 1260448 12121811 := bstep (se 1 (by rfl) ⟨9091358, by rfl⟩ : syracuseStep 12121811 = 18182717) B18182717
theorem B6387497 : Blo 1260448 6387497 := bstep (se 2 (by rfl) ⟨2395311, by rfl⟩ : syracuseStep 6387497 = 4790623) B4790623
theorem B3192655 : Blo 1260448 3192655 := bstep (se 1 (by rfl) ⟨2394491, by rfl⟩ : syracuseStep 3192655 = 4788983) B4788983
theorem B3192767 : Blo 1260448 3192767 := bstep (se 1 (by rfl) ⟨2394575, by rfl⟩ : syracuseStep 3192767 = 4789151) B4789151
theorem B9574685 : Blo 1260448 9574685 := bstep (se 3 (by rfl) ⟨1795253, by rfl⟩ : syracuseStep 9574685 = 3590507) B3590507
theorem B4545031 : Blo 1260448 4545031 := bstep (se 1 (by rfl) ⟨3408773, by rfl⟩ : syracuseStep 4545031 = 6817547) B6817547
theorem B1890911 : Blo 1260448 1890911 := bstep (se 1 (by rfl) ⟨1418183, by rfl⟩ : syracuseStep 1890911 = 2836367) B2836367
theorem B5388905 : Blo 1260448 5388905 := bstep (se 2 (by rfl) ⟨2020839, by rfl⟩ : syracuseStep 5388905 = 4041679) B4041679
theorem B1891007 : Blo 1260448 1891007 := bstep (se 1 (by rfl) ⟨1418255, by rfl⟩ : syracuseStep 1891007 = 2836511) B2836511
theorem B1891049 : Blo 1260448 1891049 := bstep (se 2 (by rfl) ⟨709143, by rfl⟩ : syracuseStep 1891049 = 1418287) B1418287
theorem B2022121 : Blo 1260448 2022121 := bstep (se 2 (by rfl) ⟨758295, by rfl⟩ : syracuseStep 2022121 = 1516591) B1516591
theorem B1891175 : Blo 1260448 1891175 := bstep (se 1 (by rfl) ⟨1418381, by rfl⟩ : syracuseStep 1891175 = 2836763) B2836763
theorem B1891241 : Blo 1260448 1891241 := bstep (se 2 (by rfl) ⟨709215, by rfl⟩ : syracuseStep 1891241 = 1418431) B1418431
theorem B1260479 : Blo 1260448 1260479 := bstep (se 1 (by rfl) ⟨945359, by rfl⟩ : syracuseStep 1260479 = 1890719) B1890719
theorem B5389247 : Blo 1260448 5389247 := bstep (se 1 (by rfl) ⟨4041935, by rfl⟩ : syracuseStep 5389247 = 8083871) B8083871
theorem B1260527 : Blo 1260448 1260527 := bstep (se 1 (by rfl) ⟨945395, by rfl⟩ : syracuseStep 1260527 = 1890791) B1890791
theorem B6388793 : Blo 1260448 6388793 := bstep (se 2 (by rfl) ⟨2395797, by rfl⟩ : syracuseStep 6388793 = 4791595) B4791595
theorem B1891391 : Blo 1260448 1891391 := bstep (se 1 (by rfl) ⟨1418543, by rfl⟩ : syracuseStep 1891391 = 2837087) B2837087
theorem B1891433 : Blo 1260448 1891433 := bstep (se 2 (by rfl) ⟨709287, by rfl⟩ : syracuseStep 1891433 = 1418575) B1418575
theorem B2129051 : Blo 1260448 2129051 := bstep (se 1 (by rfl) ⟨1596788, by rfl⟩ : syracuseStep 2129051 = 3193577) B3193577
theorem B112114853 : Blo 1260448 112114853 := bstep (se 4 (by rfl) ⟨10510767, by rfl⟩ : syracuseStep 112114853 = 21021535) B21021535
theorem B1891559 : Blo 1260448 1891559 := bstep (se 1 (by rfl) ⟨1418669, by rfl⟩ : syracuseStep 1891559 = 2837339) B2837339
theorem B56048881 : Blo 1260448 56048881 := bstep (se 2 (by rfl) ⟨21018330, by rfl⟩ : syracuseStep 56048881 = 42036661) B42036661
theorem B1596667 : Blo 1260448 1596667 := bstep (se 1 (by rfl) ⟨1197500, by rfl⟩ : syracuseStep 1596667 = 2395001) B2395001
theorem B10779965 : Blo 1260448 10779965 := bstep (se 3 (by rfl) ⟨2021243, by rfl⟩ : syracuseStep 10779965 = 4042487) B4042487
theorem B55328123 : Blo 1260448 55328123 := bstep (se 1 (by rfl) ⟨41496092, by rfl⟩ : syracuseStep 55328123 = 82992185) B82992185
theorem B1261023 : Blo 1260448 1261023 := bstep (se 1 (by rfl) ⟨945767, by rfl⟩ : syracuseStep 1261023 = 1891535) B1891535
theorem B28032479 : Blo 1260448 28032479 := bstep (se 1 (by rfl) ⟨21024359, by rfl⟩ : syracuseStep 28032479 = 42048719) B42048719
theorem B1261103 : Blo 1260448 1261103 := bstep (se 1 (by rfl) ⟨945827, by rfl⟩ : syracuseStep 1261103 = 1891655) B1891655
theorem B4791899 : Blo 1260448 4791899 := bstep (se 1 (by rfl) ⟨3593924, by rfl⟩ : syracuseStep 4791899 = 7187849) B7187849
theorem B1261211 : Blo 1260448 1261211 := bstep (se 1 (by rfl) ⟨945908, by rfl⟩ : syracuseStep 1261211 = 1891817) B1891817
theorem B1892063 : Blo 1260448 1892063 := bstep (se 1 (by rfl) ⟨1419047, by rfl⟩ : syracuseStep 1892063 = 2838095) B2838095
theorem B1261307 : Blo 1260448 1261307 := bstep (se 1 (by rfl) ⟨945980, by rfl⟩ : syracuseStep 1261307 = 1891961) B1891961
theorem B7184159 : Blo 1260448 7184159 := bstep (se 1 (by rfl) ⟨5388119, by rfl⟩ : syracuseStep 7184159 = 10776239) B10776239
theorem B1261471 : Blo 1260448 1261471 := bstep (se 1 (by rfl) ⟨946103, by rfl⟩ : syracuseStep 1261471 = 1892207) B1892207
theorem B1261595 : Blo 1260448 1261595 := bstep (se 1 (by rfl) ⟨946196, by rfl⟩ : syracuseStep 1261595 = 1892393) B1892393
theorem B1261615 : Blo 1260448 1261615 := bstep (se 1 (by rfl) ⟨946211, by rfl⟩ : syracuseStep 1261615 = 1892423) B1892423
theorem B1261639 : Blo 1260448 1261639 := bstep (se 1 (by rfl) ⟨946229, by rfl⟩ : syracuseStep 1261639 = 1892459) B1892459
theorem B1261695 : Blo 1260448 1261695 := bstep (se 1 (by rfl) ⟨946271, by rfl⟩ : syracuseStep 1261695 = 1892543) B1892543
theorem B1261819 : Blo 1260448 1261819 := bstep (se 1 (by rfl) ⟨946364, by rfl⟩ : syracuseStep 1261819 = 1892729) B1892729
theorem B9584891 : Blo 1260448 9584891 := bstep (se 1 (by rfl) ⟨7188668, by rfl⟩ : syracuseStep 9584891 = 14377337) B14377337
theorem B2556215 : Blo 1260448 2556215 := bstep (se 1 (by rfl) ⟨1917161, by rfl⟩ : syracuseStep 2556215 = 3834323) B3834323
theorem B1262015 : Blo 1260448 1262015 := bstep (se 1 (by rfl) ⟨946511, by rfl⟩ : syracuseStep 1262015 = 1893023) B1893023
theorem B3195359 : Blo 1260448 3195359 := bstep (se 1 (by rfl) ⟨2396519, by rfl⟩ : syracuseStep 3195359 = 4793039) B4793039
theorem B1262239 : Blo 1260448 1262239 := bstep (se 1 (by rfl) ⟨946679, by rfl⟩ : syracuseStep 1262239 = 1893359) B1893359
theorem B1262311 : Blo 1260448 1262311 := bstep (se 1 (by rfl) ⟨946733, by rfl⟩ : syracuseStep 1262311 = 1893467) B1893467
theorem B1262319 : Blo 1260448 1262319 := bstep (se 1 (by rfl) ⟨946739, by rfl⟩ : syracuseStep 1262319 = 1893479) B1893479
theorem B1262407 : Blo 1260448 1262407 := bstep (se 1 (by rfl) ⟨946805, by rfl⟩ : syracuseStep 1262407 = 1893611) B1893611
theorem B2393057 : Blo 1260448 2393057 := bstep (se 2 (by rfl) ⟨897396, by rfl⟩ : syracuseStep 2393057 = 1794793) B1794793
theorem B2696161 : Blo 1260448 2696161 := bstep (se 2 (by rfl) ⟨1011060, by rfl⟩ : syracuseStep 2696161 = 2022121) B2022121
theorem B2129915 : Blo 1260448 2129915 := bstep (se 1 (by rfl) ⟨1597436, by rfl⟩ : syracuseStep 2129915 = 3194873) B3194873
theorem B4547639 : Blo 1260448 4547639 := bstep (se 1 (by rfl) ⟨3410729, by rfl⟩ : syracuseStep 4547639 = 6821459) B6821459
theorem B3408979 : Blo 1260448 3408979 := bstep (se 1 (by rfl) ⟨2556734, by rfl⟩ : syracuseStep 3408979 = 5113469) B5113469
theorem B1893503 : Blo 1260448 1893503 := bstep (se 1 (by rfl) ⟨1420127, by rfl⟩ : syracuseStep 1893503 = 2840255) B2840255
theorem B1893641 : Blo 1260448 1893641 := bstep (se 2 (by rfl) ⟨710115, by rfl⟩ : syracuseStep 1893641 = 1420231) B1420231
theorem B103581173 : Blo 1260448 103581173 := bstep (se 5 (by rfl) ⟨4855367, by rfl⟩ : syracuseStep 103581173 = 9710735) B9710735
theorem B6383123 : Blo 1260448 6383123 := bstep (se 1 (by rfl) ⟨4787342, by rfl⟩ : syracuseStep 6383123 = 9574685) B9574685
theorem B3589687 : Blo 1260448 3589687 := bstep (se 1 (by rfl) ⟨2692265, by rfl⟩ : syracuseStep 3589687 = 5384531) B5384531
theorem B2836457 : Blo 1260448 2836457 := bstep (se 2 (by rfl) ⟨1063671, by rfl⟩ : syracuseStep 2836457 = 2127343) B2127343
theorem B10774529 : Blo 1260448 10774529 := bstep (se 2 (by rfl) ⟨4040448, by rfl⟩ : syracuseStep 10774529 = 8080897) B8080897
theorem B4786235 : Blo 1260448 4786235 := bstep (se 1 (by rfl) ⟨3589676, by rfl⟩ : syracuseStep 4786235 = 7179353) B7179353
theorem B1419367 : Blo 1260448 1419367 := bstep (se 1 (by rfl) ⟨1064525, by rfl⟩ : syracuseStep 1419367 = 2129051) B2129051
theorem B9709757 : Blo 1260448 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B7186643 : Blo 1260448 7186643 := bstep (se 1 (by rfl) ⟨5389982, by rfl⟩ : syracuseStep 7186643 = 10779965) B10779965
theorem B18688319 : Blo 1260448 18688319 := bstep (se 1 (by rfl) ⟨14016239, by rfl⟩ : syracuseStep 18688319 = 28032479) B28032479
theorem B4786735 : Blo 1260448 4786735 := bstep (se 1 (by rfl) ⟨3590051, by rfl⟩ : syracuseStep 4786735 = 7180103) B7180103
theorem B2837159 : Blo 1260448 2837159 := bstep (se 1 (by rfl) ⟨2127869, by rfl⟩ : syracuseStep 2837159 = 4255739) B4255739
theorem B4852601 : Blo 1260448 4852601 := bstep (se 2 (by rfl) ⟨1819725, by rfl⟩ : syracuseStep 4852601 = 3639451) B3639451
theorem B5115383 : Blo 1260448 5115383 := bstep (se 1 (by rfl) ⟨3836537, by rfl⟩ : syracuseStep 5115383 = 7673075) B7673075
theorem B48459545 : Blo 1260448 48459545 := bstep (se 2 (by rfl) ⟨18172329, by rfl⟩ : syracuseStep 48459545 = 36344659) B36344659
theorem B1347359 : Blo 1260448 1347359 := bstep (se 1 (by rfl) ⟨1010519, by rfl⟩ : syracuseStep 1347359 = 2021039) B2021039
theorem B8081207 : Blo 1260448 8081207 := bstep (se 1 (by rfl) ⟨6060905, by rfl⟩ : syracuseStep 8081207 = 12121811) B12121811
theorem B168112417 : Blo 1260448 168112417 := bstep (se 2 (by rfl) ⟨63042156, by rfl⟩ : syracuseStep 168112417 = 126084313) B126084313
theorem B74731841 : Blo 1260448 74731841 := bstep (se 2 (by rfl) ⟨28024440, by rfl⟩ : syracuseStep 74731841 = 56048881) B56048881
theorem B3592603 : Blo 1260448 3592603 := bstep (se 1 (by rfl) ⟨2694452, by rfl⟩ : syracuseStep 3592603 = 5388905) B5388905
theorem B7778749 : Blo 1260448 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B3592831 : Blo 1260448 3592831 := bstep (se 1 (by rfl) ⟨2694623, by rfl⟩ : syracuseStep 3592831 = 5389247) B5389247
theorem B2274131 : Blo 1260448 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B36885415 : Blo 1260448 36885415 := bstep (se 1 (by rfl) ⟨27664061, by rfl⟩ : syracuseStep 36885415 = 55328123) B55328123
theorem B4256873 : Blo 1260448 4256873 := bstep (se 2 (by rfl) ⟨1596327, by rfl⟩ : syracuseStep 4256873 = 3192655) B3192655
theorem B18199667 : Blo 1260448 18199667 := bstep (se 1 (by rfl) ⟨13649750, by rfl⟩ : syracuseStep 18199667 = 27299501) B27299501
theorem B4789439 : Blo 1260448 4789439 := bstep (se 1 (by rfl) ⟨3592079, by rfl⟩ : syracuseStep 4789439 = 7184159) B7184159
theorem B34518311 : Blo 1260448 34518311 := bstep (se 1 (by rfl) ⟨25888733, by rfl⟩ : syracuseStep 34518311 = 51777467) B51777467
theorem B7181743 : Blo 1260448 7181743 := bstep (se 1 (by rfl) ⟨5386307, by rfl⟩ : syracuseStep 7181743 = 10772615) B10772615
theorem B2692607 : Blo 1260448 2692607 := bstep (se 1 (by rfl) ⟨2019455, by rfl⟩ : syracuseStep 2692607 = 4038911) B4038911
theorem B89732765 : Blo 1260448 89732765 := bstep (se 3 (by rfl) ⟨16824893, by rfl⟩ : syracuseStep 89732765 = 33649787) B33649787
theorem B4789955 : Blo 1260448 4789955 := bstep (se 1 (by rfl) ⟨3592466, by rfl⟩ : syracuseStep 4789955 = 7184933) B7184933
theorem B3594107 : Blo 1260448 3594107 := bstep (se 1 (by rfl) ⟨2695580, by rfl⟩ : syracuseStep 3594107 = 5391161) B5391161
theorem B9582461 : Blo 1260448 9582461 := bstep (se 3 (by rfl) ⟨1796711, by rfl⟩ : syracuseStep 9582461 = 3593423) B3593423
theorem B12949379 : Blo 1260448 12949379 := bstep (se 1 (by rfl) ⟨9712034, by rfl⟩ : syracuseStep 12949379 = 19424069) B19424069
theorem B6060041 : Blo 1260448 6060041 := bstep (se 2 (by rfl) ⟨2272515, by rfl⟩ : syracuseStep 6060041 = 4545031) B4545031
theorem B3594415 : Blo 1260448 3594415 := bstep (se 1 (by rfl) ⟨2695811, by rfl⟩ : syracuseStep 3594415 = 5391623) B5391623
theorem B98376079 : Blo 1260448 98376079 := bstep (se 1 (by rfl) ⟨73782059, by rfl⟩ : syracuseStep 98376079 = 147564119) B147564119
theorem B1890767 : Blo 1260448 1890767 := bstep (se 1 (by rfl) ⟨1418075, by rfl⟩ : syracuseStep 1890767 = 2836151) B2836151
theorem B4258331 : Blo 1260448 4258331 := bstep (se 1 (by rfl) ⟨3193748, by rfl⟩ : syracuseStep 4258331 = 6387497) B6387497
theorem B2128511 : Blo 1260448 2128511 := bstep (se 1 (by rfl) ⟨1596383, by rfl⟩ : syracuseStep 2128511 = 3192767) B3192767
theorem B1891067 : Blo 1260448 1891067 := bstep (se 1 (by rfl) ⟨1418300, by rfl⟩ : syracuseStep 1891067 = 2836601) B2836601
theorem B36363113 : Blo 1260448 36363113 := bstep (se 2 (by rfl) ⟨13636167, by rfl⟩ : syracuseStep 36363113 = 27272335) B27272335
theorem B1891193 : Blo 1260448 1891193 := bstep (se 2 (by rfl) ⟨709197, by rfl⟩ : syracuseStep 1891193 = 1418395) B1418395
theorem B1891199 : Blo 1260448 1891199 := bstep (se 1 (by rfl) ⟨1418399, by rfl⟩ : syracuseStep 1891199 = 2836799) B2836799
theorem B2128889 : Blo 1260448 2128889 := bstep (se 2 (by rfl) ⟨798333, by rfl⟩ : syracuseStep 2128889 = 1596667) B1596667
theorem B1260607 : Blo 1260448 1260607 := bstep (se 1 (by rfl) ⟨945455, by rfl⟩ : syracuseStep 1260607 = 1890911) B1890911
theorem B1260671 : Blo 1260448 1260671 := bstep (se 1 (by rfl) ⟨945503, by rfl⟩ : syracuseStep 1260671 = 1891007) B1891007
theorem B1260699 : Blo 1260448 1260699 := bstep (se 1 (by rfl) ⟨945524, by rfl⟩ : syracuseStep 1260699 = 1891049) B1891049
theorem B1260783 : Blo 1260448 1260783 := bstep (se 1 (by rfl) ⟨945587, by rfl⟩ : syracuseStep 1260783 = 1891175) B1891175
theorem B1260827 : Blo 1260448 1260827 := bstep (se 1 (by rfl) ⟨945620, by rfl⟩ : syracuseStep 1260827 = 1891241) B1891241
theorem B17268029 : Blo 1260448 17268029 := bstep (se 3 (by rfl) ⟨3237755, by rfl⟩ : syracuseStep 17268029 = 6475511) B6475511
theorem B4259195 : Blo 1260448 4259195 := bstep (se 1 (by rfl) ⟨3194396, by rfl⟩ : syracuseStep 4259195 = 6388793) B6388793
theorem B1260927 : Blo 1260448 1260927 := bstep (se 1 (by rfl) ⟨945695, by rfl⟩ : syracuseStep 1260927 = 1891391) B1891391
theorem B1260955 : Blo 1260448 1260955 := bstep (se 1 (by rfl) ⟨945716, by rfl⟩ : syracuseStep 1260955 = 1891433) B1891433
theorem B74743235 : Blo 1260448 74743235 := bstep (se 1 (by rfl) ⟨56057426, by rfl⟩ : syracuseStep 74743235 = 112114853) B112114853
theorem B1261039 : Blo 1260448 1261039 := bstep (se 1 (by rfl) ⟨945779, by rfl⟩ : syracuseStep 1261039 = 1891559) B1891559
theorem B9707045 : Blo 1260448 9707045 := bstep (se 4 (by rfl) ⟨910035, by rfl⟩ : syracuseStep 9707045 = 1820071) B1820071
theorem B3194599 : Blo 1260448 3194599 := bstep (se 1 (by rfl) ⟨2395949, by rfl⟩ : syracuseStep 3194599 = 4791899) B4791899
theorem B1892105 : Blo 1260448 1892105 := bstep (se 2 (by rfl) ⟨709539, by rfl⟩ : syracuseStep 1892105 = 1419079) B1419079
theorem B1261375 : Blo 1260448 1261375 := bstep (se 1 (by rfl) ⟨946031, by rfl⟩ : syracuseStep 1261375 = 1892063) B1892063
theorem B1892489 : Blo 1260448 1892489 := bstep (se 2 (by rfl) ⟨709683, by rfl⟩ : syracuseStep 1892489 = 1419367) B1419367
theorem B6389927 : Blo 1260448 6389927 := bstep (se 1 (by rfl) ⟨4792445, by rfl⟩ : syracuseStep 6389927 = 9584891) B9584891
theorem B1704143 : Blo 1260448 1704143 := bstep (se 1 (by rfl) ⟨1278107, by rfl⟩ : syracuseStep 1704143 = 2556215) B2556215
theorem B4792553 : Blo 1260448 4792553 := bstep (se 2 (by rfl) ⟨1797207, by rfl⟩ : syracuseStep 4792553 = 3594415) B3594415
theorem B2130239 : Blo 1260448 2130239 := bstep (se 1 (by rfl) ⟨1597679, by rfl⟩ : syracuseStep 2130239 = 3195359) B3195359
theorem B224149889 : Blo 1260448 224149889 := bstep (se 2 (by rfl) ⟨84056208, by rfl⟩ : syracuseStep 224149889 = 168112417) B168112417
theorem B1516087 : Blo 1260448 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B10371665 : Blo 1260448 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B3031759 : Blo 1260448 3031759 := bstep (se 1 (by rfl) ⟨2273819, by rfl⟩ : syracuseStep 3031759 = 4547639) B4547639
theorem B6382313 : Blo 1260448 6382313 := bstep (se 2 (by rfl) ⟨2393367, by rfl⟩ : syracuseStep 6382313 = 4786735) B4786735
theorem B12133111 : Blo 1260448 12133111 := bstep (se 1 (by rfl) ⟨9099833, by rfl⟩ : syracuseStep 12133111 = 18199667) B18199667
theorem B1262335 : Blo 1260448 1262335 := bstep (se 1 (by rfl) ⟨946751, by rfl⟩ : syracuseStep 1262335 = 1893503) B1893503
theorem B1262427 : Blo 1260448 1262427 := bstep (se 1 (by rfl) ⟨946820, by rfl⟩ : syracuseStep 1262427 = 1893641) B1893641
theorem B23012207 : Blo 1260448 23012207 := bstep (se 1 (by rfl) ⟨17259155, by rfl⟩ : syracuseStep 23012207 = 34518311) B34518311
theorem B4040027 : Blo 1260448 4040027 := bstep (se 1 (by rfl) ⟨3030020, by rfl⟩ : syracuseStep 4040027 = 6060041) B6060041
theorem B6473171 : Blo 1260448 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B1419007 : Blo 1260448 1419007 := bstep (se 1 (by rfl) ⟨1064255, by rfl⟩ : syracuseStep 1419007 = 2128511) B2128511
theorem B24242075 : Blo 1260448 24242075 := bstep (se 1 (by rfl) ⟨18181556, by rfl⟩ : syracuseStep 24242075 = 36363113) B36363113
theorem B1419259 : Blo 1260448 1419259 := bstep (se 1 (by rfl) ⟨1064444, by rfl⟩ : syracuseStep 1419259 = 2128889) B2128889
theorem B4786249 : Blo 1260448 4786249 := bstep (se 2 (by rfl) ⟨1794843, by rfl⟩ : syracuseStep 4786249 = 3589687) B3589687
theorem B11512019 : Blo 1260448 11512019 := bstep (se 1 (by rfl) ⟨8634014, by rfl⟩ : syracuseStep 11512019 = 17268029) B17268029
theorem B3410255 : Blo 1260448 3410255 := bstep (se 1 (by rfl) ⟨2557691, by rfl⟩ : syracuseStep 3410255 = 5115383) B5115383
theorem B1419943 : Blo 1260448 1419943 := bstep (se 1 (by rfl) ⟨1064957, by rfl⟩ : syracuseStep 1419943 = 2129915) B2129915
theorem B2837915 : Blo 1260448 2837915 := bstep (se 1 (by rfl) ⟨2128436, by rfl⟩ : syracuseStep 2837915 = 4256873) B4256873
theorem B69054115 : Blo 1260448 69054115 := bstep (se 1 (by rfl) ⟨51790586, by rfl⟩ : syracuseStep 69054115 = 103581173) B103581173
theorem B4255415 : Blo 1260448 4255415 := bstep (se 1 (by rfl) ⟨3191561, by rfl⟩ : syracuseStep 4255415 = 6383123) B6383123
theorem B59821843 : Blo 1260448 59821843 := bstep (se 1 (by rfl) ⟨44866382, by rfl⟩ : syracuseStep 59821843 = 89732765) B89732765
theorem B49180553 : Blo 1260448 49180553 := bstep (se 2 (by rfl) ⟨18442707, by rfl⟩ : syracuseStep 49180553 = 36885415) B36885415
theorem B2396071 : Blo 1260448 2396071 := bstep (se 1 (by rfl) ⟨1797053, by rfl⟩ : syracuseStep 2396071 = 3594107) B3594107
theorem B7180285 : Blo 1260448 7180285 := bstep (se 3 (by rfl) ⟨1346303, by rfl⟩ : syracuseStep 7180285 = 2692607) B2692607
theorem B3190823 : Blo 1260448 3190823 := bstep (se 1 (by rfl) ⟨2393117, by rfl⟩ : syracuseStep 3190823 = 4786235) B4786235
theorem B2838887 : Blo 1260448 2838887 := bstep (se 1 (by rfl) ⟨2129165, by rfl⟩ : syracuseStep 2838887 = 4258331) B4258331
theorem B3592957 : Blo 1260448 3592957 := bstep (se 3 (by rfl) ⟨673679, by rfl⟩ : syracuseStep 3592957 = 1347359) B1347359
theorem B2839463 : Blo 1260448 2839463 := bstep (se 1 (by rfl) ⟨2129597, by rfl⟩ : syracuseStep 2839463 = 4259195) B4259195
theorem B49828823 : Blo 1260448 49828823 := bstep (se 1 (by rfl) ⟨37371617, by rfl⟩ : syracuseStep 49828823 = 74743235) B74743235
theorem B32306363 : Blo 1260448 32306363 := bstep (se 1 (by rfl) ⟨24229772, by rfl⟩ : syracuseStep 32306363 = 48459545) B48459545
theorem B5387471 : Blo 1260448 5387471 := bstep (se 1 (by rfl) ⟨4040603, by rfl⟩ : syracuseStep 5387471 = 8081207) B8081207
theorem B49821227 : Blo 1260448 49821227 := bstep (se 1 (by rfl) ⟨37365920, by rfl⟩ : syracuseStep 49821227 = 74731841) B74731841
theorem B131168105 : Blo 1260448 131168105 := bstep (se 2 (by rfl) ⟨49188039, by rfl⟩ : syracuseStep 131168105 = 98376079) B98376079
theorem B4790137 : Blo 1260448 4790137 := bstep (se 2 (by rfl) ⟨1796301, by rfl⟩ : syracuseStep 4790137 = 3592603) B3592603
theorem B1595371 : Blo 1260448 1595371 := bstep (se 1 (by rfl) ⟨1196528, by rfl⟩ : syracuseStep 1595371 = 2393057) B2393057
theorem B3192959 : Blo 1260448 3192959 := bstep (se 1 (by rfl) ⟨2394719, by rfl⟩ : syracuseStep 3192959 = 4789439) B4789439
theorem B4790441 : Blo 1260448 4790441 := bstep (se 2 (by rfl) ⟨1796415, by rfl⟩ : syracuseStep 4790441 = 3592831) B3592831
theorem B3193303 : Blo 1260448 3193303 := bstep (se 1 (by rfl) ⟨2394977, by rfl⟩ : syracuseStep 3193303 = 4789955) B4789955
theorem B6388307 : Blo 1260448 6388307 := bstep (se 1 (by rfl) ⟨4791230, by rfl⟩ : syracuseStep 6388307 = 9582461) B9582461
theorem B8632919 : Blo 1260448 8632919 := bstep (se 1 (by rfl) ⟨6474689, by rfl⟩ : syracuseStep 8632919 = 12949379) B12949379
theorem B3594881 : Blo 1260448 3594881 := bstep (se 2 (by rfl) ⟨1348080, by rfl⟩ : syracuseStep 3594881 = 2696161) B2696161
theorem B1890971 : Blo 1260448 1890971 := bstep (se 1 (by rfl) ⟨1418228, by rfl⟩ : syracuseStep 1890971 = 2836457) B2836457
theorem B7183019 : Blo 1260448 7183019 := bstep (se 1 (by rfl) ⟨5387264, by rfl⟩ : syracuseStep 7183019 = 10774529) B10774529
theorem B25885453 : Blo 1260448 25885453 := bstep (se 3 (by rfl) ⟨4853522, by rfl⟩ : syracuseStep 25885453 = 9707045) B9707045
theorem B4545305 : Blo 1260448 4545305 := bstep (se 2 (by rfl) ⟨1704489, by rfl⟩ : syracuseStep 4545305 = 3408979) B3408979
theorem B4791095 : Blo 1260448 4791095 := bstep (se 1 (by rfl) ⟨3593321, by rfl⟩ : syracuseStep 4791095 = 7186643) B7186643
theorem B12458879 : Blo 1260448 12458879 := bstep (se 1 (by rfl) ⟨9344159, by rfl⟩ : syracuseStep 12458879 = 18688319) B18688319
theorem B1260511 : Blo 1260448 1260511 := bstep (se 1 (by rfl) ⟨945383, by rfl⟩ : syracuseStep 1260511 = 1890767) B1890767
theorem B1891439 : Blo 1260448 1891439 := bstep (se 1 (by rfl) ⟨1418579, by rfl⟩ : syracuseStep 1891439 = 2837159) B2837159
theorem B1260711 : Blo 1260448 1260711 := bstep (se 1 (by rfl) ⟨945533, by rfl⟩ : syracuseStep 1260711 = 1891067) B1891067
theorem B9575657 : Blo 1260448 9575657 := bstep (se 2 (by rfl) ⟨3590871, by rfl⟩ : syracuseStep 9575657 = 7181743) B7181743
theorem B1260795 : Blo 1260448 1260795 := bstep (se 1 (by rfl) ⟨945596, by rfl⟩ : syracuseStep 1260795 = 1891193) B1891193
theorem B3235067 : Blo 1260448 3235067 := bstep (se 1 (by rfl) ⟨2426300, by rfl⟩ : syracuseStep 3235067 = 4852601) B4852601
theorem B1260799 : Blo 1260448 1260799 := bstep (se 1 (by rfl) ⟨945599, by rfl⟩ : syracuseStep 1260799 = 1891199) B1891199
theorem B4259465 : Blo 1260448 4259465 := bstep (se 2 (by rfl) ⟨1597299, by rfl⟩ : syracuseStep 4259465 = 3194599) B3194599
theorem B1261403 : Blo 1260448 1261403 := bstep (se 1 (by rfl) ⟨946052, by rfl⟩ : syracuseStep 1261403 = 1892105) B1892105
theorem B1261659 : Blo 1260448 1261659 := bstep (se 1 (by rfl) ⟨946244, by rfl⟩ : syracuseStep 1261659 = 1892489) B1892489
theorem B6381665 : Blo 1260448 6381665 := bstep (se 2 (by rfl) ⟨2393124, by rfl⟩ : syracuseStep 6381665 = 4786249) B4786249
theorem B4259951 : Blo 1260448 4259951 := bstep (se 1 (by rfl) ⟨3194963, by rfl⟩ : syracuseStep 4259951 = 6389927) B6389927
theorem B3195035 : Blo 1260448 3195035 := bstep (se 1 (by rfl) ⟨2396276, by rfl⟩ : syracuseStep 3195035 = 4792553) B4792553
theorem B1892591 : Blo 1260448 1892591 := bstep (se 1 (by rfl) ⟨1419443, by rfl⟩ : syracuseStep 1892591 = 2838887) B2838887
theorem B6914443 : Blo 1260448 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B1892975 : Blo 1260448 1892975 := bstep (se 1 (by rfl) ⟨1419731, by rfl⟩ : syracuseStep 1892975 = 2839463) B2839463
theorem B33219215 : Blo 1260448 33219215 := bstep (se 1 (by rfl) ⟨24914411, by rfl⟩ : syracuseStep 33219215 = 49828823) B49828823
theorem B21537575 : Blo 1260448 21537575 := bstep (se 1 (by rfl) ⟨16153181, by rfl⟩ : syracuseStep 21537575 = 32306363) B32306363
theorem B1893257 : Blo 1260448 1893257 := bstep (se 2 (by rfl) ⟨709971, by rfl⟩ : syracuseStep 1893257 = 1419943) B1419943
theorem B34513937 : Blo 1260448 34513937 := bstep (se 2 (by rfl) ⟨12942726, by rfl⟩ : syracuseStep 34513937 = 25885453) B25885453
theorem B9586349 : Blo 1260448 9586349 := bstep (se 3 (by rfl) ⟨1797440, by rfl⟩ : syracuseStep 9586349 = 3594881) B3594881
theorem B6383771 : Blo 1260448 6383771 := bstep (se 1 (by rfl) ⟨4787828, by rfl⟩ : syracuseStep 6383771 = 9575657) B9575657
theorem B2156711 : Blo 1260448 2156711 := bstep (se 1 (by rfl) ⟨1617533, by rfl⟩ : syracuseStep 2156711 = 3235067) B3235067
theorem B92072153 : Blo 1260448 92072153 := bstep (se 2 (by rfl) ⟨34527057, by rfl⟩ : syracuseStep 92072153 = 69054115) B69054115
theorem B2836943 : Blo 1260448 2836943 := bstep (se 1 (by rfl) ⟨2127707, by rfl⟩ : syracuseStep 2836943 = 4255415) B4255415
theorem B32787035 : Blo 1260448 32787035 := bstep (se 1 (by rfl) ⟨24590276, by rfl⟩ : syracuseStep 32787035 = 49180553) B49180553
theorem B1420159 : Blo 1260448 1420159 := bstep (se 1 (by rfl) ⟨1065119, by rfl⟩ : syracuseStep 1420159 = 2130239) B2130239
theorem B4254875 : Blo 1260448 4254875 := bstep (se 1 (by rfl) ⟨3191156, by rfl⟩ : syracuseStep 4254875 = 6382313) B6382313
theorem B3591647 : Blo 1260448 3591647 := bstep (se 1 (by rfl) ⟨2693735, by rfl⟩ : syracuseStep 3591647 = 5387471) B5387471
theorem B597733037 : Blo 1260448 597733037 := bstep (se 3 (by rfl) ⟨112074944, by rfl⟩ : syracuseStep 597733037 = 224149889) B224149889
theorem B33214151 : Blo 1260448 33214151 := bstep (se 1 (by rfl) ⟨24910613, by rfl⟩ : syracuseStep 33214151 = 49821227) B49821227
theorem B87445403 : Blo 1260448 87445403 := bstep (se 1 (by rfl) ⟨65584052, by rfl⟩ : syracuseStep 87445403 = 131168105) B131168105
theorem B2273503 : Blo 1260448 2273503 := bstep (se 1 (by rfl) ⟨1705127, by rfl⟩ : syracuseStep 2273503 = 3410255) B3410255
theorem B5755279 : Blo 1260448 5755279 := bstep (se 1 (by rfl) ⟨4316459, by rfl⟩ : syracuseStep 5755279 = 8632919) B8632919
theorem B4788679 : Blo 1260448 4788679 := bstep (se 1 (by rfl) ⟨3591509, by rfl⟩ : syracuseStep 4788679 = 7183019) B7183019
theorem B79762457 : Blo 1260448 79762457 := bstep (se 2 (by rfl) ⟨29910921, by rfl⟩ : syracuseStep 79762457 = 59821843) B59821843
theorem B2839643 : Blo 1260448 2839643 := bstep (se 1 (by rfl) ⟨2129732, by rfl⟩ : syracuseStep 2839643 = 4259465) B4259465
theorem B6386849 : Blo 1260448 6386849 := bstep (se 2 (by rfl) ⟨2395068, by rfl⟩ : syracuseStep 6386849 = 4790137) B4790137
theorem B2127161 : Blo 1260448 2127161 := bstep (se 2 (by rfl) ⟨797685, by rfl⟩ : syracuseStep 2127161 = 1595371) B1595371
theorem B9573713 : Blo 1260448 9573713 := bstep (se 2 (by rfl) ⟨3590142, by rfl⟩ : syracuseStep 9573713 = 7180285) B7180285
theorem B2127215 : Blo 1260448 2127215 := bstep (se 1 (by rfl) ⟨1595411, by rfl⟩ : syracuseStep 2127215 = 3190823) B3190823
theorem B4544381 : Blo 1260448 4544381 := bstep (se 3 (by rfl) ⟨852071, by rfl⟩ : syracuseStep 4544381 = 1704143) B1704143
theorem B15341471 : Blo 1260448 15341471 := bstep (se 1 (by rfl) ⟨11506103, by rfl⟩ : syracuseStep 15341471 = 23012207) B23012207
theorem B4257737 : Blo 1260448 4257737 := bstep (se 2 (by rfl) ⟨1596651, by rfl⟩ : syracuseStep 4257737 = 3193303) B3193303
theorem B2021449 : Blo 1260448 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B2693351 : Blo 1260448 2693351 := bstep (se 1 (by rfl) ⟨2020013, by rfl⟩ : syracuseStep 2693351 = 4040027) B4040027
theorem B4315447 : Blo 1260448 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B16177481 : Blo 1260448 16177481 := bstep (se 2 (by rfl) ⟨6066555, by rfl⟩ : syracuseStep 16177481 = 12133111) B12133111
theorem B4790609 : Blo 1260448 4790609 := bstep (se 2 (by rfl) ⟨1796478, by rfl⟩ : syracuseStep 4790609 = 3592957) B3592957
theorem B16169381 : Blo 1260448 16169381 := bstep (se 4 (by rfl) ⟨1515879, by rfl⟩ : syracuseStep 16169381 = 3031759) B3031759
theorem B16161383 : Blo 1260448 16161383 := bstep (se 1 (by rfl) ⟨12121037, by rfl⟩ : syracuseStep 16161383 = 24242075) B24242075
theorem B2128639 : Blo 1260448 2128639 := bstep (se 1 (by rfl) ⟨1596479, by rfl⟩ : syracuseStep 2128639 = 3192959) B3192959
theorem B3193627 : Blo 1260448 3193627 := bstep (se 1 (by rfl) ⟨2395220, by rfl⟩ : syracuseStep 3193627 = 4790441) B4790441
theorem B7674679 : Blo 1260448 7674679 := bstep (se 1 (by rfl) ⟨5756009, by rfl⟩ : syracuseStep 7674679 = 11512019) B11512019
theorem B4258871 : Blo 1260448 4258871 := bstep (se 1 (by rfl) ⟨3194153, by rfl⟩ : syracuseStep 4258871 = 6388307) B6388307
theorem B1260647 : Blo 1260448 1260647 := bstep (se 1 (by rfl) ⟨945485, by rfl⟩ : syracuseStep 1260647 = 1890971) B1890971
theorem B3030203 : Blo 1260448 3030203 := bstep (se 1 (by rfl) ⟨2272652, by rfl⟩ : syracuseStep 3030203 = 4545305) B4545305
theorem B3194063 : Blo 1260448 3194063 := bstep (se 1 (by rfl) ⟨2395547, by rfl⟩ : syracuseStep 3194063 = 4791095) B4791095
theorem B8305919 : Blo 1260448 8305919 := bstep (se 1 (by rfl) ⟨6229439, by rfl⟩ : syracuseStep 8305919 = 12458879) B12458879
theorem B1260959 : Blo 1260448 1260959 := bstep (se 1 (by rfl) ⟨945719, by rfl⟩ : syracuseStep 1260959 = 1891439) B1891439
theorem B1891943 : Blo 1260448 1891943 := bstep (se 1 (by rfl) ⟨1418957, by rfl⟩ : syracuseStep 1891943 = 2837915) B2837915
theorem B1892009 : Blo 1260448 1892009 := bstep (se 2 (by rfl) ⟨709503, by rfl⟩ : syracuseStep 1892009 = 1419007) B1419007
theorem B3194761 : Blo 1260448 3194761 := bstep (se 2 (by rfl) ⟨1198035, by rfl⟩ : syracuseStep 3194761 = 2396071) B2396071
theorem B1892345 : Blo 1260448 1892345 := bstep (se 2 (by rfl) ⟨709629, by rfl⟩ : syracuseStep 1892345 = 1419259) B1419259
theorem B2695265 : Blo 1260448 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B2130023 : Blo 1260448 2130023 := bstep (se 1 (by rfl) ⟨1597517, by rfl⟩ : syracuseStep 2130023 = 3195035) B3195035
theorem B1261727 : Blo 1260448 1261727 := bstep (se 1 (by rfl) ⟨946295, by rfl⟩ : syracuseStep 1261727 = 1892591) B1892591
theorem B3031337 : Blo 1260448 3031337 := bstep (se 2 (by rfl) ⟨1136751, by rfl⟩ : syracuseStep 3031337 = 2273503) B2273503
theorem B1261983 : Blo 1260448 1261983 := bstep (se 1 (by rfl) ⟨946487, by rfl⟩ : syracuseStep 1261983 = 1892975) B1892975
theorem B1262171 : Blo 1260448 1262171 := bstep (se 1 (by rfl) ⟨946628, by rfl⟩ : syracuseStep 1262171 = 1893257) B1893257
theorem B53174971 : Blo 1260448 53174971 := bstep (se 1 (by rfl) ⟨39881228, by rfl⟩ : syracuseStep 53174971 = 79762457) B79762457
theorem B1893095 : Blo 1260448 1893095 := bstep (se 1 (by rfl) ⟨1419821, by rfl⟩ : syracuseStep 1893095 = 2839643) B2839643
theorem B1418107 : Blo 1260448 1418107 := bstep (se 1 (by rfl) ⟨1063580, by rfl⟩ : syracuseStep 1418107 = 2127161) B2127161
theorem B6382475 : Blo 1260448 6382475 := bstep (se 1 (by rfl) ⟨4786856, by rfl⟩ : syracuseStep 6382475 = 9573713) B9573713
theorem B1418143 : Blo 1260448 1418143 := bstep (se 1 (by rfl) ⟨1063607, by rfl⟩ : syracuseStep 1418143 = 2127215) B2127215
theorem B10232905 : Blo 1260448 10232905 := bstep (se 2 (by rfl) ⟨3837339, by rfl⟩ : syracuseStep 10232905 = 7674679) B7674679
theorem B6390899 : Blo 1260448 6390899 := bstep (se 1 (by rfl) ⟨4793174, by rfl⟩ : syracuseStep 6390899 = 9586349) B9586349
theorem B1893545 : Blo 1260448 1893545 := bstep (se 2 (by rfl) ⟨710079, by rfl⟩ : syracuseStep 1893545 = 1420159) B1420159
theorem B21858023 : Blo 1260448 21858023 := bstep (se 1 (by rfl) ⟨16393517, by rfl⟩ : syracuseStep 21858023 = 32787035) B32787035
theorem B10774255 : Blo 1260448 10774255 := bstep (se 1 (by rfl) ⟨8080691, by rfl⟩ : syracuseStep 10774255 = 16161383) B16161383
theorem B23004917 : Blo 1260448 23004917 := bstep (se 5 (by rfl) ⟨1078355, by rfl⟩ : syracuseStep 23004917 = 2156711) B2156711
theorem B2836583 : Blo 1260448 2836583 := bstep (se 1 (by rfl) ⟨2127437, by rfl⟩ : syracuseStep 2836583 = 4254875) B4254875
theorem B2394431 : Blo 1260448 2394431 := bstep (se 1 (by rfl) ⟨1795823, by rfl⟩ : syracuseStep 2394431 = 3591647) B3591647
theorem B12118349 : Blo 1260448 12118349 := bstep (se 3 (by rfl) ⟨2272190, by rfl⟩ : syracuseStep 12118349 = 4544381) B4544381
theorem B58296935 : Blo 1260448 58296935 := bstep (se 1 (by rfl) ⟨43722701, by rfl⟩ : syracuseStep 58296935 = 87445403) B87445403
theorem B4254443 : Blo 1260448 4254443 := bstep (se 1 (by rfl) ⟨3190832, by rfl⟩ : syracuseStep 4254443 = 6381665) B6381665
theorem B5753929 : Blo 1260448 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B22146143 : Blo 1260448 22146143 := bstep (se 1 (by rfl) ⟨16609607, by rfl⟩ : syracuseStep 22146143 = 33219215) B33219215
theorem B9219257 : Blo 1260448 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B245525741 : Blo 1260448 245525741 := bstep (se 3 (by rfl) ⟨46036076, by rfl⟩ : syracuseStep 245525741 = 92072153) B92072153
theorem B6384905 : Blo 1260448 6384905 := bstep (se 2 (by rfl) ⟨2394339, by rfl⟩ : syracuseStep 6384905 = 4788679) B4788679
theorem B2838185 : Blo 1260448 2838185 := bstep (se 2 (by rfl) ⟨1064319, by rfl⟩ : syracuseStep 2838185 = 2128639) B2128639
theorem B10227647 : Blo 1260448 10227647 := bstep (se 1 (by rfl) ⟨7670735, by rfl⟩ : syracuseStep 10227647 = 15341471) B15341471
theorem B2838491 : Blo 1260448 2838491 := bstep (se 1 (by rfl) ⟨2128868, by rfl⟩ : syracuseStep 2838491 = 4257737) B4257737
theorem B4255847 : Blo 1260448 4255847 := bstep (se 1 (by rfl) ⟨3191885, by rfl⟩ : syracuseStep 4255847 = 6383771) B6383771
theorem B10784987 : Blo 1260448 10784987 := bstep (se 1 (by rfl) ⟨8088740, by rfl⟩ : syracuseStep 10784987 = 16177481) B16177481
theorem B2839247 : Blo 1260448 2839247 := bstep (se 1 (by rfl) ⟨2129435, by rfl⟩ : syracuseStep 2839247 = 4258871) B4258871
theorem B2020135 : Blo 1260448 2020135 := bstep (se 1 (by rfl) ⟨1515101, by rfl⟩ : syracuseStep 2020135 = 3030203) B3030203
theorem B398488691 : Blo 1260448 398488691 := bstep (se 1 (by rfl) ⟨298866518, by rfl⟩ : syracuseStep 398488691 = 597733037) B597733037
theorem B2839967 : Blo 1260448 2839967 := bstep (se 1 (by rfl) ⟨2129975, by rfl⟩ : syracuseStep 2839967 = 4259951) B4259951
theorem B7673705 : Blo 1260448 7673705 := bstep (se 2 (by rfl) ⟨2877639, by rfl⟩ : syracuseStep 7673705 = 5755279) B5755279
theorem B14358383 : Blo 1260448 14358383 := bstep (se 1 (by rfl) ⟨10768787, by rfl⟩ : syracuseStep 14358383 = 21537575) B21537575
theorem B7182269 : Blo 1260448 7182269 := bstep (se 3 (by rfl) ⟨1346675, by rfl⟩ : syracuseStep 7182269 = 2693351) B2693351
theorem B23009291 : Blo 1260448 23009291 := bstep (se 1 (by rfl) ⟨17256968, by rfl⟩ : syracuseStep 23009291 = 34513937) B34513937
theorem B4257899 : Blo 1260448 4257899 := bstep (se 1 (by rfl) ⟨3193424, by rfl⟩ : syracuseStep 4257899 = 6386849) B6386849
theorem B4258169 : Blo 1260448 4258169 := bstep (se 2 (by rfl) ⟨1596813, by rfl⟩ : syracuseStep 4258169 = 3193627) B3193627
theorem B3193739 : Blo 1260448 3193739 := bstep (se 1 (by rfl) ⟨2395304, by rfl⟩ : syracuseStep 3193739 = 4790609) B4790609
theorem B10779587 : Blo 1260448 10779587 := bstep (se 1 (by rfl) ⟨8084690, by rfl⟩ : syracuseStep 10779587 = 16169381) B16169381
theorem B1891295 : Blo 1260448 1891295 := bstep (se 1 (by rfl) ⟨1418471, by rfl⟩ : syracuseStep 1891295 = 2836943) B2836943
theorem B2129375 : Blo 1260448 2129375 := bstep (se 1 (by rfl) ⟨1597031, by rfl⟩ : syracuseStep 2129375 = 3194063) B3194063
theorem B5537279 : Blo 1260448 5537279 := bstep (se 1 (by rfl) ⟨4152959, by rfl⟩ : syracuseStep 5537279 = 8305919) B8305919
theorem B1261295 : Blo 1260448 1261295 := bstep (se 1 (by rfl) ⟨945971, by rfl⟩ : syracuseStep 1261295 = 1891943) B1891943
theorem B1261339 : Blo 1260448 1261339 := bstep (se 1 (by rfl) ⟨946004, by rfl⟩ : syracuseStep 1261339 = 1892009) B1892009
theorem B22142767 : Blo 1260448 22142767 := bstep (se 1 (by rfl) ⟨16607075, by rfl⟩ : syracuseStep 22142767 = 33214151) B33214151
theorem B4259681 : Blo 1260448 4259681 := bstep (se 2 (by rfl) ⟨1597380, by rfl⟩ : syracuseStep 4259681 = 3194761) B3194761
theorem B1261563 : Blo 1260448 1261563 := bstep (se 1 (by rfl) ⟨946172, by rfl⟩ : syracuseStep 1261563 = 1892345) B1892345
theorem B59056381 : Blo 1260448 59056381 := bstep (se 3 (by rfl) ⟨11073071, by rfl⟩ : syracuseStep 59056381 = 22146143) B22146143
theorem B1892831 : Blo 1260448 1892831 := bstep (se 1 (by rfl) ⟨1419623, by rfl⟩ : syracuseStep 1892831 = 2839247) B2839247
theorem B1262063 : Blo 1260448 1262063 := bstep (se 1 (by rfl) ⟨946547, by rfl⟩ : syracuseStep 1262063 = 1893095) B1893095
theorem B4260599 : Blo 1260448 4260599 := bstep (se 1 (by rfl) ⟨3195449, by rfl⟩ : syracuseStep 4260599 = 6390899) B6390899
theorem B1262363 : Blo 1260448 1262363 := bstep (se 1 (by rfl) ⟨946772, by rfl⟩ : syracuseStep 1262363 = 1893545) B1893545
theorem B1893311 : Blo 1260448 1893311 := bstep (se 1 (by rfl) ⟨1419983, by rfl⟩ : syracuseStep 1893311 = 2839967) B2839967
theorem B15336611 : Blo 1260448 15336611 := bstep (se 1 (by rfl) ⟨11502458, by rfl⟩ : syracuseStep 15336611 = 23004917) B23004917
theorem B8078899 : Blo 1260448 8078899 := bstep (se 1 (by rfl) ⟨6059174, by rfl⟩ : syracuseStep 8078899 = 12118349) B12118349
theorem B38864623 : Blo 1260448 38864623 := bstep (se 1 (by rfl) ⟨29148467, by rfl⟩ : syracuseStep 38864623 = 58296935) B58296935
theorem B2836295 : Blo 1260448 2836295 := bstep (se 1 (by rfl) ⟨2127221, by rfl⟩ : syracuseStep 2836295 = 4254443) B4254443
theorem B58288061 : Blo 1260448 58288061 := bstep (se 3 (by rfl) ⟨10929011, by rfl⟩ : syracuseStep 58288061 = 21858023) B21858023
theorem B7186391 : Blo 1260448 7186391 := bstep (se 1 (by rfl) ⟨5389793, by rfl⟩ : syracuseStep 7186391 = 10779587) B10779587
theorem B6146171 : Blo 1260448 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B1419583 : Blo 1260448 1419583 := bstep (se 1 (by rfl) ⟨1064687, by rfl⟩ : syracuseStep 1419583 = 2129375) B2129375
theorem B6818431 : Blo 1260448 6818431 := bstep (se 1 (by rfl) ⟨5113823, by rfl⟩ : syracuseStep 6818431 = 10227647) B10227647
theorem B1796843 : Blo 1260448 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B2837231 : Blo 1260448 2837231 := bstep (se 1 (by rfl) ⟨2127923, by rfl⟩ : syracuseStep 2837231 = 4255847) B4255847
theorem B1420015 : Blo 1260448 1420015 := bstep (se 1 (by rfl) ⟨1065011, by rfl⟩ : syracuseStep 1420015 = 2130023) B2130023
theorem B1062636509 : Blo 1260448 1062636509 := bstep (se 3 (by rfl) ⟨199244345, by rfl⟩ : syracuseStep 1062636509 = 398488691) B398488691
theorem B4254983 : Blo 1260448 4254983 := bstep (se 1 (by rfl) ⟨3191237, by rfl⟩ : syracuseStep 4254983 = 6382475) B6382475
theorem B5115803 : Blo 1260448 5115803 := bstep (se 1 (by rfl) ⟨3836852, by rfl⟩ : syracuseStep 5115803 = 7673705) B7673705
theorem B9572255 : Blo 1260448 9572255 := bstep (se 1 (by rfl) ⟨7179191, by rfl⟩ : syracuseStep 9572255 = 14358383) B14358383
theorem B4788179 : Blo 1260448 4788179 := bstep (se 1 (by rfl) ⟨3591134, by rfl⟩ : syracuseStep 4788179 = 7182269) B7182269
theorem B14766077 : Blo 1260448 14766077 := bstep (se 3 (by rfl) ⟨2768639, by rfl⟩ : syracuseStep 14766077 = 5537279) B5537279
theorem B15339527 : Blo 1260448 15339527 := bstep (se 1 (by rfl) ⟨11504645, by rfl⟩ : syracuseStep 15339527 = 23009291) B23009291
theorem B2838599 : Blo 1260448 2838599 := bstep (se 1 (by rfl) ⟨2128949, by rfl⟩ : syracuseStep 2838599 = 4257899) B4257899
theorem B7671905 : Blo 1260448 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B13643873 : Blo 1260448 13643873 := bstep (se 2 (by rfl) ⟨5116452, by rfl⟩ : syracuseStep 13643873 = 10232905) B10232905
theorem B2838779 : Blo 1260448 2838779 := bstep (se 1 (by rfl) ⟨2129084, by rfl⟩ : syracuseStep 2838779 = 4258169) B4258169
theorem B4256603 : Blo 1260448 4256603 := bstep (se 1 (by rfl) ⟨3192452, by rfl⟩ : syracuseStep 4256603 = 6384905) B6384905
theorem B14365673 : Blo 1260448 14365673 := bstep (se 2 (by rfl) ⟨5387127, by rfl⟩ : syracuseStep 14365673 = 10774255) B10774255
theorem B2839787 : Blo 1260448 2839787 := bstep (se 1 (by rfl) ⟨2129840, by rfl⟩ : syracuseStep 2839787 = 4259681) B4259681
theorem B7189991 : Blo 1260448 7189991 := bstep (se 1 (by rfl) ⟨5392493, by rfl⟩ : syracuseStep 7189991 = 10784987) B10784987
theorem B2020891 : Blo 1260448 2020891 := bstep (se 1 (by rfl) ⟨1515668, by rfl⟩ : syracuseStep 2020891 = 3031337) B3031337
theorem B70899961 : Blo 1260448 70899961 := bstep (se 2 (by rfl) ⟨26587485, by rfl⟩ : syracuseStep 70899961 = 53174971) B53174971
theorem B2693513 : Blo 1260448 2693513 := bstep (se 2 (by rfl) ⟨1010067, by rfl⟩ : syracuseStep 2693513 = 2020135) B2020135
theorem B1890809 : Blo 1260448 1890809 := bstep (se 2 (by rfl) ⟨709053, by rfl⟩ : syracuseStep 1890809 = 1418107) B1418107
theorem B1890857 : Blo 1260448 1890857 := bstep (se 2 (by rfl) ⟨709071, by rfl⟩ : syracuseStep 1890857 = 1418143) B1418143
theorem B1891055 : Blo 1260448 1891055 := bstep (se 1 (by rfl) ⟨1418291, by rfl⟩ : syracuseStep 1891055 = 2836583) B2836583
theorem B1596287 : Blo 1260448 1596287 := bstep (se 1 (by rfl) ⟨1197215, by rfl⟩ : syracuseStep 1596287 = 2394431) B2394431
theorem B2129159 : Blo 1260448 2129159 := bstep (se 1 (by rfl) ⟨1596869, by rfl⟩ : syracuseStep 2129159 = 3193739) B3193739
theorem B1260863 : Blo 1260448 1260863 := bstep (se 1 (by rfl) ⟨945647, by rfl⟩ : syracuseStep 1260863 = 1891295) B1891295
theorem B163683827 : Blo 1260448 163683827 := bstep (se 1 (by rfl) ⟨122762870, by rfl⟩ : syracuseStep 163683827 = 245525741) B245525741
theorem B29523689 : Blo 1260448 29523689 := bstep (se 2 (by rfl) ⟨11071383, by rfl⟩ : syracuseStep 29523689 = 22142767) B22142767
theorem B1892123 : Blo 1260448 1892123 := bstep (se 1 (by rfl) ⟨1419092, by rfl⟩ : syracuseStep 1892123 = 2838185) B2838185
theorem B1892327 : Blo 1260448 1892327 := bstep (se 1 (by rfl) ⟨1419245, by rfl⟩ : syracuseStep 1892327 = 2838491) B2838491
theorem B1892399 : Blo 1260448 1892399 := bstep (se 1 (by rfl) ⟨1419299, by rfl⟩ : syracuseStep 1892399 = 2838599) B2838599
theorem B1892519 : Blo 1260448 1892519 := bstep (se 1 (by rfl) ⟨1419389, by rfl⟩ : syracuseStep 1892519 = 2838779) B2838779
theorem B1261887 : Blo 1260448 1261887 := bstep (se 1 (by rfl) ⟨946415, by rfl⟩ : syracuseStep 1261887 = 1892831) B1892831
theorem B78741841 : Blo 1260448 78741841 := bstep (se 2 (by rfl) ⟨29528190, by rfl⟩ : syracuseStep 78741841 = 59056381) B59056381
theorem B1892777 : Blo 1260448 1892777 := bstep (se 2 (by rfl) ⟨709791, by rfl⟩ : syracuseStep 1892777 = 1419583) B1419583
theorem B1262207 : Blo 1260448 1262207 := bstep (se 1 (by rfl) ⟨946655, by rfl⟩ : syracuseStep 1262207 = 1893311) B1893311
theorem B9577115 : Blo 1260448 9577115 := bstep (se 1 (by rfl) ⟨7182836, by rfl⟩ : syracuseStep 9577115 = 14365673) B14365673
theorem B10224407 : Blo 1260448 10224407 := bstep (se 1 (by rfl) ⟨7668305, by rfl⟩ : syracuseStep 10224407 = 15336611) B15336611
theorem B1893191 : Blo 1260448 1893191 := bstep (se 1 (by rfl) ⟨1419893, by rfl⟩ : syracuseStep 1893191 = 2839787) B2839787
theorem B1893353 : Blo 1260448 1893353 := bstep (se 2 (by rfl) ⟨710007, by rfl⟩ : syracuseStep 1893353 = 1420015) B1420015
theorem B4793327 : Blo 1260448 4793327 := bstep (se 1 (by rfl) ⟨3594995, by rfl⟩ : syracuseStep 4793327 = 7189991) B7189991
theorem B4097447 : Blo 1260448 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B2836655 : Blo 1260448 2836655 := bstep (se 1 (by rfl) ⟨2127491, by rfl⟩ : syracuseStep 2836655 = 4254983) B4254983
theorem B1419439 : Blo 1260448 1419439 := bstep (se 1 (by rfl) ⟨1064579, by rfl⟩ : syracuseStep 1419439 = 2129159) B2129159
theorem B13642141 : Blo 1260448 13642141 := bstep (se 3 (by rfl) ⟨2557901, by rfl⟩ : syracuseStep 13642141 = 5115803) B5115803
theorem B2833697357 : Blo 1260448 2833697357 := bstep (se 3 (by rfl) ⟨531318254, by rfl⟩ : syracuseStep 2833697357 = 1062636509) B1062636509
theorem B10226351 : Blo 1260448 10226351 := bstep (se 1 (by rfl) ⟨7669763, by rfl⟩ : syracuseStep 10226351 = 15339527) B15339527
theorem B5114603 : Blo 1260448 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B9095915 : Blo 1260448 9095915 := bstep (se 1 (by rfl) ⟨6821936, by rfl⟩ : syracuseStep 9095915 = 13643873) B13643873
theorem B2837735 : Blo 1260448 2837735 := bstep (se 1 (by rfl) ⟨2128301, by rfl⟩ : syracuseStep 2837735 = 4256603) B4256603
theorem B38858707 : Blo 1260448 38858707 := bstep (se 1 (by rfl) ⟨29144030, by rfl⟩ : syracuseStep 38858707 = 58288061) B58288061
theorem B51819497 : Blo 1260448 51819497 := bstep (se 2 (by rfl) ⟨19432311, by rfl⟩ : syracuseStep 51819497 = 38864623) B38864623
theorem B109122551 : Blo 1260448 109122551 := bstep (se 1 (by rfl) ⟨81841913, by rfl⟩ : syracuseStep 109122551 = 163683827) B163683827
theorem B4256765 : Blo 1260448 4256765 := bstep (se 3 (by rfl) ⟨798143, by rfl⟩ : syracuseStep 4256765 = 1596287) B1596287
theorem B19682459 : Blo 1260448 19682459 := bstep (se 1 (by rfl) ⟨14761844, by rfl⟩ : syracuseStep 19682459 = 29523689) B29523689
theorem B3192119 : Blo 1260448 3192119 := bstep (se 1 (by rfl) ⟨2394089, by rfl⟩ : syracuseStep 3192119 = 4788179) B4788179
theorem B39376205 : Blo 1260448 39376205 := bstep (se 3 (by rfl) ⟨7383038, by rfl⟩ : syracuseStep 39376205 = 14766077) B14766077
theorem B94533281 : Blo 1260448 94533281 := bstep (se 2 (by rfl) ⟨35449980, by rfl⟩ : syracuseStep 94533281 = 70899961) B70899961
theorem B2840399 : Blo 1260448 2840399 := bstep (se 1 (by rfl) ⟨2130299, by rfl⟩ : syracuseStep 2840399 = 4260599) B4260599
theorem B9091241 : Blo 1260448 9091241 := bstep (se 2 (by rfl) ⟨3409215, by rfl⟩ : syracuseStep 9091241 = 6818431) B6818431
theorem B7182701 : Blo 1260448 7182701 := bstep (se 3 (by rfl) ⟨1346756, by rfl⟩ : syracuseStep 7182701 = 2693513) B2693513
theorem B1890863 : Blo 1260448 1890863 := bstep (se 1 (by rfl) ⟨1418147, by rfl⟩ : syracuseStep 1890863 = 2836295) B2836295
theorem B4790927 : Blo 1260448 4790927 := bstep (se 1 (by rfl) ⟨3593195, by rfl⟩ : syracuseStep 4790927 = 7186391) B7186391
theorem B1260539 : Blo 1260448 1260539 := bstep (se 1 (by rfl) ⟨945404, by rfl⟩ : syracuseStep 1260539 = 1890809) B1890809
theorem B1260571 : Blo 1260448 1260571 := bstep (se 1 (by rfl) ⟨945428, by rfl⟩ : syracuseStep 1260571 = 1890857) B1890857
theorem B1260703 : Blo 1260448 1260703 := bstep (se 1 (by rfl) ⟨945527, by rfl⟩ : syracuseStep 1260703 = 1891055) B1891055
theorem B1891487 : Blo 1260448 1891487 := bstep (se 1 (by rfl) ⟨1418615, by rfl⟩ : syracuseStep 1891487 = 2837231) B2837231
theorem B4791581 : Blo 1260448 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B2694521 : Blo 1260448 2694521 := bstep (se 2 (by rfl) ⟨1010445, by rfl⟩ : syracuseStep 2694521 = 2020891) B2020891
theorem B10771865 : Blo 1260448 10771865 := bstep (se 2 (by rfl) ⟨4039449, by rfl⟩ : syracuseStep 10771865 = 8078899) B8078899
theorem B1261415 : Blo 1260448 1261415 := bstep (se 1 (by rfl) ⟨946061, by rfl⟩ : syracuseStep 1261415 = 1892123) B1892123
theorem B6381503 : Blo 1260448 6381503 := bstep (se 1 (by rfl) ⟨4786127, by rfl⟩ : syracuseStep 6381503 = 9572255) B9572255
theorem B1261551 : Blo 1260448 1261551 := bstep (se 1 (by rfl) ⟨946163, by rfl⟩ : syracuseStep 1261551 = 1892327) B1892327
theorem B1261599 : Blo 1260448 1261599 := bstep (se 1 (by rfl) ⟨946199, by rfl⟩ : syracuseStep 1261599 = 1892399) B1892399
theorem B1261679 : Blo 1260448 1261679 := bstep (se 1 (by rfl) ⟨946259, by rfl⟩ : syracuseStep 1261679 = 1892519) B1892519
theorem B1892585 : Blo 1260448 1892585 := bstep (se 2 (by rfl) ⟨709719, by rfl⟩ : syracuseStep 1892585 = 1419439) B1419439
theorem B1261851 : Blo 1260448 1261851 := bstep (se 1 (by rfl) ⟨946388, by rfl⟩ : syracuseStep 1261851 = 1892777) B1892777
theorem B104989121 : Blo 1260448 104989121 := bstep (se 2 (by rfl) ⟨39370920, by rfl⟩ : syracuseStep 104989121 = 78741841) B78741841
theorem B6816271 : Blo 1260448 6816271 := bstep (se 1 (by rfl) ⟨5112203, by rfl⟩ : syracuseStep 6816271 = 10224407) B10224407
theorem B1262127 : Blo 1260448 1262127 := bstep (se 1 (by rfl) ⟨946595, by rfl⟩ : syracuseStep 1262127 = 1893191) B1893191
theorem B1262235 : Blo 1260448 1262235 := bstep (se 1 (by rfl) ⟨946676, by rfl⟩ : syracuseStep 1262235 = 1893353) B1893353
theorem B34546331 : Blo 1260448 34546331 := bstep (se 1 (by rfl) ⟨25909748, by rfl⟩ : syracuseStep 34546331 = 51819497) B51819497
theorem B3195551 : Blo 1260448 3195551 := bstep (se 1 (by rfl) ⟨2396663, by rfl⟩ : syracuseStep 3195551 = 4793327) B4793327
theorem B63022187 : Blo 1260448 63022187 := bstep (se 1 (by rfl) ⟨47266640, by rfl⟩ : syracuseStep 63022187 = 94533281) B94533281
theorem B1893599 : Blo 1260448 1893599 := bstep (se 1 (by rfl) ⟨1420199, by rfl⟩ : syracuseStep 1893599 = 2840399) B2840399
theorem B43706101 : Blo 1260448 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B6817567 : Blo 1260448 6817567 := bstep (se 1 (by rfl) ⟨5113175, by rfl⟩ : syracuseStep 6817567 = 10226351) B10226351
theorem B3409735 : Blo 1260448 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B6063943 : Blo 1260448 6063943 := bstep (se 1 (by rfl) ⟨4547957, by rfl⟩ : syracuseStep 6063943 = 9095915) B9095915
theorem B1796347 : Blo 1260448 1796347 := bstep (se 1 (by rfl) ⟨1347260, by rfl⟩ : syracuseStep 1796347 = 2694521) B2694521
theorem B4254335 : Blo 1260448 4254335 := bstep (se 1 (by rfl) ⟨3190751, by rfl⟩ : syracuseStep 4254335 = 6381503) B6381503
theorem B6384743 : Blo 1260448 6384743 := bstep (se 1 (by rfl) ⟨4788557, by rfl⟩ : syracuseStep 6384743 = 9577115) B9577115
theorem B18189521 : Blo 1260448 18189521 := bstep (se 2 (by rfl) ⟨6821070, by rfl⟩ : syracuseStep 18189521 = 13642141) B13642141
theorem B72748367 : Blo 1260448 72748367 := bstep (se 1 (by rfl) ⟨54561275, by rfl⟩ : syracuseStep 72748367 = 109122551) B109122551
theorem B2837843 : Blo 1260448 2837843 := bstep (se 1 (by rfl) ⟨2128382, by rfl⟩ : syracuseStep 2837843 = 4256765) B4256765
theorem B26250803 : Blo 1260448 26250803 := bstep (se 1 (by rfl) ⟨19688102, by rfl⟩ : syracuseStep 26250803 = 39376205) B39376205
theorem B4788467 : Blo 1260448 4788467 := bstep (se 1 (by rfl) ⟨3591350, by rfl⟩ : syracuseStep 4788467 = 7182701) B7182701
theorem B7181243 : Blo 1260448 7181243 := bstep (se 1 (by rfl) ⟨5385932, by rfl⟩ : syracuseStep 7181243 = 10771865) B10771865
theorem B51811609 : Blo 1260448 51811609 := bstep (se 2 (by rfl) ⟨19429353, by rfl⟩ : syracuseStep 51811609 = 38858707) B38858707
theorem B13121639 : Blo 1260448 13121639 := bstep (se 1 (by rfl) ⟨9841229, by rfl⟩ : syracuseStep 13121639 = 19682459) B19682459
theorem B2128079 : Blo 1260448 2128079 := bstep (se 1 (by rfl) ⟨1596059, by rfl⟩ : syracuseStep 2128079 = 3192119) B3192119
theorem B6060827 : Blo 1260448 6060827 := bstep (se 1 (by rfl) ⟨4545620, by rfl⟩ : syracuseStep 6060827 = 9091241) B9091241
theorem B1891103 : Blo 1260448 1891103 := bstep (se 1 (by rfl) ⟨1418327, by rfl⟩ : syracuseStep 1891103 = 2836655) B2836655
theorem B1260575 : Blo 1260448 1260575 := bstep (se 1 (by rfl) ⟨945431, by rfl⟩ : syracuseStep 1260575 = 1890863) B1890863
theorem B1889131571 : Blo 1260448 1889131571 := bstep (se 1 (by rfl) ⟨1416848678, by rfl⟩ : syracuseStep 1889131571 = 2833697357) B2833697357
theorem B3193951 : Blo 1260448 3193951 := bstep (se 1 (by rfl) ⟨2395463, by rfl⟩ : syracuseStep 3193951 = 4790927) B4790927
theorem B1260991 : Blo 1260448 1260991 := bstep (se 1 (by rfl) ⟨945743, by rfl⟩ : syracuseStep 1260991 = 1891487) B1891487
theorem B1891823 : Blo 1260448 1891823 := bstep (se 1 (by rfl) ⟨1418867, by rfl⟩ : syracuseStep 1891823 = 2837735) B2837735
theorem B3194387 : Blo 1260448 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B1261723 : Blo 1260448 1261723 := bstep (se 1 (by rfl) ⟨946292, by rfl⟩ : syracuseStep 1261723 = 1892585) B1892585
theorem B69992747 : Blo 1260448 69992747 := bstep (se 1 (by rfl) ⟨52494560, by rfl⟩ : syracuseStep 69992747 = 104989121) B104989121
theorem B2130367 : Blo 1260448 2130367 := bstep (se 1 (by rfl) ⟨1597775, by rfl⟩ : syracuseStep 2130367 = 3195551) B3195551
theorem B1262399 : Blo 1260448 1262399 := bstep (se 1 (by rfl) ⟨946799, by rfl⟩ : syracuseStep 1262399 = 1893599) B1893599
theorem B1418719 : Blo 1260448 1418719 := bstep (se 1 (by rfl) ⟨1064039, by rfl⟩ : syracuseStep 1418719 = 2128079) B2128079
theorem B2836223 : Blo 1260448 2836223 := bstep (se 1 (by rfl) ⟨2127167, by rfl⟩ : syracuseStep 2836223 = 4254335) B4254335
theorem B4040551 : Blo 1260448 4040551 := bstep (se 1 (by rfl) ⟨3030413, by rfl⟩ : syracuseStep 4040551 = 6060827) B6060827
theorem B12126347 : Blo 1260448 12126347 := bstep (se 1 (by rfl) ⟨9094760, by rfl⟩ : syracuseStep 12126347 = 18189521) B18189521
theorem B48498911 : Blo 1260448 48498911 := bstep (se 1 (by rfl) ⟨36374183, by rfl⟩ : syracuseStep 48498911 = 72748367) B72748367
theorem B17500535 : Blo 1260448 17500535 := bstep (se 1 (by rfl) ⟨13125401, by rfl⟩ : syracuseStep 17500535 = 26250803) B26250803
theorem B23030887 : Blo 1260448 23030887 := bstep (se 1 (by rfl) ⟨17273165, by rfl⟩ : syracuseStep 23030887 = 34546331) B34546331
theorem B4787495 : Blo 1260448 4787495 := bstep (se 1 (by rfl) ⟨3590621, by rfl⟩ : syracuseStep 4787495 = 7181243) B7181243
theorem B9088361 : Blo 1260448 9088361 := bstep (se 2 (by rfl) ⟨3408135, by rfl⟩ : syracuseStep 9088361 = 6816271) B6816271
theorem B9580517 : Blo 1260448 9580517 := bstep (se 4 (by rfl) ⟨898173, by rfl⟩ : syracuseStep 9580517 = 1796347) B1796347
theorem B4256495 : Blo 1260448 4256495 := bstep (se 1 (by rfl) ⟨3192371, by rfl⟩ : syracuseStep 4256495 = 6384743) B6384743
theorem B58274801 : Blo 1260448 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B9090089 : Blo 1260448 9090089 := bstep (se 2 (by rfl) ⟨3408783, by rfl⟩ : syracuseStep 9090089 = 6817567) B6817567
theorem B3192311 : Blo 1260448 3192311 := bstep (se 1 (by rfl) ⟨2394233, by rfl⟩ : syracuseStep 3192311 = 4788467) B4788467
theorem B42014791 : Blo 1260448 42014791 := bstep (se 1 (by rfl) ⟨31511093, by rfl⟩ : syracuseStep 42014791 = 63022187) B63022187
theorem B8747759 : Blo 1260448 8747759 := bstep (se 1 (by rfl) ⟨6560819, by rfl⟩ : syracuseStep 8747759 = 13121639) B13121639
theorem B4258601 : Blo 1260448 4258601 := bstep (se 2 (by rfl) ⟨1596975, by rfl⟩ : syracuseStep 4258601 = 3193951) B3193951
theorem B69082145 : Blo 1260448 69082145 := bstep (se 2 (by rfl) ⟨25905804, by rfl⟩ : syracuseStep 69082145 = 51811609) B51811609
theorem B1260735 : Blo 1260448 1260735 := bstep (se 1 (by rfl) ⟨945551, by rfl⟩ : syracuseStep 1260735 = 1891103) B1891103
theorem B1259421047 : Blo 1260448 1259421047 := bstep (se 1 (by rfl) ⟨944565785, by rfl⟩ : syracuseStep 1259421047 = 1889131571) B1889131571
theorem B1891895 : Blo 1260448 1891895 := bstep (se 1 (by rfl) ⟨1418921, by rfl⟩ : syracuseStep 1891895 = 2837843) B2837843
theorem B1261215 : Blo 1260448 1261215 := bstep (se 1 (by rfl) ⟨945911, by rfl⟩ : syracuseStep 1261215 = 1891823) B1891823
theorem B2129591 : Blo 1260448 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B4546313 : Blo 1260448 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B8085257 : Blo 1260448 8085257 := bstep (se 2 (by rfl) ⟨3031971, by rfl⟩ : syracuseStep 8085257 = 6063943) B6063943
theorem B46661831 : Blo 1260448 46661831 := bstep (se 1 (by rfl) ⟨34996373, by rfl⟩ : syracuseStep 46661831 = 69992747) B69992747
theorem B11667023 : Blo 1260448 11667023 := bstep (se 1 (by rfl) ⟨8750267, by rfl⟩ : syracuseStep 11667023 = 17500535) B17500535
theorem B1419727 : Blo 1260448 1419727 := bstep (se 1 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 1419727 = 2129591) B2129591
theorem B56019721 : Blo 1260448 56019721 := bstep (se 2 (by rfl) ⟨21007395, by rfl⟩ : syracuseStep 56019721 = 42014791) B42014791
theorem B2837663 : Blo 1260448 2837663 := bstep (se 1 (by rfl) ⟨2128247, by rfl⟩ : syracuseStep 2837663 = 4256495) B4256495
theorem B38849867 : Blo 1260448 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B30707849 : Blo 1260448 30707849 := bstep (se 2 (by rfl) ⟨11515443, by rfl⟩ : syracuseStep 30707849 = 23030887) B23030887
theorem B2839067 : Blo 1260448 2839067 := bstep (se 1 (by rfl) ⟨2129300, by rfl⟩ : syracuseStep 2839067 = 4258601) B4258601
theorem B3191663 : Blo 1260448 3191663 := bstep (se 1 (by rfl) ⟨2393747, by rfl⟩ : syracuseStep 3191663 = 4787495) B4787495
theorem B6058907 : Blo 1260448 6058907 := bstep (se 1 (by rfl) ⟨4544180, by rfl⟩ : syracuseStep 6058907 = 9088361) B9088361
theorem B5387401 : Blo 1260448 5387401 := bstep (se 2 (by rfl) ⟨2020275, by rfl⟩ : syracuseStep 5387401 = 4040551) B4040551
theorem B6387011 : Blo 1260448 6387011 := bstep (se 1 (by rfl) ⟨4790258, by rfl⟩ : syracuseStep 6387011 = 9580517) B9580517
theorem B2840489 : Blo 1260448 2840489 := bstep (se 2 (by rfl) ⟨1065183, by rfl⟩ : syracuseStep 2840489 = 2130367) B2130367
theorem B6060059 : Blo 1260448 6060059 := bstep (se 1 (by rfl) ⟨4545044, by rfl⟩ : syracuseStep 6060059 = 9090089) B9090089
theorem B2128207 : Blo 1260448 2128207 := bstep (se 1 (by rfl) ⟨1596155, by rfl⟩ : syracuseStep 2128207 = 3192311) B3192311
theorem B1890815 : Blo 1260448 1890815 := bstep (se 1 (by rfl) ⟨1418111, by rfl⟩ : syracuseStep 1890815 = 2836223) B2836223
theorem B8084231 : Blo 1260448 8084231 := bstep (se 1 (by rfl) ⟨6063173, by rfl⟩ : syracuseStep 8084231 = 12126347) B12126347
theorem B32332607 : Blo 1260448 32332607 := bstep (se 1 (by rfl) ⟨24249455, by rfl⟩ : syracuseStep 32332607 = 48498911) B48498911
theorem B5831839 : Blo 1260448 5831839 := bstep (se 1 (by rfl) ⟨4373879, by rfl⟩ : syracuseStep 5831839 = 8747759) B8747759
theorem B1891625 : Blo 1260448 1891625 := bstep (se 2 (by rfl) ⟨709359, by rfl⟩ : syracuseStep 1891625 = 1418719) B1418719
theorem B46054763 : Blo 1260448 46054763 := bstep (se 1 (by rfl) ⟨34541072, by rfl⟩ : syracuseStep 46054763 = 69082145) B69082145
theorem B839614031 : Blo 1260448 839614031 := bstep (se 1 (by rfl) ⟨629710523, by rfl⟩ : syracuseStep 839614031 = 1259421047) B1259421047
theorem B1261263 : Blo 1260448 1261263 := bstep (se 1 (by rfl) ⟨945947, by rfl⟩ : syracuseStep 1261263 = 1891895) B1891895
theorem B3030875 : Blo 1260448 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B5390171 : Blo 1260448 5390171 := bstep (se 1 (by rfl) ⟨4042628, by rfl⟩ : syracuseStep 5390171 = 8085257) B8085257
theorem B20471899 : Blo 1260448 20471899 := bstep (se 1 (by rfl) ⟨15353924, by rfl⟩ : syracuseStep 20471899 = 30707849) B30707849
theorem B1892711 : Blo 1260448 1892711 := bstep (se 1 (by rfl) ⟨1419533, by rfl⟩ : syracuseStep 1892711 = 2839067) B2839067
theorem B4039271 : Blo 1260448 4039271 := bstep (se 1 (by rfl) ⟨3029453, by rfl⟩ : syracuseStep 4039271 = 6058907) B6058907
theorem B1892969 : Blo 1260448 1892969 := bstep (se 2 (by rfl) ⟨709863, by rfl⟩ : syracuseStep 1892969 = 1419727) B1419727
theorem B1893659 : Blo 1260448 1893659 := bstep (se 1 (by rfl) ⟨1420244, by rfl⟩ : syracuseStep 1893659 = 2840489) B2840489
theorem B4040039 : Blo 1260448 4040039 := bstep (se 1 (by rfl) ⟨3030029, by rfl⟩ : syracuseStep 4040039 = 6060059) B6060059
theorem B7775785 : Blo 1260448 7775785 := bstep (se 2 (by rfl) ⟨2915919, by rfl⟩ : syracuseStep 7775785 = 5831839) B5831839
theorem B21555071 : Blo 1260448 21555071 := bstep (se 1 (by rfl) ⟨16166303, by rfl⟩ : syracuseStep 21555071 = 32332607) B32332607
theorem B31107887 : Blo 1260448 31107887 := bstep (se 1 (by rfl) ⟨23330915, by rfl⟩ : syracuseStep 31107887 = 46661831) B46661831
theorem B2837609 : Blo 1260448 2837609 := bstep (se 2 (by rfl) ⟨1064103, by rfl⟩ : syracuseStep 2837609 = 2128207) B2128207
theorem B7778015 : Blo 1260448 7778015 := bstep (se 1 (by rfl) ⟨5833511, by rfl⟩ : syracuseStep 7778015 = 11667023) B11667023
theorem B25899911 : Blo 1260448 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B2020583 : Blo 1260448 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B3593447 : Blo 1260448 3593447 := bstep (se 1 (by rfl) ⟨2695085, by rfl⟩ : syracuseStep 3593447 = 5390171) B5390171
theorem B2127775 : Blo 1260448 2127775 := bstep (se 1 (by rfl) ⟨1595831, by rfl⟩ : syracuseStep 2127775 = 3191663) B3191663
theorem B4258007 : Blo 1260448 4258007 := bstep (se 1 (by rfl) ⟨3193505, by rfl⟩ : syracuseStep 4258007 = 6387011) B6387011
theorem B74692961 : Blo 1260448 74692961 := bstep (se 2 (by rfl) ⟨28009860, by rfl⟩ : syracuseStep 74692961 = 56019721) B56019721
theorem B7183201 : Blo 1260448 7183201 := bstep (se 2 (by rfl) ⟨2693700, by rfl⟩ : syracuseStep 7183201 = 5387401) B5387401
theorem B1260543 : Blo 1260448 1260543 := bstep (se 1 (by rfl) ⟨945407, by rfl⟩ : syracuseStep 1260543 = 1890815) B1890815
theorem B5389487 : Blo 1260448 5389487 := bstep (se 1 (by rfl) ⟨4042115, by rfl⟩ : syracuseStep 5389487 = 8084231) B8084231
theorem B1891775 : Blo 1260448 1891775 := bstep (se 1 (by rfl) ⟨1418831, by rfl⟩ : syracuseStep 1891775 = 2837663) B2837663
theorem B1261083 : Blo 1260448 1261083 := bstep (se 1 (by rfl) ⟨945812, by rfl⟩ : syracuseStep 1261083 = 1891625) B1891625
theorem B30703175 : Blo 1260448 30703175 := bstep (se 1 (by rfl) ⟨23027381, by rfl⟩ : syracuseStep 30703175 = 46054763) B46054763
theorem B559742687 : Blo 1260448 559742687 := bstep (se 1 (by rfl) ⟨419807015, by rfl⟩ : syracuseStep 559742687 = 839614031) B839614031
theorem B27295865 : Blo 1260448 27295865 := bstep (se 2 (by rfl) ⟨10235949, by rfl⟩ : syracuseStep 27295865 = 20471899) B20471899
theorem B1261807 : Blo 1260448 1261807 := bstep (se 1 (by rfl) ⟨946355, by rfl⟩ : syracuseStep 1261807 = 1892711) B1892711
theorem B1261979 : Blo 1260448 1261979 := bstep (se 1 (by rfl) ⟨946484, by rfl⟩ : syracuseStep 1261979 = 1892969) B1892969
theorem B1262439 : Blo 1260448 1262439 := bstep (se 1 (by rfl) ⟨946829, by rfl⟩ : syracuseStep 1262439 = 1893659) B1893659
theorem B9577601 : Blo 1260448 9577601 := bstep (se 2 (by rfl) ⟨3591600, by rfl⟩ : syracuseStep 9577601 = 7183201) B7183201
theorem B14370047 : Blo 1260448 14370047 := bstep (se 1 (by rfl) ⟨10777535, by rfl⟩ : syracuseStep 14370047 = 21555071) B21555071
theorem B2837033 : Blo 1260448 2837033 := bstep (se 2 (by rfl) ⟨1063887, by rfl⟩ : syracuseStep 2837033 = 2127775) B2127775
theorem B2395631 : Blo 1260448 2395631 := bstep (se 1 (by rfl) ⟨1796723, by rfl⟩ : syracuseStep 2395631 = 3593447) B3593447
theorem B2838671 : Blo 1260448 2838671 := bstep (se 1 (by rfl) ⟨2129003, by rfl⟩ : syracuseStep 2838671 = 4258007) B4258007
theorem B49795307 : Blo 1260448 49795307 := bstep (se 1 (by rfl) ⟨37346480, by rfl⟩ : syracuseStep 49795307 = 74692961) B74692961
theorem B20738591 : Blo 1260448 20738591 := bstep (se 1 (by rfl) ⟨15553943, by rfl⟩ : syracuseStep 20738591 = 31107887) B31107887
theorem B10367713 : Blo 1260448 10367713 := bstep (se 2 (by rfl) ⟨3887892, by rfl⟩ : syracuseStep 10367713 = 7775785) B7775785
theorem B3592991 : Blo 1260448 3592991 := bstep (se 1 (by rfl) ⟨2694743, by rfl⟩ : syracuseStep 3592991 = 5389487) B5389487
theorem B20468783 : Blo 1260448 20468783 := bstep (se 1 (by rfl) ⟨15351587, by rfl⟩ : syracuseStep 20468783 = 30703175) B30703175
theorem B2692847 : Blo 1260448 2692847 := bstep (se 1 (by rfl) ⟨2019635, by rfl⟩ : syracuseStep 2692847 = 4039271) B4039271
theorem B17266607 : Blo 1260448 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B5388221 : Blo 1260448 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B2693359 : Blo 1260448 2693359 := bstep (se 1 (by rfl) ⟨2020019, by rfl⟩ : syracuseStep 2693359 = 4040039) B4040039
theorem B1891739 : Blo 1260448 1891739 := bstep (se 1 (by rfl) ⟨1418804, by rfl⟩ : syracuseStep 1891739 = 2837609) B2837609
theorem B1261183 : Blo 1260448 1261183 := bstep (se 1 (by rfl) ⟨945887, by rfl⟩ : syracuseStep 1261183 = 1891775) B1891775
theorem B373161791 : Blo 1260448 373161791 := bstep (se 1 (by rfl) ⟨279871343, by rfl⟩ : syracuseStep 373161791 = 559742687) B559742687
theorem B5185343 : Blo 1260448 5185343 := bstep (se 1 (by rfl) ⟨3889007, by rfl⟩ : syracuseStep 5185343 = 7778015) B7778015
theorem B1892447 : Blo 1260448 1892447 := bstep (se 1 (by rfl) ⟨1419335, by rfl⟩ : syracuseStep 1892447 = 2838671) B2838671
theorem B1795231 : Blo 1260448 1795231 := bstep (se 1 (by rfl) ⟨1346423, by rfl⟩ : syracuseStep 1795231 = 2692847) B2692847
theorem B11511071 : Blo 1260448 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B18197243 : Blo 1260448 18197243 := bstep (se 1 (by rfl) ⟨13647932, by rfl⟩ : syracuseStep 18197243 = 27295865) B27295865
theorem B33196871 : Blo 1260448 33196871 := bstep (se 1 (by rfl) ⟨24897653, by rfl⟩ : syracuseStep 33196871 = 49795307) B49795307
theorem B3591145 : Blo 1260448 3591145 := bstep (se 2 (by rfl) ⟨1346679, by rfl⟩ : syracuseStep 3591145 = 2693359) B2693359
theorem B2395327 : Blo 1260448 2395327 := bstep (se 1 (by rfl) ⟨1796495, by rfl⟩ : syracuseStep 2395327 = 3592991) B3592991
theorem B6385067 : Blo 1260448 6385067 := bstep (se 1 (by rfl) ⟨4788800, by rfl⟩ : syracuseStep 6385067 = 9577601) B9577601
theorem B9580031 : Blo 1260448 9580031 := bstep (se 1 (by rfl) ⟨7185023, by rfl⟩ : syracuseStep 9580031 = 14370047) B14370047
theorem B13823617 : Blo 1260448 13823617 := bstep (se 2 (by rfl) ⟨5183856, by rfl⟩ : syracuseStep 13823617 = 10367713) B10367713
theorem B13825727 : Blo 1260448 13825727 := bstep (se 1 (by rfl) ⟨10369295, by rfl⟩ : syracuseStep 13825727 = 20738591) B20738591
theorem B13645855 : Blo 1260448 13645855 := bstep (se 1 (by rfl) ⟨10234391, by rfl⟩ : syracuseStep 13645855 = 20468783) B20468783
theorem B1891355 : Blo 1260448 1891355 := bstep (se 1 (by rfl) ⟨1418516, by rfl⟩ : syracuseStep 1891355 = 2837033) B2837033
theorem B13827581 : Blo 1260448 13827581 := bstep (se 3 (by rfl) ⟨2592671, by rfl⟩ : syracuseStep 13827581 = 5185343) B5185343
theorem B1261159 : Blo 1260448 1261159 := bstep (se 1 (by rfl) ⟨945869, by rfl⟩ : syracuseStep 1261159 = 1891739) B1891739
theorem B1597087 : Blo 1260448 1597087 := bstep (se 1 (by rfl) ⟨1197815, by rfl⟩ : syracuseStep 1597087 = 2395631) B2395631
theorem B14368589 : Blo 1260448 14368589 := bstep (se 3 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 14368589 = 5388221) B5388221
theorem B248774527 : Blo 1260448 248774527 := bstep (se 1 (by rfl) ⟨186580895, by rfl⟩ : syracuseStep 248774527 = 373161791) B373161791
theorem B18194473 : Blo 1260448 18194473 := bstep (se 2 (by rfl) ⟨6822927, by rfl⟩ : syracuseStep 18194473 = 13645855) B13645855
theorem B1261631 : Blo 1260448 1261631 := bstep (se 1 (by rfl) ⟨946223, by rfl⟩ : syracuseStep 1261631 = 1892447) B1892447
theorem B9217151 : Blo 1260448 9217151 := bstep (se 1 (by rfl) ⟨6912863, by rfl⟩ : syracuseStep 9217151 = 13825727) B13825727
theorem B2393641 : Blo 1260448 2393641 := bstep (se 2 (by rfl) ⟨897615, by rfl⟩ : syracuseStep 2393641 = 1795231) B1795231
theorem B9218387 : Blo 1260448 9218387 := bstep (se 1 (by rfl) ⟨6913790, by rfl⟩ : syracuseStep 9218387 = 13827581) B13827581
theorem B9579059 : Blo 1260448 9579059 := bstep (se 1 (by rfl) ⟨7184294, by rfl⟩ : syracuseStep 9579059 = 14368589) B14368589
theorem B4788193 : Blo 1260448 4788193 := bstep (se 2 (by rfl) ⟨1795572, by rfl⟩ : syracuseStep 4788193 = 3591145) B3591145
theorem B22131247 : Blo 1260448 22131247 := bstep (se 1 (by rfl) ⟨16598435, by rfl⟩ : syracuseStep 22131247 = 33196871) B33196871
theorem B4256711 : Blo 1260448 4256711 := bstep (se 1 (by rfl) ⟨3192533, by rfl⟩ : syracuseStep 4256711 = 6385067) B6385067
theorem B6386687 : Blo 1260448 6386687 := bstep (se 1 (by rfl) ⟨4790015, by rfl⟩ : syracuseStep 6386687 = 9580031) B9580031
theorem B331699369 : Blo 1260448 331699369 := bstep (se 2 (by rfl) ⟨124387263, by rfl⟩ : syracuseStep 331699369 = 248774527) B248774527
theorem B7674047 : Blo 1260448 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B3193769 : Blo 1260448 3193769 := bstep (se 2 (by rfl) ⟨1197663, by rfl⟩ : syracuseStep 3193769 = 2395327) B2395327
theorem B12131495 : Blo 1260448 12131495 := bstep (se 1 (by rfl) ⟨9098621, by rfl⟩ : syracuseStep 12131495 = 18197243) B18197243
theorem B1260903 : Blo 1260448 1260903 := bstep (se 1 (by rfl) ⟨945677, by rfl⟩ : syracuseStep 1260903 = 1891355) B1891355
theorem B18431489 : Blo 1260448 18431489 := bstep (se 2 (by rfl) ⟨6911808, by rfl⟩ : syracuseStep 18431489 = 13823617) B13823617
theorem B2129449 : Blo 1260448 2129449 := bstep (se 2 (by rfl) ⟨798543, by rfl⟩ : syracuseStep 2129449 = 1597087) B1597087
theorem B29508329 : Blo 1260448 29508329 := bstep (se 2 (by rfl) ⟨11065623, by rfl⟩ : syracuseStep 29508329 = 22131247) B22131247
theorem B6144767 : Blo 1260448 6144767 := bstep (se 1 (by rfl) ⟨4608575, by rfl⟩ : syracuseStep 6144767 = 9217151) B9217151
theorem B6145591 : Blo 1260448 6145591 := bstep (se 1 (by rfl) ⟨4609193, by rfl⟩ : syracuseStep 6145591 = 9218387) B9218387
theorem B8087663 : Blo 1260448 8087663 := bstep (se 1 (by rfl) ⟨6065747, by rfl⟩ : syracuseStep 8087663 = 12131495) B12131495
theorem B6384257 : Blo 1260448 6384257 := bstep (se 2 (by rfl) ⟨2394096, by rfl⟩ : syracuseStep 6384257 = 4788193) B4788193
theorem B24259297 : Blo 1260448 24259297 := bstep (se 2 (by rfl) ⟨9097236, by rfl⟩ : syracuseStep 24259297 = 18194473) B18194473
theorem B2837807 : Blo 1260448 2837807 := bstep (se 1 (by rfl) ⟨2128355, by rfl⟩ : syracuseStep 2837807 = 4256711) B4256711
theorem B5116031 : Blo 1260448 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B442265825 : Blo 1260448 442265825 := bstep (se 2 (by rfl) ⟨165849684, by rfl⟩ : syracuseStep 442265825 = 331699369) B331699369
theorem B6386039 : Blo 1260448 6386039 := bstep (se 1 (by rfl) ⟨4789529, by rfl⟩ : syracuseStep 6386039 = 9579059) B9579059
theorem B3191521 : Blo 1260448 3191521 := bstep (se 2 (by rfl) ⟨1196820, by rfl⟩ : syracuseStep 3191521 = 2393641) B2393641
theorem B2839265 : Blo 1260448 2839265 := bstep (se 2 (by rfl) ⟨1064724, by rfl⟩ : syracuseStep 2839265 = 2129449) B2129449
theorem B4257791 : Blo 1260448 4257791 := bstep (se 1 (by rfl) ⟨3193343, by rfl⟩ : syracuseStep 4257791 = 6386687) B6386687
theorem B2129179 : Blo 1260448 2129179 := bstep (se 1 (by rfl) ⟨1596884, by rfl⟩ : syracuseStep 2129179 = 3193769) B3193769
theorem B12287659 : Blo 1260448 12287659 := bstep (se 1 (by rfl) ⟨9215744, by rfl⟩ : syracuseStep 12287659 = 18431489) B18431489
theorem B1892843 : Blo 1260448 1892843 := bstep (se 1 (by rfl) ⟨1419632, by rfl⟩ : syracuseStep 1892843 = 2839265) B2839265
theorem B4096511 : Blo 1260448 4096511 := bstep (se 1 (by rfl) ⟨3072383, by rfl⟩ : syracuseStep 4096511 = 6144767) B6144767
theorem B5391775 : Blo 1260448 5391775 := bstep (se 1 (by rfl) ⟨4043831, by rfl⟩ : syracuseStep 5391775 = 8087663) B8087663
theorem B8194121 : Blo 1260448 8194121 := bstep (se 2 (by rfl) ⟨3072795, by rfl⟩ : syracuseStep 8194121 = 6145591) B6145591
theorem B3410687 : Blo 1260448 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B19672219 : Blo 1260448 19672219 := bstep (se 1 (by rfl) ⟨14754164, by rfl⟩ : syracuseStep 19672219 = 29508329) B29508329
theorem B4255361 : Blo 1260448 4255361 := bstep (se 2 (by rfl) ⟨1595760, by rfl⟩ : syracuseStep 4255361 = 3191521) B3191521
theorem B32345729 : Blo 1260448 32345729 := bstep (se 2 (by rfl) ⟨12129648, by rfl⟩ : syracuseStep 32345729 = 24259297) B24259297
theorem B2838527 : Blo 1260448 2838527 := bstep (se 1 (by rfl) ⟨2128895, by rfl⟩ : syracuseStep 2838527 = 4257791) B4257791
theorem B2838905 : Blo 1260448 2838905 := bstep (se 2 (by rfl) ⟨1064589, by rfl⟩ : syracuseStep 2838905 = 2129179) B2129179
theorem B4256171 : Blo 1260448 4256171 := bstep (se 1 (by rfl) ⟨3192128, by rfl⟩ : syracuseStep 4256171 = 6384257) B6384257
theorem B294843883 : Blo 1260448 294843883 := bstep (se 1 (by rfl) ⟨221132912, by rfl⟩ : syracuseStep 294843883 = 442265825) B442265825
theorem B4257359 : Blo 1260448 4257359 := bstep (se 1 (by rfl) ⟨3193019, by rfl⟩ : syracuseStep 4257359 = 6386039) B6386039
theorem B1891871 : Blo 1260448 1891871 := bstep (se 1 (by rfl) ⟨1418903, by rfl⟩ : syracuseStep 1891871 = 2837807) B2837807
theorem B16383545 : Blo 1260448 16383545 := bstep (se 2 (by rfl) ⟨6143829, by rfl⟩ : syracuseStep 16383545 = 12287659) B12287659
theorem B1892603 : Blo 1260448 1892603 := bstep (se 1 (by rfl) ⟨1419452, by rfl⟩ : syracuseStep 1892603 = 2838905) B2838905
theorem B1261895 : Blo 1260448 1261895 := bstep (se 1 (by rfl) ⟨946421, by rfl⟩ : syracuseStep 1261895 = 1892843) B1892843
theorem B1892351 : Blo 1260448 1892351 := bstep (se 1 (by rfl) ⟨1419263, by rfl⟩ : syracuseStep 1892351 = 2838527) B2838527
theorem B9095165 : Blo 1260448 9095165 := bstep (se 3 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 9095165 = 3410687) B3410687
theorem B10922363 : Blo 1260448 10922363 := bstep (se 1 (by rfl) ⟨8191772, by rfl⟩ : syracuseStep 10922363 = 16383545) B16383545
theorem B2836907 : Blo 1260448 2836907 := bstep (se 1 (by rfl) ⟨2127680, by rfl⟩ : syracuseStep 2836907 = 4255361) B4255361
theorem B21563819 : Blo 1260448 21563819 := bstep (se 1 (by rfl) ⟨16172864, by rfl⟩ : syracuseStep 21563819 = 32345729) B32345729
theorem B2837447 : Blo 1260448 2837447 := bstep (se 1 (by rfl) ⟨2128085, by rfl⟩ : syracuseStep 2837447 = 4256171) B4256171
theorem B2731007 : Blo 1260448 2731007 := bstep (se 1 (by rfl) ⟨2048255, by rfl⟩ : syracuseStep 2731007 = 4096511) B4096511
theorem B104918501 : Blo 1260448 104918501 := bstep (se 4 (by rfl) ⟨9836109, by rfl⟩ : syracuseStep 104918501 = 19672219) B19672219
theorem B2838239 : Blo 1260448 2838239 := bstep (se 1 (by rfl) ⟨2128679, by rfl⟩ : syracuseStep 2838239 = 4257359) B4257359
theorem B7189033 : Blo 1260448 7189033 := bstep (se 2 (by rfl) ⟨2695887, by rfl⟩ : syracuseStep 7189033 = 5391775) B5391775
theorem B5462747 : Blo 1260448 5462747 := bstep (se 1 (by rfl) ⟨4097060, by rfl⟩ : syracuseStep 5462747 = 8194121) B8194121
theorem B393125177 : Blo 1260448 393125177 := bstep (se 2 (by rfl) ⟨147421941, by rfl⟩ : syracuseStep 393125177 = 294843883) B294843883
theorem B1261247 : Blo 1260448 1261247 := bstep (se 1 (by rfl) ⟨945935, by rfl⟩ : syracuseStep 1261247 = 1891871) B1891871
theorem B1261735 : Blo 1260448 1261735 := bstep (se 1 (by rfl) ⟨946301, by rfl⟩ : syracuseStep 1261735 = 1892603) B1892603
theorem B9585377 : Blo 1260448 9585377 := bstep (se 2 (by rfl) ⟨3594516, by rfl⟩ : syracuseStep 9585377 = 7189033) B7189033
theorem B279782669 : Blo 1260448 279782669 := bstep (se 3 (by rfl) ⟨52459250, by rfl⟩ : syracuseStep 279782669 = 104918501) B104918501
theorem B6063443 : Blo 1260448 6063443 := bstep (se 1 (by rfl) ⟨4547582, by rfl⟩ : syracuseStep 6063443 = 9095165) B9095165
theorem B3641831 : Blo 1260448 3641831 := bstep (se 1 (by rfl) ⟨2731373, by rfl⟩ : syracuseStep 3641831 = 5462747) B5462747
theorem B262083451 : Blo 1260448 262083451 := bstep (se 1 (by rfl) ⟨196562588, by rfl⟩ : syracuseStep 262083451 = 393125177) B393125177
theorem B1261567 : Blo 1260448 1261567 := bstep (se 1 (by rfl) ⟨946175, by rfl⟩ : syracuseStep 1261567 = 1892351) B1892351
theorem B7281575 : Blo 1260448 7281575 := bstep (se 1 (by rfl) ⟨5461181, by rfl⟩ : syracuseStep 7281575 = 10922363) B10922363
theorem B1891271 : Blo 1260448 1891271 := bstep (se 1 (by rfl) ⟨1418453, by rfl⟩ : syracuseStep 1891271 = 2836907) B2836907
theorem B14375879 : Blo 1260448 14375879 := bstep (se 1 (by rfl) ⟨10781909, by rfl⟩ : syracuseStep 14375879 = 21563819) B21563819
theorem B1891631 : Blo 1260448 1891631 := bstep (se 1 (by rfl) ⟨1418723, by rfl⟩ : syracuseStep 1891631 = 2837447) B2837447
theorem B1892159 : Blo 1260448 1892159 := bstep (se 1 (by rfl) ⟨1419119, by rfl⟩ : syracuseStep 1892159 = 2838239) B2838239
theorem B7282685 : Blo 1260448 7282685 := bstep (se 3 (by rfl) ⟨1365503, by rfl⟩ : syracuseStep 7282685 = 2731007) B2731007
theorem B6390251 : Blo 1260448 6390251 := bstep (se 1 (by rfl) ⟨4792688, by rfl⟩ : syracuseStep 6390251 = 9585377) B9585377
theorem B2427887 : Blo 1260448 2427887 := bstep (se 1 (by rfl) ⟨1820915, by rfl⟩ : syracuseStep 2427887 = 3641831) B3641831
theorem B4042295 : Blo 1260448 4042295 := bstep (se 1 (by rfl) ⟨3031721, by rfl⟩ : syracuseStep 4042295 = 6063443) B6063443
theorem B4854383 : Blo 1260448 4854383 := bstep (se 1 (by rfl) ⟨3640787, by rfl⟩ : syracuseStep 4854383 = 7281575) B7281575
theorem B4855123 : Blo 1260448 4855123 := bstep (se 1 (by rfl) ⟨3641342, by rfl⟩ : syracuseStep 4855123 = 7282685) B7282685
theorem B186521779 : Blo 1260448 186521779 := bstep (se 1 (by rfl) ⟨139891334, by rfl⟩ : syracuseStep 186521779 = 279782669) B279782669
theorem B349444601 : Blo 1260448 349444601 := bstep (se 2 (by rfl) ⟨131041725, by rfl⟩ : syracuseStep 349444601 = 262083451) B262083451
theorem B1260847 : Blo 1260448 1260847 := bstep (se 1 (by rfl) ⟨945635, by rfl⟩ : syracuseStep 1260847 = 1891271) B1891271
theorem B9583919 : Blo 1260448 9583919 := bstep (se 1 (by rfl) ⟨7187939, by rfl⟩ : syracuseStep 9583919 = 14375879) B14375879
theorem B1261087 : Blo 1260448 1261087 := bstep (se 1 (by rfl) ⟨945815, by rfl⟩ : syracuseStep 1261087 = 1891631) B1891631
theorem B1261439 : Blo 1260448 1261439 := bstep (se 1 (by rfl) ⟨946079, by rfl⟩ : syracuseStep 1261439 = 1892159) B1892159
theorem B4260167 : Blo 1260448 4260167 := bstep (se 1 (by rfl) ⟨3195125, by rfl⟩ : syracuseStep 4260167 = 6390251) B6390251
theorem B3236255 : Blo 1260448 3236255 := bstep (se 1 (by rfl) ⟨2427191, by rfl⟩ : syracuseStep 3236255 = 4854383) B4854383
theorem B248695705 : Blo 1260448 248695705 := bstep (se 2 (by rfl) ⟨93260889, by rfl⟩ : syracuseStep 248695705 = 186521779) B186521779
theorem B1618591 : Blo 1260448 1618591 := bstep (se 1 (by rfl) ⟨1213943, by rfl⟩ : syracuseStep 1618591 = 2427887) B2427887
theorem B232963067 : Blo 1260448 232963067 := bstep (se 1 (by rfl) ⟨174722300, by rfl⟩ : syracuseStep 232963067 = 349444601) B349444601
theorem B25893989 : Blo 1260448 25893989 := bstep (se 4 (by rfl) ⟨2427561, by rfl⟩ : syracuseStep 25893989 = 4855123) B4855123
theorem B6389279 : Blo 1260448 6389279 := bstep (se 1 (by rfl) ⟨4791959, by rfl⟩ : syracuseStep 6389279 = 9583919) B9583919
theorem B2694863 : Blo 1260448 2694863 := bstep (se 1 (by rfl) ⟨2021147, by rfl⟩ : syracuseStep 2694863 = 4042295) B4042295
theorem B17262659 : Blo 1260448 17262659 := bstep (se 1 (by rfl) ⟨12946994, by rfl⟩ : syracuseStep 17262659 = 25893989) B25893989
theorem B1796575 : Blo 1260448 1796575 := bstep (se 1 (by rfl) ⟨1347431, by rfl⟩ : syracuseStep 1796575 = 2694863) B2694863
theorem B2158121 : Blo 1260448 2158121 := bstep (se 2 (by rfl) ⟨809295, by rfl⟩ : syracuseStep 2158121 = 1618591) B1618591
theorem B155308711 : Blo 1260448 155308711 := bstep (se 1 (by rfl) ⟨116481533, by rfl⟩ : syracuseStep 155308711 = 232963067) B232963067
theorem B2840111 : Blo 1260448 2840111 := bstep (se 1 (by rfl) ⟨2130083, by rfl⟩ : syracuseStep 2840111 = 4260167) B4260167
theorem B331594273 : Blo 1260448 331594273 := bstep (se 2 (by rfl) ⟨124347852, by rfl⟩ : syracuseStep 331594273 = 248695705) B248695705
theorem B34520053 : Blo 1260448 34520053 := bstep (se 5 (by rfl) ⟨1618127, by rfl⟩ : syracuseStep 34520053 = 3236255) B3236255
theorem B4259519 : Blo 1260448 4259519 := bstep (se 1 (by rfl) ⟨3194639, by rfl⟩ : syracuseStep 4259519 = 6389279) B6389279
theorem B207078281 : Blo 1260448 207078281 := bstep (se 2 (by rfl) ⟨77654355, by rfl⟩ : syracuseStep 207078281 = 155308711) B155308711
theorem B1893407 : Blo 1260448 1893407 := bstep (se 1 (by rfl) ⟨1420055, by rfl⟩ : syracuseStep 1893407 = 2840111) B2840111
theorem B2395433 : Blo 1260448 2395433 := bstep (se 2 (by rfl) ⟨898287, by rfl⟩ : syracuseStep 2395433 = 1796575) B1796575
theorem B442125697 : Blo 1260448 442125697 := bstep (se 2 (by rfl) ⟨165797136, by rfl⟩ : syracuseStep 442125697 = 331594273) B331594273
theorem B46026737 : Blo 1260448 46026737 := bstep (se 2 (by rfl) ⟨17260026, by rfl⟩ : syracuseStep 46026737 = 34520053) B34520053
theorem B5754989 : Blo 1260448 5754989 := bstep (se 3 (by rfl) ⟨1079060, by rfl⟩ : syracuseStep 5754989 = 2158121) B2158121
theorem B2839679 : Blo 1260448 2839679 := bstep (se 1 (by rfl) ⟨2129759, by rfl⟩ : syracuseStep 2839679 = 4259519) B4259519
theorem B11508439 : Blo 1260448 11508439 := bstep (se 1 (by rfl) ⟨8631329, by rfl⟩ : syracuseStep 11508439 = 17262659) B17262659
theorem B138052187 : Blo 1260448 138052187 := bstep (se 1 (by rfl) ⟨103539140, by rfl⟩ : syracuseStep 138052187 = 207078281) B207078281
theorem B1262271 : Blo 1260448 1262271 := bstep (se 1 (by rfl) ⟨946703, by rfl⟩ : syracuseStep 1262271 = 1893407) B1893407
theorem B1893119 : Blo 1260448 1893119 := bstep (se 1 (by rfl) ⟨1419839, by rfl⟩ : syracuseStep 1893119 = 2839679) B2839679
theorem B15344585 : Blo 1260448 15344585 := bstep (se 2 (by rfl) ⟨5754219, by rfl⟩ : syracuseStep 15344585 = 11508439) B11508439
theorem B3836659 : Blo 1260448 3836659 := bstep (se 1 (by rfl) ⟨2877494, by rfl⟩ : syracuseStep 3836659 = 5754989) B5754989
theorem B589500929 : Blo 1260448 589500929 := bstep (se 2 (by rfl) ⟨221062848, by rfl⟩ : syracuseStep 589500929 = 442125697) B442125697
theorem B30684491 : Blo 1260448 30684491 := bstep (se 1 (by rfl) ⟨23013368, by rfl⟩ : syracuseStep 30684491 = 46026737) B46026737
theorem B6387821 : Blo 1260448 6387821 := bstep (se 3 (by rfl) ⟨1197716, by rfl⟩ : syracuseStep 6387821 = 2395433) B2395433
theorem B1262079 : Blo 1260448 1262079 := bstep (se 1 (by rfl) ⟨946559, by rfl⟩ : syracuseStep 1262079 = 1893119) B1893119
theorem B20456327 : Blo 1260448 20456327 := bstep (se 1 (by rfl) ⟨15342245, by rfl⟩ : syracuseStep 20456327 = 30684491) B30684491
theorem B5115545 : Blo 1260448 5115545 := bstep (se 2 (by rfl) ⟨1918329, by rfl⟩ : syracuseStep 5115545 = 3836659) B3836659
theorem B393000619 : Blo 1260448 393000619 := bstep (se 1 (by rfl) ⟨294750464, by rfl⟩ : syracuseStep 393000619 = 589500929) B589500929
theorem B92034791 : Blo 1260448 92034791 := bstep (se 1 (by rfl) ⟨69026093, by rfl⟩ : syracuseStep 92034791 = 138052187) B138052187
theorem B10229723 : Blo 1260448 10229723 := bstep (se 1 (by rfl) ⟨7672292, by rfl⟩ : syracuseStep 10229723 = 15344585) B15344585
theorem B4258547 : Blo 1260448 4258547 := bstep (se 1 (by rfl) ⟨3193910, by rfl⟩ : syracuseStep 4258547 = 6387821) B6387821
theorem B3410363 : Blo 1260448 3410363 := bstep (se 1 (by rfl) ⟨2557772, by rfl⟩ : syracuseStep 3410363 = 5115545) B5115545
theorem B6819815 : Blo 1260448 6819815 := bstep (se 1 (by rfl) ⟨5114861, by rfl⟩ : syracuseStep 6819815 = 10229723) B10229723
theorem B2839031 : Blo 1260448 2839031 := bstep (se 1 (by rfl) ⟨2129273, by rfl⟩ : syracuseStep 2839031 = 4258547) B4258547
theorem B61356527 : Blo 1260448 61356527 := bstep (se 1 (by rfl) ⟨46017395, by rfl⟩ : syracuseStep 61356527 = 92034791) B92034791
theorem B524000825 : Blo 1260448 524000825 := bstep (se 2 (by rfl) ⟨196500309, by rfl⟩ : syracuseStep 524000825 = 393000619) B393000619
theorem B54550205 : Blo 1260448 54550205 := bstep (se 3 (by rfl) ⟨10228163, by rfl⟩ : syracuseStep 54550205 = 20456327) B20456327
theorem B1892687 : Blo 1260448 1892687 := bstep (se 1 (by rfl) ⟨1419515, by rfl⟩ : syracuseStep 1892687 = 2839031) B2839031
theorem B40904351 : Blo 1260448 40904351 := bstep (se 1 (by rfl) ⟨30678263, by rfl⟩ : syracuseStep 40904351 = 61356527) B61356527
theorem B349333883 : Blo 1260448 349333883 := bstep (se 1 (by rfl) ⟨262000412, by rfl⟩ : syracuseStep 349333883 = 524000825) B524000825
theorem B36366803 : Blo 1260448 36366803 := bstep (se 1 (by rfl) ⟨27275102, by rfl⟩ : syracuseStep 36366803 = 54550205) B54550205
theorem B2273575 : Blo 1260448 2273575 := bstep (se 1 (by rfl) ⟨1705181, by rfl⟩ : syracuseStep 2273575 = 3410363) B3410363
theorem B4546543 : Blo 1260448 4546543 := bstep (se 1 (by rfl) ⟨3409907, by rfl⟩ : syracuseStep 4546543 = 6819815) B6819815
theorem B1261791 : Blo 1260448 1261791 := bstep (se 1 (by rfl) ⟨946343, by rfl⟩ : syracuseStep 1261791 = 1892687) B1892687
theorem B3031433 : Blo 1260448 3031433 := bstep (se 2 (by rfl) ⟨1136787, by rfl⟩ : syracuseStep 3031433 = 2273575) B2273575
theorem B24244535 : Blo 1260448 24244535 := bstep (se 1 (by rfl) ⟨18183401, by rfl⟩ : syracuseStep 24244535 = 36366803) B36366803
theorem B27269567 : Blo 1260448 27269567 := bstep (se 1 (by rfl) ⟨20452175, by rfl⟩ : syracuseStep 27269567 = 40904351) B40904351
theorem B232889255 : Blo 1260448 232889255 := bstep (se 1 (by rfl) ⟨174666941, by rfl⟩ : syracuseStep 232889255 = 349333883) B349333883
theorem B6062057 : Blo 1260448 6062057 := bstep (se 2 (by rfl) ⟨2273271, by rfl⟩ : syracuseStep 6062057 = 4546543) B4546543
theorem B16163023 : Blo 1260448 16163023 := bstep (se 1 (by rfl) ⟨12122267, by rfl⟩ : syracuseStep 16163023 = 24244535) B24244535
theorem B18179711 : Blo 1260448 18179711 := bstep (se 1 (by rfl) ⟨13634783, by rfl⟩ : syracuseStep 18179711 = 27269567) B27269567
theorem B4041371 : Blo 1260448 4041371 := bstep (se 1 (by rfl) ⟨3031028, by rfl⟩ : syracuseStep 4041371 = 6062057) B6062057
theorem B155259503 : Blo 1260448 155259503 := bstep (se 1 (by rfl) ⟨116444627, by rfl⟩ : syracuseStep 155259503 = 232889255) B232889255
theorem B2020955 : Blo 1260448 2020955 := bstep (se 1 (by rfl) ⟨1515716, by rfl⟩ : syracuseStep 2020955 = 3031433) B3031433
theorem B103506335 : Blo 1260448 103506335 := bstep (se 1 (by rfl) ⟨77629751, by rfl⟩ : syracuseStep 103506335 = 155259503) B155259503
theorem B12119807 : Blo 1260448 12119807 := bstep (se 1 (by rfl) ⟨9089855, by rfl⟩ : syracuseStep 12119807 = 18179711) B18179711
theorem B10776989 : Blo 1260448 10776989 := bstep (se 3 (by rfl) ⟨2020685, by rfl⟩ : syracuseStep 10776989 = 4041371) B4041371
theorem B21550697 : Blo 1260448 21550697 := bstep (se 2 (by rfl) ⟨8081511, by rfl⟩ : syracuseStep 21550697 = 16163023) B16163023
theorem B5389213 : Blo 1260448 5389213 := bstep (se 3 (by rfl) ⟨1010477, by rfl⟩ : syracuseStep 5389213 = 2020955) B2020955
theorem B7184659 : Blo 1260448 7184659 := bstep (se 1 (by rfl) ⟨5388494, by rfl⟩ : syracuseStep 7184659 = 10776989) B10776989
theorem B7185617 : Blo 1260448 7185617 := bstep (se 2 (by rfl) ⟨2694606, by rfl⟩ : syracuseStep 7185617 = 5389213) B5389213
theorem B32319485 : Blo 1260448 32319485 := bstep (se 3 (by rfl) ⟨6059903, by rfl⟩ : syracuseStep 32319485 = 12119807) B12119807
theorem B69004223 : Blo 1260448 69004223 := bstep (se 1 (by rfl) ⟨51753167, by rfl⟩ : syracuseStep 69004223 = 103506335) B103506335
theorem B14367131 : Blo 1260448 14367131 := bstep (se 1 (by rfl) ⟨10775348, by rfl⟩ : syracuseStep 14367131 = 21550697) B21550697
theorem B21546323 : Blo 1260448 21546323 := bstep (se 1 (by rfl) ⟨16159742, by rfl⟩ : syracuseStep 21546323 = 32319485) B32319485
theorem B9578087 : Blo 1260448 9578087 := bstep (se 1 (by rfl) ⟨7183565, by rfl⟩ : syracuseStep 9578087 = 14367131) B14367131
theorem B9579545 : Blo 1260448 9579545 := bstep (se 2 (by rfl) ⟨3592329, by rfl⟩ : syracuseStep 9579545 = 7184659) B7184659
theorem B46002815 : Blo 1260448 46002815 := bstep (se 1 (by rfl) ⟨34502111, by rfl⟩ : syracuseStep 46002815 = 69004223) B69004223
theorem B4790411 : Blo 1260448 4790411 := bstep (se 1 (by rfl) ⟨3592808, by rfl⟩ : syracuseStep 4790411 = 7185617) B7185617
theorem B14364215 : Blo 1260448 14364215 := bstep (se 1 (by rfl) ⟨10773161, by rfl⟩ : syracuseStep 14364215 = 21546323) B21546323
theorem B6385391 : Blo 1260448 6385391 := bstep (se 1 (by rfl) ⟨4789043, by rfl⟩ : syracuseStep 6385391 = 9578087) B9578087
theorem B6386363 : Blo 1260448 6386363 := bstep (se 1 (by rfl) ⟨4789772, by rfl⟩ : syracuseStep 6386363 = 9579545) B9579545
theorem B30668543 : Blo 1260448 30668543 := bstep (se 1 (by rfl) ⟨23001407, by rfl⟩ : syracuseStep 30668543 = 46002815) B46002815
theorem B3193607 : Blo 1260448 3193607 := bstep (se 1 (by rfl) ⟨2395205, by rfl⟩ : syracuseStep 3193607 = 4790411) B4790411
theorem B4256927 : Blo 1260448 4256927 := bstep (se 1 (by rfl) ⟨3192695, by rfl⟩ : syracuseStep 4256927 = 6385391) B6385391
theorem B4257575 : Blo 1260448 4257575 := bstep (se 1 (by rfl) ⟨3193181, by rfl⟩ : syracuseStep 4257575 = 6386363) B6386363
theorem B20445695 : Blo 1260448 20445695 := bstep (se 1 (by rfl) ⟨15334271, by rfl⟩ : syracuseStep 20445695 = 30668543) B30668543
theorem B2129071 : Blo 1260448 2129071 := bstep (se 1 (by rfl) ⟨1596803, by rfl⟩ : syracuseStep 2129071 = 3193607) B3193607
theorem B9576143 : Blo 1260448 9576143 := bstep (se 1 (by rfl) ⟨7182107, by rfl⟩ : syracuseStep 9576143 = 14364215) B14364215
theorem B6384095 : Blo 1260448 6384095 := bstep (se 1 (by rfl) ⟨4788071, by rfl⟩ : syracuseStep 6384095 = 9576143) B9576143
theorem B2837951 : Blo 1260448 2837951 := bstep (se 1 (by rfl) ⟨2128463, by rfl⟩ : syracuseStep 2837951 = 4256927) B4256927
theorem B2838383 : Blo 1260448 2838383 := bstep (se 1 (by rfl) ⟨2128787, by rfl⟩ : syracuseStep 2838383 = 4257575) B4257575
theorem B2838761 : Blo 1260448 2838761 := bstep (se 2 (by rfl) ⟨1064535, by rfl⟩ : syracuseStep 2838761 = 2129071) B2129071
theorem B13630463 : Blo 1260448 13630463 := bstep (se 1 (by rfl) ⟨10222847, by rfl⟩ : syracuseStep 13630463 = 20445695) B20445695
theorem B1892507 : Blo 1260448 1892507 := bstep (se 1 (by rfl) ⟨1419380, by rfl⟩ : syracuseStep 1892507 = 2838761) B2838761
theorem B9086975 : Blo 1260448 9086975 := bstep (se 1 (by rfl) ⟨6815231, by rfl⟩ : syracuseStep 9086975 = 13630463) B13630463
theorem B4256063 : Blo 1260448 4256063 := bstep (se 1 (by rfl) ⟨3192047, by rfl⟩ : syracuseStep 4256063 = 6384095) B6384095
theorem B1891967 : Blo 1260448 1891967 := bstep (se 1 (by rfl) ⟨1418975, by rfl⟩ : syracuseStep 1891967 = 2837951) B2837951
theorem B1892255 : Blo 1260448 1892255 := bstep (se 1 (by rfl) ⟨1419191, by rfl⟩ : syracuseStep 1892255 = 2838383) B2838383
theorem B1261671 : Blo 1260448 1261671 := bstep (se 1 (by rfl) ⟨946253, by rfl⟩ : syracuseStep 1261671 = 1892507) B1892507
theorem B2837375 : Blo 1260448 2837375 := bstep (se 1 (by rfl) ⟨2128031, by rfl⟩ : syracuseStep 2837375 = 4256063) B4256063
theorem B6057983 : Blo 1260448 6057983 := bstep (se 1 (by rfl) ⟨4543487, by rfl⟩ : syracuseStep 6057983 = 9086975) B9086975
theorem B1261311 : Blo 1260448 1261311 := bstep (se 1 (by rfl) ⟨945983, by rfl⟩ : syracuseStep 1261311 = 1891967) B1891967
theorem B1261503 : Blo 1260448 1261503 := bstep (se 1 (by rfl) ⟨946127, by rfl⟩ : syracuseStep 1261503 = 1892255) B1892255
theorem B1891583 : Blo 1260448 1891583 := bstep (se 1 (by rfl) ⟨1418687, by rfl⟩ : syracuseStep 1891583 = 2837375) B2837375
theorem B4038655 : Blo 1260448 4038655 := bstep (se 1 (by rfl) ⟨3028991, by rfl⟩ : syracuseStep 4038655 = 6057983) B6057983
theorem B5384873 : Blo 1260448 5384873 := bstep (se 2 (by rfl) ⟨2019327, by rfl⟩ : syracuseStep 5384873 = 4038655) B4038655
theorem B1261055 : Blo 1260448 1261055 := bstep (se 1 (by rfl) ⟨945791, by rfl⟩ : syracuseStep 1261055 = 1891583) B1891583
theorem B3589915 : Blo 1260448 3589915 := bstep (se 1 (by rfl) ⟨2692436, by rfl⟩ : syracuseStep 3589915 = 5384873) B5384873
theorem B4786553 : Blo 1260448 4786553 := bstep (se 2 (by rfl) ⟨1794957, by rfl⟩ : syracuseStep 4786553 = 3589915) B3589915
theorem B3191035 : Blo 1260448 3191035 := bstep (se 1 (by rfl) ⟨2393276, by rfl⟩ : syracuseStep 3191035 = 4786553) B4786553
theorem B4254713 : Blo 1260448 4254713 := bstep (se 2 (by rfl) ⟨1595517, by rfl⟩ : syracuseStep 4254713 = 3191035) B3191035
theorem B2836475 : Blo 1260448 2836475 := bstep (se 1 (by rfl) ⟨2127356, by rfl⟩ : syracuseStep 2836475 = 4254713) B4254713
theorem B1890983 : Blo 1260448 1890983 := bstep (se 1 (by rfl) ⟨1418237, by rfl⟩ : syracuseStep 1890983 = 2836475) B2836475
theorem B1260655 : Blo 1260448 1260655 := bstep (se 1 (by rfl) ⟨945491, by rfl⟩ : syracuseStep 1260655 = 1890983) B1890983

theorem C0 (j : ℕ) (h1 : 315112 ≤ j) (h2 : j ≤ 315611) : Blo 1260448 (4 * j + 3) := by
  interval_cases j
  · exact B1260451
  · exact B1260455
  · exact B1260459
  · exact B1260463
  · exact B1260467
  · exact B1260471
  · exact B1260475
  · exact B1260479
  · exact B1260483
  · exact B1260487
  · exact B1260491
  · exact B1260495
  · exact B1260499
  · exact B1260503
  · exact B1260507
  · exact B1260511
  · exact B1260515
  · exact B1260519
  · exact B1260523
  · exact B1260527
  · exact B1260531
  · exact B1260535
  · exact B1260539
  · exact B1260543
  · exact B1260547
  · exact B1260551
  · exact B1260555
  · exact B1260559
  · exact B1260563
  · exact B1260567
  · exact B1260571
  · exact B1260575
  · exact B1260579
  · exact B1260583
  · exact B1260587
  · exact B1260591
  · exact B1260595
  · exact B1260599
  · exact B1260603
  · exact B1260607
  · exact B1260611
  · exact B1260615
  · exact B1260619
  · exact B1260623
  · exact B1260627
  · exact B1260631
  · exact B1260635
  · exact B1260639
  · exact B1260643
  · exact B1260647
  · exact B1260651
  · exact B1260655
  · exact B1260659
  · exact B1260663
  · exact B1260667
  · exact B1260671
  · exact B1260675
  · exact B1260679
  · exact B1260683
  · exact B1260687
  · exact B1260691
  · exact B1260695
  · exact B1260699
  · exact B1260703
  · exact B1260707
  · exact B1260711
  · exact B1260715
  · exact B1260719
  · exact B1260723
  · exact B1260727
  · exact B1260731
  · exact B1260735
  · exact B1260739
  · exact B1260743
  · exact B1260747
  · exact B1260751
  · exact B1260755
  · exact B1260759
  · exact B1260763
  · exact B1260767
  · exact B1260771
  · exact B1260775
  · exact B1260779
  · exact B1260783
  · exact B1260787
  · exact B1260791
  · exact B1260795
  · exact B1260799
  · exact B1260803
  · exact B1260807
  · exact B1260811
  · exact B1260815
  · exact B1260819
  · exact B1260823
  · exact B1260827
  · exact B1260831
  · exact B1260835
  · exact B1260839
  · exact B1260843
  · exact B1260847
  · exact B1260851
  · exact B1260855
  · exact B1260859
  · exact B1260863
  · exact B1260867
  · exact B1260871
  · exact B1260875
  · exact B1260879
  · exact B1260883
  · exact B1260887
  · exact B1260891
  · exact B1260895
  · exact B1260899
  · exact B1260903
  · exact B1260907
  · exact B1260911
  · exact B1260915
  · exact B1260919
  · exact B1260923
  · exact B1260927
  · exact B1260931
  · exact B1260935
  · exact B1260939
  · exact B1260943
  · exact B1260947
  · exact B1260951
  · exact B1260955
  · exact B1260959
  · exact B1260963
  · exact B1260967
  · exact B1260971
  · exact B1260975
  · exact B1260979
  · exact B1260983
  · exact B1260987
  · exact B1260991
  · exact B1260995
  · exact B1260999
  · exact B1261003
  · exact B1261007
  · exact B1261011
  · exact B1261015
  · exact B1261019
  · exact B1261023
  · exact B1261027
  · exact B1261031
  · exact B1261035
  · exact B1261039
  · exact B1261043
  · exact B1261047
  · exact B1261051
  · exact B1261055
  · exact B1261059
  · exact B1261063
  · exact B1261067
  · exact B1261071
  · exact B1261075
  · exact B1261079
  · exact B1261083
  · exact B1261087
  · exact B1261091
  · exact B1261095
  · exact B1261099
  · exact B1261103
  · exact B1261107
  · exact B1261111
  · exact B1261115
  · exact B1261119
  · exact B1261123
  · exact B1261127
  · exact B1261131
  · exact B1261135
  · exact B1261139
  · exact B1261143
  · exact B1261147
  · exact B1261151
  · exact B1261155
  · exact B1261159
  · exact B1261163
  · exact B1261167
  · exact B1261171
  · exact B1261175
  · exact B1261179
  · exact B1261183
  · exact B1261187
  · exact B1261191
  · exact B1261195
  · exact B1261199
  · exact B1261203
  · exact B1261207
  · exact B1261211
  · exact B1261215
  · exact B1261219
  · exact B1261223
  · exact B1261227
  · exact B1261231
  · exact B1261235
  · exact B1261239
  · exact B1261243
  · exact B1261247
  · exact B1261251
  · exact B1261255
  · exact B1261259
  · exact B1261263
  · exact B1261267
  · exact B1261271
  · exact B1261275
  · exact B1261279
  · exact B1261283
  · exact B1261287
  · exact B1261291
  · exact B1261295
  · exact B1261299
  · exact B1261303
  · exact B1261307
  · exact B1261311
  · exact B1261315
  · exact B1261319
  · exact B1261323
  · exact B1261327
  · exact B1261331
  · exact B1261335
  · exact B1261339
  · exact B1261343
  · exact B1261347
  · exact B1261351
  · exact B1261355
  · exact B1261359
  · exact B1261363
  · exact B1261367
  · exact B1261371
  · exact B1261375
  · exact B1261379
  · exact B1261383
  · exact B1261387
  · exact B1261391
  · exact B1261395
  · exact B1261399
  · exact B1261403
  · exact B1261407
  · exact B1261411
  · exact B1261415
  · exact B1261419
  · exact B1261423
  · exact B1261427
  · exact B1261431
  · exact B1261435
  · exact B1261439
  · exact B1261443
  · exact B1261447
  · exact B1261451
  · exact B1261455
  · exact B1261459
  · exact B1261463
  · exact B1261467
  · exact B1261471
  · exact B1261475
  · exact B1261479
  · exact B1261483
  · exact B1261487
  · exact B1261491
  · exact B1261495
  · exact B1261499
  · exact B1261503
  · exact B1261507
  · exact B1261511
  · exact B1261515
  · exact B1261519
  · exact B1261523
  · exact B1261527
  · exact B1261531
  · exact B1261535
  · exact B1261539
  · exact B1261543
  · exact B1261547
  · exact B1261551
  · exact B1261555
  · exact B1261559
  · exact B1261563
  · exact B1261567
  · exact B1261571
  · exact B1261575
  · exact B1261579
  · exact B1261583
  · exact B1261587
  · exact B1261591
  · exact B1261595
  · exact B1261599
  · exact B1261603
  · exact B1261607
  · exact B1261611
  · exact B1261615
  · exact B1261619
  · exact B1261623
  · exact B1261627
  · exact B1261631
  · exact B1261635
  · exact B1261639
  · exact B1261643
  · exact B1261647
  · exact B1261651
  · exact B1261655
  · exact B1261659
  · exact B1261663
  · exact B1261667
  · exact B1261671
  · exact B1261675
  · exact B1261679
  · exact B1261683
  · exact B1261687
  · exact B1261691
  · exact B1261695
  · exact B1261699
  · exact B1261703
  · exact B1261707
  · exact B1261711
  · exact B1261715
  · exact B1261719
  · exact B1261723
  · exact B1261727
  · exact B1261731
  · exact B1261735
  · exact B1261739
  · exact B1261743
  · exact B1261747
  · exact B1261751
  · exact B1261755
  · exact B1261759
  · exact B1261763
  · exact B1261767
  · exact B1261771
  · exact B1261775
  · exact B1261779
  · exact B1261783
  · exact B1261787
  · exact B1261791
  · exact B1261795
  · exact B1261799
  · exact B1261803
  · exact B1261807
  · exact B1261811
  · exact B1261815
  · exact B1261819
  · exact B1261823
  · exact B1261827
  · exact B1261831
  · exact B1261835
  · exact B1261839
  · exact B1261843
  · exact B1261847
  · exact B1261851
  · exact B1261855
  · exact B1261859
  · exact B1261863
  · exact B1261867
  · exact B1261871
  · exact B1261875
  · exact B1261879
  · exact B1261883
  · exact B1261887
  · exact B1261891
  · exact B1261895
  · exact B1261899
  · exact B1261903
  · exact B1261907
  · exact B1261911
  · exact B1261915
  · exact B1261919
  · exact B1261923
  · exact B1261927
  · exact B1261931
  · exact B1261935
  · exact B1261939
  · exact B1261943
  · exact B1261947
  · exact B1261951
  · exact B1261955
  · exact B1261959
  · exact B1261963
  · exact B1261967
  · exact B1261971
  · exact B1261975
  · exact B1261979
  · exact B1261983
  · exact B1261987
  · exact B1261991
  · exact B1261995
  · exact B1261999
  · exact B1262003
  · exact B1262007
  · exact B1262011
  · exact B1262015
  · exact B1262019
  · exact B1262023
  · exact B1262027
  · exact B1262031
  · exact B1262035
  · exact B1262039
  · exact B1262043
  · exact B1262047
  · exact B1262051
  · exact B1262055
  · exact B1262059
  · exact B1262063
  · exact B1262067
  · exact B1262071
  · exact B1262075
  · exact B1262079
  · exact B1262083
  · exact B1262087
  · exact B1262091
  · exact B1262095
  · exact B1262099
  · exact B1262103
  · exact B1262107
  · exact B1262111
  · exact B1262115
  · exact B1262119
  · exact B1262123
  · exact B1262127
  · exact B1262131
  · exact B1262135
  · exact B1262139
  · exact B1262143
  · exact B1262147
  · exact B1262151
  · exact B1262155
  · exact B1262159
  · exact B1262163
  · exact B1262167
  · exact B1262171
  · exact B1262175
  · exact B1262179
  · exact B1262183
  · exact B1262187
  · exact B1262191
  · exact B1262195
  · exact B1262199
  · exact B1262203
  · exact B1262207
  · exact B1262211
  · exact B1262215
  · exact B1262219
  · exact B1262223
  · exact B1262227
  · exact B1262231
  · exact B1262235
  · exact B1262239
  · exact B1262243
  · exact B1262247
  · exact B1262251
  · exact B1262255
  · exact B1262259
  · exact B1262263
  · exact B1262267
  · exact B1262271
  · exact B1262275
  · exact B1262279
  · exact B1262283
  · exact B1262287
  · exact B1262291
  · exact B1262295
  · exact B1262299
  · exact B1262303
  · exact B1262307
  · exact B1262311
  · exact B1262315
  · exact B1262319
  · exact B1262323
  · exact B1262327
  · exact B1262331
  · exact B1262335
  · exact B1262339
  · exact B1262343
  · exact B1262347
  · exact B1262351
  · exact B1262355
  · exact B1262359
  · exact B1262363
  · exact B1262367
  · exact B1262371
  · exact B1262375
  · exact B1262379
  · exact B1262383
  · exact B1262387
  · exact B1262391
  · exact B1262395
  · exact B1262399
  · exact B1262403
  · exact B1262407
  · exact B1262411
  · exact B1262415
  · exact B1262419
  · exact B1262423
  · exact B1262427
  · exact B1262431
  · exact B1262435
  · exact B1262439
  · exact B1262443
  · exact B1262447

theorem solution (m : ℕ) (hlo : 1260448 ≤ m) (hhi : m ≤ 1262448) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 315112 ≤ j := by omega
    have hj2 : j ≤ 315611 := by omega
    have hb : Blo 1260448 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
