-- Prove2me | solution 1 for syracuse_descends_range_1559477_1561477
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:06:14.010276+00:00
-- url     : https://prove2.me/submissions/e3b73717-85ae-4328-be67-0ada4cdd09d7

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


theorem B5922821 : Blo 1559477 5922821 := bbase (se 4 (by rfl) ⟨555264, by rfl⟩ : syracuseStep 5922821 = 1110529) (by norm_num)
theorem B1974289 : Blo 1559477 1974289 := bbase (se 2 (by rfl) ⟨740358, by rfl⟩ : syracuseStep 1974289 = 1480717) (by norm_num)
theorem B1581089 : Blo 1559477 1581089 := bbase (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) (by norm_num)
theorem B1974385 : Blo 1559477 1974385 := bbase (se 2 (by rfl) ⟨740394, by rfl⟩ : syracuseStep 1974385 = 1480789) (by norm_num)
theorem B3162277 : Blo 1559477 3162277 := bbase (se 4 (by rfl) ⟨296463, by rfl⟩ : syracuseStep 3162277 = 592927) (by norm_num)
theorem B3948709 : Blo 1559477 3948709 := bbase (se 4 (by rfl) ⟨370191, by rfl⟩ : syracuseStep 3948709 = 740383) (by norm_num)
theorem B6086917 : Blo 1559477 6086917 := bbase (se 4 (by rfl) ⟨570648, by rfl⟩ : syracuseStep 6086917 = 1141297) (by norm_num)
theorem B4006157 : Blo 1559477 4006157 := bbase (se 3 (by rfl) ⟨751154, by rfl⟩ : syracuseStep 4006157 = 1502309) (by norm_num)
theorem B3948821 : Blo 1559477 3948821 := bbase (se 6 (by rfl) ⟨92550, by rfl⟩ : syracuseStep 3948821 = 185101) (by norm_num)
theorem B2498845 : Blo 1559477 2498845 := bbase (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) (by norm_num)
theorem B1974557 : Blo 1559477 1974557 := bbase (se 3 (by rfl) ⟨370229, by rfl⟩ : syracuseStep 1974557 = 740459) (by norm_num)
theorem B7119173 : Blo 1559477 7119173 := bbase (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) (by norm_num)
theorem B1974613 : Blo 1559477 1974613 := bbase (se 10 (by rfl) ⟨2892, by rfl⟩ : syracuseStep 1974613 = 5785) (by norm_num)
theorem B5267861 : Blo 1559477 5267861 := bbase (se 6 (by rfl) ⟨123465, by rfl⟩ : syracuseStep 5267861 = 246931) (by norm_num)
theorem B8438165 : Blo 1559477 8438165 := bbase (se 6 (by rfl) ⟨197769, by rfl⟩ : syracuseStep 8438165 = 395539) (by norm_num)
theorem B1974709 : Blo 1559477 1974709 := bbase (se 5 (by rfl) ⟨92564, by rfl⟩ : syracuseStep 1974709 = 185129) (by norm_num)
theorem B3949013 : Blo 1559477 3949013 := bbase (se 7 (by rfl) ⟨46277, by rfl⟩ : syracuseStep 3949013 = 92555) (by norm_num)
theorem B3334621 : Blo 1559477 3334621 := bbase (se 3 (by rfl) ⟨625241, by rfl⟩ : syracuseStep 3334621 = 1250483) (by norm_num)
theorem B2499101 : Blo 1559477 2499101 := bbase (se 3 (by rfl) ⟨468581, by rfl⟩ : syracuseStep 2499101 = 937163) (by norm_num)
theorem B2253349 : Blo 1559477 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B1581637 : Blo 1559477 1581637 := bbase (se 4 (by rfl) ⟨148278, by rfl⟩ : syracuseStep 1581637 = 296557) (by norm_num)
theorem B8438357 : Blo 1559477 8438357 := bbase (se 8 (by rfl) ⟨49443, by rfl⟩ : syracuseStep 8438357 = 98887) (by norm_num)
theorem B2220637 : Blo 1559477 2220637 := bbase (se 3 (by rfl) ⟨416369, by rfl⟩ : syracuseStep 2220637 = 832739) (by norm_num)
theorem B1974881 : Blo 1559477 1974881 := bbase (se 2 (by rfl) ⟨740580, by rfl⟩ : syracuseStep 1974881 = 1481161) (by norm_num)
theorem B3334765 : Blo 1559477 3334765 := bbase (se 3 (by rfl) ⟨625268, by rfl⟩ : syracuseStep 3334765 = 1250537) (by norm_num)
theorem B1974937 : Blo 1559477 1974937 := bbase (se 2 (by rfl) ⟨740601, by rfl⟩ : syracuseStep 1974937 = 1481203) (by norm_num)
theorem B7119557 : Blo 1559477 7119557 := bbase (se 4 (by rfl) ⟨667458, by rfl⟩ : syracuseStep 7119557 = 1334917) (by norm_num)
theorem B2499293 : Blo 1559477 2499293 := bbase (se 3 (by rfl) ⟨468617, by rfl⟩ : syracuseStep 2499293 = 937235) (by norm_num)
theorem B1975033 : Blo 1559477 1975033 := bbase (se 2 (by rfl) ⟨740637, by rfl⟩ : syracuseStep 1975033 = 1481275) (by norm_num)
theorem B3949357 : Blo 1559477 3949357 := bbase (se 3 (by rfl) ⟨740504, by rfl⟩ : syracuseStep 3949357 = 1481009) (by norm_num)
theorem B2220853 : Blo 1559477 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B5268293 : Blo 1559477 5268293 := bbase (se 4 (by rfl) ⟨493902, by rfl⟩ : syracuseStep 5268293 = 987805) (by norm_num)
theorem B3801941 : Blo 1559477 3801941 := bbase (se 9 (by rfl) ⟨11138, by rfl⟩ : syracuseStep 3801941 = 22277) (by norm_num)
theorem B3949469 : Blo 1559477 3949469 := bbase (se 3 (by rfl) ⟨740525, by rfl⟩ : syracuseStep 3949469 = 1481051) (by norm_num)
theorem B1975205 : Blo 1559477 1975205 := bbase (se 4 (by rfl) ⟨185175, by rfl⟩ : syracuseStep 1975205 = 370351) (by norm_num)
theorem B4219829 : Blo 1559477 4219829 := bbase (se 5 (by rfl) ⟨197804, by rfl⟩ : syracuseStep 4219829 = 395609) (by norm_num)
theorem B1975261 : Blo 1559477 1975261 := bbase (se 3 (by rfl) ⟨370361, by rfl⟩ : syracuseStep 1975261 = 740723) (by norm_num)
theorem B1975357 : Blo 1559477 1975357 := bbase (se 3 (by rfl) ⟨370379, by rfl⟩ : syracuseStep 1975357 = 740759) (by norm_num)
theorem B3949661 : Blo 1559477 3949661 := bbase (se 3 (by rfl) ⟨740561, by rfl⟩ : syracuseStep 3949661 = 1481123) (by norm_num)
theorem B4441205 : Blo 1559477 4441205 := bbase (se 5 (by rfl) ⟨208181, by rfl⟩ : syracuseStep 4441205 = 416363) (by norm_num)
theorem B1582201 : Blo 1559477 1582201 := bbase (se 2 (by rfl) ⟨593325, by rfl⟩ : syracuseStep 1582201 = 1186651) (by norm_num)
theorem B11854997 : Blo 1559477 11854997 := bbase (se 6 (by rfl) ⟨277851, by rfl⟩ : syracuseStep 11854997 = 555703) (by norm_num)
theorem B2221229 : Blo 1559477 2221229 := bbase (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) (by norm_num)
theorem B7898309 : Blo 1559477 7898309 := bbase (se 4 (by rfl) ⟨740466, by rfl⟩ : syracuseStep 7898309 = 1480933) (by norm_num)
theorem B1975529 : Blo 1559477 1975529 := bbase (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) (by norm_num)
theorem B5268725 : Blo 1559477 5268725 := bbase (se 5 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 5268725 = 493943) (by norm_num)
theorem B10003733 : Blo 1559477 10003733 := bbase (se 6 (by rfl) ⟨234462, by rfl⟩ : syracuseStep 10003733 = 468925) (by norm_num)
theorem B1975585 : Blo 1559477 1975585 := bbase (se 2 (by rfl) ⟨740844, by rfl⟩ : syracuseStep 1975585 = 1481689) (by norm_num)
theorem B3163445 : Blo 1559477 3163445 := bbase (se 5 (by rfl) ⟨148286, by rfl⟩ : syracuseStep 3163445 = 296573) (by norm_num)
theorem B1754437 : Blo 1559477 1754437 := bbase (se 4 (by rfl) ⟨164478, by rfl⟩ : syracuseStep 1754437 = 328957) (by norm_num)
theorem B1754473 : Blo 1559477 1754473 := bbase (se 2 (by rfl) ⟨657927, by rfl⟩ : syracuseStep 1754473 = 1315855) (by norm_num)
theorem B1975681 : Blo 1559477 1975681 := bbase (se 2 (by rfl) ⟨740880, by rfl⟩ : syracuseStep 1975681 = 1481761) (by norm_num)
theorem B1754509 : Blo 1559477 1754509 := bbase (se 3 (by rfl) ⟨328970, by rfl⟩ : syracuseStep 1754509 = 657941) (by norm_num)
theorem B3163541 : Blo 1559477 3163541 := bbase (se 6 (by rfl) ⟨74145, by rfl⟩ : syracuseStep 3163541 = 148291) (by norm_num)
theorem B1754545 : Blo 1559477 1754545 := bbase (se 2 (by rfl) ⟨657954, by rfl⟩ : syracuseStep 1754545 = 1315909) (by norm_num)
theorem B3950005 : Blo 1559477 3950005 := bbase (se 5 (by rfl) ⟨185156, by rfl⟩ : syracuseStep 3950005 = 370313) (by norm_num)
theorem B1754581 : Blo 1559477 1754581 := bbase (se 7 (by rfl) ⟨20561, by rfl⟩ : syracuseStep 1754581 = 41123) (by norm_num)
theorem B4220389 : Blo 1559477 4220389 := bbase (se 4 (by rfl) ⟨395661, by rfl⟩ : syracuseStep 4220389 = 791323) (by norm_num)
theorem B1754617 : Blo 1559477 1754617 := bbase (se 2 (by rfl) ⟨657981, by rfl⟩ : syracuseStep 1754617 = 1315963) (by norm_num)
theorem B1754653 : Blo 1559477 1754653 := bbase (se 3 (by rfl) ⟨328997, by rfl⟩ : syracuseStep 1754653 = 657995) (by norm_num)
theorem B3950117 : Blo 1559477 3950117 := bbase (se 4 (by rfl) ⟨370323, by rfl⟩ : syracuseStep 3950117 = 740647) (by norm_num)
theorem B1975853 : Blo 1559477 1975853 := bbase (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) (by norm_num)
theorem B11847221 : Blo 1559477 11847221 := bbase (se 5 (by rfl) ⟨555338, by rfl⟩ : syracuseStep 11847221 = 1110677) (by norm_num)
theorem B1754689 : Blo 1559477 1754689 := bbase (se 2 (by rfl) ⟨658008, by rfl⟩ : syracuseStep 1754689 = 1316017) (by norm_num)
theorem B1754725 : Blo 1559477 1754725 := bbase (se 4 (by rfl) ⟨164505, by rfl⟩ : syracuseStep 1754725 = 329011) (by norm_num)
theorem B1975909 : Blo 1559477 1975909 := bbase (se 4 (by rfl) ⟨185241, by rfl⟩ : syracuseStep 1975909 = 370483) (by norm_num)
theorem B3376765 : Blo 1559477 3376765 := bbase (se 3 (by rfl) ⟨633143, by rfl⟩ : syracuseStep 3376765 = 1266287) (by norm_num)
theorem B2500229 : Blo 1559477 2500229 := bbase (se 4 (by rfl) ⟨234396, by rfl⟩ : syracuseStep 2500229 = 468793) (by norm_num)
theorem B1754761 : Blo 1559477 1754761 := bbase (se 2 (by rfl) ⟨658035, by rfl⟩ : syracuseStep 1754761 = 1316071) (by norm_num)
theorem B5269157 : Blo 1559477 5269157 := bbase (se 4 (by rfl) ⟨493983, by rfl⟩ : syracuseStep 5269157 = 987967) (by norm_num)
theorem B1754797 : Blo 1559477 1754797 := bbase (se 3 (by rfl) ⟨329024, by rfl⟩ : syracuseStep 1754797 = 658049) (by norm_num)
theorem B1976005 : Blo 1559477 1976005 := bbase (se 4 (by rfl) ⟨185250, by rfl⟩ : syracuseStep 1976005 = 370501) (by norm_num)
theorem B1754833 : Blo 1559477 1754833 := bbase (se 2 (by rfl) ⟨658062, by rfl⟩ : syracuseStep 1754833 = 1316125) (by norm_num)
theorem B3950309 : Blo 1559477 3950309 := bbase (se 4 (by rfl) ⟨370341, by rfl⟩ : syracuseStep 3950309 = 740683) (by norm_num)
theorem B1754869 : Blo 1559477 1754869 := bbase (se 5 (by rfl) ⟨82259, by rfl⟩ : syracuseStep 1754869 = 164519) (by norm_num)
theorem B1754905 : Blo 1559477 1754905 := bbase (se 2 (by rfl) ⟨658089, by rfl⟩ : syracuseStep 1754905 = 1316179) (by norm_num)
theorem B1754941 : Blo 1559477 1754941 := bbase (se 3 (by rfl) ⟨329051, by rfl⟩ : syracuseStep 1754941 = 658103) (by norm_num)
theorem B1754977 : Blo 1559477 1754977 := bbase (se 2 (by rfl) ⟨658116, by rfl⟩ : syracuseStep 1754977 = 1316233) (by norm_num)
theorem B1976177 : Blo 1559477 1976177 := bbase (se 2 (by rfl) ⟨741066, by rfl⟩ : syracuseStep 1976177 = 1482133) (by norm_num)
theorem B1755013 : Blo 1559477 1755013 := bbase (se 4 (by rfl) ⟨164532, by rfl⟩ : syracuseStep 1755013 = 329065) (by norm_num)
theorem B18270101 : Blo 1559477 18270101 := bbase (se 6 (by rfl) ⟨428205, by rfl⟩ : syracuseStep 18270101 = 856411) (by norm_num)
theorem B1689509 : Blo 1559477 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B1755049 : Blo 1559477 1755049 := bbase (se 2 (by rfl) ⟨658143, by rfl⟩ : syracuseStep 1755049 = 1316287) (by norm_num)
theorem B1976233 : Blo 1559477 1976233 := bbase (se 2 (by rfl) ⟨741087, by rfl⟩ : syracuseStep 1976233 = 1482175) (by norm_num)
theorem B2631629 : Blo 1559477 2631629 := bbase (se 3 (by rfl) ⟨493430, by rfl⟩ : syracuseStep 2631629 = 986861) (by norm_num)
theorem B1755085 : Blo 1559477 1755085 := bbase (se 3 (by rfl) ⟨329078, by rfl⟩ : syracuseStep 1755085 = 658157) (by norm_num)
theorem B1755121 : Blo 1559477 1755121 := bbase (se 2 (by rfl) ⟨658170, by rfl⟩ : syracuseStep 1755121 = 1316341) (by norm_num)
theorem B2500613 : Blo 1559477 2500613 := bbase (se 4 (by rfl) ⟨234432, by rfl⟩ : syracuseStep 2500613 = 468865) (by norm_num)
theorem B1755157 : Blo 1559477 1755157 := bbase (se 6 (by rfl) ⟨41136, by rfl⟩ : syracuseStep 1755157 = 82273) (by norm_num)
theorem B1755193 : Blo 1559477 1755193 := bbase (se 2 (by rfl) ⟨658197, by rfl⟩ : syracuseStep 1755193 = 1316395) (by norm_num)
theorem B3950653 : Blo 1559477 3950653 := bbase (se 3 (by rfl) ⟨740747, by rfl⟩ : syracuseStep 3950653 = 1481495) (by norm_num)
theorem B5924933 : Blo 1559477 5924933 := bbase (se 4 (by rfl) ⟨555462, by rfl⟩ : syracuseStep 5924933 = 1110925) (by norm_num)
theorem B2631757 : Blo 1559477 2631757 := bbase (se 3 (by rfl) ⟨493454, by rfl⟩ : syracuseStep 2631757 = 986909) (by norm_num)
theorem B5269589 : Blo 1559477 5269589 := bbase (se 8 (by rfl) ⟨30876, by rfl⟩ : syracuseStep 5269589 = 61753) (by norm_num)
theorem B1755229 : Blo 1559477 1755229 := bbase (se 3 (by rfl) ⟨329105, by rfl⟩ : syracuseStep 1755229 = 658211) (by norm_num)
theorem B14993525 : Blo 1559477 14993525 := bbase (se 5 (by rfl) ⟨702821, by rfl⟩ : syracuseStep 14993525 = 1405643) (by norm_num)
theorem B1755265 : Blo 1559477 1755265 := bbase (se 2 (by rfl) ⟨658224, by rfl⟩ : syracuseStep 1755265 = 1316449) (by norm_num)
theorem B2500741 : Blo 1559477 2500741 := bbase (se 4 (by rfl) ⟨234444, by rfl⟩ : syracuseStep 2500741 = 468889) (by norm_num)
theorem B2631845 : Blo 1559477 2631845 := bbase (se 4 (by rfl) ⟨246735, by rfl⟩ : syracuseStep 2631845 = 493471) (by norm_num)
theorem B1755301 : Blo 1559477 1755301 := bbase (se 4 (by rfl) ⟨164559, by rfl⟩ : syracuseStep 1755301 = 329119) (by norm_num)
theorem B3950765 : Blo 1559477 3950765 := bbase (se 3 (by rfl) ⟨740768, by rfl⟩ : syracuseStep 3950765 = 1481537) (by norm_num)
theorem B1755337 : Blo 1559477 1755337 := bbase (se 2 (by rfl) ⟨658251, by rfl⟩ : syracuseStep 1755337 = 1316503) (by norm_num)
theorem B1755373 : Blo 1559477 1755373 := bbase (se 3 (by rfl) ⟨329132, by rfl⟩ : syracuseStep 1755373 = 658265) (by norm_num)
theorem B5335301 : Blo 1559477 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B1755409 : Blo 1559477 1755409 := bbase (se 2 (by rfl) ⟨658278, by rfl⟩ : syracuseStep 1755409 = 1316557) (by norm_num)
theorem B2631973 : Blo 1559477 2631973 := bbase (se 4 (by rfl) ⟨246747, by rfl⟩ : syracuseStep 2631973 = 493495) (by norm_num)
theorem B1755445 : Blo 1559477 1755445 := bbase (se 5 (by rfl) ⟨82286, by rfl⟩ : syracuseStep 1755445 = 164573) (by norm_num)
theorem B4811093 : Blo 1559477 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B1755481 : Blo 1559477 1755481 := bbase (se 2 (by rfl) ⟨658305, by rfl⟩ : syracuseStep 1755481 = 1316611) (by norm_num)
theorem B5925221 : Blo 1559477 5925221 := bbase (se 4 (by rfl) ⟨555489, by rfl⟩ : syracuseStep 5925221 = 1110979) (by norm_num)
theorem B3950957 : Blo 1559477 3950957 := bbase (se 3 (by rfl) ⟨740804, by rfl⟩ : syracuseStep 3950957 = 1481609) (by norm_num)
theorem B1665397 : Blo 1559477 1665397 := bbase (se 5 (by rfl) ⟨78065, by rfl⟩ : syracuseStep 1665397 = 156131) (by norm_num)
theorem B2632061 : Blo 1559477 2632061 := bbase (se 3 (by rfl) ⟨493511, by rfl⟩ : syracuseStep 2632061 = 987023) (by norm_num)
theorem B1755517 : Blo 1559477 1755517 := bbase (se 3 (by rfl) ⟨329159, by rfl⟩ : syracuseStep 1755517 = 658319) (by norm_num)
theorem B4999573 : Blo 1559477 4999573 := bbase (se 6 (by rfl) ⟨117177, by rfl⟩ : syracuseStep 4999573 = 234355) (by norm_num)
theorem B1755553 : Blo 1559477 1755553 := bbase (se 2 (by rfl) ⟨658332, by rfl⟩ : syracuseStep 1755553 = 1316665) (by norm_num)
theorem B1665469 : Blo 1559477 1665469 := bbase (se 3 (by rfl) ⟨312275, by rfl⟩ : syracuseStep 1665469 = 624551) (by norm_num)
theorem B1755589 : Blo 1559477 1755589 := bbase (se 4 (by rfl) ⟨164586, by rfl⟩ : syracuseStep 1755589 = 329173) (by norm_num)
theorem B7899605 : Blo 1559477 7899605 := bbase (se 7 (by rfl) ⟨92573, by rfl⟩ : syracuseStep 7899605 = 185147) (by norm_num)
theorem B4999637 : Blo 1559477 4999637 := bbase (se 7 (by rfl) ⟨58589, by rfl⟩ : syracuseStep 4999637 = 117179) (by norm_num)
theorem B1755625 : Blo 1559477 1755625 := bbase (se 2 (by rfl) ⟨658359, by rfl⟩ : syracuseStep 1755625 = 1316719) (by norm_num)
theorem B2632189 : Blo 1559477 2632189 := bbase (se 3 (by rfl) ⟨493535, by rfl⟩ : syracuseStep 2632189 = 987071) (by norm_num)
theorem B1755661 : Blo 1559477 1755661 := bbase (se 3 (by rfl) ⟨329186, by rfl⟩ : syracuseStep 1755661 = 658373) (by norm_num)
theorem B1755697 : Blo 1559477 1755697 := bbase (se 2 (by rfl) ⟨658386, by rfl⟩ : syracuseStep 1755697 = 1316773) (by norm_num)
theorem B1804853 : Blo 1559477 1804853 := bbase (se 5 (by rfl) ⟨84602, by rfl⟩ : syracuseStep 1804853 = 169205) (by norm_num)
theorem B2222653 : Blo 1559477 2222653 := bbase (se 3 (by rfl) ⟨416747, by rfl⟩ : syracuseStep 2222653 = 833495) (by norm_num)
theorem B2632277 : Blo 1559477 2632277 := bbase (se 8 (by rfl) ⟨15423, by rfl⟩ : syracuseStep 2632277 = 30847) (by norm_num)
theorem B1755733 : Blo 1559477 1755733 := bbase (se 8 (by rfl) ⟨10287, by rfl⟩ : syracuseStep 1755733 = 20575) (by norm_num)
theorem B3508829 : Blo 1559477 3508829 := bbase (se 3 (by rfl) ⟨657905, by rfl⟩ : syracuseStep 3508829 = 1315811) (by norm_num)
theorem B3164773 : Blo 1559477 3164773 := bbase (se 4 (by rfl) ⟨296697, by rfl⟩ : syracuseStep 3164773 = 593395) (by norm_num)
theorem B1755769 : Blo 1559477 1755769 := bbase (se 2 (by rfl) ⟨658413, by rfl⟩ : syracuseStep 1755769 = 1316827) (by norm_num)
theorem B1755805 : Blo 1559477 1755805 := bbase (se 3 (by rfl) ⟨329213, by rfl⟩ : syracuseStep 1755805 = 658427) (by norm_num)
theorem B3508901 : Blo 1559477 3508901 := bbase (se 4 (by rfl) ⟨328959, by rfl⟩ : syracuseStep 3508901 = 657919) (by norm_num)
theorem B4442789 : Blo 1559477 4442789 := bbase (se 4 (by rfl) ⟨416511, by rfl⟩ : syracuseStep 4442789 = 833023) (by norm_num)
theorem B2001601 : Blo 1559477 2001601 := bbase (se 2 (by rfl) ⟨750600, by rfl⟩ : syracuseStep 2001601 = 1501201) (by norm_num)
theorem B1755841 : Blo 1559477 1755841 := bbase (se 2 (by rfl) ⟨658440, by rfl⟩ : syracuseStep 1755841 = 1316881) (by norm_num)
theorem B3951301 : Blo 1559477 3951301 := bbase (se 4 (by rfl) ⟨370434, by rfl⟩ : syracuseStep 3951301 = 740869) (by norm_num)
theorem B2632405 : Blo 1559477 2632405 := bbase (se 7 (by rfl) ⟨30848, by rfl⟩ : syracuseStep 2632405 = 61697) (by norm_num)
theorem B3558109 : Blo 1559477 3558109 := bbase (se 3 (by rfl) ⟨667145, by rfl⟩ : syracuseStep 3558109 = 1334291) (by norm_num)
theorem B1755877 : Blo 1559477 1755877 := bbase (se 4 (by rfl) ⟨164613, by rfl⟩ : syracuseStep 1755877 = 329227) (by norm_num)
theorem B3508973 : Blo 1559477 3508973 := bbase (se 3 (by rfl) ⟨657932, by rfl⟩ : syracuseStep 3508973 = 1315865) (by norm_num)
theorem B1755913 : Blo 1559477 1755913 := bbase (se 2 (by rfl) ⟨658467, by rfl⟩ : syracuseStep 1755913 = 1316935) (by norm_num)
theorem B2632493 : Blo 1559477 2632493 := bbase (se 3 (by rfl) ⟨493592, by rfl⟩ : syracuseStep 2632493 = 987185) (by norm_num)
theorem B1755949 : Blo 1559477 1755949 := bbase (se 3 (by rfl) ⟨329240, by rfl⟩ : syracuseStep 1755949 = 658481) (by norm_num)
theorem B1665841 : Blo 1559477 1665841 := bbase (se 2 (by rfl) ⟨624690, by rfl⟩ : syracuseStep 1665841 = 1249381) (by norm_num)
theorem B3509045 : Blo 1559477 3509045 := bbase (se 5 (by rfl) ⟨164486, by rfl⟩ : syracuseStep 3509045 = 328973) (by norm_num)
theorem B3951413 : Blo 1559477 3951413 := bbase (se 5 (by rfl) ⟨185222, by rfl⟩ : syracuseStep 3951413 = 370445) (by norm_num)
theorem B1755985 : Blo 1559477 1755985 := bbase (se 2 (by rfl) ⟨658494, by rfl⟩ : syracuseStep 1755985 = 1316989) (by norm_num)
theorem B1756021 : Blo 1559477 1756021 := bbase (se 5 (by rfl) ⟨82313, by rfl⟩ : syracuseStep 1756021 = 164627) (by norm_num)
theorem B3509117 : Blo 1559477 3509117 := bbase (se 3 (by rfl) ⟨657959, by rfl⟩ : syracuseStep 3509117 = 1315919) (by norm_num)
theorem B1756057 : Blo 1559477 1756057 := bbase (se 2 (by rfl) ⟨658521, by rfl⟩ : syracuseStep 1756057 = 1317043) (by norm_num)
theorem B2632621 : Blo 1559477 2632621 := bbase (se 3 (by rfl) ⟨493616, by rfl⟩ : syracuseStep 2632621 = 987233) (by norm_num)
theorem B1756093 : Blo 1559477 1756093 := bbase (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) (by norm_num)
theorem B3509189 : Blo 1559477 3509189 := bbase (se 4 (by rfl) ⟨328986, by rfl⟩ : syracuseStep 3509189 = 657973) (by norm_num)
theorem B3378133 : Blo 1559477 3378133 := bbase (se 7 (by rfl) ⟨39587, by rfl⟩ : syracuseStep 3378133 = 79175) (by norm_num)
theorem B1756129 : Blo 1559477 1756129 := bbase (se 2 (by rfl) ⟨658548, by rfl⟩ : syracuseStep 1756129 = 1317097) (by norm_num)
theorem B3951605 : Blo 1559477 3951605 := bbase (se 5 (by rfl) ⟨185231, by rfl⟩ : syracuseStep 3951605 = 370463) (by norm_num)
theorem B7597061 : Blo 1559477 7597061 := bbase (se 4 (by rfl) ⟨712224, by rfl⟩ : syracuseStep 7597061 = 1424449) (by norm_num)
theorem B2632709 : Blo 1559477 2632709 := bbase (se 4 (by rfl) ⟨246816, by rfl⟩ : syracuseStep 2632709 = 493633) (by norm_num)
theorem B1756165 : Blo 1559477 1756165 := bbase (se 4 (by rfl) ⟨164640, by rfl⟩ : syracuseStep 1756165 = 329281) (by norm_num)
theorem B3509261 : Blo 1559477 3509261 := bbase (se 3 (by rfl) ⟨657986, by rfl⟩ : syracuseStep 3509261 = 1315973) (by norm_num)
theorem B1756201 : Blo 1559477 1756201 := bbase (se 2 (by rfl) ⟨658575, by rfl⟩ : syracuseStep 1756201 = 1317151) (by norm_num)
theorem B1756237 : Blo 1559477 1756237 := bbase (se 3 (by rfl) ⟨329294, by rfl⟩ : syracuseStep 1756237 = 658589) (by norm_num)
theorem B3509333 : Blo 1559477 3509333 := bbase (se 8 (by rfl) ⟨20562, by rfl⟩ : syracuseStep 3509333 = 41125) (by norm_num)
theorem B8891477 : Blo 1559477 8891477 := bbase (se 8 (by rfl) ⟨52098, by rfl⟩ : syracuseStep 8891477 = 104197) (by norm_num)
theorem B3206245 : Blo 1559477 3206245 := bbase (se 4 (by rfl) ⟨300585, by rfl⟩ : syracuseStep 3206245 = 601171) (by norm_num)
theorem B1756273 : Blo 1559477 1756273 := bbase (se 2 (by rfl) ⟨658602, by rfl⟩ : syracuseStep 1756273 = 1317205) (by norm_num)
theorem B2632837 : Blo 1559477 2632837 := bbase (se 4 (by rfl) ⟨246828, by rfl⟩ : syracuseStep 2632837 = 493657) (by norm_num)
theorem B2223245 : Blo 1559477 2223245 := bbase (se 3 (by rfl) ⟨416858, by rfl⟩ : syracuseStep 2223245 = 833717) (by norm_num)
theorem B1756309 : Blo 1559477 1756309 := bbase (se 6 (by rfl) ⟨41163, by rfl⟩ : syracuseStep 1756309 = 82327) (by norm_num)
theorem B3509405 : Blo 1559477 3509405 := bbase (se 3 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 3509405 = 1316027) (by norm_num)
theorem B1666217 : Blo 1559477 1666217 := bbase (se 2 (by rfl) ⟨624831, by rfl⟩ : syracuseStep 1666217 = 1249663) (by norm_num)
theorem B1756345 : Blo 1559477 1756345 := bbase (se 2 (by rfl) ⟨658629, by rfl⟩ : syracuseStep 1756345 = 1317259) (by norm_num)
theorem B2632925 : Blo 1559477 2632925 := bbase (se 3 (by rfl) ⟨493673, by rfl⟩ : syracuseStep 2632925 = 987347) (by norm_num)
theorem B1756381 : Blo 1559477 1756381 := bbase (se 3 (by rfl) ⟨329321, by rfl⟩ : syracuseStep 1756381 = 658643) (by norm_num)
theorem B3509477 : Blo 1559477 3509477 := bbase (se 4 (by rfl) ⟨329013, by rfl⟩ : syracuseStep 3509477 = 658027) (by norm_num)
theorem B2960621 : Blo 1559477 2960621 := bbase (se 3 (by rfl) ⟨555116, by rfl⟩ : syracuseStep 2960621 = 1110233) (by norm_num)
theorem B1666289 : Blo 1559477 1666289 := bbase (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) (by norm_num)
theorem B3252221 : Blo 1559477 3252221 := bbase (se 3 (by rfl) ⟨609791, by rfl⟩ : syracuseStep 3252221 = 1219583) (by norm_num)
theorem B1756417 : Blo 1559477 1756417 := bbase (se 2 (by rfl) ⟨658656, by rfl⟩ : syracuseStep 1756417 = 1317313) (by norm_num)
theorem B2108693 : Blo 1559477 2108693 := bbase (se 6 (by rfl) ⟨49422, by rfl⟩ : syracuseStep 2108693 = 98845) (by norm_num)
theorem B3378461 : Blo 1559477 3378461 := bbase (se 3 (by rfl) ⟨633461, by rfl⟩ : syracuseStep 3378461 = 1266923) (by norm_num)
theorem B1756453 : Blo 1559477 1756453 := bbase (se 4 (by rfl) ⟨164667, by rfl⟩ : syracuseStep 1756453 = 329335) (by norm_num)
theorem B3509549 : Blo 1559477 3509549 := bbase (se 3 (by rfl) ⟨658040, by rfl⟩ : syracuseStep 3509549 = 1316081) (by norm_num)
theorem B4443461 : Blo 1559477 4443461 := bbase (se 4 (by rfl) ⟨416574, by rfl⟩ : syracuseStep 4443461 = 833149) (by norm_num)
theorem B1756489 : Blo 1559477 1756489 := bbase (se 2 (by rfl) ⟨658683, by rfl⟩ : syracuseStep 1756489 = 1317367) (by norm_num)
theorem B3951949 : Blo 1559477 3951949 := bbase (se 3 (by rfl) ⟨740990, by rfl⟩ : syracuseStep 3951949 = 1481981) (by norm_num)
theorem B2633053 : Blo 1559477 2633053 := bbase (se 3 (by rfl) ⟨493697, by rfl⟩ : syracuseStep 2633053 = 987395) (by norm_num)
theorem B1756525 : Blo 1559477 1756525 := bbase (se 3 (by rfl) ⟨329348, by rfl⟩ : syracuseStep 1756525 = 658697) (by norm_num)
theorem B3509621 : Blo 1559477 3509621 := bbase (se 5 (by rfl) ⟨164513, by rfl⟩ : syracuseStep 3509621 = 329027) (by norm_num)
theorem B1756561 : Blo 1559477 1756561 := bbase (se 2 (by rfl) ⟨658710, by rfl⟩ : syracuseStep 1756561 = 1317421) (by norm_num)
theorem B1666477 : Blo 1559477 1666477 := bbase (se 3 (by rfl) ⟨312464, by rfl⟩ : syracuseStep 1666477 = 624929) (by norm_num)
theorem B2633141 : Blo 1559477 2633141 := bbase (se 5 (by rfl) ⟨123428, by rfl⟩ : syracuseStep 2633141 = 246857) (by norm_num)
theorem B1756597 : Blo 1559477 1756597 := bbase (se 5 (by rfl) ⟨82340, by rfl⟩ : syracuseStep 1756597 = 164681) (by norm_num)
theorem B3509693 : Blo 1559477 3509693 := bbase (se 3 (by rfl) ⟨658067, by rfl⟩ : syracuseStep 3509693 = 1316135) (by norm_num)
theorem B3952061 : Blo 1559477 3952061 := bbase (se 3 (by rfl) ⟨741011, by rfl⟩ : syracuseStep 3952061 = 1482023) (by norm_num)
theorem B5336533 : Blo 1559477 5336533 := bbase (se 7 (by rfl) ⟨62537, by rfl⟩ : syracuseStep 5336533 = 125075) (by norm_num)
theorem B1756633 : Blo 1559477 1756633 := bbase (se 2 (by rfl) ⟨658737, by rfl⟩ : syracuseStep 1756633 = 1317475) (by norm_num)
theorem B6663653 : Blo 1559477 6663653 := bbase (se 4 (by rfl) ⟨624717, by rfl⟩ : syracuseStep 6663653 = 1249435) (by norm_num)
theorem B3509765 : Blo 1559477 3509765 := bbase (se 4 (by rfl) ⟨329040, by rfl⟩ : syracuseStep 3509765 = 658081) (by norm_num)
theorem B5926405 : Blo 1559477 5926405 := bbase (se 4 (by rfl) ⟨555600, by rfl⟩ : syracuseStep 5926405 = 1111201) (by norm_num)
theorem B2633269 : Blo 1559477 2633269 := bbase (se 5 (by rfl) ⟨123434, by rfl⟩ : syracuseStep 2633269 = 246869) (by norm_num)
theorem B3509837 : Blo 1559477 3509837 := bbase (se 3 (by rfl) ⟨658094, by rfl⟩ : syracuseStep 3509837 = 1316189) (by norm_num)
theorem B17780309 : Blo 1559477 17780309 := bbase (se 8 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 17780309 = 208363) (by norm_num)
theorem B3747421 : Blo 1559477 3747421 := bbase (se 3 (by rfl) ⟨702641, by rfl⟩ : syracuseStep 3747421 = 1405283) (by norm_num)
theorem B1666661 : Blo 1559477 1666661 := bbase (se 4 (by rfl) ⟨156249, by rfl⟩ : syracuseStep 1666661 = 312499) (by norm_num)
theorem B3952253 : Blo 1559477 3952253 := bbase (se 3 (by rfl) ⟨741047, by rfl⟩ : syracuseStep 3952253 = 1482095) (by norm_num)
theorem B2633357 : Blo 1559477 2633357 := bbase (se 3 (by rfl) ⟨493754, by rfl⟩ : syracuseStep 2633357 = 987509) (by norm_num)
theorem B3509909 : Blo 1559477 3509909 := bbase (se 6 (by rfl) ⟨82263, by rfl⟩ : syracuseStep 3509909 = 164527) (by norm_num)
theorem B5336725 : Blo 1559477 5336725 := bbase (se 6 (by rfl) ⟨125079, by rfl⟩ : syracuseStep 5336725 = 250159) (by norm_num)
theorem B3509981 : Blo 1559477 3509981 := bbase (se 3 (by rfl) ⟨658121, by rfl⟩ : syracuseStep 3509981 = 1316243) (by norm_num)
theorem B7900901 : Blo 1559477 7900901 := bbase (se 4 (by rfl) ⟨740709, by rfl⟩ : syracuseStep 7900901 = 1481419) (by norm_num)
theorem B4443893 : Blo 1559477 4443893 := bbase (se 5 (by rfl) ⟨208307, by rfl⟩ : syracuseStep 4443893 = 416615) (by norm_num)
theorem B2633485 : Blo 1559477 2633485 := bbase (se 3 (by rfl) ⟨493778, by rfl⟩ : syracuseStep 2633485 = 987557) (by norm_num)
theorem B3747613 : Blo 1559477 3747613 := bbase (se 3 (by rfl) ⟨702677, by rfl⟩ : syracuseStep 3747613 = 1405355) (by norm_num)
theorem B3510053 : Blo 1559477 3510053 := bbase (se 4 (by rfl) ⟨329067, by rfl⟩ : syracuseStep 3510053 = 658135) (by norm_num)
theorem B7499573 : Blo 1559477 7499573 := bbase (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) (by norm_num)
theorem B5926709 : Blo 1559477 5926709 := bbase (se 5 (by rfl) ⟨277814, by rfl⟩ : syracuseStep 5926709 = 555629) (by norm_num)
theorem B3747653 : Blo 1559477 3747653 := bbase (se 4 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 3747653 = 702685) (by norm_num)
theorem B2633573 : Blo 1559477 2633573 := bbase (se 4 (by rfl) ⟨246897, by rfl⟩ : syracuseStep 2633573 = 493795) (by norm_num)
theorem B3510125 : Blo 1559477 3510125 := bbase (se 3 (by rfl) ⟨658148, by rfl⟩ : syracuseStep 3510125 = 1316297) (by norm_num)
theorem B3559277 : Blo 1559477 3559277 := bbase (se 3 (by rfl) ⟨667364, by rfl⟩ : syracuseStep 3559277 = 1334729) (by norm_num)
theorem B3510197 : Blo 1559477 3510197 := bbase (se 5 (by rfl) ⟨164540, by rfl⟩ : syracuseStep 3510197 = 329081) (by norm_num)
theorem B2961373 : Blo 1559477 2961373 := bbase (se 3 (by rfl) ⟨555257, by rfl⟩ : syracuseStep 2961373 = 1110515) (by norm_num)
theorem B2002909 : Blo 1559477 2002909 := bbase (se 3 (by rfl) ⟨375545, by rfl⟩ : syracuseStep 2002909 = 751091) (by norm_num)
theorem B2633701 : Blo 1559477 2633701 := bbase (se 4 (by rfl) ⟨246909, by rfl⟩ : syracuseStep 2633701 = 493819) (by norm_num)
theorem B2002925 : Blo 1559477 2002925 := bbase (se 3 (by rfl) ⟨375548, by rfl⟩ : syracuseStep 2002925 = 751097) (by norm_num)
theorem B3510269 : Blo 1559477 3510269 := bbase (se 3 (by rfl) ⟨658175, by rfl⟩ : syracuseStep 3510269 = 1316351) (by norm_num)
theorem B2633789 : Blo 1559477 2633789 := bbase (se 3 (by rfl) ⟨493835, by rfl⟩ : syracuseStep 2633789 = 987671) (by norm_num)
theorem B3510341 : Blo 1559477 3510341 := bbase (se 4 (by rfl) ⟨329094, by rfl⟩ : syracuseStep 3510341 = 658189) (by norm_num)
theorem B3747941 : Blo 1559477 3747941 := bbase (se 4 (by rfl) ⟨351369, by rfl⟩ : syracuseStep 3747941 = 702739) (by norm_num)
theorem B2961517 : Blo 1559477 2961517 := bbase (se 3 (by rfl) ⟨555284, by rfl⟩ : syracuseStep 2961517 = 1110569) (by norm_num)
theorem B3510413 : Blo 1559477 3510413 := bbase (se 3 (by rfl) ⟨658202, by rfl⟩ : syracuseStep 3510413 = 1316405) (by norm_num)
theorem B5263541 : Blo 1559477 5263541 := bbase (se 5 (by rfl) ⟨246728, by rfl⟩ : syracuseStep 5263541 = 493457) (by norm_num)
theorem B2633917 : Blo 1559477 2633917 := bbase (se 3 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 2633917 = 987719) (by norm_num)
theorem B3510485 : Blo 1559477 3510485 := bbase (se 7 (by rfl) ⟨41138, by rfl⟩ : syracuseStep 3510485 = 82277) (by norm_num)
theorem B2961677 : Blo 1559477 2961677 := bbase (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) (by norm_num)
theorem B2634005 : Blo 1559477 2634005 := bbase (se 6 (by rfl) ⟨61734, by rfl⟩ : syracuseStep 2634005 = 123469) (by norm_num)
theorem B3510557 : Blo 1559477 3510557 := bbase (se 3 (by rfl) ⟨658229, by rfl⟩ : syracuseStep 3510557 = 1316459) (by norm_num)
theorem B1667413 : Blo 1559477 1667413 := bbase (se 10 (by rfl) ⟨2442, by rfl⟩ : syracuseStep 1667413 = 4885) (by norm_num)
theorem B3510629 : Blo 1559477 3510629 := bbase (se 4 (by rfl) ⟨329121, by rfl⟩ : syracuseStep 3510629 = 658243) (by norm_num)
theorem B2634133 : Blo 1559477 2634133 := bbase (se 6 (by rfl) ⟨61737, by rfl⟩ : syracuseStep 2634133 = 123475) (by norm_num)
theorem B3658133 : Blo 1559477 3658133 := bbase (se 6 (by rfl) ⟨85737, by rfl⟩ : syracuseStep 3658133 = 171475) (by norm_num)
theorem B2961821 : Blo 1559477 2961821 := bbase (se 3 (by rfl) ⟨555341, by rfl⟩ : syracuseStep 2961821 = 1110683) (by norm_num)
theorem B2339237 : Blo 1559477 2339237 := bbase (se 4 (by rfl) ⟨219303, by rfl⟩ : syracuseStep 2339237 = 438607) (by norm_num)
theorem B3510701 : Blo 1559477 3510701 := bbase (se 3 (by rfl) ⟨658256, by rfl⟩ : syracuseStep 3510701 = 1316513) (by norm_num)
theorem B2339261 : Blo 1559477 2339261 := bbase (se 3 (by rfl) ⟨438611, by rfl⟩ : syracuseStep 2339261 = 877223) (by norm_num)
theorem B2339285 : Blo 1559477 2339285 := bbase (se 7 (by rfl) ⟨27413, by rfl⟩ : syracuseStep 2339285 = 54827) (by norm_num)
theorem B4444645 : Blo 1559477 4444645 := bbase (se 4 (by rfl) ⟨416685, by rfl⟩ : syracuseStep 4444645 = 833371) (by norm_num)
theorem B2339309 : Blo 1559477 2339309 := bbase (se 3 (by rfl) ⟨438620, by rfl⟩ : syracuseStep 2339309 = 877241) (by norm_num)
theorem B2634221 : Blo 1559477 2634221 := bbase (se 3 (by rfl) ⟨493916, by rfl⟩ : syracuseStep 2634221 = 987833) (by norm_num)
theorem B3510773 : Blo 1559477 3510773 := bbase (se 5 (by rfl) ⟨164567, by rfl⟩ : syracuseStep 3510773 = 329135) (by norm_num)
theorem B2339333 : Blo 1559477 2339333 := bbase (se 4 (by rfl) ⟨219312, by rfl⟩ : syracuseStep 2339333 = 438625) (by norm_num)
theorem B2339357 : Blo 1559477 2339357 := bbase (se 3 (by rfl) ⟨438629, by rfl⟩ : syracuseStep 2339357 = 877259) (by norm_num)
theorem B2339381 : Blo 1559477 2339381 := bbase (se 5 (by rfl) ⟨109658, by rfl⟩ : syracuseStep 2339381 = 219317) (by norm_num)
theorem B13333045 : Blo 1559477 13333045 := bbase (se 5 (by rfl) ⟨624986, by rfl⟩ : syracuseStep 13333045 = 1249973) (by norm_num)
theorem B3510845 : Blo 1559477 3510845 := bbase (se 3 (by rfl) ⟨658283, by rfl⟩ : syracuseStep 3510845 = 1316567) (by norm_num)
theorem B2339405 : Blo 1559477 2339405 := bbase (se 3 (by rfl) ⟨438638, by rfl⟩ : syracuseStep 2339405 = 877277) (by norm_num)
theorem B2339429 : Blo 1559477 2339429 := bbase (se 4 (by rfl) ⟨219321, by rfl⟩ : syracuseStep 2339429 = 438643) (by norm_num)
theorem B5263973 : Blo 1559477 5263973 := bbase (se 4 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 5263973 = 986995) (by norm_num)
theorem B2634349 : Blo 1559477 2634349 := bbase (se 3 (by rfl) ⟨493940, by rfl⟩ : syracuseStep 2634349 = 987881) (by norm_num)
theorem B2339453 : Blo 1559477 2339453 := bbase (se 3 (by rfl) ⟨438647, by rfl⟩ : syracuseStep 2339453 = 877295) (by norm_num)
theorem B3510917 : Blo 1559477 3510917 := bbase (se 4 (by rfl) ⟨329148, by rfl⟩ : syracuseStep 3510917 = 658297) (by norm_num)
theorem B2339477 : Blo 1559477 2339477 := bbase (se 6 (by rfl) ⟨54831, by rfl⟩ : syracuseStep 2339477 = 109663) (by norm_num)
theorem B2372261 : Blo 1559477 2372261 := bbase (se 4 (by rfl) ⟨222399, by rfl⟩ : syracuseStep 2372261 = 444799) (by norm_num)
theorem B3330733 : Blo 1559477 3330733 := bbase (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) (by norm_num)
theorem B2339501 : Blo 1559477 2339501 := bbase (se 3 (by rfl) ⟨438656, by rfl⟩ : syracuseStep 2339501 = 877313) (by norm_num)
theorem B2962109 : Blo 1559477 2962109 := bbase (se 3 (by rfl) ⟨555395, by rfl⟩ : syracuseStep 2962109 = 1110791) (by norm_num)
theorem B2339525 : Blo 1559477 2339525 := bbase (se 4 (by rfl) ⟨219330, by rfl⟩ : syracuseStep 2339525 = 438661) (by norm_num)
theorem B2634437 : Blo 1559477 2634437 := bbase (se 4 (by rfl) ⟨246978, by rfl⟩ : syracuseStep 2634437 = 493957) (by norm_num)
theorem B3510989 : Blo 1559477 3510989 := bbase (se 3 (by rfl) ⟨658310, by rfl⟩ : syracuseStep 3510989 = 1316621) (by norm_num)
theorem B2339549 : Blo 1559477 2339549 := bbase (se 3 (by rfl) ⟨438665, by rfl⟩ : syracuseStep 2339549 = 877331) (by norm_num)
theorem B2339573 : Blo 1559477 2339573 := bbase (se 5 (by rfl) ⟨109667, by rfl⟩ : syracuseStep 2339573 = 219335) (by norm_num)
theorem B2339597 : Blo 1559477 2339597 := bbase (se 3 (by rfl) ⟨438674, by rfl⟩ : syracuseStep 2339597 = 877349) (by norm_num)
theorem B3511061 : Blo 1559477 3511061 := bbase (se 6 (by rfl) ⟨82290, by rfl⟩ : syracuseStep 3511061 = 164581) (by norm_num)
theorem B2339621 : Blo 1559477 2339621 := bbase (se 4 (by rfl) ⟨219339, by rfl⟩ : syracuseStep 2339621 = 438679) (by norm_num)
theorem B2339645 : Blo 1559477 2339645 := bbase (se 3 (by rfl) ⟨438683, by rfl⟩ : syracuseStep 2339645 = 877367) (by norm_num)
theorem B2634565 : Blo 1559477 2634565 := bbase (se 4 (by rfl) ⟨246990, by rfl⟩ : syracuseStep 2634565 = 493981) (by norm_num)
theorem B2339669 : Blo 1559477 2339669 := bbase (se 9 (by rfl) ⟨6854, by rfl⟩ : syracuseStep 2339669 = 13709) (by norm_num)
theorem B2962261 : Blo 1559477 2962261 := bbase (se 9 (by rfl) ⟨8678, by rfl⟩ : syracuseStep 2962261 = 17357) (by norm_num)
theorem B3511133 : Blo 1559477 3511133 := bbase (se 3 (by rfl) ⟨658337, by rfl⟩ : syracuseStep 3511133 = 1316675) (by norm_num)
theorem B2339693 : Blo 1559477 2339693 := bbase (se 3 (by rfl) ⟨438692, by rfl⟩ : syracuseStep 2339693 = 877385) (by norm_num)
theorem B2339717 : Blo 1559477 2339717 := bbase (se 4 (by rfl) ⟨219348, by rfl⟩ : syracuseStep 2339717 = 438697) (by norm_num)
theorem B2339741 : Blo 1559477 2339741 := bbase (se 3 (by rfl) ⟨438701, by rfl⟩ : syracuseStep 2339741 = 877403) (by norm_num)
theorem B2634653 : Blo 1559477 2634653 := bbase (se 3 (by rfl) ⟨493997, by rfl⟩ : syracuseStep 2634653 = 987995) (by norm_num)
theorem B3511205 : Blo 1559477 3511205 := bbase (se 4 (by rfl) ⟨329175, by rfl⟩ : syracuseStep 3511205 = 658351) (by norm_num)
theorem B2339765 : Blo 1559477 2339765 := bbase (se 5 (by rfl) ⟨109676, by rfl⟩ : syracuseStep 2339765 = 219353) (by norm_num)
theorem B15004597 : Blo 1559477 15004597 := bbase (se 5 (by rfl) ⟨703340, by rfl⟩ : syracuseStep 15004597 = 1406681) (by norm_num)
theorem B2339789 : Blo 1559477 2339789 := bbase (se 3 (by rfl) ⟨438710, by rfl⟩ : syracuseStep 2339789 = 877421) (by norm_num)
theorem B2339813 : Blo 1559477 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B3511277 : Blo 1559477 3511277 := bbase (se 3 (by rfl) ⟨658364, by rfl⟩ : syracuseStep 3511277 = 1316729) (by norm_num)
theorem B4215797 : Blo 1559477 4215797 := bbase (se 5 (by rfl) ⟨197615, by rfl⟩ : syracuseStep 4215797 = 395231) (by norm_num)
theorem B7902197 : Blo 1559477 7902197 := bbase (se 5 (by rfl) ⟨370415, by rfl⟩ : syracuseStep 7902197 = 740831) (by norm_num)
theorem B2339837 : Blo 1559477 2339837 := bbase (se 3 (by rfl) ⟨438719, by rfl⟩ : syracuseStep 2339837 = 877439) (by norm_num)
theorem B2667541 : Blo 1559477 2667541 := bbase (se 6 (by rfl) ⟨62520, by rfl⟩ : syracuseStep 2667541 = 125041) (by norm_num)
theorem B5264405 : Blo 1559477 5264405 := bbase (se 6 (by rfl) ⟨123384, by rfl⟩ : syracuseStep 5264405 = 246769) (by norm_num)
theorem B2339861 : Blo 1559477 2339861 := bbase (se 6 (by rfl) ⟨54840, by rfl⟩ : syracuseStep 2339861 = 109681) (by norm_num)
theorem B2634781 : Blo 1559477 2634781 := bbase (se 3 (by rfl) ⟨494021, by rfl⟩ : syracuseStep 2634781 = 988043) (by norm_num)
theorem B2339885 : Blo 1559477 2339885 := bbase (se 3 (by rfl) ⟨438728, by rfl⟩ : syracuseStep 2339885 = 877457) (by norm_num)
theorem B3511349 : Blo 1559477 3511349 := bbase (se 5 (by rfl) ⟨164594, by rfl⟩ : syracuseStep 3511349 = 329189) (by norm_num)
theorem B2339909 : Blo 1559477 2339909 := bbase (se 4 (by rfl) ⟨219366, by rfl⟩ : syracuseStep 2339909 = 438733) (by norm_num)
theorem B2339933 : Blo 1559477 2339933 := bbase (se 3 (by rfl) ⟨438737, by rfl⟩ : syracuseStep 2339933 = 877475) (by norm_num)
theorem B2339957 : Blo 1559477 2339957 := bbase (se 5 (by rfl) ⟨109685, by rfl⟩ : syracuseStep 2339957 = 219371) (by norm_num)
theorem B2634869 : Blo 1559477 2634869 := bbase (se 5 (by rfl) ⟨123509, by rfl⟩ : syracuseStep 2634869 = 247019) (by norm_num)
theorem B3511421 : Blo 1559477 3511421 := bbase (se 3 (by rfl) ⟨658391, by rfl⟩ : syracuseStep 3511421 = 1316783) (by norm_num)
theorem B2962565 : Blo 1559477 2962565 := bbase (se 4 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 2962565 = 555481) (by norm_num)
theorem B2339981 : Blo 1559477 2339981 := bbase (se 3 (by rfl) ⟨438746, by rfl⟩ : syracuseStep 2339981 = 877493) (by norm_num)
theorem B2340005 : Blo 1559477 2340005 := bbase (se 4 (by rfl) ⟨219375, by rfl⟩ : syracuseStep 2340005 = 438751) (by norm_num)
theorem B2340029 : Blo 1559477 2340029 := bbase (se 3 (by rfl) ⟨438755, by rfl⟩ : syracuseStep 2340029 = 877511) (by norm_num)
theorem B3511493 : Blo 1559477 3511493 := bbase (se 4 (by rfl) ⟨329202, by rfl⟩ : syracuseStep 3511493 = 658405) (by norm_num)
theorem B2340053 : Blo 1559477 2340053 := bbase (se 7 (by rfl) ⟨27422, by rfl⟩ : syracuseStep 2340053 = 54845) (by norm_num)
theorem B6665429 : Blo 1559477 6665429 := bbase (se 7 (by rfl) ⟨78110, by rfl⟩ : syracuseStep 6665429 = 156221) (by norm_num)
theorem B2340077 : Blo 1559477 2340077 := bbase (se 3 (by rfl) ⟨438764, by rfl⟩ : syracuseStep 2340077 = 877529) (by norm_num)
theorem B2340101 : Blo 1559477 2340101 := bbase (se 4 (by rfl) ⟨219384, by rfl⟩ : syracuseStep 2340101 = 438769) (by norm_num)
theorem B3511565 : Blo 1559477 3511565 := bbase (se 3 (by rfl) ⟨658418, by rfl⟩ : syracuseStep 3511565 = 1316837) (by norm_num)
theorem B2340125 : Blo 1559477 2340125 := bbase (se 3 (by rfl) ⟨438773, by rfl⟩ : syracuseStep 2340125 = 877547) (by norm_num)
theorem B2340149 : Blo 1559477 2340149 := bbase (se 5 (by rfl) ⟨109694, by rfl⟩ : syracuseStep 2340149 = 219389) (by norm_num)
theorem B2340173 : Blo 1559477 2340173 := bbase (se 3 (by rfl) ⟨438782, by rfl⟩ : syracuseStep 2340173 = 877565) (by norm_num)
theorem B3511637 : Blo 1559477 3511637 := bbase (se 14 (by rfl) ⟨321, by rfl⟩ : syracuseStep 3511637 = 643) (by norm_num)
theorem B2340197 : Blo 1559477 2340197 := bbase (se 4 (by rfl) ⟨219393, by rfl⟩ : syracuseStep 2340197 = 438787) (by norm_num)
theorem B2340221 : Blo 1559477 2340221 := bbase (se 3 (by rfl) ⟨438791, by rfl⟩ : syracuseStep 2340221 = 877583) (by norm_num)
theorem B2340245 : Blo 1559477 2340245 := bbase (se 6 (by rfl) ⟨54849, by rfl⟩ : syracuseStep 2340245 = 109699) (by norm_num)
theorem B3511709 : Blo 1559477 3511709 := bbase (se 3 (by rfl) ⟨658445, by rfl⟩ : syracuseStep 3511709 = 1316891) (by norm_num)
theorem B4216229 : Blo 1559477 4216229 := bbase (se 4 (by rfl) ⟨395271, by rfl⟩ : syracuseStep 4216229 = 790543) (by norm_num)
theorem B2340269 : Blo 1559477 2340269 := bbase (se 3 (by rfl) ⟨438800, by rfl⟩ : syracuseStep 2340269 = 877601) (by norm_num)
theorem B5264837 : Blo 1559477 5264837 := bbase (se 4 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 5264837 = 987157) (by norm_num)
theorem B2340293 : Blo 1559477 2340293 := bbase (se 4 (by rfl) ⟨219402, by rfl⟩ : syracuseStep 2340293 = 438805) (by norm_num)
theorem B2340317 : Blo 1559477 2340317 := bbase (se 3 (by rfl) ⟨438809, by rfl⟩ : syracuseStep 2340317 = 877619) (by norm_num)
theorem B3511781 : Blo 1559477 3511781 := bbase (se 4 (by rfl) ⟨329229, by rfl⟩ : syracuseStep 3511781 = 658459) (by norm_num)
theorem B2340341 : Blo 1559477 2340341 := bbase (se 5 (by rfl) ⟨109703, by rfl⟩ : syracuseStep 2340341 = 219407) (by norm_num)
theorem B3208693 : Blo 1559477 3208693 := bbase (se 5 (by rfl) ⟨150407, by rfl⟩ : syracuseStep 3208693 = 300815) (by norm_num)
theorem B2340365 : Blo 1559477 2340365 := bbase (se 3 (by rfl) ⟨438818, by rfl⟩ : syracuseStep 2340365 = 877637) (by norm_num)
theorem B3331621 : Blo 1559477 3331621 := bbase (se 4 (by rfl) ⟨312339, by rfl⟩ : syracuseStep 3331621 = 624679) (by norm_num)
theorem B2340389 : Blo 1559477 2340389 := bbase (se 4 (by rfl) ⟨219411, by rfl⟩ : syracuseStep 2340389 = 438823) (by norm_num)
theorem B3511853 : Blo 1559477 3511853 := bbase (se 3 (by rfl) ⟨658472, by rfl⟩ : syracuseStep 3511853 = 1316945) (by norm_num)
theorem B3798589 : Blo 1559477 3798589 := bbase (se 3 (by rfl) ⟨712235, by rfl⟩ : syracuseStep 3798589 = 1424471) (by norm_num)
theorem B2340413 : Blo 1559477 2340413 := bbase (se 3 (by rfl) ⟨438827, by rfl⟩ : syracuseStep 2340413 = 877655) (by norm_num)
theorem B2340437 : Blo 1559477 2340437 := bbase (se 8 (by rfl) ⟨13713, by rfl⟩ : syracuseStep 2340437 = 27427) (by norm_num)
theorem B2340461 : Blo 1559477 2340461 := bbase (se 3 (by rfl) ⟨438836, by rfl⟩ : syracuseStep 2340461 = 877673) (by norm_num)
theorem B3511925 : Blo 1559477 3511925 := bbase (se 5 (by rfl) ⟨164621, by rfl⟩ : syracuseStep 3511925 = 329243) (by norm_num)
theorem B2340485 : Blo 1559477 2340485 := bbase (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) (by norm_num)
theorem B2340509 : Blo 1559477 2340509 := bbase (se 3 (by rfl) ⟨438845, by rfl⟩ : syracuseStep 2340509 = 877691) (by norm_num)
theorem B2340533 : Blo 1559477 2340533 := bbase (se 5 (by rfl) ⟨109712, by rfl⟩ : syracuseStep 2340533 = 219425) (by norm_num)
theorem B3511997 : Blo 1559477 3511997 := bbase (se 3 (by rfl) ⟨658499, by rfl⟩ : syracuseStep 3511997 = 1316999) (by norm_num)
theorem B2340557 : Blo 1559477 2340557 := bbase (se 3 (by rfl) ⟨438854, by rfl⟩ : syracuseStep 2340557 = 877709) (by norm_num)
theorem B2340581 : Blo 1559477 2340581 := bbase (se 4 (by rfl) ⟨219429, by rfl⟩ : syracuseStep 2340581 = 438859) (by norm_num)
theorem B2340605 : Blo 1559477 2340605 := bbase (se 3 (by rfl) ⟨438863, by rfl⟩ : syracuseStep 2340605 = 877727) (by norm_num)
theorem B3512069 : Blo 1559477 3512069 := bbase (se 4 (by rfl) ⟨329256, by rfl⟩ : syracuseStep 3512069 = 658513) (by norm_num)
theorem B2340629 : Blo 1559477 2340629 := bbase (se 6 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 2340629 = 109717) (by norm_num)
theorem B2340653 : Blo 1559477 2340653 := bbase (se 3 (by rfl) ⟨438872, by rfl⟩ : syracuseStep 2340653 = 877745) (by norm_num)
theorem B4331317 : Blo 1559477 4331317 := bbase (se 5 (by rfl) ⟨203030, by rfl⟩ : syracuseStep 4331317 = 406061) (by norm_num)
theorem B3798845 : Blo 1559477 3798845 := bbase (se 3 (by rfl) ⟨712283, by rfl⟩ : syracuseStep 3798845 = 1424567) (by norm_num)
theorem B2340677 : Blo 1559477 2340677 := bbase (se 4 (by rfl) ⟨219438, by rfl⟩ : syracuseStep 2340677 = 438877) (by norm_num)
theorem B3512141 : Blo 1559477 3512141 := bbase (se 3 (by rfl) ⟨658526, by rfl⟩ : syracuseStep 3512141 = 1317053) (by norm_num)
theorem B2340701 : Blo 1559477 2340701 := bbase (se 3 (by rfl) ⟨438881, by rfl⟩ : syracuseStep 2340701 = 877763) (by norm_num)
theorem B4003685 : Blo 1559477 4003685 := bbase (se 4 (by rfl) ⟨375345, by rfl⟩ : syracuseStep 4003685 = 750691) (by norm_num)
theorem B5265269 : Blo 1559477 5265269 := bbase (se 5 (by rfl) ⟨246809, by rfl⟩ : syracuseStep 5265269 = 493619) (by norm_num)
theorem B2340725 : Blo 1559477 2340725 := bbase (se 5 (by rfl) ⟨109721, by rfl⟩ : syracuseStep 2340725 = 219443) (by norm_num)
theorem B2963317 : Blo 1559477 2963317 := bbase (se 5 (by rfl) ⟨138905, by rfl⟩ : syracuseStep 2963317 = 277811) (by norm_num)
theorem B2340749 : Blo 1559477 2340749 := bbase (se 3 (by rfl) ⟨438890, by rfl⟩ : syracuseStep 2340749 = 877781) (by norm_num)
theorem B2930573 : Blo 1559477 2930573 := bbase (se 3 (by rfl) ⟨549482, by rfl⟩ : syracuseStep 2930573 = 1098965) (by norm_num)
theorem B3512213 : Blo 1559477 3512213 := bbase (se 6 (by rfl) ⟨82317, by rfl⟩ : syracuseStep 3512213 = 164635) (by norm_num)
theorem B2340773 : Blo 1559477 2340773 := bbase (se 4 (by rfl) ⟨219447, by rfl⟩ : syracuseStep 2340773 = 438895) (by norm_num)
theorem B11245493 : Blo 1559477 11245493 := bbase (se 5 (by rfl) ⟨527132, by rfl⟩ : syracuseStep 11245493 = 1054265) (by norm_num)
theorem B2340797 : Blo 1559477 2340797 := bbase (se 3 (by rfl) ⟨438899, by rfl⟩ : syracuseStep 2340797 = 877799) (by norm_num)
theorem B4503509 : Blo 1559477 4503509 := bbase (se 7 (by rfl) ⟨52775, by rfl⟩ : syracuseStep 4503509 = 105551) (by norm_num)
theorem B2340821 : Blo 1559477 2340821 := bbase (se 7 (by rfl) ⟨27431, by rfl⟩ : syracuseStep 2340821 = 54863) (by norm_num)
theorem B6330325 : Blo 1559477 6330325 := bbase (se 7 (by rfl) ⟨74183, by rfl⟩ : syracuseStep 6330325 = 148367) (by norm_num)
theorem B3512285 : Blo 1559477 3512285 := bbase (se 3 (by rfl) ⟨658553, by rfl⟩ : syracuseStep 3512285 = 1317107) (by norm_num)
theorem B2340845 : Blo 1559477 2340845 := bbase (se 3 (by rfl) ⟨438908, by rfl⟩ : syracuseStep 2340845 = 877817) (by norm_num)
theorem B2340869 : Blo 1559477 2340869 := bbase (se 4 (by rfl) ⟨219456, by rfl⟩ : syracuseStep 2340869 = 438913) (by norm_num)
theorem B2963461 : Blo 1559477 2963461 := bbase (se 4 (by rfl) ⟨277824, by rfl⟩ : syracuseStep 2963461 = 555649) (by norm_num)
theorem B3332117 : Blo 1559477 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B2340893 : Blo 1559477 2340893 := bbase (se 3 (by rfl) ⟨438917, by rfl⟩ : syracuseStep 2340893 = 877835) (by norm_num)
theorem B3512357 : Blo 1559477 3512357 := bbase (se 4 (by rfl) ⟨329283, by rfl⟩ : syracuseStep 3512357 = 658567) (by norm_num)
theorem B2340917 : Blo 1559477 2340917 := bbase (se 5 (by rfl) ⟨109730, by rfl⟩ : syracuseStep 2340917 = 219461) (by norm_num)
theorem B5339189 : Blo 1559477 5339189 := bbase (se 5 (by rfl) ⟨250274, by rfl⟩ : syracuseStep 5339189 = 500549) (by norm_num)
theorem B2340941 : Blo 1559477 2340941 := bbase (se 3 (by rfl) ⟨438926, by rfl⟩ : syracuseStep 2340941 = 877853) (by norm_num)
theorem B2340965 : Blo 1559477 2340965 := bbase (se 4 (by rfl) ⟨219465, by rfl⟩ : syracuseStep 2340965 = 438931) (by norm_num)
theorem B3512429 : Blo 1559477 3512429 := bbase (se 3 (by rfl) ⟨658580, by rfl⟩ : syracuseStep 3512429 = 1317161) (by norm_num)
theorem B2250877 : Blo 1559477 2250877 := bbase (se 3 (by rfl) ⟨422039, by rfl⟩ : syracuseStep 2250877 = 844079) (by norm_num)
theorem B2340989 : Blo 1559477 2340989 := bbase (se 3 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 2340989 = 877871) (by norm_num)
theorem B2341013 : Blo 1559477 2341013 := bbase (se 6 (by rfl) ⟨54867, by rfl⟩ : syracuseStep 2341013 = 109735) (by norm_num)
theorem B2963621 : Blo 1559477 2963621 := bbase (se 4 (by rfl) ⟨277839, by rfl⟩ : syracuseStep 2963621 = 555679) (by norm_num)
theorem B2341037 : Blo 1559477 2341037 := bbase (se 3 (by rfl) ⟨438944, by rfl⟩ : syracuseStep 2341037 = 877889) (by norm_num)
theorem B6666421 : Blo 1559477 6666421 := bbase (se 5 (by rfl) ⟨312488, by rfl⟩ : syracuseStep 6666421 = 624977) (by norm_num)
theorem B3512501 : Blo 1559477 3512501 := bbase (se 5 (by rfl) ⟨164648, by rfl⟩ : syracuseStep 3512501 = 329297) (by norm_num)
theorem B2341061 : Blo 1559477 2341061 := bbase (se 4 (by rfl) ⟨219474, by rfl⟩ : syracuseStep 2341061 = 438949) (by norm_num)
theorem B2341085 : Blo 1559477 2341085 := bbase (se 3 (by rfl) ⟨438953, by rfl⟩ : syracuseStep 2341085 = 877907) (by norm_num)
theorem B2341109 : Blo 1559477 2341109 := bbase (se 5 (by rfl) ⟨109739, by rfl⟩ : syracuseStep 2341109 = 219479) (by norm_num)
theorem B3512573 : Blo 1559477 3512573 := bbase (se 3 (by rfl) ⟨658607, by rfl⟩ : syracuseStep 3512573 = 1317215) (by norm_num)
theorem B7903493 : Blo 1559477 7903493 := bbase (se 4 (by rfl) ⟨740952, by rfl⟩ : syracuseStep 7903493 = 1481905) (by norm_num)
theorem B2341133 : Blo 1559477 2341133 := bbase (se 3 (by rfl) ⟨438962, by rfl⟩ : syracuseStep 2341133 = 877925) (by norm_num)
theorem B5265701 : Blo 1559477 5265701 := bbase (se 4 (by rfl) ⟨493659, by rfl⟩ : syracuseStep 5265701 = 987319) (by norm_num)
theorem B2341157 : Blo 1559477 2341157 := bbase (se 4 (by rfl) ⟨219483, by rfl⟩ : syracuseStep 2341157 = 438967) (by norm_num)
theorem B1874225 : Blo 1559477 1874225 := bbase (se 2 (by rfl) ⟨702834, by rfl⟩ : syracuseStep 1874225 = 1405669) (by norm_num)
theorem B2963765 : Blo 1559477 2963765 := bbase (se 5 (by rfl) ⟨138926, by rfl⟩ : syracuseStep 2963765 = 277853) (by norm_num)
theorem B2341181 : Blo 1559477 2341181 := bbase (se 3 (by rfl) ⟨438971, by rfl⟩ : syracuseStep 2341181 = 877943) (by norm_num)
theorem B3512645 : Blo 1559477 3512645 := bbase (se 4 (by rfl) ⟨329310, by rfl⟩ : syracuseStep 3512645 = 658621) (by norm_num)
theorem B2341205 : Blo 1559477 2341205 := bbase (se 10 (by rfl) ⟨3429, by rfl⟩ : syracuseStep 2341205 = 6859) (by norm_num)
theorem B2341229 : Blo 1559477 2341229 := bbase (se 3 (by rfl) ⟨438980, by rfl⟩ : syracuseStep 2341229 = 877961) (by norm_num)
theorem B2341253 : Blo 1559477 2341253 := bbase (se 4 (by rfl) ⟨219492, by rfl⟩ : syracuseStep 2341253 = 438985) (by norm_num)
theorem B3512717 : Blo 1559477 3512717 := bbase (se 3 (by rfl) ⟨658634, by rfl⟩ : syracuseStep 3512717 = 1317269) (by norm_num)
theorem B2341277 : Blo 1559477 2341277 := bbase (se 3 (by rfl) ⟨438989, by rfl⟩ : syracuseStep 2341277 = 877979) (by norm_num)
theorem B5339573 : Blo 1559477 5339573 := bbase (se 5 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 5339573 = 500585) (by norm_num)
theorem B2341301 : Blo 1559477 2341301 := bbase (se 5 (by rfl) ⟨109748, by rfl⟩ : syracuseStep 2341301 = 219497) (by norm_num)
theorem B2341325 : Blo 1559477 2341325 := bbase (se 3 (by rfl) ⟨438998, by rfl⟩ : syracuseStep 2341325 = 877997) (by norm_num)
theorem B3512789 : Blo 1559477 3512789 := bbase (se 7 (by rfl) ⟨41165, by rfl⟩ : syracuseStep 3512789 = 82331) (by norm_num)
theorem B2669021 : Blo 1559477 2669021 := bbase (se 3 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 2669021 = 1000883) (by norm_num)
theorem B2341349 : Blo 1559477 2341349 := bbase (se 4 (by rfl) ⟨219501, by rfl⟩ : syracuseStep 2341349 = 439003) (by norm_num)
theorem B13335029 : Blo 1559477 13335029 := bbase (se 5 (by rfl) ⟨625079, by rfl⟩ : syracuseStep 13335029 = 1250159) (by norm_num)
theorem B2341373 : Blo 1559477 2341373 := bbase (se 3 (by rfl) ⟨439007, by rfl⟩ : syracuseStep 2341373 = 878015) (by norm_num)
theorem B2849293 : Blo 1559477 2849293 := bbase (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) (by norm_num)
theorem B2341397 : Blo 1559477 2341397 := bbase (se 6 (by rfl) ⟨54876, by rfl⟩ : syracuseStep 2341397 = 109753) (by norm_num)
theorem B3512861 : Blo 1559477 3512861 := bbase (se 3 (by rfl) ⟨658661, by rfl⟩ : syracuseStep 3512861 = 1317323) (by norm_num)
theorem B2341421 : Blo 1559477 2341421 := bbase (se 3 (by rfl) ⟨439016, by rfl⟩ : syracuseStep 2341421 = 878033) (by norm_num)
theorem B5921333 : Blo 1559477 5921333 := bbase (se 5 (by rfl) ⟨277562, by rfl⟩ : syracuseStep 5921333 = 555125) (by norm_num)
theorem B2341445 : Blo 1559477 2341445 := bbase (se 4 (by rfl) ⟨219510, by rfl⟩ : syracuseStep 2341445 = 439021) (by norm_num)
theorem B2964053 : Blo 1559477 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B2341469 : Blo 1559477 2341469 := bbase (se 3 (by rfl) ⟨439025, by rfl⟩ : syracuseStep 2341469 = 878051) (by norm_num)
theorem B8010341 : Blo 1559477 8010341 := bbase (se 4 (by rfl) ⟨750969, by rfl⟩ : syracuseStep 8010341 = 1501939) (by norm_num)
theorem B3512933 : Blo 1559477 3512933 := bbase (se 4 (by rfl) ⟨329337, by rfl⟩ : syracuseStep 3512933 = 658675) (by norm_num)
theorem B2341493 : Blo 1559477 2341493 := bbase (se 5 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 2341493 = 219515) (by norm_num)
theorem B7502453 : Blo 1559477 7502453 := bbase (se 5 (by rfl) ⟨351677, by rfl⟩ : syracuseStep 7502453 = 703355) (by norm_num)
theorem B2341517 : Blo 1559477 2341517 := bbase (se 3 (by rfl) ⟨439034, by rfl⟩ : syracuseStep 2341517 = 878069) (by norm_num)
theorem B1899173 : Blo 1559477 1899173 := bbase (se 4 (by rfl) ⟨178047, by rfl⟩ : syracuseStep 1899173 = 356095) (by norm_num)
theorem B7895717 : Blo 1559477 7895717 := bbase (se 4 (by rfl) ⟨740223, by rfl⟩ : syracuseStep 7895717 = 1480447) (by norm_num)
theorem B2341541 : Blo 1559477 2341541 := bbase (se 4 (by rfl) ⟨219519, by rfl⟩ : syracuseStep 2341541 = 439039) (by norm_num)
theorem B2136749 : Blo 1559477 2136749 := bbase (se 3 (by rfl) ⟨400640, by rfl⟩ : syracuseStep 2136749 = 801281) (by norm_num)
theorem B3513005 : Blo 1559477 3513005 := bbase (se 3 (by rfl) ⟨658688, by rfl⟩ : syracuseStep 3513005 = 1317377) (by norm_num)
theorem B2341565 : Blo 1559477 2341565 := bbase (se 3 (by rfl) ⟨439043, by rfl⟩ : syracuseStep 2341565 = 878087) (by norm_num)
theorem B2251477 : Blo 1559477 2251477 := bbase (se 7 (by rfl) ⟨26384, by rfl⟩ : syracuseStep 2251477 = 52769) (by norm_num)
theorem B5266133 : Blo 1559477 5266133 := bbase (se 7 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 5266133 = 123425) (by norm_num)
theorem B2341589 : Blo 1559477 2341589 := bbase (se 7 (by rfl) ⟨27440, by rfl⟩ : syracuseStep 2341589 = 54881) (by norm_num)
theorem B5626597 : Blo 1559477 5626597 := bbase (se 4 (by rfl) ⟨527493, by rfl⟩ : syracuseStep 5626597 = 1054987) (by norm_num)
theorem B2341613 : Blo 1559477 2341613 := bbase (se 3 (by rfl) ⟨439052, by rfl⟩ : syracuseStep 2341613 = 878105) (by norm_num)
theorem B2964205 : Blo 1559477 2964205 := bbase (se 3 (by rfl) ⟨555788, by rfl⟩ : syracuseStep 2964205 = 1111577) (by norm_num)
theorem B3513077 : Blo 1559477 3513077 := bbase (se 5 (by rfl) ⟨164675, by rfl⟩ : syracuseStep 3513077 = 329351) (by norm_num)
theorem B2341637 : Blo 1559477 2341637 := bbase (se 4 (by rfl) ⟨219528, by rfl⟩ : syracuseStep 2341637 = 439057) (by norm_num)
theorem B1874701 : Blo 1559477 1874701 := bbase (se 3 (by rfl) ⟨351506, by rfl⟩ : syracuseStep 1874701 = 703013) (by norm_num)
theorem B4217621 : Blo 1559477 4217621 := bbase (se 6 (by rfl) ⟨98850, by rfl⟩ : syracuseStep 4217621 = 197701) (by norm_num)
theorem B2341661 : Blo 1559477 2341661 := bbase (se 3 (by rfl) ⟨439061, by rfl⟩ : syracuseStep 2341661 = 878123) (by norm_num)
theorem B1874729 : Blo 1559477 1874729 := bbase (se 2 (by rfl) ⟨703023, by rfl⟩ : syracuseStep 1874729 = 1406047) (by norm_num)
theorem B12008245 : Blo 1559477 12008245 := bbase (se 5 (by rfl) ⟨562886, by rfl⟩ : syracuseStep 12008245 = 1125773) (by norm_num)
theorem B2341685 : Blo 1559477 2341685 := bbase (se 5 (by rfl) ⟨109766, by rfl⟩ : syracuseStep 2341685 = 219533) (by norm_num)
theorem B3513149 : Blo 1559477 3513149 := bbase (se 3 (by rfl) ⟨658715, by rfl⟩ : syracuseStep 3513149 = 1317431) (by norm_num)
theorem B2341709 : Blo 1559477 2341709 := bbase (se 3 (by rfl) ⟨439070, by rfl⟩ : syracuseStep 2341709 = 878141) (by norm_num)
theorem B20003669 : Blo 1559477 20003669 := bbase (se 9 (by rfl) ⟨58604, by rfl⟩ : syracuseStep 20003669 = 117209) (by norm_num)
theorem B2341733 : Blo 1559477 2341733 := bbase (se 4 (by rfl) ⟨219537, by rfl⟩ : syracuseStep 2341733 = 439075) (by norm_num)
theorem B3332981 : Blo 1559477 3332981 := bbase (se 5 (by rfl) ⟨156233, by rfl⟩ : syracuseStep 3332981 = 312467) (by norm_num)
theorem B2341757 : Blo 1559477 2341757 := bbase (se 3 (by rfl) ⟨439079, by rfl⟩ : syracuseStep 2341757 = 878159) (by norm_num)
theorem B3513221 : Blo 1559477 3513221 := bbase (se 4 (by rfl) ⟨329364, by rfl⟩ : syracuseStep 3513221 = 658729) (by norm_num)
theorem B2341781 : Blo 1559477 2341781 := bbase (se 6 (by rfl) ⟨54885, by rfl⟩ : syracuseStep 2341781 = 109771) (by norm_num)
theorem B2341805 : Blo 1559477 2341805 := bbase (se 3 (by rfl) ⟨439088, by rfl⟩ : syracuseStep 2341805 = 878177) (by norm_num)
theorem B4275125 : Blo 1559477 4275125 := bbase (se 5 (by rfl) ⟨200396, by rfl⟩ : syracuseStep 4275125 = 400793) (by norm_num)
theorem B2341829 : Blo 1559477 2341829 := bbase (se 4 (by rfl) ⟨219546, by rfl⟩ : syracuseStep 2341829 = 439093) (by norm_num)
theorem B3513293 : Blo 1559477 3513293 := bbase (se 3 (by rfl) ⟨658742, by rfl⟩ : syracuseStep 3513293 = 1317485) (by norm_num)
theorem B2341853 : Blo 1559477 2341853 := bbase (se 3 (by rfl) ⟨439097, by rfl⟩ : syracuseStep 2341853 = 878195) (by norm_num)
theorem B1874917 : Blo 1559477 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B2341877 : Blo 1559477 2341877 := bbase (se 5 (by rfl) ⟨109775, by rfl⟩ : syracuseStep 2341877 = 219551) (by norm_num)
theorem B3947525 : Blo 1559477 3947525 := bbase (se 4 (by rfl) ⟨370080, by rfl⟩ : syracuseStep 3947525 = 740161) (by norm_num)
theorem B3333125 : Blo 1559477 3333125 := bbase (se 4 (by rfl) ⟨312480, by rfl⟩ : syracuseStep 3333125 = 624961) (by norm_num)
theorem B2341901 : Blo 1559477 2341901 := bbase (se 3 (by rfl) ⟨439106, by rfl⟩ : syracuseStep 2341901 = 878213) (by norm_num)
theorem B30063637 : Blo 1559477 30063637 := bbase (se 6 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 30063637 = 1409233) (by norm_num)
theorem B2341925 : Blo 1559477 2341925 := bbase (se 4 (by rfl) ⟨219555, by rfl⟩ : syracuseStep 2341925 = 439111) (by norm_num)
theorem B2341949 : Blo 1559477 2341949 := bbase (se 3 (by rfl) ⟨439115, by rfl⟩ : syracuseStep 2341949 = 878231) (by norm_num)
theorem B2341973 : Blo 1559477 2341973 := bbase (se 8 (by rfl) ⟨13722, by rfl⟩ : syracuseStep 2341973 = 27445) (by norm_num)
theorem B1875037 : Blo 1559477 1875037 := bbase (se 3 (by rfl) ⟨351569, by rfl⟩ : syracuseStep 1875037 = 703139) (by norm_num)
theorem B2341997 : Blo 1559477 2341997 := bbase (se 3 (by rfl) ⟨439124, by rfl⟩ : syracuseStep 2341997 = 878249) (by norm_num)
theorem B5266565 : Blo 1559477 5266565 := bbase (se 4 (by rfl) ⟨493740, by rfl⟩ : syracuseStep 5266565 = 987481) (by norm_num)
theorem B2342021 : Blo 1559477 2342021 := bbase (se 4 (by rfl) ⟨219564, by rfl⟩ : syracuseStep 2342021 = 439129) (by norm_num)
theorem B2342045 : Blo 1559477 2342045 := bbase (se 3 (by rfl) ⟨439133, by rfl⟩ : syracuseStep 2342045 = 878267) (by norm_num)
theorem B2342069 : Blo 1559477 2342069 := bbase (se 5 (by rfl) ⟨109784, by rfl⟩ : syracuseStep 2342069 = 219569) (by norm_num)
theorem B3947717 : Blo 1559477 3947717 := bbase (se 4 (by rfl) ⟨370098, by rfl⟩ : syracuseStep 3947717 = 740197) (by norm_num)
theorem B2342093 : Blo 1559477 2342093 := bbase (se 3 (by rfl) ⟨439142, by rfl⟩ : syracuseStep 2342093 = 878285) (by norm_num)
theorem B2342117 : Blo 1559477 2342117 := bbase (se 4 (by rfl) ⟨219573, by rfl⟩ : syracuseStep 2342117 = 439147) (by norm_num)
theorem B2342141 : Blo 1559477 2342141 := bbase (se 3 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 2342141 = 878303) (by norm_num)
theorem B2342165 : Blo 1559477 2342165 := bbase (se 6 (by rfl) ⟨54894, by rfl⟩ : syracuseStep 2342165 = 109789) (by norm_num)
theorem B2342189 : Blo 1559477 2342189 := bbase (se 3 (by rfl) ⟨439160, by rfl⟩ : syracuseStep 2342189 = 878321) (by norm_num)
theorem B2342213 : Blo 1559477 2342213 := bbase (se 4 (by rfl) ⟨219582, by rfl⟩ : syracuseStep 2342213 = 439165) (by norm_num)
theorem B1973737 : Blo 1559477 1973737 := bbase (se 2 (by rfl) ⟨740151, by rfl⟩ : syracuseStep 1973737 = 1480303) (by norm_num)
theorem B4505077 : Blo 1559477 4505077 := bbase (se 5 (by rfl) ⟨211175, by rfl⟩ : syracuseStep 4505077 = 422351) (by norm_num)
theorem B7904789 : Blo 1559477 7904789 := bbase (se 6 (by rfl) ⟨185268, by rfl⟩ : syracuseStep 7904789 = 370537) (by norm_num)
theorem B3948061 : Blo 1559477 3948061 := bbase (se 3 (by rfl) ⟨740261, by rfl⟩ : syracuseStep 3948061 = 1480523) (by norm_num)
theorem B5266997 : Blo 1559477 5266997 := bbase (se 5 (by rfl) ⟨246890, by rfl⟩ : syracuseStep 5266997 = 493781) (by norm_num)
theorem B3751525 : Blo 1559477 3751525 := bbase (se 4 (by rfl) ⟨351705, by rfl⟩ : syracuseStep 3751525 = 703411) (by norm_num)
theorem B4996741 : Blo 1559477 4996741 := bbase (se 4 (by rfl) ⟨468444, by rfl⟩ : syracuseStep 4996741 = 936889) (by norm_num)
theorem B3948173 : Blo 1559477 3948173 := bbase (se 3 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 3948173 = 1480565) (by norm_num)
theorem B1973909 : Blo 1559477 1973909 := bbase (se 6 (by rfl) ⟨46263, by rfl⟩ : syracuseStep 1973909 = 92527) (by norm_num)
theorem B1973965 : Blo 1559477 1973965 := bbase (se 3 (by rfl) ⟨370118, by rfl⟩ : syracuseStep 1973965 = 740237) (by norm_num)
theorem B5922517 : Blo 1559477 5922517 := bbase (se 7 (by rfl) ⟨69404, by rfl⟩ : syracuseStep 5922517 = 138809) (by norm_num)
theorem B3333869 : Blo 1559477 3333869 := bbase (se 3 (by rfl) ⟨625100, by rfl⟩ : syracuseStep 3333869 = 1250201) (by norm_num)
theorem B1974061 : Blo 1559477 1974061 := bbase (se 3 (by rfl) ⟨370136, by rfl⟩ : syracuseStep 1974061 = 740273) (by norm_num)
theorem B4742965 : Blo 1559477 4742965 := bbase (se 5 (by rfl) ⟨222326, by rfl⟩ : syracuseStep 4742965 = 444653) (by norm_num)
theorem B3948365 : Blo 1559477 3948365 := bbase (se 3 (by rfl) ⟨740318, by rfl⟩ : syracuseStep 3948365 = 1480637) (by norm_num)
theorem B32481109 : Blo 1559477 32481109 := bbase (se 9 (by rfl) ⟨95159, by rfl⟩ : syracuseStep 32481109 = 190319) (by norm_num)
theorem B7897013 : Blo 1559477 7897013 := bbase (se 5 (by rfl) ⟨370172, by rfl⟩ : syracuseStep 7897013 = 740345) (by norm_num)
theorem B1974233 : Blo 1559477 1974233 := bbase (se 2 (by rfl) ⟨740337, by rfl⟩ : syracuseStep 1974233 = 1480675) (by norm_num)
theorem B5267429 : Blo 1559477 5267429 := bbase (se 4 (by rfl) ⟨493821, by rfl⟩ : syracuseStep 5267429 = 987643) (by norm_num)
theorem B7495669 : Blo 1559477 7495669 := bbase (se 5 (by rfl) ⟨351359, by rfl⟩ : syracuseStep 7495669 = 702719) (by norm_num)
theorem B3948547 : Blo 1559477 3948547 := bstep (se 1 (by rfl) ⟨2961410, by rfl⟩ : syracuseStep 3948547 = 5922821) B5922821
theorem B2498627 : Blo 1559477 2498627 := bstep (se 1 (by rfl) ⟨1873970, by rfl⟩ : syracuseStep 2498627 = 3747941) B3747941
theorem B5267537 : Blo 1559477 5267537 := bstep (se 2 (by rfl) ⟨1975326, by rfl⟩ : syracuseStep 5267537 = 3950653) B3950653
theorem B3948689 : Blo 1559477 3948689 := bstep (se 2 (by rfl) ⟨1480758, by rfl⟩ : syracuseStep 3948689 = 2961517) B2961517
theorem B3334321 : Blo 1559477 3334321 := bstep (se 2 (by rfl) ⟨1250370, by rfl⟩ : syracuseStep 3334321 = 2500741) B2500741
theorem B1974451 : Blo 1559477 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B17768645 : Blo 1559477 17768645 := bstep (se 4 (by rfl) ⟨1665810, by rfl⟩ : syracuseStep 17768645 = 3331621) B3331621
theorem B8888561 : Blo 1559477 8888561 := bstep (se 2 (by rfl) ⟨3333210, by rfl⟩ : syracuseStep 8888561 = 6666421) B6666421
theorem B1974547 : Blo 1559477 1974547 := bstep (se 1 (by rfl) ⟨1480910, by rfl⟩ : syracuseStep 1974547 = 2961821) B2961821
theorem B36036917 : Blo 1559477 36036917 := bstep (se 5 (by rfl) ⟨1689230, by rfl⟩ : syracuseStep 36036917 = 3378461) B3378461
theorem B5923277 : Blo 1559477 5923277 := bstep (se 3 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 5923277 = 2221229) B2221229
theorem B2220529 : Blo 1559477 2220529 := bstep (se 2 (by rfl) ⟨832698, by rfl⟩ : syracuseStep 2220529 = 1665397) B1665397
theorem B2220625 : Blo 1559477 2220625 := bstep (se 2 (by rfl) ⟨832734, by rfl⟩ : syracuseStep 2220625 = 1665469) B1665469
theorem B5268077 : Blo 1559477 5268077 := bstep (se 3 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 5268077 = 1975529) B1975529
theorem B2810531 : Blo 1559477 2810531 := bstep (se 1 (by rfl) ⟨2107898, by rfl⟩ : syracuseStep 2810531 = 4215797) B4215797
theorem B5268131 : Blo 1559477 5268131 := bstep (se 1 (by rfl) ⟨3951098, by rfl⟩ : syracuseStep 5268131 = 7902197) B7902197
theorem B10683085 : Blo 1559477 10683085 := bstep (se 3 (by rfl) ⟨2003078, by rfl⟩ : syracuseStep 10683085 = 4006157) B4006157
theorem B17777393 : Blo 1559477 17777393 := bstep (se 2 (by rfl) ⟨6666522, by rfl⟩ : syracuseStep 17777393 = 13333045) B13333045
theorem B1975043 : Blo 1559477 1975043 := bstep (se 1 (by rfl) ⟨1481282, by rfl⟩ : syracuseStep 1975043 = 2962565) B2962565
theorem B4997933 : Blo 1559477 4997933 := bstep (se 3 (by rfl) ⟨937112, by rfl⟩ : syracuseStep 4997933 = 1874225) B1874225
theorem B4219697 : Blo 1559477 4219697 := bstep (se 2 (by rfl) ⟨1582386, by rfl⟩ : syracuseStep 4219697 = 3164773) B3164773
theorem B6669155 : Blo 1559477 6669155 := bstep (se 1 (by rfl) ⟨5001866, by rfl⟩ : syracuseStep 6669155 = 10003733) B10003733
theorem B4440977 : Blo 1559477 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B5268401 : Blo 1559477 5268401 := bstep (se 2 (by rfl) ⟨1975650, by rfl⟩ : syracuseStep 5268401 = 3951301) B3951301
theorem B2810819 : Blo 1559477 2810819 := bstep (se 1 (by rfl) ⟨2108114, by rfl⟩ : syracuseStep 2810819 = 4216229) B4216229
theorem B4744145 : Blo 1559477 4744145 := bstep (se 2 (by rfl) ⟨1779054, by rfl⟩ : syracuseStep 4744145 = 3558109) B3558109
theorem B2499601 : Blo 1559477 2499601 := bstep (se 2 (by rfl) ⟨937350, by rfl⟩ : syracuseStep 2499601 = 1874701) B1874701
theorem B7898147 : Blo 1559477 7898147 := bstep (se 1 (by rfl) ⟨5923610, by rfl⟩ : syracuseStep 7898147 = 11847221) B11847221
theorem B2221121 : Blo 1559477 2221121 := bstep (se 2 (by rfl) ⟨832920, by rfl⟩ : syracuseStep 2221121 = 1665841) B1665841
theorem B3949681 : Blo 1559477 3949681 := bstep (se 2 (by rfl) ⟨1481130, by rfl⟩ : syracuseStep 3949681 = 2962261) B2962261
theorem B2532563 : Blo 1559477 2532563 := bstep (se 1 (by rfl) ⟨1899422, by rfl⟩ : syracuseStep 2532563 = 3798845) B3798845
theorem B20006129 : Blo 1559477 20006129 := bstep (se 2 (by rfl) ⟨7502298, by rfl⟩ : syracuseStep 20006129 = 15004597) B15004597
theorem B7496995 : Blo 1559477 7496995 := bstep (se 1 (by rfl) ⟨5622746, by rfl⟩ : syracuseStep 7496995 = 11245493) B11245493
theorem B1754419 : Blo 1559477 1754419 := bstep (se 1 (by rfl) ⟨1315814, by rfl⟩ : syracuseStep 1754419 = 2631629) B2631629
theorem B3556721 : Blo 1559477 3556721 := bstep (se 2 (by rfl) ⟨1333770, by rfl⟩ : syracuseStep 3556721 = 2667541) B2667541
theorem B3949955 : Blo 1559477 3949955 := bstep (se 1 (by rfl) ⟨2962466, by rfl⟩ : syracuseStep 3949955 = 5924933) B5924933
theorem B1754563 : Blo 1559477 1754563 := bstep (se 1 (by rfl) ⟨1315922, by rfl⟩ : syracuseStep 1754563 = 2631845) B2631845
theorem B1975747 : Blo 1559477 1975747 := bstep (se 1 (by rfl) ⟨1481810, by rfl⟩ : syracuseStep 1975747 = 2963621) B2963621
theorem B5268941 : Blo 1559477 5268941 := bstep (se 3 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 5268941 = 1975853) B1975853
theorem B2500049 : Blo 1559477 2500049 := bstep (se 2 (by rfl) ⟨937518, by rfl⟩ : syracuseStep 2500049 = 1875037) B1875037
theorem B3556867 : Blo 1559477 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B5268995 : Blo 1559477 5268995 := bstep (se 1 (by rfl) ⟨3951746, by rfl⟩ : syracuseStep 5268995 = 7903493) B7903493
theorem B1975843 : Blo 1559477 1975843 := bstep (se 1 (by rfl) ⟨1481882, by rfl⟩ : syracuseStep 1975843 = 2963765) B2963765
theorem B3950147 : Blo 1559477 3950147 := bstep (se 1 (by rfl) ⟨2962610, by rfl⟩ : syracuseStep 3950147 = 5925221) B5925221
theorem B1754707 : Blo 1559477 1754707 := bstep (se 1 (by rfl) ⟨1316030, by rfl⟩ : syracuseStep 1754707 = 2632061) B2632061
theorem B1779347 : Blo 1559477 1779347 := bstep (se 1 (by rfl) ⟨1334510, by rfl⟩ : syracuseStep 1779347 = 2669021) B2669021
theorem B8890019 : Blo 1559477 8890019 := bstep (se 1 (by rfl) ⟨6667514, by rfl⟩ : syracuseStep 8890019 = 13335029) B13335029
theorem B1754851 : Blo 1559477 1754851 := bstep (se 1 (by rfl) ⟨1316138, by rfl⟩ : syracuseStep 1754851 = 2632277) B2632277
theorem B5064461 : Blo 1559477 5064461 := bstep (se 3 (by rfl) ⟨949586, by rfl⟩ : syracuseStep 5064461 = 1899173) B1899173
theorem B6326029 : Blo 1559477 6326029 := bstep (se 3 (by rfl) ⟨1186130, by rfl⟩ : syracuseStep 6326029 = 2372261) B2372261
theorem B5269265 : Blo 1559477 5269265 := bstep (se 2 (by rfl) ⟨1975974, by rfl⟩ : syracuseStep 5269265 = 3951949) B3951949
theorem B22791989 : Blo 1559477 22791989 := bstep (se 5 (by rfl) ⟨1068374, by rfl⟩ : syracuseStep 22791989 = 2136749) B2136749
theorem B7898957 : Blo 1559477 7898957 := bstep (se 3 (by rfl) ⟨1481054, by rfl⟩ : syracuseStep 7898957 = 2962109) B2962109
theorem B1754995 : Blo 1559477 1754995 := bstep (se 1 (by rfl) ⟨1316246, by rfl⟩ : syracuseStep 1754995 = 2632493) B2632493
theorem B2221987 : Blo 1559477 2221987 := bstep (se 1 (by rfl) ⟨1666490, by rfl⟩ : syracuseStep 2221987 = 3332981) B3332981
theorem B2631649 : Blo 1559477 2631649 := bstep (se 2 (by rfl) ⟨986868, by rfl⟩ : syracuseStep 2631649 = 1973737) B1973737
theorem B4278257 : Blo 1559477 4278257 := bstep (se 2 (by rfl) ⟨1604346, by rfl⟩ : syracuseStep 4278257 = 3208693) B3208693
theorem B2631683 : Blo 1559477 2631683 := bstep (se 1 (by rfl) ⟨1973762, by rfl⟩ : syracuseStep 2631683 = 3947525) B3947525
theorem B5064707 : Blo 1559477 5064707 := bstep (se 1 (by rfl) ⟨3798530, by rfl⟩ : syracuseStep 5064707 = 7597061) B7597061
theorem B1755139 : Blo 1559477 1755139 := bstep (se 1 (by rfl) ⟨1316354, by rfl⟩ : syracuseStep 1755139 = 2632709) B2632709
theorem B2222083 : Blo 1559477 2222083 := bstep (se 1 (by rfl) ⟨1666562, by rfl⟩ : syracuseStep 2222083 = 3333125) B3333125
theorem B5064785 : Blo 1559477 5064785 := bstep (se 2 (by rfl) ⟨1899294, by rfl⟩ : syracuseStep 5064785 = 3798589) B3798589
theorem B4999277 : Blo 1559477 4999277 := bstep (se 3 (by rfl) ⟨937364, by rfl⟩ : syracuseStep 4999277 = 1874729) B1874729
theorem B2631811 : Blo 1559477 2631811 := bstep (se 1 (by rfl) ⟨1973858, by rfl⟩ : syracuseStep 2631811 = 3947717) B3947717
theorem B1755283 : Blo 1559477 1755283 := bstep (se 1 (by rfl) ⟨1316462, by rfl⟩ : syracuseStep 1755283 = 2632925) B2632925
theorem B6662321 : Blo 1559477 6662321 := bstep (se 2 (by rfl) ⟨2498370, by rfl⟩ : syracuseStep 6662321 = 4996741) B4996741
theorem B2631953 : Blo 1559477 2631953 := bstep (se 2 (by rfl) ⟨986982, by rfl⟩ : syracuseStep 2631953 = 1973965) B1973965
theorem B1755427 : Blo 1559477 1755427 := bstep (se 1 (by rfl) ⟨1316570, by rfl⟩ : syracuseStep 1755427 = 2633141) B2633141
theorem B5269805 : Blo 1559477 5269805 := bstep (se 3 (by rfl) ⟨988088, by rfl⟩ : syracuseStep 5269805 = 1976177) B1976177
theorem B4442435 : Blo 1559477 4442435 := bstep (se 1 (by rfl) ⟨3331826, by rfl⟩ : syracuseStep 4442435 = 6663653) B6663653
theorem B5269859 : Blo 1559477 5269859 := bstep (se 1 (by rfl) ⟨3952394, by rfl⟩ : syracuseStep 5269859 = 7904789) B7904789
theorem B48720269 : Blo 1559477 48720269 := bstep (se 3 (by rfl) ⟨9135050, by rfl⟩ : syracuseStep 48720269 = 18270101) B18270101
theorem B2632081 : Blo 1559477 2632081 := bstep (se 2 (by rfl) ⟨987030, by rfl⟩ : syracuseStep 2632081 = 1974061) B1974061
theorem B2632115 : Blo 1559477 2632115 := bstep (se 1 (by rfl) ⟨1974086, by rfl⟩ : syracuseStep 2632115 = 3948173) B3948173
theorem B1755571 : Blo 1559477 1755571 := bstep (se 1 (by rfl) ⟨1316678, by rfl⟩ : syracuseStep 1755571 = 2633357) B2633357
theorem B3951089 : Blo 1559477 3951089 := bstep (se 2 (by rfl) ⟨1481658, by rfl⟩ : syracuseStep 3951089 = 2963317) B2963317
theorem B2222579 : Blo 1559477 2222579 := bstep (se 1 (by rfl) ⟨1666934, by rfl⟩ : syracuseStep 2222579 = 3333869) B3333869
theorem B4999715 : Blo 1559477 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B3951139 : Blo 1559477 3951139 := bstep (se 1 (by rfl) ⟨2963354, by rfl⟩ : syracuseStep 3951139 = 5926709) B5926709
theorem B2632243 : Blo 1559477 2632243 := bstep (se 1 (by rfl) ⟨1974182, by rfl⟩ : syracuseStep 2632243 = 3948365) B3948365
theorem B1755715 : Blo 1559477 1755715 := bstep (se 1 (by rfl) ⟨1316786, by rfl⟩ : syracuseStep 1755715 = 2633573) B2633573
theorem B8440433 : Blo 1559477 8440433 := bstep (se 2 (by rfl) ⟨3165162, by rfl⟩ : syracuseStep 8440433 = 6330325) B6330325
theorem B3951281 : Blo 1559477 3951281 := bstep (se 2 (by rfl) ⟨1481730, by rfl⟩ : syracuseStep 3951281 = 2963461) B2963461
theorem B2632385 : Blo 1559477 2632385 := bstep (se 2 (by rfl) ⟨987144, by rfl⟩ : syracuseStep 2632385 = 1974289) B1974289
theorem B1755859 : Blo 1559477 1755859 := bstep (se 1 (by rfl) ⟨1316894, by rfl⟩ : syracuseStep 1755859 = 2633789) B2633789
theorem B3509009 : Blo 1559477 3509009 := bstep (se 2 (by rfl) ⟨1315878, by rfl⟩ : syracuseStep 3509009 = 2631757) B2631757
theorem B3509027 : Blo 1559477 3509027 := bstep (se 1 (by rfl) ⟨2631770, by rfl⟩ : syracuseStep 3509027 = 5263541) B5263541
theorem B2632513 : Blo 1559477 2632513 := bstep (se 2 (by rfl) ⟨987192, by rfl⟩ : syracuseStep 2632513 = 1974385) B1974385
theorem B3001169 : Blo 1559477 3001169 := bstep (se 2 (by rfl) ⟨1125438, by rfl⟩ : syracuseStep 3001169 = 2250877) B2250877
theorem B2632547 : Blo 1559477 2632547 := bstep (se 1 (by rfl) ⟨1974410, by rfl⟩ : syracuseStep 2632547 = 3948821) B3948821
theorem B1756003 : Blo 1559477 1756003 := bstep (se 1 (by rfl) ⟨1317002, by rfl⟩ : syracuseStep 1756003 = 2634005) B2634005
theorem B4746115 : Blo 1559477 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B1559491 : Blo 1559477 1559491 := bstep (se 1 (by rfl) ⟨1169618, by rfl⟩ : syracuseStep 1559491 = 2339237) B2339237
theorem B1559507 : Blo 1559477 1559507 := bstep (se 1 (by rfl) ⟨1169630, by rfl⟩ : syracuseStep 1559507 = 2339261) B2339261
theorem B1559523 : Blo 1559477 1559523 := bstep (se 1 (by rfl) ⟨1169642, by rfl⟩ : syracuseStep 1559523 = 2339285) B2339285
theorem B2632675 : Blo 1559477 2632675 := bstep (se 1 (by rfl) ⟨1974506, by rfl⟩ : syracuseStep 2632675 = 3949013) B3949013
theorem B1559539 : Blo 1559477 1559539 := bstep (se 1 (by rfl) ⟨1169654, by rfl⟩ : syracuseStep 1559539 = 2339309) B2339309
theorem B1756147 : Blo 1559477 1756147 := bstep (se 1 (by rfl) ⟨1317110, by rfl⟩ : syracuseStep 1756147 = 2634221) B2634221
theorem B1559555 : Blo 1559477 1559555 := bstep (se 1 (by rfl) ⟨1169666, by rfl⟩ : syracuseStep 1559555 = 2339333) B2339333
theorem B1559571 : Blo 1559477 1559571 := bstep (se 1 (by rfl) ⟨1169678, by rfl⟩ : syracuseStep 1559571 = 2339357) B2339357
theorem B1666067 : Blo 1559477 1666067 := bstep (se 1 (by rfl) ⟨1249550, by rfl⟩ : syracuseStep 1666067 = 2499101) B2499101
theorem B1559587 : Blo 1559477 1559587 := bstep (se 1 (by rfl) ⟨1169690, by rfl⟩ : syracuseStep 1559587 = 2339381) B2339381
theorem B3509297 : Blo 1559477 3509297 := bstep (se 2 (by rfl) ⟨1315986, by rfl⟩ : syracuseStep 3509297 = 2631973) B2631973
theorem B1559603 : Blo 1559477 1559603 := bstep (se 1 (by rfl) ⟨1169702, by rfl⟩ : syracuseStep 1559603 = 2339405) B2339405
theorem B1559619 : Blo 1559477 1559619 := bstep (se 1 (by rfl) ⟨1169714, by rfl⟩ : syracuseStep 1559619 = 2339429) B2339429
theorem B3509315 : Blo 1559477 3509315 := bstep (se 1 (by rfl) ⟨2631986, by rfl⟩ : syracuseStep 3509315 = 5263973) B5263973
theorem B1559635 : Blo 1559477 1559635 := bstep (se 1 (by rfl) ⟨1169726, by rfl⟩ : syracuseStep 1559635 = 2339453) B2339453
theorem B1559651 : Blo 1559477 1559651 := bstep (se 1 (by rfl) ⟨1169738, by rfl⟩ : syracuseStep 1559651 = 2339477) B2339477
theorem B4443245 : Blo 1559477 4443245 := bstep (se 3 (by rfl) ⟨833108, by rfl⟩ : syracuseStep 4443245 = 1666217) B1666217
theorem B2632817 : Blo 1559477 2632817 := bstep (se 2 (by rfl) ⟨987306, by rfl⟩ : syracuseStep 2632817 = 1974613) B1974613
theorem B1559667 : Blo 1559477 1559667 := bstep (se 1 (by rfl) ⟨1169750, by rfl⟩ : syracuseStep 1559667 = 2339501) B2339501
theorem B2223217 : Blo 1559477 2223217 := bstep (se 2 (by rfl) ⟨833706, by rfl⟩ : syracuseStep 2223217 = 1667413) B1667413
theorem B1559683 : Blo 1559477 1559683 := bstep (se 1 (by rfl) ⟨1169762, by rfl⟩ : syracuseStep 1559683 = 2339525) B2339525
theorem B4746371 : Blo 1559477 4746371 := bstep (se 1 (by rfl) ⟨3559778, by rfl⟩ : syracuseStep 4746371 = 7119557) B7119557
theorem B1756291 : Blo 1559477 1756291 := bstep (se 1 (by rfl) ⟨1317218, by rfl⟩ : syracuseStep 1756291 = 2634437) B2634437
theorem B1559699 : Blo 1559477 1559699 := bstep (se 1 (by rfl) ⟨1169774, by rfl⟩ : syracuseStep 1559699 = 2339549) B2339549
theorem B1559715 : Blo 1559477 1559715 := bstep (se 1 (by rfl) ⟨1169786, by rfl⟩ : syracuseStep 1559715 = 2339573) B2339573
theorem B1559731 : Blo 1559477 1559731 := bstep (se 1 (by rfl) ⟨1169798, by rfl⟩ : syracuseStep 1559731 = 2339597) B2339597
theorem B1559747 : Blo 1559477 1559747 := bstep (se 1 (by rfl) ⟨1169810, by rfl⟩ : syracuseStep 1559747 = 2339621) B2339621
theorem B20008133 : Blo 1559477 20008133 := bstep (se 4 (by rfl) ⟨1875762, by rfl⟩ : syracuseStep 20008133 = 3751525) B3751525
theorem B1559763 : Blo 1559477 1559763 := bstep (se 1 (by rfl) ⟨1169822, by rfl⟩ : syracuseStep 1559763 = 2339645) B2339645
theorem B1559779 : Blo 1559477 1559779 := bstep (se 1 (by rfl) ⟨1169834, by rfl⟩ : syracuseStep 1559779 = 2339669) B2339669
theorem B2534627 : Blo 1559477 2534627 := bstep (se 1 (by rfl) ⟨1900970, by rfl⟩ : syracuseStep 2534627 = 3801941) B3801941
theorem B2632945 : Blo 1559477 2632945 := bstep (se 2 (by rfl) ⟨987354, by rfl⟩ : syracuseStep 2632945 = 1974709) B1974709
theorem B1559795 : Blo 1559477 1559795 := bstep (se 1 (by rfl) ⟨1169846, by rfl⟩ : syracuseStep 1559795 = 2339693) B2339693
theorem B1559811 : Blo 1559477 1559811 := bstep (se 1 (by rfl) ⟨1169858, by rfl⟩ : syracuseStep 1559811 = 2339717) B2339717
theorem B1559827 : Blo 1559477 1559827 := bstep (se 1 (by rfl) ⟨1169870, by rfl⟩ : syracuseStep 1559827 = 2339741) B2339741
theorem B2632979 : Blo 1559477 2632979 := bstep (se 1 (by rfl) ⟨1974734, by rfl⟩ : syracuseStep 2632979 = 3949469) B3949469
theorem B1756435 : Blo 1559477 1756435 := bstep (se 1 (by rfl) ⟨1317326, by rfl⟩ : syracuseStep 1756435 = 2634653) B2634653
theorem B1559843 : Blo 1559477 1559843 := bstep (se 1 (by rfl) ⟨1169882, by rfl⟩ : syracuseStep 1559843 = 2339765) B2339765
theorem B2813219 : Blo 1559477 2813219 := bstep (se 1 (by rfl) ⟨2109914, by rfl⟩ : syracuseStep 2813219 = 4219829) B4219829
theorem B4443437 : Blo 1559477 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B5926193 : Blo 1559477 5926193 := bstep (se 2 (by rfl) ⟨2222322, by rfl⟩ : syracuseStep 5926193 = 4444645) B4444645
theorem B1559859 : Blo 1559477 1559859 := bstep (se 1 (by rfl) ⟨1169894, by rfl⟩ : syracuseStep 1559859 = 2339789) B2339789
theorem B1559875 : Blo 1559477 1559875 := bstep (se 1 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 1559875 = 2339813) B2339813
theorem B3509585 : Blo 1559477 3509585 := bstep (se 2 (by rfl) ⟨1316094, by rfl⟩ : syracuseStep 3509585 = 2632189) B2632189
theorem B1559891 : Blo 1559477 1559891 := bstep (se 1 (by rfl) ⟨1169918, by rfl⟩ : syracuseStep 1559891 = 2339837) B2339837
theorem B3509603 : Blo 1559477 3509603 := bstep (se 1 (by rfl) ⟨2632202, by rfl⟩ : syracuseStep 3509603 = 5264405) B5264405
theorem B1559907 : Blo 1559477 1559907 := bstep (se 1 (by rfl) ⟨1169930, by rfl⟩ : syracuseStep 1559907 = 2339861) B2339861
theorem B1559923 : Blo 1559477 1559923 := bstep (se 1 (by rfl) ⟨1169942, by rfl⟩ : syracuseStep 1559923 = 2339885) B2339885
theorem B1559939 : Blo 1559477 1559939 := bstep (se 1 (by rfl) ⟨1169954, by rfl⟩ : syracuseStep 1559939 = 2339909) B2339909
theorem B5623181 : Blo 1559477 5623181 := bstep (se 3 (by rfl) ⟨1054346, by rfl⟩ : syracuseStep 5623181 = 2108693) B2108693
theorem B1559955 : Blo 1559477 1559955 := bstep (se 1 (by rfl) ⟨1169966, by rfl⟩ : syracuseStep 1559955 = 2339933) B2339933
theorem B2633107 : Blo 1559477 2633107 := bstep (se 1 (by rfl) ⟨1974830, by rfl⟩ : syracuseStep 2633107 = 3949661) B3949661
theorem B2960803 : Blo 1559477 2960803 := bstep (se 1 (by rfl) ⟨2220602, by rfl⟩ : syracuseStep 2960803 = 4441205) B4441205
theorem B1559971 : Blo 1559477 1559971 := bstep (se 1 (by rfl) ⟨1169978, by rfl⟩ : syracuseStep 1559971 = 2339957) B2339957
theorem B1756579 : Blo 1559477 1756579 := bstep (se 1 (by rfl) ⟨1317434, by rfl⟩ : syracuseStep 1756579 = 2634869) B2634869
theorem B2108849 : Blo 1559477 2108849 := bstep (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) B1581637
theorem B1559987 : Blo 1559477 1559987 := bstep (se 1 (by rfl) ⟨1169990, by rfl⟩ : syracuseStep 1559987 = 2339981) B2339981
theorem B1560003 : Blo 1559477 1560003 := bstep (se 1 (by rfl) ⟨1170002, by rfl⟩ : syracuseStep 1560003 = 2340005) B2340005
theorem B2960849 : Blo 1559477 2960849 := bstep (se 2 (by rfl) ⟨1110318, by rfl⟩ : syracuseStep 2960849 = 2220637) B2220637
theorem B1560019 : Blo 1559477 1560019 := bstep (se 1 (by rfl) ⟨1170014, by rfl⟩ : syracuseStep 1560019 = 2340029) B2340029
theorem B1560035 : Blo 1559477 1560035 := bstep (se 1 (by rfl) ⟨1170026, by rfl⟩ : syracuseStep 1560035 = 2340053) B2340053
theorem B1560051 : Blo 1559477 1560051 := bstep (se 1 (by rfl) ⟨1170038, by rfl⟩ : syracuseStep 1560051 = 2340077) B2340077
theorem B1560067 : Blo 1559477 1560067 := bstep (se 1 (by rfl) ⟨1170050, by rfl⟩ : syracuseStep 1560067 = 2340101) B2340101
theorem B1560083 : Blo 1559477 1560083 := bstep (se 1 (by rfl) ⟨1170062, by rfl⟩ : syracuseStep 1560083 = 2340125) B2340125
theorem B2633249 : Blo 1559477 2633249 := bstep (se 2 (by rfl) ⟨987468, by rfl⟩ : syracuseStep 2633249 = 1974937) B1974937
theorem B1560099 : Blo 1559477 1560099 := bstep (se 1 (by rfl) ⟨1170074, by rfl⟩ : syracuseStep 1560099 = 2340149) B2340149
theorem B2108963 : Blo 1559477 2108963 := bstep (se 1 (by rfl) ⟨1581722, by rfl⟩ : syracuseStep 2108963 = 3163445) B3163445
theorem B1560115 : Blo 1559477 1560115 := bstep (se 1 (by rfl) ⟨1170086, by rfl⟩ : syracuseStep 1560115 = 2340173) B2340173
theorem B1560131 : Blo 1559477 1560131 := bstep (se 1 (by rfl) ⟨1170098, by rfl⟩ : syracuseStep 1560131 = 2340197) B2340197
theorem B1560147 : Blo 1559477 1560147 := bstep (se 1 (by rfl) ⟨1170110, by rfl⟩ : syracuseStep 1560147 = 2340221) B2340221
theorem B1560163 : Blo 1559477 1560163 := bstep (se 1 (by rfl) ⟨1170122, by rfl⟩ : syracuseStep 1560163 = 2340245) B2340245
theorem B3509873 : Blo 1559477 3509873 := bstep (se 2 (by rfl) ⟨1316202, by rfl⟩ : syracuseStep 3509873 = 2632405) B2632405
theorem B3001969 : Blo 1559477 3001969 := bstep (se 2 (by rfl) ⟨1125738, by rfl⟩ : syracuseStep 3001969 = 2251477) B2251477
theorem B1560179 : Blo 1559477 1560179 := bstep (se 1 (by rfl) ⟨1170134, by rfl⟩ : syracuseStep 1560179 = 2340269) B2340269
theorem B3509891 : Blo 1559477 3509891 := bstep (se 1 (by rfl) ⟨2632418, by rfl⟩ : syracuseStep 3509891 = 5264837) B5264837
theorem B1560195 : Blo 1559477 1560195 := bstep (se 1 (by rfl) ⟨1170146, by rfl⟩ : syracuseStep 1560195 = 2340293) B2340293
theorem B3952273 : Blo 1559477 3952273 := bstep (se 2 (by rfl) ⟨1482102, by rfl⟩ : syracuseStep 3952273 = 2964205) B2964205
theorem B1560211 : Blo 1559477 1560211 := bstep (se 1 (by rfl) ⟨1170158, by rfl⟩ : syracuseStep 1560211 = 2340317) B2340317
theorem B2633377 : Blo 1559477 2633377 := bstep (se 2 (by rfl) ⟨987516, by rfl⟩ : syracuseStep 2633377 = 1975033) B1975033
theorem B1560227 : Blo 1559477 1560227 := bstep (se 1 (by rfl) ⟨1170170, by rfl⟩ : syracuseStep 1560227 = 2340341) B2340341
theorem B1560243 : Blo 1559477 1560243 := bstep (se 1 (by rfl) ⟨1170182, by rfl⟩ : syracuseStep 1560243 = 2340365) B2340365
theorem B1560259 : Blo 1559477 1560259 := bstep (se 1 (by rfl) ⟨1170194, by rfl⟩ : syracuseStep 1560259 = 2340389) B2340389
theorem B2633411 : Blo 1559477 2633411 := bstep (se 1 (by rfl) ⟨1975058, by rfl⟩ : syracuseStep 2633411 = 3950117) B3950117
theorem B1560275 : Blo 1559477 1560275 := bstep (se 1 (by rfl) ⟨1170206, by rfl⟩ : syracuseStep 1560275 = 2340413) B2340413
theorem B1560291 : Blo 1559477 1560291 := bstep (se 1 (by rfl) ⟨1170218, by rfl⟩ : syracuseStep 1560291 = 2340437) B2340437
theorem B2961137 : Blo 1559477 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B16010993 : Blo 1559477 16010993 := bstep (se 2 (by rfl) ⟨6004122, by rfl⟩ : syracuseStep 16010993 = 12008245) B12008245
theorem B1560307 : Blo 1559477 1560307 := bstep (se 1 (by rfl) ⟨1170230, by rfl⟩ : syracuseStep 1560307 = 2340461) B2340461
theorem B1560323 : Blo 1559477 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B1666819 : Blo 1559477 1666819 := bstep (se 1 (by rfl) ⟨1250114, by rfl⟩ : syracuseStep 1666819 = 2500229) B2500229
theorem B1560339 : Blo 1559477 1560339 := bstep (se 1 (by rfl) ⟨1170254, by rfl⟩ : syracuseStep 1560339 = 2340509) B2340509
theorem B1560355 : Blo 1559477 1560355 := bstep (se 1 (by rfl) ⟨1170266, by rfl⟩ : syracuseStep 1560355 = 2340533) B2340533
theorem B1560371 : Blo 1559477 1560371 := bstep (se 1 (by rfl) ⟨1170278, by rfl⟩ : syracuseStep 1560371 = 2340557) B2340557
theorem B1560387 : Blo 1559477 1560387 := bstep (se 1 (by rfl) ⟨1170290, by rfl⟩ : syracuseStep 1560387 = 2340581) B2340581
theorem B2633539 : Blo 1559477 2633539 := bstep (se 1 (by rfl) ⟨1975154, by rfl⟩ : syracuseStep 2633539 = 3950309) B3950309
theorem B1560403 : Blo 1559477 1560403 := bstep (se 1 (by rfl) ⟨1170302, by rfl⟩ : syracuseStep 1560403 = 2340605) B2340605
theorem B1560419 : Blo 1559477 1560419 := bstep (se 1 (by rfl) ⟨1170314, by rfl⟩ : syracuseStep 1560419 = 2340629) B2340629
theorem B1560435 : Blo 1559477 1560435 := bstep (se 1 (by rfl) ⟨1170326, by rfl⟩ : syracuseStep 1560435 = 2340653) B2340653
theorem B1560451 : Blo 1559477 1560451 := bstep (se 1 (by rfl) ⟨1170338, by rfl⟩ : syracuseStep 1560451 = 2340677) B2340677
theorem B3510161 : Blo 1559477 3510161 := bstep (se 2 (by rfl) ⟨1316310, by rfl⟩ : syracuseStep 3510161 = 2632621) B2632621
theorem B1560467 : Blo 1559477 1560467 := bstep (se 1 (by rfl) ⟨1170350, by rfl⟩ : syracuseStep 1560467 = 2340701) B2340701
theorem B3510179 : Blo 1559477 3510179 := bstep (se 1 (by rfl) ⟨2632634, by rfl⟩ : syracuseStep 3510179 = 5265269) B5265269
theorem B1560483 : Blo 1559477 1560483 := bstep (se 1 (by rfl) ⟨1170362, by rfl⟩ : syracuseStep 1560483 = 2340725) B2340725
theorem B1560499 : Blo 1559477 1560499 := bstep (se 1 (by rfl) ⟨1170374, by rfl⟩ : syracuseStep 1560499 = 2340749) B2340749
theorem B1953715 : Blo 1559477 1953715 := bstep (se 1 (by rfl) ⟨1465286, by rfl⟩ : syracuseStep 1953715 = 2930573) B2930573
theorem B1560515 : Blo 1559477 1560515 := bstep (se 1 (by rfl) ⟨1170386, by rfl⟩ : syracuseStep 1560515 = 2340773) B2340773
theorem B2633681 : Blo 1559477 2633681 := bstep (se 2 (by rfl) ⟨987630, by rfl⟩ : syracuseStep 2633681 = 1975261) B1975261
theorem B1560531 : Blo 1559477 1560531 := bstep (se 1 (by rfl) ⟨1170398, by rfl⟩ : syracuseStep 1560531 = 2340797) B2340797
theorem B3002339 : Blo 1559477 3002339 := bstep (se 1 (by rfl) ⟨2251754, by rfl⟩ : syracuseStep 3002339 = 4503509) B4503509
theorem B1560547 : Blo 1559477 1560547 := bstep (se 1 (by rfl) ⟨1170410, by rfl⟩ : syracuseStep 1560547 = 2340821) B2340821
theorem B1560563 : Blo 1559477 1560563 := bstep (se 1 (by rfl) ⟨1170422, by rfl⟩ : syracuseStep 1560563 = 2340845) B2340845
theorem B1560579 : Blo 1559477 1560579 := bstep (se 1 (by rfl) ⟨1170434, by rfl⟩ : syracuseStep 1560579 = 2340869) B2340869
theorem B1667075 : Blo 1559477 1667075 := bstep (se 1 (by rfl) ⟨1250306, by rfl⟩ : syracuseStep 1667075 = 2500613) B2500613
theorem B1560595 : Blo 1559477 1560595 := bstep (se 1 (by rfl) ⟨1170446, by rfl⟩ : syracuseStep 1560595 = 2340893) B2340893
theorem B1560611 : Blo 1559477 1560611 := bstep (se 1 (by rfl) ⟨1170458, by rfl⟩ : syracuseStep 1560611 = 2340917) B2340917
theorem B3559459 : Blo 1559477 3559459 := bstep (se 1 (by rfl) ⟨2669594, by rfl⟩ : syracuseStep 3559459 = 5339189) B5339189
theorem B1560627 : Blo 1559477 1560627 := bstep (se 1 (by rfl) ⟨1170470, by rfl⟩ : syracuseStep 1560627 = 2340941) B2340941
theorem B1560643 : Blo 1559477 1560643 := bstep (se 1 (by rfl) ⟨1170482, by rfl⟩ : syracuseStep 1560643 = 2340965) B2340965
theorem B2633809 : Blo 1559477 2633809 := bstep (se 2 (by rfl) ⟨987678, by rfl⟩ : syracuseStep 2633809 = 1975357) B1975357
theorem B1560659 : Blo 1559477 1560659 := bstep (se 1 (by rfl) ⟨1170494, by rfl⟩ : syracuseStep 1560659 = 2340989) B2340989
theorem B1560675 : Blo 1559477 1560675 := bstep (se 1 (by rfl) ⟨1170506, by rfl⟩ : syracuseStep 1560675 = 2341013) B2341013
theorem B1560691 : Blo 1559477 1560691 := bstep (se 1 (by rfl) ⟨1170518, by rfl⟩ : syracuseStep 1560691 = 2341037) B2341037
theorem B2633843 : Blo 1559477 2633843 := bstep (se 1 (by rfl) ⟨1975382, by rfl⟩ : syracuseStep 2633843 = 3950765) B3950765
theorem B1560707 : Blo 1559477 1560707 := bstep (se 1 (by rfl) ⟨1170530, by rfl⟩ : syracuseStep 1560707 = 2341061) B2341061
theorem B4812941 : Blo 1559477 4812941 := bstep (se 3 (by rfl) ⟨902426, by rfl⟩ : syracuseStep 4812941 = 1804853) B1804853
theorem B1560723 : Blo 1559477 1560723 := bstep (se 1 (by rfl) ⟨1170542, by rfl⟩ : syracuseStep 1560723 = 2341085) B2341085
theorem B2109601 : Blo 1559477 2109601 := bstep (se 2 (by rfl) ⟨791100, by rfl⟩ : syracuseStep 2109601 = 1582201) B1582201
theorem B1560739 : Blo 1559477 1560739 := bstep (se 1 (by rfl) ⟨1170554, by rfl⟩ : syracuseStep 1560739 = 2341109) B2341109
theorem B3510449 : Blo 1559477 3510449 := bstep (se 2 (by rfl) ⟨1316418, by rfl⟩ : syracuseStep 3510449 = 2632837) B2632837
theorem B1560755 : Blo 1559477 1560755 := bstep (se 1 (by rfl) ⟨1170566, by rfl⟩ : syracuseStep 1560755 = 2341133) B2341133
theorem B3510467 : Blo 1559477 3510467 := bstep (se 1 (by rfl) ⟨2632850, by rfl⟩ : syracuseStep 3510467 = 5265701) B5265701
theorem B1560771 : Blo 1559477 1560771 := bstep (se 1 (by rfl) ⟨1170578, by rfl⟩ : syracuseStep 1560771 = 2341157) B2341157
theorem B1560787 : Blo 1559477 1560787 := bstep (se 1 (by rfl) ⟨1170590, by rfl⟩ : syracuseStep 1560787 = 2341181) B2341181
theorem B1560803 : Blo 1559477 1560803 := bstep (se 1 (by rfl) ⟨1170602, by rfl⟩ : syracuseStep 1560803 = 2341205) B2341205
theorem B3207395 : Blo 1559477 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B1560819 : Blo 1559477 1560819 := bstep (se 1 (by rfl) ⟨1170614, by rfl⟩ : syracuseStep 1560819 = 2341229) B2341229
theorem B2633971 : Blo 1559477 2633971 := bstep (se 1 (by rfl) ⟨1975478, by rfl⟩ : syracuseStep 2633971 = 3950957) B3950957
theorem B1560835 : Blo 1559477 1560835 := bstep (se 1 (by rfl) ⟨1170626, by rfl⟩ : syracuseStep 1560835 = 2341253) B2341253
theorem B4444429 : Blo 1559477 4444429 := bstep (se 3 (by rfl) ⟨833330, by rfl⟩ : syracuseStep 4444429 = 1666661) B1666661
theorem B1560851 : Blo 1559477 1560851 := bstep (se 1 (by rfl) ⟨1170638, by rfl⟩ : syracuseStep 1560851 = 2341277) B2341277
theorem B3559715 : Blo 1559477 3559715 := bstep (se 1 (by rfl) ⟨2669786, by rfl⟩ : syracuseStep 3559715 = 5339573) B5339573
theorem B1560867 : Blo 1559477 1560867 := bstep (se 1 (by rfl) ⟨1170650, by rfl⟩ : syracuseStep 1560867 = 2341301) B2341301
theorem B1560883 : Blo 1559477 1560883 := bstep (se 1 (by rfl) ⟨1170662, by rfl⟩ : syracuseStep 1560883 = 2341325) B2341325
theorem B1560899 : Blo 1559477 1560899 := bstep (se 1 (by rfl) ⟨1170674, by rfl⟩ : syracuseStep 1560899 = 2341349) B2341349
theorem B1560915 : Blo 1559477 1560915 := bstep (se 1 (by rfl) ⟨1170686, by rfl⟩ : syracuseStep 1560915 = 2341373) B2341373
theorem B1560931 : Blo 1559477 1560931 := bstep (se 1 (by rfl) ⟨1170698, by rfl⟩ : syracuseStep 1560931 = 2341397) B2341397
theorem B1560947 : Blo 1559477 1560947 := bstep (se 1 (by rfl) ⟨1170710, by rfl⟩ : syracuseStep 1560947 = 2341421) B2341421
theorem B2634113 : Blo 1559477 2634113 := bstep (se 2 (by rfl) ⟨987792, by rfl⟩ : syracuseStep 2634113 = 1975585) B1975585
theorem B1560963 : Blo 1559477 1560963 := bstep (se 1 (by rfl) ⟨1170722, by rfl⟩ : syracuseStep 1560963 = 2341445) B2341445
theorem B5263757 : Blo 1559477 5263757 := bstep (se 3 (by rfl) ⟨986954, by rfl⟩ : syracuseStep 5263757 = 1973909) B1973909
theorem B2339219 : Blo 1559477 2339219 := bstep (se 1 (by rfl) ⟨1754414, by rfl⟩ : syracuseStep 2339219 = 3508829) B3508829
theorem B1560979 : Blo 1559477 1560979 := bstep (se 1 (by rfl) ⟨1170734, by rfl⟩ : syracuseStep 1560979 = 2341469) B2341469
theorem B1560995 : Blo 1559477 1560995 := bstep (se 1 (by rfl) ⟨1170746, by rfl⟩ : syracuseStep 1560995 = 2341493) B2341493
theorem B5001635 : Blo 1559477 5001635 := bstep (se 1 (by rfl) ⟨3751226, by rfl⟩ : syracuseStep 5001635 = 7502453) B7502453
theorem B2339249 : Blo 1559477 2339249 := bstep (se 2 (by rfl) ⟨877218, by rfl⟩ : syracuseStep 2339249 = 1754437) B1754437
theorem B1561011 : Blo 1559477 1561011 := bstep (se 1 (by rfl) ⟨1170758, by rfl⟩ : syracuseStep 1561011 = 2341517) B2341517
theorem B2339267 : Blo 1559477 2339267 := bstep (se 1 (by rfl) ⟨1754450, by rfl⟩ : syracuseStep 2339267 = 3508901) B3508901
theorem B5263811 : Blo 1559477 5263811 := bstep (se 1 (by rfl) ⟨3947858, by rfl⟩ : syracuseStep 5263811 = 7895717) B7895717
theorem B2961859 : Blo 1559477 2961859 := bstep (se 1 (by rfl) ⟨2221394, by rfl⟩ : syracuseStep 2961859 = 4442789) B4442789
theorem B1561027 : Blo 1559477 1561027 := bstep (se 1 (by rfl) ⟨1170770, by rfl⟩ : syracuseStep 1561027 = 2341541) B2341541
theorem B3510737 : Blo 1559477 3510737 := bstep (se 2 (by rfl) ⟨1316526, by rfl⟩ : syracuseStep 3510737 = 2633053) B2633053
theorem B1561043 : Blo 1559477 1561043 := bstep (se 1 (by rfl) ⟨1170782, by rfl⟩ : syracuseStep 1561043 = 2341565) B2341565
theorem B2339297 : Blo 1559477 2339297 := bstep (se 2 (by rfl) ⟨877236, by rfl⟩ : syracuseStep 2339297 = 1754473) B1754473
theorem B3510755 : Blo 1559477 3510755 := bstep (se 1 (by rfl) ⟨2633066, by rfl⟩ : syracuseStep 3510755 = 5266133) B5266133
theorem B1561059 : Blo 1559477 1561059 := bstep (se 1 (by rfl) ⟨1170794, by rfl⟩ : syracuseStep 1561059 = 2341589) B2341589
theorem B2339315 : Blo 1559477 2339315 := bstep (se 1 (by rfl) ⟨1754486, by rfl⟩ : syracuseStep 2339315 = 3508973) B3508973
theorem B1561075 : Blo 1559477 1561075 := bstep (se 1 (by rfl) ⟨1170806, by rfl⟩ : syracuseStep 1561075 = 2341613) B2341613
theorem B2634241 : Blo 1559477 2634241 := bstep (se 2 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 2634241 = 1975681) B1975681
theorem B1561091 : Blo 1559477 1561091 := bstep (se 1 (by rfl) ⟨1170818, by rfl⟩ : syracuseStep 1561091 = 2341637) B2341637
theorem B2339345 : Blo 1559477 2339345 := bstep (se 2 (by rfl) ⟨877254, by rfl⟩ : syracuseStep 2339345 = 1754509) B1754509
theorem B1561107 : Blo 1559477 1561107 := bstep (se 1 (by rfl) ⟨1170830, by rfl⟩ : syracuseStep 1561107 = 2341661) B2341661
theorem B2339363 : Blo 1559477 2339363 := bstep (se 1 (by rfl) ⟨1754522, by rfl⟩ : syracuseStep 2339363 = 3509045) B3509045
theorem B2634275 : Blo 1559477 2634275 := bstep (se 1 (by rfl) ⟨1975706, by rfl⟩ : syracuseStep 2634275 = 3951413) B3951413
theorem B1561123 : Blo 1559477 1561123 := bstep (se 1 (by rfl) ⟨1170842, by rfl⟩ : syracuseStep 1561123 = 2341685) B2341685
theorem B1561139 : Blo 1559477 1561139 := bstep (se 1 (by rfl) ⟨1170854, by rfl⟩ : syracuseStep 1561139 = 2341709) B2341709
theorem B2339393 : Blo 1559477 2339393 := bstep (se 2 (by rfl) ⟨877272, by rfl⟩ : syracuseStep 2339393 = 1754545) B1754545
theorem B1561155 : Blo 1559477 1561155 := bstep (se 1 (by rfl) ⟨1170866, by rfl⟩ : syracuseStep 1561155 = 2341733) B2341733
theorem B6664781 : Blo 1559477 6664781 := bstep (se 3 (by rfl) ⟨1249646, by rfl⟩ : syracuseStep 6664781 = 2499293) B2499293
theorem B2339411 : Blo 1559477 2339411 := bstep (se 1 (by rfl) ⟨1754558, by rfl⟩ : syracuseStep 2339411 = 3509117) B3509117
theorem B1561171 : Blo 1559477 1561171 := bstep (se 1 (by rfl) ⟨1170878, by rfl⟩ : syracuseStep 1561171 = 2341757) B2341757
theorem B1561187 : Blo 1559477 1561187 := bstep (se 1 (by rfl) ⟨1170890, by rfl⟩ : syracuseStep 1561187 = 2341781) B2341781
theorem B2339441 : Blo 1559477 2339441 := bstep (se 2 (by rfl) ⟨877290, by rfl⟩ : syracuseStep 2339441 = 1754581) B1754581
theorem B7115377 : Blo 1559477 7115377 := bstep (se 2 (by rfl) ⟨2668266, by rfl⟩ : syracuseStep 7115377 = 5336533) B5336533
theorem B1561203 : Blo 1559477 1561203 := bstep (se 1 (by rfl) ⟨1170902, by rfl⟩ : syracuseStep 1561203 = 2341805) B2341805
theorem B2339459 : Blo 1559477 2339459 := bstep (se 1 (by rfl) ⟨1754594, by rfl⟩ : syracuseStep 2339459 = 3509189) B3509189
theorem B1561219 : Blo 1559477 1561219 := bstep (se 1 (by rfl) ⟨1170914, by rfl⟩ : syracuseStep 1561219 = 2341829) B2341829
theorem B1561235 : Blo 1559477 1561235 := bstep (se 1 (by rfl) ⟨1170926, by rfl⟩ : syracuseStep 1561235 = 2341853) B2341853
theorem B2339489 : Blo 1559477 2339489 := bstep (se 2 (by rfl) ⟨877308, by rfl⟩ : syracuseStep 2339489 = 1754617) B1754617
theorem B2634403 : Blo 1559477 2634403 := bstep (se 1 (by rfl) ⟨1975802, by rfl⟩ : syracuseStep 2634403 = 3951605) B3951605
theorem B1561251 : Blo 1559477 1561251 := bstep (se 1 (by rfl) ⟨1170938, by rfl⟩ : syracuseStep 1561251 = 2341877) B2341877
theorem B7901873 : Blo 1559477 7901873 := bstep (se 2 (by rfl) ⟨2963202, by rfl⟩ : syracuseStep 7901873 = 5926405) B5926405
theorem B2339507 : Blo 1559477 2339507 := bstep (se 1 (by rfl) ⟨1754630, by rfl⟩ : syracuseStep 2339507 = 3509261) B3509261
theorem B1561267 : Blo 1559477 1561267 := bstep (se 1 (by rfl) ⟨1170950, by rfl⟩ : syracuseStep 1561267 = 2341901) B2341901
theorem B1561283 : Blo 1559477 1561283 := bstep (se 1 (by rfl) ⟨1170962, by rfl⟩ : syracuseStep 1561283 = 2341925) B2341925
theorem B2339537 : Blo 1559477 2339537 := bstep (se 2 (by rfl) ⟨877326, by rfl⟩ : syracuseStep 2339537 = 1754653) B1754653
theorem B5264081 : Blo 1559477 5264081 := bstep (se 2 (by rfl) ⟨1974030, by rfl⟩ : syracuseStep 5264081 = 3948061) B3948061
theorem B1561299 : Blo 1559477 1561299 := bstep (se 1 (by rfl) ⟨1170974, by rfl⟩ : syracuseStep 1561299 = 2341949) B2341949
theorem B2339555 : Blo 1559477 2339555 := bstep (se 1 (by rfl) ⟨1754666, by rfl⟩ : syracuseStep 2339555 = 3509333) B3509333
theorem B5927651 : Blo 1559477 5927651 := bstep (se 1 (by rfl) ⟨4445738, by rfl⟩ : syracuseStep 5927651 = 8891477) B8891477
theorem B1561315 : Blo 1559477 1561315 := bstep (se 1 (by rfl) ⟨1170986, by rfl⟩ : syracuseStep 1561315 = 2341973) B2341973
theorem B3511025 : Blo 1559477 3511025 := bstep (se 2 (by rfl) ⟨1316634, by rfl⟩ : syracuseStep 3511025 = 2633269) B2633269
theorem B1561331 : Blo 1559477 1561331 := bstep (se 1 (by rfl) ⟨1170998, by rfl⟩ : syracuseStep 1561331 = 2341997) B2341997
theorem B2339585 : Blo 1559477 2339585 := bstep (se 2 (by rfl) ⟨877344, by rfl⟩ : syracuseStep 2339585 = 1754689) B1754689
theorem B3511043 : Blo 1559477 3511043 := bstep (se 1 (by rfl) ⟨2633282, by rfl⟩ : syracuseStep 3511043 = 5266565) B5266565
theorem B1561347 : Blo 1559477 1561347 := bstep (se 1 (by rfl) ⟨1171010, by rfl⟩ : syracuseStep 1561347 = 2342021) B2342021
theorem B2339603 : Blo 1559477 2339603 := bstep (se 1 (by rfl) ⟨1754702, by rfl⟩ : syracuseStep 2339603 = 3509405) B3509405
theorem B1561363 : Blo 1559477 1561363 := bstep (se 1 (by rfl) ⟨1171022, by rfl⟩ : syracuseStep 1561363 = 2342045) B2342045
theorem B1561379 : Blo 1559477 1561379 := bstep (se 1 (by rfl) ⟨1171034, by rfl⟩ : syracuseStep 1561379 = 2342069) B2342069
theorem B2339633 : Blo 1559477 2339633 := bstep (se 2 (by rfl) ⟨877362, by rfl⟩ : syracuseStep 2339633 = 1754725) B1754725
theorem B2634545 : Blo 1559477 2634545 := bstep (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) B1975909
theorem B1561395 : Blo 1559477 1561395 := bstep (se 1 (by rfl) ⟨1171046, by rfl⟩ : syracuseStep 1561395 = 2342093) B2342093
theorem B2339651 : Blo 1559477 2339651 := bstep (se 1 (by rfl) ⟨1754738, by rfl⟩ : syracuseStep 2339651 = 3509477) B3509477
theorem B1561411 : Blo 1559477 1561411 := bstep (se 1 (by rfl) ⟨1171058, by rfl⟩ : syracuseStep 1561411 = 2342117) B2342117
theorem B4502353 : Blo 1559477 4502353 := bstep (se 2 (by rfl) ⟨1688382, by rfl⟩ : syracuseStep 4502353 = 3376765) B3376765
theorem B1561427 : Blo 1559477 1561427 := bstep (se 1 (by rfl) ⟨1171070, by rfl⟩ : syracuseStep 1561427 = 2342141) B2342141
theorem B2339681 : Blo 1559477 2339681 := bstep (se 2 (by rfl) ⟨877380, by rfl⟩ : syracuseStep 2339681 = 1754761) B1754761
theorem B1561443 : Blo 1559477 1561443 := bstep (se 1 (by rfl) ⟨1171082, by rfl⟩ : syracuseStep 1561443 = 2342165) B2342165
theorem B7115633 : Blo 1559477 7115633 := bstep (se 2 (by rfl) ⟨2668362, by rfl⟩ : syracuseStep 7115633 = 5336725) B5336725
theorem B2339699 : Blo 1559477 2339699 := bstep (se 1 (by rfl) ⟨1754774, by rfl⟩ : syracuseStep 2339699 = 3509549) B3509549
theorem B1561459 : Blo 1559477 1561459 := bstep (se 1 (by rfl) ⟨1171094, by rfl⟩ : syracuseStep 1561459 = 2342189) B2342189
theorem B2962307 : Blo 1559477 2962307 := bstep (se 1 (by rfl) ⟨2221730, by rfl⟩ : syracuseStep 2962307 = 4443461) B4443461
theorem B1561475 : Blo 1559477 1561475 := bstep (se 1 (by rfl) ⟨1171106, by rfl⟩ : syracuseStep 1561475 = 2342213) B2342213
theorem B2339729 : Blo 1559477 2339729 := bstep (se 2 (by rfl) ⟨877398, by rfl⟩ : syracuseStep 2339729 = 1754797) B1754797
theorem B2339747 : Blo 1559477 2339747 := bstep (se 1 (by rfl) ⟨1754810, by rfl⟩ : syracuseStep 2339747 = 3509621) B3509621
theorem B2634673 : Blo 1559477 2634673 := bstep (se 2 (by rfl) ⟨988002, by rfl⟩ : syracuseStep 2634673 = 1976005) B1976005
theorem B2339777 : Blo 1559477 2339777 := bstep (se 2 (by rfl) ⟨877416, by rfl⟩ : syracuseStep 2339777 = 1754833) B1754833
theorem B2339795 : Blo 1559477 2339795 := bstep (se 1 (by rfl) ⟨1754846, by rfl⟩ : syracuseStep 2339795 = 3509693) B3509693
theorem B2634707 : Blo 1559477 2634707 := bstep (se 1 (by rfl) ⟨1976030, by rfl⟩ : syracuseStep 2634707 = 3952061) B3952061
theorem B2339825 : Blo 1559477 2339825 := bstep (se 2 (by rfl) ⟨877434, by rfl⟩ : syracuseStep 2339825 = 1754869) B1754869
theorem B2339843 : Blo 1559477 2339843 := bstep (se 1 (by rfl) ⟨1754882, by rfl⟩ : syracuseStep 2339843 = 3509765) B3509765
theorem B3511313 : Blo 1559477 3511313 := bstep (se 2 (by rfl) ⟨1316742, by rfl⟩ : syracuseStep 3511313 = 2633485) B2633485
theorem B2339873 : Blo 1559477 2339873 := bstep (se 2 (by rfl) ⟨877452, by rfl⟩ : syracuseStep 2339873 = 1754905) B1754905
theorem B3511331 : Blo 1559477 3511331 := bstep (se 1 (by rfl) ⟨2633498, by rfl⟩ : syracuseStep 3511331 = 5266997) B5266997
theorem B2339891 : Blo 1559477 2339891 := bstep (se 1 (by rfl) ⟨1754918, by rfl⟩ : syracuseStep 2339891 = 3509837) B3509837
theorem B2339921 : Blo 1559477 2339921 := bstep (se 2 (by rfl) ⟨877470, by rfl⟩ : syracuseStep 2339921 = 1754941) B1754941
theorem B2634835 : Blo 1559477 2634835 := bstep (se 1 (by rfl) ⟨1976126, by rfl⟩ : syracuseStep 2634835 = 3952253) B3952253
theorem B2339939 : Blo 1559477 2339939 := bstep (se 1 (by rfl) ⟨1754954, by rfl⟩ : syracuseStep 2339939 = 3509909) B3509909
theorem B43308145 : Blo 1559477 43308145 := bstep (se 2 (by rfl) ⟨16240554, by rfl⟩ : syracuseStep 43308145 = 32481109) B32481109
theorem B2339969 : Blo 1559477 2339969 := bstep (se 2 (by rfl) ⟨877488, by rfl⟩ : syracuseStep 2339969 = 1754977) B1754977
theorem B2339987 : Blo 1559477 2339987 := bstep (se 1 (by rfl) ⟨1754990, by rfl⟩ : syracuseStep 2339987 = 3509981) B3509981
theorem B2962595 : Blo 1559477 2962595 := bstep (se 1 (by rfl) ⟨2221946, by rfl⟩ : syracuseStep 2962595 = 4443893) B4443893
theorem B2340017 : Blo 1559477 2340017 := bstep (se 2 (by rfl) ⟨877506, by rfl⟩ : syracuseStep 2340017 = 1755013) B1755013
theorem B2340035 : Blo 1559477 2340035 := bstep (se 1 (by rfl) ⟨1755026, by rfl⟩ : syracuseStep 2340035 = 3510053) B3510053
theorem B9999557 : Blo 1559477 9999557 := bstep (se 4 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 9999557 = 1874917) B1874917
theorem B22508741 : Blo 1559477 22508741 := bstep (se 4 (by rfl) ⟨2110194, by rfl⟩ : syracuseStep 22508741 = 4220389) B4220389
theorem B2340065 : Blo 1559477 2340065 := bstep (se 2 (by rfl) ⟨877524, by rfl⟩ : syracuseStep 2340065 = 1755049) B1755049
theorem B2634977 : Blo 1559477 2634977 := bstep (se 2 (by rfl) ⟨988116, by rfl⟩ : syracuseStep 2634977 = 1976233) B1976233
theorem B5264621 : Blo 1559477 5264621 := bstep (se 3 (by rfl) ⟨987116, by rfl⟩ : syracuseStep 5264621 = 1974233) B1974233
theorem B2340083 : Blo 1559477 2340083 := bstep (se 1 (by rfl) ⟨1755062, by rfl⟩ : syracuseStep 2340083 = 3510125) B3510125
theorem B2372851 : Blo 1559477 2372851 := bstep (se 1 (by rfl) ⟨1779638, by rfl⟩ : syracuseStep 2372851 = 3559277) B3559277
theorem B2340113 : Blo 1559477 2340113 := bstep (se 2 (by rfl) ⟨877542, by rfl⟩ : syracuseStep 2340113 = 1755085) B1755085
theorem B5264675 : Blo 1559477 5264675 := bstep (se 1 (by rfl) ⟨3948506, by rfl⟩ : syracuseStep 5264675 = 7897013) B7897013
theorem B2340131 : Blo 1559477 2340131 := bstep (se 1 (by rfl) ⟨1755098, by rfl⟩ : syracuseStep 2340131 = 3510197) B3510197
theorem B3511601 : Blo 1559477 3511601 := bstep (se 2 (by rfl) ⟨1316850, by rfl⟩ : syracuseStep 3511601 = 2633701) B2633701
theorem B2340161 : Blo 1559477 2340161 := bstep (se 2 (by rfl) ⟨877560, by rfl⟩ : syracuseStep 2340161 = 1755121) B1755121
theorem B3511619 : Blo 1559477 3511619 := bstep (se 1 (by rfl) ⟨2633714, by rfl⟩ : syracuseStep 3511619 = 5267429) B5267429
theorem B2340179 : Blo 1559477 2340179 := bstep (se 1 (by rfl) ⟨1755134, by rfl⟩ : syracuseStep 2340179 = 3510269) B3510269
theorem B2168147 : Blo 1559477 2168147 := bstep (se 1 (by rfl) ⟨1626110, by rfl⟩ : syracuseStep 2168147 = 3252221) B3252221
theorem B2340209 : Blo 1559477 2340209 := bstep (se 2 (by rfl) ⟨877578, by rfl⟩ : syracuseStep 2340209 = 1755157) B1755157
theorem B2340227 : Blo 1559477 2340227 := bstep (se 1 (by rfl) ⟨1755170, by rfl⟩ : syracuseStep 2340227 = 3510341) B3510341
theorem B8885645 : Blo 1559477 8885645 := bstep (se 3 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 8885645 = 3332117) B3332117
theorem B2340257 : Blo 1559477 2340257 := bstep (se 2 (by rfl) ⟨877596, by rfl⟩ : syracuseStep 2340257 = 1755193) B1755193
theorem B2340275 : Blo 1559477 2340275 := bstep (se 1 (by rfl) ⟨1755206, by rfl⟩ : syracuseStep 2340275 = 3510413) B3510413
theorem B160339397 : Blo 1559477 160339397 := bstep (se 4 (by rfl) ⟨15031818, by rfl⟩ : syracuseStep 160339397 = 30063637) B30063637
theorem B2340305 : Blo 1559477 2340305 := bstep (se 2 (by rfl) ⟨877614, by rfl⟩ : syracuseStep 2340305 = 1755229) B1755229
theorem B2340323 : Blo 1559477 2340323 := bstep (se 1 (by rfl) ⟨1755242, by rfl⟩ : syracuseStep 2340323 = 3510485) B3510485
theorem B2340353 : Blo 1559477 2340353 := bstep (se 2 (by rfl) ⟨877632, by rfl⟩ : syracuseStep 2340353 = 1755265) B1755265
theorem B2340371 : Blo 1559477 2340371 := bstep (se 1 (by rfl) ⟨1755278, by rfl⟩ : syracuseStep 2340371 = 3510557) B3510557
theorem B4216369 : Blo 1559477 4216369 := bstep (se 2 (by rfl) ⟨1581138, by rfl⟩ : syracuseStep 4216369 = 3162277) B3162277
theorem B5264945 : Blo 1559477 5264945 := bstep (se 2 (by rfl) ⟨1974354, by rfl⟩ : syracuseStep 5264945 = 3948709) B3948709
theorem B2340401 : Blo 1559477 2340401 := bstep (se 2 (by rfl) ⟨877650, by rfl⟩ : syracuseStep 2340401 = 1755301) B1755301
theorem B44987957 : Blo 1559477 44987957 := bstep (se 5 (by rfl) ⟨2108810, by rfl⟩ : syracuseStep 44987957 = 4217621) B4217621
theorem B2340419 : Blo 1559477 2340419 := bstep (se 1 (by rfl) ⟨1755314, by rfl⟩ : syracuseStep 2340419 = 3510629) B3510629
theorem B3511889 : Blo 1559477 3511889 := bstep (se 2 (by rfl) ⟨1316958, by rfl⟩ : syracuseStep 3511889 = 2633917) B2633917
theorem B2340449 : Blo 1559477 2340449 := bstep (se 2 (by rfl) ⟨877668, by rfl⟩ : syracuseStep 2340449 = 1755337) B1755337
theorem B3511907 : Blo 1559477 3511907 := bstep (se 1 (by rfl) ⟨2633930, by rfl⟩ : syracuseStep 3511907 = 5267861) B5267861
theorem B5625443 : Blo 1559477 5625443 := bstep (se 1 (by rfl) ⟨4219082, by rfl⟩ : syracuseStep 5625443 = 8438165) B8438165
theorem B2438755 : Blo 1559477 2438755 := bstep (se 1 (by rfl) ⟨1829066, by rfl⟩ : syracuseStep 2438755 = 3658133) B3658133
theorem B2340467 : Blo 1559477 2340467 := bstep (se 1 (by rfl) ⟨1755350, by rfl⟩ : syracuseStep 2340467 = 3510701) B3510701
theorem B39982733 : Blo 1559477 39982733 := bstep (se 3 (by rfl) ⟨7496762, by rfl⟩ : syracuseStep 39982733 = 14993525) B14993525
theorem B2340497 : Blo 1559477 2340497 := bstep (se 2 (by rfl) ⟨877686, by rfl⟩ : syracuseStep 2340497 = 1755373) B1755373
theorem B2340515 : Blo 1559477 2340515 := bstep (se 1 (by rfl) ⟨1755386, by rfl⟩ : syracuseStep 2340515 = 3510773) B3510773
theorem B8115889 : Blo 1559477 8115889 := bstep (se 2 (by rfl) ⟨3043458, by rfl⟩ : syracuseStep 8115889 = 6086917) B6086917
theorem B16864949 : Blo 1559477 16864949 := bstep (se 5 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 16864949 = 1581089) B1581089
theorem B2340545 : Blo 1559477 2340545 := bstep (se 2 (by rfl) ⟨877704, by rfl⟩ : syracuseStep 2340545 = 1755409) B1755409
theorem B5928653 : Blo 1559477 5928653 := bstep (se 3 (by rfl) ⟨1111622, by rfl⟩ : syracuseStep 5928653 = 2223245) B2223245
theorem B3331793 : Blo 1559477 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B2340563 : Blo 1559477 2340563 := bstep (se 1 (by rfl) ⟨1755422, by rfl⟩ : syracuseStep 2340563 = 3510845) B3510845
theorem B2340593 : Blo 1559477 2340593 := bstep (se 2 (by rfl) ⟨877722, by rfl⟩ : syracuseStep 2340593 = 1755445) B1755445
theorem B2340611 : Blo 1559477 2340611 := bstep (se 1 (by rfl) ⟨1755458, by rfl⟩ : syracuseStep 2340611 = 3510917) B3510917
theorem B2340641 : Blo 1559477 2340641 := bstep (se 2 (by rfl) ⟨877740, by rfl⟩ : syracuseStep 2340641 = 1755481) B1755481
theorem B2340659 : Blo 1559477 2340659 := bstep (se 1 (by rfl) ⟨1755494, by rfl⟩ : syracuseStep 2340659 = 3510989) B3510989
theorem B2340689 : Blo 1559477 2340689 := bstep (se 2 (by rfl) ⟨877758, by rfl⟩ : syracuseStep 2340689 = 1755517) B1755517
theorem B2340707 : Blo 1559477 2340707 := bstep (se 1 (by rfl) ⟨1755530, by rfl⟩ : syracuseStep 2340707 = 3511061) B3511061
theorem B6666097 : Blo 1559477 6666097 := bstep (se 2 (by rfl) ⟨2499786, by rfl⟩ : syracuseStep 6666097 = 4999573) B4999573
theorem B3512177 : Blo 1559477 3512177 := bstep (se 2 (by rfl) ⟨1317066, by rfl⟩ : syracuseStep 3512177 = 2634133) B2634133
theorem B2340737 : Blo 1559477 2340737 := bstep (se 2 (by rfl) ⟨877776, by rfl⟩ : syracuseStep 2340737 = 1755553) B1755553
theorem B3512195 : Blo 1559477 3512195 := bstep (se 1 (by rfl) ⟨2634146, by rfl⟩ : syracuseStep 3512195 = 5268293) B5268293
theorem B17774477 : Blo 1559477 17774477 := bstep (se 3 (by rfl) ⟨3332714, by rfl⟩ : syracuseStep 17774477 = 6665429) B6665429
theorem B2340755 : Blo 1559477 2340755 := bstep (se 1 (by rfl) ⟨1755566, by rfl⟩ : syracuseStep 2340755 = 3511133) B3511133
theorem B2340785 : Blo 1559477 2340785 := bstep (se 2 (by rfl) ⟨877794, by rfl⟩ : syracuseStep 2340785 = 1755589) B1755589
theorem B2340803 : Blo 1559477 2340803 := bstep (se 1 (by rfl) ⟨1755602, by rfl⟩ : syracuseStep 2340803 = 3511205) B3511205
theorem B4446161 : Blo 1559477 4446161 := bstep (se 2 (by rfl) ⟨1667310, by rfl⟩ : syracuseStep 4446161 = 3334621) B3334621
theorem B2340833 : Blo 1559477 2340833 := bstep (se 2 (by rfl) ⟨877812, by rfl⟩ : syracuseStep 2340833 = 1755625) B1755625
theorem B2340851 : Blo 1559477 2340851 := bstep (se 1 (by rfl) ⟨1755638, by rfl⟩ : syracuseStep 2340851 = 3511277) B3511277
theorem B3799057 : Blo 1559477 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B2340881 : Blo 1559477 2340881 := bstep (se 2 (by rfl) ⟨877830, by rfl⟩ : syracuseStep 2340881 = 1755661) B1755661
theorem B2340899 : Blo 1559477 2340899 := bstep (se 1 (by rfl) ⟨1755674, by rfl⟩ : syracuseStep 2340899 = 3511349) B3511349
theorem B3004465 : Blo 1559477 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B2340929 : Blo 1559477 2340929 := bstep (se 2 (by rfl) ⟨877848, by rfl⟩ : syracuseStep 2340929 = 1755697) B1755697
theorem B5265485 : Blo 1559477 5265485 := bstep (se 3 (by rfl) ⟨987278, by rfl⟩ : syracuseStep 5265485 = 1974557) B1974557
theorem B2963537 : Blo 1559477 2963537 := bstep (se 2 (by rfl) ⟨1111326, by rfl⟩ : syracuseStep 2963537 = 2222653) B2222653
theorem B2340947 : Blo 1559477 2340947 := bstep (se 1 (by rfl) ⟨1755710, by rfl⟩ : syracuseStep 2340947 = 3511421) B3511421
theorem B7903331 : Blo 1559477 7903331 := bstep (se 1 (by rfl) ⟨5927498, by rfl⟩ : syracuseStep 7903331 = 11854997) B11854997
theorem B2340977 : Blo 1559477 2340977 := bstep (se 2 (by rfl) ⟨877866, by rfl⟩ : syracuseStep 2340977 = 1755733) B1755733
theorem B5265539 : Blo 1559477 5265539 := bstep (se 1 (by rfl) ⟨3949154, by rfl⟩ : syracuseStep 5265539 = 7898309) B7898309
theorem B2340995 : Blo 1559477 2340995 := bstep (se 1 (by rfl) ⟨1755746, by rfl⟩ : syracuseStep 2340995 = 3511493) B3511493
theorem B3512465 : Blo 1559477 3512465 := bstep (se 2 (by rfl) ⟨1317174, by rfl⟩ : syracuseStep 3512465 = 2634349) B2634349
theorem B4446353 : Blo 1559477 4446353 := bstep (se 2 (by rfl) ⟨1667382, by rfl⟩ : syracuseStep 4446353 = 3334765) B3334765
theorem B2341025 : Blo 1559477 2341025 := bstep (se 2 (by rfl) ⟨877884, by rfl⟩ : syracuseStep 2341025 = 1755769) B1755769
theorem B3512483 : Blo 1559477 3512483 := bstep (se 1 (by rfl) ⟨2634362, by rfl⟩ : syracuseStep 3512483 = 5268725) B5268725
theorem B2341043 : Blo 1559477 2341043 := bstep (se 1 (by rfl) ⟨1755782, by rfl⟩ : syracuseStep 2341043 = 3511565) B3511565
theorem B2341073 : Blo 1559477 2341073 := bstep (se 2 (by rfl) ⟨877902, by rfl⟩ : syracuseStep 2341073 = 1755805) B1755805
theorem B2341091 : Blo 1559477 2341091 := bstep (se 1 (by rfl) ⟨1755818, by rfl⟩ : syracuseStep 2341091 = 3511637) B3511637
theorem B2668801 : Blo 1559477 2668801 := bstep (se 2 (by rfl) ⟨1000800, by rfl⟩ : syracuseStep 2668801 = 2001601) B2001601
theorem B2341121 : Blo 1559477 2341121 := bstep (se 2 (by rfl) ⟨877920, by rfl⟩ : syracuseStep 2341121 = 1755841) B1755841
theorem B2341139 : Blo 1559477 2341139 := bstep (se 1 (by rfl) ⟨1755854, by rfl⟩ : syracuseStep 2341139 = 3511709) B3511709
theorem B2341169 : Blo 1559477 2341169 := bstep (se 2 (by rfl) ⟨877938, by rfl⟩ : syracuseStep 2341169 = 1755877) B1755877
theorem B7502129 : Blo 1559477 7502129 := bstep (se 2 (by rfl) ⟨2813298, by rfl⟩ : syracuseStep 7502129 = 5626597) B5626597
theorem B2341187 : Blo 1559477 2341187 := bstep (se 1 (by rfl) ⟨1755890, by rfl⟩ : syracuseStep 2341187 = 3511781) B3511781
theorem B2341217 : Blo 1559477 2341217 := bstep (se 2 (by rfl) ⟨877956, by rfl⟩ : syracuseStep 2341217 = 1755913) B1755913
theorem B2341235 : Blo 1559477 2341235 := bstep (se 1 (by rfl) ⟨1755926, by rfl⟩ : syracuseStep 2341235 = 3511853) B3511853
theorem B8436109 : Blo 1559477 8436109 := bstep (se 3 (by rfl) ⟨1581770, by rfl⟩ : syracuseStep 8436109 = 3163541) B3163541
theorem B5265809 : Blo 1559477 5265809 := bstep (se 2 (by rfl) ⟨1974678, by rfl⟩ : syracuseStep 5265809 = 3949357) B3949357
theorem B2341265 : Blo 1559477 2341265 := bstep (se 2 (by rfl) ⟨877974, by rfl⟩ : syracuseStep 2341265 = 1755949) B1755949
theorem B2341283 : Blo 1559477 2341283 := bstep (se 1 (by rfl) ⟨1755962, by rfl⟩ : syracuseStep 2341283 = 3511925) B3511925
theorem B3512753 : Blo 1559477 3512753 := bstep (se 2 (by rfl) ⟨1317282, by rfl⟩ : syracuseStep 3512753 = 2634565) B2634565
theorem B2341313 : Blo 1559477 2341313 := bstep (se 2 (by rfl) ⟨877992, by rfl⟩ : syracuseStep 2341313 = 1755985) B1755985
theorem B3512771 : Blo 1559477 3512771 := bstep (se 1 (by rfl) ⟨2634578, by rfl⟩ : syracuseStep 3512771 = 5269157) B5269157
theorem B2341331 : Blo 1559477 2341331 := bstep (se 1 (by rfl) ⟨1755998, by rfl⟩ : syracuseStep 2341331 = 3511997) B3511997
theorem B2341361 : Blo 1559477 2341361 := bstep (se 2 (by rfl) ⟨878010, by rfl⟩ : syracuseStep 2341361 = 1756021) B1756021
theorem B2341379 : Blo 1559477 2341379 := bstep (se 1 (by rfl) ⟨1756034, by rfl⟩ : syracuseStep 2341379 = 3512069) B3512069
theorem B2341409 : Blo 1559477 2341409 := bstep (se 2 (by rfl) ⟨878028, by rfl⟩ : syracuseStep 2341409 = 1756057) B1756057
theorem B2341427 : Blo 1559477 2341427 := bstep (se 1 (by rfl) ⟨1756070, by rfl⟩ : syracuseStep 2341427 = 3512141) B3512141
theorem B2669123 : Blo 1559477 2669123 := bstep (se 1 (by rfl) ⟨2001842, by rfl⟩ : syracuseStep 2669123 = 4003685) B4003685
theorem B2341457 : Blo 1559477 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B2341475 : Blo 1559477 2341475 := bstep (se 1 (by rfl) ⟨1756106, by rfl⟩ : syracuseStep 2341475 = 3512213) B3512213
theorem B4504177 : Blo 1559477 4504177 := bstep (se 2 (by rfl) ⟨1689066, by rfl⟩ : syracuseStep 4504177 = 3378133) B3378133
theorem B2341505 : Blo 1559477 2341505 := bstep (se 2 (by rfl) ⟨878064, by rfl⟩ : syracuseStep 2341505 = 1756129) B1756129
theorem B2341523 : Blo 1559477 2341523 := bstep (se 1 (by rfl) ⟨1756142, by rfl⟩ : syracuseStep 2341523 = 3512285) B3512285
theorem B2341553 : Blo 1559477 2341553 := bstep (se 2 (by rfl) ⟨878082, by rfl⟩ : syracuseStep 2341553 = 1756165) B1756165
theorem B2341571 : Blo 1559477 2341571 := bstep (se 1 (by rfl) ⟨1756178, by rfl⟩ : syracuseStep 2341571 = 3512357) B3512357
theorem B3513041 : Blo 1559477 3513041 := bstep (se 2 (by rfl) ⟨1317390, by rfl⟩ : syracuseStep 3513041 = 2634781) B2634781
theorem B2341601 : Blo 1559477 2341601 := bstep (se 2 (by rfl) ⟨878100, by rfl⟩ : syracuseStep 2341601 = 1756201) B1756201
theorem B3513059 : Blo 1559477 3513059 := bstep (se 1 (by rfl) ⟨2634794, by rfl⟩ : syracuseStep 3513059 = 5269589) B5269589
theorem B2341619 : Blo 1559477 2341619 := bstep (se 1 (by rfl) ⟨1756214, by rfl⟩ : syracuseStep 2341619 = 3512429) B3512429
theorem B2341649 : Blo 1559477 2341649 := bstep (se 2 (by rfl) ⟨878118, by rfl⟩ : syracuseStep 2341649 = 1756237) B1756237
theorem B2341667 : Blo 1559477 2341667 := bstep (se 1 (by rfl) ⟨1756250, by rfl⟩ : syracuseStep 2341667 = 3512501) B3512501
theorem B4274993 : Blo 1559477 4274993 := bstep (se 2 (by rfl) ⟨1603122, by rfl⟩ : syracuseStep 4274993 = 3206245) B3206245
theorem B2341697 : Blo 1559477 2341697 := bstep (se 2 (by rfl) ⟨878136, by rfl⟩ : syracuseStep 2341697 = 1756273) B1756273
theorem B2341715 : Blo 1559477 2341715 := bstep (se 1 (by rfl) ⟨1756286, by rfl⟩ : syracuseStep 2341715 = 3512573) B3512573
theorem B2341745 : Blo 1559477 2341745 := bstep (se 2 (by rfl) ⟨878154, by rfl⟩ : syracuseStep 2341745 = 1756309) B1756309
theorem B2341763 : Blo 1559477 2341763 := bstep (se 1 (by rfl) ⟨1756322, by rfl⟩ : syracuseStep 2341763 = 3512645) B3512645
theorem B22502285 : Blo 1559477 22502285 := bstep (se 3 (by rfl) ⟨4219178, by rfl⟩ : syracuseStep 22502285 = 8438357) B8438357
theorem B7904141 : Blo 1559477 7904141 := bstep (se 3 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 7904141 = 2964053) B2964053
theorem B2341793 : Blo 1559477 2341793 := bstep (se 2 (by rfl) ⟨878172, by rfl⟩ : syracuseStep 2341793 = 1756345) B1756345
theorem B5266349 : Blo 1559477 5266349 := bstep (se 3 (by rfl) ⟨987440, by rfl⟩ : syracuseStep 5266349 = 1974881) B1974881
theorem B2341811 : Blo 1559477 2341811 := bstep (se 1 (by rfl) ⟨1756358, by rfl⟩ : syracuseStep 2341811 = 3512717) B3512717
theorem B25295813 : Blo 1559477 25295813 := bstep (se 4 (by rfl) ⟨2371482, by rfl⟩ : syracuseStep 25295813 = 4742965) B4742965
theorem B2341841 : Blo 1559477 2341841 := bstep (se 2 (by rfl) ⟨878190, by rfl⟩ : syracuseStep 2341841 = 1756381) B1756381
theorem B5266403 : Blo 1559477 5266403 := bstep (se 1 (by rfl) ⟨3949802, by rfl⟩ : syracuseStep 5266403 = 7899605) B7899605
theorem B3333091 : Blo 1559477 3333091 := bstep (se 1 (by rfl) ⟨2499818, by rfl⟩ : syracuseStep 3333091 = 4999637) B4999637
theorem B2341859 : Blo 1559477 2341859 := bstep (se 1 (by rfl) ⟨1756394, by rfl⟩ : syracuseStep 2341859 = 3512789) B3512789
theorem B2341889 : Blo 1559477 2341889 := bstep (se 2 (by rfl) ⟨878208, by rfl⟩ : syracuseStep 2341889 = 1756417) B1756417
theorem B2341907 : Blo 1559477 2341907 := bstep (se 1 (by rfl) ⟨1756430, by rfl⟩ : syracuseStep 2341907 = 3512861) B3512861
theorem B3947555 : Blo 1559477 3947555 := bstep (se 1 (by rfl) ⟨2960666, by rfl⟩ : syracuseStep 3947555 = 5921333) B5921333
theorem B2341937 : Blo 1559477 2341937 := bstep (se 2 (by rfl) ⟨878226, by rfl⟩ : syracuseStep 2341937 = 1756453) B1756453
theorem B5340227 : Blo 1559477 5340227 := bstep (se 1 (by rfl) ⟨4005170, by rfl⟩ : syracuseStep 5340227 = 8010341) B8010341
theorem B2341955 : Blo 1559477 2341955 := bstep (se 1 (by rfl) ⟨1756466, by rfl⟩ : syracuseStep 2341955 = 3512933) B3512933
theorem B2341985 : Blo 1559477 2341985 := bstep (se 2 (by rfl) ⟨878244, by rfl⟩ : syracuseStep 2341985 = 1756489) B1756489
theorem B2342003 : Blo 1559477 2342003 := bstep (se 1 (by rfl) ⟨1756502, by rfl⟩ : syracuseStep 2342003 = 3513005) B3513005
theorem B2342033 : Blo 1559477 2342033 := bstep (se 2 (by rfl) ⟨878262, by rfl⟩ : syracuseStep 2342033 = 1756525) B1756525
theorem B2342051 : Blo 1559477 2342051 := bstep (se 1 (by rfl) ⟨1756538, by rfl⟩ : syracuseStep 2342051 = 3513077) B3513077
theorem B2342081 : Blo 1559477 2342081 := bstep (se 2 (by rfl) ⟨878280, by rfl⟩ : syracuseStep 2342081 = 1756561) B1756561
theorem B2342099 : Blo 1559477 2342099 := bstep (se 1 (by rfl) ⟨1756574, by rfl⟩ : syracuseStep 2342099 = 3513149) B3513149
theorem B13335779 : Blo 1559477 13335779 := bstep (se 1 (by rfl) ⟨10001834, by rfl⟩ : syracuseStep 13335779 = 20003669) B20003669
theorem B5266673 : Blo 1559477 5266673 := bstep (se 2 (by rfl) ⟨1975002, by rfl⟩ : syracuseStep 5266673 = 3950005) B3950005
theorem B2342129 : Blo 1559477 2342129 := bstep (se 2 (by rfl) ⟨878298, by rfl⟩ : syracuseStep 2342129 = 1756597) B1756597
theorem B2342147 : Blo 1559477 2342147 := bstep (se 1 (by rfl) ⟨1756610, by rfl⟩ : syracuseStep 2342147 = 3513221) B3513221
theorem B2342177 : Blo 1559477 2342177 := bstep (se 2 (by rfl) ⟨878316, by rfl⟩ : syracuseStep 2342177 = 1756633) B1756633
theorem B2850083 : Blo 1559477 2850083 := bstep (se 1 (by rfl) ⟨2137562, by rfl⟩ : syracuseStep 2850083 = 4275125) B4275125
theorem B2342195 : Blo 1559477 2342195 := bstep (se 1 (by rfl) ⟨1756646, by rfl⟩ : syracuseStep 2342195 = 3513293) B3513293
theorem B4996561 : Blo 1559477 4996561 := bstep (se 2 (by rfl) ⟨1873710, by rfl⟩ : syracuseStep 4996561 = 3747421) B3747421
theorem B1973747 : Blo 1559477 1973747 := bstep (se 1 (by rfl) ⟨1480310, by rfl⟩ : syracuseStep 1973747 = 2960621) B2960621
theorem B8887877 : Blo 1559477 8887877 := bstep (se 4 (by rfl) ⟨833238, by rfl⟩ : syracuseStep 8887877 = 1666477) B1666477
theorem B7896689 : Blo 1559477 7896689 := bstep (se 2 (by rfl) ⟨2961258, by rfl⟩ : syracuseStep 7896689 = 5922517) B5922517
theorem B4996817 : Blo 1559477 4996817 := bstep (se 2 (by rfl) ⟨1873806, by rfl⟩ : syracuseStep 4996817 = 3747613) B3747613
theorem B11853539 : Blo 1559477 11853539 := bstep (se 1 (by rfl) ⟨8890154, by rfl⟩ : syracuseStep 11853539 = 17780309) B17780309
theorem B5775089 : Blo 1559477 5775089 := bstep (se 2 (by rfl) ⟨2165658, by rfl⟩ : syracuseStep 5775089 = 4331317) B4331317
theorem B5267213 : Blo 1559477 5267213 := bstep (se 3 (by rfl) ⟨987602, by rfl⟩ : syracuseStep 5267213 = 1975205) B1975205
theorem B4505357 : Blo 1559477 4505357 := bstep (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) B1689509
theorem B5267267 : Blo 1559477 5267267 := bstep (se 1 (by rfl) ⟨3950450, by rfl⟩ : syracuseStep 5267267 = 7900901) B7900901
theorem B2498435 : Blo 1559477 2498435 := bstep (se 1 (by rfl) ⟨1873826, by rfl⟩ : syracuseStep 2498435 = 3747653) B3747653
theorem B24027077 : Blo 1559477 24027077 := bstep (se 4 (by rfl) ⟨2252538, by rfl⟩ : syracuseStep 24027077 = 4505077) B4505077
theorem B5341133 : Blo 1559477 5341133 := bstep (se 3 (by rfl) ⟨1001462, by rfl⟩ : syracuseStep 5341133 = 2002925) B2002925
theorem B3948497 : Blo 1559477 3948497 := bstep (se 2 (by rfl) ⟨1480686, by rfl⟩ : syracuseStep 3948497 = 2961373) B2961373
theorem B2670545 : Blo 1559477 2670545 := bstep (se 2 (by rfl) ⟨1001454, by rfl⟩ : syracuseStep 2670545 = 2002909) B2002909
theorem B9994225 : Blo 1559477 9994225 := bstep (se 2 (by rfl) ⟨3747834, by rfl⟩ : syracuseStep 9994225 = 7495669) B7495669
theorem B4005953 : Blo 1559477 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B11845763 : Blo 1559477 11845763 := bstep (se 1 (by rfl) ⟨8884322, by rfl⟩ : syracuseStep 11845763 = 17768645) B17768645
theorem B5922989 : Blo 1559477 5922989 := bstep (se 3 (by rfl) ⟨1110560, by rfl⟩ : syracuseStep 5922989 = 2221121) B2221121
theorem B3948851 : Blo 1559477 3948851 := bstep (se 1 (by rfl) ⟨2961638, by rfl⟩ : syracuseStep 3948851 = 5923277) B5923277
theorem B12656989 : Blo 1559477 12656989 := bstep (se 3 (by rfl) ⟨2373185, by rfl⟩ : syracuseStep 12656989 = 4746371) B4746371
theorem B5267915 : Blo 1559477 5267915 := bstep (se 1 (by rfl) ⟨3950936, by rfl⟩ : syracuseStep 5267915 = 7901873) B7901873
theorem B11248145 : Blo 1559477 11248145 := bstep (se 2 (by rfl) ⟨4218054, by rfl⟩ : syracuseStep 11248145 = 8436109) B8436109
theorem B4743755 : Blo 1559477 4743755 := bstep (se 1 (by rfl) ⟨3557816, by rfl⟩ : syracuseStep 4743755 = 7115633) B7115633
theorem B1974871 : Blo 1559477 1974871 := bstep (se 1 (by rfl) ⟨1481153, by rfl⟩ : syracuseStep 1974871 = 2962307) B2962307
theorem B3949145 : Blo 1559477 3949145 := bstep (se 2 (by rfl) ⟨1480929, by rfl⟩ : syracuseStep 3949145 = 2961859) B2961859
theorem B8553053 : Blo 1559477 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B3162763 : Blo 1559477 3162763 := bstep (se 1 (by rfl) ⟨2372072, by rfl⟩ : syracuseStep 3162763 = 4744145) B4744145
theorem B5268185 : Blo 1559477 5268185 := bstep (se 2 (by rfl) ⟨1975569, by rfl⟩ : syracuseStep 5268185 = 3951139) B3951139
theorem B1688375 : Blo 1559477 1688375 := bstep (se 1 (by rfl) ⟨1266281, by rfl⟩ : syracuseStep 1688375 = 2532563) B2532563
theorem B9487169 : Blo 1559477 9487169 := bstep (se 2 (by rfl) ⟨3557688, by rfl⟩ : syracuseStep 9487169 = 7115377) B7115377
theorem B13337419 : Blo 1559477 13337419 := bstep (se 1 (by rfl) ⟨10003064, by rfl⟩ : syracuseStep 13337419 = 20006129) B20006129
theorem B5923763 : Blo 1559477 5923763 := bstep (se 1 (by rfl) ⟨4442822, by rfl⟩ : syracuseStep 5923763 = 8885645) B8885645
theorem B29991971 : Blo 1559477 29991971 := bstep (se 1 (by rfl) ⟨22493978, by rfl⟩ : syracuseStep 29991971 = 44987957) B44987957
theorem B13337693 : Blo 1559477 13337693 := bstep (se 3 (by rfl) ⟨2500817, by rfl⟩ : syracuseStep 13337693 = 5001635) B5001635
theorem B2221195 : Blo 1559477 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B3376307 : Blo 1559477 3376307 := bstep (se 1 (by rfl) ⟨2532230, by rfl⟩ : syracuseStep 3376307 = 5064461) B5064461
theorem B2852171 : Blo 1559477 2852171 := bstep (se 1 (by rfl) ⟨2139128, by rfl⟩ : syracuseStep 2852171 = 4278257) B4278257
theorem B1754455 : Blo 1559477 1754455 := bstep (se 1 (by rfl) ⟨1315841, by rfl⟩ : syracuseStep 1754455 = 2631683) B2631683
theorem B3376471 : Blo 1559477 3376471 := bstep (se 1 (by rfl) ⟨2532353, by rfl⟩ : syracuseStep 3376471 = 5064707) B5064707
theorem B3376523 : Blo 1559477 3376523 := bstep (se 1 (by rfl) ⟨2532392, by rfl⟩ : syracuseStep 3376523 = 5064785) B5064785
theorem B1975691 : Blo 1559477 1975691 := bstep (se 1 (by rfl) ⟨1481768, by rfl⟩ : syracuseStep 1975691 = 2963537) B2963537
theorem B5268887 : Blo 1559477 5268887 := bstep (se 1 (by rfl) ⟨3951665, by rfl⟩ : syracuseStep 5268887 = 7903331) B7903331
theorem B4441547 : Blo 1559477 4441547 := bstep (se 1 (by rfl) ⟨3331160, by rfl⟩ : syracuseStep 4441547 = 6662321) B6662321
theorem B1754635 : Blo 1559477 1754635 := bstep (se 1 (by rfl) ⟨1315976, by rfl⟩ : syracuseStep 1754635 = 2631953) B2631953
theorem B1754743 : Blo 1559477 1754743 := bstep (se 1 (by rfl) ⟨1316057, by rfl⟩ : syracuseStep 1754743 = 2632115) B2632115
theorem B3163801 : Blo 1559477 3163801 := bstep (se 2 (by rfl) ⟨1186425, by rfl⟩ : syracuseStep 3163801 = 2372851) B2372851
theorem B1779415 : Blo 1559477 1779415 := bstep (se 1 (by rfl) ⟨1334561, by rfl⟩ : syracuseStep 1779415 = 2669123) B2669123
theorem B9995993 : Blo 1559477 9995993 := bstep (se 2 (by rfl) ⟨3748497, by rfl⟩ : syracuseStep 9995993 = 7496995) B7496995
theorem B4744925 : Blo 1559477 4744925 := bstep (se 3 (by rfl) ⟨889673, by rfl⟩ : syracuseStep 4744925 = 1779347) B1779347
theorem B1754923 : Blo 1559477 1754923 := bstep (se 1 (by rfl) ⟨1316192, by rfl⟩ : syracuseStep 1754923 = 2632385) B2632385
theorem B1755031 : Blo 1559477 1755031 := bstep (se 1 (by rfl) ⟨1316273, by rfl⟩ : syracuseStep 1755031 = 2632547) B2632547
theorem B15001523 : Blo 1559477 15001523 := bstep (se 1 (by rfl) ⟨11251142, by rfl⟩ : syracuseStep 15001523 = 22502285) B22502285
theorem B5269427 : Blo 1559477 5269427 := bstep (se 1 (by rfl) ⟨3952070, by rfl⟩ : syracuseStep 5269427 = 7904141) B7904141
theorem B6662081 : Blo 1559477 6662081 := bstep (se 2 (by rfl) ⟨2498280, by rfl⟩ : syracuseStep 6662081 = 4996561) B4996561
theorem B2631703 : Blo 1559477 2631703 := bstep (se 1 (by rfl) ⟨1973777, by rfl⟩ : syracuseStep 2631703 = 3947555) B3947555
theorem B5621825 : Blo 1559477 5621825 := bstep (se 2 (by rfl) ⟨2108184, by rfl⟩ : syracuseStep 5621825 = 4216369) B4216369
theorem B1755211 : Blo 1559477 1755211 := bstep (se 1 (by rfl) ⟨1316408, by rfl⟩ : syracuseStep 1755211 = 2632817) B2632817
theorem B13338755 : Blo 1559477 13338755 := bstep (se 1 (by rfl) ⟨10004066, by rfl⟩ : syracuseStep 13338755 = 20008133) B20008133
theorem B60778637 : Blo 1559477 60778637 := bstep (se 3 (by rfl) ⟨11395994, by rfl⟩ : syracuseStep 60778637 = 22791989) B22791989
theorem B8890519 : Blo 1559477 8890519 := bstep (se 1 (by rfl) ⟨6667889, by rfl⟩ : syracuseStep 8890519 = 13335779) B13335779
theorem B1689751 : Blo 1559477 1689751 := bstep (se 1 (by rfl) ⟨1267313, by rfl⟩ : syracuseStep 1689751 = 2534627) B2534627
theorem B1755319 : Blo 1559477 1755319 := bstep (se 1 (by rfl) ⟨1316489, by rfl⟩ : syracuseStep 1755319 = 2632979) B2632979
theorem B5269697 : Blo 1559477 5269697 := bstep (se 2 (by rfl) ⟨1976136, by rfl⟩ : syracuseStep 5269697 = 3952273) B3952273
theorem B3950795 : Blo 1559477 3950795 := bstep (se 1 (by rfl) ⟨2963096, by rfl⟩ : syracuseStep 3950795 = 5926193) B5926193
theorem B2222425 : Blo 1559477 2222425 := bstep (se 2 (by rfl) ⟨833409, by rfl⟩ : syracuseStep 2222425 = 1666819) B1666819
theorem B1755499 : Blo 1559477 1755499 := bstep (se 1 (by rfl) ⟨1316624, by rfl⟩ : syracuseStep 1755499 = 2633249) B2633249
theorem B5925251 : Blo 1559477 5925251 := bstep (se 1 (by rfl) ⟨4443938, by rfl⟩ : syracuseStep 5925251 = 8887877) B8887877
theorem B1755607 : Blo 1559477 1755607 := bstep (se 1 (by rfl) ⟨1316705, by rfl⟩ : syracuseStep 1755607 = 2633411) B2633411
theorem B64072205 : Blo 1559477 64072205 := bstep (se 3 (by rfl) ⟨12013538, by rfl⟩ : syracuseStep 64072205 = 24027077) B24027077
theorem B7121453 : Blo 1559477 7121453 := bstep (se 3 (by rfl) ⟨1335272, by rfl⟩ : syracuseStep 7121453 = 2670545) B2670545
theorem B1665623 : Blo 1559477 1665623 := bstep (se 1 (by rfl) ⟨1249217, by rfl⟩ : syracuseStep 1665623 = 2498435) B2498435
theorem B3508865 : Blo 1559477 3508865 := bstep (se 2 (by rfl) ⟨1315824, by rfl⟩ : syracuseStep 3508865 = 2631649) B2631649
theorem B2632331 : Blo 1559477 2632331 := bstep (se 1 (by rfl) ⟨1974248, by rfl⟩ : syracuseStep 2632331 = 3948497) B3948497
theorem B1755787 : Blo 1559477 1755787 := bstep (se 1 (by rfl) ⟨1316840, by rfl⟩ : syracuseStep 1755787 = 2633681) B2633681
theorem B2001559 : Blo 1559477 2001559 := bstep (se 1 (by rfl) ⟨1501169, by rfl⟩ : syracuseStep 2001559 = 3002339) B3002339
theorem B5065409 : Blo 1559477 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B4745945 : Blo 1559477 4745945 := bstep (se 2 (by rfl) ⟨1779729, by rfl⟩ : syracuseStep 4745945 = 3559459) B3559459
theorem B4442845 : Blo 1559477 4442845 := bstep (se 3 (by rfl) ⟨833033, by rfl⟩ : syracuseStep 4442845 = 1666067) B1666067
theorem B1755895 : Blo 1559477 1755895 := bstep (se 1 (by rfl) ⟨1316921, by rfl⟩ : syracuseStep 1755895 = 2633843) B2633843
theorem B2632459 : Blo 1559477 2632459 := bstep (se 1 (by rfl) ⟨1974344, by rfl⟩ : syracuseStep 2632459 = 3948689) B3948689
theorem B5925707 : Blo 1559477 5925707 := bstep (se 1 (by rfl) ⟨4444280, by rfl⟩ : syracuseStep 5925707 = 8888561) B8888561
theorem B3509081 : Blo 1559477 3509081 := bstep (se 2 (by rfl) ⟨1315905, by rfl⟩ : syracuseStep 3509081 = 2631811) B2631811
theorem B6663005 : Blo 1559477 6663005 := bstep (se 3 (by rfl) ⟨1249313, by rfl⟩ : syracuseStep 6663005 = 2498627) B2498627
theorem B14240605 : Blo 1559477 14240605 := bstep (se 3 (by rfl) ⟨2670113, by rfl⟩ : syracuseStep 14240605 = 5340227) B5340227
theorem B2812801 : Blo 1559477 2812801 := bstep (se 2 (by rfl) ⟨1054800, by rfl⟩ : syracuseStep 2812801 = 2109601) B2109601
theorem B2632601 : Blo 1559477 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B1756075 : Blo 1559477 1756075 := bstep (se 1 (by rfl) ⟨1317056, by rfl⟩ : syracuseStep 1756075 = 2634113) B2634113
theorem B3509171 : Blo 1559477 3509171 := bstep (se 1 (by rfl) ⟨2631878, by rfl⟩ : syracuseStep 3509171 = 5263757) B5263757
theorem B1559479 : Blo 1559477 1559479 := bstep (se 1 (by rfl) ⟨1169609, by rfl⟩ : syracuseStep 1559479 = 2339219) B2339219
theorem B1559499 : Blo 1559477 1559499 := bstep (se 1 (by rfl) ⟨1169624, by rfl⟩ : syracuseStep 1559499 = 2339249) B2339249
theorem B13331405 : Blo 1559477 13331405 := bstep (se 3 (by rfl) ⟨2499638, by rfl⟩ : syracuseStep 13331405 = 4999277) B4999277
theorem B1559511 : Blo 1559477 1559511 := bstep (se 1 (by rfl) ⟨1169633, by rfl⟩ : syracuseStep 1559511 = 2339267) B2339267
theorem B3509207 : Blo 1559477 3509207 := bstep (se 1 (by rfl) ⟨2631905, by rfl⟩ : syracuseStep 3509207 = 5263811) B5263811
theorem B1559531 : Blo 1559477 1559531 := bstep (se 1 (by rfl) ⟨1169648, by rfl⟩ : syracuseStep 1559531 = 2339297) B2339297
theorem B1559543 : Blo 1559477 1559543 := bstep (se 1 (by rfl) ⟨1169657, by rfl⟩ : syracuseStep 1559543 = 2339315) B2339315
theorem B3558401 : Blo 1559477 3558401 := bstep (se 2 (by rfl) ⟨1334400, by rfl⟩ : syracuseStep 3558401 = 2668801) B2668801
theorem B1559563 : Blo 1559477 1559563 := bstep (se 1 (by rfl) ⟨1169672, by rfl⟩ : syracuseStep 1559563 = 2339345) B2339345
theorem B5925905 : Blo 1559477 5925905 := bstep (se 2 (by rfl) ⟨2222214, by rfl⟩ : syracuseStep 5925905 = 4444429) B4444429
theorem B1559575 : Blo 1559477 1559575 := bstep (se 1 (by rfl) ⟨1169681, by rfl⟩ : syracuseStep 1559575 = 2339363) B2339363
theorem B1756183 : Blo 1559477 1756183 := bstep (se 1 (by rfl) ⟨1317137, by rfl⟩ : syracuseStep 1756183 = 2634275) B2634275
theorem B2632729 : Blo 1559477 2632729 := bstep (se 2 (by rfl) ⟨987273, by rfl⟩ : syracuseStep 2632729 = 1974547) B1974547
theorem B1559595 : Blo 1559477 1559595 := bstep (se 1 (by rfl) ⟨1169696, by rfl⟩ : syracuseStep 1559595 = 2339393) B2339393
theorem B11856941 : Blo 1559477 11856941 := bstep (se 3 (by rfl) ⟨2223176, by rfl⟩ : syracuseStep 11856941 = 4446353) B4446353
theorem B4443187 : Blo 1559477 4443187 := bstep (se 1 (by rfl) ⟨3332390, by rfl⟩ : syracuseStep 4443187 = 6664781) B6664781
theorem B1559607 : Blo 1559477 1559607 := bstep (se 1 (by rfl) ⟨1169705, by rfl⟩ : syracuseStep 1559607 = 2339411) B2339411
theorem B1559627 : Blo 1559477 1559627 := bstep (se 1 (by rfl) ⟨1169720, by rfl⟩ : syracuseStep 1559627 = 2339441) B2339441
theorem B1559639 : Blo 1559477 1559639 := bstep (se 1 (by rfl) ⟨1169729, by rfl⟩ : syracuseStep 1559639 = 2339459) B2339459
theorem B7900253 : Blo 1559477 7900253 := bstep (se 3 (by rfl) ⟨1481297, by rfl⟩ : syracuseStep 7900253 = 2962595) B2962595
theorem B1559659 : Blo 1559477 1559659 := bstep (se 1 (by rfl) ⟨1169744, by rfl⟩ : syracuseStep 1559659 = 2339489) B2339489
theorem B1559671 : Blo 1559477 1559671 := bstep (se 1 (by rfl) ⟨1169753, by rfl⟩ : syracuseStep 1559671 = 2339507) B2339507
theorem B1559691 : Blo 1559477 1559691 := bstep (se 1 (by rfl) ⟨1169768, by rfl⟩ : syracuseStep 1559691 = 2339537) B2339537
theorem B3509387 : Blo 1559477 3509387 := bstep (se 1 (by rfl) ⟨2632040, by rfl⟩ : syracuseStep 3509387 = 5264081) B5264081
theorem B1559703 : Blo 1559477 1559703 := bstep (se 1 (by rfl) ⟨1169777, by rfl⟩ : syracuseStep 1559703 = 2339555) B2339555
theorem B3951767 : Blo 1559477 3951767 := bstep (se 1 (by rfl) ⟨2963825, by rfl⟩ : syracuseStep 3951767 = 5927651) B5927651
theorem B1559723 : Blo 1559477 1559723 := bstep (se 1 (by rfl) ⟨1169792, by rfl⟩ : syracuseStep 1559723 = 2339585) B2339585
theorem B1559735 : Blo 1559477 1559735 := bstep (se 1 (by rfl) ⟨1169801, by rfl⟩ : syracuseStep 1559735 = 2339603) B2339603
theorem B3509441 : Blo 1559477 3509441 := bstep (se 2 (by rfl) ⟨1316040, by rfl⟩ : syracuseStep 3509441 = 2632081) B2632081
theorem B1559755 : Blo 1559477 1559755 := bstep (se 1 (by rfl) ⟨1169816, by rfl⟩ : syracuseStep 1559755 = 2339633) B2339633
theorem B1756363 : Blo 1559477 1756363 := bstep (se 1 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 1756363 = 2634545) B2634545
theorem B1559767 : Blo 1559477 1559767 := bstep (se 1 (by rfl) ⟨1169825, by rfl⟩ : syracuseStep 1559767 = 2339651) B2339651
theorem B1559787 : Blo 1559477 1559787 := bstep (se 1 (by rfl) ⟨1169840, by rfl⟩ : syracuseStep 1559787 = 2339681) B2339681
theorem B1559799 : Blo 1559477 1559799 := bstep (se 1 (by rfl) ⟨1169849, by rfl⟩ : syracuseStep 1559799 = 2339699) B2339699
theorem B24022277 : Blo 1559477 24022277 := bstep (se 4 (by rfl) ⟨2252088, by rfl⟩ : syracuseStep 24022277 = 4504177) B4504177
theorem B2960651 : Blo 1559477 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B1559819 : Blo 1559477 1559819 := bstep (se 1 (by rfl) ⟨1169864, by rfl⟩ : syracuseStep 1559819 = 2339729) B2339729
theorem B1559831 : Blo 1559477 1559831 := bstep (se 1 (by rfl) ⟨1169873, by rfl⟩ : syracuseStep 1559831 = 2339747) B2339747
theorem B1559851 : Blo 1559477 1559851 := bstep (se 1 (by rfl) ⟨1169888, by rfl⟩ : syracuseStep 1559851 = 2339777) B2339777
theorem B1559863 : Blo 1559477 1559863 := bstep (se 1 (by rfl) ⟨1169897, by rfl⟩ : syracuseStep 1559863 = 2339795) B2339795
theorem B1756471 : Blo 1559477 1756471 := bstep (se 1 (by rfl) ⟨1317353, by rfl⟩ : syracuseStep 1756471 = 2634707) B2634707
theorem B2960705 : Blo 1559477 2960705 := bstep (se 2 (by rfl) ⟨1110264, by rfl⟩ : syracuseStep 2960705 = 2220529) B2220529
theorem B1559883 : Blo 1559477 1559883 := bstep (se 1 (by rfl) ⟨1169912, by rfl⟩ : syracuseStep 1559883 = 2339825) B2339825
theorem B1559895 : Blo 1559477 1559895 := bstep (se 1 (by rfl) ⟨1169921, by rfl⟩ : syracuseStep 1559895 = 2339843) B2339843
theorem B1559915 : Blo 1559477 1559915 := bstep (se 1 (by rfl) ⟨1169936, by rfl⟩ : syracuseStep 1559915 = 2339873) B2339873
theorem B1559927 : Blo 1559477 1559927 := bstep (se 1 (by rfl) ⟨1169945, by rfl⟩ : syracuseStep 1559927 = 2339891) B2339891
theorem B1559947 : Blo 1559477 1559947 := bstep (se 1 (by rfl) ⟨1169960, by rfl⟩ : syracuseStep 1559947 = 2339921) B2339921
theorem B1559959 : Blo 1559477 1559959 := bstep (se 1 (by rfl) ⟨1169969, by rfl⟩ : syracuseStep 1559959 = 2339939) B2339939
theorem B3509657 : Blo 1559477 3509657 := bstep (se 2 (by rfl) ⟨1316121, by rfl⟩ : syracuseStep 3509657 = 2632243) B2632243
theorem B1559979 : Blo 1559477 1559979 := bstep (se 1 (by rfl) ⟨1169984, by rfl⟩ : syracuseStep 1559979 = 2339969) B2339969
theorem B1559991 : Blo 1559477 1559991 := bstep (se 1 (by rfl) ⟨1169993, by rfl⟩ : syracuseStep 1559991 = 2339987) B2339987
theorem B1560011 : Blo 1559477 1560011 := bstep (se 1 (by rfl) ⟨1170008, by rfl⟩ : syracuseStep 1560011 = 2340017) B2340017
theorem B11849165 : Blo 1559477 11849165 := bstep (se 3 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 11849165 = 4443437) B4443437
theorem B1560023 : Blo 1559477 1560023 := bstep (se 1 (by rfl) ⟨1170017, by rfl⟩ : syracuseStep 1560023 = 2340035) B2340035
theorem B1560043 : Blo 1559477 1560043 := bstep (se 1 (by rfl) ⟨1170032, by rfl⟩ : syracuseStep 1560043 = 2340065) B2340065
theorem B1756651 : Blo 1559477 1756651 := bstep (se 1 (by rfl) ⟨1317488, by rfl⟩ : syracuseStep 1756651 = 2634977) B2634977
theorem B3509747 : Blo 1559477 3509747 := bstep (se 1 (by rfl) ⟨2632310, by rfl⟩ : syracuseStep 3509747 = 5264621) B5264621
theorem B1560055 : Blo 1559477 1560055 := bstep (se 1 (by rfl) ⟨1170041, by rfl⟩ : syracuseStep 1560055 = 2340083) B2340083
theorem B1560075 : Blo 1559477 1560075 := bstep (se 1 (by rfl) ⟨1170056, by rfl⟩ : syracuseStep 1560075 = 2340113) B2340113
theorem B3509783 : Blo 1559477 3509783 := bstep (se 1 (by rfl) ⟨2632337, by rfl⟩ : syracuseStep 3509783 = 5264675) B5264675
theorem B1560087 : Blo 1559477 1560087 := bstep (se 1 (by rfl) ⟨1170065, by rfl⟩ : syracuseStep 1560087 = 2340131) B2340131
theorem B1560107 : Blo 1559477 1560107 := bstep (se 1 (by rfl) ⟨1170080, by rfl⟩ : syracuseStep 1560107 = 2340161) B2340161
theorem B1560119 : Blo 1559477 1560119 := bstep (se 1 (by rfl) ⟨1170089, by rfl⟩ : syracuseStep 1560119 = 2340179) B2340179
theorem B1560139 : Blo 1559477 1560139 := bstep (se 1 (by rfl) ⟨1170104, by rfl⟩ : syracuseStep 1560139 = 2340209) B2340209
theorem B1560151 : Blo 1559477 1560151 := bstep (se 1 (by rfl) ⟨1170113, by rfl⟩ : syracuseStep 1560151 = 2340227) B2340227
theorem B2633303 : Blo 1559477 2633303 := bstep (se 1 (by rfl) ⟨1974977, by rfl⟩ : syracuseStep 2633303 = 3949955) B3949955
theorem B1560171 : Blo 1559477 1560171 := bstep (se 1 (by rfl) ⟨1170128, by rfl⟩ : syracuseStep 1560171 = 2340257) B2340257
theorem B1560183 : Blo 1559477 1560183 := bstep (se 1 (by rfl) ⟨1170137, by rfl⟩ : syracuseStep 1560183 = 2340275) B2340275
theorem B1560203 : Blo 1559477 1560203 := bstep (se 1 (by rfl) ⟨1170152, by rfl⟩ : syracuseStep 1560203 = 2340305) B2340305
theorem B1666699 : Blo 1559477 1666699 := bstep (se 1 (by rfl) ⟨1250024, by rfl⟩ : syracuseStep 1666699 = 2500049) B2500049
theorem B1560215 : Blo 1559477 1560215 := bstep (se 1 (by rfl) ⟨1170161, by rfl⟩ : syracuseStep 1560215 = 2340323) B2340323
theorem B1560235 : Blo 1559477 1560235 := bstep (se 1 (by rfl) ⟨1170176, by rfl⟩ : syracuseStep 1560235 = 2340353) B2340353
theorem B1560247 : Blo 1559477 1560247 := bstep (se 1 (by rfl) ⟨1170185, by rfl⟩ : syracuseStep 1560247 = 2340371) B2340371
theorem B3509963 : Blo 1559477 3509963 := bstep (se 1 (by rfl) ⟨2632472, by rfl⟩ : syracuseStep 3509963 = 5264945) B5264945
theorem B1560267 : Blo 1559477 1560267 := bstep (se 1 (by rfl) ⟨1170200, by rfl⟩ : syracuseStep 1560267 = 2340401) B2340401
theorem B129920717 : Blo 1559477 129920717 := bstep (se 3 (by rfl) ⟨24360134, by rfl⟩ : syracuseStep 129920717 = 48720269) B48720269
theorem B1560279 : Blo 1559477 1560279 := bstep (se 1 (by rfl) ⟨1170209, by rfl⟩ : syracuseStep 1560279 = 2340419) B2340419
theorem B2633431 : Blo 1559477 2633431 := bstep (se 1 (by rfl) ⟨1975073, by rfl⟩ : syracuseStep 2633431 = 3950147) B3950147
theorem B1560299 : Blo 1559477 1560299 := bstep (se 1 (by rfl) ⟨1170224, by rfl⟩ : syracuseStep 1560299 = 2340449) B2340449
theorem B1560311 : Blo 1559477 1560311 := bstep (se 1 (by rfl) ⟨1170233, by rfl⟩ : syracuseStep 1560311 = 2340467) B2340467
theorem B3510017 : Blo 1559477 3510017 := bstep (se 2 (by rfl) ⟨1316256, by rfl⟩ : syracuseStep 3510017 = 2632513) B2632513
theorem B1560331 : Blo 1559477 1560331 := bstep (se 1 (by rfl) ⟨1170248, by rfl⟩ : syracuseStep 1560331 = 2340497) B2340497
theorem B1560343 : Blo 1559477 1560343 := bstep (se 1 (by rfl) ⟨1170257, by rfl⟩ : syracuseStep 1560343 = 2340515) B2340515
theorem B5926679 : Blo 1559477 5926679 := bstep (se 1 (by rfl) ⟨4445009, by rfl⟩ : syracuseStep 5926679 = 8890019) B8890019
theorem B11243299 : Blo 1559477 11243299 := bstep (se 1 (by rfl) ⟨8432474, by rfl⟩ : syracuseStep 11243299 = 16864949) B16864949
theorem B1560363 : Blo 1559477 1560363 := bstep (se 1 (by rfl) ⟨1170272, by rfl⟩ : syracuseStep 1560363 = 2340545) B2340545
theorem B5623597 : Blo 1559477 5623597 := bstep (se 3 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 5623597 = 2108849) B2108849
theorem B3952435 : Blo 1559477 3952435 := bstep (se 1 (by rfl) ⟨2964326, by rfl⟩ : syracuseStep 3952435 = 5928653) B5928653
theorem B1560375 : Blo 1559477 1560375 := bstep (se 1 (by rfl) ⟨1170281, by rfl⟩ : syracuseStep 1560375 = 2340563) B2340563
theorem B1560395 : Blo 1559477 1560395 := bstep (se 1 (by rfl) ⟨1170296, by rfl⟩ : syracuseStep 1560395 = 2340593) B2340593
theorem B1560407 : Blo 1559477 1560407 := bstep (se 1 (by rfl) ⟨1170305, by rfl⟩ : syracuseStep 1560407 = 2340611) B2340611
theorem B6328153 : Blo 1559477 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B1560427 : Blo 1559477 1560427 := bstep (se 1 (by rfl) ⟨1170320, by rfl⟩ : syracuseStep 1560427 = 2340641) B2340641
theorem B1560439 : Blo 1559477 1560439 := bstep (se 1 (by rfl) ⟨1170329, by rfl⟩ : syracuseStep 1560439 = 2340659) B2340659
theorem B1560459 : Blo 1559477 1560459 := bstep (se 1 (by rfl) ⟨1170344, by rfl⟩ : syracuseStep 1560459 = 2340689) B2340689
theorem B1560471 : Blo 1559477 1560471 := bstep (se 1 (by rfl) ⟨1170353, by rfl⟩ : syracuseStep 1560471 = 2340707) B2340707
theorem B1560491 : Blo 1559477 1560491 := bstep (se 1 (by rfl) ⟨1170368, by rfl⟩ : syracuseStep 1560491 = 2340737) B2340737
theorem B11849651 : Blo 1559477 11849651 := bstep (se 1 (by rfl) ⟨8887238, by rfl⟩ : syracuseStep 11849651 = 17774477) B17774477
theorem B1560503 : Blo 1559477 1560503 := bstep (se 1 (by rfl) ⟨1170377, by rfl⟩ : syracuseStep 1560503 = 2340755) B2340755
theorem B1560523 : Blo 1559477 1560523 := bstep (se 1 (by rfl) ⟨1170392, by rfl⟩ : syracuseStep 1560523 = 2340785) B2340785
theorem B1560535 : Blo 1559477 1560535 := bstep (se 1 (by rfl) ⟨1170401, by rfl⟩ : syracuseStep 1560535 = 2340803) B2340803
theorem B3510233 : Blo 1559477 3510233 := bstep (se 2 (by rfl) ⟨1316337, by rfl⟩ : syracuseStep 3510233 = 2632675) B2632675
theorem B4444121 : Blo 1559477 4444121 := bstep (se 2 (by rfl) ⟨1666545, by rfl⟩ : syracuseStep 4444121 = 3333091) B3333091
theorem B5263325 : Blo 1559477 5263325 := bstep (se 3 (by rfl) ⟨986873, by rfl⟩ : syracuseStep 5263325 = 1973747) B1973747
theorem B5926877 : Blo 1559477 5926877 := bstep (se 3 (by rfl) ⟨1111289, by rfl⟩ : syracuseStep 5926877 = 2222579) B2222579
theorem B1560555 : Blo 1559477 1560555 := bstep (se 1 (by rfl) ⟨1170416, by rfl⟩ : syracuseStep 1560555 = 2340833) B2340833
theorem B1560567 : Blo 1559477 1560567 := bstep (se 1 (by rfl) ⟨1170425, by rfl⟩ : syracuseStep 1560567 = 2340851) B2340851
theorem B1560587 : Blo 1559477 1560587 := bstep (se 1 (by rfl) ⟨1170440, by rfl⟩ : syracuseStep 1560587 = 2340881) B2340881
theorem B1560599 : Blo 1559477 1560599 := bstep (se 1 (by rfl) ⟨1170449, by rfl⟩ : syracuseStep 1560599 = 2340899) B2340899
theorem B1560619 : Blo 1559477 1560619 := bstep (se 1 (by rfl) ⟨1170464, by rfl⟩ : syracuseStep 1560619 = 2340929) B2340929
theorem B3510323 : Blo 1559477 3510323 := bstep (se 1 (by rfl) ⟨2632742, by rfl⟩ : syracuseStep 3510323 = 5265485) B5265485
theorem B1560631 : Blo 1559477 1560631 := bstep (se 1 (by rfl) ⟨1170473, by rfl⟩ : syracuseStep 1560631 = 2340947) B2340947
theorem B1560651 : Blo 1559477 1560651 := bstep (se 1 (by rfl) ⟨1170488, by rfl⟩ : syracuseStep 1560651 = 2340977) B2340977
theorem B3510359 : Blo 1559477 3510359 := bstep (se 1 (by rfl) ⟨2632769, by rfl⟩ : syracuseStep 3510359 = 5265539) B5265539
theorem B1560663 : Blo 1559477 1560663 := bstep (se 1 (by rfl) ⟨1170497, by rfl⟩ : syracuseStep 1560663 = 2340995) B2340995
theorem B5623901 : Blo 1559477 5623901 := bstep (se 3 (by rfl) ⟨1054481, by rfl⟩ : syracuseStep 5623901 = 2108963) B2108963
theorem B1560683 : Blo 1559477 1560683 := bstep (se 1 (by rfl) ⟨1170512, by rfl⟩ : syracuseStep 1560683 = 2341025) B2341025
theorem B1560695 : Blo 1559477 1560695 := bstep (se 1 (by rfl) ⟨1170521, by rfl⟩ : syracuseStep 1560695 = 2341043) B2341043
theorem B1560715 : Blo 1559477 1560715 := bstep (se 1 (by rfl) ⟨1170536, by rfl⟩ : syracuseStep 1560715 = 2341073) B2341073
theorem B1560727 : Blo 1559477 1560727 := bstep (se 1 (by rfl) ⟨1170545, by rfl⟩ : syracuseStep 1560727 = 2341091) B2341091
theorem B1560747 : Blo 1559477 1560747 := bstep (se 1 (by rfl) ⟨1170560, by rfl⟩ : syracuseStep 1560747 = 2341121) B2341121
theorem B1560759 : Blo 1559477 1560759 := bstep (se 1 (by rfl) ⟨1170569, by rfl⟩ : syracuseStep 1560759 = 2341139) B2341139
theorem B1560779 : Blo 1559477 1560779 := bstep (se 1 (by rfl) ⟨1170584, by rfl⟩ : syracuseStep 1560779 = 2341169) B2341169
theorem B5001419 : Blo 1559477 5001419 := bstep (se 1 (by rfl) ⟨3751064, by rfl⟩ : syracuseStep 5001419 = 7502129) B7502129
theorem B2961623 : Blo 1559477 2961623 := bstep (se 1 (by rfl) ⟨2221217, by rfl⟩ : syracuseStep 2961623 = 4442435) B4442435
theorem B1560791 : Blo 1559477 1560791 := bstep (se 1 (by rfl) ⟨1170593, by rfl⟩ : syracuseStep 1560791 = 2341187) B2341187
theorem B1560811 : Blo 1559477 1560811 := bstep (se 1 (by rfl) ⟨1170608, by rfl⟩ : syracuseStep 1560811 = 2341217) B2341217
theorem B1560823 : Blo 1559477 1560823 := bstep (se 1 (by rfl) ⟨1170617, by rfl⟩ : syracuseStep 1560823 = 2341235) B2341235
theorem B3510539 : Blo 1559477 3510539 := bstep (se 1 (by rfl) ⟨2632904, by rfl⟩ : syracuseStep 3510539 = 5265809) B5265809
theorem B1560843 : Blo 1559477 1560843 := bstep (se 1 (by rfl) ⟨1170632, by rfl⟩ : syracuseStep 1560843 = 2341265) B2341265
theorem B1560855 : Blo 1559477 1560855 := bstep (se 1 (by rfl) ⟨1170641, by rfl⟩ : syracuseStep 1560855 = 2341283) B2341283
theorem B1560875 : Blo 1559477 1560875 := bstep (se 1 (by rfl) ⟨1170656, by rfl⟩ : syracuseStep 1560875 = 2341313) B2341313
theorem B1560887 : Blo 1559477 1560887 := bstep (se 1 (by rfl) ⟨1170665, by rfl⟩ : syracuseStep 1560887 = 2341331) B2341331
theorem B3510593 : Blo 1559477 3510593 := bstep (se 2 (by rfl) ⟨1316472, by rfl⟩ : syracuseStep 3510593 = 2632945) B2632945
theorem B1560907 : Blo 1559477 1560907 := bstep (se 1 (by rfl) ⟨1170680, by rfl⟩ : syracuseStep 1560907 = 2341361) B2341361
theorem B2634059 : Blo 1559477 2634059 := bstep (se 1 (by rfl) ⟨1975544, by rfl⟩ : syracuseStep 2634059 = 3951089) B3951089
theorem B1560919 : Blo 1559477 1560919 := bstep (se 1 (by rfl) ⟨1170689, by rfl⟩ : syracuseStep 1560919 = 2341379) B2341379
theorem B1560939 : Blo 1559477 1560939 := bstep (se 1 (by rfl) ⟨1170704, by rfl⟩ : syracuseStep 1560939 = 2341409) B2341409
theorem B1560951 : Blo 1559477 1560951 := bstep (se 1 (by rfl) ⟨1170713, by rfl⟩ : syracuseStep 1560951 = 2341427) B2341427
theorem B1560971 : Blo 1559477 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B1560983 : Blo 1559477 1560983 := bstep (se 1 (by rfl) ⟨1170737, by rfl⟩ : syracuseStep 1560983 = 2341475) B2341475
theorem B2339225 : Blo 1559477 2339225 := bstep (se 2 (by rfl) ⟨877209, by rfl⟩ : syracuseStep 2339225 = 1754419) B1754419
theorem B1561003 : Blo 1559477 1561003 := bstep (se 1 (by rfl) ⟨1170752, by rfl⟩ : syracuseStep 1561003 = 2341505) B2341505
theorem B1561015 : Blo 1559477 1561015 := bstep (se 1 (by rfl) ⟨1170761, by rfl⟩ : syracuseStep 1561015 = 2341523) B2341523
theorem B2634187 : Blo 1559477 2634187 := bstep (se 1 (by rfl) ⟨1975640, by rfl⟩ : syracuseStep 2634187 = 3951281) B3951281
theorem B1561035 : Blo 1559477 1561035 := bstep (se 1 (by rfl) ⟨1170776, by rfl⟩ : syracuseStep 1561035 = 2341553) B2341553
theorem B1561047 : Blo 1559477 1561047 := bstep (se 1 (by rfl) ⟨1170785, by rfl⟩ : syracuseStep 1561047 = 2341571) B2341571
theorem B1561067 : Blo 1559477 1561067 := bstep (se 1 (by rfl) ⟨1170800, by rfl⟩ : syracuseStep 1561067 = 2341601) B2341601
theorem B1561079 : Blo 1559477 1561079 := bstep (se 1 (by rfl) ⟨1170809, by rfl⟩ : syracuseStep 1561079 = 2341619) B2341619
theorem B2339339 : Blo 1559477 2339339 := bstep (se 1 (by rfl) ⟨1754504, by rfl⟩ : syracuseStep 2339339 = 3509009) B3509009
theorem B1561099 : Blo 1559477 1561099 := bstep (se 1 (by rfl) ⟨1170824, by rfl⟩ : syracuseStep 1561099 = 2341649) B2341649
theorem B2339351 : Blo 1559477 2339351 := bstep (se 1 (by rfl) ⟨1754513, by rfl⟩ : syracuseStep 2339351 = 3509027) B3509027
theorem B1561111 : Blo 1559477 1561111 := bstep (se 1 (by rfl) ⟨1170833, by rfl⟩ : syracuseStep 1561111 = 2341667) B2341667
theorem B3510809 : Blo 1559477 3510809 := bstep (se 2 (by rfl) ⟨1316553, by rfl⟩ : syracuseStep 3510809 = 2633107) B2633107
theorem B1561131 : Blo 1559477 1561131 := bstep (se 1 (by rfl) ⟨1170848, by rfl⟩ : syracuseStep 1561131 = 2341697) B2341697
theorem B1561143 : Blo 1559477 1561143 := bstep (se 1 (by rfl) ⟨1170857, by rfl⟩ : syracuseStep 1561143 = 2341715) B2341715
theorem B1561163 : Blo 1559477 1561163 := bstep (se 1 (by rfl) ⟨1170872, by rfl⟩ : syracuseStep 1561163 = 2341745) B2341745
theorem B1561175 : Blo 1559477 1561175 := bstep (se 1 (by rfl) ⟨1170881, by rfl⟩ : syracuseStep 1561175 = 2341763) B2341763
theorem B2339417 : Blo 1559477 2339417 := bstep (se 2 (by rfl) ⟨877281, by rfl⟩ : syracuseStep 2339417 = 1754563) B1754563
theorem B2634329 : Blo 1559477 2634329 := bstep (se 2 (by rfl) ⟨987873, by rfl⟩ : syracuseStep 2634329 = 1975747) B1975747
theorem B1561195 : Blo 1559477 1561195 := bstep (se 1 (by rfl) ⟨1170896, by rfl⟩ : syracuseStep 1561195 = 2341793) B2341793
theorem B3510899 : Blo 1559477 3510899 := bstep (se 1 (by rfl) ⟨2633174, by rfl⟩ : syracuseStep 3510899 = 5266349) B5266349
theorem B1561207 : Blo 1559477 1561207 := bstep (se 1 (by rfl) ⟨1170905, by rfl⟩ : syracuseStep 1561207 = 2341811) B2341811
theorem B16863875 : Blo 1559477 16863875 := bstep (se 1 (by rfl) ⟨12647906, by rfl⟩ : syracuseStep 16863875 = 25295813) B25295813
theorem B1561227 : Blo 1559477 1561227 := bstep (se 1 (by rfl) ⟨1170920, by rfl⟩ : syracuseStep 1561227 = 2341841) B2341841
theorem B3510935 : Blo 1559477 3510935 := bstep (se 1 (by rfl) ⟨2633201, by rfl⟩ : syracuseStep 3510935 = 5266403) B5266403
theorem B1561239 : Blo 1559477 1561239 := bstep (se 1 (by rfl) ⟨1170929, by rfl⟩ : syracuseStep 1561239 = 2341859) B2341859
theorem B1561259 : Blo 1559477 1561259 := bstep (se 1 (by rfl) ⟨1170944, by rfl⟩ : syracuseStep 1561259 = 2341889) B2341889
theorem B1561271 : Blo 1559477 1561271 := bstep (se 1 (by rfl) ⟨1170953, by rfl⟩ : syracuseStep 1561271 = 2341907) B2341907
theorem B2339531 : Blo 1559477 2339531 := bstep (se 1 (by rfl) ⟨1754648, by rfl⟩ : syracuseStep 2339531 = 3509297) B3509297
theorem B1561291 : Blo 1559477 1561291 := bstep (se 1 (by rfl) ⟨1170968, by rfl⟩ : syracuseStep 1561291 = 2341937) B2341937
theorem B2339543 : Blo 1559477 2339543 := bstep (se 1 (by rfl) ⟨1754657, by rfl⟩ : syracuseStep 2339543 = 3509315) B3509315
theorem B1561303 : Blo 1559477 1561303 := bstep (se 1 (by rfl) ⟨1170977, by rfl⟩ : syracuseStep 1561303 = 2341955) B2341955
theorem B2634457 : Blo 1559477 2634457 := bstep (se 2 (by rfl) ⟨987921, by rfl⟩ : syracuseStep 2634457 = 1975843) B1975843
theorem B1561323 : Blo 1559477 1561323 := bstep (se 1 (by rfl) ⟨1170992, by rfl⟩ : syracuseStep 1561323 = 2341985) B2341985
theorem B2962163 : Blo 1559477 2962163 := bstep (se 1 (by rfl) ⟨2221622, by rfl⟩ : syracuseStep 2962163 = 4443245) B4443245
theorem B1561335 : Blo 1559477 1561335 := bstep (se 1 (by rfl) ⟨1171001, by rfl⟩ : syracuseStep 1561335 = 2342003) B2342003
theorem B1561355 : Blo 1559477 1561355 := bstep (se 1 (by rfl) ⟨1171016, by rfl⟩ : syracuseStep 1561355 = 2342033) B2342033
theorem B1561367 : Blo 1559477 1561367 := bstep (se 1 (by rfl) ⟨1171025, by rfl⟩ : syracuseStep 1561367 = 2342051) B2342051
theorem B2339609 : Blo 1559477 2339609 := bstep (se 2 (by rfl) ⟨877353, by rfl⟩ : syracuseStep 2339609 = 1754707) B1754707
theorem B1561387 : Blo 1559477 1561387 := bstep (se 1 (by rfl) ⟨1171040, by rfl⟩ : syracuseStep 1561387 = 2342081) B2342081
theorem B11252525 : Blo 1559477 11252525 := bstep (se 3 (by rfl) ⟨2109848, by rfl⟩ : syracuseStep 11252525 = 4219697) B4219697
theorem B1561399 : Blo 1559477 1561399 := bstep (se 1 (by rfl) ⟨1171049, by rfl⟩ : syracuseStep 1561399 = 2342099) B2342099
theorem B4002625 : Blo 1559477 4002625 := bstep (se 2 (by rfl) ⟨1500984, by rfl⟩ : syracuseStep 4002625 = 3001969) B3001969
theorem B3511115 : Blo 1559477 3511115 := bstep (se 1 (by rfl) ⟨2633336, by rfl⟩ : syracuseStep 3511115 = 5266673) B5266673
theorem B1561419 : Blo 1559477 1561419 := bstep (se 1 (by rfl) ⟨1171064, by rfl⟩ : syracuseStep 1561419 = 2342129) B2342129
theorem B1561431 : Blo 1559477 1561431 := bstep (se 1 (by rfl) ⟨1171073, by rfl⟩ : syracuseStep 1561431 = 2342147) B2342147
theorem B1561451 : Blo 1559477 1561451 := bstep (se 1 (by rfl) ⟨1171088, by rfl⟩ : syracuseStep 1561451 = 2342177) B2342177
theorem B1561463 : Blo 1559477 1561463 := bstep (se 1 (by rfl) ⟨1171097, by rfl⟩ : syracuseStep 1561463 = 2342195) B2342195
theorem B3511169 : Blo 1559477 3511169 := bstep (se 2 (by rfl) ⟨1316688, by rfl⟩ : syracuseStep 3511169 = 2633377) B2633377
theorem B2339723 : Blo 1559477 2339723 := bstep (se 1 (by rfl) ⟨1754792, by rfl⟩ : syracuseStep 2339723 = 3509585) B3509585
theorem B2339735 : Blo 1559477 2339735 := bstep (se 1 (by rfl) ⟨1754801, by rfl⟩ : syracuseStep 2339735 = 3509603) B3509603
theorem B3748787 : Blo 1559477 3748787 := bstep (se 1 (by rfl) ⟨2811590, by rfl⟩ : syracuseStep 3748787 = 5623181) B5623181
theorem B2339801 : Blo 1559477 2339801 := bstep (se 2 (by rfl) ⟨877425, by rfl⟩ : syracuseStep 2339801 = 1754851) B1754851
theorem B8434705 : Blo 1559477 8434705 := bstep (se 2 (by rfl) ⟨3163014, by rfl⟩ : syracuseStep 8434705 = 6326029) B6326029
theorem B5264459 : Blo 1559477 5264459 := bstep (se 1 (by rfl) ⟨3948344, by rfl⟩ : syracuseStep 5264459 = 7896689) B7896689
theorem B2339915 : Blo 1559477 2339915 := bstep (se 1 (by rfl) ⟨1754936, by rfl⟩ : syracuseStep 2339915 = 3509873) B3509873
theorem B2339927 : Blo 1559477 2339927 := bstep (se 1 (by rfl) ⟨1754945, by rfl⟩ : syracuseStep 2339927 = 3509891) B3509891
theorem B3511385 : Blo 1559477 3511385 := bstep (se 2 (by rfl) ⟨1316769, by rfl⟩ : syracuseStep 3511385 = 2633539) B2633539
theorem B3331211 : Blo 1559477 3331211 := bstep (se 1 (by rfl) ⟨2498408, by rfl⟩ : syracuseStep 3331211 = 4996817) B4996817
theorem B7902359 : Blo 1559477 7902359 := bstep (se 1 (by rfl) ⟨5926769, by rfl⟩ : syracuseStep 7902359 = 11853539) B11853539
theorem B2339993 : Blo 1559477 2339993 := bstep (se 2 (by rfl) ⟨877497, by rfl⟩ : syracuseStep 2339993 = 1754995) B1754995
theorem B3511475 : Blo 1559477 3511475 := bstep (se 1 (by rfl) ⟨2633606, by rfl⟩ : syracuseStep 3511475 = 5267213) B5267213
theorem B3003571 : Blo 1559477 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B61600949 : Blo 1559477 61600949 := bstep (se 5 (by rfl) ⟨2887544, by rfl⟩ : syracuseStep 61600949 = 5775089) B5775089
theorem B3511511 : Blo 1559477 3511511 := bstep (se 1 (by rfl) ⟨2633633, by rfl⟩ : syracuseStep 3511511 = 5267267) B5267267
theorem B2962649 : Blo 1559477 2962649 := bstep (se 2 (by rfl) ⟨1110993, by rfl⟩ : syracuseStep 2962649 = 2221987) B2221987
theorem B2340107 : Blo 1559477 2340107 := bstep (se 1 (by rfl) ⟨1755080, by rfl⟩ : syracuseStep 2340107 = 3510161) B3510161
theorem B2340119 : Blo 1559477 2340119 := bstep (se 1 (by rfl) ⟨1755089, by rfl⟩ : syracuseStep 2340119 = 3510179) B3510179
theorem B3560755 : Blo 1559477 3560755 := bstep (se 1 (by rfl) ⟨2670566, by rfl⟩ : syracuseStep 3560755 = 5341133) B5341133
theorem B13325633 : Blo 1559477 13325633 := bstep (se 2 (by rfl) ⟨4997112, by rfl⟩ : syracuseStep 13325633 = 9994225) B9994225
theorem B5264729 : Blo 1559477 5264729 := bstep (se 2 (by rfl) ⟨1974273, by rfl⟩ : syracuseStep 5264729 = 3948547) B3948547
theorem B2340185 : Blo 1559477 2340185 := bstep (se 2 (by rfl) ⟨877569, by rfl⟩ : syracuseStep 2340185 = 1755139) B1755139
theorem B4445533 : Blo 1559477 4445533 := bstep (se 3 (by rfl) ⟨833537, by rfl⟩ : syracuseStep 4445533 = 1667075) B1667075
theorem B11851109 : Blo 1559477 11851109 := bstep (se 4 (by rfl) ⟨1111041, by rfl⟩ : syracuseStep 11851109 = 2222083) B2222083
theorem B3511691 : Blo 1559477 3511691 := bstep (se 1 (by rfl) ⟨2633768, by rfl⟩ : syracuseStep 3511691 = 5267537) B5267537
theorem B3208627 : Blo 1559477 3208627 := bstep (se 1 (by rfl) ⟨2406470, by rfl⟩ : syracuseStep 3208627 = 4812941) B4812941
theorem B3511745 : Blo 1559477 3511745 := bstep (se 2 (by rfl) ⟨1316904, by rfl⟩ : syracuseStep 3511745 = 2633809) B2633809
theorem B2340299 : Blo 1559477 2340299 := bstep (se 1 (by rfl) ⟨1755224, by rfl⟩ : syracuseStep 2340299 = 3510449) B3510449
theorem B2340311 : Blo 1559477 2340311 := bstep (se 1 (by rfl) ⟨1755233, by rfl⟩ : syracuseStep 2340311 = 3510467) B3510467
theorem B2373143 : Blo 1559477 2373143 := bstep (se 1 (by rfl) ⟨1779857, by rfl⟩ : syracuseStep 2373143 = 3559715) B3559715
theorem B2340377 : Blo 1559477 2340377 := bstep (se 2 (by rfl) ⟨877641, by rfl⟩ : syracuseStep 2340377 = 1755283) B1755283
theorem B24024611 : Blo 1559477 24024611 := bstep (se 1 (by rfl) ⟨18018458, by rfl⟩ : syracuseStep 24024611 = 36036917) B36036917
theorem B4445761 : Blo 1559477 4445761 := bstep (se 2 (by rfl) ⟨1667160, by rfl⟩ : syracuseStep 4445761 = 3334321) B3334321
theorem B2340491 : Blo 1559477 2340491 := bstep (se 1 (by rfl) ⟨1755368, by rfl⟩ : syracuseStep 2340491 = 3510737) B3510737
theorem B2340503 : Blo 1559477 2340503 := bstep (se 1 (by rfl) ⟨1755377, by rfl⟩ : syracuseStep 2340503 = 3510755) B3510755
theorem B3511961 : Blo 1559477 3511961 := bstep (se 2 (by rfl) ⟨1316985, by rfl⟩ : syracuseStep 3511961 = 2633971) B2633971
theorem B2340569 : Blo 1559477 2340569 := bstep (se 2 (by rfl) ⟨877713, by rfl⟩ : syracuseStep 2340569 = 1755427) B1755427
theorem B3512051 : Blo 1559477 3512051 := bstep (se 1 (by rfl) ⟨2634038, by rfl⟩ : syracuseStep 3512051 = 5268077) B5268077
theorem B11843333 : Blo 1559477 11843333 := bstep (se 4 (by rfl) ⟨1110312, by rfl⟩ : syracuseStep 11843333 = 2220625) B2220625
theorem B1873687 : Blo 1559477 1873687 := bstep (se 1 (by rfl) ⟨1405265, by rfl⟩ : syracuseStep 1873687 = 2810531) B2810531
theorem B3512087 : Blo 1559477 3512087 := bstep (se 1 (by rfl) ⟨2634065, by rfl⟩ : syracuseStep 3512087 = 5268131) B5268131
theorem B2340683 : Blo 1559477 2340683 := bstep (se 1 (by rfl) ⟨1755512, by rfl⟩ : syracuseStep 2340683 = 3511025) B3511025
theorem B11851595 : Blo 1559477 11851595 := bstep (se 1 (by rfl) ⟨8888696, by rfl⟩ : syracuseStep 11851595 = 17777393) B17777393
theorem B2340695 : Blo 1559477 2340695 := bstep (se 1 (by rfl) ⟨1755521, by rfl⟩ : syracuseStep 2340695 = 3511043) B3511043
theorem B13006693 : Blo 1559477 13006693 := bstep (se 4 (by rfl) ⟨1219377, by rfl⟩ : syracuseStep 13006693 = 2438755) B2438755
theorem B3331955 : Blo 1559477 3331955 := bstep (se 1 (by rfl) ⟨2498966, by rfl⟩ : syracuseStep 3331955 = 4997933) B4997933
theorem B4446103 : Blo 1559477 4446103 := bstep (se 1 (by rfl) ⟨3334577, by rfl⟩ : syracuseStep 4446103 = 6669155) B6669155
theorem B2340761 : Blo 1559477 2340761 := bstep (se 2 (by rfl) ⟨877785, by rfl⟩ : syracuseStep 2340761 = 1755571) B1755571
theorem B3512267 : Blo 1559477 3512267 := bstep (se 1 (by rfl) ⟨2634200, by rfl⟩ : syracuseStep 3512267 = 5268401) B5268401
theorem B3512321 : Blo 1559477 3512321 := bstep (se 2 (by rfl) ⟨1317120, by rfl⟩ : syracuseStep 3512321 = 2634241) B2634241
theorem B2340875 : Blo 1559477 2340875 := bstep (se 1 (by rfl) ⟨1755656, by rfl⟩ : syracuseStep 2340875 = 3511313) B3511313
theorem B5265431 : Blo 1559477 5265431 := bstep (se 1 (by rfl) ⟨3949073, by rfl⟩ : syracuseStep 5265431 = 7898147) B7898147
theorem B2340887 : Blo 1559477 2340887 := bstep (se 1 (by rfl) ⟨1755665, by rfl⟩ : syracuseStep 2340887 = 3511331) B3511331
theorem B2340953 : Blo 1559477 2340953 := bstep (se 2 (by rfl) ⟨877857, by rfl⟩ : syracuseStep 2340953 = 1755715) B1755715
theorem B6666371 : Blo 1559477 6666371 := bstep (se 1 (by rfl) ⟨4999778, by rfl⟩ : syracuseStep 6666371 = 9999557) B9999557
theorem B15005827 : Blo 1559477 15005827 := bstep (se 1 (by rfl) ⟨11254370, by rfl⟩ : syracuseStep 15005827 = 22508741) B22508741
theorem B2341067 : Blo 1559477 2341067 := bstep (se 1 (by rfl) ⟨1755800, by rfl⟩ : syracuseStep 2341067 = 3511601) B3511601
theorem B2341079 : Blo 1559477 2341079 := bstep (se 1 (by rfl) ⟨1755809, by rfl⟩ : syracuseStep 2341079 = 3511619) B3511619
theorem B3512537 : Blo 1559477 3512537 := bstep (se 2 (by rfl) ⟨1317201, by rfl⟩ : syracuseStep 3512537 = 2634403) B2634403
theorem B5781725 : Blo 1559477 5781725 := bstep (se 3 (by rfl) ⟨1084073, by rfl⟩ : syracuseStep 5781725 = 2168147) B2168147
theorem B14244113 : Blo 1559477 14244113 := bstep (se 2 (by rfl) ⟨5341542, by rfl⟩ : syracuseStep 14244113 = 10683085) B10683085
theorem B2341145 : Blo 1559477 2341145 := bstep (se 2 (by rfl) ⟨877929, by rfl⟩ : syracuseStep 2341145 = 1755859) B1755859
theorem B9484589 : Blo 1559477 9484589 := bstep (se 3 (by rfl) ⟨1778360, by rfl⟩ : syracuseStep 9484589 = 3556721) B3556721
theorem B3512627 : Blo 1559477 3512627 := bstep (se 1 (by rfl) ⟨2634470, by rfl⟩ : syracuseStep 3512627 = 5268941) B5268941
theorem B3512663 : Blo 1559477 3512663 := bstep (se 1 (by rfl) ⟨2634497, by rfl⟩ : syracuseStep 3512663 = 5268995) B5268995
theorem B2341259 : Blo 1559477 2341259 := bstep (se 1 (by rfl) ⟨1755944, by rfl⟩ : syracuseStep 2341259 = 3511889) B3511889
theorem B2341271 : Blo 1559477 2341271 := bstep (se 1 (by rfl) ⟨1755953, by rfl⟩ : syracuseStep 2341271 = 3511907) B3511907
theorem B3750295 : Blo 1559477 3750295 := bstep (se 1 (by rfl) ⟨2812721, by rfl⟩ : syracuseStep 3750295 = 5625443) B5625443
theorem B26655155 : Blo 1559477 26655155 := bstep (se 1 (by rfl) ⟨19991366, by rfl⟩ : syracuseStep 26655155 = 39982733) B39982733
theorem B6003137 : Blo 1559477 6003137 := bstep (se 2 (by rfl) ⟨2251176, by rfl⟩ : syracuseStep 6003137 = 4502353) B4502353
theorem B2341337 : Blo 1559477 2341337 := bstep (se 2 (by rfl) ⟨878001, by rfl⟩ : syracuseStep 2341337 = 1756003) B1756003
theorem B3512843 : Blo 1559477 3512843 := bstep (se 1 (by rfl) ⟨2634632, by rfl⟩ : syracuseStep 3512843 = 5269265) B5269265
theorem B427571725 : Blo 1559477 427571725 := bstep (se 3 (by rfl) ⟨80169698, by rfl⟩ : syracuseStep 427571725 = 160339397) B160339397
theorem B5265971 : Blo 1559477 5265971 := bstep (se 1 (by rfl) ⟨3949478, by rfl⟩ : syracuseStep 5265971 = 7898957) B7898957
theorem B3512897 : Blo 1559477 3512897 := bstep (se 2 (by rfl) ⟨1317336, by rfl⟩ : syracuseStep 3512897 = 2634673) B2634673
theorem B2341451 : Blo 1559477 2341451 := bstep (se 1 (by rfl) ⟨1756088, by rfl⟩ : syracuseStep 2341451 = 3512177) B3512177
theorem B2341463 : Blo 1559477 2341463 := bstep (se 1 (by rfl) ⟨1756097, by rfl⟩ : syracuseStep 2341463 = 3512195) B3512195
theorem B2964107 : Blo 1559477 2964107 := bstep (se 1 (by rfl) ⟨2223080, by rfl⟩ : syracuseStep 2964107 = 4446161) B4446161
theorem B2341529 : Blo 1559477 2341529 := bstep (se 2 (by rfl) ⟨878073, by rfl⟩ : syracuseStep 2341529 = 1756147) B1756147
theorem B3332801 : Blo 1559477 3332801 := bstep (se 2 (by rfl) ⟨1249800, by rfl⟩ : syracuseStep 3332801 = 2499601) B2499601
theorem B2341643 : Blo 1559477 2341643 := bstep (se 1 (by rfl) ⟨1756232, by rfl⟩ : syracuseStep 2341643 = 3512465) B3512465
theorem B2341655 : Blo 1559477 2341655 := bstep (se 1 (by rfl) ⟨1756241, by rfl⟩ : syracuseStep 2341655 = 3512483) B3512483
theorem B3513113 : Blo 1559477 3513113 := bstep (se 2 (by rfl) ⟨1317417, by rfl⟩ : syracuseStep 3513113 = 2634835) B2634835
theorem B5266241 : Blo 1559477 5266241 := bstep (se 2 (by rfl) ⟨1974840, by rfl⟩ : syracuseStep 5266241 = 3949681) B3949681
theorem B57744193 : Blo 1559477 57744193 := bstep (se 2 (by rfl) ⟨21654072, by rfl⟩ : syracuseStep 57744193 = 43308145) B43308145
theorem B2964289 : Blo 1559477 2964289 := bstep (se 2 (by rfl) ⟨1111608, by rfl⟩ : syracuseStep 2964289 = 2223217) B2223217
theorem B2341721 : Blo 1559477 2341721 := bstep (se 2 (by rfl) ⟨878145, by rfl⟩ : syracuseStep 2341721 = 1756291) B1756291
theorem B3513203 : Blo 1559477 3513203 := bstep (se 1 (by rfl) ⟨2634902, by rfl⟩ : syracuseStep 3513203 = 5269805) B5269805
theorem B3513239 : Blo 1559477 3513239 := bstep (se 1 (by rfl) ⟨2634929, by rfl⟩ : syracuseStep 3513239 = 5269859) B5269859
theorem B2341835 : Blo 1559477 2341835 := bstep (se 1 (by rfl) ⟨1756376, by rfl⟩ : syracuseStep 2341835 = 3512753) B3512753
theorem B2341847 : Blo 1559477 2341847 := bstep (se 1 (by rfl) ⟨1756385, by rfl⟩ : syracuseStep 2341847 = 3512771) B3512771
theorem B3333143 : Blo 1559477 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B2341913 : Blo 1559477 2341913 := bstep (se 2 (by rfl) ⟨878217, by rfl⟩ : syracuseStep 2341913 = 1756435) B1756435
theorem B5626955 : Blo 1559477 5626955 := bstep (se 1 (by rfl) ⟨4220216, by rfl⟩ : syracuseStep 5626955 = 8440433) B8440433
theorem B2342027 : Blo 1559477 2342027 := bstep (se 1 (by rfl) ⟨1756520, by rfl⟩ : syracuseStep 2342027 = 3513041) B3513041
theorem B2342039 : Blo 1559477 2342039 := bstep (se 1 (by rfl) ⟨1756529, by rfl⟩ : syracuseStep 2342039 = 3513059) B3513059
theorem B2849995 : Blo 1559477 2849995 := bstep (se 1 (by rfl) ⟨2137496, by rfl⟩ : syracuseStep 2849995 = 4274993) B4274993
theorem B3947737 : Blo 1559477 3947737 := bstep (se 2 (by rfl) ⟨1480401, by rfl⟩ : syracuseStep 3947737 = 2960803) B2960803
theorem B2342105 : Blo 1559477 2342105 := bstep (se 2 (by rfl) ⟨878289, by rfl⟩ : syracuseStep 2342105 = 1756579) B1756579
theorem B7896365 : Blo 1559477 7896365 := bstep (se 3 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 7896365 = 2961137) B2961137
theorem B42695981 : Blo 1559477 42695981 := bstep (se 3 (by rfl) ⟨8005496, by rfl⟩ : syracuseStep 42695981 = 16010993) B16010993
theorem B4742489 : Blo 1559477 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B5266781 : Blo 1559477 5266781 := bstep (se 3 (by rfl) ⟨987521, by rfl⟩ : syracuseStep 5266781 = 1975043) B1975043
theorem B1900055 : Blo 1559477 1900055 := bstep (se 1 (by rfl) ⟨1425041, by rfl⟩ : syracuseStep 1900055 = 2850083) B2850083
theorem B1875479 : Blo 1559477 1875479 := bstep (se 1 (by rfl) ⟨1406609, by rfl⟩ : syracuseStep 1875479 = 2813219) B2813219
theorem B8003117 : Blo 1559477 8003117 := bstep (se 3 (by rfl) ⟨1500584, by rfl⟩ : syracuseStep 8003117 = 3001169) B3001169
theorem B10821185 : Blo 1559477 10821185 := bstep (se 2 (by rfl) ⟨4057944, by rfl⟩ : syracuseStep 10821185 = 8115889) B8115889
theorem B1973899 : Blo 1559477 1973899 := bstep (se 1 (by rfl) ⟨1480424, by rfl⟩ : syracuseStep 1973899 = 2960849) B2960849
theorem B8888129 : Blo 1559477 8888129 := bstep (se 2 (by rfl) ⟨3333048, by rfl⟩ : syracuseStep 8888129 = 6666097) B6666097
theorem B7495517 : Blo 1559477 7495517 := bstep (se 3 (by rfl) ⟨1405409, by rfl⟩ : syracuseStep 7495517 = 2810819) B2810819
theorem B2604953 : Blo 1559477 2604953 := bstep (se 2 (by rfl) ⟨976857, by rfl⟩ : syracuseStep 2604953 = 1953715) B1953715
theorem B2670635 : Blo 1559477 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B7897175 : Blo 1559477 7897175 := bstep (se 1 (by rfl) ⟨5922881, by rfl⟩ : syracuseStep 7897175 = 11845763) B11845763
theorem B3948659 : Blo 1559477 3948659 := bstep (se 1 (by rfl) ⟨2961494, by rfl⟩ : syracuseStep 3948659 = 5922989) B5922989
theorem B3334279 : Blo 1559477 3334279 := bstep (se 1 (by rfl) ⟨2500709, by rfl⟩ : syracuseStep 3334279 = 5001419) B5001419
theorem B11854025 : Blo 1559477 11854025 := bstep (se 2 (by rfl) ⟨4445259, by rfl⟩ : syracuseStep 11854025 = 8890519) B8890519
theorem B3162503 : Blo 1559477 3162503 := bstep (se 1 (by rfl) ⟨2371877, by rfl⟩ : syracuseStep 3162503 = 4743755) B4743755
theorem B16875985 : Blo 1559477 16875985 := bstep (se 2 (by rfl) ⟨6328494, by rfl⟩ : syracuseStep 16875985 = 12656989) B12656989
theorem B1974775 : Blo 1559477 1974775 := bstep (se 1 (by rfl) ⟨1481081, by rfl⟩ : syracuseStep 1974775 = 2962163) B2962163
theorem B6324779 : Blo 1559477 6324779 := bstep (se 1 (by rfl) ⟨4743584, by rfl⟩ : syracuseStep 6324779 = 9487169) B9487169
theorem B7897661 : Blo 1559477 7897661 := bstep (se 3 (by rfl) ⟨1480811, by rfl⟩ : syracuseStep 7897661 = 2961623) B2961623
theorem B3949175 : Blo 1559477 3949175 := bstep (se 1 (by rfl) ⟨2961881, by rfl⟩ : syracuseStep 3949175 = 5923763) B5923763
theorem B2499191 : Blo 1559477 2499191 := bstep (se 1 (by rfl) ⟨1874393, by rfl⟩ : syracuseStep 2499191 = 3748787) B3748787
theorem B8889061 : Blo 1559477 8889061 := bstep (se 4 (by rfl) ⟨833349, by rfl⟩ : syracuseStep 8889061 = 1666699) B1666699
theorem B5268239 : Blo 1559477 5268239 := bstep (se 1 (by rfl) ⟨3951179, by rfl⟩ : syracuseStep 5268239 = 7902359) B7902359
theorem B41067299 : Blo 1559477 41067299 := bstep (se 1 (by rfl) ⟨30800474, by rfl⟩ : syracuseStep 41067299 = 61600949) B61600949
theorem B9012005 : Blo 1559477 9012005 := bstep (se 4 (by rfl) ⟨844875, by rfl⟩ : syracuseStep 9012005 = 1689751) B1689751
theorem B1975099 : Blo 1559477 1975099 := bstep (se 1 (by rfl) ⟨1481324, by rfl⟩ : syracuseStep 1975099 = 2962649) B2962649
theorem B1901447 : Blo 1559477 1901447 := bstep (se 1 (by rfl) ⟨1426085, by rfl⟩ : syracuseStep 1901447 = 2852171) B2852171
theorem B5923793 : Blo 1559477 5923793 := bstep (se 2 (by rfl) ⟨2221422, by rfl⟩ : syracuseStep 5923793 = 4442845) B4442845
theorem B9004061 : Blo 1559477 9004061 := bstep (se 3 (by rfl) ⟨1688261, by rfl⟩ : syracuseStep 9004061 = 3376523) B3376523
theorem B5268509 : Blo 1559477 5268509 := bstep (se 3 (by rfl) ⟨987845, by rfl⟩ : syracuseStep 5268509 = 1975691) B1975691
theorem B3163283 : Blo 1559477 3163283 := bstep (se 1 (by rfl) ⟨2372462, by rfl⟩ : syracuseStep 3163283 = 4744925) B4744925
theorem B4441387 : Blo 1559477 4441387 := bstep (se 1 (by rfl) ⟨3331040, by rfl⟩ : syracuseStep 4441387 = 6662081) B6662081
theorem B5924249 : Blo 1559477 5924249 := bstep (se 2 (by rfl) ⟨2221593, by rfl⟩ : syracuseStep 5924249 = 4443187) B4443187
theorem B40519091 : Blo 1559477 40519091 := bstep (se 1 (by rfl) ⟨30389318, by rfl⟩ : syracuseStep 40519091 = 60778637) B60778637
theorem B18990541 : Blo 1559477 18990541 := bstep (se 3 (by rfl) ⟨3560726, by rfl⟩ : syracuseStep 18990541 = 7121453) B7121453
theorem B9496075 : Blo 1559477 9496075 := bstep (se 1 (by rfl) ⟨7122056, by rfl⟩ : syracuseStep 9496075 = 14244113) B14244113
theorem B4441661 : Blo 1559477 4441661 := bstep (se 3 (by rfl) ⟨832811, by rfl⟩ : syracuseStep 4441661 = 1665623) B1665623
theorem B29992517 : Blo 1559477 29992517 := bstep (se 4 (by rfl) ⟨2811798, by rfl⟩ : syracuseStep 29992517 = 5623597) B5623597
theorem B22808141 : Blo 1559477 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B3950167 : Blo 1559477 3950167 := bstep (se 1 (by rfl) ⟨2962625, by rfl⟩ : syracuseStep 3950167 = 5925251) B5925251
theorem B17770103 : Blo 1559477 17770103 := bstep (se 1 (by rfl) ⟨13327577, by rfl⟩ : syracuseStep 17770103 = 26655155) B26655155
theorem B42714803 : Blo 1559477 42714803 := bstep (se 1 (by rfl) ⟨32036102, by rfl⟩ : syracuseStep 42714803 = 64072205) B64072205
theorem B1754887 : Blo 1559477 1754887 := bstep (se 1 (by rfl) ⟨1316165, by rfl⟩ : syracuseStep 1754887 = 2632331) B2632331
theorem B1976071 : Blo 1559477 1976071 := bstep (se 1 (by rfl) ⟨1482053, by rfl⟩ : syracuseStep 1976071 = 2964107) B2964107
theorem B3376939 : Blo 1559477 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B2221867 : Blo 1559477 2221867 := bstep (se 1 (by rfl) ⟨1666400, by rfl⟩ : syracuseStep 2221867 = 3332801) B3332801
theorem B3163963 : Blo 1559477 3163963 := bstep (se 1 (by rfl) ⟨2372972, by rfl⟩ : syracuseStep 3163963 = 4745945) B4745945
theorem B3950471 : Blo 1559477 3950471 := bstep (se 1 (by rfl) ⟨2962853, by rfl⟩ : syracuseStep 3950471 = 5925707) B5925707
theorem B4442003 : Blo 1559477 4442003 := bstep (se 1 (by rfl) ⟨3331502, by rfl⟩ : syracuseStep 4442003 = 6663005) B6663005
theorem B4278169 : Blo 1559477 4278169 := bstep (se 2 (by rfl) ⟨1604313, by rfl⟩ : syracuseStep 4278169 = 3208627) B3208627
theorem B1755067 : Blo 1559477 1755067 := bstep (se 1 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 1755067 = 2632601) B2632601
theorem B3950603 : Blo 1559477 3950603 := bstep (se 1 (by rfl) ⟨2962952, by rfl⟩ : syracuseStep 3950603 = 5925905) B5925905
theorem B2222095 : Blo 1559477 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B2631865 : Blo 1559477 2631865 := bstep (se 2 (by rfl) ⟨986949, by rfl⟩ : syracuseStep 2631865 = 1973899) B1973899
theorem B7899443 : Blo 1559477 7899443 := bstep (se 1 (by rfl) ⟨5924582, by rfl⟩ : syracuseStep 7899443 = 11849165) B11849165
theorem B5335411 : Blo 1559477 5335411 := bstep (se 1 (by rfl) ⟨4001558, by rfl⟩ : syracuseStep 5335411 = 8003117) B8003117
theorem B1755535 : Blo 1559477 1755535 := bstep (se 1 (by rfl) ⟨1316651, by rfl⟩ : syracuseStep 1755535 = 2633303) B2633303
theorem B5269913 : Blo 1559477 5269913 := bstep (se 2 (by rfl) ⟨1976217, by rfl⟩ : syracuseStep 5269913 = 3952435) B3952435
theorem B3951119 : Blo 1559477 3951119 := bstep (se 1 (by rfl) ⟨2963339, by rfl⟩ : syracuseStep 3951119 = 5926679) B5926679
theorem B5925419 : Blo 1559477 5925419 := bstep (se 1 (by rfl) ⟨4444064, by rfl⟩ : syracuseStep 5925419 = 8888129) B8888129
theorem B7899767 : Blo 1559477 7899767 := bstep (se 1 (by rfl) ⟨5924825, by rfl⟩ : syracuseStep 7899767 = 11849651) B11849651
theorem B3508883 : Blo 1559477 3508883 := bstep (se 1 (by rfl) ⟨2631662, by rfl⟩ : syracuseStep 3508883 = 5263325) B5263325
theorem B3951251 : Blo 1559477 3951251 := bstep (se 1 (by rfl) ⟨2963438, by rfl⟩ : syracuseStep 3951251 = 5926877) B5926877
theorem B3508937 : Blo 1559477 3508937 := bstep (se 2 (by rfl) ⟨1315851, by rfl⟩ : syracuseStep 3508937 = 2631703) B2631703
theorem B20007769 : Blo 1559477 20007769 := bstep (se 2 (by rfl) ⟨7502913, by rfl⟩ : syracuseStep 20007769 = 15005827) B15005827
theorem B2632567 : Blo 1559477 2632567 := bstep (se 1 (by rfl) ⟨1974425, by rfl⟩ : syracuseStep 2632567 = 3948851) B3948851
theorem B1756039 : Blo 1559477 1756039 := bstep (se 1 (by rfl) ⟨1317029, by rfl⟩ : syracuseStep 1756039 = 2634059) B2634059
theorem B1559483 : Blo 1559477 1559483 := bstep (se 1 (by rfl) ⟨1169612, by rfl⟩ : syracuseStep 1559483 = 2339225) B2339225
theorem B1559559 : Blo 1559477 1559559 := bstep (se 1 (by rfl) ⟨1169669, by rfl⟩ : syracuseStep 1559559 = 2339339) B2339339
theorem B7498763 : Blo 1559477 7498763 := bstep (se 1 (by rfl) ⟨5624072, by rfl⟩ : syracuseStep 7498763 = 11248145) B11248145
theorem B1559567 : Blo 1559477 1559567 := bstep (se 1 (by rfl) ⟨1169675, by rfl⟩ : syracuseStep 1559567 = 2339351) B2339351
theorem B8883229 : Blo 1559477 8883229 := bstep (se 3 (by rfl) ⟨1665605, by rfl⟩ : syracuseStep 8883229 = 3331211) B3331211
theorem B1559611 : Blo 1559477 1559611 := bstep (se 1 (by rfl) ⟨1169708, by rfl⟩ : syracuseStep 1559611 = 2339417) B2339417
theorem B2632763 : Blo 1559477 2632763 := bstep (se 1 (by rfl) ⟨1974572, by rfl⟩ : syracuseStep 2632763 = 3949145) B3949145
theorem B1756219 : Blo 1559477 1756219 := bstep (se 1 (by rfl) ⟨1317164, by rfl⟩ : syracuseStep 1756219 = 2634329) B2634329
theorem B11242583 : Blo 1559477 11242583 := bstep (se 1 (by rfl) ⟨8431937, by rfl⟩ : syracuseStep 11242583 = 16863875) B16863875
theorem B1559687 : Blo 1559477 1559687 := bstep (se 1 (by rfl) ⟨1169765, by rfl⟩ : syracuseStep 1559687 = 2339531) B2339531
theorem B1559695 : Blo 1559477 1559695 := bstep (se 1 (by rfl) ⟨1169771, by rfl⟩ : syracuseStep 1559695 = 2339543) B2339543
theorem B1559739 : Blo 1559477 1559739 := bstep (se 1 (by rfl) ⟨1169804, by rfl⟩ : syracuseStep 1559739 = 2339609) B2339609
theorem B5000393 : Blo 1559477 5000393 := bstep (se 2 (by rfl) ⟨1875147, by rfl⟩ : syracuseStep 5000393 = 3750295) B3750295
theorem B1559815 : Blo 1559477 1559815 := bstep (se 1 (by rfl) ⟨1169861, by rfl⟩ : syracuseStep 1559815 = 2339723) B2339723
theorem B1559823 : Blo 1559477 1559823 := bstep (se 1 (by rfl) ⟨1169867, by rfl⟩ : syracuseStep 1559823 = 2339735) B2339735
theorem B1559867 : Blo 1559477 1559867 := bstep (se 1 (by rfl) ⟨1169900, by rfl⟩ : syracuseStep 1559867 = 2339801) B2339801
theorem B3509639 : Blo 1559477 3509639 := bstep (se 1 (by rfl) ⟨2632229, by rfl⟩ : syracuseStep 3509639 = 5264459) B5264459
theorem B1559943 : Blo 1559477 1559943 := bstep (se 1 (by rfl) ⟨1169957, by rfl⟩ : syracuseStep 1559943 = 2339915) B2339915
theorem B1559951 : Blo 1559477 1559951 := bstep (se 1 (by rfl) ⟨1169963, by rfl⟩ : syracuseStep 1559951 = 2339927) B2339927
theorem B8891795 : Blo 1559477 8891795 := bstep (se 1 (by rfl) ⟨6668846, by rfl⟩ : syracuseStep 8891795 = 13337693) B13337693
theorem B1559995 : Blo 1559477 1559995 := bstep (se 1 (by rfl) ⟨1169996, by rfl⟩ : syracuseStep 1559995 = 2339993) B2339993
theorem B2633161 : Blo 1559477 2633161 := bstep (se 2 (by rfl) ⟨987435, by rfl⟩ : syracuseStep 2633161 = 1974871) B1974871
theorem B1560071 : Blo 1559477 1560071 := bstep (se 1 (by rfl) ⟨1170053, by rfl⟩ : syracuseStep 1560071 = 2340107) B2340107
theorem B1560079 : Blo 1559477 1560079 := bstep (se 1 (by rfl) ⟨1170059, by rfl⟩ : syracuseStep 1560079 = 2340119) B2340119
theorem B8883755 : Blo 1559477 8883755 := bstep (se 1 (by rfl) ⟨6662816, by rfl⟩ : syracuseStep 8883755 = 13325633) B13325633
theorem B3509819 : Blo 1559477 3509819 := bstep (se 1 (by rfl) ⟨2632364, by rfl⟩ : syracuseStep 3509819 = 5264729) B5264729
theorem B1560123 : Blo 1559477 1560123 := bstep (se 1 (by rfl) ⟨1170092, by rfl⟩ : syracuseStep 1560123 = 2340185) B2340185
theorem B7900739 : Blo 1559477 7900739 := bstep (se 1 (by rfl) ⟨5925554, by rfl⟩ : syracuseStep 7900739 = 11851109) B11851109
theorem B16019045 : Blo 1559477 16019045 := bstep (se 4 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 16019045 = 3003571) B3003571
theorem B2961031 : Blo 1559477 2961031 := bstep (se 1 (by rfl) ⟨2220773, by rfl⟩ : syracuseStep 2961031 = 4441547) B4441547
theorem B1560199 : Blo 1559477 1560199 := bstep (se 1 (by rfl) ⟨1170149, by rfl⟩ : syracuseStep 1560199 = 2340299) B2340299
theorem B1560207 : Blo 1559477 1560207 := bstep (se 1 (by rfl) ⟨1170155, by rfl⟩ : syracuseStep 1560207 = 2340311) B2340311
theorem B3509945 : Blo 1559477 3509945 := bstep (se 2 (by rfl) ⟨1316229, by rfl⟩ : syracuseStep 3509945 = 2632459) B2632459
theorem B1560251 : Blo 1559477 1560251 := bstep (se 1 (by rfl) ⟨1170188, by rfl⟩ : syracuseStep 1560251 = 2340377) B2340377
theorem B5336833 : Blo 1559477 5336833 := bstep (se 2 (by rfl) ⟨2001312, by rfl⟩ : syracuseStep 5336833 = 4002625) B4002625
theorem B76992257 : Blo 1559477 76992257 := bstep (se 2 (by rfl) ⟨28872096, by rfl⟩ : syracuseStep 76992257 = 57744193) B57744193
theorem B3952385 : Blo 1559477 3952385 := bstep (se 2 (by rfl) ⟨1482144, by rfl⟩ : syracuseStep 3952385 = 2964289) B2964289
theorem B1560327 : Blo 1559477 1560327 := bstep (se 1 (by rfl) ⟨1170245, by rfl⟩ : syracuseStep 1560327 = 2340491) B2340491
theorem B1560335 : Blo 1559477 1560335 := bstep (se 1 (by rfl) ⟨1170251, by rfl⟩ : syracuseStep 1560335 = 2340503) B2340503
theorem B9490213 : Blo 1559477 9490213 := bstep (se 4 (by rfl) ⟨889707, by rfl⟩ : syracuseStep 9490213 = 1779415) B1779415
theorem B6663995 : Blo 1559477 6663995 := bstep (se 1 (by rfl) ⟨4997996, by rfl⟩ : syracuseStep 6663995 = 9995993) B9995993
theorem B1560379 : Blo 1559477 1560379 := bstep (se 1 (by rfl) ⟨1170284, by rfl⟩ : syracuseStep 1560379 = 2340569) B2340569
theorem B1560455 : Blo 1559477 1560455 := bstep (se 1 (by rfl) ⟨1170341, by rfl⟩ : syracuseStep 1560455 = 2340683) B2340683
theorem B7901063 : Blo 1559477 7901063 := bstep (se 1 (by rfl) ⟨5925797, by rfl⟩ : syracuseStep 7901063 = 11851595) B11851595
theorem B1560463 : Blo 1559477 1560463 := bstep (se 1 (by rfl) ⟨1170347, by rfl⟩ : syracuseStep 1560463 = 2340695) B2340695
theorem B1560507 : Blo 1559477 1560507 := bstep (se 1 (by rfl) ⟨1170380, by rfl⟩ : syracuseStep 1560507 = 2340761) B2340761
theorem B1560583 : Blo 1559477 1560583 := bstep (se 1 (by rfl) ⟨1170437, by rfl⟩ : syracuseStep 1560583 = 2340875) B2340875
theorem B3510287 : Blo 1559477 3510287 := bstep (se 1 (by rfl) ⟨2632715, by rfl⟩ : syracuseStep 3510287 = 5265431) B5265431
theorem B1560591 : Blo 1559477 1560591 := bstep (se 1 (by rfl) ⟨1170443, by rfl⟩ : syracuseStep 1560591 = 2340887) B2340887
theorem B3510305 : Blo 1559477 3510305 := bstep (se 2 (by rfl) ⟨1316364, by rfl⟩ : syracuseStep 3510305 = 2632729) B2632729
theorem B3747883 : Blo 1559477 3747883 := bstep (se 1 (by rfl) ⟨2810912, by rfl⟩ : syracuseStep 3747883 = 5621825) B5621825
theorem B1560635 : Blo 1559477 1560635 := bstep (se 1 (by rfl) ⟨1170476, by rfl⟩ : syracuseStep 1560635 = 2340953) B2340953
theorem B5066813 : Blo 1559477 5066813 := bstep (se 3 (by rfl) ⟨950027, by rfl⟩ : syracuseStep 5066813 = 1900055) B1900055
theorem B6328381 : Blo 1559477 6328381 := bstep (se 3 (by rfl) ⟨1186571, by rfl⟩ : syracuseStep 6328381 = 2373143) B2373143
theorem B5001277 : Blo 1559477 5001277 := bstep (se 3 (by rfl) ⟨937739, by rfl⟩ : syracuseStep 5001277 = 1875479) B1875479
theorem B4444247 : Blo 1559477 4444247 := bstep (se 1 (by rfl) ⟨3333185, by rfl⟩ : syracuseStep 4444247 = 6666371) B6666371
theorem B8892503 : Blo 1559477 8892503 := bstep (se 1 (by rfl) ⟨6669377, by rfl⟩ : syracuseStep 8892503 = 13338755) B13338755
theorem B64065629 : Blo 1559477 64065629 := bstep (se 3 (by rfl) ⟨12012305, by rfl⟩ : syracuseStep 64065629 = 24024611) B24024611
theorem B1560711 : Blo 1559477 1560711 := bstep (se 1 (by rfl) ⟨1170533, by rfl⟩ : syracuseStep 1560711 = 2341067) B2341067
theorem B2633863 : Blo 1559477 2633863 := bstep (se 1 (by rfl) ⟨1975397, by rfl⟩ : syracuseStep 2633863 = 3950795) B3950795
theorem B1560719 : Blo 1559477 1560719 := bstep (se 1 (by rfl) ⟨1170539, by rfl⟩ : syracuseStep 1560719 = 2341079) B2341079
theorem B3854483 : Blo 1559477 3854483 := bstep (se 1 (by rfl) ⟨2890862, by rfl⟩ : syracuseStep 3854483 = 5781725) B5781725
theorem B2961593 : Blo 1559477 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B1560763 : Blo 1559477 1560763 := bstep (se 1 (by rfl) ⟨1170572, by rfl⟩ : syracuseStep 1560763 = 2341145) B2341145
theorem B1560839 : Blo 1559477 1560839 := bstep (se 1 (by rfl) ⟨1170629, by rfl⟩ : syracuseStep 1560839 = 2341259) B2341259
theorem B1560847 : Blo 1559477 1560847 := bstep (se 1 (by rfl) ⟨1170635, by rfl⟩ : syracuseStep 1560847 = 2341271) B2341271
theorem B5263649 : Blo 1559477 5263649 := bstep (se 2 (by rfl) ⟨1973868, by rfl⟩ : syracuseStep 5263649 = 3947737) B3947737
theorem B4002091 : Blo 1559477 4002091 := bstep (se 1 (by rfl) ⟨3001568, by rfl⟩ : syracuseStep 4002091 = 6003137) B6003137
theorem B1560891 : Blo 1559477 1560891 := bstep (se 1 (by rfl) ⟨1170668, by rfl⟩ : syracuseStep 1560891 = 2341337) B2341337
theorem B3510647 : Blo 1559477 3510647 := bstep (se 1 (by rfl) ⟨2632985, by rfl⟩ : syracuseStep 3510647 = 5265971) B5265971
theorem B1560967 : Blo 1559477 1560967 := bstep (se 1 (by rfl) ⟨1170725, by rfl⟩ : syracuseStep 1560967 = 2341451) B2341451
theorem B1560975 : Blo 1559477 1560975 := bstep (se 1 (by rfl) ⟨1170731, by rfl⟩ : syracuseStep 1560975 = 2341463) B2341463
theorem B4747673 : Blo 1559477 4747673 := bstep (se 2 (by rfl) ⟨1780377, by rfl⟩ : syracuseStep 4747673 = 3560755) B3560755
theorem B2339243 : Blo 1559477 2339243 := bstep (se 1 (by rfl) ⟨1754432, by rfl⟩ : syracuseStep 2339243 = 3508865) B3508865
theorem B1561019 : Blo 1559477 1561019 := bstep (se 1 (by rfl) ⟨1170764, by rfl⟩ : syracuseStep 1561019 = 2341529) B2341529
theorem B2339273 : Blo 1559477 2339273 := bstep (se 2 (by rfl) ⟨877227, by rfl⟩ : syracuseStep 2339273 = 1754455) B1754455
theorem B4501961 : Blo 1559477 4501961 := bstep (se 2 (by rfl) ⟨1688235, by rfl⟩ : syracuseStep 4501961 = 3376471) B3376471
theorem B5927377 : Blo 1559477 5927377 := bstep (se 2 (by rfl) ⟨2222766, by rfl⟩ : syracuseStep 5927377 = 4445533) B4445533
theorem B1561095 : Blo 1559477 1561095 := bstep (se 1 (by rfl) ⟨1170821, by rfl⟩ : syracuseStep 1561095 = 2341643) B2341643
theorem B1561103 : Blo 1559477 1561103 := bstep (se 1 (by rfl) ⟨1170827, by rfl⟩ : syracuseStep 1561103 = 2341655) B2341655
theorem B3510827 : Blo 1559477 3510827 := bstep (se 1 (by rfl) ⟨2633120, by rfl⟩ : syracuseStep 3510827 = 5266241) B5266241
theorem B2339387 : Blo 1559477 2339387 := bstep (se 1 (by rfl) ⟨1754540, by rfl⟩ : syracuseStep 2339387 = 3509081) B3509081
theorem B1561147 : Blo 1559477 1561147 := bstep (se 1 (by rfl) ⟨1170860, by rfl⟩ : syracuseStep 1561147 = 2341721) B2341721
theorem B2339447 : Blo 1559477 2339447 := bstep (se 1 (by rfl) ⟨1754585, by rfl⟩ : syracuseStep 2339447 = 3509171) B3509171
theorem B1561223 : Blo 1559477 1561223 := bstep (se 1 (by rfl) ⟨1170917, by rfl⟩ : syracuseStep 1561223 = 2341835) B2341835
theorem B2339471 : Blo 1559477 2339471 := bstep (se 1 (by rfl) ⟨1754603, by rfl⟩ : syracuseStep 2339471 = 3509207) B3509207
theorem B1561231 : Blo 1559477 1561231 := bstep (se 1 (by rfl) ⟨1170923, by rfl⟩ : syracuseStep 1561231 = 2341847) B2341847
theorem B2372267 : Blo 1559477 2372267 := bstep (se 1 (by rfl) ⟨1779200, by rfl⟩ : syracuseStep 2372267 = 3558401) B3558401
theorem B2339513 : Blo 1559477 2339513 := bstep (se 2 (by rfl) ⟨877317, by rfl⟩ : syracuseStep 2339513 = 1754635) B1754635
theorem B1561275 : Blo 1559477 1561275 := bstep (se 1 (by rfl) ⟨1170956, by rfl⟩ : syracuseStep 1561275 = 2341913) B2341913
theorem B5927681 : Blo 1559477 5927681 := bstep (se 2 (by rfl) ⟨2222880, by rfl⟩ : syracuseStep 5927681 = 4445761) B4445761
theorem B2339591 : Blo 1559477 2339591 := bstep (se 1 (by rfl) ⟨1754693, by rfl⟩ : syracuseStep 2339591 = 3509387) B3509387
theorem B1561351 : Blo 1559477 1561351 := bstep (se 1 (by rfl) ⟨1171013, by rfl⟩ : syracuseStep 1561351 = 2342027) B2342027
theorem B2634511 : Blo 1559477 2634511 := bstep (se 1 (by rfl) ⟨1975883, by rfl⟩ : syracuseStep 2634511 = 3951767) B3951767
theorem B1561359 : Blo 1559477 1561359 := bstep (se 1 (by rfl) ⟨1171019, by rfl⟩ : syracuseStep 1561359 = 2342039) B2342039
theorem B2339627 : Blo 1559477 2339627 := bstep (se 1 (by rfl) ⟨1754720, by rfl⟩ : syracuseStep 2339627 = 3509441) B3509441
theorem B1561403 : Blo 1559477 1561403 := bstep (se 1 (by rfl) ⟨1171052, by rfl⟩ : syracuseStep 1561403 = 2342105) B2342105
theorem B4502333 : Blo 1559477 4502333 := bstep (se 3 (by rfl) ⟨844187, by rfl⟩ : syracuseStep 4502333 = 1688375) B1688375
theorem B2339657 : Blo 1559477 2339657 := bstep (se 2 (by rfl) ⟨877371, by rfl⟩ : syracuseStep 2339657 = 1754743) B1754743
theorem B5264243 : Blo 1559477 5264243 := bstep (se 1 (by rfl) ⟨3948182, by rfl⟩ : syracuseStep 5264243 = 7896365) B7896365
theorem B28463987 : Blo 1559477 28463987 := bstep (se 1 (by rfl) ⟨21347990, by rfl⟩ : syracuseStep 28463987 = 42695981) B42695981
theorem B3511187 : Blo 1559477 3511187 := bstep (se 1 (by rfl) ⟨2633390, by rfl⟩ : syracuseStep 3511187 = 5266781) B5266781
theorem B2339771 : Blo 1559477 2339771 := bstep (se 1 (by rfl) ⟨1754828, by rfl⟩ : syracuseStep 2339771 = 3509657) B3509657
theorem B3511241 : Blo 1559477 3511241 := bstep (se 2 (by rfl) ⟨1316715, by rfl⟩ : syracuseStep 3511241 = 2633431) B2633431
theorem B8885213 : Blo 1559477 8885213 := bstep (se 3 (by rfl) ⟨1665977, by rfl⟩ : syracuseStep 8885213 = 3331955) B3331955
theorem B2339831 : Blo 1559477 2339831 := bstep (se 1 (by rfl) ⟨1754873, by rfl⟩ : syracuseStep 2339831 = 3509747) B3509747
theorem B2339855 : Blo 1559477 2339855 := bstep (se 1 (by rfl) ⟨1754891, by rfl⟩ : syracuseStep 2339855 = 3509783) B3509783
theorem B7214123 : Blo 1559477 7214123 := bstep (se 1 (by rfl) ⟨5410592, by rfl⟩ : syracuseStep 7214123 = 10821185) B10821185
theorem B2339897 : Blo 1559477 2339897 := bstep (se 2 (by rfl) ⟨877461, by rfl⟩ : syracuseStep 2339897 = 1754923) B1754923
theorem B2339975 : Blo 1559477 2339975 := bstep (se 1 (by rfl) ⟨1754981, by rfl⟩ : syracuseStep 2339975 = 3509963) B3509963
theorem B2340011 : Blo 1559477 2340011 := bstep (se 1 (by rfl) ⟨1755008, by rfl⟩ : syracuseStep 2340011 = 3510017) B3510017
theorem B2340041 : Blo 1559477 2340041 := bstep (se 2 (by rfl) ⟨877515, by rfl⟩ : syracuseStep 2340041 = 1755031) B1755031
theorem B5928137 : Blo 1559477 5928137 := bstep (se 2 (by rfl) ⟨2223051, by rfl⟩ : syracuseStep 5928137 = 4446103) B4446103
theorem B2340155 : Blo 1559477 2340155 := bstep (se 1 (by rfl) ⟨1755116, by rfl⟩ : syracuseStep 2340155 = 3510233) B3510233
theorem B2962747 : Blo 1559477 2962747 := bstep (se 1 (by rfl) ⟨2222060, by rfl⟩ : syracuseStep 2962747 = 4444121) B4444121
theorem B2340215 : Blo 1559477 2340215 := bstep (se 1 (by rfl) ⟨1755161, by rfl⟩ : syracuseStep 2340215 = 3510323) B3510323
theorem B2340239 : Blo 1559477 2340239 := bstep (se 1 (by rfl) ⟨1755179, by rfl⟩ : syracuseStep 2340239 = 3510359) B3510359
theorem B3749267 : Blo 1559477 3749267 := bstep (se 1 (by rfl) ⟨2811950, by rfl⟩ : syracuseStep 3749267 = 5623901) B5623901
theorem B2340281 : Blo 1559477 2340281 := bstep (se 2 (by rfl) ⟨877605, by rfl⟩ : syracuseStep 2340281 = 1755211) B1755211
theorem B2340359 : Blo 1559477 2340359 := bstep (se 1 (by rfl) ⟨1755269, by rfl⟩ : syracuseStep 2340359 = 3510539) B3510539
theorem B15005213 : Blo 1559477 15005213 := bstep (se 3 (by rfl) ⟨2813477, by rfl⟩ : syracuseStep 15005213 = 5626955) B5626955
theorem B2340395 : Blo 1559477 2340395 := bstep (se 1 (by rfl) ⟨1755296, by rfl⟩ : syracuseStep 2340395 = 3510593) B3510593
theorem B2340425 : Blo 1559477 2340425 := bstep (se 2 (by rfl) ⟨877659, by rfl⟩ : syracuseStep 2340425 = 1755319) B1755319
theorem B3511943 : Blo 1559477 3511943 := bstep (se 1 (by rfl) ⟨2633957, by rfl⟩ : syracuseStep 3511943 = 5267915) B5267915
theorem B2340539 : Blo 1559477 2340539 := bstep (se 1 (by rfl) ⟨1755404, by rfl⟩ : syracuseStep 2340539 = 3510809) B3510809
theorem B2340599 : Blo 1559477 2340599 := bstep (se 1 (by rfl) ⟨1755449, by rfl⟩ : syracuseStep 2340599 = 3510899) B3510899
theorem B2340623 : Blo 1559477 2340623 := bstep (se 1 (by rfl) ⟨1755467, by rfl⟩ : syracuseStep 2340623 = 3510935) B3510935
theorem B2963233 : Blo 1559477 2963233 := bstep (se 2 (by rfl) ⟨1111212, by rfl⟩ : syracuseStep 2963233 = 2222425) B2222425
theorem B2340665 : Blo 1559477 2340665 := bstep (se 2 (by rfl) ⟨877749, by rfl⟩ : syracuseStep 2340665 = 1755499) B1755499
theorem B3512123 : Blo 1559477 3512123 := bstep (se 1 (by rfl) ⟨2634092, by rfl⟩ : syracuseStep 3512123 = 5268185) B5268185
theorem B2340743 : Blo 1559477 2340743 := bstep (se 1 (by rfl) ⟨1755557, by rfl⟩ : syracuseStep 2340743 = 3511115) B3511115
theorem B2340779 : Blo 1559477 2340779 := bstep (se 1 (by rfl) ⟨1755584, by rfl⟩ : syracuseStep 2340779 = 3511169) B3511169
theorem B3512249 : Blo 1559477 3512249 := bstep (se 2 (by rfl) ⟨1317093, by rfl⟩ : syracuseStep 3512249 = 2634187) B2634187
theorem B2340809 : Blo 1559477 2340809 := bstep (se 2 (by rfl) ⟨877803, by rfl⟩ : syracuseStep 2340809 = 1755607) B1755607
theorem B570095633 : Blo 1559477 570095633 := bstep (se 2 (by rfl) ⟨213785862, by rfl⟩ : syracuseStep 570095633 = 427571725) B427571725
theorem B19994647 : Blo 1559477 19994647 := bstep (se 1 (by rfl) ⟨14995985, by rfl⟩ : syracuseStep 19994647 = 29991971) B29991971
theorem B7895069 : Blo 1559477 7895069 := bstep (se 3 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 7895069 = 2960651) B2960651
theorem B2340923 : Blo 1559477 2340923 := bstep (se 1 (by rfl) ⟨1755692, by rfl⟩ : syracuseStep 2340923 = 3511385) B3511385
theorem B2250871 : Blo 1559477 2250871 := bstep (se 1 (by rfl) ⟨1688153, by rfl⟩ : syracuseStep 2250871 = 3376307) B3376307
theorem B2340983 : Blo 1559477 2340983 := bstep (se 1 (by rfl) ⟨1755737, by rfl⟩ : syracuseStep 2340983 = 3511475) B3511475
theorem B2341007 : Blo 1559477 2341007 := bstep (se 1 (by rfl) ⟨1755755, by rfl⟩ : syracuseStep 2341007 = 3511511) B3511511
theorem B4217017 : Blo 1559477 4217017 := bstep (se 2 (by rfl) ⟨1581381, by rfl⟩ : syracuseStep 4217017 = 3162763) B3162763
theorem B2341049 : Blo 1559477 2341049 := bstep (se 2 (by rfl) ⟨877893, by rfl⟩ : syracuseStep 2341049 = 1755787) B1755787
theorem B2668745 : Blo 1559477 2668745 := bstep (se 2 (by rfl) ⟨1000779, by rfl⟩ : syracuseStep 2668745 = 2001559) B2001559
theorem B2341127 : Blo 1559477 2341127 := bstep (se 1 (by rfl) ⟨1755845, by rfl⟩ : syracuseStep 2341127 = 3511691) B3511691
theorem B3512591 : Blo 1559477 3512591 := bstep (se 1 (by rfl) ⟨2634443, by rfl⟩ : syracuseStep 3512591 = 5268887) B5268887
theorem B3512609 : Blo 1559477 3512609 := bstep (se 2 (by rfl) ⟨1317228, by rfl⟩ : syracuseStep 3512609 = 2634457) B2634457
theorem B2341163 : Blo 1559477 2341163 := bstep (se 1 (by rfl) ⟨1755872, by rfl⟩ : syracuseStep 2341163 = 3511745) B3511745
theorem B2341193 : Blo 1559477 2341193 := bstep (se 2 (by rfl) ⟨877947, by rfl⟩ : syracuseStep 2341193 = 1755895) B1755895
theorem B17783225 : Blo 1559477 17783225 := bstep (se 2 (by rfl) ⟨6668709, by rfl⟩ : syracuseStep 17783225 = 13337419) B13337419
theorem B2341307 : Blo 1559477 2341307 := bstep (se 1 (by rfl) ⟨1755980, by rfl⟩ : syracuseStep 2341307 = 3511961) B3511961
theorem B18987473 : Blo 1559477 18987473 := bstep (se 2 (by rfl) ⟨7120302, by rfl⟩ : syracuseStep 18987473 = 14240605) B14240605
theorem B2341367 : Blo 1559477 2341367 := bstep (se 1 (by rfl) ⟨1756025, by rfl⟩ : syracuseStep 2341367 = 3512051) B3512051
theorem B3750401 : Blo 1559477 3750401 := bstep (se 2 (by rfl) ⟨1406400, by rfl⟩ : syracuseStep 3750401 = 2812801) B2812801
theorem B7895555 : Blo 1559477 7895555 := bstep (se 1 (by rfl) ⟨5921666, by rfl⟩ : syracuseStep 7895555 = 11843333) B11843333
theorem B2341391 : Blo 1559477 2341391 := bstep (se 1 (by rfl) ⟨1756043, by rfl⟩ : syracuseStep 2341391 = 3512087) B3512087
theorem B2341433 : Blo 1559477 2341433 := bstep (se 2 (by rfl) ⟨878037, by rfl⟩ : syracuseStep 2341433 = 1756075) B1756075
theorem B10001015 : Blo 1559477 10001015 := bstep (se 1 (by rfl) ⟨7500761, by rfl⟩ : syracuseStep 10001015 = 15001523) B15001523
theorem B3512951 : Blo 1559477 3512951 := bstep (se 1 (by rfl) ⟨2634713, by rfl⟩ : syracuseStep 3512951 = 5269427) B5269427
theorem B2341511 : Blo 1559477 2341511 := bstep (se 1 (by rfl) ⟨1756133, by rfl⟩ : syracuseStep 2341511 = 3512267) B3512267
theorem B2341547 : Blo 1559477 2341547 := bstep (se 1 (by rfl) ⟨1756160, by rfl⟩ : syracuseStep 2341547 = 3512321) B3512321
theorem B11246273 : Blo 1559477 11246273 := bstep (se 2 (by rfl) ⟨4217352, by rfl⟩ : syracuseStep 11246273 = 8434705) B8434705
theorem B2341577 : Blo 1559477 2341577 := bstep (se 2 (by rfl) ⟨878091, by rfl⟩ : syracuseStep 2341577 = 1756183) B1756183
theorem B3513131 : Blo 1559477 3513131 := bstep (se 1 (by rfl) ⟨2634848, by rfl⟩ : syracuseStep 3513131 = 5269697) B5269697
theorem B2341691 : Blo 1559477 2341691 := bstep (se 1 (by rfl) ⟨1756268, by rfl⟩ : syracuseStep 2341691 = 3512537) B3512537
theorem B6323059 : Blo 1559477 6323059 := bstep (se 1 (by rfl) ⟨4742294, by rfl⟩ : syracuseStep 6323059 = 9484589) B9484589
theorem B2341751 : Blo 1559477 2341751 := bstep (se 1 (by rfl) ⟨1756313, by rfl⟩ : syracuseStep 2341751 = 3512627) B3512627
theorem B2341775 : Blo 1559477 2341775 := bstep (se 1 (by rfl) ⟨1756331, by rfl⟩ : syracuseStep 2341775 = 3512663) B3512663
theorem B3799993 : Blo 1559477 3799993 := bstep (se 2 (by rfl) ⟨1424997, by rfl⟩ : syracuseStep 3799993 = 2849995) B2849995
theorem B2341817 : Blo 1559477 2341817 := bstep (se 2 (by rfl) ⟨878181, by rfl⟩ : syracuseStep 2341817 = 1756363) B1756363
theorem B2341895 : Blo 1559477 2341895 := bstep (se 1 (by rfl) ⟨1756421, by rfl⟩ : syracuseStep 2341895 = 3512843) B3512843
theorem B2341931 : Blo 1559477 2341931 := bstep (se 1 (by rfl) ⟨1756448, by rfl⟩ : syracuseStep 2341931 = 3512897) B3512897
theorem B2341961 : Blo 1559477 2341961 := bstep (se 2 (by rfl) ⟨878235, by rfl⟩ : syracuseStep 2341961 = 1756471) B1756471
theorem B2342075 : Blo 1559477 2342075 := bstep (se 1 (by rfl) ⟨1756556, by rfl⟩ : syracuseStep 2342075 = 3513113) B3513113
theorem B346455245 : Blo 1559477 346455245 := bstep (se 3 (by rfl) ⟨64960358, by rfl⟩ : syracuseStep 346455245 = 129920717) B129920717
theorem B2342135 : Blo 1559477 2342135 := bstep (se 1 (by rfl) ⟨1756601, by rfl⟩ : syracuseStep 2342135 = 3513203) B3513203
theorem B2342159 : Blo 1559477 2342159 := bstep (se 1 (by rfl) ⟨1756619, by rfl⟩ : syracuseStep 2342159 = 3513239) B3513239
theorem B8887603 : Blo 1559477 8887603 := bstep (se 1 (by rfl) ⟨6665702, by rfl⟩ : syracuseStep 8887603 = 13331405) B13331405
theorem B2342201 : Blo 1559477 2342201 := bstep (se 2 (by rfl) ⟨878325, by rfl⟩ : syracuseStep 2342201 = 1756651) B1756651
theorem B7904627 : Blo 1559477 7904627 := bstep (se 1 (by rfl) ⟨5928470, by rfl⟩ : syracuseStep 7904627 = 11856941) B11856941
theorem B5266835 : Blo 1559477 5266835 := bstep (se 1 (by rfl) ⟨3950126, by rfl⟩ : syracuseStep 5266835 = 7900253) B7900253
theorem B30006733 : Blo 1559477 30006733 := bstep (se 3 (by rfl) ⟨5626262, by rfl⟩ : syracuseStep 30006733 = 11252525) B11252525
theorem B16014851 : Blo 1559477 16014851 := bstep (se 1 (by rfl) ⟨12011138, by rfl⟩ : syracuseStep 16014851 = 24022277) B24022277
theorem B4218401 : Blo 1559477 4218401 := bstep (se 2 (by rfl) ⟨1581900, by rfl⟩ : syracuseStep 4218401 = 3163801) B3163801
theorem B1973803 : Blo 1559477 1973803 := bstep (se 1 (by rfl) ⟨1480352, by rfl⟩ : syracuseStep 1973803 = 2960705) B2960705
theorem B3161659 : Blo 1559477 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B2498249 : Blo 1559477 2498249 := bstep (se 2 (by rfl) ⟨936843, by rfl⟩ : syracuseStep 2498249 = 1873687) B1873687
theorem B14991065 : Blo 1559477 14991065 := bstep (se 2 (by rfl) ⟨5621649, by rfl⟩ : syracuseStep 14991065 = 11243299) B11243299
theorem B6946541 : Blo 1559477 6946541 := bstep (se 3 (by rfl) ⟨1302476, by rfl⟩ : syracuseStep 6946541 = 2604953) B2604953
theorem B8437537 : Blo 1559477 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B17342257 : Blo 1559477 17342257 := bstep (se 2 (by rfl) ⟨6503346, by rfl⟩ : syracuseStep 17342257 = 13006693) B13006693
theorem B4997011 : Blo 1559477 4997011 := bstep (se 1 (by rfl) ⟨3747758, by rfl⟩ : syracuseStep 4997011 = 7495517) B7495517
theorem B4997177 : Blo 1559477 4997177 := bstep (se 2 (by rfl) ⟨1873941, by rfl⟩ : syracuseStep 4997177 = 3747883) B3747883
theorem B8437841 : Blo 1559477 8437841 := bstep (se 2 (by rfl) ⟨3164190, by rfl⟩ : syracuseStep 8437841 = 6328381) B6328381
theorem B6668369 : Blo 1559477 6668369 := bstep (se 2 (by rfl) ⟨2500638, by rfl⟩ : syracuseStep 6668369 = 5001277) B5001277
theorem B1974395 : Blo 1559477 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B27378199 : Blo 1559477 27378199 := bstep (se 1 (by rfl) ⟨20533649, by rfl⟩ : syracuseStep 27378199 = 41067299) B41067299
theorem B3949195 : Blo 1559477 3949195 := bstep (se 1 (by rfl) ⟨2961896, by rfl⟩ : syracuseStep 3949195 = 5923793) B5923793
theorem B5923475 : Blo 1559477 5923475 := bstep (se 1 (by rfl) ⟨4442606, by rfl⟩ : syracuseStep 5923475 = 8885213) B8885213
theorem B4809415 : Blo 1559477 4809415 := bstep (se 1 (by rfl) ⟨3607061, by rfl⟩ : syracuseStep 4809415 = 7214123) B7214123
theorem B2499511 : Blo 1559477 2499511 := bstep (se 1 (by rfl) ⟨1874633, by rfl⟩ : syracuseStep 2499511 = 3749267) B3749267
theorem B3949499 : Blo 1559477 3949499 := bstep (se 1 (by rfl) ⟨2962124, by rfl⟩ : syracuseStep 3949499 = 5924249) B5924249
theorem B10003475 : Blo 1559477 10003475 := bstep (se 1 (by rfl) ⟨7502606, by rfl⟩ : syracuseStep 10003475 = 15005213) B15005213
theorem B15205427 : Blo 1559477 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B11846735 : Blo 1559477 11846735 := bstep (se 1 (by rfl) ⟨8885051, by rfl⟩ : syracuseStep 11846735 = 17770103) B17770103
theorem B28476535 : Blo 1559477 28476535 := bstep (se 1 (by rfl) ⟨21357401, by rfl⟩ : syracuseStep 28476535 = 42714803) B42714803
theorem B8430745 : Blo 1559477 8430745 := bstep (se 2 (by rfl) ⟨3161529, by rfl⟩ : syracuseStep 8430745 = 6323059) B6323059
theorem B1779163 : Blo 1559477 1779163 := bstep (se 1 (by rfl) ⟨1334372, by rfl⟩ : syracuseStep 1779163 = 2668745) B2668745
theorem B11855483 : Blo 1559477 11855483 := bstep (se 1 (by rfl) ⟨8891612, by rfl⟩ : syracuseStep 11855483 = 17783225) B17783225
theorem B12658315 : Blo 1559477 12658315 := bstep (se 1 (by rfl) ⟨9493736, by rfl⟩ : syracuseStep 12658315 = 18987473) B18987473
theorem B3950279 : Blo 1559477 3950279 := bstep (se 1 (by rfl) ⟨2962709, by rfl⟩ : syracuseStep 3950279 = 5925419) B5925419
theorem B3950329 : Blo 1559477 3950329 := bstep (se 2 (by rfl) ⟨1481373, by rfl⟩ : syracuseStep 3950329 = 2962747) B2962747
theorem B6326045 : Blo 1559477 6326045 := bstep (se 3 (by rfl) ⟨1186133, by rfl⟩ : syracuseStep 6326045 = 2372267) B2372267
theorem B7497515 : Blo 1559477 7497515 := bstep (se 1 (by rfl) ⟨5623136, by rfl⟩ : syracuseStep 7497515 = 11246273) B11246273
theorem B6661997 : Blo 1559477 6661997 := bstep (se 3 (by rfl) ⟨1249124, by rfl⟩ : syracuseStep 6661997 = 2498249) B2498249
theorem B4999175 : Blo 1559477 4999175 := bstep (se 1 (by rfl) ⟨3749381, by rfl⟩ : syracuseStep 4999175 = 7498763) B7498763
theorem B1755175 : Blo 1559477 1755175 := bstep (se 1 (by rfl) ⟨1316381, by rfl⟩ : syracuseStep 1755175 = 2632763) B2632763
theorem B2631737 : Blo 1559477 2631737 := bstep (se 2 (by rfl) ⟨986901, by rfl⟩ : syracuseStep 2631737 = 1973803) B1973803
theorem B5269751 : Blo 1559477 5269751 := bstep (se 1 (by rfl) ⟨3952313, by rfl⟩ : syracuseStep 5269751 = 7904627) B7904627
theorem B10676567 : Blo 1559477 10676567 := bstep (se 1 (by rfl) ⟨8007425, by rfl⟩ : syracuseStep 10676567 = 16014851) B16014851
theorem B2812267 : Blo 1559477 2812267 := bstep (se 1 (by rfl) ⟨2109200, by rfl⟩ : syracuseStep 2812267 = 4218401) B4218401
theorem B11250049 : Blo 1559477 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B3950977 : Blo 1559477 3950977 := bstep (se 2 (by rfl) ⟨1481616, by rfl⟩ : syracuseStep 3950977 = 2963233) B2963233
theorem B4631027 : Blo 1559477 4631027 := bstep (se 1 (by rfl) ⟨3473270, by rfl⟩ : syracuseStep 4631027 = 6946541) B6946541
theorem B6662681 : Blo 1559477 6662681 := bstep (se 2 (by rfl) ⟨2498505, by rfl⟩ : syracuseStep 6662681 = 4997011) B4997011
theorem B5704225 : Blo 1559477 5704225 := bstep (se 2 (by rfl) ⟨2139084, by rfl⟩ : syracuseStep 5704225 = 4278169) B4278169
theorem B4442663 : Blo 1559477 4442663 := bstep (se 1 (by rfl) ⟨3331997, by rfl⟩ : syracuseStep 4442663 = 6663995) B6663995
theorem B1780423 : Blo 1559477 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B26659529 : Blo 1559477 26659529 := bstep (se 2 (by rfl) ⟨9997323, by rfl⟩ : syracuseStep 26659529 = 19994647) B19994647
theorem B3377875 : Blo 1559477 3377875 := bstep (se 1 (by rfl) ⟨2533406, by rfl⟩ : syracuseStep 3377875 = 5066813) B5066813
theorem B2632439 : Blo 1559477 2632439 := bstep (se 1 (by rfl) ⟨1974329, by rfl⟩ : syracuseStep 2632439 = 3948659) B3948659
theorem B3509099 : Blo 1559477 3509099 := bstep (se 1 (by rfl) ⟨2631824, by rfl⟩ : syracuseStep 3509099 = 5263649) B5263649
theorem B3509153 : Blo 1559477 3509153 := bstep (se 2 (by rfl) ⟨1315932, by rfl⟩ : syracuseStep 3509153 = 2631865) B2631865
theorem B5622689 : Blo 1559477 5622689 := bstep (se 2 (by rfl) ⟨2108508, by rfl⟩ : syracuseStep 5622689 = 4217017) B4217017
theorem B1559495 : Blo 1559477 1559495 := bstep (se 1 (by rfl) ⟨1169621, by rfl⟩ : syracuseStep 1559495 = 2339243) B2339243
theorem B81128405 : Blo 1559477 81128405 := bstep (se 7 (by rfl) ⟨950723, by rfl⟩ : syracuseStep 81128405 = 1901447) B1901447
theorem B1559515 : Blo 1559477 1559515 := bstep (se 1 (by rfl) ⟨1169636, by rfl⟩ : syracuseStep 1559515 = 2339273) B2339273
theorem B3001307 : Blo 1559477 3001307 := bstep (se 1 (by rfl) ⟨2250980, by rfl⟩ : syracuseStep 3001307 = 4501961) B4501961
theorem B1559591 : Blo 1559477 1559591 := bstep (se 1 (by rfl) ⟨1169693, by rfl⟩ : syracuseStep 1559591 = 2339387) B2339387
theorem B1559631 : Blo 1559477 1559631 := bstep (se 1 (by rfl) ⟨1169723, by rfl⟩ : syracuseStep 1559631 = 2339447) B2339447
theorem B2632783 : Blo 1559477 2632783 := bstep (se 1 (by rfl) ⟨1974587, by rfl⟩ : syracuseStep 2632783 = 3949175) B3949175
theorem B1666127 : Blo 1559477 1666127 := bstep (se 1 (by rfl) ⟨1249595, by rfl⟩ : syracuseStep 1666127 = 2499191) B2499191
theorem B1559647 : Blo 1559477 1559647 := bstep (se 1 (by rfl) ⟨1169735, by rfl⟩ : syracuseStep 1559647 = 2339471) B2339471
theorem B1559675 : Blo 1559477 1559675 := bstep (se 1 (by rfl) ⟨1169756, by rfl⟩ : syracuseStep 1559675 = 2339513) B2339513
theorem B7113881 : Blo 1559477 7113881 := bstep (se 2 (by rfl) ⟨2667705, by rfl⟩ : syracuseStep 7113881 = 5335411) B5335411
theorem B3951787 : Blo 1559477 3951787 := bstep (se 1 (by rfl) ⟨2963840, by rfl⟩ : syracuseStep 3951787 = 5927681) B5927681
theorem B1559727 : Blo 1559477 1559727 := bstep (se 1 (by rfl) ⟨1169795, by rfl⟩ : syracuseStep 1559727 = 2339591) B2339591
theorem B6008003 : Blo 1559477 6008003 := bstep (se 1 (by rfl) ⟨4506002, by rfl⟩ : syracuseStep 6008003 = 9012005) B9012005
theorem B1559751 : Blo 1559477 1559751 := bstep (se 1 (by rfl) ⟨1169813, by rfl⟩ : syracuseStep 1559751 = 2339627) B2339627
theorem B3001555 : Blo 1559477 3001555 := bstep (se 1 (by rfl) ⟨2251166, by rfl⟩ : syracuseStep 3001555 = 4502333) B4502333
theorem B1559771 : Blo 1559477 1559771 := bstep (se 1 (by rfl) ⟨1169828, by rfl⟩ : syracuseStep 1559771 = 2339657) B2339657
theorem B3509495 : Blo 1559477 3509495 := bstep (se 1 (by rfl) ⟨2632121, by rfl⟩ : syracuseStep 3509495 = 5264243) B5264243
theorem B18975991 : Blo 1559477 18975991 := bstep (se 1 (by rfl) ⟨14231993, by rfl⟩ : syracuseStep 18975991 = 28463987) B28463987
theorem B12004645 : Blo 1559477 12004645 := bstep (se 4 (by rfl) ⟨1125435, by rfl⟩ : syracuseStep 12004645 = 2250871) B2250871
theorem B1559847 : Blo 1559477 1559847 := bstep (se 1 (by rfl) ⟨1169885, by rfl⟩ : syracuseStep 1559847 = 2339771) B2339771
theorem B2633033 : Blo 1559477 2633033 := bstep (se 2 (by rfl) ⟨987387, by rfl⟩ : syracuseStep 2633033 = 1974775) B1974775
theorem B1559887 : Blo 1559477 1559887 := bstep (se 1 (by rfl) ⟨1169915, by rfl⟩ : syracuseStep 1559887 = 2339831) B2339831
theorem B1559903 : Blo 1559477 1559903 := bstep (se 1 (by rfl) ⟨1169927, by rfl⟩ : syracuseStep 1559903 = 2339855) B2339855
theorem B1559931 : Blo 1559477 1559931 := bstep (se 1 (by rfl) ⟨1169948, by rfl⟩ : syracuseStep 1559931 = 2339897) B2339897
theorem B1559983 : Blo 1559477 1559983 := bstep (se 1 (by rfl) ⟨1169987, by rfl⟩ : syracuseStep 1559983 = 2339975) B2339975
theorem B2108855 : Blo 1559477 2108855 := bstep (se 1 (by rfl) ⟨1581641, by rfl⟩ : syracuseStep 2108855 = 3163283) B3163283
theorem B1560007 : Blo 1559477 1560007 := bstep (se 1 (by rfl) ⟨1170005, by rfl⟩ : syracuseStep 1560007 = 2340011) B2340011
theorem B1560027 : Blo 1559477 1560027 := bstep (se 1 (by rfl) ⟨1170020, by rfl⟩ : syracuseStep 1560027 = 2340041) B2340041
theorem B3952091 : Blo 1559477 3952091 := bstep (se 1 (by rfl) ⟨2964068, by rfl⟩ : syracuseStep 3952091 = 5928137) B5928137
theorem B1560103 : Blo 1559477 1560103 := bstep (se 1 (by rfl) ⟨1170077, by rfl⟩ : syracuseStep 1560103 = 2340155) B2340155
theorem B1560143 : Blo 1559477 1560143 := bstep (se 1 (by rfl) ⟨1170107, by rfl⟩ : syracuseStep 1560143 = 2340215) B2340215
theorem B1560159 : Blo 1559477 1560159 := bstep (se 1 (by rfl) ⟨1170119, by rfl⟩ : syracuseStep 1560159 = 2340239) B2340239
theorem B27012727 : Blo 1559477 27012727 := bstep (se 1 (by rfl) ⟨20259545, by rfl⟩ : syracuseStep 27012727 = 40519091) B40519091
theorem B1560187 : Blo 1559477 1560187 := bstep (se 1 (by rfl) ⟨1170140, by rfl⟩ : syracuseStep 1560187 = 2340281) B2340281
theorem B1560239 : Blo 1559477 1560239 := bstep (se 1 (by rfl) ⟨1170179, by rfl⟩ : syracuseStep 1560239 = 2340359) B2340359
theorem B8433341 : Blo 1559477 8433341 := bstep (se 3 (by rfl) ⟨1581251, by rfl⟩ : syracuseStep 8433341 = 3162503) B3162503
theorem B1560263 : Blo 1559477 1560263 := bstep (se 1 (by rfl) ⟨1170197, by rfl⟩ : syracuseStep 1560263 = 2340395) B2340395
theorem B2961107 : Blo 1559477 2961107 := bstep (se 1 (by rfl) ⟨2220830, by rfl⟩ : syracuseStep 2961107 = 4441661) B4441661
theorem B1560283 : Blo 1559477 1560283 := bstep (se 1 (by rfl) ⟨1170212, by rfl⟩ : syracuseStep 1560283 = 2340425) B2340425
theorem B12660461 : Blo 1559477 12660461 := bstep (se 3 (by rfl) ⟨2373836, by rfl⟩ : syracuseStep 12660461 = 4747673) B4747673
theorem B2633465 : Blo 1559477 2633465 := bstep (se 2 (by rfl) ⟨987549, by rfl⟩ : syracuseStep 2633465 = 1975099) B1975099
theorem B26677025 : Blo 1559477 26677025 := bstep (se 2 (by rfl) ⟨10003884, by rfl⟩ : syracuseStep 26677025 = 20007769) B20007769
theorem B1560359 : Blo 1559477 1560359 := bstep (se 1 (by rfl) ⟨1170269, by rfl⟩ : syracuseStep 1560359 = 2340539) B2340539
theorem B3510089 : Blo 1559477 3510089 := bstep (se 2 (by rfl) ⟨1316283, by rfl⟩ : syracuseStep 3510089 = 2632567) B2632567
theorem B1560399 : Blo 1559477 1560399 := bstep (se 1 (by rfl) ⟨1170299, by rfl⟩ : syracuseStep 1560399 = 2340599) B2340599
theorem B1560415 : Blo 1559477 1560415 := bstep (se 1 (by rfl) ⟨1170311, by rfl⟩ : syracuseStep 1560415 = 2340623) B2340623
theorem B1560443 : Blo 1559477 1560443 := bstep (se 1 (by rfl) ⟨1170332, by rfl⟩ : syracuseStep 1560443 = 2340665) B2340665
theorem B5066657 : Blo 1559477 5066657 := bstep (se 2 (by rfl) ⟨1899996, by rfl⟩ : syracuseStep 5066657 = 3799993) B3799993
theorem B1560495 : Blo 1559477 1560495 := bstep (se 1 (by rfl) ⟨1170371, by rfl⟩ : syracuseStep 1560495 = 2340743) B2340743
theorem B2633647 : Blo 1559477 2633647 := bstep (se 1 (by rfl) ⟨1975235, by rfl⟩ : syracuseStep 2633647 = 3950471) B3950471
theorem B2961335 : Blo 1559477 2961335 := bstep (se 1 (by rfl) ⟨2221001, by rfl⟩ : syracuseStep 2961335 = 4442003) B4442003
theorem B1560519 : Blo 1559477 1560519 := bstep (se 1 (by rfl) ⟨1170389, by rfl⟩ : syracuseStep 1560519 = 2340779) B2340779
theorem B1560539 : Blo 1559477 1560539 := bstep (se 1 (by rfl) ⟨1170404, by rfl⟩ : syracuseStep 1560539 = 2340809) B2340809
theorem B2633735 : Blo 1559477 2633735 := bstep (se 1 (by rfl) ⟨1975301, by rfl⟩ : syracuseStep 2633735 = 3950603) B3950603
theorem B380063755 : Blo 1559477 380063755 := bstep (se 1 (by rfl) ⟨285047816, by rfl⟩ : syracuseStep 380063755 = 570095633) B570095633
theorem B5263379 : Blo 1559477 5263379 := bstep (se 1 (by rfl) ⟨3947534, by rfl⟩ : syracuseStep 5263379 = 7895069) B7895069
theorem B1560615 : Blo 1559477 1560615 := bstep (se 1 (by rfl) ⟨1170461, by rfl⟩ : syracuseStep 1560615 = 2340923) B2340923
theorem B1560655 : Blo 1559477 1560655 := bstep (se 1 (by rfl) ⟨1170491, by rfl⟩ : syracuseStep 1560655 = 2340983) B2340983
theorem B1560671 : Blo 1559477 1560671 := bstep (se 1 (by rfl) ⟨1170503, by rfl⟩ : syracuseStep 1560671 = 2341007) B2341007
theorem B1560699 : Blo 1559477 1560699 := bstep (se 1 (by rfl) ⟨1170524, by rfl⟩ : syracuseStep 1560699 = 2341049) B2341049
theorem B1560751 : Blo 1559477 1560751 := bstep (se 1 (by rfl) ⟨1170563, by rfl⟩ : syracuseStep 1560751 = 2341127) B2341127
theorem B1560775 : Blo 1559477 1560775 := bstep (se 1 (by rfl) ⟨1170581, by rfl⟩ : syracuseStep 1560775 = 2341163) B2341163
theorem B1560795 : Blo 1559477 1560795 := bstep (se 1 (by rfl) ⟨1170596, by rfl⟩ : syracuseStep 1560795 = 2341193) B2341193
theorem B21344485 : Blo 1559477 21344485 := bstep (se 4 (by rfl) ⟨2001045, by rfl⟩ : syracuseStep 21344485 = 4002091) B4002091
theorem B1560871 : Blo 1559477 1560871 := bstep (se 1 (by rfl) ⟨1170653, by rfl⟩ : syracuseStep 1560871 = 2341307) B2341307
theorem B1560911 : Blo 1559477 1560911 := bstep (se 1 (by rfl) ⟨1170683, by rfl⟩ : syracuseStep 1560911 = 2341367) B2341367
theorem B5263703 : Blo 1559477 5263703 := bstep (se 1 (by rfl) ⟨3947777, by rfl⟩ : syracuseStep 5263703 = 7895555) B7895555
theorem B1560927 : Blo 1559477 1560927 := bstep (se 1 (by rfl) ⟨1170695, by rfl⟩ : syracuseStep 1560927 = 2341391) B2341391
theorem B2634079 : Blo 1559477 2634079 := bstep (se 1 (by rfl) ⟨1975559, by rfl⟩ : syracuseStep 2634079 = 3951119) B3951119
theorem B1560955 : Blo 1559477 1560955 := bstep (se 1 (by rfl) ⟨1170716, by rfl⟩ : syracuseStep 1560955 = 2341433) B2341433
theorem B11850137 : Blo 1559477 11850137 := bstep (se 2 (by rfl) ⟨4443801, by rfl⟩ : syracuseStep 11850137 = 8887603) B8887603
theorem B1561007 : Blo 1559477 1561007 := bstep (se 1 (by rfl) ⟨1170755, by rfl⟩ : syracuseStep 1561007 = 2341511) B2341511
theorem B2339255 : Blo 1559477 2339255 := bstep (se 1 (by rfl) ⟨1754441, by rfl⟩ : syracuseStep 2339255 = 3508883) B3508883
theorem B2634167 : Blo 1559477 2634167 := bstep (se 1 (by rfl) ⟨1975625, by rfl⟩ : syracuseStep 2634167 = 3951251) B3951251
theorem B1561031 : Blo 1559477 1561031 := bstep (se 1 (by rfl) ⟨1170773, by rfl⟩ : syracuseStep 1561031 = 2341547) B2341547
theorem B2339291 : Blo 1559477 2339291 := bstep (se 1 (by rfl) ⟨1754468, by rfl⟩ : syracuseStep 2339291 = 3508937) B3508937
theorem B1561051 : Blo 1559477 1561051 := bstep (se 1 (by rfl) ⟨1170788, by rfl⟩ : syracuseStep 1561051 = 2341577) B2341577
theorem B1561127 : Blo 1559477 1561127 := bstep (se 1 (by rfl) ⟨1170845, by rfl⟩ : syracuseStep 1561127 = 2341691) B2341691
theorem B1561167 : Blo 1559477 1561167 := bstep (se 1 (by rfl) ⟨1170875, by rfl⟩ : syracuseStep 1561167 = 2341751) B2341751
theorem B1561183 : Blo 1559477 1561183 := bstep (se 1 (by rfl) ⟨1170887, by rfl⟩ : syracuseStep 1561183 = 2341775) B2341775
theorem B3510881 : Blo 1559477 3510881 := bstep (se 2 (by rfl) ⟨1316580, by rfl⟩ : syracuseStep 3510881 = 2633161) B2633161
theorem B1561211 : Blo 1559477 1561211 := bstep (se 1 (by rfl) ⟨1170908, by rfl⟩ : syracuseStep 1561211 = 2341817) B2341817
theorem B1561263 : Blo 1559477 1561263 := bstep (se 1 (by rfl) ⟨1170947, by rfl⟩ : syracuseStep 1561263 = 2341895) B2341895
theorem B12661433 : Blo 1559477 12661433 := bstep (se 2 (by rfl) ⟨4748037, by rfl⟩ : syracuseStep 12661433 = 9496075) B9496075
theorem B1561287 : Blo 1559477 1561287 := bstep (se 1 (by rfl) ⟨1170965, by rfl⟩ : syracuseStep 1561287 = 2341931) B2341931
theorem B1561307 : Blo 1559477 1561307 := bstep (se 1 (by rfl) ⟨1170980, by rfl⟩ : syracuseStep 1561307 = 2341961) B2341961
theorem B4215545 : Blo 1559477 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B1561383 : Blo 1559477 1561383 := bstep (se 1 (by rfl) ⟨1171037, by rfl⟩ : syracuseStep 1561383 = 2342075) B2342075
theorem B230970163 : Blo 1559477 230970163 := bstep (se 1 (by rfl) ⟨173227622, by rfl⟩ : syracuseStep 230970163 = 346455245) B346455245
theorem B1561423 : Blo 1559477 1561423 := bstep (se 1 (by rfl) ⟨1171067, by rfl⟩ : syracuseStep 1561423 = 2342135) B2342135
theorem B1561439 : Blo 1559477 1561439 := bstep (se 1 (by rfl) ⟨1171079, by rfl⟩ : syracuseStep 1561439 = 2342159) B2342159
theorem B1561467 : Blo 1559477 1561467 := bstep (se 1 (by rfl) ⟨1171100, by rfl⟩ : syracuseStep 1561467 = 2342201) B2342201
theorem B2339759 : Blo 1559477 2339759 := bstep (se 1 (by rfl) ⟨1754819, by rfl⟩ : syracuseStep 2339759 = 3509639) B3509639
theorem B3511223 : Blo 1559477 3511223 := bstep (se 1 (by rfl) ⟨2633417, by rfl⟩ : syracuseStep 3511223 = 5266835) B5266835
theorem B5927863 : Blo 1559477 5927863 := bstep (se 1 (by rfl) ⟨4445897, by rfl⟩ : syracuseStep 5927863 = 8891795) B8891795
theorem B7115777 : Blo 1559477 7115777 := bstep (se 2 (by rfl) ⟨2668416, by rfl⟩ : syracuseStep 7115777 = 5336833) B5336833
theorem B2339849 : Blo 1559477 2339849 := bstep (se 2 (by rfl) ⟨877443, by rfl⟩ : syracuseStep 2339849 = 1754887) B1754887
theorem B2634761 : Blo 1559477 2634761 := bstep (se 2 (by rfl) ⟨988035, by rfl⟩ : syracuseStep 2634761 = 1976071) B1976071
theorem B2339879 : Blo 1559477 2339879 := bstep (se 1 (by rfl) ⟨1754909, by rfl⟩ : syracuseStep 2339879 = 3509819) B3509819
theorem B12653617 : Blo 1559477 12653617 := bstep (se 2 (by rfl) ⟨4745106, by rfl⟩ : syracuseStep 12653617 = 9490213) B9490213
theorem B4502585 : Blo 1559477 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B2962489 : Blo 1559477 2962489 := bstep (se 2 (by rfl) ⟨1110933, by rfl⟩ : syracuseStep 2962489 = 2221867) B2221867
theorem B23123009 : Blo 1559477 23123009 := bstep (se 2 (by rfl) ⟨8671128, by rfl⟩ : syracuseStep 23123009 = 17342257) B17342257
theorem B10679363 : Blo 1559477 10679363 := bstep (se 1 (by rfl) ⟨8009522, by rfl⟩ : syracuseStep 10679363 = 16019045) B16019045
theorem B2339963 : Blo 1559477 2339963 := bstep (se 1 (by rfl) ⟨1754972, by rfl⟩ : syracuseStep 2339963 = 3509945) B3509945
theorem B51328171 : Blo 1559477 51328171 := bstep (se 1 (by rfl) ⟨38496128, by rfl⟩ : syracuseStep 51328171 = 76992257) B76992257
theorem B2634923 : Blo 1559477 2634923 := bstep (se 1 (by rfl) ⟨1976192, by rfl⟩ : syracuseStep 2634923 = 3952385) B3952385
theorem B2340089 : Blo 1559477 2340089 := bstep (se 2 (by rfl) ⟨877533, by rfl⟩ : syracuseStep 2340089 = 1755067) B1755067
theorem B2340191 : Blo 1559477 2340191 := bstep (se 1 (by rfl) ⟨1755143, by rfl⟩ : syracuseStep 2340191 = 3510287) B3510287
theorem B2962793 : Blo 1559477 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B2340203 : Blo 1559477 2340203 := bstep (se 1 (by rfl) ⟨1755152, by rfl⟩ : syracuseStep 2340203 = 3510305) B3510305
theorem B5264783 : Blo 1559477 5264783 := bstep (se 1 (by rfl) ⟨3948587, by rfl⟩ : syracuseStep 5264783 = 7897175) B7897175
theorem B2962831 : Blo 1559477 2962831 := bstep (se 1 (by rfl) ⟨2222123, by rfl⟩ : syracuseStep 2962831 = 4444247) B4444247
theorem B5928335 : Blo 1559477 5928335 := bstep (se 1 (by rfl) ⟨4446251, by rfl⟩ : syracuseStep 5928335 = 8892503) B8892503
theorem B42710419 : Blo 1559477 42710419 := bstep (se 1 (by rfl) ⟨32032814, by rfl⟩ : syracuseStep 42710419 = 64065629) B64065629
theorem B2569655 : Blo 1559477 2569655 := bstep (se 1 (by rfl) ⟨1927241, by rfl⟩ : syracuseStep 2569655 = 3854483) B3854483
theorem B7902683 : Blo 1559477 7902683 := bstep (se 1 (by rfl) ⟨5927012, by rfl⟩ : syracuseStep 7902683 = 11854025) B11854025
theorem B3511817 : Blo 1559477 3511817 := bstep (se 2 (by rfl) ⟨1316931, by rfl⟩ : syracuseStep 3511817 = 2633863) B2633863
theorem B4445705 : Blo 1559477 4445705 := bstep (se 2 (by rfl) ⟨1667139, by rfl⟩ : syracuseStep 4445705 = 3334279) B3334279
theorem B2340431 : Blo 1559477 2340431 := bstep (se 1 (by rfl) ⟨1755323, by rfl⟩ : syracuseStep 2340431 = 3510647) B3510647
theorem B4216519 : Blo 1559477 4216519 := bstep (se 1 (by rfl) ⟨3162389, by rfl⟩ : syracuseStep 4216519 = 6324779) B6324779
theorem B2340551 : Blo 1559477 2340551 := bstep (se 1 (by rfl) ⟨1755413, by rfl⟩ : syracuseStep 2340551 = 3510827) B3510827
theorem B5265107 : Blo 1559477 5265107 := bstep (se 1 (by rfl) ⟨3948830, by rfl⟩ : syracuseStep 5265107 = 7897661) B7897661
theorem B3512159 : Blo 1559477 3512159 := bstep (se 1 (by rfl) ⟨2634119, by rfl⟩ : syracuseStep 3512159 = 5268239) B5268239
theorem B2340713 : Blo 1559477 2340713 := bstep (se 2 (by rfl) ⟨877767, by rfl⟩ : syracuseStep 2340713 = 1755535) B1755535
theorem B13334381 : Blo 1559477 13334381 := bstep (se 3 (by rfl) ⟨2500196, by rfl⟩ : syracuseStep 13334381 = 5000393) B5000393
theorem B2340791 : Blo 1559477 2340791 := bstep (se 1 (by rfl) ⟨1755593, by rfl⟩ : syracuseStep 2340791 = 3511187) B3511187
theorem B22501313 : Blo 1559477 22501313 := bstep (se 2 (by rfl) ⟨8437992, by rfl⟩ : syracuseStep 22501313 = 16875985) B16875985
theorem B7903169 : Blo 1559477 7903169 := bstep (se 2 (by rfl) ⟨2963688, by rfl⟩ : syracuseStep 7903169 = 5927377) B5927377
theorem B2340827 : Blo 1559477 2340827 := bstep (se 1 (by rfl) ⟨1755620, by rfl⟩ : syracuseStep 2340827 = 3511241) B3511241
theorem B6002707 : Blo 1559477 6002707 := bstep (se 1 (by rfl) ⟨4502030, by rfl⟩ : syracuseStep 6002707 = 9004061) B9004061
theorem B3512339 : Blo 1559477 3512339 := bstep (se 1 (by rfl) ⟨2634254, by rfl⟩ : syracuseStep 3512339 = 5268509) B5268509
theorem B11852081 : Blo 1559477 11852081 := bstep (se 2 (by rfl) ⟨4444530, by rfl⟩ : syracuseStep 11852081 = 8889061) B8889061
theorem B3512681 : Blo 1559477 3512681 := bstep (se 2 (by rfl) ⟨1317255, by rfl⟩ : syracuseStep 3512681 = 2634511) B2634511
theorem B19995011 : Blo 1559477 19995011 := bstep (se 1 (by rfl) ⟨14996258, by rfl⟩ : syracuseStep 19995011 = 29992517) B29992517
theorem B2341295 : Blo 1559477 2341295 := bstep (se 1 (by rfl) ⟨1755971, by rfl⟩ : syracuseStep 2341295 = 3511943) B3511943
theorem B2341385 : Blo 1559477 2341385 := bstep (se 2 (by rfl) ⟨878019, by rfl⟩ : syracuseStep 2341385 = 1756039) B1756039
theorem B2341415 : Blo 1559477 2341415 := bstep (se 1 (by rfl) ⟨1756061, by rfl⟩ : syracuseStep 2341415 = 3512123) B3512123
theorem B2341499 : Blo 1559477 2341499 := bstep (se 1 (by rfl) ⟨1756124, by rfl⟩ : syracuseStep 2341499 = 3512249) B3512249
theorem B10001069 : Blo 1559477 10001069 := bstep (se 3 (by rfl) ⟨1875200, by rfl⟩ : syracuseStep 10001069 = 3750401) B3750401
theorem B11844305 : Blo 1559477 11844305 := bstep (se 2 (by rfl) ⟨4441614, by rfl⟩ : syracuseStep 11844305 = 8883229) B8883229
theorem B2341625 : Blo 1559477 2341625 := bstep (se 2 (by rfl) ⟨878109, by rfl⟩ : syracuseStep 2341625 = 1756219) B1756219
theorem B2341727 : Blo 1559477 2341727 := bstep (se 1 (by rfl) ⟨1756295, by rfl⟩ : syracuseStep 2341727 = 3512591) B3512591
theorem B2341739 : Blo 1559477 2341739 := bstep (se 1 (by rfl) ⟨1756304, by rfl⟩ : syracuseStep 2341739 = 3512609) B3512609
theorem B5266295 : Blo 1559477 5266295 := bstep (se 1 (by rfl) ⟨3949721, by rfl⟩ : syracuseStep 5266295 = 7899443) B7899443
theorem B3513275 : Blo 1559477 3513275 := bstep (se 1 (by rfl) ⟨2634956, by rfl⟩ : syracuseStep 3513275 = 5269913) B5269913
theorem B5921849 : Blo 1559477 5921849 := bstep (se 2 (by rfl) ⟨2220693, by rfl⟩ : syracuseStep 5921849 = 4441387) B4441387
theorem B5266511 : Blo 1559477 5266511 := bstep (se 1 (by rfl) ⟨3949883, by rfl⟩ : syracuseStep 5266511 = 7899767) B7899767
theorem B6667343 : Blo 1559477 6667343 := bstep (se 1 (by rfl) ⟨5000507, by rfl⟩ : syracuseStep 6667343 = 10001015) B10001015
theorem B2341967 : Blo 1559477 2341967 := bstep (se 1 (by rfl) ⟨1756475, by rfl⟩ : syracuseStep 2341967 = 3512951) B3512951
theorem B2342087 : Blo 1559477 2342087 := bstep (se 1 (by rfl) ⟨1756565, by rfl⟩ : syracuseStep 2342087 = 3513131) B3513131
theorem B40008977 : Blo 1559477 40008977 := bstep (se 2 (by rfl) ⟨15003366, by rfl⟩ : syracuseStep 40008977 = 30006733) B30006733
theorem B25320721 : Blo 1559477 25320721 := bstep (se 2 (by rfl) ⟨9495270, by rfl⟩ : syracuseStep 25320721 = 18990541) B18990541
theorem B7495055 : Blo 1559477 7495055 := bstep (se 1 (by rfl) ⟨5621291, by rfl⟩ : syracuseStep 7495055 = 11242583) B11242583
theorem B5266889 : Blo 1559477 5266889 := bstep (se 2 (by rfl) ⟨1975083, by rfl⟩ : syracuseStep 5266889 = 3950167) B3950167
theorem B3948041 : Blo 1559477 3948041 := bstep (se 2 (by rfl) ⟨1480515, by rfl⟩ : syracuseStep 3948041 = 2961031) B2961031
theorem B5922503 : Blo 1559477 5922503 := bstep (se 1 (by rfl) ⟨4441877, by rfl⟩ : syracuseStep 5922503 = 8883755) B8883755
theorem B5267159 : Blo 1559477 5267159 := bstep (se 1 (by rfl) ⟨3950369, by rfl⟩ : syracuseStep 5267159 = 7900739) B7900739
theorem B4218617 : Blo 1559477 4218617 := bstep (se 2 (by rfl) ⟨1581981, by rfl⟩ : syracuseStep 4218617 = 3163963) B3163963
theorem B9994043 : Blo 1559477 9994043 := bstep (se 1 (by rfl) ⟨7495532, by rfl⟩ : syracuseStep 9994043 = 14991065) B14991065
theorem B5267375 : Blo 1559477 5267375 := bstep (se 1 (by rfl) ⟨3950531, by rfl⟩ : syracuseStep 5267375 = 7901063) B7901063
theorem B8003609 : Blo 1559477 8003609 := bstep (se 2 (by rfl) ⟨3001353, by rfl⟩ : syracuseStep 8003609 = 6002707) B6002707
theorem B61661357 : Blo 1559477 61661357 := bstep (se 3 (by rfl) ⟨11561504, by rfl⟩ : syracuseStep 61661357 = 23123009) B23123009
theorem B28459313 : Blo 1559477 28459313 := bstep (se 2 (by rfl) ⟨10672242, by rfl⟩ : syracuseStep 28459313 = 21344485) B21344485
theorem B3948983 : Blo 1559477 3948983 := bstep (se 1 (by rfl) ⟨2961737, by rfl⟩ : syracuseStep 3948983 = 5923475) B5923475
theorem B15000065 : Blo 1559477 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B5267969 : Blo 1559477 5267969 := bstep (se 2 (by rfl) ⟨1975488, by rfl⟩ : syracuseStep 5267969 = 3950977) B3950977
theorem B4743851 : Blo 1559477 4743851 := bstep (se 1 (by rfl) ⟨3557888, by rfl⟩ : syracuseStep 4743851 = 7115777) B7115777
theorem B6668983 : Blo 1559477 6668983 := bstep (se 1 (by rfl) ⟨5001737, by rfl⟩ : syracuseStep 6668983 = 10003475) B10003475
theorem B36504265 : Blo 1559477 36504265 := bstep (se 2 (by rfl) ⟨13689099, by rfl⟩ : syracuseStep 36504265 = 27378199) B27378199
theorem B7119575 : Blo 1559477 7119575 := bstep (se 1 (by rfl) ⟨5339681, by rfl⟩ : syracuseStep 7119575 = 10679363) B10679363
theorem B7897823 : Blo 1559477 7897823 := bstep (se 1 (by rfl) ⟨5923367, by rfl⟩ : syracuseStep 7897823 = 11846735) B11846735
theorem B1975195 : Blo 1559477 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B5268455 : Blo 1559477 5268455 := bstep (se 1 (by rfl) ⟨3951341, by rfl⟩ : syracuseStep 5268455 = 7902683) B7902683
theorem B22488101 : Blo 1559477 22488101 := bstep (se 4 (by rfl) ⟨2108259, by rfl⟩ : syracuseStep 22488101 = 4216519) B4216519
theorem B9495589 : Blo 1559477 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B16008293 : Blo 1559477 16008293 := bstep (se 4 (by rfl) ⟨1500777, by rfl⟩ : syracuseStep 16008293 = 3001555) B3001555
theorem B4998343 : Blo 1559477 4998343 := bstep (se 1 (by rfl) ⟨3748757, by rfl⟩ : syracuseStep 4998343 = 7497515) B7497515
theorem B4441331 : Blo 1559477 4441331 := bstep (se 1 (by rfl) ⟨3330998, by rfl⟩ : syracuseStep 4441331 = 6661997) B6661997
theorem B8889587 : Blo 1559477 8889587 := bstep (se 1 (by rfl) ⟨6667190, by rfl⟩ : syracuseStep 8889587 = 13334381) B13334381
theorem B15000875 : Blo 1559477 15000875 := bstep (se 1 (by rfl) ⟨11250656, by rfl⟩ : syracuseStep 15000875 = 22501313) B22501313
theorem B5268779 : Blo 1559477 5268779 := bstep (se 1 (by rfl) ⟨3951584, by rfl⟩ : syracuseStep 5268779 = 7903169) B7903169
theorem B1754491 : Blo 1559477 1754491 := bstep (se 1 (by rfl) ⟨1315868, by rfl⟩ : syracuseStep 1754491 = 2631737) B2631737
theorem B3949985 : Blo 1559477 3949985 := bstep (se 2 (by rfl) ⟨1481244, by rfl⟩ : syracuseStep 3949985 = 2962489) B2962489
theorem B11240993 : Blo 1559477 11240993 := bstep (se 2 (by rfl) ⟨4215372, by rfl⟩ : syracuseStep 11240993 = 8430745) B8430745
theorem B68437561 : Blo 1559477 68437561 := bstep (se 2 (by rfl) ⟨25664085, by rfl⟩ : syracuseStep 68437561 = 51328171) B51328171
theorem B5269049 : Blo 1559477 5269049 := bstep (se 2 (by rfl) ⟨1975893, by rfl⟩ : syracuseStep 5269049 = 3951787) B3951787
theorem B13330007 : Blo 1559477 13330007 := bstep (se 1 (by rfl) ⟨9997505, by rfl⟩ : syracuseStep 13330007 = 19995011) B19995011
theorem B4441787 : Blo 1559477 4441787 := bstep (se 1 (by rfl) ⟨3331340, by rfl⟩ : syracuseStep 4441787 = 6662681) B6662681
theorem B33760961 : Blo 1559477 33760961 := bstep (se 2 (by rfl) ⟨12660360, by rfl⟩ : syracuseStep 33760961 = 25320721) B25320721
theorem B1754959 : Blo 1559477 1754959 := bstep (se 1 (by rfl) ⟨1316219, by rfl⟩ : syracuseStep 1754959 = 2632439) B2632439
theorem B3950441 : Blo 1559477 3950441 := bstep (se 2 (by rfl) ⟨1481415, by rfl⟩ : syracuseStep 3950441 = 2962831) B2962831
theorem B54085603 : Blo 1559477 54085603 := bstep (se 1 (by rfl) ⟨40564202, by rfl⟩ : syracuseStep 54085603 = 81128405) B81128405
theorem B26650781 : Blo 1559477 26650781 := bstep (se 3 (by rfl) ⟨4997021, by rfl⟩ : syracuseStep 26650781 = 9994043) B9994043
theorem B16877753 : Blo 1559477 16877753 := bstep (se 2 (by rfl) ⟨6329157, by rfl⟩ : syracuseStep 16877753 = 12658315) B12658315
theorem B1755355 : Blo 1559477 1755355 := bstep (se 1 (by rfl) ⟨1316516, by rfl⟩ : syracuseStep 1755355 = 2633033) B2633033
theorem B2632027 : Blo 1559477 2632027 := bstep (se 1 (by rfl) ⟨1974020, by rfl⟩ : syracuseStep 2632027 = 3948041) B3948041
theorem B5622227 : Blo 1559477 5622227 := bstep (se 1 (by rfl) ⟨4216670, by rfl⟩ : syracuseStep 5622227 = 8433341) B8433341
theorem B9488869 : Blo 1559477 9488869 := bstep (se 4 (by rfl) ⟨889581, by rfl⟩ : syracuseStep 9488869 = 1779163) B1779163
theorem B8440307 : Blo 1559477 8440307 := bstep (se 1 (by rfl) ⟨6330230, by rfl⟩ : syracuseStep 8440307 = 12660461) B12660461
theorem B1755643 : Blo 1559477 1755643 := bstep (se 1 (by rfl) ⟨1316732, by rfl⟩ : syracuseStep 1755643 = 2633465) B2633465
theorem B2812411 : Blo 1559477 2812411 := bstep (se 1 (by rfl) ⟨2109308, by rfl⟩ : syracuseStep 2812411 = 4218617) B4218617
theorem B3377771 : Blo 1559477 3377771 := bstep (se 1 (by rfl) ⟨2533328, by rfl⟩ : syracuseStep 3377771 = 5066657) B5066657
theorem B1755823 : Blo 1559477 1755823 := bstep (se 1 (by rfl) ⟨1316867, by rfl⟩ : syracuseStep 1755823 = 2633735) B2633735
theorem B3508919 : Blo 1559477 3508919 := bstep (se 1 (by rfl) ⟨2631689, by rfl⟩ : syracuseStep 3508919 = 5263379) B5263379
theorem B506751673 : Blo 1559477 506751673 := bstep (se 2 (by rfl) ⟨190031877, by rfl⟩ : syracuseStep 506751673 = 380063755) B380063755
theorem B4443005 : Blo 1559477 4443005 := bstep (se 3 (by rfl) ⟨833063, by rfl⟩ : syracuseStep 4443005 = 1666127) B1666127
theorem B3509135 : Blo 1559477 3509135 := bstep (se 1 (by rfl) ⟨2631851, by rfl⟩ : syracuseStep 3509135 = 5263703) B5263703
theorem B7900091 : Blo 1559477 7900091 := bstep (se 1 (by rfl) ⟨5925068, by rfl⟩ : syracuseStep 7900091 = 11850137) B11850137
theorem B1559503 : Blo 1559477 1559503 := bstep (se 1 (by rfl) ⟨1169627, by rfl⟩ : syracuseStep 1559503 = 2339255) B2339255
theorem B1756111 : Blo 1559477 1756111 := bstep (se 1 (by rfl) ⟨1317083, by rfl⟩ : syracuseStep 1756111 = 2634167) B2634167
theorem B1559527 : Blo 1559477 1559527 := bstep (se 1 (by rfl) ⟨1169645, by rfl⟩ : syracuseStep 1559527 = 2339291) B2339291
theorem B8440955 : Blo 1559477 8440955 := bstep (se 1 (by rfl) ⟨6330716, by rfl⟩ : syracuseStep 8440955 = 12661433) B12661433
theorem B1559839 : Blo 1559477 1559839 := bstep (se 1 (by rfl) ⟨1169879, by rfl⟩ : syracuseStep 1559839 = 2339759) B2339759
theorem B2632999 : Blo 1559477 2632999 := bstep (se 1 (by rfl) ⟨1974749, by rfl⟩ : syracuseStep 2632999 = 3949499) B3949499
theorem B1559899 : Blo 1559477 1559899 := bstep (se 1 (by rfl) ⟨1169924, by rfl⟩ : syracuseStep 1559899 = 2339849) B2339849
theorem B1756507 : Blo 1559477 1756507 := bstep (se 1 (by rfl) ⟨1317380, by rfl⟩ : syracuseStep 1756507 = 2634761) B2634761
theorem B1559919 : Blo 1559477 1559919 := bstep (se 1 (by rfl) ⟨1169939, by rfl⟩ : syracuseStep 1559919 = 2339879) B2339879
theorem B10136951 : Blo 1559477 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B1559975 : Blo 1559477 1559975 := bstep (se 1 (by rfl) ⟨1169981, by rfl⟩ : syracuseStep 1559975 = 2339963) B2339963
theorem B1756615 : Blo 1559477 1756615 := bstep (se 1 (by rfl) ⟨1317461, by rfl⟩ : syracuseStep 1756615 = 2634923) B2634923
theorem B1560059 : Blo 1559477 1560059 := bstep (se 1 (by rfl) ⟨1170044, by rfl⟩ : syracuseStep 1560059 = 2340089) B2340089
theorem B28470845 : Blo 1559477 28470845 := bstep (se 3 (by rfl) ⟨5338283, by rfl⟩ : syracuseStep 28470845 = 10676567) B10676567
theorem B1560127 : Blo 1559477 1560127 := bstep (se 1 (by rfl) ⟨1170095, by rfl⟩ : syracuseStep 1560127 = 2340191) B2340191
theorem B1560135 : Blo 1559477 1560135 := bstep (se 1 (by rfl) ⟨1170101, by rfl⟩ : syracuseStep 1560135 = 2340203) B2340203
theorem B3509855 : Blo 1559477 3509855 := bstep (se 1 (by rfl) ⟨2632391, by rfl⟩ : syracuseStep 3509855 = 5264783) B5264783
theorem B3952223 : Blo 1559477 3952223 := bstep (se 1 (by rfl) ⟨2964167, by rfl⟩ : syracuseStep 3952223 = 5928335) B5928335
theorem B1560287 : Blo 1559477 1560287 := bstep (se 1 (by rfl) ⟨1170215, by rfl⟩ : syracuseStep 1560287 = 2340431) B2340431
theorem B1560367 : Blo 1559477 1560367 := bstep (se 1 (by rfl) ⟨1170275, by rfl⟩ : syracuseStep 1560367 = 2340551) B2340551
theorem B2633519 : Blo 1559477 2633519 := bstep (se 1 (by rfl) ⟨1975139, by rfl⟩ : syracuseStep 2633519 = 3950279) B3950279
theorem B3510071 : Blo 1559477 3510071 := bstep (se 1 (by rfl) ⟨2632553, by rfl⟩ : syracuseStep 3510071 = 5265107) B5265107
theorem B5623613 : Blo 1559477 5623613 := bstep (se 3 (by rfl) ⟨1054427, by rfl⟩ : syracuseStep 5623613 = 2108855) B2108855
theorem B6852413 : Blo 1559477 6852413 := bstep (se 3 (by rfl) ⟨1284827, by rfl⟩ : syracuseStep 6852413 = 2569655) B2569655
theorem B1560475 : Blo 1559477 1560475 := bstep (se 1 (by rfl) ⟨1170356, by rfl⟩ : syracuseStep 1560475 = 2340713) B2340713
theorem B1560527 : Blo 1559477 1560527 := bstep (se 1 (by rfl) ⟨1170395, by rfl⟩ : syracuseStep 1560527 = 2340791) B2340791
theorem B1560551 : Blo 1559477 1560551 := bstep (se 1 (by rfl) ⟨1170413, by rfl⟩ : syracuseStep 1560551 = 2340827) B2340827
theorem B16871489 : Blo 1559477 16871489 := bstep (se 2 (by rfl) ⟨6326808, by rfl⟩ : syracuseStep 16871489 = 12653617) B12653617
theorem B3510377 : Blo 1559477 3510377 := bstep (se 2 (by rfl) ⟨1316391, by rfl⟩ : syracuseStep 3510377 = 2632783) B2632783
theorem B7901387 : Blo 1559477 7901387 := bstep (se 1 (by rfl) ⟨5926040, by rfl⟩ : syracuseStep 7901387 = 11852081) B11852081
theorem B1560863 : Blo 1559477 1560863 := bstep (se 1 (by rfl) ⟨1170647, by rfl⟩ : syracuseStep 1560863 = 2341295) B2341295
theorem B25301321 : Blo 1559477 25301321 := bstep (se 2 (by rfl) ⟨9487995, by rfl⟩ : syracuseStep 25301321 = 18975991) B18975991
theorem B1560923 : Blo 1559477 1560923 := bstep (se 1 (by rfl) ⟨1170692, by rfl⟩ : syracuseStep 1560923 = 2341385) B2341385
theorem B2961775 : Blo 1559477 2961775 := bstep (se 1 (by rfl) ⟨2221331, by rfl⟩ : syracuseStep 2961775 = 4442663) B4442663
theorem B1560943 : Blo 1559477 1560943 := bstep (se 1 (by rfl) ⟨1170707, by rfl⟩ : syracuseStep 1560943 = 2341415) B2341415
theorem B1560999 : Blo 1559477 1560999 := bstep (se 1 (by rfl) ⟨1170749, by rfl⟩ : syracuseStep 1560999 = 2341499) B2341499
theorem B17773019 : Blo 1559477 17773019 := bstep (se 1 (by rfl) ⟨13329764, by rfl⟩ : syracuseStep 17773019 = 26659529) B26659529
theorem B1561083 : Blo 1559477 1561083 := bstep (se 1 (by rfl) ⟨1170812, by rfl⟩ : syracuseStep 1561083 = 2341625) B2341625
theorem B56947225 : Blo 1559477 56947225 := bstep (se 2 (by rfl) ⟨21355209, by rfl⟩ : syracuseStep 56947225 = 42710419) B42710419
theorem B1561151 : Blo 1559477 1561151 := bstep (se 1 (by rfl) ⟨1170863, by rfl⟩ : syracuseStep 1561151 = 2341727) B2341727
theorem B2339399 : Blo 1559477 2339399 := bstep (se 1 (by rfl) ⟨1754549, by rfl⟩ : syracuseStep 2339399 = 3509099) B3509099
theorem B1561159 : Blo 1559477 1561159 := bstep (se 1 (by rfl) ⟨1170869, by rfl⟩ : syracuseStep 1561159 = 2341739) B2341739
theorem B3510863 : Blo 1559477 3510863 := bstep (se 1 (by rfl) ⟨2633147, by rfl⟩ : syracuseStep 3510863 = 5266295) B5266295
theorem B2339435 : Blo 1559477 2339435 := bstep (se 1 (by rfl) ⟨1754576, by rfl⟩ : syracuseStep 2339435 = 3509153) B3509153
theorem B3748459 : Blo 1559477 3748459 := bstep (se 1 (by rfl) ⟨2811344, by rfl⟩ : syracuseStep 3748459 = 5622689) B5622689
theorem B3511007 : Blo 1559477 3511007 := bstep (se 1 (by rfl) ⟨2633255, by rfl⟩ : syracuseStep 3511007 = 5266511) B5266511
theorem B4444895 : Blo 1559477 4444895 := bstep (se 1 (by rfl) ⟨3333671, by rfl⟩ : syracuseStep 4444895 = 6667343) B6667343
theorem B1561311 : Blo 1559477 1561311 := bstep (se 1 (by rfl) ⟨1170983, by rfl⟩ : syracuseStep 1561311 = 2341967) B2341967
theorem B1561391 : Blo 1559477 1561391 := bstep (se 1 (by rfl) ⟨1171043, by rfl⟩ : syracuseStep 1561391 = 2342087) B2342087
theorem B36016969 : Blo 1559477 36016969 := bstep (se 2 (by rfl) ⟨13506363, by rfl⟩ : syracuseStep 36016969 = 27012727) B27012727
theorem B2339663 : Blo 1559477 2339663 := bstep (se 1 (by rfl) ⟨1754747, by rfl⟩ : syracuseStep 2339663 = 3509495) B3509495
theorem B3511259 : Blo 1559477 3511259 := bstep (se 1 (by rfl) ⟨2633444, by rfl⟩ : syracuseStep 3511259 = 5266889) B5266889
theorem B2634727 : Blo 1559477 2634727 := bstep (se 1 (by rfl) ⟨1976045, by rfl⟩ : syracuseStep 2634727 = 3952091) B3952091
theorem B3511439 : Blo 1559477 3511439 := bstep (se 1 (by rfl) ⟨2633579, by rfl⟩ : syracuseStep 3511439 = 5267159) B5267159
theorem B2340059 : Blo 1559477 2340059 := bstep (se 1 (by rfl) ⟨1755044, by rfl⟩ : syracuseStep 2340059 = 3510089) B3510089
theorem B3511529 : Blo 1559477 3511529 := bstep (se 2 (by rfl) ⟨1316823, by rfl⟩ : syracuseStep 3511529 = 2633647) B2633647
theorem B3511583 : Blo 1559477 3511583 := bstep (se 1 (by rfl) ⟨2633687, by rfl⟩ : syracuseStep 3511583 = 5267375) B5267375
theorem B3331451 : Blo 1559477 3331451 := bstep (se 1 (by rfl) ⟨2498588, by rfl⟩ : syracuseStep 3331451 = 4997177) B4997177
theorem B2340233 : Blo 1559477 2340233 := bstep (se 2 (by rfl) ⟨877587, by rfl⟩ : syracuseStep 2340233 = 1755175) B1755175
theorem B5625227 : Blo 1559477 5625227 := bstep (se 1 (by rfl) ⟨4218920, by rfl⟩ : syracuseStep 5625227 = 8437841) B8437841
theorem B4445579 : Blo 1559477 4445579 := bstep (se 1 (by rfl) ⟨3334184, by rfl⟩ : syracuseStep 4445579 = 6668369) B6668369
theorem B12006893 : Blo 1559477 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B5265053 : Blo 1559477 5265053 := bstep (se 3 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 5265053 = 1974395) B1974395
theorem B2340587 : Blo 1559477 2340587 := bstep (se 1 (by rfl) ⟨1755440, by rfl⟩ : syracuseStep 2340587 = 3510881) B3510881
theorem B3512105 : Blo 1559477 3512105 := bstep (se 2 (by rfl) ⟨1317039, by rfl⟩ : syracuseStep 3512105 = 2634079) B2634079
theorem B3749689 : Blo 1559477 3749689 := bstep (se 2 (by rfl) ⟨1406133, by rfl⟩ : syracuseStep 3749689 = 2812267) B2812267
theorem B2340815 : Blo 1559477 2340815 := bstep (se 1 (by rfl) ⟨1755611, by rfl⟩ : syracuseStep 2340815 = 3511223) B3511223
theorem B121690133 : Blo 1559477 121690133 := bstep (se 6 (by rfl) ⟨2852112, by rfl⟩ : syracuseStep 121690133 = 5704225) B5704225
theorem B5265593 : Blo 1559477 5265593 := bstep (se 2 (by rfl) ⟨1974597, by rfl⟩ : syracuseStep 5265593 = 3949195) B3949195
theorem B6412553 : Blo 1559477 6412553 := bstep (se 2 (by rfl) ⟨2404707, by rfl⟩ : syracuseStep 6412553 = 4809415) B4809415
theorem B4503833 : Blo 1559477 4503833 := bstep (se 2 (by rfl) ⟨1688937, by rfl⟩ : syracuseStep 4503833 = 3377875) B3377875
theorem B2341211 : Blo 1559477 2341211 := bstep (se 1 (by rfl) ⟨1755908, by rfl⟩ : syracuseStep 2341211 = 3511817) B3511817
theorem B2963803 : Blo 1559477 2963803 := bstep (se 1 (by rfl) ⟨2222852, by rfl⟩ : syracuseStep 2963803 = 4445705) B4445705
theorem B307960217 : Blo 1559477 307960217 := bstep (se 2 (by rfl) ⟨115485081, by rfl⟩ : syracuseStep 307960217 = 230970163) B230970163
theorem B7903655 : Blo 1559477 7903655 := bstep (se 1 (by rfl) ⟨5927741, by rfl⟩ : syracuseStep 7903655 = 11855483) B11855483
theorem B4217363 : Blo 1559477 4217363 := bstep (se 1 (by rfl) ⟨3163022, by rfl⟩ : syracuseStep 4217363 = 6326045) B6326045
theorem B2341439 : Blo 1559477 2341439 := bstep (se 1 (by rfl) ⟨1756079, by rfl⟩ : syracuseStep 2341439 = 3512159) B3512159
theorem B3332681 : Blo 1559477 3332681 := bstep (se 2 (by rfl) ⟨1249755, by rfl⟩ : syracuseStep 3332681 = 2499511) B2499511
theorem B7903817 : Blo 1559477 7903817 := bstep (se 2 (by rfl) ⟨2963931, by rfl⟩ : syracuseStep 7903817 = 5927863) B5927863
theorem B3332783 : Blo 1559477 3332783 := bstep (se 1 (by rfl) ⟨2499587, by rfl⟩ : syracuseStep 3332783 = 4999175) B4999175
theorem B2341559 : Blo 1559477 2341559 := bstep (se 1 (by rfl) ⟨1756169, by rfl⟩ : syracuseStep 2341559 = 3512339) B3512339
theorem B37968713 : Blo 1559477 37968713 := bstep (se 2 (by rfl) ⟨14238267, by rfl⟩ : syracuseStep 37968713 = 28476535) B28476535
theorem B3513167 : Blo 1559477 3513167 := bstep (se 1 (by rfl) ⟨2634875, by rfl⟩ : syracuseStep 3513167 = 5269751) B5269751
theorem B2341787 : Blo 1559477 2341787 := bstep (se 1 (by rfl) ⟨1756340, by rfl⟩ : syracuseStep 2341787 = 3512681) B3512681
theorem B16006193 : Blo 1559477 16006193 := bstep (se 2 (by rfl) ⟨6002322, by rfl⟩ : syracuseStep 16006193 = 12004645) B12004645
theorem B6667379 : Blo 1559477 6667379 := bstep (se 1 (by rfl) ⟨5000534, by rfl⟩ : syracuseStep 6667379 = 10001069) B10001069
theorem B7896203 : Blo 1559477 7896203 := bstep (se 1 (by rfl) ⟨5922152, by rfl⟩ : syracuseStep 7896203 = 11844305) B11844305
theorem B2342183 : Blo 1559477 2342183 := bstep (se 1 (by rfl) ⟨1756637, by rfl⟩ : syracuseStep 2342183 = 3513275) B3513275
theorem B3947899 : Blo 1559477 3947899 := bstep (se 1 (by rfl) ⟨2960924, by rfl⟩ : syracuseStep 3947899 = 5921849) B5921849
theorem B4742587 : Blo 1559477 4742587 := bstep (se 1 (by rfl) ⟨3556940, by rfl⟩ : syracuseStep 4742587 = 7113881) B7113881
theorem B4005335 : Blo 1559477 4005335 := bstep (se 1 (by rfl) ⟨3004001, by rfl⟩ : syracuseStep 4005335 = 6008003) B6008003
theorem B26672651 : Blo 1559477 26672651 := bstep (se 1 (by rfl) ⟨20004488, by rfl⟩ : syracuseStep 26672651 = 40008977) B40008977
theorem B4996703 : Blo 1559477 4996703 := bstep (se 1 (by rfl) ⟨3747527, by rfl⟩ : syracuseStep 4996703 = 7495055) B7495055
theorem B5267105 : Blo 1559477 5267105 := bstep (se 2 (by rfl) ⟨1975164, by rfl⟩ : syracuseStep 5267105 = 3950329) B3950329
theorem B3948335 : Blo 1559477 3948335 := bstep (se 1 (by rfl) ⟨2961251, by rfl⟩ : syracuseStep 3948335 = 5922503) B5922503
theorem B1974071 : Blo 1559477 1974071 := bstep (se 1 (by rfl) ⟨1480553, by rfl⟩ : syracuseStep 1974071 = 2961107) B2961107
theorem B17784683 : Blo 1559477 17784683 := bstep (se 1 (by rfl) ⟨13338512, by rfl⟩ : syracuseStep 17784683 = 26677025) B26677025
theorem B49397621 : Blo 1559477 49397621 := bstep (se 5 (by rfl) ⟨2315513, by rfl⟩ : syracuseStep 49397621 = 4631027) B4631027
theorem B8003485 : Blo 1559477 8003485 := bstep (se 3 (by rfl) ⟨1500653, by rfl⟩ : syracuseStep 8003485 = 3001307) B3001307
theorem B44965813 : Blo 1559477 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B1974223 : Blo 1559477 1974223 := bstep (se 1 (by rfl) ⟨1480667, by rfl⟩ : syracuseStep 1974223 = 2961335) B2961335
theorem B11247659 : Blo 1559477 11247659 := bstep (se 1 (by rfl) ⟨8435744, by rfl⟩ : syracuseStep 11247659 = 16871489) B16871489
theorem B41107571 : Blo 1559477 41107571 := bstep (se 1 (by rfl) ⟨30830678, by rfl⟩ : syracuseStep 41107571 = 61661357) B61661357
theorem B5267591 : Blo 1559477 5267591 := bstep (se 1 (by rfl) ⟨3950693, by rfl⟩ : syracuseStep 5267591 = 7901387) B7901387
theorem B18972875 : Blo 1559477 18972875 := bstep (se 1 (by rfl) ⟨14229656, by rfl⟩ : syracuseStep 18972875 = 28459313) B28459313
theorem B16867547 : Blo 1559477 16867547 := bstep (se 1 (by rfl) ⟨12650660, by rfl⟩ : syracuseStep 16867547 = 25301321) B25301321
theorem B3949033 : Blo 1559477 3949033 := bstep (se 2 (by rfl) ⟨1480887, by rfl⟩ : syracuseStep 3949033 = 2961775) B2961775
theorem B14992067 : Blo 1559477 14992067 := bstep (se 1 (by rfl) ⟨11244050, by rfl⟩ : syracuseStep 14992067 = 22488101) B22488101
theorem B4997945 : Blo 1559477 4997945 := bstep (se 2 (by rfl) ⟨1874229, by rfl⟩ : syracuseStep 4997945 = 3748459) B3748459
theorem B675668897 : Blo 1559477 675668897 := bstep (se 2 (by rfl) ⟨253375836, by rfl⟩ : syracuseStep 675668897 = 506751673) B506751673
theorem B2220967 : Blo 1559477 2220967 := bstep (se 1 (by rfl) ⟨1665725, by rfl⟩ : syracuseStep 2220967 = 3331451) B3331451
theorem B8004595 : Blo 1559477 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B48022625 : Blo 1559477 48022625 := bstep (se 2 (by rfl) ⟨18008484, by rfl⟩ : syracuseStep 48022625 = 36016969) B36016969
theorem B81126755 : Blo 1559477 81126755 := bstep (se 1 (by rfl) ⟨60845066, by rfl⟩ : syracuseStep 81126755 = 121690133) B121690133
theorem B5269103 : Blo 1559477 5269103 := bstep (se 1 (by rfl) ⟨3951827, by rfl⟩ : syracuseStep 5269103 = 7903655) B7903655
theorem B2811575 : Blo 1559477 2811575 := bstep (se 1 (by rfl) ⟨2108681, by rfl⟩ : syracuseStep 2811575 = 4217363) B4217363
theorem B2221787 : Blo 1559477 2221787 := bstep (se 1 (by rfl) ⟨1666340, by rfl⟩ : syracuseStep 2221787 = 3332681) B3332681
theorem B5269211 : Blo 1559477 5269211 := bstep (se 1 (by rfl) ⟨3951908, by rfl⟩ : syracuseStep 5269211 = 7903817) B7903817
theorem B12650269 : Blo 1559477 12650269 := bstep (se 3 (by rfl) ⟨2371925, by rfl⟩ : syracuseStep 12650269 = 4743851) B4743851
theorem B4999585 : Blo 1559477 4999585 := bstep (se 2 (by rfl) ⟨1874844, by rfl⟩ : syracuseStep 4999585 = 3749689) B3749689
theorem B2632223 : Blo 1559477 2632223 := bstep (se 1 (by rfl) ⟨1974167, by rfl⟩ : syracuseStep 2632223 = 3948335) B3948335
theorem B1755679 : Blo 1559477 1755679 := bstep (se 1 (by rfl) ⟨1316759, by rfl⟩ : syracuseStep 1755679 = 2633519) B2633519
theorem B11856455 : Blo 1559477 11856455 := bstep (se 1 (by rfl) ⟨8892341, by rfl⟩ : syracuseStep 11856455 = 17784683) B17784683
theorem B2632297 : Blo 1559477 2632297 := bstep (se 2 (by rfl) ⟨987111, by rfl⟩ : syracuseStep 2632297 = 1974223) B1974223
theorem B5335739 : Blo 1559477 5335739 := bstep (se 1 (by rfl) ⟨4001804, by rfl⟩ : syracuseStep 5335739 = 8003609) B8003609
theorem B2632655 : Blo 1559477 2632655 := bstep (se 1 (by rfl) ⟨1974491, by rfl⟩ : syracuseStep 2632655 = 3948983) B3948983
theorem B11848679 : Blo 1559477 11848679 := bstep (se 1 (by rfl) ⟨8886509, by rfl⟩ : syracuseStep 11848679 = 17773019) B17773019
theorem B1559599 : Blo 1559477 1559599 := bstep (se 1 (by rfl) ⟨1169699, by rfl⟩ : syracuseStep 1559599 = 2339399) B2339399
theorem B1559623 : Blo 1559477 1559623 := bstep (se 1 (by rfl) ⟨1169717, by rfl⟩ : syracuseStep 1559623 = 2339435) B2339435
theorem B3509369 : Blo 1559477 3509369 := bstep (se 2 (by rfl) ⟨1316013, by rfl⟩ : syracuseStep 3509369 = 2632027) B2632027
theorem B3951737 : Blo 1559477 3951737 := bstep (se 2 (by rfl) ⟨1481901, by rfl⟩ : syracuseStep 3951737 = 2963803) B2963803
theorem B4746383 : Blo 1559477 4746383 := bstep (se 1 (by rfl) ⟨3559787, by rfl⟩ : syracuseStep 4746383 = 7119575) B7119575
theorem B1559775 : Blo 1559477 1559775 := bstep (se 1 (by rfl) ⟨1169831, by rfl⟩ : syracuseStep 1559775 = 2339663) B2339663
theorem B1560039 : Blo 1559477 1560039 := bstep (se 1 (by rfl) ⟨1170029, by rfl⟩ : syracuseStep 1560039 = 2340059) B2340059
theorem B2960887 : Blo 1559477 2960887 := bstep (se 1 (by rfl) ⟨2220665, by rfl⟩ : syracuseStep 2960887 = 4441331) B4441331
theorem B5926391 : Blo 1559477 5926391 := bstep (se 1 (by rfl) ⟨4444793, by rfl⟩ : syracuseStep 5926391 = 8889587) B8889587
theorem B8891977 : Blo 1559477 8891977 := bstep (se 2 (by rfl) ⟨3334491, by rfl⟩ : syracuseStep 8891977 = 6668983) B6668983
theorem B1560155 : Blo 1559477 1560155 := bstep (se 1 (by rfl) ⟨1170116, by rfl⟩ : syracuseStep 1560155 = 2340233) B2340233
theorem B48672353 : Blo 1559477 48672353 := bstep (se 2 (by rfl) ⟨18252132, by rfl⟩ : syracuseStep 48672353 = 36504265) B36504265
theorem B2633323 : Blo 1559477 2633323 := bstep (se 1 (by rfl) ⟨1974992, by rfl⟩ : syracuseStep 2633323 = 3949985) B3949985
theorem B3510035 : Blo 1559477 3510035 := bstep (se 1 (by rfl) ⟨2632526, by rfl⟩ : syracuseStep 3510035 = 5265053) B5265053
theorem B2961191 : Blo 1559477 2961191 := bstep (se 1 (by rfl) ⟨2220893, by rfl⟩ : syracuseStep 2961191 = 4441787) B4441787
theorem B22507307 : Blo 1559477 22507307 := bstep (se 1 (by rfl) ⟨16880480, by rfl⟩ : syracuseStep 22507307 = 33760961) B33760961
theorem B1560391 : Blo 1559477 1560391 := bstep (se 1 (by rfl) ⟨1170293, by rfl⟩ : syracuseStep 1560391 = 2340587) B2340587
theorem B2633593 : Blo 1559477 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B2633627 : Blo 1559477 2633627 := bstep (se 1 (by rfl) ⟨1975220, by rfl⟩ : syracuseStep 2633627 = 3950441) B3950441
theorem B1560543 : Blo 1559477 1560543 := bstep (se 1 (by rfl) ⟨1170407, by rfl⟩ : syracuseStep 1560543 = 2340815) B2340815
theorem B12660785 : Blo 1559477 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B3510395 : Blo 1559477 3510395 := bstep (se 1 (by rfl) ⟨2632796, by rfl⟩ : syracuseStep 3510395 = 5265593) B5265593
theorem B11251835 : Blo 1559477 11251835 := bstep (se 1 (by rfl) ⟨8438876, by rfl⟩ : syracuseStep 11251835 = 16877753) B16877753
theorem B3002555 : Blo 1559477 3002555 := bstep (se 1 (by rfl) ⟨2251916, by rfl⟩ : syracuseStep 3002555 = 4503833) B4503833
theorem B1560807 : Blo 1559477 1560807 := bstep (se 1 (by rfl) ⟨1170605, by rfl⟩ : syracuseStep 1560807 = 2341211) B2341211
theorem B6664457 : Blo 1559477 6664457 := bstep (se 2 (by rfl) ⟨2499171, by rfl⟩ : syracuseStep 6664457 = 4998343) B4998343
theorem B3748151 : Blo 1559477 3748151 := bstep (se 1 (by rfl) ⟨2811113, by rfl⟩ : syracuseStep 3748151 = 5622227) B5622227
theorem B1560959 : Blo 1559477 1560959 := bstep (se 1 (by rfl) ⟨1170719, by rfl⟩ : syracuseStep 1560959 = 2341439) B2341439
theorem B3510665 : Blo 1559477 3510665 := bstep (se 2 (by rfl) ⟨1316499, by rfl⟩ : syracuseStep 3510665 = 2632999) B2632999
theorem B2339279 : Blo 1559477 2339279 := bstep (se 1 (by rfl) ⟨1754459, by rfl⟩ : syracuseStep 2339279 = 3508919) B3508919
theorem B1561039 : Blo 1559477 1561039 := bstep (se 1 (by rfl) ⟨1170779, by rfl⟩ : syracuseStep 1561039 = 2341559) B2341559
theorem B5263865 : Blo 1559477 5263865 := bstep (se 2 (by rfl) ⟨1973949, by rfl⟩ : syracuseStep 5263865 = 3947899) B3947899
theorem B2339321 : Blo 1559477 2339321 := bstep (se 2 (by rfl) ⟨877245, by rfl⟩ : syracuseStep 2339321 = 1754491) B1754491
theorem B2962003 : Blo 1559477 2962003 := bstep (se 1 (by rfl) ⟨2221502, by rfl⟩ : syracuseStep 2962003 = 4443005) B4443005
theorem B2339423 : Blo 1559477 2339423 := bstep (se 1 (by rfl) ⟨1754567, by rfl⟩ : syracuseStep 2339423 = 3509135) B3509135
theorem B1561191 : Blo 1559477 1561191 := bstep (se 1 (by rfl) ⟨1170893, by rfl⟩ : syracuseStep 1561191 = 2341787) B2341787
theorem B10670795 : Blo 1559477 10670795 := bstep (se 1 (by rfl) ⟨8003096, by rfl⟩ : syracuseStep 10670795 = 16006193) B16006193
theorem B4444919 : Blo 1559477 4444919 := bstep (se 1 (by rfl) ⟨3333689, by rfl⟩ : syracuseStep 4444919 = 6667379) B6667379
theorem B5264135 : Blo 1559477 5264135 := bstep (se 1 (by rfl) ⟨3948101, by rfl⟩ : syracuseStep 5264135 = 7896203) B7896203
theorem B5264189 : Blo 1559477 5264189 := bstep (se 3 (by rfl) ⟨987035, by rfl⟩ : syracuseStep 5264189 = 1974071) B1974071
theorem B1561455 : Blo 1559477 1561455 := bstep (se 1 (by rfl) ⟨1171091, by rfl⟩ : syracuseStep 1561455 = 2342183) B2342183
theorem B17781767 : Blo 1559477 17781767 := bstep (se 1 (by rfl) ⟨13336325, by rfl⟩ : syracuseStep 17781767 = 26672651) B26672651
theorem B3331135 : Blo 1559477 3331135 := bstep (se 1 (by rfl) ⟨2498351, by rfl⟩ : syracuseStep 3331135 = 4996703) B4996703
theorem B2339903 : Blo 1559477 2339903 := bstep (se 1 (by rfl) ⟨1754927, by rfl⟩ : syracuseStep 2339903 = 3509855) B3509855
theorem B2634815 : Blo 1559477 2634815 := bstep (se 1 (by rfl) ⟨1976111, by rfl⟩ : syracuseStep 2634815 = 3952223) B3952223
theorem B2339945 : Blo 1559477 2339945 := bstep (se 2 (by rfl) ⟨877479, by rfl⟩ : syracuseStep 2339945 = 1754959) B1754959
theorem B3511403 : Blo 1559477 3511403 := bstep (se 1 (by rfl) ⟨2633552, by rfl⟩ : syracuseStep 3511403 = 5267105) B5267105
theorem B50607301 : Blo 1559477 50607301 := bstep (se 4 (by rfl) ⟨4744434, by rfl⟩ : syracuseStep 50607301 = 9488869) B9488869
theorem B2340047 : Blo 1559477 2340047 := bstep (se 1 (by rfl) ⟨1755035, by rfl⟩ : syracuseStep 2340047 = 3510071) B3510071
theorem B10671313 : Blo 1559477 10671313 := bstep (se 2 (by rfl) ⟨4001742, by rfl⟩ : syracuseStep 10671313 = 8003485) B8003485
theorem B3749075 : Blo 1559477 3749075 := bstep (se 1 (by rfl) ⟨2811806, by rfl⟩ : syracuseStep 3749075 = 5623613) B5623613
theorem B4568275 : Blo 1559477 4568275 := bstep (se 1 (by rfl) ⟨3426206, by rfl⟩ : syracuseStep 4568275 = 6852413) B6852413
theorem B59954417 : Blo 1559477 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B2340251 : Blo 1559477 2340251 := bstep (se 1 (by rfl) ⟨1755188, by rfl⟩ : syracuseStep 2340251 = 3510377) B3510377
theorem B2340473 : Blo 1559477 2340473 := bstep (se 2 (by rfl) ⟨877677, by rfl⟩ : syracuseStep 2340473 = 1755355) B1755355
theorem B10000043 : Blo 1559477 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B3511979 : Blo 1559477 3511979 := bstep (se 1 (by rfl) ⟨2633984, by rfl⟩ : syracuseStep 3511979 = 5267969) B5267969
theorem B2340575 : Blo 1559477 2340575 := bstep (se 1 (by rfl) ⟨1755431, by rfl⟩ : syracuseStep 2340575 = 3510863) B3510863
theorem B5265215 : Blo 1559477 5265215 := bstep (se 1 (by rfl) ⟨3948911, by rfl⟩ : syracuseStep 5265215 = 7897823) B7897823
theorem B2340671 : Blo 1559477 2340671 := bstep (se 1 (by rfl) ⟨1755503, by rfl⟩ : syracuseStep 2340671 = 3511007) B3511007
theorem B2340839 : Blo 1559477 2340839 := bstep (se 1 (by rfl) ⟨1755629, by rfl⟩ : syracuseStep 2340839 = 3511259) B3511259
theorem B3512303 : Blo 1559477 3512303 := bstep (se 1 (by rfl) ⟨2634227, by rfl⟩ : syracuseStep 3512303 = 5268455) B5268455
theorem B2340857 : Blo 1559477 2340857 := bstep (se 2 (by rfl) ⟨877821, by rfl⟩ : syracuseStep 2340857 = 1755643) B1755643
theorem B75929633 : Blo 1559477 75929633 := bstep (se 2 (by rfl) ⟨28473612, by rfl⟩ : syracuseStep 75929633 = 56947225) B56947225
theorem B10672195 : Blo 1559477 10672195 := bstep (se 1 (by rfl) ⟨8004146, by rfl⟩ : syracuseStep 10672195 = 16008293) B16008293
theorem B2340959 : Blo 1559477 2340959 := bstep (se 1 (by rfl) ⟨1755719, by rfl⟩ : syracuseStep 2340959 = 3511439) B3511439
theorem B2341019 : Blo 1559477 2341019 := bstep (se 1 (by rfl) ⟨1755764, by rfl⟩ : syracuseStep 2341019 = 3511529) B3511529
theorem B2341055 : Blo 1559477 2341055 := bstep (se 1 (by rfl) ⟨1755791, by rfl⟩ : syracuseStep 2341055 = 3511583) B3511583
theorem B10000583 : Blo 1559477 10000583 := bstep (se 1 (by rfl) ⟨7500437, by rfl⟩ : syracuseStep 10000583 = 15000875) B15000875
theorem B3512519 : Blo 1559477 3512519 := bstep (se 1 (by rfl) ⟨2634389, by rfl⟩ : syracuseStep 3512519 = 5268779) B5268779
theorem B2341097 : Blo 1559477 2341097 := bstep (se 2 (by rfl) ⟨877911, by rfl⟩ : syracuseStep 2341097 = 1755823) B1755823
theorem B3750151 : Blo 1559477 3750151 := bstep (se 1 (by rfl) ⟨2812613, by rfl⟩ : syracuseStep 3750151 = 5625227) B5625227
theorem B2963719 : Blo 1559477 2963719 := bstep (se 1 (by rfl) ⟨2222789, by rfl⟩ : syracuseStep 2963719 = 4445579) B4445579
theorem B7493995 : Blo 1559477 7493995 := bstep (se 1 (by rfl) ⟨5620496, by rfl⟩ : syracuseStep 7493995 = 11240993) B11240993
theorem B3512699 : Blo 1559477 3512699 := bstep (se 1 (by rfl) ⟨2634524, by rfl⟩ : syracuseStep 3512699 = 5269049) B5269049
theorem B8886671 : Blo 1559477 8886671 := bstep (se 1 (by rfl) ⟨6665003, by rfl⟩ : syracuseStep 8886671 = 13330007) B13330007
theorem B2341403 : Blo 1559477 2341403 := bstep (se 1 (by rfl) ⟨1756052, by rfl⟩ : syracuseStep 2341403 = 3512105) B3512105
theorem B10680893 : Blo 1559477 10680893 := bstep (se 3 (by rfl) ⟨2002667, by rfl⟩ : syracuseStep 10680893 = 4005335) B4005335
theorem B2341481 : Blo 1559477 2341481 := bstep (se 2 (by rfl) ⟨878055, by rfl⟩ : syracuseStep 2341481 = 1756111) B1756111
theorem B3512969 : Blo 1559477 3512969 := bstep (se 2 (by rfl) ⟨1317363, by rfl⟩ : syracuseStep 3512969 = 2634727) B2634727
theorem B17767187 : Blo 1559477 17767187 := bstep (se 1 (by rfl) ⟨13325390, by rfl⟩ : syracuseStep 17767187 = 26650781) B26650781
theorem B4275035 : Blo 1559477 4275035 := bstep (se 1 (by rfl) ⟨3206276, by rfl⟩ : syracuseStep 4275035 = 6412553) B6412553
theorem B205306811 : Blo 1559477 205306811 := bstep (se 1 (by rfl) ⟨153980108, by rfl⟩ : syracuseStep 205306811 = 307960217) B307960217
theorem B5626871 : Blo 1559477 5626871 := bstep (se 1 (by rfl) ⟨4220153, by rfl⟩ : syracuseStep 5626871 = 8440307) B8440307
theorem B2251847 : Blo 1559477 2251847 := bstep (se 1 (by rfl) ⟨1688885, by rfl⟩ : syracuseStep 2251847 = 3377771) B3377771
theorem B2342009 : Blo 1559477 2342009 := bstep (se 2 (by rfl) ⟨878253, by rfl⟩ : syracuseStep 2342009 = 1756507) B1756507
theorem B8887421 : Blo 1559477 8887421 := bstep (se 3 (by rfl) ⟨1666391, by rfl⟩ : syracuseStep 8887421 = 3332783) B3332783
theorem B25312475 : Blo 1559477 25312475 := bstep (se 1 (by rfl) ⟨18984356, by rfl⟩ : syracuseStep 25312475 = 37968713) B37968713
theorem B2342111 : Blo 1559477 2342111 := bstep (se 1 (by rfl) ⟨1756583, by rfl⟩ : syracuseStep 2342111 = 3513167) B3513167
theorem B6323449 : Blo 1559477 6323449 := bstep (se 2 (by rfl) ⟨2371293, by rfl⟩ : syracuseStep 6323449 = 4742587) B4742587
theorem B11853053 : Blo 1559477 11853053 := bstep (se 3 (by rfl) ⟨2222447, by rfl⟩ : syracuseStep 11853053 = 4444895) B4444895
theorem B2342153 : Blo 1559477 2342153 := bstep (se 2 (by rfl) ⟨878307, by rfl⟩ : syracuseStep 2342153 = 1756615) B1756615
theorem B5266727 : Blo 1559477 5266727 := bstep (se 1 (by rfl) ⟨3950045, by rfl⟩ : syracuseStep 5266727 = 7900091) B7900091
theorem B91250081 : Blo 1559477 91250081 := bstep (se 2 (by rfl) ⟨34218780, by rfl⟩ : syracuseStep 91250081 = 68437561) B68437561
theorem B5627303 : Blo 1559477 5627303 := bstep (se 1 (by rfl) ⟨4220477, by rfl⟩ : syracuseStep 5627303 = 8440955) B8440955
theorem B6757967 : Blo 1559477 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B131726989 : Blo 1559477 131726989 := bstep (se 3 (by rfl) ⟨24698810, by rfl⟩ : syracuseStep 131726989 = 49397621) B49397621
theorem B18980563 : Blo 1559477 18980563 := bstep (se 1 (by rfl) ⟨14235422, by rfl⟩ : syracuseStep 18980563 = 28470845) B28470845
theorem B72114137 : Blo 1559477 72114137 := bstep (se 2 (by rfl) ⟨27042801, by rfl⟩ : syracuseStep 72114137 = 54085603) B54085603
theorem B14999525 : Blo 1559477 14999525 := bstep (se 4 (by rfl) ⟨1406205, by rfl⟩ : syracuseStep 14999525 = 2812411) B2812411
theorem B14229593 : Blo 1559477 14229593 := bstep (se 2 (by rfl) ⟨5336097, by rfl⟩ : syracuseStep 14229593 = 10672195) B10672195
theorem B12648583 : Blo 1559477 12648583 := bstep (se 1 (by rfl) ⟨9486437, by rfl⟩ : syracuseStep 12648583 = 18972875) B18972875
theorem B6004925 : Blo 1559477 6004925 := bstep (se 3 (by rfl) ⟨1125923, by rfl⟩ : syracuseStep 6004925 = 2251847) B2251847
theorem B9994711 : Blo 1559477 9994711 := bstep (se 1 (by rfl) ⟨7496033, by rfl⟩ : syracuseStep 9994711 = 14992067) B14992067
theorem B450445931 : Blo 1559477 450445931 := bstep (se 1 (by rfl) ⟨337834448, by rfl⟩ : syracuseStep 450445931 = 675668897) B675668897
theorem B11854511 : Blo 1559477 11854511 := bstep (se 1 (by rfl) ⟨8890883, by rfl⟩ : syracuseStep 11854511 = 17781767) B17781767
theorem B32015083 : Blo 1559477 32015083 := bstep (se 1 (by rfl) ⟨24011312, by rfl⟩ : syracuseStep 32015083 = 48022625) B48022625
theorem B3949337 : Blo 1559477 3949337 := bstep (se 2 (by rfl) ⟨1481001, by rfl⟩ : syracuseStep 3949337 = 2962003) B2962003
theorem B2499383 : Blo 1559477 2499383 := bstep (se 1 (by rfl) ⟨1874537, by rfl⟩ : syracuseStep 2499383 = 3749075) B3749075
theorem B9995069 : Blo 1559477 9995069 := bstep (se 3 (by rfl) ⟨1874075, by rfl⟩ : syracuseStep 9995069 = 3748151) B3748151
theorem B39969611 : Blo 1559477 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B54084503 : Blo 1559477 54084503 := bstep (se 1 (by rfl) ⟨40563377, by rfl⟩ : syracuseStep 54084503 = 81126755) B81126755
theorem B50619755 : Blo 1559477 50619755 := bstep (se 1 (by rfl) ⟨37964816, by rfl⟩ : syracuseStep 50619755 = 75929633) B75929633
theorem B4441513 : Blo 1559477 4441513 := bstep (se 2 (by rfl) ⟨1665567, by rfl⟩ : syracuseStep 4441513 = 3331135) B3331135
theorem B5924447 : Blo 1559477 5924447 := bstep (se 1 (by rfl) ⟨4443335, by rfl⟩ : syracuseStep 5924447 = 8886671) B8886671
theorem B8431265 : Blo 1559477 8431265 := bstep (se 2 (by rfl) ⟨3161724, by rfl⟩ : syracuseStep 8431265 = 6323449) B6323449
theorem B1754815 : Blo 1559477 1754815 := bstep (se 1 (by rfl) ⟨1316111, by rfl⟩ : syracuseStep 1754815 = 2632223) B2632223
theorem B7120595 : Blo 1559477 7120595 := bstep (se 1 (by rfl) ⟨5340446, by rfl⟩ : syracuseStep 7120595 = 10680893) B10680893
theorem B3557159 : Blo 1559477 3557159 := bstep (se 1 (by rfl) ⟨2667869, by rfl⟩ : syracuseStep 3557159 = 5335739) B5335739
theorem B5924765 : Blo 1559477 5924765 := bstep (se 3 (by rfl) ⟨1110893, by rfl⟩ : syracuseStep 5924765 = 2221787) B2221787
theorem B1755103 : Blo 1559477 1755103 := bstep (se 1 (by rfl) ⟨1316327, by rfl⟩ : syracuseStep 1755103 = 2632655) B2632655
theorem B7899119 : Blo 1559477 7899119 := bstep (se 1 (by rfl) ⟨5924339, by rfl⟩ : syracuseStep 7899119 = 11848679) B11848679
theorem B5924947 : Blo 1559477 5924947 := bstep (se 1 (by rfl) ⟨4443710, by rfl⟩ : syracuseStep 5924947 = 8887421) B8887421
theorem B3164255 : Blo 1559477 3164255 := bstep (se 1 (by rfl) ⟨2373191, by rfl⟩ : syracuseStep 3164255 = 4746383) B4746383
theorem B11855969 : Blo 1559477 11855969 := bstep (se 2 (by rfl) ⟨4445988, by rfl⟩ : syracuseStep 11855969 = 8891977) B8891977
theorem B25307417 : Blo 1559477 25307417 := bstep (se 2 (by rfl) ⟨9490281, by rfl⟩ : syracuseStep 25307417 = 18980563) B18980563
theorem B3950927 : Blo 1559477 3950927 := bstep (se 1 (by rfl) ⟨2963195, by rfl⟩ : syracuseStep 3950927 = 5926391) B5926391
theorem B1755751 : Blo 1559477 1755751 := bstep (se 1 (by rfl) ⟨1316813, by rfl⟩ : syracuseStep 1755751 = 2633627) B2633627
theorem B7498439 : Blo 1559477 7498439 := bstep (se 1 (by rfl) ⟨5623829, by rfl⟩ : syracuseStep 7498439 = 11247659) B11247659
theorem B8440523 : Blo 1559477 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B27405047 : Blo 1559477 27405047 := bstep (se 1 (by rfl) ⟨20553785, by rfl⟩ : syracuseStep 27405047 = 41107571) B41107571
theorem B4442971 : Blo 1559477 4442971 := bstep (se 1 (by rfl) ⟨3332228, by rfl⟩ : syracuseStep 4442971 = 6664457) B6664457
theorem B1559519 : Blo 1559477 1559519 := bstep (se 1 (by rfl) ⟨1169639, by rfl⟩ : syracuseStep 1559519 = 2339279) B2339279
theorem B3509243 : Blo 1559477 3509243 := bstep (se 1 (by rfl) ⟨2631932, by rfl⟩ : syracuseStep 3509243 = 5263865) B5263865
theorem B1559547 : Blo 1559477 1559547 := bstep (se 1 (by rfl) ⟨1169660, by rfl⟩ : syracuseStep 1559547 = 2339321) B2339321
theorem B5000201 : Blo 1559477 5000201 := bstep (se 2 (by rfl) ⟨1875075, by rfl⟩ : syracuseStep 5000201 = 3750151) B3750151
theorem B3951625 : Blo 1559477 3951625 := bstep (se 2 (by rfl) ⟨1481859, by rfl⟩ : syracuseStep 3951625 = 2963719) B2963719
theorem B1559615 : Blo 1559477 1559615 := bstep (se 1 (by rfl) ⟨1169711, by rfl⟩ : syracuseStep 1559615 = 2339423) B2339423
theorem B7113863 : Blo 1559477 7113863 := bstep (se 1 (by rfl) ⟨5335397, by rfl⟩ : syracuseStep 7113863 = 10670795) B10670795
theorem B8006813 : Blo 1559477 8006813 := bstep (se 3 (by rfl) ⟨1501277, by rfl⟩ : syracuseStep 8006813 = 3002555) B3002555
theorem B3509423 : Blo 1559477 3509423 := bstep (se 1 (by rfl) ⟨2632067, by rfl⟩ : syracuseStep 3509423 = 5264135) B5264135
theorem B3509459 : Blo 1559477 3509459 := bstep (se 1 (by rfl) ⟨2632094, by rfl⟩ : syracuseStep 3509459 = 5264189) B5264189
theorem B1559935 : Blo 1559477 1559935 := bstep (se 1 (by rfl) ⟨1169951, by rfl⟩ : syracuseStep 1559935 = 2339903) B2339903
theorem B1756543 : Blo 1559477 1756543 := bstep (se 1 (by rfl) ⟨1317407, by rfl⟩ : syracuseStep 1756543 = 2634815) B2634815
theorem B1559963 : Blo 1559477 1559963 := bstep (se 1 (by rfl) ⟨1169972, by rfl⟩ : syracuseStep 1559963 = 2339945) B2339945
theorem B1560031 : Blo 1559477 1560031 := bstep (se 1 (by rfl) ⟨1170023, by rfl⟩ : syracuseStep 1560031 = 2340047) B2340047
theorem B3509729 : Blo 1559477 3509729 := bstep (se 2 (by rfl) ⟨1316148, by rfl⟩ : syracuseStep 3509729 = 2632297) B2632297
theorem B1560167 : Blo 1559477 1560167 := bstep (se 1 (by rfl) ⟨1170125, by rfl⟩ : syracuseStep 1560167 = 2340251) B2340251
theorem B1560315 : Blo 1559477 1560315 := bstep (se 1 (by rfl) ⟨1170236, by rfl⟩ : syracuseStep 1560315 = 2340473) B2340473
theorem B1560383 : Blo 1559477 1560383 := bstep (se 1 (by rfl) ⟨1170287, by rfl⟩ : syracuseStep 1560383 = 2340575) B2340575
theorem B3510143 : Blo 1559477 3510143 := bstep (se 1 (by rfl) ⟨2632607, by rfl⟩ : syracuseStep 3510143 = 5265215) B5265215
theorem B1560447 : Blo 1559477 1560447 := bstep (se 1 (by rfl) ⟨1170335, by rfl⟩ : syracuseStep 1560447 = 2340671) B2340671
theorem B2961289 : Blo 1559477 2961289 := bstep (se 2 (by rfl) ⟨1110483, by rfl⟩ : syracuseStep 2961289 = 2220967) B2220967
theorem B1560559 : Blo 1559477 1560559 := bstep (se 1 (by rfl) ⟨1170419, by rfl⟩ : syracuseStep 1560559 = 2340839) B2340839
theorem B1560571 : Blo 1559477 1560571 := bstep (se 1 (by rfl) ⟨1170428, by rfl⟩ : syracuseStep 1560571 = 2340857) B2340857
theorem B1560639 : Blo 1559477 1560639 := bstep (se 1 (by rfl) ⟨1170479, by rfl⟩ : syracuseStep 1560639 = 2340959) B2340959
theorem B1560679 : Blo 1559477 1560679 := bstep (se 1 (by rfl) ⟨1170509, by rfl⟩ : syracuseStep 1560679 = 2341019) B2341019
theorem B1560703 : Blo 1559477 1560703 := bstep (se 1 (by rfl) ⟨1170527, by rfl⟩ : syracuseStep 1560703 = 2341055) B2341055
theorem B1560731 : Blo 1559477 1560731 := bstep (se 1 (by rfl) ⟨1170548, by rfl⟩ : syracuseStep 1560731 = 2341097) B2341097
theorem B6091033 : Blo 1559477 6091033 := bstep (se 2 (by rfl) ⟨2284137, by rfl⟩ : syracuseStep 6091033 = 4568275) B4568275
theorem B1560935 : Blo 1559477 1560935 := bstep (se 1 (by rfl) ⟨1170701, by rfl⟩ : syracuseStep 1560935 = 2341403) B2341403
theorem B1560987 : Blo 1559477 1560987 := bstep (se 1 (by rfl) ⟨1170740, by rfl⟩ : syracuseStep 1560987 = 2341481) B2341481
theorem B2339579 : Blo 1559477 2339579 := bstep (se 1 (by rfl) ⟨1754684, by rfl⟩ : syracuseStep 2339579 = 3509369) B3509369
theorem B2634491 : Blo 1559477 2634491 := bstep (se 1 (by rfl) ⟨1975868, by rfl⟩ : syracuseStep 2634491 = 3951737) B3951737
theorem B1561339 : Blo 1559477 1561339 := bstep (se 1 (by rfl) ⟨1171004, by rfl⟩ : syracuseStep 1561339 = 2342009) B2342009
theorem B3511097 : Blo 1559477 3511097 := bstep (se 2 (by rfl) ⟨1316661, by rfl⟩ : syracuseStep 3511097 = 2633323) B2633323
theorem B1561407 : Blo 1559477 1561407 := bstep (se 1 (by rfl) ⟨1171055, by rfl⟩ : syracuseStep 1561407 = 2342111) B2342111
theorem B7902035 : Blo 1559477 7902035 := bstep (se 1 (by rfl) ⟨5926526, by rfl⟩ : syracuseStep 7902035 = 11853053) B11853053
theorem B1561435 : Blo 1559477 1561435 := bstep (se 1 (by rfl) ⟨1171076, by rfl⟩ : syracuseStep 1561435 = 2342153) B2342153
theorem B3511151 : Blo 1559477 3511151 := bstep (se 1 (by rfl) ⟨2633363, by rfl⟩ : syracuseStep 3511151 = 5266727) B5266727
theorem B3511457 : Blo 1559477 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B2340023 : Blo 1559477 2340023 := bstep (se 1 (by rfl) ⟨1755017, by rfl⟩ : syracuseStep 2340023 = 3510035) B3510035
theorem B15004871 : Blo 1559477 15004871 := bstep (se 1 (by rfl) ⟨11253653, by rfl⟩ : syracuseStep 15004871 = 22507307) B22507307
theorem B48076091 : Blo 1559477 48076091 := bstep (se 1 (by rfl) ⟨36057068, by rfl⟩ : syracuseStep 48076091 = 72114137) B72114137
theorem B9999683 : Blo 1559477 9999683 := bstep (se 1 (by rfl) ⟨7499762, by rfl⟩ : syracuseStep 9999683 = 14999525) B14999525
theorem B2340263 : Blo 1559477 2340263 := bstep (se 1 (by rfl) ⟨1755197, by rfl⟩ : syracuseStep 2340263 = 3510395) B3510395
theorem B7501223 : Blo 1559477 7501223 := bstep (se 1 (by rfl) ⟨5625917, by rfl⟩ : syracuseStep 7501223 = 11251835) B11251835
theorem B3511727 : Blo 1559477 3511727 := bstep (se 1 (by rfl) ⟨2633795, by rfl⟩ : syracuseStep 3511727 = 5267591) B5267591
theorem B11245031 : Blo 1559477 11245031 := bstep (se 1 (by rfl) ⟨8433773, by rfl⟩ : syracuseStep 11245031 = 16867547) B16867547
theorem B2340443 : Blo 1559477 2340443 := bstep (se 1 (by rfl) ⟨1755332, by rfl⟩ : syracuseStep 2340443 = 3510665) B3510665
theorem B9991993 : Blo 1559477 9991993 := bstep (se 2 (by rfl) ⟨3746997, by rfl⟩ : syracuseStep 9991993 = 7493995) B7493995
theorem B2963279 : Blo 1559477 2963279 := bstep (se 1 (by rfl) ⟨2222459, by rfl⟩ : syracuseStep 2963279 = 4444919) B4444919
theorem B3331963 : Blo 1559477 3331963 := bstep (se 1 (by rfl) ⟨2498972, by rfl⟩ : syracuseStep 3331963 = 4997945) B4997945
theorem B6666113 : Blo 1559477 6666113 := bstep (se 2 (by rfl) ⟨2499792, by rfl⟩ : syracuseStep 6666113 = 4999585) B4999585
theorem B5265377 : Blo 1559477 5265377 := bstep (se 2 (by rfl) ⟨1974516, by rfl⟩ : syracuseStep 5265377 = 3949033) B3949033
theorem B2340905 : Blo 1559477 2340905 := bstep (se 2 (by rfl) ⟨877839, by rfl⟩ : syracuseStep 2340905 = 1755679) B1755679
theorem B2340935 : Blo 1559477 2340935 := bstep (se 1 (by rfl) ⟨1755701, by rfl⟩ : syracuseStep 2340935 = 3511403) B3511403
theorem B3512735 : Blo 1559477 3512735 := bstep (se 1 (by rfl) ⟨2634551, by rfl⟩ : syracuseStep 3512735 = 5269103) B5269103
theorem B6666695 : Blo 1559477 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B2341319 : Blo 1559477 2341319 := bstep (se 1 (by rfl) ⟨1755989, by rfl⟩ : syracuseStep 2341319 = 3511979) B3511979
theorem B1874383 : Blo 1559477 1874383 := bstep (se 1 (by rfl) ⟨1405787, by rfl⟩ : syracuseStep 1874383 = 2811575) B2811575
theorem B3512807 : Blo 1559477 3512807 := bstep (se 1 (by rfl) ⟨2634605, by rfl⟩ : syracuseStep 3512807 = 5269211) B5269211
theorem B10672793 : Blo 1559477 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B2341535 : Blo 1559477 2341535 := bstep (se 1 (by rfl) ⟨1756151, by rfl⟩ : syracuseStep 2341535 = 3512303) B3512303
theorem B6667055 : Blo 1559477 6667055 := bstep (se 1 (by rfl) ⟨5000291, by rfl⟩ : syracuseStep 6667055 = 10000583) B10000583
theorem B2341679 : Blo 1559477 2341679 := bstep (se 1 (by rfl) ⟨1756259, by rfl⟩ : syracuseStep 2341679 = 3512519) B3512519
theorem B2341799 : Blo 1559477 2341799 := bstep (se 1 (by rfl) ⟨1756349, by rfl⟩ : syracuseStep 2341799 = 3512699) B3512699
theorem B67476401 : Blo 1559477 67476401 := bstep (se 2 (by rfl) ⟨25303650, by rfl⟩ : syracuseStep 67476401 = 50607301) B50607301
theorem B14228417 : Blo 1559477 14228417 := bstep (se 2 (by rfl) ⟨5335656, by rfl⟩ : syracuseStep 14228417 = 10671313) B10671313
theorem B7904303 : Blo 1559477 7904303 := bstep (se 1 (by rfl) ⟨5928227, by rfl⟩ : syracuseStep 7904303 = 11856455) B11856455
theorem B2341979 : Blo 1559477 2341979 := bstep (se 1 (by rfl) ⟨1756484, by rfl⟩ : syracuseStep 2341979 = 3512969) B3512969
theorem B11844791 : Blo 1559477 11844791 := bstep (se 1 (by rfl) ⟨8883593, by rfl⟩ : syracuseStep 11844791 = 17767187) B17767187
theorem B2850023 : Blo 1559477 2850023 := bstep (se 1 (by rfl) ⟨2137517, by rfl⟩ : syracuseStep 2850023 = 4275035) B4275035
theorem B136871207 : Blo 1559477 136871207 := bstep (se 1 (by rfl) ⟨102653405, by rfl⟩ : syracuseStep 136871207 = 205306811) B205306811
theorem B3947849 : Blo 1559477 3947849 := bstep (se 2 (by rfl) ⟨1480443, by rfl⟩ : syracuseStep 3947849 = 2960887) B2960887
theorem B3751247 : Blo 1559477 3751247 := bstep (se 1 (by rfl) ⟨2813435, by rfl⟩ : syracuseStep 3751247 = 5626871) B5626871
theorem B16874983 : Blo 1559477 16874983 := bstep (se 1 (by rfl) ⟨12656237, by rfl⟩ : syracuseStep 16874983 = 25312475) B25312475
theorem B175635985 : Blo 1559477 175635985 := bstep (se 2 (by rfl) ⟨65863494, by rfl⟩ : syracuseStep 175635985 = 131726989) B131726989
theorem B60833387 : Blo 1559477 60833387 := bstep (se 1 (by rfl) ⟨45625040, by rfl⟩ : syracuseStep 60833387 = 91250081) B91250081
theorem B3751535 : Blo 1559477 3751535 := bstep (se 1 (by rfl) ⟨2813651, by rfl⟩ : syracuseStep 3751535 = 5627303) B5627303
theorem B16867025 : Blo 1559477 16867025 := bstep (se 2 (by rfl) ⟨6325134, by rfl⟩ : syracuseStep 16867025 = 12650269) B12650269
theorem B4505311 : Blo 1559477 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B32448235 : Blo 1559477 32448235 := bstep (se 1 (by rfl) ⟨24336176, by rfl⟩ : syracuseStep 32448235 = 48672353) B48672353
theorem B1974127 : Blo 1559477 1974127 := bstep (se 1 (by rfl) ⟨1480595, by rfl⟩ : syracuseStep 1974127 = 2961191) B2961191
theorem B9486395 : Blo 1559477 9486395 := bstep (se 1 (by rfl) ⟨7114796, by rfl⟩ : syracuseStep 9486395 = 14229593) B14229593
theorem B5268023 : Blo 1559477 5268023 := bstep (se 1 (by rfl) ⟨3951017, by rfl⟩ : syracuseStep 5268023 = 7902035) B7902035
theorem B67486445 : Blo 1559477 67486445 := bstep (se 3 (by rfl) ⟨12653708, by rfl⟩ : syracuseStep 67486445 = 25307417) B25307417
theorem B10003247 : Blo 1559477 10003247 := bstep (se 1 (by rfl) ⟨7502435, by rfl⟩ : syracuseStep 10003247 = 15004871) B15004871
theorem B7496687 : Blo 1559477 7496687 := bstep (se 1 (by rfl) ⟨5622515, by rfl⟩ : syracuseStep 7496687 = 11245031) B11245031
theorem B3949631 : Blo 1559477 3949631 := bstep (se 1 (by rfl) ⟨2962223, by rfl⟩ : syracuseStep 3949631 = 5924447) B5924447
theorem B5620843 : Blo 1559477 5620843 := bstep (se 1 (by rfl) ⟨4215632, by rfl⟩ : syracuseStep 5620843 = 8431265) B8431265
theorem B5923961 : Blo 1559477 5923961 := bstep (se 2 (by rfl) ⟨2221485, by rfl⟩ : syracuseStep 5923961 = 4442971) B4442971
theorem B1975519 : Blo 1559477 1975519 := bstep (se 1 (by rfl) ⟨1481639, by rfl⟩ : syracuseStep 1975519 = 2963279) B2963279
theorem B3949843 : Blo 1559477 3949843 := bstep (se 1 (by rfl) ⟨2962382, by rfl⟩ : syracuseStep 3949843 = 5924765) B5924765
theorem B5268833 : Blo 1559477 5268833 := bstep (se 2 (by rfl) ⟨1975812, by rfl⟩ : syracuseStep 5268833 = 3951625) B3951625
theorem B4998959 : Blo 1559477 4998959 := bstep (se 1 (by rfl) ⟨3749219, by rfl⟩ : syracuseStep 4998959 = 7498439) B7498439
theorem B18270031 : Blo 1559477 18270031 := bstep (se 1 (by rfl) ⟨13702523, by rfl⟩ : syracuseStep 18270031 = 27405047) B27405047
theorem B44984267 : Blo 1559477 44984267 := bstep (se 1 (by rfl) ⟨33738200, by rfl⟩ : syracuseStep 44984267 = 67476401) B67476401
theorem B5269535 : Blo 1559477 5269535 := bstep (se 1 (by rfl) ⟨3952151, by rfl⟩ : syracuseStep 5269535 = 7904303) B7904303
theorem B2631899 : Blo 1559477 2631899 := bstep (se 1 (by rfl) ⟨1973924, by rfl⟩ : syracuseStep 2631899 = 3947849) B3947849
theorem B2500831 : Blo 1559477 2500831 := bstep (se 1 (by rfl) ⟨1875623, by rfl⟩ : syracuseStep 2500831 = 3751247) B3751247
theorem B6007081 : Blo 1559477 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B43264313 : Blo 1559477 43264313 := bstep (se 2 (by rfl) ⟨16224117, by rfl⟩ : syracuseStep 43264313 = 32448235) B32448235
theorem B2501023 : Blo 1559477 2501023 := bstep (se 1 (by rfl) ⟨1875767, by rfl⟩ : syracuseStep 2501023 = 3751535) B3751535
theorem B13322657 : Blo 1559477 13322657 := bstep (se 2 (by rfl) ⟨4995996, by rfl⟩ : syracuseStep 13322657 = 9991993) B9991993
theorem B9996709 : Blo 1559477 9996709 := bstep (se 4 (by rfl) ⟨937191, by rfl⟩ : syracuseStep 9996709 = 1874383) B1874383
theorem B2632169 : Blo 1559477 2632169 := bstep (se 2 (by rfl) ⟨987063, by rfl⟩ : syracuseStep 2632169 = 1974127) B1974127
theorem B4442617 : Blo 1559477 4442617 := bstep (se 2 (by rfl) ⟨1665981, by rfl⟩ : syracuseStep 4442617 = 3331963) B3331963
theorem B7899929 : Blo 1559477 7899929 := bstep (se 2 (by rfl) ⟨2962473, by rfl⟩ : syracuseStep 7899929 = 5924947) B5924947
theorem B8121377 : Blo 1559477 8121377 := bstep (se 2 (by rfl) ⟨3045516, by rfl⟩ : syracuseStep 8121377 = 6091033) B6091033
theorem B300297287 : Blo 1559477 300297287 := bstep (se 1 (by rfl) ⟨225222965, by rfl⟩ : syracuseStep 300297287 = 450445931) B450445931
theorem B1559719 : Blo 1559477 1559719 := bstep (se 1 (by rfl) ⟨1169789, by rfl⟩ : syracuseStep 1559719 = 2339579) B2339579
theorem B1756327 : Blo 1559477 1756327 := bstep (se 1 (by rfl) ⟨1317245, by rfl⟩ : syracuseStep 1756327 = 2634491) B2634491
theorem B2632891 : Blo 1559477 2632891 := bstep (se 1 (by rfl) ⟨1974668, by rfl⟩ : syracuseStep 2632891 = 3949337) B3949337
theorem B1666255 : Blo 1559477 1666255 := bstep (se 1 (by rfl) ⟨1249691, by rfl⟩ : syracuseStep 1666255 = 2499383) B2499383
theorem B6663379 : Blo 1559477 6663379 := bstep (se 1 (by rfl) ⟨4997534, by rfl⟩ : syracuseStep 6663379 = 9995069) B9995069
theorem B36056335 : Blo 1559477 36056335 := bstep (se 1 (by rfl) ⟨27042251, by rfl⟩ : syracuseStep 36056335 = 54084503) B54084503
theorem B1560015 : Blo 1559477 1560015 := bstep (se 1 (by rfl) ⟨1170011, by rfl⟩ : syracuseStep 1560015 = 2340023) B2340023
theorem B32050727 : Blo 1559477 32050727 := bstep (se 1 (by rfl) ⟨24038045, by rfl⟩ : syracuseStep 32050727 = 48076091) B48076091
theorem B1560175 : Blo 1559477 1560175 := bstep (se 1 (by rfl) ⟨1170131, by rfl⟩ : syracuseStep 1560175 = 2340263) B2340263
theorem B5000815 : Blo 1559477 5000815 := bstep (se 1 (by rfl) ⟨3750611, by rfl⟩ : syracuseStep 5000815 = 7501223) B7501223
theorem B1560295 : Blo 1559477 1560295 := bstep (se 1 (by rfl) ⟨1170221, by rfl⟩ : syracuseStep 1560295 = 2340443) B2340443
theorem B2371439 : Blo 1559477 2371439 := bstep (se 1 (by rfl) ⟨1778579, by rfl⟩ : syracuseStep 2371439 = 3557159) B3557159
theorem B4444075 : Blo 1559477 4444075 := bstep (se 1 (by rfl) ⟨3333056, by rfl⟩ : syracuseStep 4444075 = 6666113) B6666113
theorem B3510251 : Blo 1559477 3510251 := bstep (se 1 (by rfl) ⟨2632688, by rfl⟩ : syracuseStep 3510251 = 5265377) B5265377
theorem B1560603 : Blo 1559477 1560603 := bstep (se 1 (by rfl) ⟨1170452, by rfl⟩ : syracuseStep 1560603 = 2340905) B2340905
theorem B1560623 : Blo 1559477 1560623 := bstep (se 1 (by rfl) ⟨1170467, by rfl⟩ : syracuseStep 1560623 = 2340935) B2340935
theorem B2109503 : Blo 1559477 2109503 := bstep (se 1 (by rfl) ⟨1582127, by rfl⟩ : syracuseStep 2109503 = 3164255) B3164255
theorem B2633951 : Blo 1559477 2633951 := bstep (se 1 (by rfl) ⟨1975463, by rfl⟩ : syracuseStep 2633951 = 3950927) B3950927
theorem B162222365 : Blo 1559477 162222365 := bstep (se 3 (by rfl) ⟨30416693, by rfl⟩ : syracuseStep 162222365 = 60833387) B60833387
theorem B4444463 : Blo 1559477 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B1560879 : Blo 1559477 1560879 := bstep (se 1 (by rfl) ⟨1170659, by rfl⟩ : syracuseStep 1560879 = 2341319) B2341319
theorem B7115195 : Blo 1559477 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B1561023 : Blo 1559477 1561023 := bstep (se 1 (by rfl) ⟨1170767, by rfl⟩ : syracuseStep 1561023 = 2341535) B2341535
theorem B4444703 : Blo 1559477 4444703 := bstep (se 1 (by rfl) ⟨3333527, by rfl⟩ : syracuseStep 4444703 = 6667055) B6667055
theorem B1561119 : Blo 1559477 1561119 := bstep (se 1 (by rfl) ⟨1170839, by rfl⟩ : syracuseStep 1561119 = 2341679) B2341679
theorem B1561199 : Blo 1559477 1561199 := bstep (se 1 (by rfl) ⟨1170899, by rfl⟩ : syracuseStep 1561199 = 2341799) B2341799
theorem B22499977 : Blo 1559477 22499977 := bstep (se 2 (by rfl) ⟨8437491, by rfl⟩ : syracuseStep 22499977 = 16874983) B16874983
theorem B2339495 : Blo 1559477 2339495 := bstep (se 1 (by rfl) ⟨1754621, by rfl⟩ : syracuseStep 2339495 = 3509243) B3509243
theorem B234181313 : Blo 1559477 234181313 := bstep (se 2 (by rfl) ⟨87817992, by rfl⟩ : syracuseStep 234181313 = 175635985) B175635985
theorem B1561319 : Blo 1559477 1561319 := bstep (se 1 (by rfl) ⟨1170989, by rfl⟩ : syracuseStep 1561319 = 2341979) B2341979
theorem B5337875 : Blo 1559477 5337875 := bstep (se 1 (by rfl) ⟨4003406, by rfl⟩ : syracuseStep 5337875 = 8006813) B8006813
theorem B2339615 : Blo 1559477 2339615 := bstep (se 1 (by rfl) ⟨1754711, by rfl⟩ : syracuseStep 2339615 = 3509423) B3509423
theorem B2339639 : Blo 1559477 2339639 := bstep (se 1 (by rfl) ⟨1754729, by rfl⟩ : syracuseStep 2339639 = 3509459) B3509459
theorem B91247471 : Blo 1559477 91247471 := bstep (se 1 (by rfl) ⟨68435603, by rfl⟩ : syracuseStep 91247471 = 136871207) B136871207
theorem B2339753 : Blo 1559477 2339753 := bstep (se 2 (by rfl) ⟨877407, by rfl⟩ : syracuseStep 2339753 = 1754815) B1754815
theorem B2339819 : Blo 1559477 2339819 := bstep (se 1 (by rfl) ⟨1754864, by rfl⟩ : syracuseStep 2339819 = 3509729) B3509729
theorem B11244683 : Blo 1559477 11244683 := bstep (se 1 (by rfl) ⟨8433512, by rfl⟩ : syracuseStep 11244683 = 16867025) B16867025
theorem B37942445 : Blo 1559477 37942445 := bstep (se 3 (by rfl) ⟨7114208, by rfl⟩ : syracuseStep 37942445 = 14228417) B14228417
theorem B2340095 : Blo 1559477 2340095 := bstep (se 1 (by rfl) ⟨1755071, by rfl⟩ : syracuseStep 2340095 = 3510143) B3510143
theorem B2340137 : Blo 1559477 2340137 := bstep (se 2 (by rfl) ⟨877551, by rfl⟩ : syracuseStep 2340137 = 1755103) B1755103
theorem B4003283 : Blo 1559477 4003283 := bstep (se 1 (by rfl) ⟨3002462, by rfl⟩ : syracuseStep 4003283 = 6004925) B6004925
theorem B16864777 : Blo 1559477 16864777 := bstep (se 2 (by rfl) ⟨6324291, by rfl⟩ : syracuseStep 16864777 = 12648583) B12648583
theorem B18970301 : Blo 1559477 18970301 := bstep (se 3 (by rfl) ⟨3556931, by rfl⟩ : syracuseStep 18970301 = 7113863) B7113863
theorem B7903007 : Blo 1559477 7903007 := bstep (se 1 (by rfl) ⟨5927255, by rfl⟩ : syracuseStep 7903007 = 11854511) B11854511
theorem B2340731 : Blo 1559477 2340731 := bstep (se 1 (by rfl) ⟨1755548, by rfl⟩ : syracuseStep 2340731 = 3511097) B3511097
theorem B26646407 : Blo 1559477 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B2340767 : Blo 1559477 2340767 := bstep (se 1 (by rfl) ⟨1755575, by rfl⟩ : syracuseStep 2340767 = 3511151) B3511151
theorem B7600061 : Blo 1559477 7600061 := bstep (se 3 (by rfl) ⟨1425011, by rfl⟩ : syracuseStep 7600061 = 2850023) B2850023
theorem B13326281 : Blo 1559477 13326281 := bstep (se 2 (by rfl) ⟨4997355, by rfl⟩ : syracuseStep 13326281 = 9994711) B9994711
theorem B2340971 : Blo 1559477 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B2341001 : Blo 1559477 2341001 := bstep (se 2 (by rfl) ⟨877875, by rfl⟩ : syracuseStep 2341001 = 1755751) B1755751
theorem B6666455 : Blo 1559477 6666455 := bstep (se 1 (by rfl) ⟨4999841, by rfl⟩ : syracuseStep 6666455 = 9999683) B9999683
theorem B134986013 : Blo 1559477 134986013 := bstep (se 3 (by rfl) ⟨25309877, by rfl⟩ : syracuseStep 134986013 = 50619755) B50619755
theorem B2341151 : Blo 1559477 2341151 := bstep (se 1 (by rfl) ⟨1755863, by rfl⟩ : syracuseStep 2341151 = 3511727) B3511727
theorem B42686777 : Blo 1559477 42686777 := bstep (se 2 (by rfl) ⟨16007541, by rfl⟩ : syracuseStep 42686777 = 32015083) B32015083
theorem B5266079 : Blo 1559477 5266079 := bstep (se 1 (by rfl) ⟨3949559, by rfl⟩ : syracuseStep 5266079 = 7899119) B7899119
theorem B7903979 : Blo 1559477 7903979 := bstep (se 1 (by rfl) ⟨5927984, by rfl⟩ : syracuseStep 7903979 = 11855969) B11855969
theorem B2341823 : Blo 1559477 2341823 := bstep (se 1 (by rfl) ⟨1756367, by rfl⟩ : syracuseStep 2341823 = 3512735) B3512735
theorem B2341871 : Blo 1559477 2341871 := bstep (se 1 (by rfl) ⟨1756403, by rfl⟩ : syracuseStep 2341871 = 3512807) B3512807
theorem B5627015 : Blo 1559477 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B2342057 : Blo 1559477 2342057 := bstep (se 2 (by rfl) ⟨878271, by rfl⟩ : syracuseStep 2342057 = 1756543) B1756543
theorem B18988253 : Blo 1559477 18988253 := bstep (se 3 (by rfl) ⟨3560297, by rfl⟩ : syracuseStep 18988253 = 7120595) B7120595
theorem B5922017 : Blo 1559477 5922017 := bstep (se 2 (by rfl) ⟨2220756, by rfl⟩ : syracuseStep 5922017 = 4441513) B4441513
theorem B3333467 : Blo 1559477 3333467 := bstep (se 1 (by rfl) ⟨2500100, by rfl⟩ : syracuseStep 3333467 = 5000201) B5000201
theorem B7896527 : Blo 1559477 7896527 := bstep (se 1 (by rfl) ⟨5922395, by rfl⟩ : syracuseStep 7896527 = 11844791) B11844791
theorem B3948385 : Blo 1559477 3948385 := bstep (se 2 (by rfl) ⟨1480644, by rfl⟩ : syracuseStep 3948385 = 2961289) B2961289
theorem B6324263 : Blo 1559477 6324263 := bstep (se 1 (by rfl) ⟨4743197, by rfl⟩ : syracuseStep 6324263 = 9486395) B9486395
theorem B4743463 : Blo 1559477 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B3334441 : Blo 1559477 3334441 := bstep (se 2 (by rfl) ⟨1250415, by rfl⟩ : syracuseStep 3334441 = 2500831) B2500831
theorem B44990963 : Blo 1559477 44990963 := bstep (se 1 (by rfl) ⟨33743222, by rfl⟩ : syracuseStep 44990963 = 67486445) B67486445
theorem B6668831 : Blo 1559477 6668831 := bstep (se 1 (by rfl) ⟨5001623, by rfl⟩ : syracuseStep 6668831 = 10003247) B10003247
theorem B3334697 : Blo 1559477 3334697 := bstep (se 2 (by rfl) ⟨1250511, by rfl⟩ : syracuseStep 3334697 = 2501023) B2501023
theorem B13328945 : Blo 1559477 13328945 := bstep (se 2 (by rfl) ⟨4998354, by rfl⟩ : syracuseStep 13328945 = 9996709) B9996709
theorem B4997791 : Blo 1559477 4997791 := bstep (se 1 (by rfl) ⟨3748343, by rfl⟩ : syracuseStep 4997791 = 7496687) B7496687
theorem B5923489 : Blo 1559477 5923489 := bstep (se 2 (by rfl) ⟨2221308, by rfl⟩ : syracuseStep 5923489 = 4442617) B4442617
theorem B3949307 : Blo 1559477 3949307 := bstep (se 1 (by rfl) ⟨2961980, by rfl⟩ : syracuseStep 3949307 = 5923961) B5923961
theorem B29999969 : Blo 1559477 29999969 := bstep (se 2 (by rfl) ⟨11249988, by rfl⟩ : syracuseStep 29999969 = 22499977) B22499977
theorem B5268671 : Blo 1559477 5268671 := bstep (se 1 (by rfl) ⟨3951503, by rfl⟩ : syracuseStep 5268671 = 7903007) B7903007
theorem B10675421 : Blo 1559477 10675421 := bstep (se 3 (by rfl) ⟨2001641, by rfl⟩ : syracuseStep 10675421 = 4003283) B4003283
theorem B1754599 : Blo 1559477 1754599 := bstep (se 1 (by rfl) ⟨1315949, by rfl⟩ : syracuseStep 1754599 = 2631899) B2631899
theorem B89990675 : Blo 1559477 89990675 := bstep (se 1 (by rfl) ⟨67493006, by rfl⟩ : syracuseStep 89990675 = 134986013) B134986013
theorem B2221673 : Blo 1559477 2221673 := bstep (se 2 (by rfl) ⟨833127, by rfl⟩ : syracuseStep 2221673 = 1666255) B1666255
theorem B8881771 : Blo 1559477 8881771 := bstep (se 1 (by rfl) ⟨6661328, by rfl⟩ : syracuseStep 8881771 = 13322657) B13322657
theorem B1754779 : Blo 1559477 1754779 := bstep (se 1 (by rfl) ⟨1316084, by rfl⟩ : syracuseStep 1754779 = 2632169) B2632169
theorem B5269319 : Blo 1559477 5269319 := bstep (se 1 (by rfl) ⟨3951989, by rfl⟩ : syracuseStep 5269319 = 7903979) B7903979
theorem B200198191 : Blo 1559477 200198191 := bstep (se 1 (by rfl) ⟨150148643, by rfl⟩ : syracuseStep 200198191 = 300297287) B300297287
theorem B12658835 : Blo 1559477 12658835 := bstep (se 1 (by rfl) ⟨9494126, by rfl⟩ : syracuseStep 12658835 = 18988253) B18988253
theorem B2222311 : Blo 1559477 2222311 := bstep (se 1 (by rfl) ⟨1666733, by rfl⟩ : syracuseStep 2222311 = 3333467) B3333467
theorem B21367151 : Blo 1559477 21367151 := bstep (se 1 (by rfl) ⟨16025363, by rfl⟩ : syracuseStep 21367151 = 32050727) B32050727
theorem B5925433 : Blo 1559477 5925433 := bstep (se 2 (by rfl) ⟨2222037, by rfl⟩ : syracuseStep 5925433 = 4444075) B4444075
theorem B1755967 : Blo 1559477 1755967 := bstep (se 1 (by rfl) ⟨1316975, by rfl⟩ : syracuseStep 1755967 = 2633951) B2633951
theorem B29985821 : Blo 1559477 29985821 := bstep (se 3 (by rfl) ⟨5622341, by rfl⟩ : syracuseStep 29985821 = 11244683) B11244683
theorem B1559663 : Blo 1559477 1559663 := bstep (se 1 (by rfl) ⟨1169747, by rfl⟩ : syracuseStep 1559663 = 2339495) B2339495
theorem B3558583 : Blo 1559477 3558583 := bstep (se 1 (by rfl) ⟨2668937, by rfl⟩ : syracuseStep 3558583 = 5337875) B5337875
theorem B1559743 : Blo 1559477 1559743 := bstep (se 1 (by rfl) ⟨1169807, by rfl⟩ : syracuseStep 1559743 = 2339615) B2339615
theorem B1559759 : Blo 1559477 1559759 := bstep (se 1 (by rfl) ⟨1169819, by rfl⟩ : syracuseStep 1559759 = 2339639) B2339639
theorem B1559835 : Blo 1559477 1559835 := bstep (se 1 (by rfl) ⟨1169876, by rfl⟩ : syracuseStep 1559835 = 2339753) B2339753
theorem B1559879 : Blo 1559477 1559879 := bstep (se 1 (by rfl) ⟨1169909, by rfl⟩ : syracuseStep 1559879 = 2339819) B2339819
theorem B2633087 : Blo 1559477 2633087 := bstep (se 1 (by rfl) ⟨1974815, by rfl⟩ : syracuseStep 2633087 = 3949631) B3949631
theorem B113831405 : Blo 1559477 113831405 := bstep (se 3 (by rfl) ⟨21343388, by rfl⟩ : syracuseStep 113831405 = 42686777) B42686777
theorem B1560063 : Blo 1559477 1560063 := bstep (se 1 (by rfl) ⟨1170047, by rfl⟩ : syracuseStep 1560063 = 2340095) B2340095
theorem B1560091 : Blo 1559477 1560091 := bstep (se 1 (by rfl) ⟨1170068, by rfl⟩ : syracuseStep 1560091 = 2340137) B2340137
theorem B1560487 : Blo 1559477 1560487 := bstep (se 1 (by rfl) ⟨1170365, by rfl⟩ : syracuseStep 1560487 = 2340731) B2340731
theorem B17764271 : Blo 1559477 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B1560511 : Blo 1559477 1560511 := bstep (se 1 (by rfl) ⟨1170383, by rfl⟩ : syracuseStep 1560511 = 2340767) B2340767
theorem B5066707 : Blo 1559477 5066707 := bstep (se 1 (by rfl) ⟨3800030, by rfl⟩ : syracuseStep 5066707 = 7600061) B7600061
theorem B8884187 : Blo 1559477 8884187 := bstep (se 1 (by rfl) ⟨6663140, by rfl⟩ : syracuseStep 8884187 = 13326281) B13326281
theorem B1560647 : Blo 1559477 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B1560667 : Blo 1559477 1560667 := bstep (se 1 (by rfl) ⟨1170500, by rfl⟩ : syracuseStep 1560667 = 2341001) B2341001
theorem B4444303 : Blo 1559477 4444303 := bstep (se 1 (by rfl) ⟨3333227, by rfl⟩ : syracuseStep 4444303 = 6666455) B6666455
theorem B1560767 : Blo 1559477 1560767 := bstep (se 1 (by rfl) ⟨1170575, by rfl⟩ : syracuseStep 1560767 = 2341151) B2341151
theorem B3510521 : Blo 1559477 3510521 := bstep (se 2 (by rfl) ⟨1316445, by rfl⟩ : syracuseStep 3510521 = 2632891) B2632891
theorem B8884505 : Blo 1559477 8884505 := bstep (se 2 (by rfl) ⟨3331689, by rfl⟩ : syracuseStep 8884505 = 6663379) B6663379
theorem B2634025 : Blo 1559477 2634025 := bstep (se 2 (by rfl) ⟨987759, by rfl⟩ : syracuseStep 2634025 = 1975519) B1975519
theorem B48075113 : Blo 1559477 48075113 := bstep (se 2 (by rfl) ⟨18028167, by rfl⟩ : syracuseStep 48075113 = 36056335) B36056335
theorem B3510719 : Blo 1559477 3510719 := bstep (se 1 (by rfl) ⟨2633039, by rfl⟩ : syracuseStep 3510719 = 5266079) B5266079
theorem B1561215 : Blo 1559477 1561215 := bstep (se 1 (by rfl) ⟨1170911, by rfl⟩ : syracuseStep 1561215 = 2341823) B2341823
theorem B1561247 : Blo 1559477 1561247 := bstep (se 1 (by rfl) ⟨1170935, by rfl⟩ : syracuseStep 1561247 = 2341871) B2341871
theorem B1561371 : Blo 1559477 1561371 := bstep (se 1 (by rfl) ⟨1171028, by rfl⟩ : syracuseStep 1561371 = 2342057) B2342057
theorem B5264351 : Blo 1559477 5264351 := bstep (se 1 (by rfl) ⟨3948263, by rfl⟩ : syracuseStep 5264351 = 7896527) B7896527
theorem B24360041 : Blo 1559477 24360041 := bstep (se 2 (by rfl) ⟨9135015, by rfl⟩ : syracuseStep 24360041 = 18270031) B18270031
theorem B5264513 : Blo 1559477 5264513 := bstep (se 2 (by rfl) ⟨1974192, by rfl⟩ : syracuseStep 5264513 = 3948385) B3948385
theorem B2340167 : Blo 1559477 2340167 := bstep (se 1 (by rfl) ⟨1755125, by rfl⟩ : syracuseStep 2340167 = 3510251) B3510251
theorem B5625341 : Blo 1559477 5625341 := bstep (se 3 (by rfl) ⟨1054751, by rfl⟩ : syracuseStep 5625341 = 2109503) B2109503
theorem B108148243 : Blo 1559477 108148243 := bstep (se 1 (by rfl) ⟨81111182, by rfl⟩ : syracuseStep 108148243 = 162222365) B162222365
theorem B2962975 : Blo 1559477 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B2963135 : Blo 1559477 2963135 := bstep (se 1 (by rfl) ⟨2222351, by rfl⟩ : syracuseStep 2963135 = 4444703) B4444703
theorem B3512015 : Blo 1559477 3512015 := bstep (se 1 (by rfl) ⟨2634011, by rfl⟩ : syracuseStep 3512015 = 5268023) B5268023
theorem B8009441 : Blo 1559477 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B156120875 : Blo 1559477 156120875 := bstep (se 1 (by rfl) ⟨117090656, by rfl⟩ : syracuseStep 156120875 = 234181313) B234181313
theorem B60831647 : Blo 1559477 60831647 := bstep (se 1 (by rfl) ⟨45623735, by rfl⟩ : syracuseStep 60831647 = 91247471) B91247471
theorem B25294963 : Blo 1559477 25294963 := bstep (se 1 (by rfl) ⟨18971222, by rfl⟩ : syracuseStep 25294963 = 37942445) B37942445
theorem B3512555 : Blo 1559477 3512555 := bstep (se 1 (by rfl) ⟨2634416, by rfl⟩ : syracuseStep 3512555 = 5268833) B5268833
theorem B12646867 : Blo 1559477 12646867 := bstep (se 1 (by rfl) ⟨9485150, by rfl⟩ : syracuseStep 12646867 = 18970301) B18970301
theorem B3332639 : Blo 1559477 3332639 := bstep (se 1 (by rfl) ⟨2499479, by rfl⟩ : syracuseStep 3332639 = 4998959) B4998959
theorem B29989511 : Blo 1559477 29989511 := bstep (se 1 (by rfl) ⟨22492133, by rfl⟩ : syracuseStep 29989511 = 44984267) B44984267
theorem B3513023 : Blo 1559477 3513023 := bstep (se 1 (by rfl) ⟨2634767, by rfl⟩ : syracuseStep 3513023 = 5269535) B5269535
theorem B7494457 : Blo 1559477 7494457 := bstep (se 2 (by rfl) ⟨2810421, by rfl⟩ : syracuseStep 7494457 = 5620843) B5620843
theorem B28842875 : Blo 1559477 28842875 := bstep (se 1 (by rfl) ⟨21632156, by rfl⟩ : syracuseStep 28842875 = 43264313) B43264313
theorem B2341769 : Blo 1559477 2341769 := bstep (se 2 (by rfl) ⟨878163, by rfl⟩ : syracuseStep 2341769 = 1756327) B1756327
theorem B5266457 : Blo 1559477 5266457 := bstep (se 2 (by rfl) ⟨1974921, by rfl⟩ : syracuseStep 5266457 = 3949843) B3949843
theorem B5266619 : Blo 1559477 5266619 := bstep (se 1 (by rfl) ⟨3949964, by rfl⟩ : syracuseStep 5266619 = 7899929) B7899929
theorem B22486369 : Blo 1559477 22486369 := bstep (se 2 (by rfl) ⟨8432388, by rfl⟩ : syracuseStep 22486369 = 16864777) B16864777
theorem B5414251 : Blo 1559477 5414251 := bstep (se 1 (by rfl) ⟨4060688, by rfl⟩ : syracuseStep 5414251 = 8121377) B8121377
theorem B3751343 : Blo 1559477 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B6667753 : Blo 1559477 6667753 := bstep (se 2 (by rfl) ⟨2500407, by rfl⟩ : syracuseStep 6667753 = 5000815) B5000815
theorem B3948011 : Blo 1559477 3948011 := bstep (se 1 (by rfl) ⟨2961008, by rfl⟩ : syracuseStep 3948011 = 5922017) B5922017
theorem B6323837 : Blo 1559477 6323837 := bstep (se 3 (by rfl) ⟨1185719, by rfl⟩ : syracuseStep 6323837 = 2371439) B2371439
theorem B33726617 : Blo 1559477 33726617 := bstep (se 2 (by rfl) ⟨12647481, by rfl⟩ : syracuseStep 33726617 = 25294963) B25294963
theorem B5923003 : Blo 1559477 5923003 := bstep (se 1 (by rfl) ⟨4442252, by rfl⟩ : syracuseStep 5923003 = 8884505) B8884505
theorem B6324617 : Blo 1559477 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B7897985 : Blo 1559477 7897985 := bstep (se 2 (by rfl) ⟨2961744, by rfl⟩ : syracuseStep 7897985 = 5923489) B5923489
theorem B1975423 : Blo 1559477 1975423 := bstep (se 1 (by rfl) ⟨1481567, by rfl⟩ : syracuseStep 1975423 = 2963135) B2963135
theorem B104080583 : Blo 1559477 104080583 := bstep (se 1 (by rfl) ⟨78060437, by rfl⟩ : syracuseStep 104080583 = 156120875) B156120875
theorem B8439223 : Blo 1559477 8439223 := bstep (se 1 (by rfl) ⟨6329417, by rfl⟩ : syracuseStep 8439223 = 12658835) B12658835
theorem B4744777 : Blo 1559477 4744777 := bstep (se 2 (by rfl) ⟨1779291, by rfl⟩ : syracuseStep 4744777 = 3558583) B3558583
theorem B5924461 : Blo 1559477 5924461 := bstep (se 3 (by rfl) ⟨1110836, by rfl⟩ : syracuseStep 5924461 = 2221673) B2221673
theorem B2221759 : Blo 1559477 2221759 := bstep (se 1 (by rfl) ⟨1666319, by rfl⟩ : syracuseStep 2221759 = 3332639) B3332639
theorem B7219001 : Blo 1559477 7219001 := bstep (se 2 (by rfl) ⟨2707125, by rfl⟩ : syracuseStep 7219001 = 5414251) B5414251
theorem B19228583 : Blo 1559477 19228583 := bstep (se 1 (by rfl) ⟨14421437, by rfl⟩ : syracuseStep 19228583 = 28842875) B28842875
theorem B8890337 : Blo 1559477 8890337 := bstep (se 2 (by rfl) ⟨3333876, by rfl⟩ : syracuseStep 8890337 = 6667753) B6667753
theorem B19990547 : Blo 1559477 19990547 := bstep (se 1 (by rfl) ⟨14992910, by rfl⟩ : syracuseStep 19990547 = 29985821) B29985821
theorem B144197657 : Blo 1559477 144197657 := bstep (se 2 (by rfl) ⟨54074121, by rfl⟩ : syracuseStep 144197657 = 108148243) B108148243
theorem B3950633 : Blo 1559477 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B1755391 : Blo 1559477 1755391 := bstep (se 1 (by rfl) ⟨1316543, by rfl⟩ : syracuseStep 1755391 = 2633087) B2633087
theorem B2500895 : Blo 1559477 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B2632007 : Blo 1559477 2632007 := bstep (se 1 (by rfl) ⟨1974005, by rfl⟩ : syracuseStep 2632007 = 3948011) B3948011
theorem B266930921 : Blo 1559477 266930921 := bstep (se 2 (by rfl) ⟨100099095, by rfl⟩ : syracuseStep 266930921 = 200198191) B200198191
theorem B5925737 : Blo 1559477 5925737 := bstep (se 2 (by rfl) ⟨2222151, by rfl⟩ : syracuseStep 5925737 = 4444303) B4444303
theorem B32050075 : Blo 1559477 32050075 := bstep (se 1 (by rfl) ⟨24037556, by rfl⟩ : syracuseStep 32050075 = 48075113) B48075113
theorem B29993975 : Blo 1559477 29993975 := bstep (se 1 (by rfl) ⟨22495481, by rfl⟩ : syracuseStep 29993975 = 44990963) B44990963
theorem B2223131 : Blo 1559477 2223131 := bstep (se 1 (by rfl) ⟨1667348, by rfl⟩ : syracuseStep 2223131 = 3334697) B3334697
theorem B2632871 : Blo 1559477 2632871 := bstep (se 1 (by rfl) ⟨1974653, by rfl⟩ : syracuseStep 2632871 = 3949307) B3949307
theorem B19999979 : Blo 1559477 19999979 := bstep (se 1 (by rfl) ⟨14999984, by rfl⟩ : syracuseStep 19999979 = 29999969) B29999969
theorem B16862489 : Blo 1559477 16862489 := bstep (se 2 (by rfl) ⟨6323433, by rfl⟩ : syracuseStep 16862489 = 12646867) B12646867
theorem B3509567 : Blo 1559477 3509567 := bstep (se 1 (by rfl) ⟨2632175, by rfl⟩ : syracuseStep 3509567 = 5264351) B5264351
theorem B16240027 : Blo 1559477 16240027 := bstep (se 1 (by rfl) ⟨12180020, by rfl⟩ : syracuseStep 16240027 = 24360041) B24360041
theorem B7900577 : Blo 1559477 7900577 := bstep (se 2 (by rfl) ⟨2962716, by rfl⟩ : syracuseStep 7900577 = 5925433) B5925433
theorem B3509675 : Blo 1559477 3509675 := bstep (se 1 (by rfl) ⟨2632256, by rfl⟩ : syracuseStep 3509675 = 5264513) B5264513
theorem B6663721 : Blo 1559477 6663721 := bstep (se 2 (by rfl) ⟨2498895, by rfl⟩ : syracuseStep 6663721 = 4997791) B4997791
theorem B1560111 : Blo 1559477 1560111 := bstep (se 1 (by rfl) ⟨1170083, by rfl⟩ : syracuseStep 1560111 = 2340167) B2340167
theorem B59993783 : Blo 1559477 59993783 := bstep (se 1 (by rfl) ⟨44995337, by rfl⟩ : syracuseStep 59993783 = 89990675) B89990675
theorem B40554431 : Blo 1559477 40554431 := bstep (se 1 (by rfl) ⟨30415823, by rfl⟩ : syracuseStep 40554431 = 60831647) B60831647
theorem B16863565 : Blo 1559477 16863565 := bstep (se 3 (by rfl) ⟨3161918, by rfl⟩ : syracuseStep 16863565 = 6323837) B6323837
theorem B19993007 : Blo 1559477 19993007 := bstep (se 1 (by rfl) ⟨14994755, by rfl⟩ : syracuseStep 19993007 = 29989511) B29989511
theorem B1561179 : Blo 1559477 1561179 := bstep (se 1 (by rfl) ⟨1170884, by rfl⟩ : syracuseStep 1561179 = 2341769) B2341769
theorem B2339465 : Blo 1559477 2339465 := bstep (se 2 (by rfl) ⟨877299, by rfl⟩ : syracuseStep 2339465 = 1754599) B1754599
theorem B3510971 : Blo 1559477 3510971 := bstep (se 1 (by rfl) ⟨2633228, by rfl⟩ : syracuseStep 3510971 = 5266457) B5266457
theorem B3511079 : Blo 1559477 3511079 := bstep (se 1 (by rfl) ⟨2633309, by rfl⟩ : syracuseStep 3511079 = 5266619) B5266619
theorem B11842361 : Blo 1559477 11842361 := bstep (se 2 (by rfl) ⟨4440885, by rfl⟩ : syracuseStep 11842361 = 8881771) B8881771
theorem B2339705 : Blo 1559477 2339705 := bstep (se 2 (by rfl) ⟨877389, by rfl⟩ : syracuseStep 2339705 = 1754779) B1754779
theorem B75887603 : Blo 1559477 75887603 := bstep (se 1 (by rfl) ⟨56915702, by rfl⟩ : syracuseStep 75887603 = 113831405) B113831405
theorem B6755609 : Blo 1559477 6755609 := bstep (se 2 (by rfl) ⟨2533353, by rfl⟩ : syracuseStep 6755609 = 5066707) B5066707
theorem B11842847 : Blo 1559477 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B4216175 : Blo 1559477 4216175 := bstep (se 1 (by rfl) ⟨3162131, by rfl⟩ : syracuseStep 4216175 = 6324263) B6324263
theorem B2340347 : Blo 1559477 2340347 := bstep (se 1 (by rfl) ⟨1755260, by rfl⟩ : syracuseStep 2340347 = 3510521) B3510521
theorem B2340479 : Blo 1559477 2340479 := bstep (se 1 (by rfl) ⟨1755359, by rfl⟩ : syracuseStep 2340479 = 3510719) B3510719
theorem B2963081 : Blo 1559477 2963081 := bstep (se 2 (by rfl) ⟨1111155, by rfl⟩ : syracuseStep 2963081 = 2222311) B2222311
theorem B4445887 : Blo 1559477 4445887 := bstep (se 1 (by rfl) ⟨3334415, by rfl⟩ : syracuseStep 4445887 = 6668831) B6668831
theorem B8885963 : Blo 1559477 8885963 := bstep (se 1 (by rfl) ⟨6664472, by rfl⟩ : syracuseStep 8885963 = 13328945) B13328945
theorem B3512033 : Blo 1559477 3512033 := bstep (se 2 (by rfl) ⟨1317012, by rfl⟩ : syracuseStep 3512033 = 2634025) B2634025
theorem B4445921 : Blo 1559477 4445921 := bstep (se 2 (by rfl) ⟨1667220, by rfl⟩ : syracuseStep 4445921 = 3334441) B3334441
theorem B3512447 : Blo 1559477 3512447 := bstep (se 1 (by rfl) ⟨2634335, by rfl⟩ : syracuseStep 3512447 = 5268671) B5268671
theorem B7116947 : Blo 1559477 7116947 := bstep (se 1 (by rfl) ⟨5337710, by rfl⟩ : syracuseStep 7116947 = 10675421) B10675421
theorem B3750227 : Blo 1559477 3750227 := bstep (se 1 (by rfl) ⟨2812670, by rfl⟩ : syracuseStep 3750227 = 5625341) B5625341
theorem B9992609 : Blo 1559477 9992609 := bstep (se 2 (by rfl) ⟨3747228, by rfl⟩ : syracuseStep 9992609 = 7494457) B7494457
theorem B2341289 : Blo 1559477 2341289 := bstep (se 2 (by rfl) ⟨877983, by rfl⟩ : syracuseStep 2341289 = 1755967) B1755967
theorem B2341343 : Blo 1559477 2341343 := bstep (se 1 (by rfl) ⟨1756007, by rfl⟩ : syracuseStep 2341343 = 3512015) B3512015
theorem B5339627 : Blo 1559477 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B3512879 : Blo 1559477 3512879 := bstep (se 1 (by rfl) ⟨2634659, by rfl⟩ : syracuseStep 3512879 = 5269319) B5269319
theorem B2341703 : Blo 1559477 2341703 := bstep (se 1 (by rfl) ⟨1756277, by rfl⟩ : syracuseStep 2341703 = 3512555) B3512555
theorem B14244767 : Blo 1559477 14244767 := bstep (se 1 (by rfl) ⟨10683575, by rfl⟩ : syracuseStep 14244767 = 21367151) B21367151
theorem B2342015 : Blo 1559477 2342015 := bstep (se 1 (by rfl) ⟨1756511, by rfl⟩ : syracuseStep 2342015 = 3513023) B3513023
theorem B29981825 : Blo 1559477 29981825 := bstep (se 2 (by rfl) ⟨11243184, by rfl⟩ : syracuseStep 29981825 = 22486369) B22486369
theorem B5922791 : Blo 1559477 5922791 := bstep (se 1 (by rfl) ⟨4442093, by rfl⟩ : syracuseStep 5922791 = 8884187) B8884187
theorem B7897337 : Blo 1559477 7897337 := bstep (se 2 (by rfl) ⟨2961501, by rfl⟩ : syracuseStep 7897337 = 5923003) B5923003
theorem B13328671 : Blo 1559477 13328671 := bstep (se 1 (by rfl) ⟨9996503, by rfl⟩ : syracuseStep 13328671 = 19993007) B19993007
theorem B18014957 : Blo 1559477 18014957 := bstep (se 3 (by rfl) ⟨3377804, by rfl⟩ : syracuseStep 18014957 = 6755609) B6755609
theorem B6669053 : Blo 1559477 6669053 := bstep (se 3 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 6669053 = 2500895) B2500895
theorem B2810783 : Blo 1559477 2810783 := bstep (se 1 (by rfl) ⟨2108087, by rfl⟩ : syracuseStep 2810783 = 4216175) B4216175
theorem B5923975 : Blo 1559477 5923975 := bstep (se 1 (by rfl) ⟨4442981, by rfl⟩ : syracuseStep 5923975 = 8885963) B8885963
theorem B4744631 : Blo 1559477 4744631 := bstep (se 1 (by rfl) ⟨3558473, by rfl⟩ : syracuseStep 4744631 = 7116947) B7116947
theorem B1754671 : Blo 1559477 1754671 := bstep (se 1 (by rfl) ⟨1316003, by rfl⟩ : syracuseStep 1754671 = 2632007) B2632007
theorem B2500151 : Blo 1559477 2500151 := bstep (se 1 (by rfl) ⟨1875113, by rfl⟩ : syracuseStep 2500151 = 3750227) B3750227
theorem B6661739 : Blo 1559477 6661739 := bstep (se 1 (by rfl) ⟨4996304, by rfl⟩ : syracuseStep 6661739 = 9992609) B9992609
theorem B21653369 : Blo 1559477 21653369 := bstep (se 2 (by rfl) ⟨8120013, by rfl⟩ : syracuseStep 21653369 = 16240027) B16240027
theorem B3950491 : Blo 1559477 3950491 := bstep (se 1 (by rfl) ⟨2962868, by rfl⟩ : syracuseStep 3950491 = 5925737) B5925737
theorem B9496511 : Blo 1559477 9496511 := bstep (se 1 (by rfl) ⟨7122383, by rfl⟩ : syracuseStep 9496511 = 14244767) B14244767
theorem B6326369 : Blo 1559477 6326369 := bstep (se 2 (by rfl) ⟨2372388, by rfl⟩ : syracuseStep 6326369 = 4744777) B4744777
theorem B1755247 : Blo 1559477 1755247 := bstep (se 1 (by rfl) ⟨1316435, by rfl⟩ : syracuseStep 1755247 = 2632871) B2632871
theorem B7899281 : Blo 1559477 7899281 := bstep (se 2 (by rfl) ⟨2962230, by rfl⟩ : syracuseStep 7899281 = 5924461) B5924461
theorem B11241659 : Blo 1559477 11241659 := bstep (se 1 (by rfl) ⟨8431244, by rfl⟩ : syracuseStep 11241659 = 16862489) B16862489
theorem B39995855 : Blo 1559477 39995855 := bstep (se 1 (by rfl) ⟨29996891, by rfl⟩ : syracuseStep 39995855 = 59993783) B59993783
theorem B27036287 : Blo 1559477 27036287 := bstep (se 1 (by rfl) ⟨20277215, by rfl⟩ : syracuseStep 27036287 = 40554431) B40554431
theorem B1559643 : Blo 1559477 1559643 := bstep (se 1 (by rfl) ⟨1169732, by rfl⟩ : syracuseStep 1559643 = 2339465) B2339465
theorem B277548221 : Blo 1559477 277548221 := bstep (se 3 (by rfl) ⟨52040291, by rfl⟩ : syracuseStep 277548221 = 104080583) B104080583
theorem B1559803 : Blo 1559477 1559803 := bstep (se 1 (by rfl) ⟨1169852, by rfl⟩ : syracuseStep 1559803 = 2339705) B2339705
theorem B1560231 : Blo 1559477 1560231 := bstep (se 1 (by rfl) ⟨1170173, by rfl⟩ : syracuseStep 1560231 = 2340347) B2340347
theorem B1560319 : Blo 1559477 1560319 := bstep (se 1 (by rfl) ⟨1170239, by rfl⟩ : syracuseStep 1560319 = 2340479) B2340479
theorem B42733433 : Blo 1559477 42733433 := bstep (se 2 (by rfl) ⟨16025037, by rfl⟩ : syracuseStep 42733433 = 32050075) B32050075
theorem B5926891 : Blo 1559477 5926891 := bstep (se 1 (by rfl) ⟨4445168, by rfl⟩ : syracuseStep 5926891 = 8890337) B8890337
theorem B2633755 : Blo 1559477 2633755 := bstep (se 1 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 2633755 = 3950633) B3950633
theorem B2633897 : Blo 1559477 2633897 := bstep (se 2 (by rfl) ⟨987711, by rfl⟩ : syracuseStep 2633897 = 1975423) B1975423
theorem B1560859 : Blo 1559477 1560859 := bstep (se 1 (by rfl) ⟨1170644, by rfl⟩ : syracuseStep 1560859 = 2341289) B2341289
theorem B1560895 : Blo 1559477 1560895 := bstep (se 1 (by rfl) ⟨1170671, by rfl⟩ : syracuseStep 1560895 = 2341343) B2341343
theorem B3559751 : Blo 1559477 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B7901549 : Blo 1559477 7901549 := bstep (se 3 (by rfl) ⟨1481540, by rfl⟩ : syracuseStep 7901549 = 2963081) B2963081
theorem B1561135 : Blo 1559477 1561135 := bstep (se 1 (by rfl) ⟨1170851, by rfl⟩ : syracuseStep 1561135 = 2341703) B2341703
theorem B11252297 : Blo 1559477 11252297 := bstep (se 2 (by rfl) ⟨4219611, by rfl⟩ : syracuseStep 11252297 = 8439223) B8439223
theorem B711815789 : Blo 1559477 711815789 := bstep (se 3 (by rfl) ⟨133465460, by rfl⟩ : syracuseStep 711815789 = 266930921) B266930921
theorem B8884961 : Blo 1559477 8884961 := bstep (se 2 (by rfl) ⟨3331860, by rfl⟩ : syracuseStep 8884961 = 6663721) B6663721
theorem B1561343 : Blo 1559477 1561343 := bstep (se 1 (by rfl) ⟨1171007, by rfl⟩ : syracuseStep 1561343 = 2342015) B2342015
theorem B13333319 : Blo 1559477 13333319 := bstep (se 1 (by rfl) ⟨9999989, by rfl⟩ : syracuseStep 13333319 = 19999979) B19999979
theorem B2339711 : Blo 1559477 2339711 := bstep (se 1 (by rfl) ⟨1754783, by rfl⟩ : syracuseStep 2339711 = 3509567) B3509567
theorem B2962345 : Blo 1559477 2962345 := bstep (se 2 (by rfl) ⟨1110879, by rfl⟩ : syracuseStep 2962345 = 2221759) B2221759
theorem B5927849 : Blo 1559477 5927849 := bstep (se 2 (by rfl) ⟨2222943, by rfl⟩ : syracuseStep 5927849 = 4445887) B4445887
theorem B2339783 : Blo 1559477 2339783 := bstep (se 1 (by rfl) ⟨1754837, by rfl⟩ : syracuseStep 2339783 = 3509675) B3509675
theorem B5928349 : Blo 1559477 5928349 := bstep (se 3 (by rfl) ⟨1111565, by rfl⟩ : syracuseStep 5928349 = 2223131) B2223131
theorem B22484411 : Blo 1559477 22484411 := bstep (se 1 (by rfl) ⟨16863308, by rfl⟩ : syracuseStep 22484411 = 33726617) B33726617
theorem B4216411 : Blo 1559477 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B2340521 : Blo 1559477 2340521 := bstep (se 2 (by rfl) ⟨877695, by rfl⟩ : syracuseStep 2340521 = 1755391) B1755391
theorem B22484753 : Blo 1559477 22484753 := bstep (se 2 (by rfl) ⟨8431782, by rfl⟩ : syracuseStep 22484753 = 16863565) B16863565
theorem B2340647 : Blo 1559477 2340647 := bstep (se 1 (by rfl) ⟨1755485, by rfl⟩ : syracuseStep 2340647 = 3510971) B3510971
theorem B2340719 : Blo 1559477 2340719 := bstep (se 1 (by rfl) ⟨1755539, by rfl⟩ : syracuseStep 2340719 = 3511079) B3511079
theorem B7894907 : Blo 1559477 7894907 := bstep (se 1 (by rfl) ⟨5921180, by rfl⟩ : syracuseStep 7894907 = 11842361) B11842361
theorem B5265323 : Blo 1559477 5265323 := bstep (se 1 (by rfl) ⟨3948992, by rfl⟩ : syracuseStep 5265323 = 7897985) B7897985
theorem B50591735 : Blo 1559477 50591735 := bstep (se 1 (by rfl) ⟨37943801, by rfl⟩ : syracuseStep 50591735 = 75887603) B75887603
theorem B7895231 : Blo 1559477 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B2341355 : Blo 1559477 2341355 := bstep (se 1 (by rfl) ⟨1756016, by rfl⟩ : syracuseStep 2341355 = 3512033) B3512033
theorem B2963947 : Blo 1559477 2963947 := bstep (se 1 (by rfl) ⟨2222960, by rfl⟩ : syracuseStep 2963947 = 4445921) B4445921
theorem B12819055 : Blo 1559477 12819055 := bstep (se 1 (by rfl) ⟨9614291, by rfl⟩ : syracuseStep 12819055 = 19228583) B19228583
theorem B13327031 : Blo 1559477 13327031 := bstep (se 1 (by rfl) ⟨9995273, by rfl⟩ : syracuseStep 13327031 = 19990547) B19990547
theorem B96131771 : Blo 1559477 96131771 := bstep (se 1 (by rfl) ⟨72098828, by rfl⟩ : syracuseStep 96131771 = 144197657) B144197657
theorem B2341631 : Blo 1559477 2341631 := bstep (se 1 (by rfl) ⟨1756223, by rfl⟩ : syracuseStep 2341631 = 3512447) B3512447
theorem B2341919 : Blo 1559477 2341919 := bstep (se 1 (by rfl) ⟨1756439, by rfl⟩ : syracuseStep 2341919 = 3512879) B3512879
theorem B19995983 : Blo 1559477 19995983 := bstep (se 1 (by rfl) ⟨14996987, by rfl⟩ : syracuseStep 19995983 = 29993975) B29993975
theorem B19987883 : Blo 1559477 19987883 := bstep (se 1 (by rfl) ⟨14990912, by rfl⟩ : syracuseStep 19987883 = 29981825) B29981825
theorem B19250669 : Blo 1559477 19250669 := bstep (se 3 (by rfl) ⟨3609500, by rfl⟩ : syracuseStep 19250669 = 7219001) B7219001
theorem B5267051 : Blo 1559477 5267051 := bstep (se 1 (by rfl) ⟨3950288, by rfl⟩ : syracuseStep 5267051 = 7900577) B7900577
theorem B3948527 : Blo 1559477 3948527 := bstep (se 1 (by rfl) ⟨2961395, by rfl⟩ : syracuseStep 3948527 = 5922791) B5922791
theorem B5267699 : Blo 1559477 5267699 := bstep (se 1 (by rfl) ⟨3950774, by rfl⟩ : syracuseStep 5267699 = 7901549) B7901549
theorem B5923307 : Blo 1559477 5923307 := bstep (se 1 (by rfl) ⟨4442480, by rfl⟩ : syracuseStep 5923307 = 8884961) B8884961
theorem B12009971 : Blo 1559477 12009971 := bstep (se 1 (by rfl) ⟨9007478, by rfl⟩ : syracuseStep 12009971 = 18014957) B18014957
theorem B8888879 : Blo 1559477 8888879 := bstep (se 1 (by rfl) ⟨6666659, by rfl⟩ : syracuseStep 8888879 = 13333319) B13333319
theorem B3163087 : Blo 1559477 3163087 := bstep (se 1 (by rfl) ⟨2372315, by rfl⟩ : syracuseStep 3163087 = 4744631) B4744631
theorem B4441159 : Blo 1559477 4441159 := bstep (se 1 (by rfl) ⟨3330869, by rfl⟩ : syracuseStep 4441159 = 6661739) B6661739
theorem B3949793 : Blo 1559477 3949793 := bstep (se 2 (by rfl) ⟨1481172, by rfl⟩ : syracuseStep 3949793 = 2962345) B2962345
theorem B14435579 : Blo 1559477 14435579 := bstep (se 1 (by rfl) ⟨10826684, by rfl⟩ : syracuseStep 14435579 = 21653369) B21653369
theorem B33727823 : Blo 1559477 33727823 := bstep (se 1 (by rfl) ⟨25295867, by rfl⟩ : syracuseStep 33727823 = 50591735) B50591735
theorem B7898633 : Blo 1559477 7898633 := bstep (se 2 (by rfl) ⟨2961987, by rfl⟩ : syracuseStep 7898633 = 5923975) B5923975
theorem B18024191 : Blo 1559477 18024191 := bstep (se 1 (by rfl) ⟨13518143, by rfl⟩ : syracuseStep 18024191 = 27036287) B27036287
theorem B64087847 : Blo 1559477 64087847 := bstep (se 1 (by rfl) ⟨48065885, by rfl⟩ : syracuseStep 64087847 = 96131771) B96131771
theorem B5621881 : Blo 1559477 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B13330655 : Blo 1559477 13330655 := bstep (se 1 (by rfl) ⟨9997991, by rfl⟩ : syracuseStep 13330655 = 19995983) B19995983
theorem B2632351 : Blo 1559477 2632351 := bstep (se 1 (by rfl) ⟨1974263, by rfl⟩ : syracuseStep 2632351 = 3948527) B3948527
theorem B1755931 : Blo 1559477 1755931 := bstep (se 1 (by rfl) ⟨1316948, by rfl⟩ : syracuseStep 1755931 = 2633897) B2633897
theorem B17771561 : Blo 1559477 17771561 := bstep (se 2 (by rfl) ⟨6664335, by rfl⟩ : syracuseStep 17771561 = 13328671) B13328671
theorem B26668277 : Blo 1559477 26668277 := bstep (se 5 (by rfl) ⟨1250075, by rfl⟩ : syracuseStep 26668277 = 2500151) B2500151
theorem B1559807 : Blo 1559477 1559807 := bstep (se 1 (by rfl) ⟨1169855, by rfl⟩ : syracuseStep 1559807 = 2339711) B2339711
theorem B3951899 : Blo 1559477 3951899 := bstep (se 1 (by rfl) ⟨2963924, by rfl⟩ : syracuseStep 3951899 = 5927849) B5927849
theorem B1559855 : Blo 1559477 1559855 := bstep (se 1 (by rfl) ⟨1169891, by rfl⟩ : syracuseStep 1559855 = 2339783) B2339783
theorem B3951929 : Blo 1559477 3951929 := bstep (se 2 (by rfl) ⟨1481973, by rfl⟩ : syracuseStep 3951929 = 2963947) B2963947
theorem B17092073 : Blo 1559477 17092073 := bstep (se 2 (by rfl) ⟨6409527, by rfl⟩ : syracuseStep 17092073 = 12819055) B12819055
theorem B1560347 : Blo 1559477 1560347 := bstep (se 1 (by rfl) ⟨1170260, by rfl⟩ : syracuseStep 1560347 = 2340521) B2340521
theorem B1560431 : Blo 1559477 1560431 := bstep (se 1 (by rfl) ⟨1170323, by rfl⟩ : syracuseStep 1560431 = 2340647) B2340647
theorem B1560479 : Blo 1559477 1560479 := bstep (se 1 (by rfl) ⟨1170359, by rfl⟩ : syracuseStep 1560479 = 2340719) B2340719
theorem B5263271 : Blo 1559477 5263271 := bstep (se 1 (by rfl) ⟨3947453, by rfl⟩ : syracuseStep 5263271 = 7894907) B7894907
theorem B3510215 : Blo 1559477 3510215 := bstep (se 1 (by rfl) ⟨2632661, by rfl⟩ : syracuseStep 3510215 = 5265323) B5265323
theorem B51335117 : Blo 1559477 51335117 := bstep (se 3 (by rfl) ⟨9625334, by rfl⟩ : syracuseStep 51335117 = 19250669) B19250669
theorem B5263487 : Blo 1559477 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B1560903 : Blo 1559477 1560903 := bstep (se 1 (by rfl) ⟨1170677, by rfl⟩ : syracuseStep 1560903 = 2341355) B2341355
theorem B8884687 : Blo 1559477 8884687 := bstep (se 1 (by rfl) ⟨6663515, by rfl⟩ : syracuseStep 8884687 = 13327031) B13327031
theorem B1561087 : Blo 1559477 1561087 := bstep (se 1 (by rfl) ⟨1170815, by rfl⟩ : syracuseStep 1561087 = 2341631) B2341631
theorem B1561279 : Blo 1559477 1561279 := bstep (se 1 (by rfl) ⟨1170959, by rfl⟩ : syracuseStep 1561279 = 2341919) B2341919
theorem B2339561 : Blo 1559477 2339561 := bstep (se 2 (by rfl) ⟨877335, by rfl⟩ : syracuseStep 2339561 = 1754671) B1754671
theorem B13325255 : Blo 1559477 13325255 := bstep (se 1 (by rfl) ⟨9993941, by rfl⟩ : syracuseStep 13325255 = 19987883) B19987883
theorem B3511367 : Blo 1559477 3511367 := bstep (se 1 (by rfl) ⟨2633525, by rfl⟩ : syracuseStep 3511367 = 5267051) B5267051
theorem B28488955 : Blo 1559477 28488955 := bstep (se 1 (by rfl) ⟨21366716, by rfl⟩ : syracuseStep 28488955 = 42733433) B42733433
theorem B7902521 : Blo 1559477 7902521 := bstep (se 2 (by rfl) ⟨2963445, by rfl⟩ : syracuseStep 7902521 = 5926891) B5926891
theorem B3511673 : Blo 1559477 3511673 := bstep (se 2 (by rfl) ⟨1316877, by rfl⟩ : syracuseStep 3511673 = 2633755) B2633755
theorem B2340329 : Blo 1559477 2340329 := bstep (se 2 (by rfl) ⟨877623, by rfl⟩ : syracuseStep 2340329 = 1755247) B1755247
theorem B5264891 : Blo 1559477 5264891 := bstep (se 1 (by rfl) ⟨3948668, by rfl⟩ : syracuseStep 5264891 = 7897337) B7897337
theorem B2373167 : Blo 1559477 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B7501531 : Blo 1559477 7501531 := bstep (se 1 (by rfl) ⟨5626148, by rfl⟩ : syracuseStep 7501531 = 11252297) B11252297
theorem B474543859 : Blo 1559477 474543859 := bstep (se 1 (by rfl) ⟨355907894, by rfl⟩ : syracuseStep 474543859 = 711815789) B711815789
theorem B740128589 : Blo 1559477 740128589 := bstep (se 3 (by rfl) ⟨138774110, by rfl⟩ : syracuseStep 740128589 = 277548221) B277548221
theorem B4446035 : Blo 1559477 4446035 := bstep (se 1 (by rfl) ⟨3334526, by rfl⟩ : syracuseStep 4446035 = 6669053) B6669053
theorem B1873855 : Blo 1559477 1873855 := bstep (se 1 (by rfl) ⟨1405391, by rfl⟩ : syracuseStep 1873855 = 2810783) B2810783
theorem B14989607 : Blo 1559477 14989607 := bstep (se 1 (by rfl) ⟨11242205, by rfl⟩ : syracuseStep 14989607 = 22484411) B22484411
theorem B14989835 : Blo 1559477 14989835 := bstep (se 1 (by rfl) ⟨11242376, by rfl⟩ : syracuseStep 14989835 = 22484753) B22484753
theorem B6331007 : Blo 1559477 6331007 := bstep (se 1 (by rfl) ⟨4748255, by rfl⟩ : syracuseStep 6331007 = 9496511) B9496511
theorem B4217579 : Blo 1559477 4217579 := bstep (se 1 (by rfl) ⟨3163184, by rfl⟩ : syracuseStep 4217579 = 6326369) B6326369
theorem B5266187 : Blo 1559477 5266187 := bstep (se 1 (by rfl) ⟨3949640, by rfl⟩ : syracuseStep 5266187 = 7899281) B7899281
theorem B7494439 : Blo 1559477 7494439 := bstep (se 1 (by rfl) ⟨5620829, by rfl⟩ : syracuseStep 7494439 = 11241659) B11241659
theorem B26663903 : Blo 1559477 26663903 := bstep (se 1 (by rfl) ⟨19997927, by rfl⟩ : syracuseStep 26663903 = 39995855) B39995855
theorem B7904465 : Blo 1559477 7904465 := bstep (se 2 (by rfl) ⟨2964174, by rfl⟩ : syracuseStep 7904465 = 5928349) B5928349
theorem B5267321 : Blo 1559477 5267321 := bstep (se 2 (by rfl) ⟨1975245, by rfl⟩ : syracuseStep 5267321 = 3950491) B3950491
theorem B7495841 : Blo 1559477 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B3948871 : Blo 1559477 3948871 := bstep (se 1 (by rfl) ⟨2961653, by rfl⟩ : syracuseStep 3948871 = 5923307) B5923307
theorem B11846249 : Blo 1559477 11846249 := bstep (se 2 (by rfl) ⟨4442343, by rfl⟩ : syracuseStep 11846249 = 8884687) B8884687
theorem B5268347 : Blo 1559477 5268347 := bstep (se 1 (by rfl) ⟨3951260, by rfl⟩ : syracuseStep 5268347 = 7902521) B7902521
theorem B1582111 : Blo 1559477 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B4220671 : Blo 1559477 4220671 := bstep (se 1 (by rfl) ⟨3165503, by rfl⟩ : syracuseStep 4220671 = 6331007) B6331007
theorem B2811719 : Blo 1559477 2811719 := bstep (se 1 (by rfl) ⟨2108789, by rfl⟩ : syracuseStep 2811719 = 4217579) B4217579
theorem B11847707 : Blo 1559477 11847707 := bstep (se 1 (by rfl) ⟨8885780, by rfl⟩ : syracuseStep 11847707 = 17771561) B17771561
theorem B5269643 : Blo 1559477 5269643 := bstep (se 1 (by rfl) ⟨3952232, by rfl⟩ : syracuseStep 5269643 = 7904465) B7904465
theorem B17778851 : Blo 1559477 17778851 := bstep (se 1 (by rfl) ⟨13334138, by rfl⟩ : syracuseStep 17778851 = 26668277) B26668277
theorem B3508847 : Blo 1559477 3508847 := bstep (se 1 (by rfl) ⟨2631635, by rfl⟩ : syracuseStep 3508847 = 5263271) B5263271
theorem B3508991 : Blo 1559477 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B5925919 : Blo 1559477 5925919 := bstep (se 1 (by rfl) ⟨4444439, by rfl⟩ : syracuseStep 5925919 = 8888879) B8888879
theorem B1559707 : Blo 1559477 1559707 := bstep (se 1 (by rfl) ⟨1169780, by rfl⟩ : syracuseStep 1559707 = 2339561) B2339561
theorem B8883503 : Blo 1559477 8883503 := bstep (se 1 (by rfl) ⟨6662627, by rfl⟩ : syracuseStep 8883503 = 13325255) B13325255
theorem B2633195 : Blo 1559477 2633195 := bstep (se 1 (by rfl) ⟨1974896, by rfl⟩ : syracuseStep 2633195 = 3949793) B3949793
theorem B3509801 : Blo 1559477 3509801 := bstep (se 2 (by rfl) ⟨1316175, by rfl⟩ : syracuseStep 3509801 = 2632351) B2632351
theorem B1560219 : Blo 1559477 1560219 := bstep (se 1 (by rfl) ⟨1170164, by rfl⟩ : syracuseStep 1560219 = 2340329) B2340329
theorem B3509927 : Blo 1559477 3509927 := bstep (se 1 (by rfl) ⟨2632445, by rfl⟩ : syracuseStep 3509927 = 5264891) B5264891
theorem B42725231 : Blo 1559477 42725231 := bstep (se 1 (by rfl) ⟨32043923, by rfl⟩ : syracuseStep 42725231 = 64087847) B64087847
theorem B32026589 : Blo 1559477 32026589 := bstep (se 3 (by rfl) ⟨6004985, by rfl⟩ : syracuseStep 32026589 = 12009971) B12009971
theorem B3510791 : Blo 1559477 3510791 := bstep (se 1 (by rfl) ⟨2633093, by rfl⟩ : syracuseStep 3510791 = 5266187) B5266187
theorem B2634599 : Blo 1559477 2634599 := bstep (se 1 (by rfl) ⟨1975949, by rfl⟩ : syracuseStep 2634599 = 3951899) B3951899
theorem B2634619 : Blo 1559477 2634619 := bstep (se 1 (by rfl) ⟨1975964, by rfl⟩ : syracuseStep 2634619 = 3951929) B3951929
theorem B3511547 : Blo 1559477 3511547 := bstep (se 1 (by rfl) ⟨2633660, by rfl⟩ : syracuseStep 3511547 = 5267321) B5267321
theorem B2340143 : Blo 1559477 2340143 := bstep (se 1 (by rfl) ⟨1755107, by rfl⟩ : syracuseStep 2340143 = 3510215) B3510215
theorem B34223411 : Blo 1559477 34223411 := bstep (se 1 (by rfl) ⟨25667558, by rfl⟩ : syracuseStep 34223411 = 51335117) B51335117
theorem B3511799 : Blo 1559477 3511799 := bstep (se 1 (by rfl) ⟨2633849, by rfl⟩ : syracuseStep 3511799 = 5267699) B5267699
theorem B2340911 : Blo 1559477 2340911 := bstep (se 1 (by rfl) ⟨1755683, by rfl⟩ : syracuseStep 2340911 = 3511367) B3511367
theorem B9623719 : Blo 1559477 9623719 := bstep (se 1 (by rfl) ⟨7217789, by rfl⟩ : syracuseStep 9623719 = 14435579) B14435579
theorem B22485215 : Blo 1559477 22485215 := bstep (se 1 (by rfl) ⟨16863911, by rfl⟩ : syracuseStep 22485215 = 33727823) B33727823
theorem B2341115 : Blo 1559477 2341115 := bstep (se 1 (by rfl) ⟨1755836, by rfl⟩ : syracuseStep 2341115 = 3511673) B3511673
theorem B5265755 : Blo 1559477 5265755 := bstep (se 1 (by rfl) ⟨3949316, by rfl⟩ : syracuseStep 5265755 = 7898633) B7898633
theorem B2341241 : Blo 1559477 2341241 := bstep (se 2 (by rfl) ⟨877965, by rfl⟩ : syracuseStep 2341241 = 1755931) B1755931
theorem B9992585 : Blo 1559477 9992585 := bstep (se 2 (by rfl) ⟨3747219, by rfl⟩ : syracuseStep 9992585 = 7494439) B7494439
theorem B12016127 : Blo 1559477 12016127 := bstep (se 1 (by rfl) ⟨9012095, by rfl⟩ : syracuseStep 12016127 = 18024191) B18024191
theorem B493419059 : Blo 1559477 493419059 := bstep (se 1 (by rfl) ⟨370064294, by rfl⟩ : syracuseStep 493419059 = 740128589) B740128589
theorem B2964023 : Blo 1559477 2964023 := bstep (se 1 (by rfl) ⟨2223017, by rfl⟩ : syracuseStep 2964023 = 4446035) B4446035
theorem B4217449 : Blo 1559477 4217449 := bstep (se 2 (by rfl) ⟨1581543, by rfl⟩ : syracuseStep 4217449 = 3163087) B3163087
theorem B5921545 : Blo 1559477 5921545 := bstep (se 2 (by rfl) ⟨2220579, by rfl⟩ : syracuseStep 5921545 = 4441159) B4441159
theorem B8887103 : Blo 1559477 8887103 := bstep (se 1 (by rfl) ⟨6665327, by rfl⟩ : syracuseStep 8887103 = 13330655) B13330655
theorem B9993071 : Blo 1559477 9993071 := bstep (se 1 (by rfl) ⟨7494803, by rfl⟩ : syracuseStep 9993071 = 14989607) B14989607
theorem B37985273 : Blo 1559477 37985273 := bstep (se 2 (by rfl) ⟨14244477, by rfl⟩ : syracuseStep 37985273 = 28488955) B28488955
theorem B9993223 : Blo 1559477 9993223 := bstep (se 1 (by rfl) ⟨7494917, by rfl⟩ : syracuseStep 9993223 = 14989835) B14989835
theorem B17775935 : Blo 1559477 17775935 := bstep (se 1 (by rfl) ⟨13331951, by rfl⟩ : syracuseStep 17775935 = 26663903) B26663903
theorem B10002041 : Blo 1559477 10002041 := bstep (se 2 (by rfl) ⟨3750765, by rfl⟩ : syracuseStep 10002041 = 7501531) B7501531
theorem B632725145 : Blo 1559477 632725145 := bstep (se 2 (by rfl) ⟨237271929, by rfl⟩ : syracuseStep 632725145 = 474543859) B474543859
theorem B11394715 : Blo 1559477 11394715 := bstep (se 1 (by rfl) ⟨8546036, by rfl⟩ : syracuseStep 11394715 = 17092073) B17092073
theorem B2498473 : Blo 1559477 2498473 := bstep (se 2 (by rfl) ⟨936927, by rfl⟩ : syracuseStep 2498473 = 1873855) B1873855
theorem B4997227 : Blo 1559477 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B8437925 : Blo 1559477 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B7897499 : Blo 1559477 7897499 := bstep (se 1 (by rfl) ⟨5923124, by rfl⟩ : syracuseStep 7897499 = 11846249) B11846249
theorem B22815607 : Blo 1559477 22815607 := bstep (se 1 (by rfl) ⟨17111705, by rfl⟩ : syracuseStep 22815607 = 34223411) B34223411
theorem B7898471 : Blo 1559477 7898471 := bstep (se 1 (by rfl) ⟨5923853, by rfl⟩ : syracuseStep 7898471 = 11847707) B11847707
theorem B6661723 : Blo 1559477 6661723 := bstep (se 1 (by rfl) ⟨4996292, by rfl⟩ : syracuseStep 6661723 = 9992585) B9992585
theorem B1976015 : Blo 1559477 1976015 := bstep (se 1 (by rfl) ⟨1482011, by rfl⟩ : syracuseStep 1976015 = 2964023) B2964023
theorem B5924735 : Blo 1559477 5924735 := bstep (se 1 (by rfl) ⟨4443551, by rfl⟩ : syracuseStep 5924735 = 8887103) B8887103
theorem B6662047 : Blo 1559477 6662047 := bstep (se 1 (by rfl) ⟨4996535, by rfl⟩ : syracuseStep 6662047 = 9993071) B9993071
theorem B25323515 : Blo 1559477 25323515 := bstep (se 1 (by rfl) ⟨18992636, by rfl⟩ : syracuseStep 25323515 = 37985273) B37985273
theorem B7497917 : Blo 1559477 7497917 := bstep (se 3 (by rfl) ⟨1405859, by rfl⟩ : syracuseStep 7497917 = 2811719) B2811719
theorem B1755463 : Blo 1559477 1755463 := bstep (se 1 (by rfl) ⟨1316597, by rfl⟩ : syracuseStep 1755463 = 2633195) B2633195
theorem B421816763 : Blo 1559477 421816763 := bstep (se 1 (by rfl) ⟨316362572, by rfl⟩ : syracuseStep 421816763 = 632725145) B632725145
theorem B21351059 : Blo 1559477 21351059 := bstep (se 1 (by rfl) ⟨16013294, by rfl⟩ : syracuseStep 21351059 = 32026589) B32026589
theorem B12831625 : Blo 1559477 12831625 := bstep (se 2 (by rfl) ⟨4811859, by rfl⟩ : syracuseStep 12831625 = 9623719) B9623719
theorem B1756399 : Blo 1559477 1756399 := bstep (se 1 (by rfl) ⟨1317299, by rfl⟩ : syracuseStep 1756399 = 2634599) B2634599
theorem B5623265 : Blo 1559477 5623265 := bstep (se 2 (by rfl) ⟨2108724, by rfl⟩ : syracuseStep 5623265 = 4217449) B4217449
theorem B1560095 : Blo 1559477 1560095 := bstep (se 1 (by rfl) ⟨1170071, by rfl⟩ : syracuseStep 1560095 = 2340143) B2340143
theorem B13324297 : Blo 1559477 13324297 := bstep (se 2 (by rfl) ⟨4996611, by rfl⟩ : syracuseStep 13324297 = 9993223) B9993223
theorem B1560607 : Blo 1559477 1560607 := bstep (se 1 (by rfl) ⟨1170455, by rfl⟩ : syracuseStep 1560607 = 2340911) B2340911
theorem B7901225 : Blo 1559477 7901225 := bstep (se 2 (by rfl) ⟨2962959, by rfl⟩ : syracuseStep 7901225 = 5925919) B5925919
theorem B1560743 : Blo 1559477 1560743 := bstep (se 1 (by rfl) ⟨1170557, by rfl⟩ : syracuseStep 1560743 = 2341115) B2341115
theorem B3510503 : Blo 1559477 3510503 := bstep (se 1 (by rfl) ⟨2632877, by rfl⟩ : syracuseStep 3510503 = 5265755) B5265755
theorem B1560827 : Blo 1559477 1560827 := bstep (se 1 (by rfl) ⟨1170620, by rfl⟩ : syracuseStep 1560827 = 2341241) B2341241
theorem B328946039 : Blo 1559477 328946039 := bstep (se 1 (by rfl) ⟨246709529, by rfl⟩ : syracuseStep 328946039 = 493419059) B493419059
theorem B2339231 : Blo 1559477 2339231 := bstep (se 1 (by rfl) ⟨1754423, by rfl⟩ : syracuseStep 2339231 = 3508847) B3508847
theorem B2339327 : Blo 1559477 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B15192953 : Blo 1559477 15192953 := bstep (se 2 (by rfl) ⟨5697357, by rfl⟩ : syracuseStep 15192953 = 11394715) B11394715
theorem B11850623 : Blo 1559477 11850623 := bstep (se 1 (by rfl) ⟨8887967, by rfl⟩ : syracuseStep 11850623 = 17775935) B17775935
theorem B2339867 : Blo 1559477 2339867 := bstep (se 1 (by rfl) ⟨1754900, by rfl⟩ : syracuseStep 2339867 = 3509801) B3509801
theorem B2339951 : Blo 1559477 2339951 := bstep (se 1 (by rfl) ⟨1754963, by rfl⟩ : syracuseStep 2339951 = 3509927) B3509927
theorem B3331297 : Blo 1559477 3331297 := bstep (se 2 (by rfl) ⟨1249236, by rfl⟩ : syracuseStep 3331297 = 2498473) B2498473
theorem B2340527 : Blo 1559477 2340527 := bstep (se 1 (by rfl) ⟨1755395, by rfl⟩ : syracuseStep 2340527 = 3510791) B3510791
theorem B5265161 : Blo 1559477 5265161 := bstep (se 2 (by rfl) ⟨1974435, by rfl⟩ : syracuseStep 5265161 = 3948871) B3948871
theorem B3512231 : Blo 1559477 3512231 := bstep (se 1 (by rfl) ⟨2634173, by rfl⟩ : syracuseStep 3512231 = 5268347) B5268347
theorem B2341031 : Blo 1559477 2341031 := bstep (se 1 (by rfl) ⟨1755773, by rfl⟩ : syracuseStep 2341031 = 3511547) B3511547
theorem B2341199 : Blo 1559477 2341199 := bstep (se 1 (by rfl) ⟨1755899, by rfl⟩ : syracuseStep 2341199 = 3511799) B3511799
theorem B7895393 : Blo 1559477 7895393 := bstep (se 2 (by rfl) ⟨2960772, by rfl⟩ : syracuseStep 7895393 = 5921545) B5921545
theorem B3512825 : Blo 1559477 3512825 := bstep (se 2 (by rfl) ⟨1317309, by rfl⟩ : syracuseStep 3512825 = 2634619) B2634619
theorem B3513095 : Blo 1559477 3513095 := bstep (se 1 (by rfl) ⟨2634821, by rfl⟩ : syracuseStep 3513095 = 5269643) B5269643
theorem B11852567 : Blo 1559477 11852567 := bstep (se 1 (by rfl) ⟨8889425, by rfl⟩ : syracuseStep 11852567 = 17778851) B17778851
theorem B14990143 : Blo 1559477 14990143 := bstep (se 1 (by rfl) ⟨11242607, by rfl⟩ : syracuseStep 14990143 = 22485215) B22485215
theorem B8010751 : Blo 1559477 8010751 := bstep (se 1 (by rfl) ⟨6008063, by rfl⟩ : syracuseStep 8010751 = 12016127) B12016127
theorem B5922335 : Blo 1559477 5922335 := bstep (se 1 (by rfl) ⟨4441751, by rfl⟩ : syracuseStep 5922335 = 8883503) B8883503
theorem B5627561 : Blo 1559477 5627561 := bstep (se 2 (by rfl) ⟨2110335, by rfl⟩ : syracuseStep 5627561 = 4220671) B4220671
theorem B6668027 : Blo 1559477 6668027 := bstep (se 1 (by rfl) ⟨5001020, by rfl⟩ : syracuseStep 6668027 = 10002041) B10002041
theorem B28483487 : Blo 1559477 28483487 := bstep (se 1 (by rfl) ⟨21362615, by rfl⟩ : syracuseStep 28483487 = 42725231) B42725231
theorem B5267483 : Blo 1559477 5267483 := bstep (se 1 (by rfl) ⟨3950612, by rfl⟩ : syracuseStep 5267483 = 7901225) B7901225
theorem B3949823 : Blo 1559477 3949823 := bstep (se 1 (by rfl) ⟨2962367, by rfl⟩ : syracuseStep 3949823 = 5924735) B5924735
theorem B4998611 : Blo 1559477 4998611 := bstep (se 1 (by rfl) ⟨3748958, by rfl⟩ : syracuseStep 4998611 = 7497917) B7497917
theorem B4441729 : Blo 1559477 4441729 := bstep (se 2 (by rfl) ⟨1665648, by rfl⟩ : syracuseStep 4441729 = 3331297) B3331297
theorem B5269373 : Blo 1559477 5269373 := bstep (se 3 (by rfl) ⟨988007, by rfl⟩ : syracuseStep 5269373 = 1976015) B1976015
theorem B8882297 : Blo 1559477 8882297 := bstep (se 2 (by rfl) ⟨3330861, by rfl⟩ : syracuseStep 8882297 = 6661723) B6661723
theorem B8882729 : Blo 1559477 8882729 := bstep (se 2 (by rfl) ⟨3331023, by rfl⟩ : syracuseStep 8882729 = 6662047) B6662047
theorem B6662969 : Blo 1559477 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B1559487 : Blo 1559477 1559487 := bstep (se 1 (by rfl) ⟨1169615, by rfl⟩ : syracuseStep 1559487 = 2339231) B2339231
theorem B1559551 : Blo 1559477 1559551 := bstep (se 1 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 1559551 = 2339327) B2339327
theorem B10128635 : Blo 1559477 10128635 := bstep (se 1 (by rfl) ⟨7596476, by rfl⟩ : syracuseStep 10128635 = 15192953) B15192953
theorem B7900415 : Blo 1559477 7900415 := bstep (se 1 (by rfl) ⟨5925311, by rfl⟩ : syracuseStep 7900415 = 11850623) B11850623
theorem B1559911 : Blo 1559477 1559911 := bstep (se 1 (by rfl) ⟨1169933, by rfl⟩ : syracuseStep 1559911 = 2339867) B2339867
theorem B1559967 : Blo 1559477 1559967 := bstep (se 1 (by rfl) ⟨1169975, by rfl⟩ : syracuseStep 1559967 = 2339951) B2339951
theorem B1560351 : Blo 1559477 1560351 := bstep (se 1 (by rfl) ⟨1170263, by rfl⟩ : syracuseStep 1560351 = 2340527) B2340527
theorem B30420809 : Blo 1559477 30420809 := bstep (se 2 (by rfl) ⟨11407803, by rfl⟩ : syracuseStep 30420809 = 22815607) B22815607
theorem B3510107 : Blo 1559477 3510107 := bstep (se 1 (by rfl) ⟨2632580, by rfl⟩ : syracuseStep 3510107 = 5265161) B5265161
theorem B17108833 : Blo 1559477 17108833 := bstep (se 2 (by rfl) ⟨6415812, by rfl⟩ : syracuseStep 17108833 = 12831625) B12831625
theorem B1560687 : Blo 1559477 1560687 := bstep (se 1 (by rfl) ⟨1170515, by rfl⟩ : syracuseStep 1560687 = 2341031) B2341031
theorem B1560799 : Blo 1559477 1560799 := bstep (se 1 (by rfl) ⟨1170599, by rfl⟩ : syracuseStep 1560799 = 2341199) B2341199
theorem B5263595 : Blo 1559477 5263595 := bstep (se 1 (by rfl) ⟨3947696, by rfl⟩ : syracuseStep 5263595 = 7895393) B7895393
theorem B281211175 : Blo 1559477 281211175 := bstep (se 1 (by rfl) ⟨210908381, by rfl⟩ : syracuseStep 281211175 = 421816763) B421816763
theorem B14234039 : Blo 1559477 14234039 := bstep (se 1 (by rfl) ⟨10675529, by rfl⟩ : syracuseStep 14234039 = 21351059) B21351059
theorem B7901711 : Blo 1559477 7901711 := bstep (se 1 (by rfl) ⟨5926283, by rfl⟩ : syracuseStep 7901711 = 11852567) B11852567
theorem B3748843 : Blo 1559477 3748843 := bstep (se 1 (by rfl) ⟨2811632, by rfl⟩ : syracuseStep 3748843 = 5623265) B5623265
theorem B4445351 : Blo 1559477 4445351 := bstep (se 1 (by rfl) ⟨3334013, by rfl⟩ : syracuseStep 4445351 = 6668027) B6668027
theorem B17765729 : Blo 1559477 17765729 := bstep (se 2 (by rfl) ⟨6662148, by rfl⟩ : syracuseStep 17765729 = 13324297) B13324297
theorem B5625283 : Blo 1559477 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B2340335 : Blo 1559477 2340335 := bstep (se 1 (by rfl) ⟨1755251, by rfl⟩ : syracuseStep 2340335 = 3510503) B3510503
theorem B219297359 : Blo 1559477 219297359 := bstep (se 1 (by rfl) ⟨164473019, by rfl⟩ : syracuseStep 219297359 = 328946039) B328946039
theorem B5264999 : Blo 1559477 5264999 := bstep (se 1 (by rfl) ⟨3948749, by rfl⟩ : syracuseStep 5264999 = 7897499) B7897499
theorem B2340617 : Blo 1559477 2340617 := bstep (se 2 (by rfl) ⟨877731, by rfl⟩ : syracuseStep 2340617 = 1755463) B1755463
theorem B5265647 : Blo 1559477 5265647 := bstep (se 1 (by rfl) ⟨3949235, by rfl⟩ : syracuseStep 5265647 = 7898471) B7898471
theorem B19986857 : Blo 1559477 19986857 := bstep (se 2 (by rfl) ⟨7495071, by rfl⟩ : syracuseStep 19986857 = 14990143) B14990143
theorem B2341487 : Blo 1559477 2341487 := bstep (se 1 (by rfl) ⟨1756115, by rfl⟩ : syracuseStep 2341487 = 3512231) B3512231
theorem B16882343 : Blo 1559477 16882343 := bstep (se 1 (by rfl) ⟨12661757, by rfl⟩ : syracuseStep 16882343 = 25323515) B25323515
theorem B10681001 : Blo 1559477 10681001 := bstep (se 2 (by rfl) ⟨4005375, by rfl⟩ : syracuseStep 10681001 = 8010751) B8010751
theorem B2341865 : Blo 1559477 2341865 := bstep (se 2 (by rfl) ⟨878199, by rfl⟩ : syracuseStep 2341865 = 1756399) B1756399
theorem B2341883 : Blo 1559477 2341883 := bstep (se 1 (by rfl) ⟨1756412, by rfl⟩ : syracuseStep 2341883 = 3512825) B3512825
theorem B15006829 : Blo 1559477 15006829 := bstep (se 3 (by rfl) ⟨2813780, by rfl⟩ : syracuseStep 15006829 = 5627561) B5627561
theorem B2342063 : Blo 1559477 2342063 := bstep (se 1 (by rfl) ⟨1756547, by rfl⟩ : syracuseStep 2342063 = 3513095) B3513095
theorem B3948223 : Blo 1559477 3948223 := bstep (se 1 (by rfl) ⟨2961167, by rfl⟩ : syracuseStep 3948223 = 5922335) B5922335
theorem B18988991 : Blo 1559477 18988991 := bstep (se 1 (by rfl) ⟨14241743, by rfl⟩ : syracuseStep 18988991 = 28483487) B28483487
theorem B5267807 : Blo 1559477 5267807 := bstep (se 1 (by rfl) ⟨3950855, by rfl⟩ : syracuseStep 5267807 = 7901711) B7901711
theorem B374948233 : Blo 1559477 374948233 := bstep (se 2 (by rfl) ⟨140605587, by rfl⟩ : syracuseStep 374948233 = 281211175) B281211175
theorem B13329629 : Blo 1559477 13329629 := bstep (se 3 (by rfl) ⟨2499305, by rfl⟩ : syracuseStep 13329629 = 4998611) B4998611
theorem B4998457 : Blo 1559477 4998457 := bstep (se 2 (by rfl) ⟨1874421, by rfl⟩ : syracuseStep 4998457 = 3748843) B3748843
theorem B7120667 : Blo 1559477 7120667 := bstep (se 1 (by rfl) ⟨5340500, by rfl⟩ : syracuseStep 7120667 = 10681001) B10681001
theorem B4441979 : Blo 1559477 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B6752423 : Blo 1559477 6752423 := bstep (se 1 (by rfl) ⟨5064317, by rfl⟩ : syracuseStep 6752423 = 10128635) B10128635
theorem B12659327 : Blo 1559477 12659327 := bstep (se 1 (by rfl) ⟨9494495, by rfl⟩ : syracuseStep 12659327 = 18988991) B18988991
theorem B3509063 : Blo 1559477 3509063 := bstep (se 1 (by rfl) ⟨2631797, by rfl⟩ : syracuseStep 3509063 = 5263595) B5263595
theorem B9489359 : Blo 1559477 9489359 := bstep (se 1 (by rfl) ⟨7117019, by rfl⟩ : syracuseStep 9489359 = 14234039) B14234039
theorem B2633215 : Blo 1559477 2633215 := bstep (se 1 (by rfl) ⟨1974911, by rfl⟩ : syracuseStep 2633215 = 3949823) B3949823
theorem B1560223 : Blo 1559477 1560223 := bstep (se 1 (by rfl) ⟨1170167, by rfl⟩ : syracuseStep 1560223 = 2340335) B2340335
theorem B146198239 : Blo 1559477 146198239 := bstep (se 1 (by rfl) ⟨109648679, by rfl⟩ : syracuseStep 146198239 = 219297359) B219297359
theorem B3509999 : Blo 1559477 3509999 := bstep (se 1 (by rfl) ⟨2632499, by rfl⟩ : syracuseStep 3509999 = 5264999) B5264999
theorem B1560411 : Blo 1559477 1560411 := bstep (se 1 (by rfl) ⟨1170308, by rfl⟩ : syracuseStep 1560411 = 2340617) B2340617
theorem B20009105 : Blo 1559477 20009105 := bstep (se 2 (by rfl) ⟨7503414, by rfl⟩ : syracuseStep 20009105 = 15006829) B15006829
theorem B3510431 : Blo 1559477 3510431 := bstep (se 1 (by rfl) ⟨2632823, by rfl⟩ : syracuseStep 3510431 = 5265647) B5265647
theorem B13324571 : Blo 1559477 13324571 := bstep (se 1 (by rfl) ⟨9993428, by rfl⟩ : syracuseStep 13324571 = 19986857) B19986857
theorem B1560991 : Blo 1559477 1560991 := bstep (se 1 (by rfl) ⟨1170743, by rfl⟩ : syracuseStep 1560991 = 2341487) B2341487
theorem B7500377 : Blo 1559477 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B1561243 : Blo 1559477 1561243 := bstep (se 1 (by rfl) ⟨1170932, by rfl⟩ : syracuseStep 1561243 = 2341865) B2341865
theorem B1561255 : Blo 1559477 1561255 := bstep (se 1 (by rfl) ⟨1170941, by rfl⟩ : syracuseStep 1561255 = 2341883) B2341883
theorem B1561375 : Blo 1559477 1561375 := bstep (se 1 (by rfl) ⟨1171031, by rfl⟩ : syracuseStep 1561375 = 2342063) B2342063
theorem B5264297 : Blo 1559477 5264297 := bstep (se 2 (by rfl) ⟨1974111, by rfl⟩ : syracuseStep 5264297 = 3948223) B3948223
theorem B22811777 : Blo 1559477 22811777 := bstep (se 2 (by rfl) ⟨8554416, by rfl⟩ : syracuseStep 22811777 = 17108833) B17108833
theorem B20280539 : Blo 1559477 20280539 := bstep (se 1 (by rfl) ⟨15210404, by rfl⟩ : syracuseStep 20280539 = 30420809) B30420809
theorem B2340071 : Blo 1559477 2340071 := bstep (se 1 (by rfl) ⟨1755053, by rfl⟩ : syracuseStep 2340071 = 3510107) B3510107
theorem B3511655 : Blo 1559477 3511655 := bstep (se 1 (by rfl) ⟨2633741, by rfl⟩ : syracuseStep 3511655 = 5267483) B5267483
theorem B2963567 : Blo 1559477 2963567 := bstep (se 1 (by rfl) ⟨2222675, by rfl⟩ : syracuseStep 2963567 = 4445351) B4445351
theorem B11843819 : Blo 1559477 11843819 := bstep (se 1 (by rfl) ⟨8882864, by rfl⟩ : syracuseStep 11843819 = 17765729) B17765729
theorem B3512915 : Blo 1559477 3512915 := bstep (se 1 (by rfl) ⟨2634686, by rfl⟩ : syracuseStep 3512915 = 5269373) B5269373
theorem B5921531 : Blo 1559477 5921531 := bstep (se 1 (by rfl) ⟨4441148, by rfl⟩ : syracuseStep 5921531 = 8882297) B8882297
theorem B5921819 : Blo 1559477 5921819 := bstep (se 1 (by rfl) ⟨4441364, by rfl⟩ : syracuseStep 5921819 = 8882729) B8882729
theorem B11254895 : Blo 1559477 11254895 := bstep (se 1 (by rfl) ⟨8441171, by rfl⟩ : syracuseStep 11254895 = 16882343) B16882343
theorem B5266943 : Blo 1559477 5266943 := bstep (se 1 (by rfl) ⟨3950207, by rfl⟩ : syracuseStep 5266943 = 7900415) B7900415
theorem B5922305 : Blo 1559477 5922305 := bstep (se 2 (by rfl) ⟨2220864, by rfl⟩ : syracuseStep 5922305 = 4441729) B4441729
theorem B18006461 : Blo 1559477 18006461 := bstep (se 3 (by rfl) ⟨3376211, by rfl⟩ : syracuseStep 18006461 = 6752423) B6752423
theorem B779723941 : Blo 1559477 779723941 := bstep (se 4 (by rfl) ⟨73099119, by rfl⟩ : syracuseStep 779723941 = 146198239) B146198239
theorem B8439551 : Blo 1559477 8439551 := bstep (se 1 (by rfl) ⟨6329663, by rfl⟩ : syracuseStep 8439551 = 12659327) B12659327
theorem B13339403 : Blo 1559477 13339403 := bstep (se 1 (by rfl) ⟨10004552, by rfl⟩ : syracuseStep 13339403 = 20009105) B20009105
theorem B8883047 : Blo 1559477 8883047 := bstep (se 1 (by rfl) ⟨6662285, by rfl⟩ : syracuseStep 8883047 = 13324571) B13324571
theorem B3509531 : Blo 1559477 3509531 := bstep (se 1 (by rfl) ⟨2632148, by rfl⟩ : syracuseStep 3509531 = 5264297) B5264297
theorem B15207851 : Blo 1559477 15207851 := bstep (se 1 (by rfl) ⟨11405888, by rfl⟩ : syracuseStep 15207851 = 22811777) B22811777
theorem B13520359 : Blo 1559477 13520359 := bstep (se 1 (by rfl) ⟨10140269, by rfl⟩ : syracuseStep 13520359 = 20280539) B20280539
theorem B1560047 : Blo 1559477 1560047 := bstep (se 1 (by rfl) ⟨1170035, by rfl⟩ : syracuseStep 1560047 = 2340071) B2340071
theorem B20001005 : Blo 1559477 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B6664609 : Blo 1559477 6664609 := bstep (se 2 (by rfl) ⟨2499228, by rfl⟩ : syracuseStep 6664609 = 4998457) B4998457
theorem B2339375 : Blo 1559477 2339375 := bstep (se 1 (by rfl) ⟨1754531, by rfl⟩ : syracuseStep 2339375 = 3509063) B3509063
theorem B3510953 : Blo 1559477 3510953 := bstep (se 2 (by rfl) ⟨1316607, by rfl⟩ : syracuseStep 3510953 = 2633215) B2633215
theorem B3511295 : Blo 1559477 3511295 := bstep (se 1 (by rfl) ⟨2633471, by rfl⟩ : syracuseStep 3511295 = 5266943) B5266943
theorem B2339999 : Blo 1559477 2339999 := bstep (se 1 (by rfl) ⟨1754999, by rfl⟩ : syracuseStep 2339999 = 3509999) B3509999
theorem B2340287 : Blo 1559477 2340287 := bstep (se 1 (by rfl) ⟨1755215, by rfl⟩ : syracuseStep 2340287 = 3510431) B3510431
theorem B7998895637 : Blo 1559477 7998895637 := bstep (se 6 (by rfl) ⟨187474116, by rfl⟩ : syracuseStep 7998895637 = 374948233) B374948233
theorem B3511871 : Blo 1559477 3511871 := bstep (se 1 (by rfl) ⟨2633903, by rfl⟩ : syracuseStep 3511871 = 5267807) B5267807
theorem B7902845 : Blo 1559477 7902845 := bstep (se 3 (by rfl) ⟨1481783, by rfl⟩ : syracuseStep 7902845 = 2963567) B2963567
theorem B8886419 : Blo 1559477 8886419 := bstep (se 1 (by rfl) ⟨6664814, by rfl⟩ : syracuseStep 8886419 = 13329629) B13329629
theorem B2341103 : Blo 1559477 2341103 := bstep (se 1 (by rfl) ⟨1755827, by rfl⟩ : syracuseStep 2341103 = 3511655) B3511655
theorem B7895879 : Blo 1559477 7895879 := bstep (se 1 (by rfl) ⟨5921909, by rfl⟩ : syracuseStep 7895879 = 11843819) B11843819
theorem B2341943 : Blo 1559477 2341943 := bstep (se 1 (by rfl) ⟨1756457, by rfl⟩ : syracuseStep 2341943 = 3512915) B3512915
theorem B3947687 : Blo 1559477 3947687 := bstep (se 1 (by rfl) ⟨2960765, by rfl⟩ : syracuseStep 3947687 = 5921531) B5921531
theorem B3947879 : Blo 1559477 3947879 := bstep (se 1 (by rfl) ⟨2960909, by rfl⟩ : syracuseStep 3947879 = 5921819) B5921819
theorem B18988445 : Blo 1559477 18988445 := bstep (se 3 (by rfl) ⟨3560333, by rfl⟩ : syracuseStep 18988445 = 7120667) B7120667
theorem B7503263 : Blo 1559477 7503263 := bstep (se 1 (by rfl) ⟨5627447, by rfl⟩ : syracuseStep 7503263 = 11254895) B11254895
theorem B11845277 : Blo 1559477 11845277 := bstep (se 3 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 11845277 = 4441979) B4441979
theorem B3948203 : Blo 1559477 3948203 := bstep (se 1 (by rfl) ⟨2961152, by rfl⟩ : syracuseStep 3948203 = 5922305) B5922305
theorem B25304957 : Blo 1559477 25304957 := bstep (se 3 (by rfl) ⟨4744679, by rfl⟩ : syracuseStep 25304957 = 9489359) B9489359
theorem B50635853 : Blo 1559477 50635853 := bstep (se 3 (by rfl) ⟨9494222, by rfl⟩ : syracuseStep 50635853 = 18988445) B18988445
theorem B5268563 : Blo 1559477 5268563 := bstep (se 1 (by rfl) ⟨3951422, by rfl⟩ : syracuseStep 5268563 = 7902845) B7902845
theorem B5924279 : Blo 1559477 5924279 := bstep (se 1 (by rfl) ⟨4443209, by rfl⟩ : syracuseStep 5924279 = 8886419) B8886419
theorem B1039631921 : Blo 1559477 1039631921 := bstep (se 2 (by rfl) ⟨389861970, by rfl⟩ : syracuseStep 1039631921 = 779723941) B779723941
theorem B2631791 : Blo 1559477 2631791 := bstep (se 1 (by rfl) ⟨1973843, by rfl⟩ : syracuseStep 2631791 = 3947687) B3947687
theorem B2631919 : Blo 1559477 2631919 := bstep (se 1 (by rfl) ⟨1973939, by rfl⟩ : syracuseStep 2631919 = 3947879) B3947879
theorem B2632135 : Blo 1559477 2632135 := bstep (se 1 (by rfl) ⟨1974101, by rfl⟩ : syracuseStep 2632135 = 3948203) B3948203
theorem B16869971 : Blo 1559477 16869971 := bstep (se 1 (by rfl) ⟨12652478, by rfl⟩ : syracuseStep 16869971 = 25304957) B25304957
theorem B12004307 : Blo 1559477 12004307 := bstep (se 1 (by rfl) ⟨9003230, by rfl⟩ : syracuseStep 12004307 = 18006461) B18006461
theorem B1559583 : Blo 1559477 1559583 := bstep (se 1 (by rfl) ⟨1169687, by rfl⟩ : syracuseStep 1559583 = 2339375) B2339375
theorem B1559999 : Blo 1559477 1559999 := bstep (se 1 (by rfl) ⟨1169999, by rfl⟩ : syracuseStep 1559999 = 2339999) B2339999
theorem B1560191 : Blo 1559477 1560191 := bstep (se 1 (by rfl) ⟨1170143, by rfl⟩ : syracuseStep 1560191 = 2340287) B2340287
theorem B1560735 : Blo 1559477 1560735 := bstep (se 1 (by rfl) ⟨1170551, by rfl⟩ : syracuseStep 1560735 = 2341103) B2341103
theorem B8892935 : Blo 1559477 8892935 := bstep (se 1 (by rfl) ⟨6669701, by rfl⟩ : syracuseStep 8892935 = 13339403) B13339403
theorem B5263919 : Blo 1559477 5263919 := bstep (se 1 (by rfl) ⟨3947939, by rfl⟩ : syracuseStep 5263919 = 7895879) B7895879
theorem B18027145 : Blo 1559477 18027145 := bstep (se 2 (by rfl) ⟨6760179, by rfl⟩ : syracuseStep 18027145 = 13520359) B13520359
theorem B1561295 : Blo 1559477 1561295 := bstep (se 1 (by rfl) ⟨1170971, by rfl⟩ : syracuseStep 1561295 = 2341943) B2341943
theorem B2339687 : Blo 1559477 2339687 := bstep (se 1 (by rfl) ⟨1754765, by rfl⟩ : syracuseStep 2339687 = 3509531) B3509531
theorem B5002175 : Blo 1559477 5002175 := bstep (se 1 (by rfl) ⟨3751631, by rfl⟩ : syracuseStep 5002175 = 7503263) B7503263
theorem B10138567 : Blo 1559477 10138567 := bstep (se 1 (by rfl) ⟨7603925, by rfl⟩ : syracuseStep 10138567 = 15207851) B15207851
theorem B13334003 : Blo 1559477 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B2340635 : Blo 1559477 2340635 := bstep (se 1 (by rfl) ⟨1755476, by rfl⟩ : syracuseStep 2340635 = 3510953) B3510953
theorem B8886145 : Blo 1559477 8886145 := bstep (se 2 (by rfl) ⟨3332304, by rfl⟩ : syracuseStep 8886145 = 6664609) B6664609
theorem B2340863 : Blo 1559477 2340863 := bstep (se 1 (by rfl) ⟨1755647, by rfl⟩ : syracuseStep 2340863 = 3511295) B3511295
theorem B5332597091 : Blo 1559477 5332597091 := bstep (se 1 (by rfl) ⟨3999447818, by rfl⟩ : syracuseStep 5332597091 = 7998895637) B7998895637
theorem B2341247 : Blo 1559477 2341247 := bstep (se 1 (by rfl) ⟨1755935, by rfl⟩ : syracuseStep 2341247 = 3511871) B3511871
theorem B5626367 : Blo 1559477 5626367 := bstep (se 1 (by rfl) ⟨4219775, by rfl⟩ : syracuseStep 5626367 = 8439551) B8439551
theorem B5922031 : Blo 1559477 5922031 := bstep (se 1 (by rfl) ⟨4441523, by rfl⟩ : syracuseStep 5922031 = 8883047) B8883047
theorem B7896851 : Blo 1559477 7896851 := bstep (se 1 (by rfl) ⟨5922638, by rfl⟩ : syracuseStep 7896851 = 11845277) B11845277
theorem B3334783 : Blo 1559477 3334783 := bstep (se 1 (by rfl) ⟨2501087, by rfl⟩ : syracuseStep 3334783 = 5002175) B5002175
theorem B24036193 : Blo 1559477 24036193 := bstep (se 2 (by rfl) ⟨9013572, by rfl⟩ : syracuseStep 24036193 = 18027145) B18027145
theorem B3949519 : Blo 1559477 3949519 := bstep (se 1 (by rfl) ⟨2962139, by rfl⟩ : syracuseStep 3949519 = 5924279) B5924279
theorem B8889335 : Blo 1559477 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B13518089 : Blo 1559477 13518089 := bstep (se 2 (by rfl) ⟨5069283, by rfl⟩ : syracuseStep 13518089 = 10138567) B10138567
theorem B1754527 : Blo 1559477 1754527 := bstep (se 1 (by rfl) ⟨1315895, by rfl⟩ : syracuseStep 1754527 = 2631791) B2631791
theorem B11848193 : Blo 1559477 11848193 := bstep (se 2 (by rfl) ⟨4443072, by rfl⟩ : syracuseStep 11848193 = 8886145) B8886145
theorem B3509225 : Blo 1559477 3509225 := bstep (se 2 (by rfl) ⟨1315959, by rfl⟩ : syracuseStep 3509225 = 2631919) B2631919
theorem B3509279 : Blo 1559477 3509279 := bstep (se 1 (by rfl) ⟨2631959, by rfl⟩ : syracuseStep 3509279 = 5263919) B5263919
theorem B1559791 : Blo 1559477 1559791 := bstep (se 1 (by rfl) ⟨1169843, by rfl⟩ : syracuseStep 1559791 = 2339687) B2339687
theorem B3509513 : Blo 1559477 3509513 := bstep (se 2 (by rfl) ⟨1316067, by rfl⟩ : syracuseStep 3509513 = 2632135) B2632135
theorem B693087947 : Blo 1559477 693087947 := bstep (se 1 (by rfl) ⟨519815960, by rfl⟩ : syracuseStep 693087947 = 1039631921) B1039631921
theorem B1560423 : Blo 1559477 1560423 := bstep (se 1 (by rfl) ⟨1170317, by rfl⟩ : syracuseStep 1560423 = 2340635) B2340635
theorem B1560575 : Blo 1559477 1560575 := bstep (se 1 (by rfl) ⟨1170431, by rfl⟩ : syracuseStep 1560575 = 2340863) B2340863
theorem B1560831 : Blo 1559477 1560831 := bstep (se 1 (by rfl) ⟨1170623, by rfl⟩ : syracuseStep 1560831 = 2341247) B2341247
theorem B5264567 : Blo 1559477 5264567 := bstep (se 1 (by rfl) ⟨3948425, by rfl⟩ : syracuseStep 5264567 = 7896851) B7896851
theorem B5928623 : Blo 1559477 5928623 := bstep (se 1 (by rfl) ⟨4446467, by rfl⟩ : syracuseStep 5928623 = 8892935) B8892935
theorem B33757235 : Blo 1559477 33757235 := bstep (se 1 (by rfl) ⟨25317926, by rfl⟩ : syracuseStep 33757235 = 50635853) B50635853
theorem B3512375 : Blo 1559477 3512375 := bstep (se 1 (by rfl) ⟨2634281, by rfl⟩ : syracuseStep 3512375 = 5268563) B5268563
theorem B3555064727 : Blo 1559477 3555064727 := bstep (se 1 (by rfl) ⟨2666298545, by rfl⟩ : syracuseStep 3555064727 = 5332597091) B5332597091
theorem B7896041 : Blo 1559477 7896041 := bstep (se 2 (by rfl) ⟨2961015, by rfl⟩ : syracuseStep 7896041 = 5922031) B5922031
theorem B3750911 : Blo 1559477 3750911 := bstep (se 1 (by rfl) ⟨2813183, by rfl⟩ : syracuseStep 3750911 = 5626367) B5626367
theorem B11246647 : Blo 1559477 11246647 := bstep (se 1 (by rfl) ⟨8434985, by rfl⟩ : syracuseStep 11246647 = 16869971) B16869971
theorem B8002871 : Blo 1559477 8002871 := bstep (se 1 (by rfl) ⟨6002153, by rfl⟩ : syracuseStep 8002871 = 12004307) B12004307
theorem B9012059 : Blo 1559477 9012059 := bstep (se 1 (by rfl) ⟨6759044, by rfl⟩ : syracuseStep 9012059 = 13518089) B13518089
theorem B32048257 : Blo 1559477 32048257 := bstep (se 2 (by rfl) ⟨12018096, by rfl⟩ : syracuseStep 32048257 = 24036193) B24036193
theorem B22504823 : Blo 1559477 22504823 := bstep (se 1 (by rfl) ⟨16878617, by rfl⟩ : syracuseStep 22504823 = 33757235) B33757235
theorem B7898795 : Blo 1559477 7898795 := bstep (se 1 (by rfl) ⟨5924096, by rfl⟩ : syracuseStep 7898795 = 11848193) B11848193
theorem B2500607 : Blo 1559477 2500607 := bstep (se 1 (by rfl) ⟨1875455, by rfl⟩ : syracuseStep 2500607 = 3750911) B3750911
theorem B5335247 : Blo 1559477 5335247 := bstep (se 1 (by rfl) ⟨4001435, by rfl⟩ : syracuseStep 5335247 = 8002871) B8002871
theorem B5926223 : Blo 1559477 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B3509711 : Blo 1559477 3509711 := bstep (se 1 (by rfl) ⟨2632283, by rfl⟩ : syracuseStep 3509711 = 5264567) B5264567
theorem B3952415 : Blo 1559477 3952415 := bstep (se 1 (by rfl) ⟨2964311, by rfl⟩ : syracuseStep 3952415 = 5928623) B5928623
theorem B14995529 : Blo 1559477 14995529 := bstep (se 2 (by rfl) ⟨5623323, by rfl⟩ : syracuseStep 14995529 = 11246647) B11246647
theorem B2339369 : Blo 1559477 2339369 := bstep (se 2 (by rfl) ⟨877263, by rfl⟩ : syracuseStep 2339369 = 1754527) B1754527
theorem B2339483 : Blo 1559477 2339483 := bstep (se 1 (by rfl) ⟨1754612, by rfl⟩ : syracuseStep 2339483 = 3509225) B3509225
theorem B5264027 : Blo 1559477 5264027 := bstep (se 1 (by rfl) ⟨3948020, by rfl⟩ : syracuseStep 5264027 = 7896041) B7896041
theorem B2339519 : Blo 1559477 2339519 := bstep (se 1 (by rfl) ⟨1754639, by rfl⟩ : syracuseStep 2339519 = 3509279) B3509279
theorem B2339675 : Blo 1559477 2339675 := bstep (se 1 (by rfl) ⟨1754756, by rfl⟩ : syracuseStep 2339675 = 3509513) B3509513
theorem B462058631 : Blo 1559477 462058631 := bstep (se 1 (by rfl) ⟨346543973, by rfl⟩ : syracuseStep 462058631 = 693087947) B693087947
theorem B4446377 : Blo 1559477 4446377 := bstep (se 2 (by rfl) ⟨1667391, by rfl⟩ : syracuseStep 4446377 = 3334783) B3334783
theorem B5266025 : Blo 1559477 5266025 := bstep (se 2 (by rfl) ⟨1974759, by rfl⟩ : syracuseStep 5266025 = 3949519) B3949519
theorem B2341583 : Blo 1559477 2341583 := bstep (se 1 (by rfl) ⟨1756187, by rfl⟩ : syracuseStep 2341583 = 3512375) B3512375
theorem B2370043151 : Blo 1559477 2370043151 := bstep (se 1 (by rfl) ⟨1777532363, by rfl⟩ : syracuseStep 2370043151 = 3555064727) B3555064727
theorem B42731009 : Blo 1559477 42731009 := bstep (se 2 (by rfl) ⟨16024128, by rfl⟩ : syracuseStep 42731009 = 32048257) B32048257
theorem B3950815 : Blo 1559477 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B9997019 : Blo 1559477 9997019 := bstep (se 1 (by rfl) ⟨7497764, by rfl⟩ : syracuseStep 9997019 = 14995529) B14995529
theorem B1559579 : Blo 1559477 1559579 := bstep (se 1 (by rfl) ⟨1169684, by rfl⟩ : syracuseStep 1559579 = 2339369) B2339369
theorem B1559655 : Blo 1559477 1559655 := bstep (se 1 (by rfl) ⟨1169741, by rfl⟩ : syracuseStep 1559655 = 2339483) B2339483
theorem B3509351 : Blo 1559477 3509351 := bstep (se 1 (by rfl) ⟨2632013, by rfl⟩ : syracuseStep 3509351 = 5264027) B5264027
theorem B1559679 : Blo 1559477 1559679 := bstep (se 1 (by rfl) ⟨1169759, by rfl⟩ : syracuseStep 1559679 = 2339519) B2339519
theorem B1559783 : Blo 1559477 1559783 := bstep (se 1 (by rfl) ⟨1169837, by rfl⟩ : syracuseStep 1559783 = 2339675) B2339675
theorem B6008039 : Blo 1559477 6008039 := bstep (se 1 (by rfl) ⟨4506029, by rfl⟩ : syracuseStep 6008039 = 9012059) B9012059
theorem B308039087 : Blo 1559477 308039087 := bstep (se 1 (by rfl) ⟨231029315, by rfl⟩ : syracuseStep 308039087 = 462058631) B462058631
theorem B15003215 : Blo 1559477 15003215 := bstep (se 1 (by rfl) ⟨11252411, by rfl⟩ : syracuseStep 15003215 = 22504823) B22504823
theorem B1667071 : Blo 1559477 1667071 := bstep (se 1 (by rfl) ⟨1250303, by rfl⟩ : syracuseStep 1667071 = 2500607) B2500607
theorem B3510683 : Blo 1559477 3510683 := bstep (se 1 (by rfl) ⟨2633012, by rfl⟩ : syracuseStep 3510683 = 5266025) B5266025
theorem B1561055 : Blo 1559477 1561055 := bstep (se 1 (by rfl) ⟨1170791, by rfl⟩ : syracuseStep 1561055 = 2341583) B2341583
theorem B1580028767 : Blo 1559477 1580028767 := bstep (se 1 (by rfl) ⟨1185021575, by rfl⟩ : syracuseStep 1580028767 = 2370043151) B2370043151
theorem B2339807 : Blo 1559477 2339807 := bstep (se 1 (by rfl) ⟨1754855, by rfl⟩ : syracuseStep 2339807 = 3509711) B3509711
theorem B2634943 : Blo 1559477 2634943 := bstep (se 1 (by rfl) ⟨1976207, by rfl⟩ : syracuseStep 2634943 = 3952415) B3952415
theorem B14227325 : Blo 1559477 14227325 := bstep (se 3 (by rfl) ⟨2667623, by rfl⟩ : syracuseStep 14227325 = 5335247) B5335247
theorem B5265863 : Blo 1559477 5265863 := bstep (se 1 (by rfl) ⟨3949397, by rfl⟩ : syracuseStep 5265863 = 7898795) B7898795
theorem B2964251 : Blo 1559477 2964251 := bstep (se 1 (by rfl) ⟨2223188, by rfl⟩ : syracuseStep 2964251 = 4446377) B4446377
theorem B5267753 : Blo 1559477 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B1053352511 : Blo 1559477 1053352511 := bstep (se 1 (by rfl) ⟨790014383, by rfl⟩ : syracuseStep 1053352511 = 1580028767) B1580028767
theorem B1976167 : Blo 1559477 1976167 := bstep (se 1 (by rfl) ⟨1482125, by rfl⟩ : syracuseStep 1976167 = 2964251) B2964251
theorem B205359391 : Blo 1559477 205359391 := bstep (se 1 (by rfl) ⟨154019543, by rfl⟩ : syracuseStep 205359391 = 308039087) B308039087
theorem B8891045 : Blo 1559477 8891045 := bstep (se 4 (by rfl) ⟨833535, by rfl⟩ : syracuseStep 8891045 = 1667071) B1667071
theorem B1559871 : Blo 1559477 1559871 := bstep (se 1 (by rfl) ⟨1169903, by rfl⟩ : syracuseStep 1559871 = 2339807) B2339807
theorem B28487339 : Blo 1559477 28487339 := bstep (se 1 (by rfl) ⟨21365504, by rfl⟩ : syracuseStep 28487339 = 42731009) B42731009
theorem B3510575 : Blo 1559477 3510575 := bstep (se 1 (by rfl) ⟨2632931, by rfl⟩ : syracuseStep 3510575 = 5265863) B5265863
theorem B6664679 : Blo 1559477 6664679 := bstep (se 1 (by rfl) ⟨4998509, by rfl⟩ : syracuseStep 6664679 = 9997019) B9997019
theorem B2339567 : Blo 1559477 2339567 := bstep (se 1 (by rfl) ⟨1754675, by rfl⟩ : syracuseStep 2339567 = 3509351) B3509351
theorem B2340455 : Blo 1559477 2340455 := bstep (se 1 (by rfl) ⟨1755341, by rfl⟩ : syracuseStep 2340455 = 3510683) B3510683
theorem B9484883 : Blo 1559477 9484883 := bstep (se 1 (by rfl) ⟨7113662, by rfl⟩ : syracuseStep 9484883 = 14227325) B14227325
theorem B3513257 : Blo 1559477 3513257 := bstep (se 2 (by rfl) ⟨1317471, by rfl⟩ : syracuseStep 3513257 = 2634943) B2634943
theorem B4005359 : Blo 1559477 4005359 := bstep (se 1 (by rfl) ⟨3004019, by rfl⟩ : syracuseStep 4005359 = 6008039) B6008039
theorem B10002143 : Blo 1559477 10002143 := bstep (se 1 (by rfl) ⟨7501607, by rfl⟩ : syracuseStep 10002143 = 15003215) B15003215
theorem B702235007 : Blo 1559477 702235007 := bstep (se 1 (by rfl) ⟨526676255, by rfl⟩ : syracuseStep 702235007 = 1053352511) B1053352511
theorem B18991559 : Blo 1559477 18991559 := bstep (se 1 (by rfl) ⟨14243669, by rfl⟩ : syracuseStep 18991559 = 28487339) B28487339
theorem B4443119 : Blo 1559477 4443119 := bstep (se 1 (by rfl) ⟨3332339, by rfl⟩ : syracuseStep 4443119 = 6664679) B6664679
theorem B273812521 : Blo 1559477 273812521 := bstep (se 2 (by rfl) ⟨102679695, by rfl⟩ : syracuseStep 273812521 = 205359391) B205359391
theorem B1559711 : Blo 1559477 1559711 := bstep (se 1 (by rfl) ⟨1169783, by rfl⟩ : syracuseStep 1559711 = 2339567) B2339567
theorem B1560303 : Blo 1559477 1560303 := bstep (se 1 (by rfl) ⟨1170227, by rfl⟩ : syracuseStep 1560303 = 2340455) B2340455
theorem B5927363 : Blo 1559477 5927363 := bstep (se 1 (by rfl) ⟨4445522, by rfl⟩ : syracuseStep 5927363 = 8891045) B8891045
theorem B2634889 : Blo 1559477 2634889 := bstep (se 2 (by rfl) ⟨988083, by rfl⟩ : syracuseStep 2634889 = 1976167) B1976167
theorem B3511835 : Blo 1559477 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B2340383 : Blo 1559477 2340383 := bstep (se 1 (by rfl) ⟨1755287, by rfl⟩ : syracuseStep 2340383 = 3510575) B3510575
theorem B6323255 : Blo 1559477 6323255 := bstep (se 1 (by rfl) ⟨4742441, by rfl⟩ : syracuseStep 6323255 = 9484883) B9484883
theorem B2342171 : Blo 1559477 2342171 := bstep (se 1 (by rfl) ⟨1756628, by rfl⟩ : syracuseStep 2342171 = 3513257) B3513257
theorem B2670239 : Blo 1559477 2670239 := bstep (se 1 (by rfl) ⟨2002679, by rfl⟩ : syracuseStep 2670239 = 4005359) B4005359
theorem B6668095 : Blo 1559477 6668095 := bstep (se 1 (by rfl) ⟨5001071, by rfl⟩ : syracuseStep 6668095 = 10002143) B10002143
theorem B468156671 : Blo 1559477 468156671 := bstep (se 1 (by rfl) ⟨351117503, by rfl⟩ : syracuseStep 468156671 = 702235007) B702235007
theorem B8890793 : Blo 1559477 8890793 := bstep (se 2 (by rfl) ⟨3334047, by rfl⟩ : syracuseStep 8890793 = 6668095) B6668095
theorem B1780159 : Blo 1559477 1780159 := bstep (se 1 (by rfl) ⟨1335119, by rfl⟩ : syracuseStep 1780159 = 2670239) B2670239
theorem B3951575 : Blo 1559477 3951575 := bstep (se 1 (by rfl) ⟨2963681, by rfl⟩ : syracuseStep 3951575 = 5927363) B5927363
theorem B1560255 : Blo 1559477 1560255 := bstep (se 1 (by rfl) ⟨1170191, by rfl⟩ : syracuseStep 1560255 = 2340383) B2340383
theorem B12661039 : Blo 1559477 12661039 := bstep (se 1 (by rfl) ⟨9495779, by rfl⟩ : syracuseStep 12661039 = 18991559) B18991559
theorem B2962079 : Blo 1559477 2962079 := bstep (se 1 (by rfl) ⟨2221559, by rfl⟩ : syracuseStep 2962079 = 4443119) B4443119
theorem B4215503 : Blo 1559477 4215503 := bstep (se 1 (by rfl) ⟨3161627, by rfl⟩ : syracuseStep 4215503 = 6323255) B6323255
theorem B1561447 : Blo 1559477 1561447 := bstep (se 1 (by rfl) ⟨1171085, by rfl⟩ : syracuseStep 1561447 = 2342171) B2342171
theorem B2341223 : Blo 1559477 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B365083361 : Blo 1559477 365083361 := bstep (se 2 (by rfl) ⟨136906260, by rfl⟩ : syracuseStep 365083361 = 273812521) B273812521
theorem B3513185 : Blo 1559477 3513185 := bstep (se 2 (by rfl) ⟨1317444, by rfl⟩ : syracuseStep 3513185 = 2634889) B2634889
theorem B1974719 : Blo 1559477 1974719 := bstep (se 1 (by rfl) ⟨1481039, by rfl⟩ : syracuseStep 1974719 = 2962079) B2962079
theorem B11241341 : Blo 1559477 11241341 := bstep (se 3 (by rfl) ⟨2107751, by rfl⟩ : syracuseStep 11241341 = 4215503) B4215503
theorem B1560815 : Blo 1559477 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B5927195 : Blo 1559477 5927195 := bstep (se 1 (by rfl) ⟨4445396, by rfl⟩ : syracuseStep 5927195 = 8890793) B8890793
theorem B243388907 : Blo 1559477 243388907 := bstep (se 1 (by rfl) ⟨182541680, by rfl⟩ : syracuseStep 243388907 = 365083361) B365083361
theorem B2634383 : Blo 1559477 2634383 := bstep (se 1 (by rfl) ⟨1975787, by rfl⟩ : syracuseStep 2634383 = 3951575) B3951575
theorem B312104447 : Blo 1559477 312104447 := bstep (se 1 (by rfl) ⟨234078335, by rfl⟩ : syracuseStep 312104447 = 468156671) B468156671
theorem B16881385 : Blo 1559477 16881385 := bstep (se 2 (by rfl) ⟨6330519, by rfl⟩ : syracuseStep 16881385 = 12661039) B12661039
theorem B2373545 : Blo 1559477 2373545 := bstep (se 2 (by rfl) ⟨890079, by rfl⟩ : syracuseStep 2373545 = 1780159) B1780159
theorem B2342123 : Blo 1559477 2342123 := bstep (se 1 (by rfl) ⟨1756592, by rfl⟩ : syracuseStep 2342123 = 3513185) B3513185
theorem B162259271 : Blo 1559477 162259271 := bstep (se 1 (by rfl) ⟨121694453, by rfl⟩ : syracuseStep 162259271 = 243388907) B243388907
theorem B208069631 : Blo 1559477 208069631 := bstep (se 1 (by rfl) ⟨156052223, by rfl⟩ : syracuseStep 208069631 = 312104447) B312104447
theorem B1582363 : Blo 1559477 1582363 := bstep (se 1 (by rfl) ⟨1186772, by rfl⟩ : syracuseStep 1582363 = 2373545) B2373545
theorem B3951463 : Blo 1559477 3951463 := bstep (se 1 (by rfl) ⟨2963597, by rfl⟩ : syracuseStep 3951463 = 5927195) B5927195
theorem B1756255 : Blo 1559477 1756255 := bstep (se 1 (by rfl) ⟨1317191, by rfl⟩ : syracuseStep 1756255 = 2634383) B2634383
theorem B1561415 : Blo 1559477 1561415 := bstep (se 1 (by rfl) ⟨1171061, by rfl⟩ : syracuseStep 1561415 = 2342123) B2342123
theorem B22508513 : Blo 1559477 22508513 := bstep (se 2 (by rfl) ⟨8440692, by rfl⟩ : syracuseStep 22508513 = 16881385) B16881385
theorem B5265917 : Blo 1559477 5265917 := bstep (se 3 (by rfl) ⟨987359, by rfl⟩ : syracuseStep 5265917 = 1974719) B1974719
theorem B7494227 : Blo 1559477 7494227 := bstep (se 1 (by rfl) ⟨5620670, by rfl⟩ : syracuseStep 7494227 = 11241341) B11241341
theorem B5268617 : Blo 1559477 5268617 := bstep (se 2 (by rfl) ⟨1975731, by rfl⟩ : syracuseStep 5268617 = 3951463) B3951463
theorem B3510611 : Blo 1559477 3510611 := bstep (se 1 (by rfl) ⟨2632958, by rfl⟩ : syracuseStep 3510611 = 5265917) B5265917
theorem B2109817 : Blo 1559477 2109817 := bstep (se 2 (by rfl) ⟨791181, by rfl⟩ : syracuseStep 2109817 = 1582363) B1582363
theorem B108172847 : Blo 1559477 108172847 := bstep (se 1 (by rfl) ⟨81129635, by rfl⟩ : syracuseStep 108172847 = 162259271) B162259271
theorem B15005675 : Blo 1559477 15005675 := bstep (se 1 (by rfl) ⟨11254256, by rfl⟩ : syracuseStep 15005675 = 22508513) B22508513
theorem B138713087 : Blo 1559477 138713087 := bstep (se 1 (by rfl) ⟨104034815, by rfl⟩ : syracuseStep 138713087 = 208069631) B208069631
theorem B2341673 : Blo 1559477 2341673 := bstep (se 2 (by rfl) ⟨878127, by rfl⟩ : syracuseStep 2341673 = 1756255) B1756255
theorem B4996151 : Blo 1559477 4996151 := bstep (se 1 (by rfl) ⟨3747113, by rfl⟩ : syracuseStep 4996151 = 7494227) B7494227
theorem B72115231 : Blo 1559477 72115231 := bstep (se 1 (by rfl) ⟨54086423, by rfl⟩ : syracuseStep 72115231 = 108172847) B108172847
theorem B10003783 : Blo 1559477 10003783 := bstep (se 1 (by rfl) ⟨7502837, by rfl⟩ : syracuseStep 10003783 = 15005675) B15005675
theorem B1561115 : Blo 1559477 1561115 := bstep (se 1 (by rfl) ⟨1170836, by rfl⟩ : syracuseStep 1561115 = 2341673) B2341673
theorem B11252357 : Blo 1559477 11252357 := bstep (se 4 (by rfl) ⟨1054908, by rfl⟩ : syracuseStep 11252357 = 2109817) B2109817
theorem B3330767 : Blo 1559477 3330767 := bstep (se 1 (by rfl) ⟨2498075, by rfl⟩ : syracuseStep 3330767 = 4996151) B4996151
theorem B2340407 : Blo 1559477 2340407 := bstep (se 1 (by rfl) ⟨1755305, by rfl⟩ : syracuseStep 2340407 = 3510611) B3510611
theorem B3512411 : Blo 1559477 3512411 := bstep (se 1 (by rfl) ⟨2634308, by rfl⟩ : syracuseStep 3512411 = 5268617) B5268617
theorem B369901565 : Blo 1559477 369901565 := bstep (se 3 (by rfl) ⟨69356543, by rfl⟩ : syracuseStep 369901565 = 138713087) B138713087
theorem B13338377 : Blo 1559477 13338377 := bstep (se 2 (by rfl) ⟨5001891, by rfl⟩ : syracuseStep 13338377 = 10003783) B10003783
theorem B8882045 : Blo 1559477 8882045 := bstep (se 3 (by rfl) ⟨1665383, by rfl⟩ : syracuseStep 8882045 = 3330767) B3330767
theorem B1560271 : Blo 1559477 1560271 := bstep (se 1 (by rfl) ⟨1170203, by rfl⟩ : syracuseStep 1560271 = 2340407) B2340407
theorem B96153641 : Blo 1559477 96153641 := bstep (se 2 (by rfl) ⟨36057615, by rfl⟩ : syracuseStep 96153641 = 72115231) B72115231
theorem B246601043 : Blo 1559477 246601043 := bstep (se 1 (by rfl) ⟨184950782, by rfl⟩ : syracuseStep 246601043 = 369901565) B369901565
theorem B7501571 : Blo 1559477 7501571 := bstep (se 1 (by rfl) ⟨5626178, by rfl⟩ : syracuseStep 7501571 = 11252357) B11252357
theorem B2341607 : Blo 1559477 2341607 := bstep (se 1 (by rfl) ⟨1756205, by rfl⟩ : syracuseStep 2341607 = 3512411) B3512411
theorem B64102427 : Blo 1559477 64102427 := bstep (se 1 (by rfl) ⟨48076820, by rfl⟩ : syracuseStep 64102427 = 96153641) B96153641
theorem B164400695 : Blo 1559477 164400695 := bstep (se 1 (by rfl) ⟨123300521, by rfl⟩ : syracuseStep 164400695 = 246601043) B246601043
theorem B5001047 : Blo 1559477 5001047 := bstep (se 1 (by rfl) ⟨3750785, by rfl⟩ : syracuseStep 5001047 = 7501571) B7501571
theorem B8892251 : Blo 1559477 8892251 := bstep (se 1 (by rfl) ⟨6669188, by rfl⟩ : syracuseStep 8892251 = 13338377) B13338377
theorem B1561071 : Blo 1559477 1561071 := bstep (se 1 (by rfl) ⟨1170803, by rfl⟩ : syracuseStep 1561071 = 2341607) B2341607
theorem B5921363 : Blo 1559477 5921363 := bstep (se 1 (by rfl) ⟨4441022, by rfl⟩ : syracuseStep 5921363 = 8882045) B8882045
theorem B5928167 : Blo 1559477 5928167 := bstep (se 1 (by rfl) ⟨4446125, by rfl⟩ : syracuseStep 5928167 = 8892251) B8892251
theorem B42734951 : Blo 1559477 42734951 := bstep (se 1 (by rfl) ⟨32051213, by rfl⟩ : syracuseStep 42734951 = 64102427) B64102427
theorem B3947575 : Blo 1559477 3947575 := bstep (se 1 (by rfl) ⟨2960681, by rfl⟩ : syracuseStep 3947575 = 5921363) B5921363
theorem B109600463 : Blo 1559477 109600463 := bstep (se 1 (by rfl) ⟨82200347, by rfl⟩ : syracuseStep 109600463 = 164400695) B164400695
theorem B3334031 : Blo 1559477 3334031 := bstep (se 1 (by rfl) ⟨2500523, by rfl⟩ : syracuseStep 3334031 = 5001047) B5001047
theorem B292267901 : Blo 1559477 292267901 := bstep (se 3 (by rfl) ⟨54800231, by rfl⟩ : syracuseStep 292267901 = 109600463) B109600463
theorem B2222687 : Blo 1559477 2222687 := bstep (se 1 (by rfl) ⟨1667015, by rfl⟩ : syracuseStep 2222687 = 3334031) B3334031
theorem B3952111 : Blo 1559477 3952111 := bstep (se 1 (by rfl) ⟨2964083, by rfl⟩ : syracuseStep 3952111 = 5928167) B5928167
theorem B5263433 : Blo 1559477 5263433 := bstep (se 2 (by rfl) ⟨1973787, by rfl⟩ : syracuseStep 5263433 = 3947575) B3947575
theorem B28489967 : Blo 1559477 28489967 := bstep (se 1 (by rfl) ⟨21367475, by rfl⟩ : syracuseStep 28489967 = 42734951) B42734951
theorem B5269481 : Blo 1559477 5269481 := bstep (se 2 (by rfl) ⟨1976055, by rfl⟩ : syracuseStep 5269481 = 3952111) B3952111
theorem B3508955 : Blo 1559477 3508955 := bstep (se 1 (by rfl) ⟨2631716, by rfl⟩ : syracuseStep 3508955 = 5263433) B5263433
theorem B18993311 : Blo 1559477 18993311 := bstep (se 1 (by rfl) ⟨14244983, by rfl⟩ : syracuseStep 18993311 = 28489967) B28489967
theorem B5927165 : Blo 1559477 5927165 := bstep (se 3 (by rfl) ⟨1111343, by rfl⟩ : syracuseStep 5927165 = 2222687) B2222687
theorem B194845267 : Blo 1559477 194845267 := bstep (se 1 (by rfl) ⟨146133950, by rfl⟩ : syracuseStep 194845267 = 292267901) B292267901
theorem B259793689 : Blo 1559477 259793689 := bstep (se 2 (by rfl) ⟨97422633, by rfl⟩ : syracuseStep 259793689 = 194845267) B194845267
theorem B3951443 : Blo 1559477 3951443 := bstep (se 1 (by rfl) ⟨2963582, by rfl⟩ : syracuseStep 3951443 = 5927165) B5927165
theorem B2339303 : Blo 1559477 2339303 := bstep (se 1 (by rfl) ⟨1754477, by rfl⟩ : syracuseStep 2339303 = 3508955) B3508955
theorem B12662207 : Blo 1559477 12662207 := bstep (se 1 (by rfl) ⟨9496655, by rfl⟩ : syracuseStep 12662207 = 18993311) B18993311
theorem B3512987 : Blo 1559477 3512987 := bstep (se 1 (by rfl) ⟨2634740, by rfl⟩ : syracuseStep 3512987 = 5269481) B5269481
theorem B346391585 : Blo 1559477 346391585 := bstep (se 2 (by rfl) ⟨129896844, by rfl⟩ : syracuseStep 346391585 = 259793689) B259793689
theorem B1559535 : Blo 1559477 1559535 := bstep (se 1 (by rfl) ⟨1169651, by rfl⟩ : syracuseStep 1559535 = 2339303) B2339303
theorem B8441471 : Blo 1559477 8441471 := bstep (se 1 (by rfl) ⟨6331103, by rfl⟩ : syracuseStep 8441471 = 12662207) B12662207
theorem B2634295 : Blo 1559477 2634295 := bstep (se 1 (by rfl) ⟨1975721, by rfl⟩ : syracuseStep 2634295 = 3951443) B3951443
theorem B2341991 : Blo 1559477 2341991 := bstep (se 1 (by rfl) ⟨1756493, by rfl⟩ : syracuseStep 2341991 = 3512987) B3512987
theorem B230927723 : Blo 1559477 230927723 := bstep (se 1 (by rfl) ⟨173195792, by rfl⟩ : syracuseStep 230927723 = 346391585) B346391585
theorem B1561327 : Blo 1559477 1561327 := bstep (se 1 (by rfl) ⟨1170995, by rfl⟩ : syracuseStep 1561327 = 2341991) B2341991
theorem B3512393 : Blo 1559477 3512393 := bstep (se 2 (by rfl) ⟨1317147, by rfl⟩ : syracuseStep 3512393 = 2634295) B2634295
theorem B5627647 : Blo 1559477 5627647 := bstep (se 1 (by rfl) ⟨4220735, by rfl⟩ : syracuseStep 5627647 = 8441471) B8441471
theorem B2341595 : Blo 1559477 2341595 := bstep (se 1 (by rfl) ⟨1756196, by rfl⟩ : syracuseStep 2341595 = 3512393) B3512393
theorem B153951815 : Blo 1559477 153951815 := bstep (se 1 (by rfl) ⟨115463861, by rfl⟩ : syracuseStep 153951815 = 230927723) B230927723
theorem B7503529 : Blo 1559477 7503529 := bstep (se 2 (by rfl) ⟨2813823, by rfl⟩ : syracuseStep 7503529 = 5627647) B5627647
theorem B10004705 : Blo 1559477 10004705 := bstep (se 2 (by rfl) ⟨3751764, by rfl⟩ : syracuseStep 10004705 = 7503529) B7503529
theorem B1561063 : Blo 1559477 1561063 := bstep (se 1 (by rfl) ⟨1170797, by rfl⟩ : syracuseStep 1561063 = 2341595) B2341595
theorem B102634543 : Blo 1559477 102634543 := bstep (se 1 (by rfl) ⟨76975907, by rfl⟩ : syracuseStep 102634543 = 153951815) B153951815
theorem B6669803 : Blo 1559477 6669803 := bstep (se 1 (by rfl) ⟨5002352, by rfl⟩ : syracuseStep 6669803 = 10004705) B10004705
theorem B136846057 : Blo 1559477 136846057 := bstep (se 2 (by rfl) ⟨51317271, by rfl⟩ : syracuseStep 136846057 = 102634543) B102634543
theorem B182461409 : Blo 1559477 182461409 := bstep (se 2 (by rfl) ⟨68423028, by rfl⟩ : syracuseStep 182461409 = 136846057) B136846057
theorem B17786141 : Blo 1559477 17786141 := bstep (se 3 (by rfl) ⟨3334901, by rfl⟩ : syracuseStep 17786141 = 6669803) B6669803
theorem B11857427 : Blo 1559477 11857427 := bstep (se 1 (by rfl) ⟨8893070, by rfl⟩ : syracuseStep 11857427 = 17786141) B17786141
theorem B121640939 : Blo 1559477 121640939 := bstep (se 1 (by rfl) ⟨91230704, by rfl⟩ : syracuseStep 121640939 = 182461409) B182461409
theorem B81093959 : Blo 1559477 81093959 := bstep (se 1 (by rfl) ⟨60820469, by rfl⟩ : syracuseStep 81093959 = 121640939) B121640939
theorem B7904951 : Blo 1559477 7904951 := bstep (se 1 (by rfl) ⟨5928713, by rfl⟩ : syracuseStep 7904951 = 11857427) B11857427
theorem B5269967 : Blo 1559477 5269967 := bstep (se 1 (by rfl) ⟨3952475, by rfl⟩ : syracuseStep 5269967 = 7904951) B7904951
theorem B54062639 : Blo 1559477 54062639 := bstep (se 1 (by rfl) ⟨40546979, by rfl⟩ : syracuseStep 54062639 = 81093959) B81093959
theorem B36041759 : Blo 1559477 36041759 := bstep (se 1 (by rfl) ⟨27031319, by rfl⟩ : syracuseStep 36041759 = 54062639) B54062639
theorem B3513311 : Blo 1559477 3513311 := bstep (se 1 (by rfl) ⟨2634983, by rfl⟩ : syracuseStep 3513311 = 5269967) B5269967
theorem B24027839 : Blo 1559477 24027839 := bstep (se 1 (by rfl) ⟨18020879, by rfl⟩ : syracuseStep 24027839 = 36041759) B36041759
theorem B2342207 : Blo 1559477 2342207 := bstep (se 1 (by rfl) ⟨1756655, by rfl⟩ : syracuseStep 2342207 = 3513311) B3513311
theorem B16018559 : Blo 1559477 16018559 := bstep (se 1 (by rfl) ⟨12013919, by rfl⟩ : syracuseStep 16018559 = 24027839) B24027839
theorem B1561471 : Blo 1559477 1561471 := bstep (se 1 (by rfl) ⟨1171103, by rfl⟩ : syracuseStep 1561471 = 2342207) B2342207
theorem B10679039 : Blo 1559477 10679039 := bstep (se 1 (by rfl) ⟨8009279, by rfl⟩ : syracuseStep 10679039 = 16018559) B16018559
theorem B7119359 : Blo 1559477 7119359 := bstep (se 1 (by rfl) ⟨5339519, by rfl⟩ : syracuseStep 7119359 = 10679039) B10679039
theorem B4746239 : Blo 1559477 4746239 := bstep (se 1 (by rfl) ⟨3559679, by rfl⟩ : syracuseStep 4746239 = 7119359) B7119359
theorem B3164159 : Blo 1559477 3164159 := bstep (se 1 (by rfl) ⟨2373119, by rfl⟩ : syracuseStep 3164159 = 4746239) B4746239
theorem B2109439 : Blo 1559477 2109439 := bstep (se 1 (by rfl) ⟨1582079, by rfl⟩ : syracuseStep 2109439 = 3164159) B3164159
theorem B2812585 : Blo 1559477 2812585 := bstep (se 2 (by rfl) ⟨1054719, by rfl⟩ : syracuseStep 2812585 = 2109439) B2109439
theorem B3750113 : Blo 1559477 3750113 := bstep (se 2 (by rfl) ⟨1406292, by rfl⟩ : syracuseStep 3750113 = 2812585) B2812585
theorem B2500075 : Blo 1559477 2500075 := bstep (se 1 (by rfl) ⟨1875056, by rfl⟩ : syracuseStep 2500075 = 3750113) B3750113
theorem B3333433 : Blo 1559477 3333433 := bstep (se 2 (by rfl) ⟨1250037, by rfl⟩ : syracuseStep 3333433 = 2500075) B2500075
theorem B4444577 : Blo 1559477 4444577 := bstep (se 2 (by rfl) ⟨1666716, by rfl⟩ : syracuseStep 4444577 = 3333433) B3333433
theorem B2963051 : Blo 1559477 2963051 := bstep (se 1 (by rfl) ⟨2222288, by rfl⟩ : syracuseStep 2963051 = 4444577) B4444577
theorem B1975367 : Blo 1559477 1975367 := bstep (se 1 (by rfl) ⟨1481525, by rfl⟩ : syracuseStep 1975367 = 2963051) B2963051
theorem B5267645 : Blo 1559477 5267645 := bstep (se 3 (by rfl) ⟨987683, by rfl⟩ : syracuseStep 5267645 = 1975367) B1975367
theorem B3511763 : Blo 1559477 3511763 := bstep (se 1 (by rfl) ⟨2633822, by rfl⟩ : syracuseStep 3511763 = 5267645) B5267645
theorem B2341175 : Blo 1559477 2341175 := bstep (se 1 (by rfl) ⟨1755881, by rfl⟩ : syracuseStep 2341175 = 3511763) B3511763
theorem B1560783 : Blo 1559477 1560783 := bstep (se 1 (by rfl) ⟨1170587, by rfl⟩ : syracuseStep 1560783 = 2341175) B2341175

theorem C0 (j : ℕ) (h1 : 389869 ≤ j) (h2 : j ≤ 390368) : Blo 1559477 (4 * j + 3) := by
  interval_cases j
  · exact B1559479
  · exact B1559483
  · exact B1559487
  · exact B1559491
  · exact B1559495
  · exact B1559499
  · exact B1559503
  · exact B1559507
  · exact B1559511
  · exact B1559515
  · exact B1559519
  · exact B1559523
  · exact B1559527
  · exact B1559531
  · exact B1559535
  · exact B1559539
  · exact B1559543
  · exact B1559547
  · exact B1559551
  · exact B1559555
  · exact B1559559
  · exact B1559563
  · exact B1559567
  · exact B1559571
  · exact B1559575
  · exact B1559579
  · exact B1559583
  · exact B1559587
  · exact B1559591
  · exact B1559595
  · exact B1559599
  · exact B1559603
  · exact B1559607
  · exact B1559611
  · exact B1559615
  · exact B1559619
  · exact B1559623
  · exact B1559627
  · exact B1559631
  · exact B1559635
  · exact B1559639
  · exact B1559643
  · exact B1559647
  · exact B1559651
  · exact B1559655
  · exact B1559659
  · exact B1559663
  · exact B1559667
  · exact B1559671
  · exact B1559675
  · exact B1559679
  · exact B1559683
  · exact B1559687
  · exact B1559691
  · exact B1559695
  · exact B1559699
  · exact B1559703
  · exact B1559707
  · exact B1559711
  · exact B1559715
  · exact B1559719
  · exact B1559723
  · exact B1559727
  · exact B1559731
  · exact B1559735
  · exact B1559739
  · exact B1559743
  · exact B1559747
  · exact B1559751
  · exact B1559755
  · exact B1559759
  · exact B1559763
  · exact B1559767
  · exact B1559771
  · exact B1559775
  · exact B1559779
  · exact B1559783
  · exact B1559787
  · exact B1559791
  · exact B1559795
  · exact B1559799
  · exact B1559803
  · exact B1559807
  · exact B1559811
  · exact B1559815
  · exact B1559819
  · exact B1559823
  · exact B1559827
  · exact B1559831
  · exact B1559835
  · exact B1559839
  · exact B1559843
  · exact B1559847
  · exact B1559851
  · exact B1559855
  · exact B1559859
  · exact B1559863
  · exact B1559867
  · exact B1559871
  · exact B1559875
  · exact B1559879
  · exact B1559883
  · exact B1559887
  · exact B1559891
  · exact B1559895
  · exact B1559899
  · exact B1559903
  · exact B1559907
  · exact B1559911
  · exact B1559915
  · exact B1559919
  · exact B1559923
  · exact B1559927
  · exact B1559931
  · exact B1559935
  · exact B1559939
  · exact B1559943
  · exact B1559947
  · exact B1559951
  · exact B1559955
  · exact B1559959
  · exact B1559963
  · exact B1559967
  · exact B1559971
  · exact B1559975
  · exact B1559979
  · exact B1559983
  · exact B1559987
  · exact B1559991
  · exact B1559995
  · exact B1559999
  · exact B1560003
  · exact B1560007
  · exact B1560011
  · exact B1560015
  · exact B1560019
  · exact B1560023
  · exact B1560027
  · exact B1560031
  · exact B1560035
  · exact B1560039
  · exact B1560043
  · exact B1560047
  · exact B1560051
  · exact B1560055
  · exact B1560059
  · exact B1560063
  · exact B1560067
  · exact B1560071
  · exact B1560075
  · exact B1560079
  · exact B1560083
  · exact B1560087
  · exact B1560091
  · exact B1560095
  · exact B1560099
  · exact B1560103
  · exact B1560107
  · exact B1560111
  · exact B1560115
  · exact B1560119
  · exact B1560123
  · exact B1560127
  · exact B1560131
  · exact B1560135
  · exact B1560139
  · exact B1560143
  · exact B1560147
  · exact B1560151
  · exact B1560155
  · exact B1560159
  · exact B1560163
  · exact B1560167
  · exact B1560171
  · exact B1560175
  · exact B1560179
  · exact B1560183
  · exact B1560187
  · exact B1560191
  · exact B1560195
  · exact B1560199
  · exact B1560203
  · exact B1560207
  · exact B1560211
  · exact B1560215
  · exact B1560219
  · exact B1560223
  · exact B1560227
  · exact B1560231
  · exact B1560235
  · exact B1560239
  · exact B1560243
  · exact B1560247
  · exact B1560251
  · exact B1560255
  · exact B1560259
  · exact B1560263
  · exact B1560267
  · exact B1560271
  · exact B1560275
  · exact B1560279
  · exact B1560283
  · exact B1560287
  · exact B1560291
  · exact B1560295
  · exact B1560299
  · exact B1560303
  · exact B1560307
  · exact B1560311
  · exact B1560315
  · exact B1560319
  · exact B1560323
  · exact B1560327
  · exact B1560331
  · exact B1560335
  · exact B1560339
  · exact B1560343
  · exact B1560347
  · exact B1560351
  · exact B1560355
  · exact B1560359
  · exact B1560363
  · exact B1560367
  · exact B1560371
  · exact B1560375
  · exact B1560379
  · exact B1560383
  · exact B1560387
  · exact B1560391
  · exact B1560395
  · exact B1560399
  · exact B1560403
  · exact B1560407
  · exact B1560411
  · exact B1560415
  · exact B1560419
  · exact B1560423
  · exact B1560427
  · exact B1560431
  · exact B1560435
  · exact B1560439
  · exact B1560443
  · exact B1560447
  · exact B1560451
  · exact B1560455
  · exact B1560459
  · exact B1560463
  · exact B1560467
  · exact B1560471
  · exact B1560475
  · exact B1560479
  · exact B1560483
  · exact B1560487
  · exact B1560491
  · exact B1560495
  · exact B1560499
  · exact B1560503
  · exact B1560507
  · exact B1560511
  · exact B1560515
  · exact B1560519
  · exact B1560523
  · exact B1560527
  · exact B1560531
  · exact B1560535
  · exact B1560539
  · exact B1560543
  · exact B1560547
  · exact B1560551
  · exact B1560555
  · exact B1560559
  · exact B1560563
  · exact B1560567
  · exact B1560571
  · exact B1560575
  · exact B1560579
  · exact B1560583
  · exact B1560587
  · exact B1560591
  · exact B1560595
  · exact B1560599
  · exact B1560603
  · exact B1560607
  · exact B1560611
  · exact B1560615
  · exact B1560619
  · exact B1560623
  · exact B1560627
  · exact B1560631
  · exact B1560635
  · exact B1560639
  · exact B1560643
  · exact B1560647
  · exact B1560651
  · exact B1560655
  · exact B1560659
  · exact B1560663
  · exact B1560667
  · exact B1560671
  · exact B1560675
  · exact B1560679
  · exact B1560683
  · exact B1560687
  · exact B1560691
  · exact B1560695
  · exact B1560699
  · exact B1560703
  · exact B1560707
  · exact B1560711
  · exact B1560715
  · exact B1560719
  · exact B1560723
  · exact B1560727
  · exact B1560731
  · exact B1560735
  · exact B1560739
  · exact B1560743
  · exact B1560747
  · exact B1560751
  · exact B1560755
  · exact B1560759
  · exact B1560763
  · exact B1560767
  · exact B1560771
  · exact B1560775
  · exact B1560779
  · exact B1560783
  · exact B1560787
  · exact B1560791
  · exact B1560795
  · exact B1560799
  · exact B1560803
  · exact B1560807
  · exact B1560811
  · exact B1560815
  · exact B1560819
  · exact B1560823
  · exact B1560827
  · exact B1560831
  · exact B1560835
  · exact B1560839
  · exact B1560843
  · exact B1560847
  · exact B1560851
  · exact B1560855
  · exact B1560859
  · exact B1560863
  · exact B1560867
  · exact B1560871
  · exact B1560875
  · exact B1560879
  · exact B1560883
  · exact B1560887
  · exact B1560891
  · exact B1560895
  · exact B1560899
  · exact B1560903
  · exact B1560907
  · exact B1560911
  · exact B1560915
  · exact B1560919
  · exact B1560923
  · exact B1560927
  · exact B1560931
  · exact B1560935
  · exact B1560939
  · exact B1560943
  · exact B1560947
  · exact B1560951
  · exact B1560955
  · exact B1560959
  · exact B1560963
  · exact B1560967
  · exact B1560971
  · exact B1560975
  · exact B1560979
  · exact B1560983
  · exact B1560987
  · exact B1560991
  · exact B1560995
  · exact B1560999
  · exact B1561003
  · exact B1561007
  · exact B1561011
  · exact B1561015
  · exact B1561019
  · exact B1561023
  · exact B1561027
  · exact B1561031
  · exact B1561035
  · exact B1561039
  · exact B1561043
  · exact B1561047
  · exact B1561051
  · exact B1561055
  · exact B1561059
  · exact B1561063
  · exact B1561067
  · exact B1561071
  · exact B1561075
  · exact B1561079
  · exact B1561083
  · exact B1561087
  · exact B1561091
  · exact B1561095
  · exact B1561099
  · exact B1561103
  · exact B1561107
  · exact B1561111
  · exact B1561115
  · exact B1561119
  · exact B1561123
  · exact B1561127
  · exact B1561131
  · exact B1561135
  · exact B1561139
  · exact B1561143
  · exact B1561147
  · exact B1561151
  · exact B1561155
  · exact B1561159
  · exact B1561163
  · exact B1561167
  · exact B1561171
  · exact B1561175
  · exact B1561179
  · exact B1561183
  · exact B1561187
  · exact B1561191
  · exact B1561195
  · exact B1561199
  · exact B1561203
  · exact B1561207
  · exact B1561211
  · exact B1561215
  · exact B1561219
  · exact B1561223
  · exact B1561227
  · exact B1561231
  · exact B1561235
  · exact B1561239
  · exact B1561243
  · exact B1561247
  · exact B1561251
  · exact B1561255
  · exact B1561259
  · exact B1561263
  · exact B1561267
  · exact B1561271
  · exact B1561275
  · exact B1561279
  · exact B1561283
  · exact B1561287
  · exact B1561291
  · exact B1561295
  · exact B1561299
  · exact B1561303
  · exact B1561307
  · exact B1561311
  · exact B1561315
  · exact B1561319
  · exact B1561323
  · exact B1561327
  · exact B1561331
  · exact B1561335
  · exact B1561339
  · exact B1561343
  · exact B1561347
  · exact B1561351
  · exact B1561355
  · exact B1561359
  · exact B1561363
  · exact B1561367
  · exact B1561371
  · exact B1561375
  · exact B1561379
  · exact B1561383
  · exact B1561387
  · exact B1561391
  · exact B1561395
  · exact B1561399
  · exact B1561403
  · exact B1561407
  · exact B1561411
  · exact B1561415
  · exact B1561419
  · exact B1561423
  · exact B1561427
  · exact B1561431
  · exact B1561435
  · exact B1561439
  · exact B1561443
  · exact B1561447
  · exact B1561451
  · exact B1561455
  · exact B1561459
  · exact B1561463
  · exact B1561467
  · exact B1561471
  · exact B1561475

theorem solution (m : ℕ) (hlo : 1559477 ≤ m) (hhi : m ≤ 1561477) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 389869 ≤ j := by omega
    have hj2 : j ≤ 390368 := by omega
    have hb : Blo 1559477 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
