-- Prove2me | solution 1 for syracuse_descends_range_1462551_1464551
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:44:21.790536+00:00
-- url     : https://prove2.me/submissions/d994cbe6-5945-4288-ab23-434a979132f7

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


theorem B3293189 : Blo 1462551 3293189 := bbase (se 4 (by rfl) ⟨308736, by rfl⟩ : syracuseStep 3293189 = 617473) (by norm_num)
theorem B2195477 : Blo 1462551 2195477 := bbase (se 6 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 2195477 = 102913) (by norm_num)
theorem B1646617 : Blo 1462551 1646617 := bbase (se 2 (by rfl) ⟨617481, by rfl⟩ : syracuseStep 1646617 = 1234963) (by norm_num)
theorem B1851437 : Blo 1462551 1851437 := bbase (se 3 (by rfl) ⟨347144, by rfl⟩ : syracuseStep 1851437 = 694289) (by norm_num)
theorem B2195501 : Blo 1462551 2195501 := bbase (se 3 (by rfl) ⟨411656, by rfl⟩ : syracuseStep 2195501 = 823313) (by norm_num)
theorem B2777141 : Blo 1462551 2777141 := bbase (se 5 (by rfl) ⟨130178, by rfl⟩ : syracuseStep 2777141 = 260357) (by norm_num)
theorem B1646653 : Blo 1462551 1646653 := bbase (se 3 (by rfl) ⟨308747, by rfl⟩ : syracuseStep 1646653 = 617495) (by norm_num)
theorem B2195525 : Blo 1462551 2195525 := bbase (se 4 (by rfl) ⟨205830, by rfl⟩ : syracuseStep 2195525 = 411661) (by norm_num)
theorem B3293261 : Blo 1462551 3293261 := bbase (se 3 (by rfl) ⟨617486, by rfl⟩ : syracuseStep 3293261 = 1234973) (by norm_num)
theorem B2195549 : Blo 1462551 2195549 := bbase (se 3 (by rfl) ⟨411665, by rfl⟩ : syracuseStep 2195549 = 823331) (by norm_num)
theorem B1646689 : Blo 1462551 1646689 := bbase (se 2 (by rfl) ⟨617508, by rfl⟩ : syracuseStep 1646689 = 1235017) (by norm_num)
theorem B1851493 : Blo 1462551 1851493 := bbase (se 4 (by rfl) ⟨173577, by rfl⟩ : syracuseStep 1851493 = 347155) (by norm_num)
theorem B2195573 : Blo 1462551 2195573 := bbase (se 5 (by rfl) ⟨102917, by rfl⟩ : syracuseStep 2195573 = 205835) (by norm_num)
theorem B1646725 : Blo 1462551 1646725 := bbase (se 4 (by rfl) ⟨154380, by rfl⟩ : syracuseStep 1646725 = 308761) (by norm_num)
theorem B2195597 : Blo 1462551 2195597 := bbase (se 3 (by rfl) ⟨411674, by rfl⟩ : syracuseStep 2195597 = 823349) (by norm_num)
theorem B11108501 : Blo 1462551 11108501 := bbase (se 6 (by rfl) ⟨260355, by rfl⟩ : syracuseStep 11108501 = 520711) (by norm_num)
theorem B3293333 : Blo 1462551 3293333 := bbase (se 6 (by rfl) ⟨77187, by rfl⟩ : syracuseStep 3293333 = 154375) (by norm_num)
theorem B2195621 : Blo 1462551 2195621 := bbase (se 4 (by rfl) ⟨205839, by rfl⟩ : syracuseStep 2195621 = 411679) (by norm_num)
theorem B1646761 : Blo 1462551 1646761 := bbase (se 2 (by rfl) ⟨617535, by rfl⟩ : syracuseStep 1646761 = 1235071) (by norm_num)
theorem B10018997 : Blo 1462551 10018997 := bbase (se 5 (by rfl) ⟨469640, by rfl⟩ : syracuseStep 10018997 = 939281) (by norm_num)
theorem B2195645 : Blo 1462551 2195645 := bbase (se 3 (by rfl) ⟨411683, by rfl⟩ : syracuseStep 2195645 = 823367) (by norm_num)
theorem B1851589 : Blo 1462551 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B4939973 : Blo 1462551 4939973 := bbase (se 4 (by rfl) ⟨463122, by rfl⟩ : syracuseStep 4939973 = 926245) (by norm_num)
theorem B1482953 : Blo 1462551 1482953 := bbase (se 2 (by rfl) ⟨556107, by rfl⟩ : syracuseStep 1482953 = 1112215) (by norm_num)
theorem B1646797 : Blo 1462551 1646797 := bbase (se 3 (by rfl) ⟨308774, by rfl⟩ : syracuseStep 1646797 = 617549) (by norm_num)
theorem B2195669 : Blo 1462551 2195669 := bbase (se 7 (by rfl) ⟨25730, by rfl⟩ : syracuseStep 2195669 = 51461) (by norm_num)
theorem B47489237 : Blo 1462551 47489237 := bbase (se 7 (by rfl) ⟨556514, by rfl⟩ : syracuseStep 47489237 = 1113029) (by norm_num)
theorem B8904917 : Blo 1462551 8904917 := bbase (se 7 (by rfl) ⟨104354, by rfl⟩ : syracuseStep 8904917 = 208709) (by norm_num)
theorem B8339669 : Blo 1462551 8339669 := bbase (se 7 (by rfl) ⟨97730, by rfl⟩ : syracuseStep 8339669 = 195461) (by norm_num)
theorem B3293405 : Blo 1462551 3293405 := bbase (se 3 (by rfl) ⟨617513, by rfl⟩ : syracuseStep 3293405 = 1235027) (by norm_num)
theorem B2343149 : Blo 1462551 2343149 := bbase (se 3 (by rfl) ⟨439340, by rfl⟩ : syracuseStep 2343149 = 878681) (by norm_num)
theorem B2195693 : Blo 1462551 2195693 := bbase (se 3 (by rfl) ⟨411692, by rfl⟩ : syracuseStep 2195693 = 823385) (by norm_num)
theorem B1646833 : Blo 1462551 1646833 := bbase (se 2 (by rfl) ⟨617562, by rfl⟩ : syracuseStep 1646833 = 1235125) (by norm_num)
theorem B7405829 : Blo 1462551 7405829 := bbase (se 4 (by rfl) ⟨694296, by rfl⟩ : syracuseStep 7405829 = 1388593) (by norm_num)
theorem B2195717 : Blo 1462551 2195717 := bbase (se 4 (by rfl) ⟨205848, by rfl⟩ : syracuseStep 2195717 = 411697) (by norm_num)
theorem B1646869 : Blo 1462551 1646869 := bbase (se 6 (by rfl) ⟨38598, by rfl⟩ : syracuseStep 1646869 = 77197) (by norm_num)
theorem B2195741 : Blo 1462551 2195741 := bbase (se 3 (by rfl) ⟨411701, by rfl⟩ : syracuseStep 2195741 = 823403) (by norm_num)
theorem B3293477 : Blo 1462551 3293477 := bbase (se 4 (by rfl) ⟨308763, by rfl⟩ : syracuseStep 3293477 = 617527) (by norm_num)
theorem B2195765 : Blo 1462551 2195765 := bbase (se 5 (by rfl) ⟨102926, by rfl⟩ : syracuseStep 2195765 = 205853) (by norm_num)
theorem B1646905 : Blo 1462551 1646905 := bbase (se 2 (by rfl) ⟨617589, by rfl⟩ : syracuseStep 1646905 = 1235179) (by norm_num)
theorem B3703117 : Blo 1462551 3703117 := bbase (se 3 (by rfl) ⟨694334, by rfl⟩ : syracuseStep 3703117 = 1388669) (by norm_num)
theorem B2195789 : Blo 1462551 2195789 := bbase (se 3 (by rfl) ⟨411710, by rfl⟩ : syracuseStep 2195789 = 823421) (by norm_num)
theorem B8331605 : Blo 1462551 8331605 := bbase (se 10 (by rfl) ⟨12204, by rfl⟩ : syracuseStep 8331605 = 24409) (by norm_num)
theorem B2777429 : Blo 1462551 2777429 := bbase (se 10 (by rfl) ⟨4068, by rfl⟩ : syracuseStep 2777429 = 8137) (by norm_num)
theorem B85524821 : Blo 1462551 85524821 := bbase (se 10 (by rfl) ⟨125280, by rfl⟩ : syracuseStep 85524821 = 250561) (by norm_num)
theorem B1646941 : Blo 1462551 1646941 := bbase (se 3 (by rfl) ⟨308801, by rfl⟩ : syracuseStep 1646941 = 617603) (by norm_num)
theorem B2195813 : Blo 1462551 2195813 := bbase (se 4 (by rfl) ⟨205857, by rfl⟩ : syracuseStep 2195813 = 411715) (by norm_num)
theorem B2343277 : Blo 1462551 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B3293549 : Blo 1462551 3293549 := bbase (se 3 (by rfl) ⟨617540, by rfl⟩ : syracuseStep 3293549 = 1235081) (by norm_num)
theorem B1851761 : Blo 1462551 1851761 := bbase (se 2 (by rfl) ⟨694410, by rfl⟩ : syracuseStep 1851761 = 1388821) (by norm_num)
theorem B2195837 : Blo 1462551 2195837 := bbase (se 3 (by rfl) ⟨411719, by rfl⟩ : syracuseStep 2195837 = 823439) (by norm_num)
theorem B1646977 : Blo 1462551 1646977 := bbase (se 2 (by rfl) ⟨617616, by rfl⟩ : syracuseStep 1646977 = 1235233) (by norm_num)
theorem B2195861 : Blo 1462551 2195861 := bbase (se 6 (by rfl) ⟨51465, by rfl⟩ : syracuseStep 2195861 = 102931) (by norm_num)
theorem B1647013 : Blo 1462551 1647013 := bbase (se 4 (by rfl) ⟨154407, by rfl⟩ : syracuseStep 1647013 = 308815) (by norm_num)
theorem B1851817 : Blo 1462551 1851817 := bbase (se 2 (by rfl) ⟨694431, by rfl⟩ : syracuseStep 1851817 = 1388863) (by norm_num)
theorem B2195885 : Blo 1462551 2195885 := bbase (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) (by norm_num)
theorem B3293621 : Blo 1462551 3293621 := bbase (se 5 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 3293621 = 308777) (by norm_num)
theorem B3703229 : Blo 1462551 3703229 := bbase (se 3 (by rfl) ⟨694355, by rfl⟩ : syracuseStep 3703229 = 1388711) (by norm_num)
theorem B2195909 : Blo 1462551 2195909 := bbase (se 4 (by rfl) ⟨205866, by rfl⟩ : syracuseStep 2195909 = 411733) (by norm_num)
theorem B1647049 : Blo 1462551 1647049 := bbase (se 2 (by rfl) ⟨617643, by rfl⟩ : syracuseStep 1647049 = 1235287) (by norm_num)
theorem B2195933 : Blo 1462551 2195933 := bbase (se 3 (by rfl) ⟨411737, by rfl⟩ : syracuseStep 2195933 = 823475) (by norm_num)
theorem B2777581 : Blo 1462551 2777581 := bbase (se 3 (by rfl) ⟨520796, by rfl⟩ : syracuseStep 2777581 = 1041593) (by norm_num)
theorem B1647085 : Blo 1462551 1647085 := bbase (se 3 (by rfl) ⟨308828, by rfl⟩ : syracuseStep 1647085 = 617657) (by norm_num)
theorem B2195957 : Blo 1462551 2195957 := bbase (se 5 (by rfl) ⟨102935, by rfl⟩ : syracuseStep 2195957 = 205871) (by norm_num)
theorem B3293693 : Blo 1462551 3293693 := bbase (se 3 (by rfl) ⟨617567, by rfl⟩ : syracuseStep 3293693 = 1235135) (by norm_num)
theorem B1851913 : Blo 1462551 1851913 := bbase (se 2 (by rfl) ⟨694467, by rfl⟩ : syracuseStep 1851913 = 1388935) (by norm_num)
theorem B2195981 : Blo 1462551 2195981 := bbase (se 3 (by rfl) ⟨411746, by rfl⟩ : syracuseStep 2195981 = 823493) (by norm_num)
theorem B1647121 : Blo 1462551 1647121 := bbase (se 2 (by rfl) ⟨617670, by rfl⟩ : syracuseStep 1647121 = 1235341) (by norm_num)
theorem B2196005 : Blo 1462551 2196005 := bbase (se 4 (by rfl) ⟨205875, by rfl⟩ : syracuseStep 2196005 = 411751) (by norm_num)
theorem B1647157 : Blo 1462551 1647157 := bbase (se 5 (by rfl) ⟨77210, by rfl⟩ : syracuseStep 1647157 = 154421) (by norm_num)
theorem B2196029 : Blo 1462551 2196029 := bbase (se 3 (by rfl) ⟨411755, by rfl⟩ : syracuseStep 2196029 = 823511) (by norm_num)
theorem B3293765 : Blo 1462551 3293765 := bbase (se 4 (by rfl) ⟨308790, by rfl⟩ : syracuseStep 3293765 = 617581) (by norm_num)
theorem B1876565 : Blo 1462551 1876565 := bbase (se 8 (by rfl) ⟨10995, by rfl⟩ : syracuseStep 1876565 = 21991) (by norm_num)
theorem B2196053 : Blo 1462551 2196053 := bbase (se 8 (by rfl) ⟨12867, by rfl⟩ : syracuseStep 2196053 = 25735) (by norm_num)
theorem B4170325 : Blo 1462551 4170325 := bbase (se 8 (by rfl) ⟨24435, by rfl⟩ : syracuseStep 4170325 = 48871) (by norm_num)
theorem B1647193 : Blo 1462551 1647193 := bbase (se 2 (by rfl) ⟨617697, by rfl⟩ : syracuseStep 1647193 = 1235395) (by norm_num)
theorem B2196077 : Blo 1462551 2196077 := bbase (se 3 (by rfl) ⟨411764, by rfl⟩ : syracuseStep 2196077 = 823529) (by norm_num)
theorem B4940405 : Blo 1462551 4940405 := bbase (se 5 (by rfl) ⟨231581, by rfl⟩ : syracuseStep 4940405 = 463163) (by norm_num)
theorem B3703421 : Blo 1462551 3703421 := bbase (se 3 (by rfl) ⟨694391, by rfl⟩ : syracuseStep 3703421 = 1388783) (by norm_num)
theorem B1647229 : Blo 1462551 1647229 := bbase (se 3 (by rfl) ⟨308855, by rfl⟩ : syracuseStep 1647229 = 617711) (by norm_num)
theorem B2966149 : Blo 1462551 2966149 := bbase (se 4 (by rfl) ⟨278076, by rfl⟩ : syracuseStep 2966149 = 556153) (by norm_num)
theorem B2196101 : Blo 1462551 2196101 := bbase (se 4 (by rfl) ⟨205884, by rfl⟩ : syracuseStep 2196101 = 411769) (by norm_num)
theorem B3293837 : Blo 1462551 3293837 := bbase (se 3 (by rfl) ⟨617594, by rfl⟩ : syracuseStep 3293837 = 1235189) (by norm_num)
theorem B18743957 : Blo 1462551 18743957 := bbase (se 6 (by rfl) ⟨439311, by rfl⟩ : syracuseStep 18743957 = 878623) (by norm_num)
theorem B2196125 : Blo 1462551 2196125 := bbase (se 3 (by rfl) ⟨411773, by rfl⟩ : syracuseStep 2196125 = 823547) (by norm_num)
theorem B1647265 : Blo 1462551 1647265 := bbase (se 2 (by rfl) ⟨617724, by rfl⟩ : syracuseStep 1647265 = 1235449) (by norm_num)
theorem B1852085 : Blo 1462551 1852085 := bbase (se 5 (by rfl) ⟨86816, by rfl⟩ : syracuseStep 1852085 = 173633) (by norm_num)
theorem B2196149 : Blo 1462551 2196149 := bbase (se 5 (by rfl) ⟨102944, by rfl⟩ : syracuseStep 2196149 = 205889) (by norm_num)
theorem B2966213 : Blo 1462551 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B1647301 : Blo 1462551 1647301 := bbase (se 4 (by rfl) ⟨154434, by rfl⟩ : syracuseStep 1647301 = 308869) (by norm_num)
theorem B2196173 : Blo 1462551 2196173 := bbase (se 3 (by rfl) ⟨411782, by rfl⟩ : syracuseStep 2196173 = 823565) (by norm_num)
theorem B3293909 : Blo 1462551 3293909 := bbase (se 7 (by rfl) ⟨38600, by rfl⟩ : syracuseStep 3293909 = 77201) (by norm_num)
theorem B2196197 : Blo 1462551 2196197 := bbase (se 4 (by rfl) ⟨205893, by rfl⟩ : syracuseStep 2196197 = 411787) (by norm_num)
theorem B1647337 : Blo 1462551 1647337 := bbase (se 2 (by rfl) ⟨617751, by rfl⟩ : syracuseStep 1647337 = 1235503) (by norm_num)
theorem B1852141 : Blo 1462551 1852141 := bbase (se 3 (by rfl) ⟨347276, by rfl⟩ : syracuseStep 1852141 = 694553) (by norm_num)
theorem B2196221 : Blo 1462551 2196221 := bbase (se 3 (by rfl) ⟨411791, by rfl⟩ : syracuseStep 2196221 = 823583) (by norm_num)
theorem B1647373 : Blo 1462551 1647373 := bbase (se 3 (by rfl) ⟨308882, by rfl⟩ : syracuseStep 1647373 = 617765) (by norm_num)
theorem B2196245 : Blo 1462551 2196245 := bbase (se 6 (by rfl) ⟨51474, by rfl⟩ : syracuseStep 2196245 = 102949) (by norm_num)
theorem B2777885 : Blo 1462551 2777885 := bbase (se 3 (by rfl) ⟨520853, by rfl⟩ : syracuseStep 2777885 = 1041707) (by norm_num)
theorem B3293981 : Blo 1462551 3293981 := bbase (se 3 (by rfl) ⟨617621, by rfl⟩ : syracuseStep 3293981 = 1235243) (by norm_num)
theorem B2196269 : Blo 1462551 2196269 := bbase (se 3 (by rfl) ⟨411800, by rfl⟩ : syracuseStep 2196269 = 823601) (by norm_num)
theorem B1647409 : Blo 1462551 1647409 := bbase (se 2 (by rfl) ⟨617778, by rfl⟩ : syracuseStep 1647409 = 1235557) (by norm_num)
theorem B2196293 : Blo 1462551 2196293 := bbase (se 4 (by rfl) ⟨205902, by rfl⟩ : syracuseStep 2196293 = 411805) (by norm_num)
theorem B1852237 : Blo 1462551 1852237 := bbase (se 3 (by rfl) ⟨347294, by rfl⟩ : syracuseStep 1852237 = 694589) (by norm_num)
theorem B1647445 : Blo 1462551 1647445 := bbase (se 9 (by rfl) ⟨4826, by rfl⟩ : syracuseStep 1647445 = 9653) (by norm_num)
theorem B2196317 : Blo 1462551 2196317 := bbase (se 3 (by rfl) ⟨411809, by rfl⟩ : syracuseStep 2196317 = 823619) (by norm_num)
theorem B3294053 : Blo 1462551 3294053 := bbase (se 4 (by rfl) ⟨308817, by rfl⟩ : syracuseStep 3294053 = 617635) (by norm_num)
theorem B2196341 : Blo 1462551 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B1647481 : Blo 1462551 1647481 := bbase (se 2 (by rfl) ⟨617805, by rfl⟩ : syracuseStep 1647481 = 1235611) (by norm_num)
theorem B2196365 : Blo 1462551 2196365 := bbase (se 3 (by rfl) ⟨411818, by rfl⟩ : syracuseStep 2196365 = 823637) (by norm_num)
theorem B1647517 : Blo 1462551 1647517 := bbase (se 3 (by rfl) ⟨308909, by rfl⟩ : syracuseStep 1647517 = 617819) (by norm_num)
theorem B2196389 : Blo 1462551 2196389 := bbase (se 4 (by rfl) ⟨205911, by rfl⟩ : syracuseStep 2196389 = 411823) (by norm_num)
theorem B3294125 : Blo 1462551 3294125 := bbase (se 3 (by rfl) ⟨617648, by rfl⟩ : syracuseStep 3294125 = 1235297) (by norm_num)
theorem B2196413 : Blo 1462551 2196413 := bbase (se 3 (by rfl) ⟨411827, by rfl⟩ : syracuseStep 2196413 = 823655) (by norm_num)
theorem B1647553 : Blo 1462551 1647553 := bbase (se 2 (by rfl) ⟨617832, by rfl⟩ : syracuseStep 1647553 = 1235665) (by norm_num)
theorem B3703765 : Blo 1462551 3703765 := bbase (se 7 (by rfl) ⟨43403, by rfl⟩ : syracuseStep 3703765 = 86807) (by norm_num)
theorem B2196437 : Blo 1462551 2196437 := bbase (se 7 (by rfl) ⟨25739, by rfl⟩ : syracuseStep 2196437 = 51479) (by norm_num)
theorem B1647589 : Blo 1462551 1647589 := bbase (se 4 (by rfl) ⟨154461, by rfl⟩ : syracuseStep 1647589 = 308923) (by norm_num)
theorem B2196461 : Blo 1462551 2196461 := bbase (se 3 (by rfl) ⟨411836, by rfl⟩ : syracuseStep 2196461 = 823673) (by norm_num)
theorem B3294197 : Blo 1462551 3294197 := bbase (se 5 (by rfl) ⟨154415, by rfl⟩ : syracuseStep 3294197 = 308831) (by norm_num)
theorem B1852409 : Blo 1462551 1852409 := bbase (se 2 (by rfl) ⟨694653, by rfl⟩ : syracuseStep 1852409 = 1389307) (by norm_num)
theorem B6251525 : Blo 1462551 6251525 := bbase (se 4 (by rfl) ⟨586080, by rfl⟩ : syracuseStep 6251525 = 1172161) (by norm_num)
theorem B2196485 : Blo 1462551 2196485 := bbase (se 4 (by rfl) ⟨205920, by rfl⟩ : syracuseStep 2196485 = 411841) (by norm_num)
theorem B2196509 : Blo 1462551 2196509 := bbase (se 3 (by rfl) ⟨411845, by rfl⟩ : syracuseStep 2196509 = 823691) (by norm_num)
theorem B4940837 : Blo 1462551 4940837 := bbase (se 4 (by rfl) ⟨463203, by rfl⟩ : syracuseStep 4940837 = 926407) (by norm_num)
theorem B1852465 : Blo 1462551 1852465 := bbase (se 2 (by rfl) ⟨694674, by rfl⟩ : syracuseStep 1852465 = 1389349) (by norm_num)
theorem B2196533 : Blo 1462551 2196533 := bbase (se 5 (by rfl) ⟨102962, by rfl⟩ : syracuseStep 2196533 = 205925) (by norm_num)
theorem B3294269 : Blo 1462551 3294269 := bbase (se 3 (by rfl) ⟨617675, by rfl⟩ : syracuseStep 3294269 = 1235351) (by norm_num)
theorem B3703877 : Blo 1462551 3703877 := bbase (se 4 (by rfl) ⟨347238, by rfl⟩ : syracuseStep 3703877 = 694477) (by norm_num)
theorem B2196557 : Blo 1462551 2196557 := bbase (se 3 (by rfl) ⟨411854, by rfl⟩ : syracuseStep 2196557 = 823709) (by norm_num)
theorem B42787925 : Blo 1462551 42787925 := bbase (se 8 (by rfl) ⟨250710, by rfl⟩ : syracuseStep 42787925 = 501421) (by norm_num)
theorem B2196581 : Blo 1462551 2196581 := bbase (se 4 (by rfl) ⟨205929, by rfl⟩ : syracuseStep 2196581 = 411859) (by norm_num)
theorem B2196605 : Blo 1462551 2196605 := bbase (se 3 (by rfl) ⟨411863, by rfl⟩ : syracuseStep 2196605 = 823727) (by norm_num)
theorem B1483909 : Blo 1462551 1483909 := bbase (se 4 (by rfl) ⟨139116, by rfl⟩ : syracuseStep 1483909 = 278233) (by norm_num)
theorem B3294341 : Blo 1462551 3294341 := bbase (se 4 (by rfl) ⟨308844, by rfl⟩ : syracuseStep 3294341 = 617689) (by norm_num)
theorem B3957893 : Blo 1462551 3957893 := bbase (se 4 (by rfl) ⟨371052, by rfl⟩ : syracuseStep 3957893 = 742105) (by norm_num)
theorem B1852561 : Blo 1462551 1852561 := bbase (se 2 (by rfl) ⟨694710, by rfl⟩ : syracuseStep 1852561 = 1389421) (by norm_num)
theorem B2196629 : Blo 1462551 2196629 := bbase (se 6 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 2196629 = 102967) (by norm_num)
theorem B2196653 : Blo 1462551 2196653 := bbase (se 3 (by rfl) ⟨411872, by rfl⟩ : syracuseStep 2196653 = 823745) (by norm_num)
theorem B2196677 : Blo 1462551 2196677 := bbase (se 4 (by rfl) ⟨205938, by rfl⟩ : syracuseStep 2196677 = 411877) (by norm_num)
theorem B3294413 : Blo 1462551 3294413 := bbase (se 3 (by rfl) ⟨617702, by rfl⟩ : syracuseStep 3294413 = 1235405) (by norm_num)
theorem B2196701 : Blo 1462551 2196701 := bbase (se 3 (by rfl) ⟨411881, by rfl⟩ : syracuseStep 2196701 = 823763) (by norm_num)
theorem B2196725 : Blo 1462551 2196725 := bbase (se 5 (by rfl) ⟨102971, by rfl⟩ : syracuseStep 2196725 = 205943) (by norm_num)
theorem B3704069 : Blo 1462551 3704069 := bbase (se 4 (by rfl) ⟨347256, by rfl⟩ : syracuseStep 3704069 = 694513) (by norm_num)
theorem B2196749 : Blo 1462551 2196749 := bbase (se 3 (by rfl) ⟨411890, by rfl⟩ : syracuseStep 2196749 = 823781) (by norm_num)
theorem B3294485 : Blo 1462551 3294485 := bbase (se 6 (by rfl) ⟨77214, by rfl⟩ : syracuseStep 3294485 = 154429) (by norm_num)
theorem B6251813 : Blo 1462551 6251813 := bbase (se 4 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 6251813 = 1172215) (by norm_num)
theorem B2196773 : Blo 1462551 2196773 := bbase (se 4 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 2196773 = 411895) (by norm_num)
theorem B1852733 : Blo 1462551 1852733 := bbase (se 3 (by rfl) ⟨347387, by rfl⟩ : syracuseStep 1852733 = 694775) (by norm_num)
theorem B2196797 : Blo 1462551 2196797 := bbase (se 3 (by rfl) ⟨411899, by rfl⟩ : syracuseStep 2196797 = 823799) (by norm_num)
theorem B2344277 : Blo 1462551 2344277 := bbase (se 12 (by rfl) ⟨858, by rfl⟩ : syracuseStep 2344277 = 1717) (by norm_num)
theorem B2196821 : Blo 1462551 2196821 := bbase (se 12 (by rfl) ⟨804, by rfl⟩ : syracuseStep 2196821 = 1609) (by norm_num)
theorem B3294557 : Blo 1462551 3294557 := bbase (se 3 (by rfl) ⟨617729, by rfl⟩ : syracuseStep 3294557 = 1235459) (by norm_num)
theorem B5555573 : Blo 1462551 5555573 := bbase (se 5 (by rfl) ⟨260417, by rfl⟩ : syracuseStep 5555573 = 520835) (by norm_num)
theorem B1852789 : Blo 1462551 1852789 := bbase (se 5 (by rfl) ⟨86849, by rfl⟩ : syracuseStep 1852789 = 173699) (by norm_num)
theorem B8340853 : Blo 1462551 8340853 := bbase (se 5 (by rfl) ⟨390977, by rfl⟩ : syracuseStep 8340853 = 781955) (by norm_num)
theorem B3294629 : Blo 1462551 3294629 := bbase (se 4 (by rfl) ⟨308871, by rfl⟩ : syracuseStep 3294629 = 617743) (by norm_num)
theorem B8898005 : Blo 1462551 8898005 := bbase (se 7 (by rfl) ⟨104273, by rfl⟩ : syracuseStep 8898005 = 208547) (by norm_num)
theorem B2344405 : Blo 1462551 2344405 := bbase (se 7 (by rfl) ⟨27473, by rfl⟩ : syracuseStep 2344405 = 54947) (by norm_num)
theorem B1852885 : Blo 1462551 1852885 := bbase (se 7 (by rfl) ⟨21713, by rfl⟩ : syracuseStep 1852885 = 43427) (by norm_num)
theorem B4941269 : Blo 1462551 4941269 := bbase (se 7 (by rfl) ⟨57905, by rfl⟩ : syracuseStep 4941269 = 115811) (by norm_num)
theorem B3294701 : Blo 1462551 3294701 := bbase (se 3 (by rfl) ⟨617756, by rfl⟩ : syracuseStep 3294701 = 1235513) (by norm_num)
theorem B2778637 : Blo 1462551 2778637 := bbase (se 3 (by rfl) ⟨520994, by rfl⟩ : syracuseStep 2778637 = 1041989) (by norm_num)
theorem B7407125 : Blo 1462551 7407125 := bbase (se 6 (by rfl) ⟨173604, by rfl⟩ : syracuseStep 7407125 = 347209) (by norm_num)
theorem B3294773 : Blo 1462551 3294773 := bbase (se 5 (by rfl) ⟨154442, by rfl⟩ : syracuseStep 3294773 = 308885) (by norm_num)
theorem B3704413 : Blo 1462551 3704413 := bbase (se 3 (by rfl) ⟨694577, by rfl⟩ : syracuseStep 3704413 = 1389155) (by norm_num)
theorem B1877617 : Blo 1462551 1877617 := bbase (se 2 (by rfl) ⟨704106, by rfl⟩ : syracuseStep 1877617 = 1408213) (by norm_num)
theorem B3294845 : Blo 1462551 3294845 := bbase (se 3 (by rfl) ⟨617783, by rfl⟩ : syracuseStep 3294845 = 1235567) (by norm_num)
theorem B1853057 : Blo 1462551 1853057 := bbase (se 2 (by rfl) ⟨694896, by rfl⟩ : syracuseStep 1853057 = 1389793) (by norm_num)
theorem B5555861 : Blo 1462551 5555861 := bbase (se 6 (by rfl) ⟨130215, by rfl⟩ : syracuseStep 5555861 = 260431) (by norm_num)
theorem B2778781 : Blo 1462551 2778781 := bbase (se 3 (by rfl) ⟨521021, by rfl⟩ : syracuseStep 2778781 = 1042043) (by norm_num)
theorem B1853113 : Blo 1462551 1853113 := bbase (se 2 (by rfl) ⟨694917, by rfl⟩ : syracuseStep 1853113 = 1389835) (by norm_num)
theorem B3294917 : Blo 1462551 3294917 := bbase (se 4 (by rfl) ⟨308898, by rfl⟩ : syracuseStep 3294917 = 617797) (by norm_num)
theorem B3704525 : Blo 1462551 3704525 := bbase (se 3 (by rfl) ⟨694598, by rfl⟩ : syracuseStep 3704525 = 1389197) (by norm_num)
theorem B3294989 : Blo 1462551 3294989 := bbase (se 3 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 3294989 = 1235621) (by norm_num)
theorem B1853209 : Blo 1462551 1853209 := bbase (se 2 (by rfl) ⟨694953, by rfl⟩ : syracuseStep 1853209 = 1389907) (by norm_num)
theorem B2778941 : Blo 1462551 2778941 := bbase (se 3 (by rfl) ⟨521051, by rfl⟩ : syracuseStep 2778941 = 1042103) (by norm_num)
theorem B2344789 : Blo 1462551 2344789 := bbase (se 9 (by rfl) ⟨6869, by rfl⟩ : syracuseStep 2344789 = 13739) (by norm_num)
theorem B3295061 : Blo 1462551 3295061 := bbase (se 9 (by rfl) ⟨9653, by rfl⟩ : syracuseStep 3295061 = 19307) (by norm_num)
theorem B4687733 : Blo 1462551 4687733 := bbase (se 5 (by rfl) ⟨219737, by rfl⟩ : syracuseStep 4687733 = 439475) (by norm_num)
theorem B2082685 : Blo 1462551 2082685 := bbase (se 3 (by rfl) ⟨390503, by rfl⟩ : syracuseStep 2082685 = 781007) (by norm_num)
theorem B4941701 : Blo 1462551 4941701 := bbase (se 4 (by rfl) ⟨463284, by rfl⟩ : syracuseStep 4941701 = 926569) (by norm_num)
theorem B3704717 : Blo 1462551 3704717 := bbase (se 3 (by rfl) ⟨694634, by rfl⟩ : syracuseStep 3704717 = 1389269) (by norm_num)
theorem B3295133 : Blo 1462551 3295133 := bbase (se 3 (by rfl) ⟨617837, by rfl⟩ : syracuseStep 3295133 = 1235675) (by norm_num)
theorem B1853381 : Blo 1462551 1853381 := bbase (se 4 (by rfl) ⟨173754, by rfl⟩ : syracuseStep 1853381 = 347509) (by norm_num)
theorem B2779085 : Blo 1462551 2779085 := bbase (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) (by norm_num)
theorem B3008477 : Blo 1462551 3008477 := bbase (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) (by norm_num)
theorem B3295205 : Blo 1462551 3295205 := bbase (se 4 (by rfl) ⟨308925, by rfl⟩ : syracuseStep 3295205 = 617851) (by norm_num)
theorem B1853437 : Blo 1462551 1853437 := bbase (se 3 (by rfl) ⟨347519, by rfl⟩ : syracuseStep 1853437 = 695039) (by norm_num)
theorem B6252565 : Blo 1462551 6252565 := bbase (se 6 (by rfl) ⟨146544, by rfl⟩ : syracuseStep 6252565 = 293089) (by norm_num)
theorem B2345045 : Blo 1462551 2345045 := bbase (se 8 (by rfl) ⟨13740, by rfl⟩ : syracuseStep 2345045 = 27481) (by norm_num)
theorem B1853533 : Blo 1462551 1853533 := bbase (se 3 (by rfl) ⟨347537, by rfl⟩ : syracuseStep 1853533 = 695075) (by norm_num)
theorem B7514261 : Blo 1462551 7514261 := bbase (se 6 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 7514261 = 352231) (by norm_num)
theorem B9373877 : Blo 1462551 9373877 := bbase (se 5 (by rfl) ⟨439400, by rfl⟩ : syracuseStep 9373877 = 878801) (by norm_num)
theorem B3705061 : Blo 1462551 3705061 := bbase (se 4 (by rfl) ⟨347349, by rfl⟩ : syracuseStep 3705061 = 694699) (by norm_num)
theorem B2779373 : Blo 1462551 2779373 := bbase (se 3 (by rfl) ⟨521132, by rfl⟩ : syracuseStep 2779373 = 1042265) (by norm_num)
theorem B3336461 : Blo 1462551 3336461 := bbase (se 3 (by rfl) ⟨625586, by rfl⟩ : syracuseStep 3336461 = 1251173) (by norm_num)
theorem B2468117 : Blo 1462551 2468117 := bbase (se 6 (by rfl) ⟨57846, by rfl⟩ : syracuseStep 2468117 = 115693) (by norm_num)
theorem B4942133 : Blo 1462551 4942133 := bbase (se 5 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 4942133 = 463325) (by norm_num)
theorem B3705173 : Blo 1462551 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B12495221 : Blo 1462551 12495221 := bbase (se 5 (by rfl) ⟨585713, by rfl⟩ : syracuseStep 12495221 = 1171427) (by norm_num)
theorem B2779525 : Blo 1462551 2779525 := bbase (se 4 (by rfl) ⟨260580, by rfl⟩ : syracuseStep 2779525 = 521161) (by norm_num)
theorem B2468245 : Blo 1462551 2468245 := bbase (se 6 (by rfl) ⟨57849, by rfl⟩ : syracuseStep 2468245 = 115699) (by norm_num)
theorem B2083277 : Blo 1462551 2083277 := bbase (se 3 (by rfl) ⟨390614, by rfl⟩ : syracuseStep 2083277 = 781229) (by norm_num)
theorem B2468333 : Blo 1462551 2468333 := bbase (se 3 (by rfl) ⟨462812, by rfl⟩ : syracuseStep 2468333 = 925625) (by norm_num)
theorem B3705365 : Blo 1462551 3705365 := bbase (se 6 (by rfl) ⟨86844, by rfl⟩ : syracuseStep 3705365 = 173689) (by norm_num)
theorem B2083357 : Blo 1462551 2083357 := bbase (se 3 (by rfl) ⟨390629, by rfl⟩ : syracuseStep 2083357 = 781259) (by norm_num)
theorem B2468461 : Blo 1462551 2468461 := bbase (se 3 (by rfl) ⟨462836, by rfl⟩ : syracuseStep 2468461 = 925673) (by norm_num)
theorem B2083477 : Blo 1462551 2083477 := bbase (se 6 (by rfl) ⟨48831, by rfl⟩ : syracuseStep 2083477 = 97663) (by norm_num)
theorem B2779829 : Blo 1462551 2779829 := bbase (se 5 (by rfl) ⟨130304, by rfl⟩ : syracuseStep 2779829 = 260609) (by norm_num)
theorem B2468549 : Blo 1462551 2468549 := bbase (se 4 (by rfl) ⟨231426, by rfl⟩ : syracuseStep 2468549 = 462853) (by norm_num)
theorem B3123917 : Blo 1462551 3123917 := bbase (se 3 (by rfl) ⟨585734, by rfl⟩ : syracuseStep 3123917 = 1171469) (by norm_num)
theorem B4942565 : Blo 1462551 4942565 := bbase (se 4 (by rfl) ⟨463365, by rfl⟩ : syracuseStep 4942565 = 926731) (by norm_num)
theorem B2083573 : Blo 1462551 2083573 := bbase (se 5 (by rfl) ⟨97667, by rfl⟩ : syracuseStep 2083573 = 195335) (by norm_num)
theorem B6253301 : Blo 1462551 6253301 := bbase (se 5 (by rfl) ⟨293123, by rfl⟩ : syracuseStep 6253301 = 586247) (by norm_num)
theorem B30034709 : Blo 1462551 30034709 := bbase (se 6 (by rfl) ⟨703938, by rfl⟩ : syracuseStep 30034709 = 1407877) (by norm_num)
theorem B7408421 : Blo 1462551 7408421 := bbase (se 4 (by rfl) ⟨694539, by rfl⟩ : syracuseStep 7408421 = 1389079) (by norm_num)
theorem B1878833 : Blo 1462551 1878833 := bbase (se 2 (by rfl) ⟨704562, by rfl⟩ : syracuseStep 1878833 = 1409125) (by norm_num)
theorem B5557045 : Blo 1462551 5557045 := bbase (se 5 (by rfl) ⟨260486, by rfl⟩ : syracuseStep 5557045 = 520973) (by norm_num)
theorem B2468677 : Blo 1462551 2468677 := bbase (se 4 (by rfl) ⟨231438, by rfl⟩ : syracuseStep 2468677 = 462877) (by norm_num)
theorem B7129957 : Blo 1462551 7129957 := bbase (se 4 (by rfl) ⟨668433, by rfl⟩ : syracuseStep 7129957 = 1336867) (by norm_num)
theorem B3705709 : Blo 1462551 3705709 := bbase (se 3 (by rfl) ⟨694820, by rfl⟩ : syracuseStep 3705709 = 1389641) (by norm_num)
theorem B1977205 : Blo 1462551 1977205 := bbase (se 5 (by rfl) ⟨92681, by rfl⟩ : syracuseStep 1977205 = 185363) (by norm_num)
theorem B2468765 : Blo 1462551 2468765 := bbase (se 3 (by rfl) ⟨462893, by rfl⟩ : syracuseStep 2468765 = 925787) (by norm_num)
theorem B3517357 : Blo 1462551 3517357 := bbase (se 3 (by rfl) ⟨659504, by rfl⟩ : syracuseStep 3517357 = 1319009) (by norm_num)
theorem B2345917 : Blo 1462551 2345917 := bbase (se 3 (by rfl) ⟨439859, by rfl⟩ : syracuseStep 2345917 = 879719) (by norm_num)
theorem B6679493 : Blo 1462551 6679493 := bbase (se 4 (by rfl) ⟨626202, by rfl⟩ : syracuseStep 6679493 = 1252405) (by norm_num)
theorem B3705821 : Blo 1462551 3705821 := bbase (se 3 (by rfl) ⟨694841, by rfl⟩ : syracuseStep 3705821 = 1389683) (by norm_num)
theorem B2468893 : Blo 1462551 2468893 := bbase (se 3 (by rfl) ⟨462917, by rfl⟩ : syracuseStep 2468893 = 925835) (by norm_num)
theorem B1977373 : Blo 1462551 1977373 := bbase (se 3 (by rfl) ⟨370757, by rfl⟩ : syracuseStep 1977373 = 741515) (by norm_num)
theorem B20024405 : Blo 1462551 20024405 := bbase (se 8 (by rfl) ⟨117330, by rfl⟩ : syracuseStep 20024405 = 234661) (by norm_num)
theorem B5557349 : Blo 1462551 5557349 := bbase (se 4 (by rfl) ⟨521001, by rfl⟩ : syracuseStep 5557349 = 1042003) (by norm_num)
theorem B2468981 : Blo 1462551 2468981 := bbase (se 5 (by rfl) ⟨115733, by rfl⟩ : syracuseStep 2468981 = 231467) (by norm_num)
theorem B3706013 : Blo 1462551 3706013 := bbase (se 3 (by rfl) ⟨694877, by rfl⟩ : syracuseStep 3706013 = 1389755) (by norm_num)
theorem B2084069 : Blo 1462551 2084069 := bbase (se 4 (by rfl) ⟨195381, by rfl⟩ : syracuseStep 2084069 = 390763) (by norm_num)
theorem B2469109 : Blo 1462551 2469109 := bbase (se 5 (by rfl) ⟨115739, by rfl⟩ : syracuseStep 2469109 = 231479) (by norm_num)
theorem B2469197 : Blo 1462551 2469197 := bbase (se 3 (by rfl) ⟨462974, by rfl⟩ : syracuseStep 2469197 = 925949) (by norm_num)
theorem B7032197 : Blo 1462551 7032197 := bbase (se 4 (by rfl) ⟨659268, by rfl⟩ : syracuseStep 7032197 = 1318537) (by norm_num)
theorem B3755429 : Blo 1462551 3755429 := bbase (se 4 (by rfl) ⟨352071, by rfl⟩ : syracuseStep 3755429 = 704143) (by norm_num)
theorem B3124669 : Blo 1462551 3124669 := bbase (se 3 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 3124669 = 1171751) (by norm_num)
theorem B2469325 : Blo 1462551 2469325 := bbase (se 3 (by rfl) ⟨462998, by rfl⟩ : syracuseStep 2469325 = 925997) (by norm_num)
theorem B3706357 : Blo 1462551 3706357 := bbase (se 5 (by rfl) ⟨173735, by rfl⟩ : syracuseStep 3706357 = 347471) (by norm_num)
theorem B2469413 : Blo 1462551 2469413 := bbase (se 4 (by rfl) ⟨231507, by rfl⟩ : syracuseStep 2469413 = 463015) (by norm_num)
theorem B3124813 : Blo 1462551 3124813 := bbase (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) (by norm_num)
theorem B3518029 : Blo 1462551 3518029 := bbase (se 3 (by rfl) ⟨659630, by rfl⟩ : syracuseStep 3518029 = 1319261) (by norm_num)
theorem B3706469 : Blo 1462551 3706469 := bbase (se 4 (by rfl) ⟨347481, by rfl⟩ : syracuseStep 3706469 = 694963) (by norm_num)
theorem B2469541 : Blo 1462551 2469541 := bbase (se 4 (by rfl) ⟨231519, by rfl⟩ : syracuseStep 2469541 = 463039) (by norm_num)
theorem B2223821 : Blo 1462551 2223821 := bbase (se 3 (by rfl) ⟨416966, by rfl⟩ : syracuseStep 2223821 = 833933) (by norm_num)
theorem B2469629 : Blo 1462551 2469629 := bbase (se 3 (by rfl) ⟨463055, by rfl⟩ : syracuseStep 2469629 = 926111) (by norm_num)
theorem B2084621 : Blo 1462551 2084621 := bbase (se 3 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 2084621 = 781733) (by norm_num)
theorem B28503829 : Blo 1462551 28503829 := bbase (se 6 (by rfl) ⟨668058, by rfl⟩ : syracuseStep 28503829 = 1336117) (by norm_num)
theorem B3706661 : Blo 1462551 3706661 := bbase (se 4 (by rfl) ⟨347499, by rfl⟩ : syracuseStep 3706661 = 694999) (by norm_num)
theorem B3518261 : Blo 1462551 3518261 := bbase (se 5 (by rfl) ⟨164918, by rfl⟩ : syracuseStep 3518261 = 329837) (by norm_num)
theorem B2469757 : Blo 1462551 2469757 := bbase (se 3 (by rfl) ⟨463079, by rfl⟩ : syracuseStep 2469757 = 926159) (by norm_num)
theorem B3125189 : Blo 1462551 3125189 := bbase (se 4 (by rfl) ⟨292986, by rfl⟩ : syracuseStep 3125189 = 585973) (by norm_num)
theorem B3518405 : Blo 1462551 3518405 := bbase (se 4 (by rfl) ⟨329850, by rfl⟩ : syracuseStep 3518405 = 659701) (by norm_num)
theorem B2469845 : Blo 1462551 2469845 := bbase (se 7 (by rfl) ⟨28943, by rfl⟩ : syracuseStep 2469845 = 57887) (by norm_num)
theorem B3518453 : Blo 1462551 3518453 := bbase (se 5 (by rfl) ⟨164927, by rfl⟩ : syracuseStep 3518453 = 329855) (by norm_num)
theorem B17813525 : Blo 1462551 17813525 := bbase (se 6 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 17813525 = 835009) (by norm_num)
theorem B2256925 : Blo 1462551 2256925 := bbase (se 3 (by rfl) ⟨423173, by rfl⟩ : syracuseStep 2256925 = 846347) (by norm_num)
theorem B7032869 : Blo 1462551 7032869 := bbase (se 4 (by rfl) ⟨659331, by rfl⟩ : syracuseStep 7032869 = 1318663) (by norm_num)
theorem B7409717 : Blo 1462551 7409717 := bbase (se 5 (by rfl) ⟨347330, by rfl⟩ : syracuseStep 7409717 = 694661) (by norm_num)
theorem B1691713 : Blo 1462551 1691713 := bbase (se 2 (by rfl) ⟨634392, by rfl⟩ : syracuseStep 1691713 = 1268785) (by norm_num)
theorem B6672469 : Blo 1462551 6672469 := bbase (se 8 (by rfl) ⟨39096, by rfl⟩ : syracuseStep 6672469 = 78193) (by norm_num)
theorem B2469973 : Blo 1462551 2469973 := bbase (se 8 (by rfl) ⟨14472, by rfl⟩ : syracuseStep 2469973 = 28945) (by norm_num)
theorem B3707005 : Blo 1462551 3707005 := bbase (se 3 (by rfl) ⟨695063, by rfl⟩ : syracuseStep 3707005 = 1390127) (by norm_num)
theorem B2470061 : Blo 1462551 2470061 := bbase (se 3 (by rfl) ⟨463136, by rfl⟩ : syracuseStep 2470061 = 926273) (by norm_num)
theorem B1757381 : Blo 1462551 1757381 := bbase (se 4 (by rfl) ⟨164754, by rfl⟩ : syracuseStep 1757381 = 329509) (by norm_num)
theorem B3707117 : Blo 1462551 3707117 := bbase (se 3 (by rfl) ⟨695084, by rfl⟩ : syracuseStep 3707117 = 1390169) (by norm_num)
theorem B1503497 : Blo 1462551 1503497 := bbase (se 2 (by rfl) ⟨563811, by rfl⟩ : syracuseStep 1503497 = 1127623) (by norm_num)
theorem B3518741 : Blo 1462551 3518741 := bbase (se 6 (by rfl) ⟨82470, by rfl⟩ : syracuseStep 3518741 = 164941) (by norm_num)
theorem B2470189 : Blo 1462551 2470189 := bbase (se 3 (by rfl) ⟨463160, by rfl⟩ : syracuseStep 2470189 = 926321) (by norm_num)
theorem B3125557 : Blo 1462551 3125557 := bbase (se 5 (by rfl) ⟨146510, by rfl⟩ : syracuseStep 3125557 = 293021) (by norm_num)
theorem B2470277 : Blo 1462551 2470277 := bbase (se 4 (by rfl) ⟨231588, by rfl⟩ : syracuseStep 2470277 = 463177) (by norm_num)
theorem B2470405 : Blo 1462551 2470405 := bbase (se 4 (by rfl) ⟨231600, by rfl⟩ : syracuseStep 2470405 = 463201) (by norm_num)
theorem B2503181 : Blo 1462551 2503181 := bbase (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) (by norm_num)
theorem B2470493 : Blo 1462551 2470493 := bbase (se 3 (by rfl) ⟨463217, by rfl⟩ : syracuseStep 2470493 = 926435) (by norm_num)
theorem B3338869 : Blo 1462551 3338869 := bbase (se 5 (by rfl) ⟨156509, by rfl⟩ : syracuseStep 3338869 = 313019) (by norm_num)
theorem B1503893 : Blo 1462551 1503893 := bbase (se 6 (by rfl) ⟨35247, by rfl⟩ : syracuseStep 1503893 = 70495) (by norm_num)
theorem B2470621 : Blo 1462551 2470621 := bbase (se 3 (by rfl) ⟨463241, by rfl⟩ : syracuseStep 2470621 = 926483) (by norm_num)
theorem B2470709 : Blo 1462551 2470709 := bbase (se 5 (by rfl) ⟨115814, by rfl⟩ : syracuseStep 2470709 = 231629) (by norm_num)
theorem B4936517 : Blo 1462551 4936517 := bbase (se 4 (by rfl) ⟨462798, by rfl⟩ : syracuseStep 4936517 = 925597) (by norm_num)
theorem B1758073 : Blo 1462551 1758073 := bbase (se 2 (by rfl) ⟨659277, by rfl⟩ : syracuseStep 1758073 = 1318555) (by norm_num)
theorem B2503565 : Blo 1462551 2503565 := bbase (se 3 (by rfl) ⟨469418, by rfl⟩ : syracuseStep 2503565 = 938837) (by norm_num)
theorem B2470837 : Blo 1462551 2470837 := bbase (se 5 (by rfl) ⟨115820, by rfl⟩ : syracuseStep 2470837 = 231641) (by norm_num)
theorem B1758169 : Blo 1462551 1758169 := bbase (se 2 (by rfl) ⟨659313, by rfl⟩ : syracuseStep 1758169 = 1318627) (by norm_num)
theorem B2470925 : Blo 1462551 2470925 := bbase (se 3 (by rfl) ⟨463298, by rfl⟩ : syracuseStep 2470925 = 926597) (by norm_num)
theorem B1692725 : Blo 1462551 1692725 := bbase (se 5 (by rfl) ⟨79346, by rfl⟩ : syracuseStep 1692725 = 158693) (by norm_num)
theorem B3339325 : Blo 1462551 3339325 := bbase (se 3 (by rfl) ⟨626123, by rfl⟩ : syracuseStep 3339325 = 1252247) (by norm_num)
theorem B5272661 : Blo 1462551 5272661 := bbase (se 8 (by rfl) ⟨30894, by rfl⟩ : syracuseStep 5272661 = 61789) (by norm_num)
theorem B2471053 : Blo 1462551 2471053 := bbase (se 3 (by rfl) ⟨463322, by rfl⟩ : syracuseStep 2471053 = 926645) (by norm_num)
theorem B5559461 : Blo 1462551 5559461 := bbase (se 4 (by rfl) ⟨521199, by rfl⟩ : syracuseStep 5559461 = 1042399) (by norm_num)
theorem B1668277 : Blo 1462551 1668277 := bbase (se 5 (by rfl) ⟨78200, by rfl⟩ : syracuseStep 1668277 = 156401) (by norm_num)
theorem B2471141 : Blo 1462551 2471141 := bbase (se 4 (by rfl) ⟨231669, by rfl⟩ : syracuseStep 2471141 = 463339) (by norm_num)
theorem B4936949 : Blo 1462551 4936949 := bbase (se 5 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 4936949 = 462839) (by norm_num)
theorem B11867381 : Blo 1462551 11867381 := bbase (se 5 (by rfl) ⟨556283, by rfl⟩ : syracuseStep 11867381 = 1112567) (by norm_num)
theorem B7411013 : Blo 1462551 7411013 := bbase (se 4 (by rfl) ⟨694782, by rfl⟩ : syracuseStep 7411013 = 1389565) (by norm_num)
theorem B1758553 : Blo 1462551 1758553 := bbase (se 2 (by rfl) ⟨659457, by rfl⟩ : syracuseStep 1758553 = 1318915) (by norm_num)
theorem B2471269 : Blo 1462551 2471269 := bbase (se 4 (by rfl) ⟨231681, by rfl⟩ : syracuseStep 2471269 = 463363) (by norm_num)
theorem B3757421 : Blo 1462551 3757421 := bbase (se 3 (by rfl) ⟨704516, by rfl⟩ : syracuseStep 3757421 = 1409033) (by norm_num)
theorem B2471357 : Blo 1462551 2471357 := bbase (se 3 (by rfl) ⟨463379, by rfl⟩ : syracuseStep 2471357 = 926759) (by norm_num)
theorem B5559749 : Blo 1462551 5559749 := bbase (se 4 (by rfl) ⟨521226, by rfl⟩ : syracuseStep 5559749 = 1042453) (by norm_num)
theorem B4691525 : Blo 1462551 4691525 := bbase (se 4 (by rfl) ⟨439830, by rfl⟩ : syracuseStep 4691525 = 879661) (by norm_num)
theorem B3290741 : Blo 1462551 3290741 := bbase (se 5 (by rfl) ⟨154253, by rfl⟩ : syracuseStep 3290741 = 308507) (by norm_num)
theorem B4937381 : Blo 1462551 4937381 := bbase (se 4 (by rfl) ⟨462879, by rfl⟩ : syracuseStep 4937381 = 925759) (by norm_num)
theorem B3290813 : Blo 1462551 3290813 := bbase (se 3 (by rfl) ⟨617027, by rfl⟩ : syracuseStep 3290813 = 1234055) (by norm_num)
theorem B3290885 : Blo 1462551 3290885 := bbase (se 4 (by rfl) ⟨308520, by rfl⟩ : syracuseStep 3290885 = 617041) (by norm_num)
theorem B3127061 : Blo 1462551 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B1562437 : Blo 1462551 1562437 := bbase (se 4 (by rfl) ⟨146478, by rfl⟩ : syracuseStep 1562437 = 292957) (by norm_num)
theorem B3290957 : Blo 1462551 3290957 := bbase (se 3 (by rfl) ⟨617054, by rfl⟩ : syracuseStep 3290957 = 1234109) (by norm_num)
theorem B6420325 : Blo 1462551 6420325 := bbase (se 4 (by rfl) ⟨601905, by rfl⟩ : syracuseStep 6420325 = 1203811) (by norm_num)
theorem B4167557 : Blo 1462551 4167557 := bbase (se 4 (by rfl) ⟨390708, by rfl⟩ : syracuseStep 4167557 = 781417) (by norm_num)
theorem B1562509 : Blo 1462551 1562509 := bbase (se 3 (by rfl) ⟨292970, by rfl⟩ : syracuseStep 1562509 = 585941) (by norm_num)
theorem B3291029 : Blo 1462551 3291029 := bbase (se 6 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 3291029 = 154267) (by norm_num)
theorem B9017237 : Blo 1462551 9017237 := bbase (se 6 (by rfl) ⟨211341, by rfl⟩ : syracuseStep 9017237 = 422683) (by norm_num)
theorem B9508757 : Blo 1462551 9508757 := bbase (se 6 (by rfl) ⟨222861, by rfl⟩ : syracuseStep 9508757 = 445723) (by norm_num)
theorem B3127205 : Blo 1462551 3127205 := bbase (se 4 (by rfl) ⟨293175, by rfl⟩ : syracuseStep 3127205 = 586351) (by norm_num)
theorem B3291101 : Blo 1462551 3291101 := bbase (se 3 (by rfl) ⟨617081, by rfl⟩ : syracuseStep 3291101 = 1234163) (by norm_num)
theorem B3168229 : Blo 1462551 3168229 := bbase (se 4 (by rfl) ⟨297021, by rfl⟩ : syracuseStep 3168229 = 594043) (by norm_num)
theorem B3291173 : Blo 1462551 3291173 := bbase (se 4 (by rfl) ⟨308547, by rfl⟩ : syracuseStep 3291173 = 617095) (by norm_num)
theorem B1562689 : Blo 1462551 1562689 := bbase (se 2 (by rfl) ⟨586008, by rfl⟩ : syracuseStep 1562689 = 1172017) (by norm_num)
theorem B3954757 : Blo 1462551 3954757 := bbase (se 4 (by rfl) ⟨370758, by rfl⟩ : syracuseStep 3954757 = 741517) (by norm_num)
theorem B16660565 : Blo 1462551 16660565 := bbase (se 8 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 16660565 = 195241) (by norm_num)
theorem B4937813 : Blo 1462551 4937813 := bbase (se 8 (by rfl) ⟨28932, by rfl⟩ : syracuseStep 4937813 = 57865) (by norm_num)
theorem B3291245 : Blo 1462551 3291245 := bbase (se 3 (by rfl) ⟨617108, by rfl⟩ : syracuseStep 3291245 = 1234217) (by norm_num)
theorem B1669285 : Blo 1462551 1669285 := bbase (se 4 (by rfl) ⟨156495, by rfl⟩ : syracuseStep 1669285 = 312991) (by norm_num)
theorem B3291317 : Blo 1462551 3291317 := bbase (se 5 (by rfl) ⟨154280, by rfl⟩ : syracuseStep 3291317 = 308561) (by norm_num)
theorem B12507317 : Blo 1462551 12507317 := bbase (se 5 (by rfl) ⟨586280, by rfl⟩ : syracuseStep 12507317 = 1172561) (by norm_num)
theorem B5003477 : Blo 1462551 5003477 := bbase (se 7 (by rfl) ⟨58634, by rfl⟩ : syracuseStep 5003477 = 117269) (by norm_num)
theorem B2504933 : Blo 1462551 2504933 := bbase (se 4 (by rfl) ⟨234837, by rfl⟩ : syracuseStep 2504933 = 469675) (by norm_num)
theorem B3291389 : Blo 1462551 3291389 := bbase (se 3 (by rfl) ⟨617135, by rfl⟩ : syracuseStep 3291389 = 1234271) (by norm_num)
theorem B3127565 : Blo 1462551 3127565 := bbase (se 3 (by rfl) ⟨586418, by rfl⟩ : syracuseStep 3127565 = 1172837) (by norm_num)
theorem B2005277 : Blo 1462551 2005277 := bbase (se 3 (by rfl) ⟨375989, by rfl⟩ : syracuseStep 2005277 = 751979) (by norm_num)
theorem B3291461 : Blo 1462551 3291461 := bbase (se 4 (by rfl) ⟨308574, by rfl⟩ : syracuseStep 3291461 = 617149) (by norm_num)
theorem B3291533 : Blo 1462551 3291533 := bbase (se 3 (by rfl) ⟨617162, by rfl⟩ : syracuseStep 3291533 = 1234325) (by norm_num)
theorem B2193845 : Blo 1462551 2193845 := bbase (se 5 (by rfl) ⟨102836, by rfl⟩ : syracuseStep 2193845 = 205673) (by norm_num)
theorem B2193869 : Blo 1462551 2193869 := bbase (se 3 (by rfl) ⟨411350, by rfl⟩ : syracuseStep 2193869 = 822701) (by norm_num)
theorem B3291605 : Blo 1462551 3291605 := bbase (se 7 (by rfl) ⟨38573, by rfl⟩ : syracuseStep 3291605 = 77147) (by norm_num)
theorem B2193893 : Blo 1462551 2193893 := bbase (se 4 (by rfl) ⟨205677, by rfl⟩ : syracuseStep 2193893 = 411355) (by norm_num)
theorem B2193917 : Blo 1462551 2193917 := bbase (se 3 (by rfl) ⟨411359, by rfl⟩ : syracuseStep 2193917 = 822719) (by norm_num)
theorem B1563133 : Blo 1462551 1563133 := bbase (se 3 (by rfl) ⟨293087, by rfl⟩ : syracuseStep 1563133 = 586175) (by norm_num)
theorem B4938245 : Blo 1462551 4938245 := bbase (se 4 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 4938245 = 925921) (by norm_num)
theorem B2193941 : Blo 1462551 2193941 := bbase (se 6 (by rfl) ⟨51420, by rfl⟩ : syracuseStep 2193941 = 102841) (by norm_num)
theorem B3291677 : Blo 1462551 3291677 := bbase (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) (by norm_num)
theorem B2193965 : Blo 1462551 2193965 := bbase (se 3 (by rfl) ⟨411368, by rfl⟩ : syracuseStep 2193965 = 822737) (by norm_num)
theorem B2193989 : Blo 1462551 2193989 := bbase (se 4 (by rfl) ⟨205686, by rfl⟩ : syracuseStep 2193989 = 411373) (by norm_num)
theorem B7412309 : Blo 1462551 7412309 := bbase (se 8 (by rfl) ⟨43431, by rfl⟩ : syracuseStep 7412309 = 86863) (by norm_num)
theorem B2194013 : Blo 1462551 2194013 := bbase (se 3 (by rfl) ⟨411377, by rfl⟩ : syracuseStep 2194013 = 822755) (by norm_num)
theorem B3291749 : Blo 1462551 3291749 := bbase (se 4 (by rfl) ⟨308601, by rfl⟩ : syracuseStep 3291749 = 617203) (by norm_num)
theorem B2194037 : Blo 1462551 2194037 := bbase (se 5 (by rfl) ⟨102845, by rfl⟩ : syracuseStep 2194037 = 205691) (by norm_num)
theorem B1563257 : Blo 1462551 1563257 := bbase (se 2 (by rfl) ⟨586221, by rfl⟩ : syracuseStep 1563257 = 1172443) (by norm_num)
theorem B5077637 : Blo 1462551 5077637 := bbase (se 4 (by rfl) ⟨476028, by rfl⟩ : syracuseStep 5077637 = 952057) (by norm_num)
theorem B2194061 : Blo 1462551 2194061 := bbase (se 3 (by rfl) ⟨411386, by rfl⟩ : syracuseStep 2194061 = 822773) (by norm_num)
theorem B2194085 : Blo 1462551 2194085 := bbase (se 4 (by rfl) ⟨205695, by rfl⟩ : syracuseStep 2194085 = 411391) (by norm_num)
theorem B3291821 : Blo 1462551 3291821 := bbase (se 3 (by rfl) ⟨617216, by rfl⟩ : syracuseStep 3291821 = 1234433) (by norm_num)
theorem B2194109 : Blo 1462551 2194109 := bbase (se 3 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 2194109 = 822791) (by norm_num)
theorem B2194133 : Blo 1462551 2194133 := bbase (se 7 (by rfl) ⟨25712, by rfl⟩ : syracuseStep 2194133 = 51425) (by norm_num)
theorem B2194157 : Blo 1462551 2194157 := bbase (se 3 (by rfl) ⟨411404, by rfl⟩ : syracuseStep 2194157 = 822809) (by norm_num)
theorem B3291893 : Blo 1462551 3291893 := bbase (se 5 (by rfl) ⟨154307, by rfl⟩ : syracuseStep 3291893 = 308615) (by norm_num)
theorem B2194181 : Blo 1462551 2194181 := bbase (se 4 (by rfl) ⟨205704, by rfl⟩ : syracuseStep 2194181 = 411409) (by norm_num)
theorem B2194205 : Blo 1462551 2194205 := bbase (se 3 (by rfl) ⟨411413, by rfl⟩ : syracuseStep 2194205 = 822827) (by norm_num)
theorem B3955493 : Blo 1462551 3955493 := bbase (se 4 (by rfl) ⟨370827, by rfl⟩ : syracuseStep 3955493 = 741655) (by norm_num)
theorem B2194229 : Blo 1462551 2194229 := bbase (se 5 (by rfl) ⟨102854, by rfl⟩ : syracuseStep 2194229 = 205709) (by norm_num)
theorem B3291965 : Blo 1462551 3291965 := bbase (se 3 (by rfl) ⟨617243, by rfl⟩ : syracuseStep 3291965 = 1234487) (by norm_num)
theorem B2194253 : Blo 1462551 2194253 := bbase (se 3 (by rfl) ⟨411422, by rfl⟩ : syracuseStep 2194253 = 822845) (by norm_num)
theorem B1645393 : Blo 1462551 1645393 := bbase (se 2 (by rfl) ⟨617022, by rfl⟩ : syracuseStep 1645393 = 1234045) (by norm_num)
theorem B2194277 : Blo 1462551 2194277 := bbase (se 4 (by rfl) ⟨205713, by rfl⟩ : syracuseStep 2194277 = 411427) (by norm_num)
theorem B1645429 : Blo 1462551 1645429 := bbase (se 5 (by rfl) ⟨77129, by rfl⟩ : syracuseStep 1645429 = 154259) (by norm_num)
theorem B1563509 : Blo 1462551 1563509 := bbase (se 5 (by rfl) ⟨73289, by rfl⟩ : syracuseStep 1563509 = 146579) (by norm_num)
theorem B2194301 : Blo 1462551 2194301 := bbase (se 3 (by rfl) ⟨411431, by rfl⟩ : syracuseStep 2194301 = 822863) (by norm_num)
theorem B3292037 : Blo 1462551 3292037 := bbase (se 4 (by rfl) ⟨308628, by rfl⟩ : syracuseStep 3292037 = 617257) (by norm_num)
theorem B2194325 : Blo 1462551 2194325 := bbase (se 6 (by rfl) ⟨51429, by rfl⟩ : syracuseStep 2194325 = 102859) (by norm_num)
theorem B1645465 : Blo 1462551 1645465 := bbase (se 2 (by rfl) ⟨617049, by rfl⟩ : syracuseStep 1645465 = 1234099) (by norm_num)
theorem B2194349 : Blo 1462551 2194349 := bbase (se 3 (by rfl) ⟨411440, by rfl⟩ : syracuseStep 2194349 = 822881) (by norm_num)
theorem B4938677 : Blo 1462551 4938677 := bbase (se 5 (by rfl) ⟨231500, by rfl⟩ : syracuseStep 4938677 = 463001) (by norm_num)
theorem B1645501 : Blo 1462551 1645501 := bbase (se 3 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 1645501 = 617063) (by norm_num)
theorem B2816957 : Blo 1462551 2816957 := bbase (se 3 (by rfl) ⟨528179, by rfl⟩ : syracuseStep 2816957 = 1056359) (by norm_num)
theorem B2194373 : Blo 1462551 2194373 := bbase (se 4 (by rfl) ⟨205722, by rfl⟩ : syracuseStep 2194373 = 411445) (by norm_num)
theorem B3292109 : Blo 1462551 3292109 := bbase (se 3 (by rfl) ⟨617270, by rfl⟩ : syracuseStep 3292109 = 1234541) (by norm_num)
theorem B2194397 : Blo 1462551 2194397 := bbase (se 3 (by rfl) ⟨411449, by rfl⟩ : syracuseStep 2194397 = 822899) (by norm_num)
theorem B1645537 : Blo 1462551 1645537 := bbase (se 2 (by rfl) ⟨617076, by rfl⟩ : syracuseStep 1645537 = 1234153) (by norm_num)
theorem B7404533 : Blo 1462551 7404533 := bbase (se 5 (by rfl) ⟨347087, by rfl⟩ : syracuseStep 7404533 = 694175) (by norm_num)
theorem B2194421 : Blo 1462551 2194421 := bbase (se 5 (by rfl) ⟨102863, by rfl⟩ : syracuseStep 2194421 = 205727) (by norm_num)
theorem B5553157 : Blo 1462551 5553157 := bbase (se 4 (by rfl) ⟨520608, by rfl⟩ : syracuseStep 5553157 = 1041217) (by norm_num)
theorem B1645573 : Blo 1462551 1645573 := bbase (se 4 (by rfl) ⟨154272, by rfl⟩ : syracuseStep 1645573 = 308545) (by norm_num)
theorem B2194445 : Blo 1462551 2194445 := bbase (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) (by norm_num)
theorem B3292181 : Blo 1462551 3292181 := bbase (se 6 (by rfl) ⟨77160, by rfl⟩ : syracuseStep 3292181 = 154321) (by norm_num)
theorem B2194469 : Blo 1462551 2194469 := bbase (se 4 (by rfl) ⟨205731, by rfl⟩ : syracuseStep 2194469 = 411463) (by norm_num)
theorem B4168741 : Blo 1462551 4168741 := bbase (se 4 (by rfl) ⟨390819, by rfl⟩ : syracuseStep 4168741 = 781639) (by norm_num)
theorem B1645609 : Blo 1462551 1645609 := bbase (se 2 (by rfl) ⟨617103, by rfl⟩ : syracuseStep 1645609 = 1234207) (by norm_num)
theorem B2194493 : Blo 1462551 2194493 := bbase (se 3 (by rfl) ⟨411467, by rfl⟩ : syracuseStep 2194493 = 822935) (by norm_num)
theorem B1645645 : Blo 1462551 1645645 := bbase (se 3 (by rfl) ⟨308558, by rfl⟩ : syracuseStep 1645645 = 617117) (by norm_num)
theorem B2194517 : Blo 1462551 2194517 := bbase (se 8 (by rfl) ⟨12858, by rfl⟩ : syracuseStep 2194517 = 25717) (by norm_num)
theorem B3292253 : Blo 1462551 3292253 := bbase (se 3 (by rfl) ⟨617297, by rfl⟩ : syracuseStep 3292253 = 1234595) (by norm_num)
theorem B7511141 : Blo 1462551 7511141 := bbase (se 4 (by rfl) ⟨704169, by rfl⟩ : syracuseStep 7511141 = 1408339) (by norm_num)
theorem B2194541 : Blo 1462551 2194541 := bbase (se 3 (by rfl) ⟨411476, by rfl⟩ : syracuseStep 2194541 = 822953) (by norm_num)
theorem B1645681 : Blo 1462551 1645681 := bbase (se 2 (by rfl) ⟨617130, by rfl⟩ : syracuseStep 1645681 = 1234261) (by norm_num)
theorem B2194565 : Blo 1462551 2194565 := bbase (se 4 (by rfl) ⟨205740, by rfl⟩ : syracuseStep 2194565 = 411481) (by norm_num)
theorem B1645717 : Blo 1462551 1645717 := bbase (se 6 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 1645717 = 77143) (by norm_num)
theorem B2194589 : Blo 1462551 2194589 := bbase (se 3 (by rfl) ⟨411485, by rfl⟩ : syracuseStep 2194589 = 822971) (by norm_num)
theorem B3292325 : Blo 1462551 3292325 := bbase (se 4 (by rfl) ⟨308655, by rfl⟩ : syracuseStep 3292325 = 617311) (by norm_num)
theorem B2636965 : Blo 1462551 2636965 := bbase (se 4 (by rfl) ⟨247215, by rfl⟩ : syracuseStep 2636965 = 494431) (by norm_num)
theorem B2194613 : Blo 1462551 2194613 := bbase (se 5 (by rfl) ⟨102872, by rfl⟩ : syracuseStep 2194613 = 205745) (by norm_num)
theorem B1645753 : Blo 1462551 1645753 := bbase (se 2 (by rfl) ⟨617157, by rfl⟩ : syracuseStep 1645753 = 1234315) (by norm_num)
theorem B4168901 : Blo 1462551 4168901 := bbase (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) (by norm_num)
theorem B2194637 : Blo 1462551 2194637 := bbase (se 3 (by rfl) ⟨411494, by rfl⟩ : syracuseStep 2194637 = 822989) (by norm_num)
theorem B1645789 : Blo 1462551 1645789 := bbase (se 3 (by rfl) ⟨308585, by rfl⟩ : syracuseStep 1645789 = 617171) (by norm_num)
theorem B2194661 : Blo 1462551 2194661 := bbase (se 4 (by rfl) ⟨205749, by rfl⟩ : syracuseStep 2194661 = 411499) (by norm_num)
theorem B3292397 : Blo 1462551 3292397 := bbase (se 3 (by rfl) ⟨617324, by rfl⟩ : syracuseStep 3292397 = 1234649) (by norm_num)
theorem B2194685 : Blo 1462551 2194685 := bbase (se 3 (by rfl) ⟨411503, by rfl⟩ : syracuseStep 2194685 = 823007) (by norm_num)
theorem B1645825 : Blo 1462551 1645825 := bbase (se 2 (by rfl) ⟨617184, by rfl⟩ : syracuseStep 1645825 = 1234369) (by norm_num)
theorem B2194709 : Blo 1462551 2194709 := bbase (se 6 (by rfl) ⟨51438, by rfl⟩ : syracuseStep 2194709 = 102877) (by norm_num)
theorem B1645861 : Blo 1462551 1645861 := bbase (se 4 (by rfl) ⟨154299, by rfl⟩ : syracuseStep 1645861 = 308599) (by norm_num)
theorem B2194733 : Blo 1462551 2194733 := bbase (se 3 (by rfl) ⟨411512, by rfl⟩ : syracuseStep 2194733 = 823025) (by norm_num)
theorem B1563953 : Blo 1462551 1563953 := bbase (se 2 (by rfl) ⟨586482, by rfl⟩ : syracuseStep 1563953 = 1172965) (by norm_num)
theorem B5553461 : Blo 1462551 5553461 := bbase (se 5 (by rfl) ⟨260318, by rfl⟩ : syracuseStep 5553461 = 520637) (by norm_num)
theorem B15015221 : Blo 1462551 15015221 := bbase (se 5 (by rfl) ⟨703838, by rfl⟩ : syracuseStep 15015221 = 1407677) (by norm_num)
theorem B3292469 : Blo 1462551 3292469 := bbase (se 5 (by rfl) ⟨154334, by rfl⟩ : syracuseStep 3292469 = 308669) (by norm_num)
theorem B2194757 : Blo 1462551 2194757 := bbase (se 4 (by rfl) ⟨205758, by rfl⟩ : syracuseStep 2194757 = 411517) (by norm_num)
theorem B1645897 : Blo 1462551 1645897 := bbase (se 2 (by rfl) ⟨617211, by rfl⟩ : syracuseStep 1645897 = 1234423) (by norm_num)
theorem B3956053 : Blo 1462551 3956053 := bbase (se 11 (by rfl) ⟨2897, by rfl⟩ : syracuseStep 3956053 = 5795) (by norm_num)
theorem B2194781 : Blo 1462551 2194781 := bbase (se 3 (by rfl) ⟨411521, by rfl⟩ : syracuseStep 2194781 = 823043) (by norm_num)
theorem B4939109 : Blo 1462551 4939109 := bbase (se 4 (by rfl) ⟨463041, by rfl⟩ : syracuseStep 4939109 = 926083) (by norm_num)
theorem B3702125 : Blo 1462551 3702125 := bbase (se 3 (by rfl) ⟨694148, by rfl⟩ : syracuseStep 3702125 = 1388297) (by norm_num)
theorem B1645933 : Blo 1462551 1645933 := bbase (se 3 (by rfl) ⟨308612, by rfl⟩ : syracuseStep 1645933 = 617225) (by norm_num)
theorem B2194805 : Blo 1462551 2194805 := bbase (se 5 (by rfl) ⟨102881, by rfl⟩ : syracuseStep 2194805 = 205763) (by norm_num)
theorem B3292541 : Blo 1462551 3292541 := bbase (se 3 (by rfl) ⟨617351, by rfl⟩ : syracuseStep 3292541 = 1234703) (by norm_num)
theorem B2194829 : Blo 1462551 2194829 := bbase (se 3 (by rfl) ⟨411530, by rfl⟩ : syracuseStep 2194829 = 823061) (by norm_num)
theorem B1645969 : Blo 1462551 1645969 := bbase (se 2 (by rfl) ⟨617238, by rfl⟩ : syracuseStep 1645969 = 1234477) (by norm_num)
theorem B2194853 : Blo 1462551 2194853 := bbase (se 4 (by rfl) ⟨205767, by rfl⟩ : syracuseStep 2194853 = 411535) (by norm_num)
theorem B1646005 : Blo 1462551 1646005 := bbase (se 5 (by rfl) ⟨77156, by rfl⟩ : syracuseStep 1646005 = 154313) (by norm_num)
theorem B4169141 : Blo 1462551 4169141 := bbase (se 5 (by rfl) ⟨195428, by rfl⟩ : syracuseStep 4169141 = 390857) (by norm_num)
theorem B2194877 : Blo 1462551 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B3292613 : Blo 1462551 3292613 := bbase (se 4 (by rfl) ⟨308682, by rfl⟩ : syracuseStep 3292613 = 617365) (by norm_num)
theorem B3005909 : Blo 1462551 3005909 := bbase (se 7 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 3005909 = 70451) (by norm_num)
theorem B2194901 : Blo 1462551 2194901 := bbase (se 7 (by rfl) ⟨25721, by rfl⟩ : syracuseStep 2194901 = 51443) (by norm_num)
theorem B1646041 : Blo 1462551 1646041 := bbase (se 2 (by rfl) ⟨617265, by rfl⟩ : syracuseStep 1646041 = 1234531) (by norm_num)
theorem B2194925 : Blo 1462551 2194925 := bbase (se 3 (by rfl) ⟨411548, by rfl⟩ : syracuseStep 2194925 = 823097) (by norm_num)
theorem B1646077 : Blo 1462551 1646077 := bbase (se 3 (by rfl) ⟨308639, by rfl⟩ : syracuseStep 1646077 = 617279) (by norm_num)
theorem B2194949 : Blo 1462551 2194949 := bbase (se 4 (by rfl) ⟨205776, by rfl⟩ : syracuseStep 2194949 = 411553) (by norm_num)
theorem B3292685 : Blo 1462551 3292685 := bbase (se 3 (by rfl) ⟨617378, by rfl⟩ : syracuseStep 3292685 = 1234757) (by norm_num)
theorem B2194973 : Blo 1462551 2194973 := bbase (se 3 (by rfl) ⟨411557, by rfl⟩ : syracuseStep 2194973 = 823115) (by norm_num)
theorem B1646113 : Blo 1462551 1646113 := bbase (se 2 (by rfl) ⟨617292, by rfl⟩ : syracuseStep 1646113 = 1234585) (by norm_num)
theorem B2194997 : Blo 1462551 2194997 := bbase (se 5 (by rfl) ⟨102890, by rfl⟩ : syracuseStep 2194997 = 205781) (by norm_num)
theorem B1646149 : Blo 1462551 1646149 := bbase (se 4 (by rfl) ⟨154326, by rfl⟩ : syracuseStep 1646149 = 308653) (by norm_num)
theorem B2195021 : Blo 1462551 2195021 := bbase (se 3 (by rfl) ⟨411566, by rfl⟩ : syracuseStep 2195021 = 823133) (by norm_num)
theorem B3292757 : Blo 1462551 3292757 := bbase (se 8 (by rfl) ⟨19293, by rfl⟩ : syracuseStep 3292757 = 38587) (by norm_num)
theorem B2195045 : Blo 1462551 2195045 := bbase (se 4 (by rfl) ⟨205785, by rfl⟩ : syracuseStep 2195045 = 411571) (by norm_num)
theorem B1646185 : Blo 1462551 1646185 := bbase (se 2 (by rfl) ⟨617319, by rfl⟩ : syracuseStep 1646185 = 1234639) (by norm_num)
theorem B2776693 : Blo 1462551 2776693 := bbase (se 5 (by rfl) ⟨130157, by rfl⟩ : syracuseStep 2776693 = 260315) (by norm_num)
theorem B4169333 : Blo 1462551 4169333 := bbase (se 5 (by rfl) ⟨195437, by rfl⟩ : syracuseStep 4169333 = 390875) (by norm_num)
theorem B2195069 : Blo 1462551 2195069 := bbase (se 3 (by rfl) ⟨411575, by rfl⟩ : syracuseStep 2195069 = 823151) (by norm_num)
theorem B1646221 : Blo 1462551 1646221 := bbase (se 3 (by rfl) ⟨308666, by rfl⟩ : syracuseStep 1646221 = 617333) (by norm_num)
theorem B2195093 : Blo 1462551 2195093 := bbase (se 6 (by rfl) ⟨51447, by rfl⟩ : syracuseStep 2195093 = 102895) (by norm_num)
theorem B3292829 : Blo 1462551 3292829 := bbase (se 3 (by rfl) ⟨617405, by rfl⟩ : syracuseStep 3292829 = 1234811) (by norm_num)
theorem B2195117 : Blo 1462551 2195117 := bbase (se 3 (by rfl) ⟨411584, by rfl⟩ : syracuseStep 2195117 = 823169) (by norm_num)
theorem B1646257 : Blo 1462551 1646257 := bbase (se 2 (by rfl) ⟨617346, by rfl⟩ : syracuseStep 1646257 = 1234693) (by norm_num)
theorem B3702469 : Blo 1462551 3702469 := bbase (se 4 (by rfl) ⟨347106, by rfl⟩ : syracuseStep 3702469 = 694213) (by norm_num)
theorem B2195141 : Blo 1462551 2195141 := bbase (se 4 (by rfl) ⟨205794, by rfl⟩ : syracuseStep 2195141 = 411589) (by norm_num)
theorem B1646293 : Blo 1462551 1646293 := bbase (se 7 (by rfl) ⟨19292, by rfl⟩ : syracuseStep 1646293 = 38585) (by norm_num)
theorem B2195165 : Blo 1462551 2195165 := bbase (se 3 (by rfl) ⟨411593, by rfl⟩ : syracuseStep 2195165 = 823187) (by norm_num)
theorem B3292901 : Blo 1462551 3292901 := bbase (se 4 (by rfl) ⟨308709, by rfl⟩ : syracuseStep 3292901 = 617419) (by norm_num)
theorem B1851113 : Blo 1462551 1851113 := bbase (se 2 (by rfl) ⟨694167, by rfl⟩ : syracuseStep 1851113 = 1388335) (by norm_num)
theorem B2195189 : Blo 1462551 2195189 := bbase (se 5 (by rfl) ⟨102899, by rfl⟩ : syracuseStep 2195189 = 205799) (by norm_num)
theorem B11116277 : Blo 1462551 11116277 := bbase (se 5 (by rfl) ⟨521075, by rfl⟩ : syracuseStep 11116277 = 1042151) (by norm_num)
theorem B1646329 : Blo 1462551 1646329 := bbase (se 2 (by rfl) ⟨617373, by rfl⟩ : syracuseStep 1646329 = 1234747) (by norm_num)
theorem B2776837 : Blo 1462551 2776837 := bbase (se 4 (by rfl) ⟨260328, by rfl⟩ : syracuseStep 2776837 = 520657) (by norm_num)
theorem B2195213 : Blo 1462551 2195213 := bbase (se 3 (by rfl) ⟨411602, by rfl⟩ : syracuseStep 2195213 = 823205) (by norm_num)
theorem B4939541 : Blo 1462551 4939541 := bbase (se 6 (by rfl) ⟨115770, by rfl⟩ : syracuseStep 4939541 = 231541) (by norm_num)
theorem B1646365 : Blo 1462551 1646365 := bbase (se 3 (by rfl) ⟨308693, by rfl⟩ : syracuseStep 1646365 = 617387) (by norm_num)
theorem B1851169 : Blo 1462551 1851169 := bbase (se 2 (by rfl) ⟨694188, by rfl⟩ : syracuseStep 1851169 = 1388377) (by norm_num)
theorem B2195237 : Blo 1462551 2195237 := bbase (se 4 (by rfl) ⟨205803, by rfl⟩ : syracuseStep 2195237 = 411607) (by norm_num)
theorem B3292973 : Blo 1462551 3292973 := bbase (se 3 (by rfl) ⟨617432, by rfl⟩ : syracuseStep 3292973 = 1234865) (by norm_num)
theorem B3702581 : Blo 1462551 3702581 := bbase (se 5 (by rfl) ⟨173558, by rfl⟩ : syracuseStep 3702581 = 347117) (by norm_num)
theorem B2195261 : Blo 1462551 2195261 := bbase (se 3 (by rfl) ⟨411611, by rfl⟩ : syracuseStep 2195261 = 823223) (by norm_num)
theorem B1646401 : Blo 1462551 1646401 := bbase (se 2 (by rfl) ⟨617400, by rfl⟩ : syracuseStep 1646401 = 1234801) (by norm_num)
theorem B5930837 : Blo 1462551 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B2195285 : Blo 1462551 2195285 := bbase (se 9 (by rfl) ⟨6431, by rfl⟩ : syracuseStep 2195285 = 12863) (by norm_num)
theorem B3514205 : Blo 1462551 3514205 := bbase (se 3 (by rfl) ⟨658913, by rfl⟩ : syracuseStep 3514205 = 1317827) (by norm_num)
theorem B1646437 : Blo 1462551 1646437 := bbase (se 4 (by rfl) ⟨154353, by rfl⟩ : syracuseStep 1646437 = 308707) (by norm_num)
theorem B7413605 : Blo 1462551 7413605 := bbase (se 4 (by rfl) ⟨695025, by rfl⟩ : syracuseStep 7413605 = 1390051) (by norm_num)
theorem B2342765 : Blo 1462551 2342765 := bbase (se 3 (by rfl) ⟨439268, by rfl⟩ : syracuseStep 2342765 = 878537) (by norm_num)
theorem B2195309 : Blo 1462551 2195309 := bbase (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) (by norm_num)
theorem B3293045 : Blo 1462551 3293045 := bbase (se 5 (by rfl) ⟨154361, by rfl⟩ : syracuseStep 3293045 = 308723) (by norm_num)
theorem B3383165 : Blo 1462551 3383165 := bbase (se 3 (by rfl) ⟨634343, by rfl⟩ : syracuseStep 3383165 = 1268687) (by norm_num)
theorem B1851265 : Blo 1462551 1851265 := bbase (se 2 (by rfl) ⟨694224, by rfl⟩ : syracuseStep 1851265 = 1388449) (by norm_num)
theorem B2195333 : Blo 1462551 2195333 := bbase (se 4 (by rfl) ⟨205812, by rfl⟩ : syracuseStep 2195333 = 411625) (by norm_num)
theorem B1646473 : Blo 1462551 1646473 := bbase (se 2 (by rfl) ⟨617427, by rfl⟩ : syracuseStep 1646473 = 1234855) (by norm_num)
theorem B2195357 : Blo 1462551 2195357 := bbase (se 3 (by rfl) ⟨411629, by rfl⟩ : syracuseStep 2195357 = 823259) (by norm_num)
theorem B2776997 : Blo 1462551 2776997 := bbase (se 4 (by rfl) ⟨260343, by rfl⟩ : syracuseStep 2776997 = 520687) (by norm_num)
theorem B1646509 : Blo 1462551 1646509 := bbase (se 3 (by rfl) ⟨308720, by rfl⟩ : syracuseStep 1646509 = 617441) (by norm_num)
theorem B2195381 : Blo 1462551 2195381 := bbase (se 5 (by rfl) ⟨102908, by rfl⟩ : syracuseStep 2195381 = 205817) (by norm_num)
theorem B3293117 : Blo 1462551 3293117 := bbase (se 3 (by rfl) ⟨617459, by rfl⟩ : syracuseStep 3293117 = 1234919) (by norm_num)
theorem B2195405 : Blo 1462551 2195405 := bbase (se 3 (by rfl) ⟨411638, by rfl⟩ : syracuseStep 2195405 = 823277) (by norm_num)
theorem B2637773 : Blo 1462551 2637773 := bbase (se 3 (by rfl) ⟨494582, by rfl⟩ : syracuseStep 2637773 = 989165) (by norm_num)
theorem B1646545 : Blo 1462551 1646545 := bbase (se 2 (by rfl) ⟨617454, by rfl⟩ : syracuseStep 1646545 = 1234909) (by norm_num)
theorem B5930965 : Blo 1462551 5930965 := bbase (se 7 (by rfl) ⟨69503, by rfl⟩ : syracuseStep 5930965 = 139007) (by norm_num)
theorem B2195429 : Blo 1462551 2195429 := bbase (se 4 (by rfl) ⟨205821, by rfl⟩ : syracuseStep 2195429 = 411643) (by norm_num)
theorem B3702773 : Blo 1462551 3702773 := bbase (se 5 (by rfl) ⟨173567, by rfl⟩ : syracuseStep 3702773 = 347135) (by norm_num)
theorem B1646581 : Blo 1462551 1646581 := bbase (se 5 (by rfl) ⟨77183, by rfl⟩ : syracuseStep 1646581 = 154367) (by norm_num)
theorem B2195453 : Blo 1462551 2195453 := bbase (se 3 (by rfl) ⟨411647, by rfl⟩ : syracuseStep 2195453 = 823295) (by norm_num)
theorem B2195459 : Blo 1462551 2195459 := bstep (se 1 (by rfl) ⟨1646594, by rfl⟩ : syracuseStep 2195459 = 3293189) B3293189
theorem B2195489 : Blo 1462551 2195489 := bstep (se 2 (by rfl) ⟨823308, by rfl⟩ : syracuseStep 2195489 = 1646617) B1646617
theorem B1851427 : Blo 1462551 1851427 := bstep (se 1 (by rfl) ⟨1388570, by rfl⟩ : syracuseStep 1851427 = 2777141) B2777141
theorem B4939811 : Blo 1462551 4939811 := bstep (se 1 (by rfl) ⟨3704858, by rfl⟩ : syracuseStep 4939811 = 7409717) B7409717
theorem B2195507 : Blo 1462551 2195507 := bstep (se 1 (by rfl) ⟨1646630, by rfl⟩ : syracuseStep 2195507 = 3293261) B3293261
theorem B2195537 : Blo 1462551 2195537 := bstep (se 2 (by rfl) ⟨823326, by rfl⟩ : syracuseStep 2195537 = 1646653) B1646653
theorem B7405667 : Blo 1462551 7405667 := bstep (se 1 (by rfl) ⟨5554250, by rfl⟩ : syracuseStep 7405667 = 11108501) B11108501
theorem B2195555 : Blo 1462551 2195555 := bstep (se 1 (by rfl) ⟨1646666, by rfl⟩ : syracuseStep 2195555 = 3293333) B3293333
theorem B8896625 : Blo 1462551 8896625 := bstep (se 2 (by rfl) ⟨3336234, by rfl⟩ : syracuseStep 8896625 = 6672469) B6672469
theorem B3293297 : Blo 1462551 3293297 := bstep (se 2 (by rfl) ⟨1234986, by rfl⟩ : syracuseStep 3293297 = 2469973) B2469973
theorem B1646707 : Blo 1462551 1646707 := bstep (se 1 (by rfl) ⟨1235030, by rfl⟩ : syracuseStep 1646707 = 2470061) B2470061
theorem B2195585 : Blo 1462551 2195585 := bstep (se 2 (by rfl) ⟨823344, by rfl⟩ : syracuseStep 2195585 = 1646689) B1646689
theorem B3293315 : Blo 1462551 3293315 := bstep (se 1 (by rfl) ⟨2469986, by rfl⟩ : syracuseStep 3293315 = 4939973) B4939973
theorem B4513933 : Blo 1462551 4513933 := bstep (se 3 (by rfl) ⟨846362, by rfl⟩ : syracuseStep 4513933 = 1692725) B1692725
theorem B2195603 : Blo 1462551 2195603 := bstep (se 1 (by rfl) ⟨1646702, by rfl⟩ : syracuseStep 2195603 = 3293405) B3293405
theorem B2195633 : Blo 1462551 2195633 := bstep (se 2 (by rfl) ⟨823362, by rfl⟩ : syracuseStep 2195633 = 1646725) B1646725
theorem B2195651 : Blo 1462551 2195651 := bstep (se 1 (by rfl) ⟨1646738, by rfl⟩ : syracuseStep 2195651 = 3293477) B3293477
theorem B2195681 : Blo 1462551 2195681 := bstep (se 2 (by rfl) ⟨823380, by rfl⟩ : syracuseStep 2195681 = 1646761) B1646761
theorem B5554403 : Blo 1462551 5554403 := bstep (se 1 (by rfl) ⟨4165802, by rfl⟩ : syracuseStep 5554403 = 8331605) B8331605
theorem B57016547 : Blo 1462551 57016547 := bstep (se 1 (by rfl) ⟨42762410, by rfl⟩ : syracuseStep 57016547 = 85524821) B85524821
theorem B2195699 : Blo 1462551 2195699 := bstep (se 1 (by rfl) ⟨1646774, by rfl⟩ : syracuseStep 2195699 = 3293549) B3293549
theorem B1646851 : Blo 1462551 1646851 := bstep (se 1 (by rfl) ⟨1235138, by rfl⟩ : syracuseStep 1646851 = 2470277) B2470277
theorem B2195729 : Blo 1462551 2195729 := bstep (se 2 (by rfl) ⟨823398, by rfl⟩ : syracuseStep 2195729 = 1646797) B1646797
theorem B2195747 : Blo 1462551 2195747 := bstep (se 1 (by rfl) ⟨1646810, by rfl⟩ : syracuseStep 2195747 = 3293621) B3293621
theorem B4940081 : Blo 1462551 4940081 := bstep (se 2 (by rfl) ⟨1852530, by rfl⟩ : syracuseStep 4940081 = 3705061) B3705061
theorem B2195777 : Blo 1462551 2195777 := bstep (se 2 (by rfl) ⟨823416, by rfl⟩ : syracuseStep 2195777 = 1646833) B1646833
theorem B17809733 : Blo 1462551 17809733 := bstep (se 4 (by rfl) ⟨1669662, by rfl⟩ : syracuseStep 17809733 = 3339325) B3339325
theorem B2195795 : Blo 1462551 2195795 := bstep (se 1 (by rfl) ⟨1646846, by rfl⟩ : syracuseStep 2195795 = 3293693) B3293693
theorem B2195825 : Blo 1462551 2195825 := bstep (se 2 (by rfl) ⟨823434, by rfl⟩ : syracuseStep 2195825 = 1646869) B1646869
theorem B2195843 : Blo 1462551 2195843 := bstep (se 1 (by rfl) ⟨1646882, by rfl⟩ : syracuseStep 2195843 = 3293765) B3293765
theorem B3293585 : Blo 1462551 3293585 := bstep (se 2 (by rfl) ⟨1235094, by rfl⟩ : syracuseStep 3293585 = 2470189) B2470189
theorem B1646995 : Blo 1462551 1646995 := bstep (se 1 (by rfl) ⟨1235246, by rfl⟩ : syracuseStep 1646995 = 2470493) B2470493
theorem B2195873 : Blo 1462551 2195873 := bstep (se 2 (by rfl) ⟨823452, by rfl⟩ : syracuseStep 2195873 = 1646905) B1646905
theorem B3293603 : Blo 1462551 3293603 := bstep (se 1 (by rfl) ⟨2470202, by rfl⟩ : syracuseStep 3293603 = 4940405) B4940405
theorem B2195891 : Blo 1462551 2195891 := bstep (se 1 (by rfl) ⟨1646918, by rfl⟩ : syracuseStep 2195891 = 3293837) B3293837
theorem B2195921 : Blo 1462551 2195921 := bstep (se 2 (by rfl) ⟨823470, by rfl⟩ : syracuseStep 2195921 = 1646941) B1646941
theorem B2195939 : Blo 1462551 2195939 := bstep (se 1 (by rfl) ⟨1646954, by rfl⟩ : syracuseStep 2195939 = 3293909) B3293909
theorem B2195969 : Blo 1462551 2195969 := bstep (se 2 (by rfl) ⟨823488, by rfl⟩ : syracuseStep 2195969 = 1646977) B1646977
theorem B4686349 : Blo 1462551 4686349 := bstep (se 3 (by rfl) ⟨878690, by rfl⟩ : syracuseStep 4686349 = 1757381) B1757381
theorem B1851923 : Blo 1462551 1851923 := bstep (se 1 (by rfl) ⟨1388942, by rfl⟩ : syracuseStep 1851923 = 2777885) B2777885
theorem B2195987 : Blo 1462551 2195987 := bstep (se 1 (by rfl) ⟨1646990, by rfl⟩ : syracuseStep 2195987 = 3293981) B3293981
theorem B1647139 : Blo 1462551 1647139 := bstep (se 1 (by rfl) ⟨1235354, by rfl⟩ : syracuseStep 1647139 = 2470709) B2470709
theorem B2196017 : Blo 1462551 2196017 := bstep (se 2 (by rfl) ⟨823506, by rfl⟩ : syracuseStep 2196017 = 1647013) B1647013
theorem B2196035 : Blo 1462551 2196035 := bstep (se 1 (by rfl) ⟨1647026, by rfl⟩ : syracuseStep 2196035 = 3294053) B3294053
theorem B2196065 : Blo 1462551 2196065 := bstep (se 2 (by rfl) ⟨823524, by rfl⟩ : syracuseStep 2196065 = 1647049) B1647049
theorem B2196083 : Blo 1462551 2196083 := bstep (se 1 (by rfl) ⟨1647062, by rfl⟩ : syracuseStep 2196083 = 3294125) B3294125
theorem B3703441 : Blo 1462551 3703441 := bstep (se 2 (by rfl) ⟨1388790, by rfl⟩ : syracuseStep 3703441 = 2777581) B2777581
theorem B2196113 : Blo 1462551 2196113 := bstep (se 2 (by rfl) ⟨823542, by rfl⟩ : syracuseStep 2196113 = 1647085) B1647085
theorem B2196131 : Blo 1462551 2196131 := bstep (se 1 (by rfl) ⟨1647098, by rfl⟩ : syracuseStep 2196131 = 3294197) B3294197
theorem B3293873 : Blo 1462551 3293873 := bstep (se 2 (by rfl) ⟨1235202, by rfl⟩ : syracuseStep 3293873 = 2470405) B2470405
theorem B1647283 : Blo 1462551 1647283 := bstep (se 1 (by rfl) ⟨1235462, by rfl⟩ : syracuseStep 1647283 = 2470925) B2470925
theorem B2196161 : Blo 1462551 2196161 := bstep (se 2 (by rfl) ⟨823560, by rfl⟩ : syracuseStep 2196161 = 1647121) B1647121
theorem B3293891 : Blo 1462551 3293891 := bstep (se 1 (by rfl) ⟨2470418, by rfl⟩ : syracuseStep 3293891 = 4940837) B4940837
theorem B15819461 : Blo 1462551 15819461 := bstep (se 4 (by rfl) ⟨1483074, by rfl⟩ : syracuseStep 15819461 = 2966149) B2966149
theorem B7914181 : Blo 1462551 7914181 := bstep (se 4 (by rfl) ⟨741954, by rfl⟩ : syracuseStep 7914181 = 1483909) B1483909
theorem B2777809 : Blo 1462551 2777809 := bstep (se 2 (by rfl) ⟨1041678, by rfl⟩ : syracuseStep 2777809 = 2083357) B2083357
theorem B2196179 : Blo 1462551 2196179 := bstep (se 1 (by rfl) ⟨1647134, by rfl⟩ : syracuseStep 2196179 = 3294269) B3294269
theorem B28525283 : Blo 1462551 28525283 := bstep (se 1 (by rfl) ⟨21393962, by rfl⟩ : syracuseStep 28525283 = 42787925) B42787925
theorem B2196209 : Blo 1462551 2196209 := bstep (se 2 (by rfl) ⟨823578, by rfl⟩ : syracuseStep 2196209 = 1647157) B1647157
theorem B2196227 : Blo 1462551 2196227 := bstep (se 1 (by rfl) ⟨1647170, by rfl⟩ : syracuseStep 2196227 = 3294341) B3294341
theorem B2638595 : Blo 1462551 2638595 := bstep (se 1 (by rfl) ⟨1978946, by rfl⟩ : syracuseStep 2638595 = 3957893) B3957893
theorem B2196257 : Blo 1462551 2196257 := bstep (se 2 (by rfl) ⟨823596, by rfl⟩ : syracuseStep 2196257 = 1647193) B1647193
theorem B4170541 : Blo 1462551 4170541 := bstep (se 3 (by rfl) ⟨781976, by rfl⟩ : syracuseStep 4170541 = 1563953) B1563953
theorem B2196275 : Blo 1462551 2196275 := bstep (se 1 (by rfl) ⟨1647206, by rfl⟩ : syracuseStep 2196275 = 3294413) B3294413
theorem B1647427 : Blo 1462551 1647427 := bstep (se 1 (by rfl) ⟨1235570, by rfl⟩ : syracuseStep 1647427 = 2471141) B2471141
theorem B4940621 : Blo 1462551 4940621 := bstep (se 3 (by rfl) ⟨926366, by rfl⟩ : syracuseStep 4940621 = 1852733) B1852733
theorem B2196305 : Blo 1462551 2196305 := bstep (se 2 (by rfl) ⟨823614, by rfl⟩ : syracuseStep 2196305 = 1647229) B1647229
theorem B2196323 : Blo 1462551 2196323 := bstep (se 1 (by rfl) ⟨1647242, by rfl⟩ : syracuseStep 2196323 = 3294485) B3294485
theorem B2777969 : Blo 1462551 2777969 := bstep (se 2 (by rfl) ⟨1041738, by rfl⟩ : syracuseStep 2777969 = 2083477) B2083477
theorem B2196353 : Blo 1462551 2196353 := bstep (se 2 (by rfl) ⟨823632, by rfl⟩ : syracuseStep 2196353 = 1647265) B1647265
theorem B4940675 : Blo 1462551 4940675 := bstep (se 1 (by rfl) ⟨3705506, by rfl⟩ : syracuseStep 4940675 = 7411013) B7411013
theorem B7406477 : Blo 1462551 7406477 := bstep (se 3 (by rfl) ⟨1388714, by rfl⟩ : syracuseStep 7406477 = 2777429) B2777429
theorem B2196371 : Blo 1462551 2196371 := bstep (se 1 (by rfl) ⟨1647278, by rfl⟩ : syracuseStep 2196371 = 3294557) B3294557
theorem B3703715 : Blo 1462551 3703715 := bstep (se 1 (by rfl) ⟨2777786, by rfl⟩ : syracuseStep 3703715 = 5555573) B5555573
theorem B2196401 : Blo 1462551 2196401 := bstep (se 2 (by rfl) ⟨823650, by rfl⟩ : syracuseStep 2196401 = 1647301) B1647301
theorem B2196419 : Blo 1462551 2196419 := bstep (se 1 (by rfl) ⟨1647314, by rfl⟩ : syracuseStep 2196419 = 3294629) B3294629
theorem B3294161 : Blo 1462551 3294161 := bstep (se 2 (by rfl) ⟨1235310, by rfl⟩ : syracuseStep 3294161 = 2470621) B2470621
theorem B1647571 : Blo 1462551 1647571 := bstep (se 1 (by rfl) ⟨1235678, by rfl⟩ : syracuseStep 1647571 = 2471357) B2471357
theorem B2196449 : Blo 1462551 2196449 := bstep (se 2 (by rfl) ⟨823668, by rfl⟩ : syracuseStep 2196449 = 1647337) B1647337
theorem B5932003 : Blo 1462551 5932003 := bstep (se 1 (by rfl) ⟨4449002, by rfl⟩ : syracuseStep 5932003 = 8898005) B8898005
theorem B3294179 : Blo 1462551 3294179 := bstep (se 1 (by rfl) ⟨2470634, by rfl⟩ : syracuseStep 3294179 = 4941269) B4941269
theorem B2196467 : Blo 1462551 2196467 := bstep (se 1 (by rfl) ⟨1647350, by rfl⟩ : syracuseStep 2196467 = 3294701) B3294701
theorem B2196497 : Blo 1462551 2196497 := bstep (se 2 (by rfl) ⟨823686, by rfl⟩ : syracuseStep 2196497 = 1647373) B1647373
theorem B2196515 : Blo 1462551 2196515 := bstep (se 1 (by rfl) ⟨1647386, by rfl⟩ : syracuseStep 2196515 = 3294773) B3294773
theorem B2196545 : Blo 1462551 2196545 := bstep (se 2 (by rfl) ⟨823704, by rfl⟩ : syracuseStep 2196545 = 1647409) B1647409
theorem B2196563 : Blo 1462551 2196563 := bstep (se 1 (by rfl) ⟨1647422, by rfl⟩ : syracuseStep 2196563 = 3294845) B3294845
theorem B3703907 : Blo 1462551 3703907 := bstep (se 1 (by rfl) ⟨2777930, by rfl⟩ : syracuseStep 3703907 = 5555861) B5555861
theorem B2196593 : Blo 1462551 2196593 := bstep (se 2 (by rfl) ⟨823722, by rfl⟩ : syracuseStep 2196593 = 1647445) B1647445
theorem B2196611 : Blo 1462551 2196611 := bstep (se 1 (by rfl) ⟨1647458, by rfl⟩ : syracuseStep 2196611 = 3294917) B3294917
theorem B4940945 : Blo 1462551 4940945 := bstep (se 2 (by rfl) ⟨1852854, by rfl⟩ : syracuseStep 4940945 = 3705709) B3705709
theorem B2344097 : Blo 1462551 2344097 := bstep (se 2 (by rfl) ⟨879036, by rfl⟩ : syracuseStep 2344097 = 1758073) B1758073
theorem B2196641 : Blo 1462551 2196641 := bstep (se 2 (by rfl) ⟨823740, by rfl⟩ : syracuseStep 2196641 = 1647481) B1647481
theorem B2196659 : Blo 1462551 2196659 := bstep (se 1 (by rfl) ⟨1647494, by rfl⟩ : syracuseStep 2196659 = 3294989) B3294989
theorem B5555405 : Blo 1462551 5555405 := bstep (se 3 (by rfl) ⟨1041638, by rfl⟩ : syracuseStep 5555405 = 2083277) B2083277
theorem B2196689 : Blo 1462551 2196689 := bstep (se 2 (by rfl) ⟨823758, by rfl⟩ : syracuseStep 2196689 = 1647517) B1647517
theorem B1852627 : Blo 1462551 1852627 := bstep (se 1 (by rfl) ⟨1389470, by rfl⟩ : syracuseStep 1852627 = 2778941) B2778941
theorem B2196707 : Blo 1462551 2196707 := bstep (se 1 (by rfl) ⟨1647530, by rfl⟩ : syracuseStep 2196707 = 3295061) B3295061
theorem B3294449 : Blo 1462551 3294449 := bstep (se 2 (by rfl) ⟨1235418, by rfl⟩ : syracuseStep 3294449 = 2470837) B2470837
theorem B2778371 : Blo 1462551 2778371 := bstep (se 1 (by rfl) ⟨2083778, by rfl⟩ : syracuseStep 2778371 = 4167557) B4167557
theorem B3294467 : Blo 1462551 3294467 := bstep (se 1 (by rfl) ⟨2470850, by rfl⟩ : syracuseStep 3294467 = 4941701) B4941701
theorem B2196737 : Blo 1462551 2196737 := bstep (se 2 (by rfl) ⟨823776, by rfl⟩ : syracuseStep 2196737 = 1647553) B1647553
theorem B2196755 : Blo 1462551 2196755 := bstep (se 1 (by rfl) ⟨1647566, by rfl⟩ : syracuseStep 2196755 = 3295133) B3295133
theorem B2344225 : Blo 1462551 2344225 := bstep (se 2 (by rfl) ⟨879084, by rfl⟩ : syracuseStep 2344225 = 1758169) B1758169
theorem B2196785 : Blo 1462551 2196785 := bstep (se 2 (by rfl) ⟨823794, by rfl⟩ : syracuseStep 2196785 = 1647589) B1647589
theorem B1852723 : Blo 1462551 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B2196803 : Blo 1462551 2196803 := bstep (se 1 (by rfl) ⟨1647602, by rfl⟩ : syracuseStep 2196803 = 3295205) B3295205
theorem B152020421 : Blo 1462551 152020421 := bstep (se 4 (by rfl) ⟨14251914, by rfl⟩ : syracuseStep 152020421 = 28503829) B28503829
theorem B3335651 : Blo 1462551 3335651 := bstep (se 1 (by rfl) ⟨2501738, by rfl⟩ : syracuseStep 3335651 = 5003477) B5003477
theorem B12510733 : Blo 1462551 12510733 := bstep (se 3 (by rfl) ⟨2345762, by rfl⟩ : syracuseStep 12510733 = 4691525) B4691525
theorem B3294737 : Blo 1462551 3294737 := bstep (se 2 (by rfl) ⟨1235526, by rfl⟩ : syracuseStep 3294737 = 2471053) B2471053
theorem B3294755 : Blo 1462551 3294755 := bstep (se 1 (by rfl) ⟨2471066, by rfl⟩ : syracuseStep 3294755 = 4942133) B4942133
theorem B101426741 : Blo 1462551 101426741 := bstep (se 5 (by rfl) ⟨4754378, by rfl⟩ : syracuseStep 101426741 = 9508757) B9508757
theorem B11118221 : Blo 1462551 11118221 := bstep (se 3 (by rfl) ⟨2084666, by rfl⟩ : syracuseStep 11118221 = 4169333) B4169333
theorem B4941485 : Blo 1462551 4941485 := bstep (se 3 (by rfl) ⟨926528, by rfl⟩ : syracuseStep 4941485 = 1853057) B1853057
theorem B4941539 : Blo 1462551 4941539 := bstep (se 1 (by rfl) ⟨3706154, by rfl⟩ : syracuseStep 4941539 = 7412309) B7412309
theorem B3385091 : Blo 1462551 3385091 := bstep (se 1 (by rfl) ⟨2538818, by rfl⟩ : syracuseStep 3385091 = 5077637) B5077637
theorem B1853219 : Blo 1462551 1853219 := bstep (se 1 (by rfl) ⟨1389914, by rfl⟩ : syracuseStep 1853219 = 2779829) B2779829
theorem B3295025 : Blo 1462551 3295025 := bstep (se 2 (by rfl) ⟨1235634, by rfl⟩ : syracuseStep 3295025 = 2471269) B2471269
theorem B2082611 : Blo 1462551 2082611 := bstep (se 1 (by rfl) ⟨1561958, by rfl⟩ : syracuseStep 2082611 = 3123917) B3123917
theorem B3295043 : Blo 1462551 3295043 := bstep (se 1 (by rfl) ⟨2471282, by rfl⟩ : syracuseStep 3295043 = 4942565) B4942565
theorem B20023139 : Blo 1462551 20023139 := bstep (se 1 (by rfl) ⟨15017354, by rfl⟩ : syracuseStep 20023139 = 30034709) B30034709
theorem B1877971 : Blo 1462551 1877971 := bstep (se 1 (by rfl) ⟨1408478, by rfl⟩ : syracuseStep 1877971 = 2816957) B2816957
theorem B4941809 : Blo 1462551 4941809 := bstep (se 2 (by rfl) ⟨1853178, by rfl⟩ : syracuseStep 4941809 = 3706357) B3706357
theorem B3704849 : Blo 1462551 3704849 := bstep (se 2 (by rfl) ⟨1389318, by rfl⟩ : syracuseStep 3704849 = 2778637) B2778637
theorem B3704899 : Blo 1462551 3704899 := bstep (se 1 (by rfl) ⟨2778674, by rfl⟩ : syracuseStep 3704899 = 5557349) B5557349
theorem B5007427 : Blo 1462551 5007427 := bstep (se 1 (by rfl) ⟨3755570, by rfl⟩ : syracuseStep 5007427 = 7511141) B7511141
theorem B8333381 : Blo 1462551 8333381 := bstep (se 4 (by rfl) ⟨781254, by rfl⟩ : syracuseStep 8333381 = 1562509) B1562509
theorem B2779267 : Blo 1462551 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B3705041 : Blo 1462551 3705041 := bstep (se 2 (by rfl) ⟨1389390, by rfl⟩ : syracuseStep 3705041 = 2778781) B2778781
theorem B2468083 : Blo 1462551 2468083 := bstep (se 1 (by rfl) ⟨1851062, by rfl⟩ : syracuseStep 2468083 = 3702125) B3702125
theorem B4688131 : Blo 1462551 4688131 := bstep (se 1 (by rfl) ⟨3516098, by rfl⟩ : syracuseStep 4688131 = 7032197) B7032197
theorem B2779427 : Blo 1462551 2779427 := bstep (se 1 (by rfl) ⟨2084570, by rfl⟩ : syracuseStep 2779427 = 4169141) B4169141
theorem B9021773 : Blo 1462551 9021773 := bstep (se 3 (by rfl) ⟨1691582, by rfl⟩ : syracuseStep 9021773 = 3383165) B3383165
theorem B2468225 : Blo 1462551 2468225 := bstep (se 2 (by rfl) ⟨925584, by rfl⟩ : syracuseStep 2468225 = 1851169) B1851169
theorem B2083249 : Blo 1462551 2083249 := bstep (se 2 (by rfl) ⟨781218, by rfl⟩ : syracuseStep 2083249 = 1562437) B1562437
theorem B2468353 : Blo 1462551 2468353 := bstep (se 2 (by rfl) ⟨925632, by rfl⟩ : syracuseStep 2468353 = 1851265) B1851265
theorem B8333837 : Blo 1462551 8333837 := bstep (se 3 (by rfl) ⟨1562594, by rfl⟩ : syracuseStep 8333837 = 3125189) B3125189
theorem B4942349 : Blo 1462551 4942349 := bstep (se 3 (by rfl) ⟨926690, by rfl⟩ : syracuseStep 4942349 = 1853381) B1853381
theorem B2468387 : Blo 1462551 2468387 := bstep (se 1 (by rfl) ⟨1851290, by rfl⟩ : syracuseStep 2468387 = 3702581) B3702581
theorem B2345507 : Blo 1462551 2345507 := bstep (se 1 (by rfl) ⟨1759130, by rfl⟩ : syracuseStep 2345507 = 3518261) B3518261
theorem B4942403 : Blo 1462551 4942403 := bstep (se 1 (by rfl) ⟨3706802, by rfl⟩ : syracuseStep 4942403 = 7413605) B7413605
theorem B7907953 : Blo 1462551 7907953 := bstep (se 2 (by rfl) ⟨2965482, by rfl⟩ : syracuseStep 7907953 = 5930965) B5930965
theorem B2345603 : Blo 1462551 2345603 := bstep (se 1 (by rfl) ⟨1759202, by rfl⟩ : syracuseStep 2345603 = 3518405) B3518405
theorem B2468515 : Blo 1462551 2468515 := bstep (se 1 (by rfl) ⟨1851386, by rfl⟩ : syracuseStep 2468515 = 3702773) B3702773
theorem B2345635 : Blo 1462551 2345635 := bstep (se 1 (by rfl) ⟨1759226, by rfl⟩ : syracuseStep 2345635 = 3518453) B3518453
theorem B4688579 : Blo 1462551 4688579 := bstep (se 1 (by rfl) ⟨3516434, by rfl⟩ : syracuseStep 4688579 = 7032869) B7032869
theorem B3009233 : Blo 1462551 3009233 := bstep (se 2 (by rfl) ⟨1128462, by rfl⟩ : syracuseStep 3009233 = 2256925) B2256925
theorem B2083585 : Blo 1462551 2083585 := bstep (se 2 (by rfl) ⟨781344, by rfl⟩ : syracuseStep 2083585 = 1562689) B1562689
theorem B2255617 : Blo 1462551 2255617 := bstep (se 2 (by rfl) ⟨845856, by rfl⟩ : syracuseStep 2255617 = 1691713) B1691713
theorem B6679331 : Blo 1462551 6679331 := bstep (se 1 (by rfl) ⟨5009498, by rfl⟩ : syracuseStep 6679331 = 10018997) B10018997
theorem B2468657 : Blo 1462551 2468657 := bstep (se 2 (by rfl) ⟨925746, by rfl⟩ : syracuseStep 2468657 = 1851493) B1851493
theorem B4942673 : Blo 1462551 4942673 := bstep (se 2 (by rfl) ⟨1853502, by rfl⟩ : syracuseStep 4942673 = 3707005) B3707005
theorem B14060429 : Blo 1462551 14060429 := bstep (se 3 (by rfl) ⟨2636330, by rfl⟩ : syracuseStep 14060429 = 5272661) B5272661
theorem B6253453 : Blo 1462551 6253453 := bstep (se 3 (by rfl) ⟨1172522, by rfl⟩ : syracuseStep 6253453 = 2345045) B2345045
theorem B2468785 : Blo 1462551 2468785 := bstep (se 2 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 2468785 = 1851589) B1851589
theorem B2468819 : Blo 1462551 2468819 := bstep (se 1 (by rfl) ⟨1851614, by rfl⟩ : syracuseStep 2468819 = 3703229) B3703229
theorem B2468947 : Blo 1462551 2468947 := bstep (se 1 (by rfl) ⟨1851710, by rfl⟩ : syracuseStep 2468947 = 3703421) B3703421
theorem B12495971 : Blo 1462551 12495971 := bstep (se 1 (by rfl) ⟨9371978, by rfl⟩ : syracuseStep 12495971 = 18743957) B18743957
theorem B3124369 : Blo 1462551 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B3706033 : Blo 1462551 3706033 := bstep (se 2 (by rfl) ⟨1389762, by rfl⟩ : syracuseStep 3706033 = 2779525) B2779525
theorem B2469089 : Blo 1462551 2469089 := bstep (se 2 (by rfl) ⟨925908, by rfl⟩ : syracuseStep 2469089 = 1851817) B1851817
theorem B5557517 : Blo 1462551 5557517 := bstep (se 3 (by rfl) ⟨1042034, by rfl⟩ : syracuseStep 5557517 = 2084069) B2084069
theorem B2084177 : Blo 1462551 2084177 := bstep (se 2 (by rfl) ⟨781566, by rfl⟩ : syracuseStep 2084177 = 1563133) B1563133
theorem B2469217 : Blo 1462551 2469217 := bstep (se 2 (by rfl) ⟨925956, by rfl⟩ : syracuseStep 2469217 = 1851913) B1851913
theorem B2469251 : Blo 1462551 2469251 := bstep (se 1 (by rfl) ⟨1851938, by rfl⟩ : syracuseStep 2469251 = 3703877) B3703877
theorem B9383309 : Blo 1462551 9383309 := bstep (se 3 (by rfl) ⟨1759370, by rfl⟩ : syracuseStep 9383309 = 3518741) B3518741
theorem B3706307 : Blo 1462551 3706307 := bstep (se 1 (by rfl) ⟨2779730, by rfl⟩ : syracuseStep 3706307 = 5559461) B5559461
theorem B4451825 : Blo 1462551 4451825 := bstep (se 2 (by rfl) ⟨1669434, by rfl⟩ : syracuseStep 4451825 = 3338869) B3338869
theorem B2469379 : Blo 1462551 2469379 := bstep (se 1 (by rfl) ⟨1852034, by rfl⟩ : syracuseStep 2469379 = 3704069) B3704069
theorem B3706499 : Blo 1462551 3706499 := bstep (se 1 (by rfl) ⟨2779874, by rfl⟩ : syracuseStep 3706499 = 5559749) B5559749
theorem B2469521 : Blo 1462551 2469521 := bstep (se 2 (by rfl) ⟨926070, by rfl⟩ : syracuseStep 2469521 = 1852141) B1852141
theorem B7409393 : Blo 1462551 7409393 := bstep (se 2 (by rfl) ⟨2778522, by rfl⟩ : syracuseStep 7409393 = 5557045) B5557045
theorem B2469649 : Blo 1462551 2469649 := bstep (se 2 (by rfl) ⟨926118, by rfl⟩ : syracuseStep 2469649 = 1852237) B1852237
theorem B9506609 : Blo 1462551 9506609 := bstep (se 2 (by rfl) ⟨3564978, by rfl⟩ : syracuseStep 9506609 = 7129957) B7129957
theorem B2469683 : Blo 1462551 2469683 := bstep (se 1 (by rfl) ⟨1852262, by rfl⟩ : syracuseStep 2469683 = 3704525) B3704525
theorem B2084707 : Blo 1462551 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B4689809 : Blo 1462551 4689809 := bstep (se 2 (by rfl) ⟨1758678, by rfl⟩ : syracuseStep 4689809 = 3517357) B3517357
theorem B3125155 : Blo 1462551 3125155 := bstep (se 1 (by rfl) ⟨2343866, by rfl⟩ : syracuseStep 3125155 = 4687733) B4687733
theorem B2469811 : Blo 1462551 2469811 := bstep (se 1 (by rfl) ⟨1852358, by rfl⟩ : syracuseStep 2469811 = 3704717) B3704717
theorem B11112389 : Blo 1462551 11112389 := bstep (se 4 (by rfl) ⟨1041786, by rfl⟩ : syracuseStep 11112389 = 2083573) B2083573
theorem B5558321 : Blo 1462551 5558321 := bstep (se 2 (by rfl) ⟨2084370, by rfl⟩ : syracuseStep 5558321 = 4168741) B4168741
theorem B2469953 : Blo 1462551 2469953 := bstep (se 2 (by rfl) ⟨926232, by rfl⟩ : syracuseStep 2469953 = 1852465) B1852465
theorem B5009507 : Blo 1462551 5009507 := bstep (se 1 (by rfl) ⟨3757130, by rfl⟩ : syracuseStep 5009507 = 7514261) B7514261
theorem B2224307 : Blo 1462551 2224307 := bstep (se 1 (by rfl) ⟨1668230, by rfl⟩ : syracuseStep 2224307 = 3336461) B3336461
theorem B2085043 : Blo 1462551 2085043 := bstep (se 1 (by rfl) ⟨1563782, by rfl⟩ : syracuseStep 2085043 = 3127565) B3127565
theorem B2470081 : Blo 1462551 2470081 := bstep (se 2 (by rfl) ⟨926280, by rfl⟩ : syracuseStep 2470081 = 1852561) B1852561
theorem B2470115 : Blo 1462551 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B2224369 : Blo 1462551 2224369 := bstep (se 2 (by rfl) ⟨834138, by rfl⟩ : syracuseStep 2224369 = 1668277) B1668277
theorem B1462563 : Blo 1462551 1462563 := bstep (se 1 (by rfl) ⟨1096922, by rfl⟩ : syracuseStep 1462563 = 2193845) B2193845
theorem B1462579 : Blo 1462551 1462579 := bstep (se 1 (by rfl) ⟨1096934, by rfl⟩ : syracuseStep 1462579 = 2193869) B2193869
theorem B1462595 : Blo 1462551 1462595 := bstep (se 1 (by rfl) ⟨1096946, by rfl⟩ : syracuseStep 1462595 = 2193893) B2193893
theorem B1462611 : Blo 1462551 1462611 := bstep (se 1 (by rfl) ⟨1096958, by rfl⟩ : syracuseStep 1462611 = 2193917) B2193917
theorem B1462627 : Blo 1462551 1462627 := bstep (se 1 (by rfl) ⟨1096970, by rfl⟩ : syracuseStep 1462627 = 2193941) B2193941
theorem B2470243 : Blo 1462551 2470243 := bstep (se 1 (by rfl) ⟨1852682, by rfl⟩ : syracuseStep 2470243 = 3705365) B3705365
theorem B1462643 : Blo 1462551 1462643 := bstep (se 1 (by rfl) ⟨1096982, by rfl⟩ : syracuseStep 1462643 = 2193965) B2193965
theorem B1462659 : Blo 1462551 1462659 := bstep (se 1 (by rfl) ⟨1096994, by rfl⟩ : syracuseStep 1462659 = 2193989) B2193989
theorem B4010381 : Blo 1462551 4010381 := bstep (se 3 (by rfl) ⟨751946, by rfl⟩ : syracuseStep 4010381 = 1503893) B1503893
theorem B1462675 : Blo 1462551 1462675 := bstep (se 1 (by rfl) ⟨1097006, by rfl⟩ : syracuseStep 1462675 = 2194013) B2194013
theorem B1462691 : Blo 1462551 1462691 := bstep (se 1 (by rfl) ⟨1097018, by rfl⟩ : syracuseStep 1462691 = 2194037) B2194037
theorem B1462707 : Blo 1462551 1462707 := bstep (se 1 (by rfl) ⟨1097030, by rfl⟩ : syracuseStep 1462707 = 2194061) B2194061
theorem B1462723 : Blo 1462551 1462723 := bstep (se 1 (by rfl) ⟨1097042, by rfl⟩ : syracuseStep 1462723 = 2194085) B2194085
theorem B1462739 : Blo 1462551 1462739 := bstep (se 1 (by rfl) ⟨1097054, by rfl⟩ : syracuseStep 1462739 = 2194109) B2194109
theorem B1462755 : Blo 1462551 1462755 := bstep (se 1 (by rfl) ⟨1097066, by rfl⟩ : syracuseStep 1462755 = 2194133) B2194133
theorem B2470385 : Blo 1462551 2470385 := bstep (se 2 (by rfl) ⟨926394, by rfl⟩ : syracuseStep 2470385 = 1852789) B1852789
theorem B11121137 : Blo 1462551 11121137 := bstep (se 2 (by rfl) ⟨4170426, by rfl⟩ : syracuseStep 11121137 = 8340853) B8340853
theorem B1462771 : Blo 1462551 1462771 := bstep (se 1 (by rfl) ⟨1097078, by rfl⟩ : syracuseStep 1462771 = 2194157) B2194157
theorem B1462787 : Blo 1462551 1462787 := bstep (se 1 (by rfl) ⟨1097090, by rfl⟩ : syracuseStep 1462787 = 2194181) B2194181
theorem B7909901 : Blo 1462551 7909901 := bstep (se 3 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 7909901 = 2966213) B2966213
theorem B1462803 : Blo 1462551 1462803 := bstep (se 1 (by rfl) ⟨1097102, by rfl⟩ : syracuseStep 1462803 = 2194205) B2194205
theorem B37515797 : Blo 1462551 37515797 := bstep (se 6 (by rfl) ⟨879276, by rfl⟩ : syracuseStep 37515797 = 1758553) B1758553
theorem B1462819 : Blo 1462551 1462819 := bstep (se 1 (by rfl) ⟨1097114, by rfl⟩ : syracuseStep 1462819 = 2194229) B2194229
theorem B1462835 : Blo 1462551 1462835 := bstep (se 1 (by rfl) ⟨1097126, by rfl⟩ : syracuseStep 1462835 = 2194253) B2194253
theorem B1462851 : Blo 1462551 1462851 := bstep (se 1 (by rfl) ⟨1097138, by rfl⟩ : syracuseStep 1462851 = 2194277) B2194277
theorem B4166225 : Blo 1462551 4166225 := bstep (se 2 (by rfl) ⟨1562334, by rfl⟩ : syracuseStep 4166225 = 3124669) B3124669
theorem B1462867 : Blo 1462551 1462867 := bstep (se 1 (by rfl) ⟨1097150, by rfl⟩ : syracuseStep 1462867 = 2194301) B2194301
theorem B1462883 : Blo 1462551 1462883 := bstep (se 1 (by rfl) ⟨1097162, by rfl⟩ : syracuseStep 1462883 = 2194325) B2194325
theorem B4936301 : Blo 1462551 4936301 := bstep (se 3 (by rfl) ⟨925556, by rfl⟩ : syracuseStep 4936301 = 1851113) B1851113
theorem B3125873 : Blo 1462551 3125873 := bstep (se 2 (by rfl) ⟨1172202, by rfl⟩ : syracuseStep 3125873 = 2344405) B2344405
theorem B2470513 : Blo 1462551 2470513 := bstep (se 2 (by rfl) ⟨926442, by rfl⟩ : syracuseStep 2470513 = 1852885) B1852885
theorem B1462899 : Blo 1462551 1462899 := bstep (se 1 (by rfl) ⟨1097174, by rfl⟩ : syracuseStep 1462899 = 2194349) B2194349
theorem B1462915 : Blo 1462551 1462915 := bstep (se 1 (by rfl) ⟨1097186, by rfl⟩ : syracuseStep 1462915 = 2194373) B2194373
theorem B4452995 : Blo 1462551 4452995 := bstep (se 1 (by rfl) ⟨3339746, by rfl⟩ : syracuseStep 4452995 = 6679493) B6679493
theorem B1462931 : Blo 1462551 1462931 := bstep (se 1 (by rfl) ⟨1097198, by rfl⟩ : syracuseStep 1462931 = 2194397) B2194397
theorem B2470547 : Blo 1462551 2470547 := bstep (se 1 (by rfl) ⟨1852910, by rfl⟩ : syracuseStep 2470547 = 3705821) B3705821
theorem B4936355 : Blo 1462551 4936355 := bstep (se 1 (by rfl) ⟨3702266, by rfl⟩ : syracuseStep 4936355 = 7404533) B7404533
theorem B1462947 : Blo 1462551 1462947 := bstep (se 1 (by rfl) ⟨1097210, by rfl⟩ : syracuseStep 1462947 = 2194421) B2194421
theorem B1462963 : Blo 1462551 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B1462979 : Blo 1462551 1462979 := bstep (se 1 (by rfl) ⟨1097234, by rfl⟩ : syracuseStep 1462979 = 2194469) B2194469
theorem B5558989 : Blo 1462551 5558989 := bstep (se 3 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 5558989 = 2084621) B2084621
theorem B1462995 : Blo 1462551 1462995 := bstep (se 1 (by rfl) ⟨1097246, by rfl⟩ : syracuseStep 1462995 = 2194493) B2194493
theorem B1463011 : Blo 1462551 1463011 := bstep (se 1 (by rfl) ⟨1097258, by rfl⟩ : syracuseStep 1463011 = 2194517) B2194517
theorem B13349603 : Blo 1462551 13349603 := bstep (se 1 (by rfl) ⟨10012202, by rfl⟩ : syracuseStep 13349603 = 20024405) B20024405
theorem B1463027 : Blo 1462551 1463027 := bstep (se 1 (by rfl) ⟨1097270, by rfl⟩ : syracuseStep 1463027 = 2194541) B2194541
theorem B1463043 : Blo 1462551 1463043 := bstep (se 1 (by rfl) ⟨1097282, by rfl⟩ : syracuseStep 1463043 = 2194565) B2194565
theorem B4166417 : Blo 1462551 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B1463059 : Blo 1462551 1463059 := bstep (se 1 (by rfl) ⟨1097294, by rfl⟩ : syracuseStep 1463059 = 2194589) B2194589
theorem B2470675 : Blo 1462551 2470675 := bstep (se 1 (by rfl) ⟨1853006, by rfl⟩ : syracuseStep 2470675 = 3706013) B3706013
theorem B4690705 : Blo 1462551 4690705 := bstep (se 2 (by rfl) ⟨1759014, by rfl⟩ : syracuseStep 4690705 = 3518029) B3518029
theorem B1463075 : Blo 1462551 1463075 := bstep (se 1 (by rfl) ⟨1097306, by rfl⟩ : syracuseStep 1463075 = 2194613) B2194613
theorem B5010221 : Blo 1462551 5010221 := bstep (se 3 (by rfl) ⟨939416, by rfl⟩ : syracuseStep 5010221 = 1878833) B1878833
theorem B1463091 : Blo 1462551 1463091 := bstep (se 1 (by rfl) ⟨1097318, by rfl⟩ : syracuseStep 1463091 = 2194637) B2194637
theorem B2503489 : Blo 1462551 2503489 := bstep (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) B1877617
theorem B1463107 : Blo 1462551 1463107 := bstep (se 1 (by rfl) ⟨1097330, by rfl⟩ : syracuseStep 1463107 = 2194661) B2194661
theorem B1463123 : Blo 1462551 1463123 := bstep (se 1 (by rfl) ⟨1097342, by rfl⟩ : syracuseStep 1463123 = 2194685) B2194685
theorem B1463139 : Blo 1462551 1463139 := bstep (se 1 (by rfl) ⟨1097354, by rfl⟩ : syracuseStep 1463139 = 2194709) B2194709
theorem B1463155 : Blo 1462551 1463155 := bstep (se 1 (by rfl) ⟨1097366, by rfl⟩ : syracuseStep 1463155 = 2194733) B2194733
theorem B1463171 : Blo 1462551 1463171 := bstep (se 1 (by rfl) ⟨1097378, by rfl⟩ : syracuseStep 1463171 = 2194757) B2194757
theorem B1463187 : Blo 1462551 1463187 := bstep (se 1 (by rfl) ⟨1097390, by rfl⟩ : syracuseStep 1463187 = 2194781) B2194781
theorem B2470817 : Blo 1462551 2470817 := bstep (se 2 (by rfl) ⟨926556, by rfl⟩ : syracuseStep 2470817 = 1853113) B1853113
theorem B1463203 : Blo 1462551 1463203 := bstep (se 1 (by rfl) ⟨1097402, by rfl⟩ : syracuseStep 1463203 = 2194805) B2194805
theorem B4936625 : Blo 1462551 4936625 := bstep (se 2 (by rfl) ⟨1851234, by rfl⟩ : syracuseStep 4936625 = 3702469) B3702469
theorem B1463219 : Blo 1462551 1463219 := bstep (se 1 (by rfl) ⟨1097414, by rfl⟩ : syracuseStep 1463219 = 2194829) B2194829
theorem B1463235 : Blo 1462551 1463235 := bstep (se 1 (by rfl) ⟨1097426, by rfl⟩ : syracuseStep 1463235 = 2194853) B2194853
theorem B2503619 : Blo 1462551 2503619 := bstep (se 1 (by rfl) ⟨1877714, by rfl⟩ : syracuseStep 2503619 = 3755429) B3755429
theorem B1463251 : Blo 1462551 1463251 := bstep (se 1 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 1463251 = 2194877) B2194877
theorem B1463267 : Blo 1462551 1463267 := bstep (se 1 (by rfl) ⟨1097450, by rfl⟩ : syracuseStep 1463267 = 2194901) B2194901
theorem B1463283 : Blo 1462551 1463283 := bstep (se 1 (by rfl) ⟨1097462, by rfl⟩ : syracuseStep 1463283 = 2194925) B2194925
theorem B1463299 : Blo 1462551 1463299 := bstep (se 1 (by rfl) ⟨1097474, by rfl⟩ : syracuseStep 1463299 = 2194949) B2194949
theorem B1463315 : Blo 1462551 1463315 := bstep (se 1 (by rfl) ⟨1097486, by rfl⟩ : syracuseStep 1463315 = 2194973) B2194973
theorem B2470945 : Blo 1462551 2470945 := bstep (se 2 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 2470945 = 1853209) B1853209
theorem B1463331 : Blo 1462551 1463331 := bstep (se 1 (by rfl) ⟨1097498, by rfl⟩ : syracuseStep 1463331 = 2194997) B2194997
theorem B1463347 : Blo 1462551 1463347 := bstep (se 1 (by rfl) ⟨1097510, by rfl⟩ : syracuseStep 1463347 = 2195021) B2195021
theorem B1463363 : Blo 1462551 1463363 := bstep (se 1 (by rfl) ⟨1097522, by rfl⟩ : syracuseStep 1463363 = 2195045) B2195045
theorem B2470979 : Blo 1462551 2470979 := bstep (se 1 (by rfl) ⟨1853234, by rfl⟩ : syracuseStep 2470979 = 3706469) B3706469
theorem B1463379 : Blo 1462551 1463379 := bstep (se 1 (by rfl) ⟨1097534, by rfl⟩ : syracuseStep 1463379 = 2195069) B2195069
theorem B1463395 : Blo 1462551 1463395 := bstep (se 1 (by rfl) ⟨1097546, by rfl⟩ : syracuseStep 1463395 = 2195093) B2195093
theorem B3126385 : Blo 1462551 3126385 := bstep (se 2 (by rfl) ⟨1172394, by rfl⟩ : syracuseStep 3126385 = 2344789) B2344789
theorem B1463411 : Blo 1462551 1463411 := bstep (se 1 (by rfl) ⟨1097558, by rfl⟩ : syracuseStep 1463411 = 2195117) B2195117
theorem B1463427 : Blo 1462551 1463427 := bstep (se 1 (by rfl) ⟨1097570, by rfl⟩ : syracuseStep 1463427 = 2195141) B2195141
theorem B1463443 : Blo 1462551 1463443 := bstep (se 1 (by rfl) ⟨1097582, by rfl⟩ : syracuseStep 1463443 = 2195165) B2195165
theorem B1463459 : Blo 1462551 1463459 := bstep (se 1 (by rfl) ⟨1097594, by rfl⟩ : syracuseStep 1463459 = 2195189) B2195189
theorem B7410851 : Blo 1462551 7410851 := bstep (se 1 (by rfl) ⟨5558138, by rfl⟩ : syracuseStep 7410851 = 11116277) B11116277
theorem B1463475 : Blo 1462551 1463475 := bstep (se 1 (by rfl) ⟨1097606, by rfl⟩ : syracuseStep 1463475 = 2195213) B2195213
theorem B1463491 : Blo 1462551 1463491 := bstep (se 1 (by rfl) ⟨1097618, by rfl⟩ : syracuseStep 1463491 = 2195237) B2195237
theorem B2471107 : Blo 1462551 2471107 := bstep (se 1 (by rfl) ⟨1853330, by rfl⟩ : syracuseStep 2471107 = 3706661) B3706661
theorem B1463507 : Blo 1462551 1463507 := bstep (se 1 (by rfl) ⟨1097630, by rfl⟩ : syracuseStep 1463507 = 2195261) B2195261
theorem B3953891 : Blo 1462551 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B1463523 : Blo 1462551 1463523 := bstep (se 1 (by rfl) ⟨1097642, by rfl⟩ : syracuseStep 1463523 = 2195285) B2195285
theorem B1561843 : Blo 1462551 1561843 := bstep (se 1 (by rfl) ⟨1171382, by rfl⟩ : syracuseStep 1561843 = 2342765) B2342765
theorem B1463539 : Blo 1462551 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B1463555 : Blo 1462551 1463555 := bstep (se 1 (by rfl) ⟨1097666, by rfl⟩ : syracuseStep 1463555 = 2195333) B2195333
theorem B1463571 : Blo 1462551 1463571 := bstep (se 1 (by rfl) ⟨1097678, by rfl⟩ : syracuseStep 1463571 = 2195357) B2195357
theorem B1463587 : Blo 1462551 1463587 := bstep (se 1 (by rfl) ⟨1097690, by rfl⟩ : syracuseStep 1463587 = 2195381) B2195381
theorem B4224305 : Blo 1462551 4224305 := bstep (se 2 (by rfl) ⟨1584114, by rfl⟩ : syracuseStep 4224305 = 3168229) B3168229
theorem B1463603 : Blo 1462551 1463603 := bstep (se 1 (by rfl) ⟨1097702, by rfl⟩ : syracuseStep 1463603 = 2195405) B2195405
theorem B1758515 : Blo 1462551 1758515 := bstep (se 1 (by rfl) ⟨1318886, by rfl⟩ : syracuseStep 1758515 = 2637773) B2637773
theorem B1463619 : Blo 1462551 1463619 := bstep (se 1 (by rfl) ⟨1097714, by rfl⟩ : syracuseStep 1463619 = 2195429) B2195429
theorem B2471249 : Blo 1462551 2471249 := bstep (se 2 (by rfl) ⟨926718, by rfl⟩ : syracuseStep 2471249 = 1853437) B1853437
theorem B1463635 : Blo 1462551 1463635 := bstep (se 1 (by rfl) ⟨1097726, by rfl⟩ : syracuseStep 1463635 = 2195453) B2195453
theorem B1463651 : Blo 1462551 1463651 := bstep (se 1 (by rfl) ⟨1097738, by rfl⟩ : syracuseStep 1463651 = 2195477) B2195477
theorem B8336753 : Blo 1462551 8336753 := bstep (se 2 (by rfl) ⟨3126282, by rfl⟩ : syracuseStep 8336753 = 6252565) B6252565
theorem B1463667 : Blo 1462551 1463667 := bstep (se 1 (by rfl) ⟨1097750, by rfl⟩ : syracuseStep 1463667 = 2195501) B2195501
theorem B1463683 : Blo 1462551 1463683 := bstep (se 1 (by rfl) ⟨1097762, by rfl⟩ : syracuseStep 1463683 = 2195525) B2195525
theorem B47502733 : Blo 1462551 47502733 := bstep (se 3 (by rfl) ⟨8906762, by rfl⟩ : syracuseStep 47502733 = 17813525) B17813525
theorem B1463699 : Blo 1462551 1463699 := bstep (se 1 (by rfl) ⟨1097774, by rfl⟩ : syracuseStep 1463699 = 2195549) B2195549
theorem B1463715 : Blo 1462551 1463715 := bstep (se 1 (by rfl) ⟨1097786, by rfl⟩ : syracuseStep 1463715 = 2195573) B2195573
theorem B5273009 : Blo 1462551 5273009 := bstep (se 2 (by rfl) ⟨1977378, by rfl⟩ : syracuseStep 5273009 = 3954757) B3954757
theorem B1463731 : Blo 1462551 1463731 := bstep (se 1 (by rfl) ⟨1097798, by rfl⟩ : syracuseStep 1463731 = 2195597) B2195597
theorem B1463747 : Blo 1462551 1463747 := bstep (se 1 (by rfl) ⟨1097810, by rfl⟩ : syracuseStep 1463747 = 2195621) B2195621
theorem B4937165 : Blo 1462551 4937165 := bstep (se 3 (by rfl) ⟨925718, by rfl⟩ : syracuseStep 4937165 = 1851437) B1851437
theorem B2471377 : Blo 1462551 2471377 := bstep (se 2 (by rfl) ⟨926766, by rfl⟩ : syracuseStep 2471377 = 1853533) B1853533
theorem B1463763 : Blo 1462551 1463763 := bstep (se 1 (by rfl) ⟨1097822, by rfl⟩ : syracuseStep 1463763 = 2195645) B2195645
theorem B1463779 : Blo 1462551 1463779 := bstep (se 1 (by rfl) ⟨1097834, by rfl⟩ : syracuseStep 1463779 = 2195669) B2195669
theorem B31659491 : Blo 1462551 31659491 := bstep (se 1 (by rfl) ⟨23744618, by rfl⟩ : syracuseStep 31659491 = 47489237) B47489237
theorem B5559779 : Blo 1462551 5559779 := bstep (se 1 (by rfl) ⟨4169834, by rfl⟩ : syracuseStep 5559779 = 8339669) B8339669
theorem B1562099 : Blo 1462551 1562099 := bstep (se 1 (by rfl) ⟨1171574, by rfl⟩ : syracuseStep 1562099 = 2343149) B2343149
theorem B1463795 : Blo 1462551 1463795 := bstep (se 1 (by rfl) ⟨1097846, by rfl⟩ : syracuseStep 1463795 = 2195693) B2195693
theorem B2471411 : Blo 1462551 2471411 := bstep (se 1 (by rfl) ⟨1853558, by rfl⟩ : syracuseStep 2471411 = 3707117) B3707117
theorem B4937219 : Blo 1462551 4937219 := bstep (se 1 (by rfl) ⟨3702914, by rfl⟩ : syracuseStep 4937219 = 7405829) B7405829
theorem B1463811 : Blo 1462551 1463811 := bstep (se 1 (by rfl) ⟨1097858, by rfl⟩ : syracuseStep 1463811 = 2195717) B2195717
theorem B1463827 : Blo 1462551 1463827 := bstep (se 1 (by rfl) ⟨1097870, by rfl⟩ : syracuseStep 1463827 = 2195741) B2195741
theorem B1463843 : Blo 1462551 1463843 := bstep (se 1 (by rfl) ⟨1097882, by rfl⟩ : syracuseStep 1463843 = 2195765) B2195765
theorem B2225713 : Blo 1462551 2225713 := bstep (se 2 (by rfl) ⟨834642, by rfl⟩ : syracuseStep 2225713 = 1669285) B1669285
theorem B1463859 : Blo 1462551 1463859 := bstep (se 1 (by rfl) ⟨1097894, by rfl⟩ : syracuseStep 1463859 = 2195789) B2195789
theorem B1463875 : Blo 1462551 1463875 := bstep (se 1 (by rfl) ⟨1097906, by rfl⟩ : syracuseStep 1463875 = 2195813) B2195813
theorem B1463891 : Blo 1462551 1463891 := bstep (se 1 (by rfl) ⟨1097918, by rfl⟩ : syracuseStep 1463891 = 2195837) B2195837
theorem B1463907 : Blo 1462551 1463907 := bstep (se 1 (by rfl) ⟨1097930, by rfl⟩ : syracuseStep 1463907 = 2195861) B2195861
theorem B1463923 : Blo 1462551 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B1463939 : Blo 1462551 1463939 := bstep (se 1 (by rfl) ⟨1097954, by rfl⟩ : syracuseStep 1463939 = 2195909) B2195909
theorem B1463955 : Blo 1462551 1463955 := bstep (se 1 (by rfl) ⟨1097966, by rfl⟩ : syracuseStep 1463955 = 2195933) B2195933
theorem B1463971 : Blo 1462551 1463971 := bstep (se 1 (by rfl) ⟨1097978, by rfl⟩ : syracuseStep 1463971 = 2195957) B2195957
theorem B1463987 : Blo 1462551 1463987 := bstep (se 1 (by rfl) ⟨1097990, by rfl⟩ : syracuseStep 1463987 = 2195981) B2195981
theorem B1464003 : Blo 1462551 1464003 := bstep (se 1 (by rfl) ⟨1098002, by rfl⟩ : syracuseStep 1464003 = 2196005) B2196005
theorem B1464019 : Blo 1462551 1464019 := bstep (se 1 (by rfl) ⟨1098014, by rfl⟩ : syracuseStep 1464019 = 2196029) B2196029
theorem B64149205 : Blo 1462551 64149205 := bstep (se 7 (by rfl) ⟨751748, by rfl⟩ : syracuseStep 64149205 = 1503497) B1503497
theorem B1464035 : Blo 1462551 1464035 := bstep (se 1 (by rfl) ⟨1098026, by rfl⟩ : syracuseStep 1464035 = 2196053) B2196053
theorem B4167409 : Blo 1462551 4167409 := bstep (se 2 (by rfl) ⟨1562778, by rfl⟩ : syracuseStep 4167409 = 3125557) B3125557
theorem B1464051 : Blo 1462551 1464051 := bstep (se 1 (by rfl) ⟨1098038, by rfl⟩ : syracuseStep 1464051 = 2196077) B2196077
theorem B1464067 : Blo 1462551 1464067 := bstep (se 1 (by rfl) ⟨1098050, by rfl⟩ : syracuseStep 1464067 = 2196101) B2196101
theorem B4937489 : Blo 1462551 4937489 := bstep (se 2 (by rfl) ⟨1851558, by rfl⟩ : syracuseStep 4937489 = 3703117) B3703117
theorem B1464083 : Blo 1462551 1464083 := bstep (se 1 (by rfl) ⟨1098062, by rfl⟩ : syracuseStep 1464083 = 2196125) B2196125
theorem B1464099 : Blo 1462551 1464099 := bstep (se 1 (by rfl) ⟨1098074, by rfl⟩ : syracuseStep 1464099 = 2196149) B2196149
theorem B1464115 : Blo 1462551 1464115 := bstep (se 1 (by rfl) ⟨1098086, by rfl⟩ : syracuseStep 1464115 = 2196173) B2196173
theorem B1464131 : Blo 1462551 1464131 := bstep (se 1 (by rfl) ⟨1098098, by rfl⟩ : syracuseStep 1464131 = 2196197) B2196197
theorem B1464147 : Blo 1462551 1464147 := bstep (se 1 (by rfl) ⟨1098110, by rfl⟩ : syracuseStep 1464147 = 2196221) B2196221
theorem B1464163 : Blo 1462551 1464163 := bstep (se 1 (by rfl) ⟨1098122, by rfl⟩ : syracuseStep 1464163 = 2196245) B2196245
theorem B3954541 : Blo 1462551 3954541 := bstep (se 3 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 3954541 = 1482953) B1482953
theorem B3290993 : Blo 1462551 3290993 := bstep (se 2 (by rfl) ⟨1234122, by rfl⟩ : syracuseStep 3290993 = 2468245) B2468245
theorem B1464179 : Blo 1462551 1464179 := bstep (se 1 (by rfl) ⟨1098134, by rfl⟩ : syracuseStep 1464179 = 2196269) B2196269
theorem B3291011 : Blo 1462551 3291011 := bstep (se 1 (by rfl) ⟨2468258, by rfl⟩ : syracuseStep 3291011 = 4936517) B4936517
theorem B1464195 : Blo 1462551 1464195 := bstep (se 1 (by rfl) ⟨1098146, by rfl⟩ : syracuseStep 1464195 = 2196293) B2196293
theorem B23746445 : Blo 1462551 23746445 := bstep (se 3 (by rfl) ⟨4452458, by rfl⟩ : syracuseStep 23746445 = 8904917) B8904917
theorem B1464211 : Blo 1462551 1464211 := bstep (se 1 (by rfl) ⟨1098158, by rfl⟩ : syracuseStep 1464211 = 2196317) B2196317
theorem B1464227 : Blo 1462551 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B1669043 : Blo 1462551 1669043 := bstep (se 1 (by rfl) ⟨1251782, by rfl⟩ : syracuseStep 1669043 = 2503565) B2503565
theorem B1464243 : Blo 1462551 1464243 := bstep (se 1 (by rfl) ⟨1098182, by rfl⟩ : syracuseStep 1464243 = 2196365) B2196365
theorem B1464259 : Blo 1462551 1464259 := bstep (se 1 (by rfl) ⟨1098194, by rfl⟩ : syracuseStep 1464259 = 2196389) B2196389
theorem B7411661 : Blo 1462551 7411661 := bstep (se 3 (by rfl) ⟨1389686, by rfl⟩ : syracuseStep 7411661 = 2779373) B2779373
theorem B1464275 : Blo 1462551 1464275 := bstep (se 1 (by rfl) ⟨1098206, by rfl⟩ : syracuseStep 1464275 = 2196413) B2196413
theorem B1464291 : Blo 1462551 1464291 := bstep (se 1 (by rfl) ⟨1098218, by rfl⟩ : syracuseStep 1464291 = 2196437) B2196437
theorem B1464307 : Blo 1462551 1464307 := bstep (se 1 (by rfl) ⟨1098230, by rfl⟩ : syracuseStep 1464307 = 2196461) B2196461
theorem B4167683 : Blo 1462551 4167683 := bstep (se 1 (by rfl) ⟨3125762, by rfl⟩ : syracuseStep 4167683 = 6251525) B6251525
theorem B1464323 : Blo 1462551 1464323 := bstep (se 1 (by rfl) ⟨1098242, by rfl⟩ : syracuseStep 1464323 = 2196485) B2196485
theorem B1464339 : Blo 1462551 1464339 := bstep (se 1 (by rfl) ⟨1098254, by rfl⟩ : syracuseStep 1464339 = 2196509) B2196509
theorem B1464355 : Blo 1462551 1464355 := bstep (se 1 (by rfl) ⟨1098266, by rfl⟩ : syracuseStep 1464355 = 2196533) B2196533
theorem B1464371 : Blo 1462551 1464371 := bstep (se 1 (by rfl) ⟨1098278, by rfl⟩ : syracuseStep 1464371 = 2196557) B2196557
theorem B1464387 : Blo 1462551 1464387 := bstep (se 1 (by rfl) ⟨1098290, by rfl⟩ : syracuseStep 1464387 = 2196581) B2196581
theorem B5347405 : Blo 1462551 5347405 := bstep (se 3 (by rfl) ⟨1002638, by rfl⟩ : syracuseStep 5347405 = 2005277) B2005277
theorem B1464403 : Blo 1462551 1464403 := bstep (se 1 (by rfl) ⟨1098302, by rfl⟩ : syracuseStep 1464403 = 2196605) B2196605
theorem B1464419 : Blo 1462551 1464419 := bstep (se 1 (by rfl) ⟨1098314, by rfl⟩ : syracuseStep 1464419 = 2196629) B2196629
theorem B5560433 : Blo 1462551 5560433 := bstep (se 2 (by rfl) ⟨2085162, by rfl⟩ : syracuseStep 5560433 = 4170325) B4170325
theorem B1464435 : Blo 1462551 1464435 := bstep (se 1 (by rfl) ⟨1098326, by rfl⟩ : syracuseStep 1464435 = 2196653) B2196653
theorem B1464451 : Blo 1462551 1464451 := bstep (se 1 (by rfl) ⟨1098338, by rfl⟩ : syracuseStep 1464451 = 2196677) B2196677
theorem B3291281 : Blo 1462551 3291281 := bstep (se 2 (by rfl) ⟨1234230, by rfl⟩ : syracuseStep 3291281 = 2468461) B2468461
theorem B1464467 : Blo 1462551 1464467 := bstep (se 1 (by rfl) ⟨1098350, by rfl⟩ : syracuseStep 1464467 = 2196701) B2196701
theorem B3291299 : Blo 1462551 3291299 := bstep (se 1 (by rfl) ⟨2468474, by rfl⟩ : syracuseStep 3291299 = 4936949) B4936949
theorem B7911587 : Blo 1462551 7911587 := bstep (se 1 (by rfl) ⟨5933690, by rfl⟩ : syracuseStep 7911587 = 11867381) B11867381
theorem B1464483 : Blo 1462551 1464483 := bstep (se 1 (by rfl) ⟨1098362, by rfl⟩ : syracuseStep 1464483 = 2196725) B2196725
theorem B1464499 : Blo 1462551 1464499 := bstep (se 1 (by rfl) ⟨1098374, by rfl⟩ : syracuseStep 1464499 = 2196749) B2196749
theorem B4167875 : Blo 1462551 4167875 := bstep (se 1 (by rfl) ⟨3125906, by rfl⟩ : syracuseStep 4167875 = 6251813) B6251813
theorem B1464515 : Blo 1462551 1464515 := bstep (se 1 (by rfl) ⟨1098386, by rfl⟩ : syracuseStep 1464515 = 2196773) B2196773
theorem B14063813 : Blo 1462551 14063813 := bstep (se 4 (by rfl) ⟨1318482, by rfl⟩ : syracuseStep 14063813 = 2636965) B2636965
theorem B1464531 : Blo 1462551 1464531 := bstep (se 1 (by rfl) ⟨1098398, by rfl⟩ : syracuseStep 1464531 = 2196797) B2196797
theorem B1562851 : Blo 1462551 1562851 := bstep (se 1 (by rfl) ⟨1172138, by rfl⟩ : syracuseStep 1562851 = 2344277) B2344277
theorem B1464547 : Blo 1462551 1464547 := bstep (se 1 (by rfl) ⟨1098410, by rfl⟩ : syracuseStep 1464547 = 2196821) B2196821
theorem B2504947 : Blo 1462551 2504947 := bstep (se 1 (by rfl) ⟨1878710, by rfl⟩ : syracuseStep 2504947 = 3757421) B3757421
theorem B4938029 : Blo 1462551 4938029 := bstep (se 3 (by rfl) ⟨925880, by rfl⟩ : syracuseStep 4938029 = 1851761) B1851761
theorem B4938083 : Blo 1462551 4938083 := bstep (se 1 (by rfl) ⟨3703562, by rfl⟩ : syracuseStep 4938083 = 7407125) B7407125
theorem B2193827 : Blo 1462551 2193827 := bstep (se 1 (by rfl) ⟨1645370, by rfl⟩ : syracuseStep 2193827 = 3290741) B3290741
theorem B3291569 : Blo 1462551 3291569 := bstep (se 2 (by rfl) ⟨1234338, by rfl⟩ : syracuseStep 3291569 = 2468677) B2468677
theorem B2193857 : Blo 1462551 2193857 := bstep (se 2 (by rfl) ⟨822696, by rfl⟩ : syracuseStep 2193857 = 1645393) B1645393
theorem B3291587 : Blo 1462551 3291587 := bstep (se 1 (by rfl) ⟨2468690, by rfl⟩ : syracuseStep 3291587 = 4937381) B4937381
theorem B2193875 : Blo 1462551 2193875 := bstep (se 1 (by rfl) ⟨1645406, by rfl⟩ : syracuseStep 2193875 = 3290813) B3290813
theorem B2193905 : Blo 1462551 2193905 := bstep (se 2 (by rfl) ⟨822714, by rfl⟩ : syracuseStep 2193905 = 1645429) B1645429
theorem B2636273 : Blo 1462551 2636273 := bstep (se 2 (by rfl) ⟨988602, by rfl⟩ : syracuseStep 2636273 = 1977205) B1977205
theorem B2193923 : Blo 1462551 2193923 := bstep (se 1 (by rfl) ⟨1645442, by rfl⟩ : syracuseStep 2193923 = 3290885) B3290885
theorem B2193953 : Blo 1462551 2193953 := bstep (se 2 (by rfl) ⟨822732, by rfl⟩ : syracuseStep 2193953 = 1645465) B1645465
theorem B2193971 : Blo 1462551 2193971 := bstep (se 1 (by rfl) ⟨1645478, by rfl⟩ : syracuseStep 2193971 = 3290957) B3290957
theorem B2194001 : Blo 1462551 2194001 := bstep (se 2 (by rfl) ⟨822750, by rfl⟩ : syracuseStep 2194001 = 1645501) B1645501
theorem B3127889 : Blo 1462551 3127889 := bstep (se 2 (by rfl) ⟨1172958, by rfl⟩ : syracuseStep 3127889 = 2345917) B2345917
theorem B2194019 : Blo 1462551 2194019 := bstep (se 1 (by rfl) ⟨1645514, by rfl⟩ : syracuseStep 2194019 = 3291029) B3291029
theorem B6011491 : Blo 1462551 6011491 := bstep (se 1 (by rfl) ⟨4508618, by rfl⟩ : syracuseStep 6011491 = 9017237) B9017237
theorem B4938353 : Blo 1462551 4938353 := bstep (se 2 (by rfl) ⟨1851882, by rfl⟩ : syracuseStep 4938353 = 3703765) B3703765
theorem B2194049 : Blo 1462551 2194049 := bstep (se 2 (by rfl) ⟨822768, by rfl⟩ : syracuseStep 2194049 = 1645537) B1645537
theorem B2194067 : Blo 1462551 2194067 := bstep (se 1 (by rfl) ⟨1645550, by rfl⟩ : syracuseStep 2194067 = 3291101) B3291101
theorem B2005651 : Blo 1462551 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B7404209 : Blo 1462551 7404209 := bstep (se 2 (by rfl) ⟨2776578, by rfl⟩ : syracuseStep 7404209 = 5553157) B5553157
theorem B2194097 : Blo 1462551 2194097 := bstep (se 2 (by rfl) ⟨822786, by rfl⟩ : syracuseStep 2194097 = 1645573) B1645573
theorem B2194115 : Blo 1462551 2194115 := bstep (se 1 (by rfl) ⟨1645586, by rfl⟩ : syracuseStep 2194115 = 3291173) B3291173
theorem B6675149 : Blo 1462551 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B3291857 : Blo 1462551 3291857 := bstep (se 2 (by rfl) ⟨1234446, by rfl⟩ : syracuseStep 3291857 = 2468893) B2468893
theorem B2636497 : Blo 1462551 2636497 := bstep (se 2 (by rfl) ⟨988686, by rfl⟩ : syracuseStep 2636497 = 1977373) B1977373
theorem B2194145 : Blo 1462551 2194145 := bstep (se 2 (by rfl) ⟨822804, by rfl⟩ : syracuseStep 2194145 = 1645609) B1645609
theorem B11107043 : Blo 1462551 11107043 := bstep (se 1 (by rfl) ⟨8330282, by rfl⟩ : syracuseStep 11107043 = 16660565) B16660565
theorem B3291875 : Blo 1462551 3291875 := bstep (se 1 (by rfl) ⟨2468906, by rfl⟩ : syracuseStep 3291875 = 4937813) B4937813
theorem B2194163 : Blo 1462551 2194163 := bstep (se 1 (by rfl) ⟨1645622, by rfl⟩ : syracuseStep 2194163 = 3291245) B3291245
theorem B2194193 : Blo 1462551 2194193 := bstep (se 2 (by rfl) ⟨822822, by rfl⟩ : syracuseStep 2194193 = 1645645) B1645645
theorem B2194211 : Blo 1462551 2194211 := bstep (se 1 (by rfl) ⟨1645658, by rfl⟩ : syracuseStep 2194211 = 3291317) B3291317
theorem B6249251 : Blo 1462551 6249251 := bstep (se 1 (by rfl) ⟨4686938, by rfl⟩ : syracuseStep 6249251 = 9373877) B9373877
theorem B8338211 : Blo 1462551 8338211 := bstep (se 1 (by rfl) ⟨6253658, by rfl⟩ : syracuseStep 8338211 = 12507317) B12507317
theorem B2194241 : Blo 1462551 2194241 := bstep (se 2 (by rfl) ⟨822840, by rfl⟩ : syracuseStep 2194241 = 1645681) B1645681
theorem B1669955 : Blo 1462551 1669955 := bstep (se 1 (by rfl) ⟨1252466, by rfl⟩ : syracuseStep 1669955 = 2504933) B2504933
theorem B2194259 : Blo 1462551 2194259 := bstep (se 1 (by rfl) ⟨1645694, by rfl⟩ : syracuseStep 2194259 = 3291389) B3291389
theorem B1645411 : Blo 1462551 1645411 := bstep (se 1 (by rfl) ⟨1234058, by rfl⟩ : syracuseStep 1645411 = 2468117) B2468117
theorem B2194289 : Blo 1462551 2194289 := bstep (se 2 (by rfl) ⟨822858, by rfl⟩ : syracuseStep 2194289 = 1645717) B1645717
theorem B2194307 : Blo 1462551 2194307 := bstep (se 1 (by rfl) ⟨1645730, by rfl⟩ : syracuseStep 2194307 = 3291461) B3291461
theorem B5004173 : Blo 1462551 5004173 := bstep (se 3 (by rfl) ⟨938282, by rfl⟩ : syracuseStep 5004173 = 1876565) B1876565
theorem B2194337 : Blo 1462551 2194337 := bstep (se 2 (by rfl) ⟨822876, by rfl⟩ : syracuseStep 2194337 = 1645753) B1645753
theorem B8330147 : Blo 1462551 8330147 := bstep (se 1 (by rfl) ⟨6247610, by rfl⟩ : syracuseStep 8330147 = 12495221) B12495221
theorem B2194355 : Blo 1462551 2194355 := bstep (se 1 (by rfl) ⟨1645766, by rfl⟩ : syracuseStep 2194355 = 3291533) B3291533
theorem B2194385 : Blo 1462551 2194385 := bstep (se 2 (by rfl) ⟨822894, by rfl⟩ : syracuseStep 2194385 = 1645789) B1645789
theorem B2194403 : Blo 1462551 2194403 := bstep (se 1 (by rfl) ⟨1645802, by rfl⟩ : syracuseStep 2194403 = 3291605) B3291605
theorem B4168685 : Blo 1462551 4168685 := bstep (se 3 (by rfl) ⟨781628, by rfl⟩ : syracuseStep 4168685 = 1563257) B1563257
theorem B3292145 : Blo 1462551 3292145 := bstep (se 2 (by rfl) ⟨1234554, by rfl⟩ : syracuseStep 3292145 = 2469109) B2469109
theorem B1645555 : Blo 1462551 1645555 := bstep (se 1 (by rfl) ⟨1234166, by rfl⟩ : syracuseStep 1645555 = 2468333) B2468333
theorem B2194433 : Blo 1462551 2194433 := bstep (se 2 (by rfl) ⟨822912, by rfl⟩ : syracuseStep 2194433 = 1645825) B1645825
theorem B3292163 : Blo 1462551 3292163 := bstep (se 1 (by rfl) ⟨2469122, by rfl⟩ : syracuseStep 3292163 = 4938245) B4938245
theorem B2194451 : Blo 1462551 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B2194481 : Blo 1462551 2194481 := bstep (se 2 (by rfl) ⟨822930, by rfl⟩ : syracuseStep 2194481 = 1645861) B1645861
theorem B2194499 : Blo 1462551 2194499 := bstep (se 1 (by rfl) ⟨1645874, by rfl⟩ : syracuseStep 2194499 = 3291749) B3291749
theorem B2194529 : Blo 1462551 2194529 := bstep (se 2 (by rfl) ⟨822948, by rfl⟩ : syracuseStep 2194529 = 1645897) B1645897
theorem B5274737 : Blo 1462551 5274737 := bstep (se 2 (by rfl) ⟨1978026, by rfl⟩ : syracuseStep 5274737 = 3956053) B3956053
theorem B2194547 : Blo 1462551 2194547 := bstep (se 1 (by rfl) ⟨1645910, by rfl⟩ : syracuseStep 2194547 = 3291821) B3291821
theorem B1645699 : Blo 1462551 1645699 := bstep (se 1 (by rfl) ⟨1234274, by rfl⟩ : syracuseStep 1645699 = 2468549) B2468549
theorem B4938893 : Blo 1462551 4938893 := bstep (se 3 (by rfl) ⟨926042, by rfl⟩ : syracuseStep 4938893 = 1852085) B1852085
theorem B2194577 : Blo 1462551 2194577 := bstep (se 2 (by rfl) ⟨822966, by rfl⟩ : syracuseStep 2194577 = 1645933) B1645933
theorem B2194595 : Blo 1462551 2194595 := bstep (se 1 (by rfl) ⟨1645946, by rfl⟩ : syracuseStep 2194595 = 3291893) B3291893
theorem B4168867 : Blo 1462551 4168867 := bstep (se 1 (by rfl) ⟨3126650, by rfl⟩ : syracuseStep 4168867 = 6253301) B6253301
theorem B2194625 : Blo 1462551 2194625 := bstep (se 2 (by rfl) ⟨822984, by rfl⟩ : syracuseStep 2194625 = 1645969) B1645969
theorem B2636995 : Blo 1462551 2636995 := bstep (se 1 (by rfl) ⟨1977746, by rfl⟩ : syracuseStep 2636995 = 3955493) B3955493
theorem B4938947 : Blo 1462551 4938947 := bstep (se 1 (by rfl) ⟨3704210, by rfl⟩ : syracuseStep 4938947 = 7408421) B7408421
theorem B2194643 : Blo 1462551 2194643 := bstep (se 1 (by rfl) ⟨1645982, by rfl⟩ : syracuseStep 2194643 = 3291965) B3291965
theorem B2194673 : Blo 1462551 2194673 := bstep (se 2 (by rfl) ⟨823002, by rfl⟩ : syracuseStep 2194673 = 1646005) B1646005
theorem B2194691 : Blo 1462551 2194691 := bstep (se 1 (by rfl) ⟨1646018, by rfl⟩ : syracuseStep 2194691 = 3292037) B3292037
theorem B3292433 : Blo 1462551 3292433 := bstep (se 2 (by rfl) ⟨1234662, by rfl⟩ : syracuseStep 3292433 = 2469325) B2469325
theorem B1645843 : Blo 1462551 1645843 := bstep (se 1 (by rfl) ⟨1234382, by rfl⟩ : syracuseStep 1645843 = 2468765) B2468765
theorem B2194721 : Blo 1462551 2194721 := bstep (se 2 (by rfl) ⟨823020, by rfl⟩ : syracuseStep 2194721 = 1646041) B1646041
theorem B3292451 : Blo 1462551 3292451 := bstep (se 1 (by rfl) ⟨2469338, by rfl⟩ : syracuseStep 3292451 = 4938677) B4938677
theorem B2194739 : Blo 1462551 2194739 := bstep (se 1 (by rfl) ⟨1646054, by rfl⟩ : syracuseStep 2194739 = 3292109) B3292109
theorem B2194769 : Blo 1462551 2194769 := bstep (se 2 (by rfl) ⟨823038, by rfl⟩ : syracuseStep 2194769 = 1646077) B1646077
theorem B2194787 : Blo 1462551 2194787 := bstep (se 1 (by rfl) ⟨1646090, by rfl⟩ : syracuseStep 2194787 = 3292181) B3292181
theorem B2194817 : Blo 1462551 2194817 := bstep (se 2 (by rfl) ⟨823056, by rfl⟩ : syracuseStep 2194817 = 1646113) B1646113
theorem B2194835 : Blo 1462551 2194835 := bstep (se 1 (by rfl) ⟨1646126, by rfl⟩ : syracuseStep 2194835 = 3292253) B3292253
theorem B1645987 : Blo 1462551 1645987 := bstep (se 1 (by rfl) ⟨1234490, by rfl⟩ : syracuseStep 1645987 = 2468981) B2468981
theorem B2194865 : Blo 1462551 2194865 := bstep (se 2 (by rfl) ⟨823074, by rfl⟩ : syracuseStep 2194865 = 1646149) B1646149
theorem B2194883 : Blo 1462551 2194883 := bstep (se 1 (by rfl) ⟨1646162, by rfl⟩ : syracuseStep 2194883 = 3292325) B3292325
theorem B4939217 : Blo 1462551 4939217 := bstep (se 2 (by rfl) ⟨1852206, by rfl⟩ : syracuseStep 4939217 = 3704413) B3704413
theorem B2194913 : Blo 1462551 2194913 := bstep (se 2 (by rfl) ⟨823092, by rfl⟩ : syracuseStep 2194913 = 1646185) B1646185
theorem B3702257 : Blo 1462551 3702257 := bstep (se 2 (by rfl) ⟨1388346, by rfl⟩ : syracuseStep 3702257 = 2776693) B2776693
theorem B2194931 : Blo 1462551 2194931 := bstep (se 1 (by rfl) ⟨1646198, by rfl⟩ : syracuseStep 2194931 = 3292397) B3292397
theorem B2194961 : Blo 1462551 2194961 := bstep (se 2 (by rfl) ⟨823110, by rfl⟩ : syracuseStep 2194961 = 1646221) B1646221
theorem B3702307 : Blo 1462551 3702307 := bstep (se 1 (by rfl) ⟨2776730, by rfl⟩ : syracuseStep 3702307 = 5553461) B5553461
theorem B10010147 : Blo 1462551 10010147 := bstep (se 1 (by rfl) ⟨7507610, by rfl⟩ : syracuseStep 10010147 = 15015221) B15015221
theorem B2194979 : Blo 1462551 2194979 := bstep (se 1 (by rfl) ⟨1646234, by rfl⟩ : syracuseStep 2194979 = 3292469) B3292469
theorem B3292721 : Blo 1462551 3292721 := bstep (se 2 (by rfl) ⟨1234770, by rfl⟩ : syracuseStep 3292721 = 2469541) B2469541
theorem B1646131 : Blo 1462551 1646131 := bstep (se 1 (by rfl) ⟨1234598, by rfl⟩ : syracuseStep 1646131 = 2469197) B2469197
theorem B32063029 : Blo 1462551 32063029 := bstep (se 5 (by rfl) ⟨1502954, by rfl⟩ : syracuseStep 32063029 = 3005909) B3005909
theorem B2195009 : Blo 1462551 2195009 := bstep (se 2 (by rfl) ⟨823128, by rfl⟩ : syracuseStep 2195009 = 1646257) B1646257
theorem B3292739 : Blo 1462551 3292739 := bstep (se 1 (by rfl) ⟨2469554, by rfl⟩ : syracuseStep 3292739 = 4939109) B4939109
theorem B9371213 : Blo 1462551 9371213 := bstep (se 3 (by rfl) ⟨1757102, by rfl⟩ : syracuseStep 9371213 = 3514205) B3514205
theorem B2195027 : Blo 1462551 2195027 := bstep (se 1 (by rfl) ⟨1646270, by rfl⟩ : syracuseStep 2195027 = 3292541) B3292541
theorem B2195057 : Blo 1462551 2195057 := bstep (se 2 (by rfl) ⟨823146, by rfl⟩ : syracuseStep 2195057 = 1646293) B1646293
theorem B2195075 : Blo 1462551 2195075 := bstep (se 1 (by rfl) ⟨1646306, by rfl⟩ : syracuseStep 2195075 = 3292613) B3292613
theorem B4169357 : Blo 1462551 4169357 := bstep (se 3 (by rfl) ⟨781754, by rfl⟩ : syracuseStep 4169357 = 1563509) B1563509
theorem B2195105 : Blo 1462551 2195105 := bstep (se 2 (by rfl) ⟨823164, by rfl⟩ : syracuseStep 2195105 = 1646329) B1646329
theorem B3702449 : Blo 1462551 3702449 := bstep (se 2 (by rfl) ⟨1388418, by rfl⟩ : syracuseStep 3702449 = 2776837) B2776837
theorem B2195123 : Blo 1462551 2195123 := bstep (se 1 (by rfl) ⟨1646342, by rfl⟩ : syracuseStep 2195123 = 3292685) B3292685
theorem B1646275 : Blo 1462551 1646275 := bstep (se 1 (by rfl) ⟨1234706, by rfl⟩ : syracuseStep 1646275 = 2469413) B2469413
theorem B2195153 : Blo 1462551 2195153 := bstep (se 2 (by rfl) ⟨823182, by rfl⟩ : syracuseStep 2195153 = 1646365) B1646365
theorem B2195171 : Blo 1462551 2195171 := bstep (se 1 (by rfl) ⟨1646378, by rfl⟩ : syracuseStep 2195171 = 3292757) B3292757
theorem B2195201 : Blo 1462551 2195201 := bstep (se 2 (by rfl) ⟨823200, by rfl⟩ : syracuseStep 2195201 = 1646401) B1646401
theorem B8339213 : Blo 1462551 8339213 := bstep (se 3 (by rfl) ⟨1563602, by rfl⟩ : syracuseStep 8339213 = 3127205) B3127205
theorem B2195219 : Blo 1462551 2195219 := bstep (se 1 (by rfl) ⟨1646414, by rfl⟩ : syracuseStep 2195219 = 3292829) B3292829
theorem B8560433 : Blo 1462551 8560433 := bstep (se 2 (by rfl) ⟨3210162, by rfl⟩ : syracuseStep 8560433 = 6420325) B6420325
theorem B2195249 : Blo 1462551 2195249 := bstep (se 2 (by rfl) ⟨823218, by rfl⟩ : syracuseStep 2195249 = 1646437) B1646437
theorem B1482547 : Blo 1462551 1482547 := bstep (se 1 (by rfl) ⟨1111910, by rfl⟩ : syracuseStep 1482547 = 2223821) B2223821
theorem B2195267 : Blo 1462551 2195267 := bstep (se 1 (by rfl) ⟨1646450, by rfl⟩ : syracuseStep 2195267 = 3292901) B3292901
theorem B2776913 : Blo 1462551 2776913 := bstep (se 2 (by rfl) ⟨1041342, by rfl⟩ : syracuseStep 2776913 = 2082685) B2082685
theorem B3293009 : Blo 1462551 3293009 := bstep (se 2 (by rfl) ⟨1234878, by rfl⟩ : syracuseStep 3293009 = 2469757) B2469757
theorem B1646419 : Blo 1462551 1646419 := bstep (se 1 (by rfl) ⟨1234814, by rfl⟩ : syracuseStep 1646419 = 2469629) B2469629
theorem B2195297 : Blo 1462551 2195297 := bstep (se 2 (by rfl) ⟨823236, by rfl⟩ : syracuseStep 2195297 = 1646473) B1646473
theorem B3293027 : Blo 1462551 3293027 := bstep (se 1 (by rfl) ⟨2469770, by rfl⟩ : syracuseStep 3293027 = 4939541) B4939541
theorem B2195315 : Blo 1462551 2195315 := bstep (se 1 (by rfl) ⟨1646486, by rfl⟩ : syracuseStep 2195315 = 3292973) B3292973
theorem B2195345 : Blo 1462551 2195345 := bstep (se 2 (by rfl) ⟨823254, by rfl⟩ : syracuseStep 2195345 = 1646509) B1646509
theorem B2195363 : Blo 1462551 2195363 := bstep (se 1 (by rfl) ⟨1646522, by rfl⟩ : syracuseStep 2195363 = 3293045) B3293045
theorem B2195393 : Blo 1462551 2195393 := bstep (se 2 (by rfl) ⟨823272, by rfl⟩ : syracuseStep 2195393 = 1646545) B1646545
theorem B1851331 : Blo 1462551 1851331 := bstep (se 1 (by rfl) ⟨1388498, by rfl⟩ : syracuseStep 1851331 = 2776997) B2776997
theorem B2195411 : Blo 1462551 2195411 := bstep (se 1 (by rfl) ⟨1646558, by rfl⟩ : syracuseStep 2195411 = 3293117) B3293117
theorem B1646563 : Blo 1462551 1646563 := bstep (se 1 (by rfl) ⟨1234922, by rfl⟩ : syracuseStep 1646563 = 2469845) B2469845
theorem B4939757 : Blo 1462551 4939757 := bstep (se 3 (by rfl) ⟨926204, by rfl⟩ : syracuseStep 4939757 = 1852409) B1852409
theorem B2195441 : Blo 1462551 2195441 := bstep (se 2 (by rfl) ⟨823290, by rfl⟩ : syracuseStep 2195441 = 1646581) B1646581
theorem B3293207 : Blo 1462551 3293207 := bstep (se 1 (by rfl) ⟨2469905, by rfl⟩ : syracuseStep 3293207 = 4939811) B4939811
theorem B1646635 : Blo 1462551 1646635 := bstep (se 1 (by rfl) ⟨1234976, by rfl⟩ : syracuseStep 1646635 = 2469953) B2469953
theorem B5931083 : Blo 1462551 5931083 := bstep (se 1 (by rfl) ⟨4448312, by rfl⟩ : syracuseStep 5931083 = 8896625) B8896625
theorem B2195531 : Blo 1462551 2195531 := bstep (se 1 (by rfl) ⟨1646648, by rfl⟩ : syracuseStep 2195531 = 3293297) B3293297
theorem B2195543 : Blo 1462551 2195543 := bstep (se 1 (by rfl) ⟨1646657, by rfl⟩ : syracuseStep 2195543 = 3293315) B3293315
theorem B4939865 : Blo 1462551 4939865 := bstep (se 2 (by rfl) ⟨1852449, by rfl⟩ : syracuseStep 4939865 = 3704899) B3704899
theorem B3702935 : Blo 1462551 3702935 := bstep (se 1 (by rfl) ⟨2777201, by rfl⟩ : syracuseStep 3702935 = 5554403) B5554403
theorem B38011031 : Blo 1462551 38011031 := bstep (se 1 (by rfl) ⟨28508273, by rfl⟩ : syracuseStep 38011031 = 57016547) B57016547
theorem B2195609 : Blo 1462551 2195609 := bstep (se 2 (by rfl) ⟨823353, by rfl⟩ : syracuseStep 2195609 = 1646707) B1646707
theorem B1646743 : Blo 1462551 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B3293387 : Blo 1462551 3293387 := bstep (se 1 (by rfl) ⟨2470040, by rfl⟩ : syracuseStep 3293387 = 4940081) B4940081
theorem B3293441 : Blo 1462551 3293441 := bstep (se 2 (by rfl) ⟨1235040, by rfl⟩ : syracuseStep 3293441 = 2470081) B2470081
theorem B2195723 : Blo 1462551 2195723 := bstep (se 1 (by rfl) ⟨1646792, by rfl⟩ : syracuseStep 2195723 = 3293585) B3293585
theorem B2195735 : Blo 1462551 2195735 := bstep (se 1 (by rfl) ⟨1646801, by rfl⟩ : syracuseStep 2195735 = 3293603) B3293603
theorem B2965825 : Blo 1462551 2965825 := bstep (se 2 (by rfl) ⟨1112184, by rfl⟩ : syracuseStep 2965825 = 2224369) B2224369
theorem B1646923 : Blo 1462551 1646923 := bstep (se 1 (by rfl) ⟨1235192, by rfl⟩ : syracuseStep 1646923 = 2470385) B2470385
theorem B7414091 : Blo 1462551 7414091 := bstep (se 1 (by rfl) ⟨5560568, by rfl⟩ : syracuseStep 7414091 = 11121137) B11121137
theorem B6250841 : Blo 1462551 6250841 := bstep (se 2 (by rfl) ⟨2344065, by rfl⟩ : syracuseStep 6250841 = 4688131) B4688131
theorem B2195801 : Blo 1462551 2195801 := bstep (se 2 (by rfl) ⟨823425, by rfl⟩ : syracuseStep 2195801 = 1646851) B1646851
theorem B25010531 : Blo 1462551 25010531 := bstep (se 1 (by rfl) ⟨18757898, by rfl⟩ : syracuseStep 25010531 = 37515797) B37515797
theorem B26706277 : Blo 1462551 26706277 := bstep (se 4 (by rfl) ⟨2503713, by rfl⟩ : syracuseStep 26706277 = 5007427) B5007427
theorem B2777483 : Blo 1462551 2777483 := bstep (se 1 (by rfl) ⟨2083112, by rfl⟩ : syracuseStep 2777483 = 4166225) B4166225
theorem B6250925 : Blo 1462551 6250925 := bstep (se 3 (by rfl) ⟨1172048, by rfl⟩ : syracuseStep 6250925 = 2344097) B2344097
theorem B1647031 : Blo 1462551 1647031 := bstep (se 1 (by rfl) ⟨1235273, by rfl⟩ : syracuseStep 1647031 = 2470547) B2470547
theorem B2195915 : Blo 1462551 2195915 := bstep (se 1 (by rfl) ⟨1646936, by rfl⟩ : syracuseStep 2195915 = 3293873) B3293873
theorem B2195927 : Blo 1462551 2195927 := bstep (se 1 (by rfl) ⟨1646945, by rfl⟩ : syracuseStep 2195927 = 3293891) B3293891
theorem B3293657 : Blo 1462551 3293657 := bstep (se 2 (by rfl) ⟨1235121, by rfl⟩ : syracuseStep 3293657 = 2470243) B2470243
theorem B5931485 : Blo 1462551 5931485 := bstep (se 3 (by rfl) ⟨1112153, by rfl⟩ : syracuseStep 5931485 = 2224307) B2224307
theorem B2195993 : Blo 1462551 2195993 := bstep (se 2 (by rfl) ⟨823497, by rfl⟩ : syracuseStep 2195993 = 1646995) B1646995
theorem B3293747 : Blo 1462551 3293747 := bstep (se 1 (by rfl) ⟨2470310, by rfl⟩ : syracuseStep 3293747 = 4940621) B4940621
theorem B2777665 : Blo 1462551 2777665 := bstep (se 2 (by rfl) ⟨1041624, by rfl⟩ : syracuseStep 2777665 = 2083249) B2083249
theorem B1851979 : Blo 1462551 1851979 := bstep (se 1 (by rfl) ⟨1388984, by rfl⟩ : syracuseStep 1851979 = 2777969) B2777969
theorem B3293783 : Blo 1462551 3293783 := bstep (se 1 (by rfl) ⟨2470337, by rfl⟩ : syracuseStep 3293783 = 4940675) B4940675
theorem B10543709 : Blo 1462551 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B1647211 : Blo 1462551 1647211 := bstep (se 1 (by rfl) ⟨1235408, by rfl⟩ : syracuseStep 1647211 = 2470817) B2470817
theorem B2196107 : Blo 1462551 2196107 := bstep (se 1 (by rfl) ⟨1647080, by rfl⟩ : syracuseStep 2196107 = 3294161) B3294161
theorem B2196119 : Blo 1462551 2196119 := bstep (se 1 (by rfl) ⟨1647089, by rfl⟩ : syracuseStep 2196119 = 3294179) B3294179
theorem B1647319 : Blo 1462551 1647319 := bstep (se 1 (by rfl) ⟨1235489, by rfl⟩ : syracuseStep 1647319 = 2470979) B2470979
theorem B2196185 : Blo 1462551 2196185 := bstep (se 2 (by rfl) ⟨823569, by rfl⟩ : syracuseStep 2196185 = 1647139) B1647139
theorem B3293963 : Blo 1462551 3293963 := bstep (se 1 (by rfl) ⟨2470472, by rfl⟩ : syracuseStep 3293963 = 4940945) B4940945
theorem B4940567 : Blo 1462551 4940567 := bstep (se 1 (by rfl) ⟨3705425, by rfl⟩ : syracuseStep 4940567 = 7410851) B7410851
theorem B3703603 : Blo 1462551 3703603 := bstep (se 1 (by rfl) ⟨2777702, by rfl⟩ : syracuseStep 3703603 = 5555405) B5555405
theorem B10543937 : Blo 1462551 10543937 := bstep (se 2 (by rfl) ⟨3953976, by rfl⟩ : syracuseStep 10543937 = 7907953) B7907953
theorem B3294017 : Blo 1462551 3294017 := bstep (se 2 (by rfl) ⟨1235256, by rfl⟩ : syracuseStep 3294017 = 2470513) B2470513
theorem B2196299 : Blo 1462551 2196299 := bstep (se 1 (by rfl) ⟨1647224, by rfl⟩ : syracuseStep 2196299 = 3294449) B3294449
theorem B1852247 : Blo 1462551 1852247 := bstep (se 1 (by rfl) ⟨1389185, by rfl⟩ : syracuseStep 1852247 = 2778371) B2778371
theorem B2196311 : Blo 1462551 2196311 := bstep (se 1 (by rfl) ⟨1647233, by rfl⟩ : syracuseStep 2196311 = 3294467) B3294467
theorem B1647499 : Blo 1462551 1647499 := bstep (se 1 (by rfl) ⟨1235624, by rfl⟩ : syracuseStep 1647499 = 2471249) B2471249
theorem B2196377 : Blo 1462551 2196377 := bstep (se 2 (by rfl) ⟨823641, by rfl⟩ : syracuseStep 2196377 = 1647283) B1647283
theorem B10552241 : Blo 1462551 10552241 := bstep (se 2 (by rfl) ⟨3957090, by rfl⟩ : syracuseStep 10552241 = 7914181) B7914181
theorem B3515329 : Blo 1462551 3515329 := bstep (se 2 (by rfl) ⟨1318248, by rfl⟩ : syracuseStep 3515329 = 2636497) B2636497
theorem B3703745 : Blo 1462551 3703745 := bstep (se 2 (by rfl) ⟨1388904, by rfl⟩ : syracuseStep 3703745 = 2777809) B2777809
theorem B3515339 : Blo 1462551 3515339 := bstep (se 1 (by rfl) ⟨2636504, by rfl⟩ : syracuseStep 3515339 = 5273009) B5273009
theorem B1647607 : Blo 1462551 1647607 := bstep (se 1 (by rfl) ⟨1235705, by rfl⟩ : syracuseStep 1647607 = 2471411) B2471411
theorem B2778113 : Blo 1462551 2778113 := bstep (se 2 (by rfl) ⟨1041792, by rfl⟩ : syracuseStep 2778113 = 2083585) B2083585
theorem B2196491 : Blo 1462551 2196491 := bstep (se 1 (by rfl) ⟨1647368, by rfl⟩ : syracuseStep 2196491 = 3294737) B3294737
theorem B2196503 : Blo 1462551 2196503 := bstep (se 1 (by rfl) ⟨1647377, by rfl⟩ : syracuseStep 2196503 = 3294755) B3294755
theorem B3294233 : Blo 1462551 3294233 := bstep (se 2 (by rfl) ⟨1235337, by rfl⟩ : syracuseStep 3294233 = 2470675) B2470675
theorem B67617827 : Blo 1462551 67617827 := bstep (se 1 (by rfl) ⟨50713370, by rfl⟩ : syracuseStep 67617827 = 101426741) B101426741
theorem B2196569 : Blo 1462551 2196569 := bstep (se 2 (by rfl) ⟨823713, by rfl⟩ : syracuseStep 2196569 = 1647427) B1647427
theorem B3294323 : Blo 1462551 3294323 := bstep (se 1 (by rfl) ⟨2470742, by rfl⟩ : syracuseStep 3294323 = 4941485) B4941485
theorem B3294359 : Blo 1462551 3294359 := bstep (se 1 (by rfl) ⟨2470769, by rfl⟩ : syracuseStep 3294359 = 4941539) B4941539
theorem B2196683 : Blo 1462551 2196683 := bstep (se 1 (by rfl) ⟨1647512, by rfl⟩ : syracuseStep 2196683 = 3295025) B3295025
theorem B2196695 : Blo 1462551 2196695 := bstep (se 1 (by rfl) ⟨1647521, by rfl⟩ : syracuseStep 2196695 = 3295043) B3295043
theorem B2196761 : Blo 1462551 2196761 := bstep (se 2 (by rfl) ⟨823785, by rfl⟩ : syracuseStep 2196761 = 1647571) B1647571
theorem B7030061 : Blo 1462551 7030061 := bstep (se 3 (by rfl) ⟨1318136, by rfl⟩ : syracuseStep 7030061 = 2636273) B2636273
theorem B4941107 : Blo 1462551 4941107 := bstep (se 1 (by rfl) ⟨3705830, by rfl⟩ : syracuseStep 4941107 = 7411661) B7411661
theorem B3294539 : Blo 1462551 3294539 := bstep (se 1 (by rfl) ⟨2470904, by rfl⟩ : syracuseStep 3294539 = 4941809) B4941809
theorem B2778455 : Blo 1462551 2778455 := bstep (se 1 (by rfl) ⟨2083841, by rfl⟩ : syracuseStep 2778455 = 4167683) B4167683
theorem B3294593 : Blo 1462551 3294593 := bstep (se 2 (by rfl) ⟨1235472, by rfl⟩ : syracuseStep 3294593 = 2470945) B2470945
theorem B5555587 : Blo 1462551 5555587 := bstep (se 1 (by rfl) ⟨4166690, by rfl⟩ : syracuseStep 5555587 = 8333381) B8333381
theorem B1852951 : Blo 1462551 1852951 := bstep (se 1 (by rfl) ⟨1389713, by rfl⟩ : syracuseStep 1852951 = 2779427) B2779427
theorem B6014515 : Blo 1462551 6014515 := bstep (se 1 (by rfl) ⟨4510886, by rfl⟩ : syracuseStep 6014515 = 9021773) B9021773
theorem B4941377 : Blo 1462551 4941377 := bstep (se 2 (by rfl) ⟨1853016, by rfl⟩ : syracuseStep 4941377 = 3706033) B3706033
theorem B3515993 : Blo 1462551 3515993 := bstep (se 2 (by rfl) ⟨1318497, by rfl⟩ : syracuseStep 3515993 = 2636995) B2636995
theorem B3294809 : Blo 1462551 3294809 := bstep (se 2 (by rfl) ⟨1235553, by rfl⟩ : syracuseStep 3294809 = 2471107) B2471107
theorem B2082457 : Blo 1462551 2082457 := bstep (se 2 (by rfl) ⟨780921, by rfl⟩ : syracuseStep 2082457 = 1561843) B1561843
theorem B5555891 : Blo 1462551 5555891 := bstep (se 1 (by rfl) ⟨4166918, by rfl⟩ : syracuseStep 5555891 = 8333837) B8333837
theorem B3294899 : Blo 1462551 3294899 := bstep (se 1 (by rfl) ⟨2471174, by rfl⟩ : syracuseStep 3294899 = 4942349) B4942349
theorem B3294935 : Blo 1462551 3294935 := bstep (se 1 (by rfl) ⟨2471201, by rfl⟩ : syracuseStep 3294935 = 4942403) B4942403
theorem B4450099 : Blo 1462551 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B3295115 : Blo 1462551 3295115 := bstep (se 1 (by rfl) ⟨2471336, by rfl⟩ : syracuseStep 3295115 = 4942673) B4942673
theorem B3336115 : Blo 1462551 3336115 := bstep (se 1 (by rfl) ⟨2502086, by rfl⟩ : syracuseStep 3336115 = 5004173) B5004173
theorem B9373619 : Blo 1462551 9373619 := bstep (se 1 (by rfl) ⟨7030214, by rfl⟩ : syracuseStep 9373619 = 14060429) B14060429
theorem B3295169 : Blo 1462551 3295169 := bstep (se 2 (by rfl) ⟨1235688, by rfl⟩ : syracuseStep 3295169 = 2471377) B2471377
theorem B2779123 : Blo 1462551 2779123 := bstep (se 1 (by rfl) ⟨2084342, by rfl⟩ : syracuseStep 2779123 = 4168685) B4168685
theorem B16680977 : Blo 1462551 16680977 := bstep (se 2 (by rfl) ⟨6255366, by rfl⟩ : syracuseStep 16680977 = 12510733) B12510733
theorem B11110445 : Blo 1462551 11110445 := bstep (se 3 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 11110445 = 4166417) B4166417
theorem B2967617 : Blo 1462551 2967617 := bstep (se 2 (by rfl) ⟨1112856, by rfl⟩ : syracuseStep 2967617 = 2225713) B2225713
theorem B3516491 : Blo 1462551 3516491 := bstep (se 1 (by rfl) ⟨2637368, by rfl⟩ : syracuseStep 3516491 = 5274737) B5274737
theorem B4941917 : Blo 1462551 4941917 := bstep (se 3 (by rfl) ⟨926609, by rfl⟩ : syracuseStep 4941917 = 1853219) B1853219
theorem B3705011 : Blo 1462551 3705011 := bstep (se 1 (by rfl) ⟨2778758, by rfl⟩ : syracuseStep 3705011 = 5557517) B5557517
theorem B5556545 : Blo 1462551 5556545 := bstep (se 2 (by rfl) ⟨2083704, by rfl⟩ : syracuseStep 5556545 = 4167409) B4167409
theorem B2468171 : Blo 1462551 2468171 := bstep (se 1 (by rfl) ⟨1851128, by rfl⟩ : syracuseStep 2468171 = 3702257) B3702257
theorem B2967883 : Blo 1462551 2967883 := bstep (se 1 (by rfl) ⟨2225912, by rfl⟩ : syracuseStep 2967883 = 4451825) B4451825
theorem B1976729 : Blo 1462551 1976729 := bstep (se 2 (by rfl) ⟨741273, by rfl⟩ : syracuseStep 1976729 = 1482547) B1482547
theorem B2779571 : Blo 1462551 2779571 := bstep (se 1 (by rfl) ⟨2084678, by rfl⟩ : syracuseStep 2779571 = 4169357) B4169357
theorem B2468299 : Blo 1462551 2468299 := bstep (se 1 (by rfl) ⟨1851224, by rfl⟩ : syracuseStep 2468299 = 3702449) B3702449
theorem B2779609 : Blo 1462551 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B4450781 : Blo 1462551 4450781 := bstep (se 3 (by rfl) ⟨834521, by rfl⟩ : syracuseStep 4450781 = 1669043) B1669043
theorem B2468441 : Blo 1462551 2468441 := bstep (se 2 (by rfl) ⟨925665, by rfl⟩ : syracuseStep 2468441 = 1851331) B1851331
theorem B7408259 : Blo 1462551 7408259 := bstep (se 1 (by rfl) ⟨5556194, by rfl⟩ : syracuseStep 7408259 = 11112389) B11112389
theorem B3705547 : Blo 1462551 3705547 := bstep (se 1 (by rfl) ⟨2779160, by rfl⟩ : syracuseStep 3705547 = 5558321) B5558321
theorem B2468569 : Blo 1462551 2468569 := bstep (se 2 (by rfl) ⟨925713, by rfl⟩ : syracuseStep 2468569 = 1851427) B1851427
theorem B7129873 : Blo 1462551 7129873 := bstep (se 2 (by rfl) ⟨2673702, by rfl⟩ : syracuseStep 7129873 = 5347405) B5347405
theorem B3705689 : Blo 1462551 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B11873155 : Blo 1462551 11873155 := bstep (se 1 (by rfl) ⟨8904866, by rfl⟩ : syracuseStep 11873155 = 17809733) B17809733
theorem B2780057 : Blo 1462551 2780057 := bstep (se 2 (by rfl) ⟨1042521, by rfl⟩ : syracuseStep 2780057 = 2085043) B2085043
theorem B2673587 : Blo 1462551 2673587 := bstep (se 1 (by rfl) ⟨2005190, by rfl⟩ : syracuseStep 2673587 = 4010381) B4010381
theorem B171002821 : Blo 1462551 171002821 := bstep (se 4 (by rfl) ⟨16031514, by rfl⟩ : syracuseStep 171002821 = 32063029) B32063029
theorem B2083801 : Blo 1462551 2083801 := bstep (se 2 (by rfl) ⟨781425, by rfl⟩ : syracuseStep 2083801 = 1562851) B1562851
theorem B2083915 : Blo 1462551 2083915 := bstep (se 1 (by rfl) ⟨1562936, by rfl⟩ : syracuseStep 2083915 = 3125873) B3125873
theorem B2968663 : Blo 1462551 2968663 := bstep (se 1 (by rfl) ⟨2226497, by rfl⟩ : syracuseStep 2968663 = 4452995) B4452995
theorem B10546307 : Blo 1462551 10546307 := bstep (se 1 (by rfl) ⟨7909730, by rfl⟩ : syracuseStep 10546307 = 15819461) B15819461
theorem B8899735 : Blo 1462551 8899735 := bstep (se 1 (by rfl) ⟨6674801, by rfl⟩ : syracuseStep 8899735 = 13349603) B13349603
theorem B19016855 : Blo 1462551 19016855 := bstep (se 1 (by rfl) ⟨14262641, by rfl⟩ : syracuseStep 19016855 = 28525283) B28525283
theorem B2469143 : Blo 1462551 2469143 := bstep (se 1 (by rfl) ⟨1851857, by rfl⟩ : syracuseStep 2469143 = 3703715) B3703715
theorem B2469271 : Blo 1462551 2469271 := bstep (se 1 (by rfl) ⟨1851953, by rfl⟩ : syracuseStep 2469271 = 3703907) B3703907
theorem B8015321 : Blo 1462551 8015321 := bstep (se 2 (by rfl) ⟨3005745, by rfl⟩ : syracuseStep 8015321 = 6011491) B6011491
theorem B4689373 : Blo 1462551 4689373 := bstep (se 3 (by rfl) ⟨879257, by rfl⟩ : syracuseStep 4689373 = 1758515) B1758515
theorem B2674201 : Blo 1462551 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B5557805 : Blo 1462551 5557805 := bstep (se 3 (by rfl) ⟨1042088, by rfl⟩ : syracuseStep 5557805 = 2084177) B2084177
theorem B5557835 : Blo 1462551 5557835 := bstep (se 1 (by rfl) ⟨4168376, by rfl⟩ : syracuseStep 5557835 = 8336753) B8336753
theorem B101346947 : Blo 1462551 101346947 := bstep (se 1 (by rfl) ⟨76010210, by rfl⟩ : syracuseStep 101346947 = 152020421) B152020421
theorem B2223767 : Blo 1462551 2223767 := bstep (se 1 (by rfl) ⟨1667825, by rfl⟩ : syracuseStep 2223767 = 3335651) B3335651
theorem B21106327 : Blo 1462551 21106327 := bstep (se 1 (by rfl) ⟨15829745, by rfl⟩ : syracuseStep 21106327 = 31659491) B31659491
theorem B3706519 : Blo 1462551 3706519 := bstep (se 1 (by rfl) ⟨2779889, by rfl⟩ : syracuseStep 3706519 = 5559779) B5559779
theorem B6254273 : Blo 1462551 6254273 := bstep (se 2 (by rfl) ⟨2345352, by rfl⟩ : syracuseStep 6254273 = 4690705) B4690705
theorem B3337985 : Blo 1462551 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B2256727 : Blo 1462551 2256727 := bstep (se 1 (by rfl) ⟨1692545, by rfl⟩ : syracuseStep 2256727 = 3385091) B3385091
theorem B15830963 : Blo 1462551 15830963 := bstep (se 1 (by rfl) ⟨11873222, by rfl⟩ : syracuseStep 15830963 = 23746445) B23746445
theorem B7909337 : Blo 1462551 7909337 := bstep (se 2 (by rfl) ⟨2966001, by rfl⟩ : syracuseStep 7909337 = 5932003) B5932003
theorem B4165597 : Blo 1462551 4165597 := bstep (se 3 (by rfl) ⟨781049, by rfl⟩ : syracuseStep 4165597 = 1562099) B1562099
theorem B12029957 : Blo 1462551 12029957 := bstep (se 4 (by rfl) ⟨1127808, by rfl⟩ : syracuseStep 12029957 = 2255617) B2255617
theorem B2469899 : Blo 1462551 2469899 := bstep (se 1 (by rfl) ⟨1852424, by rfl⟩ : syracuseStep 2469899 = 3704849) B3704849
theorem B3706955 : Blo 1462551 3706955 := bstep (se 1 (by rfl) ⟨2780216, by rfl⟩ : syracuseStep 3706955 = 5560433) B5560433
theorem B26693725 : Blo 1462551 26693725 := bstep (se 3 (by rfl) ⟨5005073, by rfl⟩ : syracuseStep 26693725 = 10010147) B10010147
theorem B9375875 : Blo 1462551 9375875 := bstep (se 1 (by rfl) ⟨7031906, by rfl⟩ : syracuseStep 9375875 = 14063813) B14063813
theorem B2470027 : Blo 1462551 2470027 := bstep (se 1 (by rfl) ⟨1852520, by rfl⟩ : syracuseStep 2470027 = 3705041) B3705041
theorem B4165825 : Blo 1462551 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B5558489 : Blo 1462551 5558489 := bstep (se 2 (by rfl) ⟨2084433, by rfl⟩ : syracuseStep 5558489 = 4168867) B4168867
theorem B1462551 : Blo 1462551 1462551 := bstep (se 1 (by rfl) ⟨1096913, by rfl⟩ : syracuseStep 1462551 = 2193827) B2193827
theorem B2470169 : Blo 1462551 2470169 := bstep (se 2 (by rfl) ⟨926313, by rfl⟩ : syracuseStep 2470169 = 1852627) B1852627
theorem B1462571 : Blo 1462551 1462571 := bstep (se 1 (by rfl) ⟨1096928, by rfl⟩ : syracuseStep 1462571 = 2193857) B2193857
theorem B1462583 : Blo 1462551 1462583 := bstep (se 1 (by rfl) ⟨1096937, by rfl⟩ : syracuseStep 1462583 = 2193875) B2193875
theorem B1462603 : Blo 1462551 1462603 := bstep (se 1 (by rfl) ⟨1096952, by rfl⟩ : syracuseStep 1462603 = 2193905) B2193905
theorem B1462615 : Blo 1462551 1462615 := bstep (se 1 (by rfl) ⟨1096961, by rfl⟩ : syracuseStep 1462615 = 2193923) B2193923
theorem B6254941 : Blo 1462551 6254941 := bstep (se 3 (by rfl) ⟨1172801, by rfl⟩ : syracuseStep 6254941 = 2345603) B2345603
theorem B1462635 : Blo 1462551 1462635 := bstep (se 1 (by rfl) ⟨1096976, by rfl⟩ : syracuseStep 1462635 = 2193953) B2193953
theorem B1462647 : Blo 1462551 1462647 := bstep (se 1 (by rfl) ⟨1096985, by rfl⟩ : syracuseStep 1462647 = 2193971) B2193971
theorem B3125633 : Blo 1462551 3125633 := bstep (se 2 (by rfl) ⟨1172112, by rfl⟩ : syracuseStep 3125633 = 2344225) B2344225
theorem B1462667 : Blo 1462551 1462667 := bstep (se 1 (by rfl) ⟨1097000, by rfl⟩ : syracuseStep 1462667 = 2194001) B2194001
theorem B2085259 : Blo 1462551 2085259 := bstep (se 1 (by rfl) ⟨1563944, by rfl⟩ : syracuseStep 2085259 = 3127889) B3127889
theorem B1462679 : Blo 1462551 1462679 := bstep (se 1 (by rfl) ⟨1097009, by rfl⟩ : syracuseStep 1462679 = 2194019) B2194019
theorem B2470297 : Blo 1462551 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B1462699 : Blo 1462551 1462699 := bstep (se 1 (by rfl) ⟨1097024, by rfl⟩ : syracuseStep 1462699 = 2194049) B2194049
theorem B1462711 : Blo 1462551 1462711 := bstep (se 1 (by rfl) ⟨1097033, by rfl⟩ : syracuseStep 1462711 = 2194067) B2194067
theorem B4936139 : Blo 1462551 4936139 := bstep (se 1 (by rfl) ⟨3702104, by rfl⟩ : syracuseStep 4936139 = 7404209) B7404209
theorem B1462731 : Blo 1462551 1462731 := bstep (se 1 (by rfl) ⟨1097048, by rfl⟩ : syracuseStep 1462731 = 2194097) B2194097
theorem B1462743 : Blo 1462551 1462743 := bstep (se 1 (by rfl) ⟨1097057, by rfl⟩ : syracuseStep 1462743 = 2194115) B2194115
theorem B3125719 : Blo 1462551 3125719 := bstep (se 1 (by rfl) ⟨2344289, by rfl⟩ : syracuseStep 3125719 = 4688579) B4688579
theorem B1462763 : Blo 1462551 1462763 := bstep (se 1 (by rfl) ⟨1097072, by rfl⟩ : syracuseStep 1462763 = 2194145) B2194145
theorem B1462775 : Blo 1462551 1462775 := bstep (se 1 (by rfl) ⟨1097081, by rfl⟩ : syracuseStep 1462775 = 2194163) B2194163
theorem B1462795 : Blo 1462551 1462795 := bstep (se 1 (by rfl) ⟨1097096, by rfl⟩ : syracuseStep 1462795 = 2194193) B2194193
theorem B63336977 : Blo 1462551 63336977 := bstep (se 2 (by rfl) ⟨23751366, by rfl⟩ : syracuseStep 63336977 = 47502733) B47502733
theorem B1462807 : Blo 1462551 1462807 := bstep (se 1 (by rfl) ⟨1097105, by rfl⟩ : syracuseStep 1462807 = 2194211) B2194211
theorem B4166167 : Blo 1462551 4166167 := bstep (se 1 (by rfl) ⟨3124625, by rfl⟩ : syracuseStep 4166167 = 6249251) B6249251
theorem B5558807 : Blo 1462551 5558807 := bstep (se 1 (by rfl) ⟨4169105, by rfl⟩ : syracuseStep 5558807 = 8338211) B8338211
theorem B4452887 : Blo 1462551 4452887 := bstep (se 1 (by rfl) ⟨3339665, by rfl⟩ : syracuseStep 4452887 = 6679331) B6679331
theorem B1462827 : Blo 1462551 1462827 := bstep (se 1 (by rfl) ⟨1097120, by rfl⟩ : syracuseStep 1462827 = 2194241) B2194241
theorem B1462839 : Blo 1462551 1462839 := bstep (se 1 (by rfl) ⟨1097129, by rfl⟩ : syracuseStep 1462839 = 2194259) B2194259
theorem B1462859 : Blo 1462551 1462859 := bstep (se 1 (by rfl) ⟨1097144, by rfl⟩ : syracuseStep 1462859 = 2194289) B2194289
theorem B1462871 : Blo 1462551 1462871 := bstep (se 1 (by rfl) ⟨1097153, by rfl⟩ : syracuseStep 1462871 = 2194307) B2194307
theorem B1462891 : Blo 1462551 1462891 := bstep (se 1 (by rfl) ⟨1097168, by rfl⟩ : syracuseStep 1462891 = 2194337) B2194337
theorem B1462903 : Blo 1462551 1462903 := bstep (se 1 (by rfl) ⟨1097177, by rfl⟩ : syracuseStep 1462903 = 2194355) B2194355
theorem B1462923 : Blo 1462551 1462923 := bstep (se 1 (by rfl) ⟨1097192, by rfl⟩ : syracuseStep 1462923 = 2194385) B2194385
theorem B1462935 : Blo 1462551 1462935 := bstep (se 1 (by rfl) ⟨1097201, by rfl⟩ : syracuseStep 1462935 = 2194403) B2194403
theorem B1462955 : Blo 1462551 1462955 := bstep (se 1 (by rfl) ⟨1097216, by rfl⟩ : syracuseStep 1462955 = 2194433) B2194433
theorem B1462967 : Blo 1462551 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B1462987 : Blo 1462551 1462987 := bstep (se 1 (by rfl) ⟨1097240, by rfl⟩ : syracuseStep 1462987 = 2194481) B2194481
theorem B1462999 : Blo 1462551 1462999 := bstep (se 1 (by rfl) ⟨1097249, by rfl⟩ : syracuseStep 1462999 = 2194499) B2194499
theorem B4936409 : Blo 1462551 4936409 := bstep (se 2 (by rfl) ⟨1851153, by rfl⟩ : syracuseStep 4936409 = 3702307) B3702307
theorem B1463019 : Blo 1462551 1463019 := bstep (se 1 (by rfl) ⟨1097264, by rfl⟩ : syracuseStep 1463019 = 2194529) B2194529
theorem B1463031 : Blo 1462551 1463031 := bstep (se 1 (by rfl) ⟨1097273, by rfl⟩ : syracuseStep 1463031 = 2194547) B2194547
theorem B1463051 : Blo 1462551 1463051 := bstep (se 1 (by rfl) ⟨1097288, by rfl⟩ : syracuseStep 1463051 = 2194577) B2194577
theorem B1463063 : Blo 1462551 1463063 := bstep (se 1 (by rfl) ⟨1097297, by rfl⟩ : syracuseStep 1463063 = 2194595) B2194595
theorem B1463083 : Blo 1462551 1463083 := bstep (se 1 (by rfl) ⟨1097312, by rfl⟩ : syracuseStep 1463083 = 2194625) B2194625
theorem B1463095 : Blo 1462551 1463095 := bstep (se 1 (by rfl) ⟨1097321, by rfl⟩ : syracuseStep 1463095 = 2194643) B2194643
theorem B1463115 : Blo 1462551 1463115 := bstep (se 1 (by rfl) ⟨1097336, by rfl⟩ : syracuseStep 1463115 = 2194673) B2194673
theorem B1463127 : Blo 1462551 1463127 := bstep (se 1 (by rfl) ⟨1097345, by rfl⟩ : syracuseStep 1463127 = 2194691) B2194691
theorem B4453213 : Blo 1462551 4453213 := bstep (se 3 (by rfl) ⟨834977, by rfl⟩ : syracuseStep 4453213 = 1669955) B1669955
theorem B1463147 : Blo 1462551 1463147 := bstep (se 1 (by rfl) ⟨1097360, by rfl⟩ : syracuseStep 1463147 = 2194721) B2194721
theorem B1463159 : Blo 1462551 1463159 := bstep (se 1 (by rfl) ⟨1097369, by rfl⟩ : syracuseStep 1463159 = 2194739) B2194739
theorem B1463179 : Blo 1462551 1463179 := bstep (se 1 (by rfl) ⟨1097384, by rfl⟩ : syracuseStep 1463179 = 2194769) B2194769
theorem B1463191 : Blo 1462551 1463191 := bstep (se 1 (by rfl) ⟨1097393, by rfl⟩ : syracuseStep 1463191 = 2194787) B2194787
theorem B1463211 : Blo 1462551 1463211 := bstep (se 1 (by rfl) ⟨1097408, by rfl⟩ : syracuseStep 1463211 = 2194817) B2194817
theorem B6255539 : Blo 1462551 6255539 := bstep (se 1 (by rfl) ⟨4691654, by rfl⟩ : syracuseStep 6255539 = 9383309) B9383309
theorem B1463223 : Blo 1462551 1463223 := bstep (se 1 (by rfl) ⟨1097417, by rfl⟩ : syracuseStep 1463223 = 2194835) B2194835
theorem B1463243 : Blo 1462551 1463243 := bstep (se 1 (by rfl) ⟨1097432, by rfl⟩ : syracuseStep 1463243 = 2194865) B2194865
theorem B1463255 : Blo 1462551 1463255 := bstep (se 1 (by rfl) ⟨1097441, by rfl⟩ : syracuseStep 1463255 = 2194883) B2194883
theorem B2470871 : Blo 1462551 2470871 := bstep (se 1 (by rfl) ⟨1853153, by rfl⟩ : syracuseStep 2470871 = 3706307) B3706307
theorem B1463275 : Blo 1462551 1463275 := bstep (se 1 (by rfl) ⟨1097456, by rfl⟩ : syracuseStep 1463275 = 2194913) B2194913
theorem B1463287 : Blo 1462551 1463287 := bstep (se 1 (by rfl) ⟨1097465, by rfl⟩ : syracuseStep 1463287 = 2194931) B2194931
theorem B1463307 : Blo 1462551 1463307 := bstep (se 1 (by rfl) ⟨1097480, by rfl⟩ : syracuseStep 1463307 = 2194961) B2194961
theorem B1463319 : Blo 1462551 1463319 := bstep (se 1 (by rfl) ⟨1097489, by rfl⟩ : syracuseStep 1463319 = 2194979) B2194979
theorem B1463339 : Blo 1462551 1463339 := bstep (se 1 (by rfl) ⟨1097504, by rfl⟩ : syracuseStep 1463339 = 2195009) B2195009
theorem B6247475 : Blo 1462551 6247475 := bstep (se 1 (by rfl) ⟨4685606, by rfl⟩ : syracuseStep 6247475 = 9371213) B9371213
theorem B1463351 : Blo 1462551 1463351 := bstep (se 1 (by rfl) ⟨1097513, by rfl⟩ : syracuseStep 1463351 = 2195027) B2195027
theorem B1463371 : Blo 1462551 1463371 := bstep (se 1 (by rfl) ⟨1097528, by rfl⟩ : syracuseStep 1463371 = 2195057) B2195057
theorem B1463383 : Blo 1462551 1463383 := bstep (se 1 (by rfl) ⟨1097537, by rfl⟩ : syracuseStep 1463383 = 2195075) B2195075
theorem B2470999 : Blo 1462551 2470999 := bstep (se 1 (by rfl) ⟨1853249, by rfl⟩ : syracuseStep 2470999 = 3706499) B3706499
theorem B1463403 : Blo 1462551 1463403 := bstep (se 1 (by rfl) ⟨1097552, by rfl⟩ : syracuseStep 1463403 = 2195105) B2195105
theorem B1463415 : Blo 1462551 1463415 := bstep (se 1 (by rfl) ⟨1097561, by rfl⟩ : syracuseStep 1463415 = 2195123) B2195123
theorem B1463435 : Blo 1462551 1463435 := bstep (se 1 (by rfl) ⟨1097576, by rfl⟩ : syracuseStep 1463435 = 2195153) B2195153
theorem B5272721 : Blo 1462551 5272721 := bstep (se 2 (by rfl) ⟨1977270, by rfl⟩ : syracuseStep 5272721 = 3954541) B3954541
theorem B1463447 : Blo 1462551 1463447 := bstep (se 1 (by rfl) ⟨1097585, by rfl⟩ : syracuseStep 1463447 = 2195171) B2195171
theorem B1463467 : Blo 1462551 1463467 := bstep (se 1 (by rfl) ⟨1097600, by rfl⟩ : syracuseStep 1463467 = 2195201) B2195201
theorem B5559475 : Blo 1462551 5559475 := bstep (se 1 (by rfl) ⟨4169606, by rfl⟩ : syracuseStep 5559475 = 8339213) B8339213
theorem B1463479 : Blo 1462551 1463479 := bstep (se 1 (by rfl) ⟨1097609, by rfl⟩ : syracuseStep 1463479 = 2195219) B2195219
theorem B5706955 : Blo 1462551 5706955 := bstep (se 1 (by rfl) ⟨4280216, by rfl⟩ : syracuseStep 5706955 = 8560433) B8560433
theorem B1463499 : Blo 1462551 1463499 := bstep (se 1 (by rfl) ⟨1097624, by rfl⟩ : syracuseStep 1463499 = 2195249) B2195249
theorem B6337739 : Blo 1462551 6337739 := bstep (se 1 (by rfl) ⟨4753304, by rfl⟩ : syracuseStep 6337739 = 9506609) B9506609
theorem B1463511 : Blo 1462551 1463511 := bstep (se 1 (by rfl) ⟨1097633, by rfl⟩ : syracuseStep 1463511 = 2195267) B2195267
theorem B4166873 : Blo 1462551 4166873 := bstep (se 2 (by rfl) ⟨1562577, by rfl⟩ : syracuseStep 4166873 = 3125155) B3125155
theorem B1463531 : Blo 1462551 1463531 := bstep (se 1 (by rfl) ⟨1097648, by rfl⟩ : syracuseStep 1463531 = 2195297) B2195297
theorem B1463543 : Blo 1462551 1463543 := bstep (se 1 (by rfl) ⟨1097657, by rfl⟩ : syracuseStep 1463543 = 2195315) B2195315
theorem B1463563 : Blo 1462551 1463563 := bstep (se 1 (by rfl) ⟨1097672, by rfl⟩ : syracuseStep 1463563 = 2195345) B2195345
theorem B3126539 : Blo 1462551 3126539 := bstep (se 1 (by rfl) ⟨2344904, by rfl⟩ : syracuseStep 3126539 = 4689809) B4689809
theorem B1463575 : Blo 1462551 1463575 := bstep (se 1 (by rfl) ⟨1097681, by rfl⟩ : syracuseStep 1463575 = 2195363) B2195363
theorem B2503961 : Blo 1462551 2503961 := bstep (se 2 (by rfl) ⟨938985, by rfl⟩ : syracuseStep 2503961 = 1877971) B1877971
theorem B1463595 : Blo 1462551 1463595 := bstep (se 1 (by rfl) ⟨1097696, by rfl⟩ : syracuseStep 1463595 = 2195393) B2195393
theorem B1463607 : Blo 1462551 1463607 := bstep (se 1 (by rfl) ⟨1097705, by rfl⟩ : syracuseStep 1463607 = 2195411) B2195411
theorem B1463627 : Blo 1462551 1463627 := bstep (se 1 (by rfl) ⟨1097720, by rfl⟩ : syracuseStep 1463627 = 2195441) B2195441
theorem B1463639 : Blo 1462551 1463639 := bstep (se 1 (by rfl) ⟨1097729, by rfl⟩ : syracuseStep 1463639 = 2195459) B2195459
theorem B1463659 : Blo 1462551 1463659 := bstep (se 1 (by rfl) ⟨1097744, by rfl⟩ : syracuseStep 1463659 = 2195489) B2195489
theorem B1463671 : Blo 1462551 1463671 := bstep (se 1 (by rfl) ⟨1097753, by rfl⟩ : syracuseStep 1463671 = 2195507) B2195507
theorem B1463691 : Blo 1462551 1463691 := bstep (se 1 (by rfl) ⟨1097768, by rfl⟩ : syracuseStep 1463691 = 2195537) B2195537
theorem B4937111 : Blo 1462551 4937111 := bstep (se 1 (by rfl) ⟨3702833, by rfl⟩ : syracuseStep 4937111 = 7405667) B7405667
theorem B1463703 : Blo 1462551 1463703 := bstep (se 1 (by rfl) ⟨1097777, by rfl⟩ : syracuseStep 1463703 = 2195555) B2195555
theorem B3339671 : Blo 1462551 3339671 := bstep (se 1 (by rfl) ⟨2504753, by rfl⟩ : syracuseStep 3339671 = 5009507) B5009507
theorem B1463723 : Blo 1462551 1463723 := bstep (se 1 (by rfl) ⟨1097792, by rfl⟩ : syracuseStep 1463723 = 2195585) B2195585
theorem B1463735 : Blo 1462551 1463735 := bstep (se 1 (by rfl) ⟨1097801, by rfl⟩ : syracuseStep 1463735 = 2195603) B2195603
theorem B1463755 : Blo 1462551 1463755 := bstep (se 1 (by rfl) ⟨1097816, by rfl⟩ : syracuseStep 1463755 = 2195633) B2195633
theorem B1463767 : Blo 1462551 1463767 := bstep (se 1 (by rfl) ⟨1097825, by rfl⟩ : syracuseStep 1463767 = 2195651) B2195651
theorem B1463787 : Blo 1462551 1463787 := bstep (se 1 (by rfl) ⟨1097840, by rfl⟩ : syracuseStep 1463787 = 2195681) B2195681
theorem B1463799 : Blo 1462551 1463799 := bstep (se 1 (by rfl) ⟨1097849, by rfl⟩ : syracuseStep 1463799 = 2195699) B2195699
theorem B1463819 : Blo 1462551 1463819 := bstep (se 1 (by rfl) ⟨1097864, by rfl⟩ : syracuseStep 1463819 = 2195729) B2195729
theorem B1463831 : Blo 1462551 1463831 := bstep (se 1 (by rfl) ⟨1097873, by rfl⟩ : syracuseStep 1463831 = 2195747) B2195747
theorem B1463851 : Blo 1462551 1463851 := bstep (se 1 (by rfl) ⟨1097888, by rfl⟩ : syracuseStep 1463851 = 2195777) B2195777
theorem B1463863 : Blo 1462551 1463863 := bstep (se 1 (by rfl) ⟨1097897, by rfl⟩ : syracuseStep 1463863 = 2195795) B2195795
theorem B1463883 : Blo 1462551 1463883 := bstep (se 1 (by rfl) ⟨1097912, by rfl⟩ : syracuseStep 1463883 = 2195825) B2195825
theorem B1463895 : Blo 1462551 1463895 := bstep (se 1 (by rfl) ⟨1097921, by rfl⟩ : syracuseStep 1463895 = 2195843) B2195843
theorem B1463915 : Blo 1462551 1463915 := bstep (se 1 (by rfl) ⟨1097936, by rfl⟩ : syracuseStep 1463915 = 2195873) B2195873
theorem B1463927 : Blo 1462551 1463927 := bstep (se 1 (by rfl) ⟨1097945, by rfl⟩ : syracuseStep 1463927 = 2195891) B2195891
theorem B1463947 : Blo 1462551 1463947 := bstep (se 1 (by rfl) ⟨1097960, by rfl⟩ : syracuseStep 1463947 = 2195921) B2195921
theorem B1463959 : Blo 1462551 1463959 := bstep (se 1 (by rfl) ⟨1097969, by rfl⟩ : syracuseStep 1463959 = 2195939) B2195939
theorem B3290777 : Blo 1462551 3290777 := bstep (se 2 (by rfl) ⟨1234041, by rfl⟩ : syracuseStep 3290777 = 2468083) B2468083
theorem B3339929 : Blo 1462551 3339929 := bstep (se 2 (by rfl) ⟨1252473, by rfl⟩ : syracuseStep 3339929 = 2504947) B2504947
theorem B1463979 : Blo 1462551 1463979 := bstep (se 1 (by rfl) ⟨1097984, by rfl⟩ : syracuseStep 1463979 = 2195969) B2195969
theorem B5273267 : Blo 1462551 5273267 := bstep (se 1 (by rfl) ⟨3954950, by rfl⟩ : syracuseStep 5273267 = 7909901) B7909901
theorem B1463991 : Blo 1462551 1463991 := bstep (se 1 (by rfl) ⟨1097993, by rfl⟩ : syracuseStep 1463991 = 2195987) B2195987
theorem B1464011 : Blo 1462551 1464011 := bstep (se 1 (by rfl) ⟨1098008, by rfl⟩ : syracuseStep 1464011 = 2196017) B2196017
theorem B1464023 : Blo 1462551 1464023 := bstep (se 1 (by rfl) ⟨1098017, by rfl⟩ : syracuseStep 1464023 = 2196035) B2196035
theorem B1464043 : Blo 1462551 1464043 := bstep (se 1 (by rfl) ⟨1098032, by rfl⟩ : syracuseStep 1464043 = 2196065) B2196065
theorem B3290867 : Blo 1462551 3290867 := bstep (se 1 (by rfl) ⟨2468150, by rfl⟩ : syracuseStep 3290867 = 4936301) B4936301
theorem B1464055 : Blo 1462551 1464055 := bstep (se 1 (by rfl) ⟨1098041, by rfl⟩ : syracuseStep 1464055 = 2196083) B2196083
theorem B1464075 : Blo 1462551 1464075 := bstep (se 1 (by rfl) ⟨1098056, by rfl⟩ : syracuseStep 1464075 = 2196113) B2196113
theorem B3290903 : Blo 1462551 3290903 := bstep (se 1 (by rfl) ⟨2468177, by rfl⟩ : syracuseStep 3290903 = 4936355) B4936355
theorem B1464087 : Blo 1462551 1464087 := bstep (se 1 (by rfl) ⟨1098065, by rfl⟩ : syracuseStep 1464087 = 2196131) B2196131
theorem B1464107 : Blo 1462551 1464107 := bstep (se 1 (by rfl) ⟨1098080, by rfl⟩ : syracuseStep 1464107 = 2196161) B2196161
theorem B1464119 : Blo 1462551 1464119 := bstep (se 1 (by rfl) ⟨1098089, by rfl⟩ : syracuseStep 1464119 = 2196179) B2196179
theorem B1464139 : Blo 1462551 1464139 := bstep (se 1 (by rfl) ⟨1098104, by rfl⟩ : syracuseStep 1464139 = 2196209) B2196209
theorem B1464151 : Blo 1462551 1464151 := bstep (se 1 (by rfl) ⟨1098113, by rfl⟩ : syracuseStep 1464151 = 2196227) B2196227
theorem B11114333 : Blo 1462551 11114333 := bstep (se 3 (by rfl) ⟨2083937, by rfl⟩ : syracuseStep 11114333 = 4167875) B4167875
theorem B1464171 : Blo 1462551 1464171 := bstep (se 1 (by rfl) ⟨1098128, by rfl⟩ : syracuseStep 1464171 = 2196257) B2196257
theorem B1464183 : Blo 1462551 1464183 := bstep (se 1 (by rfl) ⟨1098137, by rfl⟩ : syracuseStep 1464183 = 2196275) B2196275
theorem B1464203 : Blo 1462551 1464203 := bstep (se 1 (by rfl) ⟨1098152, by rfl⟩ : syracuseStep 1464203 = 2196305) B2196305
theorem B1464215 : Blo 1462551 1464215 := bstep (se 1 (by rfl) ⟨1098161, by rfl⟩ : syracuseStep 1464215 = 2196323) B2196323
theorem B1464235 : Blo 1462551 1464235 := bstep (se 1 (by rfl) ⟨1098176, by rfl⟩ : syracuseStep 1464235 = 2196353) B2196353
theorem B4937651 : Blo 1462551 4937651 := bstep (se 1 (by rfl) ⟨3703238, by rfl⟩ : syracuseStep 4937651 = 7406477) B7406477
theorem B1464247 : Blo 1462551 1464247 := bstep (se 1 (by rfl) ⟨1098185, by rfl⟩ : syracuseStep 1464247 = 2196371) B2196371
theorem B3291083 : Blo 1462551 3291083 := bstep (se 1 (by rfl) ⟨2468312, by rfl⟩ : syracuseStep 3291083 = 4936625) B4936625
theorem B1464267 : Blo 1462551 1464267 := bstep (se 1 (by rfl) ⟨1098200, by rfl⟩ : syracuseStep 1464267 = 2196401) B2196401
theorem B1669079 : Blo 1462551 1669079 := bstep (se 1 (by rfl) ⟨1251809, by rfl⟩ : syracuseStep 1669079 = 2503619) B2503619
theorem B1464279 : Blo 1462551 1464279 := bstep (se 1 (by rfl) ⟨1098209, by rfl⟩ : syracuseStep 1464279 = 2196419) B2196419
theorem B1464299 : Blo 1462551 1464299 := bstep (se 1 (by rfl) ⟨1098224, by rfl⟩ : syracuseStep 1464299 = 2196449) B2196449
theorem B1464311 : Blo 1462551 1464311 := bstep (se 1 (by rfl) ⟨1098233, by rfl⟩ : syracuseStep 1464311 = 2196467) B2196467
theorem B3291137 : Blo 1462551 3291137 := bstep (se 2 (by rfl) ⟨1234176, by rfl⟩ : syracuseStep 3291137 = 2468353) B2468353
theorem B1464331 : Blo 1462551 1464331 := bstep (se 1 (by rfl) ⟨1098248, by rfl⟩ : syracuseStep 1464331 = 2196497) B2196497
theorem B6248465 : Blo 1462551 6248465 := bstep (se 2 (by rfl) ⟨2343174, by rfl⟩ : syracuseStep 6248465 = 4686349) B4686349
theorem B1464343 : Blo 1462551 1464343 := bstep (se 1 (by rfl) ⟨1098257, by rfl⟩ : syracuseStep 1464343 = 2196515) B2196515
theorem B1464363 : Blo 1462551 1464363 := bstep (se 1 (by rfl) ⟨1098272, by rfl⟩ : syracuseStep 1464363 = 2196545) B2196545
theorem B1464375 : Blo 1462551 1464375 := bstep (se 1 (by rfl) ⟨1098281, by rfl⟩ : syracuseStep 1464375 = 2196563) B2196563
theorem B24074309 : Blo 1462551 24074309 := bstep (se 4 (by rfl) ⟨2256966, by rfl⟩ : syracuseStep 24074309 = 4513933) B4513933
theorem B1464395 : Blo 1462551 1464395 := bstep (se 1 (by rfl) ⟨1098296, by rfl⟩ : syracuseStep 1464395 = 2196593) B2196593
theorem B1464407 : Blo 1462551 1464407 := bstep (se 1 (by rfl) ⟨1098305, by rfl⟩ : syracuseStep 1464407 = 2196611) B2196611
theorem B1464427 : Blo 1462551 1464427 := bstep (se 1 (by rfl) ⟨1098320, by rfl⟩ : syracuseStep 1464427 = 2196641) B2196641
theorem B1464439 : Blo 1462551 1464439 := bstep (se 1 (by rfl) ⟨1098329, by rfl⟩ : syracuseStep 1464439 = 2196659) B2196659
theorem B1464459 : Blo 1462551 1464459 := bstep (se 1 (by rfl) ⟨1098344, by rfl⟩ : syracuseStep 1464459 = 2196689) B2196689
theorem B1464471 : Blo 1462551 1464471 := bstep (se 1 (by rfl) ⟨1098353, by rfl⟩ : syracuseStep 1464471 = 2196707) B2196707
theorem B1464491 : Blo 1462551 1464491 := bstep (se 1 (by rfl) ⟨1098368, by rfl⟩ : syracuseStep 1464491 = 2196737) B2196737
theorem B1464503 : Blo 1462551 1464503 := bstep (se 1 (by rfl) ⟨1098377, by rfl⟩ : syracuseStep 1464503 = 2196755) B2196755
theorem B4937921 : Blo 1462551 4937921 := bstep (se 2 (by rfl) ⟨1851720, by rfl⟩ : syracuseStep 4937921 = 3703441) B3703441
theorem B2816203 : Blo 1462551 2816203 := bstep (se 1 (by rfl) ⟨2112152, by rfl⟩ : syracuseStep 2816203 = 4224305) B4224305
theorem B1464523 : Blo 1462551 1464523 := bstep (se 1 (by rfl) ⟨1098392, by rfl⟩ : syracuseStep 1464523 = 2196785) B2196785
theorem B1464535 : Blo 1462551 1464535 := bstep (se 1 (by rfl) ⟨1098401, by rfl⟩ : syracuseStep 1464535 = 2196803) B2196803
theorem B3291353 : Blo 1462551 3291353 := bstep (se 2 (by rfl) ⟨1234257, by rfl⟩ : syracuseStep 3291353 = 2468515) B2468515
theorem B3127513 : Blo 1462551 3127513 := bstep (se 2 (by rfl) ⟨1172817, by rfl⟩ : syracuseStep 3127513 = 2345635) B2345635
theorem B7411985 : Blo 1462551 7411985 := bstep (se 2 (by rfl) ⟨2779494, by rfl⟩ : syracuseStep 7411985 = 5558989) B5558989
theorem B3291443 : Blo 1462551 3291443 := bstep (se 1 (by rfl) ⟨2468582, by rfl⟩ : syracuseStep 3291443 = 4937165) B4937165
theorem B3291479 : Blo 1462551 3291479 := bstep (se 1 (by rfl) ⟨2468609, by rfl⟩ : syracuseStep 3291479 = 4937219) B4937219
theorem B5560721 : Blo 1462551 5560721 := bstep (se 2 (by rfl) ⟨2085270, by rfl⟩ : syracuseStep 5560721 = 4170541) B4170541
theorem B7412147 : Blo 1462551 7412147 := bstep (se 1 (by rfl) ⟨5559110, by rfl⟩ : syracuseStep 7412147 = 11118221) B11118221
theorem B2193881 : Blo 1462551 2193881 := bstep (se 2 (by rfl) ⟨822705, by rfl⟩ : syracuseStep 2193881 = 1645411) B1645411
theorem B3291659 : Blo 1462551 3291659 := bstep (se 1 (by rfl) ⟨2468744, by rfl⟩ : syracuseStep 3291659 = 4937489) B4937489
theorem B8337937 : Blo 1462551 8337937 := bstep (se 2 (by rfl) ⟨3126726, by rfl⟩ : syracuseStep 8337937 = 6253453) B6253453
theorem B3291713 : Blo 1462551 3291713 := bstep (se 2 (by rfl) ⟨1234392, by rfl⟩ : syracuseStep 3291713 = 2468785) B2468785
theorem B2193995 : Blo 1462551 2193995 := bstep (se 1 (by rfl) ⟨1645496, by rfl⟩ : syracuseStep 2193995 = 3290993) B3290993
theorem B2194007 : Blo 1462551 2194007 := bstep (se 1 (by rfl) ⟨1645505, by rfl⟩ : syracuseStep 2194007 = 3291011) B3291011
theorem B2194073 : Blo 1462551 2194073 := bstep (se 2 (by rfl) ⟨822777, by rfl⟩ : syracuseStep 2194073 = 1645555) B1645555
theorem B4938461 : Blo 1462551 4938461 := bstep (se 3 (by rfl) ⟨925961, by rfl⟩ : syracuseStep 4938461 = 1851923) B1851923
theorem B2194187 : Blo 1462551 2194187 := bstep (se 1 (by rfl) ⟨1645640, by rfl⟩ : syracuseStep 2194187 = 3291281) B3291281
theorem B2194199 : Blo 1462551 2194199 := bstep (se 1 (by rfl) ⟨1645649, by rfl⟩ : syracuseStep 2194199 = 3291299) B3291299
theorem B5274391 : Blo 1462551 5274391 := bstep (se 1 (by rfl) ⟨3955793, by rfl⟩ : syracuseStep 5274391 = 7911587) B7911587
theorem B3291929 : Blo 1462551 3291929 := bstep (se 2 (by rfl) ⟨1234473, by rfl⟩ : syracuseStep 3291929 = 2468947) B2468947
theorem B4168513 : Blo 1462551 4168513 := bstep (se 2 (by rfl) ⟨1563192, by rfl⟩ : syracuseStep 4168513 = 3126385) B3126385
theorem B2194265 : Blo 1462551 2194265 := bstep (se 2 (by rfl) ⟨822849, by rfl⟩ : syracuseStep 2194265 = 1645699) B1645699
theorem B3292019 : Blo 1462551 3292019 := bstep (se 1 (by rfl) ⟨2469014, by rfl⟩ : syracuseStep 3292019 = 4938029) B4938029
theorem B3292055 : Blo 1462551 3292055 := bstep (se 1 (by rfl) ⟨2469041, by rfl⟩ : syracuseStep 3292055 = 4938083) B4938083
theorem B1645483 : Blo 1462551 1645483 := bstep (se 1 (by rfl) ⟨1234112, by rfl⟩ : syracuseStep 1645483 = 2468225) B2468225
theorem B2194379 : Blo 1462551 2194379 := bstep (se 1 (by rfl) ⟨1645784, by rfl⟩ : syracuseStep 2194379 = 3291569) B3291569
theorem B2194391 : Blo 1462551 2194391 := bstep (se 1 (by rfl) ⟨1645793, by rfl⟩ : syracuseStep 2194391 = 3291587) B3291587
theorem B1645591 : Blo 1462551 1645591 := bstep (se 1 (by rfl) ⟨1234193, by rfl⟩ : syracuseStep 1645591 = 2468387) B2468387
theorem B1563671 : Blo 1462551 1563671 := bstep (se 1 (by rfl) ⟨1172753, by rfl⟩ : syracuseStep 1563671 = 2345507) B2345507
theorem B2194457 : Blo 1462551 2194457 := bstep (se 2 (by rfl) ⟨822921, by rfl⟩ : syracuseStep 2194457 = 1645843) B1645843
theorem B3292235 : Blo 1462551 3292235 := bstep (se 1 (by rfl) ⟨2469176, by rfl⟩ : syracuseStep 3292235 = 4938353) B4938353
theorem B3292289 : Blo 1462551 3292289 := bstep (se 2 (by rfl) ⟨1234608, by rfl⟩ : syracuseStep 3292289 = 2469217) B2469217
theorem B2194571 : Blo 1462551 2194571 := bstep (se 1 (by rfl) ⟨1645928, by rfl⟩ : syracuseStep 2194571 = 3291857) B3291857
theorem B2006155 : Blo 1462551 2006155 := bstep (se 1 (by rfl) ⟨1504616, by rfl⟩ : syracuseStep 2006155 = 3009233) B3009233
theorem B7404695 : Blo 1462551 7404695 := bstep (se 1 (by rfl) ⟨5553521, by rfl⟩ : syracuseStep 7404695 = 11107043) B11107043
theorem B2194583 : Blo 1462551 2194583 := bstep (se 1 (by rfl) ⟨1645937, by rfl⟩ : syracuseStep 2194583 = 3291875) B3291875
theorem B1645771 : Blo 1462551 1645771 := bstep (se 1 (by rfl) ⟨1234328, by rfl⟩ : syracuseStep 1645771 = 2468657) B2468657
theorem B2194649 : Blo 1462551 2194649 := bstep (se 2 (by rfl) ⟨822993, by rfl⟩ : syracuseStep 2194649 = 1645987) B1645987
theorem B5553431 : Blo 1462551 5553431 := bstep (se 1 (by rfl) ⟨4165073, by rfl⟩ : syracuseStep 5553431 = 8330147) B8330147
theorem B1645879 : Blo 1462551 1645879 := bstep (se 1 (by rfl) ⟨1234409, by rfl⟩ : syracuseStep 1645879 = 2468819) B2468819
theorem B2194763 : Blo 1462551 2194763 := bstep (se 1 (by rfl) ⟨1646072, by rfl⟩ : syracuseStep 2194763 = 3292145) B3292145
theorem B2194775 : Blo 1462551 2194775 := bstep (se 1 (by rfl) ⟨1646081, by rfl⟩ : syracuseStep 2194775 = 3292163) B3292163
theorem B3292505 : Blo 1462551 3292505 := bstep (se 2 (by rfl) ⟨1234689, by rfl⟩ : syracuseStep 3292505 = 2469379) B2469379
theorem B7036253 : Blo 1462551 7036253 := bstep (se 3 (by rfl) ⟨1319297, by rfl⟩ : syracuseStep 7036253 = 2638595) B2638595
theorem B8330647 : Blo 1462551 8330647 := bstep (se 1 (by rfl) ⟨6247985, by rfl⟩ : syracuseStep 8330647 = 12495971) B12495971
theorem B2194841 : Blo 1462551 2194841 := bstep (se 2 (by rfl) ⟨823065, by rfl⟩ : syracuseStep 2194841 = 1646131) B1646131
theorem B3292595 : Blo 1462551 3292595 := bstep (se 1 (by rfl) ⟨2469446, by rfl⟩ : syracuseStep 3292595 = 4938893) B4938893
theorem B13360589 : Blo 1462551 13360589 := bstep (se 3 (by rfl) ⟨2505110, by rfl⟩ : syracuseStep 13360589 = 5010221) B5010221
theorem B3292631 : Blo 1462551 3292631 := bstep (se 1 (by rfl) ⟨2469473, by rfl⟩ : syracuseStep 3292631 = 4938947) B4938947
theorem B5553629 : Blo 1462551 5553629 := bstep (se 3 (by rfl) ⟨1041305, by rfl⟩ : syracuseStep 5553629 = 2082611) B2082611
theorem B1646059 : Blo 1462551 1646059 := bstep (se 1 (by rfl) ⟨1234544, by rfl⟩ : syracuseStep 1646059 = 2469089) B2469089
theorem B2194955 : Blo 1462551 2194955 := bstep (se 1 (by rfl) ⟨1646216, by rfl⟩ : syracuseStep 2194955 = 3292433) B3292433
theorem B2194967 : Blo 1462551 2194967 := bstep (se 1 (by rfl) ⟨1646225, by rfl⟩ : syracuseStep 2194967 = 3292451) B3292451
theorem B1646167 : Blo 1462551 1646167 := bstep (se 1 (by rfl) ⟨1234625, by rfl⟩ : syracuseStep 1646167 = 2469251) B2469251
theorem B2195033 : Blo 1462551 2195033 := bstep (se 2 (by rfl) ⟨823137, by rfl⟩ : syracuseStep 2195033 = 1646275) B1646275
theorem B53395037 : Blo 1462551 53395037 := bstep (se 3 (by rfl) ⟨10011569, by rfl⟩ : syracuseStep 53395037 = 20023139) B20023139
theorem B85532273 : Blo 1462551 85532273 := bstep (se 2 (by rfl) ⟨32074602, by rfl⟩ : syracuseStep 85532273 = 64149205) B64149205
theorem B3292811 : Blo 1462551 3292811 := bstep (se 1 (by rfl) ⟨2469608, by rfl⟩ : syracuseStep 3292811 = 4939217) B4939217
theorem B3292865 : Blo 1462551 3292865 := bstep (se 2 (by rfl) ⟨1234824, by rfl⟩ : syracuseStep 3292865 = 2469649) B2469649
theorem B2195147 : Blo 1462551 2195147 := bstep (se 1 (by rfl) ⟨1646360, by rfl⟩ : syracuseStep 2195147 = 3292721) B3292721
theorem B2195159 : Blo 1462551 2195159 := bstep (se 1 (by rfl) ⟨1646369, by rfl⟩ : syracuseStep 2195159 = 3292739) B3292739
theorem B1646347 : Blo 1462551 1646347 := bstep (se 1 (by rfl) ⟨1234760, by rfl⟩ : syracuseStep 1646347 = 2469521) B2469521
theorem B2195225 : Blo 1462551 2195225 := bstep (se 2 (by rfl) ⟨823209, by rfl⟩ : syracuseStep 2195225 = 1646419) B1646419
theorem B4939595 : Blo 1462551 4939595 := bstep (se 1 (by rfl) ⟨3704696, by rfl⟩ : syracuseStep 4939595 = 7409393) B7409393
theorem B1646455 : Blo 1462551 1646455 := bstep (se 1 (by rfl) ⟨1234841, by rfl⟩ : syracuseStep 1646455 = 2469683) B2469683
theorem B1851275 : Blo 1462551 1851275 := bstep (se 1 (by rfl) ⟨1388456, by rfl⟩ : syracuseStep 1851275 = 2776913) B2776913
theorem B2195339 : Blo 1462551 2195339 := bstep (se 1 (by rfl) ⟨1646504, by rfl⟩ : syracuseStep 2195339 = 3293009) B3293009
theorem B2195351 : Blo 1462551 2195351 := bstep (se 1 (by rfl) ⟨1646513, by rfl⟩ : syracuseStep 2195351 = 3293027) B3293027
theorem B3293081 : Blo 1462551 3293081 := bstep (se 2 (by rfl) ⟨1234905, by rfl⟩ : syracuseStep 3293081 = 2469811) B2469811
theorem B2195417 : Blo 1462551 2195417 := bstep (se 2 (by rfl) ⟨823281, by rfl⟩ : syracuseStep 2195417 = 1646563) B1646563
theorem B3293171 : Blo 1462551 3293171 := bstep (se 1 (by rfl) ⟨2469878, by rfl⟩ : syracuseStep 3293171 = 4939757) B4939757
theorem B8019971 : Blo 1462551 8019971 := bstep (se 1 (by rfl) ⟨6014978, by rfl⟩ : syracuseStep 8019971 = 12029957) B12029957
theorem B1646599 : Blo 1462551 1646599 := bstep (se 1 (by rfl) ⟨1234949, by rfl⟩ : syracuseStep 1646599 = 2469899) B2469899
theorem B2195471 : Blo 1462551 2195471 := bstep (se 1 (by rfl) ⟨1646603, by rfl⟩ : syracuseStep 2195471 = 3293207) B3293207
theorem B2195513 : Blo 1462551 2195513 := bstep (se 2 (by rfl) ⟨823317, by rfl⟩ : syracuseStep 2195513 = 1646635) B1646635
theorem B3293243 : Blo 1462551 3293243 := bstep (se 1 (by rfl) ⟨2469932, by rfl⟩ : syracuseStep 3293243 = 4939865) B4939865
theorem B4169789 : Blo 1462551 4169789 := bstep (se 3 (by rfl) ⟨781835, by rfl⟩ : syracuseStep 4169789 = 1563671) B1563671
theorem B6250583 : Blo 1462551 6250583 := bstep (se 1 (by rfl) ⟨4687937, by rfl⟩ : syracuseStep 6250583 = 9375875) B9375875
theorem B2195591 : Blo 1462551 2195591 := bstep (se 1 (by rfl) ⟨1646693, by rfl⟩ : syracuseStep 2195591 = 3293387) B3293387
theorem B2195627 : Blo 1462551 2195627 := bstep (se 1 (by rfl) ⟨1646720, by rfl⟩ : syracuseStep 2195627 = 3293441) B3293441
theorem B7913645 : Blo 1462551 7913645 := bstep (se 3 (by rfl) ⟨1483808, by rfl⟩ : syracuseStep 7913645 = 2967617) B2967617
theorem B3293369 : Blo 1462551 3293369 := bstep (se 2 (by rfl) ⟨1235013, by rfl⟩ : syracuseStep 3293369 = 2470027) B2470027
theorem B1646779 : Blo 1462551 1646779 := bstep (se 1 (by rfl) ⟨1235084, by rfl⟩ : syracuseStep 1646779 = 2470169) B2470169
theorem B2195657 : Blo 1462551 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B5554433 : Blo 1462551 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B1851655 : Blo 1462551 1851655 := bstep (se 1 (by rfl) ⟨1388741, by rfl⟩ : syracuseStep 1851655 = 2777483) B2777483
theorem B4170017 : Blo 1462551 4170017 := bstep (se 2 (by rfl) ⟨1563756, by rfl⟩ : syracuseStep 4170017 = 3127513) B3127513
theorem B2195771 : Blo 1462551 2195771 := bstep (se 1 (by rfl) ⟨1646828, by rfl⟩ : syracuseStep 2195771 = 3293657) B3293657
theorem B2195831 : Blo 1462551 2195831 := bstep (se 1 (by rfl) ⟨1646873, by rfl⟩ : syracuseStep 2195831 = 3293747) B3293747
theorem B2195855 : Blo 1462551 2195855 := bstep (se 1 (by rfl) ⟨1646891, by rfl⟩ : syracuseStep 2195855 = 3293783) B3293783
theorem B7029139 : Blo 1462551 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B2195897 : Blo 1462551 2195897 := bstep (se 2 (by rfl) ⟨823461, by rfl⟩ : syracuseStep 2195897 = 1646923) B1646923
theorem B8339921 : Blo 1462551 8339921 := bstep (se 2 (by rfl) ⟨3127470, by rfl⟩ : syracuseStep 8339921 = 6254941) B6254941
theorem B2195975 : Blo 1462551 2195975 := bstep (se 1 (by rfl) ⟨1646981, by rfl⟩ : syracuseStep 2195975 = 3293963) B3293963
theorem B3293711 : Blo 1462551 3293711 := bstep (se 1 (by rfl) ⟨2470283, by rfl⟩ : syracuseStep 3293711 = 4940567) B4940567
theorem B3293729 : Blo 1462551 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B2196011 : Blo 1462551 2196011 := bstep (se 1 (by rfl) ⟨1647008, by rfl⟩ : syracuseStep 2196011 = 3294017) B3294017
theorem B2196041 : Blo 1462551 2196041 := bstep (se 2 (by rfl) ⟨823515, by rfl⟩ : syracuseStep 2196041 = 1647031) B1647031
theorem B4170359 : Blo 1462551 4170359 := bstep (se 1 (by rfl) ⟨3127769, by rfl⟩ : syracuseStep 4170359 = 6255539) B6255539
theorem B2343559 : Blo 1462551 2343559 := bstep (se 1 (by rfl) ⟨1757669, by rfl⟩ : syracuseStep 2343559 = 3515339) B3515339
theorem B1647247 : Blo 1462551 1647247 := bstep (se 1 (by rfl) ⟨1235435, by rfl⟩ : syracuseStep 1647247 = 2470871) B2470871
theorem B1852075 : Blo 1462551 1852075 := bstep (se 1 (by rfl) ⟨1389056, by rfl⟩ : syracuseStep 1852075 = 2778113) B2778113
theorem B2196155 : Blo 1462551 2196155 := bstep (se 1 (by rfl) ⟨1647116, by rfl⟩ : syracuseStep 2196155 = 3294233) B3294233
theorem B11117249 : Blo 1462551 11117249 := bstep (se 2 (by rfl) ⟨4168968, by rfl⟩ : syracuseStep 11117249 = 8337937) B8337937
theorem B5554889 : Blo 1462551 5554889 := bstep (se 2 (by rfl) ⟨2083083, by rfl⟩ : syracuseStep 5554889 = 4166167) B4166167
theorem B2196215 : Blo 1462551 2196215 := bstep (se 1 (by rfl) ⟨1647161, by rfl⟩ : syracuseStep 2196215 = 3294323) B3294323
theorem B3703553 : Blo 1462551 3703553 := bstep (se 2 (by rfl) ⟨1388832, by rfl⟩ : syracuseStep 3703553 = 2777665) B2777665
theorem B3515147 : Blo 1462551 3515147 := bstep (se 1 (by rfl) ⟨2636360, by rfl⟩ : syracuseStep 3515147 = 5272721) B5272721
theorem B2196239 : Blo 1462551 2196239 := bstep (se 1 (by rfl) ⟨1647179, by rfl⟩ : syracuseStep 2196239 = 3294359) B3294359
theorem B2196281 : Blo 1462551 2196281 := bstep (se 2 (by rfl) ⟨823605, by rfl⟩ : syracuseStep 2196281 = 1647211) B1647211
theorem B2777915 : Blo 1462551 2777915 := bstep (se 1 (by rfl) ⟨2083436, by rfl⟩ : syracuseStep 2777915 = 4166873) B4166873
theorem B4686707 : Blo 1462551 4686707 := bstep (se 1 (by rfl) ⟨3515030, by rfl⟩ : syracuseStep 4686707 = 7030061) B7030061
theorem B3294071 : Blo 1462551 3294071 := bstep (se 1 (by rfl) ⟨2470553, by rfl⟩ : syracuseStep 3294071 = 4941107) B4941107
theorem B2196359 : Blo 1462551 2196359 := bstep (se 1 (by rfl) ⟨1647269, by rfl⟩ : syracuseStep 2196359 = 3294539) B3294539
theorem B1852303 : Blo 1462551 1852303 := bstep (se 1 (by rfl) ⟨1389227, by rfl⟩ : syracuseStep 1852303 = 2778455) B2778455
theorem B2196395 : Blo 1462551 2196395 := bstep (se 1 (by rfl) ⟨1647296, by rfl⟩ : syracuseStep 2196395 = 3294593) B3294593
theorem B4940729 : Blo 1462551 4940729 := bstep (se 2 (by rfl) ⟨1852773, by rfl⟩ : syracuseStep 4940729 = 3705547) B3705547
theorem B2196425 : Blo 1462551 2196425 := bstep (se 2 (by rfl) ⟨823659, by rfl⟩ : syracuseStep 2196425 = 1647319) B1647319
theorem B3294251 : Blo 1462551 3294251 := bstep (se 1 (by rfl) ⟨2470688, by rfl⟩ : syracuseStep 3294251 = 4941377) B4941377
theorem B2343995 : Blo 1462551 2343995 := bstep (se 1 (by rfl) ⟨1757996, by rfl⟩ : syracuseStep 2343995 = 3515993) B3515993
theorem B2196539 : Blo 1462551 2196539 := bstep (se 1 (by rfl) ⟨1647404, by rfl⟩ : syracuseStep 2196539 = 3294809) B3294809
theorem B8905789 : Blo 1462551 8905789 := bstep (se 3 (by rfl) ⟨1669835, by rfl⟩ : syracuseStep 8905789 = 3339671) B3339671
theorem B3703927 : Blo 1462551 3703927 := bstep (se 1 (by rfl) ⟨2777945, by rfl⟩ : syracuseStep 3703927 = 5555891) B5555891
theorem B2196599 : Blo 1462551 2196599 := bstep (se 1 (by rfl) ⟨1647449, by rfl⟩ : syracuseStep 2196599 = 3294899) B3294899
theorem B2196623 : Blo 1462551 2196623 := bstep (se 1 (by rfl) ⟨1647467, by rfl⟩ : syracuseStep 2196623 = 3294935) B3294935
theorem B2196665 : Blo 1462551 2196665 := bstep (se 2 (by rfl) ⟨823749, by rfl⟩ : syracuseStep 2196665 = 1647499) B1647499
theorem B21374189 : Blo 1462551 21374189 := bstep (se 3 (by rfl) ⟨4007660, by rfl⟩ : syracuseStep 21374189 = 8015321) B8015321
theorem B2196743 : Blo 1462551 2196743 := bstep (se 1 (by rfl) ⟨1647557, by rfl⟩ : syracuseStep 2196743 = 3295115) B3295115
theorem B2778401 : Blo 1462551 2778401 := bstep (se 2 (by rfl) ⟨1041900, by rfl⟩ : syracuseStep 2778401 = 2083801) B2083801
theorem B2196779 : Blo 1462551 2196779 := bstep (se 1 (by rfl) ⟨1647584, by rfl⟩ : syracuseStep 2196779 = 3295169) B3295169
theorem B2196809 : Blo 1462551 2196809 := bstep (se 2 (by rfl) ⟨823803, by rfl⟩ : syracuseStep 2196809 = 1647607) B1647607
theorem B7406963 : Blo 1462551 7406963 := bstep (se 1 (by rfl) ⟨5555222, by rfl⟩ : syracuseStep 7406963 = 11110445) B11110445
theorem B16049539 : Blo 1462551 16049539 := bstep (se 1 (by rfl) ⟨12037154, by rfl⟩ : syracuseStep 16049539 = 24074309) B24074309
theorem B3294611 : Blo 1462551 3294611 := bstep (se 1 (by rfl) ⟨2470958, by rfl⟩ : syracuseStep 3294611 = 4941917) B4941917
theorem B2778553 : Blo 1462551 2778553 := bstep (se 2 (by rfl) ⟨1041957, by rfl⟩ : syracuseStep 2778553 = 2083915) B2083915
theorem B3294665 : Blo 1462551 3294665 := bstep (se 2 (by rfl) ⟨1235499, by rfl⟩ : syracuseStep 3294665 = 2470999) B2470999
theorem B3958217 : Blo 1462551 3958217 := bstep (se 2 (by rfl) ⟨1484331, by rfl⟩ : syracuseStep 3958217 = 2968663) B2968663
theorem B4941323 : Blo 1462551 4941323 := bstep (se 1 (by rfl) ⟨3705992, by rfl⟩ : syracuseStep 4941323 = 7411985) B7411985
theorem B3704363 : Blo 1462551 3704363 := bstep (se 1 (by rfl) ⟨2778272, by rfl⟩ : syracuseStep 3704363 = 5556545) B5556545
theorem B4941431 : Blo 1462551 4941431 := bstep (se 1 (by rfl) ⟨3706073, by rfl⟩ : syracuseStep 4941431 = 7412147) B7412147
theorem B1853047 : Blo 1462551 1853047 := bstep (se 1 (by rfl) ⟨1389785, by rfl⟩ : syracuseStep 1853047 = 2779571) B2779571
theorem B2967187 : Blo 1462551 2967187 := bstep (se 1 (by rfl) ⟨2225390, by rfl⟩ : syracuseStep 2967187 = 4450781) B4450781
theorem B15828709 : Blo 1462551 15828709 := bstep (se 4 (by rfl) ⟨1483941, by rfl⟩ : syracuseStep 15828709 = 2967883) B2967883
theorem B7407449 : Blo 1462551 7407449 := bstep (se 2 (by rfl) ⟨2777793, by rfl⟩ : syracuseStep 7407449 = 5555587) B5555587
theorem B1853371 : Blo 1462551 1853371 := bstep (se 1 (by rfl) ⟨1390028, by rfl⟩ : syracuseStep 1853371 = 2780057) B2780057
theorem B6252497 : Blo 1462551 6252497 := bstep (se 2 (by rfl) ⟨2344686, by rfl⟩ : syracuseStep 6252497 = 4689373) B4689373
theorem B3565601 : Blo 1462551 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B7030871 : Blo 1462551 7030871 := bstep (se 1 (by rfl) ⟨5273153, by rfl⟩ : syracuseStep 7030871 = 10546307) B10546307
theorem B28117165 : Blo 1462551 28117165 := bstep (se 3 (by rfl) ⟨5271968, by rfl⟩ : syracuseStep 28117165 = 10543937) B10543937
theorem B28141769 : Blo 1462551 28141769 := bstep (se 2 (by rfl) ⟨10553163, by rfl⟩ : syracuseStep 28141769 = 21106327) B21106327
theorem B4942025 : Blo 1462551 4942025 := bstep (se 2 (by rfl) ⟨1853259, by rfl⟩ : syracuseStep 4942025 = 3706519) B3706519
theorem B8907059 : Blo 1462551 8907059 := bstep (se 1 (by rfl) ⟨6680294, by rfl⟩ : syracuseStep 8907059 = 13360589) B13360589
theorem B3705203 : Blo 1462551 3705203 := bstep (se 1 (by rfl) ⟨2778902, by rfl⟩ : syracuseStep 3705203 = 5557805) B5557805
theorem B3705223 : Blo 1462551 3705223 := bstep (se 1 (by rfl) ⟨2778917, by rfl⟩ : syracuseStep 3705223 = 5557835) B5557835
theorem B35596691 : Blo 1462551 35596691 := bstep (se 1 (by rfl) ⟨26697518, by rfl⟩ : syracuseStep 35596691 = 53395037) B53395037
theorem B5933465 : Blo 1462551 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B3008969 : Blo 1462551 3008969 := bstep (se 2 (by rfl) ⟨1128363, by rfl⟩ : syracuseStep 3008969 = 2256727) B2256727
theorem B7129565 : Blo 1462551 7129565 := bstep (se 3 (by rfl) ⟨1336793, by rfl⟩ : syracuseStep 7129565 = 2673587) B2673587
theorem B4450877 : Blo 1462551 4450877 := bstep (se 3 (by rfl) ⟨834539, by rfl⟩ : syracuseStep 4450877 = 1669079) B1669079
theorem B10553975 : Blo 1462551 10553975 := bstep (se 1 (by rfl) ⟨7915481, by rfl⟩ : syracuseStep 10553975 = 15830963) B15830963
theorem B3705497 : Blo 1462551 3705497 := bstep (se 2 (by rfl) ⟨1389561, by rfl⟩ : syracuseStep 3705497 = 2779123) B2779123
theorem B2468623 : Blo 1462551 2468623 := bstep (se 1 (by rfl) ⟨1851467, by rfl⟩ : syracuseStep 2468623 = 3702935) B3702935
theorem B25340687 : Blo 1462551 25340687 := bstep (se 1 (by rfl) ⟨19005515, by rfl⟩ : syracuseStep 25340687 = 38011031) B38011031
theorem B3705659 : Blo 1462551 3705659 := bstep (se 1 (by rfl) ⟨2779244, by rfl⟩ : syracuseStep 3705659 = 5558489) B5558489
theorem B4942727 : Blo 1462551 4942727 := bstep (se 1 (by rfl) ⟨3707045, by rfl⟩ : syracuseStep 4942727 = 7414091) B7414091
theorem B16673687 : Blo 1462551 16673687 := bstep (se 1 (by rfl) ⟨12505265, by rfl⟩ : syracuseStep 16673687 = 25010531) B25010531
theorem B3754937 : Blo 1462551 3754937 := bstep (se 2 (by rfl) ⟨1408101, by rfl⟩ : syracuseStep 3754937 = 2816203) B2816203
theorem B42224651 : Blo 1462551 42224651 := bstep (se 1 (by rfl) ⟨31668488, by rfl⟩ : syracuseStep 42224651 = 63336977) B63336977
theorem B3705871 : Blo 1462551 3705871 := bstep (se 1 (by rfl) ⟨2779403, by rfl⟩ : syracuseStep 3705871 = 5558807) B5558807
theorem B2968591 : Blo 1462551 2968591 := bstep (se 1 (by rfl) ⟨2226443, by rfl⟩ : syracuseStep 2968591 = 4452887) B4452887
theorem B2780345 : Blo 1462551 2780345 := bstep (se 2 (by rfl) ⟨1042629, by rfl⟩ : syracuseStep 2780345 = 2085259) B2085259
theorem B3706145 : Blo 1462551 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B2469163 : Blo 1462551 2469163 := bstep (se 1 (by rfl) ⟨1851872, by rfl⟩ : syracuseStep 2469163 = 3703745) B3703745
theorem B4164983 : Blo 1462551 4164983 := bstep (se 1 (by rfl) ⟨3123737, by rfl⟩ : syracuseStep 4164983 = 6247475) B6247475
theorem B2469305 : Blo 1462551 2469305 := bstep (se 2 (by rfl) ⟨925989, by rfl⟩ : syracuseStep 2469305 = 1851979) B1851979
theorem B8335021 : Blo 1462551 8335021 := bstep (se 3 (by rfl) ⟨1562816, by rfl⟩ : syracuseStep 8335021 = 3125633) B3125633
theorem B9506497 : Blo 1462551 9506497 := bstep (se 2 (by rfl) ⟨3564936, by rfl⟩ : syracuseStep 9506497 = 7129873) B7129873
theorem B7032521 : Blo 1462551 7032521 := bstep (se 2 (by rfl) ⟨2637195, by rfl⟩ : syracuseStep 7032521 = 5274391) B5274391
theorem B30437093 : Blo 1462551 30437093 := bstep (se 4 (by rfl) ⟨2853477, by rfl⟩ : syracuseStep 30437093 = 5706955) B5706955
theorem B5558017 : Blo 1462551 5558017 := bstep (se 2 (by rfl) ⟨2084256, by rfl⟩ : syracuseStep 5558017 = 4168513) B4168513
theorem B15830873 : Blo 1462551 15830873 := bstep (se 2 (by rfl) ⟨5936577, by rfl⟩ : syracuseStep 15830873 = 11873155) B11873155
theorem B7409555 : Blo 1462551 7409555 := bstep (se 1 (by rfl) ⟨5557166, by rfl⟩ : syracuseStep 7409555 = 11114333) B11114333
theorem B228003761 : Blo 1462551 228003761 := bstep (se 2 (by rfl) ⟨85501410, by rfl⟩ : syracuseStep 228003761 = 171002821) B171002821
theorem B4165643 : Blo 1462551 4165643 := bstep (se 1 (by rfl) ⟨3124232, by rfl⟩ : syracuseStep 4165643 = 6248465) B6248465
theorem B11120651 : Blo 1462551 11120651 := bstep (se 1 (by rfl) ⟨8340488, by rfl⟩ : syracuseStep 11120651 = 16680977) B16680977
theorem B2470007 : Blo 1462551 2470007 := bstep (se 1 (by rfl) ⟨1852505, by rfl⟩ : syracuseStep 2470007 = 3705011) B3705011
theorem B2674873 : Blo 1462551 2674873 := bstep (se 2 (by rfl) ⟨1003077, by rfl⟩ : syracuseStep 2674873 = 2006155) B2006155
theorem B11866313 : Blo 1462551 11866313 := bstep (se 2 (by rfl) ⟨4449867, by rfl⟩ : syracuseStep 11866313 = 8899735) B8899735
theorem B3707147 : Blo 1462551 3707147 := bstep (se 1 (by rfl) ⟨2780360, by rfl⟩ : syracuseStep 3707147 = 5560721) B5560721
theorem B1462587 : Blo 1462551 1462587 := bstep (se 1 (by rfl) ⟨1096940, by rfl⟩ : syracuseStep 1462587 = 2193881) B2193881
theorem B1462663 : Blo 1462551 1462663 := bstep (se 1 (by rfl) ⟨1096997, by rfl⟩ : syracuseStep 1462663 = 2193995) B2193995
theorem B1462671 : Blo 1462551 1462671 := bstep (se 1 (by rfl) ⟨1097003, by rfl⟩ : syracuseStep 1462671 = 2194007) B2194007
theorem B1462715 : Blo 1462551 1462715 := bstep (se 1 (by rfl) ⟨1097036, by rfl⟩ : syracuseStep 1462715 = 2194073) B2194073
theorem B14062045 : Blo 1462551 14062045 := bstep (se 3 (by rfl) ⟨2636633, by rfl⟩ : syracuseStep 14062045 = 5273267) B5273267
theorem B1462791 : Blo 1462551 1462791 := bstep (se 1 (by rfl) ⟨1097093, by rfl⟩ : syracuseStep 1462791 = 2194187) B2194187
theorem B1462799 : Blo 1462551 1462799 := bstep (se 1 (by rfl) ⟨1097099, by rfl⟩ : syracuseStep 1462799 = 2194199) B2194199
theorem B1462843 : Blo 1462551 1462843 := bstep (se 1 (by rfl) ⟨1097132, by rfl⟩ : syracuseStep 1462843 = 2194265) B2194265
theorem B2470459 : Blo 1462551 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B1462919 : Blo 1462551 1462919 := bstep (se 1 (by rfl) ⟨1097189, by rfl⟩ : syracuseStep 1462919 = 2194379) B2194379
theorem B1462927 : Blo 1462551 1462927 := bstep (se 1 (by rfl) ⟨1097195, by rfl⟩ : syracuseStep 1462927 = 2194391) B2194391
theorem B1462971 : Blo 1462551 1462971 := bstep (se 1 (by rfl) ⟨1097228, by rfl⟩ : syracuseStep 1462971 = 2194457) B2194457
theorem B2470601 : Blo 1462551 2470601 := bstep (se 2 (by rfl) ⟨926475, by rfl⟩ : syracuseStep 2470601 = 1852951) B1852951
theorem B1463047 : Blo 1462551 1463047 := bstep (se 1 (by rfl) ⟨1097285, by rfl⟩ : syracuseStep 1463047 = 2194571) B2194571
theorem B4936463 : Blo 1462551 4936463 := bstep (se 1 (by rfl) ⟨3702347, by rfl⟩ : syracuseStep 4936463 = 7404695) B7404695
theorem B1463055 : Blo 1462551 1463055 := bstep (se 1 (by rfl) ⟨1097291, by rfl⟩ : syracuseStep 1463055 = 2194583) B2194583
theorem B12677903 : Blo 1462551 12677903 := bstep (se 1 (by rfl) ⟨9508427, by rfl⟩ : syracuseStep 12677903 = 19016855) B19016855
theorem B1463099 : Blo 1462551 1463099 := bstep (se 1 (by rfl) ⟨1097324, by rfl⟩ : syracuseStep 1463099 = 2194649) B2194649
theorem B1463175 : Blo 1462551 1463175 := bstep (se 1 (by rfl) ⟨1097381, by rfl⟩ : syracuseStep 1463175 = 2194763) B2194763
theorem B1463183 : Blo 1462551 1463183 := bstep (se 1 (by rfl) ⟨1097387, by rfl⟩ : syracuseStep 1463183 = 2194775) B2194775
theorem B4690835 : Blo 1462551 4690835 := bstep (se 1 (by rfl) ⟨3518126, by rfl⟩ : syracuseStep 4690835 = 7036253) B7036253
theorem B1463227 : Blo 1462551 1463227 := bstep (se 1 (by rfl) ⟨1097420, by rfl⟩ : syracuseStep 1463227 = 2194841) B2194841
theorem B18748421 : Blo 1462551 18748421 := bstep (se 4 (by rfl) ⟨1757664, by rfl⟩ : syracuseStep 18748421 = 3515329) B3515329
theorem B1463303 : Blo 1462551 1463303 := bstep (se 1 (by rfl) ⟨1097477, by rfl⟩ : syracuseStep 1463303 = 2194955) B2194955
theorem B1463311 : Blo 1462551 1463311 := bstep (se 1 (by rfl) ⟨1097483, by rfl⟩ : syracuseStep 1463311 = 2194967) B2194967
theorem B4936733 : Blo 1462551 4936733 := bstep (se 3 (by rfl) ⟨925637, by rfl⟩ : syracuseStep 4936733 = 1851275) B1851275
theorem B1463355 : Blo 1462551 1463355 := bstep (se 1 (by rfl) ⟨1097516, by rfl⟩ : syracuseStep 1463355 = 2195033) B2195033
theorem B57021515 : Blo 1462551 57021515 := bstep (se 1 (by rfl) ⟨42766136, by rfl⟩ : syracuseStep 57021515 = 85532273) B85532273
theorem B67564631 : Blo 1462551 67564631 := bstep (se 1 (by rfl) ⟨50673473, by rfl⟩ : syracuseStep 67564631 = 101346947) B101346947
theorem B1463431 : Blo 1462551 1463431 := bstep (se 1 (by rfl) ⟨1097573, by rfl⟩ : syracuseStep 1463431 = 2195147) B2195147
theorem B1463439 : Blo 1462551 1463439 := bstep (se 1 (by rfl) ⟨1097579, by rfl⟩ : syracuseStep 1463439 = 2195159) B2195159
theorem B2225323 : Blo 1462551 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B1463483 : Blo 1462551 1463483 := bstep (se 1 (by rfl) ⟨1097612, by rfl⟩ : syracuseStep 1463483 = 2195225) B2195225
theorem B21091565 : Blo 1462551 21091565 := bstep (se 3 (by rfl) ⟨3954668, by rfl⟩ : syracuseStep 21091565 = 7909337) B7909337
theorem B1463559 : Blo 1462551 1463559 := bstep (se 1 (by rfl) ⟨1097669, by rfl⟩ : syracuseStep 1463559 = 2195339) B2195339
theorem B1463567 : Blo 1462551 1463567 := bstep (se 1 (by rfl) ⟨1097675, by rfl⟩ : syracuseStep 1463567 = 2195351) B2195351
theorem B1463611 : Blo 1462551 1463611 := bstep (se 1 (by rfl) ⟨1097708, by rfl⟩ : syracuseStep 1463611 = 2195417) B2195417
theorem B3954055 : Blo 1462551 3954055 := bstep (se 1 (by rfl) ⟨2965541, by rfl⟩ : syracuseStep 3954055 = 5931083) B5931083
theorem B1463687 : Blo 1462551 1463687 := bstep (se 1 (by rfl) ⟨1097765, by rfl⟩ : syracuseStep 1463687 = 2195531) B2195531
theorem B2471303 : Blo 1462551 2471303 := bstep (se 1 (by rfl) ⟨1853477, by rfl⟩ : syracuseStep 2471303 = 3706955) B3706955
theorem B1463695 : Blo 1462551 1463695 := bstep (se 1 (by rfl) ⟨1097771, by rfl⟩ : syracuseStep 1463695 = 2195543) B2195543
theorem B1463739 : Blo 1462551 1463739 := bstep (se 1 (by rfl) ⟨1097804, by rfl⟩ : syracuseStep 1463739 = 2195609) B2195609
theorem B35591633 : Blo 1462551 35591633 := bstep (se 2 (by rfl) ⟨13346862, by rfl⟩ : syracuseStep 35591633 = 26693725) B26693725
theorem B1463815 : Blo 1462551 1463815 := bstep (se 1 (by rfl) ⟨1097861, by rfl⟩ : syracuseStep 1463815 = 2195723) B2195723
theorem B1463823 : Blo 1462551 1463823 := bstep (se 1 (by rfl) ⟨1097867, by rfl⟩ : syracuseStep 1463823 = 2195735) B2195735
theorem B9377309 : Blo 1462551 9377309 := bstep (se 3 (by rfl) ⟨1758245, by rfl⟩ : syracuseStep 9377309 = 3516491) B3516491
theorem B4167227 : Blo 1462551 4167227 := bstep (se 1 (by rfl) ⟨3125420, by rfl⟩ : syracuseStep 4167227 = 6250841) B6250841
theorem B1463867 : Blo 1462551 1463867 := bstep (se 1 (by rfl) ⟨1097900, by rfl⟩ : syracuseStep 1463867 = 2195801) B2195801
theorem B4167283 : Blo 1462551 4167283 := bstep (se 1 (by rfl) ⟨3125462, by rfl⟩ : syracuseStep 4167283 = 6250925) B6250925
theorem B3290759 : Blo 1462551 3290759 := bstep (se 1 (by rfl) ⟨2468069, by rfl⟩ : syracuseStep 3290759 = 4936139) B4936139
theorem B1463943 : Blo 1462551 1463943 := bstep (se 1 (by rfl) ⟨1097957, by rfl⟩ : syracuseStep 1463943 = 2195915) B2195915
theorem B1463951 : Blo 1462551 1463951 := bstep (se 1 (by rfl) ⟨1097963, by rfl⟩ : syracuseStep 1463951 = 2195927) B2195927
theorem B3954323 : Blo 1462551 3954323 := bstep (se 1 (by rfl) ⟨2965742, by rfl⟩ : syracuseStep 3954323 = 5931485) B5931485
theorem B1463995 : Blo 1462551 1463995 := bstep (se 1 (by rfl) ⟨1097996, by rfl⟩ : syracuseStep 1463995 = 2195993) B2195993
theorem B3954433 : Blo 1462551 3954433 := bstep (se 2 (by rfl) ⟨1482912, by rfl⟩ : syracuseStep 3954433 = 2965825) B2965825
theorem B1464071 : Blo 1462551 1464071 := bstep (se 1 (by rfl) ⟨1098053, by rfl⟩ : syracuseStep 1464071 = 2196107) B2196107
theorem B1464079 : Blo 1462551 1464079 := bstep (se 1 (by rfl) ⟨1098059, by rfl⟩ : syracuseStep 1464079 = 2196119) B2196119
theorem B35608369 : Blo 1462551 35608369 := bstep (se 2 (by rfl) ⟨13353138, by rfl⟩ : syracuseStep 35608369 = 26706277) B26706277
theorem B3290939 : Blo 1462551 3290939 := bstep (se 1 (by rfl) ⟨2468204, by rfl⟩ : syracuseStep 3290939 = 4936409) B4936409
theorem B1464123 : Blo 1462551 1464123 := bstep (se 1 (by rfl) ⟨1098092, by rfl⟩ : syracuseStep 1464123 = 2196185) B2196185
theorem B1464199 : Blo 1462551 1464199 := bstep (se 1 (by rfl) ⟨1098149, by rfl⟩ : syracuseStep 1464199 = 2196299) B2196299
theorem B1464207 : Blo 1462551 1464207 := bstep (se 1 (by rfl) ⟨1098155, by rfl⟩ : syracuseStep 1464207 = 2196311) B2196311
theorem B3291065 : Blo 1462551 3291065 := bstep (se 2 (by rfl) ⟨1234149, by rfl⟩ : syracuseStep 3291065 = 2468299) B2468299
theorem B1464251 : Blo 1462551 1464251 := bstep (se 1 (by rfl) ⟨1098188, by rfl⟩ : syracuseStep 1464251 = 2196377) B2196377
theorem B4167625 : Blo 1462551 4167625 := bstep (se 2 (by rfl) ⟨1562859, by rfl⟩ : syracuseStep 4167625 = 3125719) B3125719
theorem B1464327 : Blo 1462551 1464327 := bstep (se 1 (by rfl) ⟨1098245, by rfl⟩ : syracuseStep 1464327 = 2196491) B2196491
theorem B1464335 : Blo 1462551 1464335 := bstep (se 1 (by rfl) ⟨1098251, by rfl⟩ : syracuseStep 1464335 = 2196503) B2196503
theorem B45078551 : Blo 1462551 45078551 := bstep (se 1 (by rfl) ⟨33808913, by rfl⟩ : syracuseStep 45078551 = 67617827) B67617827
theorem B8337437 : Blo 1462551 8337437 := bstep (se 3 (by rfl) ⟨1563269, by rfl⟩ : syracuseStep 8337437 = 3126539) B3126539
theorem B1464379 : Blo 1462551 1464379 := bstep (se 1 (by rfl) ⟨1098284, by rfl⟩ : syracuseStep 1464379 = 2196569) B2196569
theorem B4225159 : Blo 1462551 4225159 := bstep (se 1 (by rfl) ⟨3168869, by rfl⟩ : syracuseStep 4225159 = 6337739) B6337739
theorem B1464455 : Blo 1462551 1464455 := bstep (se 1 (by rfl) ⟨1098341, by rfl⟩ : syracuseStep 1464455 = 2196683) B2196683
theorem B1464463 : Blo 1462551 1464463 := bstep (se 1 (by rfl) ⟨1098347, by rfl⟩ : syracuseStep 1464463 = 2196695) B2196695
theorem B1669307 : Blo 1462551 1669307 := bstep (se 1 (by rfl) ⟨1251980, by rfl⟩ : syracuseStep 1669307 = 2503961) B2503961
theorem B1464507 : Blo 1462551 1464507 := bstep (se 1 (by rfl) ⟨1098380, by rfl⟩ : syracuseStep 1464507 = 2196761) B2196761
theorem B3291407 : Blo 1462551 3291407 := bstep (se 1 (by rfl) ⟨2468555, by rfl⟩ : syracuseStep 3291407 = 4937111) B4937111
theorem B3291425 : Blo 1462551 3291425 := bstep (se 2 (by rfl) ⟨1234284, by rfl⟩ : syracuseStep 3291425 = 2468569) B2468569
theorem B4938137 : Blo 1462551 4938137 := bstep (se 2 (by rfl) ⟨1851801, by rfl⟩ : syracuseStep 4938137 = 3703603) B3703603
theorem B2193851 : Blo 1462551 2193851 := bstep (se 1 (by rfl) ⟨1645388, by rfl⟩ : syracuseStep 2193851 = 3290777) B3290777
theorem B2226619 : Blo 1462551 2226619 := bstep (se 1 (by rfl) ⟨1669964, by rfl⟩ : syracuseStep 2226619 = 3339929) B3339929
theorem B5937617 : Blo 1462551 5937617 := bstep (se 2 (by rfl) ⟨2226606, by rfl⟩ : syracuseStep 5937617 = 4453213) B4453213
theorem B2193911 : Blo 1462551 2193911 := bstep (se 1 (by rfl) ⟨1645433, by rfl⟩ : syracuseStep 2193911 = 3290867) B3290867
theorem B2193935 : Blo 1462551 2193935 := bstep (se 1 (by rfl) ⟨1645451, by rfl⟩ : syracuseStep 2193935 = 3290903) B3290903
theorem B2193977 : Blo 1462551 2193977 := bstep (se 2 (by rfl) ⟨822741, by rfl⟩ : syracuseStep 2193977 = 1645483) B1645483
theorem B6249079 : Blo 1462551 6249079 := bstep (se 1 (by rfl) ⟨4686809, by rfl⟩ : syracuseStep 6249079 = 9373619) B9373619
theorem B3291767 : Blo 1462551 3291767 := bstep (se 1 (by rfl) ⟨2468825, by rfl⟩ : syracuseStep 3291767 = 4937651) B4937651
theorem B2194055 : Blo 1462551 2194055 := bstep (se 1 (by rfl) ⟨1645541, by rfl⟩ : syracuseStep 2194055 = 3291083) B3291083
theorem B2194091 : Blo 1462551 2194091 := bstep (se 1 (by rfl) ⟨1645568, by rfl⟩ : syracuseStep 2194091 = 3291137) B3291137
theorem B2194121 : Blo 1462551 2194121 := bstep (se 2 (by rfl) ⟨822795, by rfl⟩ : syracuseStep 2194121 = 1645591) B1645591
theorem B3291947 : Blo 1462551 3291947 := bstep (se 1 (by rfl) ⟨2468960, by rfl⟩ : syracuseStep 3291947 = 4937921) B4937921
theorem B2194235 : Blo 1462551 2194235 := bstep (se 1 (by rfl) ⟨1645676, by rfl⟩ : syracuseStep 2194235 = 3291353) B3291353
theorem B2194295 : Blo 1462551 2194295 := bstep (se 1 (by rfl) ⟨1645721, by rfl⟩ : syracuseStep 2194295 = 3291443) B3291443
theorem B1645447 : Blo 1462551 1645447 := bstep (se 1 (by rfl) ⟨1234085, by rfl⟩ : syracuseStep 1645447 = 2468171) B2468171
theorem B2194319 : Blo 1462551 2194319 := bstep (se 1 (by rfl) ⟨1645739, by rfl⟩ : syracuseStep 2194319 = 3291479) B3291479
theorem B7412633 : Blo 1462551 7412633 := bstep (se 2 (by rfl) ⟨2779737, by rfl⟩ : syracuseStep 7412633 = 5559475) B5559475
theorem B21085109 : Blo 1462551 21085109 := bstep (se 5 (by rfl) ⟨988364, by rfl⟩ : syracuseStep 21085109 = 1976729) B1976729
theorem B2194361 : Blo 1462551 2194361 := bstep (se 2 (by rfl) ⟨822885, by rfl⟩ : syracuseStep 2194361 = 1645771) B1645771
theorem B2194439 : Blo 1462551 2194439 := bstep (se 1 (by rfl) ⟨1645829, by rfl⟩ : syracuseStep 2194439 = 3291659) B3291659
theorem B2194475 : Blo 1462551 2194475 := bstep (se 1 (by rfl) ⟨1645856, by rfl⟩ : syracuseStep 2194475 = 3291713) B3291713
theorem B1645627 : Blo 1462551 1645627 := bstep (se 1 (by rfl) ⟨1234220, by rfl⟩ : syracuseStep 1645627 = 2468441) B2468441
theorem B2194505 : Blo 1462551 2194505 := bstep (se 2 (by rfl) ⟨822939, by rfl⟩ : syracuseStep 2194505 = 1645879) B1645879
theorem B4938839 : Blo 1462551 4938839 := bstep (se 1 (by rfl) ⟨3704129, by rfl⟩ : syracuseStep 4938839 = 7408259) B7408259
theorem B3292307 : Blo 1462551 3292307 := bstep (se 1 (by rfl) ⟨2469230, by rfl⟩ : syracuseStep 3292307 = 4938461) B4938461
theorem B16678061 : Blo 1462551 16678061 := bstep (se 3 (by rfl) ⟨3127136, by rfl⟩ : syracuseStep 16678061 = 6254273) B6254273
theorem B2194619 : Blo 1462551 2194619 := bstep (se 1 (by rfl) ⟨1645964, by rfl⟩ : syracuseStep 2194619 = 3291929) B3291929
theorem B11107529 : Blo 1462551 11107529 := bstep (se 2 (by rfl) ⟨4165323, by rfl⟩ : syracuseStep 11107529 = 8330647) B8330647
theorem B3292361 : Blo 1462551 3292361 := bstep (se 2 (by rfl) ⟨1234635, by rfl⟩ : syracuseStep 3292361 = 2469271) B2469271
theorem B2194679 : Blo 1462551 2194679 := bstep (se 1 (by rfl) ⟨1646009, by rfl⟩ : syracuseStep 2194679 = 3292019) B3292019
theorem B2194703 : Blo 1462551 2194703 := bstep (se 1 (by rfl) ⟨1646027, by rfl⟩ : syracuseStep 2194703 = 3292055) B3292055
theorem B2194745 : Blo 1462551 2194745 := bstep (se 2 (by rfl) ⟨823029, by rfl⟩ : syracuseStep 2194745 = 1646059) B1646059
theorem B2194823 : Blo 1462551 2194823 := bstep (se 1 (by rfl) ⟨1646117, by rfl⟩ : syracuseStep 2194823 = 3292235) B3292235
theorem B8019353 : Blo 1462551 8019353 := bstep (se 2 (by rfl) ⟨3007257, by rfl⟩ : syracuseStep 8019353 = 6014515) B6014515
theorem B2194859 : Blo 1462551 2194859 := bstep (se 1 (by rfl) ⟨1646144, by rfl⟩ : syracuseStep 2194859 = 3292289) B3292289
theorem B2194889 : Blo 1462551 2194889 := bstep (se 2 (by rfl) ⟨823083, by rfl⟩ : syracuseStep 2194889 = 1646167) B1646167
theorem B3702287 : Blo 1462551 3702287 := bstep (se 1 (by rfl) ⟨2776715, by rfl⟩ : syracuseStep 3702287 = 5553431) B5553431
theorem B1646095 : Blo 1462551 1646095 := bstep (se 1 (by rfl) ⟨1234571, by rfl⟩ : syracuseStep 1646095 = 2469143) B2469143
theorem B2776609 : Blo 1462551 2776609 := bstep (se 2 (by rfl) ⟨1041228, by rfl⟩ : syracuseStep 2776609 = 2082457) B2082457
theorem B2195003 : Blo 1462551 2195003 := bstep (se 1 (by rfl) ⟨1646252, by rfl⟩ : syracuseStep 2195003 = 3292505) B3292505
theorem B4939325 : Blo 1462551 4939325 := bstep (se 3 (by rfl) ⟨926123, by rfl⟩ : syracuseStep 4939325 = 1852247) B1852247
theorem B2195063 : Blo 1462551 2195063 := bstep (se 1 (by rfl) ⟨1646297, by rfl⟩ : syracuseStep 2195063 = 3292595) B3292595
theorem B2195087 : Blo 1462551 2195087 := bstep (se 1 (by rfl) ⟨1646315, by rfl⟩ : syracuseStep 2195087 = 3292631) B3292631
theorem B3702419 : Blo 1462551 3702419 := bstep (se 1 (by rfl) ⟨2776814, by rfl⟩ : syracuseStep 3702419 = 5553629) B5553629
theorem B2195129 : Blo 1462551 2195129 := bstep (se 2 (by rfl) ⟨823173, by rfl⟩ : syracuseStep 2195129 = 1646347) B1646347
theorem B2195207 : Blo 1462551 2195207 := bstep (se 1 (by rfl) ⟨1646405, by rfl⟩ : syracuseStep 2195207 = 3292811) B3292811
theorem B1482511 : Blo 1462551 1482511 := bstep (se 1 (by rfl) ⟨1111883, by rfl⟩ : syracuseStep 1482511 = 2223767) B2223767
theorem B2195243 : Blo 1462551 2195243 := bstep (se 1 (by rfl) ⟨1646432, by rfl⟩ : syracuseStep 2195243 = 3292865) B3292865
theorem B28139309 : Blo 1462551 28139309 := bstep (se 3 (by rfl) ⟨5276120, by rfl⟩ : syracuseStep 28139309 = 10552241) B10552241
theorem B2195273 : Blo 1462551 2195273 := bstep (se 2 (by rfl) ⟨823227, by rfl⟩ : syracuseStep 2195273 = 1646455) B1646455
theorem B3293063 : Blo 1462551 3293063 := bstep (se 1 (by rfl) ⟨2469797, by rfl⟩ : syracuseStep 3293063 = 4939595) B4939595
theorem B4448153 : Blo 1462551 4448153 := bstep (se 2 (by rfl) ⟨1668057, by rfl⟩ : syracuseStep 4448153 = 3336115) B3336115
theorem B2195387 : Blo 1462551 2195387 := bstep (se 1 (by rfl) ⟨1646540, by rfl⟩ : syracuseStep 2195387 = 3293081) B3293081
theorem B5554129 : Blo 1462551 5554129 := bstep (se 2 (by rfl) ⟨2082798, by rfl⟩ : syracuseStep 5554129 = 4165597) B4165597
theorem B2195447 : Blo 1462551 2195447 := bstep (se 1 (by rfl) ⟨1646585, by rfl⟩ : syracuseStep 2195447 = 3293171) B3293171
theorem B2777095 : Blo 1462551 2777095 := bstep (se 1 (by rfl) ⟨2082821, by rfl⟩ : syracuseStep 2777095 = 4165643) B4165643
theorem B2195465 : Blo 1462551 2195465 := bstep (se 2 (by rfl) ⟨823299, by rfl⟩ : syracuseStep 2195465 = 1646599) B1646599
theorem B7413767 : Blo 1462551 7413767 := bstep (se 1 (by rfl) ⟨5560325, by rfl⟩ : syracuseStep 7413767 = 11120651) B11120651
theorem B2195495 : Blo 1462551 2195495 := bstep (se 1 (by rfl) ⟨1646621, by rfl⟩ : syracuseStep 2195495 = 3293243) B3293243
theorem B1646671 : Blo 1462551 1646671 := bstep (se 1 (by rfl) ⟨1235003, by rfl⟩ : syracuseStep 1646671 = 2470007) B2470007
theorem B5275763 : Blo 1462551 5275763 := bstep (se 1 (by rfl) ⟨3956822, by rfl⟩ : syracuseStep 5275763 = 7913645) B7913645
theorem B2195579 : Blo 1462551 2195579 := bstep (se 1 (by rfl) ⟨1646684, by rfl⟩ : syracuseStep 2195579 = 3293369) B3293369
theorem B3702955 : Blo 1462551 3702955 := bstep (se 1 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 3702955 = 5554433) B5554433
theorem B2195705 : Blo 1462551 2195705 := bstep (se 2 (by rfl) ⟨823389, by rfl⟩ : syracuseStep 2195705 = 1646779) B1646779
theorem B2195807 : Blo 1462551 2195807 := bstep (se 1 (by rfl) ⟨1646855, by rfl⟩ : syracuseStep 2195807 = 3293711) B3293711
theorem B2195819 : Blo 1462551 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B3703259 : Blo 1462551 3703259 := bstep (se 1 (by rfl) ⟨2777444, by rfl⟩ : syracuseStep 3703259 = 5554889) B5554889
theorem B1647067 : Blo 1462551 1647067 := bstep (se 1 (by rfl) ⟨1235300, by rfl⟩ : syracuseStep 1647067 = 2470601) B2470601
theorem B7414253 : Blo 1462551 7414253 := bstep (se 3 (by rfl) ⟨1390172, by rfl⟩ : syracuseStep 7414253 = 2780345) B2780345
theorem B2343431 : Blo 1462551 2343431 := bstep (se 1 (by rfl) ⟨1757573, by rfl⟩ : syracuseStep 2343431 = 3515147) B3515147
theorem B4940297 : Blo 1462551 4940297 := bstep (se 2 (by rfl) ⟨1852611, by rfl⟩ : syracuseStep 4940297 = 3705223) B3705223
theorem B9372185 : Blo 1462551 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B2196047 : Blo 1462551 2196047 := bstep (se 1 (by rfl) ⟨1647035, by rfl⟩ : syracuseStep 2196047 = 3294071) B3294071
theorem B3293819 : Blo 1462551 3293819 := bstep (se 1 (by rfl) ⟨2470364, by rfl⟩ : syracuseStep 3293819 = 4940729) B4940729
theorem B2196167 : Blo 1462551 2196167 := bstep (se 1 (by rfl) ⟨1647125, by rfl⟩ : syracuseStep 2196167 = 3294251) B3294251
theorem B3293945 : Blo 1462551 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B8332105 : Blo 1462551 8332105 := bstep (se 2 (by rfl) ⟨3124539, by rfl⟩ : syracuseStep 8332105 = 6249079) B6249079
theorem B2196329 : Blo 1462551 2196329 := bstep (se 2 (by rfl) ⟨823623, by rfl⟩ : syracuseStep 2196329 = 1647247) B1647247
theorem B1647535 : Blo 1462551 1647535 := bstep (se 1 (by rfl) ⟨1235651, by rfl⟩ : syracuseStep 1647535 = 2471303) B2471303
theorem B2196407 : Blo 1462551 2196407 := bstep (se 1 (by rfl) ⟨1647305, by rfl⟩ : syracuseStep 2196407 = 3294611) B3294611
theorem B2196443 : Blo 1462551 2196443 := bstep (se 1 (by rfl) ⟨1647332, by rfl⟩ : syracuseStep 2196443 = 3294665) B3294665
theorem B2638811 : Blo 1462551 2638811 := bstep (se 1 (by rfl) ⟨1979108, by rfl⟩ : syracuseStep 2638811 = 3958217) B3958217
theorem B3294215 : Blo 1462551 3294215 := bstep (se 1 (by rfl) ⟨2470661, by rfl⟩ : syracuseStep 3294215 = 4941323) B4941323
theorem B2778151 : Blo 1462551 2778151 := bstep (se 1 (by rfl) ⟨2083613, by rfl⟩ : syracuseStep 2778151 = 4167227) B4167227
theorem B3294287 : Blo 1462551 3294287 := bstep (se 1 (by rfl) ⟨2470715, by rfl⟩ : syracuseStep 3294287 = 4941431) B4941431
theorem B4941161 : Blo 1462551 4941161 := bstep (se 2 (by rfl) ⟨1852935, by rfl⟩ : syracuseStep 4941161 = 3705871) B3705871
theorem B3958121 : Blo 1462551 3958121 := bstep (se 2 (by rfl) ⟨1484295, by rfl⟩ : syracuseStep 3958121 = 2968591) B2968591
theorem B2377067 : Blo 1462551 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B4687247 : Blo 1462551 4687247 := bstep (se 1 (by rfl) ⟨3515435, by rfl⟩ : syracuseStep 4687247 = 7030871) B7030871
theorem B18761179 : Blo 1462551 18761179 := bstep (se 1 (by rfl) ⟨14070884, by rfl⟩ : syracuseStep 18761179 = 28141769) B28141769
theorem B3294683 : Blo 1462551 3294683 := bstep (se 1 (by rfl) ⟨2471012, by rfl⟩ : syracuseStep 3294683 = 4942025) B4942025
theorem B3958411 : Blo 1462551 3958411 := bstep (se 1 (by rfl) ⟨2968808, by rfl⟩ : syracuseStep 3958411 = 5937617) B5937617
theorem B4753043 : Blo 1462551 4753043 := bstep (se 1 (by rfl) ⟨3564782, by rfl⟩ : syracuseStep 4753043 = 7129565) B7129565
theorem B2967251 : Blo 1462551 2967251 := bstep (se 1 (by rfl) ⟨2225438, by rfl⟩ : syracuseStep 2967251 = 4450877) B4450877
theorem B21399385 : Blo 1462551 21399385 := bstep (se 2 (by rfl) ⟨8024769, by rfl⟩ : syracuseStep 21399385 = 16049539) B16049539
theorem B16893791 : Blo 1462551 16893791 := bstep (se 1 (by rfl) ⟨12670343, by rfl⟩ : syracuseStep 16893791 = 25340687) B25340687
theorem B18753389 : Blo 1462551 18753389 := bstep (se 3 (by rfl) ⟨3516260, by rfl⟩ : syracuseStep 18753389 = 7032521) B7032521
theorem B3704737 : Blo 1462551 3704737 := bstep (se 2 (by rfl) ⟨1389276, by rfl⟩ : syracuseStep 3704737 = 2778553) B2778553
theorem B3295151 : Blo 1462551 3295151 := bstep (se 1 (by rfl) ⟨2471363, by rfl⟩ : syracuseStep 3295151 = 4942727) B4942727
theorem B4941755 : Blo 1462551 4941755 := bstep (se 1 (by rfl) ⟨3706316, by rfl⟩ : syracuseStep 4941755 = 7412633) B7412633
theorem B28149767 : Blo 1462551 28149767 := bstep (se 1 (by rfl) ⟨21112325, by rfl⟩ : syracuseStep 28149767 = 42224651) B42224651
theorem B11118707 : Blo 1462551 11118707 := bstep (se 1 (by rfl) ⟨8339030, by rfl⟩ : syracuseStep 11118707 = 16678061) B16678061
theorem B5556377 : Blo 1462551 5556377 := bstep (se 2 (by rfl) ⟨2083641, by rfl⟩ : syracuseStep 5556377 = 4167283) B4167283
theorem B7407773 : Blo 1462551 7407773 := bstep (se 3 (by rfl) ⟨1388957, by rfl⟩ : syracuseStep 7407773 = 2777915) B2777915
theorem B12675329 : Blo 1462551 12675329 := bstep (se 2 (by rfl) ⟨4753248, by rfl⟩ : syracuseStep 12675329 = 9506497) B9506497
theorem B21104945 : Blo 1462551 21104945 := bstep (se 2 (by rfl) ⟨7914354, by rfl⟩ : syracuseStep 21104945 = 15828709) B15828709
theorem B2468191 : Blo 1462551 2468191 := bstep (se 1 (by rfl) ⟨1851143, by rfl⟩ : syracuseStep 2468191 = 3702287) B3702287
theorem B1976681 : Blo 1462551 1976681 := bstep (se 2 (by rfl) ⟨741255, by rfl⟩ : syracuseStep 1976681 = 1482511) B1482511
theorem B2468279 : Blo 1462551 2468279 := bstep (se 1 (by rfl) ⟨1851209, by rfl⟩ : syracuseStep 2468279 = 3702419) B3702419
theorem B10013165 : Blo 1462551 10013165 := bstep (se 3 (by rfl) ⟨1877468, by rfl⟩ : syracuseStep 10013165 = 3754937) B3754937
theorem B10553915 : Blo 1462551 10553915 := bstep (se 1 (by rfl) ⟨7915436, by rfl⟩ : syracuseStep 10553915 = 15830873) B15830873
theorem B5556833 : Blo 1462551 5556833 := bstep (se 2 (by rfl) ⟨2083812, by rfl⟩ : syracuseStep 5556833 = 4167625) B4167625
theorem B2779859 : Blo 1462551 2779859 := bstep (se 1 (by rfl) ⟨2084894, by rfl⟩ : syracuseStep 2779859 = 4169789) B4169789
theorem B2780011 : Blo 1462551 2780011 := bstep (se 1 (by rfl) ⟨2085008, by rfl⟩ : syracuseStep 2780011 = 4170017) B4170017
theorem B37489553 : Blo 1462551 37489553 := bstep (se 2 (by rfl) ⟨14058582, by rfl⟩ : syracuseStep 37489553 = 28117165) B28117165
theorem B3566497 : Blo 1462551 3566497 := bstep (se 2 (by rfl) ⟨1337436, by rfl⟩ : syracuseStep 3566497 = 2674873) B2674873
theorem B2468873 : Blo 1462551 2468873 := bstep (se 2 (by rfl) ⟨925827, by rfl⟩ : syracuseStep 2468873 = 1851655) B1851655
theorem B2780239 : Blo 1462551 2780239 := bstep (se 1 (by rfl) ⟨2085179, by rfl⟩ : syracuseStep 2780239 = 4170359) B4170359
theorem B4451485 : Blo 1462551 4451485 := bstep (se 3 (by rfl) ⟨834653, by rfl⟩ : syracuseStep 4451485 = 1669307) B1669307
theorem B2469035 : Blo 1462551 2469035 := bstep (se 1 (by rfl) ⟨1851776, by rfl⟩ : syracuseStep 2469035 = 3703553) B3703553
theorem B2968825 : Blo 1462551 2968825 := bstep (se 2 (by rfl) ⟨1113309, by rfl⟩ : syracuseStep 2968825 = 2226619) B2226619
theorem B38014343 : Blo 1462551 38014343 := bstep (se 1 (by rfl) ⟨28510757, by rfl⟩ : syracuseStep 38014343 = 57021515) B57021515
theorem B45043087 : Blo 1462551 45043087 := bstep (se 1 (by rfl) ⟨33782315, by rfl⟩ : syracuseStep 45043087 = 67564631) B67564631
theorem B7409069 : Blo 1462551 7409069 := bstep (se 3 (by rfl) ⟨1389200, by rfl⟩ : syracuseStep 7409069 = 2778401) B2778401
theorem B14249459 : Blo 1462551 14249459 := bstep (se 1 (by rfl) ⟨10687094, by rfl⟩ : syracuseStep 14249459 = 21374189) B21374189
theorem B14061043 : Blo 1462551 14061043 := bstep (se 1 (by rfl) ⟨10545782, by rfl⟩ : syracuseStep 14061043 = 21091565) B21091565
theorem B3124745 : Blo 1462551 3124745 := bstep (se 2 (by rfl) ⟨1171779, by rfl⟩ : syracuseStep 3124745 = 2343559) B2343559
theorem B2469433 : Blo 1462551 2469433 := bstep (se 2 (by rfl) ⟨926037, by rfl⟩ : syracuseStep 2469433 = 1852075) B1852075
theorem B23727755 : Blo 1462551 23727755 := bstep (se 1 (by rfl) ⟨17795816, by rfl⟩ : syracuseStep 23727755 = 35591633) B35591633
theorem B2469575 : Blo 1462551 2469575 := bstep (se 1 (by rfl) ⟨1852181, by rfl⟩ : syracuseStep 2469575 = 3704363) B3704363
theorem B2469737 : Blo 1462551 2469737 := bstep (se 2 (by rfl) ⟨926151, by rfl⟩ : syracuseStep 2469737 = 1852303) B1852303
theorem B30052367 : Blo 1462551 30052367 := bstep (se 1 (by rfl) ⟨22539275, by rfl⟩ : syracuseStep 30052367 = 45078551) B45078551
theorem B5558291 : Blo 1462551 5558291 := bstep (se 1 (by rfl) ⟨4168718, by rfl⟩ : syracuseStep 5558291 = 8337437) B8337437
theorem B25006157 : Blo 1462551 25006157 := bstep (se 3 (by rfl) ⟨4688654, by rfl⟩ : syracuseStep 25006157 = 9377309) B9377309
theorem B11874385 : Blo 1462551 11874385 := bstep (se 2 (by rfl) ⟨4452894, by rfl⟩ : syracuseStep 11874385 = 8905789) B8905789
theorem B2470135 : Blo 1462551 2470135 := bstep (se 1 (by rfl) ⟨1852601, by rfl⟩ : syracuseStep 2470135 = 3705203) B3705203
theorem B1462567 : Blo 1462551 1462567 := bstep (se 1 (by rfl) ⟨1096925, by rfl⟩ : syracuseStep 1462567 = 2193851) B2193851
theorem B1462607 : Blo 1462551 1462607 := bstep (se 1 (by rfl) ⟨1096955, by rfl⟩ : syracuseStep 1462607 = 2193911) B2193911
theorem B1462623 : Blo 1462551 1462623 := bstep (se 1 (by rfl) ⟨1096967, by rfl⟩ : syracuseStep 1462623 = 2193935) B2193935
theorem B1462651 : Blo 1462551 1462651 := bstep (se 1 (by rfl) ⟨1096988, by rfl⟩ : syracuseStep 1462651 = 2193977) B2193977
theorem B1462703 : Blo 1462551 1462703 := bstep (se 1 (by rfl) ⟨1097027, by rfl⟩ : syracuseStep 1462703 = 2194055) B2194055
theorem B2470331 : Blo 1462551 2470331 := bstep (se 1 (by rfl) ⟨1852748, by rfl⟩ : syracuseStep 2470331 = 3705497) B3705497
theorem B1462727 : Blo 1462551 1462727 := bstep (se 1 (by rfl) ⟨1097045, by rfl⟩ : syracuseStep 1462727 = 2194091) B2194091
theorem B1462747 : Blo 1462551 1462747 := bstep (se 1 (by rfl) ⟨1097060, by rfl⟩ : syracuseStep 1462747 = 2194121) B2194121
theorem B5272073 : Blo 1462551 5272073 := bstep (se 2 (by rfl) ⟨1977027, by rfl⟩ : syracuseStep 5272073 = 3954055) B3954055
theorem B1462823 : Blo 1462551 1462823 := bstep (se 1 (by rfl) ⟨1097117, by rfl⟩ : syracuseStep 1462823 = 2194235) B2194235
theorem B2470439 : Blo 1462551 2470439 := bstep (se 1 (by rfl) ⟨1852829, by rfl⟩ : syracuseStep 2470439 = 3705659) B3705659
theorem B1462863 : Blo 1462551 1462863 := bstep (se 1 (by rfl) ⟨1097147, by rfl⟩ : syracuseStep 1462863 = 2194295) B2194295
theorem B1462879 : Blo 1462551 1462879 := bstep (se 1 (by rfl) ⟨1097159, by rfl⟩ : syracuseStep 1462879 = 2194319) B2194319
theorem B1462907 : Blo 1462551 1462907 := bstep (se 1 (by rfl) ⟨1097180, by rfl⟩ : syracuseStep 1462907 = 2194361) B2194361
theorem B1462959 : Blo 1462551 1462959 := bstep (se 1 (by rfl) ⟨1097219, by rfl⟩ : syracuseStep 1462959 = 2194439) B2194439
theorem B1462983 : Blo 1462551 1462983 := bstep (se 1 (by rfl) ⟨1097237, by rfl⟩ : syracuseStep 1462983 = 2194475) B2194475
theorem B1463003 : Blo 1462551 1463003 := bstep (se 1 (by rfl) ⟨1097252, by rfl⟩ : syracuseStep 1463003 = 2194505) B2194505
theorem B1463079 : Blo 1462551 1463079 := bstep (se 1 (by rfl) ⟨1097309, by rfl⟩ : syracuseStep 1463079 = 2194619) B2194619
theorem B2470729 : Blo 1462551 2470729 := bstep (se 2 (by rfl) ⟨926523, by rfl⟩ : syracuseStep 2470729 = 1853047) B1853047
theorem B1463119 : Blo 1462551 1463119 := bstep (se 1 (by rfl) ⟨1097339, by rfl⟩ : syracuseStep 1463119 = 2194679) B2194679
theorem B1463135 : Blo 1462551 1463135 := bstep (se 1 (by rfl) ⟨1097351, by rfl⟩ : syracuseStep 1463135 = 2194703) B2194703
theorem B2470763 : Blo 1462551 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B1463163 : Blo 1462551 1463163 := bstep (se 1 (by rfl) ⟨1097372, by rfl⟩ : syracuseStep 1463163 = 2194745) B2194745
theorem B11113361 : Blo 1462551 11113361 := bstep (se 2 (by rfl) ⟨4167510, by rfl⟩ : syracuseStep 11113361 = 8335021) B8335021
theorem B1463215 : Blo 1462551 1463215 := bstep (se 1 (by rfl) ⟨1097411, by rfl⟩ : syracuseStep 1463215 = 2194823) B2194823
theorem B5346235 : Blo 1462551 5346235 := bstep (se 1 (by rfl) ⟨4009676, by rfl⟩ : syracuseStep 5346235 = 8019353) B8019353
theorem B1463239 : Blo 1462551 1463239 := bstep (se 1 (by rfl) ⟨1097429, by rfl⟩ : syracuseStep 1463239 = 2194859) B2194859
theorem B1463259 : Blo 1462551 1463259 := bstep (se 1 (by rfl) ⟨1097444, by rfl⟩ : syracuseStep 1463259 = 2194889) B2194889
theorem B12497885 : Blo 1462551 12497885 := bstep (se 3 (by rfl) ⟨2343353, by rfl⟩ : syracuseStep 12497885 = 4686707) B4686707
theorem B5272577 : Blo 1462551 5272577 := bstep (se 2 (by rfl) ⟨1977216, by rfl⟩ : syracuseStep 5272577 = 3954433) B3954433
theorem B7410689 : Blo 1462551 7410689 := bstep (se 2 (by rfl) ⟨2779008, by rfl⟩ : syracuseStep 7410689 = 5558017) B5558017
theorem B1463335 : Blo 1462551 1463335 := bstep (se 1 (by rfl) ⟨1097501, by rfl⟩ : syracuseStep 1463335 = 2195003) B2195003
theorem B47477825 : Blo 1462551 47477825 := bstep (se 2 (by rfl) ⟨17804184, by rfl⟩ : syracuseStep 47477825 = 35608369) B35608369
theorem B1463375 : Blo 1462551 1463375 := bstep (se 1 (by rfl) ⟨1097531, by rfl⟩ : syracuseStep 1463375 = 2195063) B2195063
theorem B1463391 : Blo 1462551 1463391 := bstep (se 1 (by rfl) ⟨1097543, by rfl⟩ : syracuseStep 1463391 = 2195087) B2195087
theorem B1463419 : Blo 1462551 1463419 := bstep (se 1 (by rfl) ⟨1097564, by rfl⟩ : syracuseStep 1463419 = 2195129) B2195129
theorem B1463471 : Blo 1462551 1463471 := bstep (se 1 (by rfl) ⟨1097603, by rfl⟩ : syracuseStep 1463471 = 2195207) B2195207
theorem B1463495 : Blo 1462551 1463495 := bstep (se 1 (by rfl) ⟨1097621, by rfl⟩ : syracuseStep 1463495 = 2195243) B2195243
theorem B1463515 : Blo 1462551 1463515 := bstep (se 1 (by rfl) ⟨1097636, by rfl⟩ : syracuseStep 1463515 = 2195273) B2195273
theorem B2471161 : Blo 1462551 2471161 := bstep (se 2 (by rfl) ⟨926685, by rfl⟩ : syracuseStep 2471161 = 1853371) B1853371
theorem B1463591 : Blo 1462551 1463591 := bstep (se 1 (by rfl) ⟨1097693, by rfl⟩ : syracuseStep 1463591 = 2195387) B2195387
theorem B1463631 : Blo 1462551 1463631 := bstep (se 1 (by rfl) ⟨1097723, by rfl⟩ : syracuseStep 1463631 = 2195447) B2195447
theorem B5346647 : Blo 1462551 5346647 := bstep (se 1 (by rfl) ⟨4009985, by rfl⟩ : syracuseStep 5346647 = 8019971) B8019971
theorem B1463647 : Blo 1462551 1463647 := bstep (se 1 (by rfl) ⟨1097735, by rfl⟩ : syracuseStep 1463647 = 2195471) B2195471
theorem B1463675 : Blo 1462551 1463675 := bstep (se 1 (by rfl) ⟨1097756, by rfl⟩ : syracuseStep 1463675 = 2195513) B2195513
theorem B4167055 : Blo 1462551 4167055 := bstep (se 1 (by rfl) ⟨3125291, by rfl⟩ : syracuseStep 4167055 = 6250583) B6250583
theorem B1463727 : Blo 1462551 1463727 := bstep (se 1 (by rfl) ⟨1097795, by rfl⟩ : syracuseStep 1463727 = 2195591) B2195591
theorem B1463751 : Blo 1462551 1463751 := bstep (se 1 (by rfl) ⟨1097813, by rfl⟩ : syracuseStep 1463751 = 2195627) B2195627
theorem B7910875 : Blo 1462551 7910875 := bstep (se 1 (by rfl) ⟨5933156, by rfl⟩ : syracuseStep 7910875 = 11866313) B11866313
theorem B1463771 : Blo 1462551 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B2471431 : Blo 1462551 2471431 := bstep (se 1 (by rfl) ⟨1853573, by rfl⟩ : syracuseStep 2471431 = 3707147) B3707147
theorem B5633545 : Blo 1462551 5633545 := bstep (se 2 (by rfl) ⟨2112579, by rfl⟩ : syracuseStep 5633545 = 4225159) B4225159
theorem B1463847 : Blo 1462551 1463847 := bstep (se 1 (by rfl) ⟨1097885, by rfl⟩ : syracuseStep 1463847 = 2195771) B2195771
theorem B1463887 : Blo 1462551 1463887 := bstep (se 1 (by rfl) ⟨1097915, by rfl⟩ : syracuseStep 1463887 = 2195831) B2195831
theorem B1463903 : Blo 1462551 1463903 := bstep (se 1 (by rfl) ⟨1097927, by rfl⟩ : syracuseStep 1463903 = 2195855) B2195855
theorem B1463931 : Blo 1462551 1463931 := bstep (se 1 (by rfl) ⟨1097948, by rfl⟩ : syracuseStep 1463931 = 2195897) B2195897
theorem B5559947 : Blo 1462551 5559947 := bstep (se 1 (by rfl) ⟨4169960, by rfl⟩ : syracuseStep 5559947 = 8339921) B8339921
theorem B1463983 : Blo 1462551 1463983 := bstep (se 1 (by rfl) ⟨1097987, by rfl⟩ : syracuseStep 1463983 = 2195975) B2195975
theorem B1464007 : Blo 1462551 1464007 := bstep (se 1 (by rfl) ⟨1098005, by rfl⟩ : syracuseStep 1464007 = 2196011) B2196011
theorem B1464027 : Blo 1462551 1464027 := bstep (se 1 (by rfl) ⟨1098020, by rfl⟩ : syracuseStep 1464027 = 2196041) B2196041
theorem B1464103 : Blo 1462551 1464103 := bstep (se 1 (by rfl) ⟨1098077, by rfl⟩ : syracuseStep 1464103 = 2196155) B2196155
theorem B7411499 : Blo 1462551 7411499 := bstep (se 1 (by rfl) ⟨5558624, by rfl⟩ : syracuseStep 7411499 = 11117249) B11117249
theorem B1464143 : Blo 1462551 1464143 := bstep (se 1 (by rfl) ⟨1098107, by rfl⟩ : syracuseStep 1464143 = 2196215) B2196215
theorem B3290975 : Blo 1462551 3290975 := bstep (se 1 (by rfl) ⟨2468231, by rfl⟩ : syracuseStep 3290975 = 4936463) B4936463
theorem B8451935 : Blo 1462551 8451935 := bstep (se 1 (by rfl) ⟨6338951, by rfl⟩ : syracuseStep 8451935 = 12677903) B12677903
theorem B1464159 : Blo 1462551 1464159 := bstep (se 1 (by rfl) ⟨1098119, by rfl⟩ : syracuseStep 1464159 = 2196239) B2196239
theorem B1464187 : Blo 1462551 1464187 := bstep (se 1 (by rfl) ⟨1098140, by rfl⟩ : syracuseStep 1464187 = 2196281) B2196281
theorem B1464239 : Blo 1462551 1464239 := bstep (se 1 (by rfl) ⟨1098179, by rfl⟩ : syracuseStep 1464239 = 2196359) B2196359
theorem B3127223 : Blo 1462551 3127223 := bstep (se 1 (by rfl) ⟨2345417, by rfl⟩ : syracuseStep 3127223 = 4690835) B4690835
theorem B1464263 : Blo 1462551 1464263 := bstep (se 1 (by rfl) ⟨1098197, by rfl⟩ : syracuseStep 1464263 = 2196395) B2196395
theorem B18749393 : Blo 1462551 18749393 := bstep (se 2 (by rfl) ⟨7031022, by rfl⟩ : syracuseStep 18749393 = 14062045) B14062045
theorem B1464283 : Blo 1462551 1464283 := bstep (se 1 (by rfl) ⟨1098212, by rfl⟩ : syracuseStep 1464283 = 2196425) B2196425
theorem B12498947 : Blo 1462551 12498947 := bstep (se 1 (by rfl) ⟨9374210, by rfl⟩ : syracuseStep 12498947 = 18748421) B18748421
theorem B3291155 : Blo 1462551 3291155 := bstep (se 1 (by rfl) ⟨2468366, by rfl⟩ : syracuseStep 3291155 = 4936733) B4936733
theorem B1562663 : Blo 1462551 1562663 := bstep (se 1 (by rfl) ⟨1171997, by rfl⟩ : syracuseStep 1562663 = 2343995) B2343995
theorem B1464359 : Blo 1462551 1464359 := bstep (se 1 (by rfl) ⟨1098269, by rfl⟩ : syracuseStep 1464359 = 2196539) B2196539
theorem B1464399 : Blo 1462551 1464399 := bstep (se 1 (by rfl) ⟨1098299, by rfl⟩ : syracuseStep 1464399 = 2196599) B2196599
theorem B1464415 : Blo 1462551 1464415 := bstep (se 1 (by rfl) ⟨1098311, by rfl⟩ : syracuseStep 1464415 = 2196623) B2196623
theorem B1464443 : Blo 1462551 1464443 := bstep (se 1 (by rfl) ⟨1098332, by rfl⟩ : syracuseStep 1464443 = 2196665) B2196665
theorem B1464495 : Blo 1462551 1464495 := bstep (se 1 (by rfl) ⟨1098371, by rfl⟩ : syracuseStep 1464495 = 2196743) B2196743
theorem B1464519 : Blo 1462551 1464519 := bstep (se 1 (by rfl) ⟨1098389, by rfl⟩ : syracuseStep 1464519 = 2196779) B2196779
theorem B1464539 : Blo 1462551 1464539 := bstep (se 1 (by rfl) ⟨1098404, by rfl⟩ : syracuseStep 1464539 = 2196809) B2196809
theorem B11868389 : Blo 1462551 11868389 := bstep (se 4 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 11868389 = 2225323) B2225323
theorem B4937975 : Blo 1462551 4937975 := bstep (se 1 (by rfl) ⟨3703481, by rfl⟩ : syracuseStep 4937975 = 7406963) B7406963
theorem B3291497 : Blo 1462551 3291497 := bstep (se 2 (by rfl) ⟨1234311, by rfl⟩ : syracuseStep 3291497 = 2468623) B2468623
theorem B2193839 : Blo 1462551 2193839 := bstep (se 1 (by rfl) ⟨1645379, by rfl⟩ : syracuseStep 2193839 = 3290759) B3290759
theorem B2636215 : Blo 1462551 2636215 := bstep (se 1 (by rfl) ⟨1977161, by rfl⟩ : syracuseStep 2636215 = 3954323) B3954323
theorem B2193929 : Blo 1462551 2193929 := bstep (se 2 (by rfl) ⟨822723, by rfl⟩ : syracuseStep 2193929 = 1645447) B1645447
theorem B2193959 : Blo 1462551 2193959 := bstep (se 1 (by rfl) ⟨1645469, by rfl⟩ : syracuseStep 2193959 = 3290939) B3290939
theorem B4938299 : Blo 1462551 4938299 := bstep (se 1 (by rfl) ⟨3703724, by rfl⟩ : syracuseStep 4938299 = 7407449) B7407449
theorem B2194043 : Blo 1462551 2194043 := bstep (se 1 (by rfl) ⟨1645532, by rfl⟩ : syracuseStep 2194043 = 3291065) B3291065
theorem B4168331 : Blo 1462551 4168331 := bstep (se 1 (by rfl) ⟨3126248, by rfl⟩ : syracuseStep 4168331 = 6252497) B6252497
theorem B2194169 : Blo 1462551 2194169 := bstep (se 2 (by rfl) ⟨822813, by rfl⟩ : syracuseStep 2194169 = 1645627) B1645627
theorem B4938569 : Blo 1462551 4938569 := bstep (se 2 (by rfl) ⟨1851963, by rfl⟩ : syracuseStep 4938569 = 3703927) B3703927
theorem B2194271 : Blo 1462551 2194271 := bstep (se 1 (by rfl) ⟨1645703, by rfl⟩ : syracuseStep 2194271 = 3291407) B3291407
theorem B2194283 : Blo 1462551 2194283 := bstep (se 1 (by rfl) ⟨1645712, by rfl⟩ : syracuseStep 2194283 = 3291425) B3291425
theorem B5938039 : Blo 1462551 5938039 := bstep (se 1 (by rfl) ⟨4453529, by rfl⟩ : syracuseStep 5938039 = 8907059) B8907059
theorem B23731127 : Blo 1462551 23731127 := bstep (se 1 (by rfl) ⟨17798345, by rfl⟩ : syracuseStep 23731127 = 35596691) B35596691
theorem B3292091 : Blo 1462551 3292091 := bstep (se 1 (by rfl) ⟨2469068, by rfl⟩ : syracuseStep 3292091 = 4938137) B4938137
theorem B3955643 : Blo 1462551 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B2005979 : Blo 1462551 2005979 := bstep (se 1 (by rfl) ⟨1504484, by rfl⟩ : syracuseStep 2005979 = 3008969) B3008969
theorem B3292217 : Blo 1462551 3292217 := bstep (se 2 (by rfl) ⟨1234581, by rfl⟩ : syracuseStep 3292217 = 2469163) B2469163
theorem B2194511 : Blo 1462551 2194511 := bstep (se 1 (by rfl) ⟨1645883, by rfl⟩ : syracuseStep 2194511 = 3291767) B3291767
theorem B7035983 : Blo 1462551 7035983 := bstep (se 1 (by rfl) ⟨5276987, by rfl⟩ : syracuseStep 7035983 = 10553975) B10553975
theorem B2194631 : Blo 1462551 2194631 := bstep (se 1 (by rfl) ⟨1645973, by rfl⟩ : syracuseStep 2194631 = 3291947) B3291947
theorem B81165581 : Blo 1462551 81165581 := bstep (se 3 (by rfl) ⟨15218546, by rfl⟩ : syracuseStep 81165581 = 30437093) B30437093
theorem B11115791 : Blo 1462551 11115791 := bstep (se 1 (by rfl) ⟨8336843, by rfl⟩ : syracuseStep 11115791 = 16673687) B16673687
theorem B14056739 : Blo 1462551 14056739 := bstep (se 1 (by rfl) ⟨10542554, by rfl⟩ : syracuseStep 14056739 = 21085109) B21085109
theorem B2194793 : Blo 1462551 2194793 := bstep (se 2 (by rfl) ⟨823047, by rfl⟩ : syracuseStep 2194793 = 1646095) B1646095
theorem B3702145 : Blo 1462551 3702145 := bstep (se 2 (by rfl) ⟨1388304, by rfl⟩ : syracuseStep 3702145 = 2776609) B2776609
theorem B3292559 : Blo 1462551 3292559 := bstep (se 1 (by rfl) ⟨2469419, by rfl⟩ : syracuseStep 3292559 = 4938839) B4938839
theorem B2194871 : Blo 1462551 2194871 := bstep (se 1 (by rfl) ⟨1646153, by rfl⟩ : syracuseStep 2194871 = 3292307) B3292307
theorem B7405019 : Blo 1462551 7405019 := bstep (se 1 (by rfl) ⟨5553764, by rfl⟩ : syracuseStep 7405019 = 11107529) B11107529
theorem B2194907 : Blo 1462551 2194907 := bstep (se 1 (by rfl) ⟨1646180, by rfl⟩ : syracuseStep 2194907 = 3292361) B3292361
theorem B3956249 : Blo 1462551 3956249 := bstep (se 2 (by rfl) ⟨1483593, by rfl⟩ : syracuseStep 3956249 = 2967187) B2967187
theorem B2776655 : Blo 1462551 2776655 := bstep (se 1 (by rfl) ⟨2082491, by rfl⟩ : syracuseStep 2776655 = 4164983) B4164983
theorem B1646203 : Blo 1462551 1646203 := bstep (se 1 (by rfl) ⟨1234652, by rfl⟩ : syracuseStep 1646203 = 2469305) B2469305
theorem B3292883 : Blo 1462551 3292883 := bstep (se 1 (by rfl) ⟨2469662, by rfl⟩ : syracuseStep 3292883 = 4939325) B4939325
theorem B11861741 : Blo 1462551 11861741 := bstep (se 3 (by rfl) ⟨2224076, by rfl⟩ : syracuseStep 11861741 = 4448153) B4448153
theorem B18759539 : Blo 1462551 18759539 := bstep (se 1 (by rfl) ⟨14069654, by rfl⟩ : syracuseStep 18759539 = 28139309) B28139309
theorem B2195375 : Blo 1462551 2195375 := bstep (se 1 (by rfl) ⟨1646531, by rfl⟩ : syracuseStep 2195375 = 3293063) B3293063
theorem B4939703 : Blo 1462551 4939703 := bstep (se 1 (by rfl) ⟨3704777, by rfl⟩ : syracuseStep 4939703 = 7409555) B7409555
theorem B7405505 : Blo 1462551 7405505 := bstep (se 2 (by rfl) ⟨2777064, by rfl⟩ : syracuseStep 7405505 = 5554129) B5554129
theorem B152002507 : Blo 1462551 152002507 := bstep (se 1 (by rfl) ⟨114001880, by rfl⟩ : syracuseStep 152002507 = 228003761) B228003761
theorem B3702793 : Blo 1462551 3702793 := bstep (se 2 (by rfl) ⟨1388547, by rfl⟩ : syracuseStep 3702793 = 2777095) B2777095
theorem B16670771 : Blo 1462551 16670771 := bstep (se 1 (by rfl) ⟨12503078, by rfl⟩ : syracuseStep 16670771 = 25006157) B25006157
theorem B2195561 : Blo 1462551 2195561 := bstep (se 2 (by rfl) ⟨823335, by rfl⟩ : syracuseStep 2195561 = 1646671) B1646671
theorem B1646887 : Blo 1462551 1646887 := bstep (se 1 (by rfl) ⟨1235165, by rfl⟩ : syracuseStep 1646887 = 2470331) B2470331
theorem B3293513 : Blo 1462551 3293513 := bstep (se 2 (by rfl) ⟨1235067, by rfl⟩ : syracuseStep 3293513 = 2470135) B2470135
theorem B3514715 : Blo 1462551 3514715 := bstep (se 1 (by rfl) ⟨2636036, by rfl⟩ : syracuseStep 3514715 = 5272073) B5272073
theorem B3293531 : Blo 1462551 3293531 := bstep (se 1 (by rfl) ⟨2470148, by rfl⟩ : syracuseStep 3293531 = 4940297) B4940297
theorem B1646959 : Blo 1462551 1646959 := bstep (se 1 (by rfl) ⟨1235219, by rfl⟩ : syracuseStep 1646959 = 2470439) B2470439
theorem B2195879 : Blo 1462551 2195879 := bstep (se 1 (by rfl) ⟨1646909, by rfl⟩ : syracuseStep 2195879 = 3293819) B3293819
theorem B2195963 : Blo 1462551 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B1647175 : Blo 1462551 1647175 := bstep (se 1 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 1647175 = 2470763) B2470763
theorem B2196089 : Blo 1462551 2196089 := bstep (se 2 (by rfl) ⟨823533, by rfl⟩ : syracuseStep 2196089 = 1647067) B1647067
theorem B8331923 : Blo 1462551 8331923 := bstep (se 1 (by rfl) ⟨6248942, by rfl⟩ : syracuseStep 8331923 = 12497885) B12497885
theorem B3515051 : Blo 1462551 3515051 := bstep (se 1 (by rfl) ⟨2636288, by rfl⟩ : syracuseStep 3515051 = 5272577) B5272577
theorem B4940459 : Blo 1462551 4940459 := bstep (se 1 (by rfl) ⟨3705344, by rfl⟩ : syracuseStep 4940459 = 7410689) B7410689
theorem B2196143 : Blo 1462551 2196143 := bstep (se 1 (by rfl) ⟨1647107, by rfl⟩ : syracuseStep 2196143 = 3294215) B3294215
theorem B2196191 : Blo 1462551 2196191 := bstep (se 1 (by rfl) ⟨1647143, by rfl⟩ : syracuseStep 2196191 = 3294287) B3294287
theorem B3564431 : Blo 1462551 3564431 := bstep (se 1 (by rfl) ⟨2673323, by rfl⟩ : syracuseStep 3564431 = 5346647) B5346647
theorem B3294107 : Blo 1462551 3294107 := bstep (se 1 (by rfl) ⟨2470580, by rfl⟩ : syracuseStep 3294107 = 4941161) B4941161
theorem B2638747 : Blo 1462551 2638747 := bstep (se 1 (by rfl) ⟨1979060, by rfl⟩ : syracuseStep 2638747 = 3958121) B3958121
theorem B2196455 : Blo 1462551 2196455 := bstep (se 1 (by rfl) ⟨1647341, by rfl⟩ : syracuseStep 2196455 = 3294683) B3294683
theorem B11109473 : Blo 1462551 11109473 := bstep (se 2 (by rfl) ⟨4166052, by rfl⟩ : syracuseStep 11109473 = 8332105) B8332105
theorem B3294305 : Blo 1462551 3294305 := bstep (se 2 (by rfl) ⟨1235364, by rfl⟩ : syracuseStep 3294305 = 2470729) B2470729
theorem B4940999 : Blo 1462551 4940999 := bstep (se 1 (by rfl) ⟨3705749, by rfl⟩ : syracuseStep 4940999 = 7411499) B7411499
theorem B2196713 : Blo 1462551 2196713 := bstep (se 2 (by rfl) ⟨823767, by rfl⟩ : syracuseStep 2196713 = 1647535) B1647535
theorem B12502259 : Blo 1462551 12502259 := bstep (se 1 (by rfl) ⟨9376694, by rfl⟩ : syracuseStep 12502259 = 18753389) B18753389
theorem B7128313 : Blo 1462551 7128313 := bstep (se 2 (by rfl) ⟨2673117, by rfl⟩ : syracuseStep 7128313 = 5346235) B5346235
theorem B2196767 : Blo 1462551 2196767 := bstep (se 1 (by rfl) ⟨1647575, by rfl⟩ : syracuseStep 2196767 = 3295151) B3295151
theorem B3294503 : Blo 1462551 3294503 := bstep (se 1 (by rfl) ⟨2470877, by rfl⟩ : syracuseStep 3294503 = 4941755) B4941755
theorem B8332631 : Blo 1462551 8332631 := bstep (se 1 (by rfl) ⟨6249473, by rfl⟩ : syracuseStep 8332631 = 12498947) B12498947
theorem B3704201 : Blo 1462551 3704201 := bstep (se 2 (by rfl) ⟨1389075, by rfl⟩ : syracuseStep 3704201 = 2778151) B2778151
theorem B3704251 : Blo 1462551 3704251 := bstep (se 1 (by rfl) ⟨2778188, by rfl⟩ : syracuseStep 3704251 = 5556377) B5556377
theorem B3294881 : Blo 1462551 3294881 := bstep (se 2 (by rfl) ⟨1235580, by rfl⟩ : syracuseStep 3294881 = 2471161) B2471161
theorem B3958433 : Blo 1462551 3958433 := bstep (se 2 (by rfl) ⟨1484412, by rfl⟩ : syracuseStep 3958433 = 2968825) B2968825
theorem B3704555 : Blo 1462551 3704555 := bstep (se 1 (by rfl) ⟨2778416, by rfl⟩ : syracuseStep 3704555 = 5556833) B5556833
theorem B2778887 : Blo 1462551 2778887 := bstep (se 1 (by rfl) ⟨2084165, by rfl⟩ : syracuseStep 2778887 = 4168331) B4168331
theorem B60057449 : Blo 1462551 60057449 := bstep (se 2 (by rfl) ⟨22521543, by rfl⟩ : syracuseStep 60057449 = 45043087) B45043087
theorem B5556073 : Blo 1462551 5556073 := bstep (se 2 (by rfl) ⟨2083527, by rfl⟩ : syracuseStep 5556073 = 4167055) B4167055
theorem B15820751 : Blo 1462551 15820751 := bstep (se 1 (by rfl) ⟨11865563, by rfl⟩ : syracuseStep 15820751 = 23731127) B23731127
theorem B3295241 : Blo 1462551 3295241 := bstep (se 2 (by rfl) ⟨1235715, by rfl⟩ : syracuseStep 3295241 = 2471431) B2471431
theorem B54110387 : Blo 1462551 54110387 := bstep (se 1 (by rfl) ⟨40582790, by rfl⟩ : syracuseStep 54110387 = 81165581) B81165581
theorem B5277881 : Blo 1462551 5277881 := bstep (se 2 (by rfl) ⟨1979205, by rfl⟩ : syracuseStep 5277881 = 3958411) B3958411
theorem B14059813 : Blo 1462551 14059813 := bstep (se 4 (by rfl) ⟨1318107, by rfl⟩ : syracuseStep 14059813 = 2636215) B2636215
theorem B2083163 : Blo 1462551 2083163 := bstep (se 1 (by rfl) ⟨1562372, by rfl⟩ : syracuseStep 2083163 = 3124745) B3124745
theorem B7907827 : Blo 1462551 7907827 := bstep (se 1 (by rfl) ⟨5930870, by rfl⟩ : syracuseStep 7907827 = 11861741) B11861741
theorem B4942511 : Blo 1462551 4942511 := bstep (se 1 (by rfl) ⟨3706883, by rfl⟩ : syracuseStep 4942511 = 7413767) B7413767
theorem B3705527 : Blo 1462551 3705527 := bstep (se 1 (by rfl) ⟨2779145, by rfl⟩ : syracuseStep 3705527 = 5558291) B5558291
theorem B3517175 : Blo 1462551 3517175 := bstep (se 1 (by rfl) ⟨2637881, by rfl⟩ : syracuseStep 3517175 = 5275763) B5275763
theorem B2468839 : Blo 1462551 2468839 := bstep (se 1 (by rfl) ⟨1851629, by rfl⟩ : syracuseStep 2468839 = 3703259) B3703259
theorem B4942835 : Blo 1462551 4942835 := bstep (se 1 (by rfl) ⟨3707126, by rfl⟩ : syracuseStep 4942835 = 7414253) B7414253
theorem B7408907 : Blo 1462551 7408907 := bstep (se 1 (by rfl) ⟨5556680, by rfl⟩ : syracuseStep 7408907 = 11113361) B11113361
theorem B3124831 : Blo 1462551 3124831 := bstep (se 1 (by rfl) ⟨2343623, by rfl⟩ : syracuseStep 3124831 = 4687247) B4687247
theorem B5271149 : Blo 1462551 5271149 := bstep (se 3 (by rfl) ⟨988340, by rfl⟩ : syracuseStep 5271149 = 1976681) B1976681
theorem B3706631 : Blo 1462551 3706631 := bstep (se 1 (by rfl) ⟨2779973, by rfl⟩ : syracuseStep 3706631 = 5559947) B5559947
theorem B3706681 : Blo 1462551 3706681 := bstep (se 2 (by rfl) ⟨1390005, by rfl⟩ : syracuseStep 3706681 = 2780011) B2780011
theorem B7917385 : Blo 1462551 7917385 := bstep (se 2 (by rfl) ⟨2969019, by rfl⟩ : syracuseStep 7917385 = 5938039) B5938039
theorem B4755329 : Blo 1462551 4755329 := bstep (se 2 (by rfl) ⟨1783248, by rfl⟩ : syracuseStep 4755329 = 3566497) B3566497
theorem B2084815 : Blo 1462551 2084815 := bstep (se 1 (by rfl) ⟨1563611, by rfl⟩ : syracuseStep 2084815 = 3127223) B3127223
theorem B37998557 : Blo 1462551 37998557 := bstep (se 3 (by rfl) ⟨7124729, by rfl⟩ : syracuseStep 37998557 = 14249459) B14249459
theorem B3706985 : Blo 1462551 3706985 := bstep (se 2 (by rfl) ⟨1390119, by rfl⟩ : syracuseStep 3706985 = 2780239) B2780239
theorem B28143773 : Blo 1462551 28143773 := bstep (se 3 (by rfl) ⟨5276957, by rfl⟩ : syracuseStep 28143773 = 10553915) B10553915
theorem B8450219 : Blo 1462551 8450219 := bstep (se 1 (by rfl) ⟨6337664, by rfl⟩ : syracuseStep 8450219 = 12675329) B12675329
theorem B14069963 : Blo 1462551 14069963 := bstep (se 1 (by rfl) ⟨10552472, by rfl⟩ : syracuseStep 14069963 = 21104945) B21104945
theorem B5935313 : Blo 1462551 5935313 := bstep (se 2 (by rfl) ⟨2225742, by rfl⟩ : syracuseStep 5935313 = 4451485) B4451485
theorem B1462559 : Blo 1462551 1462559 := bstep (se 1 (by rfl) ⟨1096919, by rfl⟩ : syracuseStep 1462559 = 2193839) B2193839
theorem B1462619 : Blo 1462551 1462619 := bstep (se 1 (by rfl) ⟨1096964, by rfl⟩ : syracuseStep 1462619 = 2193929) B2193929
theorem B1462639 : Blo 1462551 1462639 := bstep (se 1 (by rfl) ⟨1096979, by rfl⟩ : syracuseStep 1462639 = 2193959) B2193959
theorem B1462695 : Blo 1462551 1462695 := bstep (se 1 (by rfl) ⟨1097021, by rfl⟩ : syracuseStep 1462695 = 2194043) B2194043
theorem B1462779 : Blo 1462551 1462779 := bstep (se 1 (by rfl) ⟨1097084, by rfl⟩ : syracuseStep 1462779 = 2194169) B2194169
theorem B4936193 : Blo 1462551 4936193 := bstep (se 2 (by rfl) ⟨1851072, by rfl⟩ : syracuseStep 4936193 = 3702145) B3702145
theorem B1462847 : Blo 1462551 1462847 := bstep (se 1 (by rfl) ⟨1097135, by rfl⟩ : syracuseStep 1462847 = 2194271) B2194271
theorem B1462855 : Blo 1462551 1462855 := bstep (se 1 (by rfl) ⟨1097141, by rfl⟩ : syracuseStep 1462855 = 2194283) B2194283
theorem B10547833 : Blo 1462551 10547833 := bstep (se 2 (by rfl) ⟨3955437, by rfl⟩ : syracuseStep 10547833 = 7910875) B7910875
theorem B25014905 : Blo 1462551 25014905 := bstep (se 2 (by rfl) ⟨9380589, by rfl⟩ : syracuseStep 25014905 = 18761179) B18761179
theorem B18748057 : Blo 1462551 18748057 := bstep (se 2 (by rfl) ⟨7030521, by rfl⟩ : syracuseStep 18748057 = 14061043) B14061043
theorem B1463007 : Blo 1462551 1463007 := bstep (se 1 (by rfl) ⟨1097255, by rfl⟩ : syracuseStep 1463007 = 2194511) B2194511
theorem B4690655 : Blo 1462551 4690655 := bstep (se 1 (by rfl) ⟨3517991, by rfl⟩ : syracuseStep 4690655 = 7035983) B7035983
theorem B1463087 : Blo 1462551 1463087 := bstep (se 1 (by rfl) ⟨1097315, by rfl⟩ : syracuseStep 1463087 = 2194631) B2194631
theorem B7410527 : Blo 1462551 7410527 := bstep (se 1 (by rfl) ⟨5557895, by rfl⟩ : syracuseStep 7410527 = 11115791) B11115791
theorem B1463195 : Blo 1462551 1463195 := bstep (se 1 (by rfl) ⟨1097396, by rfl⟩ : syracuseStep 1463195 = 2194793) B2194793
theorem B25342895 : Blo 1462551 25342895 := bstep (se 1 (by rfl) ⟨19007171, by rfl⟩ : syracuseStep 25342895 = 38014343) B38014343
theorem B1463247 : Blo 1462551 1463247 := bstep (se 1 (by rfl) ⟨1097435, by rfl⟩ : syracuseStep 1463247 = 2194871) B2194871
theorem B4936679 : Blo 1462551 4936679 := bstep (se 1 (by rfl) ⟨3702509, by rfl⟩ : syracuseStep 4936679 = 7405019) B7405019
theorem B1463271 : Blo 1462551 1463271 := bstep (se 1 (by rfl) ⟨1097453, by rfl⟩ : syracuseStep 1463271 = 2194907) B2194907
theorem B12506359 : Blo 1462551 12506359 := bstep (se 1 (by rfl) ⟨9379769, by rfl⟩ : syracuseStep 12506359 = 18759539) B18759539
theorem B1463583 : Blo 1462551 1463583 := bstep (se 1 (by rfl) ⟨1097687, by rfl⟩ : syracuseStep 1463583 = 2195375) B2195375
theorem B4937003 : Blo 1462551 4937003 := bstep (se 1 (by rfl) ⟨3702752, by rfl⟩ : syracuseStep 4937003 = 7405505) B7405505
theorem B1463643 : Blo 1462551 1463643 := bstep (se 1 (by rfl) ⟨1097732, by rfl⟩ : syracuseStep 1463643 = 2195465) B2195465
theorem B20034911 : Blo 1462551 20034911 := bstep (se 1 (by rfl) ⟨15026183, by rfl⟩ : syracuseStep 20034911 = 30052367) B30052367
theorem B1463663 : Blo 1462551 1463663 := bstep (se 1 (by rfl) ⟨1097747, by rfl⟩ : syracuseStep 1463663 = 2195495) B2195495
theorem B1463719 : Blo 1462551 1463719 := bstep (se 1 (by rfl) ⟨1097789, by rfl⟩ : syracuseStep 1463719 = 2195579) B2195579
theorem B4167101 : Blo 1462551 4167101 := bstep (se 3 (by rfl) ⟨781331, by rfl⟩ : syracuseStep 4167101 = 1562663) B1562663
theorem B15832513 : Blo 1462551 15832513 := bstep (se 2 (by rfl) ⟨5937192, by rfl⟩ : syracuseStep 15832513 = 11874385) B11874385
theorem B1463803 : Blo 1462551 1463803 := bstep (se 1 (by rfl) ⟨1097852, by rfl⟩ : syracuseStep 1463803 = 2195705) B2195705
theorem B4937273 : Blo 1462551 4937273 := bstep (se 2 (by rfl) ⟨1851477, by rfl⟩ : syracuseStep 4937273 = 3702955) B3702955
theorem B1463871 : Blo 1462551 1463871 := bstep (se 1 (by rfl) ⟨1097903, by rfl⟩ : syracuseStep 1463871 = 2195807) B2195807
theorem B1463879 : Blo 1462551 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B6248123 : Blo 1462551 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B1464031 : Blo 1462551 1464031 := bstep (se 1 (by rfl) ⟨1098023, by rfl⟩ : syracuseStep 1464031 = 2196047) B2196047
theorem B3290921 : Blo 1462551 3290921 := bstep (se 2 (by rfl) ⟨1234095, by rfl⟩ : syracuseStep 3290921 = 2468191) B2468191
theorem B1464111 : Blo 1462551 1464111 := bstep (se 1 (by rfl) ⟨1098083, by rfl⟩ : syracuseStep 1464111 = 2196167) B2196167
theorem B1464219 : Blo 1462551 1464219 := bstep (se 1 (by rfl) ⟨1098164, by rfl⟩ : syracuseStep 1464219 = 2196329) B2196329
theorem B1464271 : Blo 1462551 1464271 := bstep (se 1 (by rfl) ⟨1098203, by rfl⟩ : syracuseStep 1464271 = 2196407) B2196407
theorem B1464295 : Blo 1462551 1464295 := bstep (se 1 (by rfl) ⟨1098221, by rfl⟩ : syracuseStep 1464295 = 2196443) B2196443
theorem B1759207 : Blo 1462551 1759207 := bstep (se 1 (by rfl) ⟨1319405, by rfl⟩ : syracuseStep 1759207 = 2638811) B2638811
theorem B31651883 : Blo 1462551 31651883 := bstep (se 1 (by rfl) ⟨23738912, by rfl⟩ : syracuseStep 31651883 = 47477825) B47477825
theorem B6338845 : Blo 1462551 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B3168695 : Blo 1462551 3168695 := bstep (se 1 (by rfl) ⟨2376521, by rfl⟩ : syracuseStep 3168695 = 4753043) B4753043
theorem B2193983 : Blo 1462551 2193983 := bstep (se 1 (by rfl) ⟨1645487, by rfl⟩ : syracuseStep 2193983 = 3290975) B3290975
theorem B11262527 : Blo 1462551 11262527 := bstep (se 1 (by rfl) ⟨8446895, by rfl⟩ : syracuseStep 11262527 = 16893791) B16893791
theorem B5634623 : Blo 1462551 5634623 := bstep (se 1 (by rfl) ⟨4225967, by rfl⟩ : syracuseStep 5634623 = 8451935) B8451935
theorem B12499595 : Blo 1462551 12499595 := bstep (se 1 (by rfl) ⟨9374696, by rfl⟩ : syracuseStep 12499595 = 18749393) B18749393
theorem B18766511 : Blo 1462551 18766511 := bstep (se 1 (by rfl) ⟨14074883, by rfl⟩ : syracuseStep 18766511 = 28149767) B28149767
theorem B2194103 : Blo 1462551 2194103 := bstep (se 1 (by rfl) ⟨1645577, by rfl⟩ : syracuseStep 2194103 = 3291155) B3291155
theorem B6249149 : Blo 1462551 6249149 := bstep (se 3 (by rfl) ⟨1171715, by rfl⟩ : syracuseStep 6249149 = 2343431) B2343431
theorem B10549997 : Blo 1462551 10549997 := bstep (se 3 (by rfl) ⟨1978124, by rfl⟩ : syracuseStep 10549997 = 3956249) B3956249
theorem B7412471 : Blo 1462551 7412471 := bstep (se 1 (by rfl) ⟨5559353, by rfl⟩ : syracuseStep 7412471 = 11118707) B11118707
theorem B4938515 : Blo 1462551 4938515 := bstep (se 1 (by rfl) ⟨3703886, by rfl⟩ : syracuseStep 4938515 = 7407773) B7407773
theorem B7912259 : Blo 1462551 7912259 := bstep (se 1 (by rfl) ⟨5934194, by rfl⟩ : syracuseStep 7912259 = 11868389) B11868389
theorem B3291983 : Blo 1462551 3291983 := bstep (se 1 (by rfl) ⟨2468987, by rfl⟩ : syracuseStep 3291983 = 4937975) B4937975
theorem B2194331 : Blo 1462551 2194331 := bstep (se 1 (by rfl) ⟨1645748, by rfl⟩ : syracuseStep 2194331 = 3291497) B3291497
theorem B1645519 : Blo 1462551 1645519 := bstep (se 1 (by rfl) ⟨1234139, by rfl⟩ : syracuseStep 1645519 = 2468279) B2468279
theorem B6675443 : Blo 1462551 6675443 := bstep (se 1 (by rfl) ⟨5006582, by rfl⟩ : syracuseStep 6675443 = 10013165) B10013165
theorem B3292199 : Blo 1462551 3292199 := bstep (se 1 (by rfl) ⟨2469149, by rfl⟩ : syracuseStep 3292199 = 4938299) B4938299
theorem B3292379 : Blo 1462551 3292379 := bstep (se 1 (by rfl) ⟨2469284, by rfl⟩ : syracuseStep 3292379 = 4938569) B4938569
theorem B7912669 : Blo 1462551 7912669 := bstep (se 3 (by rfl) ⟨1483625, by rfl⟩ : syracuseStep 7912669 = 2967251) B2967251
theorem B7412957 : Blo 1462551 7412957 := bstep (se 3 (by rfl) ⟨1389929, by rfl⟩ : syracuseStep 7412957 = 2779859) B2779859
theorem B24993035 : Blo 1462551 24993035 := bstep (se 1 (by rfl) ⟨18744776, by rfl⟩ : syracuseStep 24993035 = 37489553) B37489553
theorem B2194727 : Blo 1462551 2194727 := bstep (se 1 (by rfl) ⟨1646045, by rfl⟩ : syracuseStep 2194727 = 3292091) B3292091
theorem B2637095 : Blo 1462551 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B1645915 : Blo 1462551 1645915 := bstep (se 1 (by rfl) ⟨1234436, by rfl⟩ : syracuseStep 1645915 = 2468873) B2468873
theorem B7511393 : Blo 1462551 7511393 := bstep (se 2 (by rfl) ⟨2816772, by rfl⟩ : syracuseStep 7511393 = 5633545) B5633545
theorem B2194811 : Blo 1462551 2194811 := bstep (se 1 (by rfl) ⟨1646108, by rfl⟩ : syracuseStep 2194811 = 3292217) B3292217
theorem B3292577 : Blo 1462551 3292577 := bstep (se 2 (by rfl) ⟨1234716, by rfl⟩ : syracuseStep 3292577 = 2469433) B2469433
theorem B1646023 : Blo 1462551 1646023 := bstep (se 1 (by rfl) ⟨1234517, by rfl⟩ : syracuseStep 1646023 = 2469035) B2469035
theorem B2194937 : Blo 1462551 2194937 := bstep (se 2 (by rfl) ⟨823101, by rfl⟩ : syracuseStep 2194937 = 1646203) B1646203
theorem B9371159 : Blo 1462551 9371159 := bstep (se 1 (by rfl) ⟨7028369, by rfl⟩ : syracuseStep 9371159 = 14056739) B14056739
theorem B2195039 : Blo 1462551 2195039 := bstep (se 1 (by rfl) ⟨1646279, by rfl⟩ : syracuseStep 2195039 = 3292559) B3292559
theorem B4939379 : Blo 1462551 4939379 := bstep (se 1 (by rfl) ⟨3704534, by rfl⟩ : syracuseStep 4939379 = 7409069) B7409069
theorem B1851103 : Blo 1462551 1851103 := bstep (se 1 (by rfl) ⟨1388327, by rfl⟩ : syracuseStep 1851103 = 2776655) B2776655
theorem B15818503 : Blo 1462551 15818503 := bstep (se 1 (by rfl) ⟨11863877, by rfl⟩ : syracuseStep 15818503 = 23727755) B23727755
theorem B28532513 : Blo 1462551 28532513 := bstep (se 2 (by rfl) ⟨10699692, by rfl⟩ : syracuseStep 28532513 = 21399385) B21399385
theorem B1646383 : Blo 1462551 1646383 := bstep (se 1 (by rfl) ⟨1234787, by rfl⟩ : syracuseStep 1646383 = 2469575) B2469575
theorem B2195255 : Blo 1462551 2195255 := bstep (se 1 (by rfl) ⟨1646441, by rfl⟩ : syracuseStep 2195255 = 3292883) B3292883
theorem B4939649 : Blo 1462551 4939649 := bstep (se 2 (by rfl) ⟨1852368, by rfl⟩ : syracuseStep 4939649 = 3704737) B3704737
theorem B1646491 : Blo 1462551 1646491 := bstep (se 1 (by rfl) ⟨1234868, by rfl⟩ : syracuseStep 1646491 = 2469737) B2469737
theorem B5349277 : Blo 1462551 5349277 := bstep (se 3 (by rfl) ⟨1002989, by rfl⟩ : syracuseStep 5349277 = 2005979) B2005979
theorem B202670009 : Blo 1462551 202670009 := bstep (se 2 (by rfl) ⟨76001253, by rfl⟩ : syracuseStep 202670009 = 152002507) B152002507
theorem B3293135 : Blo 1462551 3293135 := bstep (se 1 (by rfl) ⟨2469851, by rfl⟩ : syracuseStep 3293135 = 4939703) B4939703
theorem B9379975 : Blo 1462551 9379975 := bstep (se 1 (by rfl) ⟨7034981, by rfl⟩ : syracuseStep 9379975 = 14069963) B14069963
theorem B2195675 : Blo 1462551 2195675 := bstep (se 1 (by rfl) ⟨1646756, by rfl⟩ : syracuseStep 2195675 = 3293513) B3293513
theorem B2343143 : Blo 1462551 2343143 := bstep (se 1 (by rfl) ⟨1757357, by rfl⟩ : syracuseStep 2343143 = 3514715) B3514715
theorem B2195687 : Blo 1462551 2195687 := bstep (se 1 (by rfl) ⟨1646765, by rfl⟩ : syracuseStep 2195687 = 3293531) B3293531
theorem B2195849 : Blo 1462551 2195849 := bstep (se 2 (by rfl) ⟨823443, by rfl⟩ : syracuseStep 2195849 = 1646887) B1646887
theorem B5554615 : Blo 1462551 5554615 := bstep (se 1 (by rfl) ⟨4165961, by rfl⟩ : syracuseStep 5554615 = 8331923) B8331923
theorem B2343367 : Blo 1462551 2343367 := bstep (se 1 (by rfl) ⟨1757525, by rfl⟩ : syracuseStep 2343367 = 3515051) B3515051
theorem B3293639 : Blo 1462551 3293639 := bstep (se 1 (by rfl) ⟨2470229, by rfl⟩ : syracuseStep 3293639 = 4940459) B4940459
theorem B144294365 : Blo 1462551 144294365 := bstep (se 3 (by rfl) ⟨27055193, by rfl⟩ : syracuseStep 144294365 = 54110387) B54110387
theorem B2195945 : Blo 1462551 2195945 := bstep (se 2 (by rfl) ⟨823479, by rfl⟩ : syracuseStep 2195945 = 1646959) B1646959
theorem B15827501 : Blo 1462551 15827501 := bstep (se 3 (by rfl) ⟨2967656, by rfl⟩ : syracuseStep 15827501 = 5935313) B5935313
theorem B4940351 : Blo 1462551 4940351 := bstep (se 1 (by rfl) ⟨3705263, by rfl⟩ : syracuseStep 4940351 = 7410527) B7410527
theorem B2376287 : Blo 1462551 2376287 := bstep (se 1 (by rfl) ⟨1782215, by rfl⟩ : syracuseStep 2376287 = 3564431) B3564431
theorem B2196071 : Blo 1462551 2196071 := bstep (se 1 (by rfl) ⟨1647053, by rfl⟩ : syracuseStep 2196071 = 3294107) B3294107
theorem B10543769 : Blo 1462551 10543769 := bstep (se 2 (by rfl) ⟨3953913, by rfl⟩ : syracuseStep 10543769 = 7907827) B7907827
theorem B7406315 : Blo 1462551 7406315 := bstep (se 1 (by rfl) ⟨5554736, by rfl⟩ : syracuseStep 7406315 = 11109473) B11109473
theorem B2196203 : Blo 1462551 2196203 := bstep (se 1 (by rfl) ⟨1647152, by rfl⟩ : syracuseStep 2196203 = 3294305) B3294305
theorem B2196233 : Blo 1462551 2196233 := bstep (se 2 (by rfl) ⟨823587, by rfl⟩ : syracuseStep 2196233 = 1647175) B1647175
theorem B3293999 : Blo 1462551 3293999 := bstep (se 1 (by rfl) ⟨2470499, by rfl⟩ : syracuseStep 3293999 = 4940999) B4940999
theorem B2196335 : Blo 1462551 2196335 := bstep (se 1 (by rfl) ⟨1647251, by rfl⟩ : syracuseStep 2196335 = 3294503) B3294503
theorem B5555087 : Blo 1462551 5555087 := bstep (se 1 (by rfl) ⟨4166315, by rfl⟩ : syracuseStep 5555087 = 8332631) B8332631
theorem B5555101 : Blo 1462551 5555101 := bstep (se 3 (by rfl) ⟨1041581, by rfl⟩ : syracuseStep 5555101 = 2083163) B2083163
theorem B2778067 : Blo 1462551 2778067 := bstep (se 1 (by rfl) ⟨2083550, by rfl⟩ : syracuseStep 2778067 = 4167101) B4167101
theorem B2196587 : Blo 1462551 2196587 := bstep (se 1 (by rfl) ⟨1647440, by rfl⟩ : syracuseStep 2196587 = 3294881) B3294881
theorem B2638955 : Blo 1462551 2638955 := bstep (se 1 (by rfl) ⟨1979216, by rfl⟩ : syracuseStep 2638955 = 3958433) B3958433
theorem B2196827 : Blo 1462551 2196827 := bstep (se 1 (by rfl) ⟨1647620, by rfl⟩ : syracuseStep 2196827 = 3295241) B3295241
theorem B8333063 : Blo 1462551 8333063 := bstep (se 1 (by rfl) ⟨6249797, by rfl⟩ : syracuseStep 8333063 = 12499595) B12499595
theorem B3295007 : Blo 1462551 3295007 := bstep (se 1 (by rfl) ⟨2471255, by rfl⟩ : syracuseStep 3295007 = 4942511) B4942511
theorem B12511007 : Blo 1462551 12511007 := bstep (se 1 (by rfl) ⟨9383255, by rfl⟩ : syracuseStep 12511007 = 18766511) B18766511
theorem B2344783 : Blo 1462551 2344783 := bstep (se 1 (by rfl) ⟨1758587, by rfl⟩ : syracuseStep 2344783 = 3517175) B3517175
theorem B4941647 : Blo 1462551 4941647 := bstep (se 1 (by rfl) ⟨3706235, by rfl⟩ : syracuseStep 4941647 = 7412471) B7412471
theorem B4450295 : Blo 1462551 4450295 := bstep (se 1 (by rfl) ⟨3337721, by rfl⟩ : syracuseStep 4450295 = 6675443) B6675443
theorem B3295223 : Blo 1462551 3295223 := bstep (se 1 (by rfl) ⟨2471417, by rfl⟩ : syracuseStep 3295223 = 4942835) B4942835
theorem B4941971 : Blo 1462551 4941971 := bstep (se 1 (by rfl) ⟨3706478, by rfl⟩ : syracuseStep 4941971 = 7412957) B7412957
theorem B5007595 : Blo 1462551 5007595 := bstep (se 1 (by rfl) ⟨3755696, by rfl⟩ : syracuseStep 5007595 = 7511393) B7511393
theorem B2468137 : Blo 1462551 2468137 := bstep (se 2 (by rfl) ⟨925551, by rfl⟩ : syracuseStep 2468137 = 1851103) B1851103
theorem B4942241 : Blo 1462551 4942241 := bstep (se 2 (by rfl) ⟨1853340, by rfl⟩ : syracuseStep 4942241 = 3706681) B3706681
theorem B7408097 : Blo 1462551 7408097 := bstep (se 2 (by rfl) ⟨2778036, by rfl⟩ : syracuseStep 7408097 = 5556073) B5556073
theorem B2779753 : Blo 1462551 2779753 := bstep (se 2 (by rfl) ⟨1042407, by rfl⟩ : syracuseStep 2779753 = 2084815) B2084815
theorem B135113339 : Blo 1462551 135113339 := bstep (se 1 (by rfl) ⟨101335004, by rfl⟩ : syracuseStep 135113339 = 202670009) B202670009
theorem B2345609 : Blo 1462551 2345609 := bstep (se 2 (by rfl) ⟨879603, by rfl⟩ : syracuseStep 2345609 = 1759207) B1759207
theorem B25332371 : Blo 1462551 25332371 := bstep (se 1 (by rfl) ⟨18999278, by rfl⟩ : syracuseStep 25332371 = 37998557) B37998557
theorem B18762515 : Blo 1462551 18762515 := bstep (se 1 (by rfl) ⟨14071886, by rfl⟩ : syracuseStep 18762515 = 28143773) B28143773
theorem B18746417 : Blo 1462551 18746417 := bstep (se 2 (by rfl) ⟨7029906, by rfl⟩ : syracuseStep 18746417 = 14059813) B14059813
theorem B16895263 : Blo 1462551 16895263 := bstep (se 1 (by rfl) ⟨12671447, by rfl⟩ : syracuseStep 16895263 = 25342895) B25342895
theorem B7032253 : Blo 1462551 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B8334839 : Blo 1462551 8334839 := bstep (se 1 (by rfl) ⟨6251129, by rfl⟩ : syracuseStep 8334839 = 12502259) B12502259
theorem B24997409 : Blo 1462551 24997409 := bstep (se 2 (by rfl) ⟨9374028, by rfl⟩ : syracuseStep 24997409 = 18748057) B18748057
theorem B2469467 : Blo 1462551 2469467 := bstep (se 1 (by rfl) ⟨1852100, by rfl⟩ : syracuseStep 2469467 = 3704201) B3704201
theorem B4165415 : Blo 1462551 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B2469703 : Blo 1462551 2469703 := bstep (se 1 (by rfl) ⟨1852277, by rfl⟩ : syracuseStep 2469703 = 3704555) B3704555
theorem B3518329 : Blo 1462551 3518329 := bstep (se 2 (by rfl) ⟨1319373, by rfl⟩ : syracuseStep 3518329 = 2638747) B2638747
theorem B40038299 : Blo 1462551 40038299 := bstep (se 1 (by rfl) ⟨30028724, by rfl⟩ : syracuseStep 40038299 = 60057449) B60057449
theorem B10547167 : Blo 1462551 10547167 := bstep (se 1 (by rfl) ⟨7910375, by rfl⟩ : syracuseStep 10547167 = 15820751) B15820751
theorem B3518587 : Blo 1462551 3518587 := bstep (se 1 (by rfl) ⟨2638940, by rfl⟩ : syracuseStep 3518587 = 5277881) B5277881
theorem B16675145 : Blo 1462551 16675145 := bstep (se 2 (by rfl) ⟨6253179, by rfl⟩ : syracuseStep 16675145 = 12506359) B12506359
theorem B1462655 : Blo 1462551 1462655 := bstep (se 1 (by rfl) ⟨1096991, by rfl⟩ : syracuseStep 1462655 = 2193983) B2193983
theorem B7508351 : Blo 1462551 7508351 := bstep (se 1 (by rfl) ⟨5631263, by rfl⟩ : syracuseStep 7508351 = 11262527) B11262527
theorem B3756415 : Blo 1462551 3756415 := bstep (se 1 (by rfl) ⟨2817311, by rfl⟩ : syracuseStep 3756415 = 5634623) B5634623
theorem B1462735 : Blo 1462551 1462735 := bstep (se 1 (by rfl) ⟨1097051, by rfl⟩ : syracuseStep 1462735 = 2194103) B2194103
theorem B2470351 : Blo 1462551 2470351 := bstep (se 1 (by rfl) ⟨1852763, by rfl⟩ : syracuseStep 2470351 = 3705527) B3705527
theorem B4166099 : Blo 1462551 4166099 := bstep (se 1 (by rfl) ⟨3124574, by rfl⟩ : syracuseStep 4166099 = 6249149) B6249149
theorem B7033331 : Blo 1462551 7033331 := bstep (se 1 (by rfl) ⟨5274998, by rfl⟩ : syracuseStep 7033331 = 10549997) B10549997
theorem B1462887 : Blo 1462551 1462887 := bstep (se 1 (by rfl) ⟨1097165, by rfl⟩ : syracuseStep 1462887 = 2194331) B2194331
theorem B7410365 : Blo 1462551 7410365 := bstep (se 3 (by rfl) ⟨1389443, by rfl⟩ : syracuseStep 7410365 = 2778887) B2778887
theorem B4166441 : Blo 1462551 4166441 := bstep (se 2 (by rfl) ⟨1562415, by rfl⟩ : syracuseStep 4166441 = 3124831) B3124831
theorem B1463151 : Blo 1462551 1463151 := bstep (se 1 (by rfl) ⟨1097363, by rfl⟩ : syracuseStep 1463151 = 2194727) B2194727
theorem B1463207 : Blo 1462551 1463207 := bstep (se 1 (by rfl) ⟨1097405, by rfl⟩ : syracuseStep 1463207 = 2194811) B2194811
theorem B1463291 : Blo 1462551 1463291 := bstep (se 1 (by rfl) ⟨1097468, by rfl⟩ : syracuseStep 1463291 = 2194937) B2194937
theorem B84440069 : Blo 1462551 84440069 := bstep (se 4 (by rfl) ⟨7916256, by rfl⟩ : syracuseStep 84440069 = 15832513) B15832513
theorem B21091337 : Blo 1462551 21091337 := bstep (se 2 (by rfl) ⟨7909251, by rfl⟩ : syracuseStep 21091337 = 15818503) B15818503
theorem B6247439 : Blo 1462551 6247439 := bstep (se 1 (by rfl) ⟨4685579, by rfl⟩ : syracuseStep 6247439 = 9371159) B9371159
theorem B1463359 : Blo 1462551 1463359 := bstep (se 1 (by rfl) ⟨1097519, by rfl⟩ : syracuseStep 1463359 = 2195039) B2195039
theorem B10556513 : Blo 1462551 10556513 := bstep (se 2 (by rfl) ⟨3958692, by rfl⟩ : syracuseStep 10556513 = 7917385) B7917385
theorem B2471087 : Blo 1462551 2471087 := bstep (se 1 (by rfl) ⟨1853315, by rfl⟩ : syracuseStep 2471087 = 3706631) B3706631
theorem B1463503 : Blo 1462551 1463503 := bstep (se 1 (by rfl) ⟨1097627, by rfl⟩ : syracuseStep 1463503 = 2195255) B2195255
theorem B7132369 : Blo 1462551 7132369 := bstep (se 2 (by rfl) ⟨2674638, by rfl⟩ : syracuseStep 7132369 = 5349277) B5349277
theorem B4937057 : Blo 1462551 4937057 := bstep (se 2 (by rfl) ⟨1851396, by rfl⟩ : syracuseStep 4937057 = 3702793) B3702793
theorem B11113847 : Blo 1462551 11113847 := bstep (se 1 (by rfl) ⟨8335385, by rfl⟩ : syracuseStep 11113847 = 16670771) B16670771
theorem B1463707 : Blo 1462551 1463707 := bstep (se 1 (by rfl) ⟨1097780, by rfl⟩ : syracuseStep 1463707 = 2195561) B2195561
theorem B2471323 : Blo 1462551 2471323 := bstep (se 1 (by rfl) ⟨1853492, by rfl⟩ : syracuseStep 2471323 = 3706985) B3706985
theorem B5633479 : Blo 1462551 5633479 := bstep (se 1 (by rfl) ⟨4225109, by rfl⟩ : syracuseStep 5633479 = 8450219) B8450219
theorem B1463919 : Blo 1462551 1463919 := bstep (se 1 (by rfl) ⟨1097939, by rfl⟩ : syracuseStep 1463919 = 2195879) B2195879
theorem B1463975 : Blo 1462551 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B3290795 : Blo 1462551 3290795 := bstep (se 1 (by rfl) ⟨2468096, by rfl⟩ : syracuseStep 3290795 = 4936193) B4936193
theorem B8451793 : Blo 1462551 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B1464059 : Blo 1462551 1464059 := bstep (se 1 (by rfl) ⟨1098044, by rfl⟩ : syracuseStep 1464059 = 2196089) B2196089
theorem B16676603 : Blo 1462551 16676603 := bstep (se 1 (by rfl) ⟨12507452, by rfl⟩ : syracuseStep 16676603 = 25014905) B25014905
theorem B1464095 : Blo 1462551 1464095 := bstep (se 1 (by rfl) ⟨1098071, by rfl⟩ : syracuseStep 1464095 = 2196143) B2196143
theorem B1464127 : Blo 1462551 1464127 := bstep (se 1 (by rfl) ⟨1098095, by rfl⟩ : syracuseStep 1464127 = 2196191) B2196191
theorem B3127103 : Blo 1462551 3127103 := bstep (se 1 (by rfl) ⟨2345327, by rfl⟩ : syracuseStep 3127103 = 4690655) B4690655
theorem B3291119 : Blo 1462551 3291119 := bstep (se 1 (by rfl) ⟨2468339, by rfl⟩ : syracuseStep 3291119 = 4936679) B4936679
theorem B1464303 : Blo 1462551 1464303 := bstep (se 1 (by rfl) ⟨1098227, by rfl⟩ : syracuseStep 1464303 = 2196455) B2196455
theorem B1464475 : Blo 1462551 1464475 := bstep (se 1 (by rfl) ⟨1098356, by rfl⟩ : syracuseStep 1464475 = 2196713) B2196713
theorem B14063777 : Blo 1462551 14063777 := bstep (se 2 (by rfl) ⟨5273916, by rfl⟩ : syracuseStep 14063777 = 10547833) B10547833
theorem B1464511 : Blo 1462551 1464511 := bstep (se 1 (by rfl) ⟨1098383, by rfl⟩ : syracuseStep 1464511 = 2196767) B2196767
theorem B3291335 : Blo 1462551 3291335 := bstep (se 1 (by rfl) ⟨2468501, by rfl⟩ : syracuseStep 3291335 = 4937003) B4937003
theorem B53426429 : Blo 1462551 53426429 := bstep (se 3 (by rfl) ⟨10017455, by rfl⟩ : syracuseStep 53426429 = 20034911) B20034911
theorem B3291515 : Blo 1462551 3291515 := bstep (se 1 (by rfl) ⟨2468636, by rfl⟩ : syracuseStep 3291515 = 4937273) B4937273
theorem B2193947 : Blo 1462551 2193947 := bstep (se 1 (by rfl) ⟨1645460, by rfl⟩ : syracuseStep 2193947 = 3290921) B3290921
theorem B2194025 : Blo 1462551 2194025 := bstep (se 2 (by rfl) ⟨822759, by rfl⟩ : syracuseStep 2194025 = 1645519) B1645519
theorem B38017669 : Blo 1462551 38017669 := bstep (se 4 (by rfl) ⟨3564156, by rfl⟩ : syracuseStep 38017669 = 7128313) B7128313
theorem B3291785 : Blo 1462551 3291785 := bstep (se 2 (by rfl) ⟨1234419, by rfl⟩ : syracuseStep 3291785 = 2468839) B2468839
theorem B21101255 : Blo 1462551 21101255 := bstep (se 1 (by rfl) ⟨15825941, by rfl⟩ : syracuseStep 21101255 = 31651883) B31651883
theorem B2112463 : Blo 1462551 2112463 := bstep (se 1 (by rfl) ⟨1584347, by rfl⟩ : syracuseStep 2112463 = 3168695) B3168695
theorem B10550225 : Blo 1462551 10550225 := bstep (se 2 (by rfl) ⟨3956334, by rfl⟩ : syracuseStep 10550225 = 7912669) B7912669
theorem B2194553 : Blo 1462551 2194553 := bstep (se 2 (by rfl) ⟨822957, by rfl⟩ : syracuseStep 2194553 = 1645915) B1645915
theorem B3292343 : Blo 1462551 3292343 := bstep (se 1 (by rfl) ⟨2469257, by rfl⟩ : syracuseStep 3292343 = 4938515) B4938515
theorem B5274839 : Blo 1462551 5274839 := bstep (se 1 (by rfl) ⟨3956129, by rfl⟩ : syracuseStep 5274839 = 7912259) B7912259
theorem B2194655 : Blo 1462551 2194655 := bstep (se 1 (by rfl) ⟨1645991, by rfl⟩ : syracuseStep 2194655 = 3291983) B3291983
theorem B4939001 : Blo 1462551 4939001 := bstep (se 2 (by rfl) ⟨1852125, by rfl⟩ : syracuseStep 4939001 = 3704251) B3704251
theorem B2194697 : Blo 1462551 2194697 := bstep (se 2 (by rfl) ⟨823011, by rfl⟩ : syracuseStep 2194697 = 1646023) B1646023
theorem B2194799 : Blo 1462551 2194799 := bstep (se 1 (by rfl) ⟨1646099, by rfl⟩ : syracuseStep 2194799 = 3292199) B3292199
theorem B76086701 : Blo 1462551 76086701 := bstep (se 3 (by rfl) ⟨14266256, by rfl⟩ : syracuseStep 76086701 = 28532513) B28532513
theorem B2194919 : Blo 1462551 2194919 := bstep (se 1 (by rfl) ⟨1646189, by rfl⟩ : syracuseStep 2194919 = 3292379) B3292379
theorem B16662023 : Blo 1462551 16662023 := bstep (se 1 (by rfl) ⟨12496517, by rfl⟩ : syracuseStep 16662023 = 24993035) B24993035
theorem B4939271 : Blo 1462551 4939271 := bstep (se 1 (by rfl) ⟨3704453, by rfl⟩ : syracuseStep 4939271 = 7408907) B7408907
theorem B2195051 : Blo 1462551 2195051 := bstep (se 1 (by rfl) ⟨1646288, by rfl⟩ : syracuseStep 2195051 = 3292577) B3292577
theorem B2195177 : Blo 1462551 2195177 := bstep (se 2 (by rfl) ⟨823191, by rfl⟩ : syracuseStep 2195177 = 1646383) B1646383
theorem B3514099 : Blo 1462551 3514099 := bstep (se 1 (by rfl) ⟨2635574, by rfl⟩ : syracuseStep 3514099 = 5271149) B5271149
theorem B3292919 : Blo 1462551 3292919 := bstep (se 1 (by rfl) ⟨2469689, by rfl⟩ : syracuseStep 3292919 = 4939379) B4939379
theorem B2195321 : Blo 1462551 2195321 := bstep (se 2 (by rfl) ⟨823245, by rfl⟩ : syracuseStep 2195321 = 1646491) B1646491
theorem B3293099 : Blo 1462551 3293099 := bstep (se 1 (by rfl) ⟨2469824, by rfl⟩ : syracuseStep 3293099 = 4939649) B4939649
theorem B3170219 : Blo 1462551 3170219 := bstep (se 1 (by rfl) ⟨2377664, by rfl⟩ : syracuseStep 3170219 = 4755329) B4755329
theorem B2195423 : Blo 1462551 2195423 := bstep (se 1 (by rfl) ⟨1646567, by rfl⟩ : syracuseStep 2195423 = 3293135) B3293135
theorem B11116763 : Blo 1462551 11116763 := bstep (se 1 (by rfl) ⟨8337572, by rfl⟩ : syracuseStep 11116763 = 16675145) B16675145
theorem B5005567 : Blo 1462551 5005567 := bstep (se 1 (by rfl) ⟨3754175, by rfl⟩ : syracuseStep 5005567 = 7508351) B7508351
theorem B2195759 : Blo 1462551 2195759 := bstep (se 1 (by rfl) ⟨1646819, by rfl⟩ : syracuseStep 2195759 = 3293639) B3293639
theorem B2777399 : Blo 1462551 2777399 := bstep (se 1 (by rfl) ⟨2083049, by rfl⟩ : syracuseStep 2777399 = 4166099) B4166099
theorem B6676793 : Blo 1462551 6676793 := bstep (se 2 (by rfl) ⟨2503797, by rfl⟩ : syracuseStep 6676793 = 5007595) B5007595
theorem B10551667 : Blo 1462551 10551667 := bstep (se 1 (by rfl) ⟨7913750, by rfl⟩ : syracuseStep 10551667 = 15827501) B15827501
theorem B3293567 : Blo 1462551 3293567 := bstep (se 1 (by rfl) ⟨2470175, by rfl⟩ : syracuseStep 3293567 = 4940351) B4940351
theorem B7029179 : Blo 1462551 7029179 := bstep (se 1 (by rfl) ⟨5271884, by rfl⟩ : syracuseStep 7029179 = 10543769) B10543769
theorem B4940243 : Blo 1462551 4940243 := bstep (se 1 (by rfl) ⟨3705182, by rfl⟩ : syracuseStep 4940243 = 7410365) B7410365
theorem B2777627 : Blo 1462551 2777627 := bstep (se 1 (by rfl) ⟨2083220, by rfl⟩ : syracuseStep 2777627 = 4166441) B4166441
theorem B2195999 : Blo 1462551 2195999 := bstep (se 1 (by rfl) ⟨1646999, by rfl⟩ : syracuseStep 2195999 = 3293999) B3293999
theorem B14066237 : Blo 1462551 14066237 := bstep (se 3 (by rfl) ⟨2637419, by rfl⟩ : syracuseStep 14066237 = 5274839) B5274839
theorem B7406153 : Blo 1462551 7406153 := bstep (se 2 (by rfl) ⟨2777307, by rfl⟩ : syracuseStep 7406153 = 5554615) B5554615
theorem B3703391 : Blo 1462551 3703391 := bstep (se 1 (by rfl) ⟨2777543, by rfl⟩ : syracuseStep 3703391 = 5555087) B5555087
theorem B3293801 : Blo 1462551 3293801 := bstep (se 2 (by rfl) ⟨1235175, by rfl⟩ : syracuseStep 3293801 = 2470351) B2470351
theorem B7037675 : Blo 1462551 7037675 := bstep (se 1 (by rfl) ⟨5278256, by rfl⟩ : syracuseStep 7037675 = 10556513) B10556513
theorem B1647391 : Blo 1462551 1647391 := bstep (se 1 (by rfl) ⟨1235543, by rfl⟩ : syracuseStep 1647391 = 2471087) B2471087
theorem B11117735 : Blo 1462551 11117735 := bstep (se 1 (by rfl) ⟨8338301, by rfl⟩ : syracuseStep 11117735 = 16676603) B16676603
theorem B5555375 : Blo 1462551 5555375 := bstep (se 1 (by rfl) ⟨4166531, by rfl⟩ : syracuseStep 5555375 = 8333063) B8333063
theorem B2196671 : Blo 1462551 2196671 := bstep (se 1 (by rfl) ⟨1647503, by rfl⟩ : syracuseStep 2196671 = 3295007) B3295007
theorem B8340671 : Blo 1462551 8340671 := bstep (se 1 (by rfl) ⟨6255503, by rfl⟩ : syracuseStep 8340671 = 12511007) B12511007
theorem B7406801 : Blo 1462551 7406801 := bstep (se 2 (by rfl) ⟨2777550, by rfl⟩ : syracuseStep 7406801 = 5555101) B5555101
theorem B3294431 : Blo 1462551 3294431 := bstep (se 1 (by rfl) ⟨2470823, by rfl⟩ : syracuseStep 3294431 = 4941647) B4941647
theorem B3704089 : Blo 1462551 3704089 := bstep (se 2 (by rfl) ⟨1389033, by rfl⟩ : syracuseStep 3704089 = 2778067) B2778067
theorem B2966863 : Blo 1462551 2966863 := bstep (se 1 (by rfl) ⟨2225147, by rfl⟩ : syracuseStep 2966863 = 4450295) B4450295
theorem B2196815 : Blo 1462551 2196815 := bstep (se 1 (by rfl) ⟨1647611, by rfl⟩ : syracuseStep 2196815 = 3295223) B3295223
theorem B3294647 : Blo 1462551 3294647 := bstep (se 1 (by rfl) ⟨2470985, by rfl⟩ : syracuseStep 3294647 = 4941971) B4941971
theorem B3294827 : Blo 1462551 3294827 := bstep (se 1 (by rfl) ⟨2471120, by rfl⟩ : syracuseStep 3294827 = 4942241) B4942241
theorem B14067503 : Blo 1462551 14067503 := bstep (se 1 (by rfl) ⟨10550627, by rfl⟩ : syracuseStep 14067503 = 21101255) B21101255
theorem B3295097 : Blo 1462551 3295097 := bstep (se 2 (by rfl) ⟨1235661, by rfl⟩ : syracuseStep 3295097 = 2471323) B2471323
theorem B5556559 : Blo 1462551 5556559 := bstep (se 1 (by rfl) ⟨4167419, by rfl⟩ : syracuseStep 5556559 = 8334839) B8334839
theorem B16664939 : Blo 1462551 16664939 := bstep (se 1 (by rfl) ⟨12498704, by rfl⟩ : syracuseStep 16664939 = 24997409) B24997409
theorem B26692199 : Blo 1462551 26692199 := bstep (se 1 (by rfl) ⟨20019149, by rfl⟩ : syracuseStep 26692199 = 40038299) B40038299
theorem B4688887 : Blo 1462551 4688887 := bstep (se 1 (by rfl) ⟨3516665, by rfl⟩ : syracuseStep 4688887 = 7033331) B7033331
theorem B1584191 : Blo 1462551 1584191 := bstep (se 1 (by rfl) ⟨1188143, by rfl⟩ : syracuseStep 1584191 = 2376287) B2376287
theorem B5008553 : Blo 1462551 5008553 := bstep (se 2 (by rfl) ⟨1878207, by rfl⟩ : syracuseStep 5008553 = 3756415) B3756415
theorem B3124489 : Blo 1462551 3124489 := bstep (se 2 (by rfl) ⟨1171683, by rfl⟩ : syracuseStep 3124489 = 2343367) B2343367
theorem B14060891 : Blo 1462551 14060891 := bstep (se 1 (by rfl) ⟨10545668, by rfl⟩ : syracuseStep 14060891 = 21091337) B21091337
theorem B4164959 : Blo 1462551 4164959 := bstep (se 1 (by rfl) ⟨3123719, by rfl⟩ : syracuseStep 4164959 = 6247439) B6247439
theorem B3706337 : Blo 1462551 3706337 := bstep (se 2 (by rfl) ⟨1389876, by rfl⟩ : syracuseStep 3706337 = 2779753) B2779753
theorem B7409231 : Blo 1462551 7409231 := bstep (se 1 (by rfl) ⟨5556923, by rfl⟩ : syracuseStep 7409231 = 11113847) B11113847
theorem B2084735 : Blo 1462551 2084735 := bstep (se 1 (by rfl) ⟨1563551, by rfl⟩ : syracuseStep 2084735 = 3127103) B3127103
theorem B9375851 : Blo 1462551 9375851 := bstep (se 1 (by rfl) ⟨7031888, by rfl⟩ : syracuseStep 9375851 = 14063777) B14063777
theorem B1462631 : Blo 1462551 1462631 := bstep (se 1 (by rfl) ⟨1096973, by rfl⟩ : syracuseStep 1462631 = 2193947) B2193947
theorem B6254957 : Blo 1462551 6254957 := bstep (se 3 (by rfl) ⟨1172804, by rfl⟩ : syracuseStep 6254957 = 2345609) B2345609
theorem B1462683 : Blo 1462551 1462683 := bstep (se 1 (by rfl) ⟨1097012, by rfl⟩ : syracuseStep 1462683 = 2194025) B2194025
theorem B90075559 : Blo 1462551 90075559 := bstep (se 1 (by rfl) ⟨67556669, by rfl⟩ : syracuseStep 90075559 = 135113339) B135113339
theorem B16888247 : Blo 1462551 16888247 := bstep (se 1 (by rfl) ⟨12666185, by rfl⟩ : syracuseStep 16888247 = 25332371) B25332371
theorem B9376337 : Blo 1462551 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B7033483 : Blo 1462551 7033483 := bstep (se 1 (by rfl) ⟨5275112, by rfl⟩ : syracuseStep 7033483 = 10550225) B10550225
theorem B12497611 : Blo 1462551 12497611 := bstep (se 1 (by rfl) ⟨9373208, by rfl⟩ : syracuseStep 12497611 = 18746417) B18746417
theorem B1463035 : Blo 1462551 1463035 := bstep (se 1 (by rfl) ⟨1097276, by rfl⟩ : syracuseStep 1463035 = 2194553) B2194553
theorem B1463103 : Blo 1462551 1463103 := bstep (se 1 (by rfl) ⟨1097327, by rfl⟩ : syracuseStep 1463103 = 2194655) B2194655
theorem B1463131 : Blo 1462551 1463131 := bstep (se 1 (by rfl) ⟨1097348, by rfl⟩ : syracuseStep 1463131 = 2194697) B2194697
theorem B1463199 : Blo 1462551 1463199 := bstep (se 1 (by rfl) ⟨1097399, by rfl⟩ : syracuseStep 1463199 = 2194799) B2194799
theorem B11269057 : Blo 1462551 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B1463279 : Blo 1462551 1463279 := bstep (se 1 (by rfl) ⟨1097459, by rfl⟩ : syracuseStep 1463279 = 2194919) B2194919
theorem B1463367 : Blo 1462551 1463367 := bstep (se 1 (by rfl) ⟨1097525, by rfl⟩ : syracuseStep 1463367 = 2195051) B2195051
theorem B3126377 : Blo 1462551 3126377 := bstep (se 2 (by rfl) ⟨1172391, by rfl⟩ : syracuseStep 3126377 = 2344783) B2344783
theorem B1463451 : Blo 1462551 1463451 := bstep (se 1 (by rfl) ⟨1097588, by rfl⟩ : syracuseStep 1463451 = 2195177) B2195177
theorem B4691105 : Blo 1462551 4691105 := bstep (se 2 (by rfl) ⟨1759164, by rfl⟩ : syracuseStep 4691105 = 3518329) B3518329
theorem B1463547 : Blo 1462551 1463547 := bstep (se 1 (by rfl) ⟨1097660, by rfl⟩ : syracuseStep 1463547 = 2195321) B2195321
theorem B14062889 : Blo 1462551 14062889 := bstep (se 2 (by rfl) ⟨5273583, by rfl⟩ : syracuseStep 14062889 = 10547167) B10547167
theorem B1463615 : Blo 1462551 1463615 := bstep (se 1 (by rfl) ⟨1097711, by rfl⟩ : syracuseStep 1463615 = 2195423) B2195423
theorem B1463783 : Blo 1462551 1463783 := bstep (se 1 (by rfl) ⟨1097837, by rfl⟩ : syracuseStep 1463783 = 2195675) B2195675
theorem B1562095 : Blo 1462551 1562095 := bstep (se 1 (by rfl) ⟨1171571, by rfl⟩ : syracuseStep 1562095 = 2343143) B2343143
theorem B1463791 : Blo 1462551 1463791 := bstep (se 1 (by rfl) ⟨1097843, by rfl⟩ : syracuseStep 1463791 = 2195687) B2195687
theorem B4691449 : Blo 1462551 4691449 := bstep (se 2 (by rfl) ⟨1759293, by rfl⟩ : syracuseStep 4691449 = 3518587) B3518587
theorem B12506633 : Blo 1462551 12506633 := bstep (se 2 (by rfl) ⟨4689987, by rfl⟩ : syracuseStep 12506633 = 9379975) B9379975
theorem B1463899 : Blo 1462551 1463899 := bstep (se 1 (by rfl) ⟨1097924, by rfl⟩ : syracuseStep 1463899 = 2195849) B2195849
theorem B96196243 : Blo 1462551 96196243 := bstep (se 1 (by rfl) ⟨72147182, by rfl⟩ : syracuseStep 96196243 = 144294365) B144294365
theorem B1463963 : Blo 1462551 1463963 := bstep (se 1 (by rfl) ⟨1097972, by rfl⟩ : syracuseStep 1463963 = 2195945) B2195945
theorem B3290849 : Blo 1462551 3290849 := bstep (se 2 (by rfl) ⟨1234068, by rfl⟩ : syracuseStep 3290849 = 2468137) B2468137
theorem B1464047 : Blo 1462551 1464047 := bstep (se 1 (by rfl) ⟨1098035, by rfl⟩ : syracuseStep 1464047 = 2196071) B2196071
theorem B4937543 : Blo 1462551 4937543 := bstep (se 1 (by rfl) ⟨3703157, by rfl⟩ : syracuseStep 4937543 = 7406315) B7406315
theorem B1464135 : Blo 1462551 1464135 := bstep (se 1 (by rfl) ⟨1098101, by rfl⟩ : syracuseStep 1464135 = 2196203) B2196203
theorem B1464155 : Blo 1462551 1464155 := bstep (se 1 (by rfl) ⟨1098116, by rfl⟩ : syracuseStep 1464155 = 2196233) B2196233
theorem B1464223 : Blo 1462551 1464223 := bstep (se 1 (by rfl) ⟨1098167, by rfl⟩ : syracuseStep 1464223 = 2196335) B2196335
theorem B56293379 : Blo 1462551 56293379 := bstep (se 1 (by rfl) ⟨42220034, by rfl⟩ : syracuseStep 56293379 = 84440069) B84440069
theorem B1464391 : Blo 1462551 1464391 := bstep (se 1 (by rfl) ⟨1098293, by rfl⟩ : syracuseStep 1464391 = 2196587) B2196587
theorem B1759303 : Blo 1462551 1759303 := bstep (se 1 (by rfl) ⟨1319477, by rfl⟩ : syracuseStep 1759303 = 2638955) B2638955
theorem B50690225 : Blo 1462551 50690225 := bstep (se 2 (by rfl) ⟨19008834, by rfl⟩ : syracuseStep 50690225 = 38017669) B38017669
theorem B1464551 : Blo 1462551 1464551 := bstep (se 1 (by rfl) ⟨1098413, by rfl⟩ : syracuseStep 1464551 = 2196827) B2196827
theorem B3291371 : Blo 1462551 3291371 := bstep (se 1 (by rfl) ⟨2468528, by rfl⟩ : syracuseStep 3291371 = 4937057) B4937057
theorem B2193863 : Blo 1462551 2193863 := bstep (se 1 (by rfl) ⟨1645397, by rfl⟩ : syracuseStep 2193863 = 3290795) B3290795
theorem B2816617 : Blo 1462551 2816617 := bstep (se 2 (by rfl) ⟨1056231, by rfl⟩ : syracuseStep 2816617 = 2112463) B2112463
theorem B2194079 : Blo 1462551 2194079 := bstep (se 1 (by rfl) ⟨1645559, by rfl⟩ : syracuseStep 2194079 = 3291119) B3291119
theorem B2194223 : Blo 1462551 2194223 := bstep (se 1 (by rfl) ⟨1645667, by rfl⟩ : syracuseStep 2194223 = 3291335) B3291335
theorem B35617619 : Blo 1462551 35617619 := bstep (se 1 (by rfl) ⟨26713214, by rfl⟩ : syracuseStep 35617619 = 53426429) B53426429
theorem B2194343 : Blo 1462551 2194343 := bstep (se 1 (by rfl) ⟨1645757, by rfl⟩ : syracuseStep 2194343 = 3291515) B3291515
theorem B9509825 : Blo 1462551 9509825 := bstep (se 2 (by rfl) ⟨3566184, by rfl⟩ : syracuseStep 9509825 = 7132369) B7132369
theorem B4938731 : Blo 1462551 4938731 := bstep (se 1 (by rfl) ⟨3704048, by rfl⟩ : syracuseStep 4938731 = 7408097) B7408097
theorem B22527017 : Blo 1462551 22527017 := bstep (se 2 (by rfl) ⟨8447631, by rfl⟩ : syracuseStep 22527017 = 16895263) B16895263
theorem B2194523 : Blo 1462551 2194523 := bstep (se 1 (by rfl) ⟨1645892, by rfl⟩ : syracuseStep 2194523 = 3291785) B3291785
theorem B12508343 : Blo 1462551 12508343 := bstep (se 1 (by rfl) ⟨9381257, by rfl⟩ : syracuseStep 12508343 = 18762515) B18762515
theorem B7511305 : Blo 1462551 7511305 := bstep (se 2 (by rfl) ⟨2816739, by rfl⟩ : syracuseStep 7511305 = 5633479) B5633479
theorem B2194895 : Blo 1462551 2194895 := bstep (se 1 (by rfl) ⟨1646171, by rfl⟩ : syracuseStep 2194895 = 3292343) B3292343
theorem B3292667 : Blo 1462551 3292667 := bstep (se 1 (by rfl) ⟨2469500, by rfl⟩ : syracuseStep 3292667 = 4939001) B4939001
theorem B50724467 : Blo 1462551 50724467 := bstep (se 1 (by rfl) ⟨38043350, by rfl⟩ : syracuseStep 50724467 = 76086701) B76086701
theorem B4685465 : Blo 1462551 4685465 := bstep (se 2 (by rfl) ⟨1757049, by rfl⟩ : syracuseStep 4685465 = 3514099) B3514099
theorem B11108015 : Blo 1462551 11108015 := bstep (se 1 (by rfl) ⟨8331011, by rfl⟩ : syracuseStep 11108015 = 16662023) B16662023
theorem B3292847 : Blo 1462551 3292847 := bstep (se 1 (by rfl) ⟨2469635, by rfl⟩ : syracuseStep 3292847 = 4939271) B4939271
theorem B1646311 : Blo 1462551 1646311 := bstep (se 1 (by rfl) ⟨1234733, by rfl⟩ : syracuseStep 1646311 = 2469467) B2469467
theorem B3292937 : Blo 1462551 3292937 := bstep (se 2 (by rfl) ⟨1234851, by rfl⟩ : syracuseStep 3292937 = 2469703) B2469703
theorem B8453917 : Blo 1462551 8453917 := bstep (se 3 (by rfl) ⟨1585109, by rfl⟩ : syracuseStep 8453917 = 3170219) B3170219
theorem B2195279 : Blo 1462551 2195279 := bstep (se 1 (by rfl) ⟨1646459, by rfl⟩ : syracuseStep 2195279 = 3292919) B3292919
theorem B2776943 : Blo 1462551 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B2195399 : Blo 1462551 2195399 := bstep (se 1 (by rfl) ⟨1646549, by rfl⟩ : syracuseStep 2195399 = 3293099) B3293099
theorem B6250567 : Blo 1462551 6250567 := bstep (se 1 (by rfl) ⟨4687925, by rfl⟩ : syracuseStep 6250567 = 9375851) B9375851
theorem B1851599 : Blo 1462551 1851599 := bstep (se 1 (by rfl) ⟨1388699, by rfl⟩ : syracuseStep 1851599 = 2777399) B2777399
theorem B4169971 : Blo 1462551 4169971 := bstep (se 1 (by rfl) ⟨3127478, by rfl⟩ : syracuseStep 4169971 = 6254957) B6254957
theorem B2195711 : Blo 1462551 2195711 := bstep (se 1 (by rfl) ⟨1646783, by rfl⟩ : syracuseStep 2195711 = 3293567) B3293567
theorem B4686119 : Blo 1462551 4686119 := bstep (se 1 (by rfl) ⟨3514589, by rfl⟩ : syracuseStep 4686119 = 7029179) B7029179
theorem B3293495 : Blo 1462551 3293495 := bstep (se 1 (by rfl) ⟨2470121, by rfl⟩ : syracuseStep 3293495 = 4940243) B4940243
theorem B1851751 : Blo 1462551 1851751 := bstep (se 1 (by rfl) ⟨1388813, by rfl⟩ : syracuseStep 1851751 = 2777627) B2777627
theorem B6250891 : Blo 1462551 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B2195867 : Blo 1462551 2195867 := bstep (se 1 (by rfl) ⟨1646900, by rfl⟩ : syracuseStep 2195867 = 3293801) B3293801
theorem B3703583 : Blo 1462551 3703583 := bstep (se 1 (by rfl) ⟨2777687, by rfl⟩ : syracuseStep 3703583 = 5555375) B5555375
theorem B2196287 : Blo 1462551 2196287 := bstep (se 1 (by rfl) ⟨1647215, by rfl⟩ : syracuseStep 2196287 = 3294431) B3294431
theorem B16663481 : Blo 1462551 16663481 := bstep (se 2 (by rfl) ⟨6248805, by rfl⟩ : syracuseStep 16663481 = 12497611) B12497611
theorem B2196431 : Blo 1462551 2196431 := bstep (se 1 (by rfl) ⟨1647323, by rfl⟩ : syracuseStep 2196431 = 3294647) B3294647
theorem B2196521 : Blo 1462551 2196521 := bstep (se 2 (by rfl) ⟨823695, by rfl⟩ : syracuseStep 2196521 = 1647391) B1647391
theorem B2196551 : Blo 1462551 2196551 := bstep (se 1 (by rfl) ⟨1647413, by rfl⟩ : syracuseStep 2196551 = 3294827) B3294827
theorem B2196731 : Blo 1462551 2196731 := bstep (se 1 (by rfl) ⟨1647548, by rfl⟩ : syracuseStep 2196731 = 3295097) B3295097
theorem B15025409 : Blo 1462551 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B6251849 : Blo 1462551 6251849 := bstep (se 2 (by rfl) ⟨2344443, by rfl⟩ : syracuseStep 6251849 = 4688887) B4688887
theorem B37528919 : Blo 1462551 37528919 := bstep (se 1 (by rfl) ⟨28146689, by rfl⟩ : syracuseStep 37528919 = 56293379) B56293379
theorem B33793483 : Blo 1462551 33793483 := bstep (se 1 (by rfl) ⟨25345112, by rfl⟩ : syracuseStep 33793483 = 50690225) B50690225
theorem B11109959 : Blo 1462551 11109959 := bstep (se 1 (by rfl) ⟨8332469, by rfl⟩ : syracuseStep 11109959 = 16664939) B16664939
theorem B12494573 : Blo 1462551 12494573 := bstep (se 3 (by rfl) ⟨2342732, by rfl⟩ : syracuseStep 12494573 = 4685465) B4685465
theorem B17794799 : Blo 1462551 17794799 := bstep (se 1 (by rfl) ⟨13346099, by rfl⟩ : syracuseStep 17794799 = 26692199) B26692199
theorem B15018011 : Blo 1462551 15018011 := bstep (se 1 (by rfl) ⟨11263508, by rfl⟩ : syracuseStep 15018011 = 22527017) B22527017
theorem B9373927 : Blo 1462551 9373927 := bstep (se 1 (by rfl) ⟨7030445, by rfl⟩ : syracuseStep 9373927 = 14060891) B14060891
theorem B4451195 : Blo 1462551 4451195 := bstep (se 1 (by rfl) ⟨3338396, by rfl⟩ : syracuseStep 4451195 = 6676793) B6676793
theorem B11258831 : Blo 1462551 11258831 := bstep (se 1 (by rfl) ⟨8444123, by rfl⟩ : syracuseStep 11258831 = 16888247) B16888247
theorem B9382949 : Blo 1462551 9382949 := bstep (se 4 (by rfl) ⟨879651, by rfl⟩ : syracuseStep 9382949 = 1759303) B1759303
theorem B2468927 : Blo 1462551 2468927 := bstep (se 1 (by rfl) ⟨1851695, by rfl⟩ : syracuseStep 2468927 = 3703391) B3703391
theorem B7408745 : Blo 1462551 7408745 := bstep (se 2 (by rfl) ⟨2778279, by rfl⟩ : syracuseStep 7408745 = 5556559) B5556559
theorem B14068889 : Blo 1462551 14068889 := bstep (se 2 (by rfl) ⟨5275833, by rfl⟩ : syracuseStep 14068889 = 10551667) B10551667
theorem B3755489 : Blo 1462551 3755489 := bstep (se 2 (by rfl) ⟨1408308, by rfl⟩ : syracuseStep 3755489 = 2816617) B2816617
theorem B9375259 : Blo 1462551 9375259 := bstep (se 1 (by rfl) ⟨7031444, by rfl⟩ : syracuseStep 9375259 = 14062889) B14062889
theorem B1462575 : Blo 1462551 1462575 := bstep (se 1 (by rfl) ⟨1096931, by rfl⟩ : syracuseStep 1462575 = 2193863) B2193863
theorem B4165985 : Blo 1462551 4165985 := bstep (se 2 (by rfl) ⟨1562244, by rfl⟩ : syracuseStep 4165985 = 3124489) B3124489
theorem B10015073 : Blo 1462551 10015073 := bstep (se 2 (by rfl) ⟨3755652, by rfl⟩ : syracuseStep 10015073 = 7511305) B7511305
theorem B1462719 : Blo 1462551 1462719 := bstep (se 1 (by rfl) ⟨1097039, by rfl⟩ : syracuseStep 1462719 = 2194079) B2194079
theorem B1462815 : Blo 1462551 1462815 := bstep (se 1 (by rfl) ⟨1097111, by rfl⟩ : syracuseStep 1462815 = 2194223) B2194223
theorem B23745079 : Blo 1462551 23745079 := bstep (se 1 (by rfl) ⟨17808809, by rfl⟩ : syracuseStep 23745079 = 35617619) B35617619
theorem B1462895 : Blo 1462551 1462895 := bstep (se 1 (by rfl) ⟨1097171, by rfl⟩ : syracuseStep 1462895 = 2194343) B2194343
theorem B6255265 : Blo 1462551 6255265 := bstep (se 2 (by rfl) ⟨2345724, by rfl⟩ : syracuseStep 6255265 = 4691449) B4691449
theorem B1463015 : Blo 1462551 1463015 := bstep (se 1 (by rfl) ⟨1097261, by rfl⟩ : syracuseStep 1463015 = 2194523) B2194523
theorem B3339035 : Blo 1462551 3339035 := bstep (se 1 (by rfl) ⟨2504276, by rfl⟩ : syracuseStep 3339035 = 5008553) B5008553
theorem B1463263 : Blo 1462551 1463263 := bstep (se 1 (by rfl) ⟨1097447, by rfl⟩ : syracuseStep 1463263 = 2194895) B2194895
theorem B2470891 : Blo 1462551 2470891 := bstep (se 1 (by rfl) ⟨1853168, by rfl⟩ : syracuseStep 2470891 = 3706337) B3706337
theorem B5559293 : Blo 1462551 5559293 := bstep (se 3 (by rfl) ⟨1042367, by rfl⟩ : syracuseStep 5559293 = 2084735) B2084735
theorem B1463519 : Blo 1462551 1463519 := bstep (se 1 (by rfl) ⟨1097639, by rfl⟩ : syracuseStep 1463519 = 2195279) B2195279
theorem B1463599 : Blo 1462551 1463599 := bstep (se 1 (by rfl) ⟨1097699, by rfl⟩ : syracuseStep 1463599 = 2195399) B2195399
theorem B7411175 : Blo 1462551 7411175 := bstep (se 1 (by rfl) ⟨5558381, by rfl⟩ : syracuseStep 7411175 = 11116763) B11116763
theorem B4224509 : Blo 1462551 4224509 := bstep (se 3 (by rfl) ⟨792095, by rfl⟩ : syracuseStep 4224509 = 1584191) B1584191
theorem B1463839 : Blo 1462551 1463839 := bstep (se 1 (by rfl) ⟨1097879, by rfl⟩ : syracuseStep 1463839 = 2195759) B2195759
theorem B8337005 : Blo 1462551 8337005 := bstep (se 3 (by rfl) ⟨1563188, by rfl⟩ : syracuseStep 8337005 = 3126377) B3126377
theorem B6674089 : Blo 1462551 6674089 := bstep (se 2 (by rfl) ⟨2502783, by rfl⟩ : syracuseStep 6674089 = 5005567) B5005567
theorem B1463999 : Blo 1462551 1463999 := bstep (se 1 (by rfl) ⟨1097999, by rfl⟩ : syracuseStep 1463999 = 2195999) B2195999
theorem B9377491 : Blo 1462551 9377491 := bstep (se 1 (by rfl) ⟨7033118, by rfl⟩ : syracuseStep 9377491 = 14066237) B14066237
theorem B4937435 : Blo 1462551 4937435 := bstep (se 1 (by rfl) ⟨3703076, by rfl⟩ : syracuseStep 4937435 = 7406153) B7406153
theorem B4691783 : Blo 1462551 4691783 := bstep (se 1 (by rfl) ⟨3518837, by rfl⟩ : syracuseStep 4691783 = 7037675) B7037675
theorem B120100745 : Blo 1462551 120100745 := bstep (se 2 (by rfl) ⟨45037779, by rfl⟩ : syracuseStep 120100745 = 90075559) B90075559
theorem B3127403 : Blo 1462551 3127403 := bstep (se 1 (by rfl) ⟨2345552, by rfl⟩ : syracuseStep 3127403 = 4691105) B4691105
theorem B7411823 : Blo 1462551 7411823 := bstep (se 1 (by rfl) ⟨5558867, by rfl⟩ : syracuseStep 7411823 = 11117735) B11117735
theorem B1464447 : Blo 1462551 1464447 := bstep (se 1 (by rfl) ⟨1098335, by rfl⟩ : syracuseStep 1464447 = 2196671) B2196671
theorem B5560447 : Blo 1462551 5560447 := bstep (se 1 (by rfl) ⟨4170335, by rfl⟩ : syracuseStep 5560447 = 8340671) B8340671
theorem B4937867 : Blo 1462551 4937867 := bstep (se 1 (by rfl) ⟨3703400, by rfl⟩ : syracuseStep 4937867 = 7406801) B7406801
theorem B9377977 : Blo 1462551 9377977 := bstep (se 2 (by rfl) ⟨3516741, by rfl⟩ : syracuseStep 9377977 = 7033483) B7033483
theorem B1464543 : Blo 1462551 1464543 := bstep (se 1 (by rfl) ⟨1098407, by rfl⟩ : syracuseStep 1464543 = 2196815) B2196815
theorem B11106557 : Blo 1462551 11106557 := bstep (se 3 (by rfl) ⟨2082479, by rfl⟩ : syracuseStep 11106557 = 4164959) B4164959
theorem B8337755 : Blo 1462551 8337755 := bstep (se 1 (by rfl) ⟨6253316, by rfl⟩ : syracuseStep 8337755 = 12506633) B12506633
theorem B2193899 : Blo 1462551 2193899 := bstep (se 1 (by rfl) ⟨1645424, by rfl⟩ : syracuseStep 2193899 = 3290849) B3290849
theorem B9378335 : Blo 1462551 9378335 := bstep (se 1 (by rfl) ⟨7033751, by rfl⟩ : syracuseStep 9378335 = 14067503) B14067503
theorem B3291695 : Blo 1462551 3291695 := bstep (se 1 (by rfl) ⟨2468771, by rfl⟩ : syracuseStep 3291695 = 4937543) B4937543
theorem B2194247 : Blo 1462551 2194247 := bstep (se 1 (by rfl) ⟨1645685, by rfl⟩ : syracuseStep 2194247 = 3291371) B3291371
theorem B4938785 : Blo 1462551 4938785 := bstep (se 2 (by rfl) ⟨1852044, by rfl⟩ : syracuseStep 4938785 = 3704089) B3704089
theorem B3955817 : Blo 1462551 3955817 := bstep (se 2 (by rfl) ⟨1483431, by rfl⟩ : syracuseStep 3955817 = 2966863) B2966863
theorem B6339883 : Blo 1462551 6339883 := bstep (se 1 (by rfl) ⟨4754912, by rfl⟩ : syracuseStep 6339883 = 9509825) B9509825
theorem B3292487 : Blo 1462551 3292487 := bstep (se 1 (by rfl) ⟨2469365, by rfl⟩ : syracuseStep 3292487 = 4938731) B4938731
theorem B8338895 : Blo 1462551 8338895 := bstep (se 1 (by rfl) ⟨6254171, by rfl⟩ : syracuseStep 8338895 = 12508343) B12508343
theorem B128261657 : Blo 1462551 128261657 := bstep (se 2 (by rfl) ⟨48098121, by rfl⟩ : syracuseStep 128261657 = 96196243) B96196243
theorem B7405181 : Blo 1462551 7405181 := bstep (se 3 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 7405181 = 2776943) B2776943
theorem B2195081 : Blo 1462551 2195081 := bstep (se 2 (by rfl) ⟨823155, by rfl⟩ : syracuseStep 2195081 = 1646311) B1646311
theorem B2195111 : Blo 1462551 2195111 := bstep (se 1 (by rfl) ⟨1646333, by rfl⟩ : syracuseStep 2195111 = 3292667) B3292667
theorem B11271889 : Blo 1462551 11271889 := bstep (se 2 (by rfl) ⟨4226958, by rfl⟩ : syracuseStep 11271889 = 8453917) B8453917
theorem B4939487 : Blo 1462551 4939487 := bstep (se 1 (by rfl) ⟨3704615, by rfl⟩ : syracuseStep 4939487 = 7409231) B7409231
theorem B33816311 : Blo 1462551 33816311 := bstep (se 1 (by rfl) ⟨25362233, by rfl⟩ : syracuseStep 33816311 = 50724467) B50724467
theorem B7405343 : Blo 1462551 7405343 := bstep (se 1 (by rfl) ⟨5554007, by rfl⟩ : syracuseStep 7405343 = 11108015) B11108015
theorem B2195231 : Blo 1462551 2195231 := bstep (se 1 (by rfl) ⟨1646423, by rfl⟩ : syracuseStep 2195231 = 3292847) B3292847
theorem B2195291 : Blo 1462551 2195291 := bstep (se 1 (by rfl) ⟨1646468, by rfl⟩ : syracuseStep 2195291 = 3292937) B3292937
theorem B8331173 : Blo 1462551 8331173 := bstep (se 4 (by rfl) ⟨781047, by rfl⟩ : syracuseStep 8331173 = 1562095) B1562095
theorem B7413929 : Blo 1462551 7413929 := bstep (se 2 (by rfl) ⟨2780223, by rfl⟩ : syracuseStep 7413929 = 5560447) B5560447
theorem B2195663 : Blo 1462551 2195663 := bstep (se 1 (by rfl) ⟨1646747, by rfl⟩ : syracuseStep 2195663 = 3293495) B3293495
theorem B2777323 : Blo 1462551 2777323 := bstep (se 1 (by rfl) ⟨2082992, by rfl⟩ : syracuseStep 2777323 = 4165985) B4165985
theorem B6676715 : Blo 1462551 6676715 := bstep (se 1 (by rfl) ⟨5007536, by rfl⟩ : syracuseStep 6676715 = 10015073) B10015073
theorem B11108987 : Blo 1462551 11108987 := bstep (se 1 (by rfl) ⟨8331740, by rfl⟩ : syracuseStep 11108987 = 16663481) B16663481
theorem B8340353 : Blo 1462551 8340353 := bstep (se 2 (by rfl) ⟨3127632, by rfl⟩ : syracuseStep 8340353 = 6255265) B6255265
theorem B25019279 : Blo 1462551 25019279 := bstep (se 1 (by rfl) ⟨18764459, by rfl⟩ : syracuseStep 25019279 = 37528919) B37528919
theorem B4940783 : Blo 1462551 4940783 := bstep (se 1 (by rfl) ⟨3705587, by rfl⟩ : syracuseStep 4940783 = 7411175) B7411175
theorem B7406639 : Blo 1462551 7406639 := bstep (se 1 (by rfl) ⟨5554979, by rfl⟩ : syracuseStep 7406639 = 11109959) B11109959
theorem B11863199 : Blo 1462551 11863199 := bstep (se 1 (by rfl) ⟨8897399, by rfl⟩ : syracuseStep 11863199 = 17794799) B17794799
theorem B3294521 : Blo 1462551 3294521 := bstep (se 2 (by rfl) ⟨1235445, by rfl⟩ : syracuseStep 3294521 = 2470891) B2470891
theorem B10012007 : Blo 1462551 10012007 := bstep (se 1 (by rfl) ⟨7509005, by rfl⟩ : syracuseStep 10012007 = 15018011) B15018011
theorem B4941215 : Blo 1462551 4941215 := bstep (se 1 (by rfl) ⟨3705911, by rfl⟩ : syracuseStep 4941215 = 7411823) B7411823
theorem B6252223 : Blo 1462551 6252223 := bstep (se 1 (by rfl) ⟨4689167, by rfl⟩ : syracuseStep 6252223 = 9378335) B9378335
theorem B2967463 : Blo 1462551 2967463 := bstep (se 1 (by rfl) ⟨2225597, by rfl⟩ : syracuseStep 2967463 = 4451195) B4451195
theorem B45057977 : Blo 1462551 45057977 := bstep (se 2 (by rfl) ⟨16896741, by rfl⟩ : syracuseStep 45057977 = 33793483) B33793483
theorem B7505887 : Blo 1462551 7505887 := bstep (se 1 (by rfl) ⟨5629415, by rfl⟩ : syracuseStep 7505887 = 11258831) B11258831
theorem B8898785 : Blo 1462551 8898785 := bstep (se 2 (by rfl) ⟨3337044, by rfl⟩ : syracuseStep 8898785 = 6674089) B6674089
theorem B12503321 : Blo 1462551 12503321 := bstep (se 2 (by rfl) ⟨4688745, by rfl⟩ : syracuseStep 12503321 = 9377491) B9377491
theorem B8334089 : Blo 1462551 8334089 := bstep (se 2 (by rfl) ⟨3125283, by rfl⟩ : syracuseStep 8334089 = 6250567) B6250567
theorem B3124079 : Blo 1462551 3124079 := bstep (se 1 (by rfl) ⟨2343059, by rfl⟩ : syracuseStep 3124079 = 4686119) B4686119
theorem B12503969 : Blo 1462551 12503969 := bstep (se 2 (by rfl) ⟨4688988, by rfl⟩ : syracuseStep 12503969 = 9377977) B9377977
theorem B2469001 : Blo 1462551 2469001 := bstep (se 2 (by rfl) ⟨925875, by rfl⟩ : syracuseStep 2469001 = 1851751) B1851751
theorem B8334521 : Blo 1462551 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B2469055 : Blo 1462551 2469055 := bstep (se 1 (by rfl) ⟨1851791, by rfl⟩ : syracuseStep 2469055 = 3703583) B3703583
theorem B3706195 : Blo 1462551 3706195 := bstep (se 1 (by rfl) ⟨2779646, by rfl⟩ : syracuseStep 3706195 = 5559293) B5559293
theorem B5558003 : Blo 1462551 5558003 := bstep (se 1 (by rfl) ⟨4168502, by rfl⟩ : syracuseStep 5558003 = 8337005) B8337005
theorem B2084935 : Blo 1462551 2084935 := bstep (se 1 (by rfl) ⟨1563701, by rfl⟩ : syracuseStep 2084935 = 3127403) B3127403
theorem B5558503 : Blo 1462551 5558503 := bstep (se 1 (by rfl) ⟨4168877, by rfl⟩ : syracuseStep 5558503 = 8337755) B8337755
theorem B1462599 : Blo 1462551 1462599 := bstep (se 1 (by rfl) ⟨1096949, by rfl⟩ : syracuseStep 1462599 = 2193899) B2193899
theorem B1462831 : Blo 1462551 1462831 := bstep (se 1 (by rfl) ⟨1097123, by rfl⟩ : syracuseStep 1462831 = 2194247) B2194247
theorem B6255299 : Blo 1462551 6255299 := bstep (se 1 (by rfl) ⟨4691474, by rfl⟩ : syracuseStep 6255299 = 9382949) B9382949
theorem B15029185 : Blo 1462551 15029185 := bstep (se 2 (by rfl) ⟨5635944, by rfl⟩ : syracuseStep 15029185 = 11271889) B11271889
theorem B5559263 : Blo 1462551 5559263 := bstep (se 1 (by rfl) ⟨4169447, by rfl⟩ : syracuseStep 5559263 = 8338895) B8338895
theorem B4936787 : Blo 1462551 4936787 := bstep (se 1 (by rfl) ⟨3702590, by rfl⟩ : syracuseStep 4936787 = 7405181) B7405181
theorem B1463387 : Blo 1462551 1463387 := bstep (se 1 (by rfl) ⟨1097540, by rfl⟩ : syracuseStep 1463387 = 2195081) B2195081
theorem B1463407 : Blo 1462551 1463407 := bstep (se 1 (by rfl) ⟨1097555, by rfl⟩ : syracuseStep 1463407 = 2195111) B2195111
theorem B4936895 : Blo 1462551 4936895 := bstep (se 1 (by rfl) ⟨3702671, by rfl⟩ : syracuseStep 4936895 = 7405343) B7405343
theorem B1463487 : Blo 1462551 1463487 := bstep (se 1 (by rfl) ⟨1097615, by rfl⟩ : syracuseStep 1463487 = 2195231) B2195231
theorem B1463527 : Blo 1462551 1463527 := bstep (se 1 (by rfl) ⟨1097645, by rfl⟩ : syracuseStep 1463527 = 2195291) B2195291
theorem B1463807 : Blo 1462551 1463807 := bstep (se 1 (by rfl) ⟨1097855, by rfl⟩ : syracuseStep 1463807 = 2195711) B2195711
theorem B1463911 : Blo 1462551 1463911 := bstep (se 1 (by rfl) ⟨1097933, by rfl⟩ : syracuseStep 1463911 = 2195867) B2195867
theorem B12498569 : Blo 1462551 12498569 := bstep (se 2 (by rfl) ⟨4686963, by rfl⟩ : syracuseStep 12498569 = 9373927) B9373927
theorem B5559961 : Blo 1462551 5559961 := bstep (se 2 (by rfl) ⟨2084985, by rfl⟩ : syracuseStep 5559961 = 4169971) B4169971
theorem B2226023 : Blo 1462551 2226023 := bstep (se 1 (by rfl) ⟨1669517, by rfl⟩ : syracuseStep 2226023 = 3339035) B3339035
theorem B4937597 : Blo 1462551 4937597 := bstep (se 3 (by rfl) ⟨925799, by rfl⟩ : syracuseStep 4937597 = 1851599) B1851599
theorem B1464191 : Blo 1462551 1464191 := bstep (se 1 (by rfl) ⟨1098143, by rfl⟩ : syracuseStep 1464191 = 2196287) B2196287
theorem B1464287 : Blo 1462551 1464287 := bstep (se 1 (by rfl) ⟨1098215, by rfl⟩ : syracuseStep 1464287 = 2196431) B2196431
theorem B1464347 : Blo 1462551 1464347 := bstep (se 1 (by rfl) ⟨1098260, by rfl⟩ : syracuseStep 1464347 = 2196521) B2196521
theorem B1464367 : Blo 1462551 1464367 := bstep (se 1 (by rfl) ⟨1098275, by rfl⟩ : syracuseStep 1464367 = 2196551) B2196551
theorem B31660105 : Blo 1462551 31660105 := bstep (se 2 (by rfl) ⟨11872539, by rfl⟩ : syracuseStep 31660105 = 23745079) B23745079
theorem B1464487 : Blo 1462551 1464487 := bstep (se 1 (by rfl) ⟨1098365, by rfl⟩ : syracuseStep 1464487 = 2196731) B2196731
theorem B10016939 : Blo 1462551 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B4167899 : Blo 1462551 4167899 := bstep (se 1 (by rfl) ⟨3125924, by rfl⟩ : syracuseStep 4167899 = 6251849) B6251849
theorem B2816339 : Blo 1462551 2816339 := bstep (se 1 (by rfl) ⟨2112254, by rfl⟩ : syracuseStep 2816339 = 4224509) B4224509
theorem B3291623 : Blo 1462551 3291623 := bstep (se 1 (by rfl) ⟨2468717, by rfl⟩ : syracuseStep 3291623 = 4937435) B4937435
theorem B8329715 : Blo 1462551 8329715 := bstep (se 1 (by rfl) ⟨6247286, by rfl⟩ : syracuseStep 8329715 = 12494573) B12494573
theorem B3127855 : Blo 1462551 3127855 := bstep (se 1 (by rfl) ⟨2345891, by rfl⟩ : syracuseStep 3127855 = 4691783) B4691783
theorem B80067163 : Blo 1462551 80067163 := bstep (se 1 (by rfl) ⟨60050372, by rfl⟩ : syracuseStep 80067163 = 120100745) B120100745
theorem B3291911 : Blo 1462551 3291911 := bstep (se 1 (by rfl) ⟨2468933, by rfl⟩ : syracuseStep 3291911 = 4937867) B4937867
theorem B7404371 : Blo 1462551 7404371 := bstep (se 1 (by rfl) ⟨5553278, by rfl⟩ : syracuseStep 7404371 = 11106557) B11106557
theorem B2194463 : Blo 1462551 2194463 := bstep (se 1 (by rfl) ⟨1645847, by rfl⟩ : syracuseStep 2194463 = 3291695) B3291695
theorem B8453177 : Blo 1462551 8453177 := bstep (se 2 (by rfl) ⟨3169941, by rfl⟩ : syracuseStep 8453177 = 6339883) B6339883
theorem B3292523 : Blo 1462551 3292523 := bstep (se 1 (by rfl) ⟨2469392, by rfl⟩ : syracuseStep 3292523 = 4938785) B4938785
theorem B12500345 : Blo 1462551 12500345 := bstep (se 2 (by rfl) ⟨4687629, by rfl⟩ : syracuseStep 12500345 = 9375259) B9375259
theorem B1645951 : Blo 1462551 1645951 := bstep (se 1 (by rfl) ⟨1234463, by rfl⟩ : syracuseStep 1645951 = 2468927) B2468927
theorem B4939163 : Blo 1462551 4939163 := bstep (se 1 (by rfl) ⟨3704372, by rfl⟩ : syracuseStep 4939163 = 7408745) B7408745
theorem B2637211 : Blo 1462551 2637211 := bstep (se 1 (by rfl) ⟨1977908, by rfl⟩ : syracuseStep 2637211 = 3955817) B3955817
theorem B9379259 : Blo 1462551 9379259 := bstep (se 1 (by rfl) ⟨7034444, by rfl⟩ : syracuseStep 9379259 = 14068889) B14068889
theorem B2194991 : Blo 1462551 2194991 := bstep (se 1 (by rfl) ⟨1646243, by rfl⟩ : syracuseStep 2194991 = 3292487) B3292487
theorem B40058549 : Blo 1462551 40058549 := bstep (se 5 (by rfl) ⟨1877744, by rfl⟩ : syracuseStep 40058549 = 3755489) B3755489
theorem B85507771 : Blo 1462551 85507771 := bstep (se 1 (by rfl) ⟨64130828, by rfl⟩ : syracuseStep 85507771 = 128261657) B128261657
theorem B3292991 : Blo 1462551 3292991 := bstep (se 1 (by rfl) ⟨2469743, by rfl⟩ : syracuseStep 3292991 = 4939487) B4939487
theorem B22544207 : Blo 1462551 22544207 := bstep (se 1 (by rfl) ⟨16908155, by rfl⟩ : syracuseStep 22544207 = 33816311) B33816311
theorem B5554115 : Blo 1462551 5554115 := bstep (se 1 (by rfl) ⟨4165586, by rfl⟩ : syracuseStep 5554115 = 8331173) B8331173
theorem B42213473 : Blo 1462551 42213473 := bstep (se 2 (by rfl) ⟨15830052, by rfl⟩ : syracuseStep 42213473 = 31660105) B31660105
theorem B3703097 : Blo 1462551 3703097 := bstep (se 2 (by rfl) ⟨1388661, by rfl⟩ : syracuseStep 3703097 = 2777323) B2777323
theorem B7405991 : Blo 1462551 7405991 := bstep (se 1 (by rfl) ⟨5554493, by rfl⟩ : syracuseStep 7405991 = 11108987) B11108987
theorem B4170199 : Blo 1462551 4170199 := bstep (se 1 (by rfl) ⟨3127649, by rfl⟩ : syracuseStep 4170199 = 6255299) B6255299
theorem B16679519 : Blo 1462551 16679519 := bstep (se 1 (by rfl) ⟨12509639, by rfl⟩ : syracuseStep 16679519 = 25019279) B25019279
theorem B3293855 : Blo 1462551 3293855 := bstep (se 1 (by rfl) ⟨2470391, by rfl⟩ : syracuseStep 3293855 = 4940783) B4940783
theorem B4170473 : Blo 1462551 4170473 := bstep (se 2 (by rfl) ⟨1563927, by rfl⟩ : syracuseStep 4170473 = 3127855) B3127855
theorem B30040949 : Blo 1462551 30040949 := bstep (se 5 (by rfl) ⟨1408169, by rfl⟩ : syracuseStep 30040949 = 2816339) B2816339
theorem B2196347 : Blo 1462551 2196347 := bstep (se 1 (by rfl) ⟨1647260, by rfl⟩ : syracuseStep 2196347 = 3294521) B3294521
theorem B3294143 : Blo 1462551 3294143 := bstep (se 1 (by rfl) ⟨2470607, by rfl⟩ : syracuseStep 3294143 = 4941215) B4941215
theorem B8332379 : Blo 1462551 8332379 := bstep (se 1 (by rfl) ⟨6249284, by rfl⟩ : syracuseStep 8332379 = 12498569) B12498569
theorem B1484015 : Blo 1462551 1484015 := bstep (se 1 (by rfl) ⟨1113011, by rfl⟩ : syracuseStep 1484015 = 2226023) B2226023
theorem B20038913 : Blo 1462551 20038913 := bstep (se 2 (by rfl) ⟨7514592, by rfl⟩ : syracuseStep 20038913 = 15029185) B15029185
theorem B6677959 : Blo 1462551 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B2778599 : Blo 1462551 2778599 := bstep (se 1 (by rfl) ⟨2083949, by rfl⟩ : syracuseStep 2778599 = 4167899) B4167899
theorem B5932523 : Blo 1462551 5932523 := bstep (se 1 (by rfl) ⟨4449392, by rfl⟩ : syracuseStep 5932523 = 8898785) B8898785
theorem B4941593 : Blo 1462551 4941593 := bstep (se 2 (by rfl) ⟨1853097, by rfl⟩ : syracuseStep 4941593 = 3706195) B3706195
theorem B5556059 : Blo 1462551 5556059 := bstep (se 1 (by rfl) ⟨4167044, by rfl⟩ : syracuseStep 5556059 = 8334089) B8334089
theorem B3516281 : Blo 1462551 3516281 := bstep (se 2 (by rfl) ⟨1318605, by rfl⟩ : syracuseStep 3516281 = 2637211) B2637211
theorem B2082719 : Blo 1462551 2082719 := bstep (se 1 (by rfl) ⟨1562039, by rfl⟩ : syracuseStep 2082719 = 3124079) B3124079
theorem B5556347 : Blo 1462551 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B114010361 : Blo 1462551 114010361 := bstep (se 2 (by rfl) ⟨42753885, by rfl⟩ : syracuseStep 114010361 = 85507771) B85507771
theorem B8333563 : Blo 1462551 8333563 := bstep (se 1 (by rfl) ⟨6250172, by rfl⟩ : syracuseStep 8333563 = 12500345) B12500345
theorem B6252839 : Blo 1462551 6252839 := bstep (se 1 (by rfl) ⟨4689629, by rfl⟩ : syracuseStep 6252839 = 9379259) B9379259
theorem B3705335 : Blo 1462551 3705335 := bstep (se 1 (by rfl) ⟨2779001, by rfl⟩ : syracuseStep 3705335 = 5558003) B5558003
theorem B2779913 : Blo 1462551 2779913 := bstep (se 2 (by rfl) ⟨1042467, by rfl⟩ : syracuseStep 2779913 = 2084935) B2084935
theorem B4942619 : Blo 1462551 4942619 := bstep (se 1 (by rfl) ⟨3706964, by rfl⟩ : syracuseStep 4942619 = 7413929) B7413929
theorem B17804573 : Blo 1462551 17804573 := bstep (se 3 (by rfl) ⟨3338357, by rfl⟩ : syracuseStep 17804573 = 6676715) B6676715
theorem B3706175 : Blo 1462551 3706175 := bstep (se 1 (by rfl) ⟨2779631, by rfl⟩ : syracuseStep 3706175 = 5559263) B5559263
theorem B8335547 : Blo 1462551 8335547 := bstep (se 1 (by rfl) ⟨6251660, by rfl⟩ : syracuseStep 8335547 = 12503321) B12503321
theorem B4936247 : Blo 1462551 4936247 := bstep (se 1 (by rfl) ⟨3702185, by rfl⟩ : syracuseStep 4936247 = 7404371) B7404371
theorem B8335979 : Blo 1462551 8335979 := bstep (se 1 (by rfl) ⟨6251984, by rfl⟩ : syracuseStep 8335979 = 12503969) B12503969
theorem B1462975 : Blo 1462551 1462975 := bstep (se 1 (by rfl) ⟨1097231, by rfl⟩ : syracuseStep 1462975 = 2194463) B2194463
theorem B8336297 : Blo 1462551 8336297 := bstep (se 2 (by rfl) ⟨3126111, by rfl⟩ : syracuseStep 8336297 = 6252223) B6252223
theorem B1463327 : Blo 1462551 1463327 := bstep (se 1 (by rfl) ⟨1097495, by rfl⟩ : syracuseStep 1463327 = 2194991) B2194991
theorem B15029471 : Blo 1462551 15029471 := bstep (se 1 (by rfl) ⟨11272103, by rfl⟩ : syracuseStep 15029471 = 22544207) B22544207
theorem B10007849 : Blo 1462551 10007849 := bstep (se 2 (by rfl) ⟨3752943, by rfl⟩ : syracuseStep 10007849 = 7505887) B7505887
theorem B1463775 : Blo 1462551 1463775 := bstep (se 1 (by rfl) ⟨1097831, by rfl⟩ : syracuseStep 1463775 = 2195663) B2195663
theorem B7411337 : Blo 1462551 7411337 := bstep (se 2 (by rfl) ⟨2779251, by rfl⟩ : syracuseStep 7411337 = 5558503) B5558503
theorem B31635197 : Blo 1462551 31635197 := bstep (se 3 (by rfl) ⟨5931599, by rfl⟩ : syracuseStep 31635197 = 11863199) B11863199
theorem B5560235 : Blo 1462551 5560235 := bstep (se 1 (by rfl) ⟨4170176, by rfl⟩ : syracuseStep 5560235 = 8340353) B8340353
theorem B4937759 : Blo 1462551 4937759 := bstep (se 1 (by rfl) ⟨3703319, by rfl⟩ : syracuseStep 4937759 = 7406639) B7406639
theorem B3291191 : Blo 1462551 3291191 := bstep (se 1 (by rfl) ⟨2468393, by rfl⟩ : syracuseStep 3291191 = 4936787) B4936787
theorem B106756217 : Blo 1462551 106756217 := bstep (se 2 (by rfl) ⟨40033581, by rfl⟩ : syracuseStep 106756217 = 80067163) B80067163
theorem B3291263 : Blo 1462551 3291263 := bstep (se 1 (by rfl) ⟨2468447, by rfl⟩ : syracuseStep 3291263 = 4936895) B4936895
theorem B6674671 : Blo 1462551 6674671 := bstep (se 1 (by rfl) ⟨5006003, by rfl⟩ : syracuseStep 6674671 = 10012007) B10012007
theorem B3291731 : Blo 1462551 3291731 := bstep (se 1 (by rfl) ⟨2468798, by rfl⟩ : syracuseStep 3291731 = 4937597) B4937597
theorem B30038651 : Blo 1462551 30038651 := bstep (se 1 (by rfl) ⟨22528988, by rfl⟩ : syracuseStep 30038651 = 45057977) B45057977
theorem B3292001 : Blo 1462551 3292001 := bstep (se 2 (by rfl) ⟨1234500, by rfl⟩ : syracuseStep 3292001 = 2469001) B2469001
theorem B3292073 : Blo 1462551 3292073 := bstep (se 2 (by rfl) ⟨1234527, by rfl⟩ : syracuseStep 3292073 = 2469055) B2469055
theorem B2194415 : Blo 1462551 2194415 := bstep (se 1 (by rfl) ⟨1645811, by rfl⟩ : syracuseStep 2194415 = 3291623) B3291623
theorem B5553143 : Blo 1462551 5553143 := bstep (se 1 (by rfl) ⟨4164857, by rfl⟩ : syracuseStep 5553143 = 8329715) B8329715
theorem B2194601 : Blo 1462551 2194601 := bstep (se 2 (by rfl) ⟨822975, by rfl⟩ : syracuseStep 2194601 = 1645951) B1645951
theorem B2194607 : Blo 1462551 2194607 := bstep (se 1 (by rfl) ⟨1645955, by rfl⟩ : syracuseStep 2194607 = 3291911) B3291911
theorem B5635451 : Blo 1462551 5635451 := bstep (se 1 (by rfl) ⟨4226588, by rfl⟩ : syracuseStep 5635451 = 8453177) B8453177
theorem B7413281 : Blo 1462551 7413281 := bstep (se 2 (by rfl) ⟨2779980, by rfl⟩ : syracuseStep 7413281 = 5559961) B5559961
theorem B2195015 : Blo 1462551 2195015 := bstep (se 1 (by rfl) ⟨1646261, by rfl⟩ : syracuseStep 2195015 = 3292523) B3292523
theorem B3292775 : Blo 1462551 3292775 := bstep (se 1 (by rfl) ⟨2469581, by rfl⟩ : syracuseStep 3292775 = 4939163) B4939163
theorem B26705699 : Blo 1462551 26705699 := bstep (se 1 (by rfl) ⟨20029274, by rfl⟩ : syracuseStep 26705699 = 40058549) B40058549
theorem B2195327 : Blo 1462551 2195327 := bstep (se 1 (by rfl) ⟨1646495, by rfl⟩ : syracuseStep 2195327 = 3292991) B3292991
theorem B3956617 : Blo 1462551 3956617 := bstep (se 2 (by rfl) ⟨1483731, by rfl⟩ : syracuseStep 3956617 = 2967463) B2967463
theorem B3702743 : Blo 1462551 3702743 := bstep (se 1 (by rfl) ⟨2777057, by rfl⟩ : syracuseStep 3702743 = 5554115) B5554115
theorem B2195903 : Blo 1462551 2195903 := bstep (se 1 (by rfl) ⟨1646927, by rfl⟩ : syracuseStep 2195903 = 3293855) B3293855
theorem B3957373 : Blo 1462551 3957373 := bstep (se 3 (by rfl) ⟨742007, by rfl⟩ : syracuseStep 3957373 = 1484015) B1484015
theorem B2196095 : Blo 1462551 2196095 := bstep (se 1 (by rfl) ⟨1647071, by rfl⟩ : syracuseStep 2196095 = 3294143) B3294143
theorem B5554919 : Blo 1462551 5554919 := bstep (se 1 (by rfl) ⟨4166189, by rfl⟩ : syracuseStep 5554919 = 8332379) B8332379
theorem B10019647 : Blo 1462551 10019647 := bstep (se 1 (by rfl) ⟨7514735, by rfl⟩ : syracuseStep 10019647 = 15029471) B15029471
theorem B1852399 : Blo 1462551 1852399 := bstep (se 1 (by rfl) ⟨1389299, by rfl⟩ : syracuseStep 1852399 = 2778599) B2778599
theorem B4940891 : Blo 1462551 4940891 := bstep (se 1 (by rfl) ⟨3705668, by rfl⟩ : syracuseStep 4940891 = 7411337) B7411337
theorem B3294395 : Blo 1462551 3294395 := bstep (se 1 (by rfl) ⟨2470796, by rfl⟩ : syracuseStep 3294395 = 4941593) B4941593
theorem B3704039 : Blo 1462551 3704039 := bstep (se 1 (by rfl) ⟨2778029, by rfl⟩ : syracuseStep 3704039 = 5556059) B5556059
theorem B2344187 : Blo 1462551 2344187 := bstep (se 1 (by rfl) ⟨1758140, by rfl⟩ : syracuseStep 2344187 = 3516281) B3516281
theorem B3704231 : Blo 1462551 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B76006907 : Blo 1462551 76006907 := bstep (se 1 (by rfl) ⟨57005180, by rfl⟩ : syracuseStep 76006907 = 114010361) B114010361
theorem B1853275 : Blo 1462551 1853275 := bstep (se 1 (by rfl) ⟨1389956, by rfl⟩ : syracuseStep 1853275 = 2779913) B2779913
theorem B3295079 : Blo 1462551 3295079 := bstep (se 1 (by rfl) ⟨2471309, by rfl⟩ : syracuseStep 3295079 = 4942619) B4942619
theorem B4942187 : Blo 1462551 4942187 := bstep (se 1 (by rfl) ⟨3706640, by rfl⟩ : syracuseStep 4942187 = 7413281) B7413281
theorem B17803799 : Blo 1462551 17803799 := bstep (se 1 (by rfl) ⟨13352849, by rfl⟩ : syracuseStep 17803799 = 26705699) B26705699
theorem B2468495 : Blo 1462551 2468495 := bstep (se 1 (by rfl) ⟨1851371, by rfl⟩ : syracuseStep 2468495 = 3702743) B3702743
theorem B28142315 : Blo 1462551 28142315 := bstep (se 1 (by rfl) ⟨21106736, by rfl⟩ : syracuseStep 28142315 = 42213473) B42213473
theorem B5557031 : Blo 1462551 5557031 := bstep (se 1 (by rfl) ⟨4167773, by rfl⟩ : syracuseStep 5557031 = 8335547) B8335547
theorem B2468731 : Blo 1462551 2468731 := bstep (se 1 (by rfl) ⟨1851548, by rfl⟩ : syracuseStep 2468731 = 3703097) B3703097
theorem B8899561 : Blo 1462551 8899561 := bstep (se 2 (by rfl) ⟨3337335, by rfl⟩ : syracuseStep 8899561 = 6674671) B6674671
theorem B11111417 : Blo 1462551 11111417 := bstep (se 2 (by rfl) ⟨4166781, by rfl⟩ : syracuseStep 11111417 = 8333563) B8333563
theorem B11119679 : Blo 1462551 11119679 := bstep (se 1 (by rfl) ⟨8339759, by rfl⟩ : syracuseStep 11119679 = 16679519) B16679519
theorem B5557319 : Blo 1462551 5557319 := bstep (se 1 (by rfl) ⟨4167989, by rfl⟩ : syracuseStep 5557319 = 8335979) B8335979
theorem B2780315 : Blo 1462551 2780315 := bstep (se 1 (by rfl) ⟨2085236, by rfl⟩ : syracuseStep 2780315 = 4170473) B4170473
theorem B5557531 : Blo 1462551 5557531 := bstep (se 1 (by rfl) ⟨4168148, by rfl⟩ : syracuseStep 5557531 = 8336297) B8336297
theorem B6671899 : Blo 1462551 6671899 := bstep (se 1 (by rfl) ⟨5003924, by rfl⟩ : syracuseStep 6671899 = 10007849) B10007849
theorem B15027869 : Blo 1462551 15027869 := bstep (se 3 (by rfl) ⟨2817725, by rfl⟩ : syracuseStep 15027869 = 5635451) B5635451
theorem B21090131 : Blo 1462551 21090131 := bstep (se 1 (by rfl) ⟨15817598, by rfl⟩ : syracuseStep 21090131 = 31635197) B31635197
theorem B3706823 : Blo 1462551 3706823 := bstep (se 1 (by rfl) ⟨2780117, by rfl⟩ : syracuseStep 3706823 = 5560235) B5560235
theorem B2470223 : Blo 1462551 2470223 := bstep (se 1 (by rfl) ⟨1852667, by rfl⟩ : syracuseStep 2470223 = 3705335) B3705335
theorem B20025767 : Blo 1462551 20025767 := bstep (se 1 (by rfl) ⟨15019325, by rfl⟩ : syracuseStep 20025767 = 30038651) B30038651
theorem B1462943 : Blo 1462551 1462943 := bstep (se 1 (by rfl) ⟨1097207, by rfl⟩ : syracuseStep 1462943 = 2194415) B2194415
theorem B1463067 : Blo 1462551 1463067 := bstep (se 1 (by rfl) ⟨1097300, by rfl⟩ : syracuseStep 1463067 = 2194601) B2194601
theorem B1463071 : Blo 1462551 1463071 := bstep (se 1 (by rfl) ⟨1097303, by rfl⟩ : syracuseStep 1463071 = 2194607) B2194607
theorem B2470783 : Blo 1462551 2470783 := bstep (se 1 (by rfl) ⟨1853087, by rfl⟩ : syracuseStep 2470783 = 3706175) B3706175
theorem B1463343 : Blo 1462551 1463343 := bstep (se 1 (by rfl) ⟨1097507, by rfl⟩ : syracuseStep 1463343 = 2195015) B2195015
theorem B1463551 : Blo 1462551 1463551 := bstep (se 1 (by rfl) ⟨1097663, by rfl⟩ : syracuseStep 1463551 = 2195327) B2195327
theorem B4937327 : Blo 1462551 4937327 := bstep (se 1 (by rfl) ⟨3702995, by rfl⟩ : syracuseStep 4937327 = 7405991) B7405991
theorem B3290831 : Blo 1462551 3290831 := bstep (se 1 (by rfl) ⟨2468123, by rfl⟩ : syracuseStep 3290831 = 4936247) B4936247
theorem B20027299 : Blo 1462551 20027299 := bstep (se 1 (by rfl) ⟨15020474, by rfl⟩ : syracuseStep 20027299 = 30040949) B30040949
theorem B1464231 : Blo 1462551 1464231 := bstep (se 1 (by rfl) ⟨1098173, by rfl⟩ : syracuseStep 1464231 = 2196347) B2196347
theorem B5560265 : Blo 1462551 5560265 := bstep (se 2 (by rfl) ⟨2085099, by rfl⟩ : syracuseStep 5560265 = 4170199) B4170199
theorem B13359275 : Blo 1462551 13359275 := bstep (se 1 (by rfl) ⟨10019456, by rfl⟩ : syracuseStep 13359275 = 20038913) B20038913
theorem B3955015 : Blo 1462551 3955015 := bstep (se 1 (by rfl) ⟨2966261, by rfl⟩ : syracuseStep 3955015 = 5932523) B5932523
theorem B3291839 : Blo 1462551 3291839 := bstep (se 1 (by rfl) ⟨2468879, by rfl⟩ : syracuseStep 3291839 = 4937759) B4937759
theorem B2194127 : Blo 1462551 2194127 := bstep (se 1 (by rfl) ⟨1645595, by rfl⟩ : syracuseStep 2194127 = 3291191) B3291191
theorem B71170811 : Blo 1462551 71170811 := bstep (se 1 (by rfl) ⟨53378108, by rfl⟩ : syracuseStep 71170811 = 106756217) B106756217
theorem B2194175 : Blo 1462551 2194175 := bstep (se 1 (by rfl) ⟨1645631, by rfl⟩ : syracuseStep 2194175 = 3291263) B3291263
theorem B4168559 : Blo 1462551 4168559 := bstep (se 1 (by rfl) ⟨3126419, by rfl⟩ : syracuseStep 4168559 = 6252839) B6252839
theorem B2194487 : Blo 1462551 2194487 := bstep (se 1 (by rfl) ⟨1645865, by rfl⟩ : syracuseStep 2194487 = 3291731) B3291731
theorem B2194667 : Blo 1462551 2194667 := bstep (se 1 (by rfl) ⟨1646000, by rfl⟩ : syracuseStep 2194667 = 3292001) B3292001
theorem B8903945 : Blo 1462551 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B2194715 : Blo 1462551 2194715 := bstep (se 1 (by rfl) ⟨1646036, by rfl⟩ : syracuseStep 2194715 = 3292073) B3292073
theorem B3702095 : Blo 1462551 3702095 := bstep (se 1 (by rfl) ⟨2776571, by rfl⟩ : syracuseStep 3702095 = 5553143) B5553143
theorem B11869715 : Blo 1462551 11869715 := bstep (se 1 (by rfl) ⟨8902286, by rfl⟩ : syracuseStep 11869715 = 17804573) B17804573
theorem B2195183 : Blo 1462551 2195183 := bstep (se 1 (by rfl) ⟨1646387, by rfl⟩ : syracuseStep 2195183 = 3292775) B3292775
theorem B5553917 : Blo 1462551 5553917 := bstep (se 3 (by rfl) ⟨1041359, by rfl⟩ : syracuseStep 5553917 = 2082719) B2082719
theorem B5275489 : Blo 1462551 5275489 := bstep (se 2 (by rfl) ⟨1978308, by rfl⟩ : syracuseStep 5275489 = 3956617) B3956617
theorem B1646815 : Blo 1462551 1646815 := bstep (se 1 (by rfl) ⟨1235111, by rfl⟩ : syracuseStep 1646815 = 2470223) B2470223
theorem B3703279 : Blo 1462551 3703279 := bstep (se 1 (by rfl) ⟨2777459, by rfl⟩ : syracuseStep 3703279 = 5554919) B5554919
theorem B6251165 : Blo 1462551 6251165 := bstep (se 3 (by rfl) ⟨1172093, by rfl⟩ : syracuseStep 6251165 = 2344187) B2344187
theorem B3293927 : Blo 1462551 3293927 := bstep (se 1 (by rfl) ⟨2470445, by rfl⟩ : syracuseStep 3293927 = 4940891) B4940891
theorem B2196263 : Blo 1462551 2196263 := bstep (se 1 (by rfl) ⟨1647197, by rfl⟩ : syracuseStep 2196263 = 3294395) B3294395
theorem B5276497 : Blo 1462551 5276497 := bstep (se 2 (by rfl) ⟨1978686, by rfl⟩ : syracuseStep 5276497 = 3957373) B3957373
theorem B3294377 : Blo 1462551 3294377 := bstep (se 2 (by rfl) ⟨1235391, by rfl⟩ : syracuseStep 3294377 = 2470783) B2470783
theorem B2196719 : Blo 1462551 2196719 := bstep (se 1 (by rfl) ⟨1647539, by rfl⟩ : syracuseStep 2196719 = 3295079) B3295079
theorem B8906183 : Blo 1462551 8906183 := bstep (se 1 (by rfl) ⟨6679637, by rfl⟩ : syracuseStep 8906183 = 13359275) B13359275
theorem B3294791 : Blo 1462551 3294791 := bstep (se 1 (by rfl) ⟨2471093, by rfl⟩ : syracuseStep 3294791 = 4942187) B4942187
theorem B18761543 : Blo 1462551 18761543 := bstep (se 1 (by rfl) ⟨14071157, by rfl⟩ : syracuseStep 18761543 = 28142315) B28142315
theorem B3704687 : Blo 1462551 3704687 := bstep (se 1 (by rfl) ⟨2778515, by rfl⟩ : syracuseStep 3704687 = 5557031) B5557031
theorem B2779039 : Blo 1462551 2779039 := bstep (se 1 (by rfl) ⟨2084279, by rfl⟩ : syracuseStep 2779039 = 4168559) B4168559
theorem B7407611 : Blo 1462551 7407611 := bstep (se 1 (by rfl) ⟨5555708, by rfl⟩ : syracuseStep 7407611 = 11111417) B11111417
theorem B3704879 : Blo 1462551 3704879 := bstep (se 1 (by rfl) ⟨2778659, by rfl⟩ : syracuseStep 3704879 = 5557319) B5557319
theorem B1853543 : Blo 1462551 1853543 := bstep (se 1 (by rfl) ⟨1390157, by rfl⟩ : syracuseStep 1853543 = 2780315) B2780315
theorem B2468063 : Blo 1462551 2468063 := bstep (se 1 (by rfl) ⟨1851047, by rfl⟩ : syracuseStep 2468063 = 3702095) B3702095
theorem B14060087 : Blo 1462551 14060087 := bstep (se 1 (by rfl) ⟨10545065, by rfl⟩ : syracuseStep 14060087 = 21090131) B21090131
theorem B2469359 : Blo 1462551 2469359 := bstep (se 1 (by rfl) ⟨1852019, by rfl⟩ : syracuseStep 2469359 = 3704039) B3704039
theorem B2469487 : Blo 1462551 2469487 := bstep (se 1 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 2469487 = 3704231) B3704231
theorem B50671271 : Blo 1462551 50671271 := bstep (se 1 (by rfl) ⟨38003453, by rfl⟩ : syracuseStep 50671271 = 76006907) B76006907
theorem B3706843 : Blo 1462551 3706843 := bstep (se 1 (by rfl) ⟨2780132, by rfl⟩ : syracuseStep 3706843 = 5560265) B5560265
theorem B2469865 : Blo 1462551 2469865 := bstep (se 2 (by rfl) ⟨926199, by rfl⟩ : syracuseStep 2469865 = 1852399) B1852399
theorem B7410041 : Blo 1462551 7410041 := bstep (se 2 (by rfl) ⟨2778765, by rfl⟩ : syracuseStep 7410041 = 5557531) B5557531
theorem B1462751 : Blo 1462551 1462751 := bstep (se 1 (by rfl) ⟨1097063, by rfl⟩ : syracuseStep 1462751 = 2194127) B2194127
theorem B1462783 : Blo 1462551 1462783 := bstep (se 1 (by rfl) ⟨1097087, by rfl⟩ : syracuseStep 1462783 = 2194175) B2194175
theorem B1462991 : Blo 1462551 1462991 := bstep (se 1 (by rfl) ⟨1097243, by rfl⟩ : syracuseStep 1462991 = 2194487) B2194487
theorem B1463111 : Blo 1462551 1463111 := bstep (se 1 (by rfl) ⟨1097333, by rfl⟩ : syracuseStep 1463111 = 2194667) B2194667
theorem B5935963 : Blo 1462551 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B1463143 : Blo 1462551 1463143 := bstep (se 1 (by rfl) ⟨1097357, by rfl⟩ : syracuseStep 1463143 = 2194715) B2194715
theorem B2471033 : Blo 1462551 2471033 := bstep (se 2 (by rfl) ⟨926637, by rfl⟩ : syracuseStep 2471033 = 1853275) B1853275
theorem B7033985 : Blo 1462551 7033985 := bstep (se 2 (by rfl) ⟨2637744, by rfl⟩ : syracuseStep 7033985 = 5275489) B5275489
theorem B1463455 : Blo 1462551 1463455 := bstep (se 1 (by rfl) ⟨1097591, by rfl⟩ : syracuseStep 1463455 = 2195183) B2195183
theorem B26703065 : Blo 1462551 26703065 := bstep (se 2 (by rfl) ⟨10013649, by rfl⟩ : syracuseStep 26703065 = 20027299) B20027299
theorem B2471215 : Blo 1462551 2471215 := bstep (se 1 (by rfl) ⟨1853411, by rfl⟩ : syracuseStep 2471215 = 3706823) B3706823
theorem B35583461 : Blo 1462551 35583461 := bstep (se 4 (by rfl) ⟨3335949, by rfl⟩ : syracuseStep 35583461 = 6671899) B6671899
theorem B13350511 : Blo 1462551 13350511 := bstep (se 1 (by rfl) ⟨10012883, by rfl⟩ : syracuseStep 13350511 = 20025767) B20025767
theorem B1463935 : Blo 1462551 1463935 := bstep (se 1 (by rfl) ⟨1097951, by rfl⟩ : syracuseStep 1463935 = 2195903) B2195903
theorem B1464063 : Blo 1462551 1464063 := bstep (se 1 (by rfl) ⟨1098047, by rfl⟩ : syracuseStep 1464063 = 2196095) B2196095
theorem B5273353 : Blo 1462551 5273353 := bstep (se 2 (by rfl) ⟨1977507, by rfl⟩ : syracuseStep 5273353 = 3955015) B3955015
theorem B3291551 : Blo 1462551 3291551 := bstep (se 1 (by rfl) ⟨2468663, by rfl⟩ : syracuseStep 3291551 = 4937327) B4937327
theorem B13359529 : Blo 1462551 13359529 := bstep (se 2 (by rfl) ⟨5009823, by rfl⟩ : syracuseStep 13359529 = 10019647) B10019647
theorem B2193887 : Blo 1462551 2193887 := bstep (se 1 (by rfl) ⟨1645415, by rfl⟩ : syracuseStep 2193887 = 3290831) B3290831
theorem B3291641 : Blo 1462551 3291641 := bstep (se 2 (by rfl) ⟨1234365, by rfl⟩ : syracuseStep 3291641 = 2468731) B2468731
theorem B11869199 : Blo 1462551 11869199 := bstep (se 1 (by rfl) ⟨8901899, by rfl⟩ : syracuseStep 11869199 = 17803799) B17803799
theorem B1645663 : Blo 1462551 1645663 := bstep (se 1 (by rfl) ⟨1234247, by rfl⟩ : syracuseStep 1645663 = 2468495) B2468495
theorem B2194559 : Blo 1462551 2194559 := bstep (se 1 (by rfl) ⟨1645919, by rfl⟩ : syracuseStep 2194559 = 3291839) B3291839
theorem B47447207 : Blo 1462551 47447207 := bstep (se 1 (by rfl) ⟨35585405, by rfl⟩ : syracuseStep 47447207 = 71170811) B71170811
theorem B7413119 : Blo 1462551 7413119 := bstep (se 1 (by rfl) ⟨5559839, by rfl⟩ : syracuseStep 7413119 = 11119679) B11119679
theorem B7913143 : Blo 1462551 7913143 := bstep (se 1 (by rfl) ⟨5934857, by rfl⟩ : syracuseStep 7913143 = 11869715) B11869715
theorem B10018579 : Blo 1462551 10018579 := bstep (se 1 (by rfl) ⟨7513934, by rfl⟩ : syracuseStep 10018579 = 15027869) B15027869
theorem B3702611 : Blo 1462551 3702611 := bstep (se 1 (by rfl) ⟨2776958, by rfl⟩ : syracuseStep 3702611 = 5553917) B5553917
theorem B47464325 : Blo 1462551 47464325 := bstep (se 4 (by rfl) ⟨4449780, by rfl⟩ : syracuseStep 47464325 = 8899561) B8899561
theorem B4940027 : Blo 1462551 4940027 := bstep (se 1 (by rfl) ⟨3705020, by rfl⟩ : syracuseStep 4940027 = 7410041) B7410041
theorem B2195753 : Blo 1462551 2195753 := bstep (se 2 (by rfl) ⟨823407, by rfl⟩ : syracuseStep 2195753 = 1646815) B1646815
theorem B2195951 : Blo 1462551 2195951 := bstep (se 1 (by rfl) ⟨1646963, by rfl⟩ : syracuseStep 2195951 = 3293927) B3293927
theorem B1647355 : Blo 1462551 1647355 := bstep (se 1 (by rfl) ⟨1235516, by rfl⟩ : syracuseStep 1647355 = 2471033) B2471033
theorem B2196251 : Blo 1462551 2196251 := bstep (se 1 (by rfl) ⟨1647188, by rfl⟩ : syracuseStep 2196251 = 3294377) B3294377
theorem B2196527 : Blo 1462551 2196527 := bstep (se 1 (by rfl) ⟨1647395, by rfl⟩ : syracuseStep 2196527 = 3294791) B3294791
theorem B7914617 : Blo 1462551 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B9373391 : Blo 1462551 9373391 := bstep (se 1 (by rfl) ⟨7030043, by rfl⟩ : syracuseStep 9373391 = 14060087) B14060087
theorem B3294953 : Blo 1462551 3294953 := bstep (se 2 (by rfl) ⟨1235607, by rfl⟩ : syracuseStep 3294953 = 2471215) B2471215
theorem B31631471 : Blo 1462551 31631471 := bstep (se 1 (by rfl) ⟨23723603, by rfl⟩ : syracuseStep 31631471 = 47447207) B47447207
theorem B4942079 : Blo 1462551 4942079 := bstep (se 1 (by rfl) ⟨3706559, by rfl⟩ : syracuseStep 4942079 = 7413119) B7413119
theorem B7031137 : Blo 1462551 7031137 := bstep (se 2 (by rfl) ⟨2636676, by rfl⟩ : syracuseStep 7031137 = 5273353) B5273353
theorem B3705385 : Blo 1462551 3705385 := bstep (se 2 (by rfl) ⟨1389519, by rfl⟩ : syracuseStep 3705385 = 2779039) B2779039
theorem B2468407 : Blo 1462551 2468407 := bstep (se 1 (by rfl) ⟨1851305, by rfl⟩ : syracuseStep 2468407 = 3702611) B3702611
theorem B4942457 : Blo 1462551 4942457 := bstep (se 2 (by rfl) ⟨1853421, by rfl⟩ : syracuseStep 4942457 = 3706843) B3706843
theorem B4942781 : Blo 1462551 4942781 := bstep (se 3 (by rfl) ⟨926771, by rfl⟩ : syracuseStep 4942781 = 1853543) B1853543
theorem B17812705 : Blo 1462551 17812705 := bstep (se 2 (by rfl) ⟨6679764, by rfl⟩ : syracuseStep 17812705 = 13359529) B13359529
theorem B71208173 : Blo 1462551 71208173 := bstep (se 3 (by rfl) ⟨13351532, by rfl⟩ : syracuseStep 71208173 = 26703065) B26703065
theorem B4689323 : Blo 1462551 4689323 := bstep (se 1 (by rfl) ⟨3516992, by rfl⟩ : syracuseStep 4689323 = 7033985) B7033985
theorem B2469791 : Blo 1462551 2469791 := bstep (se 1 (by rfl) ⟨1852343, by rfl⟩ : syracuseStep 2469791 = 3704687) B3704687
theorem B2469919 : Blo 1462551 2469919 := bstep (se 1 (by rfl) ⟨1852439, by rfl⟩ : syracuseStep 2469919 = 3704879) B3704879
theorem B1462591 : Blo 1462551 1462591 := bstep (se 1 (by rfl) ⟨1096943, by rfl⟩ : syracuseStep 1462591 = 2193887) B2193887
theorem B1463039 : Blo 1462551 1463039 := bstep (se 1 (by rfl) ⟨1097279, by rfl⟩ : syracuseStep 1463039 = 2194559) B2194559
theorem B13358105 : Blo 1462551 13358105 := bstep (se 2 (by rfl) ⟨5009289, by rfl⟩ : syracuseStep 13358105 = 10018579) B10018579
theorem B33780847 : Blo 1462551 33780847 := bstep (se 1 (by rfl) ⟨25335635, by rfl⟩ : syracuseStep 33780847 = 50671271) B50671271
theorem B31642883 : Blo 1462551 31642883 := bstep (se 1 (by rfl) ⟨23732162, by rfl⟩ : syracuseStep 31642883 = 47464325) B47464325
theorem B4167443 : Blo 1462551 4167443 := bstep (se 1 (by rfl) ⟨3125582, by rfl⟩ : syracuseStep 4167443 = 6251165) B6251165
theorem B1464175 : Blo 1462551 1464175 := bstep (se 1 (by rfl) ⟨1098131, by rfl⟩ : syracuseStep 1464175 = 2196263) B2196263
theorem B4937705 : Blo 1462551 4937705 := bstep (se 2 (by rfl) ⟨1851639, by rfl⟩ : syracuseStep 4937705 = 3703279) B3703279
theorem B1464479 : Blo 1462551 1464479 := bstep (se 1 (by rfl) ⟨1098359, by rfl⟩ : syracuseStep 1464479 = 2196719) B2196719
theorem B42203429 : Blo 1462551 42203429 := bstep (se 4 (by rfl) ⟨3956571, by rfl⟩ : syracuseStep 42203429 = 7913143) B7913143
theorem B5937455 : Blo 1462551 5937455 := bstep (se 1 (by rfl) ⟨4453091, by rfl⟩ : syracuseStep 5937455 = 8906183) B8906183
theorem B23722307 : Blo 1462551 23722307 := bstep (se 1 (by rfl) ⟨17791730, by rfl⟩ : syracuseStep 23722307 = 35583461) B35583461
theorem B7035329 : Blo 1462551 7035329 := bstep (se 2 (by rfl) ⟨2638248, by rfl⟩ : syracuseStep 7035329 = 5276497) B5276497
theorem B12507695 : Blo 1462551 12507695 := bstep (se 1 (by rfl) ⟨9380771, by rfl⟩ : syracuseStep 12507695 = 18761543) B18761543
theorem B4938407 : Blo 1462551 4938407 := bstep (se 1 (by rfl) ⟨3703805, by rfl⟩ : syracuseStep 4938407 = 7407611) B7407611
theorem B2194217 : Blo 1462551 2194217 := bstep (se 2 (by rfl) ⟨822831, by rfl⟩ : syracuseStep 2194217 = 1645663) B1645663
theorem B1645375 : Blo 1462551 1645375 := bstep (se 1 (by rfl) ⟨1234031, by rfl⟩ : syracuseStep 1645375 = 2468063) B2468063
theorem B2194367 : Blo 1462551 2194367 := bstep (se 1 (by rfl) ⟨1645775, by rfl⟩ : syracuseStep 2194367 = 3291551) B3291551
theorem B2194427 : Blo 1462551 2194427 := bstep (se 1 (by rfl) ⟨1645820, by rfl⟩ : syracuseStep 2194427 = 3291641) B3291641
theorem B7912799 : Blo 1462551 7912799 := bstep (se 1 (by rfl) ⟨5934599, by rfl⟩ : syracuseStep 7912799 = 11869199) B11869199
theorem B3292649 : Blo 1462551 3292649 := bstep (se 2 (by rfl) ⟨1234743, by rfl⟩ : syracuseStep 3292649 = 2469487) B2469487
theorem B17800681 : Blo 1462551 17800681 := bstep (se 2 (by rfl) ⟨6675255, by rfl⟩ : syracuseStep 17800681 = 13350511) B13350511
theorem B1646239 : Blo 1462551 1646239 := bstep (se 1 (by rfl) ⟨1234679, by rfl⟩ : syracuseStep 1646239 = 2469359) B2469359
theorem B3293153 : Blo 1462551 3293153 := bstep (se 2 (by rfl) ⟨1234932, by rfl⟩ : syracuseStep 3293153 = 2469865) B2469865
theorem B3293225 : Blo 1462551 3293225 := bstep (se 2 (by rfl) ⟨1234959, by rfl⟩ : syracuseStep 3293225 = 2469919) B2469919
theorem B3293351 : Blo 1462551 3293351 := bstep (se 1 (by rfl) ⟨2470013, by rfl⟩ : syracuseStep 3293351 = 4940027) B4940027
theorem B8905403 : Blo 1462551 8905403 := bstep (se 1 (by rfl) ⟨6679052, by rfl⟩ : syracuseStep 8905403 = 13358105) B13358105
theorem B4940513 : Blo 1462551 4940513 := bstep (se 2 (by rfl) ⟨1852692, by rfl⟩ : syracuseStep 4940513 = 3705385) B3705385
theorem B5276411 : Blo 1462551 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B21095255 : Blo 1462551 21095255 := bstep (se 1 (by rfl) ⟨15821441, by rfl⟩ : syracuseStep 21095255 = 31642883) B31642883
theorem B2196473 : Blo 1462551 2196473 := bstep (se 2 (by rfl) ⟨823677, by rfl⟩ : syracuseStep 2196473 = 1647355) B1647355
theorem B2196635 : Blo 1462551 2196635 := bstep (se 1 (by rfl) ⟨1647476, by rfl⟩ : syracuseStep 2196635 = 3294953) B3294953
theorem B2778295 : Blo 1462551 2778295 := bstep (se 1 (by rfl) ⟨2083721, by rfl⟩ : syracuseStep 2778295 = 4167443) B4167443
theorem B21087647 : Blo 1462551 21087647 := bstep (se 1 (by rfl) ⟨15815735, by rfl⟩ : syracuseStep 21087647 = 31631471) B31631471
theorem B45041129 : Blo 1462551 45041129 := bstep (se 2 (by rfl) ⟨16890423, by rfl⟩ : syracuseStep 45041129 = 33780847) B33780847
theorem B3294719 : Blo 1462551 3294719 := bstep (se 1 (by rfl) ⟨2471039, by rfl⟩ : syracuseStep 3294719 = 4942079) B4942079
theorem B3958303 : Blo 1462551 3958303 := bstep (se 1 (by rfl) ⟨2968727, by rfl⟩ : syracuseStep 3958303 = 5937455) B5937455
theorem B23750273 : Blo 1462551 23750273 := bstep (se 2 (by rfl) ⟨8906352, by rfl⟩ : syracuseStep 23750273 = 17812705) B17812705
theorem B3294971 : Blo 1462551 3294971 := bstep (se 1 (by rfl) ⟨2471228, by rfl⟩ : syracuseStep 3294971 = 4942457) B4942457
theorem B3295187 : Blo 1462551 3295187 := bstep (se 1 (by rfl) ⟨2471390, by rfl⟩ : syracuseStep 3295187 = 4942781) B4942781
theorem B23734241 : Blo 1462551 23734241 := bstep (se 2 (by rfl) ⟨8900340, by rfl⟩ : syracuseStep 23734241 = 17800681) B17800681
theorem B9374849 : Blo 1462551 9374849 := bstep (se 2 (by rfl) ⟨3515568, by rfl⟩ : syracuseStep 9374849 = 7031137) B7031137
theorem B28135619 : Blo 1462551 28135619 := bstep (se 1 (by rfl) ⟨21101714, by rfl⟩ : syracuseStep 28135619 = 42203429) B42203429
theorem B15814871 : Blo 1462551 15814871 := bstep (se 1 (by rfl) ⟨11861153, by rfl⟩ : syracuseStep 15814871 = 23722307) B23722307
theorem B4690219 : Blo 1462551 4690219 := bstep (se 1 (by rfl) ⟨3517664, by rfl⟩ : syracuseStep 4690219 = 7035329) B7035329
theorem B1462811 : Blo 1462551 1462811 := bstep (se 1 (by rfl) ⟨1097108, by rfl⟩ : syracuseStep 1462811 = 2194217) B2194217
theorem B1462911 : Blo 1462551 1462911 := bstep (se 1 (by rfl) ⟨1097183, by rfl⟩ : syracuseStep 1462911 = 2194367) B2194367
theorem B1462951 : Blo 1462551 1462951 := bstep (se 1 (by rfl) ⟨1097213, by rfl⟩ : syracuseStep 1462951 = 2194427) B2194427
theorem B3126215 : Blo 1462551 3126215 := bstep (se 1 (by rfl) ⟨2344661, by rfl⟩ : syracuseStep 3126215 = 4689323) B4689323
theorem B1463835 : Blo 1462551 1463835 := bstep (se 1 (by rfl) ⟨1097876, by rfl⟩ : syracuseStep 1463835 = 2195753) B2195753
theorem B1463967 : Blo 1462551 1463967 := bstep (se 1 (by rfl) ⟨1097975, by rfl⟩ : syracuseStep 1463967 = 2195951) B2195951
theorem B1464167 : Blo 1462551 1464167 := bstep (se 1 (by rfl) ⟨1098125, by rfl⟩ : syracuseStep 1464167 = 2196251) B2196251
theorem B1464351 : Blo 1462551 1464351 := bstep (se 1 (by rfl) ⟨1098263, by rfl⟩ : syracuseStep 1464351 = 2196527) B2196527
theorem B3291209 : Blo 1462551 3291209 := bstep (se 2 (by rfl) ⟨1234203, by rfl⟩ : syracuseStep 3291209 = 2468407) B2468407
theorem B2193833 : Blo 1462551 2193833 := bstep (se 2 (by rfl) ⟨822687, by rfl⟩ : syracuseStep 2193833 = 1645375) B1645375
theorem B6248927 : Blo 1462551 6248927 := bstep (se 1 (by rfl) ⟨4686695, by rfl⟩ : syracuseStep 6248927 = 9373391) B9373391
theorem B3291803 : Blo 1462551 3291803 := bstep (se 1 (by rfl) ⟨2468852, by rfl⟩ : syracuseStep 3291803 = 4937705) B4937705
theorem B8338463 : Blo 1462551 8338463 := bstep (se 1 (by rfl) ⟨6253847, by rfl⟩ : syracuseStep 8338463 = 12507695) B12507695
theorem B3292271 : Blo 1462551 3292271 := bstep (se 1 (by rfl) ⟨2469203, by rfl⟩ : syracuseStep 3292271 = 4938407) B4938407
theorem B47472115 : Blo 1462551 47472115 := bstep (se 1 (by rfl) ⟨35604086, by rfl⟩ : syracuseStep 47472115 = 71208173) B71208173
theorem B2194985 : Blo 1462551 2194985 := bstep (se 2 (by rfl) ⟨823119, by rfl⟩ : syracuseStep 2194985 = 1646239) B1646239
theorem B5275199 : Blo 1462551 5275199 := bstep (se 1 (by rfl) ⟨3956399, by rfl⟩ : syracuseStep 5275199 = 7912799) B7912799
theorem B2195099 : Blo 1462551 2195099 := bstep (se 1 (by rfl) ⟨1646324, by rfl⟩ : syracuseStep 2195099 = 3292649) B3292649
theorem B1646527 : Blo 1462551 1646527 := bstep (se 1 (by rfl) ⟨1234895, by rfl⟩ : syracuseStep 1646527 = 2469791) B2469791
theorem B2195435 : Blo 1462551 2195435 := bstep (se 1 (by rfl) ⟨1646576, by rfl⟩ : syracuseStep 2195435 = 3293153) B3293153
theorem B2195483 : Blo 1462551 2195483 := bstep (se 1 (by rfl) ⟨1646612, by rfl⟩ : syracuseStep 2195483 = 3293225) B3293225
theorem B2195567 : Blo 1462551 2195567 := bstep (se 1 (by rfl) ⟨1646675, by rfl⟩ : syracuseStep 2195567 = 3293351) B3293351
theorem B10543247 : Blo 1462551 10543247 := bstep (se 1 (by rfl) ⟨7907435, by rfl⟩ : syracuseStep 10543247 = 15814871) B15814871
theorem B3293675 : Blo 1462551 3293675 := bstep (se 1 (by rfl) ⟨2470256, by rfl⟩ : syracuseStep 3293675 = 4940513) B4940513
theorem B14058431 : Blo 1462551 14058431 := bstep (se 1 (by rfl) ⟨10543823, by rfl⟩ : syracuseStep 14058431 = 21087647) B21087647
theorem B2196479 : Blo 1462551 2196479 := bstep (se 1 (by rfl) ⟨1647359, by rfl⟩ : syracuseStep 2196479 = 3294719) B3294719
theorem B2196647 : Blo 1462551 2196647 := bstep (se 1 (by rfl) ⟨1647485, by rfl⟩ : syracuseStep 2196647 = 3294971) B3294971
theorem B2196791 : Blo 1462551 2196791 := bstep (se 1 (by rfl) ⟨1647593, by rfl⟩ : syracuseStep 2196791 = 3295187) B3295187
theorem B3704393 : Blo 1462551 3704393 := bstep (se 2 (by rfl) ⟨1389147, by rfl⟩ : syracuseStep 3704393 = 2778295) B2778295
theorem B5277737 : Blo 1462551 5277737 := bstep (se 2 (by rfl) ⟨1979151, by rfl⟩ : syracuseStep 5277737 = 3958303) B3958303
theorem B3516799 : Blo 1462551 3516799 := bstep (se 1 (by rfl) ⟨2637599, by rfl⟩ : syracuseStep 3516799 = 5275199) B5275199
theorem B6253625 : Blo 1462551 6253625 := bstep (se 2 (by rfl) ⟨2345109, by rfl⟩ : syracuseStep 6253625 = 4690219) B4690219
theorem B3517607 : Blo 1462551 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B2084143 : Blo 1462551 2084143 := bstep (se 1 (by rfl) ⟨1563107, by rfl⟩ : syracuseStep 2084143 = 3126215) B3126215
theorem B30027419 : Blo 1462551 30027419 := bstep (se 1 (by rfl) ⟨22520564, by rfl⟩ : syracuseStep 30027419 = 45041129) B45041129
theorem B15822827 : Blo 1462551 15822827 := bstep (se 1 (by rfl) ⟨11867120, by rfl⟩ : syracuseStep 15822827 = 23734241) B23734241
theorem B1462555 : Blo 1462551 1462555 := bstep (se 1 (by rfl) ⟨1096916, by rfl⟩ : syracuseStep 1462555 = 2193833) B2193833
theorem B4165951 : Blo 1462551 4165951 := bstep (se 1 (by rfl) ⟨3124463, by rfl⟩ : syracuseStep 4165951 = 6248927) B6248927
theorem B63296153 : Blo 1462551 63296153 := bstep (se 2 (by rfl) ⟨23736057, by rfl⟩ : syracuseStep 63296153 = 47472115) B47472115
theorem B5558975 : Blo 1462551 5558975 := bstep (se 1 (by rfl) ⟨4169231, by rfl⟩ : syracuseStep 5558975 = 8338463) B8338463
theorem B1463323 : Blo 1462551 1463323 := bstep (se 1 (by rfl) ⟨1097492, by rfl⟩ : syracuseStep 1463323 = 2194985) B2194985
theorem B1463399 : Blo 1462551 1463399 := bstep (se 1 (by rfl) ⟨1097549, by rfl⟩ : syracuseStep 1463399 = 2195099) B2195099
theorem B1463623 : Blo 1462551 1463623 := bstep (se 1 (by rfl) ⟨1097717, by rfl⟩ : syracuseStep 1463623 = 2195435) B2195435
theorem B18757079 : Blo 1462551 18757079 := bstep (se 1 (by rfl) ⟨14067809, by rfl⟩ : syracuseStep 18757079 = 28135619) B28135619
theorem B5936935 : Blo 1462551 5936935 := bstep (se 1 (by rfl) ⟨4452701, by rfl⟩ : syracuseStep 5936935 = 8905403) B8905403
theorem B1464315 : Blo 1462551 1464315 := bstep (se 1 (by rfl) ⟨1098236, by rfl⟩ : syracuseStep 1464315 = 2196473) B2196473
theorem B1464423 : Blo 1462551 1464423 := bstep (se 1 (by rfl) ⟨1098317, by rfl⟩ : syracuseStep 1464423 = 2196635) B2196635
theorem B15833515 : Blo 1462551 15833515 := bstep (se 1 (by rfl) ⟨11875136, by rfl⟩ : syracuseStep 15833515 = 23750273) B23750273
theorem B2194139 : Blo 1462551 2194139 := bstep (se 1 (by rfl) ⟨1645604, by rfl⟩ : syracuseStep 2194139 = 3291209) B3291209
theorem B2194535 : Blo 1462551 2194535 := bstep (se 1 (by rfl) ⟨1645901, by rfl⟩ : syracuseStep 2194535 = 3291803) B3291803
theorem B2194847 : Blo 1462551 2194847 := bstep (se 1 (by rfl) ⟨1646135, by rfl⟩ : syracuseStep 2194847 = 3292271) B3292271
theorem B6249899 : Blo 1462551 6249899 := bstep (se 1 (by rfl) ⟨4687424, by rfl⟩ : syracuseStep 6249899 = 9374849) B9374849
theorem B56254013 : Blo 1462551 56254013 := bstep (se 3 (by rfl) ⟨10547627, by rfl⟩ : syracuseStep 56254013 = 21095255) B21095255
theorem B2195369 : Blo 1462551 2195369 := bstep (se 2 (by rfl) ⟨823263, by rfl⟩ : syracuseStep 2195369 = 1646527) B1646527
theorem B7028831 : Blo 1462551 7028831 := bstep (se 1 (by rfl) ⟨5271623, by rfl⟩ : syracuseStep 7028831 = 10543247) B10543247
theorem B2195783 : Blo 1462551 2195783 := bstep (se 1 (by rfl) ⟨1646837, by rfl⟩ : syracuseStep 2195783 = 3293675) B3293675
theorem B5554601 : Blo 1462551 5554601 := bstep (se 2 (by rfl) ⟨2082975, by rfl⟩ : syracuseStep 5554601 = 4165951) B4165951
theorem B42197435 : Blo 1462551 42197435 := bstep (se 1 (by rfl) ⟨31648076, by rfl⟩ : syracuseStep 42197435 = 63296153) B63296153
theorem B9380285 : Blo 1462551 9380285 := bstep (se 3 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 9380285 = 3517607) B3517607
theorem B21111353 : Blo 1462551 21111353 := bstep (se 2 (by rfl) ⟨7916757, by rfl⟩ : syracuseStep 21111353 = 15833515) B15833515
theorem B9372287 : Blo 1462551 9372287 := bstep (se 1 (by rfl) ⟨7029215, by rfl⟩ : syracuseStep 9372287 = 14058431) B14058431
theorem B2778857 : Blo 1462551 2778857 := bstep (se 2 (by rfl) ⟨1042071, by rfl⟩ : syracuseStep 2778857 = 2084143) B2084143
theorem B7915913 : Blo 1462551 7915913 := bstep (se 2 (by rfl) ⟨2968467, by rfl⟩ : syracuseStep 7915913 = 5936935) B5936935
theorem B3705983 : Blo 1462551 3705983 := bstep (se 1 (by rfl) ⟨2779487, by rfl⟩ : syracuseStep 3705983 = 5558975) B5558975
theorem B4689065 : Blo 1462551 4689065 := bstep (se 2 (by rfl) ⟨1758399, by rfl⟩ : syracuseStep 4689065 = 3516799) B3516799
theorem B12504719 : Blo 1462551 12504719 := bstep (se 1 (by rfl) ⟨9378539, by rfl⟩ : syracuseStep 12504719 = 18757079) B18757079
theorem B2469595 : Blo 1462551 2469595 := bstep (se 1 (by rfl) ⟨1852196, by rfl⟩ : syracuseStep 2469595 = 3704393) B3704393
theorem B16666397 : Blo 1462551 16666397 := bstep (se 3 (by rfl) ⟨3124949, by rfl⟩ : syracuseStep 16666397 = 6249899) B6249899
theorem B3518491 : Blo 1462551 3518491 := bstep (se 1 (by rfl) ⟨2638868, by rfl⟩ : syracuseStep 3518491 = 5277737) B5277737
theorem B1462759 : Blo 1462551 1462759 := bstep (se 1 (by rfl) ⟨1097069, by rfl⟩ : syracuseStep 1462759 = 2194139) B2194139
theorem B1463023 : Blo 1462551 1463023 := bstep (se 1 (by rfl) ⟨1097267, by rfl⟩ : syracuseStep 1463023 = 2194535) B2194535
theorem B1463231 : Blo 1462551 1463231 := bstep (se 1 (by rfl) ⟨1097423, by rfl⟩ : syracuseStep 1463231 = 2194847) B2194847
theorem B20018279 : Blo 1462551 20018279 := bstep (se 1 (by rfl) ⟨15013709, by rfl⟩ : syracuseStep 20018279 = 30027419) B30027419
theorem B1463579 : Blo 1462551 1463579 := bstep (se 1 (by rfl) ⟨1097684, by rfl⟩ : syracuseStep 1463579 = 2195369) B2195369
theorem B10548551 : Blo 1462551 10548551 := bstep (se 1 (by rfl) ⟨7911413, by rfl⟩ : syracuseStep 10548551 = 15822827) B15822827
theorem B1463655 : Blo 1462551 1463655 := bstep (se 1 (by rfl) ⟨1097741, by rfl⟩ : syracuseStep 1463655 = 2195483) B2195483
theorem B1463711 : Blo 1462551 1463711 := bstep (se 1 (by rfl) ⟨1097783, by rfl⟩ : syracuseStep 1463711 = 2195567) B2195567
theorem B1464319 : Blo 1462551 1464319 := bstep (se 1 (by rfl) ⟨1098239, by rfl⟩ : syracuseStep 1464319 = 2196479) B2196479
theorem B1464431 : Blo 1462551 1464431 := bstep (se 1 (by rfl) ⟨1098323, by rfl⟩ : syracuseStep 1464431 = 2196647) B2196647
theorem B1464527 : Blo 1462551 1464527 := bstep (se 1 (by rfl) ⟨1098395, by rfl⟩ : syracuseStep 1464527 = 2196791) B2196791
theorem B4169083 : Blo 1462551 4169083 := bstep (se 1 (by rfl) ⟨3126812, by rfl⟩ : syracuseStep 4169083 = 6253625) B6253625
theorem B37502675 : Blo 1462551 37502675 := bstep (se 1 (by rfl) ⟨28127006, by rfl⟩ : syracuseStep 37502675 = 56254013) B56254013
theorem B4685887 : Blo 1462551 4685887 := bstep (se 1 (by rfl) ⟨3514415, by rfl⟩ : syracuseStep 4685887 = 7028831) B7028831
theorem B3703067 : Blo 1462551 3703067 := bstep (se 1 (by rfl) ⟨2777300, by rfl⟩ : syracuseStep 3703067 = 5554601) B5554601
theorem B28131623 : Blo 1462551 28131623 := bstep (se 1 (by rfl) ⟨21098717, by rfl⟩ : syracuseStep 28131623 = 42197435) B42197435
theorem B14074235 : Blo 1462551 14074235 := bstep (se 1 (by rfl) ⟨10555676, by rfl⟩ : syracuseStep 14074235 = 21111353) B21111353
theorem B13345519 : Blo 1462551 13345519 := bstep (se 1 (by rfl) ⟨10009139, by rfl⟩ : syracuseStep 13345519 = 20018279) B20018279
theorem B1852571 : Blo 1462551 1852571 := bstep (se 1 (by rfl) ⟨1389428, by rfl⟩ : syracuseStep 1852571 = 2778857) B2778857
theorem B5277275 : Blo 1462551 5277275 := bstep (se 1 (by rfl) ⟨3957956, by rfl⟩ : syracuseStep 5277275 = 7915913) B7915913
theorem B11110931 : Blo 1462551 11110931 := bstep (se 1 (by rfl) ⟨8333198, by rfl⟩ : syracuseStep 11110931 = 16666397) B16666397
theorem B6253523 : Blo 1462551 6253523 := bstep (se 1 (by rfl) ⟨4690142, by rfl⟩ : syracuseStep 6253523 = 9380285) B9380285
theorem B7032367 : Blo 1462551 7032367 := bstep (se 1 (by rfl) ⟨5274275, by rfl⟩ : syracuseStep 7032367 = 10548551) B10548551
theorem B5558777 : Blo 1462551 5558777 := bstep (se 2 (by rfl) ⟨2084541, by rfl⟩ : syracuseStep 5558777 = 4169083) B4169083
theorem B2470655 : Blo 1462551 2470655 := bstep (se 1 (by rfl) ⟨1852991, by rfl⟩ : syracuseStep 2470655 = 3705983) B3705983
theorem B3126043 : Blo 1462551 3126043 := bstep (se 1 (by rfl) ⟨2344532, by rfl⟩ : syracuseStep 3126043 = 4689065) B4689065
theorem B8336479 : Blo 1462551 8336479 := bstep (se 1 (by rfl) ⟨6252359, by rfl⟩ : syracuseStep 8336479 = 12504719) B12504719
theorem B4691321 : Blo 1462551 4691321 := bstep (se 2 (by rfl) ⟨1759245, by rfl⟩ : syracuseStep 4691321 = 3518491) B3518491
theorem B1463855 : Blo 1462551 1463855 := bstep (se 1 (by rfl) ⟨1097891, by rfl⟩ : syracuseStep 1463855 = 2195783) B2195783
theorem B6248191 : Blo 1462551 6248191 := bstep (se 1 (by rfl) ⟨4686143, by rfl⟩ : syracuseStep 6248191 = 9372287) B9372287
theorem B3292793 : Blo 1462551 3292793 := bstep (se 2 (by rfl) ⟨1234797, by rfl⟩ : syracuseStep 3292793 = 2469595) B2469595
theorem B25001783 : Blo 1462551 25001783 := bstep (se 1 (by rfl) ⟨18751337, by rfl⟩ : syracuseStep 25001783 = 37502675) B37502675
theorem B4940189 : Blo 1462551 4940189 := bstep (se 3 (by rfl) ⟨926285, by rfl⟩ : syracuseStep 4940189 = 1852571) B1852571
theorem B1647103 : Blo 1462551 1647103 := bstep (se 1 (by rfl) ⟨1235327, by rfl⟩ : syracuseStep 1647103 = 2470655) B2470655
theorem B17794025 : Blo 1462551 17794025 := bstep (se 2 (by rfl) ⟨6672759, by rfl⟩ : syracuseStep 17794025 = 13345519) B13345519
theorem B16672229 : Blo 1462551 16672229 := bstep (se 4 (by rfl) ⟨1563021, by rfl⟩ : syracuseStep 16672229 = 3126043) B3126043
theorem B7407287 : Blo 1462551 7407287 := bstep (se 1 (by rfl) ⟨5555465, by rfl⟩ : syracuseStep 7407287 = 11110931) B11110931
theorem B2468711 : Blo 1462551 2468711 := bstep (se 1 (by rfl) ⟨1851533, by rfl⟩ : syracuseStep 2468711 = 3703067) B3703067
theorem B18754415 : Blo 1462551 18754415 := bstep (se 1 (by rfl) ⟨14065811, by rfl⟩ : syracuseStep 18754415 = 28131623) B28131623
theorem B9382823 : Blo 1462551 9382823 := bstep (se 1 (by rfl) ⟨7037117, by rfl⟩ : syracuseStep 9382823 = 14074235) B14074235
theorem B3705851 : Blo 1462551 3705851 := bstep (se 1 (by rfl) ⟨2779388, by rfl⟩ : syracuseStep 3705851 = 5558777) B5558777
theorem B3518183 : Blo 1462551 3518183 := bstep (se 1 (by rfl) ⟨2638637, by rfl⟩ : syracuseStep 3518183 = 5277275) B5277275
theorem B9376489 : Blo 1462551 9376489 := bstep (se 2 (by rfl) ⟨3516183, by rfl⟩ : syracuseStep 9376489 = 7032367) B7032367
theorem B16667855 : Blo 1462551 16667855 := bstep (se 1 (by rfl) ⟨12500891, by rfl⟩ : syracuseStep 16667855 = 25001783) B25001783
theorem B6247849 : Blo 1462551 6247849 := bstep (se 2 (by rfl) ⟨2342943, by rfl⟩ : syracuseStep 6247849 = 4685887) B4685887
theorem B3127547 : Blo 1462551 3127547 := bstep (se 1 (by rfl) ⟨2345660, by rfl⟩ : syracuseStep 3127547 = 4691321) B4691321
theorem B11115305 : Blo 1462551 11115305 := bstep (se 2 (by rfl) ⟨4168239, by rfl⟩ : syracuseStep 11115305 = 8336479) B8336479
theorem B4169015 : Blo 1462551 4169015 := bstep (se 1 (by rfl) ⟨3126761, by rfl⟩ : syracuseStep 4169015 = 6253523) B6253523
theorem B8330921 : Blo 1462551 8330921 := bstep (se 2 (by rfl) ⟨3124095, by rfl⟩ : syracuseStep 8330921 = 6248191) B6248191
theorem B2195195 : Blo 1462551 2195195 := bstep (se 1 (by rfl) ⟨1646396, by rfl⟩ : syracuseStep 2195195 = 3292793) B3292793
theorem B3293459 : Blo 1462551 3293459 := bstep (se 1 (by rfl) ⟨2470094, by rfl⟩ : syracuseStep 3293459 = 4940189) B4940189
theorem B11862683 : Blo 1462551 11862683 := bstep (se 1 (by rfl) ⟨8897012, by rfl⟩ : syracuseStep 11862683 = 17794025) B17794025
theorem B2196137 : Blo 1462551 2196137 := bstep (se 2 (by rfl) ⟨823551, by rfl⟩ : syracuseStep 2196137 = 1647103) B1647103
theorem B12501985 : Blo 1462551 12501985 := bstep (se 2 (by rfl) ⟨4688244, by rfl⟩ : syracuseStep 12501985 = 9376489) B9376489
theorem B12502943 : Blo 1462551 12502943 := bstep (se 1 (by rfl) ⟨9377207, by rfl⟩ : syracuseStep 12502943 = 18754415) B18754415
theorem B2779343 : Blo 1462551 2779343 := bstep (se 1 (by rfl) ⟨2084507, by rfl⟩ : syracuseStep 2779343 = 4169015) B4169015
theorem B2345455 : Blo 1462551 2345455 := bstep (se 1 (by rfl) ⟨1759091, by rfl⟩ : syracuseStep 2345455 = 3518183) B3518183
theorem B11111903 : Blo 1462551 11111903 := bstep (se 1 (by rfl) ⟨8333927, by rfl⟩ : syracuseStep 11111903 = 16667855) B16667855
theorem B2085031 : Blo 1462551 2085031 := bstep (se 1 (by rfl) ⟨1563773, by rfl⟩ : syracuseStep 2085031 = 3127547) B3127547
theorem B7410203 : Blo 1462551 7410203 := bstep (se 1 (by rfl) ⟨5557652, by rfl⟩ : syracuseStep 7410203 = 11115305) B11115305
theorem B6255215 : Blo 1462551 6255215 := bstep (se 1 (by rfl) ⟨4691411, by rfl⟩ : syracuseStep 6255215 = 9382823) B9382823
theorem B2470567 : Blo 1462551 2470567 := bstep (se 1 (by rfl) ⟨1852925, by rfl⟩ : syracuseStep 2470567 = 3705851) B3705851
theorem B1463463 : Blo 1462551 1463463 := bstep (se 1 (by rfl) ⟨1097597, by rfl⟩ : syracuseStep 1463463 = 2195195) B2195195
theorem B11114819 : Blo 1462551 11114819 := bstep (se 1 (by rfl) ⟨8336114, by rfl⟩ : syracuseStep 11114819 = 16672229) B16672229
theorem B4938191 : Blo 1462551 4938191 := bstep (se 1 (by rfl) ⟨3703643, by rfl⟩ : syracuseStep 4938191 = 7407287) B7407287
theorem B8330465 : Blo 1462551 8330465 := bstep (se 2 (by rfl) ⟨3123924, by rfl⟩ : syracuseStep 8330465 = 6247849) B6247849
theorem B1645807 : Blo 1462551 1645807 := bstep (se 1 (by rfl) ⟨1234355, by rfl⟩ : syracuseStep 1645807 = 2468711) B2468711
theorem B5553947 : Blo 1462551 5553947 := bstep (se 1 (by rfl) ⟨4165460, by rfl⟩ : syracuseStep 5553947 = 8330921) B8330921
theorem B2195639 : Blo 1462551 2195639 := bstep (se 1 (by rfl) ⟨1646729, by rfl⟩ : syracuseStep 2195639 = 3293459) B3293459
theorem B4940135 : Blo 1462551 4940135 := bstep (se 1 (by rfl) ⟨3705101, by rfl⟩ : syracuseStep 4940135 = 7410203) B7410203
theorem B4170143 : Blo 1462551 4170143 := bstep (se 1 (by rfl) ⟨3127607, by rfl⟩ : syracuseStep 4170143 = 6255215) B6255215
theorem B3294089 : Blo 1462551 3294089 := bstep (se 2 (by rfl) ⟨1235283, by rfl⟩ : syracuseStep 3294089 = 2470567) B2470567
theorem B1852895 : Blo 1462551 1852895 := bstep (se 1 (by rfl) ⟨1389671, by rfl⟩ : syracuseStep 1852895 = 2779343) B2779343
theorem B7407935 : Blo 1462551 7407935 := bstep (se 1 (by rfl) ⟨5555951, by rfl⟩ : syracuseStep 7407935 = 11111903) B11111903
theorem B7908455 : Blo 1462551 7908455 := bstep (se 1 (by rfl) ⟨5931341, by rfl⟩ : syracuseStep 7908455 = 11862683) B11862683
theorem B11120165 : Blo 1462551 11120165 := bstep (se 4 (by rfl) ⟨1042515, by rfl⟩ : syracuseStep 11120165 = 2085031) B2085031
theorem B8335295 : Blo 1462551 8335295 := bstep (se 1 (by rfl) ⟨6251471, by rfl⟩ : syracuseStep 8335295 = 12502943) B12502943
theorem B7409879 : Blo 1462551 7409879 := bstep (se 1 (by rfl) ⟨5557409, by rfl⟩ : syracuseStep 7409879 = 11114819) B11114819
theorem B1464091 : Blo 1462551 1464091 := bstep (se 1 (by rfl) ⟨1098068, by rfl⟩ : syracuseStep 1464091 = 2196137) B2196137
theorem B16669313 : Blo 1462551 16669313 := bstep (se 2 (by rfl) ⟨6250992, by rfl⟩ : syracuseStep 16669313 = 12501985) B12501985
theorem B3292127 : Blo 1462551 3292127 := bstep (se 1 (by rfl) ⟨2469095, by rfl⟩ : syracuseStep 3292127 = 4938191) B4938191
theorem B2194409 : Blo 1462551 2194409 := bstep (se 2 (by rfl) ⟨822903, by rfl⟩ : syracuseStep 2194409 = 1645807) B1645807
theorem B5553643 : Blo 1462551 5553643 := bstep (se 1 (by rfl) ⟨4165232, by rfl⟩ : syracuseStep 5553643 = 8330465) B8330465
theorem B3702631 : Blo 1462551 3702631 := bstep (se 1 (by rfl) ⟨2776973, by rfl⟩ : syracuseStep 3702631 = 5553947) B5553947
theorem B12509093 : Blo 1462551 12509093 := bstep (se 4 (by rfl) ⟨1172727, by rfl⟩ : syracuseStep 12509093 = 2345455) B2345455
theorem B4939919 : Blo 1462551 4939919 := bstep (se 1 (by rfl) ⟨3704939, by rfl⟩ : syracuseStep 4939919 = 7409879) B7409879
theorem B3293423 : Blo 1462551 3293423 := bstep (se 1 (by rfl) ⟨2470067, by rfl⟩ : syracuseStep 3293423 = 4940135) B4940135
theorem B2196059 : Blo 1462551 2196059 := bstep (se 1 (by rfl) ⟨1647044, by rfl⟩ : syracuseStep 2196059 = 3294089) B3294089
theorem B4941053 : Blo 1462551 4941053 := bstep (se 3 (by rfl) ⟨926447, by rfl⟩ : syracuseStep 4941053 = 1852895) B1852895
theorem B5556863 : Blo 1462551 5556863 := bstep (se 1 (by rfl) ⟨4167647, by rfl⟩ : syracuseStep 5556863 = 8335295) B8335295
theorem B2780095 : Blo 1462551 2780095 := bstep (se 1 (by rfl) ⟨2085071, by rfl⟩ : syracuseStep 2780095 = 4170143) B4170143
theorem B11112875 : Blo 1462551 11112875 := bstep (se 1 (by rfl) ⟨8334656, by rfl⟩ : syracuseStep 11112875 = 16669313) B16669313
theorem B1462939 : Blo 1462551 1462939 := bstep (se 1 (by rfl) ⟨1097204, by rfl⟩ : syracuseStep 1462939 = 2194409) B2194409
theorem B5272303 : Blo 1462551 5272303 := bstep (se 1 (by rfl) ⟨3954227, by rfl⟩ : syracuseStep 5272303 = 7908455) B7908455
theorem B4936841 : Blo 1462551 4936841 := bstep (se 2 (by rfl) ⟨1851315, by rfl⟩ : syracuseStep 4936841 = 3702631) B3702631
theorem B1463759 : Blo 1462551 1463759 := bstep (se 1 (by rfl) ⟨1097819, by rfl⟩ : syracuseStep 1463759 = 2195639) B2195639
theorem B4938623 : Blo 1462551 4938623 := bstep (se 1 (by rfl) ⟨3703967, by rfl⟩ : syracuseStep 4938623 = 7407935) B7407935
theorem B7404857 : Blo 1462551 7404857 := bstep (se 2 (by rfl) ⟨2776821, by rfl⟩ : syracuseStep 7404857 = 5553643) B5553643
theorem B2194751 : Blo 1462551 2194751 := bstep (se 1 (by rfl) ⟨1646063, by rfl⟩ : syracuseStep 2194751 = 3292127) B3292127
theorem B7413443 : Blo 1462551 7413443 := bstep (se 1 (by rfl) ⟨5560082, by rfl⟩ : syracuseStep 7413443 = 11120165) B11120165
theorem B8339395 : Blo 1462551 8339395 := bstep (se 1 (by rfl) ⟨6254546, by rfl⟩ : syracuseStep 8339395 = 12509093) B12509093
theorem B3293279 : Blo 1462551 3293279 := bstep (se 1 (by rfl) ⟨2469959, by rfl⟩ : syracuseStep 3293279 = 4939919) B4939919
theorem B2195615 : Blo 1462551 2195615 := bstep (se 1 (by rfl) ⟨1646711, by rfl⟩ : syracuseStep 2195615 = 3293423) B3293423
theorem B3294035 : Blo 1462551 3294035 := bstep (se 1 (by rfl) ⟨2470526, by rfl⟩ : syracuseStep 3294035 = 4941053) B4941053
theorem B7029737 : Blo 1462551 7029737 := bstep (se 2 (by rfl) ⟨2636151, by rfl⟩ : syracuseStep 7029737 = 5272303) B5272303
theorem B3704575 : Blo 1462551 3704575 := bstep (se 1 (by rfl) ⟨2778431, by rfl⟩ : syracuseStep 3704575 = 5556863) B5556863
theorem B4942295 : Blo 1462551 4942295 := bstep (se 1 (by rfl) ⟨3706721, by rfl⟩ : syracuseStep 4942295 = 7413443) B7413443
theorem B11119193 : Blo 1462551 11119193 := bstep (se 2 (by rfl) ⟨4169697, by rfl⟩ : syracuseStep 11119193 = 8339395) B8339395
theorem B7408583 : Blo 1462551 7408583 := bstep (se 1 (by rfl) ⟨5556437, by rfl⟩ : syracuseStep 7408583 = 11112875) B11112875
theorem B3706793 : Blo 1462551 3706793 := bstep (se 2 (by rfl) ⟨1390047, by rfl⟩ : syracuseStep 3706793 = 2780095) B2780095
theorem B4936571 : Blo 1462551 4936571 := bstep (se 1 (by rfl) ⟨3702428, by rfl⟩ : syracuseStep 4936571 = 7404857) B7404857
theorem B1463167 : Blo 1462551 1463167 := bstep (se 1 (by rfl) ⟨1097375, by rfl⟩ : syracuseStep 1463167 = 2194751) B2194751
theorem B1464039 : Blo 1462551 1464039 := bstep (se 1 (by rfl) ⟨1098029, by rfl⟩ : syracuseStep 1464039 = 2196059) B2196059
theorem B3291227 : Blo 1462551 3291227 := bstep (se 1 (by rfl) ⟨2468420, by rfl⟩ : syracuseStep 3291227 = 4936841) B4936841
theorem B3292415 : Blo 1462551 3292415 := bstep (se 1 (by rfl) ⟨2469311, by rfl⟩ : syracuseStep 3292415 = 4938623) B4938623
theorem B2195519 : Blo 1462551 2195519 := bstep (se 1 (by rfl) ⟨1646639, by rfl⟩ : syracuseStep 2195519 = 3293279) B3293279
theorem B2196023 : Blo 1462551 2196023 := bstep (se 1 (by rfl) ⟨1647017, by rfl⟩ : syracuseStep 2196023 = 3294035) B3294035
theorem B4686491 : Blo 1462551 4686491 := bstep (se 1 (by rfl) ⟨3514868, by rfl⟩ : syracuseStep 4686491 = 7029737) B7029737
theorem B3294863 : Blo 1462551 3294863 := bstep (se 1 (by rfl) ⟨2471147, by rfl⟩ : syracuseStep 3294863 = 4942295) B4942295
theorem B2471195 : Blo 1462551 2471195 := bstep (se 1 (by rfl) ⟨1853396, by rfl⟩ : syracuseStep 2471195 = 3706793) B3706793
theorem B1463743 : Blo 1462551 1463743 := bstep (se 1 (by rfl) ⟨1097807, by rfl⟩ : syracuseStep 1463743 = 2195615) B2195615
theorem B3291047 : Blo 1462551 3291047 := bstep (se 1 (by rfl) ⟨2468285, by rfl⟩ : syracuseStep 3291047 = 4936571) B4936571
theorem B2194151 : Blo 1462551 2194151 := bstep (se 1 (by rfl) ⟨1645613, by rfl⟩ : syracuseStep 2194151 = 3291227) B3291227
theorem B7412795 : Blo 1462551 7412795 := bstep (se 1 (by rfl) ⟨5559596, by rfl⟩ : syracuseStep 7412795 = 11119193) B11119193
theorem B4939055 : Blo 1462551 4939055 := bstep (se 1 (by rfl) ⟨3704291, by rfl⟩ : syracuseStep 4939055 = 7408583) B7408583
theorem B2194943 : Blo 1462551 2194943 := bstep (se 1 (by rfl) ⟨1646207, by rfl⟩ : syracuseStep 2194943 = 3292415) B3292415
theorem B4939433 : Blo 1462551 4939433 := bstep (se 2 (by rfl) ⟨1852287, by rfl⟩ : syracuseStep 4939433 = 3704575) B3704575
theorem B1647463 : Blo 1462551 1647463 := bstep (se 1 (by rfl) ⟨1235597, by rfl⟩ : syracuseStep 1647463 = 2471195) B2471195
theorem B2196575 : Blo 1462551 2196575 := bstep (se 1 (by rfl) ⟨1647431, by rfl⟩ : syracuseStep 2196575 = 3294863) B3294863
theorem B4941863 : Blo 1462551 4941863 := bstep (se 1 (by rfl) ⟨3706397, by rfl⟩ : syracuseStep 4941863 = 7412795) B7412795
theorem B3124327 : Blo 1462551 3124327 := bstep (se 1 (by rfl) ⟨2343245, by rfl⟩ : syracuseStep 3124327 = 4686491) B4686491
theorem B1462767 : Blo 1462551 1462767 := bstep (se 1 (by rfl) ⟨1097075, by rfl⟩ : syracuseStep 1462767 = 2194151) B2194151
theorem B1463295 : Blo 1462551 1463295 := bstep (se 1 (by rfl) ⟨1097471, by rfl⟩ : syracuseStep 1463295 = 2194943) B2194943
theorem B1463679 : Blo 1462551 1463679 := bstep (se 1 (by rfl) ⟨1097759, by rfl⟩ : syracuseStep 1463679 = 2195519) B2195519
theorem B1464015 : Blo 1462551 1464015 := bstep (se 1 (by rfl) ⟨1098011, by rfl⟩ : syracuseStep 1464015 = 2196023) B2196023
theorem B2194031 : Blo 1462551 2194031 := bstep (se 1 (by rfl) ⟨1645523, by rfl⟩ : syracuseStep 2194031 = 3291047) B3291047
theorem B3292703 : Blo 1462551 3292703 := bstep (se 1 (by rfl) ⟨2469527, by rfl⟩ : syracuseStep 3292703 = 4939055) B4939055
theorem B3292955 : Blo 1462551 3292955 := bstep (se 1 (by rfl) ⟨2469716, by rfl⟩ : syracuseStep 3292955 = 4939433) B4939433
theorem B2196617 : Blo 1462551 2196617 := bstep (se 2 (by rfl) ⟨823731, by rfl⟩ : syracuseStep 2196617 = 1647463) B1647463
theorem B3294575 : Blo 1462551 3294575 := bstep (se 1 (by rfl) ⟨2470931, by rfl⟩ : syracuseStep 3294575 = 4941863) B4941863
theorem B4165769 : Blo 1462551 4165769 := bstep (se 2 (by rfl) ⟨1562163, by rfl⟩ : syracuseStep 4165769 = 3124327) B3124327
theorem B1462687 : Blo 1462551 1462687 := bstep (se 1 (by rfl) ⟨1097015, by rfl⟩ : syracuseStep 1462687 = 2194031) B2194031
theorem B1464383 : Blo 1462551 1464383 := bstep (se 1 (by rfl) ⟨1098287, by rfl⟩ : syracuseStep 1464383 = 2196575) B2196575
theorem B2195135 : Blo 1462551 2195135 := bstep (se 1 (by rfl) ⟨1646351, by rfl⟩ : syracuseStep 2195135 = 3292703) B3292703
theorem B2195303 : Blo 1462551 2195303 := bstep (se 1 (by rfl) ⟨1646477, by rfl⟩ : syracuseStep 2195303 = 3292955) B3292955
theorem B2777179 : Blo 1462551 2777179 := bstep (se 1 (by rfl) ⟨2082884, by rfl⟩ : syracuseStep 2777179 = 4165769) B4165769
theorem B2196383 : Blo 1462551 2196383 := bstep (se 1 (by rfl) ⟨1647287, by rfl⟩ : syracuseStep 2196383 = 3294575) B3294575
theorem B1463423 : Blo 1462551 1463423 := bstep (se 1 (by rfl) ⟨1097567, by rfl⟩ : syracuseStep 1463423 = 2195135) B2195135
theorem B1463535 : Blo 1462551 1463535 := bstep (se 1 (by rfl) ⟨1097651, by rfl⟩ : syracuseStep 1463535 = 2195303) B2195303
theorem B1464411 : Blo 1462551 1464411 := bstep (se 1 (by rfl) ⟨1098308, by rfl⟩ : syracuseStep 1464411 = 2196617) B2196617
theorem B3702905 : Blo 1462551 3702905 := bstep (se 2 (by rfl) ⟨1388589, by rfl⟩ : syracuseStep 3702905 = 2777179) B2777179
theorem B1464255 : Blo 1462551 1464255 := bstep (se 1 (by rfl) ⟨1098191, by rfl⟩ : syracuseStep 1464255 = 2196383) B2196383
theorem B2468603 : Blo 1462551 2468603 := bstep (se 1 (by rfl) ⟨1851452, by rfl⟩ : syracuseStep 2468603 = 3702905) B3702905
theorem B1645735 : Blo 1462551 1645735 := bstep (se 1 (by rfl) ⟨1234301, by rfl⟩ : syracuseStep 1645735 = 2468603) B2468603
theorem B2194313 : Blo 1462551 2194313 := bstep (se 2 (by rfl) ⟨822867, by rfl⟩ : syracuseStep 2194313 = 1645735) B1645735
theorem B1462875 : Blo 1462551 1462875 := bstep (se 1 (by rfl) ⟨1097156, by rfl⟩ : syracuseStep 1462875 = 2194313) B2194313

theorem C0 (j : ℕ) (h1 : 365637 ≤ j) (h2 : j ≤ 366137) : Blo 1462551 (4 * j + 3) := by
  interval_cases j
  · exact B1462551
  · exact B1462555
  · exact B1462559
  · exact B1462563
  · exact B1462567
  · exact B1462571
  · exact B1462575
  · exact B1462579
  · exact B1462583
  · exact B1462587
  · exact B1462591
  · exact B1462595
  · exact B1462599
  · exact B1462603
  · exact B1462607
  · exact B1462611
  · exact B1462615
  · exact B1462619
  · exact B1462623
  · exact B1462627
  · exact B1462631
  · exact B1462635
  · exact B1462639
  · exact B1462643
  · exact B1462647
  · exact B1462651
  · exact B1462655
  · exact B1462659
  · exact B1462663
  · exact B1462667
  · exact B1462671
  · exact B1462675
  · exact B1462679
  · exact B1462683
  · exact B1462687
  · exact B1462691
  · exact B1462695
  · exact B1462699
  · exact B1462703
  · exact B1462707
  · exact B1462711
  · exact B1462715
  · exact B1462719
  · exact B1462723
  · exact B1462727
  · exact B1462731
  · exact B1462735
  · exact B1462739
  · exact B1462743
  · exact B1462747
  · exact B1462751
  · exact B1462755
  · exact B1462759
  · exact B1462763
  · exact B1462767
  · exact B1462771
  · exact B1462775
  · exact B1462779
  · exact B1462783
  · exact B1462787
  · exact B1462791
  · exact B1462795
  · exact B1462799
  · exact B1462803
  · exact B1462807
  · exact B1462811
  · exact B1462815
  · exact B1462819
  · exact B1462823
  · exact B1462827
  · exact B1462831
  · exact B1462835
  · exact B1462839
  · exact B1462843
  · exact B1462847
  · exact B1462851
  · exact B1462855
  · exact B1462859
  · exact B1462863
  · exact B1462867
  · exact B1462871
  · exact B1462875
  · exact B1462879
  · exact B1462883
  · exact B1462887
  · exact B1462891
  · exact B1462895
  · exact B1462899
  · exact B1462903
  · exact B1462907
  · exact B1462911
  · exact B1462915
  · exact B1462919
  · exact B1462923
  · exact B1462927
  · exact B1462931
  · exact B1462935
  · exact B1462939
  · exact B1462943
  · exact B1462947
  · exact B1462951
  · exact B1462955
  · exact B1462959
  · exact B1462963
  · exact B1462967
  · exact B1462971
  · exact B1462975
  · exact B1462979
  · exact B1462983
  · exact B1462987
  · exact B1462991
  · exact B1462995
  · exact B1462999
  · exact B1463003
  · exact B1463007
  · exact B1463011
  · exact B1463015
  · exact B1463019
  · exact B1463023
  · exact B1463027
  · exact B1463031
  · exact B1463035
  · exact B1463039
  · exact B1463043
  · exact B1463047
  · exact B1463051
  · exact B1463055
  · exact B1463059
  · exact B1463063
  · exact B1463067
  · exact B1463071
  · exact B1463075
  · exact B1463079
  · exact B1463083
  · exact B1463087
  · exact B1463091
  · exact B1463095
  · exact B1463099
  · exact B1463103
  · exact B1463107
  · exact B1463111
  · exact B1463115
  · exact B1463119
  · exact B1463123
  · exact B1463127
  · exact B1463131
  · exact B1463135
  · exact B1463139
  · exact B1463143
  · exact B1463147
  · exact B1463151
  · exact B1463155
  · exact B1463159
  · exact B1463163
  · exact B1463167
  · exact B1463171
  · exact B1463175
  · exact B1463179
  · exact B1463183
  · exact B1463187
  · exact B1463191
  · exact B1463195
  · exact B1463199
  · exact B1463203
  · exact B1463207
  · exact B1463211
  · exact B1463215
  · exact B1463219
  · exact B1463223
  · exact B1463227
  · exact B1463231
  · exact B1463235
  · exact B1463239
  · exact B1463243
  · exact B1463247
  · exact B1463251
  · exact B1463255
  · exact B1463259
  · exact B1463263
  · exact B1463267
  · exact B1463271
  · exact B1463275
  · exact B1463279
  · exact B1463283
  · exact B1463287
  · exact B1463291
  · exact B1463295
  · exact B1463299
  · exact B1463303
  · exact B1463307
  · exact B1463311
  · exact B1463315
  · exact B1463319
  · exact B1463323
  · exact B1463327
  · exact B1463331
  · exact B1463335
  · exact B1463339
  · exact B1463343
  · exact B1463347
  · exact B1463351
  · exact B1463355
  · exact B1463359
  · exact B1463363
  · exact B1463367
  · exact B1463371
  · exact B1463375
  · exact B1463379
  · exact B1463383
  · exact B1463387
  · exact B1463391
  · exact B1463395
  · exact B1463399
  · exact B1463403
  · exact B1463407
  · exact B1463411
  · exact B1463415
  · exact B1463419
  · exact B1463423
  · exact B1463427
  · exact B1463431
  · exact B1463435
  · exact B1463439
  · exact B1463443
  · exact B1463447
  · exact B1463451
  · exact B1463455
  · exact B1463459
  · exact B1463463
  · exact B1463467
  · exact B1463471
  · exact B1463475
  · exact B1463479
  · exact B1463483
  · exact B1463487
  · exact B1463491
  · exact B1463495
  · exact B1463499
  · exact B1463503
  · exact B1463507
  · exact B1463511
  · exact B1463515
  · exact B1463519
  · exact B1463523
  · exact B1463527
  · exact B1463531
  · exact B1463535
  · exact B1463539
  · exact B1463543
  · exact B1463547
  · exact B1463551
  · exact B1463555
  · exact B1463559
  · exact B1463563
  · exact B1463567
  · exact B1463571
  · exact B1463575
  · exact B1463579
  · exact B1463583
  · exact B1463587
  · exact B1463591
  · exact B1463595
  · exact B1463599
  · exact B1463603
  · exact B1463607
  · exact B1463611
  · exact B1463615
  · exact B1463619
  · exact B1463623
  · exact B1463627
  · exact B1463631
  · exact B1463635
  · exact B1463639
  · exact B1463643
  · exact B1463647
  · exact B1463651
  · exact B1463655
  · exact B1463659
  · exact B1463663
  · exact B1463667
  · exact B1463671
  · exact B1463675
  · exact B1463679
  · exact B1463683
  · exact B1463687
  · exact B1463691
  · exact B1463695
  · exact B1463699
  · exact B1463703
  · exact B1463707
  · exact B1463711
  · exact B1463715
  · exact B1463719
  · exact B1463723
  · exact B1463727
  · exact B1463731
  · exact B1463735
  · exact B1463739
  · exact B1463743
  · exact B1463747
  · exact B1463751
  · exact B1463755
  · exact B1463759
  · exact B1463763
  · exact B1463767
  · exact B1463771
  · exact B1463775
  · exact B1463779
  · exact B1463783
  · exact B1463787
  · exact B1463791
  · exact B1463795
  · exact B1463799
  · exact B1463803
  · exact B1463807
  · exact B1463811
  · exact B1463815
  · exact B1463819
  · exact B1463823
  · exact B1463827
  · exact B1463831
  · exact B1463835
  · exact B1463839
  · exact B1463843
  · exact B1463847
  · exact B1463851
  · exact B1463855
  · exact B1463859
  · exact B1463863
  · exact B1463867
  · exact B1463871
  · exact B1463875
  · exact B1463879
  · exact B1463883
  · exact B1463887
  · exact B1463891
  · exact B1463895
  · exact B1463899
  · exact B1463903
  · exact B1463907
  · exact B1463911
  · exact B1463915
  · exact B1463919
  · exact B1463923
  · exact B1463927
  · exact B1463931
  · exact B1463935
  · exact B1463939
  · exact B1463943
  · exact B1463947
  · exact B1463951
  · exact B1463955
  · exact B1463959
  · exact B1463963
  · exact B1463967
  · exact B1463971
  · exact B1463975
  · exact B1463979
  · exact B1463983
  · exact B1463987
  · exact B1463991
  · exact B1463995
  · exact B1463999
  · exact B1464003
  · exact B1464007
  · exact B1464011
  · exact B1464015
  · exact B1464019
  · exact B1464023
  · exact B1464027
  · exact B1464031
  · exact B1464035
  · exact B1464039
  · exact B1464043
  · exact B1464047
  · exact B1464051
  · exact B1464055
  · exact B1464059
  · exact B1464063
  · exact B1464067
  · exact B1464071
  · exact B1464075
  · exact B1464079
  · exact B1464083
  · exact B1464087
  · exact B1464091
  · exact B1464095
  · exact B1464099
  · exact B1464103
  · exact B1464107
  · exact B1464111
  · exact B1464115
  · exact B1464119
  · exact B1464123
  · exact B1464127
  · exact B1464131
  · exact B1464135
  · exact B1464139
  · exact B1464143
  · exact B1464147
  · exact B1464151
  · exact B1464155
  · exact B1464159
  · exact B1464163
  · exact B1464167
  · exact B1464171
  · exact B1464175
  · exact B1464179
  · exact B1464183
  · exact B1464187
  · exact B1464191
  · exact B1464195
  · exact B1464199
  · exact B1464203
  · exact B1464207
  · exact B1464211
  · exact B1464215
  · exact B1464219
  · exact B1464223
  · exact B1464227
  · exact B1464231
  · exact B1464235
  · exact B1464239
  · exact B1464243
  · exact B1464247
  · exact B1464251
  · exact B1464255
  · exact B1464259
  · exact B1464263
  · exact B1464267
  · exact B1464271
  · exact B1464275
  · exact B1464279
  · exact B1464283
  · exact B1464287
  · exact B1464291
  · exact B1464295
  · exact B1464299
  · exact B1464303
  · exact B1464307
  · exact B1464311
  · exact B1464315
  · exact B1464319
  · exact B1464323
  · exact B1464327
  · exact B1464331
  · exact B1464335
  · exact B1464339
  · exact B1464343
  · exact B1464347
  · exact B1464351
  · exact B1464355
  · exact B1464359
  · exact B1464363
  · exact B1464367
  · exact B1464371
  · exact B1464375
  · exact B1464379
  · exact B1464383
  · exact B1464387
  · exact B1464391
  · exact B1464395
  · exact B1464399
  · exact B1464403
  · exact B1464407
  · exact B1464411
  · exact B1464415
  · exact B1464419
  · exact B1464423
  · exact B1464427
  · exact B1464431
  · exact B1464435
  · exact B1464439
  · exact B1464443
  · exact B1464447
  · exact B1464451
  · exact B1464455
  · exact B1464459
  · exact B1464463
  · exact B1464467
  · exact B1464471
  · exact B1464475
  · exact B1464479
  · exact B1464483
  · exact B1464487
  · exact B1464491
  · exact B1464495
  · exact B1464499
  · exact B1464503
  · exact B1464507
  · exact B1464511
  · exact B1464515
  · exact B1464519
  · exact B1464523
  · exact B1464527
  · exact B1464531
  · exact B1464535
  · exact B1464539
  · exact B1464543
  · exact B1464547
  · exact B1464551

theorem solution (m : ℕ) (hlo : 1462551 ≤ m) (hhi : m ≤ 1464551) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 365637 ≤ j := by omega
    have hj2 : j ≤ 366137 := by omega
    have hb : Blo 1462551 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
