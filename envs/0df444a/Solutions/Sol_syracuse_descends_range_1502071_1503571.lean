-- Prove2me | solution 1 for syracuse_descends_range_1502071_1503571
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:48:03.978511+00:00
-- url     : https://prove2.me/submissions/bedcbfd4-43b5-46fa-b654-3b216b047060

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


theorem B5070869 : Blo 1502071 5070869 := bbase (se 6 (by rfl) ⟨118848, by rfl⟩ : syracuseStep 5070869 = 237697) (by norm_num)
theorem B2891837 : Blo 1502071 2891837 := bbase (se 3 (by rfl) ⟨542219, by rfl⟩ : syracuseStep 2891837 = 1084439) (by norm_num)
theorem B2744389 : Blo 1502071 2744389 := bbase (se 4 (by rfl) ⟨257286, by rfl⟩ : syracuseStep 2744389 = 514573) (by norm_num)
theorem B3047581 : Blo 1502071 3047581 := bbase (se 3 (by rfl) ⟨571421, by rfl⟩ : syracuseStep 3047581 = 1142843) (by norm_num)
theorem B7610597 : Blo 1502071 7610597 := bbase (se 4 (by rfl) ⟨713493, by rfl⟩ : syracuseStep 7610597 = 1426987) (by norm_num)
theorem B2007349 : Blo 1502071 2007349 := bbase (se 5 (by rfl) ⟨94094, by rfl⟩ : syracuseStep 2007349 = 188189) (by norm_num)
theorem B11411765 : Blo 1502071 11411765 := bbase (se 5 (by rfl) ⟨534926, by rfl⟩ : syracuseStep 11411765 = 1069853) (by norm_num)
theorem B2253125 : Blo 1502071 2253125 := bbase (se 4 (by rfl) ⟨211230, by rfl⟩ : syracuseStep 2253125 = 422461) (by norm_num)
theorem B2253149 : Blo 1502071 2253149 := bbase (se 3 (by rfl) ⟨422465, by rfl⟩ : syracuseStep 2253149 = 844931) (by norm_num)
theorem B2253173 : Blo 1502071 2253173 := bbase (se 5 (by rfl) ⟨105617, by rfl⟩ : syracuseStep 2253173 = 211235) (by norm_num)
theorem B2253197 : Blo 1502071 2253197 := bbase (se 3 (by rfl) ⟨422474, by rfl⟩ : syracuseStep 2253197 = 844949) (by norm_num)
theorem B2253221 : Blo 1502071 2253221 := bbase (se 4 (by rfl) ⟨211239, by rfl⟩ : syracuseStep 2253221 = 422479) (by norm_num)
theorem B2892205 : Blo 1502071 2892205 := bbase (se 3 (by rfl) ⟨542288, by rfl⟩ : syracuseStep 2892205 = 1084577) (by norm_num)
theorem B2253245 : Blo 1502071 2253245 := bbase (se 3 (by rfl) ⟨422483, by rfl⟩ : syracuseStep 2253245 = 844967) (by norm_num)
theorem B5489093 : Blo 1502071 5489093 := bbase (se 4 (by rfl) ⟨514602, by rfl⟩ : syracuseStep 5489093 = 1029205) (by norm_num)
theorem B5071301 : Blo 1502071 5071301 := bbase (se 4 (by rfl) ⟨475434, by rfl⟩ : syracuseStep 5071301 = 950869) (by norm_num)
theorem B2253269 : Blo 1502071 2253269 := bbase (se 7 (by rfl) ⟨26405, by rfl⟩ : syracuseStep 2253269 = 52811) (by norm_num)
theorem B2253293 : Blo 1502071 2253293 := bbase (se 3 (by rfl) ⟨422492, by rfl⟩ : syracuseStep 2253293 = 844985) (by norm_num)
theorem B2253317 : Blo 1502071 2253317 := bbase (se 4 (by rfl) ⟨211248, by rfl⟩ : syracuseStep 2253317 = 422497) (by norm_num)
theorem B1901065 : Blo 1502071 1901065 := bbase (se 2 (by rfl) ⟨712899, by rfl⟩ : syracuseStep 1901065 = 1425799) (by norm_num)
theorem B4063765 : Blo 1502071 4063765 := bbase (se 6 (by rfl) ⟨95244, by rfl⟩ : syracuseStep 4063765 = 190489) (by norm_num)
theorem B2253341 : Blo 1502071 2253341 := bbase (se 3 (by rfl) ⟨422501, by rfl⟩ : syracuseStep 2253341 = 845003) (by norm_num)
theorem B2253365 : Blo 1502071 2253365 := bbase (se 5 (by rfl) ⟨105626, by rfl⟩ : syracuseStep 2253365 = 211253) (by norm_num)
theorem B2253389 : Blo 1502071 2253389 := bbase (se 3 (by rfl) ⟨422510, by rfl⟩ : syracuseStep 2253389 = 845021) (by norm_num)
theorem B2253413 : Blo 1502071 2253413 := bbase (se 4 (by rfl) ⟨211257, by rfl⟩ : syracuseStep 2253413 = 422515) (by norm_num)
theorem B1901161 : Blo 1502071 1901161 := bbase (se 2 (by rfl) ⟨712935, by rfl⟩ : syracuseStep 1901161 = 1425871) (by norm_num)
theorem B2253437 : Blo 1502071 2253437 := bbase (se 3 (by rfl) ⟨422519, by rfl⟩ : syracuseStep 2253437 = 845039) (by norm_num)
theorem B2253461 : Blo 1502071 2253461 := bbase (se 6 (by rfl) ⟨52815, by rfl⟩ : syracuseStep 2253461 = 105631) (by norm_num)
theorem B3048101 : Blo 1502071 3048101 := bbase (se 4 (by rfl) ⟨285759, by rfl⟩ : syracuseStep 3048101 = 571519) (by norm_num)
theorem B2253485 : Blo 1502071 2253485 := bbase (se 3 (by rfl) ⟨422528, by rfl⟩ : syracuseStep 2253485 = 845057) (by norm_num)
theorem B2253509 : Blo 1502071 2253509 := bbase (se 4 (by rfl) ⟨211266, by rfl⟩ : syracuseStep 2253509 = 422533) (by norm_num)
theorem B2253533 : Blo 1502071 2253533 := bbase (se 3 (by rfl) ⟨422537, by rfl⟩ : syracuseStep 2253533 = 845075) (by norm_num)
theorem B2253557 : Blo 1502071 2253557 := bbase (se 5 (by rfl) ⟨105635, by rfl⟩ : syracuseStep 2253557 = 211271) (by norm_num)
theorem B2253581 : Blo 1502071 2253581 := bbase (se 3 (by rfl) ⟨422546, by rfl⟩ : syracuseStep 2253581 = 845093) (by norm_num)
theorem B1901333 : Blo 1502071 1901333 := bbase (se 6 (by rfl) ⟨44562, by rfl⟩ : syracuseStep 1901333 = 89125) (by norm_num)
theorem B2253605 : Blo 1502071 2253605 := bbase (se 4 (by rfl) ⟨211275, by rfl⟩ : syracuseStep 2253605 = 422551) (by norm_num)
theorem B2253629 : Blo 1502071 2253629 := bbase (se 3 (by rfl) ⟨422555, by rfl⟩ : syracuseStep 2253629 = 845111) (by norm_num)
theorem B1901389 : Blo 1502071 1901389 := bbase (se 3 (by rfl) ⟨356510, by rfl⟩ : syracuseStep 1901389 = 713021) (by norm_num)
theorem B2253653 : Blo 1502071 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B2138989 : Blo 1502071 2138989 := bbase (se 3 (by rfl) ⟨401060, by rfl⟩ : syracuseStep 2138989 = 802121) (by norm_num)
theorem B2253677 : Blo 1502071 2253677 := bbase (se 3 (by rfl) ⟨422564, by rfl⟩ : syracuseStep 2253677 = 845129) (by norm_num)
theorem B5071733 : Blo 1502071 5071733 := bbase (se 5 (by rfl) ⟨237737, by rfl⟩ : syracuseStep 5071733 = 475475) (by norm_num)
theorem B2253701 : Blo 1502071 2253701 := bbase (se 4 (by rfl) ⟨211284, by rfl⟩ : syracuseStep 2253701 = 422569) (by norm_num)
theorem B2253725 : Blo 1502071 2253725 := bbase (se 3 (by rfl) ⟨422573, by rfl⟩ : syracuseStep 2253725 = 845147) (by norm_num)
theorem B2851757 : Blo 1502071 2851757 := bbase (se 3 (by rfl) ⟨534704, by rfl⟩ : syracuseStep 2851757 = 1069409) (by norm_num)
theorem B1901485 : Blo 1502071 1901485 := bbase (se 3 (by rfl) ⟨356528, by rfl⟩ : syracuseStep 1901485 = 713057) (by norm_num)
theorem B2253749 : Blo 1502071 2253749 := bbase (se 5 (by rfl) ⟨105644, by rfl⟩ : syracuseStep 2253749 = 211289) (by norm_num)
theorem B2253773 : Blo 1502071 2253773 := bbase (se 3 (by rfl) ⟨422582, by rfl⟩ : syracuseStep 2253773 = 845165) (by norm_num)
theorem B2253797 : Blo 1502071 2253797 := bbase (se 4 (by rfl) ⟨211293, by rfl⟩ : syracuseStep 2253797 = 422587) (by norm_num)
theorem B2253821 : Blo 1502071 2253821 := bbase (se 3 (by rfl) ⟨422591, by rfl⟩ : syracuseStep 2253821 = 845183) (by norm_num)
theorem B2253845 : Blo 1502071 2253845 := bbase (se 6 (by rfl) ⟨52824, by rfl⟩ : syracuseStep 2253845 = 105649) (by norm_num)
theorem B2253869 : Blo 1502071 2253869 := bbase (se 3 (by rfl) ⟨422600, by rfl⟩ : syracuseStep 2253869 = 845201) (by norm_num)
theorem B2139205 : Blo 1502071 2139205 := bbase (se 4 (by rfl) ⟨200550, by rfl⟩ : syracuseStep 2139205 = 401101) (by norm_num)
theorem B2253893 : Blo 1502071 2253893 := bbase (se 4 (by rfl) ⟨211302, by rfl⟩ : syracuseStep 2253893 = 422605) (by norm_num)
theorem B1901657 : Blo 1502071 1901657 := bbase (se 2 (by rfl) ⟨713121, by rfl⟩ : syracuseStep 1901657 = 1426243) (by norm_num)
theorem B2253917 : Blo 1502071 2253917 := bbase (se 3 (by rfl) ⟨422609, by rfl⟩ : syracuseStep 2253917 = 845219) (by norm_num)
theorem B2253941 : Blo 1502071 2253941 := bbase (se 5 (by rfl) ⟨105653, by rfl⟩ : syracuseStep 2253941 = 211307) (by norm_num)
theorem B6095989 : Blo 1502071 6095989 := bbase (se 5 (by rfl) ⟨285749, by rfl⟩ : syracuseStep 6095989 = 571499) (by norm_num)
theorem B6096005 : Blo 1502071 6096005 := bbase (se 4 (by rfl) ⟨571500, by rfl⟩ : syracuseStep 6096005 = 1143001) (by norm_num)
theorem B2253965 : Blo 1502071 2253965 := bbase (se 3 (by rfl) ⟨422618, by rfl⟩ : syracuseStep 2253965 = 845237) (by norm_num)
theorem B1901713 : Blo 1502071 1901713 := bbase (se 2 (by rfl) ⟨713142, by rfl⟩ : syracuseStep 1901713 = 1426285) (by norm_num)
theorem B27780245 : Blo 1502071 27780245 := bbase (se 6 (by rfl) ⟨651099, by rfl⟩ : syracuseStep 27780245 = 1302199) (by norm_num)
theorem B3802261 : Blo 1502071 3802261 := bbase (se 6 (by rfl) ⟨89115, by rfl⟩ : syracuseStep 3802261 = 178231) (by norm_num)
theorem B2253989 : Blo 1502071 2253989 := bbase (se 4 (by rfl) ⟨211311, by rfl⟩ : syracuseStep 2253989 = 422623) (by norm_num)
theorem B7521461 : Blo 1502071 7521461 := bbase (se 5 (by rfl) ⟨352568, by rfl⟩ : syracuseStep 7521461 = 705137) (by norm_num)
theorem B2254013 : Blo 1502071 2254013 := bbase (se 3 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 2254013 = 845255) (by norm_num)
theorem B2254037 : Blo 1502071 2254037 := bbase (se 7 (by rfl) ⟨26414, by rfl⟩ : syracuseStep 2254037 = 52829) (by norm_num)
theorem B2254061 : Blo 1502071 2254061 := bbase (se 3 (by rfl) ⟨422636, by rfl⟩ : syracuseStep 2254061 = 845273) (by norm_num)
theorem B1901809 : Blo 1502071 1901809 := bbase (se 2 (by rfl) ⟨713178, by rfl⟩ : syracuseStep 1901809 = 1426357) (by norm_num)
theorem B3802373 : Blo 1502071 3802373 := bbase (se 4 (by rfl) ⟨356472, by rfl⟩ : syracuseStep 3802373 = 712945) (by norm_num)
theorem B2254085 : Blo 1502071 2254085 := bbase (se 4 (by rfl) ⟨211320, by rfl⟩ : syracuseStep 2254085 = 422641) (by norm_num)
theorem B2254109 : Blo 1502071 2254109 := bbase (se 3 (by rfl) ⟨422645, by rfl⟩ : syracuseStep 2254109 = 845291) (by norm_num)
theorem B5072165 : Blo 1502071 5072165 := bbase (se 4 (by rfl) ⟨475515, by rfl⟩ : syracuseStep 5072165 = 951031) (by norm_num)
theorem B2254133 : Blo 1502071 2254133 := bbase (se 5 (by rfl) ⟨105662, by rfl⟩ : syracuseStep 2254133 = 211325) (by norm_num)
theorem B2254157 : Blo 1502071 2254157 := bbase (se 3 (by rfl) ⟨422654, by rfl⟩ : syracuseStep 2254157 = 845309) (by norm_num)
theorem B2254181 : Blo 1502071 2254181 := bbase (se 4 (by rfl) ⟨211329, by rfl⟩ : syracuseStep 2254181 = 422659) (by norm_num)
theorem B2254205 : Blo 1502071 2254205 := bbase (se 3 (by rfl) ⟨422663, by rfl⟩ : syracuseStep 2254205 = 845327) (by norm_num)
theorem B2254229 : Blo 1502071 2254229 := bbase (se 6 (by rfl) ⟨52833, by rfl⟩ : syracuseStep 2254229 = 105667) (by norm_num)
theorem B1901981 : Blo 1502071 1901981 := bbase (se 3 (by rfl) ⟨356621, by rfl⟩ : syracuseStep 1901981 = 713243) (by norm_num)
theorem B2254253 : Blo 1502071 2254253 := bbase (se 3 (by rfl) ⟨422672, by rfl⟩ : syracuseStep 2254253 = 845345) (by norm_num)
theorem B2139581 : Blo 1502071 2139581 := bbase (se 3 (by rfl) ⟨401171, by rfl⟩ : syracuseStep 2139581 = 802343) (by norm_num)
theorem B3802565 : Blo 1502071 3802565 := bbase (se 4 (by rfl) ⟨356490, by rfl⟩ : syracuseStep 3802565 = 712981) (by norm_num)
theorem B2254277 : Blo 1502071 2254277 := bbase (se 4 (by rfl) ⟨211338, by rfl⟩ : syracuseStep 2254277 = 422677) (by norm_num)
theorem B1902037 : Blo 1502071 1902037 := bbase (se 7 (by rfl) ⟨22289, by rfl⟩ : syracuseStep 1902037 = 44579) (by norm_num)
theorem B1713625 : Blo 1502071 1713625 := bbase (se 2 (by rfl) ⟨642609, by rfl⟩ : syracuseStep 1713625 = 1285219) (by norm_num)
theorem B2254301 : Blo 1502071 2254301 := bbase (se 3 (by rfl) ⟨422681, by rfl⟩ : syracuseStep 2254301 = 845363) (by norm_num)
theorem B2254325 : Blo 1502071 2254325 := bbase (se 5 (by rfl) ⟨105671, by rfl⟩ : syracuseStep 2254325 = 211343) (by norm_num)
theorem B3253765 : Blo 1502071 3253765 := bbase (se 4 (by rfl) ⟨305040, by rfl⟩ : syracuseStep 3253765 = 610081) (by norm_num)
theorem B2254349 : Blo 1502071 2254349 := bbase (se 3 (by rfl) ⟨422690, by rfl⟩ : syracuseStep 2254349 = 845381) (by norm_num)
theorem B2254373 : Blo 1502071 2254373 := bbase (se 4 (by rfl) ⟨211347, by rfl⟩ : syracuseStep 2254373 = 422695) (by norm_num)
theorem B1902133 : Blo 1502071 1902133 := bbase (se 5 (by rfl) ⟨89162, by rfl⟩ : syracuseStep 1902133 = 178325) (by norm_num)
theorem B2254397 : Blo 1502071 2254397 := bbase (se 3 (by rfl) ⟨422699, by rfl⟩ : syracuseStep 2254397 = 845399) (by norm_num)
theorem B2254421 : Blo 1502071 2254421 := bbase (se 8 (by rfl) ⟨13209, by rfl⟩ : syracuseStep 2254421 = 26419) (by norm_num)
theorem B3425885 : Blo 1502071 3425885 := bbase (se 3 (by rfl) ⟨642353, by rfl⟩ : syracuseStep 3425885 = 1284707) (by norm_num)
theorem B2254445 : Blo 1502071 2254445 := bbase (se 3 (by rfl) ⟨422708, by rfl⟩ : syracuseStep 2254445 = 845417) (by norm_num)
theorem B2254469 : Blo 1502071 2254469 := bbase (se 4 (by rfl) ⟨211356, by rfl⟩ : syracuseStep 2254469 = 422713) (by norm_num)
theorem B5703317 : Blo 1502071 5703317 := bbase (se 6 (by rfl) ⟨133671, by rfl⟩ : syracuseStep 5703317 = 267343) (by norm_num)
theorem B4277909 : Blo 1502071 4277909 := bbase (se 6 (by rfl) ⟨100263, by rfl⟩ : syracuseStep 4277909 = 200527) (by norm_num)
theorem B2852509 : Blo 1502071 2852509 := bbase (se 3 (by rfl) ⟨534845, by rfl⟩ : syracuseStep 2852509 = 1069691) (by norm_num)
theorem B2254493 : Blo 1502071 2254493 := bbase (se 3 (by rfl) ⟨422717, by rfl⟩ : syracuseStep 2254493 = 845435) (by norm_num)
theorem B1713845 : Blo 1502071 1713845 := bbase (se 5 (by rfl) ⟨80336, by rfl⟩ : syracuseStep 1713845 = 160673) (by norm_num)
theorem B2254517 : Blo 1502071 2254517 := bbase (se 5 (by rfl) ⟨105680, by rfl⟩ : syracuseStep 2254517 = 211361) (by norm_num)
theorem B2254541 : Blo 1502071 2254541 := bbase (se 3 (by rfl) ⟨422726, by rfl⟩ : syracuseStep 2254541 = 845453) (by norm_num)
theorem B5072597 : Blo 1502071 5072597 := bbase (se 7 (by rfl) ⟨59444, by rfl⟩ : syracuseStep 5072597 = 118889) (by norm_num)
theorem B1902305 : Blo 1502071 1902305 := bbase (se 2 (by rfl) ⟨713364, by rfl⟩ : syracuseStep 1902305 = 1426729) (by norm_num)
theorem B2254565 : Blo 1502071 2254565 := bbase (se 4 (by rfl) ⟨211365, by rfl⟩ : syracuseStep 2254565 = 422731) (by norm_num)
theorem B2254589 : Blo 1502071 2254589 := bbase (se 3 (by rfl) ⟨422735, by rfl⟩ : syracuseStep 2254589 = 845471) (by norm_num)
theorem B2254613 : Blo 1502071 2254613 := bbase (se 6 (by rfl) ⟨52842, by rfl⟩ : syracuseStep 2254613 = 105685) (by norm_num)
theorem B15255317 : Blo 1502071 15255317 := bbase (se 6 (by rfl) ⟨357546, by rfl⟩ : syracuseStep 15255317 = 715093) (by norm_num)
theorem B1902361 : Blo 1502071 1902361 := bbase (se 2 (by rfl) ⟨713385, by rfl⟩ : syracuseStep 1902361 = 1426771) (by norm_num)
theorem B3802909 : Blo 1502071 3802909 := bbase (se 3 (by rfl) ⟨713045, by rfl⟩ : syracuseStep 3802909 = 1426091) (by norm_num)
theorem B2852653 : Blo 1502071 2852653 := bbase (se 3 (by rfl) ⟨534872, by rfl⟩ : syracuseStep 2852653 = 1069745) (by norm_num)
theorem B2254637 : Blo 1502071 2254637 := bbase (se 3 (by rfl) ⟨422744, by rfl⟩ : syracuseStep 2254637 = 845489) (by norm_num)
theorem B3475261 : Blo 1502071 3475261 := bbase (se 3 (by rfl) ⟨651611, by rfl⟩ : syracuseStep 3475261 = 1303223) (by norm_num)
theorem B2254661 : Blo 1502071 2254661 := bbase (se 4 (by rfl) ⟨211374, by rfl⟩ : syracuseStep 2254661 = 422749) (by norm_num)
theorem B2254685 : Blo 1502071 2254685 := bbase (se 3 (by rfl) ⟨422753, by rfl⟩ : syracuseStep 2254685 = 845507) (by norm_num)
theorem B14444405 : Blo 1502071 14444405 := bbase (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) (by norm_num)
theorem B2254709 : Blo 1502071 2254709 := bbase (se 5 (by rfl) ⟨105689, by rfl⟩ : syracuseStep 2254709 = 211379) (by norm_num)
theorem B1902457 : Blo 1502071 1902457 := bbase (se 2 (by rfl) ⟨713421, by rfl⟩ : syracuseStep 1902457 = 1426843) (by norm_num)
theorem B3803021 : Blo 1502071 3803021 := bbase (se 3 (by rfl) ⟨713066, by rfl⟩ : syracuseStep 3803021 = 1426133) (by norm_num)
theorem B2254733 : Blo 1502071 2254733 := bbase (se 3 (by rfl) ⟨422762, by rfl⟩ : syracuseStep 2254733 = 845525) (by norm_num)
theorem B2254757 : Blo 1502071 2254757 := bbase (se 4 (by rfl) ⟨211383, by rfl⟩ : syracuseStep 2254757 = 422767) (by norm_num)
theorem B5703605 : Blo 1502071 5703605 := bbase (se 5 (by rfl) ⟨267356, by rfl⟩ : syracuseStep 5703605 = 534713) (by norm_num)
theorem B2254781 : Blo 1502071 2254781 := bbase (se 3 (by rfl) ⟨422771, by rfl⟩ : syracuseStep 2254781 = 845543) (by norm_num)
theorem B2852813 : Blo 1502071 2852813 := bbase (se 3 (by rfl) ⟨534902, by rfl⟩ : syracuseStep 2852813 = 1069805) (by norm_num)
theorem B2254805 : Blo 1502071 2254805 := bbase (se 7 (by rfl) ⟨26423, by rfl⟩ : syracuseStep 2254805 = 52847) (by norm_num)
theorem B2254829 : Blo 1502071 2254829 := bbase (se 3 (by rfl) ⟨422780, by rfl⟩ : syracuseStep 2254829 = 845561) (by norm_num)
theorem B2254853 : Blo 1502071 2254853 := bbase (se 4 (by rfl) ⟨211392, by rfl⟩ : syracuseStep 2254853 = 422785) (by norm_num)
theorem B2254877 : Blo 1502071 2254877 := bbase (se 3 (by rfl) ⟨422789, by rfl⟩ : syracuseStep 2254877 = 845579) (by norm_num)
theorem B1902629 : Blo 1502071 1902629 := bbase (se 4 (by rfl) ⟨178371, by rfl⟩ : syracuseStep 1902629 = 356743) (by norm_num)
theorem B2254901 : Blo 1502071 2254901 := bbase (se 5 (by rfl) ⟨105698, by rfl⟩ : syracuseStep 2254901 = 211397) (by norm_num)
theorem B3803213 : Blo 1502071 3803213 := bbase (se 3 (by rfl) ⟨713102, by rfl⟩ : syracuseStep 3803213 = 1426205) (by norm_num)
theorem B2254925 : Blo 1502071 2254925 := bbase (se 3 (by rfl) ⟨422798, by rfl⟩ : syracuseStep 2254925 = 845597) (by norm_num)
theorem B2852957 : Blo 1502071 2852957 := bbase (se 3 (by rfl) ⟨534929, by rfl⟩ : syracuseStep 2852957 = 1069859) (by norm_num)
theorem B1902685 : Blo 1502071 1902685 := bbase (se 3 (by rfl) ⟨356753, by rfl⟩ : syracuseStep 1902685 = 713507) (by norm_num)
theorem B2254949 : Blo 1502071 2254949 := bbase (se 4 (by rfl) ⟨211401, by rfl⟩ : syracuseStep 2254949 = 422803) (by norm_num)
theorem B2254973 : Blo 1502071 2254973 := bbase (se 3 (by rfl) ⟨422807, by rfl⟩ : syracuseStep 2254973 = 845615) (by norm_num)
theorem B5073029 : Blo 1502071 5073029 := bbase (se 4 (by rfl) ⟨475596, by rfl⟩ : syracuseStep 5073029 = 951193) (by norm_num)
theorem B2254997 : Blo 1502071 2254997 := bbase (se 6 (by rfl) ⟨52851, by rfl⟩ : syracuseStep 2254997 = 105703) (by norm_num)
theorem B2255021 : Blo 1502071 2255021 := bbase (se 3 (by rfl) ⟨422816, by rfl⟩ : syracuseStep 2255021 = 845633) (by norm_num)
theorem B1902781 : Blo 1502071 1902781 := bbase (se 3 (by rfl) ⟨356771, by rfl⟩ : syracuseStep 1902781 = 713543) (by norm_num)
theorem B2255045 : Blo 1502071 2255045 := bbase (se 4 (by rfl) ⟨211410, by rfl⟩ : syracuseStep 2255045 = 422821) (by norm_num)
theorem B2255069 : Blo 1502071 2255069 := bbase (se 3 (by rfl) ⟨422825, by rfl⟩ : syracuseStep 2255069 = 845651) (by norm_num)
theorem B2255093 : Blo 1502071 2255093 := bbase (se 5 (by rfl) ⟨105707, by rfl⟩ : syracuseStep 2255093 = 211415) (by norm_num)
theorem B1689853 : Blo 1502071 1689853 := bbase (se 3 (by rfl) ⟨316847, by rfl⟩ : syracuseStep 1689853 = 633695) (by norm_num)
theorem B2255117 : Blo 1502071 2255117 := bbase (se 3 (by rfl) ⟨422834, by rfl⟩ : syracuseStep 2255117 = 845669) (by norm_num)
theorem B1689889 : Blo 1502071 1689889 := bbase (se 2 (by rfl) ⟨633708, by rfl⟩ : syracuseStep 1689889 = 1267417) (by norm_num)
theorem B7219493 : Blo 1502071 7219493 := bbase (se 4 (by rfl) ⟨676827, by rfl⟩ : syracuseStep 7219493 = 1353655) (by norm_num)
theorem B2255141 : Blo 1502071 2255141 := bbase (se 4 (by rfl) ⟨211419, by rfl⟩ : syracuseStep 2255141 = 422839) (by norm_num)
theorem B2255165 : Blo 1502071 2255165 := bbase (se 3 (by rfl) ⟨422843, by rfl⟩ : syracuseStep 2255165 = 845687) (by norm_num)
theorem B1689925 : Blo 1502071 1689925 := bbase (se 4 (by rfl) ⟨158430, by rfl⟩ : syracuseStep 1689925 = 316861) (by norm_num)
theorem B2255189 : Blo 1502071 2255189 := bbase (se 10 (by rfl) ⟨3303, by rfl⟩ : syracuseStep 2255189 = 6607) (by norm_num)
theorem B1689961 : Blo 1502071 1689961 := bbase (se 2 (by rfl) ⟨633735, by rfl⟩ : syracuseStep 1689961 = 1267471) (by norm_num)
theorem B1902953 : Blo 1502071 1902953 := bbase (se 2 (by rfl) ⟨713607, by rfl⟩ : syracuseStep 1902953 = 1427215) (by norm_num)
theorem B2255213 : Blo 1502071 2255213 := bbase (se 3 (by rfl) ⟨422852, by rfl⟩ : syracuseStep 2255213 = 845705) (by norm_num)
theorem B2853245 : Blo 1502071 2853245 := bbase (se 3 (by rfl) ⟨534983, by rfl⟩ : syracuseStep 2853245 = 1069967) (by norm_num)
theorem B2255237 : Blo 1502071 2255237 := bbase (se 4 (by rfl) ⟨211428, by rfl⟩ : syracuseStep 2255237 = 422857) (by norm_num)
theorem B1689997 : Blo 1502071 1689997 := bbase (se 3 (by rfl) ⟨316874, by rfl⟩ : syracuseStep 1689997 = 633749) (by norm_num)
theorem B2255261 : Blo 1502071 2255261 := bbase (se 3 (by rfl) ⟨422861, by rfl⟩ : syracuseStep 2255261 = 845723) (by norm_num)
theorem B3803557 : Blo 1502071 3803557 := bbase (se 4 (by rfl) ⟨356583, by rfl⟩ : syracuseStep 3803557 = 713167) (by norm_num)
theorem B5491109 : Blo 1502071 5491109 := bbase (se 4 (by rfl) ⟨514791, by rfl⟩ : syracuseStep 5491109 = 1029583) (by norm_num)
theorem B1690033 : Blo 1502071 1690033 := bbase (se 2 (by rfl) ⟨633762, by rfl⟩ : syracuseStep 1690033 = 1267525) (by norm_num)
theorem B2255285 : Blo 1502071 2255285 := bbase (se 5 (by rfl) ⟨105716, by rfl⟩ : syracuseStep 2255285 = 211433) (by norm_num)
theorem B2255309 : Blo 1502071 2255309 := bbase (se 3 (by rfl) ⟨422870, by rfl⟩ : syracuseStep 2255309 = 845741) (by norm_num)
theorem B1690069 : Blo 1502071 1690069 := bbase (se 7 (by rfl) ⟨19805, by rfl⟩ : syracuseStep 1690069 = 39611) (by norm_num)
theorem B2255333 : Blo 1502071 2255333 := bbase (se 4 (by rfl) ⟨211437, by rfl⟩ : syracuseStep 2255333 = 422875) (by norm_num)
theorem B8554997 : Blo 1502071 8554997 := bbase (se 5 (by rfl) ⟨401015, by rfl⟩ : syracuseStep 8554997 = 802031) (by norm_num)
theorem B1690105 : Blo 1502071 1690105 := bbase (se 2 (by rfl) ⟨633789, by rfl⟩ : syracuseStep 1690105 = 1267579) (by norm_num)
theorem B2255357 : Blo 1502071 2255357 := bbase (se 3 (by rfl) ⟨422879, by rfl⟩ : syracuseStep 2255357 = 845759) (by norm_num)
theorem B3803669 : Blo 1502071 3803669 := bbase (se 6 (by rfl) ⟨89148, by rfl⟩ : syracuseStep 3803669 = 178297) (by norm_num)
theorem B2853397 : Blo 1502071 2853397 := bbase (se 6 (by rfl) ⟨66876, by rfl⟩ : syracuseStep 2853397 = 133753) (by norm_num)
theorem B1690141 : Blo 1502071 1690141 := bbase (se 3 (by rfl) ⟨316901, by rfl⟩ : syracuseStep 1690141 = 633803) (by norm_num)
theorem B5073461 : Blo 1502071 5073461 := bbase (se 5 (by rfl) ⟨237818, by rfl⟩ : syracuseStep 5073461 = 475637) (by norm_num)
theorem B1690177 : Blo 1502071 1690177 := bbase (se 2 (by rfl) ⟨633816, by rfl⟩ : syracuseStep 1690177 = 1267633) (by norm_num)
theorem B1690213 : Blo 1502071 1690213 := bbase (se 4 (by rfl) ⟨158457, by rfl⟩ : syracuseStep 1690213 = 316915) (by norm_num)
theorem B1690249 : Blo 1502071 1690249 := bbase (se 2 (by rfl) ⟨633843, by rfl⟩ : syracuseStep 1690249 = 1267687) (by norm_num)
theorem B1690285 : Blo 1502071 1690285 := bbase (se 3 (by rfl) ⟨316928, by rfl⟩ : syracuseStep 1690285 = 633857) (by norm_num)
theorem B1690321 : Blo 1502071 1690321 := bbase (se 2 (by rfl) ⟨633870, by rfl⟩ : syracuseStep 1690321 = 1267741) (by norm_num)
theorem B3803861 : Blo 1502071 3803861 := bbase (se 7 (by rfl) ⟨44576, by rfl⟩ : syracuseStep 3803861 = 89153) (by norm_num)
theorem B1690357 : Blo 1502071 1690357 := bbase (se 5 (by rfl) ⟨79235, by rfl⟩ : syracuseStep 1690357 = 158471) (by norm_num)
theorem B1690393 : Blo 1502071 1690393 := bbase (se 2 (by rfl) ⟨633897, by rfl⟩ : syracuseStep 1690393 = 1267795) (by norm_num)
theorem B1690429 : Blo 1502071 1690429 := bbase (se 3 (by rfl) ⟨316955, by rfl⟩ : syracuseStep 1690429 = 633911) (by norm_num)
theorem B2853701 : Blo 1502071 2853701 := bbase (se 4 (by rfl) ⟨267534, by rfl⟩ : syracuseStep 2853701 = 535069) (by norm_num)
theorem B1690465 : Blo 1502071 1690465 := bbase (se 2 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 1690465 = 1267849) (by norm_num)
theorem B1805185 : Blo 1502071 1805185 := bbase (se 2 (by rfl) ⟨676944, by rfl⟩ : syracuseStep 1805185 = 1353889) (by norm_num)
theorem B1690501 : Blo 1502071 1690501 := bbase (se 4 (by rfl) ⟨158484, by rfl⟩ : syracuseStep 1690501 = 316969) (by norm_num)
theorem B1690537 : Blo 1502071 1690537 := bbase (se 2 (by rfl) ⟨633951, by rfl⟩ : syracuseStep 1690537 = 1267903) (by norm_num)
theorem B1690573 : Blo 1502071 1690573 := bbase (se 3 (by rfl) ⟨316982, by rfl⟩ : syracuseStep 1690573 = 633965) (by norm_num)
theorem B5073893 : Blo 1502071 5073893 := bbase (se 4 (by rfl) ⟨475677, by rfl⟩ : syracuseStep 5073893 = 951355) (by norm_num)
theorem B1690609 : Blo 1502071 1690609 := bbase (se 2 (by rfl) ⟨633978, by rfl⟩ : syracuseStep 1690609 = 1267957) (by norm_num)
theorem B1690645 : Blo 1502071 1690645 := bbase (se 6 (by rfl) ⟨39624, by rfl⟩ : syracuseStep 1690645 = 79249) (by norm_num)
theorem B3804205 : Blo 1502071 3804205 := bbase (se 3 (by rfl) ⟨713288, by rfl⟩ : syracuseStep 3804205 = 1426577) (by norm_num)
theorem B1690681 : Blo 1502071 1690681 := bbase (se 2 (by rfl) ⟨634005, by rfl⟩ : syracuseStep 1690681 = 1268011) (by norm_num)
theorem B5704789 : Blo 1502071 5704789 := bbase (se 8 (by rfl) ⟨33426, by rfl⟩ : syracuseStep 5704789 = 66853) (by norm_num)
theorem B1690717 : Blo 1502071 1690717 := bbase (se 3 (by rfl) ⟨317009, by rfl⟩ : syracuseStep 1690717 = 634019) (by norm_num)
theorem B1690753 : Blo 1502071 1690753 := bbase (se 2 (by rfl) ⟨634032, by rfl⟩ : syracuseStep 1690753 = 1268065) (by norm_num)
theorem B3804317 : Blo 1502071 3804317 := bbase (se 3 (by rfl) ⟨713309, by rfl⟩ : syracuseStep 3804317 = 1426619) (by norm_num)
theorem B7605413 : Blo 1502071 7605413 := bbase (se 4 (by rfl) ⟨713007, by rfl⟩ : syracuseStep 7605413 = 1426015) (by norm_num)
theorem B1690789 : Blo 1502071 1690789 := bbase (se 4 (by rfl) ⟨158511, by rfl⟩ : syracuseStep 1690789 = 317023) (by norm_num)
theorem B4279493 : Blo 1502071 4279493 := bbase (se 4 (by rfl) ⟨401202, by rfl⟩ : syracuseStep 4279493 = 802405) (by norm_num)
theorem B1690825 : Blo 1502071 1690825 := bbase (se 2 (by rfl) ⟨634059, by rfl⟩ : syracuseStep 1690825 = 1268119) (by norm_num)
theorem B1690861 : Blo 1502071 1690861 := bbase (se 3 (by rfl) ⟨317036, by rfl⟩ : syracuseStep 1690861 = 634073) (by norm_num)
theorem B5139701 : Blo 1502071 5139701 := bbase (se 5 (by rfl) ⟨240923, by rfl⟩ : syracuseStep 5139701 = 481847) (by norm_num)
theorem B1690897 : Blo 1502071 1690897 := bbase (se 2 (by rfl) ⟨634086, by rfl⟩ : syracuseStep 1690897 = 1268173) (by norm_num)
theorem B1690933 : Blo 1502071 1690933 := bbase (se 5 (by rfl) ⟨79262, by rfl⟩ : syracuseStep 1690933 = 158525) (by norm_num)
theorem B1690969 : Blo 1502071 1690969 := bbase (se 2 (by rfl) ⟨634113, by rfl⟩ : syracuseStep 1690969 = 1268227) (by norm_num)
theorem B3804509 : Blo 1502071 3804509 := bbase (se 3 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 3804509 = 1426691) (by norm_num)
theorem B2534773 : Blo 1502071 2534773 := bbase (se 5 (by rfl) ⟨118817, by rfl⟩ : syracuseStep 2534773 = 237635) (by norm_num)
theorem B1691005 : Blo 1502071 1691005 := bbase (se 3 (by rfl) ⟨317063, by rfl⟩ : syracuseStep 1691005 = 634127) (by norm_num)
theorem B5705093 : Blo 1502071 5705093 := bbase (se 4 (by rfl) ⟨534852, by rfl⟩ : syracuseStep 5705093 = 1069705) (by norm_num)
theorem B5074325 : Blo 1502071 5074325 := bbase (se 6 (by rfl) ⟨118929, by rfl⟩ : syracuseStep 5074325 = 237859) (by norm_num)
theorem B1691041 : Blo 1502071 1691041 := bbase (se 2 (by rfl) ⟨634140, by rfl⟩ : syracuseStep 1691041 = 1268281) (by norm_num)
theorem B1691077 : Blo 1502071 1691077 := bbase (se 4 (by rfl) ⟨158538, by rfl⟩ : syracuseStep 1691077 = 317077) (by norm_num)
theorem B2534861 : Blo 1502071 2534861 := bbase (se 3 (by rfl) ⟨475286, by rfl⟩ : syracuseStep 2534861 = 950573) (by norm_num)
theorem B1691113 : Blo 1502071 1691113 := bbase (se 2 (by rfl) ⟨634167, by rfl⟩ : syracuseStep 1691113 = 1268335) (by norm_num)
theorem B1691149 : Blo 1502071 1691149 := bbase (se 3 (by rfl) ⟨317090, by rfl⟩ : syracuseStep 1691149 = 634181) (by norm_num)
theorem B1691185 : Blo 1502071 1691185 := bbase (se 2 (by rfl) ⟨634194, by rfl⟩ : syracuseStep 1691185 = 1268389) (by norm_num)
theorem B2534989 : Blo 1502071 2534989 := bbase (se 3 (by rfl) ⟨475310, by rfl⟩ : syracuseStep 2534989 = 950621) (by norm_num)
theorem B1691221 : Blo 1502071 1691221 := bbase (se 8 (by rfl) ⟨9909, by rfl⟩ : syracuseStep 1691221 = 19819) (by norm_num)
theorem B1691257 : Blo 1502071 1691257 := bbase (se 2 (by rfl) ⟨634221, by rfl⟩ : syracuseStep 1691257 = 1268443) (by norm_num)
theorem B1691293 : Blo 1502071 1691293 := bbase (se 3 (by rfl) ⟨317117, by rfl⟩ : syracuseStep 1691293 = 634235) (by norm_num)
theorem B1953445 : Blo 1502071 1953445 := bbase (se 4 (by rfl) ⟨183135, by rfl⟩ : syracuseStep 1953445 = 366271) (by norm_num)
theorem B2535077 : Blo 1502071 2535077 := bbase (se 4 (by rfl) ⟨237663, by rfl⟩ : syracuseStep 2535077 = 475327) (by norm_num)
theorem B3804853 : Blo 1502071 3804853 := bbase (se 5 (by rfl) ⟨178352, by rfl⟩ : syracuseStep 3804853 = 356705) (by norm_num)
theorem B1691329 : Blo 1502071 1691329 := bbase (se 2 (by rfl) ⟨634248, by rfl⟩ : syracuseStep 1691329 = 1268497) (by norm_num)
theorem B1691365 : Blo 1502071 1691365 := bbase (se 4 (by rfl) ⟨158565, by rfl⟩ : syracuseStep 1691365 = 317131) (by norm_num)
theorem B1691401 : Blo 1502071 1691401 := bbase (se 2 (by rfl) ⟨634275, by rfl⟩ : syracuseStep 1691401 = 1268551) (by norm_num)
theorem B14634773 : Blo 1502071 14634773 := bbase (se 6 (by rfl) ⟨343002, by rfl⟩ : syracuseStep 14634773 = 686005) (by norm_num)
theorem B2535205 : Blo 1502071 2535205 := bbase (se 4 (by rfl) ⟨237675, by rfl⟩ : syracuseStep 2535205 = 475351) (by norm_num)
theorem B3804965 : Blo 1502071 3804965 := bbase (se 4 (by rfl) ⟨356715, by rfl⟩ : syracuseStep 3804965 = 713431) (by norm_num)
theorem B1691437 : Blo 1502071 1691437 := bbase (se 3 (by rfl) ⟨317144, by rfl⟩ : syracuseStep 1691437 = 634289) (by norm_num)
theorem B1691473 : Blo 1502071 1691473 := bbase (se 2 (by rfl) ⟨634302, by rfl⟩ : syracuseStep 1691473 = 1268605) (by norm_num)
theorem B4280165 : Blo 1502071 4280165 := bbase (se 4 (by rfl) ⟨401265, by rfl⟩ : syracuseStep 4280165 = 802531) (by norm_num)
theorem B1806185 : Blo 1502071 1806185 := bbase (se 2 (by rfl) ⟨677319, by rfl⟩ : syracuseStep 1806185 = 1354639) (by norm_num)
theorem B1691509 : Blo 1502071 1691509 := bbase (se 5 (by rfl) ⟨79289, by rfl⟩ : syracuseStep 1691509 = 158579) (by norm_num)
theorem B2535293 : Blo 1502071 2535293 := bbase (se 3 (by rfl) ⟨475367, by rfl⟩ : syracuseStep 2535293 = 950735) (by norm_num)
theorem B7221125 : Blo 1502071 7221125 := bbase (se 4 (by rfl) ⟨676980, by rfl⟩ : syracuseStep 7221125 = 1353961) (by norm_num)
theorem B1806257 : Blo 1502071 1806257 := bbase (se 2 (by rfl) ⟨677346, by rfl⟩ : syracuseStep 1806257 = 1354693) (by norm_num)
theorem B3805157 : Blo 1502071 3805157 := bbase (se 4 (by rfl) ⟨356733, by rfl⟩ : syracuseStep 3805157 = 713467) (by norm_num)
theorem B2535421 : Blo 1502071 2535421 := bbase (se 3 (by rfl) ⟨475391, by rfl⟩ : syracuseStep 2535421 = 950783) (by norm_num)
theorem B1855529 : Blo 1502071 1855529 := bbase (se 2 (by rfl) ⟨695823, by rfl⟩ : syracuseStep 1855529 = 1391647) (by norm_num)
theorem B4812853 : Blo 1502071 4812853 := bbase (se 5 (by rfl) ⟨225602, by rfl⟩ : syracuseStep 4812853 = 451205) (by norm_num)
theorem B2535509 : Blo 1502071 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B1626325 : Blo 1502071 1626325 := bbase (se 7 (by rfl) ⟨19058, by rfl⟩ : syracuseStep 1626325 = 38117) (by norm_num)
theorem B2535637 : Blo 1502071 2535637 := bbase (se 7 (by rfl) ⟨29714, by rfl⟩ : syracuseStep 2535637 = 59429) (by norm_num)
theorem B6418709 : Blo 1502071 6418709 := bbase (se 6 (by rfl) ⟨150438, by rfl⟩ : syracuseStep 6418709 = 300877) (by norm_num)
theorem B4280597 : Blo 1502071 4280597 := bbase (se 6 (by rfl) ⟨100326, by rfl⟩ : syracuseStep 4280597 = 200653) (by norm_num)
theorem B2535725 : Blo 1502071 2535725 := bbase (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) (by norm_num)
theorem B4813109 : Blo 1502071 4813109 := bbase (se 5 (by rfl) ⟨225614, by rfl⟩ : syracuseStep 4813109 = 451229) (by norm_num)
theorem B7819573 : Blo 1502071 7819573 := bbase (se 5 (by rfl) ⟨366542, by rfl⟩ : syracuseStep 7819573 = 733085) (by norm_num)
theorem B3805501 : Blo 1502071 3805501 := bbase (se 3 (by rfl) ⟨713531, by rfl⟩ : syracuseStep 3805501 = 1427063) (by norm_num)
theorem B2535853 : Blo 1502071 2535853 := bbase (se 3 (by rfl) ⟨475472, by rfl⟩ : syracuseStep 2535853 = 950945) (by norm_num)
theorem B3805613 : Blo 1502071 3805613 := bbase (se 3 (by rfl) ⟨713552, by rfl⟩ : syracuseStep 3805613 = 1427105) (by norm_num)
theorem B7606709 : Blo 1502071 7606709 := bbase (se 5 (by rfl) ⟨356564, by rfl⟩ : syracuseStep 7606709 = 713129) (by norm_num)
theorem B3379661 : Blo 1502071 3379661 := bbase (se 3 (by rfl) ⟨633686, by rfl⟩ : syracuseStep 3379661 = 1267373) (by norm_num)
theorem B2535941 : Blo 1502071 2535941 := bbase (se 4 (by rfl) ⟨237744, by rfl⟩ : syracuseStep 2535941 = 475489) (by norm_num)
theorem B3379733 : Blo 1502071 3379733 := bbase (se 6 (by rfl) ⟨79212, by rfl⟩ : syracuseStep 3379733 = 158425) (by norm_num)
theorem B3379805 : Blo 1502071 3379805 := bbase (se 3 (by rfl) ⟨633713, by rfl⟩ : syracuseStep 3379805 = 1267427) (by norm_num)
theorem B3805805 : Blo 1502071 3805805 := bbase (se 3 (by rfl) ⟨713588, by rfl⟩ : syracuseStep 3805805 = 1427177) (by norm_num)
theorem B2536069 : Blo 1502071 2536069 := bbase (se 4 (by rfl) ⟨237756, by rfl⟩ : syracuseStep 2536069 = 475513) (by norm_num)
theorem B3379877 : Blo 1502071 3379877 := bbase (se 4 (by rfl) ⟨316863, by rfl⟩ : syracuseStep 3379877 = 633727) (by norm_num)
theorem B2536157 : Blo 1502071 2536157 := bbase (se 3 (by rfl) ⟨475529, by rfl⟩ : syracuseStep 2536157 = 951059) (by norm_num)
theorem B3379949 : Blo 1502071 3379949 := bbase (se 3 (by rfl) ⟨633740, by rfl⟩ : syracuseStep 3379949 = 1267481) (by norm_num)
theorem B3380021 : Blo 1502071 3380021 := bbase (se 5 (by rfl) ⟨158438, by rfl⟩ : syracuseStep 3380021 = 316877) (by norm_num)
theorem B2536285 : Blo 1502071 2536285 := bbase (se 3 (by rfl) ⟨475553, by rfl⟩ : syracuseStep 2536285 = 951107) (by norm_num)
theorem B3380093 : Blo 1502071 3380093 := bbase (se 3 (by rfl) ⟨633767, by rfl⟩ : syracuseStep 3380093 = 1267535) (by norm_num)
theorem B2536373 : Blo 1502071 2536373 := bbase (se 5 (by rfl) ⟨118892, by rfl⟩ : syracuseStep 2536373 = 237785) (by norm_num)
theorem B3380165 : Blo 1502071 3380165 := bbase (se 4 (by rfl) ⟨316890, by rfl⟩ : syracuseStep 3380165 = 633781) (by norm_num)
theorem B4281349 : Blo 1502071 4281349 := bbase (se 4 (by rfl) ⟨401376, by rfl⟩ : syracuseStep 4281349 = 802753) (by norm_num)
theorem B3380237 : Blo 1502071 3380237 := bbase (se 3 (by rfl) ⟨633794, by rfl⟩ : syracuseStep 3380237 = 1267589) (by norm_num)
theorem B2536501 : Blo 1502071 2536501 := bbase (se 5 (by rfl) ⟨118898, by rfl⟩ : syracuseStep 2536501 = 237797) (by norm_num)
theorem B3208261 : Blo 1502071 3208261 := bbase (se 4 (by rfl) ⟨300774, by rfl⟩ : syracuseStep 3208261 = 601549) (by norm_num)
theorem B3380309 : Blo 1502071 3380309 := bbase (se 8 (by rfl) ⟨19806, by rfl⟩ : syracuseStep 3380309 = 39613) (by norm_num)
theorem B4568197 : Blo 1502071 4568197 := bbase (se 4 (by rfl) ⟨428268, by rfl⟩ : syracuseStep 4568197 = 856537) (by norm_num)
theorem B2536589 : Blo 1502071 2536589 := bbase (se 3 (by rfl) ⟨475610, by rfl⟩ : syracuseStep 2536589 = 951221) (by norm_num)
theorem B3380381 : Blo 1502071 3380381 := bbase (se 3 (by rfl) ⟨633821, by rfl⟩ : syracuseStep 3380381 = 1267643) (by norm_num)
theorem B1627333 : Blo 1502071 1627333 := bbase (se 4 (by rfl) ⟨152562, by rfl⟩ : syracuseStep 1627333 = 305125) (by norm_num)
theorem B3380453 : Blo 1502071 3380453 := bbase (se 4 (by rfl) ⟨316917, by rfl⟩ : syracuseStep 3380453 = 633835) (by norm_num)
theorem B2536717 : Blo 1502071 2536717 := bbase (se 3 (by rfl) ⟨475634, by rfl⟩ : syracuseStep 2536717 = 951269) (by norm_num)
theorem B3380525 : Blo 1502071 3380525 := bbase (se 3 (by rfl) ⟨633848, by rfl⟩ : syracuseStep 3380525 = 1267697) (by norm_num)
theorem B2536805 : Blo 1502071 2536805 := bbase (se 4 (by rfl) ⟨237825, by rfl⟩ : syracuseStep 2536805 = 475651) (by norm_num)
theorem B3380597 : Blo 1502071 3380597 := bbase (se 5 (by rfl) ⟨158465, by rfl⟩ : syracuseStep 3380597 = 316931) (by norm_num)
theorem B3380669 : Blo 1502071 3380669 := bbase (se 3 (by rfl) ⟨633875, by rfl⟩ : syracuseStep 3380669 = 1267751) (by norm_num)
theorem B5707205 : Blo 1502071 5707205 := bbase (se 4 (by rfl) ⟨535050, by rfl⟩ : syracuseStep 5707205 = 1070101) (by norm_num)
theorem B2536933 : Blo 1502071 2536933 := bbase (se 4 (by rfl) ⟨237837, by rfl⟩ : syracuseStep 2536933 = 475675) (by norm_num)
theorem B3380741 : Blo 1502071 3380741 := bbase (se 4 (by rfl) ⟨316944, by rfl⟩ : syracuseStep 3380741 = 633889) (by norm_num)
theorem B2537021 : Blo 1502071 2537021 := bbase (se 3 (by rfl) ⟨475691, by rfl⟩ : syracuseStep 2537021 = 951383) (by norm_num)
theorem B3380813 : Blo 1502071 3380813 := bbase (se 3 (by rfl) ⟨633902, by rfl⟩ : syracuseStep 3380813 = 1267805) (by norm_num)
theorem B3380885 : Blo 1502071 3380885 := bbase (se 6 (by rfl) ⟨79239, by rfl⟩ : syracuseStep 3380885 = 158479) (by norm_num)
theorem B2537149 : Blo 1502071 2537149 := bbase (se 3 (by rfl) ⟨475715, by rfl⟩ : syracuseStep 2537149 = 951431) (by norm_num)
theorem B7608005 : Blo 1502071 7608005 := bbase (se 4 (by rfl) ⟨713250, by rfl⟩ : syracuseStep 7608005 = 1426501) (by norm_num)
theorem B3380957 : Blo 1502071 3380957 := bbase (se 3 (by rfl) ⟨633929, by rfl⟩ : syracuseStep 3380957 = 1267859) (by norm_num)
theorem B5707493 : Blo 1502071 5707493 := bbase (se 4 (by rfl) ⟨535077, by rfl⟩ : syracuseStep 5707493 = 1070155) (by norm_num)
theorem B2537237 : Blo 1502071 2537237 := bbase (se 6 (by rfl) ⟨59466, by rfl⟩ : syracuseStep 2537237 = 118933) (by norm_num)
theorem B3381029 : Blo 1502071 3381029 := bbase (se 4 (by rfl) ⟨316971, by rfl⟩ : syracuseStep 3381029 = 633943) (by norm_num)
theorem B3381101 : Blo 1502071 3381101 := bbase (se 3 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 3381101 = 1267913) (by norm_num)
theorem B3045277 : Blo 1502071 3045277 := bbase (se 3 (by rfl) ⟨570989, by rfl⟩ : syracuseStep 3045277 = 1141979) (by norm_num)
theorem B3381173 : Blo 1502071 3381173 := bbase (se 5 (by rfl) ⟨158492, by rfl⟩ : syracuseStep 3381173 = 316985) (by norm_num)
theorem B3209149 : Blo 1502071 3209149 := bbase (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) (by norm_num)
theorem B2316269 : Blo 1502071 2316269 := bbase (se 3 (by rfl) ⟨434300, by rfl⟩ : syracuseStep 2316269 = 868601) (by norm_num)
theorem B3381245 : Blo 1502071 3381245 := bbase (se 3 (by rfl) ⟨633983, by rfl⟩ : syracuseStep 3381245 = 1267967) (by norm_num)
theorem B6420485 : Blo 1502071 6420485 := bbase (se 4 (by rfl) ⟨601920, by rfl⟩ : syracuseStep 6420485 = 1203841) (by norm_num)
theorem B3610669 : Blo 1502071 3610669 := bbase (se 3 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 3610669 = 1354001) (by norm_num)
theorem B2439229 : Blo 1502071 2439229 := bbase (se 3 (by rfl) ⟨457355, by rfl⟩ : syracuseStep 2439229 = 914711) (by norm_num)
theorem B3381317 : Blo 1502071 3381317 := bbase (se 4 (by rfl) ⟨316998, by rfl⟩ : syracuseStep 3381317 = 633997) (by norm_num)
theorem B1980493 : Blo 1502071 1980493 := bbase (se 3 (by rfl) ⟨371342, by rfl⟩ : syracuseStep 1980493 = 742685) (by norm_num)
theorem B9140309 : Blo 1502071 9140309 := bbase (se 8 (by rfl) ⟨53556, by rfl⟩ : syracuseStep 9140309 = 107113) (by norm_num)
theorem B3381389 : Blo 1502071 3381389 := bbase (se 3 (by rfl) ⟨634010, by rfl⟩ : syracuseStep 3381389 = 1268021) (by norm_num)
theorem B12843157 : Blo 1502071 12843157 := bbase (se 6 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 12843157 = 602023) (by norm_num)
theorem B2406581 : Blo 1502071 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B3381461 : Blo 1502071 3381461 := bbase (se 7 (by rfl) ⟨39626, by rfl⟩ : syracuseStep 3381461 = 79253) (by norm_num)
theorem B3381533 : Blo 1502071 3381533 := bbase (se 3 (by rfl) ⟨634037, by rfl⟩ : syracuseStep 3381533 = 1268075) (by norm_num)
theorem B3381605 : Blo 1502071 3381605 := bbase (se 4 (by rfl) ⟨317025, by rfl⟩ : syracuseStep 3381605 = 634051) (by norm_num)
theorem B2406773 : Blo 1502071 2406773 := bbase (se 5 (by rfl) ⟨112817, by rfl⟩ : syracuseStep 2406773 = 225635) (by norm_num)
theorem B3209645 : Blo 1502071 3209645 := bbase (se 3 (by rfl) ⟨601808, by rfl⟩ : syracuseStep 3209645 = 1203617) (by norm_num)
theorem B3381677 : Blo 1502071 3381677 := bbase (se 3 (by rfl) ⟨634064, by rfl⟩ : syracuseStep 3381677 = 1268129) (by norm_num)
theorem B5143013 : Blo 1502071 5143013 := bbase (se 4 (by rfl) ⟨482157, by rfl⟩ : syracuseStep 5143013 = 964315) (by norm_num)
theorem B2439661 : Blo 1502071 2439661 := bbase (se 3 (by rfl) ⟨457436, by rfl⟩ : syracuseStep 2439661 = 914873) (by norm_num)
theorem B3381749 : Blo 1502071 3381749 := bbase (se 5 (by rfl) ⟨158519, by rfl⟩ : syracuseStep 3381749 = 317039) (by norm_num)
theorem B3045893 : Blo 1502071 3045893 := bbase (se 4 (by rfl) ⟨285552, by rfl⟩ : syracuseStep 3045893 = 571105) (by norm_num)
theorem B3381821 : Blo 1502071 3381821 := bbase (se 3 (by rfl) ⟨634091, by rfl⟩ : syracuseStep 3381821 = 1268183) (by norm_num)
theorem B1604161 : Blo 1502071 1604161 := bbase (se 2 (by rfl) ⟨601560, by rfl⟩ : syracuseStep 1604161 = 1203121) (by norm_num)
theorem B3086957 : Blo 1502071 3086957 := bbase (se 3 (by rfl) ⟨578804, by rfl⟩ : syracuseStep 3086957 = 1157609) (by norm_num)
theorem B3381893 : Blo 1502071 3381893 := bbase (se 4 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 3381893 = 634105) (by norm_num)
theorem B1604233 : Blo 1502071 1604233 := bbase (se 2 (by rfl) ⟨601587, by rfl⟩ : syracuseStep 1604233 = 1203175) (by norm_num)
theorem B8125109 : Blo 1502071 8125109 := bbase (se 5 (by rfl) ⟨380864, by rfl⟩ : syracuseStep 8125109 = 761729) (by norm_num)
theorem B2570933 : Blo 1502071 2570933 := bbase (se 5 (by rfl) ⟨120512, by rfl⟩ : syracuseStep 2570933 = 241025) (by norm_num)
theorem B3381965 : Blo 1502071 3381965 := bbase (se 3 (by rfl) ⟨634118, by rfl⟩ : syracuseStep 3381965 = 1268237) (by norm_num)
theorem B8674037 : Blo 1502071 8674037 := bbase (se 5 (by rfl) ⟨406595, by rfl⟩ : syracuseStep 8674037 = 813191) (by norm_num)
theorem B5069573 : Blo 1502071 5069573 := bbase (se 4 (by rfl) ⟨475272, by rfl⟩ : syracuseStep 5069573 = 950545) (by norm_num)
theorem B3382037 : Blo 1502071 3382037 := bbase (se 6 (by rfl) ⟨79266, by rfl⟩ : syracuseStep 3382037 = 158533) (by norm_num)
theorem B3382109 : Blo 1502071 3382109 := bbase (se 3 (by rfl) ⟨634145, by rfl⟩ : syracuseStep 3382109 = 1268291) (by norm_num)
theorem B5708677 : Blo 1502071 5708677 := bbase (se 4 (by rfl) ⟨535188, by rfl⟩ : syracuseStep 5708677 = 1070377) (by norm_num)
theorem B2284445 : Blo 1502071 2284445 := bbase (se 3 (by rfl) ⟨428333, by rfl⟩ : syracuseStep 2284445 = 856667) (by norm_num)
theorem B3382181 : Blo 1502071 3382181 := bbase (se 4 (by rfl) ⟨317079, by rfl⟩ : syracuseStep 3382181 = 634159) (by norm_num)
theorem B3046349 : Blo 1502071 3046349 := bbase (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) (by norm_num)
theorem B3521485 : Blo 1502071 3521485 := bbase (se 3 (by rfl) ⟨660278, by rfl⟩ : syracuseStep 3521485 = 1320557) (by norm_num)
theorem B7609301 : Blo 1502071 7609301 := bbase (se 7 (by rfl) ⟨89171, by rfl⟩ : syracuseStep 7609301 = 178343) (by norm_num)
theorem B3611621 : Blo 1502071 3611621 := bbase (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) (by norm_num)
theorem B6421477 : Blo 1502071 6421477 := bbase (se 4 (by rfl) ⟨602013, by rfl⟩ : syracuseStep 6421477 = 1204027) (by norm_num)
theorem B3382253 : Blo 1502071 3382253 := bbase (se 3 (by rfl) ⟨634172, by rfl⟩ : syracuseStep 3382253 = 1268345) (by norm_num)
theorem B1604605 : Blo 1502071 1604605 := bbase (se 3 (by rfl) ⟨300863, by rfl⟩ : syracuseStep 1604605 = 601727) (by norm_num)
theorem B4815877 : Blo 1502071 4815877 := bbase (se 4 (by rfl) ⟨451488, by rfl⟩ : syracuseStep 4815877 = 902977) (by norm_num)
theorem B3611677 : Blo 1502071 3611677 := bbase (se 3 (by rfl) ⟨677189, by rfl⟩ : syracuseStep 3611677 = 1354379) (by norm_num)
theorem B3382325 : Blo 1502071 3382325 := bbase (se 5 (by rfl) ⟨158546, by rfl⟩ : syracuseStep 3382325 = 317093) (by norm_num)
theorem B6855797 : Blo 1502071 6855797 := bbase (se 5 (by rfl) ⟨321365, by rfl⟩ : syracuseStep 6855797 = 642731) (by norm_num)
theorem B3382397 : Blo 1502071 3382397 := bbase (se 3 (by rfl) ⟨634199, by rfl⟩ : syracuseStep 3382397 = 1268399) (by norm_num)
theorem B5070005 : Blo 1502071 5070005 := bbase (se 5 (by rfl) ⟨237656, by rfl⟩ : syracuseStep 5070005 = 475313) (by norm_num)
theorem B3382469 : Blo 1502071 3382469 := bbase (se 4 (by rfl) ⟨317106, by rfl⟩ : syracuseStep 3382469 = 634213) (by norm_num)
theorem B3210509 : Blo 1502071 3210509 := bbase (se 3 (by rfl) ⟨601970, by rfl⟩ : syracuseStep 3210509 = 1203941) (by norm_num)
theorem B3382541 : Blo 1502071 3382541 := bbase (se 3 (by rfl) ⟨634226, by rfl⟩ : syracuseStep 3382541 = 1268453) (by norm_num)
theorem B3382613 : Blo 1502071 3382613 := bbase (se 11 (by rfl) ⟨2477, by rfl⟩ : syracuseStep 3382613 = 4955) (by norm_num)
theorem B1604981 : Blo 1502071 1604981 := bbase (se 5 (by rfl) ⟨75233, by rfl⟩ : syracuseStep 1604981 = 150467) (by norm_num)
theorem B3612053 : Blo 1502071 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B3210653 : Blo 1502071 3210653 := bbase (se 3 (by rfl) ⟨601997, by rfl⟩ : syracuseStep 3210653 = 1203995) (by norm_num)
theorem B3382685 : Blo 1502071 3382685 := bbase (se 3 (by rfl) ⟨634253, by rfl⟩ : syracuseStep 3382685 = 1268507) (by norm_num)
theorem B1605053 : Blo 1502071 1605053 := bbase (se 3 (by rfl) ⟨300947, by rfl⟩ : syracuseStep 1605053 = 601895) (by norm_num)
theorem B2285005 : Blo 1502071 2285005 := bbase (se 3 (by rfl) ⟨428438, by rfl⟩ : syracuseStep 2285005 = 856877) (by norm_num)
theorem B3382757 : Blo 1502071 3382757 := bbase (se 4 (by rfl) ⟨317133, by rfl⟩ : syracuseStep 3382757 = 634267) (by norm_num)
theorem B3382829 : Blo 1502071 3382829 := bbase (se 3 (by rfl) ⟨634280, by rfl⟩ : syracuseStep 3382829 = 1268561) (by norm_num)
theorem B5209685 : Blo 1502071 5209685 := bbase (se 8 (by rfl) ⟨30525, by rfl⟩ : syracuseStep 5209685 = 61051) (by norm_num)
theorem B5070437 : Blo 1502071 5070437 := bbase (se 4 (by rfl) ⟨475353, by rfl⟩ : syracuseStep 5070437 = 950707) (by norm_num)
theorem B3382901 : Blo 1502071 3382901 := bbase (se 5 (by rfl) ⟨158573, by rfl⟩ : syracuseStep 3382901 = 317147) (by norm_num)
theorem B1605241 : Blo 1502071 1605241 := bbase (se 2 (by rfl) ⟨601965, by rfl⟩ : syracuseStep 1605241 = 1203931) (by norm_num)
theorem B3612293 : Blo 1502071 3612293 := bbase (se 4 (by rfl) ⟨338652, by rfl⟩ : syracuseStep 3612293 = 677305) (by norm_num)
theorem B4062869 : Blo 1502071 4062869 := bbase (se 6 (by rfl) ⟨95223, by rfl⟩ : syracuseStep 4062869 = 190447) (by norm_num)
theorem B4570789 : Blo 1502071 4570789 := bbase (se 4 (by rfl) ⟨428511, by rfl⟩ : syracuseStep 4570789 = 857023) (by norm_num)
theorem B1523381 : Blo 1502071 1523381 := bbase (se 5 (by rfl) ⟨71408, by rfl⟩ : syracuseStep 1523381 = 142817) (by norm_num)
theorem B3382973 : Blo 1502071 3382973 := bbase (se 3 (by rfl) ⟨634307, by rfl⟩ : syracuseStep 3382973 = 1268615) (by norm_num)
theorem B2408221 : Blo 1502071 2408221 := bbase (se 3 (by rfl) ⟨451541, by rfl⟩ : syracuseStep 2408221 = 903083) (by norm_num)
theorem B1605425 : Blo 1502071 1605425 := bbase (se 2 (by rfl) ⟨602034, by rfl⟩ : syracuseStep 1605425 = 1204069) (by norm_num)
theorem B4570933 : Blo 1502071 4570933 := bbase (se 5 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 4570933 = 428525) (by norm_num)
theorem B2891621 : Blo 1502071 2891621 := bbase (se 4 (by rfl) ⟨271089, by rfl⟩ : syracuseStep 2891621 = 542179) (by norm_num)
theorem B9633653 : Blo 1502071 9633653 := bbase (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) (by norm_num)
theorem B4398997 : Blo 1502071 4398997 := bbase (se 6 (by rfl) ⟨103101, by rfl⟩ : syracuseStep 4398997 = 206203) (by norm_num)
theorem B3129293 : Blo 1502071 3129293 := bbase (se 3 (by rfl) ⟨586742, by rfl⟩ : syracuseStep 3129293 = 1173485) (by norm_num)
theorem B17121293 : Blo 1502071 17121293 := bstep (se 3 (by rfl) ⟨3210242, by rfl⟩ : syracuseStep 17121293 = 6420485) B6420485
theorem B32489525 : Blo 1502071 32489525 := bstep (se 5 (by rfl) ⟨1522946, by rfl⟩ : syracuseStep 32489525 = 3045893) B3045893
theorem B3252305 : Blo 1502071 3252305 := bstep (se 2 (by rfl) ⟨1219614, by rfl⟩ : syracuseStep 3252305 = 2439229) B2439229
theorem B4063441 : Blo 1502071 4063441 := bstep (se 2 (by rfl) ⟨1523790, by rfl⟩ : syracuseStep 4063441 = 3047581) B3047581
theorem B5071085 : Blo 1502071 5071085 := bstep (se 3 (by rfl) ⟨950828, by rfl⟩ : syracuseStep 5071085 = 1901657) B1901657
theorem B5071139 : Blo 1502071 5071139 := bstep (se 1 (by rfl) ⟨3803354, by rfl⟩ : syracuseStep 5071139 = 7606709) B7606709
theorem B2253107 : Blo 1502071 2253107 := bstep (se 1 (by rfl) ⟨1689830, by rfl⟩ : syracuseStep 2253107 = 3379661) B3379661
theorem B2253137 : Blo 1502071 2253137 := bstep (se 2 (by rfl) ⟨844926, by rfl⟩ : syracuseStep 2253137 = 1689853) B1689853
theorem B2253155 : Blo 1502071 2253155 := bstep (se 1 (by rfl) ⟨1689866, by rfl⟩ : syracuseStep 2253155 = 3379733) B3379733
theorem B2253185 : Blo 1502071 2253185 := bstep (se 2 (by rfl) ⟨844944, by rfl⟩ : syracuseStep 2253185 = 1689889) B1689889
theorem B2253203 : Blo 1502071 2253203 := bstep (se 1 (by rfl) ⟨1689902, by rfl⟩ : syracuseStep 2253203 = 3379805) B3379805
theorem B2253233 : Blo 1502071 2253233 := bstep (se 2 (by rfl) ⟨844962, by rfl⟩ : syracuseStep 2253233 = 1689925) B1689925
theorem B19792309 : Blo 1502071 19792309 := bstep (se 5 (by rfl) ⟨927764, by rfl⟩ : syracuseStep 19792309 = 1855529) B1855529
theorem B2253251 : Blo 1502071 2253251 := bstep (se 1 (by rfl) ⟨1689938, by rfl⟩ : syracuseStep 2253251 = 3379877) B3379877
theorem B2032067 : Blo 1502071 2032067 := bstep (se 1 (by rfl) ⟨1524050, by rfl⟩ : syracuseStep 2032067 = 3048101) B3048101
theorem B2253281 : Blo 1502071 2253281 := bstep (se 2 (by rfl) ⟨844980, by rfl⟩ : syracuseStep 2253281 = 1689961) B1689961
theorem B2253299 : Blo 1502071 2253299 := bstep (se 1 (by rfl) ⟨1689974, by rfl⟩ : syracuseStep 2253299 = 3379949) B3379949
theorem B2253329 : Blo 1502071 2253329 := bstep (se 2 (by rfl) ⟨844998, by rfl⟩ : syracuseStep 2253329 = 1689997) B1689997
theorem B2253347 : Blo 1502071 2253347 := bstep (se 1 (by rfl) ⟨1690010, by rfl⟩ : syracuseStep 2253347 = 3380021) B3380021
theorem B5071409 : Blo 1502071 5071409 := bstep (se 2 (by rfl) ⟨1901778, by rfl⟩ : syracuseStep 5071409 = 3803557) B3803557
theorem B2253377 : Blo 1502071 2253377 := bstep (se 2 (by rfl) ⟨845016, by rfl⟩ : syracuseStep 2253377 = 1690033) B1690033
theorem B2253395 : Blo 1502071 2253395 := bstep (se 1 (by rfl) ⟨1690046, by rfl⟩ : syracuseStep 2253395 = 3380093) B3380093
theorem B2253425 : Blo 1502071 2253425 := bstep (se 2 (by rfl) ⟨845034, by rfl⟩ : syracuseStep 2253425 = 1690069) B1690069
theorem B1901171 : Blo 1502071 1901171 := bstep (se 1 (by rfl) ⟨1425878, by rfl⟩ : syracuseStep 1901171 = 2851757) B2851757
theorem B2253443 : Blo 1502071 2253443 := bstep (se 1 (by rfl) ⟨1690082, by rfl⟩ : syracuseStep 2253443 = 3380165) B3380165
theorem B8561285 : Blo 1502071 8561285 := bstep (se 4 (by rfl) ⟨802620, by rfl⟩ : syracuseStep 8561285 = 1605241) B1605241
theorem B2253473 : Blo 1502071 2253473 := bstep (se 2 (by rfl) ⟨845052, by rfl⟩ : syracuseStep 2253473 = 1690105) B1690105
theorem B2253491 : Blo 1502071 2253491 := bstep (se 1 (by rfl) ⟨1690118, by rfl⟩ : syracuseStep 2253491 = 3380237) B3380237
theorem B2253521 : Blo 1502071 2253521 := bstep (se 2 (by rfl) ⟨845070, by rfl⟩ : syracuseStep 2253521 = 1690141) B1690141
theorem B2253539 : Blo 1502071 2253539 := bstep (se 1 (by rfl) ⟨1690154, by rfl⟩ : syracuseStep 2253539 = 3380309) B3380309
theorem B2138881 : Blo 1502071 2138881 := bstep (se 2 (by rfl) ⟨802080, by rfl⟩ : syracuseStep 2138881 = 1604161) B1604161
theorem B2253569 : Blo 1502071 2253569 := bstep (se 2 (by rfl) ⟨845088, by rfl⟩ : syracuseStep 2253569 = 1690177) B1690177
theorem B4064003 : Blo 1502071 4064003 := bstep (se 1 (by rfl) ⟨3048002, by rfl⟩ : syracuseStep 4064003 = 6096005) B6096005
theorem B2253587 : Blo 1502071 2253587 := bstep (se 1 (by rfl) ⟨1690190, by rfl⟩ : syracuseStep 2253587 = 3380381) B3380381
theorem B5014307 : Blo 1502071 5014307 := bstep (se 1 (by rfl) ⟨3760730, by rfl⟩ : syracuseStep 5014307 = 7521461) B7521461
theorem B2253617 : Blo 1502071 2253617 := bstep (se 2 (by rfl) ⟨845106, by rfl⟩ : syracuseStep 2253617 = 1690213) B1690213
theorem B2253635 : Blo 1502071 2253635 := bstep (se 1 (by rfl) ⟨1690226, by rfl⟩ : syracuseStep 2253635 = 3380453) B3380453
theorem B2138977 : Blo 1502071 2138977 := bstep (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) B1604233
theorem B2253665 : Blo 1502071 2253665 := bstep (se 2 (by rfl) ⟨845124, by rfl⟩ : syracuseStep 2253665 = 1690249) B1690249
theorem B2253683 : Blo 1502071 2253683 := bstep (se 1 (by rfl) ⟨1690262, by rfl⟩ : syracuseStep 2253683 = 3380525) B3380525
theorem B2253713 : Blo 1502071 2253713 := bstep (se 2 (by rfl) ⟨845142, by rfl⟩ : syracuseStep 2253713 = 1690285) B1690285
theorem B2253731 : Blo 1502071 2253731 := bstep (se 1 (by rfl) ⟨1690298, by rfl⟩ : syracuseStep 2253731 = 3380597) B3380597
theorem B2253761 : Blo 1502071 2253761 := bstep (se 2 (by rfl) ⟨845160, by rfl⟩ : syracuseStep 2253761 = 1690321) B1690321
theorem B2253779 : Blo 1502071 2253779 := bstep (se 1 (by rfl) ⟨1690334, by rfl⟩ : syracuseStep 2253779 = 3380669) B3380669
theorem B2253809 : Blo 1502071 2253809 := bstep (se 2 (by rfl) ⟨845178, by rfl⟩ : syracuseStep 2253809 = 1690357) B1690357
theorem B2253827 : Blo 1502071 2253827 := bstep (se 1 (by rfl) ⟨1690370, by rfl⟩ : syracuseStep 2253827 = 3380741) B3380741
theorem B2253857 : Blo 1502071 2253857 := bstep (se 2 (by rfl) ⟨845196, by rfl⟩ : syracuseStep 2253857 = 1690393) B1690393
theorem B2253875 : Blo 1502071 2253875 := bstep (se 1 (by rfl) ⟨1690406, by rfl⟩ : syracuseStep 2253875 = 3380813) B3380813
theorem B5071949 : Blo 1502071 5071949 := bstep (se 3 (by rfl) ⟨950990, by rfl⟩ : syracuseStep 5071949 = 1901981) B1901981
theorem B2253905 : Blo 1502071 2253905 := bstep (se 2 (by rfl) ⟨845214, by rfl⟩ : syracuseStep 2253905 = 1690429) B1690429
theorem B3802211 : Blo 1502071 3802211 := bstep (se 1 (by rfl) ⟨2851658, by rfl⟩ : syracuseStep 3802211 = 5703317) B5703317
theorem B2851939 : Blo 1502071 2851939 := bstep (se 1 (by rfl) ⟨2138954, by rfl⟩ : syracuseStep 2851939 = 4277909) B4277909
theorem B2253923 : Blo 1502071 2253923 := bstep (se 1 (by rfl) ⟨1690442, by rfl⟩ : syracuseStep 2253923 = 3380885) B3380885
theorem B2253953 : Blo 1502071 2253953 := bstep (se 2 (by rfl) ⟨845232, by rfl⟩ : syracuseStep 2253953 = 1690465) B1690465
theorem B5072003 : Blo 1502071 5072003 := bstep (se 1 (by rfl) ⟨3804002, by rfl⟩ : syracuseStep 5072003 = 7608005) B7608005
theorem B2851985 : Blo 1502071 2851985 := bstep (se 2 (by rfl) ⟨1069494, by rfl⟩ : syracuseStep 2851985 = 2138989) B2138989
theorem B2253971 : Blo 1502071 2253971 := bstep (se 1 (by rfl) ⟨1690478, by rfl⟩ : syracuseStep 2253971 = 3380957) B3380957
theorem B2254001 : Blo 1502071 2254001 := bstep (se 2 (by rfl) ⟨845250, by rfl⟩ : syracuseStep 2254001 = 1690501) B1690501
theorem B7611569 : Blo 1502071 7611569 := bstep (se 2 (by rfl) ⟨2854338, by rfl⟩ : syracuseStep 7611569 = 5708677) B5708677
theorem B2254019 : Blo 1502071 2254019 := bstep (se 1 (by rfl) ⟨1690514, by rfl⟩ : syracuseStep 2254019 = 3381029) B3381029
theorem B2254049 : Blo 1502071 2254049 := bstep (se 2 (by rfl) ⟨845268, by rfl⟩ : syracuseStep 2254049 = 1690537) B1690537
theorem B2254067 : Blo 1502071 2254067 := bstep (se 1 (by rfl) ⟨1690550, by rfl⟩ : syracuseStep 2254067 = 3381101) B3381101
theorem B2254097 : Blo 1502071 2254097 := bstep (se 2 (by rfl) ⟨845286, by rfl⟩ : syracuseStep 2254097 = 1690573) B1690573
theorem B3802403 : Blo 1502071 3802403 := bstep (se 1 (by rfl) ⟨2851802, by rfl⟩ : syracuseStep 3802403 = 5703605) B5703605
theorem B2254115 : Blo 1502071 2254115 := bstep (se 1 (by rfl) ⟨1690586, by rfl⟩ : syracuseStep 2254115 = 3381173) B3381173
theorem B8561969 : Blo 1502071 8561969 := bstep (se 2 (by rfl) ⟨3210738, by rfl⟩ : syracuseStep 8561969 = 6421477) B6421477
theorem B1901875 : Blo 1502071 1901875 := bstep (se 1 (by rfl) ⟨1426406, by rfl⟩ : syracuseStep 1901875 = 2852813) B2852813
theorem B2254145 : Blo 1502071 2254145 := bstep (se 2 (by rfl) ⟨845304, by rfl⟩ : syracuseStep 2254145 = 1690609) B1690609
theorem B2139473 : Blo 1502071 2139473 := bstep (se 2 (by rfl) ⟨802302, by rfl⟩ : syracuseStep 2139473 = 1604605) B1604605
theorem B2254163 : Blo 1502071 2254163 := bstep (se 1 (by rfl) ⟨1690622, by rfl⟩ : syracuseStep 2254163 = 3381245) B3381245
theorem B2254193 : Blo 1502071 2254193 := bstep (se 2 (by rfl) ⟨845322, by rfl⟩ : syracuseStep 2254193 = 1690645) B1690645
theorem B2254211 : Blo 1502071 2254211 := bstep (se 1 (by rfl) ⟨1690658, by rfl⟩ : syracuseStep 2254211 = 3381317) B3381317
theorem B5072273 : Blo 1502071 5072273 := bstep (se 2 (by rfl) ⟨1902102, by rfl⟩ : syracuseStep 5072273 = 3804205) B3804205
theorem B1901971 : Blo 1502071 1901971 := bstep (se 1 (by rfl) ⟨1426478, by rfl⟩ : syracuseStep 1901971 = 2852957) B2852957
theorem B2254241 : Blo 1502071 2254241 := bstep (se 2 (by rfl) ⟨845340, by rfl⟩ : syracuseStep 2254241 = 1690681) B1690681
theorem B4277681 : Blo 1502071 4277681 := bstep (se 2 (by rfl) ⟨1604130, by rfl⟩ : syracuseStep 4277681 = 3208261) B3208261
theorem B2852273 : Blo 1502071 2852273 := bstep (se 2 (by rfl) ⟨1069602, by rfl⟩ : syracuseStep 2852273 = 2139205) B2139205
theorem B2254259 : Blo 1502071 2254259 := bstep (se 1 (by rfl) ⟨1690694, by rfl⟩ : syracuseStep 2254259 = 3381389) B3381389
theorem B2254289 : Blo 1502071 2254289 := bstep (se 2 (by rfl) ⟨845358, by rfl⟩ : syracuseStep 2254289 = 1690717) B1690717
theorem B2254307 : Blo 1502071 2254307 := bstep (se 1 (by rfl) ⟨1690730, by rfl⟩ : syracuseStep 2254307 = 3381461) B3381461
theorem B2254337 : Blo 1502071 2254337 := bstep (se 2 (by rfl) ⟨845376, by rfl⟩ : syracuseStep 2254337 = 1690753) B1690753
theorem B2254355 : Blo 1502071 2254355 := bstep (se 1 (by rfl) ⟨1690766, by rfl⟩ : syracuseStep 2254355 = 3381533) B3381533
theorem B2254385 : Blo 1502071 2254385 := bstep (se 2 (by rfl) ⟨845394, by rfl⟩ : syracuseStep 2254385 = 1690789) B1690789
theorem B2254403 : Blo 1502071 2254403 := bstep (se 1 (by rfl) ⟨1690802, by rfl⟩ : syracuseStep 2254403 = 3381605) B3381605
theorem B2254433 : Blo 1502071 2254433 := bstep (se 2 (by rfl) ⟨845412, by rfl⟩ : syracuseStep 2254433 = 1690825) B1690825
theorem B2254451 : Blo 1502071 2254451 := bstep (se 1 (by rfl) ⟨1690838, by rfl⟩ : syracuseStep 2254451 = 3381677) B3381677
theorem B2254481 : Blo 1502071 2254481 := bstep (se 2 (by rfl) ⟨845430, by rfl⟩ : syracuseStep 2254481 = 1690861) B1690861
theorem B5703331 : Blo 1502071 5703331 := bstep (se 1 (by rfl) ⟨4277498, by rfl⟩ : syracuseStep 5703331 = 8554997) B8554997
theorem B2254499 : Blo 1502071 2254499 := bstep (se 1 (by rfl) ⟨1690874, by rfl⟩ : syracuseStep 2254499 = 3381749) B3381749
theorem B2254529 : Blo 1502071 2254529 := bstep (se 2 (by rfl) ⟨845448, by rfl⟩ : syracuseStep 2254529 = 1690897) B1690897
theorem B2254547 : Blo 1502071 2254547 := bstep (se 1 (by rfl) ⟨1690910, by rfl⟩ : syracuseStep 2254547 = 3381821) B3381821
theorem B2254577 : Blo 1502071 2254577 := bstep (se 2 (by rfl) ⟨845466, by rfl⟩ : syracuseStep 2254577 = 1690933) B1690933
theorem B2057971 : Blo 1502071 2057971 := bstep (se 1 (by rfl) ⟨1543478, by rfl⟩ : syracuseStep 2057971 = 3086957) B3086957
theorem B2254595 : Blo 1502071 2254595 := bstep (se 1 (by rfl) ⟨1690946, by rfl⟩ : syracuseStep 2254595 = 3381893) B3381893
theorem B2254625 : Blo 1502071 2254625 := bstep (se 2 (by rfl) ⟨845484, by rfl⟩ : syracuseStep 2254625 = 1690969) B1690969
theorem B5416739 : Blo 1502071 5416739 := bstep (se 1 (by rfl) ⟨4062554, by rfl⟩ : syracuseStep 5416739 = 8125109) B8125109
theorem B1713955 : Blo 1502071 1713955 := bstep (se 1 (by rfl) ⟨1285466, by rfl⟩ : syracuseStep 1713955 = 2570933) B2570933
theorem B2254643 : Blo 1502071 2254643 := bstep (se 1 (by rfl) ⟨1690982, by rfl⟩ : syracuseStep 2254643 = 3381965) B3381965
theorem B2254673 : Blo 1502071 2254673 := bstep (se 2 (by rfl) ⟨845502, by rfl⟩ : syracuseStep 2254673 = 1691005) B1691005
theorem B2254691 : Blo 1502071 2254691 := bstep (se 1 (by rfl) ⟨1691018, by rfl⟩ : syracuseStep 2254691 = 3382037) B3382037
theorem B2254721 : Blo 1502071 2254721 := bstep (se 2 (by rfl) ⟨845520, by rfl⟩ : syracuseStep 2254721 = 1691041) B1691041
theorem B1902467 : Blo 1502071 1902467 := bstep (se 1 (by rfl) ⟨1426850, by rfl⟩ : syracuseStep 1902467 = 2853701) B2853701
theorem B2254739 : Blo 1502071 2254739 := bstep (se 1 (by rfl) ⟨1691054, by rfl⟩ : syracuseStep 2254739 = 3382109) B3382109
theorem B5072813 : Blo 1502071 5072813 := bstep (se 3 (by rfl) ⟨951152, by rfl⟩ : syracuseStep 5072813 = 1902305) B1902305
theorem B2254769 : Blo 1502071 2254769 := bstep (se 2 (by rfl) ⟨845538, by rfl⟩ : syracuseStep 2254769 = 1691077) B1691077
theorem B2254787 : Blo 1502071 2254787 := bstep (se 1 (by rfl) ⟨1691090, by rfl⟩ : syracuseStep 2254787 = 3382181) B3382181
theorem B2254817 : Blo 1502071 2254817 := bstep (se 2 (by rfl) ⟨845556, by rfl⟩ : syracuseStep 2254817 = 1691113) B1691113
theorem B5072867 : Blo 1502071 5072867 := bstep (se 1 (by rfl) ⟨3804650, by rfl⟩ : syracuseStep 5072867 = 7609301) B7609301
theorem B2254835 : Blo 1502071 2254835 := bstep (se 1 (by rfl) ⟨1691126, by rfl⟩ : syracuseStep 2254835 = 3382253) B3382253
theorem B9627653 : Blo 1502071 9627653 := bstep (se 4 (by rfl) ⟨902592, by rfl⟩ : syracuseStep 9627653 = 1805185) B1805185
theorem B2254865 : Blo 1502071 2254865 := bstep (se 2 (by rfl) ⟨845574, by rfl⟩ : syracuseStep 2254865 = 1691149) B1691149
theorem B2254883 : Blo 1502071 2254883 := bstep (se 1 (by rfl) ⟨1691162, by rfl⟩ : syracuseStep 2254883 = 3382325) B3382325
theorem B2254913 : Blo 1502071 2254913 := bstep (se 2 (by rfl) ⟨845592, by rfl⟩ : syracuseStep 2254913 = 1691185) B1691185
theorem B2254931 : Blo 1502071 2254931 := bstep (se 1 (by rfl) ⟨1691198, by rfl⟩ : syracuseStep 2254931 = 3382397) B3382397
theorem B2254961 : Blo 1502071 2254961 := bstep (se 2 (by rfl) ⟨845610, by rfl⟩ : syracuseStep 2254961 = 1691221) B1691221
theorem B2852995 : Blo 1502071 2852995 := bstep (se 1 (by rfl) ⟨2139746, by rfl⟩ : syracuseStep 2852995 = 4279493) B4279493
theorem B2254979 : Blo 1502071 2254979 := bstep (se 1 (by rfl) ⟨1691234, by rfl⟩ : syracuseStep 2254979 = 3382469) B3382469
theorem B2255009 : Blo 1502071 2255009 := bstep (se 2 (by rfl) ⟨845628, by rfl⟩ : syracuseStep 2255009 = 1691257) B1691257
theorem B3426467 : Blo 1502071 3426467 := bstep (se 1 (by rfl) ⟨2569850, by rfl⟩ : syracuseStep 3426467 = 5139701) B5139701
theorem B2140339 : Blo 1502071 2140339 := bstep (se 1 (by rfl) ⟨1605254, by rfl⟩ : syracuseStep 2140339 = 3210509) B3210509
theorem B2255027 : Blo 1502071 2255027 := bstep (se 1 (by rfl) ⟨1691270, by rfl⟩ : syracuseStep 2255027 = 3382541) B3382541
theorem B3803345 : Blo 1502071 3803345 := bstep (se 2 (by rfl) ⟨1426254, by rfl⟩ : syracuseStep 3803345 = 2852509) B2852509
theorem B2255057 : Blo 1502071 2255057 := bstep (se 2 (by rfl) ⟨845646, by rfl⟩ : syracuseStep 2255057 = 1691293) B1691293
theorem B2255075 : Blo 1502071 2255075 := bstep (se 1 (by rfl) ⟨1691306, by rfl⟩ : syracuseStep 2255075 = 3382613) B3382613
theorem B5073137 : Blo 1502071 5073137 := bstep (se 2 (by rfl) ⟨1902426, by rfl⟩ : syracuseStep 5073137 = 3804853) B3804853
theorem B2255105 : Blo 1502071 2255105 := bstep (se 2 (by rfl) ⟨845664, by rfl⟩ : syracuseStep 2255105 = 1691329) B1691329
theorem B3803395 : Blo 1502071 3803395 := bstep (se 1 (by rfl) ⟨2852546, by rfl⟩ : syracuseStep 3803395 = 5705093) B5705093
theorem B2140435 : Blo 1502071 2140435 := bstep (se 1 (by rfl) ⟨1605326, by rfl⟩ : syracuseStep 2140435 = 3210653) B3210653
theorem B52046101 : Blo 1502071 52046101 := bstep (se 6 (by rfl) ⟨1219830, by rfl⟩ : syracuseStep 52046101 = 2439661) B2439661
theorem B2255123 : Blo 1502071 2255123 := bstep (se 1 (by rfl) ⟨1691342, by rfl⟩ : syracuseStep 2255123 = 3382685) B3382685
theorem B2255153 : Blo 1502071 2255153 := bstep (se 2 (by rfl) ⟨845682, by rfl⟩ : syracuseStep 2255153 = 1691365) B1691365
theorem B1689907 : Blo 1502071 1689907 := bstep (se 1 (by rfl) ⟨1267430, by rfl⟩ : syracuseStep 1689907 = 2534861) B2534861
theorem B2255171 : Blo 1502071 2255171 := bstep (se 1 (by rfl) ⟨1691378, by rfl⟩ : syracuseStep 2255171 = 3382757) B3382757
theorem B17115461 : Blo 1502071 17115461 := bstep (se 4 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 17115461 = 3209149) B3209149
theorem B2255201 : Blo 1502071 2255201 := bstep (se 2 (by rfl) ⟨845700, by rfl⟩ : syracuseStep 2255201 = 1691401) B1691401
theorem B2255219 : Blo 1502071 2255219 := bstep (se 1 (by rfl) ⟨1691414, by rfl⟩ : syracuseStep 2255219 = 3382829) B3382829
theorem B3803537 : Blo 1502071 3803537 := bstep (se 2 (by rfl) ⟨1426326, by rfl⟩ : syracuseStep 3803537 = 2852653) B2852653
theorem B2255249 : Blo 1502071 2255249 := bstep (se 2 (by rfl) ⟨845718, by rfl⟩ : syracuseStep 2255249 = 1691437) B1691437
theorem B2255267 : Blo 1502071 2255267 := bstep (se 1 (by rfl) ⟨1691450, by rfl⟩ : syracuseStep 2255267 = 3382901) B3382901
theorem B2255297 : Blo 1502071 2255297 := bstep (se 2 (by rfl) ⟨845736, by rfl⟩ : syracuseStep 2255297 = 1691473) B1691473
theorem B1690051 : Blo 1502071 1690051 := bstep (se 1 (by rfl) ⟨1267538, by rfl⟩ : syracuseStep 1690051 = 2535077) B2535077
theorem B2255315 : Blo 1502071 2255315 := bstep (se 1 (by rfl) ⟨1691486, by rfl⟩ : syracuseStep 2255315 = 3382973) B3382973
theorem B2255345 : Blo 1502071 2255345 := bstep (se 2 (by rfl) ⟨845754, by rfl⟩ : syracuseStep 2255345 = 1691509) B1691509
theorem B1927747 : Blo 1502071 1927747 := bstep (se 1 (by rfl) ⟨1445810, by rfl⟩ : syracuseStep 1927747 = 2891621) B2891621
theorem B2853443 : Blo 1502071 2853443 := bstep (se 1 (by rfl) ⟨2140082, by rfl⟩ : syracuseStep 2853443 = 4280165) B4280165
theorem B1690195 : Blo 1502071 1690195 := bstep (se 1 (by rfl) ⟨1267646, by rfl⟩ : syracuseStep 1690195 = 2535293) B2535293
theorem B1927891 : Blo 1502071 1927891 := bstep (se 1 (by rfl) ⟨1445918, by rfl⟩ : syracuseStep 1927891 = 2891837) B2891837
theorem B1690339 : Blo 1502071 1690339 := bstep (se 1 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 1690339 = 2535509) B2535509
theorem B6417137 : Blo 1502071 6417137 := bstep (se 2 (by rfl) ⟨2406426, by rfl⟩ : syracuseStep 6417137 = 4812853) B4812853
theorem B5073677 : Blo 1502071 5073677 := bstep (se 3 (by rfl) ⟨951314, by rfl⟩ : syracuseStep 5073677 = 1902629) B1902629
theorem B5073731 : Blo 1502071 5073731 := bstep (se 1 (by rfl) ⟨3805298, by rfl⟩ : syracuseStep 5073731 = 7610597) B7610597
theorem B4279139 : Blo 1502071 4279139 := bstep (se 1 (by rfl) ⟨3209354, by rfl⟩ : syracuseStep 4279139 = 6418709) B6418709
theorem B2853731 : Blo 1502071 2853731 := bstep (se 1 (by rfl) ⟨2140298, by rfl⟩ : syracuseStep 2853731 = 4280597) B4280597
theorem B17124209 : Blo 1502071 17124209 := bstep (se 2 (by rfl) ⟨6421578, by rfl⟩ : syracuseStep 17124209 = 12843157) B12843157
theorem B1690483 : Blo 1502071 1690483 := bstep (se 1 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 1690483 = 2535725) B2535725
theorem B1502083 : Blo 1502071 1502083 := bstep (se 1 (by rfl) ⟨1126562, by rfl⟩ : syracuseStep 1502083 = 2253125) B2253125
theorem B1502099 : Blo 1502071 1502099 := bstep (se 1 (by rfl) ⟨1126574, by rfl⟩ : syracuseStep 1502099 = 2253149) B2253149
theorem B1502115 : Blo 1502071 1502115 := bstep (se 1 (by rfl) ⟨1126586, by rfl⟩ : syracuseStep 1502115 = 2253173) B2253173
theorem B1502131 : Blo 1502071 1502131 := bstep (se 1 (by rfl) ⟨1126598, by rfl⟩ : syracuseStep 1502131 = 2253197) B2253197
theorem B1502147 : Blo 1502071 1502147 := bstep (se 1 (by rfl) ⟨1126610, by rfl⟩ : syracuseStep 1502147 = 2253221) B2253221
theorem B1502163 : Blo 1502071 1502163 := bstep (se 1 (by rfl) ⟨1126622, by rfl⟩ : syracuseStep 1502163 = 2253245) B2253245
theorem B1502179 : Blo 1502071 1502179 := bstep (se 1 (by rfl) ⟨1126634, by rfl⟩ : syracuseStep 1502179 = 2253269) B2253269
theorem B1502195 : Blo 1502071 1502195 := bstep (se 1 (by rfl) ⟨1126646, by rfl⟩ : syracuseStep 1502195 = 2253293) B2253293
theorem B1502211 : Blo 1502071 1502211 := bstep (se 1 (by rfl) ⟨1126658, by rfl⟩ : syracuseStep 1502211 = 2253317) B2253317
theorem B1690627 : Blo 1502071 1690627 := bstep (se 1 (by rfl) ⟨1267970, by rfl⟩ : syracuseStep 1690627 = 2535941) B2535941
theorem B1502227 : Blo 1502071 1502227 := bstep (se 1 (by rfl) ⟨1126670, by rfl⟩ : syracuseStep 1502227 = 2253341) B2253341
theorem B1502243 : Blo 1502071 1502243 := bstep (se 1 (by rfl) ⟨1126682, by rfl⟩ : syracuseStep 1502243 = 2253365) B2253365
theorem B1502259 : Blo 1502071 1502259 := bstep (se 1 (by rfl) ⟨1126694, by rfl⟩ : syracuseStep 1502259 = 2253389) B2253389
theorem B1502275 : Blo 1502071 1502275 := bstep (se 1 (by rfl) ⟨1126706, by rfl⟩ : syracuseStep 1502275 = 2253413) B2253413
theorem B5074001 : Blo 1502071 5074001 := bstep (se 2 (by rfl) ⟨1902750, by rfl⟩ : syracuseStep 5074001 = 3805501) B3805501
theorem B1502291 : Blo 1502071 1502291 := bstep (se 1 (by rfl) ⟨1126718, by rfl⟩ : syracuseStep 1502291 = 2253437) B2253437
theorem B1502307 : Blo 1502071 1502307 := bstep (se 1 (by rfl) ⟨1126730, by rfl⟩ : syracuseStep 1502307 = 2253461) B2253461
theorem B1502323 : Blo 1502071 1502323 := bstep (se 1 (by rfl) ⟨1126742, by rfl⟩ : syracuseStep 1502323 = 2253485) B2253485
theorem B1502339 : Blo 1502071 1502339 := bstep (se 1 (by rfl) ⟨1126754, by rfl⟩ : syracuseStep 1502339 = 2253509) B2253509
theorem B1502355 : Blo 1502071 1502355 := bstep (se 1 (by rfl) ⟨1126766, by rfl⟩ : syracuseStep 1502355 = 2253533) B2253533
theorem B1690771 : Blo 1502071 1690771 := bstep (se 1 (by rfl) ⟨1268078, by rfl⟩ : syracuseStep 1690771 = 2536157) B2536157
theorem B1502371 : Blo 1502071 1502371 := bstep (se 1 (by rfl) ⟨1126778, by rfl⟩ : syracuseStep 1502371 = 2253557) B2253557
theorem B1502387 : Blo 1502071 1502387 := bstep (se 1 (by rfl) ⟨1126790, by rfl⟩ : syracuseStep 1502387 = 2253581) B2253581
theorem B1502403 : Blo 1502071 1502403 := bstep (se 1 (by rfl) ⟨1126802, by rfl⟩ : syracuseStep 1502403 = 2253605) B2253605
theorem B1502419 : Blo 1502071 1502419 := bstep (se 1 (by rfl) ⟨1126814, by rfl⟩ : syracuseStep 1502419 = 2253629) B2253629
theorem B1502435 : Blo 1502071 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B1502451 : Blo 1502071 1502451 := bstep (se 1 (by rfl) ⟨1126838, by rfl⟩ : syracuseStep 1502451 = 2253677) B2253677
theorem B1502467 : Blo 1502071 1502467 := bstep (se 1 (by rfl) ⟨1126850, by rfl⟩ : syracuseStep 1502467 = 2253701) B2253701
theorem B1502483 : Blo 1502071 1502483 := bstep (se 1 (by rfl) ⟨1126862, by rfl⟩ : syracuseStep 1502483 = 2253725) B2253725
theorem B1502499 : Blo 1502071 1502499 := bstep (se 1 (by rfl) ⟨1126874, by rfl⟩ : syracuseStep 1502499 = 2253749) B2253749
theorem B1690915 : Blo 1502071 1690915 := bstep (se 1 (by rfl) ⟨1268186, by rfl⟩ : syracuseStep 1690915 = 2536373) B2536373
theorem B1502515 : Blo 1502071 1502515 := bstep (se 1 (by rfl) ⟨1126886, by rfl⟩ : syracuseStep 1502515 = 2253773) B2253773
theorem B1502531 : Blo 1502071 1502531 := bstep (se 1 (by rfl) ⟨1126898, by rfl⟩ : syracuseStep 1502531 = 2253797) B2253797
theorem B1502547 : Blo 1502071 1502547 := bstep (se 1 (by rfl) ⟨1126910, by rfl⟩ : syracuseStep 1502547 = 2253821) B2253821
theorem B2534753 : Blo 1502071 2534753 := bstep (se 2 (by rfl) ⟨950532, by rfl⟩ : syracuseStep 2534753 = 1901065) B1901065
theorem B1502563 : Blo 1502071 1502563 := bstep (se 1 (by rfl) ⟨1126922, by rfl⟩ : syracuseStep 1502563 = 2253845) B2253845
theorem B3804529 : Blo 1502071 3804529 := bstep (se 2 (by rfl) ⟨1426698, by rfl⟩ : syracuseStep 3804529 = 2853397) B2853397
theorem B5418353 : Blo 1502071 5418353 := bstep (se 2 (by rfl) ⟨2031882, by rfl⟩ : syracuseStep 5418353 = 4063765) B4063765
theorem B1502579 : Blo 1502071 1502579 := bstep (se 1 (by rfl) ⟨1126934, by rfl⟩ : syracuseStep 1502579 = 2253869) B2253869
theorem B1502595 : Blo 1502071 1502595 := bstep (se 1 (by rfl) ⟨1126946, by rfl⟩ : syracuseStep 1502595 = 2253893) B2253893
theorem B1502611 : Blo 1502071 1502611 := bstep (se 1 (by rfl) ⟨1126958, by rfl⟩ : syracuseStep 1502611 = 2253917) B2253917
theorem B1502627 : Blo 1502071 1502627 := bstep (se 1 (by rfl) ⟨1126970, by rfl⟩ : syracuseStep 1502627 = 2253941) B2253941
theorem B1502643 : Blo 1502071 1502643 := bstep (se 1 (by rfl) ⟨1126982, by rfl⟩ : syracuseStep 1502643 = 2253965) B2253965
theorem B1691059 : Blo 1502071 1691059 := bstep (se 1 (by rfl) ⟨1268294, by rfl⟩ : syracuseStep 1691059 = 2536589) B2536589
theorem B1502659 : Blo 1502071 1502659 := bstep (se 1 (by rfl) ⟨1126994, by rfl⟩ : syracuseStep 1502659 = 2253989) B2253989
theorem B1502675 : Blo 1502071 1502675 := bstep (se 1 (by rfl) ⟨1127006, by rfl⟩ : syracuseStep 1502675 = 2254013) B2254013
theorem B2534881 : Blo 1502071 2534881 := bstep (se 2 (by rfl) ⟨950580, by rfl⟩ : syracuseStep 2534881 = 1901161) B1901161
theorem B1502691 : Blo 1502071 1502691 := bstep (se 1 (by rfl) ⟨1127018, by rfl⟩ : syracuseStep 1502691 = 2254037) B2254037
theorem B1502707 : Blo 1502071 1502707 := bstep (se 1 (by rfl) ⟨1127030, by rfl⟩ : syracuseStep 1502707 = 2254061) B2254061
theorem B2534915 : Blo 1502071 2534915 := bstep (se 1 (by rfl) ⟨1901186, by rfl⟩ : syracuseStep 2534915 = 3802373) B3802373
theorem B1502723 : Blo 1502071 1502723 := bstep (se 1 (by rfl) ⟨1127042, by rfl⟩ : syracuseStep 1502723 = 2254085) B2254085
theorem B1502739 : Blo 1502071 1502739 := bstep (se 1 (by rfl) ⟨1127054, by rfl⟩ : syracuseStep 1502739 = 2254109) B2254109
theorem B1502755 : Blo 1502071 1502755 := bstep (se 1 (by rfl) ⟨1127066, by rfl⟩ : syracuseStep 1502755 = 2254133) B2254133
theorem B1502771 : Blo 1502071 1502771 := bstep (se 1 (by rfl) ⟨1127078, by rfl⟩ : syracuseStep 1502771 = 2254157) B2254157
theorem B1502787 : Blo 1502071 1502787 := bstep (se 1 (by rfl) ⟨1127090, by rfl⟩ : syracuseStep 1502787 = 2254181) B2254181
theorem B1691203 : Blo 1502071 1691203 := bstep (se 1 (by rfl) ⟨1268402, by rfl⟩ : syracuseStep 1691203 = 2536805) B2536805
theorem B1502803 : Blo 1502071 1502803 := bstep (se 1 (by rfl) ⟨1127102, by rfl⟩ : syracuseStep 1502803 = 2254205) B2254205
theorem B1502819 : Blo 1502071 1502819 := bstep (se 1 (by rfl) ⟨1127114, by rfl⟩ : syracuseStep 1502819 = 2254229) B2254229
theorem B5074541 : Blo 1502071 5074541 := bstep (se 3 (by rfl) ⟨951476, by rfl⟩ : syracuseStep 5074541 = 1902953) B1902953
theorem B1502835 : Blo 1502071 1502835 := bstep (se 1 (by rfl) ⟨1127126, by rfl⟩ : syracuseStep 1502835 = 2254253) B2254253
theorem B2535043 : Blo 1502071 2535043 := bstep (se 1 (by rfl) ⟨1901282, by rfl⟩ : syracuseStep 2535043 = 3802565) B3802565
theorem B1502851 : Blo 1502071 1502851 := bstep (se 1 (by rfl) ⟨1127138, by rfl⟩ : syracuseStep 1502851 = 2254277) B2254277
theorem B3804803 : Blo 1502071 3804803 := bstep (se 1 (by rfl) ⟨2853602, by rfl⟩ : syracuseStep 3804803 = 5707205) B5707205
theorem B6418061 : Blo 1502071 6418061 := bstep (se 3 (by rfl) ⟨1203386, by rfl⟩ : syracuseStep 6418061 = 2406773) B2406773
theorem B4279949 : Blo 1502071 4279949 := bstep (se 3 (by rfl) ⟨802490, by rfl⟩ : syracuseStep 4279949 = 1604981) B1604981
theorem B1502867 : Blo 1502071 1502867 := bstep (se 1 (by rfl) ⟨1127150, by rfl⟩ : syracuseStep 1502867 = 2254301) B2254301
theorem B1502883 : Blo 1502071 1502883 := bstep (se 1 (by rfl) ⟨1127162, by rfl⟩ : syracuseStep 1502883 = 2254325) B2254325
theorem B1502899 : Blo 1502071 1502899 := bstep (se 1 (by rfl) ⟨1127174, by rfl⟩ : syracuseStep 1502899 = 2254349) B2254349
theorem B1502915 : Blo 1502071 1502915 := bstep (se 1 (by rfl) ⟨1127186, by rfl⟩ : syracuseStep 1502915 = 2254373) B2254373
theorem B8679109 : Blo 1502071 8679109 := bstep (se 4 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 8679109 = 1627333) B1627333
theorem B1502931 : Blo 1502071 1502931 := bstep (se 1 (by rfl) ⟨1127198, by rfl⟩ : syracuseStep 1502931 = 2254397) B2254397
theorem B1691347 : Blo 1502071 1691347 := bstep (se 1 (by rfl) ⟨1268510, by rfl⟩ : syracuseStep 1691347 = 2537021) B2537021
theorem B1502947 : Blo 1502071 1502947 := bstep (se 1 (by rfl) ⟨1127210, by rfl⟩ : syracuseStep 1502947 = 2254421) B2254421
theorem B1502963 : Blo 1502071 1502963 := bstep (se 1 (by rfl) ⟨1127222, by rfl⟩ : syracuseStep 1502963 = 2254445) B2254445
theorem B1502979 : Blo 1502071 1502979 := bstep (se 1 (by rfl) ⟨1127234, by rfl⟩ : syracuseStep 1502979 = 2254469) B2254469
theorem B14642957 : Blo 1502071 14642957 := bstep (se 3 (by rfl) ⟨2745554, by rfl⟩ : syracuseStep 14642957 = 5491109) B5491109
theorem B2535185 : Blo 1502071 2535185 := bstep (se 2 (by rfl) ⟨950694, by rfl⟩ : syracuseStep 2535185 = 1901389) B1901389
theorem B1502995 : Blo 1502071 1502995 := bstep (se 1 (by rfl) ⟨1127246, by rfl⟩ : syracuseStep 1502995 = 2254493) B2254493
theorem B1503011 : Blo 1502071 1503011 := bstep (se 1 (by rfl) ⟨1127258, by rfl⟩ : syracuseStep 1503011 = 2254517) B2254517
theorem B1503027 : Blo 1502071 1503027 := bstep (se 1 (by rfl) ⟨1127270, by rfl⟩ : syracuseStep 1503027 = 2254541) B2254541
theorem B1503043 : Blo 1502071 1503043 := bstep (se 1 (by rfl) ⟨1127282, by rfl⟩ : syracuseStep 1503043 = 2254565) B2254565
theorem B3804995 : Blo 1502071 3804995 := bstep (se 1 (by rfl) ⟨2853746, by rfl⟩ : syracuseStep 3804995 = 5707493) B5707493
theorem B5705549 : Blo 1502071 5705549 := bstep (se 3 (by rfl) ⟨1069790, by rfl⟩ : syracuseStep 5705549 = 2139581) B2139581
theorem B4280141 : Blo 1502071 4280141 := bstep (se 3 (by rfl) ⟨802526, by rfl⟩ : syracuseStep 4280141 = 1605053) B1605053
theorem B1503059 : Blo 1502071 1503059 := bstep (se 1 (by rfl) ⟨1127294, by rfl⟩ : syracuseStep 1503059 = 2254589) B2254589
theorem B1503075 : Blo 1502071 1503075 := bstep (se 1 (by rfl) ⟨1127306, by rfl⟩ : syracuseStep 1503075 = 2254613) B2254613
theorem B1691491 : Blo 1502071 1691491 := bstep (se 1 (by rfl) ⟨1268618, by rfl⟩ : syracuseStep 1691491 = 2537237) B2537237
theorem B10170211 : Blo 1502071 10170211 := bstep (se 1 (by rfl) ⟨7627658, by rfl⟩ : syracuseStep 10170211 = 15255317) B15255317
theorem B1503091 : Blo 1502071 1503091 := bstep (se 1 (by rfl) ⟨1127318, by rfl⟩ : syracuseStep 1503091 = 2254637) B2254637
theorem B1503107 : Blo 1502071 1503107 := bstep (se 1 (by rfl) ⟨1127330, by rfl⟩ : syracuseStep 1503107 = 2254661) B2254661
theorem B2535313 : Blo 1502071 2535313 := bstep (se 2 (by rfl) ⟨950742, by rfl⟩ : syracuseStep 2535313 = 1901485) B1901485
theorem B1503123 : Blo 1502071 1503123 := bstep (se 1 (by rfl) ⟨1127342, by rfl⟩ : syracuseStep 1503123 = 2254685) B2254685
theorem B9629603 : Blo 1502071 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B1503139 : Blo 1502071 1503139 := bstep (se 1 (by rfl) ⟨1127354, by rfl⟩ : syracuseStep 1503139 = 2254709) B2254709
theorem B2535347 : Blo 1502071 2535347 := bstep (se 1 (by rfl) ⟨1901510, by rfl⟩ : syracuseStep 2535347 = 3803021) B3803021
theorem B1503155 : Blo 1502071 1503155 := bstep (se 1 (by rfl) ⟨1127366, by rfl⟩ : syracuseStep 1503155 = 2254733) B2254733
theorem B1503171 : Blo 1502071 1503171 := bstep (se 1 (by rfl) ⟨1127378, by rfl⟩ : syracuseStep 1503171 = 2254757) B2254757
theorem B1503187 : Blo 1502071 1503187 := bstep (se 1 (by rfl) ⟨1127390, by rfl⟩ : syracuseStep 1503187 = 2254781) B2254781
theorem B1503203 : Blo 1502071 1503203 := bstep (se 1 (by rfl) ⟨1127402, by rfl⟩ : syracuseStep 1503203 = 2254805) B2254805
theorem B1544179 : Blo 1502071 1544179 := bstep (se 1 (by rfl) ⟨1158134, by rfl⟩ : syracuseStep 1544179 = 2316269) B2316269
theorem B1503219 : Blo 1502071 1503219 := bstep (se 1 (by rfl) ⟨1127414, by rfl⟩ : syracuseStep 1503219 = 2254829) B2254829
theorem B1503235 : Blo 1502071 1503235 := bstep (se 1 (by rfl) ⟨1127426, by rfl⟩ : syracuseStep 1503235 = 2254853) B2254853
theorem B1503251 : Blo 1502071 1503251 := bstep (se 1 (by rfl) ⟨1127438, by rfl⟩ : syracuseStep 1503251 = 2254877) B2254877
theorem B1503267 : Blo 1502071 1503267 := bstep (se 1 (by rfl) ⟨1127450, by rfl⟩ : syracuseStep 1503267 = 2254901) B2254901
theorem B2535475 : Blo 1502071 2535475 := bstep (se 1 (by rfl) ⟨1901606, by rfl⟩ : syracuseStep 2535475 = 3803213) B3803213
theorem B1503283 : Blo 1502071 1503283 := bstep (se 1 (by rfl) ⟨1127462, by rfl⟩ : syracuseStep 1503283 = 2254925) B2254925
theorem B1503299 : Blo 1502071 1503299 := bstep (se 1 (by rfl) ⟨1127474, by rfl⟩ : syracuseStep 1503299 = 2254949) B2254949
theorem B1503315 : Blo 1502071 1503315 := bstep (se 1 (by rfl) ⟨1127486, by rfl⟩ : syracuseStep 1503315 = 2254973) B2254973
theorem B1503331 : Blo 1502071 1503331 := bstep (se 1 (by rfl) ⟨1127498, by rfl⟩ : syracuseStep 1503331 = 2254997) B2254997
theorem B7606385 : Blo 1502071 7606385 := bstep (se 2 (by rfl) ⟨2852394, by rfl⟩ : syracuseStep 7606385 = 5704789) B5704789
theorem B1503347 : Blo 1502071 1503347 := bstep (se 1 (by rfl) ⟨1127510, by rfl⟩ : syracuseStep 1503347 = 2255021) B2255021
theorem B1503363 : Blo 1502071 1503363 := bstep (se 1 (by rfl) ⟨1127522, by rfl⟩ : syracuseStep 1503363 = 2255045) B2255045
theorem B1503379 : Blo 1502071 1503379 := bstep (se 1 (by rfl) ⟨1127534, by rfl⟩ : syracuseStep 1503379 = 2255069) B2255069
theorem B1503395 : Blo 1502071 1503395 := bstep (se 1 (by rfl) ⟨1127546, by rfl⟩ : syracuseStep 1503395 = 2255093) B2255093
theorem B6090929 : Blo 1502071 6090929 := bstep (se 2 (by rfl) ⟨2284098, by rfl⟩ : syracuseStep 6090929 = 4568197) B4568197
theorem B1503411 : Blo 1502071 1503411 := bstep (se 1 (by rfl) ⟨1127558, by rfl⟩ : syracuseStep 1503411 = 2255117) B2255117
theorem B2535617 : Blo 1502071 2535617 := bstep (se 2 (by rfl) ⟨950856, by rfl⟩ : syracuseStep 2535617 = 1901713) B1901713
theorem B4812995 : Blo 1502071 4812995 := bstep (se 1 (by rfl) ⟨3609746, by rfl⟩ : syracuseStep 4812995 = 7219493) B7219493
theorem B1503427 : Blo 1502071 1503427 := bstep (se 1 (by rfl) ⟨1127570, by rfl⟩ : syracuseStep 1503427 = 2255141) B2255141
theorem B1503443 : Blo 1502071 1503443 := bstep (se 1 (by rfl) ⟨1127582, by rfl⟩ : syracuseStep 1503443 = 2255165) B2255165
theorem B1503459 : Blo 1502071 1503459 := bstep (se 1 (by rfl) ⟨1127594, by rfl⟩ : syracuseStep 1503459 = 2255189) B2255189
theorem B1503475 : Blo 1502071 1503475 := bstep (se 1 (by rfl) ⟨1127606, by rfl⟩ : syracuseStep 1503475 = 2255213) B2255213
theorem B1503491 : Blo 1502071 1503491 := bstep (se 1 (by rfl) ⟨1127618, by rfl⟩ : syracuseStep 1503491 = 2255237) B2255237
theorem B1503507 : Blo 1502071 1503507 := bstep (se 1 (by rfl) ⟨1127630, by rfl⟩ : syracuseStep 1503507 = 2255261) B2255261
theorem B42250517 : Blo 1502071 42250517 := bstep (se 6 (by rfl) ⟨990246, by rfl⟩ : syracuseStep 42250517 = 1980493) B1980493
theorem B1503523 : Blo 1502071 1503523 := bstep (se 1 (by rfl) ⟨1127642, by rfl⟩ : syracuseStep 1503523 = 2255285) B2255285
theorem B1503539 : Blo 1502071 1503539 := bstep (se 1 (by rfl) ⟨1127654, by rfl⟩ : syracuseStep 1503539 = 2255309) B2255309
theorem B2535745 : Blo 1502071 2535745 := bstep (se 2 (by rfl) ⟨950904, by rfl⟩ : syracuseStep 2535745 = 1901809) B1901809
theorem B3428675 : Blo 1502071 3428675 := bstep (se 1 (by rfl) ⟨2571506, by rfl⟩ : syracuseStep 3428675 = 5143013) B5143013
theorem B1503555 : Blo 1502071 1503555 := bstep (se 1 (by rfl) ⟨1127666, by rfl⟩ : syracuseStep 1503555 = 2255333) B2255333
theorem B1503571 : Blo 1502071 1503571 := bstep (se 1 (by rfl) ⟨1127678, by rfl⟩ : syracuseStep 1503571 = 2255357) B2255357
theorem B2535779 : Blo 1502071 2535779 := bstep (se 1 (by rfl) ⟨1901834, by rfl⟩ : syracuseStep 2535779 = 3803669) B3803669
theorem B2535907 : Blo 1502071 2535907 := bstep (se 1 (by rfl) ⟨1901930, by rfl⟩ : syracuseStep 2535907 = 3803861) B3803861
theorem B3379697 : Blo 1502071 3379697 := bstep (se 2 (by rfl) ⟨1267386, by rfl⟩ : syracuseStep 3379697 = 2534773) B2534773
theorem B3379715 : Blo 1502071 3379715 := bstep (se 1 (by rfl) ⟨2534786, by rfl⟩ : syracuseStep 3379715 = 5069573) B5069573
theorem B2536049 : Blo 1502071 2536049 := bstep (se 2 (by rfl) ⟨951018, by rfl⟩ : syracuseStep 2536049 = 1902037) B1902037
theorem B4338353 : Blo 1502071 4338353 := bstep (se 2 (by rfl) ⟨1626882, by rfl⟩ : syracuseStep 4338353 = 3253765) B3253765
theorem B2536177 : Blo 1502071 2536177 := bstep (se 2 (by rfl) ⟨951066, by rfl⟩ : syracuseStep 2536177 = 1902133) B1902133
theorem B3379985 : Blo 1502071 3379985 := bstep (se 2 (by rfl) ⟨1267494, by rfl⟩ : syracuseStep 3379985 = 2534989) B2534989
theorem B2536211 : Blo 1502071 2536211 := bstep (se 1 (by rfl) ⟨1902158, by rfl⟩ : syracuseStep 2536211 = 3804317) B3804317
theorem B3380003 : Blo 1502071 3380003 := bstep (se 1 (by rfl) ⟨2535002, by rfl⟩ : syracuseStep 3380003 = 5070005) B5070005
theorem B4281133 : Blo 1502071 4281133 := bstep (se 3 (by rfl) ⟨802712, by rfl⟩ : syracuseStep 4281133 = 1605425) B1605425
theorem B2536339 : Blo 1502071 2536339 := bstep (se 1 (by rfl) ⟨1902254, by rfl⟩ : syracuseStep 2536339 = 3804509) B3804509
theorem B2536481 : Blo 1502071 2536481 := bstep (se 2 (by rfl) ⟨951180, by rfl⟩ : syracuseStep 2536481 = 1902361) B1902361
theorem B3380273 : Blo 1502071 3380273 := bstep (se 2 (by rfl) ⟨1267602, by rfl⟩ : syracuseStep 3380273 = 2535205) B2535205
theorem B3380291 : Blo 1502071 3380291 := bstep (se 1 (by rfl) ⟨2535218, by rfl⟩ : syracuseStep 3380291 = 5070437) B5070437
theorem B18781253 : Blo 1502071 18781253 := bstep (se 4 (by rfl) ⟨1760742, by rfl⟩ : syracuseStep 18781253 = 3521485) B3521485
theorem B4633681 : Blo 1502071 4633681 := bstep (se 2 (by rfl) ⟨1737630, by rfl⟩ : syracuseStep 4633681 = 3475261) B3475261
theorem B2708579 : Blo 1502071 2708579 := bstep (se 1 (by rfl) ⟨2031434, by rfl⟩ : syracuseStep 2708579 = 4062869) B4062869
theorem B9139333 : Blo 1502071 9139333 := bstep (se 4 (by rfl) ⟨856812, by rfl⟩ : syracuseStep 9139333 = 1713625) B1713625
theorem B2536609 : Blo 1502071 2536609 := bstep (se 2 (by rfl) ⟨951228, by rfl⟩ : syracuseStep 2536609 = 1902457) B1902457
theorem B2536643 : Blo 1502071 2536643 := bstep (se 1 (by rfl) ⟨1902482, by rfl⟩ : syracuseStep 2536643 = 3804965) B3804965
theorem B8344781 : Blo 1502071 8344781 := bstep (se 3 (by rfl) ⟨1564646, by rfl⟩ : syracuseStep 8344781 = 3129293) B3129293
theorem B8123597 : Blo 1502071 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B4060369 : Blo 1502071 4060369 := bstep (se 2 (by rfl) ⟨1522638, by rfl⟩ : syracuseStep 4060369 = 3045277) B3045277
theorem B4814083 : Blo 1502071 4814083 := bstep (se 1 (by rfl) ⟨3610562, by rfl⟩ : syracuseStep 4814083 = 7221125) B7221125
theorem B2536771 : Blo 1502071 2536771 := bstep (se 1 (by rfl) ⟨1902578, by rfl⟩ : syracuseStep 2536771 = 3805157) B3805157
theorem B3380561 : Blo 1502071 3380561 := bstep (se 2 (by rfl) ⟨1267710, by rfl⟩ : syracuseStep 3380561 = 2535421) B2535421
theorem B3380579 : Blo 1502071 3380579 := bstep (se 1 (by rfl) ⟨2535434, by rfl⟩ : syracuseStep 3380579 = 5070869) B5070869
theorem B4814225 : Blo 1502071 4814225 := bstep (se 2 (by rfl) ⟨1805334, by rfl⟩ : syracuseStep 4814225 = 3610669) B3610669
theorem B3659185 : Blo 1502071 3659185 := bstep (se 2 (by rfl) ⟨1372194, by rfl⟩ : syracuseStep 3659185 = 2744389) B2744389
theorem B2536913 : Blo 1502071 2536913 := bstep (se 2 (by rfl) ⟨951342, by rfl⟩ : syracuseStep 2536913 = 1902685) B1902685
theorem B3208739 : Blo 1502071 3208739 := bstep (se 1 (by rfl) ⟨2406554, by rfl⟩ : syracuseStep 3208739 = 4813109) B4813109
theorem B7607843 : Blo 1502071 7607843 := bstep (se 1 (by rfl) ⟨5705882, by rfl⟩ : syracuseStep 7607843 = 11411765) B11411765
theorem B2537041 : Blo 1502071 2537041 := bstep (se 2 (by rfl) ⟨951390, by rfl⟩ : syracuseStep 2537041 = 1902781) B1902781
theorem B3380849 : Blo 1502071 3380849 := bstep (se 2 (by rfl) ⟨1267818, by rfl⟩ : syracuseStep 3380849 = 2535637) B2535637
theorem B2537075 : Blo 1502071 2537075 := bstep (se 1 (by rfl) ⟨1902806, by rfl⟩ : syracuseStep 2537075 = 3805613) B3805613
theorem B3380867 : Blo 1502071 3380867 := bstep (se 1 (by rfl) ⟨2535650, by rfl⟩ : syracuseStep 3380867 = 5071301) B5071301
theorem B18282125 : Blo 1502071 18282125 := bstep (se 3 (by rfl) ⟨3427898, by rfl⟩ : syracuseStep 18282125 = 6855797) B6855797
theorem B10426097 : Blo 1502071 10426097 := bstep (se 2 (by rfl) ⟨3909786, by rfl⟩ : syracuseStep 10426097 = 7819573) B7819573
theorem B2537203 : Blo 1502071 2537203 := bstep (se 1 (by rfl) ⟨1902902, by rfl⟩ : syracuseStep 2537203 = 3805805) B3805805
theorem B3381137 : Blo 1502071 3381137 := bstep (se 2 (by rfl) ⟨1267926, by rfl⟩ : syracuseStep 3381137 = 2535853) B2535853
theorem B3381155 : Blo 1502071 3381155 := bstep (se 1 (by rfl) ⟨2535866, by rfl⟩ : syracuseStep 3381155 = 5071733) B5071733
theorem B32511941 : Blo 1502071 32511941 := bstep (se 4 (by rfl) ⟨3047994, by rfl⟩ : syracuseStep 32511941 = 6095989) B6095989
theorem B18520163 : Blo 1502071 18520163 := bstep (se 1 (by rfl) ⟨13890122, by rfl⟩ : syracuseStep 18520163 = 27780245) B27780245
theorem B3381425 : Blo 1502071 3381425 := bstep (se 2 (by rfl) ⟨1268034, by rfl⟩ : syracuseStep 3381425 = 2536069) B2536069
theorem B3381443 : Blo 1502071 3381443 := bstep (se 1 (by rfl) ⟨2536082, by rfl⟩ : syracuseStep 3381443 = 5072165) B5072165
theorem B7608653 : Blo 1502071 7608653 := bstep (se 3 (by rfl) ⟨1426622, by rfl⟩ : syracuseStep 7608653 = 2853245) B2853245
theorem B9632141 : Blo 1502071 9632141 := bstep (se 3 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 9632141 = 3612053) B3612053
theorem B2283923 : Blo 1502071 2283923 := bstep (se 1 (by rfl) ⟨1712942, by rfl⟩ : syracuseStep 2283923 = 3425885) B3425885
theorem B8673733 : Blo 1502071 8673733 := bstep (se 4 (by rfl) ⟨813162, by rfl⟩ : syracuseStep 8673733 = 1626325) B1626325
theorem B8559053 : Blo 1502071 8559053 := bstep (se 3 (by rfl) ⟨1604822, by rfl⟩ : syracuseStep 8559053 = 3209645) B3209645
theorem B3381713 : Blo 1502071 3381713 := bstep (se 2 (by rfl) ⟨1268142, by rfl⟩ : syracuseStep 3381713 = 2536285) B2536285
theorem B3381731 : Blo 1502071 3381731 := bstep (se 1 (by rfl) ⟨2536298, by rfl⟩ : syracuseStep 3381731 = 5072597) B5072597
theorem B14637581 : Blo 1502071 14637581 := bstep (se 3 (by rfl) ⟨2744546, by rfl⟩ : syracuseStep 14637581 = 5489093) B5489093
theorem B6421169 : Blo 1502071 6421169 := bstep (se 2 (by rfl) ⟨2407938, by rfl⟩ : syracuseStep 6421169 = 4815877) B4815877
theorem B5708465 : Blo 1502071 5708465 := bstep (se 2 (by rfl) ⟨2140674, by rfl⟩ : syracuseStep 5708465 = 4281349) B4281349
theorem B4815569 : Blo 1502071 4815569 := bstep (se 2 (by rfl) ⟨1805838, by rfl⟩ : syracuseStep 4815569 = 3611677) B3611677
theorem B6093539 : Blo 1502071 6093539 := bstep (se 1 (by rfl) ⟨4570154, by rfl⟩ : syracuseStep 6093539 = 9140309) B9140309
theorem B3382001 : Blo 1502071 3382001 := bstep (se 2 (by rfl) ⟨1268250, by rfl⟩ : syracuseStep 3382001 = 2536501) B2536501
theorem B3382019 : Blo 1502071 3382019 := bstep (se 1 (by rfl) ⟨2536514, by rfl⟩ : syracuseStep 3382019 = 5073029) B5073029
theorem B1604387 : Blo 1502071 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B5069681 : Blo 1502071 5069681 := bstep (se 2 (by rfl) ⟨1901130, by rfl⟩ : syracuseStep 5069681 = 3802261) B3802261
theorem B10705861 : Blo 1502071 10705861 := bstep (se 4 (by rfl) ⟨1003674, by rfl⟩ : syracuseStep 10705861 = 2007349) B2007349
theorem B3382289 : Blo 1502071 3382289 := bstep (se 2 (by rfl) ⟨1268358, by rfl⟩ : syracuseStep 3382289 = 2536717) B2536717
theorem B3382307 : Blo 1502071 3382307 := bstep (se 1 (by rfl) ⟨2536730, by rfl⟩ : syracuseStep 3382307 = 5073461) B5073461
theorem B4062349 : Blo 1502071 4062349 := bstep (se 3 (by rfl) ⟨761690, by rfl⟩ : syracuseStep 4062349 = 1523381) B1523381
theorem B4570253 : Blo 1502071 4570253 := bstep (se 3 (by rfl) ⟨856922, by rfl⟩ : syracuseStep 4570253 = 1713845) B1713845
theorem B5782691 : Blo 1502071 5782691 := bstep (se 1 (by rfl) ⟨4337018, by rfl⟩ : syracuseStep 5782691 = 8674037) B8674037
theorem B3046673 : Blo 1502071 3046673 := bstep (se 2 (by rfl) ⟨1142502, by rfl⟩ : syracuseStep 3046673 = 2285005) B2285005
theorem B1522963 : Blo 1502071 1522963 := bstep (se 1 (by rfl) ⟨1142222, by rfl⟩ : syracuseStep 1522963 = 2284445) B2284445
theorem B3382577 : Blo 1502071 3382577 := bstep (se 2 (by rfl) ⟨1268466, by rfl⟩ : syracuseStep 3382577 = 2536933) B2536933
theorem B2407747 : Blo 1502071 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B3382595 : Blo 1502071 3382595 := bstep (se 1 (by rfl) ⟨2536946, by rfl⟩ : syracuseStep 3382595 = 5073893) B5073893
theorem B5070221 : Blo 1502071 5070221 := bstep (se 3 (by rfl) ⟨950666, by rfl⟩ : syracuseStep 5070221 = 1901333) B1901333
theorem B5070275 : Blo 1502071 5070275 := bstep (se 1 (by rfl) ⟨3802706, by rfl⟩ : syracuseStep 5070275 = 7605413) B7605413
theorem B2604593 : Blo 1502071 2604593 := bstep (se 2 (by rfl) ⟨976722, by rfl⟩ : syracuseStep 2604593 = 1953445) B1953445
theorem B6094385 : Blo 1502071 6094385 := bstep (se 2 (by rfl) ⟨2285394, by rfl⟩ : syracuseStep 6094385 = 4570789) B4570789
theorem B15425093 : Blo 1502071 15425093 := bstep (se 4 (by rfl) ⟨1446102, by rfl⟩ : syracuseStep 15425093 = 2892205) B2892205
theorem B3382865 : Blo 1502071 3382865 := bstep (se 2 (by rfl) ⟨1268574, by rfl⟩ : syracuseStep 3382865 = 2537149) B2537149
theorem B3382883 : Blo 1502071 3382883 := bstep (se 1 (by rfl) ⟨2537162, by rfl⟩ : syracuseStep 3382883 = 5074325) B5074325
theorem B4816493 : Blo 1502071 4816493 := bstep (se 3 (by rfl) ⟨903092, by rfl⟩ : syracuseStep 4816493 = 1806185) B1806185
theorem B5070545 : Blo 1502071 5070545 := bstep (se 2 (by rfl) ⟨1901454, by rfl⟩ : syracuseStep 5070545 = 3802909) B3802909
theorem B3210961 : Blo 1502071 3210961 := bstep (se 2 (by rfl) ⟨1204110, by rfl⟩ : syracuseStep 3210961 = 2408221) B2408221
theorem B3473123 : Blo 1502071 3473123 := bstep (se 1 (by rfl) ⟨2604842, by rfl⟩ : syracuseStep 3473123 = 5209685) B5209685
theorem B6094577 : Blo 1502071 6094577 := bstep (se 2 (by rfl) ⟨2285466, by rfl⟩ : syracuseStep 6094577 = 4570933) B4570933
theorem B2408195 : Blo 1502071 2408195 := bstep (se 1 (by rfl) ⟨1806146, by rfl⟩ : syracuseStep 2408195 = 3612293) B3612293
theorem B4816685 : Blo 1502071 4816685 := bstep (se 3 (by rfl) ⟨903128, by rfl⟩ : syracuseStep 4816685 = 1806257) B1806257
theorem B9756515 : Blo 1502071 9756515 := bstep (se 1 (by rfl) ⟨7317386, by rfl⟩ : syracuseStep 9756515 = 14634773) B14634773
theorem B5865329 : Blo 1502071 5865329 := bstep (se 2 (by rfl) ⟨2199498, by rfl⟩ : syracuseStep 5865329 = 4398997) B4398997
theorem B6422435 : Blo 1502071 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B21659683 : Blo 1502071 21659683 := bstep (se 1 (by rfl) ⟨16244762, by rfl⟩ : syracuseStep 21659683 = 32489525) B32489525
theorem B5070923 : Blo 1502071 5070923 := bstep (se 1 (by rfl) ⟨3803192, by rfl⟩ : syracuseStep 5070923 = 7606385) B7606385
theorem B2285783 : Blo 1502071 2285783 := bstep (se 1 (by rfl) ⟨1714337, by rfl⟩ : syracuseStep 2285783 = 3428675) B3428675
theorem B2253131 : Blo 1502071 2253131 := bstep (se 1 (by rfl) ⟨1689848, by rfl⟩ : syracuseStep 2253131 = 3379697) B3379697
theorem B2253143 : Blo 1502071 2253143 := bstep (se 1 (by rfl) ⟨1689857, by rfl⟩ : syracuseStep 2253143 = 3379715) B3379715
theorem B5071193 : Blo 1502071 5071193 := bstep (se 2 (by rfl) ⟨1901697, by rfl⟩ : syracuseStep 5071193 = 3803395) B3803395
theorem B69394801 : Blo 1502071 69394801 := bstep (se 2 (by rfl) ⟨26023050, by rfl⟩ : syracuseStep 69394801 = 52046101) B52046101
theorem B2253209 : Blo 1502071 2253209 := bstep (se 2 (by rfl) ⟨844953, by rfl⟩ : syracuseStep 2253209 = 1689907) B1689907
theorem B2892235 : Blo 1502071 2892235 := bstep (se 1 (by rfl) ⟨2169176, by rfl⟩ : syracuseStep 2892235 = 4338353) B4338353
theorem B2253323 : Blo 1502071 2253323 := bstep (se 1 (by rfl) ⟨1689992, by rfl⟩ : syracuseStep 2253323 = 3379985) B3379985
theorem B2253335 : Blo 1502071 2253335 := bstep (se 1 (by rfl) ⟨1690001, by rfl⟩ : syracuseStep 2253335 = 3380003) B3380003
theorem B2253401 : Blo 1502071 2253401 := bstep (se 2 (by rfl) ⟨845025, by rfl⟩ : syracuseStep 2253401 = 1690051) B1690051
theorem B2253515 : Blo 1502071 2253515 := bstep (se 1 (by rfl) ⟨1690136, by rfl⟩ : syracuseStep 2253515 = 3380273) B3380273
theorem B2253527 : Blo 1502071 2253527 := bstep (se 1 (by rfl) ⟨1690145, by rfl⟩ : syracuseStep 2253527 = 3380291) B3380291
theorem B1901323 : Blo 1502071 1901323 := bstep (se 1 (by rfl) ⟨1425992, by rfl⟩ : syracuseStep 1901323 = 2851985) B2851985
theorem B2253593 : Blo 1502071 2253593 := bstep (se 2 (by rfl) ⟨845097, by rfl⟩ : syracuseStep 2253593 = 1690195) B1690195
theorem B5563187 : Blo 1502071 5563187 := bstep (se 1 (by rfl) ⟨4172390, by rfl⟩ : syracuseStep 5563187 = 8344781) B8344781
theorem B5415731 : Blo 1502071 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B2253707 : Blo 1502071 2253707 := bstep (se 1 (by rfl) ⟨1690280, by rfl⟩ : syracuseStep 2253707 = 3380561) B3380561
theorem B2253719 : Blo 1502071 2253719 := bstep (se 1 (by rfl) ⟨1690289, by rfl⟩ : syracuseStep 2253719 = 3380579) B3380579
theorem B2851787 : Blo 1502071 2851787 := bstep (se 1 (by rfl) ⟨2138840, by rfl⟩ : syracuseStep 2851787 = 4277681) B4277681
theorem B2253785 : Blo 1502071 2253785 := bstep (se 2 (by rfl) ⟨845169, by rfl⟩ : syracuseStep 2253785 = 1690339) B1690339
theorem B2851841 : Blo 1502071 2851841 := bstep (se 2 (by rfl) ⟨1069440, by rfl⟩ : syracuseStep 2851841 = 2138881) B2138881
theorem B5071895 : Blo 1502071 5071895 := bstep (se 1 (by rfl) ⟨3803921, by rfl⟩ : syracuseStep 5071895 = 7607843) B7607843
theorem B2253899 : Blo 1502071 2253899 := bstep (se 1 (by rfl) ⟨1690424, by rfl⟩ : syracuseStep 2253899 = 3380849) B3380849
theorem B2253911 : Blo 1502071 2253911 := bstep (se 1 (by rfl) ⟨1690433, by rfl⟩ : syracuseStep 2253911 = 3380867) B3380867
theorem B2253977 : Blo 1502071 2253977 := bstep (se 2 (by rfl) ⟨845241, by rfl⟩ : syracuseStep 2253977 = 1690483) B1690483
theorem B2254091 : Blo 1502071 2254091 := bstep (se 1 (by rfl) ⟨1690568, by rfl⟩ : syracuseStep 2254091 = 3381137) B3381137
theorem B2254103 : Blo 1502071 2254103 := bstep (se 1 (by rfl) ⟨1690577, by rfl⟩ : syracuseStep 2254103 = 3381155) B3381155
theorem B2254169 : Blo 1502071 2254169 := bstep (se 2 (by rfl) ⟨845313, by rfl⟩ : syracuseStep 2254169 = 1690627) B1690627
theorem B12346775 : Blo 1502071 12346775 := bstep (se 1 (by rfl) ⟨9260081, by rfl⟩ : syracuseStep 12346775 = 18520163) B18520163
theorem B6178241 : Blo 1502071 6178241 := bstep (se 2 (by rfl) ⟨2316840, by rfl⟩ : syracuseStep 6178241 = 4633681) B4633681
theorem B2254283 : Blo 1502071 2254283 := bstep (se 1 (by rfl) ⟨1690712, by rfl⟩ : syracuseStep 2254283 = 3381425) B3381425
theorem B2254295 : Blo 1502071 2254295 := bstep (se 1 (by rfl) ⟨1690721, by rfl⟩ : syracuseStep 2254295 = 3381443) B3381443
theorem B3802585 : Blo 1502071 3802585 := bstep (se 2 (by rfl) ⟨1425969, by rfl⟩ : syracuseStep 3802585 = 2851939) B2851939
theorem B5416465 : Blo 1502071 5416465 := bstep (se 2 (by rfl) ⟨2031174, by rfl⟩ : syracuseStep 5416465 = 4062349) B4062349
theorem B2254361 : Blo 1502071 2254361 := bstep (se 2 (by rfl) ⟨845385, by rfl⟩ : syracuseStep 2254361 = 1690771) B1690771
theorem B5072435 : Blo 1502071 5072435 := bstep (se 1 (by rfl) ⟨3804326, by rfl⟩ : syracuseStep 5072435 = 7608653) B7608653
theorem B2254475 : Blo 1502071 2254475 := bstep (se 1 (by rfl) ⟨1690856, by rfl⟩ : syracuseStep 2254475 = 3381713) B3381713
theorem B2254487 : Blo 1502071 2254487 := bstep (se 1 (by rfl) ⟨1690865, by rfl⟩ : syracuseStep 2254487 = 3381731) B3381731
theorem B9758387 : Blo 1502071 9758387 := bstep (se 1 (by rfl) ⟨7318790, by rfl⟩ : syracuseStep 9758387 = 14637581) B14637581
theorem B1902295 : Blo 1502071 1902295 := bstep (se 1 (by rfl) ⟨1426721, by rfl⟩ : syracuseStep 1902295 = 2853443) B2853443
theorem B2254553 : Blo 1502071 2254553 := bstep (se 2 (by rfl) ⟨845457, by rfl⟩ : syracuseStep 2254553 = 1690915) B1690915
theorem B5072705 : Blo 1502071 5072705 := bstep (se 2 (by rfl) ⟨1902264, by rfl⟩ : syracuseStep 5072705 = 3804529) B3804529
theorem B4278091 : Blo 1502071 4278091 := bstep (se 1 (by rfl) ⟨3208568, by rfl⟩ : syracuseStep 4278091 = 6417137) B6417137
theorem B2254667 : Blo 1502071 2254667 := bstep (se 1 (by rfl) ⟨1691000, by rfl⟩ : syracuseStep 2254667 = 3382001) B3382001
theorem B2254679 : Blo 1502071 2254679 := bstep (se 1 (by rfl) ⟨1691009, by rfl⟩ : syracuseStep 2254679 = 3382019) B3382019
theorem B2852759 : Blo 1502071 2852759 := bstep (se 1 (by rfl) ⟨2139569, by rfl⟩ : syracuseStep 2852759 = 4279139) B4279139
theorem B2254745 : Blo 1502071 2254745 := bstep (se 2 (by rfl) ⟨845529, by rfl⟩ : syracuseStep 2254745 = 1691059) B1691059
theorem B2254859 : Blo 1502071 2254859 := bstep (se 1 (by rfl) ⟨1691144, by rfl⟩ : syracuseStep 2254859 = 3382289) B3382289
theorem B2254871 : Blo 1502071 2254871 := bstep (se 1 (by rfl) ⟨1691153, by rfl⟩ : syracuseStep 2254871 = 3382307) B3382307
theorem B2254937 : Blo 1502071 2254937 := bstep (se 2 (by rfl) ⟨845601, by rfl⟩ : syracuseStep 2254937 = 1691203) B1691203
theorem B4278365 : Blo 1502071 4278365 := bstep (se 3 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 4278365 = 1604387) B1604387
theorem B13371485 : Blo 1502071 13371485 := bstep (se 3 (by rfl) ⟨2507153, by rfl⟩ : syracuseStep 13371485 = 5014307) B5014307
theorem B2255051 : Blo 1502071 2255051 := bstep (se 1 (by rfl) ⟨1691288, by rfl⟩ : syracuseStep 2255051 = 3382577) B3382577
theorem B11413709 : Blo 1502071 11413709 := bstep (se 3 (by rfl) ⟨2140070, by rfl⟩ : syracuseStep 11413709 = 4280141) B4280141
theorem B2255063 : Blo 1502071 2255063 := bstep (se 1 (by rfl) ⟨1691297, by rfl⟩ : syracuseStep 2255063 = 3382595) B3382595
theorem B7604441 : Blo 1502071 7604441 := bstep (se 2 (by rfl) ⟨2851665, by rfl⟩ : syracuseStep 7604441 = 5703331) B5703331
theorem B1689835 : Blo 1502071 1689835 := bstep (se 1 (by rfl) ⟨1267376, by rfl⟩ : syracuseStep 1689835 = 2534753) B2534753
theorem B2255129 : Blo 1502071 2255129 := bstep (se 2 (by rfl) ⟨845673, by rfl⟩ : syracuseStep 2255129 = 1691347) B1691347
theorem B15640877 : Blo 1502071 15640877 := bstep (se 3 (by rfl) ⟨2932664, by rfl⟩ : syracuseStep 15640877 = 5865329) B5865329
theorem B1689943 : Blo 1502071 1689943 := bstep (se 1 (by rfl) ⟨1267457, by rfl⟩ : syracuseStep 1689943 = 2534915) B2534915
theorem B5073245 : Blo 1502071 5073245 := bstep (se 3 (by rfl) ⟨951233, by rfl⟩ : syracuseStep 5073245 = 1902467) B1902467
theorem B10283395 : Blo 1502071 10283395 := bstep (se 1 (by rfl) ⟨7712546, by rfl⟩ : syracuseStep 10283395 = 15425093) B15425093
theorem B2255243 : Blo 1502071 2255243 := bstep (se 1 (by rfl) ⟨1691432, by rfl⟩ : syracuseStep 2255243 = 3382865) B3382865
theorem B2255255 : Blo 1502071 2255255 := bstep (se 1 (by rfl) ⟨1691441, by rfl⟩ : syracuseStep 2255255 = 3382883) B3382883
theorem B4278707 : Blo 1502071 4278707 := bstep (se 1 (by rfl) ⟨3209030, by rfl⟩ : syracuseStep 4278707 = 6418061) B6418061
theorem B2853299 : Blo 1502071 2853299 := bstep (se 1 (by rfl) ⟨2139974, by rfl⟩ : syracuseStep 2853299 = 4279949) B4279949
theorem B2255321 : Blo 1502071 2255321 := bstep (se 2 (by rfl) ⟨845745, by rfl⟩ : syracuseStep 2255321 = 1691491) B1691491
theorem B13560281 : Blo 1502071 13560281 := bstep (se 2 (by rfl) ⟨5085105, by rfl⟩ : syracuseStep 13560281 = 10170211) B10170211
theorem B1690123 : Blo 1502071 1690123 := bstep (se 1 (by rfl) ⟨1267592, by rfl⟩ : syracuseStep 1690123 = 2535185) B2535185
theorem B3803699 : Blo 1502071 3803699 := bstep (se 1 (by rfl) ⟨2852774, by rfl⟩ : syracuseStep 3803699 = 5705549) B5705549
theorem B1690231 : Blo 1502071 1690231 := bstep (se 1 (by rfl) ⟨1267673, by rfl⟩ : syracuseStep 1690231 = 2535347) B2535347
theorem B2058905 : Blo 1502071 2058905 := bstep (se 2 (by rfl) ⟨772089, by rfl⟩ : syracuseStep 2058905 = 1544179) B1544179
theorem B11414195 : Blo 1502071 11414195 := bstep (se 1 (by rfl) ⟨8560646, by rfl⟩ : syracuseStep 11414195 = 17121293) B17121293
theorem B1690411 : Blo 1502071 1690411 := bstep (se 1 (by rfl) ⟨1267808, by rfl⟩ : syracuseStep 1690411 = 2535617) B2535617
theorem B3803993 : Blo 1502071 3803993 := bstep (se 2 (by rfl) ⟨1426497, by rfl⟩ : syracuseStep 3803993 = 2852995) B2852995
theorem B28167011 : Blo 1502071 28167011 := bstep (se 1 (by rfl) ⟨21125258, by rfl⟩ : syracuseStep 28167011 = 42250517) B42250517
theorem B1502071 : Blo 1502071 1502071 := bstep (se 1 (by rfl) ⟨1126553, by rfl⟩ : syracuseStep 1502071 = 2253107) B2253107
theorem B1502091 : Blo 1502071 1502091 := bstep (se 1 (by rfl) ⟨1126568, by rfl⟩ : syracuseStep 1502091 = 2253137) B2253137
theorem B1502103 : Blo 1502071 1502103 := bstep (se 1 (by rfl) ⟨1126577, by rfl⟩ : syracuseStep 1502103 = 2253155) B2253155
theorem B1690519 : Blo 1502071 1690519 := bstep (se 1 (by rfl) ⟨1267889, by rfl⟩ : syracuseStep 1690519 = 2535779) B2535779
theorem B2853785 : Blo 1502071 2853785 := bstep (se 2 (by rfl) ⟨1070169, by rfl⟩ : syracuseStep 2853785 = 2140339) B2140339
theorem B1502123 : Blo 1502071 1502123 := bstep (se 1 (by rfl) ⟨1126592, by rfl⟩ : syracuseStep 1502123 = 2253185) B2253185
theorem B1502135 : Blo 1502071 1502135 := bstep (se 1 (by rfl) ⟨1126601, by rfl⟩ : syracuseStep 1502135 = 2253203) B2253203
theorem B5417921 : Blo 1502071 5417921 := bstep (se 2 (by rfl) ⟨2031720, by rfl⟩ : syracuseStep 5417921 = 4063441) B4063441
theorem B1502155 : Blo 1502071 1502155 := bstep (se 1 (by rfl) ⟨1126616, by rfl⟩ : syracuseStep 1502155 = 2253233) B2253233
theorem B1502167 : Blo 1502071 1502167 := bstep (se 1 (by rfl) ⟨1126625, by rfl⟩ : syracuseStep 1502167 = 2253251) B2253251
theorem B1502187 : Blo 1502071 1502187 := bstep (se 1 (by rfl) ⟨1126640, by rfl⟩ : syracuseStep 1502187 = 2253281) B2253281
theorem B1502199 : Blo 1502071 1502199 := bstep (se 1 (by rfl) ⟨1126649, by rfl⟩ : syracuseStep 1502199 = 2253299) B2253299
theorem B1502219 : Blo 1502071 1502219 := bstep (se 1 (by rfl) ⟨1126664, by rfl⟩ : syracuseStep 1502219 = 2253329) B2253329
theorem B1502231 : Blo 1502071 1502231 := bstep (se 1 (by rfl) ⟨1126673, by rfl⟩ : syracuseStep 1502231 = 2253347) B2253347
theorem B1502251 : Blo 1502071 1502251 := bstep (se 1 (by rfl) ⟨1126688, by rfl⟩ : syracuseStep 1502251 = 2253377) B2253377
theorem B1502263 : Blo 1502071 1502263 := bstep (se 1 (by rfl) ⟨1126697, by rfl⟩ : syracuseStep 1502263 = 2253395) B2253395
theorem B1502283 : Blo 1502071 1502283 := bstep (se 1 (by rfl) ⟨1126712, by rfl⟩ : syracuseStep 1502283 = 2253425) B2253425
theorem B1690699 : Blo 1502071 1690699 := bstep (se 1 (by rfl) ⟨1268024, by rfl⟩ : syracuseStep 1690699 = 2536049) B2536049
theorem B1502295 : Blo 1502071 1502295 := bstep (se 1 (by rfl) ⟨1126721, by rfl⟩ : syracuseStep 1502295 = 2253443) B2253443
theorem B9137245 : Blo 1502071 9137245 := bstep (se 3 (by rfl) ⟨1713233, by rfl⟩ : syracuseStep 9137245 = 3426467) B3426467
theorem B1502315 : Blo 1502071 1502315 := bstep (se 1 (by rfl) ⟨1126736, by rfl⟩ : syracuseStep 1502315 = 2253473) B2253473
theorem B1502327 : Blo 1502071 1502327 := bstep (se 1 (by rfl) ⟨1126745, by rfl⟩ : syracuseStep 1502327 = 2253491) B2253491
theorem B1502347 : Blo 1502071 1502347 := bstep (se 1 (by rfl) ⟨1126760, by rfl⟩ : syracuseStep 1502347 = 2253521) B2253521
theorem B1502359 : Blo 1502071 1502359 := bstep (se 1 (by rfl) ⟨1126769, by rfl⟩ : syracuseStep 1502359 = 2253539) B2253539
theorem B1502379 : Blo 1502071 1502379 := bstep (se 1 (by rfl) ⟨1126784, by rfl⟩ : syracuseStep 1502379 = 2253569) B2253569
theorem B1502391 : Blo 1502071 1502391 := bstep (se 1 (by rfl) ⟨1126793, by rfl⟩ : syracuseStep 1502391 = 2253587) B2253587
theorem B1690807 : Blo 1502071 1690807 := bstep (se 1 (by rfl) ⟨1268105, by rfl⟩ : syracuseStep 1690807 = 2536211) B2536211
theorem B1502411 : Blo 1502071 1502411 := bstep (se 1 (by rfl) ⟨1126808, by rfl⟩ : syracuseStep 1502411 = 2253617) B2253617
theorem B1502423 : Blo 1502071 1502423 := bstep (se 1 (by rfl) ⟨1126817, by rfl⟩ : syracuseStep 1502423 = 2253635) B2253635
theorem B1502443 : Blo 1502071 1502443 := bstep (se 1 (by rfl) ⟨1126832, by rfl⟩ : syracuseStep 1502443 = 2253665) B2253665
theorem B26389745 : Blo 1502071 26389745 := bstep (se 2 (by rfl) ⟨9896154, by rfl⟩ : syracuseStep 26389745 = 19792309) B19792309
theorem B1502455 : Blo 1502071 1502455 := bstep (se 1 (by rfl) ⟨1126841, by rfl⟩ : syracuseStep 1502455 = 2253683) B2253683
theorem B1502475 : Blo 1502071 1502475 := bstep (se 1 (by rfl) ⟨1126856, by rfl⟩ : syracuseStep 1502475 = 2253713) B2253713
theorem B1502487 : Blo 1502071 1502487 := bstep (se 1 (by rfl) ⟨1126865, by rfl⟩ : syracuseStep 1502487 = 2253731) B2253731
theorem B1502507 : Blo 1502071 1502507 := bstep (se 1 (by rfl) ⟨1126880, by rfl⟩ : syracuseStep 1502507 = 2253761) B2253761
theorem B1502519 : Blo 1502071 1502519 := bstep (se 1 (by rfl) ⟨1126889, by rfl⟩ : syracuseStep 1502519 = 2253779) B2253779
theorem B1502539 : Blo 1502071 1502539 := bstep (se 1 (by rfl) ⟨1126904, by rfl⟩ : syracuseStep 1502539 = 2253809) B2253809
theorem B1502551 : Blo 1502071 1502551 := bstep (se 1 (by rfl) ⟨1126913, by rfl⟩ : syracuseStep 1502551 = 2253827) B2253827
theorem B1502571 : Blo 1502071 1502571 := bstep (se 1 (by rfl) ⟨1126928, by rfl⟩ : syracuseStep 1502571 = 2253857) B2253857
theorem B1690987 : Blo 1502071 1690987 := bstep (se 1 (by rfl) ⟨1268240, by rfl⟩ : syracuseStep 1690987 = 2536481) B2536481
theorem B1502583 : Blo 1502071 1502583 := bstep (se 1 (by rfl) ⟨1126937, by rfl⟩ : syracuseStep 1502583 = 2253875) B2253875
theorem B12520835 : Blo 1502071 12520835 := bstep (se 1 (by rfl) ⟨9390626, by rfl⟩ : syracuseStep 12520835 = 18781253) B18781253
theorem B1502603 : Blo 1502071 1502603 := bstep (se 1 (by rfl) ⟨1126952, by rfl⟩ : syracuseStep 1502603 = 2253905) B2253905
theorem B2534807 : Blo 1502071 2534807 := bstep (se 1 (by rfl) ⟨1901105, by rfl⟩ : syracuseStep 2534807 = 3802211) B3802211
theorem B1502615 : Blo 1502071 1502615 := bstep (se 1 (by rfl) ⟨1126961, by rfl⟩ : syracuseStep 1502615 = 2253923) B2253923
theorem B1502635 : Blo 1502071 1502635 := bstep (se 1 (by rfl) ⟨1126976, by rfl⟩ : syracuseStep 1502635 = 2253953) B2253953
theorem B1502647 : Blo 1502071 1502647 := bstep (se 1 (by rfl) ⟨1126985, by rfl⟩ : syracuseStep 1502647 = 2253971) B2253971
theorem B1502667 : Blo 1502071 1502667 := bstep (se 1 (by rfl) ⟨1127000, by rfl⟩ : syracuseStep 1502667 = 2254001) B2254001
theorem B5074379 : Blo 1502071 5074379 := bstep (se 1 (by rfl) ⟨3805784, by rfl⟩ : syracuseStep 5074379 = 7611569) B7611569
theorem B1502679 : Blo 1502071 1502679 := bstep (se 1 (by rfl) ⟨1127009, by rfl⟩ : syracuseStep 1502679 = 2254019) B2254019
theorem B1691095 : Blo 1502071 1691095 := bstep (se 1 (by rfl) ⟨1268321, by rfl⟩ : syracuseStep 1691095 = 2536643) B2536643
theorem B1502699 : Blo 1502071 1502699 := bstep (se 1 (by rfl) ⟨1127024, by rfl⟩ : syracuseStep 1502699 = 2254049) B2254049
theorem B1502711 : Blo 1502071 1502711 := bstep (se 1 (by rfl) ⟨1127033, by rfl⟩ : syracuseStep 1502711 = 2254067) B2254067
theorem B1502731 : Blo 1502071 1502731 := bstep (se 1 (by rfl) ⟨1127048, by rfl⟩ : syracuseStep 1502731 = 2254097) B2254097
theorem B2534935 : Blo 1502071 2534935 := bstep (se 1 (by rfl) ⟨1901201, by rfl⟩ : syracuseStep 2534935 = 3802403) B3802403
theorem B1502743 : Blo 1502071 1502743 := bstep (se 1 (by rfl) ⟨1127057, by rfl⟩ : syracuseStep 1502743 = 2254115) B2254115
theorem B1502763 : Blo 1502071 1502763 := bstep (se 1 (by rfl) ⟨1127072, by rfl⟩ : syracuseStep 1502763 = 2254145) B2254145
theorem B5705261 : Blo 1502071 5705261 := bstep (se 3 (by rfl) ⟨1069736, by rfl⟩ : syracuseStep 5705261 = 2139473) B2139473
theorem B1502775 : Blo 1502071 1502775 := bstep (se 1 (by rfl) ⟨1127081, by rfl⟩ : syracuseStep 1502775 = 2254163) B2254163
theorem B1502795 : Blo 1502071 1502795 := bstep (se 1 (by rfl) ⟨1127096, by rfl⟩ : syracuseStep 1502795 = 2254193) B2254193
theorem B1502807 : Blo 1502071 1502807 := bstep (se 1 (by rfl) ⟨1127105, by rfl⟩ : syracuseStep 1502807 = 2254211) B2254211
theorem B1502827 : Blo 1502071 1502827 := bstep (se 1 (by rfl) ⟨1127120, by rfl⟩ : syracuseStep 1502827 = 2254241) B2254241
theorem B1502839 : Blo 1502071 1502839 := bstep (se 1 (by rfl) ⟨1127129, by rfl⟩ : syracuseStep 1502839 = 2254259) B2254259
theorem B1502859 : Blo 1502071 1502859 := bstep (se 1 (by rfl) ⟨1127144, by rfl⟩ : syracuseStep 1502859 = 2254289) B2254289
theorem B1691275 : Blo 1502071 1691275 := bstep (se 1 (by rfl) ⟨1268456, by rfl⟩ : syracuseStep 1691275 = 2536913) B2536913
theorem B1502871 : Blo 1502071 1502871 := bstep (se 1 (by rfl) ⟨1127153, by rfl⟩ : syracuseStep 1502871 = 2254307) B2254307
theorem B1502891 : Blo 1502071 1502891 := bstep (se 1 (by rfl) ⟨1127168, by rfl⟩ : syracuseStep 1502891 = 2254337) B2254337
theorem B1502903 : Blo 1502071 1502903 := bstep (se 1 (by rfl) ⟨1127177, by rfl⟩ : syracuseStep 1502903 = 2254355) B2254355
theorem B1502923 : Blo 1502071 1502923 := bstep (se 1 (by rfl) ⟨1127192, by rfl⟩ : syracuseStep 1502923 = 2254385) B2254385
theorem B1502935 : Blo 1502071 1502935 := bstep (se 1 (by rfl) ⟨1127201, by rfl⟩ : syracuseStep 1502935 = 2254403) B2254403
theorem B6090461 : Blo 1502071 6090461 := bstep (se 3 (by rfl) ⟨1141961, by rfl⟩ : syracuseStep 6090461 = 2283923) B2283923
theorem B1502955 : Blo 1502071 1502955 := bstep (se 1 (by rfl) ⟨1127216, by rfl⟩ : syracuseStep 1502955 = 2254433) B2254433
theorem B1502967 : Blo 1502071 1502967 := bstep (se 1 (by rfl) ⟨1127225, by rfl⟩ : syracuseStep 1502967 = 2254451) B2254451
theorem B1691383 : Blo 1502071 1691383 := bstep (se 1 (by rfl) ⟨1268537, by rfl⟩ : syracuseStep 1691383 = 2537075) B2537075
theorem B1502987 : Blo 1502071 1502987 := bstep (se 1 (by rfl) ⟨1127240, by rfl⟩ : syracuseStep 1502987 = 2254481) B2254481
theorem B1502999 : Blo 1502071 1502999 := bstep (se 1 (by rfl) ⟨1127249, by rfl⟩ : syracuseStep 1502999 = 2254499) B2254499
theorem B1503019 : Blo 1502071 1503019 := bstep (se 1 (by rfl) ⟨1127264, by rfl⟩ : syracuseStep 1503019 = 2254529) B2254529
theorem B7606061 : Blo 1502071 7606061 := bstep (se 3 (by rfl) ⟨1426136, by rfl⟩ : syracuseStep 7606061 = 2852273) B2852273
theorem B1503031 : Blo 1502071 1503031 := bstep (se 1 (by rfl) ⟨1127273, by rfl⟩ : syracuseStep 1503031 = 2254547) B2254547
theorem B1503051 : Blo 1502071 1503051 := bstep (se 1 (by rfl) ⟨1127288, by rfl⟩ : syracuseStep 1503051 = 2254577) B2254577
theorem B6950731 : Blo 1502071 6950731 := bstep (se 1 (by rfl) ⟨5213048, by rfl⟩ : syracuseStep 6950731 = 10426097) B10426097
theorem B1503063 : Blo 1502071 1503063 := bstep (se 1 (by rfl) ⟨1127297, by rfl⟩ : syracuseStep 1503063 = 2254595) B2254595
theorem B5418845 : Blo 1502071 5418845 := bstep (se 3 (by rfl) ⟨1016033, by rfl⟩ : syracuseStep 5418845 = 2032067) B2032067
theorem B1503083 : Blo 1502071 1503083 := bstep (se 1 (by rfl) ⟨1127312, by rfl⟩ : syracuseStep 1503083 = 2254625) B2254625
theorem B1503095 : Blo 1502071 1503095 := bstep (se 1 (by rfl) ⟨1127321, by rfl⟩ : syracuseStep 1503095 = 2254643) B2254643
theorem B1503115 : Blo 1502071 1503115 := bstep (se 1 (by rfl) ⟨1127336, by rfl⟩ : syracuseStep 1503115 = 2254673) B2254673
theorem B1503127 : Blo 1502071 1503127 := bstep (se 1 (by rfl) ⟨1127345, by rfl⟩ : syracuseStep 1503127 = 2254691) B2254691
theorem B1503147 : Blo 1502071 1503147 := bstep (se 1 (by rfl) ⟨1127360, by rfl⟩ : syracuseStep 1503147 = 2254721) B2254721
theorem B14274481 : Blo 1502071 14274481 := bstep (se 2 (by rfl) ⟨5352930, by rfl⟩ : syracuseStep 14274481 = 10705861) B10705861
theorem B1503159 : Blo 1502071 1503159 := bstep (se 1 (by rfl) ⟨1127369, by rfl⟩ : syracuseStep 1503159 = 2254739) B2254739
theorem B1503179 : Blo 1502071 1503179 := bstep (se 1 (by rfl) ⟨1127384, by rfl⟩ : syracuseStep 1503179 = 2254769) B2254769
theorem B1503191 : Blo 1502071 1503191 := bstep (se 1 (by rfl) ⟨1127393, by rfl⟩ : syracuseStep 1503191 = 2254787) B2254787
theorem B1503211 : Blo 1502071 1503211 := bstep (se 1 (by rfl) ⟨1127408, by rfl⟩ : syracuseStep 1503211 = 2254817) B2254817
theorem B1503223 : Blo 1502071 1503223 := bstep (se 1 (by rfl) ⟨1127417, by rfl⟩ : syracuseStep 1503223 = 2254835) B2254835
theorem B6418435 : Blo 1502071 6418435 := bstep (se 1 (by rfl) ⟨4813826, by rfl⟩ : syracuseStep 6418435 = 9627653) B9627653
theorem B1503243 : Blo 1502071 1503243 := bstep (se 1 (by rfl) ⟨1127432, by rfl⟩ : syracuseStep 1503243 = 2254865) B2254865
theorem B1503255 : Blo 1502071 1503255 := bstep (se 1 (by rfl) ⟨1127441, by rfl⟩ : syracuseStep 1503255 = 2254883) B2254883
theorem B1503275 : Blo 1502071 1503275 := bstep (se 1 (by rfl) ⟨1127456, by rfl⟩ : syracuseStep 1503275 = 2254913) B2254913
theorem B1503287 : Blo 1502071 1503287 := bstep (se 1 (by rfl) ⟨1127465, by rfl⟩ : syracuseStep 1503287 = 2254931) B2254931
theorem B1503307 : Blo 1502071 1503307 := bstep (se 1 (by rfl) ⟨1127480, by rfl⟩ : syracuseStep 1503307 = 2254961) B2254961
theorem B1503319 : Blo 1502071 1503319 := bstep (se 1 (by rfl) ⟨1127489, by rfl⟩ : syracuseStep 1503319 = 2254979) B2254979
theorem B8556637 : Blo 1502071 8556637 := bstep (se 3 (by rfl) ⟨1604369, by rfl⟩ : syracuseStep 8556637 = 3208739) B3208739
theorem B11415653 : Blo 1502071 11415653 := bstep (se 4 (by rfl) ⟨1070217, by rfl⟩ : syracuseStep 11415653 = 2140435) B2140435
theorem B1503339 : Blo 1502071 1503339 := bstep (se 1 (by rfl) ⟨1127504, by rfl⟩ : syracuseStep 1503339 = 2255009) B2255009
theorem B1503351 : Blo 1502071 1503351 := bstep (se 1 (by rfl) ⟨1127513, by rfl⟩ : syracuseStep 1503351 = 2255027) B2255027
theorem B2535563 : Blo 1502071 2535563 := bstep (se 1 (by rfl) ⟨1901672, by rfl⟩ : syracuseStep 2535563 = 3803345) B3803345
theorem B1503371 : Blo 1502071 1503371 := bstep (se 1 (by rfl) ⟨1127528, by rfl⟩ : syracuseStep 1503371 = 2255057) B2255057
theorem B1503383 : Blo 1502071 1503383 := bstep (se 1 (by rfl) ⟨1127537, by rfl⟩ : syracuseStep 1503383 = 2255075) B2255075
theorem B1503403 : Blo 1502071 1503403 := bstep (se 1 (by rfl) ⟨1127552, by rfl⟩ : syracuseStep 1503403 = 2255105) B2255105
theorem B12185777 : Blo 1502071 12185777 := bstep (se 2 (by rfl) ⟨4569666, by rfl⟩ : syracuseStep 12185777 = 9139333) B9139333
theorem B1503415 : Blo 1502071 1503415 := bstep (se 1 (by rfl) ⟨1127561, by rfl⟩ : syracuseStep 1503415 = 2255123) B2255123
theorem B1503435 : Blo 1502071 1503435 := bstep (se 1 (by rfl) ⟨1127576, by rfl⟩ : syracuseStep 1503435 = 2255153) B2255153
theorem B1503447 : Blo 1502071 1503447 := bstep (se 1 (by rfl) ⟨1127585, by rfl⟩ : syracuseStep 1503447 = 2255171) B2255171
theorem B1503467 : Blo 1502071 1503467 := bstep (se 1 (by rfl) ⟨1127600, by rfl⟩ : syracuseStep 1503467 = 2255201) B2255201
theorem B1503479 : Blo 1502071 1503479 := bstep (se 1 (by rfl) ⟨1127609, by rfl⟩ : syracuseStep 1503479 = 2255219) B2255219
theorem B2535691 : Blo 1502071 2535691 := bstep (se 1 (by rfl) ⟨1901768, by rfl⟩ : syracuseStep 2535691 = 3803537) B3803537
theorem B1503499 : Blo 1502071 1503499 := bstep (se 1 (by rfl) ⟨1127624, by rfl⟩ : syracuseStep 1503499 = 2255249) B2255249
theorem B1503511 : Blo 1502071 1503511 := bstep (se 1 (by rfl) ⟨1127633, by rfl⟩ : syracuseStep 1503511 = 2255267) B2255267
theorem B1503531 : Blo 1502071 1503531 := bstep (se 1 (by rfl) ⟨1127648, by rfl⟩ : syracuseStep 1503531 = 2255297) B2255297
theorem B5706035 : Blo 1502071 5706035 := bstep (se 1 (by rfl) ⟨4279526, by rfl⟩ : syracuseStep 5706035 = 8559053) B8559053
theorem B1503543 : Blo 1502071 1503543 := bstep (se 1 (by rfl) ⟨1127657, by rfl⟩ : syracuseStep 1503543 = 2255315) B2255315
theorem B1503563 : Blo 1502071 1503563 := bstep (se 1 (by rfl) ⟨1127672, by rfl⟩ : syracuseStep 1503563 = 2255345) B2255345
theorem B6418777 : Blo 1502071 6418777 := bstep (se 2 (by rfl) ⟨2407041, by rfl⟩ : syracuseStep 6418777 = 4814083) B4814083
theorem B2535833 : Blo 1502071 2535833 := bstep (se 2 (by rfl) ⟨950937, by rfl⟩ : syracuseStep 2535833 = 1901875) B1901875
theorem B4280779 : Blo 1502071 4280779 := bstep (se 1 (by rfl) ⟨3210584, by rfl⟩ : syracuseStep 4280779 = 6421169) B6421169
theorem B3805643 : Blo 1502071 3805643 := bstep (se 1 (by rfl) ⟨2854232, by rfl⟩ : syracuseStep 3805643 = 5708465) B5708465
theorem B11407877 : Blo 1502071 11407877 := bstep (se 4 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 11407877 = 2138977) B2138977
theorem B2535961 : Blo 1502071 2535961 := bstep (se 2 (by rfl) ⟨950985, by rfl⟩ : syracuseStep 2535961 = 1901971) B1901971
theorem B12841517 : Blo 1502071 12841517 := bstep (se 3 (by rfl) ⟨2407784, by rfl⟩ : syracuseStep 12841517 = 4815569) B4815569
theorem B4878913 : Blo 1502071 4878913 := bstep (se 2 (by rfl) ⟨1829592, by rfl⟩ : syracuseStep 4878913 = 3659185) B3659185
theorem B3379787 : Blo 1502071 3379787 := bstep (se 1 (by rfl) ⟨2534840, by rfl⟩ : syracuseStep 3379787 = 5069681) B5069681
theorem B11416139 : Blo 1502071 11416139 := bstep (se 1 (by rfl) ⟨8562104, by rfl⟩ : syracuseStep 11416139 = 17124209) B17124209
theorem B9261661 : Blo 1502071 9261661 := bstep (se 3 (by rfl) ⟨1736561, by rfl⟩ : syracuseStep 9261661 = 3473123) B3473123
theorem B3379841 : Blo 1502071 3379841 := bstep (se 2 (by rfl) ⟨1267440, by rfl⟩ : syracuseStep 3379841 = 2534881) B2534881
theorem B3855127 : Blo 1502071 3855127 := bstep (se 1 (by rfl) ⟨2891345, by rfl⟩ : syracuseStep 3855127 = 5782691) B5782691
theorem B3380057 : Blo 1502071 3380057 := bstep (se 2 (by rfl) ⟨1267521, by rfl⟩ : syracuseStep 3380057 = 2535043) B2535043
theorem B11572145 : Blo 1502071 11572145 := bstep (se 2 (by rfl) ⟨4339554, by rfl⟩ : syracuseStep 11572145 = 8679109) B8679109
theorem B3380147 : Blo 1502071 3380147 := bstep (se 1 (by rfl) ⟨2535110, by rfl⟩ : syracuseStep 3380147 = 5070221) B5070221
theorem B4281281 : Blo 1502071 4281281 := bstep (se 2 (by rfl) ⟨1605480, by rfl⟩ : syracuseStep 4281281 = 3210961) B3210961
theorem B3380183 : Blo 1502071 3380183 := bstep (se 1 (by rfl) ⟨2535137, by rfl⟩ : syracuseStep 3380183 = 5070275) B5070275
theorem B2536535 : Blo 1502071 2536535 := bstep (se 1 (by rfl) ⟨1902401, by rfl⟩ : syracuseStep 2536535 = 3804803) B3804803
theorem B3380363 : Blo 1502071 3380363 := bstep (se 1 (by rfl) ⟨2535272, by rfl⟩ : syracuseStep 3380363 = 5070545) B5070545
theorem B9761971 : Blo 1502071 9761971 := bstep (se 1 (by rfl) ⟨7321478, by rfl⟩ : syracuseStep 9761971 = 14642957) B14642957
theorem B3380417 : Blo 1502071 3380417 := bstep (se 2 (by rfl) ⟨1267656, by rfl⟩ : syracuseStep 3380417 = 2535313) B2535313
theorem B2536663 : Blo 1502071 2536663 := bstep (se 1 (by rfl) ⟨1902497, by rfl⟩ : syracuseStep 2536663 = 3804995) B3804995
theorem B6419735 : Blo 1502071 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B4281623 : Blo 1502071 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B2168203 : Blo 1502071 2168203 := bstep (se 1 (by rfl) ⟨1626152, by rfl⟩ : syracuseStep 2168203 = 3252305) B3252305
theorem B3380633 : Blo 1502071 3380633 := bstep (se 2 (by rfl) ⟨1267737, by rfl⟩ : syracuseStep 3380633 = 2535475) B2535475
theorem B4060619 : Blo 1502071 4060619 := bstep (se 1 (by rfl) ⟨3045464, by rfl⟩ : syracuseStep 4060619 = 6090929) B6090929
theorem B3208663 : Blo 1502071 3208663 := bstep (se 1 (by rfl) ⟨2406497, by rfl⟩ : syracuseStep 3208663 = 4812995) B4812995
theorem B3380723 : Blo 1502071 3380723 := bstep (se 1 (by rfl) ⟨2535542, by rfl⟩ : syracuseStep 3380723 = 5071085) B5071085
theorem B3380759 : Blo 1502071 3380759 := bstep (se 1 (by rfl) ⟨2535569, by rfl⟩ : syracuseStep 3380759 = 5071139) B5071139
theorem B7222877 : Blo 1502071 7222877 := bstep (se 3 (by rfl) ⟨1354289, by rfl⟩ : syracuseStep 7222877 = 2708579) B2708579
theorem B3380939 : Blo 1502071 3380939 := bstep (se 1 (by rfl) ⟨2535704, by rfl⟩ : syracuseStep 3380939 = 5071409) B5071409
theorem B3380993 : Blo 1502071 3380993 := bstep (se 2 (by rfl) ⟨1267872, by rfl⟩ : syracuseStep 3380993 = 2535745) B2535745
theorem B5707523 : Blo 1502071 5707523 := bstep (se 1 (by rfl) ⟨4280642, by rfl⟩ : syracuseStep 5707523 = 8561285) B8561285
theorem B2709335 : Blo 1502071 2709335 := bstep (se 1 (by rfl) ⟨2032001, by rfl⟩ : syracuseStep 2709335 = 4064003) B4064003
theorem B11564977 : Blo 1502071 11564977 := bstep (se 2 (by rfl) ⟨4336866, by rfl⟩ : syracuseStep 11564977 = 8673733) B8673733
theorem B3381209 : Blo 1502071 3381209 := bstep (se 2 (by rfl) ⟨1267953, by rfl⟩ : syracuseStep 3381209 = 2535907) B2535907
theorem B8124461 : Blo 1502071 8124461 := bstep (se 3 (by rfl) ⟨1523336, by rfl⟩ : syracuseStep 8124461 = 3046673) B3046673
theorem B3381299 : Blo 1502071 3381299 := bstep (se 1 (by rfl) ⟨2535974, by rfl⟩ : syracuseStep 3381299 = 5071949) B5071949
theorem B3381335 : Blo 1502071 3381335 := bstep (se 1 (by rfl) ⟨2536001, by rfl⟩ : syracuseStep 3381335 = 5072003) B5072003
theorem B2570329 : Blo 1502071 2570329 := bstep (se 2 (by rfl) ⟨963873, by rfl⟩ : syracuseStep 2570329 = 1927747) B1927747
theorem B5707979 : Blo 1502071 5707979 := bstep (se 1 (by rfl) ⟨4280984, by rfl⟩ : syracuseStep 5707979 = 8561969) B8561969
theorem B3209483 : Blo 1502071 3209483 := bstep (se 1 (by rfl) ⟨2407112, by rfl⟩ : syracuseStep 3209483 = 4814225) B4814225
theorem B3381515 : Blo 1502071 3381515 := bstep (se 1 (by rfl) ⟨2536136, by rfl⟩ : syracuseStep 3381515 = 5072273) B5072273
theorem B2570521 : Blo 1502071 2570521 := bstep (se 2 (by rfl) ⟨963945, by rfl⟩ : syracuseStep 2570521 = 1927891) B1927891
theorem B14448941 : Blo 1502071 14448941 := bstep (se 3 (by rfl) ⟨2709176, by rfl⟩ : syracuseStep 14448941 = 5418353) B5418353
theorem B3381569 : Blo 1502071 3381569 := bstep (se 2 (by rfl) ⟨1268088, by rfl⟩ : syracuseStep 3381569 = 2536177) B2536177
theorem B5708177 : Blo 1502071 5708177 := bstep (se 2 (by rfl) ⟨2140566, by rfl⟩ : syracuseStep 5708177 = 4281133) B4281133
theorem B12188083 : Blo 1502071 12188083 := bstep (se 1 (by rfl) ⟨9141062, by rfl⟩ : syracuseStep 12188083 = 18282125) B18282125
theorem B3611159 : Blo 1502071 3611159 := bstep (se 1 (by rfl) ⟨2708369, by rfl⟩ : syracuseStep 3611159 = 5416739) B5416739
theorem B3381785 : Blo 1502071 3381785 := bstep (se 2 (by rfl) ⟨1268169, by rfl⟩ : syracuseStep 3381785 = 2536339) B2536339
theorem B3381875 : Blo 1502071 3381875 := bstep (se 1 (by rfl) ⟨2536406, by rfl⟩ : syracuseStep 3381875 = 5072813) B5072813
theorem B21674627 : Blo 1502071 21674627 := bstep (se 1 (by rfl) ⟨16255970, by rfl⟩ : syracuseStep 21674627 = 32511941) B32511941
theorem B3381911 : Blo 1502071 3381911 := bstep (se 1 (by rfl) ⟨2536433, by rfl⟩ : syracuseStep 3381911 = 5072867) B5072867
theorem B6945581 : Blo 1502071 6945581 := bstep (se 3 (by rfl) ⟨1302296, by rfl⟩ : syracuseStep 6945581 = 2604593) B2604593
theorem B3382091 : Blo 1502071 3382091 := bstep (se 1 (by rfl) ⟨2536568, by rfl⟩ : syracuseStep 3382091 = 5073137) B5073137
theorem B3382145 : Blo 1502071 3382145 := bstep (se 2 (by rfl) ⟨1268304, by rfl⟩ : syracuseStep 3382145 = 2536609) B2536609
theorem B11410307 : Blo 1502071 11410307 := bstep (se 1 (by rfl) ⟨8557730, by rfl⟩ : syracuseStep 11410307 = 17115461) B17115461
theorem B6421427 : Blo 1502071 6421427 := bstep (se 1 (by rfl) ⟨4816070, by rfl⟩ : syracuseStep 6421427 = 9632141) B9632141
theorem B5413825 : Blo 1502071 5413825 := bstep (se 2 (by rfl) ⟨2030184, by rfl⟩ : syracuseStep 5413825 = 4060369) B4060369
theorem B5069789 : Blo 1502071 5069789 := bstep (se 3 (by rfl) ⟨950585, by rfl⟩ : syracuseStep 5069789 = 1901171) B1901171
theorem B2030617 : Blo 1502071 2030617 := bstep (se 2 (by rfl) ⟨761481, by rfl⟩ : syracuseStep 2030617 = 1522963) B1522963
theorem B3210329 : Blo 1502071 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B3382361 : Blo 1502071 3382361 := bstep (se 2 (by rfl) ⟨1268385, by rfl⟩ : syracuseStep 3382361 = 2536771) B2536771
theorem B4062359 : Blo 1502071 4062359 := bstep (se 1 (by rfl) ⟨3046769, by rfl⟩ : syracuseStep 4062359 = 6093539) B6093539
theorem B3382451 : Blo 1502071 3382451 := bstep (se 1 (by rfl) ⟨2536838, by rfl⟩ : syracuseStep 3382451 = 5073677) B5073677
theorem B3382487 : Blo 1502071 3382487 := bstep (se 1 (by rfl) ⟨2536865, by rfl⟩ : syracuseStep 3382487 = 5073731) B5073731
theorem B3382667 : Blo 1502071 3382667 := bstep (se 1 (by rfl) ⟨2537000, by rfl⟩ : syracuseStep 3382667 = 5074001) B5074001
theorem B3046835 : Blo 1502071 3046835 := bstep (se 1 (by rfl) ⟨2285126, by rfl⟩ : syracuseStep 3046835 = 4570253) B4570253
theorem B3382721 : Blo 1502071 3382721 := bstep (se 2 (by rfl) ⟨1268520, by rfl⟩ : syracuseStep 3382721 = 2537041) B2537041
theorem B12844493 : Blo 1502071 12844493 := bstep (se 3 (by rfl) ⟨2408342, by rfl⟩ : syracuseStep 12844493 = 4816685) B4816685
theorem B7609949 : Blo 1502071 7609949 := bstep (se 3 (by rfl) ⟨1426865, by rfl⟩ : syracuseStep 7609949 = 2853731) B2853731
theorem B2743961 : Blo 1502071 2743961 := bstep (se 2 (by rfl) ⟨1028985, by rfl⟩ : syracuseStep 2743961 = 2057971) B2057971
theorem B3382937 : Blo 1502071 3382937 := bstep (se 2 (by rfl) ⟨1268601, by rfl⟩ : syracuseStep 3382937 = 2537203) B2537203
theorem B4062923 : Blo 1502071 4062923 := bstep (se 1 (by rfl) ⟨3047192, by rfl⟩ : syracuseStep 4062923 = 6094385) B6094385
theorem B2285273 : Blo 1502071 2285273 := bstep (se 2 (by rfl) ⟨856977, by rfl⟩ : syracuseStep 2285273 = 1713955) B1713955
theorem B3210995 : Blo 1502071 3210995 := bstep (se 1 (by rfl) ⟨2408246, by rfl⟩ : syracuseStep 3210995 = 4816493) B4816493
theorem B3383027 : Blo 1502071 3383027 := bstep (se 1 (by rfl) ⟨2537270, by rfl⟩ : syracuseStep 3383027 = 5074541) B5074541
theorem B4063051 : Blo 1502071 4063051 := bstep (se 1 (by rfl) ⟨3047288, by rfl⟩ : syracuseStep 4063051 = 6094577) B6094577
theorem B1605463 : Blo 1502071 1605463 := bstep (se 1 (by rfl) ⟨1204097, by rfl⟩ : syracuseStep 1605463 = 2408195) B2408195
theorem B6504343 : Blo 1502071 6504343 := bstep (se 1 (by rfl) ⟨4878257, by rfl⟩ : syracuseStep 6504343 = 9756515) B9756515
theorem B7610435 : Blo 1502071 7610435 := bstep (se 1 (by rfl) ⟨5707826, by rfl⟩ : syracuseStep 7610435 = 11415653) B11415653
theorem B1523855 : Blo 1502071 1523855 := bstep (se 1 (by rfl) ⟨1142891, by rfl⟩ : syracuseStep 1523855 = 2285783) B2285783
theorem B2253113 : Blo 1502071 2253113 := bstep (se 2 (by rfl) ⟨844917, by rfl⟩ : syracuseStep 2253113 = 1689835) B1689835
theorem B8561011 : Blo 1502071 8561011 := bstep (se 1 (by rfl) ⟨6420758, by rfl⟩ : syracuseStep 8561011 = 12841517) B12841517
theorem B2253191 : Blo 1502071 2253191 := bstep (se 1 (by rfl) ⟨1689893, by rfl⟩ : syracuseStep 2253191 = 3379787) B3379787
theorem B7610759 : Blo 1502071 7610759 := bstep (se 1 (by rfl) ⟨5708069, by rfl⟩ : syracuseStep 7610759 = 11416139) B11416139
theorem B2253227 : Blo 1502071 2253227 := bstep (se 1 (by rfl) ⟨1689920, by rfl⟩ : syracuseStep 2253227 = 3379841) B3379841
theorem B2253257 : Blo 1502071 2253257 := bstep (se 2 (by rfl) ⟨844971, by rfl⟩ : syracuseStep 2253257 = 1689943) B1689943
theorem B2253371 : Blo 1502071 2253371 := bstep (se 1 (by rfl) ⟨1690028, by rfl⟩ : syracuseStep 2253371 = 3380057) B3380057
theorem B2253431 : Blo 1502071 2253431 := bstep (se 1 (by rfl) ⟨1690073, by rfl⟩ : syracuseStep 2253431 = 3380147) B3380147
theorem B2253455 : Blo 1502071 2253455 := bstep (se 1 (by rfl) ⟨1690091, by rfl⟩ : syracuseStep 2253455 = 3380183) B3380183
theorem B1901227 : Blo 1502071 1901227 := bstep (se 1 (by rfl) ⟨1425920, by rfl⟩ : syracuseStep 1901227 = 2851841) B2851841
theorem B2253497 : Blo 1502071 2253497 := bstep (se 2 (by rfl) ⟨845061, by rfl⟩ : syracuseStep 2253497 = 1690123) B1690123
theorem B6505217 : Blo 1502071 6505217 := bstep (se 2 (by rfl) ⟨2439456, by rfl⟩ : syracuseStep 6505217 = 4878913) B4878913
theorem B2253575 : Blo 1502071 2253575 := bstep (se 1 (by rfl) ⟨1690181, by rfl⟩ : syracuseStep 2253575 = 3380363) B3380363
theorem B2253611 : Blo 1502071 2253611 := bstep (se 1 (by rfl) ⟨1690208, by rfl⟩ : syracuseStep 2253611 = 3380417) B3380417
theorem B2253641 : Blo 1502071 2253641 := bstep (se 2 (by rfl) ⟨845115, by rfl⟩ : syracuseStep 2253641 = 1690231) B1690231
theorem B2253755 : Blo 1502071 2253755 := bstep (se 1 (by rfl) ⟨1690316, by rfl⟩ : syracuseStep 2253755 = 3380633) B3380633
theorem B2253815 : Blo 1502071 2253815 := bstep (se 1 (by rfl) ⟨1690361, by rfl⟩ : syracuseStep 2253815 = 3380723) B3380723
theorem B2253839 : Blo 1502071 2253839 := bstep (se 1 (by rfl) ⟨1690379, by rfl⟩ : syracuseStep 2253839 = 3380759) B3380759
theorem B2253881 : Blo 1502071 2253881 := bstep (se 2 (by rfl) ⟨845205, by rfl⟩ : syracuseStep 2253881 = 1690411) B1690411
theorem B6505591 : Blo 1502071 6505591 := bstep (se 1 (by rfl) ⟨4879193, by rfl⟩ : syracuseStep 6505591 = 9758387) B9758387
theorem B2253959 : Blo 1502071 2253959 := bstep (se 1 (by rfl) ⟨1690469, by rfl⟩ : syracuseStep 2253959 = 3380939) B3380939
theorem B2253995 : Blo 1502071 2253995 := bstep (se 1 (by rfl) ⟨1690496, by rfl⟩ : syracuseStep 2253995 = 3380993) B3380993
theorem B16475309 : Blo 1502071 16475309 := bstep (se 3 (by rfl) ⟨3089120, by rfl⟩ : syracuseStep 16475309 = 6178241) B6178241
theorem B2254025 : Blo 1502071 2254025 := bstep (se 2 (by rfl) ⟨845259, by rfl⟩ : syracuseStep 2254025 = 1690519) B1690519
theorem B7218433 : Blo 1502071 7218433 := bstep (se 2 (by rfl) ⟨2706912, by rfl⟩ : syracuseStep 7218433 = 5413825) B5413825
theorem B2254139 : Blo 1502071 2254139 := bstep (se 1 (by rfl) ⟨1690604, by rfl⟩ : syracuseStep 2254139 = 3381209) B3381209
theorem B5416307 : Blo 1502071 5416307 := bstep (se 1 (by rfl) ⟨4062230, by rfl⟩ : syracuseStep 5416307 = 8124461) B8124461
theorem B2254199 : Blo 1502071 2254199 := bstep (se 1 (by rfl) ⟨1690649, by rfl⟩ : syracuseStep 2254199 = 3381299) B3381299
theorem B2254223 : Blo 1502071 2254223 := bstep (se 1 (by rfl) ⟨1690667, by rfl⟩ : syracuseStep 2254223 = 3381335) B3381335
theorem B2852243 : Blo 1502071 2852243 := bstep (se 1 (by rfl) ⟨2139182, by rfl⟩ : syracuseStep 2852243 = 4278365) B4278365
theorem B2254265 : Blo 1502071 2254265 := bstep (se 2 (by rfl) ⟨845349, by rfl⟩ : syracuseStep 2254265 = 1690699) B1690699
theorem B12182993 : Blo 1502071 12182993 := bstep (se 2 (by rfl) ⟨4568622, by rfl⟩ : syracuseStep 12182993 = 9137245) B9137245
theorem B2254343 : Blo 1502071 2254343 := bstep (se 1 (by rfl) ⟨1690757, by rfl⟩ : syracuseStep 2254343 = 3381515) B3381515
theorem B2254379 : Blo 1502071 2254379 := bstep (se 1 (by rfl) ⟨1690784, by rfl⟩ : syracuseStep 2254379 = 3381569) B3381569
theorem B2254409 : Blo 1502071 2254409 := bstep (se 2 (by rfl) ⟨845403, by rfl⟩ : syracuseStep 2254409 = 1690807) B1690807
theorem B2852471 : Blo 1502071 2852471 := bstep (se 1 (by rfl) ⟨2139353, by rfl⟩ : syracuseStep 2852471 = 4278707) B4278707
theorem B1902199 : Blo 1502071 1902199 := bstep (se 1 (by rfl) ⟨1426649, by rfl⟩ : syracuseStep 1902199 = 2853299) B2853299
theorem B2254523 : Blo 1502071 2254523 := bstep (se 1 (by rfl) ⟨1690892, by rfl⟩ : syracuseStep 2254523 = 3381785) B3381785
theorem B7317229 : Blo 1502071 7317229 := bstep (se 3 (by rfl) ⟨1371980, by rfl⟩ : syracuseStep 7317229 = 2743961) B2743961
theorem B5490413 : Blo 1502071 5490413 := bstep (se 3 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 5490413 = 2058905) B2058905
theorem B2254583 : Blo 1502071 2254583 := bstep (se 1 (by rfl) ⟨1690937, by rfl⟩ : syracuseStep 2254583 = 3381875) B3381875
theorem B2254607 : Blo 1502071 2254607 := bstep (se 1 (by rfl) ⟨1690955, by rfl⟩ : syracuseStep 2254607 = 3381911) B3381911
theorem B8562469 : Blo 1502071 8562469 := bstep (se 4 (by rfl) ⟨802731, by rfl⟩ : syracuseStep 8562469 = 1605463) B1605463
theorem B2254649 : Blo 1502071 2254649 := bstep (se 2 (by rfl) ⟨845493, by rfl⟩ : syracuseStep 2254649 = 1690987) B1690987
theorem B4630387 : Blo 1502071 4630387 := bstep (se 1 (by rfl) ⟨3472790, by rfl⟩ : syracuseStep 4630387 = 6945581) B6945581
theorem B2254727 : Blo 1502071 2254727 := bstep (se 1 (by rfl) ⟨1691045, by rfl⟩ : syracuseStep 2254727 = 3382091) B3382091
theorem B18778007 : Blo 1502071 18778007 := bstep (se 1 (by rfl) ⟨14083505, by rfl⟩ : syracuseStep 18778007 = 28167011) B28167011
theorem B2254763 : Blo 1502071 2254763 := bstep (se 1 (by rfl) ⟨1691072, by rfl⟩ : syracuseStep 2254763 = 3382145) B3382145
theorem B1902523 : Blo 1502071 1902523 := bstep (se 1 (by rfl) ⟨1426892, by rfl⟩ : syracuseStep 1902523 = 2853785) B2853785
theorem B4278217 : Blo 1502071 4278217 := bstep (se 2 (by rfl) ⟨1604331, by rfl⟩ : syracuseStep 4278217 = 3208663) B3208663
theorem B2254793 : Blo 1502071 2254793 := bstep (se 2 (by rfl) ⟨845547, by rfl⟩ : syracuseStep 2254793 = 1691095) B1691095
theorem B2140219 : Blo 1502071 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B2254907 : Blo 1502071 2254907 := bstep (se 1 (by rfl) ⟨1691180, by rfl⟩ : syracuseStep 2254907 = 3382361) B3382361
theorem B2254967 : Blo 1502071 2254967 := bstep (se 1 (by rfl) ⟨1691225, by rfl⟩ : syracuseStep 2254967 = 3382451) B3382451
theorem B2254991 : Blo 1502071 2254991 := bstep (se 1 (by rfl) ⟨1691243, by rfl⟩ : syracuseStep 2254991 = 3382487) B3382487
theorem B2255033 : Blo 1502071 2255033 := bstep (se 2 (by rfl) ⟨845637, by rfl⟩ : syracuseStep 2255033 = 1691275) B1691275
theorem B2255111 : Blo 1502071 2255111 := bstep (se 1 (by rfl) ⟨1691333, by rfl⟩ : syracuseStep 2255111 = 3382667) B3382667
theorem B1689871 : Blo 1502071 1689871 := bstep (se 1 (by rfl) ⟨1267403, by rfl⟩ : syracuseStep 1689871 = 2534807) B2534807
theorem B2255147 : Blo 1502071 2255147 := bstep (se 1 (by rfl) ⟨1691360, by rfl⟩ : syracuseStep 2255147 = 3382721) B3382721
theorem B8562995 : Blo 1502071 8562995 := bstep (se 1 (by rfl) ⟨6422246, by rfl⟩ : syracuseStep 8562995 = 12844493) B12844493
theorem B2255177 : Blo 1502071 2255177 := bstep (se 2 (by rfl) ⟨845691, by rfl⟩ : syracuseStep 2255177 = 1691383) B1691383
theorem B3803507 : Blo 1502071 3803507 := bstep (se 1 (by rfl) ⟨2852630, by rfl⟩ : syracuseStep 3803507 = 5705261) B5705261
theorem B5073299 : Blo 1502071 5073299 := bstep (se 1 (by rfl) ⟨3804974, by rfl⟩ : syracuseStep 5073299 = 7609949) B7609949
theorem B5704121 : Blo 1502071 5704121 := bstep (se 2 (by rfl) ⟨2139045, by rfl⟩ : syracuseStep 5704121 = 4278091) B4278091
theorem B5417401 : Blo 1502071 5417401 := bstep (se 2 (by rfl) ⟨2031525, by rfl⟩ : syracuseStep 5417401 = 4063051) B4063051
theorem B9267641 : Blo 1502071 9267641 := bstep (se 2 (by rfl) ⟨3475365, by rfl⟩ : syracuseStep 9267641 = 6950731) B6950731
theorem B2255291 : Blo 1502071 2255291 := bstep (se 1 (by rfl) ⟨1691468, by rfl⟩ : syracuseStep 2255291 = 3382937) B3382937
theorem B2140663 : Blo 1502071 2140663 := bstep (se 1 (by rfl) ⟨1605497, by rfl⟩ : syracuseStep 2140663 = 3210995) B3210995
theorem B2255351 : Blo 1502071 2255351 := bstep (se 1 (by rfl) ⟨1691513, by rfl⟩ : syracuseStep 2255351 = 3383027) B3383027
theorem B7604765 : Blo 1502071 7604765 := bstep (se 3 (by rfl) ⟨1425893, by rfl⟩ : syracuseStep 7604765 = 2851787) B2851787
theorem B19032641 : Blo 1502071 19032641 := bstep (se 2 (by rfl) ⟨7137240, by rfl⟩ : syracuseStep 19032641 = 14274481) B14274481
theorem B15419969 : Blo 1502071 15419969 := bstep (se 2 (by rfl) ⟨5782488, by rfl⟩ : syracuseStep 15419969 = 11564977) B11564977
theorem B28879577 : Blo 1502071 28879577 := bstep (se 2 (by rfl) ⟨10829841, by rfl⟩ : syracuseStep 28879577 = 21659683) B21659683
theorem B1690375 : Blo 1502071 1690375 := bstep (se 1 (by rfl) ⟨1267781, by rfl⟩ : syracuseStep 1690375 = 2535563) B2535563
theorem B3427105 : Blo 1502071 3427105 := bstep (se 2 (by rfl) ⟨1285164, by rfl⟩ : syracuseStep 3427105 = 2570329) B2570329
theorem B3804023 : Blo 1502071 3804023 := bstep (se 1 (by rfl) ⟨2853017, by rfl⟩ : syracuseStep 3804023 = 5706035) B5706035
theorem B1502087 : Blo 1502071 1502087 := bstep (se 1 (by rfl) ⟨1126565, by rfl⟩ : syracuseStep 1502087 = 2253131) B2253131
theorem B1502095 : Blo 1502071 1502095 := bstep (se 1 (by rfl) ⟨1126571, by rfl⟩ : syracuseStep 1502095 = 2253143) B2253143
theorem B1502139 : Blo 1502071 1502139 := bstep (se 1 (by rfl) ⟨1126604, by rfl⟩ : syracuseStep 1502139 = 2253209) B2253209
theorem B1690555 : Blo 1502071 1690555 := bstep (se 1 (by rfl) ⟨1267916, by rfl⟩ : syracuseStep 1690555 = 2535833) B2535833
theorem B7605251 : Blo 1502071 7605251 := bstep (se 1 (by rfl) ⟨5703938, by rfl⟩ : syracuseStep 7605251 = 11407877) B11407877
theorem B1502215 : Blo 1502071 1502215 := bstep (se 1 (by rfl) ⟨1126661, by rfl⟩ : syracuseStep 1502215 = 2253323) B2253323
theorem B1502223 : Blo 1502071 1502223 := bstep (se 1 (by rfl) ⟨1126667, by rfl⟩ : syracuseStep 1502223 = 2253335) B2253335
theorem B3427361 : Blo 1502071 3427361 := bstep (se 2 (by rfl) ⟨1285260, by rfl⟩ : syracuseStep 3427361 = 2570521) B2570521
theorem B1502267 : Blo 1502071 1502267 := bstep (se 1 (by rfl) ⟨1126700, by rfl⟩ : syracuseStep 1502267 = 2253401) B2253401
theorem B1502343 : Blo 1502071 1502343 := bstep (se 1 (by rfl) ⟨1126757, by rfl⟩ : syracuseStep 1502343 = 2253515) B2253515
theorem B1502351 : Blo 1502071 1502351 := bstep (se 1 (by rfl) ⟨1126763, by rfl⟩ : syracuseStep 1502351 = 2253527) B2253527
theorem B1502395 : Blo 1502071 1502395 := bstep (se 1 (by rfl) ⟨1126796, by rfl⟩ : syracuseStep 1502395 = 2253593) B2253593
theorem B1502471 : Blo 1502071 1502471 := bstep (se 1 (by rfl) ⟨1126853, by rfl⟩ : syracuseStep 1502471 = 2253707) B2253707
theorem B1502479 : Blo 1502071 1502479 := bstep (se 1 (by rfl) ⟨1126859, by rfl⟩ : syracuseStep 1502479 = 2253719) B2253719
theorem B2854187 : Blo 1502071 2854187 := bstep (se 1 (by rfl) ⟨2140640, by rfl⟩ : syracuseStep 2854187 = 4281281) B4281281
theorem B1502523 : Blo 1502071 1502523 := bstep (se 1 (by rfl) ⟨1126892, by rfl⟩ : syracuseStep 1502523 = 2253785) B2253785
theorem B1502599 : Blo 1502071 1502599 := bstep (se 1 (by rfl) ⟨1126949, by rfl⟩ : syracuseStep 1502599 = 2253899) B2253899
theorem B1502607 : Blo 1502071 1502607 := bstep (se 1 (by rfl) ⟨1126955, by rfl⟩ : syracuseStep 1502607 = 2253911) B2253911
theorem B1691023 : Blo 1502071 1691023 := bstep (se 1 (by rfl) ⟨1268267, by rfl⟩ : syracuseStep 1691023 = 2536535) B2536535
theorem B1502651 : Blo 1502071 1502651 := bstep (se 1 (by rfl) ⟨1126988, by rfl⟩ : syracuseStep 1502651 = 2253977) B2253977
theorem B12348881 : Blo 1502071 12348881 := bstep (se 2 (by rfl) ⟨4630830, by rfl⟩ : syracuseStep 12348881 = 9261661) B9261661
theorem B1502727 : Blo 1502071 1502727 := bstep (se 1 (by rfl) ⟨1127045, by rfl⟩ : syracuseStep 1502727 = 2254091) B2254091
theorem B1502735 : Blo 1502071 1502735 := bstep (se 1 (by rfl) ⟨1127051, by rfl⟩ : syracuseStep 1502735 = 2254103) B2254103
theorem B4279823 : Blo 1502071 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B2854415 : Blo 1502071 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B1502779 : Blo 1502071 1502779 := bstep (se 1 (by rfl) ⟨1127084, by rfl⟩ : syracuseStep 1502779 = 2254169) B2254169
theorem B2707079 : Blo 1502071 2707079 := bstep (se 1 (by rfl) ⟨2030309, by rfl⟩ : syracuseStep 2707079 = 4060619) B4060619
theorem B1502855 : Blo 1502071 1502855 := bstep (se 1 (by rfl) ⟨1127141, by rfl⟩ : syracuseStep 1502855 = 2254283) B2254283
theorem B1502863 : Blo 1502071 1502863 := bstep (se 1 (by rfl) ⟨1127147, by rfl⟩ : syracuseStep 1502863 = 2254295) B2254295
theorem B2535097 : Blo 1502071 2535097 := bstep (se 2 (by rfl) ⟨950661, by rfl⟩ : syracuseStep 2535097 = 1901323) B1901323
theorem B1502907 : Blo 1502071 1502907 := bstep (se 1 (by rfl) ⟨1127180, by rfl⟩ : syracuseStep 1502907 = 2254361) B2254361
theorem B5140169 : Blo 1502071 5140169 := bstep (se 2 (by rfl) ⟨1927563, by rfl⟩ : syracuseStep 5140169 = 3855127) B3855127
theorem B1502983 : Blo 1502071 1502983 := bstep (se 1 (by rfl) ⟨1127237, by rfl⟩ : syracuseStep 1502983 = 2254475) B2254475
theorem B1502991 : Blo 1502071 1502991 := bstep (se 1 (by rfl) ⟨1127243, by rfl⟩ : syracuseStep 1502991 = 2254487) B2254487
theorem B1503035 : Blo 1502071 1503035 := bstep (se 1 (by rfl) ⟨1127276, by rfl⟩ : syracuseStep 1503035 = 2254553) B2254553
theorem B3805015 : Blo 1502071 3805015 := bstep (se 1 (by rfl) ⟨2853761, by rfl⟩ : syracuseStep 3805015 = 5707523) B5707523
theorem B1503111 : Blo 1502071 1503111 := bstep (se 1 (by rfl) ⟨1127333, by rfl⟩ : syracuseStep 1503111 = 2254667) B2254667
theorem B1503119 : Blo 1502071 1503119 := bstep (se 1 (by rfl) ⟨1127339, by rfl⟩ : syracuseStep 1503119 = 2254679) B2254679
theorem B1806223 : Blo 1502071 1806223 := bstep (se 1 (by rfl) ⟨1354667, by rfl⟩ : syracuseStep 1806223 = 2709335) B2709335
theorem B1503163 : Blo 1502071 1503163 := bstep (se 1 (by rfl) ⟨1127372, by rfl⟩ : syracuseStep 1503163 = 2254745) B2254745
theorem B1503239 : Blo 1502071 1503239 := bstep (se 1 (by rfl) ⟨1127429, by rfl⟩ : syracuseStep 1503239 = 2254859) B2254859
theorem B1503247 : Blo 1502071 1503247 := bstep (se 1 (by rfl) ⟨1127435, by rfl⟩ : syracuseStep 1503247 = 2254871) B2254871
theorem B2707489 : Blo 1502071 2707489 := bstep (se 2 (by rfl) ⟨1015308, by rfl⟩ : syracuseStep 2707489 = 2030617) B2030617
theorem B1503291 : Blo 1502071 1503291 := bstep (se 1 (by rfl) ⟨1127468, by rfl⟩ : syracuseStep 1503291 = 2254937) B2254937
theorem B3805319 : Blo 1502071 3805319 := bstep (se 1 (by rfl) ⟨2853989, by rfl⟩ : syracuseStep 3805319 = 5707979) B5707979
theorem B1503367 : Blo 1502071 1503367 := bstep (se 1 (by rfl) ⟨1127525, by rfl⟩ : syracuseStep 1503367 = 2255051) B2255051
theorem B1503375 : Blo 1502071 1503375 := bstep (se 1 (by rfl) ⟨1127531, by rfl⟩ : syracuseStep 1503375 = 2255063) B2255063
theorem B1503419 : Blo 1502071 1503419 := bstep (se 1 (by rfl) ⟨1127564, by rfl⟩ : syracuseStep 1503419 = 2255129) B2255129
theorem B1503495 : Blo 1502071 1503495 := bstep (se 1 (by rfl) ⟨1127621, by rfl⟩ : syracuseStep 1503495 = 2255243) B2255243
theorem B3805451 : Blo 1502071 3805451 := bstep (se 1 (by rfl) ⟨2854088, by rfl⟩ : syracuseStep 3805451 = 5708177) B5708177
theorem B1503503 : Blo 1502071 1503503 := bstep (se 1 (by rfl) ⟨1127627, by rfl⟩ : syracuseStep 1503503 = 2255255) B2255255
theorem B1503547 : Blo 1502071 1503547 := bstep (se 1 (by rfl) ⟨1127660, by rfl⟩ : syracuseStep 1503547 = 2255321) B2255321
theorem B9040187 : Blo 1502071 9040187 := bstep (se 1 (by rfl) ⟨6780140, by rfl⟩ : syracuseStep 9040187 = 13560281) B13560281
theorem B2535799 : Blo 1502071 2535799 := bstep (se 1 (by rfl) ⟨1901849, by rfl⟩ : syracuseStep 2535799 = 3803699) B3803699
theorem B2535995 : Blo 1502071 2535995 := bstep (se 1 (by rfl) ⟨1901996, by rfl⟩ : syracuseStep 2535995 = 3803993) B3803993
theorem B7606871 : Blo 1502071 7606871 := bstep (se 1 (by rfl) ⟨5705153, by rfl⟩ : syracuseStep 7606871 = 11410307) B11410307
theorem B4280951 : Blo 1502071 4280951 := bstep (se 1 (by rfl) ⟨3210713, by rfl⟩ : syracuseStep 4280951 = 6421427) B6421427
theorem B3379859 : Blo 1502071 3379859 := bstep (se 1 (by rfl) ⟨2534894, by rfl⟩ : syracuseStep 3379859 = 5069789) B5069789
theorem B7221953 : Blo 1502071 7221953 := bstep (se 2 (by rfl) ⟨2708232, by rfl⟩ : syracuseStep 7221953 = 5416465) B5416465
theorem B3379913 : Blo 1502071 3379913 := bstep (se 2 (by rfl) ⟨1267467, by rfl⟩ : syracuseStep 3379913 = 2534935) B2534935
theorem B2708239 : Blo 1502071 2708239 := bstep (se 1 (by rfl) ⟨2031179, by rfl⟩ : syracuseStep 2708239 = 4062359) B4062359
theorem B34689829 : Blo 1502071 34689829 := bstep (se 4 (by rfl) ⟨3252171, by rfl⟩ : syracuseStep 34689829 = 6504343) B6504343
theorem B17593163 : Blo 1502071 17593163 := bstep (se 1 (by rfl) ⟨13194872, by rfl⟩ : syracuseStep 17593163 = 26389745) B26389745
theorem B2536393 : Blo 1502071 2536393 := bstep (se 2 (by rfl) ⟨951147, by rfl⟩ : syracuseStep 2536393 = 1902295) B1902295
theorem B7607357 : Blo 1502071 7607357 := bstep (se 3 (by rfl) ⟨1426379, by rfl⟩ : syracuseStep 7607357 = 2852759) B2852759
theorem B2708615 : Blo 1502071 2708615 := bstep (se 1 (by rfl) ⟨2031461, by rfl⟩ : syracuseStep 2708615 = 4062923) B4062923
theorem B4060307 : Blo 1502071 4060307 := bstep (se 1 (by rfl) ⟨3045230, by rfl⟩ : syracuseStep 4060307 = 6090461) B6090461
theorem B8557913 : Blo 1502071 8557913 := bstep (se 2 (by rfl) ⟨3209217, by rfl⟩ : syracuseStep 8557913 = 6418435) B6418435
theorem B3380615 : Blo 1502071 3380615 := bstep (se 1 (by rfl) ⟨2535461, by rfl⟩ : syracuseStep 3380615 = 5070923) B5070923
theorem B8123851 : Blo 1502071 8123851 := bstep (se 1 (by rfl) ⟨6092888, by rfl⟩ : syracuseStep 8123851 = 12185777) B12185777
theorem B11408849 : Blo 1502071 11408849 := bstep (se 2 (by rfl) ⟨4278318, by rfl⟩ : syracuseStep 11408849 = 8556637) B8556637
theorem B3380795 : Blo 1502071 3380795 := bstep (se 1 (by rfl) ⟨2535596, by rfl⟩ : syracuseStep 3380795 = 5071193) B5071193
theorem B35657293 : Blo 1502071 35657293 := bstep (se 3 (by rfl) ⟨6685742, by rfl⟩ : syracuseStep 35657293 = 13371485) B13371485
theorem B2537095 : Blo 1502071 2537095 := bstep (se 1 (by rfl) ⟨1902821, by rfl⟩ : syracuseStep 2537095 = 3805643) B3805643
theorem B3380921 : Blo 1502071 3380921 := bstep (se 2 (by rfl) ⟨1267845, by rfl⟩ : syracuseStep 3380921 = 2535691) B2535691
theorem B8558369 : Blo 1502071 8558369 := bstep (se 2 (by rfl) ⟨3209388, by rfl⟩ : syracuseStep 8558369 = 6418777) B6418777
theorem B92526401 : Blo 1502071 92526401 := bstep (se 2 (by rfl) ⟨34697400, by rfl⟩ : syracuseStep 92526401 = 69394801) B69394801
theorem B13711193 : Blo 1502071 13711193 := bstep (se 2 (by rfl) ⟨5141697, by rfl⟩ : syracuseStep 13711193 = 10283395) B10283395
theorem B3708791 : Blo 1502071 3708791 := bstep (se 1 (by rfl) ⟨2781593, by rfl⟩ : syracuseStep 3708791 = 5563187) B5563187
theorem B3610487 : Blo 1502071 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B16250777 : Blo 1502071 16250777 := bstep (se 2 (by rfl) ⟨6094041, by rfl⟩ : syracuseStep 16250777 = 12188083) B12188083
theorem B3856313 : Blo 1502071 3856313 := bstep (se 2 (by rfl) ⟨1446117, by rfl⟩ : syracuseStep 3856313 = 2892235) B2892235
theorem B5707705 : Blo 1502071 5707705 := bstep (se 2 (by rfl) ⟨2140389, by rfl⟩ : syracuseStep 5707705 = 4280779) B4280779
theorem B7714763 : Blo 1502071 7714763 := bstep (se 1 (by rfl) ⟨5786072, by rfl⟩ : syracuseStep 7714763 = 11572145) B11572145
theorem B3381263 : Blo 1502071 3381263 := bstep (se 1 (by rfl) ⟨2535947, by rfl⟩ : syracuseStep 3381263 = 5071895) B5071895
theorem B8558621 : Blo 1502071 8558621 := bstep (se 3 (by rfl) ⟨1604741, by rfl⟩ : syracuseStep 8558621 = 3209483) B3209483
theorem B3381281 : Blo 1502071 3381281 := bstep (se 2 (by rfl) ⟨1267980, by rfl⟩ : syracuseStep 3381281 = 2535961) B2535961
theorem B8231183 : Blo 1502071 8231183 := bstep (se 1 (by rfl) ⟨6173387, by rfl⟩ : syracuseStep 8231183 = 12346775) B12346775
theorem B3381623 : Blo 1502071 3381623 := bstep (se 1 (by rfl) ⟨2536217, by rfl⟩ : syracuseStep 3381623 = 5072435) B5072435
theorem B4815251 : Blo 1502071 4815251 := bstep (se 1 (by rfl) ⟨3611438, by rfl⟩ : syracuseStep 4815251 = 7222877) B7222877
theorem B3381803 : Blo 1502071 3381803 := bstep (se 1 (by rfl) ⟨2536352, by rfl⟩ : syracuseStep 3381803 = 5072705) B5072705
theorem B7609139 : Blo 1502071 7609139 := bstep (se 1 (by rfl) ⟨5706854, by rfl⟩ : syracuseStep 7609139 = 11413709) B11413709
theorem B5069627 : Blo 1502071 5069627 := bstep (se 1 (by rfl) ⟨3802220, by rfl⟩ : syracuseStep 5069627 = 7604441) B7604441
theorem B9632627 : Blo 1502071 9632627 := bstep (se 1 (by rfl) ⟨7224470, by rfl⟩ : syracuseStep 9632627 = 14448941) B14448941
theorem B10427251 : Blo 1502071 10427251 := bstep (se 1 (by rfl) ⟨7820438, by rfl⟩ : syracuseStep 10427251 = 15640877) B15640877
theorem B3382163 : Blo 1502071 3382163 := bstep (se 1 (by rfl) ⟨2536622, by rfl⟩ : syracuseStep 3382163 = 5073245) B5073245
theorem B13015961 : Blo 1502071 13015961 := bstep (se 2 (by rfl) ⟨4880985, by rfl⟩ : syracuseStep 13015961 = 9761971) B9761971
theorem B3382217 : Blo 1502071 3382217 := bstep (se 2 (by rfl) ⟨1268331, by rfl⟩ : syracuseStep 3382217 = 2536663) B2536663
theorem B2407439 : Blo 1502071 2407439 := bstep (se 1 (by rfl) ⟨1805579, by rfl⟩ : syracuseStep 2407439 = 3611159) B3611159
theorem B14449751 : Blo 1502071 14449751 := bstep (se 1 (by rfl) ⟨10837313, by rfl⟩ : syracuseStep 14449751 = 21674627) B21674627
theorem B7609463 : Blo 1502071 7609463 := bstep (se 1 (by rfl) ⟨5707097, by rfl⟩ : syracuseStep 7609463 = 11414195) B11414195
theorem B2890937 : Blo 1502071 2890937 := bstep (se 2 (by rfl) ⟨1084101, by rfl⟩ : syracuseStep 2890937 = 2168203) B2168203
theorem B6094061 : Blo 1502071 6094061 := bstep (se 3 (by rfl) ⟨1142636, by rfl⟩ : syracuseStep 6094061 = 2285273) B2285273
theorem B5070113 : Blo 1502071 5070113 := bstep (se 2 (by rfl) ⟨1901292, by rfl⟩ : syracuseStep 5070113 = 3802585) B3802585
theorem B3611947 : Blo 1502071 3611947 := bstep (se 1 (by rfl) ⟨2708960, by rfl⟩ : syracuseStep 3611947 = 5417921) B5417921
theorem B8347223 : Blo 1502071 8347223 := bstep (se 1 (by rfl) ⟨6260417, by rfl⟩ : syracuseStep 8347223 = 12520835) B12520835
theorem B2031223 : Blo 1502071 2031223 := bstep (se 1 (by rfl) ⟨1523417, by rfl⟩ : syracuseStep 2031223 = 3046835) B3046835
theorem B3382919 : Blo 1502071 3382919 := bstep (se 1 (by rfl) ⟨2537189, by rfl⟩ : syracuseStep 3382919 = 5074379) B5074379
theorem B5070707 : Blo 1502071 5070707 := bstep (se 1 (by rfl) ⟨3803030, by rfl⟩ : syracuseStep 5070707 = 7606061) B7606061
theorem B3612563 : Blo 1502071 3612563 := bstep (se 1 (by rfl) ⟨2709422, by rfl⟩ : syracuseStep 3612563 = 5418845) B5418845
theorem B2253161 : Blo 1502071 2253161 := bstep (se 2 (by rfl) ⟨844935, by rfl⟩ : syracuseStep 2253161 = 1689871) B1689871
theorem B4063613 : Blo 1502071 4063613 := bstep (se 3 (by rfl) ⟨761927, by rfl⟩ : syracuseStep 4063613 = 1523855) B1523855
theorem B5071247 : Blo 1502071 5071247 := bstep (se 1 (by rfl) ⟨3803435, by rfl⟩ : syracuseStep 5071247 = 7606871) B7606871
theorem B2253239 : Blo 1502071 2253239 := bstep (se 1 (by rfl) ⟨1689929, by rfl⟩ : syracuseStep 2253239 = 3379859) B3379859
theorem B2253275 : Blo 1502071 2253275 := bstep (se 1 (by rfl) ⟨1689956, by rfl⟩ : syracuseStep 2253275 = 3379913) B3379913
theorem B7709165 : Blo 1502071 7709165 := bstep (se 3 (by rfl) ⟨1445468, by rfl⟩ : syracuseStep 7709165 = 2890937) B2890937
theorem B5071571 : Blo 1502071 5071571 := bstep (se 1 (by rfl) ⟨3803678, by rfl⟩ : syracuseStep 5071571 = 7607357) B7607357
theorem B2253743 : Blo 1502071 2253743 := bstep (se 1 (by rfl) ⟨1690307, by rfl⟩ : syracuseStep 2253743 = 3380615) B3380615
theorem B1901495 : Blo 1502071 1901495 := bstep (se 1 (by rfl) ⟨1426121, by rfl⟩ : syracuseStep 1901495 = 2852243) B2852243
theorem B2253833 : Blo 1502071 2253833 := bstep (se 2 (by rfl) ⟨845187, by rfl⟩ : syracuseStep 2253833 = 1690375) B1690375
theorem B2253863 : Blo 1502071 2253863 := bstep (se 1 (by rfl) ⟨1690397, by rfl⟩ : syracuseStep 2253863 = 3380795) B3380795
theorem B46253105 : Blo 1502071 46253105 := bstep (se 2 (by rfl) ⟨17344914, by rfl⟩ : syracuseStep 46253105 = 34689829) B34689829
theorem B1901647 : Blo 1502071 1901647 := bstep (se 1 (by rfl) ⟨1426235, by rfl⟩ : syracuseStep 1901647 = 2852471) B2852471
theorem B2253947 : Blo 1502071 2253947 := bstep (se 1 (by rfl) ⟨1690460, by rfl⟩ : syracuseStep 2253947 = 3380921) B3380921
theorem B13903001 : Blo 1502071 13903001 := bstep (se 2 (by rfl) ⟨5213625, by rfl⟩ : syracuseStep 13903001 = 10427251) B10427251
theorem B2254073 : Blo 1502071 2254073 := bstep (se 2 (by rfl) ⟨845277, by rfl⟩ : syracuseStep 2254073 = 1690555) B1690555
theorem B12518671 : Blo 1502071 12518671 := bstep (se 1 (by rfl) ⟨9389003, by rfl⟩ : syracuseStep 12518671 = 18778007) B18778007
theorem B2254175 : Blo 1502071 2254175 := bstep (se 1 (by rfl) ⟨1690631, by rfl⟩ : syracuseStep 2254175 = 3381263) B3381263
theorem B2254187 : Blo 1502071 2254187 := bstep (se 1 (by rfl) ⟨1690640, by rfl⟩ : syracuseStep 2254187 = 3381281) B3381281
theorem B22259261 : Blo 1502071 22259261 := bstep (se 3 (by rfl) ⟨4173611, by rfl⟩ : syracuseStep 22259261 = 8347223) B8347223
theorem B2254415 : Blo 1502071 2254415 := bstep (se 1 (by rfl) ⟨1690811, by rfl⟩ : syracuseStep 2254415 = 3381623) B3381623
theorem B3802747 : Blo 1502071 3802747 := bstep (se 1 (by rfl) ⟨2852060, by rfl⟩ : syracuseStep 3802747 = 5704121) B5704121
theorem B6178427 : Blo 1502071 6178427 := bstep (se 1 (by rfl) ⟨4633820, by rfl⟩ : syracuseStep 6178427 = 9267641) B9267641
theorem B7218877 : Blo 1502071 7218877 := bstep (se 3 (by rfl) ⟨1353539, by rfl⟩ : syracuseStep 7218877 = 2707079) B2707079
theorem B2254535 : Blo 1502071 2254535 := bstep (se 1 (by rfl) ⟨1690901, by rfl⟩ : syracuseStep 2254535 = 3381803) B3381803
theorem B19253051 : Blo 1502071 19253051 := bstep (se 1 (by rfl) ⟨14439788, by rfl⟩ : syracuseStep 19253051 = 28879577) B28879577
theorem B2254697 : Blo 1502071 2254697 := bstep (se 2 (by rfl) ⟨845511, by rfl⟩ : syracuseStep 2254697 = 1691023) B1691023
theorem B5072759 : Blo 1502071 5072759 := bstep (se 1 (by rfl) ⟨3804569, by rfl⟩ : syracuseStep 5072759 = 7609139) B7609139
theorem B2254775 : Blo 1502071 2254775 := bstep (se 1 (by rfl) ⟨1691081, by rfl⟩ : syracuseStep 2254775 = 3382163) B3382163
theorem B10831801 : Blo 1502071 10831801 := bstep (se 2 (by rfl) ⟨4061925, by rfl⟩ : syracuseStep 10831801 = 8123851) B8123851
theorem B8677307 : Blo 1502071 8677307 := bstep (se 1 (by rfl) ⟨6507980, by rfl⟩ : syracuseStep 8677307 = 13015961) B13015961
theorem B2254811 : Blo 1502071 2254811 := bstep (se 1 (by rfl) ⟨1691108, by rfl⟩ : syracuseStep 2254811 = 3382217) B3382217
theorem B5072975 : Blo 1502071 5072975 := bstep (se 1 (by rfl) ⟨3804731, by rfl⟩ : syracuseStep 5072975 = 7609463) B7609463
theorem B1902791 : Blo 1502071 1902791 := bstep (se 1 (by rfl) ⟨1427093, by rfl⟩ : syracuseStep 1902791 = 2854187) B2854187
theorem B2853215 : Blo 1502071 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B1902943 : Blo 1502071 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B2255279 : Blo 1502071 2255279 := bstep (se 1 (by rfl) ⟨1691459, by rfl⟩ : syracuseStep 2255279 = 3382919) B3382919
theorem B5073353 : Blo 1502071 5073353 := bstep (se 2 (by rfl) ⟨1902507, by rfl⟩ : syracuseStep 5073353 = 3805015) B3805015
theorem B3426779 : Blo 1502071 3426779 := bstep (se 1 (by rfl) ⟨2570084, by rfl⟩ : syracuseStep 3426779 = 5140169) B5140169
theorem B10283501 : Blo 1502071 10283501 := bstep (se 3 (by rfl) ⟨1928156, by rfl⟩ : syracuseStep 10283501 = 3856313) B3856313
theorem B5704289 : Blo 1502071 5704289 := bstep (se 2 (by rfl) ⟨2139108, by rfl⟩ : syracuseStep 5704289 = 4278217) B4278217
theorem B5073623 : Blo 1502071 5073623 := bstep (se 1 (by rfl) ⟨3805217, by rfl⟩ : syracuseStep 5073623 = 7610435) B7610435
theorem B2853625 : Blo 1502071 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B1502075 : Blo 1502071 1502075 := bstep (se 1 (by rfl) ⟨1126556, by rfl⟩ : syracuseStep 1502075 = 2253113) B2253113
theorem B1502127 : Blo 1502071 1502127 := bstep (se 1 (by rfl) ⟨1126595, by rfl⟩ : syracuseStep 1502127 = 2253191) B2253191
theorem B5073839 : Blo 1502071 5073839 := bstep (se 1 (by rfl) ⟨3805379, by rfl⟩ : syracuseStep 5073839 = 7610759) B7610759
theorem B1502151 : Blo 1502071 1502151 := bstep (se 1 (by rfl) ⟨1126613, by rfl⟩ : syracuseStep 1502151 = 2253227) B2253227
theorem B1502171 : Blo 1502071 1502171 := bstep (se 1 (by rfl) ⟨1126628, by rfl⟩ : syracuseStep 1502171 = 2253257) B2253257
theorem B1502247 : Blo 1502071 1502247 := bstep (se 1 (by rfl) ⟨1126685, by rfl⟩ : syracuseStep 1502247 = 2253371) B2253371
theorem B1690663 : Blo 1502071 1690663 := bstep (se 1 (by rfl) ⟨1267997, by rfl⟩ : syracuseStep 1690663 = 2535995) B2535995
theorem B1502287 : Blo 1502071 1502287 := bstep (se 1 (by rfl) ⟨1126715, by rfl⟩ : syracuseStep 1502287 = 2253431) B2253431
theorem B2853967 : Blo 1502071 2853967 := bstep (se 1 (by rfl) ⟨2140475, by rfl⟩ : syracuseStep 2853967 = 4280951) B4280951
theorem B1502303 : Blo 1502071 1502303 := bstep (se 1 (by rfl) ⟨1126727, by rfl⟩ : syracuseStep 1502303 = 2253455) B2253455
theorem B1502331 : Blo 1502071 1502331 := bstep (se 1 (by rfl) ⟨1126748, by rfl⟩ : syracuseStep 1502331 = 2253497) B2253497
theorem B11414681 : Blo 1502071 11414681 := bstep (se 2 (by rfl) ⟨4280505, by rfl⟩ : syracuseStep 11414681 = 8561011) B8561011
theorem B4336811 : Blo 1502071 4336811 := bstep (se 1 (by rfl) ⟨3252608, by rfl⟩ : syracuseStep 4336811 = 6505217) B6505217
theorem B1502383 : Blo 1502071 1502383 := bstep (se 1 (by rfl) ⟨1126787, by rfl⟩ : syracuseStep 1502383 = 2253575) B2253575
theorem B1502407 : Blo 1502071 1502407 := bstep (se 1 (by rfl) ⟨1126805, by rfl⟩ : syracuseStep 1502407 = 2253611) B2253611
theorem B1502427 : Blo 1502071 1502427 := bstep (se 1 (by rfl) ⟨1126820, by rfl⟩ : syracuseStep 1502427 = 2253641) B2253641
theorem B1502503 : Blo 1502071 1502503 := bstep (se 1 (by rfl) ⟨1126877, by rfl⟩ : syracuseStep 1502503 = 2253755) B2253755
theorem B2854217 : Blo 1502071 2854217 := bstep (se 2 (by rfl) ⟨1070331, by rfl⟩ : syracuseStep 2854217 = 2140663) B2140663
theorem B1502543 : Blo 1502071 1502543 := bstep (se 1 (by rfl) ⟨1126907, by rfl⟩ : syracuseStep 1502543 = 2253815) B2253815
theorem B1502559 : Blo 1502071 1502559 := bstep (se 1 (by rfl) ⟨1126919, by rfl⟩ : syracuseStep 1502559 = 2253839) B2253839
theorem B1502587 : Blo 1502071 1502587 := bstep (se 1 (by rfl) ⟨1126940, by rfl⟩ : syracuseStep 1502587 = 2253881) B2253881
theorem B1502639 : Blo 1502071 1502639 := bstep (se 1 (by rfl) ⟨1126979, by rfl⟩ : syracuseStep 1502639 = 2253959) B2253959
theorem B1805743 : Blo 1502071 1805743 := bstep (se 1 (by rfl) ⟨1354307, by rfl⟩ : syracuseStep 1805743 = 2708615) B2708615
theorem B2706871 : Blo 1502071 2706871 := bstep (se 1 (by rfl) ⟨2030153, by rfl⟩ : syracuseStep 2706871 = 4060307) B4060307
theorem B1502663 : Blo 1502071 1502663 := bstep (se 1 (by rfl) ⟨1126997, by rfl⟩ : syracuseStep 1502663 = 2253995) B2253995
theorem B1502683 : Blo 1502071 1502683 := bstep (se 1 (by rfl) ⟨1127012, by rfl⟩ : syracuseStep 1502683 = 2254025) B2254025
theorem B1502759 : Blo 1502071 1502759 := bstep (se 1 (by rfl) ⟨1127069, by rfl⟩ : syracuseStep 1502759 = 2254139) B2254139
theorem B2534969 : Blo 1502071 2534969 := bstep (se 2 (by rfl) ⟨950613, by rfl⟩ : syracuseStep 2534969 = 1901227) B1901227
theorem B5705275 : Blo 1502071 5705275 := bstep (se 1 (by rfl) ⟨4278956, by rfl⟩ : syracuseStep 5705275 = 8557913) B8557913
theorem B1502799 : Blo 1502071 1502799 := bstep (se 1 (by rfl) ⟨1127099, by rfl⟩ : syracuseStep 1502799 = 2254199) B2254199
theorem B1502815 : Blo 1502071 1502815 := bstep (se 1 (by rfl) ⟨1127111, by rfl⟩ : syracuseStep 1502815 = 2254223) B2254223
theorem B1502843 : Blo 1502071 1502843 := bstep (se 1 (by rfl) ⟨1127132, by rfl⟩ : syracuseStep 1502843 = 2254265) B2254265
theorem B8121995 : Blo 1502071 8121995 := bstep (se 1 (by rfl) ⟨6091496, by rfl⟩ : syracuseStep 8121995 = 12182993) B12182993
theorem B7605899 : Blo 1502071 7605899 := bstep (se 1 (by rfl) ⟨5704424, by rfl⟩ : syracuseStep 7605899 = 11408849) B11408849
theorem B1502895 : Blo 1502071 1502895 := bstep (se 1 (by rfl) ⟨1127171, by rfl⟩ : syracuseStep 1502895 = 2254343) B2254343
theorem B1502919 : Blo 1502071 1502919 := bstep (se 1 (by rfl) ⟨1127189, by rfl⟩ : syracuseStep 1502919 = 2254379) B2254379
theorem B1502939 : Blo 1502071 1502939 := bstep (se 1 (by rfl) ⟨1127204, by rfl⟩ : syracuseStep 1502939 = 2254409) B2254409
theorem B1503015 : Blo 1502071 1503015 := bstep (se 1 (by rfl) ⟨1127261, by rfl⟩ : syracuseStep 1503015 = 2254523) B2254523
theorem B1503055 : Blo 1502071 1503055 := bstep (se 1 (by rfl) ⟨1127291, by rfl⟩ : syracuseStep 1503055 = 2254583) B2254583
theorem B1503071 : Blo 1502071 1503071 := bstep (se 1 (by rfl) ⟨1127303, by rfl⟩ : syracuseStep 1503071 = 2254607) B2254607
theorem B5705579 : Blo 1502071 5705579 := bstep (se 1 (by rfl) ⟨4279184, by rfl⟩ : syracuseStep 5705579 = 8558369) B8558369
theorem B1503099 : Blo 1502071 1503099 := bstep (se 1 (by rfl) ⟨1127324, by rfl⟩ : syracuseStep 1503099 = 2254649) B2254649
theorem B1503151 : Blo 1502071 1503151 := bstep (se 1 (by rfl) ⟨1127363, by rfl⟩ : syracuseStep 1503151 = 2254727) B2254727
theorem B10833851 : Blo 1502071 10833851 := bstep (se 1 (by rfl) ⟨8125388, by rfl⟩ : syracuseStep 10833851 = 16250777) B16250777
theorem B1503175 : Blo 1502071 1503175 := bstep (se 1 (by rfl) ⟨1127381, by rfl⟩ : syracuseStep 1503175 = 2254763) B2254763
theorem B1503195 : Blo 1502071 1503195 := bstep (se 1 (by rfl) ⟨1127396, by rfl⟩ : syracuseStep 1503195 = 2254793) B2254793
theorem B5705747 : Blo 1502071 5705747 := bstep (se 1 (by rfl) ⟨4279310, by rfl⟩ : syracuseStep 5705747 = 8558621) B8558621
theorem B1503271 : Blo 1502071 1503271 := bstep (se 1 (by rfl) ⟨1127453, by rfl⟩ : syracuseStep 1503271 = 2254907) B2254907
theorem B1503311 : Blo 1502071 1503311 := bstep (se 1 (by rfl) ⟨1127483, by rfl⟩ : syracuseStep 1503311 = 2254967) B2254967
theorem B1503327 : Blo 1502071 1503327 := bstep (se 1 (by rfl) ⟨1127495, by rfl⟩ : syracuseStep 1503327 = 2254991) B2254991
theorem B1503355 : Blo 1502071 1503355 := bstep (se 1 (by rfl) ⟨1127516, by rfl⟩ : syracuseStep 1503355 = 2255033) B2255033
theorem B1503407 : Blo 1502071 1503407 := bstep (se 1 (by rfl) ⟨1127555, by rfl⟩ : syracuseStep 1503407 = 2255111) B2255111
theorem B1503431 : Blo 1502071 1503431 := bstep (se 1 (by rfl) ⟨1127573, by rfl⟩ : syracuseStep 1503431 = 2255147) B2255147
theorem B1503451 : Blo 1502071 1503451 := bstep (se 1 (by rfl) ⟨1127588, by rfl⟩ : syracuseStep 1503451 = 2255177) B2255177
theorem B2535671 : Blo 1502071 2535671 := bstep (se 1 (by rfl) ⟨1901753, by rfl⟩ : syracuseStep 2535671 = 3803507) B3803507
theorem B1503527 : Blo 1502071 1503527 := bstep (se 1 (by rfl) ⟨1127645, by rfl⟩ : syracuseStep 1503527 = 2255291) B2255291
theorem B1503567 : Blo 1502071 1503567 := bstep (se 1 (by rfl) ⟨1127675, by rfl⟩ : syracuseStep 1503567 = 2255351) B2255351
theorem B3379751 : Blo 1502071 3379751 := bstep (se 1 (by rfl) ⟨2534813, by rfl⟩ : syracuseStep 3379751 = 5069627) B5069627
theorem B2536015 : Blo 1502071 2536015 := bstep (se 1 (by rfl) ⟨1902011, by rfl⟩ : syracuseStep 2536015 = 3804023) B3804023
theorem B47543057 : Blo 1502071 47543057 := bstep (se 2 (by rfl) ⟨17828646, by rfl⟩ : syracuseStep 47543057 = 35657293) B35657293
theorem B2708297 : Blo 1502071 2708297 := bstep (se 2 (by rfl) ⟨1015611, by rfl⟩ : syracuseStep 2708297 = 2031223) B2031223
theorem B2536265 : Blo 1502071 2536265 := bstep (se 2 (by rfl) ⟨951099, by rfl⟩ : syracuseStep 2536265 = 1902199) B1902199
theorem B3380075 : Blo 1502071 3380075 := bstep (se 1 (by rfl) ⟨2535056, by rfl⟩ : syracuseStep 3380075 = 5070113) B5070113
theorem B3380129 : Blo 1502071 3380129 := bstep (se 2 (by rfl) ⟨1267548, by rfl⟩ : syracuseStep 3380129 = 2535097) B2535097
theorem B11416625 : Blo 1502071 11416625 := bstep (se 2 (by rfl) ⟨4281234, by rfl⟩ : syracuseStep 11416625 = 8562469) B8562469
theorem B6173849 : Blo 1502071 6173849 := bstep (se 2 (by rfl) ⟨2315193, by rfl⟩ : syracuseStep 6173849 = 4630387) B4630387
theorem B3380471 : Blo 1502071 3380471 := bstep (se 1 (by rfl) ⟨2535353, by rfl⟩ : syracuseStep 3380471 = 5070707) B5070707
theorem B2536697 : Blo 1502071 2536697 := bstep (se 2 (by rfl) ⟨951261, by rfl⟩ : syracuseStep 2536697 = 1902523) B1902523
theorem B6419837 : Blo 1502071 6419837 := bstep (se 3 (by rfl) ⟨1203719, by rfl⟩ : syracuseStep 6419837 = 2407439) B2407439
theorem B2536879 : Blo 1502071 2536879 := bstep (se 1 (by rfl) ⟨1902659, by rfl⟩ : syracuseStep 2536879 = 3805319) B3805319
theorem B14439941 : Blo 1502071 14439941 := bstep (se 4 (by rfl) ⟨1353744, by rfl⟩ : syracuseStep 14439941 = 2707489) B2707489
theorem B2536967 : Blo 1502071 2536967 := bstep (se 1 (by rfl) ⟨1902725, by rfl⟩ : syracuseStep 2536967 = 3805451) B3805451
theorem B4814635 : Blo 1502071 4814635 := bstep (se 1 (by rfl) ⟨3610976, by rfl⟩ : syracuseStep 4814635 = 7221953) B7221953
theorem B3381065 : Blo 1502071 3381065 := bstep (se 2 (by rfl) ⟨1267899, by rfl⟩ : syracuseStep 3381065 = 2535799) B2535799
theorem B11728775 : Blo 1502071 11728775 := bstep (se 1 (by rfl) ⟨8796581, by rfl⟩ : syracuseStep 11728775 = 17593163) B17593163
theorem B7223201 : Blo 1502071 7223201 := bstep (se 2 (by rfl) ⟨2708700, by rfl⟩ : syracuseStep 7223201 = 5417401) B5417401
theorem B10983539 : Blo 1502071 10983539 := bstep (se 1 (by rfl) ⟨8237654, by rfl⟩ : syracuseStep 10983539 = 16475309) B16475309
theorem B24107165 : Blo 1502071 24107165 := bstep (se 3 (by rfl) ⟨4520093, by rfl⟩ : syracuseStep 24107165 = 9040187) B9040187
theorem B3610871 : Blo 1502071 3610871 := bstep (se 1 (by rfl) ⟨2708153, by rfl⟩ : syracuseStep 3610871 = 5416307) B5416307
theorem B3610985 : Blo 1502071 3610985 := bstep (se 2 (by rfl) ⟨1354119, by rfl⟩ : syracuseStep 3610985 = 2708239) B2708239
theorem B4569473 : Blo 1502071 4569473 := bstep (se 2 (by rfl) ⟨1713552, by rfl⟩ : syracuseStep 4569473 = 3427105) B3427105
theorem B3660275 : Blo 1502071 3660275 := bstep (se 1 (by rfl) ⟨2745206, by rfl⟩ : syracuseStep 3660275 = 5490413) B5490413
theorem B61684267 : Blo 1502071 61684267 := bstep (se 1 (by rfl) ⟨46263200, by rfl⟩ : syracuseStep 61684267 = 92526401) B92526401
theorem B9140795 : Blo 1502071 9140795 := bstep (se 1 (by rfl) ⟨6855596, by rfl⟩ : syracuseStep 9140795 = 13711193) B13711193
theorem B2472527 : Blo 1502071 2472527 := bstep (se 1 (by rfl) ⟨1854395, by rfl⟩ : syracuseStep 2472527 = 3708791) B3708791
theorem B2406991 : Blo 1502071 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B3381857 : Blo 1502071 3381857 := bstep (se 2 (by rfl) ⟨1268196, by rfl⟩ : syracuseStep 3381857 = 2536393) B2536393
theorem B5143175 : Blo 1502071 5143175 := bstep (se 1 (by rfl) ⟨3857381, by rfl⟩ : syracuseStep 5143175 = 7714763) B7714763
theorem B8674121 : Blo 1502071 8674121 := bstep (se 2 (by rfl) ⟨3252795, by rfl⟩ : syracuseStep 8674121 = 6505591) B6505591
theorem B5487455 : Blo 1502071 5487455 := bstep (se 1 (by rfl) ⟨4115591, by rfl⟩ : syracuseStep 5487455 = 8231183) B8231183
theorem B5708663 : Blo 1502071 5708663 := bstep (se 1 (by rfl) ⟨4281497, by rfl⟩ : syracuseStep 5708663 = 8562995) B8562995
theorem B3210167 : Blo 1502071 3210167 := bstep (se 1 (by rfl) ⟨2407625, by rfl⟩ : syracuseStep 3210167 = 4815251) B4815251
theorem B3382199 : Blo 1502071 3382199 := bstep (se 1 (by rfl) ⟨2536649, by rfl⟩ : syracuseStep 3382199 = 5073299) B5073299
theorem B9624577 : Blo 1502071 9624577 := bstep (se 2 (by rfl) ⟨3609216, by rfl⟩ : syracuseStep 9624577 = 7218433) B7218433
theorem B5069843 : Blo 1502071 5069843 := bstep (se 1 (by rfl) ⟨3802382, by rfl⟩ : syracuseStep 5069843 = 7604765) B7604765
theorem B12688427 : Blo 1502071 12688427 := bstep (se 1 (by rfl) ⟨9516320, by rfl⟩ : syracuseStep 12688427 = 19032641) B19032641
theorem B10279979 : Blo 1502071 10279979 := bstep (se 1 (by rfl) ⟨7709984, by rfl⟩ : syracuseStep 10279979 = 15419969) B15419969
theorem B4815929 : Blo 1502071 4815929 := bstep (se 2 (by rfl) ⟨1805973, by rfl⟩ : syracuseStep 4815929 = 3611947) B3611947
theorem B6421751 : Blo 1502071 6421751 := bstep (se 1 (by rfl) ⟨4816313, by rfl⟩ : syracuseStep 6421751 = 9632627) B9632627
theorem B5070167 : Blo 1502071 5070167 := bstep (se 1 (by rfl) ⟨3802625, by rfl⟩ : syracuseStep 5070167 = 7605251) B7605251
theorem B2284907 : Blo 1502071 2284907 := bstep (se 1 (by rfl) ⟨1713680, by rfl⟩ : syracuseStep 2284907 = 3427361) B3427361
theorem B9633167 : Blo 1502071 9633167 := bstep (se 1 (by rfl) ⟨7224875, by rfl⟩ : syracuseStep 9633167 = 14449751) B14449751
theorem B4062707 : Blo 1502071 4062707 := bstep (se 1 (by rfl) ⟨3047030, by rfl⟩ : syracuseStep 4062707 = 6094061) B6094061
theorem B3382793 : Blo 1502071 3382793 := bstep (se 2 (by rfl) ⟨1268547, by rfl⟩ : syracuseStep 3382793 = 2537095) B2537095
theorem B8232587 : Blo 1502071 8232587 := bstep (se 1 (by rfl) ⟨6174440, by rfl⟩ : syracuseStep 8232587 = 12348881) B12348881
theorem B9756305 : Blo 1502071 9756305 := bstep (se 2 (by rfl) ⟨3658614, by rfl⟩ : syracuseStep 9756305 = 7317229) B7317229
theorem B2408297 : Blo 1502071 2408297 := bstep (se 2 (by rfl) ⟨903111, by rfl⟩ : syracuseStep 2408297 = 1806223) B1806223
theorem B7610273 : Blo 1502071 7610273 := bstep (se 2 (by rfl) ⟨2853852, by rfl⟩ : syracuseStep 7610273 = 5707705) B5707705
theorem B2408375 : Blo 1502071 2408375 := bstep (se 1 (by rfl) ⟨1806281, by rfl⟩ : syracuseStep 2408375 = 3612563) B3612563
theorem B2253167 : Blo 1502071 2253167 := bstep (se 1 (by rfl) ⟨1689875, by rfl⟩ : syracuseStep 2253167 = 3379751) B3379751
theorem B31695371 : Blo 1502071 31695371 := bstep (se 1 (by rfl) ⟨23771528, by rfl⟩ : syracuseStep 31695371 = 47543057) B47543057
theorem B2253383 : Blo 1502071 2253383 := bstep (se 1 (by rfl) ⟨1690037, by rfl⟩ : syracuseStep 2253383 = 3380075) B3380075
theorem B2253419 : Blo 1502071 2253419 := bstep (se 1 (by rfl) ⟨1690064, by rfl⟩ : syracuseStep 2253419 = 3380129) B3380129
theorem B30835403 : Blo 1502071 30835403 := bstep (se 1 (by rfl) ⟨23126552, by rfl⟩ : syracuseStep 30835403 = 46253105) B46253105
theorem B7611083 : Blo 1502071 7611083 := bstep (se 1 (by rfl) ⟨5708312, by rfl⟩ : syracuseStep 7611083 = 11416625) B11416625
theorem B2253647 : Blo 1502071 2253647 := bstep (se 1 (by rfl) ⟨1690235, by rfl⟩ : syracuseStep 2253647 = 3380471) B3380471
theorem B7611245 : Blo 1502071 7611245 := bstep (se 3 (by rfl) ⟨1427108, by rfl⟩ : syracuseStep 7611245 = 2854217) B2854217
theorem B9626627 : Blo 1502071 9626627 := bstep (se 1 (by rfl) ⟨7219970, by rfl⟩ : syracuseStep 9626627 = 14439941) B14439941
theorem B2254043 : Blo 1502071 2254043 := bstep (se 1 (by rfl) ⟨1690532, by rfl⟩ : syracuseStep 2254043 = 3381065) B3381065
theorem B5784871 : Blo 1502071 5784871 := bstep (se 1 (by rfl) ⟨4338653, by rfl⟩ : syracuseStep 5784871 = 8677307) B8677307
theorem B2254217 : Blo 1502071 2254217 := bstep (se 2 (by rfl) ⟨845331, by rfl⟩ : syracuseStep 2254217 = 1690663) B1690663
theorem B1902143 : Blo 1502071 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B1648351 : Blo 1502071 1648351 := bstep (se 1 (by rfl) ⟨1236263, by rfl⟩ : syracuseStep 1648351 = 2472527) B2472527
theorem B3802859 : Blo 1502071 3802859 := bstep (se 1 (by rfl) ⟨2852144, by rfl⟩ : syracuseStep 3802859 = 5704289) B5704289
theorem B2254571 : Blo 1502071 2254571 := bstep (se 1 (by rfl) ⟨1690928, by rfl⟩ : syracuseStep 2254571 = 3381857) B3381857
theorem B2140111 : Blo 1502071 2140111 := bstep (se 1 (by rfl) ⟨1605083, by rfl⟩ : syracuseStep 2140111 = 3210167) B3210167
theorem B2254799 : Blo 1502071 2254799 := bstep (se 1 (by rfl) ⟨1691099, by rfl⟩ : syracuseStep 2254799 = 3382199) B3382199
theorem B2255195 : Blo 1502071 2255195 := bstep (se 1 (by rfl) ⟨1691396, by rfl⟩ : syracuseStep 2255195 = 3382793) B3382793
theorem B1689979 : Blo 1502071 1689979 := bstep (se 1 (by rfl) ⟨1267484, by rfl⟩ : syracuseStep 1689979 = 2534969) B2534969
theorem B3803719 : Blo 1502071 3803719 := bstep (se 1 (by rfl) ⟨2852789, by rfl⟩ : syracuseStep 3803719 = 5705579) B5705579
theorem B5073515 : Blo 1502071 5073515 := bstep (se 1 (by rfl) ⟨3805136, by rfl⟩ : syracuseStep 5073515 = 7610273) B7610273
theorem B3803831 : Blo 1502071 3803831 := bstep (se 1 (by rfl) ⟨2852873, by rfl⟩ : syracuseStep 3803831 = 5705747) B5705747
theorem B1690447 : Blo 1502071 1690447 := bstep (se 1 (by rfl) ⟨1267835, by rfl⟩ : syracuseStep 1690447 = 2535671) B2535671
theorem B1502107 : Blo 1502071 1502107 := bstep (se 1 (by rfl) ⟨1126580, by rfl⟩ : syracuseStep 1502107 = 2253161) B2253161
theorem B1502159 : Blo 1502071 1502159 := bstep (se 1 (by rfl) ⟨1126619, by rfl⟩ : syracuseStep 1502159 = 2253239) B2253239
theorem B1502183 : Blo 1502071 1502183 := bstep (se 1 (by rfl) ⟨1126637, by rfl⟩ : syracuseStep 1502183 = 2253275) B2253275
theorem B5139443 : Blo 1502071 5139443 := bstep (se 1 (by rfl) ⟨3854582, by rfl⟩ : syracuseStep 5139443 = 7709165) B7709165
theorem B5074109 : Blo 1502071 5074109 := bstep (se 3 (by rfl) ⟨951395, by rfl⟩ : syracuseStep 5074109 = 1902791) B1902791
theorem B1805531 : Blo 1502071 1805531 := bstep (se 1 (by rfl) ⟨1354148, by rfl⟩ : syracuseStep 1805531 = 2708297) B2708297
theorem B1690843 : Blo 1502071 1690843 := bstep (se 1 (by rfl) ⟨1268132, by rfl⟩ : syracuseStep 1690843 = 2536265) B2536265
theorem B1502495 : Blo 1502071 1502495 := bstep (se 1 (by rfl) ⟨1126871, by rfl⟩ : syracuseStep 1502495 = 2253743) B2253743
theorem B1502555 : Blo 1502071 1502555 := bstep (se 1 (by rfl) ⟨1126916, by rfl⟩ : syracuseStep 1502555 = 2253833) B2253833
theorem B1502575 : Blo 1502071 1502575 := bstep (se 1 (by rfl) ⟨1126931, by rfl⟩ : syracuseStep 1502575 = 2253863) B2253863
theorem B1502631 : Blo 1502071 1502631 := bstep (se 1 (by rfl) ⟨1126973, by rfl⟩ : syracuseStep 1502631 = 2253947) B2253947
theorem B4115899 : Blo 1502071 4115899 := bstep (se 1 (by rfl) ⟨3086924, by rfl⟩ : syracuseStep 4115899 = 6173849) B6173849
theorem B9268667 : Blo 1502071 9268667 := bstep (se 1 (by rfl) ⟨6951500, by rfl⟩ : syracuseStep 9268667 = 13903001) B13903001
theorem B1502715 : Blo 1502071 1502715 := bstep (se 1 (by rfl) ⟨1127036, by rfl⟩ : syracuseStep 1502715 = 2254073) B2254073
theorem B1691131 : Blo 1502071 1691131 := bstep (se 1 (by rfl) ⟨1268348, by rfl⟩ : syracuseStep 1691131 = 2536697) B2536697
theorem B1502783 : Blo 1502071 1502783 := bstep (se 1 (by rfl) ⟨1127087, by rfl⟩ : syracuseStep 1502783 = 2254175) B2254175
theorem B1502791 : Blo 1502071 1502791 := bstep (se 1 (by rfl) ⟨1127093, by rfl⟩ : syracuseStep 1502791 = 2254187) B2254187
theorem B4279891 : Blo 1502071 4279891 := bstep (se 1 (by rfl) ⟨3209918, by rfl⟩ : syracuseStep 4279891 = 6419837) B6419837
theorem B9629293 : Blo 1502071 9629293 := bstep (se 3 (by rfl) ⟨1805492, by rfl⟩ : syracuseStep 9629293 = 3610985) B3610985
theorem B3804833 : Blo 1502071 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B1691311 : Blo 1502071 1691311 := bstep (se 1 (by rfl) ⟨1268483, by rfl⟩ : syracuseStep 1691311 = 2536967) B2536967
theorem B14839507 : Blo 1502071 14839507 := bstep (se 1 (by rfl) ⟨11129630, by rfl⟩ : syracuseStep 14839507 = 22259261) B22259261
theorem B1502943 : Blo 1502071 1502943 := bstep (se 1 (by rfl) ⟨1127207, by rfl⟩ : syracuseStep 1502943 = 2254415) B2254415
theorem B1503023 : Blo 1502071 1503023 := bstep (se 1 (by rfl) ⟨1127267, by rfl⟩ : syracuseStep 1503023 = 2254535) B2254535
theorem B1503131 : Blo 1502071 1503131 := bstep (se 1 (by rfl) ⟨1127348, by rfl⟩ : syracuseStep 1503131 = 2254697) B2254697
theorem B7819183 : Blo 1502071 7819183 := bstep (se 1 (by rfl) ⟨5864387, by rfl⟩ : syracuseStep 7819183 = 11728775) B11728775
theorem B1503183 : Blo 1502071 1503183 := bstep (se 1 (by rfl) ⟨1127387, by rfl⟩ : syracuseStep 1503183 = 2254775) B2254775
theorem B9760733 : Blo 1502071 9760733 := bstep (se 3 (by rfl) ⟨1830137, by rfl⟩ : syracuseStep 9760733 = 3660275) B3660275
theorem B1503207 : Blo 1502071 1503207 := bstep (se 1 (by rfl) ⟨1127405, by rfl⟩ : syracuseStep 1503207 = 2254811) B2254811
theorem B12832769 : Blo 1502071 12832769 := bstep (se 2 (by rfl) ⟨4812288, by rfl⟩ : syracuseStep 12832769 = 9624577) B9624577
theorem B2535529 : Blo 1502071 2535529 := bstep (se 2 (by rfl) ⟨950823, by rfl⟩ : syracuseStep 2535529 = 1901647) B1901647
theorem B3805289 : Blo 1502071 3805289 := bstep (se 2 (by rfl) ⟨1426983, by rfl⟩ : syracuseStep 3805289 = 2853967) B2853967
theorem B1503519 : Blo 1502071 1503519 := bstep (se 1 (by rfl) ⟨1127639, by rfl⟩ : syracuseStep 1503519 = 2255279) B2255279
theorem B16691561 : Blo 1502071 16691561 := bstep (se 2 (by rfl) ⟨6259335, by rfl⟩ : syracuseStep 16691561 = 12518671) B12518671
theorem B3428783 : Blo 1502071 3428783 := bstep (se 1 (by rfl) ⟨2571587, by rfl⟩ : syracuseStep 3428783 = 5143175) B5143175
theorem B3658303 : Blo 1502071 3658303 := bstep (se 1 (by rfl) ⟨2743727, by rfl⟩ : syracuseStep 3658303 = 5487455) B5487455
theorem B3609161 : Blo 1502071 3609161 := bstep (se 2 (by rfl) ⟨1353435, by rfl⟩ : syracuseStep 3609161 = 2706871) B2706871
theorem B3805775 : Blo 1502071 3805775 := bstep (se 1 (by rfl) ⟨2854331, by rfl⟩ : syracuseStep 3805775 = 5708663) B5708663
theorem B3379895 : Blo 1502071 3379895 := bstep (se 1 (by rfl) ⟨2534921, by rfl⟩ : syracuseStep 3379895 = 5069843) B5069843
theorem B8458951 : Blo 1502071 8458951 := bstep (se 1 (by rfl) ⟨6344213, by rfl⟩ : syracuseStep 8458951 = 12688427) B12688427
theorem B6853319 : Blo 1502071 6853319 := bstep (se 1 (by rfl) ⟨5139989, by rfl⟩ : syracuseStep 6853319 = 10279979) B10279979
theorem B7607033 : Blo 1502071 7607033 := bstep (se 2 (by rfl) ⟨2852637, by rfl⟩ : syracuseStep 7607033 = 5705275) B5705275
theorem B4281167 : Blo 1502071 4281167 := bstep (se 1 (by rfl) ⟨3210875, by rfl⟩ : syracuseStep 4281167 = 6421751) B6421751
theorem B3380111 : Blo 1502071 3380111 := bstep (se 1 (by rfl) ⟨2535083, by rfl⟩ : syracuseStep 3380111 = 5070167) B5070167
theorem B2708471 : Blo 1502071 2708471 := bstep (se 1 (by rfl) ⟨2031353, by rfl⟩ : syracuseStep 2708471 = 4062707) B4062707
theorem B6419513 : Blo 1502071 6419513 := bstep (se 2 (by rfl) ⟨2407317, by rfl⟩ : syracuseStep 6419513 = 4814635) B4814635
theorem B28890269 : Blo 1502071 28890269 := bstep (se 3 (by rfl) ⟨5416925, by rfl⟩ : syracuseStep 28890269 = 10833851) B10833851
theorem B3380831 : Blo 1502071 3380831 := bstep (se 1 (by rfl) ⟨2535623, by rfl⟩ : syracuseStep 3380831 = 5071247) B5071247
theorem B2537257 : Blo 1502071 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B3381047 : Blo 1502071 3381047 := bstep (se 1 (by rfl) ⟨2535785, by rfl⟩ : syracuseStep 3381047 = 5071571) B5071571
theorem B82245689 : Blo 1502071 82245689 := bstep (se 2 (by rfl) ⟨30842133, by rfl⟩ : syracuseStep 82245689 = 61684267) B61684267
theorem B3209321 : Blo 1502071 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B3381353 : Blo 1502071 3381353 := bstep (se 2 (by rfl) ⟨1268007, by rfl⟩ : syracuseStep 3381353 = 2536015) B2536015
theorem B6093085 : Blo 1502071 6093085 := bstep (se 3 (by rfl) ⟨1142453, by rfl⟩ : syracuseStep 6093085 = 2284907) B2284907
theorem B10836301 : Blo 1502071 10836301 := bstep (se 3 (by rfl) ⟨2031806, by rfl⟩ : syracuseStep 10836301 = 4063613) B4063613
theorem B4118951 : Blo 1502071 4118951 := bstep (se 1 (by rfl) ⟨3089213, by rfl⟩ : syracuseStep 4118951 = 6178427) B6178427
theorem B25688501 : Blo 1502071 25688501 := bstep (se 5 (by rfl) ⟨1204148, by rfl⟩ : syracuseStep 25688501 = 2408297) B2408297
theorem B12835367 : Blo 1502071 12835367 := bstep (se 1 (by rfl) ⟨9626525, by rfl⟩ : syracuseStep 12835367 = 19253051) B19253051
theorem B3381839 : Blo 1502071 3381839 := bstep (se 1 (by rfl) ⟨2536379, by rfl⟩ : syracuseStep 3381839 = 5072759) B5072759
theorem B4815467 : Blo 1502071 4815467 := bstep (se 1 (by rfl) ⟨3611600, by rfl⟩ : syracuseStep 4815467 = 7223201) B7223201
theorem B3381983 : Blo 1502071 3381983 := bstep (se 1 (by rfl) ⟨2536487, by rfl⟩ : syracuseStep 3381983 = 5072975) B5072975
theorem B7322359 : Blo 1502071 7322359 := bstep (se 1 (by rfl) ⟨5491769, by rfl⟩ : syracuseStep 7322359 = 10983539) B10983539
theorem B16071443 : Blo 1502071 16071443 := bstep (se 1 (by rfl) ⟨12053582, by rfl⟩ : syracuseStep 16071443 = 24107165) B24107165
theorem B2407247 : Blo 1502071 2407247 := bstep (se 1 (by rfl) ⟨1805435, by rfl⟩ : syracuseStep 2407247 = 3610871) B3610871
theorem B3046315 : Blo 1502071 3046315 := bstep (se 1 (by rfl) ⟨2284736, by rfl⟩ : syracuseStep 3046315 = 4569473) B4569473
theorem B3382235 : Blo 1502071 3382235 := bstep (se 1 (by rfl) ⟨2536676, by rfl⟩ : syracuseStep 3382235 = 5073353) B5073353
theorem B2284519 : Blo 1502071 2284519 := bstep (se 1 (by rfl) ⟨1713389, by rfl⟩ : syracuseStep 2284519 = 3426779) B3426779
theorem B6855667 : Blo 1502071 6855667 := bstep (se 1 (by rfl) ⟨5141750, by rfl⟩ : syracuseStep 6855667 = 10283501) B10283501
theorem B6093863 : Blo 1502071 6093863 := bstep (se 1 (by rfl) ⟨4570397, by rfl⟩ : syracuseStep 6093863 = 9140795) B9140795
theorem B3382415 : Blo 1502071 3382415 := bstep (se 1 (by rfl) ⟨2536811, by rfl⟩ : syracuseStep 3382415 = 5073623) B5073623
theorem B5782747 : Blo 1502071 5782747 := bstep (se 1 (by rfl) ⟨4337060, by rfl⟩ : syracuseStep 5782747 = 8674121) B8674121
theorem B2407657 : Blo 1502071 2407657 := bstep (se 2 (by rfl) ⟨902871, by rfl⟩ : syracuseStep 2407657 = 1805743) B1805743
theorem B3382505 : Blo 1502071 3382505 := bstep (se 2 (by rfl) ⟨1268439, by rfl⟩ : syracuseStep 3382505 = 2536879) B2536879
theorem B3382559 : Blo 1502071 3382559 := bstep (se 1 (by rfl) ⟨2536919, by rfl⟩ : syracuseStep 3382559 = 5073839) B5073839
theorem B3210619 : Blo 1502071 3210619 := bstep (se 1 (by rfl) ⟨2407964, by rfl⟩ : syracuseStep 3210619 = 4815929) B4815929
theorem B7609787 : Blo 1502071 7609787 := bstep (se 1 (by rfl) ⟨5707340, by rfl⟩ : syracuseStep 7609787 = 11414681) B11414681
theorem B2891207 : Blo 1502071 2891207 := bstep (se 1 (by rfl) ⟨2168405, by rfl⟩ : syracuseStep 2891207 = 4336811) B4336811
theorem B5070329 : Blo 1502071 5070329 := bstep (se 2 (by rfl) ⟨1901373, by rfl⟩ : syracuseStep 5070329 = 3802747) B3802747
theorem B9625169 : Blo 1502071 9625169 := bstep (se 2 (by rfl) ⟨3609438, by rfl⟩ : syracuseStep 9625169 = 7218877) B7218877
theorem B6422111 : Blo 1502071 6422111 := bstep (se 1 (by rfl) ⟨4816583, by rfl⟩ : syracuseStep 6422111 = 9633167) B9633167
theorem B5488391 : Blo 1502071 5488391 := bstep (se 1 (by rfl) ⟨4116293, by rfl⟩ : syracuseStep 5488391 = 8232587) B8232587
theorem B5414663 : Blo 1502071 5414663 := bstep (se 1 (by rfl) ⟨4060997, by rfl⟩ : syracuseStep 5414663 = 8121995) B8121995
theorem B5070599 : Blo 1502071 5070599 := bstep (se 1 (by rfl) ⟨3802949, by rfl⟩ : syracuseStep 5070599 = 7605899) B7605899
theorem B6504203 : Blo 1502071 6504203 := bstep (se 1 (by rfl) ⟨4878152, by rfl⟩ : syracuseStep 6504203 = 9756305) B9756305
theorem B5070653 : Blo 1502071 5070653 := bstep (se 3 (by rfl) ⟨950747, by rfl⟩ : syracuseStep 5070653 = 1901495) B1901495
theorem B14442401 : Blo 1502071 14442401 := bstep (se 2 (by rfl) ⟨5415900, by rfl⟩ : syracuseStep 14442401 = 10831801) B10831801
theorem B1605583 : Blo 1502071 1605583 := bstep (se 1 (by rfl) ⟨1204187, by rfl⟩ : syracuseStep 1605583 = 2408375) B2408375
theorem B2285855 : Blo 1502071 2285855 := bstep (se 1 (by rfl) ⟨1714391, by rfl⟩ : syracuseStep 2285855 = 3428783) B3428783
theorem B2253263 : Blo 1502071 2253263 := bstep (se 1 (by rfl) ⟨1689947, by rfl⟩ : syracuseStep 2253263 = 3379895) B3379895
theorem B2253305 : Blo 1502071 2253305 := bstep (se 2 (by rfl) ⟨844989, by rfl⟩ : syracuseStep 2253305 = 1689979) B1689979
theorem B5071355 : Blo 1502071 5071355 := bstep (se 1 (by rfl) ⟨3803516, by rfl⟩ : syracuseStep 5071355 = 7607033) B7607033
theorem B2253407 : Blo 1502071 2253407 := bstep (se 1 (by rfl) ⟨1690055, by rfl⟩ : syracuseStep 2253407 = 3380111) B3380111
theorem B5071625 : Blo 1502071 5071625 := bstep (se 2 (by rfl) ⟨1901859, by rfl⟩ : syracuseStep 5071625 = 3803719) B3803719
theorem B19260179 : Blo 1502071 19260179 := bstep (se 1 (by rfl) ⟨14445134, by rfl⟩ : syracuseStep 19260179 = 28890269) B28890269
theorem B2253887 : Blo 1502071 2253887 := bstep (se 1 (by rfl) ⟨1690415, by rfl⟩ : syracuseStep 2253887 = 3380831) B3380831
theorem B79144037 : Blo 1502071 79144037 := bstep (se 4 (by rfl) ⟨7419753, by rfl⟩ : syracuseStep 79144037 = 14839507) B14839507
theorem B2253929 : Blo 1502071 2253929 := bstep (se 2 (by rfl) ⟨845223, by rfl⟩ : syracuseStep 2253929 = 1690447) B1690447
theorem B2254031 : Blo 1502071 2254031 := bstep (se 1 (by rfl) ⟨1690523, by rfl⟩ : syracuseStep 2254031 = 3381047) B3381047
theorem B54830459 : Blo 1502071 54830459 := bstep (se 1 (by rfl) ⟨41122844, by rfl⟩ : syracuseStep 54830459 = 82245689) B82245689
theorem B2139547 : Blo 1502071 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B2254235 : Blo 1502071 2254235 := bstep (se 1 (by rfl) ⟨1690676, by rfl⟩ : syracuseStep 2254235 = 3381353) B3381353
theorem B5072381 : Blo 1502071 5072381 := bstep (se 3 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 5072381 = 1902143) B1902143
theorem B2745967 : Blo 1502071 2745967 := bstep (se 1 (by rfl) ⟨2059475, by rfl⟩ : syracuseStep 2745967 = 4118951) B4118951
theorem B7710329 : Blo 1502071 7710329 := bstep (se 2 (by rfl) ⟨2891373, by rfl⟩ : syracuseStep 7710329 = 5782747) B5782747
theorem B2254457 : Blo 1502071 2254457 := bstep (se 2 (by rfl) ⟨845421, by rfl⟩ : syracuseStep 2254457 = 1690843) B1690843
theorem B2254559 : Blo 1502071 2254559 := bstep (se 1 (by rfl) ⟨1690919, by rfl⟩ : syracuseStep 2254559 = 3381839) B3381839
theorem B2254655 : Blo 1502071 2254655 := bstep (se 1 (by rfl) ⟨1690991, by rfl⟩ : syracuseStep 2254655 = 3381983) B3381983
theorem B2254823 : Blo 1502071 2254823 := bstep (se 1 (by rfl) ⟨1691117, by rfl⟩ : syracuseStep 2254823 = 3382235) B3382235
theorem B3426295 : Blo 1502071 3426295 := bstep (se 1 (by rfl) ⟨2569721, by rfl⟩ : syracuseStep 3426295 = 5139443) B5139443
theorem B2254841 : Blo 1502071 2254841 := bstep (se 2 (by rfl) ⟨845565, by rfl⟩ : syracuseStep 2254841 = 1691131) B1691131
theorem B2254943 : Blo 1502071 2254943 := bstep (se 1 (by rfl) ⟨1691207, by rfl⟩ : syracuseStep 2254943 = 3382415) B3382415
theorem B12839057 : Blo 1502071 12839057 := bstep (se 2 (by rfl) ⟨4814646, by rfl⟩ : syracuseStep 12839057 = 9629293) B9629293
theorem B2255003 : Blo 1502071 2255003 := bstep (se 1 (by rfl) ⟨1691252, by rfl⟩ : syracuseStep 2255003 = 3382505) B3382505
theorem B2255039 : Blo 1502071 2255039 := bstep (se 1 (by rfl) ⟨1691279, by rfl⟩ : syracuseStep 2255039 = 3382559) B3382559
theorem B2255081 : Blo 1502071 2255081 := bstep (se 2 (by rfl) ⟨845655, by rfl⟩ : syracuseStep 2255081 = 1691311) B1691311
theorem B5073191 : Blo 1502071 5073191 := bstep (se 1 (by rfl) ⟨3804893, by rfl⟩ : syracuseStep 5073191 = 7609787) B7609787
theorem B6179111 : Blo 1502071 6179111 := bstep (se 1 (by rfl) ⟨4634333, by rfl⟩ : syracuseStep 6179111 = 9268667) B9268667
theorem B2197801 : Blo 1502071 2197801 := bstep (se 2 (by rfl) ⟨824175, by rfl⟩ : syracuseStep 2197801 = 1648351) B1648351
theorem B1927471 : Blo 1502071 1927471 := bstep (se 1 (by rfl) ⟨1445603, by rfl⟩ : syracuseStep 1927471 = 2891207) B2891207
theorem B6416779 : Blo 1502071 6416779 := bstep (se 1 (by rfl) ⟨4812584, by rfl⟩ : syracuseStep 6416779 = 9625169) B9625169
theorem B38513069 : Blo 1502071 38513069 := bstep (se 3 (by rfl) ⟨7221200, by rfl⟩ : syracuseStep 38513069 = 14442401) B14442401
theorem B4336135 : Blo 1502071 4336135 := bstep (se 1 (by rfl) ⟨3252101, by rfl⟩ : syracuseStep 4336135 = 6504203) B6504203
theorem B36563557 : Blo 1502071 36563557 := bstep (se 4 (by rfl) ⟨3427833, by rfl⟩ : syracuseStep 36563557 = 6855667) B6855667
theorem B2853481 : Blo 1502071 2853481 := bstep (se 2 (by rfl) ⟨1070055, by rfl⟩ : syracuseStep 2853481 = 2140111) B2140111
theorem B2140777 : Blo 1502071 2140777 := bstep (se 2 (by rfl) ⟨802791, by rfl⟩ : syracuseStep 2140777 = 1605583) B1605583
theorem B6507155 : Blo 1502071 6507155 := bstep (se 1 (by rfl) ⟨4880366, by rfl⟩ : syracuseStep 6507155 = 9760733) B9760733
theorem B8555179 : Blo 1502071 8555179 := bstep (se 1 (by rfl) ⟨6416384, by rfl⟩ : syracuseStep 8555179 = 12832769) B12832769
theorem B11127707 : Blo 1502071 11127707 := bstep (se 1 (by rfl) ⟨8345780, by rfl⟩ : syracuseStep 11127707 = 16691561) B16691561
theorem B1502111 : Blo 1502071 1502111 := bstep (se 1 (by rfl) ⟨1126583, by rfl⟩ : syracuseStep 1502111 = 2253167) B2253167
theorem B21130247 : Blo 1502071 21130247 := bstep (se 1 (by rfl) ⟨15847685, by rfl⟩ : syracuseStep 21130247 = 31695371) B31695371
theorem B1502255 : Blo 1502071 1502255 := bstep (se 1 (by rfl) ⟨1126691, by rfl⟩ : syracuseStep 1502255 = 2253383) B2253383
theorem B1502279 : Blo 1502071 1502279 := bstep (se 1 (by rfl) ⟨1126709, by rfl⟩ : syracuseStep 1502279 = 2253419) B2253419
theorem B20556935 : Blo 1502071 20556935 := bstep (se 1 (by rfl) ⟨15417701, by rfl⟩ : syracuseStep 20556935 = 30835403) B30835403
theorem B5074055 : Blo 1502071 5074055 := bstep (se 1 (by rfl) ⟨3805541, by rfl⟩ : syracuseStep 5074055 = 7611083) B7611083
theorem B1502431 : Blo 1502071 1502431 := bstep (se 1 (by rfl) ⟨1126823, by rfl⟩ : syracuseStep 1502431 = 2253647) B2253647
theorem B2854111 : Blo 1502071 2854111 := bstep (se 1 (by rfl) ⟨2140583, by rfl⟩ : syracuseStep 2854111 = 4281167) B4281167
theorem B5074163 : Blo 1502071 5074163 := bstep (se 1 (by rfl) ⟨3805622, by rfl⟩ : syracuseStep 5074163 = 7611245) B7611245
theorem B1805647 : Blo 1502071 1805647 := bstep (se 1 (by rfl) ⟨1354235, by rfl⟩ : syracuseStep 1805647 = 2708471) B2708471
theorem B4279675 : Blo 1502071 4279675 := bstep (se 1 (by rfl) ⟨3209756, by rfl⟩ : syracuseStep 4279675 = 6419513) B6419513
theorem B1502695 : Blo 1502071 1502695 := bstep (se 1 (by rfl) ⟨1127021, by rfl⟩ : syracuseStep 1502695 = 2254043) B2254043
theorem B1502811 : Blo 1502071 1502811 := bstep (se 1 (by rfl) ⟨1127108, by rfl⟩ : syracuseStep 1502811 = 2254217) B2254217
theorem B2535239 : Blo 1502071 2535239 := bstep (se 1 (by rfl) ⟨1901429, by rfl⟩ : syracuseStep 2535239 = 3802859) B3802859
theorem B1503047 : Blo 1502071 1503047 := bstep (se 1 (by rfl) ⟨1127285, by rfl⟩ : syracuseStep 1503047 = 2254571) B2254571
theorem B1503199 : Blo 1502071 1503199 := bstep (se 1 (by rfl) ⟨1127399, by rfl⟩ : syracuseStep 1503199 = 2254799) B2254799
theorem B1503463 : Blo 1502071 1503463 := bstep (se 1 (by rfl) ⟨1127597, by rfl⟩ : syracuseStep 1503463 = 2255195) B2255195
theorem B17125667 : Blo 1502071 17125667 := bstep (se 1 (by rfl) ⟨12844250, by rfl⟩ : syracuseStep 17125667 = 25688501) B25688501
theorem B8556911 : Blo 1502071 8556911 := bstep (se 1 (by rfl) ⟨6417683, by rfl⟩ : syracuseStep 8556911 = 12835367) B12835367
theorem B7713161 : Blo 1502071 7713161 := bstep (se 2 (by rfl) ⟨2892435, by rfl⟩ : syracuseStep 7713161 = 5784871) B5784871
theorem B2535887 : Blo 1502071 2535887 := bstep (se 1 (by rfl) ⟨1901915, by rfl⟩ : syracuseStep 2535887 = 3803831) B3803831
theorem B4280825 : Blo 1502071 4280825 := bstep (se 2 (by rfl) ⟨1605309, by rfl⟩ : syracuseStep 4280825 = 3210619) B3210619
theorem B5706521 : Blo 1502071 5706521 := bstep (se 2 (by rfl) ⟨2139945, by rfl⟩ : syracuseStep 5706521 = 4279891) B4279891
theorem B21951461 : Blo 1502071 21951461 := bstep (se 4 (by rfl) ⟨2057949, by rfl⟩ : syracuseStep 21951461 = 4115899) B4115899
theorem B3380219 : Blo 1502071 3380219 := bstep (se 1 (by rfl) ⟨2535164, by rfl⟩ : syracuseStep 3380219 = 5070329) B5070329
theorem B4281407 : Blo 1502071 4281407 := bstep (se 1 (by rfl) ⟨3211055, by rfl⟩ : syracuseStep 4281407 = 6422111) B6422111
theorem B2536555 : Blo 1502071 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B3658927 : Blo 1502071 3658927 := bstep (se 1 (by rfl) ⟨2744195, by rfl⟩ : syracuseStep 3658927 = 5488391) B5488391
theorem B3609775 : Blo 1502071 3609775 := bstep (se 1 (by rfl) ⟨2707331, by rfl⟩ : syracuseStep 3609775 = 5414663) B5414663
theorem B3380399 : Blo 1502071 3380399 := bstep (se 1 (by rfl) ⟨2535299, by rfl⟩ : syracuseStep 3380399 = 5070599) B5070599
theorem B3380435 : Blo 1502071 3380435 := bstep (se 1 (by rfl) ⟨2535326, by rfl⟩ : syracuseStep 3380435 = 5070653) B5070653
theorem B10425577 : Blo 1502071 10425577 := bstep (se 2 (by rfl) ⟨3909591, by rfl⟩ : syracuseStep 10425577 = 7819183) B7819183
theorem B25671005 : Blo 1502071 25671005 := bstep (se 3 (by rfl) ⟨4813313, by rfl⟩ : syracuseStep 25671005 = 9626627) B9626627
theorem B2536859 : Blo 1502071 2536859 := bstep (se 1 (by rfl) ⟨1902644, by rfl⟩ : syracuseStep 2536859 = 3805289) B3805289
theorem B3380705 : Blo 1502071 3380705 := bstep (se 2 (by rfl) ⟨1267764, by rfl⟩ : syracuseStep 3380705 = 2535529) B2535529
theorem B19510949 : Blo 1502071 19510949 := bstep (se 4 (by rfl) ⟨1829151, by rfl⟩ : syracuseStep 19510949 = 3658303) B3658303
theorem B8124113 : Blo 1502071 8124113 := bstep (se 2 (by rfl) ⟨3046542, by rfl⟩ : syracuseStep 8124113 = 6093085) B6093085
theorem B2406107 : Blo 1502071 2406107 := bstep (se 1 (by rfl) ⟨1804580, by rfl⟩ : syracuseStep 2406107 = 3609161) B3609161
theorem B2537183 : Blo 1502071 2537183 := bstep (se 1 (by rfl) ⟨1902887, by rfl⟩ : syracuseStep 2537183 = 3805775) B3805775
theorem B14448401 : Blo 1502071 14448401 := bstep (se 2 (by rfl) ⟨5418150, by rfl⟩ : syracuseStep 14448401 = 10836301) B10836301
theorem B4568879 : Blo 1502071 4568879 := bstep (se 1 (by rfl) ⟨3426659, by rfl⟩ : syracuseStep 4568879 = 6853319) B6853319
theorem B4814749 : Blo 1502071 4814749 := bstep (se 3 (by rfl) ⟨902765, by rfl⟩ : syracuseStep 4814749 = 1805531) B1805531
theorem B11278601 : Blo 1502071 11278601 := bstep (se 2 (by rfl) ⟨4229475, by rfl⟩ : syracuseStep 11278601 = 8458951) B8458951
theorem B9763145 : Blo 1502071 9763145 := bstep (se 2 (by rfl) ⟨3661179, by rfl⟩ : syracuseStep 9763145 = 7322359) B7322359
theorem B4061753 : Blo 1502071 4061753 := bstep (se 2 (by rfl) ⟨1523157, by rfl⟩ : syracuseStep 4061753 = 3046315) B3046315
theorem B3046025 : Blo 1502071 3046025 := bstep (se 2 (by rfl) ⟨1142259, by rfl⟩ : syracuseStep 3046025 = 2284519) B2284519
theorem B3210209 : Blo 1502071 3210209 := bstep (se 2 (by rfl) ⟨1203828, by rfl⟩ : syracuseStep 3210209 = 2407657) B2407657
theorem B3210311 : Blo 1502071 3210311 := bstep (se 1 (by rfl) ⟨2407733, by rfl⟩ : syracuseStep 3210311 = 4815467) B4815467
theorem B3382343 : Blo 1502071 3382343 := bstep (se 1 (by rfl) ⟨2536757, by rfl⟩ : syracuseStep 3382343 = 5073515) B5073515
theorem B10714295 : Blo 1502071 10714295 := bstep (se 1 (by rfl) ⟨8035721, by rfl⟩ : syracuseStep 10714295 = 16071443) B16071443
theorem B1604831 : Blo 1502071 1604831 := bstep (se 1 (by rfl) ⟨1203623, by rfl⟩ : syracuseStep 1604831 = 2407247) B2407247
theorem B4062575 : Blo 1502071 4062575 := bstep (se 1 (by rfl) ⟨3046931, by rfl⟩ : syracuseStep 4062575 = 6093863) B6093863
theorem B3382739 : Blo 1502071 3382739 := bstep (se 1 (by rfl) ⟨2537054, by rfl⟩ : syracuseStep 3382739 = 5074109) B5074109
theorem B3383009 : Blo 1502071 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B92504213 : Blo 1502071 92504213 := bstep (se 6 (by rfl) ⟨2168067, by rfl⟩ : syracuseStep 92504213 = 4336135) B4336135
theorem B8560829 : Blo 1502071 8560829 := bstep (se 3 (by rfl) ⟨1605155, by rfl⟩ : syracuseStep 8560829 = 3210311) B3210311
theorem B2253479 : Blo 1502071 2253479 := bstep (se 1 (by rfl) ⟨1690109, by rfl⟩ : syracuseStep 2253479 = 3380219) B3380219
theorem B2253599 : Blo 1502071 2253599 := bstep (se 1 (by rfl) ⟨1690199, by rfl⟩ : syracuseStep 2253599 = 3380399) B3380399
theorem B48751409 : Blo 1502071 48751409 := bstep (se 2 (by rfl) ⟨18281778, by rfl⟩ : syracuseStep 48751409 = 36563557) B36563557
theorem B2253623 : Blo 1502071 2253623 := bstep (se 1 (by rfl) ⟨1690217, by rfl⟩ : syracuseStep 2253623 = 3380435) B3380435
theorem B17114003 : Blo 1502071 17114003 := bstep (se 1 (by rfl) ⟨12835502, by rfl⟩ : syracuseStep 17114003 = 25671005) B25671005
theorem B36553639 : Blo 1502071 36553639 := bstep (se 1 (by rfl) ⟨27415229, by rfl⟩ : syracuseStep 36553639 = 54830459) B54830459
theorem B2253803 : Blo 1502071 2253803 := bstep (se 1 (by rfl) ⟨1690352, by rfl⟩ : syracuseStep 2253803 = 3380705) B3380705
theorem B5416075 : Blo 1502071 5416075 := bstep (se 1 (by rfl) ⟨4062056, by rfl⟩ : syracuseStep 5416075 = 8124113) B8124113
theorem B25675379 : Blo 1502071 25675379 := bstep (se 1 (by rfl) ⟨19256534, by rfl⟩ : syracuseStep 25675379 = 38513069) B38513069
theorem B2852729 : Blo 1502071 2852729 := bstep (se 2 (by rfl) ⟨1069773, by rfl⟩ : syracuseStep 2852729 = 2139547) B2139547
theorem B2140139 : Blo 1502071 2140139 := bstep (se 1 (by rfl) ⟨1605104, by rfl⟩ : syracuseStep 2140139 = 3210209) B3210209
theorem B2254895 : Blo 1502071 2254895 := bstep (se 1 (by rfl) ⟨1691171, by rfl⟩ : syracuseStep 2254895 = 3382343) B3382343
theorem B2255159 : Blo 1502071 2255159 := bstep (se 1 (by rfl) ⟨1691369, by rfl⟩ : syracuseStep 2255159 = 3382739) B3382739
theorem B2255339 : Blo 1502071 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B1690159 : Blo 1502071 1690159 := bstep (se 1 (by rfl) ⟨1267619, by rfl⟩ : syracuseStep 1690159 = 2535239) B2535239
theorem B56347325 : Blo 1502071 56347325 := bstep (se 3 (by rfl) ⟨10565123, by rfl⟩ : syracuseStep 56347325 = 21130247) B21130247
theorem B5704607 : Blo 1502071 5704607 := bstep (se 1 (by rfl) ⟨4278455, by rfl⟩ : syracuseStep 5704607 = 8556911) B8556911
theorem B1502175 : Blo 1502071 1502175 := bstep (se 1 (by rfl) ⟨1126631, by rfl⟩ : syracuseStep 1502175 = 2253263) B2253263
theorem B1690591 : Blo 1502071 1690591 := bstep (se 1 (by rfl) ⟨1267943, by rfl⟩ : syracuseStep 1690591 = 2535887) B2535887
theorem B24382453 : Blo 1502071 24382453 := bstep (se 5 (by rfl) ⟨1142927, by rfl⟩ : syracuseStep 24382453 = 2285855) B2285855
theorem B1502203 : Blo 1502071 1502203 := bstep (se 1 (by rfl) ⟨1126652, by rfl⟩ : syracuseStep 1502203 = 2253305) B2253305
theorem B2853883 : Blo 1502071 2853883 := bstep (se 1 (by rfl) ⟨2140412, by rfl⟩ : syracuseStep 2853883 = 4280825) B4280825
theorem B1502271 : Blo 1502071 1502271 := bstep (se 1 (by rfl) ⟨1126703, by rfl⟩ : syracuseStep 1502271 = 2253407) B2253407
theorem B8555705 : Blo 1502071 8555705 := bstep (se 2 (by rfl) ⟨3208389, by rfl⟩ : syracuseStep 8555705 = 6416779) B6416779
theorem B12840119 : Blo 1502071 12840119 := bstep (se 1 (by rfl) ⟨9630089, by rfl⟩ : syracuseStep 12840119 = 19260179) B19260179
theorem B3804347 : Blo 1502071 3804347 := bstep (se 1 (by rfl) ⟨2853260, by rfl⟩ : syracuseStep 3804347 = 5706521) B5706521
theorem B4279549 : Blo 1502071 4279549 := bstep (se 3 (by rfl) ⟨802415, by rfl⟩ : syracuseStep 4279549 = 1604831) B1604831
theorem B14634307 : Blo 1502071 14634307 := bstep (se 1 (by rfl) ⟨10975730, by rfl⟩ : syracuseStep 14634307 = 21951461) B21951461
theorem B1502591 : Blo 1502071 1502591 := bstep (se 1 (by rfl) ⟨1126943, by rfl⟩ : syracuseStep 1502591 = 2253887) B2253887
theorem B2854271 : Blo 1502071 2854271 := bstep (se 1 (by rfl) ⟨2140703, by rfl⟩ : syracuseStep 2854271 = 4281407) B4281407
theorem B1502619 : Blo 1502071 1502619 := bstep (se 1 (by rfl) ⟨1126964, by rfl⟩ : syracuseStep 1502619 = 2253929) B2253929
theorem B1502687 : Blo 1502071 1502687 := bstep (se 1 (by rfl) ⟨1127015, by rfl⟩ : syracuseStep 1502687 = 2254031) B2254031
theorem B3804641 : Blo 1502071 3804641 := bstep (se 2 (by rfl) ⟨1426740, by rfl⟩ : syracuseStep 3804641 = 2853481) B2853481
theorem B2854369 : Blo 1502071 2854369 := bstep (se 2 (by rfl) ⟨1070388, by rfl⟩ : syracuseStep 2854369 = 2140777) B2140777
theorem B11406905 : Blo 1502071 11406905 := bstep (se 2 (by rfl) ⟨4277589, by rfl⟩ : syracuseStep 11406905 = 8555179) B8555179
theorem B1502823 : Blo 1502071 1502823 := bstep (se 1 (by rfl) ⟨1127117, by rfl⟩ : syracuseStep 1502823 = 2254235) B2254235
theorem B1691239 : Blo 1502071 1691239 := bstep (se 1 (by rfl) ⟨1268429, by rfl⟩ : syracuseStep 1691239 = 2536859) B2536859
theorem B10833533 : Blo 1502071 10833533 := bstep (se 3 (by rfl) ⟨2031287, by rfl⟩ : syracuseStep 10833533 = 4062575) B4062575
theorem B1502971 : Blo 1502071 1502971 := bstep (se 1 (by rfl) ⟨1127228, by rfl⟩ : syracuseStep 1502971 = 2254457) B2254457
theorem B1503039 : Blo 1502071 1503039 := bstep (se 1 (by rfl) ⟨1127279, by rfl⟩ : syracuseStep 1503039 = 2254559) B2254559
theorem B1691455 : Blo 1502071 1691455 := bstep (se 1 (by rfl) ⟨1268591, by rfl⟩ : syracuseStep 1691455 = 2537183) B2537183
theorem B1503103 : Blo 1502071 1503103 := bstep (se 1 (by rfl) ⟨1127327, by rfl⟩ : syracuseStep 1503103 = 2254655) B2254655
theorem B1503215 : Blo 1502071 1503215 := bstep (se 1 (by rfl) ⟨1127411, by rfl⟩ : syracuseStep 1503215 = 2254823) B2254823
theorem B1503227 : Blo 1502071 1503227 := bstep (se 1 (by rfl) ⟨1127420, by rfl⟩ : syracuseStep 1503227 = 2254841) B2254841
theorem B1503295 : Blo 1502071 1503295 := bstep (se 1 (by rfl) ⟨1127471, by rfl⟩ : syracuseStep 1503295 = 2254943) B2254943
theorem B1503335 : Blo 1502071 1503335 := bstep (se 1 (by rfl) ⟨1127501, by rfl⟩ : syracuseStep 1503335 = 2255003) B2255003
theorem B1503359 : Blo 1502071 1503359 := bstep (se 1 (by rfl) ⟨1127519, by rfl⟩ : syracuseStep 1503359 = 2255039) B2255039
theorem B1503387 : Blo 1502071 1503387 := bstep (se 1 (by rfl) ⟨1127540, by rfl⟩ : syracuseStep 1503387 = 2255081) B2255081
theorem B6508763 : Blo 1502071 6508763 := bstep (se 1 (by rfl) ⟨4881572, by rfl⟩ : syracuseStep 6508763 = 9763145) B9763145
theorem B4878569 : Blo 1502071 4878569 := bstep (se 2 (by rfl) ⟨1829463, by rfl⟩ : syracuseStep 4878569 = 3658927) B3658927
theorem B4813033 : Blo 1502071 4813033 := bstep (se 2 (by rfl) ⟨1804887, by rfl⟩ : syracuseStep 4813033 = 3609775) B3609775
theorem B3805481 : Blo 1502071 3805481 := bstep (se 2 (by rfl) ⟨1427055, by rfl⟩ : syracuseStep 3805481 = 2854111) B2854111
theorem B2707835 : Blo 1502071 2707835 := bstep (se 1 (by rfl) ⟨2030876, by rfl⟩ : syracuseStep 2707835 = 4061753) B4061753
theorem B4338103 : Blo 1502071 4338103 := bstep (se 1 (by rfl) ⟨3253577, by rfl⟩ : syracuseStep 4338103 = 6507155) B6507155
theorem B5706233 : Blo 1502071 5706233 := bstep (se 2 (by rfl) ⟨2139837, by rfl⟩ : syracuseStep 5706233 = 4279675) B4279675
theorem B7418471 : Blo 1502071 7418471 := bstep (se 1 (by rfl) ⟨5563853, by rfl⟩ : syracuseStep 7418471 = 11127707) B11127707
theorem B6419665 : Blo 1502071 6419665 := bstep (se 2 (by rfl) ⟨2407374, by rfl⟩ : syracuseStep 6419665 = 4814749) B4814749
theorem B4568393 : Blo 1502071 4568393 := bstep (se 2 (by rfl) ⟨1713147, by rfl⟩ : syracuseStep 4568393 = 3426295) B3426295
theorem B11417111 : Blo 1502071 11417111 := bstep (se 1 (by rfl) ⟨8562833, by rfl⟩ : syracuseStep 11417111 = 17125667) B17125667
theorem B5142107 : Blo 1502071 5142107 := bstep (se 1 (by rfl) ⟨3856580, by rfl⟩ : syracuseStep 5142107 = 7713161) B7713161
theorem B3380903 : Blo 1502071 3380903 := bstep (se 1 (by rfl) ⟨2535677, by rfl⟩ : syracuseStep 3380903 = 5071355) B5071355
theorem B2930401 : Blo 1502071 2930401 := bstep (se 2 (by rfl) ⟨1098900, by rfl⟩ : syracuseStep 2930401 = 2197801) B2197801
theorem B2569961 : Blo 1502071 2569961 := bstep (se 2 (by rfl) ⟨963735, by rfl⟩ : syracuseStep 2569961 = 1927471) B1927471
theorem B3381083 : Blo 1502071 3381083 := bstep (se 1 (by rfl) ⟨2535812, by rfl⟩ : syracuseStep 3381083 = 5071625) B5071625
theorem B52762691 : Blo 1502071 52762691 := bstep (se 1 (by rfl) ⟨39572018, by rfl⟩ : syracuseStep 52762691 = 79144037) B79144037
theorem B3381587 : Blo 1502071 3381587 := bstep (se 1 (by rfl) ⟨2536190, by rfl⟩ : syracuseStep 3381587 = 5072381) B5072381
theorem B13007299 : Blo 1502071 13007299 := bstep (se 1 (by rfl) ⟨9755474, by rfl⟩ : syracuseStep 13007299 = 19510949) B19510949
theorem B1604071 : Blo 1502071 1604071 := bstep (se 1 (by rfl) ⟨1203053, by rfl⟩ : syracuseStep 1604071 = 2406107) B2406107
theorem B9632267 : Blo 1502071 9632267 := bstep (se 1 (by rfl) ⟨7224200, by rfl⟩ : syracuseStep 9632267 = 14448401) B14448401
theorem B3045919 : Blo 1502071 3045919 := bstep (se 1 (by rfl) ⟨2284439, by rfl⟩ : syracuseStep 3045919 = 4568879) B4568879
theorem B8559371 : Blo 1502071 8559371 := bstep (se 1 (by rfl) ⟨6419528, by rfl⟩ : syracuseStep 8559371 = 12839057) B12839057
theorem B3382073 : Blo 1502071 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B7519067 : Blo 1502071 7519067 := bstep (se 1 (by rfl) ⟨5639300, by rfl⟩ : syracuseStep 7519067 = 11278601) B11278601
theorem B3382127 : Blo 1502071 3382127 := bstep (se 1 (by rfl) ⟨2536595, by rfl⟩ : syracuseStep 3382127 = 5073191) B5073191
theorem B4119407 : Blo 1502071 4119407 := bstep (se 1 (by rfl) ⟨3089555, by rfl⟩ : syracuseStep 4119407 = 6179111) B6179111
theorem B13900769 : Blo 1502071 13900769 := bstep (se 2 (by rfl) ⟨5212788, by rfl⟩ : syracuseStep 13900769 = 10425577) B10425577
theorem B20560877 : Blo 1502071 20560877 := bstep (se 3 (by rfl) ⟨3855164, by rfl⟩ : syracuseStep 20560877 = 7710329) B7710329
theorem B2030683 : Blo 1502071 2030683 := bstep (se 1 (by rfl) ⟨1523012, by rfl⟩ : syracuseStep 2030683 = 3046025) B3046025
theorem B2407529 : Blo 1502071 2407529 := bstep (se 2 (by rfl) ⟨902823, by rfl⟩ : syracuseStep 2407529 = 1805647) B1805647
theorem B13704623 : Blo 1502071 13704623 := bstep (se 1 (by rfl) ⟨10278467, by rfl⟩ : syracuseStep 13704623 = 20556935) B20556935
theorem B3382703 : Blo 1502071 3382703 := bstep (se 1 (by rfl) ⟨2537027, by rfl⟩ : syracuseStep 3382703 = 5074055) B5074055
theorem B7142863 : Blo 1502071 7142863 := bstep (se 1 (by rfl) ⟨5357147, by rfl⟩ : syracuseStep 7142863 = 10714295) B10714295
theorem B3661289 : Blo 1502071 3661289 := bstep (se 2 (by rfl) ⟨1372983, by rfl⟩ : syracuseStep 3661289 = 2745967) B2745967
theorem B3382775 : Blo 1502071 3382775 := bstep (se 1 (by rfl) ⟨2537081, by rfl⟩ : syracuseStep 3382775 = 5074163) B5074163
theorem B61669475 : Blo 1502071 61669475 := bstep (se 1 (by rfl) ⟨46252106, by rfl⟩ : syracuseStep 61669475 = 92504213) B92504213
theorem B5784137 : Blo 1502071 5784137 := bstep (se 2 (by rfl) ⟨2169051, by rfl⟩ : syracuseStep 5784137 = 4338103) B4338103
theorem B17343065 : Blo 1502071 17343065 := bstep (se 2 (by rfl) ⟨6503649, by rfl⟩ : syracuseStep 17343065 = 13007299) B13007299
theorem B13009517 : Blo 1502071 13009517 := bstep (se 3 (by rfl) ⟨2439284, by rfl⟩ : syracuseStep 13009517 = 4878569) B4878569
theorem B2138761 : Blo 1502071 2138761 := bstep (se 2 (by rfl) ⟨802035, by rfl⟩ : syracuseStep 2138761 = 1604071) B1604071
theorem B2253545 : Blo 1502071 2253545 := bstep (se 2 (by rfl) ⟨845079, by rfl⟩ : syracuseStep 2253545 = 1690159) B1690159
theorem B7611407 : Blo 1502071 7611407 := bstep (se 1 (by rfl) ⟨5708555, by rfl⟩ : syracuseStep 7611407 = 11417111) B11417111
theorem B2253935 : Blo 1502071 2253935 := bstep (se 1 (by rfl) ⟨1690451, by rfl⟩ : syracuseStep 2253935 = 3380903) B3380903
theorem B1713307 : Blo 1502071 1713307 := bstep (se 1 (by rfl) ⟨1284980, by rfl⟩ : syracuseStep 1713307 = 2569961) B2569961
theorem B2254055 : Blo 1502071 2254055 := bstep (se 1 (by rfl) ⟨1690541, by rfl⟩ : syracuseStep 2254055 = 3381083) B3381083
theorem B1901819 : Blo 1502071 1901819 := bstep (se 1 (by rfl) ⟨1426364, by rfl⟩ : syracuseStep 1901819 = 2852729) B2852729
theorem B2254121 : Blo 1502071 2254121 := bstep (se 2 (by rfl) ⟨845295, by rfl⟩ : syracuseStep 2254121 = 1690591) B1690591
theorem B2254391 : Blo 1502071 2254391 := bstep (se 1 (by rfl) ⟨1690793, by rfl⟩ : syracuseStep 2254391 = 3381587) B3381587
theorem B2254715 : Blo 1502071 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B2254751 : Blo 1502071 2254751 := bstep (se 1 (by rfl) ⟨1691063, by rfl⟩ : syracuseStep 2254751 = 3382127) B3382127
theorem B2746271 : Blo 1502071 2746271 := bstep (se 1 (by rfl) ⟨2059703, by rfl⟩ : syracuseStep 2746271 = 4119407) B4119407
theorem B3803071 : Blo 1502071 3803071 := bstep (se 1 (by rfl) ⟨2852303, by rfl⟩ : syracuseStep 3803071 = 5704607) B5704607
theorem B9267179 : Blo 1502071 9267179 := bstep (se 1 (by rfl) ⟨6950384, by rfl⟩ : syracuseStep 9267179 = 13900769) B13900769
theorem B13707251 : Blo 1502071 13707251 := bstep (se 1 (by rfl) ⟨10280438, by rfl⟩ : syracuseStep 13707251 = 20560877) B20560877
theorem B5703803 : Blo 1502071 5703803 := bstep (se 1 (by rfl) ⟨4277852, by rfl⟩ : syracuseStep 5703803 = 8555705) B8555705
theorem B2254985 : Blo 1502071 2254985 := bstep (se 2 (by rfl) ⟨845619, by rfl⟩ : syracuseStep 2254985 = 1691239) B1691239
theorem B1902847 : Blo 1502071 1902847 := bstep (se 1 (by rfl) ⟨1427135, by rfl⟩ : syracuseStep 1902847 = 2854271) B2854271
theorem B9136415 : Blo 1502071 9136415 := bstep (se 1 (by rfl) ⟨6852311, by rfl⟩ : syracuseStep 9136415 = 13704623) B13704623
theorem B2255135 : Blo 1502071 2255135 := bstep (se 1 (by rfl) ⟨1691351, by rfl⟩ : syracuseStep 2255135 = 3382703) B3382703
theorem B2255183 : Blo 1502071 2255183 := bstep (se 1 (by rfl) ⟨1691387, by rfl⟩ : syracuseStep 2255183 = 3382775) B3382775
theorem B7604603 : Blo 1502071 7604603 := bstep (se 1 (by rfl) ⟨5703452, by rfl⟩ : syracuseStep 7604603 = 11406905) B11406905
theorem B2255273 : Blo 1502071 2255273 := bstep (se 2 (by rfl) ⟨845727, by rfl⟩ : syracuseStep 2255273 = 1691455) B1691455
theorem B140700509 : Blo 1502071 140700509 := bstep (se 3 (by rfl) ⟨26381345, by rfl⟩ : syracuseStep 140700509 = 52762691) B52762691
theorem B6417377 : Blo 1502071 6417377 := bstep (se 2 (by rfl) ⟨2406516, by rfl⟩ : syracuseStep 6417377 = 4813033) B4813033
theorem B3804155 : Blo 1502071 3804155 := bstep (se 1 (by rfl) ⟨2853116, by rfl⟩ : syracuseStep 3804155 = 5706233) B5706233
theorem B1502319 : Blo 1502071 1502319 := bstep (se 1 (by rfl) ⟨1126739, by rfl⟩ : syracuseStep 1502319 = 2253479) B2253479
theorem B1502399 : Blo 1502071 1502399 := bstep (se 1 (by rfl) ⟨1126799, by rfl⟩ : syracuseStep 1502399 = 2253599) B2253599
theorem B32500939 : Blo 1502071 32500939 := bstep (se 1 (by rfl) ⟨24375704, by rfl⟩ : syracuseStep 32500939 = 48751409) B48751409
theorem B1502415 : Blo 1502071 1502415 := bstep (se 1 (by rfl) ⟨1126811, by rfl⟩ : syracuseStep 1502415 = 2253623) B2253623
theorem B1502535 : Blo 1502071 1502535 := bstep (se 1 (by rfl) ⟨1126901, by rfl⟩ : syracuseStep 1502535 = 2253803) B2253803
theorem B17116919 : Blo 1502071 17116919 := bstep (se 1 (by rfl) ⟨12837689, by rfl⟩ : syracuseStep 17116919 = 25675379) B25675379
theorem B48738185 : Blo 1502071 48738185 := bstep (se 2 (by rfl) ⟨18276819, by rfl⟩ : syracuseStep 48738185 = 36553639) B36553639
theorem B32509937 : Blo 1502071 32509937 := bstep (se 2 (by rfl) ⟨12191226, by rfl⟩ : syracuseStep 32509937 = 24382453) B24382453
theorem B3805177 : Blo 1502071 3805177 := bstep (se 2 (by rfl) ⟨1426941, by rfl⟩ : syracuseStep 3805177 = 2853883) B2853883
theorem B1503263 : Blo 1502071 1503263 := bstep (se 1 (by rfl) ⟨1127447, by rfl⟩ : syracuseStep 1503263 = 2254895) B2254895
theorem B2707577 : Blo 1502071 2707577 := bstep (se 2 (by rfl) ⟨1015341, by rfl⟩ : syracuseStep 2707577 = 2030683) B2030683
theorem B7221433 : Blo 1502071 7221433 := bstep (se 2 (by rfl) ⟨2708037, by rfl⟩ : syracuseStep 7221433 = 5416075) B5416075
theorem B1503439 : Blo 1502071 1503439 := bstep (se 1 (by rfl) ⟨1127579, by rfl⟩ : syracuseStep 1503439 = 2255159) B2255159
theorem B1503559 : Blo 1502071 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B5706065 : Blo 1502071 5706065 := bstep (se 2 (by rfl) ⟨2139774, by rfl⟩ : syracuseStep 5706065 = 4279549) B4279549
theorem B37564883 : Blo 1502071 37564883 := bstep (se 1 (by rfl) ⟨28173662, by rfl⟩ : syracuseStep 37564883 = 56347325) B56347325
theorem B5706247 : Blo 1502071 5706247 := bstep (se 1 (by rfl) ⟨4279685, by rfl⟩ : syracuseStep 5706247 = 8559371) B8559371
theorem B9523817 : Blo 1502071 9523817 := bstep (se 2 (by rfl) ⟨3571431, by rfl⟩ : syracuseStep 9523817 = 7142863) B7142863
theorem B3805825 : Blo 1502071 3805825 := bstep (se 2 (by rfl) ⟨1427184, by rfl⟩ : syracuseStep 3805825 = 2854369) B2854369
theorem B2536231 : Blo 1502071 2536231 := bstep (se 1 (by rfl) ⟨1902173, by rfl⟩ : syracuseStep 2536231 = 3804347) B3804347
theorem B2536427 : Blo 1502071 2536427 := bstep (se 1 (by rfl) ⟨1902320, by rfl⟩ : syracuseStep 2536427 = 3804641) B3804641
theorem B7222355 : Blo 1502071 7222355 := bstep (se 1 (by rfl) ⟨5416766, by rfl⟩ : syracuseStep 7222355 = 10833533) B10833533
theorem B5707037 : Blo 1502071 5707037 := bstep (se 3 (by rfl) ⟨1070069, by rfl⟩ : syracuseStep 5707037 = 2140139) B2140139
theorem B5707219 : Blo 1502071 5707219 := bstep (se 1 (by rfl) ⟨4280414, by rfl⟩ : syracuseStep 5707219 = 8560829) B8560829
theorem B4339175 : Blo 1502071 4339175 := bstep (se 1 (by rfl) ⟨3254381, by rfl⟩ : syracuseStep 4339175 = 6508763) B6508763
theorem B2536987 : Blo 1502071 2536987 := bstep (se 1 (by rfl) ⟨1902740, by rfl⟩ : syracuseStep 2536987 = 3805481) B3805481
theorem B11409335 : Blo 1502071 11409335 := bstep (se 1 (by rfl) ⟨8557001, by rfl⟩ : syracuseStep 11409335 = 17114003) B17114003
theorem B4061225 : Blo 1502071 4061225 := bstep (se 2 (by rfl) ⟨1522959, by rfl⟩ : syracuseStep 4061225 = 3045919) B3045919
theorem B3045595 : Blo 1502071 3045595 := bstep (se 1 (by rfl) ⟨2284196, by rfl⟩ : syracuseStep 3045595 = 4568393) B4568393
theorem B28883573 : Blo 1502071 28883573 := bstep (se 5 (by rfl) ⟨1353917, by rfl⟩ : syracuseStep 28883573 = 2707835) B2707835
theorem B13712285 : Blo 1502071 13712285 := bstep (se 3 (by rfl) ⟨2571053, by rfl⟩ : syracuseStep 13712285 = 5142107) B5142107
theorem B19782589 : Blo 1502071 19782589 := bstep (se 3 (by rfl) ⟨3709235, by rfl⟩ : syracuseStep 19782589 = 7418471) B7418471
theorem B8559553 : Blo 1502071 8559553 := bstep (se 2 (by rfl) ⟨3209832, by rfl⟩ : syracuseStep 8559553 = 6419665) B6419665
theorem B6421511 : Blo 1502071 6421511 := bstep (se 1 (by rfl) ⟨4816133, by rfl⟩ : syracuseStep 6421511 = 9632267) B9632267
theorem B19512409 : Blo 1502071 19512409 := bstep (se 2 (by rfl) ⟨7317153, by rfl⟩ : syracuseStep 19512409 = 14634307) B14634307
theorem B5012711 : Blo 1502071 5012711 := bstep (se 1 (by rfl) ⟨3759533, by rfl⟩ : syracuseStep 5012711 = 7519067) B7519067
theorem B1605019 : Blo 1502071 1605019 := bstep (se 1 (by rfl) ⟨1203764, by rfl⟩ : syracuseStep 1605019 = 2407529) B2407529
theorem B8560079 : Blo 1502071 8560079 := bstep (se 1 (by rfl) ⟨6420059, by rfl⟩ : syracuseStep 8560079 = 12840119) B12840119
theorem B3907201 : Blo 1502071 3907201 := bstep (se 2 (by rfl) ⟨1465200, by rfl⟩ : syracuseStep 3907201 = 2930401) B2930401
theorem B2440859 : Blo 1502071 2440859 := bstep (se 1 (by rfl) ⟨1830644, by rfl⟩ : syracuseStep 2440859 = 3661289) B3661289
theorem B10829933 : Blo 1502071 10829933 := bstep (se 3 (by rfl) ⟨2030612, by rfl⟩ : syracuseStep 10829933 = 4061225) B4061225
theorem B25043255 : Blo 1502071 25043255 := bstep (se 1 (by rfl) ⟨18782441, by rfl⟩ : syracuseStep 25043255 = 37564883) B37564883
theorem B6349211 : Blo 1502071 6349211 := bstep (se 1 (by rfl) ⟨4761908, by rfl⟩ : syracuseStep 6349211 = 9523817) B9523817
theorem B5071517 : Blo 1502071 5071517 := bstep (se 3 (by rfl) ⟨950909, by rfl⟩ : syracuseStep 5071517 = 1901819) B1901819
theorem B24363773 : Blo 1502071 24363773 := bstep (se 3 (by rfl) ⟨4568207, by rfl⟩ : syracuseStep 24363773 = 9136415) B9136415
theorem B2851681 : Blo 1502071 2851681 := bstep (se 2 (by rfl) ⟨1069380, by rfl⟩ : syracuseStep 2851681 = 2138761) B2138761
theorem B11412737 : Blo 1502071 11412737 := bstep (se 2 (by rfl) ⟨4279776, by rfl⟩ : syracuseStep 11412737 = 8559553) B8559553
theorem B3802535 : Blo 1502071 3802535 := bstep (se 1 (by rfl) ⟨2851901, by rfl⟩ : syracuseStep 3802535 = 5703803) B5703803
theorem B2140025 : Blo 1502071 2140025 := bstep (se 2 (by rfl) ⟨802509, by rfl⟩ : syracuseStep 2140025 = 1605019) B1605019
theorem B93800339 : Blo 1502071 93800339 := bstep (se 1 (by rfl) ⟨70350254, by rfl⟩ : syracuseStep 93800339 = 140700509) B140700509
theorem B4278251 : Blo 1502071 4278251 := bstep (se 1 (by rfl) ⟨3208688, by rfl⟩ : syracuseStep 4278251 = 6417377) B6417377
theorem B32492123 : Blo 1502071 32492123 := bstep (se 1 (by rfl) ⟨24369092, by rfl⟩ : syracuseStep 32492123 = 48738185) B48738185
theorem B5073569 : Blo 1502071 5073569 := bstep (se 2 (by rfl) ⟨1902588, by rfl⟩ : syracuseStep 5073569 = 3805177) B3805177
theorem B1805051 : Blo 1502071 1805051 := bstep (se 1 (by rfl) ⟨1353788, by rfl⟩ : syracuseStep 1805051 = 2707577) B2707577
theorem B3804043 : Blo 1502071 3804043 := bstep (se 1 (by rfl) ⟨2853032, by rfl⟩ : syracuseStep 3804043 = 5706065) B5706065
theorem B9628577 : Blo 1502071 9628577 := bstep (se 2 (by rfl) ⟨3610716, by rfl⟩ : syracuseStep 9628577 = 7221433) B7221433
theorem B11562043 : Blo 1502071 11562043 := bstep (se 1 (by rfl) ⟨8671532, by rfl⟩ : syracuseStep 11562043 = 17343065) B17343065
theorem B1502363 : Blo 1502071 1502363 := bstep (se 1 (by rfl) ⟨1126772, by rfl⟩ : syracuseStep 1502363 = 2253545) B2253545
theorem B1690951 : Blo 1502071 1690951 := bstep (se 1 (by rfl) ⟨1268213, by rfl⟩ : syracuseStep 1690951 = 2536427) B2536427
theorem B5074271 : Blo 1502071 5074271 := bstep (se 1 (by rfl) ⟨3805703, by rfl⟩ : syracuseStep 5074271 = 7611407) B7611407
theorem B1502623 : Blo 1502071 1502623 := bstep (se 1 (by rfl) ⟨1126967, by rfl⟩ : syracuseStep 1502623 = 2253935) B2253935
theorem B1502703 : Blo 1502071 1502703 := bstep (se 1 (by rfl) ⟨1127027, by rfl⟩ : syracuseStep 1502703 = 2254055) B2254055
theorem B5074433 : Blo 1502071 5074433 := bstep (se 2 (by rfl) ⟨1902912, by rfl⟩ : syracuseStep 5074433 = 3805825) B3805825
theorem B3804691 : Blo 1502071 3804691 := bstep (se 1 (by rfl) ⟨2853518, by rfl⟩ : syracuseStep 3804691 = 5707037) B5707037
theorem B1502747 : Blo 1502071 1502747 := bstep (se 1 (by rfl) ⟨1127060, by rfl⟩ : syracuseStep 1502747 = 2254121) B2254121
theorem B1502927 : Blo 1502071 1502927 := bstep (se 1 (by rfl) ⟨1127195, by rfl⟩ : syracuseStep 1502927 = 2254391) B2254391
theorem B1503143 : Blo 1502071 1503143 := bstep (se 1 (by rfl) ⟨1127357, by rfl⟩ : syracuseStep 1503143 = 2254715) B2254715
theorem B11571133 : Blo 1502071 11571133 := bstep (se 3 (by rfl) ⟨2169587, by rfl⟩ : syracuseStep 11571133 = 4339175) B4339175
theorem B1503167 : Blo 1502071 1503167 := bstep (se 1 (by rfl) ⟨1127375, by rfl⟩ : syracuseStep 1503167 = 2254751) B2254751
theorem B1830847 : Blo 1502071 1830847 := bstep (se 1 (by rfl) ⟨1373135, by rfl⟩ : syracuseStep 1830847 = 2746271) B2746271
theorem B7606223 : Blo 1502071 7606223 := bstep (se 1 (by rfl) ⟨5704667, by rfl⟩ : syracuseStep 7606223 = 11409335) B11409335
theorem B9138167 : Blo 1502071 9138167 := bstep (se 1 (by rfl) ⟨6853625, by rfl⟩ : syracuseStep 9138167 = 13707251) B13707251
theorem B1503323 : Blo 1502071 1503323 := bstep (se 1 (by rfl) ⟨1127492, by rfl⟩ : syracuseStep 1503323 = 2254985) B2254985
theorem B1503423 : Blo 1502071 1503423 := bstep (se 1 (by rfl) ⟨1127567, by rfl⟩ : syracuseStep 1503423 = 2255135) B2255135
theorem B1503455 : Blo 1502071 1503455 := bstep (se 1 (by rfl) ⟨1127591, by rfl⟩ : syracuseStep 1503455 = 2255183) B2255183
theorem B1503515 : Blo 1502071 1503515 := bstep (se 1 (by rfl) ⟨1127636, by rfl⟩ : syracuseStep 1503515 = 2255273) B2255273
theorem B6508957 : Blo 1502071 6508957 := bstep (se 3 (by rfl) ⟨1220429, by rfl⟩ : syracuseStep 6508957 = 2440859) B2440859
theorem B19255715 : Blo 1502071 19255715 := bstep (se 1 (by rfl) ⟨14441786, by rfl⟩ : syracuseStep 19255715 = 28883573) B28883573
theorem B2536103 : Blo 1502071 2536103 := bstep (se 1 (by rfl) ⟨1902077, by rfl⟩ : syracuseStep 2536103 = 3804155) B3804155
theorem B4281007 : Blo 1502071 4281007 := bstep (se 1 (by rfl) ⟨3210755, by rfl⟩ : syracuseStep 4281007 = 6421511) B6421511
theorem B5706719 : Blo 1502071 5706719 := bstep (se 1 (by rfl) ⟨4280039, by rfl⟩ : syracuseStep 5706719 = 8560079) B8560079
theorem B36566093 : Blo 1502071 36566093 := bstep (se 3 (by rfl) ⟨6856142, by rfl⟩ : syracuseStep 36566093 = 13712285) B13712285
theorem B98849909 : Blo 1502071 98849909 := bstep (se 5 (by rfl) ⟨4633589, by rfl⟩ : syracuseStep 98849909 = 9267179) B9267179
theorem B21673291 : Blo 1502071 21673291 := bstep (se 1 (by rfl) ⟨16254968, by rfl⟩ : syracuseStep 21673291 = 32509937) B32509937
theorem B41112983 : Blo 1502071 41112983 := bstep (se 1 (by rfl) ⟨30834737, by rfl⟩ : syracuseStep 41112983 = 61669475) B61669475
theorem B4060793 : Blo 1502071 4060793 := bstep (se 2 (by rfl) ⟨1522797, by rfl⟩ : syracuseStep 4060793 = 3045595) B3045595
theorem B2537129 : Blo 1502071 2537129 := bstep (se 2 (by rfl) ⟨951423, by rfl⟩ : syracuseStep 2537129 = 1902847) B1902847
theorem B3856091 : Blo 1502071 3856091 := bstep (se 1 (by rfl) ⟨2892068, by rfl⟩ : syracuseStep 3856091 = 5784137) B5784137
theorem B8673011 : Blo 1502071 8673011 := bstep (se 1 (by rfl) ⟨6504758, by rfl⟩ : syracuseStep 8673011 = 13009517) B13009517
theorem B7608329 : Blo 1502071 7608329 := bstep (se 2 (by rfl) ⟨2853123, by rfl⟩ : syracuseStep 7608329 = 5706247) B5706247
theorem B4814903 : Blo 1502071 4814903 := bstep (se 1 (by rfl) ⟨3611177, by rfl⟩ : syracuseStep 4814903 = 7222355) B7222355
theorem B3381641 : Blo 1502071 3381641 := bstep (se 2 (by rfl) ⟨1268115, by rfl⟩ : syracuseStep 3381641 = 2536231) B2536231
theorem B26376785 : Blo 1502071 26376785 := bstep (se 2 (by rfl) ⟨9891294, by rfl⟩ : syracuseStep 26376785 = 19782589) B19782589
theorem B26016545 : Blo 1502071 26016545 := bstep (se 2 (by rfl) ⟨9756204, by rfl⟩ : syracuseStep 26016545 = 19512409) B19512409
theorem B2284409 : Blo 1502071 2284409 := bstep (se 2 (by rfl) ⟨856653, by rfl⟩ : syracuseStep 2284409 = 1713307) B1713307
theorem B5069735 : Blo 1502071 5069735 := bstep (se 1 (by rfl) ⟨3802301, by rfl⟩ : syracuseStep 5069735 = 7604603) B7604603
theorem B43334585 : Blo 1502071 43334585 := bstep (se 2 (by rfl) ⟨16250469, by rfl⟩ : syracuseStep 43334585 = 32500939) B32500939
theorem B7609625 : Blo 1502071 7609625 := bstep (se 2 (by rfl) ⟨2853609, by rfl⟩ : syracuseStep 7609625 = 5707219) B5707219
theorem B3382649 : Blo 1502071 3382649 := bstep (se 2 (by rfl) ⟨1268493, by rfl⟩ : syracuseStep 3382649 = 2536987) B2536987
theorem B3341807 : Blo 1502071 3341807 := bstep (se 1 (by rfl) ⟨2506355, by rfl⟩ : syracuseStep 3341807 = 5012711) B5012711
theorem B5209601 : Blo 1502071 5209601 := bstep (se 2 (by rfl) ⟨1953600, by rfl⟩ : syracuseStep 5209601 = 3907201) B3907201
theorem B11411279 : Blo 1502071 11411279 := bstep (se 1 (by rfl) ⟨8558459, by rfl⟩ : syracuseStep 11411279 = 17116919) B17116919
theorem B5070761 : Blo 1502071 5070761 := bstep (se 2 (by rfl) ⟨1901535, by rfl⟩ : syracuseStep 5070761 = 3803071) B3803071
theorem B97509581 : Blo 1502071 97509581 := bstep (se 3 (by rfl) ⟨18283046, by rfl⟩ : syracuseStep 97509581 = 36566093) B36566093
theorem B16695503 : Blo 1502071 16695503 := bstep (se 1 (by rfl) ⟨12521627, by rfl⟩ : syracuseStep 16695503 = 25043255) B25043255
theorem B12837143 : Blo 1502071 12837143 := bstep (se 1 (by rfl) ⟨9627857, by rfl⟩ : syracuseStep 12837143 = 19255715) B19255715
theorem B3802241 : Blo 1502071 3802241 := bstep (se 2 (by rfl) ⟨1425840, by rfl⟩ : syracuseStep 3802241 = 2851681) B2851681
theorem B5072057 : Blo 1502071 5072057 := bstep (se 2 (by rfl) ⟨1902021, by rfl⟩ : syracuseStep 5072057 = 3804043) B3804043
theorem B2852167 : Blo 1502071 2852167 := bstep (se 1 (by rfl) ⟨2139125, by rfl⟩ : syracuseStep 2852167 = 4278251) B4278251
theorem B5072219 : Blo 1502071 5072219 := bstep (se 1 (by rfl) ⟨3804164, by rfl⟩ : syracuseStep 5072219 = 7608329) B7608329
theorem B2254427 : Blo 1502071 2254427 := bstep (se 1 (by rfl) ⟨1690820, by rfl⟩ : syracuseStep 2254427 = 3381641) B3381641
theorem B21661415 : Blo 1502071 21661415 := bstep (se 1 (by rfl) ⟨16246061, by rfl⟩ : syracuseStep 21661415 = 32492123) B32492123
theorem B2254601 : Blo 1502071 2254601 := bstep (se 2 (by rfl) ⟨845475, by rfl⟩ : syracuseStep 2254601 = 1690951) B1690951
theorem B17344363 : Blo 1502071 17344363 := bstep (se 1 (by rfl) ⟨13008272, by rfl⟩ : syracuseStep 17344363 = 26016545) B26016545
theorem B10282909 : Blo 1502071 10282909 := bstep (se 3 (by rfl) ⟨1928045, by rfl⟩ : syracuseStep 10282909 = 3856091) B3856091
theorem B5072921 : Blo 1502071 5072921 := bstep (se 2 (by rfl) ⟨1902345, by rfl⟩ : syracuseStep 5072921 = 3804691) B3804691
theorem B5073083 : Blo 1502071 5073083 := bstep (se 1 (by rfl) ⟨3804812, by rfl⟩ : syracuseStep 5073083 = 7609625) B7609625
theorem B2255099 : Blo 1502071 2255099 := bstep (se 1 (by rfl) ⟨1691324, by rfl⟩ : syracuseStep 2255099 = 3382649) B3382649
theorem B15428177 : Blo 1502071 15428177 := bstep (se 2 (by rfl) ⟨5785566, by rfl⟩ : syracuseStep 15428177 = 11571133) B11571133
theorem B7219955 : Blo 1502071 7219955 := bstep (se 1 (by rfl) ⟨5414966, by rfl⟩ : syracuseStep 7219955 = 10829933) B10829933
theorem B12839741 : Blo 1502071 12839741 := bstep (se 3 (by rfl) ⟨2407451, by rfl⟩ : syracuseStep 12839741 = 4814903) B4814903
theorem B1690735 : Blo 1502071 1690735 := bstep (se 1 (by rfl) ⟨1268051, by rfl⟩ : syracuseStep 1690735 = 2536103) B2536103
theorem B8678609 : Blo 1502071 8678609 := bstep (se 2 (by rfl) ⟨3254478, by rfl⟩ : syracuseStep 8678609 = 6508957) B6508957
theorem B3804479 : Blo 1502071 3804479 := bstep (se 1 (by rfl) ⟨2853359, by rfl⟩ : syracuseStep 3804479 = 5706719) B5706719
theorem B2535023 : Blo 1502071 2535023 := bstep (se 1 (by rfl) ⟨1901267, by rfl⟩ : syracuseStep 2535023 = 3802535) B3802535
theorem B2707195 : Blo 1502071 2707195 := bstep (se 1 (by rfl) ⟨2030396, by rfl⟩ : syracuseStep 2707195 = 4060793) B4060793
theorem B1691419 : Blo 1502071 1691419 := bstep (se 1 (by rfl) ⟨1268564, by rfl⟩ : syracuseStep 1691419 = 2537129) B2537129
theorem B62533559 : Blo 1502071 62533559 := bstep (se 1 (by rfl) ⟨46900169, by rfl⟩ : syracuseStep 62533559 = 93800339) B93800339
theorem B17584523 : Blo 1502071 17584523 := bstep (se 1 (by rfl) ⟨13188392, by rfl⟩ : syracuseStep 17584523 = 26376785) B26376785
theorem B28897721 : Blo 1502071 28897721 := bstep (se 2 (by rfl) ⟨10836645, by rfl⟩ : syracuseStep 28897721 = 21673291) B21673291
theorem B6419051 : Blo 1502071 6419051 := bstep (se 1 (by rfl) ⟨4814288, by rfl⟩ : syracuseStep 6419051 = 9628577) B9628577
theorem B3379823 : Blo 1502071 3379823 := bstep (se 1 (by rfl) ⟨2534867, by rfl⟩ : syracuseStep 3379823 = 5069735) B5069735
theorem B28889723 : Blo 1502071 28889723 := bstep (se 1 (by rfl) ⟨21667292, by rfl⟩ : syracuseStep 28889723 = 43334585) B43334585
theorem B4813469 : Blo 1502071 4813469 := bstep (se 3 (by rfl) ⟨902525, by rfl⟩ : syracuseStep 4813469 = 1805051) B1805051
theorem B6091757 : Blo 1502071 6091757 := bstep (se 3 (by rfl) ⟨1142204, by rfl⟩ : syracuseStep 6091757 = 2284409) B2284409
theorem B5706733 : Blo 1502071 5706733 := bstep (se 3 (by rfl) ⟨1070012, by rfl⟩ : syracuseStep 5706733 = 2140025) B2140025
theorem B7607519 : Blo 1502071 7607519 := bstep (se 1 (by rfl) ⟨5705639, by rfl⟩ : syracuseStep 7607519 = 11411279) B11411279
theorem B3380507 : Blo 1502071 3380507 := bstep (se 1 (by rfl) ⟨2535380, by rfl⟩ : syracuseStep 3380507 = 5070761) B5070761
theorem B6092111 : Blo 1502071 6092111 := bstep (se 1 (by rfl) ⟨4569083, by rfl⟩ : syracuseStep 6092111 = 9138167) B9138167
theorem B4232807 : Blo 1502071 4232807 := bstep (se 1 (by rfl) ⟨3174605, by rfl⟩ : syracuseStep 4232807 = 6349211) B6349211
theorem B263599757 : Blo 1502071 263599757 := bstep (se 3 (by rfl) ⟨49424954, by rfl⟩ : syracuseStep 263599757 = 98849909) B98849909
theorem B3381011 : Blo 1502071 3381011 := bstep (se 1 (by rfl) ⟨2535758, by rfl⟩ : syracuseStep 3381011 = 5071517) B5071517
theorem B16242515 : Blo 1502071 16242515 := bstep (se 1 (by rfl) ⟨12181886, by rfl⟩ : syracuseStep 16242515 = 24363773) B24363773
theorem B7608491 : Blo 1502071 7608491 := bstep (se 1 (by rfl) ⟨5706368, by rfl⟩ : syracuseStep 7608491 = 11412737) B11412737
theorem B5708009 : Blo 1502071 5708009 := bstep (se 2 (by rfl) ⟨2140503, by rfl⟩ : syracuseStep 5708009 = 4281007) B4281007
theorem B27408655 : Blo 1502071 27408655 := bstep (se 1 (by rfl) ⟨20556491, by rfl⟩ : syracuseStep 27408655 = 41112983) B41112983
theorem B5782007 : Blo 1502071 5782007 := bstep (se 1 (by rfl) ⟨4336505, by rfl⟩ : syracuseStep 5782007 = 8673011) B8673011
theorem B13892269 : Blo 1502071 13892269 := bstep (se 3 (by rfl) ⟨2604800, by rfl⟩ : syracuseStep 13892269 = 5209601) B5209601
theorem B15416057 : Blo 1502071 15416057 := bstep (se 2 (by rfl) ⟨5781021, by rfl⟩ : syracuseStep 15416057 = 11562043) B11562043
theorem B3382379 : Blo 1502071 3382379 := bstep (se 1 (by rfl) ⟨2536784, by rfl⟩ : syracuseStep 3382379 = 5073569) B5073569
theorem B3382847 : Blo 1502071 3382847 := bstep (se 1 (by rfl) ⟨2537135, by rfl⟩ : syracuseStep 3382847 = 5074271) B5074271
theorem B2227871 : Blo 1502071 2227871 := bstep (se 1 (by rfl) ⟨1670903, by rfl⟩ : syracuseStep 2227871 = 3341807) B3341807
theorem B3382955 : Blo 1502071 3382955 := bstep (se 1 (by rfl) ⟨2537216, by rfl⟩ : syracuseStep 3382955 = 5074433) B5074433
theorem B2441129 : Blo 1502071 2441129 := bstep (se 2 (by rfl) ⟨915423, by rfl⟩ : syracuseStep 2441129 = 1830847) B1830847
theorem B5070815 : Blo 1502071 5070815 := bstep (se 1 (by rfl) ⟨3803111, by rfl⟩ : syracuseStep 5070815 = 7606223) B7606223
theorem B11723015 : Blo 1502071 11723015 := bstep (se 1 (by rfl) ⟨8792261, by rfl⟩ : syracuseStep 11723015 = 17584523) B17584523
theorem B36544873 : Blo 1502071 36544873 := bstep (se 2 (by rfl) ⟨13704327, by rfl⟩ : syracuseStep 36544873 = 27408655) B27408655
theorem B2253215 : Blo 1502071 2253215 := bstep (se 1 (by rfl) ⟨1689911, by rfl⟩ : syracuseStep 2253215 = 3379823) B3379823
theorem B19259815 : Blo 1502071 19259815 := bstep (se 1 (by rfl) ⟨14444861, by rfl⟩ : syracuseStep 19259815 = 28889723) B28889723
theorem B5071679 : Blo 1502071 5071679 := bstep (se 1 (by rfl) ⟨3803759, by rfl⟩ : syracuseStep 5071679 = 7607519) B7607519
theorem B2253671 : Blo 1502071 2253671 := bstep (se 1 (by rfl) ⟨1690253, by rfl⟩ : syracuseStep 2253671 = 3380507) B3380507
theorem B16245629 : Blo 1502071 16245629 := bstep (se 3 (by rfl) ⟨3046055, by rfl⟩ : syracuseStep 16245629 = 6092111) B6092111
theorem B18523025 : Blo 1502071 18523025 := bstep (se 2 (by rfl) ⟨6946134, by rfl⟩ : syracuseStep 18523025 = 13892269) B13892269
theorem B2254007 : Blo 1502071 2254007 := bstep (se 1 (by rfl) ⟨1690505, by rfl⟩ : syracuseStep 2254007 = 3381011) B3381011
theorem B5072327 : Blo 1502071 5072327 := bstep (se 1 (by rfl) ⟨3804245, by rfl⟩ : syracuseStep 5072327 = 7608491) B7608491
theorem B2254313 : Blo 1502071 2254313 := bstep (se 2 (by rfl) ⟨845367, by rfl⟩ : syracuseStep 2254313 = 1690735) B1690735
theorem B5940989 : Blo 1502071 5940989 := bstep (se 3 (by rfl) ⟨1113935, by rfl⟩ : syracuseStep 5940989 = 2227871) B2227871
theorem B3802889 : Blo 1502071 3802889 := bstep (se 2 (by rfl) ⟨1426083, by rfl⟩ : syracuseStep 3802889 = 2852167) B2852167
theorem B2254919 : Blo 1502071 2254919 := bstep (se 1 (by rfl) ⟨1691189, by rfl⟩ : syracuseStep 2254919 = 3382379) B3382379
theorem B5785739 : Blo 1502071 5785739 := bstep (se 1 (by rfl) ⟨4339304, by rfl⟩ : syracuseStep 5785739 = 8678609) B8678609
theorem B2255225 : Blo 1502071 2255225 := bstep (se 2 (by rfl) ⟨845709, by rfl⟩ : syracuseStep 2255225 = 1691419) B1691419
theorem B2255231 : Blo 1502071 2255231 := bstep (se 1 (by rfl) ⟨1691423, by rfl⟩ : syracuseStep 2255231 = 3382847) B3382847
theorem B1690015 : Blo 1502071 1690015 := bstep (se 1 (by rfl) ⟨1267511, by rfl⟩ : syracuseStep 1690015 = 2535023) B2535023
theorem B2255303 : Blo 1502071 2255303 := bstep (se 1 (by rfl) ⟨1691477, by rfl⟩ : syracuseStep 2255303 = 3382955) B3382955
theorem B65006387 : Blo 1502071 65006387 := bstep (se 1 (by rfl) ⟨48754790, by rfl⟩ : syracuseStep 65006387 = 97509581) B97509581
theorem B4279367 : Blo 1502071 4279367 := bstep (se 1 (by rfl) ⟨3209525, by rfl⟩ : syracuseStep 4279367 = 6419051) B6419051
theorem B2534827 : Blo 1502071 2534827 := bstep (se 1 (by rfl) ⟨1901120, by rfl⟩ : syracuseStep 2534827 = 3802241) B3802241
theorem B1502951 : Blo 1502071 1502951 := bstep (se 1 (by rfl) ⟨1127213, by rfl⟩ : syracuseStep 1502951 = 2254427) B2254427
theorem B2821871 : Blo 1502071 2821871 := bstep (se 1 (by rfl) ⟨2116403, by rfl⟩ : syracuseStep 2821871 = 4232807) B4232807
theorem B1503067 : Blo 1502071 1503067 := bstep (se 1 (by rfl) ⟨1127300, by rfl⟩ : syracuseStep 1503067 = 2254601) B2254601
theorem B3805339 : Blo 1502071 3805339 := bstep (se 1 (by rfl) ⟨2854004, by rfl⟩ : syracuseStep 3805339 = 5708009) B5708009
theorem B1503399 : Blo 1502071 1503399 := bstep (se 1 (by rfl) ⟨1127549, by rfl⟩ : syracuseStep 1503399 = 2255099) B2255099
theorem B3854671 : Blo 1502071 3854671 := bstep (se 1 (by rfl) ⟨2891003, by rfl⟩ : syracuseStep 3854671 = 5782007) B5782007
theorem B10285451 : Blo 1502071 10285451 := bstep (se 1 (by rfl) ⟨7714088, by rfl⟩ : syracuseStep 10285451 = 15428177) B15428177
theorem B4813303 : Blo 1502071 4813303 := bstep (se 1 (by rfl) ⟨3609977, by rfl⟩ : syracuseStep 4813303 = 7219955) B7219955
theorem B10277371 : Blo 1502071 10277371 := bstep (se 1 (by rfl) ⟨7708028, by rfl⟩ : syracuseStep 10277371 = 15416057) B15416057
theorem B2536319 : Blo 1502071 2536319 := bstep (se 1 (by rfl) ⟨1902239, by rfl⟩ : syracuseStep 2536319 = 3804479) B3804479
theorem B3609593 : Blo 1502071 3609593 := bstep (se 2 (by rfl) ⟨1353597, by rfl⟩ : syracuseStep 3609593 = 2707195) B2707195
theorem B6509677 : Blo 1502071 6509677 := bstep (se 3 (by rfl) ⟨1220564, by rfl⟩ : syracuseStep 6509677 = 2441129) B2441129
theorem B13710545 : Blo 1502071 13710545 := bstep (se 2 (by rfl) ⟨5141454, by rfl⟩ : syracuseStep 13710545 = 10282909) B10282909
theorem B3380543 : Blo 1502071 3380543 := bstep (se 1 (by rfl) ⟨2535407, by rfl⟩ : syracuseStep 3380543 = 5070815) B5070815
theorem B11130335 : Blo 1502071 11130335 := bstep (se 1 (by rfl) ⟨8347751, by rfl⟩ : syracuseStep 11130335 = 16695503) B16695503
theorem B8558095 : Blo 1502071 8558095 := bstep (se 1 (by rfl) ⟨6418571, by rfl⟩ : syracuseStep 8558095 = 12837143) B12837143
theorem B19265147 : Blo 1502071 19265147 := bstep (se 1 (by rfl) ⟨14448860, by rfl⟩ : syracuseStep 19265147 = 28897721) B28897721
theorem B3208979 : Blo 1502071 3208979 := bstep (se 1 (by rfl) ⟨2406734, by rfl⟩ : syracuseStep 3208979 = 4813469) B4813469
theorem B4061171 : Blo 1502071 4061171 := bstep (se 1 (by rfl) ⟨3045878, by rfl⟩ : syracuseStep 4061171 = 6091757) B6091757
theorem B3381371 : Blo 1502071 3381371 := bstep (se 1 (by rfl) ⟨2536028, by rfl⟩ : syracuseStep 3381371 = 5072057) B5072057
theorem B3381479 : Blo 1502071 3381479 := bstep (se 1 (by rfl) ⟨2536109, by rfl⟩ : syracuseStep 3381479 = 5072219) B5072219
theorem B175733171 : Blo 1502071 175733171 := bstep (se 1 (by rfl) ⟨131799878, by rfl⟩ : syracuseStep 175733171 = 263599757) B263599757
theorem B14440943 : Blo 1502071 14440943 := bstep (se 1 (by rfl) ⟨10830707, by rfl⟩ : syracuseStep 14440943 = 21661415) B21661415
theorem B10828343 : Blo 1502071 10828343 := bstep (se 1 (by rfl) ⟨8121257, by rfl⟩ : syracuseStep 10828343 = 16242515) B16242515
theorem B7608977 : Blo 1502071 7608977 := bstep (se 2 (by rfl) ⟨2853366, by rfl⟩ : syracuseStep 7608977 = 5706733) B5706733
theorem B3381947 : Blo 1502071 3381947 := bstep (se 1 (by rfl) ⟨2536460, by rfl⟩ : syracuseStep 3381947 = 5072921) B5072921
theorem B3382055 : Blo 1502071 3382055 := bstep (se 1 (by rfl) ⟨2536541, by rfl⟩ : syracuseStep 3382055 = 5073083) B5073083
theorem B8559827 : Blo 1502071 8559827 := bstep (se 1 (by rfl) ⟨6419870, by rfl⟩ : syracuseStep 8559827 = 12839741) B12839741
theorem B23125817 : Blo 1502071 23125817 := bstep (se 2 (by rfl) ⟨8672181, by rfl⟩ : syracuseStep 23125817 = 17344363) B17344363
theorem B41689039 : Blo 1502071 41689039 := bstep (se 1 (by rfl) ⟨31266779, by rfl⟩ : syracuseStep 41689039 = 62533559) B62533559
theorem B6856967 : Blo 1502071 6856967 := bstep (se 1 (by rfl) ⟨5142725, by rfl⟩ : syracuseStep 6856967 = 10285451) B10285451
theorem B48726497 : Blo 1502071 48726497 := bstep (se 2 (by rfl) ⟨18272436, by rfl⟩ : syracuseStep 48726497 = 36544873) B36544873
theorem B2253353 : Blo 1502071 2253353 := bstep (se 2 (by rfl) ⟨845007, by rfl⟩ : syracuseStep 2253353 = 1690015) B1690015
theorem B10830419 : Blo 1502071 10830419 := bstep (se 1 (by rfl) ⟨8122814, by rfl⟩ : syracuseStep 10830419 = 16245629) B16245629
theorem B31261373 : Blo 1502071 31261373 := bstep (se 3 (by rfl) ⟨5861507, by rfl⟩ : syracuseStep 31261373 = 11723015) B11723015
theorem B2253695 : Blo 1502071 2253695 := bstep (se 1 (by rfl) ⟨1690271, by rfl⟩ : syracuseStep 2253695 = 3380543) B3380543
theorem B2139319 : Blo 1502071 2139319 := bstep (se 1 (by rfl) ⟨1604489, by rfl⟩ : syracuseStep 2139319 = 3208979) B3208979
theorem B2254247 : Blo 1502071 2254247 := bstep (se 1 (by rfl) ⟨1690685, by rfl⟩ : syracuseStep 2254247 = 3381371) B3381371
theorem B2254319 : Blo 1502071 2254319 := bstep (se 1 (by rfl) ⟨1690739, by rfl⟩ : syracuseStep 2254319 = 3381479) B3381479
theorem B117155447 : Blo 1502071 117155447 := bstep (se 1 (by rfl) ⟨87866585, by rfl⟩ : syracuseStep 117155447 = 175733171) B175733171
theorem B9627295 : Blo 1502071 9627295 := bstep (se 1 (by rfl) ⟨7220471, by rfl⟩ : syracuseStep 9627295 = 14440943) B14440943
theorem B7218895 : Blo 1502071 7218895 := bstep (se 1 (by rfl) ⟨5414171, by rfl⟩ : syracuseStep 7218895 = 10828343) B10828343
theorem B5072651 : Blo 1502071 5072651 := bstep (se 1 (by rfl) ⟨3804488, by rfl⟩ : syracuseStep 5072651 = 7608977) B7608977
theorem B2254631 : Blo 1502071 2254631 := bstep (se 1 (by rfl) ⟨1690973, by rfl⟩ : syracuseStep 2254631 = 3381947) B3381947
theorem B2254703 : Blo 1502071 2254703 := bstep (se 1 (by rfl) ⟨1691027, by rfl⟩ : syracuseStep 2254703 = 3382055) B3382055
theorem B43337591 : Blo 1502071 43337591 := bstep (se 1 (by rfl) ⟨32503193, by rfl⟩ : syracuseStep 43337591 = 65006387) B65006387
theorem B2852911 : Blo 1502071 2852911 := bstep (se 1 (by rfl) ⟨2139683, by rfl⟩ : syracuseStep 2852911 = 4279367) B4279367
theorem B55585385 : Blo 1502071 55585385 := bstep (se 2 (by rfl) ⟨20844519, by rfl⟩ : syracuseStep 55585385 = 41689039) B41689039
theorem B5073785 : Blo 1502071 5073785 := bstep (se 2 (by rfl) ⟨1902669, by rfl⟩ : syracuseStep 5073785 = 3805339) B3805339
theorem B1502143 : Blo 1502071 1502143 := bstep (se 1 (by rfl) ⟨1126607, by rfl⟩ : syracuseStep 1502143 = 2253215) B2253215
theorem B1502447 : Blo 1502071 1502447 := bstep (se 1 (by rfl) ⟨1126835, by rfl⟩ : syracuseStep 1502447 = 2253671) B2253671
theorem B1690879 : Blo 1502071 1690879 := bstep (se 1 (by rfl) ⟨1268159, by rfl⟩ : syracuseStep 1690879 = 2536319) B2536319
theorem B12348683 : Blo 1502071 12348683 := bstep (se 1 (by rfl) ⟨9261512, by rfl⟩ : syracuseStep 12348683 = 18523025) B18523025
theorem B6417737 : Blo 1502071 6417737 := bstep (se 2 (by rfl) ⟨2406651, by rfl⟩ : syracuseStep 6417737 = 4813303) B4813303
theorem B1502671 : Blo 1502071 1502671 := bstep (se 1 (by rfl) ⟨1127003, by rfl⟩ : syracuseStep 1502671 = 2254007) B2254007
theorem B1502875 : Blo 1502071 1502875 := bstep (se 1 (by rfl) ⟨1127156, by rfl⟩ : syracuseStep 1502875 = 2254313) B2254313
theorem B3960659 : Blo 1502071 3960659 := bstep (se 1 (by rfl) ⟨2970494, by rfl⟩ : syracuseStep 3960659 = 5940989) B5940989
theorem B2535259 : Blo 1502071 2535259 := bstep (se 1 (by rfl) ⟨1901444, by rfl⟩ : syracuseStep 2535259 = 3802889) B3802889
theorem B2707447 : Blo 1502071 2707447 := bstep (se 1 (by rfl) ⟨2030585, by rfl⟩ : syracuseStep 2707447 = 4061171) B4061171
theorem B1503279 : Blo 1502071 1503279 := bstep (se 1 (by rfl) ⟨1127459, by rfl⟩ : syracuseStep 1503279 = 2254919) B2254919
theorem B8679569 : Blo 1502071 8679569 := bstep (se 2 (by rfl) ⟨3254838, by rfl⟩ : syracuseStep 8679569 = 6509677) B6509677
theorem B1503483 : Blo 1502071 1503483 := bstep (se 1 (by rfl) ⟨1127612, by rfl⟩ : syracuseStep 1503483 = 2255225) B2255225
theorem B1503487 : Blo 1502071 1503487 := bstep (se 1 (by rfl) ⟨1127615, by rfl⟩ : syracuseStep 1503487 = 2255231) B2255231
theorem B1503535 : Blo 1502071 1503535 := bstep (se 1 (by rfl) ⟨1127651, by rfl⟩ : syracuseStep 1503535 = 2255303) B2255303
theorem B20558245 : Blo 1502071 20558245 := bstep (se 4 (by rfl) ⟨1927335, by rfl⟩ : syracuseStep 20558245 = 3854671) B3854671
theorem B3379769 : Blo 1502071 3379769 := bstep (se 2 (by rfl) ⟨1267413, by rfl⟩ : syracuseStep 3379769 = 2534827) B2534827
theorem B7524989 : Blo 1502071 7524989 := bstep (se 3 (by rfl) ⟨1410935, by rfl⟩ : syracuseStep 7524989 = 2821871) B2821871
theorem B5706551 : Blo 1502071 5706551 := bstep (se 1 (by rfl) ⟨4279913, by rfl⟩ : syracuseStep 5706551 = 8559827) B8559827
theorem B3381119 : Blo 1502071 3381119 := bstep (se 1 (by rfl) ⟨2535839, by rfl⟩ : syracuseStep 3381119 = 5071679) B5071679
theorem B25679753 : Blo 1502071 25679753 := bstep (se 2 (by rfl) ⟨9629907, by rfl⟩ : syracuseStep 25679753 = 19259815) B19259815
theorem B2406395 : Blo 1502071 2406395 := bstep (se 1 (by rfl) ⟨1804796, by rfl⟩ : syracuseStep 2406395 = 3609593) B3609593
theorem B9140363 : Blo 1502071 9140363 := bstep (se 1 (by rfl) ⟨6855272, by rfl⟩ : syracuseStep 9140363 = 13710545) B13710545
theorem B3381551 : Blo 1502071 3381551 := bstep (se 1 (by rfl) ⟨2536163, by rfl⟩ : syracuseStep 3381551 = 5072327) B5072327
theorem B7420223 : Blo 1502071 7420223 := bstep (se 1 (by rfl) ⟨5565167, by rfl⟩ : syracuseStep 7420223 = 11130335) B11130335
theorem B12843431 : Blo 1502071 12843431 := bstep (se 1 (by rfl) ⟨9632573, by rfl⟩ : syracuseStep 12843431 = 19265147) B19265147
theorem B3857159 : Blo 1502071 3857159 := bstep (se 1 (by rfl) ⟨2892869, by rfl⟩ : syracuseStep 3857159 = 5785739) B5785739
theorem B11410793 : Blo 1502071 11410793 := bstep (se 2 (by rfl) ⟨4279047, by rfl⟩ : syracuseStep 11410793 = 8558095) B8558095
theorem B15417211 : Blo 1502071 15417211 := bstep (se 1 (by rfl) ⟨11562908, by rfl⟩ : syracuseStep 15417211 = 23125817) B23125817
theorem B54812645 : Blo 1502071 54812645 := bstep (se 4 (by rfl) ⟨5138685, by rfl⟩ : syracuseStep 54812645 = 10277371) B10277371
theorem B4571311 : Blo 1502071 4571311 := bstep (se 1 (by rfl) ⟨3428483, by rfl⟩ : syracuseStep 4571311 = 6856967) B6856967
theorem B2253179 : Blo 1502071 2253179 := bstep (se 1 (by rfl) ⟨1689884, by rfl⟩ : syracuseStep 2253179 = 3379769) B3379769
theorem B20840915 : Blo 1502071 20840915 := bstep (se 1 (by rfl) ⟨15630686, by rfl⟩ : syracuseStep 20840915 = 31261373) B31261373
theorem B27410993 : Blo 1502071 27410993 := bstep (se 2 (by rfl) ⟨10279122, by rfl⟩ : syracuseStep 27410993 = 20558245) B20558245
theorem B78103631 : Blo 1502071 78103631 := bstep (se 1 (by rfl) ⟨58577723, by rfl⟩ : syracuseStep 78103631 = 117155447) B117155447
theorem B2254079 : Blo 1502071 2254079 := bstep (se 1 (by rfl) ⟨1690559, by rfl⟩ : syracuseStep 2254079 = 3381119) B3381119
theorem B2254367 : Blo 1502071 2254367 := bstep (se 1 (by rfl) ⟨1690775, by rfl⟩ : syracuseStep 2254367 = 3381551) B3381551
theorem B2852425 : Blo 1502071 2852425 := bstep (se 2 (by rfl) ⟨1069659, by rfl⟩ : syracuseStep 2852425 = 2139319) B2139319
theorem B8562287 : Blo 1502071 8562287 := bstep (se 1 (by rfl) ⟨6421715, by rfl⟩ : syracuseStep 8562287 = 12843431) B12843431
theorem B2254505 : Blo 1502071 2254505 := bstep (se 2 (by rfl) ⟨845439, by rfl⟩ : syracuseStep 2254505 = 1690879) B1690879
theorem B4278491 : Blo 1502071 4278491 := bstep (se 1 (by rfl) ⟨3208868, by rfl⟩ : syracuseStep 4278491 = 6417737) B6417737
theorem B20556281 : Blo 1502071 20556281 := bstep (se 2 (by rfl) ⟨7708605, by rfl⟩ : syracuseStep 20556281 = 15417211) B15417211
theorem B2640439 : Blo 1502071 2640439 := bstep (se 1 (by rfl) ⟨1980329, by rfl⟩ : syracuseStep 2640439 = 3960659) B3960659
theorem B6417053 : Blo 1502071 6417053 := bstep (se 3 (by rfl) ⟨1203197, by rfl⟩ : syracuseStep 6417053 = 2406395) B2406395
theorem B3803881 : Blo 1502071 3803881 := bstep (se 2 (by rfl) ⟨1426455, by rfl⟩ : syracuseStep 3803881 = 2852911) B2852911
theorem B32484331 : Blo 1502071 32484331 := bstep (se 1 (by rfl) ⟨24363248, by rfl⟩ : syracuseStep 32484331 = 48726497) B48726497
theorem B1502235 : Blo 1502071 1502235 := bstep (se 1 (by rfl) ⟨1126676, by rfl⟩ : syracuseStep 1502235 = 2253353) B2253353
theorem B23145517 : Blo 1502071 23145517 := bstep (se 3 (by rfl) ⟨4339784, by rfl⟩ : syracuseStep 23145517 = 8679569) B8679569
theorem B7220279 : Blo 1502071 7220279 := bstep (se 1 (by rfl) ⟨5415209, by rfl⟩ : syracuseStep 7220279 = 10830419) B10830419
theorem B5016659 : Blo 1502071 5016659 := bstep (se 1 (by rfl) ⟨3762494, by rfl⟩ : syracuseStep 5016659 = 7524989) B7524989
theorem B3804367 : Blo 1502071 3804367 := bstep (se 1 (by rfl) ⟨2853275, by rfl⟩ : syracuseStep 3804367 = 5706551) B5706551
theorem B1502463 : Blo 1502071 1502463 := bstep (se 1 (by rfl) ⟨1126847, by rfl⟩ : syracuseStep 1502463 = 2253695) B2253695
theorem B1502831 : Blo 1502071 1502831 := bstep (se 1 (by rfl) ⟨1127123, by rfl⟩ : syracuseStep 1502831 = 2254247) B2254247
theorem B1502879 : Blo 1502071 1502879 := bstep (se 1 (by rfl) ⟨1127159, by rfl⟩ : syracuseStep 1502879 = 2254319) B2254319
theorem B1503087 : Blo 1502071 1503087 := bstep (se 1 (by rfl) ⟨1127315, by rfl⟩ : syracuseStep 1503087 = 2254631) B2254631
theorem B1503135 : Blo 1502071 1503135 := bstep (se 1 (by rfl) ⟨1127351, by rfl⟩ : syracuseStep 1503135 = 2254703) B2254703
theorem B37056923 : Blo 1502071 37056923 := bstep (se 1 (by rfl) ⟨27792692, by rfl⟩ : syracuseStep 37056923 = 55585385) B55585385
theorem B7607195 : Blo 1502071 7607195 := bstep (se 1 (by rfl) ⟨5705396, by rfl⟩ : syracuseStep 7607195 = 11410793) B11410793
theorem B3380345 : Blo 1502071 3380345 := bstep (se 2 (by rfl) ⟨1267629, by rfl⟩ : syracuseStep 3380345 = 2535259) B2535259
theorem B36541763 : Blo 1502071 36541763 := bstep (se 1 (by rfl) ⟨27406322, by rfl⟩ : syracuseStep 36541763 = 54812645) B54812645
theorem B3609929 : Blo 1502071 3609929 := bstep (se 2 (by rfl) ⟨1353723, by rfl⟩ : syracuseStep 3609929 = 2707447) B2707447
theorem B3381767 : Blo 1502071 3381767 := bstep (se 1 (by rfl) ⟨2536325, by rfl⟩ : syracuseStep 3381767 = 5072651) B5072651
theorem B28891727 : Blo 1502071 28891727 := bstep (se 1 (by rfl) ⟨21668795, by rfl⟩ : syracuseStep 28891727 = 43337591) B43337591
theorem B17119835 : Blo 1502071 17119835 := bstep (se 1 (by rfl) ⟨12839876, by rfl⟩ : syracuseStep 17119835 = 25679753) B25679753
theorem B6093575 : Blo 1502071 6093575 := bstep (se 1 (by rfl) ⟨4570181, by rfl⟩ : syracuseStep 6093575 = 9140363) B9140363
theorem B4946815 : Blo 1502071 4946815 := bstep (se 1 (by rfl) ⟨3710111, by rfl⟩ : syracuseStep 4946815 = 7420223) B7420223
theorem B2571439 : Blo 1502071 2571439 := bstep (se 1 (by rfl) ⟨1928579, by rfl⟩ : syracuseStep 2571439 = 3857159) B3857159
theorem B3382523 : Blo 1502071 3382523 := bstep (se 1 (by rfl) ⟨2536892, by rfl⟩ : syracuseStep 3382523 = 5073785) B5073785
theorem B8232455 : Blo 1502071 8232455 := bstep (se 1 (by rfl) ⟨6174341, by rfl⟩ : syracuseStep 8232455 = 12348683) B12348683
theorem B12836393 : Blo 1502071 12836393 := bstep (se 2 (by rfl) ⟨4813647, by rfl⟩ : syracuseStep 12836393 = 9627295) B9627295
theorem B9625193 : Blo 1502071 9625193 := bstep (se 2 (by rfl) ⟨3609447, by rfl⟩ : syracuseStep 9625193 = 7218895) B7218895
theorem B6095081 : Blo 1502071 6095081 := bstep (se 2 (by rfl) ⟨2285655, by rfl⟩ : syracuseStep 6095081 = 4571311) B4571311
theorem B14082341 : Blo 1502071 14082341 := bstep (se 4 (by rfl) ⟨1320219, by rfl⟩ : syracuseStep 14082341 = 2640439) B2640439
theorem B13893943 : Blo 1502071 13893943 := bstep (se 1 (by rfl) ⟨10420457, by rfl⟩ : syracuseStep 13893943 = 20840915) B20840915
theorem B5071463 : Blo 1502071 5071463 := bstep (se 1 (by rfl) ⟨3803597, by rfl⟩ : syracuseStep 5071463 = 7607195) B7607195
theorem B52069087 : Blo 1502071 52069087 := bstep (se 1 (by rfl) ⟨39051815, by rfl⟩ : syracuseStep 52069087 = 78103631) B78103631
theorem B2253563 : Blo 1502071 2253563 := bstep (se 1 (by rfl) ⟨1690172, by rfl⟩ : syracuseStep 2253563 = 3380345) B3380345
theorem B53511029 : Blo 1502071 53511029 := bstep (se 5 (by rfl) ⟨2508329, by rfl⟩ : syracuseStep 53511029 = 5016659) B5016659
theorem B5071841 : Blo 1502071 5071841 := bstep (se 2 (by rfl) ⟨1901940, by rfl⟩ : syracuseStep 5071841 = 3803881) B3803881
theorem B6595753 : Blo 1502071 6595753 := bstep (se 2 (by rfl) ⟨2473407, by rfl⟩ : syracuseStep 6595753 = 4946815) B4946815
theorem B43312441 : Blo 1502071 43312441 := bstep (se 2 (by rfl) ⟨16242165, by rfl⟩ : syracuseStep 43312441 = 32484331) B32484331
theorem B30860689 : Blo 1502071 30860689 := bstep (se 2 (by rfl) ⟨11572758, by rfl⟩ : syracuseStep 30860689 = 23145517) B23145517
theorem B2852327 : Blo 1502071 2852327 := bstep (se 1 (by rfl) ⟨2139245, by rfl⟩ : syracuseStep 2852327 = 4278491) B4278491
theorem B5072489 : Blo 1502071 5072489 := bstep (se 2 (by rfl) ⟨1902183, by rfl⟩ : syracuseStep 5072489 = 3804367) B3804367
theorem B2254511 : Blo 1502071 2254511 := bstep (se 1 (by rfl) ⟨1690883, by rfl⟩ : syracuseStep 2254511 = 3381767) B3381767
theorem B19261151 : Blo 1502071 19261151 := bstep (se 1 (by rfl) ⟨14445863, by rfl⟩ : syracuseStep 19261151 = 28891727) B28891727
theorem B11413223 : Blo 1502071 11413223 := bstep (se 1 (by rfl) ⟨8559917, by rfl⟩ : syracuseStep 11413223 = 17119835) B17119835
theorem B4278035 : Blo 1502071 4278035 := bstep (se 1 (by rfl) ⟨3208526, by rfl⟩ : syracuseStep 4278035 = 6417053) B6417053
theorem B3803233 : Blo 1502071 3803233 := bstep (se 2 (by rfl) ⟨1426212, by rfl⟩ : syracuseStep 3803233 = 2852425) B2852425
theorem B2255015 : Blo 1502071 2255015 := bstep (se 1 (by rfl) ⟨1691261, by rfl⟩ : syracuseStep 2255015 = 3382523) B3382523
theorem B6416795 : Blo 1502071 6416795 := bstep (se 1 (by rfl) ⟨4812596, by rfl⟩ : syracuseStep 6416795 = 9625193) B9625193
theorem B1502119 : Blo 1502071 1502119 := bstep (se 1 (by rfl) ⟨1126589, by rfl⟩ : syracuseStep 1502119 = 2253179) B2253179
theorem B1502719 : Blo 1502071 1502719 := bstep (se 1 (by rfl) ⟨1127039, by rfl⟩ : syracuseStep 1502719 = 2254079) B2254079
theorem B1502911 : Blo 1502071 1502911 := bstep (se 1 (by rfl) ⟨1127183, by rfl⟩ : syracuseStep 1502911 = 2254367) B2254367
theorem B1503003 : Blo 1502071 1503003 := bstep (se 1 (by rfl) ⟨1127252, by rfl⟩ : syracuseStep 1503003 = 2254505) B2254505
theorem B3428585 : Blo 1502071 3428585 := bstep (se 2 (by rfl) ⟨1285719, by rfl⟩ : syracuseStep 3428585 = 2571439) B2571439
theorem B4813519 : Blo 1502071 4813519 := bstep (se 1 (by rfl) ⟨3610139, by rfl⟩ : syracuseStep 4813519 = 7220279) B7220279
theorem B8557595 : Blo 1502071 8557595 := bstep (se 1 (by rfl) ⟨6418196, by rfl⟩ : syracuseStep 8557595 = 12836393) B12836393
theorem B24704615 : Blo 1502071 24704615 := bstep (se 1 (by rfl) ⟨18528461, by rfl⟩ : syracuseStep 24704615 = 37056923) B37056923
theorem B18273995 : Blo 1502071 18273995 := bstep (se 1 (by rfl) ⟨13705496, by rfl⟩ : syracuseStep 18273995 = 27410993) B27410993
theorem B24361175 : Blo 1502071 24361175 := bstep (se 1 (by rfl) ⟨18270881, by rfl⟩ : syracuseStep 24361175 = 36541763) B36541763
theorem B2406619 : Blo 1502071 2406619 := bstep (se 1 (by rfl) ⟨1804964, by rfl⟩ : syracuseStep 2406619 = 3609929) B3609929
theorem B5708191 : Blo 1502071 5708191 := bstep (se 1 (by rfl) ⟨4281143, by rfl⟩ : syracuseStep 5708191 = 8562287) B8562287
theorem B21953213 : Blo 1502071 21953213 := bstep (se 3 (by rfl) ⟨4116227, by rfl⟩ : syracuseStep 21953213 = 8232455) B8232455
theorem B13704187 : Blo 1502071 13704187 := bstep (se 1 (by rfl) ⟨10278140, by rfl⟩ : syracuseStep 13704187 = 20556281) B20556281
theorem B4062383 : Blo 1502071 4062383 := bstep (se 1 (by rfl) ⟨3046787, by rfl⟩ : syracuseStep 4062383 = 6093575) B6093575
theorem B5070977 : Blo 1502071 5070977 := bstep (se 2 (by rfl) ⟨1901616, by rfl⟩ : syracuseStep 5070977 = 3803233) B3803233
theorem B4063387 : Blo 1502071 4063387 := bstep (se 1 (by rfl) ⟨3047540, by rfl⟩ : syracuseStep 4063387 = 6095081) B6095081
theorem B2285723 : Blo 1502071 2285723 := bstep (se 1 (by rfl) ⟨1714292, by rfl⟩ : syracuseStep 2285723 = 3428585) B3428585
theorem B7610921 : Blo 1502071 7610921 := bstep (se 2 (by rfl) ⟨2854095, by rfl⟩ : syracuseStep 7610921 = 5708191) B5708191
theorem B37552909 : Blo 1502071 37552909 := bstep (se 3 (by rfl) ⟨7041170, by rfl⟩ : syracuseStep 37552909 = 14082341) B14082341
theorem B1901551 : Blo 1502071 1901551 := bstep (se 1 (by rfl) ⟨1426163, by rfl⟩ : syracuseStep 1901551 = 2852327) B2852327
theorem B12182663 : Blo 1502071 12182663 := bstep (se 1 (by rfl) ⟨9136997, by rfl⟩ : syracuseStep 12182663 = 18273995) B18273995
theorem B277701797 : Blo 1502071 277701797 := bstep (se 4 (by rfl) ⟨26034543, by rfl⟩ : syracuseStep 277701797 = 52069087) B52069087
theorem B2852023 : Blo 1502071 2852023 := bstep (se 1 (by rfl) ⟨2139017, by rfl⟩ : syracuseStep 2852023 = 4278035) B4278035
theorem B4277863 : Blo 1502071 4277863 := bstep (se 1 (by rfl) ⟨3208397, by rfl⟩ : syracuseStep 4277863 = 6416795) B6416795
theorem B18525257 : Blo 1502071 18525257 := bstep (se 2 (by rfl) ⟨6946971, by rfl⟩ : syracuseStep 18525257 = 13893943) B13893943
theorem B1502375 : Blo 1502071 1502375 := bstep (se 1 (by rfl) ⟨1126781, by rfl⟩ : syracuseStep 1502375 = 2253563) B2253563
theorem B5705063 : Blo 1502071 5705063 := bstep (se 1 (by rfl) ⟨4278797, by rfl⟩ : syracuseStep 5705063 = 8557595) B8557595
theorem B6418025 : Blo 1502071 6418025 := bstep (se 2 (by rfl) ⟨2406759, by rfl⟩ : syracuseStep 6418025 = 4813519) B4813519
theorem B16469743 : Blo 1502071 16469743 := bstep (se 1 (by rfl) ⟨12352307, by rfl⟩ : syracuseStep 16469743 = 24704615) B24704615
theorem B1503007 : Blo 1502071 1503007 := bstep (se 1 (by rfl) ⟨1127255, by rfl⟩ : syracuseStep 1503007 = 2254511) B2254511
theorem B12840767 : Blo 1502071 12840767 := bstep (se 1 (by rfl) ⟨9630575, by rfl⟩ : syracuseStep 12840767 = 19261151) B19261151
theorem B18272249 : Blo 1502071 18272249 := bstep (se 2 (by rfl) ⟨6852093, by rfl⟩ : syracuseStep 18272249 = 13704187) B13704187
theorem B1503343 : Blo 1502071 1503343 := bstep (se 1 (by rfl) ⟨1127507, by rfl⟩ : syracuseStep 1503343 = 2255015) B2255015
theorem B16240783 : Blo 1502071 16240783 := bstep (se 1 (by rfl) ⟨12180587, by rfl⟩ : syracuseStep 16240783 = 24361175) B24361175
theorem B8794337 : Blo 1502071 8794337 := bstep (se 2 (by rfl) ⟨3297876, by rfl⟩ : syracuseStep 8794337 = 6595753) B6595753
theorem B57749921 : Blo 1502071 57749921 := bstep (se 2 (by rfl) ⟨21656220, by rfl⟩ : syracuseStep 57749921 = 43312441) B43312441
theorem B14635475 : Blo 1502071 14635475 := bstep (se 1 (by rfl) ⟨10976606, by rfl⟩ : syracuseStep 14635475 = 21953213) B21953213
theorem B2708255 : Blo 1502071 2708255 := bstep (se 1 (by rfl) ⟨2031191, by rfl⟩ : syracuseStep 2708255 = 4062383) B4062383
theorem B3208825 : Blo 1502071 3208825 := bstep (se 2 (by rfl) ⟨1203309, by rfl⟩ : syracuseStep 3208825 = 2406619) B2406619
theorem B3380975 : Blo 1502071 3380975 := bstep (se 1 (by rfl) ⟨2535731, by rfl⟩ : syracuseStep 3380975 = 5071463) B5071463
theorem B35674019 : Blo 1502071 35674019 := bstep (se 1 (by rfl) ⟨26755514, by rfl⟩ : syracuseStep 35674019 = 53511029) B53511029
theorem B3381227 : Blo 1502071 3381227 := bstep (se 1 (by rfl) ⟨2535920, by rfl⟩ : syracuseStep 3381227 = 5071841) B5071841
theorem B3381659 : Blo 1502071 3381659 := bstep (se 1 (by rfl) ⟨2536244, by rfl⟩ : syracuseStep 3381659 = 5072489) B5072489
theorem B7608815 : Blo 1502071 7608815 := bstep (se 1 (by rfl) ⟨5706611, by rfl⟩ : syracuseStep 7608815 = 11413223) B11413223
theorem B41147585 : Blo 1502071 41147585 := bstep (se 2 (by rfl) ⟨15430344, by rfl⟩ : syracuseStep 41147585 = 30860689) B30860689
theorem B1523815 : Blo 1502071 1523815 := bstep (se 1 (by rfl) ⟨1142861, by rfl⟩ : syracuseStep 1523815 = 2285723) B2285723
theorem B9756983 : Blo 1502071 9756983 := bstep (se 1 (by rfl) ⟨7317737, by rfl⟩ : syracuseStep 9756983 = 14635475) B14635475
theorem B50070545 : Blo 1502071 50070545 := bstep (se 2 (by rfl) ⟨18776454, by rfl⟩ : syracuseStep 50070545 = 37552909) B37552909
theorem B2253983 : Blo 1502071 2253983 := bstep (se 1 (by rfl) ⟨1690487, by rfl⟩ : syracuseStep 2253983 = 3380975) B3380975
theorem B23782679 : Blo 1502071 23782679 := bstep (se 1 (by rfl) ⟨17837009, by rfl⟩ : syracuseStep 23782679 = 35674019) B35674019
theorem B2254151 : Blo 1502071 2254151 := bstep (se 1 (by rfl) ⟨1690613, by rfl⟩ : syracuseStep 2254151 = 3381227) B3381227
theorem B3802697 : Blo 1502071 3802697 := bstep (se 2 (by rfl) ⟨1426011, by rfl⟩ : syracuseStep 3802697 = 2852023) B2852023
theorem B2254439 : Blo 1502071 2254439 := bstep (se 1 (by rfl) ⟨1690829, by rfl⟩ : syracuseStep 2254439 = 3381659) B3381659
theorem B5072543 : Blo 1502071 5072543 := bstep (se 1 (by rfl) ⟨3804407, by rfl⟩ : syracuseStep 5072543 = 7608815) B7608815
theorem B5703817 : Blo 1502071 5703817 := bstep (se 2 (by rfl) ⟨2138931, by rfl⟩ : syracuseStep 5703817 = 4277863) B4277863
theorem B4278433 : Blo 1502071 4278433 := bstep (se 2 (by rfl) ⟨1604412, by rfl⟩ : syracuseStep 4278433 = 3208825) B3208825
theorem B3803375 : Blo 1502071 3803375 := bstep (se 1 (by rfl) ⟨2852531, by rfl⟩ : syracuseStep 3803375 = 5705063) B5705063
theorem B4278683 : Blo 1502071 4278683 := bstep (se 1 (by rfl) ⟨3209012, by rfl⟩ : syracuseStep 4278683 = 6418025) B6418025
theorem B21654377 : Blo 1502071 21654377 := bstep (se 2 (by rfl) ⟨8120391, by rfl⟩ : syracuseStep 21654377 = 16240783) B16240783
theorem B5417849 : Blo 1502071 5417849 := bstep (se 2 (by rfl) ⟨2031693, by rfl⟩ : syracuseStep 5417849 = 4063387) B4063387
theorem B5073947 : Blo 1502071 5073947 := bstep (se 1 (by rfl) ⟨3805460, by rfl⟩ : syracuseStep 5073947 = 7610921) B7610921
theorem B1805503 : Blo 1502071 1805503 := bstep (se 1 (by rfl) ⟨1354127, by rfl⟩ : syracuseStep 1805503 = 2708255) B2708255
theorem B2535401 : Blo 1502071 2535401 := bstep (se 2 (by rfl) ⟨950775, by rfl⟩ : syracuseStep 2535401 = 1901551) B1901551
theorem B12350171 : Blo 1502071 12350171 := bstep (se 1 (by rfl) ⟨9262628, by rfl⟩ : syracuseStep 12350171 = 18525257) B18525257
theorem B27431723 : Blo 1502071 27431723 := bstep (se 1 (by rfl) ⟨20573792, by rfl⟩ : syracuseStep 27431723 = 41147585) B41147585
theorem B21959657 : Blo 1502071 21959657 := bstep (se 2 (by rfl) ⟨8234871, by rfl⟩ : syracuseStep 21959657 = 16469743) B16469743
theorem B3380651 : Blo 1502071 3380651 := bstep (se 1 (by rfl) ⟨2535488, by rfl⟩ : syracuseStep 3380651 = 5070977) B5070977
theorem B38499947 : Blo 1502071 38499947 := bstep (se 1 (by rfl) ⟨28874960, by rfl⟩ : syracuseStep 38499947 = 57749921) B57749921
theorem B32487101 : Blo 1502071 32487101 := bstep (se 3 (by rfl) ⟨6091331, by rfl⟩ : syracuseStep 32487101 = 12182663) B12182663
theorem B740538125 : Blo 1502071 740538125 := bstep (se 3 (by rfl) ⟨138850898, by rfl⟩ : syracuseStep 740538125 = 277701797) B277701797
theorem B93806261 : Blo 1502071 93806261 := bstep (se 5 (by rfl) ⟨4397168, by rfl⟩ : syracuseStep 93806261 = 8794337) B8794337
theorem B8560511 : Blo 1502071 8560511 := bstep (se 1 (by rfl) ⟨6420383, by rfl⟩ : syracuseStep 8560511 = 12840767) B12840767
theorem B12181499 : Blo 1502071 12181499 := bstep (se 1 (by rfl) ⟨9136124, by rfl⟩ : syracuseStep 12181499 = 18272249) B18272249
theorem B8233447 : Blo 1502071 8233447 := bstep (se 1 (by rfl) ⟨6175085, by rfl⟩ : syracuseStep 8233447 = 12350171) B12350171
theorem B8127013 : Blo 1502071 8127013 := bstep (se 4 (by rfl) ⟨761907, by rfl⟩ : syracuseStep 8127013 = 1523815) B1523815
theorem B14639771 : Blo 1502071 14639771 := bstep (se 1 (by rfl) ⟨10979828, by rfl⟩ : syracuseStep 14639771 = 21959657) B21959657
theorem B26018621 : Blo 1502071 26018621 := bstep (se 3 (by rfl) ⟨4878491, by rfl⟩ : syracuseStep 26018621 = 9756983) B9756983
theorem B2253767 : Blo 1502071 2253767 := bstep (se 1 (by rfl) ⟨1690325, by rfl⟩ : syracuseStep 2253767 = 3380651) B3380651
theorem B25666631 : Blo 1502071 25666631 := bstep (se 1 (by rfl) ⟨19249973, by rfl⟩ : syracuseStep 25666631 = 38499947) B38499947
theorem B493692083 : Blo 1502071 493692083 := bstep (se 1 (by rfl) ⟨370269062, by rfl⟩ : syracuseStep 493692083 = 740538125) B740538125
theorem B14436251 : Blo 1502071 14436251 := bstep (se 1 (by rfl) ⟨10827188, by rfl⟩ : syracuseStep 14436251 = 21654377) B21654377
theorem B1690267 : Blo 1502071 1690267 := bstep (se 1 (by rfl) ⟨1267700, by rfl⟩ : syracuseStep 1690267 = 2535401) B2535401
theorem B8120999 : Blo 1502071 8120999 := bstep (se 1 (by rfl) ⟨6090749, by rfl⟩ : syracuseStep 8120999 = 12181499) B12181499
theorem B7605089 : Blo 1502071 7605089 := bstep (se 2 (by rfl) ⟨2851908, by rfl⟩ : syracuseStep 7605089 = 5703817) B5703817
theorem B5704577 : Blo 1502071 5704577 := bstep (se 2 (by rfl) ⟨2139216, by rfl⟩ : syracuseStep 5704577 = 4278433) B4278433
theorem B18287815 : Blo 1502071 18287815 := bstep (se 1 (by rfl) ⟨13715861, by rfl⟩ : syracuseStep 18287815 = 27431723) B27431723
theorem B1502655 : Blo 1502071 1502655 := bstep (se 1 (by rfl) ⟨1126991, by rfl⟩ : syracuseStep 1502655 = 2253983) B2253983
theorem B15855119 : Blo 1502071 15855119 := bstep (se 1 (by rfl) ⟨11891339, by rfl⟩ : syracuseStep 15855119 = 23782679) B23782679
theorem B1502767 : Blo 1502071 1502767 := bstep (se 1 (by rfl) ⟨1127075, by rfl⟩ : syracuseStep 1502767 = 2254151) B2254151
theorem B2535131 : Blo 1502071 2535131 := bstep (se 1 (by rfl) ⟨1901348, by rfl⟩ : syracuseStep 2535131 = 3802697) B3802697
theorem B1502959 : Blo 1502071 1502959 := bstep (se 1 (by rfl) ⟨1127219, by rfl⟩ : syracuseStep 1502959 = 2254439) B2254439
theorem B2535583 : Blo 1502071 2535583 := bstep (se 1 (by rfl) ⟨1901687, by rfl⟩ : syracuseStep 2535583 = 3803375) B3803375
theorem B5707007 : Blo 1502071 5707007 := bstep (se 1 (by rfl) ⟨4280255, by rfl⟩ : syracuseStep 5707007 = 8560511) B8560511
theorem B33380363 : Blo 1502071 33380363 := bstep (se 1 (by rfl) ⟨25035272, by rfl⟩ : syracuseStep 33380363 = 50070545) B50070545
theorem B11409821 : Blo 1502071 11409821 := bstep (se 3 (by rfl) ⟨2139341, by rfl⟩ : syracuseStep 11409821 = 4278683) B4278683
theorem B3381695 : Blo 1502071 3381695 := bstep (se 1 (by rfl) ⟨2536271, by rfl⟩ : syracuseStep 3381695 = 5072543) B5072543
theorem B21658067 : Blo 1502071 21658067 := bstep (se 1 (by rfl) ⟨16243550, by rfl⟩ : syracuseStep 21658067 = 32487101) B32487101
theorem B2407337 : Blo 1502071 2407337 := bstep (se 2 (by rfl) ⟨902751, by rfl⟩ : syracuseStep 2407337 = 1805503) B1805503
theorem B3611899 : Blo 1502071 3611899 := bstep (se 1 (by rfl) ⟨2708924, by rfl⟩ : syracuseStep 3611899 = 5417849) B5417849
theorem B3382631 : Blo 1502071 3382631 := bstep (se 1 (by rfl) ⟨2536973, by rfl⟩ : syracuseStep 3382631 = 5073947) B5073947
theorem B62537507 : Blo 1502071 62537507 := bstep (se 1 (by rfl) ⟨46903130, by rfl⟩ : syracuseStep 62537507 = 93806261) B93806261
theorem B10977929 : Blo 1502071 10977929 := bstep (se 2 (by rfl) ⟨4116723, by rfl⟩ : syracuseStep 10977929 = 8233447) B8233447
theorem B2253689 : Blo 1502071 2253689 := bstep (se 2 (by rfl) ⟨845133, by rfl⟩ : syracuseStep 2253689 = 1690267) B1690267
theorem B2254463 : Blo 1502071 2254463 := bstep (se 1 (by rfl) ⟨1690847, by rfl⟩ : syracuseStep 2254463 = 3381695) B3381695
theorem B3803051 : Blo 1502071 3803051 := bstep (se 1 (by rfl) ⟨2852288, by rfl⟩ : syracuseStep 3803051 = 5704577) B5704577
theorem B2255087 : Blo 1502071 2255087 := bstep (se 1 (by rfl) ⟨1691315, by rfl⟩ : syracuseStep 2255087 = 3382631) B3382631
theorem B10570079 : Blo 1502071 10570079 := bstep (se 1 (by rfl) ⟨7927559, by rfl⟩ : syracuseStep 10570079 = 15855119) B15855119
theorem B1690087 : Blo 1502071 1690087 := bstep (se 1 (by rfl) ⟨1267565, by rfl⟩ : syracuseStep 1690087 = 2535131) B2535131
theorem B41691671 : Blo 1502071 41691671 := bstep (se 1 (by rfl) ⟨31268753, by rfl⟩ : syracuseStep 41691671 = 62537507) B62537507
theorem B9759847 : Blo 1502071 9759847 := bstep (se 1 (by rfl) ⟨7319885, by rfl⟩ : syracuseStep 9759847 = 14639771) B14639771
theorem B17345747 : Blo 1502071 17345747 := bstep (se 1 (by rfl) ⟨13009310, by rfl⟩ : syracuseStep 17345747 = 26018621) B26018621
theorem B1502511 : Blo 1502071 1502511 := bstep (se 1 (by rfl) ⟨1126883, by rfl⟩ : syracuseStep 1502511 = 2253767) B2253767
theorem B3804671 : Blo 1502071 3804671 := bstep (se 1 (by rfl) ⟨2853503, by rfl⟩ : syracuseStep 3804671 = 5707007) B5707007
theorem B22253575 : Blo 1502071 22253575 := bstep (se 1 (by rfl) ⟨16690181, by rfl⟩ : syracuseStep 22253575 = 33380363) B33380363
theorem B24383753 : Blo 1502071 24383753 := bstep (se 2 (by rfl) ⟨9143907, by rfl⟩ : syracuseStep 24383753 = 18287815) B18287815
theorem B7606547 : Blo 1502071 7606547 := bstep (se 1 (by rfl) ⟨5704910, by rfl⟩ : syracuseStep 7606547 = 11409821) B11409821
theorem B14438711 : Blo 1502071 14438711 := bstep (se 1 (by rfl) ⟨10829033, by rfl⟩ : syracuseStep 14438711 = 21658067) B21658067
theorem B3380777 : Blo 1502071 3380777 := bstep (se 2 (by rfl) ⟨1267791, by rfl⟩ : syracuseStep 3380777 = 2535583) B2535583
theorem B17111087 : Blo 1502071 17111087 := bstep (se 1 (by rfl) ⟨12833315, by rfl⟩ : syracuseStep 17111087 = 25666631) B25666631
theorem B10836017 : Blo 1502071 10836017 := bstep (se 2 (by rfl) ⟨4063506, by rfl⟩ : syracuseStep 10836017 = 8127013) B8127013
theorem B329128055 : Blo 1502071 329128055 := bstep (se 1 (by rfl) ⟨246846041, by rfl⟩ : syracuseStep 329128055 = 493692083) B493692083
theorem B9624167 : Blo 1502071 9624167 := bstep (se 1 (by rfl) ⟨7218125, by rfl⟩ : syracuseStep 9624167 = 14436251) B14436251
theorem B4815865 : Blo 1502071 4815865 := bstep (se 2 (by rfl) ⟨1805949, by rfl⟩ : syracuseStep 4815865 = 3611899) B3611899
theorem B5413999 : Blo 1502071 5413999 := bstep (se 1 (by rfl) ⟨4060499, by rfl⟩ : syracuseStep 5413999 = 8120999) B8120999
theorem B5070059 : Blo 1502071 5070059 := bstep (se 1 (by rfl) ⟨3802544, by rfl⟩ : syracuseStep 5070059 = 7605089) B7605089
theorem B1604891 : Blo 1502071 1604891 := bstep (se 1 (by rfl) ⟨1203668, by rfl⟩ : syracuseStep 1604891 = 2407337) B2407337
theorem B29671433 : Blo 1502071 29671433 := bstep (se 2 (by rfl) ⟨11126787, by rfl⟩ : syracuseStep 29671433 = 22253575) B22253575
theorem B5071031 : Blo 1502071 5071031 := bstep (se 1 (by rfl) ⟨3803273, by rfl⟩ : syracuseStep 5071031 = 7606547) B7606547
theorem B9625807 : Blo 1502071 9625807 := bstep (se 1 (by rfl) ⟨7219355, by rfl⟩ : syracuseStep 9625807 = 14438711) B14438711
theorem B2253449 : Blo 1502071 2253449 := bstep (se 2 (by rfl) ⟨845043, by rfl⟩ : syracuseStep 2253449 = 1690087) B1690087
theorem B2253851 : Blo 1502071 2253851 := bstep (se 1 (by rfl) ⟨1690388, by rfl⟩ : syracuseStep 2253851 = 3380777) B3380777
theorem B7218665 : Blo 1502071 7218665 := bstep (se 2 (by rfl) ⟨2706999, by rfl⟩ : syracuseStep 7218665 = 5413999) B5413999
theorem B7046719 : Blo 1502071 7046719 := bstep (se 1 (by rfl) ⟨5285039, by rfl⟩ : syracuseStep 7046719 = 10570079) B10570079
theorem B6416111 : Blo 1502071 6416111 := bstep (se 1 (by rfl) ⟨4812083, by rfl⟩ : syracuseStep 6416111 = 9624167) B9624167
theorem B16255835 : Blo 1502071 16255835 := bstep (se 1 (by rfl) ⟨12191876, by rfl⟩ : syracuseStep 16255835 = 24383753) B24383753
theorem B7318619 : Blo 1502071 7318619 := bstep (se 1 (by rfl) ⟨5488964, by rfl⟩ : syracuseStep 7318619 = 10977929) B10977929
theorem B1502459 : Blo 1502071 1502459 := bstep (se 1 (by rfl) ⟨1126844, by rfl⟩ : syracuseStep 1502459 = 2253689) B2253689
theorem B4279709 : Blo 1502071 4279709 := bstep (se 3 (by rfl) ⟨802445, by rfl⟩ : syracuseStep 4279709 = 1604891) B1604891
theorem B1502975 : Blo 1502071 1502975 := bstep (se 1 (by rfl) ⟨1127231, by rfl⟩ : syracuseStep 1502975 = 2254463) B2254463
theorem B2535367 : Blo 1502071 2535367 := bstep (se 1 (by rfl) ⟨1901525, by rfl⟩ : syracuseStep 2535367 = 3803051) B3803051
theorem B11407391 : Blo 1502071 11407391 := bstep (se 1 (by rfl) ⟨8555543, by rfl⟩ : syracuseStep 11407391 = 17111087) B17111087
theorem B219418703 : Blo 1502071 219418703 := bstep (se 1 (by rfl) ⟨164564027, by rfl⟩ : syracuseStep 219418703 = 329128055) B329128055
theorem B13013129 : Blo 1502071 13013129 := bstep (se 2 (by rfl) ⟨4879923, by rfl⟩ : syracuseStep 13013129 = 9759847) B9759847
theorem B1503391 : Blo 1502071 1503391 := bstep (se 1 (by rfl) ⟨1127543, by rfl⟩ : syracuseStep 1503391 = 2255087) B2255087
theorem B11563831 : Blo 1502071 11563831 := bstep (se 1 (by rfl) ⟨8672873, by rfl⟩ : syracuseStep 11563831 = 17345747) B17345747
theorem B3380039 : Blo 1502071 3380039 := bstep (se 1 (by rfl) ⟨2535029, by rfl⟩ : syracuseStep 3380039 = 5070059) B5070059
theorem B2536447 : Blo 1502071 2536447 := bstep (se 1 (by rfl) ⟨1902335, by rfl⟩ : syracuseStep 2536447 = 3804671) B3804671
theorem B6421153 : Blo 1502071 6421153 := bstep (se 2 (by rfl) ⟨2407932, by rfl⟩ : syracuseStep 6421153 = 4815865) B4815865
theorem B7224011 : Blo 1502071 7224011 := bstep (se 1 (by rfl) ⟨5418008, by rfl⟩ : syracuseStep 7224011 = 10836017) B10836017
theorem B27794447 : Blo 1502071 27794447 := bstep (se 1 (by rfl) ⟨20845835, by rfl⟩ : syracuseStep 27794447 = 41691671) B41691671
theorem B8675419 : Blo 1502071 8675419 := bstep (se 1 (by rfl) ⟨6506564, by rfl⟩ : syracuseStep 8675419 = 13013129) B13013129
theorem B2253359 : Blo 1502071 2253359 := bstep (se 1 (by rfl) ⟨1690019, by rfl⟩ : syracuseStep 2253359 = 3380039) B3380039
theorem B8561537 : Blo 1502071 8561537 := bstep (se 2 (by rfl) ⟨3210576, by rfl⟩ : syracuseStep 8561537 = 6421153) B6421153
theorem B15418441 : Blo 1502071 15418441 := bstep (se 2 (by rfl) ⟨5781915, by rfl⟩ : syracuseStep 15418441 = 11563831) B11563831
theorem B2853139 : Blo 1502071 2853139 := bstep (se 1 (by rfl) ⟨2139854, by rfl⟩ : syracuseStep 2853139 = 4279709) B4279709
theorem B7604927 : Blo 1502071 7604927 := bstep (se 1 (by rfl) ⟨5703695, by rfl⟩ : syracuseStep 7604927 = 11407391) B11407391
theorem B146279135 : Blo 1502071 146279135 := bstep (se 1 (by rfl) ⟨109709351, by rfl⟩ : syracuseStep 146279135 = 219418703) B219418703
theorem B1502299 : Blo 1502071 1502299 := bstep (se 1 (by rfl) ⟨1126724, by rfl⟩ : syracuseStep 1502299 = 2253449) B2253449
theorem B1502567 : Blo 1502071 1502567 := bstep (se 1 (by rfl) ⟨1126925, by rfl⟩ : syracuseStep 1502567 = 2253851) B2253851
theorem B4812443 : Blo 1502071 4812443 := bstep (se 1 (by rfl) ⟨3609332, by rfl⟩ : syracuseStep 4812443 = 7218665) B7218665
theorem B17109629 : Blo 1502071 17109629 := bstep (se 3 (by rfl) ⟨3208055, by rfl⟩ : syracuseStep 17109629 = 6416111) B6416111
theorem B4879079 : Blo 1502071 4879079 := bstep (se 1 (by rfl) ⟨3659309, by rfl⟩ : syracuseStep 4879079 = 7318619) B7318619
theorem B3380489 : Blo 1502071 3380489 := bstep (se 2 (by rfl) ⟨1267683, by rfl⟩ : syracuseStep 3380489 = 2535367) B2535367
theorem B19780955 : Blo 1502071 19780955 := bstep (se 1 (by rfl) ⟨14835716, by rfl⟩ : syracuseStep 19780955 = 29671433) B29671433
theorem B3380687 : Blo 1502071 3380687 := bstep (se 1 (by rfl) ⟨2535515, by rfl⟩ : syracuseStep 3380687 = 5071031) B5071031
theorem B12834409 : Blo 1502071 12834409 := bstep (se 2 (by rfl) ⟨4812903, by rfl⟩ : syracuseStep 12834409 = 9625807) B9625807
theorem B37582501 : Blo 1502071 37582501 := bstep (se 4 (by rfl) ⟨3523359, by rfl⟩ : syracuseStep 37582501 = 7046719) B7046719
theorem B3381929 : Blo 1502071 3381929 := bstep (se 2 (by rfl) ⟨1268223, by rfl⟩ : syracuseStep 3381929 = 2536447) B2536447
theorem B4816007 : Blo 1502071 4816007 := bstep (se 1 (by rfl) ⟨3612005, by rfl⟩ : syracuseStep 4816007 = 7224011) B7224011
theorem B10837223 : Blo 1502071 10837223 := bstep (se 1 (by rfl) ⟨8127917, by rfl⟩ : syracuseStep 10837223 = 16255835) B16255835
theorem B18529631 : Blo 1502071 18529631 := bstep (se 1 (by rfl) ⟨13897223, by rfl⟩ : syracuseStep 18529631 = 27794447) B27794447
theorem B11567225 : Blo 1502071 11567225 := bstep (se 2 (by rfl) ⟨4337709, by rfl⟩ : syracuseStep 11567225 = 8675419) B8675419
theorem B3252719 : Blo 1502071 3252719 := bstep (se 1 (by rfl) ⟨2439539, by rfl⟩ : syracuseStep 3252719 = 4879079) B4879079
theorem B2253659 : Blo 1502071 2253659 := bstep (se 1 (by rfl) ⟨1690244, by rfl⟩ : syracuseStep 2253659 = 3380489) B3380489
theorem B2253791 : Blo 1502071 2253791 := bstep (se 1 (by rfl) ⟨1690343, by rfl⟩ : syracuseStep 2253791 = 3380687) B3380687
theorem B2254619 : Blo 1502071 2254619 := bstep (se 1 (by rfl) ⟨1690964, by rfl⟩ : syracuseStep 2254619 = 3381929) B3381929
theorem B97519423 : Blo 1502071 97519423 := bstep (se 1 (by rfl) ⟨73139567, by rfl⟩ : syracuseStep 97519423 = 146279135) B146279135
theorem B3804185 : Blo 1502071 3804185 := bstep (se 2 (by rfl) ⟨1426569, by rfl⟩ : syracuseStep 3804185 = 2853139) B2853139
theorem B1502239 : Blo 1502071 1502239 := bstep (se 1 (by rfl) ⟨1126679, by rfl⟩ : syracuseStep 1502239 = 2253359) B2253359
theorem B11406419 : Blo 1502071 11406419 := bstep (se 1 (by rfl) ⟨8554814, by rfl⟩ : syracuseStep 11406419 = 17109629) B17109629
theorem B20557921 : Blo 1502071 20557921 := bstep (se 2 (by rfl) ⟨7709220, by rfl⟩ : syracuseStep 20557921 = 15418441) B15418441
theorem B3208295 : Blo 1502071 3208295 := bstep (se 1 (by rfl) ⟨2406221, by rfl⟩ : syracuseStep 3208295 = 4812443) B4812443
theorem B5707691 : Blo 1502071 5707691 := bstep (se 1 (by rfl) ⟨4280768, by rfl⟩ : syracuseStep 5707691 = 8561537) B8561537
theorem B13187303 : Blo 1502071 13187303 := bstep (se 1 (by rfl) ⟨9890477, by rfl⟩ : syracuseStep 13187303 = 19780955) B19780955
theorem B5069951 : Blo 1502071 5069951 := bstep (se 1 (by rfl) ⟨3802463, by rfl⟩ : syracuseStep 5069951 = 7604927) B7604927
theorem B3210671 : Blo 1502071 3210671 := bstep (se 1 (by rfl) ⟨2408003, by rfl⟩ : syracuseStep 3210671 = 4816007) B4816007
theorem B17112545 : Blo 1502071 17112545 := bstep (se 2 (by rfl) ⟨6417204, by rfl⟩ : syracuseStep 17112545 = 12834409) B12834409
theorem B7224815 : Blo 1502071 7224815 := bstep (se 1 (by rfl) ⟨5418611, by rfl⟩ : syracuseStep 7224815 = 10837223) B10837223
theorem B50110001 : Blo 1502071 50110001 := bstep (se 2 (by rfl) ⟨18791250, by rfl⟩ : syracuseStep 50110001 = 37582501) B37582501
theorem B12353087 : Blo 1502071 12353087 := bstep (se 1 (by rfl) ⟨9264815, by rfl⟩ : syracuseStep 12353087 = 18529631) B18529631
theorem B27410561 : Blo 1502071 27410561 := bstep (se 2 (by rfl) ⟨10278960, by rfl⟩ : syracuseStep 27410561 = 20557921) B20557921
theorem B8791535 : Blo 1502071 8791535 := bstep (se 1 (by rfl) ⟨6593651, by rfl⟩ : syracuseStep 8791535 = 13187303) B13187303
theorem B7604279 : Blo 1502071 7604279 := bstep (se 1 (by rfl) ⟨5703209, by rfl⟩ : syracuseStep 7604279 = 11406419) B11406419
theorem B2140447 : Blo 1502071 2140447 := bstep (se 1 (by rfl) ⟨1605335, by rfl⟩ : syracuseStep 2140447 = 3210671) B3210671
theorem B8235391 : Blo 1502071 8235391 := bstep (se 1 (by rfl) ⟨6176543, by rfl⟩ : syracuseStep 8235391 = 12353087) B12353087
theorem B130025897 : Blo 1502071 130025897 := bstep (se 2 (by rfl) ⟨48759711, by rfl⟩ : syracuseStep 130025897 = 97519423) B97519423
theorem B7711483 : Blo 1502071 7711483 := bstep (se 1 (by rfl) ⟨5783612, by rfl⟩ : syracuseStep 7711483 = 11567225) B11567225
theorem B8555453 : Blo 1502071 8555453 := bstep (se 3 (by rfl) ⟨1604147, by rfl⟩ : syracuseStep 8555453 = 3208295) B3208295
theorem B1502439 : Blo 1502071 1502439 := bstep (se 1 (by rfl) ⟨1126829, by rfl⟩ : syracuseStep 1502439 = 2253659) B2253659
theorem B1502527 : Blo 1502071 1502527 := bstep (se 1 (by rfl) ⟨1126895, by rfl⟩ : syracuseStep 1502527 = 2253791) B2253791
theorem B1503079 : Blo 1502071 1503079 := bstep (se 1 (by rfl) ⟨1127309, by rfl⟩ : syracuseStep 1503079 = 2254619) B2254619
theorem B3805127 : Blo 1502071 3805127 := bstep (se 1 (by rfl) ⟨2853845, by rfl⟩ : syracuseStep 3805127 = 5707691) B5707691
theorem B2536123 : Blo 1502071 2536123 := bstep (se 1 (by rfl) ⟨1902092, by rfl⟩ : syracuseStep 2536123 = 3804185) B3804185
theorem B3379967 : Blo 1502071 3379967 := bstep (se 1 (by rfl) ⟨2534975, by rfl⟩ : syracuseStep 3379967 = 5069951) B5069951
theorem B11408363 : Blo 1502071 11408363 := bstep (se 1 (by rfl) ⟨8556272, by rfl⟩ : syracuseStep 11408363 = 17112545) B17112545
theorem B2168479 : Blo 1502071 2168479 := bstep (se 1 (by rfl) ⟨1626359, by rfl⟩ : syracuseStep 2168479 = 3252719) B3252719
theorem B19266173 : Blo 1502071 19266173 := bstep (se 3 (by rfl) ⟨3612407, by rfl⟩ : syracuseStep 19266173 = 7224815) B7224815
theorem B33406667 : Blo 1502071 33406667 := bstep (se 1 (by rfl) ⟨25055000, by rfl⟩ : syracuseStep 33406667 = 50110001) B50110001
theorem B2253311 : Blo 1502071 2253311 := bstep (se 1 (by rfl) ⟨1689983, by rfl⟩ : syracuseStep 2253311 = 3379967) B3379967
theorem B10281977 : Blo 1502071 10281977 := bstep (se 2 (by rfl) ⟨3855741, by rfl⟩ : syracuseStep 10281977 = 7711483) B7711483
theorem B5703635 : Blo 1502071 5703635 := bstep (se 1 (by rfl) ⟨4277726, by rfl⟩ : syracuseStep 5703635 = 8555453) B8555453
theorem B2853929 : Blo 1502071 2853929 := bstep (se 2 (by rfl) ⟨1070223, by rfl⟩ : syracuseStep 2853929 = 2140447) B2140447
theorem B10980521 : Blo 1502071 10980521 := bstep (se 2 (by rfl) ⟨4117695, by rfl⟩ : syracuseStep 10980521 = 8235391) B8235391
theorem B7605575 : Blo 1502071 7605575 := bstep (se 1 (by rfl) ⟨5704181, by rfl⟩ : syracuseStep 7605575 = 11408363) B11408363
theorem B86683931 : Blo 1502071 86683931 := bstep (se 1 (by rfl) ⟨65012948, by rfl⟩ : syracuseStep 86683931 = 130025897) B130025897
theorem B22271111 : Blo 1502071 22271111 := bstep (se 1 (by rfl) ⟨16703333, by rfl⟩ : syracuseStep 22271111 = 33406667) B33406667
theorem B2536751 : Blo 1502071 2536751 := bstep (se 1 (by rfl) ⟨1902563, by rfl⟩ : syracuseStep 2536751 = 3805127) B3805127
theorem B18273707 : Blo 1502071 18273707 := bstep (se 1 (by rfl) ⟨13705280, by rfl⟩ : syracuseStep 18273707 = 27410561) B27410561
theorem B3381497 : Blo 1502071 3381497 := bstep (se 2 (by rfl) ⟨1268061, by rfl⟩ : syracuseStep 3381497 = 2536123) B2536123
theorem B23444093 : Blo 1502071 23444093 := bstep (se 3 (by rfl) ⟨4395767, by rfl⟩ : syracuseStep 23444093 = 8791535) B8791535
theorem B5069519 : Blo 1502071 5069519 := bstep (se 1 (by rfl) ⟨3802139, by rfl⟩ : syracuseStep 5069519 = 7604279) B7604279
theorem B12844115 : Blo 1502071 12844115 := bstep (se 1 (by rfl) ⟨9633086, by rfl⟩ : syracuseStep 12844115 = 19266173) B19266173
theorem B2891305 : Blo 1502071 2891305 := bstep (se 2 (by rfl) ⟨1084239, by rfl⟩ : syracuseStep 2891305 = 2168479) B2168479
theorem B12182471 : Blo 1502071 12182471 := bstep (se 1 (by rfl) ⟨9136853, by rfl⟩ : syracuseStep 12182471 = 18273707) B18273707
theorem B3802423 : Blo 1502071 3802423 := bstep (se 1 (by rfl) ⟨2851817, by rfl⟩ : syracuseStep 3802423 = 5703635) B5703635
theorem B2254331 : Blo 1502071 2254331 := bstep (se 1 (by rfl) ⟨1690748, by rfl⟩ : syracuseStep 2254331 = 3381497) B3381497
theorem B1902619 : Blo 1502071 1902619 := bstep (se 1 (by rfl) ⟨1426964, by rfl⟩ : syracuseStep 1902619 = 2853929) B2853929
theorem B8562743 : Blo 1502071 8562743 := bstep (se 1 (by rfl) ⟨6422057, by rfl⟩ : syracuseStep 8562743 = 12844115) B12844115
theorem B57789287 : Blo 1502071 57789287 := bstep (se 1 (by rfl) ⟨43341965, by rfl⟩ : syracuseStep 57789287 = 86683931) B86683931
theorem B15420293 : Blo 1502071 15420293 := bstep (se 4 (by rfl) ⟨1445652, by rfl⟩ : syracuseStep 15420293 = 2891305) B2891305
theorem B1502207 : Blo 1502071 1502207 := bstep (se 1 (by rfl) ⟨1126655, by rfl⟩ : syracuseStep 1502207 = 2253311) B2253311
theorem B14847407 : Blo 1502071 14847407 := bstep (se 1 (by rfl) ⟨11135555, by rfl⟩ : syracuseStep 14847407 = 22271111) B22271111
theorem B1691167 : Blo 1502071 1691167 := bstep (se 1 (by rfl) ⟨1268375, by rfl⟩ : syracuseStep 1691167 = 2536751) B2536751
theorem B3379679 : Blo 1502071 3379679 := bstep (se 1 (by rfl) ⟨2534759, by rfl⟩ : syracuseStep 3379679 = 5069519) B5069519
theorem B7320347 : Blo 1502071 7320347 := bstep (se 1 (by rfl) ⟨5490260, by rfl⟩ : syracuseStep 7320347 = 10980521) B10980521
theorem B6854651 : Blo 1502071 6854651 := bstep (se 1 (by rfl) ⟨5140988, by rfl⟩ : syracuseStep 6854651 = 10281977) B10281977
theorem B15629395 : Blo 1502071 15629395 := bstep (se 1 (by rfl) ⟨11722046, by rfl⟩ : syracuseStep 15629395 = 23444093) B23444093
theorem B5070383 : Blo 1502071 5070383 := bstep (se 1 (by rfl) ⟨3802787, by rfl⟩ : syracuseStep 5070383 = 7605575) B7605575
theorem B2253119 : Blo 1502071 2253119 := bstep (se 1 (by rfl) ⟨1689839, by rfl⟩ : syracuseStep 2253119 = 3379679) B3379679
theorem B2254889 : Blo 1502071 2254889 := bstep (se 2 (by rfl) ⟨845583, by rfl⟩ : syracuseStep 2254889 = 1691167) B1691167
theorem B9898271 : Blo 1502071 9898271 := bstep (se 1 (by rfl) ⟨7423703, by rfl⟩ : syracuseStep 9898271 = 14847407) B14847407
theorem B8121647 : Blo 1502071 8121647 := bstep (se 1 (by rfl) ⟨6091235, by rfl⟩ : syracuseStep 8121647 = 12182471) B12182471
theorem B1502887 : Blo 1502071 1502887 := bstep (se 1 (by rfl) ⟨1127165, by rfl⟩ : syracuseStep 1502887 = 2254331) B2254331
theorem B3380255 : Blo 1502071 3380255 := bstep (se 1 (by rfl) ⟨2535191, by rfl⟩ : syracuseStep 3380255 = 5070383) B5070383
theorem B2536825 : Blo 1502071 2536825 := bstep (se 2 (by rfl) ⟨951309, by rfl⟩ : syracuseStep 2536825 = 1902619) B1902619
theorem B4880231 : Blo 1502071 4880231 := bstep (se 1 (by rfl) ⟨3660173, by rfl⟩ : syracuseStep 4880231 = 7320347) B7320347
theorem B4569767 : Blo 1502071 4569767 := bstep (se 1 (by rfl) ⟨3427325, by rfl⟩ : syracuseStep 4569767 = 6854651) B6854651
theorem B5708495 : Blo 1502071 5708495 := bstep (se 1 (by rfl) ⟨4281371, by rfl⟩ : syracuseStep 5708495 = 8562743) B8562743
theorem B20839193 : Blo 1502071 20839193 := bstep (se 2 (by rfl) ⟨7814697, by rfl⟩ : syracuseStep 20839193 = 15629395) B15629395
theorem B5069897 : Blo 1502071 5069897 := bstep (se 2 (by rfl) ⟨1901211, by rfl⟩ : syracuseStep 5069897 = 3802423) B3802423
theorem B38526191 : Blo 1502071 38526191 := bstep (se 1 (by rfl) ⟨28894643, by rfl⟩ : syracuseStep 38526191 = 57789287) B57789287
theorem B10280195 : Blo 1502071 10280195 := bstep (se 1 (by rfl) ⟨7710146, by rfl⟩ : syracuseStep 10280195 = 15420293) B15420293
theorem B2253503 : Blo 1502071 2253503 := bstep (se 1 (by rfl) ⟨1690127, by rfl⟩ : syracuseStep 2253503 = 3380255) B3380255
theorem B3253487 : Blo 1502071 3253487 := bstep (se 1 (by rfl) ⟨2440115, by rfl⟩ : syracuseStep 3253487 = 4880231) B4880231
theorem B25684127 : Blo 1502071 25684127 := bstep (se 1 (by rfl) ⟨19263095, by rfl⟩ : syracuseStep 25684127 = 38526191) B38526191
theorem B1502079 : Blo 1502071 1502079 := bstep (se 1 (by rfl) ⟨1126559, by rfl⟩ : syracuseStep 1502079 = 2253119) B2253119
theorem B1503259 : Blo 1502071 1503259 := bstep (se 1 (by rfl) ⟨1127444, by rfl⟩ : syracuseStep 1503259 = 2254889) B2254889
theorem B6598847 : Blo 1502071 6598847 := bstep (se 1 (by rfl) ⟨4949135, by rfl⟩ : syracuseStep 6598847 = 9898271) B9898271
theorem B3805663 : Blo 1502071 3805663 := bstep (se 1 (by rfl) ⟨2854247, by rfl⟩ : syracuseStep 3805663 = 5708495) B5708495
theorem B3379931 : Blo 1502071 3379931 := bstep (se 1 (by rfl) ⟨2534948, by rfl⟩ : syracuseStep 3379931 = 5069897) B5069897
theorem B6853463 : Blo 1502071 6853463 := bstep (se 1 (by rfl) ⟨5140097, by rfl⟩ : syracuseStep 6853463 = 10280195) B10280195
theorem B21657725 : Blo 1502071 21657725 := bstep (se 3 (by rfl) ⟨4060823, by rfl⟩ : syracuseStep 21657725 = 8121647) B8121647
theorem B3046511 : Blo 1502071 3046511 := bstep (se 1 (by rfl) ⟨2284883, by rfl⟩ : syracuseStep 3046511 = 4569767) B4569767
theorem B3382433 : Blo 1502071 3382433 := bstep (se 2 (by rfl) ⟨1268412, by rfl⟩ : syracuseStep 3382433 = 2536825) B2536825
theorem B13892795 : Blo 1502071 13892795 := bstep (se 1 (by rfl) ⟨10419596, by rfl⟩ : syracuseStep 13892795 = 20839193) B20839193
theorem B4399231 : Blo 1502071 4399231 := bstep (se 1 (by rfl) ⟨3299423, by rfl⟩ : syracuseStep 4399231 = 6598847) B6598847
theorem B2253287 : Blo 1502071 2253287 := bstep (se 1 (by rfl) ⟨1689965, by rfl⟩ : syracuseStep 2253287 = 3379931) B3379931
theorem B8675965 : Blo 1502071 8675965 := bstep (se 3 (by rfl) ⟨1626743, by rfl⟩ : syracuseStep 8675965 = 3253487) B3253487
theorem B17122751 : Blo 1502071 17122751 := bstep (se 1 (by rfl) ⟨12842063, by rfl⟩ : syracuseStep 17122751 = 25684127) B25684127
theorem B2254955 : Blo 1502071 2254955 := bstep (se 1 (by rfl) ⟨1691216, by rfl⟩ : syracuseStep 2254955 = 3382433) B3382433
theorem B1502335 : Blo 1502071 1502335 := bstep (se 1 (by rfl) ⟨1126751, by rfl⟩ : syracuseStep 1502335 = 2253503) B2253503
theorem B5074217 : Blo 1502071 5074217 := bstep (se 2 (by rfl) ⟨1902831, by rfl⟩ : syracuseStep 5074217 = 3805663) B3805663
theorem B14438483 : Blo 1502071 14438483 := bstep (se 1 (by rfl) ⟨10828862, by rfl⟩ : syracuseStep 14438483 = 21657725) B21657725
theorem B9261863 : Blo 1502071 9261863 := bstep (se 1 (by rfl) ⟨6946397, by rfl⟩ : syracuseStep 9261863 = 13892795) B13892795
theorem B4568975 : Blo 1502071 4568975 := bstep (se 1 (by rfl) ⟨3426731, by rfl⟩ : syracuseStep 4568975 = 6853463) B6853463
theorem B2031007 : Blo 1502071 2031007 := bstep (se 1 (by rfl) ⟨1523255, by rfl⟩ : syracuseStep 2031007 = 3046511) B3046511
theorem B9625655 : Blo 1502071 9625655 := bstep (se 1 (by rfl) ⟨7219241, by rfl⟩ : syracuseStep 9625655 = 14438483) B14438483
theorem B5865641 : Blo 1502071 5865641 := bstep (se 2 (by rfl) ⟨2199615, by rfl⟩ : syracuseStep 5865641 = 4399231) B4399231
theorem B11567953 : Blo 1502071 11567953 := bstep (se 2 (by rfl) ⟨4337982, by rfl⟩ : syracuseStep 11567953 = 8675965) B8675965
theorem B1502191 : Blo 1502071 1502191 := bstep (se 1 (by rfl) ⟨1126643, by rfl⟩ : syracuseStep 1502191 = 2253287) B2253287
theorem B11415167 : Blo 1502071 11415167 := bstep (se 1 (by rfl) ⟨8561375, by rfl⟩ : syracuseStep 11415167 = 17122751) B17122751
theorem B1503303 : Blo 1502071 1503303 := bstep (se 1 (by rfl) ⟨1127477, by rfl⟩ : syracuseStep 1503303 = 2254955) B2254955
theorem B2708009 : Blo 1502071 2708009 := bstep (se 2 (by rfl) ⟨1015503, by rfl⟩ : syracuseStep 2708009 = 2031007) B2031007
theorem B6174575 : Blo 1502071 6174575 := bstep (se 1 (by rfl) ⟨4630931, by rfl⟩ : syracuseStep 6174575 = 9261863) B9261863
theorem B3045983 : Blo 1502071 3045983 := bstep (se 1 (by rfl) ⟨2284487, by rfl⟩ : syracuseStep 3045983 = 4568975) B4568975
theorem B3382811 : Blo 1502071 3382811 := bstep (se 1 (by rfl) ⟨2537108, by rfl⟩ : syracuseStep 3382811 = 5074217) B5074217
theorem B61695749 : Blo 1502071 61695749 := bstep (se 4 (by rfl) ⟨5783976, by rfl⟩ : syracuseStep 61695749 = 11567953) B11567953
theorem B2255207 : Blo 1502071 2255207 := bstep (se 1 (by rfl) ⟨1691405, by rfl⟩ : syracuseStep 2255207 = 3382811) B3382811
theorem B6417103 : Blo 1502071 6417103 := bstep (se 1 (by rfl) ⟨4812827, by rfl⟩ : syracuseStep 6417103 = 9625655) B9625655
theorem B3910427 : Blo 1502071 3910427 := bstep (se 1 (by rfl) ⟨2932820, by rfl⟩ : syracuseStep 3910427 = 5865641) B5865641
theorem B1805339 : Blo 1502071 1805339 := bstep (se 1 (by rfl) ⟨1354004, by rfl⟩ : syracuseStep 1805339 = 2708009) B2708009
theorem B4116383 : Blo 1502071 4116383 := bstep (se 1 (by rfl) ⟨3087287, by rfl⟩ : syracuseStep 4116383 = 6174575) B6174575
theorem B8122621 : Blo 1502071 8122621 := bstep (se 3 (by rfl) ⟨1522991, by rfl⟩ : syracuseStep 8122621 = 3045983) B3045983
theorem B7610111 : Blo 1502071 7610111 := bstep (se 1 (by rfl) ⟨5707583, by rfl⟩ : syracuseStep 7610111 = 11415167) B11415167
theorem B10830161 : Blo 1502071 10830161 := bstep (se 2 (by rfl) ⟨4061310, by rfl⟩ : syracuseStep 10830161 = 8122621) B8122621
theorem B2606951 : Blo 1502071 2606951 := bstep (se 1 (by rfl) ⟨1955213, by rfl⟩ : syracuseStep 2606951 = 3910427) B3910427
theorem B5073407 : Blo 1502071 5073407 := bstep (se 1 (by rfl) ⟨3805055, by rfl⟩ : syracuseStep 5073407 = 7610111) B7610111
theorem B8556137 : Blo 1502071 8556137 := bstep (se 2 (by rfl) ⟨3208551, by rfl⟩ : syracuseStep 8556137 = 6417103) B6417103
theorem B1503471 : Blo 1502071 1503471 := bstep (se 1 (by rfl) ⟨1127603, by rfl⟩ : syracuseStep 1503471 = 2255207) B2255207
theorem B4814237 : Blo 1502071 4814237 := bstep (se 3 (by rfl) ⟨902669, by rfl⟩ : syracuseStep 4814237 = 1805339) B1805339
theorem B41130499 : Blo 1502071 41130499 := bstep (se 1 (by rfl) ⟨30847874, by rfl⟩ : syracuseStep 41130499 = 61695749) B61695749
theorem B2744255 : Blo 1502071 2744255 := bstep (se 1 (by rfl) ⟨2058191, by rfl⟩ : syracuseStep 2744255 = 4116383) B4116383
theorem B1737967 : Blo 1502071 1737967 := bstep (se 1 (by rfl) ⟨1303475, by rfl⟩ : syracuseStep 1737967 = 2606951) B2606951
theorem B5704091 : Blo 1502071 5704091 := bstep (se 1 (by rfl) ⟨4278068, by rfl⟩ : syracuseStep 5704091 = 8556137) B8556137
theorem B1829503 : Blo 1502071 1829503 := bstep (se 1 (by rfl) ⟨1372127, by rfl⟩ : syracuseStep 1829503 = 2744255) B2744255
theorem B7220107 : Blo 1502071 7220107 := bstep (se 1 (by rfl) ⟨5415080, by rfl⟩ : syracuseStep 7220107 = 10830161) B10830161
theorem B54840665 : Blo 1502071 54840665 := bstep (se 2 (by rfl) ⟨20565249, by rfl⟩ : syracuseStep 54840665 = 41130499) B41130499
theorem B3209491 : Blo 1502071 3209491 := bstep (se 1 (by rfl) ⟨2407118, by rfl⟩ : syracuseStep 3209491 = 4814237) B4814237
theorem B3382271 : Blo 1502071 3382271 := bstep (se 1 (by rfl) ⟨2536703, by rfl⟩ : syracuseStep 3382271 = 5073407) B5073407
theorem B9626809 : Blo 1502071 9626809 := bstep (se 2 (by rfl) ⟨3610053, by rfl⟩ : syracuseStep 9626809 = 7220107) B7220107
theorem B3802727 : Blo 1502071 3802727 := bstep (se 1 (by rfl) ⟨2852045, by rfl⟩ : syracuseStep 3802727 = 5704091) B5704091
theorem B2254847 : Blo 1502071 2254847 := bstep (se 1 (by rfl) ⟨1691135, by rfl⟩ : syracuseStep 2254847 = 3382271) B3382271
theorem B4279321 : Blo 1502071 4279321 := bstep (se 2 (by rfl) ⟨1604745, by rfl⟩ : syracuseStep 4279321 = 3209491) B3209491
theorem B2439337 : Blo 1502071 2439337 := bstep (se 2 (by rfl) ⟨914751, by rfl⟩ : syracuseStep 2439337 = 1829503) B1829503
theorem B146241773 : Blo 1502071 146241773 := bstep (se 3 (by rfl) ⟨27420332, by rfl⟩ : syracuseStep 146241773 = 54840665) B54840665
theorem B2317289 : Blo 1502071 2317289 := bstep (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) B1737967
theorem B3252449 : Blo 1502071 3252449 := bstep (se 2 (by rfl) ⟨1219668, by rfl⟩ : syracuseStep 3252449 = 2439337) B2439337
theorem B97494515 : Blo 1502071 97494515 := bstep (se 1 (by rfl) ⟨73120886, by rfl⟩ : syracuseStep 97494515 = 146241773) B146241773
theorem B6179437 : Blo 1502071 6179437 := bstep (se 3 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 6179437 = 2317289) B2317289
theorem B2535151 : Blo 1502071 2535151 := bstep (se 1 (by rfl) ⟨1901363, by rfl⟩ : syracuseStep 2535151 = 3802727) B3802727
theorem B1503231 : Blo 1502071 1503231 := bstep (se 1 (by rfl) ⟨1127423, by rfl⟩ : syracuseStep 1503231 = 2254847) B2254847
theorem B5705761 : Blo 1502071 5705761 := bstep (se 2 (by rfl) ⟨2139660, by rfl⟩ : syracuseStep 5705761 = 4279321) B4279321
theorem B12835745 : Blo 1502071 12835745 := bstep (se 2 (by rfl) ⟨4813404, by rfl⟩ : syracuseStep 12835745 = 9626809) B9626809
theorem B64996343 : Blo 1502071 64996343 := bstep (se 1 (by rfl) ⟨48747257, by rfl⟩ : syracuseStep 64996343 = 97494515) B97494515
theorem B8557163 : Blo 1502071 8557163 := bstep (se 1 (by rfl) ⟨6417872, by rfl⟩ : syracuseStep 8557163 = 12835745) B12835745
theorem B3380201 : Blo 1502071 3380201 := bstep (se 2 (by rfl) ⟨1267575, by rfl⟩ : syracuseStep 3380201 = 2535151) B2535151
theorem B7607681 : Blo 1502071 7607681 := bstep (se 2 (by rfl) ⟨2852880, by rfl⟩ : syracuseStep 7607681 = 5705761) B5705761
theorem B2168299 : Blo 1502071 2168299 := bstep (se 1 (by rfl) ⟨1626224, by rfl⟩ : syracuseStep 2168299 = 3252449) B3252449
theorem B8239249 : Blo 1502071 8239249 := bstep (se 2 (by rfl) ⟨3089718, by rfl⟩ : syracuseStep 8239249 = 6179437) B6179437
theorem B2253467 : Blo 1502071 2253467 := bstep (se 1 (by rfl) ⟨1690100, by rfl⟩ : syracuseStep 2253467 = 3380201) B3380201
theorem B43942661 : Blo 1502071 43942661 := bstep (se 4 (by rfl) ⟨4119624, by rfl⟩ : syracuseStep 43942661 = 8239249) B8239249
theorem B5071787 : Blo 1502071 5071787 := bstep (se 1 (by rfl) ⟨3803840, by rfl⟩ : syracuseStep 5071787 = 7607681) B7607681
theorem B5704775 : Blo 1502071 5704775 := bstep (se 1 (by rfl) ⟨4278581, by rfl⟩ : syracuseStep 5704775 = 8557163) B8557163
theorem B43330895 : Blo 1502071 43330895 := bstep (se 1 (by rfl) ⟨32498171, by rfl⟩ : syracuseStep 43330895 = 64996343) B64996343
theorem B11564261 : Blo 1502071 11564261 := bstep (se 4 (by rfl) ⟨1084149, by rfl⟩ : syracuseStep 11564261 = 2168299) B2168299
theorem B29295107 : Blo 1502071 29295107 := bstep (se 1 (by rfl) ⟨21971330, by rfl⟩ : syracuseStep 29295107 = 43942661) B43942661
theorem B7709507 : Blo 1502071 7709507 := bstep (se 1 (by rfl) ⟨5782130, by rfl⟩ : syracuseStep 7709507 = 11564261) B11564261
theorem B3803183 : Blo 1502071 3803183 := bstep (se 1 (by rfl) ⟨2852387, by rfl⟩ : syracuseStep 3803183 = 5704775) B5704775
theorem B28887263 : Blo 1502071 28887263 := bstep (se 1 (by rfl) ⟨21665447, by rfl⟩ : syracuseStep 28887263 = 43330895) B43330895
theorem B1502311 : Blo 1502071 1502311 := bstep (se 1 (by rfl) ⟨1126733, by rfl⟩ : syracuseStep 1502311 = 2253467) B2253467
theorem B3381191 : Blo 1502071 3381191 := bstep (se 1 (by rfl) ⟨2535893, by rfl⟩ : syracuseStep 3381191 = 5071787) B5071787
theorem B19530071 : Blo 1502071 19530071 := bstep (se 1 (by rfl) ⟨14647553, by rfl⟩ : syracuseStep 19530071 = 29295107) B29295107
theorem B2254127 : Blo 1502071 2254127 := bstep (se 1 (by rfl) ⟨1690595, by rfl⟩ : syracuseStep 2254127 = 3381191) B3381191
theorem B5139671 : Blo 1502071 5139671 := bstep (se 1 (by rfl) ⟨3854753, by rfl⟩ : syracuseStep 5139671 = 7709507) B7709507
theorem B2535455 : Blo 1502071 2535455 := bstep (se 1 (by rfl) ⟨1901591, by rfl⟩ : syracuseStep 2535455 = 3803183) B3803183
theorem B19258175 : Blo 1502071 19258175 := bstep (se 1 (by rfl) ⟨14443631, by rfl⟩ : syracuseStep 19258175 = 28887263) B28887263
theorem B13705789 : Blo 1502071 13705789 := bstep (se 3 (by rfl) ⟨2569835, by rfl⟩ : syracuseStep 13705789 = 5139671) B5139671
theorem B12838783 : Blo 1502071 12838783 := bstep (se 1 (by rfl) ⟨9629087, by rfl⟩ : syracuseStep 12838783 = 19258175) B19258175
theorem B1690303 : Blo 1502071 1690303 := bstep (se 1 (by rfl) ⟨1267727, by rfl⟩ : syracuseStep 1690303 = 2535455) B2535455
theorem B13020047 : Blo 1502071 13020047 := bstep (se 1 (by rfl) ⟨9765035, by rfl⟩ : syracuseStep 13020047 = 19530071) B19530071
theorem B1502751 : Blo 1502071 1502751 := bstep (se 1 (by rfl) ⟨1127063, by rfl⟩ : syracuseStep 1502751 = 2254127) B2254127
theorem B2253737 : Blo 1502071 2253737 := bstep (se 2 (by rfl) ⟨845151, by rfl⟩ : syracuseStep 2253737 = 1690303) B1690303
theorem B8680031 : Blo 1502071 8680031 := bstep (se 1 (by rfl) ⟨6510023, by rfl⟩ : syracuseStep 8680031 = 13020047) B13020047
theorem B17118377 : Blo 1502071 17118377 := bstep (se 2 (by rfl) ⟨6419391, by rfl⟩ : syracuseStep 17118377 = 12838783) B12838783
theorem B18274385 : Blo 1502071 18274385 := bstep (se 2 (by rfl) ⟨6852894, by rfl⟩ : syracuseStep 18274385 = 13705789) B13705789
theorem B11412251 : Blo 1502071 11412251 := bstep (se 1 (by rfl) ⟨8559188, by rfl⟩ : syracuseStep 11412251 = 17118377) B17118377
theorem B12182923 : Blo 1502071 12182923 := bstep (se 1 (by rfl) ⟨9137192, by rfl⟩ : syracuseStep 12182923 = 18274385) B18274385
theorem B5786687 : Blo 1502071 5786687 := bstep (se 1 (by rfl) ⟨4340015, by rfl⟩ : syracuseStep 5786687 = 8680031) B8680031
theorem B1502491 : Blo 1502071 1502491 := bstep (se 1 (by rfl) ⟨1126868, by rfl⟩ : syracuseStep 1502491 = 2253737) B2253737
theorem B15431165 : Blo 1502071 15431165 := bstep (se 3 (by rfl) ⟨2893343, by rfl⟩ : syracuseStep 15431165 = 5786687) B5786687
theorem B7608167 : Blo 1502071 7608167 := bstep (se 1 (by rfl) ⟨5706125, by rfl⟩ : syracuseStep 7608167 = 11412251) B11412251
theorem B16243897 : Blo 1502071 16243897 := bstep (se 2 (by rfl) ⟨6091461, by rfl⟩ : syracuseStep 16243897 = 12182923) B12182923
theorem B5072111 : Blo 1502071 5072111 := bstep (se 1 (by rfl) ⟨3804083, by rfl⟩ : syracuseStep 5072111 = 7608167) B7608167
theorem B10287443 : Blo 1502071 10287443 := bstep (se 1 (by rfl) ⟨7715582, by rfl⟩ : syracuseStep 10287443 = 15431165) B15431165
theorem B21658529 : Blo 1502071 21658529 := bstep (se 2 (by rfl) ⟨8121948, by rfl⟩ : syracuseStep 21658529 = 16243897) B16243897
theorem B14439019 : Blo 1502071 14439019 := bstep (se 1 (by rfl) ⟨10829264, by rfl⟩ : syracuseStep 14439019 = 21658529) B21658529
theorem B3381407 : Blo 1502071 3381407 := bstep (se 1 (by rfl) ⟨2536055, by rfl⟩ : syracuseStep 3381407 = 5072111) B5072111
theorem B27433181 : Blo 1502071 27433181 := bstep (se 3 (by rfl) ⟨5143721, by rfl⟩ : syracuseStep 27433181 = 10287443) B10287443
theorem B73155149 : Blo 1502071 73155149 := bstep (se 3 (by rfl) ⟨13716590, by rfl⟩ : syracuseStep 73155149 = 27433181) B27433181
theorem B19252025 : Blo 1502071 19252025 := bstep (se 2 (by rfl) ⟨7219509, by rfl⟩ : syracuseStep 19252025 = 14439019) B14439019
theorem B2254271 : Blo 1502071 2254271 := bstep (se 1 (by rfl) ⟨1690703, by rfl⟩ : syracuseStep 2254271 = 3381407) B3381407
theorem B48770099 : Blo 1502071 48770099 := bstep (se 1 (by rfl) ⟨36577574, by rfl⟩ : syracuseStep 48770099 = 73155149) B73155149
theorem B1502847 : Blo 1502071 1502847 := bstep (se 1 (by rfl) ⟨1127135, by rfl⟩ : syracuseStep 1502847 = 2254271) B2254271
theorem B12834683 : Blo 1502071 12834683 := bstep (se 1 (by rfl) ⟨9626012, by rfl⟩ : syracuseStep 12834683 = 19252025) B19252025
theorem B8556455 : Blo 1502071 8556455 := bstep (se 1 (by rfl) ⟨6417341, by rfl⟩ : syracuseStep 8556455 = 12834683) B12834683
theorem B32513399 : Blo 1502071 32513399 := bstep (se 1 (by rfl) ⟨24385049, by rfl⟩ : syracuseStep 32513399 = 48770099) B48770099
theorem B5704303 : Blo 1502071 5704303 := bstep (se 1 (by rfl) ⟨4278227, by rfl⟩ : syracuseStep 5704303 = 8556455) B8556455
theorem B21675599 : Blo 1502071 21675599 := bstep (se 1 (by rfl) ⟨16256699, by rfl⟩ : syracuseStep 21675599 = 32513399) B32513399
theorem B7605737 : Blo 1502071 7605737 := bstep (se 2 (by rfl) ⟨2852151, by rfl⟩ : syracuseStep 7605737 = 5704303) B5704303
theorem B14450399 : Blo 1502071 14450399 := bstep (se 1 (by rfl) ⟨10837799, by rfl⟩ : syracuseStep 14450399 = 21675599) B21675599
theorem B5070491 : Blo 1502071 5070491 := bstep (se 1 (by rfl) ⟨3802868, by rfl⟩ : syracuseStep 5070491 = 7605737) B7605737
theorem B9633599 : Blo 1502071 9633599 := bstep (se 1 (by rfl) ⟨7225199, by rfl⟩ : syracuseStep 9633599 = 14450399) B14450399
theorem B3380327 : Blo 1502071 3380327 := bstep (se 1 (by rfl) ⟨2535245, by rfl⟩ : syracuseStep 3380327 = 5070491) B5070491
theorem B6422399 : Blo 1502071 6422399 := bstep (se 1 (by rfl) ⟨4816799, by rfl⟩ : syracuseStep 6422399 = 9633599) B9633599
theorem B2253551 : Blo 1502071 2253551 := bstep (se 1 (by rfl) ⟨1690163, by rfl⟩ : syracuseStep 2253551 = 3380327) B3380327
theorem B4281599 : Blo 1502071 4281599 := bstep (se 1 (by rfl) ⟨3211199, by rfl⟩ : syracuseStep 4281599 = 6422399) B6422399
theorem B1502367 : Blo 1502071 1502367 := bstep (se 1 (by rfl) ⟨1126775, by rfl⟩ : syracuseStep 1502367 = 2253551) B2253551
theorem B11417597 : Blo 1502071 11417597 := bstep (se 3 (by rfl) ⟨2140799, by rfl⟩ : syracuseStep 11417597 = 4281599) B4281599
theorem B7611731 : Blo 1502071 7611731 := bstep (se 1 (by rfl) ⟨5708798, by rfl⟩ : syracuseStep 7611731 = 11417597) B11417597
theorem B5074487 : Blo 1502071 5074487 := bstep (se 1 (by rfl) ⟨3805865, by rfl⟩ : syracuseStep 5074487 = 7611731) B7611731
theorem B3382991 : Blo 1502071 3382991 := bstep (se 1 (by rfl) ⟨2537243, by rfl⟩ : syracuseStep 3382991 = 5074487) B5074487
theorem B2255327 : Blo 1502071 2255327 := bstep (se 1 (by rfl) ⟨1691495, by rfl⟩ : syracuseStep 2255327 = 3382991) B3382991
theorem B1503551 : Blo 1502071 1503551 := bstep (se 1 (by rfl) ⟨1127663, by rfl⟩ : syracuseStep 1503551 = 2255327) B2255327

theorem C0 (j : ℕ) (h1 : 375517 ≤ j) (h2 : j ≤ 375892) : Blo 1502071 (4 * j + 3) := by
  interval_cases j
  · exact B1502071
  · exact B1502075
  · exact B1502079
  · exact B1502083
  · exact B1502087
  · exact B1502091
  · exact B1502095
  · exact B1502099
  · exact B1502103
  · exact B1502107
  · exact B1502111
  · exact B1502115
  · exact B1502119
  · exact B1502123
  · exact B1502127
  · exact B1502131
  · exact B1502135
  · exact B1502139
  · exact B1502143
  · exact B1502147
  · exact B1502151
  · exact B1502155
  · exact B1502159
  · exact B1502163
  · exact B1502167
  · exact B1502171
  · exact B1502175
  · exact B1502179
  · exact B1502183
  · exact B1502187
  · exact B1502191
  · exact B1502195
  · exact B1502199
  · exact B1502203
  · exact B1502207
  · exact B1502211
  · exact B1502215
  · exact B1502219
  · exact B1502223
  · exact B1502227
  · exact B1502231
  · exact B1502235
  · exact B1502239
  · exact B1502243
  · exact B1502247
  · exact B1502251
  · exact B1502255
  · exact B1502259
  · exact B1502263
  · exact B1502267
  · exact B1502271
  · exact B1502275
  · exact B1502279
  · exact B1502283
  · exact B1502287
  · exact B1502291
  · exact B1502295
  · exact B1502299
  · exact B1502303
  · exact B1502307
  · exact B1502311
  · exact B1502315
  · exact B1502319
  · exact B1502323
  · exact B1502327
  · exact B1502331
  · exact B1502335
  · exact B1502339
  · exact B1502343
  · exact B1502347
  · exact B1502351
  · exact B1502355
  · exact B1502359
  · exact B1502363
  · exact B1502367
  · exact B1502371
  · exact B1502375
  · exact B1502379
  · exact B1502383
  · exact B1502387
  · exact B1502391
  · exact B1502395
  · exact B1502399
  · exact B1502403
  · exact B1502407
  · exact B1502411
  · exact B1502415
  · exact B1502419
  · exact B1502423
  · exact B1502427
  · exact B1502431
  · exact B1502435
  · exact B1502439
  · exact B1502443
  · exact B1502447
  · exact B1502451
  · exact B1502455
  · exact B1502459
  · exact B1502463
  · exact B1502467
  · exact B1502471
  · exact B1502475
  · exact B1502479
  · exact B1502483
  · exact B1502487
  · exact B1502491
  · exact B1502495
  · exact B1502499
  · exact B1502503
  · exact B1502507
  · exact B1502511
  · exact B1502515
  · exact B1502519
  · exact B1502523
  · exact B1502527
  · exact B1502531
  · exact B1502535
  · exact B1502539
  · exact B1502543
  · exact B1502547
  · exact B1502551
  · exact B1502555
  · exact B1502559
  · exact B1502563
  · exact B1502567
  · exact B1502571
  · exact B1502575
  · exact B1502579
  · exact B1502583
  · exact B1502587
  · exact B1502591
  · exact B1502595
  · exact B1502599
  · exact B1502603
  · exact B1502607
  · exact B1502611
  · exact B1502615
  · exact B1502619
  · exact B1502623
  · exact B1502627
  · exact B1502631
  · exact B1502635
  · exact B1502639
  · exact B1502643
  · exact B1502647
  · exact B1502651
  · exact B1502655
  · exact B1502659
  · exact B1502663
  · exact B1502667
  · exact B1502671
  · exact B1502675
  · exact B1502679
  · exact B1502683
  · exact B1502687
  · exact B1502691
  · exact B1502695
  · exact B1502699
  · exact B1502703
  · exact B1502707
  · exact B1502711
  · exact B1502715
  · exact B1502719
  · exact B1502723
  · exact B1502727
  · exact B1502731
  · exact B1502735
  · exact B1502739
  · exact B1502743
  · exact B1502747
  · exact B1502751
  · exact B1502755
  · exact B1502759
  · exact B1502763
  · exact B1502767
  · exact B1502771
  · exact B1502775
  · exact B1502779
  · exact B1502783
  · exact B1502787
  · exact B1502791
  · exact B1502795
  · exact B1502799
  · exact B1502803
  · exact B1502807
  · exact B1502811
  · exact B1502815
  · exact B1502819
  · exact B1502823
  · exact B1502827
  · exact B1502831
  · exact B1502835
  · exact B1502839
  · exact B1502843
  · exact B1502847
  · exact B1502851
  · exact B1502855
  · exact B1502859
  · exact B1502863
  · exact B1502867
  · exact B1502871
  · exact B1502875
  · exact B1502879
  · exact B1502883
  · exact B1502887
  · exact B1502891
  · exact B1502895
  · exact B1502899
  · exact B1502903
  · exact B1502907
  · exact B1502911
  · exact B1502915
  · exact B1502919
  · exact B1502923
  · exact B1502927
  · exact B1502931
  · exact B1502935
  · exact B1502939
  · exact B1502943
  · exact B1502947
  · exact B1502951
  · exact B1502955
  · exact B1502959
  · exact B1502963
  · exact B1502967
  · exact B1502971
  · exact B1502975
  · exact B1502979
  · exact B1502983
  · exact B1502987
  · exact B1502991
  · exact B1502995
  · exact B1502999
  · exact B1503003
  · exact B1503007
  · exact B1503011
  · exact B1503015
  · exact B1503019
  · exact B1503023
  · exact B1503027
  · exact B1503031
  · exact B1503035
  · exact B1503039
  · exact B1503043
  · exact B1503047
  · exact B1503051
  · exact B1503055
  · exact B1503059
  · exact B1503063
  · exact B1503067
  · exact B1503071
  · exact B1503075
  · exact B1503079
  · exact B1503083
  · exact B1503087
  · exact B1503091
  · exact B1503095
  · exact B1503099
  · exact B1503103
  · exact B1503107
  · exact B1503111
  · exact B1503115
  · exact B1503119
  · exact B1503123
  · exact B1503127
  · exact B1503131
  · exact B1503135
  · exact B1503139
  · exact B1503143
  · exact B1503147
  · exact B1503151
  · exact B1503155
  · exact B1503159
  · exact B1503163
  · exact B1503167
  · exact B1503171
  · exact B1503175
  · exact B1503179
  · exact B1503183
  · exact B1503187
  · exact B1503191
  · exact B1503195
  · exact B1503199
  · exact B1503203
  · exact B1503207
  · exact B1503211
  · exact B1503215
  · exact B1503219
  · exact B1503223
  · exact B1503227
  · exact B1503231
  · exact B1503235
  · exact B1503239
  · exact B1503243
  · exact B1503247
  · exact B1503251
  · exact B1503255
  · exact B1503259
  · exact B1503263
  · exact B1503267
  · exact B1503271
  · exact B1503275
  · exact B1503279
  · exact B1503283
  · exact B1503287
  · exact B1503291
  · exact B1503295
  · exact B1503299
  · exact B1503303
  · exact B1503307
  · exact B1503311
  · exact B1503315
  · exact B1503319
  · exact B1503323
  · exact B1503327
  · exact B1503331
  · exact B1503335
  · exact B1503339
  · exact B1503343
  · exact B1503347
  · exact B1503351
  · exact B1503355
  · exact B1503359
  · exact B1503363
  · exact B1503367
  · exact B1503371
  · exact B1503375
  · exact B1503379
  · exact B1503383
  · exact B1503387
  · exact B1503391
  · exact B1503395
  · exact B1503399
  · exact B1503403
  · exact B1503407
  · exact B1503411
  · exact B1503415
  · exact B1503419
  · exact B1503423
  · exact B1503427
  · exact B1503431
  · exact B1503435
  · exact B1503439
  · exact B1503443
  · exact B1503447
  · exact B1503451
  · exact B1503455
  · exact B1503459
  · exact B1503463
  · exact B1503467
  · exact B1503471
  · exact B1503475
  · exact B1503479
  · exact B1503483
  · exact B1503487
  · exact B1503491
  · exact B1503495
  · exact B1503499
  · exact B1503503
  · exact B1503507
  · exact B1503511
  · exact B1503515
  · exact B1503519
  · exact B1503523
  · exact B1503527
  · exact B1503531
  · exact B1503535
  · exact B1503539
  · exact B1503543
  · exact B1503547
  · exact B1503551
  · exact B1503555
  · exact B1503559
  · exact B1503563
  · exact B1503567
  · exact B1503571

theorem solution (m : ℕ) (hlo : 1502071 ≤ m) (hhi : m ≤ 1503571) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 375517 ≤ j := by omega
    have hj2 : j ≤ 375892 := by omega
    have hb : Blo 1502071 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
