-- Prove2me | solution 1 for syracuse_descends_range_1733067_1735067
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:32:26.661535+00:00
-- url     : https://prove2.me/submissions/ca584c5f-6d12-461e-bb9b-838c10e3a3c0

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


theorem B1949701 : Blo 1733067 1949701 := bbase (se 4 (by rfl) ⟨182784, by rfl⟩ : syracuseStep 1949701 = 365569) (by norm_num)
theorem B7913477 : Blo 1733067 7913477 := bbase (se 4 (by rfl) ⟨741888, by rfl⟩ : syracuseStep 7913477 = 1483777) (by norm_num)
theorem B3899429 : Blo 1733067 3899429 := bbase (se 4 (by rfl) ⟨365571, by rfl⟩ : syracuseStep 3899429 = 731143) (by norm_num)
theorem B4390949 : Blo 1733067 4390949 := bbase (se 4 (by rfl) ⟨411651, by rfl⟩ : syracuseStep 4390949 = 823303) (by norm_num)
theorem B1949737 : Blo 1733067 1949737 := bbase (se 2 (by rfl) ⟨731151, by rfl⟩ : syracuseStep 1949737 = 1462303) (by norm_num)
theorem B2195525 : Blo 1733067 2195525 := bbase (se 4 (by rfl) ⟨205830, by rfl⟩ : syracuseStep 2195525 = 411661) (by norm_num)
theorem B1949773 : Blo 1733067 1949773 := bbase (se 3 (by rfl) ⟨365582, by rfl⟩ : syracuseStep 1949773 = 731165) (by norm_num)
theorem B7610453 : Blo 1733067 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B3899501 : Blo 1733067 3899501 := bbase (se 3 (by rfl) ⟨731156, by rfl⟩ : syracuseStep 3899501 = 1462313) (by norm_num)
theorem B2924653 : Blo 1733067 2924653 := bbase (se 3 (by rfl) ⟨548372, by rfl⟩ : syracuseStep 2924653 = 1096745) (by norm_num)
theorem B1949809 : Blo 1733067 1949809 := bbase (se 2 (by rfl) ⟨731178, by rfl⟩ : syracuseStep 1949809 = 1462357) (by norm_num)
theorem B2777213 : Blo 1733067 2777213 := bbase (se 3 (by rfl) ⟨520727, by rfl⟩ : syracuseStep 2777213 = 1041455) (by norm_num)
theorem B2195581 : Blo 1733067 2195581 := bbase (se 3 (by rfl) ⟨411671, by rfl⟩ : syracuseStep 2195581 = 823343) (by norm_num)
theorem B3702925 : Blo 1733067 3702925 := bbase (se 3 (by rfl) ⟨694298, by rfl⟩ : syracuseStep 3702925 = 1388597) (by norm_num)
theorem B1949845 : Blo 1733067 1949845 := bbase (se 6 (by rfl) ⟨45699, by rfl⟩ : syracuseStep 1949845 = 91399) (by norm_num)
theorem B6250661 : Blo 1733067 6250661 := bbase (se 4 (by rfl) ⟨585999, by rfl⟩ : syracuseStep 6250661 = 1171999) (by norm_num)
theorem B3899573 : Blo 1733067 3899573 := bbase (se 5 (by rfl) ⟨182792, by rfl⟩ : syracuseStep 3899573 = 365585) (by norm_num)
theorem B8331445 : Blo 1733067 8331445 := bbase (se 5 (by rfl) ⟨390536, by rfl⟩ : syracuseStep 8331445 = 781073) (by norm_num)
theorem B1949881 : Blo 1733067 1949881 := bbase (se 2 (by rfl) ⟨731205, by rfl⟩ : syracuseStep 1949881 = 1462411) (by norm_num)
theorem B2924741 : Blo 1733067 2924741 := bbase (se 4 (by rfl) ⟨274194, by rfl⟩ : syracuseStep 2924741 = 548389) (by norm_num)
theorem B1949917 : Blo 1733067 1949917 := bbase (se 3 (by rfl) ⟨365609, by rfl⟩ : syracuseStep 1949917 = 731219) (by norm_num)
theorem B2195677 : Blo 1733067 2195677 := bbase (se 3 (by rfl) ⟨411689, by rfl⟩ : syracuseStep 2195677 = 823379) (by norm_num)
theorem B5849333 : Blo 1733067 5849333 := bbase (se 5 (by rfl) ⟨274187, by rfl⟩ : syracuseStep 5849333 = 548375) (by norm_num)
theorem B3899645 : Blo 1733067 3899645 := bbase (se 3 (by rfl) ⟨731183, by rfl⟩ : syracuseStep 3899645 = 1462367) (by norm_num)
theorem B1949953 : Blo 1733067 1949953 := bbase (se 2 (by rfl) ⟨731232, by rfl⟩ : syracuseStep 1949953 = 1462465) (by norm_num)
theorem B1949989 : Blo 1733067 1949989 := bbase (se 4 (by rfl) ⟨182811, by rfl⟩ : syracuseStep 1949989 = 365623) (by norm_num)
theorem B14639413 : Blo 1733067 14639413 := bbase (se 5 (by rfl) ⟨686222, by rfl⟩ : syracuseStep 14639413 = 1372445) (by norm_num)
theorem B3899717 : Blo 1733067 3899717 := bbase (se 4 (by rfl) ⟨365598, by rfl⟩ : syracuseStep 3899717 = 731197) (by norm_num)
theorem B2924869 : Blo 1733067 2924869 := bbase (se 4 (by rfl) ⟨274206, by rfl⟩ : syracuseStep 2924869 = 548413) (by norm_num)
theorem B1950025 : Blo 1733067 1950025 := bbase (se 2 (by rfl) ⟨731259, by rfl⟩ : syracuseStep 1950025 = 1462519) (by norm_num)
theorem B8782181 : Blo 1733067 8782181 := bbase (se 4 (by rfl) ⟨823329, by rfl⟩ : syracuseStep 8782181 = 1646659) (by norm_num)
theorem B1950061 : Blo 1733067 1950061 := bbase (se 3 (by rfl) ⟨365636, by rfl⟩ : syracuseStep 1950061 = 731273) (by norm_num)
theorem B4940149 : Blo 1733067 4940149 := bbase (se 5 (by rfl) ⟨231569, by rfl⟩ : syracuseStep 4940149 = 463139) (by norm_num)
theorem B4391293 : Blo 1733067 4391293 := bbase (se 3 (by rfl) ⟨823367, by rfl⟩ : syracuseStep 4391293 = 1646735) (by norm_num)
theorem B3514757 : Blo 1733067 3514757 := bbase (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) (by norm_num)
theorem B2195849 : Blo 1733067 2195849 := bbase (se 2 (by rfl) ⟨823443, by rfl⟩ : syracuseStep 2195849 = 1646887) (by norm_num)
theorem B3899789 : Blo 1733067 3899789 := bbase (se 3 (by rfl) ⟨731210, by rfl⟩ : syracuseStep 3899789 = 1462421) (by norm_num)
theorem B1950097 : Blo 1733067 1950097 := bbase (se 2 (by rfl) ⟨731286, by rfl⟩ : syracuseStep 1950097 = 1462573) (by norm_num)
theorem B2924957 : Blo 1733067 2924957 := bbase (se 3 (by rfl) ⟨548429, by rfl⟩ : syracuseStep 2924957 = 1096859) (by norm_num)
theorem B3514781 : Blo 1733067 3514781 := bbase (se 3 (by rfl) ⟨659021, by rfl⟩ : syracuseStep 3514781 = 1318043) (by norm_num)
theorem B1851817 : Blo 1733067 1851817 := bbase (se 2 (by rfl) ⟨694431, by rfl⟩ : syracuseStep 1851817 = 1388863) (by norm_num)
theorem B1950133 : Blo 1733067 1950133 := bbase (se 5 (by rfl) ⟨91412, by rfl⟩ : syracuseStep 1950133 = 182825) (by norm_num)
theorem B10011061 : Blo 1733067 10011061 := bbase (se 5 (by rfl) ⟨469268, by rfl⟩ : syracuseStep 10011061 = 938537) (by norm_num)
theorem B2195905 : Blo 1733067 2195905 := bbase (se 2 (by rfl) ⟨823464, by rfl⟩ : syracuseStep 2195905 = 1646929) (by norm_num)
theorem B3899861 : Blo 1733067 3899861 := bbase (se 7 (by rfl) ⟨45701, by rfl⟩ : syracuseStep 3899861 = 91403) (by norm_num)
theorem B1950169 : Blo 1733067 1950169 := bbase (se 2 (by rfl) ⟨731313, by rfl⟩ : syracuseStep 1950169 = 1462627) (by norm_num)
theorem B4391405 : Blo 1733067 4391405 := bbase (se 3 (by rfl) ⟨823388, by rfl⟩ : syracuseStep 4391405 = 1646777) (by norm_num)
theorem B15024629 : Blo 1733067 15024629 := bbase (se 5 (by rfl) ⟨704279, by rfl⟩ : syracuseStep 15024629 = 1408559) (by norm_num)
theorem B1950205 : Blo 1733067 1950205 := bbase (se 3 (by rfl) ⟨365663, by rfl⟩ : syracuseStep 1950205 = 731327) (by norm_num)
theorem B7029269 : Blo 1733067 7029269 := bbase (se 6 (by rfl) ⟨164748, by rfl⟩ : syracuseStep 7029269 = 329497) (by norm_num)
theorem B3899933 : Blo 1733067 3899933 := bbase (se 3 (by rfl) ⟨731237, by rfl⟩ : syracuseStep 3899933 = 1462475) (by norm_num)
theorem B2925085 : Blo 1733067 2925085 := bbase (se 3 (by rfl) ⟨548453, by rfl⟩ : syracuseStep 2925085 = 1096907) (by norm_num)
theorem B1950241 : Blo 1733067 1950241 := bbase (se 2 (by rfl) ⟨731340, by rfl⟩ : syracuseStep 1950241 = 1462681) (by norm_num)
theorem B1851941 : Blo 1733067 1851941 := bbase (se 4 (by rfl) ⟨173619, by rfl⟩ : syracuseStep 1851941 = 347239) (by norm_num)
theorem B1950277 : Blo 1733067 1950277 := bbase (se 4 (by rfl) ⟨182838, by rfl⟩ : syracuseStep 1950277 = 365677) (by norm_num)
theorem B3900005 : Blo 1733067 3900005 := bbase (se 4 (by rfl) ⟨365625, by rfl⟩ : syracuseStep 3900005 = 731251) (by norm_num)
theorem B3293797 : Blo 1733067 3293797 := bbase (se 4 (by rfl) ⟨308793, by rfl⟩ : syracuseStep 3293797 = 617587) (by norm_num)
theorem B1950313 : Blo 1733067 1950313 := bbase (se 2 (by rfl) ⟨731367, by rfl⟩ : syracuseStep 1950313 = 1462735) (by norm_num)
theorem B2343533 : Blo 1733067 2343533 := bbase (se 3 (by rfl) ⟨439412, by rfl⟩ : syracuseStep 2343533 = 878825) (by norm_num)
theorem B2925173 : Blo 1733067 2925173 := bbase (se 5 (by rfl) ⟨137117, by rfl⟩ : syracuseStep 2925173 = 274235) (by norm_num)
theorem B1950349 : Blo 1733067 1950349 := bbase (se 3 (by rfl) ⟨365690, by rfl⟩ : syracuseStep 1950349 = 731381) (by norm_num)
theorem B11870869 : Blo 1733067 11870869 := bbase (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) (by norm_num)
theorem B5849765 : Blo 1733067 5849765 := bbase (se 4 (by rfl) ⟨548415, by rfl⟩ : syracuseStep 5849765 = 1096831) (by norm_num)
theorem B3900077 : Blo 1733067 3900077 := bbase (se 3 (by rfl) ⟨731264, by rfl⟩ : syracuseStep 3900077 = 1462529) (by norm_num)
theorem B4391597 : Blo 1733067 4391597 := bbase (se 3 (by rfl) ⟨823424, by rfl⟩ : syracuseStep 4391597 = 1646849) (by norm_num)
theorem B1950385 : Blo 1733067 1950385 := bbase (se 2 (by rfl) ⟨731394, by rfl⟩ : syracuseStep 1950385 = 1462789) (by norm_num)
theorem B7406261 : Blo 1733067 7406261 := bbase (se 5 (by rfl) ⟨347168, by rfl⟩ : syracuseStep 7406261 = 694337) (by norm_num)
theorem B2966213 : Blo 1733067 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B1950421 : Blo 1733067 1950421 := bbase (se 7 (by rfl) ⟨22856, by rfl⟩ : syracuseStep 1950421 = 45713) (by norm_num)
theorem B3900149 : Blo 1733067 3900149 := bbase (se 5 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 3900149 = 365639) (by norm_num)
theorem B2925301 : Blo 1733067 2925301 := bbase (se 5 (by rfl) ⟨137123, by rfl⟩ : syracuseStep 2925301 = 274247) (by norm_num)
theorem B1950457 : Blo 1733067 1950457 := bbase (se 2 (by rfl) ⟨731421, by rfl⟩ : syracuseStep 1950457 = 1462843) (by norm_num)
theorem B8774405 : Blo 1733067 8774405 := bbase (se 4 (by rfl) ⟨822600, by rfl⟩ : syracuseStep 8774405 = 1645201) (by norm_num)
theorem B1950493 : Blo 1733067 1950493 := bbase (se 3 (by rfl) ⟨365717, by rfl⟩ : syracuseStep 1950493 = 731435) (by norm_num)
theorem B1852193 : Blo 1733067 1852193 := bbase (se 2 (by rfl) ⟨694572, by rfl⟩ : syracuseStep 1852193 = 1389145) (by norm_num)
theorem B3900221 : Blo 1733067 3900221 := bbase (se 3 (by rfl) ⟨731291, by rfl⟩ : syracuseStep 3900221 = 1462583) (by norm_num)
theorem B1950529 : Blo 1733067 1950529 := bbase (se 2 (by rfl) ⟨731448, by rfl⟩ : syracuseStep 1950529 = 1462897) (by norm_num)
theorem B2925389 : Blo 1733067 2925389 := bbase (se 3 (by rfl) ⟨548510, by rfl⟩ : syracuseStep 2925389 = 1097021) (by norm_num)
theorem B1950565 : Blo 1733067 1950565 := bbase (se 4 (by rfl) ⟨182865, by rfl⟩ : syracuseStep 1950565 = 365731) (by norm_num)
theorem B3900293 : Blo 1733067 3900293 := bbase (se 4 (by rfl) ⟨365652, by rfl⟩ : syracuseStep 3900293 = 731305) (by norm_num)
theorem B1950601 : Blo 1733067 1950601 := bbase (se 2 (by rfl) ⟨731475, by rfl⟩ : syracuseStep 1950601 = 1462951) (by norm_num)
theorem B1950637 : Blo 1733067 1950637 := bbase (se 3 (by rfl) ⟨365744, by rfl⟩ : syracuseStep 1950637 = 731489) (by norm_num)
theorem B9880501 : Blo 1733067 9880501 := bbase (se 5 (by rfl) ⟨463148, by rfl⟩ : syracuseStep 9880501 = 926297) (by norm_num)
theorem B3900365 : Blo 1733067 3900365 := bbase (se 3 (by rfl) ⟨731318, by rfl⟩ : syracuseStep 3900365 = 1462637) (by norm_num)
theorem B2925517 : Blo 1733067 2925517 := bbase (se 3 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 2925517 = 1097069) (by norm_num)
theorem B1950673 : Blo 1733067 1950673 := bbase (se 2 (by rfl) ⟨731502, by rfl⟩ : syracuseStep 1950673 = 1463005) (by norm_num)
theorem B7406549 : Blo 1733067 7406549 := bbase (se 7 (by rfl) ⟨86795, by rfl⟩ : syracuseStep 7406549 = 173591) (by norm_num)
theorem B6587365 : Blo 1733067 6587365 := bbase (se 4 (by rfl) ⟨617565, by rfl⟩ : syracuseStep 6587365 = 1235131) (by norm_num)
theorem B1950709 : Blo 1733067 1950709 := bbase (se 5 (by rfl) ⟨91439, by rfl⟩ : syracuseStep 1950709 = 182879) (by norm_num)
theorem B3900437 : Blo 1733067 3900437 := bbase (se 6 (by rfl) ⟨91416, by rfl⟩ : syracuseStep 3900437 = 182833) (by norm_num)
theorem B1950745 : Blo 1733067 1950745 := bbase (se 2 (by rfl) ⟨731529, by rfl⟩ : syracuseStep 1950745 = 1463059) (by norm_num)
theorem B2925605 : Blo 1733067 2925605 := bbase (se 4 (by rfl) ⟨274275, by rfl⟩ : syracuseStep 2925605 = 548551) (by norm_num)
theorem B1950781 : Blo 1733067 1950781 := bbase (se 3 (by rfl) ⟨365771, by rfl⟩ : syracuseStep 1950781 = 731543) (by norm_num)
theorem B5850197 : Blo 1733067 5850197 := bbase (se 8 (by rfl) ⟨34278, by rfl⟩ : syracuseStep 5850197 = 68557) (by norm_num)
theorem B3900509 : Blo 1733067 3900509 := bbase (se 3 (by rfl) ⟨731345, by rfl⟩ : syracuseStep 3900509 = 1462691) (by norm_num)
theorem B1950817 : Blo 1733067 1950817 := bbase (se 2 (by rfl) ⟨731556, by rfl⟩ : syracuseStep 1950817 = 1463113) (by norm_num)
theorem B1950853 : Blo 1733067 1950853 := bbase (se 4 (by rfl) ⟨182892, by rfl⟩ : syracuseStep 1950853 = 365785) (by norm_num)
theorem B3900581 : Blo 1733067 3900581 := bbase (se 4 (by rfl) ⟨365679, by rfl⟩ : syracuseStep 3900581 = 731359) (by norm_num)
theorem B2925733 : Blo 1733067 2925733 := bbase (se 4 (by rfl) ⟨274287, by rfl⟩ : syracuseStep 2925733 = 548575) (by norm_num)
theorem B1950889 : Blo 1733067 1950889 := bbase (se 2 (by rfl) ⟨731583, by rfl⟩ : syracuseStep 1950889 = 1463167) (by norm_num)
theorem B1950925 : Blo 1733067 1950925 := bbase (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) (by norm_num)
theorem B1852637 : Blo 1733067 1852637 := bbase (se 3 (by rfl) ⟨347369, by rfl⟩ : syracuseStep 1852637 = 694739) (by norm_num)
theorem B3900653 : Blo 1733067 3900653 := bbase (se 3 (by rfl) ⟨731372, by rfl⟩ : syracuseStep 3900653 = 1462745) (by norm_num)
theorem B1950961 : Blo 1733067 1950961 := bbase (se 2 (by rfl) ⟨731610, by rfl⟩ : syracuseStep 1950961 = 1463221) (by norm_num)
theorem B2925821 : Blo 1733067 2925821 := bbase (se 3 (by rfl) ⟨548591, by rfl⟩ : syracuseStep 2925821 = 1097183) (by norm_num)
theorem B1950997 : Blo 1733067 1950997 := bbase (se 6 (by rfl) ⟨45726, by rfl⟩ : syracuseStep 1950997 = 91453) (by norm_num)
theorem B6587669 : Blo 1733067 6587669 := bbase (se 6 (by rfl) ⟨154398, by rfl⟩ : syracuseStep 6587669 = 308797) (by norm_num)
theorem B3900725 : Blo 1733067 3900725 := bbase (se 5 (by rfl) ⟨182846, by rfl⟩ : syracuseStep 3900725 = 365693) (by norm_num)
theorem B1951033 : Blo 1733067 1951033 := bbase (se 2 (by rfl) ⟨731637, by rfl⟩ : syracuseStep 1951033 = 1463275) (by norm_num)
theorem B1951069 : Blo 1733067 1951069 := bbase (se 3 (by rfl) ⟨365825, by rfl⟩ : syracuseStep 1951069 = 731651) (by norm_num)
theorem B3900797 : Blo 1733067 3900797 := bbase (se 3 (by rfl) ⟨731399, by rfl⟩ : syracuseStep 3900797 = 1462799) (by norm_num)
theorem B2925949 : Blo 1733067 2925949 := bbase (se 3 (by rfl) ⟨548615, by rfl⟩ : syracuseStep 2925949 = 1097231) (by norm_num)
theorem B1951105 : Blo 1733067 1951105 := bbase (se 2 (by rfl) ⟨731664, by rfl⟩ : syracuseStep 1951105 = 1463329) (by norm_num)
theorem B8897941 : Blo 1733067 8897941 := bbase (se 6 (by rfl) ⟨208545, by rfl⟩ : syracuseStep 8897941 = 417091) (by norm_num)
theorem B1951141 : Blo 1733067 1951141 := bbase (se 4 (by rfl) ⟨182919, by rfl⟩ : syracuseStep 1951141 = 365839) (by norm_num)
theorem B2778533 : Blo 1733067 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B3900869 : Blo 1733067 3900869 := bbase (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) (by norm_num)
theorem B1951177 : Blo 1733067 1951177 := bbase (se 2 (by rfl) ⟨731691, by rfl⟩ : syracuseStep 1951177 = 1463383) (by norm_num)
theorem B2926037 : Blo 1733067 2926037 := bbase (se 7 (by rfl) ⟨34289, by rfl⟩ : syracuseStep 2926037 = 68579) (by norm_num)
theorem B1951213 : Blo 1733067 1951213 := bbase (se 3 (by rfl) ⟨365852, by rfl⟩ : syracuseStep 1951213 = 731705) (by norm_num)
theorem B5850629 : Blo 1733067 5850629 := bbase (se 4 (by rfl) ⟨548496, by rfl⟩ : syracuseStep 5850629 = 1096993) (by norm_num)
theorem B2778629 : Blo 1733067 2778629 := bbase (se 4 (by rfl) ⟨260496, by rfl⟩ : syracuseStep 2778629 = 520993) (by norm_num)
theorem B3900941 : Blo 1733067 3900941 := bbase (se 3 (by rfl) ⟨731426, by rfl⟩ : syracuseStep 3900941 = 1462853) (by norm_num)
theorem B1951249 : Blo 1733067 1951249 := bbase (se 2 (by rfl) ⟨731718, by rfl⟩ : syracuseStep 1951249 = 1463437) (by norm_num)
theorem B2778661 : Blo 1733067 2778661 := bbase (se 4 (by rfl) ⟨260499, by rfl⟩ : syracuseStep 2778661 = 520999) (by norm_num)
theorem B1951285 : Blo 1733067 1951285 := bbase (se 5 (by rfl) ⟨91466, by rfl⟩ : syracuseStep 1951285 = 182933) (by norm_num)
theorem B3901013 : Blo 1733067 3901013 := bbase (se 8 (by rfl) ⟨22857, by rfl⟩ : syracuseStep 3901013 = 45715) (by norm_num)
theorem B2926165 : Blo 1733067 2926165 := bbase (se 8 (by rfl) ⟨17145, by rfl⟩ : syracuseStep 2926165 = 34291) (by norm_num)
theorem B1951321 : Blo 1733067 1951321 := bbase (se 2 (by rfl) ⟨731745, by rfl⟩ : syracuseStep 1951321 = 1463491) (by norm_num)
theorem B3704429 : Blo 1733067 3704429 := bbase (se 3 (by rfl) ⟨694580, by rfl⟩ : syracuseStep 3704429 = 1389161) (by norm_num)
theorem B8783477 : Blo 1733067 8783477 := bbase (se 5 (by rfl) ⟨411725, by rfl⟩ : syracuseStep 8783477 = 823451) (by norm_num)
theorem B2139769 : Blo 1733067 2139769 := bbase (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) (by norm_num)
theorem B1951357 : Blo 1733067 1951357 := bbase (se 3 (by rfl) ⟨365879, by rfl⟩ : syracuseStep 1951357 = 731759) (by norm_num)
theorem B5555861 : Blo 1733067 5555861 := bbase (se 6 (by rfl) ⟨130215, by rfl⟩ : syracuseStep 5555861 = 260431) (by norm_num)
theorem B3901085 : Blo 1733067 3901085 := bbase (se 3 (by rfl) ⟨731453, by rfl⟩ : syracuseStep 3901085 = 1462907) (by norm_num)
theorem B1951393 : Blo 1733067 1951393 := bbase (se 2 (by rfl) ⟨731772, by rfl⟩ : syracuseStep 1951393 = 1463545) (by norm_num)
theorem B2926253 : Blo 1733067 2926253 := bbase (se 3 (by rfl) ⟨548672, by rfl⟩ : syracuseStep 2926253 = 1097345) (by norm_num)
theorem B7407301 : Blo 1733067 7407301 := bbase (se 4 (by rfl) ⟨694434, by rfl⟩ : syracuseStep 7407301 = 1388869) (by norm_num)
theorem B1951429 : Blo 1733067 1951429 := bbase (se 4 (by rfl) ⟨182946, by rfl⟩ : syracuseStep 1951429 = 365893) (by norm_num)
theorem B3901157 : Blo 1733067 3901157 := bbase (se 4 (by rfl) ⟨365733, by rfl⟩ : syracuseStep 3901157 = 731467) (by norm_num)
theorem B1951465 : Blo 1733067 1951465 := bbase (se 2 (by rfl) ⟨731799, by rfl⟩ : syracuseStep 1951465 = 1463599) (by norm_num)
theorem B4450037 : Blo 1733067 4450037 := bbase (se 5 (by rfl) ⟨208595, by rfl⟩ : syracuseStep 4450037 = 417191) (by norm_num)
theorem B3704573 : Blo 1733067 3704573 := bbase (se 3 (by rfl) ⟨694607, by rfl⟩ : syracuseStep 3704573 = 1389215) (by norm_num)
theorem B2467597 : Blo 1733067 2467597 := bbase (se 3 (by rfl) ⟨462674, by rfl⟩ : syracuseStep 2467597 = 925349) (by norm_num)
theorem B1951501 : Blo 1733067 1951501 := bbase (se 3 (by rfl) ⟨365906, by rfl⟩ : syracuseStep 1951501 = 731813) (by norm_num)
theorem B25011989 : Blo 1733067 25011989 := bbase (se 6 (by rfl) ⟨586218, by rfl⟩ : syracuseStep 25011989 = 1172437) (by norm_num)
theorem B3901229 : Blo 1733067 3901229 := bbase (se 3 (by rfl) ⟨731480, by rfl⟩ : syracuseStep 3901229 = 1462961) (by norm_num)
theorem B2926381 : Blo 1733067 2926381 := bbase (se 3 (by rfl) ⟨548696, by rfl⟩ : syracuseStep 2926381 = 1097393) (by norm_num)
theorem B1951537 : Blo 1733067 1951537 := bbase (se 2 (by rfl) ⟨731826, by rfl⟩ : syracuseStep 1951537 = 1463653) (by norm_num)
theorem B2967349 : Blo 1733067 2967349 := bbase (se 5 (by rfl) ⟨139094, by rfl⟩ : syracuseStep 2967349 = 278189) (by norm_num)
theorem B1951573 : Blo 1733067 1951573 := bbase (se 9 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 1951573 = 11435) (by norm_num)
theorem B3901301 : Blo 1733067 3901301 := bbase (se 5 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 3901301 = 365747) (by norm_num)
theorem B1951609 : Blo 1733067 1951609 := bbase (se 2 (by rfl) ⟨731853, by rfl⟩ : syracuseStep 1951609 = 1463707) (by norm_num)
theorem B2926469 : Blo 1733067 2926469 := bbase (se 4 (by rfl) ⟨274356, by rfl⟩ : syracuseStep 2926469 = 548713) (by norm_num)
theorem B1951645 : Blo 1733067 1951645 := bbase (se 3 (by rfl) ⟨365933, by rfl⟩ : syracuseStep 1951645 = 731867) (by norm_num)
theorem B5851061 : Blo 1733067 5851061 := bbase (se 5 (by rfl) ⟨274268, by rfl⟩ : syracuseStep 5851061 = 548537) (by norm_num)
theorem B3901373 : Blo 1733067 3901373 := bbase (se 3 (by rfl) ⟨731507, by rfl⟩ : syracuseStep 3901373 = 1463015) (by norm_num)
theorem B1951681 : Blo 1733067 1951681 := bbase (se 2 (by rfl) ⟨731880, by rfl⟩ : syracuseStep 1951681 = 1463761) (by norm_num)
theorem B12502997 : Blo 1733067 12502997 := bbase (se 7 (by rfl) ⟨146519, by rfl⟩ : syracuseStep 12502997 = 293039) (by norm_num)
theorem B1951717 : Blo 1733067 1951717 := bbase (se 4 (by rfl) ⟨182973, by rfl⟩ : syracuseStep 1951717 = 365947) (by norm_num)
theorem B3901445 : Blo 1733067 3901445 := bbase (se 4 (by rfl) ⟨365760, by rfl⟩ : syracuseStep 3901445 = 731521) (by norm_num)
theorem B2926597 : Blo 1733067 2926597 := bbase (se 4 (by rfl) ⟨274368, by rfl⟩ : syracuseStep 2926597 = 548737) (by norm_num)
theorem B1951753 : Blo 1733067 1951753 := bbase (se 2 (by rfl) ⟨731907, by rfl⟩ : syracuseStep 1951753 = 1463815) (by norm_num)
theorem B8775701 : Blo 1733067 8775701 := bbase (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) (by norm_num)
theorem B6252565 : Blo 1733067 6252565 := bbase (se 6 (by rfl) ⟨146544, by rfl⟩ : syracuseStep 6252565 = 293089) (by norm_num)
theorem B1951789 : Blo 1733067 1951789 := bbase (se 3 (by rfl) ⟨365960, by rfl⟩ : syracuseStep 1951789 = 731921) (by norm_num)
theorem B3901517 : Blo 1733067 3901517 := bbase (se 3 (by rfl) ⟨731534, by rfl⟩ : syracuseStep 3901517 = 1463069) (by norm_num)
theorem B1951825 : Blo 1733067 1951825 := bbase (se 2 (by rfl) ⟨731934, by rfl⟩ : syracuseStep 1951825 = 1463869) (by norm_num)
theorem B53413973 : Blo 1733067 53413973 := bbase (se 8 (by rfl) ⟨312972, by rfl⟩ : syracuseStep 53413973 = 625945) (by norm_num)
theorem B2926685 : Blo 1733067 2926685 := bbase (se 3 (by rfl) ⟨548753, by rfl⟩ : syracuseStep 2926685 = 1097507) (by norm_num)
theorem B3704933 : Blo 1733067 3704933 := bbase (se 4 (by rfl) ⟨347337, by rfl⟩ : syracuseStep 3704933 = 694675) (by norm_num)
theorem B1951861 : Blo 1733067 1951861 := bbase (se 5 (by rfl) ⟨91493, by rfl⟩ : syracuseStep 1951861 = 182987) (by norm_num)
theorem B3901589 : Blo 1733067 3901589 := bbase (se 6 (by rfl) ⟨91443, by rfl⟩ : syracuseStep 3901589 = 182887) (by norm_num)
theorem B1951897 : Blo 1733067 1951897 := bbase (se 2 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 1951897 = 1463923) (by norm_num)
theorem B1951933 : Blo 1733067 1951933 := bbase (se 3 (by rfl) ⟨365987, by rfl⟩ : syracuseStep 1951933 = 731975) (by norm_num)
theorem B3901661 : Blo 1733067 3901661 := bbase (se 3 (by rfl) ⟨731561, by rfl⟩ : syracuseStep 3901661 = 1463123) (by norm_num)
theorem B2926813 : Blo 1733067 2926813 := bbase (se 3 (by rfl) ⟨548777, by rfl⟩ : syracuseStep 2926813 = 1097555) (by norm_num)
theorem B3901733 : Blo 1733067 3901733 := bbase (se 4 (by rfl) ⟨365787, by rfl⟩ : syracuseStep 3901733 = 731575) (by norm_num)
theorem B2926901 : Blo 1733067 2926901 := bbase (se 5 (by rfl) ⟨137198, by rfl⟩ : syracuseStep 2926901 = 274397) (by norm_num)
theorem B2468189 : Blo 1733067 2468189 := bbase (se 3 (by rfl) ⟨462785, by rfl⟩ : syracuseStep 2468189 = 925571) (by norm_num)
theorem B2083169 : Blo 1733067 2083169 := bbase (se 2 (by rfl) ⟨781188, by rfl⟩ : syracuseStep 2083169 = 1562377) (by norm_num)
theorem B5851493 : Blo 1733067 5851493 := bbase (se 4 (by rfl) ⟨548577, by rfl⟩ : syracuseStep 5851493 = 1097155) (by norm_num)
theorem B3901805 : Blo 1733067 3901805 := bbase (se 3 (by rfl) ⟨731588, by rfl⟩ : syracuseStep 3901805 = 1463177) (by norm_num)
theorem B1976737 : Blo 1733067 1976737 := bbase (se 2 (by rfl) ⟨741276, by rfl⟩ : syracuseStep 1976737 = 1482553) (by norm_num)
theorem B7408037 : Blo 1733067 7408037 := bbase (se 4 (by rfl) ⟨694503, by rfl⟩ : syracuseStep 7408037 = 1389007) (by norm_num)
theorem B2468269 : Blo 1733067 2468269 := bbase (se 3 (by rfl) ⟨462800, by rfl⟩ : syracuseStep 2468269 = 925601) (by norm_num)
theorem B3901877 : Blo 1733067 3901877 := bbase (se 5 (by rfl) ⟨182900, by rfl⟩ : syracuseStep 3901877 = 365801) (by norm_num)
theorem B2927029 : Blo 1733067 2927029 := bbase (se 5 (by rfl) ⟨137204, by rfl⟩ : syracuseStep 2927029 = 274409) (by norm_num)
theorem B3901949 : Blo 1733067 3901949 := bbase (se 3 (by rfl) ⟨731615, by rfl⟩ : syracuseStep 3901949 = 1463231) (by norm_num)
theorem B2927117 : Blo 1733067 2927117 := bbase (se 3 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 2927117 = 1097669) (by norm_num)
theorem B5556757 : Blo 1733067 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B2083357 : Blo 1733067 2083357 := bbase (se 3 (by rfl) ⟨390629, by rfl⟩ : syracuseStep 2083357 = 781259) (by norm_num)
theorem B2468389 : Blo 1733067 2468389 := bbase (se 4 (by rfl) ⟨231411, by rfl⟩ : syracuseStep 2468389 = 462823) (by norm_num)
theorem B3902021 : Blo 1733067 3902021 := bbase (se 4 (by rfl) ⟨365814, by rfl⟩ : syracuseStep 3902021 = 731629) (by norm_num)
theorem B2468485 : Blo 1733067 2468485 := bbase (se 4 (by rfl) ⟨231420, by rfl⟩ : syracuseStep 2468485 = 462841) (by norm_num)
theorem B4016773 : Blo 1733067 4016773 := bbase (se 4 (by rfl) ⟨376572, by rfl⟩ : syracuseStep 4016773 = 753145) (by norm_num)
theorem B3902093 : Blo 1733067 3902093 := bbase (se 3 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 3902093 = 1463285) (by norm_num)
theorem B2927245 : Blo 1733067 2927245 := bbase (se 3 (by rfl) ⟨548858, by rfl⟩ : syracuseStep 2927245 = 1097717) (by norm_num)
theorem B7129781 : Blo 1733067 7129781 := bbase (se 5 (by rfl) ⟨334208, by rfl⟩ : syracuseStep 7129781 = 668417) (by norm_num)
theorem B2599613 : Blo 1733067 2599613 := bbase (se 3 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 2599613 = 974855) (by norm_num)
theorem B4164301 : Blo 1733067 4164301 := bbase (se 3 (by rfl) ⟨780806, by rfl⟩ : syracuseStep 4164301 = 1561613) (by norm_num)
theorem B2599637 : Blo 1733067 2599637 := bbase (se 7 (by rfl) ⟨30464, by rfl⟩ : syracuseStep 2599637 = 60929) (by norm_num)
theorem B3902165 : Blo 1733067 3902165 := bbase (se 7 (by rfl) ⟨45728, by rfl⟩ : syracuseStep 3902165 = 91457) (by norm_num)
theorem B2927333 : Blo 1733067 2927333 := bbase (se 4 (by rfl) ⟨274437, by rfl⟩ : syracuseStep 2927333 = 548875) (by norm_num)
theorem B2599661 : Blo 1733067 2599661 := bbase (se 3 (by rfl) ⟨487436, by rfl⟩ : syracuseStep 2599661 = 974873) (by norm_num)
theorem B2083573 : Blo 1733067 2083573 := bbase (se 5 (by rfl) ⟨97667, by rfl⟩ : syracuseStep 2083573 = 195335) (by norm_num)
theorem B6253301 : Blo 1733067 6253301 := bbase (se 5 (by rfl) ⟨293123, by rfl⟩ : syracuseStep 6253301 = 586247) (by norm_num)
theorem B2599685 : Blo 1733067 2599685 := bbase (se 4 (by rfl) ⟨243720, by rfl⟩ : syracuseStep 2599685 = 487441) (by norm_num)
theorem B5851925 : Blo 1733067 5851925 := bbase (se 6 (by rfl) ⟨137154, by rfl⟩ : syracuseStep 5851925 = 274309) (by norm_num)
theorem B2599709 : Blo 1733067 2599709 := bbase (se 3 (by rfl) ⟨487445, by rfl⟩ : syracuseStep 2599709 = 974891) (by norm_num)
theorem B3902237 : Blo 1733067 3902237 := bbase (se 3 (by rfl) ⟨731669, by rfl⟩ : syracuseStep 3902237 = 1463339) (by norm_num)
theorem B2599733 : Blo 1733067 2599733 := bbase (se 5 (by rfl) ⟨121862, by rfl⟩ : syracuseStep 2599733 = 243725) (by norm_num)
theorem B2599757 : Blo 1733067 2599757 := bbase (se 3 (by rfl) ⟨487454, by rfl⟩ : syracuseStep 2599757 = 974909) (by norm_num)
theorem B2599781 : Blo 1733067 2599781 := bbase (se 4 (by rfl) ⟨243729, by rfl⟩ : syracuseStep 2599781 = 487459) (by norm_num)
theorem B3902309 : Blo 1733067 3902309 := bbase (se 4 (by rfl) ⟨365841, by rfl⟩ : syracuseStep 3902309 = 731683) (by norm_num)
theorem B2927461 : Blo 1733067 2927461 := bbase (se 4 (by rfl) ⟨274449, by rfl⟩ : syracuseStep 2927461 = 548899) (by norm_num)
theorem B2599805 : Blo 1733067 2599805 := bbase (se 3 (by rfl) ⟨487463, by rfl⟩ : syracuseStep 2599805 = 974927) (by norm_num)
theorem B2599829 : Blo 1733067 2599829 := bbase (se 6 (by rfl) ⟨60933, by rfl⟩ : syracuseStep 2599829 = 121867) (by norm_num)
theorem B5557157 : Blo 1733067 5557157 := bbase (se 4 (by rfl) ⟨520983, by rfl⟩ : syracuseStep 5557157 = 1041967) (by norm_num)
theorem B2599853 : Blo 1733067 2599853 := bbase (se 3 (by rfl) ⟨487472, by rfl⟩ : syracuseStep 2599853 = 974945) (by norm_num)
theorem B3902381 : Blo 1733067 3902381 := bbase (se 3 (by rfl) ⟨731696, by rfl⟩ : syracuseStep 3902381 = 1463393) (by norm_num)
theorem B4221877 : Blo 1733067 4221877 := bbase (se 5 (by rfl) ⟨197900, by rfl⟩ : syracuseStep 4221877 = 395801) (by norm_num)
theorem B2927549 : Blo 1733067 2927549 := bbase (se 3 (by rfl) ⟨548915, by rfl⟩ : syracuseStep 2927549 = 1097831) (by norm_num)
theorem B2599877 : Blo 1733067 2599877 := bbase (se 4 (by rfl) ⟨243738, by rfl⟩ : syracuseStep 2599877 = 487477) (by norm_num)
theorem B8899541 : Blo 1733067 8899541 := bbase (se 7 (by rfl) ⟨104291, by rfl⟩ : syracuseStep 8899541 = 208583) (by norm_num)
theorem B2599901 : Blo 1733067 2599901 := bbase (se 3 (by rfl) ⟨487481, by rfl⟩ : syracuseStep 2599901 = 974963) (by norm_num)
theorem B2599925 : Blo 1733067 2599925 := bbase (se 5 (by rfl) ⟨121871, by rfl⟩ : syracuseStep 2599925 = 243743) (by norm_num)
theorem B3902453 : Blo 1733067 3902453 := bbase (se 5 (by rfl) ⟨182927, by rfl⟩ : syracuseStep 3902453 = 365855) (by norm_num)
theorem B2599949 : Blo 1733067 2599949 := bbase (se 3 (by rfl) ⟨487490, by rfl⟩ : syracuseStep 2599949 = 974981) (by norm_num)
theorem B2083861 : Blo 1733067 2083861 := bbase (se 6 (by rfl) ⟨48840, by rfl⟩ : syracuseStep 2083861 = 97681) (by norm_num)
theorem B2599973 : Blo 1733067 2599973 := bbase (se 4 (by rfl) ⟨243747, by rfl⟩ : syracuseStep 2599973 = 487495) (by norm_num)
theorem B2599997 : Blo 1733067 2599997 := bbase (se 3 (by rfl) ⟨487499, by rfl⟩ : syracuseStep 2599997 = 974999) (by norm_num)
theorem B3902525 : Blo 1733067 3902525 := bbase (se 3 (by rfl) ⟨731723, by rfl⟩ : syracuseStep 3902525 = 1463447) (by norm_num)
theorem B2927677 : Blo 1733067 2927677 := bbase (se 3 (by rfl) ⟨548939, by rfl⟩ : syracuseStep 2927677 = 1097879) (by norm_num)
theorem B2600021 : Blo 1733067 2600021 := bbase (se 8 (by rfl) ⟨15234, by rfl⟩ : syracuseStep 2600021 = 30469) (by norm_num)
theorem B2600045 : Blo 1733067 2600045 := bbase (se 3 (by rfl) ⟨487508, by rfl⟩ : syracuseStep 2600045 = 975017) (by norm_num)
theorem B2468981 : Blo 1733067 2468981 := bbase (se 5 (by rfl) ⟨115733, by rfl⟩ : syracuseStep 2468981 = 231467) (by norm_num)
theorem B2600069 : Blo 1733067 2600069 := bbase (se 4 (by rfl) ⟨243756, by rfl⟩ : syracuseStep 2600069 = 487513) (by norm_num)
theorem B3902597 : Blo 1733067 3902597 := bbase (se 4 (by rfl) ⟨365868, by rfl⟩ : syracuseStep 3902597 = 731737) (by norm_num)
theorem B2927765 : Blo 1733067 2927765 := bbase (se 6 (by rfl) ⟨68619, by rfl⟩ : syracuseStep 2927765 = 137239) (by norm_num)
theorem B2600093 : Blo 1733067 2600093 := bbase (se 3 (by rfl) ⟨487517, by rfl⟩ : syracuseStep 2600093 = 975035) (by norm_num)
theorem B4451485 : Blo 1733067 4451485 := bbase (se 3 (by rfl) ⟨834653, by rfl⟩ : syracuseStep 4451485 = 1669307) (by norm_num)
theorem B2600117 : Blo 1733067 2600117 := bbase (se 5 (by rfl) ⟨121880, by rfl⟩ : syracuseStep 2600117 = 243761) (by norm_num)
theorem B5852357 : Blo 1733067 5852357 := bbase (se 4 (by rfl) ⟨548658, by rfl⟩ : syracuseStep 5852357 = 1097317) (by norm_num)
theorem B2600141 : Blo 1733067 2600141 := bbase (se 3 (by rfl) ⟨487526, by rfl⟩ : syracuseStep 2600141 = 975053) (by norm_num)
theorem B3902669 : Blo 1733067 3902669 := bbase (se 3 (by rfl) ⟨731750, by rfl⟩ : syracuseStep 3902669 = 1463501) (by norm_num)
theorem B2600165 : Blo 1733067 2600165 := bbase (se 4 (by rfl) ⟨243765, by rfl⟩ : syracuseStep 2600165 = 487531) (by norm_num)
theorem B5270773 : Blo 1733067 5270773 := bbase (se 5 (by rfl) ⟨247067, by rfl⟩ : syracuseStep 5270773 = 494135) (by norm_num)
theorem B2600189 : Blo 1733067 2600189 := bbase (se 3 (by rfl) ⟨487535, by rfl⟩ : syracuseStep 2600189 = 975071) (by norm_num)
theorem B2600213 : Blo 1733067 2600213 := bbase (se 6 (by rfl) ⟨60942, by rfl⟩ : syracuseStep 2600213 = 121885) (by norm_num)
theorem B3902741 : Blo 1733067 3902741 := bbase (se 6 (by rfl) ⟨91470, by rfl⟩ : syracuseStep 3902741 = 182941) (by norm_num)
theorem B2927893 : Blo 1733067 2927893 := bbase (se 6 (by rfl) ⟨68622, by rfl⟩ : syracuseStep 2927893 = 137245) (by norm_num)
theorem B8776997 : Blo 1733067 8776997 := bbase (se 4 (by rfl) ⟨822843, by rfl⟩ : syracuseStep 8776997 = 1645687) (by norm_num)
theorem B2600237 : Blo 1733067 2600237 := bbase (se 3 (by rfl) ⟨487544, by rfl⟩ : syracuseStep 2600237 = 975089) (by norm_num)
theorem B2600261 : Blo 1733067 2600261 := bbase (se 4 (by rfl) ⟨243774, by rfl⟩ : syracuseStep 2600261 = 487549) (by norm_num)
theorem B2223445 : Blo 1733067 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B2600285 : Blo 1733067 2600285 := bbase (se 3 (by rfl) ⟨487553, by rfl⟩ : syracuseStep 2600285 = 975107) (by norm_num)
theorem B3902813 : Blo 1733067 3902813 := bbase (se 3 (by rfl) ⟨731777, by rfl⟩ : syracuseStep 3902813 = 1463555) (by norm_num)
theorem B2600309 : Blo 1733067 2600309 := bbase (se 5 (by rfl) ⟨121889, by rfl⟩ : syracuseStep 2600309 = 243779) (by norm_num)
theorem B2600333 : Blo 1733067 2600333 := bbase (se 3 (by rfl) ⟨487562, by rfl⟩ : syracuseStep 2600333 = 975125) (by norm_num)
theorem B5270933 : Blo 1733067 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B2600357 : Blo 1733067 2600357 := bbase (se 4 (by rfl) ⟨243783, by rfl⟩ : syracuseStep 2600357 = 487567) (by norm_num)
theorem B3902885 : Blo 1733067 3902885 := bbase (se 4 (by rfl) ⟨365895, by rfl⟩ : syracuseStep 3902885 = 731791) (by norm_num)
theorem B2600381 : Blo 1733067 2600381 := bbase (se 3 (by rfl) ⟨487571, by rfl⟩ : syracuseStep 2600381 = 975143) (by norm_num)
theorem B2600405 : Blo 1733067 2600405 := bbase (se 7 (by rfl) ⟨30473, by rfl⟩ : syracuseStep 2600405 = 60947) (by norm_num)
theorem B2600429 : Blo 1733067 2600429 := bbase (se 3 (by rfl) ⟨487580, by rfl⟩ : syracuseStep 2600429 = 975161) (by norm_num)
theorem B3902957 : Blo 1733067 3902957 := bbase (se 3 (by rfl) ⟨731804, by rfl⟩ : syracuseStep 3902957 = 1463609) (by norm_num)
theorem B2600453 : Blo 1733067 2600453 := bbase (se 4 (by rfl) ⟨243792, by rfl⟩ : syracuseStep 2600453 = 487585) (by norm_num)
theorem B2600477 : Blo 1733067 2600477 := bbase (se 3 (by rfl) ⟨487589, by rfl⟩ : syracuseStep 2600477 = 975179) (by norm_num)
theorem B2600501 : Blo 1733067 2600501 := bbase (se 5 (by rfl) ⟨121898, by rfl⟩ : syracuseStep 2600501 = 243797) (by norm_num)
theorem B3903029 : Blo 1733067 3903029 := bbase (se 5 (by rfl) ⟨182954, by rfl⟩ : syracuseStep 3903029 = 365909) (by norm_num)
theorem B2600525 : Blo 1733067 2600525 := bbase (se 3 (by rfl) ⟨487598, by rfl⟩ : syracuseStep 2600525 = 975197) (by norm_num)
theorem B2600549 : Blo 1733067 2600549 := bbase (se 4 (by rfl) ⟨243801, by rfl⟩ : syracuseStep 2600549 = 487603) (by norm_num)
theorem B4689509 : Blo 1733067 4689509 := bbase (se 4 (by rfl) ⟨439641, by rfl⟩ : syracuseStep 4689509 = 879283) (by norm_num)
theorem B5852789 : Blo 1733067 5852789 := bbase (se 5 (by rfl) ⟨274349, by rfl⟩ : syracuseStep 5852789 = 548699) (by norm_num)
theorem B2600573 : Blo 1733067 2600573 := bbase (se 3 (by rfl) ⟨487607, by rfl⟩ : syracuseStep 2600573 = 975215) (by norm_num)
theorem B3903101 : Blo 1733067 3903101 := bbase (se 3 (by rfl) ⟨731831, by rfl⟩ : syracuseStep 3903101 = 1463663) (by norm_num)
theorem B2600597 : Blo 1733067 2600597 := bbase (se 6 (by rfl) ⟨60951, by rfl⟩ : syracuseStep 2600597 = 121903) (by norm_num)
theorem B2469533 : Blo 1733067 2469533 := bbase (se 3 (by rfl) ⟨463037, by rfl⟩ : syracuseStep 2469533 = 926075) (by norm_num)
theorem B2600621 : Blo 1733067 2600621 := bbase (se 3 (by rfl) ⟨487616, by rfl⟩ : syracuseStep 2600621 = 975233) (by norm_num)
theorem B2600645 : Blo 1733067 2600645 := bbase (se 4 (by rfl) ⟨243810, by rfl⟩ : syracuseStep 2600645 = 487621) (by norm_num)
theorem B3903173 : Blo 1733067 3903173 := bbase (se 4 (by rfl) ⟨365922, by rfl⟩ : syracuseStep 3903173 = 731845) (by norm_num)
theorem B8335061 : Blo 1733067 8335061 := bbase (se 7 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 8335061 = 195353) (by norm_num)
theorem B2600669 : Blo 1733067 2600669 := bbase (se 3 (by rfl) ⟨487625, by rfl⟩ : syracuseStep 2600669 = 975251) (by norm_num)
theorem B6582005 : Blo 1733067 6582005 := bbase (se 5 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 6582005 = 617063) (by norm_num)
theorem B2600693 : Blo 1733067 2600693 := bbase (se 5 (by rfl) ⟨121907, by rfl⟩ : syracuseStep 2600693 = 243815) (by norm_num)
theorem B1756937 : Blo 1733067 1756937 := bbase (se 2 (by rfl) ⟨658851, by rfl⟩ : syracuseStep 1756937 = 1317703) (by norm_num)
theorem B2600717 : Blo 1733067 2600717 := bbase (se 3 (by rfl) ⟨487634, by rfl⟩ : syracuseStep 2600717 = 975269) (by norm_num)
theorem B3903245 : Blo 1733067 3903245 := bbase (se 3 (by rfl) ⟨731858, by rfl⟩ : syracuseStep 3903245 = 1463717) (by norm_num)
theorem B2600741 : Blo 1733067 2600741 := bbase (se 4 (by rfl) ⟨243819, by rfl⟩ : syracuseStep 2600741 = 487639) (by norm_num)
theorem B2600765 : Blo 1733067 2600765 := bbase (se 3 (by rfl) ⟨487643, by rfl⟩ : syracuseStep 2600765 = 975287) (by norm_num)
theorem B2600789 : Blo 1733067 2600789 := bbase (se 9 (by rfl) ⟨7619, by rfl⟩ : syracuseStep 2600789 = 15239) (by norm_num)
theorem B3903317 : Blo 1733067 3903317 := bbase (se 9 (by rfl) ⟨11435, by rfl⟩ : syracuseStep 3903317 = 22871) (by norm_num)
theorem B2600813 : Blo 1733067 2600813 := bbase (se 3 (by rfl) ⟨487652, by rfl⟩ : syracuseStep 2600813 = 975305) (by norm_num)
theorem B6246277 : Blo 1733067 6246277 := bbase (se 4 (by rfl) ⟨585588, by rfl⟩ : syracuseStep 6246277 = 1171177) (by norm_num)
theorem B2600837 : Blo 1733067 2600837 := bbase (se 4 (by rfl) ⟨243828, by rfl⟩ : syracuseStep 2600837 = 487657) (by norm_num)
theorem B2600861 : Blo 1733067 2600861 := bbase (se 3 (by rfl) ⟨487661, by rfl⟩ : syracuseStep 2600861 = 975323) (by norm_num)
theorem B3903389 : Blo 1733067 3903389 := bbase (se 3 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 3903389 = 1463771) (by norm_num)
theorem B2600885 : Blo 1733067 2600885 := bbase (se 5 (by rfl) ⟨121916, by rfl⟩ : syracuseStep 2600885 = 243833) (by norm_num)
theorem B2600909 : Blo 1733067 2600909 := bbase (se 3 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 2600909 = 975341) (by norm_num)
theorem B2600933 : Blo 1733067 2600933 := bbase (se 4 (by rfl) ⟨243837, by rfl⟩ : syracuseStep 2600933 = 487675) (by norm_num)
theorem B3903461 : Blo 1733067 3903461 := bbase (se 4 (by rfl) ⟨365949, by rfl⟩ : syracuseStep 3903461 = 731899) (by norm_num)
theorem B2600957 : Blo 1733067 2600957 := bbase (se 3 (by rfl) ⟨487679, by rfl⟩ : syracuseStep 2600957 = 975359) (by norm_num)
theorem B13340693 : Blo 1733067 13340693 := bbase (se 6 (by rfl) ⟨312672, by rfl⟩ : syracuseStep 13340693 = 625345) (by norm_num)
theorem B22212629 : Blo 1733067 22212629 := bbase (se 6 (by rfl) ⟨520608, by rfl⟩ : syracuseStep 22212629 = 1041217) (by norm_num)
theorem B6582293 : Blo 1733067 6582293 := bbase (se 6 (by rfl) ⟨154272, by rfl⟩ : syracuseStep 6582293 = 308545) (by norm_num)
theorem B2600981 : Blo 1733067 2600981 := bbase (se 6 (by rfl) ⟨60960, by rfl⟩ : syracuseStep 2600981 = 121921) (by norm_num)
theorem B5853221 : Blo 1733067 5853221 := bbase (se 4 (by rfl) ⟨548739, by rfl⟩ : syracuseStep 5853221 = 1097479) (by norm_num)
theorem B2601005 : Blo 1733067 2601005 := bbase (se 3 (by rfl) ⟨487688, by rfl⟩ : syracuseStep 2601005 = 975377) (by norm_num)
theorem B3903533 : Blo 1733067 3903533 := bbase (se 3 (by rfl) ⟨731912, by rfl⟩ : syracuseStep 3903533 = 1463825) (by norm_num)
theorem B4386869 : Blo 1733067 4386869 := bbase (se 5 (by rfl) ⟨205634, by rfl⟩ : syracuseStep 4386869 = 411269) (by norm_num)
theorem B4165685 : Blo 1733067 4165685 := bbase (se 5 (by rfl) ⟨195266, by rfl⟩ : syracuseStep 4165685 = 390533) (by norm_num)
theorem B2601029 : Blo 1733067 2601029 := bbase (se 4 (by rfl) ⟨243846, by rfl⟩ : syracuseStep 2601029 = 487693) (by norm_num)
theorem B2601053 : Blo 1733067 2601053 := bbase (se 3 (by rfl) ⟨487697, by rfl⟩ : syracuseStep 2601053 = 975395) (by norm_num)
theorem B2601077 : Blo 1733067 2601077 := bbase (se 5 (by rfl) ⟨121925, by rfl⟩ : syracuseStep 2601077 = 243851) (by norm_num)
theorem B3903605 : Blo 1733067 3903605 := bbase (se 5 (by rfl) ⟨182981, by rfl⟩ : syracuseStep 3903605 = 365963) (by norm_num)
theorem B2601101 : Blo 1733067 2601101 := bbase (se 3 (by rfl) ⟨487706, by rfl⟩ : syracuseStep 2601101 = 975413) (by norm_num)
theorem B2601125 : Blo 1733067 2601125 := bbase (se 4 (by rfl) ⟨243855, by rfl⟩ : syracuseStep 2601125 = 487711) (by norm_num)
theorem B2601149 : Blo 1733067 2601149 := bbase (se 3 (by rfl) ⟨487715, by rfl⟩ : syracuseStep 2601149 = 975431) (by norm_num)
theorem B3903677 : Blo 1733067 3903677 := bbase (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) (by norm_num)
theorem B2601173 : Blo 1733067 2601173 := bbase (se 7 (by rfl) ⟨30482, by rfl⟩ : syracuseStep 2601173 = 60965) (by norm_num)
theorem B2601197 : Blo 1733067 2601197 := bbase (se 3 (by rfl) ⟨487724, by rfl⟩ : syracuseStep 2601197 = 975449) (by norm_num)
theorem B4387061 : Blo 1733067 4387061 := bbase (se 5 (by rfl) ⟨205643, by rfl⟩ : syracuseStep 4387061 = 411287) (by norm_num)
theorem B4165877 : Blo 1733067 4165877 := bbase (se 5 (by rfl) ⟨195275, by rfl⟩ : syracuseStep 4165877 = 390551) (by norm_num)
theorem B2601221 : Blo 1733067 2601221 := bbase (se 4 (by rfl) ⟨243864, by rfl⟩ : syracuseStep 2601221 = 487729) (by norm_num)
theorem B3903749 : Blo 1733067 3903749 := bbase (se 4 (by rfl) ⟨365976, by rfl⟩ : syracuseStep 3903749 = 731953) (by norm_num)
theorem B2601245 : Blo 1733067 2601245 := bbase (se 3 (by rfl) ⟨487733, by rfl⟩ : syracuseStep 2601245 = 975467) (by norm_num)
theorem B2601269 : Blo 1733067 2601269 := bbase (se 5 (by rfl) ⟨121934, by rfl⟩ : syracuseStep 2601269 = 243869) (by norm_num)
theorem B2601293 : Blo 1733067 2601293 := bbase (se 3 (by rfl) ⟨487742, by rfl⟩ : syracuseStep 2601293 = 975485) (by norm_num)
theorem B3903821 : Blo 1733067 3903821 := bbase (se 3 (by rfl) ⟨731966, by rfl⟩ : syracuseStep 3903821 = 1463933) (by norm_num)
theorem B2601317 : Blo 1733067 2601317 := bbase (se 4 (by rfl) ⟨243873, by rfl⟩ : syracuseStep 2601317 = 487747) (by norm_num)
theorem B2601341 : Blo 1733067 2601341 := bbase (se 3 (by rfl) ⟨487751, by rfl⟩ : syracuseStep 2601341 = 975503) (by norm_num)
theorem B5271941 : Blo 1733067 5271941 := bbase (se 4 (by rfl) ⟨494244, by rfl⟩ : syracuseStep 5271941 = 988489) (by norm_num)
theorem B2470285 : Blo 1733067 2470285 := bbase (se 3 (by rfl) ⟨463178, by rfl⟩ : syracuseStep 2470285 = 926357) (by norm_num)
theorem B2601365 : Blo 1733067 2601365 := bbase (se 6 (by rfl) ⟨60969, by rfl⟩ : syracuseStep 2601365 = 121939) (by norm_num)
theorem B3903893 : Blo 1733067 3903893 := bbase (se 6 (by rfl) ⟨91497, by rfl⟩ : syracuseStep 3903893 = 182995) (by norm_num)
theorem B2601389 : Blo 1733067 2601389 := bbase (se 3 (by rfl) ⟨487760, by rfl⟩ : syracuseStep 2601389 = 975521) (by norm_num)
theorem B2601413 : Blo 1733067 2601413 := bbase (se 4 (by rfl) ⟨243882, by rfl⟩ : syracuseStep 2601413 = 487765) (by norm_num)
theorem B5853653 : Blo 1733067 5853653 := bbase (se 7 (by rfl) ⟨68597, by rfl⟩ : syracuseStep 5853653 = 137195) (by norm_num)
theorem B2601437 : Blo 1733067 2601437 := bbase (se 3 (by rfl) ⟨487769, by rfl⟩ : syracuseStep 2601437 = 975539) (by norm_num)
theorem B6509045 : Blo 1733067 6509045 := bbase (se 5 (by rfl) ⟨305111, by rfl⟩ : syracuseStep 6509045 = 610223) (by norm_num)
theorem B13169141 : Blo 1733067 13169141 := bbase (se 5 (by rfl) ⟨617303, by rfl⟩ : syracuseStep 13169141 = 1234607) (by norm_num)
theorem B2601461 : Blo 1733067 2601461 := bbase (se 5 (by rfl) ⟨121943, by rfl⟩ : syracuseStep 2601461 = 243887) (by norm_num)
theorem B2601485 : Blo 1733067 2601485 := bbase (se 3 (by rfl) ⟨487778, by rfl⟩ : syracuseStep 2601485 = 975557) (by norm_num)
theorem B2601509 : Blo 1733067 2601509 := bbase (se 4 (by rfl) ⟨243891, by rfl⟩ : syracuseStep 2601509 = 487783) (by norm_num)
theorem B8778293 : Blo 1733067 8778293 := bbase (se 5 (by rfl) ⟨411482, by rfl⟩ : syracuseStep 8778293 = 822965) (by norm_num)
theorem B2601533 : Blo 1733067 2601533 := bbase (se 3 (by rfl) ⟨487787, by rfl⟩ : syracuseStep 2601533 = 975575) (by norm_num)
theorem B4387405 : Blo 1733067 4387405 := bbase (se 3 (by rfl) ⟨822638, by rfl⟩ : syracuseStep 4387405 = 1645277) (by norm_num)
theorem B2601557 : Blo 1733067 2601557 := bbase (se 8 (by rfl) ⟨15243, by rfl⟩ : syracuseStep 2601557 = 30487) (by norm_num)
theorem B2601581 : Blo 1733067 2601581 := bbase (se 3 (by rfl) ⟨487796, by rfl⟩ : syracuseStep 2601581 = 975593) (by norm_num)
theorem B2601605 : Blo 1733067 2601605 := bbase (se 4 (by rfl) ⟨243900, by rfl⟩ : syracuseStep 2601605 = 487801) (by norm_num)
theorem B2601629 : Blo 1733067 2601629 := bbase (se 3 (by rfl) ⟨487805, by rfl⟩ : syracuseStep 2601629 = 975611) (by norm_num)
theorem B7508645 : Blo 1733067 7508645 := bbase (se 4 (by rfl) ⟨703935, by rfl⟩ : syracuseStep 7508645 = 1407871) (by norm_num)
theorem B2601653 : Blo 1733067 2601653 := bbase (se 5 (by rfl) ⟨121952, by rfl⟩ : syracuseStep 2601653 = 243905) (by norm_num)
theorem B4387517 : Blo 1733067 4387517 := bbase (se 3 (by rfl) ⟨822659, by rfl⟩ : syracuseStep 4387517 = 1645319) (by norm_num)
theorem B2601677 : Blo 1733067 2601677 := bbase (se 3 (by rfl) ⟨487814, by rfl⟩ : syracuseStep 2601677 = 975629) (by norm_num)
theorem B3125965 : Blo 1733067 3125965 := bbase (se 3 (by rfl) ⟨586118, by rfl⟩ : syracuseStep 3125965 = 1172237) (by norm_num)
theorem B2601701 : Blo 1733067 2601701 := bbase (se 4 (by rfl) ⟨243909, by rfl⟩ : syracuseStep 2601701 = 487819) (by norm_num)
theorem B2601725 : Blo 1733067 2601725 := bbase (se 3 (by rfl) ⟨487823, by rfl⟩ : syracuseStep 2601725 = 975647) (by norm_num)
theorem B2601749 : Blo 1733067 2601749 := bbase (se 6 (by rfl) ⟨60978, by rfl⟩ : syracuseStep 2601749 = 121957) (by norm_num)
theorem B2601773 : Blo 1733067 2601773 := bbase (se 3 (by rfl) ⟨487832, by rfl⟩ : syracuseStep 2601773 = 975665) (by norm_num)
theorem B2601797 : Blo 1733067 2601797 := bbase (se 4 (by rfl) ⟨243918, by rfl⟩ : syracuseStep 2601797 = 487837) (by norm_num)
theorem B2601821 : Blo 1733067 2601821 := bbase (se 3 (by rfl) ⟨487841, by rfl⟩ : syracuseStep 2601821 = 975683) (by norm_num)
theorem B3126109 : Blo 1733067 3126109 := bbase (se 3 (by rfl) ⟨586145, by rfl⟩ : syracuseStep 3126109 = 1172291) (by norm_num)
theorem B8123237 : Blo 1733067 8123237 := bbase (se 4 (by rfl) ⟨761553, by rfl⟩ : syracuseStep 8123237 = 1523107) (by norm_num)
theorem B2601845 : Blo 1733067 2601845 := bbase (se 5 (by rfl) ⟨121961, by rfl⟩ : syracuseStep 2601845 = 243923) (by norm_num)
theorem B4387709 : Blo 1733067 4387709 := bbase (se 3 (by rfl) ⟨822695, by rfl⟩ : syracuseStep 4387709 = 1645391) (by norm_num)
theorem B5854085 : Blo 1733067 5854085 := bbase (se 4 (by rfl) ⟨548820, by rfl⟩ : syracuseStep 5854085 = 1097641) (by norm_num)
theorem B2601869 : Blo 1733067 2601869 := bbase (se 3 (by rfl) ⟨487850, by rfl⟩ : syracuseStep 2601869 = 975701) (by norm_num)
theorem B13161365 : Blo 1733067 13161365 := bbase (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) (by norm_num)
theorem B2601893 : Blo 1733067 2601893 := bbase (se 4 (by rfl) ⟨243927, by rfl⟩ : syracuseStep 2601893 = 487855) (by norm_num)
theorem B2601917 : Blo 1733067 2601917 := bbase (se 3 (by rfl) ⟨487859, by rfl⟩ : syracuseStep 2601917 = 975719) (by norm_num)
theorem B2601941 : Blo 1733067 2601941 := bbase (se 7 (by rfl) ⟨30491, by rfl⟩ : syracuseStep 2601941 = 60983) (by norm_num)
theorem B1758169 : Blo 1733067 1758169 := bbase (se 2 (by rfl) ⟨659313, by rfl⟩ : syracuseStep 1758169 = 1318627) (by norm_num)
theorem B2601965 : Blo 1733067 2601965 := bbase (se 3 (by rfl) ⟨487868, by rfl⟩ : syracuseStep 2601965 = 975737) (by norm_num)
theorem B4166645 : Blo 1733067 4166645 := bbase (se 5 (by rfl) ⟨195311, by rfl⟩ : syracuseStep 4166645 = 390623) (by norm_num)
theorem B2601989 : Blo 1733067 2601989 := bbase (se 4 (by rfl) ⟨243936, by rfl⟩ : syracuseStep 2601989 = 487873) (by norm_num)
theorem B2602013 : Blo 1733067 2602013 := bbase (se 3 (by rfl) ⟨487877, by rfl⟩ : syracuseStep 2602013 = 975755) (by norm_num)
theorem B2602037 : Blo 1733067 2602037 := bbase (se 5 (by rfl) ⟨121970, by rfl⟩ : syracuseStep 2602037 = 243941) (by norm_num)
theorem B2602061 : Blo 1733067 2602061 := bbase (se 3 (by rfl) ⟨487886, by rfl⟩ : syracuseStep 2602061 = 975773) (by norm_num)
theorem B3290213 : Blo 1733067 3290213 := bbase (se 4 (by rfl) ⟨308457, by rfl⟩ : syracuseStep 3290213 = 616915) (by norm_num)
theorem B2602085 : Blo 1733067 2602085 := bbase (se 4 (by rfl) ⟨243945, by rfl⟩ : syracuseStep 2602085 = 487891) (by norm_num)
theorem B2602109 : Blo 1733067 2602109 := bbase (se 3 (by rfl) ⟨487895, by rfl⟩ : syracuseStep 2602109 = 975791) (by norm_num)
theorem B7509125 : Blo 1733067 7509125 := bbase (se 4 (by rfl) ⟨703980, by rfl⟩ : syracuseStep 7509125 = 1407961) (by norm_num)
theorem B16888981 : Blo 1733067 16888981 := bbase (se 6 (by rfl) ⟨395835, by rfl⟩ : syracuseStep 16888981 = 791671) (by norm_num)
theorem B2602133 : Blo 1733067 2602133 := bbase (se 6 (by rfl) ⟨60987, by rfl⟩ : syracuseStep 2602133 = 121975) (by norm_num)
theorem B2602157 : Blo 1733067 2602157 := bbase (se 3 (by rfl) ⟨487904, by rfl⟩ : syracuseStep 2602157 = 975809) (by norm_num)
theorem B6583477 : Blo 1733067 6583477 := bbase (se 5 (by rfl) ⟨308600, by rfl⟩ : syracuseStep 6583477 = 617201) (by norm_num)
theorem B2602181 : Blo 1733067 2602181 := bbase (se 4 (by rfl) ⟨243954, by rfl⟩ : syracuseStep 2602181 = 487909) (by norm_num)
theorem B4388053 : Blo 1733067 4388053 := bbase (se 7 (by rfl) ⟨51422, by rfl⟩ : syracuseStep 4388053 = 102845) (by norm_num)
theorem B2602205 : Blo 1733067 2602205 := bbase (se 3 (by rfl) ⟨487913, by rfl⟩ : syracuseStep 2602205 = 975827) (by norm_num)
theorem B2225377 : Blo 1733067 2225377 := bbase (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) (by norm_num)
theorem B3290357 : Blo 1733067 3290357 := bbase (se 5 (by rfl) ⟨154235, by rfl⟩ : syracuseStep 3290357 = 308471) (by norm_num)
theorem B2602229 : Blo 1733067 2602229 := bbase (se 5 (by rfl) ⟨121979, by rfl⟩ : syracuseStep 2602229 = 243959) (by norm_num)
theorem B2602253 : Blo 1733067 2602253 := bbase (se 3 (by rfl) ⟨487922, by rfl⟩ : syracuseStep 2602253 = 975845) (by norm_num)
theorem B2602277 : Blo 1733067 2602277 := bbase (se 4 (by rfl) ⟨243963, by rfl⟩ : syracuseStep 2602277 = 487927) (by norm_num)
theorem B5854517 : Blo 1733067 5854517 := bbase (se 5 (by rfl) ⟨274430, by rfl⟩ : syracuseStep 5854517 = 548861) (by norm_num)
theorem B2225461 : Blo 1733067 2225461 := bbase (se 5 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 2225461 = 208637) (by norm_num)
theorem B2602301 : Blo 1733067 2602301 := bbase (se 3 (by rfl) ⟨487931, by rfl⟩ : syracuseStep 2602301 = 975863) (by norm_num)
theorem B4388165 : Blo 1733067 4388165 := bbase (se 4 (by rfl) ⟨411390, by rfl⟩ : syracuseStep 4388165 = 822781) (by norm_num)
theorem B2602325 : Blo 1733067 2602325 := bbase (se 13 (by rfl) ⟨476, by rfl⟩ : syracuseStep 2602325 = 953) (by norm_num)
theorem B2602349 : Blo 1733067 2602349 := bbase (se 3 (by rfl) ⟨487940, by rfl⟩ : syracuseStep 2602349 = 975881) (by norm_num)
theorem B2602373 : Blo 1733067 2602373 := bbase (se 4 (by rfl) ⟨243972, by rfl⟩ : syracuseStep 2602373 = 487945) (by norm_num)
theorem B2602397 : Blo 1733067 2602397 := bbase (se 3 (by rfl) ⟨487949, by rfl⟩ : syracuseStep 2602397 = 975899) (by norm_num)
theorem B2602421 : Blo 1733067 2602421 := bbase (se 5 (by rfl) ⟨121988, by rfl⟩ : syracuseStep 2602421 = 243977) (by norm_num)
theorem B2602445 : Blo 1733067 2602445 := bbase (se 3 (by rfl) ⟨487958, by rfl⟩ : syracuseStep 2602445 = 975917) (by norm_num)
theorem B6583781 : Blo 1733067 6583781 := bbase (se 4 (by rfl) ⟨617229, by rfl⟩ : syracuseStep 6583781 = 1234459) (by norm_num)
theorem B2602469 : Blo 1733067 2602469 := bbase (se 4 (by rfl) ⟨243981, by rfl⟩ : syracuseStep 2602469 = 487963) (by norm_num)
theorem B2602493 : Blo 1733067 2602493 := bbase (se 3 (by rfl) ⟨487967, by rfl⟩ : syracuseStep 2602493 = 975935) (by norm_num)
theorem B4388357 : Blo 1733067 4388357 := bbase (se 4 (by rfl) ⟨411408, by rfl⟩ : syracuseStep 4388357 = 822817) (by norm_num)
theorem B3290645 : Blo 1733067 3290645 := bbase (se 6 (by rfl) ⟨77124, by rfl⟩ : syracuseStep 3290645 = 154249) (by norm_num)
theorem B14816789 : Blo 1733067 14816789 := bbase (se 6 (by rfl) ⟨347268, by rfl⟩ : syracuseStep 14816789 = 694537) (by norm_num)
theorem B2602517 : Blo 1733067 2602517 := bbase (se 6 (by rfl) ⟨60996, by rfl⟩ : syracuseStep 2602517 = 121993) (by norm_num)
theorem B2602541 : Blo 1733067 2602541 := bbase (se 3 (by rfl) ⟨487976, by rfl⟩ : syracuseStep 2602541 = 975953) (by norm_num)
theorem B8336965 : Blo 1733067 8336965 := bbase (se 4 (by rfl) ⟨781590, by rfl⟩ : syracuseStep 8336965 = 1563181) (by norm_num)
theorem B2602565 : Blo 1733067 2602565 := bbase (se 4 (by rfl) ⟨243990, by rfl⟩ : syracuseStep 2602565 = 487981) (by norm_num)
theorem B8336981 : Blo 1733067 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B2602589 : Blo 1733067 2602589 := bbase (se 3 (by rfl) ⟨487985, by rfl⟩ : syracuseStep 2602589 = 975971) (by norm_num)
theorem B4748933 : Blo 1733067 4748933 := bbase (se 4 (by rfl) ⟨445212, by rfl⟩ : syracuseStep 4748933 = 890425) (by norm_num)
theorem B4937381 : Blo 1733067 4937381 := bbase (se 4 (by rfl) ⟨462879, by rfl⟩ : syracuseStep 4937381 = 925759) (by norm_num)
theorem B3290797 : Blo 1733067 3290797 := bbase (se 3 (by rfl) ⟨617024, by rfl⟩ : syracuseStep 3290797 = 1234049) (by norm_num)
theorem B5002933 : Blo 1733067 5002933 := bbase (se 5 (by rfl) ⟨234512, by rfl⟩ : syracuseStep 5002933 = 469025) (by norm_num)
theorem B5854949 : Blo 1733067 5854949 := bbase (se 4 (by rfl) ⟨548901, by rfl⟩ : syracuseStep 5854949 = 1097803) (by norm_num)
theorem B3954421 : Blo 1733067 3954421 := bbase (se 5 (by rfl) ⟨185363, by rfl⟩ : syracuseStep 3954421 = 370727) (by norm_num)
theorem B8779589 : Blo 1733067 8779589 := bbase (se 4 (by rfl) ⟨823086, by rfl⟩ : syracuseStep 8779589 = 1646173) (by norm_num)
theorem B4388701 : Blo 1733067 4388701 := bbase (se 3 (by rfl) ⟨822881, by rfl⟩ : syracuseStep 4388701 = 1645763) (by norm_num)
theorem B4388813 : Blo 1733067 4388813 := bbase (se 3 (by rfl) ⟨822902, by rfl⟩ : syracuseStep 4388813 = 1645805) (by norm_num)
theorem B5003221 : Blo 1733067 5003221 := bbase (se 7 (by rfl) ⟨58631, by rfl⟩ : syracuseStep 5003221 = 117263) (by norm_num)
theorem B3561437 : Blo 1733067 3561437 := bbase (se 3 (by rfl) ⟨667769, by rfl⟩ : syracuseStep 3561437 = 1335539) (by norm_num)
theorem B3291101 : Blo 1733067 3291101 := bbase (se 3 (by rfl) ⟨617081, by rfl⟩ : syracuseStep 3291101 = 1234163) (by norm_num)
theorem B2816077 : Blo 1733067 2816077 := bbase (se 3 (by rfl) ⟨528014, by rfl⟩ : syracuseStep 2816077 = 1056029) (by norm_num)
theorem B4389005 : Blo 1733067 4389005 := bbase (se 3 (by rfl) ⟨822938, by rfl⟩ : syracuseStep 4389005 = 1645877) (by norm_num)
theorem B5855381 : Blo 1733067 5855381 := bbase (se 6 (by rfl) ⟨137235, by rfl⟩ : syracuseStep 5855381 = 274471) (by norm_num)
theorem B2193581 : Blo 1733067 2193581 := bbase (se 3 (by rfl) ⟨411296, by rfl⟩ : syracuseStep 2193581 = 822593) (by norm_num)
theorem B2193637 : Blo 1733067 2193637 := bbase (se 4 (by rfl) ⟨205653, by rfl⟩ : syracuseStep 2193637 = 411307) (by norm_num)
theorem B2193733 : Blo 1733067 2193733 := bbase (se 4 (by rfl) ⟨205662, by rfl⟩ : syracuseStep 2193733 = 411325) (by norm_num)
theorem B8444341 : Blo 1733067 8444341 := bbase (se 5 (by rfl) ⟨395828, by rfl⟩ : syracuseStep 8444341 = 791657) (by norm_num)
theorem B26442197 : Blo 1733067 26442197 := bbase (se 7 (by rfl) ⟨309869, by rfl⟩ : syracuseStep 26442197 = 619739) (by norm_num)
theorem B6248933 : Blo 1733067 6248933 := bbase (se 4 (by rfl) ⟨585837, by rfl⟩ : syracuseStep 6248933 = 1171675) (by norm_num)
theorem B4389349 : Blo 1733067 4389349 := bbase (se 4 (by rfl) ⟨411501, by rfl⟩ : syracuseStep 4389349 = 823003) (by norm_num)
theorem B2193905 : Blo 1733067 2193905 := bbase (se 2 (by rfl) ⟨822714, by rfl⟩ : syracuseStep 2193905 = 1645429) (by norm_num)
theorem B4446733 : Blo 1733067 4446733 := bbase (se 3 (by rfl) ⟨833762, by rfl⟩ : syracuseStep 4446733 = 1667525) (by norm_num)
theorem B2636317 : Blo 1733067 2636317 := bbase (se 3 (by rfl) ⟨494309, by rfl⟩ : syracuseStep 2636317 = 988619) (by norm_num)
theorem B2193961 : Blo 1733067 2193961 := bbase (se 2 (by rfl) ⟨822735, by rfl⟩ : syracuseStep 2193961 = 1645471) (by norm_num)
theorem B16661045 : Blo 1733067 16661045 := bbase (se 5 (by rfl) ⟨780986, by rfl⟩ : syracuseStep 16661045 = 1561973) (by norm_num)
theorem B5855813 : Blo 1733067 5855813 := bbase (se 4 (by rfl) ⟨548982, by rfl⟩ : syracuseStep 5855813 = 1097965) (by norm_num)
theorem B4389461 : Blo 1733067 4389461 := bbase (se 8 (by rfl) ⟨25719, by rfl⟩ : syracuseStep 4389461 = 51439) (by norm_num)
theorem B2194057 : Blo 1733067 2194057 := bbase (se 2 (by rfl) ⟨822771, by rfl⟩ : syracuseStep 2194057 = 1645543) (by norm_num)
theorem B3291853 : Blo 1733067 3291853 := bbase (se 3 (by rfl) ⟨617222, by rfl⟩ : syracuseStep 3291853 = 1234445) (by norm_num)
theorem B6249221 : Blo 1733067 6249221 := bbase (se 4 (by rfl) ⟨585864, by rfl⟩ : syracuseStep 6249221 = 1171729) (by norm_num)
theorem B4389653 : Blo 1733067 4389653 := bbase (se 6 (by rfl) ⟨102882, by rfl⟩ : syracuseStep 4389653 = 205765) (by norm_num)
theorem B2194229 : Blo 1733067 2194229 := bbase (se 5 (by rfl) ⟨102854, by rfl⟩ : syracuseStep 2194229 = 205709) (by norm_num)
theorem B4938565 : Blo 1733067 4938565 := bbase (se 4 (by rfl) ⟨462990, by rfl⟩ : syracuseStep 4938565 = 925981) (by norm_num)
theorem B3291997 : Blo 1733067 3291997 := bbase (se 3 (by rfl) ⟨617249, by rfl⟩ : syracuseStep 3291997 = 1234499) (by norm_num)
theorem B4684645 : Blo 1733067 4684645 := bbase (se 4 (by rfl) ⟨439185, by rfl⟩ : syracuseStep 4684645 = 878371) (by norm_num)
theorem B2194285 : Blo 1733067 2194285 := bbase (se 3 (by rfl) ⟨411428, by rfl⟩ : syracuseStep 2194285 = 822857) (by norm_num)
theorem B11115413 : Blo 1733067 11115413 := bbase (se 6 (by rfl) ⟨260517, by rfl⟩ : syracuseStep 11115413 = 521035) (by norm_num)
theorem B2194381 : Blo 1733067 2194381 := bbase (se 3 (by rfl) ⟨411446, by rfl⟩ : syracuseStep 2194381 = 822893) (by norm_num)
theorem B4938725 : Blo 1733067 4938725 := bbase (se 4 (by rfl) ⟨463005, by rfl⟩ : syracuseStep 4938725 = 926011) (by norm_num)
theorem B3292157 : Blo 1733067 3292157 := bbase (se 3 (by rfl) ⟨617279, by rfl⟩ : syracuseStep 3292157 = 1234559) (by norm_num)
theorem B4168741 : Blo 1733067 4168741 := bbase (se 4 (by rfl) ⟨390819, by rfl⟩ : syracuseStep 4168741 = 781639) (by norm_num)
theorem B8780885 : Blo 1733067 8780885 := bbase (se 8 (by rfl) ⟨51450, by rfl⟩ : syracuseStep 8780885 = 102901) (by norm_num)
theorem B4389997 : Blo 1733067 4389997 := bbase (se 3 (by rfl) ⟨823124, by rfl⟩ : syracuseStep 4389997 = 1646249) (by norm_num)
theorem B2194553 : Blo 1733067 2194553 := bbase (se 2 (by rfl) ⟨822957, by rfl⟩ : syracuseStep 2194553 = 1645915) (by norm_num)
theorem B3292301 : Blo 1733067 3292301 := bbase (se 3 (by rfl) ⟨617306, by rfl⟩ : syracuseStep 3292301 = 1234613) (by norm_num)
theorem B2194609 : Blo 1733067 2194609 := bbase (se 2 (by rfl) ⟨822978, by rfl⟩ : syracuseStep 2194609 = 1645957) (by norm_num)
theorem B4447429 : Blo 1733067 4447429 := bbase (se 4 (by rfl) ⟨416946, by rfl⟩ : syracuseStep 4447429 = 833893) (by norm_num)
theorem B4938965 : Blo 1733067 4938965 := bbase (se 7 (by rfl) ⟨57878, by rfl⟩ : syracuseStep 4938965 = 115757) (by norm_num)
theorem B4390109 : Blo 1733067 4390109 := bbase (se 3 (by rfl) ⟨823145, by rfl⟩ : syracuseStep 4390109 = 1646291) (by norm_num)
theorem B2194705 : Blo 1733067 2194705 := bbase (se 2 (by rfl) ⟨823014, by rfl⟩ : syracuseStep 2194705 = 1646029) (by norm_num)
theorem B3702037 : Blo 1733067 3702037 := bbase (se 6 (by rfl) ⟨86766, by rfl⟩ : syracuseStep 3702037 = 173533) (by norm_num)
theorem B7028005 : Blo 1733067 7028005 := bbase (se 4 (by rfl) ⟨658875, by rfl⟩ : syracuseStep 7028005 = 1317751) (by norm_num)
theorem B4685141 : Blo 1733067 4685141 := bbase (se 11 (by rfl) ⟨3431, by rfl⟩ : syracuseStep 4685141 = 6863) (by norm_num)
theorem B4939157 : Blo 1733067 4939157 := bbase (se 6 (by rfl) ⟨115761, by rfl⟩ : syracuseStep 4939157 = 231523) (by norm_num)
theorem B4390301 : Blo 1733067 4390301 := bbase (se 3 (by rfl) ⟨823181, by rfl⟩ : syracuseStep 4390301 = 1646363) (by norm_num)
theorem B3702181 : Blo 1733067 3702181 := bbase (se 4 (by rfl) ⟨347079, by rfl⟩ : syracuseStep 3702181 = 694159) (by norm_num)
theorem B3292589 : Blo 1733067 3292589 := bbase (se 3 (by rfl) ⟨617360, by rfl⟩ : syracuseStep 3292589 = 1234721) (by norm_num)
theorem B2194877 : Blo 1733067 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B2194933 : Blo 1733067 2194933 := bbase (se 5 (by rfl) ⟨102887, by rfl⟩ : syracuseStep 2194933 = 205775) (by norm_num)
theorem B6585893 : Blo 1733067 6585893 := bbase (se 4 (by rfl) ⟨617427, by rfl⟩ : syracuseStep 6585893 = 1234855) (by norm_num)
theorem B3292741 : Blo 1733067 3292741 := bbase (se 4 (by rfl) ⟨308694, by rfl⟩ : syracuseStep 3292741 = 617389) (by norm_num)
theorem B2195029 : Blo 1733067 2195029 := bbase (se 8 (by rfl) ⟨12861, by rfl⟩ : syracuseStep 2195029 = 25723) (by norm_num)
theorem B6250085 : Blo 1733067 6250085 := bbase (se 4 (by rfl) ⟨585945, by rfl⟩ : syracuseStep 6250085 = 1171891) (by norm_num)
theorem B5004965 : Blo 1733067 5004965 := bbase (se 4 (by rfl) ⟨469215, by rfl⟩ : syracuseStep 5004965 = 938431) (by norm_num)
theorem B3956437 : Blo 1733067 3956437 := bbase (se 7 (by rfl) ⟨46364, by rfl⟩ : syracuseStep 3956437 = 92729) (by norm_num)
theorem B1851121 : Blo 1733067 1851121 := bbase (se 2 (by rfl) ⟨694170, by rfl⟩ : syracuseStep 1851121 = 1388341) (by norm_num)
theorem B4390645 : Blo 1733067 4390645 := bbase (se 5 (by rfl) ⟨205811, by rfl⟩ : syracuseStep 4390645 = 411623) (by norm_num)
theorem B2195201 : Blo 1733067 2195201 := bbase (se 2 (by rfl) ⟨823200, by rfl⟩ : syracuseStep 2195201 = 1646401) (by norm_num)
theorem B3514117 : Blo 1733067 3514117 := bbase (se 4 (by rfl) ⟨329448, by rfl⟩ : syracuseStep 3514117 = 658897) (by norm_num)
theorem B9879317 : Blo 1733067 9879317 := bbase (se 6 (by rfl) ⟨231546, by rfl⟩ : syracuseStep 9879317 = 463093) (by norm_num)
theorem B3702557 : Blo 1733067 3702557 := bbase (se 3 (by rfl) ⟨694229, by rfl⟩ : syracuseStep 3702557 = 1388459) (by norm_num)
theorem B1851193 : Blo 1733067 1851193 := bbase (se 2 (by rfl) ⟨694197, by rfl⟩ : syracuseStep 1851193 = 1388395) (by norm_num)
theorem B2195257 : Blo 1733067 2195257 := bbase (se 2 (by rfl) ⟨823221, by rfl⟩ : syracuseStep 2195257 = 1646443) (by norm_num)
theorem B6586181 : Blo 1733067 6586181 := bbase (se 4 (by rfl) ⟨617454, by rfl⟩ : syracuseStep 6586181 = 1234909) (by norm_num)
theorem B4390757 : Blo 1733067 4390757 := bbase (se 4 (by rfl) ⟨411633, by rfl⟩ : syracuseStep 4390757 = 823267) (by norm_num)
theorem B3293045 : Blo 1733067 3293045 := bbase (se 5 (by rfl) ⟨154361, by rfl⟩ : syracuseStep 3293045 = 308723) (by norm_num)
theorem B3383165 : Blo 1733067 3383165 := bbase (se 3 (by rfl) ⟨634343, by rfl⟩ : syracuseStep 3383165 = 1268687) (by norm_num)
theorem B9871253 : Blo 1733067 9871253 := bbase (se 6 (by rfl) ⟨231357, by rfl⟩ : syracuseStep 9871253 = 462715) (by norm_num)
theorem B2195353 : Blo 1733067 2195353 := bbase (se 2 (by rfl) ⟨823257, by rfl⟩ : syracuseStep 2195353 = 1646515) (by norm_num)
theorem B2777021 : Blo 1733067 2777021 := bbase (se 3 (by rfl) ⟨520691, by rfl⟩ : syracuseStep 2777021 = 1041383) (by norm_num)
theorem B1851373 : Blo 1733067 1851373 := bbase (se 3 (by rfl) ⟨347132, by rfl⟩ : syracuseStep 1851373 = 694265) (by norm_num)
theorem B21102605 : Blo 1733067 21102605 := bstep (se 3 (by rfl) ⟨3956738, by rfl⟩ : syracuseStep 21102605 = 7913477) B7913477
theorem B2924579 : Blo 1733067 2924579 := bstep (se 1 (by rfl) ⟨2193434, by rfl⟩ : syracuseStep 2924579 = 4386869) B4386869
theorem B2777123 : Blo 1733067 2777123 := bstep (se 1 (by rfl) ⟨2082842, by rfl⟩ : syracuseStep 2777123 = 4165685) B4165685
theorem B1949827 : Blo 1733067 1949827 := bstep (se 1 (by rfl) ⟨1462370, by rfl⟩ : syracuseStep 1949827 = 2924741) B2924741
theorem B3899537 : Blo 1733067 3899537 := bstep (se 2 (by rfl) ⟨1462326, by rfl⟩ : syracuseStep 3899537 = 2924653) B2924653
theorem B3899555 : Blo 1733067 3899555 := bstep (se 1 (by rfl) ⟨2924666, by rfl⟩ : syracuseStep 3899555 = 5849333) B5849333
theorem B2924707 : Blo 1733067 2924707 := bstep (se 1 (by rfl) ⟨2193530, by rfl⟩ : syracuseStep 2924707 = 4387061) B4387061
theorem B2777251 : Blo 1733067 2777251 := bstep (se 1 (by rfl) ⟨2082938, by rfl⟩ : syracuseStep 2777251 = 4165877) B4165877
theorem B11108593 : Blo 1733067 11108593 := bstep (se 2 (by rfl) ⟨4165722, by rfl⟩ : syracuseStep 11108593 = 8331445) B8331445
theorem B3514627 : Blo 1733067 3514627 := bstep (se 1 (by rfl) ⟨2635970, by rfl⟩ : syracuseStep 3514627 = 5271941) B5271941
theorem B1949971 : Blo 1733067 1949971 := bstep (se 1 (by rfl) ⟨1462478, by rfl⟩ : syracuseStep 1949971 = 2924957) B2924957
theorem B2343187 : Blo 1733067 2343187 := bstep (se 1 (by rfl) ⟨1757390, by rfl⟩ : syracuseStep 2343187 = 3514781) B3514781
theorem B2924849 : Blo 1733067 2924849 := bstep (se 2 (by rfl) ⟨1096818, by rfl⟩ : syracuseStep 2924849 = 2193637) B2193637
theorem B7405901 : Blo 1733067 7405901 := bstep (se 3 (by rfl) ⟨1388606, by rfl⟩ : syracuseStep 7405901 = 2777213) B2777213
theorem B4686179 : Blo 1733067 4686179 := bstep (se 1 (by rfl) ⟨3514634, by rfl⟩ : syracuseStep 4686179 = 7029269) B7029269
theorem B1950115 : Blo 1733067 1950115 := bstep (se 1 (by rfl) ⟨1462586, by rfl⟩ : syracuseStep 1950115 = 2925173) B2925173
theorem B3899825 : Blo 1733067 3899825 := bstep (se 2 (by rfl) ⟨1462434, by rfl⟩ : syracuseStep 3899825 = 2924869) B2924869
theorem B2924977 : Blo 1733067 2924977 := bstep (se 2 (by rfl) ⟨1096866, by rfl⟩ : syracuseStep 2924977 = 2193733) B2193733
theorem B3899843 : Blo 1733067 3899843 := bstep (se 1 (by rfl) ⟨2924882, by rfl⟩ : syracuseStep 3899843 = 5849765) B5849765
theorem B5005763 : Blo 1733067 5005763 := bstep (se 1 (by rfl) ⟨3754322, by rfl⟩ : syracuseStep 5005763 = 7508645) B7508645
theorem B5849549 : Blo 1733067 5849549 := bstep (se 3 (by rfl) ⟨1096790, by rfl⟩ : syracuseStep 5849549 = 2193581) B2193581
theorem B2925011 : Blo 1733067 2925011 := bstep (se 1 (by rfl) ⟨2193758, by rfl⟩ : syracuseStep 2925011 = 4387517) B4387517
theorem B6586865 : Blo 1733067 6586865 := bstep (se 2 (by rfl) ⟨2470074, by rfl⟩ : syracuseStep 6586865 = 4940149) B4940149
theorem B5849603 : Blo 1733067 5849603 := bstep (se 1 (by rfl) ⟨4387202, by rfl⟩ : syracuseStep 5849603 = 8774405) B8774405
theorem B3293713 : Blo 1733067 3293713 := bstep (se 2 (by rfl) ⟨1235142, by rfl⟩ : syracuseStep 3293713 = 2470285) B2470285
theorem B1950259 : Blo 1733067 1950259 := bstep (se 1 (by rfl) ⟨1462694, by rfl⟩ : syracuseStep 1950259 = 2925389) B2925389
theorem B5415491 : Blo 1733067 5415491 := bstep (se 1 (by rfl) ⟨4061618, by rfl⟩ : syracuseStep 5415491 = 8123237) B8123237
theorem B4940365 : Blo 1733067 4940365 := bstep (se 3 (by rfl) ⟨926318, by rfl⟩ : syracuseStep 4940365 = 1852637) B1852637
theorem B2925139 : Blo 1733067 2925139 := bstep (se 1 (by rfl) ⟨2193854, by rfl⟩ : syracuseStep 2925139 = 4387709) B4387709
theorem B8774243 : Blo 1733067 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B1950403 : Blo 1733067 1950403 := bstep (se 1 (by rfl) ⟨1462802, by rfl⟩ : syracuseStep 1950403 = 2925605) B2925605
theorem B13165253 : Blo 1733067 13165253 := bstep (se 4 (by rfl) ⟨1234242, by rfl⟩ : syracuseStep 13165253 = 2468485) B2468485
theorem B21422789 : Blo 1733067 21422789 := bstep (se 4 (by rfl) ⟨2008386, by rfl⟩ : syracuseStep 21422789 = 4016773) B4016773
theorem B3900113 : Blo 1733067 3900113 := bstep (se 2 (by rfl) ⟨1462542, by rfl⟩ : syracuseStep 3900113 = 2925085) B2925085
theorem B3515089 : Blo 1733067 3515089 := bstep (se 2 (by rfl) ⟨1318158, by rfl⟩ : syracuseStep 3515089 = 2636317) B2636317
theorem B2777809 : Blo 1733067 2777809 := bstep (se 2 (by rfl) ⟨1041678, by rfl⟩ : syracuseStep 2777809 = 2083357) B2083357
theorem B2925281 : Blo 1733067 2925281 := bstep (se 2 (by rfl) ⟨1096980, by rfl⟩ : syracuseStep 2925281 = 2193961) B2193961
theorem B3900131 : Blo 1733067 3900131 := bstep (se 1 (by rfl) ⟨2925098, by rfl⟩ : syracuseStep 3900131 = 5850197) B5850197
theorem B5849873 : Blo 1733067 5849873 := bstep (se 2 (by rfl) ⟨2193702, by rfl⟩ : syracuseStep 5849873 = 4387405) B4387405
theorem B4391729 : Blo 1733067 4391729 := bstep (se 2 (by rfl) ⟨1646898, by rfl⟩ : syracuseStep 4391729 = 3293797) B3293797
theorem B1950547 : Blo 1733067 1950547 := bstep (se 1 (by rfl) ⟨1462910, by rfl⟩ : syracuseStep 1950547 = 2925821) B2925821
theorem B2925409 : Blo 1733067 2925409 := bstep (se 2 (by rfl) ⟨1097028, by rfl⟩ : syracuseStep 2925409 = 2194057) B2194057
theorem B4391779 : Blo 1733067 4391779 := bstep (se 1 (by rfl) ⟨3293834, by rfl⟩ : syracuseStep 4391779 = 6587669) B6587669
theorem B15827825 : Blo 1733067 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B2925443 : Blo 1733067 2925443 := bstep (se 1 (by rfl) ⟨2194082, by rfl⟩ : syracuseStep 2925443 = 4388165) B4388165
theorem B12493709 : Blo 1733067 12493709 := bstep (se 3 (by rfl) ⟨2342570, by rfl⟩ : syracuseStep 12493709 = 4685141) B4685141
theorem B5555117 : Blo 1733067 5555117 := bstep (se 3 (by rfl) ⟨1041584, by rfl⟩ : syracuseStep 5555117 = 2083169) B2083169
theorem B1852355 : Blo 1733067 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B1950691 : Blo 1733067 1950691 := bstep (se 1 (by rfl) ⟨1463018, by rfl⟩ : syracuseStep 1950691 = 2926037) B2926037
theorem B3900401 : Blo 1733067 3900401 := bstep (se 2 (by rfl) ⟨1462650, by rfl⟩ : syracuseStep 3900401 = 2925301) B2925301
theorem B3900419 : Blo 1733067 3900419 := bstep (se 1 (by rfl) ⟨2925314, by rfl⟩ : syracuseStep 3900419 = 5850629) B5850629
theorem B2925571 : Blo 1733067 2925571 := bstep (se 1 (by rfl) ⟨2194178, by rfl⟩ : syracuseStep 2925571 = 4388357) B4388357
theorem B9372685 : Blo 1733067 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B240305237 : Blo 1733067 240305237 := bstep (se 8 (by rfl) ⟨1408038, by rfl⟩ : syracuseStep 240305237 = 2816077) B2816077
theorem B3703907 : Blo 1733067 3703907 := bstep (se 1 (by rfl) ⟨2777930, by rfl⟩ : syracuseStep 3703907 = 5555861) B5555861
theorem B1950835 : Blo 1733067 1950835 := bstep (se 1 (by rfl) ⟨1463126, by rfl⟩ : syracuseStep 1950835 = 2926253) B2926253
theorem B2925713 : Blo 1733067 2925713 := bstep (se 2 (by rfl) ⟨1097142, by rfl⟩ : syracuseStep 2925713 = 2194285) B2194285
theorem B5629169 : Blo 1733067 5629169 := bstep (se 2 (by rfl) ⟨2110938, by rfl⟩ : syracuseStep 5629169 = 4221877) B4221877
theorem B13174001 : Blo 1733067 13174001 := bstep (se 2 (by rfl) ⟨4940250, by rfl⟩ : syracuseStep 13174001 = 9880501) B9880501
theorem B1950979 : Blo 1733067 1950979 := bstep (se 1 (by rfl) ⟨1463234, by rfl⟩ : syracuseStep 1950979 = 2926469) B2926469
theorem B3900689 : Blo 1733067 3900689 := bstep (se 2 (by rfl) ⟨1462758, by rfl⟩ : syracuseStep 3900689 = 2925517) B2925517
theorem B2925841 : Blo 1733067 2925841 := bstep (se 2 (by rfl) ⟨1097190, by rfl⟩ : syracuseStep 2925841 = 2194381) B2194381
theorem B2344225 : Blo 1733067 2344225 := bstep (se 2 (by rfl) ⟨879084, by rfl⟩ : syracuseStep 2344225 = 1758169) B1758169
theorem B3900707 : Blo 1733067 3900707 := bstep (se 1 (by rfl) ⟨2925530, by rfl⟩ : syracuseStep 3900707 = 5851061) B5851061
theorem B5850413 : Blo 1733067 5850413 := bstep (se 3 (by rfl) ⟨1096952, by rfl⟩ : syracuseStep 5850413 = 2193905) B2193905
theorem B8783153 : Blo 1733067 8783153 := bstep (se 2 (by rfl) ⟨3293682, by rfl⟩ : syracuseStep 8783153 = 6587365) B6587365
theorem B2925875 : Blo 1733067 2925875 := bstep (se 1 (by rfl) ⟨2194406, by rfl⟩ : syracuseStep 2925875 = 4388813) B4388813
theorem B5850467 : Blo 1733067 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B2778481 : Blo 1733067 2778481 := bstep (se 2 (by rfl) ⟨1041930, by rfl⟩ : syracuseStep 2778481 = 2083861) B2083861
theorem B8775053 : Blo 1733067 8775053 := bstep (se 3 (by rfl) ⟨1645322, by rfl⟩ : syracuseStep 8775053 = 3290645) B3290645
theorem B1951123 : Blo 1733067 1951123 := bstep (se 1 (by rfl) ⟨1463342, by rfl⟩ : syracuseStep 1951123 = 2926685) B2926685
theorem B2926003 : Blo 1733067 2926003 := bstep (se 1 (by rfl) ⟨2194502, by rfl⟩ : syracuseStep 2926003 = 4389005) B4389005
theorem B1951267 : Blo 1733067 1951267 := bstep (se 1 (by rfl) ⟨1463450, by rfl⟩ : syracuseStep 1951267 = 2926901) B2926901
theorem B3900977 : Blo 1733067 3900977 := bstep (se 2 (by rfl) ⟨1462866, by rfl⟩ : syracuseStep 3900977 = 2925733) B2925733
theorem B2926145 : Blo 1733067 2926145 := bstep (se 2 (by rfl) ⟨1097304, by rfl⟩ : syracuseStep 2926145 = 2194609) B2194609
theorem B3900995 : Blo 1733067 3900995 := bstep (se 1 (by rfl) ⟨2925746, by rfl⟩ : syracuseStep 3900995 = 5851493) B5851493
theorem B5850737 : Blo 1733067 5850737 := bstep (se 2 (by rfl) ⟨2194026, by rfl⟩ : syracuseStep 5850737 = 4388053) B4388053
theorem B9873029 : Blo 1733067 9873029 := bstep (se 4 (by rfl) ⟨925596, by rfl⟩ : syracuseStep 9873029 = 1851193) B1851193
theorem B1951411 : Blo 1733067 1951411 := bstep (se 1 (by rfl) ⟨1463558, by rfl⟩ : syracuseStep 1951411 = 2927117) B2927117
theorem B2926273 : Blo 1733067 2926273 := bstep (se 2 (by rfl) ⟨1097352, by rfl⟩ : syracuseStep 2926273 = 2194705) B2194705
theorem B2926307 : Blo 1733067 2926307 := bstep (se 1 (by rfl) ⟨2194730, by rfl⟩ : syracuseStep 2926307 = 4389461) B4389461
theorem B2967281 : Blo 1733067 2967281 := bstep (se 2 (by rfl) ⟨1112730, by rfl⟩ : syracuseStep 2967281 = 2225461) B2225461
theorem B4753187 : Blo 1733067 4753187 := bstep (se 1 (by rfl) ⟨3564890, by rfl⟩ : syracuseStep 4753187 = 7129781) B7129781
theorem B1951555 : Blo 1733067 1951555 := bstep (se 1 (by rfl) ⟨1463666, by rfl⟩ : syracuseStep 1951555 = 2927333) B2927333
theorem B3901265 : Blo 1733067 3901265 := bstep (se 2 (by rfl) ⟨1462974, by rfl⟩ : syracuseStep 3901265 = 2925949) B2925949
theorem B3901283 : Blo 1733067 3901283 := bstep (se 1 (by rfl) ⟨2925962, by rfl⟩ : syracuseStep 3901283 = 5851925) B5851925
theorem B2926435 : Blo 1733067 2926435 := bstep (se 1 (by rfl) ⟨2194826, by rfl⟩ : syracuseStep 2926435 = 4389653) B4389653
theorem B11863921 : Blo 1733067 11863921 := bstep (se 2 (by rfl) ⟨4448970, by rfl⟩ : syracuseStep 11863921 = 8897941) B8897941
theorem B3704771 : Blo 1733067 3704771 := bstep (se 1 (by rfl) ⟨2778578, by rfl⟩ : syracuseStep 3704771 = 5557157) B5557157
theorem B1951699 : Blo 1733067 1951699 := bstep (se 1 (by rfl) ⟨1463774, by rfl⟩ : syracuseStep 1951699 = 2927549) B2927549
theorem B5933027 : Blo 1733067 5933027 := bstep (se 1 (by rfl) ⟨4449770, by rfl⟩ : syracuseStep 5933027 = 8899541) B8899541
theorem B2926577 : Blo 1733067 2926577 := bstep (se 2 (by rfl) ⟨1097466, by rfl⟩ : syracuseStep 2926577 = 2194933) B2194933
theorem B3704881 : Blo 1733067 3704881 := bstep (se 2 (by rfl) ⟨1389330, by rfl⟩ : syracuseStep 3704881 = 2778661) B2778661
theorem B9873485 : Blo 1733067 9873485 := bstep (se 3 (by rfl) ⟨1851278, by rfl⟩ : syracuseStep 9873485 = 3702557) B3702557
theorem B1951843 : Blo 1733067 1951843 := bstep (se 1 (by rfl) ⟨1463882, by rfl⟩ : syracuseStep 1951843 = 2927765) B2927765
theorem B3901553 : Blo 1733067 3901553 := bstep (se 2 (by rfl) ⟨1463082, by rfl⟩ : syracuseStep 3901553 = 2926165) B2926165
theorem B2926705 : Blo 1733067 2926705 := bstep (se 2 (by rfl) ⟨1097514, by rfl⟩ : syracuseStep 2926705 = 2195029) B2195029
theorem B3901571 : Blo 1733067 3901571 := bstep (se 1 (by rfl) ⟨2926178, by rfl⟩ : syracuseStep 3901571 = 5852357) B5852357
theorem B5851277 : Blo 1733067 5851277 := bstep (se 3 (by rfl) ⟨1097114, by rfl⟩ : syracuseStep 5851277 = 2194229) B2194229
theorem B2926739 : Blo 1733067 2926739 := bstep (se 1 (by rfl) ⟨2195054, by rfl⟩ : syracuseStep 2926739 = 4390109) B4390109
theorem B2853025 : Blo 1733067 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B5851331 : Blo 1733067 5851331 := bstep (se 1 (by rfl) ⟨4388498, by rfl⟩ : syracuseStep 5851331 = 8776997) B8776997
theorem B6670577 : Blo 1733067 6670577 := bstep (se 2 (by rfl) ⟨2501466, by rfl⟩ : syracuseStep 6670577 = 5002933) B5002933
theorem B2926867 : Blo 1733067 2926867 := bstep (se 1 (by rfl) ⟨2195150, by rfl⟩ : syracuseStep 2926867 = 4390301) B4390301
theorem B2468161 : Blo 1733067 2468161 := bstep (se 2 (by rfl) ⟨925560, by rfl⟩ : syracuseStep 2468161 = 1851121) B1851121
theorem B9021773 : Blo 1733067 9021773 := bstep (se 3 (by rfl) ⟨1691582, by rfl⟩ : syracuseStep 9021773 = 3383165) B3383165
theorem B3901841 : Blo 1733067 3901841 := bstep (se 2 (by rfl) ⟨1463190, by rfl⟩ : syracuseStep 3901841 = 2926381) B2926381
theorem B2927009 : Blo 1733067 2927009 := bstep (se 2 (by rfl) ⟨1097628, by rfl⟩ : syracuseStep 2927009 = 2195257) B2195257
theorem B3901859 : Blo 1733067 3901859 := bstep (se 1 (by rfl) ⟨2926394, by rfl⟩ : syracuseStep 3901859 = 5852789) B5852789
theorem B3336643 : Blo 1733067 3336643 := bstep (se 1 (by rfl) ⟨2502482, by rfl⟩ : syracuseStep 3336643 = 5004965) B5004965
theorem B5851601 : Blo 1733067 5851601 := bstep (se 2 (by rfl) ⟨2194350, by rfl⟩ : syracuseStep 5851601 = 4388701) B4388701
theorem B5556707 : Blo 1733067 5556707 := bstep (se 1 (by rfl) ⟨4167530, by rfl⟩ : syracuseStep 5556707 = 8335061) B8335061
theorem B2927137 : Blo 1733067 2927137 := bstep (se 2 (by rfl) ⟨1097676, by rfl⟩ : syracuseStep 2927137 = 2195353) B2195353
theorem B44444213 : Blo 1733067 44444213 := bstep (se 5 (by rfl) ⟨2083322, by rfl⟩ : syracuseStep 44444213 = 4166645) B4166645
theorem B2927171 : Blo 1733067 2927171 := bstep (se 1 (by rfl) ⟨2195378, by rfl⟩ : syracuseStep 2927171 = 4390757) B4390757
theorem B6580835 : Blo 1733067 6580835 := bstep (se 1 (by rfl) ⟨4935626, by rfl⟩ : syracuseStep 6580835 = 9871253) B9871253
theorem B6670961 : Blo 1733067 6670961 := bstep (se 2 (by rfl) ⟨2501610, by rfl⟩ : syracuseStep 6670961 = 5003221) B5003221
theorem B2468497 : Blo 1733067 2468497 := bstep (se 2 (by rfl) ⟨925686, by rfl⟩ : syracuseStep 2468497 = 1851373) B1851373
theorem B2599601 : Blo 1733067 2599601 := bstep (se 2 (by rfl) ⟨974850, by rfl⟩ : syracuseStep 2599601 = 1949701) B1949701
theorem B3902129 : Blo 1733067 3902129 := bstep (se 2 (by rfl) ⟨1463298, by rfl⟩ : syracuseStep 3902129 = 2926597) B2926597
theorem B2599619 : Blo 1733067 2599619 := bstep (se 1 (by rfl) ⟨1949714, by rfl⟩ : syracuseStep 2599619 = 3899429) B3899429
theorem B3902147 : Blo 1733067 3902147 := bstep (se 1 (by rfl) ⟨2926610, by rfl⟩ : syracuseStep 3902147 = 5853221) B5853221
theorem B2927299 : Blo 1733067 2927299 := bstep (se 1 (by rfl) ⟨2195474, by rfl⟩ : syracuseStep 2927299 = 4390949) B4390949
theorem B2599649 : Blo 1733067 2599649 := bstep (se 2 (by rfl) ⟨974868, by rfl⟩ : syracuseStep 2599649 = 1949737) B1949737
theorem B5073635 : Blo 1733067 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B2599667 : Blo 1733067 2599667 := bstep (se 1 (by rfl) ⟨1949750, by rfl⟩ : syracuseStep 2599667 = 3899501) B3899501
theorem B2599697 : Blo 1733067 2599697 := bstep (se 2 (by rfl) ⟨974886, by rfl⟩ : syracuseStep 2599697 = 1949773) B1949773
theorem B2599715 : Blo 1733067 2599715 := bstep (se 1 (by rfl) ⟨1949786, by rfl⟩ : syracuseStep 2599715 = 3899573) B3899573
theorem B2599745 : Blo 1733067 2599745 := bstep (se 2 (by rfl) ⟨974904, by rfl⟩ : syracuseStep 2599745 = 1949809) B1949809
theorem B2927441 : Blo 1733067 2927441 := bstep (se 2 (by rfl) ⟨1097790, by rfl⟩ : syracuseStep 2927441 = 2195581) B2195581
theorem B2599763 : Blo 1733067 2599763 := bstep (se 1 (by rfl) ⟨1949822, by rfl⟩ : syracuseStep 2599763 = 3899645) B3899645
theorem B2599793 : Blo 1733067 2599793 := bstep (se 2 (by rfl) ⟨974922, by rfl⟩ : syracuseStep 2599793 = 1949845) B1949845
theorem B2599811 : Blo 1733067 2599811 := bstep (se 1 (by rfl) ⟨1949858, by rfl⟩ : syracuseStep 2599811 = 3899717) B3899717
theorem B2599841 : Blo 1733067 2599841 := bstep (se 2 (by rfl) ⟨974940, by rfl⟩ : syracuseStep 2599841 = 1949881) B1949881
theorem B2599859 : Blo 1733067 2599859 := bstep (se 1 (by rfl) ⟨1949894, by rfl⟩ : syracuseStep 2599859 = 3899789) B3899789
theorem B2599889 : Blo 1733067 2599889 := bstep (se 2 (by rfl) ⟨974958, by rfl⟩ : syracuseStep 2599889 = 1949917) B1949917
theorem B3902417 : Blo 1733067 3902417 := bstep (se 2 (by rfl) ⟨1463406, by rfl⟩ : syracuseStep 3902417 = 2926813) B2926813
theorem B2927569 : Blo 1733067 2927569 := bstep (se 2 (by rfl) ⟨1097838, by rfl⟩ : syracuseStep 2927569 = 2195677) B2195677
theorem B2599907 : Blo 1733067 2599907 := bstep (se 1 (by rfl) ⟨1949930, by rfl⟩ : syracuseStep 2599907 = 3899861) B3899861
theorem B3902435 : Blo 1733067 3902435 := bstep (se 1 (by rfl) ⟨2926826, by rfl⟩ : syracuseStep 3902435 = 5853653) B5853653
theorem B5852141 : Blo 1733067 5852141 := bstep (se 3 (by rfl) ⟨1097276, by rfl⟩ : syracuseStep 5852141 = 2194553) B2194553
theorem B2927603 : Blo 1733067 2927603 := bstep (se 1 (by rfl) ⟨2195702, by rfl⟩ : syracuseStep 2927603 = 4391405) B4391405
theorem B2599937 : Blo 1733067 2599937 := bstep (se 2 (by rfl) ⟨974976, by rfl⟩ : syracuseStep 2599937 = 1949953) B1949953
theorem B20024333 : Blo 1733067 20024333 := bstep (se 3 (by rfl) ⟨3754562, by rfl⟩ : syracuseStep 20024333 = 7509125) B7509125
theorem B2599955 : Blo 1733067 2599955 := bstep (se 1 (by rfl) ⟨1949966, by rfl⟩ : syracuseStep 2599955 = 3899933) B3899933
theorem B5852195 : Blo 1733067 5852195 := bstep (se 1 (by rfl) ⟨4389146, by rfl⟩ : syracuseStep 5852195 = 8778293) B8778293
theorem B2599985 : Blo 1733067 2599985 := bstep (se 2 (by rfl) ⟨974994, by rfl⟩ : syracuseStep 2599985 = 1949989) B1949989
theorem B2600003 : Blo 1733067 2600003 := bstep (se 1 (by rfl) ⟨1950002, by rfl⟩ : syracuseStep 2600003 = 3900005) B3900005
theorem B2600033 : Blo 1733067 2600033 := bstep (se 2 (by rfl) ⟨975012, by rfl⟩ : syracuseStep 2600033 = 1950025) B1950025
theorem B2600051 : Blo 1733067 2600051 := bstep (se 1 (by rfl) ⟨1950038, by rfl⟩ : syracuseStep 2600051 = 3900077) B3900077
theorem B2927731 : Blo 1733067 2927731 := bstep (se 1 (by rfl) ⟨2195798, by rfl⟩ : syracuseStep 2927731 = 4391597) B4391597
theorem B2600081 : Blo 1733067 2600081 := bstep (se 2 (by rfl) ⟨975030, by rfl⟩ : syracuseStep 2600081 = 1950061) B1950061
theorem B2600099 : Blo 1733067 2600099 := bstep (se 1 (by rfl) ⟨1950074, by rfl⟩ : syracuseStep 2600099 = 3900149) B3900149
theorem B2600129 : Blo 1733067 2600129 := bstep (se 2 (by rfl) ⟨975048, by rfl⟩ : syracuseStep 2600129 = 1950097) B1950097
theorem B2600147 : Blo 1733067 2600147 := bstep (se 1 (by rfl) ⟨1950110, by rfl⟩ : syracuseStep 2600147 = 3900221) B3900221
theorem B2469089 : Blo 1733067 2469089 := bstep (se 2 (by rfl) ⟨925908, by rfl⟩ : syracuseStep 2469089 = 1851817) B1851817
theorem B2600177 : Blo 1733067 2600177 := bstep (se 2 (by rfl) ⟨975066, by rfl⟩ : syracuseStep 2600177 = 1950133) B1950133
theorem B11259121 : Blo 1733067 11259121 := bstep (se 2 (by rfl) ⟨4222170, by rfl⟩ : syracuseStep 11259121 = 8444341) B8444341
theorem B13348081 : Blo 1733067 13348081 := bstep (se 2 (by rfl) ⟨5005530, by rfl⟩ : syracuseStep 13348081 = 10011061) B10011061
theorem B3902705 : Blo 1733067 3902705 := bstep (se 2 (by rfl) ⟨1463514, by rfl⟩ : syracuseStep 3902705 = 2927029) B2927029
theorem B2927873 : Blo 1733067 2927873 := bstep (se 2 (by rfl) ⟨1097952, by rfl⟩ : syracuseStep 2927873 = 2195905) B2195905
theorem B2600195 : Blo 1733067 2600195 := bstep (se 1 (by rfl) ⟨1950146, by rfl⟩ : syracuseStep 2600195 = 3900293) B3900293
theorem B3902723 : Blo 1733067 3902723 := bstep (se 1 (by rfl) ⟨2927042, by rfl⟩ : syracuseStep 3902723 = 5854085) B5854085
theorem B2600225 : Blo 1733067 2600225 := bstep (se 2 (by rfl) ⟨975084, by rfl⟩ : syracuseStep 2600225 = 1950169) B1950169
theorem B5852465 : Blo 1733067 5852465 := bstep (se 2 (by rfl) ⟨2194674, by rfl⟩ : syracuseStep 5852465 = 4389349) B4389349
theorem B2600243 : Blo 1733067 2600243 := bstep (se 1 (by rfl) ⟨1950182, by rfl⟩ : syracuseStep 2600243 = 3900365) B3900365
theorem B2600273 : Blo 1733067 2600273 := bstep (se 2 (by rfl) ⟨975102, by rfl⟩ : syracuseStep 2600273 = 1950205) B1950205
theorem B2600291 : Blo 1733067 2600291 := bstep (se 1 (by rfl) ⟨1950218, by rfl⟩ : syracuseStep 2600291 = 3900437) B3900437
theorem B7409009 : Blo 1733067 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B2600321 : Blo 1733067 2600321 := bstep (se 2 (by rfl) ⟨975120, by rfl⟩ : syracuseStep 2600321 = 1950241) B1950241
theorem B2600339 : Blo 1733067 2600339 := bstep (se 1 (by rfl) ⟨1950254, by rfl⟩ : syracuseStep 2600339 = 3900509) B3900509
theorem B2600369 : Blo 1733067 2600369 := bstep (se 2 (by rfl) ⟨975138, by rfl⟩ : syracuseStep 2600369 = 1950277) B1950277
theorem B2600387 : Blo 1733067 2600387 := bstep (se 1 (by rfl) ⟨1950290, by rfl⟩ : syracuseStep 2600387 = 3900581) B3900581
theorem B2600417 : Blo 1733067 2600417 := bstep (se 2 (by rfl) ⟨975156, by rfl⟩ : syracuseStep 2600417 = 1950313) B1950313
theorem B2600435 : Blo 1733067 2600435 := bstep (se 1 (by rfl) ⟨1950326, by rfl⟩ : syracuseStep 2600435 = 3900653) B3900653
theorem B2600465 : Blo 1733067 2600465 := bstep (se 2 (by rfl) ⟨975174, by rfl⟩ : syracuseStep 2600465 = 1950349) B1950349
theorem B3902993 : Blo 1733067 3902993 := bstep (se 2 (by rfl) ⟨1463622, by rfl⟩ : syracuseStep 3902993 = 2927245) B2927245
theorem B2600483 : Blo 1733067 2600483 := bstep (se 1 (by rfl) ⟨1950362, by rfl⟩ : syracuseStep 2600483 = 3900725) B3900725
theorem B3903011 : Blo 1733067 3903011 := bstep (se 1 (by rfl) ⟨2927258, by rfl⟩ : syracuseStep 3903011 = 5854517) B5854517
theorem B2600513 : Blo 1733067 2600513 := bstep (se 2 (by rfl) ⟨975192, by rfl⟩ : syracuseStep 2600513 = 1950385) B1950385
theorem B6581837 : Blo 1733067 6581837 := bstep (se 3 (by rfl) ⟨1234094, by rfl⟩ : syracuseStep 6581837 = 2468189) B2468189
theorem B2600531 : Blo 1733067 2600531 := bstep (se 1 (by rfl) ⟨1950398, by rfl⟩ : syracuseStep 2600531 = 3900797) B3900797
theorem B2600561 : Blo 1733067 2600561 := bstep (se 2 (by rfl) ⟨975210, by rfl⟩ : syracuseStep 2600561 = 1950421) B1950421
theorem B2600579 : Blo 1733067 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B2600609 : Blo 1733067 2600609 := bstep (se 2 (by rfl) ⟨975228, by rfl⟩ : syracuseStep 2600609 = 1950457) B1950457
theorem B2600627 : Blo 1733067 2600627 := bstep (se 1 (by rfl) ⟨1950470, by rfl⟩ : syracuseStep 2600627 = 3900941) B3900941
theorem B2600657 : Blo 1733067 2600657 := bstep (se 2 (by rfl) ⟨975246, by rfl⟩ : syracuseStep 2600657 = 1950493) B1950493
theorem B2600675 : Blo 1733067 2600675 := bstep (se 1 (by rfl) ⟨1950506, by rfl⟩ : syracuseStep 2600675 = 3901013) B3901013
theorem B5557987 : Blo 1733067 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B2469619 : Blo 1733067 2469619 := bstep (se 1 (by rfl) ⟨1852214, by rfl⟩ : syracuseStep 2469619 = 3704429) B3704429
theorem B2600705 : Blo 1733067 2600705 := bstep (se 2 (by rfl) ⟨975264, by rfl⟩ : syracuseStep 2600705 = 1950529) B1950529
theorem B3165955 : Blo 1733067 3165955 := bstep (se 1 (by rfl) ⟨2374466, by rfl⟩ : syracuseStep 3165955 = 4748933) B4748933
theorem B2600723 : Blo 1733067 2600723 := bstep (se 1 (by rfl) ⟨1950542, by rfl⟩ : syracuseStep 2600723 = 3901085) B3901085
theorem B6246193 : Blo 1733067 6246193 := bstep (se 2 (by rfl) ⟨2342322, by rfl⟩ : syracuseStep 6246193 = 4684645) B4684645
theorem B2600753 : Blo 1733067 2600753 := bstep (se 2 (by rfl) ⟨975282, by rfl⟩ : syracuseStep 2600753 = 1950565) B1950565
theorem B3903281 : Blo 1733067 3903281 := bstep (se 2 (by rfl) ⟨1463730, by rfl⟩ : syracuseStep 3903281 = 2927461) B2927461
theorem B2600771 : Blo 1733067 2600771 := bstep (se 1 (by rfl) ⟨1950578, by rfl⟩ : syracuseStep 2600771 = 3901157) B3901157
theorem B3903299 : Blo 1733067 3903299 := bstep (se 1 (by rfl) ⟨2927474, by rfl⟩ : syracuseStep 3903299 = 5854949) B5854949
theorem B5853005 : Blo 1733067 5853005 := bstep (se 3 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 5853005 = 2194877) B2194877
theorem B2600801 : Blo 1733067 2600801 := bstep (se 2 (by rfl) ⟨975300, by rfl⟩ : syracuseStep 2600801 = 1950601) B1950601
theorem B16674659 : Blo 1733067 16674659 := bstep (se 1 (by rfl) ⟨12505994, by rfl⟩ : syracuseStep 16674659 = 25011989) B25011989
theorem B2600819 : Blo 1733067 2600819 := bstep (se 1 (by rfl) ⟨1950614, by rfl⟩ : syracuseStep 2600819 = 3901229) B3901229
theorem B5853059 : Blo 1733067 5853059 := bstep (se 1 (by rfl) ⟨4389794, by rfl⟩ : syracuseStep 5853059 = 8779589) B8779589
theorem B2600849 : Blo 1733067 2600849 := bstep (se 2 (by rfl) ⟨975318, by rfl⟩ : syracuseStep 2600849 = 1950637) B1950637
theorem B2600867 : Blo 1733067 2600867 := bstep (se 1 (by rfl) ⟨1950650, by rfl⟩ : syracuseStep 2600867 = 3901301) B3901301
theorem B2600897 : Blo 1733067 2600897 := bstep (se 2 (by rfl) ⟨975336, by rfl⟩ : syracuseStep 2600897 = 1950673) B1950673
theorem B11112389 : Blo 1733067 11112389 := bstep (se 4 (by rfl) ⟨1041786, by rfl⟩ : syracuseStep 11112389 = 2083573) B2083573
theorem B2600915 : Blo 1733067 2600915 := bstep (se 1 (by rfl) ⟨1950686, by rfl⟩ : syracuseStep 2600915 = 3901373) B3901373
theorem B8335331 : Blo 1733067 8335331 := bstep (se 1 (by rfl) ⟨6251498, by rfl⟩ : syracuseStep 8335331 = 12502997) B12502997
theorem B2600945 : Blo 1733067 2600945 := bstep (se 2 (by rfl) ⟨975354, by rfl⟩ : syracuseStep 2600945 = 1950709) B1950709
theorem B2600963 : Blo 1733067 2600963 := bstep (se 1 (by rfl) ⟨1950722, by rfl⟩ : syracuseStep 2600963 = 3901445) B3901445
theorem B7409677 : Blo 1733067 7409677 := bstep (se 3 (by rfl) ⟨1389314, by rfl⟩ : syracuseStep 7409677 = 2778629) B2778629
theorem B2600993 : Blo 1733067 2600993 := bstep (se 2 (by rfl) ⟨975372, by rfl⟩ : syracuseStep 2600993 = 1950745) B1950745
theorem B5558321 : Blo 1733067 5558321 := bstep (se 2 (by rfl) ⟨2084370, by rfl⟩ : syracuseStep 5558321 = 4168741) B4168741
theorem B2601011 : Blo 1733067 2601011 := bstep (se 1 (by rfl) ⟨1950758, by rfl⟩ : syracuseStep 2601011 = 3901517) B3901517
theorem B2469955 : Blo 1733067 2469955 := bstep (se 1 (by rfl) ⟨1852466, by rfl⟩ : syracuseStep 2469955 = 3704933) B3704933
theorem B2601041 : Blo 1733067 2601041 := bstep (se 2 (by rfl) ⟨975390, by rfl⟩ : syracuseStep 2601041 = 1950781) B1950781
theorem B3903569 : Blo 1733067 3903569 := bstep (se 2 (by rfl) ⟨1463838, by rfl⟩ : syracuseStep 3903569 = 2927677) B2927677
theorem B2601059 : Blo 1733067 2601059 := bstep (se 1 (by rfl) ⟨1950794, by rfl⟩ : syracuseStep 2601059 = 3901589) B3901589
theorem B3903587 : Blo 1733067 3903587 := bstep (se 1 (by rfl) ⟨2927690, by rfl⟩ : syracuseStep 3903587 = 5855381) B5855381
theorem B2601089 : Blo 1733067 2601089 := bstep (se 2 (by rfl) ⟨975408, by rfl⟩ : syracuseStep 2601089 = 1950817) B1950817
theorem B5853329 : Blo 1733067 5853329 := bstep (se 2 (by rfl) ⟨2194998, by rfl⟩ : syracuseStep 5853329 = 4389997) B4389997
theorem B2601107 : Blo 1733067 2601107 := bstep (se 1 (by rfl) ⟨1950830, by rfl⟩ : syracuseStep 2601107 = 3901661) B3901661
theorem B2601137 : Blo 1733067 2601137 := bstep (se 2 (by rfl) ⟨975426, by rfl⟩ : syracuseStep 2601137 = 1950853) B1950853
theorem B2601155 : Blo 1733067 2601155 := bstep (se 1 (by rfl) ⟨1950866, by rfl⟩ : syracuseStep 2601155 = 3901733) B3901733
theorem B5935313 : Blo 1733067 5935313 := bstep (se 2 (by rfl) ⟨2225742, by rfl⟩ : syracuseStep 5935313 = 4451485) B4451485
theorem B2601185 : Blo 1733067 2601185 := bstep (se 2 (by rfl) ⟨975444, by rfl⟩ : syracuseStep 2601185 = 1950889) B1950889
theorem B8777969 : Blo 1733067 8777969 := bstep (se 2 (by rfl) ⟨3291738, by rfl⟩ : syracuseStep 8777969 = 6583477) B6583477
theorem B2601203 : Blo 1733067 2601203 := bstep (se 1 (by rfl) ⟨1950902, by rfl⟩ : syracuseStep 2601203 = 3901805) B3901805
theorem B12505357 : Blo 1733067 12505357 := bstep (se 3 (by rfl) ⟨2344754, by rfl⟩ : syracuseStep 12505357 = 4689509) B4689509
theorem B2601233 : Blo 1733067 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B2601251 : Blo 1733067 2601251 := bstep (se 1 (by rfl) ⟨1950938, by rfl⟩ : syracuseStep 2601251 = 3901877) B3901877
theorem B4165955 : Blo 1733067 4165955 := bstep (se 1 (by rfl) ⟨3124466, by rfl⟩ : syracuseStep 4165955 = 6248933) B6248933
theorem B2601281 : Blo 1733067 2601281 := bstep (se 2 (by rfl) ⟨975480, by rfl⟩ : syracuseStep 2601281 = 1950961) B1950961
theorem B2601299 : Blo 1733067 2601299 := bstep (se 1 (by rfl) ⟨1950974, by rfl⟩ : syracuseStep 2601299 = 3901949) B3901949
theorem B4936049 : Blo 1733067 4936049 := bstep (se 2 (by rfl) ⟨1851018, by rfl⟩ : syracuseStep 4936049 = 3702037) B3702037
theorem B2601329 : Blo 1733067 2601329 := bstep (se 2 (by rfl) ⟨975498, by rfl⟩ : syracuseStep 2601329 = 1950997) B1950997
theorem B3903857 : Blo 1733067 3903857 := bstep (se 2 (by rfl) ⟨1463946, by rfl⟩ : syracuseStep 3903857 = 2927893) B2927893
theorem B2601347 : Blo 1733067 2601347 := bstep (se 1 (by rfl) ⟨1951010, by rfl⟩ : syracuseStep 2601347 = 3902021) B3902021
theorem B3903875 : Blo 1733067 3903875 := bstep (se 1 (by rfl) ⟨2927906, by rfl⟩ : syracuseStep 3903875 = 5855813) B5855813
theorem B2601377 : Blo 1733067 2601377 := bstep (se 2 (by rfl) ⟨975516, by rfl⟩ : syracuseStep 2601377 = 1951033) B1951033
theorem B2601395 : Blo 1733067 2601395 := bstep (se 1 (by rfl) ⟨1951046, by rfl⟩ : syracuseStep 2601395 = 3902093) B3902093
theorem B2601425 : Blo 1733067 2601425 := bstep (se 2 (by rfl) ⟨975534, by rfl⟩ : syracuseStep 2601425 = 1951069) B1951069
theorem B1733075 : Blo 1733067 1733075 := bstep (se 1 (by rfl) ⟨1299806, by rfl⟩ : syracuseStep 1733075 = 2599613) B2599613
theorem B1733091 : Blo 1733067 1733091 := bstep (se 1 (by rfl) ⟨1299818, by rfl⟩ : syracuseStep 1733091 = 2599637) B2599637
theorem B2601443 : Blo 1733067 2601443 := bstep (se 1 (by rfl) ⟨1951082, by rfl⟩ : syracuseStep 2601443 = 3902165) B3902165
theorem B1733107 : Blo 1733067 1733107 := bstep (se 1 (by rfl) ⟨1299830, by rfl⟩ : syracuseStep 1733107 = 2599661) B2599661
theorem B2601473 : Blo 1733067 2601473 := bstep (se 2 (by rfl) ⟨975552, by rfl⟩ : syracuseStep 2601473 = 1951105) B1951105
theorem B1733123 : Blo 1733067 1733123 := bstep (se 1 (by rfl) ⟨1299842, by rfl⟩ : syracuseStep 1733123 = 2599685) B2599685
theorem B4166147 : Blo 1733067 4166147 := bstep (se 1 (by rfl) ⟨3124610, by rfl⟩ : syracuseStep 4166147 = 6249221) B6249221
theorem B7909901 : Blo 1733067 7909901 := bstep (se 3 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 7909901 = 2966213) B2966213
theorem B1733139 : Blo 1733067 1733139 := bstep (se 1 (by rfl) ⟨1299854, by rfl⟩ : syracuseStep 1733139 = 2599709) B2599709
theorem B2601491 : Blo 1733067 2601491 := bstep (se 1 (by rfl) ⟨1951118, by rfl⟩ : syracuseStep 2601491 = 3902237) B3902237
theorem B1733155 : Blo 1733067 1733155 := bstep (se 1 (by rfl) ⟨1299866, by rfl⟩ : syracuseStep 1733155 = 2599733) B2599733
theorem B4936241 : Blo 1733067 4936241 := bstep (se 2 (by rfl) ⟨1851090, by rfl⟩ : syracuseStep 4936241 = 3702181) B3702181
theorem B2601521 : Blo 1733067 2601521 := bstep (se 2 (by rfl) ⟨975570, by rfl⟩ : syracuseStep 2601521 = 1951141) B1951141
theorem B1733171 : Blo 1733067 1733171 := bstep (se 1 (by rfl) ⟨1299878, by rfl⟩ : syracuseStep 1733171 = 2599757) B2599757
theorem B1733187 : Blo 1733067 1733187 := bstep (se 1 (by rfl) ⟨1299890, by rfl⟩ : syracuseStep 1733187 = 2599781) B2599781
theorem B2601539 : Blo 1733067 2601539 := bstep (se 1 (by rfl) ⟨1951154, by rfl⟩ : syracuseStep 2601539 = 3902309) B3902309
theorem B1733203 : Blo 1733067 1733203 := bstep (se 1 (by rfl) ⟨1299902, by rfl⟩ : syracuseStep 1733203 = 2599805) B2599805
theorem B2601569 : Blo 1733067 2601569 := bstep (se 2 (by rfl) ⟨975588, by rfl⟩ : syracuseStep 2601569 = 1951177) B1951177
theorem B1733219 : Blo 1733067 1733219 := bstep (se 1 (by rfl) ⟨1299914, by rfl⟩ : syracuseStep 1733219 = 2599829) B2599829
theorem B7410275 : Blo 1733067 7410275 := bstep (se 1 (by rfl) ⟨5557706, by rfl⟩ : syracuseStep 7410275 = 11115413) B11115413
theorem B1733235 : Blo 1733067 1733235 := bstep (se 1 (by rfl) ⟨1299926, by rfl⟩ : syracuseStep 1733235 = 2599853) B2599853
theorem B2601587 : Blo 1733067 2601587 := bstep (se 1 (by rfl) ⟨1951190, by rfl⟩ : syracuseStep 2601587 = 3902381) B3902381
theorem B1733251 : Blo 1733067 1733251 := bstep (se 1 (by rfl) ⟨1299938, by rfl⟩ : syracuseStep 1733251 = 2599877) B2599877
theorem B11866765 : Blo 1733067 11866765 := bstep (se 3 (by rfl) ⟨2225018, by rfl⟩ : syracuseStep 11866765 = 4450037) B4450037
theorem B2601617 : Blo 1733067 2601617 := bstep (se 2 (by rfl) ⟨975606, by rfl⟩ : syracuseStep 2601617 = 1951213) B1951213
theorem B1733267 : Blo 1733067 1733267 := bstep (se 1 (by rfl) ⟨1299950, by rfl⟩ : syracuseStep 1733267 = 2599901) B2599901
theorem B1733283 : Blo 1733067 1733283 := bstep (se 1 (by rfl) ⟨1299962, by rfl⟩ : syracuseStep 1733283 = 2599925) B2599925
theorem B2601635 : Blo 1733067 2601635 := bstep (se 1 (by rfl) ⟨1951226, by rfl⟩ : syracuseStep 2601635 = 3902453) B3902453
theorem B5853869 : Blo 1733067 5853869 := bstep (se 3 (by rfl) ⟨1097600, by rfl⟩ : syracuseStep 5853869 = 2195201) B2195201
theorem B1733299 : Blo 1733067 1733299 := bstep (se 1 (by rfl) ⟨1299974, by rfl⟩ : syracuseStep 1733299 = 2599949) B2599949
theorem B2601665 : Blo 1733067 2601665 := bstep (se 2 (by rfl) ⟨975624, by rfl⟩ : syracuseStep 2601665 = 1951249) B1951249
theorem B1733315 : Blo 1733067 1733315 := bstep (se 1 (by rfl) ⟨1299986, by rfl⟩ : syracuseStep 1733315 = 2599973) B2599973
theorem B33313477 : Blo 1733067 33313477 := bstep (se 4 (by rfl) ⟨3123138, by rfl⟩ : syracuseStep 33313477 = 6246277) B6246277
theorem B1733331 : Blo 1733067 1733331 := bstep (se 1 (by rfl) ⟨1299998, by rfl⟩ : syracuseStep 1733331 = 2599997) B2599997
theorem B2601683 : Blo 1733067 2601683 := bstep (se 1 (by rfl) ⟨1951262, by rfl⟩ : syracuseStep 2601683 = 3902525) B3902525
theorem B1733347 : Blo 1733067 1733347 := bstep (se 1 (by rfl) ⟨1300010, by rfl⟩ : syracuseStep 1733347 = 2600021) B2600021
theorem B5853923 : Blo 1733067 5853923 := bstep (se 1 (by rfl) ⟨4390442, by rfl⟩ : syracuseStep 5853923 = 8780885) B8780885
theorem B2601713 : Blo 1733067 2601713 := bstep (se 2 (by rfl) ⟨975642, by rfl⟩ : syracuseStep 2601713 = 1951285) B1951285
theorem B1733363 : Blo 1733067 1733363 := bstep (se 1 (by rfl) ⟨1300022, by rfl⟩ : syracuseStep 1733363 = 2600045) B2600045
theorem B1733379 : Blo 1733067 1733379 := bstep (se 1 (by rfl) ⟨1300034, by rfl⟩ : syracuseStep 1733379 = 2600069) B2600069
theorem B2601731 : Blo 1733067 2601731 := bstep (se 1 (by rfl) ⟨1951298, by rfl⟩ : syracuseStep 2601731 = 3902597) B3902597
theorem B1733395 : Blo 1733067 1733395 := bstep (se 1 (by rfl) ⟨1300046, by rfl⟩ : syracuseStep 1733395 = 2600093) B2600093
theorem B2601761 : Blo 1733067 2601761 := bstep (se 2 (by rfl) ⟨975660, by rfl⟩ : syracuseStep 2601761 = 1951321) B1951321
theorem B1733411 : Blo 1733067 1733411 := bstep (se 1 (by rfl) ⟨1300058, by rfl⟩ : syracuseStep 1733411 = 2600117) B2600117
theorem B1733427 : Blo 1733067 1733427 := bstep (se 1 (by rfl) ⟨1300070, by rfl⟩ : syracuseStep 1733427 = 2600141) B2600141
theorem B2601779 : Blo 1733067 2601779 := bstep (se 1 (by rfl) ⟨1951334, by rfl⟩ : syracuseStep 2601779 = 3902669) B3902669
theorem B1733443 : Blo 1733067 1733443 := bstep (se 1 (by rfl) ⟨1300082, by rfl⟩ : syracuseStep 1733443 = 2600165) B2600165
theorem B2601809 : Blo 1733067 2601809 := bstep (se 2 (by rfl) ⟨975678, by rfl⟩ : syracuseStep 2601809 = 1951357) B1951357
theorem B1733459 : Blo 1733067 1733459 := bstep (se 1 (by rfl) ⟨1300094, by rfl⟩ : syracuseStep 1733459 = 2600189) B2600189
theorem B1733475 : Blo 1733067 1733475 := bstep (se 1 (by rfl) ⟨1300106, by rfl⟩ : syracuseStep 1733475 = 2600213) B2600213
theorem B2601827 : Blo 1733067 2601827 := bstep (se 1 (by rfl) ⟨1951370, by rfl⟩ : syracuseStep 2601827 = 3902741) B3902741
theorem B1733491 : Blo 1733067 1733491 := bstep (se 1 (by rfl) ⟨1300118, by rfl⟩ : syracuseStep 1733491 = 2600237) B2600237
theorem B2601857 : Blo 1733067 2601857 := bstep (se 2 (by rfl) ⟨975696, by rfl⟩ : syracuseStep 2601857 = 1951393) B1951393
theorem B1733507 : Blo 1733067 1733507 := bstep (se 1 (by rfl) ⟨1300130, by rfl⟩ : syracuseStep 1733507 = 2600261) B2600261
theorem B4387729 : Blo 1733067 4387729 := bstep (se 2 (by rfl) ⟨1645398, by rfl⟩ : syracuseStep 4387729 = 3290797) B3290797
theorem B1733523 : Blo 1733067 1733523 := bstep (se 1 (by rfl) ⟨1300142, by rfl⟩ : syracuseStep 1733523 = 2600285) B2600285
theorem B2601875 : Blo 1733067 2601875 := bstep (se 1 (by rfl) ⟨1951406, by rfl⟩ : syracuseStep 2601875 = 3902813) B3902813
theorem B1733539 : Blo 1733067 1733539 := bstep (se 1 (by rfl) ⟨1300154, by rfl⟩ : syracuseStep 1733539 = 2600309) B2600309
theorem B9876401 : Blo 1733067 9876401 := bstep (se 2 (by rfl) ⟨3703650, by rfl⟩ : syracuseStep 9876401 = 7407301) B7407301
theorem B2601905 : Blo 1733067 2601905 := bstep (se 2 (by rfl) ⟨975714, by rfl⟩ : syracuseStep 2601905 = 1951429) B1951429
theorem B1733555 : Blo 1733067 1733555 := bstep (se 1 (by rfl) ⟨1300166, by rfl⟩ : syracuseStep 1733555 = 2600333) B2600333
theorem B1733571 : Blo 1733067 1733571 := bstep (se 1 (by rfl) ⟨1300178, by rfl⟩ : syracuseStep 1733571 = 2600357) B2600357
theorem B2601923 : Blo 1733067 2601923 := bstep (se 1 (by rfl) ⟨1951442, by rfl⟩ : syracuseStep 2601923 = 3902885) B3902885
theorem B1733587 : Blo 1733067 1733587 := bstep (se 1 (by rfl) ⟨1300190, by rfl⟩ : syracuseStep 1733587 = 2600381) B2600381
theorem B1733603 : Blo 1733067 1733603 := bstep (se 1 (by rfl) ⟨1300202, by rfl⟩ : syracuseStep 1733603 = 2600405) B2600405
theorem B2601953 : Blo 1733067 2601953 := bstep (se 2 (by rfl) ⟨975732, by rfl⟩ : syracuseStep 2601953 = 1951465) B1951465
theorem B5272561 : Blo 1733067 5272561 := bstep (se 2 (by rfl) ⟨1977210, by rfl⟩ : syracuseStep 5272561 = 3954421) B3954421
theorem B1733619 : Blo 1733067 1733619 := bstep (se 1 (by rfl) ⟨1300214, by rfl⟩ : syracuseStep 1733619 = 2600429) B2600429
theorem B5854193 : Blo 1733067 5854193 := bstep (se 2 (by rfl) ⟨2195322, by rfl⟩ : syracuseStep 5854193 = 4390645) B4390645
theorem B2601971 : Blo 1733067 2601971 := bstep (se 1 (by rfl) ⟨1951478, by rfl⟩ : syracuseStep 2601971 = 3902957) B3902957
theorem B1733635 : Blo 1733067 1733635 := bstep (se 1 (by rfl) ⟨1300226, by rfl⟩ : syracuseStep 1733635 = 2600453) B2600453
theorem B3290129 : Blo 1733067 3290129 := bstep (se 2 (by rfl) ⟨1233798, by rfl⟩ : syracuseStep 3290129 = 2467597) B2467597
theorem B2602001 : Blo 1733067 2602001 := bstep (se 2 (by rfl) ⟨975750, by rfl⟩ : syracuseStep 2602001 = 1951501) B1951501
theorem B1733651 : Blo 1733067 1733651 := bstep (se 1 (by rfl) ⟨1300238, by rfl⟩ : syracuseStep 1733651 = 2600477) B2600477
theorem B1733667 : Blo 1733067 1733667 := bstep (se 1 (by rfl) ⟨1300250, by rfl⟩ : syracuseStep 1733667 = 2600501) B2600501
theorem B2602019 : Blo 1733067 2602019 := bstep (se 1 (by rfl) ⟨1951514, by rfl⟩ : syracuseStep 2602019 = 3903029) B3903029
theorem B1733683 : Blo 1733067 1733683 := bstep (se 1 (by rfl) ⟨1300262, by rfl⟩ : syracuseStep 1733683 = 2600525) B2600525
theorem B2602049 : Blo 1733067 2602049 := bstep (se 2 (by rfl) ⟨975768, by rfl⟩ : syracuseStep 2602049 = 1951537) B1951537
theorem B1733699 : Blo 1733067 1733699 := bstep (se 1 (by rfl) ⟨1300274, by rfl⟩ : syracuseStep 1733699 = 2600549) B2600549
theorem B4166723 : Blo 1733067 4166723 := bstep (se 1 (by rfl) ⟨3125042, by rfl⟩ : syracuseStep 4166723 = 6250085) B6250085
theorem B1733715 : Blo 1733067 1733715 := bstep (se 1 (by rfl) ⟨1300286, by rfl⟩ : syracuseStep 1733715 = 2600573) B2600573
theorem B2602067 : Blo 1733067 2602067 := bstep (se 1 (by rfl) ⟨1951550, by rfl⟩ : syracuseStep 2602067 = 3903101) B3903101
theorem B1733731 : Blo 1733067 1733731 := bstep (se 1 (by rfl) ⟨1300298, by rfl⟩ : syracuseStep 1733731 = 2600597) B2600597
theorem B2602097 : Blo 1733067 2602097 := bstep (se 2 (by rfl) ⟨975786, by rfl⟩ : syracuseStep 2602097 = 1951573) B1951573
theorem B1733747 : Blo 1733067 1733747 := bstep (se 1 (by rfl) ⟨1300310, by rfl⟩ : syracuseStep 1733747 = 2600621) B2600621
theorem B1733763 : Blo 1733067 1733763 := bstep (se 1 (by rfl) ⟨1300322, by rfl⟩ : syracuseStep 1733763 = 2600645) B2600645
theorem B2602115 : Blo 1733067 2602115 := bstep (se 1 (by rfl) ⟨1951586, by rfl⟩ : syracuseStep 2602115 = 3903173) B3903173
theorem B1733779 : Blo 1733067 1733779 := bstep (se 1 (by rfl) ⟨1300334, by rfl⟩ : syracuseStep 1733779 = 2600669) B2600669
theorem B2602145 : Blo 1733067 2602145 := bstep (se 2 (by rfl) ⟨975804, by rfl⟩ : syracuseStep 2602145 = 1951609) B1951609
theorem B4388003 : Blo 1733067 4388003 := bstep (se 1 (by rfl) ⟨3291002, by rfl⟩ : syracuseStep 4388003 = 6582005) B6582005
theorem B1733795 : Blo 1733067 1733795 := bstep (se 1 (by rfl) ⟨1300346, by rfl⟩ : syracuseStep 1733795 = 2600693) B2600693
theorem B1733811 : Blo 1733067 1733811 := bstep (se 1 (by rfl) ⟨1300358, by rfl⟩ : syracuseStep 1733811 = 2600717) B2600717
theorem B2602163 : Blo 1733067 2602163 := bstep (se 1 (by rfl) ⟨1951622, by rfl⟩ : syracuseStep 2602163 = 3903245) B3903245
theorem B1733827 : Blo 1733067 1733827 := bstep (se 1 (by rfl) ⟨1300370, by rfl⟩ : syracuseStep 1733827 = 2600741) B2600741
theorem B2602193 : Blo 1733067 2602193 := bstep (se 2 (by rfl) ⟨975822, by rfl⟩ : syracuseStep 2602193 = 1951645) B1951645
theorem B1733843 : Blo 1733067 1733843 := bstep (se 1 (by rfl) ⟨1300382, by rfl⟩ : syracuseStep 1733843 = 2600765) B2600765
theorem B1733859 : Blo 1733067 1733859 := bstep (se 1 (by rfl) ⟨1300394, by rfl⟩ : syracuseStep 1733859 = 2600789) B2600789
theorem B2602211 : Blo 1733067 2602211 := bstep (se 1 (by rfl) ⟨1951658, by rfl⟩ : syracuseStep 2602211 = 3903317) B3903317
theorem B1733875 : Blo 1733067 1733875 := bstep (se 1 (by rfl) ⟨1300406, by rfl⟩ : syracuseStep 1733875 = 2600813) B2600813
theorem B2602241 : Blo 1733067 2602241 := bstep (se 2 (by rfl) ⟨975840, by rfl⟩ : syracuseStep 2602241 = 1951681) B1951681
theorem B1733891 : Blo 1733067 1733891 := bstep (se 1 (by rfl) ⟨1300418, by rfl⟩ : syracuseStep 1733891 = 2600837) B2600837
theorem B1733907 : Blo 1733067 1733907 := bstep (se 1 (by rfl) ⟨1300430, by rfl⟩ : syracuseStep 1733907 = 2600861) B2600861
theorem B2602259 : Blo 1733067 2602259 := bstep (se 1 (by rfl) ⟨1951694, by rfl⟩ : syracuseStep 2602259 = 3903389) B3903389
theorem B1733923 : Blo 1733067 1733923 := bstep (se 1 (by rfl) ⟨1300442, by rfl⟩ : syracuseStep 1733923 = 2600885) B2600885
theorem B2602289 : Blo 1733067 2602289 := bstep (se 2 (by rfl) ⟨975858, by rfl⟩ : syracuseStep 2602289 = 1951717) B1951717
theorem B1733939 : Blo 1733067 1733939 := bstep (se 1 (by rfl) ⟨1300454, by rfl⟩ : syracuseStep 1733939 = 2600909) B2600909
theorem B1733955 : Blo 1733067 1733955 := bstep (se 1 (by rfl) ⟨1300466, by rfl⟩ : syracuseStep 1733955 = 2600933) B2600933
theorem B2602307 : Blo 1733067 2602307 := bstep (se 1 (by rfl) ⟨1951730, by rfl⟩ : syracuseStep 2602307 = 3903461) B3903461
theorem B1733971 : Blo 1733067 1733971 := bstep (se 1 (by rfl) ⟨1300478, by rfl⟩ : syracuseStep 1733971 = 2600957) B2600957
theorem B2602337 : Blo 1733067 2602337 := bstep (se 2 (by rfl) ⟨975876, by rfl⟩ : syracuseStep 2602337 = 1951753) B1951753
theorem B8893795 : Blo 1733067 8893795 := bstep (se 1 (by rfl) ⟨6670346, by rfl⟩ : syracuseStep 8893795 = 13340693) B13340693
theorem B14808419 : Blo 1733067 14808419 := bstep (se 1 (by rfl) ⟨11106314, by rfl⟩ : syracuseStep 14808419 = 22212629) B22212629
theorem B4388195 : Blo 1733067 4388195 := bstep (se 1 (by rfl) ⟨3291146, by rfl⟩ : syracuseStep 4388195 = 6582293) B6582293
theorem B1733987 : Blo 1733067 1733987 := bstep (se 1 (by rfl) ⟨1300490, by rfl⟩ : syracuseStep 1733987 = 2600981) B2600981
theorem B8336753 : Blo 1733067 8336753 := bstep (se 2 (by rfl) ⟨3126282, by rfl⟩ : syracuseStep 8336753 = 6252565) B6252565
theorem B1734003 : Blo 1733067 1734003 := bstep (se 1 (by rfl) ⟨1300502, by rfl⟩ : syracuseStep 1734003 = 2601005) B2601005
theorem B2602355 : Blo 1733067 2602355 := bstep (se 1 (by rfl) ⟨1951766, by rfl⟩ : syracuseStep 2602355 = 3903533) B3903533
theorem B1734019 : Blo 1733067 1734019 := bstep (se 1 (by rfl) ⟨1300514, by rfl⟩ : syracuseStep 1734019 = 2601029) B2601029
theorem B2602385 : Blo 1733067 2602385 := bstep (se 2 (by rfl) ⟨975894, by rfl⟩ : syracuseStep 2602385 = 1951789) B1951789
theorem B1734035 : Blo 1733067 1734035 := bstep (se 1 (by rfl) ⟨1300526, by rfl⟩ : syracuseStep 1734035 = 2601053) B2601053
theorem B1734051 : Blo 1733067 1734051 := bstep (se 1 (by rfl) ⟨1300538, by rfl⟩ : syracuseStep 1734051 = 2601077) B2601077
theorem B2602403 : Blo 1733067 2602403 := bstep (se 1 (by rfl) ⟨1951802, by rfl⟩ : syracuseStep 2602403 = 3903605) B3903605
theorem B1734067 : Blo 1733067 1734067 := bstep (se 1 (by rfl) ⟨1300550, by rfl⟩ : syracuseStep 1734067 = 2601101) B2601101
theorem B2602433 : Blo 1733067 2602433 := bstep (se 2 (by rfl) ⟨975912, by rfl⟩ : syracuseStep 2602433 = 1951825) B1951825
theorem B1734083 : Blo 1733067 1734083 := bstep (se 1 (by rfl) ⟨1300562, by rfl⟩ : syracuseStep 1734083 = 2601125) B2601125
theorem B4167107 : Blo 1733067 4167107 := bstep (se 1 (by rfl) ⟨3125330, by rfl⟩ : syracuseStep 4167107 = 6250661) B6250661
theorem B1734099 : Blo 1733067 1734099 := bstep (se 1 (by rfl) ⟨1300574, by rfl⟩ : syracuseStep 1734099 = 2601149) B2601149
theorem B2602451 : Blo 1733067 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B1734115 : Blo 1733067 1734115 := bstep (se 1 (by rfl) ⟨1300586, by rfl⟩ : syracuseStep 1734115 = 2601173) B2601173
theorem B2602481 : Blo 1733067 2602481 := bstep (se 2 (by rfl) ⟨975930, by rfl⟩ : syracuseStep 2602481 = 1951861) B1951861
theorem B1734131 : Blo 1733067 1734131 := bstep (se 1 (by rfl) ⟨1300598, by rfl⟩ : syracuseStep 1734131 = 2601197) B2601197
theorem B1734147 : Blo 1733067 1734147 := bstep (se 1 (by rfl) ⟨1300610, by rfl⟩ : syracuseStep 1734147 = 2601221) B2601221
theorem B2602499 : Blo 1733067 2602499 := bstep (se 1 (by rfl) ⟨1951874, by rfl⟩ : syracuseStep 2602499 = 3903749) B3903749
theorem B5854733 : Blo 1733067 5854733 := bstep (se 3 (by rfl) ⟨1097762, by rfl⟩ : syracuseStep 5854733 = 2195525) B2195525
theorem B4937233 : Blo 1733067 4937233 := bstep (se 2 (by rfl) ⟨1851462, by rfl⟩ : syracuseStep 4937233 = 3702925) B3702925
theorem B1734163 : Blo 1733067 1734163 := bstep (se 1 (by rfl) ⟨1300622, by rfl⟩ : syracuseStep 1734163 = 2601245) B2601245
theorem B2602529 : Blo 1733067 2602529 := bstep (se 2 (by rfl) ⟨975948, by rfl⟩ : syracuseStep 2602529 = 1951897) B1951897
theorem B1734179 : Blo 1733067 1734179 := bstep (se 1 (by rfl) ⟨1300634, by rfl⟩ : syracuseStep 1734179 = 2601269) B2601269
theorem B1734195 : Blo 1733067 1734195 := bstep (se 1 (by rfl) ⟨1300646, by rfl⟩ : syracuseStep 1734195 = 2601293) B2601293
theorem B2602547 : Blo 1733067 2602547 := bstep (se 1 (by rfl) ⟨1951910, by rfl⟩ : syracuseStep 2602547 = 3903821) B3903821
theorem B1734211 : Blo 1733067 1734211 := bstep (se 1 (by rfl) ⟨1300658, by rfl⟩ : syracuseStep 1734211 = 2601317) B2601317
theorem B5854787 : Blo 1733067 5854787 := bstep (se 1 (by rfl) ⟨4391090, by rfl⟩ : syracuseStep 5854787 = 8782181) B8782181
theorem B2602577 : Blo 1733067 2602577 := bstep (se 2 (by rfl) ⟨975966, by rfl⟩ : syracuseStep 2602577 = 1951933) B1951933
theorem B1734227 : Blo 1733067 1734227 := bstep (se 1 (by rfl) ⟨1300670, by rfl⟩ : syracuseStep 1734227 = 2601341) B2601341
theorem B1734243 : Blo 1733067 1734243 := bstep (se 1 (by rfl) ⟨1300682, by rfl⟩ : syracuseStep 1734243 = 2601365) B2601365
theorem B2602595 : Blo 1733067 2602595 := bstep (se 1 (by rfl) ⟨1951946, by rfl⟩ : syracuseStep 2602595 = 3903893) B3903893
theorem B1734259 : Blo 1733067 1734259 := bstep (se 1 (by rfl) ⟨1300694, by rfl⟩ : syracuseStep 1734259 = 2601389) B2601389
theorem B1734275 : Blo 1733067 1734275 := bstep (se 1 (by rfl) ⟨1300706, by rfl⟩ : syracuseStep 1734275 = 2601413) B2601413
theorem B6583949 : Blo 1733067 6583949 := bstep (se 3 (by rfl) ⟨1234490, by rfl⟩ : syracuseStep 6583949 = 2468981) B2468981
theorem B1734291 : Blo 1733067 1734291 := bstep (se 1 (by rfl) ⟨1300718, by rfl⟩ : syracuseStep 1734291 = 2601437) B2601437
theorem B8779427 : Blo 1733067 8779427 := bstep (se 1 (by rfl) ⟨6584570, by rfl⟩ : syracuseStep 8779427 = 13169141) B13169141
theorem B1734307 : Blo 1733067 1734307 := bstep (se 1 (by rfl) ⟨1300730, by rfl⟩ : syracuseStep 1734307 = 2601461) B2601461
theorem B10016419 : Blo 1733067 10016419 := bstep (se 1 (by rfl) ⟨7512314, by rfl⟩ : syracuseStep 10016419 = 15024629) B15024629
theorem B1734323 : Blo 1733067 1734323 := bstep (se 1 (by rfl) ⟨1300742, by rfl⟩ : syracuseStep 1734323 = 2601485) B2601485
theorem B1734339 : Blo 1733067 1734339 := bstep (se 1 (by rfl) ⟨1300754, by rfl⟩ : syracuseStep 1734339 = 2601509) B2601509
theorem B1734355 : Blo 1733067 1734355 := bstep (se 1 (by rfl) ⟨1300766, by rfl⟩ : syracuseStep 1734355 = 2601533) B2601533
theorem B1734371 : Blo 1733067 1734371 := bstep (se 1 (by rfl) ⟨1300778, by rfl⟩ : syracuseStep 1734371 = 2601557) B2601557
theorem B19519217 : Blo 1733067 19519217 := bstep (se 2 (by rfl) ⟨7319706, by rfl⟩ : syracuseStep 19519217 = 14639413) B14639413
theorem B1734387 : Blo 1733067 1734387 := bstep (se 1 (by rfl) ⟨1300790, by rfl⟩ : syracuseStep 1734387 = 2601581) B2601581
theorem B1734403 : Blo 1733067 1734403 := bstep (se 1 (by rfl) ⟨1300802, by rfl⟩ : syracuseStep 1734403 = 2601605) B2601605
theorem B1734419 : Blo 1733067 1734419 := bstep (se 1 (by rfl) ⟨1300814, by rfl⟩ : syracuseStep 1734419 = 2601629) B2601629
theorem B4937507 : Blo 1733067 4937507 := bstep (se 1 (by rfl) ⟨3703130, by rfl⟩ : syracuseStep 4937507 = 7406261) B7406261
theorem B1734435 : Blo 1733067 1734435 := bstep (se 1 (by rfl) ⟨1300826, by rfl⟩ : syracuseStep 1734435 = 2601653) B2601653
theorem B1734451 : Blo 1733067 1734451 := bstep (se 1 (by rfl) ⟨1300838, by rfl⟩ : syracuseStep 1734451 = 2601677) B2601677
theorem B1734467 : Blo 1733067 1734467 := bstep (se 1 (by rfl) ⟨1300850, by rfl⟩ : syracuseStep 1734467 = 2601701) B2601701
theorem B5855057 : Blo 1733067 5855057 := bstep (se 2 (by rfl) ⟨2195646, by rfl⟩ : syracuseStep 5855057 = 4391293) B4391293
theorem B1734483 : Blo 1733067 1734483 := bstep (se 1 (by rfl) ⟨1300862, by rfl⟩ : syracuseStep 1734483 = 2601725) B2601725
theorem B1734499 : Blo 1733067 1734499 := bstep (se 1 (by rfl) ⟨1300874, by rfl⟩ : syracuseStep 1734499 = 2601749) B2601749
theorem B1734515 : Blo 1733067 1734515 := bstep (se 1 (by rfl) ⟨1300886, by rfl⟩ : syracuseStep 1734515 = 2601773) B2601773
theorem B2635649 : Blo 1733067 2635649 := bstep (se 2 (by rfl) ⟨988368, by rfl⟩ : syracuseStep 2635649 = 1976737) B1976737
theorem B1734531 : Blo 1733067 1734531 := bstep (se 1 (by rfl) ⟨1300898, by rfl⟩ : syracuseStep 1734531 = 2601797) B2601797
theorem B3291025 : Blo 1733067 3291025 := bstep (se 2 (by rfl) ⟨1234134, by rfl⟩ : syracuseStep 3291025 = 2468269) B2468269
theorem B1734547 : Blo 1733067 1734547 := bstep (se 1 (by rfl) ⟨1300910, by rfl⟩ : syracuseStep 1734547 = 2601821) B2601821
theorem B1734563 : Blo 1733067 1734563 := bstep (se 1 (by rfl) ⟨1300922, by rfl⟩ : syracuseStep 1734563 = 2601845) B2601845
theorem B1734579 : Blo 1733067 1734579 := bstep (se 1 (by rfl) ⟨1300934, by rfl⟩ : syracuseStep 1734579 = 2601869) B2601869
theorem B1734595 : Blo 1733067 1734595 := bstep (se 1 (by rfl) ⟨1300946, by rfl⟩ : syracuseStep 1734595 = 2601893) B2601893
theorem B1734611 : Blo 1733067 1734611 := bstep (se 1 (by rfl) ⟨1300958, by rfl⟩ : syracuseStep 1734611 = 2601917) B2601917
theorem B4937699 : Blo 1733067 4937699 := bstep (se 1 (by rfl) ⟨3703274, by rfl⟩ : syracuseStep 4937699 = 7406549) B7406549
theorem B1734627 : Blo 1733067 1734627 := bstep (se 1 (by rfl) ⟨1300970, by rfl⟩ : syracuseStep 1734627 = 2601941) B2601941
theorem B1734643 : Blo 1733067 1734643 := bstep (se 1 (by rfl) ⟨1300982, by rfl⟩ : syracuseStep 1734643 = 2601965) B2601965
theorem B1734659 : Blo 1733067 1734659 := bstep (se 1 (by rfl) ⟨1300994, by rfl⟩ : syracuseStep 1734659 = 2601989) B2601989
theorem B5928977 : Blo 1733067 5928977 := bstep (se 2 (by rfl) ⟨2223366, by rfl⟩ : syracuseStep 5928977 = 4446733) B4446733
theorem B1734675 : Blo 1733067 1734675 := bstep (se 1 (by rfl) ⟨1301006, by rfl⟩ : syracuseStep 1734675 = 2602013) B2602013
theorem B1734691 : Blo 1733067 1734691 := bstep (se 1 (by rfl) ⟨1301018, by rfl⟩ : syracuseStep 1734691 = 2602037) B2602037
theorem B3291185 : Blo 1733067 3291185 := bstep (se 2 (by rfl) ⟨1234194, by rfl⟩ : syracuseStep 3291185 = 2468389) B2468389
theorem B1734707 : Blo 1733067 1734707 := bstep (se 1 (by rfl) ⟨1301030, by rfl⟩ : syracuseStep 1734707 = 2602061) B2602061
theorem B2193475 : Blo 1733067 2193475 := bstep (se 1 (by rfl) ⟨1645106, by rfl⟩ : syracuseStep 2193475 = 3290213) B3290213
theorem B1734723 : Blo 1733067 1734723 := bstep (se 1 (by rfl) ⟨1301042, by rfl⟩ : syracuseStep 1734723 = 2602085) B2602085
theorem B1734739 : Blo 1733067 1734739 := bstep (se 1 (by rfl) ⟨1301054, by rfl⟩ : syracuseStep 1734739 = 2602109) B2602109
theorem B1734755 : Blo 1733067 1734755 := bstep (se 1 (by rfl) ⟨1301066, by rfl⟩ : syracuseStep 1734755 = 2602133) B2602133
theorem B1734771 : Blo 1733067 1734771 := bstep (se 1 (by rfl) ⟨1301078, by rfl⟩ : syracuseStep 1734771 = 2602157) B2602157
theorem B1734787 : Blo 1733067 1734787 := bstep (se 1 (by rfl) ⟨1301090, by rfl⟩ : syracuseStep 1734787 = 2602181) B2602181
theorem B1734803 : Blo 1733067 1734803 := bstep (se 1 (by rfl) ⟨1301102, by rfl⟩ : syracuseStep 1734803 = 2602205) B2602205
theorem B2193571 : Blo 1733067 2193571 := bstep (se 1 (by rfl) ⟨1645178, by rfl⟩ : syracuseStep 2193571 = 3290357) B3290357
theorem B1734819 : Blo 1733067 1734819 := bstep (se 1 (by rfl) ⟨1301114, by rfl⟩ : syracuseStep 1734819 = 2602229) B2602229
theorem B1734835 : Blo 1733067 1734835 := bstep (se 1 (by rfl) ⟨1301126, by rfl⟩ : syracuseStep 1734835 = 2602253) B2602253
theorem B1734851 : Blo 1733067 1734851 := bstep (se 1 (by rfl) ⟨1301138, by rfl⟩ : syracuseStep 1734851 = 2602277) B2602277
theorem B1734867 : Blo 1733067 1734867 := bstep (se 1 (by rfl) ⟨1301150, by rfl⟩ : syracuseStep 1734867 = 2602301) B2602301
theorem B1734883 : Blo 1733067 1734883 := bstep (se 1 (by rfl) ⟨1301162, by rfl⟩ : syracuseStep 1734883 = 2602325) B2602325
theorem B1734899 : Blo 1733067 1734899 := bstep (se 1 (by rfl) ⟨1301174, by rfl⟩ : syracuseStep 1734899 = 2602349) B2602349
theorem B1734915 : Blo 1733067 1734915 := bstep (se 1 (by rfl) ⟨1301186, by rfl⟩ : syracuseStep 1734915 = 2602373) B2602373
theorem B5552401 : Blo 1733067 5552401 := bstep (se 2 (by rfl) ⟨2082150, by rfl⟩ : syracuseStep 5552401 = 4164301) B4164301
theorem B4389137 : Blo 1733067 4389137 := bstep (se 2 (by rfl) ⟨1645926, by rfl⟩ : syracuseStep 4389137 = 3291853) B3291853
theorem B4167953 : Blo 1733067 4167953 := bstep (se 2 (by rfl) ⟨1562982, by rfl⟩ : syracuseStep 4167953 = 3125965) B3125965
theorem B1734931 : Blo 1733067 1734931 := bstep (se 1 (by rfl) ⟨1301198, by rfl⟩ : syracuseStep 1734931 = 2602397) B2602397
theorem B1734947 : Blo 1733067 1734947 := bstep (se 1 (by rfl) ⟨1301210, by rfl⟩ : syracuseStep 1734947 = 2602421) B2602421
theorem B1734963 : Blo 1733067 1734963 := bstep (se 1 (by rfl) ⟨1301222, by rfl⟩ : syracuseStep 1734963 = 2602445) B2602445
theorem B4389187 : Blo 1733067 4389187 := bstep (se 1 (by rfl) ⟨3291890, by rfl⟩ : syracuseStep 4389187 = 6583781) B6583781
theorem B1734979 : Blo 1733067 1734979 := bstep (se 1 (by rfl) ⟨1301234, by rfl⟩ : syracuseStep 1734979 = 2602469) B2602469
theorem B1734995 : Blo 1733067 1734995 := bstep (se 1 (by rfl) ⟨1301246, by rfl⟩ : syracuseStep 1734995 = 2602493) B2602493
theorem B9877859 : Blo 1733067 9877859 := bstep (se 1 (by rfl) ⟨7408394, by rfl⟩ : syracuseStep 9877859 = 14816789) B14816789
theorem B1735011 : Blo 1733067 1735011 := bstep (se 1 (by rfl) ⟨1301258, by rfl⟩ : syracuseStep 1735011 = 2602517) B2602517
theorem B5855597 : Blo 1733067 5855597 := bstep (se 3 (by rfl) ⟨1097924, by rfl⟩ : syracuseStep 5855597 = 2195849) B2195849
theorem B1735027 : Blo 1733067 1735027 := bstep (se 1 (by rfl) ⟨1301270, by rfl⟩ : syracuseStep 1735027 = 2602541) B2602541
theorem B1735043 : Blo 1733067 1735043 := bstep (se 1 (by rfl) ⟨1301282, by rfl⟩ : syracuseStep 1735043 = 2602565) B2602565
theorem B13171085 : Blo 1733067 13171085 := bstep (se 3 (by rfl) ⟨2469578, by rfl⟩ : syracuseStep 13171085 = 4939157) B4939157
theorem B1735059 : Blo 1733067 1735059 := bstep (se 1 (by rfl) ⟨1301294, by rfl⟩ : syracuseStep 1735059 = 2602589) B2602589
theorem B5855651 : Blo 1733067 5855651 := bstep (se 1 (by rfl) ⟨4391738, by rfl⟩ : syracuseStep 5855651 = 8783477) B8783477
theorem B6584753 : Blo 1733067 6584753 := bstep (se 2 (by rfl) ⟨2469282, by rfl⟩ : syracuseStep 6584753 = 4938565) B4938565
theorem B3291587 : Blo 1733067 3291587 := bstep (se 1 (by rfl) ⟨2468690, by rfl⟩ : syracuseStep 3291587 = 4937381) B4937381
theorem B8780237 : Blo 1733067 8780237 := bstep (se 3 (by rfl) ⟨1646294, by rfl⟩ : syracuseStep 8780237 = 3292589) B3292589
theorem B4389329 : Blo 1733067 4389329 := bstep (se 2 (by rfl) ⟨1645998, by rfl⟩ : syracuseStep 4389329 = 3291997) B3291997
theorem B4168145 : Blo 1733067 4168145 := bstep (se 2 (by rfl) ⟨1563054, by rfl⟩ : syracuseStep 4168145 = 3126109) B3126109
theorem B11868677 : Blo 1733067 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B17357453 : Blo 1733067 17357453 := bstep (se 3 (by rfl) ⟨3254522, by rfl⟩ : syracuseStep 17357453 = 6509045) B6509045
theorem B2374291 : Blo 1733067 2374291 := bstep (se 1 (by rfl) ⟨1780718, by rfl⟩ : syracuseStep 2374291 = 3561437) B3561437
theorem B2194067 : Blo 1733067 2194067 := bstep (se 1 (by rfl) ⟨1645550, by rfl⟩ : syracuseStep 2194067 = 3291101) B3291101
theorem B35609315 : Blo 1733067 35609315 := bstep (se 1 (by rfl) ⟨26706986, by rfl⟩ : syracuseStep 35609315 = 53413973) B53413973
theorem B4938509 : Blo 1733067 4938509 := bstep (se 3 (by rfl) ⟨925970, by rfl⟩ : syracuseStep 4938509 = 1851941) B1851941
theorem B94878485 : Blo 1733067 94878485 := bstep (se 6 (by rfl) ⟨2223714, by rfl⟩ : syracuseStep 94878485 = 4447429) B4447429
theorem B22518641 : Blo 1733067 22518641 := bstep (se 2 (by rfl) ⟨8444490, by rfl⟩ : syracuseStep 22518641 = 16888981) B16888981
theorem B4938691 : Blo 1733067 4938691 := bstep (se 1 (by rfl) ⟨3704018, by rfl⟩ : syracuseStep 4938691 = 7408037) B7408037
theorem B6249421 : Blo 1733067 6249421 := bstep (se 3 (by rfl) ⟨1171766, by rfl⟩ : syracuseStep 6249421 = 2343533) B2343533
theorem B17628131 : Blo 1733067 17628131 := bstep (se 1 (by rfl) ⟨13221098, by rfl⟩ : syracuseStep 17628131 = 26442197) B26442197
theorem B7027697 : Blo 1733067 7027697 := bstep (se 2 (by rfl) ⟨2635386, by rfl⟩ : syracuseStep 7027697 = 5270773) B5270773
theorem B11107363 : Blo 1733067 11107363 := bstep (se 1 (by rfl) ⟨8330522, by rfl⟩ : syracuseStep 11107363 = 16661045) B16661045
theorem B9370673 : Blo 1733067 9370673 := bstep (se 2 (by rfl) ⟨3514002, by rfl⟩ : syracuseStep 9370673 = 7028005) B7028005
theorem B6585421 : Blo 1733067 6585421 := bstep (se 3 (by rfl) ⟨1234766, by rfl⟩ : syracuseStep 6585421 = 2469533) B2469533
theorem B2964593 : Blo 1733067 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B4168867 : Blo 1733067 4168867 := bstep (se 1 (by rfl) ⟨3126650, by rfl⟩ : syracuseStep 4168867 = 6253301) B6253301
theorem B3292483 : Blo 1733067 3292483 := bstep (se 1 (by rfl) ⟨2469362, by rfl⟩ : syracuseStep 3292483 = 4938725) B4938725
theorem B9878861 : Blo 1733067 9878861 := bstep (se 3 (by rfl) ⟨1852286, by rfl⟩ : syracuseStep 9878861 = 3704573) B3704573
theorem B2194771 : Blo 1733067 2194771 := bstep (se 1 (by rfl) ⟨1646078, by rfl⟩ : syracuseStep 2194771 = 3292157) B3292157
theorem B4685165 : Blo 1733067 4685165 := bstep (se 3 (by rfl) ⟨878468, by rfl⟩ : syracuseStep 4685165 = 1756937) B1756937
theorem B4939181 : Blo 1733067 4939181 := bstep (se 3 (by rfl) ⟨926096, by rfl⟩ : syracuseStep 4939181 = 1852193) B1852193
theorem B4390321 : Blo 1733067 4390321 := bstep (se 2 (by rfl) ⟨1646370, by rfl⟩ : syracuseStep 4390321 = 3292741) B3292741
theorem B11115953 : Blo 1733067 11115953 := bstep (se 2 (by rfl) ⟨4168482, by rfl⟩ : syracuseStep 11115953 = 8336965) B8336965
theorem B2194867 : Blo 1733067 2194867 := bstep (se 1 (by rfl) ⟨1646150, by rfl⟩ : syracuseStep 2194867 = 3292301) B3292301
theorem B3292643 : Blo 1733067 3292643 := bstep (se 1 (by rfl) ⟨2469482, by rfl⟩ : syracuseStep 3292643 = 4938965) B4938965
theorem B3513955 : Blo 1733067 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B5275249 : Blo 1733067 5275249 := bstep (se 2 (by rfl) ⟨1978218, by rfl⟩ : syracuseStep 5275249 = 3956437) B3956437
theorem B4685489 : Blo 1733067 4685489 := bstep (se 2 (by rfl) ⟨1757058, by rfl⟩ : syracuseStep 4685489 = 3514117) B3514117
theorem B4390595 : Blo 1733067 4390595 := bstep (se 1 (by rfl) ⟨3292946, by rfl⟩ : syracuseStep 4390595 = 6585893) B6585893
theorem B3956465 : Blo 1733067 3956465 := bstep (se 2 (by rfl) ⟨1483674, by rfl⟩ : syracuseStep 3956465 = 2967349) B2967349
theorem B6586211 : Blo 1733067 6586211 := bstep (se 1 (by rfl) ⟨4939658, by rfl⟩ : syracuseStep 6586211 = 9879317) B9879317
theorem B4390787 : Blo 1733067 4390787 := bstep (se 1 (by rfl) ⟨3293090, by rfl⟩ : syracuseStep 4390787 = 6586181) B6586181
theorem B2195363 : Blo 1733067 2195363 := bstep (se 1 (by rfl) ⟨1646522, by rfl⟩ : syracuseStep 2195363 = 3293045) B3293045
theorem B1851347 : Blo 1733067 1851347 := bstep (se 1 (by rfl) ⟨1388510, by rfl⟩ : syracuseStep 1851347 = 2777021) B2777021
theorem B9879569 : Blo 1733067 9879569 := bstep (se 2 (by rfl) ⟨3704838, by rfl⟩ : syracuseStep 9879569 = 7409677) B7409677
theorem B1949719 : Blo 1733067 1949719 := bstep (se 1 (by rfl) ⟨1462289, by rfl⟩ : syracuseStep 1949719 = 2924579) B2924579
theorem B4939841 : Blo 1733067 4939841 := bstep (se 2 (by rfl) ⟨1852440, by rfl⟩ : syracuseStep 4939841 = 3704881) B3704881
theorem B2924633 : Blo 1733067 2924633 := bstep (se 2 (by rfl) ⟨1096737, by rfl⟩ : syracuseStep 2924633 = 2193475) B2193475
theorem B7405661 : Blo 1733067 7405661 := bstep (se 3 (by rfl) ⟨1388561, by rfl⟩ : syracuseStep 7405661 = 2777123) B2777123
theorem B3293273 : Blo 1733067 3293273 := bstep (se 2 (by rfl) ⟨1234977, by rfl⟩ : syracuseStep 3293273 = 2469955) B2469955
theorem B1949899 : Blo 1733067 1949899 := bstep (se 1 (by rfl) ⟨1462424, by rfl⟩ : syracuseStep 1949899 = 2924849) B2924849
theorem B2777303 : Blo 1733067 2777303 := bstep (se 1 (by rfl) ⟨2082977, by rfl⟩ : syracuseStep 2777303 = 4165955) B4165955
theorem B3899609 : Blo 1733067 3899609 := bstep (se 2 (by rfl) ⟨1462353, by rfl⟩ : syracuseStep 3899609 = 2924707) B2924707
theorem B2924761 : Blo 1733067 2924761 := bstep (se 2 (by rfl) ⟨1096785, by rfl⟩ : syracuseStep 2924761 = 2193571) B2193571
theorem B3703001 : Blo 1733067 3703001 := bstep (se 2 (by rfl) ⟨1388625, by rfl⟩ : syracuseStep 3703001 = 2777251) B2777251
theorem B3899699 : Blo 1733067 3899699 := bstep (se 1 (by rfl) ⟨2924774, by rfl⟩ : syracuseStep 3899699 = 5849549) B5849549
theorem B1950007 : Blo 1733067 1950007 := bstep (se 1 (by rfl) ⟨1462505, by rfl⟩ : syracuseStep 1950007 = 2925011) B2925011
theorem B14811457 : Blo 1733067 14811457 := bstep (se 2 (by rfl) ⟨5554296, by rfl⟩ : syracuseStep 14811457 = 11108593) B11108593
theorem B4391243 : Blo 1733067 4391243 := bstep (se 1 (by rfl) ⟨3293432, by rfl⟩ : syracuseStep 4391243 = 6586865) B6586865
theorem B3899735 : Blo 1733067 3899735 := bstep (se 1 (by rfl) ⟨2924801, by rfl⟩ : syracuseStep 3899735 = 5849603) B5849603
theorem B2777431 : Blo 1733067 2777431 := bstep (se 1 (by rfl) ⟨2083073, by rfl⟩ : syracuseStep 2777431 = 4166147) B4166147
theorem B4686169 : Blo 1733067 4686169 := bstep (se 2 (by rfl) ⟨1757313, by rfl⟩ : syracuseStep 4686169 = 3514627) B3514627
theorem B5849495 : Blo 1733067 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B4940183 : Blo 1733067 4940183 := bstep (se 1 (by rfl) ⟨3705137, by rfl⟩ : syracuseStep 4940183 = 7410275) B7410275
theorem B1950187 : Blo 1733067 1950187 := bstep (se 1 (by rfl) ⟨1462640, by rfl⟩ : syracuseStep 1950187 = 2925281) B2925281
theorem B3899915 : Blo 1733067 3899915 := bstep (se 1 (by rfl) ⟨2924936, by rfl⟩ : syracuseStep 3899915 = 5849873) B5849873
theorem B15827501 : Blo 1733067 15827501 := bstep (se 3 (by rfl) ⟨2967656, by rfl⟩ : syracuseStep 15827501 = 5935313) B5935313
theorem B3899969 : Blo 1733067 3899969 := bstep (se 2 (by rfl) ⟨1462488, by rfl⟩ : syracuseStep 3899969 = 2924977) B2924977
theorem B10551883 : Blo 1733067 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B1950295 : Blo 1733067 1950295 := bstep (se 1 (by rfl) ⟨1462721, by rfl⟩ : syracuseStep 1950295 = 2925443) B2925443
theorem B4448857 : Blo 1733067 4448857 := bstep (se 2 (by rfl) ⟨1668321, by rfl⟩ : syracuseStep 4448857 = 3336643) B3336643
theorem B3703411 : Blo 1733067 3703411 := bstep (se 1 (by rfl) ⟨2777558, by rfl⟩ : syracuseStep 3703411 = 5555117) B5555117
theorem B4391617 : Blo 1733067 4391617 := bstep (se 2 (by rfl) ⟨1646856, by rfl⟩ : syracuseStep 4391617 = 3293713) B3293713
theorem B2777815 : Blo 1733067 2777815 := bstep (se 1 (by rfl) ⟨2083361, by rfl⟩ : syracuseStep 2777815 = 4166723) B4166723
theorem B160203491 : Blo 1733067 160203491 := bstep (se 1 (by rfl) ⟨120152618, by rfl⟩ : syracuseStep 160203491 = 240305237) B240305237
theorem B1950475 : Blo 1733067 1950475 := bstep (se 1 (by rfl) ⟨1462856, by rfl⟩ : syracuseStep 1950475 = 2925713) B2925713
theorem B6587153 : Blo 1733067 6587153 := bstep (se 2 (by rfl) ⟨2470182, by rfl⟩ : syracuseStep 6587153 = 4940365) B4940365
theorem B2925335 : Blo 1733067 2925335 := bstep (se 1 (by rfl) ⟨2194001, by rfl⟩ : syracuseStep 2925335 = 4388003) B4388003
theorem B3900185 : Blo 1733067 3900185 := bstep (se 2 (by rfl) ⟨1462569, by rfl⟩ : syracuseStep 3900185 = 2925139) B2925139
theorem B3752779 : Blo 1733067 3752779 := bstep (se 1 (by rfl) ⟨2814584, by rfl⟩ : syracuseStep 3752779 = 5629169) B5629169
theorem B8782667 : Blo 1733067 8782667 := bstep (se 1 (by rfl) ⟨6587000, by rfl⟩ : syracuseStep 8782667 = 13174001) B13174001
theorem B3900275 : Blo 1733067 3900275 := bstep (se 1 (by rfl) ⟨2925206, by rfl⟩ : syracuseStep 3900275 = 5850413) B5850413
theorem B1950583 : Blo 1733067 1950583 := bstep (se 1 (by rfl) ⟨1462937, by rfl⟩ : syracuseStep 1950583 = 2925875) B2925875
theorem B9872279 : Blo 1733067 9872279 := bstep (se 1 (by rfl) ⟨7404209, by rfl⟩ : syracuseStep 9872279 = 14808419) B14808419
theorem B3900311 : Blo 1733067 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B2925463 : Blo 1733067 2925463 := bstep (se 1 (by rfl) ⟨2194097, by rfl⟩ : syracuseStep 2925463 = 4388195) B4388195
theorem B44417969 : Blo 1733067 44417969 := bstep (se 2 (by rfl) ⟨16656738, by rfl⟩ : syracuseStep 44417969 = 33313477) B33313477
theorem B5850035 : Blo 1733067 5850035 := bstep (se 1 (by rfl) ⟨4387526, by rfl⟩ : syracuseStep 5850035 = 8775053) B8775053
theorem B4686785 : Blo 1733067 4686785 := bstep (se 2 (by rfl) ⟨1757544, by rfl⟩ : syracuseStep 4686785 = 3515089) B3515089
theorem B3703745 : Blo 1733067 3703745 := bstep (se 2 (by rfl) ⟨1388904, by rfl⟩ : syracuseStep 3703745 = 2777809) B2777809
theorem B2778071 : Blo 1733067 2778071 := bstep (se 1 (by rfl) ⟨2083553, by rfl⟩ : syracuseStep 2778071 = 4167107) B4167107
theorem B1950763 : Blo 1733067 1950763 := bstep (se 1 (by rfl) ⟨1463072, by rfl⟩ : syracuseStep 1950763 = 2926145) B2926145
theorem B3900491 : Blo 1733067 3900491 := bstep (se 1 (by rfl) ⟨2925368, by rfl⟩ : syracuseStep 3900491 = 5850737) B5850737
theorem B3900545 : Blo 1733067 3900545 := bstep (se 2 (by rfl) ⟨1462704, by rfl⟩ : syracuseStep 3900545 = 2925409) B2925409
theorem B1950871 : Blo 1733067 1950871 := bstep (se 1 (by rfl) ⟨1463153, by rfl⟩ : syracuseStep 1950871 = 2926307) B2926307
theorem B5850305 : Blo 1733067 5850305 := bstep (se 2 (by rfl) ⟨2193864, by rfl⟩ : syracuseStep 5850305 = 4387729) B4387729
theorem B8332561 : Blo 1733067 8332561 := bstep (se 2 (by rfl) ⟨3124710, by rfl⟩ : syracuseStep 8332561 = 6249421) B6249421
theorem B7030081 : Blo 1733067 7030081 := bstep (se 2 (by rfl) ⟨2636280, by rfl⟩ : syracuseStep 7030081 = 5272561) B5272561
theorem B1951051 : Blo 1733067 1951051 := bstep (se 1 (by rfl) ⟨1463288, by rfl⟩ : syracuseStep 1951051 = 2926577) B2926577
theorem B3900761 : Blo 1733067 3900761 := bstep (se 2 (by rfl) ⟨1462785, by rfl⟩ : syracuseStep 3900761 = 2925571) B2925571
theorem B16885093 : Blo 1733067 16885093 := bstep (se 4 (by rfl) ⟨1582977, by rfl⟩ : syracuseStep 16885093 = 3165955) B3165955
theorem B3900851 : Blo 1733067 3900851 := bstep (se 1 (by rfl) ⟨2925638, by rfl⟩ : syracuseStep 3900851 = 5851277) B5851277
theorem B1951159 : Blo 1733067 1951159 := bstep (se 1 (by rfl) ⟨1463369, by rfl⟩ : syracuseStep 1951159 = 2926739) B2926739
theorem B3900887 : Blo 1733067 3900887 := bstep (se 1 (by rfl) ⟨2925665, by rfl⟩ : syracuseStep 3900887 = 5851331) B5851331
theorem B2926091 : Blo 1733067 2926091 := bstep (se 1 (by rfl) ⟨2194568, by rfl⟩ : syracuseStep 2926091 = 4389137) B4389137
theorem B2778635 : Blo 1733067 2778635 := bstep (se 1 (by rfl) ⟨2083976, by rfl⟩ : syracuseStep 2778635 = 4167953) B4167953
theorem B6014515 : Blo 1733067 6014515 := bstep (se 1 (by rfl) ⟨4510886, by rfl⟩ : syracuseStep 6014515 = 9021773) B9021773
theorem B1951339 : Blo 1733067 1951339 := bstep (se 1 (by rfl) ⟨1463504, by rfl⟩ : syracuseStep 1951339 = 2927009) B2927009
theorem B3901067 : Blo 1733067 3901067 := bstep (se 1 (by rfl) ⟨2925800, by rfl⟩ : syracuseStep 3901067 = 5851601) B5851601
theorem B2926219 : Blo 1733067 2926219 := bstep (se 1 (by rfl) ⟨2194664, by rfl⟩ : syracuseStep 2926219 = 4389329) B4389329
theorem B3704471 : Blo 1733067 3704471 := bstep (se 1 (by rfl) ⟨2778353, by rfl⟩ : syracuseStep 3704471 = 5556707) B5556707
theorem B3901121 : Blo 1733067 3901121 := bstep (se 2 (by rfl) ⟨1462920, by rfl⟩ : syracuseStep 3901121 = 2925841) B2925841
theorem B1951447 : Blo 1733067 1951447 := bstep (se 1 (by rfl) ⟨1463585, by rfl⟩ : syracuseStep 1951447 = 2927171) B2927171
theorem B5850845 : Blo 1733067 5850845 := bstep (se 3 (by rfl) ⟨1097033, by rfl⟩ : syracuseStep 5850845 = 2194067) B2194067
theorem B2926361 : Blo 1733067 2926361 := bstep (se 2 (by rfl) ⟨1097385, by rfl⟩ : syracuseStep 2926361 = 2194771) B2194771
theorem B63252323 : Blo 1733067 63252323 := bstep (se 1 (by rfl) ⟨47439242, by rfl⟩ : syracuseStep 63252323 = 94878485) B94878485
theorem B1951627 : Blo 1733067 1951627 := bstep (se 1 (by rfl) ⟨1463720, by rfl⟩ : syracuseStep 1951627 = 2927441) B2927441
theorem B3901337 : Blo 1733067 3901337 := bstep (se 2 (by rfl) ⟨1463001, by rfl⟩ : syracuseStep 3901337 = 2926003) B2926003
theorem B2926489 : Blo 1733067 2926489 := bstep (se 2 (by rfl) ⟨1097433, by rfl⟩ : syracuseStep 2926489 = 2194867) B2194867
theorem B3901427 : Blo 1733067 3901427 := bstep (se 1 (by rfl) ⟨2926070, by rfl⟩ : syracuseStep 3901427 = 5852141) B5852141
theorem B1951735 : Blo 1733067 1951735 := bstep (se 1 (by rfl) ⟨1463801, by rfl⟩ : syracuseStep 1951735 = 2927603) B2927603
theorem B3901463 : Blo 1733067 3901463 := bstep (se 1 (by rfl) ⟨2926097, by rfl⟩ : syracuseStep 3901463 = 5852195) B5852195
theorem B1976395 : Blo 1733067 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B1951915 : Blo 1733067 1951915 := bstep (se 1 (by rfl) ⟨1463936, by rfl⟩ : syracuseStep 1951915 = 2927873) B2927873
theorem B3901643 : Blo 1733067 3901643 := bstep (se 1 (by rfl) ⟨2926232, by rfl⟩ : syracuseStep 3901643 = 5852465) B5852465
theorem B13355225 : Blo 1733067 13355225 := bstep (se 2 (by rfl) ⟨5008209, by rfl⟩ : syracuseStep 13355225 = 10016419) B10016419
theorem B3123443 : Blo 1733067 3123443 := bstep (se 1 (by rfl) ⟨2342582, by rfl⟩ : syracuseStep 3123443 = 4685165) B4685165
theorem B3901697 : Blo 1733067 3901697 := bstep (se 2 (by rfl) ⟨1463136, by rfl⟩ : syracuseStep 3901697 = 2926273) B2926273
theorem B3123659 : Blo 1733067 3123659 := bstep (se 1 (by rfl) ⟨2342744, by rfl⟩ : syracuseStep 3123659 = 4685489) B4685489
theorem B2927063 : Blo 1733067 2927063 := bstep (se 1 (by rfl) ⟨2195297, by rfl⟩ : syracuseStep 2927063 = 4390595) B4390595
theorem B3901913 : Blo 1733067 3901913 := bstep (se 2 (by rfl) ⟨1463217, by rfl⟩ : syracuseStep 3901913 = 2926435) B2926435
theorem B3902003 : Blo 1733067 3902003 := bstep (se 1 (by rfl) ⟨2926502, by rfl⟩ : syracuseStep 3902003 = 5853005) B5853005
theorem B3902039 : Blo 1733067 3902039 := bstep (se 1 (by rfl) ⟨2926529, by rfl⟩ : syracuseStep 3902039 = 5853059) B5853059
theorem B2927191 : Blo 1733067 2927191 := bstep (se 1 (by rfl) ⟨2195393, by rfl⟩ : syracuseStep 2927191 = 4390787) B4390787
theorem B13167197 : Blo 1733067 13167197 := bstep (se 3 (by rfl) ⟨2468849, by rfl⟩ : syracuseStep 13167197 = 4937699) B4937699
theorem B7408259 : Blo 1733067 7408259 := bstep (se 1 (by rfl) ⟨5556194, by rfl⟩ : syracuseStep 7408259 = 11112389) B11112389
theorem B5556887 : Blo 1733067 5556887 := bstep (se 1 (by rfl) ⟨4167665, by rfl⟩ : syracuseStep 5556887 = 8335331) B8335331
theorem B14068403 : Blo 1733067 14068403 := bstep (se 1 (by rfl) ⟨10551302, by rfl⟩ : syracuseStep 14068403 = 21102605) B21102605
theorem B2599691 : Blo 1733067 2599691 := bstep (se 1 (by rfl) ⟨1949768, by rfl⟩ : syracuseStep 2599691 = 3899537) B3899537
theorem B3902219 : Blo 1733067 3902219 := bstep (se 1 (by rfl) ⟨2926664, by rfl⟩ : syracuseStep 3902219 = 5853329) B5853329
theorem B2599703 : Blo 1733067 2599703 := bstep (se 1 (by rfl) ⟨1949777, by rfl⟩ : syracuseStep 2599703 = 3899555) B3899555
theorem B14822189 : Blo 1733067 14822189 := bstep (se 3 (by rfl) ⟨2779160, by rfl⟩ : syracuseStep 14822189 = 5558321) B5558321
theorem B3902273 : Blo 1733067 3902273 := bstep (se 2 (by rfl) ⟨1463352, by rfl⟩ : syracuseStep 3902273 = 2926705) B2926705
theorem B5851979 : Blo 1733067 5851979 := bstep (se 1 (by rfl) ⟨4388984, by rfl⟩ : syracuseStep 5851979 = 8777969) B8777969
theorem B2599769 : Blo 1733067 2599769 := bstep (se 2 (by rfl) ⟨974913, by rfl⟩ : syracuseStep 2599769 = 1949827) B1949827
theorem B2599883 : Blo 1733067 2599883 := bstep (se 1 (by rfl) ⟨1949912, by rfl⟩ : syracuseStep 2599883 = 3899825) B3899825
theorem B2599895 : Blo 1733067 2599895 := bstep (se 1 (by rfl) ⟨1949921, by rfl⟩ : syracuseStep 2599895 = 3899843) B3899843
theorem B3337175 : Blo 1733067 3337175 := bstep (se 1 (by rfl) ⟨2502881, by rfl⟩ : syracuseStep 3337175 = 5005763) B5005763
theorem B16673809 : Blo 1733067 16673809 := bstep (se 2 (by rfl) ⟨6252678, by rfl⟩ : syracuseStep 16673809 = 12505357) B12505357
theorem B2599961 : Blo 1733067 2599961 := bstep (se 2 (by rfl) ⟨974985, by rfl⟩ : syracuseStep 2599961 = 1949971) B1949971
theorem B3902489 : Blo 1733067 3902489 := bstep (se 2 (by rfl) ⟨1463433, by rfl⟩ : syracuseStep 3902489 = 2926867) B2926867
theorem B5852249 : Blo 1733067 5852249 := bstep (se 2 (by rfl) ⟨2194593, by rfl⟩ : syracuseStep 5852249 = 4389187) B4389187
theorem B3902579 : Blo 1733067 3902579 := bstep (se 1 (by rfl) ⟨2926934, by rfl⟩ : syracuseStep 3902579 = 5853869) B5853869
theorem B8776835 : Blo 1733067 8776835 := bstep (se 1 (by rfl) ⟨6582626, by rfl⟩ : syracuseStep 8776835 = 13165253) B13165253
theorem B14281859 : Blo 1733067 14281859 := bstep (se 1 (by rfl) ⟨10711394, by rfl⟩ : syracuseStep 14281859 = 21422789) B21422789
theorem B2600075 : Blo 1733067 2600075 := bstep (se 1 (by rfl) ⟨1950056, by rfl⟩ : syracuseStep 2600075 = 3900113) B3900113
theorem B2600087 : Blo 1733067 2600087 := bstep (se 1 (by rfl) ⟨1950065, by rfl⟩ : syracuseStep 2600087 = 3900131) B3900131
theorem B3902615 : Blo 1733067 3902615 := bstep (se 1 (by rfl) ⟨2926961, by rfl⟩ : syracuseStep 3902615 = 5853923) B5853923
theorem B2927819 : Blo 1733067 2927819 := bstep (se 1 (by rfl) ⟨2195864, by rfl⟩ : syracuseStep 2927819 = 4391729) B4391729
theorem B2600153 : Blo 1733067 2600153 := bstep (se 2 (by rfl) ⟨975057, by rfl⟩ : syracuseStep 2600153 = 1950115) B1950115
theorem B28134661 : Blo 1733067 28134661 := bstep (se 4 (by rfl) ⟨2637624, by rfl⟩ : syracuseStep 28134661 = 5275249) B5275249
theorem B2600267 : Blo 1733067 2600267 := bstep (se 1 (by rfl) ⟨1950200, by rfl⟩ : syracuseStep 2600267 = 3900401) B3900401
theorem B3902795 : Blo 1733067 3902795 := bstep (se 1 (by rfl) ⟨2927096, by rfl⟩ : syracuseStep 3902795 = 5854193) B5854193
theorem B2600279 : Blo 1733067 2600279 := bstep (se 1 (by rfl) ⟨1950209, by rfl⟩ : syracuseStep 2600279 = 3900419) B3900419
theorem B3902849 : Blo 1733067 3902849 := bstep (se 2 (by rfl) ⟨1463568, by rfl⟩ : syracuseStep 3902849 = 2927137) B2927137
theorem B2600345 : Blo 1733067 2600345 := bstep (se 2 (by rfl) ⟨975129, by rfl⟩ : syracuseStep 2600345 = 1950259) B1950259
theorem B15216133 : Blo 1733067 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B2600459 : Blo 1733067 2600459 := bstep (se 1 (by rfl) ⟨1950344, by rfl⟩ : syracuseStep 2600459 = 3900689) B3900689
theorem B15822353 : Blo 1733067 15822353 := bstep (se 2 (by rfl) ⟨5933382, by rfl⟩ : syracuseStep 15822353 = 11866765) B11866765
theorem B2600471 : Blo 1733067 2600471 := bstep (se 1 (by rfl) ⟨1950353, by rfl⟩ : syracuseStep 2600471 = 3900707) B3900707
theorem B5557835 : Blo 1733067 5557835 := bstep (se 1 (by rfl) ⟨4168376, by rfl⟩ : syracuseStep 5557835 = 8336753) B8336753
theorem B2600537 : Blo 1733067 2600537 := bstep (se 2 (by rfl) ⟨975201, by rfl⟩ : syracuseStep 2600537 = 1950403) B1950403
theorem B3903065 : Blo 1733067 3903065 := bstep (se 2 (by rfl) ⟨1463649, by rfl⟩ : syracuseStep 3903065 = 2927299) B2927299
theorem B12496477 : Blo 1733067 12496477 := bstep (se 3 (by rfl) ⟨2343089, by rfl⟩ : syracuseStep 12496477 = 4686179) B4686179
theorem B3903155 : Blo 1733067 3903155 := bstep (se 1 (by rfl) ⟨2927366, by rfl⟩ : syracuseStep 3903155 = 5854733) B5854733
theorem B2600651 : Blo 1733067 2600651 := bstep (se 1 (by rfl) ⟨1950488, by rfl⟩ : syracuseStep 2600651 = 3900977) B3900977
theorem B2600663 : Blo 1733067 2600663 := bstep (se 1 (by rfl) ⟨1950497, by rfl⟩ : syracuseStep 2600663 = 3900995) B3900995
theorem B3903191 : Blo 1733067 3903191 := bstep (se 1 (by rfl) ⟨2927393, by rfl⟩ : syracuseStep 3903191 = 5854787) B5854787
theorem B6582019 : Blo 1733067 6582019 := bstep (se 1 (by rfl) ⟨4936514, by rfl⟩ : syracuseStep 6582019 = 9873029) B9873029
theorem B5852951 : Blo 1733067 5852951 := bstep (se 1 (by rfl) ⟨4389713, by rfl⟩ : syracuseStep 5852951 = 8779427) B8779427
theorem B2600729 : Blo 1733067 2600729 := bstep (se 2 (by rfl) ⟨975273, by rfl⟩ : syracuseStep 2600729 = 1950547) B1950547
theorem B13012811 : Blo 1733067 13012811 := bstep (se 1 (by rfl) ⟨9759608, by rfl⟩ : syracuseStep 13012811 = 19519217) B19519217
theorem B1978187 : Blo 1733067 1978187 := bstep (se 1 (by rfl) ⟨1483640, by rfl⟩ : syracuseStep 1978187 = 2967281) B2967281
theorem B29642597 : Blo 1733067 29642597 := bstep (se 4 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 29642597 = 5557987) B5557987
theorem B2600843 : Blo 1733067 2600843 := bstep (se 1 (by rfl) ⟨1950632, by rfl⟩ : syracuseStep 2600843 = 3901265) B3901265
theorem B3903371 : Blo 1733067 3903371 := bstep (se 1 (by rfl) ⟨2927528, by rfl⟩ : syracuseStep 3903371 = 5855057) B5855057
theorem B2600855 : Blo 1733067 2600855 := bstep (se 1 (by rfl) ⟨1950641, by rfl⟩ : syracuseStep 2600855 = 3901283) B3901283
theorem B1757099 : Blo 1733067 1757099 := bstep (se 1 (by rfl) ⟨1317824, by rfl⟩ : syracuseStep 1757099 = 2635649) B2635649
theorem B3903425 : Blo 1733067 3903425 := bstep (se 2 (by rfl) ⟨1463784, by rfl⟩ : syracuseStep 3903425 = 2927569) B2927569
theorem B2469847 : Blo 1733067 2469847 := bstep (se 1 (by rfl) ⟨1852385, by rfl⟩ : syracuseStep 2469847 = 3704771) B3704771
theorem B2600921 : Blo 1733067 2600921 := bstep (se 2 (by rfl) ⟨975345, by rfl⟩ : syracuseStep 2600921 = 1950691) B1950691
theorem B3952651 : Blo 1733067 3952651 := bstep (se 1 (by rfl) ⟨2964488, by rfl⟩ : syracuseStep 3952651 = 5928977) B5928977
theorem B12496913 : Blo 1733067 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B6582323 : Blo 1733067 6582323 := bstep (se 1 (by rfl) ⟨4936742, by rfl⟩ : syracuseStep 6582323 = 9873485) B9873485
theorem B2601035 : Blo 1733067 2601035 := bstep (se 1 (by rfl) ⟨1950776, by rfl⟩ : syracuseStep 2601035 = 3901553) B3901553
theorem B2601047 : Blo 1733067 2601047 := bstep (se 1 (by rfl) ⟨1950785, by rfl⟩ : syracuseStep 2601047 = 3901571) B3901571
theorem B12496997 : Blo 1733067 12496997 := bstep (se 4 (by rfl) ⟨1171593, by rfl⟩ : syracuseStep 12496997 = 2343187) B2343187
theorem B2601113 : Blo 1733067 2601113 := bstep (se 2 (by rfl) ⟨975417, by rfl⟩ : syracuseStep 2601113 = 1950835) B1950835
theorem B3903641 : Blo 1733067 3903641 := bstep (se 2 (by rfl) ⟨1463865, by rfl⟩ : syracuseStep 3903641 = 2927731) B2927731
theorem B5558489 : Blo 1733067 5558489 := bstep (se 2 (by rfl) ⟨2084433, by rfl⟩ : syracuseStep 5558489 = 4168867) B4168867
theorem B3903731 : Blo 1733067 3903731 := bstep (se 1 (by rfl) ⟨2927798, by rfl⟩ : syracuseStep 3903731 = 5855597) B5855597
theorem B2601227 : Blo 1733067 2601227 := bstep (se 1 (by rfl) ⟨1950920, by rfl⟩ : syracuseStep 2601227 = 3901841) B3901841
theorem B2601239 : Blo 1733067 2601239 := bstep (se 1 (by rfl) ⟨1950929, by rfl⟩ : syracuseStep 2601239 = 3901859) B3901859
theorem B3903767 : Blo 1733067 3903767 := bstep (se 1 (by rfl) ⟨2927825, by rfl⟩ : syracuseStep 3903767 = 5855651) B5855651
theorem B5853491 : Blo 1733067 5853491 := bstep (se 1 (by rfl) ⟨4390118, by rfl⟩ : syracuseStep 5853491 = 8780237) B8780237
theorem B15012161 : Blo 1733067 15012161 := bstep (se 2 (by rfl) ⟨5629560, by rfl⟩ : syracuseStep 15012161 = 11259121) B11259121
theorem B17797441 : Blo 1733067 17797441 := bstep (se 2 (by rfl) ⟨6674040, by rfl⟩ : syracuseStep 17797441 = 13348081) B13348081
theorem B2601305 : Blo 1733067 2601305 := bstep (se 2 (by rfl) ⟨975489, by rfl⟩ : syracuseStep 2601305 = 1950979) B1950979
theorem B3125633 : Blo 1733067 3125633 := bstep (se 2 (by rfl) ⟨1172112, by rfl⟩ : syracuseStep 3125633 = 2344225) B2344225
theorem B4387223 : Blo 1733067 4387223 := bstep (se 1 (by rfl) ⟨3290417, by rfl⟩ : syracuseStep 4387223 = 6580835) B6580835
theorem B11571635 : Blo 1733067 11571635 := bstep (se 1 (by rfl) ⟨8678726, by rfl⟩ : syracuseStep 11571635 = 17357453) B17357453
theorem B1733067 : Blo 1733067 1733067 := bstep (se 1 (by rfl) ⟨1299800, by rfl⟩ : syracuseStep 1733067 = 2599601) B2599601
theorem B2601419 : Blo 1733067 2601419 := bstep (se 1 (by rfl) ⟨1951064, by rfl⟩ : syracuseStep 2601419 = 3902129) B3902129
theorem B1733079 : Blo 1733067 1733079 := bstep (se 1 (by rfl) ⟨1299809, by rfl⟩ : syracuseStep 1733079 = 2599619) B2599619
theorem B2601431 : Blo 1733067 2601431 := bstep (se 1 (by rfl) ⟨1951073, by rfl⟩ : syracuseStep 2601431 = 3902147) B3902147
theorem B11858393 : Blo 1733067 11858393 := bstep (se 2 (by rfl) ⟨4446897, by rfl⟩ : syracuseStep 11858393 = 8893795) B8893795
theorem B1733099 : Blo 1733067 1733099 := bstep (se 1 (by rfl) ⟨1299824, by rfl⟩ : syracuseStep 1733099 = 2599649) B2599649
theorem B1733111 : Blo 1733067 1733111 := bstep (se 1 (by rfl) ⟨1299833, by rfl⟩ : syracuseStep 1733111 = 2599667) B2599667
theorem B1733131 : Blo 1733067 1733131 := bstep (se 1 (by rfl) ⟨1299848, by rfl⟩ : syracuseStep 1733131 = 2599697) B2599697
theorem B1733143 : Blo 1733067 1733143 := bstep (se 1 (by rfl) ⟨1299857, by rfl⟩ : syracuseStep 1733143 = 2599715) B2599715
theorem B2601497 : Blo 1733067 2601497 := bstep (se 2 (by rfl) ⟨975561, by rfl⟩ : syracuseStep 2601497 = 1951123) B1951123
theorem B1733163 : Blo 1733067 1733163 := bstep (se 1 (by rfl) ⟨1299872, by rfl⟩ : syracuseStep 1733163 = 2599745) B2599745
theorem B1733175 : Blo 1733067 1733175 := bstep (se 1 (by rfl) ⟨1299881, by rfl⟩ : syracuseStep 1733175 = 2599763) B2599763
theorem B5853761 : Blo 1733067 5853761 := bstep (se 2 (by rfl) ⟨2195160, by rfl⟩ : syracuseStep 5853761 = 4390321) B4390321
theorem B1733195 : Blo 1733067 1733195 := bstep (se 1 (by rfl) ⟨1299896, by rfl⟩ : syracuseStep 1733195 = 2599793) B2599793
theorem B15012427 : Blo 1733067 15012427 := bstep (se 1 (by rfl) ⟨11259320, by rfl⟩ : syracuseStep 15012427 = 22518641) B22518641
theorem B1733207 : Blo 1733067 1733207 := bstep (se 1 (by rfl) ⟨1299905, by rfl⟩ : syracuseStep 1733207 = 2599811) B2599811
theorem B13529693 : Blo 1733067 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B94958173 : Blo 1733067 94958173 := bstep (se 3 (by rfl) ⟨17804657, by rfl⟩ : syracuseStep 94958173 = 35609315) B35609315
theorem B1733227 : Blo 1733067 1733227 := bstep (se 1 (by rfl) ⟨1299920, by rfl⟩ : syracuseStep 1733227 = 2599841) B2599841
theorem B1733239 : Blo 1733067 1733239 := bstep (se 1 (by rfl) ⟨1299929, by rfl⟩ : syracuseStep 1733239 = 2599859) B2599859
theorem B1733259 : Blo 1733067 1733259 := bstep (se 1 (by rfl) ⟨1299944, by rfl⟩ : syracuseStep 1733259 = 2599889) B2599889
theorem B2601611 : Blo 1733067 2601611 := bstep (se 1 (by rfl) ⟨1951208, by rfl⟩ : syracuseStep 2601611 = 3902417) B3902417
theorem B1733271 : Blo 1733067 1733271 := bstep (se 1 (by rfl) ⟨1299953, by rfl⟩ : syracuseStep 1733271 = 2599907) B2599907
theorem B11752087 : Blo 1733067 11752087 := bstep (se 1 (by rfl) ⟨8814065, by rfl⟩ : syracuseStep 11752087 = 17628131) B17628131
theorem B2601623 : Blo 1733067 2601623 := bstep (se 1 (by rfl) ⟨1951217, by rfl⟩ : syracuseStep 2601623 = 3902435) B3902435
theorem B1733291 : Blo 1733067 1733291 := bstep (se 1 (by rfl) ⟨1299968, by rfl⟩ : syracuseStep 1733291 = 2599937) B2599937
theorem B13349555 : Blo 1733067 13349555 := bstep (se 1 (by rfl) ⟨10012166, by rfl⟩ : syracuseStep 13349555 = 20024333) B20024333
theorem B1733303 : Blo 1733067 1733303 := bstep (se 1 (by rfl) ⟨1299977, by rfl⟩ : syracuseStep 1733303 = 2599955) B2599955
theorem B6582977 : Blo 1733067 6582977 := bstep (se 2 (by rfl) ⟨2468616, by rfl⟩ : syracuseStep 6582977 = 4937233) B4937233
theorem B1733323 : Blo 1733067 1733323 := bstep (se 1 (by rfl) ⟨1299992, by rfl⟩ : syracuseStep 1733323 = 2599985) B2599985
theorem B6247115 : Blo 1733067 6247115 := bstep (se 1 (by rfl) ⟨4685336, by rfl⟩ : syracuseStep 6247115 = 9370673) B9370673
theorem B1733335 : Blo 1733067 1733335 := bstep (se 1 (by rfl) ⟨1300001, by rfl⟩ : syracuseStep 1733335 = 2600003) B2600003
theorem B2601689 : Blo 1733067 2601689 := bstep (se 2 (by rfl) ⟨975633, by rfl⟩ : syracuseStep 2601689 = 1951267) B1951267
theorem B1733355 : Blo 1733067 1733355 := bstep (se 1 (by rfl) ⟨1300016, by rfl⟩ : syracuseStep 1733355 = 2600033) B2600033
theorem B1733367 : Blo 1733067 1733367 := bstep (se 1 (by rfl) ⟨1300025, by rfl⟩ : syracuseStep 1733367 = 2600051) B2600051
theorem B1733387 : Blo 1733067 1733387 := bstep (se 1 (by rfl) ⟨1300040, by rfl⟩ : syracuseStep 1733387 = 2600081) B2600081
theorem B1733399 : Blo 1733067 1733399 := bstep (se 1 (by rfl) ⟨1300049, by rfl⟩ : syracuseStep 1733399 = 2600099) B2600099
theorem B1733419 : Blo 1733067 1733419 := bstep (se 1 (by rfl) ⟨1300064, by rfl⟩ : syracuseStep 1733419 = 2600129) B2600129
theorem B1733431 : Blo 1733067 1733431 := bstep (se 1 (by rfl) ⟨1300073, by rfl⟩ : syracuseStep 1733431 = 2600147) B2600147
theorem B1733451 : Blo 1733067 1733451 := bstep (se 1 (by rfl) ⟨1300088, by rfl⟩ : syracuseStep 1733451 = 2600177) B2600177
theorem B2601803 : Blo 1733067 2601803 := bstep (se 1 (by rfl) ⟨1951352, by rfl⟩ : syracuseStep 2601803 = 3902705) B3902705
theorem B1733463 : Blo 1733067 1733463 := bstep (se 1 (by rfl) ⟨1300097, by rfl⟩ : syracuseStep 1733463 = 2600195) B2600195
theorem B2601815 : Blo 1733067 2601815 := bstep (se 1 (by rfl) ⟨1951361, by rfl⟩ : syracuseStep 2601815 = 3902723) B3902723
theorem B1733483 : Blo 1733067 1733483 := bstep (se 1 (by rfl) ⟨1300112, by rfl⟩ : syracuseStep 1733483 = 2600225) B2600225
theorem B1733495 : Blo 1733067 1733495 := bstep (se 1 (by rfl) ⟨1300121, by rfl⟩ : syracuseStep 1733495 = 2600243) B2600243
theorem B1733515 : Blo 1733067 1733515 := bstep (se 1 (by rfl) ⟨1300136, by rfl⟩ : syracuseStep 1733515 = 2600273) B2600273
theorem B1733527 : Blo 1733067 1733527 := bstep (se 1 (by rfl) ⟨1300145, by rfl⟩ : syracuseStep 1733527 = 2600291) B2600291
theorem B2601881 : Blo 1733067 2601881 := bstep (se 2 (by rfl) ⟨975705, by rfl⟩ : syracuseStep 2601881 = 1951411) B1951411
theorem B1733547 : Blo 1733067 1733547 := bstep (se 1 (by rfl) ⟨1300160, by rfl⟩ : syracuseStep 1733547 = 2600321) B2600321
theorem B1733559 : Blo 1733067 1733559 := bstep (se 1 (by rfl) ⟨1300169, by rfl⟩ : syracuseStep 1733559 = 2600339) B2600339
theorem B1733579 : Blo 1733067 1733579 := bstep (se 1 (by rfl) ⟨1300184, by rfl⟩ : syracuseStep 1733579 = 2600369) B2600369
theorem B7410635 : Blo 1733067 7410635 := bstep (se 1 (by rfl) ⟨5557976, by rfl⟩ : syracuseStep 7410635 = 11115953) B11115953
theorem B1733591 : Blo 1733067 1733591 := bstep (se 1 (by rfl) ⟨1300193, by rfl⟩ : syracuseStep 1733591 = 2600387) B2600387
theorem B1733611 : Blo 1733067 1733611 := bstep (se 1 (by rfl) ⟨1300208, by rfl⟩ : syracuseStep 1733611 = 2600417) B2600417
theorem B1733623 : Blo 1733067 1733623 := bstep (se 1 (by rfl) ⟨1300217, by rfl⟩ : syracuseStep 1733623 = 2600435) B2600435
theorem B1733643 : Blo 1733067 1733643 := bstep (se 1 (by rfl) ⟨1300232, by rfl⟩ : syracuseStep 1733643 = 2600465) B2600465
theorem B2601995 : Blo 1733067 2601995 := bstep (se 1 (by rfl) ⟨1951496, by rfl⟩ : syracuseStep 2601995 = 3902993) B3902993
theorem B1733655 : Blo 1733067 1733655 := bstep (se 1 (by rfl) ⟨1300241, by rfl⟩ : syracuseStep 1733655 = 2600483) B2600483
theorem B2602007 : Blo 1733067 2602007 := bstep (se 1 (by rfl) ⟨1951505, by rfl⟩ : syracuseStep 2602007 = 3903011) B3903011
theorem B1733675 : Blo 1733067 1733675 := bstep (se 1 (by rfl) ⟨1300256, by rfl⟩ : syracuseStep 1733675 = 2600513) B2600513
theorem B4387891 : Blo 1733067 4387891 := bstep (se 1 (by rfl) ⟨3290918, by rfl⟩ : syracuseStep 4387891 = 6581837) B6581837
theorem B1733687 : Blo 1733067 1733687 := bstep (se 1 (by rfl) ⟨1300265, by rfl⟩ : syracuseStep 1733687 = 2600531) B2600531
theorem B8328257 : Blo 1733067 8328257 := bstep (se 2 (by rfl) ⟨3123096, by rfl⟩ : syracuseStep 8328257 = 6246193) B6246193
theorem B1733707 : Blo 1733067 1733707 := bstep (se 1 (by rfl) ⟨1300280, by rfl⟩ : syracuseStep 1733707 = 2600561) B2600561
theorem B1733719 : Blo 1733067 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B2602073 : Blo 1733067 2602073 := bstep (se 2 (by rfl) ⟨975777, by rfl⟩ : syracuseStep 2602073 = 1951555) B1951555
theorem B5854301 : Blo 1733067 5854301 := bstep (se 3 (by rfl) ⟨1097681, by rfl⟩ : syracuseStep 5854301 = 2195363) B2195363
theorem B1733739 : Blo 1733067 1733739 := bstep (se 1 (by rfl) ⟨1300304, by rfl⟩ : syracuseStep 1733739 = 2600609) B2600609
theorem B1733751 : Blo 1733067 1733751 := bstep (se 1 (by rfl) ⟨1300313, by rfl⟩ : syracuseStep 1733751 = 2600627) B2600627
theorem B1733771 : Blo 1733067 1733771 := bstep (se 1 (by rfl) ⟨1300328, by rfl⟩ : syracuseStep 1733771 = 2600657) B2600657
theorem B1733783 : Blo 1733067 1733783 := bstep (se 1 (by rfl) ⟨1300337, by rfl⟩ : syracuseStep 1733783 = 2600675) B2600675
theorem B1733803 : Blo 1733067 1733803 := bstep (se 1 (by rfl) ⟨1300352, by rfl⟩ : syracuseStep 1733803 = 2600705) B2600705
theorem B1733815 : Blo 1733067 1733815 := bstep (se 1 (by rfl) ⟨1300361, by rfl⟩ : syracuseStep 1733815 = 2600723) B2600723
theorem B4388033 : Blo 1733067 4388033 := bstep (se 2 (by rfl) ⟨1645512, by rfl⟩ : syracuseStep 4388033 = 3291025) B3291025
theorem B1733835 : Blo 1733067 1733835 := bstep (se 1 (by rfl) ⟨1300376, by rfl⟩ : syracuseStep 1733835 = 2600753) B2600753
theorem B2602187 : Blo 1733067 2602187 := bstep (se 1 (by rfl) ⟨1951640, by rfl⟩ : syracuseStep 2602187 = 3903281) B3903281
theorem B1733847 : Blo 1733067 1733847 := bstep (se 1 (by rfl) ⟨1300385, by rfl⟩ : syracuseStep 1733847 = 2600771) B2600771
theorem B2602199 : Blo 1733067 2602199 := bstep (se 1 (by rfl) ⟨1951649, by rfl⟩ : syracuseStep 2602199 = 3903299) B3903299
theorem B4936925 : Blo 1733067 4936925 := bstep (se 3 (by rfl) ⟨925673, by rfl⟩ : syracuseStep 4936925 = 1851347) B1851347
theorem B1733867 : Blo 1733067 1733867 := bstep (se 1 (by rfl) ⟨1300400, by rfl⟩ : syracuseStep 1733867 = 2600801) B2600801
theorem B1733879 : Blo 1733067 1733879 := bstep (se 1 (by rfl) ⟨1300409, by rfl⟩ : syracuseStep 1733879 = 2600819) B2600819
theorem B1733899 : Blo 1733067 1733899 := bstep (se 1 (by rfl) ⟨1300424, by rfl⟩ : syracuseStep 1733899 = 2600849) B2600849
theorem B1733911 : Blo 1733067 1733911 := bstep (se 1 (by rfl) ⟨1300433, by rfl⟩ : syracuseStep 1733911 = 2600867) B2600867
theorem B2602265 : Blo 1733067 2602265 := bstep (se 2 (by rfl) ⟨975849, by rfl⟩ : syracuseStep 2602265 = 1951699) B1951699
theorem B1733931 : Blo 1733067 1733931 := bstep (se 1 (by rfl) ⟨1300448, by rfl⟩ : syracuseStep 1733931 = 2600897) B2600897
theorem B1733943 : Blo 1733067 1733943 := bstep (se 1 (by rfl) ⟨1300457, by rfl⟩ : syracuseStep 1733943 = 2600915) B2600915
theorem B1733963 : Blo 1733067 1733963 := bstep (se 1 (by rfl) ⟨1300472, by rfl⟩ : syracuseStep 1733963 = 2600945) B2600945
theorem B1733975 : Blo 1733067 1733975 := bstep (se 1 (by rfl) ⟨1300481, by rfl⟩ : syracuseStep 1733975 = 2600963) B2600963
theorem B1733995 : Blo 1733067 1733995 := bstep (se 1 (by rfl) ⟨1300496, by rfl⟩ : syracuseStep 1733995 = 2600993) B2600993
theorem B1734007 : Blo 1733067 1734007 := bstep (se 1 (by rfl) ⟨1300505, by rfl⟩ : syracuseStep 1734007 = 2601011) B2601011
theorem B1734027 : Blo 1733067 1734027 := bstep (se 1 (by rfl) ⟨1300520, by rfl⟩ : syracuseStep 1734027 = 2601041) B2601041
theorem B2602379 : Blo 1733067 2602379 := bstep (se 1 (by rfl) ⟨1951784, by rfl⟩ : syracuseStep 2602379 = 3903569) B3903569
theorem B1734039 : Blo 1733067 1734039 := bstep (se 1 (by rfl) ⟨1300529, by rfl⟩ : syracuseStep 1734039 = 2601059) B2601059
theorem B2602391 : Blo 1733067 2602391 := bstep (se 1 (by rfl) ⟨1951793, by rfl⟩ : syracuseStep 2602391 = 3903587) B3903587
theorem B1734059 : Blo 1733067 1734059 := bstep (se 1 (by rfl) ⟨1300544, by rfl⟩ : syracuseStep 1734059 = 2601089) B2601089
theorem B1734071 : Blo 1733067 1734071 := bstep (se 1 (by rfl) ⟨1300553, by rfl⟩ : syracuseStep 1734071 = 2601107) B2601107
theorem B1734091 : Blo 1733067 1734091 := bstep (se 1 (by rfl) ⟨1300568, by rfl⟩ : syracuseStep 1734091 = 2601137) B2601137
theorem B1734103 : Blo 1733067 1734103 := bstep (se 1 (by rfl) ⟨1300577, by rfl⟩ : syracuseStep 1734103 = 2601155) B2601155
theorem B2602457 : Blo 1733067 2602457 := bstep (se 2 (by rfl) ⟨975921, by rfl⟩ : syracuseStep 2602457 = 1951843) B1951843
theorem B1734123 : Blo 1733067 1734123 := bstep (se 1 (by rfl) ⟨1300592, by rfl⟩ : syracuseStep 1734123 = 2601185) B2601185
theorem B1734135 : Blo 1733067 1734135 := bstep (se 1 (by rfl) ⟨1300601, by rfl⟩ : syracuseStep 1734135 = 2601203) B2601203
theorem B1734155 : Blo 1733067 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B1734167 : Blo 1733067 1734167 := bstep (se 1 (by rfl) ⟨1300625, by rfl⟩ : syracuseStep 1734167 = 2601251) B2601251
theorem B1734187 : Blo 1733067 1734187 := bstep (se 1 (by rfl) ⟨1300640, by rfl⟩ : syracuseStep 1734187 = 2601281) B2601281
theorem B4937267 : Blo 1733067 4937267 := bstep (se 1 (by rfl) ⟨3702950, by rfl⟩ : syracuseStep 4937267 = 7405901) B7405901
theorem B1734199 : Blo 1733067 1734199 := bstep (se 1 (by rfl) ⟨1300649, by rfl⟩ : syracuseStep 1734199 = 2601299) B2601299
theorem B3290699 : Blo 1733067 3290699 := bstep (se 1 (by rfl) ⟨2468024, by rfl⟩ : syracuseStep 3290699 = 4936049) B4936049
theorem B1734219 : Blo 1733067 1734219 := bstep (se 1 (by rfl) ⟨1300664, by rfl⟩ : syracuseStep 1734219 = 2601329) B2601329
theorem B2602571 : Blo 1733067 2602571 := bstep (se 1 (by rfl) ⟨1951928, by rfl⟩ : syracuseStep 2602571 = 3903857) B3903857
theorem B1734231 : Blo 1733067 1734231 := bstep (se 1 (by rfl) ⟨1300673, by rfl⟩ : syracuseStep 1734231 = 2601347) B2601347
theorem B2602583 : Blo 1733067 2602583 := bstep (se 1 (by rfl) ⟨1951937, by rfl⟩ : syracuseStep 2602583 = 3903875) B3903875
theorem B9877085 : Blo 1733067 9877085 := bstep (se 3 (by rfl) ⟨1851953, by rfl⟩ : syracuseStep 9877085 = 3703907) B3703907
theorem B1734251 : Blo 1733067 1734251 := bstep (se 1 (by rfl) ⟨1300688, by rfl⟩ : syracuseStep 1734251 = 2601377) B2601377
theorem B1734263 : Blo 1733067 1734263 := bstep (se 1 (by rfl) ⟨1300697, by rfl⟩ : syracuseStep 1734263 = 2601395) B2601395
theorem B1734283 : Blo 1733067 1734283 := bstep (se 1 (by rfl) ⟨1300712, by rfl⟩ : syracuseStep 1734283 = 2601425) B2601425
theorem B1734295 : Blo 1733067 1734295 := bstep (se 1 (by rfl) ⟨1300721, by rfl⟩ : syracuseStep 1734295 = 2601443) B2601443
theorem B1734315 : Blo 1733067 1734315 := bstep (se 1 (by rfl) ⟨1300736, by rfl⟩ : syracuseStep 1734315 = 2601473) B2601473
theorem B5273267 : Blo 1733067 5273267 := bstep (se 1 (by rfl) ⟨3954950, by rfl⟩ : syracuseStep 5273267 = 7909901) B7909901
theorem B1734327 : Blo 1733067 1734327 := bstep (se 1 (by rfl) ⟨1300745, by rfl⟩ : syracuseStep 1734327 = 2601491) B2601491
theorem B7403201 : Blo 1733067 7403201 := bstep (se 2 (by rfl) ⟨2776200, by rfl⟩ : syracuseStep 7403201 = 5552401) B5552401
theorem B1734347 : Blo 1733067 1734347 := bstep (se 1 (by rfl) ⟨1300760, by rfl⟩ : syracuseStep 1734347 = 2601521) B2601521
theorem B3610327 : Blo 1733067 3610327 := bstep (se 1 (by rfl) ⟨2707745, by rfl⟩ : syracuseStep 3610327 = 5415491) B5415491
theorem B1734359 : Blo 1733067 1734359 := bstep (se 1 (by rfl) ⟨1300769, by rfl⟩ : syracuseStep 1734359 = 2601539) B2601539
theorem B1734379 : Blo 1733067 1734379 := bstep (se 1 (by rfl) ⟨1300784, by rfl⟩ : syracuseStep 1734379 = 2601569) B2601569
theorem B1734391 : Blo 1733067 1734391 := bstep (se 1 (by rfl) ⟨1300793, by rfl⟩ : syracuseStep 1734391 = 2601587) B2601587
theorem B3290881 : Blo 1733067 3290881 := bstep (se 2 (by rfl) ⟨1234080, by rfl⟩ : syracuseStep 3290881 = 2468161) B2468161
theorem B1734411 : Blo 1733067 1734411 := bstep (se 1 (by rfl) ⟨1300808, by rfl⟩ : syracuseStep 1734411 = 2601617) B2601617
theorem B1734423 : Blo 1733067 1734423 := bstep (se 1 (by rfl) ⟨1300817, by rfl⟩ : syracuseStep 1734423 = 2601635) B2601635
theorem B1734443 : Blo 1733067 1734443 := bstep (se 1 (by rfl) ⟨1300832, by rfl⟩ : syracuseStep 1734443 = 2601665) B2601665
theorem B1734455 : Blo 1733067 1734455 := bstep (se 1 (by rfl) ⟨1300841, by rfl⟩ : syracuseStep 1734455 = 2601683) B2601683
theorem B1734475 : Blo 1733067 1734475 := bstep (se 1 (by rfl) ⟨1300856, by rfl⟩ : syracuseStep 1734475 = 2601713) B2601713
theorem B1734487 : Blo 1733067 1734487 := bstep (se 1 (by rfl) ⟨1300865, by rfl⟩ : syracuseStep 1734487 = 2601731) B2601731
theorem B1734507 : Blo 1733067 1734507 := bstep (se 1 (by rfl) ⟨1300880, by rfl⟩ : syracuseStep 1734507 = 2601761) B2601761
theorem B1734519 : Blo 1733067 1734519 := bstep (se 1 (by rfl) ⟨1300889, by rfl⟩ : syracuseStep 1734519 = 2601779) B2601779
theorem B1734539 : Blo 1733067 1734539 := bstep (se 1 (by rfl) ⟨1300904, by rfl⟩ : syracuseStep 1734539 = 2601809) B2601809
theorem B1734551 : Blo 1733067 1734551 := bstep (se 1 (by rfl) ⟨1300913, by rfl⟩ : syracuseStep 1734551 = 2601827) B2601827
theorem B1734571 : Blo 1733067 1734571 := bstep (se 1 (by rfl) ⟨1300928, by rfl⟩ : syracuseStep 1734571 = 2601857) B2601857
theorem B6584237 : Blo 1733067 6584237 := bstep (se 3 (by rfl) ⟨1234544, by rfl⟩ : syracuseStep 6584237 = 2469089) B2469089
theorem B8329139 : Blo 1733067 8329139 := bstep (se 1 (by rfl) ⟨6246854, by rfl⟩ : syracuseStep 8329139 = 12493709) B12493709
theorem B1734583 : Blo 1733067 1734583 := bstep (se 1 (by rfl) ⟨1300937, by rfl⟩ : syracuseStep 1734583 = 2601875) B2601875
theorem B6584267 : Blo 1733067 6584267 := bstep (se 1 (by rfl) ⟨4938200, by rfl⟩ : syracuseStep 6584267 = 9876401) B9876401
theorem B1734603 : Blo 1733067 1734603 := bstep (se 1 (by rfl) ⟨1300952, by rfl⟩ : syracuseStep 1734603 = 2601905) B2601905
theorem B1734615 : Blo 1733067 1734615 := bstep (se 1 (by rfl) ⟨1300961, by rfl⟩ : syracuseStep 1734615 = 2601923) B2601923
theorem B1734635 : Blo 1733067 1734635 := bstep (se 1 (by rfl) ⟨1300976, by rfl⟩ : syracuseStep 1734635 = 2601953) B2601953
theorem B1734647 : Blo 1733067 1734647 := bstep (se 1 (by rfl) ⟨1300985, by rfl⟩ : syracuseStep 1734647 = 2601971) B2601971
theorem B2193419 : Blo 1733067 2193419 := bstep (se 1 (by rfl) ⟨1645064, by rfl⟩ : syracuseStep 2193419 = 3290129) B3290129
theorem B1734667 : Blo 1733067 1734667 := bstep (se 1 (by rfl) ⟨1301000, by rfl⟩ : syracuseStep 1734667 = 2602001) B2602001
theorem B1734679 : Blo 1733067 1734679 := bstep (se 1 (by rfl) ⟨1301009, by rfl⟩ : syracuseStep 1734679 = 2602019) B2602019
theorem B1734699 : Blo 1733067 1734699 := bstep (se 1 (by rfl) ⟨1301024, by rfl⟩ : syracuseStep 1734699 = 2602049) B2602049
theorem B1734711 : Blo 1733067 1734711 := bstep (se 1 (by rfl) ⟨1301033, by rfl⟩ : syracuseStep 1734711 = 2602067) B2602067
theorem B1734731 : Blo 1733067 1734731 := bstep (se 1 (by rfl) ⟨1301048, by rfl⟩ : syracuseStep 1734731 = 2602097) B2602097
theorem B1734743 : Blo 1733067 1734743 := bstep (se 1 (by rfl) ⟨1301057, by rfl⟩ : syracuseStep 1734743 = 2602115) B2602115
theorem B12662885 : Blo 1733067 12662885 := bstep (se 4 (by rfl) ⟨1187145, by rfl⟩ : syracuseStep 12662885 = 2374291) B2374291
theorem B1734763 : Blo 1733067 1734763 := bstep (se 1 (by rfl) ⟨1301072, by rfl⟩ : syracuseStep 1734763 = 2602145) B2602145
theorem B1734775 : Blo 1733067 1734775 := bstep (se 1 (by rfl) ⟨1301081, by rfl⟩ : syracuseStep 1734775 = 2602163) B2602163
theorem B1734795 : Blo 1733067 1734795 := bstep (se 1 (by rfl) ⟨1301096, by rfl⟩ : syracuseStep 1734795 = 2602193) B2602193
theorem B1734807 : Blo 1733067 1734807 := bstep (se 1 (by rfl) ⟨1301105, by rfl⟩ : syracuseStep 1734807 = 2602211) B2602211
theorem B1734827 : Blo 1733067 1734827 := bstep (se 1 (by rfl) ⟨1301120, by rfl⟩ : syracuseStep 1734827 = 2602241) B2602241
theorem B1734839 : Blo 1733067 1734839 := bstep (se 1 (by rfl) ⟨1301129, by rfl⟩ : syracuseStep 1734839 = 2602259) B2602259
theorem B3291329 : Blo 1733067 3291329 := bstep (se 2 (by rfl) ⟨1234248, by rfl⟩ : syracuseStep 3291329 = 2468497) B2468497
theorem B1734859 : Blo 1733067 1734859 := bstep (se 1 (by rfl) ⟨1301144, by rfl⟩ : syracuseStep 1734859 = 2602289) B2602289
theorem B5855435 : Blo 1733067 5855435 := bstep (se 1 (by rfl) ⟨4391576, by rfl⟩ : syracuseStep 5855435 = 8783153) B8783153
theorem B1734871 : Blo 1733067 1734871 := bstep (se 1 (by rfl) ⟨1301153, by rfl⟩ : syracuseStep 1734871 = 2602307) B2602307
theorem B1734891 : Blo 1733067 1734891 := bstep (se 1 (by rfl) ⟨1301168, by rfl⟩ : syracuseStep 1734891 = 2602337) B2602337
theorem B1734903 : Blo 1733067 1734903 := bstep (se 1 (by rfl) ⟨1301177, by rfl⟩ : syracuseStep 1734903 = 2602355) B2602355
theorem B1734923 : Blo 1733067 1734923 := bstep (se 1 (by rfl) ⟨1301192, by rfl⟩ : syracuseStep 1734923 = 2602385) B2602385
theorem B1734935 : Blo 1733067 1734935 := bstep (se 1 (by rfl) ⟨1301201, by rfl⟩ : syracuseStep 1734935 = 2602403) B2602403
theorem B1734955 : Blo 1733067 1734955 := bstep (se 1 (by rfl) ⟨1301216, by rfl⟩ : syracuseStep 1734955 = 2602433) B2602433
theorem B19757357 : Blo 1733067 19757357 := bstep (se 3 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 19757357 = 7409009) B7409009
theorem B1734967 : Blo 1733067 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B1734987 : Blo 1733067 1734987 := bstep (se 1 (by rfl) ⟨1301240, by rfl⟩ : syracuseStep 1734987 = 2602481) B2602481
theorem B1734999 : Blo 1733067 1734999 := bstep (se 1 (by rfl) ⟨1301249, by rfl⟩ : syracuseStep 1734999 = 2602499) B2602499
theorem B1735019 : Blo 1733067 1735019 := bstep (se 1 (by rfl) ⟨1301264, by rfl⟩ : syracuseStep 1735019 = 2602529) B2602529
theorem B1735031 : Blo 1733067 1735031 := bstep (se 1 (by rfl) ⟨1301273, by rfl⟩ : syracuseStep 1735031 = 2602547) B2602547
theorem B1735051 : Blo 1733067 1735051 := bstep (se 1 (by rfl) ⟨1301288, by rfl⟩ : syracuseStep 1735051 = 2602577) B2602577
theorem B1735063 : Blo 1733067 1735063 := bstep (se 1 (by rfl) ⟨1301297, by rfl⟩ : syracuseStep 1735063 = 2602595) B2602595
theorem B4389299 : Blo 1733067 4389299 := bstep (se 1 (by rfl) ⟨3291974, by rfl⟩ : syracuseStep 4389299 = 6583949) B6583949
theorem B5855705 : Blo 1733067 5855705 := bstep (se 2 (by rfl) ⟨2195889, by rfl⟩ : syracuseStep 5855705 = 4391779) B4391779
theorem B3291671 : Blo 1733067 3291671 := bstep (se 1 (by rfl) ⟨2468753, by rfl⟩ : syracuseStep 3291671 = 4937507) B4937507
theorem B3168791 : Blo 1733067 3168791 := bstep (se 1 (by rfl) ⟨2376593, by rfl⟩ : syracuseStep 3168791 = 4753187) B4753187
theorem B11115053 : Blo 1733067 11115053 := bstep (se 3 (by rfl) ⟨2084072, by rfl⟩ : syracuseStep 11115053 = 4168145) B4168145
theorem B6584921 : Blo 1733067 6584921 := bstep (se 2 (by rfl) ⟨2469345, by rfl⟩ : syracuseStep 6584921 = 4938691) B4938691
theorem B3955351 : Blo 1733067 3955351 := bstep (se 1 (by rfl) ⟨2966513, by rfl⟩ : syracuseStep 3955351 = 5933027) B5933027
theorem B2194123 : Blo 1733067 2194123 := bstep (se 1 (by rfl) ⟨1645592, by rfl⟩ : syracuseStep 2194123 = 3291185) B3291185
theorem B14809817 : Blo 1733067 14809817 := bstep (se 2 (by rfl) ⟨5553681, by rfl⟩ : syracuseStep 14809817 = 11107363) B11107363
theorem B8780561 : Blo 1733067 8780561 := bstep (se 2 (by rfl) ⟨3292710, by rfl⟩ : syracuseStep 8780561 = 6585421) B6585421
theorem B13163309 : Blo 1733067 13163309 := bstep (se 3 (by rfl) ⟨2468120, by rfl⟩ : syracuseStep 13163309 = 4936241) B4936241
theorem B4447051 : Blo 1733067 4447051 := bstep (se 1 (by rfl) ⟨3335288, by rfl⟩ : syracuseStep 4447051 = 6670577) B6670577
theorem B6585239 : Blo 1733067 6585239 := bstep (se 1 (by rfl) ⟨4938929, by rfl⟩ : syracuseStep 6585239 = 9877859) B9877859
theorem B8780723 : Blo 1733067 8780723 := bstep (se 1 (by rfl) ⟨6585542, by rfl⟩ : syracuseStep 8780723 = 13171085) B13171085
theorem B4389835 : Blo 1733067 4389835 := bstep (se 1 (by rfl) ⟨3292376, by rfl⟩ : syracuseStep 4389835 = 6584753) B6584753
theorem B2194391 : Blo 1733067 2194391 := bstep (se 1 (by rfl) ⟨1645793, by rfl⟩ : syracuseStep 2194391 = 3291587) B3291587
theorem B7912451 : Blo 1733067 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B29629475 : Blo 1733067 29629475 := bstep (se 1 (by rfl) ⟨22222106, by rfl⟩ : syracuseStep 29629475 = 44444213) B44444213
theorem B4447307 : Blo 1733067 4447307 := bstep (se 1 (by rfl) ⟨3335480, by rfl⟩ : syracuseStep 4447307 = 6670961) B6670961
theorem B4389977 : Blo 1733067 4389977 := bstep (se 2 (by rfl) ⟨1646241, by rfl⟩ : syracuseStep 4389977 = 3292483) B3292483
theorem B3292339 : Blo 1733067 3292339 := bstep (se 1 (by rfl) ⟨2469254, by rfl⟩ : syracuseStep 3292339 = 4938509) B4938509
theorem B14818565 : Blo 1733067 14818565 := bstep (se 4 (by rfl) ⟨1389240, by rfl⟩ : syracuseStep 14818565 = 2778481) B2778481
theorem B10550573 : Blo 1733067 10550573 := bstep (se 3 (by rfl) ⟨1978232, by rfl⟩ : syracuseStep 10550573 = 3956465) B3956465
theorem B4685131 : Blo 1733067 4685131 := bstep (se 1 (by rfl) ⟨3513848, by rfl⟩ : syracuseStep 4685131 = 7027697) B7027697
theorem B4685273 : Blo 1733067 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B6585907 : Blo 1733067 6585907 := bstep (se 1 (by rfl) ⟨4939430, by rfl⟩ : syracuseStep 6585907 = 9878861) B9878861
theorem B3292787 : Blo 1733067 3292787 := bstep (se 1 (by rfl) ⟨2469590, by rfl⟩ : syracuseStep 3292787 = 4939181) B4939181
theorem B2195095 : Blo 1733067 2195095 := bstep (se 1 (by rfl) ⟨1646321, by rfl⟩ : syracuseStep 2195095 = 3292643) B3292643
theorem B3292825 : Blo 1733067 3292825 := bstep (se 2 (by rfl) ⟨1234809, by rfl⟩ : syracuseStep 3292825 = 2469619) B2469619
theorem B15818561 : Blo 1733067 15818561 := bstep (se 2 (by rfl) ⟨5931960, by rfl⟩ : syracuseStep 15818561 = 11863921) B11863921
theorem B4939613 : Blo 1733067 4939613 := bstep (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) B1852355
theorem B4390807 : Blo 1733067 4390807 := bstep (se 1 (by rfl) ⟨3293105, by rfl⟩ : syracuseStep 4390807 = 6586211) B6586211
theorem B11116439 : Blo 1733067 11116439 := bstep (se 1 (by rfl) ⟨8337329, by rfl⟩ : syracuseStep 11116439 = 16674659) B16674659
theorem B8331275 : Blo 1733067 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B6586379 : Blo 1733067 6586379 := bstep (se 1 (by rfl) ⟨4939784, by rfl⟩ : syracuseStep 6586379 = 9879569) B9879569
theorem B5849117 : Blo 1733067 5849117 := bstep (se 3 (by rfl) ⟨1096709, by rfl⟩ : syracuseStep 5849117 = 2193419) B2193419
theorem B3293227 : Blo 1733067 3293227 := bstep (se 1 (by rfl) ⟨2469920, by rfl⟩ : syracuseStep 3293227 = 4939841) B4939841
theorem B1949755 : Blo 1733067 1949755 := bstep (se 1 (by rfl) ⟨1462316, by rfl⟩ : syracuseStep 1949755 = 2924633) B2924633
theorem B2195515 : Blo 1733067 2195515 := bstep (se 1 (by rfl) ⟨1646636, by rfl⟩ : syracuseStep 2195515 = 3293273) B3293273
theorem B8331331 : Blo 1733067 8331331 := bstep (se 1 (by rfl) ⟨6248498, by rfl⟩ : syracuseStep 8331331 = 12496997) B12496997
theorem B1851535 : Blo 1733067 1851535 := bstep (se 1 (by rfl) ⟨1388651, by rfl⟩ : syracuseStep 1851535 = 2777303) B2777303
theorem B3899663 : Blo 1733067 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B2924815 : Blo 1733067 2924815 := bstep (se 1 (by rfl) ⟨2193611, by rfl⟩ : syracuseStep 2924815 = 4387223) B4387223
theorem B3293455 : Blo 1733067 3293455 := bstep (se 1 (by rfl) ⟨2470091, by rfl⟩ : syracuseStep 3293455 = 4940183) B4940183
theorem B3899681 : Blo 1733067 3899681 := bstep (se 2 (by rfl) ⟨1462380, by rfl⟩ : syracuseStep 3899681 = 2924761) B2924761
theorem B7905595 : Blo 1733067 7905595 := bstep (se 1 (by rfl) ⟨5929196, by rfl⟩ : syracuseStep 7905595 = 11858393) B11858393
theorem B10551667 : Blo 1733067 10551667 := bstep (se 1 (by rfl) ⟨7913750, by rfl⟩ : syracuseStep 10551667 = 15827501) B15827501
theorem B3703241 : Blo 1733067 3703241 := bstep (se 2 (by rfl) ⟨1388715, by rfl⟩ : syracuseStep 3703241 = 2777431) B2777431
theorem B4391435 : Blo 1733067 4391435 := bstep (se 1 (by rfl) ⟨3293576, by rfl⟩ : syracuseStep 4391435 = 6587153) B6587153
theorem B1950223 : Blo 1733067 1950223 := bstep (se 1 (by rfl) ⟨1462667, by rfl⟩ : syracuseStep 1950223 = 2925335) B2925335
theorem B19751525 : Blo 1733067 19751525 := bstep (se 4 (by rfl) ⟨1851705, by rfl⟩ : syracuseStep 19751525 = 3703411) B3703411
theorem B3900023 : Blo 1733067 3900023 := bstep (se 1 (by rfl) ⟨2925017, by rfl⟩ : syracuseStep 3900023 = 5850035) B5850035
theorem B4940423 : Blo 1733067 4940423 := bstep (se 1 (by rfl) ⟨3705317, by rfl⟩ : syracuseStep 4940423 = 7410635) B7410635
theorem B5931809 : Blo 1733067 5931809 := bstep (se 2 (by rfl) ⟨2224428, by rfl⟩ : syracuseStep 5931809 = 4448857) B4448857
theorem B3900203 : Blo 1733067 3900203 := bstep (se 1 (by rfl) ⟨2925152, by rfl⟩ : syracuseStep 3900203 = 5850305) B5850305
theorem B2925355 : Blo 1733067 2925355 := bstep (se 1 (by rfl) ⟨2194016, by rfl⟩ : syracuseStep 2925355 = 4388033) B4388033
theorem B2925497 : Blo 1733067 2925497 := bstep (se 2 (by rfl) ⟨1097061, by rfl⟩ : syracuseStep 2925497 = 2194123) B2194123
theorem B3703753 : Blo 1733067 3703753 := bstep (se 2 (by rfl) ⟨1388907, by rfl⟩ : syracuseStep 3703753 = 2777815) B2777815
theorem B1950727 : Blo 1733067 1950727 := bstep (se 1 (by rfl) ⟨1463045, by rfl⟩ : syracuseStep 1950727 = 2926091) B2926091
theorem B3900563 : Blo 1733067 3900563 := bstep (se 1 (by rfl) ⟨2925422, by rfl⟩ : syracuseStep 3900563 = 5850845) B5850845
theorem B1950907 : Blo 1733067 1950907 := bstep (se 1 (by rfl) ⟨1463180, by rfl⟩ : syracuseStep 1950907 = 2926361) B2926361
theorem B3900617 : Blo 1733067 3900617 := bstep (se 2 (by rfl) ⟨1462731, by rfl⟩ : syracuseStep 3900617 = 2925463) B2925463
theorem B5850521 : Blo 1733067 5850521 := bstep (se 2 (by rfl) ⟨2193945, by rfl⟩ : syracuseStep 5850521 = 4387891) B4387891
theorem B2082295 : Blo 1733067 2082295 := bstep (se 1 (by rfl) ⟨1561721, by rfl⟩ : syracuseStep 2082295 = 3123443) B3123443
theorem B36079181 : Blo 1733067 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B2926199 : Blo 1733067 2926199 := bstep (se 1 (by rfl) ⟨2194649, by rfl⟩ : syracuseStep 2926199 = 4389299) B4389299
theorem B2082439 : Blo 1733067 2082439 := bstep (se 1 (by rfl) ⟨1561829, by rfl⟩ : syracuseStep 2082439 = 3123659) B3123659
theorem B1951375 : Blo 1733067 1951375 := bstep (se 1 (by rfl) ⟨1463531, by rfl⟩ : syracuseStep 1951375 = 2927063) B2927063
theorem B37512881 : Blo 1733067 37512881 := bstep (se 2 (by rfl) ⟨14067330, by rfl⟩ : syracuseStep 37512881 = 28134661) B28134661
theorem B11110081 : Blo 1733067 11110081 := bstep (se 2 (by rfl) ⟨4166280, by rfl⟩ : syracuseStep 11110081 = 8332561) B8332561
theorem B23717605 : Blo 1733067 23717605 := bstep (se 4 (by rfl) ⟨2223525, by rfl⟩ : syracuseStep 23717605 = 4447051) B4447051
theorem B24987365 : Blo 1733067 24987365 := bstep (se 4 (by rfl) ⟨2342565, by rfl⟩ : syracuseStep 24987365 = 4685131) B4685131
theorem B9373441 : Blo 1733067 9373441 := bstep (se 2 (by rfl) ⟨3515040, by rfl⟩ : syracuseStep 9373441 = 7030081) B7030081
theorem B3704591 : Blo 1733067 3704591 := bstep (se 1 (by rfl) ⟨2778443, by rfl⟩ : syracuseStep 3704591 = 5556887) B5556887
theorem B22513457 : Blo 1733067 22513457 := bstep (se 2 (by rfl) ⟨8442546, by rfl⟩ : syracuseStep 22513457 = 16885093) B16885093
theorem B9873211 : Blo 1733067 9873211 := bstep (se 1 (by rfl) ⟨7404908, by rfl⟩ : syracuseStep 9873211 = 14809817) B14809817
theorem B8775539 : Blo 1733067 8775539 := bstep (se 1 (by rfl) ⟨6581654, by rfl⟩ : syracuseStep 8775539 = 13163309) B13163309
theorem B9881459 : Blo 1733067 9881459 := bstep (se 1 (by rfl) ⟨7411094, by rfl⟩ : syracuseStep 9881459 = 14822189) B14822189
theorem B3901319 : Blo 1733067 3901319 := bstep (se 1 (by rfl) ⟨2925989, by rfl⟩ : syracuseStep 3901319 = 5851979) B5851979
theorem B19752983 : Blo 1733067 19752983 := bstep (se 1 (by rfl) ⟨14814737, by rfl⟩ : syracuseStep 19752983 = 29629475) B29629475
theorem B3901499 : Blo 1733067 3901499 := bstep (se 1 (by rfl) ⟨2926124, by rfl⟩ : syracuseStep 3901499 = 5852249) B5852249
theorem B2926651 : Blo 1733067 2926651 := bstep (se 1 (by rfl) ⟨2194988, by rfl⟩ : syracuseStep 2926651 = 4389977) B4389977
theorem B5851223 : Blo 1733067 5851223 := bstep (se 1 (by rfl) ⟨4388417, by rfl⟩ : syracuseStep 5851223 = 8776835) B8776835
theorem B9521239 : Blo 1733067 9521239 := bstep (se 1 (by rfl) ⟨7140929, by rfl⟩ : syracuseStep 9521239 = 14281859) B14281859
theorem B1951879 : Blo 1733067 1951879 := bstep (se 1 (by rfl) ⟨1463909, by rfl⟩ : syracuseStep 1951879 = 2927819) B2927819
theorem B3901625 : Blo 1733067 3901625 := bstep (se 2 (by rfl) ⟨1463109, by rfl⟩ : syracuseStep 3901625 = 2926219) B2926219
theorem B2926793 : Blo 1733067 2926793 := bstep (se 2 (by rfl) ⟨1097547, by rfl⟩ : syracuseStep 2926793 = 2195095) B2195095
theorem B3123515 : Blo 1733067 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B8776025 : Blo 1733067 8776025 := bstep (se 2 (by rfl) ⟨3291009, by rfl⟩ : syracuseStep 8776025 = 6582019) B6582019
theorem B3705223 : Blo 1733067 3705223 := bstep (se 1 (by rfl) ⟨2778917, by rfl⟩ : syracuseStep 3705223 = 5557835) B5557835
theorem B3901967 : Blo 1733067 3901967 := bstep (se 1 (by rfl) ⟨2926475, by rfl⟩ : syracuseStep 3901967 = 5852951) B5852951
theorem B3901985 : Blo 1733067 3901985 := bstep (se 2 (by rfl) ⟨1463244, by rfl⟩ : syracuseStep 3901985 = 2926489) B2926489
theorem B10545707 : Blo 1733067 10545707 := bstep (se 1 (by rfl) ⟨7909280, by rfl⟩ : syracuseStep 10545707 = 15818561) B15818561
theorem B5851709 : Blo 1733067 5851709 := bstep (se 3 (by rfl) ⟨1097195, by rfl⟩ : syracuseStep 5851709 = 2194391) B2194391
theorem B7408189 : Blo 1733067 7408189 := bstep (se 3 (by rfl) ⟨1389035, by rfl⟩ : syracuseStep 7408189 = 2778071) B2778071
theorem B19761731 : Blo 1733067 19761731 := bstep (se 1 (by rfl) ⟨14821298, by rfl⟩ : syracuseStep 19761731 = 29642597) B29642597
theorem B5270201 : Blo 1733067 5270201 := bstep (se 2 (by rfl) ⟨1976325, by rfl⟩ : syracuseStep 5270201 = 3952651) B3952651
theorem B2599625 : Blo 1733067 2599625 := bstep (se 2 (by rfl) ⟨974859, by rfl⟩ : syracuseStep 2599625 = 1949719) B1949719
theorem B2599739 : Blo 1733067 2599739 := bstep (se 1 (by rfl) ⟨1949804, by rfl⟩ : syracuseStep 2599739 = 3899609) B3899609
theorem B3705659 : Blo 1733067 3705659 := bstep (se 1 (by rfl) ⟨2779244, by rfl⟩ : syracuseStep 3705659 = 5558489) B5558489
theorem B2599799 : Blo 1733067 2599799 := bstep (se 1 (by rfl) ⟨1949849, by rfl⟩ : syracuseStep 2599799 = 3899699) B3899699
theorem B3902327 : Blo 1733067 3902327 := bstep (se 1 (by rfl) ⟨2926745, by rfl⟩ : syracuseStep 3902327 = 5853491) B5853491
theorem B2927495 : Blo 1733067 2927495 := bstep (se 1 (by rfl) ⟨2195621, by rfl⟩ : syracuseStep 2927495 = 4391243) B4391243
theorem B2599823 : Blo 1733067 2599823 := bstep (se 1 (by rfl) ⟨1949867, by rfl⟩ : syracuseStep 2599823 = 3899735) B3899735
theorem B2599865 : Blo 1733067 2599865 := bstep (se 2 (by rfl) ⟨974949, by rfl⟩ : syracuseStep 2599865 = 1949899) B1949899
theorem B2599943 : Blo 1733067 2599943 := bstep (se 1 (by rfl) ⟨1949957, by rfl⟩ : syracuseStep 2599943 = 3899915) B3899915
theorem B2599979 : Blo 1733067 2599979 := bstep (se 1 (by rfl) ⟨1949984, by rfl⟩ : syracuseStep 2599979 = 3899969) B3899969
theorem B3902507 : Blo 1733067 3902507 := bstep (se 1 (by rfl) ⟨2926880, by rfl⟩ : syracuseStep 3902507 = 5853761) B5853761
theorem B2600009 : Blo 1733067 2600009 := bstep (se 2 (by rfl) ⟨975003, by rfl⟩ : syracuseStep 2600009 = 1950007) B1950007
theorem B8899703 : Blo 1733067 8899703 := bstep (se 1 (by rfl) ⟨6674777, by rfl⟩ : syracuseStep 8899703 = 13349555) B13349555
theorem B4164743 : Blo 1733067 4164743 := bstep (se 1 (by rfl) ⟨3123557, by rfl⟩ : syracuseStep 4164743 = 6247115) B6247115
theorem B106802327 : Blo 1733067 106802327 := bstep (se 1 (by rfl) ⟨80101745, by rfl⟩ : syracuseStep 106802327 = 160203491) B160203491
theorem B2600123 : Blo 1733067 2600123 := bstep (se 1 (by rfl) ⟨1950092, by rfl⟩ : syracuseStep 2600123 = 3900185) B3900185
theorem B9874669 : Blo 1733067 9874669 := bstep (se 3 (by rfl) ⟨1851500, by rfl⟩ : syracuseStep 9874669 = 3703001) B3703001
theorem B2600183 : Blo 1733067 2600183 := bstep (se 1 (by rfl) ⟨1950137, by rfl⟩ : syracuseStep 2600183 = 3900275) B3900275
theorem B6581519 : Blo 1733067 6581519 := bstep (se 1 (by rfl) ⟨4936139, by rfl⟩ : syracuseStep 6581519 = 9872279) B9872279
theorem B2600207 : Blo 1733067 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B3124523 : Blo 1733067 3124523 := bstep (se 1 (by rfl) ⟨2343392, by rfl⟩ : syracuseStep 3124523 = 4686785) B4686785
theorem B2600249 : Blo 1733067 2600249 := bstep (se 2 (by rfl) ⟨975093, by rfl⟩ : syracuseStep 2600249 = 1950187) B1950187
theorem B2600327 : Blo 1733067 2600327 := bstep (se 1 (by rfl) ⟨1950245, by rfl⟩ : syracuseStep 2600327 = 3900491) B3900491
theorem B3902867 : Blo 1733067 3902867 := bstep (se 1 (by rfl) ⟨2927150, by rfl⟩ : syracuseStep 3902867 = 5854301) B5854301
theorem B2600363 : Blo 1733067 2600363 := bstep (se 1 (by rfl) ⟨1950272, by rfl⟩ : syracuseStep 2600363 = 3900545) B3900545
theorem B20016569 : Blo 1733067 20016569 := bstep (se 2 (by rfl) ⟨7506213, by rfl⟩ : syracuseStep 20016569 = 15012427) B15012427
theorem B14069177 : Blo 1733067 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B2600393 : Blo 1733067 2600393 := bstep (se 2 (by rfl) ⟨975147, by rfl⟩ : syracuseStep 2600393 = 1950295) B1950295
theorem B3902921 : Blo 1733067 3902921 := bstep (se 2 (by rfl) ⟨1463595, by rfl⟩ : syracuseStep 3902921 = 2927191) B2927191
theorem B126610897 : Blo 1733067 126610897 := bstep (se 2 (by rfl) ⟨47479086, by rfl⟩ : syracuseStep 126610897 = 94958173) B94958173
theorem B2600507 : Blo 1733067 2600507 := bstep (se 1 (by rfl) ⟨1950380, by rfl⟩ : syracuseStep 2600507 = 3900761) B3900761
theorem B2600567 : Blo 1733067 2600567 := bstep (se 1 (by rfl) ⟨1950425, by rfl⟩ : syracuseStep 2600567 = 3900851) B3900851
theorem B2600591 : Blo 1733067 2600591 := bstep (se 1 (by rfl) ⟨1950443, by rfl⟩ : syracuseStep 2600591 = 3900887) B3900887
theorem B2600633 : Blo 1733067 2600633 := bstep (se 2 (by rfl) ⟨975237, by rfl⟩ : syracuseStep 2600633 = 1950475) B1950475
theorem B2600711 : Blo 1733067 2600711 := bstep (se 1 (by rfl) ⟨1950533, by rfl⟩ : syracuseStep 2600711 = 3901067) B3901067
theorem B2469647 : Blo 1733067 2469647 := bstep (se 1 (by rfl) ⟨1852235, by rfl⟩ : syracuseStep 2469647 = 3704471) B3704471
theorem B4935467 : Blo 1733067 4935467 := bstep (se 1 (by rfl) ⟨3701600, by rfl⟩ : syracuseStep 4935467 = 7403201) B7403201
theorem B2600747 : Blo 1733067 2600747 := bstep (se 1 (by rfl) ⟨1950560, by rfl⟩ : syracuseStep 2600747 = 3901121) B3901121
theorem B2600777 : Blo 1733067 2600777 := bstep (se 2 (by rfl) ⟨975291, by rfl⟩ : syracuseStep 2600777 = 1950583) B1950583
theorem B42168215 : Blo 1733067 42168215 := bstep (se 1 (by rfl) ⟨31626161, by rfl⟩ : syracuseStep 42168215 = 63252323) B63252323
theorem B5853113 : Blo 1733067 5853113 := bstep (se 2 (by rfl) ⟨2194917, by rfl⟩ : syracuseStep 5853113 = 4389835) B4389835
theorem B2600891 : Blo 1733067 2600891 := bstep (se 1 (by rfl) ⟨1950668, by rfl⟩ : syracuseStep 2600891 = 3901337) B3901337
theorem B2600951 : Blo 1733067 2600951 := bstep (se 1 (by rfl) ⟨1950713, by rfl⟩ : syracuseStep 2600951 = 3901427) B3901427
theorem B2600975 : Blo 1733067 2600975 := bstep (se 1 (by rfl) ⟨1950731, by rfl⟩ : syracuseStep 2600975 = 3901463) B3901463
theorem B7409693 : Blo 1733067 7409693 := bstep (se 3 (by rfl) ⟨1389317, by rfl⟩ : syracuseStep 7409693 = 2778635) B2778635
theorem B2601017 : Blo 1733067 2601017 := bstep (se 2 (by rfl) ⟨975381, by rfl⟩ : syracuseStep 2601017 = 1950763) B1950763
theorem B8441923 : Blo 1733067 8441923 := bstep (se 1 (by rfl) ⟨6331442, by rfl⟩ : syracuseStep 8441923 = 12662885) B12662885
theorem B2601095 : Blo 1733067 2601095 := bstep (se 1 (by rfl) ⟨1950821, by rfl⟩ : syracuseStep 2601095 = 3901643) B3901643
theorem B3903623 : Blo 1733067 3903623 := bstep (se 1 (by rfl) ⟨2927717, by rfl⟩ : syracuseStep 3903623 = 5855435) B5855435
theorem B2601131 : Blo 1733067 2601131 := bstep (se 1 (by rfl) ⟨1950848, by rfl⟩ : syracuseStep 2601131 = 3901697) B3901697
theorem B2601161 : Blo 1733067 2601161 := bstep (se 2 (by rfl) ⟨975435, by rfl⟩ : syracuseStep 2601161 = 1950871) B1950871
theorem B2601275 : Blo 1733067 2601275 := bstep (se 1 (by rfl) ⟨1950956, by rfl⟩ : syracuseStep 2601275 = 3901913) B3901913
theorem B3903803 : Blo 1733067 3903803 := bstep (se 1 (by rfl) ⟨2927852, by rfl⟩ : syracuseStep 3903803 = 5855705) B5855705
theorem B7410035 : Blo 1733067 7410035 := bstep (se 1 (by rfl) ⟨5557526, by rfl⟩ : syracuseStep 7410035 = 11115053) B11115053
theorem B2601335 : Blo 1733067 2601335 := bstep (se 1 (by rfl) ⟨1951001, by rfl⟩ : syracuseStep 2601335 = 3902003) B3902003
theorem B2601359 : Blo 1733067 2601359 := bstep (se 1 (by rfl) ⟨1951019, by rfl⟩ : syracuseStep 2601359 = 3902039) B3902039
theorem B8778131 : Blo 1733067 8778131 := bstep (se 1 (by rfl) ⟨6583598, by rfl⟩ : syracuseStep 8778131 = 13167197) B13167197
theorem B2601401 : Blo 1733067 2601401 := bstep (se 2 (by rfl) ⟨975525, by rfl⟩ : syracuseStep 2601401 = 1951051) B1951051
theorem B14062045 : Blo 1733067 14062045 := bstep (se 3 (by rfl) ⟨2636633, by rfl⟩ : syracuseStep 14062045 = 5273267) B5273267
theorem B1733127 : Blo 1733067 1733127 := bstep (se 1 (by rfl) ⟨1299845, by rfl⟩ : syracuseStep 1733127 = 2599691) B2599691
theorem B2601479 : Blo 1733067 2601479 := bstep (se 1 (by rfl) ⟨1951109, by rfl⟩ : syracuseStep 2601479 = 3902219) B3902219
theorem B5853707 : Blo 1733067 5853707 := bstep (se 1 (by rfl) ⟨4390280, by rfl⟩ : syracuseStep 5853707 = 8780561) B8780561
theorem B1733135 : Blo 1733067 1733135 := bstep (se 1 (by rfl) ⟨1299851, by rfl⟩ : syracuseStep 1733135 = 2599703) B2599703
theorem B2601515 : Blo 1733067 2601515 := bstep (se 1 (by rfl) ⟨1951136, by rfl⟩ : syracuseStep 2601515 = 3902273) B3902273
theorem B1733179 : Blo 1733067 1733179 := bstep (se 1 (by rfl) ⟨1299884, by rfl⟩ : syracuseStep 1733179 = 2599769) B2599769
theorem B2601545 : Blo 1733067 2601545 := bstep (se 2 (by rfl) ⟨975579, by rfl⟩ : syracuseStep 2601545 = 1951159) B1951159
theorem B5853815 : Blo 1733067 5853815 := bstep (se 1 (by rfl) ⟨4390361, by rfl⟩ : syracuseStep 5853815 = 8780723) B8780723
theorem B1733255 : Blo 1733067 1733255 := bstep (se 1 (by rfl) ⟨1299941, by rfl⟩ : syracuseStep 1733255 = 2599883) B2599883
theorem B1733263 : Blo 1733067 1733263 := bstep (se 1 (by rfl) ⟨1299947, by rfl⟩ : syracuseStep 1733263 = 2599895) B2599895
theorem B2224783 : Blo 1733067 2224783 := bstep (se 1 (by rfl) ⟨1668587, by rfl⟩ : syracuseStep 2224783 = 3337175) B3337175
theorem B20288177 : Blo 1733067 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B1733307 : Blo 1733067 1733307 := bstep (se 1 (by rfl) ⟨1299980, by rfl⟩ : syracuseStep 1733307 = 2599961) B2599961
theorem B2601659 : Blo 1733067 2601659 := bstep (se 1 (by rfl) ⟨1951244, by rfl⟩ : syracuseStep 2601659 = 3902489) B3902489
theorem B2601719 : Blo 1733067 2601719 := bstep (se 1 (by rfl) ⟨1951289, by rfl⟩ : syracuseStep 2601719 = 3902579) B3902579
theorem B1733383 : Blo 1733067 1733383 := bstep (se 1 (by rfl) ⟨1300037, by rfl⟩ : syracuseStep 1733383 = 2600075) B2600075
theorem B1733391 : Blo 1733067 1733391 := bstep (se 1 (by rfl) ⟨1300043, by rfl⟩ : syracuseStep 1733391 = 2600087) B2600087
theorem B2601743 : Blo 1733067 2601743 := bstep (se 1 (by rfl) ⟨1951307, by rfl⟩ : syracuseStep 2601743 = 3902615) B3902615
theorem B2601785 : Blo 1733067 2601785 := bstep (se 2 (by rfl) ⟨975669, by rfl⟩ : syracuseStep 2601785 = 1951339) B1951339
theorem B1733435 : Blo 1733067 1733435 := bstep (se 1 (by rfl) ⟨1300076, by rfl⟩ : syracuseStep 1733435 = 2600153) B2600153
theorem B7033715 : Blo 1733067 7033715 := bstep (se 1 (by rfl) ⟨5275286, by rfl⟩ : syracuseStep 7033715 = 10550573) B10550573
theorem B1733511 : Blo 1733067 1733511 := bstep (se 1 (by rfl) ⟨1300133, by rfl⟩ : syracuseStep 1733511 = 2600267) B2600267
theorem B2601863 : Blo 1733067 2601863 := bstep (se 1 (by rfl) ⟨1951397, by rfl⟩ : syracuseStep 2601863 = 3902795) B3902795
theorem B1733519 : Blo 1733067 1733519 := bstep (se 1 (by rfl) ⟨1300139, by rfl⟩ : syracuseStep 1733519 = 2600279) B2600279
theorem B2601899 : Blo 1733067 2601899 := bstep (se 1 (by rfl) ⟨1951424, by rfl⟩ : syracuseStep 2601899 = 3902849) B3902849
theorem B1733563 : Blo 1733067 1733563 := bstep (se 1 (by rfl) ⟨1300172, by rfl⟩ : syracuseStep 1733563 = 2600345) B2600345
theorem B4813769 : Blo 1733067 4813769 := bstep (se 2 (by rfl) ⟨1805163, by rfl⟩ : syracuseStep 4813769 = 3610327) B3610327
theorem B2601929 : Blo 1733067 2601929 := bstep (se 2 (by rfl) ⟨975723, by rfl⟩ : syracuseStep 2601929 = 1951447) B1951447
theorem B4387841 : Blo 1733067 4387841 := bstep (se 2 (by rfl) ⟨1645440, by rfl⟩ : syracuseStep 4387841 = 3290881) B3290881
theorem B1733639 : Blo 1733067 1733639 := bstep (se 1 (by rfl) ⟨1300229, by rfl⟩ : syracuseStep 1733639 = 2600459) B2600459
theorem B10548235 : Blo 1733067 10548235 := bstep (se 1 (by rfl) ⟨7911176, by rfl⟩ : syracuseStep 10548235 = 15822353) B15822353
theorem B1733647 : Blo 1733067 1733647 := bstep (se 1 (by rfl) ⟨1300235, by rfl⟩ : syracuseStep 1733647 = 2600471) B2600471
theorem B1733691 : Blo 1733067 1733691 := bstep (se 1 (by rfl) ⟨1300268, by rfl⟩ : syracuseStep 1733691 = 2600537) B2600537
theorem B2602043 : Blo 1733067 2602043 := bstep (se 1 (by rfl) ⟨1951532, by rfl⟩ : syracuseStep 2602043 = 3903065) B3903065
theorem B2602103 : Blo 1733067 2602103 := bstep (se 1 (by rfl) ⟨1951577, by rfl⟩ : syracuseStep 2602103 = 3903155) B3903155
theorem B1733767 : Blo 1733067 1733767 := bstep (se 1 (by rfl) ⟨1300325, by rfl⟩ : syracuseStep 1733767 = 2600651) B2600651
theorem B1733775 : Blo 1733067 1733775 := bstep (se 1 (by rfl) ⟨1300331, by rfl⟩ : syracuseStep 1733775 = 2600663) B2600663
theorem B2602127 : Blo 1733067 2602127 := bstep (se 1 (by rfl) ⟨1951595, by rfl⟩ : syracuseStep 2602127 = 3903191) B3903191
theorem B9876653 : Blo 1733067 9876653 := bstep (se 3 (by rfl) ⟨1851872, by rfl⟩ : syracuseStep 9876653 = 3703745) B3703745
theorem B2602169 : Blo 1733067 2602169 := bstep (se 2 (by rfl) ⟨975813, by rfl⟩ : syracuseStep 2602169 = 1951627) B1951627
theorem B1733819 : Blo 1733067 1733819 := bstep (se 1 (by rfl) ⟨1300364, by rfl⟩ : syracuseStep 1733819 = 2600729) B2600729
theorem B5854409 : Blo 1733067 5854409 := bstep (se 2 (by rfl) ⟨2195403, by rfl⟩ : syracuseStep 5854409 = 4390807) B4390807
theorem B1733895 : Blo 1733067 1733895 := bstep (se 1 (by rfl) ⟨1300421, by rfl⟩ : syracuseStep 1733895 = 2600843) B2600843
theorem B2602247 : Blo 1733067 2602247 := bstep (se 1 (by rfl) ⟨1951685, by rfl⟩ : syracuseStep 2602247 = 3903371) B3903371
theorem B1733903 : Blo 1733067 1733903 := bstep (se 1 (by rfl) ⟨1300427, by rfl⟩ : syracuseStep 1733903 = 2600855) B2600855
theorem B7410959 : Blo 1733067 7410959 := bstep (se 1 (by rfl) ⟨5558219, by rfl⟩ : syracuseStep 7410959 = 11116439) B11116439
theorem B2602283 : Blo 1733067 2602283 := bstep (se 1 (by rfl) ⟨1951712, by rfl⟩ : syracuseStep 2602283 = 3903425) B3903425
theorem B1733947 : Blo 1733067 1733947 := bstep (se 1 (by rfl) ⟨1300460, by rfl⟩ : syracuseStep 1733947 = 2600921) B2600921
theorem B2602313 : Blo 1733067 2602313 := bstep (se 2 (by rfl) ⟨975867, by rfl⟩ : syracuseStep 2602313 = 1951735) B1951735
theorem B21099869 : Blo 1733067 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B4388215 : Blo 1733067 4388215 := bstep (se 1 (by rfl) ⟨3291161, by rfl⟩ : syracuseStep 4388215 = 6582323) B6582323
theorem B1734023 : Blo 1733067 1734023 := bstep (se 1 (by rfl) ⟨1300517, by rfl⟩ : syracuseStep 1734023 = 2601035) B2601035
theorem B1734031 : Blo 1733067 1734031 := bstep (se 1 (by rfl) ⟨1300523, by rfl⟩ : syracuseStep 1734031 = 2601047) B2601047
theorem B4937107 : Blo 1733067 4937107 := bstep (se 1 (by rfl) ⟨3702830, by rfl⟩ : syracuseStep 4937107 = 7405661) B7405661
theorem B2635193 : Blo 1733067 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B1734075 : Blo 1733067 1734075 := bstep (se 1 (by rfl) ⟨1300556, by rfl⟩ : syracuseStep 1734075 = 2601113) B2601113
theorem B2602427 : Blo 1733067 2602427 := bstep (se 1 (by rfl) ⟨1951820, by rfl⟩ : syracuseStep 2602427 = 3903641) B3903641
theorem B2602487 : Blo 1733067 2602487 := bstep (se 1 (by rfl) ⟨1951865, by rfl⟩ : syracuseStep 2602487 = 3903731) B3903731
theorem B1734151 : Blo 1733067 1734151 := bstep (se 1 (by rfl) ⟨1300613, by rfl⟩ : syracuseStep 1734151 = 2601227) B2601227
theorem B1734159 : Blo 1733067 1734159 := bstep (se 1 (by rfl) ⟨1300619, by rfl⟩ : syracuseStep 1734159 = 2601239) B2601239
theorem B2602511 : Blo 1733067 2602511 := bstep (se 1 (by rfl) ⟨1951883, by rfl⟩ : syracuseStep 2602511 = 3903767) B3903767
theorem B10008107 : Blo 1733067 10008107 := bstep (se 1 (by rfl) ⟨7506080, by rfl⟩ : syracuseStep 10008107 = 15012161) B15012161
theorem B2602553 : Blo 1733067 2602553 := bstep (se 2 (by rfl) ⟨975957, by rfl⟩ : syracuseStep 2602553 = 1951915) B1951915
theorem B1734203 : Blo 1733067 1734203 := bstep (se 1 (by rfl) ⟨1300652, by rfl⟩ : syracuseStep 1734203 = 2601305) B2601305
theorem B7714423 : Blo 1733067 7714423 := bstep (se 1 (by rfl) ⟨5785817, by rfl⟩ : syracuseStep 7714423 = 11571635) B11571635
theorem B1734279 : Blo 1733067 1734279 := bstep (se 1 (by rfl) ⟨1300709, by rfl⟩ : syracuseStep 1734279 = 2601419) B2601419
theorem B1734287 : Blo 1733067 1734287 := bstep (se 1 (by rfl) ⟨1300715, by rfl⟩ : syracuseStep 1734287 = 2601431) B2601431
theorem B1734331 : Blo 1733067 1734331 := bstep (se 1 (by rfl) ⟨1300748, by rfl⟩ : syracuseStep 1734331 = 2601497) B2601497
theorem B19748609 : Blo 1733067 19748609 := bstep (se 2 (by rfl) ⟨7405728, by rfl⟩ : syracuseStep 19748609 = 14811457) B14811457
theorem B23729921 : Blo 1733067 23729921 := bstep (se 2 (by rfl) ⟨8898720, by rfl⟩ : syracuseStep 23729921 = 17797441) B17797441
theorem B1734407 : Blo 1733067 1734407 := bstep (se 1 (by rfl) ⟨1300805, by rfl⟩ : syracuseStep 1734407 = 2601611) B2601611
theorem B1734415 : Blo 1733067 1734415 := bstep (se 1 (by rfl) ⟨1300811, by rfl⟩ : syracuseStep 1734415 = 2601623) B2601623
theorem B6248225 : Blo 1733067 6248225 := bstep (se 2 (by rfl) ⟨2343084, by rfl⟩ : syracuseStep 6248225 = 4686169) B4686169
theorem B4388651 : Blo 1733067 4388651 := bstep (se 1 (by rfl) ⟨3291488, by rfl⟩ : syracuseStep 4388651 = 6582977) B6582977
theorem B1734459 : Blo 1733067 1734459 := bstep (se 1 (by rfl) ⟨1300844, by rfl⟩ : syracuseStep 1734459 = 2601689) B2601689
theorem B1734535 : Blo 1733067 1734535 := bstep (se 1 (by rfl) ⟨1300901, by rfl⟩ : syracuseStep 1734535 = 2601803) B2601803
theorem B5855111 : Blo 1733067 5855111 := bstep (se 1 (by rfl) ⟨4391333, by rfl⟩ : syracuseStep 5855111 = 8782667) B8782667
theorem B1734543 : Blo 1733067 1734543 := bstep (se 1 (by rfl) ⟨1300907, by rfl⟩ : syracuseStep 1734543 = 2601815) B2601815
theorem B1734587 : Blo 1733067 1734587 := bstep (se 1 (by rfl) ⟨1300940, by rfl⟩ : syracuseStep 1734587 = 2601881) B2601881
theorem B29611979 : Blo 1733067 29611979 := bstep (se 1 (by rfl) ⟨22208984, by rfl⟩ : syracuseStep 29611979 = 44417969) B44417969
theorem B1734663 : Blo 1733067 1734663 := bstep (se 1 (by rfl) ⟨1300997, by rfl⟩ : syracuseStep 1734663 = 2601995) B2601995
theorem B1734671 : Blo 1733067 1734671 := bstep (se 1 (by rfl) ⟨1301003, by rfl⟩ : syracuseStep 1734671 = 2602007) B2602007
theorem B5552171 : Blo 1733067 5552171 := bstep (se 1 (by rfl) ⟨4164128, by rfl⟩ : syracuseStep 5552171 = 8328257) B8328257
theorem B1734715 : Blo 1733067 1734715 := bstep (se 1 (by rfl) ⟨1301036, by rfl⟩ : syracuseStep 1734715 = 2602073) B2602073
theorem B1734791 : Blo 1733067 1734791 := bstep (se 1 (by rfl) ⟨1301093, by rfl⟩ : syracuseStep 1734791 = 2602187) B2602187
theorem B1734799 : Blo 1733067 1734799 := bstep (se 1 (by rfl) ⟨1301099, by rfl⟩ : syracuseStep 1734799 = 2602199) B2602199
theorem B3291283 : Blo 1733067 3291283 := bstep (se 1 (by rfl) ⟨2468462, by rfl⟩ : syracuseStep 3291283 = 4936925) B4936925
theorem B1734843 : Blo 1733067 1734843 := bstep (se 1 (by rfl) ⟨1301132, by rfl⟩ : syracuseStep 1734843 = 2602265) B2602265
theorem B15669449 : Blo 1733067 15669449 := bstep (se 2 (by rfl) ⟨5876043, by rfl⟩ : syracuseStep 15669449 = 11752087) B11752087
theorem B5273801 : Blo 1733067 5273801 := bstep (se 2 (by rfl) ⟨1977675, by rfl⟩ : syracuseStep 5273801 = 3955351) B3955351
theorem B5855489 : Blo 1733067 5855489 := bstep (se 2 (by rfl) ⟨2195808, by rfl⟩ : syracuseStep 5855489 = 4391617) B4391617
theorem B1734919 : Blo 1733067 1734919 := bstep (se 1 (by rfl) ⟨1301189, by rfl⟩ : syracuseStep 1734919 = 2602379) B2602379
theorem B1734927 : Blo 1733067 1734927 := bstep (se 1 (by rfl) ⟨1301195, by rfl⟩ : syracuseStep 1734927 = 2602391) B2602391
theorem B1734971 : Blo 1733067 1734971 := bstep (se 1 (by rfl) ⟨1301228, by rfl⟩ : syracuseStep 1734971 = 2602457) B2602457
theorem B3291511 : Blo 1733067 3291511 := bstep (se 1 (by rfl) ⟨2468633, by rfl⟩ : syracuseStep 3291511 = 4937267) B4937267
theorem B2193799 : Blo 1733067 2193799 := bstep (se 1 (by rfl) ⟨1645349, by rfl⟩ : syracuseStep 2193799 = 3290699) B3290699
theorem B1735047 : Blo 1733067 1735047 := bstep (se 1 (by rfl) ⟨1301285, by rfl⟩ : syracuseStep 1735047 = 2602571) B2602571
theorem B1735055 : Blo 1733067 1735055 := bstep (se 1 (by rfl) ⟨1301291, by rfl⟩ : syracuseStep 1735055 = 2602583) B2602583
theorem B6584723 : Blo 1733067 6584723 := bstep (se 1 (by rfl) ⟨4938542, by rfl⟩ : syracuseStep 6584723 = 9877085) B9877085
theorem B5003705 : Blo 1733067 5003705 := bstep (se 2 (by rfl) ⟨1876389, by rfl⟩ : syracuseStep 5003705 = 3752779) B3752779
theorem B4389491 : Blo 1733067 4389491 := bstep (se 1 (by rfl) ⟨3292118, by rfl⟩ : syracuseStep 4389491 = 6584237) B6584237
theorem B5552759 : Blo 1733067 5552759 := bstep (se 1 (by rfl) ⟨4164569, by rfl⟩ : syracuseStep 5552759 = 8329139) B8329139
theorem B4389511 : Blo 1733067 4389511 := bstep (se 1 (by rfl) ⟨3292133, by rfl⟩ : syracuseStep 4389511 = 6584267) B6584267
theorem B33340085 : Blo 1733067 33340085 := bstep (se 5 (by rfl) ⟨1562816, by rfl⟩ : syracuseStep 33340085 = 3125633) B3125633
theorem B22231745 : Blo 1733067 22231745 := bstep (se 2 (by rfl) ⟨8336904, by rfl⟩ : syracuseStep 22231745 = 16673809) B16673809
theorem B2194219 : Blo 1733067 2194219 := bstep (se 1 (by rfl) ⟨1645664, by rfl⟩ : syracuseStep 2194219 = 3291329) B3291329
theorem B8903483 : Blo 1733067 8903483 := bstep (se 1 (by rfl) ⟨6677612, by rfl⟩ : syracuseStep 8903483 = 13355225) B13355225
theorem B13171571 : Blo 1733067 13171571 := bstep (se 1 (by rfl) ⟨9878678, by rfl⟩ : syracuseStep 13171571 = 19757357) B19757357
theorem B4389785 : Blo 1733067 4389785 := bstep (se 2 (by rfl) ⟨1646169, by rfl⟩ : syracuseStep 4389785 = 3292339) B3292339
theorem B2194447 : Blo 1733067 2194447 := bstep (se 1 (by rfl) ⟨1645835, by rfl⟩ : syracuseStep 2194447 = 3291671) B3291671
theorem B2112527 : Blo 1733067 2112527 := bstep (se 1 (by rfl) ⟨1584395, by rfl⟩ : syracuseStep 2112527 = 3168791) B3168791
theorem B4389947 : Blo 1733067 4389947 := bstep (se 1 (by rfl) ⟨3292460, by rfl⟩ : syracuseStep 4389947 = 6584921) B6584921
theorem B4938839 : Blo 1733067 4938839 := bstep (se 1 (by rfl) ⟨3704129, by rfl⟩ : syracuseStep 4938839 = 7408259) B7408259
theorem B9378935 : Blo 1733067 9378935 := bstep (se 1 (by rfl) ⟨7034201, by rfl⟩ : syracuseStep 9378935 = 14068403) B14068403
theorem B4390159 : Blo 1733067 4390159 := bstep (se 1 (by rfl) ⟨3292619, by rfl⟩ : syracuseStep 4390159 = 6585239) B6585239
theorem B2964871 : Blo 1733067 2964871 := bstep (se 1 (by rfl) ⟨2223653, by rfl⟩ : syracuseStep 2964871 = 4447307) B4447307
theorem B8019353 : Blo 1733067 8019353 := bstep (se 2 (by rfl) ⟨3007257, by rfl⟩ : syracuseStep 8019353 = 6014515) B6014515
theorem B8781209 : Blo 1733067 8781209 := bstep (se 2 (by rfl) ⟨3292953, by rfl⟩ : syracuseStep 8781209 = 6585907) B6585907
theorem B16661969 : Blo 1733067 16661969 := bstep (se 2 (by rfl) ⟨6248238, by rfl⟩ : syracuseStep 16661969 = 12496477) B12496477
theorem B9879043 : Blo 1733067 9879043 := bstep (se 1 (by rfl) ⟨7409282, by rfl⟩ : syracuseStep 9879043 = 14818565) B14818565
theorem B5275165 : Blo 1733067 5275165 := bstep (se 3 (by rfl) ⟨989093, by rfl⟩ : syracuseStep 5275165 = 1978187) B1978187
theorem B4390433 : Blo 1733067 4390433 := bstep (se 2 (by rfl) ⟨1646412, by rfl⟩ : syracuseStep 4390433 = 3292825) B3292825
theorem B2195191 : Blo 1733067 2195191 := bstep (se 1 (by rfl) ⟨1646393, by rfl⟩ : syracuseStep 2195191 = 3292787) B3292787
theorem B4685597 : Blo 1733067 4685597 := bstep (se 3 (by rfl) ⟨878549, by rfl⟩ : syracuseStep 4685597 = 1757099) B1757099
theorem B8675207 : Blo 1733067 8675207 := bstep (se 1 (by rfl) ⟨6506405, by rfl⟩ : syracuseStep 8675207 = 13012811) B13012811
theorem B3293075 : Blo 1733067 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B3293129 : Blo 1733067 3293129 := bstep (se 2 (by rfl) ⟨1234923, by rfl⟩ : syracuseStep 3293129 = 2469847) B2469847
theorem B5554183 : Blo 1733067 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B4390919 : Blo 1733067 4390919 := bstep (se 1 (by rfl) ⟨3293189, by rfl⟩ : syracuseStep 4390919 = 6586379) B6586379
theorem B3899411 : Blo 1733067 3899411 := bstep (se 1 (by rfl) ⟨2924558, by rfl⟩ : syracuseStep 3899411 = 5849117) B5849117
theorem B4939795 : Blo 1733067 4939795 := bstep (se 1 (by rfl) ⟨3704846, by rfl⟩ : syracuseStep 4939795 = 7409693) B7409693
theorem B4390969 : Blo 1733067 4390969 := bstep (se 2 (by rfl) ⟨1646613, by rfl⟩ : syracuseStep 4390969 = 3293227) B3293227
theorem B11255897 : Blo 1733067 11255897 := bstep (se 2 (by rfl) ⟨4220961, by rfl⟩ : syracuseStep 11255897 = 8441923) B8441923
theorem B11108441 : Blo 1733067 11108441 := bstep (se 2 (by rfl) ⟨4165665, by rfl⟩ : syracuseStep 11108441 = 8331331) B8331331
theorem B4940023 : Blo 1733067 4940023 := bstep (se 1 (by rfl) ⟨3705017, by rfl⟩ : syracuseStep 4940023 = 7410035) B7410035
theorem B3899753 : Blo 1733067 3899753 := bstep (se 2 (by rfl) ⟨1462407, by rfl⟩ : syracuseStep 3899753 = 2924815) B2924815
theorem B4391273 : Blo 1733067 4391273 := bstep (se 2 (by rfl) ⟨1646727, by rfl⟩ : syracuseStep 4391273 = 3293455) B3293455
theorem B3293615 : Blo 1733067 3293615 := bstep (se 1 (by rfl) ⟨2470211, by rfl⟩ : syracuseStep 3293615 = 4940423) B4940423
theorem B13525451 : Blo 1733067 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B2925065 : Blo 1733067 2925065 := bstep (se 2 (by rfl) ⟨1096899, by rfl⟩ : syracuseStep 2925065 = 2193799) B2193799
theorem B4940297 : Blo 1733067 4940297 := bstep (se 2 (by rfl) ⟨1852611, by rfl⟩ : syracuseStep 4940297 = 3705223) B3705223
theorem B1950331 : Blo 1733067 1950331 := bstep (se 1 (by rfl) ⟨1462748, by rfl⟩ : syracuseStep 1950331 = 2925497) B2925497
theorem B2925227 : Blo 1733067 2925227 := bstep (se 1 (by rfl) ⟨2193920, by rfl⟩ : syracuseStep 2925227 = 4387841) B4387841
theorem B4940639 : Blo 1733067 4940639 := bstep (se 1 (by rfl) ⟨3705479, by rfl⟩ : syracuseStep 4940639 = 7410959) B7410959
theorem B2966377 : Blo 1733067 2966377 := bstep (se 2 (by rfl) ⟨1112391, by rfl⟩ : syracuseStep 2966377 = 2224783) B2224783
theorem B14066579 : Blo 1733067 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B3900347 : Blo 1733067 3900347 := bstep (se 1 (by rfl) ⟨2925260, by rfl⟩ : syracuseStep 3900347 = 5850521) B5850521
theorem B24052787 : Blo 1733067 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B3900473 : Blo 1733067 3900473 := bstep (se 2 (by rfl) ⟨1462677, by rfl⟩ : syracuseStep 3900473 = 2925355) B2925355
theorem B2925625 : Blo 1733067 2925625 := bstep (se 2 (by rfl) ⟨1097109, by rfl⟩ : syracuseStep 2925625 = 2194219) B2194219
theorem B1950799 : Blo 1733067 1950799 := bstep (se 1 (by rfl) ⟨1463099, by rfl⟩ : syracuseStep 1950799 = 2926199) B2926199
theorem B13165739 : Blo 1733067 13165739 := bstep (se 1 (by rfl) ⟨9874304, by rfl⟩ : syracuseStep 13165739 = 19748609) B19748609
theorem B15819947 : Blo 1733067 15819947 := bstep (se 1 (by rfl) ⟨11864960, by rfl⟩ : syracuseStep 15819947 = 23729921) B23729921
theorem B2925767 : Blo 1733067 2925767 := bstep (se 1 (by rfl) ⟨2194325, by rfl⟩ : syracuseStep 2925767 = 4388651) B4388651
theorem B15008971 : Blo 1733067 15008971 := bstep (se 1 (by rfl) ⟨11256728, by rfl⟩ : syracuseStep 15008971 = 22513457) B22513457
theorem B5850359 : Blo 1733067 5850359 := bstep (se 1 (by rfl) ⟨4387769, by rfl⟩ : syracuseStep 5850359 = 8775539) B8775539
theorem B6587639 : Blo 1733067 6587639 := bstep (se 1 (by rfl) ⟨4940729, by rfl⟩ : syracuseStep 6587639 = 9881459) B9881459
theorem B2925929 : Blo 1733067 2925929 := bstep (se 2 (by rfl) ⟨1097223, by rfl⟩ : syracuseStep 2925929 = 2194447) B2194447
theorem B3900815 : Blo 1733067 3900815 := bstep (se 1 (by rfl) ⟨2925611, by rfl⟩ : syracuseStep 3900815 = 5851223) B5851223
theorem B10446299 : Blo 1733067 10446299 := bstep (se 1 (by rfl) ⟨7834724, by rfl⟩ : syracuseStep 10446299 = 15669449) B15669449
theorem B3515867 : Blo 1733067 3515867 := bstep (se 1 (by rfl) ⟨2636900, by rfl⟩ : syracuseStep 3515867 = 5273801) B5273801
theorem B1951195 : Blo 1733067 1951195 := bstep (se 1 (by rfl) ⟨1463396, by rfl⟩ : syracuseStep 1951195 = 2926793) B2926793
theorem B2082343 : Blo 1733067 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B5850683 : Blo 1733067 5850683 := bstep (se 1 (by rfl) ⟨4388012, by rfl⟩ : syracuseStep 5850683 = 8776025) B8776025
theorem B3335803 : Blo 1733067 3335803 := bstep (se 1 (by rfl) ⟨2501852, by rfl⟩ : syracuseStep 3335803 = 5003705) B5003705
theorem B13166225 : Blo 1733067 13166225 := bstep (se 2 (by rfl) ⟨4937334, by rfl⟩ : syracuseStep 13166225 = 9874669) B9874669
theorem B7030471 : Blo 1733067 7030471 := bstep (se 1 (by rfl) ⟨5272853, by rfl⟩ : syracuseStep 7030471 = 10545707) B10545707
theorem B3901139 : Blo 1733067 3901139 := bstep (se 1 (by rfl) ⟨2925854, by rfl⟩ : syracuseStep 3901139 = 5851709) B5851709
theorem B13174487 : Blo 1733067 13174487 := bstep (se 1 (by rfl) ⟨9880865, by rfl⟩ : syracuseStep 13174487 = 19761731) B19761731
theorem B2926327 : Blo 1733067 2926327 := bstep (se 1 (by rfl) ⟨2194745, by rfl⟩ : syracuseStep 2926327 = 4389491) B4389491
theorem B22226723 : Blo 1733067 22226723 := bstep (se 1 (by rfl) ⟨16670042, by rfl⟩ : syracuseStep 22226723 = 33340085) B33340085
theorem B14821163 : Blo 1733067 14821163 := bstep (se 1 (by rfl) ⟨11115872, by rfl⟩ : syracuseStep 14821163 = 22231745) B22231745
theorem B5850953 : Blo 1733067 5850953 := bstep (se 2 (by rfl) ⟨2194107, by rfl⟩ : syracuseStep 5850953 = 4388215) B4388215
theorem B1951663 : Blo 1733067 1951663 := bstep (se 1 (by rfl) ⟨1463747, by rfl⟩ : syracuseStep 1951663 = 2927495) B2927495
theorem B2926523 : Blo 1733067 2926523 := bstep (se 1 (by rfl) ⟨2194892, by rfl⟩ : syracuseStep 2926523 = 4389785) B4389785
theorem B168814529 : Blo 1733067 168814529 := bstep (se 2 (by rfl) ⟨63305448, by rfl⟩ : syracuseStep 168814529 = 126610897) B126610897
theorem B2926631 : Blo 1733067 2926631 := bstep (se 1 (by rfl) ⟨2194973, by rfl⟩ : syracuseStep 2926631 = 4389947) B4389947
theorem B5933135 : Blo 1733067 5933135 := bstep (se 1 (by rfl) ⟨4449851, by rfl⟩ : syracuseStep 5933135 = 8899703) B8899703
theorem B6252623 : Blo 1733067 6252623 := bstep (se 1 (by rfl) ⟨4689467, by rfl⟩ : syracuseStep 6252623 = 9378935) B9378935
theorem B2083015 : Blo 1733067 2083015 := bstep (se 1 (by rfl) ⟨1562261, by rfl⟩ : syracuseStep 2083015 = 3124523) B3124523
theorem B14813441 : Blo 1733067 14813441 := bstep (se 2 (by rfl) ⟨5555040, by rfl⟩ : syracuseStep 14813441 = 11110081) B11110081
theorem B31623473 : Blo 1733067 31623473 := bstep (se 2 (by rfl) ⟨11858802, by rfl⟩ : syracuseStep 31623473 = 23717605) B23717605
theorem B2926921 : Blo 1733067 2926921 := bstep (se 2 (by rfl) ⟨1097595, by rfl⟩ : syracuseStep 2926921 = 2195191) B2195191
theorem B2926955 : Blo 1733067 2926955 := bstep (se 1 (by rfl) ⟨2195216, by rfl⟩ : syracuseStep 2926955 = 4390433) B4390433
theorem B3123731 : Blo 1733067 3123731 := bstep (se 1 (by rfl) ⟨2342798, by rfl⟩ : syracuseStep 3123731 = 4685597) B4685597
theorem B3902075 : Blo 1733067 3902075 := bstep (se 1 (by rfl) ⟨2926556, by rfl⟩ : syracuseStep 3902075 = 5853113) B5853113
theorem B2599673 : Blo 1733067 2599673 := bstep (se 2 (by rfl) ⟨974877, by rfl⟩ : syracuseStep 2599673 = 1949755) B1949755
theorem B3902201 : Blo 1733067 3902201 := bstep (se 2 (by rfl) ⟨1463325, by rfl⟩ : syracuseStep 3902201 = 2926651) B2926651
theorem B2927353 : Blo 1733067 2927353 := bstep (se 2 (by rfl) ⟨1097757, by rfl⟩ : syracuseStep 2927353 = 2195515) B2195515
theorem B2599775 : Blo 1733067 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B2468713 : Blo 1733067 2468713 := bstep (se 2 (by rfl) ⟨925767, by rfl⟩ : syracuseStep 2468713 = 1851535) B1851535
theorem B2599787 : Blo 1733067 2599787 := bstep (se 1 (by rfl) ⟨1949840, by rfl⟩ : syracuseStep 2599787 = 3899681) B3899681
theorem B5852087 : Blo 1733067 5852087 := bstep (se 1 (by rfl) ⟨4389065, by rfl⟩ : syracuseStep 5852087 = 8778131) B8778131
theorem B2468827 : Blo 1733067 2468827 := bstep (se 1 (by rfl) ⟨1851620, by rfl⟩ : syracuseStep 2468827 = 3703241) B3703241
theorem B3902471 : Blo 1733067 3902471 := bstep (se 1 (by rfl) ⟨2926853, by rfl⟩ : syracuseStep 3902471 = 5853707) B5853707
theorem B2927623 : Blo 1733067 2927623 := bstep (se 1 (by rfl) ⟨2195717, by rfl⟩ : syracuseStep 2927623 = 4391435) B4391435
theorem B13167683 : Blo 1733067 13167683 := bstep (se 1 (by rfl) ⟨9875762, by rfl⟩ : syracuseStep 13167683 = 19751525) B19751525
theorem B2600015 : Blo 1733067 2600015 := bstep (se 1 (by rfl) ⟨1950011, by rfl⟩ : syracuseStep 2600015 = 3900023) B3900023
theorem B3902543 : Blo 1733067 3902543 := bstep (se 1 (by rfl) ⟨2926907, by rfl⟩ : syracuseStep 3902543 = 5853815) B5853815
theorem B14068889 : Blo 1733067 14068889 := bstep (se 2 (by rfl) ⟨5275833, by rfl⟩ : syracuseStep 14068889 = 10551667) B10551667
theorem B2600135 : Blo 1733067 2600135 := bstep (se 1 (by rfl) ⟨1950101, by rfl⟩ : syracuseStep 2600135 = 3900203) B3900203
theorem B4689143 : Blo 1733067 4689143 := bstep (se 1 (by rfl) ⟨3516857, by rfl⟩ : syracuseStep 4689143 = 7033715) B7033715
theorem B2600297 : Blo 1733067 2600297 := bstep (se 2 (by rfl) ⟨975111, by rfl⟩ : syracuseStep 2600297 = 1950223) B1950223
theorem B2600375 : Blo 1733067 2600375 := bstep (se 1 (by rfl) ⟨1950281, by rfl⟩ : syracuseStep 2600375 = 3900563) B3900563
theorem B2600411 : Blo 1733067 2600411 := bstep (se 1 (by rfl) ⟨1950308, by rfl⟩ : syracuseStep 2600411 = 3900617) B3900617
theorem B3902939 : Blo 1733067 3902939 := bstep (se 1 (by rfl) ⟨2927204, by rfl⟩ : syracuseStep 3902939 = 5854409) B5854409
theorem B5852681 : Blo 1733067 5852681 := bstep (se 2 (by rfl) ⟨2194755, by rfl⟩ : syracuseStep 5852681 = 4389511) B4389511
theorem B6672071 : Blo 1733067 6672071 := bstep (se 1 (by rfl) ⟨5004053, by rfl⟩ : syracuseStep 6672071 = 10008107) B10008107
theorem B16658243 : Blo 1733067 16658243 := bstep (se 1 (by rfl) ⟨12493682, by rfl⟩ : syracuseStep 16658243 = 24987365) B24987365
theorem B2469727 : Blo 1733067 2469727 := bstep (se 1 (by rfl) ⟨1852295, by rfl⟩ : syracuseStep 2469727 = 3704591) B3704591
theorem B2600879 : Blo 1733067 2600879 := bstep (se 1 (by rfl) ⟨1950659, by rfl⟩ : syracuseStep 2600879 = 3901319) B3901319
theorem B3903407 : Blo 1733067 3903407 := bstep (se 1 (by rfl) ⟨2927555, by rfl⟩ : syracuseStep 3903407 = 5855111) B5855111
theorem B2600969 : Blo 1733067 2600969 := bstep (se 2 (by rfl) ⟨975363, by rfl⟩ : syracuseStep 2600969 = 1950727) B1950727
theorem B13168655 : Blo 1733067 13168655 := bstep (se 1 (by rfl) ⟨9876491, by rfl⟩ : syracuseStep 13168655 = 19752983) B19752983
theorem B2600999 : Blo 1733067 2600999 := bstep (se 1 (by rfl) ⟨1950749, by rfl⟩ : syracuseStep 2600999 = 3901499) B3901499
theorem B2601083 : Blo 1733067 2601083 := bstep (se 1 (by rfl) ⟨1950812, by rfl⟩ : syracuseStep 2601083 = 3901625) B3901625
theorem B3903659 : Blo 1733067 3903659 := bstep (se 1 (by rfl) ⟨2927744, by rfl⟩ : syracuseStep 3903659 = 5855489) B5855489
theorem B2601209 : Blo 1733067 2601209 := bstep (se 2 (by rfl) ⟨975453, by rfl⟩ : syracuseStep 2601209 = 1950907) B1950907
theorem B14807357 : Blo 1733067 14807357 := bstep (se 3 (by rfl) ⟨2776379, by rfl⟩ : syracuseStep 14807357 = 5552759) B5552759
theorem B2601311 : Blo 1733067 2601311 := bstep (se 1 (by rfl) ⟨1950983, by rfl⟩ : syracuseStep 2601311 = 3901967) B3901967
theorem B5853545 : Blo 1733067 5853545 := bstep (se 2 (by rfl) ⟨2195079, by rfl⟩ : syracuseStep 5853545 = 4390159) B4390159
theorem B2601323 : Blo 1733067 2601323 := bstep (se 1 (by rfl) ⟨1950992, by rfl⟩ : syracuseStep 2601323 = 3901985) B3901985
theorem B1733083 : Blo 1733067 1733083 := bstep (se 1 (by rfl) ⟨1299812, by rfl⟩ : syracuseStep 1733083 = 2599625) B2599625
theorem B3953161 : Blo 1733067 3953161 := bstep (se 2 (by rfl) ⟨1482435, by rfl⟩ : syracuseStep 3953161 = 2964871) B2964871
theorem B6582809 : Blo 1733067 6582809 := bstep (se 2 (by rfl) ⟨2468553, by rfl⟩ : syracuseStep 6582809 = 4937107) B4937107
theorem B1733159 : Blo 1733067 1733159 := bstep (se 1 (by rfl) ⟨1299869, by rfl⟩ : syracuseStep 1733159 = 2599739) B2599739
theorem B5935655 : Blo 1733067 5935655 := bstep (se 1 (by rfl) ⟨4451741, by rfl⟩ : syracuseStep 5935655 = 8903483) B8903483
theorem B2470439 : Blo 1733067 2470439 := bstep (se 1 (by rfl) ⟨1852829, by rfl⟩ : syracuseStep 2470439 = 3705659) B3705659
theorem B1733199 : Blo 1733067 1733199 := bstep (se 1 (by rfl) ⟨1299899, by rfl⟩ : syracuseStep 1733199 = 2599799) B2599799
theorem B2601551 : Blo 1733067 2601551 := bstep (se 1 (by rfl) ⟨1951163, by rfl⟩ : syracuseStep 2601551 = 3902327) B3902327
theorem B1733215 : Blo 1733067 1733215 := bstep (se 1 (by rfl) ⟨1299911, by rfl⟩ : syracuseStep 1733215 = 2599823) B2599823
theorem B1733243 : Blo 1733067 1733243 := bstep (se 1 (by rfl) ⟨1299932, by rfl⟩ : syracuseStep 1733243 = 2599865) B2599865
theorem B1733295 : Blo 1733067 1733295 := bstep (se 1 (by rfl) ⟨1299971, by rfl⟩ : syracuseStep 1733295 = 2599943) B2599943
theorem B1733319 : Blo 1733067 1733319 := bstep (se 1 (by rfl) ⟨1299989, by rfl⟩ : syracuseStep 1733319 = 2599979) B2599979
theorem B2601671 : Blo 1733067 2601671 := bstep (se 1 (by rfl) ⟨1951253, by rfl⟩ : syracuseStep 2601671 = 3902507) B3902507
theorem B7033553 : Blo 1733067 7033553 := bstep (se 2 (by rfl) ⟨2637582, by rfl⟩ : syracuseStep 7033553 = 5275165) B5275165
theorem B1733339 : Blo 1733067 1733339 := bstep (se 1 (by rfl) ⟨1300004, by rfl⟩ : syracuseStep 1733339 = 2600009) B2600009
theorem B71201551 : Blo 1733067 71201551 := bstep (se 1 (by rfl) ⟨53401163, by rfl⟩ : syracuseStep 71201551 = 106802327) B106802327
theorem B1733415 : Blo 1733067 1733415 := bstep (se 1 (by rfl) ⟨1300061, by rfl⟩ : syracuseStep 1733415 = 2600123) B2600123
theorem B10285897 : Blo 1733067 10285897 := bstep (se 2 (by rfl) ⟨3857211, by rfl⟩ : syracuseStep 10285897 = 7714423) B7714423
theorem B1733455 : Blo 1733067 1733455 := bstep (se 1 (by rfl) ⟨1300091, by rfl⟩ : syracuseStep 1733455 = 2600183) B2600183
theorem B4387679 : Blo 1733067 4387679 := bstep (se 1 (by rfl) ⟨3290759, by rfl⟩ : syracuseStep 4387679 = 6581519) B6581519
theorem B1733471 : Blo 1733067 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B2601833 : Blo 1733067 2601833 := bstep (se 2 (by rfl) ⟨975687, by rfl⟩ : syracuseStep 2601833 = 1951375) B1951375
theorem B1733499 : Blo 1733067 1733499 := bstep (se 1 (by rfl) ⟨1300124, by rfl⟩ : syracuseStep 1733499 = 2600249) B2600249
theorem B1733551 : Blo 1733067 1733551 := bstep (se 1 (by rfl) ⟨1300163, by rfl⟩ : syracuseStep 1733551 = 2600327) B2600327
theorem B2601911 : Blo 1733067 2601911 := bstep (se 1 (by rfl) ⟨1951433, by rfl⟩ : syracuseStep 2601911 = 3902867) B3902867
theorem B5346235 : Blo 1733067 5346235 := bstep (se 1 (by rfl) ⟨4009676, by rfl⟩ : syracuseStep 5346235 = 8019353) B8019353
theorem B5854139 : Blo 1733067 5854139 := bstep (se 1 (by rfl) ⟨4390604, by rfl⟩ : syracuseStep 5854139 = 8781209) B8781209
theorem B1733575 : Blo 1733067 1733575 := bstep (se 1 (by rfl) ⟨1300181, by rfl⟩ : syracuseStep 1733575 = 2600363) B2600363
theorem B1733595 : Blo 1733067 1733595 := bstep (se 1 (by rfl) ⟨1300196, by rfl⟩ : syracuseStep 1733595 = 2600393) B2600393
theorem B2601947 : Blo 1733067 2601947 := bstep (se 1 (by rfl) ⟨1951460, by rfl⟩ : syracuseStep 2601947 = 3902921) B3902921
theorem B12497921 : Blo 1733067 12497921 := bstep (se 2 (by rfl) ⟨4686720, by rfl⟩ : syracuseStep 12497921 = 9373441) B9373441
theorem B1733671 : Blo 1733067 1733671 := bstep (se 1 (by rfl) ⟨1300253, by rfl⟩ : syracuseStep 1733671 = 2600507) B2600507
theorem B1733711 : Blo 1733067 1733711 := bstep (se 1 (by rfl) ⟨1300283, by rfl⟩ : syracuseStep 1733711 = 2600567) B2600567
theorem B1733727 : Blo 1733067 1733727 := bstep (se 1 (by rfl) ⟨1300295, by rfl⟩ : syracuseStep 1733727 = 2600591) B2600591
theorem B1733755 : Blo 1733067 1733755 := bstep (se 1 (by rfl) ⟨1300316, by rfl⟩ : syracuseStep 1733755 = 2600633) B2600633
theorem B1733807 : Blo 1733067 1733807 := bstep (se 1 (by rfl) ⟨1300355, by rfl⟩ : syracuseStep 1733807 = 2600711) B2600711
theorem B3290311 : Blo 1733067 3290311 := bstep (se 1 (by rfl) ⟨2467733, by rfl⟩ : syracuseStep 3290311 = 4935467) B4935467
theorem B1733831 : Blo 1733067 1733831 := bstep (se 1 (by rfl) ⟨1300373, by rfl⟩ : syracuseStep 1733831 = 2600747) B2600747
theorem B1733851 : Blo 1733067 1733851 := bstep (se 1 (by rfl) ⟨1300388, by rfl⟩ : syracuseStep 1733851 = 2600777) B2600777
theorem B28112143 : Blo 1733067 28112143 := bstep (se 1 (by rfl) ⟨21084107, by rfl⟩ : syracuseStep 28112143 = 42168215) B42168215
theorem B1733927 : Blo 1733067 1733927 := bstep (se 1 (by rfl) ⟨1300445, by rfl⟩ : syracuseStep 1733927 = 2600891) B2600891
theorem B1733967 : Blo 1733067 1733967 := bstep (se 1 (by rfl) ⟨1300475, by rfl⟩ : syracuseStep 1733967 = 2600951) B2600951
theorem B1733983 : Blo 1733067 1733983 := bstep (se 1 (by rfl) ⟨1300487, by rfl⟩ : syracuseStep 1733983 = 2600975) B2600975
theorem B1734011 : Blo 1733067 1734011 := bstep (se 1 (by rfl) ⟨1300508, by rfl⟩ : syracuseStep 1734011 = 2601017) B2601017
theorem B5633405 : Blo 1733067 5633405 := bstep (se 3 (by rfl) ⟨1056263, by rfl⟩ : syracuseStep 5633405 = 2112527) B2112527
theorem B1734063 : Blo 1733067 1734063 := bstep (se 1 (by rfl) ⟨1300547, by rfl⟩ : syracuseStep 1734063 = 2601095) B2601095
theorem B2602415 : Blo 1733067 2602415 := bstep (se 1 (by rfl) ⟨1951811, by rfl⟩ : syracuseStep 2602415 = 3903623) B3903623
theorem B1734087 : Blo 1733067 1734087 := bstep (se 1 (by rfl) ⟨1300565, by rfl⟩ : syracuseStep 1734087 = 2601131) B2601131
theorem B12694985 : Blo 1733067 12694985 := bstep (se 2 (by rfl) ⟨4760619, by rfl⟩ : syracuseStep 12694985 = 9521239) B9521239
theorem B1734107 : Blo 1733067 1734107 := bstep (se 1 (by rfl) ⟨1300580, by rfl⟩ : syracuseStep 1734107 = 2601161) B2601161
theorem B2602505 : Blo 1733067 2602505 := bstep (se 2 (by rfl) ⟨975939, by rfl⟩ : syracuseStep 2602505 = 1951879) B1951879
theorem B4388377 : Blo 1733067 4388377 := bstep (se 2 (by rfl) ⟨1645641, by rfl⟩ : syracuseStep 4388377 = 3291283) B3291283
theorem B1734183 : Blo 1733067 1734183 := bstep (se 1 (by rfl) ⟨1300637, by rfl⟩ : syracuseStep 1734183 = 2601275) B2601275
theorem B2602535 : Blo 1733067 2602535 := bstep (se 1 (by rfl) ⟨1951901, by rfl⟩ : syracuseStep 2602535 = 3903803) B3903803
theorem B1734223 : Blo 1733067 1734223 := bstep (se 1 (by rfl) ⟨1300667, by rfl⟩ : syracuseStep 1734223 = 2601335) B2601335
theorem B1734239 : Blo 1733067 1734239 := bstep (se 1 (by rfl) ⟨1300679, by rfl⟩ : syracuseStep 1734239 = 2601359) B2601359
theorem B1734267 : Blo 1733067 1734267 := bstep (se 1 (by rfl) ⟨1300700, by rfl⟩ : syracuseStep 1734267 = 2601401) B2601401
theorem B1734319 : Blo 1733067 1734319 := bstep (se 1 (by rfl) ⟨1300739, by rfl⟩ : syracuseStep 1734319 = 2601479) B2601479
theorem B11105981 : Blo 1733067 11105981 := bstep (se 3 (by rfl) ⟨2082371, by rfl⟩ : syracuseStep 11105981 = 4164743) B4164743
theorem B1734343 : Blo 1733067 1734343 := bstep (se 1 (by rfl) ⟨1300757, by rfl⟩ : syracuseStep 1734343 = 2601515) B2601515
theorem B1734363 : Blo 1733067 1734363 := bstep (se 1 (by rfl) ⟨1300772, by rfl⟩ : syracuseStep 1734363 = 2601545) B2601545
theorem B10540793 : Blo 1733067 10540793 := bstep (se 2 (by rfl) ⟨3952797, by rfl⟩ : syracuseStep 10540793 = 7905595) B7905595
theorem B1734439 : Blo 1733067 1734439 := bstep (se 1 (by rfl) ⟨1300829, by rfl⟩ : syracuseStep 1734439 = 2601659) B2601659
theorem B4388681 : Blo 1733067 4388681 := bstep (se 2 (by rfl) ⟨1645755, by rfl⟩ : syracuseStep 4388681 = 3291511) B3291511
theorem B1734479 : Blo 1733067 1734479 := bstep (se 1 (by rfl) ⟨1300859, by rfl⟩ : syracuseStep 1734479 = 2601719) B2601719
theorem B1734495 : Blo 1733067 1734495 := bstep (se 1 (by rfl) ⟨1300871, by rfl⟩ : syracuseStep 1734495 = 2601743) B2601743
theorem B3954539 : Blo 1733067 3954539 := bstep (se 1 (by rfl) ⟨2965904, by rfl⟩ : syracuseStep 3954539 = 5931809) B5931809
theorem B1734523 : Blo 1733067 1734523 := bstep (se 1 (by rfl) ⟨1300892, by rfl⟩ : syracuseStep 1734523 = 2601785) B2601785
theorem B1734575 : Blo 1733067 1734575 := bstep (se 1 (by rfl) ⟨1300931, by rfl⟩ : syracuseStep 1734575 = 2601863) B2601863
theorem B1734599 : Blo 1733067 1734599 := bstep (se 1 (by rfl) ⟨1300949, by rfl⟩ : syracuseStep 1734599 = 2601899) B2601899
theorem B18749393 : Blo 1733067 18749393 := bstep (se 2 (by rfl) ⟨7031022, by rfl⟩ : syracuseStep 18749393 = 14062045) B14062045
theorem B1734619 : Blo 1733067 1734619 := bstep (se 1 (by rfl) ⟨1300964, by rfl⟩ : syracuseStep 1734619 = 2601929) B2601929
theorem B1734695 : Blo 1733067 1734695 := bstep (se 1 (by rfl) ⟨1301021, by rfl⟩ : syracuseStep 1734695 = 2602043) B2602043
theorem B1734735 : Blo 1733067 1734735 := bstep (se 1 (by rfl) ⟨1301051, by rfl⟩ : syracuseStep 1734735 = 2602103) B2602103
theorem B9877585 : Blo 1733067 9877585 := bstep (se 2 (by rfl) ⟨3704094, by rfl⟩ : syracuseStep 9877585 = 7408189) B7408189
theorem B1734751 : Blo 1733067 1734751 := bstep (se 1 (by rfl) ⟨1301063, by rfl⟩ : syracuseStep 1734751 = 2602127) B2602127
theorem B6584435 : Blo 1733067 6584435 := bstep (se 1 (by rfl) ⟨4938326, by rfl⟩ : syracuseStep 6584435 = 9876653) B9876653
theorem B1734779 : Blo 1733067 1734779 := bstep (se 1 (by rfl) ⟨1301084, by rfl⟩ : syracuseStep 1734779 = 2602169) B2602169
theorem B1734831 : Blo 1733067 1734831 := bstep (se 1 (by rfl) ⟨1301123, by rfl⟩ : syracuseStep 1734831 = 2602247) B2602247
theorem B1734855 : Blo 1733067 1734855 := bstep (se 1 (by rfl) ⟨1301141, by rfl⟩ : syracuseStep 1734855 = 2602283) B2602283
theorem B1734875 : Blo 1733067 1734875 := bstep (se 1 (by rfl) ⟨1301156, by rfl⟩ : syracuseStep 1734875 = 2602313) B2602313
theorem B1734951 : Blo 1733067 1734951 := bstep (se 1 (by rfl) ⟨1301213, by rfl⟩ : syracuseStep 1734951 = 2602427) B2602427
theorem B1734991 : Blo 1733067 1734991 := bstep (se 1 (by rfl) ⟨1301243, by rfl⟩ : syracuseStep 1734991 = 2602487) B2602487
theorem B1735007 : Blo 1733067 1735007 := bstep (se 1 (by rfl) ⟨1301255, by rfl⟩ : syracuseStep 1735007 = 2602511) B2602511
theorem B1735035 : Blo 1733067 1735035 := bstep (se 1 (by rfl) ⟨1301276, by rfl⟩ : syracuseStep 1735035 = 2602553) B2602553
theorem B25008587 : Blo 1733067 25008587 := bstep (se 1 (by rfl) ⟨18756440, by rfl⟩ : syracuseStep 25008587 = 37512881) B37512881
theorem B7027181 : Blo 1733067 7027181 := bstep (se 3 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 7027181 = 2635193) B2635193
theorem B53377517 : Blo 1733067 53377517 := bstep (se 3 (by rfl) ⟨10008284, by rfl⟩ : syracuseStep 53377517 = 20016569) B20016569
theorem B4938337 : Blo 1733067 4938337 := bstep (se 2 (by rfl) ⟨1851876, by rfl⟩ : syracuseStep 4938337 = 3703753) B3703753
theorem B19741319 : Blo 1733067 19741319 := bstep (se 1 (by rfl) ⟨14805989, by rfl⟩ : syracuseStep 19741319 = 29611979) B29611979
theorem B14064313 : Blo 1733067 14064313 := bstep (se 2 (by rfl) ⟨5274117, by rfl⟩ : syracuseStep 14064313 = 10548235) B10548235
theorem B3701447 : Blo 1733067 3701447 := bstep (se 1 (by rfl) ⟨2776085, by rfl⟩ : syracuseStep 3701447 = 5552171) B5552171
theorem B4389815 : Blo 1733067 4389815 := bstep (se 1 (by rfl) ⟨3292361, by rfl⟩ : syracuseStep 4389815 = 6584723) B6584723
theorem B3513467 : Blo 1733067 3513467 := bstep (se 1 (by rfl) ⟨2635100, by rfl⟩ : syracuseStep 3513467 = 5270201) B5270201
theorem B8781047 : Blo 1733067 8781047 := bstep (se 1 (by rfl) ⟨6585785, by rfl⟩ : syracuseStep 8781047 = 13171571) B13171571
theorem B2776393 : Blo 1733067 2776393 := bstep (se 2 (by rfl) ⟨1041147, by rfl⟩ : syracuseStep 2776393 = 2082295) B2082295
theorem B13172057 : Blo 1733067 13172057 := bstep (se 2 (by rfl) ⟨4939521, by rfl⟩ : syracuseStep 13172057 = 9879043) B9879043
theorem B6585725 : Blo 1733067 6585725 := bstep (se 3 (by rfl) ⟨1234823, by rfl⟩ : syracuseStep 6585725 = 2469647) B2469647
theorem B3292559 : Blo 1733067 3292559 := bstep (se 1 (by rfl) ⟨2469419, by rfl⟩ : syracuseStep 3292559 = 4938839) B4938839
theorem B16661933 : Blo 1733067 16661933 := bstep (se 3 (by rfl) ⟨3124112, by rfl⟩ : syracuseStep 16661933 = 6248225) B6248225
theorem B2776585 : Blo 1733067 2776585 := bstep (se 2 (by rfl) ⟨1041219, by rfl⟩ : syracuseStep 2776585 = 2082439) B2082439
theorem B9379451 : Blo 1733067 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B11107979 : Blo 1733067 11107979 := bstep (se 1 (by rfl) ⟨8330984, by rfl⟩ : syracuseStep 11107979 = 16661969) B16661969
theorem B8781533 : Blo 1733067 8781533 := bstep (se 3 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 8781533 = 3293075) B3293075
theorem B13164281 : Blo 1733067 13164281 := bstep (se 2 (by rfl) ⟨4936605, by rfl⟩ : syracuseStep 13164281 = 9873211) B9873211
theorem B12836717 : Blo 1733067 12836717 := bstep (se 3 (by rfl) ⟨2406884, by rfl⟩ : syracuseStep 12836717 = 4813769) B4813769
theorem B5783471 : Blo 1733067 5783471 := bstep (se 1 (by rfl) ⟨4337603, by rfl⟩ : syracuseStep 5783471 = 8675207) B8675207
theorem B2195419 : Blo 1733067 2195419 := bstep (se 1 (by rfl) ⟨1646564, by rfl⟩ : syracuseStep 2195419 = 3293129) B3293129
theorem B7405577 : Blo 1733067 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B6586393 : Blo 1733067 6586393 := bstep (se 2 (by rfl) ⟨2469897, by rfl⟩ : syracuseStep 6586393 = 4939795) B4939795
theorem B7503931 : Blo 1733067 7503931 := bstep (se 1 (by rfl) ⟨5627948, by rfl⟩ : syracuseStep 7503931 = 11255897) B11255897
theorem B7405627 : Blo 1733067 7405627 := bstep (se 1 (by rfl) ⟨5554220, by rfl⟩ : syracuseStep 7405627 = 11108441) B11108441
theorem B9871571 : Blo 1733067 9871571 := bstep (se 1 (by rfl) ⟨7403678, by rfl⟩ : syracuseStep 9871571 = 14807357) B14807357
theorem B2195743 : Blo 1733067 2195743 := bstep (se 1 (by rfl) ⟨1646807, by rfl⟩ : syracuseStep 2195743 = 3293615) B3293615
theorem B6586697 : Blo 1733067 6586697 := bstep (se 2 (by rfl) ⟨2470011, by rfl⟩ : syracuseStep 6586697 = 4940023) B4940023
theorem B1950043 : Blo 1733067 1950043 := bstep (se 1 (by rfl) ⟨1462532, by rfl⟩ : syracuseStep 1950043 = 2925065) B2925065
theorem B3293531 : Blo 1733067 3293531 := bstep (se 1 (by rfl) ⟨2470148, by rfl⟩ : syracuseStep 3293531 = 4940297) B4940297
theorem B3957103 : Blo 1733067 3957103 := bstep (se 1 (by rfl) ⟨2967827, by rfl⟩ : syracuseStep 3957103 = 5935655) B5935655
theorem B1950151 : Blo 1733067 1950151 := bstep (se 1 (by rfl) ⟨1462613, by rfl⟩ : syracuseStep 1950151 = 2925227) B2925227
theorem B2925119 : Blo 1733067 2925119 := bstep (se 1 (by rfl) ⟨2193839, by rfl⟩ : syracuseStep 2925119 = 4387679) B4387679
theorem B3293759 : Blo 1733067 3293759 := bstep (se 1 (by rfl) ⟨2470319, by rfl⟩ : syracuseStep 3293759 = 4940639) B4940639
theorem B8331947 : Blo 1733067 8331947 := bstep (se 1 (by rfl) ⟨6248960, by rfl⟩ : syracuseStep 8331947 = 12497921) B12497921
theorem B1950511 : Blo 1733067 1950511 := bstep (se 1 (by rfl) ⟨1462883, by rfl⟩ : syracuseStep 1950511 = 2925767) B2925767
theorem B3900239 : Blo 1733067 3900239 := bstep (se 1 (by rfl) ⟨2925179, by rfl⟩ : syracuseStep 3900239 = 5850359) B5850359
theorem B4391759 : Blo 1733067 4391759 := bstep (se 1 (by rfl) ⟨3293819, by rfl⟩ : syracuseStep 4391759 = 6587639) B6587639
theorem B1950619 : Blo 1733067 1950619 := bstep (se 1 (by rfl) ⟨1462964, by rfl⟩ : syracuseStep 1950619 = 2925929) B2925929
theorem B18752417 : Blo 1733067 18752417 := bstep (se 2 (by rfl) ⟨7032156, by rfl⟩ : syracuseStep 18752417 = 14064313) B14064313
theorem B8463323 : Blo 1733067 8463323 := bstep (se 1 (by rfl) ⟨6347492, by rfl⟩ : syracuseStep 8463323 = 12694985) B12694985
theorem B6964199 : Blo 1733067 6964199 := bstep (se 1 (by rfl) ⟨5223149, by rfl⟩ : syracuseStep 6964199 = 10446299) B10446299
theorem B2343911 : Blo 1733067 2343911 := bstep (se 1 (by rfl) ⟨1757933, by rfl⟩ : syracuseStep 2343911 = 3515867) B3515867
theorem B11109413 : Blo 1733067 11109413 := bstep (se 4 (by rfl) ⟨1041507, by rfl⟩ : syracuseStep 11109413 = 2083015) B2083015
theorem B3900455 : Blo 1733067 3900455 := bstep (se 1 (by rfl) ⟨2925341, by rfl⟩ : syracuseStep 3900455 = 5850683) B5850683
theorem B13714529 : Blo 1733067 13714529 := bstep (se 2 (by rfl) ⟨5142948, by rfl⟩ : syracuseStep 13714529 = 10285897) B10285897
theorem B8782991 : Blo 1733067 8782991 := bstep (se 1 (by rfl) ⟨6587243, by rfl⟩ : syracuseStep 8782991 = 13174487) B13174487
theorem B9880775 : Blo 1733067 9880775 := bstep (se 1 (by rfl) ⟨7410581, by rfl⟩ : syracuseStep 9880775 = 14821163) B14821163
theorem B3900635 : Blo 1733067 3900635 := bstep (se 1 (by rfl) ⟨2925476, by rfl⟩ : syracuseStep 3900635 = 5850953) B5850953
theorem B2925787 : Blo 1733067 2925787 := bstep (se 1 (by rfl) ⟨2194340, by rfl⟩ : syracuseStep 2925787 = 4388681) B4388681
theorem B7128313 : Blo 1733067 7128313 := bstep (se 2 (by rfl) ⟨2673117, by rfl⟩ : syracuseStep 7128313 = 5346235) B5346235
theorem B1951015 : Blo 1733067 1951015 := bstep (se 1 (by rfl) ⟨1463261, by rfl⟩ : syracuseStep 1951015 = 2926523) B2926523
theorem B112543019 : Blo 1733067 112543019 := bstep (se 1 (by rfl) ⟨84407264, by rfl⟩ : syracuseStep 112543019 = 168814529) B168814529
theorem B1951087 : Blo 1733067 1951087 := bstep (se 1 (by rfl) ⟨1463315, by rfl⟩ : syracuseStep 1951087 = 2926631) B2926631
theorem B3900833 : Blo 1733067 3900833 := bstep (se 2 (by rfl) ⟨1462812, by rfl⟩ : syracuseStep 3900833 = 2925625) B2925625
theorem B6587837 : Blo 1733067 6587837 := bstep (se 3 (by rfl) ⟨1235219, by rfl⟩ : syracuseStep 6587837 = 2470439) B2470439
theorem B1951303 : Blo 1733067 1951303 := bstep (se 1 (by rfl) ⟨1463477, by rfl⟩ : syracuseStep 1951303 = 2926955) B2926955
theorem B16672391 : Blo 1733067 16672391 := bstep (se 1 (by rfl) ⟨12504293, by rfl⟩ : syracuseStep 16672391 = 25008587) B25008587
theorem B2467631 : Blo 1733067 2467631 := bstep (se 1 (by rfl) ⟨1850723, by rfl⟩ : syracuseStep 2467631 = 3701447) B3701447
theorem B3901391 : Blo 1733067 3901391 := bstep (se 1 (by rfl) ⟨2926043, by rfl⟩ : syracuseStep 3901391 = 5852087) B5852087
theorem B2926543 : Blo 1733067 2926543 := bstep (se 1 (by rfl) ⟨2194907, by rfl⟩ : syracuseStep 2926543 = 4389815) B4389815
theorem B5851169 : Blo 1733067 5851169 := bstep (se 2 (by rfl) ⟨2194188, by rfl⟩ : syracuseStep 5851169 = 4388377) B4388377
theorem B9373961 : Blo 1733067 9373961 := bstep (se 2 (by rfl) ⟨3515235, by rfl⟩ : syracuseStep 9373961 = 7030471) B7030471
theorem B10545437 : Blo 1733067 10545437 := bstep (se 3 (by rfl) ⟨1977269, by rfl⟩ : syracuseStep 10545437 = 3954539) B3954539
theorem B3901769 : Blo 1733067 3901769 := bstep (se 2 (by rfl) ⟨1463163, by rfl⟩ : syracuseStep 3901769 = 2926327) B2926327
theorem B3901787 : Blo 1733067 3901787 := bstep (se 1 (by rfl) ⟨2926340, by rfl⟩ : syracuseStep 3901787 = 5852681) B5852681
theorem B6252967 : Blo 1733067 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B8776187 : Blo 1733067 8776187 := bstep (se 1 (by rfl) ⟨6582140, by rfl⟩ : syracuseStep 8776187 = 13164281) B13164281
theorem B2927225 : Blo 1733067 2927225 := bstep (se 2 (by rfl) ⟨1097709, by rfl⟩ : syracuseStep 2927225 = 2195419) B2195419
theorem B2927279 : Blo 1733067 2927279 := bstep (se 1 (by rfl) ⟨2195459, by rfl⟩ : syracuseStep 2927279 = 4390919) B4390919
theorem B2599607 : Blo 1733067 2599607 := bstep (se 1 (by rfl) ⟨1949705, by rfl⟩ : syracuseStep 2599607 = 3899411) B3899411
theorem B15821693 : Blo 1733067 15821693 := bstep (se 3 (by rfl) ⟨2966567, by rfl⟩ : syracuseStep 15821693 = 5933135) B5933135
theorem B2599835 : Blo 1733067 2599835 := bstep (se 1 (by rfl) ⟨1949876, by rfl⟩ : syracuseStep 2599835 = 3899753) B3899753
theorem B3902363 : Blo 1733067 3902363 := bstep (se 1 (by rfl) ⟨2926772, by rfl⟩ : syracuseStep 3902363 = 5853545) B5853545
theorem B2927515 : Blo 1733067 2927515 := bstep (se 1 (by rfl) ⟨2195636, by rfl⟩ : syracuseStep 2927515 = 4391273) B4391273
theorem B3902561 : Blo 1733067 3902561 := bstep (se 2 (by rfl) ⟨1463460, by rfl⟩ : syracuseStep 3902561 = 2926921) B2926921
theorem B4689035 : Blo 1733067 4689035 := bstep (se 1 (by rfl) ⟨3516776, by rfl⟩ : syracuseStep 4689035 = 7033553) B7033553
theorem B2600231 : Blo 1733067 2600231 := bstep (se 1 (by rfl) ⟨1950173, by rfl⟩ : syracuseStep 2600231 = 3900347) B3900347
theorem B3902759 : Blo 1733067 3902759 := bstep (se 1 (by rfl) ⟨2927069, by rfl⟩ : syracuseStep 3902759 = 5854139) B5854139
theorem B5270881 : Blo 1733067 5270881 := bstep (se 2 (by rfl) ⟨1976580, by rfl⟩ : syracuseStep 5270881 = 3953161) B3953161
theorem B16035191 : Blo 1733067 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B2600315 : Blo 1733067 2600315 := bstep (se 1 (by rfl) ⟨1950236, by rfl⟩ : syracuseStep 2600315 = 3900473) B3900473
theorem B8777159 : Blo 1733067 8777159 := bstep (se 1 (by rfl) ⟨6582869, by rfl⟩ : syracuseStep 8777159 = 13165739) B13165739
theorem B10546631 : Blo 1733067 10546631 := bstep (se 1 (by rfl) ⟨7909973, by rfl⟩ : syracuseStep 10546631 = 15819947) B15819947
theorem B2600441 : Blo 1733067 2600441 := bstep (se 2 (by rfl) ⟨975165, by rfl⟩ : syracuseStep 2600441 = 1950331) B1950331
theorem B3755603 : Blo 1733067 3755603 := bstep (se 1 (by rfl) ⟨2816702, by rfl⟩ : syracuseStep 3755603 = 5633405) B5633405
theorem B2600543 : Blo 1733067 2600543 := bstep (se 1 (by rfl) ⟨1950407, by rfl⟩ : syracuseStep 2600543 = 3900815) B3900815
theorem B3903137 : Blo 1733067 3903137 := bstep (se 2 (by rfl) ⟨1463676, by rfl⟩ : syracuseStep 3903137 = 2927353) B2927353
theorem B8777483 : Blo 1733067 8777483 := bstep (se 1 (by rfl) ⟨6583112, by rfl⟩ : syracuseStep 8777483 = 13166225) B13166225
theorem B2600759 : Blo 1733067 2600759 := bstep (se 1 (by rfl) ⟨1950569, by rfl⟩ : syracuseStep 2600759 = 3901139) B3901139
theorem B3903497 : Blo 1733067 3903497 := bstep (se 2 (by rfl) ⟨1463811, by rfl⟩ : syracuseStep 3903497 = 2927623) B2927623
theorem B2601065 : Blo 1733067 2601065 := bstep (se 2 (by rfl) ⟨975399, by rfl⟩ : syracuseStep 2601065 = 1950799) B1950799
theorem B9875627 : Blo 1733067 9875627 := bstep (se 1 (by rfl) ⟨7406720, by rfl⟩ : syracuseStep 9875627 = 14813441) B14813441
theorem B21082315 : Blo 1733067 21082315 := bstep (se 1 (by rfl) ⟨15811736, by rfl⟩ : syracuseStep 21082315 = 31623473) B31623473
theorem B4387081 : Blo 1733067 4387081 := bstep (se 2 (by rfl) ⟨1645155, by rfl⟩ : syracuseStep 4387081 = 3290311) B3290311
theorem B37482857 : Blo 1733067 37482857 := bstep (se 2 (by rfl) ⟨14056071, by rfl⟩ : syracuseStep 37482857 = 28112143) B28112143
theorem B2601383 : Blo 1733067 2601383 := bstep (se 1 (by rfl) ⟨1951037, by rfl⟩ : syracuseStep 2601383 = 3902075) B3902075
theorem B13160879 : Blo 1733067 13160879 := bstep (se 1 (by rfl) ⟨9870659, by rfl⟩ : syracuseStep 13160879 = 19741319) B19741319
theorem B1733115 : Blo 1733067 1733115 := bstep (se 1 (by rfl) ⟨1299836, by rfl⟩ : syracuseStep 1733115 = 2599673) B2599673
theorem B2601467 : Blo 1733067 2601467 := bstep (se 1 (by rfl) ⟨1951100, by rfl⟩ : syracuseStep 2601467 = 3902201) B3902201
theorem B1733183 : Blo 1733067 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B1733191 : Blo 1733067 1733191 := bstep (se 1 (by rfl) ⟨1299893, by rfl⟩ : syracuseStep 1733191 = 2599787) B2599787
theorem B2601593 : Blo 1733067 2601593 := bstep (se 2 (by rfl) ⟨975597, by rfl⟩ : syracuseStep 2601593 = 1951195) B1951195
theorem B2601647 : Blo 1733067 2601647 := bstep (se 1 (by rfl) ⟨1951235, by rfl⟩ : syracuseStep 2601647 = 3902471) B3902471
theorem B8778455 : Blo 1733067 8778455 := bstep (se 1 (by rfl) ⟨6583841, by rfl⟩ : syracuseStep 8778455 = 13167683) B13167683
theorem B1733343 : Blo 1733067 1733343 := bstep (se 1 (by rfl) ⟨1300007, by rfl⟩ : syracuseStep 1733343 = 2600015) B2600015
theorem B2601695 : Blo 1733067 2601695 := bstep (se 1 (by rfl) ⟨1951271, by rfl⟩ : syracuseStep 2601695 = 3902543) B3902543
theorem B1733423 : Blo 1733067 1733423 := bstep (se 1 (by rfl) ⟨1300067, by rfl⟩ : syracuseStep 1733423 = 2600135) B2600135
theorem B5854031 : Blo 1733067 5854031 := bstep (se 1 (by rfl) ⟨4390523, by rfl⟩ : syracuseStep 5854031 = 8781047) B8781047
theorem B3126095 : Blo 1733067 3126095 := bstep (se 1 (by rfl) ⟨2344571, by rfl⟩ : syracuseStep 3126095 = 4689143) B4689143
theorem B1733531 : Blo 1733067 1733531 := bstep (se 1 (by rfl) ⟨1300148, by rfl⟩ : syracuseStep 1733531 = 2600297) B2600297
theorem B1733583 : Blo 1733067 1733583 := bstep (se 1 (by rfl) ⟨1300187, by rfl⟩ : syracuseStep 1733583 = 2600375) B2600375
theorem B1733607 : Blo 1733067 1733607 := bstep (se 1 (by rfl) ⟨1300205, by rfl⟩ : syracuseStep 1733607 = 2600411) B2600411
theorem B2601959 : Blo 1733067 2601959 := bstep (se 1 (by rfl) ⟨1951469, by rfl⟩ : syracuseStep 2601959 = 3902939) B3902939
theorem B5854355 : Blo 1733067 5854355 := bstep (se 1 (by rfl) ⟨4390766, by rfl⟩ : syracuseStep 5854355 = 8781533) B8781533
theorem B11105495 : Blo 1733067 11105495 := bstep (se 1 (by rfl) ⟨8329121, by rfl⟩ : syracuseStep 11105495 = 16658243) B16658243
theorem B2602217 : Blo 1733067 2602217 := bstep (se 2 (by rfl) ⟨975831, by rfl⟩ : syracuseStep 2602217 = 1951663) B1951663
theorem B8557811 : Blo 1733067 8557811 := bstep (se 1 (by rfl) ⟨6418358, by rfl⟩ : syracuseStep 8557811 = 12836717) B12836717
theorem B3855647 : Blo 1733067 3855647 := bstep (se 1 (by rfl) ⟨2891735, by rfl⟩ : syracuseStep 3855647 = 5783471) B5783471
theorem B1733919 : Blo 1733067 1733919 := bstep (se 1 (by rfl) ⟨1300439, by rfl⟩ : syracuseStep 1733919 = 2600879) B2600879
theorem B2602271 : Blo 1733067 2602271 := bstep (se 1 (by rfl) ⟨1951703, by rfl⟩ : syracuseStep 2602271 = 3903407) B3903407
theorem B1733979 : Blo 1733067 1733979 := bstep (se 1 (by rfl) ⟨1300484, by rfl⟩ : syracuseStep 1733979 = 2600969) B2600969
theorem B8779103 : Blo 1733067 8779103 := bstep (se 1 (by rfl) ⟨6584327, by rfl⟩ : syracuseStep 8779103 = 13168655) B13168655
theorem B1733999 : Blo 1733067 1733999 := bstep (se 1 (by rfl) ⟨1300499, by rfl⟩ : syracuseStep 1733999 = 2600999) B2600999
theorem B5854625 : Blo 1733067 5854625 := bstep (se 2 (by rfl) ⟨2195484, by rfl⟩ : syracuseStep 5854625 = 4390969) B4390969
theorem B1734055 : Blo 1733067 1734055 := bstep (se 1 (by rfl) ⟨1300541, by rfl⟩ : syracuseStep 1734055 = 2601083) B2601083
theorem B13170113 : Blo 1733067 13170113 := bstep (se 2 (by rfl) ⟨4938792, by rfl⟩ : syracuseStep 13170113 = 9877585) B9877585
theorem B2602439 : Blo 1733067 2602439 := bstep (se 1 (by rfl) ⟨1951829, by rfl⟩ : syracuseStep 2602439 = 3903659) B3903659
theorem B1734139 : Blo 1733067 1734139 := bstep (se 1 (by rfl) ⟨1300604, by rfl⟩ : syracuseStep 1734139 = 2601209) B2601209
theorem B1734207 : Blo 1733067 1734207 := bstep (se 1 (by rfl) ⟨1300655, by rfl⟩ : syracuseStep 1734207 = 2601311) B2601311
theorem B1734215 : Blo 1733067 1734215 := bstep (se 1 (by rfl) ⟨1300661, by rfl⟩ : syracuseStep 1734215 = 2601323) B2601323
theorem B9016967 : Blo 1733067 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B9369245 : Blo 1733067 9369245 := bstep (se 3 (by rfl) ⟨1756733, by rfl⟩ : syracuseStep 9369245 = 3513467) B3513467
theorem B4388539 : Blo 1733067 4388539 := bstep (se 1 (by rfl) ⟨3291404, by rfl⟩ : syracuseStep 4388539 = 6582809) B6582809
theorem B1734367 : Blo 1733067 1734367 := bstep (se 1 (by rfl) ⟨1300775, by rfl⟩ : syracuseStep 1734367 = 2601551) B2601551
theorem B1734447 : Blo 1733067 1734447 := bstep (se 1 (by rfl) ⟨1300835, by rfl⟩ : syracuseStep 1734447 = 2601671) B2601671
theorem B1734555 : Blo 1733067 1734555 := bstep (se 1 (by rfl) ⟨1300916, by rfl⟩ : syracuseStep 1734555 = 2601833) B2601833
theorem B1734607 : Blo 1733067 1734607 := bstep (se 1 (by rfl) ⟨1300955, by rfl⟩ : syracuseStep 1734607 = 2601911) B2601911
theorem B17790949 : Blo 1733067 17790949 := bstep (se 4 (by rfl) ⟨1667901, by rfl⟩ : syracuseStep 17790949 = 3335803) B3335803
theorem B1734631 : Blo 1733067 1734631 := bstep (se 1 (by rfl) ⟨1300973, by rfl⟩ : syracuseStep 1734631 = 2601947) B2601947
theorem B6584449 : Blo 1733067 6584449 := bstep (se 2 (by rfl) ⟨2469168, by rfl⟩ : syracuseStep 6584449 = 4938337) B4938337
theorem B1734943 : Blo 1733067 1734943 := bstep (se 1 (by rfl) ⟨1301207, by rfl⟩ : syracuseStep 1734943 = 2602415) B2602415
theorem B1735003 : Blo 1733067 1735003 := bstep (se 1 (by rfl) ⟨1301252, by rfl⟩ : syracuseStep 1735003 = 2602505) B2602505
theorem B94935401 : Blo 1733067 94935401 := bstep (se 2 (by rfl) ⟨35600775, by rfl⟩ : syracuseStep 94935401 = 71201551) B71201551
theorem B1735023 : Blo 1733067 1735023 := bstep (se 1 (by rfl) ⟨1301267, by rfl⟩ : syracuseStep 1735023 = 2602535) B2602535
theorem B7403987 : Blo 1733067 7403987 := bstep (se 1 (by rfl) ⟨5552990, by rfl⟩ : syracuseStep 7403987 = 11105981) B11105981
theorem B3291617 : Blo 1733067 3291617 := bstep (se 2 (by rfl) ⟨1234356, by rfl⟩ : syracuseStep 3291617 = 2468713) B2468713
theorem B3955169 : Blo 1733067 3955169 := bstep (se 2 (by rfl) ⟨1483188, by rfl⟩ : syracuseStep 3955169 = 2966377) B2966377
theorem B7027195 : Blo 1733067 7027195 := bstep (se 1 (by rfl) ⟨5270396, by rfl⟩ : syracuseStep 7027195 = 10540793) B10540793
theorem B14817815 : Blo 1733067 14817815 := bstep (se 1 (by rfl) ⟨11113361, by rfl⟩ : syracuseStep 14817815 = 22226723) B22226723
theorem B3291769 : Blo 1733067 3291769 := bstep (se 2 (by rfl) ⟨1234413, by rfl⟩ : syracuseStep 3291769 = 2468827) B2468827
theorem B12499595 : Blo 1733067 12499595 := bstep (se 1 (by rfl) ⟨9374696, by rfl⟩ : syracuseStep 12499595 = 18749393) B18749393
theorem B8329949 : Blo 1733067 8329949 := bstep (se 3 (by rfl) ⟨1561865, by rfl⟩ : syracuseStep 8329949 = 3123731) B3123731
theorem B4168415 : Blo 1733067 4168415 := bstep (se 1 (by rfl) ⟨3126311, by rfl⟩ : syracuseStep 4168415 = 6252623) B6252623
theorem B4389623 : Blo 1733067 4389623 := bstep (se 1 (by rfl) ⟨3292217, by rfl⟩ : syracuseStep 4389623 = 6584435) B6584435
theorem B20011961 : Blo 1733067 20011961 := bstep (se 2 (by rfl) ⟨7504485, by rfl⟩ : syracuseStep 20011961 = 15008971) B15008971
theorem B4684787 : Blo 1733067 4684787 := bstep (se 1 (by rfl) ⟨3513590, by rfl⟩ : syracuseStep 4684787 = 7027181) B7027181
theorem B35585011 : Blo 1733067 35585011 := bstep (se 1 (by rfl) ⟨26688758, by rfl⟩ : syracuseStep 35585011 = 53377517) B53377517
theorem B3701857 : Blo 1733067 3701857 := bstep (se 2 (by rfl) ⟨1388196, by rfl⟩ : syracuseStep 3701857 = 2776393) B2776393
theorem B3702113 : Blo 1733067 3702113 := bstep (se 2 (by rfl) ⟨1388292, by rfl⟩ : syracuseStep 3702113 = 2776585) B2776585
theorem B2776457 : Blo 1733067 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B9379259 : Blo 1733067 9379259 := bstep (se 1 (by rfl) ⟨7034444, by rfl⟩ : syracuseStep 9379259 = 14068889) B14068889
theorem B8781371 : Blo 1733067 8781371 := bstep (se 1 (by rfl) ⟨6586028, by rfl⟩ : syracuseStep 8781371 = 13172057) B13172057
theorem B4390483 : Blo 1733067 4390483 := bstep (se 1 (by rfl) ⟨3292862, by rfl⟩ : syracuseStep 4390483 = 6585725) B6585725
theorem B2195039 : Blo 1733067 2195039 := bstep (se 1 (by rfl) ⟨1646279, by rfl⟩ : syracuseStep 2195039 = 3292559) B3292559
theorem B11107955 : Blo 1733067 11107955 := bstep (se 1 (by rfl) ⟨8330966, by rfl⟩ : syracuseStep 11107955 = 16661933) B16661933
theorem B37510877 : Blo 1733067 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B7405319 : Blo 1733067 7405319 := bstep (se 1 (by rfl) ⟨5553989, by rfl⟩ : syracuseStep 7405319 = 11107979) B11107979
theorem B3292969 : Blo 1733067 3292969 := bstep (se 2 (by rfl) ⟨1234863, by rfl⟩ : syracuseStep 3292969 = 2469727) B2469727
theorem B4448047 : Blo 1733067 4448047 := bstep (se 1 (by rfl) ⟨3336035, by rfl⟩ : syracuseStep 4448047 = 6672071) B6672071
theorem B8781857 : Blo 1733067 8781857 := bstep (se 2 (by rfl) ⟨3293196, by rfl⟩ : syracuseStep 8781857 = 6586393) B6586393
theorem B4391131 : Blo 1733067 4391131 := bstep (se 1 (by rfl) ⟨3293348, by rfl⟩ : syracuseStep 4391131 = 6586697) B6586697
theorem B2195687 : Blo 1733067 2195687 := bstep (se 1 (by rfl) ⟨1646765, by rfl⟩ : syracuseStep 2195687 = 3293531) B3293531
theorem B8773919 : Blo 1733067 8773919 := bstep (se 1 (by rfl) ⟨6580439, by rfl⟩ : syracuseStep 8773919 = 13160879) B13160879
theorem B5849441 : Blo 1733067 5849441 := bstep (se 2 (by rfl) ⟨2193540, by rfl⟩ : syracuseStep 5849441 = 4387081) B4387081
theorem B1950079 : Blo 1733067 1950079 := bstep (se 1 (by rfl) ⟨1462559, by rfl⟩ : syracuseStep 1950079 = 2925119) B2925119
theorem B2195839 : Blo 1733067 2195839 := bstep (se 1 (by rfl) ⟨1646879, by rfl⟩ : syracuseStep 2195839 = 3293759) B3293759
theorem B5554631 : Blo 1733067 5554631 := bstep (se 1 (by rfl) ⟨4165973, by rfl⟩ : syracuseStep 5554631 = 8331947) B8331947
theorem B12501611 : Blo 1733067 12501611 := bstep (se 1 (by rfl) ⟨9376208, by rfl⟩ : syracuseStep 12501611 = 18752417) B18752417
theorem B10281725 : Blo 1733067 10281725 := bstep (se 3 (by rfl) ⟨1927823, by rfl⟩ : syracuseStep 10281725 = 3855647) B3855647
theorem B6587183 : Blo 1733067 6587183 := bstep (se 1 (by rfl) ⟨4940387, by rfl⟩ : syracuseStep 6587183 = 9880775) B9880775
theorem B4391891 : Blo 1733067 4391891 := bstep (se 1 (by rfl) ⟨3293918, by rfl⟩ : syracuseStep 4391891 = 6587837) B6587837
theorem B3900779 : Blo 1733067 3900779 := bstep (se 1 (by rfl) ⟨2925584, by rfl⟩ : syracuseStep 3900779 = 5851169) B5851169
theorem B3901049 : Blo 1733067 3901049 := bstep (se 2 (by rfl) ⟨1462893, by rfl⟩ : syracuseStep 3901049 = 2925787) B2925787
theorem B5850791 : Blo 1733067 5850791 := bstep (se 1 (by rfl) ⟨4388093, by rfl⟩ : syracuseStep 5850791 = 8776187) B8776187
theorem B24045245 : Blo 1733067 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B1951483 : Blo 1733067 1951483 := bstep (se 1 (by rfl) ⟨1463612, by rfl⟩ : syracuseStep 1951483 = 2927225) B2927225
theorem B8333063 : Blo 1733067 8333063 := bstep (se 1 (by rfl) ⟨6249797, by rfl⟩ : syracuseStep 8333063 = 12499595) B12499595
theorem B1951519 : Blo 1733067 1951519 := bstep (se 1 (by rfl) ⟨1463639, by rfl⟩ : syracuseStep 1951519 = 2927279) B2927279
theorem B2778943 : Blo 1733067 2778943 := bstep (se 1 (by rfl) ⟨2084207, by rfl⟩ : syracuseStep 2778943 = 4168415) B4168415
theorem B2926415 : Blo 1733067 2926415 := bstep (se 1 (by rfl) ⟨2194811, by rfl⟩ : syracuseStep 2926415 = 4389623) B4389623
theorem B21104549 : Blo 1733067 21104549 := bstep (se 4 (by rfl) ⟨1978551, by rfl⟩ : syracuseStep 21104549 = 3957103) B3957103
theorem B3123191 : Blo 1733067 3123191 := bstep (se 1 (by rfl) ⟨2342393, by rfl⟩ : syracuseStep 3123191 = 4684787) B4684787
theorem B6580349 : Blo 1733067 6580349 := bstep (se 3 (by rfl) ⟨1233815, by rfl⟩ : syracuseStep 6580349 = 2467631) B2467631
theorem B2468075 : Blo 1733067 2468075 := bstep (se 1 (by rfl) ⟨1851056, by rfl⟩ : syracuseStep 2468075 = 3702113) B3702113
theorem B5851385 : Blo 1733067 5851385 := bstep (se 2 (by rfl) ⟨2194269, by rfl⟩ : syracuseStep 5851385 = 4388539) B4388539
theorem B6252839 : Blo 1733067 6252839 := bstep (se 1 (by rfl) ⟨4689629, by rfl⟩ : syracuseStep 6252839 = 9379259) B9379259
theorem B5851439 : Blo 1733067 5851439 := bstep (se 1 (by rfl) ⟨4388579, by rfl⟩ : syracuseStep 5851439 = 8777159) B8777159
theorem B7031087 : Blo 1733067 7031087 := bstep (se 1 (by rfl) ⟨5273315, by rfl⟩ : syracuseStep 7031087 = 10546631) B10546631
theorem B53365229 : Blo 1733067 53365229 := bstep (se 3 (by rfl) ⟨10005980, by rfl⟩ : syracuseStep 53365229 = 20011961) B20011961
theorem B5851655 : Blo 1733067 5851655 := bstep (se 1 (by rfl) ⟨4388741, by rfl⟩ : syracuseStep 5851655 = 8777483) B8777483
theorem B3902057 : Blo 1733067 3902057 := bstep (se 2 (by rfl) ⟨1463271, by rfl⟩ : syracuseStep 3902057 = 2926543) B2926543
theorem B10005241 : Blo 1733067 10005241 := bstep (se 2 (by rfl) ⟨3751965, by rfl⟩ : syracuseStep 10005241 = 7503931) B7503931
theorem B9874169 : Blo 1733067 9874169 := bstep (se 2 (by rfl) ⟨3702813, by rfl⟩ : syracuseStep 9874169 = 7405627) B7405627
theorem B29625101 : Blo 1733067 29625101 := bstep (se 3 (by rfl) ⟨5554706, by rfl⟩ : syracuseStep 29625101 = 11109413) B11109413
theorem B6581047 : Blo 1733067 6581047 := bstep (se 1 (by rfl) ⟨4935785, by rfl⟩ : syracuseStep 6581047 = 9871571) B9871571
theorem B24988571 : Blo 1733067 24988571 := bstep (se 1 (by rfl) ⟨18741428, by rfl⟩ : syracuseStep 24988571 = 37482857) B37482857
theorem B36572077 : Blo 1733067 36572077 := bstep (se 3 (by rfl) ⟨6857264, by rfl⟩ : syracuseStep 36572077 = 13714529) B13714529
theorem B28109753 : Blo 1733067 28109753 := bstep (se 2 (by rfl) ⟨10541157, by rfl⟩ : syracuseStep 28109753 = 21082315) B21082315
theorem B2927657 : Blo 1733067 2927657 := bstep (se 2 (by rfl) ⟨1097871, by rfl⟩ : syracuseStep 2927657 = 2195743) B2195743
theorem B2600057 : Blo 1733067 2600057 := bstep (se 2 (by rfl) ⟨975021, by rfl⟩ : syracuseStep 2600057 = 1950043) B1950043
theorem B5852303 : Blo 1733067 5852303 := bstep (se 1 (by rfl) ⟨4389227, by rfl⟩ : syracuseStep 5852303 = 8778455) B8778455
theorem B2600159 : Blo 1733067 2600159 := bstep (se 1 (by rfl) ⟨1950119, by rfl⟩ : syracuseStep 2600159 = 3900239) B3900239
theorem B3902687 : Blo 1733067 3902687 := bstep (se 1 (by rfl) ⟨2927015, by rfl⟩ : syracuseStep 3902687 = 5854031) B5854031
theorem B2084063 : Blo 1733067 2084063 := bstep (se 1 (by rfl) ⟨1563047, by rfl⟩ : syracuseStep 2084063 = 3126095) B3126095
theorem B2927839 : Blo 1733067 2927839 := bstep (se 1 (by rfl) ⟨2195879, by rfl⟩ : syracuseStep 2927839 = 4391759) B4391759
theorem B2600201 : Blo 1733067 2600201 := bstep (se 2 (by rfl) ⟨975075, by rfl⟩ : syracuseStep 2600201 = 1950151) B1950151
theorem B2600303 : Blo 1733067 2600303 := bstep (se 1 (by rfl) ⟨1950227, by rfl⟩ : syracuseStep 2600303 = 3900455) B3900455
theorem B3902903 : Blo 1733067 3902903 := bstep (se 1 (by rfl) ⟨2927177, by rfl⟩ : syracuseStep 3902903 = 5854355) B5854355
theorem B2600423 : Blo 1733067 2600423 := bstep (se 1 (by rfl) ⟨1950317, by rfl⟩ : syracuseStep 2600423 = 3900635) B3900635
theorem B5705207 : Blo 1733067 5705207 := bstep (se 1 (by rfl) ⟨4278905, by rfl⟩ : syracuseStep 5705207 = 8557811) B8557811
theorem B5852735 : Blo 1733067 5852735 := bstep (se 1 (by rfl) ⟨4389551, by rfl⟩ : syracuseStep 5852735 = 8779103) B8779103
theorem B2600555 : Blo 1733067 2600555 := bstep (se 1 (by rfl) ⟨1950416, by rfl⟩ : syracuseStep 2600555 = 3900833) B3900833
theorem B3903083 : Blo 1733067 3903083 := bstep (se 1 (by rfl) ⟨2927312, by rfl⟩ : syracuseStep 3903083 = 5854625) B5854625
theorem B2600681 : Blo 1733067 2600681 := bstep (se 2 (by rfl) ⟨975255, by rfl⟩ : syracuseStep 2600681 = 1950511) B1950511
theorem B6246163 : Blo 1733067 6246163 := bstep (se 1 (by rfl) ⟨4684622, by rfl⟩ : syracuseStep 6246163 = 9369245) B9369245
theorem B2600825 : Blo 1733067 2600825 := bstep (se 2 (by rfl) ⟨975309, by rfl⟩ : syracuseStep 2600825 = 1950619) B1950619
theorem B3903353 : Blo 1733067 3903353 := bstep (se 2 (by rfl) ⟨1463757, by rfl⟩ : syracuseStep 3903353 = 2927515) B2927515
theorem B8777645 : Blo 1733067 8777645 := bstep (se 3 (by rfl) ⟨1645808, by rfl⟩ : syracuseStep 8777645 = 3291617) B3291617
theorem B10547117 : Blo 1733067 10547117 := bstep (se 3 (by rfl) ⟨1977584, by rfl⟩ : syracuseStep 10547117 = 3955169) B3955169
theorem B2600927 : Blo 1733067 2600927 := bstep (se 1 (by rfl) ⟨1950695, by rfl⟩ : syracuseStep 2600927 = 3901391) B3901391
theorem B4935809 : Blo 1733067 4935809 := bstep (se 2 (by rfl) ⟨1850928, by rfl⟩ : syracuseStep 4935809 = 3701857) B3701857
theorem B2601179 : Blo 1733067 2601179 := bstep (se 1 (by rfl) ⟨1950884, by rfl⟩ : syracuseStep 2601179 = 3901769) B3901769
theorem B10014941 : Blo 1733067 10014941 := bstep (se 3 (by rfl) ⟨1877801, by rfl⟩ : syracuseStep 10014941 = 3755603) B3755603
theorem B2601191 : Blo 1733067 2601191 := bstep (se 1 (by rfl) ⟨1950893, by rfl⟩ : syracuseStep 2601191 = 3901787) B3901787
theorem B5853437 : Blo 1733067 5853437 := bstep (se 3 (by rfl) ⟨1097519, by rfl⟩ : syracuseStep 5853437 = 2195039) B2195039
theorem B4935991 : Blo 1733067 4935991 := bstep (se 1 (by rfl) ⟨3701993, by rfl⟩ : syracuseStep 4935991 = 7403987) B7403987
theorem B2601353 : Blo 1733067 2601353 := bstep (se 2 (by rfl) ⟨975507, by rfl⟩ : syracuseStep 2601353 = 1951015) B1951015
theorem B1733071 : Blo 1733067 1733071 := bstep (se 1 (by rfl) ⟨1299803, by rfl⟩ : syracuseStep 1733071 = 2599607) B2599607
theorem B2601449 : Blo 1733067 2601449 := bstep (se 2 (by rfl) ⟨975543, by rfl⟩ : syracuseStep 2601449 = 1951087) B1951087
theorem B100029005 : Blo 1733067 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B10547795 : Blo 1733067 10547795 := bstep (se 1 (by rfl) ⟨7910846, by rfl⟩ : syracuseStep 10547795 = 15821693) B15821693
theorem B1733223 : Blo 1733067 1733223 := bstep (se 1 (by rfl) ⟨1299917, by rfl⟩ : syracuseStep 1733223 = 2599835) B2599835
theorem B2601575 : Blo 1733067 2601575 := bstep (se 1 (by rfl) ⟨1951181, by rfl⟩ : syracuseStep 2601575 = 3902363) B3902363
theorem B2601707 : Blo 1733067 2601707 := bstep (se 1 (by rfl) ⟨1951280, by rfl⟩ : syracuseStep 2601707 = 3902561) B3902561
theorem B3126023 : Blo 1733067 3126023 := bstep (se 1 (by rfl) ⟨2344517, by rfl⟩ : syracuseStep 3126023 = 4689035) B4689035
theorem B2601737 : Blo 1733067 2601737 := bstep (se 2 (by rfl) ⟨975651, by rfl⟩ : syracuseStep 2601737 = 1951303) B1951303
theorem B5853977 : Blo 1733067 5853977 := bstep (se 2 (by rfl) ⟨2195241, by rfl⟩ : syracuseStep 5853977 = 4390483) B4390483
theorem B1733487 : Blo 1733067 1733487 := bstep (se 1 (by rfl) ⟨1300115, by rfl⟩ : syracuseStep 1733487 = 2600231) B2600231
theorem B2601839 : Blo 1733067 2601839 := bstep (se 1 (by rfl) ⟨1951379, by rfl⟩ : syracuseStep 2601839 = 3902759) B3902759
theorem B1733543 : Blo 1733067 1733543 := bstep (se 1 (by rfl) ⟨1300157, by rfl⟩ : syracuseStep 1733543 = 2600315) B2600315
theorem B1733627 : Blo 1733067 1733627 := bstep (se 1 (by rfl) ⟨1300220, by rfl⟩ : syracuseStep 1733627 = 2600441) B2600441
theorem B5854247 : Blo 1733067 5854247 := bstep (se 1 (by rfl) ⟨4390685, by rfl⟩ : syracuseStep 5854247 = 8781371) B8781371
theorem B1733695 : Blo 1733067 1733695 := bstep (se 1 (by rfl) ⟨1300271, by rfl⟩ : syracuseStep 1733695 = 2600543) B2600543
theorem B2602091 : Blo 1733067 2602091 := bstep (se 1 (by rfl) ⟨1951568, by rfl⟩ : syracuseStep 2602091 = 3903137) B3903137
theorem B4936879 : Blo 1733067 4936879 := bstep (se 1 (by rfl) ⟨3702659, by rfl⟩ : syracuseStep 4936879 = 7405319) B7405319
theorem B1733839 : Blo 1733067 1733839 := bstep (se 1 (by rfl) ⟨1300379, by rfl⟩ : syracuseStep 1733839 = 2600759) B2600759
theorem B23721265 : Blo 1733067 23721265 := bstep (se 2 (by rfl) ⟨8895474, by rfl⟩ : syracuseStep 23721265 = 17790949) B17790949
theorem B4937051 : Blo 1733067 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B2602331 : Blo 1733067 2602331 := bstep (se 1 (by rfl) ⟨1951748, by rfl⟩ : syracuseStep 2602331 = 3903497) B3903497
theorem B1734043 : Blo 1733067 1734043 := bstep (se 1 (by rfl) ⟨1300532, by rfl⟩ : syracuseStep 1734043 = 2601065) B2601065
theorem B6583751 : Blo 1733067 6583751 := bstep (se 1 (by rfl) ⟨4937813, by rfl⟩ : syracuseStep 6583751 = 9875627) B9875627
theorem B8779265 : Blo 1733067 8779265 := bstep (se 2 (by rfl) ⟨3292224, by rfl⟩ : syracuseStep 8779265 = 6584449) B6584449
theorem B1734255 : Blo 1733067 1734255 := bstep (se 1 (by rfl) ⟨1300691, by rfl⟩ : syracuseStep 1734255 = 2601383) B2601383
theorem B1734311 : Blo 1733067 1734311 := bstep (se 1 (by rfl) ⟨1300733, by rfl⟩ : syracuseStep 1734311 = 2601467) B2601467
theorem B1734395 : Blo 1733067 1734395 := bstep (se 1 (by rfl) ⟨1300796, by rfl⟩ : syracuseStep 1734395 = 2601593) B2601593
theorem B1734431 : Blo 1733067 1734431 := bstep (se 1 (by rfl) ⟨1300823, by rfl⟩ : syracuseStep 1734431 = 2601647) B2601647
theorem B1734463 : Blo 1733067 1734463 := bstep (se 1 (by rfl) ⟨1300847, by rfl⟩ : syracuseStep 1734463 = 2601695) B2601695
theorem B8337289 : Blo 1733067 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B1734639 : Blo 1733067 1734639 := bstep (se 1 (by rfl) ⟨1300979, by rfl⟩ : syracuseStep 1734639 = 2601959) B2601959
theorem B9369593 : Blo 1733067 9369593 := bstep (se 2 (by rfl) ⟨3513597, by rfl⟩ : syracuseStep 9369593 = 7027195) B7027195
theorem B28121165 : Blo 1733067 28121165 := bstep (se 3 (by rfl) ⟨5272718, by rfl⟩ : syracuseStep 28121165 = 10545437) B10545437
theorem B5855327 : Blo 1733067 5855327 := bstep (se 1 (by rfl) ⟨4391495, by rfl⟩ : syracuseStep 5855327 = 8782991) B8782991
theorem B7403663 : Blo 1733067 7403663 := bstep (se 1 (by rfl) ⟨5552747, by rfl⟩ : syracuseStep 7403663 = 11105495) B11105495
theorem B1734811 : Blo 1733067 1734811 := bstep (se 1 (by rfl) ⟨1301108, by rfl⟩ : syracuseStep 1734811 = 2602217) B2602217
theorem B4389025 : Blo 1733067 4389025 := bstep (se 2 (by rfl) ⟨1645884, by rfl⟩ : syracuseStep 4389025 = 3291769) B3291769
theorem B1734847 : Blo 1733067 1734847 := bstep (se 1 (by rfl) ⟨1301135, by rfl⟩ : syracuseStep 1734847 = 2602271) B2602271
theorem B75028679 : Blo 1733067 75028679 := bstep (se 1 (by rfl) ⟨56271509, by rfl⟩ : syracuseStep 75028679 = 112543019) B112543019
theorem B8780075 : Blo 1733067 8780075 := bstep (se 1 (by rfl) ⟨6585056, by rfl⟩ : syracuseStep 8780075 = 13170113) B13170113
theorem B1734959 : Blo 1733067 1734959 := bstep (se 1 (by rfl) ⟨1301219, by rfl⟩ : syracuseStep 1734959 = 2602439) B2602439
theorem B7403885 : Blo 1733067 7403885 := bstep (se 3 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 7403885 = 2776457) B2776457
theorem B11114927 : Blo 1733067 11114927 := bstep (se 1 (by rfl) ⟨8336195, by rfl⟩ : syracuseStep 11114927 = 16672391) B16672391
theorem B38017669 : Blo 1733067 38017669 := bstep (se 4 (by rfl) ⟨3564156, by rfl⟩ : syracuseStep 38017669 = 7128313) B7128313
theorem B47446681 : Blo 1733067 47446681 := bstep (se 2 (by rfl) ⟨17792505, by rfl⟩ : syracuseStep 47446681 = 35585011) B35585011
theorem B6249307 : Blo 1733067 6249307 := bstep (se 1 (by rfl) ⟨4686980, by rfl⟩ : syracuseStep 6249307 = 9373961) B9373961
theorem B63290267 : Blo 1733067 63290267 := bstep (se 1 (by rfl) ⟨47467700, by rfl⟩ : syracuseStep 63290267 = 94935401) B94935401
theorem B9878543 : Blo 1733067 9878543 := bstep (se 1 (by rfl) ⟨7408907, by rfl⟩ : syracuseStep 9878543 = 14817815) B14817815
theorem B7027841 : Blo 1733067 7027841 := bstep (se 2 (by rfl) ⟨2635440, by rfl⟩ : syracuseStep 7027841 = 5270881) B5270881
theorem B5553299 : Blo 1733067 5553299 := bstep (se 1 (by rfl) ⟨4164974, by rfl⟩ : syracuseStep 5553299 = 8329949) B8329949
theorem B10690127 : Blo 1733067 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B4390625 : Blo 1733067 4390625 := bstep (se 2 (by rfl) ⟨1646484, by rfl⟩ : syracuseStep 4390625 = 3292969) B3292969
theorem B5930729 : Blo 1733067 5930729 := bstep (se 2 (by rfl) ⟨2224023, by rfl⟩ : syracuseStep 5930729 = 4448047) B4448047
theorem B74284789 : Blo 1733067 74284789 := bstep (se 5 (by rfl) ⟨3482099, by rfl⟩ : syracuseStep 74284789 = 6964199) B6964199
theorem B7405303 : Blo 1733067 7405303 := bstep (se 1 (by rfl) ⟨5553977, by rfl⟩ : syracuseStep 7405303 = 11107955) B11107955
theorem B22568861 : Blo 1733067 22568861 := bstep (se 3 (by rfl) ⟨4231661, by rfl⟩ : syracuseStep 22568861 = 8463323) B8463323
theorem B6250429 : Blo 1733067 6250429 := bstep (se 3 (by rfl) ⟨1171955, by rfl⟩ : syracuseStep 6250429 = 2343911) B2343911
theorem B6676627 : Blo 1733067 6676627 := bstep (se 1 (by rfl) ⟨5007470, by rfl⟩ : syracuseStep 6676627 = 10014941) B10014941
theorem B5849279 : Blo 1733067 5849279 := bstep (se 1 (by rfl) ⟨4386959, by rfl⟩ : syracuseStep 5849279 = 8773919) B8773919
theorem B3899627 : Blo 1733067 3899627 := bstep (se 1 (by rfl) ⟨2924720, by rfl⟩ : syracuseStep 3899627 = 5849441) B5849441
theorem B3703087 : Blo 1733067 3703087 := bstep (se 1 (by rfl) ⟨2777315, by rfl⟩ : syracuseStep 3703087 = 5554631) B5554631
theorem B4391455 : Blo 1733067 4391455 := bstep (se 1 (by rfl) ⟨3293591, by rfl⟩ : syracuseStep 4391455 = 6587183) B6587183
theorem B8774729 : Blo 1733067 8774729 := bstep (se 2 (by rfl) ⟨3290523, by rfl⟩ : syracuseStep 8774729 = 6581047) B6581047
theorem B3900527 : Blo 1733067 3900527 := bstep (se 1 (by rfl) ⟨2925395, by rfl⟩ : syracuseStep 3900527 = 5850791) B5850791
theorem B8332409 : Blo 1733067 8332409 := bstep (se 2 (by rfl) ⟨3124653, by rfl⟩ : syracuseStep 8332409 = 6249307) B6249307
theorem B5555375 : Blo 1733067 5555375 := bstep (se 1 (by rfl) ⟨4166531, by rfl⟩ : syracuseStep 5555375 = 8333063) B8333063
theorem B1950943 : Blo 1733067 1950943 := bstep (se 1 (by rfl) ⟨1463207, by rfl⟩ : syracuseStep 1950943 = 2926415) B2926415
theorem B2082127 : Blo 1733067 2082127 := bstep (se 1 (by rfl) ⟨1561595, by rfl⟩ : syracuseStep 2082127 = 3123191) B3123191
theorem B3900923 : Blo 1733067 3900923 := bstep (se 1 (by rfl) ⟨2925692, by rfl⟩ : syracuseStep 3900923 = 5851385) B5851385
theorem B3900959 : Blo 1733067 3900959 := bstep (se 1 (by rfl) ⟨2925719, by rfl⟩ : syracuseStep 3900959 = 5851439) B5851439
theorem B4687391 : Blo 1733067 4687391 := bstep (se 1 (by rfl) ⟨3515543, by rfl⟩ : syracuseStep 4687391 = 7031087) B7031087
theorem B3901103 : Blo 1733067 3901103 := bstep (se 1 (by rfl) ⟨2925827, by rfl⟩ : syracuseStep 3901103 = 5851655) B5851655
theorem B1951771 : Blo 1733067 1951771 := bstep (se 1 (by rfl) ⟨1463828, by rfl⟩ : syracuseStep 1951771 = 2927657) B2927657
theorem B3901535 : Blo 1733067 3901535 := bstep (se 1 (by rfl) ⟨2926151, by rfl⟩ : syracuseStep 3901535 = 5852303) B5852303
theorem B33335621 : Blo 1733067 33335621 := bstep (se 4 (by rfl) ⟨3125214, by rfl⟩ : syracuseStep 33335621 = 6250429) B6250429
theorem B9873737 : Blo 1733067 9873737 := bstep (se 2 (by rfl) ⟨3702651, by rfl⟩ : syracuseStep 9873737 = 7405303) B7405303
theorem B3803471 : Blo 1733067 3803471 := bstep (se 1 (by rfl) ⟨2852603, by rfl⟩ : syracuseStep 3803471 = 5705207) B5705207
theorem B3901823 : Blo 1733067 3901823 := bstep (se 1 (by rfl) ⟨2926367, by rfl⟩ : syracuseStep 3901823 = 5852735) B5852735
theorem B3705257 : Blo 1733067 3705257 := bstep (se 2 (by rfl) ⟨1389471, by rfl⟩ : syracuseStep 3705257 = 2778943) B2778943
theorem B2927083 : Blo 1733067 2927083 := bstep (se 1 (by rfl) ⟨2195312, by rfl⟩ : syracuseStep 2927083 = 4390625) B4390625
theorem B5851763 : Blo 1733067 5851763 := bstep (se 1 (by rfl) ⟨4388822, by rfl⟩ : syracuseStep 5851763 = 8777645) B8777645
theorem B7031411 : Blo 1733067 7031411 := bstep (se 1 (by rfl) ⟨5273558, by rfl⟩ : syracuseStep 7031411 = 10547117) B10547117
theorem B3902291 : Blo 1733067 3902291 := bstep (se 1 (by rfl) ⟨2926718, by rfl⟩ : syracuseStep 3902291 = 5853437) B5853437
theorem B5852033 : Blo 1733067 5852033 := bstep (se 2 (by rfl) ⟨2194512, by rfl⟩ : syracuseStep 5852033 = 4389025) B4389025
theorem B66686003 : Blo 1733067 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B7031863 : Blo 1733067 7031863 := bstep (se 1 (by rfl) ⟨5273897, by rfl⟩ : syracuseStep 7031863 = 10547795) B10547795
theorem B8334407 : Blo 1733067 8334407 := bstep (se 1 (by rfl) ⟨6250805, by rfl⟩ : syracuseStep 8334407 = 12501611) B12501611
theorem B6581321 : Blo 1733067 6581321 := bstep (se 2 (by rfl) ⟨2467995, by rfl⟩ : syracuseStep 6581321 = 4935991) B4935991
theorem B2600105 : Blo 1733067 2600105 := bstep (se 2 (by rfl) ⟨975039, by rfl⟩ : syracuseStep 2600105 = 1950079) B1950079
theorem B2927785 : Blo 1733067 2927785 := bstep (se 2 (by rfl) ⟨1097919, by rfl⟩ : syracuseStep 2927785 = 2195839) B2195839
theorem B2084015 : Blo 1733067 2084015 := bstep (se 1 (by rfl) ⟨1563011, by rfl⟩ : syracuseStep 2084015 = 3126023) B3126023
theorem B3902651 : Blo 1733067 3902651 := bstep (se 1 (by rfl) ⟨2926988, by rfl⟩ : syracuseStep 3902651 = 5853977) B5853977
theorem B5557501 : Blo 1733067 5557501 := bstep (se 3 (by rfl) ⟨1042031, by rfl⟩ : syracuseStep 5557501 = 2084063) B2084063
theorem B6581533 : Blo 1733067 6581533 := bstep (se 3 (by rfl) ⟨1234037, by rfl⟩ : syracuseStep 6581533 = 2468075) B2468075
theorem B2927927 : Blo 1733067 2927927 := bstep (se 1 (by rfl) ⟨2195945, by rfl⟩ : syracuseStep 2927927 = 4391891) B4391891
theorem B3902831 : Blo 1733067 3902831 := bstep (se 1 (by rfl) ⟨2927123, by rfl⟩ : syracuseStep 3902831 = 5854247) B5854247
theorem B63262241 : Blo 1733067 63262241 := bstep (se 2 (by rfl) ⟨23723340, by rfl⟩ : syracuseStep 63262241 = 47446681) B47446681
theorem B2600519 : Blo 1733067 2600519 := bstep (se 1 (by rfl) ⟨1950389, by rfl⟩ : syracuseStep 2600519 = 3900779) B3900779
theorem B13340321 : Blo 1733067 13340321 := bstep (se 2 (by rfl) ⟨5002620, by rfl⟩ : syracuseStep 13340321 = 10005241) B10005241
theorem B5852843 : Blo 1733067 5852843 := bstep (se 1 (by rfl) ⟨4389632, by rfl⟩ : syracuseStep 5852843 = 8779265) B8779265
theorem B2600699 : Blo 1733067 2600699 := bstep (se 1 (by rfl) ⟨1950524, by rfl⟩ : syracuseStep 2600699 = 3901049) B3901049
theorem B14069699 : Blo 1733067 14069699 := bstep (se 1 (by rfl) ⟨10552274, by rfl⟩ : syracuseStep 14069699 = 21104549) B21104549
theorem B6246395 : Blo 1733067 6246395 := bstep (se 1 (by rfl) ⟨4684796, by rfl⟩ : syracuseStep 6246395 = 9369593) B9369593
theorem B18747443 : Blo 1733067 18747443 := bstep (se 1 (by rfl) ⟨14060582, by rfl⟩ : syracuseStep 18747443 = 28121165) B28121165
theorem B3903551 : Blo 1733067 3903551 := bstep (se 1 (by rfl) ⟨2927663, by rfl⟩ : syracuseStep 3903551 = 5855327) B5855327
theorem B4386899 : Blo 1733067 4386899 := bstep (se 1 (by rfl) ⟨3290174, by rfl⟩ : syracuseStep 4386899 = 6580349) B6580349
theorem B4935775 : Blo 1733067 4935775 := bstep (se 1 (by rfl) ⟨3701831, by rfl⟩ : syracuseStep 4935775 = 7403663) B7403663
theorem B5853383 : Blo 1733067 5853383 := bstep (se 1 (by rfl) ⟨4390037, by rfl⟩ : syracuseStep 5853383 = 8780075) B8780075
theorem B6582505 : Blo 1733067 6582505 := bstep (se 2 (by rfl) ⟨2468439, by rfl⟩ : syracuseStep 6582505 = 4936879) B4936879
theorem B4935923 : Blo 1733067 4935923 := bstep (se 1 (by rfl) ⟨3701942, by rfl⟩ : syracuseStep 4935923 = 7403885) B7403885
theorem B7409951 : Blo 1733067 7409951 := bstep (se 1 (by rfl) ⟨5557463, by rfl⟩ : syracuseStep 7409951 = 11114927) B11114927
theorem B3903785 : Blo 1733067 3903785 := bstep (se 2 (by rfl) ⟨1463919, by rfl⟩ : syracuseStep 3903785 = 2927839) B2927839
theorem B2601371 : Blo 1733067 2601371 := bstep (se 1 (by rfl) ⟨1951028, by rfl⟩ : syracuseStep 2601371 = 3902057) B3902057
theorem B6582779 : Blo 1733067 6582779 := bstep (se 1 (by rfl) ⟨4937084, by rfl⟩ : syracuseStep 6582779 = 9874169) B9874169
theorem B16659047 : Blo 1733067 16659047 := bstep (se 1 (by rfl) ⟨12494285, by rfl⟩ : syracuseStep 16659047 = 24988571) B24988571
theorem B42193511 : Blo 1733067 42193511 := bstep (se 1 (by rfl) ⟨31645133, by rfl⟩ : syracuseStep 42193511 = 63290267) B63290267
theorem B18739835 : Blo 1733067 18739835 := bstep (se 1 (by rfl) ⟨14054876, by rfl⟩ : syracuseStep 18739835 = 28109753) B28109753
theorem B1733371 : Blo 1733067 1733371 := bstep (se 1 (by rfl) ⟨1300028, by rfl⟩ : syracuseStep 1733371 = 2600057) B2600057
theorem B1733439 : Blo 1733067 1733439 := bstep (se 1 (by rfl) ⟨1300079, by rfl⟩ : syracuseStep 1733439 = 2600159) B2600159
theorem B2601791 : Blo 1733067 2601791 := bstep (se 1 (by rfl) ⟨1951343, by rfl⟩ : syracuseStep 2601791 = 3902687) B3902687
theorem B1733467 : Blo 1733067 1733467 := bstep (se 1 (by rfl) ⟨1300100, by rfl⟩ : syracuseStep 1733467 = 2600201) B2600201
theorem B1733535 : Blo 1733067 1733535 := bstep (se 1 (by rfl) ⟨1300151, by rfl⟩ : syracuseStep 1733535 = 2600303) B2600303
theorem B2601935 : Blo 1733067 2601935 := bstep (se 1 (by rfl) ⟨1951451, by rfl⟩ : syracuseStep 2601935 = 3902903) B3902903
theorem B1733615 : Blo 1733067 1733615 := bstep (se 1 (by rfl) ⟨1300211, by rfl⟩ : syracuseStep 1733615 = 2600423) B2600423
theorem B99046385 : Blo 1733067 99046385 := bstep (se 2 (by rfl) ⟨37142394, by rfl⟩ : syracuseStep 99046385 = 74284789) B74284789
theorem B2601977 : Blo 1733067 2601977 := bstep (se 2 (by rfl) ⟨975741, by rfl⟩ : syracuseStep 2601977 = 1951483) B1951483
theorem B8328217 : Blo 1733067 8328217 := bstep (se 2 (by rfl) ⟨3123081, by rfl⟩ : syracuseStep 8328217 = 6246163) B6246163
theorem B2602025 : Blo 1733067 2602025 := bstep (se 2 (by rfl) ⟨975759, by rfl⟩ : syracuseStep 2602025 = 1951519) B1951519
theorem B1733703 : Blo 1733067 1733703 := bstep (se 1 (by rfl) ⟨1300277, by rfl⟩ : syracuseStep 1733703 = 2600555) B2600555
theorem B2602055 : Blo 1733067 2602055 := bstep (se 1 (by rfl) ⟨1951541, by rfl⟩ : syracuseStep 2602055 = 3903083) B3903083
theorem B3953819 : Blo 1733067 3953819 := bstep (se 1 (by rfl) ⟨2965364, by rfl⟩ : syracuseStep 3953819 = 5930729) B5930729
theorem B1733787 : Blo 1733067 1733787 := bstep (se 1 (by rfl) ⟨1300340, by rfl⟩ : syracuseStep 1733787 = 2600681) B2600681
theorem B1733883 : Blo 1733067 1733883 := bstep (se 1 (by rfl) ⟨1300412, by rfl⟩ : syracuseStep 1733883 = 2600825) B2600825
theorem B2602235 : Blo 1733067 2602235 := bstep (se 1 (by rfl) ⟨1951676, by rfl⟩ : syracuseStep 2602235 = 3903353) B3903353
theorem B15045907 : Blo 1733067 15045907 := bstep (se 1 (by rfl) ⟨11284430, by rfl⟩ : syracuseStep 15045907 = 22568861) B22568861
theorem B1733951 : Blo 1733067 1733951 := bstep (se 1 (by rfl) ⟨1300463, by rfl⟩ : syracuseStep 1733951 = 2600927) B2600927
theorem B5854571 : Blo 1733067 5854571 := bstep (se 1 (by rfl) ⟨4390928, by rfl⟩ : syracuseStep 5854571 = 8781857) B8781857
theorem B3290539 : Blo 1733067 3290539 := bstep (se 1 (by rfl) ⟨2467904, by rfl⟩ : syracuseStep 3290539 = 4935809) B4935809
theorem B1734119 : Blo 1733067 1734119 := bstep (se 1 (by rfl) ⟨1300589, by rfl⟩ : syracuseStep 1734119 = 2601179) B2601179
theorem B1734127 : Blo 1733067 1734127 := bstep (se 1 (by rfl) ⟨1300595, by rfl⟩ : syracuseStep 1734127 = 2601191) B2601191
theorem B1734235 : Blo 1733067 1734235 := bstep (se 1 (by rfl) ⟨1300676, by rfl⟩ : syracuseStep 1734235 = 2601353) B2601353
theorem B5854841 : Blo 1733067 5854841 := bstep (se 2 (by rfl) ⟨2195565, by rfl⟩ : syracuseStep 5854841 = 4391131) B4391131
theorem B1734299 : Blo 1733067 1734299 := bstep (se 1 (by rfl) ⟨1300724, by rfl⟩ : syracuseStep 1734299 = 2601449) B2601449
theorem B18740909 : Blo 1733067 18740909 := bstep (se 3 (by rfl) ⟨3513920, by rfl⟩ : syracuseStep 18740909 = 7027841) B7027841
theorem B1734383 : Blo 1733067 1734383 := bstep (se 1 (by rfl) ⟨1300787, by rfl⟩ : syracuseStep 1734383 = 2601575) B2601575
theorem B1734471 : Blo 1733067 1734471 := bstep (se 1 (by rfl) ⟨1300853, by rfl⟩ : syracuseStep 1734471 = 2601707) B2601707
theorem B6854483 : Blo 1733067 6854483 := bstep (se 1 (by rfl) ⟨5140862, by rfl⟩ : syracuseStep 6854483 = 10281725) B10281725
theorem B1734491 : Blo 1733067 1734491 := bstep (se 1 (by rfl) ⟨1300868, by rfl⟩ : syracuseStep 1734491 = 2601737) B2601737
theorem B1734559 : Blo 1733067 1734559 := bstep (se 1 (by rfl) ⟨1300919, by rfl⟩ : syracuseStep 1734559 = 2601839) B2601839
theorem B5855165 : Blo 1733067 5855165 := bstep (se 3 (by rfl) ⟨1097843, by rfl⟩ : syracuseStep 5855165 = 2195687) B2195687
theorem B1734727 : Blo 1733067 1734727 := bstep (se 1 (by rfl) ⟨1301045, by rfl⟩ : syracuseStep 1734727 = 2602091) B2602091
theorem B50690225 : Blo 1733067 50690225 := bstep (se 2 (by rfl) ⟨19008834, by rfl⟩ : syracuseStep 50690225 = 38017669) B38017669
theorem B3291367 : Blo 1733067 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B1734887 : Blo 1733067 1734887 := bstep (se 1 (by rfl) ⟨1301165, by rfl⟩ : syracuseStep 1734887 = 2602331) B2602331
theorem B4389167 : Blo 1733067 4389167 := bstep (se 1 (by rfl) ⟨3291875, by rfl⟩ : syracuseStep 4389167 = 6583751) B6583751
theorem B16030163 : Blo 1733067 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B50019119 : Blo 1733067 50019119 := bstep (se 1 (by rfl) ⟨37514339, by rfl⟩ : syracuseStep 50019119 = 75028679) B75028679
theorem B4168559 : Blo 1733067 4168559 := bstep (se 1 (by rfl) ⟨3126419, by rfl⟩ : syracuseStep 4168559 = 6252839) B6252839
theorem B35576819 : Blo 1733067 35576819 := bstep (se 1 (by rfl) ⟨26682614, by rfl⟩ : syracuseStep 35576819 = 53365229) B53365229
theorem B31628353 : Blo 1733067 31628353 := bstep (se 2 (by rfl) ⟨11860632, by rfl⟩ : syracuseStep 31628353 = 23721265) B23721265
theorem B19750067 : Blo 1733067 19750067 := bstep (se 1 (by rfl) ⟨14812550, by rfl⟩ : syracuseStep 19750067 = 29625101) B29625101
theorem B6585695 : Blo 1733067 6585695 := bstep (se 1 (by rfl) ⟨4939271, by rfl⟩ : syracuseStep 6585695 = 9878543) B9878543
theorem B3702199 : Blo 1733067 3702199 := bstep (se 1 (by rfl) ⟨2776649, by rfl⟩ : syracuseStep 3702199 = 5553299) B5553299
theorem B195051077 : Blo 1733067 195051077 := bstep (se 4 (by rfl) ⟨18286038, by rfl⟩ : syracuseStep 195051077 = 36572077) B36572077
theorem B7126751 : Blo 1733067 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B11116385 : Blo 1733067 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B2924599 : Blo 1733067 2924599 := bstep (se 1 (by rfl) ⟨2193449, by rfl⟩ : syracuseStep 2924599 = 4386899) B4386899
theorem B3899519 : Blo 1733067 3899519 := bstep (se 1 (by rfl) ⟨2924639, by rfl⟩ : syracuseStep 3899519 = 5849279) B5849279
theorem B4939967 : Blo 1733067 4939967 := bstep (se 1 (by rfl) ⟨3704975, by rfl⟩ : syracuseStep 4939967 = 7409951) B7409951
theorem B37503269 : Blo 1733067 37503269 := bstep (se 4 (by rfl) ⟨3515931, by rfl⟩ : syracuseStep 37503269 = 7031863) B7031863
theorem B10543517 : Blo 1733067 10543517 := bstep (se 3 (by rfl) ⟨1976909, by rfl⟩ : syracuseStep 10543517 = 3953819) B3953819
theorem B12493223 : Blo 1733067 12493223 := bstep (se 1 (by rfl) ⟨9369917, by rfl⟩ : syracuseStep 12493223 = 18739835) B18739835
theorem B5849819 : Blo 1733067 5849819 := bstep (se 1 (by rfl) ⟨4387364, by rfl⟩ : syracuseStep 5849819 = 8774729) B8774729
theorem B5554939 : Blo 1733067 5554939 := bstep (se 1 (by rfl) ⟨4166204, by rfl⟩ : syracuseStep 5554939 = 8332409) B8332409
theorem B3703583 : Blo 1733067 3703583 := bstep (se 1 (by rfl) ⟨2777687, by rfl⟩ : syracuseStep 3703583 = 5555375) B5555375
theorem B12493939 : Blo 1733067 12493939 := bstep (se 1 (by rfl) ⟨9370454, by rfl⟩ : syracuseStep 12493939 = 18740909) B18740909
theorem B42747101 : Blo 1733067 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B33793483 : Blo 1733067 33793483 := bstep (se 1 (by rfl) ⟨25345112, by rfl⟩ : syracuseStep 33793483 = 50690225) B50690225
theorem B2926111 : Blo 1733067 2926111 := bstep (se 1 (by rfl) ⟨2194583, by rfl⟩ : syracuseStep 2926111 = 4389167) B4389167
theorem B8775377 : Blo 1733067 8775377 := bstep (se 2 (by rfl) ⟨3290766, by rfl⟩ : syracuseStep 8775377 = 6581533) B6581533
theorem B3901175 : Blo 1733067 3901175 := bstep (se 1 (by rfl) ⟨2925881, by rfl⟩ : syracuseStep 3901175 = 5851763) B5851763
theorem B4687607 : Blo 1733067 4687607 := bstep (se 1 (by rfl) ⟨3515705, by rfl⟩ : syracuseStep 4687607 = 7031411) B7031411
theorem B2779039 : Blo 1733067 2779039 := bstep (se 1 (by rfl) ⟨2084279, by rfl⟩ : syracuseStep 2779039 = 4168559) B4168559
theorem B3901355 : Blo 1733067 3901355 := bstep (se 1 (by rfl) ⟨2926016, by rfl⟩ : syracuseStep 3901355 = 5852033) B5852033
theorem B23717879 : Blo 1733067 23717879 := bstep (se 1 (by rfl) ⟨17788409, by rfl⟩ : syracuseStep 23717879 = 35576819) B35576819
theorem B5556271 : Blo 1733067 5556271 := bstep (se 1 (by rfl) ⟨4167203, by rfl⟩ : syracuseStep 5556271 = 8334407) B8334407
theorem B13166711 : Blo 1733067 13166711 := bstep (se 1 (by rfl) ⟨9875033, by rfl⟩ : syracuseStep 13166711 = 19750067) B19750067
theorem B1951951 : Blo 1733067 1951951 := bstep (se 1 (by rfl) ⟨1463963, by rfl⟩ : syracuseStep 1951951 = 2927927) B2927927
theorem B42174827 : Blo 1733067 42174827 := bstep (se 1 (by rfl) ⟨31631120, by rfl⟩ : syracuseStep 42174827 = 63262241) B63262241
theorem B130034051 : Blo 1733067 130034051 := bstep (se 1 (by rfl) ⟨97525538, by rfl⟩ : syracuseStep 130034051 = 195051077) B195051077
theorem B3901895 : Blo 1733067 3901895 := bstep (se 1 (by rfl) ⟨2926421, by rfl⟩ : syracuseStep 3901895 = 5852843) B5852843
theorem B4164263 : Blo 1733067 4164263 := bstep (se 1 (by rfl) ⟨3123197, by rfl⟩ : syracuseStep 4164263 = 6246395) B6246395
theorem B6581033 : Blo 1733067 6581033 := bstep (se 2 (by rfl) ⟨2467887, by rfl⟩ : syracuseStep 6581033 = 4935775) B4935775
theorem B3902255 : Blo 1733067 3902255 := bstep (se 1 (by rfl) ⟨2926691, by rfl⟩ : syracuseStep 3902255 = 5853383) B5853383
theorem B2599751 : Blo 1733067 2599751 := bstep (se 1 (by rfl) ⟨1949813, by rfl⟩ : syracuseStep 2599751 = 3899627) B3899627
theorem B8776673 : Blo 1733067 8776673 := bstep (se 2 (by rfl) ⟨3291252, by rfl⟩ : syracuseStep 8776673 = 6582505) B6582505
theorem B5557373 : Blo 1733067 5557373 := bstep (se 3 (by rfl) ⟨1042007, by rfl⟩ : syracuseStep 5557373 = 2084015) B2084015
theorem B3902777 : Blo 1733067 3902777 := bstep (se 2 (by rfl) ⟨1463541, by rfl⟩ : syracuseStep 3902777 = 2927083) B2927083
theorem B66030923 : Blo 1733067 66030923 := bstep (se 1 (by rfl) ⟨49523192, by rfl⟩ : syracuseStep 66030923 = 99046385) B99046385
theorem B2600351 : Blo 1733067 2600351 := bstep (se 1 (by rfl) ⟨1950263, by rfl⟩ : syracuseStep 2600351 = 3900527) B3900527
theorem B3903047 : Blo 1733067 3903047 := bstep (se 1 (by rfl) ⟨2927285, by rfl⟩ : syracuseStep 3903047 = 5854571) B5854571
theorem B2600615 : Blo 1733067 2600615 := bstep (se 1 (by rfl) ⟨1950461, by rfl⟩ : syracuseStep 2600615 = 3900923) B3900923
theorem B2600639 : Blo 1733067 2600639 := bstep (se 1 (by rfl) ⟨1950479, by rfl⟩ : syracuseStep 2600639 = 3900959) B3900959
theorem B3124927 : Blo 1733067 3124927 := bstep (se 1 (by rfl) ⟨2343695, by rfl⟩ : syracuseStep 3124927 = 4687391) B4687391
theorem B3903227 : Blo 1733067 3903227 := bstep (se 1 (by rfl) ⟨2927420, by rfl⟩ : syracuseStep 3903227 = 5854841) B5854841
theorem B2600735 : Blo 1733067 2600735 := bstep (se 1 (by rfl) ⟨1950551, by rfl⟩ : syracuseStep 2600735 = 3901103) B3901103
theorem B3903443 : Blo 1733067 3903443 := bstep (se 1 (by rfl) ⟨2927582, by rfl⟩ : syracuseStep 3903443 = 5855165) B5855165
theorem B11104289 : Blo 1733067 11104289 := bstep (se 2 (by rfl) ⟨4164108, by rfl⟩ : syracuseStep 11104289 = 8328217) B8328217
theorem B2601023 : Blo 1733067 2601023 := bstep (se 1 (by rfl) ⟨1950767, by rfl⟩ : syracuseStep 2601023 = 3901535) B3901535
theorem B6582491 : Blo 1733067 6582491 := bstep (se 1 (by rfl) ⟨4936868, by rfl⟩ : syracuseStep 6582491 = 9873737) B9873737
theorem B2535647 : Blo 1733067 2535647 := bstep (se 1 (by rfl) ⟨1901735, by rfl⟩ : syracuseStep 2535647 = 3803471) B3803471
theorem B3903713 : Blo 1733067 3903713 := bstep (se 2 (by rfl) ⟨1463892, by rfl⟩ : syracuseStep 3903713 = 2927785) B2927785
theorem B2601215 : Blo 1733067 2601215 := bstep (se 1 (by rfl) ⟨1950911, by rfl⟩ : syracuseStep 2601215 = 3901823) B3901823
theorem B2470171 : Blo 1733067 2470171 := bstep (se 1 (by rfl) ⟨1852628, by rfl⟩ : syracuseStep 2470171 = 3705257) B3705257
theorem B2601257 : Blo 1733067 2601257 := bstep (se 2 (by rfl) ⟨975471, by rfl⟩ : syracuseStep 2601257 = 1950943) B1950943
theorem B7410001 : Blo 1733067 7410001 := bstep (se 2 (by rfl) ⟨2778750, by rfl⟩ : syracuseStep 7410001 = 5557501) B5557501
theorem B33346079 : Blo 1733067 33346079 := bstep (se 1 (by rfl) ⟨25009559, by rfl⟩ : syracuseStep 33346079 = 50019119) B50019119
theorem B2601527 : Blo 1733067 2601527 := bstep (se 1 (by rfl) ⟨1951145, by rfl⟩ : syracuseStep 2601527 = 3902291) B3902291
theorem B4387385 : Blo 1733067 4387385 := bstep (se 2 (by rfl) ⟨1645269, by rfl⟩ : syracuseStep 4387385 = 3290539) B3290539
theorem B4936265 : Blo 1733067 4936265 := bstep (se 2 (by rfl) ⟨1851099, by rfl⟩ : syracuseStep 4936265 = 3702199) B3702199
theorem B4387547 : Blo 1733067 4387547 := bstep (se 1 (by rfl) ⟨3290660, by rfl⟩ : syracuseStep 4387547 = 6581321) B6581321
theorem B1733403 : Blo 1733067 1733403 := bstep (se 1 (by rfl) ⟨1300052, by rfl⟩ : syracuseStep 1733403 = 2600105) B2600105
theorem B2601767 : Blo 1733067 2601767 := bstep (se 1 (by rfl) ⟨1951325, by rfl⟩ : syracuseStep 2601767 = 3902651) B3902651
theorem B2601887 : Blo 1733067 2601887 := bstep (se 1 (by rfl) ⟨1951415, by rfl⟩ : syracuseStep 2601887 = 3902831) B3902831
theorem B1733679 : Blo 1733067 1733679 := bstep (se 1 (by rfl) ⟨1300259, by rfl⟩ : syracuseStep 1733679 = 2600519) B2600519
theorem B8893547 : Blo 1733067 8893547 := bstep (se 1 (by rfl) ⟨6670160, by rfl⟩ : syracuseStep 8893547 = 13340321) B13340321
theorem B1733799 : Blo 1733067 1733799 := bstep (se 1 (by rfl) ⟨1300349, by rfl⟩ : syracuseStep 1733799 = 2600699) B2600699
theorem B7410923 : Blo 1733067 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B12498295 : Blo 1733067 12498295 := bstep (se 1 (by rfl) ⟨9373721, by rfl⟩ : syracuseStep 12498295 = 18747443) B18747443
theorem B2602361 : Blo 1733067 2602361 := bstep (se 2 (by rfl) ⟨975885, by rfl⟩ : syracuseStep 2602361 = 1951771) B1951771
theorem B2602367 : Blo 1733067 2602367 := bstep (se 1 (by rfl) ⟨1951775, by rfl⟩ : syracuseStep 2602367 = 3903551) B3903551
theorem B3290615 : Blo 1733067 3290615 := bstep (se 1 (by rfl) ⟨2467961, by rfl⟩ : syracuseStep 3290615 = 4935923) B4935923
theorem B8902169 : Blo 1733067 8902169 := bstep (se 2 (by rfl) ⟨3338313, by rfl⟩ : syracuseStep 8902169 = 6676627) B6676627
theorem B2602523 : Blo 1733067 2602523 := bstep (se 1 (by rfl) ⟨1951892, by rfl⟩ : syracuseStep 2602523 = 3903785) B3903785
theorem B1734247 : Blo 1733067 1734247 := bstep (se 1 (by rfl) ⟨1300685, by rfl⟩ : syracuseStep 1734247 = 2601371) B2601371
theorem B4388489 : Blo 1733067 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B4388519 : Blo 1733067 4388519 := bstep (se 1 (by rfl) ⟨3291389, by rfl⟩ : syracuseStep 4388519 = 6582779) B6582779
theorem B4937449 : Blo 1733067 4937449 := bstep (se 2 (by rfl) ⟨1851543, by rfl⟩ : syracuseStep 4937449 = 3703087) B3703087
theorem B11106031 : Blo 1733067 11106031 := bstep (se 1 (by rfl) ⟨8329523, by rfl⟩ : syracuseStep 11106031 = 16659047) B16659047
theorem B28129007 : Blo 1733067 28129007 := bstep (se 1 (by rfl) ⟨21096755, by rfl⟩ : syracuseStep 28129007 = 42193511) B42193511
theorem B1734527 : Blo 1733067 1734527 := bstep (se 1 (by rfl) ⟨1300895, by rfl⟩ : syracuseStep 1734527 = 2601791) B2601791
theorem B1734623 : Blo 1733067 1734623 := bstep (se 1 (by rfl) ⟨1300967, by rfl⟩ : syracuseStep 1734623 = 2601935) B2601935
theorem B1734651 : Blo 1733067 1734651 := bstep (se 1 (by rfl) ⟨1300988, by rfl⟩ : syracuseStep 1734651 = 2601977) B2601977
theorem B1734683 : Blo 1733067 1734683 := bstep (se 1 (by rfl) ⟨1301012, by rfl⟩ : syracuseStep 1734683 = 2602025) B2602025
theorem B5855273 : Blo 1733067 5855273 := bstep (se 2 (by rfl) ⟨2195727, by rfl⟩ : syracuseStep 5855273 = 4391455) B4391455
theorem B1734703 : Blo 1733067 1734703 := bstep (se 1 (by rfl) ⟨1301027, by rfl⟩ : syracuseStep 1734703 = 2602055) B2602055
theorem B1734823 : Blo 1733067 1734823 := bstep (se 1 (by rfl) ⟨1301117, by rfl⟩ : syracuseStep 1734823 = 2602235) B2602235
theorem B4569655 : Blo 1733067 4569655 := bstep (se 1 (by rfl) ⟨3427241, by rfl⟩ : syracuseStep 4569655 = 6854483) B6854483
theorem B42171137 : Blo 1733067 42171137 := bstep (se 2 (by rfl) ⟨15814176, by rfl⟩ : syracuseStep 42171137 = 31628353) B31628353
theorem B22223747 : Blo 1733067 22223747 := bstep (se 1 (by rfl) ⟨16667810, by rfl⟩ : syracuseStep 22223747 = 33335621) B33335621
theorem B20061209 : Blo 1733067 20061209 := bstep (se 2 (by rfl) ⟨7522953, by rfl⟩ : syracuseStep 20061209 = 15045907) B15045907
theorem B2776169 : Blo 1733067 2776169 := bstep (se 2 (by rfl) ⟨1041063, by rfl⟩ : syracuseStep 2776169 = 2082127) B2082127
theorem B19004669 : Blo 1733067 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B44457335 : Blo 1733067 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B4390463 : Blo 1733067 4390463 := bstep (se 1 (by rfl) ⟨3292847, by rfl⟩ : syracuseStep 4390463 = 6585695) B6585695
theorem B9379799 : Blo 1733067 9379799 := bstep (se 1 (by rfl) ⟨7034849, by rfl⟩ : syracuseStep 9379799 = 14069699) B14069699
theorem B3899465 : Blo 1733067 3899465 := bstep (se 2 (by rfl) ⟨1462299, by rfl⟩ : syracuseStep 3899465 = 2924599) B2924599
theorem B3293311 : Blo 1733067 3293311 := bstep (se 1 (by rfl) ⟨2469983, by rfl⟩ : syracuseStep 3293311 = 4939967) B4939967
theorem B25002179 : Blo 1733067 25002179 := bstep (se 1 (by rfl) ⟨18751634, by rfl⟩ : syracuseStep 25002179 = 37503269) B37503269
theorem B7029011 : Blo 1733067 7029011 := bstep (se 1 (by rfl) ⟨5271758, by rfl⟩ : syracuseStep 7029011 = 10543517) B10543517
theorem B3293561 : Blo 1733067 3293561 := bstep (se 2 (by rfl) ⟨1235085, by rfl⟩ : syracuseStep 3293561 = 2470171) B2470171
theorem B2924923 : Blo 1733067 2924923 := bstep (se 1 (by rfl) ⟨2193692, by rfl⟩ : syracuseStep 2924923 = 4387385) B4387385
theorem B9880001 : Blo 1733067 9880001 := bstep (se 2 (by rfl) ⟨3705000, by rfl⟩ : syracuseStep 9880001 = 7410001) B7410001
theorem B3899879 : Blo 1733067 3899879 := bstep (se 1 (by rfl) ⟨2924909, by rfl⟩ : syracuseStep 3899879 = 5849819) B5849819
theorem B2925031 : Blo 1733067 2925031 := bstep (se 1 (by rfl) ⟨2193773, by rfl⟩ : syracuseStep 2925031 = 4387547) B4387547
theorem B4940615 : Blo 1733067 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B7406585 : Blo 1733067 7406585 := bstep (se 2 (by rfl) ⟨2777469, by rfl⟩ : syracuseStep 7406585 = 5554939) B5554939
theorem B2925659 : Blo 1733067 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B2925679 : Blo 1733067 2925679 := bstep (se 1 (by rfl) ⟨2194259, by rfl⟩ : syracuseStep 2925679 = 4388519) B4388519
theorem B5850251 : Blo 1733067 5850251 := bstep (se 1 (by rfl) ⟨4387688, by rfl⟩ : syracuseStep 5850251 = 8775377) B8775377
theorem B18752671 : Blo 1733067 18752671 := bstep (se 1 (by rfl) ⟨14064503, by rfl⟩ : syracuseStep 18752671 = 28129007) B28129007
theorem B15811919 : Blo 1733067 15811919 := bstep (se 1 (by rfl) ⟨11858939, by rfl⟩ : syracuseStep 15811919 = 23717879) B23717879
theorem B28116551 : Blo 1733067 28116551 := bstep (se 1 (by rfl) ⟨21087413, by rfl⟩ : syracuseStep 28116551 = 42174827) B42174827
theorem B86689367 : Blo 1733067 86689367 := bstep (se 1 (by rfl) ⟨65017025, by rfl⟩ : syracuseStep 86689367 = 130034051) B130034051
theorem B16664393 : Blo 1733067 16664393 := bstep (se 2 (by rfl) ⟨6249147, by rfl⟩ : syracuseStep 16664393 = 12498295) B12498295
theorem B45057977 : Blo 1733067 45057977 := bstep (se 2 (by rfl) ⟨16896741, by rfl⟩ : syracuseStep 45057977 = 33793483) B33793483
theorem B5851115 : Blo 1733067 5851115 := bstep (se 1 (by rfl) ⟨4388336, by rfl⟩ : syracuseStep 5851115 = 8776673) B8776673
theorem B3901481 : Blo 1733067 3901481 := bstep (se 2 (by rfl) ⟨1463055, by rfl⟩ : syracuseStep 3901481 = 2926111) B2926111
theorem B3704915 : Blo 1733067 3704915 := bstep (se 1 (by rfl) ⟨2778686, by rfl⟩ : syracuseStep 3704915 = 5557373) B5557373
theorem B14821541 : Blo 1733067 14821541 := bstep (se 4 (by rfl) ⟨1389519, by rfl⟩ : syracuseStep 14821541 = 2779039) B2779039
theorem B2926975 : Blo 1733067 2926975 := bstep (se 1 (by rfl) ⟨2195231, by rfl⟩ : syracuseStep 2926975 = 4390463) B4390463
theorem B6253199 : Blo 1733067 6253199 := bstep (se 1 (by rfl) ⟨4689899, by rfl⟩ : syracuseStep 6253199 = 9379799) B9379799
theorem B7408361 : Blo 1733067 7408361 := bstep (se 2 (by rfl) ⟨2778135, by rfl⟩ : syracuseStep 7408361 = 5556271) B5556271
theorem B53496557 : Blo 1733067 53496557 := bstep (se 3 (by rfl) ⟨10030604, by rfl⟩ : syracuseStep 53496557 = 20061209) B20061209
theorem B2599679 : Blo 1733067 2599679 := bstep (se 1 (by rfl) ⟨1949759, by rfl⟩ : syracuseStep 2599679 = 3899519) B3899519
theorem B2469055 : Blo 1733067 2469055 := bstep (se 1 (by rfl) ⟨1851791, by rfl⟩ : syracuseStep 2469055 = 3703583) B3703583
theorem B5934779 : Blo 1733067 5934779 := bstep (se 1 (by rfl) ⟨4451084, by rfl⟩ : syracuseStep 5934779 = 8902169) B8902169
theorem B2600783 : Blo 1733067 2600783 := bstep (se 1 (by rfl) ⟨1950587, by rfl⟩ : syracuseStep 2600783 = 3901175) B3901175
theorem B3125071 : Blo 1733067 3125071 := bstep (se 1 (by rfl) ⟨2343803, by rfl⟩ : syracuseStep 3125071 = 4687607) B4687607
theorem B2600903 : Blo 1733067 2600903 := bstep (se 1 (by rfl) ⟨1950677, by rfl⟩ : syracuseStep 2600903 = 3901355) B3901355
theorem B3903515 : Blo 1733067 3903515 := bstep (se 1 (by rfl) ⟨2927636, by rfl⟩ : syracuseStep 3903515 = 5855273) B5855273
theorem B8777807 : Blo 1733067 8777807 := bstep (se 1 (by rfl) ⟨6583355, by rfl⟩ : syracuseStep 8777807 = 13166711) B13166711
theorem B16658585 : Blo 1733067 16658585 := bstep (se 2 (by rfl) ⟨6246969, by rfl⟩ : syracuseStep 16658585 = 12493939) B12493939
theorem B2601263 : Blo 1733067 2601263 := bstep (se 1 (by rfl) ⟨1950947, by rfl⟩ : syracuseStep 2601263 = 3901895) B3901895
theorem B4387355 : Blo 1733067 4387355 := bstep (se 1 (by rfl) ⟨3290516, by rfl⟩ : syracuseStep 4387355 = 6581033) B6581033
theorem B2601503 : Blo 1733067 2601503 := bstep (se 1 (by rfl) ⟨1951127, by rfl⟩ : syracuseStep 2601503 = 3902255) B3902255
theorem B1733167 : Blo 1733067 1733167 := bstep (se 1 (by rfl) ⟨1299875, by rfl⟩ : syracuseStep 1733167 = 2599751) B2599751
theorem B14815831 : Blo 1733067 14815831 := bstep (se 1 (by rfl) ⟨11111873, by rfl⟩ : syracuseStep 14815831 = 22223747) B22223747
theorem B12669779 : Blo 1733067 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B2601851 : Blo 1733067 2601851 := bstep (se 1 (by rfl) ⟨1951388, by rfl⟩ : syracuseStep 2601851 = 3902777) B3902777
theorem B44020615 : Blo 1733067 44020615 := bstep (se 1 (by rfl) ⟨33015461, by rfl⟩ : syracuseStep 44020615 = 66030923) B66030923
theorem B4166569 : Blo 1733067 4166569 := bstep (se 2 (by rfl) ⟨1562463, by rfl⟩ : syracuseStep 4166569 = 3124927) B3124927
theorem B1733567 : Blo 1733067 1733567 := bstep (se 1 (by rfl) ⟨1300175, by rfl⟩ : syracuseStep 1733567 = 2600351) B2600351
theorem B6583265 : Blo 1733067 6583265 := bstep (se 2 (by rfl) ⟨2468724, by rfl⟩ : syracuseStep 6583265 = 4937449) B4937449
theorem B14808041 : Blo 1733067 14808041 := bstep (se 2 (by rfl) ⟨5553015, by rfl⟩ : syracuseStep 14808041 = 11106031) B11106031
theorem B27046901 : Blo 1733067 27046901 := bstep (se 5 (by rfl) ⟨1267823, by rfl⟩ : syracuseStep 27046901 = 2535647) B2535647
theorem B2602031 : Blo 1733067 2602031 := bstep (se 1 (by rfl) ⟨1951523, by rfl⟩ : syracuseStep 2602031 = 3903047) B3903047
theorem B1733743 : Blo 1733067 1733743 := bstep (se 1 (by rfl) ⟨1300307, by rfl⟩ : syracuseStep 1733743 = 2600615) B2600615
theorem B1733759 : Blo 1733067 1733759 := bstep (se 1 (by rfl) ⟨1300319, by rfl⟩ : syracuseStep 1733759 = 2600639) B2600639
theorem B2602151 : Blo 1733067 2602151 := bstep (se 1 (by rfl) ⟨1951613, by rfl⟩ : syracuseStep 2602151 = 3903227) B3903227
theorem B1733823 : Blo 1733067 1733823 := bstep (se 1 (by rfl) ⟨1300367, by rfl⟩ : syracuseStep 1733823 = 2600735) B2600735
theorem B2602295 : Blo 1733067 2602295 := bstep (se 1 (by rfl) ⟨1951721, by rfl⟩ : syracuseStep 2602295 = 3903443) B3903443
theorem B7402859 : Blo 1733067 7402859 := bstep (se 1 (by rfl) ⟨5552144, by rfl⟩ : syracuseStep 7402859 = 11104289) B11104289
theorem B1734015 : Blo 1733067 1734015 := bstep (se 1 (by rfl) ⟨1300511, by rfl⟩ : syracuseStep 1734015 = 2601023) B2601023
theorem B4388327 : Blo 1733067 4388327 := bstep (se 1 (by rfl) ⟨3291245, by rfl⟩ : syracuseStep 4388327 = 6582491) B6582491
theorem B2602475 : Blo 1733067 2602475 := bstep (se 1 (by rfl) ⟨1951856, by rfl⟩ : syracuseStep 2602475 = 3903713) B3903713
theorem B1734143 : Blo 1733067 1734143 := bstep (se 1 (by rfl) ⟨1300607, by rfl⟩ : syracuseStep 1734143 = 2601215) B2601215
theorem B1734171 : Blo 1733067 1734171 := bstep (se 1 (by rfl) ⟨1300628, by rfl⟩ : syracuseStep 1734171 = 2601257) B2601257
theorem B2602601 : Blo 1733067 2602601 := bstep (se 2 (by rfl) ⟨975975, by rfl⟩ : syracuseStep 2602601 = 1951951) B1951951
theorem B8328815 : Blo 1733067 8328815 := bstep (se 1 (by rfl) ⟨6246611, by rfl⟩ : syracuseStep 8328815 = 12493223) B12493223
theorem B22230719 : Blo 1733067 22230719 := bstep (se 1 (by rfl) ⟨16673039, by rfl⟩ : syracuseStep 22230719 = 33346079) B33346079
theorem B1734351 : Blo 1733067 1734351 := bstep (se 1 (by rfl) ⟨1300763, by rfl⟩ : syracuseStep 1734351 = 2601527) B2601527
theorem B3290843 : Blo 1733067 3290843 := bstep (se 1 (by rfl) ⟨2468132, by rfl⟩ : syracuseStep 3290843 = 4936265) B4936265
theorem B1734511 : Blo 1733067 1734511 := bstep (se 1 (by rfl) ⟨1300883, by rfl⟩ : syracuseStep 1734511 = 2601767) B2601767
theorem B1734591 : Blo 1733067 1734591 := bstep (se 1 (by rfl) ⟨1300943, by rfl⟩ : syracuseStep 1734591 = 2601887) B2601887
theorem B5929031 : Blo 1733067 5929031 := bstep (se 1 (by rfl) ⟨4446773, by rfl⟩ : syracuseStep 5929031 = 8893547) B8893547
theorem B6092873 : Blo 1733067 6092873 := bstep (se 2 (by rfl) ⟨2284827, by rfl⟩ : syracuseStep 6092873 = 4569655) B4569655
theorem B28498067 : Blo 1733067 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B1734907 : Blo 1733067 1734907 := bstep (se 1 (by rfl) ⟨1301180, by rfl⟩ : syracuseStep 1734907 = 2602361) B2602361
theorem B1734911 : Blo 1733067 1734911 := bstep (se 1 (by rfl) ⟨1301183, by rfl⟩ : syracuseStep 1734911 = 2602367) B2602367
theorem B2193743 : Blo 1733067 2193743 := bstep (se 1 (by rfl) ⟨1645307, by rfl⟩ : syracuseStep 2193743 = 3290615) B3290615
theorem B1735015 : Blo 1733067 1735015 := bstep (se 1 (by rfl) ⟨1301261, by rfl⟩ : syracuseStep 1735015 = 2602523) B2602523
theorem B2776175 : Blo 1733067 2776175 := bstep (se 1 (by rfl) ⟨2082131, by rfl⟩ : syracuseStep 2776175 = 4164263) B4164263
theorem B28114091 : Blo 1733067 28114091 := bstep (se 1 (by rfl) ⟨21085568, by rfl⟩ : syracuseStep 28114091 = 42171137) B42171137
theorem B1850779 : Blo 1733067 1850779 := bstep (se 1 (by rfl) ⟨1388084, by rfl⟩ : syracuseStep 1850779 = 2776169) B2776169
theorem B29638223 : Blo 1733067 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B4391081 : Blo 1733067 4391081 := bstep (se 2 (by rfl) ⟨1646655, by rfl⟩ : syracuseStep 4391081 = 3293311) B3293311
theorem B4686007 : Blo 1733067 4686007 := bstep (se 1 (by rfl) ⟨3514505, by rfl⟩ : syracuseStep 4686007 = 7029011) B7029011
theorem B6586667 : Blo 1733067 6586667 := bstep (se 1 (by rfl) ⟨4940000, by rfl⟩ : syracuseStep 6586667 = 9880001) B9880001
theorem B2924903 : Blo 1733067 2924903 := bstep (se 1 (by rfl) ⟨2193677, by rfl⟩ : syracuseStep 2924903 = 4387355) B4387355
theorem B3899897 : Blo 1733067 3899897 := bstep (se 2 (by rfl) ⟨1462461, by rfl⟩ : syracuseStep 3899897 = 2924923) B2924923
theorem B8446519 : Blo 1733067 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B3900041 : Blo 1733067 3900041 := bstep (se 2 (by rfl) ⟨1462515, by rfl⟩ : syracuseStep 3900041 = 2925031) B2925031
theorem B9872027 : Blo 1733067 9872027 := bstep (se 1 (by rfl) ⟨7404020, by rfl⟩ : syracuseStep 9872027 = 14808041) B14808041
theorem B18031267 : Blo 1733067 18031267 := bstep (se 1 (by rfl) ⟨13523450, by rfl⟩ : syracuseStep 18031267 = 27046901) B27046901
theorem B1950439 : Blo 1733067 1950439 := bstep (se 1 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 1950439 = 2925659) B2925659
theorem B3900167 : Blo 1733067 3900167 := bstep (se 1 (by rfl) ⟨2925125, by rfl⟩ : syracuseStep 3900167 = 5850251) B5850251
theorem B5849981 : Blo 1733067 5849981 := bstep (se 3 (by rfl) ⟨1096871, by rfl⟩ : syracuseStep 5849981 = 2193743) B2193743
theorem B8782829 : Blo 1733067 8782829 := bstep (se 3 (by rfl) ⟨1646780, by rfl⟩ : syracuseStep 8782829 = 3293561) B3293561
theorem B2925551 : Blo 1733067 2925551 := bstep (se 1 (by rfl) ⟨2194163, by rfl⟩ : syracuseStep 2925551 = 4388327) B4388327
theorem B18744367 : Blo 1733067 18744367 := bstep (se 1 (by rfl) ⟨14058275, by rfl⟩ : syracuseStep 18744367 = 28116551) B28116551
theorem B14820479 : Blo 1733067 14820479 := bstep (se 1 (by rfl) ⟨11115359, by rfl⟩ : syracuseStep 14820479 = 22230719) B22230719
theorem B11109595 : Blo 1733067 11109595 := bstep (se 1 (by rfl) ⟨8332196, by rfl⟩ : syracuseStep 11109595 = 16664393) B16664393
theorem B5555425 : Blo 1733067 5555425 := bstep (se 2 (by rfl) ⟨2083284, by rfl⟩ : syracuseStep 5555425 = 4166569) B4166569
theorem B3900743 : Blo 1733067 3900743 := bstep (se 1 (by rfl) ⟨2925557, by rfl⟩ : syracuseStep 3900743 = 5851115) B5851115
theorem B18998711 : Blo 1733067 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B9881027 : Blo 1733067 9881027 := bstep (se 1 (by rfl) ⟨7410770, by rfl⟩ : syracuseStep 9881027 = 14821541) B14821541
theorem B3900905 : Blo 1733067 3900905 := bstep (se 2 (by rfl) ⟨1462839, by rfl⟩ : syracuseStep 3900905 = 2925679) B2925679
theorem B25003561 : Blo 1733067 25003561 := bstep (se 2 (by rfl) ⟨9376335, by rfl⟩ : syracuseStep 25003561 = 18752671) B18752671
theorem B13174973 : Blo 1733067 13174973 := bstep (se 3 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 13174973 = 4940615) B4940615
theorem B2599643 : Blo 1733067 2599643 := bstep (se 1 (by rfl) ⟨1949732, by rfl⟩ : syracuseStep 2599643 = 3899465) B3899465
theorem B5851871 : Blo 1733067 5851871 := bstep (se 1 (by rfl) ⟨4388903, by rfl⟩ : syracuseStep 5851871 = 8777807) B8777807
theorem B2599919 : Blo 1733067 2599919 := bstep (se 1 (by rfl) ⟨1949939, by rfl⟩ : syracuseStep 2599919 = 3899879) B3899879
theorem B3902633 : Blo 1733067 3902633 := bstep (se 2 (by rfl) ⟨1463487, by rfl⟩ : syracuseStep 3902633 = 2926975) B2926975
theorem B19754441 : Blo 1733067 19754441 := bstep (se 2 (by rfl) ⟨7407915, by rfl⟩ : syracuseStep 19754441 = 14815831) B14815831
theorem B4935239 : Blo 1733067 4935239 := bstep (se 1 (by rfl) ⟨3701429, by rfl⟩ : syracuseStep 4935239 = 7402859) B7402859
theorem B2600987 : Blo 1733067 2600987 := bstep (se 1 (by rfl) ⟨1950740, by rfl⟩ : syracuseStep 2600987 = 3901481) B3901481
theorem B3952687 : Blo 1733067 3952687 := bstep (se 1 (by rfl) ⟨2964515, by rfl⟩ : syracuseStep 3952687 = 5929031) B5929031
theorem B2469943 : Blo 1733067 2469943 := bstep (se 1 (by rfl) ⟨1852457, by rfl⟩ : syracuseStep 2469943 = 3704915) B3704915
theorem B16667045 : Blo 1733067 16667045 := bstep (se 4 (by rfl) ⟨1562535, by rfl⟩ : syracuseStep 16667045 = 3125071) B3125071
theorem B35664371 : Blo 1733067 35664371 := bstep (se 1 (by rfl) ⟨26748278, by rfl⟩ : syracuseStep 35664371 = 53496557) B53496557
theorem B1733119 : Blo 1733067 1733119 := bstep (se 1 (by rfl) ⟨1299839, by rfl⟩ : syracuseStep 1733119 = 2599679) B2599679
theorem B1733855 : Blo 1733067 1733855 := bstep (se 1 (by rfl) ⟨1300391, by rfl⟩ : syracuseStep 1733855 = 2600783) B2600783
theorem B1733935 : Blo 1733067 1733935 := bstep (se 1 (by rfl) ⟨1300451, by rfl⟩ : syracuseStep 1733935 = 2600903) B2600903
theorem B2602343 : Blo 1733067 2602343 := bstep (se 1 (by rfl) ⟨1951757, by rfl⟩ : syracuseStep 2602343 = 3903515) B3903515
theorem B11105723 : Blo 1733067 11105723 := bstep (se 1 (by rfl) ⟨8329292, by rfl⟩ : syracuseStep 11105723 = 16658585) B16658585
theorem B16668119 : Blo 1733067 16668119 := bstep (se 1 (by rfl) ⟨12501089, by rfl⟩ : syracuseStep 16668119 = 25002179) B25002179
theorem B1734175 : Blo 1733067 1734175 := bstep (se 1 (by rfl) ⟨1300631, by rfl⟩ : syracuseStep 1734175 = 2601263) B2601263
theorem B1734335 : Blo 1733067 1734335 := bstep (se 1 (by rfl) ⟨1300751, by rfl⟩ : syracuseStep 1734335 = 2601503) B2601503
theorem B1734567 : Blo 1733067 1734567 := bstep (se 1 (by rfl) ⟨1300925, by rfl⟩ : syracuseStep 1734567 = 2601851) B2601851
theorem B4388843 : Blo 1733067 4388843 := bstep (se 1 (by rfl) ⟨3291632, by rfl⟩ : syracuseStep 4388843 = 6583265) B6583265
theorem B4937723 : Blo 1733067 4937723 := bstep (se 1 (by rfl) ⟨3703292, by rfl⟩ : syracuseStep 4937723 = 7406585) B7406585
theorem B1734687 : Blo 1733067 1734687 := bstep (se 1 (by rfl) ⟨1301015, by rfl⟩ : syracuseStep 1734687 = 2602031) B2602031
theorem B1734767 : Blo 1733067 1734767 := bstep (se 1 (by rfl) ⟨1301075, by rfl⟩ : syracuseStep 1734767 = 2602151) B2602151
theorem B1734863 : Blo 1733067 1734863 := bstep (se 1 (by rfl) ⟨1301147, by rfl⟩ : syracuseStep 1734863 = 2602295) B2602295
theorem B10541279 : Blo 1733067 10541279 := bstep (se 1 (by rfl) ⟨7905959, by rfl⟩ : syracuseStep 10541279 = 15811919) B15811919
theorem B1734983 : Blo 1733067 1734983 := bstep (se 1 (by rfl) ⟨1301237, by rfl⟩ : syracuseStep 1734983 = 2602475) B2602475
theorem B57792911 : Blo 1733067 57792911 := bstep (se 1 (by rfl) ⟨43344683, by rfl⟩ : syracuseStep 57792911 = 86689367) B86689367
theorem B1735067 : Blo 1733067 1735067 := bstep (se 1 (by rfl) ⟨1301300, by rfl⟩ : syracuseStep 1735067 = 2602601) B2602601
theorem B5552543 : Blo 1733067 5552543 := bstep (se 1 (by rfl) ⟨4164407, by rfl⟩ : syracuseStep 5552543 = 8328815) B8328815
theorem B2193895 : Blo 1733067 2193895 := bstep (se 1 (by rfl) ⟨1645421, by rfl⟩ : syracuseStep 2193895 = 3290843) B3290843
theorem B58694153 : Blo 1733067 58694153 := bstep (se 2 (by rfl) ⟨22010307, by rfl⟩ : syracuseStep 58694153 = 44020615) B44020615
theorem B30038651 : Blo 1733067 30038651 := bstep (se 1 (by rfl) ⟨22528988, by rfl⟩ : syracuseStep 30038651 = 45057977) B45057977
theorem B4061915 : Blo 1733067 4061915 := bstep (se 1 (by rfl) ⟨3046436, by rfl⟩ : syracuseStep 4061915 = 6092873) B6092873
theorem B3292073 : Blo 1733067 3292073 := bstep (se 2 (by rfl) ⟨1234527, by rfl⟩ : syracuseStep 3292073 = 2469055) B2469055
theorem B4168799 : Blo 1733067 4168799 := bstep (se 1 (by rfl) ⟨3126599, by rfl⟩ : syracuseStep 4168799 = 6253199) B6253199
theorem B4938907 : Blo 1733067 4938907 := bstep (se 1 (by rfl) ⟨3704180, by rfl⟩ : syracuseStep 4938907 = 7408361) B7408361
theorem B1850783 : Blo 1733067 1850783 := bstep (se 1 (by rfl) ⟨1388087, by rfl⟩ : syracuseStep 1850783 = 2776175) B2776175
theorem B18742727 : Blo 1733067 18742727 := bstep (se 1 (by rfl) ⟨14057045, by rfl⟩ : syracuseStep 18742727 = 28114091) B28114091
theorem B9870821 : Blo 1733067 9870821 := bstep (se 4 (by rfl) ⟨925389, by rfl⟩ : syracuseStep 9870821 = 1850779) B1850779
theorem B19758815 : Blo 1733067 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B3956519 : Blo 1733067 3956519 := bstep (se 1 (by rfl) ⟨2967389, by rfl⟩ : syracuseStep 3956519 = 5934779) B5934779
theorem B4391111 : Blo 1733067 4391111 := bstep (se 1 (by rfl) ⟨3293333, by rfl⟩ : syracuseStep 4391111 = 6586667) B6586667
theorem B1949935 : Blo 1733067 1949935 := bstep (se 1 (by rfl) ⟨1462451, by rfl⟩ : syracuseStep 1949935 = 2924903) B2924903
theorem B13173029 : Blo 1733067 13173029 := bstep (se 4 (by rfl) ⟨1234971, by rfl⟩ : syracuseStep 13173029 = 2469943) B2469943
theorem B3899987 : Blo 1733067 3899987 := bstep (se 1 (by rfl) ⟨2924990, by rfl⟩ : syracuseStep 3899987 = 5849981) B5849981
theorem B2925193 : Blo 1733067 2925193 := bstep (se 2 (by rfl) ⟨1096947, by rfl⟩ : syracuseStep 2925193 = 2193895) B2193895
theorem B1950367 : Blo 1733067 1950367 := bstep (se 1 (by rfl) ⟨1462775, by rfl⟩ : syracuseStep 1950367 = 2925551) B2925551
theorem B9880319 : Blo 1733067 9880319 := bstep (se 1 (by rfl) ⟨7410239, by rfl⟩ : syracuseStep 9880319 = 14820479) B14820479
theorem B96166757 : Blo 1733067 96166757 := bstep (se 4 (by rfl) ⟨9015633, by rfl⟩ : syracuseStep 96166757 = 18031267) B18031267
theorem B12665807 : Blo 1733067 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B6587351 : Blo 1733067 6587351 := bstep (se 1 (by rfl) ⟨4940513, by rfl⟩ : syracuseStep 6587351 = 9881027) B9881027
theorem B2925895 : Blo 1733067 2925895 := bstep (se 1 (by rfl) ⟨2194421, by rfl⟩ : syracuseStep 2925895 = 4388843) B4388843
theorem B156517741 : Blo 1733067 156517741 := bstep (se 3 (by rfl) ⟨29347076, by rfl⟩ : syracuseStep 156517741 = 58694153) B58694153
theorem B8783315 : Blo 1733067 8783315 := bstep (se 1 (by rfl) ⟨6587486, by rfl⟩ : syracuseStep 8783315 = 13174973) B13174973
theorem B14812793 : Blo 1733067 14812793 := bstep (se 2 (by rfl) ⟨5554797, by rfl⟩ : syracuseStep 14812793 = 11109595) B11109595
theorem B7407233 : Blo 1733067 7407233 := bstep (se 2 (by rfl) ⟨2777712, by rfl⟩ : syracuseStep 7407233 = 5555425) B5555425
theorem B3901247 : Blo 1733067 3901247 := bstep (se 1 (by rfl) ⟨2925935, by rfl⟩ : syracuseStep 3901247 = 5851871) B5851871
theorem B2779199 : Blo 1733067 2779199 := bstep (se 1 (by rfl) ⟨2084399, by rfl⟩ : syracuseStep 2779199 = 4168799) B4168799
theorem B12495151 : Blo 1733067 12495151 := bstep (se 1 (by rfl) ⟨9371363, by rfl⟩ : syracuseStep 12495151 = 18742727) B18742727
theorem B6580547 : Blo 1733067 6580547 := bstep (se 1 (by rfl) ⟨4935410, by rfl⟩ : syracuseStep 6580547 = 9870821) B9870821
theorem B5270249 : Blo 1733067 5270249 := bstep (se 2 (by rfl) ⟨1976343, by rfl⟩ : syracuseStep 5270249 = 3952687) B3952687
theorem B2927387 : Blo 1733067 2927387 := bstep (se 1 (by rfl) ⟨2195540, by rfl⟩ : syracuseStep 2927387 = 4391081) B4391081
theorem B11111363 : Blo 1733067 11111363 := bstep (se 1 (by rfl) ⟨8333522, by rfl⟩ : syracuseStep 11111363 = 16667045) B16667045
theorem B23776247 : Blo 1733067 23776247 := bstep (se 1 (by rfl) ⟨17832185, by rfl⟩ : syracuseStep 23776247 = 35664371) B35664371
theorem B2599931 : Blo 1733067 2599931 := bstep (se 1 (by rfl) ⟨1949948, by rfl⟩ : syracuseStep 2599931 = 3899897) B3899897
theorem B2600027 : Blo 1733067 2600027 := bstep (se 1 (by rfl) ⟨1950020, by rfl⟩ : syracuseStep 2600027 = 3900041) B3900041
theorem B6581351 : Blo 1733067 6581351 := bstep (se 1 (by rfl) ⟨4936013, by rfl⟩ : syracuseStep 6581351 = 9872027) B9872027
theorem B2600111 : Blo 1733067 2600111 := bstep (se 1 (by rfl) ⟨1950083, by rfl⟩ : syracuseStep 2600111 = 3900167) B3900167
theorem B2600495 : Blo 1733067 2600495 := bstep (se 1 (by rfl) ⟨1950371, by rfl⟩ : syracuseStep 2600495 = 3900743) B3900743
theorem B2600585 : Blo 1733067 2600585 := bstep (se 2 (by rfl) ⟨975219, by rfl⟩ : syracuseStep 2600585 = 1950439) B1950439
theorem B11112079 : Blo 1733067 11112079 := bstep (se 1 (by rfl) ⟨8334059, by rfl⟩ : syracuseStep 11112079 = 16668119) B16668119
theorem B2600603 : Blo 1733067 2600603 := bstep (se 1 (by rfl) ⟨1950452, by rfl⟩ : syracuseStep 2600603 = 3900905) B3900905
theorem B4935421 : Blo 1733067 4935421 := bstep (se 3 (by rfl) ⟨925391, by rfl⟩ : syracuseStep 4935421 = 1850783) B1850783
theorem B20025767 : Blo 1733067 20025767 := bstep (se 1 (by rfl) ⟨15019325, by rfl⟩ : syracuseStep 20025767 = 30038651) B30038651
theorem B1733095 : Blo 1733067 1733095 := bstep (se 1 (by rfl) ⟨1299821, by rfl⟩ : syracuseStep 1733095 = 2599643) B2599643
theorem B2707943 : Blo 1733067 2707943 := bstep (se 1 (by rfl) ⟨2030957, by rfl⟩ : syracuseStep 2707943 = 4061915) B4061915
theorem B1733279 : Blo 1733067 1733279 := bstep (se 1 (by rfl) ⟨1299959, by rfl⟩ : syracuseStep 1733279 = 2599919) B2599919
theorem B33338081 : Blo 1733067 33338081 := bstep (se 2 (by rfl) ⟨12501780, by rfl⟩ : syracuseStep 33338081 = 25003561) B25003561
theorem B2601755 : Blo 1733067 2601755 := bstep (se 1 (by rfl) ⟨1951316, by rfl⟩ : syracuseStep 2601755 = 3902633) B3902633
theorem B13169627 : Blo 1733067 13169627 := bstep (se 1 (by rfl) ⟨9877220, by rfl⟩ : syracuseStep 13169627 = 19754441) B19754441
theorem B3290159 : Blo 1733067 3290159 := bstep (se 1 (by rfl) ⟨2467619, by rfl⟩ : syracuseStep 3290159 = 4935239) B4935239
theorem B1733991 : Blo 1733067 1733991 := bstep (se 1 (by rfl) ⟨1300493, by rfl⟩ : syracuseStep 1733991 = 2600987) B2600987
theorem B6248009 : Blo 1733067 6248009 := bstep (se 2 (by rfl) ⟨2343003, by rfl⟩ : syracuseStep 6248009 = 4686007) B4686007
theorem B5855219 : Blo 1733067 5855219 := bstep (se 1 (by rfl) ⟨4391414, by rfl⟩ : syracuseStep 5855219 = 8782829) B8782829
theorem B11262025 : Blo 1733067 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B1734895 : Blo 1733067 1734895 := bstep (se 1 (by rfl) ⟨1301171, by rfl⟩ : syracuseStep 1734895 = 2602343) B2602343
theorem B7403815 : Blo 1733067 7403815 := bstep (se 1 (by rfl) ⟨5552861, by rfl⟩ : syracuseStep 7403815 = 11105723) B11105723
theorem B154114429 : Blo 1733067 154114429 := bstep (se 3 (by rfl) ⟨28896455, by rfl⟩ : syracuseStep 154114429 = 57792911) B57792911
theorem B3291815 : Blo 1733067 3291815 := bstep (se 1 (by rfl) ⟨2468861, by rfl⟩ : syracuseStep 3291815 = 4937723) B4937723
theorem B24992489 : Blo 1733067 24992489 := bstep (se 2 (by rfl) ⟨9372183, by rfl⟩ : syracuseStep 24992489 = 18744367) B18744367
theorem B7027519 : Blo 1733067 7027519 := bstep (se 1 (by rfl) ⟨5270639, by rfl⟩ : syracuseStep 7027519 = 10541279) B10541279
theorem B6585209 : Blo 1733067 6585209 := bstep (se 2 (by rfl) ⟨2469453, by rfl⟩ : syracuseStep 6585209 = 4938907) B4938907
theorem B3701695 : Blo 1733067 3701695 := bstep (se 1 (by rfl) ⟨2776271, by rfl⟩ : syracuseStep 3701695 = 5552543) B5552543
theorem B2194715 : Blo 1733067 2194715 := bstep (se 1 (by rfl) ⟨1646036, by rfl⟩ : syracuseStep 2194715 = 3292073) B3292073
theorem B13172543 : Blo 1733067 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B2637679 : Blo 1733067 2637679 := bstep (se 1 (by rfl) ⟨1978259, by rfl⟩ : syracuseStep 2637679 = 3956519) B3956519
theorem B15016033 : Blo 1733067 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B8773757 : Blo 1733067 8773757 := bstep (se 3 (by rfl) ⟨1645079, by rfl⟩ : syracuseStep 8773757 = 3290159) B3290159
theorem B8782019 : Blo 1733067 8782019 := bstep (se 1 (by rfl) ⟨6586514, by rfl⟩ : syracuseStep 8782019 = 13173029) B13173029
theorem B9871753 : Blo 1733067 9871753 := bstep (se 2 (by rfl) ⟨3701907, by rfl⟩ : syracuseStep 9871753 = 7403815) B7403815
theorem B22225387 : Blo 1733067 22225387 := bstep (se 1 (by rfl) ⟨16669040, by rfl⟩ : syracuseStep 22225387 = 33338081) B33338081
theorem B6586879 : Blo 1733067 6586879 := bstep (se 1 (by rfl) ⟨4940159, by rfl⟩ : syracuseStep 6586879 = 9880319) B9880319
theorem B64111171 : Blo 1733067 64111171 := bstep (se 1 (by rfl) ⟨48083378, by rfl⟩ : syracuseStep 64111171 = 96166757) B96166757
theorem B4391567 : Blo 1733067 4391567 := bstep (se 1 (by rfl) ⟨3293675, by rfl⟩ : syracuseStep 4391567 = 6587351) B6587351
theorem B3900257 : Blo 1733067 3900257 := bstep (se 2 (by rfl) ⟨1462596, by rfl⟩ : syracuseStep 3900257 = 2925193) B2925193
theorem B1852799 : Blo 1733067 1852799 := bstep (se 1 (by rfl) ⟨1389599, by rfl⟩ : syracuseStep 1852799 = 2779199) B2779199
theorem B3901193 : Blo 1733067 3901193 := bstep (se 2 (by rfl) ⟨1462947, by rfl⟩ : syracuseStep 3901193 = 2925895) B2925895
theorem B1951591 : Blo 1733067 1951591 := bstep (se 1 (by rfl) ⟨1463693, by rfl⟩ : syracuseStep 1951591 = 2927387) B2927387
theorem B7407575 : Blo 1733067 7407575 := bstep (se 1 (by rfl) ⟨5555681, by rfl⟩ : syracuseStep 7407575 = 11111363) B11111363
theorem B6580561 : Blo 1733067 6580561 := bstep (se 2 (by rfl) ⟨2467710, by rfl⟩ : syracuseStep 6580561 = 4935421) B4935421
theorem B3516905 : Blo 1733067 3516905 := bstep (se 2 (by rfl) ⟨1318839, by rfl⟩ : syracuseStep 3516905 = 2637679) B2637679
theorem B2927407 : Blo 1733067 2927407 := bstep (se 1 (by rfl) ⟨2195555, by rfl⟩ : syracuseStep 2927407 = 4391111) B4391111
theorem B2599913 : Blo 1733067 2599913 := bstep (se 2 (by rfl) ⟨974967, by rfl⟩ : syracuseStep 2599913 = 1949935) B1949935
theorem B2599991 : Blo 1733067 2599991 := bstep (se 1 (by rfl) ⟨1949993, by rfl⟩ : syracuseStep 2599991 = 3899987) B3899987
theorem B5852573 : Blo 1733067 5852573 := bstep (se 3 (by rfl) ⟨1097357, by rfl⟩ : syracuseStep 5852573 = 2194715) B2194715
theorem B2600489 : Blo 1733067 2600489 := bstep (se 2 (by rfl) ⟨975183, by rfl⟩ : syracuseStep 2600489 = 1950367) B1950367
theorem B4165339 : Blo 1733067 4165339 := bstep (se 1 (by rfl) ⟨3124004, by rfl⟩ : syracuseStep 4165339 = 6248009) B6248009
theorem B9875195 : Blo 1733067 9875195 := bstep (se 1 (by rfl) ⟨7406396, by rfl⟩ : syracuseStep 9875195 = 14812793) B14812793
theorem B2600831 : Blo 1733067 2600831 := bstep (se 1 (by rfl) ⟨1950623, by rfl⟩ : syracuseStep 2600831 = 3901247) B3901247
theorem B4935593 : Blo 1733067 4935593 := bstep (se 2 (by rfl) ⟨1850847, by rfl⟩ : syracuseStep 4935593 = 3701695) B3701695
theorem B3903479 : Blo 1733067 3903479 := bstep (se 1 (by rfl) ⟨2927609, by rfl⟩ : syracuseStep 3903479 = 5855219) B5855219
theorem B4387031 : Blo 1733067 4387031 := bstep (se 1 (by rfl) ⟨3290273, by rfl⟩ : syracuseStep 4387031 = 6580547) B6580547
theorem B66646637 : Blo 1733067 66646637 := bstep (se 3 (by rfl) ⟨12496244, by rfl⟩ : syracuseStep 66646637 = 24992489) B24992489
theorem B1733287 : Blo 1733067 1733287 := bstep (se 1 (by rfl) ⟨1299965, by rfl⟩ : syracuseStep 1733287 = 2599931) B2599931
theorem B1733351 : Blo 1733067 1733351 := bstep (se 1 (by rfl) ⟨1300013, by rfl⟩ : syracuseStep 1733351 = 2600027) B2600027
theorem B4387567 : Blo 1733067 4387567 := bstep (se 1 (by rfl) ⟨3290675, by rfl⟩ : syracuseStep 4387567 = 6581351) B6581351
theorem B1733407 : Blo 1733067 1733407 := bstep (se 1 (by rfl) ⟨1300055, by rfl⟩ : syracuseStep 1733407 = 2600111) B2600111
theorem B14816105 : Blo 1733067 14816105 := bstep (se 2 (by rfl) ⟨5556039, by rfl⟩ : syracuseStep 14816105 = 11112079) B11112079
theorem B1733663 : Blo 1733067 1733663 := bstep (se 1 (by rfl) ⟨1300247, by rfl⟩ : syracuseStep 1733663 = 2600495) B2600495
theorem B1733723 : Blo 1733067 1733723 := bstep (se 1 (by rfl) ⟨1300292, by rfl⟩ : syracuseStep 1733723 = 2600585) B2600585
theorem B1733735 : Blo 1733067 1733735 := bstep (se 1 (by rfl) ⟨1300301, by rfl⟩ : syracuseStep 1733735 = 2600603) B2600603
theorem B13350511 : Blo 1733067 13350511 := bstep (se 1 (by rfl) ⟨10012883, by rfl⟩ : syracuseStep 13350511 = 20025767) B20025767
theorem B16660201 : Blo 1733067 16660201 := bstep (se 2 (by rfl) ⟨6247575, by rfl⟩ : syracuseStep 16660201 = 12495151) B12495151
theorem B205485905 : Blo 1733067 205485905 := bstep (se 2 (by rfl) ⟨77057214, by rfl⟩ : syracuseStep 205485905 = 154114429) B154114429
theorem B1734503 : Blo 1733067 1734503 := bstep (se 1 (by rfl) ⟨1300877, by rfl⟩ : syracuseStep 1734503 = 2601755) B2601755
theorem B8443871 : Blo 1733067 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B8779751 : Blo 1733067 8779751 := bstep (se 1 (by rfl) ⟨6584813, by rfl⟩ : syracuseStep 8779751 = 13169627) B13169627
theorem B5855543 : Blo 1733067 5855543 := bstep (se 1 (by rfl) ⟨4391657, by rfl⟩ : syracuseStep 5855543 = 8783315) B8783315
theorem B9370025 : Blo 1733067 9370025 := bstep (se 2 (by rfl) ⟨3513759, by rfl⟩ : syracuseStep 9370025 = 7027519) B7027519
theorem B4938155 : Blo 1733067 4938155 := bstep (se 1 (by rfl) ⟨3703616, by rfl⟩ : syracuseStep 4938155 = 7407233) B7407233
theorem B2194543 : Blo 1733067 2194543 := bstep (se 1 (by rfl) ⟨1645907, by rfl⟩ : syracuseStep 2194543 = 3291815) B3291815
theorem B208690321 : Blo 1733067 208690321 := bstep (se 2 (by rfl) ⟨78258870, by rfl⟩ : syracuseStep 208690321 = 156517741) B156517741
theorem B3513499 : Blo 1733067 3513499 := bstep (se 1 (by rfl) ⟨2635124, by rfl⟩ : syracuseStep 3513499 = 5270249) B5270249
theorem B4390139 : Blo 1733067 4390139 := bstep (se 1 (by rfl) ⟨3292604, by rfl⟩ : syracuseStep 4390139 = 6585209) B6585209
theorem B15850831 : Blo 1733067 15850831 := bstep (se 1 (by rfl) ⟨11888123, by rfl⟩ : syracuseStep 15850831 = 23776247) B23776247
theorem B28884725 : Blo 1733067 28884725 := bstep (se 5 (by rfl) ⟨1353971, by rfl⟩ : syracuseStep 28884725 = 2707943) B2707943
theorem B8781695 : Blo 1733067 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B5849171 : Blo 1733067 5849171 := bstep (se 1 (by rfl) ⟨4386878, by rfl⟩ : syracuseStep 5849171 = 8773757) B8773757
theorem B20021377 : Blo 1733067 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B2924687 : Blo 1733067 2924687 := bstep (se 1 (by rfl) ⟨2193515, by rfl⟩ : syracuseStep 2924687 = 4387031) B4387031
theorem B8774081 : Blo 1733067 8774081 := bstep (se 2 (by rfl) ⟨3290280, by rfl⟩ : syracuseStep 8774081 = 6580561) B6580561
theorem B8782505 : Blo 1733067 8782505 := bstep (se 2 (by rfl) ⟨3293439, by rfl⟩ : syracuseStep 8782505 = 6586879) B6586879
theorem B5850089 : Blo 1733067 5850089 := bstep (se 2 (by rfl) ⟨2193783, by rfl⟩ : syracuseStep 5850089 = 4387567) B4387567
theorem B5629247 : Blo 1733067 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B2926057 : Blo 1733067 2926057 := bstep (se 2 (by rfl) ⟨1097271, by rfl⟩ : syracuseStep 2926057 = 2194543) B2194543
theorem B2926759 : Blo 1733067 2926759 := bstep (se 1 (by rfl) ⟨2195069, by rfl⟩ : syracuseStep 2926759 = 4390139) B4390139
theorem B3901715 : Blo 1733067 3901715 := bstep (se 1 (by rfl) ⟨2926286, by rfl⟩ : syracuseStep 3901715 = 5852573) B5852573
theorem B4452060181 : Blo 1733067 4452060181 := bstep (se 6 (by rfl) ⟨104345160, by rfl⟩ : syracuseStep 4452060181 = 208690321) B208690321
theorem B2927711 : Blo 1733067 2927711 := bstep (se 1 (by rfl) ⟨2195783, by rfl⟩ : syracuseStep 2927711 = 4391567) B4391567
theorem B2600171 : Blo 1733067 2600171 := bstep (se 1 (by rfl) ⟨1950128, by rfl⟩ : syracuseStep 2600171 = 3900257) B3900257
theorem B29633849 : Blo 1733067 29633849 := bstep (se 2 (by rfl) ⟨11112693, by rfl⟩ : syracuseStep 29633849 = 22225387) B22225387
theorem B18738661 : Blo 1733067 18738661 := bstep (se 4 (by rfl) ⟨1756749, by rfl⟩ : syracuseStep 18738661 = 3513499) B3513499
theorem B3903209 : Blo 1733067 3903209 := bstep (se 2 (by rfl) ⟨1463703, by rfl⟩ : syracuseStep 3903209 = 2927407) B2927407
theorem B2600795 : Blo 1733067 2600795 := bstep (se 1 (by rfl) ⟨1950596, by rfl⟩ : syracuseStep 2600795 = 3901193) B3901193
theorem B136990603 : Blo 1733067 136990603 := bstep (se 1 (by rfl) ⟨102742952, by rfl⟩ : syracuseStep 136990603 = 205485905) B205485905
theorem B5853167 : Blo 1733067 5853167 := bstep (se 1 (by rfl) ⟨4389875, by rfl⟩ : syracuseStep 5853167 = 8779751) B8779751
theorem B19763189 : Blo 1733067 19763189 := bstep (se 5 (by rfl) ⟨926399, by rfl⟩ : syracuseStep 19763189 = 1852799) B1852799
theorem B3903695 : Blo 1733067 3903695 := bstep (se 1 (by rfl) ⟨2927771, by rfl⟩ : syracuseStep 3903695 = 5855543) B5855543
theorem B6246683 : Blo 1733067 6246683 := bstep (se 1 (by rfl) ⟨4685012, by rfl⟩ : syracuseStep 6246683 = 9370025) B9370025
theorem B1733275 : Blo 1733067 1733275 := bstep (se 1 (by rfl) ⟨1299956, by rfl⟩ : syracuseStep 1733275 = 2599913) B2599913
theorem B1733327 : Blo 1733067 1733327 := bstep (se 1 (by rfl) ⟨1299995, by rfl⟩ : syracuseStep 1733327 = 2599991) B2599991
theorem B22213601 : Blo 1733067 22213601 := bstep (se 2 (by rfl) ⟨8330100, by rfl⟩ : syracuseStep 22213601 = 16660201) B16660201
theorem B1733659 : Blo 1733067 1733659 := bstep (se 1 (by rfl) ⟨1300244, by rfl⟩ : syracuseStep 1733659 = 2600489) B2600489
theorem B2602121 : Blo 1733067 2602121 := bstep (se 2 (by rfl) ⟨975795, by rfl⟩ : syracuseStep 2602121 = 1951591) B1951591
theorem B19256483 : Blo 1733067 19256483 := bstep (se 1 (by rfl) ⟨14442362, by rfl⟩ : syracuseStep 19256483 = 28884725) B28884725
theorem B6583463 : Blo 1733067 6583463 := bstep (se 1 (by rfl) ⟨4937597, by rfl⟩ : syracuseStep 6583463 = 9875195) B9875195
theorem B1733887 : Blo 1733067 1733887 := bstep (se 1 (by rfl) ⟨1300415, by rfl⟩ : syracuseStep 1733887 = 2600831) B2600831
theorem B5854463 : Blo 1733067 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B3290395 : Blo 1733067 3290395 := bstep (se 1 (by rfl) ⟨2467796, by rfl⟩ : syracuseStep 3290395 = 4935593) B4935593
theorem B2602319 : Blo 1733067 2602319 := bstep (se 1 (by rfl) ⟨1951739, by rfl⟩ : syracuseStep 2602319 = 3903479) B3903479
theorem B5854679 : Blo 1733067 5854679 := bstep (se 1 (by rfl) ⟨4391009, by rfl⟩ : syracuseStep 5854679 = 8782019) B8782019
theorem B44431091 : Blo 1733067 44431091 := bstep (se 1 (by rfl) ⟨33323318, by rfl⟩ : syracuseStep 44431091 = 66646637) B66646637
theorem B13162337 : Blo 1733067 13162337 := bstep (se 2 (by rfl) ⟨4935876, by rfl⟩ : syracuseStep 13162337 = 9871753) B9871753
theorem B9877403 : Blo 1733067 9877403 := bstep (se 1 (by rfl) ⟨7408052, by rfl⟩ : syracuseStep 9877403 = 14816105) B14816105
theorem B85481561 : Blo 1733067 85481561 := bstep (se 2 (by rfl) ⟨32055585, by rfl⟩ : syracuseStep 85481561 = 64111171) B64111171
theorem B9378413 : Blo 1733067 9378413 := bstep (se 3 (by rfl) ⟨1758452, by rfl⟩ : syracuseStep 9378413 = 3516905) B3516905
theorem B4938383 : Blo 1733067 4938383 := bstep (se 1 (by rfl) ⟨3703787, by rfl⟩ : syracuseStep 4938383 = 7407575) B7407575
theorem B3292103 : Blo 1733067 3292103 := bstep (se 1 (by rfl) ⟨2469077, by rfl⟩ : syracuseStep 3292103 = 4938155) B4938155
theorem B21134441 : Blo 1733067 21134441 := bstep (se 2 (by rfl) ⟨7925415, by rfl⟩ : syracuseStep 21134441 = 15850831) B15850831
theorem B17800681 : Blo 1733067 17800681 := bstep (se 2 (by rfl) ⟨6675255, by rfl⟩ : syracuseStep 17800681 = 13350511) B13350511
theorem B5553785 : Blo 1733067 5553785 := bstep (se 2 (by rfl) ⟨2082669, by rfl⟩ : syracuseStep 5553785 = 4165339) B4165339
theorem B3899447 : Blo 1733067 3899447 := bstep (se 1 (by rfl) ⟨2924585, by rfl⟩ : syracuseStep 3899447 = 5849171) B5849171
theorem B1949791 : Blo 1733067 1949791 := bstep (se 1 (by rfl) ⟨1462343, by rfl⟩ : syracuseStep 1949791 = 2924687) B2924687
theorem B5849387 : Blo 1733067 5849387 := bstep (se 1 (by rfl) ⟨4387040, by rfl⟩ : syracuseStep 5849387 = 8774081) B8774081
theorem B3900059 : Blo 1733067 3900059 := bstep (se 1 (by rfl) ⟨2925044, by rfl⟩ : syracuseStep 3900059 = 5850089) B5850089
theorem B12837655 : Blo 1733067 12837655 := bstep (se 1 (by rfl) ⟨9628241, by rfl⟩ : syracuseStep 12837655 = 19256483) B19256483
theorem B3752831 : Blo 1733067 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B8774891 : Blo 1733067 8774891 := bstep (se 1 (by rfl) ⟨6581168, by rfl⟩ : syracuseStep 8774891 = 13162337) B13162337
theorem B5936080241 : Blo 1733067 5936080241 := bstep (se 2 (by rfl) ⟨2226030090, by rfl⟩ : syracuseStep 5936080241 = 4452060181) B4452060181
theorem B6252275 : Blo 1733067 6252275 := bstep (se 1 (by rfl) ⟨4689206, by rfl⟩ : syracuseStep 6252275 = 9378413) B9378413
theorem B3901409 : Blo 1733067 3901409 := bstep (se 2 (by rfl) ⟨1463028, by rfl⟩ : syracuseStep 3901409 = 2926057) B2926057
theorem B23734241 : Blo 1733067 23734241 := bstep (se 2 (by rfl) ⟨8900340, by rfl⟩ : syracuseStep 23734241 = 17800681) B17800681
theorem B1951807 : Blo 1733067 1951807 := bstep (se 1 (by rfl) ⟨1463855, by rfl⟩ : syracuseStep 1951807 = 2927711) B2927711
theorem B3902111 : Blo 1733067 3902111 := bstep (se 1 (by rfl) ⟨2926583, by rfl⟩ : syracuseStep 3902111 = 5853167) B5853167
theorem B13175459 : Blo 1733067 13175459 := bstep (se 1 (by rfl) ⟨9881594, by rfl⟩ : syracuseStep 13175459 = 19763189) B19763189
theorem B4164455 : Blo 1733067 4164455 := bstep (se 1 (by rfl) ⟨3123341, by rfl⟩ : syracuseStep 4164455 = 6246683) B6246683
theorem B3902345 : Blo 1733067 3902345 := bstep (se 2 (by rfl) ⟨1463379, by rfl⟩ : syracuseStep 3902345 = 2926759) B2926759
theorem B3902975 : Blo 1733067 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B3903119 : Blo 1733067 3903119 := bstep (se 1 (by rfl) ⟨2927339, by rfl⟩ : syracuseStep 3903119 = 5854679) B5854679
theorem B56987707 : Blo 1733067 56987707 := bstep (se 1 (by rfl) ⟨42740780, by rfl⟩ : syracuseStep 56987707 = 85481561) B85481561
theorem B2601143 : Blo 1733067 2601143 := bstep (se 1 (by rfl) ⟨1950857, by rfl⟩ : syracuseStep 2601143 = 3901715) B3901715
theorem B4387193 : Blo 1733067 4387193 := bstep (se 2 (by rfl) ⟨1645197, by rfl⟩ : syracuseStep 4387193 = 3290395) B3290395
theorem B1733447 : Blo 1733067 1733447 := bstep (se 1 (by rfl) ⟨1300085, by rfl⟩ : syracuseStep 1733447 = 2600171) B2600171
theorem B19755899 : Blo 1733067 19755899 := bstep (se 1 (by rfl) ⟨14816924, by rfl⟩ : syracuseStep 19755899 = 29633849) B29633849
theorem B2602139 : Blo 1733067 2602139 := bstep (se 1 (by rfl) ⟨1951604, by rfl⟩ : syracuseStep 2602139 = 3903209) B3903209
theorem B182654137 : Blo 1733067 182654137 := bstep (se 2 (by rfl) ⟨68495301, by rfl⟩ : syracuseStep 182654137 = 136990603) B136990603
theorem B8778941 : Blo 1733067 8778941 := bstep (se 3 (by rfl) ⟨1646051, by rfl⟩ : syracuseStep 8778941 = 3292103) B3292103
theorem B1733863 : Blo 1733067 1733863 := bstep (se 1 (by rfl) ⟨1300397, by rfl⟩ : syracuseStep 1733863 = 2600795) B2600795
theorem B2602463 : Blo 1733067 2602463 := bstep (se 1 (by rfl) ⟨1951847, by rfl⟩ : syracuseStep 2602463 = 3903695) B3903695
theorem B26695169 : Blo 1733067 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B5855003 : Blo 1733067 5855003 := bstep (se 1 (by rfl) ⟨4391252, by rfl⟩ : syracuseStep 5855003 = 8782505) B8782505
theorem B14809067 : Blo 1733067 14809067 := bstep (se 1 (by rfl) ⟨11106800, by rfl⟩ : syracuseStep 14809067 = 22213601) B22213601
theorem B1734747 : Blo 1733067 1734747 := bstep (se 1 (by rfl) ⟨1301060, by rfl⟩ : syracuseStep 1734747 = 2602121) B2602121
theorem B4388975 : Blo 1733067 4388975 := bstep (se 1 (by rfl) ⟨3291731, by rfl⟩ : syracuseStep 4388975 = 6583463) B6583463
theorem B1734879 : Blo 1733067 1734879 := bstep (se 1 (by rfl) ⟨1301159, by rfl⟩ : syracuseStep 1734879 = 2602319) B2602319
theorem B29620727 : Blo 1733067 29620727 := bstep (se 1 (by rfl) ⟨22215545, by rfl⟩ : syracuseStep 29620727 = 44431091) B44431091
theorem B6584935 : Blo 1733067 6584935 := bstep (se 1 (by rfl) ⟨4938701, by rfl⟩ : syracuseStep 6584935 = 9877403) B9877403
theorem B3292255 : Blo 1733067 3292255 := bstep (se 1 (by rfl) ⟨2469191, by rfl⟩ : syracuseStep 3292255 = 4938383) B4938383
theorem B24984881 : Blo 1733067 24984881 := bstep (se 2 (by rfl) ⟨9369330, by rfl⟩ : syracuseStep 24984881 = 18738661) B18738661
theorem B14089627 : Blo 1733067 14089627 := bstep (se 1 (by rfl) ⟨10567220, by rfl⟩ : syracuseStep 14089627 = 21134441) B21134441
theorem B3702523 : Blo 1733067 3702523 := bstep (se 1 (by rfl) ⟨2776892, by rfl⟩ : syracuseStep 3702523 = 5553785) B5553785
theorem B3899591 : Blo 1733067 3899591 := bstep (se 1 (by rfl) ⟨2924693, by rfl⟩ : syracuseStep 3899591 = 5849387) B5849387
theorem B2924795 : Blo 1733067 2924795 := bstep (se 1 (by rfl) ⟨2193596, by rfl⟩ : syracuseStep 2924795 = 4387193) B4387193
theorem B5849927 : Blo 1733067 5849927 := bstep (se 1 (by rfl) ⟨4387445, by rfl⟩ : syracuseStep 5849927 = 8774891) B8774891
theorem B9872711 : Blo 1733067 9872711 := bstep (se 1 (by rfl) ⟨7404533, by rfl⟩ : syracuseStep 9872711 = 14809067) B14809067
theorem B2925983 : Blo 1733067 2925983 := bstep (se 1 (by rfl) ⟨2194487, by rfl⟩ : syracuseStep 2925983 = 4388975) B4388975
theorem B8783639 : Blo 1733067 8783639 := bstep (se 1 (by rfl) ⟨6587729, by rfl⟩ : syracuseStep 8783639 = 13175459) B13175459
theorem B18786169 : Blo 1733067 18786169 := bstep (se 2 (by rfl) ⟨7044813, by rfl⟩ : syracuseStep 18786169 = 14089627) B14089627
theorem B16656587 : Blo 1733067 16656587 := bstep (se 1 (by rfl) ⟨12492440, by rfl⟩ : syracuseStep 16656587 = 24984881) B24984881
theorem B2599631 : Blo 1733067 2599631 := bstep (se 1 (by rfl) ⟨1949723, by rfl⟩ : syracuseStep 2599631 = 3899447) B3899447
theorem B75983609 : Blo 1733067 75983609 := bstep (se 2 (by rfl) ⟨28493853, by rfl⟩ : syracuseStep 75983609 = 56987707) B56987707
theorem B2599721 : Blo 1733067 2599721 := bstep (se 2 (by rfl) ⟨974895, by rfl⟩ : syracuseStep 2599721 = 1949791) B1949791
theorem B2600039 : Blo 1733067 2600039 := bstep (se 1 (by rfl) ⟨1950029, by rfl⟩ : syracuseStep 2600039 = 3900059) B3900059
theorem B5852627 : Blo 1733067 5852627 := bstep (se 1 (by rfl) ⟨4389470, by rfl⟩ : syracuseStep 5852627 = 8778941) B8778941
theorem B3957386827 : Blo 1733067 3957386827 := bstep (se 1 (by rfl) ⟨2968040120, by rfl⟩ : syracuseStep 3957386827 = 5936080241) B5936080241
theorem B17796779 : Blo 1733067 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B3903335 : Blo 1733067 3903335 := bstep (se 1 (by rfl) ⟨2927501, by rfl⟩ : syracuseStep 3903335 = 5855003) B5855003
theorem B2600939 : Blo 1733067 2600939 := bstep (se 1 (by rfl) ⟨1950704, by rfl⟩ : syracuseStep 2600939 = 3901409) B3901409
theorem B15822827 : Blo 1733067 15822827 := bstep (se 1 (by rfl) ⟨11867120, by rfl⟩ : syracuseStep 15822827 = 23734241) B23734241
theorem B19747151 : Blo 1733067 19747151 := bstep (se 1 (by rfl) ⟨14810363, by rfl⟩ : syracuseStep 19747151 = 29620727) B29620727
theorem B2601407 : Blo 1733067 2601407 := bstep (se 1 (by rfl) ⟨1951055, by rfl⟩ : syracuseStep 2601407 = 3902111) B3902111
theorem B2601563 : Blo 1733067 2601563 := bstep (se 1 (by rfl) ⟨1951172, by rfl⟩ : syracuseStep 2601563 = 3902345) B3902345
theorem B4936697 : Blo 1733067 4936697 := bstep (se 2 (by rfl) ⟨1851261, by rfl⟩ : syracuseStep 4936697 = 3702523) B3702523
theorem B10007549 : Blo 1733067 10007549 := bstep (se 3 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 10007549 = 3752831) B3752831
theorem B2601983 : Blo 1733067 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B2602079 : Blo 1733067 2602079 := bstep (se 1 (by rfl) ⟨1951559, by rfl⟩ : syracuseStep 2602079 = 3903119) B3903119
theorem B2602409 : Blo 1733067 2602409 := bstep (se 2 (by rfl) ⟨975903, by rfl⟩ : syracuseStep 2602409 = 1951807) B1951807
theorem B1734095 : Blo 1733067 1734095 := bstep (se 1 (by rfl) ⟨1300571, by rfl⟩ : syracuseStep 1734095 = 2601143) B2601143
theorem B13170599 : Blo 1733067 13170599 := bstep (se 1 (by rfl) ⟨9877949, by rfl⟩ : syracuseStep 13170599 = 19755899) B19755899
theorem B1734759 : Blo 1733067 1734759 := bstep (se 1 (by rfl) ⟨1301069, by rfl⟩ : syracuseStep 1734759 = 2602139) B2602139
theorem B8779913 : Blo 1733067 8779913 := bstep (se 2 (by rfl) ⟨3292467, by rfl⟩ : syracuseStep 8779913 = 6584935) B6584935
theorem B1734975 : Blo 1733067 1734975 := bstep (se 1 (by rfl) ⟨1301231, by rfl⟩ : syracuseStep 1734975 = 2602463) B2602463
theorem B4168183 : Blo 1733067 4168183 := bstep (se 1 (by rfl) ⟨3126137, by rfl⟩ : syracuseStep 4168183 = 6252275) B6252275
theorem B68467493 : Blo 1733067 68467493 := bstep (se 4 (by rfl) ⟨6418827, by rfl⟩ : syracuseStep 68467493 = 12837655) B12837655
theorem B4389673 : Blo 1733067 4389673 := bstep (se 2 (by rfl) ⟨1646127, by rfl⟩ : syracuseStep 4389673 = 3292255) B3292255
theorem B243538849 : Blo 1733067 243538849 := bstep (se 2 (by rfl) ⟨91327068, by rfl⟩ : syracuseStep 243538849 = 182654137) B182654137
theorem B2776303 : Blo 1733067 2776303 := bstep (se 1 (by rfl) ⟨2082227, by rfl⟩ : syracuseStep 2776303 = 4164455) B4164455
theorem B1949863 : Blo 1733067 1949863 := bstep (se 1 (by rfl) ⟨1462397, by rfl⟩ : syracuseStep 1949863 = 2924795) B2924795
theorem B13164767 : Blo 1733067 13164767 := bstep (se 1 (by rfl) ⟨9873575, by rfl⟩ : syracuseStep 13164767 = 19747151) B19747151
theorem B3899951 : Blo 1733067 3899951 := bstep (se 1 (by rfl) ⟨2924963, by rfl⟩ : syracuseStep 3899951 = 5849927) B5849927
theorem B1950655 : Blo 1733067 1950655 := bstep (se 1 (by rfl) ⟨1462991, by rfl⟩ : syracuseStep 1950655 = 2925983) B2925983
theorem B3901751 : Blo 1733067 3901751 := bstep (se 1 (by rfl) ⟨2926313, by rfl⟩ : syracuseStep 3901751 = 5852627) B5852627
theorem B11864519 : Blo 1733067 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B2599727 : Blo 1733067 2599727 := bstep (se 1 (by rfl) ⟨1949795, by rfl⟩ : syracuseStep 2599727 = 3899591) B3899591
theorem B5557577 : Blo 1733067 5557577 := bstep (se 2 (by rfl) ⟨2084091, by rfl⟩ : syracuseStep 5557577 = 4168183) B4168183
theorem B6671699 : Blo 1733067 6671699 := bstep (se 1 (by rfl) ⟨5003774, by rfl⟩ : syracuseStep 6671699 = 10007549) B10007549
theorem B6581807 : Blo 1733067 6581807 := bstep (se 1 (by rfl) ⟨4936355, by rfl⟩ : syracuseStep 6581807 = 9872711) B9872711
theorem B5852897 : Blo 1733067 5852897 := bstep (se 2 (by rfl) ⟨2194836, by rfl⟩ : syracuseStep 5852897 = 4389673) B4389673
theorem B324718465 : Blo 1733067 324718465 := bstep (se 2 (by rfl) ⟨121769424, by rfl⟩ : syracuseStep 324718465 = 243538849) B243538849
theorem B5853275 : Blo 1733067 5853275 := bstep (se 1 (by rfl) ⟨4389956, by rfl⟩ : syracuseStep 5853275 = 8779913) B8779913
theorem B11104391 : Blo 1733067 11104391 := bstep (se 1 (by rfl) ⟨8328293, by rfl⟩ : syracuseStep 11104391 = 16656587) B16656587
theorem B1733087 : Blo 1733067 1733087 := bstep (se 1 (by rfl) ⟨1299815, by rfl⟩ : syracuseStep 1733087 = 2599631) B2599631
theorem B50655739 : Blo 1733067 50655739 := bstep (se 1 (by rfl) ⟨37991804, by rfl⟩ : syracuseStep 50655739 = 75983609) B75983609
theorem B1733147 : Blo 1733067 1733147 := bstep (se 1 (by rfl) ⟨1299860, by rfl⟩ : syracuseStep 1733147 = 2599721) B2599721
theorem B1733359 : Blo 1733067 1733359 := bstep (se 1 (by rfl) ⟨1300019, by rfl⟩ : syracuseStep 1733359 = 2600039) B2600039
theorem B25048225 : Blo 1733067 25048225 := bstep (se 2 (by rfl) ⟨9393084, by rfl⟩ : syracuseStep 25048225 = 18786169) B18786169
theorem B2602223 : Blo 1733067 2602223 := bstep (se 1 (by rfl) ⟨1951667, by rfl⟩ : syracuseStep 2602223 = 3903335) B3903335
theorem B1733959 : Blo 1733067 1733959 := bstep (se 1 (by rfl) ⟨1300469, by rfl⟩ : syracuseStep 1733959 = 2600939) B2600939
theorem B10548551 : Blo 1733067 10548551 := bstep (se 1 (by rfl) ⟨7911413, by rfl⟩ : syracuseStep 10548551 = 15822827) B15822827
theorem B1734271 : Blo 1733067 1734271 := bstep (se 1 (by rfl) ⟨1300703, by rfl⟩ : syracuseStep 1734271 = 2601407) B2601407
theorem B1734375 : Blo 1733067 1734375 := bstep (se 1 (by rfl) ⟨1300781, by rfl⟩ : syracuseStep 1734375 = 2601563) B2601563
theorem B3291131 : Blo 1733067 3291131 := bstep (se 1 (by rfl) ⟨2468348, by rfl⟩ : syracuseStep 3291131 = 4936697) B4936697
theorem B1734655 : Blo 1733067 1734655 := bstep (se 1 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 1734655 = 2601983) B2601983
theorem B1734719 : Blo 1733067 1734719 := bstep (se 1 (by rfl) ⟨1301039, by rfl⟩ : syracuseStep 1734719 = 2602079) B2602079
theorem B1734939 : Blo 1733067 1734939 := bstep (se 1 (by rfl) ⟨1301204, by rfl⟩ : syracuseStep 1734939 = 2602409) B2602409
theorem B5855759 : Blo 1733067 5855759 := bstep (se 1 (by rfl) ⟨4391819, by rfl⟩ : syracuseStep 5855759 = 8783639) B8783639
theorem B8780399 : Blo 1733067 8780399 := bstep (se 1 (by rfl) ⟨6585299, by rfl⟩ : syracuseStep 8780399 = 13170599) B13170599
theorem B3701737 : Blo 1733067 3701737 := bstep (se 2 (by rfl) ⟨1388151, by rfl⟩ : syracuseStep 3701737 = 2776303) B2776303
theorem B45644995 : Blo 1733067 45644995 := bstep (se 1 (by rfl) ⟨34233746, by rfl⟩ : syracuseStep 45644995 = 68467493) B68467493
theorem B5276515769 : Blo 1733067 5276515769 := bstep (se 2 (by rfl) ⟨1978693413, by rfl⟩ : syracuseStep 5276515769 = 3957386827) B3957386827
theorem B14820205 : Blo 1733067 14820205 := bstep (se 3 (by rfl) ⟨2778788, by rfl⟩ : syracuseStep 14820205 = 5557577) B5557577
theorem B60859993 : Blo 1733067 60859993 := bstep (se 2 (by rfl) ⟨22822497, by rfl⟩ : syracuseStep 60859993 = 45644995) B45644995
theorem B3901931 : Blo 1733067 3901931 := bstep (se 1 (by rfl) ⟨2926448, by rfl⟩ : syracuseStep 3901931 = 5852897) B5852897
theorem B432957953 : Blo 1733067 432957953 := bstep (se 2 (by rfl) ⟨162359232, by rfl⟩ : syracuseStep 432957953 = 324718465) B324718465
theorem B8776349 : Blo 1733067 8776349 := bstep (se 3 (by rfl) ⟨1645565, by rfl⟩ : syracuseStep 8776349 = 3291131) B3291131
theorem B3902183 : Blo 1733067 3902183 := bstep (se 1 (by rfl) ⟨2926637, by rfl⟩ : syracuseStep 3902183 = 5853275) B5853275
theorem B8776511 : Blo 1733067 8776511 := bstep (se 1 (by rfl) ⟨6582383, by rfl⟩ : syracuseStep 8776511 = 13164767) B13164767
theorem B2599817 : Blo 1733067 2599817 := bstep (se 2 (by rfl) ⟨974931, by rfl⟩ : syracuseStep 2599817 = 1949863) B1949863
theorem B2599967 : Blo 1733067 2599967 := bstep (se 1 (by rfl) ⟨1949975, by rfl⟩ : syracuseStep 2599967 = 3899951) B3899951
theorem B7032367 : Blo 1733067 7032367 := bstep (se 1 (by rfl) ⟨5274275, by rfl⟩ : syracuseStep 7032367 = 10548551) B10548551
theorem B2600873 : Blo 1733067 2600873 := bstep (se 2 (by rfl) ⟨975327, by rfl⟩ : syracuseStep 2600873 = 1950655) B1950655
theorem B4935649 : Blo 1733067 4935649 := bstep (se 2 (by rfl) ⟨1850868, by rfl⟩ : syracuseStep 4935649 = 3701737) B3701737
theorem B2601167 : Blo 1733067 2601167 := bstep (se 1 (by rfl) ⟨1950875, by rfl⟩ : syracuseStep 2601167 = 3901751) B3901751
theorem B7909679 : Blo 1733067 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B3903839 : Blo 1733067 3903839 := bstep (se 1 (by rfl) ⟨2927879, by rfl⟩ : syracuseStep 3903839 = 5855759) B5855759
theorem B5853599 : Blo 1733067 5853599 := bstep (se 1 (by rfl) ⟨4390199, by rfl⟩ : syracuseStep 5853599 = 8780399) B8780399
theorem B1733151 : Blo 1733067 1733151 := bstep (se 1 (by rfl) ⟨1299863, by rfl⟩ : syracuseStep 1733151 = 2599727) B2599727
theorem B4387871 : Blo 1733067 4387871 := bstep (se 1 (by rfl) ⟨3290903, by rfl⟩ : syracuseStep 4387871 = 6581807) B6581807
theorem B7402927 : Blo 1733067 7402927 := bstep (se 1 (by rfl) ⟨5552195, by rfl⟩ : syracuseStep 7402927 = 11104391) B11104391
theorem B67540985 : Blo 1733067 67540985 := bstep (se 2 (by rfl) ⟨25327869, by rfl⟩ : syracuseStep 67540985 = 50655739) B50655739
theorem B1734815 : Blo 1733067 1734815 := bstep (se 1 (by rfl) ⟨1301111, by rfl⟩ : syracuseStep 1734815 = 2602223) B2602223
theorem B33397633 : Blo 1733067 33397633 := bstep (se 2 (by rfl) ⟨12524112, by rfl⟩ : syracuseStep 33397633 = 25048225) B25048225
theorem B4447799 : Blo 1733067 4447799 := bstep (se 1 (by rfl) ⟨3335849, by rfl⟩ : syracuseStep 4447799 = 6671699) B6671699
theorem B3517677179 : Blo 1733067 3517677179 := bstep (se 1 (by rfl) ⟨2638257884, by rfl⟩ : syracuseStep 3517677179 = 5276515769) B5276515769
theorem B2925247 : Blo 1733067 2925247 := bstep (se 1 (by rfl) ⟨2193935, by rfl⟩ : syracuseStep 2925247 = 4387871) B4387871
theorem B19760273 : Blo 1733067 19760273 := bstep (se 2 (by rfl) ⟨7410102, by rfl⟩ : syracuseStep 19760273 = 14820205) B14820205
theorem B288638635 : Blo 1733067 288638635 := bstep (se 1 (by rfl) ⟨216478976, by rfl⟩ : syracuseStep 288638635 = 432957953) B432957953
theorem B5850899 : Blo 1733067 5850899 := bstep (se 1 (by rfl) ⟨4388174, by rfl⟩ : syracuseStep 5850899 = 8776349) B8776349
theorem B5851007 : Blo 1733067 5851007 := bstep (se 1 (by rfl) ⟨4388255, by rfl⟩ : syracuseStep 5851007 = 8776511) B8776511
theorem B2345118119 : Blo 1733067 2345118119 := bstep (se 1 (by rfl) ⟨1758838589, by rfl⟩ : syracuseStep 2345118119 = 3517677179) B3517677179
theorem B6580865 : Blo 1733067 6580865 := bstep (se 2 (by rfl) ⟨2467824, by rfl⟩ : syracuseStep 6580865 = 4935649) B4935649
theorem B3902399 : Blo 1733067 3902399 := bstep (se 1 (by rfl) ⟨2926799, by rfl⟩ : syracuseStep 3902399 = 5853599) B5853599
theorem B45027323 : Blo 1733067 45027323 := bstep (se 1 (by rfl) ⟨33770492, by rfl⟩ : syracuseStep 45027323 = 67540985) B67540985
theorem B2601287 : Blo 1733067 2601287 := bstep (se 1 (by rfl) ⟨1950965, by rfl⟩ : syracuseStep 2601287 = 3901931) B3901931
theorem B2601455 : Blo 1733067 2601455 := bstep (se 1 (by rfl) ⟨1951091, by rfl⟩ : syracuseStep 2601455 = 3902183) B3902183
theorem B1733211 : Blo 1733067 1733211 := bstep (se 1 (by rfl) ⟨1299908, by rfl⟩ : syracuseStep 1733211 = 2599817) B2599817
theorem B1733311 : Blo 1733067 1733311 := bstep (se 1 (by rfl) ⟨1299983, by rfl⟩ : syracuseStep 1733311 = 2599967) B2599967
theorem B9376489 : Blo 1733067 9376489 := bstep (se 2 (by rfl) ⟨3516183, by rfl⟩ : syracuseStep 9376489 = 7032367) B7032367
theorem B81146657 : Blo 1733067 81146657 := bstep (se 2 (by rfl) ⟨30429996, by rfl⟩ : syracuseStep 81146657 = 60859993) B60859993
theorem B1733915 : Blo 1733067 1733915 := bstep (se 1 (by rfl) ⟨1300436, by rfl⟩ : syracuseStep 1733915 = 2600873) B2600873
theorem B1734111 : Blo 1733067 1734111 := bstep (se 1 (by rfl) ⟨1300583, by rfl⟩ : syracuseStep 1734111 = 2601167) B2601167
theorem B5273119 : Blo 1733067 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B2602559 : Blo 1733067 2602559 := bstep (se 1 (by rfl) ⟨1951919, by rfl⟩ : syracuseStep 2602559 = 3903839) B3903839
theorem B44530177 : Blo 1733067 44530177 := bstep (se 2 (by rfl) ⟨16698816, by rfl⟩ : syracuseStep 44530177 = 33397633) B33397633
theorem B9870569 : Blo 1733067 9870569 := bstep (se 2 (by rfl) ⟨3701463, by rfl⟩ : syracuseStep 9870569 = 7402927) B7402927
theorem B2965199 : Blo 1733067 2965199 := bstep (se 1 (by rfl) ⟨2223899, by rfl⟩ : syracuseStep 2965199 = 4447799) B4447799
theorem B28123301 : Blo 1733067 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B13173515 : Blo 1733067 13173515 := bstep (se 1 (by rfl) ⟨9880136, by rfl⟩ : syracuseStep 13173515 = 19760273) B19760273
theorem B3900329 : Blo 1733067 3900329 := bstep (se 2 (by rfl) ⟨1462623, by rfl⟩ : syracuseStep 3900329 = 2925247) B2925247
theorem B3900599 : Blo 1733067 3900599 := bstep (se 1 (by rfl) ⟨2925449, by rfl⟩ : syracuseStep 3900599 = 5850899) B5850899
theorem B3900671 : Blo 1733067 3900671 := bstep (se 1 (by rfl) ⟨2925503, by rfl⟩ : syracuseStep 3900671 = 5851007) B5851007
theorem B1563412079 : Blo 1733067 1563412079 := bstep (se 1 (by rfl) ⟨1172559059, by rfl⟩ : syracuseStep 1563412079 = 2345118119) B2345118119
theorem B6580379 : Blo 1733067 6580379 := bstep (se 1 (by rfl) ⟨4935284, by rfl⟩ : syracuseStep 6580379 = 9870569) B9870569
theorem B30018215 : Blo 1733067 30018215 := bstep (se 1 (by rfl) ⟨22513661, by rfl⟩ : syracuseStep 30018215 = 45027323) B45027323
theorem B50007941 : Blo 1733067 50007941 := bstep (se 4 (by rfl) ⟨4688244, by rfl⟩ : syracuseStep 50007941 = 9376489) B9376489
theorem B4387243 : Blo 1733067 4387243 := bstep (se 1 (by rfl) ⟨3290432, by rfl⟩ : syracuseStep 4387243 = 6580865) B6580865
theorem B2601599 : Blo 1733067 2601599 := bstep (se 1 (by rfl) ⟨1951199, by rfl⟩ : syracuseStep 2601599 = 3902399) B3902399
theorem B1734191 : Blo 1733067 1734191 := bstep (se 1 (by rfl) ⟨1300643, by rfl⟩ : syracuseStep 1734191 = 2601287) B2601287
theorem B1734303 : Blo 1733067 1734303 := bstep (se 1 (by rfl) ⟨1300727, by rfl⟩ : syracuseStep 1734303 = 2601455) B2601455
theorem B59373569 : Blo 1733067 59373569 := bstep (se 2 (by rfl) ⟨22265088, by rfl⟩ : syracuseStep 59373569 = 44530177) B44530177
theorem B1735039 : Blo 1733067 1735039 := bstep (se 1 (by rfl) ⟨1301279, by rfl⟩ : syracuseStep 1735039 = 2602559) B2602559
theorem B216391085 : Blo 1733067 216391085 := bstep (se 3 (by rfl) ⟨40573328, by rfl⟩ : syracuseStep 216391085 = 81146657) B81146657
theorem B31628789 : Blo 1733067 31628789 := bstep (se 5 (by rfl) ⟨1482599, by rfl⟩ : syracuseStep 31628789 = 2965199) B2965199
theorem B384851513 : Blo 1733067 384851513 := bstep (se 2 (by rfl) ⟨144319317, by rfl⟩ : syracuseStep 384851513 = 288638635) B288638635
theorem B8782343 : Blo 1733067 8782343 := bstep (se 1 (by rfl) ⟨6586757, by rfl⟩ : syracuseStep 8782343 = 13173515) B13173515
theorem B5849657 : Blo 1733067 5849657 := bstep (se 2 (by rfl) ⟨2193621, by rfl⟩ : syracuseStep 5849657 = 4387243) B4387243
theorem B256567675 : Blo 1733067 256567675 := bstep (se 1 (by rfl) ⟨192425756, by rfl⟩ : syracuseStep 256567675 = 384851513) B384851513
theorem B2600219 : Blo 1733067 2600219 := bstep (se 1 (by rfl) ⟨1950164, by rfl⟩ : syracuseStep 2600219 = 3900329) B3900329
theorem B2600399 : Blo 1733067 2600399 := bstep (se 1 (by rfl) ⟨1950299, by rfl⟩ : syracuseStep 2600399 = 3900599) B3900599
theorem B2600447 : Blo 1733067 2600447 := bstep (se 1 (by rfl) ⟨1950335, by rfl⟩ : syracuseStep 2600447 = 3900671) B3900671
theorem B4386919 : Blo 1733067 4386919 := bstep (se 1 (by rfl) ⟨3290189, by rfl⟩ : syracuseStep 4386919 = 6580379) B6580379
theorem B33338627 : Blo 1733067 33338627 := bstep (se 1 (by rfl) ⟨25003970, by rfl⟩ : syracuseStep 33338627 = 50007941) B50007941
theorem B18748867 : Blo 1733067 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B1734399 : Blo 1733067 1734399 := bstep (se 1 (by rfl) ⟨1300799, by rfl⟩ : syracuseStep 1734399 = 2601599) B2601599
theorem B1042274719 : Blo 1733067 1042274719 := bstep (se 1 (by rfl) ⟨781706039, by rfl⟩ : syracuseStep 1042274719 = 1563412079) B1563412079
theorem B39582379 : Blo 1733067 39582379 := bstep (se 1 (by rfl) ⟨29686784, by rfl⟩ : syracuseStep 39582379 = 59373569) B59373569
theorem B20012143 : Blo 1733067 20012143 := bstep (se 1 (by rfl) ⟨15009107, by rfl⟩ : syracuseStep 20012143 = 30018215) B30018215
theorem B144260723 : Blo 1733067 144260723 := bstep (se 1 (by rfl) ⟨108195542, by rfl⟩ : syracuseStep 144260723 = 216391085) B216391085
theorem B21085859 : Blo 1733067 21085859 := bstep (se 1 (by rfl) ⟨15814394, by rfl⟩ : syracuseStep 21085859 = 31628789) B31628789
theorem B5849225 : Blo 1733067 5849225 := bstep (se 2 (by rfl) ⟨2193459, by rfl⟩ : syracuseStep 5849225 = 4386919) B4386919
theorem B3899771 : Blo 1733067 3899771 := bstep (se 1 (by rfl) ⟨2924828, by rfl⟩ : syracuseStep 3899771 = 5849657) B5849657
theorem B342090233 : Blo 1733067 342090233 := bstep (se 2 (by rfl) ⟨128283837, by rfl⟩ : syracuseStep 342090233 = 256567675) B256567675
theorem B1389699625 : Blo 1733067 1389699625 := bstep (se 2 (by rfl) ⟨521137359, by rfl⟩ : syracuseStep 1389699625 = 1042274719) B1042274719
theorem B22225751 : Blo 1733067 22225751 := bstep (se 1 (by rfl) ⟨16669313, by rfl⟩ : syracuseStep 22225751 = 33338627) B33338627
theorem B26682857 : Blo 1733067 26682857 := bstep (se 2 (by rfl) ⟨10006071, by rfl⟩ : syracuseStep 26682857 = 20012143) B20012143
theorem B52776505 : Blo 1733067 52776505 := bstep (se 2 (by rfl) ⟨19791189, by rfl⟩ : syracuseStep 52776505 = 39582379) B39582379
theorem B24998489 : Blo 1733067 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B1733479 : Blo 1733067 1733479 := bstep (se 1 (by rfl) ⟨1300109, by rfl⟩ : syracuseStep 1733479 = 2600219) B2600219
theorem B1733599 : Blo 1733067 1733599 := bstep (se 1 (by rfl) ⟨1300199, by rfl⟩ : syracuseStep 1733599 = 2600399) B2600399
theorem B1733631 : Blo 1733067 1733631 := bstep (se 1 (by rfl) ⟨1300223, by rfl⟩ : syracuseStep 1733631 = 2600447) B2600447
theorem B5854895 : Blo 1733067 5854895 := bstep (se 1 (by rfl) ⟨4391171, by rfl⟩ : syracuseStep 5854895 = 8782343) B8782343
theorem B96173815 : Blo 1733067 96173815 := bstep (se 1 (by rfl) ⟨72130361, by rfl⟩ : syracuseStep 96173815 = 144260723) B144260723
theorem B14057239 : Blo 1733067 14057239 := bstep (se 1 (by rfl) ⟨10542929, by rfl⟩ : syracuseStep 14057239 = 21085859) B21085859
theorem B3899483 : Blo 1733067 3899483 := bstep (se 1 (by rfl) ⟨2924612, by rfl⟩ : syracuseStep 3899483 = 5849225) B5849225
theorem B1852932833 : Blo 1733067 1852932833 := bstep (se 2 (by rfl) ⟨694849812, by rfl⟩ : syracuseStep 1852932833 = 1389699625) B1389699625
theorem B128231753 : Blo 1733067 128231753 := bstep (se 2 (by rfl) ⟨48086907, by rfl⟩ : syracuseStep 128231753 = 96173815) B96173815
theorem B2599847 : Blo 1733067 2599847 := bstep (se 1 (by rfl) ⟨1949885, by rfl⟩ : syracuseStep 2599847 = 3899771) B3899771
theorem B228060155 : Blo 1733067 228060155 := bstep (se 1 (by rfl) ⟨171045116, by rfl⟩ : syracuseStep 228060155 = 342090233) B342090233
theorem B16665659 : Blo 1733067 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B17788571 : Blo 1733067 17788571 := bstep (se 1 (by rfl) ⟨13341428, by rfl⟩ : syracuseStep 17788571 = 26682857) B26682857
theorem B3903263 : Blo 1733067 3903263 := bstep (se 1 (by rfl) ⟨2927447, by rfl⟩ : syracuseStep 3903263 = 5854895) B5854895
theorem B14817167 : Blo 1733067 14817167 := bstep (se 1 (by rfl) ⟨11112875, by rfl⟩ : syracuseStep 14817167 = 22225751) B22225751
theorem B70368673 : Blo 1733067 70368673 := bstep (se 2 (by rfl) ⟨26388252, by rfl⟩ : syracuseStep 70368673 = 52776505) B52776505
theorem B18742985 : Blo 1733067 18742985 := bstep (se 2 (by rfl) ⟨7028619, by rfl⟩ : syracuseStep 18742985 = 14057239) B14057239
theorem B1235288555 : Blo 1733067 1235288555 := bstep (se 1 (by rfl) ⟨926466416, by rfl⟩ : syracuseStep 1235288555 = 1852932833) B1852932833
theorem B93824897 : Blo 1733067 93824897 := bstep (se 2 (by rfl) ⟨35184336, by rfl⟩ : syracuseStep 93824897 = 70368673) B70368673
theorem B11110439 : Blo 1733067 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B12495323 : Blo 1733067 12495323 := bstep (se 1 (by rfl) ⟨9371492, by rfl⟩ : syracuseStep 12495323 = 18742985) B18742985
theorem B608160413 : Blo 1733067 608160413 := bstep (se 3 (by rfl) ⟨114030077, by rfl⟩ : syracuseStep 608160413 = 228060155) B228060155
theorem B2599655 : Blo 1733067 2599655 := bstep (se 1 (by rfl) ⟨1949741, by rfl⟩ : syracuseStep 2599655 = 3899483) B3899483
theorem B1367805365 : Blo 1733067 1367805365 := bstep (se 5 (by rfl) ⟨64115876, by rfl⟩ : syracuseStep 1367805365 = 128231753) B128231753
theorem B1733231 : Blo 1733067 1733231 := bstep (se 1 (by rfl) ⟨1299923, by rfl⟩ : syracuseStep 1733231 = 2599847) B2599847
theorem B11859047 : Blo 1733067 11859047 := bstep (se 1 (by rfl) ⟨8894285, by rfl⟩ : syracuseStep 11859047 = 17788571) B17788571
theorem B2602175 : Blo 1733067 2602175 := bstep (se 1 (by rfl) ⟨1951631, by rfl⟩ : syracuseStep 2602175 = 3903263) B3903263
theorem B9878111 : Blo 1733067 9878111 := bstep (se 1 (by rfl) ⟨7408583, by rfl⟩ : syracuseStep 9878111 = 14817167) B14817167
theorem B823525703 : Blo 1733067 823525703 := bstep (se 1 (by rfl) ⟨617644277, by rfl⟩ : syracuseStep 823525703 = 1235288555) B1235288555
theorem B7906031 : Blo 1733067 7906031 := bstep (se 1 (by rfl) ⟨5929523, by rfl⟩ : syracuseStep 7906031 = 11859047) B11859047
theorem B7406959 : Blo 1733067 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B405440275 : Blo 1733067 405440275 := bstep (se 1 (by rfl) ⟨304080206, by rfl⟩ : syracuseStep 405440275 = 608160413) B608160413
theorem B911870243 : Blo 1733067 911870243 := bstep (se 1 (by rfl) ⟨683902682, by rfl⟩ : syracuseStep 911870243 = 1367805365) B1367805365
theorem B1733103 : Blo 1733067 1733103 := bstep (se 1 (by rfl) ⟨1299827, by rfl⟩ : syracuseStep 1733103 = 2599655) B2599655
theorem B1734783 : Blo 1733067 1734783 := bstep (se 1 (by rfl) ⟨1301087, by rfl⟩ : syracuseStep 1734783 = 2602175) B2602175
theorem B1000798901 : Blo 1733067 1000798901 := bstep (se 5 (by rfl) ⟨46912448, by rfl⟩ : syracuseStep 1000798901 = 93824897) B93824897
theorem B8330215 : Blo 1733067 8330215 := bstep (se 1 (by rfl) ⟨6247661, by rfl⟩ : syracuseStep 8330215 = 12495323) B12495323
theorem B6585407 : Blo 1733067 6585407 := bstep (se 1 (by rfl) ⟨4939055, by rfl⟩ : syracuseStep 6585407 = 9878111) B9878111
theorem B607913495 : Blo 1733067 607913495 := bstep (se 1 (by rfl) ⟨455935121, by rfl⟩ : syracuseStep 607913495 = 911870243) B911870243
theorem B667199267 : Blo 1733067 667199267 := bstep (se 1 (by rfl) ⟨500399450, by rfl⟩ : syracuseStep 667199267 = 1000798901) B1000798901
theorem B5270687 : Blo 1733067 5270687 := bstep (se 1 (by rfl) ⟨3953015, by rfl⟩ : syracuseStep 5270687 = 7906031) B7906031
theorem B9875945 : Blo 1733067 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B540587033 : Blo 1733067 540587033 := bstep (se 2 (by rfl) ⟨202720137, by rfl⟩ : syracuseStep 540587033 = 405440275) B405440275
theorem B549017135 : Blo 1733067 549017135 := bstep (se 1 (by rfl) ⟨411762851, by rfl⟩ : syracuseStep 549017135 = 823525703) B823525703
theorem B11106953 : Blo 1733067 11106953 := bstep (se 2 (by rfl) ⟨4165107, by rfl⟩ : syracuseStep 11106953 = 8330215) B8330215
theorem B4390271 : Blo 1733067 4390271 := bstep (se 1 (by rfl) ⟨3292703, by rfl⟩ : syracuseStep 4390271 = 6585407) B6585407
theorem B360391355 : Blo 1733067 360391355 := bstep (se 1 (by rfl) ⟨270293516, by rfl⟩ : syracuseStep 360391355 = 540587033) B540587033
theorem B405275663 : Blo 1733067 405275663 := bstep (se 1 (by rfl) ⟨303956747, by rfl⟩ : syracuseStep 405275663 = 607913495) B607913495
theorem B366011423 : Blo 1733067 366011423 := bstep (se 1 (by rfl) ⟨274508567, by rfl⟩ : syracuseStep 366011423 = 549017135) B549017135
theorem B2926847 : Blo 1733067 2926847 := bstep (se 1 (by rfl) ⟨2195135, by rfl⟩ : syracuseStep 2926847 = 4390271) B4390271
theorem B6583963 : Blo 1733067 6583963 := bstep (se 1 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 6583963 = 9875945) B9875945
theorem B444799511 : Blo 1733067 444799511 := bstep (se 1 (by rfl) ⟨333599633, by rfl⟩ : syracuseStep 444799511 = 667199267) B667199267
theorem B7404635 : Blo 1733067 7404635 := bstep (se 1 (by rfl) ⟨5553476, by rfl⟩ : syracuseStep 7404635 = 11106953) B11106953
theorem B3513791 : Blo 1733067 3513791 := bstep (se 1 (by rfl) ⟨2635343, by rfl⟩ : syracuseStep 3513791 = 5270687) B5270687
theorem B244007615 : Blo 1733067 244007615 := bstep (se 1 (by rfl) ⟨183005711, by rfl⟩ : syracuseStep 244007615 = 366011423) B366011423
theorem B1951231 : Blo 1733067 1951231 := bstep (se 1 (by rfl) ⟨1463423, by rfl⟩ : syracuseStep 1951231 = 2926847) B2926847
theorem B19745693 : Blo 1733067 19745693 := bstep (se 3 (by rfl) ⟨3702317, by rfl⟩ : syracuseStep 19745693 = 7404635) B7404635
theorem B270183775 : Blo 1733067 270183775 := bstep (se 1 (by rfl) ⟨202637831, by rfl⟩ : syracuseStep 270183775 = 405275663) B405275663
theorem B8778617 : Blo 1733067 8778617 := bstep (se 2 (by rfl) ⟨3291981, by rfl⟩ : syracuseStep 8778617 = 6583963) B6583963
theorem B240260903 : Blo 1733067 240260903 := bstep (se 1 (by rfl) ⟨180195677, by rfl⟩ : syracuseStep 240260903 = 360391355) B360391355
theorem B296533007 : Blo 1733067 296533007 := bstep (se 1 (by rfl) ⟨222399755, by rfl⟩ : syracuseStep 296533007 = 444799511) B444799511
theorem B2342527 : Blo 1733067 2342527 := bstep (se 1 (by rfl) ⟨1756895, by rfl⟩ : syracuseStep 2342527 = 3513791) B3513791
theorem B12493477 : Blo 1733067 12493477 := bstep (se 4 (by rfl) ⟨1171263, by rfl⟩ : syracuseStep 12493477 = 2342527) B2342527
theorem B360245033 : Blo 1733067 360245033 := bstep (se 2 (by rfl) ⟨135091887, by rfl⟩ : syracuseStep 360245033 = 270183775) B270183775
theorem B162671743 : Blo 1733067 162671743 := bstep (se 1 (by rfl) ⟨122003807, by rfl⟩ : syracuseStep 162671743 = 244007615) B244007615
theorem B5852411 : Blo 1733067 5852411 := bstep (se 1 (by rfl) ⟨4389308, by rfl⟩ : syracuseStep 5852411 = 8778617) B8778617
theorem B160173935 : Blo 1733067 160173935 := bstep (se 1 (by rfl) ⟨120130451, by rfl⟩ : syracuseStep 160173935 = 240260903) B240260903
theorem B2601641 : Blo 1733067 2601641 := bstep (se 2 (by rfl) ⟨975615, by rfl⟩ : syracuseStep 2601641 = 1951231) B1951231
theorem B13163795 : Blo 1733067 13163795 := bstep (se 1 (by rfl) ⟨9872846, by rfl⟩ : syracuseStep 13163795 = 19745693) B19745693
theorem B197688671 : Blo 1733067 197688671 := bstep (se 1 (by rfl) ⟨148266503, by rfl⟩ : syracuseStep 197688671 = 296533007) B296533007
theorem B3901607 : Blo 1733067 3901607 := bstep (se 1 (by rfl) ⟨2926205, by rfl⟩ : syracuseStep 3901607 = 5852411) B5852411
theorem B8775863 : Blo 1733067 8775863 := bstep (se 1 (by rfl) ⟨6581897, by rfl⟩ : syracuseStep 8775863 = 13163795) B13163795
theorem B16657969 : Blo 1733067 16657969 := bstep (se 2 (by rfl) ⟨6246738, by rfl⟩ : syracuseStep 16657969 = 12493477) B12493477
theorem B216895657 : Blo 1733067 216895657 := bstep (se 2 (by rfl) ⟨81335871, by rfl⟩ : syracuseStep 216895657 = 162671743) B162671743
theorem B1734427 : Blo 1733067 1734427 := bstep (se 1 (by rfl) ⟨1300820, by rfl⟩ : syracuseStep 1734427 = 2601641) B2601641
theorem B240163355 : Blo 1733067 240163355 := bstep (se 1 (by rfl) ⟨180122516, by rfl⟩ : syracuseStep 240163355 = 360245033) B360245033
theorem B131792447 : Blo 1733067 131792447 := bstep (se 1 (by rfl) ⟨98844335, by rfl⟩ : syracuseStep 131792447 = 197688671) B197688671
theorem B106782623 : Blo 1733067 106782623 := bstep (se 1 (by rfl) ⟨80086967, by rfl⟩ : syracuseStep 106782623 = 160173935) B160173935
theorem B289194209 : Blo 1733067 289194209 := bstep (se 2 (by rfl) ⟨108447828, by rfl⟩ : syracuseStep 289194209 = 216895657) B216895657
theorem B5850575 : Blo 1733067 5850575 := bstep (se 1 (by rfl) ⟨4387931, by rfl⟩ : syracuseStep 5850575 = 8775863) B8775863
theorem B22210625 : Blo 1733067 22210625 := bstep (se 2 (by rfl) ⟨8328984, by rfl⟩ : syracuseStep 22210625 = 16657969) B16657969
theorem B87861631 : Blo 1733067 87861631 := bstep (se 1 (by rfl) ⟨65896223, by rfl⟩ : syracuseStep 87861631 = 131792447) B131792447
theorem B2601071 : Blo 1733067 2601071 := bstep (se 1 (by rfl) ⟨1950803, by rfl⟩ : syracuseStep 2601071 = 3901607) B3901607
theorem B160108903 : Blo 1733067 160108903 := bstep (se 1 (by rfl) ⟨120081677, by rfl⟩ : syracuseStep 160108903 = 240163355) B240163355
theorem B71188415 : Blo 1733067 71188415 := bstep (se 1 (by rfl) ⟨53391311, by rfl⟩ : syracuseStep 71188415 = 106782623) B106782623
theorem B3900383 : Blo 1733067 3900383 := bstep (se 1 (by rfl) ⟨2925287, by rfl⟩ : syracuseStep 3900383 = 5850575) B5850575
theorem B47458943 : Blo 1733067 47458943 := bstep (se 1 (by rfl) ⟨35594207, by rfl⟩ : syracuseStep 47458943 = 71188415) B71188415
theorem B213478537 : Blo 1733067 213478537 := bstep (se 2 (by rfl) ⟨80054451, by rfl⟩ : syracuseStep 213478537 = 160108903) B160108903
theorem B117148841 : Blo 1733067 117148841 := bstep (se 2 (by rfl) ⟨43930815, by rfl⟩ : syracuseStep 117148841 = 87861631) B87861631
theorem B14807083 : Blo 1733067 14807083 := bstep (se 1 (by rfl) ⟨11105312, by rfl⟩ : syracuseStep 14807083 = 22210625) B22210625
theorem B1734047 : Blo 1733067 1734047 := bstep (se 1 (by rfl) ⟨1300535, by rfl⟩ : syracuseStep 1734047 = 2601071) B2601071
theorem B192796139 : Blo 1733067 192796139 := bstep (se 1 (by rfl) ⟨144597104, by rfl⟩ : syracuseStep 192796139 = 289194209) B289194209
theorem B19742777 : Blo 1733067 19742777 := bstep (se 2 (by rfl) ⟨7403541, by rfl⟩ : syracuseStep 19742777 = 14807083) B14807083
theorem B514123037 : Blo 1733067 514123037 := bstep (se 3 (by rfl) ⟨96398069, by rfl⟩ : syracuseStep 514123037 = 192796139) B192796139
theorem B31639295 : Blo 1733067 31639295 := bstep (se 1 (by rfl) ⟨23729471, by rfl⟩ : syracuseStep 31639295 = 47458943) B47458943
theorem B2600255 : Blo 1733067 2600255 := bstep (se 1 (by rfl) ⟨1950191, by rfl⟩ : syracuseStep 2600255 = 3900383) B3900383
theorem B78099227 : Blo 1733067 78099227 := bstep (se 1 (by rfl) ⟨58574420, by rfl⟩ : syracuseStep 78099227 = 117148841) B117148841
theorem B284638049 : Blo 1733067 284638049 := bstep (se 2 (by rfl) ⟨106739268, by rfl⟩ : syracuseStep 284638049 = 213478537) B213478537
theorem B84371453 : Blo 1733067 84371453 := bstep (se 3 (by rfl) ⟨15819647, by rfl⟩ : syracuseStep 84371453 = 31639295) B31639295
theorem B342748691 : Blo 1733067 342748691 := bstep (se 1 (by rfl) ⟨257061518, by rfl⟩ : syracuseStep 342748691 = 514123037) B514123037
theorem B1733503 : Blo 1733067 1733503 := bstep (se 1 (by rfl) ⟨1300127, by rfl⟩ : syracuseStep 1733503 = 2600255) B2600255
theorem B13161851 : Blo 1733067 13161851 := bstep (se 1 (by rfl) ⟨9871388, by rfl⟩ : syracuseStep 13161851 = 19742777) B19742777
theorem B52066151 : Blo 1733067 52066151 := bstep (se 1 (by rfl) ⟨39049613, by rfl⟩ : syracuseStep 52066151 = 78099227) B78099227
theorem B189758699 : Blo 1733067 189758699 := bstep (se 1 (by rfl) ⟨142319024, by rfl⟩ : syracuseStep 189758699 = 284638049) B284638049
theorem B8774567 : Blo 1733067 8774567 := bstep (se 1 (by rfl) ⟨6580925, by rfl⟩ : syracuseStep 8774567 = 13161851) B13161851
theorem B34710767 : Blo 1733067 34710767 := bstep (se 1 (by rfl) ⟨26033075, by rfl⟩ : syracuseStep 34710767 = 52066151) B52066151
theorem B56247635 : Blo 1733067 56247635 := bstep (se 1 (by rfl) ⟨42185726, by rfl⟩ : syracuseStep 56247635 = 84371453) B84371453
theorem B126505799 : Blo 1733067 126505799 := bstep (se 1 (by rfl) ⟨94879349, by rfl⟩ : syracuseStep 126505799 = 189758699) B189758699
theorem B228499127 : Blo 1733067 228499127 := bstep (se 1 (by rfl) ⟨171374345, by rfl⟩ : syracuseStep 228499127 = 342748691) B342748691
theorem B84337199 : Blo 1733067 84337199 := bstep (se 1 (by rfl) ⟨63252899, by rfl⟩ : syracuseStep 84337199 = 126505799) B126505799
theorem B5849711 : Blo 1733067 5849711 := bstep (se 1 (by rfl) ⟨4387283, by rfl⟩ : syracuseStep 5849711 = 8774567) B8774567
theorem B152332751 : Blo 1733067 152332751 := bstep (se 1 (by rfl) ⟨114249563, by rfl⟩ : syracuseStep 152332751 = 228499127) B228499127
theorem B37498423 : Blo 1733067 37498423 := bstep (se 1 (by rfl) ⟨28123817, by rfl⟩ : syracuseStep 37498423 = 56247635) B56247635
theorem B23140511 : Blo 1733067 23140511 := bstep (se 1 (by rfl) ⟨17355383, by rfl⟩ : syracuseStep 23140511 = 34710767) B34710767
theorem B3899807 : Blo 1733067 3899807 := bstep (se 1 (by rfl) ⟨2924855, by rfl⟩ : syracuseStep 3899807 = 5849711) B5849711
theorem B15427007 : Blo 1733067 15427007 := bstep (se 1 (by rfl) ⟨11570255, by rfl⟩ : syracuseStep 15427007 = 23140511) B23140511
theorem B49997897 : Blo 1733067 49997897 := bstep (se 2 (by rfl) ⟨18749211, by rfl⟩ : syracuseStep 49997897 = 37498423) B37498423
theorem B56224799 : Blo 1733067 56224799 := bstep (se 1 (by rfl) ⟨42168599, by rfl⟩ : syracuseStep 56224799 = 84337199) B84337199
theorem B101555167 : Blo 1733067 101555167 := bstep (se 1 (by rfl) ⟨76166375, by rfl⟩ : syracuseStep 101555167 = 152332751) B152332751
theorem B135406889 : Blo 1733067 135406889 := bstep (se 2 (by rfl) ⟨50777583, by rfl⟩ : syracuseStep 135406889 = 101555167) B101555167
theorem B2599871 : Blo 1733067 2599871 := bstep (se 1 (by rfl) ⟨1949903, by rfl⟩ : syracuseStep 2599871 = 3899807) B3899807
theorem B10284671 : Blo 1733067 10284671 := bstep (se 1 (by rfl) ⟨7713503, by rfl⟩ : syracuseStep 10284671 = 15427007) B15427007
theorem B37483199 : Blo 1733067 37483199 := bstep (se 1 (by rfl) ⟨28112399, by rfl⟩ : syracuseStep 37483199 = 56224799) B56224799
theorem B33331931 : Blo 1733067 33331931 := bstep (se 1 (by rfl) ⟨24998948, by rfl⟩ : syracuseStep 33331931 = 49997897) B49997897
theorem B24988799 : Blo 1733067 24988799 := bstep (se 1 (by rfl) ⟨18741599, by rfl⟩ : syracuseStep 24988799 = 37483199) B37483199
theorem B90271259 : Blo 1733067 90271259 := bstep (se 1 (by rfl) ⟨67703444, by rfl⟩ : syracuseStep 90271259 = 135406889) B135406889
theorem B22221287 : Blo 1733067 22221287 := bstep (se 1 (by rfl) ⟨16665965, by rfl⟩ : syracuseStep 22221287 = 33331931) B33331931
theorem B1733247 : Blo 1733067 1733247 := bstep (se 1 (by rfl) ⟨1299935, by rfl⟩ : syracuseStep 1733247 = 2599871) B2599871
theorem B6856447 : Blo 1733067 6856447 := bstep (se 1 (by rfl) ⟨5142335, by rfl⟩ : syracuseStep 6856447 = 10284671) B10284671
theorem B60180839 : Blo 1733067 60180839 := bstep (se 1 (by rfl) ⟨45135629, by rfl⟩ : syracuseStep 60180839 = 90271259) B90271259
theorem B14814191 : Blo 1733067 14814191 := bstep (se 1 (by rfl) ⟨11110643, by rfl⟩ : syracuseStep 14814191 = 22221287) B22221287
theorem B16659199 : Blo 1733067 16659199 := bstep (se 1 (by rfl) ⟨12494399, by rfl⟩ : syracuseStep 16659199 = 24988799) B24988799
theorem B9141929 : Blo 1733067 9141929 := bstep (se 2 (by rfl) ⟨3428223, by rfl⟩ : syracuseStep 9141929 = 6856447) B6856447
theorem B22212265 : Blo 1733067 22212265 := bstep (se 2 (by rfl) ⟨8329599, by rfl⟩ : syracuseStep 22212265 = 16659199) B16659199
theorem B40120559 : Blo 1733067 40120559 := bstep (se 1 (by rfl) ⟨30090419, by rfl⟩ : syracuseStep 40120559 = 60180839) B60180839
theorem B9876127 : Blo 1733067 9876127 := bstep (se 1 (by rfl) ⟨7407095, by rfl⟩ : syracuseStep 9876127 = 14814191) B14814191
theorem B6094619 : Blo 1733067 6094619 := bstep (se 1 (by rfl) ⟨4570964, by rfl⟩ : syracuseStep 6094619 = 9141929) B9141929
theorem B26747039 : Blo 1733067 26747039 := bstep (se 1 (by rfl) ⟨20060279, by rfl⟩ : syracuseStep 26747039 = 40120559) B40120559
theorem B29616353 : Blo 1733067 29616353 := bstep (se 2 (by rfl) ⟨11106132, by rfl⟩ : syracuseStep 29616353 = 22212265) B22212265
theorem B13168169 : Blo 1733067 13168169 := bstep (se 2 (by rfl) ⟨4938063, by rfl⟩ : syracuseStep 13168169 = 9876127) B9876127
theorem B4063079 : Blo 1733067 4063079 := bstep (se 1 (by rfl) ⟨3047309, by rfl⟩ : syracuseStep 4063079 = 6094619) B6094619
theorem B19744235 : Blo 1733067 19744235 := bstep (se 1 (by rfl) ⟨14808176, by rfl⟩ : syracuseStep 19744235 = 29616353) B29616353
theorem B10834877 : Blo 1733067 10834877 := bstep (se 3 (by rfl) ⟨2031539, by rfl⟩ : syracuseStep 10834877 = 4063079) B4063079
theorem B8778779 : Blo 1733067 8778779 := bstep (se 1 (by rfl) ⟨6584084, by rfl⟩ : syracuseStep 8778779 = 13168169) B13168169
theorem B17831359 : Blo 1733067 17831359 := bstep (se 1 (by rfl) ⟨13373519, by rfl⟩ : syracuseStep 17831359 = 26747039) B26747039
theorem B5852519 : Blo 1733067 5852519 := bstep (se 1 (by rfl) ⟨4389389, by rfl⟩ : syracuseStep 5852519 = 8778779) B8778779
theorem B7223251 : Blo 1733067 7223251 := bstep (se 1 (by rfl) ⟨5417438, by rfl⟩ : syracuseStep 7223251 = 10834877) B10834877
theorem B13162823 : Blo 1733067 13162823 := bstep (se 1 (by rfl) ⟨9872117, by rfl⟩ : syracuseStep 13162823 = 19744235) B19744235
theorem B95100581 : Blo 1733067 95100581 := bstep (se 4 (by rfl) ⟨8915679, by rfl⟩ : syracuseStep 95100581 = 17831359) B17831359
theorem B8775215 : Blo 1733067 8775215 := bstep (se 1 (by rfl) ⟨6581411, by rfl⟩ : syracuseStep 8775215 = 13162823) B13162823
theorem B253601549 : Blo 1733067 253601549 := bstep (se 3 (by rfl) ⟨47550290, by rfl⟩ : syracuseStep 253601549 = 95100581) B95100581
theorem B3901679 : Blo 1733067 3901679 := bstep (se 1 (by rfl) ⟨2926259, by rfl⟩ : syracuseStep 3901679 = 5852519) B5852519
theorem B9631001 : Blo 1733067 9631001 := bstep (se 2 (by rfl) ⟨3611625, by rfl⟩ : syracuseStep 9631001 = 7223251) B7223251
theorem B25682669 : Blo 1733067 25682669 := bstep (se 3 (by rfl) ⟨4815500, by rfl⟩ : syracuseStep 25682669 = 9631001) B9631001
theorem B5850143 : Blo 1733067 5850143 := bstep (se 1 (by rfl) ⟨4387607, by rfl⟩ : syracuseStep 5850143 = 8775215) B8775215
theorem B169067699 : Blo 1733067 169067699 := bstep (se 1 (by rfl) ⟨126800774, by rfl⟩ : syracuseStep 169067699 = 253601549) B253601549
theorem B2601119 : Blo 1733067 2601119 := bstep (se 1 (by rfl) ⟨1950839, by rfl⟩ : syracuseStep 2601119 = 3901679) B3901679
theorem B17121779 : Blo 1733067 17121779 := bstep (se 1 (by rfl) ⟨12841334, by rfl⟩ : syracuseStep 17121779 = 25682669) B25682669
theorem B3900095 : Blo 1733067 3900095 := bstep (se 1 (by rfl) ⟨2925071, by rfl⟩ : syracuseStep 3900095 = 5850143) B5850143
theorem B1734079 : Blo 1733067 1734079 := bstep (se 1 (by rfl) ⟨1300559, by rfl⟩ : syracuseStep 1734079 = 2601119) B2601119
theorem B112711799 : Blo 1733067 112711799 := bstep (se 1 (by rfl) ⟨84533849, by rfl⟩ : syracuseStep 112711799 = 169067699) B169067699
theorem B11414519 : Blo 1733067 11414519 := bstep (se 1 (by rfl) ⟨8560889, by rfl⟩ : syracuseStep 11414519 = 17121779) B17121779
theorem B2600063 : Blo 1733067 2600063 := bstep (se 1 (by rfl) ⟨1950047, by rfl⟩ : syracuseStep 2600063 = 3900095) B3900095
theorem B75141199 : Blo 1733067 75141199 := bstep (se 1 (by rfl) ⟨56355899, by rfl⟩ : syracuseStep 75141199 = 112711799) B112711799
theorem B100188265 : Blo 1733067 100188265 := bstep (se 2 (by rfl) ⟨37570599, by rfl⟩ : syracuseStep 100188265 = 75141199) B75141199
theorem B1733375 : Blo 1733067 1733375 := bstep (se 1 (by rfl) ⟨1300031, by rfl⟩ : syracuseStep 1733375 = 2600063) B2600063
theorem B7609679 : Blo 1733067 7609679 := bstep (se 1 (by rfl) ⟨5707259, by rfl⟩ : syracuseStep 7609679 = 11414519) B11414519
theorem B5073119 : Blo 1733067 5073119 := bstep (se 1 (by rfl) ⟨3804839, by rfl⟩ : syracuseStep 5073119 = 7609679) B7609679
theorem B133584353 : Blo 1733067 133584353 := bstep (se 2 (by rfl) ⟨50094132, by rfl⟩ : syracuseStep 133584353 = 100188265) B100188265
theorem B89056235 : Blo 1733067 89056235 := bstep (se 1 (by rfl) ⟨66792176, by rfl⟩ : syracuseStep 89056235 = 133584353) B133584353
theorem B3382079 : Blo 1733067 3382079 := bstep (se 1 (by rfl) ⟨2536559, by rfl⟩ : syracuseStep 3382079 = 5073119) B5073119
theorem B59370823 : Blo 1733067 59370823 := bstep (se 1 (by rfl) ⟨44528117, by rfl⟩ : syracuseStep 59370823 = 89056235) B89056235
theorem B9018877 : Blo 1733067 9018877 := bstep (se 3 (by rfl) ⟨1691039, by rfl⟩ : syracuseStep 9018877 = 3382079) B3382079
theorem B79161097 : Blo 1733067 79161097 := bstep (se 2 (by rfl) ⟨29685411, by rfl⟩ : syracuseStep 79161097 = 59370823) B59370823
theorem B12025169 : Blo 1733067 12025169 := bstep (se 2 (by rfl) ⟨4509438, by rfl⟩ : syracuseStep 12025169 = 9018877) B9018877
theorem B105548129 : Blo 1733067 105548129 := bstep (se 2 (by rfl) ⟨39580548, by rfl⟩ : syracuseStep 105548129 = 79161097) B79161097
theorem B8016779 : Blo 1733067 8016779 := bstep (se 1 (by rfl) ⟨6012584, by rfl⟩ : syracuseStep 8016779 = 12025169) B12025169
theorem B5344519 : Blo 1733067 5344519 := bstep (se 1 (by rfl) ⟨4008389, by rfl⟩ : syracuseStep 5344519 = 8016779) B8016779
theorem B70365419 : Blo 1733067 70365419 := bstep (se 1 (by rfl) ⟨52774064, by rfl⟩ : syracuseStep 70365419 = 105548129) B105548129
theorem B114016405 : Blo 1733067 114016405 := bstep (se 6 (by rfl) ⟨2672259, by rfl⟩ : syracuseStep 114016405 = 5344519) B5344519
theorem B46910279 : Blo 1733067 46910279 := bstep (se 1 (by rfl) ⟨35182709, by rfl⟩ : syracuseStep 46910279 = 70365419) B70365419
theorem B125094077 : Blo 1733067 125094077 := bstep (se 3 (by rfl) ⟨23455139, by rfl⟩ : syracuseStep 125094077 = 46910279) B46910279
theorem B152021873 : Blo 1733067 152021873 := bstep (se 2 (by rfl) ⟨57008202, by rfl⟩ : syracuseStep 152021873 = 114016405) B114016405
theorem B83396051 : Blo 1733067 83396051 := bstep (se 1 (by rfl) ⟨62547038, by rfl⟩ : syracuseStep 83396051 = 125094077) B125094077
theorem B405391661 : Blo 1733067 405391661 := bstep (se 3 (by rfl) ⟨76010936, by rfl⟩ : syracuseStep 405391661 = 152021873) B152021873
theorem B55597367 : Blo 1733067 55597367 := bstep (se 1 (by rfl) ⟨41698025, by rfl⟩ : syracuseStep 55597367 = 83396051) B83396051
theorem B270261107 : Blo 1733067 270261107 := bstep (se 1 (by rfl) ⟨202695830, by rfl⟩ : syracuseStep 270261107 = 405391661) B405391661
theorem B37064911 : Blo 1733067 37064911 := bstep (se 1 (by rfl) ⟨27798683, by rfl⟩ : syracuseStep 37064911 = 55597367) B55597367
theorem B180174071 : Blo 1733067 180174071 := bstep (se 1 (by rfl) ⟨135130553, by rfl⟩ : syracuseStep 180174071 = 270261107) B270261107
theorem B120116047 : Blo 1733067 120116047 := bstep (se 1 (by rfl) ⟨90087035, by rfl⟩ : syracuseStep 120116047 = 180174071) B180174071
theorem B49419881 : Blo 1733067 49419881 := bstep (se 2 (by rfl) ⟨18532455, by rfl⟩ : syracuseStep 49419881 = 37064911) B37064911
theorem B160154729 : Blo 1733067 160154729 := bstep (se 2 (by rfl) ⟨60058023, by rfl⟩ : syracuseStep 160154729 = 120116047) B120116047
theorem B32946587 : Blo 1733067 32946587 := bstep (se 1 (by rfl) ⟨24709940, by rfl⟩ : syracuseStep 32946587 = 49419881) B49419881
theorem B21964391 : Blo 1733067 21964391 := bstep (se 1 (by rfl) ⟨16473293, by rfl⟩ : syracuseStep 21964391 = 32946587) B32946587
theorem B106769819 : Blo 1733067 106769819 := bstep (se 1 (by rfl) ⟨80077364, by rfl⟩ : syracuseStep 106769819 = 160154729) B160154729
theorem B14642927 : Blo 1733067 14642927 := bstep (se 1 (by rfl) ⟨10982195, by rfl⟩ : syracuseStep 14642927 = 21964391) B21964391
theorem B71179879 : Blo 1733067 71179879 := bstep (se 1 (by rfl) ⟨53384909, by rfl⟩ : syracuseStep 71179879 = 106769819) B106769819
theorem B94906505 : Blo 1733067 94906505 := bstep (se 2 (by rfl) ⟨35589939, by rfl⟩ : syracuseStep 94906505 = 71179879) B71179879
theorem B9761951 : Blo 1733067 9761951 := bstep (se 1 (by rfl) ⟨7321463, by rfl⟩ : syracuseStep 9761951 = 14642927) B14642927
theorem B253084013 : Blo 1733067 253084013 := bstep (se 3 (by rfl) ⟨47453252, by rfl⟩ : syracuseStep 253084013 = 94906505) B94906505
theorem B6507967 : Blo 1733067 6507967 := bstep (se 1 (by rfl) ⟨4880975, by rfl⟩ : syracuseStep 6507967 = 9761951) B9761951
theorem B168722675 : Blo 1733067 168722675 := bstep (se 1 (by rfl) ⟨126542006, by rfl⟩ : syracuseStep 168722675 = 253084013) B253084013
theorem B8677289 : Blo 1733067 8677289 := bstep (se 2 (by rfl) ⟨3253983, by rfl⟩ : syracuseStep 8677289 = 6507967) B6507967
theorem B5784859 : Blo 1733067 5784859 := bstep (se 1 (by rfl) ⟨4338644, by rfl⟩ : syracuseStep 5784859 = 8677289) B8677289
theorem B112481783 : Blo 1733067 112481783 := bstep (se 1 (by rfl) ⟨84361337, by rfl⟩ : syracuseStep 112481783 = 168722675) B168722675
theorem B7713145 : Blo 1733067 7713145 := bstep (se 2 (by rfl) ⟨2892429, by rfl⟩ : syracuseStep 7713145 = 5784859) B5784859
theorem B74987855 : Blo 1733067 74987855 := bstep (se 1 (by rfl) ⟨56240891, by rfl⟩ : syracuseStep 74987855 = 112481783) B112481783
theorem B10284193 : Blo 1733067 10284193 := bstep (se 2 (by rfl) ⟨3856572, by rfl⟩ : syracuseStep 10284193 = 7713145) B7713145
theorem B49991903 : Blo 1733067 49991903 := bstep (se 1 (by rfl) ⟨37493927, by rfl⟩ : syracuseStep 49991903 = 74987855) B74987855
theorem B33327935 : Blo 1733067 33327935 := bstep (se 1 (by rfl) ⟨24995951, by rfl⟩ : syracuseStep 33327935 = 49991903) B49991903
theorem B13712257 : Blo 1733067 13712257 := bstep (se 2 (by rfl) ⟨5142096, by rfl⟩ : syracuseStep 13712257 = 10284193) B10284193
theorem B22218623 : Blo 1733067 22218623 := bstep (se 1 (by rfl) ⟨16663967, by rfl⟩ : syracuseStep 22218623 = 33327935) B33327935
theorem B18283009 : Blo 1733067 18283009 := bstep (se 2 (by rfl) ⟨6856128, by rfl⟩ : syracuseStep 18283009 = 13712257) B13712257
theorem B14812415 : Blo 1733067 14812415 := bstep (se 1 (by rfl) ⟨11109311, by rfl⟩ : syracuseStep 14812415 = 22218623) B22218623
theorem B24377345 : Blo 1733067 24377345 := bstep (se 2 (by rfl) ⟨9141504, by rfl⟩ : syracuseStep 24377345 = 18283009) B18283009
theorem B9874943 : Blo 1733067 9874943 := bstep (se 1 (by rfl) ⟨7406207, by rfl⟩ : syracuseStep 9874943 = 14812415) B14812415
theorem B16251563 : Blo 1733067 16251563 := bstep (se 1 (by rfl) ⟨12188672, by rfl⟩ : syracuseStep 16251563 = 24377345) B24377345
theorem B43337501 : Blo 1733067 43337501 := bstep (se 3 (by rfl) ⟨8125781, by rfl⟩ : syracuseStep 43337501 = 16251563) B16251563
theorem B6583295 : Blo 1733067 6583295 := bstep (se 1 (by rfl) ⟨4937471, by rfl⟩ : syracuseStep 6583295 = 9874943) B9874943
theorem B4388863 : Blo 1733067 4388863 := bstep (se 1 (by rfl) ⟨3291647, by rfl⟩ : syracuseStep 4388863 = 6583295) B6583295
theorem B28891667 : Blo 1733067 28891667 := bstep (se 1 (by rfl) ⟨21668750, by rfl⟩ : syracuseStep 28891667 = 43337501) B43337501
theorem B19261111 : Blo 1733067 19261111 := bstep (se 1 (by rfl) ⟨14445833, by rfl⟩ : syracuseStep 19261111 = 28891667) B28891667
theorem B5851817 : Blo 1733067 5851817 := bstep (se 2 (by rfl) ⟨2194431, by rfl⟩ : syracuseStep 5851817 = 4388863) B4388863
theorem B3901211 : Blo 1733067 3901211 := bstep (se 1 (by rfl) ⟨2925908, by rfl⟩ : syracuseStep 3901211 = 5851817) B5851817
theorem B25681481 : Blo 1733067 25681481 := bstep (se 2 (by rfl) ⟨9630555, by rfl⟩ : syracuseStep 25681481 = 19261111) B19261111
theorem B2600807 : Blo 1733067 2600807 := bstep (se 1 (by rfl) ⟨1950605, by rfl⟩ : syracuseStep 2600807 = 3901211) B3901211
theorem B17120987 : Blo 1733067 17120987 := bstep (se 1 (by rfl) ⟨12840740, by rfl⟩ : syracuseStep 17120987 = 25681481) B25681481
theorem B11413991 : Blo 1733067 11413991 := bstep (se 1 (by rfl) ⟨8560493, by rfl⟩ : syracuseStep 11413991 = 17120987) B17120987
theorem B1733871 : Blo 1733067 1733871 := bstep (se 1 (by rfl) ⟨1300403, by rfl⟩ : syracuseStep 1733871 = 2600807) B2600807
theorem B30437309 : Blo 1733067 30437309 := bstep (se 3 (by rfl) ⟨5706995, by rfl⟩ : syracuseStep 30437309 = 11413991) B11413991
theorem B20291539 : Blo 1733067 20291539 := bstep (se 1 (by rfl) ⟨15218654, by rfl⟩ : syracuseStep 20291539 = 30437309) B30437309
theorem B27055385 : Blo 1733067 27055385 := bstep (se 2 (by rfl) ⟨10145769, by rfl⟩ : syracuseStep 27055385 = 20291539) B20291539
theorem B18036923 : Blo 1733067 18036923 := bstep (se 1 (by rfl) ⟨13527692, by rfl⟩ : syracuseStep 18036923 = 27055385) B27055385
theorem B48098461 : Blo 1733067 48098461 := bstep (se 3 (by rfl) ⟨9018461, by rfl⟩ : syracuseStep 48098461 = 18036923) B18036923
theorem B64131281 : Blo 1733067 64131281 := bstep (se 2 (by rfl) ⟨24049230, by rfl⟩ : syracuseStep 64131281 = 48098461) B48098461
theorem B42754187 : Blo 1733067 42754187 := bstep (se 1 (by rfl) ⟨32065640, by rfl⟩ : syracuseStep 42754187 = 64131281) B64131281
theorem B114011165 : Blo 1733067 114011165 := bstep (se 3 (by rfl) ⟨21377093, by rfl⟩ : syracuseStep 114011165 = 42754187) B42754187
theorem B76007443 : Blo 1733067 76007443 := bstep (se 1 (by rfl) ⟨57005582, by rfl⟩ : syracuseStep 76007443 = 114011165) B114011165
theorem B101343257 : Blo 1733067 101343257 := bstep (se 2 (by rfl) ⟨38003721, by rfl⟩ : syracuseStep 101343257 = 76007443) B76007443
theorem B67562171 : Blo 1733067 67562171 := bstep (se 1 (by rfl) ⟨50671628, by rfl⟩ : syracuseStep 67562171 = 101343257) B101343257
theorem B45041447 : Blo 1733067 45041447 := bstep (se 1 (by rfl) ⟨33781085, by rfl⟩ : syracuseStep 45041447 = 67562171) B67562171
theorem B30027631 : Blo 1733067 30027631 := bstep (se 1 (by rfl) ⟨22520723, by rfl⟩ : syracuseStep 30027631 = 45041447) B45041447
theorem B40036841 : Blo 1733067 40036841 := bstep (se 2 (by rfl) ⟨15013815, by rfl⟩ : syracuseStep 40036841 = 30027631) B30027631
theorem B26691227 : Blo 1733067 26691227 := bstep (se 1 (by rfl) ⟨20018420, by rfl⟩ : syracuseStep 26691227 = 40036841) B40036841
theorem B17794151 : Blo 1733067 17794151 := bstep (se 1 (by rfl) ⟨13345613, by rfl⟩ : syracuseStep 17794151 = 26691227) B26691227
theorem B11862767 : Blo 1733067 11862767 := bstep (se 1 (by rfl) ⟨8897075, by rfl⟩ : syracuseStep 11862767 = 17794151) B17794151
theorem B7908511 : Blo 1733067 7908511 := bstep (se 1 (by rfl) ⟨5931383, by rfl⟩ : syracuseStep 7908511 = 11862767) B11862767
theorem B10544681 : Blo 1733067 10544681 := bstep (se 2 (by rfl) ⟨3954255, by rfl⟩ : syracuseStep 10544681 = 7908511) B7908511
theorem B28119149 : Blo 1733067 28119149 := bstep (se 3 (by rfl) ⟨5272340, by rfl⟩ : syracuseStep 28119149 = 10544681) B10544681
theorem B18746099 : Blo 1733067 18746099 := bstep (se 1 (by rfl) ⟨14059574, by rfl⟩ : syracuseStep 18746099 = 28119149) B28119149
theorem B12497399 : Blo 1733067 12497399 := bstep (se 1 (by rfl) ⟨9373049, by rfl⟩ : syracuseStep 12497399 = 18746099) B18746099
theorem B8331599 : Blo 1733067 8331599 := bstep (se 1 (by rfl) ⟨6248699, by rfl⟩ : syracuseStep 8331599 = 12497399) B12497399
theorem B22217597 : Blo 1733067 22217597 := bstep (se 3 (by rfl) ⟨4165799, by rfl⟩ : syracuseStep 22217597 = 8331599) B8331599
theorem B14811731 : Blo 1733067 14811731 := bstep (se 1 (by rfl) ⟨11108798, by rfl⟩ : syracuseStep 14811731 = 22217597) B22217597
theorem B9874487 : Blo 1733067 9874487 := bstep (se 1 (by rfl) ⟨7405865, by rfl⟩ : syracuseStep 9874487 = 14811731) B14811731
theorem B6582991 : Blo 1733067 6582991 := bstep (se 1 (by rfl) ⟨4937243, by rfl⟩ : syracuseStep 6582991 = 9874487) B9874487
theorem B8777321 : Blo 1733067 8777321 := bstep (se 2 (by rfl) ⟨3291495, by rfl⟩ : syracuseStep 8777321 = 6582991) B6582991
theorem B5851547 : Blo 1733067 5851547 := bstep (se 1 (by rfl) ⟨4388660, by rfl⟩ : syracuseStep 5851547 = 8777321) B8777321
theorem B3901031 : Blo 1733067 3901031 := bstep (se 1 (by rfl) ⟨2925773, by rfl⟩ : syracuseStep 3901031 = 5851547) B5851547
theorem B2600687 : Blo 1733067 2600687 := bstep (se 1 (by rfl) ⟨1950515, by rfl⟩ : syracuseStep 2600687 = 3901031) B3901031
theorem B1733791 : Blo 1733067 1733791 := bstep (se 1 (by rfl) ⟨1300343, by rfl⟩ : syracuseStep 1733791 = 2600687) B2600687

theorem C0 (j : ℕ) (h1 : 433266 ≤ j) (h2 : j ≤ 433766) : Blo 1733067 (4 * j + 3) := by
  interval_cases j
  · exact B1733067
  · exact B1733071
  · exact B1733075
  · exact B1733079
  · exact B1733083
  · exact B1733087
  · exact B1733091
  · exact B1733095
  · exact B1733099
  · exact B1733103
  · exact B1733107
  · exact B1733111
  · exact B1733115
  · exact B1733119
  · exact B1733123
  · exact B1733127
  · exact B1733131
  · exact B1733135
  · exact B1733139
  · exact B1733143
  · exact B1733147
  · exact B1733151
  · exact B1733155
  · exact B1733159
  · exact B1733163
  · exact B1733167
  · exact B1733171
  · exact B1733175
  · exact B1733179
  · exact B1733183
  · exact B1733187
  · exact B1733191
  · exact B1733195
  · exact B1733199
  · exact B1733203
  · exact B1733207
  · exact B1733211
  · exact B1733215
  · exact B1733219
  · exact B1733223
  · exact B1733227
  · exact B1733231
  · exact B1733235
  · exact B1733239
  · exact B1733243
  · exact B1733247
  · exact B1733251
  · exact B1733255
  · exact B1733259
  · exact B1733263
  · exact B1733267
  · exact B1733271
  · exact B1733275
  · exact B1733279
  · exact B1733283
  · exact B1733287
  · exact B1733291
  · exact B1733295
  · exact B1733299
  · exact B1733303
  · exact B1733307
  · exact B1733311
  · exact B1733315
  · exact B1733319
  · exact B1733323
  · exact B1733327
  · exact B1733331
  · exact B1733335
  · exact B1733339
  · exact B1733343
  · exact B1733347
  · exact B1733351
  · exact B1733355
  · exact B1733359
  · exact B1733363
  · exact B1733367
  · exact B1733371
  · exact B1733375
  · exact B1733379
  · exact B1733383
  · exact B1733387
  · exact B1733391
  · exact B1733395
  · exact B1733399
  · exact B1733403
  · exact B1733407
  · exact B1733411
  · exact B1733415
  · exact B1733419
  · exact B1733423
  · exact B1733427
  · exact B1733431
  · exact B1733435
  · exact B1733439
  · exact B1733443
  · exact B1733447
  · exact B1733451
  · exact B1733455
  · exact B1733459
  · exact B1733463
  · exact B1733467
  · exact B1733471
  · exact B1733475
  · exact B1733479
  · exact B1733483
  · exact B1733487
  · exact B1733491
  · exact B1733495
  · exact B1733499
  · exact B1733503
  · exact B1733507
  · exact B1733511
  · exact B1733515
  · exact B1733519
  · exact B1733523
  · exact B1733527
  · exact B1733531
  · exact B1733535
  · exact B1733539
  · exact B1733543
  · exact B1733547
  · exact B1733551
  · exact B1733555
  · exact B1733559
  · exact B1733563
  · exact B1733567
  · exact B1733571
  · exact B1733575
  · exact B1733579
  · exact B1733583
  · exact B1733587
  · exact B1733591
  · exact B1733595
  · exact B1733599
  · exact B1733603
  · exact B1733607
  · exact B1733611
  · exact B1733615
  · exact B1733619
  · exact B1733623
  · exact B1733627
  · exact B1733631
  · exact B1733635
  · exact B1733639
  · exact B1733643
  · exact B1733647
  · exact B1733651
  · exact B1733655
  · exact B1733659
  · exact B1733663
  · exact B1733667
  · exact B1733671
  · exact B1733675
  · exact B1733679
  · exact B1733683
  · exact B1733687
  · exact B1733691
  · exact B1733695
  · exact B1733699
  · exact B1733703
  · exact B1733707
  · exact B1733711
  · exact B1733715
  · exact B1733719
  · exact B1733723
  · exact B1733727
  · exact B1733731
  · exact B1733735
  · exact B1733739
  · exact B1733743
  · exact B1733747
  · exact B1733751
  · exact B1733755
  · exact B1733759
  · exact B1733763
  · exact B1733767
  · exact B1733771
  · exact B1733775
  · exact B1733779
  · exact B1733783
  · exact B1733787
  · exact B1733791
  · exact B1733795
  · exact B1733799
  · exact B1733803
  · exact B1733807
  · exact B1733811
  · exact B1733815
  · exact B1733819
  · exact B1733823
  · exact B1733827
  · exact B1733831
  · exact B1733835
  · exact B1733839
  · exact B1733843
  · exact B1733847
  · exact B1733851
  · exact B1733855
  · exact B1733859
  · exact B1733863
  · exact B1733867
  · exact B1733871
  · exact B1733875
  · exact B1733879
  · exact B1733883
  · exact B1733887
  · exact B1733891
  · exact B1733895
  · exact B1733899
  · exact B1733903
  · exact B1733907
  · exact B1733911
  · exact B1733915
  · exact B1733919
  · exact B1733923
  · exact B1733927
  · exact B1733931
  · exact B1733935
  · exact B1733939
  · exact B1733943
  · exact B1733947
  · exact B1733951
  · exact B1733955
  · exact B1733959
  · exact B1733963
  · exact B1733967
  · exact B1733971
  · exact B1733975
  · exact B1733979
  · exact B1733983
  · exact B1733987
  · exact B1733991
  · exact B1733995
  · exact B1733999
  · exact B1734003
  · exact B1734007
  · exact B1734011
  · exact B1734015
  · exact B1734019
  · exact B1734023
  · exact B1734027
  · exact B1734031
  · exact B1734035
  · exact B1734039
  · exact B1734043
  · exact B1734047
  · exact B1734051
  · exact B1734055
  · exact B1734059
  · exact B1734063
  · exact B1734067
  · exact B1734071
  · exact B1734075
  · exact B1734079
  · exact B1734083
  · exact B1734087
  · exact B1734091
  · exact B1734095
  · exact B1734099
  · exact B1734103
  · exact B1734107
  · exact B1734111
  · exact B1734115
  · exact B1734119
  · exact B1734123
  · exact B1734127
  · exact B1734131
  · exact B1734135
  · exact B1734139
  · exact B1734143
  · exact B1734147
  · exact B1734151
  · exact B1734155
  · exact B1734159
  · exact B1734163
  · exact B1734167
  · exact B1734171
  · exact B1734175
  · exact B1734179
  · exact B1734183
  · exact B1734187
  · exact B1734191
  · exact B1734195
  · exact B1734199
  · exact B1734203
  · exact B1734207
  · exact B1734211
  · exact B1734215
  · exact B1734219
  · exact B1734223
  · exact B1734227
  · exact B1734231
  · exact B1734235
  · exact B1734239
  · exact B1734243
  · exact B1734247
  · exact B1734251
  · exact B1734255
  · exact B1734259
  · exact B1734263
  · exact B1734267
  · exact B1734271
  · exact B1734275
  · exact B1734279
  · exact B1734283
  · exact B1734287
  · exact B1734291
  · exact B1734295
  · exact B1734299
  · exact B1734303
  · exact B1734307
  · exact B1734311
  · exact B1734315
  · exact B1734319
  · exact B1734323
  · exact B1734327
  · exact B1734331
  · exact B1734335
  · exact B1734339
  · exact B1734343
  · exact B1734347
  · exact B1734351
  · exact B1734355
  · exact B1734359
  · exact B1734363
  · exact B1734367
  · exact B1734371
  · exact B1734375
  · exact B1734379
  · exact B1734383
  · exact B1734387
  · exact B1734391
  · exact B1734395
  · exact B1734399
  · exact B1734403
  · exact B1734407
  · exact B1734411
  · exact B1734415
  · exact B1734419
  · exact B1734423
  · exact B1734427
  · exact B1734431
  · exact B1734435
  · exact B1734439
  · exact B1734443
  · exact B1734447
  · exact B1734451
  · exact B1734455
  · exact B1734459
  · exact B1734463
  · exact B1734467
  · exact B1734471
  · exact B1734475
  · exact B1734479
  · exact B1734483
  · exact B1734487
  · exact B1734491
  · exact B1734495
  · exact B1734499
  · exact B1734503
  · exact B1734507
  · exact B1734511
  · exact B1734515
  · exact B1734519
  · exact B1734523
  · exact B1734527
  · exact B1734531
  · exact B1734535
  · exact B1734539
  · exact B1734543
  · exact B1734547
  · exact B1734551
  · exact B1734555
  · exact B1734559
  · exact B1734563
  · exact B1734567
  · exact B1734571
  · exact B1734575
  · exact B1734579
  · exact B1734583
  · exact B1734587
  · exact B1734591
  · exact B1734595
  · exact B1734599
  · exact B1734603
  · exact B1734607
  · exact B1734611
  · exact B1734615
  · exact B1734619
  · exact B1734623
  · exact B1734627
  · exact B1734631
  · exact B1734635
  · exact B1734639
  · exact B1734643
  · exact B1734647
  · exact B1734651
  · exact B1734655
  · exact B1734659
  · exact B1734663
  · exact B1734667
  · exact B1734671
  · exact B1734675
  · exact B1734679
  · exact B1734683
  · exact B1734687
  · exact B1734691
  · exact B1734695
  · exact B1734699
  · exact B1734703
  · exact B1734707
  · exact B1734711
  · exact B1734715
  · exact B1734719
  · exact B1734723
  · exact B1734727
  · exact B1734731
  · exact B1734735
  · exact B1734739
  · exact B1734743
  · exact B1734747
  · exact B1734751
  · exact B1734755
  · exact B1734759
  · exact B1734763
  · exact B1734767
  · exact B1734771
  · exact B1734775
  · exact B1734779
  · exact B1734783
  · exact B1734787
  · exact B1734791
  · exact B1734795
  · exact B1734799
  · exact B1734803
  · exact B1734807
  · exact B1734811
  · exact B1734815
  · exact B1734819
  · exact B1734823
  · exact B1734827
  · exact B1734831
  · exact B1734835
  · exact B1734839
  · exact B1734843
  · exact B1734847
  · exact B1734851
  · exact B1734855
  · exact B1734859
  · exact B1734863
  · exact B1734867
  · exact B1734871
  · exact B1734875
  · exact B1734879
  · exact B1734883
  · exact B1734887
  · exact B1734891
  · exact B1734895
  · exact B1734899
  · exact B1734903
  · exact B1734907
  · exact B1734911
  · exact B1734915
  · exact B1734919
  · exact B1734923
  · exact B1734927
  · exact B1734931
  · exact B1734935
  · exact B1734939
  · exact B1734943
  · exact B1734947
  · exact B1734951
  · exact B1734955
  · exact B1734959
  · exact B1734963
  · exact B1734967
  · exact B1734971
  · exact B1734975
  · exact B1734979
  · exact B1734983
  · exact B1734987
  · exact B1734991
  · exact B1734995
  · exact B1734999
  · exact B1735003
  · exact B1735007
  · exact B1735011
  · exact B1735015
  · exact B1735019
  · exact B1735023
  · exact B1735027
  · exact B1735031
  · exact B1735035
  · exact B1735039
  · exact B1735043
  · exact B1735047
  · exact B1735051
  · exact B1735055
  · exact B1735059
  · exact B1735063
  · exact B1735067

theorem solution (m : ℕ) (hlo : 1733067 ≤ m) (hhi : m ≤ 1735067) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 433266 ≤ j := by omega
    have hj2 : j ≤ 433766 := by omega
    have hb : Blo 1733067 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
