-- Prove2me | solution 1 for syracuse_descends_range_1391515_1393515
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:36.677349+00:00
-- url     : https://prove2.me/submissions/a4a77acb-dcdd-4328-8baf-c24cb40a44ac

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


theorem B2088965 : Blo 1391515 2088965 := bbase (se 4 (by rfl) ⟨195840, by rfl⟩ : syracuseStep 2088965 = 391681) (by norm_num)
theorem B7053317 : Blo 1391515 7053317 := bbase (se 4 (by rfl) ⟨661248, by rfl⟩ : syracuseStep 7053317 = 1322497) (by norm_num)
theorem B2088989 : Blo 1391515 2088989 := bbase (se 3 (by rfl) ⟨391685, by rfl⟩ : syracuseStep 2088989 = 783371) (by norm_num)
theorem B5947445 : Blo 1391515 5947445 := bbase (se 5 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 5947445 = 557573) (by norm_num)
theorem B2089013 : Blo 1391515 2089013 := bbase (se 5 (by rfl) ⟨97922, by rfl⟩ : syracuseStep 2089013 = 195845) (by norm_num)
theorem B3522629 : Blo 1391515 3522629 := bbase (se 4 (by rfl) ⟨330246, by rfl⟩ : syracuseStep 3522629 = 660493) (by norm_num)
theorem B2351173 : Blo 1391515 2351173 := bbase (se 4 (by rfl) ⟨220422, by rfl⟩ : syracuseStep 2351173 = 440845) (by norm_num)
theorem B2089037 : Blo 1391515 2089037 := bbase (se 3 (by rfl) ⟨391694, by rfl⟩ : syracuseStep 2089037 = 783389) (by norm_num)
theorem B1761365 : Blo 1391515 1761365 := bbase (se 8 (by rfl) ⟨10320, by rfl⟩ : syracuseStep 1761365 = 20641) (by norm_num)
theorem B2089061 : Blo 1391515 2089061 := bbase (se 4 (by rfl) ⟨195849, by rfl⟩ : syracuseStep 2089061 = 391699) (by norm_num)
theorem B2089085 : Blo 1391515 2089085 := bbase (se 3 (by rfl) ⟨391703, by rfl⟩ : syracuseStep 2089085 = 783407) (by norm_num)
theorem B1761421 : Blo 1391515 1761421 := bbase (se 3 (by rfl) ⟨330266, by rfl⟩ : syracuseStep 1761421 = 660533) (by norm_num)
theorem B2089109 : Blo 1391515 2089109 := bbase (se 6 (by rfl) ⟨48963, by rfl⟩ : syracuseStep 2089109 = 97927) (by norm_num)
theorem B2351261 : Blo 1391515 2351261 := bbase (se 3 (by rfl) ⟨440861, by rfl⟩ : syracuseStep 2351261 = 881723) (by norm_num)
theorem B4702373 : Blo 1391515 4702373 := bbase (se 4 (by rfl) ⟨440847, by rfl⟩ : syracuseStep 4702373 = 881695) (by norm_num)
theorem B2089133 : Blo 1391515 2089133 := bbase (se 3 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 2089133 = 783425) (by norm_num)
theorem B2089157 : Blo 1391515 2089157 := bbase (se 4 (by rfl) ⟨195858, by rfl⟩ : syracuseStep 2089157 = 391717) (by norm_num)
theorem B2678989 : Blo 1391515 2678989 := bbase (se 3 (by rfl) ⟨502310, by rfl⟩ : syracuseStep 2678989 = 1004621) (by norm_num)
theorem B6029525 : Blo 1391515 6029525 := bbase (se 7 (by rfl) ⟨70658, by rfl⟩ : syracuseStep 6029525 = 141317) (by norm_num)
theorem B2089181 : Blo 1391515 2089181 := bbase (se 3 (by rfl) ⟨391721, by rfl⟩ : syracuseStep 2089181 = 783443) (by norm_num)
theorem B1761517 : Blo 1391515 1761517 := bbase (se 3 (by rfl) ⟨330284, by rfl⟩ : syracuseStep 1761517 = 660569) (by norm_num)
theorem B2089205 : Blo 1391515 2089205 := bbase (se 5 (by rfl) ⟨97931, by rfl⟩ : syracuseStep 2089205 = 195863) (by norm_num)
theorem B2089229 : Blo 1391515 2089229 := bbase (se 3 (by rfl) ⟨391730, by rfl⟩ : syracuseStep 2089229 = 783461) (by norm_num)
theorem B2351389 : Blo 1391515 2351389 := bbase (se 3 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 2351389 = 881771) (by norm_num)
theorem B2089253 : Blo 1391515 2089253 := bbase (se 4 (by rfl) ⟨195867, by rfl⟩ : syracuseStep 2089253 = 391735) (by norm_num)
theorem B3965237 : Blo 1391515 3965237 := bbase (se 5 (by rfl) ⟨185870, by rfl⟩ : syracuseStep 3965237 = 371741) (by norm_num)
theorem B2974013 : Blo 1391515 2974013 := bbase (se 3 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 2974013 = 1115255) (by norm_num)
theorem B2089277 : Blo 1391515 2089277 := bbase (se 3 (by rfl) ⟨391739, by rfl⟩ : syracuseStep 2089277 = 783479) (by norm_num)
theorem B2089301 : Blo 1391515 2089301 := bbase (se 10 (by rfl) ⟨3060, by rfl⟩ : syracuseStep 2089301 = 6121) (by norm_num)
theorem B2089325 : Blo 1391515 2089325 := bbase (se 3 (by rfl) ⟨391748, by rfl⟩ : syracuseStep 2089325 = 783497) (by norm_num)
theorem B2351477 : Blo 1391515 2351477 := bbase (se 5 (by rfl) ⟨110225, by rfl⟩ : syracuseStep 2351477 = 220451) (by norm_num)
theorem B2089349 : Blo 1391515 2089349 := bbase (se 4 (by rfl) ⟨195876, by rfl⟩ : syracuseStep 2089349 = 391753) (by norm_num)
theorem B1761689 : Blo 1391515 1761689 := bbase (se 2 (by rfl) ⟨660633, by rfl⟩ : syracuseStep 1761689 = 1321267) (by norm_num)
theorem B3522973 : Blo 1391515 3522973 := bbase (se 3 (by rfl) ⟨660557, by rfl⟩ : syracuseStep 3522973 = 1321115) (by norm_num)
theorem B2089373 : Blo 1391515 2089373 := bbase (se 3 (by rfl) ⟨391757, by rfl⟩ : syracuseStep 2089373 = 783515) (by norm_num)
theorem B7045541 : Blo 1391515 7045541 := bbase (se 4 (by rfl) ⟨660519, by rfl⟩ : syracuseStep 7045541 = 1321039) (by norm_num)
theorem B2974133 : Blo 1391515 2974133 := bbase (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) (by norm_num)
theorem B2089397 : Blo 1391515 2089397 := bbase (se 5 (by rfl) ⟨97940, by rfl⟩ : syracuseStep 2089397 = 195881) (by norm_num)
theorem B2089421 : Blo 1391515 2089421 := bbase (se 3 (by rfl) ⟨391766, by rfl⟩ : syracuseStep 2089421 = 783533) (by norm_num)
theorem B1761745 : Blo 1391515 1761745 := bbase (se 2 (by rfl) ⟨660654, by rfl⟩ : syracuseStep 1761745 = 1321309) (by norm_num)
theorem B2089445 : Blo 1391515 2089445 := bbase (se 4 (by rfl) ⟨195885, by rfl⟩ : syracuseStep 2089445 = 391771) (by norm_num)
theorem B2089469 : Blo 1391515 2089469 := bbase (se 3 (by rfl) ⟨391775, by rfl⟩ : syracuseStep 2089469 = 783551) (by norm_num)
theorem B3523085 : Blo 1391515 3523085 := bbase (se 3 (by rfl) ⟨660578, by rfl⟩ : syracuseStep 3523085 = 1321157) (by norm_num)
theorem B2089493 : Blo 1391515 2089493 := bbase (se 6 (by rfl) ⟨48972, by rfl⟩ : syracuseStep 2089493 = 97945) (by norm_num)
theorem B2089517 : Blo 1391515 2089517 := bbase (se 3 (by rfl) ⟨391784, by rfl⟩ : syracuseStep 2089517 = 783569) (by norm_num)
theorem B1761841 : Blo 1391515 1761841 := bbase (se 2 (by rfl) ⟨660690, by rfl⟩ : syracuseStep 1761841 = 1321381) (by norm_num)
theorem B2089541 : Blo 1391515 2089541 := bbase (se 4 (by rfl) ⟨195894, by rfl⟩ : syracuseStep 2089541 = 391789) (by norm_num)
theorem B4702805 : Blo 1391515 4702805 := bbase (se 8 (by rfl) ⟨27555, by rfl⟩ : syracuseStep 4702805 = 55111) (by norm_num)
theorem B2089565 : Blo 1391515 2089565 := bbase (se 3 (by rfl) ⟨391793, by rfl⟩ : syracuseStep 2089565 = 783587) (by norm_num)
theorem B2089589 : Blo 1391515 2089589 := bbase (se 5 (by rfl) ⟨97949, by rfl⟩ : syracuseStep 2089589 = 195899) (by norm_num)
theorem B2089613 : Blo 1391515 2089613 := bbase (se 3 (by rfl) ⟨391802, by rfl⟩ : syracuseStep 2089613 = 783605) (by norm_num)
theorem B2089637 : Blo 1391515 2089637 := bbase (se 4 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 2089637 = 391807) (by norm_num)
theorem B2089661 : Blo 1391515 2089661 := bbase (se 3 (by rfl) ⟨391811, by rfl⟩ : syracuseStep 2089661 = 783623) (by norm_num)
theorem B3523277 : Blo 1391515 3523277 := bbase (se 3 (by rfl) ⟨660614, by rfl⟩ : syracuseStep 3523277 = 1321229) (by norm_num)
theorem B3572437 : Blo 1391515 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B2089685 : Blo 1391515 2089685 := bbase (se 7 (by rfl) ⟨24488, by rfl⟩ : syracuseStep 2089685 = 48977) (by norm_num)
theorem B1762013 : Blo 1391515 1762013 := bbase (se 3 (by rfl) ⟨330377, by rfl⟩ : syracuseStep 1762013 = 660755) (by norm_num)
theorem B3965669 : Blo 1391515 3965669 := bbase (se 4 (by rfl) ⟨371781, by rfl⟩ : syracuseStep 3965669 = 743563) (by norm_num)
theorem B2089709 : Blo 1391515 2089709 := bbase (se 3 (by rfl) ⟨391820, by rfl⟩ : syracuseStep 2089709 = 783641) (by norm_num)
theorem B1696505 : Blo 1391515 1696505 := bbase (se 2 (by rfl) ⟨636189, by rfl⟩ : syracuseStep 1696505 = 1272379) (by norm_num)
theorem B2089733 : Blo 1391515 2089733 := bbase (se 4 (by rfl) ⟨195912, by rfl⟩ : syracuseStep 2089733 = 391825) (by norm_num)
theorem B1762069 : Blo 1391515 1762069 := bbase (se 6 (by rfl) ⟨41298, by rfl⟩ : syracuseStep 1762069 = 82597) (by norm_num)
theorem B2089757 : Blo 1391515 2089757 := bbase (se 3 (by rfl) ⟨391829, by rfl⟩ : syracuseStep 2089757 = 783659) (by norm_num)
theorem B1565473 : Blo 1391515 1565473 := bbase (se 2 (by rfl) ⟨587052, by rfl⟩ : syracuseStep 1565473 = 1174105) (by norm_num)
theorem B2089781 : Blo 1391515 2089781 := bbase (se 5 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 2089781 = 195917) (by norm_num)
theorem B1565509 : Blo 1391515 1565509 := bbase (se 4 (by rfl) ⟨146766, by rfl⟩ : syracuseStep 1565509 = 293533) (by norm_num)
theorem B1672013 : Blo 1391515 1672013 := bbase (se 3 (by rfl) ⟨313502, by rfl⟩ : syracuseStep 1672013 = 627005) (by norm_num)
theorem B2089805 : Blo 1391515 2089805 := bbase (se 3 (by rfl) ⟨391838, by rfl⟩ : syracuseStep 2089805 = 783677) (by norm_num)
theorem B2089829 : Blo 1391515 2089829 := bbase (se 4 (by rfl) ⟨195921, by rfl⟩ : syracuseStep 2089829 = 391843) (by norm_num)
theorem B1565545 : Blo 1391515 1565545 := bbase (se 2 (by rfl) ⟨587079, by rfl⟩ : syracuseStep 1565545 = 1174159) (by norm_num)
theorem B1762165 : Blo 1391515 1762165 := bbase (se 5 (by rfl) ⟨82601, by rfl⟩ : syracuseStep 1762165 = 165203) (by norm_num)
theorem B2089853 : Blo 1391515 2089853 := bbase (se 3 (by rfl) ⟨391847, by rfl⟩ : syracuseStep 2089853 = 783695) (by norm_num)
theorem B5358469 : Blo 1391515 5358469 := bbase (se 4 (by rfl) ⟨502356, by rfl⟩ : syracuseStep 5358469 = 1004713) (by norm_num)
theorem B1565581 : Blo 1391515 1565581 := bbase (se 3 (by rfl) ⟨293546, by rfl⟩ : syracuseStep 1565581 = 587093) (by norm_num)
theorem B2089877 : Blo 1391515 2089877 := bbase (se 6 (by rfl) ⟨48981, by rfl⟩ : syracuseStep 2089877 = 97963) (by norm_num)
theorem B2089901 : Blo 1391515 2089901 := bbase (se 3 (by rfl) ⟨391856, by rfl⟩ : syracuseStep 2089901 = 783713) (by norm_num)
theorem B1565617 : Blo 1391515 1565617 := bbase (se 2 (by rfl) ⟨587106, by rfl⟩ : syracuseStep 1565617 = 1174213) (by norm_num)
theorem B2089925 : Blo 1391515 2089925 := bbase (se 4 (by rfl) ⟨195930, by rfl⟩ : syracuseStep 2089925 = 391861) (by norm_num)
theorem B1565653 : Blo 1391515 1565653 := bbase (se 7 (by rfl) ⟨18347, by rfl⟩ : syracuseStep 1565653 = 36695) (by norm_num)
theorem B2089949 : Blo 1391515 2089949 := bbase (se 3 (by rfl) ⟨391865, by rfl⟩ : syracuseStep 2089949 = 783731) (by norm_num)
theorem B2089973 : Blo 1391515 2089973 := bbase (se 5 (by rfl) ⟨97967, by rfl⟩ : syracuseStep 2089973 = 195935) (by norm_num)
theorem B1565689 : Blo 1391515 1565689 := bbase (se 2 (by rfl) ⟨587133, by rfl⟩ : syracuseStep 1565689 = 1174267) (by norm_num)
theorem B2507789 : Blo 1391515 2507789 := bbase (se 3 (by rfl) ⟨470210, by rfl⟩ : syracuseStep 2507789 = 940421) (by norm_num)
theorem B2089997 : Blo 1391515 2089997 := bbase (se 3 (by rfl) ⟨391874, by rfl⟩ : syracuseStep 2089997 = 783749) (by norm_num)
theorem B5284885 : Blo 1391515 5284885 := bbase (se 6 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 5284885 = 247729) (by norm_num)
theorem B8471573 : Blo 1391515 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B16950293 : Blo 1391515 16950293 := bbase (se 6 (by rfl) ⟨397272, by rfl⟩ : syracuseStep 16950293 = 794545) (by norm_num)
theorem B1565725 : Blo 1391515 1565725 := bbase (se 3 (by rfl) ⟨293573, by rfl⟩ : syracuseStep 1565725 = 587147) (by norm_num)
theorem B1762337 : Blo 1391515 1762337 := bbase (se 2 (by rfl) ⟨660876, by rfl⟩ : syracuseStep 1762337 = 1321753) (by norm_num)
theorem B3523621 : Blo 1391515 3523621 := bbase (se 4 (by rfl) ⟨330339, by rfl⟩ : syracuseStep 3523621 = 660679) (by norm_num)
theorem B2090021 : Blo 1391515 2090021 := bbase (se 4 (by rfl) ⟨195939, by rfl⟩ : syracuseStep 2090021 = 391879) (by norm_num)
theorem B2974765 : Blo 1391515 2974765 := bbase (se 3 (by rfl) ⟨557768, by rfl⟩ : syracuseStep 2974765 = 1115537) (by norm_num)
theorem B1983541 : Blo 1391515 1983541 := bbase (se 5 (by rfl) ⟨92978, by rfl⟩ : syracuseStep 1983541 = 185957) (by norm_num)
theorem B2090045 : Blo 1391515 2090045 := bbase (se 3 (by rfl) ⟨391883, by rfl⟩ : syracuseStep 2090045 = 783767) (by norm_num)
theorem B1565761 : Blo 1391515 1565761 := bbase (se 2 (by rfl) ⟨587160, by rfl⟩ : syracuseStep 1565761 = 1174321) (by norm_num)
theorem B2090069 : Blo 1391515 2090069 := bbase (se 8 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 2090069 = 24493) (by norm_num)
theorem B1762393 : Blo 1391515 1762393 := bbase (se 2 (by rfl) ⟨660897, by rfl⟩ : syracuseStep 1762393 = 1321795) (by norm_num)
theorem B1565797 : Blo 1391515 1565797 := bbase (se 4 (by rfl) ⟨146793, by rfl⟩ : syracuseStep 1565797 = 293587) (by norm_num)
theorem B2090093 : Blo 1391515 2090093 := bbase (se 3 (by rfl) ⟨391892, by rfl⟩ : syracuseStep 2090093 = 783785) (by norm_num)
theorem B13386869 : Blo 1391515 13386869 := bbase (se 5 (by rfl) ⟨627509, by rfl⟩ : syracuseStep 13386869 = 1255019) (by norm_num)
theorem B1672321 : Blo 1391515 1672321 := bbase (se 2 (by rfl) ⟨627120, by rfl⟩ : syracuseStep 1672321 = 1254241) (by norm_num)
theorem B1696897 : Blo 1391515 1696897 := bbase (se 2 (by rfl) ⟨636336, by rfl⟩ : syracuseStep 1696897 = 1272673) (by norm_num)
theorem B2090117 : Blo 1391515 2090117 := bbase (se 4 (by rfl) ⟨195948, by rfl⟩ : syracuseStep 2090117 = 391897) (by norm_num)
theorem B1565833 : Blo 1391515 1565833 := bbase (se 2 (by rfl) ⟨587187, by rfl⟩ : syracuseStep 1565833 = 1174375) (by norm_num)
theorem B3523733 : Blo 1391515 3523733 := bbase (se 6 (by rfl) ⟨82587, by rfl⟩ : syracuseStep 3523733 = 165175) (by norm_num)
theorem B23798933 : Blo 1391515 23798933 := bbase (se 6 (by rfl) ⟨557787, by rfl⟩ : syracuseStep 23798933 = 1115575) (by norm_num)
theorem B1787029 : Blo 1391515 1787029 := bbase (se 6 (by rfl) ⟨41883, by rfl⟩ : syracuseStep 1787029 = 83767) (by norm_num)
theorem B2090141 : Blo 1391515 2090141 := bbase (se 3 (by rfl) ⟨391901, by rfl⟩ : syracuseStep 2090141 = 783803) (by norm_num)
theorem B1565869 : Blo 1391515 1565869 := bbase (se 3 (by rfl) ⟨293600, by rfl⟩ : syracuseStep 1565869 = 587201) (by norm_num)
theorem B2090165 : Blo 1391515 2090165 := bbase (se 5 (by rfl) ⟨97976, by rfl⟩ : syracuseStep 2090165 = 195953) (by norm_num)
theorem B1762489 : Blo 1391515 1762489 := bbase (se 2 (by rfl) ⟨660933, by rfl⟩ : syracuseStep 1762489 = 1321867) (by norm_num)
theorem B2090189 : Blo 1391515 2090189 := bbase (se 3 (by rfl) ⟨391910, by rfl⟩ : syracuseStep 2090189 = 783821) (by norm_num)
theorem B1565905 : Blo 1391515 1565905 := bbase (se 2 (by rfl) ⟨587214, by rfl⟩ : syracuseStep 1565905 = 1174429) (by norm_num)
theorem B1672421 : Blo 1391515 1672421 := bbase (se 4 (by rfl) ⟨156789, by rfl⟩ : syracuseStep 1672421 = 313579) (by norm_num)
theorem B2090213 : Blo 1391515 2090213 := bbase (se 4 (by rfl) ⟨195957, by rfl⟩ : syracuseStep 2090213 = 391915) (by norm_num)
theorem B1565941 : Blo 1391515 1565941 := bbase (se 5 (by rfl) ⟨73403, by rfl⟩ : syracuseStep 1565941 = 146807) (by norm_num)
theorem B2090237 : Blo 1391515 2090237 := bbase (se 3 (by rfl) ⟨391919, by rfl⟩ : syracuseStep 2090237 = 783839) (by norm_num)
theorem B1549577 : Blo 1391515 1549577 := bbase (se 2 (by rfl) ⟨581091, by rfl⟩ : syracuseStep 1549577 = 1162183) (by norm_num)
theorem B7054613 : Blo 1391515 7054613 := bbase (se 6 (by rfl) ⟨165342, by rfl⟩ : syracuseStep 7054613 = 330685) (by norm_num)
theorem B2090261 : Blo 1391515 2090261 := bbase (se 6 (by rfl) ⟨48990, by rfl⟩ : syracuseStep 2090261 = 97981) (by norm_num)
theorem B1565977 : Blo 1391515 1565977 := bbase (se 2 (by rfl) ⟨587241, by rfl⟩ : syracuseStep 1565977 = 1174483) (by norm_num)
theorem B1566013 : Blo 1391515 1566013 := bbase (se 3 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 1566013 = 587255) (by norm_num)
theorem B5285189 : Blo 1391515 5285189 := bbase (se 4 (by rfl) ⟨495486, by rfl⟩ : syracuseStep 5285189 = 990973) (by norm_num)
theorem B3523925 : Blo 1391515 3523925 := bbase (se 12 (by rfl) ⟨1290, by rfl⟩ : syracuseStep 3523925 = 2581) (by norm_num)
theorem B7144789 : Blo 1391515 7144789 := bbase (se 12 (by rfl) ⟨2616, by rfl⟩ : syracuseStep 7144789 = 5233) (by norm_num)
theorem B1566049 : Blo 1391515 1566049 := bbase (se 2 (by rfl) ⟨587268, by rfl⟩ : syracuseStep 1566049 = 1174537) (by norm_num)
theorem B1762661 : Blo 1391515 1762661 := bbase (se 4 (by rfl) ⟨165249, by rfl⟩ : syracuseStep 1762661 = 330499) (by norm_num)
theorem B1566085 : Blo 1391515 1566085 := bbase (se 4 (by rfl) ⟨146820, by rfl⟩ : syracuseStep 1566085 = 293641) (by norm_num)
theorem B1762717 : Blo 1391515 1762717 := bbase (se 3 (by rfl) ⟨330509, by rfl⟩ : syracuseStep 1762717 = 661019) (by norm_num)
theorem B1566121 : Blo 1391515 1566121 := bbase (se 2 (by rfl) ⟨587295, by rfl⟩ : syracuseStep 1566121 = 1174591) (by norm_num)
theorem B3343805 : Blo 1391515 3343805 := bbase (se 3 (by rfl) ⟨626963, by rfl⟩ : syracuseStep 3343805 = 1253927) (by norm_num)
theorem B1566157 : Blo 1391515 1566157 := bbase (se 3 (by rfl) ⟨293654, by rfl⟩ : syracuseStep 1566157 = 587309) (by norm_num)
theorem B3966421 : Blo 1391515 3966421 := bbase (se 7 (by rfl) ⟨46481, by rfl⟩ : syracuseStep 3966421 = 92963) (by norm_num)
theorem B6694373 : Blo 1391515 6694373 := bbase (se 4 (by rfl) ⟨627597, by rfl⟩ : syracuseStep 6694373 = 1255195) (by norm_num)
theorem B1566193 : Blo 1391515 1566193 := bbase (se 2 (by rfl) ⟨587322, by rfl⟩ : syracuseStep 1566193 = 1174645) (by norm_num)
theorem B1762813 : Blo 1391515 1762813 := bbase (se 3 (by rfl) ⟨330527, by rfl⟩ : syracuseStep 1762813 = 661055) (by norm_num)
theorem B1566229 : Blo 1391515 1566229 := bbase (se 6 (by rfl) ⟨36708, by rfl⟩ : syracuseStep 1566229 = 73417) (by norm_num)
theorem B1566265 : Blo 1391515 1566265 := bbase (se 2 (by rfl) ⟨587349, by rfl⟩ : syracuseStep 1566265 = 1174699) (by norm_num)
theorem B3130973 : Blo 1391515 3130973 := bbase (se 3 (by rfl) ⟨587057, by rfl⟩ : syracuseStep 3130973 = 1174115) (by norm_num)
theorem B1566301 : Blo 1391515 1566301 := bbase (se 3 (by rfl) ⟨293681, by rfl⟩ : syracuseStep 1566301 = 587363) (by norm_num)
theorem B2229869 : Blo 1391515 2229869 := bbase (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) (by norm_num)
theorem B1672825 : Blo 1391515 1672825 := bbase (se 2 (by rfl) ⟨627309, by rfl⟩ : syracuseStep 1672825 = 1254619) (by norm_num)
theorem B1566337 : Blo 1391515 1566337 := bbase (se 2 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 1566337 = 1174753) (by norm_num)
theorem B2008733 : Blo 1391515 2008733 := bbase (se 3 (by rfl) ⟨376637, by rfl⟩ : syracuseStep 2008733 = 753275) (by norm_num)
theorem B3131045 : Blo 1391515 3131045 := bbase (se 4 (by rfl) ⟨293535, by rfl⟩ : syracuseStep 3131045 = 587071) (by norm_num)
theorem B4458149 : Blo 1391515 4458149 := bbase (se 4 (by rfl) ⟨417951, by rfl⟩ : syracuseStep 4458149 = 835903) (by norm_num)
theorem B1566373 : Blo 1391515 1566373 := bbase (se 4 (by rfl) ⟨146847, by rfl⟩ : syracuseStep 1566373 = 293695) (by norm_num)
theorem B1762985 : Blo 1391515 1762985 := bbase (se 2 (by rfl) ⟨661119, by rfl⟩ : syracuseStep 1762985 = 1322239) (by norm_num)
theorem B3524269 : Blo 1391515 3524269 := bbase (se 3 (by rfl) ⟨660800, by rfl⟩ : syracuseStep 3524269 = 1321601) (by norm_num)
theorem B7046837 : Blo 1391515 7046837 := bbase (se 5 (by rfl) ⟨330320, by rfl⟩ : syracuseStep 7046837 = 660641) (by norm_num)
theorem B1566409 : Blo 1391515 1566409 := bbase (se 2 (by rfl) ⟨587403, by rfl⟩ : syracuseStep 1566409 = 1174807) (by norm_num)
theorem B1763041 : Blo 1391515 1763041 := bbase (se 2 (by rfl) ⟨661140, by rfl⟩ : syracuseStep 1763041 = 1322281) (by norm_num)
theorem B3131117 : Blo 1391515 3131117 := bbase (se 3 (by rfl) ⟨587084, by rfl⟩ : syracuseStep 3131117 = 1174169) (by norm_num)
theorem B1566445 : Blo 1391515 1566445 := bbase (se 3 (by rfl) ⟨293708, by rfl⟩ : syracuseStep 1566445 = 587417) (by norm_num)
theorem B1566481 : Blo 1391515 1566481 := bbase (se 2 (by rfl) ⟨587430, by rfl⟩ : syracuseStep 1566481 = 1174861) (by norm_num)
theorem B2066197 : Blo 1391515 2066197 := bbase (se 6 (by rfl) ⟨48426, by rfl⟩ : syracuseStep 2066197 = 96853) (by norm_num)
theorem B3524381 : Blo 1391515 3524381 := bbase (se 3 (by rfl) ⟨660821, by rfl⟩ : syracuseStep 3524381 = 1321643) (by norm_num)
theorem B3131189 : Blo 1391515 3131189 := bbase (se 5 (by rfl) ⟨146774, by rfl⟩ : syracuseStep 3131189 = 293549) (by norm_num)
theorem B1566517 : Blo 1391515 1566517 := bbase (se 5 (by rfl) ⟨73430, by rfl⟩ : syracuseStep 1566517 = 146861) (by norm_num)
theorem B1763137 : Blo 1391515 1763137 := bbase (se 2 (by rfl) ⟨661176, by rfl⟩ : syracuseStep 1763137 = 1322353) (by norm_num)
theorem B1566553 : Blo 1391515 1566553 := bbase (se 2 (by rfl) ⟨587457, by rfl⟩ : syracuseStep 1566553 = 1174915) (by norm_num)
theorem B1632101 : Blo 1391515 1632101 := bbase (se 4 (by rfl) ⟨153009, by rfl⟩ : syracuseStep 1632101 = 306019) (by norm_num)
theorem B3131261 : Blo 1391515 3131261 := bbase (se 3 (by rfl) ⟨587111, by rfl⟩ : syracuseStep 3131261 = 1174223) (by norm_num)
theorem B1566589 : Blo 1391515 1566589 := bbase (se 3 (by rfl) ⟨293735, by rfl⟩ : syracuseStep 1566589 = 587471) (by norm_num)
theorem B1566625 : Blo 1391515 1566625 := bbase (se 2 (by rfl) ⟨587484, by rfl⟩ : syracuseStep 1566625 = 1174969) (by norm_num)
theorem B2975653 : Blo 1391515 2975653 := bbase (se 4 (by rfl) ⟨278967, by rfl⟩ : syracuseStep 2975653 = 557935) (by norm_num)
theorem B3131333 : Blo 1391515 3131333 := bbase (se 4 (by rfl) ⟨293562, by rfl⟩ : syracuseStep 3131333 = 587125) (by norm_num)
theorem B1566661 : Blo 1391515 1566661 := bbase (se 4 (by rfl) ⟨146874, by rfl⟩ : syracuseStep 1566661 = 293749) (by norm_num)
theorem B3344333 : Blo 1391515 3344333 := bbase (se 3 (by rfl) ⟨627062, by rfl⟩ : syracuseStep 3344333 = 1254125) (by norm_num)
theorem B3524573 : Blo 1391515 3524573 := bbase (se 3 (by rfl) ⟨660857, by rfl⟩ : syracuseStep 3524573 = 1321715) (by norm_num)
theorem B1566697 : Blo 1391515 1566697 := bbase (se 2 (by rfl) ⟨587511, by rfl⟩ : syracuseStep 1566697 = 1175023) (by norm_num)
theorem B1763309 : Blo 1391515 1763309 := bbase (se 3 (by rfl) ⟨330620, by rfl⟩ : syracuseStep 1763309 = 661241) (by norm_num)
theorem B5720053 : Blo 1391515 5720053 := bbase (se 5 (by rfl) ⟨268127, by rfl⟩ : syracuseStep 5720053 = 536255) (by norm_num)
theorem B1673209 : Blo 1391515 1673209 := bbase (se 2 (by rfl) ⟨627453, by rfl⟩ : syracuseStep 1673209 = 1254907) (by norm_num)
theorem B3131405 : Blo 1391515 3131405 := bbase (se 3 (by rfl) ⟨587138, by rfl⟩ : syracuseStep 3131405 = 1174277) (by norm_num)
theorem B1566733 : Blo 1391515 1566733 := bbase (se 3 (by rfl) ⟨293762, by rfl⟩ : syracuseStep 1566733 = 587525) (by norm_num)
theorem B2975773 : Blo 1391515 2975773 := bbase (se 3 (by rfl) ⟨557957, by rfl⟩ : syracuseStep 2975773 = 1115915) (by norm_num)
theorem B1763365 : Blo 1391515 1763365 := bbase (se 4 (by rfl) ⟨165315, by rfl⟩ : syracuseStep 1763365 = 330631) (by norm_num)
theorem B1566769 : Blo 1391515 1566769 := bbase (se 2 (by rfl) ⟨587538, by rfl⟩ : syracuseStep 1566769 = 1175077) (by norm_num)
theorem B2230325 : Blo 1391515 2230325 := bbase (se 5 (by rfl) ⟨104546, by rfl⟩ : syracuseStep 2230325 = 209093) (by norm_num)
theorem B3131477 : Blo 1391515 3131477 := bbase (se 8 (by rfl) ⟨18348, by rfl⟩ : syracuseStep 3131477 = 36697) (by norm_num)
theorem B1566805 : Blo 1391515 1566805 := bbase (se 8 (by rfl) ⟨9180, by rfl⟩ : syracuseStep 1566805 = 18361) (by norm_num)
theorem B1566841 : Blo 1391515 1566841 := bbase (se 2 (by rfl) ⟨587565, by rfl⟩ : syracuseStep 1566841 = 1175131) (by norm_num)
theorem B1763461 : Blo 1391515 1763461 := bbase (se 4 (by rfl) ⟨165324, by rfl⟩ : syracuseStep 1763461 = 330649) (by norm_num)
theorem B3131549 : Blo 1391515 3131549 := bbase (se 3 (by rfl) ⟨587165, by rfl⟩ : syracuseStep 3131549 = 1174331) (by norm_num)
theorem B1566877 : Blo 1391515 1566877 := bbase (se 3 (by rfl) ⟨293789, by rfl⟩ : syracuseStep 1566877 = 587579) (by norm_num)
theorem B3344573 : Blo 1391515 3344573 := bbase (se 3 (by rfl) ⟨627107, by rfl⟩ : syracuseStep 3344573 = 1254215) (by norm_num)
theorem B1566913 : Blo 1391515 1566913 := bbase (se 2 (by rfl) ⟨587592, by rfl⟩ : syracuseStep 1566913 = 1175185) (by norm_num)
theorem B3131621 : Blo 1391515 3131621 := bbase (se 4 (by rfl) ⟨293589, by rfl⟩ : syracuseStep 3131621 = 587179) (by norm_num)
theorem B1566949 : Blo 1391515 1566949 := bbase (se 4 (by rfl) ⟨146901, by rfl⟩ : syracuseStep 1566949 = 293803) (by norm_num)
theorem B4237541 : Blo 1391515 4237541 := bbase (se 4 (by rfl) ⟨397269, by rfl⟩ : syracuseStep 4237541 = 794539) (by norm_num)
theorem B1566985 : Blo 1391515 1566985 := bbase (se 2 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 1566985 = 1175239) (by norm_num)
theorem B2976029 : Blo 1391515 2976029 := bbase (se 3 (by rfl) ⟨558005, by rfl⟩ : syracuseStep 2976029 = 1116011) (by norm_num)
theorem B2509093 : Blo 1391515 2509093 := bbase (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) (by norm_num)
theorem B3131693 : Blo 1391515 3131693 := bbase (se 3 (by rfl) ⟨587192, by rfl⟩ : syracuseStep 3131693 = 1174385) (by norm_num)
theorem B1567021 : Blo 1391515 1567021 := bbase (se 3 (by rfl) ⟨293816, by rfl⟩ : syracuseStep 1567021 = 587633) (by norm_num)
theorem B1763633 : Blo 1391515 1763633 := bbase (se 2 (by rfl) ⟨661362, by rfl⟩ : syracuseStep 1763633 = 1322725) (by norm_num)
theorem B3524917 : Blo 1391515 3524917 := bbase (se 5 (by rfl) ⟨165230, by rfl⟩ : syracuseStep 3524917 = 330461) (by norm_num)
theorem B1567057 : Blo 1391515 1567057 := bbase (se 2 (by rfl) ⟨587646, by rfl⟩ : syracuseStep 1567057 = 1175293) (by norm_num)
theorem B3131765 : Blo 1391515 3131765 := bbase (se 5 (by rfl) ⟨146801, by rfl⟩ : syracuseStep 3131765 = 293603) (by norm_num)
theorem B1567093 : Blo 1391515 1567093 := bbase (se 5 (by rfl) ⟨73457, by rfl⟩ : syracuseStep 1567093 = 146915) (by norm_num)
theorem B1567129 : Blo 1391515 1567129 := bbase (se 2 (by rfl) ⟨587673, by rfl⟩ : syracuseStep 1567129 = 1175347) (by norm_num)
theorem B3525029 : Blo 1391515 3525029 := bbase (se 4 (by rfl) ⟨330471, by rfl⟩ : syracuseStep 3525029 = 660943) (by norm_num)
theorem B3131837 : Blo 1391515 3131837 := bbase (se 3 (by rfl) ⟨587219, by rfl⟩ : syracuseStep 3131837 = 1174439) (by norm_num)
theorem B1567165 : Blo 1391515 1567165 := bbase (se 3 (by rfl) ⟨293843, by rfl⟩ : syracuseStep 1567165 = 587687) (by norm_num)
theorem B1567201 : Blo 1391515 1567201 := bbase (se 2 (by rfl) ⟨587700, by rfl⟩ : syracuseStep 1567201 = 1175401) (by norm_num)
theorem B3131909 : Blo 1391515 3131909 := bbase (se 4 (by rfl) ⟨293616, by rfl⟩ : syracuseStep 3131909 = 587233) (by norm_num)
theorem B3574277 : Blo 1391515 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B1567237 : Blo 1391515 1567237 := bbase (se 4 (by rfl) ⟨146928, by rfl⟩ : syracuseStep 1567237 = 293857) (by norm_num)
theorem B1411625 : Blo 1391515 1411625 := bbase (se 2 (by rfl) ⟨529359, by rfl⟩ : syracuseStep 1411625 = 1058719) (by norm_num)
theorem B1567273 : Blo 1391515 1567273 := bbase (se 2 (by rfl) ⟨587727, by rfl⟩ : syracuseStep 1567273 = 1175455) (by norm_num)
theorem B3131981 : Blo 1391515 3131981 := bbase (se 3 (by rfl) ⟨587246, by rfl⟩ : syracuseStep 3131981 = 1174493) (by norm_num)
theorem B1567309 : Blo 1391515 1567309 := bbase (se 3 (by rfl) ⟨293870, by rfl⟩ : syracuseStep 1567309 = 587741) (by norm_num)
theorem B1411673 : Blo 1391515 1411673 := bbase (se 2 (by rfl) ⟨529377, by rfl⟩ : syracuseStep 1411673 = 1058755) (by norm_num)
theorem B3525221 : Blo 1391515 3525221 := bbase (se 4 (by rfl) ⟨330489, by rfl⟩ : syracuseStep 3525221 = 660979) (by norm_num)
theorem B1567345 : Blo 1391515 1567345 := bbase (se 2 (by rfl) ⟨587754, by rfl⟩ : syracuseStep 1567345 = 1175509) (by norm_num)
theorem B3132053 : Blo 1391515 3132053 := bbase (se 6 (by rfl) ⟨73407, by rfl⟩ : syracuseStep 3132053 = 146815) (by norm_num)
theorem B1567381 : Blo 1391515 1567381 := bbase (se 6 (by rfl) ⟨36735, by rfl⟩ : syracuseStep 1567381 = 73471) (by norm_num)
theorem B4696757 : Blo 1391515 4696757 := bbase (se 5 (by rfl) ⟨220160, by rfl⟩ : syracuseStep 4696757 = 440321) (by norm_num)
theorem B1567417 : Blo 1391515 1567417 := bbase (se 2 (by rfl) ⟨587781, by rfl⟩ : syracuseStep 1567417 = 1175563) (by norm_num)
theorem B3132125 : Blo 1391515 3132125 := bbase (se 3 (by rfl) ⟨587273, by rfl⟩ : syracuseStep 3132125 = 1174547) (by norm_num)
theorem B1567453 : Blo 1391515 1567453 := bbase (se 3 (by rfl) ⟨293897, by rfl⟩ : syracuseStep 1567453 = 587795) (by norm_num)
theorem B1567489 : Blo 1391515 1567489 := bbase (se 2 (by rfl) ⟨587808, by rfl⟩ : syracuseStep 1567489 = 1175617) (by norm_num)
theorem B3132197 : Blo 1391515 3132197 := bbase (se 4 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 3132197 = 587287) (by norm_num)
theorem B1567525 : Blo 1391515 1567525 := bbase (se 4 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 1567525 = 293911) (by norm_num)
theorem B2009933 : Blo 1391515 2009933 := bbase (se 3 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 2009933 = 753725) (by norm_num)
theorem B1567561 : Blo 1391515 1567561 := bbase (se 2 (by rfl) ⟨587835, by rfl⟩ : syracuseStep 1567561 = 1175671) (by norm_num)
theorem B1674065 : Blo 1391515 1674065 := bbase (se 2 (by rfl) ⟨627774, by rfl⟩ : syracuseStep 1674065 = 1255549) (by norm_num)
theorem B3132269 : Blo 1391515 3132269 := bbase (se 3 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 3132269 = 1174601) (by norm_num)
theorem B1567597 : Blo 1391515 1567597 := bbase (se 3 (by rfl) ⟨293924, by rfl⟩ : syracuseStep 1567597 = 587849) (by norm_num)
theorem B6695797 : Blo 1391515 6695797 := bbase (se 5 (by rfl) ⟨313865, by rfl⟩ : syracuseStep 6695797 = 627731) (by norm_num)
theorem B1567633 : Blo 1391515 1567633 := bbase (se 2 (by rfl) ⟨587862, by rfl⟩ : syracuseStep 1567633 = 1175725) (by norm_num)
theorem B1608617 : Blo 1391515 1608617 := bbase (se 2 (by rfl) ⟨603231, by rfl⟩ : syracuseStep 1608617 = 1206463) (by norm_num)
theorem B3132341 : Blo 1391515 3132341 := bbase (se 5 (by rfl) ⟨146828, by rfl⟩ : syracuseStep 3132341 = 293657) (by norm_num)
theorem B1567669 : Blo 1391515 1567669 := bbase (se 5 (by rfl) ⟨73484, by rfl⟩ : syracuseStep 1567669 = 146969) (by norm_num)
theorem B3525565 : Blo 1391515 3525565 := bbase (se 3 (by rfl) ⟨661043, by rfl⟩ : syracuseStep 3525565 = 1322087) (by norm_num)
theorem B7048133 : Blo 1391515 7048133 := bbase (se 4 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 7048133 = 1321525) (by norm_num)
theorem B1567705 : Blo 1391515 1567705 := bbase (se 2 (by rfl) ⟨587889, by rfl⟩ : syracuseStep 1567705 = 1175779) (by norm_num)
theorem B3132413 : Blo 1391515 3132413 := bbase (se 3 (by rfl) ⟨587327, by rfl⟩ : syracuseStep 3132413 = 1174655) (by norm_num)
theorem B8915989 : Blo 1391515 8915989 := bbase (se 6 (by rfl) ⟨208968, by rfl⟩ : syracuseStep 8915989 = 417937) (by norm_num)
theorem B2231317 : Blo 1391515 2231317 := bbase (se 6 (by rfl) ⟨52296, by rfl⟩ : syracuseStep 2231317 = 104593) (by norm_num)
theorem B3525677 : Blo 1391515 3525677 := bbase (se 3 (by rfl) ⟨661064, by rfl⟩ : syracuseStep 3525677 = 1322129) (by norm_num)
theorem B5016629 : Blo 1391515 5016629 := bbase (se 5 (by rfl) ⟨235154, by rfl⟩ : syracuseStep 5016629 = 470309) (by norm_num)
theorem B3132485 : Blo 1391515 3132485 := bbase (se 4 (by rfl) ⟨293670, by rfl⟩ : syracuseStep 3132485 = 587341) (by norm_num)
theorem B4697189 : Blo 1391515 4697189 := bbase (se 4 (by rfl) ⟨440361, by rfl⟩ : syracuseStep 4697189 = 880723) (by norm_num)
theorem B3132557 : Blo 1391515 3132557 := bbase (se 3 (by rfl) ⟨587354, by rfl⟩ : syracuseStep 3132557 = 1174709) (by norm_num)
theorem B1485973 : Blo 1391515 1485973 := bbase (se 6 (by rfl) ⟨34827, by rfl⟩ : syracuseStep 1485973 = 69655) (by norm_num)
theorem B5016773 : Blo 1391515 5016773 := bbase (se 4 (by rfl) ⟨470322, by rfl⟩ : syracuseStep 5016773 = 940645) (by norm_num)
theorem B3132629 : Blo 1391515 3132629 := bbase (se 7 (by rfl) ⟨36710, by rfl⟩ : syracuseStep 3132629 = 73421) (by norm_num)
theorem B3525869 : Blo 1391515 3525869 := bbase (se 3 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 3525869 = 1322201) (by norm_num)
theorem B3132701 : Blo 1391515 3132701 := bbase (se 3 (by rfl) ⟨587381, by rfl⟩ : syracuseStep 3132701 = 1174763) (by norm_num)
theorem B3132773 : Blo 1391515 3132773 := bbase (se 4 (by rfl) ⟨293697, by rfl⟩ : syracuseStep 3132773 = 587395) (by norm_num)
theorem B5287301 : Blo 1391515 5287301 := bbase (se 4 (by rfl) ⟨495684, by rfl⟩ : syracuseStep 5287301 = 991369) (by norm_num)
theorem B7925141 : Blo 1391515 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B3132845 : Blo 1391515 3132845 := bbase (se 3 (by rfl) ⟨587408, by rfl⟩ : syracuseStep 3132845 = 1174817) (by norm_num)
theorem B1486289 : Blo 1391515 1486289 := bbase (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) (by norm_num)
theorem B1609205 : Blo 1391515 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B3132917 : Blo 1391515 3132917 := bbase (se 5 (by rfl) ⟨146855, by rfl⟩ : syracuseStep 3132917 = 293711) (by norm_num)
theorem B2510333 : Blo 1391515 2510333 := bbase (se 3 (by rfl) ⟨470687, by rfl⟩ : syracuseStep 2510333 = 941375) (by norm_num)
theorem B4697621 : Blo 1391515 4697621 := bbase (se 6 (by rfl) ⟨110100, by rfl⟩ : syracuseStep 4697621 = 220201) (by norm_num)
theorem B3132989 : Blo 1391515 3132989 := bbase (se 3 (by rfl) ⟨587435, by rfl⟩ : syracuseStep 3132989 = 1174871) (by norm_num)
theorem B3526213 : Blo 1391515 3526213 := bbase (se 4 (by rfl) ⟨330582, by rfl⟩ : syracuseStep 3526213 = 661165) (by norm_num)
theorem B3133061 : Blo 1391515 3133061 := bbase (se 4 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 3133061 = 587449) (by norm_num)
theorem B2231965 : Blo 1391515 2231965 := bbase (se 3 (by rfl) ⟨418493, by rfl⟩ : syracuseStep 2231965 = 836987) (by norm_num)
theorem B5287589 : Blo 1391515 5287589 := bbase (se 4 (by rfl) ⟨495711, by rfl⟩ : syracuseStep 5287589 = 991423) (by norm_num)
theorem B3526325 : Blo 1391515 3526325 := bbase (se 5 (by rfl) ⟨165296, by rfl⟩ : syracuseStep 3526325 = 330593) (by norm_num)
theorem B3133133 : Blo 1391515 3133133 := bbase (se 3 (by rfl) ⟨587462, by rfl⟩ : syracuseStep 3133133 = 1174925) (by norm_num)
theorem B7147237 : Blo 1391515 7147237 := bbase (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) (by norm_num)
theorem B7147253 : Blo 1391515 7147253 := bbase (se 5 (by rfl) ⟨335027, by rfl⟩ : syracuseStep 7147253 = 670055) (by norm_num)
theorem B3133205 : Blo 1391515 3133205 := bbase (se 6 (by rfl) ⟨73434, by rfl⟩ : syracuseStep 3133205 = 146869) (by norm_num)
theorem B10579733 : Blo 1391515 10579733 := bbase (se 6 (by rfl) ⟨247962, by rfl⟩ : syracuseStep 10579733 = 495925) (by norm_num)
theorem B4460341 : Blo 1391515 4460341 := bbase (se 5 (by rfl) ⟨209078, by rfl⟩ : syracuseStep 4460341 = 418157) (by norm_num)
theorem B3133277 : Blo 1391515 3133277 := bbase (se 3 (by rfl) ⟨587489, by rfl⟩ : syracuseStep 3133277 = 1174979) (by norm_num)
theorem B3346285 : Blo 1391515 3346285 := bbase (se 3 (by rfl) ⟨627428, by rfl⟩ : syracuseStep 3346285 = 1254857) (by norm_num)
theorem B3526517 : Blo 1391515 3526517 := bbase (se 5 (by rfl) ⟨165305, by rfl⟩ : syracuseStep 3526517 = 330611) (by norm_num)
theorem B2641805 : Blo 1391515 2641805 := bbase (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) (by norm_num)
theorem B1486733 : Blo 1391515 1486733 := bbase (se 3 (by rfl) ⟨278762, by rfl⟩ : syracuseStep 1486733 = 557525) (by norm_num)
theorem B3133349 : Blo 1391515 3133349 := bbase (se 4 (by rfl) ⟨293751, by rfl⟩ : syracuseStep 3133349 = 587503) (by norm_num)
theorem B6352805 : Blo 1391515 6352805 := bbase (se 4 (by rfl) ⟨595575, by rfl⟩ : syracuseStep 6352805 = 1191151) (by norm_num)
theorem B4698053 : Blo 1391515 4698053 := bbase (se 4 (by rfl) ⟨440442, by rfl⟩ : syracuseStep 4698053 = 880885) (by norm_num)
theorem B1486793 : Blo 1391515 1486793 := bbase (se 2 (by rfl) ⟨557547, by rfl⟩ : syracuseStep 1486793 = 1115095) (by norm_num)
theorem B3133421 : Blo 1391515 3133421 := bbase (se 3 (by rfl) ⟨587516, by rfl⟩ : syracuseStep 3133421 = 1175033) (by norm_num)
theorem B3133493 : Blo 1391515 3133493 := bbase (se 5 (by rfl) ⟨146882, by rfl⟩ : syracuseStep 3133493 = 293765) (by norm_num)
theorem B1486921 : Blo 1391515 1486921 := bbase (se 2 (by rfl) ⟨557595, by rfl⟩ : syracuseStep 1486921 = 1115191) (by norm_num)
theorem B2117717 : Blo 1391515 2117717 := bbase (se 8 (by rfl) ⟨12408, by rfl⟩ : syracuseStep 2117717 = 24817) (by norm_num)
theorem B3133565 : Blo 1391515 3133565 := bbase (se 3 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 3133565 = 1175087) (by norm_num)
theorem B10571957 : Blo 1391515 10571957 := bbase (se 5 (by rfl) ⟨495560, by rfl⟩ : syracuseStep 10571957 = 991121) (by norm_num)
theorem B3133637 : Blo 1391515 3133637 := bbase (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) (by norm_num)
theorem B3526861 : Blo 1391515 3526861 := bbase (se 3 (by rfl) ⟨661286, by rfl⟩ : syracuseStep 3526861 = 1322573) (by norm_num)
theorem B7049429 : Blo 1391515 7049429 := bbase (se 7 (by rfl) ⟨82610, by rfl⟩ : syracuseStep 7049429 = 165221) (by norm_num)
theorem B5951717 : Blo 1391515 5951717 := bbase (se 4 (by rfl) ⟨557973, by rfl⟩ : syracuseStep 5951717 = 1115947) (by norm_num)
theorem B3133709 : Blo 1391515 3133709 := bbase (se 3 (by rfl) ⟨587570, by rfl⟩ : syracuseStep 3133709 = 1175141) (by norm_num)
theorem B1610041 : Blo 1391515 1610041 := bbase (se 2 (by rfl) ⟨603765, by rfl⟩ : syracuseStep 1610041 = 1207531) (by norm_num)
theorem B3526973 : Blo 1391515 3526973 := bbase (se 3 (by rfl) ⟨661307, by rfl⟩ : syracuseStep 3526973 = 1322615) (by norm_num)
theorem B3764549 : Blo 1391515 3764549 := bbase (se 4 (by rfl) ⟨352926, by rfl⟩ : syracuseStep 3764549 = 705853) (by norm_num)
theorem B3133781 : Blo 1391515 3133781 := bbase (se 10 (by rfl) ⟨4590, by rfl⟩ : syracuseStep 3133781 = 9181) (by norm_num)
theorem B4698485 : Blo 1391515 4698485 := bbase (se 5 (by rfl) ⟨220241, by rfl⟩ : syracuseStep 4698485 = 440483) (by norm_num)
theorem B3174805 : Blo 1391515 3174805 := bbase (se 6 (by rfl) ⟨74409, by rfl⟩ : syracuseStep 3174805 = 148819) (by norm_num)
theorem B3133853 : Blo 1391515 3133853 := bbase (se 3 (by rfl) ⟨587597, by rfl⟩ : syracuseStep 3133853 = 1175195) (by norm_num)
theorem B3133925 : Blo 1391515 3133925 := bbase (se 4 (by rfl) ⟨293805, by rfl⟩ : syracuseStep 3133925 = 587611) (by norm_num)
theorem B3527165 : Blo 1391515 3527165 := bbase (se 3 (by rfl) ⟨661343, by rfl⟩ : syracuseStep 3527165 = 1322687) (by norm_num)
theorem B4018693 : Blo 1391515 4018693 := bbase (se 4 (by rfl) ⟨376752, by rfl⟩ : syracuseStep 4018693 = 753505) (by norm_num)
theorem B1487365 : Blo 1391515 1487365 := bbase (se 4 (by rfl) ⟨139440, by rfl⟩ : syracuseStep 1487365 = 278881) (by norm_num)
theorem B3437093 : Blo 1391515 3437093 := bbase (se 4 (by rfl) ⟨322227, by rfl⟩ : syracuseStep 3437093 = 644455) (by norm_num)
theorem B3133997 : Blo 1391515 3133997 := bbase (se 3 (by rfl) ⟨587624, by rfl⟩ : syracuseStep 3133997 = 1175249) (by norm_num)
theorem B10031701 : Blo 1391515 10031701 := bbase (se 8 (by rfl) ⟨58779, by rfl⟩ : syracuseStep 10031701 = 117559) (by norm_num)
theorem B2413165 : Blo 1391515 2413165 := bbase (se 3 (by rfl) ⟨452468, by rfl⟩ : syracuseStep 2413165 = 904937) (by norm_num)
theorem B4461173 : Blo 1391515 4461173 := bbase (se 5 (by rfl) ⟨209117, by rfl⟩ : syracuseStep 4461173 = 418235) (by norm_num)
theorem B3134069 : Blo 1391515 3134069 := bbase (se 5 (by rfl) ⟨146909, by rfl⟩ : syracuseStep 3134069 = 293819) (by norm_num)
theorem B2642557 : Blo 1391515 2642557 := bbase (se 3 (by rfl) ⟨495479, by rfl⟩ : syracuseStep 2642557 = 990959) (by norm_num)
theorem B1487485 : Blo 1391515 1487485 := bbase (se 3 (by rfl) ⟨278903, by rfl⟩ : syracuseStep 1487485 = 557807) (by norm_num)
theorem B3134141 : Blo 1391515 3134141 := bbase (se 3 (by rfl) ⟨587651, by rfl⟩ : syracuseStep 3134141 = 1175303) (by norm_num)
theorem B3764981 : Blo 1391515 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B3134213 : Blo 1391515 3134213 := bbase (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) (by norm_num)
theorem B2642701 : Blo 1391515 2642701 := bbase (se 3 (by rfl) ⟨495506, by rfl⟩ : syracuseStep 2642701 = 991013) (by norm_num)
theorem B4698917 : Blo 1391515 4698917 := bbase (se 4 (by rfl) ⟨440523, by rfl⟩ : syracuseStep 4698917 = 881047) (by norm_num)
theorem B1528633 : Blo 1391515 1528633 := bbase (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) (by norm_num)
theorem B5288773 : Blo 1391515 5288773 := bbase (se 4 (by rfl) ⟨495822, by rfl⟩ : syracuseStep 5288773 = 991645) (by norm_num)
theorem B3134285 : Blo 1391515 3134285 := bbase (se 3 (by rfl) ⟨587678, by rfl⟩ : syracuseStep 3134285 = 1175357) (by norm_num)
theorem B8926037 : Blo 1391515 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B1487737 : Blo 1391515 1487737 := bbase (se 2 (by rfl) ⟨557901, by rfl⟩ : syracuseStep 1487737 = 1115803) (by norm_num)
theorem B1487741 : Blo 1391515 1487741 := bbase (se 3 (by rfl) ⟨278951, by rfl⟩ : syracuseStep 1487741 = 557903) (by norm_num)
theorem B3134357 : Blo 1391515 3134357 := bbase (se 6 (by rfl) ⟨73461, by rfl⟩ : syracuseStep 3134357 = 146923) (by norm_num)
theorem B2642861 : Blo 1391515 2642861 := bbase (se 3 (by rfl) ⟨495536, by rfl⟩ : syracuseStep 2642861 = 991073) (by norm_num)
theorem B11006933 : Blo 1391515 11006933 := bbase (se 7 (by rfl) ⟨128987, by rfl⟩ : syracuseStep 11006933 = 257975) (by norm_num)
theorem B3134429 : Blo 1391515 3134429 := bbase (se 3 (by rfl) ⟨587705, by rfl⟩ : syracuseStep 3134429 = 1175411) (by norm_num)
theorem B4584421 : Blo 1391515 4584421 := bbase (se 4 (by rfl) ⟨429789, by rfl⟩ : syracuseStep 4584421 = 859579) (by norm_num)
theorem B2118629 : Blo 1391515 2118629 := bbase (se 4 (by rfl) ⟨198621, by rfl⟩ : syracuseStep 2118629 = 397243) (by norm_num)
theorem B3134501 : Blo 1391515 3134501 := bbase (se 4 (by rfl) ⟨293859, by rfl⟩ : syracuseStep 3134501 = 587719) (by norm_num)
theorem B7935029 : Blo 1391515 7935029 := bbase (se 5 (by rfl) ⟨371954, by rfl⟩ : syracuseStep 7935029 = 743909) (by norm_num)
theorem B1881149 : Blo 1391515 1881149 := bbase (se 3 (by rfl) ⟨352715, by rfl⟩ : syracuseStep 1881149 = 705431) (by norm_num)
theorem B2643005 : Blo 1391515 2643005 := bbase (se 3 (by rfl) ⟨495563, by rfl⟩ : syracuseStep 2643005 = 991127) (by norm_num)
theorem B3134573 : Blo 1391515 3134573 := bbase (se 3 (by rfl) ⟨587732, by rfl⟩ : syracuseStep 3134573 = 1175465) (by norm_num)
theorem B5289077 : Blo 1391515 5289077 := bbase (se 5 (by rfl) ⟨247925, by rfl⟩ : syracuseStep 5289077 = 495851) (by norm_num)
theorem B3134645 : Blo 1391515 3134645 := bbase (se 5 (by rfl) ⟨146936, by rfl⟩ : syracuseStep 3134645 = 293873) (by norm_num)
theorem B2348237 : Blo 1391515 2348237 := bbase (se 3 (by rfl) ⟨440294, by rfl⟩ : syracuseStep 2348237 = 880589) (by norm_num)
theorem B4699349 : Blo 1391515 4699349 := bbase (se 7 (by rfl) ⟨55070, by rfl⟩ : syracuseStep 4699349 = 110141) (by norm_num)
theorem B4019429 : Blo 1391515 4019429 := bbase (se 4 (by rfl) ⟨376821, by rfl⟩ : syracuseStep 4019429 = 753643) (by norm_num)
theorem B3134717 : Blo 1391515 3134717 := bbase (se 3 (by rfl) ⟨587759, by rfl⟩ : syracuseStep 3134717 = 1175519) (by norm_num)
theorem B3347725 : Blo 1391515 3347725 := bbase (se 3 (by rfl) ⟨627698, by rfl⟩ : syracuseStep 3347725 = 1255397) (by norm_num)
theorem B13047061 : Blo 1391515 13047061 := bbase (se 6 (by rfl) ⟨305790, by rfl⟩ : syracuseStep 13047061 = 611581) (by norm_num)
theorem B2823493 : Blo 1391515 2823493 := bbase (se 4 (by rfl) ⟨264702, by rfl⟩ : syracuseStep 2823493 = 529405) (by norm_num)
theorem B3134789 : Blo 1391515 3134789 := bbase (se 4 (by rfl) ⟨293886, by rfl⟩ : syracuseStep 3134789 = 587773) (by norm_num)
theorem B2348365 : Blo 1391515 2348365 := bbase (se 3 (by rfl) ⟨440318, by rfl⟩ : syracuseStep 2348365 = 880637) (by norm_num)
theorem B5944661 : Blo 1391515 5944661 := bbase (se 13 (by rfl) ⟨1088, by rfl⟩ : syracuseStep 5944661 = 2177) (by norm_num)
theorem B2643293 : Blo 1391515 2643293 := bbase (se 3 (by rfl) ⟨495617, by rfl⟩ : syracuseStep 2643293 = 991235) (by norm_num)
theorem B3134861 : Blo 1391515 3134861 := bbase (se 3 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 3134861 = 1175573) (by norm_num)
theorem B2348453 : Blo 1391515 2348453 := bbase (se 4 (by rfl) ⟨220167, by rfl⟩ : syracuseStep 2348453 = 440335) (by norm_num)
theorem B3134933 : Blo 1391515 3134933 := bbase (se 7 (by rfl) ⟨36737, by rfl⟩ : syracuseStep 3134933 = 73475) (by norm_num)
theorem B3175901 : Blo 1391515 3175901 := bbase (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) (by norm_num)
theorem B7050725 : Blo 1391515 7050725 := bbase (se 4 (by rfl) ⟨661005, by rfl⟩ : syracuseStep 7050725 = 1322011) (by norm_num)
theorem B2643445 : Blo 1391515 2643445 := bbase (se 5 (by rfl) ⟨123911, by rfl⟩ : syracuseStep 2643445 = 247823) (by norm_num)
theorem B3135005 : Blo 1391515 3135005 := bbase (se 3 (by rfl) ⟨587813, by rfl⟩ : syracuseStep 3135005 = 1175627) (by norm_num)
theorem B2348581 : Blo 1391515 2348581 := bbase (se 4 (by rfl) ⟨220179, by rfl⟩ : syracuseStep 2348581 = 440359) (by norm_num)
theorem B3135077 : Blo 1391515 3135077 := bbase (se 4 (by rfl) ⟨293913, by rfl⟩ : syracuseStep 3135077 = 587827) (by norm_num)
theorem B2348669 : Blo 1391515 2348669 := bbase (se 3 (by rfl) ⟨440375, by rfl⟩ : syracuseStep 2348669 = 880751) (by norm_num)
theorem B2545277 : Blo 1391515 2545277 := bbase (se 3 (by rfl) ⟨477239, by rfl⟩ : syracuseStep 2545277 = 954479) (by norm_num)
theorem B4699781 : Blo 1391515 4699781 := bbase (se 4 (by rfl) ⟨440604, by rfl⟩ : syracuseStep 4699781 = 881209) (by norm_num)
theorem B4019861 : Blo 1391515 4019861 := bbase (se 6 (by rfl) ⟨94215, by rfl⟩ : syracuseStep 4019861 = 188431) (by norm_num)
theorem B3135149 : Blo 1391515 3135149 := bbase (se 3 (by rfl) ⟨587840, by rfl⟩ : syracuseStep 3135149 = 1175681) (by norm_num)
theorem B1586893 : Blo 1391515 1586893 := bbase (se 3 (by rfl) ⟨297542, by rfl⟩ : syracuseStep 1586893 = 595085) (by norm_num)
theorem B3135221 : Blo 1391515 3135221 := bbase (se 5 (by rfl) ⟨146963, by rfl⟩ : syracuseStep 3135221 = 293927) (by norm_num)
theorem B2348797 : Blo 1391515 2348797 := bbase (se 3 (by rfl) ⟨440399, by rfl⟩ : syracuseStep 2348797 = 880799) (by norm_num)
theorem B2643749 : Blo 1391515 2643749 := bbase (se 4 (by rfl) ⟨247851, by rfl⟩ : syracuseStep 2643749 = 495703) (by norm_num)
theorem B13391669 : Blo 1391515 13391669 := bbase (se 5 (by rfl) ⟨627734, by rfl⟩ : syracuseStep 13391669 = 1255469) (by norm_num)
theorem B3135293 : Blo 1391515 3135293 := bbase (se 3 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 3135293 = 1175735) (by norm_num)
theorem B2348885 : Blo 1391515 2348885 := bbase (se 9 (by rfl) ⟨6881, by rfl⟩ : syracuseStep 2348885 = 13763) (by norm_num)
theorem B3135365 : Blo 1391515 3135365 := bbase (se 4 (by rfl) ⟨293940, by rfl⟩ : syracuseStep 3135365 = 587881) (by norm_num)
theorem B3766181 : Blo 1391515 3766181 := bbase (se 4 (by rfl) ⟨353079, by rfl⟩ : syracuseStep 3766181 = 706159) (by norm_num)
theorem B2349013 : Blo 1391515 2349013 := bbase (se 7 (by rfl) ⟨27527, by rfl⟩ : syracuseStep 2349013 = 55055) (by norm_num)
theorem B1587217 : Blo 1391515 1587217 := bbase (se 2 (by rfl) ⟨595206, by rfl⟩ : syracuseStep 1587217 = 1190413) (by norm_num)
theorem B2349101 : Blo 1391515 2349101 := bbase (se 3 (by rfl) ⟨440456, by rfl⟩ : syracuseStep 2349101 = 880913) (by norm_num)
theorem B4700213 : Blo 1391515 4700213 := bbase (se 5 (by rfl) ⟨220322, by rfl⟩ : syracuseStep 4700213 = 440645) (by norm_num)
theorem B3962981 : Blo 1391515 3962981 := bbase (se 4 (by rfl) ⟨371529, by rfl⟩ : syracuseStep 3962981 = 743059) (by norm_num)
theorem B2349229 : Blo 1391515 2349229 := bbase (se 3 (by rfl) ⟨440480, by rfl⟩ : syracuseStep 2349229 = 880961) (by norm_num)
theorem B2349317 : Blo 1391515 2349317 := bbase (se 4 (by rfl) ⟨220248, by rfl⟩ : syracuseStep 2349317 = 440497) (by norm_num)
theorem B5945669 : Blo 1391515 5945669 := bbase (se 4 (by rfl) ⟨557406, by rfl⟩ : syracuseStep 5945669 = 1114813) (by norm_num)
theorem B13375829 : Blo 1391515 13375829 := bbase (se 10 (by rfl) ⟨19593, by rfl⟩ : syracuseStep 13375829 = 39187) (by norm_num)
theorem B2087285 : Blo 1391515 2087285 := bbase (se 5 (by rfl) ⟨97841, by rfl⟩ : syracuseStep 2087285 = 195683) (by norm_num)
theorem B2349445 : Blo 1391515 2349445 := bbase (se 4 (by rfl) ⟨220260, by rfl⟩ : syracuseStep 2349445 = 440521) (by norm_num)
theorem B2087309 : Blo 1391515 2087309 := bbase (se 3 (by rfl) ⟨391370, by rfl⟩ : syracuseStep 2087309 = 782741) (by norm_num)
theorem B2087333 : Blo 1391515 2087333 := bbase (se 4 (by rfl) ⟨195687, by rfl⟩ : syracuseStep 2087333 = 391375) (by norm_num)
theorem B2087357 : Blo 1391515 2087357 := bbase (se 3 (by rfl) ⟨391379, by rfl⟩ : syracuseStep 2087357 = 782759) (by norm_num)
theorem B4463045 : Blo 1391515 4463045 := bbase (se 4 (by rfl) ⟨418410, by rfl⟩ : syracuseStep 4463045 = 836821) (by norm_num)
theorem B2087381 : Blo 1391515 2087381 := bbase (se 7 (by rfl) ⟨24461, by rfl⟩ : syracuseStep 2087381 = 48923) (by norm_num)
theorem B2349533 : Blo 1391515 2349533 := bbase (se 3 (by rfl) ⟨440537, by rfl⟩ : syracuseStep 2349533 = 881075) (by norm_num)
theorem B4700645 : Blo 1391515 4700645 := bbase (se 4 (by rfl) ⟨440685, by rfl⟩ : syracuseStep 4700645 = 881371) (by norm_num)
theorem B2087405 : Blo 1391515 2087405 := bbase (se 3 (by rfl) ⟨391388, by rfl⟩ : syracuseStep 2087405 = 782777) (by norm_num)
theorem B2087429 : Blo 1391515 2087429 := bbase (se 4 (by rfl) ⟨195696, by rfl⟩ : syracuseStep 2087429 = 391393) (by norm_num)
theorem B2644501 : Blo 1391515 2644501 := bbase (se 6 (by rfl) ⟨61980, by rfl⟩ : syracuseStep 2644501 = 123961) (by norm_num)
theorem B2087453 : Blo 1391515 2087453 := bbase (se 3 (by rfl) ⟨391397, by rfl⟩ : syracuseStep 2087453 = 782795) (by norm_num)
theorem B2087477 : Blo 1391515 2087477 := bbase (se 5 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 2087477 = 195701) (by norm_num)
theorem B2087501 : Blo 1391515 2087501 := bbase (se 3 (by rfl) ⟨391406, by rfl⟩ : syracuseStep 2087501 = 782813) (by norm_num)
theorem B2349661 : Blo 1391515 2349661 := bbase (se 3 (by rfl) ⟨440561, by rfl⟩ : syracuseStep 2349661 = 881123) (by norm_num)
theorem B2087525 : Blo 1391515 2087525 := bbase (se 4 (by rfl) ⟨195705, by rfl⟩ : syracuseStep 2087525 = 391411) (by norm_num)
theorem B2087549 : Blo 1391515 2087549 := bbase (se 3 (by rfl) ⟨391415, by rfl⟩ : syracuseStep 2087549 = 782831) (by norm_num)
theorem B2087573 : Blo 1391515 2087573 := bbase (se 6 (by rfl) ⟨48927, by rfl⟩ : syracuseStep 2087573 = 97855) (by norm_num)
theorem B4766357 : Blo 1391515 4766357 := bbase (se 6 (by rfl) ⟨111711, by rfl⟩ : syracuseStep 4766357 = 223423) (by norm_num)
theorem B2644645 : Blo 1391515 2644645 := bbase (se 4 (by rfl) ⟨247935, by rfl⟩ : syracuseStep 2644645 = 495871) (by norm_num)
theorem B2087597 : Blo 1391515 2087597 := bbase (se 3 (by rfl) ⟨391424, by rfl⟩ : syracuseStep 2087597 = 782849) (by norm_num)
theorem B2349749 : Blo 1391515 2349749 := bbase (se 5 (by rfl) ⟨110144, by rfl⟩ : syracuseStep 2349749 = 220289) (by norm_num)
theorem B2087621 : Blo 1391515 2087621 := bbase (se 4 (by rfl) ⟨195714, by rfl⟩ : syracuseStep 2087621 = 391429) (by norm_num)
theorem B2087645 : Blo 1391515 2087645 := bbase (se 3 (by rfl) ⟨391433, by rfl⟩ : syracuseStep 2087645 = 782867) (by norm_num)
theorem B2087669 : Blo 1391515 2087669 := bbase (se 5 (by rfl) ⟨97859, by rfl⟩ : syracuseStep 2087669 = 195719) (by norm_num)
theorem B7052021 : Blo 1391515 7052021 := bbase (se 5 (by rfl) ⟨330563, by rfl⟩ : syracuseStep 7052021 = 661127) (by norm_num)
theorem B2087693 : Blo 1391515 2087693 := bbase (se 3 (by rfl) ⟨391442, by rfl⟩ : syracuseStep 2087693 = 782885) (by norm_num)
theorem B26753813 : Blo 1391515 26753813 := bbase (se 6 (by rfl) ⟨627042, by rfl⟩ : syracuseStep 26753813 = 1254085) (by norm_num)
theorem B2087717 : Blo 1391515 2087717 := bbase (se 4 (by rfl) ⟨195723, by rfl⟩ : syracuseStep 2087717 = 391447) (by norm_num)
theorem B2349877 : Blo 1391515 2349877 := bbase (se 5 (by rfl) ⟨110150, by rfl⟩ : syracuseStep 2349877 = 220301) (by norm_num)
theorem B2087741 : Blo 1391515 2087741 := bbase (se 3 (by rfl) ⟨391451, by rfl⟩ : syracuseStep 2087741 = 782903) (by norm_num)
theorem B2644805 : Blo 1391515 2644805 := bbase (se 4 (by rfl) ⟨247950, by rfl⟩ : syracuseStep 2644805 = 495901) (by norm_num)
theorem B2087765 : Blo 1391515 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B2087789 : Blo 1391515 2087789 := bbase (se 3 (by rfl) ⟨391460, by rfl⟩ : syracuseStep 2087789 = 782921) (by norm_num)
theorem B2087813 : Blo 1391515 2087813 := bbase (se 4 (by rfl) ⟨195732, by rfl⟩ : syracuseStep 2087813 = 391465) (by norm_num)
theorem B2349965 : Blo 1391515 2349965 := bbase (se 3 (by rfl) ⟨440618, by rfl⟩ : syracuseStep 2349965 = 881237) (by norm_num)
theorem B4701077 : Blo 1391515 4701077 := bbase (se 6 (by rfl) ⟨110181, by rfl⟩ : syracuseStep 4701077 = 220363) (by norm_num)
theorem B2087837 : Blo 1391515 2087837 := bbase (se 3 (by rfl) ⟨391469, by rfl⟩ : syracuseStep 2087837 = 782939) (by norm_num)
theorem B2087861 : Blo 1391515 2087861 := bbase (se 5 (by rfl) ⟨97868, by rfl⟩ : syracuseStep 2087861 = 195737) (by norm_num)
theorem B8919989 : Blo 1391515 8919989 := bbase (se 5 (by rfl) ⟨418124, by rfl⟩ : syracuseStep 8919989 = 836249) (by norm_num)
theorem B1907645 : Blo 1391515 1907645 := bbase (se 3 (by rfl) ⟨357683, by rfl⟩ : syracuseStep 1907645 = 715367) (by norm_num)
theorem B2087885 : Blo 1391515 2087885 := bbase (se 3 (by rfl) ⟨391478, by rfl⟩ : syracuseStep 2087885 = 782957) (by norm_num)
theorem B2972629 : Blo 1391515 2972629 := bbase (se 7 (by rfl) ⟨34835, by rfl⟩ : syracuseStep 2972629 = 69671) (by norm_num)
theorem B2644949 : Blo 1391515 2644949 := bbase (se 7 (by rfl) ⟨30995, by rfl⟩ : syracuseStep 2644949 = 61991) (by norm_num)
theorem B2087909 : Blo 1391515 2087909 := bbase (se 4 (by rfl) ⟨195741, by rfl⟩ : syracuseStep 2087909 = 391483) (by norm_num)
theorem B4234229 : Blo 1391515 4234229 := bbase (se 5 (by rfl) ⟨198479, by rfl⟩ : syracuseStep 4234229 = 396959) (by norm_num)
theorem B2087933 : Blo 1391515 2087933 := bbase (se 3 (by rfl) ⟨391487, by rfl⟩ : syracuseStep 2087933 = 782975) (by norm_num)
theorem B2350093 : Blo 1391515 2350093 := bbase (se 3 (by rfl) ⟨440642, by rfl⟩ : syracuseStep 2350093 = 881285) (by norm_num)
theorem B2087957 : Blo 1391515 2087957 := bbase (se 6 (by rfl) ⟨48936, by rfl⟩ : syracuseStep 2087957 = 97873) (by norm_num)
theorem B2087981 : Blo 1391515 2087981 := bbase (se 3 (by rfl) ⟨391496, by rfl⟩ : syracuseStep 2087981 = 782993) (by norm_num)
theorem B4021301 : Blo 1391515 4021301 := bbase (se 5 (by rfl) ⟨188498, by rfl⟩ : syracuseStep 4021301 = 376997) (by norm_num)
theorem B2088005 : Blo 1391515 2088005 := bbase (se 4 (by rfl) ⟨195750, by rfl⟩ : syracuseStep 2088005 = 391501) (by norm_num)
theorem B1981525 : Blo 1391515 1981525 := bbase (se 8 (by rfl) ⟨11610, by rfl⟩ : syracuseStep 1981525 = 23221) (by norm_num)
theorem B2088029 : Blo 1391515 2088029 := bbase (se 3 (by rfl) ⟨391505, by rfl⟩ : syracuseStep 2088029 = 783011) (by norm_num)
theorem B2350181 : Blo 1391515 2350181 := bbase (se 4 (by rfl) ⟨220329, by rfl⟩ : syracuseStep 2350181 = 440659) (by norm_num)
theorem B2088053 : Blo 1391515 2088053 := bbase (se 5 (by rfl) ⟨97877, by rfl⟩ : syracuseStep 2088053 = 195755) (by norm_num)
theorem B2088077 : Blo 1391515 2088077 := bbase (se 3 (by rfl) ⟨391514, by rfl⟩ : syracuseStep 2088077 = 783029) (by norm_num)
theorem B2088101 : Blo 1391515 2088101 := bbase (se 4 (by rfl) ⟨195759, by rfl⟩ : syracuseStep 2088101 = 391519) (by norm_num)
theorem B3054773 : Blo 1391515 3054773 := bbase (se 5 (by rfl) ⟨143192, by rfl⟩ : syracuseStep 3054773 = 286385) (by norm_num)
theorem B2088125 : Blo 1391515 2088125 := bbase (se 3 (by rfl) ⟨391523, by rfl⟩ : syracuseStep 2088125 = 783047) (by norm_num)
theorem B2088149 : Blo 1391515 2088149 := bbase (se 7 (by rfl) ⟨24470, by rfl⟩ : syracuseStep 2088149 = 48941) (by norm_num)
theorem B2350309 : Blo 1391515 2350309 := bbase (se 4 (by rfl) ⟨220341, by rfl⟩ : syracuseStep 2350309 = 440683) (by norm_num)
theorem B2088173 : Blo 1391515 2088173 := bbase (se 3 (by rfl) ⟨391532, by rfl⟩ : syracuseStep 2088173 = 783065) (by norm_num)
theorem B2645237 : Blo 1391515 2645237 := bbase (se 5 (by rfl) ⟨123995, by rfl⟩ : syracuseStep 2645237 = 247991) (by norm_num)
theorem B2088197 : Blo 1391515 2088197 := bbase (se 4 (by rfl) ⟨195768, by rfl⟩ : syracuseStep 2088197 = 391537) (by norm_num)
theorem B2088221 : Blo 1391515 2088221 := bbase (se 3 (by rfl) ⟨391541, by rfl⟩ : syracuseStep 2088221 = 783083) (by norm_num)
theorem B1981741 : Blo 1391515 1981741 := bbase (se 3 (by rfl) ⟨371576, by rfl⟩ : syracuseStep 1981741 = 743153) (by norm_num)
theorem B2088245 : Blo 1391515 2088245 := bbase (se 5 (by rfl) ⟨97886, by rfl⟩ : syracuseStep 2088245 = 195773) (by norm_num)
theorem B2350397 : Blo 1391515 2350397 := bbase (se 3 (by rfl) ⟨440699, by rfl⟩ : syracuseStep 2350397 = 881399) (by norm_num)
theorem B4701509 : Blo 1391515 4701509 := bbase (se 4 (by rfl) ⟨440766, by rfl⟩ : syracuseStep 4701509 = 881533) (by norm_num)
theorem B2088269 : Blo 1391515 2088269 := bbase (se 3 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 2088269 = 783101) (by norm_num)
theorem B13557077 : Blo 1391515 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B2088293 : Blo 1391515 2088293 := bbase (se 4 (by rfl) ⟨195777, by rfl⟩ : syracuseStep 2088293 = 391555) (by norm_num)
theorem B2088317 : Blo 1391515 2088317 := bbase (se 3 (by rfl) ⟨391559, by rfl⟩ : syracuseStep 2088317 = 783119) (by norm_num)
theorem B2645389 : Blo 1391515 2645389 := bbase (se 3 (by rfl) ⟨496010, by rfl⟩ : syracuseStep 2645389 = 992021) (by norm_num)
theorem B2088341 : Blo 1391515 2088341 := bbase (se 6 (by rfl) ⟨48945, by rfl⟩ : syracuseStep 2088341 = 97891) (by norm_num)
theorem B2088365 : Blo 1391515 2088365 := bbase (se 3 (by rfl) ⟨391568, by rfl⟩ : syracuseStep 2088365 = 783137) (by norm_num)
theorem B2350525 : Blo 1391515 2350525 := bbase (se 3 (by rfl) ⟨440723, by rfl⟩ : syracuseStep 2350525 = 881447) (by norm_num)
theorem B2973125 : Blo 1391515 2973125 := bbase (se 4 (by rfl) ⟨278730, by rfl⟩ : syracuseStep 2973125 = 557461) (by norm_num)
theorem B2088389 : Blo 1391515 2088389 := bbase (se 4 (by rfl) ⟨195786, by rfl⟩ : syracuseStep 2088389 = 391573) (by norm_num)
theorem B2088413 : Blo 1391515 2088413 := bbase (se 3 (by rfl) ⟨391577, by rfl⟩ : syracuseStep 2088413 = 783155) (by norm_num)
theorem B2088437 : Blo 1391515 2088437 := bbase (se 5 (by rfl) ⟨97895, by rfl⟩ : syracuseStep 2088437 = 195791) (by norm_num)
theorem B6692357 : Blo 1391515 6692357 := bbase (se 4 (by rfl) ⟨627408, by rfl⟩ : syracuseStep 6692357 = 1254817) (by norm_num)
theorem B2088461 : Blo 1391515 2088461 := bbase (se 3 (by rfl) ⟨391586, by rfl⟩ : syracuseStep 2088461 = 783173) (by norm_num)
theorem B2350613 : Blo 1391515 2350613 := bbase (se 6 (by rfl) ⟨55092, by rfl⟩ : syracuseStep 2350613 = 110185) (by norm_num)
theorem B15867413 : Blo 1391515 15867413 := bbase (se 6 (by rfl) ⟨371892, by rfl⟩ : syracuseStep 15867413 = 743785) (by norm_num)
theorem B2088485 : Blo 1391515 2088485 := bbase (se 4 (by rfl) ⟨195795, by rfl⟩ : syracuseStep 2088485 = 391591) (by norm_num)
theorem B2088509 : Blo 1391515 2088509 := bbase (se 3 (by rfl) ⟨391595, by rfl⟩ : syracuseStep 2088509 = 783191) (by norm_num)
theorem B5283413 : Blo 1391515 5283413 := bbase (se 8 (by rfl) ⟨30957, by rfl⟩ : syracuseStep 5283413 = 61915) (by norm_num)
theorem B2088533 : Blo 1391515 2088533 := bbase (se 8 (by rfl) ⟨12237, by rfl⟩ : syracuseStep 2088533 = 24475) (by norm_num)
theorem B6692453 : Blo 1391515 6692453 := bbase (se 4 (by rfl) ⟨627417, by rfl⟩ : syracuseStep 6692453 = 1254835) (by norm_num)
theorem B2088557 : Blo 1391515 2088557 := bbase (se 3 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 2088557 = 783209) (by norm_num)
theorem B5799557 : Blo 1391515 5799557 := bbase (se 4 (by rfl) ⟨543708, by rfl⟩ : syracuseStep 5799557 = 1087417) (by norm_num)
theorem B2088581 : Blo 1391515 2088581 := bbase (se 4 (by rfl) ⟨195804, by rfl⟩ : syracuseStep 2088581 = 391609) (by norm_num)
theorem B3964565 : Blo 1391515 3964565 := bbase (se 6 (by rfl) ⟨92919, by rfl⟩ : syracuseStep 3964565 = 185839) (by norm_num)
theorem B2350741 : Blo 1391515 2350741 := bbase (se 6 (by rfl) ⟨55095, by rfl⟩ : syracuseStep 2350741 = 110191) (by norm_num)
theorem B2088605 : Blo 1391515 2088605 := bbase (se 3 (by rfl) ⟨391613, by rfl⟩ : syracuseStep 2088605 = 783227) (by norm_num)
theorem B1982117 : Blo 1391515 1982117 := bbase (se 4 (by rfl) ⟨185823, by rfl⟩ : syracuseStep 1982117 = 371647) (by norm_num)
theorem B3391141 : Blo 1391515 3391141 := bbase (se 4 (by rfl) ⟨317919, by rfl⟩ : syracuseStep 3391141 = 635839) (by norm_num)
theorem B2088629 : Blo 1391515 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B2088653 : Blo 1391515 2088653 := bbase (se 3 (by rfl) ⟨391622, by rfl⟩ : syracuseStep 2088653 = 783245) (by norm_num)
theorem B2088677 : Blo 1391515 2088677 := bbase (se 4 (by rfl) ⟨195813, by rfl⟩ : syracuseStep 2088677 = 391627) (by norm_num)
theorem B2350829 : Blo 1391515 2350829 := bbase (se 3 (by rfl) ⟨440780, by rfl⟩ : syracuseStep 2350829 = 881561) (by norm_num)
theorem B4701941 : Blo 1391515 4701941 := bbase (se 5 (by rfl) ⟨220403, by rfl⟩ : syracuseStep 4701941 = 440807) (by norm_num)
theorem B2088701 : Blo 1391515 2088701 := bbase (se 3 (by rfl) ⟨391631, by rfl⟩ : syracuseStep 2088701 = 783263) (by norm_num)
theorem B3522325 : Blo 1391515 3522325 := bbase (se 6 (by rfl) ⟨82554, by rfl⟩ : syracuseStep 3522325 = 165109) (by norm_num)
theorem B2088725 : Blo 1391515 2088725 := bbase (se 6 (by rfl) ⟨48954, by rfl⟩ : syracuseStep 2088725 = 97909) (by norm_num)
theorem B1859365 : Blo 1391515 1859365 := bbase (se 4 (by rfl) ⟨174315, by rfl⟩ : syracuseStep 1859365 = 348631) (by norm_num)
theorem B2088749 : Blo 1391515 2088749 := bbase (se 3 (by rfl) ⟨391640, by rfl⟩ : syracuseStep 2088749 = 783281) (by norm_num)
theorem B2088773 : Blo 1391515 2088773 := bbase (se 4 (by rfl) ⟨195822, by rfl⟩ : syracuseStep 2088773 = 391645) (by norm_num)
theorem B2088797 : Blo 1391515 2088797 := bbase (se 3 (by rfl) ⟨391649, by rfl⟩ : syracuseStep 2088797 = 783299) (by norm_num)
theorem B2350957 : Blo 1391515 2350957 := bbase (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) (by norm_num)
theorem B5283701 : Blo 1391515 5283701 := bbase (se 5 (by rfl) ⟨247673, by rfl⟩ : syracuseStep 5283701 = 495347) (by norm_num)
theorem B2088821 : Blo 1391515 2088821 := bbase (se 5 (by rfl) ⟨97913, by rfl⟩ : syracuseStep 2088821 = 195827) (by norm_num)
theorem B3522437 : Blo 1391515 3522437 := bbase (se 4 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 3522437 = 660457) (by norm_num)
theorem B2088845 : Blo 1391515 2088845 := bbase (se 3 (by rfl) ⟨391658, by rfl⟩ : syracuseStep 2088845 = 783317) (by norm_num)
theorem B2088869 : Blo 1391515 2088869 := bbase (se 4 (by rfl) ⟨195831, by rfl⟩ : syracuseStep 2088869 = 391663) (by norm_num)
theorem B1761193 : Blo 1391515 1761193 := bbase (se 2 (by rfl) ⟨660447, by rfl⟩ : syracuseStep 1761193 = 1320895) (by norm_num)
theorem B2088893 : Blo 1391515 2088893 := bbase (se 3 (by rfl) ⟨391667, by rfl⟩ : syracuseStep 2088893 = 783335) (by norm_num)
theorem B2351045 : Blo 1391515 2351045 := bbase (se 4 (by rfl) ⟨220410, by rfl⟩ : syracuseStep 2351045 = 440821) (by norm_num)
theorem B2088917 : Blo 1391515 2088917 := bbase (se 7 (by rfl) ⟨24479, by rfl⟩ : syracuseStep 2088917 = 48959) (by norm_num)
theorem B2088941 : Blo 1391515 2088941 := bbase (se 3 (by rfl) ⟨391676, by rfl⟩ : syracuseStep 2088941 = 783353) (by norm_num)
theorem B1392643 : Blo 1391515 1392643 := bstep (se 1 (by rfl) ⟨1044482, by rfl⟩ : syracuseStep 1392643 = 2088965) B2088965
theorem B4702211 : Blo 1391515 4702211 := bstep (se 1 (by rfl) ⟨3526658, by rfl⟩ : syracuseStep 4702211 = 7053317) B7053317
theorem B2088977 : Blo 1391515 2088977 := bstep (se 2 (by rfl) ⟨783366, by rfl⟩ : syracuseStep 2088977 = 1566733) B1566733
theorem B1392659 : Blo 1391515 1392659 := bstep (se 1 (by rfl) ⟨1044494, by rfl⟩ : syracuseStep 1392659 = 2088989) B2088989
theorem B3964963 : Blo 1391515 3964963 := bstep (se 1 (by rfl) ⟨2973722, by rfl⟩ : syracuseStep 3964963 = 5947445) B5947445
theorem B2088995 : Blo 1391515 2088995 := bstep (se 1 (by rfl) ⟨1566746, by rfl⟩ : syracuseStep 2088995 = 3133493) B3133493
theorem B1392675 : Blo 1391515 1392675 := bstep (se 1 (by rfl) ⟨1044506, by rfl⟩ : syracuseStep 1392675 = 2089013) B2089013
theorem B2351153 : Blo 1391515 2351153 := bstep (se 2 (by rfl) ⟨881682, by rfl⟩ : syracuseStep 2351153 = 1763365) B1763365
theorem B1392691 : Blo 1391515 1392691 := bstep (se 1 (by rfl) ⟨1044518, by rfl⟩ : syracuseStep 1392691 = 2089037) B2089037
theorem B2089025 : Blo 1391515 2089025 := bstep (se 2 (by rfl) ⟨783384, by rfl⟩ : syracuseStep 2089025 = 1566769) B1566769
theorem B1392707 : Blo 1391515 1392707 := bstep (se 1 (by rfl) ⟨1044530, by rfl⟩ : syracuseStep 1392707 = 2089061) B2089061
theorem B2089043 : Blo 1391515 2089043 := bstep (se 1 (by rfl) ⟨1566782, by rfl⟩ : syracuseStep 2089043 = 3133565) B3133565
theorem B1392723 : Blo 1391515 1392723 := bstep (se 1 (by rfl) ⟨1044542, by rfl⟩ : syracuseStep 1392723 = 2089085) B2089085
theorem B1982561 : Blo 1391515 1982561 := bstep (se 2 (by rfl) ⟨743460, by rfl⟩ : syracuseStep 1982561 = 1486921) B1486921
theorem B1392739 : Blo 1391515 1392739 := bstep (se 1 (by rfl) ⟨1044554, by rfl⟩ : syracuseStep 1392739 = 2089109) B2089109
theorem B2089073 : Blo 1391515 2089073 := bstep (se 2 (by rfl) ⟨783402, by rfl⟩ : syracuseStep 2089073 = 1566805) B1566805
theorem B1392755 : Blo 1391515 1392755 := bstep (se 1 (by rfl) ⟨1044566, by rfl⟩ : syracuseStep 1392755 = 2089133) B2089133
theorem B2089091 : Blo 1391515 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B1392771 : Blo 1391515 1392771 := bstep (se 1 (by rfl) ⟨1044578, by rfl⟩ : syracuseStep 1392771 = 2089157) B2089157
theorem B1392787 : Blo 1391515 1392787 := bstep (se 1 (by rfl) ⟨1044590, by rfl⟩ : syracuseStep 1392787 = 2089181) B2089181
theorem B2089121 : Blo 1391515 2089121 := bstep (se 2 (by rfl) ⟨783420, by rfl⟩ : syracuseStep 2089121 = 1566841) B1566841
theorem B1392803 : Blo 1391515 1392803 := bstep (se 1 (by rfl) ⟨1044602, by rfl⟩ : syracuseStep 1392803 = 2089205) B2089205
theorem B2351281 : Blo 1391515 2351281 := bstep (se 2 (by rfl) ⟨881730, by rfl⟩ : syracuseStep 2351281 = 1763461) B1763461
theorem B2089139 : Blo 1391515 2089139 := bstep (se 1 (by rfl) ⟨1566854, by rfl⟩ : syracuseStep 2089139 = 3133709) B3133709
theorem B1392819 : Blo 1391515 1392819 := bstep (se 1 (by rfl) ⟨1044614, by rfl⟩ : syracuseStep 1392819 = 2089229) B2089229
theorem B1392835 : Blo 1391515 1392835 := bstep (se 1 (by rfl) ⟨1044626, by rfl⟩ : syracuseStep 1392835 = 2089253) B2089253
theorem B2089169 : Blo 1391515 2089169 := bstep (se 2 (by rfl) ⟨783438, by rfl⟩ : syracuseStep 2089169 = 1566877) B1566877
theorem B1982675 : Blo 1391515 1982675 := bstep (se 1 (by rfl) ⟨1487006, by rfl⟩ : syracuseStep 1982675 = 2974013) B2974013
theorem B1392851 : Blo 1391515 1392851 := bstep (se 1 (by rfl) ⟨1044638, by rfl⟩ : syracuseStep 1392851 = 2089277) B2089277
theorem B2351315 : Blo 1391515 2351315 := bstep (se 1 (by rfl) ⟨1763486, by rfl⟩ : syracuseStep 2351315 = 3526973) B3526973
theorem B2089187 : Blo 1391515 2089187 := bstep (se 1 (by rfl) ⟨1566890, by rfl⟩ : syracuseStep 2089187 = 3133781) B3133781
theorem B1392867 : Blo 1391515 1392867 := bstep (se 1 (by rfl) ⟨1044650, by rfl⟩ : syracuseStep 1392867 = 2089301) B2089301
theorem B1392883 : Blo 1391515 1392883 := bstep (se 1 (by rfl) ⟨1044662, by rfl⟩ : syracuseStep 1392883 = 2089325) B2089325
theorem B2089217 : Blo 1391515 2089217 := bstep (se 2 (by rfl) ⟨783456, by rfl⟩ : syracuseStep 2089217 = 1566913) B1566913
theorem B1392899 : Blo 1391515 1392899 := bstep (se 1 (by rfl) ⟨1044674, by rfl⟩ : syracuseStep 1392899 = 2089349) B2089349
theorem B3571985 : Blo 1391515 3571985 := bstep (se 2 (by rfl) ⟨1339494, by rfl⟩ : syracuseStep 3571985 = 2678989) B2678989
theorem B4702481 : Blo 1391515 4702481 := bstep (se 2 (by rfl) ⟨1763430, by rfl⟩ : syracuseStep 4702481 = 3526861) B3526861
theorem B2089235 : Blo 1391515 2089235 := bstep (se 1 (by rfl) ⟨1566926, by rfl⟩ : syracuseStep 2089235 = 3133853) B3133853
theorem B1392915 : Blo 1391515 1392915 := bstep (se 1 (by rfl) ⟨1044686, by rfl⟩ : syracuseStep 1392915 = 2089373) B2089373
theorem B1982755 : Blo 1391515 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B1392931 : Blo 1391515 1392931 := bstep (se 1 (by rfl) ⟨1044698, by rfl⟩ : syracuseStep 1392931 = 2089397) B2089397
theorem B2089265 : Blo 1391515 2089265 := bstep (se 2 (by rfl) ⟨783474, by rfl⟩ : syracuseStep 2089265 = 1566949) B1566949
theorem B1392947 : Blo 1391515 1392947 := bstep (se 1 (by rfl) ⟨1044710, by rfl⟩ : syracuseStep 1392947 = 2089421) B2089421
theorem B2089283 : Blo 1391515 2089283 := bstep (se 1 (by rfl) ⟨1566962, by rfl⟩ : syracuseStep 2089283 = 3133925) B3133925
theorem B1392963 : Blo 1391515 1392963 := bstep (se 1 (by rfl) ⟨1044722, by rfl⟩ : syracuseStep 1392963 = 2089445) B2089445
theorem B1392979 : Blo 1391515 1392979 := bstep (se 1 (by rfl) ⟨1044734, by rfl⟩ : syracuseStep 1392979 = 2089469) B2089469
theorem B2351443 : Blo 1391515 2351443 := bstep (se 1 (by rfl) ⟨1763582, by rfl⟩ : syracuseStep 2351443 = 3527165) B3527165
theorem B2089313 : Blo 1391515 2089313 := bstep (se 2 (by rfl) ⟨783492, by rfl⟩ : syracuseStep 2089313 = 1566985) B1566985
theorem B1392995 : Blo 1391515 1392995 := bstep (se 1 (by rfl) ⟨1044746, by rfl⟩ : syracuseStep 1392995 = 2089493) B2089493
theorem B2089331 : Blo 1391515 2089331 := bstep (se 1 (by rfl) ⟨1566998, by rfl⟩ : syracuseStep 2089331 = 3133997) B3133997
theorem B1393011 : Blo 1391515 1393011 := bstep (se 1 (by rfl) ⟨1044758, by rfl⟩ : syracuseStep 1393011 = 2089517) B2089517
theorem B1393027 : Blo 1391515 1393027 := bstep (se 1 (by rfl) ⟨1044770, by rfl⟩ : syracuseStep 1393027 = 2089541) B2089541
theorem B2089361 : Blo 1391515 2089361 := bstep (se 2 (by rfl) ⟨783510, by rfl⟩ : syracuseStep 2089361 = 1567021) B1567021
theorem B1393043 : Blo 1391515 1393043 := bstep (se 1 (by rfl) ⟨1044782, by rfl⟩ : syracuseStep 1393043 = 2089565) B2089565
theorem B2146721 : Blo 1391515 2146721 := bstep (se 2 (by rfl) ⟨805020, by rfl⟩ : syracuseStep 2146721 = 1610041) B1610041
theorem B2974115 : Blo 1391515 2974115 := bstep (se 1 (by rfl) ⟨2230586, by rfl⟩ : syracuseStep 2974115 = 4461173) B4461173
theorem B2089379 : Blo 1391515 2089379 := bstep (se 1 (by rfl) ⟨1567034, by rfl⟩ : syracuseStep 2089379 = 3134069) B3134069
theorem B1393059 : Blo 1391515 1393059 := bstep (se 1 (by rfl) ⟨1044794, by rfl⟩ : syracuseStep 1393059 = 2089589) B2089589
theorem B1393075 : Blo 1391515 1393075 := bstep (se 1 (by rfl) ⟨1044806, by rfl⟩ : syracuseStep 1393075 = 2089613) B2089613
theorem B2089409 : Blo 1391515 2089409 := bstep (se 2 (by rfl) ⟨783528, by rfl⟩ : syracuseStep 2089409 = 1567057) B1567057
theorem B1393091 : Blo 1391515 1393091 := bstep (se 1 (by rfl) ⟨1044818, by rfl⟩ : syracuseStep 1393091 = 2089637) B2089637
theorem B2089427 : Blo 1391515 2089427 := bstep (se 1 (by rfl) ⟨1567070, by rfl⟩ : syracuseStep 2089427 = 3134141) B3134141
theorem B1393107 : Blo 1391515 1393107 := bstep (se 1 (by rfl) ⟨1044830, by rfl⟩ : syracuseStep 1393107 = 2089661) B2089661
theorem B1393123 : Blo 1391515 1393123 := bstep (se 1 (by rfl) ⟨1044842, by rfl⟩ : syracuseStep 1393123 = 2089685) B2089685
theorem B2089457 : Blo 1391515 2089457 := bstep (se 2 (by rfl) ⟨783546, by rfl⟩ : syracuseStep 2089457 = 1567093) B1567093
theorem B1393139 : Blo 1391515 1393139 := bstep (se 1 (by rfl) ⟨1044854, by rfl⟩ : syracuseStep 1393139 = 2089709) B2089709
theorem B2089475 : Blo 1391515 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B1393155 : Blo 1391515 1393155 := bstep (se 1 (by rfl) ⟨1044866, by rfl⟩ : syracuseStep 1393155 = 2089733) B2089733
theorem B13378061 : Blo 1391515 13378061 := bstep (se 3 (by rfl) ⟨2508386, by rfl⟩ : syracuseStep 13378061 = 5016773) B5016773
theorem B1393171 : Blo 1391515 1393171 := bstep (se 1 (by rfl) ⟨1044878, by rfl⟩ : syracuseStep 1393171 = 2089757) B2089757
theorem B2089505 : Blo 1391515 2089505 := bstep (se 2 (by rfl) ⟨783564, by rfl⟩ : syracuseStep 2089505 = 1567129) B1567129
theorem B1393187 : Blo 1391515 1393187 := bstep (se 1 (by rfl) ⟨1044890, by rfl⟩ : syracuseStep 1393187 = 2089781) B2089781
theorem B2089523 : Blo 1391515 2089523 := bstep (se 1 (by rfl) ⟨1567142, by rfl⟩ : syracuseStep 2089523 = 3134285) B3134285
theorem B1393203 : Blo 1391515 1393203 := bstep (se 1 (by rfl) ⟨1044902, by rfl⟩ : syracuseStep 1393203 = 2089805) B2089805
theorem B1393219 : Blo 1391515 1393219 := bstep (se 1 (by rfl) ⟨1044914, by rfl⟩ : syracuseStep 1393219 = 2089829) B2089829
theorem B2089553 : Blo 1391515 2089553 := bstep (se 2 (by rfl) ⟨783582, by rfl⟩ : syracuseStep 2089553 = 1567165) B1567165
theorem B1393235 : Blo 1391515 1393235 := bstep (se 1 (by rfl) ⟨1044926, by rfl⟩ : syracuseStep 1393235 = 2089853) B2089853
theorem B2089571 : Blo 1391515 2089571 := bstep (se 1 (by rfl) ⟨1567178, by rfl⟩ : syracuseStep 2089571 = 3134357) B3134357
theorem B1393251 : Blo 1391515 1393251 := bstep (se 1 (by rfl) ⟨1044938, by rfl⟩ : syracuseStep 1393251 = 2089877) B2089877
theorem B1761907 : Blo 1391515 1761907 := bstep (se 1 (by rfl) ⟨1321430, by rfl⟩ : syracuseStep 1761907 = 2642861) B2642861
theorem B1393267 : Blo 1391515 1393267 := bstep (se 1 (by rfl) ⟨1044950, by rfl⟩ : syracuseStep 1393267 = 2089901) B2089901
theorem B2089601 : Blo 1391515 2089601 := bstep (se 2 (by rfl) ⟨783600, by rfl⟩ : syracuseStep 2089601 = 1567201) B1567201
theorem B1393283 : Blo 1391515 1393283 := bstep (se 1 (by rfl) ⟨1044962, by rfl⟩ : syracuseStep 1393283 = 2089925) B2089925
theorem B7053965 : Blo 1391515 7053965 := bstep (se 3 (by rfl) ⟨1322618, by rfl⟩ : syracuseStep 7053965 = 2645237) B2645237
theorem B2089619 : Blo 1391515 2089619 := bstep (se 1 (by rfl) ⟨1567214, by rfl⟩ : syracuseStep 2089619 = 3134429) B3134429
theorem B1393299 : Blo 1391515 1393299 := bstep (se 1 (by rfl) ⟨1044974, by rfl⟩ : syracuseStep 1393299 = 2089949) B2089949
theorem B1393315 : Blo 1391515 1393315 := bstep (se 1 (by rfl) ⟨1044986, by rfl⟩ : syracuseStep 1393315 = 2089973) B2089973
theorem B5358257 : Blo 1391515 5358257 := bstep (se 2 (by rfl) ⟨2009346, by rfl⟩ : syracuseStep 5358257 = 4018693) B4018693
theorem B2089649 : Blo 1391515 2089649 := bstep (se 2 (by rfl) ⟨783618, by rfl⟩ : syracuseStep 2089649 = 1567237) B1567237
theorem B1671859 : Blo 1391515 1671859 := bstep (se 1 (by rfl) ⟨1253894, by rfl⟩ : syracuseStep 1671859 = 2507789) B2507789
theorem B1393331 : Blo 1391515 1393331 := bstep (se 1 (by rfl) ⟨1044998, by rfl⟩ : syracuseStep 1393331 = 2089997) B2089997
theorem B2089667 : Blo 1391515 2089667 := bstep (se 1 (by rfl) ⟨1567250, by rfl⟩ : syracuseStep 2089667 = 3134501) B3134501
theorem B1393347 : Blo 1391515 1393347 := bstep (se 1 (by rfl) ⟨1045010, by rfl⟩ : syracuseStep 1393347 = 2090021) B2090021
theorem B1762003 : Blo 1391515 1762003 := bstep (se 1 (by rfl) ⟨1321502, by rfl⟩ : syracuseStep 1762003 = 2643005) B2643005
theorem B1393363 : Blo 1391515 1393363 := bstep (se 1 (by rfl) ⟨1045022, by rfl⟩ : syracuseStep 1393363 = 2090045) B2090045
theorem B2089697 : Blo 1391515 2089697 := bstep (se 2 (by rfl) ⟨783636, by rfl⟩ : syracuseStep 2089697 = 1567273) B1567273
theorem B1393379 : Blo 1391515 1393379 := bstep (se 1 (by rfl) ⟨1045034, by rfl⟩ : syracuseStep 1393379 = 2090069) B2090069
theorem B2089715 : Blo 1391515 2089715 := bstep (se 1 (by rfl) ⟨1567286, by rfl⟩ : syracuseStep 2089715 = 3134573) B3134573
theorem B1393395 : Blo 1391515 1393395 := bstep (se 1 (by rfl) ⟨1045046, by rfl⟩ : syracuseStep 1393395 = 2090093) B2090093
theorem B1393411 : Blo 1391515 1393411 := bstep (se 1 (by rfl) ⟨1045058, by rfl⟩ : syracuseStep 1393411 = 2090117) B2090117
theorem B2089745 : Blo 1391515 2089745 := bstep (se 2 (by rfl) ⟨783654, by rfl⟩ : syracuseStep 2089745 = 1567309) B1567309
theorem B1393427 : Blo 1391515 1393427 := bstep (se 1 (by rfl) ⟨1045070, by rfl⟩ : syracuseStep 1393427 = 2090141) B2090141
theorem B2089763 : Blo 1391515 2089763 := bstep (se 1 (by rfl) ⟨1567322, by rfl⟩ : syracuseStep 2089763 = 3134645) B3134645
theorem B1393443 : Blo 1391515 1393443 := bstep (se 1 (by rfl) ⟨1045082, by rfl⟩ : syracuseStep 1393443 = 2090165) B2090165
theorem B4703021 : Blo 1391515 4703021 := bstep (se 3 (by rfl) ⟨881816, by rfl⟩ : syracuseStep 4703021 = 1763633) B1763633
theorem B1565491 : Blo 1391515 1565491 := bstep (se 1 (by rfl) ⟨1174118, by rfl⟩ : syracuseStep 1565491 = 2348237) B2348237
theorem B1393459 : Blo 1391515 1393459 := bstep (se 1 (by rfl) ⟨1045094, by rfl⟩ : syracuseStep 1393459 = 2090189) B2090189
theorem B21439285 : Blo 1391515 21439285 := bstep (se 5 (by rfl) ⟨1004966, by rfl⟩ : syracuseStep 21439285 = 2009933) B2009933
theorem B2089793 : Blo 1391515 2089793 := bstep (se 2 (by rfl) ⟨783672, by rfl⟩ : syracuseStep 2089793 = 1567345) B1567345
theorem B1393475 : Blo 1391515 1393475 := bstep (se 1 (by rfl) ⟨1045106, by rfl⟩ : syracuseStep 1393475 = 2090213) B2090213
theorem B3523409 : Blo 1391515 3523409 := bstep (se 2 (by rfl) ⟨1321278, by rfl⟩ : syracuseStep 3523409 = 2642557) B2642557
theorem B1983313 : Blo 1391515 1983313 := bstep (se 2 (by rfl) ⟨743742, by rfl⟩ : syracuseStep 1983313 = 1487485) B1487485
theorem B2089811 : Blo 1391515 2089811 := bstep (se 1 (by rfl) ⟨1567358, by rfl⟩ : syracuseStep 2089811 = 3134717) B3134717
theorem B1393491 : Blo 1391515 1393491 := bstep (se 1 (by rfl) ⟨1045118, by rfl⟩ : syracuseStep 1393491 = 2090237) B2090237
theorem B4703075 : Blo 1391515 4703075 := bstep (se 1 (by rfl) ⟨3527306, by rfl⟩ : syracuseStep 4703075 = 7054613) B7054613
theorem B1393507 : Blo 1391515 1393507 := bstep (se 1 (by rfl) ⟨1045130, by rfl⟩ : syracuseStep 1393507 = 2090261) B2090261
theorem B2089841 : Blo 1391515 2089841 := bstep (se 2 (by rfl) ⟨783690, by rfl⟩ : syracuseStep 2089841 = 1567381) B1567381
theorem B3523459 : Blo 1391515 3523459 := bstep (se 1 (by rfl) ⟨2642594, by rfl⟩ : syracuseStep 3523459 = 5285189) B5285189
theorem B2089859 : Blo 1391515 2089859 := bstep (se 1 (by rfl) ⟨1567394, by rfl⟩ : syracuseStep 2089859 = 3134789) B3134789
theorem B2089889 : Blo 1391515 2089889 := bstep (se 2 (by rfl) ⟨783708, by rfl⟩ : syracuseStep 2089889 = 1567417) B1567417
theorem B2089907 : Blo 1391515 2089907 := bstep (se 1 (by rfl) ⟨1567430, by rfl⟩ : syracuseStep 2089907 = 3134861) B3134861
theorem B15057845 : Blo 1391515 15057845 := bstep (se 5 (by rfl) ⟨705836, by rfl⟩ : syracuseStep 15057845 = 1411673) B1411673
theorem B1565635 : Blo 1391515 1565635 := bstep (se 1 (by rfl) ⟨1174226, by rfl⟩ : syracuseStep 1565635 = 2348453) B2348453
theorem B2089937 : Blo 1391515 2089937 := bstep (se 2 (by rfl) ⟨783726, by rfl⟩ : syracuseStep 2089937 = 1567453) B1567453
theorem B2229203 : Blo 1391515 2229203 := bstep (se 1 (by rfl) ⟨1671902, by rfl⟩ : syracuseStep 2229203 = 3343805) B3343805
theorem B2089955 : Blo 1391515 2089955 := bstep (se 1 (by rfl) ⟨1567466, by rfl⟩ : syracuseStep 2089955 = 3134933) B3134933
theorem B2089985 : Blo 1391515 2089985 := bstep (se 2 (by rfl) ⟨783744, by rfl⟩ : syracuseStep 2089985 = 1567489) B1567489
theorem B3523601 : Blo 1391515 3523601 := bstep (se 2 (by rfl) ⟨1321350, by rfl⟩ : syracuseStep 3523601 = 2642701) B2642701
theorem B2090003 : Blo 1391515 2090003 := bstep (se 1 (by rfl) ⟨1567502, by rfl⟩ : syracuseStep 2090003 = 3135005) B3135005
theorem B2090033 : Blo 1391515 2090033 := bstep (se 2 (by rfl) ⟨783762, by rfl⟩ : syracuseStep 2090033 = 1567525) B1567525
theorem B17409077 : Blo 1391515 17409077 := bstep (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) B1632101
theorem B2090051 : Blo 1391515 2090051 := bstep (se 1 (by rfl) ⟨1567538, by rfl⟩ : syracuseStep 2090051 = 3135077) B3135077
theorem B1565779 : Blo 1391515 1565779 := bstep (se 1 (by rfl) ⟨1174334, by rfl⟩ : syracuseStep 1565779 = 2348669) B2348669
theorem B2090081 : Blo 1391515 2090081 := bstep (se 2 (by rfl) ⟨783780, by rfl⟩ : syracuseStep 2090081 = 1567561) B1567561
theorem B2679907 : Blo 1391515 2679907 := bstep (se 1 (by rfl) ⟨2009930, by rfl⟩ : syracuseStep 2679907 = 4019861) B4019861
theorem B2090099 : Blo 1391515 2090099 := bstep (se 1 (by rfl) ⟨1567574, by rfl⟩ : syracuseStep 2090099 = 3135149) B3135149
theorem B2090129 : Blo 1391515 2090129 := bstep (se 2 (by rfl) ⟨783798, by rfl⟩ : syracuseStep 2090129 = 1567597) B1567597
theorem B2090147 : Blo 1391515 2090147 := bstep (se 1 (by rfl) ⟨1567610, by rfl⟩ : syracuseStep 2090147 = 3135221) B3135221
theorem B7144625 : Blo 1391515 7144625 := bstep (se 2 (by rfl) ⟨2679234, by rfl⟩ : syracuseStep 7144625 = 5358469) B5358469
theorem B2090177 : Blo 1391515 2090177 := bstep (se 2 (by rfl) ⟨783816, by rfl⟩ : syracuseStep 2090177 = 1567633) B1567633
theorem B1762499 : Blo 1391515 1762499 := bstep (se 1 (by rfl) ⟨1321874, by rfl⟩ : syracuseStep 1762499 = 2643749) B2643749
theorem B2090195 : Blo 1391515 2090195 := bstep (se 1 (by rfl) ⟨1567646, by rfl⟩ : syracuseStep 2090195 = 3135293) B3135293
theorem B1565923 : Blo 1391515 1565923 := bstep (se 1 (by rfl) ⟨1174442, by rfl⟩ : syracuseStep 1565923 = 2348885) B2348885
theorem B2090225 : Blo 1391515 2090225 := bstep (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) B1567669
theorem B2090243 : Blo 1391515 2090243 := bstep (se 1 (by rfl) ⟨1567682, by rfl⟩ : syracuseStep 2090243 = 3135365) B3135365
theorem B17851661 : Blo 1391515 17851661 := bstep (se 3 (by rfl) ⟨3347186, by rfl⟩ : syracuseStep 17851661 = 6694373) B6694373
theorem B2090273 : Blo 1391515 2090273 := bstep (se 2 (by rfl) ⟨783852, by rfl⟩ : syracuseStep 2090273 = 1567705) B1567705
theorem B11887985 : Blo 1391515 11887985 := bstep (se 2 (by rfl) ⟨4457994, by rfl⟩ : syracuseStep 11887985 = 8915989) B8915989
theorem B7046513 : Blo 1391515 7046513 := bstep (se 2 (by rfl) ⟨2642442, by rfl⟩ : syracuseStep 7046513 = 5284885) B5284885
theorem B1566067 : Blo 1391515 1566067 := bstep (se 1 (by rfl) ⟨1174550, by rfl⟩ : syracuseStep 1566067 = 2349101) B2349101
theorem B3966353 : Blo 1391515 3966353 := bstep (se 2 (by rfl) ⟨1487382, by rfl⟩ : syracuseStep 3966353 = 2974765) B2974765
theorem B2229715 : Blo 1391515 2229715 := bstep (se 1 (by rfl) ⟨1672286, by rfl⟩ : syracuseStep 2229715 = 3344573) B3344573
theorem B2229761 : Blo 1391515 2229761 := bstep (se 2 (by rfl) ⟨836160, by rfl⟩ : syracuseStep 2229761 = 1672321) B1672321
theorem B2262529 : Blo 1391515 2262529 := bstep (se 2 (by rfl) ⟨848448, by rfl⟩ : syracuseStep 2262529 = 1696897) B1696897
theorem B1566211 : Blo 1391515 1566211 := bstep (se 1 (by rfl) ⟨1174658, by rfl⟩ : syracuseStep 1566211 = 2349317) B2349317
theorem B1984019 : Blo 1391515 1984019 := bstep (se 1 (by rfl) ⟨1488014, by rfl⟩ : syracuseStep 1984019 = 2976029) B2976029
theorem B2975363 : Blo 1391515 2975363 := bstep (se 1 (by rfl) ⟨2231522, by rfl⟩ : syracuseStep 2975363 = 4463045) B4463045
theorem B8152709 : Blo 1391515 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B1566355 : Blo 1391515 1566355 := bstep (se 1 (by rfl) ⟨1174766, by rfl⟩ : syracuseStep 1566355 = 2349533) B2349533
theorem B5285645 : Blo 1391515 5285645 := bstep (se 3 (by rfl) ⟨991058, by rfl⟩ : syracuseStep 5285645 = 1982117) B1982117
theorem B3131153 : Blo 1391515 3131153 := bstep (se 2 (by rfl) ⟨1174182, by rfl⟩ : syracuseStep 3131153 = 2348365) B2348365
theorem B3131171 : Blo 1391515 3131171 := bstep (se 1 (by rfl) ⟨2348378, by rfl⟩ : syracuseStep 3131171 = 4696757) B4696757
theorem B1566499 : Blo 1391515 1566499 := bstep (se 1 (by rfl) ⟨1174874, by rfl⟩ : syracuseStep 1566499 = 2349749) B2349749
theorem B17835875 : Blo 1391515 17835875 := bstep (se 1 (by rfl) ⟨13376906, by rfl⟩ : syracuseStep 17835875 = 26753813) B26753813
theorem B1763203 : Blo 1391515 1763203 := bstep (se 1 (by rfl) ⟨1322402, by rfl⟩ : syracuseStep 1763203 = 2644805) B2644805
theorem B1566643 : Blo 1391515 1566643 := bstep (se 1 (by rfl) ⟨1174982, by rfl⟩ : syracuseStep 1566643 = 2349965) B2349965
theorem B1763299 : Blo 1391515 1763299 := bstep (se 1 (by rfl) ⟨1322474, by rfl⟩ : syracuseStep 1763299 = 2644949) B2644949
theorem B4524013 : Blo 1391515 4524013 := bstep (se 3 (by rfl) ⟨848252, by rfl⟩ : syracuseStep 4524013 = 1696505) B1696505
theorem B3524593 : Blo 1391515 3524593 := bstep (se 2 (by rfl) ⟨1321722, by rfl⟩ : syracuseStep 3524593 = 2643445) B2643445
theorem B3344419 : Blo 1391515 3344419 := bstep (se 1 (by rfl) ⟨2508314, by rfl⟩ : syracuseStep 3344419 = 5016629) B5016629
theorem B2680867 : Blo 1391515 2680867 := bstep (se 1 (by rfl) ⟨2010650, by rfl⟩ : syracuseStep 2680867 = 4021301) B4021301
theorem B3131441 : Blo 1391515 3131441 := bstep (se 2 (by rfl) ⟨1174290, by rfl⟩ : syracuseStep 3131441 = 2348581) B2348581
theorem B3131459 : Blo 1391515 3131459 := bstep (se 1 (by rfl) ⟨2348594, by rfl⟩ : syracuseStep 3131459 = 4697189) B4697189
theorem B1566787 : Blo 1391515 1566787 := bstep (se 1 (by rfl) ⟨1175090, by rfl⟩ : syracuseStep 1566787 = 2350181) B2350181
theorem B2230433 : Blo 1391515 2230433 := bstep (se 2 (by rfl) ⟨836412, by rfl⟩ : syracuseStep 2230433 = 1672825) B1672825
theorem B4458701 : Blo 1391515 4458701 := bstep (se 3 (by rfl) ⟨836006, by rfl⟩ : syracuseStep 4458701 = 1672013) B1672013
theorem B2975953 : Blo 1391515 2975953 := bstep (se 2 (by rfl) ⟨1115982, by rfl⟩ : syracuseStep 2975953 = 2231965) B2231965
theorem B1566931 : Blo 1391515 1566931 := bstep (se 1 (by rfl) ⟨1175198, by rfl⟩ : syracuseStep 1566931 = 2350397) B2350397
theorem B9038051 : Blo 1391515 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B3524867 : Blo 1391515 3524867 := bstep (se 1 (by rfl) ⟨2643650, by rfl⟩ : syracuseStep 3524867 = 5287301) B5287301
theorem B2115857 : Blo 1391515 2115857 := bstep (se 2 (by rfl) ⟨793446, by rfl⟩ : syracuseStep 2115857 = 1586893) B1586893
theorem B9529649 : Blo 1391515 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B3967309 : Blo 1391515 3967309 := bstep (se 3 (by rfl) ⟨743870, by rfl⟩ : syracuseStep 3967309 = 1487741) B1487741
theorem B3131729 : Blo 1391515 3131729 := bstep (se 2 (by rfl) ⟨1174398, by rfl⟩ : syracuseStep 3131729 = 2348797) B2348797
theorem B1673555 : Blo 1391515 1673555 := bstep (se 1 (by rfl) ⟨1255166, by rfl⟩ : syracuseStep 1673555 = 2510333) B2510333
theorem B3131747 : Blo 1391515 3131747 := bstep (se 1 (by rfl) ⟨2348810, by rfl⟩ : syracuseStep 3131747 = 4697621) B4697621
theorem B1567075 : Blo 1391515 1567075 := bstep (se 1 (by rfl) ⟨1175306, by rfl⟩ : syracuseStep 1567075 = 2350613) B2350613
theorem B10578275 : Blo 1391515 10578275 := bstep (se 1 (by rfl) ⟨7933706, by rfl⟩ : syracuseStep 10578275 = 15867413) B15867413
theorem B4696433 : Blo 1391515 4696433 := bstep (se 2 (by rfl) ⟨1761162, by rfl⟩ : syracuseStep 4696433 = 3522325) B3522325
theorem B2754929 : Blo 1391515 2754929 := bstep (se 2 (by rfl) ⟨1033098, by rfl⟩ : syracuseStep 2754929 = 2066197) B2066197
theorem B3525059 : Blo 1391515 3525059 := bstep (se 1 (by rfl) ⟨2643794, by rfl⟩ : syracuseStep 3525059 = 5287589) B5287589
theorem B1567219 : Blo 1391515 1567219 := bstep (se 1 (by rfl) ⟨1175414, by rfl⟩ : syracuseStep 1567219 = 2350829) B2350829
theorem B3967537 : Blo 1391515 3967537 := bstep (se 2 (by rfl) ⟨1487826, by rfl⟩ : syracuseStep 3967537 = 2975653) B2975653
theorem B3132017 : Blo 1391515 3132017 := bstep (se 2 (by rfl) ⟨1174506, by rfl⟩ : syracuseStep 3132017 = 2349013) B2349013
theorem B3132035 : Blo 1391515 3132035 := bstep (se 1 (by rfl) ⟨2349026, by rfl⟩ : syracuseStep 3132035 = 4698053) B4698053
theorem B1567363 : Blo 1391515 1567363 := bstep (se 1 (by rfl) ⟨1175522, by rfl⟩ : syracuseStep 1567363 = 2351045) B2351045
theorem B2230945 : Blo 1391515 2230945 := bstep (se 2 (by rfl) ⟨836604, by rfl⟩ : syracuseStep 2230945 = 1673209) B1673209
theorem B2116289 : Blo 1391515 2116289 := bstep (se 2 (by rfl) ⟨793608, by rfl⟩ : syracuseStep 2116289 = 1587217) B1587217
theorem B7932613 : Blo 1391515 7932613 := bstep (se 4 (by rfl) ⟨743682, by rfl⟩ : syracuseStep 7932613 = 1487365) B1487365
theorem B3967697 : Blo 1391515 3967697 := bstep (se 2 (by rfl) ⟨1487886, by rfl⟩ : syracuseStep 3967697 = 2975773) B2975773
theorem B1411811 : Blo 1391515 1411811 := bstep (se 1 (by rfl) ⟨1058858, by rfl⟩ : syracuseStep 1411811 = 2117717) B2117717
theorem B1567507 : Blo 1391515 1567507 := bstep (se 1 (by rfl) ⟨1175630, by rfl⟩ : syracuseStep 1567507 = 2351261) B2351261
theorem B7047971 : Blo 1391515 7047971 := bstep (se 1 (by rfl) ⟨5285978, by rfl⟩ : syracuseStep 7047971 = 10571957) B10571957
theorem B3967811 : Blo 1391515 3967811 := bstep (se 1 (by rfl) ⟨2975858, by rfl⟩ : syracuseStep 3967811 = 5951717) B5951717
theorem B2509699 : Blo 1391515 2509699 := bstep (se 1 (by rfl) ⟨1882274, by rfl⟩ : syracuseStep 2509699 = 3764549) B3764549
theorem B4696973 : Blo 1391515 4696973 := bstep (se 3 (by rfl) ⟨880682, by rfl⟩ : syracuseStep 4696973 = 1761365) B1761365
theorem B3132305 : Blo 1391515 3132305 := bstep (se 2 (by rfl) ⟨1174614, by rfl⟩ : syracuseStep 3132305 = 2349229) B2349229
theorem B3132323 : Blo 1391515 3132323 := bstep (se 1 (by rfl) ⟨2349242, by rfl⟩ : syracuseStep 3132323 = 4698485) B4698485
theorem B1567651 : Blo 1391515 1567651 := bstep (se 1 (by rfl) ⟨1175738, by rfl⟩ : syracuseStep 1567651 = 2351477) B2351477
theorem B4697027 : Blo 1391515 4697027 := bstep (se 1 (by rfl) ⟨3522770, by rfl⟩ : syracuseStep 4697027 = 7045541) B7045541
theorem B3345457 : Blo 1391515 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B8146061 : Blo 1391515 8146061 := bstep (se 3 (by rfl) ⟨1527386, by rfl⟩ : syracuseStep 8146061 = 3054773) B3054773
theorem B3132593 : Blo 1391515 3132593 := bstep (se 2 (by rfl) ⟨1174722, by rfl⟩ : syracuseStep 3132593 = 2349445) B2349445
theorem B3132611 : Blo 1391515 3132611 := bstep (se 1 (by rfl) ⟨2349458, by rfl⟩ : syracuseStep 3132611 = 4698917) B4698917
theorem B4697297 : Blo 1391515 4697297 := bstep (se 2 (by rfl) ⟨1761486, by rfl⟩ : syracuseStep 4697297 = 3522973) B3522973
theorem B5950691 : Blo 1391515 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B4459789 : Blo 1391515 4459789 := bstep (se 3 (by rfl) ⟨836210, by rfl⟩ : syracuseStep 4459789 = 1672421) B1672421
theorem B10718477 : Blo 1391515 10718477 := bstep (se 3 (by rfl) ⟨2009714, by rfl⟩ : syracuseStep 10718477 = 4019429) B4019429
theorem B20065589 : Blo 1391515 20065589 := bstep (se 5 (by rfl) ⟨940574, by rfl⟩ : syracuseStep 20065589 = 1881149) B1881149
theorem B1412419 : Blo 1391515 1412419 := bstep (se 1 (by rfl) ⟨1059314, by rfl⟩ : syracuseStep 1412419 = 2118629) B2118629
theorem B5647715 : Blo 1391515 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B11300195 : Blo 1391515 11300195 := bstep (se 1 (by rfl) ⟨8475146, by rfl⟩ : syracuseStep 11300195 = 16950293) B16950293
theorem B4132205 : Blo 1391515 4132205 := bstep (se 3 (by rfl) ⟨774788, by rfl⟩ : syracuseStep 4132205 = 1549577) B1549577
theorem B3526001 : Blo 1391515 3526001 := bstep (se 2 (by rfl) ⟨1322250, by rfl⟩ : syracuseStep 3526001 = 2644501) B2644501
theorem B8924579 : Blo 1391515 8924579 := bstep (se 1 (by rfl) ⟨6693434, by rfl⟩ : syracuseStep 8924579 = 13386869) B13386869
theorem B3526051 : Blo 1391515 3526051 := bstep (se 1 (by rfl) ⟨2644538, by rfl⟩ : syracuseStep 3526051 = 5289077) B5289077
theorem B9530821 : Blo 1391515 9530821 := bstep (se 4 (by rfl) ⟨893514, by rfl⟩ : syracuseStep 9530821 = 1787029) B1787029
theorem B3132881 : Blo 1391515 3132881 := bstep (se 2 (by rfl) ⟨1174830, by rfl⟩ : syracuseStep 3132881 = 2349661) B2349661
theorem B3132899 : Blo 1391515 3132899 := bstep (se 1 (by rfl) ⟨2349674, by rfl⟩ : syracuseStep 3132899 = 4699349) B4699349
theorem B3526193 : Blo 1391515 3526193 := bstep (se 2 (by rfl) ⟨1322322, by rfl⟩ : syracuseStep 3526193 = 2644645) B2644645
theorem B7048781 : Blo 1391515 7048781 := bstep (se 3 (by rfl) ⟨1321646, by rfl⟩ : syracuseStep 7048781 = 2643293) B2643293
theorem B4763249 : Blo 1391515 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B2117267 : Blo 1391515 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B4697837 : Blo 1391515 4697837 := bstep (se 3 (by rfl) ⟨880844, by rfl⟩ : syracuseStep 4697837 = 1761689) B1761689
theorem B3133169 : Blo 1391515 3133169 := bstep (se 2 (by rfl) ⟨1174938, by rfl⟩ : syracuseStep 3133169 = 2349877) B2349877
theorem B3133187 : Blo 1391515 3133187 := bstep (se 1 (by rfl) ⟨2349890, by rfl⟩ : syracuseStep 3133187 = 4699781) B4699781
theorem B4697891 : Blo 1391515 4697891 := bstep (se 1 (by rfl) ⟨3523418, by rfl⟩ : syracuseStep 4697891 = 7046837) B7046837
theorem B3133457 : Blo 1391515 3133457 := bstep (se 2 (by rfl) ⟨1175046, by rfl⟩ : syracuseStep 3133457 = 2350093) B2350093
theorem B1486883 : Blo 1391515 1486883 := bstep (se 1 (by rfl) ⟨1115162, by rfl⟩ : syracuseStep 1486883 = 2230325) B2230325
theorem B3133475 : Blo 1391515 3133475 := bstep (se 1 (by rfl) ⟨2350106, by rfl⟩ : syracuseStep 3133475 = 4700213) B4700213
theorem B4698161 : Blo 1391515 4698161 := bstep (se 2 (by rfl) ⟨1761810, by rfl⟩ : syracuseStep 4698161 = 3523621) B3523621
theorem B2641987 : Blo 1391515 2641987 := bstep (se 1 (by rfl) ⟨1981490, by rfl⟩ : syracuseStep 2641987 = 3962981) B3962981
theorem B3764333 : Blo 1391515 3764333 := bstep (se 3 (by rfl) ⟨705812, by rfl⟩ : syracuseStep 3764333 = 1411625) B1411625
theorem B2642033 : Blo 1391515 2642033 := bstep (se 2 (by rfl) ⟨990762, by rfl⟩ : syracuseStep 2642033 = 1981525) B1981525
theorem B8917219 : Blo 1391515 8917219 := bstep (se 1 (by rfl) ⟨6687914, by rfl⟩ : syracuseStep 8917219 = 13375829) B13375829
theorem B3133745 : Blo 1391515 3133745 := bstep (se 2 (by rfl) ⟨1175154, by rfl⟩ : syracuseStep 3133745 = 2350309) B2350309
theorem B3133763 : Blo 1391515 3133763 := bstep (se 1 (by rfl) ⟨2350322, by rfl⟩ : syracuseStep 3133763 = 4700645) B4700645
theorem B6787405 : Blo 1391515 6787405 := bstep (se 3 (by rfl) ⟨1272638, by rfl⟩ : syracuseStep 6787405 = 2545277) B2545277
theorem B17396081 : Blo 1391515 17396081 := bstep (se 2 (by rfl) ⟨6523530, by rfl⟩ : syracuseStep 17396081 = 13047061) B13047061
theorem B2642321 : Blo 1391515 2642321 := bstep (se 2 (by rfl) ⟨990870, by rfl⟩ : syracuseStep 2642321 = 1981741) B1981741
theorem B3764657 : Blo 1391515 3764657 := bstep (se 2 (by rfl) ⟨1411746, by rfl⟩ : syracuseStep 3764657 = 2823493) B2823493
theorem B3527185 : Blo 1391515 3527185 := bstep (se 2 (by rfl) ⟨1322694, by rfl⟩ : syracuseStep 3527185 = 2645389) B2645389
theorem B4698701 : Blo 1391515 4698701 := bstep (se 3 (by rfl) ⟨881006, by rfl⟩ : syracuseStep 4698701 = 1762013) B1762013
theorem B3134033 : Blo 1391515 3134033 := bstep (se 2 (by rfl) ⟨1175262, by rfl⟩ : syracuseStep 3134033 = 2350525) B2350525
theorem B3134051 : Blo 1391515 3134051 := bstep (se 1 (by rfl) ⟨2350538, by rfl⟩ : syracuseStep 3134051 = 4701077) B4701077
theorem B5288561 : Blo 1391515 5288561 := bstep (se 2 (by rfl) ⟨1983210, by rfl⟩ : syracuseStep 5288561 = 3966421) B3966421
theorem B4698755 : Blo 1391515 4698755 := bstep (se 1 (by rfl) ⟨3524066, by rfl⟩ : syracuseStep 4698755 = 7048133) B7048133
theorem B7934597 : Blo 1391515 7934597 := bstep (se 4 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 7934597 = 1487737) B1487737
theorem B10039949 : Blo 1391515 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B2822819 : Blo 1391515 2822819 := bstep (se 1 (by rfl) ⟨2117114, by rfl⟩ : syracuseStep 2822819 = 4234229) B4234229
theorem B3134321 : Blo 1391515 3134321 := bstep (se 2 (by rfl) ⟨1175370, by rfl⟩ : syracuseStep 3134321 = 2350741) B2350741
theorem B3134339 : Blo 1391515 3134339 := bstep (se 1 (by rfl) ⟨2350754, by rfl⟩ : syracuseStep 3134339 = 4701509) B4701509
theorem B4699025 : Blo 1391515 4699025 := bstep (se 2 (by rfl) ⟨1762134, by rfl⟩ : syracuseStep 4699025 = 3524269) B3524269
theorem B4461571 : Blo 1391515 4461571 := bstep (se 1 (by rfl) ⟨3346178, by rfl⟩ : syracuseStep 4461571 = 6692357) B6692357
theorem B2479153 : Blo 1391515 2479153 := bstep (se 2 (by rfl) ⟨929682, by rfl⟩ : syracuseStep 2479153 = 1859365) B1859365
theorem B4461635 : Blo 1391515 4461635 := bstep (se 1 (by rfl) ⟨3346226, by rfl⟩ : syracuseStep 4461635 = 6692453) B6692453
theorem B2643043 : Blo 1391515 2643043 := bstep (se 1 (by rfl) ⟨1982282, by rfl⟩ : syracuseStep 2643043 = 3964565) B3964565
theorem B4289645 : Blo 1391515 4289645 := bstep (se 3 (by rfl) ⟨804308, by rfl⟩ : syracuseStep 4289645 = 1608617) B1608617
theorem B4461713 : Blo 1391515 4461713 := bstep (se 2 (by rfl) ⟨1673142, by rfl⟩ : syracuseStep 4461713 = 3346285) B3346285
theorem B3134609 : Blo 1391515 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B4764835 : Blo 1391515 4764835 := bstep (se 1 (by rfl) ⟨3573626, by rfl⟩ : syracuseStep 4764835 = 7147253) B7147253
theorem B3134627 : Blo 1391515 3134627 := bstep (se 1 (by rfl) ⟨2350970, by rfl⟩ : syracuseStep 3134627 = 4701941) B4701941
theorem B24450245 : Blo 1391515 24450245 := bstep (se 4 (by rfl) ⟨2292210, by rfl⟩ : syracuseStep 24450245 = 4584421) B4584421
theorem B8918221 : Blo 1391515 8918221 := bstep (se 3 (by rfl) ⟨1672166, by rfl⟩ : syracuseStep 8918221 = 3344333) B3344333
theorem B2348257 : Blo 1391515 2348257 := bstep (se 2 (by rfl) ⟨880596, by rfl⟩ : syracuseStep 2348257 = 1761193) B1761193
theorem B2348291 : Blo 1391515 2348291 := bstep (se 1 (by rfl) ⟨1761218, by rfl⟩ : syracuseStep 2348291 = 3522437) B3522437
theorem B2348419 : Blo 1391515 2348419 := bstep (se 1 (by rfl) ⟨1761314, by rfl⟩ : syracuseStep 2348419 = 3522629) B3522629
theorem B4699565 : Blo 1391515 4699565 := bstep (se 3 (by rfl) ⟨881168, by rfl⟩ : syracuseStep 4699565 = 1762337) B1762337
theorem B3134897 : Blo 1391515 3134897 := bstep (se 2 (by rfl) ⟨1175586, by rfl⟩ : syracuseStep 3134897 = 2351173) B2351173
theorem B3134915 : Blo 1391515 3134915 := bstep (se 1 (by rfl) ⟨2351186, by rfl⟩ : syracuseStep 3134915 = 4702373) B4702373
theorem B11900357 : Blo 1391515 11900357 := bstep (se 4 (by rfl) ⟨1115658, by rfl⟩ : syracuseStep 11900357 = 2231317) B2231317
theorem B4699619 : Blo 1391515 4699619 := bstep (se 1 (by rfl) ⟨3524714, by rfl⟩ : syracuseStep 4699619 = 7049429) B7049429
theorem B2348561 : Blo 1391515 2348561 := bstep (se 2 (by rfl) ⟨880710, by rfl⟩ : syracuseStep 2348561 = 1761421) B1761421
theorem B2643491 : Blo 1391515 2643491 := bstep (se 1 (by rfl) ⟨1982618, by rfl⟩ : syracuseStep 2643491 = 3965237) B3965237
theorem B2348689 : Blo 1391515 2348689 := bstep (se 2 (by rfl) ⟨880758, by rfl⟩ : syracuseStep 2348689 = 1761517) B1761517
theorem B2348723 : Blo 1391515 2348723 := bstep (se 1 (by rfl) ⟨1761542, by rfl⟩ : syracuseStep 2348723 = 3523085) B3523085
theorem B3135185 : Blo 1391515 3135185 := bstep (se 2 (by rfl) ⟨1175694, by rfl⟩ : syracuseStep 3135185 = 2351389) B2351389
theorem B3135203 : Blo 1391515 3135203 := bstep (se 1 (by rfl) ⟨2351402, by rfl⟩ : syracuseStep 3135203 = 4702805) B4702805
theorem B4699889 : Blo 1391515 4699889 := bstep (se 2 (by rfl) ⟨1762458, by rfl⟩ : syracuseStep 4699889 = 3524917) B3524917
theorem B2348851 : Blo 1391515 2348851 := bstep (se 1 (by rfl) ⟨1761638, by rfl⟩ : syracuseStep 2348851 = 3523277) B3523277
theorem B2643779 : Blo 1391515 2643779 := bstep (se 1 (by rfl) ⟨1982834, by rfl⟩ : syracuseStep 2643779 = 3965669) B3965669
theorem B4233073 : Blo 1391515 4233073 := bstep (se 2 (by rfl) ⟨1587402, by rfl⟩ : syracuseStep 4233073 = 3174805) B3174805
theorem B16078733 : Blo 1391515 16078733 := bstep (se 3 (by rfl) ⟨3014762, by rfl⟩ : syracuseStep 16078733 = 6029525) B6029525
theorem B2348993 : Blo 1391515 2348993 := bstep (se 2 (by rfl) ⟨880872, by rfl⟩ : syracuseStep 2348993 = 1761745) B1761745
theorem B5290019 : Blo 1391515 5290019 := bstep (se 1 (by rfl) ⟨3967514, by rfl⟩ : syracuseStep 5290019 = 7935029) B7935029
theorem B2349121 : Blo 1391515 2349121 := bstep (se 2 (by rfl) ⟨880920, by rfl⟩ : syracuseStep 2349121 = 1761841) B1761841
theorem B2349155 : Blo 1391515 2349155 := bstep (se 1 (by rfl) ⟨1761866, by rfl⟩ : syracuseStep 2349155 = 3523733) B3523733
theorem B15865955 : Blo 1391515 15865955 := bstep (se 1 (by rfl) ⟨11899466, by rfl⟩ : syracuseStep 15865955 = 23798933) B23798933
theorem B13375601 : Blo 1391515 13375601 := bstep (se 2 (by rfl) ⟨5015850, by rfl⟩ : syracuseStep 13375601 = 10031701) B10031701
theorem B3217553 : Blo 1391515 3217553 := bstep (se 2 (by rfl) ⟨1206582, by rfl⟩ : syracuseStep 3217553 = 2413165) B2413165
theorem B3963107 : Blo 1391515 3963107 := bstep (se 1 (by rfl) ⟨2972330, by rfl⟩ : syracuseStep 3963107 = 5944661) B5944661
theorem B2349283 : Blo 1391515 2349283 := bstep (se 1 (by rfl) ⟨1761962, by rfl⟩ : syracuseStep 2349283 = 3523925) B3523925
theorem B4700429 : Blo 1391515 4700429 := bstep (se 3 (by rfl) ⟨881330, by rfl⟩ : syracuseStep 4700429 = 1762661) B1762661
theorem B4700483 : Blo 1391515 4700483 := bstep (se 1 (by rfl) ⟨3525362, by rfl⟩ : syracuseStep 4700483 = 7050725) B7050725
theorem B2349425 : Blo 1391515 2349425 := bstep (se 2 (by rfl) ⟨881034, by rfl⟩ : syracuseStep 2349425 = 1762069) B1762069
theorem B2087297 : Blo 1391515 2087297 := bstep (se 2 (by rfl) ⟨782736, by rfl⟩ : syracuseStep 2087297 = 1565473) B1565473
theorem B2087315 : Blo 1391515 2087315 := bstep (se 1 (by rfl) ⟨1565486, by rfl⟩ : syracuseStep 2087315 = 3130973) B3130973
theorem B2087345 : Blo 1391515 2087345 := bstep (se 2 (by rfl) ⟨782754, by rfl⟩ : syracuseStep 2087345 = 1565509) B1565509
theorem B7051697 : Blo 1391515 7051697 := bstep (se 2 (by rfl) ⟨2644386, by rfl⟩ : syracuseStep 7051697 = 5288773) B5288773
theorem B2087363 : Blo 1391515 2087363 := bstep (se 1 (by rfl) ⟨1565522, by rfl⟩ : syracuseStep 2087363 = 3131045) B3131045
theorem B2972099 : Blo 1391515 2972099 := bstep (se 1 (by rfl) ⟨2229074, by rfl⟩ : syracuseStep 2972099 = 4458149) B4458149
theorem B2087393 : Blo 1391515 2087393 := bstep (se 2 (by rfl) ⟨782772, by rfl⟩ : syracuseStep 2087393 = 1565545) B1565545
theorem B2349553 : Blo 1391515 2349553 := bstep (se 2 (by rfl) ⟨881082, by rfl⟩ : syracuseStep 2349553 = 1762165) B1762165
theorem B8927729 : Blo 1391515 8927729 := bstep (se 2 (by rfl) ⟨3347898, by rfl⟩ : syracuseStep 8927729 = 6695797) B6695797
theorem B2087411 : Blo 1391515 2087411 := bstep (se 1 (by rfl) ⟨1565558, by rfl⟩ : syracuseStep 2087411 = 3131117) B3131117
theorem B2087441 : Blo 1391515 2087441 := bstep (se 2 (by rfl) ⟨782790, by rfl⟩ : syracuseStep 2087441 = 1565581) B1565581
theorem B2349587 : Blo 1391515 2349587 := bstep (se 1 (by rfl) ⟨1762190, by rfl⟩ : syracuseStep 2349587 = 3524381) B3524381
theorem B2087459 : Blo 1391515 2087459 := bstep (se 1 (by rfl) ⟨1565594, by rfl⟩ : syracuseStep 2087459 = 3131189) B3131189
theorem B8927779 : Blo 1391515 8927779 := bstep (se 1 (by rfl) ⟨6695834, by rfl⟩ : syracuseStep 8927779 = 13391669) B13391669
theorem B3963437 : Blo 1391515 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B2087489 : Blo 1391515 2087489 := bstep (se 2 (by rfl) ⟨782808, by rfl⟩ : syracuseStep 2087489 = 1565617) B1565617
theorem B4700753 : Blo 1391515 4700753 := bstep (se 2 (by rfl) ⟨1762782, by rfl⟩ : syracuseStep 4700753 = 3525565) B3525565
theorem B2087507 : Blo 1391515 2087507 := bstep (se 1 (by rfl) ⟨1565630, by rfl⟩ : syracuseStep 2087507 = 3131261) B3131261
theorem B2087537 : Blo 1391515 2087537 := bstep (se 2 (by rfl) ⟨782826, by rfl⟩ : syracuseStep 2087537 = 1565653) B1565653
theorem B3963505 : Blo 1391515 3963505 := bstep (se 2 (by rfl) ⟨1486314, by rfl⟩ : syracuseStep 3963505 = 2972629) B2972629
theorem B2087555 : Blo 1391515 2087555 := bstep (se 1 (by rfl) ⟨1565666, by rfl⟩ : syracuseStep 2087555 = 3131333) B3131333
theorem B4291213 : Blo 1391515 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B2349715 : Blo 1391515 2349715 := bstep (se 1 (by rfl) ⟨1762286, by rfl⟩ : syracuseStep 2349715 = 3524573) B3524573
theorem B2087585 : Blo 1391515 2087585 := bstep (se 2 (by rfl) ⟨782844, by rfl⟩ : syracuseStep 2087585 = 1565689) B1565689
theorem B2087603 : Blo 1391515 2087603 := bstep (se 1 (by rfl) ⟨1565702, by rfl⟩ : syracuseStep 2087603 = 3131405) B3131405
theorem B2087633 : Blo 1391515 2087633 := bstep (se 2 (by rfl) ⟨782862, by rfl⟩ : syracuseStep 2087633 = 1565725) B1565725
theorem B2087651 : Blo 1391515 2087651 := bstep (se 1 (by rfl) ⟨1565738, by rfl⟩ : syracuseStep 2087651 = 3131477) B3131477
theorem B2644721 : Blo 1391515 2644721 := bstep (se 2 (by rfl) ⟨991770, by rfl⟩ : syracuseStep 2644721 = 1983541) B1983541
theorem B2087681 : Blo 1391515 2087681 := bstep (se 2 (by rfl) ⟨782880, by rfl⟩ : syracuseStep 2087681 = 1565761) B1565761
theorem B9165581 : Blo 1391515 9165581 := bstep (se 3 (by rfl) ⟨1718546, by rfl⟩ : syracuseStep 9165581 = 3437093) B3437093
theorem B2087699 : Blo 1391515 2087699 := bstep (se 1 (by rfl) ⟨1565774, by rfl⟩ : syracuseStep 2087699 = 3131549) B3131549
theorem B2349857 : Blo 1391515 2349857 := bstep (se 2 (by rfl) ⟨881196, by rfl⟩ : syracuseStep 2349857 = 1762393) B1762393
theorem B2087729 : Blo 1391515 2087729 := bstep (se 2 (by rfl) ⟨782898, by rfl⟩ : syracuseStep 2087729 = 1565797) B1565797
theorem B2087747 : Blo 1391515 2087747 := bstep (se 1 (by rfl) ⟨1565810, by rfl⟩ : syracuseStep 2087747 = 3131621) B3131621
theorem B2825027 : Blo 1391515 2825027 := bstep (se 1 (by rfl) ⟨2118770, by rfl⟩ : syracuseStep 2825027 = 4237541) B4237541
theorem B2087777 : Blo 1391515 2087777 := bstep (se 2 (by rfl) ⟨782916, by rfl⟩ : syracuseStep 2087777 = 1565833) B1565833
theorem B1981297 : Blo 1391515 1981297 := bstep (se 2 (by rfl) ⟨742986, by rfl⟩ : syracuseStep 1981297 = 1485973) B1485973
theorem B2087795 : Blo 1391515 2087795 := bstep (se 1 (by rfl) ⟨1565846, by rfl⟩ : syracuseStep 2087795 = 3131693) B3131693
theorem B3963779 : Blo 1391515 3963779 := bstep (se 1 (by rfl) ⟨2972834, by rfl⟩ : syracuseStep 3963779 = 5945669) B5945669
theorem B2087825 : Blo 1391515 2087825 := bstep (se 2 (by rfl) ⟨782934, by rfl⟩ : syracuseStep 2087825 = 1565869) B1565869
theorem B2349985 : Blo 1391515 2349985 := bstep (se 2 (by rfl) ⟨881244, by rfl⟩ : syracuseStep 2349985 = 1762489) B1762489
theorem B1391523 : Blo 1391515 1391523 := bstep (se 1 (by rfl) ⟨1043642, by rfl⟩ : syracuseStep 1391523 = 2087285) B2087285
theorem B2087843 : Blo 1391515 2087843 := bstep (se 1 (by rfl) ⟨1565882, by rfl⟩ : syracuseStep 2087843 = 3131765) B3131765
theorem B1391539 : Blo 1391515 1391539 := bstep (se 1 (by rfl) ⟨1043654, by rfl⟩ : syracuseStep 1391539 = 2087309) B2087309
theorem B2087873 : Blo 1391515 2087873 := bstep (se 2 (by rfl) ⟨782952, by rfl⟩ : syracuseStep 2087873 = 1565905) B1565905
theorem B1391555 : Blo 1391515 1391555 := bstep (se 1 (by rfl) ⟨1043666, by rfl⟩ : syracuseStep 1391555 = 2087333) B2087333
theorem B2350019 : Blo 1391515 2350019 := bstep (se 1 (by rfl) ⟨1762514, by rfl⟩ : syracuseStep 2350019 = 3525029) B3525029
theorem B5946317 : Blo 1391515 5946317 := bstep (se 3 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 5946317 = 2229869) B2229869
theorem B1391571 : Blo 1391515 1391571 := bstep (se 1 (by rfl) ⟨1043678, by rfl⟩ : syracuseStep 1391571 = 2087357) B2087357
theorem B2087891 : Blo 1391515 2087891 := bstep (se 1 (by rfl) ⟨1565918, by rfl⟩ : syracuseStep 2087891 = 3131837) B3131837
theorem B1391587 : Blo 1391515 1391587 := bstep (se 1 (by rfl) ⟨1043690, by rfl⟩ : syracuseStep 1391587 = 2087381) B2087381
theorem B2087921 : Blo 1391515 2087921 := bstep (se 2 (by rfl) ⟨782970, by rfl⟩ : syracuseStep 2087921 = 1565941) B1565941
theorem B1391603 : Blo 1391515 1391603 := bstep (se 1 (by rfl) ⟨1043702, by rfl⟩ : syracuseStep 1391603 = 2087405) B2087405
theorem B1391619 : Blo 1391515 1391619 := bstep (se 1 (by rfl) ⟨1043714, by rfl⟩ : syracuseStep 1391619 = 2087429) B2087429
theorem B2087939 : Blo 1391515 2087939 := bstep (se 1 (by rfl) ⟨1565954, by rfl⟩ : syracuseStep 2087939 = 3131909) B3131909
theorem B2382851 : Blo 1391515 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B15465485 : Blo 1391515 15465485 := bstep (se 3 (by rfl) ⟨2899778, by rfl⟩ : syracuseStep 15465485 = 5799557) B5799557
theorem B1391635 : Blo 1391515 1391635 := bstep (se 1 (by rfl) ⟨1043726, by rfl⟩ : syracuseStep 1391635 = 2087453) B2087453
theorem B4463633 : Blo 1391515 4463633 := bstep (se 2 (by rfl) ⟨1673862, by rfl⟩ : syracuseStep 4463633 = 3347725) B3347725
theorem B2087969 : Blo 1391515 2087969 := bstep (se 2 (by rfl) ⟨782988, by rfl⟩ : syracuseStep 2087969 = 1565977) B1565977
theorem B1391651 : Blo 1391515 1391651 := bstep (se 1 (by rfl) ⟨1043738, by rfl⟩ : syracuseStep 1391651 = 2087477) B2087477
theorem B1391667 : Blo 1391515 1391667 := bstep (se 1 (by rfl) ⟨1043750, by rfl⟩ : syracuseStep 1391667 = 2087501) B2087501
theorem B2087987 : Blo 1391515 2087987 := bstep (se 1 (by rfl) ⟨1565990, by rfl⟩ : syracuseStep 2087987 = 3131981) B3131981
theorem B1391683 : Blo 1391515 1391683 := bstep (se 1 (by rfl) ⟨1043762, by rfl⟩ : syracuseStep 1391683 = 2087525) B2087525
theorem B2350147 : Blo 1391515 2350147 := bstep (se 1 (by rfl) ⟨1762610, by rfl⟩ : syracuseStep 2350147 = 3525221) B3525221
theorem B5356621 : Blo 1391515 5356621 := bstep (se 3 (by rfl) ⟨1004366, by rfl⟩ : syracuseStep 5356621 = 2008733) B2008733
theorem B2088017 : Blo 1391515 2088017 := bstep (se 2 (by rfl) ⟨783006, by rfl⟩ : syracuseStep 2088017 = 1566013) B1566013
theorem B1391699 : Blo 1391515 1391699 := bstep (se 1 (by rfl) ⟨1043774, by rfl⟩ : syracuseStep 1391699 = 2087549) B2087549
theorem B1391715 : Blo 1391515 1391715 := bstep (se 1 (by rfl) ⟨1043786, by rfl⟩ : syracuseStep 1391715 = 2087573) B2087573
theorem B2088035 : Blo 1391515 2088035 := bstep (se 1 (by rfl) ⟨1566026, by rfl⟩ : syracuseStep 2088035 = 3132053) B3132053
theorem B3177571 : Blo 1391515 3177571 := bstep (se 1 (by rfl) ⟨2383178, by rfl⟩ : syracuseStep 3177571 = 4766357) B4766357
theorem B4701293 : Blo 1391515 4701293 := bstep (se 3 (by rfl) ⟨881492, by rfl⟩ : syracuseStep 4701293 = 1762985) B1762985
theorem B1391731 : Blo 1391515 1391731 := bstep (se 1 (by rfl) ⟨1043798, by rfl⟩ : syracuseStep 1391731 = 2087597) B2087597
theorem B9526385 : Blo 1391515 9526385 := bstep (se 2 (by rfl) ⟨3572394, by rfl⟩ : syracuseStep 9526385 = 7144789) B7144789
theorem B2088065 : Blo 1391515 2088065 := bstep (se 2 (by rfl) ⟨783024, by rfl⟩ : syracuseStep 2088065 = 1566049) B1566049
theorem B1391747 : Blo 1391515 1391747 := bstep (se 1 (by rfl) ⟨1043810, by rfl⟩ : syracuseStep 1391747 = 2087621) B2087621
theorem B1391763 : Blo 1391515 1391763 := bstep (se 1 (by rfl) ⟨1043822, by rfl⟩ : syracuseStep 1391763 = 2087645) B2087645
theorem B2088083 : Blo 1391515 2088083 := bstep (se 1 (by rfl) ⟨1566062, by rfl⟩ : syracuseStep 2088083 = 3132125) B3132125
theorem B1391779 : Blo 1391515 1391779 := bstep (se 1 (by rfl) ⟨1043834, by rfl⟩ : syracuseStep 1391779 = 2087669) B2087669
theorem B4701347 : Blo 1391515 4701347 := bstep (se 1 (by rfl) ⟨3526010, by rfl⟩ : syracuseStep 4701347 = 7052021) B7052021
theorem B2088113 : Blo 1391515 2088113 := bstep (se 2 (by rfl) ⟨783042, by rfl⟩ : syracuseStep 2088113 = 1566085) B1566085
theorem B1391795 : Blo 1391515 1391795 := bstep (se 1 (by rfl) ⟨1043846, by rfl⟩ : syracuseStep 1391795 = 2087693) B2087693
theorem B1391811 : Blo 1391515 1391811 := bstep (se 1 (by rfl) ⟨1043858, by rfl⟩ : syracuseStep 1391811 = 2087717) B2087717
theorem B2088131 : Blo 1391515 2088131 := bstep (se 1 (by rfl) ⟨1566098, by rfl⟩ : syracuseStep 2088131 = 3132197) B3132197
theorem B2350289 : Blo 1391515 2350289 := bstep (se 2 (by rfl) ⟨881358, by rfl⟩ : syracuseStep 2350289 = 1762717) B1762717
theorem B1391827 : Blo 1391515 1391827 := bstep (se 1 (by rfl) ⟨1043870, by rfl⟩ : syracuseStep 1391827 = 2087741) B2087741
theorem B2088161 : Blo 1391515 2088161 := bstep (se 2 (by rfl) ⟨783060, by rfl⟩ : syracuseStep 2088161 = 1566121) B1566121
theorem B1391843 : Blo 1391515 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B1391859 : Blo 1391515 1391859 := bstep (se 1 (by rfl) ⟨1043894, by rfl⟩ : syracuseStep 1391859 = 2087789) B2087789
theorem B2088179 : Blo 1391515 2088179 := bstep (se 1 (by rfl) ⟨1566134, by rfl⟩ : syracuseStep 2088179 = 3132269) B3132269
theorem B1391875 : Blo 1391515 1391875 := bstep (se 1 (by rfl) ⟨1043906, by rfl⟩ : syracuseStep 1391875 = 2087813) B2087813
theorem B2088209 : Blo 1391515 2088209 := bstep (se 2 (by rfl) ⟨783078, by rfl⟩ : syracuseStep 2088209 = 1566157) B1566157
theorem B1391891 : Blo 1391515 1391891 := bstep (se 1 (by rfl) ⟨1043918, by rfl⟩ : syracuseStep 1391891 = 2087837) B2087837
theorem B1391907 : Blo 1391515 1391907 := bstep (se 1 (by rfl) ⟨1043930, by rfl⟩ : syracuseStep 1391907 = 2087861) B2087861
theorem B2088227 : Blo 1391515 2088227 := bstep (se 1 (by rfl) ⟨1566170, by rfl⟩ : syracuseStep 2088227 = 3132341) B3132341
theorem B5946659 : Blo 1391515 5946659 := bstep (se 1 (by rfl) ⟨4459994, by rfl⟩ : syracuseStep 5946659 = 8919989) B8919989
theorem B1391923 : Blo 1391515 1391923 := bstep (se 1 (by rfl) ⟨1043942, by rfl⟩ : syracuseStep 1391923 = 2087885) B2087885
theorem B2088257 : Blo 1391515 2088257 := bstep (se 2 (by rfl) ⟨783096, by rfl⟩ : syracuseStep 2088257 = 1566193) B1566193
theorem B1391939 : Blo 1391515 1391939 := bstep (se 1 (by rfl) ⟨1043954, by rfl⟩ : syracuseStep 1391939 = 2087909) B2087909
theorem B2350417 : Blo 1391515 2350417 := bstep (se 2 (by rfl) ⟨881406, by rfl⟩ : syracuseStep 2350417 = 1762813) B1762813
theorem B1391955 : Blo 1391515 1391955 := bstep (se 1 (by rfl) ⟨1043966, by rfl⟩ : syracuseStep 1391955 = 2087933) B2087933
theorem B2088275 : Blo 1391515 2088275 := bstep (se 1 (by rfl) ⟨1566206, by rfl⟩ : syracuseStep 2088275 = 3132413) B3132413
theorem B1391971 : Blo 1391515 1391971 := bstep (se 1 (by rfl) ⟨1043978, by rfl⟩ : syracuseStep 1391971 = 2087957) B2087957
theorem B2088305 : Blo 1391515 2088305 := bstep (se 2 (by rfl) ⟨783114, by rfl⟩ : syracuseStep 2088305 = 1566229) B1566229
theorem B1391987 : Blo 1391515 1391987 := bstep (se 1 (by rfl) ⟨1043990, by rfl⟩ : syracuseStep 1391987 = 2087981) B2087981
theorem B2350451 : Blo 1391515 2350451 := bstep (se 1 (by rfl) ⟨1762838, by rfl⟩ : syracuseStep 2350451 = 3525677) B3525677
theorem B1392003 : Blo 1391515 1392003 := bstep (se 1 (by rfl) ⟨1044002, by rfl⟩ : syracuseStep 1392003 = 2088005) B2088005
theorem B2088323 : Blo 1391515 2088323 := bstep (se 1 (by rfl) ⟨1566242, by rfl⟩ : syracuseStep 2088323 = 3132485) B3132485
theorem B1392019 : Blo 1391515 1392019 := bstep (se 1 (by rfl) ⟨1044014, by rfl⟩ : syracuseStep 1392019 = 2088029) B2088029
theorem B2088353 : Blo 1391515 2088353 := bstep (se 2 (by rfl) ⟨783132, by rfl⟩ : syracuseStep 2088353 = 1566265) B1566265
theorem B1392035 : Blo 1391515 1392035 := bstep (se 1 (by rfl) ⟨1044026, by rfl⟩ : syracuseStep 1392035 = 2088053) B2088053
theorem B4701617 : Blo 1391515 4701617 := bstep (se 2 (by rfl) ⟨1763106, by rfl⟩ : syracuseStep 4701617 = 3526213) B3526213
theorem B1392051 : Blo 1391515 1392051 := bstep (se 1 (by rfl) ⟨1044038, by rfl⟩ : syracuseStep 1392051 = 2088077) B2088077
theorem B2088371 : Blo 1391515 2088371 := bstep (se 1 (by rfl) ⟨1566278, by rfl⟩ : syracuseStep 2088371 = 3132557) B3132557
theorem B1392067 : Blo 1391515 1392067 := bstep (se 1 (by rfl) ⟨1044050, by rfl⟩ : syracuseStep 1392067 = 2088101) B2088101
theorem B2088401 : Blo 1391515 2088401 := bstep (se 2 (by rfl) ⟨783150, by rfl⟩ : syracuseStep 2088401 = 1566301) B1566301
theorem B1392083 : Blo 1391515 1392083 := bstep (se 1 (by rfl) ⟨1044062, by rfl⟩ : syracuseStep 1392083 = 2088125) B2088125
theorem B1392099 : Blo 1391515 1392099 := bstep (se 1 (by rfl) ⟨1044074, by rfl⟩ : syracuseStep 1392099 = 2088149) B2088149
theorem B2088419 : Blo 1391515 2088419 := bstep (se 1 (by rfl) ⟨1566314, by rfl⟩ : syracuseStep 2088419 = 3132629) B3132629
theorem B1392115 : Blo 1391515 1392115 := bstep (se 1 (by rfl) ⟨1044086, by rfl⟩ : syracuseStep 1392115 = 2088173) B2088173
theorem B2350579 : Blo 1391515 2350579 := bstep (se 1 (by rfl) ⟨1762934, by rfl⟩ : syracuseStep 2350579 = 3525869) B3525869
theorem B2088449 : Blo 1391515 2088449 := bstep (se 2 (by rfl) ⟨783168, by rfl⟩ : syracuseStep 2088449 = 1566337) B1566337
theorem B1392131 : Blo 1391515 1392131 := bstep (se 1 (by rfl) ⟨1044098, by rfl⟩ : syracuseStep 1392131 = 2088197) B2088197
theorem B1392147 : Blo 1391515 1392147 := bstep (se 1 (by rfl) ⟨1044110, by rfl⟩ : syracuseStep 1392147 = 2088221) B2088221
theorem B2088467 : Blo 1391515 2088467 := bstep (se 1 (by rfl) ⟨1566350, by rfl⟩ : syracuseStep 2088467 = 3132701) B3132701
theorem B1392163 : Blo 1391515 1392163 := bstep (se 1 (by rfl) ⟨1044122, by rfl⟩ : syracuseStep 1392163 = 2088245) B2088245
theorem B4464173 : Blo 1391515 4464173 := bstep (se 3 (by rfl) ⟨837032, by rfl⟩ : syracuseStep 4464173 = 1674065) B1674065
theorem B2088497 : Blo 1391515 2088497 := bstep (se 2 (by rfl) ⟨783186, by rfl⟩ : syracuseStep 2088497 = 1566373) B1566373
theorem B4521521 : Blo 1391515 4521521 := bstep (se 2 (by rfl) ⟨1695570, by rfl⟩ : syracuseStep 4521521 = 3391141) B3391141
theorem B1392179 : Blo 1391515 1392179 := bstep (se 1 (by rfl) ⟨1044134, by rfl⟩ : syracuseStep 1392179 = 2088269) B2088269
theorem B117407285 : Blo 1391515 117407285 := bstep (se 5 (by rfl) ⟨5503466, by rfl⟩ : syracuseStep 117407285 = 11006933) B11006933
theorem B1392195 : Blo 1391515 1392195 := bstep (se 1 (by rfl) ⟨1044146, by rfl⟩ : syracuseStep 1392195 = 2088293) B2088293
theorem B2088515 : Blo 1391515 2088515 := bstep (se 1 (by rfl) ⟨1566386, by rfl⟩ : syracuseStep 2088515 = 3132773) B3132773
theorem B1392211 : Blo 1391515 1392211 := bstep (se 1 (by rfl) ⟨1044158, by rfl⟩ : syracuseStep 1392211 = 2088317) B2088317
theorem B2088545 : Blo 1391515 2088545 := bstep (se 2 (by rfl) ⟨783204, by rfl⟩ : syracuseStep 2088545 = 1566409) B1566409
theorem B5283427 : Blo 1391515 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B1392227 : Blo 1391515 1392227 := bstep (se 1 (by rfl) ⟨1044170, by rfl⟩ : syracuseStep 1392227 = 2088341) B2088341
theorem B1392243 : Blo 1391515 1392243 := bstep (se 1 (by rfl) ⟨1044182, by rfl⟩ : syracuseStep 1392243 = 2088365) B2088365
theorem B2088563 : Blo 1391515 2088563 := bstep (se 1 (by rfl) ⟨1566422, by rfl⟩ : syracuseStep 2088563 = 3132845) B3132845
theorem B2350721 : Blo 1391515 2350721 := bstep (se 2 (by rfl) ⟨881520, by rfl⟩ : syracuseStep 2350721 = 1763041) B1763041
theorem B1982083 : Blo 1391515 1982083 := bstep (se 1 (by rfl) ⟨1486562, by rfl⟩ : syracuseStep 1982083 = 2973125) B2973125
theorem B1392259 : Blo 1391515 1392259 := bstep (se 1 (by rfl) ⟨1044194, by rfl⟩ : syracuseStep 1392259 = 2088389) B2088389
theorem B2088593 : Blo 1391515 2088593 := bstep (se 2 (by rfl) ⟨783222, by rfl⟩ : syracuseStep 2088593 = 1566445) B1566445
theorem B1392275 : Blo 1391515 1392275 := bstep (se 1 (by rfl) ⟨1044206, by rfl⟩ : syracuseStep 1392275 = 2088413) B2088413
theorem B1392291 : Blo 1391515 1392291 := bstep (se 1 (by rfl) ⟨1044218, by rfl⟩ : syracuseStep 1392291 = 2088437) B2088437
theorem B2088611 : Blo 1391515 2088611 := bstep (se 1 (by rfl) ⟨1566458, by rfl⟩ : syracuseStep 2088611 = 3132917) B3132917
theorem B1392307 : Blo 1391515 1392307 := bstep (se 1 (by rfl) ⟨1044230, by rfl⟩ : syracuseStep 1392307 = 2088461) B2088461
theorem B2088641 : Blo 1391515 2088641 := bstep (se 2 (by rfl) ⟨783240, by rfl⟩ : syracuseStep 2088641 = 1566481) B1566481
theorem B1392323 : Blo 1391515 1392323 := bstep (se 1 (by rfl) ⟨1044242, by rfl⟩ : syracuseStep 1392323 = 2088485) B2088485
theorem B3964621 : Blo 1391515 3964621 := bstep (se 3 (by rfl) ⟨743366, by rfl⟩ : syracuseStep 3964621 = 1486733) B1486733
theorem B1392339 : Blo 1391515 1392339 := bstep (se 1 (by rfl) ⟨1044254, by rfl⟩ : syracuseStep 1392339 = 2088509) B2088509
theorem B2088659 : Blo 1391515 2088659 := bstep (se 1 (by rfl) ⟨1566494, by rfl⟩ : syracuseStep 2088659 = 3132989) B3132989
theorem B3522275 : Blo 1391515 3522275 := bstep (se 1 (by rfl) ⟨2641706, by rfl⟩ : syracuseStep 3522275 = 5283413) B5283413
theorem B1392355 : Blo 1391515 1392355 := bstep (se 1 (by rfl) ⟨1044266, by rfl⟩ : syracuseStep 1392355 = 2088533) B2088533
theorem B5947121 : Blo 1391515 5947121 := bstep (se 2 (by rfl) ⟨2230170, by rfl⟩ : syracuseStep 5947121 = 4460341) B4460341
theorem B2088689 : Blo 1391515 2088689 := bstep (se 2 (by rfl) ⟨783258, by rfl⟩ : syracuseStep 2088689 = 1566517) B1566517
theorem B1392371 : Blo 1391515 1392371 := bstep (se 1 (by rfl) ⟨1044278, by rfl⟩ : syracuseStep 1392371 = 2088557) B2088557
theorem B2350849 : Blo 1391515 2350849 := bstep (se 2 (by rfl) ⟨881568, by rfl⟩ : syracuseStep 2350849 = 1763137) B1763137
theorem B1392387 : Blo 1391515 1392387 := bstep (se 1 (by rfl) ⟨1044290, by rfl⟩ : syracuseStep 1392387 = 2088581) B2088581
theorem B2088707 : Blo 1391515 2088707 := bstep (se 1 (by rfl) ⟨1566530, by rfl⟩ : syracuseStep 2088707 = 3133061) B3133061
theorem B10043149 : Blo 1391515 10043149 := bstep (se 3 (by rfl) ⟨1883090, by rfl⟩ : syracuseStep 10043149 = 3766181) B3766181
theorem B1392403 : Blo 1391515 1392403 := bstep (se 1 (by rfl) ⟨1044302, by rfl⟩ : syracuseStep 1392403 = 2088605) B2088605
theorem B2088737 : Blo 1391515 2088737 := bstep (se 2 (by rfl) ⟨783276, by rfl⟩ : syracuseStep 2088737 = 1566553) B1566553
theorem B1392419 : Blo 1391515 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B2350883 : Blo 1391515 2350883 := bstep (se 1 (by rfl) ⟨1763162, by rfl⟩ : syracuseStep 2350883 = 3526325) B3526325
theorem B1392435 : Blo 1391515 1392435 := bstep (se 1 (by rfl) ⟨1044326, by rfl⟩ : syracuseStep 1392435 = 2088653) B2088653
theorem B2088755 : Blo 1391515 2088755 := bstep (se 1 (by rfl) ⟨1566566, by rfl⟩ : syracuseStep 2088755 = 3133133) B3133133
theorem B1392451 : Blo 1391515 1392451 := bstep (se 1 (by rfl) ⟨1044338, by rfl⟩ : syracuseStep 1392451 = 2088677) B2088677
theorem B5087053 : Blo 1391515 5087053 := bstep (se 3 (by rfl) ⟨953822, by rfl⟩ : syracuseStep 5087053 = 1907645) B1907645
theorem B2088785 : Blo 1391515 2088785 := bstep (se 2 (by rfl) ⟨783294, by rfl⟩ : syracuseStep 2088785 = 1566589) B1566589
theorem B1392467 : Blo 1391515 1392467 := bstep (se 1 (by rfl) ⟨1044350, by rfl⟩ : syracuseStep 1392467 = 2088701) B2088701
theorem B1392483 : Blo 1391515 1392483 := bstep (se 1 (by rfl) ⟨1044362, by rfl⟩ : syracuseStep 1392483 = 2088725) B2088725
theorem B2088803 : Blo 1391515 2088803 := bstep (se 1 (by rfl) ⟨1566602, by rfl⟩ : syracuseStep 2088803 = 3133205) B3133205
theorem B7053155 : Blo 1391515 7053155 := bstep (se 1 (by rfl) ⟨5289866, by rfl⟩ : syracuseStep 7053155 = 10579733) B10579733
theorem B3964781 : Blo 1391515 3964781 := bstep (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) B1486793
theorem B1392499 : Blo 1391515 1392499 := bstep (se 1 (by rfl) ⟨1044374, by rfl⟩ : syracuseStep 1392499 = 2088749) B2088749
theorem B2088833 : Blo 1391515 2088833 := bstep (se 2 (by rfl) ⟨783312, by rfl⟩ : syracuseStep 2088833 = 1566625) B1566625
theorem B1392515 : Blo 1391515 1392515 := bstep (se 1 (by rfl) ⟨1044386, by rfl⟩ : syracuseStep 1392515 = 2088773) B2088773
theorem B1392531 : Blo 1391515 1392531 := bstep (se 1 (by rfl) ⟨1044398, by rfl⟩ : syracuseStep 1392531 = 2088797) B2088797
theorem B2088851 : Blo 1391515 2088851 := bstep (se 1 (by rfl) ⟨1566638, by rfl⟩ : syracuseStep 2088851 = 3133277) B3133277
theorem B3522467 : Blo 1391515 3522467 := bstep (se 1 (by rfl) ⟨2641850, by rfl⟩ : syracuseStep 3522467 = 5283701) B5283701
theorem B1392547 : Blo 1391515 1392547 := bstep (se 1 (by rfl) ⟨1044410, by rfl⟩ : syracuseStep 1392547 = 2088821) B2088821
theorem B2351011 : Blo 1391515 2351011 := bstep (se 1 (by rfl) ⟨1763258, by rfl⟩ : syracuseStep 2351011 = 3526517) B3526517
theorem B2088881 : Blo 1391515 2088881 := bstep (se 2 (by rfl) ⟨783330, by rfl⟩ : syracuseStep 2088881 = 1566661) B1566661
theorem B1761203 : Blo 1391515 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B1392563 : Blo 1391515 1392563 := bstep (se 1 (by rfl) ⟨1044422, by rfl⟩ : syracuseStep 1392563 = 2088845) B2088845
theorem B1392579 : Blo 1391515 1392579 := bstep (se 1 (by rfl) ⟨1044434, by rfl⟩ : syracuseStep 1392579 = 2088869) B2088869
theorem B2088899 : Blo 1391515 2088899 := bstep (se 1 (by rfl) ⟨1566674, by rfl⟩ : syracuseStep 2088899 = 3133349) B3133349
theorem B4235203 : Blo 1391515 4235203 := bstep (se 1 (by rfl) ⟨3176402, by rfl⟩ : syracuseStep 4235203 = 6352805) B6352805
theorem B4702157 : Blo 1391515 4702157 := bstep (se 3 (by rfl) ⟨881654, by rfl⟩ : syracuseStep 4702157 = 1763309) B1763309
theorem B1392595 : Blo 1391515 1392595 := bstep (se 1 (by rfl) ⟨1044446, by rfl⟩ : syracuseStep 1392595 = 2088893) B2088893
theorem B2088929 : Blo 1391515 2088929 := bstep (se 2 (by rfl) ⟨783348, by rfl⟩ : syracuseStep 2088929 = 1566697) B1566697
theorem B1392611 : Blo 1391515 1392611 := bstep (se 1 (by rfl) ⟨1044458, by rfl⟩ : syracuseStep 1392611 = 2088917) B2088917
theorem B7626737 : Blo 1391515 7626737 := bstep (se 2 (by rfl) ⟨2860026, by rfl⟩ : syracuseStep 7626737 = 5720053) B5720053
theorem B1392627 : Blo 1391515 1392627 := bstep (se 1 (by rfl) ⟨1044470, by rfl⟩ : syracuseStep 1392627 = 2088941) B2088941
theorem B2088947 : Blo 1391515 2088947 := bstep (se 1 (by rfl) ⟨1566710, by rfl⟩ : syracuseStep 2088947 = 3133421) B3133421
theorem B2088971 : Blo 1391515 2088971 := bstep (se 1 (by rfl) ⟨1566728, by rfl⟩ : syracuseStep 2088971 = 3133457) B3133457
theorem B1392651 : Blo 1391515 1392651 := bstep (se 1 (by rfl) ⟨1044488, by rfl⟩ : syracuseStep 1392651 = 2088977) B2088977
theorem B2088983 : Blo 1391515 2088983 := bstep (se 1 (by rfl) ⟨1566737, by rfl⟩ : syracuseStep 2088983 = 3133475) B3133475
theorem B1392663 : Blo 1391515 1392663 := bstep (se 1 (by rfl) ⟨1044497, by rfl⟩ : syracuseStep 1392663 = 2088995) B2088995
theorem B1392683 : Blo 1391515 1392683 := bstep (se 1 (by rfl) ⟨1044512, by rfl⟩ : syracuseStep 1392683 = 2089025) B2089025
theorem B11903021 : Blo 1391515 11903021 := bstep (se 3 (by rfl) ⟨2231816, by rfl⟩ : syracuseStep 11903021 = 4463633) B4463633
theorem B1392695 : Blo 1391515 1392695 := bstep (se 1 (by rfl) ⟨1044521, by rfl⟩ : syracuseStep 1392695 = 2089043) B2089043
theorem B1761355 : Blo 1391515 1761355 := bstep (se 1 (by rfl) ⟨1321016, by rfl⟩ : syracuseStep 1761355 = 2642033) B2642033
theorem B1392715 : Blo 1391515 1392715 := bstep (se 1 (by rfl) ⟨1044536, by rfl⟩ : syracuseStep 1392715 = 2089073) B2089073
theorem B1392727 : Blo 1391515 1392727 := bstep (se 1 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 1392727 = 2089091) B2089091
theorem B3522649 : Blo 1391515 3522649 := bstep (se 2 (by rfl) ⟨1320993, by rfl⟩ : syracuseStep 3522649 = 2641987) B2641987
theorem B2089049 : Blo 1391515 2089049 := bstep (se 2 (by rfl) ⟨783393, by rfl⟩ : syracuseStep 2089049 = 1566787) B1566787
theorem B3965021 : Blo 1391515 3965021 := bstep (se 3 (by rfl) ⟨743441, by rfl⟩ : syracuseStep 3965021 = 1486883) B1486883
theorem B1392747 : Blo 1391515 1392747 := bstep (se 1 (by rfl) ⟨1044560, by rfl⟩ : syracuseStep 1392747 = 2089121) B2089121
theorem B1392759 : Blo 1391515 1392759 := bstep (se 1 (by rfl) ⟨1044569, by rfl⟩ : syracuseStep 1392759 = 2089139) B2089139
theorem B1392779 : Blo 1391515 1392779 := bstep (se 1 (by rfl) ⟨1044584, by rfl⟩ : syracuseStep 1392779 = 2089169) B2089169
theorem B1392791 : Blo 1391515 1392791 := bstep (se 1 (by rfl) ⟨1044593, by rfl⟩ : syracuseStep 1392791 = 2089187) B2089187
theorem B1392811 : Blo 1391515 1392811 := bstep (se 1 (by rfl) ⟨1044608, by rfl⟩ : syracuseStep 1392811 = 2089217) B2089217
theorem B1392823 : Blo 1391515 1392823 := bstep (se 1 (by rfl) ⟨1044617, by rfl⟩ : syracuseStep 1392823 = 2089235) B2089235
theorem B2089163 : Blo 1391515 2089163 := bstep (se 1 (by rfl) ⟨1566872, by rfl⟩ : syracuseStep 2089163 = 3133745) B3133745
theorem B1392843 : Blo 1391515 1392843 := bstep (se 1 (by rfl) ⟨1044632, by rfl⟩ : syracuseStep 1392843 = 2089265) B2089265
theorem B2089175 : Blo 1391515 2089175 := bstep (se 1 (by rfl) ⟨1566881, by rfl⟩ : syracuseStep 2089175 = 3133763) B3133763
theorem B1392855 : Blo 1391515 1392855 := bstep (se 1 (by rfl) ⟨1044641, by rfl⟩ : syracuseStep 1392855 = 2089283) B2089283
theorem B1392875 : Blo 1391515 1392875 := bstep (se 1 (by rfl) ⟨1044656, by rfl⟩ : syracuseStep 1392875 = 2089313) B2089313
theorem B1392887 : Blo 1391515 1392887 := bstep (se 1 (by rfl) ⟨1044665, by rfl⟩ : syracuseStep 1392887 = 2089331) B2089331
theorem B1392907 : Blo 1391515 1392907 := bstep (se 1 (by rfl) ⟨1044680, by rfl⟩ : syracuseStep 1392907 = 2089361) B2089361
theorem B1392919 : Blo 1391515 1392919 := bstep (se 1 (by rfl) ⟨1044689, by rfl⟩ : syracuseStep 1392919 = 2089379) B2089379
theorem B2089241 : Blo 1391515 2089241 := bstep (se 2 (by rfl) ⟨783465, by rfl⟩ : syracuseStep 2089241 = 1566931) B1566931
theorem B1392939 : Blo 1391515 1392939 := bstep (se 1 (by rfl) ⟨1044704, by rfl⟩ : syracuseStep 1392939 = 2089409) B2089409
theorem B1392951 : Blo 1391515 1392951 := bstep (se 1 (by rfl) ⟨1044713, by rfl⟩ : syracuseStep 1392951 = 2089427) B2089427
theorem B1392971 : Blo 1391515 1392971 := bstep (se 1 (by rfl) ⟨1044728, by rfl⟩ : syracuseStep 1392971 = 2089457) B2089457
theorem B1392983 : Blo 1391515 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B1393003 : Blo 1391515 1393003 := bstep (se 1 (by rfl) ⟨1044752, by rfl⟩ : syracuseStep 1393003 = 2089505) B2089505
theorem B1393015 : Blo 1391515 1393015 := bstep (se 1 (by rfl) ⟨1044761, by rfl⟩ : syracuseStep 1393015 = 2089523) B2089523
theorem B2089355 : Blo 1391515 2089355 := bstep (se 1 (by rfl) ⟨1567016, by rfl⟩ : syracuseStep 2089355 = 3134033) B3134033
theorem B1393035 : Blo 1391515 1393035 := bstep (se 1 (by rfl) ⟨1044776, by rfl⟩ : syracuseStep 1393035 = 2089553) B2089553
theorem B2089367 : Blo 1391515 2089367 := bstep (se 1 (by rfl) ⟨1567025, by rfl⟩ : syracuseStep 2089367 = 3134051) B3134051
theorem B1393047 : Blo 1391515 1393047 := bstep (se 1 (by rfl) ⟨1044785, by rfl⟩ : syracuseStep 1393047 = 2089571) B2089571
theorem B1393067 : Blo 1391515 1393067 := bstep (se 1 (by rfl) ⟨1044800, by rfl⟩ : syracuseStep 1393067 = 2089601) B2089601
theorem B6693299 : Blo 1391515 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B1393079 : Blo 1391515 1393079 := bstep (se 1 (by rfl) ⟨1044809, by rfl⟩ : syracuseStep 1393079 = 2089619) B2089619
theorem B4702643 : Blo 1391515 4702643 := bstep (se 1 (by rfl) ⟨3526982, by rfl⟩ : syracuseStep 4702643 = 7053965) B7053965
theorem B3572171 : Blo 1391515 3572171 := bstep (se 1 (by rfl) ⟨2679128, by rfl⟩ : syracuseStep 3572171 = 5358257) B5358257
theorem B1393099 : Blo 1391515 1393099 := bstep (se 1 (by rfl) ⟨1044824, by rfl⟩ : syracuseStep 1393099 = 2089649) B2089649
theorem B1393111 : Blo 1391515 1393111 := bstep (se 1 (by rfl) ⟨1044833, by rfl⟩ : syracuseStep 1393111 = 2089667) B2089667
theorem B2089433 : Blo 1391515 2089433 := bstep (se 2 (by rfl) ⟨783537, by rfl⟩ : syracuseStep 2089433 = 1567075) B1567075
theorem B1393131 : Blo 1391515 1393131 := bstep (se 1 (by rfl) ⟨1044848, by rfl⟩ : syracuseStep 1393131 = 2089697) B2089697
theorem B1393143 : Blo 1391515 1393143 := bstep (se 1 (by rfl) ⟨1044857, by rfl⟩ : syracuseStep 1393143 = 2089715) B2089715
theorem B1393163 : Blo 1391515 1393163 := bstep (se 1 (by rfl) ⟨1044872, by rfl⟩ : syracuseStep 1393163 = 2089745) B2089745
theorem B1393175 : Blo 1391515 1393175 := bstep (se 1 (by rfl) ⟨1044881, by rfl⟩ : syracuseStep 1393175 = 2089763) B2089763
theorem B1393195 : Blo 1391515 1393195 := bstep (se 1 (by rfl) ⟨1044896, by rfl⟩ : syracuseStep 1393195 = 2089793) B2089793
theorem B1393207 : Blo 1391515 1393207 := bstep (se 1 (by rfl) ⟨1044905, by rfl⟩ : syracuseStep 1393207 = 2089811) B2089811
theorem B2089547 : Blo 1391515 2089547 := bstep (se 1 (by rfl) ⟨1567160, by rfl⟩ : syracuseStep 2089547 = 3134321) B3134321
theorem B1393227 : Blo 1391515 1393227 := bstep (se 1 (by rfl) ⟨1044920, by rfl⟩ : syracuseStep 1393227 = 2089841) B2089841
theorem B2089559 : Blo 1391515 2089559 := bstep (se 1 (by rfl) ⟨1567169, by rfl⟩ : syracuseStep 2089559 = 3134339) B3134339
theorem B1393239 : Blo 1391515 1393239 := bstep (se 1 (by rfl) ⟨1044929, by rfl⟩ : syracuseStep 1393239 = 2089859) B2089859
theorem B1393259 : Blo 1391515 1393259 := bstep (se 1 (by rfl) ⟨1044944, by rfl⟩ : syracuseStep 1393259 = 2089889) B2089889
theorem B1393271 : Blo 1391515 1393271 := bstep (se 1 (by rfl) ⟨1044953, by rfl⟩ : syracuseStep 1393271 = 2089907) B2089907
theorem B1393291 : Blo 1391515 1393291 := bstep (se 1 (by rfl) ⟨1044968, by rfl⟩ : syracuseStep 1393291 = 2089937) B2089937
theorem B1393303 : Blo 1391515 1393303 := bstep (se 1 (by rfl) ⟨1044977, by rfl⟩ : syracuseStep 1393303 = 2089955) B2089955
theorem B2089625 : Blo 1391515 2089625 := bstep (se 2 (by rfl) ⟨783609, by rfl⟩ : syracuseStep 2089625 = 1567219) B1567219
theorem B1393323 : Blo 1391515 1393323 := bstep (se 1 (by rfl) ⟨1044992, by rfl⟩ : syracuseStep 1393323 = 2089985) B2089985
theorem B1393335 : Blo 1391515 1393335 := bstep (se 1 (by rfl) ⟨1045001, by rfl⟩ : syracuseStep 1393335 = 2090003) B2090003
theorem B4702913 : Blo 1391515 4702913 := bstep (se 2 (by rfl) ⟨1763592, by rfl⟩ : syracuseStep 4702913 = 3527185) B3527185
theorem B1393355 : Blo 1391515 1393355 := bstep (se 1 (by rfl) ⟨1045016, by rfl⟩ : syracuseStep 1393355 = 2090033) B2090033
theorem B2974423 : Blo 1391515 2974423 := bstep (se 1 (by rfl) ⟨2230817, by rfl⟩ : syracuseStep 2974423 = 4461635) B4461635
theorem B1393367 : Blo 1391515 1393367 := bstep (se 1 (by rfl) ⟨1045025, by rfl⟩ : syracuseStep 1393367 = 2090051) B2090051
theorem B11903705 : Blo 1391515 11903705 := bstep (se 2 (by rfl) ⟨4463889, by rfl⟩ : syracuseStep 11903705 = 8927779) B8927779
theorem B1393387 : Blo 1391515 1393387 := bstep (se 1 (by rfl) ⟨1045040, by rfl⟩ : syracuseStep 1393387 = 2090081) B2090081
theorem B1393399 : Blo 1391515 1393399 := bstep (se 1 (by rfl) ⟨1045049, by rfl⟩ : syracuseStep 1393399 = 2090099) B2090099
theorem B2974475 : Blo 1391515 2974475 := bstep (se 1 (by rfl) ⟨2230856, by rfl⟩ : syracuseStep 2974475 = 4461713) B4461713
theorem B2089739 : Blo 1391515 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B1393419 : Blo 1391515 1393419 := bstep (se 1 (by rfl) ⟨1045064, by rfl⟩ : syracuseStep 1393419 = 2090129) B2090129
theorem B2089751 : Blo 1391515 2089751 := bstep (se 1 (by rfl) ⟨1567313, by rfl⟩ : syracuseStep 2089751 = 3134627) B3134627
theorem B1393431 : Blo 1391515 1393431 := bstep (se 1 (by rfl) ⟨1045073, by rfl⟩ : syracuseStep 1393431 = 2090147) B2090147
theorem B1393451 : Blo 1391515 1393451 := bstep (se 1 (by rfl) ⟨1045088, by rfl⟩ : syracuseStep 1393451 = 2090177) B2090177
theorem B1393463 : Blo 1391515 1393463 := bstep (se 1 (by rfl) ⟨1045097, by rfl⟩ : syracuseStep 1393463 = 2090195) B2090195
theorem B5284673 : Blo 1391515 5284673 := bstep (se 2 (by rfl) ⟨1981752, by rfl⟩ : syracuseStep 5284673 = 3963505) B3963505
theorem B1393483 : Blo 1391515 1393483 := bstep (se 1 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 1393483 = 2090225) B2090225
theorem B1565527 : Blo 1391515 1565527 := bstep (se 1 (by rfl) ⟨1174145, by rfl⟩ : syracuseStep 1565527 = 2348291) B2348291
theorem B1393495 : Blo 1391515 1393495 := bstep (se 1 (by rfl) ⟨1045121, by rfl⟩ : syracuseStep 1393495 = 2090243) B2090243
theorem B2089817 : Blo 1391515 2089817 := bstep (se 2 (by rfl) ⟨783681, by rfl⟩ : syracuseStep 2089817 = 1567363) B1567363
theorem B1393515 : Blo 1391515 1393515 := bstep (se 1 (by rfl) ⟨1045136, by rfl⟩ : syracuseStep 1393515 = 2090273) B2090273
theorem B10576817 : Blo 1391515 10576817 := bstep (se 2 (by rfl) ⟨3966306, by rfl⟩ : syracuseStep 10576817 = 7932613) B7932613
theorem B2089931 : Blo 1391515 2089931 := bstep (se 1 (by rfl) ⟨1567448, by rfl⟩ : syracuseStep 2089931 = 3134897) B3134897
theorem B2089943 : Blo 1391515 2089943 := bstep (se 1 (by rfl) ⟨1567457, by rfl⟩ : syracuseStep 2089943 = 3134915) B3134915
theorem B1565707 : Blo 1391515 1565707 := bstep (se 1 (by rfl) ⟨1174280, by rfl⟩ : syracuseStep 1565707 = 2348561) B2348561
theorem B1762327 : Blo 1391515 1762327 := bstep (se 1 (by rfl) ⟨1321745, by rfl⟩ : syracuseStep 1762327 = 2643491) B2643491
theorem B2090009 : Blo 1391515 2090009 := bstep (se 2 (by rfl) ⟨783753, by rfl⟩ : syracuseStep 2090009 = 1567507) B1567507
theorem B7046189 : Blo 1391515 7046189 := bstep (se 3 (by rfl) ⟨1321160, by rfl⟩ : syracuseStep 7046189 = 2642321) B2642321
theorem B1983575 : Blo 1391515 1983575 := bstep (se 1 (by rfl) ⟨1487681, by rfl⟩ : syracuseStep 1983575 = 2975363) B2975363
theorem B7930973 : Blo 1391515 7930973 := bstep (se 3 (by rfl) ⟨1487057, by rfl⟩ : syracuseStep 7930973 = 2974115) B2974115
theorem B1565815 : Blo 1391515 1565815 := bstep (se 1 (by rfl) ⟨1174361, by rfl⟩ : syracuseStep 1565815 = 2348723) B2348723
theorem B2090123 : Blo 1391515 2090123 := bstep (se 1 (by rfl) ⟨1567592, by rfl⟩ : syracuseStep 2090123 = 3135185) B3135185
theorem B2090135 : Blo 1391515 2090135 := bstep (se 1 (by rfl) ⟨1567601, by rfl⟩ : syracuseStep 2090135 = 3135203) B3135203
theorem B3523763 : Blo 1391515 3523763 := bstep (se 1 (by rfl) ⟨2642822, by rfl⟩ : syracuseStep 3523763 = 5285645) B5285645
theorem B185558197 : Blo 1391515 185558197 := bstep (se 5 (by rfl) ⟨8698040, by rfl⟩ : syracuseStep 185558197 = 17396081) B17396081
theorem B2090201 : Blo 1391515 2090201 := bstep (se 2 (by rfl) ⟨783825, by rfl⟩ : syracuseStep 2090201 = 1567651) B1567651
theorem B1565995 : Blo 1391515 1565995 := bstep (se 1 (by rfl) ⟨1174496, by rfl⟩ : syracuseStep 1565995 = 2348993) B2348993
theorem B5948761 : Blo 1391515 5948761 := bstep (se 2 (by rfl) ⟨2230785, by rfl⟩ : syracuseStep 5948761 = 4461571) B4461571
theorem B1566103 : Blo 1391515 1566103 := bstep (se 1 (by rfl) ⟨1174577, by rfl⟩ : syracuseStep 1566103 = 2349155) B2349155
theorem B10577303 : Blo 1391515 10577303 := bstep (se 1 (by rfl) ⟨7932977, by rfl⟩ : syracuseStep 10577303 = 15865955) B15865955
theorem B3524057 : Blo 1391515 3524057 := bstep (se 2 (by rfl) ⟨1321521, by rfl⟩ : syracuseStep 3524057 = 2643043) B2643043
theorem B3573209 : Blo 1391515 3573209 := bstep (se 2 (by rfl) ⟨1339953, by rfl⟩ : syracuseStep 3573209 = 2679907) B2679907
theorem B4236761 : Blo 1391515 4236761 := bstep (se 2 (by rfl) ⟨1588785, by rfl⟩ : syracuseStep 4236761 = 3177571) B3177571
theorem B1410571 : Blo 1391515 1410571 := bstep (se 1 (by rfl) ⟨1057928, by rfl⟩ : syracuseStep 1410571 = 2115857) B2115857
theorem B3130955 : Blo 1391515 3130955 := bstep (se 1 (by rfl) ⟨2348216, by rfl⟩ : syracuseStep 3130955 = 4696433) B4696433
theorem B1566283 : Blo 1391515 1566283 := bstep (se 1 (by rfl) ⟨1174712, by rfl⟩ : syracuseStep 1566283 = 2349425) B2349425
theorem B3131009 : Blo 1391515 3131009 := bstep (se 2 (by rfl) ⟨1174128, by rfl⟩ : syracuseStep 3131009 = 2348257) B2348257
theorem B1566391 : Blo 1391515 1566391 := bstep (se 1 (by rfl) ⟨1174793, by rfl⟩ : syracuseStep 1566391 = 2349587) B2349587
theorem B1410859 : Blo 1391515 1410859 := bstep (se 1 (by rfl) ⟨1058144, by rfl⟩ : syracuseStep 1410859 = 2116289) B2116289
theorem B1763147 : Blo 1391515 1763147 := bstep (se 1 (by rfl) ⟨1322360, by rfl⟩ : syracuseStep 1763147 = 2644721) B2644721
theorem B3131225 : Blo 1391515 3131225 := bstep (se 2 (by rfl) ⟨1174209, by rfl⟩ : syracuseStep 3131225 = 2348419) B2348419
theorem B1566571 : Blo 1391515 1566571 := bstep (se 1 (by rfl) ⟨1174928, by rfl⟩ : syracuseStep 1566571 = 2349857) B2349857
theorem B12707761 : Blo 1391515 12707761 := bstep (se 2 (by rfl) ⟨4765410, by rfl⟩ : syracuseStep 12707761 = 9530821) B9530821
theorem B3131315 : Blo 1391515 3131315 := bstep (se 1 (by rfl) ⟨2348486, by rfl⟩ : syracuseStep 3131315 = 4696973) B4696973
theorem B3131351 : Blo 1391515 3131351 := bstep (se 1 (by rfl) ⟨2348513, by rfl⟩ : syracuseStep 3131351 = 4697027) B4697027
theorem B1566679 : Blo 1391515 1566679 := bstep (se 1 (by rfl) ⟨1175009, by rfl⟩ : syracuseStep 1566679 = 2350019) B2350019
theorem B3016705 : Blo 1391515 3016705 := bstep (se 2 (by rfl) ⟨1131264, by rfl⟩ : syracuseStep 3016705 = 2262529) B2262529
theorem B6350923 : Blo 1391515 6350923 := bstep (se 1 (by rfl) ⟨4763192, by rfl⟩ : syracuseStep 6350923 = 9526385) B9526385
theorem B3131531 : Blo 1391515 3131531 := bstep (se 1 (by rfl) ⟨2348648, by rfl⟩ : syracuseStep 3131531 = 4697297) B4697297
theorem B1566859 : Blo 1391515 1566859 := bstep (se 1 (by rfl) ⟨1175144, by rfl⟩ : syracuseStep 1566859 = 2350289) B2350289
theorem B3967127 : Blo 1391515 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B7145651 : Blo 1391515 7145651 := bstep (se 1 (by rfl) ⟨5359238, by rfl⟩ : syracuseStep 7145651 = 10718477) B10718477
theorem B3131585 : Blo 1391515 3131585 := bstep (se 2 (by rfl) ⟨1174344, by rfl⟩ : syracuseStep 3131585 = 2348689) B2348689
theorem B2754803 : Blo 1391515 2754803 := bstep (se 1 (by rfl) ⟨2066102, by rfl⟩ : syracuseStep 2754803 = 4132205) B4132205
theorem B1566967 : Blo 1391515 1566967 := bstep (se 1 (by rfl) ⟨1175225, by rfl⟩ : syracuseStep 1566967 = 2350451) B2350451
theorem B5286161 : Blo 1391515 5286161 := bstep (se 2 (by rfl) ⟨1982310, by rfl⟩ : syracuseStep 5286161 = 3964621) B3964621
theorem B5949719 : Blo 1391515 5949719 := bstep (se 1 (by rfl) ⟨4462289, by rfl⟩ : syracuseStep 5949719 = 8924579) B8924579
theorem B2976115 : Blo 1391515 2976115 := bstep (se 1 (by rfl) ⟨2232086, by rfl⟩ : syracuseStep 2976115 = 4464173) B4464173
theorem B15059317 : Blo 1391515 15059317 := bstep (se 5 (by rfl) ⟨705905, by rfl⟩ : syracuseStep 15059317 = 1411811) B1411811
theorem B3131801 : Blo 1391515 3131801 := bstep (se 2 (by rfl) ⟨1174425, by rfl⟩ : syracuseStep 3131801 = 2348851) B2348851
theorem B1567147 : Blo 1391515 1567147 := bstep (se 1 (by rfl) ⟨1175360, by rfl⟩ : syracuseStep 1567147 = 2350721) B2350721
theorem B1411511 : Blo 1391515 1411511 := bstep (se 1 (by rfl) ⟨1058633, by rfl⟩ : syracuseStep 1411511 = 2117267) B2117267
theorem B4696541 : Blo 1391515 4696541 := bstep (se 3 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 4696541 = 1761203) B1761203
theorem B3131891 : Blo 1391515 3131891 := bstep (se 1 (by rfl) ⟨2348918, by rfl⟩ : syracuseStep 3131891 = 4697837) B4697837
theorem B3131927 : Blo 1391515 3131927 := bstep (se 1 (by rfl) ⟨2348945, by rfl⟩ : syracuseStep 3131927 = 4697891) B4697891
theorem B1567255 : Blo 1391515 1567255 := bstep (se 1 (by rfl) ⟨1175441, by rfl⟩ : syracuseStep 1567255 = 2350883) B2350883
theorem B5646937 : Blo 1391515 5646937 := bstep (se 2 (by rfl) ⟨2117601, by rfl⟩ : syracuseStep 5646937 = 4235203) B4235203
theorem B6032017 : Blo 1391515 6032017 := bstep (se 2 (by rfl) ⟨2262006, by rfl⟩ : syracuseStep 6032017 = 4524013) B4524013
theorem B3132107 : Blo 1391515 3132107 := bstep (se 1 (by rfl) ⟨2349080, by rfl⟩ : syracuseStep 3132107 = 4698161) B4698161
theorem B1567435 : Blo 1391515 1567435 := bstep (se 1 (by rfl) ⟨1175576, by rfl⟩ : syracuseStep 1567435 = 2351153) B2351153
theorem B4459225 : Blo 1391515 4459225 := bstep (se 2 (by rfl) ⟨1672209, by rfl⟩ : syracuseStep 4459225 = 3344419) B3344419
theorem B5286617 : Blo 1391515 5286617 := bstep (se 2 (by rfl) ⟨1982481, by rfl⟩ : syracuseStep 5286617 = 3964963) B3964963
theorem B3574489 : Blo 1391515 3574489 := bstep (se 2 (by rfl) ⟨1340433, by rfl⟩ : syracuseStep 3574489 = 2680867) B2680867
theorem B2509555 : Blo 1391515 2509555 := bstep (se 1 (by rfl) ⟨1882166, by rfl⟩ : syracuseStep 2509555 = 3764333) B3764333
theorem B3132161 : Blo 1391515 3132161 := bstep (se 2 (by rfl) ⟨1174560, by rfl⟩ : syracuseStep 3132161 = 2349121) B2349121
theorem B1567543 : Blo 1391515 1567543 := bstep (se 1 (by rfl) ⟨1175657, by rfl⟩ : syracuseStep 1567543 = 2351315) B2351315
theorem B5286829 : Blo 1391515 5286829 := bstep (se 3 (by rfl) ⟨991280, by rfl⟩ : syracuseStep 5286829 = 1982561) B1982561
theorem B3967937 : Blo 1391515 3967937 := bstep (se 2 (by rfl) ⟨1487976, by rfl⟩ : syracuseStep 3967937 = 2975953) B2975953
theorem B2509771 : Blo 1391515 2509771 := bstep (se 1 (by rfl) ⟨1882328, by rfl⟩ : syracuseStep 2509771 = 3764657) B3764657
theorem B11439053 : Blo 1391515 11439053 := bstep (se 3 (by rfl) ⟨2144822, by rfl⟩ : syracuseStep 11439053 = 4289645) B4289645
theorem B11889625 : Blo 1391515 11889625 := bstep (se 2 (by rfl) ⟨4458609, by rfl⟩ : syracuseStep 11889625 = 8917219) B8917219
theorem B3132377 : Blo 1391515 3132377 := bstep (se 2 (by rfl) ⟨1174641, by rfl⟩ : syracuseStep 3132377 = 2349283) B2349283
theorem B3132467 : Blo 1391515 3132467 := bstep (se 1 (by rfl) ⟨2349350, by rfl⟩ : syracuseStep 3132467 = 4698701) B4698701
theorem B28568645 : Blo 1391515 28568645 := bstep (se 4 (by rfl) ⟨2678310, by rfl⟩ : syracuseStep 28568645 = 5356621) B5356621
theorem B3525707 : Blo 1391515 3525707 := bstep (se 1 (by rfl) ⟨2644280, by rfl⟩ : syracuseStep 3525707 = 5288561) B5288561
theorem B3132503 : Blo 1391515 3132503 := bstep (se 1 (by rfl) ⟨2349377, by rfl⟩ : syracuseStep 3132503 = 4698755) B4698755
theorem B5287133 : Blo 1391515 5287133 := bstep (se 3 (by rfl) ⟨991337, by rfl⟩ : syracuseStep 5287133 = 1982675) B1982675
theorem B3132683 : Blo 1391515 3132683 := bstep (se 1 (by rfl) ⟨2349512, by rfl⟩ : syracuseStep 3132683 = 4699025) B4699025
theorem B10038563 : Blo 1391515 10038563 := bstep (se 1 (by rfl) ⟨7528922, by rfl⟩ : syracuseStep 10038563 = 15057845) B15057845
theorem B1486135 : Blo 1391515 1486135 := bstep (se 1 (by rfl) ⟨1114601, by rfl⟩ : syracuseStep 1486135 = 2229203) B2229203
theorem B3132737 : Blo 1391515 3132737 := bstep (se 2 (by rfl) ⟨1174776, by rfl⟩ : syracuseStep 3132737 = 2349553) B2349553
theorem B11898373 : Blo 1391515 11898373 := bstep (se 4 (by rfl) ⟨1115472, by rfl⟩ : syracuseStep 11898373 = 2230945) B2230945
theorem B5721617 : Blo 1391515 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B3132953 : Blo 1391515 3132953 := bstep (se 2 (by rfl) ⟨1174857, by rfl⟩ : syracuseStep 3132953 = 2349715) B2349715
theorem B7925323 : Blo 1391515 7925323 := bstep (se 1 (by rfl) ⟨5943992, by rfl⟩ : syracuseStep 7925323 = 11887985) B11887985
theorem B4697675 : Blo 1391515 4697675 := bstep (se 1 (by rfl) ⟨3523256, by rfl⟩ : syracuseStep 4697675 = 7046513) B7046513
theorem B30133853 : Blo 1391515 30133853 := bstep (se 3 (by rfl) ⟨5650097, by rfl⟩ : syracuseStep 30133853 = 11300195) B11300195
theorem B8916581 : Blo 1391515 8916581 := bstep (se 4 (by rfl) ⟨835929, by rfl⟩ : syracuseStep 8916581 = 1671859) B1671859
theorem B3133043 : Blo 1391515 3133043 := bstep (se 1 (by rfl) ⟨2349782, by rfl⟩ : syracuseStep 3133043 = 4699565) B4699565
theorem B7933571 : Blo 1391515 7933571 := bstep (se 1 (by rfl) ⟨5950178, by rfl⟩ : syracuseStep 7933571 = 11900357) B11900357
theorem B3133079 : Blo 1391515 3133079 := bstep (se 1 (by rfl) ⟨2349809, by rfl⟩ : syracuseStep 3133079 = 4699619) B4699619
theorem B1486507 : Blo 1391515 1486507 := bstep (se 1 (by rfl) ⟨1114880, by rfl⟩ : syracuseStep 1486507 = 2229761) B2229761
theorem B2641729 : Blo 1391515 2641729 := bstep (se 2 (by rfl) ⟨990648, by rfl⟩ : syracuseStep 2641729 = 1981297) B1981297
theorem B3133259 : Blo 1391515 3133259 := bstep (se 1 (by rfl) ⟨2349944, by rfl⟩ : syracuseStep 3133259 = 4699889) B4699889
theorem B4697945 : Blo 1391515 4697945 := bstep (se 2 (by rfl) ⟨1761729, by rfl⟩ : syracuseStep 4697945 = 3523459) B3523459
theorem B3346265 : Blo 1391515 3346265 := bstep (se 2 (by rfl) ⟨1254849, by rfl⟩ : syracuseStep 3346265 = 2509699) B2509699
theorem B7925597 : Blo 1391515 7925597 := bstep (se 3 (by rfl) ⟨1486049, by rfl⟩ : syracuseStep 7925597 = 2972099) B2972099
theorem B3133313 : Blo 1391515 3133313 := bstep (se 2 (by rfl) ⟨1174992, by rfl⟩ : syracuseStep 3133313 = 2349985) B2349985
theorem B11890583 : Blo 1391515 11890583 := bstep (se 1 (by rfl) ⟨8917937, by rfl⟩ : syracuseStep 11890583 = 17835875) B17835875
theorem B10719155 : Blo 1391515 10719155 := bstep (se 1 (by rfl) ⟨8039366, by rfl⟩ : syracuseStep 10719155 = 16078733) B16078733
theorem B3526679 : Blo 1391515 3526679 := bstep (se 1 (by rfl) ⟨2645009, by rfl⟩ : syracuseStep 3526679 = 5290019) B5290019
theorem B3305537 : Blo 1391515 3305537 := bstep (se 2 (by rfl) ⟨1239576, by rfl⟩ : syracuseStep 3305537 = 2479153) B2479153
theorem B4460609 : Blo 1391515 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B8917067 : Blo 1391515 8917067 := bstep (se 1 (by rfl) ⟨6687800, by rfl⟩ : syracuseStep 8917067 = 13375601) B13375601
theorem B3133529 : Blo 1391515 3133529 := bstep (se 2 (by rfl) ⟨1175073, by rfl⟩ : syracuseStep 3133529 = 2350147) B2350147
theorem B1486955 : Blo 1391515 1486955 := bstep (se 1 (by rfl) ⟨1115216, by rfl⟩ : syracuseStep 1486955 = 2230433) B2230433
theorem B6025367 : Blo 1391515 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B2642071 : Blo 1391515 2642071 := bstep (se 1 (by rfl) ⟨1981553, by rfl⟩ : syracuseStep 2642071 = 3963107) B3963107
theorem B3133619 : Blo 1391515 3133619 := bstep (se 1 (by rfl) ⟨2350214, by rfl⟩ : syracuseStep 3133619 = 4700429) B4700429
theorem B6353099 : Blo 1391515 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B3133655 : Blo 1391515 3133655 := bstep (se 1 (by rfl) ⟨2350241, by rfl⟩ : syracuseStep 3133655 = 4700483) B4700483
theorem B6353113 : Blo 1391515 6353113 := bstep (se 2 (by rfl) ⟨2382417, by rfl⟩ : syracuseStep 6353113 = 4764835) B4764835
theorem B11890961 : Blo 1391515 11890961 := bstep (se 2 (by rfl) ⟨4459110, by rfl⟩ : syracuseStep 11890961 = 8918221) B8918221
theorem B5951819 : Blo 1391515 5951819 := bstep (se 1 (by rfl) ⟨4463864, by rfl⟩ : syracuseStep 5951819 = 8927729) B8927729
theorem B2642291 : Blo 1391515 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B30110069 : Blo 1391515 30110069 := bstep (se 5 (by rfl) ⟨1411409, by rfl⟩ : syracuseStep 30110069 = 2822819) B2822819
theorem B3133835 : Blo 1391515 3133835 := bstep (se 1 (by rfl) ⟨2350376, by rfl⟩ : syracuseStep 3133835 = 4700753) B4700753
theorem B3133889 : Blo 1391515 3133889 := bstep (se 2 (by rfl) ⟨1175208, by rfl⟩ : syracuseStep 3133889 = 2350417) B2350417
theorem B4698647 : Blo 1391515 4698647 := bstep (se 1 (by rfl) ⟨3523985, by rfl⟩ : syracuseStep 4698647 = 7047971) B7047971
theorem B2642519 : Blo 1391515 2642519 := bstep (se 1 (by rfl) ⟨1981889, by rfl⟩ : syracuseStep 2642519 = 3963779) B3963779
theorem B3134105 : Blo 1391515 3134105 := bstep (se 2 (by rfl) ⟨1175289, by rfl⟩ : syracuseStep 3134105 = 2350579) B2350579
theorem B10310323 : Blo 1391515 10310323 := bstep (se 1 (by rfl) ⟨7732742, by rfl⟩ : syracuseStep 10310323 = 15465485) B15465485
theorem B3134195 : Blo 1391515 3134195 := bstep (se 1 (by rfl) ⟨2350646, by rfl⟩ : syracuseStep 3134195 = 4701293) B4701293
theorem B3134231 : Blo 1391515 3134231 := bstep (se 1 (by rfl) ⟨2350673, by rfl⟩ : syracuseStep 3134231 = 4701347) B4701347
theorem B2642777 : Blo 1391515 2642777 := bstep (se 2 (by rfl) ⟨991041, by rfl⟩ : syracuseStep 2642777 = 1982083) B1982083
theorem B7050077 : Blo 1391515 7050077 := bstep (se 3 (by rfl) ⟨1321889, by rfl⟩ : syracuseStep 7050077 = 2643779) B2643779
theorem B3765143 : Blo 1391515 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B3134411 : Blo 1391515 3134411 := bstep (se 1 (by rfl) ⟨2350808, by rfl⟩ : syracuseStep 3134411 = 4701617) B4701617
theorem B3134465 : Blo 1391515 3134465 := bstep (se 2 (by rfl) ⟨1175424, by rfl⟩ : syracuseStep 3134465 = 2350849) B2350849
theorem B13390865 : Blo 1391515 13390865 := bstep (se 2 (by rfl) ⟨5021574, by rfl⟩ : syracuseStep 13390865 = 10043149) B10043149
theorem B78271523 : Blo 1391515 78271523 := bstep (se 1 (by rfl) ⟨58703642, by rfl⟩ : syracuseStep 78271523 = 117407285) B117407285
theorem B4699187 : Blo 1391515 4699187 := bstep (se 1 (by rfl) ⟨3524390, by rfl⟩ : syracuseStep 4699187 = 7048781) B7048781
theorem B3175499 : Blo 1391515 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B2348183 : Blo 1391515 2348183 := bstep (se 1 (by rfl) ⟨1761137, by rfl⟩ : syracuseStep 2348183 = 3522275) B3522275
theorem B3134681 : Blo 1391515 3134681 := bstep (se 2 (by rfl) ⟨1175505, by rfl⟩ : syracuseStep 3134681 = 2351011) B2351011
theorem B2643187 : Blo 1391515 2643187 := bstep (se 1 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 2643187 = 3964781) B3964781
theorem B2348311 : Blo 1391515 2348311 := bstep (se 1 (by rfl) ⟨1761233, by rfl⟩ : syracuseStep 2348311 = 3522467) B3522467
theorem B3134771 : Blo 1391515 3134771 := bstep (se 1 (by rfl) ⟨2351078, by rfl⟩ : syracuseStep 3134771 = 4702157) B4702157
theorem B4699457 : Blo 1391515 4699457 := bstep (se 2 (by rfl) ⟨1762296, by rfl⟩ : syracuseStep 4699457 = 3524593) B3524593
theorem B5084491 : Blo 1391515 5084491 := bstep (se 1 (by rfl) ⟨3813368, by rfl⟩ : syracuseStep 5084491 = 7626737) B7626737
theorem B3134807 : Blo 1391515 3134807 := bstep (se 1 (by rfl) ⟨2351105, by rfl⟩ : syracuseStep 3134807 = 4702211) B4702211
theorem B2381323 : Blo 1391515 2381323 := bstep (se 1 (by rfl) ⟨1785992, by rfl⟩ : syracuseStep 2381323 = 3571985) B3571985
theorem B3134987 : Blo 1391515 3134987 := bstep (se 1 (by rfl) ⟨2351240, by rfl⟩ : syracuseStep 3134987 = 4702481) B4702481
theorem B3135041 : Blo 1391515 3135041 := bstep (se 2 (by rfl) ⟨1175640, by rfl⟩ : syracuseStep 3135041 = 2351281) B2351281
theorem B8918707 : Blo 1391515 8918707 := bstep (se 1 (by rfl) ⟨6689030, by rfl⟩ : syracuseStep 8918707 = 13378061) B13378061
theorem B2643673 : Blo 1391515 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B5289731 : Blo 1391515 5289731 := bstep (se 1 (by rfl) ⟨3967298, by rfl⟩ : syracuseStep 5289731 = 7934597) B7934597
theorem B5289745 : Blo 1391515 5289745 := bstep (se 2 (by rfl) ⟨1983654, by rfl⟩ : syracuseStep 5289745 = 3967309) B3967309
theorem B9049873 : Blo 1391515 9049873 := bstep (se 2 (by rfl) ⟨3393702, by rfl⟩ : syracuseStep 9049873 = 6787405) B6787405
theorem B3135257 : Blo 1391515 3135257 := bstep (se 2 (by rfl) ⟨1175721, by rfl⟩ : syracuseStep 3135257 = 2351443) B2351443
theorem B19052333 : Blo 1391515 19052333 := bstep (se 3 (by rfl) ⟨3572312, by rfl⟩ : syracuseStep 19052333 = 7144625) B7144625
theorem B4699997 : Blo 1391515 4699997 := bstep (se 3 (by rfl) ⟨881249, by rfl⟩ : syracuseStep 4699997 = 1762499) B1762499
theorem B3135347 : Blo 1391515 3135347 := bstep (se 1 (by rfl) ⟨2351510, by rfl⟩ : syracuseStep 3135347 = 4703021) B4703021
theorem B2348939 : Blo 1391515 2348939 := bstep (se 1 (by rfl) ⟨1761704, by rfl⟩ : syracuseStep 2348939 = 3523409) B3523409
theorem B3135383 : Blo 1391515 3135383 := bstep (se 1 (by rfl) ⟨2351537, by rfl⟩ : syracuseStep 3135383 = 4703075) B4703075
theorem B2349067 : Blo 1391515 2349067 := bstep (se 1 (by rfl) ⟨1761800, by rfl⟩ : syracuseStep 2349067 = 3523601) B3523601
theorem B11606051 : Blo 1391515 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B5290049 : Blo 1391515 5290049 := bstep (se 2 (by rfl) ⟨1983768, by rfl⟩ : syracuseStep 5290049 = 3967537) B3967537
theorem B16300163 : Blo 1391515 16300163 := bstep (se 1 (by rfl) ⟨12225122, by rfl⟩ : syracuseStep 16300163 = 24450245) B24450245
theorem B2349209 : Blo 1391515 2349209 := bstep (se 2 (by rfl) ⟨880953, by rfl⟩ : syracuseStep 2349209 = 1761907) B1761907
theorem B11901107 : Blo 1391515 11901107 := bstep (se 1 (by rfl) ⟨8925830, by rfl⟩ : syracuseStep 11901107 = 17851661) B17851661
theorem B4462813 : Blo 1391515 4462813 := bstep (se 3 (by rfl) ⟨836777, by rfl⟩ : syracuseStep 4462813 = 1673555) B1673555
theorem B2644235 : Blo 1391515 2644235 := bstep (se 1 (by rfl) ⟨1983176, by rfl⟩ : syracuseStep 2644235 = 3966353) B3966353
theorem B2349337 : Blo 1391515 2349337 := bstep (se 2 (by rfl) ⟨881001, by rfl⟩ : syracuseStep 2349337 = 1762003) B1762003
theorem B7346477 : Blo 1391515 7346477 := bstep (se 3 (by rfl) ⟨1377464, by rfl⟩ : syracuseStep 7346477 = 2754929) B2754929
theorem B2087321 : Blo 1391515 2087321 := bstep (se 2 (by rfl) ⟨782745, by rfl⟩ : syracuseStep 2087321 = 1565491) B1565491
theorem B5724589 : Blo 1391515 5724589 := bstep (se 3 (by rfl) ⟨1073360, by rfl⟩ : syracuseStep 5724589 = 2146721) B2146721
theorem B2644417 : Blo 1391515 2644417 := bstep (se 2 (by rfl) ⟨991656, by rfl⟩ : syracuseStep 2644417 = 1983313) B1983313
theorem B2087435 : Blo 1391515 2087435 := bstep (se 1 (by rfl) ⟨1565576, by rfl⟩ : syracuseStep 2087435 = 3131153) B3131153
theorem B2087447 : Blo 1391515 2087447 := bstep (se 1 (by rfl) ⟨1565585, by rfl⟩ : syracuseStep 2087447 = 3131171) B3131171
theorem B2087513 : Blo 1391515 2087513 := bstep (se 2 (by rfl) ⟨782817, by rfl⟩ : syracuseStep 2087513 = 1565635) B1565635
theorem B2087627 : Blo 1391515 2087627 := bstep (se 1 (by rfl) ⟨1565720, by rfl⟩ : syracuseStep 2087627 = 3131441) B3131441
theorem B2087639 : Blo 1391515 2087639 := bstep (se 1 (by rfl) ⟨1565729, by rfl⟩ : syracuseStep 2087639 = 3131459) B3131459
theorem B5290717 : Blo 1391515 5290717 := bstep (se 3 (by rfl) ⟨992009, by rfl⟩ : syracuseStep 5290717 = 1984019) B1984019
theorem B2145035 : Blo 1391515 2145035 := bstep (se 1 (by rfl) ⟨1608776, by rfl⟩ : syracuseStep 2145035 = 3217553) B3217553
theorem B2087705 : Blo 1391515 2087705 := bstep (se 2 (by rfl) ⟨782889, by rfl⟩ : syracuseStep 2087705 = 1565779) B1565779
theorem B2972467 : Blo 1391515 2972467 := bstep (se 1 (by rfl) ⟨2229350, by rfl⟩ : syracuseStep 2972467 = 4458701) B4458701
theorem B2349911 : Blo 1391515 2349911 := bstep (se 1 (by rfl) ⟨1762433, by rfl⟩ : syracuseStep 2349911 = 3524867) B3524867
theorem B2087819 : Blo 1391515 2087819 := bstep (se 1 (by rfl) ⟨1565864, by rfl⟩ : syracuseStep 2087819 = 3131729) B3131729
theorem B2087831 : Blo 1391515 2087831 := bstep (se 1 (by rfl) ⟨1565873, by rfl⟩ : syracuseStep 2087831 = 3131747) B3131747
theorem B7052183 : Blo 1391515 7052183 := bstep (se 1 (by rfl) ⟨5289137, by rfl⟩ : syracuseStep 7052183 = 10578275) B10578275
theorem B1391531 : Blo 1391515 1391531 := bstep (se 1 (by rfl) ⟨1043648, by rfl⟩ : syracuseStep 1391531 = 2087297) B2087297
theorem B1391543 : Blo 1391515 1391543 := bstep (se 1 (by rfl) ⟨1043657, by rfl⟩ : syracuseStep 1391543 = 2087315) B2087315
theorem B114342853 : Blo 1391515 114342853 := bstep (se 4 (by rfl) ⟨10719642, by rfl⟩ : syracuseStep 114342853 = 21439285) B21439285
theorem B1391563 : Blo 1391515 1391563 := bstep (se 1 (by rfl) ⟨1043672, by rfl⟩ : syracuseStep 1391563 = 2087345) B2087345
theorem B4701131 : Blo 1391515 4701131 := bstep (se 1 (by rfl) ⟨3525848, by rfl⟩ : syracuseStep 4701131 = 7051697) B7051697
theorem B1391575 : Blo 1391515 1391575 := bstep (se 1 (by rfl) ⟨1043681, by rfl⟩ : syracuseStep 1391575 = 2087363) B2087363
theorem B2087897 : Blo 1391515 2087897 := bstep (se 2 (by rfl) ⟨782961, by rfl⟩ : syracuseStep 2087897 = 1565923) B1565923
theorem B2350039 : Blo 1391515 2350039 := bstep (se 1 (by rfl) ⟨1762529, by rfl⟩ : syracuseStep 2350039 = 3525059) B3525059
theorem B1391595 : Blo 1391515 1391595 := bstep (se 1 (by rfl) ⟨1043696, by rfl⟩ : syracuseStep 1391595 = 2087393) B2087393
theorem B1391607 : Blo 1391515 1391607 := bstep (se 1 (by rfl) ⟨1043705, by rfl⟩ : syracuseStep 1391607 = 2087411) B2087411
theorem B1391627 : Blo 1391515 1391627 := bstep (se 1 (by rfl) ⟨1043720, by rfl⟩ : syracuseStep 1391627 = 2087441) B2087441
theorem B5946385 : Blo 1391515 5946385 := bstep (se 2 (by rfl) ⟨2229894, by rfl⟩ : syracuseStep 5946385 = 4459789) B4459789
theorem B21740557 : Blo 1391515 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B1391639 : Blo 1391515 1391639 := bstep (se 1 (by rfl) ⟨1043729, by rfl⟩ : syracuseStep 1391639 = 2087459) B2087459
theorem B1391659 : Blo 1391515 1391659 := bstep (se 1 (by rfl) ⟨1043744, by rfl⟩ : syracuseStep 1391659 = 2087489) B2087489
theorem B1391671 : Blo 1391515 1391671 := bstep (se 1 (by rfl) ⟨1043753, by rfl⟩ : syracuseStep 1391671 = 2087507) B2087507
theorem B1391691 : Blo 1391515 1391691 := bstep (se 1 (by rfl) ⟨1043768, by rfl⟩ : syracuseStep 1391691 = 2087537) B2087537
theorem B2088011 : Blo 1391515 2088011 := bstep (se 1 (by rfl) ⟨1566008, by rfl⟩ : syracuseStep 2088011 = 3132017) B3132017
theorem B1391703 : Blo 1391515 1391703 := bstep (se 1 (by rfl) ⟨1043777, by rfl⟩ : syracuseStep 1391703 = 2087555) B2087555
theorem B2088023 : Blo 1391515 2088023 := bstep (se 1 (by rfl) ⟨1566017, by rfl⟩ : syracuseStep 2088023 = 3132035) B3132035
theorem B1883225 : Blo 1391515 1883225 := bstep (se 2 (by rfl) ⟨706209, by rfl⟩ : syracuseStep 1883225 = 1412419) B1412419
theorem B1391723 : Blo 1391515 1391723 := bstep (se 1 (by rfl) ⟨1043792, by rfl⟩ : syracuseStep 1391723 = 2087585) B2087585
theorem B1391735 : Blo 1391515 1391735 := bstep (se 1 (by rfl) ⟨1043801, by rfl⟩ : syracuseStep 1391735 = 2087603) B2087603
theorem B1391755 : Blo 1391515 1391755 := bstep (se 1 (by rfl) ⟨1043816, by rfl⟩ : syracuseStep 1391755 = 2087633) B2087633
theorem B2645131 : Blo 1391515 2645131 := bstep (se 1 (by rfl) ⟨1983848, by rfl⟩ : syracuseStep 2645131 = 3967697) B3967697
theorem B1391767 : Blo 1391515 1391767 := bstep (se 1 (by rfl) ⟨1043825, by rfl⟩ : syracuseStep 1391767 = 2087651) B2087651
theorem B2088089 : Blo 1391515 2088089 := bstep (se 2 (by rfl) ⟨783033, by rfl⟩ : syracuseStep 2088089 = 1566067) B1566067
theorem B1391787 : Blo 1391515 1391787 := bstep (se 1 (by rfl) ⟨1043840, by rfl⟩ : syracuseStep 1391787 = 2087681) B2087681
theorem B6110387 : Blo 1391515 6110387 := bstep (se 1 (by rfl) ⟨4582790, by rfl⟩ : syracuseStep 6110387 = 9165581) B9165581
theorem B1391799 : Blo 1391515 1391799 := bstep (se 1 (by rfl) ⟨1043849, by rfl⟩ : syracuseStep 1391799 = 2087699) B2087699
theorem B1391819 : Blo 1391515 1391819 := bstep (se 1 (by rfl) ⟨1043864, by rfl⟩ : syracuseStep 1391819 = 2087729) B2087729
theorem B1391831 : Blo 1391515 1391831 := bstep (se 1 (by rfl) ⟨1043873, by rfl⟩ : syracuseStep 1391831 = 2087747) B2087747
theorem B2645207 : Blo 1391515 2645207 := bstep (se 1 (by rfl) ⟨1983905, by rfl⟩ : syracuseStep 2645207 = 3967811) B3967811
theorem B4701401 : Blo 1391515 4701401 := bstep (se 2 (by rfl) ⟨1763025, by rfl⟩ : syracuseStep 4701401 = 3526051) B3526051
theorem B1883351 : Blo 1391515 1883351 := bstep (se 1 (by rfl) ⟨1412513, by rfl⟩ : syracuseStep 1883351 = 2825027) B2825027
theorem B1391851 : Blo 1391515 1391851 := bstep (se 1 (by rfl) ⟨1043888, by rfl⟩ : syracuseStep 1391851 = 2087777) B2087777
theorem B1391863 : Blo 1391515 1391863 := bstep (se 1 (by rfl) ⟨1043897, by rfl⟩ : syracuseStep 1391863 = 2087795) B2087795
theorem B1391883 : Blo 1391515 1391883 := bstep (se 1 (by rfl) ⟨1043912, by rfl⟩ : syracuseStep 1391883 = 2087825) B2087825
theorem B2088203 : Blo 1391515 2088203 := bstep (se 1 (by rfl) ⟨1566152, by rfl⟩ : syracuseStep 2088203 = 3132305) B3132305
theorem B1391895 : Blo 1391515 1391895 := bstep (se 1 (by rfl) ⟨1043921, by rfl⟩ : syracuseStep 1391895 = 2087843) B2087843
theorem B2088215 : Blo 1391515 2088215 := bstep (se 1 (by rfl) ⟨1566161, by rfl⟩ : syracuseStep 2088215 = 3132323) B3132323
theorem B2972953 : Blo 1391515 2972953 := bstep (se 2 (by rfl) ⟨1114857, by rfl⟩ : syracuseStep 2972953 = 2229715) B2229715
theorem B1391915 : Blo 1391515 1391915 := bstep (se 1 (by rfl) ⟨1043936, by rfl⟩ : syracuseStep 1391915 = 2087873) B2087873
theorem B3964211 : Blo 1391515 3964211 := bstep (se 1 (by rfl) ⟨2973158, by rfl⟩ : syracuseStep 3964211 = 5946317) B5946317
theorem B1391927 : Blo 1391515 1391927 := bstep (se 1 (by rfl) ⟨1043945, by rfl⟩ : syracuseStep 1391927 = 2087891) B2087891
theorem B1391947 : Blo 1391515 1391947 := bstep (se 1 (by rfl) ⟨1043960, by rfl⟩ : syracuseStep 1391947 = 2087921) B2087921
theorem B1391959 : Blo 1391515 1391959 := bstep (se 1 (by rfl) ⟨1043969, by rfl⟩ : syracuseStep 1391959 = 2087939) B2087939
theorem B1588567 : Blo 1391515 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B2088281 : Blo 1391515 2088281 := bstep (se 2 (by rfl) ⟨783105, by rfl⟩ : syracuseStep 2088281 = 1566211) B1566211
theorem B1391979 : Blo 1391515 1391979 := bstep (se 1 (by rfl) ⟨1043984, by rfl⟩ : syracuseStep 1391979 = 2087969) B2087969
theorem B1391991 : Blo 1391515 1391991 := bstep (se 1 (by rfl) ⟨1043993, by rfl⟩ : syracuseStep 1391991 = 2087987) B2087987
theorem B1392011 : Blo 1391515 1392011 := bstep (se 1 (by rfl) ⟨1044008, by rfl⟩ : syracuseStep 1392011 = 2088017) B2088017
theorem B1392023 : Blo 1391515 1392023 := bstep (se 1 (by rfl) ⟨1044017, by rfl⟩ : syracuseStep 1392023 = 2088035) B2088035
theorem B1392043 : Blo 1391515 1392043 := bstep (se 1 (by rfl) ⟨1044032, by rfl⟩ : syracuseStep 1392043 = 2088065) B2088065
theorem B5430707 : Blo 1391515 5430707 := bstep (se 1 (by rfl) ⟨4073030, by rfl⟩ : syracuseStep 5430707 = 8146061) B8146061
theorem B1392055 : Blo 1391515 1392055 := bstep (se 1 (by rfl) ⟨1044041, by rfl⟩ : syracuseStep 1392055 = 2088083) B2088083
theorem B1392075 : Blo 1391515 1392075 := bstep (se 1 (by rfl) ⟨1044056, by rfl⟩ : syracuseStep 1392075 = 2088113) B2088113
theorem B2088395 : Blo 1391515 2088395 := bstep (se 1 (by rfl) ⟨1566296, by rfl⟩ : syracuseStep 2088395 = 3132593) B3132593
theorem B1392087 : Blo 1391515 1392087 := bstep (se 1 (by rfl) ⟨1044065, by rfl⟩ : syracuseStep 1392087 = 2088131) B2088131
theorem B2088407 : Blo 1391515 2088407 := bstep (se 1 (by rfl) ⟨1566305, by rfl⟩ : syracuseStep 2088407 = 3132611) B3132611
theorem B7044569 : Blo 1391515 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B1392107 : Blo 1391515 1392107 := bstep (se 1 (by rfl) ⟨1044080, by rfl⟩ : syracuseStep 1392107 = 2088161) B2088161
theorem B1392119 : Blo 1391515 1392119 := bstep (se 1 (by rfl) ⟨1044089, by rfl⟩ : syracuseStep 1392119 = 2088179) B2088179
theorem B1392139 : Blo 1391515 1392139 := bstep (se 1 (by rfl) ⟨1044104, by rfl⟩ : syracuseStep 1392139 = 2088209) B2088209
theorem B1392151 : Blo 1391515 1392151 := bstep (se 1 (by rfl) ⟨1044113, by rfl⟩ : syracuseStep 1392151 = 2088227) B2088227
theorem B3964439 : Blo 1391515 3964439 := bstep (se 1 (by rfl) ⟨2973329, by rfl⟩ : syracuseStep 3964439 = 5946659) B5946659
theorem B2088473 : Blo 1391515 2088473 := bstep (se 2 (by rfl) ⟨783177, by rfl⟩ : syracuseStep 2088473 = 1566355) B1566355
theorem B13377059 : Blo 1391515 13377059 := bstep (se 1 (by rfl) ⟨10032794, by rfl⟩ : syracuseStep 13377059 = 20065589) B20065589
theorem B1392171 : Blo 1391515 1392171 := bstep (se 1 (by rfl) ⟨1044128, by rfl⟩ : syracuseStep 1392171 = 2088257) B2088257
theorem B1392183 : Blo 1391515 1392183 := bstep (se 1 (by rfl) ⟨1044137, by rfl⟩ : syracuseStep 1392183 = 2088275) B2088275
theorem B1392203 : Blo 1391515 1392203 := bstep (se 1 (by rfl) ⟨1044152, by rfl⟩ : syracuseStep 1392203 = 2088305) B2088305
theorem B2350667 : Blo 1391515 2350667 := bstep (se 1 (by rfl) ⟨1763000, by rfl⟩ : syracuseStep 2350667 = 3526001) B3526001
theorem B1392215 : Blo 1391515 1392215 := bstep (se 1 (by rfl) ⟨1044161, by rfl⟩ : syracuseStep 1392215 = 2088323) B2088323
theorem B1392235 : Blo 1391515 1392235 := bstep (se 1 (by rfl) ⟨1044176, by rfl⟩ : syracuseStep 1392235 = 2088353) B2088353
theorem B1392247 : Blo 1391515 1392247 := bstep (se 1 (by rfl) ⟨1044185, by rfl⟩ : syracuseStep 1392247 = 2088371) B2088371
theorem B1392267 : Blo 1391515 1392267 := bstep (se 1 (by rfl) ⟨1044200, by rfl⟩ : syracuseStep 1392267 = 2088401) B2088401
theorem B2088587 : Blo 1391515 2088587 := bstep (se 1 (by rfl) ⟨1566440, by rfl⟩ : syracuseStep 2088587 = 3132881) B3132881
theorem B1392279 : Blo 1391515 1392279 := bstep (se 1 (by rfl) ⟨1044209, by rfl⟩ : syracuseStep 1392279 = 2088419) B2088419
theorem B2088599 : Blo 1391515 2088599 := bstep (se 1 (by rfl) ⟨1566449, by rfl⟩ : syracuseStep 2088599 = 3132899) B3132899
theorem B1392299 : Blo 1391515 1392299 := bstep (se 1 (by rfl) ⟨1044224, by rfl⟩ : syracuseStep 1392299 = 2088449) B2088449
theorem B1392311 : Blo 1391515 1392311 := bstep (se 1 (by rfl) ⟨1044233, by rfl⟩ : syracuseStep 1392311 = 2088467) B2088467
theorem B1392331 : Blo 1391515 1392331 := bstep (se 1 (by rfl) ⟨1044248, by rfl⟩ : syracuseStep 1392331 = 2088497) B2088497
theorem B3014347 : Blo 1391515 3014347 := bstep (se 1 (by rfl) ⟨2260760, by rfl⟩ : syracuseStep 3014347 = 4521521) B4521521
theorem B2350795 : Blo 1391515 2350795 := bstep (se 1 (by rfl) ⟨1763096, by rfl⟩ : syracuseStep 2350795 = 3526193) B3526193
theorem B1392343 : Blo 1391515 1392343 := bstep (se 1 (by rfl) ⟨1044257, by rfl⟩ : syracuseStep 1392343 = 2088515) B2088515
theorem B2088665 : Blo 1391515 2088665 := bstep (se 2 (by rfl) ⟨783249, by rfl⟩ : syracuseStep 2088665 = 1566499) B1566499
theorem B1392363 : Blo 1391515 1392363 := bstep (se 1 (by rfl) ⟨1044272, by rfl⟩ : syracuseStep 1392363 = 2088545) B2088545
theorem B1392375 : Blo 1391515 1392375 := bstep (se 1 (by rfl) ⟨1044281, by rfl⟩ : syracuseStep 1392375 = 2088563) B2088563
theorem B1392395 : Blo 1391515 1392395 := bstep (se 1 (by rfl) ⟨1044296, by rfl⟩ : syracuseStep 1392395 = 2088593) B2088593
theorem B6782737 : Blo 1391515 6782737 := bstep (se 2 (by rfl) ⟨2543526, by rfl⟩ : syracuseStep 6782737 = 5087053) B5087053
theorem B1392407 : Blo 1391515 1392407 := bstep (se 1 (by rfl) ⟨1044305, by rfl⟩ : syracuseStep 1392407 = 2088611) B2088611
theorem B1392427 : Blo 1391515 1392427 := bstep (se 1 (by rfl) ⟨1044320, by rfl⟩ : syracuseStep 1392427 = 2088641) B2088641
theorem B1392439 : Blo 1391515 1392439 := bstep (se 1 (by rfl) ⟨1044329, by rfl⟩ : syracuseStep 1392439 = 2088659) B2088659
theorem B5644097 : Blo 1391515 5644097 := bstep (se 2 (by rfl) ⟨2116536, by rfl⟩ : syracuseStep 5644097 = 4233073) B4233073
theorem B3964747 : Blo 1391515 3964747 := bstep (se 1 (by rfl) ⟨2973560, by rfl⟩ : syracuseStep 3964747 = 5947121) B5947121
theorem B1392459 : Blo 1391515 1392459 := bstep (se 1 (by rfl) ⟨1044344, by rfl⟩ : syracuseStep 1392459 = 2088689) B2088689
theorem B2088779 : Blo 1391515 2088779 := bstep (se 1 (by rfl) ⟨1566584, by rfl⟩ : syracuseStep 2088779 = 3133169) B3133169
theorem B1392471 : Blo 1391515 1392471 := bstep (se 1 (by rfl) ⟨1044353, by rfl⟩ : syracuseStep 1392471 = 2088707) B2088707
theorem B2088791 : Blo 1391515 2088791 := bstep (se 1 (by rfl) ⟨1566593, by rfl⟩ : syracuseStep 2088791 = 3133187) B3133187
theorem B2350937 : Blo 1391515 2350937 := bstep (se 2 (by rfl) ⟨881601, by rfl⟩ : syracuseStep 2350937 = 1763203) B1763203
theorem B1392491 : Blo 1391515 1392491 := bstep (se 1 (by rfl) ⟨1044368, by rfl⟩ : syracuseStep 1392491 = 2088737) B2088737
theorem B1392503 : Blo 1391515 1392503 := bstep (se 1 (by rfl) ⟨1044377, by rfl⟩ : syracuseStep 1392503 = 2088755) B2088755
theorem B1392523 : Blo 1391515 1392523 := bstep (se 1 (by rfl) ⟨1044392, by rfl⟩ : syracuseStep 1392523 = 2088785) B2088785
theorem B1392535 : Blo 1391515 1392535 := bstep (se 1 (by rfl) ⟨1044401, by rfl⟩ : syracuseStep 1392535 = 2088803) B2088803
theorem B4702103 : Blo 1391515 4702103 := bstep (se 1 (by rfl) ⟨3526577, by rfl⟩ : syracuseStep 4702103 = 7053155) B7053155
theorem B2088857 : Blo 1391515 2088857 := bstep (se 2 (by rfl) ⟨783321, by rfl⟩ : syracuseStep 2088857 = 1566643) B1566643
theorem B1392555 : Blo 1391515 1392555 := bstep (se 1 (by rfl) ⟨1044416, by rfl⟩ : syracuseStep 1392555 = 2088833) B2088833
theorem B1392567 : Blo 1391515 1392567 := bstep (se 1 (by rfl) ⟨1044425, by rfl⟩ : syracuseStep 1392567 = 2088851) B2088851
theorem B1392587 : Blo 1391515 1392587 := bstep (se 1 (by rfl) ⟨1044440, by rfl⟩ : syracuseStep 1392587 = 2088881) B2088881
theorem B1392599 : Blo 1391515 1392599 := bstep (se 1 (by rfl) ⟨1044449, by rfl⟩ : syracuseStep 1392599 = 2088899) B2088899
theorem B2351065 : Blo 1391515 2351065 := bstep (se 2 (by rfl) ⟨881649, by rfl⟩ : syracuseStep 2351065 = 1763299) B1763299
theorem B1392619 : Blo 1391515 1392619 := bstep (se 1 (by rfl) ⟨1044464, by rfl⟩ : syracuseStep 1392619 = 2088929) B2088929
theorem B1392631 : Blo 1391515 1392631 := bstep (se 1 (by rfl) ⟨1044473, by rfl⟩ : syracuseStep 1392631 = 2088947) B2088947
theorem B4022273 : Blo 1391515 4022273 := bstep (se 2 (by rfl) ⟨1508352, by rfl⟩ : syracuseStep 4022273 = 3016705) B3016705
theorem B1392647 : Blo 1391515 1392647 := bstep (se 1 (by rfl) ⟨1044485, by rfl⟩ : syracuseStep 1392647 = 2088971) B2088971
theorem B1392655 : Blo 1391515 1392655 := bstep (se 1 (by rfl) ⟨1044491, by rfl⟩ : syracuseStep 1392655 = 2088983) B2088983
theorem B2351119 : Blo 1391515 2351119 := bstep (se 1 (by rfl) ⟨1763339, by rfl⟩ : syracuseStep 2351119 = 3526679) B3526679
theorem B2203691 : Blo 1391515 2203691 := bstep (se 1 (by rfl) ⟨1652768, by rfl⟩ : syracuseStep 2203691 = 3305537) B3305537
theorem B2089019 : Blo 1391515 2089019 := bstep (se 1 (by rfl) ⟨1566764, by rfl⟩ : syracuseStep 2089019 = 3133529) B3133529
theorem B1392699 : Blo 1391515 1392699 := bstep (se 1 (by rfl) ⟨1044524, by rfl⟩ : syracuseStep 1392699 = 2089049) B2089049
theorem B2089079 : Blo 1391515 2089079 := bstep (se 1 (by rfl) ⟨1566809, by rfl⟩ : syracuseStep 2089079 = 3133619) B3133619
theorem B1392775 : Blo 1391515 1392775 := bstep (se 1 (by rfl) ⟨1044581, by rfl⟩ : syracuseStep 1392775 = 2089163) B2089163
theorem B4235399 : Blo 1391515 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B2089103 : Blo 1391515 2089103 := bstep (se 1 (by rfl) ⟨1566827, by rfl⟩ : syracuseStep 2089103 = 3133655) B3133655
theorem B1392783 : Blo 1391515 1392783 := bstep (se 1 (by rfl) ⟨1044587, by rfl⟩ : syracuseStep 1392783 = 2089175) B2089175
theorem B11894957 : Blo 1391515 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B2089145 : Blo 1391515 2089145 := bstep (se 2 (by rfl) ⟨783429, by rfl⟩ : syracuseStep 2089145 = 1566859) B1566859
theorem B1392827 : Blo 1391515 1392827 := bstep (se 1 (by rfl) ⟨1044620, by rfl⟩ : syracuseStep 1392827 = 2089241) B2089241
theorem B3522761 : Blo 1391515 3522761 := bstep (se 2 (by rfl) ⟨1321035, by rfl⟩ : syracuseStep 3522761 = 2642071) B2642071
theorem B5021933 : Blo 1391515 5021933 := bstep (se 3 (by rfl) ⟨941612, by rfl⟩ : syracuseStep 5021933 = 1883225) B1883225
theorem B1761527 : Blo 1391515 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B2089223 : Blo 1391515 2089223 := bstep (se 1 (by rfl) ⟨1566917, by rfl⟩ : syracuseStep 2089223 = 3133835) B3133835
theorem B1392903 : Blo 1391515 1392903 := bstep (se 1 (by rfl) ⟨1044677, by rfl⟩ : syracuseStep 1392903 = 2089355) B2089355
theorem B1392911 : Blo 1391515 1392911 := bstep (se 1 (by rfl) ⟨1044683, by rfl⟩ : syracuseStep 1392911 = 2089367) B2089367
theorem B3965213 : Blo 1391515 3965213 := bstep (se 3 (by rfl) ⟨743477, by rfl⟩ : syracuseStep 3965213 = 1486955) B1486955
theorem B8470817 : Blo 1391515 8470817 := bstep (se 2 (by rfl) ⟨3176556, by rfl⟩ : syracuseStep 8470817 = 6353113) B6353113
theorem B2089259 : Blo 1391515 2089259 := bstep (se 1 (by rfl) ⟨1566944, by rfl⟩ : syracuseStep 2089259 = 3133889) B3133889
theorem B1392955 : Blo 1391515 1392955 := bstep (se 1 (by rfl) ⟨1044716, by rfl⟩ : syracuseStep 1392955 = 2089433) B2089433
theorem B2089289 : Blo 1391515 2089289 := bstep (se 2 (by rfl) ⟨783483, by rfl⟩ : syracuseStep 2089289 = 1566967) B1566967
theorem B43467101 : Blo 1391515 43467101 := bstep (se 3 (by rfl) ⟨8150081, by rfl⟩ : syracuseStep 43467101 = 16300163) B16300163
theorem B1393031 : Blo 1391515 1393031 := bstep (se 1 (by rfl) ⟨1044773, by rfl⟩ : syracuseStep 1393031 = 2089547) B2089547
theorem B1761679 : Blo 1391515 1761679 := bstep (se 1 (by rfl) ⟨1321259, by rfl⟩ : syracuseStep 1761679 = 2642519) B2642519
theorem B1393039 : Blo 1391515 1393039 := bstep (se 1 (by rfl) ⟨1044779, by rfl⟩ : syracuseStep 1393039 = 2089559) B2089559
theorem B2089403 : Blo 1391515 2089403 := bstep (se 1 (by rfl) ⟨1567052, by rfl⟩ : syracuseStep 2089403 = 3134105) B3134105
theorem B1393083 : Blo 1391515 1393083 := bstep (se 1 (by rfl) ⟨1044812, by rfl⟩ : syracuseStep 1393083 = 2089625) B2089625
theorem B20079089 : Blo 1391515 20079089 := bstep (se 2 (by rfl) ⟨7529658, by rfl⟩ : syracuseStep 20079089 = 15059317) B15059317
theorem B2089463 : Blo 1391515 2089463 := bstep (se 1 (by rfl) ⟨1567097, by rfl⟩ : syracuseStep 2089463 = 3134195) B3134195
theorem B1982983 : Blo 1391515 1982983 := bstep (se 1 (by rfl) ⟨1487237, by rfl⟩ : syracuseStep 1982983 = 2974475) B2974475
theorem B1393159 : Blo 1391515 1393159 := bstep (se 1 (by rfl) ⟨1044869, by rfl⟩ : syracuseStep 1393159 = 2089739) B2089739
theorem B2089487 : Blo 1391515 2089487 := bstep (se 1 (by rfl) ⟨1567115, by rfl⟩ : syracuseStep 2089487 = 3134231) B3134231
theorem B1393167 : Blo 1391515 1393167 := bstep (se 1 (by rfl) ⟨1044875, by rfl⟩ : syracuseStep 1393167 = 2089751) B2089751
theorem B3523115 : Blo 1391515 3523115 := bstep (se 1 (by rfl) ⟨2642336, by rfl⟩ : syracuseStep 3523115 = 5284673) B5284673
theorem B2089529 : Blo 1391515 2089529 := bstep (se 2 (by rfl) ⟨783573, by rfl⟩ : syracuseStep 2089529 = 1567147) B1567147
theorem B1761851 : Blo 1391515 1761851 := bstep (se 1 (by rfl) ⟨1321388, by rfl⟩ : syracuseStep 1761851 = 2642777) B2642777
theorem B1393211 : Blo 1391515 1393211 := bstep (se 1 (by rfl) ⟨1044908, by rfl⟩ : syracuseStep 1393211 = 2089817) B2089817
theorem B5022269 : Blo 1391515 5022269 := bstep (se 3 (by rfl) ⟨941675, by rfl⟩ : syracuseStep 5022269 = 1883351) B1883351
theorem B2089607 : Blo 1391515 2089607 := bstep (se 1 (by rfl) ⟨1567205, by rfl⟩ : syracuseStep 2089607 = 3134411) B3134411
theorem B1393287 : Blo 1391515 1393287 := bstep (se 1 (by rfl) ⟨1044965, by rfl⟩ : syracuseStep 1393287 = 2089931) B2089931
theorem B1393295 : Blo 1391515 1393295 := bstep (se 1 (by rfl) ⟨1044971, by rfl⟩ : syracuseStep 1393295 = 2089943) B2089943
theorem B2089643 : Blo 1391515 2089643 := bstep (se 1 (by rfl) ⟨1567232, by rfl⟩ : syracuseStep 2089643 = 3134465) B3134465
theorem B1393339 : Blo 1391515 1393339 := bstep (se 1 (by rfl) ⟨1045004, by rfl⟩ : syracuseStep 1393339 = 2090009) B2090009
theorem B2089673 : Blo 1391515 2089673 := bstep (se 2 (by rfl) ⟨783627, by rfl⟩ : syracuseStep 2089673 = 1567255) B1567255
theorem B1393415 : Blo 1391515 1393415 := bstep (se 1 (by rfl) ⟨1045061, by rfl⟩ : syracuseStep 1393415 = 2090123) B2090123
theorem B1565455 : Blo 1391515 1565455 := bstep (se 1 (by rfl) ⟨1174091, by rfl⟩ : syracuseStep 1565455 = 2348183) B2348183
theorem B1393423 : Blo 1391515 1393423 := bstep (se 1 (by rfl) ⟨1045067, by rfl⟩ : syracuseStep 1393423 = 2090135) B2090135
theorem B7529249 : Blo 1391515 7529249 := bstep (se 2 (by rfl) ⟨2823468, by rfl⟩ : syracuseStep 7529249 = 5646937) B5646937
theorem B2089787 : Blo 1391515 2089787 := bstep (se 1 (by rfl) ⟨1567340, by rfl⟩ : syracuseStep 2089787 = 3134681) B3134681
theorem B1393467 : Blo 1391515 1393467 := bstep (se 1 (by rfl) ⟨1045100, by rfl⟩ : syracuseStep 1393467 = 2090201) B2090201
theorem B2089847 : Blo 1391515 2089847 := bstep (se 1 (by rfl) ⟨1567385, by rfl⟩ : syracuseStep 2089847 = 3134771) B3134771
theorem B2089871 : Blo 1391515 2089871 := bstep (se 1 (by rfl) ⟨1567403, by rfl⟩ : syracuseStep 2089871 = 3134807) B3134807
theorem B13747097 : Blo 1391515 13747097 := bstep (se 2 (by rfl) ⟨5155161, by rfl⟩ : syracuseStep 13747097 = 10310323) B10310323
theorem B2089913 : Blo 1391515 2089913 := bstep (se 2 (by rfl) ⟨783717, by rfl⟩ : syracuseStep 2089913 = 1567435) B1567435
theorem B3965897 : Blo 1391515 3965897 := bstep (se 2 (by rfl) ⟨1487211, by rfl⟩ : syracuseStep 3965897 = 2974423) B2974423
theorem B7054289 : Blo 1391515 7054289 := bstep (se 2 (by rfl) ⟨2645358, by rfl⟩ : syracuseStep 7054289 = 5290717) B5290717
theorem B2089991 : Blo 1391515 2089991 := bstep (se 1 (by rfl) ⟨1567493, by rfl⟩ : syracuseStep 2089991 = 3134987) B3134987
theorem B2090027 : Blo 1391515 2090027 := bstep (se 1 (by rfl) ⟨1567520, by rfl⟩ : syracuseStep 2090027 = 3135041) B3135041
theorem B2090057 : Blo 1391515 2090057 := bstep (se 2 (by rfl) ⟨783771, by rfl⟩ : syracuseStep 2090057 = 1567543) B1567543
theorem B2090171 : Blo 1391515 2090171 := bstep (se 1 (by rfl) ⟨1567628, by rfl⟩ : syracuseStep 2090171 = 3135257) B3135257
theorem B2090231 : Blo 1391515 2090231 := bstep (se 1 (by rfl) ⟨1567673, by rfl⟩ : syracuseStep 2090231 = 3135347) B3135347
theorem B1565959 : Blo 1391515 1565959 := bstep (se 1 (by rfl) ⟨1174469, by rfl⟩ : syracuseStep 1565959 = 2348939) B2348939
theorem B2090255 : Blo 1391515 2090255 := bstep (se 1 (by rfl) ⟨1567691, by rfl⟩ : syracuseStep 2090255 = 3135383) B3135383
theorem B15852833 : Blo 1391515 15852833 := bstep (se 2 (by rfl) ⟨5944812, by rfl⟩ : syracuseStep 15852833 = 11889625) B11889625
theorem B1566139 : Blo 1391515 1566139 := bstep (se 1 (by rfl) ⟨1174604, by rfl⟩ : syracuseStep 1566139 = 2349209) B2349209
theorem B1836535 : Blo 1391515 1836535 := bstep (se 1 (by rfl) ⟨1377401, by rfl⟩ : syracuseStep 1836535 = 2754803) B2754803
theorem B1762823 : Blo 1391515 1762823 := bstep (se 1 (by rfl) ⟨1322117, by rfl⟩ : syracuseStep 1762823 = 2644235) B2644235
theorem B3524107 : Blo 1391515 3524107 := bstep (se 1 (by rfl) ⟨2643080, by rfl⟩ : syracuseStep 3524107 = 5286161) B5286161
theorem B3966479 : Blo 1391515 3966479 := bstep (se 1 (by rfl) ⟨2974859, by rfl⟩ : syracuseStep 3966479 = 5949719) B5949719
theorem B3131027 : Blo 1391515 3131027 := bstep (se 1 (by rfl) ⟨2348270, by rfl⟩ : syracuseStep 3131027 = 4696541) B4696541
theorem B3524249 : Blo 1391515 3524249 := bstep (se 2 (by rfl) ⟨1321593, by rfl⟩ : syracuseStep 3524249 = 2643187) B2643187
theorem B3131081 : Blo 1391515 3131081 := bstep (se 2 (by rfl) ⟨1174155, by rfl⟩ : syracuseStep 3131081 = 2348311) B2348311
theorem B7931681 : Blo 1391515 7931681 := bstep (se 2 (by rfl) ⟨2974380, by rfl⟩ : syracuseStep 7931681 = 5948761) B5948761
theorem B3524411 : Blo 1391515 3524411 := bstep (se 1 (by rfl) ⟨2643308, by rfl⟩ : syracuseStep 3524411 = 5286617) B5286617
theorem B1566607 : Blo 1391515 1566607 := bstep (se 1 (by rfl) ⟨1174955, by rfl⟩ : syracuseStep 1566607 = 2349911) B2349911
theorem B4073591 : Blo 1391515 4073591 := bstep (se 1 (by rfl) ⟨3055193, by rfl⟩ : syracuseStep 4073591 = 6110387) B6110387
theorem B1763471 : Blo 1391515 1763471 := bstep (se 1 (by rfl) ⟨1322603, by rfl⟩ : syracuseStep 1763471 = 2645207) B2645207
theorem B3524755 : Blo 1391515 3524755 := bstep (se 1 (by rfl) ⟨2643566, by rfl⟩ : syracuseStep 3524755 = 5287133) B5287133
theorem B3524897 : Blo 1391515 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B4696379 : Blo 1391515 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B3131783 : Blo 1391515 3131783 := bstep (se 1 (by rfl) ⟨2348837, by rfl⟩ : syracuseStep 3131783 = 4697675) B4697675
theorem B1567111 : Blo 1391515 1567111 := bstep (se 1 (by rfl) ⟨1175333, by rfl⟩ : syracuseStep 1567111 = 2350667) B2350667
theorem B20089235 : Blo 1391515 20089235 := bstep (se 1 (by rfl) ⟨15066926, by rfl⟩ : syracuseStep 20089235 = 30133853) B30133853
theorem B5286329 : Blo 1391515 5286329 := bstep (se 2 (by rfl) ⟨1982373, by rfl⟩ : syracuseStep 5286329 = 3964747) B3964747
theorem B3762731 : Blo 1391515 3762731 := bstep (se 1 (by rfl) ⟨2822048, by rfl⟩ : syracuseStep 3762731 = 5644097) B5644097
theorem B3131963 : Blo 1391515 3131963 := bstep (se 1 (by rfl) ⟨2348972, by rfl⟩ : syracuseStep 3131963 = 4697945) B4697945
theorem B2230843 : Blo 1391515 2230843 := bstep (se 1 (by rfl) ⟨1673132, by rfl⟩ : syracuseStep 2230843 = 3346265) B3346265
theorem B1567291 : Blo 1391515 1567291 := bstep (se 1 (by rfl) ⟨1175468, by rfl⟩ : syracuseStep 1567291 = 2350937) B2350937
theorem B16943681 : Blo 1391515 16943681 := bstep (se 2 (by rfl) ⟨6353880, by rfl⟩ : syracuseStep 16943681 = 12707761) B12707761
theorem B7146103 : Blo 1391515 7146103 := bstep (se 1 (by rfl) ⟨5359577, by rfl⟩ : syracuseStep 7146103 = 10719155) B10719155
theorem B3132089 : Blo 1391515 3132089 := bstep (se 2 (by rfl) ⟨1174533, by rfl⟩ : syracuseStep 3132089 = 2349067) B2349067
theorem B4696865 : Blo 1391515 4696865 := bstep (se 2 (by rfl) ⟨1761324, by rfl⟩ : syracuseStep 4696865 = 3522649) B3522649
theorem B3967879 : Blo 1391515 3967879 := bstep (se 1 (by rfl) ⟨2975909, by rfl⟩ : syracuseStep 3967879 = 5951819) B5951819
theorem B20073379 : Blo 1391515 20073379 := bstep (se 1 (by rfl) ⟨15055034, by rfl⟩ : syracuseStep 20073379 = 30110069) B30110069
theorem B5950417 : Blo 1391515 5950417 := bstep (se 2 (by rfl) ⟨2231406, by rfl⟩ : syracuseStep 5950417 = 4462813) B4462813
theorem B3132431 : Blo 1391515 3132431 := bstep (se 1 (by rfl) ⟨2349323, by rfl⟩ : syracuseStep 3132431 = 4698647) B4698647
theorem B3132449 : Blo 1391515 3132449 := bstep (se 2 (by rfl) ⟨1174668, by rfl⟩ : syracuseStep 3132449 = 2349337) B2349337
theorem B16067645 : Blo 1391515 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B3968153 : Blo 1391515 3968153 := bstep (se 2 (by rfl) ⟨1488057, by rfl⟩ : syracuseStep 3968153 = 2976115) B2976115
theorem B3525889 : Blo 1391515 3525889 := bstep (se 2 (by rfl) ⟨1322208, by rfl⟩ : syracuseStep 3525889 = 2644417) B2644417
theorem B4697459 : Blo 1391515 4697459 := bstep (se 1 (by rfl) ⟨3523094, by rfl⟩ : syracuseStep 4697459 = 7046189) B7046189
theorem B3132791 : Blo 1391515 3132791 := bstep (se 1 (by rfl) ⟨2349593, by rfl⟩ : syracuseStep 3132791 = 4699187) B4699187
theorem B2116999 : Blo 1391515 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B5287315 : Blo 1391515 5287315 := bstep (se 1 (by rfl) ⟨3965486, by rfl⟩ : syracuseStep 5287315 = 7930973) B7930973
theorem B19590605 : Blo 1391515 19590605 := bstep (se 3 (by rfl) ⟨3673238, by rfl⟩ : syracuseStep 19590605 = 7346477) B7346477
theorem B3132971 : Blo 1391515 3132971 := bstep (se 1 (by rfl) ⟨2349728, by rfl⟩ : syracuseStep 3132971 = 4699457) B4699457
theorem B3346073 : Blo 1391515 3346073 := bstep (se 2 (by rfl) ⟨1254777, by rfl⟩ : syracuseStep 3346073 = 2509555) B2509555
theorem B3764029 : Blo 1391515 3764029 := bstep (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) B1411511
theorem B3526487 : Blo 1391515 3526487 := bstep (se 1 (by rfl) ⟨2644865, by rfl⟩ : syracuseStep 3526487 = 5289731) B5289731
theorem B12701555 : Blo 1391515 12701555 := bstep (se 1 (by rfl) ⟨9526166, by rfl⟩ : syracuseStep 12701555 = 19052333) B19052333
theorem B7049105 : Blo 1391515 7049105 := bstep (se 2 (by rfl) ⟨2643414, by rfl⟩ : syracuseStep 7049105 = 5286829) B5286829
theorem B3133331 : Blo 1391515 3133331 := bstep (se 1 (by rfl) ⟨2349998, by rfl⟩ : syracuseStep 3133331 = 4699997) B4699997
theorem B152457137 : Blo 1391515 152457137 := bstep (se 2 (by rfl) ⟨57171426, by rfl⟩ : syracuseStep 152457137 = 114342853) B114342853
theorem B3346361 : Blo 1391515 3346361 := bstep (se 2 (by rfl) ⟨1254885, by rfl⟩ : syracuseStep 3346361 = 2509771) B2509771
theorem B3133385 : Blo 1391515 3133385 := bstep (se 2 (by rfl) ⟨1175019, by rfl⟩ : syracuseStep 3133385 = 2350039) B2350039
theorem B28987409 : Blo 1391515 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B7737367 : Blo 1391515 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B3526699 : Blo 1391515 3526699 := bstep (se 1 (by rfl) ⟨2645024, by rfl⟩ : syracuseStep 3526699 = 5290049) B5290049
theorem B4763767 : Blo 1391515 4763767 := bstep (se 1 (by rfl) ⟨3572825, by rfl⟩ : syracuseStep 4763767 = 7145651) B7145651
theorem B7934071 : Blo 1391515 7934071 := bstep (se 1 (by rfl) ⟨5950553, by rfl⟩ : syracuseStep 7934071 = 11901107) B11901107
theorem B15855749 : Blo 1391515 15855749 := bstep (se 4 (by rfl) ⟨1486476, by rfl⟩ : syracuseStep 15855749 = 2972953) B2972953
theorem B3526841 : Blo 1391515 3526841 := bstep (se 2 (by rfl) ⟨1322565, by rfl⟩ : syracuseStep 3526841 = 2645131) B2645131
theorem B247410929 : Blo 1391515 247410929 := bstep (se 2 (by rfl) ⟨92779098, by rfl⟩ : syracuseStep 247410929 = 185558197) B185558197
theorem B6779321 : Blo 1391515 6779321 := bstep (se 2 (by rfl) ⟨2542245, by rfl⟩ : syracuseStep 6779321 = 5084491) B5084491
theorem B2118089 : Blo 1391515 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B1430023 : Blo 1391515 1430023 := bstep (se 1 (by rfl) ⟨1072517, by rfl⟩ : syracuseStep 1430023 = 2145035) B2145035
theorem B3134087 : Blo 1391515 3134087 := bstep (se 1 (by rfl) ⟨2350565, by rfl⟩ : syracuseStep 3134087 = 4701131) B4701131
theorem B15864497 : Blo 1391515 15864497 := bstep (se 2 (by rfl) ⟨5949186, by rfl⟩ : syracuseStep 15864497 = 11898373) B11898373
theorem B1880761 : Blo 1391515 1880761 := bstep (se 2 (by rfl) ⟨705285, by rfl⟩ : syracuseStep 1880761 = 1410571) B1410571
theorem B3175097 : Blo 1391515 3175097 := bstep (se 2 (by rfl) ⟨1190661, by rfl⟩ : syracuseStep 3175097 = 2381323) B2381323
theorem B3134267 : Blo 1391515 3134267 := bstep (se 1 (by rfl) ⟨2350700, by rfl⟩ : syracuseStep 3134267 = 4701401) B4701401
theorem B2642807 : Blo 1391515 2642807 := bstep (se 1 (by rfl) ⟨1982105, by rfl⟩ : syracuseStep 2642807 = 3964211) B3964211
theorem B11891609 : Blo 1391515 11891609 := bstep (se 2 (by rfl) ⟨4459353, by rfl⟩ : syracuseStep 11891609 = 8918707) B8918707
theorem B4019129 : Blo 1391515 4019129 := bstep (se 2 (by rfl) ⟨1507173, by rfl⟩ : syracuseStep 4019129 = 3014347) B3014347
theorem B3134393 : Blo 1391515 3134393 := bstep (se 2 (by rfl) ⟨1175397, by rfl⟩ : syracuseStep 3134393 = 2350795) B2350795
theorem B3814411 : Blo 1391515 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B2642959 : Blo 1391515 2642959 := bstep (se 1 (by rfl) ⟨1982219, by rfl⟩ : syracuseStep 2642959 = 3964439) B3964439
theorem B8918039 : Blo 1391515 8918039 := bstep (se 1 (by rfl) ⟨6688529, by rfl⟩ : syracuseStep 8918039 = 13377059) B13377059
theorem B1881145 : Blo 1391515 1881145 := bstep (se 2 (by rfl) ⟨705429, by rfl⟩ : syracuseStep 1881145 = 1410859) B1410859
theorem B10040381 : Blo 1391515 10040381 := bstep (se 3 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 10040381 = 3765143) B3765143
theorem B5944387 : Blo 1391515 5944387 := bstep (se 1 (by rfl) ⟨4458290, by rfl⟩ : syracuseStep 5944387 = 8916581) B8916581
theorem B5289047 : Blo 1391515 5289047 := bstep (se 1 (by rfl) ⟨3966785, by rfl⟩ : syracuseStep 5289047 = 7933571) B7933571
theorem B7927055 : Blo 1391515 7927055 := bstep (se 1 (by rfl) ⟨5945291, by rfl⟩ : syracuseStep 7927055 = 11890583) B11890583
theorem B3134735 : Blo 1391515 3134735 := bstep (se 1 (by rfl) ⟨2351051, by rfl⟩ : syracuseStep 3134735 = 4702103) B4702103
theorem B3134753 : Blo 1391515 3134753 := bstep (se 2 (by rfl) ⟨1175532, by rfl⟩ : syracuseStep 3134753 = 2351065) B2351065
theorem B7935347 : Blo 1391515 7935347 := bstep (se 1 (by rfl) ⟨5951510, by rfl⟩ : syracuseStep 7935347 = 11903021) B11903021
theorem B5944711 : Blo 1391515 5944711 := bstep (se 1 (by rfl) ⟨4458533, by rfl⟩ : syracuseStep 5944711 = 8917067) B8917067
theorem B2643347 : Blo 1391515 2643347 := bstep (se 1 (by rfl) ⟨1982510, by rfl⟩ : syracuseStep 2643347 = 3965021) B3965021
theorem B2348473 : Blo 1391515 2348473 := bstep (se 2 (by rfl) ⟨880677, by rfl⟩ : syracuseStep 2348473 = 1761355) B1761355
theorem B8467897 : Blo 1391515 8467897 := bstep (se 2 (by rfl) ⟨3175461, by rfl⟩ : syracuseStep 8467897 = 6350923) B6350923
theorem B7927307 : Blo 1391515 7927307 := bstep (se 1 (by rfl) ⟨5945480, by rfl⟩ : syracuseStep 7927307 = 11890961) B11890961
theorem B5289533 : Blo 1391515 5289533 := bstep (se 3 (by rfl) ⟨991787, by rfl⟩ : syracuseStep 5289533 = 1983575) B1983575
theorem B4462199 : Blo 1391515 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B3135095 : Blo 1391515 3135095 := bstep (se 1 (by rfl) ⟨2351321, by rfl⟩ : syracuseStep 3135095 = 4702643) B4702643
theorem B2381447 : Blo 1391515 2381447 := bstep (se 1 (by rfl) ⟨1786085, by rfl⟩ : syracuseStep 2381447 = 3572171) B3572171
theorem B3135275 : Blo 1391515 3135275 := bstep (se 1 (by rfl) ⟨2351456, by rfl⟩ : syracuseStep 3135275 = 4702913) B4702913
theorem B7935803 : Blo 1391515 7935803 := bstep (se 1 (by rfl) ⟨5951852, by rfl⟩ : syracuseStep 7935803 = 11903705) B11903705
theorem B7632785 : Blo 1391515 7632785 := bstep (se 2 (by rfl) ⟨2862294, by rfl⟩ : syracuseStep 7632785 = 5724589) B5724589
theorem B4700051 : Blo 1391515 4700051 := bstep (se 1 (by rfl) ⟨3525038, by rfl⟩ : syracuseStep 4700051 = 7050077) B7050077
theorem B7051211 : Blo 1391515 7051211 := bstep (se 1 (by rfl) ⟨5288408, by rfl⟩ : syracuseStep 7051211 = 10576817) B10576817
theorem B8927243 : Blo 1391515 8927243 := bstep (se 1 (by rfl) ⟨6695432, by rfl⟩ : syracuseStep 8927243 = 13390865) B13390865
theorem B52181015 : Blo 1391515 52181015 := bstep (se 1 (by rfl) ⟨39135761, by rfl⟩ : syracuseStep 52181015 = 78271523) B78271523
theorem B2349175 : Blo 1391515 2349175 := bstep (se 1 (by rfl) ⟨1761881, by rfl⟩ : syracuseStep 2349175 = 3523763) B3523763
theorem B8042689 : Blo 1391515 8042689 := bstep (se 2 (by rfl) ⟨3016008, by rfl⟩ : syracuseStep 8042689 = 6032017) B6032017
theorem B7051535 : Blo 1391515 7051535 := bstep (se 1 (by rfl) ⟨5288651, by rfl⟩ : syracuseStep 7051535 = 10577303) B10577303
theorem B5945633 : Blo 1391515 5945633 := bstep (se 2 (by rfl) ⟨2229612, by rfl⟩ : syracuseStep 5945633 = 4459225) B4459225
theorem B4765985 : Blo 1391515 4765985 := bstep (se 2 (by rfl) ⟨1787244, by rfl⟩ : syracuseStep 4765985 = 3574489) B3574489
theorem B2349371 : Blo 1391515 2349371 := bstep (se 1 (by rfl) ⟨1762028, by rfl⟩ : syracuseStep 2349371 = 3524057) B3524057
theorem B2382139 : Blo 1391515 2382139 := bstep (se 1 (by rfl) ⟨1786604, by rfl⟩ : syracuseStep 2382139 = 3573209) B3573209
theorem B2824507 : Blo 1391515 2824507 := bstep (se 1 (by rfl) ⟨2118380, by rfl⟩ : syracuseStep 2824507 = 4236761) B4236761
theorem B2087303 : Blo 1391515 2087303 := bstep (se 1 (by rfl) ⟨1565477, by rfl⟩ : syracuseStep 2087303 = 3130955) B3130955
theorem B3963289 : Blo 1391515 3963289 := bstep (se 2 (by rfl) ⟨1486233, by rfl⟩ : syracuseStep 3963289 = 2972467) B2972467
theorem B2087339 : Blo 1391515 2087339 := bstep (se 1 (by rfl) ⟨1565504, by rfl⟩ : syracuseStep 2087339 = 3131009) B3131009
theorem B2087369 : Blo 1391515 2087369 := bstep (se 2 (by rfl) ⟨782763, by rfl⟩ : syracuseStep 2087369 = 1565527) B1565527
theorem B2087483 : Blo 1391515 2087483 := bstep (se 1 (by rfl) ⟨1565612, by rfl⟩ : syracuseStep 2087483 = 3131225) B3131225
theorem B2087543 : Blo 1391515 2087543 := bstep (se 1 (by rfl) ⟨1565657, by rfl⟩ : syracuseStep 2087543 = 3131315) B3131315
theorem B2087567 : Blo 1391515 2087567 := bstep (se 1 (by rfl) ⟨1565675, by rfl⟩ : syracuseStep 2087567 = 3131351) B3131351
theorem B2087609 : Blo 1391515 2087609 := bstep (se 2 (by rfl) ⟨782853, by rfl⟩ : syracuseStep 2087609 = 1565707) B1565707
theorem B7928513 : Blo 1391515 7928513 := bstep (se 2 (by rfl) ⟨2973192, by rfl⟩ : syracuseStep 7928513 = 5946385) B5946385
theorem B2349769 : Blo 1391515 2349769 := bstep (se 2 (by rfl) ⟨881163, by rfl⟩ : syracuseStep 2349769 = 1762327) B1762327
theorem B2087687 : Blo 1391515 2087687 := bstep (se 1 (by rfl) ⟨1565765, by rfl⟩ : syracuseStep 2087687 = 3131531) B3131531
theorem B2644751 : Blo 1391515 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B2087723 : Blo 1391515 2087723 := bstep (se 1 (by rfl) ⟨1565792, by rfl⟩ : syracuseStep 2087723 = 3131585) B3131585
theorem B2087753 : Blo 1391515 2087753 := bstep (se 2 (by rfl) ⟨782907, by rfl⟩ : syracuseStep 2087753 = 1565815) B1565815
theorem B1391547 : Blo 1391515 1391547 := bstep (se 1 (by rfl) ⟨1043660, by rfl⟩ : syracuseStep 1391547 = 2087321) B2087321
theorem B2087867 : Blo 1391515 2087867 := bstep (se 1 (by rfl) ⟨1565900, by rfl⟩ : syracuseStep 2087867 = 3131801) B3131801
theorem B2087927 : Blo 1391515 2087927 := bstep (se 1 (by rfl) ⟨1565945, by rfl⟩ : syracuseStep 2087927 = 3131891) B3131891
theorem B1391623 : Blo 1391515 1391623 := bstep (se 1 (by rfl) ⟨1043717, by rfl⟩ : syracuseStep 1391623 = 2087435) B2087435
theorem B1391631 : Blo 1391515 1391631 := bstep (se 1 (by rfl) ⟨1043723, by rfl⟩ : syracuseStep 1391631 = 2087447) B2087447
theorem B2087951 : Blo 1391515 2087951 := bstep (se 1 (by rfl) ⟨1565963, by rfl⟩ : syracuseStep 2087951 = 3131927) B3131927
theorem B2087993 : Blo 1391515 2087993 := bstep (se 2 (by rfl) ⟨782997, by rfl⟩ : syracuseStep 2087993 = 1565995) B1565995
theorem B1391675 : Blo 1391515 1391675 := bstep (se 1 (by rfl) ⟨1043756, by rfl⟩ : syracuseStep 1391675 = 2087513) B2087513
theorem B1981513 : Blo 1391515 1981513 := bstep (se 2 (by rfl) ⟨743067, by rfl⟩ : syracuseStep 1981513 = 1486135) B1486135
theorem B1391751 : Blo 1391515 1391751 := bstep (se 1 (by rfl) ⟨1043813, by rfl⟩ : syracuseStep 1391751 = 2087627) B2087627
theorem B2088071 : Blo 1391515 2088071 := bstep (se 1 (by rfl) ⟨1566053, by rfl⟩ : syracuseStep 2088071 = 3132107) B3132107
theorem B1391759 : Blo 1391515 1391759 := bstep (se 1 (by rfl) ⟨1043819, by rfl⟩ : syracuseStep 1391759 = 2087639) B2087639
theorem B2088107 : Blo 1391515 2088107 := bstep (se 1 (by rfl) ⟨1566080, by rfl⟩ : syracuseStep 2088107 = 3132161) B3132161
theorem B1391803 : Blo 1391515 1391803 := bstep (se 1 (by rfl) ⟨1043852, by rfl⟩ : syracuseStep 1391803 = 2087705) B2087705
theorem B2088137 : Blo 1391515 2088137 := bstep (se 2 (by rfl) ⟨783051, by rfl⟩ : syracuseStep 2088137 = 1566103) B1566103
theorem B1391879 : Blo 1391515 1391879 := bstep (se 1 (by rfl) ⟨1043909, by rfl⟩ : syracuseStep 1391879 = 2087819) B2087819
theorem B1391887 : Blo 1391515 1391887 := bstep (se 1 (by rfl) ⟨1043915, by rfl⟩ : syracuseStep 1391887 = 2087831) B2087831
theorem B4701455 : Blo 1391515 4701455 := bstep (se 1 (by rfl) ⟨3526091, by rfl⟩ : syracuseStep 4701455 = 7052183) B7052183
theorem B2645291 : Blo 1391515 2645291 := bstep (se 1 (by rfl) ⟨1983968, by rfl⟩ : syracuseStep 2645291 = 3967937) B3967937
theorem B7626035 : Blo 1391515 7626035 := bstep (se 1 (by rfl) ⟨5719526, by rfl⟩ : syracuseStep 7626035 = 11439053) B11439053
theorem B1391931 : Blo 1391515 1391931 := bstep (se 1 (by rfl) ⟨1043948, by rfl⟩ : syracuseStep 1391931 = 2087897) B2087897
theorem B2088251 : Blo 1391515 2088251 := bstep (se 1 (by rfl) ⟨1566188, by rfl⟩ : syracuseStep 2088251 = 3132377) B3132377
theorem B2088311 : Blo 1391515 2088311 := bstep (se 1 (by rfl) ⟨1566233, by rfl⟩ : syracuseStep 2088311 = 3132467) B3132467
theorem B19045763 : Blo 1391515 19045763 := bstep (se 1 (by rfl) ⟨14284322, by rfl⟩ : syracuseStep 19045763 = 28568645) B28568645
theorem B1392007 : Blo 1391515 1392007 := bstep (se 1 (by rfl) ⟨1044005, by rfl⟩ : syracuseStep 1392007 = 2088011) B2088011
theorem B2350471 : Blo 1391515 2350471 := bstep (se 1 (by rfl) ⟨1762853, by rfl⟩ : syracuseStep 2350471 = 3525707) B3525707
theorem B1392015 : Blo 1391515 1392015 := bstep (se 1 (by rfl) ⟨1044011, by rfl⟩ : syracuseStep 1392015 = 2088023) B2088023
theorem B2088335 : Blo 1391515 2088335 := bstep (se 1 (by rfl) ⟨1566251, by rfl⟩ : syracuseStep 2088335 = 3132503) B3132503
theorem B10567097 : Blo 1391515 10567097 := bstep (se 2 (by rfl) ⟨3962661, by rfl⟩ : syracuseStep 10567097 = 7925323) B7925323
theorem B2088377 : Blo 1391515 2088377 := bstep (se 2 (by rfl) ⟨783141, by rfl⟩ : syracuseStep 2088377 = 1566283) B1566283
theorem B1392059 : Blo 1391515 1392059 := bstep (se 1 (by rfl) ⟨1044044, by rfl⟩ : syracuseStep 1392059 = 2088089) B2088089
theorem B1392135 : Blo 1391515 1392135 := bstep (se 1 (by rfl) ⟨1044101, by rfl⟩ : syracuseStep 1392135 = 2088203) B2088203
theorem B2088455 : Blo 1391515 2088455 := bstep (se 1 (by rfl) ⟨1566341, by rfl⟩ : syracuseStep 2088455 = 3132683) B3132683
theorem B1392143 : Blo 1391515 1392143 := bstep (se 1 (by rfl) ⟨1044107, by rfl⟩ : syracuseStep 1392143 = 2088215) B2088215
theorem B6692375 : Blo 1391515 6692375 := bstep (se 1 (by rfl) ⟨5019281, by rfl⟩ : syracuseStep 6692375 = 10038563) B10038563
theorem B4701725 : Blo 1391515 4701725 := bstep (se 3 (by rfl) ⟨881573, by rfl⟩ : syracuseStep 4701725 = 1763147) B1763147
theorem B2088491 : Blo 1391515 2088491 := bstep (se 1 (by rfl) ⟨1566368, by rfl⟩ : syracuseStep 2088491 = 3132737) B3132737
theorem B1982009 : Blo 1391515 1982009 := bstep (se 2 (by rfl) ⟨743253, by rfl⟩ : syracuseStep 1982009 = 1486507) B1486507
theorem B1392187 : Blo 1391515 1392187 := bstep (se 1 (by rfl) ⟨1044140, by rfl⟩ : syracuseStep 1392187 = 2088281) B2088281
theorem B2088521 : Blo 1391515 2088521 := bstep (se 2 (by rfl) ⟨783195, by rfl⟩ : syracuseStep 2088521 = 1566391) B1566391
theorem B3620471 : Blo 1391515 3620471 := bstep (se 1 (by rfl) ⟨2715353, by rfl⟩ : syracuseStep 3620471 = 5430707) B5430707
theorem B1392263 : Blo 1391515 1392263 := bstep (se 1 (by rfl) ⟨1044197, by rfl⟩ : syracuseStep 1392263 = 2088395) B2088395
theorem B1392271 : Blo 1391515 1392271 := bstep (se 1 (by rfl) ⟨1044203, by rfl⟩ : syracuseStep 1392271 = 2088407) B2088407
theorem B1392315 : Blo 1391515 1392315 := bstep (se 1 (by rfl) ⟨1044236, by rfl⟩ : syracuseStep 1392315 = 2088473) B2088473
theorem B2088635 : Blo 1391515 2088635 := bstep (se 1 (by rfl) ⟨1566476, by rfl⟩ : syracuseStep 2088635 = 3132953) B3132953
theorem B9043649 : Blo 1391515 9043649 := bstep (se 2 (by rfl) ⟨3391368, by rfl⟩ : syracuseStep 9043649 = 6782737) B6782737
theorem B7052993 : Blo 1391515 7052993 := bstep (se 2 (by rfl) ⟨2644872, by rfl⟩ : syracuseStep 7052993 = 5289745) B5289745
theorem B12066497 : Blo 1391515 12066497 := bstep (se 2 (by rfl) ⟨4524936, by rfl⟩ : syracuseStep 12066497 = 9049873) B9049873
theorem B2088695 : Blo 1391515 2088695 := bstep (se 1 (by rfl) ⟨1566521, by rfl⟩ : syracuseStep 2088695 = 3133043) B3133043
theorem B3522305 : Blo 1391515 3522305 := bstep (se 2 (by rfl) ⟨1320864, by rfl⟩ : syracuseStep 3522305 = 2641729) B2641729
theorem B1392391 : Blo 1391515 1392391 := bstep (se 1 (by rfl) ⟨1044293, by rfl⟩ : syracuseStep 1392391 = 2088587) B2088587
theorem B1392399 : Blo 1391515 1392399 := bstep (se 1 (by rfl) ⟨1044299, by rfl⟩ : syracuseStep 1392399 = 2088599) B2088599
theorem B2088719 : Blo 1391515 2088719 := bstep (se 1 (by rfl) ⟨1566539, by rfl⟩ : syracuseStep 2088719 = 3133079) B3133079
theorem B2088761 : Blo 1391515 2088761 := bstep (se 2 (by rfl) ⟨783285, by rfl⟩ : syracuseStep 2088761 = 1566571) B1566571
theorem B1392443 : Blo 1391515 1392443 := bstep (se 1 (by rfl) ⟨1044332, by rfl⟩ : syracuseStep 1392443 = 2088665) B2088665
theorem B1392519 : Blo 1391515 1392519 := bstep (se 1 (by rfl) ⟨1044389, by rfl⟩ : syracuseStep 1392519 = 2088779) B2088779
theorem B2088839 : Blo 1391515 2088839 := bstep (se 1 (by rfl) ⟨1566629, by rfl⟩ : syracuseStep 2088839 = 3133259) B3133259
theorem B1392527 : Blo 1391515 1392527 := bstep (se 1 (by rfl) ⟨1044395, by rfl⟩ : syracuseStep 1392527 = 2088791) B2088791
theorem B5283731 : Blo 1391515 5283731 := bstep (se 1 (by rfl) ⟨3962798, by rfl⟩ : syracuseStep 5283731 = 7925597) B7925597
theorem B2088875 : Blo 1391515 2088875 := bstep (se 1 (by rfl) ⟨1566656, by rfl⟩ : syracuseStep 2088875 = 3133313) B3133313
theorem B1392571 : Blo 1391515 1392571 := bstep (se 1 (by rfl) ⟨1044428, by rfl⟩ : syracuseStep 1392571 = 2088857) B2088857
theorem B2088905 : Blo 1391515 2088905 := bstep (se 2 (by rfl) ⟨783339, by rfl⟩ : syracuseStep 2088905 = 1566679) B1566679
theorem B1392679 : Blo 1391515 1392679 := bstep (se 1 (by rfl) ⟨1044509, by rfl⟩ : syracuseStep 1392679 = 2089019) B2089019
theorem B77299757 : Blo 1391515 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B4702265 : Blo 1391515 4702265 := bstep (se 2 (by rfl) ⟨1763349, by rfl⟩ : syracuseStep 4702265 = 3526699) B3526699
theorem B23781437 : Blo 1391515 23781437 := bstep (se 3 (by rfl) ⟨4459019, by rfl⟩ : syracuseStep 23781437 = 8918039) B8918039
theorem B1392719 : Blo 1391515 1392719 := bstep (se 1 (by rfl) ⟨1044539, by rfl⟩ : syracuseStep 1392719 = 2089079) B2089079
theorem B1392735 : Blo 1391515 1392735 := bstep (se 1 (by rfl) ⟨1044551, by rfl⟩ : syracuseStep 1392735 = 2089103) B2089103
theorem B7929971 : Blo 1391515 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B1392763 : Blo 1391515 1392763 := bstep (se 1 (by rfl) ⟨1044572, by rfl⟩ : syracuseStep 1392763 = 2089145) B2089145
theorem B2351227 : Blo 1391515 2351227 := bstep (se 1 (by rfl) ⟨1763420, by rfl⟩ : syracuseStep 2351227 = 3526841) B3526841
theorem B1392815 : Blo 1391515 1392815 := bstep (se 1 (by rfl) ⟨1044611, by rfl⟩ : syracuseStep 1392815 = 2089223) B2089223
theorem B1392839 : Blo 1391515 1392839 := bstep (se 1 (by rfl) ⟨1044629, by rfl⟩ : syracuseStep 1392839 = 2089259) B2089259
theorem B1392859 : Blo 1391515 1392859 := bstep (se 1 (by rfl) ⟨1044644, by rfl⟩ : syracuseStep 1392859 = 2089289) B2089289
theorem B556597493 : Blo 1391515 556597493 := bstep (se 5 (by rfl) ⟨26090507, by rfl⟩ : syracuseStep 556597493 = 52181015) B52181015
theorem B10723585 : Blo 1391515 10723585 := bstep (se 2 (by rfl) ⟨4021344, by rfl⟩ : syracuseStep 10723585 = 8042689) B8042689
theorem B1392935 : Blo 1391515 1392935 := bstep (se 1 (by rfl) ⟨1044701, by rfl⟩ : syracuseStep 1392935 = 2089403) B2089403
theorem B13386059 : Blo 1391515 13386059 := bstep (se 1 (by rfl) ⟨10039544, by rfl⟩ : syracuseStep 13386059 = 20079089) B20079089
theorem B1392975 : Blo 1391515 1392975 := bstep (se 1 (by rfl) ⟨1044731, by rfl⟩ : syracuseStep 1392975 = 2089463) B2089463
theorem B1392991 : Blo 1391515 1392991 := bstep (se 1 (by rfl) ⟨1044743, by rfl⟩ : syracuseStep 1392991 = 2089487) B2089487
theorem B1393019 : Blo 1391515 1393019 := bstep (se 1 (by rfl) ⟨1044764, by rfl⟩ : syracuseStep 1393019 = 2089529) B2089529
theorem B4702589 : Blo 1391515 4702589 := bstep (se 3 (by rfl) ⟨881735, by rfl⟩ : syracuseStep 4702589 = 1763471) B1763471
theorem B10568069 : Blo 1391515 10568069 := bstep (se 4 (by rfl) ⟨990756, by rfl⟩ : syracuseStep 10568069 = 1981513) B1981513
theorem B2089391 : Blo 1391515 2089391 := bstep (se 1 (by rfl) ⟨1567043, by rfl⟩ : syracuseStep 2089391 = 3134087) B3134087
theorem B1393071 : Blo 1391515 1393071 := bstep (se 1 (by rfl) ⟨1044803, by rfl⟩ : syracuseStep 1393071 = 2089607) B2089607
theorem B1393095 : Blo 1391515 1393095 := bstep (se 1 (by rfl) ⟨1044821, by rfl⟩ : syracuseStep 1393095 = 2089643) B2089643
theorem B10576331 : Blo 1391515 10576331 := bstep (se 1 (by rfl) ⟨7932248, by rfl⟩ : syracuseStep 10576331 = 15864497) B15864497
theorem B1393115 : Blo 1391515 1393115 := bstep (se 1 (by rfl) ⟨1044836, by rfl⟩ : syracuseStep 1393115 = 2089673) B2089673
theorem B2089481 : Blo 1391515 2089481 := bstep (se 2 (by rfl) ⟨783555, by rfl⟩ : syracuseStep 2089481 = 1567111) B1567111
theorem B5284385 : Blo 1391515 5284385 := bstep (se 2 (by rfl) ⟨1981644, by rfl⟩ : syracuseStep 5284385 = 3963289) B3963289
theorem B2089511 : Blo 1391515 2089511 := bstep (se 1 (by rfl) ⟨1567133, by rfl⟩ : syracuseStep 2089511 = 3134267) B3134267
theorem B1393191 : Blo 1391515 1393191 := bstep (se 1 (by rfl) ⟨1044893, by rfl⟩ : syracuseStep 1393191 = 2089787) B2089787
theorem B1393231 : Blo 1391515 1393231 := bstep (se 1 (by rfl) ⟨1044923, by rfl⟩ : syracuseStep 1393231 = 2089847) B2089847
theorem B1393247 : Blo 1391515 1393247 := bstep (se 1 (by rfl) ⟨1044935, by rfl⟩ : syracuseStep 1393247 = 2089871) B2089871
theorem B2679419 : Blo 1391515 2679419 := bstep (se 1 (by rfl) ⟨2009564, by rfl⟩ : syracuseStep 2679419 = 4019129) B4019129
theorem B2089595 : Blo 1391515 2089595 := bstep (se 1 (by rfl) ⟨1567196, by rfl⟩ : syracuseStep 2089595 = 3134393) B3134393
theorem B1393275 : Blo 1391515 1393275 := bstep (se 1 (by rfl) ⟨1044956, by rfl⟩ : syracuseStep 1393275 = 2089913) B2089913
theorem B4702859 : Blo 1391515 4702859 := bstep (se 1 (by rfl) ⟨3527144, by rfl⟩ : syracuseStep 4702859 = 7054289) B7054289
theorem B1393327 : Blo 1391515 1393327 := bstep (se 1 (by rfl) ⟨1044995, by rfl⟩ : syracuseStep 1393327 = 2089991) B2089991
theorem B1393351 : Blo 1391515 1393351 := bstep (se 1 (by rfl) ⟨1045013, by rfl⟩ : syracuseStep 1393351 = 2090027) B2090027
theorem B6693587 : Blo 1391515 6693587 := bstep (se 1 (by rfl) ⟨5020190, by rfl⟩ : syracuseStep 6693587 = 10040381) B10040381
theorem B1393371 : Blo 1391515 1393371 := bstep (se 1 (by rfl) ⟨1045028, by rfl⟩ : syracuseStep 1393371 = 2090057) B2090057
theorem B2974457 : Blo 1391515 2974457 := bstep (se 2 (by rfl) ⟨1115421, by rfl⟩ : syracuseStep 2974457 = 2230843) B2230843
theorem B2089721 : Blo 1391515 2089721 := bstep (se 2 (by rfl) ⟨783645, by rfl⟩ : syracuseStep 2089721 = 1567291) B1567291
theorem B1393447 : Blo 1391515 1393447 := bstep (se 1 (by rfl) ⟨1045085, by rfl⟩ : syracuseStep 1393447 = 2090171) B2090171
theorem B9528137 : Blo 1391515 9528137 := bstep (se 2 (by rfl) ⟨3573051, by rfl⟩ : syracuseStep 9528137 = 7146103) B7146103
theorem B1393487 : Blo 1391515 1393487 := bstep (se 1 (by rfl) ⟨1045115, by rfl⟩ : syracuseStep 1393487 = 2090231) B2090231
theorem B5284703 : Blo 1391515 5284703 := bstep (se 1 (by rfl) ⟨3963527, by rfl⟩ : syracuseStep 5284703 = 7927055) B7927055
theorem B2089823 : Blo 1391515 2089823 := bstep (se 1 (by rfl) ⟨1567367, by rfl⟩ : syracuseStep 2089823 = 3134735) B3134735
theorem B1393503 : Blo 1391515 1393503 := bstep (se 1 (by rfl) ⟨1045127, by rfl⟩ : syracuseStep 1393503 = 2090255) B2090255
theorem B10568555 : Blo 1391515 10568555 := bstep (se 1 (by rfl) ⟨7926416, by rfl⟩ : syracuseStep 10568555 = 15852833) B15852833
theorem B2089835 : Blo 1391515 2089835 := bstep (se 1 (by rfl) ⟨1567376, by rfl⟩ : syracuseStep 2089835 = 3134753) B3134753
theorem B2507681 : Blo 1391515 2507681 := bstep (se 2 (by rfl) ⟨940380, by rfl⟩ : syracuseStep 2507681 = 1880761) B1880761
theorem B1762231 : Blo 1391515 1762231 := bstep (se 1 (by rfl) ⟨1321673, by rfl⟩ : syracuseStep 1762231 = 2643347) B2643347
theorem B5284871 : Blo 1391515 5284871 := bstep (se 1 (by rfl) ⟨3963653, by rfl⟩ : syracuseStep 5284871 = 7927307) B7927307
theorem B2974799 : Blo 1391515 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B2090063 : Blo 1391515 2090063 := bstep (se 1 (by rfl) ⟨1567547, by rfl⟩ : syracuseStep 2090063 = 3135095) B3135095
theorem B2090183 : Blo 1391515 2090183 := bstep (se 1 (by rfl) ⟨1567637, by rfl⟩ : syracuseStep 2090183 = 3135275) B3135275
theorem B26764505 : Blo 1391515 26764505 := bstep (se 2 (by rfl) ⟨10036689, by rfl⟩ : syracuseStep 26764505 = 20073379) B20073379
theorem B5088523 : Blo 1391515 5088523 := bstep (se 1 (by rfl) ⟨3816392, by rfl⟩ : syracuseStep 5088523 = 7632785) B7632785
theorem B3523945 : Blo 1391515 3523945 := bstep (se 2 (by rfl) ⟨1321479, by rfl⟩ : syracuseStep 3523945 = 2642959) B2642959
theorem B2508193 : Blo 1391515 2508193 := bstep (se 2 (by rfl) ⟨940572, by rfl⟩ : syracuseStep 2508193 = 1881145) B1881145
theorem B5285357 : Blo 1391515 5285357 := bstep (se 3 (by rfl) ⟨991004, by rfl⟩ : syracuseStep 5285357 = 1982009) B1982009
theorem B3130919 : Blo 1391515 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B1566247 : Blo 1391515 1566247 := bstep (se 1 (by rfl) ⟨1174685, by rfl⟩ : syracuseStep 1566247 = 2349371) B2349371
theorem B3524219 : Blo 1391515 3524219 := bstep (se 1 (by rfl) ⟨2643164, by rfl⟩ : syracuseStep 3524219 = 5286329) B5286329
theorem B6350525 : Blo 1391515 6350525 := bstep (se 3 (by rfl) ⟨1190723, by rfl⟩ : syracuseStep 6350525 = 2381447) B2381447
theorem B5285675 : Blo 1391515 5285675 := bstep (se 1 (by rfl) ⟨3964256, by rfl⟩ : syracuseStep 5285675 = 7928513) B7928513
theorem B3131243 : Blo 1391515 3131243 := bstep (se 1 (by rfl) ⟨2348432, by rfl⟩ : syracuseStep 3131243 = 4696865) B4696865
theorem B3131297 : Blo 1391515 3131297 := bstep (se 2 (by rfl) ⟨1174236, by rfl⟩ : syracuseStep 3131297 = 2348473) B2348473
theorem B11290529 : Blo 1391515 11290529 := bstep (se 2 (by rfl) ⟨4233948, by rfl⟩ : syracuseStep 11290529 = 8467897) B8467897
theorem B11290661 : Blo 1391515 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B1763527 : Blo 1391515 1763527 := bstep (se 1 (by rfl) ⟨1322645, by rfl⟩ : syracuseStep 1763527 = 2645291) B2645291
theorem B3131639 : Blo 1391515 3131639 := bstep (se 1 (by rfl) ⟨2348729, by rfl⟩ : syracuseStep 3131639 = 4697459) B4697459
theorem B13060403 : Blo 1391515 13060403 := bstep (se 1 (by rfl) ⟨9795302, by rfl⟩ : syracuseStep 13060403 = 19590605) B19590605
theorem B7047485 : Blo 1391515 7047485 := bstep (se 3 (by rfl) ⟨1321403, by rfl⟩ : syracuseStep 7047485 = 2642807) B2642807
theorem B2230715 : Blo 1391515 2230715 := bstep (se 1 (by rfl) ⟨1673036, by rfl⟩ : syracuseStep 2230715 = 3346073) B3346073
theorem B2230907 : Blo 1391515 2230907 := bstep (se 1 (by rfl) ⟨1673180, by rfl⟩ : syracuseStep 2230907 = 3346361) B3346361
theorem B2681515 : Blo 1391515 2681515 := bstep (se 1 (by rfl) ⟨2011136, by rfl⟩ : syracuseStep 2681515 = 4022273) B4022273
theorem B10316489 : Blo 1391515 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B10570499 : Blo 1391515 10570499 := bstep (se 1 (by rfl) ⟨7927874, by rfl⟩ : syracuseStep 10570499 = 15855749) B15855749
theorem B3132233 : Blo 1391515 3132233 := bstep (se 2 (by rfl) ⟨1174587, by rfl⟩ : syracuseStep 3132233 = 2349175) B2349175
theorem B6351689 : Blo 1391515 6351689 := bstep (se 2 (by rfl) ⟨2381883, by rfl⟩ : syracuseStep 6351689 = 4763767) B4763767
theorem B164940619 : Blo 1391515 164940619 := bstep (se 1 (by rfl) ⟨123705464, by rfl⟩ : syracuseStep 164940619 = 247410929) B247410929
theorem B10578761 : Blo 1391515 10578761 := bstep (se 2 (by rfl) ⟨3967035, by rfl⟩ : syracuseStep 10578761 = 7934071) B7934071
theorem B5647211 : Blo 1391515 5647211 := bstep (se 1 (by rfl) ⟨4235408, by rfl⟩ : syracuseStep 5647211 = 8470817) B8470817
theorem B28978067 : Blo 1391515 28978067 := bstep (se 1 (by rfl) ⟨21733550, by rfl⟩ : syracuseStep 28978067 = 43467101) B43467101
theorem B23506037 : Blo 1391515 23506037 := bstep (se 5 (by rfl) ⟨1101845, by rfl⟩ : syracuseStep 23506037 = 2203691) B2203691
theorem B4697405 : Blo 1391515 4697405 := bstep (se 3 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 4697405 = 1761527) B1761527
theorem B3526031 : Blo 1391515 3526031 := bstep (se 1 (by rfl) ⟨2644523, by rfl⟩ : syracuseStep 3526031 = 5289047) B5289047
theorem B20336093 : Blo 1391515 20336093 := bstep (se 3 (by rfl) ⟨3813017, by rfl⟩ : syracuseStep 20336093 = 7626035) B7626035
theorem B3133025 : Blo 1391515 3133025 := bstep (se 2 (by rfl) ⟨1174884, by rfl⟩ : syracuseStep 3133025 = 2349769) B2349769
theorem B3526355 : Blo 1391515 3526355 := bstep (se 1 (by rfl) ⟨2644766, by rfl⟩ : syracuseStep 3526355 = 5289533) B5289533
theorem B5287787 : Blo 1391515 5287787 := bstep (se 1 (by rfl) ⟨3965840, by rfl⟩ : syracuseStep 5287787 = 7931681) B7931681
theorem B5648237 : Blo 1391515 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B3133367 : Blo 1391515 3133367 := bstep (se 1 (by rfl) ⟨2350025, by rfl⟩ : syracuseStep 3133367 = 4700051) B4700051
theorem B7933889 : Blo 1391515 7933889 := bstep (se 2 (by rfl) ⟨2975208, by rfl⟩ : syracuseStep 7933889 = 5950417) B5950417
theorem B5951495 : Blo 1391515 5951495 := bstep (se 1 (by rfl) ⟨4463621, by rfl⟩ : syracuseStep 5951495 = 8927243) B8927243
theorem B2715727 : Blo 1391515 2715727 := bstep (se 1 (by rfl) ⟨2036795, by rfl⟩ : syracuseStep 2715727 = 4073591) B4073591
theorem B7925849 : Blo 1391515 7925849 := bstep (se 2 (by rfl) ⟨2972193, by rfl⟩ : syracuseStep 7925849 = 5944387) B5944387
theorem B4698269 : Blo 1391515 4698269 := bstep (se 3 (by rfl) ⟨880925, by rfl⟩ : syracuseStep 4698269 = 1761851) B1761851
theorem B9654589 : Blo 1391515 9654589 := bstep (se 3 (by rfl) ⟨1810235, by rfl⟩ : syracuseStep 9654589 = 3620471) B3620471
theorem B8466925 : Blo 1391515 8466925 := bstep (se 3 (by rfl) ⟨1587548, by rfl⟩ : syracuseStep 8466925 = 3175097) B3175097
theorem B7926281 : Blo 1391515 7926281 := bstep (se 2 (by rfl) ⟨2972355, by rfl⟩ : syracuseStep 7926281 = 5944711) B5944711
theorem B3133961 : Blo 1391515 3133961 := bstep (se 2 (by rfl) ⟨1175235, by rfl⟩ : syracuseStep 3133961 = 2350471) B2350471
theorem B7049753 : Blo 1391515 7049753 := bstep (se 2 (by rfl) ⟨2643657, by rfl⟩ : syracuseStep 7049753 = 5287315) B5287315
theorem B4698809 : Blo 1391515 4698809 := bstep (se 2 (by rfl) ⟨1762053, by rfl⟩ : syracuseStep 4698809 = 3524107) B3524107
theorem B10711763 : Blo 1391515 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B3134303 : Blo 1391515 3134303 := bstep (se 1 (by rfl) ⟨2350727, by rfl⟩ : syracuseStep 3134303 = 4701455) B4701455
theorem B4461583 : Blo 1391515 4461583 := bstep (se 1 (by rfl) ⟨3346187, by rfl⟩ : syracuseStep 4461583 = 6692375) B6692375
theorem B3134483 : Blo 1391515 3134483 := bstep (se 1 (by rfl) ⟨2350862, by rfl⟩ : syracuseStep 3134483 = 4701725) B4701725
theorem B5018705 : Blo 1391515 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B2348203 : Blo 1391515 2348203 := bstep (se 1 (by rfl) ⟨1761152, by rfl⟩ : syracuseStep 2348203 = 3522305) B3522305
theorem B8467703 : Blo 1391515 8467703 := bstep (se 1 (by rfl) ⟨6350777, by rfl⟩ : syracuseStep 8467703 = 12701555) B12701555
theorem B4699403 : Blo 1391515 4699403 := bstep (se 1 (by rfl) ⟨3524552, by rfl⟩ : syracuseStep 4699403 = 7049105) B7049105
theorem B3134825 : Blo 1391515 3134825 := bstep (se 2 (by rfl) ⟨1175559, by rfl⟩ : syracuseStep 3134825 = 2351119) B2351119
theorem B2823599 : Blo 1391515 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B2348507 : Blo 1391515 2348507 := bstep (se 1 (by rfl) ⟨1761380, by rfl⟩ : syracuseStep 2348507 = 3522761) B3522761
theorem B4699673 : Blo 1391515 4699673 := bstep (se 2 (by rfl) ⟨1762377, by rfl⟩ : syracuseStep 4699673 = 3524755) B3524755
theorem B4519547 : Blo 1391515 4519547 := bstep (se 1 (by rfl) ⟨3389660, by rfl⟩ : syracuseStep 4519547 = 6779321) B6779321
theorem B2348743 : Blo 1391515 2348743 := bstep (se 1 (by rfl) ⟨1761557, by rfl⟩ : syracuseStep 2348743 = 3523115) B3523115
theorem B3348179 : Blo 1391515 3348179 := bstep (se 1 (by rfl) ⟨2511134, by rfl⟩ : syracuseStep 3348179 = 5022269) B5022269
theorem B3176185 : Blo 1391515 3176185 := bstep (se 2 (by rfl) ⟨1191069, by rfl⟩ : syracuseStep 3176185 = 2382139) B2382139
theorem B3766009 : Blo 1391515 3766009 := bstep (se 2 (by rfl) ⟨1412253, by rfl⟩ : syracuseStep 3766009 = 2824507) B2824507
theorem B2348905 : Blo 1391515 2348905 := bstep (se 2 (by rfl) ⟨880839, by rfl⟩ : syracuseStep 2348905 = 1761679) B1761679
theorem B5019499 : Blo 1391515 5019499 := bstep (se 1 (by rfl) ⟨3764624, by rfl⟩ : syracuseStep 5019499 = 7529249) B7529249
theorem B7927739 : Blo 1391515 7927739 := bstep (se 1 (by rfl) ⟨5945804, by rfl⟩ : syracuseStep 7927739 = 11891609) B11891609
theorem B9164731 : Blo 1391515 9164731 := bstep (se 1 (by rfl) ⟨6873548, by rfl⟩ : syracuseStep 9164731 = 13747097) B13747097
theorem B13391821 : Blo 1391515 13391821 := bstep (se 3 (by rfl) ⟨2510966, by rfl⟩ : syracuseStep 13391821 = 5021933) B5021933
theorem B2643931 : Blo 1391515 2643931 := bstep (se 1 (by rfl) ⟨1982948, by rfl⟩ : syracuseStep 2643931 = 3965897) B3965897
theorem B1906697 : Blo 1391515 1906697 := bstep (se 2 (by rfl) ⟨715011, by rfl⟩ : syracuseStep 1906697 = 1430023) B1430023
theorem B2643977 : Blo 1391515 2643977 := bstep (se 2 (by rfl) ⟨991491, by rfl⟩ : syracuseStep 2643977 = 1982983) B1982983
theorem B10573901 : Blo 1391515 10573901 := bstep (se 3 (by rfl) ⟨1982606, by rfl⟩ : syracuseStep 10573901 = 3965213) B3965213
theorem B5290231 : Blo 1391515 5290231 := bstep (se 1 (by rfl) ⟨3967673, by rfl⟩ : syracuseStep 5290231 = 7935347) B7935347
theorem B2644319 : Blo 1391515 2644319 := bstep (se 1 (by rfl) ⟨1983239, by rfl⟩ : syracuseStep 2644319 = 3966479) B3966479
theorem B2087273 : Blo 1391515 2087273 := bstep (se 2 (by rfl) ⟨782727, by rfl⟩ : syracuseStep 2087273 = 1565455) B1565455
theorem B2087351 : Blo 1391515 2087351 := bstep (se 1 (by rfl) ⟨1565513, by rfl⟩ : syracuseStep 2087351 = 3131027) B3131027
theorem B2349499 : Blo 1391515 2349499 := bstep (se 1 (by rfl) ⟨1762124, by rfl⟩ : syracuseStep 2349499 = 3524249) B3524249
theorem B2087387 : Blo 1391515 2087387 := bstep (se 1 (by rfl) ⟨1565540, by rfl⟩ : syracuseStep 2087387 = 3131081) B3131081
theorem B5290505 : Blo 1391515 5290505 := bstep (se 2 (by rfl) ⟨1983939, by rfl⟩ : syracuseStep 5290505 = 3967879) B3967879
theorem B2349607 : Blo 1391515 2349607 := bstep (se 1 (by rfl) ⟨1762205, by rfl⟩ : syracuseStep 2349607 = 3524411) B3524411
theorem B5290535 : Blo 1391515 5290535 := bstep (se 1 (by rfl) ⟨3967901, by rfl⟩ : syracuseStep 5290535 = 7935803) B7935803
theorem B4700807 : Blo 1391515 4700807 := bstep (se 1 (by rfl) ⟨3525605, by rfl⟩ : syracuseStep 4700807 = 7051211) B7051211
theorem B5085881 : Blo 1391515 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B4700861 : Blo 1391515 4700861 := bstep (se 3 (by rfl) ⟨881411, by rfl⟩ : syracuseStep 4700861 = 1762823) B1762823
theorem B10033949 : Blo 1391515 10033949 := bstep (se 3 (by rfl) ⟨1881365, by rfl⟩ : syracuseStep 10033949 = 3762731) B3762731
theorem B4701023 : Blo 1391515 4701023 := bstep (se 1 (by rfl) ⟨3525767, by rfl⟩ : syracuseStep 4701023 = 7051535) B7051535
theorem B3963755 : Blo 1391515 3963755 := bstep (se 1 (by rfl) ⟨2972816, by rfl⟩ : syracuseStep 3963755 = 5945633) B5945633
theorem B2349931 : Blo 1391515 2349931 := bstep (se 1 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 2349931 = 3524897) B3524897
theorem B3177323 : Blo 1391515 3177323 := bstep (se 1 (by rfl) ⟨2382992, by rfl⟩ : syracuseStep 3177323 = 4765985) B4765985
theorem B1391535 : Blo 1391515 1391535 := bstep (se 1 (by rfl) ⟨1043651, by rfl⟩ : syracuseStep 1391535 = 2087303) B2087303
theorem B2087855 : Blo 1391515 2087855 := bstep (se 1 (by rfl) ⟨1565891, by rfl⟩ : syracuseStep 2087855 = 3131783) B3131783
theorem B13392823 : Blo 1391515 13392823 := bstep (se 1 (by rfl) ⟨10044617, by rfl⟩ : syracuseStep 13392823 = 20089235) B20089235
theorem B1391559 : Blo 1391515 1391559 := bstep (se 1 (by rfl) ⟨1043669, by rfl⟩ : syracuseStep 1391559 = 2087339) B2087339
theorem B1391579 : Blo 1391515 1391579 := bstep (se 1 (by rfl) ⟨1043684, by rfl⟩ : syracuseStep 1391579 = 2087369) B2087369
theorem B4701185 : Blo 1391515 4701185 := bstep (se 2 (by rfl) ⟨1762944, by rfl⟩ : syracuseStep 4701185 = 3525889) B3525889
theorem B2087945 : Blo 1391515 2087945 := bstep (se 2 (by rfl) ⟨782979, by rfl⟩ : syracuseStep 2087945 = 1565959) B1565959
theorem B1391655 : Blo 1391515 1391655 := bstep (se 1 (by rfl) ⟨1043741, by rfl⟩ : syracuseStep 1391655 = 2087483) B2087483
theorem B2087975 : Blo 1391515 2087975 := bstep (se 1 (by rfl) ⟨1565981, by rfl⟩ : syracuseStep 2087975 = 3131963) B3131963
theorem B11295787 : Blo 1391515 11295787 := bstep (se 1 (by rfl) ⟨8471840, by rfl⟩ : syracuseStep 11295787 = 16943681) B16943681
theorem B1391695 : Blo 1391515 1391695 := bstep (se 1 (by rfl) ⟨1043771, by rfl⟩ : syracuseStep 1391695 = 2087543) B2087543
theorem B1391711 : Blo 1391515 1391711 := bstep (se 1 (by rfl) ⟨1043783, by rfl⟩ : syracuseStep 1391711 = 2087567) B2087567
theorem B1391739 : Blo 1391515 1391739 := bstep (se 1 (by rfl) ⟨1043804, by rfl⟩ : syracuseStep 1391739 = 2087609) B2087609
theorem B2088059 : Blo 1391515 2088059 := bstep (se 1 (by rfl) ⟨1566044, by rfl⟩ : syracuseStep 2088059 = 3132089) B3132089
theorem B1391791 : Blo 1391515 1391791 := bstep (se 1 (by rfl) ⟨1043843, by rfl⟩ : syracuseStep 1391791 = 2087687) B2087687
theorem B1391815 : Blo 1391515 1391815 := bstep (se 1 (by rfl) ⟨1043861, by rfl⟩ : syracuseStep 1391815 = 2087723) B2087723
theorem B1391835 : Blo 1391515 1391835 := bstep (se 1 (by rfl) ⟨1043876, by rfl⟩ : syracuseStep 1391835 = 2087753) B2087753
theorem B2088185 : Blo 1391515 2088185 := bstep (se 2 (by rfl) ⟨783069, by rfl⟩ : syracuseStep 2088185 = 1566139) B1566139
theorem B1391911 : Blo 1391515 1391911 := bstep (se 1 (by rfl) ⟨1043933, by rfl⟩ : syracuseStep 1391911 = 2087867) B2087867
theorem B2448713 : Blo 1391515 2448713 := bstep (se 2 (by rfl) ⟨918267, by rfl⟩ : syracuseStep 2448713 = 1836535) B1836535
theorem B1391951 : Blo 1391515 1391951 := bstep (se 1 (by rfl) ⟨1043963, by rfl⟩ : syracuseStep 1391951 = 2087927) B2087927
theorem B1391967 : Blo 1391515 1391967 := bstep (se 1 (by rfl) ⟨1043975, by rfl⟩ : syracuseStep 1391967 = 2087951) B2087951
theorem B2088287 : Blo 1391515 2088287 := bstep (se 1 (by rfl) ⟨1566215, by rfl⟩ : syracuseStep 2088287 = 3132431) B3132431
theorem B2088299 : Blo 1391515 2088299 := bstep (se 1 (by rfl) ⟨1566224, by rfl⟩ : syracuseStep 2088299 = 3132449) B3132449
theorem B1391995 : Blo 1391515 1391995 := bstep (se 1 (by rfl) ⟨1043996, by rfl⟩ : syracuseStep 1391995 = 2087993) B2087993
theorem B7052669 : Blo 1391515 7052669 := bstep (se 3 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 7052669 = 2644751) B2644751
theorem B1392047 : Blo 1391515 1392047 := bstep (se 1 (by rfl) ⟨1044035, by rfl⟩ : syracuseStep 1392047 = 2088071) B2088071
theorem B2645435 : Blo 1391515 2645435 := bstep (se 1 (by rfl) ⟨1984076, by rfl⟩ : syracuseStep 2645435 = 3968153) B3968153
theorem B1392071 : Blo 1391515 1392071 := bstep (se 1 (by rfl) ⟨1044053, by rfl⟩ : syracuseStep 1392071 = 2088107) B2088107
theorem B1392091 : Blo 1391515 1392091 := bstep (se 1 (by rfl) ⟨1044068, by rfl⟩ : syracuseStep 1392091 = 2088137) B2088137
theorem B1392167 : Blo 1391515 1392167 := bstep (se 1 (by rfl) ⟨1044125, by rfl⟩ : syracuseStep 1392167 = 2088251) B2088251
theorem B1392207 : Blo 1391515 1392207 := bstep (se 1 (by rfl) ⟨1044155, by rfl⟩ : syracuseStep 1392207 = 2088311) B2088311
theorem B2088527 : Blo 1391515 2088527 := bstep (se 1 (by rfl) ⟨1566395, by rfl⟩ : syracuseStep 2088527 = 3132791) B3132791
theorem B12697175 : Blo 1391515 12697175 := bstep (se 1 (by rfl) ⟨9522881, by rfl⟩ : syracuseStep 12697175 = 19045763) B19045763
theorem B1392223 : Blo 1391515 1392223 := bstep (se 1 (by rfl) ⟨1044167, by rfl⟩ : syracuseStep 1392223 = 2088335) B2088335
theorem B7044731 : Blo 1391515 7044731 := bstep (se 1 (by rfl) ⟨5283548, by rfl⟩ : syracuseStep 7044731 = 10567097) B10567097
theorem B1392251 : Blo 1391515 1392251 := bstep (se 1 (by rfl) ⟨1044188, by rfl⟩ : syracuseStep 1392251 = 2088377) B2088377
theorem B1392303 : Blo 1391515 1392303 := bstep (se 1 (by rfl) ⟨1044227, by rfl⟩ : syracuseStep 1392303 = 2088455) B2088455
theorem B1392327 : Blo 1391515 1392327 := bstep (se 1 (by rfl) ⟨1044245, by rfl⟩ : syracuseStep 1392327 = 2088491) B2088491
theorem B2088647 : Blo 1391515 2088647 := bstep (se 1 (by rfl) ⟨1566485, by rfl⟩ : syracuseStep 2088647 = 3132971) B3132971
theorem B1392347 : Blo 1391515 1392347 := bstep (se 1 (by rfl) ⟨1044260, by rfl⟩ : syracuseStep 1392347 = 2088521) B2088521
theorem B1392423 : Blo 1391515 1392423 := bstep (se 1 (by rfl) ⟨1044317, by rfl⟩ : syracuseStep 1392423 = 2088635) B2088635
theorem B6029099 : Blo 1391515 6029099 := bstep (se 1 (by rfl) ⟨4521824, by rfl⟩ : syracuseStep 6029099 = 9043649) B9043649
theorem B4701995 : Blo 1391515 4701995 := bstep (se 1 (by rfl) ⟨3526496, by rfl⟩ : syracuseStep 4701995 = 7052993) B7052993
theorem B8044331 : Blo 1391515 8044331 := bstep (se 1 (by rfl) ⟨6033248, by rfl⟩ : syracuseStep 8044331 = 12066497) B12066497
theorem B1392463 : Blo 1391515 1392463 := bstep (se 1 (by rfl) ⟨1044347, by rfl⟩ : syracuseStep 1392463 = 2088695) B2088695
theorem B1392479 : Blo 1391515 1392479 := bstep (se 1 (by rfl) ⟨1044359, by rfl⟩ : syracuseStep 1392479 = 2088719) B2088719
theorem B2088809 : Blo 1391515 2088809 := bstep (se 2 (by rfl) ⟨783303, by rfl⟩ : syracuseStep 2088809 = 1566607) B1566607
theorem B1392507 : Blo 1391515 1392507 := bstep (se 1 (by rfl) ⟨1044380, by rfl⟩ : syracuseStep 1392507 = 2088761) B2088761
theorem B2350991 : Blo 1391515 2350991 := bstep (se 1 (by rfl) ⟨1763243, by rfl⟩ : syracuseStep 2350991 = 3526487) B3526487
theorem B1392559 : Blo 1391515 1392559 := bstep (se 1 (by rfl) ⟨1044419, by rfl⟩ : syracuseStep 1392559 = 2088839) B2088839
theorem B3522487 : Blo 1391515 3522487 := bstep (se 1 (by rfl) ⟨2641865, by rfl⟩ : syracuseStep 3522487 = 5283731) B5283731
theorem B2088887 : Blo 1391515 2088887 := bstep (se 1 (by rfl) ⟨1566665, by rfl⟩ : syracuseStep 2088887 = 3133331) B3133331
theorem B1392583 : Blo 1391515 1392583 := bstep (se 1 (by rfl) ⟨1044437, by rfl⟩ : syracuseStep 1392583 = 2088875) B2088875
theorem B101638091 : Blo 1391515 101638091 := bstep (se 1 (by rfl) ⟨76228568, by rfl⟩ : syracuseStep 101638091 = 152457137) B152457137
theorem B1392603 : Blo 1391515 1392603 := bstep (se 1 (by rfl) ⟨1044452, by rfl⟩ : syracuseStep 1392603 = 2088905) B2088905
theorem B2088923 : Blo 1391515 2088923 := bstep (se 1 (by rfl) ⟨1566692, by rfl⟩ : syracuseStep 2088923 = 3133385) B3133385
theorem B5283899 : Blo 1391515 5283899 := bstep (se 1 (by rfl) ⟨3962924, by rfl⟩ : syracuseStep 5283899 = 7925849) B7925849
theorem B3620969 : Blo 1391515 3620969 := bstep (se 2 (by rfl) ⟨1357863, by rfl⟩ : syracuseStep 3620969 = 2715727) B2715727
theorem B371064995 : Blo 1391515 371064995 := bstep (se 1 (by rfl) ⟨278298746, by rfl⟩ : syracuseStep 371064995 = 556597493) B556597493
theorem B7045379 : Blo 1391515 7045379 := bstep (se 1 (by rfl) ⟨5284034, by rfl⟩ : syracuseStep 7045379 = 10568069) B10568069
theorem B2351369 : Blo 1391515 2351369 := bstep (se 2 (by rfl) ⟨881763, by rfl⟩ : syracuseStep 2351369 = 1763527) B1763527
theorem B1392927 : Blo 1391515 1392927 := bstep (se 1 (by rfl) ⟨1044695, by rfl⟩ : syracuseStep 1392927 = 2089391) B2089391
theorem B7053641 : Blo 1391515 7053641 := bstep (se 2 (by rfl) ⟨2645115, by rfl⟩ : syracuseStep 7053641 = 5290231) B5290231
theorem B5284187 : Blo 1391515 5284187 := bstep (se 1 (by rfl) ⟨3963140, by rfl⟩ : syracuseStep 5284187 = 7926281) B7926281
theorem B2089307 : Blo 1391515 2089307 := bstep (se 1 (by rfl) ⟨1566980, by rfl⟩ : syracuseStep 2089307 = 3133961) B3133961
theorem B1392987 : Blo 1391515 1392987 := bstep (se 1 (by rfl) ⟨1044740, by rfl⟩ : syracuseStep 1392987 = 2089481) B2089481
theorem B3522923 : Blo 1391515 3522923 := bstep (se 1 (by rfl) ⟨2642192, by rfl⟩ : syracuseStep 3522923 = 5284385) B5284385
theorem B1393007 : Blo 1391515 1393007 := bstep (se 1 (by rfl) ⟨1044755, by rfl⟩ : syracuseStep 1393007 = 2089511) B2089511
theorem B1786279 : Blo 1391515 1786279 := bstep (se 1 (by rfl) ⟨1339709, by rfl⟩ : syracuseStep 1786279 = 2679419) B2679419
theorem B1393063 : Blo 1391515 1393063 := bstep (se 1 (by rfl) ⟨1044797, by rfl⟩ : syracuseStep 1393063 = 2089595) B2089595
theorem B1982971 : Blo 1391515 1982971 := bstep (se 1 (by rfl) ⟨1487228, by rfl⟩ : syracuseStep 1982971 = 2974457) B2974457
theorem B1393147 : Blo 1391515 1393147 := bstep (se 1 (by rfl) ⟨1044860, by rfl⟩ : syracuseStep 1393147 = 2089721) B2089721
theorem B3523135 : Blo 1391515 3523135 := bstep (se 1 (by rfl) ⟨2642351, by rfl⟩ : syracuseStep 3523135 = 5284703) B5284703
theorem B2089535 : Blo 1391515 2089535 := bstep (se 1 (by rfl) ⟨1567151, by rfl⟩ : syracuseStep 2089535 = 3134303) B3134303
theorem B1393215 : Blo 1391515 1393215 := bstep (se 1 (by rfl) ⟨1044911, by rfl⟩ : syracuseStep 1393215 = 2089823) B2089823
theorem B7045703 : Blo 1391515 7045703 := bstep (se 1 (by rfl) ⟨5284277, by rfl⟩ : syracuseStep 7045703 = 10568555) B10568555
theorem B1393223 : Blo 1391515 1393223 := bstep (se 1 (by rfl) ⟨1044917, by rfl⟩ : syracuseStep 1393223 = 2089835) B2089835
theorem B1671787 : Blo 1391515 1671787 := bstep (se 1 (by rfl) ⟨1253840, by rfl⟩ : syracuseStep 1671787 = 2507681) B2507681
theorem B11289233 : Blo 1391515 11289233 := bstep (se 2 (by rfl) ⟨4233462, by rfl⟩ : syracuseStep 11289233 = 8466925) B8466925
theorem B3523247 : Blo 1391515 3523247 := bstep (se 1 (by rfl) ⟨2642435, by rfl⟩ : syracuseStep 3523247 = 5284871) B5284871
theorem B2089655 : Blo 1391515 2089655 := bstep (se 1 (by rfl) ⟨1567241, by rfl⟩ : syracuseStep 2089655 = 3134483) B3134483
theorem B1983199 : Blo 1391515 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B1393375 : Blo 1391515 1393375 := bstep (se 1 (by rfl) ⟨1045031, by rfl⟩ : syracuseStep 1393375 = 2090063) B2090063
theorem B1393455 : Blo 1391515 1393455 := bstep (se 1 (by rfl) ⟨1045091, by rfl⟩ : syracuseStep 1393455 = 2090183) B2090183
theorem B17843003 : Blo 1391515 17843003 := bstep (se 1 (by rfl) ⟨13382252, by rfl⟩ : syracuseStep 17843003 = 26764505) B26764505
theorem B5645135 : Blo 1391515 5645135 := bstep (se 1 (by rfl) ⟨4233851, by rfl⟩ : syracuseStep 5645135 = 8467703) B8467703
theorem B2089883 : Blo 1391515 2089883 := bstep (se 1 (by rfl) ⟨1567412, by rfl⟩ : syracuseStep 2089883 = 3134825) B3134825
theorem B1565671 : Blo 1391515 1565671 := bstep (se 1 (by rfl) ⟨1174253, by rfl⟩ : syracuseStep 1565671 = 2348507) B2348507
theorem B3523571 : Blo 1391515 3523571 := bstep (se 1 (by rfl) ⟨2642678, by rfl⟩ : syracuseStep 3523571 = 5285357) B5285357
theorem B7529597 : Blo 1391515 7529597 := bstep (se 3 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 7529597 = 2823599) B2823599
theorem B3523783 : Blo 1391515 3523783 := bstep (se 1 (by rfl) ⟨2642837, by rfl⟩ : syracuseStep 3523783 = 5285675) B5285675
theorem B5285159 : Blo 1391515 5285159 := bstep (se 1 (by rfl) ⟨3963869, by rfl⟩ : syracuseStep 5285159 = 7927739) B7927739
theorem B1762651 : Blo 1391515 1762651 := bstep (se 1 (by rfl) ⟨1321988, by rfl⟩ : syracuseStep 1762651 = 2643977) B2643977
theorem B5948777 : Blo 1391515 5948777 := bstep (se 2 (by rfl) ⟨2230791, by rfl⟩ : syracuseStep 5948777 = 4461583) B4461583
theorem B3130937 : Blo 1391515 3130937 := bstep (se 2 (by rfl) ⟨1174101, by rfl⟩ : syracuseStep 3130937 = 2348203) B2348203
theorem B33859133 : Blo 1391515 33859133 := bstep (se 3 (by rfl) ⟨6348587, by rfl⟩ : syracuseStep 33859133 = 12697175) B12697175
theorem B1762879 : Blo 1391515 1762879 := bstep (se 1 (by rfl) ⟨1322159, by rfl⟩ : syracuseStep 1762879 = 2644319) B2644319
theorem B5949085 : Blo 1391515 5949085 := bstep (se 3 (by rfl) ⟨1115453, by rfl⟩ : syracuseStep 5949085 = 2230907) B2230907
theorem B6784697 : Blo 1391515 6784697 := bstep (se 2 (by rfl) ⟨2544261, by rfl⟩ : syracuseStep 6784697 = 5088523) B5088523
theorem B7046999 : Blo 1391515 7046999 := bstep (se 1 (by rfl) ⟨5285249, by rfl⟩ : syracuseStep 7046999 = 10570499) B10570499
theorem B3344257 : Blo 1391515 3344257 := bstep (se 2 (by rfl) ⟨1254096, by rfl⟩ : syracuseStep 3344257 = 2508193) B2508193
theorem B19318711 : Blo 1391515 19318711 := bstep (se 1 (by rfl) ⟨14489033, by rfl⟩ : syracuseStep 19318711 = 28978067) B28978067
theorem B3131603 : Blo 1391515 3131603 := bstep (se 1 (by rfl) ⟨2348702, by rfl⟩ : syracuseStep 3131603 = 4697405) B4697405
theorem B1632475 : Blo 1391515 1632475 := bstep (se 1 (by rfl) ⟨1224356, by rfl⟩ : syracuseStep 1632475 = 2448713) B2448713
theorem B3131657 : Blo 1391515 3131657 := bstep (se 2 (by rfl) ⟨1174371, by rfl⟩ : syracuseStep 3131657 = 2348743) B2348743
theorem B10570013 : Blo 1391515 10570013 := bstep (se 3 (by rfl) ⟨1981877, by rfl⟩ : syracuseStep 10570013 = 3963755) B3963755
theorem B1763623 : Blo 1391515 1763623 := bstep (se 1 (by rfl) ⟨1322717, by rfl⟩ : syracuseStep 1763623 = 2645435) B2645435
theorem B4696487 : Blo 1391515 4696487 := bstep (se 1 (by rfl) ⟨3522365, by rfl⟩ : syracuseStep 4696487 = 7044731) B7044731
theorem B3131873 : Blo 1391515 3131873 := bstep (se 2 (by rfl) ⟨1174452, by rfl⟩ : syracuseStep 3131873 = 2348905) B2348905
theorem B271034909 : Blo 1391515 271034909 := bstep (se 3 (by rfl) ⟨50819045, by rfl⟩ : syracuseStep 271034909 = 101638091) B101638091
theorem B3525191 : Blo 1391515 3525191 := bstep (se 1 (by rfl) ⟨2643893, by rfl⟩ : syracuseStep 3525191 = 5287787) B5287787
theorem B4696649 : Blo 1391515 4696649 := bstep (se 2 (by rfl) ⟨1761243, by rfl⟩ : syracuseStep 4696649 = 3522487) B3522487
theorem B1567327 : Blo 1391515 1567327 := bstep (se 1 (by rfl) ⟨1175495, by rfl⟩ : syracuseStep 1567327 = 2350991) B2350991
theorem B3525241 : Blo 1391515 3525241 := bstep (se 2 (by rfl) ⟨1321965, by rfl⟩ : syracuseStep 3525241 = 2643931) B2643931
theorem B3967663 : Blo 1391515 3967663 := bstep (se 1 (by rfl) ⟨2975747, by rfl⟩ : syracuseStep 3967663 = 5951495) B5951495
theorem B15854291 : Blo 1391515 15854291 := bstep (se 1 (by rfl) ⟨11890718, by rfl⟩ : syracuseStep 15854291 = 23781437) B23781437
theorem B5286647 : Blo 1391515 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B3132179 : Blo 1391515 3132179 := bstep (se 1 (by rfl) ⟨2349134, by rfl⟩ : syracuseStep 3132179 = 4698269) B4698269
theorem B8924039 : Blo 1391515 8924039 := bstep (se 1 (by rfl) ⟨6693029, by rfl⟩ : syracuseStep 8924039 = 13386059) B13386059
theorem B14298113 : Blo 1391515 14298113 := bstep (se 2 (by rfl) ⟨5361792, by rfl⟩ : syracuseStep 14298113 = 10723585) B10723585
theorem B12872785 : Blo 1391515 12872785 := bstep (se 2 (by rfl) ⟨4827294, by rfl⟩ : syracuseStep 12872785 = 9654589) B9654589
theorem B3132539 : Blo 1391515 3132539 := bstep (se 1 (by rfl) ⟨2349404, by rfl⟩ : syracuseStep 3132539 = 4698809) B4698809
theorem B6352091 : Blo 1391515 6352091 := bstep (se 1 (by rfl) ⟨4764068, by rfl⟩ : syracuseStep 6352091 = 9528137) B9528137
theorem B3132665 : Blo 1391515 3132665 := bstep (se 2 (by rfl) ⟨1174749, by rfl⟩ : syracuseStep 3132665 = 2349499) B2349499
theorem B3132809 : Blo 1391515 3132809 := bstep (se 2 (by rfl) ⟨1174803, by rfl⟩ : syracuseStep 3132809 = 2349607) B2349607
theorem B3345803 : Blo 1391515 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B3132935 : Blo 1391515 3132935 := bstep (se 1 (by rfl) ⟨2349701, by rfl⟩ : syracuseStep 3132935 = 4699403) B4699403
theorem B3575353 : Blo 1391515 3575353 := bstep (se 2 (by rfl) ⟨1340757, by rfl⟩ : syracuseStep 3575353 = 2681515) B2681515
theorem B3133115 : Blo 1391515 3133115 := bstep (se 1 (by rfl) ⟨2349836, by rfl⟩ : syracuseStep 3133115 = 4699673) B4699673
theorem B2232119 : Blo 1391515 2232119 := bstep (se 1 (by rfl) ⟨1674089, by rfl⟩ : syracuseStep 2232119 = 3348179) B3348179
theorem B3133241 : Blo 1391515 3133241 := bstep (se 2 (by rfl) ⟨1174965, by rfl⟩ : syracuseStep 3133241 = 2349931) B2349931
theorem B7049267 : Blo 1391515 7049267 := bstep (se 1 (by rfl) ⟨5286950, by rfl⟩ : syracuseStep 7049267 = 10573901) B10573901
theorem B15061049 : Blo 1391515 15061049 := bstep (se 2 (by rfl) ⟨5647893, by rfl⟩ : syracuseStep 15061049 = 11295787) B11295787
theorem B4698323 : Blo 1391515 4698323 := bstep (se 1 (by rfl) ⟨3523742, by rfl⟩ : syracuseStep 4698323 = 7047485) B7047485
theorem B1487143 : Blo 1391515 1487143 := bstep (se 1 (by rfl) ⟨1115357, by rfl⟩ : syracuseStep 1487143 = 2230715) B2230715
theorem B3527003 : Blo 1391515 3527003 := bstep (se 1 (by rfl) ⟨2645252, by rfl⟩ : syracuseStep 3527003 = 5290505) B5290505
theorem B3527023 : Blo 1391515 3527023 := bstep (se 1 (by rfl) ⟨2645267, by rfl⟩ : syracuseStep 3527023 = 5290535) B5290535
theorem B3133871 : Blo 1391515 3133871 := bstep (se 1 (by rfl) ⟨2350403, by rfl⟩ : syracuseStep 3133871 = 4700807) B4700807
theorem B3133907 : Blo 1391515 3133907 := bstep (se 1 (by rfl) ⟨2350430, by rfl⟩ : syracuseStep 3133907 = 4700861) B4700861
theorem B4698593 : Blo 1391515 4698593 := bstep (se 2 (by rfl) ⟨1761972, by rfl⟩ : syracuseStep 4698593 = 3523945) B3523945
theorem B6689299 : Blo 1391515 6689299 := bstep (se 1 (by rfl) ⟨5016974, by rfl⟩ : syracuseStep 6689299 = 10033949) B10033949
theorem B3134015 : Blo 1391515 3134015 := bstep (se 1 (by rfl) ⟨2350511, by rfl⟩ : syracuseStep 3134015 = 4701023) B4701023
theorem B3764807 : Blo 1391515 3764807 := bstep (se 1 (by rfl) ⟨2823605, by rfl⟩ : syracuseStep 3764807 = 5647211) B5647211
theorem B2118215 : Blo 1391515 2118215 := bstep (se 1 (by rfl) ⟨1588661, by rfl⟩ : syracuseStep 2118215 = 3177323) B3177323
theorem B3134123 : Blo 1391515 3134123 := bstep (se 1 (by rfl) ⟨2350592, by rfl⟩ : syracuseStep 3134123 = 4701185) B4701185
theorem B21451549 : Blo 1391515 21451549 := bstep (se 3 (by rfl) ⟨4022165, by rfl⟩ : syracuseStep 21451549 = 8044331) B8044331
theorem B16937837 : Blo 1391515 16937837 := bstep (se 3 (by rfl) ⟨3175844, by rfl⟩ : syracuseStep 16937837 = 6351689) B6351689
theorem B4019399 : Blo 1391515 4019399 := bstep (se 1 (by rfl) ⟨3014549, by rfl⟩ : syracuseStep 4019399 = 6029099) B6029099
theorem B3134663 : Blo 1391515 3134663 := bstep (se 1 (by rfl) ⟨2350997, by rfl⟩ : syracuseStep 3134663 = 4701995) B4701995
theorem B3765491 : Blo 1391515 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B12219641 : Blo 1391515 12219641 := bstep (se 2 (by rfl) ⟨4582365, by rfl⟩ : syracuseStep 12219641 = 9164731) B9164731
theorem B17855761 : Blo 1391515 17855761 := bstep (se 2 (by rfl) ⟨6695910, by rfl⟩ : syracuseStep 17855761 = 13391821) B13391821
theorem B5289259 : Blo 1391515 5289259 := bstep (se 1 (by rfl) ⟨3966944, by rfl⟩ : syracuseStep 5289259 = 7933889) B7933889
theorem B5084525 : Blo 1391515 5084525 := bstep (se 3 (by rfl) ⟨953348, by rfl⟩ : syracuseStep 5084525 = 1906697) B1906697
theorem B51533171 : Blo 1391515 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B3134843 : Blo 1391515 3134843 := bstep (se 1 (by rfl) ⟨2351132, by rfl⟩ : syracuseStep 3134843 = 4702265) B4702265
theorem B3134969 : Blo 1391515 3134969 := bstep (se 2 (by rfl) ⟨1175613, by rfl⟩ : syracuseStep 3134969 = 2351227) B2351227
theorem B3135059 : Blo 1391515 3135059 := bstep (se 1 (by rfl) ⟨2351294, by rfl⟩ : syracuseStep 3135059 = 4702589) B4702589
theorem B7050887 : Blo 1391515 7050887 := bstep (se 1 (by rfl) ⟨5288165, by rfl⟩ : syracuseStep 7050887 = 10576331) B10576331
theorem B4699835 : Blo 1391515 4699835 := bstep (se 1 (by rfl) ⟨3524876, by rfl⟩ : syracuseStep 4699835 = 7049753) B7049753
theorem B3135239 : Blo 1391515 3135239 := bstep (se 1 (by rfl) ⟨2351429, by rfl⟩ : syracuseStep 3135239 = 4702859) B4702859
theorem B7141175 : Blo 1391515 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B4462391 : Blo 1391515 4462391 := bstep (se 1 (by rfl) ⟨3346793, by rfl⟩ : syracuseStep 4462391 = 6693587) B6693587
theorem B2087279 : Blo 1391515 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B3013031 : Blo 1391515 3013031 := bstep (se 1 (by rfl) ⟨2259773, by rfl⟩ : syracuseStep 3013031 = 4519547) B4519547
theorem B2349479 : Blo 1391515 2349479 := bstep (se 1 (by rfl) ⟨1762109, by rfl⟩ : syracuseStep 2349479 = 3524219) B3524219
theorem B219920825 : Blo 1391515 219920825 := bstep (se 2 (by rfl) ⟨82470309, by rfl⟩ : syracuseStep 219920825 = 164940619) B164940619
theorem B4233683 : Blo 1391515 4233683 := bstep (se 1 (by rfl) ⟨3175262, by rfl⟩ : syracuseStep 4233683 = 6350525) B6350525
theorem B2087495 : Blo 1391515 2087495 := bstep (se 1 (by rfl) ⟨1565621, by rfl⟩ : syracuseStep 2087495 = 3131243) B3131243
theorem B2349641 : Blo 1391515 2349641 := bstep (se 2 (by rfl) ⟨881115, by rfl⟩ : syracuseStep 2349641 = 1762231) B1762231
theorem B17857097 : Blo 1391515 17857097 := bstep (se 2 (by rfl) ⟨6696411, by rfl⟩ : syracuseStep 17857097 = 13392823) B13392823
theorem B2087531 : Blo 1391515 2087531 := bstep (se 1 (by rfl) ⟨1565648, by rfl⟩ : syracuseStep 2087531 = 3131297) B3131297
theorem B7527019 : Blo 1391515 7527019 := bstep (se 1 (by rfl) ⟨5645264, by rfl⟩ : syracuseStep 7527019 = 11290529) B11290529
theorem B7527107 : Blo 1391515 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B2087759 : Blo 1391515 2087759 := bstep (se 1 (by rfl) ⟨1565819, by rfl⟩ : syracuseStep 2087759 = 3131639) B3131639
theorem B8706935 : Blo 1391515 8706935 := bstep (se 1 (by rfl) ⟨6530201, by rfl⟩ : syracuseStep 8706935 = 13060403) B13060403
theorem B1391515 : Blo 1391515 1391515 := bstep (se 1 (by rfl) ⟨1043636, by rfl⟩ : syracuseStep 1391515 = 2087273) B2087273
theorem B1391567 : Blo 1391515 1391567 := bstep (se 1 (by rfl) ⟨1043675, by rfl⟩ : syracuseStep 1391567 = 2087351) B2087351
theorem B1391591 : Blo 1391515 1391591 := bstep (se 1 (by rfl) ⟨1043693, by rfl⟩ : syracuseStep 1391591 = 2087387) B2087387
theorem B3390587 : Blo 1391515 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B2088155 : Blo 1391515 2088155 := bstep (se 1 (by rfl) ⟨1566116, by rfl⟩ : syracuseStep 2088155 = 3132233) B3132233
theorem B7052507 : Blo 1391515 7052507 := bstep (se 1 (by rfl) ⟨5289380, by rfl⟩ : syracuseStep 7052507 = 10578761) B10578761
theorem B1391903 : Blo 1391515 1391903 := bstep (se 1 (by rfl) ⟨1043927, by rfl⟩ : syracuseStep 1391903 = 2087855) B2087855
theorem B1391963 : Blo 1391515 1391963 := bstep (se 1 (by rfl) ⟨1043972, by rfl⟩ : syracuseStep 1391963 = 2087945) B2087945
theorem B1391983 : Blo 1391515 1391983 := bstep (se 1 (by rfl) ⟨1043987, by rfl⟩ : syracuseStep 1391983 = 2087975) B2087975
theorem B2088329 : Blo 1391515 2088329 := bstep (se 2 (by rfl) ⟨783123, by rfl⟩ : syracuseStep 2088329 = 1566247) B1566247
theorem B15670691 : Blo 1391515 15670691 := bstep (se 1 (by rfl) ⟨11753018, by rfl⟩ : syracuseStep 15670691 = 23506037) B23506037
theorem B1392039 : Blo 1391515 1392039 := bstep (se 1 (by rfl) ⟨1044029, by rfl⟩ : syracuseStep 1392039 = 2088059) B2088059
theorem B110042549 : Blo 1391515 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B1392123 : Blo 1391515 1392123 := bstep (se 1 (by rfl) ⟨1044092, by rfl⟩ : syracuseStep 1392123 = 2088185) B2088185
theorem B1392191 : Blo 1391515 1392191 := bstep (se 1 (by rfl) ⟨1044143, by rfl⟩ : syracuseStep 1392191 = 2088287) B2088287
theorem B1392199 : Blo 1391515 1392199 := bstep (se 1 (by rfl) ⟨1044149, by rfl⟩ : syracuseStep 1392199 = 2088299) B2088299
theorem B4701779 : Blo 1391515 4701779 := bstep (se 1 (by rfl) ⟨3526334, by rfl⟩ : syracuseStep 4701779 = 7052669) B7052669
theorem B2350687 : Blo 1391515 2350687 := bstep (se 1 (by rfl) ⟨1763015, by rfl⟩ : syracuseStep 2350687 = 3526031) B3526031
theorem B13557395 : Blo 1391515 13557395 := bstep (se 1 (by rfl) ⟨10168046, by rfl⟩ : syracuseStep 13557395 = 20336093) B20336093
theorem B4234913 : Blo 1391515 4234913 := bstep (se 2 (by rfl) ⟨1588092, by rfl⟩ : syracuseStep 4234913 = 3176185) B3176185
theorem B5021345 : Blo 1391515 5021345 := bstep (se 2 (by rfl) ⟨1883004, by rfl⟩ : syracuseStep 5021345 = 3766009) B3766009
theorem B1392351 : Blo 1391515 1392351 := bstep (se 1 (by rfl) ⟨1044263, by rfl⟩ : syracuseStep 1392351 = 2088527) B2088527
theorem B2088683 : Blo 1391515 2088683 := bstep (se 1 (by rfl) ⟨1566512, by rfl⟩ : syracuseStep 2088683 = 3133025) B3133025
theorem B1392431 : Blo 1391515 1392431 := bstep (se 1 (by rfl) ⟨1044323, by rfl⟩ : syracuseStep 1392431 = 2088647) B2088647
theorem B6692665 : Blo 1391515 6692665 := bstep (se 2 (by rfl) ⟨2509749, by rfl⟩ : syracuseStep 6692665 = 5019499) B5019499
theorem B2350903 : Blo 1391515 2350903 := bstep (se 1 (by rfl) ⟨1763177, by rfl⟩ : syracuseStep 2350903 = 3526355) B3526355
theorem B1392539 : Blo 1391515 1392539 := bstep (se 1 (by rfl) ⟨1044404, by rfl⟩ : syracuseStep 1392539 = 2088809) B2088809
theorem B1392591 : Blo 1391515 1392591 := bstep (se 1 (by rfl) ⟨1044443, by rfl⟩ : syracuseStep 1392591 = 2088887) B2088887
theorem B2088911 : Blo 1391515 2088911 := bstep (se 1 (by rfl) ⟨1566683, by rfl⟩ : syracuseStep 2088911 = 3133367) B3133367
theorem B1392615 : Blo 1391515 1392615 := bstep (se 1 (by rfl) ⟨1044461, by rfl⟩ : syracuseStep 1392615 = 2088923) B2088923
theorem B3522599 : Blo 1391515 3522599 := bstep (se 1 (by rfl) ⟨2641949, by rfl⟩ : syracuseStep 3522599 = 5283899) B5283899
theorem B4702427 : Blo 1391515 4702427 := bstep (se 1 (by rfl) ⟨3526820, by rfl⟩ : syracuseStep 4702427 = 7053641) B7053641
theorem B3522791 : Blo 1391515 3522791 := bstep (se 1 (by rfl) ⟨2642093, by rfl⟩ : syracuseStep 3522791 = 5284187) B5284187
theorem B1392871 : Blo 1391515 1392871 := bstep (se 1 (by rfl) ⟨1044653, by rfl⟩ : syracuseStep 1392871 = 2089307) B2089307
theorem B2351335 : Blo 1391515 2351335 := bstep (se 1 (by rfl) ⟨1763501, by rfl⟩ : syracuseStep 2351335 = 3527003) B3527003
theorem B2089247 : Blo 1391515 2089247 := bstep (se 1 (by rfl) ⟨1566935, by rfl⟩ : syracuseStep 2089247 = 3133871) B3133871
theorem B2089271 : Blo 1391515 2089271 := bstep (se 1 (by rfl) ⟨1566953, by rfl⟩ : syracuseStep 2089271 = 3133907) B3133907
theorem B2089343 : Blo 1391515 2089343 := bstep (se 1 (by rfl) ⟨1567007, by rfl⟩ : syracuseStep 2089343 = 3134015) B3134015
theorem B1393023 : Blo 1391515 1393023 := bstep (se 1 (by rfl) ⟨1044767, by rfl⟩ : syracuseStep 1393023 = 2089535) B2089535
theorem B2351497 : Blo 1391515 2351497 := bstep (se 2 (by rfl) ⟨881811, by rfl⟩ : syracuseStep 2351497 = 1763623) B1763623
theorem B2089415 : Blo 1391515 2089415 := bstep (se 1 (by rfl) ⟨1567061, by rfl⟩ : syracuseStep 2089415 = 3134123) B3134123
theorem B1393103 : Blo 1391515 1393103 := bstep (se 1 (by rfl) ⟨1044827, by rfl⟩ : syracuseStep 1393103 = 2089655) B2089655
theorem B4702697 : Blo 1391515 4702697 := bstep (se 2 (by rfl) ⟨1763511, by rfl⟩ : syracuseStep 4702697 = 3527023) B3527023
theorem B11895335 : Blo 1391515 11895335 := bstep (se 1 (by rfl) ⟨8921501, by rfl⟩ : syracuseStep 11895335 = 17843003) B17843003
theorem B1393255 : Blo 1391515 1393255 := bstep (se 1 (by rfl) ⟨1044941, by rfl⟩ : syracuseStep 1393255 = 2089883) B2089883
theorem B2089769 : Blo 1391515 2089769 := bstep (se 2 (by rfl) ⟨783663, by rfl⟩ : syracuseStep 2089769 = 1567327) B1567327
theorem B2679599 : Blo 1391515 2679599 := bstep (se 1 (by rfl) ⟨2009699, by rfl⟩ : syracuseStep 2679599 = 4019399) B4019399
theorem B2089775 : Blo 1391515 2089775 := bstep (se 1 (by rfl) ⟨1567331, by rfl⟩ : syracuseStep 2089775 = 3134663) B3134663
theorem B2229049 : Blo 1391515 2229049 := bstep (se 2 (by rfl) ⟨835893, by rfl⟩ : syracuseStep 2229049 = 1671787) B1671787
theorem B10036025 : Blo 1391515 10036025 := bstep (se 2 (by rfl) ⟨3763509, by rfl⟩ : syracuseStep 10036025 = 7527019) B7527019
theorem B3523439 : Blo 1391515 3523439 := bstep (se 1 (by rfl) ⟨2642579, by rfl⟩ : syracuseStep 3523439 = 5285159) B5285159
theorem B3965851 : Blo 1391515 3965851 := bstep (se 1 (by rfl) ⟨2974388, by rfl⟩ : syracuseStep 3965851 = 5948777) B5948777
theorem B2089895 : Blo 1391515 2089895 := bstep (se 1 (by rfl) ⟨1567421, by rfl⟩ : syracuseStep 2089895 = 3134843) B3134843
theorem B2089979 : Blo 1391515 2089979 := bstep (se 1 (by rfl) ⟨1567484, by rfl⟩ : syracuseStep 2089979 = 3134969) B3134969
theorem B2090039 : Blo 1391515 2090039 := bstep (se 1 (by rfl) ⟨1567529, by rfl⟩ : syracuseStep 2090039 = 3135059) B3135059
theorem B4523131 : Blo 1391515 4523131 := bstep (se 1 (by rfl) ⟨3392348, by rfl⟩ : syracuseStep 4523131 = 6784697) B6784697
theorem B2090159 : Blo 1391515 2090159 := bstep (se 1 (by rfl) ⟨1567619, by rfl⟩ : syracuseStep 2090159 = 3135239) B3135239
theorem B4760783 : Blo 1391515 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B17163713 : Blo 1391515 17163713 := bstep (se 2 (by rfl) ⟨6436392, by rfl⟩ : syracuseStep 17163713 = 12872785) B12872785
theorem B7046675 : Blo 1391515 7046675 := bstep (se 1 (by rfl) ⟨5285006, by rfl⟩ : syracuseStep 7046675 = 10570013) B10570013
theorem B7931429 : Blo 1391515 7931429 := bstep (se 4 (by rfl) ⟨743571, by rfl⟩ : syracuseStep 7931429 = 1487143) B1487143
theorem B3130991 : Blo 1391515 3130991 := bstep (se 1 (by rfl) ⟨2348243, by rfl⟩ : syracuseStep 3130991 = 4696487) B4696487
theorem B2008687 : Blo 1391515 2008687 := bstep (se 1 (by rfl) ⟨1506515, by rfl⟩ : syracuseStep 2008687 = 3013031) B3013031
theorem B1566319 : Blo 1391515 1566319 := bstep (se 1 (by rfl) ⟨1174739, by rfl⟩ : syracuseStep 1566319 = 2349479) B2349479
theorem B146613883 : Blo 1391515 146613883 := bstep (se 1 (by rfl) ⟨109960412, by rfl⟩ : syracuseStep 146613883 = 219920825) B219920825
theorem B23807681 : Blo 1391515 23807681 := bstep (se 2 (by rfl) ⟨8927880, by rfl⟩ : syracuseStep 23807681 = 17855761) B17855761
theorem B3131099 : Blo 1391515 3131099 := bstep (se 1 (by rfl) ⟨2348324, by rfl⟩ : syracuseStep 3131099 = 4696649) B4696649
theorem B1566427 : Blo 1391515 1566427 := bstep (se 1 (by rfl) ⟨1174820, by rfl⟩ : syracuseStep 1566427 = 2349641) B2349641
theorem B11904731 : Blo 1391515 11904731 := bstep (se 1 (by rfl) ⟨8928548, by rfl⟩ : syracuseStep 11904731 = 17857097) B17857097
theorem B10569527 : Blo 1391515 10569527 := bstep (se 1 (by rfl) ⟨7927145, by rfl⟩ : syracuseStep 10569527 = 15854291) B15854291
theorem B3524431 : Blo 1391515 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B20072285 : Blo 1391515 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B5949359 : Blo 1391515 5949359 := bstep (se 1 (by rfl) ⟨4462019, by rfl⟩ : syracuseStep 5949359 = 8924039) B8924039
theorem B7932113 : Blo 1391515 7932113 := bstep (se 2 (by rfl) ⟨2974542, by rfl⟩ : syracuseStep 7932113 = 5949085) B5949085
theorem B2230535 : Blo 1391515 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B10447127 : Blo 1391515 10447127 := bstep (se 1 (by rfl) ⟨7835345, by rfl⟩ : syracuseStep 10447127 = 15670691) B15670691
theorem B73361699 : Blo 1391515 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B8923553 : Blo 1391515 8923553 := bstep (se 2 (by rfl) ⟨3346332, by rfl⟩ : syracuseStep 8923553 = 6692665) B6692665
theorem B9038263 : Blo 1391515 9038263 := bstep (se 1 (by rfl) ⟨6778697, by rfl⟩ : syracuseStep 9038263 = 13557395) B13557395
theorem B4459009 : Blo 1391515 4459009 := bstep (se 2 (by rfl) ⟨1672128, by rfl⟩ : syracuseStep 4459009 = 3344257) B3344257
theorem B25758281 : Blo 1391515 25758281 := bstep (se 2 (by rfl) ⟨9659355, by rfl⟩ : syracuseStep 25758281 = 19318711) B19318711
theorem B247376663 : Blo 1391515 247376663 := bstep (se 1 (by rfl) ⟨185532497, by rfl⟩ : syracuseStep 247376663 = 371064995) B371064995
theorem B3132215 : Blo 1391515 3132215 := bstep (se 1 (by rfl) ⟨2349161, by rfl⟩ : syracuseStep 3132215 = 4698323) B4698323
theorem B4696919 : Blo 1391515 4696919 := bstep (se 1 (by rfl) ⟨3522689, by rfl⟩ : syracuseStep 4696919 = 7045379) B7045379
theorem B1567579 : Blo 1391515 1567579 := bstep (se 1 (by rfl) ⟨1175684, by rfl⟩ : syracuseStep 1567579 = 2351369) B2351369
theorem B3132395 : Blo 1391515 3132395 := bstep (se 1 (by rfl) ⟨2349296, by rfl⟩ : syracuseStep 3132395 = 4698593) B4698593
theorem B4697135 : Blo 1391515 4697135 := bstep (se 1 (by rfl) ⟨3522851, by rfl⟩ : syracuseStep 4697135 = 7045703) B7045703
theorem B2509871 : Blo 1391515 2509871 := bstep (se 1 (by rfl) ⟨1882403, by rfl⟩ : syracuseStep 2509871 = 3764807) B3764807
theorem B3763423 : Blo 1391515 3763423 := bstep (se 1 (by rfl) ⟨2822567, by rfl⟩ : syracuseStep 3763423 = 5645135) B5645135
theorem B11291891 : Blo 1391515 11291891 := bstep (se 1 (by rfl) ⟨8468918, by rfl⟩ : syracuseStep 11291891 = 16937837) B16937837
theorem B4697513 : Blo 1391515 4697513 := bstep (se 2 (by rfl) ⟨1761567, by rfl⟩ : syracuseStep 4697513 = 3523135) B3523135
theorem B2510327 : Blo 1391515 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B8146427 : Blo 1391515 8146427 := bstep (se 1 (by rfl) ⟨6109820, by rfl⟩ : syracuseStep 8146427 = 12219641) B12219641
theorem B28602065 : Blo 1391515 28602065 := bstep (se 2 (by rfl) ⟨10725774, by rfl⟩ : syracuseStep 28602065 = 21451549) B21451549
theorem B22572755 : Blo 1391515 22572755 := bstep (se 1 (by rfl) ⟨16929566, by rfl⟩ : syracuseStep 22572755 = 33859133) B33859133
theorem B3133223 : Blo 1391515 3133223 := bstep (se 1 (by rfl) ⟨2349917, by rfl⟩ : syracuseStep 3133223 = 4699835) B4699835
theorem B4697999 : Blo 1391515 4697999 := bstep (se 1 (by rfl) ⟨3523499, by rfl⟩ : syracuseStep 4697999 = 7046999) B7046999
theorem B5648573 : Blo 1391515 5648573 := bstep (se 3 (by rfl) ⟨1059107, by rfl⟩ : syracuseStep 5648573 = 2118215) B2118215
theorem B4698377 : Blo 1391515 4698377 := bstep (se 2 (by rfl) ⟨1761891, by rfl⟩ : syracuseStep 4698377 = 3523783) B3523783
theorem B2822455 : Blo 1391515 2822455 := bstep (se 1 (by rfl) ⟨2116841, by rfl⟩ : syracuseStep 2822455 = 4233683) B4233683
theorem B5804623 : Blo 1391515 5804623 := bstep (se 1 (by rfl) ⟨4353467, by rfl⟩ : syracuseStep 5804623 = 8706935) B8706935
theorem B9532075 : Blo 1391515 9532075 := bstep (se 1 (by rfl) ⟨7149056, by rfl⟩ : syracuseStep 9532075 = 14298113) B14298113
theorem B3134249 : Blo 1391515 3134249 := bstep (se 2 (by rfl) ⟨1175343, by rfl⟩ : syracuseStep 3134249 = 2350687) B2350687
theorem B11899709 : Blo 1391515 11899709 := bstep (se 3 (by rfl) ⟨2231195, by rfl⟩ : syracuseStep 11899709 = 4462391) B4462391
theorem B3134519 : Blo 1391515 3134519 := bstep (se 1 (by rfl) ⟨2350889, by rfl⟩ : syracuseStep 3134519 = 4701779) B4701779
theorem B3134537 : Blo 1391515 3134537 := bstep (se 2 (by rfl) ⟨1175451, by rfl⟩ : syracuseStep 3134537 = 2350903) B2350903
theorem B2823275 : Blo 1391515 2823275 := bstep (se 1 (by rfl) ⟨2117456, by rfl⟩ : syracuseStep 2823275 = 4234913) B4234913
theorem B3347563 : Blo 1391515 3347563 := bstep (se 1 (by rfl) ⟨2510672, by rfl⟩ : syracuseStep 3347563 = 5021345) B5021345
theorem B1488079 : Blo 1391515 1488079 := bstep (se 1 (by rfl) ⟨1116059, by rfl⟩ : syracuseStep 1488079 = 2232119) B2232119
theorem B4699511 : Blo 1391515 4699511 := bstep (se 1 (by rfl) ⟨3524633, by rfl⟩ : syracuseStep 4699511 = 7049267) B7049267
theorem B10040699 : Blo 1391515 10040699 := bstep (se 1 (by rfl) ⟨7530524, by rfl⟩ : syracuseStep 10040699 = 15061049) B15061049
theorem B2413979 : Blo 1391515 2413979 := bstep (se 1 (by rfl) ⟨1810484, by rfl⟩ : syracuseStep 2413979 = 3620969) B3620969
theorem B2348615 : Blo 1391515 2348615 := bstep (se 1 (by rfl) ⟨1761461, by rfl⟩ : syracuseStep 2348615 = 3522923) B3522923
theorem B2176633 : Blo 1391515 2176633 := bstep (se 2 (by rfl) ⟨816237, by rfl⟩ : syracuseStep 2176633 = 1632475) B1632475
theorem B7526155 : Blo 1391515 7526155 := bstep (se 1 (by rfl) ⟨5644616, by rfl⟩ : syracuseStep 7526155 = 11289233) B11289233
theorem B2348831 : Blo 1391515 2348831 := bstep (se 1 (by rfl) ⟨1761623, by rfl⟩ : syracuseStep 2348831 = 3523247) B3523247
theorem B2381705 : Blo 1391515 2381705 := bstep (se 2 (by rfl) ⟨893139, by rfl⟩ : syracuseStep 2381705 = 1786279) B1786279
theorem B2349047 : Blo 1391515 2349047 := bstep (se 1 (by rfl) ⟨1761785, by rfl⟩ : syracuseStep 2349047 = 3523571) B3523571
theorem B8919065 : Blo 1391515 8919065 := bstep (se 2 (by rfl) ⟨3344649, by rfl⟩ : syracuseStep 8919065 = 6689299) B6689299
theorem B5019731 : Blo 1391515 5019731 := bstep (se 1 (by rfl) ⟨3764798, by rfl⟩ : syracuseStep 5019731 = 7529597) B7529597
theorem B4700321 : Blo 1391515 4700321 := bstep (se 2 (by rfl) ⟨1762620, by rfl⟩ : syracuseStep 4700321 = 3525241) B3525241
theorem B5290217 : Blo 1391515 5290217 := bstep (se 2 (by rfl) ⟨1983831, by rfl⟩ : syracuseStep 5290217 = 3967663) B3967663
theorem B3389683 : Blo 1391515 3389683 := bstep (se 1 (by rfl) ⟨2542262, by rfl⟩ : syracuseStep 3389683 = 5084525) B5084525
theorem B34355447 : Blo 1391515 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B2644265 : Blo 1391515 2644265 := bstep (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) B1983199
theorem B2087291 : Blo 1391515 2087291 := bstep (se 1 (by rfl) ⟨1565468, by rfl⟩ : syracuseStep 2087291 = 3130937) B3130937
theorem B4700591 : Blo 1391515 4700591 := bstep (se 1 (by rfl) ⟨3525443, by rfl⟩ : syracuseStep 4700591 = 7050887) B7050887
theorem B2087561 : Blo 1391515 2087561 := bstep (se 2 (by rfl) ⟨782835, by rfl⟩ : syracuseStep 2087561 = 1565671) B1565671
theorem B2087735 : Blo 1391515 2087735 := bstep (se 1 (by rfl) ⟨1565801, by rfl⟩ : syracuseStep 2087735 = 3131603) B3131603
theorem B2087771 : Blo 1391515 2087771 := bstep (se 1 (by rfl) ⟨1565828, by rfl⟩ : syracuseStep 2087771 = 3131657) B3131657
theorem B1391519 : Blo 1391515 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B2087915 : Blo 1391515 2087915 := bstep (se 1 (by rfl) ⟨1565936, by rfl⟩ : syracuseStep 2087915 = 3131873) B3131873
theorem B180689939 : Blo 1391515 180689939 := bstep (se 1 (by rfl) ⟨135517454, by rfl⟩ : syracuseStep 180689939 = 271034909) B271034909
theorem B1391663 : Blo 1391515 1391663 := bstep (se 1 (by rfl) ⟨1043747, by rfl⟩ : syracuseStep 1391663 = 2087495) B2087495
theorem B2350127 : Blo 1391515 2350127 := bstep (se 1 (by rfl) ⟨1762595, by rfl⟩ : syracuseStep 2350127 = 3525191) B3525191
theorem B7052345 : Blo 1391515 7052345 := bstep (se 2 (by rfl) ⟨2644629, by rfl⟩ : syracuseStep 7052345 = 5289259) B5289259
theorem B1391687 : Blo 1391515 1391687 := bstep (se 1 (by rfl) ⟨1043765, by rfl⟩ : syracuseStep 1391687 = 2087531) B2087531
theorem B2350201 : Blo 1391515 2350201 := bstep (se 2 (by rfl) ⟨881325, by rfl⟩ : syracuseStep 2350201 = 1762651) B1762651
theorem B2088119 : Blo 1391515 2088119 := bstep (se 1 (by rfl) ⟨1566089, by rfl⟩ : syracuseStep 2088119 = 3132179) B3132179
theorem B1391839 : Blo 1391515 1391839 := bstep (se 1 (by rfl) ⟨1043879, by rfl⟩ : syracuseStep 1391839 = 2087759) B2087759
theorem B4767137 : Blo 1391515 4767137 := bstep (se 2 (by rfl) ⟨1787676, by rfl⟩ : syracuseStep 4767137 = 3575353) B3575353
theorem B2260391 : Blo 1391515 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B2088359 : Blo 1391515 2088359 := bstep (se 1 (by rfl) ⟨1566269, by rfl⟩ : syracuseStep 2088359 = 3132539) B3132539
theorem B2350505 : Blo 1391515 2350505 := bstep (se 2 (by rfl) ⟨881439, by rfl⟩ : syracuseStep 2350505 = 1762879) B1762879
theorem B1392103 : Blo 1391515 1392103 := bstep (se 1 (by rfl) ⟨1044077, by rfl⟩ : syracuseStep 1392103 = 2088155) B2088155
theorem B4234727 : Blo 1391515 4234727 := bstep (se 1 (by rfl) ⟨3176045, by rfl⟩ : syracuseStep 4234727 = 6352091) B6352091
theorem B4701671 : Blo 1391515 4701671 := bstep (se 1 (by rfl) ⟨3526253, by rfl⟩ : syracuseStep 4701671 = 7052507) B7052507
theorem B2088443 : Blo 1391515 2088443 := bstep (se 1 (by rfl) ⟨1566332, by rfl⟩ : syracuseStep 2088443 = 3132665) B3132665
theorem B1392219 : Blo 1391515 1392219 := bstep (se 1 (by rfl) ⟨1044164, by rfl⟩ : syracuseStep 1392219 = 2088329) B2088329
theorem B2088539 : Blo 1391515 2088539 := bstep (se 1 (by rfl) ⟨1566404, by rfl⟩ : syracuseStep 2088539 = 3132809) B3132809
theorem B2088623 : Blo 1391515 2088623 := bstep (se 1 (by rfl) ⟨1566467, by rfl⟩ : syracuseStep 2088623 = 3132935) B3132935
theorem B2088743 : Blo 1391515 2088743 := bstep (se 1 (by rfl) ⟨1566557, by rfl⟩ : syracuseStep 2088743 = 3133115) B3133115
theorem B1392455 : Blo 1391515 1392455 := bstep (se 1 (by rfl) ⟨1044341, by rfl⟩ : syracuseStep 1392455 = 2088683) B2088683
theorem B2088827 : Blo 1391515 2088827 := bstep (se 1 (by rfl) ⟨1566620, by rfl⟩ : syracuseStep 2088827 = 3133241) B3133241
theorem B1392607 : Blo 1391515 1392607 := bstep (se 1 (by rfl) ⟨1044455, by rfl⟩ : syracuseStep 1392607 = 2088911) B2088911
theorem B10575845 : Blo 1391515 10575845 := bstep (se 4 (by rfl) ⟨991485, by rfl⟩ : syracuseStep 10575845 = 1982971) B1982971
theorem B1392831 : Blo 1391515 1392831 := bstep (se 1 (by rfl) ⟨1044623, by rfl⟩ : syracuseStep 1392831 = 2089247) B2089247
theorem B1392847 : Blo 1391515 1392847 := bstep (se 1 (by rfl) ⟨1044635, by rfl⟩ : syracuseStep 1392847 = 2089271) B2089271
theorem B1392895 : Blo 1391515 1392895 := bstep (se 1 (by rfl) ⟨1044671, by rfl⟩ : syracuseStep 1392895 = 2089343) B2089343
theorem B7528733 : Blo 1391515 7528733 := bstep (se 3 (by rfl) ⟨1411637, by rfl⟩ : syracuseStep 7528733 = 2823275) B2823275
theorem B1392943 : Blo 1391515 1392943 := bstep (se 1 (by rfl) ⟨1044707, by rfl⟩ : syracuseStep 1392943 = 2089415) B2089415
theorem B7930223 : Blo 1391515 7930223 := bstep (se 1 (by rfl) ⟨5947667, by rfl⟩ : syracuseStep 7930223 = 11895335) B11895335
theorem B26771957 : Blo 1391515 26771957 := bstep (se 5 (by rfl) ⟨1254935, by rfl⟩ : syracuseStep 26771957 = 2509871) B2509871
theorem B2089499 : Blo 1391515 2089499 := bstep (se 1 (by rfl) ⟨1567124, by rfl⟩ : syracuseStep 2089499 = 3134249) B3134249
theorem B1393179 : Blo 1391515 1393179 := bstep (se 1 (by rfl) ⟨1044884, by rfl⟩ : syracuseStep 1393179 = 2089769) B2089769
theorem B1393183 : Blo 1391515 1393183 := bstep (se 1 (by rfl) ⟨1044887, by rfl⟩ : syracuseStep 1393183 = 2089775) B2089775
theorem B12051017 : Blo 1391515 12051017 := bstep (se 2 (by rfl) ⟨4519131, by rfl⟩ : syracuseStep 12051017 = 9038263) B9038263
theorem B1393263 : Blo 1391515 1393263 := bstep (se 1 (by rfl) ⟨1044947, by rfl⟩ : syracuseStep 1393263 = 2089895) B2089895
theorem B1393319 : Blo 1391515 1393319 := bstep (se 1 (by rfl) ⟨1044989, by rfl⟩ : syracuseStep 1393319 = 2089979) B2089979
theorem B5948093 : Blo 1391515 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B2089679 : Blo 1391515 2089679 := bstep (se 1 (by rfl) ⟨1567259, by rfl⟩ : syracuseStep 2089679 = 3134519) B3134519
theorem B1393359 : Blo 1391515 1393359 := bstep (se 1 (by rfl) ⟨1045019, by rfl⟩ : syracuseStep 1393359 = 2090039) B2090039
theorem B2089691 : Blo 1391515 2089691 := bstep (se 1 (by rfl) ⟨1567268, by rfl⟩ : syracuseStep 2089691 = 3134537) B3134537
theorem B1393439 : Blo 1391515 1393439 := bstep (se 1 (by rfl) ⟨1045079, by rfl⟩ : syracuseStep 1393439 = 2090159) B2090159
theorem B6693799 : Blo 1391515 6693799 := bstep (se 1 (by rfl) ⟨5020349, by rfl⟩ : syracuseStep 6693799 = 10040699) B10040699
theorem B1565743 : Blo 1391515 1565743 := bstep (se 1 (by rfl) ⟨1174307, by rfl⟩ : syracuseStep 1565743 = 2348615) B2348615
theorem B2090105 : Blo 1391515 2090105 := bstep (se 2 (by rfl) ⟨783789, by rfl⟩ : syracuseStep 2090105 = 1567579) B1567579
theorem B1565887 : Blo 1391515 1565887 := bstep (se 1 (by rfl) ⟨1174415, by rfl⟩ : syracuseStep 1565887 = 2348831) B2348831
theorem B7046351 : Blo 1391515 7046351 := bstep (se 1 (by rfl) ⟨5284763, by rfl⟩ : syracuseStep 7046351 = 10569527) B10569527
theorem B3966239 : Blo 1391515 3966239 := bstep (se 1 (by rfl) ⟨2974679, by rfl⟩ : syracuseStep 3966239 = 5949359) B5949359
theorem B1566031 : Blo 1391515 1566031 := bstep (se 1 (by rfl) ⟨1174523, by rfl⟩ : syracuseStep 1566031 = 2349047) B2349047
theorem B25404853 : Blo 1391515 25404853 := bstep (se 5 (by rfl) ⟨1190852, by rfl⟩ : syracuseStep 25404853 = 2381705) B2381705
theorem B6030841 : Blo 1391515 6030841 := bstep (se 2 (by rfl) ⟨2261565, by rfl⟩ : syracuseStep 6030841 = 4523131) B4523131
theorem B6964751 : Blo 1391515 6964751 := bstep (se 1 (by rfl) ⟨5223563, by rfl⟩ : syracuseStep 6964751 = 10447127) B10447127
theorem B48907799 : Blo 1391515 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B1984105 : Blo 1391515 1984105 := bstep (se 2 (by rfl) ⟨744039, by rfl⟩ : syracuseStep 1984105 = 1488079) B1488079
theorem B5949035 : Blo 1391515 5949035 := bstep (se 1 (by rfl) ⟨4461776, by rfl⟩ : syracuseStep 5949035 = 8923553) B8923553
theorem B3131279 : Blo 1391515 3131279 := bstep (se 1 (by rfl) ⟨2348459, by rfl⟩ : syracuseStep 3131279 = 4696919) B4696919
theorem B3131423 : Blo 1391515 3131423 := bstep (se 1 (by rfl) ⟨2348567, by rfl⟩ : syracuseStep 3131423 = 4697135) B4697135
theorem B1566751 : Blo 1391515 1566751 := bstep (se 1 (by rfl) ⟨1175063, by rfl⟩ : syracuseStep 1566751 = 2350127) B2350127
theorem B7145597 : Blo 1391515 7145597 := bstep (se 3 (by rfl) ⟨1339799, by rfl⟩ : syracuseStep 7145597 = 2679599) B2679599
theorem B2902177 : Blo 1391515 2902177 := bstep (se 2 (by rfl) ⟨1088316, by rfl⟩ : syracuseStep 2902177 = 2176633) B2176633
theorem B3131675 : Blo 1391515 3131675 := bstep (se 1 (by rfl) ⟨2348756, by rfl⟩ : syracuseStep 3131675 = 4697513) B4697513
theorem B1567003 : Blo 1391515 1567003 := bstep (se 1 (by rfl) ⟨1175252, by rfl⟩ : syracuseStep 1567003 = 2350505) B2350505
theorem B1673551 : Blo 1391515 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B3131999 : Blo 1391515 3131999 := bstep (se 1 (by rfl) ⟨2348999, by rfl⟩ : syracuseStep 3131999 = 4697999) B4697999
theorem B3132251 : Blo 1391515 3132251 := bstep (se 1 (by rfl) ⟨2349188, by rfl⟩ : syracuseStep 3132251 = 4698377) B4698377
theorem B3763273 : Blo 1391515 3763273 := bstep (se 2 (by rfl) ⟨1411227, by rfl⟩ : syracuseStep 3763273 = 2822455) B2822455
theorem B7933139 : Blo 1391515 7933139 := bstep (se 1 (by rfl) ⟨5949854, by rfl⟩ : syracuseStep 7933139 = 11899709) B11899709
theorem B3173855 : Blo 1391515 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B12709433 : Blo 1391515 12709433 := bstep (se 2 (by rfl) ⟨4766037, by rfl⟩ : syracuseStep 12709433 = 9532075) B9532075
theorem B3133007 : Blo 1391515 3133007 := bstep (se 1 (by rfl) ⟨2349755, by rfl⟩ : syracuseStep 3133007 = 4699511) B4699511
theorem B1609319 : Blo 1391515 1609319 := bstep (se 1 (by rfl) ⟨1206989, by rfl⟩ : syracuseStep 1609319 = 2413979) B2413979
theorem B4697783 : Blo 1391515 4697783 := bstep (se 1 (by rfl) ⟨3523337, by rfl⟩ : syracuseStep 4697783 = 7046675) B7046675
theorem B5287619 : Blo 1391515 5287619 := bstep (se 1 (by rfl) ⟨3965714, by rfl⟩ : syracuseStep 5287619 = 7931429) B7931429
theorem B15871787 : Blo 1391515 15871787 := bstep (se 1 (by rfl) ⟨11903840, by rfl⟩ : syracuseStep 15871787 = 23807681) B23807681
theorem B5287801 : Blo 1391515 5287801 := bstep (se 2 (by rfl) ⟨1982925, by rfl⟩ : syracuseStep 5287801 = 3965851) B3965851
theorem B13381523 : Blo 1391515 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B11292605 : Blo 1391515 11292605 := bstep (se 3 (by rfl) ⟨2117363, by rfl⟩ : syracuseStep 11292605 = 4234727) B4234727
theorem B3346487 : Blo 1391515 3346487 := bstep (se 1 (by rfl) ⟨2509865, by rfl⟩ : syracuseStep 3346487 = 5019731) B5019731
theorem B3133547 : Blo 1391515 3133547 := bstep (se 1 (by rfl) ⟨2350160, by rfl⟩ : syracuseStep 3133547 = 4700321) B4700321
theorem B5288075 : Blo 1391515 5288075 := bstep (se 1 (by rfl) ⟨3966056, by rfl⟩ : syracuseStep 5288075 = 7932113) B7932113
theorem B3526811 : Blo 1391515 3526811 := bstep (se 1 (by rfl) ⟨2645108, by rfl⟩ : syracuseStep 3526811 = 5290217) B5290217
theorem B3133601 : Blo 1391515 3133601 := bstep (se 2 (by rfl) ⟨1175100, by rfl⟩ : syracuseStep 3133601 = 2350201) B2350201
theorem B3133727 : Blo 1391515 3133727 := bstep (se 1 (by rfl) ⟨2350295, by rfl⟩ : syracuseStep 3133727 = 4700591) B4700591
theorem B5017897 : Blo 1391515 5017897 := bstep (se 2 (by rfl) ⟨1881711, by rfl⟩ : syracuseStep 5017897 = 3763423) B3763423
theorem B164917775 : Blo 1391515 164917775 := bstep (se 1 (by rfl) ⟨123688331, by rfl⟩ : syracuseStep 164917775 = 247376663) B247376663
theorem B120459959 : Blo 1391515 120459959 := bstep (se 1 (by rfl) ⟨90344969, by rfl⟩ : syracuseStep 120459959 = 180689939) B180689939
theorem B3134447 : Blo 1391515 3134447 := bstep (se 1 (by rfl) ⟨2350835, by rfl⟩ : syracuseStep 3134447 = 4701671) B4701671
theorem B4699241 : Blo 1391515 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B19068043 : Blo 1391515 19068043 := bstep (se 1 (by rfl) ⟨14301032, by rfl⟩ : syracuseStep 19068043 = 28602065) B28602065
theorem B7050563 : Blo 1391515 7050563 := bstep (se 1 (by rfl) ⟨5287922, by rfl⟩ : syracuseStep 7050563 = 10575845) B10575845
theorem B2348399 : Blo 1391515 2348399 := bstep (se 1 (by rfl) ⟨1761299, by rfl⟩ : syracuseStep 2348399 = 3522599) B3522599
theorem B3134951 : Blo 1391515 3134951 := bstep (se 1 (by rfl) ⟨2351213, by rfl⟩ : syracuseStep 3134951 = 4702427) B4702427
theorem B2348527 : Blo 1391515 2348527 := bstep (se 1 (by rfl) ⟨1761395, by rfl⟩ : syracuseStep 2348527 = 3522791) B3522791
theorem B3135113 : Blo 1391515 3135113 := bstep (se 2 (by rfl) ⟨1175667, by rfl⟩ : syracuseStep 3135113 = 2351335) B2351335
theorem B4519577 : Blo 1391515 4519577 := bstep (se 2 (by rfl) ⟨1694841, by rfl⟩ : syracuseStep 4519577 = 3389683) B3389683
theorem B3135131 : Blo 1391515 3135131 := bstep (se 1 (by rfl) ⟨2351348, by rfl⟩ : syracuseStep 3135131 = 4702697) B4702697
theorem B15062861 : Blo 1391515 15062861 := bstep (se 3 (by rfl) ⟨2824286, by rfl⟩ : syracuseStep 15062861 = 5648573) B5648573
theorem B3135329 : Blo 1391515 3135329 := bstep (se 2 (by rfl) ⟨1175748, by rfl⟩ : syracuseStep 3135329 = 2351497) B2351497
theorem B6690683 : Blo 1391515 6690683 := bstep (se 1 (by rfl) ⟨5018012, by rfl⟩ : syracuseStep 6690683 = 10036025) B10036025
theorem B2348959 : Blo 1391515 2348959 := bstep (se 1 (by rfl) ⟨1761719, by rfl⟩ : syracuseStep 2348959 = 3523439) B3523439
theorem B30111709 : Blo 1391515 30111709 := bstep (se 3 (by rfl) ⟨5645945, by rfl⟩ : syracuseStep 30111709 = 11291891) B11291891
theorem B5945345 : Blo 1391515 5945345 := bstep (se 2 (by rfl) ⟨2229504, by rfl⟩ : syracuseStep 5945345 = 4459009) B4459009
theorem B7739497 : Blo 1391515 7739497 := bstep (se 2 (by rfl) ⟨2902311, by rfl⟩ : syracuseStep 7739497 = 5804623) B5804623
theorem B7051373 : Blo 1391515 7051373 := bstep (se 3 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 7051373 = 2644265) B2644265
theorem B11442475 : Blo 1391515 11442475 := bstep (se 1 (by rfl) ⟨8581856, by rfl⟩ : syracuseStep 11442475 = 17163713) B17163713
theorem B2087327 : Blo 1391515 2087327 := bstep (se 1 (by rfl) ⟨1565495, by rfl⟩ : syracuseStep 2087327 = 3130991) B3130991
theorem B2972065 : Blo 1391515 2972065 := bstep (se 2 (by rfl) ⟨1114524, by rfl⟩ : syracuseStep 2972065 = 2229049) B2229049
theorem B6027709 : Blo 1391515 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B2087399 : Blo 1391515 2087399 := bstep (se 1 (by rfl) ⟨1565549, by rfl⟩ : syracuseStep 2087399 = 3131099) B3131099
theorem B7936487 : Blo 1391515 7936487 := bstep (se 1 (by rfl) ⟨5952365, by rfl⟩ : syracuseStep 7936487 = 11904731) B11904731
theorem B21723805 : Blo 1391515 21723805 := bstep (se 3 (by rfl) ⟨4073213, by rfl⟩ : syracuseStep 21723805 = 8146427) B8146427
theorem B5946043 : Blo 1391515 5946043 := bstep (se 1 (by rfl) ⟨4459532, by rfl⟩ : syracuseStep 5946043 = 8919065) B8919065
theorem B4463417 : Blo 1391515 4463417 := bstep (se 2 (by rfl) ⟨1673781, by rfl⟩ : syracuseStep 4463417 = 3347563) B3347563
theorem B22903631 : Blo 1391515 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B68688749 : Blo 1391515 68688749 := bstep (se 3 (by rfl) ⟨12879140, by rfl⟩ : syracuseStep 68688749 = 25758281) B25758281
theorem B1391527 : Blo 1391515 1391527 := bstep (se 1 (by rfl) ⟨1043645, by rfl⟩ : syracuseStep 1391527 = 2087291) B2087291
theorem B1391707 : Blo 1391515 1391707 := bstep (se 1 (by rfl) ⟨1043780, by rfl⟩ : syracuseStep 1391707 = 2087561) B2087561
theorem B1391823 : Blo 1391515 1391823 := bstep (se 1 (by rfl) ⟨1043867, by rfl⟩ : syracuseStep 1391823 = 2087735) B2087735
theorem B2088143 : Blo 1391515 2088143 := bstep (se 1 (by rfl) ⟨1566107, by rfl⟩ : syracuseStep 2088143 = 3132215) B3132215
theorem B1391847 : Blo 1391515 1391847 := bstep (se 1 (by rfl) ⟨1043885, by rfl⟩ : syracuseStep 1391847 = 2087771) B2087771
theorem B1391943 : Blo 1391515 1391943 := bstep (se 1 (by rfl) ⟨1043957, by rfl⟩ : syracuseStep 1391943 = 2087915) B2087915
theorem B2088263 : Blo 1391515 2088263 := bstep (se 1 (by rfl) ⟨1566197, by rfl⟩ : syracuseStep 2088263 = 3132395) B3132395
theorem B4701563 : Blo 1391515 4701563 := bstep (se 1 (by rfl) ⟨3526172, by rfl⟩ : syracuseStep 4701563 = 7052345) B7052345
theorem B1392079 : Blo 1391515 1392079 := bstep (se 1 (by rfl) ⟨1044059, by rfl⟩ : syracuseStep 1392079 = 2088119) B2088119
theorem B2678249 : Blo 1391515 2678249 := bstep (se 2 (by rfl) ⟨1004343, by rfl⟩ : syracuseStep 2678249 = 2008687) B2008687
theorem B2088425 : Blo 1391515 2088425 := bstep (se 2 (by rfl) ⟨783159, by rfl⟩ : syracuseStep 2088425 = 1566319) B1566319
theorem B195485177 : Blo 1391515 195485177 := bstep (se 2 (by rfl) ⟨73306941, by rfl⟩ : syracuseStep 195485177 = 146613883) B146613883
theorem B3178091 : Blo 1391515 3178091 := bstep (se 1 (by rfl) ⟨2383568, by rfl⟩ : syracuseStep 3178091 = 4767137) B4767137
theorem B1392239 : Blo 1391515 1392239 := bstep (se 1 (by rfl) ⟨1044179, by rfl⟩ : syracuseStep 1392239 = 2088359) B2088359
theorem B2088569 : Blo 1391515 2088569 := bstep (se 2 (by rfl) ⟨783213, by rfl⟩ : syracuseStep 2088569 = 1566427) B1566427
theorem B1392295 : Blo 1391515 1392295 := bstep (se 1 (by rfl) ⟨1044221, by rfl⟩ : syracuseStep 1392295 = 2088443) B2088443
theorem B10034873 : Blo 1391515 10034873 := bstep (se 2 (by rfl) ⟨3763077, by rfl⟩ : syracuseStep 10034873 = 7526155) B7526155
theorem B1392359 : Blo 1391515 1392359 := bstep (se 1 (by rfl) ⟨1044269, by rfl⟩ : syracuseStep 1392359 = 2088539) B2088539
theorem B1392415 : Blo 1391515 1392415 := bstep (se 1 (by rfl) ⟨1044311, by rfl⟩ : syracuseStep 1392415 = 2088623) B2088623
theorem B15048503 : Blo 1391515 15048503 := bstep (se 1 (by rfl) ⟨11286377, by rfl⟩ : syracuseStep 15048503 = 22572755) B22572755
theorem B1392495 : Blo 1391515 1392495 := bstep (se 1 (by rfl) ⟨1044371, by rfl⟩ : syracuseStep 1392495 = 2088743) B2088743
theorem B2088815 : Blo 1391515 2088815 := bstep (se 1 (by rfl) ⟨1566611, by rfl⟩ : syracuseStep 2088815 = 3133223) B3133223
theorem B1392551 : Blo 1391515 1392551 := bstep (se 1 (by rfl) ⟨1044413, by rfl⟩ : syracuseStep 1392551 = 2088827) B2088827
theorem B2089001 : Blo 1391515 2089001 := bstep (se 2 (by rfl) ⟨783375, by rfl⟩ : syracuseStep 2089001 = 1566751) B1566751
theorem B2089031 : Blo 1391515 2089031 := bstep (se 1 (by rfl) ⟨1566773, by rfl⟩ : syracuseStep 2089031 = 3133547) B3133547
theorem B2351207 : Blo 1391515 2351207 := bstep (se 1 (by rfl) ⟨1763405, by rfl⟩ : syracuseStep 2351207 = 3526811) B3526811
theorem B2089067 : Blo 1391515 2089067 := bstep (se 1 (by rfl) ⟨1566800, by rfl⟩ : syracuseStep 2089067 = 3133601) B3133601
theorem B2089151 : Blo 1391515 2089151 := bstep (se 1 (by rfl) ⟨1566863, by rfl⟩ : syracuseStep 2089151 = 3133727) B3133727
theorem B109945183 : Blo 1391515 109945183 := bstep (se 1 (by rfl) ⟨82458887, by rfl⟩ : syracuseStep 109945183 = 164917775) B164917775
theorem B1392999 : Blo 1391515 1392999 := bstep (se 1 (by rfl) ⟨1044749, by rfl⟩ : syracuseStep 1392999 = 2089499) B2089499
theorem B2089337 : Blo 1391515 2089337 := bstep (se 2 (by rfl) ⟨783501, by rfl⟩ : syracuseStep 2089337 = 1567003) B1567003
theorem B80306639 : Blo 1391515 80306639 := bstep (se 1 (by rfl) ⟨60229979, by rfl⟩ : syracuseStep 80306639 = 120459959) B120459959
theorem B1393119 : Blo 1391515 1393119 := bstep (se 1 (by rfl) ⟨1044839, by rfl⟩ : syracuseStep 1393119 = 2089679) B2089679
theorem B1393127 : Blo 1391515 1393127 := bstep (se 1 (by rfl) ⟨1044845, by rfl⟩ : syracuseStep 1393127 = 2089691) B2089691
theorem B8036945 : Blo 1391515 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B2089631 : Blo 1391515 2089631 := bstep (se 1 (by rfl) ⟨1567223, by rfl⟩ : syracuseStep 2089631 = 3134447) B3134447
theorem B1393403 : Blo 1391515 1393403 := bstep (se 1 (by rfl) ⟨1045052, by rfl⟩ : syracuseStep 1393403 = 2090105) B2090105
theorem B1565599 : Blo 1391515 1565599 := bstep (se 1 (by rfl) ⟨1174199, by rfl⟩ : syracuseStep 1565599 = 2348399) B2348399
theorem B2089967 : Blo 1391515 2089967 := bstep (se 1 (by rfl) ⟨1567475, by rfl⟩ : syracuseStep 2089967 = 3134951) B3134951
theorem B32605199 : Blo 1391515 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B3966023 : Blo 1391515 3966023 := bstep (se 1 (by rfl) ⟨2974517, by rfl⟩ : syracuseStep 3966023 = 5949035) B5949035
theorem B2090075 : Blo 1391515 2090075 := bstep (se 1 (by rfl) ⟨1567556, by rfl⟩ : syracuseStep 2090075 = 3135113) B3135113
theorem B2090087 : Blo 1391515 2090087 := bstep (se 1 (by rfl) ⟨1567565, by rfl⟩ : syracuseStep 2090087 = 3135131) B3135131
theorem B2090219 : Blo 1391515 2090219 := bstep (se 1 (by rfl) ⟨1567664, by rfl⟩ : syracuseStep 2090219 = 3135329) B3135329
theorem B33891821 : Blo 1391515 33891821 := bstep (se 3 (by rfl) ⟨6354716, by rfl⟩ : syracuseStep 33891821 = 12709433) B12709433
theorem B15861581 : Blo 1391515 15861581 := bstep (se 3 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 15861581 = 5948093) B5948093
theorem B2975611 : Blo 1391515 2975611 := bstep (se 1 (by rfl) ⟨2231708, by rfl⟩ : syracuseStep 2975611 = 4463417) B4463417
theorem B3131369 : Blo 1391515 3131369 := bstep (se 2 (by rfl) ⟨1174263, by rfl⟩ : syracuseStep 3131369 = 2348527) B2348527
theorem B3131855 : Blo 1391515 3131855 := bstep (se 1 (by rfl) ⟨2348891, by rfl⟩ : syracuseStep 3131855 = 4697783) B4697783
theorem B3525079 : Blo 1391515 3525079 := bstep (se 1 (by rfl) ⟨2643809, by rfl⟩ : syracuseStep 3525079 = 5287619) B5287619
theorem B3131945 : Blo 1391515 3131945 := bstep (se 2 (by rfl) ⟨1174479, by rfl⟩ : syracuseStep 3131945 = 2348959) B2348959
theorem B2230991 : Blo 1391515 2230991 := bstep (se 1 (by rfl) ⟨1673243, by rfl⟩ : syracuseStep 2230991 = 3346487) B3346487
theorem B3525383 : Blo 1391515 3525383 := bstep (se 1 (by rfl) ⟨2644037, by rfl⟩ : syracuseStep 3525383 = 5288075) B5288075
theorem B5286815 : Blo 1391515 5286815 := bstep (se 1 (by rfl) ⟨3965111, by rfl⟩ : syracuseStep 5286815 = 7930223) B7930223
theorem B15256633 : Blo 1391515 15256633 := bstep (se 2 (by rfl) ⟨5721237, by rfl⟩ : syracuseStep 15256633 = 11442475) B11442475
theorem B2231401 : Blo 1391515 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B3132827 : Blo 1391515 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B4697567 : Blo 1391515 4697567 := bstep (se 1 (by rfl) ⟨3523175, by rfl⟩ : syracuseStep 4697567 = 7046351) B7046351
theorem B15478277 : Blo 1391515 15478277 := bstep (se 4 (by rfl) ⟨1451088, by rfl⟩ : syracuseStep 15478277 = 2902177) B2902177
theorem B8925065 : Blo 1391515 8925065 := bstep (se 2 (by rfl) ⟨3346899, by rfl⟩ : syracuseStep 8925065 = 6693799) B6693799
theorem B4460455 : Blo 1391515 4460455 := bstep (se 1 (by rfl) ⟨3345341, by rfl⟩ : syracuseStep 4460455 = 6690683) B6690683
theorem B4763731 : Blo 1391515 4763731 := bstep (se 1 (by rfl) ⟨3572798, by rfl⟩ : syracuseStep 4763731 = 7145597) B7145597
theorem B5017697 : Blo 1391515 5017697 := bstep (se 2 (by rfl) ⟨1881636, by rfl⟩ : syracuseStep 5017697 = 3763273) B3763273
theorem B25424057 : Blo 1391515 25424057 := bstep (se 2 (by rfl) ⟨9534021, by rfl⟩ : syracuseStep 25424057 = 19068043) B19068043
theorem B8041121 : Blo 1391515 8041121 := bstep (se 2 (by rfl) ⟨3015420, by rfl⟩ : syracuseStep 8041121 = 6030841) B6030841
theorem B5288759 : Blo 1391515 5288759 := bstep (se 1 (by rfl) ⟨3966569, by rfl⟩ : syracuseStep 5288759 = 7933139) B7933139
theorem B3134375 : Blo 1391515 3134375 := bstep (se 1 (by rfl) ⟨2350781, by rfl⟩ : syracuseStep 3134375 = 4701563) B4701563
theorem B33854453 : Blo 1391515 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B130323451 : Blo 1391515 130323451 := bstep (se 1 (by rfl) ⟨97742588, by rfl⟩ : syracuseStep 130323451 = 195485177) B195485177
theorem B2118727 : Blo 1391515 2118727 := bstep (se 1 (by rfl) ⟨1589045, by rfl⟩ : syracuseStep 2118727 = 3178091) B3178091
theorem B6689915 : Blo 1391515 6689915 := bstep (se 1 (by rfl) ⟨5017436, by rfl⟩ : syracuseStep 6689915 = 10034873) B10034873
theorem B7050401 : Blo 1391515 7050401 := bstep (se 2 (by rfl) ⟨2643900, by rfl⟩ : syracuseStep 7050401 = 5287801) B5287801
theorem B10581191 : Blo 1391515 10581191 := bstep (se 1 (by rfl) ⟨7935893, by rfl⟩ : syracuseStep 10581191 = 15871787) B15871787
theorem B10032335 : Blo 1391515 10032335 := bstep (se 1 (by rfl) ⟨7524251, by rfl⟩ : syracuseStep 10032335 = 15048503) B15048503
theorem B10319329 : Blo 1391515 10319329 := bstep (se 2 (by rfl) ⟨3869748, by rfl⟩ : syracuseStep 10319329 = 7739497) B7739497
theorem B5019155 : Blo 1391515 5019155 := bstep (se 1 (by rfl) ⟨3764366, by rfl⟩ : syracuseStep 5019155 = 7528733) B7528733
theorem B17847971 : Blo 1391515 17847971 := bstep (se 1 (by rfl) ⟨13385978, by rfl⟩ : syracuseStep 17847971 = 26771957) B26771957
theorem B8034011 : Blo 1391515 8034011 := bstep (se 1 (by rfl) ⟨6025508, by rfl⟩ : syracuseStep 8034011 = 12051017) B12051017
theorem B6690529 : Blo 1391515 6690529 := bstep (se 2 (by rfl) ⟨2508948, by rfl⟩ : syracuseStep 6690529 = 5017897) B5017897
theorem B3962753 : Blo 1391515 3962753 := bstep (se 2 (by rfl) ⟨1486032, by rfl⟩ : syracuseStep 3962753 = 2972065) B2972065
theorem B2644159 : Blo 1391515 2644159 := bstep (se 1 (by rfl) ⟨1983119, by rfl⟩ : syracuseStep 2644159 = 3966239) B3966239
theorem B28965073 : Blo 1391515 28965073 := bstep (se 2 (by rfl) ⟨10861902, by rfl⟩ : syracuseStep 28965073 = 21723805) B21723805
theorem B4700375 : Blo 1391515 4700375 := bstep (se 1 (by rfl) ⟨3525281, by rfl⟩ : syracuseStep 4700375 = 7050563) B7050563
theorem B7928057 : Blo 1391515 7928057 := bstep (se 2 (by rfl) ⟨2973021, by rfl⟩ : syracuseStep 7928057 = 5946043) B5946043
theorem B4643167 : Blo 1391515 4643167 := bstep (se 1 (by rfl) ⟨3482375, by rfl⟩ : syracuseStep 4643167 = 6964751) B6964751
theorem B3013051 : Blo 1391515 3013051 := bstep (se 1 (by rfl) ⟨2259788, by rfl⟩ : syracuseStep 3013051 = 4519577) B4519577
theorem B10041907 : Blo 1391515 10041907 := bstep (se 1 (by rfl) ⟨7531430, by rfl⟩ : syracuseStep 10041907 = 15062861) B15062861
theorem B2087519 : Blo 1391515 2087519 := bstep (se 1 (by rfl) ⟨1565639, by rfl⟩ : syracuseStep 2087519 = 3131279) B3131279
theorem B3963563 : Blo 1391515 3963563 := bstep (se 1 (by rfl) ⟨2972672, by rfl⟩ : syracuseStep 3963563 = 5945345) B5945345
theorem B2087615 : Blo 1391515 2087615 := bstep (se 1 (by rfl) ⟨1565711, by rfl⟩ : syracuseStep 2087615 = 3131423) B3131423
theorem B2087657 : Blo 1391515 2087657 := bstep (se 2 (by rfl) ⟨782871, by rfl⟩ : syracuseStep 2087657 = 1565743) B1565743
theorem B4700915 : Blo 1391515 4700915 := bstep (se 1 (by rfl) ⟨3525686, by rfl⟩ : syracuseStep 4700915 = 7051373) B7051373
theorem B2087783 : Blo 1391515 2087783 := bstep (se 1 (by rfl) ⟨1565837, by rfl⟩ : syracuseStep 2087783 = 3131675) B3131675
theorem B2087849 : Blo 1391515 2087849 := bstep (se 2 (by rfl) ⟨782943, by rfl⟩ : syracuseStep 2087849 = 1565887) B1565887
theorem B4291517 : Blo 1391515 4291517 := bstep (se 3 (by rfl) ⟨804659, by rfl⟩ : syracuseStep 4291517 = 1609319) B1609319
theorem B1391551 : Blo 1391515 1391551 := bstep (se 1 (by rfl) ⟨1043663, by rfl⟩ : syracuseStep 1391551 = 2087327) B2087327
theorem B1391599 : Blo 1391515 1391599 := bstep (se 1 (by rfl) ⟨1043699, by rfl⟩ : syracuseStep 1391599 = 2087399) B2087399
theorem B5290991 : Blo 1391515 5290991 := bstep (se 1 (by rfl) ⟨3968243, by rfl⟩ : syracuseStep 5290991 = 7936487) B7936487
theorem B2087999 : Blo 1391515 2087999 := bstep (se 1 (by rfl) ⟨1565999, by rfl⟩ : syracuseStep 2087999 = 3131999) B3131999
theorem B2088041 : Blo 1391515 2088041 := bstep (se 2 (by rfl) ⟨783015, by rfl⟩ : syracuseStep 2088041 = 1566031) B1566031
theorem B15269087 : Blo 1391515 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B2088167 : Blo 1391515 2088167 := bstep (se 1 (by rfl) ⟨1566125, by rfl⟩ : syracuseStep 2088167 = 3132251) B3132251
theorem B33873137 : Blo 1391515 33873137 := bstep (se 2 (by rfl) ⟨12702426, by rfl⟩ : syracuseStep 33873137 = 25404853) B25404853
theorem B45792499 : Blo 1391515 45792499 := bstep (se 1 (by rfl) ⟨34344374, by rfl⟩ : syracuseStep 45792499 = 68688749) B68688749
theorem B1392095 : Blo 1391515 1392095 := bstep (se 1 (by rfl) ⟨1044071, by rfl⟩ : syracuseStep 1392095 = 2088143) B2088143
theorem B2645473 : Blo 1391515 2645473 := bstep (se 2 (by rfl) ⟨992052, by rfl⟩ : syracuseStep 2645473 = 1984105) B1984105
theorem B1392175 : Blo 1391515 1392175 := bstep (se 1 (by rfl) ⟨1044131, by rfl⟩ : syracuseStep 1392175 = 2088263) B2088263
theorem B1785499 : Blo 1391515 1785499 := bstep (se 1 (by rfl) ⟨1339124, by rfl⟩ : syracuseStep 1785499 = 2678249) B2678249
theorem B1392283 : Blo 1391515 1392283 := bstep (se 1 (by rfl) ⟨1044212, by rfl⟩ : syracuseStep 1392283 = 2088425) B2088425
theorem B2088671 : Blo 1391515 2088671 := bstep (se 1 (by rfl) ⟨1566503, by rfl⟩ : syracuseStep 2088671 = 3133007) B3133007
theorem B1392379 : Blo 1391515 1392379 := bstep (se 1 (by rfl) ⟨1044284, by rfl⟩ : syracuseStep 1392379 = 2088569) B2088569
theorem B1392543 : Blo 1391515 1392543 := bstep (se 1 (by rfl) ⟨1044407, by rfl⟩ : syracuseStep 1392543 = 2088815) B2088815
theorem B8921015 : Blo 1391515 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B40148945 : Blo 1391515 40148945 := bstep (se 2 (by rfl) ⟨15055854, by rfl⟩ : syracuseStep 40148945 = 30111709) B30111709
theorem B7528403 : Blo 1391515 7528403 := bstep (se 1 (by rfl) ⟨5646302, by rfl⟩ : syracuseStep 7528403 = 11292605) B11292605
theorem B1392667 : Blo 1391515 1392667 := bstep (se 1 (by rfl) ⟨1044500, by rfl⟩ : syracuseStep 1392667 = 2089001) B2089001
theorem B1392687 : Blo 1391515 1392687 := bstep (se 1 (by rfl) ⟨1044515, by rfl⟩ : syracuseStep 1392687 = 2089031) B2089031
theorem B1392711 : Blo 1391515 1392711 := bstep (se 1 (by rfl) ⟨1044533, by rfl⟩ : syracuseStep 1392711 = 2089067) B2089067
theorem B16949371 : Blo 1391515 16949371 := bstep (se 1 (by rfl) ⟨12712028, by rfl⟩ : syracuseStep 16949371 = 25424057) B25424057
theorem B1392767 : Blo 1391515 1392767 := bstep (se 1 (by rfl) ⟨1044575, by rfl⟩ : syracuseStep 1392767 = 2089151) B2089151
theorem B1392891 : Blo 1391515 1392891 := bstep (se 1 (by rfl) ⟨1044668, by rfl⟩ : syracuseStep 1392891 = 2089337) B2089337
theorem B5357963 : Blo 1391515 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B1393087 : Blo 1391515 1393087 := bstep (se 1 (by rfl) ⟨1044815, by rfl⟩ : syracuseStep 1393087 = 2089631) B2089631
theorem B2089583 : Blo 1391515 2089583 := bstep (se 1 (by rfl) ⟨1567187, by rfl⟩ : syracuseStep 2089583 = 3134375) B3134375
theorem B1393311 : Blo 1391515 1393311 := bstep (se 1 (by rfl) ⟨1044983, by rfl⟩ : syracuseStep 1393311 = 2089967) B2089967
theorem B22569635 : Blo 1391515 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B1393383 : Blo 1391515 1393383 := bstep (se 1 (by rfl) ⟨1045037, by rfl⟩ : syracuseStep 1393383 = 2090075) B2090075
theorem B1393391 : Blo 1391515 1393391 := bstep (se 1 (by rfl) ⟨1045043, by rfl⟩ : syracuseStep 1393391 = 2090087) B2090087
theorem B7054127 : Blo 1391515 7054127 := bstep (se 1 (by rfl) ⟨5290595, by rfl⟩ : syracuseStep 7054127 = 10581191) B10581191
theorem B1393479 : Blo 1391515 1393479 := bstep (se 1 (by rfl) ⟨1045109, by rfl⟩ : syracuseStep 1393479 = 2090219) B2090219
theorem B22594547 : Blo 1391515 22594547 := bstep (se 1 (by rfl) ⟨16945910, by rfl⟩ : syracuseStep 22594547 = 33891821) B33891821
theorem B20342177 : Blo 1391515 20342177 := bstep (se 2 (by rfl) ⟨7628316, by rfl⟩ : syracuseStep 20342177 = 15256633) B15256633
theorem B2975201 : Blo 1391515 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B5285371 : Blo 1391515 5285371 := bstep (se 1 (by rfl) ⟨3964028, by rfl⟩ : syracuseStep 5285371 = 7928057) B7928057
theorem B61056665 : Blo 1391515 61056665 := bstep (se 2 (by rfl) ⟨22896249, by rfl⟩ : syracuseStep 61056665 = 45792499) B45792499
theorem B3524543 : Blo 1391515 3524543 := bstep (se 1 (by rfl) ⟨2643407, by rfl⟩ : syracuseStep 3524543 = 5286815) B5286815
theorem B2861011 : Blo 1391515 2861011 := bstep (se 1 (by rfl) ⟨2145758, by rfl⟩ : syracuseStep 2861011 = 4291517) B4291517
theorem B3131711 : Blo 1391515 3131711 := bstep (se 1 (by rfl) ⟨2348783, by rfl⟩ : syracuseStep 3131711 = 4697567) B4697567
theorem B3967481 : Blo 1391515 3967481 := bstep (se 2 (by rfl) ⟨1487805, by rfl⟩ : syracuseStep 3967481 = 2975611) B2975611
theorem B5950043 : Blo 1391515 5950043 := bstep (se 1 (by rfl) ⟨4462532, by rfl⟩ : syracuseStep 5950043 = 8925065) B8925065
theorem B26765963 : Blo 1391515 26765963 := bstep (se 1 (by rfl) ⟨20074472, by rfl⟩ : syracuseStep 26765963 = 40148945) B40148945
theorem B3345131 : Blo 1391515 3345131 := bstep (se 1 (by rfl) ⟨2508848, by rfl⟩ : syracuseStep 3345131 = 5017697) B5017697
theorem B1567471 : Blo 1391515 1567471 := bstep (se 1 (by rfl) ⟨1175603, by rfl⟩ : syracuseStep 1567471 = 2351207) B2351207
theorem B6351641 : Blo 1391515 6351641 := bstep (se 2 (by rfl) ⟨2381865, by rfl⟩ : syracuseStep 6351641 = 4763731) B4763731
theorem B3525545 : Blo 1391515 3525545 := bstep (se 2 (by rfl) ⟨1322079, by rfl⟩ : syracuseStep 3525545 = 2644159) B2644159
theorem B38620097 : Blo 1391515 38620097 := bstep (se 2 (by rfl) ⟨14482536, by rfl⟩ : syracuseStep 38620097 = 28965073) B28965073
theorem B53537759 : Blo 1391515 53537759 := bstep (se 1 (by rfl) ⟨40153319, by rfl⟩ : syracuseStep 53537759 = 80306639) B80306639
theorem B5360747 : Blo 1391515 5360747 := bstep (se 1 (by rfl) ⟨4020560, by rfl⟩ : syracuseStep 5360747 = 8041121) B8041121
theorem B3525839 : Blo 1391515 3525839 := bstep (se 1 (by rfl) ⟨2644379, by rfl⟩ : syracuseStep 3525839 = 5288759) B5288759
theorem B4017401 : Blo 1391515 4017401 := bstep (se 2 (by rfl) ⟨1506525, by rfl⟩ : syracuseStep 4017401 = 3013051) B3013051
theorem B40717565 : Blo 1391515 40717565 := bstep (se 3 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 40717565 = 15269087) B15269087
theorem B21736799 : Blo 1391515 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B13389209 : Blo 1391515 13389209 := bstep (se 2 (by rfl) ⟨5020953, by rfl⟩ : syracuseStep 13389209 = 10041907) B10041907
theorem B4459943 : Blo 1391515 4459943 := bstep (se 1 (by rfl) ⟨3344957, by rfl⟩ : syracuseStep 4459943 = 6689915) B6689915
theorem B6688223 : Blo 1391515 6688223 := bstep (se 1 (by rfl) ⟨5016167, by rfl⟩ : syracuseStep 6688223 = 10032335) B10032335
theorem B3346103 : Blo 1391515 3346103 := bstep (se 1 (by rfl) ⟨2509577, by rfl⟩ : syracuseStep 3346103 = 5019155) B5019155
theorem B11898647 : Blo 1391515 11898647 := bstep (se 1 (by rfl) ⟨8923985, by rfl⟩ : syracuseStep 11898647 = 17847971) B17847971
theorem B2641835 : Blo 1391515 2641835 := bstep (se 1 (by rfl) ⟨1981376, by rfl⟩ : syracuseStep 2641835 = 3962753) B3962753
theorem B173764601 : Blo 1391515 173764601 := bstep (se 2 (by rfl) ⟨65161725, by rfl⟩ : syracuseStep 173764601 = 130323451) B130323451
theorem B41275405 : Blo 1391515 41275405 := bstep (se 3 (by rfl) ⟨7739138, by rfl⟩ : syracuseStep 41275405 = 15478277) B15478277
theorem B3133583 : Blo 1391515 3133583 := bstep (se 1 (by rfl) ⟨2350187, by rfl⟩ : syracuseStep 3133583 = 4700375) B4700375
theorem B2642375 : Blo 1391515 2642375 := bstep (se 1 (by rfl) ⟨1981781, by rfl⟩ : syracuseStep 2642375 = 3963563) B3963563
theorem B1487327 : Blo 1391515 1487327 := bstep (se 1 (by rfl) ⟨1115495, by rfl⟩ : syracuseStep 1487327 = 2230991) B2230991
theorem B3133943 : Blo 1391515 3133943 := bstep (se 1 (by rfl) ⟨2350457, by rfl⟩ : syracuseStep 3133943 = 4700915) B4700915
theorem B13759105 : Blo 1391515 13759105 := bstep (se 2 (by rfl) ⟨5159664, by rfl⟩ : syracuseStep 13759105 = 10319329) B10319329
theorem B3527297 : Blo 1391515 3527297 := bstep (se 2 (by rfl) ⟨1322736, by rfl⟩ : syracuseStep 3527297 = 2645473) B2645473
theorem B3527327 : Blo 1391515 3527327 := bstep (se 1 (by rfl) ⟨2645495, by rfl⟩ : syracuseStep 3527327 = 5290991) B5290991
theorem B22582091 : Blo 1391515 22582091 := bstep (se 1 (by rfl) ⟨16936568, by rfl⟩ : syracuseStep 22582091 = 33873137) B33873137
theorem B5018935 : Blo 1391515 5018935 := bstep (se 1 (by rfl) ⟨3764201, by rfl⟩ : syracuseStep 5018935 = 7528403) B7528403
theorem B6190889 : Blo 1391515 6190889 := bstep (se 2 (by rfl) ⟨2321583, by rfl⟩ : syracuseStep 6190889 = 4643167) B4643167
theorem B146593577 : Blo 1391515 146593577 := bstep (se 2 (by rfl) ⟨54972591, by rfl⟩ : syracuseStep 146593577 = 109945183) B109945183
theorem B38090645 : Blo 1391515 38090645 := bstep (se 6 (by rfl) ⟨892749, by rfl⟩ : syracuseStep 38090645 = 1785499) B1785499
theorem B4700105 : Blo 1391515 4700105 := bstep (se 2 (by rfl) ⟨1762539, by rfl⟩ : syracuseStep 4700105 = 3525079) B3525079
theorem B2644015 : Blo 1391515 2644015 := bstep (se 1 (by rfl) ⟨1983011, by rfl⟩ : syracuseStep 2644015 = 3966023) B3966023
theorem B4700267 : Blo 1391515 4700267 := bstep (se 1 (by rfl) ⟨3525200, by rfl⟩ : syracuseStep 4700267 = 7050401) B7050401
theorem B5356007 : Blo 1391515 5356007 := bstep (se 1 (by rfl) ⟨4017005, by rfl⟩ : syracuseStep 5356007 = 8034011) B8034011
theorem B2087465 : Blo 1391515 2087465 := bstep (se 2 (by rfl) ⟨782799, by rfl⟩ : syracuseStep 2087465 = 1565599) B1565599
theorem B10574387 : Blo 1391515 10574387 := bstep (se 1 (by rfl) ⟨7930790, by rfl⟩ : syracuseStep 10574387 = 15861581) B15861581
theorem B2087579 : Blo 1391515 2087579 := bstep (se 1 (by rfl) ⟨1565684, by rfl⟩ : syracuseStep 2087579 = 3131369) B3131369
theorem B2824969 : Blo 1391515 2824969 := bstep (se 2 (by rfl) ⟨1059363, by rfl⟩ : syracuseStep 2824969 = 2118727) B2118727
theorem B2087903 : Blo 1391515 2087903 := bstep (se 1 (by rfl) ⟨1565927, by rfl⟩ : syracuseStep 2087903 = 3131855) B3131855
theorem B2087963 : Blo 1391515 2087963 := bstep (se 1 (by rfl) ⟨1565972, by rfl⟩ : syracuseStep 2087963 = 3131945) B3131945
theorem B1391679 : Blo 1391515 1391679 := bstep (se 1 (by rfl) ⟨1043759, by rfl⟩ : syracuseStep 1391679 = 2087519) B2087519
theorem B1391743 : Blo 1391515 1391743 := bstep (se 1 (by rfl) ⟨1043807, by rfl⟩ : syracuseStep 1391743 = 2087615) B2087615
theorem B1391771 : Blo 1391515 1391771 := bstep (se 1 (by rfl) ⟨1043828, by rfl⟩ : syracuseStep 1391771 = 2087657) B2087657
theorem B2350255 : Blo 1391515 2350255 := bstep (se 1 (by rfl) ⟨1762691, by rfl⟩ : syracuseStep 2350255 = 3525383) B3525383
theorem B1391855 : Blo 1391515 1391855 := bstep (se 1 (by rfl) ⟨1043891, by rfl⟩ : syracuseStep 1391855 = 2087783) B2087783
theorem B1391899 : Blo 1391515 1391899 := bstep (se 1 (by rfl) ⟨1043924, by rfl⟩ : syracuseStep 1391899 = 2087849) B2087849
theorem B1391999 : Blo 1391515 1391999 := bstep (se 1 (by rfl) ⟨1043999, by rfl⟩ : syracuseStep 1391999 = 2087999) B2087999
theorem B1392027 : Blo 1391515 1392027 := bstep (se 1 (by rfl) ⟨1044020, by rfl⟩ : syracuseStep 1392027 = 2088041) B2088041
theorem B1392111 : Blo 1391515 1392111 := bstep (se 1 (by rfl) ⟨1044083, by rfl⟩ : syracuseStep 1392111 = 2088167) B2088167
theorem B2088551 : Blo 1391515 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B8920705 : Blo 1391515 8920705 := bstep (se 2 (by rfl) ⟨3345264, by rfl⟩ : syracuseStep 8920705 = 6690529) B6690529
theorem B1392447 : Blo 1391515 1392447 := bstep (se 1 (by rfl) ⟨1044335, by rfl⟩ : syracuseStep 1392447 = 2088671) B2088671
theorem B5947273 : Blo 1391515 5947273 := bstep (se 2 (by rfl) ⟨2230227, by rfl⟩ : syracuseStep 5947273 = 4460455) B4460455
theorem B5947343 : Blo 1391515 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B55033873 : Blo 1391515 55033873 := bstep (se 2 (by rfl) ⟨20637702, by rfl⟩ : syracuseStep 55033873 = 41275405) B41275405
theorem B2089055 : Blo 1391515 2089055 := bstep (se 1 (by rfl) ⟨1566791, by rfl⟩ : syracuseStep 2089055 = 3133583) B3133583
theorem B3571975 : Blo 1391515 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B1761583 : Blo 1391515 1761583 := bstep (se 1 (by rfl) ⟨1321187, by rfl⟩ : syracuseStep 1761583 = 2642375) B2642375
theorem B2089295 : Blo 1391515 2089295 := bstep (se 1 (by rfl) ⟨1566971, by rfl⟩ : syracuseStep 2089295 = 3133943) B3133943
theorem B1393055 : Blo 1391515 1393055 := bstep (se 1 (by rfl) ⟨1044791, by rfl⟩ : syracuseStep 1393055 = 2089583) B2089583
theorem B2351531 : Blo 1391515 2351531 := bstep (se 1 (by rfl) ⟨1763648, by rfl⟩ : syracuseStep 2351531 = 3527297) B3527297
theorem B2351551 : Blo 1391515 2351551 := bstep (se 1 (by rfl) ⟨1763663, by rfl⟩ : syracuseStep 2351551 = 3527327) B3527327
theorem B4702751 : Blo 1391515 4702751 := bstep (se 1 (by rfl) ⟨3527063, by rfl⟩ : syracuseStep 4702751 = 7054127) B7054127
theorem B2089961 : Blo 1391515 2089961 := bstep (se 2 (by rfl) ⟨783735, by rfl⟩ : syracuseStep 2089961 = 1567471) B1567471
theorem B1983467 : Blo 1391515 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B57181301 : Blo 1391515 57181301 := bstep (se 5 (by rfl) ⟨2680373, by rfl⟩ : syracuseStep 57181301 = 5360747) B5360747
theorem B3966205 : Blo 1391515 3966205 := bstep (se 3 (by rfl) ⟨743663, by rfl⟩ : syracuseStep 3966205 = 1487327) B1487327
theorem B3966695 : Blo 1391515 3966695 := bstep (se 1 (by rfl) ⟨2975021, by rfl⟩ : syracuseStep 3966695 = 5950043) B5950043
theorem B17843975 : Blo 1391515 17843975 := bstep (se 1 (by rfl) ⟨13382981, by rfl⟩ : syracuseStep 17843975 = 26765963) B26765963
theorem B2230087 : Blo 1391515 2230087 := bstep (se 1 (by rfl) ⟨1672565, by rfl⟩ : syracuseStep 2230087 = 3345131) B3345131
theorem B7047161 : Blo 1391515 7047161 := bstep (se 2 (by rfl) ⟨2642685, by rfl⟩ : syracuseStep 7047161 = 5285371) B5285371
theorem B16509037 : Blo 1391515 16509037 := bstep (se 3 (by rfl) ⟨3095444, by rfl⟩ : syracuseStep 16509037 = 6190889) B6190889
theorem B390916205 : Blo 1391515 390916205 := bstep (se 3 (by rfl) ⟨73296788, by rfl⟩ : syracuseStep 390916205 = 146593577) B146593577
theorem B4458815 : Blo 1391515 4458815 := bstep (se 1 (by rfl) ⟨3344111, by rfl⟩ : syracuseStep 4458815 = 6688223) B6688223
theorem B2230735 : Blo 1391515 2230735 := bstep (se 1 (by rfl) ⟨1673051, by rfl⟩ : syracuseStep 2230735 = 3346103) B3346103
theorem B7932431 : Blo 1391515 7932431 := bstep (se 1 (by rfl) ⟨5949323, by rfl⟩ : syracuseStep 7932431 = 11898647) B11898647
theorem B3525353 : Blo 1391515 3525353 := bstep (se 2 (by rfl) ⟨1322007, by rfl⟩ : syracuseStep 3525353 = 2644015) B2644015
theorem B18345473 : Blo 1391515 18345473 := bstep (se 2 (by rfl) ⟨6879552, by rfl⟩ : syracuseStep 18345473 = 13759105) B13759105
theorem B13561451 : Blo 1391515 13561451 := bstep (se 1 (by rfl) ⟨10171088, by rfl⟩ : syracuseStep 13561451 = 20342177) B20342177
theorem B3133403 : Blo 1391515 3133403 := bstep (se 1 (by rfl) ⟨2350052, by rfl⟩ : syracuseStep 3133403 = 4700105) B4700105
theorem B3133511 : Blo 1391515 3133511 := bstep (se 1 (by rfl) ⟨2350133, by rfl⟩ : syracuseStep 3133511 = 4700267) B4700267
theorem B3133673 : Blo 1391515 3133673 := bstep (se 2 (by rfl) ⟨1175127, by rfl⟩ : syracuseStep 3133673 = 2350255) B2350255
theorem B7049591 : Blo 1391515 7049591 := bstep (se 1 (by rfl) ⟨5287193, by rfl⟩ : syracuseStep 7049591 = 10574387) B10574387
theorem B27145043 : Blo 1391515 27145043 := bstep (se 1 (by rfl) ⟨20358782, by rfl⟩ : syracuseStep 27145043 = 40717565) B40717565
theorem B8926139 : Blo 1391515 8926139 := bstep (se 1 (by rfl) ⟨6694604, by rfl⟩ : syracuseStep 8926139 = 13389209) B13389209
theorem B3814681 : Blo 1391515 3814681 := bstep (se 2 (by rfl) ⟨1430505, by rfl⟩ : syracuseStep 3814681 = 2861011) B2861011
theorem B22599161 : Blo 1391515 22599161 := bstep (se 2 (by rfl) ⟨8474685, by rfl⟩ : syracuseStep 22599161 = 16949371) B16949371
theorem B15063031 : Blo 1391515 15063031 := bstep (se 1 (by rfl) ⟨11297273, by rfl⟩ : syracuseStep 15063031 = 22594547) B22594547
theorem B3766625 : Blo 1391515 3766625 := bstep (se 2 (by rfl) ⟨1412484, by rfl⟩ : syracuseStep 3766625 = 2824969) B2824969
theorem B40704443 : Blo 1391515 40704443 := bstep (se 1 (by rfl) ⟨30528332, by rfl⟩ : syracuseStep 40704443 = 61056665) B61056665
theorem B25393763 : Blo 1391515 25393763 := bstep (se 1 (by rfl) ⟨19045322, by rfl⟩ : syracuseStep 25393763 = 38090645) B38090645
theorem B2349695 : Blo 1391515 2349695 := bstep (se 1 (by rfl) ⟨1762271, by rfl⟩ : syracuseStep 2349695 = 3524543) B3524543
theorem B2087807 : Blo 1391515 2087807 := bstep (se 1 (by rfl) ⟨1565855, by rfl⟩ : syracuseStep 2087807 = 3131711) B3131711
theorem B3570671 : Blo 1391515 3570671 := bstep (se 1 (by rfl) ⟨2678003, by rfl⟩ : syracuseStep 3570671 = 5356007) B5356007
theorem B2644987 : Blo 1391515 2644987 := bstep (se 1 (by rfl) ⟨1983740, by rfl⟩ : syracuseStep 2644987 = 3967481) B3967481
theorem B1391643 : Blo 1391515 1391643 := bstep (se 1 (by rfl) ⟨1043732, by rfl⟩ : syracuseStep 1391643 = 2087465) B2087465
theorem B6691913 : Blo 1391515 6691913 := bstep (se 2 (by rfl) ⟨2509467, by rfl⟩ : syracuseStep 6691913 = 5018935) B5018935
theorem B60185693 : Blo 1391515 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B1391719 : Blo 1391515 1391719 := bstep (se 1 (by rfl) ⟨1043789, by rfl⟩ : syracuseStep 1391719 = 2087579) B2087579
theorem B4234427 : Blo 1391515 4234427 := bstep (se 1 (by rfl) ⟨3175820, by rfl⟩ : syracuseStep 4234427 = 6351641) B6351641
theorem B115843067 : Blo 1391515 115843067 := bstep (se 1 (by rfl) ⟨86882300, by rfl⟩ : syracuseStep 115843067 = 173764601) B173764601
theorem B2350363 : Blo 1391515 2350363 := bstep (se 1 (by rfl) ⟨1762772, by rfl⟩ : syracuseStep 2350363 = 3525545) B3525545
theorem B25746731 : Blo 1391515 25746731 := bstep (se 1 (by rfl) ⟨19310048, by rfl⟩ : syracuseStep 25746731 = 38620097) B38620097
theorem B1391935 : Blo 1391515 1391935 := bstep (se 1 (by rfl) ⟨1043951, by rfl⟩ : syracuseStep 1391935 = 2087903) B2087903
theorem B35691839 : Blo 1391515 35691839 := bstep (se 1 (by rfl) ⟨26768879, by rfl⟩ : syracuseStep 35691839 = 53537759) B53537759
theorem B1391975 : Blo 1391515 1391975 := bstep (se 1 (by rfl) ⟨1043981, by rfl⟩ : syracuseStep 1391975 = 2087963) B2087963
theorem B2350559 : Blo 1391515 2350559 := bstep (se 1 (by rfl) ⟨1762919, by rfl⟩ : syracuseStep 2350559 = 3525839) B3525839
theorem B2678267 : Blo 1391515 2678267 := bstep (se 1 (by rfl) ⟨2008700, by rfl⟩ : syracuseStep 2678267 = 4017401) B4017401
theorem B11894273 : Blo 1391515 11894273 := bstep (se 2 (by rfl) ⟨4460352, by rfl⟩ : syracuseStep 11894273 = 8920705) B8920705
theorem B60218909 : Blo 1391515 60218909 := bstep (se 3 (by rfl) ⟨11291045, by rfl⟩ : syracuseStep 60218909 = 22582091) B22582091
theorem B14491199 : Blo 1391515 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B2973295 : Blo 1391515 2973295 := bstep (se 1 (by rfl) ⟨2229971, by rfl⟩ : syracuseStep 2973295 = 4459943) B4459943
theorem B1392367 : Blo 1391515 1392367 := bstep (se 1 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 1392367 = 2088551) B2088551
theorem B7044893 : Blo 1391515 7044893 := bstep (se 3 (by rfl) ⟨1320917, by rfl⟩ : syracuseStep 7044893 = 2641835) B2641835
theorem B7929697 : Blo 1391515 7929697 := bstep (se 2 (by rfl) ⟨2973636, by rfl⟩ : syracuseStep 7929697 = 5947273) B5947273
theorem B3964895 : Blo 1391515 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B2089007 : Blo 1391515 2089007 := bstep (se 1 (by rfl) ⟨1566755, by rfl⟩ : syracuseStep 2089007 = 3133511) B3133511
theorem B1392703 : Blo 1391515 1392703 := bstep (se 1 (by rfl) ⟨1044527, by rfl⟩ : syracuseStep 1392703 = 2089055) B2089055
theorem B2089115 : Blo 1391515 2089115 := bstep (se 1 (by rfl) ⟨1566836, by rfl⟩ : syracuseStep 2089115 = 3133673) B3133673
theorem B1392863 : Blo 1391515 1392863 := bstep (se 1 (by rfl) ⟨1044647, by rfl⟩ : syracuseStep 1392863 = 2089295) B2089295
theorem B18096695 : Blo 1391515 18096695 := bstep (se 1 (by rfl) ⟨13572521, by rfl⟩ : syracuseStep 18096695 = 27145043) B27145043
theorem B2974313 : Blo 1391515 2974313 := bstep (se 2 (by rfl) ⟨1115367, by rfl⟩ : syracuseStep 2974313 = 2230735) B2230735
theorem B1393307 : Blo 1391515 1393307 := bstep (se 1 (by rfl) ⟨1044980, by rfl⟩ : syracuseStep 1393307 = 2089961) B2089961
theorem B15066107 : Blo 1391515 15066107 := bstep (se 1 (by rfl) ⟨11299580, by rfl⟩ : syracuseStep 15066107 = 22599161) B22599161
theorem B11895983 : Blo 1391515 11895983 := bstep (se 1 (by rfl) ⟨8921987, by rfl⟩ : syracuseStep 11895983 = 17843975) B17843975
theorem B1566463 : Blo 1391515 1566463 := bstep (se 1 (by rfl) ⟨1174847, by rfl⟩ : syracuseStep 1566463 = 2349695) B2349695
theorem B17164487 : Blo 1391515 17164487 := bstep (se 1 (by rfl) ⟨12873365, by rfl⟩ : syracuseStep 17164487 = 25746731) B25746731
theorem B352192789 : Blo 1391515 352192789 := bstep (se 6 (by rfl) ⟨8254518, by rfl⟩ : syracuseStep 352192789 = 16509037) B16509037
theorem B1567039 : Blo 1391515 1567039 := bstep (se 1 (by rfl) ⟨1175279, by rfl⟩ : syracuseStep 1567039 = 2350559) B2350559
theorem B9660799 : Blo 1391515 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B4696595 : Blo 1391515 4696595 := bstep (se 1 (by rfl) ⟨3522446, by rfl⟩ : syracuseStep 4696595 = 7044893) B7044893
theorem B77228711 : Blo 1391515 77228711 := bstep (se 1 (by rfl) ⟨57921533, by rfl⟩ : syracuseStep 77228711 = 115843067) B115843067
theorem B293513989 : Blo 1391515 293513989 := bstep (se 4 (by rfl) ⟨27516936, by rfl⟩ : syracuseStep 293513989 = 55033873) B55033873
theorem B1567687 : Blo 1391515 1567687 := bstep (se 1 (by rfl) ⟨1175765, by rfl⟩ : syracuseStep 1567687 = 2351531) B2351531
theorem B4762633 : Blo 1391515 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B5950759 : Blo 1391515 5950759 := bstep (se 1 (by rfl) ⟨4463069, by rfl⟩ : syracuseStep 5950759 = 8926139) B8926139
theorem B38120867 : Blo 1391515 38120867 := bstep (se 1 (by rfl) ⟨28590650, by rfl⟩ : syracuseStep 38120867 = 57181301) B57181301
theorem B3526649 : Blo 1391515 3526649 := bstep (se 2 (by rfl) ⟨1322493, by rfl⟩ : syracuseStep 3526649 = 2644987) B2644987
theorem B4698107 : Blo 1391515 4698107 := bstep (se 1 (by rfl) ⟨3523580, by rfl⟩ : syracuseStep 4698107 = 7047161) B7047161
theorem B2511083 : Blo 1391515 2511083 := bstep (se 1 (by rfl) ⟨1883312, by rfl⟩ : syracuseStep 2511083 = 3766625) B3766625
theorem B27136295 : Blo 1391515 27136295 := bstep (se 1 (by rfl) ⟨20352221, by rfl⟩ : syracuseStep 27136295 = 40704443) B40704443
theorem B5288273 : Blo 1391515 5288273 := bstep (se 2 (by rfl) ⟨1983102, by rfl⟩ : syracuseStep 5288273 = 3966205) B3966205
theorem B5288287 : Blo 1391515 5288287 := bstep (se 1 (by rfl) ⟨3966215, by rfl⟩ : syracuseStep 5288287 = 7932431) B7932431
theorem B3133817 : Blo 1391515 3133817 := bstep (se 2 (by rfl) ⟨1175181, by rfl⟩ : syracuseStep 3133817 = 2350363) B2350363
theorem B16929175 : Blo 1391515 16929175 := bstep (se 1 (by rfl) ⟨12696881, by rfl⟩ : syracuseStep 16929175 = 25393763) B25393763
theorem B2380447 : Blo 1391515 2380447 := bstep (se 1 (by rfl) ⟨1785335, by rfl⟩ : syracuseStep 2380447 = 3570671) B3570671
theorem B4461275 : Blo 1391515 4461275 := bstep (se 1 (by rfl) ⟨3345956, by rfl⟩ : syracuseStep 4461275 = 6691913) B6691913
theorem B2822951 : Blo 1391515 2822951 := bstep (se 1 (by rfl) ⟨2117213, by rfl⟩ : syracuseStep 2822951 = 4234427) B4234427
theorem B23794559 : Blo 1391515 23794559 := bstep (se 1 (by rfl) ⟨17845919, by rfl⟩ : syracuseStep 23794559 = 35691839) B35691839
theorem B40145939 : Blo 1391515 40145939 := bstep (se 1 (by rfl) ⟨30109454, by rfl⟩ : syracuseStep 40145939 = 60218909) B60218909
theorem B9040967 : Blo 1391515 9040967 := bstep (se 1 (by rfl) ⟨6780725, by rfl⟩ : syracuseStep 9040967 = 13561451) B13561451
theorem B10572929 : Blo 1391515 10572929 := bstep (se 2 (by rfl) ⟨3964848, by rfl⟩ : syracuseStep 10572929 = 7929697) B7929697
theorem B5289245 : Blo 1391515 5289245 := bstep (se 3 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 5289245 = 1983467) B1983467
theorem B2643263 : Blo 1391515 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B20084041 : Blo 1391515 20084041 := bstep (se 2 (by rfl) ⟨7531515, by rfl⟩ : syracuseStep 20084041 = 15063031) B15063031
theorem B4699727 : Blo 1391515 4699727 := bstep (se 1 (by rfl) ⟨3524795, by rfl⟩ : syracuseStep 4699727 = 7049591) B7049591
theorem B3135167 : Blo 1391515 3135167 := bstep (se 1 (by rfl) ⟨2351375, by rfl⟩ : syracuseStep 3135167 = 4702751) B4702751
theorem B2348777 : Blo 1391515 2348777 := bstep (se 2 (by rfl) ⟨880791, by rfl⟩ : syracuseStep 2348777 = 1761583) B1761583
theorem B3135401 : Blo 1391515 3135401 := bstep (se 2 (by rfl) ⟨1175775, by rfl⟩ : syracuseStep 3135401 = 2351551) B2351551
theorem B2644463 : Blo 1391515 2644463 := bstep (se 1 (by rfl) ⟨1983347, by rfl⟩ : syracuseStep 2644463 = 3966695) B3966695
theorem B260610803 : Blo 1391515 260610803 := bstep (se 1 (by rfl) ⟨195458102, by rfl⟩ : syracuseStep 260610803 = 390916205) B390916205
theorem B2972543 : Blo 1391515 2972543 := bstep (se 1 (by rfl) ⟨2229407, by rfl⟩ : syracuseStep 2972543 = 4458815) B4458815
theorem B5086241 : Blo 1391515 5086241 := bstep (se 2 (by rfl) ⟨1907340, by rfl⟩ : syracuseStep 5086241 = 3814681) B3814681
theorem B2350235 : Blo 1391515 2350235 := bstep (se 1 (by rfl) ⟨1762676, by rfl⟩ : syracuseStep 2350235 = 3525353) B3525353
theorem B1391871 : Blo 1391515 1391871 := bstep (se 1 (by rfl) ⟨1043903, by rfl⟩ : syracuseStep 1391871 = 2087807) B2087807
theorem B40123795 : Blo 1391515 40123795 := bstep (se 1 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 40123795 = 60185693) B60185693
theorem B3964393 : Blo 1391515 3964393 := bstep (se 2 (by rfl) ⟨1486647, by rfl⟩ : syracuseStep 3964393 = 2973295) B2973295
theorem B1785511 : Blo 1391515 1785511 := bstep (se 1 (by rfl) ⟨1339133, by rfl⟩ : syracuseStep 1785511 = 2678267) B2678267
theorem B7929515 : Blo 1391515 7929515 := bstep (se 1 (by rfl) ⟨5947136, by rfl⟩ : syracuseStep 7929515 = 11894273) B11894273
theorem B12230315 : Blo 1391515 12230315 := bstep (se 1 (by rfl) ⟨9172736, by rfl⟩ : syracuseStep 12230315 = 18345473) B18345473
theorem B2973449 : Blo 1391515 2973449 := bstep (se 2 (by rfl) ⟨1115043, by rfl⟩ : syracuseStep 2973449 = 2230087) B2230087
theorem B2088935 : Blo 1391515 2088935 := bstep (se 1 (by rfl) ⟨1566701, by rfl⟩ : syracuseStep 2088935 = 3133403) B3133403
theorem B1392671 : Blo 1391515 1392671 := bstep (se 1 (by rfl) ⟨1044503, by rfl⟩ : syracuseStep 1392671 = 2089007) B2089007
theorem B1392743 : Blo 1391515 1392743 := bstep (se 1 (by rfl) ⟨1044557, by rfl⟩ : syracuseStep 1392743 = 2089115) B2089115
theorem B2089211 : Blo 1391515 2089211 := bstep (se 1 (by rfl) ⟨1566908, by rfl⟩ : syracuseStep 2089211 = 3133817) B3133817
theorem B469590385 : Blo 1391515 469590385 := bstep (se 2 (by rfl) ⟨176096394, by rfl⟩ : syracuseStep 469590385 = 352192789) B352192789
theorem B1982875 : Blo 1391515 1982875 := bstep (se 1 (by rfl) ⟨1487156, by rfl⟩ : syracuseStep 1982875 = 2974313) B2974313
theorem B2089385 : Blo 1391515 2089385 := bstep (se 2 (by rfl) ⟨783519, by rfl⟩ : syracuseStep 2089385 = 1567039) B1567039
theorem B10044071 : Blo 1391515 10044071 := bstep (se 1 (by rfl) ⟨7533053, by rfl⟩ : syracuseStep 10044071 = 15066107) B15066107
theorem B26763959 : Blo 1391515 26763959 := bstep (se 1 (by rfl) ⟨20072969, by rfl⟩ : syracuseStep 26763959 = 40145939) B40145939
theorem B7930655 : Blo 1391515 7930655 := bstep (se 1 (by rfl) ⟨5947991, by rfl⟩ : syracuseStep 7930655 = 11895983) B11895983
theorem B1762175 : Blo 1391515 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B2090111 : Blo 1391515 2090111 := bstep (se 1 (by rfl) ⟨1567583, by rfl⟩ : syracuseStep 2090111 = 3135167) B3135167
theorem B1565851 : Blo 1391515 1565851 := bstep (se 1 (by rfl) ⟨1174388, by rfl⟩ : syracuseStep 1565851 = 2348777) B2348777
theorem B2090249 : Blo 1391515 2090249 := bstep (se 2 (by rfl) ⟨783843, by rfl⟩ : syracuseStep 2090249 = 1567687) B1567687
theorem B2090267 : Blo 1391515 2090267 := bstep (se 1 (by rfl) ⟨1567700, by rfl⟩ : syracuseStep 2090267 = 3135401) B3135401
theorem B6350177 : Blo 1391515 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B1762975 : Blo 1391515 1762975 := bstep (se 1 (by rfl) ⟨1322231, by rfl⟩ : syracuseStep 1762975 = 2644463) B2644463
theorem B3131063 : Blo 1391515 3131063 := bstep (se 1 (by rfl) ⟨2348297, by rfl⟩ : syracuseStep 3131063 = 4696595) B4696595
theorem B11896733 : Blo 1391515 11896733 := bstep (se 3 (by rfl) ⟨2230637, by rfl⟩ : syracuseStep 11896733 = 4461275) B4461275
theorem B5285857 : Blo 1391515 5285857 := bstep (se 2 (by rfl) ⟨1982196, by rfl⟩ : syracuseStep 5285857 = 3964393) B3964393
theorem B1566823 : Blo 1391515 1566823 := bstep (se 1 (by rfl) ⟨1175117, by rfl⟩ : syracuseStep 1566823 = 2350235) B2350235
theorem B25413911 : Blo 1391515 25413911 := bstep (se 1 (by rfl) ⟨19060433, by rfl⟩ : syracuseStep 25413911 = 38120867) B38120867
theorem B5286343 : Blo 1391515 5286343 := bstep (se 1 (by rfl) ⟨3964757, by rfl⟩ : syracuseStep 5286343 = 7929515) B7929515
theorem B8153543 : Blo 1391515 8153543 := bstep (se 1 (by rfl) ⟨6115157, by rfl⟩ : syracuseStep 8153543 = 12230315) B12230315
theorem B3132071 : Blo 1391515 3132071 := bstep (se 1 (by rfl) ⟨2349053, by rfl⟩ : syracuseStep 3132071 = 4698107) B4698107
theorem B1674055 : Blo 1391515 1674055 := bstep (se 1 (by rfl) ⟨1255541, by rfl⟩ : syracuseStep 1674055 = 2511083) B2511083
theorem B18090863 : Blo 1391515 18090863 := bstep (se 1 (by rfl) ⟨13568147, by rfl⟩ : syracuseStep 18090863 = 27136295) B27136295
theorem B3525515 : Blo 1391515 3525515 := bstep (se 1 (by rfl) ⟨2644136, by rfl⟩ : syracuseStep 3525515 = 5288273) B5288273
theorem B12881065 : Blo 1391515 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B45771965 : Blo 1391515 45771965 := bstep (se 3 (by rfl) ⟨8582243, by rfl⟩ : syracuseStep 45771965 = 17164487) B17164487
theorem B22572233 : Blo 1391515 22572233 := bstep (se 2 (by rfl) ⟨8464587, by rfl⟩ : syracuseStep 22572233 = 16929175) B16929175
theorem B15863039 : Blo 1391515 15863039 := bstep (se 1 (by rfl) ⟨11897279, by rfl⟩ : syracuseStep 15863039 = 23794559) B23794559
theorem B7048619 : Blo 1391515 7048619 := bstep (se 1 (by rfl) ⟨5286464, by rfl⟩ : syracuseStep 7048619 = 10572929) B10572929
theorem B3526163 : Blo 1391515 3526163 := bstep (se 1 (by rfl) ⟨2644622, by rfl⟩ : syracuseStep 3526163 = 5289245) B5289245
theorem B391351985 : Blo 1391515 391351985 := bstep (se 2 (by rfl) ⟨146756994, by rfl⟩ : syracuseStep 391351985 = 293513989) B293513989
theorem B3133151 : Blo 1391515 3133151 := bstep (se 1 (by rfl) ⟨2349863, by rfl⟩ : syracuseStep 3133151 = 4699727) B4699727
theorem B7934345 : Blo 1391515 7934345 := bstep (se 2 (by rfl) ⟨2975379, by rfl⟩ : syracuseStep 7934345 = 5950759) B5950759
theorem B173740535 : Blo 1391515 173740535 := bstep (se 1 (by rfl) ⟨130305401, by rfl⟩ : syracuseStep 173740535 = 260610803) B260610803
theorem B53498393 : Blo 1391515 53498393 := bstep (se 2 (by rfl) ⟨20061897, by rfl⟩ : syracuseStep 53498393 = 40123795) B40123795
theorem B2380681 : Blo 1391515 2380681 := bstep (se 2 (by rfl) ⟨892755, by rfl⟩ : syracuseStep 2380681 = 1785511) B1785511
theorem B7926781 : Blo 1391515 7926781 := bstep (se 3 (by rfl) ⟨1486271, by rfl⟩ : syracuseStep 7926781 = 2972543) B2972543
theorem B12064463 : Blo 1391515 12064463 := bstep (se 1 (by rfl) ⟨9048347, by rfl⟩ : syracuseStep 12064463 = 18096695) B18096695
theorem B7051049 : Blo 1391515 7051049 := bstep (se 2 (by rfl) ⟨2644143, by rfl⟩ : syracuseStep 7051049 = 5288287) B5288287
theorem B1881967 : Blo 1391515 1881967 := bstep (se 1 (by rfl) ⟨1411475, by rfl⟩ : syracuseStep 1881967 = 2822951) B2822951
theorem B6027311 : Blo 1391515 6027311 := bstep (se 1 (by rfl) ⟨4520483, by rfl⟩ : syracuseStep 6027311 = 9040967) B9040967
theorem B12695717 : Blo 1391515 12695717 := bstep (se 4 (by rfl) ⟨1190223, by rfl⟩ : syracuseStep 12695717 = 2380447) B2380447
theorem B26778721 : Blo 1391515 26778721 := bstep (se 2 (by rfl) ⟨10042020, by rfl⟩ : syracuseStep 26778721 = 20084041) B20084041
theorem B51485807 : Blo 1391515 51485807 := bstep (se 1 (by rfl) ⟨38614355, by rfl⟩ : syracuseStep 51485807 = 77228711) B77228711
theorem B3390827 : Blo 1391515 3390827 := bstep (se 1 (by rfl) ⟨2543120, by rfl⟩ : syracuseStep 3390827 = 5086241) B5086241
theorem B7929197 : Blo 1391515 7929197 := bstep (se 3 (by rfl) ⟨1486724, by rfl⟩ : syracuseStep 7929197 = 2973449) B2973449
theorem B2088617 : Blo 1391515 2088617 := bstep (se 2 (by rfl) ⟨783231, by rfl⟩ : syracuseStep 2088617 = 1566463) B1566463
theorem B2351099 : Blo 1391515 2351099 := bstep (se 1 (by rfl) ⟨1763324, by rfl⟩ : syracuseStep 2351099 = 3526649) B3526649
theorem B1392623 : Blo 1391515 1392623 := bstep (se 1 (by rfl) ⟨1044467, by rfl⟩ : syracuseStep 1392623 = 2088935) B2088935
theorem B2089097 : Blo 1391515 2089097 := bstep (se 2 (by rfl) ⟨783411, by rfl⟩ : syracuseStep 2089097 = 1566823) B1566823
theorem B1392807 : Blo 1391515 1392807 := bstep (se 1 (by rfl) ⟨1044605, by rfl⟩ : syracuseStep 1392807 = 2089211) B2089211
theorem B1392923 : Blo 1391515 1392923 := bstep (se 1 (by rfl) ⟨1044692, by rfl⟩ : syracuseStep 1392923 = 2089385) B2089385
theorem B115827023 : Blo 1391515 115827023 := bstep (se 1 (by rfl) ⟨86870267, by rfl⟩ : syracuseStep 115827023 = 173740535) B173740535
theorem B17842639 : Blo 1391515 17842639 := bstep (se 1 (by rfl) ⟨13381979, by rfl⟩ : syracuseStep 17842639 = 26763959) B26763959
theorem B1393407 : Blo 1391515 1393407 := bstep (se 1 (by rfl) ⟨1045055, by rfl⟩ : syracuseStep 1393407 = 2090111) B2090111
theorem B1393499 : Blo 1391515 1393499 := bstep (se 1 (by rfl) ⟨1045124, by rfl⟩ : syracuseStep 1393499 = 2090249) B2090249
theorem B1393511 : Blo 1391515 1393511 := bstep (se 1 (by rfl) ⟨1045133, by rfl⟩ : syracuseStep 1393511 = 2090267) B2090267
theorem B16933805 : Blo 1391515 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B36168821 : Blo 1391515 36168821 := bstep (se 5 (by rfl) ⟨1695413, by rfl⟩ : syracuseStep 36168821 = 3390827) B3390827
theorem B7931155 : Blo 1391515 7931155 := bstep (se 1 (by rfl) ⟨5948366, by rfl⟩ : syracuseStep 7931155 = 11896733) B11896733
theorem B10569041 : Blo 1391515 10569041 := bstep (se 2 (by rfl) ⟨3963390, by rfl⟩ : syracuseStep 10569041 = 7926781) B7926781
theorem B8463811 : Blo 1391515 8463811 := bstep (se 1 (by rfl) ⟨6347858, by rfl⟩ : syracuseStep 8463811 = 12695717) B12695717
theorem B16942607 : Blo 1391515 16942607 := bstep (se 1 (by rfl) ⟨12706955, by rfl⟩ : syracuseStep 16942607 = 25413911) B25413911
theorem B12060575 : Blo 1391515 12060575 := bstep (se 1 (by rfl) ⟨9045431, by rfl⟩ : syracuseStep 12060575 = 18090863) B18090863
theorem B5286131 : Blo 1391515 5286131 := bstep (se 1 (by rfl) ⟨3964598, by rfl⟩ : syracuseStep 5286131 = 7929197) B7929197
theorem B260901323 : Blo 1391515 260901323 := bstep (se 1 (by rfl) ⟨195675992, by rfl⟩ : syracuseStep 260901323 = 391351985) B391351985
theorem B2509289 : Blo 1391515 2509289 := bstep (se 2 (by rfl) ⟨940983, by rfl⟩ : syracuseStep 2509289 = 1881967) B1881967
theorem B7047809 : Blo 1391515 7047809 := bstep (se 2 (by rfl) ⟨2642928, by rfl⟩ : syracuseStep 7047809 = 5285857) B5285857
theorem B1567399 : Blo 1391515 1567399 := bstep (se 1 (by rfl) ⟨1175549, by rfl⟩ : syracuseStep 1567399 = 2351099) B2351099
theorem B6696047 : Blo 1391515 6696047 := bstep (se 1 (by rfl) ⟨5022035, by rfl⟩ : syracuseStep 6696047 = 10044071) B10044071
theorem B5287103 : Blo 1391515 5287103 := bstep (se 1 (by rfl) ⟨3965327, by rfl⟩ : syracuseStep 5287103 = 7930655) B7930655
theorem B7048457 : Blo 1391515 7048457 := bstep (se 2 (by rfl) ⟨2643171, by rfl⟩ : syracuseStep 7048457 = 5286343) B5286343
theorem B2232073 : Blo 1391515 2232073 := bstep (se 2 (by rfl) ⟨837027, by rfl⟩ : syracuseStep 2232073 = 1674055) B1674055
theorem B3174241 : Blo 1391515 3174241 := bstep (se 2 (by rfl) ⟨1190340, by rfl⟩ : syracuseStep 3174241 = 2380681) B2380681
theorem B4018207 : Blo 1391515 4018207 := bstep (se 1 (by rfl) ⟨3013655, by rfl⟩ : syracuseStep 4018207 = 6027311) B6027311
theorem B35704961 : Blo 1391515 35704961 := bstep (se 2 (by rfl) ⟨13389360, by rfl⟩ : syracuseStep 35704961 = 26778721) B26778721
theorem B17174753 : Blo 1391515 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B5435695 : Blo 1391515 5435695 := bstep (se 1 (by rfl) ⟨4076771, by rfl⟩ : syracuseStep 5435695 = 8153543) B8153543
theorem B4699079 : Blo 1391515 4699079 := bstep (se 1 (by rfl) ⟨3524309, by rfl⟩ : syracuseStep 4699079 = 7048619) B7048619
theorem B4699133 : Blo 1391515 4699133 := bstep (se 3 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 4699133 = 1762175) B1762175
theorem B5289563 : Blo 1391515 5289563 := bstep (se 1 (by rfl) ⟨3967172, by rfl⟩ : syracuseStep 5289563 = 7934345) B7934345
theorem B35665595 : Blo 1391515 35665595 := bstep (se 1 (by rfl) ⟨26749196, by rfl⟩ : syracuseStep 35665595 = 53498393) B53498393
theorem B626120513 : Blo 1391515 626120513 := bstep (se 2 (by rfl) ⟨234795192, by rfl⟩ : syracuseStep 626120513 = 469590385) B469590385
theorem B2643833 : Blo 1391515 2643833 := bstep (se 2 (by rfl) ⟨991437, by rfl⟩ : syracuseStep 2643833 = 1982875) B1982875
theorem B2087375 : Blo 1391515 2087375 := bstep (se 1 (by rfl) ⟨1565531, by rfl⟩ : syracuseStep 2087375 = 3131063) B3131063
theorem B8042975 : Blo 1391515 8042975 := bstep (se 1 (by rfl) ⟨6032231, by rfl⟩ : syracuseStep 8042975 = 12064463) B12064463
theorem B4700699 : Blo 1391515 4700699 := bstep (se 1 (by rfl) ⟨3525524, by rfl⟩ : syracuseStep 4700699 = 7051049) B7051049
theorem B2087801 : Blo 1391515 2087801 := bstep (se 2 (by rfl) ⟨782925, by rfl⟩ : syracuseStep 2087801 = 1565851) B1565851
theorem B2088047 : Blo 1391515 2088047 := bstep (se 1 (by rfl) ⟨1566035, by rfl⟩ : syracuseStep 2088047 = 3132071) B3132071
theorem B2350343 : Blo 1391515 2350343 := bstep (se 1 (by rfl) ⟨1762757, by rfl⟩ : syracuseStep 2350343 = 3525515) B3525515
theorem B34323871 : Blo 1391515 34323871 := bstep (se 1 (by rfl) ⟨25742903, by rfl⟩ : syracuseStep 34323871 = 51485807) B51485807
theorem B30514643 : Blo 1391515 30514643 := bstep (se 1 (by rfl) ⟨22885982, by rfl⟩ : syracuseStep 30514643 = 45771965) B45771965
theorem B15048155 : Blo 1391515 15048155 := bstep (se 1 (by rfl) ⟨11286116, by rfl⟩ : syracuseStep 15048155 = 22572233) B22572233
theorem B10575359 : Blo 1391515 10575359 := bstep (se 1 (by rfl) ⟨7931519, by rfl⟩ : syracuseStep 10575359 = 15863039) B15863039
theorem B2350633 : Blo 1391515 2350633 := bstep (se 2 (by rfl) ⟨881487, by rfl⟩ : syracuseStep 2350633 = 1762975) B1762975
theorem B2350775 : Blo 1391515 2350775 := bstep (se 1 (by rfl) ⟨1763081, by rfl⟩ : syracuseStep 2350775 = 3526163) B3526163
theorem B1392411 : Blo 1391515 1392411 := bstep (se 1 (by rfl) ⟨1044308, by rfl⟩ : syracuseStep 1392411 = 2088617) B2088617
theorem B2088767 : Blo 1391515 2088767 := bstep (se 1 (by rfl) ⟨1566575, by rfl⟩ : syracuseStep 2088767 = 3133151) B3133151
theorem B5357609 : Blo 1391515 5357609 := bstep (se 2 (by rfl) ⟨2009103, by rfl⟩ : syracuseStep 5357609 = 4018207) B4018207
theorem B1392731 : Blo 1391515 1392731 := bstep (se 1 (by rfl) ⟨1044548, by rfl⟩ : syracuseStep 1392731 = 2089097) B2089097
theorem B23790185 : Blo 1391515 23790185 := bstep (se 2 (by rfl) ⟨8921319, by rfl⟩ : syracuseStep 23790185 = 17842639) B17842639
theorem B11289203 : Blo 1391515 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B308872061 : Blo 1391515 308872061 := bstep (se 3 (by rfl) ⟨57913511, by rfl⟩ : syracuseStep 308872061 = 115827023) B115827023
theorem B2089865 : Blo 1391515 2089865 := bstep (se 2 (by rfl) ⟨783699, by rfl⟩ : syracuseStep 2089865 = 1567399) B1567399
theorem B7046027 : Blo 1391515 7046027 := bstep (se 1 (by rfl) ⟨5284520, by rfl⟩ : syracuseStep 7046027 = 10569041) B10569041
theorem B1762555 : Blo 1391515 1762555 := bstep (se 1 (by rfl) ⟨1321916, by rfl⟩ : syracuseStep 1762555 = 2643833) B2643833
theorem B3524087 : Blo 1391515 3524087 := bstep (se 1 (by rfl) ⟨2643065, by rfl⟩ : syracuseStep 3524087 = 5286131) B5286131
theorem B173934215 : Blo 1391515 173934215 := bstep (se 1 (by rfl) ⟨130450661, by rfl⟩ : syracuseStep 173934215 = 260901323) B260901323
theorem B1672859 : Blo 1391515 1672859 := bstep (se 1 (by rfl) ⟨1254644, by rfl⟩ : syracuseStep 1672859 = 2509289) B2509289
theorem B3524735 : Blo 1391515 3524735 := bstep (se 1 (by rfl) ⟨2643551, by rfl⟩ : syracuseStep 3524735 = 5287103) B5287103
theorem B1566895 : Blo 1391515 1566895 := bstep (se 1 (by rfl) ⟨1175171, by rfl⟩ : syracuseStep 1566895 = 2350343) B2350343
theorem B20343095 : Blo 1391515 20343095 := bstep (se 1 (by rfl) ⟨15257321, by rfl⟩ : syracuseStep 20343095 = 30514643) B30514643
theorem B2976097 : Blo 1391515 2976097 := bstep (se 2 (by rfl) ⟨1116036, by rfl⟩ : syracuseStep 2976097 = 2232073) B2232073
theorem B1567183 : Blo 1391515 1567183 := bstep (se 1 (by rfl) ⟨1175387, by rfl⟩ : syracuseStep 1567183 = 2350775) B2350775
theorem B3132719 : Blo 1391515 3132719 := bstep (se 1 (by rfl) ⟨2349539, by rfl⟩ : syracuseStep 3132719 = 4699079) B4699079
theorem B3132755 : Blo 1391515 3132755 := bstep (se 1 (by rfl) ⟨2349566, by rfl⟩ : syracuseStep 3132755 = 4699133) B4699133
theorem B24112547 : Blo 1391515 24112547 := bstep (se 1 (by rfl) ⟨18084410, by rfl⟩ : syracuseStep 24112547 = 36168821) B36168821
theorem B3526375 : Blo 1391515 3526375 := bstep (se 1 (by rfl) ⟨2644781, by rfl⟩ : syracuseStep 3526375 = 5289563) B5289563
theorem B23777063 : Blo 1391515 23777063 := bstep (se 1 (by rfl) ⟨17832797, by rfl⟩ : syracuseStep 23777063 = 35665595) B35665595
theorem B8040383 : Blo 1391515 8040383 := bstep (se 1 (by rfl) ⟨6030287, by rfl⟩ : syracuseStep 8040383 = 12060575) B12060575
theorem B5361983 : Blo 1391515 5361983 := bstep (se 1 (by rfl) ⟨4021487, by rfl⟩ : syracuseStep 5361983 = 8042975) B8042975
theorem B3133799 : Blo 1391515 3133799 := bstep (se 1 (by rfl) ⟨2350349, by rfl⟩ : syracuseStep 3133799 = 4700699) B4700699
theorem B4698539 : Blo 1391515 4698539 := bstep (se 1 (by rfl) ⟨3523904, by rfl⟩ : syracuseStep 4698539 = 7047809) B7047809
theorem B45765161 : Blo 1391515 45765161 := bstep (se 2 (by rfl) ⟨17161935, by rfl⟩ : syracuseStep 45765161 = 34323871) B34323871
theorem B11285081 : Blo 1391515 11285081 := bstep (se 2 (by rfl) ⟨4231905, by rfl⟩ : syracuseStep 11285081 = 8463811) B8463811
theorem B3134177 : Blo 1391515 3134177 := bstep (se 2 (by rfl) ⟨1175316, by rfl⟩ : syracuseStep 3134177 = 2350633) B2350633
theorem B4698971 : Blo 1391515 4698971 := bstep (se 1 (by rfl) ⟨3524228, by rfl⟩ : syracuseStep 4698971 = 7048457) B7048457
theorem B10032103 : Blo 1391515 10032103 := bstep (se 1 (by rfl) ⟨7524077, by rfl⟩ : syracuseStep 10032103 = 15048155) B15048155
theorem B7050239 : Blo 1391515 7050239 := bstep (se 1 (by rfl) ⟨5287679, by rfl⟩ : syracuseStep 7050239 = 10575359) B10575359
theorem B4232321 : Blo 1391515 4232321 := bstep (se 2 (by rfl) ⟨1587120, by rfl⟩ : syracuseStep 4232321 = 3174241) B3174241
theorem B23803307 : Blo 1391515 23803307 := bstep (se 1 (by rfl) ⟨17852480, by rfl⟩ : syracuseStep 23803307 = 35704961) B35704961
theorem B11449835 : Blo 1391515 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B17856125 : Blo 1391515 17856125 := bstep (se 3 (by rfl) ⟨3348023, by rfl⟩ : syracuseStep 17856125 = 6696047) B6696047
theorem B7247593 : Blo 1391515 7247593 := bstep (se 2 (by rfl) ⟨2717847, by rfl⟩ : syracuseStep 7247593 = 5435695) B5435695
theorem B11295071 : Blo 1391515 11295071 := bstep (se 1 (by rfl) ⟨8471303, by rfl⟩ : syracuseStep 11295071 = 16942607) B16942607
theorem B417413675 : Blo 1391515 417413675 := bstep (se 1 (by rfl) ⟨313060256, by rfl⟩ : syracuseStep 417413675 = 626120513) B626120513
theorem B1391583 : Blo 1391515 1391583 := bstep (se 1 (by rfl) ⟨1043687, by rfl⟩ : syracuseStep 1391583 = 2087375) B2087375
theorem B10574873 : Blo 1391515 10574873 := bstep (se 2 (by rfl) ⟨3965577, by rfl⟩ : syracuseStep 10574873 = 7931155) B7931155
theorem B1391867 : Blo 1391515 1391867 := bstep (se 1 (by rfl) ⟨1043900, by rfl⟩ : syracuseStep 1391867 = 2087801) B2087801
theorem B1392031 : Blo 1391515 1392031 := bstep (se 1 (by rfl) ⟨1044023, by rfl⟩ : syracuseStep 1392031 = 2088047) B2088047
theorem B1392511 : Blo 1391515 1392511 := bstep (se 1 (by rfl) ⟨1044383, by rfl⟩ : syracuseStep 1392511 = 2088767) B2088767
theorem B3571739 : Blo 1391515 3571739 := bstep (se 1 (by rfl) ⟨2678804, by rfl⟩ : syracuseStep 3571739 = 5357609) B5357609
theorem B2089193 : Blo 1391515 2089193 := bstep (se 2 (by rfl) ⟨783447, by rfl⟩ : syracuseStep 2089193 = 1566895) B1566895
theorem B2089199 : Blo 1391515 2089199 := bstep (se 1 (by rfl) ⟨1566899, by rfl⟩ : syracuseStep 2089199 = 3133799) B3133799
theorem B15860123 : Blo 1391515 15860123 := bstep (se 1 (by rfl) ⟨11895092, by rfl⟩ : syracuseStep 15860123 = 23790185) B23790185
theorem B2089451 : Blo 1391515 2089451 := bstep (se 1 (by rfl) ⟨1567088, by rfl⟩ : syracuseStep 2089451 = 3134177) B3134177
theorem B205914707 : Blo 1391515 205914707 := bstep (se 1 (by rfl) ⟨154436030, by rfl⟩ : syracuseStep 205914707 = 308872061) B308872061
theorem B1393243 : Blo 1391515 1393243 := bstep (se 1 (by rfl) ⟨1044932, by rfl⟩ : syracuseStep 1393243 = 2089865) B2089865
theorem B2089577 : Blo 1391515 2089577 := bstep (se 2 (by rfl) ⟨783591, by rfl⟩ : syracuseStep 2089577 = 1567183) B1567183
theorem B15868871 : Blo 1391515 15868871 := bstep (se 1 (by rfl) ⟨11901653, by rfl⟩ : syracuseStep 15868871 = 23803307) B23803307
theorem B11904083 : Blo 1391515 11904083 := bstep (se 1 (by rfl) ⟨8928062, by rfl⟩ : syracuseStep 11904083 = 17856125) B17856125
theorem B7530047 : Blo 1391515 7530047 := bstep (se 1 (by rfl) ⟨5647535, by rfl⟩ : syracuseStep 7530047 = 11295071) B11295071
theorem B278275783 : Blo 1391515 278275783 := bstep (se 1 (by rfl) ⟨208706837, by rfl⟩ : syracuseStep 278275783 = 417413675) B417413675
theorem B16075031 : Blo 1391515 16075031 := bstep (se 1 (by rfl) ⟨12056273, by rfl⟩ : syracuseStep 16075031 = 24112547) B24112547
theorem B5360255 : Blo 1391515 5360255 := bstep (se 1 (by rfl) ⟨4020191, by rfl⟩ : syracuseStep 5360255 = 8040383) B8040383
theorem B3574655 : Blo 1391515 3574655 := bstep (se 1 (by rfl) ⟨2680991, by rfl⟩ : syracuseStep 3574655 = 5361983) B5361983
theorem B3132359 : Blo 1391515 3132359 := bstep (se 1 (by rfl) ⟨2349269, by rfl⟩ : syracuseStep 3132359 = 4698539) B4698539
theorem B30510107 : Blo 1391515 30510107 := bstep (se 1 (by rfl) ⟨22882580, by rfl⟩ : syracuseStep 30510107 = 45765161) B45765161
theorem B7523387 : Blo 1391515 7523387 := bstep (se 1 (by rfl) ⟨5642540, by rfl⟩ : syracuseStep 7523387 = 11285081) B11285081
theorem B3968129 : Blo 1391515 3968129 := bstep (se 2 (by rfl) ⟨1488048, by rfl⟩ : syracuseStep 3968129 = 2976097) B2976097
theorem B3132647 : Blo 1391515 3132647 := bstep (se 1 (by rfl) ⟨2349485, by rfl⟩ : syracuseStep 3132647 = 4698971) B4698971
theorem B4697351 : Blo 1391515 4697351 := bstep (se 1 (by rfl) ⟨3523013, by rfl⟩ : syracuseStep 4697351 = 7046027) B7046027
theorem B2821547 : Blo 1391515 2821547 := bstep (se 1 (by rfl) ⟨2116160, by rfl⟩ : syracuseStep 2821547 = 4232321) B4232321
theorem B13562063 : Blo 1391515 13562063 := bstep (se 1 (by rfl) ⟨10171547, by rfl⟩ : syracuseStep 13562063 = 20343095) B20343095
theorem B4460957 : Blo 1391515 4460957 := bstep (se 3 (by rfl) ⟨836429, by rfl⟩ : syracuseStep 4460957 = 1672859) B1672859
theorem B7049915 : Blo 1391515 7049915 := bstep (se 1 (by rfl) ⟨5287436, by rfl⟩ : syracuseStep 7049915 = 10574873) B10574873
theorem B9663457 : Blo 1391515 9663457 := bstep (se 2 (by rfl) ⟨3623796, by rfl⟩ : syracuseStep 9663457 = 7247593) B7247593
theorem B7526135 : Blo 1391515 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B4700159 : Blo 1391515 4700159 := bstep (se 1 (by rfl) ⟨3525119, by rfl⟩ : syracuseStep 4700159 = 7050239) B7050239
theorem B7633223 : Blo 1391515 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B2349391 : Blo 1391515 2349391 := bstep (se 1 (by rfl) ⟨1762043, by rfl⟩ : syracuseStep 2349391 = 3524087) B3524087
theorem B115956143 : Blo 1391515 115956143 := bstep (se 1 (by rfl) ⟨86967107, by rfl⟩ : syracuseStep 115956143 = 173934215) B173934215
theorem B13376137 : Blo 1391515 13376137 := bstep (se 2 (by rfl) ⟨5016051, by rfl⟩ : syracuseStep 13376137 = 10032103) B10032103
theorem B2349823 : Blo 1391515 2349823 := bstep (se 1 (by rfl) ⟨1762367, by rfl⟩ : syracuseStep 2349823 = 3524735) B3524735
theorem B2350073 : Blo 1391515 2350073 := bstep (se 2 (by rfl) ⟨881277, by rfl⟩ : syracuseStep 2350073 = 1762555) B1762555
theorem B2088479 : Blo 1391515 2088479 := bstep (se 1 (by rfl) ⟨1566359, by rfl⟩ : syracuseStep 2088479 = 3132719) B3132719
theorem B2088503 : Blo 1391515 2088503 := bstep (se 1 (by rfl) ⟨1566377, by rfl⟩ : syracuseStep 2088503 = 3132755) B3132755
theorem B4701833 : Blo 1391515 4701833 := bstep (se 2 (by rfl) ⟨1763187, by rfl⟩ : syracuseStep 4701833 = 3526375) B3526375
theorem B15851375 : Blo 1391515 15851375 := bstep (se 1 (by rfl) ⟨11888531, by rfl⟩ : syracuseStep 15851375 = 23777063) B23777063
theorem B1392795 : Blo 1391515 1392795 := bstep (se 1 (by rfl) ⟨1044596, by rfl⟩ : syracuseStep 1392795 = 2089193) B2089193
theorem B1392799 : Blo 1391515 1392799 := bstep (se 1 (by rfl) ⟨1044599, by rfl⟩ : syracuseStep 1392799 = 2089199) B2089199
theorem B2973971 : Blo 1391515 2973971 := bstep (se 1 (by rfl) ⟨2230478, by rfl⟩ : syracuseStep 2973971 = 4460957) B4460957
theorem B1392967 : Blo 1391515 1392967 := bstep (se 1 (by rfl) ⟨1044725, by rfl⟩ : syracuseStep 1392967 = 2089451) B2089451
theorem B1393051 : Blo 1391515 1393051 := bstep (se 1 (by rfl) ⟨1044788, by rfl⟩ : syracuseStep 1393051 = 2089577) B2089577
theorem B17834849 : Blo 1391515 17834849 := bstep (se 2 (by rfl) ⟨6688068, by rfl⟩ : syracuseStep 17834849 = 13376137) B13376137
theorem B5088815 : Blo 1391515 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B3573503 : Blo 1391515 3573503 := bstep (se 1 (by rfl) ⟨2680127, by rfl⟩ : syracuseStep 3573503 = 5360255) B5360255
theorem B1566715 : Blo 1391515 1566715 := bstep (se 1 (by rfl) ⟨1175036, by rfl⟩ : syracuseStep 1566715 = 2350073) B2350073
theorem B5015591 : Blo 1391515 5015591 := bstep (se 1 (by rfl) ⟨3761693, by rfl⟩ : syracuseStep 5015591 = 7523387) B7523387
theorem B3131567 : Blo 1391515 3131567 := bstep (se 1 (by rfl) ⟨2348675, by rfl⟩ : syracuseStep 3131567 = 4697351) B4697351
theorem B371034377 : Blo 1391515 371034377 := bstep (se 2 (by rfl) ⟨139137891, by rfl⟩ : syracuseStep 371034377 = 278275783) B278275783
theorem B137276471 : Blo 1391515 137276471 := bstep (se 1 (by rfl) ⟨102957353, by rfl⟩ : syracuseStep 137276471 = 205914707) B205914707
theorem B3132521 : Blo 1391515 3132521 := bstep (se 2 (by rfl) ⟨1174695, by rfl⟩ : syracuseStep 3132521 = 2349391) B2349391
theorem B10579247 : Blo 1391515 10579247 := bstep (se 1 (by rfl) ⟨7934435, by rfl⟩ : syracuseStep 10579247 = 15868871) B15868871
theorem B3133097 : Blo 1391515 3133097 := bstep (se 2 (by rfl) ⟨1174911, by rfl⟩ : syracuseStep 3133097 = 2349823) B2349823
theorem B5017423 : Blo 1391515 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B3133439 : Blo 1391515 3133439 := bstep (se 1 (by rfl) ⟨2350079, by rfl⟩ : syracuseStep 3133439 = 4700159) B4700159
theorem B77304095 : Blo 1391515 77304095 := bstep (se 1 (by rfl) ⟨57978071, by rfl⟩ : syracuseStep 77304095 = 115956143) B115956143
theorem B1881031 : Blo 1391515 1881031 := bstep (se 1 (by rfl) ⟨1410773, by rfl⟩ : syracuseStep 1881031 = 2821547) B2821547
theorem B3134555 : Blo 1391515 3134555 := bstep (se 1 (by rfl) ⟨2350916, by rfl⟩ : syracuseStep 3134555 = 4701833) B4701833
theorem B2381159 : Blo 1391515 2381159 := bstep (se 1 (by rfl) ⟨1785869, by rfl⟩ : syracuseStep 2381159 = 3571739) B3571739
theorem B9041375 : Blo 1391515 9041375 := bstep (se 1 (by rfl) ⟨6781031, by rfl⟩ : syracuseStep 9041375 = 13562063) B13562063
theorem B10573415 : Blo 1391515 10573415 := bstep (se 1 (by rfl) ⟨7930061, by rfl⟩ : syracuseStep 10573415 = 15860123) B15860123
theorem B10581677 : Blo 1391515 10581677 := bstep (se 3 (by rfl) ⟨1984064, by rfl⟩ : syracuseStep 10581677 = 3968129) B3968129
theorem B4699943 : Blo 1391515 4699943 := bstep (se 1 (by rfl) ⟨3524957, by rfl⟩ : syracuseStep 4699943 = 7049915) B7049915
theorem B7936055 : Blo 1391515 7936055 := bstep (se 1 (by rfl) ⟨5952041, by rfl⟩ : syracuseStep 7936055 = 11904083) B11904083
theorem B42866749 : Blo 1391515 42866749 := bstep (se 3 (by rfl) ⟨8037515, by rfl⟩ : syracuseStep 42866749 = 16075031) B16075031
theorem B5020031 : Blo 1391515 5020031 := bstep (se 1 (by rfl) ⟨3765023, by rfl⟩ : syracuseStep 5020031 = 7530047) B7530047
theorem B12884609 : Blo 1391515 12884609 := bstep (se 2 (by rfl) ⟨4831728, by rfl⟩ : syracuseStep 12884609 = 9663457) B9663457
theorem B2383103 : Blo 1391515 2383103 := bstep (se 1 (by rfl) ⟨1787327, by rfl⟩ : syracuseStep 2383103 = 3574655) B3574655
theorem B2088239 : Blo 1391515 2088239 := bstep (se 1 (by rfl) ⟨1566179, by rfl⟩ : syracuseStep 2088239 = 3132359) B3132359
theorem B20340071 : Blo 1391515 20340071 := bstep (se 1 (by rfl) ⟨15255053, by rfl⟩ : syracuseStep 20340071 = 30510107) B30510107
theorem B2088431 : Blo 1391515 2088431 := bstep (se 1 (by rfl) ⟨1566323, by rfl⟩ : syracuseStep 2088431 = 3132647) B3132647
theorem B1392319 : Blo 1391515 1392319 := bstep (se 1 (by rfl) ⟨1044239, by rfl⟩ : syracuseStep 1392319 = 2088479) B2088479
theorem B1392335 : Blo 1391515 1392335 := bstep (se 1 (by rfl) ⟨1044251, by rfl⟩ : syracuseStep 1392335 = 2088503) B2088503
theorem B10567583 : Blo 1391515 10567583 := bstep (se 1 (by rfl) ⟨7925687, by rfl⟩ : syracuseStep 10567583 = 15851375) B15851375
theorem B1982647 : Blo 1391515 1982647 := bstep (se 1 (by rfl) ⟨1486985, by rfl⟩ : syracuseStep 1982647 = 2973971) B2973971
theorem B51536063 : Blo 1391515 51536063 := bstep (se 1 (by rfl) ⟨38652047, by rfl⟩ : syracuseStep 51536063 = 77304095) B77304095
theorem B228622661 : Blo 1391515 228622661 := bstep (se 4 (by rfl) ⟨21433374, by rfl⟩ : syracuseStep 228622661 = 42866749) B42866749
theorem B2089703 : Blo 1391515 2089703 := bstep (se 1 (by rfl) ⟨1567277, by rfl⟩ : syracuseStep 2089703 = 3134555) B3134555
theorem B3392543 : Blo 1391515 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B7054451 : Blo 1391515 7054451 := bstep (se 1 (by rfl) ⟨5290838, by rfl⟩ : syracuseStep 7054451 = 10581677) B10581677
theorem B2508041 : Blo 1391515 2508041 := bstep (se 2 (by rfl) ⟨940515, by rfl⟩ : syracuseStep 2508041 = 1881031) B1881031
theorem B3343727 : Blo 1391515 3343727 := bstep (se 1 (by rfl) ⟨2507795, by rfl⟩ : syracuseStep 3343727 = 5015591) B5015591
theorem B34358957 : Blo 1391515 34358957 := bstep (se 3 (by rfl) ⟨6442304, by rfl⟩ : syracuseStep 34358957 = 12884609) B12884609
theorem B13560047 : Blo 1391515 13560047 := bstep (se 1 (by rfl) ⟨10170035, by rfl⟩ : syracuseStep 13560047 = 20340071) B20340071
theorem B11889899 : Blo 1391515 11889899 := bstep (se 1 (by rfl) ⟨8917424, by rfl⟩ : syracuseStep 11889899 = 17834849) B17834849
theorem B7048943 : Blo 1391515 7048943 := bstep (se 1 (by rfl) ⟨5286707, by rfl⟩ : syracuseStep 7048943 = 10573415) B10573415
theorem B3133295 : Blo 1391515 3133295 := bstep (se 1 (by rfl) ⟨2349971, by rfl⟩ : syracuseStep 3133295 = 4699943) B4699943
theorem B3346687 : Blo 1391515 3346687 := bstep (se 1 (by rfl) ⟨2510015, by rfl⟩ : syracuseStep 3346687 = 5020031) B5020031
theorem B91517647 : Blo 1391515 91517647 := bstep (se 1 (by rfl) ⟨68638235, by rfl⟩ : syracuseStep 91517647 = 137276471) B137276471
theorem B6689897 : Blo 1391515 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B1587439 : Blo 1391515 1587439 := bstep (se 1 (by rfl) ⟨1190579, by rfl⟩ : syracuseStep 1587439 = 2381159) B2381159
theorem B6027583 : Blo 1391515 6027583 := bstep (se 1 (by rfl) ⟨4520687, by rfl⟩ : syracuseStep 6027583 = 9041375) B9041375
theorem B2382335 : Blo 1391515 2382335 := bstep (se 1 (by rfl) ⟨1786751, by rfl⟩ : syracuseStep 2382335 = 3573503) B3573503
theorem B5290703 : Blo 1391515 5290703 := bstep (se 1 (by rfl) ⟨3968027, by rfl⟩ : syracuseStep 5290703 = 7936055) B7936055
theorem B2087711 : Blo 1391515 2087711 := bstep (se 1 (by rfl) ⟨1565783, by rfl⟩ : syracuseStep 2087711 = 3131567) B3131567
theorem B247356251 : Blo 1391515 247356251 := bstep (se 1 (by rfl) ⟨185517188, by rfl⟩ : syracuseStep 247356251 = 371034377) B371034377
theorem B2088347 : Blo 1391515 2088347 := bstep (se 1 (by rfl) ⟨1566260, by rfl⟩ : syracuseStep 2088347 = 3132521) B3132521
theorem B1588735 : Blo 1391515 1588735 := bstep (se 1 (by rfl) ⟨1191551, by rfl⟩ : syracuseStep 1588735 = 2383103) B2383103
theorem B1392159 : Blo 1391515 1392159 := bstep (se 1 (by rfl) ⟨1044119, by rfl⟩ : syracuseStep 1392159 = 2088239) B2088239
theorem B7052831 : Blo 1391515 7052831 := bstep (se 1 (by rfl) ⟨5289623, by rfl⟩ : syracuseStep 7052831 = 10579247) B10579247
theorem B1392287 : Blo 1391515 1392287 := bstep (se 1 (by rfl) ⟨1044215, by rfl⟩ : syracuseStep 1392287 = 2088431) B2088431
theorem B2088953 : Blo 1391515 2088953 := bstep (se 2 (by rfl) ⟨783357, by rfl⟩ : syracuseStep 2088953 = 1566715) B1566715
theorem B2088959 : Blo 1391515 2088959 := bstep (se 1 (by rfl) ⟨1566719, by rfl⟩ : syracuseStep 2088959 = 3133439) B3133439
theorem B2088731 : Blo 1391515 2088731 := bstep (se 1 (by rfl) ⟨1566548, by rfl⟩ : syracuseStep 2088731 = 3133097) B3133097
theorem B7045055 : Blo 1391515 7045055 := bstep (se 1 (by rfl) ⟨5283791, by rfl⟩ : syracuseStep 7045055 = 10567583) B10567583
theorem B34357375 : Blo 1391515 34357375 := bstep (se 1 (by rfl) ⟨25768031, by rfl⟩ : syracuseStep 34357375 = 51536063) B51536063
theorem B8036777 : Blo 1391515 8036777 := bstep (se 2 (by rfl) ⟨3013791, by rfl⟩ : syracuseStep 8036777 = 6027583) B6027583
theorem B1393135 : Blo 1391515 1393135 := bstep (se 1 (by rfl) ⟨1044851, by rfl⟩ : syracuseStep 1393135 = 2089703) B2089703
theorem B4702967 : Blo 1391515 4702967 := bstep (se 1 (by rfl) ⟨3527225, by rfl⟩ : syracuseStep 4702967 = 7054451) B7054451
theorem B22905971 : Blo 1391515 22905971 := bstep (se 1 (by rfl) ⟨17179478, by rfl⟩ : syracuseStep 22905971 = 34358957) B34358957
theorem B1392635 : Blo 1391515 1392635 := bstep (se 1 (by rfl) ⟨1044476, by rfl⟩ : syracuseStep 1392635 = 2088953) B2088953
theorem B4696703 : Blo 1391515 4696703 := bstep (se 1 (by rfl) ⟨3522527, by rfl⟩ : syracuseStep 4696703 = 7045055) B7045055
theorem B9046781 : Blo 1391515 9046781 := bstep (se 3 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 9046781 = 3392543) B3392543
theorem B152415107 : Blo 1391515 152415107 := bstep (se 1 (by rfl) ⟨114311330, by rfl⟩ : syracuseStep 152415107 = 228622661) B228622661
theorem B2116585 : Blo 1391515 2116585 := bstep (se 2 (by rfl) ⟨793719, by rfl⟩ : syracuseStep 2116585 = 1587439) B1587439
theorem B6688109 : Blo 1391515 6688109 := bstep (se 3 (by rfl) ⟨1254020, by rfl⟩ : syracuseStep 6688109 = 2508041) B2508041
theorem B4459931 : Blo 1391515 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B122023529 : Blo 1391515 122023529 := bstep (se 2 (by rfl) ⟨45758823, by rfl⟩ : syracuseStep 122023529 = 91517647) B91517647
theorem B8916605 : Blo 1391515 8916605 := bstep (se 3 (by rfl) ⟨1671863, by rfl⟩ : syracuseStep 8916605 = 3343727) B3343727
theorem B9040031 : Blo 1391515 9040031 := bstep (se 1 (by rfl) ⟨6780023, by rfl⟩ : syracuseStep 9040031 = 13560047) B13560047
theorem B3527135 : Blo 1391515 3527135 := bstep (se 1 (by rfl) ⟨2645351, by rfl⟩ : syracuseStep 3527135 = 5290703) B5290703
theorem B2118313 : Blo 1391515 2118313 := bstep (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) B1588735
theorem B7926599 : Blo 1391515 7926599 := bstep (se 1 (by rfl) ⟨5944949, by rfl⟩ : syracuseStep 7926599 = 11889899) B11889899
theorem B4699295 : Blo 1391515 4699295 := bstep (se 1 (by rfl) ⟨3524471, by rfl⟩ : syracuseStep 4699295 = 7048943) B7048943
theorem B2643529 : Blo 1391515 2643529 := bstep (se 2 (by rfl) ⟨991323, by rfl⟩ : syracuseStep 2643529 = 1982647) B1982647
theorem B17848997 : Blo 1391515 17848997 := bstep (se 4 (by rfl) ⟨1673343, by rfl⟩ : syracuseStep 17848997 = 3346687) B3346687
theorem B1391807 : Blo 1391515 1391807 := bstep (se 1 (by rfl) ⟨1043855, by rfl⟩ : syracuseStep 1391807 = 2087711) B2087711
theorem B164904167 : Blo 1391515 164904167 := bstep (se 1 (by rfl) ⟨123678125, by rfl⟩ : syracuseStep 164904167 = 247356251) B247356251
theorem B1392231 : Blo 1391515 1392231 := bstep (se 1 (by rfl) ⟨1044173, by rfl⟩ : syracuseStep 1392231 = 2088347) B2088347
theorem B4701887 : Blo 1391515 4701887 := bstep (se 1 (by rfl) ⟨3526415, by rfl⟩ : syracuseStep 4701887 = 7052831) B7052831
theorem B1392487 : Blo 1391515 1392487 := bstep (se 1 (by rfl) ⟨1044365, by rfl⟩ : syracuseStep 1392487 = 2088731) B2088731
theorem B2088863 : Blo 1391515 2088863 := bstep (se 1 (by rfl) ⟨1566647, by rfl⟩ : syracuseStep 2088863 = 3133295) B3133295
theorem B25411573 : Blo 1391515 25411573 := bstep (se 5 (by rfl) ⟨1191167, by rfl⟩ : syracuseStep 25411573 = 2382335) B2382335
theorem B1392639 : Blo 1391515 1392639 := bstep (se 1 (by rfl) ⟨1044479, by rfl⟩ : syracuseStep 1392639 = 2088959) B2088959
theorem B45809833 : Blo 1391515 45809833 := bstep (se 2 (by rfl) ⟨17178687, by rfl⟩ : syracuseStep 45809833 = 34357375) B34357375
theorem B5357851 : Blo 1391515 5357851 := bstep (se 1 (by rfl) ⟨4018388, by rfl⟩ : syracuseStep 5357851 = 8036777) B8036777
theorem B2351423 : Blo 1391515 2351423 := bstep (se 1 (by rfl) ⟨1763567, by rfl⟩ : syracuseStep 2351423 = 3527135) B3527135
theorem B5284399 : Blo 1391515 5284399 := bstep (se 1 (by rfl) ⟨3963299, by rfl⟩ : syracuseStep 5284399 = 7926599) B7926599
theorem B15270647 : Blo 1391515 15270647 := bstep (se 1 (by rfl) ⟨11452985, by rfl⟩ : syracuseStep 15270647 = 22905971) B22905971
theorem B3131135 : Blo 1391515 3131135 := bstep (se 1 (by rfl) ⟨2348351, by rfl⟩ : syracuseStep 3131135 = 4696703) B4696703
theorem B6031187 : Blo 1391515 6031187 := bstep (se 1 (by rfl) ⟨4523390, by rfl⟩ : syracuseStep 6031187 = 9046781) B9046781
theorem B3524705 : Blo 1391515 3524705 := bstep (se 2 (by rfl) ⟨1321764, by rfl⟩ : syracuseStep 3524705 = 2643529) B2643529
theorem B4458739 : Blo 1391515 4458739 := bstep (se 1 (by rfl) ⟨3344054, by rfl⟩ : syracuseStep 4458739 = 6688109) B6688109
theorem B81349019 : Blo 1391515 81349019 := bstep (se 1 (by rfl) ⟨61011764, by rfl⟩ : syracuseStep 81349019 = 122023529) B122023529
theorem B3132863 : Blo 1391515 3132863 := bstep (se 1 (by rfl) ⟨2349647, by rfl⟩ : syracuseStep 3132863 = 4699295) B4699295
theorem B2822113 : Blo 1391515 2822113 := bstep (se 2 (by rfl) ⟨1058292, by rfl⟩ : syracuseStep 2822113 = 2116585) B2116585
theorem B11899331 : Blo 1391515 11899331 := bstep (se 1 (by rfl) ⟨8924498, by rfl⟩ : syracuseStep 11899331 = 17848997) B17848997
theorem B101610071 : Blo 1391515 101610071 := bstep (se 1 (by rfl) ⟨76207553, by rfl⟩ : syracuseStep 101610071 = 152415107) B152415107
theorem B5944403 : Blo 1391515 5944403 := bstep (se 1 (by rfl) ⟨4458302, by rfl⟩ : syracuseStep 5944403 = 8916605) B8916605
theorem B3134591 : Blo 1391515 3134591 := bstep (se 1 (by rfl) ⟨2350943, by rfl⟩ : syracuseStep 3134591 = 4701887) B4701887
theorem B6026687 : Blo 1391515 6026687 := bstep (se 1 (by rfl) ⟨4520015, by rfl⟩ : syracuseStep 6026687 = 9040031) B9040031
theorem B3135311 : Blo 1391515 3135311 := bstep (se 1 (by rfl) ⟨2351483, by rfl⟩ : syracuseStep 3135311 = 4702967) B4702967
theorem B2824417 : Blo 1391515 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B109936111 : Blo 1391515 109936111 := bstep (se 1 (by rfl) ⟨82452083, by rfl⟩ : syracuseStep 109936111 = 164904167) B164904167
theorem B2973287 : Blo 1391515 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B1392575 : Blo 1391515 1392575 := bstep (se 1 (by rfl) ⟨1044431, by rfl⟩ : syracuseStep 1392575 = 2088863) B2088863
theorem B33882097 : Blo 1391515 33882097 := bstep (se 2 (by rfl) ⟨12705786, by rfl⟩ : syracuseStep 33882097 = 25411573) B25411573
theorem B61079777 : Blo 1391515 61079777 := bstep (se 2 (by rfl) ⟨22904916, by rfl⟩ : syracuseStep 61079777 = 45809833) B45809833
theorem B67740047 : Blo 1391515 67740047 := bstep (se 1 (by rfl) ⟨50805035, by rfl⟩ : syracuseStep 67740047 = 101610071) B101610071
theorem B7045865 : Blo 1391515 7045865 := bstep (se 2 (by rfl) ⟨2642199, by rfl⟩ : syracuseStep 7045865 = 5284399) B5284399
theorem B2089727 : Blo 1391515 2089727 := bstep (se 1 (by rfl) ⟨1567295, by rfl⟩ : syracuseStep 2089727 = 3134591) B3134591
theorem B2090207 : Blo 1391515 2090207 := bstep (se 1 (by rfl) ⟨1567655, by rfl⟩ : syracuseStep 2090207 = 3135311) B3135311
theorem B54232679 : Blo 1391515 54232679 := bstep (se 1 (by rfl) ⟨40674509, by rfl⟩ : syracuseStep 54232679 = 81349019) B81349019
theorem B146581481 : Blo 1391515 146581481 := bstep (se 2 (by rfl) ⟨54968055, by rfl⟩ : syracuseStep 146581481 = 109936111) B109936111
theorem B3762817 : Blo 1391515 3762817 := bstep (se 2 (by rfl) ⟨1411056, by rfl⟩ : syracuseStep 3762817 = 2822113) B2822113
theorem B1567615 : Blo 1391515 1567615 := bstep (se 1 (by rfl) ⟨1175711, by rfl⟩ : syracuseStep 1567615 = 2351423) B2351423
theorem B7932887 : Blo 1391515 7932887 := bstep (se 1 (by rfl) ⟨5949665, by rfl⟩ : syracuseStep 7932887 = 11899331) B11899331
theorem B4017791 : Blo 1391515 4017791 := bstep (se 1 (by rfl) ⟨3013343, by rfl⟩ : syracuseStep 4017791 = 6026687) B6026687
theorem B45176129 : Blo 1391515 45176129 := bstep (se 2 (by rfl) ⟨16941048, by rfl⟩ : syracuseStep 45176129 = 33882097) B33882097
theorem B3765889 : Blo 1391515 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B5944985 : Blo 1391515 5944985 := bstep (se 2 (by rfl) ⟨2229369, by rfl⟩ : syracuseStep 5944985 = 4458739) B4458739
theorem B114300821 : Blo 1391515 114300821 := bstep (se 6 (by rfl) ⟨2678925, by rfl⟩ : syracuseStep 114300821 = 5357851) B5357851
theorem B3962935 : Blo 1391515 3962935 := bstep (se 1 (by rfl) ⟨2972201, by rfl⟩ : syracuseStep 3962935 = 5944403) B5944403
theorem B2087423 : Blo 1391515 2087423 := bstep (se 1 (by rfl) ⟨1565567, by rfl⟩ : syracuseStep 2087423 = 3131135) B3131135
theorem B4020791 : Blo 1391515 4020791 := bstep (se 1 (by rfl) ⟨3015593, by rfl⟩ : syracuseStep 4020791 = 6031187) B6031187
theorem B2349803 : Blo 1391515 2349803 := bstep (se 1 (by rfl) ⟨1762352, by rfl⟩ : syracuseStep 2349803 = 3524705) B3524705
theorem B7928765 : Blo 1391515 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B40721725 : Blo 1391515 40721725 := bstep (se 3 (by rfl) ⟨7635323, by rfl⟩ : syracuseStep 40721725 = 15270647) B15270647
theorem B2088575 : Blo 1391515 2088575 := bstep (se 1 (by rfl) ⟨1566431, by rfl⟩ : syracuseStep 2088575 = 3132863) B3132863
theorem B5283913 : Blo 1391515 5283913 := bstep (se 2 (by rfl) ⟨1981467, by rfl⟩ : syracuseStep 5283913 = 3962935) B3962935
theorem B1393151 : Blo 1391515 1393151 := bstep (se 1 (by rfl) ⟨1044863, by rfl⟩ : syracuseStep 1393151 = 2089727) B2089727
theorem B1393471 : Blo 1391515 1393471 := bstep (se 1 (by rfl) ⟨1045103, by rfl⟩ : syracuseStep 1393471 = 2090207) B2090207
theorem B2090153 : Blo 1391515 2090153 := bstep (se 2 (by rfl) ⟨783807, by rfl⟩ : syracuseStep 2090153 = 1567615) B1567615
theorem B1566535 : Blo 1391515 1566535 := bstep (se 1 (by rfl) ⟨1174901, by rfl⟩ : syracuseStep 1566535 = 2349803) B2349803
theorem B5285843 : Blo 1391515 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B4697243 : Blo 1391515 4697243 := bstep (se 1 (by rfl) ⟨3522932, by rfl⟩ : syracuseStep 4697243 = 7045865) B7045865
theorem B42888437 : Blo 1391515 42888437 := bstep (se 5 (by rfl) ⟨2010395, by rfl⟩ : syracuseStep 42888437 = 4020791) B4020791
theorem B30117419 : Blo 1391515 30117419 := bstep (se 1 (by rfl) ⟨22588064, by rfl⟩ : syracuseStep 30117419 = 45176129) B45176129
theorem B36155119 : Blo 1391515 36155119 := bstep (se 1 (by rfl) ⟨27116339, by rfl⟩ : syracuseStep 36155119 = 54232679) B54232679
theorem B5288591 : Blo 1391515 5288591 := bstep (se 1 (by rfl) ⟨3966443, by rfl⟩ : syracuseStep 5288591 = 7932887) B7932887
theorem B40719851 : Blo 1391515 40719851 := bstep (se 1 (by rfl) ⟨30539888, by rfl⟩ : syracuseStep 40719851 = 61079777) B61079777
theorem B45160031 : Blo 1391515 45160031 := bstep (se 1 (by rfl) ⟨33870023, by rfl⟩ : syracuseStep 45160031 = 67740047) B67740047
theorem B20068357 : Blo 1391515 20068357 := bstep (se 4 (by rfl) ⟨1881408, by rfl⟩ : syracuseStep 20068357 = 3762817) B3762817
theorem B3963323 : Blo 1391515 3963323 := bstep (se 1 (by rfl) ⟨2972492, by rfl⟩ : syracuseStep 3963323 = 5944985) B5944985
theorem B76200547 : Blo 1391515 76200547 := bstep (se 1 (by rfl) ⟨57150410, by rfl⟩ : syracuseStep 76200547 = 114300821) B114300821
theorem B97720987 : Blo 1391515 97720987 := bstep (se 1 (by rfl) ⟨73290740, by rfl⟩ : syracuseStep 97720987 = 146581481) B146581481
theorem B1391615 : Blo 1391515 1391615 := bstep (se 1 (by rfl) ⟨1043711, by rfl⟩ : syracuseStep 1391615 = 2087423) B2087423
theorem B54295633 : Blo 1391515 54295633 := bstep (se 2 (by rfl) ⟨20360862, by rfl⟩ : syracuseStep 54295633 = 40721725) B40721725
theorem B5021185 : Blo 1391515 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B2678527 : Blo 1391515 2678527 := bstep (se 1 (by rfl) ⟨2008895, by rfl⟩ : syracuseStep 2678527 = 4017791) B4017791
theorem B1392383 : Blo 1391515 1392383 := bstep (se 1 (by rfl) ⟨1044287, by rfl⟩ : syracuseStep 1392383 = 2088575) B2088575
theorem B7045217 : Blo 1391515 7045217 := bstep (se 2 (by rfl) ⟨2641956, by rfl⟩ : syracuseStep 7045217 = 5283913) B5283913
theorem B1393435 : Blo 1391515 1393435 := bstep (se 1 (by rfl) ⟨1045076, by rfl⟩ : syracuseStep 1393435 = 2090153) B2090153
theorem B130294649 : Blo 1391515 130294649 := bstep (se 2 (by rfl) ⟨48860493, by rfl⟩ : syracuseStep 130294649 = 97720987) B97720987
theorem B30106687 : Blo 1391515 30106687 := bstep (se 1 (by rfl) ⟨22580015, by rfl⟩ : syracuseStep 30106687 = 45160031) B45160031
theorem B3523895 : Blo 1391515 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B72394177 : Blo 1391515 72394177 := bstep (se 2 (by rfl) ⟨27147816, by rfl⟩ : syracuseStep 72394177 = 54295633) B54295633
theorem B6694913 : Blo 1391515 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B3131495 : Blo 1391515 3131495 := bstep (se 1 (by rfl) ⟨2348621, by rfl⟩ : syracuseStep 3131495 = 4697243) B4697243
theorem B28592291 : Blo 1391515 28592291 := bstep (se 1 (by rfl) ⟨21444218, by rfl⟩ : syracuseStep 28592291 = 42888437) B42888437
theorem B26757809 : Blo 1391515 26757809 := bstep (se 2 (by rfl) ⟨10034178, by rfl⟩ : syracuseStep 26757809 = 20068357) B20068357
theorem B3525727 : Blo 1391515 3525727 := bstep (se 1 (by rfl) ⟨2644295, by rfl⟩ : syracuseStep 3525727 = 5288591) B5288591
theorem B101600729 : Blo 1391515 101600729 := bstep (se 2 (by rfl) ⟨38100273, by rfl⟩ : syracuseStep 101600729 = 76200547) B76200547
theorem B2642215 : Blo 1391515 2642215 := bstep (se 1 (by rfl) ⟨1981661, by rfl⟩ : syracuseStep 2642215 = 3963323) B3963323
theorem B48206825 : Blo 1391515 48206825 := bstep (se 2 (by rfl) ⟨18077559, by rfl⟩ : syracuseStep 48206825 = 36155119) B36155119
theorem B27146567 : Blo 1391515 27146567 := bstep (se 1 (by rfl) ⟨20359925, by rfl⟩ : syracuseStep 27146567 = 40719851) B40719851
theorem B14285477 : Blo 1391515 14285477 := bstep (se 4 (by rfl) ⟨1339263, by rfl⟩ : syracuseStep 14285477 = 2678527) B2678527
theorem B20078279 : Blo 1391515 20078279 := bstep (se 1 (by rfl) ⟨15058709, by rfl⟩ : syracuseStep 20078279 = 30117419) B30117419
theorem B2088713 : Blo 1391515 2088713 := bstep (se 2 (by rfl) ⟨783267, by rfl⟩ : syracuseStep 2088713 = 1566535) B1566535
theorem B3522953 : Blo 1391515 3522953 := bstep (se 2 (by rfl) ⟨1321107, by rfl⟩ : syracuseStep 3522953 = 2642215) B2642215
theorem B32137883 : Blo 1391515 32137883 := bstep (se 1 (by rfl) ⟨24103412, by rfl⟩ : syracuseStep 32137883 = 48206825) B48206825
theorem B40142249 : Blo 1391515 40142249 := bstep (se 2 (by rfl) ⟨15053343, by rfl⟩ : syracuseStep 40142249 = 30106687) B30106687
theorem B67733819 : Blo 1391515 67733819 := bstep (se 1 (by rfl) ⟨50800364, by rfl⟩ : syracuseStep 67733819 = 101600729) B101600729
theorem B4696811 : Blo 1391515 4696811 := bstep (se 1 (by rfl) ⟨3522608, by rfl⟩ : syracuseStep 4696811 = 7045217) B7045217
theorem B86863099 : Blo 1391515 86863099 := bstep (se 1 (by rfl) ⟨65147324, by rfl⟩ : syracuseStep 86863099 = 130294649) B130294649
theorem B9523651 : Blo 1391515 9523651 := bstep (se 1 (by rfl) ⟨7142738, by rfl⟩ : syracuseStep 9523651 = 14285477) B14285477
theorem B17838539 : Blo 1391515 17838539 := bstep (se 1 (by rfl) ⟨13378904, by rfl⟩ : syracuseStep 17838539 = 26757809) B26757809
theorem B72390845 : Blo 1391515 72390845 := bstep (se 3 (by rfl) ⟨13573283, by rfl⟩ : syracuseStep 72390845 = 27146567) B27146567
theorem B2349263 : Blo 1391515 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B4463275 : Blo 1391515 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B2087663 : Blo 1391515 2087663 := bstep (se 1 (by rfl) ⟨1565747, by rfl⟩ : syracuseStep 2087663 = 3131495) B3131495
theorem B19061527 : Blo 1391515 19061527 := bstep (se 1 (by rfl) ⟨14296145, by rfl⟩ : syracuseStep 19061527 = 28592291) B28592291
theorem B4700969 : Blo 1391515 4700969 := bstep (se 2 (by rfl) ⟨1762863, by rfl⟩ : syracuseStep 4700969 = 3525727) B3525727
theorem B96525569 : Blo 1391515 96525569 := bstep (se 2 (by rfl) ⟨36197088, by rfl⟩ : syracuseStep 96525569 = 72394177) B72394177
theorem B13385519 : Blo 1391515 13385519 := bstep (se 1 (by rfl) ⟨10039139, by rfl⟩ : syracuseStep 13385519 = 20078279) B20078279
theorem B1392475 : Blo 1391515 1392475 := bstep (se 1 (by rfl) ⟨1044356, by rfl⟩ : syracuseStep 1392475 = 2088713) B2088713
theorem B12698201 : Blo 1391515 12698201 := bstep (se 2 (by rfl) ⟨4761825, by rfl⟩ : syracuseStep 12698201 = 9523651) B9523651
theorem B1566175 : Blo 1391515 1566175 := bstep (se 1 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 1566175 = 2349263) B2349263
theorem B45155879 : Blo 1391515 45155879 := bstep (se 1 (by rfl) ⟨33866909, by rfl⟩ : syracuseStep 45155879 = 67733819) B67733819
theorem B3131207 : Blo 1391515 3131207 := bstep (se 1 (by rfl) ⟨2348405, by rfl⟩ : syracuseStep 3131207 = 4696811) B4696811
theorem B64350379 : Blo 1391515 64350379 := bstep (se 1 (by rfl) ⟨48262784, by rfl⟩ : syracuseStep 64350379 = 96525569) B96525569
theorem B8923679 : Blo 1391515 8923679 := bstep (se 1 (by rfl) ⟨6692759, by rfl⟩ : syracuseStep 8923679 = 13385519) B13385519
theorem B21425255 : Blo 1391515 21425255 := bstep (se 1 (by rfl) ⟨16068941, by rfl⟩ : syracuseStep 21425255 = 32137883) B32137883
theorem B5951033 : Blo 1391515 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B25415369 : Blo 1391515 25415369 := bstep (se 2 (by rfl) ⟨9530763, by rfl⟩ : syracuseStep 25415369 = 19061527) B19061527
theorem B3133979 : Blo 1391515 3133979 := bstep (se 1 (by rfl) ⟨2350484, by rfl⟩ : syracuseStep 3133979 = 4700969) B4700969
theorem B2348635 : Blo 1391515 2348635 := bstep (se 1 (by rfl) ⟨1761476, by rfl⟩ : syracuseStep 2348635 = 3522953) B3522953
theorem B11892359 : Blo 1391515 11892359 := bstep (se 1 (by rfl) ⟨8919269, by rfl⟩ : syracuseStep 11892359 = 17838539) B17838539
theorem B193042253 : Blo 1391515 193042253 := bstep (se 3 (by rfl) ⟨36195422, by rfl⟩ : syracuseStep 193042253 = 72390845) B72390845
theorem B26761499 : Blo 1391515 26761499 := bstep (se 1 (by rfl) ⟨20071124, by rfl⟩ : syracuseStep 26761499 = 40142249) B40142249
theorem B115817465 : Blo 1391515 115817465 := bstep (se 2 (by rfl) ⟨43431549, by rfl⟩ : syracuseStep 115817465 = 86863099) B86863099
theorem B1391775 : Blo 1391515 1391775 := bstep (se 1 (by rfl) ⟨1043831, by rfl⟩ : syracuseStep 1391775 = 2087663) B2087663
theorem B2089319 : Blo 1391515 2089319 := bstep (se 1 (by rfl) ⟨1566989, by rfl⟩ : syracuseStep 2089319 = 3133979) B3133979
theorem B5949119 : Blo 1391515 5949119 := bstep (se 1 (by rfl) ⟨4461839, by rfl⟩ : syracuseStep 5949119 = 8923679) B8923679
theorem B77211643 : Blo 1391515 77211643 := bstep (se 1 (by rfl) ⟨57908732, by rfl⟩ : syracuseStep 77211643 = 115817465) B115817465
theorem B3131513 : Blo 1391515 3131513 := bstep (se 2 (by rfl) ⟨1174317, by rfl⟩ : syracuseStep 3131513 = 2348635) B2348635
theorem B3967355 : Blo 1391515 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B16943579 : Blo 1391515 16943579 := bstep (se 1 (by rfl) ⟨12707684, by rfl⟩ : syracuseStep 16943579 = 25415369) B25415369
theorem B8465467 : Blo 1391515 8465467 := bstep (se 1 (by rfl) ⟨6349100, by rfl⟩ : syracuseStep 8465467 = 12698201) B12698201
theorem B14283503 : Blo 1391515 14283503 := bstep (se 1 (by rfl) ⟨10712627, by rfl⟩ : syracuseStep 14283503 = 21425255) B21425255
theorem B85800505 : Blo 1391515 85800505 := bstep (se 2 (by rfl) ⟨32175189, by rfl⟩ : syracuseStep 85800505 = 64350379) B64350379
theorem B30103919 : Blo 1391515 30103919 := bstep (se 1 (by rfl) ⟨22577939, by rfl⟩ : syracuseStep 30103919 = 45155879) B45155879
theorem B7928239 : Blo 1391515 7928239 := bstep (se 1 (by rfl) ⟨5946179, by rfl⟩ : syracuseStep 7928239 = 11892359) B11892359
theorem B2087471 : Blo 1391515 2087471 := bstep (se 1 (by rfl) ⟨1565603, by rfl⟩ : syracuseStep 2087471 = 3131207) B3131207
theorem B128694835 : Blo 1391515 128694835 := bstep (se 1 (by rfl) ⟨96521126, by rfl⟩ : syracuseStep 128694835 = 193042253) B193042253
theorem B17840999 : Blo 1391515 17840999 := bstep (se 1 (by rfl) ⟨13380749, by rfl⟩ : syracuseStep 17840999 = 26761499) B26761499
theorem B2088233 : Blo 1391515 2088233 := bstep (se 2 (by rfl) ⟨783087, by rfl⟩ : syracuseStep 2088233 = 1566175) B1566175
theorem B1392879 : Blo 1391515 1392879 := bstep (se 1 (by rfl) ⟨1044659, by rfl⟩ : syracuseStep 1392879 = 2089319) B2089319
theorem B3966079 : Blo 1391515 3966079 := bstep (se 1 (by rfl) ⟨2974559, by rfl⟩ : syracuseStep 3966079 = 5949119) B5949119
theorem B9522335 : Blo 1391515 9522335 := bstep (se 1 (by rfl) ⟨7141751, by rfl⟩ : syracuseStep 9522335 = 14283503) B14283503
theorem B10570985 : Blo 1391515 10570985 := bstep (se 2 (by rfl) ⟨3964119, by rfl⟩ : syracuseStep 10570985 = 7928239) B7928239
theorem B171593113 : Blo 1391515 171593113 := bstep (se 2 (by rfl) ⟨64347417, by rfl⟩ : syracuseStep 171593113 = 128694835) B128694835
theorem B11287289 : Blo 1391515 11287289 := bstep (se 2 (by rfl) ⟨4232733, by rfl⟩ : syracuseStep 11287289 = 8465467) B8465467
theorem B2087675 : Blo 1391515 2087675 := bstep (se 1 (by rfl) ⟨1565756, by rfl⟩ : syracuseStep 2087675 = 3131513) B3131513
theorem B20069279 : Blo 1391515 20069279 := bstep (se 1 (by rfl) ⟨15051959, by rfl⟩ : syracuseStep 20069279 = 30103919) B30103919
theorem B2644903 : Blo 1391515 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B11295719 : Blo 1391515 11295719 := bstep (se 1 (by rfl) ⟨8471789, by rfl⟩ : syracuseStep 11295719 = 16943579) B16943579
theorem B1391647 : Blo 1391515 1391647 := bstep (se 1 (by rfl) ⟨1043735, by rfl⟩ : syracuseStep 1391647 = 2087471) B2087471
theorem B11893999 : Blo 1391515 11893999 := bstep (se 1 (by rfl) ⟨8920499, by rfl⟩ : syracuseStep 11893999 = 17840999) B17840999
theorem B114400673 : Blo 1391515 114400673 := bstep (se 2 (by rfl) ⟨42900252, by rfl⟩ : syracuseStep 114400673 = 85800505) B85800505
theorem B1392155 : Blo 1391515 1392155 := bstep (se 1 (by rfl) ⟨1044116, by rfl⟩ : syracuseStep 1392155 = 2088233) B2088233
theorem B102948857 : Blo 1391515 102948857 := bstep (se 2 (by rfl) ⟨38605821, by rfl⟩ : syracuseStep 102948857 = 77211643) B77211643
theorem B13379519 : Blo 1391515 13379519 := bstep (se 1 (by rfl) ⟨10034639, by rfl⟩ : syracuseStep 13379519 = 20069279) B20069279
theorem B7530479 : Blo 1391515 7530479 := bstep (se 1 (by rfl) ⟨5647859, by rfl⟩ : syracuseStep 7530479 = 11295719) B11295719
theorem B7047323 : Blo 1391515 7047323 := bstep (se 1 (by rfl) ⟨5285492, by rfl⟩ : syracuseStep 7047323 = 10570985) B10570985
theorem B3526537 : Blo 1391515 3526537 := bstep (se 2 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 3526537 = 2644903) B2644903
theorem B5288105 : Blo 1391515 5288105 := bstep (se 2 (by rfl) ⟨1983039, by rfl⟩ : syracuseStep 5288105 = 3966079) B3966079
theorem B7524859 : Blo 1391515 7524859 := bstep (se 1 (by rfl) ⟨5643644, by rfl⟩ : syracuseStep 7524859 = 11287289) B11287289
theorem B228790817 : Blo 1391515 228790817 := bstep (se 2 (by rfl) ⟨85796556, by rfl⟩ : syracuseStep 228790817 = 171593113) B171593113
theorem B15858665 : Blo 1391515 15858665 := bstep (se 2 (by rfl) ⟨5946999, by rfl⟩ : syracuseStep 15858665 = 11893999) B11893999
theorem B1391783 : Blo 1391515 1391783 := bstep (se 1 (by rfl) ⟨1043837, by rfl⟩ : syracuseStep 1391783 = 2087675) B2087675
theorem B6348223 : Blo 1391515 6348223 := bstep (se 1 (by rfl) ⟨4761167, by rfl⟩ : syracuseStep 6348223 = 9522335) B9522335
theorem B76267115 : Blo 1391515 76267115 := bstep (se 1 (by rfl) ⟨57200336, by rfl⟩ : syracuseStep 76267115 = 114400673) B114400673
theorem B68632571 : Blo 1391515 68632571 := bstep (se 1 (by rfl) ⟨51474428, by rfl⟩ : syracuseStep 68632571 = 102948857) B102948857
theorem B152527211 : Blo 1391515 152527211 := bstep (se 1 (by rfl) ⟨114395408, by rfl⟩ : syracuseStep 152527211 = 228790817) B228790817
theorem B35678717 : Blo 1391515 35678717 := bstep (se 3 (by rfl) ⟨6689759, by rfl⟩ : syracuseStep 35678717 = 13379519) B13379519
theorem B45755047 : Blo 1391515 45755047 := bstep (se 1 (by rfl) ⟨34316285, by rfl⟩ : syracuseStep 45755047 = 68632571) B68632571
theorem B3525403 : Blo 1391515 3525403 := bstep (se 1 (by rfl) ⟨2644052, by rfl⟩ : syracuseStep 3525403 = 5288105) B5288105
theorem B4698215 : Blo 1391515 4698215 := bstep (se 1 (by rfl) ⟨3523661, by rfl⟩ : syracuseStep 4698215 = 7047323) B7047323
theorem B10572443 : Blo 1391515 10572443 := bstep (se 1 (by rfl) ⟨7929332, by rfl⟩ : syracuseStep 10572443 = 15858665) B15858665
theorem B50844743 : Blo 1391515 50844743 := bstep (se 1 (by rfl) ⟨38133557, by rfl⟩ : syracuseStep 50844743 = 76267115) B76267115
theorem B10033145 : Blo 1391515 10033145 := bstep (se 2 (by rfl) ⟨3762429, by rfl⟩ : syracuseStep 10033145 = 7524859) B7524859
theorem B5020319 : Blo 1391515 5020319 := bstep (se 1 (by rfl) ⟨3765239, by rfl⟩ : syracuseStep 5020319 = 7530479) B7530479
theorem B33857189 : Blo 1391515 33857189 := bstep (se 4 (by rfl) ⟨3174111, by rfl⟩ : syracuseStep 33857189 = 6348223) B6348223
theorem B4702049 : Blo 1391515 4702049 := bstep (se 2 (by rfl) ⟨1763268, by rfl⟩ : syracuseStep 4702049 = 3526537) B3526537
theorem B13387517 : Blo 1391515 13387517 := bstep (se 3 (by rfl) ⟨2510159, by rfl⟩ : syracuseStep 13387517 = 5020319) B5020319
theorem B22571459 : Blo 1391515 22571459 := bstep (se 1 (by rfl) ⟨16928594, by rfl⟩ : syracuseStep 22571459 = 33857189) B33857189
theorem B3132143 : Blo 1391515 3132143 := bstep (se 1 (by rfl) ⟨2349107, by rfl⟩ : syracuseStep 3132143 = 4698215) B4698215
theorem B7048295 : Blo 1391515 7048295 := bstep (se 1 (by rfl) ⟨5286221, by rfl⟩ : syracuseStep 7048295 = 10572443) B10572443
theorem B244026917 : Blo 1391515 244026917 := bstep (se 4 (by rfl) ⟨22877523, by rfl⟩ : syracuseStep 244026917 = 45755047) B45755047
theorem B6688763 : Blo 1391515 6688763 := bstep (se 1 (by rfl) ⟨5016572, by rfl⟩ : syracuseStep 6688763 = 10033145) B10033145
theorem B23785811 : Blo 1391515 23785811 := bstep (se 1 (by rfl) ⟨17839358, by rfl⟩ : syracuseStep 23785811 = 35678717) B35678717
theorem B3134699 : Blo 1391515 3134699 := bstep (se 1 (by rfl) ⟨2351024, by rfl⟩ : syracuseStep 3134699 = 4702049) B4702049
theorem B101684807 : Blo 1391515 101684807 := bstep (se 1 (by rfl) ⟨76263605, by rfl⟩ : syracuseStep 101684807 = 152527211) B152527211
theorem B33896495 : Blo 1391515 33896495 := bstep (se 1 (by rfl) ⟨25422371, by rfl⟩ : syracuseStep 33896495 = 50844743) B50844743
theorem B4700537 : Blo 1391515 4700537 := bstep (se 2 (by rfl) ⟨1762701, by rfl⟩ : syracuseStep 4700537 = 3525403) B3525403
theorem B2089799 : Blo 1391515 2089799 := bstep (se 1 (by rfl) ⟨1567349, by rfl⟩ : syracuseStep 2089799 = 3134699) B3134699
theorem B67789871 : Blo 1391515 67789871 := bstep (se 1 (by rfl) ⟨50842403, by rfl⟩ : syracuseStep 67789871 = 101684807) B101684807
theorem B4459175 : Blo 1391515 4459175 := bstep (se 1 (by rfl) ⟨3344381, by rfl⟩ : syracuseStep 4459175 = 6688763) B6688763
theorem B8925011 : Blo 1391515 8925011 := bstep (se 1 (by rfl) ⟨6693758, by rfl⟩ : syracuseStep 8925011 = 13387517) B13387517
theorem B22597663 : Blo 1391515 22597663 := bstep (se 1 (by rfl) ⟨16948247, by rfl⟩ : syracuseStep 22597663 = 33896495) B33896495
theorem B3133691 : Blo 1391515 3133691 := bstep (se 1 (by rfl) ⟨2350268, by rfl⟩ : syracuseStep 3133691 = 4700537) B4700537
theorem B4698863 : Blo 1391515 4698863 := bstep (se 1 (by rfl) ⟨3524147, by rfl⟩ : syracuseStep 4698863 = 7048295) B7048295
theorem B15857207 : Blo 1391515 15857207 := bstep (se 1 (by rfl) ⟨11892905, by rfl⟩ : syracuseStep 15857207 = 23785811) B23785811
theorem B15047639 : Blo 1391515 15047639 := bstep (se 1 (by rfl) ⟨11285729, by rfl⟩ : syracuseStep 15047639 = 22571459) B22571459
theorem B2088095 : Blo 1391515 2088095 := bstep (se 1 (by rfl) ⟨1566071, by rfl⟩ : syracuseStep 2088095 = 3132143) B3132143
theorem B162684611 : Blo 1391515 162684611 := bstep (se 1 (by rfl) ⟨122013458, by rfl⟩ : syracuseStep 162684611 = 244026917) B244026917
theorem B30130217 : Blo 1391515 30130217 := bstep (se 2 (by rfl) ⟨11298831, by rfl⟩ : syracuseStep 30130217 = 22597663) B22597663
theorem B2089127 : Blo 1391515 2089127 := bstep (se 1 (by rfl) ⟨1566845, by rfl⟩ : syracuseStep 2089127 = 3133691) B3133691
theorem B1393199 : Blo 1391515 1393199 := bstep (se 1 (by rfl) ⟨1044899, by rfl⟩ : syracuseStep 1393199 = 2089799) B2089799
theorem B108456407 : Blo 1391515 108456407 := bstep (se 1 (by rfl) ⟨81342305, by rfl⟩ : syracuseStep 108456407 = 162684611) B162684611
theorem B5950007 : Blo 1391515 5950007 := bstep (se 1 (by rfl) ⟨4462505, by rfl⟩ : syracuseStep 5950007 = 8925011) B8925011
theorem B3132575 : Blo 1391515 3132575 := bstep (se 1 (by rfl) ⟨2349431, by rfl⟩ : syracuseStep 3132575 = 4698863) B4698863
theorem B10571471 : Blo 1391515 10571471 := bstep (se 1 (by rfl) ⟨7928603, by rfl⟩ : syracuseStep 10571471 = 15857207) B15857207
theorem B10031759 : Blo 1391515 10031759 := bstep (se 1 (by rfl) ⟨7523819, by rfl⟩ : syracuseStep 10031759 = 15047639) B15047639
theorem B45193247 : Blo 1391515 45193247 := bstep (se 1 (by rfl) ⟨33894935, by rfl⟩ : syracuseStep 45193247 = 67789871) B67789871
theorem B2972783 : Blo 1391515 2972783 := bstep (se 1 (by rfl) ⟨2229587, by rfl⟩ : syracuseStep 2972783 = 4459175) B4459175
theorem B1392063 : Blo 1391515 1392063 := bstep (se 1 (by rfl) ⟨1044047, by rfl⟩ : syracuseStep 1392063 = 2088095) B2088095
theorem B20086811 : Blo 1391515 20086811 := bstep (se 1 (by rfl) ⟨15065108, by rfl⟩ : syracuseStep 20086811 = 30130217) B30130217
theorem B1392751 : Blo 1391515 1392751 := bstep (se 1 (by rfl) ⟨1044563, by rfl⟩ : syracuseStep 1392751 = 2089127) B2089127
theorem B72304271 : Blo 1391515 72304271 := bstep (se 1 (by rfl) ⟨54228203, by rfl⟩ : syracuseStep 72304271 = 108456407) B108456407
theorem B3966671 : Blo 1391515 3966671 := bstep (se 1 (by rfl) ⟨2975003, by rfl⟩ : syracuseStep 3966671 = 5950007) B5950007
theorem B7047647 : Blo 1391515 7047647 := bstep (se 1 (by rfl) ⟨5285735, by rfl⟩ : syracuseStep 7047647 = 10571471) B10571471
theorem B6687839 : Blo 1391515 6687839 := bstep (se 1 (by rfl) ⟨5015879, by rfl⟩ : syracuseStep 6687839 = 10031759) B10031759
theorem B30128831 : Blo 1391515 30128831 := bstep (se 1 (by rfl) ⟨22596623, by rfl⟩ : syracuseStep 30128831 = 45193247) B45193247
theorem B1981855 : Blo 1391515 1981855 := bstep (se 1 (by rfl) ⟨1486391, by rfl⟩ : syracuseStep 1981855 = 2972783) B2972783
theorem B2088383 : Blo 1391515 2088383 := bstep (se 1 (by rfl) ⟨1566287, by rfl⟩ : syracuseStep 2088383 = 3132575) B3132575
theorem B48202847 : Blo 1391515 48202847 := bstep (se 1 (by rfl) ⟨36152135, by rfl⟩ : syracuseStep 48202847 = 72304271) B72304271
theorem B10577789 : Blo 1391515 10577789 := bstep (se 3 (by rfl) ⟨1983335, by rfl⟩ : syracuseStep 10577789 = 3966671) B3966671
theorem B4458559 : Blo 1391515 4458559 := bstep (se 1 (by rfl) ⟨3343919, by rfl⟩ : syracuseStep 4458559 = 6687839) B6687839
theorem B4698431 : Blo 1391515 4698431 := bstep (se 1 (by rfl) ⟨3523823, by rfl⟩ : syracuseStep 4698431 = 7047647) B7047647
theorem B2642473 : Blo 1391515 2642473 := bstep (se 2 (by rfl) ⟨990927, by rfl⟩ : syracuseStep 2642473 = 1981855) B1981855
theorem B13391207 : Blo 1391515 13391207 := bstep (se 1 (by rfl) ⟨10043405, by rfl⟩ : syracuseStep 13391207 = 20086811) B20086811
theorem B20085887 : Blo 1391515 20085887 := bstep (se 1 (by rfl) ⟨15064415, by rfl⟩ : syracuseStep 20085887 = 30128831) B30128831
theorem B1392255 : Blo 1391515 1392255 := bstep (se 1 (by rfl) ⟨1044191, by rfl⟩ : syracuseStep 1392255 = 2088383) B2088383
theorem B3523297 : Blo 1391515 3523297 := bstep (se 2 (by rfl) ⟨1321236, by rfl⟩ : syracuseStep 3523297 = 2642473) B2642473
theorem B3132287 : Blo 1391515 3132287 := bstep (se 1 (by rfl) ⟨2349215, by rfl⟩ : syracuseStep 3132287 = 4698431) B4698431
theorem B13390591 : Blo 1391515 13390591 := bstep (se 1 (by rfl) ⟨10042943, by rfl⟩ : syracuseStep 13390591 = 20085887) B20085887
theorem B5944745 : Blo 1391515 5944745 := bstep (se 2 (by rfl) ⟨2229279, by rfl⟩ : syracuseStep 5944745 = 4458559) B4458559
theorem B32135231 : Blo 1391515 32135231 := bstep (se 1 (by rfl) ⟨24101423, by rfl⟩ : syracuseStep 32135231 = 48202847) B48202847
theorem B8927471 : Blo 1391515 8927471 := bstep (se 1 (by rfl) ⟨6695603, by rfl⟩ : syracuseStep 8927471 = 13391207) B13391207
theorem B7051859 : Blo 1391515 7051859 := bstep (se 1 (by rfl) ⟨5288894, by rfl⟩ : syracuseStep 7051859 = 10577789) B10577789
theorem B21423487 : Blo 1391515 21423487 := bstep (se 1 (by rfl) ⟨16067615, by rfl⟩ : syracuseStep 21423487 = 32135231) B32135231
theorem B4697729 : Blo 1391515 4697729 := bstep (se 2 (by rfl) ⟨1761648, by rfl⟩ : syracuseStep 4697729 = 3523297) B3523297
theorem B17854121 : Blo 1391515 17854121 := bstep (se 2 (by rfl) ⟨6695295, by rfl⟩ : syracuseStep 17854121 = 13390591) B13390591
theorem B5951647 : Blo 1391515 5951647 := bstep (se 1 (by rfl) ⟨4463735, by rfl⟩ : syracuseStep 5951647 = 8927471) B8927471
theorem B3963163 : Blo 1391515 3963163 := bstep (se 1 (by rfl) ⟨2972372, by rfl⟩ : syracuseStep 3963163 = 5944745) B5944745
theorem B4701239 : Blo 1391515 4701239 := bstep (se 1 (by rfl) ⟨3525929, by rfl⟩ : syracuseStep 4701239 = 7051859) B7051859
theorem B2088191 : Blo 1391515 2088191 := bstep (se 1 (by rfl) ⟨1566143, by rfl⟩ : syracuseStep 2088191 = 3132287) B3132287
theorem B5284217 : Blo 1391515 5284217 := bstep (se 2 (by rfl) ⟨1981581, by rfl⟩ : syracuseStep 5284217 = 3963163) B3963163
theorem B3131819 : Blo 1391515 3131819 := bstep (se 1 (by rfl) ⟨2348864, by rfl⟩ : syracuseStep 3131819 = 4697729) B4697729
theorem B3134159 : Blo 1391515 3134159 := bstep (se 1 (by rfl) ⟨2350619, by rfl⟩ : syracuseStep 3134159 = 4701239) B4701239
theorem B7935529 : Blo 1391515 7935529 := bstep (se 2 (by rfl) ⟨2975823, by rfl⟩ : syracuseStep 7935529 = 5951647) B5951647
theorem B28564649 : Blo 1391515 28564649 := bstep (se 2 (by rfl) ⟨10711743, by rfl⟩ : syracuseStep 28564649 = 21423487) B21423487
theorem B1392127 : Blo 1391515 1392127 := bstep (se 1 (by rfl) ⟨1044095, by rfl⟩ : syracuseStep 1392127 = 2088191) B2088191
theorem B11902747 : Blo 1391515 11902747 := bstep (se 1 (by rfl) ⟨8927060, by rfl⟩ : syracuseStep 11902747 = 17854121) B17854121
theorem B3522811 : Blo 1391515 3522811 := bstep (se 1 (by rfl) ⟨2642108, by rfl⟩ : syracuseStep 3522811 = 5284217) B5284217
theorem B2089439 : Blo 1391515 2089439 := bstep (se 1 (by rfl) ⟨1567079, by rfl⟩ : syracuseStep 2089439 = 3134159) B3134159
theorem B15870329 : Blo 1391515 15870329 := bstep (se 2 (by rfl) ⟨5951373, by rfl⟩ : syracuseStep 15870329 = 11902747) B11902747
theorem B10580705 : Blo 1391515 10580705 := bstep (se 2 (by rfl) ⟨3967764, by rfl⟩ : syracuseStep 10580705 = 7935529) B7935529
theorem B19043099 : Blo 1391515 19043099 := bstep (se 1 (by rfl) ⟨14282324, by rfl⟩ : syracuseStep 19043099 = 28564649) B28564649
theorem B2087879 : Blo 1391515 2087879 := bstep (se 1 (by rfl) ⟨1565909, by rfl⟩ : syracuseStep 2087879 = 3131819) B3131819
theorem B1392959 : Blo 1391515 1392959 := bstep (se 1 (by rfl) ⟨1044719, by rfl⟩ : syracuseStep 1392959 = 2089439) B2089439
theorem B7053803 : Blo 1391515 7053803 := bstep (se 1 (by rfl) ⟨5290352, by rfl⟩ : syracuseStep 7053803 = 10580705) B10580705
theorem B4697081 : Blo 1391515 4697081 := bstep (se 2 (by rfl) ⟨1761405, by rfl⟩ : syracuseStep 4697081 = 3522811) B3522811
theorem B10580219 : Blo 1391515 10580219 := bstep (se 1 (by rfl) ⟨7935164, by rfl⟩ : syracuseStep 10580219 = 15870329) B15870329
theorem B12695399 : Blo 1391515 12695399 := bstep (se 1 (by rfl) ⟨9521549, by rfl⟩ : syracuseStep 12695399 = 19043099) B19043099
theorem B1391919 : Blo 1391515 1391919 := bstep (se 1 (by rfl) ⟨1043939, by rfl⟩ : syracuseStep 1391919 = 2087879) B2087879
theorem B7053479 : Blo 1391515 7053479 := bstep (se 1 (by rfl) ⟨5290109, by rfl⟩ : syracuseStep 7053479 = 10580219) B10580219
theorem B4702535 : Blo 1391515 4702535 := bstep (se 1 (by rfl) ⟨3526901, by rfl⟩ : syracuseStep 4702535 = 7053803) B7053803
theorem B8463599 : Blo 1391515 8463599 := bstep (se 1 (by rfl) ⟨6347699, by rfl⟩ : syracuseStep 8463599 = 12695399) B12695399
theorem B3131387 : Blo 1391515 3131387 := bstep (se 1 (by rfl) ⟨2348540, by rfl⟩ : syracuseStep 3131387 = 4697081) B4697081
theorem B4702319 : Blo 1391515 4702319 := bstep (se 1 (by rfl) ⟨3526739, by rfl⟩ : syracuseStep 4702319 = 7053479) B7053479
theorem B3135023 : Blo 1391515 3135023 := bstep (se 1 (by rfl) ⟨2351267, by rfl⟩ : syracuseStep 3135023 = 4702535) B4702535
theorem B5642399 : Blo 1391515 5642399 := bstep (se 1 (by rfl) ⟨4231799, by rfl⟩ : syracuseStep 5642399 = 8463599) B8463599
theorem B2087591 : Blo 1391515 2087591 := bstep (se 1 (by rfl) ⟨1565693, by rfl⟩ : syracuseStep 2087591 = 3131387) B3131387
theorem B2090015 : Blo 1391515 2090015 := bstep (se 1 (by rfl) ⟨1567511, by rfl⟩ : syracuseStep 2090015 = 3135023) B3135023
theorem B3761599 : Blo 1391515 3761599 := bstep (se 1 (by rfl) ⟨2821199, by rfl⟩ : syracuseStep 3761599 = 5642399) B5642399
theorem B3134879 : Blo 1391515 3134879 := bstep (se 1 (by rfl) ⟨2351159, by rfl⟩ : syracuseStep 3134879 = 4702319) B4702319
theorem B1391727 : Blo 1391515 1391727 := bstep (se 1 (by rfl) ⟨1043795, by rfl⟩ : syracuseStep 1391727 = 2087591) B2087591
theorem B1393343 : Blo 1391515 1393343 := bstep (se 1 (by rfl) ⟨1045007, by rfl⟩ : syracuseStep 1393343 = 2090015) B2090015
theorem B2089919 : Blo 1391515 2089919 := bstep (se 1 (by rfl) ⟨1567439, by rfl⟩ : syracuseStep 2089919 = 3134879) B3134879
theorem B5015465 : Blo 1391515 5015465 := bstep (se 2 (by rfl) ⟨1880799, by rfl⟩ : syracuseStep 5015465 = 3761599) B3761599
theorem B1393279 : Blo 1391515 1393279 := bstep (se 1 (by rfl) ⟨1044959, by rfl⟩ : syracuseStep 1393279 = 2089919) B2089919
theorem B3343643 : Blo 1391515 3343643 := bstep (se 1 (by rfl) ⟨2507732, by rfl⟩ : syracuseStep 3343643 = 5015465) B5015465
theorem B2229095 : Blo 1391515 2229095 := bstep (se 1 (by rfl) ⟨1671821, by rfl⟩ : syracuseStep 2229095 = 3343643) B3343643
theorem B1486063 : Blo 1391515 1486063 := bstep (se 1 (by rfl) ⟨1114547, by rfl⟩ : syracuseStep 1486063 = 2229095) B2229095
theorem B1981417 : Blo 1391515 1981417 := bstep (se 2 (by rfl) ⟨743031, by rfl⟩ : syracuseStep 1981417 = 1486063) B1486063
theorem B2641889 : Blo 1391515 2641889 := bstep (se 2 (by rfl) ⟨990708, by rfl⟩ : syracuseStep 2641889 = 1981417) B1981417
theorem B1761259 : Blo 1391515 1761259 := bstep (se 1 (by rfl) ⟨1320944, by rfl⟩ : syracuseStep 1761259 = 2641889) B2641889
theorem B2348345 : Blo 1391515 2348345 := bstep (se 2 (by rfl) ⟨880629, by rfl⟩ : syracuseStep 2348345 = 1761259) B1761259
theorem B1565563 : Blo 1391515 1565563 := bstep (se 1 (by rfl) ⟨1174172, by rfl⟩ : syracuseStep 1565563 = 2348345) B2348345
theorem B2087417 : Blo 1391515 2087417 := bstep (se 2 (by rfl) ⟨782781, by rfl⟩ : syracuseStep 2087417 = 1565563) B1565563
theorem B1391611 : Blo 1391515 1391611 := bstep (se 1 (by rfl) ⟨1043708, by rfl⟩ : syracuseStep 1391611 = 2087417) B2087417

theorem C0 (j : ℕ) (h1 : 347878 ≤ j) (h2 : j ≤ 348378) : Blo 1391515 (4 * j + 3) := by
  interval_cases j
  · exact B1391515
  · exact B1391519
  · exact B1391523
  · exact B1391527
  · exact B1391531
  · exact B1391535
  · exact B1391539
  · exact B1391543
  · exact B1391547
  · exact B1391551
  · exact B1391555
  · exact B1391559
  · exact B1391563
  · exact B1391567
  · exact B1391571
  · exact B1391575
  · exact B1391579
  · exact B1391583
  · exact B1391587
  · exact B1391591
  · exact B1391595
  · exact B1391599
  · exact B1391603
  · exact B1391607
  · exact B1391611
  · exact B1391615
  · exact B1391619
  · exact B1391623
  · exact B1391627
  · exact B1391631
  · exact B1391635
  · exact B1391639
  · exact B1391643
  · exact B1391647
  · exact B1391651
  · exact B1391655
  · exact B1391659
  · exact B1391663
  · exact B1391667
  · exact B1391671
  · exact B1391675
  · exact B1391679
  · exact B1391683
  · exact B1391687
  · exact B1391691
  · exact B1391695
  · exact B1391699
  · exact B1391703
  · exact B1391707
  · exact B1391711
  · exact B1391715
  · exact B1391719
  · exact B1391723
  · exact B1391727
  · exact B1391731
  · exact B1391735
  · exact B1391739
  · exact B1391743
  · exact B1391747
  · exact B1391751
  · exact B1391755
  · exact B1391759
  · exact B1391763
  · exact B1391767
  · exact B1391771
  · exact B1391775
  · exact B1391779
  · exact B1391783
  · exact B1391787
  · exact B1391791
  · exact B1391795
  · exact B1391799
  · exact B1391803
  · exact B1391807
  · exact B1391811
  · exact B1391815
  · exact B1391819
  · exact B1391823
  · exact B1391827
  · exact B1391831
  · exact B1391835
  · exact B1391839
  · exact B1391843
  · exact B1391847
  · exact B1391851
  · exact B1391855
  · exact B1391859
  · exact B1391863
  · exact B1391867
  · exact B1391871
  · exact B1391875
  · exact B1391879
  · exact B1391883
  · exact B1391887
  · exact B1391891
  · exact B1391895
  · exact B1391899
  · exact B1391903
  · exact B1391907
  · exact B1391911
  · exact B1391915
  · exact B1391919
  · exact B1391923
  · exact B1391927
  · exact B1391931
  · exact B1391935
  · exact B1391939
  · exact B1391943
  · exact B1391947
  · exact B1391951
  · exact B1391955
  · exact B1391959
  · exact B1391963
  · exact B1391967
  · exact B1391971
  · exact B1391975
  · exact B1391979
  · exact B1391983
  · exact B1391987
  · exact B1391991
  · exact B1391995
  · exact B1391999
  · exact B1392003
  · exact B1392007
  · exact B1392011
  · exact B1392015
  · exact B1392019
  · exact B1392023
  · exact B1392027
  · exact B1392031
  · exact B1392035
  · exact B1392039
  · exact B1392043
  · exact B1392047
  · exact B1392051
  · exact B1392055
  · exact B1392059
  · exact B1392063
  · exact B1392067
  · exact B1392071
  · exact B1392075
  · exact B1392079
  · exact B1392083
  · exact B1392087
  · exact B1392091
  · exact B1392095
  · exact B1392099
  · exact B1392103
  · exact B1392107
  · exact B1392111
  · exact B1392115
  · exact B1392119
  · exact B1392123
  · exact B1392127
  · exact B1392131
  · exact B1392135
  · exact B1392139
  · exact B1392143
  · exact B1392147
  · exact B1392151
  · exact B1392155
  · exact B1392159
  · exact B1392163
  · exact B1392167
  · exact B1392171
  · exact B1392175
  · exact B1392179
  · exact B1392183
  · exact B1392187
  · exact B1392191
  · exact B1392195
  · exact B1392199
  · exact B1392203
  · exact B1392207
  · exact B1392211
  · exact B1392215
  · exact B1392219
  · exact B1392223
  · exact B1392227
  · exact B1392231
  · exact B1392235
  · exact B1392239
  · exact B1392243
  · exact B1392247
  · exact B1392251
  · exact B1392255
  · exact B1392259
  · exact B1392263
  · exact B1392267
  · exact B1392271
  · exact B1392275
  · exact B1392279
  · exact B1392283
  · exact B1392287
  · exact B1392291
  · exact B1392295
  · exact B1392299
  · exact B1392303
  · exact B1392307
  · exact B1392311
  · exact B1392315
  · exact B1392319
  · exact B1392323
  · exact B1392327
  · exact B1392331
  · exact B1392335
  · exact B1392339
  · exact B1392343
  · exact B1392347
  · exact B1392351
  · exact B1392355
  · exact B1392359
  · exact B1392363
  · exact B1392367
  · exact B1392371
  · exact B1392375
  · exact B1392379
  · exact B1392383
  · exact B1392387
  · exact B1392391
  · exact B1392395
  · exact B1392399
  · exact B1392403
  · exact B1392407
  · exact B1392411
  · exact B1392415
  · exact B1392419
  · exact B1392423
  · exact B1392427
  · exact B1392431
  · exact B1392435
  · exact B1392439
  · exact B1392443
  · exact B1392447
  · exact B1392451
  · exact B1392455
  · exact B1392459
  · exact B1392463
  · exact B1392467
  · exact B1392471
  · exact B1392475
  · exact B1392479
  · exact B1392483
  · exact B1392487
  · exact B1392491
  · exact B1392495
  · exact B1392499
  · exact B1392503
  · exact B1392507
  · exact B1392511
  · exact B1392515
  · exact B1392519
  · exact B1392523
  · exact B1392527
  · exact B1392531
  · exact B1392535
  · exact B1392539
  · exact B1392543
  · exact B1392547
  · exact B1392551
  · exact B1392555
  · exact B1392559
  · exact B1392563
  · exact B1392567
  · exact B1392571
  · exact B1392575
  · exact B1392579
  · exact B1392583
  · exact B1392587
  · exact B1392591
  · exact B1392595
  · exact B1392599
  · exact B1392603
  · exact B1392607
  · exact B1392611
  · exact B1392615
  · exact B1392619
  · exact B1392623
  · exact B1392627
  · exact B1392631
  · exact B1392635
  · exact B1392639
  · exact B1392643
  · exact B1392647
  · exact B1392651
  · exact B1392655
  · exact B1392659
  · exact B1392663
  · exact B1392667
  · exact B1392671
  · exact B1392675
  · exact B1392679
  · exact B1392683
  · exact B1392687
  · exact B1392691
  · exact B1392695
  · exact B1392699
  · exact B1392703
  · exact B1392707
  · exact B1392711
  · exact B1392715
  · exact B1392719
  · exact B1392723
  · exact B1392727
  · exact B1392731
  · exact B1392735
  · exact B1392739
  · exact B1392743
  · exact B1392747
  · exact B1392751
  · exact B1392755
  · exact B1392759
  · exact B1392763
  · exact B1392767
  · exact B1392771
  · exact B1392775
  · exact B1392779
  · exact B1392783
  · exact B1392787
  · exact B1392791
  · exact B1392795
  · exact B1392799
  · exact B1392803
  · exact B1392807
  · exact B1392811
  · exact B1392815
  · exact B1392819
  · exact B1392823
  · exact B1392827
  · exact B1392831
  · exact B1392835
  · exact B1392839
  · exact B1392843
  · exact B1392847
  · exact B1392851
  · exact B1392855
  · exact B1392859
  · exact B1392863
  · exact B1392867
  · exact B1392871
  · exact B1392875
  · exact B1392879
  · exact B1392883
  · exact B1392887
  · exact B1392891
  · exact B1392895
  · exact B1392899
  · exact B1392903
  · exact B1392907
  · exact B1392911
  · exact B1392915
  · exact B1392919
  · exact B1392923
  · exact B1392927
  · exact B1392931
  · exact B1392935
  · exact B1392939
  · exact B1392943
  · exact B1392947
  · exact B1392951
  · exact B1392955
  · exact B1392959
  · exact B1392963
  · exact B1392967
  · exact B1392971
  · exact B1392975
  · exact B1392979
  · exact B1392983
  · exact B1392987
  · exact B1392991
  · exact B1392995
  · exact B1392999
  · exact B1393003
  · exact B1393007
  · exact B1393011
  · exact B1393015
  · exact B1393019
  · exact B1393023
  · exact B1393027
  · exact B1393031
  · exact B1393035
  · exact B1393039
  · exact B1393043
  · exact B1393047
  · exact B1393051
  · exact B1393055
  · exact B1393059
  · exact B1393063
  · exact B1393067
  · exact B1393071
  · exact B1393075
  · exact B1393079
  · exact B1393083
  · exact B1393087
  · exact B1393091
  · exact B1393095
  · exact B1393099
  · exact B1393103
  · exact B1393107
  · exact B1393111
  · exact B1393115
  · exact B1393119
  · exact B1393123
  · exact B1393127
  · exact B1393131
  · exact B1393135
  · exact B1393139
  · exact B1393143
  · exact B1393147
  · exact B1393151
  · exact B1393155
  · exact B1393159
  · exact B1393163
  · exact B1393167
  · exact B1393171
  · exact B1393175
  · exact B1393179
  · exact B1393183
  · exact B1393187
  · exact B1393191
  · exact B1393195
  · exact B1393199
  · exact B1393203
  · exact B1393207
  · exact B1393211
  · exact B1393215
  · exact B1393219
  · exact B1393223
  · exact B1393227
  · exact B1393231
  · exact B1393235
  · exact B1393239
  · exact B1393243
  · exact B1393247
  · exact B1393251
  · exact B1393255
  · exact B1393259
  · exact B1393263
  · exact B1393267
  · exact B1393271
  · exact B1393275
  · exact B1393279
  · exact B1393283
  · exact B1393287
  · exact B1393291
  · exact B1393295
  · exact B1393299
  · exact B1393303
  · exact B1393307
  · exact B1393311
  · exact B1393315
  · exact B1393319
  · exact B1393323
  · exact B1393327
  · exact B1393331
  · exact B1393335
  · exact B1393339
  · exact B1393343
  · exact B1393347
  · exact B1393351
  · exact B1393355
  · exact B1393359
  · exact B1393363
  · exact B1393367
  · exact B1393371
  · exact B1393375
  · exact B1393379
  · exact B1393383
  · exact B1393387
  · exact B1393391
  · exact B1393395
  · exact B1393399
  · exact B1393403
  · exact B1393407
  · exact B1393411
  · exact B1393415
  · exact B1393419
  · exact B1393423
  · exact B1393427
  · exact B1393431
  · exact B1393435
  · exact B1393439
  · exact B1393443
  · exact B1393447
  · exact B1393451
  · exact B1393455
  · exact B1393459
  · exact B1393463
  · exact B1393467
  · exact B1393471
  · exact B1393475
  · exact B1393479
  · exact B1393483
  · exact B1393487
  · exact B1393491
  · exact B1393495
  · exact B1393499
  · exact B1393503
  · exact B1393507
  · exact B1393511
  · exact B1393515

theorem solution (m : ℕ) (hlo : 1391515 ≤ m) (hhi : m ≤ 1393515) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 347878 ≤ j := by omega
    have hj2 : j ≤ 348378 := by omega
    have hb : Blo 1391515 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
